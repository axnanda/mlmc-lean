"""Tests for scripts/prove2me/upload.py against an in-process mock of the prove2.me API.

Checks: a fresh upload publishes definitions, stubs and solutions (all private) in order; a rerun
after the state file is lost submits nothing (state is rebuilt from the server's publish-job
history); source links are pinned to the payload's commit; `--make-public` refuses to run without
`--confirm-irreversible` and then publishes every node.  No network access: the uploader's base URL
is pointed at a local mock inside this process, with a fake API key.

Usage:  python3 scripts/prove2me/test_upload.py
"""
import contextlib
import importlib.util
import io
import json
import os
import re
import sys
import tempfile
import threading
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse, parse_qs

REPO = Path(__file__).resolve().parents[2]

class Mock:
    def __init__(self):
        self.jobs = {}      # id -> job
        self.items = {}     # theorem_id -> item
        self.subs = {}
        self.calls = []
        self.polls = {}
        self.me = "user-me"
    def item_by_name(self, name):
        return next((i for i in self.items.values() if i["theorem_name"] == name), None)

M = Mock()

class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def _send(self, code, body):
        raw = json.dumps(body).encode()
        self.send_response(code); self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(raw))); self.end_headers(); self.wfile.write(raw)
    def _body(self):
        n = int(self.headers.get("Content-Length", 0)); return self.rfile.read(n)
    def do_GET(self):
        u = urlparse(self.path); q = {k: v[0] for k, v in parse_qs(u.query).items()}
        p = u.path.replace("/api/v1", "")
        M.calls.append(("GET", p))
        if p == "/environments":
            return self._send(200, {"environments": [{"mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474", "toolchain": "v4.33.1", "is_default": True}]})
        if p == "/me":
            return self._send(200, {"user_id": M.me, "username": "tester", "licensing": {"status": "accepted"}})
        if p == "/publish-jobs":
            jobs = list(reversed(list(M.jobs.values())))
            off = int(q.get("offset", 0)); lim = int(q.get("limit", 50))
            return self._send(200, {"jobs": jobs[off:off + lim], "total": len(jobs)})
        m = re.match(r"^/publish-jobs/(.+)$", p)
        if m:
            j = M.jobs[m.group(1)]
            M.polls[j["id"]] = M.polls.get(j["id"], 0) + 1
            if j["status"] == "QUEUED" and M.polls[j["id"]] >= 2:
                j["status"] = "PUBLISHED"
                tid = str(uuid.uuid4()); j["theorem_id"] = tid
                M.items[tid] = {"theorem_id": tid, "theorem_name": j["theorem_name"],
                                "status": "Definition" if j["kind"] == "definition" else "Open",
                                "created_by": M.me, "formal_statement": j.get("formal_statement", ""),
                                "tags": j["tags"], "visibility": j["visibility"]}
            return self._send(200, j)
        if p == "/theorems":
            if "theorem_name" in q:
                it = M.item_by_name(q["theorem_name"])
                return self._send(200, {"theorems": [it] if it else [], "total": 1 if it else 0})
            rows = [i for i in M.items.values() if q.get("tags", "") in i["tags"]]
            off = int(q.get("offset", 0)); lim = int(q.get("limit", 50))
            return self._send(200, {"theorems": rows[off:off + lim], "total": len(rows)})
        m = re.match(r"^/theorems/([^/]+)$", p)
        if m:
            return self._send(200, M.items[m.group(1)])
        if p == "/verify":
            s = M.subs[q["submission_id"]]
            M.polls[s["id"]] = M.polls.get(s["id"], 0) + 1
            if s["status"] == "PENDING" and M.polls[s["id"]] >= 2:
                s["status"] = "ACCEPTED"; M.items[s["theorem_id"]]["status"] = "Proved"
            return self._send(200, s)
        return self._send(404, {"error": p})
    def do_POST(self):
        u = urlparse(self.path); p = u.path.replace("/api/v1", "")
        raw = self._body()
        M.calls.append(("POST", p))
        if p == "/agent/refresh":
            assert json.loads(raw)["api_key"] == "p2m_FAKE"
            return self._send(200, {"access_token": "tok", "expires_at": 9e12, "version": "0.11.1"})
        if p == "/submit-definition":
            b = json.loads(raw); assert b["private"] is True
            if M.item_by_name(b["definition_name"]) or any(j["theorem_name"] == b["definition_name"] and j["status"] == "PUBLISHED" for j in M.jobs.values()):
                jid = str(uuid.uuid4()); M.jobs[jid] = {"id": jid, "kind": "definition", "theorem_name": b["definition_name"], "status": "FAILED", "error_message": "name taken", "tags": b["tags"], "visibility": "private"}
                return self._send(202, {"job_id": jid})
            jid = str(uuid.uuid4())
            M.jobs[jid] = {"id": jid, "kind": "definition", "theorem_name": b["definition_name"], "status": "QUEUED", "error_message": "", "tags": b["tags"], "visibility": "private", "source": b["source"]}
            return self._send(202, {"job_id": jid})
        if p == "/submit-problem":
            b = json.loads(raw); assert b["private"] is True
            pr = b["problems"][0]
            assert M.item_by_name(pr["theorem_name"]) is None, "duplicate submit " + pr["theorem_name"]
            jid = str(uuid.uuid4())
            M.jobs[jid] = {"id": jid, "kind": "problem", "theorem_name": pr["theorem_name"], "status": "QUEUED", "error_message": "", "tags": pr["tags"], "visibility": "private", "formal_statement": pr["formal_statement"], "source": pr["source"]}
            return self._send(202, {"jobs": [{"job_id": jid}], "errors": []})
        if p == "/verify":
            m = re.search(rb'name="theorem_id"\r\n\r\n([^\r]+)', raw)
            tid = m.group(1).decode(); sid = str(uuid.uuid4())
            M.subs[sid] = {"id": sid, "theorem_id": tid, "status": "PENDING"}
            return self._send(202, {"submission_id": sid})
        m = re.match(r"^/theorems/([^/]+)/make-public$", p)
        if m:
            M.items[m.group(1)]["visibility"] = "public"
            return self._send(200, {"made_public": [m.group(1)]})
        return self._send(404, {"error": p})

srv = ThreadingHTTPServer(("127.0.0.1", 0), H)
threading.Thread(target=srv.serve_forever, daemon=True).start()

# fixture repo root with payload + metadata
root = Path(tempfile.mkdtemp()); (root / "prove2me").mkdir(parents=True, exist_ok=True)
thms = ["X.leaf", "X.mid", "X.top"]
payload = {"definitions": [{"definition_name": "MLMC_A", "module": "Definitions.Def_MLMC_A", "source_file": "MlmcLean/A.lean", "definition": "def a := 1\n"}],
           "theorems": [{"theorem_name": n, "module": "Theorems.Thm_" + n.replace(".", "_"), "source_file": "MlmcLean/A.lean", "source_lines": [3, 9], "preamble": "import Definitions.Def_MLMC_A\n", "formal_statement": f"theorem {n} : True := by sorry\n"} for n in thms],
           "solutions": [{"theorem_name": n, "module": "Solutions.Sol_" + n.replace(".", "_"), "solution": "import Theorems.Thm_Y\n\ntheorem solution : True := trivial\n"} for n in thms],
           "upload_order": thms, "source_commit": "abc123"}
meta = {"definitions": {"MLMC_A": {"definition_title": "A", "natural_language_statement": "A.", "source": "Giles 2015"}},
        "theorems": {n: {"theorem_title": n, "natural_language_statement": "S.", "source": "Giles 2015, Theorem 1", "explanation": "E.", "tags": ["mlmc"]} for n in thms}}
(root / "prove2me" / "payload.json").write_text(json.dumps(payload))
(root / "prove2me" / "metadata.json").write_text(json.dumps(meta))

spec = importlib.util.spec_from_file_location("upload", REPO / "scripts/prove2me/upload.py")
up = importlib.util.module_from_spec(spec); spec.loader.exec_module(up)
up.BASE = f"http://127.0.0.1:{srv.server_address[1]}/api/v1"
up.ROOT = root
up.time.sleep = lambda s: None
os.environ["PROVE2ME_API_KEY"] = "p2m_FAKE"

def run(*argv):
    sys.argv = ["upload.py", *argv]
    out = io.StringIO()
    code = 0
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
        try:
            up.main()
        except SystemExit as e:
            code = e.code or 0
    return code, out.getvalue()

state = root / "prove2me" / "upload_state.json"
if state.exists(): state.unlink()
code, out = run("--dry-run"); assert code == 0, out
code, out = run(); print(out); assert code == 0, out
assert all(i["status"] in ("Proved", "Definition") for i in M.items.values())
posts = [c for c in M.calls if c[0] == "POST" and c[1] != "/agent/refresh"]
assert len([c for c in posts if c[1] == "/submit-problem"]) == 3 and len([c for c in posts if c[1] == "/verify"]) == 3
src = next(j for j in M.jobs.values() if j["theorem_name"] == "X.top")["source"]
assert src == "Giles 2015, Theorem 1. Lean source: https://github.com/axnanda/mlmc-lean/blob/abc123/MlmcLean/A.lean#L3-L9", src
# lose the state file: a rerun must not resubmit anything
state.unlink(); n_before = len(M.calls)
code, out = run(); print(out); assert code == 0, out
new_posts = [c for c in M.calls[n_before:] if c[0] == "POST" and c[1] != "/agent/refresh"]
assert new_posts == [], new_posts
# make-public is gated
code, out = run("--make-public"); assert code == 1 and "--confirm-irreversible" in out, out
assert all(i["visibility"] == "private" for i in M.items.values())
code, out = run("--make-public", "--confirm-irreversible"); print(out); assert code == 0, out
assert all(i["visibility"] == "public" for i in M.items.values())
code, out = run("--verify-final"); assert code == 0, out
print("ALL UPLOAD TESTS PASSED")
