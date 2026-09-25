#!/usr/bin/env python3
"""Idempotent uploader for the prove2.me platform tree (upload_full_project.md, Phase 7).

Uploads, strictly in dependency order,
  1. the Definitions bundles          (POST /submit-definition, then poll /publish-jobs/:id),
  2. the theorem statements (stubs)   (POST /submit-problem, then poll /publish-jobs/:id),
  3. the solutions, leaves first      (POST /verify, then poll /verify?submission_id=…),
so that every node resolves straight to Proved.  Every action is written to a state file before
and after its API call, so an interrupted run resumes by polling instead of resubmitting.

Inputs (all in the repository):
  prove2me/payload.json    exact upload text, produced by scripts/prove2me/generate.py
  prove2me/metadata.json   titles, natural-language statements, sources, tags, explanations
Credentials: the Prove2me API key (starts with `p2m_`) from $PROVE2ME_API_KEY or from
`prove2me/credentials.json` ({"api_key": "..."}; gitignored).  It is only ever sent to
https://prove2.me/api/v1.

Usage:
  python3 scripts/prove2me/upload.py --dry-run      # validate payload + metadata, no network
  python3 scripts/prove2me/upload.py --preflight    # log in, check environment and name clashes
  python3 scripts/prove2me/upload.py                # upload everything (resumable)
  python3 scripts/prove2me/upload.py --verify-final # list the project's theorems and statuses
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = "https://prove2.me/api/v1"
SKILL_VERSION = "0.11.1"  # prove2me_workspace release this pipeline was written against
ENV_REV = "0df444a360eaa60ab8c11dca51a86af692955474"  # Lean v4.33.1 environment (lakefile.toml)
PROJECT_TAG = "mlmc-lean"
TERMINAL_JOB = {"PUBLISHED", "FAILED", "ERROR"}
TERMINAL_SUB = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}


def die(msg: str) -> None:
    print(f"upload.py: {msg}", file=sys.stderr)
    sys.exit(1)


class State:
    """Append-only record of every action, persisted after each change."""

    def __init__(self, path: Path):
        self.path = path
        self.data = json.loads(path.read_text()) if path.exists() else {
            "definitions": {}, "theorems": {}, "solutions": {}, "log": []}

    def save(self) -> None:
        tmp = self.path.with_suffix(".tmp")
        tmp.write_text(json.dumps(self.data, indent=1, ensure_ascii=False) + "\n")
        tmp.replace(self.path)

    def log(self, event: str, **kw) -> None:
        self.data["log"].append({"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                                 "event": event, **kw})
        self.save()


class Client:
    def __init__(self, api_key: str):
        self.api_key = api_key
        self.token = None
        self.expires = 0.0

    def _refresh(self) -> None:
        body = json.dumps({"api_key": self.api_key}).encode()
        req = urllib.request.Request(f"{BASE}/agent/refresh", data=body, method="POST",
                                     headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=60) as r:
            resp = json.loads(r.read())
        self.token = resp["access_token"]
        self.expires = float(resp.get("expires_at", time.time() + 3600))
        if resp.get("version") and resp["version"] != SKILL_VERSION:
            print(f"warning: platform version {resp['version']} differs from the skill version "
                  f"{SKILL_VERSION} this uploader was written against; check "
                  "https://github.com/prove2me/prove2me_workspace for API changes.")

    def request(self, method: str, path: str, *, json_body=None, form=None, query=None,
                retries: int = 6):
        if self.token is None or time.time() > self.expires - 300:
            self._refresh()
        url = f"{BASE}{path}"
        if query:
            url += "?" + urllib.parse.urlencode(query)
        headers = {"Authorization": f"Bearer {self.token}"}
        data = None
        if json_body is not None:
            data = json.dumps(json_body, ensure_ascii=False).encode()
            headers["Content-Type"] = "application/json"
        elif form is not None:
            boundary = uuid.uuid4().hex
            parts = []
            for k, v in form.items():
                if isinstance(v, tuple):  # (filename, content)
                    parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{k}"; '
                                 f'filename="{v[0]}"\r\nContent-Type: text/plain\r\n\r\n'.encode()
                                 + v[1].encode() + b"\r\n")
                else:
                    parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{k}"'
                                 f'\r\n\r\n'.encode() + str(v).encode() + b"\r\n")
            data = b"".join(parts) + f"--{boundary}--\r\n".encode()
            headers["Content-Type"] = f"multipart/form-data; boundary={boundary}"
        delay = 5.0
        for attempt in range(retries):
            req = urllib.request.Request(url, data=data, method=method, headers=headers)
            try:
                with urllib.request.urlopen(req, timeout=120) as r:
                    raw = r.read()
                    return r.status, (json.loads(raw) if raw else None)
            except urllib.error.HTTPError as e:
                raw = e.read()
                body = None
                try:
                    body = json.loads(raw) if raw else None
                except json.JSONDecodeError:
                    body = raw.decode(errors="replace")
                if e.code == 401 and attempt == 0:
                    self._refresh()
                    headers["Authorization"] = f"Bearer {self.token}"
                    continue
                if e.code == 429 or e.code >= 500:
                    print(f"  {method} {path}: HTTP {e.code}; retrying in {delay:.0f}s")
                    time.sleep(delay)
                    delay = min(delay * 2, 120)
                    continue
                return e.code, body
            except urllib.error.URLError as e:
                print(f"  {method} {path}: {e}; retrying in {delay:.0f}s")
                time.sleep(delay)
                delay = min(delay * 2, 120)
        die(f"{method} {path}: giving up after {retries} attempts")


def load_inputs():
    payload = json.loads((ROOT / "prove2me" / "payload.json").read_text())
    meta = json.loads((ROOT / "prove2me" / "metadata.json").read_text())
    problems = []
    for d in payload["definitions"]:
        m = meta["definitions"].get(d["definition_name"])
        if not m:
            problems.append(f"no metadata for definition {d['definition_name']}")
            continue
        for k in ("definition_title", "natural_language_statement", "source"):
            if not m.get(k):
                problems.append(f"definition {d['definition_name']}: missing {k}")
    for t in payload["theorems"]:
        m = meta["theorems"].get(t["theorem_name"])
        if not m:
            problems.append(f"no metadata for theorem {t['theorem_name']}")
            continue
        for k in ("theorem_title", "natural_language_statement", "source", "explanation"):
            if not m.get(k):
                problems.append(f"theorem {t['theorem_name']}: missing {k}")
        if len(m.get("theorem_title", "")) > 200:
            problems.append(f"theorem {t['theorem_name']}: title longer than 200 characters")
        if "sorry" in next(s["solution"] for s in payload["solutions"]
                           if s["theorem_name"] == t["theorem_name"]).replace("-- ", ""):
            problems.append(f"solution of {t['theorem_name']} mentions sorry")
        if not t["formal_statement"].rstrip().endswith(":= by sorry"):
            problems.append(f"theorem {t['theorem_name']}: formal_statement must end in := by sorry")
        if t["formal_statement"].lstrip().startswith("/--"):
            problems.append(f"theorem {t['theorem_name']}: formal_statement starts with a docstring")
    for s in payload["solutions"]:
        if f"import Theorems.Thm_{s['theorem_name'].replace('.', '_')}\n" in s["solution"]:
            problems.append(f"solution of {s['theorem_name']} imports its own target")
        if "\ntheorem solution" not in s["solution"]:
            problems.append(f"solution of {s['theorem_name']} has no top-level `theorem solution`")
    if problems:
        die("payload/metadata check failed:\n  " + "\n  ".join(problems))
    return payload, meta


def tags_for(meta_entry: dict) -> list[str]:
    tags = list(meta_entry.get("tags", []))
    if PROJECT_TAG not in tags:
        tags.append(PROJECT_TAG)
    return tags


def find_by_name(c: Client, name: str, env_param: dict, definition: bool = False):
    """Exact-match lookup of a theorem or definition by its name (GET /theorems?theorem_name=)."""
    query = {"theorem_name": name, "limit": 50, **env_param}
    if definition:
        query["status"] = "Definition"
    code, body = c.request("GET", "/theorems", query=query)
    if code != 200:
        die(f"GET /theorems?theorem_name={name}: HTTP {code}: {body}")
    items = body.get("theorems", []) if isinstance(body, dict) else body
    for it in items or []:
        if name in (it.get("theorem_name"), it.get("definition_name")):
            return it
    return None


def poll_job(c: Client, job_id: str) -> dict:
    delay = 3.0
    while True:
        code, body = c.request("GET", f"/publish-jobs/{job_id}")
        if code != 200:
            die(f"GET /publish-jobs/{job_id}: HTTP {code}: {body}")
        if body["status"] in TERMINAL_JOB:
            return body
        time.sleep(delay)
        delay = min(delay * 1.5, 30)


def poll_submission(c: Client, sub_id: str) -> dict:
    delay = 3.0
    while True:
        code, body = c.request("GET", "/verify", query={"submission_id": sub_id})
        if code != 200:
            die(f"GET /verify?submission_id={sub_id}: HTTP {code}: {body}")
        if body["status"] in TERMINAL_SUB:
            return body
        time.sleep(delay)
        delay = min(delay * 1.5, 30)


def env_param_for(c: Client) -> dict:
    code, body = c.request("GET", "/environments")
    if code != 200:
        die(f"GET /environments: HTTP {code}: {body}")
    envs = body["environments"]
    ours = [e for e in envs if e["mathlib_rev"] == ENV_REV]
    if not ours:
        die(f"the platform no longer offers the environment {ENV_REV}; available: "
            + ", ".join(f"{e['mathlib_rev'][:7]} ({e['toolchain']})" for e in envs)
            + ". Re-pin lakefile.toml/lean-toolchain to one of them, rebuild and regenerate.")
    return {} if ours[0].get("is_default") else {"env": ENV_REV}


def preflight(c: Client, payload: dict, state: State) -> dict:
    env_param = env_param_for(c)
    print(f"environment {ENV_REV[:7]} available" + (" (non-default)" if env_param else " (default)"))
    clashes = []
    for d in payload["definitions"]:
        hit = find_by_name(c, d["definition_name"], env_param, definition=True)
        if hit and d["definition_name"] not in state.data["definitions"]:
            clashes.append(f"definition {d['definition_name']} (id {hit.get('theorem_id')})")
    for t in payload["theorems"]:
        hit = find_by_name(c, t["theorem_name"], env_param)
        if hit and t["theorem_name"] not in state.data["theorems"]:
            clashes.append(f"theorem {t['theorem_name']} (id {hit.get('theorem_id')})")
    if clashes:
        print("names already taken on the platform (not by this uploader's earlier runs):")
        for x in clashes:
            print("  " + x)
        die("resolve the clashes first (e.g. wrap the upload in a distinguishing namespace) — "
            "uploaded names are immutable.")
    print("no name clashes")
    return env_param


def upload(c: Client, payload: dict, meta: dict, state: State, env_param: dict) -> None:
    S = state.data
    # 1. definitions, in dependency order
    for d in payload["definitions"]:
        name = d["definition_name"]
        rec = S["definitions"].setdefault(name, {})
        if rec.get("definition_id"):
            continue
        if not rec.get("job_id"):
            m = meta["definitions"][name]
            body = {"definition_name": name, "definition_title": m["definition_title"],
                    "definition": d["definition"],
                    "natural_language_statement": m["natural_language_statement"],
                    "source": m["source"], "tags": tags_for(m), **env_param}
            state.log("submit-definition", name=name)
            code, resp = c.request("POST", "/submit-definition", json_body=body)
            if code not in (200, 201, 202):
                die(f"submit-definition {name}: HTTP {code}: {resp}")
            rec["job_id"] = resp["job_id"]
            state.log("submit-definition:queued", name=name, job_id=rec["job_id"])
        job = poll_job(c, rec["job_id"])
        if job["status"] != "PUBLISHED":
            rec.pop("job_id")
            state.save()
            die(f"definition {name}: job {job['status']}: {job.get('error_message')}")
        rec["definition_id"] = job.get("theorem_id") or job.get("definition_id")
        state.log("definition:published", name=name, id=rec["definition_id"])
        print(f"definition {name}: published")

    # 2. theorem statements, leaves first
    by_name = {t["theorem_name"]: t for t in payload["theorems"]}
    for name in payload["upload_order"]:
        t = by_name[name]
        rec = S["theorems"].setdefault(name, {})
        if rec.get("theorem_id"):
            continue
        if not rec.get("job_id"):
            m = meta["theorems"][name]
            problem = {"theorem_name": name, "theorem_title": m["theorem_title"],
                       "formal_statement": t["formal_statement"],
                       "natural_language_statement": m["natural_language_statement"],
                       "preamble": t["preamble"], "source": m["source"], "tags": tags_for(m)}
            state.log("submit-problem", name=name)
            code, resp = c.request("POST", "/submit-problem",
                                   json_body={"problems": [problem], **env_param})
            if code not in (200, 201, 202) or resp.get("errors"):
                die(f"submit-problem {name}: HTTP {code}: {resp}")
            rec["job_id"] = resp["jobs"][0]["job_id"]
            state.log("submit-problem:queued", name=name, job_id=rec["job_id"])
        job = poll_job(c, rec["job_id"])
        if job["status"] != "PUBLISHED":
            rec.pop("job_id")
            state.save()
            die(f"theorem {name}: job {job['status']}: {job.get('error_message')}")
        rec["theorem_id"] = job["theorem_id"]
        state.log("theorem:published", name=name, id=rec["theorem_id"])
        print(f"theorem {name}: published")

    # 3. solutions, leaves first (children are Proved before their parents are verified)
    sols = {s["theorem_name"]: s for s in payload["solutions"]}
    for name in payload["upload_order"]:
        rec = S["solutions"].setdefault(name, {})
        if rec.get("status") == "ACCEPTED":
            continue
        if not rec.get("submission_id"):
            form = {"theorem_id": S["theorems"][name]["theorem_id"],
                    "proof_type": "prove",
                    "explanation": meta["theorems"][name]["explanation"],
                    "file": ("solution.lean", sols[name]["solution"])}
            state.log("verify", name=name)
            code, resp = c.request("POST", "/verify", form=form)
            if code not in (200, 201, 202):
                die(f"verify {name}: HTTP {code}: {resp}")
            rec["submission_id"] = resp["submission_id"]
            state.log("verify:queued", name=name, submission_id=rec["submission_id"])
        sub = poll_submission(c, rec["submission_id"])
        rec["status"] = sub["status"]
        state.log("verify:result", name=name, status=sub["status"],
                  error=sub.get("error_message", ""))
        if sub["status"] == "SKETCH_ACCEPTED":
            die(f"solution {name} was accepted only as a sketch: a child is not Proved yet")
        if sub["status"] != "ACCEPTED":
            rec.pop("submission_id")
            state.save()
            die(f"solution {name}: {sub['status']}: {sub.get('error_message')}")
        print(f"solution {name}: ACCEPTED")


def verify_final(c: Client, env_param: dict) -> None:
    offset, rows = 0, []
    while True:
        code, body = c.request("GET", "/theorems",
                               query={"tags": PROJECT_TAG, "limit": 100, "offset": offset,
                                      **env_param})
        if code != 200:
            die(f"GET /theorems?tags={PROJECT_TAG}: HTTP {code}: {body}")
        items = body.get("theorems", body.get("items", [])) if isinstance(body, dict) else body
        rows += items or []
        if not items or len(items) < 100:
            break
        offset += 100
    for r in rows:
        print(f"{r.get('status', '?'):10} {r.get('theorem_name') or r.get('definition_name')}")
    open_ = [r for r in rows if r.get("status") == "Open"]
    print(f"{len(rows)} items, {len(open_)} Open")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--preflight", action="store_true")
    ap.add_argument("--verify-final", action="store_true")
    ap.add_argument("--state", default=str(ROOT / "prove2me" / "upload_state.json"))
    args = ap.parse_args()
    payload, meta = load_inputs()
    print(f"{len(payload['definitions'])} definitions, {len(payload['theorems'])} theorems, "
          f"{len(payload['solutions'])} solutions; order: {len(payload['upload_order'])} nodes")
    if args.dry_run:
        print("dry run: payload and metadata are complete")
        return
    key = os.environ.get("PROVE2ME_API_KEY")
    cred = ROOT / "prove2me" / "credentials.json"
    if not key and cred.exists():
        key = json.loads(cred.read_text()).get("api_key")
    if not key:
        die("no API key: set PROVE2ME_API_KEY or create prove2me/credentials.json")
    c = Client(key)
    state = State(Path(args.state))
    if args.verify_final:
        verify_final(c, env_param_for(c))
        return
    env_param = preflight(c, payload, state)
    if args.preflight:
        return
    upload(c, payload, meta, state, env_param)
    verify_final(c, env_param)


if __name__ == "__main__":
    main()
