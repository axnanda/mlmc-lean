#!/usr/bin/env python3
"""Draft the prove2.me mission proposals on top of the uploaded tree (upload_full_project.md,
"Final verification"; mission_captain.md, "Mission proposals").

For each `prove2me/proposals/<slug>/proposal.json` (+ its `description.md`) this creates a mission
proposal, adds the goal, the milestone theorems and the definition bundles as `reference` items
(ids from the uploader's state file, or by exact name), orders them (definitions first, then the
milestones, then the goal), marks the goal, and lays out the milestone list.  It never submits:
only the account owner can audit and submit a proposal, on the website.

Idempotent: `prove2me/proposal_state.json` records every created object, so a rerun continues
where the last one stopped.  Fields are looked up by slug (`GET /fields?q=`); if a slug does not
exist the script stops and lists the candidates instead of creating a field.

Usage:  python3 scripts/prove2me/propose.py [--only <slug>] [--dry-run]
Credentials as for upload.py ($PROVE2ME_API_KEY or prove2me/credentials.json).
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import upload as up  # noqa: E402  (shares the API client, the base URL and the key handling)

ROOT = up.ROOT


def load_proposals(only: str | None) -> list[tuple[str, dict, str]]:
    out = []
    for d in sorted((ROOT / "prove2me" / "proposals").iterdir()):
        if not (d / "proposal.json").exists() or (only and d.name != only):
            continue
        p = json.loads((d / "proposal.json").read_text())
        desc = (d / p["description_file"]).read_text()
        for k in ("name", "mission_type", "goal", "milestones", "fields"):
            if not p.get(k):
                up.die(f"{d.name}: proposal.json lacks {k}")
        if p["mission_type"] not in ("OpenProblem", "Textbook", "ResearchPaper"):
            up.die(f"{d.name}: bad mission_type {p['mission_type']}")
        if len(p["name"]) > 200:
            up.die(f"{d.name}: name longer than 200 characters")
        for m in p["milestones"]:
            if len(m["title"]) > 200 or not m["description"].strip():
                up.die(f"{d.name}: milestone {m['theorem']}: bad title or empty description")
            if m["theorem"] == p["goal"]:
                up.die(f"{d.name}: the goal cannot be a milestone")
        out.append((d.name, p, desc))
    return out


def ids_from_upload(payload_names: set[str]) -> dict[str, str]:
    """Theorem and definition ids recorded by upload.py."""
    path = ROOT / "prove2me" / "upload_state.json"
    if not path.exists():
        return {}
    s = json.loads(path.read_text())
    ids = {n: r["theorem_id"] for n, r in s.get("theorems", {}).items() if r.get("theorem_id")}
    ids |= {n: r["definition_id"] for n, r in s.get("definitions", {}).items()
            if r.get("definition_id")}
    return {n: i for n, i in ids.items() if n in payload_names}


def resolve(c: up.Client, name: str, known: dict[str, str], env_param: dict, definition: bool) -> str:
    if name in known:
        return known[name]
    hit = up.find_by_name(c, name, env_param, definition=definition)
    if hit is None:
        up.die(f"{name} is not on the platform yet: run upload.py first")
    return hit["theorem_id"]


def field_ids(c: up.Client, slugs: list[str]) -> list[str]:
    ids = []
    for slug in slugs:
        code, body = c.request("GET", "/fields", query={"q": slug, "limit": 50})
        if code != 200:
            up.die(f"GET /fields?q={slug}: HTTP {code}: {body}")
        fields = up.list_items(body)
        exact = [f for f in fields if f.get("slug") == slug]
        if not exact:
            print(f"no field with slug {slug!r}; candidates:")
            for f in fields:
                print(f"  {f.get('slug')}: {f.get('name')} ({f.get('mission_count')} missions)")
            up.die("choose existing field slugs in proposal.json (the script never creates fields)")
        ids.append(exact[0]["id"])
    return ids


def build(c: up.Client, slug: str, p: dict, desc: str, st: dict, save, env_param: dict,
          known: dict[str, str]) -> None:
    rec = st.setdefault(slug, {"items": {}, "milestones": []})
    if not rec.get("proposal_id"):
        body = {"name": p["name"], "description": desc, "mission_type": p["mission_type"],
                "field_ids": field_ids(c, p["fields"]),
                "visibility": p.get("visibility", "private"), **env_param}
        code, resp = c.request("POST", "/mission-proposals", json_body=body)
        if code not in (200, 201):
            up.die(f"{slug}: POST /mission-proposals: HTTP {code}: {resp}")
        rec["proposal_id"] = resp["id"]
        save()
        print(f"{slug}: proposal {rec['proposal_id']} created")
    pid = rec["proposal_id"]
    # items: definitions first, then milestones in order, then the goal
    order = ([(d, True) for d in p.get("definitions", [])]
             + [(m["theorem"], False) for m in p["milestones"]] + [(p["goal"], False)])
    for name, is_def in order:
        if name in rec["items"]:
            continue
        tid = resolve(c, name, known, env_param, is_def)
        code, resp = c.request("POST", f"/mission-proposals/{pid}/items",
                               json_body={"kind": "reference", "theorem_id": tid})
        if code == 409:  # already in the proposal (an earlier run died before saving)
            code, detail = c.request("GET", f"/mission-proposals/{pid}")
            if code != 200:
                up.die(f"{slug}: GET proposal: HTTP {code}: {detail}")
            resp = next((it for it in detail.get("items", []) if it.get("theorem_id") == tid), None)
            if resp is None:
                up.die(f"{slug}: {name} reported as present but not found in the proposal")
        elif code not in (200, 201):
            up.die(f"{slug}: add item {name}: HTTP {code}: {resp}")
        rec["items"][name] = resp.get("id") or resp.get("item_id")
        save()
        print(f"{slug}: item {name}")
    if not rec.get("ordered"):
        body = {"main_item_id": rec["items"][p["goal"]],
                "item_order": [rec["items"][n] for n, _ in order]}
        code, resp = c.request("PATCH", f"/mission-proposals/{pid}", json_body=body)
        if code != 200:
            up.die(f"{slug}: PATCH proposal: HTTP {code}: {resp}")
        rec["ordered"] = True
        save()
    for m in p["milestones"]:
        if m["theorem"] in rec["milestones"]:
            continue
        body = {"item_id": rec["items"][m["theorem"]], "milestone_title": m["title"],
                "milestone_description": m["description"]}
        code, resp = c.request("POST", f"/mission-proposals/{pid}/milestones", json_body=body)
        if code not in (200, 201):
            up.die(f"{slug}: milestone {m['theorem']}: HTTP {code}: {resp}")
        rec["milestones"].append(m["theorem"])
        save()
        print(f"{slug}: milestone {m['title']}")
    print(f"{slug}: ready for review — the account owner audits and submits it on the website "
          f"(homepage → My missions)")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--only", help="one proposal directory name")
    ap.add_argument("--dry-run", action="store_true", help="check the proposal files only")
    ap.add_argument("--state", default=str(ROOT / "prove2me" / "proposal_state.json"))
    args = ap.parse_args()
    props = load_proposals(args.only)
    payload = json.loads((ROOT / "prove2me" / "payload.json").read_text())
    names = ({t["theorem_name"] for t in payload["theorems"]}
             | {d["definition_name"] for d in payload["definitions"]})
    for slug, p, _ in props:
        for n in [p["goal"], *(m["theorem"] for m in p["milestones"]), *p.get("definitions", [])]:
            if n not in names:
                up.die(f"{slug}: {n} is not in the payload (not uploaded by upload.py)")
    print(f"{len(props)} proposal(s): " + ", ".join(s for s, _, _ in props))
    if args.dry_run:
        return
    key = os.environ.get("PROVE2ME_API_KEY")
    cred = ROOT / "prove2me" / "credentials.json"
    if not key and cred.exists():
        key = json.loads(cred.read_text()).get("api_key")
    if not key:
        up.die("no API key: set PROVE2ME_API_KEY or create prove2me/credentials.json")
    c = up.Client(key)
    env_param = up.env_param_for(c)
    state_path = Path(args.state)
    st = json.loads(state_path.read_text()) if state_path.exists() else {}

    def save() -> None:
        tmp = state_path.with_suffix(".tmp")
        tmp.write_text(json.dumps(st, indent=1) + "\n")
        tmp.replace(state_path)

    known = ids_from_upload(names)
    for slug, p, desc in props:
        build(c, slug, p, desc, st, save, env_param, known)


if __name__ == "__main__":
    main()
