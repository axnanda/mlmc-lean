#!/usr/bin/env python3
"""Phase 5 of the prove2.me playbook (upload_full_project.md): validate the exact upload text.

Run from the repository root after `generate.py` and `lake build Definitions Theorems Solutions`:

1. **Type diff, source vs stubs.**  The elaborated type of every node in the source library equals
   the type of its `Theorems/Thm_*` stub (compared structurally, up to binder names).
2. **Solutions match their stubs.**  For every node, `solution` in `Solutions/Sol_*` has exactly
   the type of the stub `Theorems/Thm_*` — the check the platform performs on `POST /verify`.
3. **No sorry, no self-import.**  No declaration made by a solution file uses `sorryAx` directly
   (children are referenced through their stubs, which is how reductions work), and no solution
   imports its own stub.

Usage:  python3 scripts/prove2me/validate.py [--payload prove2me/payload.json] [--jobs 4]
Exits non-zero, with a report, on any failure.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECK_DIR = ROOT / "prove2me" / "check"
LEAN_CMD = ["lake", "env", "lean"]  # overridden by --lean
WORKDIR = ROOT  # overridden by --workdir

# A canonical, binder-name-free rendering of a type, so that two elaborations of the same
# statement in different files compare equal exactly when their `Expr`s are alpha-equivalent.
CANON = r"""
open Lean Meta

partial def canonExpr : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar _ => "?fvar"
  | .mvar _ => "?mvar"
  | .sort l => s!"(Sort {l})"
  | .const n ls => s!"({n} {ls})"
  | .app f a => s!"({canonExpr f} {canonExpr a})"
  | .lam _ t b bi => s!"(fun {repr bi} {canonExpr t} {canonExpr b})"
  | .forallE _ t b bi => s!"(pi {repr bi} {canonExpr t} {canonExpr b})"
  | .letE _ t v b _ => s!"(let {canonExpr t} {canonExpr v} {canonExpr b})"
  | .lit (.natVal n) => s!"(nat {n})"
  | .lit (.strVal s) => s!"(str {repr s})"
  | .mdata _ e => canonExpr e
  | .proj s i e => s!"(proj {s} {i} {canonExpr e})"

def usesSorry (ci : ConstantInfo) : Bool :=
  let v? : Option Expr := match ci with
    | .thmInfo t => some t.value
    | .defnInfo d => some d.value
    | .opaqueInfo o => some o.value
    | _ => none
  (v?.map fun v => v.getUsedConstants.contains ``sorryAx).getD false ||
    ci.type.getUsedConstants.contains ``sorryAx
"""


def lean_file(imports: list[str], body: str) -> str:
    return "".join(f"import {i}\n" for i in ["Lean"] + imports) + CANON + "\n" + body


def run_lean(path: Path) -> tuple[int, str]:
    r = subprocess.run(LEAN_CMD + [str(path)], cwd=WORKDIR, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def type_dump(names: list[str], chunk: int = 20) -> str:
    # One `run_meta` block per `chunk` names: a single `do` block with one statement per node
    # exceeds Lean's maximum recursion depth once there are more than about 140 nodes.
    blocks = []
    for k in range(0, len(names), chunk):
        lines = [f'  IO.println s!"@@TYPE {n} {{canonExpr (← getConstInfo `{n}).type}}"'
                 for n in names[k:k + chunk]]
        blocks.append("run_meta do\n" + "\n".join(lines) + "\n")
    return "\n".join(blocks)


def parse_types(out: str) -> dict[str, str]:
    types = {}
    for line in out.splitlines():
        if line.startswith("@@TYPE "):
            _, name, canon = line.split(" ", 2)
            types[name] = canon
    return types


def main() -> None:
    global LEAN_CMD, WORKDIR, CHECK_DIR
    ap = argparse.ArgumentParser()
    ap.add_argument("--payload", default=str(ROOT / "prove2me" / "payload.json"))
    ap.add_argument("--source-root", default="MlmcLean", help="root module of the source library")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--lean", default="lake env lean", help="command that runs Lean on a file")
    ap.add_argument("--workdir", default=str(ROOT))
    ap.add_argument("--check-dir", default=str(CHECK_DIR))
    args = ap.parse_args()
    LEAN_CMD = args.lean.split()
    WORKDIR = Path(args.workdir)
    CHECK_DIR = Path(args.check_dir)
    payload = json.loads(Path(args.payload).read_text())
    nodes = [t["theorem_name"] for t in payload["theorems"]]
    stub_module = {t["theorem_name"]: t["module"] for t in payload["theorems"]}
    CHECK_DIR.mkdir(parents=True, exist_ok=True)
    failures: list[str] = []

    # 1. source types vs stub types
    src = CHECK_DIR / "SourceTypes.lean"
    src.write_text(lean_file([args.source_root], type_dump(nodes)))
    stubs = CHECK_DIR / "StubTypes.lean"
    stubs.write_text(lean_file([stub_module[n] for n in nodes], type_dump(nodes)))
    (rc1, out1), (rc2, out2) = run_lean(src), run_lean(stubs)
    if rc1 != 0:
        failures.append(f"source type dump failed:\n{out1}")
    if rc2 != 0:
        failures.append(f"stub type dump failed:\n{out2}")
    t_src, t_stub = parse_types(out1), parse_types(out2)
    for n in nodes:
        if n not in t_src or n not in t_stub:
            failures.append(f"{n}: missing type (source: {n in t_src}, stub: {n in t_stub})")
        elif t_src[n] != t_stub[n]:
            failures.append(f"{n}: stub type differs from the source type\n"
                            f"  source: {t_src[n][:400]}\n  stub:   {t_stub[n][:400]}")

    # 2./3. each solution against its own stub, one Lean process per solution
    def check_solution(sol: dict) -> list[str]:
        n = sol["theorem_name"]
        errs = []
        if stub_module[n] in sol["imports"]:
            errs.append(f"{n}: solution imports its own target {stub_module[n]}")
        body = (
            "run_meta do\n"
            "  let env ← getEnv\n"
            f"  let stub ← getConstInfo `{n}\n"
            "  let sol ← getConstInfo `solution\n"
            '  IO.println s!"@@SAME {stub.type == sol.type} '
            '{stub.levelParams == sol.levelParams}"\n'
            f"  let some idx := env.getModuleIdx? `{sol['module']} | throwError \"no module\"\n"
            "  for (c, ci) in env.constants.toList do\n"
            "    if env.getModuleIdxFor? c == some idx && usesSorry ci then\n"
            '      IO.println s!"@@SORRY {c}"\n'
        )
        f = CHECK_DIR / f"Check_{n.replace('.', '_')}.lean"
        f.write_text(lean_file([stub_module[n], sol["module"]], body))
        rc, out = run_lean(f)
        if rc != 0:
            return errs + [f"{n}: solution check failed to run:\n{out}"]
        same = [line for line in out.splitlines() if line.startswith("@@SAME ")]
        if same != ["@@SAME true true"]:
            errs.append(f"{n}: `solution` does not have the stub's type ({same})")
        for line in out.splitlines():
            if line.startswith("@@SORRY "):
                errs.append(f"{n}: {line[8:]} uses sorry")
        return errs

    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for errs in ex.map(check_solution, payload["solutions"]):
            failures.extend(errs)

    print(f"validated {len(nodes)} nodes: {len(failures)} failure(s)")
    for f in failures:
        print("FAIL", f)
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
