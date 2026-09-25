#!/usr/bin/env python3
"""Generate the prove2.me platform tree from the Lean sources by skeleton subtraction.

This implements Phases 2–4 of the prove2.me playbook
(prove2me_workspace/references/upload_full_project.md, v0.11.1):

* Phase 1 facts are produced in CI by `scripts/prove2me/extract_decl_graph.lean` (Stage 1:
  declaration graph) and `scripts/prove2me/extract_sketch_info.lean` (Stage 2: positions,
  extended with every top-level command so that namespaces, sections and `variable`s can be
  rebuilt).  They live in `prove2me/facts/`.
* Phase 2: every declaration reachable from the targets is classified as a *node* (listed in
  `scripts/prove2me/plan.json`; gets `Theorems/Thm_*` + `Solutions/Sol_*`), *Def-material*
  (definitions; one `Definitions/Def_*` bundle per source module) or an *inline helper* (every
  other theorem; pasted into each solution that needs it, inside its own `section` with the
  `variable`/`open` context it was written in).
* Phase 3/4: files are produced by deleting or copying source spans at the byte offsets reported
  by Lean; statements are cut at the reported `valStart`, docstrings are dropped from formal
  statements, namespaces become `open`s, `c in` wrappers are hoisted, and each node is declared
  with its fully-dotted name (stub) or as top-level `theorem solution` (solution).

No Lean source is pattern-matched: all positions and dependencies come from the facts.

Usage:  python3 scripts/prove2me/generate.py [--facts prove2me/facts] [--out prove2me/platform]
Writes the three libraries under --out and `prove2me/payload.json` (the exact upload text).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PROJECT_PREFIX = "MlmcLean"  # overridden by --prefix
SRC_ROOT = ROOT  # overridden by --root

# Syntax kinds of the top-level commands that shape the scope of later declarations.
K_NAMESPACE = "Lean.Parser.Command.namespace"
K_SECTION = "Lean.Parser.Command.section"
K_END = "Lean.Parser.Command.end"
SCOPE_KINDS = {
    "Lean.Parser.Command.variable",
    "Lean.Parser.Command.open",
    "Lean.Parser.Command.omit",
    "Lean.Parser.Command.include",
    "Lean.Parser.Command.universe",
    "Lean.Parser.Command.set_option",
}

ASCII_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$")


def fail(msg: str) -> None:
    print(f"generate.py: error: {msg}", file=sys.stderr)
    sys.exit(1)


@dataclass
class Frame:
    kind: str  # "file" | "namespace" | "section"
    name: str
    cmds: list[str] = field(default_factory=list)


@dataclass
class Decl:
    name: str
    module: str
    kind: str
    type_deps: set[str]
    value_deps: set[str]
    fact: dict | None = None
    frames: list[Frame] | None = None  # scope snapshot at the declaration

    @property
    def ns_path(self) -> str:
        return ".".join(f.name for f in self.frames if f.kind == "namespace")


class Module:
    def __init__(self, name: str, facts_dir: Path):
        self.name = name
        rel = name.replace(".", "/") + ".lean"
        self.path = SRC_ROOT / rel
        self.rel = rel
        self.text = self.path.read_bytes()
        fpath = facts_dir / f"sketch_info.{name.split('.')[-1]}.jsonl"
        if not fpath.exists():
            fail(f"missing Stage 2 facts {fpath}")
        rows = [json.loads(line) for line in fpath.read_text().splitlines() if line.strip()]
        imports = [r for r in rows if r["kind"] == "imports"]
        if len(imports) != 1:
            fail(f"{fpath}: expected one imports fact")
        self.imports: list[str] = imports[0]["modules"]
        he = imports[0]["headerEnd"]
        self.header_end: int = he["offset"] if he else 0  # no `import` lines: empty header
        self.cmds = sorted((r for r in rows if r["kind"] == "cmd"), key=lambda r: r["start"]["offset"])
        self.decl_facts = sorted((r for r in rows if r["kind"] == "decl"),
                                 key=lambda r: r["declStart"]["offset"])

    def slice(self, a: int, b: int) -> str:
        return self.text[a:b].decode("utf-8")

    @property
    def project_imports(self) -> list[str]:
        return [m for m in self.imports if m.split(".")[0] == PROJECT_PREFIX]

    @property
    def external_imports(self) -> list[str]:
        return [m for m in self.imports if m.split(".")[0] != PROJECT_PREFIX and m != "Init"]

    def scopes(self) -> dict[int, list[Frame]]:
        """Scope snapshot (namespaces, sections and their scope commands) at each declaration,
        keyed by the declaration's start offset."""
        decl_starts = {d["declStart"]["offset"] for d in self.decl_facts}
        stack = [Frame("file", "")]
        snaps: dict[int, list[Frame]] = {}
        for c in self.cmds:
            a, b = c["start"]["offset"], c["end"]["offset"]
            kind = c["syntaxKind"]
            if kind == K_NAMESPACE:
                stack.append(Frame("namespace", self.slice(a, b).split()[1]))
            elif kind == K_SECTION:
                parts = self.slice(a, b).split()
                stack.append(Frame("section", parts[1] if len(parts) > 1 else ""))
            elif kind == K_END:
                if len(stack) == 1:
                    fail(f"{self.rel}: unbalanced `end` at offset {a}")
                stack.pop()
            elif kind in SCOPE_KINDS:
                stack[-1].cmds.append(self.slice(a, b))
            elif a in decl_starts:
                snaps[a] = [Frame(f.kind, f.name, list(f.cmds)) for f in stack]
        return snaps


def load(facts_dir: Path, plan: dict):
    graph_path = facts_dir / "decl_graph.jsonl"
    if not graph_path.exists():
        fail(f"missing Stage 1 facts {graph_path}")
    rows = [json.loads(line) for line in graph_path.read_text().splitlines() if line.strip()]
    decls: dict[str, Decl] = {}
    for r in rows:
        decls[r["name"]] = Decl(r["name"], r["module"], r["kind"], set(r["typeDeps"]),
                                set(r["valueDeps"]))
        decls[r["name"]].start_line = r["startLine"]  # type: ignore[attr-defined]
        decls[r["name"]].is_private = r["isPrivate"]  # type: ignore[attr-defined]
        decls[r["name"]].is_instance = r["isInstance"]  # type: ignore[attr-defined]
    modules = {m: Module(m, facts_dir) for m in sorted({d.module for d in decls.values()})}
    # join Stage 1 rows to Stage 2 decl facts by containment of the start line
    for mod in modules.values():
        snaps = mod.scopes()
        for d in decls.values():
            if d.module != mod.name or d.start_line == 0:  # type: ignore[attr-defined]
                continue
            hits = [f for f in mod.decl_facts
                    if f["declStart"]["line"] <= d.start_line <= f["declEnd"]["line"]]  # type: ignore[attr-defined]
            if len(hits) != 1:
                fail(f"{d.name}: {len(hits)} decl facts contain line {d.start_line}")  # type: ignore[attr-defined]
            d.fact = hits[0]
            d.frames = snaps[hits[0]["declStart"]["offset"]]
    return decls, modules


def project_closure(modules: dict[str, Module], m: str) -> list[str]:
    """`m` and its transitive project imports, dependencies first."""
    seen: list[str] = []

    def visit(x: str) -> None:
        if x in seen:
            return
        for y in modules[x].project_imports:
            visit(y)
        seen.append(x)

    visit(m)
    return seen


def external_union(modules: dict[str, Module], mods: list[str]) -> list[str]:
    out: list[str] = []
    for m in mods:
        for x in project_closure(modules, m):
            for i in modules[x].external_imports:
                if i not in out:
                    out.append(i)
    return out


def main() -> None:
    global PROJECT_PREFIX, SRC_ROOT
    ap = argparse.ArgumentParser()
    ap.add_argument("--facts", default=str(ROOT / "prove2me" / "facts"))
    ap.add_argument("--out", default=str(ROOT / "prove2me" / "platform"))
    ap.add_argument("--plan", default=str(ROOT / "scripts" / "prove2me" / "plan.json"))
    ap.add_argument("--payload", default=str(ROOT / "prove2me" / "payload.json"))
    ap.add_argument("--root", default=str(ROOT), help="source tree root (contains <prefix>/*.lean)")
    ap.add_argument("--prefix", default="MlmcLean", help="project module prefix")
    args = ap.parse_args()
    PROJECT_PREFIX = args.prefix
    SRC_ROOT = Path(args.root)
    plan = json.loads(Path(args.plan).read_text())
    decls, modules = load(Path(args.facts), plan)

    targets: list[str] = plan["targets"]
    for n in targets:
        if n not in decls:
            fail(f"plan target {n} is not a project declaration")
        if decls[n].kind != "theorem":
            fail(f"plan target {n} is not a theorem")

    # ---- Phase 2: reachability from the targets, then classification ----
    reach: set[str] = set()
    work = list(targets)
    while work:
        x = work.pop()
        if x in reach or x not in decls:
            continue
        reach.add(x)
        work.extend(decls[x].type_deps | decls[x].value_deps)
    reach = {x for x in reach if decls[x].start_line > 0}  # type: ignore[attr-defined]
    for x in reach:
        if decls[x].is_private:  # type: ignore[attr-defined]
            fail(f"private declaration {x} is reachable; not supported by this generator")
        if decls[x].is_instance:  # type: ignore[attr-defined]
            fail(f"instance {x} is reachable; not supported by this generator")

    theorems = {x for x in reach if decls[x].kind == "theorem"}
    users: dict[str, set[str]] = {x: set() for x in theorems}
    for y in reach:
        for x in decls[y].value_deps:
            if x in users and x != y:
                users[x].add(y)

    def proof_lines(x: str) -> int:
        f = decls[x].fact
        return f["declEnd"]["line"] - f["valStart"]["line"] if f and f["valStart"] else 0

    force_node = set(plan.get("forceNode", []))
    force_inline = set(plan.get("forceInline", []))
    paper_named = set(plan.get("paperNamed", []))
    node_set = set(targets) | force_node
    changed = True
    while changed:  # the "used by >= 2 nodes" signal depends on the node set: iterate
        changed = False
        for x in sorted(theorems - node_set - force_inline):
            lines = proof_lines(x)
            signal = (len(users[x] & node_set) >= 2
                      or any(decls[u].module != decls[x].module for u in users[x])
                      or decls[x].fact["docstring"] is not None
                      or x in paper_named)
            if lines > 40 or (lines > 10 and signal):
                node_set.add(x)
                changed = True
    nodes: list[str] = sorted(node_set, key=lambda x: (decls[x].module,
                                                       decls[x].fact["declStart"]["offset"]))
    for n in nodes:
        if not ASCII_IDENT.match(n):
            fail(f"node name {n} is not a conservative ASCII identifier")

    def_material = {x for x in reach if decls[x].kind != "theorem"}
    helpers = theorems - node_set
    for x in def_material:
        for y in decls[x].type_deps | decls[x].value_deps:
            if y in reach and decls[y].kind == "theorem":
                fail(f"definition {x} cites theorem {y} (a Def-embedded theorem); move it")
    for n in nodes:
        for y in decls[n].type_deps:
            if y in reach and y not in def_material:
                fail(f"statement of {n} mentions non-definition {y}")

    bundle_name: dict[str, str] = dict(plan.get("defBundles", {}))
    bundles: dict[str, list[str]] = {}
    for x in sorted(def_material, key=lambda x: decls[x].fact["declStart"]["offset"]):
        bundles.setdefault(decls[x].module, []).append(x)
    for m in bundles:
        # default bundle name: <bundlePrefix><last module component>
        bundle_name.setdefault(m, plan.get("bundlePrefix", "") + m.split(".")[-1])
        if not ASCII_IDENT.match(bundle_name[m]) or "." in bundle_name[m]:
            fail(f"bundle name {bundle_name[m]} is not an ASCII identifier")

    mod_order = []
    for m in modules:
        for x in project_closure(modules, m):
            if x not in mod_order:
                mod_order.append(x)

    def bundle_module(m: str) -> str:
        return f"Definitions.Def_{bundle_name[m]}"

    def thm_module(n: str) -> str:
        return "Theorems.Thm_" + n.replace(".", "_")

    def sol_module(n: str) -> str:
        return "Solutions.Sol_" + n.replace(".", "_")

    def bundles_for(mods: list[str]) -> list[str]:
        out = []
        for m in mod_order:
            if m in bundles and any(m in project_closure(modules, x) for x in mods):
                out.append(bundle_module(m))
        return out

    def statement_text(d: Decl) -> str:
        """`<binders> : <type> ` — from the end of the declared name to the start of the value."""
        f = d.fact
        mod = modules[d.module]
        return mod.slice(f["declId"]["end"]["offset"], f["valStart"]["offset"])

    out = Path(args.out)
    for sub in ("Definitions", "Theorems", "Solutions"):
        (out / sub).mkdir(parents=True, exist_ok=True)
        for old in (out / sub).glob("*.lean"):
            old.unlink()

    header_note = "-- Generated by scripts/prove2me/generate.py from {src}; do not edit by hand.\n"
    payload = {"definitions": [], "theorems": [], "solutions": []}

    # ---- Definitions: one bundle per source module (skeleton subtraction) ----
    for m in mod_order:
        if m not in bundles:
            continue
        mod = modules[m]
        keep = set(bundles[m])
        cuts = []
        for d in decls.values():
            if d.module == m and d.fact is not None and d.name not in keep:
                cuts.append((d.fact["declStart"]["offset"], d.fact["declEnd"]["offset"]))
        # declarations with no Stage 1 row (e.g. `example`s) are also cut
        known = {(d.fact["declStart"]["offset"]) for d in decls.values() if d.fact is not None}
        for f in mod.decl_facts:
            if f["declStart"]["offset"] not in known:
                cuts.append((f["declStart"]["offset"], f["declEnd"]["offset"]))
        cuts = sorted(set(cuts))
        body = bytearray(mod.text)
        for a, b in reversed(cuts):
            # drop the span and the newline after it
            if b < len(body) and body[b:b + 1] == b"\n":
                b += 1
            del body[a:b]
        body_text = body[mod.header_end:].decode("utf-8")
        imports = [bundle_module(x) for x in project_closure(modules, m)[:-1] if x in bundles]
        imports += external_union(modules, [m])
        code = header_note.format(src=mod.rel) + "".join(f"import {i}\n" for i in imports)
        code += body_text
        path = out / "Definitions" / f"Def_{bundle_name[m]}.lean"
        path.write_text(code)
        payload["definitions"].append({
            "definition_name": bundle_name[m],
            "module": bundle_module(m),
            "source_module": m,
            "source_file": mod.rel,
            "declarations": bundles[m],
            "imports": [i for i in imports if i.startswith("Definitions.")],
            "definition": code,
        })

    # ---- Theorems (stubs) and Solutions ----
    def closure_of(n: str) -> tuple[list[str], list[str], set[str]]:
        """Inline helpers (source order), child nodes, and modules whose definitions are used."""
        hs: set[str] = set()
        kids: set[str] = set()
        mods: set[str] = {decls[n].module}
        work = list(decls[n].value_deps | decls[n].type_deps)
        while work:
            y = work.pop()
            if y not in reach:
                continue
            if y in def_material:
                mods.add(decls[y].module)
            elif y in nodes:
                if y != n:
                    kids.add(y)
            elif y in helpers and y not in hs:
                hs.add(y)
                mods.add(decls[y].module)
                work.extend(decls[y].value_deps | decls[y].type_deps)
        order = sorted(hs, key=lambda h: (mod_order.index(decls[h].module),
                                          decls[h].fact["declStart"]["offset"]))
        return order, sorted(kids), mods

    for n in nodes:
        d = decls[n]
        mod = modules[d.module]
        f = d.fact
        if f["valStart"] is None or f["declId"] is None:
            fail(f"{n}: missing declId/valStart facts")
        full_name = n
        # stub
        stub_imports = bundles_for([d.module]) + external_union(modules, [d.module])
        wrappers = [mod.slice(w["start"]["offset"], w["end"]["offset"]) for w in f["wrappers"]]
        # scope commands must come after the `open` of the namespace (they may use its names)
        pre_lines = [header_note.format(src=mod.rel).rstrip("\n")]
        pre_lines += [f"import {i}" for i in stub_imports]
        pre_lines.append("")
        pre_lines += [c for fr in d.frames if fr.kind == "file" for c in fr.cmds]
        if d.ns_path:
            pre_lines.append(f"open {d.ns_path}")
        pre_lines += [c for fr in d.frames if fr.kind != "file" for c in fr.cmds]
        pre_lines += wrappers  # hoisted `c in` wrappers, now standalone commands
        preamble = "\n".join(pre_lines) + "\n\n"
        formal = f"theorem {full_name}{statement_text(d)}:= by sorry\n"
        (out / "Theorems" / f"Thm_{n.replace('.', '_')}.lean").write_text(preamble + formal)
        start_line = f["declStart"]["line"]
        end_line = f["declEnd"]["line"]
        payload["theorems"].append({
            "theorem_name": n,
            "module": thm_module(n),
            "source_module": d.module,
            "source_file": mod.rel,
            "source_lines": [start_line, end_line],
            "preamble": preamble,
            "formal_statement": formal,
            "imports": [i for i in stub_imports if i.startswith("Definitions.")],
        })

        # solution
        hs, kids, mods = closure_of(n)
        sol_imports = bundles_for(sorted(mods)) + [thm_module(k) for k in kids]
        sol_imports += external_union(modules, sorted(mods))
        lines = [header_note.format(src=mod.rel).rstrip("\n")]
        lines += [f"import {i}" for i in sol_imports]
        lines.append("")
        for h in hs:
            hd = decls[h]
            hmod = modules[hd.module]
            hf = hd.fact
            if hd.ns_path:
                lines.append(f"namespace {hd.ns_path}")
            lines.append("section")
            lines += [c for fr in hd.frames for c in fr.cmds]
            lines.append(hmod.slice(hf["declStart"]["offset"], hf["declEnd"]["offset"]))
            lines.append("end")
            if hd.ns_path:
                lines.append(f"end {hd.ns_path}")
            lines.append("")
        lines += [c for fr in d.frames if fr.kind == "file" for c in fr.cmds]
        if d.ns_path:
            lines.append(f"open {d.ns_path}")
        lines += [c for fr in d.frames if fr.kind != "file" for c in fr.cmds]
        prefix = mod.slice(f["declStart"]["offset"], f["innerStart"]["offset"])
        body = mod.slice(f["declId"]["end"]["offset"], f["declEnd"]["offset"])
        lines.append("")
        lines.append(prefix + "theorem solution" + body)
        code = "\n".join(lines) + "\n"
        (out / "Solutions" / f"Sol_{n.replace('.', '_')}.lean").write_text(code)
        payload["solutions"].append({
            "theorem_name": n,
            "module": sol_module(n),
            "children": kids,
            "inline_helpers": hs,
            "imports": [i for i in sol_imports if i.startswith(("Definitions.", "Theorems."))],
            "solution": code,
        })

    # upload order: definitions (already dependency-ordered), theorems and solutions leaves-first
    order: list[str] = []

    def visit(n: str, stack: tuple = ()) -> None:
        if n in order:
            return
        if n in stack:
            fail(f"cycle through {n}")
        for k in next(s for s in payload["solutions"] if s["theorem_name"] == n)["children"]:
            visit(k, stack + (n,))
        order.append(n)

    for n in nodes:
        visit(n)
    payload["upload_order"] = order
    # the commit the upload text was generated from; upload.py pins its source links to it
    try:
        payload["source_commit"] = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=SRC_ROOT, capture_output=True, text=True,
            check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        payload["source_commit"] = None
    payload["classification"] = {
        "targets": targets,
        "nodes": nodes,
        "inline_helpers": sorted(helpers),
        "definitions": {bundle_name[m]: v for m, v in bundles.items()},
        "proof_lines": {x: proof_lines(x) for x in sorted(theorems)},
    }
    Path(args.payload).write_text(json.dumps(payload, indent=1, ensure_ascii=False) + "\n")
    print(f"{len(payload['definitions'])} Def bundles, {len(nodes)} nodes, "
          f"{len(helpers)} inline helpers -> {out}")


if __name__ == "__main__":
    main()
