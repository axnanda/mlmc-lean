#!/bin/bash
# Regression test for the prove2.me pipeline on a small Lean-core-only project (no Mathlib):
# build it, extract the facts (Stage 1 and 2), generate the platform tree, compile every generated
# file, and validate it (validate.py). The fixture covers: section variables and `omit … in`,
# a node by size, inline helpers, a recursive target, a proof that uses a `@[simp]` rfl-lemma only
# implicitly, and a module with no project imports.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
cp -r "$HERE/Fix" "$HERE/Fix.lean" "$HERE/plan.json" "$REPO/lean-toolchain" "$W/"
cd "$W"
mkdir -p build/Fix facts pbuild
sed -e 's/^import MlmcLean$/import Lean\nimport Fix/' -e 's/`MlmcLean$/`Fix/' \
  "$REPO/scripts/prove2me/extract_decl_graph.lean" > extract_decl_graph.lean
export LEAN_PATH="$W/build"
MODS="Defs Lemmas Main Rec NoDefs"
for m in $MODS; do lean -o "build/Fix/$m.olean" -i "build/Fix/$m.ilean" "Fix/$m.lean"; done
lean -o build/Fix.olean Fix.lean
lean extract_decl_graph.lean > /dev/null
mv decl_graph.jsonl facts/
for m in $MODS; do
  lean --run "$REPO/scripts/prove2me/extract_sketch_info.lean" "Fix/$m.lean" FX > "facts/sketch_info.$m.jsonl"
done
python3 "$REPO/scripts/prove2me/generate.py" --root "$W" --prefix Fix --facts facts \
  --out platform --plan plan.json --payload payload.json
export LEAN_PATH="$W/build:$W/pbuild"
python3 - <<'PY'
import json, os, subprocess, sys
p = json.load(open("payload.json"))
ok = True
for kind, key in (("Definitions", "definitions"), ("Theorems", "theorems"), ("Solutions", "solutions")):
    for item in p[key]:
        mod = item["module"]
        out = "pbuild/" + mod.replace(".", "/")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        r = subprocess.run(["lean", "-o", out + ".olean", "-i", out + ".ilean",
                            f"platform/{kind}/{mod.split('.')[-1]}.lean"], capture_output=True, text=True)
        if r.returncode != 0:
            ok = False
            print(f"FAIL {mod}\n{r.stdout}{r.stderr}")
print(f"compiled {sum(len(p[k]) for k in ('definitions', 'theorems', 'solutions'))} files")
sys.exit(0 if ok else 1)
PY
python3 "$REPO/scripts/prove2me/validate.py" --payload payload.json --source-root Fix --lean lean \
  --workdir "$W" --check-dir "$W/check" --jobs 4
