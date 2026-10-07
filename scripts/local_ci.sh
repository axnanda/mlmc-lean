#!/bin/bash
# The steps of .github/workflows/lean_action_ci.yml, for running where GitHub Actions is not
# available (for example when the free minutes are used up).  Run `lake exe cache get` first (see
# CLAUDE.md), then, from anywhere:
#
#   bash scripts/local_ci.sh
#
# Steps: uploader tests, `lake build`, the generator regression fixture, the axiom audit (only
# propext, Classical.choice and Quot.sound may appear), the prove2.me facts, the platform tree
# (generate, build, validate) and the dry runs of the uploader and the proposals.
set -eo pipefail
cd "$(dirname "$0")/.."

echo "== prove2.me uploader tests"
python3 scripts/prove2me/test_upload.py

echo "== lake build"
lake build

echo "== prove2.me generator regression test (fixture)"
bash scripts/prove2me/fixture/run.sh

echo "== axiom audit"
axioms=$(mktemp)
trap 'rm -f "$axioms"' EXIT
lake env lean scripts/AxiomCheck.lean | tee "$axioms"
if grep -q "sorryAx" "$axioms"; then echo "sorry found"; exit 1; fi
ok='(propext|Classical\.choice|Quot\.sound)'
# Lean wraps the axiom list of a long theorem name over several lines: join them first
if sed -E ':a;N;$!ba;s/,\n[[:space:]]+/, /g' "$axioms" | grep "depends on axioms" |
    grep -vE "depends on axioms: \[$ok(, $ok)*\][[:space:]]*$"; then
  echo "unexpected axioms"; exit 1
fi

echo "== prove2.me facts (Stage 1 declaration graph, Stage 2 sketch facts)"
mkdir -p facts
lake env lean scripts/prove2me/extract_decl_graph.lean
mv decl_graph.jsonl facts/
for f in MlmcLean/*.lean; do
  m=$(basename "$f" .lean)
  if ! lake env lean --run scripts/prove2me/extract_sketch_info.lean "$f" MLMC \
      > "facts/sketch_info.$m.jsonl"; then
    cat "facts/sketch_info.$m.jsonl"; exit 1
  fi
done
wc -l facts/*

echo "== prove2.me platform tree (generate, build, validate)"
python3 scripts/prove2me/generate.py --facts facts --out prove2me/platform \
  --payload prove2me/payload.json
lake build Definitions Theorems Solutions
python3 scripts/prove2me/validate.py --jobs 4
python3 scripts/prove2me/upload.py --dry-run
python3 scripts/prove2me/propose.py --dry-run

echo "== all steps passed"
