# Instructions for Claude sessions in this repo

This is a Lean 4 + Mathlib formalisation of multilevel Monte Carlo (MLMC) complexity bounds. Read
`PLAN.md` (milestones and ground rules) and `README.md` (what is proved, modelling choices) before
changing anything.

## Build and verify

```bash
lake exe cache get                      # never build Mathlib from source; cache host: cache.mathlib.org
lake build
lake env lean scripts/AxiomCheck.lean   # may only list propext, Classical.choice, Quot.sound
```

## Rules

- No `sorry`, `admit`, new `axiom`s or `native_decide`. Add every new main theorem to
  `scripts/AxiomCheck.lean`.
- Keep Mathlib imports targeted (not `import Mathlib`). Cite the paper and the equation or
  theorem number in each docstring.
- Use one branch and one draft PR per milestone, and never push to `master`. Keep CI green.
- Tick off milestones in `PLAN.md` as they land.
- `experiments/`, `notes/` and `docs/` are not part of the Lean build. Don't edit experiment
  results unless you re-run the scripts.
