# Plan: formalising MLMC complexity bounds in Lean 4

**Goal.** Machine-checked Lean 4 + Mathlib proofs of the multilevel Monte Carlo (MLMC) complexity
bounds, stated as in the papers and with zero `sorry`, building on what is already proven here.

## Status (2026-09-24)

These are done and axiom-clean (see the README table and "Modelling choices"):
- **Giles (2015) Theorem 1:** `MLMC.giles_theorem1`, on a probability space, and
  `MLMC.mlmc_complexity_core`, the deterministic core with all three regimes and an explicit c₄.
- **Optimal sample allocation:** the Cauchy–Schwarz lower bound and the rounded-up integer
  allocation (`MlmcLean/Allocation.lean`).
- **Haas–Giles (2025) nested estimator, eq. (9)–(12):** `MlmcLean/Nested.lean`.

## Setup and verification (Linux / cloud session)

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
source "$HOME/.elan/env"
lake exe cache get                      # Mathlib cache from cache.mathlib.org (must be reachable;
                                        # building Mathlib from source takes hours)
lake build                              # this project: ~1–2 min once the cache is in place
lake env lean scripts/AxiomCheck.lean   # each theorem: [propext, Classical.choice, Quot.sound] only
```

The pins are Lean `v4.35.0-rc2` and the Mathlib tag `v4.35.0-rc2` (see `lake-manifest.json`).
Don't bump them unless blocked.

## Ground rules

- **No shortcuts:** no `sorry`, `admit`, new `axiom`s or `native_decide`. Add every new main
  theorem to `scripts/AxiomCheck.lean`. CI runs the build plus this audit.
- **Stay close to the papers:** state theorems as the papers do and cite the paper and
  equation/theorem number in each docstring. Record any deviation under "Modelling choices" in
  the README.
- **Targeted imports:** list the specific Mathlib modules each file needs (not `import Mathlib`)
  so builds stay fast.
- **Branches:** one branch and one draft PR per milestone; never push to `master`.

## Milestones

**M0: Verify the baseline (first).** Run the setup above. The build and axiom audit must be green
before any change, and GitHub Actions must be green on `master`.

**M1: Polish the existing results (small).**
- Asymptotic corollaries of Theorem 1: each regime as an `Asymptotics.IsBigO` statement as
  ε → 0⁺ (`𝓝[>] 0`).
- Random per-sample cost with expectation `C_ℓ`, as Giles allows. This closes a gap listed in
  the README's modelling choices.
- Done when: the new statements are in `AxiomCheck.lean` and the README table is updated.

**M2: Randomised (single-term) MLMC (Giles 2015 §2.2; Rhee & Glynn).**
- Prove unbiasedness `E[Y] = E[P]` under the paper's conditions, plus the second-moment/variance
  formula.
- Prove that with `β > γ` and `p_ℓ ∝ 2^{−(β+γ)ℓ/2}`, both the variance and the expected cost are
  finite.
- Done when: the statements match §2.2, with zero `sorry`.

**M3: Multi-Index Monte Carlo (Giles 2015 §2.4, Theorem 2; Haji-Ali, Nobile & Tempone).**
- Start with the η < 0 case, then η = 0 and η > 0 with the `|log ε|` exponents `e₁`, `e₂`.
- The hard part is summing over index sets `{ℓ : δ·ℓ ≤ L}` (lattice-point counting).
- Done when: Theorem 2 is proved as stated, or a clearly documented subset is (e.g. D = 2 first).

**M4: Research, needs Alex's sign-off before formalising: nested MLMC with level-dependent
precision.**
- Write the theorem on paper in `notes/` first: the cost model `C̃_ℓ(d)` and correction-variance
  model `V^Δ_ℓ(d)` (Haas–Giles §4–6), the optimal precision schedule `d_ℓ`, and the resulting
  ε-complexity and constant-factor gain over Theorem 1.
- Check Sheridan-Methven & Giles (2024) first; part of this may already exist.
- Then formalise, reusing `Allocation.lean` and `Nested.lean`.

## Out of scope

- **Proving the rate assumptions (α, β, γ) for Euler–Maruyama or Milstein.** This needs Itô
  calculus, which Mathlib doesn't have. The theorems stay conditional on assumptions (i)–(iv),
  exactly as in the papers.
- **Hardware and benchmark work** (see `notes/research-notes.md` §5).

## Open questions for Alex

- The prove2me submission format and requirements (which theorems, what packaging).
- Priority between M2 and M3 once M1 is done.
