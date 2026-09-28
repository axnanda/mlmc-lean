# Plan: formalising MLMC complexity bounds in Lean 4

**Goal.** Machine-checked Lean 4 + Mathlib proofs of the multilevel Monte Carlo (MLMC) complexity
bounds, stated as in the papers and with zero `sorry`, building on what is already proven here.

## Fresh start (read first)

- **Start from scratch.** Don't rely on, search for, or try to reconstruct previous Claude
  sessions or chats, and don't use AI-written summaries of the papers. Nothing from earlier
  sessions carries over.
- **Sources of truth:** the papers in `docs/` (Giles 2015 and Haas–Giles 2025, including the
  LaTeX source) and what you can verify yourself in this repo (`lake build` plus the axiom
  audit).
- **Treat everything else as unverified:** the Status section below, README claims and `notes/`
  are leads to check, not facts. `notes/` is optional background and isn't needed for M0–M3.

## Status (2026-09-27; re-verified in M0; CI builds and audits every push)

Proved with zero `sorry` and only `propext`, `Classical.choice`, `Quot.sound` (see the README
table and `notes/statement-audit.md`, which compares every statement with the papers):
- **Giles (2015) Theorem 1** on a probability space with random costs (`giles_theorem1`), its
  deterministic core (`mlmc_complexity_core`), big-O forms, and the theorem for the estimator
  (2.2) built from independent samples (`giles_theorem1_standard`, `giles_theorem1_iid`).
- **Eq. (1.1), (2.1)–(2.3)** and the optimal sample allocation, with its unique minimiser, the
  dual (fixed-cost) problem and the two-level ratio of §1.2 (`MlmcLean/Allocation.lean`,
  `MlmcLean/Estimator.lean`); (2.3) for the estimator (2.2) itself
  (`mlmcEstimator_mean_variance`).
- **Randomised MLMC**, Giles §2.2 (`MlmcLean/Randomised.lean`), including the expected cost per
  sample, the necessity of both series, the estimator with `N` samples and the optimal level
  distribution as a minimiser.
- **Giles (2015) Theorem 2 (MIMC)** in the paper's form (`giles_theorem2_full`: exponents exist
  for `α_d ≥ ½β_d` and are the paper's when every `α_d > ½β_d`), for every dimension and all
  three regimes (`giles_theorem2`, `giles_theorem2_boundary`), and the telescoping sum
  `E[P] = ∑_{ℓ≥0} E[ΔP_ℓ]` (`hasSum_integral_crossDiff`).
- **Haas–Giles (2025) nested estimator, eq. (9)–(12)** (`MlmcLean/Nested.lean`): (12) as the
  least nested cost, the claimed saving factor as an inequality, and the estimator built from
  independent inputs with its mean, variance and expected cost.
- **Every other formal claim of both papers that follows from probability and algebra** (M5):
  Giles §1–§3 in full (control variates, Richardson–Romberg MLMC and its complexity, multiple
  outputs, non-geometric MLMC and the subset search, Algorithms 1 and 2, the implementation
  checks), the pure steps of the applications in §5, §7, §8 (the Poisson coupling), §9 and §10,
  and Haas–Giles §2–§6 (the Euler–Maruyama coupling, approximate normals, the rounding-error
  model, the fixed-point path, the cost model and the bit-width optimisation). The README table
  lists the modules; `scripts/AxiomCheck.lean` lists the 408 audited theorems.

## Setup and verification (Linux / cloud session)

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
source "$HOME/.elan/env"
lake exe cache get                      # Mathlib cache from cache.mathlib.org (must be reachable;
                                        # building Mathlib from source takes hours)
lake build                              # this project: ~1–2 min once the cache is in place
lake env lean scripts/AxiomCheck.lean   # each theorem: [propext, Classical.choice, Quot.sound] only
```

The pins are Lean `v4.33.1` and Mathlib `0df444a` (see `lake-manifest.json`): the default
verification environment of prove2.me, so that every file compiles exactly as on the platform's
servers (the build also uses the platform's `autoImplicit = false`). Don't bump them unless the
platform does; `scripts/prove2me/upload.py` checks that the environment is still offered.

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

**M0: Re-verify everything independently (first).** ✅ Done 2026-09-25: build and axiom audit
green in CI; `notes/statement-audit.md` records five deviations found and fixed (miscited
equation numbers, condition (ii) at `n = 0`, `E[C]` instead of `∑ N_ℓ C_ℓ`, and Theorem 1 for the
actual estimator (2.2)) and audits every later milestone the same way.
- Run the setup above. The build and axiom audit must pass, and GitHub Actions must be green on
  `master`.
- Audit statement fidelity from scratch. For each main theorem in `scripts/AxiomCheck.lean`,
  read the matching statement in the paper (Giles 2015 Theorem 1 and §2; Haas–Giles eq. 9–12)
  and check that the Lean hypotheses and conclusion match it. A proof that compiles shows the
  Lean statement is true, not that it is the paper's statement.
- Write the result to `notes/statement-audit.md` (paper statement, Lean statement, deviations).
  Fix or document every deviation before starting M1.

**M1: Polish the existing results (small).** ✅ Done: `giles_theorem1` bounds `E[C]` for random
costs; `giles_theorem1_isBigO`; eq. (1.1) optimality `optimal_cost_isLeast`; Theorem 1 for the
estimator (2.2) built from i.i.d. samples (`giles_theorem1_standard`, `giles_theorem1_iid`).
- Asymptotic corollaries of Theorem 1: each regime as an `Asymptotics.IsBigO` statement as
  ε → 0⁺ (`𝓝[>] 0`).
- Random per-sample cost with expectation `C_ℓ`, as Giles allows. This closes a gap listed in
  the README's modelling choices.
- Done when: the new statements are in `AxiomCheck.lean` and the README table is updated.

**M2: Randomised (single-term) MLMC (Giles 2015 §2.2; Rhee & Glynn).** ✅ Done
(`MlmcLean/Randomised.lean`). Note: the paper only claims the two *necessary* series are finite
for `β > γ`; the full variance can diverge under (i)–(iv) alone (counterexample in
`notes/statement-audit.md`), so finiteness is proved under the second-moment form of (iii).
- Prove unbiasedness `E[Y] = E[P]` under the paper's conditions, plus the second-moment/variance
  formula.
- Prove that with `β > γ` and `p_ℓ ∝ 2^{−(β+γ)ℓ/2}`, both the variance and the expected cost are
  finite.
- Done when: the statements match §2.2, with zero `sorry`.

**M3: Multi-Index Monte Carlo (Giles 2015 §2.4, Theorem 2; Haji-Ali, Nobile & Tempone).**
✅ Done: `giles_theorem2` (all `D`, all three regimes, the paper's `e₁ = 2D₂`,
`e₂ = (D₂−1)(2+η)` for `α_d > ½β_d`) and `giles_theorem2_boundary` (`α_d ≥ ½β_d`, where the paper
leaves the exponents open, with `e₁ = 2D₂ + (D₃−3)⁺`, `e₂ = (D₂−1)(2+η) + (D₃−1)⁺` where
`D₃ = #{d : α_d = ½β_d}`; these are the paper's exponents when `D₃ = 0`).
- Start with the η < 0 case, then η = 0 and η > 0 with the `|log ε|` exponents `e₁`, `e₂`.
- The hard part is summing over index sets `{ℓ : δ·ℓ ≤ L}` (lattice-point counting).
- Done when: Theorem 2 is proved as stated, or a clearly documented subset is (e.g. D = 2 first).

**M5: Every formal claim of the papers, and a full review.** ✅ Done 2026-09-27, except the
items listed under "Not formalised" below.
- ✅ Independent review of all modules; every finding fixed (docstrings, citations, truncated
  exponents, hypotheses for `n ≥ 1`, unused hypotheses and deprecated tactics removed).
- ✅ Theorem 2 in the paper's form (`giles_theorem2_full`) and the MIMC telescoping sum.
- ✅ §1.2–1.3: unique optimal allocation, the fixed-cost dual, the two-level ratio.
- ✅ §2.2: expected cost per sample, necessity of both series, `N`-sample estimator, optimal
  level probabilities as a minimiser.
- ✅ Haas–Giles §2.2: (12) as the least cost, the saving factor, the estimator from samples.
- ✅ §1.1–§1.3 control variates and cost comparisons; §2.1 remarks; §2.3 Richardson extrapolation,
  ML2R and its complexity; §2.5 multiple outputs; §2.6 non-geometric MLMC (the subset cost, the
  exhaustive search, the test (2.5)); §2.4 Figure 2.1 and the rectangular index set.
- ✅ §3: Algorithm 1 and Algorithm 2 (MLQMC) with exact values (termination, variance target,
  MSE), the driver's estimates, the consistency check, the kurtosis.
- ✅ Applications, the parts that need no SDE/PDE theory: §5 (Euler–Maruyama coupling, rates from
  the timestep, conditional expectations, Brownian-bridge midpoint, antithetic swap, splitting,
  explicit-step stability, smoothed CDF, density limit), §7.1, §8 (tau-leaping, the Poisson
  coupling and its correction variance `O(h)`), §9 (nested simulation, the `−1/8` constant), §10.1 (contraction, variance decay, the
  uniform invariant law).
- ✅ Haas–Giles §2–§6: the Euler–Maruyama coupling (4)–(5), approximate normals (13)–(19), the
  rounding-error model (20)–(29) (with the corrections recorded in `notes/statement-audit.md`),
  Algorithm 1 and the error accumulation, the cost model and the bit-width optimisation
  (30)–(41).
- ✅ Theorem 1 for tau-leaping MLMC with the Poisson coupling (§8, `TauLeapingMLMC.lean`): the
  payoffs are square integrable, (2.4) holds, `β = 1` on every level, and the estimator reaches
  MSE `ε²` at cost `O(ε⁻²(log ε)²)` given the weak rate `α ≥ ½` (a property of the exact chain).
- ✅ The weak convergence of the contracting chain to `X_∞` (§10.1, `MarkovLimit.lean`) and the
  MSE of the lookup tables as `d → ∞` (Haas–Giles §3.4, `LUTLimits.lean`: `→ 0` for uniform
  intervals, bounded below by a positive constant for dyadic intervals).
- ✅ Geometric Brownian motion end to end (§5.1, Figure 5.3, `GBMEulerMaruyama.lean`): the
  strong error of Euler–Maruyama `E[(S_{t_n} − Ŝ_n)²] ≤ C(t_n) h` from the exact solution, the
  weak rate `α = ½` and the variance rate `β = 1` for Lipschitz payoffs, and Theorem 1 with no
  assumed rate (MSE `< ε²` at cost `O(ε⁻²(log ε)²)`).
- ✅ The Milstein scheme for geometric Brownian motion end to end (§5.2, Figure 5.5,
  `GBMMilstein.lean`): first-order strong convergence `E[(S_{t_n} − Ŝ_n)²] ≤ C(t_n) h²`, the weak
  rate `α = 1` and the variance rate `β = 2` for Lipschitz payoffs, and Theorem 1 with cost
  `O(ε⁻²)` and no assumed rate.
- Not formalised: the convergence orders of the discretisations for general SDEs (Itô calculus,
  not in Mathlib; proved for geometric Brownian motion from its exact solution)
  and of QMC; for tau-leaping (§8), the weak rate `α = 1` against the exact chain and the exact
  (SSA) coupling on the finest level, which need the continuous-time chain itself; Algorithm 3
  with path-dependent timesteps (§5.6, needs Brownian motion at stopping times); the value of the
  dyadic limit `C` and the rate "MSE halves per bit" (Haas–Giles §3.4, need the asymptotics of
  `Φ⁻¹`); the floating-point remark of §10.2; the remaining claims are numerical or empirical
  (tables, figures, run times).

**M4: Research, needs Alex's sign-off before formalising: nested MLMC with level-dependent
precision.**
- Write the theorem on paper in `notes/` first: the cost model `C̃_ℓ(d)` and correction-variance
  model `V^Δ_ℓ(d)` (Haas–Giles §4–6), the optimal precision schedule `d_ℓ`, and the resulting
  ε-complexity and constant-factor gain over Theorem 1.
- Check Sheridan-Methven & Giles (2024) first; part of this may already exist.
- Then formalise, reusing `Allocation.lean` and `Nested.lean`.

## Out of scope

- **Proving the rate assumptions (α, β, γ) for Euler–Maruyama or Milstein for general SDEs.**
  This needs Itô calculus, which Mathlib doesn't have. The theorems stay conditional on
  assumptions (i)–(iv), exactly as in the papers. (For geometric Brownian motion the rates are
  proved from the explicit solution: `GBMEulerMaruyama.lean`, `GBMMilstein.lean`.)
- **Hardware and benchmark work** (see `notes/research-notes.md` §5).

## prove2.me

The platform's upload standard (prove2me_workspace `upload_full_project.md`) is implemented in
`scripts/prove2me/`: Lean extractors for the declaration graph and per-file facts, a generator
that builds the `Definitions/Theorems/Solutions` tree by skeleton subtraction, a validator (stub
types equal the source types; every solution has exactly its stub's type; no `sorry`), and an
idempotent, private-by-default uploader. CI runs all of it on every push and prints the size of
the tree in its plan summary (theorem nodes: the main theorems and the long or shared lemmas, all
in the axiom audit; one definition bundle per module with definitions; inlined helpers); the tree
validates with 0 failures.
`prove2me/metadata.json` holds the titles, natural-language statements, sources and proof
explanations; `prove2me/proposals/` the mission proposals for Theorems 1 and 2 (`propose.py`).
Uploading needs an account API key (CI's opt-in `upload` job, or `upload.py` locally); making the
tree public is irreversible and waits for Alex.

## Open questions for Alex

- Whether to make the uploaded tree public, and whether to launch the mission proposal.
