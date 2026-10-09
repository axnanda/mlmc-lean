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
- **Every other formal claim of both papers that follows from probability and algebra** (M5),
  except the items listed under "Not formalised" in M5 below: Giles §1–§3 (control variates,
  Richardson–Romberg MLMC and its complexity, multiple outputs, non-geometric MLMC and the subset
  search, Algorithms 1 and 2, the implementation checks), the pure steps of the applications in
  §5, §7, §8 (the Poisson coupling), §9 and §10, and Haas–Giles §2–§6 (the Euler–Maruyama
  coupling, approximate normals, the rounding-error model, the fixed-point path, the cost model
  and the bit-width optimisation). The README table lists the modules; `scripts/AxiomCheck.lean`
  lists the audited theorems.
- **Round 10 (2026-09-29): an independent coverage re-audit of both papers** (644 claims,
  `notes/coverage/`) found no misstatement; every claim it found missing or partial is now
  formalised or listed below with its reason (`notes/coverage/README.md`).
- **Round 11 (2026-09-29): verification.** All 139 theorems added in round 10 were read back
  blind by independent auditors (`notes/readbacks/README.md`, eleventh round): all true, none
  vacuous, none dependent on a junk value. `lake build` is warning-free and `scripts/local_ci.sh`
  passes: 53 modules, 565 audited theorems, each depending only on `propext`,
  `Classical.choice` and `Quot.sound`, and 565 validated prove2.me nodes.

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
- ✅ The weak convergence of the contracting chain to `X_∞` (§10.1, `MarkovLimit.lean`; it assumes
  a finite moment of the first step, which the paper does not state and which cannot be dropped,
  `MarkovNoWeakLimit.lean`, round 25) and the MSE of the lookup tables as `d → ∞` (Haas–Giles §3.4,
  `LUTLimits.lean`: `→ 0` for uniform intervals, bounded below by a positive constant for dyadic
  intervals).
- ✅ Geometric Brownian motion end to end (§5.1, Figure 5.3, `GBMEulerMaruyama.lean`): the
  strong error of Euler–Maruyama `E[(S_{t_n} − Ŝ_n)²] ≤ C(t_n) h` from the exact solution, the
  weak rate `α = ½` and the variance rate `β = 1` for Lipschitz payoffs, and Theorem 1 with no
  assumed rate (MSE `< ε²` at cost `O(ε⁻²(log ε)²)`).
- ✅ The Milstein scheme for geometric Brownian motion end to end (§5.2, Figure 5.5,
  `GBMMilstein.lean`): first-order strong convergence `E[(S_{t_n} − Ŝ_n)²] ≤ C(t_n) h²`, the weak
  rate `α = 1` and the variance rate `β = 2` for Lipschitz payoffs, and Theorem 1 with cost
  `O(ε⁻²)` and no assumed rate.
- ✅ Round 10: the claims the coverage re-audit found missing — ML2R's bias and complexity for
  the estimator itself (`ML2RTheorem.lean`), Theorem 2 on the explicit simplex, asymptotic
  normality (`AsymptoticNormal.lean`), random-shift QMC, the §2.2/§2.6/§5.2/§10.1 remarks
  (`GilesRemarks.lean`), the §5 probability steps (`SDEDigital.lean`, `SDEMisc.lean`), §6.2, §7,
  §10.2 (`ApplicationExtras.lean`), Poisson noise on union grids (`PoissonGrids.lean`), the limit
  law and MLMC for Markov chains (`MarkovLimitLaw.lean`), the §9 rates with discretised inner
  paths, a piecewise linear `f` and MIMC (`NestedRates.lean`), and the Haas–Giles §6 remarks
  (`HaasGilesRemarks.lean`).
- ✅ Round 12: the central limit theorem with a growing number of levels — the Lindeberg and
  Lyapunov CLTs for triangular arrays, asymptotic normality of the MLMC estimator under
  Lyapunov's condition, and Collier et al.'s confidence intervals with the exact variance
  (`MLMCCentralLimit.lean`); QMC in one dimension — error `O(N⁻¹)` for integrands of bounded
  variation, randomly shifted rank-1 lattices, and the MLQMC complexity `O(ε^{−p})`, `p < 2`
  (`QMC1D.lean`).
- ✅ Round 13: the consistency check with empirical variances, asymptotically, with the paper's
  `0.3%` failing for small samples (`ConsistencyCheck.lean`); nested simulation with a piecewise
  linear `f` and discretised inner paths: `α = 1`, `β = 3/2`, cost `O(ε^{−5/2})`, and a
  counterexample to the paper's MIMC rates `β₁ = β₂ = 1.5` for this case (`NestedKinkSde.lean`).
- ✅ Round 14: Collier et al.'s confidence intervals with estimated variances
  (`MLMCConfidenceEstimated.lean`); the corrected MIMC rates for a piecewise linear `f`,
  `V = O(2^{−ℓ₁−ℓ₂})` (sharp), and the cost `O(ε⁻²|log ε|⁴)` (`NestedMimcKink.lean`); the
  existence of the dyadic MSE limit `C > 0` and the order `2^{−d}/d` of the uniform MSE
  (Haas–Giles §3.4, `LUTAsymptotics.lean`).
- ✅ Round 15: for `dS = −S³dt + dW`, the moments of the explicit Euler–Maruyama scheme diverge
  as the timestep tends to `0` (Hutzenthaler–Jentzen–Kloeden), while the tamed scheme's second
  moment stays bounded (`EulerSuperlinear.lean`); the MLQMC boundary case `b = g ≤ a` costs
  `Θ(ε⁻¹|log ε|^{3/2})`, with lower bounds (`MLQMCBoundary.lean`).
- ✅ Round 16 (after an independent completeness spot-check, `notes/coverage/round15_spot_check.md`):
  nested MIMC with a smooth payoff end to end at cost `O(ε⁻²)` (`NestedMimcSmooth.lean`); the
  optimal bit-widths of Haas–Giles §6.1 exist without convexity and satisfy (35)
  (`BitWidthOptimum.lean`); the elliptic example of §7.1 with its finite-difference scheme solved
  exactly, `α = 2`, `β = 4` end to end (`EllipticFD.lean`); contracting SDEs with a fixed step, the
  lookup-table streams, refinement factor `M` and small corollaries (`GilesCorollaries.lean`).
- ✅ Round 17: Table 5.2's Asian and lookback rows for GBM with discrete monitoring, Euler–Maruyama
  and Milstein, Theorem 1 end to end (`GBMPathDependent.lean`); the mean-square stability analysis
  behind `k_ℓ = k_{ℓ−1}/4` in §7.3 (`SPDEStability.lean`); drift-implicit Euler and the integrating
  factor of §5.6 (`DriftImplicit.lean`); Brownian paths on union grids (Algorithm 3), the
  Brownian-bridge midpoint law and time reversal within coarse steps (`BrownianPaths.lean`).
- ✅ Round 18 (after a second completeness spot-check, `notes/coverage/round17_spot_check.md`): the
  digital option's fourth moments, the Milstein variance and `E[Pc] = E[Pf]` for the smoothed coarse
  payoff (`GBMDigital.lean`); tau-leaping against the exact chain, built by uniformisation, with
  weak order 1 for bounded payoffs and MLMC with the exact target (`TauLeapingExact.lean`); `Φ⁻¹` in
  Lean and the lookup-table results for it with no hypothesis on `f` (`InverseNormal.lean`); the
  elliptic estimator, the call, refinement factor `M` end to end, and small results
  (`EndToEndInstances.lean`).
- ✅ Round 19: the discrete parts of §6 (a discrete exponential-Lévy Asian analogue with `β = 2`,
  jump-adapted grids with random jump times, the thinning likelihood ratio; `JumpProcesses.lean`);
  the G2.1-36 counterexample, the consistency check with one or two samples, the variance of the
  sample variance (`EstimatorRemarks.lean`); drift-implicit Euler with multiplicative noise, the
  time-reversed path as a Brownian motion, several kinks (`SDEExtensions.lean`); contracting SDEs
  with level-dependent steps (`ContractingLevels.lean`).
- ✅ Round 20: `L^p` strong errors for GBM and the digital option's rates up to an arbitrarily
  small loss in the exponent (`GBMStrongLp.lean`); path-dependent (adaptive) grids on a base grid,
  with (2.4), Theorem 1 and Algorithm 3's coupling (`AdaptiveGrids.lean`); randomly shifted rank-1
  lattice rules in `d` dimensions and the MLQMC complexity with a level-dependent dimension
  (`LatticeRuleD.lean`); Theorem 1 with a polylogarithmic cost factor, which gives the contracting
  SDEs of §10.1 the cost `O(ε⁻²|log ε|³)` (`Theorem1Log.lean`).
- ✅ Round 21: weak order one of Euler–Maruyama for GBM with polynomial and smooth payoffs, and
  Theorem 1 with the paper's `α = β = γ = log₂ M` (`GBMWeakOrder.lean`); the GBM error uniformly
  over the grid and lookback options monitored at every time step (`GBMGridMax.lean`); the
  divergence theorem of Hutzenthaler, Jentzen and Kloeden for scalar coefficients
  (`EulerSuperlinearGeneral.lean`).
- ✅ Round 22 (after a spot-check of round 21 by two auditors,
  `notes/coverage/round17_spot_check.md`): Theorem 1 for the digital option of GBM at cost
  `O(ε^{−3−η})` (Euler–Maruyama) and `O(ε^{−2−η})` (Milstein), the barrier option at fixed
  monitoring dates, and splitting with a Milstein final step (`GBMDigitalTheorem1.lean`); small
  items of the spot checks: the ML2R bias `2^{−αL²}` is not attainable, the variance of the
  smoothed-CDF correction, the heat scheme with Dirichlet boundary values, nested inputs, `Θ(ε⁻³)`
  for standard nested Monte Carlo, the invariant law of the Ornstein–Uhlenbeck Euler chain, the
  corrected inputs of §10.2 and `V_ℓC_ℓ` in Haas–Giles §2.1 (`SpotCheckRemarks.lean`); the parabolic
  example of §7.1 end to end (`ParabolicExample.lean`); nested simulation with inner time steps for
  curved pieces and several kinks, and MIMC on the two axes for the kink counterexample
  (`NestedKinkCurved.lean`); tau-leaping against the exact chain for Lipschitz payoffs, and with
  state-dependent propensities on adaptive grids (`TauLeapingExtensions.lean`).
- ✅ Round 23: the conditional-expectation estimator of the digital option for GBM, with the
  conditional laws of the fine and the coarse path matching to `O(h)`, `V_ℓ = O(h^q)` for every
  `q < 3/2`, the weak rate `q < 1`, zero variance on level `0`, Theorem 1 at the paper's cost
  `O(ε⁻²)` and splitting at the same rate (`GBMDigitalCondExp.lean`); tau-leaping coupled with the
  exact chain on the finest level, an unbiased multilevel estimator at expected cost `O(ε⁻²)` with a
  fixed number of levels (`TauLeapingSSA.lean`); the truncated Karhunen–Loève field with Mercer's
  expansion as hypotheses: the level correction, the truncation error, the pointwise law, uniform
  moments of the diffusivity and the covariance (`KarhunenLoeve.lean`); when the change-of-measure
  correction of §5.2 has finite variance (`ChangeOfMeasureVariance.lean`).
- ✅ Round 24: the small-jump truncation of §6.2 for the terminal value of a pure-jump Lévy process:
  the large jumps as compound Poisson variables, (2.4), the correction variance from the
  intermediate range of jump sizes, the `L²` limit and the bias as `δ_ℓ → 0`, the expected cost, and
  Theorem 1 with `δ_ℓ = 2^{−ℓ}`, including a one-sided stable-like example at cost `O(ε⁻²)`,
  `O(ε⁻²(log ε)²)` or `O(ε^{−2Y/(2−Y)})` (`LevyTruncation.lean`); the untruncated Karhunen–Loève
  field of §7.2 with Mercer's expansion as hypotheses: almost sure convergence, its Gaussian law,
  covariance and joint Gaussianity, the lognormal moments of the diffusivity and their convergence,
  and that the diffusivity is unbounded (`KarhunenLoeveLimit.lean`); sensitivities for GBM (§5.4):
  the pathwise delta of the call with upper bounds at the digital option's variance rates and
  Theorem 1 at cost `O(ε^{−3−η})` (Euler–Maruyama) and `O(ε^{−2−η})` (Milstein), and the digital
  delta from the conditional-expectation payoffs, unbiased and with (2.4) (`GBMSensitivities.lean`);
  after the round-23 read-back, `variance_ssaCorrection_exact_le` states that its sampling law is a
  probability measure.
- ✅ Round 25 (after a spot-check of round 24 by two auditors,
  `notes/coverage/round17_spot_check.md`): the conditional-expectation estimator of the digital
  option for the strike `K = 0` (corrections `O(h^q)` for every `q`), hence its variance rate and
  Theorem 1 for every strike, and Theorem 1 for the splitting estimator with `⌈h_ℓ^{−1/2}⌉`
  sub-samples at cost `O(ε⁻²)` (`GBMDigitalCondExpExtras.lean`); tau-leaping with Lipschitz
  propensities of linear growth: the moments of the chain, the `O(h)` correction variance and
  Theorem 1 given the weak rate, and for the linear birth rate `λ(x) = cx` with `Φ(x) = x` Theorem 1
  with no assumed rate (`TauLeapingLinearGrowth.lean`); Theorem 1 in a Banach space with the type-2
  inequality as a hypothesis, which holds for Hilbert spaces, spaces isomorphic to a subspace of one
  and finite-dimensional spaces (`BanachTheorem1.lean`); the random digital shift of QMC points:
  unbiased, with i.i.d. replicates, and fair binary digits are uniform on the unit cube
  (`DigitalShiftQMC.lean`); the small jumps of §6.2 replaced by a Brownian term, with Theorem 1 at
  the rates of the truncation, and Table 6.3's Asian row for Variance-Gamma laws with no assumption
  left (`LevyExtras.lean`); a counterexample showing that the weak convergence claimed in §10.1
  needs a moment condition on one step (`MarkovNoWeakLimit.lean`). The spot-check's documentation
  fixes are the "Round 25" notes in the coverage tables; stale module docstrings were corrected.
- ✅ Round 26 (three more items from the spot-check-24 lists,
  `notes/coverage/round17_spot_check.md`): the digital option for GBM with Euler–Maruyama at the
  endpoint of Table 5.2's analysis column: the mismatch probability, `V_ℓ` and `E[(ΔP)⁴]` are
  `O((h log(1/h))^{1/2})`, hence `O(h^{1/2} log h)`, uniformly in `S₀` and `K`, from Gaussian-type
  tails of the log error (`GBMDigitalEndpoint.lean`); the exact halving of the method-1 MSE of
  `Φ⁻¹` per bit, `MSE(d + 1)/MSE(d) → ½`, from `MSE(d) ~ κ 2^{−d}/d` with
  `κ = (∑_{j≥0} V_j)/log 2 ≈ 1.5586` (Haas–Giles §3.4, `LUTHalving.lean`); the variance of the
  digital-delta corrections of §5.4 for GBM, `V_ℓ = O(h^q)` for every `q < ½`
  (`GBMDigitalDeltaVariance.lean`). Module docstrings that called these unproved were corrected.
- Not formalised (each with its reason in `notes/coverage/README.md`): the convergence orders of the
  discretisations of general SDEs, SPDEs and PDEs (Itô calculus and PDE regularity are not in
  Mathlib; the SPDE of §7.3 has multiplicative noise and an absorbing boundary; proved for geometric
  Brownian motion from its exact solution, including weak order one for smooth and polynomial
  payoffs) and of QMC in `d` dimensions (discrepancy theory and the existence of good lattices; the
  one-dimensional case, and in `d` dimensions the variance of shifted lattice rules and the MLQMC
  complexity given the decay of the dual-lattice sums, are proved); for the parabolic example of
  §7.1, the identification of the limit of the level means with the SPDE functional
  `E ∫₀¹ u(x, ¼)² dx` (a stochastic integral) and the strong error `O(2^{−2ℓ})` (its rates `α = 2`,
  `β = 4` and Theorem 1 at cost `O(ε⁻²)` are proved); the optimality of the simplex among all MIMC
  index sets; the adaptive, stopped algorithm of Collier et al. (their confidence intervals for
  deterministic numbers of levels and samples are proved); the kurtosis upper bounds of the digital
  option, the endpoints of its rates `O(h^{1/2})`, `O(h)` (every smaller exponent is proved for GBM
  from `L^p` strong errors, and with Euler–Maruyama the endpoint up to a factor `(log(1/h))^{1/2}`,
  i.e. Table 5.2's analysis rate `O(h^{1/2} log h)`, from the tails of the log error), and its weak
  rate `α = 1`, hence the paper's `O(ε^{−2.5})` (Theorem 1 at cost `O(ε^{−3−η})`, and
  `O(ε^{−2−η})` with Milstein, is proved for GBM); for the
  conditional-expectation estimator of the digital option, the endpoints `β = 3/2` and `α = 1`, the
  kurtosis `O(h^{−1/2})` and, for the strike `K = 0`, that the corrections are exponentially small
  (every `q < 3/2`, resp. `q < 1`, and Theorem 1 at the paper's cost `O(ε⁻²)` are proved for GBM and
  every strike, and for `K = 0` the corrections are `O(h^q)` for every `q`), and for splitting the
  variance "the same, to leading order" as with the conditional expectation (the same rate, and
  Theorem 1 at cost `O(ε⁻²)` with `⌈h_ℓ^{−1/2}⌉` sub-samples, are proved, with an Euler–Maruyama
  final step); for the change-of-measure estimator, finite variance after averaging over the paths
  and its variance rate (finite variance for fixed conditional laws is proved, when the sampling
  variance exceeds half of the fine and the coarse one); continuously monitored path-dependent
  payoffs (Brownian-bridge extremes), and the barrier option monitored at every time step, whose
  variance `O(h^{1/2})` (§5.2, p. 38) needs a small-ball bound for the grid maximum near the
  barrier, uniform in the number of steps (for GBM, Asian and lookback options and the barrier
  option at fixed monitoring dates, and lookback options monitored at every time step, are proved);
  real-valued adaptive step sizes (Brownian motion at stopping times; deterministic union grids and
  adaptive steps on a base grid are proved); for tau-leaping on adaptive grids, the variance rate of
  the coupling and time-dependent propensities ((2.4) with state-dependent propensities on a base
  grid is proved), tau-leaping's weak rate for unbounded propensities or payoffs of super-linear
  growth (bounded propensities with bounded or Lipschitz payoffs are proved; for Lipschitz
  propensities of linear growth the moments of the chain, the `O(h)` correction variance and
  Theorem 1 given the weak rate are proved, and for the linear birth rate `λ(x) = cx` with
  `Φ(x) = x` also the weak rate against the limit of the tau-leaping means and Theorem 1 with no
  assumed rate); the exact (SSA) coupling on the finest level for several reactions, unbounded
  propensities or unbounded payoffs, and the random cost of the exact level (one reaction with a
  bounded propensity and a bounded payoff, coupled by uniformisation, is proved: the estimator is
  unbiased and costs `O(ε⁻²)` in expectation with a fixed number of levels); the comparison of the
  explicit scheme with the exact solution for super-linear coefficients, and several dimensions (the
  divergence of the scheme's moments is proved for scalar coefficients); the jump-diffusion and
  Lévy-process theory of §6 beyond grid values and terminal values (the Poisson and Lévy processes
  themselves, path-dependent Lévy payoffs, Table 6.3 beyond its Asian row for Variance-Gamma laws
  (the NIG and spectrally negative α-stable columns need laws Mathlib does not have, the lookback
  and barrier rows fluctuation theory), the Lévy–Khintchine law of the limit of the truncated
  levels (not yet formalised, though reachable from `charFun_cpSum`), Dereich's improved bias for the Brownian replacement of the small jumps, and bounds on the
  realised rather than the expected cost; the discrete parts are proved, and so are the small-jump
  truncation for the terminal value of a pure-jump Lévy process, with Theorem 1 for `δ_ℓ = 2^{−ℓ}`
  and a one-sided stable-like example, the Brownian replacement of the small jumps with the same
  rates, and the Asian row of Table 6.3 for Variance-Gamma laws, with exactly simulated increments
  and the trapezoidal average); Mercer's theorem behind the Karhunen–Loève expansion, the
  identification of the joint law of the limit field with a multivariate Gaussian (this needs no
  spectral theory: Mathlib has `multivariateGaussian`; not yet formalised), the regularity of
  `κ` and the moments of `max_x κ` and `1/min_x κ`, and the finite-element analysis of §7.2
  (spectral theory of covariance operators and elliptic regularity; with Mercer's expansion as a
  hypothesis the truncation error, the pointwise law, the moments and the covariance of the
  truncated field are proved, and for the untruncated field the almost sure convergence, the
  Gaussian law, joint Gaussianity, the covariance, the moments of `κ` and that it is unbounded, and
  (2.4) for nested inputs `ξ_ℓ = (ξ_{ℓ−1}, z_ℓ)`); for the sensitivities of §5.4, the endpoint
  `q = ½` of the variance rate of the digital-delta corrections (the paper states no rate and defers
  to Burgos 2014; every `q < ½` is proved for GBM) and Theorem 1 for them (it needs the convergence
  of the density of the discretised `S_T` at the strike), sensitivities for general SDEs and Greeks
  other than the delta (they need the SDE's tangent process), and lower bounds behind "similar
  difficulties" (for GBM the pathwise delta of the call, with upper bounds matching the digital
  option's rates and costs, and the unbiased digital delta from the conditional-expectation payoffs,
  with the variance rate of its corrections, are proved); that the limit of the discretised
  contracting chains is the SDE's invariant law (§10.1; fixed and level-dependent steps are proved
  for the discretised chains, and for the Ornstein–Uhlenbeck SDE the invariant laws of the scheme
  tend to `N(0, σ²/(2κ))`); for the weak convergence of contracting Markov chains (§10.1),
  conditions weaker than the finite first-step moment `E[d(x₀, φ(x₀, ξ))^p] < ∞` that the Lean
  statements assume, such as a logarithmic moment, and the need for a complete space (that the
  paper's claim fails without any moment condition is proved, `hc_cannot_be_dropped`); the value of
  the dyadic limit `C` (Haas–Giles §3.4; the existence of `C > 0` is proved for `Φ⁻¹`, and so is the
  exact halving of the method-1 MSE per bit as a limit, `MSE(d + 1)/MSE(d) → ½`, with the constant
  `κ` of `MSE(d) ~ κ 2^{−d}/d` as a series, not in closed form); whether MIMC reaches `O(ε⁻²)` for
  a general piecewise linear `f` (the paper's rates are refuted, the corrected rates give
  `O(ε⁻²|log ε|⁴)`, and for the counterexample itself MIMC on the two axes reaches `O(ε⁻²)`).
  Further claims that need theory Mathlib lacks, such as Creutzig et al.'s lower bound, type 2 for
  Banach spaces not isomorphic to a Hilbert space (Theorem 1 with type 2 as a hypothesis, and type 2
  for spaces isomorphic to a subspace of a Hilbert space, are proved), Owen's scrambling of Sobol
  points, their construction and QMC error rates (the random digital shift is proved), Feynman–Kac
  and exit times, the Clark–Cameron bound and the Giles–Szpruch analysis, are in the out-of-scope
  table of `notes/coverage/README.md`, and a few minor sub-claims that are provable but not
  formalised are noted in the rows of the coverage tables. The remaining claims are numerical or
  empirical (measured rates, figures, run times), hardware facts, citations or informal remarks.

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
