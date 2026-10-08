# Completeness spot-check after round 17 (2026-10-07)

Two independent auditors re-read Giles (2015) §1–§5, and Giles (2015) §6–§11 with all of
Haas–Giles (2025), against the coverage tables and the Lean statements themselves. They mapped
every line of the papers to rows with a script and checked that every cited name exists. They
also read the exact types (`#check`) of about 130 rows marked DONE, DONE-DEV or resolved in rounds
12–17.

**Claims missing from the tables.** None is substantive. The round-15 gaps (time reversal,
Gaussian union grids, the deterministic drift-implicit analogue) were closed in round 17. Not
tracked separately: existence of the least-squares minimiser in Haas–Giles §3.2 (assumed as `hx`
by `alternating_min_*`).

**Lean misstatements.** None: every checked statement says what the paper says, or states a
documented special case or corrected version of it.

**Rows and documentation corrected.**

| Item | Was | Now |
|---|---|---|
| G5.2-18 | DONE | PARTIAL: `integral_condExp_eq_of_map_eq` assumes the law equality that is the claim |
| G7.1-07, -17, -18, G7.3-08 | DONE / DONE-DEV | PARTIAL: only the complexity bound is evaluated |
| G5.2-09, G5.1-08 notes | stale | `digital_mismatch_le` exists; discrete monitoring needs only the dates |
| `GilesRemarks.lean` header | "zero variance on the coarsest level" not stated | `digital_smoothing_level_zero` |
| README, tamed scheme | `E X_N² ≤ x₀² + T` "uniformly in `N`" | for `N ≥ T/54` (`tamedCubic_second_moment_le` assumes `T ≤ 54N`) |
| G9.2-12 resolution | hypotheses incomplete | adds `f″` Lipschitz and fourth moments bounded uniformly in `ℓ` |
| G9.2-13/-14 resolution, statement audit | "the true rates are `β₁ = β₂ = 1`" | sharp along `ℓ₁ = 2ℓ₂`; the MIMC rates assume inner strong orders `½` and `1` |
| H3-25, H3-30 resolution | unconditional wording | under hypotheses on `f` that `Φ⁻¹` satisfies (not in Lean) |
| `not_convexOn_bitLevelCost` docstring | "contradicts the remark" | the numerical non-convexity concerns other parameters than the paper's |
| coverage README | | status columns keep the round-10 classification; "Round N" notes give the current state |

**Docstring-only claims (not formalised).** The README calls the digital `O(h^{1/3})` rate from
mean square "sharp" (example in the `digital_mismatch_le` docstring); the G2.1-36 counterexample
("therefore so is `Y`" fails without Lyapunov's condition, `MLMCCentralLimit.lean` docstring); the
0.3% consistency check failing for every `N ≤ 274` (numerical). The auditors checked the first two
examples by hand.

**Provable with the current library.** The auditors listed, with statement sketches and effort
estimates:
- **Small to medium:**
  - the Milstein digital variance for GBM;
  - `E[(ΔP)⁴] = P(ΔP ≠ 0)` bounds for the digital;
  - the sharpness example;
  - G5.2-18 for the actual construction;
  - GBM with refinement factor `M`;
  - the discounted call;
  - fourth moments of the tamed scheme;
  - the elliptic estimator end to end;
  - the least-squares minimiser of §3.2;
  - the law difference behind G10.2-05.
- **Medium:**
  - tau-leaping's weak rate against the exact chain for bounded payoffs, by uniformisation (G8-11);
  - `Φ⁻¹` in Lean, which makes the lookup-table results unconditional;
  - a discrete exponential-Lévy analogue of Table 6.3's Asian row (G6-09);
  - the constant-rate jump-adapted coupling (G6-02);
  - general piecewise-differentiable `f` (G9.1-15);
  - drift-implicit moments with multiplicative noise;
  - `IsBrownianReal` of the time-reversed path.
- **Medium to large:**
  - adaptive grids by discrete conditioning (G5.6-09, G8-19);
  - level-dependent steps for contracting SDEs (G10.1-16);
  - `L^p` strong errors for GBM;
  - the shifted-lattice variance in `d` dimensions.

**Out of reach.**
- **No Itô calculus:** strong and weak orders of general SDE schemes, Clark–Cameron, Giles–Szpruch.
- **No reflection principle or strong Markov property:** continuous monitoring and barriers.
- **No information-based complexity:** Creutzig et al.'s lower bound.
- **No PDE theory:** Feynman–Kac.
- **No Rademacher type in Banach spaces.**
- **No digital nets:** Sobol points and scrambling.
- **No Lévy–Itô theory or Wiener–Hopf factorisation.**
- **No Mercer's theorem:** Karhunen–Loève.
- **No lognormal elliptic regularity.**
- **Too fine:** the exact halving ratio of H3-30 (it needs the constant in `MSE ~ κ2^{−d}/d`).
- **Open:** whether nested MIMC reaches `O(ε⁻²)` for a piecewise linear `f`.

**Follow-up (round 18).** Formalised: the GBM digital items and G5.2-18 (`GBMDigital.lean`;
the paper's rates `O(h^{1/2})`, `O(h)` and the kurtosis rates remain open here), tau-leaping
against the exact chain for bounded payoffs (`TauLeapingExact.lean`), `Φ⁻¹` and the lookup-table
results for it (`InverseNormal.lean`), the elliptic estimator, the call, refinement factor `M`,
tamed fourth moments, the method-2 iteration and the rounded increments
(`EndToEndInstances.lean`).  Not yet: the G2.1-36 counterexample as a theorem, the medium and
large items above.

**Follow-up (round 19).** Formalised: the discrete parts of §6 (`JumpProcesses.lean`), the
G2.1-36 counterexample, the consistency check with one or two samples and the variance of the
sample variance (`EstimatorRemarks.lean`), drift-implicit Euler with multiplicative noise, the
time-reversed path as a Brownian motion and several kinks (`SDEExtensions.lean`), and contracting
SDEs with level-dependent steps (`ContractingLevels.lean`).  Still open from the list: adaptive
(path-dependent) grids, `L^p` strong errors for GBM, the shifted-lattice variance in `d`
dimensions, and the large items.

**Follow-up (round 20).** Formalised: `L^p` strong errors for GBM and the digital rates up to an
arbitrarily small loss in the exponent (`GBMStrongLp.lean`), adaptive grids on a base grid with
Algorithm 3's coupling (`AdaptiveGrids.lean`), the shifted-lattice variance in `d` dimensions and
the MLQMC complexity it gives (`LatticeRuleD.lean`), and Theorem 1 with a polylogarithmic cost
factor, which gives G10.1-16 the cost `O(ε⁻²|log ε|³)` (`Theorem1Log.lean`).  Every small, medium
and medium-to-large item of the list above is now formalised; the items "out of reach" remain.

**Follow-up (round 21).** Auditor A's fuller list (`report_A`, kept outside the repository) had
four items not carried into the summary above: weak order one of Euler–Maruyama for GBM (R19), the
strong error uniformly over the grid (R17), the general theorem of Hutzenthaler, Jentzen and Kloeden
(R14), and the optimality of the simplex among MIMC index sets (R16).  The first three are formalised
(`GBMWeakOrder.lean`, `GBMGridMax.lean` with the every-step lookback, `EulerSuperlinearGeneral.lean`);
the simplex optimality (large) remains open, as does the kurtosis upper bound (anti-concentration).

**Follow-up (round 22).** After round 21 a further spot-check ("spot-check 21"; two independent
auditors, reports kept outside the repository) re-read both papers against the coverage tables and
the elaborated Lean statements, about 170 rows, and found no Lean misstatement; its documentation
fixes are the "Spot-check 21" notes in the coverage tables and in `notes/coverage/README.md`.
From it, round 22 formalised: Theorem 1 for the digital option of GBM, the barrier option at fixed
monitoring dates and splitting with a Milstein final step (`GBMDigitalTheorem1.lean`); that the ML2R
bias `2^{−αL²}` is not attainable, as a theorem, the variance of the smoothed-CDF correction, the
heat scheme with Dirichlet boundary values, (2.4) for nested inputs, `Θ(ε⁻³)` for standard nested
Monte Carlo, the Ornstein–Uhlenbeck Euler chain, the corrected §10.2 inputs and `V_ℓC_ℓ` in
Haas–Giles §2.1 (`SpotCheckRemarks.lean`); the rates and Theorem 1 for the parabolic example of
§7.1 (`ParabolicExample.lean`); curved pieces and several kinks with inner time steps, and MIMC on
the two axes for the kink counterexample (`NestedKinkCurved.lean`); tau-leaping against the exact
chain for Lipschitz payoffs and with state-dependent rates on adaptive grids
(`TauLeapingExtensions.lean`).  Still open: the digital option's weak order `α = 1` (hence the
paper's `O(ε^{−2.5})`), the identification of the parabolic limit with the SPDE functional, the
truncation error of the Karhunen–Loève expansion, the variance rate of adaptive tau-leaping, the
simplex optimality, the kurtosis upper bound, and whether MIMC reaches `O(ε⁻²)` for a general
piecewise linear `f`.

**Follow-up (round 23).** From the remaining spot-check 21 notes and the out-of-scope table,
round 23 formalised: the conditional-expectation estimator of the digital option for GBM, with the
`O(h)` matching of the fine and the coarse conditional laws, `V_ℓ = O(h^q)` for every `q < 3/2`,
the weak rate `q < 1` and Theorem 1 at the paper's cost `O(ε⁻²)`, and splitting at the same rate
(`GBMDigitalCondExp.lean`); the coupling of the finest tau-leaping level with the exact chain, an
unbiased estimator at cost `O(ε⁻²)` with a fixed number of levels, for one reaction with a bounded
propensity and payoff (`TauLeapingSSA.lean`); the truncation error of the Karhunen–Loève expansion,
and the law, moments and covariance of the truncated field, with Mercer's expansion as hypotheses
(`KarhunenLoeve.lean`); when the change-of-measure correction has finite variance
(`ChangeOfMeasureVariance.lean`).  Still open: the digital option's weak order `α = 1` (hence the
paper's `O(ε^{−2.5})`) and, for the conditional-expectation estimator, the endpoints `β = 3/2`,
`α = 1`; the splitting variance "the same, to leading order"; Mercer's theorem and the law of the
limit field; the SSA coupling for several reactions and unbounded propensities; the identification
of the parabolic limit with the SPDE functional, the variance rate of adaptive tau-leaping, the
simplex optimality, the kurtosis upper bound, and whether MIMC reaches `O(ε⁻²)` for a general
piecewise linear `f`.
