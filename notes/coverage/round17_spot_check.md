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

**Follow-up (round 24).** From the out-of-scope table and the round-23 notes, round 24 formalised:
the small-jump truncation of §6.2 for the terminal value of a pure-jump Lévy process, with (2.4),
the correction variance from the intermediate range of jump sizes, the `L²` limit and the bias as
`δ_ℓ → 0`, the expected cost and Theorem 1 for `δ_ℓ = 2^{−ℓ}`, with a one-sided stable-like example
(`LevyTruncation.lean`); the untruncated Karhunen–Loève field, with Mercer's expansion as
hypotheses: almost sure convergence, the Gaussian law, covariance and joint Gaussianity, the moments
of the diffusivity and that it is unbounded (`KarhunenLoeveLimit.lean`); sensitivities for GBM: the
pathwise delta of the call, with the digital option's rates and costs as upper bounds, and the
digital delta from the conditional-expectation payoffs, unbiased and with (2.4)
(`GBMSensitivities.lean`); and, from the round-23 read-back, an `IsProbabilityMeasure` conjunct of
`variance_ssaCorrection_exact_le`.  Still open: the digital option's weak order `α = 1` (hence the
paper's `O(ε^{−2.5})`) and, for the conditional-expectation estimator, the endpoints `β = 3/2`,
`α = 1`; the splitting variance "the same, to leading order"; the variance rate of the digital-delta
corrections and sensitivities for general SDEs; Mercer's theorem, the identification of the joint
law of the limit field with a multivariate Gaussian (done in round 27, `LimitLawExtras.lean`), the
regularity of `κ` and the moments of `max_x κ` and `1/min_x κ`; the Brownian replacement of the
small jumps, the Lévy–Khintchine law of the truncation limit (done in round 27,
`LevyKhintchineLimit.lean`) and path-dependent Lévy payoffs; the SSA coupling for several reactions
and unbounded propensities; the identification of the parabolic limit with the SPDE functional, the
variance rate of adaptive tau-leaping, the simplex optimality, the kurtosis upper bound, and whether
MIMC reaches `O(ε⁻²)` for a general piecewise linear `f`.

**Follow-up (round 25).** After round 24 a further spot-check ("spot-check 24"; two independent
auditors, reports kept outside the repository) re-read both papers against the coverage tables and
the elaborated Lean statements (auditor A: 226 theorems over about 145 rows of Giles §1–§5; auditor
B: 70 rows of Giles §6–§11 and Haas–Giles) and found no wrong, vacuous or junk-dependent Lean
statement. Its documentation fixes are the "Round 25" notes in the coverage tables and the
spot-check 24 section of `notes/coverage/README.md`: row texts that only the resolution table showed
resolved, round-10 sections without a pointer, G9.2-04 (PARTIAL by the spot-check-21 standard; done
end to end by `nested_sde_mlmc_complexity`), the untracked barrier option monitored at every time
step (G5.2-23), overclaims in the README and PLAN (the ML2R row, the every-step barrier, the
"variance rates and costs" of the call delta, which are upper bounds), the deviations of §8, §9.1
and §10.1 added to `notes/statement-audit.md`, and the paper slips added to its corrections table
(among them the weak convergence of §10.1, now refuted formally); stale module docstrings were
corrected. From the auditors' lists of provable claims, round 25 formalised: the strike `K = 0` and
Theorem 1 for splitting (`GBMDigitalCondExpExtras.lean`); the `O(h)` correction variance and
Theorem 1 for Lipschitz propensities of linear growth, given the weak rate, and the linear birth
example with no assumed rate (`TauLeapingLinearGrowth.lean`); Theorem 1 in a Banach space with an
assumed type-2 inequality (`BanachTheorem1.lean`); the random digital shift
(`DigitalShiftQMC.lean`); the Brownian replacement of the small jumps, with the rates of the
truncation, and Table 6.3's Asian row for Variance-Gamma laws (`LevyExtras.lean`); the
counterexample to the weak convergence claim of §10.1 (`MarkovNoWeakLimit.lean`). Still open from
the lists: the variance rate of the digital-delta corrections and Theorem 1 for them; the
Euler–Maruyama digital endpoint `O(√(h log(1/h)))`; the barrier option monitored at every time step
(it needs a small-ball bound for the grid maximum, uniform in the number of steps); the lower bounds
`P(ΔP ≠ 0) ≥ c√h` (Euler–Maruyama) and `≥ ch` (Milstein), hence the kurtosis rates and the splitting
variance "the same, to leading order"; the existence of good lattice generating vectors; Dereich's
improved bias; the NIG column of Table 6.3; the exact halving ratio of HG25 §3.4; the non-convexity
of the λ-function of HG25 §6.1 (numerical in the corrections table). Still open from earlier rounds:
the digital option's weak order `α = 1` (hence the paper's `O(ε^{−2.5})`), the endpoints `β = 3/2`,
`α = 1` of the conditional-expectation estimator and the exponential smallness for `K = 0`; the weak
rate of tau-leaping for unbounded propensities; Mercer's theorem and the identification of the joint
law of the limit field with `multivariateGaussian` (done in round 27, `LimitLawExtras.lean`); the
SSA coupling for several reactions and unbounded propensities; the identification of the parabolic
limit with the SPDE functional, the variance rate of adaptive tau-leaping, the simplex optimality,
and whether MIMC reaches `O(ε⁻²)` for a general piecewise linear `f`. Out of reach, as before: Itô
calculus, the reflection principle, Clark–Cameron, Lévy areas and Giles–Szpruch, information-based
complexity, Feynman–Kac and exit times, Rademacher type beyond spaces isomorphic to a subspace of a
Hilbert space, Sobol nets and Owen's scrambling, general tangent processes, Lévy path functionals
and Wiener–Hopf factorisation.

**Follow-up (round 26).** From the spot-check-24 lists still open after round 25, round 26
formalised three items: the Euler–Maruyama digital endpoint for GBM, the mismatch probability, `V_ℓ`
and `E[(ΔP)⁴]` at most `C (h_{ℓ+1}(ℓ + 1))^{1/2}`, i.e. `O(√(h log(1/h)))`, uniformly in `S₀` and
`K`, hence Table 5.2's analysis rate `O(h^{1/2} log h)` (`GBMDigitalEndpoint.lean`; from
Gaussian-type tails of the log error, not Avikainen's argument); the exact halving ratio of HG25
§3.4 for `Φ⁻¹`, `MSE(d + 1)/MSE(d) → ½`, as a limit, from `MSE(d) ~ κ 2^{−d}/d` with
`κ = (∑_{j≥0} V_j)/log 2 ≈ 1.5586` (`LUTHalving.lean`); the variance rate of the digital-delta
corrections for GBM, `V_ℓ = O(h^q)` for every `q < ½` (`GBMDigitalDeltaVariance.lean`; the paper
states no rate, and Burgos 2014 was not consulted). The module docstrings that called these unproved
(`LUTAsymptotics.lean`, `InverseNormal.lean`, `GBMSensitivities.lean`, `GBMDigital.lean`,
`GBMStrongLp.lean`, `GBMDigitalTheorem1.lean`, `SDEDigital.lean`) now point to them, and the "Round
26" notes in the coverage tables record them. Still open from the lists: Theorem 1 for the digital
delta (it needs the convergence of the density of the discretised `S_T` at the strike) and the
endpoint `q = ½` of its variance rate; the observed `O(h^{1/2})` of the Euler–Maruyama digital
option without the logarithm; the barrier option monitored at every time step (it needs a small-ball
bound for the grid maximum, uniform in the number of steps); the lower bounds `P(ΔP ≠ 0) ≥ c√h`
(Euler–Maruyama) and `≥ ch` (Milstein), hence the kurtosis rates and the splitting variance "the
same, to leading order"; the existence of good lattice generating vectors; Dereich's improved bias;
the NIG column of Table 6.3; the non-convexity of the λ-function of HG25 §6.1 (numerical in the
corrections table). Still open from earlier rounds: the digital option's weak order `α = 1` (hence
the paper's `O(ε^{−2.5})`), the endpoints `β = 3/2`, `α = 1` of the conditional-expectation
estimator and the exponential smallness for `K = 0`; the weak rate of tau-leaping for unbounded
propensities; Mercer's theorem and the identification of the joint law of the limit field with
`multivariateGaussian` (done in round 27, `LimitLawExtras.lean`); the SSA coupling for several
reactions and unbounded propensities; the identification of the parabolic limit with the SPDE
functional, the variance rate of adaptive tau-leaping, the simplex optimality, and whether MIMC
reaches `O(ε⁻²)` for a general piecewise linear `f`. Out of reach, as before: Itô calculus, the
reflection principle, Clark–Cameron, Lévy areas and Giles–Szpruch, information-based complexity,
Feynman–Kac and exit times, Rademacher type beyond spaces isomorphic to a subspace of a Hilbert
space, Sobol nets and Owen's scrambling, general tangent processes, Lévy path functionals and
Wiener–Hopf factorisation.

**Follow-up (round 27).** After round 26 a further spot-check ("spot-check 26"; two auditors,
reports not in the repository) led to the documentation fixes at the end of round 26 and listed
claims that are provable but not formalised. From that list and the lists above, round 27
formalised: Theorem 1 with factors `(ℓ + 1)^a`, `(ℓ + 1)^b` in the bias and variance bounds, in the
case `β < γ`, and with it Theorem 1 for the GBM digital option with Euler–Maruyama at cost
`O(ε⁻³|log ε|)`, the weak error being bounded by the mismatch probability `O((h log(1/h))^{1/2})`
(`GBMDigitalTheorem1Log.lean`); the optimality of the type-2 constant `√2` of `ℝ × ℝ` with the
maximum norm, and `V_0 = 0` for the digital delta (`SpotCheck26Extras.lean`); the identification of
the joint law of the Karhunen–Loève limit field with `multivariateGaussian`, and a counterexample on
`(0, ∞)` showing that completeness cannot be dropped from the weak convergence of §10.1
(`LimitLawExtras.lean`); the Lévy–Khintchine law of the truncation limit of §6.2, for the terminal
value only (`LevyKhintchineLimit.lean`). The module docstrings that called these unproved
(`BanachTheorem1.lean`, `KarhunenLoeveLimit.lean`, `MarkovNoWeakLimit.lean`, `MarkovLimit.lean`,
`LevyTruncation.lean`, `GBMDigitalTheorem1.lean`, `GBMSensitivities.lean`) now point to them, the
stale remarks of `TauLeapingMLMC.lean` and `PoissonGrids.lean` point to results of earlier rounds,
`spde_meanSquare_stable` notes its trivial case `h = 0`, and the "Round 27" notes in the coverage
tables record the new results. Still open from the lists: Theorem 1 for the digital delta (it needs
the convergence of the density of the discretised `S_T` at the strike), the endpoint `q = ½` of
its variance rate and the endpoint `β = 3/2` of the conditional-expectation estimator, possibly up
to logarithms; the observed `O(h^{1/2})` of the Euler–Maruyama digital option without the
logarithm, and the cases `β ≥ γ` of Theorem 1 with logarithmic factors in the rates; the barrier
option monitored at every time step; the lower bounds `P(ΔP ≠ 0) ≥ c√h` (Euler–Maruyama) and `≥ ch`
(Milstein), hence the kurtosis rates and the splitting variance "the same, to leading order"; the
random cost of the exact (SSA) level; the change-of-measure variance after averaging over the paths;
a lower bound on the cost of ML2R; that a logarithmic moment suffices for the chain of
`MarkovNoWeakLimit.lean`; the existence of good lattice generating vectors; Dereich's improved bias;
the NIG column of Table 6.3; the non-convexity of the λ-function of HG25 §6.1 (numerical in the
corrections table). Still open from earlier rounds: the digital option's weak order `α = 1` (hence
the paper's `O(ε^{−2.5})`), the endpoints `β = 3/2`, `α = 1` of the conditional-expectation
estimator and the exponential smallness for `K = 0`; the weak rate of tau-leaping for unbounded
propensities; Mercer's theorem; the SSA coupling for several reactions and unbounded propensities;
the identification of the parabolic limit with the SPDE functional, the variance rate of adaptive
tau-leaping, the simplex optimality, and whether MIMC reaches `O(ε⁻²)` for a general piecewise
linear `f`. Out of reach, as before: Itô calculus, the reflection principle, Clark–Cameron, Lévy
areas and Giles–Szpruch, information-based complexity, Feynman–Kac and exit times, Rademacher type
beyond spaces isomorphic to a subspace of a Hilbert space, Sobol nets and Owen's scrambling, general
tangent processes, Lévy path functionals and Wiener–Hopf factorisation.
