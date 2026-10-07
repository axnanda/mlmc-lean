# Coverage audits of the two papers (round 10, 2026-09-29)

Five independent auditors read Giles (2015) and Haas–Giles (2025) in full and classified every
claim — numbered equations, theorems, stated identities and inequalities, rates, complexity
statements, algorithm steps and prose claims — against the Lean statements in `MlmcLean/`.
They read the Lean statements themselves (hypotheses, conclusions, quantifier order), not only
the docstrings, and treated the README and `notes/` as unverified leads.

| File | Range | Claims | Done | Done, documented deviation | Partial | Missing | Out of scope | N/A |
|---|---|---|---|---|---|---|---|---|
| `giles_s1_s2.3.md` | G15 §1–§2.3 | 118 | 64 | 12 | 4 | 2 | 2 | 34 |
| `giles_s2.4_s3.md` | G15 §2.4–§3.5 | 132 | 60 | 14 | 4 | 1 | 4 | 49 |
| `giles_s4_s6.md` | G15 §4–§6 | 140 | 29 | 8 | 4 | 13 | 40 | 46 |
| `giles_s7_s11.md` | G15 §7–§11 | 125 | 30 | 19 | 7 | 8 | 10 | 51 |
| `haas_giles.md` | HG25, all | 129 | 57 | 14 | 7 | 0 | 12 | 39 |

No Lean statement misstates a paper. The tables are the state **before** round 10; every item
they mark missing or partial, and every out-of-scope item they found undocumented, is resolved
below. "Not formalised" entries give the reason; they are also listed in `PLAN.md`.

## Resolution of the missing and partial items

| Item | Claim | Resolution (Lean, all in the axiom audit) |
|---|---|---|
| G2.1-35 | each level estimator is asymptotically normal | `tendstoInDistribution_levelEstimator` (`AsymptoticNormal.lean`, from Mathlib's CLT) |
| G2.1-36 | "and therefore so is `Y`" | `tendstoInDistribution_mlmcEstimator`, for a fixed number of levels and `N_ℓ = m_ℓ n`. Round 12: `L` growing with `ε` (Collier et al.) in `MLMCCentralLimit.lean`: the Lindeberg and Lyapunov CLTs for triangular arrays (`tendstoInDistribution_lindeberg`, `tendstoInDistribution_lyapunov`) and `tendstoInDistribution_mlmcEstimator_lyapunov`, `tendstoInDistribution_mlmcEstimator_of_moment_le`. With a growing `L` the "therefore" needs a hypothesis such as Lyapunov's condition (counterexample in the module docstring) |
| G2.1-34 | Collier et al.'s confidence interval for `E[P]` | Round 12 (`MLMCCentralLimit.lean`), with the exact `σ_k`: `P(|Y_k − E[P_{L_k}]| ≤ zσ_k) → 2Φ(z) − 1` (`tendsto_measureReal_abs_mlmcEstimator_sub_le`, `…_of_moment_le`), around `E[P]` when the bias is `o(σ_k)` (`tendsto_measureReal_abs_mlmcEstimator_sub_le_of_bias`) and with the tolerance split (`eventually_lt_measureReal_abs_mlmcEstimator_sub_le_tol`). Round 14 (`MLMCConfidenceEstimated.lean`): with estimated variances `σ̂_k² = ∑_ℓ s_ℓ²/N_{k,ℓ}`, for a fixed number of levels (strong law) and a growing one (bounded kurtosis, `E|s_N² − V| ≤ (√((κ−1)/N) + 1/N) V`): `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd_fixed`, `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd`, `…_estSd_of_bias`, and the tolerance test `eventually_lt_measureReal_test_and_abs_sub_le_tol` (deterministic `L_k`, `N_{k,ℓ}`; the adaptive, stopped algorithm is not formalised) |
| G3.5-03, G1-04 (QMC), G2.7-04 | QMC error `O(N⁻¹)`; MLQMC complexity `O(ε^{−p})`, `p < 2` | Round 12, in one dimension (`QMC1D.lean`): `qmc_error_le_of_boundedVariationOn`, `latticeRule_error_le_variation_div`, `latticeRule_randomShift`, `latticeRule_replicates`, `rank1Lattice_torus_replicates`, `latticeRule_vs_monteCarlo`; `mlqmc_complexity`, `mlqmc_complexity_of_lt`, `mlqmc_complexity_lt_two` (`p < 2` whenever `g < 2a` and `g < a + b`). Not formalised: `d > 1` (discrepancy theory) |
| G2.2-16 | `E_ℓ² ≪ V_ℓ` ⇒ `N ≈ ε⁻² Σ V_ℓ/p_ℓ` | `singleTerm_variance_le_of_sq_le`, `singleTermN_samples_of_sq_le` (factor `1 + δ`) |
| G2.3-08 | ML2R bias `O(2^{−αL²})` | `abs_ml2rWeight_le_sharp`, `ml2r_bias_le`: `O(2^{−αL(L+1)/2})` uniformly in `L`; the printed rate is not attainable (`ml2r_bias`) |
| G2.3-12, -13 | ML2R cost `O(ε⁻²|log ε|)`, `O(ε⁻²2^{(γ−β)√(|log₂ε|/α)})` | `ml2r_theorem_eq`, `ml2r_theorem_lt` for the estimator's MSE (exponent `√(2|log₂ε|/α)`) |
| G2.4-32 | the optimal `𝓛` is of the form `ℓ·n ≤ L` | `giles_theorem2_indexSet`, `giles_theorem2_boundary_indexSet` (and the deterministic `…_indexSet`): the simplex achieves the bounds. Not formalised: its optimality among all index sets |
| G2.6-09, -10 | combined variance and cost of two kept levels | `levelKeep_combined` |
| G3.3-05 | consistency check with *empirical* variances | Round 13 (`ConsistencyCheck.lean`): with empirical variances the check fails with asymptotic probability at most `P(|Z| ≥ 3) < 0.003` as the sample sizes grow at any rates (`consistency_check_empirical`, `consistency_check_empirical_lt`; strong law `tendsto_empVar_ae`, two-sample CLT `tendstoInDistribution_twoSample`), and the bound is attained (`consistency_check_empirical_sharp`). For a fixed sample size the paper's `0.3%` can fail (it exceeds `0.003` for every `N ≤ 274` in the module docstring's example), so the claim holds only asymptotically. The Gaussian bound with the true variances is `consistency_check_gaussian` |
| G3.5-05 | random-shift QMC gives independent unbiased replicates | `shiftedQMC_unbiased`, `randomShift_replicates` |
| G5.1-09 | European, Asian, lookback payoffs are Lipschitz | `lipschitz_european_asian_lookback`, `variance_lipschitz_payoff_le` |
| G5.1-25, G5.2-09 | digital option: bounded density ⇒ `V_ℓ = O(h^{1/2})` | `digital_mismatch_le`, `variance_digital_le`, `variance_digital_levelDiff_le`, `variance_digital_rate` (`O(h^{1/3})` from the mean-square strong error, sharp), `digital_mismatch_le_of_tail` (`O(√(h log(1/h)))` with Gaussian tails), `digital_mismatch_le_of_moment`, `gbm_digital_variance_le` (`β = 1/3` for GBM, no assumption). Not formalised: the kurtosis rates, which need a lower bound on the mismatch |
| G5.2-11, -12, -17 | conditional expectation of the last step, `Φ` formulas, `V₀ = 0` | `integral_digital_final_step`, `condExp_digital_last_step`, `digital_smoothing`, `digital_smoothing_coarse`, `digital_smoothing_level_zero` |
| G5.2-19 | splitting: same variance to leading order | `splitting_variance_le`, `splitting_leading_order` (iff `E[v]/V[m] = o(h⁻¹)`) |
| G5.2-21 | change of measure | `gaussian_change_of_measure`, `integral_mul_likelihoodRatio`, `integral_mul_sub_likelihoodRatio` |
| G5.3-09 | antithetic `O(h²)` for smooth payoffs (d dimensions) | `abs_midpoint_sub_avg_le_fderiv`, `abs_antithetic_le_fderiv`, `abs_antithetic_le_midpoint`, `variance_antithetic_le_fderiv`, `variance_antithetic_le_midpoint` |
| G5.3-10 | antithetic `O(h^{3/2})` for the call | `abs_call_antithetic_le`, `variance_call_antithetic_le` (under a bounded conditional density; marginal information alone does not give `3/2`), `variance_call_antithetic_le_holder` |
| G5.4-02 | the call payoff's derivative is discontinuous | `hasDerivAt_call_payoff` |
| G5.6-04, -05 | super-linear drift is unstable; taming | `eulerCubic_growth`, `eulerCubic_tendsto_atTop`, `eulerCubic_bounded`, `abs_tamedDrift_lt`, `abs_tamedDriftStep_sub_eulerDriftStep_le`, `tamedDriftStep_iterate_bounded`, `tamedCubic_bounded` (deterministic analogues). Not formalised: the moment results for the SDE (Hutzenthaler–Jentzen–Kloeden) |
| G5.7-06 | the smoothed CDF for general smoothers | `abs_smoothCDF_sub_le_of_bounded`, `tendsto_smoothCDF_of_bounded`, `tendsto_smoothCDF_of_continuous` |
| G5.7-11 | density of multi-dimensional outputs | `tendsto_density_multidim`, `tendsto_density_euclidean` |
| G6-14 | Lévy increments summed for the coarse path | `measurePreserving_levyPairSum`, `integral_levyCoarse`, `levy_telescoping`, `levyPath_levyPairSum`, `map_levyPath_levyPairSum` |
| G6-16 | several random periods concentrate at `T` | `sum_exponential_periods`, `exponential_periods_clt` |
| G7.1-03 | central differences = FE with one-point quadrature | `fe_eq_centralDiff` |
| (§7.1) | a deterministic `K` with `|P − P_ℓ| < K h_ℓ²` | impossible for the example (`not_ae_abs_gaussian_sq_mul_le`); random `K`: `rates_of_pathwise_random`, `elliptic_rates_random` (`α = 2`, `β = 4`) |
| G7.3-03 | the Milstein SPDE scheme | `spdeMilsteinStep_eq`, `spdeScheme_eq_milstein` |
| G8-19 | Poisson variates on non-nested grids | `stepCounts_hasLaw`, `iIndepFun_stepCounts`, `unionGrid_hasLaw`, `map_comp_stepCounts_eq`, `integral_comp_stepCounts_eq`, `unionGrid_2_4`, `unionChain_fine`, `unionChain_coarse`, `unionChain_nested`, `unionChain_2_4` (deterministic grids). Not formalised: path-dependent grids (a martingale argument) |
| G9.1-15 | piecewise linear `f`: `β = 1.5`, cost `O(ε⁻²)` | `antithetic_kink`, `nested_kink_variance_rate`, `nested_kink_variance_rate_of_density`, `nested_kink_bias_rate`, `nested_kink_mlmc_complexity`, if the conditional fourth moments are bounded and the inner mean has little mass near the kink (e.g. a bounded density, `small_ball_of_density`) |
| G9.2-02, -04 | inner paths with `2^ℓ` Milstein steps: `α = 1`, `β = 2`, `γ = 2`, cost `O(ε⁻²(log ε)²)` | `nestedSdeP`, `nestedSdeDelta`, `integral_nestedSdeDelta`, `nested_sde_bias_rate`, `nested_sde_mean_rate`, `nested_sde_variance_rate`, `nested_sde_mlmc_complexity`; the Milstein weak and strong orders are hypotheses on the inner approximations |
| G9.2-06 | the MIMC Taylor expansion | `mimc_antithetic_quadratic` (the coefficient is `−1/8`, as in §9.1), `abs_mimc_antithetic_taylor_le`, `abs_mimc_antithetic_le` |
| G9.2-08, -09, -11 | `E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})`, `V_ℓ = O(2^{−2ℓ₁−2ℓ₂})` | `nestedMimcDelta`, `abs_mimc_antithetic_le_of_deriv2`, `nested_mimc_mean_rate`, `nested_mimc_variance_rate`, with `f″` Lipschitz and `L⁴` strong convergence; the intermediate `O(·)` claims hold after re-centring |
| G9.2-13, -14 | piecewise linear `f` with inner time steps (MLMC `O(ε^{−2.5})`, MIMC `O(ε⁻²)`) | Round 13 (`NestedKinkSde.lean`): MLMC with inner time steps has `α = 1` (`nested_kink_bias_rate_one`, `nested_kink_sde_bias_rate`), `β = 3/2` (`nested_kink_sde_variance_rate`) and cost `O(ε^{−5/2})` (`nested_kink_sde_mlmc_complexity`), under a small-ball hypothesis, bounded centred conditional fourth moments, and weak order 1 and strong order 1/4 of the inner discretisation (hypotheses, as Itô calculus is not in Mathlib). The MIMC claim `β₁ = β₂ = 1.5` is **false**: an explicit example meets every hypothesis, yet `V[Y_ℓ]` is not `O(2^{−β₁ℓ₁−β₂ℓ₂})` for any `2β₁ + β₂ > 3` (`kinkMimc_variance_ge`, `nested_mimc_kink_rates_false`), so Theorem 2 does not give `O(ε⁻²)`. Round 14 (`NestedMimcKink.lean`): the corrected rates are `V[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` (`nested_mimc_kink_variance_rate`, sharp along `ℓ₁ = 2ℓ₂`: `nested_mimc_kink_rate_sharp`) and `|E[Y_ℓ]| = O(2^{−ℓ₁/2−ℓ₂})` (`nested_mimc_kink_mean_rate`); Theorem 2 then gives MSE `< ε²` at cost `O(ε⁻²|log ε|⁴)` (`nested_mimc_kink_complexity`), still below MLMC's `O(ε^{−5/2})` (`nested_mimc_kink_beats_mlmc`). Whether `O(ε⁻²)` is attainable is not decided |
| G10.1-07 | "the invariant distribution … is the uniform distribution on `[0, 2]`" | `map_limit_invariant`, `map_limit_eq_of_invariant`, `invariant_unique`, `existsUnique_invariant`, `map_limit_halfStep`, `halfStep_limit_uniform`, `halfStep_invariant_unique` |
| G10.1-10 | the bias of the levels; MLMC for `E[f(X_∞)]` | `lintegral_dist_limit_le`, `sq_integral_sub_limit_le`, `abs_integral_sub_limit_le`, `abs_integral_fwdIter_sub_limit_le`, `markov_mlmc_rates`, `markov_randomised_mlmc`, `markov_mlmc_theorem1` |
| G10.1-15 | `N_ℓ` linear in `ℓ` | `markov_linear_levels` |
| G10.2-05 | truncating increments breaks (2.4) | `roundFixed_sum_inconsistent`, `roundFixed_sum_inconsistent_general` |
| G10.2-07 | Brownian-bridge construction respects the telescoping sum | `bbPath_nested`, `bbPath_congr`, `bb_telescoping`, `vpPath_castLE`, `integral_vpCoarse`, `vp_telescoping` |
| H3-07 | a sum of approximate `N(0, 1/n)` is approximately `N(0, 1)` | `sum_gaussian_hasLaw`, `tendstoInDistribution_sum_of_approxNormal`, `tendstoInDistribution_sum_inv_sqrt_mul` |
| H3-25 | dyadic intervals: MSE `→ C > 0` | `dyadic_mse_ge`, `method3_mse_ge`, `method3_mse_not_tendsto_zero`; round 14 (`LUTAsymptotics.lean`): the limit exists and is positive, `C = 2∑_k E_k` with `E_k` the least-squares affine error on the `k`-th dyadic interval (`tendsto_method3MSE`, `method3Limit_pos`, `exists_tendsto_method3MSE`). The paper's mechanism ("only the interval closest to 0 changes") is only asymptotic: the error on every dyadic interval decreases with `d` (`dyadic_groupMSE_eq`, `groupMSE_odd_quadratic`) |
| H3-30 | method 1: "MSE divided by 2 each time `d` increases by 1" | Round 14 (`LUTAsymptotics.lean`), under block-wise bounds on `f` that `Φ⁻¹` satisfies: `c 2^{−d}/d ≤ MSE ≤ C 2^{−d}/d` (`method1MSE_order`) and `log(MSE)/d → −log 2` (`tendsto_log_method1MSE_div`). Not formalised: the exact ratio `MSE(d+1)/MSE(d) → ½`, which needs finer asymptotics of `Φ⁻¹` (numerically the ratio is `½(1 − 1/d + …)`) |
| H6-16 | cost factor `< 1` ⇒ nested is cheaper | `levelCost34_eq_mul_costFactor`, `nestedCost_le_of_costFactor_le`, `nestedCost_lt_of_costFactor_le`; for the full cost (32) the factor must satisfy `ρ²(1+ρ²) < 1` (`exists_costFactor_lt_one_nestedCost_gt`) |
| H6-21, -23, -24 | sizes of the path variables, "`S_i` are the largest" | `integral_sq_mul1_sum1_eq`, `integral_sq_mul1_sum1_bounds`, `integral_gbmPath_eq`, `integral_sq_gbmPath_mul2_eq_pow`, `gbmPath_size_bounds`, `integral_sq_mul2_bounds`, `gbmPath_sq_largest` |
| H6-35 | fixed bit-widths: rounding errors dominate for small `h` | `variance_linearised_indep_eq`, `variance_linearised_indep_ge`, `perturbed_path_sub_mean_variance`, `integral_sq_perturbed_path_sub_bounds`, `strongError_lt_integral_sq_perturbed_path_sub` |

## Out-of-scope items (not formalised), with the reason

| Items | Claim | Reason |
|---|---|---|
| G1-04, G2.7-04, G3.5-03 | QMC error `O(N⁻¹)`, MLQMC complexity, in `d` dimensions | QMC error theory (discrepancy, Koksma–Hlawka) is not in Mathlib. Round 12 proves the one-dimensional case (`QMC1D.lean`, see the resolution table) |
| G2.5-12 | other norms via Banach-space results | cited (type-2 Banach spaces); the Hilbert-space case is proved (`giles_theorem1_hilbert`) and the sup-norm counterexample is `sq_norm_add_of_indepFun_fails_sup` |
| G3.5-06 | digital scrambling of Sobol points | QMC construction |
| G5.1-15, -16 | Creutzig et al.'s lower bound and worst-case optimality | cited information-based complexity |
| G5.x (Table 5.2, Clark–Cameron, Lévy areas, Giles–Szpruch, Giles–Debrabant–Rößler, exit times, Feynman–Kac G5.5-01, G5.5-03) | strong and weak orders of SDE discretisations | Itô calculus is not in Mathlib; the GBM case is proved from the explicit solution (`GBMEulerMaruyama.lean`, `GBMMilstein.lean`) |
| G5.4-04 | digital sensitivities by pathwise differentiation | needs the SDE's pathwise derivative |
| G6-02, -03, -05, -06, -09 to -11, -15, -18 | jump-diffusion couplings, thinning, the Xia–Giles change of measure, small-jump truncation, Table 6.3, Wiener–Hopf sampling, lookback complexity | Lévy-process theory (jump SDEs, Wiener–Hopf factorisation) is not in Mathlib; the coarse-increment identity is proved (G6-14) |
| G7.1-15, -16 | Milstein and finite-difference convergence orders | SDE/PDE theory |
| G7.2-03, -07 | Karhunen–Loève expansion; FE analysis with lognormal coefficients | spectral theory of covariance operators; elliptic PDE regularity |
| G7.3-04 | the stability constraint `k_ℓ = k_{ℓ−1}/4` | mean-square stability of an SPDE scheme with unbounded random coefficients |
| G8-11, -13 | tau-leaping weak rate `α = 1` against the exact chain; the SSA coupling on the finest level | the continuous-time Markov chain itself |
| G10.1-16 | contracting SDEs | SDE theory |
| H2-03, H2-14 | weak and variance rates of general SDEs | as above |
| H1-08, H2-23, H2-25, H3-06, H3-33, H5-01, H5-05, H5-06, H7-03 | FPGA and hardware costs | hardware facts, not mathematics |

Numerical results, figures, tables of measurements and historical remarks are marked N/A in the
tables.
