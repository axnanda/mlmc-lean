# mlmc-lean: multilevel Monte Carlo in Lean 4, plus research notes

A research repo (Sept 2026) with four parts:

| Path | What it is |
|---|---|
| `MlmcLean/` | Machine-checked **Lean 4 + Mathlib proofs** of Giles' MLMC complexity theorem (Theorem 1), randomised MLMC, the Multi-Index Monte Carlo theorem (Theorem 2), the MLMC and MLQMC algorithms, Richardson–Romberg MLMC, and the pure-mathematics content of the application sections of Giles (2015) and of Haas–Giles (2025): 82 modules, 962 audited theorems. Zero `sorry`. |
| `PLAN.md` | Formalisation milestones (M0–M3 and M5 done; M4, level-dependent precision, awaits sign-off) and ground rules. **Start here for new work.** |
| `notes/research-notes.md` | Evaluation of ternary/low-precision inputs for the Haas–Giles framework, the weak-vs-strong ("path") argument, AWS F2/Trainium notes, strategy and open directions. |
| `experiments/quantization/` | The two numerical checks behind the notes (Python), with saved outputs in `results/`. |
| `docs/` | The two papers: PDFs, extracted text and the Haas–Giles arXiv LaTeX source. |

## Lean formalisation

Machine-checked proofs (Lean 4 + Mathlib) of the complexity results for MLMC from:

* **[G15]** M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015) 259–328.
  §1 (Monte Carlo, control variates, eq. (1.1)), §2 (Theorems 1 and 2, randomised MLMC,
  Richardson–Romberg MLMC, multiple outputs, non-geometric MLMC, MLQMC), §3 (Algorithms 1 and 2
  and the implementation), and the parts of the applications in §5 (SDEs), §7 (PDEs), §8
  (continuous-time Markov chains), §9 (nested simulation) and §10 (Markov chain equilibria) that
  follow from probability and algebra.
* **[HG25]** I.-B. Haas, M.B. Giles, *A nested MLMC framework for efficient simulations on
  FPGAs*, arXiv:2502.07123 (2025). §2 (eq. (2)–(13)), §3 (approximate normals, (14)–(19)),
  §4 (rounding errors, (20)–(29)), §5–§6 (the cost model and the bit-width optimisation,
  (30)–(41)).

The convergence orders of the discretisations themselves (Euler–Maruyama, Milstein, finite
differences, QMC) are not formalised in general: Mathlib has no Itô calculus. The theorems that
use them take the orders as hypotheses, as the papers' complexity theorems do. The exception is
the paper's worked example, geometric Brownian motion, whose solution is explicit: there the
strong and weak rates of Euler–Maruyama and Milstein are proved and Theorem 1 holds with no
assumed rate (`GBMEulerMaruyama.lean`, `GBMMilstein.lean`).

The statement-by-statement comparison with the papers, including every deviation, is in
`notes/statement-audit.md`.

### What is proved

| File | Content | Paper |
|---|---|---|
| `MlmcLean/Allocation.lean` | Optimal sample allocation. `cost_lower_bound` / `optimal_cost_isLeast`: over **all** real allocations with total variance `≤ τ`, the least cost is `τ⁻¹(Σ√(V_iC_i))²` (Cauchy–Schwarz), attained by the Lagrange allocation `lagrangeN` (variance exactly `τ`, `lagrangeN_variance_cost`) and by no other allocation (`lagrangeN_unique`), so the stationary point of the paper is the unique global minimum. `optimal_variance_isLeast`: the dual problem (least variance `B⁻¹(Σ√(V_iC_i))²` for cost `≤ B`); `twoLevel_optimal_ratio`: for two levels, minimal variance at fixed cost **iff** `N₁/N₀ = √(V₁/C₁)/√(V₀/C₀)`. `optimalN_variance` / `optimalN_cost`: the rounded-up `N_i = ⌈lagrangeN⌉` meets the variance target with cost `≤ τ⁻¹(Σ√(V_iC_i))² + ΣC_i`. | [G15] (1.1), §1.2 p. 3, §1.3 p. 4; [HG25] (8) |
| `MlmcLean/LevelDiff.lean` | The correction `ΔP_ℓ = P_ℓ − P_{ℓ−1}`, `P_{−1} ≡ 0` (`levelDiff`) and the telescoping identity `Σ_{ℓ≤L} E[ΔP_ℓ] = E[P_L]` (`sum_integral_levelDiff`). | [G15] §1.3, (2.2) |
| `MlmcLean/Estimator.lean` | `mse_eq_variance_add_sq_bias`: `E[(Y−m)²] = V[Y] + (E[Y]−m)²`. `mlmc_mean`: `E[ΣY_ℓ] = E[P_L]` (telescoping). `mlmc_variance`: `V[ΣY_ℓ] = ΣV[Y_ℓ]` for pairwise independent `Y_ℓ`. `mlmc_mse`: their combination. | [G15] (2.1), (2.3) |
| `MlmcLean/Complexity.lean` | `mlmc_complexity_core`: the deterministic core of Theorem 1 in all three regimes `β > γ`, `β = γ`, `β < γ`, with `c₄` depending only on `α, β, γ, c₁, c₂, c₃`. | [G15] Thm 1 (proof, p. 7) |
| `MlmcLean/Theorem1.lean` | `giles_theorem1`: **Theorem 1 as stated**, on an arbitrary probability space, with random per-sample costs: `MSE < ε²` and `E[C] ≤ c₄·(ε⁻², ε⁻²(log ε)², ε^{−2−(γ−β)/α})`. `giles_theorem1_cost_sum` (the same for `Σ N_ℓC_ℓ`), `giles_theorem1_isBigO` (each regime as `IsBigO` as `ε → 0⁺`), `variance_sample_mean` (`V[N⁻¹ΣX_n] = v/N`). | [G15] Thm 1 |
| `MlmcLean/StandardEstimator.lean` | Theorem 1 for the actual estimator (2.2) `Y_ℓ = N_ℓ⁻¹Σ_n(P_ℓ − P_{ℓ−1})(ω^{(ℓ,n)})` built from independent inputs: unbiasedness, `V[Y_ℓ] = V_ℓ/N_ℓ` and independence across levels are **proved** (`integral_levelEstimator`, `variance_levelEstimator`, `indepFun_levelEstimator`), and so is (2.3) for the whole estimator (`mlmcEstimator_mean_variance`); `giles_theorem1_standard`; `giles_theorem1_iid` on the product space `(Ω₀^{ℕ×ℕ}, ν^{⊗ℕ×ℕ})`, where no independence assumption remains (`exists_iid_inputs`). | [G15] (2.2), (2.3), Thm 1 |
| `MlmcLean/SampleMean.lean` | Monte Carlo averages over blocks of independent inputs (`blockMean`): unbiased, variance `V/N`, and independent across blocks (`integral_blockMean`, `variance_blockMean`, `indepFun_blockMean`). | [G15] §1.1 p. 2, §1.3 |
| `MlmcLean/Randomised.lean` | Randomised single-term MLMC: `singleTerm_unbiased` (`E[Y] = E[P]`), `singleTerm_variance` (`V[Y] = Σp_ℓ⁻¹(V_ℓ + E_ℓ²) − (ΣE_ℓ)²` with `E_ℓ = E[P_ℓ − P_{ℓ−1}]`), `singleTerm_variance_ge` (`V[Y] ≥ Σp_ℓ⁻¹V_ℓ`), `integral_cost_level` (the expected cost of one sample is `Σp_ℓC_ℓ`, finite iff the series converges), `randomised_necessary` (finite variance and finite expected cost force `Σp_ℓ⁻¹V_ℓ < ∞` and `Σp_ℓC_ℓ < ∞`), `singleTermN_mean_variance` (the estimator with `N` samples: unbiased, variance `V[Y]/N`), `randomised_summable` / `randomised_not_summable` (possible iff `β > γ`), `randomised_optimal_p_isLeast` (optimal `p_ℓ ∝ √(V_ℓ/C_ℓ)` minimises `(Σp_ℓ⁻¹V_ℓ)(Σp_ℓC_ℓ)`), `randomised_optimal_cost` (with it, `Σ V_ℓ/p_ℓ = (Σ√(V_ℓC_ℓ))(Σ√(V_ℓ/C_ℓ))` and the cost is `ε⁻²(Σ√(V_ℓC_ℓ))²`), `randomised_mlmc_finite`. | [G15] §2.2 (Rhee–Glynn) |
| `MlmcLean/MultiIndex.lean` | Multi-indices `ℓ ∈ ℕ^D`, the cross-difference `ΔP_ℓ = (∏_dΔ_d)P_ℓ` (`crossDiff`; Figure 2.1 in two dimensions, `crossDiff_two`) and telescoping over boxes, `sum_crossDiff`. | [G15] §2.4, Fig. 2.1 |
| `MlmcLean/Lattice.lean` | Lattice sums over the MIMC index sets `{θ·ℓ ≤ L}`: `slab_bound`, `tail_bound`, `inner_bound` (with the polynomial factor `(1+L)^{(#critical directions − 1)⁺}`). | [G15] §2.4 (proof) |
| `MlmcLean/Theorem2.lean` | `giles_theorem2_full`: **Theorem 2 (MIMC) in the paper's form**: for `α_d ≥ ½β_d` there are exponents `e₁, e₂` (depending only on `α, β, γ`), equal to `2D₂` and `(D₂−1)(2+η)` when every `α_d > ½β_d`, for which the bound holds on every probability space, for all `D ≥ 1` and all three regimes. `giles_theorem2`: the case `α_d > ½β_d` with the paper's exponents. `giles_theorem2_boundary`: the case `α_d ≥ ½β_d`, whose exponents the paper leaves open, with `e₁ = 2D₂ + (D₃−3)⁺`, `e₂ = (D₂−1)(2+η) + (D₃−1)⁺`, `D₃ = #{d : α_d = ½β_d}` (the paper's exponents when `D₃ = 0`). Deterministic forms `mimc_complexity`, `mimc_complexity_boundary`, `mimc_complexity_core`. The telescoping sum `E[P] = Σ_{ℓ≥0} E[ΔP_ℓ]` of p. 13: along boxes from condition i) (`tendsto_sum_box_integral_crossDiff`) and as an absolutely convergent series under i)–iii) (`hasSum_integral_crossDiff`). | [G15] §2.4, Thm 2 |
| `MlmcLean/Nested.lean` | Haas–Giles nested estimator. `nested_cost_isLeast`: eq. (12) is the least nested cost over all real allocations, attained by the paper's Lagrange allocation `λ_M√(Ṽ/C̃)`, `λ_M√(V^Δ/C^Δ)`; `nested_cost_lower_bound` and `nested_optimal_allocation` (integer sample numbers, up to the rounding overhead `Σ(C̃_ℓ + C^Δ_ℓ)`). `nested_saving`: the claimed saving factor `≈ max_ℓ C̃_ℓ/C^Δ_ℓ` as an inequality between the optimal costs (12) and (8). The nested estimator built from independent inputs has mean `E[P_L]` (9) and variance (11) (`nestedEstimator_mean_variance`) and expected cost (10) (`nestedCost_mean`); `nested_mlmc_mse`: mean, variance and MSE for abstract component estimators. | [HG25] (9)–(12), §2.2 |
| `MlmcLean/ControlVariate.lean` | Plain Monte Carlo (`mc_estimate`), control variates: unbiasedness, variance, the optimal coefficient and the factor `1 − ρ²` (`controlVariate_mean`, `controlVariate_variance`, `controlVariate_optimal`, `controlVariate_estimator`), and the behaviour of the cost (1.1) when `V_ℓC_ℓ` is constant, increasing or decreasing (`optimal_cost_const_product`, `optimal_cost_increasing`, `optimal_cost_decreasing`). | [G15] §1.1–§1.3 |
| `MlmcLean/ErrorAnalysis.lean` | The MSE budget (`mse_lt_of_half`), the weak rate from the second moment (`weak_rate_of_second_moment`), the allocation (3.1) (`allocation_eq_3_1`), the remaining-error estimate and the convergence test (`remaining_error`, `convergence_test_mse`), the consistency check (`consistency_mean`, `consistency_sd`), the standard deviation of the sample variance and the kurtosis (`sampleVariance_sd`, `kurtosis_of_ternary`, `tendsto_kurtosis_atTop`). | [G15] §2.1, §3.1, §3.3 |
| `MlmcLean/LevelDropping.lean` | Non-geometric MLMC: the cost of MLMC on an ordered subset of the levels (`subsetCost_eq`, `subset_optimal_cost`, `sum_subsetCorr`), the exhaustive search over the `2^L` candidate subsets (`card_levelSubsets`, `exists_optimal_subset`), and the level-dropping test (2.5) with its two extreme cases (`levelKeep_product`, `levelDrop_test`, `levelDrop_variance`, `levelDrop_perfect_correlation`, `levelDrop_uncorrelated`). | [G15] §2.6 |
| `MlmcLean/Corrections.lean` | The identity (2.4) for fine/coarse and antithetic estimators and Theorem 1 for them (`integral_fineCoarseDiff`, `integral_antitheticDiff`, `giles_theorem1_corrections`, `giles_theorem1_fineCoarse`, `giles_theorem1_antithetic`). | [G15] §2.1 (2.4) |
| `MlmcLean/Richardson.lean`, `MlmcLean/ML2RComplexity.lean` | Richardson extrapolation (`richardson_extrapolation`); the ML2R weights and their moment conditions (`ml2r_weights`, `ml2r_moment_succ`), the bias `O(2^{−αL(L+1)/2})` (`ml2r_bias_eq`, `ml2r_bias`), the rearranged estimator (`ml2r_rearrange`, `ml2r_estimator_mean_variance`); uniform bounds on the weights, the number of levels and the costs `O(ε⁻²|log ε|)` for `β = γ` and `O(ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)})` for `β < γ` (`ml2r_mse_cost`, `ml2r_complexity_eq`, `ml2r_complexity_lt`). | [G15] §2.3 |
| `MlmcLean/MultiOutput.lean` | Several outputs with a common allocation (`multiOutput_variance`, `multiOutput_optimal`), Hilbert-space-valued outputs (`mlmc_mse_hilbert`, `giles_theorem1_hilbert`), and a counterexample in the sup norm (`sq_norm_add_of_indepFun_fails_sup`). | [G15] §2.5 |
| `MlmcLean/GeometricRates.lean`, `MlmcLean/CostComparison.lean` | Allocation under geometric rates and the case `β = 2α` (`lagrangeN_geometric`, `cost_of_beta_eq_two_alpha`); the standard Monte Carlo cost and complexity `ε^{−2−γ/α}` (`mc_cost`, `mc_cost_lower`, `mc_complexity`), the MLMC saving factors (`mlmc_vs_mc_increasing`, `mlmc_vs_mc_decreasing`), the split of the MSE budget (`split_cost`, `tendsto_split_cost`) and the randomised estimator's half cost (`randomised_half_cost`). | [G15] §1.3, §2.1–§2.2 |
| `MlmcLean/RectangularMIMC.lean` | MIMC on a rectangular index set: box telescoping, the cost and MSE bounds, and when the rectangle suffices (`giles_mimc_rectangular`, `mimc_rect_lower_bounds`, `mimc_rect_necessary`). | [G15] §2.4 |
| `MlmcLean/Algorithm.lean`, `MlmcLean/MLQMC.lean` | Algorithm 1 with exact means and variances: the robust convergence test, termination, the variance and MSE at exit, the cost of Theorem 1 order, and that the algorithm is heuristic (`alg1_terminates`, `alg1_variance`, `robust_test_mse`, `alg1_mse`, `alg1_complexity`, `alg1_not_guaranteed`). Algorithm 2 (MLQMC): the greedy doubling (3.3) reaches the variance target (3.2) (`mlqmc_inner_terminates`), the algorithm stops with `∑ V_ℓ ≤ ε²/2` (`mlqmc_algorithm`) and MSE `≤ ε²` (`mlqmc_mse`). | [G15] §3.1, §3.5 |
| `MlmcLean/Implementation.lean` | The driver's variance estimate from power sums, the floors and the regression for `α, β, γ`, the probability that the consistency check fails (Gaussian `< 0.3%`, Chebyshev `≤ 1/9`), the relative accuracy of the sample variance, and the MLQMC rule (3.3) (`mlqmc_doubling_level`). | [G15] §3.3–§3.5 |
| `MlmcLean/EulerMaruyama.lean`, `MlmcLean/SDEExtras.lean` | The Euler–Maruyama fine/coarse coupling: the coarse path has the law of the level-`ℓ−1` path, (2.4), Theorem 1 for it (`measurePreserving_pairAvg`, `integral_emCoarse`, `em_mlmc_theorem1`), the variance rate from the strong rate (`variance_levelDiff_of_strong`). The §5 steps that need no SDE theory: rates from the timestep, the complexities of the digital option and of Milstein, conditional expectations and (2.4), the Brownian-bridge midpoint, the antithetic swap and its variance `O(h²)` (`measurePreserving_swapIncrements`, `variance_antithetic_le`), splitting (`splitting_mean_variance`: same mean, variance `V[m] + E[v]/M`), the stability of the explicit step, the smoothed CDF and the density as a limit (`tendsto_smoothCDF`, `tendsto_density`). `MlmcLean/GBMEulerMaruyama.lean`: the Euler–Maruyama MLMC estimator for geometric Brownian motion end to end — the exact solution and the Euler–Maruyama path as products of one-step factors, the strong error `E[(S_{t_n} − Ŝ_n)²] ≤ C(t_n) h` (`gbm_em_strong_error`), the consistency of the exact solution across levels (`gbmExact_pairAvg`, `map_gbmExact`), the weak rate `α = ½` and the variance rate `β = 1` for Lipschitz payoffs (`gbm_weak_error_le`, `gbm_correction_variance_le`) and Theorem 1 with no assumed rate (`gbm_mlmc_theorem1`). `MlmcLean/GBMMilstein.lean`: the Milstein MLMC estimator for geometric Brownian motion end to end — the Milstein path (`milsteinPath`, iterating `milsteinStep`) as a product, first-order strong convergence `E[(S_{t_n} − Ŝ_n)²] ≤ C(t_n) h²` (`gbm_mil_strong_error`, from the Gaussian moments up to `E[Z⁴] = 3` and a second-order bound on `aⁿ − 2bⁿ + cⁿ`), the weak rate `α = 1` and the variance rate `β = 2` for Lipschitz payoffs (`gbm_mil_weak_error_le`, `gbm_mil_correction_variance_le`) and Theorem 1 with cost `O(ε⁻²)` (`gbm_mil_mlmc_theorem1`). | [HG25] (2), (4)–(5); [G15] §5 |
| `MlmcLean/PDEExamples.lean` | Pathwise errors give `α` and `β = 2α` (`rates_of_pathwise`, `elliptic_rates`), the discrete maximum principle and stability of the explicit heat scheme for `k/h² ≤ ½`, the cost factor 8 (`parabolic_cost`), Euler–Maruyama = Milstein for additive noise, and the complexity (`pde_complexity`). | [G15] §7.1 |
| `MlmcLean/PoissonCoupling.lean` | Tau-leaping and the Anderson–Higham Poisson coupling: the marginals are the fine and coarse tau-leaping chains, (2.4), the moments of the coupled difference, the correction variance `O(h)` for a Lipschitz, bounded propensity and a Lipschitz payoff (`β = 1`: the coupled paths are `O(h)` apart in mean square at the final time), and the complexity statements (`coupled_increments_hasLaw`, `integral_sq_coupledIncr_sub`, `coupledChain_fst`, `coupledChain_snd`, `tauLeaping_2_4`, `coupledChain_sq_le`, `variance_coupledChain_le`, `tauLeaping_level_variance`, `tauLeaping_complexity`). `MlmcLean/TauLeapingMLMC.lean`: Theorem 1 for the tau-leaping estimator with the Poisson coupling — square-integrable payoffs, (2.4), `β = 1` on every level, and MSE `< ε²` at cost `O(ε⁻²(log ε)²)` given the weak rate `α ≥ ½` of tau-leaping (`lintegral_sq_tauChain_lt_top`, `integral_tauCoarse`, `variance_tauCorrection_le`, `tauLeaping_mlmc_theorem1`). | [G15] §8 |
| `MlmcLean/NestedSimulation.lean`, `MlmcLean/NestedMLMC.lean` | Nested simulation: the antithetic difference (with the constant `−1/8`, correcting the paper's `−1/4`), moment bounds, the exponents of §9.1–§9.2, and the nested MLMC estimator with its expectation, the rates `α = 1`, `β = 2` and the complexity `O(ε⁻²)` (`antithetic_quadratic`, `nested_variance_rate`, `nested_mean_rate`, `nested_complexity`). | [G15] §9 |
| `MlmcLean/MarkovChain.lean` | Markov chains started in the past: the coupled chains contract (`lintegral_dist_backIter_le`, `lintegral_dist_start_le`), the correction variance decays like `ρ^{N_{ℓ−1}}` (`variance_levels_le`), and the example `X_{n+1} = X_n/2 + ξ_n` has the uniform law on `[0, 2]` as invariant law (`map_halfStep`). `MlmcLean/MarkovLimit.lean`: the chain started `n` steps in the past has the law of `X_n` (`map_backIter_eq_map_fwdIter`), the chains started in the past converge almost surely (`ae_tendsto_backIter`), and the distribution of `X_n` converges weakly to that of a limit `X_∞` (`tendstoInDistribution_fwdIter`). | [G15] §10.1 |
| `MlmcLean/ApproxNormal.lean` | Approximate normal random variables: the `L²` projection behind (14)–(15), the lookup tables of methods 1–3, (16)–(19), the coupling (17), and that methods 2 and 3 cannot beat method 1 (`intervalMean_isLeast`, `method1_le`, `method1_le_perm`). `MlmcLean/LUTLimits.lean`: as `d → ∞` the MSE of method 1 (uniform intervals) tends to `0` for monotone `f` (`tendsto_method1MSE`), while that of method 3 (dyadic intervals) stays above a positive constant where `f` is strongly concave (`dyadic_mse_ge`, `method3_mse_ge`, `method3_mse_not_tendsto_zero`). | [HG25] §3 |
| `MlmcLean/RoundingError.lean`, `MlmcLean/FixedPointPath.lean` | Fixed-point rounding and its error bounds (20)–(22), the error-variance model (25)–(29) with the independent and fully correlated cases (`variance_linearised_indep`, `variance_linearised_corr`, `vIndep_le_vCorr`), the GBM path of Algorithm 1, the sizes (39)–(41) of its variables and the accumulation of rounding errors along the path (`integral_abs_roundFixed_path_sub_le`). | [HG25] §4, §6.3 |
| `MlmcLean/BitWidth.lean`, `MlmcLean/LagrangeBitWidth.lean` | The cost model (30)–(34), the separable optimisation, the Lagrange conditions (35) and (37) (sufficient and necessary), the ratio (38), the trends of §6.3 and the lookup-table size (`levelwise_optimisation`, `exists_unique_bitWidth`, `greedy_rounding_feasible`, `exists_eq35_isMin`, `eq35_of_isLocalMinOn`, `eq37_iff`). | [HG25] §5–§6 |
| `MlmcLean/ML2RTheorem.lean` | ML2R end to end: the sharp weight bound `|w_ℓ| ≤ B² r^{(L−ℓ)(L−ℓ+1)/2}` (`abs_ml2rWeight_le_sharp`), the bias from the weak-error expansion, `≤ C_α K 2^{−αL(L+1)/2}` uniformly in `L` (`ml2r_bias_le`; the printed `2^{−αL²}` is not attainable), and the ML2R estimator's MSE `< ε²` at cost `O(ε⁻²|log ε|)` for `β = γ` and `O(ε⁻²2^{(γ−β)√(2 log₂(1/ε)/α)})` for `β < γ` (`ml2r_theorem_eq`, `ml2r_theorem_lt`). | [G15] §2.3 |
| `MlmcLean/Theorem2.lean` (index set) | Theorem 2 on the simplex `{θ·ℓ ≤ L}`, `θ_d = α_d + (γ_d − β_d)/2`: the index set "of the form `ℓ·n ≤ L`" achieves the bounds (`giles_theorem2_indexSet`, `giles_theorem2_boundary_indexSet`, `mimc_complexity_core_indexSet`). | [G15] §2.4, p. 15 |
| `MlmcLean/AsymptoticNormal.lean` | Asymptotic normality from Mathlib's central limit theorem: each level estimator (`tendstoInDistribution_levelEstimator`) and, for a fixed number of levels with `N_ℓ = m_ℓ n`, the MLMC estimator, `√n (Y − E[P_L]) → N(0, Σ V_ℓ/m_ℓ)` (`tendstoInDistribution_mlmcEstimator`); sums of independent `N(0, 1/n)` are `N(0, 1)` and sums of approximate normals are approximately normal (`sum_gaussian_hasLaw`, `tendstoInDistribution_sum_of_approxNormal`, `tendstoInDistribution_sum_inv_sqrt_mul`). | [G15] §2.1 p. 8; [HG25] §3.2 |
| `MlmcLean/GilesRemarks.lean`, `MlmcLean/RandomShiftQMC.lean` | The randomised variance between `Σ V_ℓ/p_ℓ` and `(1+δ) Σ V_ℓ/p_ℓ` when `E_ℓ² ≤ δV_ℓ` (`singleTerm_variance_le_of_sq_le`), the combined variance and cost of two kept levels (`levelKeep_combined`), splitting to leading order iff `E[v]/V[m] = o(1/h)` (`splitting_leading_order`), `N_ℓ` linear for Markov chains (`markov_linear_levels`); a uniform random shift makes a QMC rule unbiased and independent shifts give i.i.d. replicates with an unbiased variance estimate (`shiftedQMC_unbiased`, `randomShift_replicates`). | [G15] §2.2, §2.6, §3.5, §5.2, §10.1 |
| `MlmcLean/SDEDigital.lean`, `MlmcLean/SDEMisc.lean` | The §5 probability steps not in `SDEExtras`: Lipschitz payoffs; the digital option's variance from the strong error, `O(h^{1/3})` from mean square (sharp: `digital_mismatch_exponent_sharp`), `β = 1/3` for GBM with no assumption (`gbm_digital_variance_le`); conditional expectation of the last step with the `Φ` formulas, (2.4) and `V₀ = 0` (`digital_smoothing`, `digital_smoothing_coarse`, `digital_smoothing_level_zero`); Gaussian change of measure; the call payoff's derivative; the antithetic bound in `d` dimensions and for the call (`variance_antithetic_le_fderiv`, `variance_call_antithetic_le`); explicit versus tamed Euler steps for super-linear drift; the smoothed CDF for any bounded smoother; the density of a `d`-dimensional output. | [G15] §5.1–§5.7 |
| `MlmcLean/ApplicationExtras.lean`, `MlmcLean/PoissonGrids.lean` | Summed Lévy increments have the coarse law, so (2.4) holds (`integral_levyCoarse`, `levy_telescoping`); exponential periods concentrate at `T`; FE with midpoint quadrature is the FD scheme (`fe_eq_centralDiff`); the elliptic rates `α = 2`, `β = 4` with a random `K` (`elliptic_rates_random`; no deterministic `K` exists, `not_ae_abs_gaussian_sq_mul_le`); the §7.3 scheme is one Milstein step (`spdeScheme_eq_milstein`); the Brownian-bridge and variable-precision paths agree in both roles (`bb_telescoping`, `vp_telescoping`); Poisson counts summed on union grids and tau-leaping on non-nested grids keep the laws, so (2.4) holds (`unionGrid_2_4`, `unionChain_2_4`); truncating increments breaks it (`roundFixed_sum_inconsistent_general`). | [G15] §6.2, §7, §8, §10.2 |
| `MlmcLean/MarkovLimitLaw.lean` | The level bias decays geometrically (`abs_integral_sub_limit_le`); the law of the limit is the unique invariant law (`existsUnique_invariant`, `invariant_unique`), `U[0, 2]` in the example (`halfStep_invariant_unique`, `halfStep_limit_uniform`); Glynn–Rhee's randomised estimator of `E[f(X_∞)]` is unbiased with finite variance and cost (`markov_randomised_mlmc`), and MLMC reaches MSE `< ε²` at cost `O(ε⁻²)` (`markov_mlmc_theorem1`). | [G15] §10.1 |
| `MlmcLean/NestedRates.lean` | The §9.2 Taylor expansion with the coefficient `−1/8` (`mimc_antithetic_quadratic`, `abs_mimc_antithetic_taylor_le`); nested MLMC with `2^ℓ` inner samples of a level-`ℓ` inner approximation (e.g. `2^ℓ` Milstein steps, whose weak and strong orders are hypotheses): `α = 1`, `β = 2`, `γ = 2` and cost `O(ε⁻²(log ε)²)` (`nested_sde_bias_rate`, `nested_sde_variance_rate`, `nested_sde_mlmc_complexity`); a piecewise linear `f`: `β = 3/2`, `α = ½` and cost `O(ε⁻²)` when the inner mean has little mass near the kink, e.g. a bounded density (`antithetic_kink`, `nested_kink_variance_rate_of_density`, `nested_kink_mlmc_complexity`); the nested MIMC rates `E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})`, `V_ℓ = O(2^{−2ℓ₁−2ℓ₂})` (`nested_mimc_mean_rate`, `nested_mimc_variance_rate`). | [G15] §9.1–§9.2 |
| `MlmcLean/HaasGilesRemarks.lean` | The plotted cost factor and when the nested estimator is cheaper (`nestedCost_le_of_costFactor_le`; the full cost (32) needs `ρ²(1+ρ²) < 1`, `exists_costFactor_lt_one_nestedCost_gt`), two-sided sizes of the path variables (39)–(41) (`gbmPath_size_bounds`, `gbmPath_sq_largest`), and the accumulated rounding error with fixed precision: exact variance, lower bound, and it exceeds the discretisation error for small `h` (`perturbed_path_sub_mean_variance`, `strongError_lt_integral_sq_perturbed_path_sub`). | [HG25] §6.1, §6.3 |
| `MlmcLean/MLMCCentralLimit.lean` | The Lindeberg and Lyapunov central limit theorems for triangular arrays (`tendstoInDistribution_lindeberg`, `tendstoInDistribution_lyapunov`); asymptotic normality of the MLMC estimator with a growing number of levels, `(Y_k − E[P_{L_k}])/σ_k → N(0, 1)`, under Lyapunov's condition or a uniform bound on the standardised `(2+δ)`-th moments with `min_ℓ N_{k,ℓ} → ∞` (`tendstoInDistribution_mlmcEstimator_lyapunov`, `tendstoInDistribution_mlmcEstimator_of_moment_le`; without such a hypothesis the paper's "therefore so is `Y`" fails, counterexample in the module docstring); the confidence intervals of Collier et al. with the exact `σ_k`, around `E[P_{L_k}]`, around `E[P]` when the bias is `o(σ_k)`, and with the tolerance split (`tendsto_measureReal_abs_mlmcEstimator_sub_le`, `tendsto_measureReal_abs_mlmcEstimator_sub_le_of_bias`, `eventually_lt_measureReal_abs_mlmcEstimator_sub_le_tol`). | [G15] §2.1 p. 8 |
| `MlmcLean/QMC1D.lean` | QMC in one dimension: one point per cell `[i/N, (i+1)/N]` integrates `f` of bounded variation with error `≤ V(f)/N` (`qmc_error_le_of_boundedVariationOn`); the (randomly shifted) rank-1 lattice `{(i+u)/N}` and its shift modulo `1`: error `≤ V(f)/N` for every shift, unbiased with variance `≤ V(f)²/N²`, `R` replicates with variance `≤ V(f)²/(RN²)` and an unbiased variance estimate (`latticeRule_randomShift`, `latticeRule_replicates`, `rank1Lattice_torus_replicates`), against `Var[f(U)]/N` for Monte Carlo (`latticeRule_vs_monteCarlo`, `variance_latticeRule_id_vs_mc`); MLQMC with a shifted lattice per level reaches MSE `< ε²` at cost `O(ε^{−max(1, g/a)})` when `b > g` and `O(ε^{−max(1+(g−b)/a, g/a)})` when `b < g`, so `p < 2` whenever `g < 2a` and `g < a + b` (`mlqmc_complexity`, `mlqmc_complexity_of_lt`, `mlqmc_complexity_lt_two`). QMC in `d` dimensions (discrepancy theory) is not formalised. | [G15] §1, §2.7, §3.5 |
| `MlmcLean/ConsistencyCheck.lean` | The consistency check with empirical variances: the empirical variance is consistent (`tendsto_empVar_ae`, strong law), `(a − b + c)/σ → N(0, 1)` for two independent samples of any sizes growing at any rates (`tendstoInDistribution_twoSample`, `tendstoInDistribution_consistencyStat`), and the check fails with asymptotic probability at most `P(|Z| ≥ 3) < 0.3%` (`consistency_check_empirical`, `consistency_check_empirical_lt`); the bound is attained (`consistency_check_empirical_sharp`), and for a fixed sample size it can fail (module docstring). | [G15] §3.3 p. 22 |
| `MlmcLean/NestedKinkSde.lean` | Nested simulation with a piecewise linear `f` and discretised inner paths (inner weak order 1 and strong order 1/4 as hypotheses): the bias has `α = 1` under a small-ball hypothesis (`nested_kink_bias_rate_one`, `nested_kink_sde_bias_rate`), `β = 3/2` (`nested_kink_sde_variance_rate`), and MSE `< ε²` at cost `O(ε^{−5/2})` (`nested_kink_sde_mlmc_complexity`); an explicit example meeting every hypothesis (`kinkInnerApprox_hypotheses`, `kinkInnerApprox_mlmc_rates`) refutes the paper's MIMC rates `β₁ = β₂ = 1.5` (`kinkMimc_variance_ge`, `nested_mimc_kink_rates_false`). | [G15] §9.2 p. 60 |
| `MlmcLean/MLMCConfidenceEstimated.lean` | Collier et al.'s confidence intervals with estimated variances `σ̂_k² = ∑_ℓ s_ℓ²/N_{k,ℓ}`: `σ̂_k/σ_k → 1` in probability for a fixed number of levels (strong law) and for a growing one under a kurtosis bound (`E|s_N² − V| ≤ (√((κ−1)/N) + 1/N) V`, `integral_abs_empVar_sub_le`); `P(|Y_k − E[P_{L_k}]| ≤ zσ̂_k) → 2Φ(z) − 1` (`tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd_fixed`, `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd`), around `E[P]` (`…_estSd_of_bias`), and the tolerance test with estimated variances (`eventually_lt_measureReal_test_and_abs_sub_le_tol`). | [G15] §2.1 p. 8 |
| `MlmcLean/NestedMimcKink.lean` | The corrected MIMC rates for nested simulation with a piecewise linear `f`: `V[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` (`nested_mimc_kink_variance_rate`, sharp: `nested_mimc_kink_rate_sharp`) and `|E[Y_ℓ]| = O(2^{−ℓ₁/2−ℓ₂})` (`nested_mimc_kink_mean_rate`); Theorem 2 gives MSE `< ε²` at cost `O(ε⁻²|log ε|⁴)` (`nested_mimc_kink_complexity`), below MLMC's `O(ε^{−5/2})` (`nested_mimc_kink_beats_mlmc`). | [G15] §9.2 p. 60 |
| `MlmcLean/LUTAsymptotics.lean` | The lookup-table MSEs as `d → ∞`: method 3 (dyadic intervals, least-squares affine values) converges to `C = 2∑_k E_k > 0` (`exists_tendsto_method3MSE`, `tendsto_method3MSE`, `method3Limit_pos`), the error on each dyadic interval decreasing with `d` (`dyadic_groupMSE_eq`, `groupMSE_quadratic`); method 1 (uniform intervals) has MSE of order `2^{−d}/d` (`method1MSE_order`), so `log(MSE)/d → −log 2` (`tendsto_log_method1MSE_div`). | [HG25] §3.4 |
| `MlmcLean/EulerSuperlinear.lean` | For `dS = −S³dt + dW`: bounded noise cannot stop the doubly exponential growth of the explicit scheme (`eulerCubic_noise_growth`), Gaussian lower bounds (`le_gaussianReal_real_Icc`, `le_gaussianReal_real_Ici`), and Hutzenthaler–Jentzen–Kloeden's divergence `E|X_N|^p → ∞` as the timestep `T/N → 0` (`emCubic_moment_ge`, `emCubic_moment_tendsto_atTop`); the tamed scheme instead has `E|X_N| ≤ max(|x₀|, 1) + √(TN)` and `E X_N² ≤ x₀² + T` uniformly in `N ≥ T/54` (`tamedPath_integral_abs_le`, `tamedCubic_second_moment_le`, `tamedCubic_nonexpansive_iff`). | [G15] §5.6 p. 44 |
| `MlmcLean/MLQMCBoundary.lean` | The one-dimensional MLQMC cost in the boundary case `b = g ≤ a` is `Θ(ε⁻¹|log ε|^{3/2})`: upper bound (`mlqmc_boundary_complexity_core`, `mlqmc_boundary_complexity` for randomly shifted lattices) and lower bounds for every allocation (`mlqmc_boundary_cost_lower`, `mlqmc_boundary_exponents_optimal`); the finest level alone costs `≥ c ε^{−g/a}`, so `g < 2a` is necessary for `p < 2` (`mlqmc_finest_level_cost_lower`, `mlqmc_finest_level_exponent_optimal`). | [G15] §2.7, §3.5 |
| `MlmcLean/NestedMimcSmooth.lean` | Nested MIMC with a smooth payoff end to end: `E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` and `V_ℓ = O(2^{−2ℓ₁−2ℓ₂})` on all of `ℕ²`, boundary levels included (`nested_mimc_smooth_variance_rate`, `nested_mimc_smooth_mean_rate`), and MSE `< ε²` at cost `O(ε⁻²)` on the simplex index set (`nested_mimc_smooth_complexity`). | [G15] §9.2 p. 60 |
| `MlmcLean/BitWidthOptimum.lean` | The optimal relaxed bit-widths: a minimiser of the level cost (34) exists without convexity (`exists_isMinOn_bitLevelCost_of_nonneg`), satisfies (35)–(36) with `λ* = √(V V^Δ/(C C̃))` and minimises the λ-function (`lagrange_of_isMinOn_bitLevelCost`, `isMinOn_lambda_bitLevelCost`), and beats every uniform bit-width (`exists_best_uniform_bitLevelCost`, `bitLevelCost_lt_uniform`); (34) is strictly convex without additions (`strictConvexOn_bitLevelCost`, `existsUnique_isMinOn_bitLevelCost`) but not in general (`not_convexOn_bitLevelCost`). | [HG25] §6.1 |
| `MlmcLean/EllipticFD.lean` | The one-dimensional elliptic example: exact solution and exact finite-difference solution (`ellipticSol`, `ellipticFDSol`), `\|P − P_ℓ\| ≤ (50/3) Z² h_ℓ²` with a random constant (`ellipticFD_error`, `ellipticPl_error`), and `α = 2`, `β = 4` end to end (`elliptic_fd_rates`). | [G15] §7.1 |
| `MlmcLean/GilesCorollaries.lean` | A dissipative SDE's Euler–Maruyama step is a mean-square contraction, so MLMC for the limit of the chain costs `O(ε⁻²)` (`emStep_meanSquare_contraction`, `contracting_sde_mlmc`); the lookup-table streams tend to `N(0, 1)` (`lutStream_tendstoInDistribution`, `lutStreams_sum_tendstoInDistribution`); plain MC costs `ε⁻⁴`, `ε⁻³` (`mc_exit_time_complexity`); `β ≤ 2α` (`beta_le_two_alpha`); the `D = 1` necessity of `γ < β` (`mlmc_optimal_complexity_necessary`); Euler–Maruyama with refinement factor `M` and Theorem 1 (`integral_emCoarseM`, `em_mlmc_theorem1_M`). | [G15] §2.1, §2.4, §5.1, §5.5, §10.1; [HG25] §3.2 |
| `MlmcLean/GBMPathDependent.lean` | Discretely monitored Asian and lookback options for GBM (Table 5.2 at fixed monitoring dates): mean-square errors `O(h)` (Euler–Maruyama) and `O(h²)` (Milstein), `V_ℓ = O(h)` and `O(h²)` (`gbm_em_asian_variance_le`, `gbm_mil_lookback_variance_le`, …), and Theorem 1 end to end (`gbm_em_asian_theorem1`, `gbm_mil_asian_theorem1`, `gbm_em_lookback_theorem1`, `gbm_mil_lookback_theorem1`). Continuous monitoring is not formalised. | [G15] §5.1, §5.2 |
| `MlmcLean/SPDEStability.lean` | The SPDE scheme of §7.3 is the Milstein step with increment `√k Z_n` (`spdeStep_eq_milstein`); mean-square von Neumann stability iff `λ(1 + 2ρ²) ≤ 1`, `λ = k/h²` (`spde_meanSquare_stable`, `spde_meanSquare_unstable`, `spde_meanSquare_stable_periodic`), hence `k_ℓ = k_{ℓ−1}/4` when `h_ℓ = h_{ℓ−1}/2` and the cost factor 8 (`spde_level_refinement`, `spde_level_cost`). | [G15] §7.3 |
| `MlmcLean/DriftImplicit.lean` | The drift-implicit Euler step is well posed for one-sided Lipschitz drifts (`existsUnique_implicitStep`); for `dX = −X³ dt + σ dW` its second and fourth moments stay bounded for every step size, where those of explicit Euler diverge (`implicitPath_moments_le`, `implicit_vs_explicit_cubic_moments`); the deterministic analogue (`implicitCubic_stable_explicitCubic_threshold`); the integrating factor for a stiff linear drift (`intFactorPath_second_moment_le`, `emLinear_second_moment_tendsto_atTop`). | [G15] §5.6 |
| `MlmcLean/BrownianPaths.lean` | Brownian paths on the union of two grids (Algorithm 3, deterministic grids): summed increments have the correct joint law on either grid (`unionGridBM_increments`, `unionGrid_brownian_map_eq`); the Brownian-bridge midpoint law (`bridge_midpoint_law`, `brownian_bridge_midpoint`); weighted averages of interpolants (`bridgeInterp_weighted_sum`); time reversal of a pre-Brownian motion within each coarse step is pre-Brownian and swaps the fine increments (`isPreBrownianReal_antitheticBM`, `fineIncrements_antitheticBM`). | [G15] §5.2, §5.3, §5.6 |
| `MlmcLean/GBMDigital.lean` | The digital option for GBM: the Milstein correction variance `O(h^{2/3})` (`gbm_mil_digital_variance_le`); `E[(ΔP)⁴] = P(ΔP ≠ 0) ≤ C h^{1/3}` (Euler–Maruyama) and `C h^{2/3}` (Milstein) (`gbm_em_digital_fourth_moment_le`, `gbm_mil_digital_fourth_moment_le`); the exponent `1/3` from mean square cannot be improved (`digital_mismatch_exponent_sharp`); the coarse smoothed payoff that reuses the fine increment has the fine payoff's mean, so (2.4) holds (`map_milsteinEM_coarse_eq_fine`, `digital_smoothing_milsteinEM_mean_eq`, `gbm_digital_smoothing_mean_eq`). The paper's rates `O(h^{1/2})`, `O(h)` and the kurtosis rates are not proved. | [G15] §5.1, §5.2 |
| `MlmcLean/TauLeapingExact.lean` | The exact continuous-time chain with bounded rates, by uniformisation (`exactLaw`): a probability measure with the semigroup property (`exactLaw_add`), independent of the uniformisation rate (`exactLaw_eq_of_bound`), solving the backward, forward and master equations (`exactLaw_master_equation`), and the only semigroup with the same uniform `O(t²)` generator expansion (`exactLaw_unique`); tau-leaping has weak order 1 against it for bounded payoffs (`tauLeaping_weak_error_exact`), and MLMC with the exact chain as target needs no assumed weak rate (`tauLeaping_mlmc_exact`). | [G15] §8 |
| `MlmcLean/InverseNormal.lean` | The standard normal CDF `Φ` (`normCDF`) and its inverse (`normCDFInv`): continuity, strict monotonicity, symmetry, `Φ⁻¹(U) ~ N(0, 1)` (`hasLaw_normCDFInv`), derivatives, concavity and Mills-ratio bounds; the lookup-table results for `f = Φ⁻¹` with no hypothesis on `f`: the streams tend to `N(0, 1)` (`lutStream_normCDFInv_tendstoInDistribution`), the dyadic MSE has a positive limit (`tendsto_method3MSE_normCDFInv`, `method3_mse_ge_normCDFInv`), and the uniform-table MSE is of order `2^{−d}/d` (`method1MSE_order_normCDFInv`, `tendsto_log_method1MSE_normCDFInv`). | [HG25] §3 |
| `MlmcLean/EndToEndInstances.lean` | End-to-end instances: the elliptic estimator of §7.1 at cost `O(ε⁻²)` (`elliptic_mlmc_theorem1`); the discounted call for GBM with Euler–Maruyama and Milstein (`gbm_call_mlmc_theorem1`, `gbm_mil_call_mlmc_theorem1`); GBM with refinement factor `M` (`gbm_mlmc_theorem1_M`); the tamed scheme's fourth moment (`tamedCubic_fourth_moment_le`); the method-2 iteration of Haas–Giles §3.2 is well defined (`exists_lsq_minimiser`, `method2_iteration_exists`); rounding the coarse increment directly and rounding the fine increments first give different means or laws (`roundFixed_coarse_increment_mean`, `truncGrid_coarse_increment_mean_lt`). | [G15] §5.1, §5.6, §7.1, §10.2; [HG25] §3.2 |
| `MlmcLean/JumpProcesses.lean` | §6 without Lévy-process theory: for an exponential Lévy model with exact increments on uniform steps (a discrete analogue of Table 6.3's Asian row), the fine and coarse Asian averages are `O(h)` apart in root mean square, so `β = 2`, and Theorem 1 holds end to end (`levy_asian_avg_sq_le`, `levy_asian_theorem1`, `jumpDiffusion_asian_theorem1`); jump-adapted grids with a constant rate satisfy (2.4), for fixed and for random jump times (`jumpAdapted_coarse_map_eq`, `jumpAdapted_random_2_4`); the thinning change of measure is unbiased and respects the telescoping sum (`thinning_lr_unbiased`, `thinning_mlmc_correction`). | [G15] §6 |
| `MlmcLean/EstimatorRemarks.lean` | A counterexample to "each level is asymptotically normal, and therefore so is `Y`" with a growing number of levels: every level estimator is asymptotically normal but the normalised MLMC estimator tends to `0` in probability, not to `N(0, 1)`, and Lindeberg's and Lyapunov's conditions fail (`exists_mlmc_clt_counterexample`, `mlmc_clt_counterexample_conditions`); the consistency check with one sample per level fails with probability 1 and with two samples, in the module's Gaussian example, with probability `(2/π) arctan(√2/3) ≈ 0.280` (biased variance estimate) or `(2/π) arctan(1/3) ≈ 0.205` (unbiased) (`consistency_check_one_sample`, `consistency_check_two_samples`); the mean and variance of the unbiased and biased sample variance, and their standard deviation `√((κ − 1)/N) σ²(1 + O(1/N))` (`sampleVar_mean_variance`, `sampleVar_sd`, `tendsto_sampleVar_sd_div`, `empVar_sd`). | [G15] §2.1, §3.3 |
| `MlmcLean/SDEExtensions.lean` | Drift-implicit Euler with multiplicative noise has second moments bounded uniformly in the step size (`implicitPathMult_second_moment_le`, sharp: `implicitPathMult_second_moment_sharp`); the time-reversed path of a Brownian motion is a Brownian motion, with continuous paths, and has the same running maxima in law (`isBrownianReal_antitheticBM`, `map_iSup_antitheticBM`); nested simulation with a payoff with finitely many kinks has `β = 3/2` and cost `O(ε⁻²)` (`nested_kinks_variance_rate`, `nested_kinks_mlmc_complexity`). | [G15] §5.3, §5.6, §9.1 |
| `MlmcLean/ContractingLevels.lean` | Contracting SDEs with level-dependent steps and horizons: the fine path (step `h`, interval `[−T_ℓ, 0]`) and the coarse path (step `2h`, `[−T_{ℓ−1}, 0]`, sharing the summed increments) are `O(h)`-close in mean square up to the contraction of the unshared start (`integral_sq_fine_sub_coarse_le`), so `V_ℓ = O(2^{−ℓ})` for `T_ℓ` growing linearly (`variance_contractLevels_le_two_pow`) and MLMC for the limit of the discretised chains has cost `O(ε^{−2−η})` for every `η > 0` (the cost per sample grows like `ℓ 2^ℓ`) (`contracting_levels_mlmc`), improved to `O(ε⁻²|log ε|³)` in `Theorem1Log.lean`. Identifying that limit with the SDE's invariant law is not formalised. | [G15] §10.1 |
| `MlmcLean/AdaptiveGrids.lean` | Path-dependent (adaptive) time steps on a fixed base grid, by discrete conditioning: given the path so far, or the whole history of base increments used, the increment over an adaptively chosen step is `N(0, n_k δ)` (`adaptiveIncr_condLaw_gaussian`, `histIncr_condLaw_gaussian`) and a Poisson count is `P(λh_k)` (`adaptiveCount_condLaw`, `histCount_condLaw`); the fine and the coarse path with independent adaptation rules each have their single-level law, so (2.4) and Theorem 1 hold for non-nested grids (`adaptiveEM_fine_coarse`, `adaptiveEM_2_4`, `adaptiveEM_mlmc_theorem1`); the pair of paths read off Algorithm 3 has the law of the two single-level paths computed from one sequence of base increments (`algorithm3_joint_law`, `algorithm3_EM_joint_law`). | [G15] §5.6, §8 |
| `MlmcLean/LatticeRuleD.lean` | Randomly shifted rank-1 lattice rules in `d` dimensions: the variance is the dual-lattice sum `∑_{k ∈ L^⊥∖{0}} |f̂(k)|²` (`hasSum_variance_rank1Lattice`, with Parseval's identity on `𝕋^d`), unbiased replicates (`rank1Lattice_replicates`), at most the Monte Carlo variance (`variance_rank1Lattice_le_variance`), the bound `|Q(u) − ∫f| ≤ ∑_{L^⊥∖{0}} |f̂(k)|` for every shift (`abs_rank1Lattice_sub_integral_le`); MLQMC with a dimension growing with the level has cost `O(ε^{−p})`, `p < 2`, when `g < 2a` and `g < a + b`, assuming the decay of the dual-lattice sums (`mlqmcLattice_complexity`, `mlqmcLattice_complexity_lt_two`, `mlqmcLattice_complexity_rate`). | [G15] §1, §2.7, §3.5 |
| `MlmcLean/Theorem1Log.lean` | Theorem 1 when the cost per sample has a polylogarithmic factor, `C_ℓ ≤ c₃(ℓ+1)^κ 2^{γℓ}` (an extension not stated in the paper): the cost bounds gain `|log ε|^κ` (`giles_theorem1_log`, uniform constant `giles_theorem1_log_uniform`, general corrections `giles_theorem1_corrections_log`, `giles_theorem1_fineCoarse_log`), the exponents cannot be lowered for the model problem with equality in the rate conditions (`mlmc_cost_lower_log`), except that `O(ε⁻²)` remains when `β > γ` and `γ < 2α` (`giles_theorem1_log_of_lt`); so the contracting SDEs of §10.1 cost `O(ε⁻²|log ε|³)` (`contracting_levels_mlmc_log`). | [G15] §2.1, §10.1 |
| `MlmcLean/GBMStrongLp.lean` | Strong errors of Euler–Maruyama and Milstein for GBM in every `L^{2m}`: `E[(S_{t_n} − Ŝ_n)^{2m}] ≤ C_m h^m`, resp. `C_m h^{2m}`, with explicit constants (`gbm_em_moment_error`, `gbm_mil_moment_error`); for the digital option the mismatch probability, `V_ℓ` and `E[(P_ℓ − P_{ℓ−1})⁴]` are `≤ C h_ℓ^q` for every `q < ½` (Euler–Maruyama) and every `q < 1` (Milstein), with `C` uniform in `S₀` and `K`, and the kurtosis is at least `(C h_ℓ^q)⁻¹` (`gbm_em_digital_rate`, `gbm_mil_digital_rate`): the paper's exponents up to an arbitrarily small loss. The constants are loose, so the gain over `GBMDigital` is asymptotic only. | [G15] §5.1, §5.2 |

No `sorry` and no extra axioms (see Verification below).

### Modelling choices

* **Estimators are the primitive in Theorems 1 and 2.** Following Giles ("independent estimators
  `Y_ℓ` based on `N_ℓ` Monte Carlo samples, each with expected cost `C_ℓ` and variance `V_ℓ`"),
  `giles_theorem1` and `giles_theorem2` take `Y ℓ n : Ω → ℝ` for every level and sample size
  `n ≥ 1`, with `V[Y ℓ n] = V_ℓ/n` and pairwise independence across levels. The estimator (2.2)
  itself is built and shown to satisfy these in `StandardEstimator.lean`.
* **Random cost.** The cost of `Y ℓ n` is a random variable with `E[Cost ℓ n] = n·C_ℓ`, and the
  theorems bound `E[C]`, as Giles does ("the simulation cost of individual samples is itself
  random", p. 7).
* **Conditions for `n ≥ 1` only.** The estimator (2.2) with zero samples is `0`, which is not
  unbiased, so the conditions (including square-integrability) are required for sample sizes
  `n ≥ 1`, the only ones the theorems use.
* **Pairwise independence.** Across levels (and across multi-indices, and across the `2(L+1)`
  nested components) only pairwise independence is assumed, which is weaker than the papers'
  independence and is all the variance formulas need.
* **Real sample numbers in the allocation results.** As in the papers, the optimisation treats
  `N_ℓ` as real numbers; the variance constraint is `≤ τ` (the minimiser meets it with equality).
  The integer allocations are the rounded-up Lagrange values.
* **Strict `MSE < ε²`.** This comes from bias `≤ ε/2` and variance `≤ ε²/2`. Giles uses `ε/√2`
  and `ε²/2`; the constant `c₄` absorbs the difference.
* **MIMC summation region.** `𝓛 = {ℓ : θ·ℓ ≤ L}` with `θ_d = α_d + (γ_d − β_d)/2`, a region "of
  the form `ℓ·n ≤ L`" as Giles describes (p. 15). Giles lists the conditions of Theorem 2 as
  i), iii), ii), iv), v); the hypothesis names follow that labelling.
* **Haas–Giles (12)** is an optimal-allocation formula, not a rate theorem. The paper derives it
  with Lagrange multipliers, "ignoring the small increase in the cost when `N_ℓ` are rounded up".
  We prove it as a lower bound for every allocation that is achievable up to exactly that
  rounding term.
* **Randomised MLMC finiteness.** The paper only claims that the two series `Σp_ℓ⁻¹V_ℓ` and
  `Σp_ℓC_ℓ` can be made finite for `β > γ`; the full variance also contains `Σp_ℓ⁻¹E_ℓ²`, which
  can diverge under (i)–(iv) alone. `randomised_mlmc_finite` uses the second-moment form of (iii)
  that Giles mentions on p. 7. The cost of a sample on level `ℓ` is a random variable `κ_ℓ`
  independent of the random level, so the expected cost of one sample is `Σp_ℓ E[κ_ℓ]`
  (`integral_cost_level`).
* **Theorem 2's exponents.** The paper states Theorem 2 under `α_d ≥ ½β_d` but gives the
  exponents only when `α_d > ½β_d`; `giles_theorem2_full` states exactly that (the exponents
  exist, and are the paper's in the strict case). The explicit boundary exponents of
  `giles_theorem2_boundary` are this formalisation's.
* **Hypotheses in place of SDE theory.** Where a claim of §5, §9 or §10 rests on the convergence
  order of a discretisation, that order is a hypothesis of the Lean statement (for example the
  Milstein weak and strong orders of the inner paths in `NestedRates.lean`, or the mean-square
  strong rate in `SDEDigital.lean`). Where the paper's argument needs more than the order, the
  extra hypothesis is stated: a bounded density of the underlying for the digital option (§5.1),
  a bounded conditional density for the antithetic call (§5.3), little mass of the inner mean near
  the kink for a piecewise linear `f` (§9.1), `L⁴` strong convergence and a Lipschitz `f″` for the
  nested MIMC rates (§9.2).
* **ML2R's weak-error expansion.** The paper's remainder `O(2^{−αℓL})` is read with one constant
  for all `L` and `ℓ ≤ L`, which the complexity argument needs since `L` grows as `ε → 0`.
* **Base grids.** The union grids for non-nested timesteps (§5.6, §8) are deterministic
  (`BrownianPaths.lean`, `PoissonGrids.lean`) or path-dependent with step sizes that are multiples
  of a fixed base spacing (`AdaptiveGrids.lean`); real-valued adaptive step sizes are not covered.
* **Random constants.** The PDE bound `|P − P_ℓ| < K h_ℓ²` of §7.1 holds with a random `K`,
  `E[K²] < ∞`; for the paper's example no deterministic `K` exists
  (`not_ae_abs_gaussian_sq_mul_le`).

### Build

```
# needs elan (https://github.com/leanprover/elan); the toolchain is pinned in lean-toolchain
lake exe cache get      # Mathlib build cache (a few GB) from cache.mathlib.org
lake build              # a few minutes once the Mathlib cache is in place
```

The pins are Lean `v4.33.1` and Mathlib `0df444a`, the default verification environment of
prove2.me, and the build uses the platform's option `autoImplicit = false`, so every file here
compiles as it does on the platform's servers. Each file imports only the Mathlib modules it
needs, not all of Mathlib.

### Verification

```
lake env lean scripts/AxiomCheck.lean
```

This prints `#print axioms` for every main theorem. Each one must list only `propext`,
`Classical.choice` and `Quot.sound`, the standard axioms, and in particular no `sorryAx`.
GitHub Actions runs the build and this audit on every push (`.github/workflows/lean_action_ci.yml`).
Where GitHub Actions is not available (for example when the free minutes are used up),
`bash scripts/local_ci.sh` runs the same steps locally: the uploader tests, `lake build`, the
generator regression test, this audit, the prove2.me facts, and the generation, build and
validation of the platform tree.

### prove2.me

`scripts/prove2me/` packages the project for [prove2.me](https://prove2.me) following the
platform's full-project playbook: `extract_decl_graph.lean` and `extract_sketch_info.lean`
(declaration graph and per-file facts), `generate.py` (the `Definitions/Theorems/Solutions`
tree by skeleton subtraction, one node per main theorem plus every long or reused lemma),
`validate.py` (every stub has the source statement's type; every solution has exactly its stub's
type and uses no `sorry`), and `upload.py` (idempotent, dependency-ordered, private by default;
publishing is a separate, explicit step). CI regenerates, builds and validates the tree on every
push and tests the uploader against a mock of the API (`test_upload.py`). The metadata
(titles, statements, sources) is in `prove2me/metadata.json`; the mission proposals are in
`prove2me/proposals/` and are created by `propose.py`.

To upload (needs a prove2.me API key, `p2m_…`, of the account that should own the results):

```
# either locally, after `lake build` and the extraction/generation steps of the CI workflow:
export PROVE2ME_API_KEY=p2m_...
python3 scripts/prove2me/upload.py --preflight   # environment, account, name clashes
python3 scripts/prove2me/upload.py               # private upload, resumable; ends with a status table
python3 scripts/prove2me/propose.py              # the mission proposals (drafts, never submitted)
```

or from GitHub, without a local build: add the repository secret `PROVE2ME_API_KEY` and the
repository variable `PROVE2ME_UPLOAD = true`; the `upload` job of the CI workflow then uploads the
tree that the `build` job generated and validated, on every run (reruns submit nothing twice).

Everything is uploaded **private**. `upload.py --make-public --confirm-irreversible` publishes the
whole tree and cannot be undone; the proposals are audited and submitted by the account owner on
the website.

## Experiments (Python)

```
pip install numpy scipy ml_dtypes
python experiments/quantization/ternary_check.py          # ~1 min: ternary vs d-bit inputs, 3 payoffs
python experiments/quantization/neuron_formats_check.py   # ~10 s: FP8/BF16 inputs, BF16/FP16 state, RN vs SR
```

Both use the Haas–Giles GBM test case and report `v_ℓ = V[ΔP − Δ̃P] / V[ΔP]` per level, which
caps the nested-MLMC speedup at `≈ 1/v_ℓ`. Saved outputs are in
`experiments/quantization/results/`, and the interpretation is in `notes/research-notes.md` §2–4.

## Layout

```
MlmcLean.lean                     root module
MlmcLean/Allocation.lean          optimal allocation (Cauchy–Schwarz)
MlmcLean/Estimator.lean           mean / variance / MSE of the MLMC estimator
MlmcLean/Complexity.lean          Giles Theorem 1, deterministic core
MlmcLean/Theorem1.lean            Giles Theorem 1 on a probability space
MlmcLean/StandardEstimator.lean   the estimator (2.2) from independent samples; Theorem 1 for it
MlmcLean/Randomised.lean          randomised single-term MLMC (Giles §2.2)
MlmcLean/MultiIndex.lean          multi-indices, cross-differences (Giles §2.4)
MlmcLean/Lattice.lean             lattice sums over the MIMC index sets
MlmcLean/Theorem2.lean            Giles Theorem 2 (Multi-Index Monte Carlo)
MlmcLean/Nested.lean              Haas–Giles nested MLMC (9)–(12)
MlmcLean/ControlVariate.lean      §1.1–§1.3: plain MC, control variates, the cost (1.1)
MlmcLean/ErrorAnalysis.lean       §2.1, §3.1, §3.3: MSE budget, weak rate, convergence test
MlmcLean/LevelDropping.lean       §2.6: subsets of the levels, exhaustive search, the test (2.5)
MlmcLean/Corrections.lean         §2.1: (2.4) and antithetic estimators
MlmcLean/Richardson.lean          §2.3: Richardson extrapolation and ML2R
MlmcLean/ML2RComplexity.lean      §2.3: the ML2R complexity
MlmcLean/MultiOutput.lean         §2.5: several outputs, Hilbert-space outputs
MlmcLean/GeometricRates.lean      §2.1: allocation under geometric rates, β = 2α
MlmcLean/CostComparison.lean      §1.3, §2.1–§2.2: MC vs MLMC costs, the MSE split
MlmcLean/RectangularMIMC.lean     §2.4: MIMC on a rectangular index set
MlmcLean/Algorithm.lean           §3.1: Algorithm 1
MlmcLean/MLQMC.lean               §3.5: Algorithm 2 (MLQMC)
MlmcLean/Implementation.lean      §3.3–§3.5: the driver's estimates and checks
MlmcLean/EulerMaruyama.lean       [HG25] (2), (4)–(5), §5.1: the Euler–Maruyama coupling
MlmcLean/SDEExtras.lean           §5: the steps that need no SDE theory
MlmcLean/GBMEulerMaruyama.lean    §5.1: geometric Brownian motion end to end
MlmcLean/GBMMilstein.lean         §5.2: the Milstein scheme for geometric Brownian motion end to end
MlmcLean/PDEExamples.lean         §7.1: the PDE examples
MlmcLean/PoissonCoupling.lean     §8: tau-leaping and the Poisson coupling
MlmcLean/TauLeapingMLMC.lean      §8: Theorem 1 for tau-leaping MLMC
MlmcLean/NestedSimulation.lean    §9: nested simulation, antithetic difference, moments
MlmcLean/NestedMLMC.lean          §9.1: the nested MLMC estimator and its rates
MlmcLean/MarkovChain.lean         §10.1: Markov chains started in the past
MlmcLean/MarkovLimit.lean         §10.1: almost sure and weak convergence of the chain
MlmcLean/ApproxNormal.lean        [HG25] §3: approximate normals
MlmcLean/LUTLimits.lean           [HG25] §3.4: the MSE of the lookup tables as d → ∞
MlmcLean/RoundingError.lean       [HG25] §4: fixed-point rounding and the error model
MlmcLean/FixedPointPath.lean      [HG25] §4.1, §6.3: the GBM path and error accumulation
MlmcLean/BitWidth.lean            [HG25] §5–§6: the cost model and bit-width optimisation
MlmcLean/LagrangeBitWidth.lean    [HG25] §4.3, §6: the Lagrange conditions (35), (37)
scripts/AxiomCheck.lean           axiom audit (run in CI)
scripts/local_ci.sh               the steps of the CI workflow, for running them locally
scripts/prove2me/                 prove2.me packaging: extractors, generator, validator, uploader
PLAN.md, CLAUDE.md                milestones; instructions for Claude sessions
notes/statement-audit.md          statement-by-statement comparison with the papers
notes/research-notes.md           research notes (quantization, hardware, strategy)
experiments/quantization/         numerical checks + results/
docs/                             papers: PDF, extracted text, Haas–Giles LaTeX source
```
