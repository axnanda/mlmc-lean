# mlmc-lean: multilevel Monte Carlo in Lean 4, plus research notes

A research repo (Sept 2026) with four parts:

| Path | What it is |
|---|---|
| `MlmcLean/` | Machine-checked **Lean 4 + Mathlib proofs** of Giles' MLMC complexity theorem (Theorem 1), randomised MLMC, the Multi-Index Monte Carlo theorem (Theorem 2), the MLMC and MLQMC algorithms, Richardson–Romberg MLMC, and the pure-mathematics content of the application sections of Giles (2015) and of Haas–Giles (2025): 37 modules, 390 audited theorems. Zero `sorry`. |
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
  FPGAs*, arXiv:2502.07123 (2025). §2 (eq. (2)–(12)), §3 (approximate normals, (13)–(19)),
  §4 (rounding errors, (20)–(29)), §5–§6 (the cost model and the bit-width optimisation,
  (30)–(41)).

The convergence orders of the discretisations themselves (Euler–Maruyama, Milstein, finite
differences, QMC) are not formalised: Mathlib has no Itô calculus. The theorems that use them
take the orders as hypotheses, as the papers' complexity theorems do.

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
| `MlmcLean/EulerMaruyama.lean`, `MlmcLean/SDEExtras.lean` | The Euler–Maruyama fine/coarse coupling: the coarse path has the law of the level-`ℓ−1` path, (2.4), Theorem 1 for it (`measurePreserving_pairAvg`, `integral_emCoarse`, `em_mlmc_theorem1`), the variance rate from the strong rate (`variance_levelDiff_of_strong`). The §5 steps that need no SDE theory: rates from the timestep, the complexities of the digital option and of Milstein, conditional expectations and (2.4), the Brownian-bridge midpoint, the antithetic swap and its variance `O(h²)` (`measurePreserving_swapIncrements`, `variance_antithetic_le`), splitting (`splitting_mean_variance`: same mean, variance `V[m] + E[v]/M`), the stability of the explicit step, the smoothed CDF and the density as a limit (`tendsto_smoothCDF`, `tendsto_density`). | [HG25] (2), (4)–(5); [G15] §5 |
| `MlmcLean/PDEExamples.lean` | Pathwise errors give `α` and `β = 2α` (`rates_of_pathwise`, `elliptic_rates`), the discrete maximum principle and stability of the explicit heat scheme for `k/h² ≤ ½`, the cost factor 8 (`parabolic_cost`), Euler–Maruyama = Milstein for additive noise, and the complexity (`pde_complexity`). | [G15] §7.1 |
| `MlmcLean/PoissonCoupling.lean` | Tau-leaping and the Anderson–Higham Poisson coupling: the marginals are the fine and coarse tau-leaping chains, (2.4), the moments of the coupled difference, and the complexity statements (`coupled_increments_hasLaw`, `integral_sq_coupledIncr_sub`, `coupledChain_fst`, `coupledChain_snd`, `tauLeaping_2_4`, `tauLeaping_complexity`). | [G15] §8 |
| `MlmcLean/NestedSimulation.lean`, `MlmcLean/NestedMLMC.lean` | Nested simulation: the antithetic difference (with the constant `−1/8`, correcting the paper's `−1/4`), moment bounds, the exponents of §9.1–§9.2, and the nested MLMC estimator with its expectation, the rates `α = 1`, `β = 2` and the complexity `O(ε⁻²)` (`antithetic_quadratic`, `nested_variance_rate`, `nested_mean_rate`, `nested_complexity`). | [G15] §9 |
| `MlmcLean/MarkovChain.lean` | Markov chains started in the past: the coupled chains contract (`lintegral_dist_backIter_le`, `lintegral_dist_start_le`), the correction variance decays like `ρ^{N_{ℓ−1}}` (`variance_levels_le`), and the example `X_{n+1} = X_n/2 + ξ_n` has the uniform law on `[0, 2]` as invariant law (`map_halfStep`). | [G15] §10.1 |
| `MlmcLean/ApproxNormal.lean` | Approximate normal random variables: the `L²` projection behind (14)–(15), the lookup tables of methods 1–3, (16)–(19), the coupling (17), and that methods 2 and 3 cannot beat method 1 (`intervalMean_isLeast`, `method1_le`, `method1_le_perm`). | [HG25] §3 |
| `MlmcLean/RoundingError.lean`, `MlmcLean/FixedPointPath.lean` | Fixed-point rounding and its error bounds (20)–(22), the error-variance model (25)–(29) with the independent and fully correlated cases (`variance_linearised_indep`, `variance_linearised_corr`, `vIndep_le_vCorr`), the GBM path of Algorithm 1, the sizes (39)–(41) of its variables and the accumulation of rounding errors along the path (`integral_abs_roundFixed_path_sub_le`). | [HG25] §4, §6.3 |
| `MlmcLean/BitWidth.lean`, `MlmcLean/LagrangeBitWidth.lean` | The cost model (30)–(34), the separable optimisation, the Lagrange conditions (35) and (37) (sufficient and necessary), the ratio (38), the trends of §6.3 and the lookup-table size (`levelwise_optimisation`, `exists_unique_bitWidth`, `greedy_rounding_feasible`, `exists_eq35_isMin`, `eq35_of_isLocalMinOn`, `eq37_iff`). | [HG25] §5–§6 |

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
MlmcLean/PDEExamples.lean         §7.1: the PDE examples
MlmcLean/PoissonCoupling.lean     §8: tau-leaping and the Poisson coupling
MlmcLean/NestedSimulation.lean    §9: nested simulation, antithetic difference, moments
MlmcLean/NestedMLMC.lean          §9.1: the nested MLMC estimator and its rates
MlmcLean/MarkovChain.lean         §10.1: Markov chains started in the past
MlmcLean/ApproxNormal.lean        [HG25] §3: approximate normals
MlmcLean/RoundingError.lean       [HG25] §4: fixed-point rounding and the error model
MlmcLean/FixedPointPath.lean      [HG25] §4.1, §6.3: the GBM path and error accumulation
MlmcLean/BitWidth.lean            [HG25] §5–§6: the cost model and bit-width optimisation
MlmcLean/LagrangeBitWidth.lean    [HG25] §4.3, §6: the Lagrange conditions (35), (37)
scripts/AxiomCheck.lean           axiom audit (run in CI)
scripts/prove2me/                 prove2.me packaging: extractors, generator, validator, uploader
PLAN.md, CLAUDE.md                milestones; instructions for Claude sessions
notes/statement-audit.md          statement-by-statement comparison with the papers
notes/research-notes.md           research notes (quantization, hardware, strategy)
experiments/quantization/         numerical checks + results/
docs/                             papers: PDF, extracted text, Haas–Giles LaTeX source
```
