# Blind read-backs of the headline statements

Written 2026-09-25 by independent auditor agents that saw only the Lean statements (docstrings and
comments stripped, proofs replaced by `sorry`), the definitions they use, and the prove2.me
auditor rules (`mission_auditor.md`) — never the papers, the docstrings or the intent. They
render what each statement literally asserts, so they can be compared line by line with the papers
in `docs/` and with `notes/statement-audit.md`.

| File | Statements |
|---|---|
| `theorem1.md` | `giles_theorem1`, `giles_theorem1_standard`, `exists_iid_inputs`, `giles_theorem1_iid`, `optimal_cost_isLeast` |
| `theorem2.md` | `sum_crossDiff`, `giles_theorem2`, `giles_theorem2_boundary` |
| `randomised_nested.md` | `singleTerm_unbiased`, `singleTerm_variance`, `randomised_summable`, `randomised_not_summable`, `randomised_mlmc_finite`, `nested_cost_lower_bound`, `nested_optimal_allocation`, `nested_mlmc_mse` |
| `theorem2_boundary_d3.md` (2026-09-26) | `mimc_extra_term`, `mimc_complexity_core`, `mimc_complexity_boundary`, `giles_theorem2_boundary` (the sharpened boundary exponents) |
| `allocation_theorem2_full.md` (2026-09-26) | `sumSqrtVC`, `lagrangeN`, `lagrangeN_variance_cost`, `lagrangeN_unique`, `optimal_cost_isLeast`, `optimal_variance_isLeast`, `twoLevel_optimal_ratio`; `dot`, `crossDiff`, `mimcEta`, `mimcD2`, `mimcD3`, `mimcBound`, `tendsto_sum_box_integral_crossDiff`, `hasSum_integral_crossDiff`, `giles_theorem2_full` |
| `estimators_randomised.md` (2026-09-26) | `levelDiff`, `sum_integral_levelDiff`, `blockMean`, `integral_blockMean`, `variance_blockMean`, `indepFun_blockMean`, the estimator (2.2) and `mlmcEstimator_mean_variance`, `integral_cost_level`, `randomised_necessary`, `singleTermN_mean_variance`, `randomised_optimal_p_isLeast`, `randomised_mlmc_finite` |
| `nested_estimator.md` (2026-09-26) | `nIdx`, `pairFam`, `nestedTerm`, `nestedEstimator`, `nestedCost`, `nested_cost_isLeast`, `nested_saving`, `nestedEstimator_mean_variance`, `nestedCost_mean`, `nested_mlmc_mse` |
| `controlvariate_leveldropping.md` (round 3) | `blockMean`, `mc_estimate`, `correlation`, `controlVariate_mean`, `controlVariate_variance`, `controlVariate_optimal`, `controlVariate_estimator`, `optimal_cost_const_product`, `optimal_cost_increasing`, `optimal_cost_decreasing`, `levelKeep_product`, `levelDrop_test`, `levelDrop_variance`, `levelDrop_perfect_correlation`, `levelDrop_uncorrelated` |
| `erroranalysis.md` (round 3) | `mse_lt_of_half`, `weak_rate_of_second_moment`, `allocation_eq_3_1`, `remaining_error`, `convergence_test_mse`, `consistency_mean`, `covariance_sq_le`, `sqrt_variance_add_le`, `sqrt_variance_sub_le`, `consistency_sd`, `kurtosis`, `sampleVariance_sd`, `kurtosis_of_ternary`, `tendsto_kurtosis_atTop` |
| `corrections_richardson.md` (round 3) | `levelDiff`, `blockMean`, `totalCost`, `complexityBound`, `fineCoarseDiff`, `antitheticDiff`, `integral_fineCoarseDiff`, `integral_antitheticDiff`, `giles_theorem1_corrections`, `giles_theorem1_fineCoarse`, `giles_theorem1_antithetic`, `ml2rNode`, `ml2rWeight`, `richardson_extrapolation`, `ml2r_weights`, `ml2r_moment_succ`, `ml2r_bias_eq`, `ml2r_bias`, `ml2r_rearrange`, `ml2r_estimator_mean_variance` |
| `multioutput.md` (round 3) | `sumSqrtVC`, `lagrangeN`, `complexityBound`, `multiOutput_variance`, `multiOutput_optimal`, `integral_norm_add_sq_of_indepFun`, `integral_add_sq_of_indepFun`, `integral_norm_sum_sq_of_indepFun`, `integral_norm_sub_sq_eq`, `mlmc_mse_hilbert`, `giles_theorem1_hilbert`, `sq_norm_add_of_indepFun_fails_sup` |

Outcome of the comparison with the papers: every statement matches, with one exception, which was
fixed — `singleTerm_unbiased` did not assume `P` integrable, so for a non-integrable `P` it read
`E[P]` as Lean's junk value `0`; the hypothesis `hP : Integrable P μ` was added (the read-back in
`randomised_nested.md` predates the fix). The read-backs also make explicit some deliberate
generalisations recorded in `notes/statement-audit.md` (pairwise instead of mutual independence;
conditions for sample sizes `n ≥ 1`; no sign conditions on costs).

**Second round (2026-09-26).** The three read-backs dated 2026-09-26 cover the statements added or
changed in the review of M5. None of them found a vacuous or trivially true statement; every
hypothesis set was shown satisfiable. Findings and what was done:

- `giles_theorem2_full`: the exponents `e₁, e₂` were pinned only when every `α_d > ½β_d`, so in the
  boundary case the read-back saw free existentials (as in the paper, which leaves them open).
  The statement now also says `e₁ = 2D₂ + (D₃ − 3)⁺` and `e₂ = (D₂ − 1)(2 + η) + (D₃ − 1)⁺`
  (the read-back predates this change).
- `twoLevel_optimal_ratio`: the hypothesis `B > 0` was redundant (it follows from
  `n₀C₀ + n₁C₁ = B`) and was removed.
- `randomised_optimal_p_isLeast`: the docstring said the minimum is attained by
  `optimalLevelProb`, the statement only that it is attained; the statement now includes
  `p*_ℓ > 0`, `∑ p*_ℓ = 1` and the value of the product at `p*`.
- Kept as they are, since they follow the papers or are harmless: real (not integer) sample sizes
  in the allocation problems (the papers' relaxation); `c₄` chosen after the instance data (the
  paper's order of quantifiers); hypotheses imposed for all levels rather than only `ℓ ≤ L`;
  `nested_saving` compares closed-form costs (the paper's claim is an approximation, and the
  formal version is an inequality); `integral_cost_level` holds for any measure;
  `randomised_mlmc_finite` is qualitative, as is the paper's claim.

**Third round (2026-09-26/27).** Four read-backs cover the modules added for Giles §1.2–1.3,
§2.1 (corrections), §2.3, §2.5, §2.6 and §3 (`ControlVariate`, `LevelDropping`, `ErrorAnalysis`,
`Corrections`, `Richardson`, `MultiOutput`), in four packets read by two auditors (packets 10–11
and 12–13); `levelDiff` is defined in packet 12 and was missing from packet 11.  No statement was
found vacuous, and no conclusion holds only because of a junk value under the stated hypotheses.
Findings and what was done:

- `weak_rate_of_second_moment`, `remaining_error`, `convergence_test_mse`: the packet with these
  statements did not define `levelDiff`, and they are true only for a backward difference.  It is
  one: `levelDiff Pl 0 = Pl 0`, `levelDiff Pl (ℓ + 1) = Pl (ℓ + 1) − Pl ℓ` (`LevelDiff.lean`, and
  the read-back of `levelDiff` in `corrections_richardson.md`).
- `giles_theorem1_corrections`, `giles_theorem1_fineCoarse`, `giles_theorem1_antithetic`,
  `giles_theorem1_hilbert`: the constant `c₄` is chosen after the data, as in the paper's
  statement of Theorem 1, so these statements do not say that it depends only on
  `α, β, γ, c₁, c₂, c₃`.  The paper's proof gives that, and it is now a theorem:
  `giles_theorem1_uniform` chooses one `c₄` before the probability space and the data (its
  probabilistic step is `giles_theorem1_of_core`, which keeps the constant of
  `mlmc_complexity_core`).
- `multiOutput_optimal`: the docstring said that the Lagrange allocation attains the least cost;
  the statement now says so (positivity and the exact cost), not only that it meets the
  individual constraints.
- `integral_norm_add_sq_of_indepFun`, `integral_add_sq_of_indepFun`: the hypothesis `E[b] = 0`
  was unused (`E[a] = 0` alone kills the cross term) and was removed, which strengthens both.
  `tendsto_kurtosis_atTop` now holds for any measure (the probability instance was unused).
- Kept as they are, with the reason:
  - `remaining_error`, `convergence_test_mse` assume `E[P_ℓ − P_{ℓ−1}] = a·2^{−αℓ}` exactly for
    `ℓ ≥ L`: the paper's hypothesis is "`E[P_ℓ − P_{ℓ−1}] ∝ 2^{−αℓ}`" (§3.1, p. 21).
  - `kurtosis` is `E[X⁴]/(E[X²])²` with raw moments: this is the paper's definition, for `X` with
    zero mean (§3.3, p. 23).
  - `sampleVariance_sd` is about `N⁻¹ ∑ X_n²`, the sample variance of a zero-mean `X` when the
    mean is known, whose standard deviation is exactly `√((κ − 1)/N) E[X²]`; the paper's
    "approximately" also covers the usual estimator with the sample mean subtracted.
  - `levelKeep_product` and the allocation theorems use real sample sizes (the papers'
    relaxation).
  - `consistency_mean` takes `E[P^f_ℓ] = E[P^c_ℓ]` as a hypothesis: that identity is the
    assumption (2.4) behind the consistency check, not a consequence of it.
  - `ml2r_bias_eq` is the identity for an arbitrary remainder `R_ℓ`; `ml2r_bias` is the statement
    with content (the exact bias for an expansion of order `L + 1`).
  - Redundant hypotheses that mirror the paper's assumptions or keep a statement from relying on
    Lean's conventions for `x / 0` or non-integrable functions (for example `hf` in
    `controlVariate_mean`, `hVX, hVY` in the level-dropping theorems, `hp` in
    `kurtosis_of_ternary`, `hα` in `richardson_extrapolation`).  `hΔm` in
    `giles_theorem1_corrections` and `hPlm` in `ml2r_estimator_mean_variance` (measurability of
    the corrections) are used by the proofs: independence is preserved by composition with
    measurable maps, and square-integrability alone gives only a.e.-strong measurability.

**Fourth round (2026-09-27).** Two read-backs, in the same blind setting:
`rounding_error.md` (Haas–Giles §4: `roundFixed`, `abs_sub_roundFixed_le`, `roundFixed_mantissa`,
`integral_sq_roundError_le`, `integral_sq_of_isUniform`, `integral_sq_uniform_roundError`,
`vIndep`, `vCorr`, `variance_sum_eq`, `variance_le_integral_sq`, `variance_sum_mul_le_of_indep`,
`variance_linearised_indep`, `variance_sum_le_sq_sum_sqrt`, `sqrt_variance_mul_le`,
`variance_linearised_corr`, `vIndep_le_vCorr`, `variance_extended_indep`,
`variance_extended_corr`) and `theorem1_uniform_multioutput.md` (the statements changed in the
third round: `giles_theorem1_of_core`, `giles_theorem1_uniform`, `multiOutput_optimal`,
`integral_norm_add_sq_of_indepFun`, `integral_add_sq_of_indepFun`, `tendsto_kurtosis_atTop`).
No statement is false or vacuous, and none holds only because of a junk value.  Points recorded,
all consistent with the papers or deliberate:

- `roundFixed` rounds on the fixed grid `2^{e−d}ℤ` with ties toward `+∞` (Haas–Giles fix the
  exponent `e_i` of each variable in advance, §4.1); the mantissa bound needs the separate range
  hypothesis of `roundFixed_mantissa`.
- `variance_linearised_indep` and `variance_extended_indep` take the rounding errors to be
  uniform and independent of the sensitivities, the model assumption of Haas–Giles (22) and
  (26); a measurable function of `x̄_i` cannot satisfy it, and the worst-case (`corr`) theorems
  cover actual rounding errors.  Their `≤` is an equality under these hypotheses.
- `sqrt_variance_mul_le` (`hB`) and `vIndep_le_vCorr` (`hM`) have a redundant hypothesis; kept,
  as they mirror the paper's setting.
- `multiOutput_optimal` optimises the aggregated variance of Giles §2.5,
  `V_ℓ ≡ max_m V_{ℓ,m}/ε_m²` (Nagapetyan's "simple approach"), with real sample sizes; for each
  output separately the allocation is feasible but need not be optimal.

**Fifth round (2026-09-27).** Five blind read-backs of 341 declarations, covering every module
added since the fourth round and the new §2, §3.5 and §5 statements:
`fixedpoint_bitwidth.md` (Haas–Giles §4.1, §5–§6: `FixedPointPath`, `BitWidth`,
`LagrangeBitWidth`), `approxnormal_em_sde.md` (Haas–Giles §3 and (2), (4)–(5); Giles §5:
`ApproxNormal`, `EulerMaruyama`, `SDEExtras`, including splitting and the density as a limit),
`giles_sections1_2.md` (Giles §1–§2: cost comparisons, geometric rates, the rectangular MIMC set,
ML2R complexity, the Figure 2.1 cross-difference, the randomised optimal cost, the level subsets
of §2.6), `giles_section3_algorithms.md` (Giles §3: Algorithm 1, the implementation facts,
Algorithm 2) and `giles_applications.md` (Giles §7–§10: `PDEExamples`, `PoissonCoupling`,
`NestedSimulation`, `NestedMLMC`, `MarkovChain`).  No statement is false or vacuous, and none
holds only because of a junk value.  Changed in response:

- `mlqmc_mse`: the hypothesis that the corrections `m_ℓ` tend to `0` is derived from
  `E[P_ℓ] → E[P]` instead of assumed, and the variance hypothesis is `V[Y] ≤ ∑ V_ℓ` (it was an
  equality).
- `greedy_rounding_feasible` held with `k = n` for every order; it now states the stopping rule
  of the heuristic of Haas–Giles §6.2: the least feasible number `k` of added bits exists, is at
  most `n`, and every smaller number is infeasible.
- `integral_abs_perturbed_sub_le` did not require the perturbations to be measurable, so for a
  non-measurable perturbation the bound held through the convention `∫ f = 0` for non-integrable
  `f`.  It now assumes measurable perturbations and concludes that the error is integrable;
  `integral_abs_roundFixed_path_sub_le` concludes the same, rounding being measurable
  (`measurable_roundFixed`).

Points recorded, all consistent with the papers or deliberate:

- `em_complexity`, `digital_em_complexity`, `milstein_complexity`, `pde_complexity`,
  `tauLeaping_complexity`, `nested_complexity` and `nested_mimc_complexity` only evaluate the
  regime of `complexityBound` / `mimcBound` at the exponents the paper derives; the statements
  about the estimators are the instances of Theorems 1 and 2 (`em_mlmc_theorem1`,
  `nested_mlmc_complexity`, `giles_theorem2_boundary`, …).
- `exists_optimal_subset` is the exhaustive search of §2.6: a finite nonempty family of subsets
  has a minimiser of the cost; `subset_optimal_cost` relaxes the sample numbers to reals, as (1.1).
- `mimc_rect_lower_bounds` and `mimc_rect_necessary` rest on a lower bound of the bias in each
  direction, the assumption under which the converse of Giles §2.4 is stated.
- Several identities hold in the non-integrable case with both sides `0` (`integral_emCoarse`,
  `integral_condExp_eq_of_map_eq`, `lutValue_mirror`); their meaning in the integrable case is
  unaffected.
- Redundant hypotheses, kept because they mirror the papers' setting: `a < b` in
  `integral_sq_sub_eq`, `M > 0` in `fiber_bias_le` and `integrable_innerMean_pow_four`, `c₃ > 0` in
  `nested_mlmc_complexity`, `v ≠ 0` in `consistency_check_gaussian`, `h ≤ 1` in
  `integral_sq_gbmPath_le`, `V, C > 0` in `hasDerivAt_levelCost`.

**Sixth round (2026-09-28).** `poisson_variance.md` is a blind read-back of the statements added
for the correction variance of the Poisson coupling (Giles §8): `lintegral_sq_coupledIncr_le`,
`lintegral_sq_coupledTwoStep_le`, `lintegral_sq_coupledChain_le`, `coupledChain_sq_le`,
`variance_coupledChain_le`, `tauLeaping_level_variance`, with the definitions `couplePair`,
`coupledIncr`, `tauStep`, `tauChain`, `coupledTwoStep`, `coupledChain`.  No statement is false or
vacuous, and none holds only because of a junk value (`coupledChain_sq_le` asserts integrability,
so its Bochner integral is genuine); the auditor checked the bounds numerically on about 53,000
cases and found the one-step bound sharp.  Points recorded, all consistent with the paper or
deliberate:

- The packet showed the first line of the equation-compiler proof of
  `lintegral_sq_coupledChain_le` (a quirk of the packet generator, which cuts proofs at `:=`); the
  statement is unaffected, and the proof in `PoissonCoupling.lean` is complete (CI, axiom audit).
- The packet does not state the marginals of `coupledChain`; they are `coupledChain_fst` (the fine
  chain with step `h` after `2k` steps) and `coupledChain_snd` (the coarse chain with step `2h`
  after `k` steps), read back in `giles_applications.md`.
- The coarse coordinate keeps the rate of the start of its step for both fine sub-steps: this is
  the Anderson–Higham coupling of §8 (the coarse path takes one step of size `2h`).
- The propensity is assumed bounded and Lipschitz, and the constant `c` is chosen after the
  propensity and the payoff: `V_ℓ = O(h_ℓ)` for a given model, as in the paper.
- `tauLeaping_level_variance` covers the levels with `h_ℓ ≤ 1`, all but finitely many; the claim
  of the paper is asymptotic.

**Seventh round (2026-09-28).** Three blind read-backs of the modules added in the same round:
`lut_limits.md` (Haas–Giles §3.4: `tendsto_method1MSE`, `dyadic_mse_ge`, `method3_mse_ge`,
`method3_mse_not_tendsto_zero`, with `gridPt`, `lutValue`, `method1MSE`), `markov_limit.md`
(Giles §10.1: `map_backIter_eq_map_fwdIter`, `ae_tendsto_backIter`,
`tendstoInDistribution_fwdIter`, with `fwdIter`, `revFun`, `revPerm`, `backIter`) and
`tau_leaping_mlmc.md` (Giles §8: `lintegral_sq_tauChain_lt_top`, `integral_tauFine`,
`integral_tauCoarse`, `variance_tauCorrection_le`, `tauLeaping_mlmc_theorem1`, with the level laws
and the input law).  All twelve theorems read back as true, none is vacuous, and none holds only
because of a junk value; the auditors confirmed them numerically (exact rational arithmetic, closed
forms for `Φ⁻¹`, exact truncated Poisson laws, Monte Carlo).  Points recorded, all consistent with
the papers or deliberate:

- Packet G was cut before the fix that indexes the dyadic cells of `dyadic_mse_ge` by `ℕ`
  (`Ico (2 ^ (d - k - 1) : ℕ) (2 ^ (d - k))`); the auditor read the index set as natural numbers,
  which is what the statement now says explicitly.
- `tendsto_method1MSE` is qualitative (no rate); the auditor shows that no uniform rate exists for
  monotone square-integrable `f` (a rate of order `1/d` is possible), which is why the paper's
  "halves per bit" heuristic is not formalised.  `hf2` is essential; `hmono` is not needed for the
  limit (it is the setting of the paper).
- In the three dyadic theorems the concavity hypothesis `hconc` is imposed on one block
  `[2^{−(k+1)}, 2^{−k}]` only; for `Φ⁻¹` it holds with `k ≥ 2`, and the explicit constant is of order
  `μ² 2^{−5k}`.  Either `hf` or `hf2` alone would suffice.
- `map_backIter_eq_map_fwdIter` equates the laws at each fixed `n` (not the joint laws), as in
  §10.1; `tendstoInDistribution_fwdIter` gives the weak convergence of `X_n` to a limit `X∞` stated
  in §10.1.  Stationarity of the limit law is not stated for the general chain (the paper states the
  invariant law only for its example, `halfStep_invariant` in `MarkovChain.lean`); the scope is a
  complete separable metric space with its Borel σ-algebra.
- `tauInputLaw` is an infinite product and would be the zero measure if a factor failed to be a
  probability measure; `isProbabilityMeasure_tauLevelLaw` and `isProbabilityMeasure_tauInputLaw`
  (not in the packet) prove that every factor is one.  On `ℕ` a bounded propensity is automatically
  Lipschitz, so `hK` is implied by `hΛ` (with `K = Λ`); it is kept because it is the paper's
  condition.  The weak rate `α` of tau-leaping is a hypothesis (it compares with the exact chain,
  which needs a continuous-time Markov chain).
- After the read-back, the lemma `revFun_involutive` cited by the packet was inlined into
  `revPerm` (the prove2.me generator does not allow a definition to cite a theorem); the
  definition is unchanged.
