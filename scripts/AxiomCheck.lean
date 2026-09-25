import MlmcLean

/-! Axiom audit: every theorem below must depend only on `propext`, `Classical.choice`,
`Quot.sound` (the standard Lean/Mathlib axioms) — in particular no `sorryAx`. -/

#print axioms MLMC.cost_lower_bound
#print axioms MLMC.optimal_cost_isLeast
#print axioms MLMC.optimalN_variance
#print axioms MLMC.optimalN_cost
#print axioms MLMC.mse_eq_variance_add_sq_bias
#print axioms MLMC.mlmc_mean
#print axioms MLMC.mlmc_variance
#print axioms MLMC.mlmc_mse
#print axioms MLMC.mlmc_complexity_core
#print axioms MLMC.variance_sample_mean
#print axioms MLMC.giles_theorem1
#print axioms MLMC.giles_theorem1_cost_sum
#print axioms MLMC.giles_theorem1_isBigO
#print axioms MLMC.integral_levelEstimator
#print axioms MLMC.variance_levelEstimator
#print axioms MLMC.indepFun_levelEstimator
#print axioms MLMC.giles_theorem1_standard
#print axioms MLMC.exists_iid_inputs
#print axioms MLMC.giles_theorem1_iid
#print axioms MLMC.integral_comp_level
#print axioms MLMC.singleTerm_unbiased
#print axioms MLMC.singleTerm_variance
#print axioms MLMC.singleTerm_variance_ge
#print axioms MLMC.summable_of_memLp_singleTerm
#print axioms MLMC.randomised_summable
#print axioms MLMC.randomised_not_summable
#print axioms MLMC.randomised_optimal_p
#print axioms MLMC.randomised_optimal_p_eq
#print axioms MLMC.randomised_mlmc_finite
#print axioms MLMC.nested_cost_lower_bound
#print axioms MLMC.nested_optimal_allocation
#print axioms MLMC.nested_mlmc_mse
