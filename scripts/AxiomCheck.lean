import MlmcLean

/-! Axiom audit: every theorem below must depend only on `propext`, `Classical.choice`,
`Quot.sound` (the standard Lean/Mathlib axioms) — in particular no `sorryAx`. -/

#print axioms MLMC.cost_lower_bound
#print axioms MLMC.optimalN_variance
#print axioms MLMC.optimalN_cost
#print axioms MLMC.mse_eq_variance_add_sq_bias
#print axioms MLMC.mlmc_mean
#print axioms MLMC.mlmc_variance
#print axioms MLMC.mlmc_mse
#print axioms MLMC.mlmc_complexity_core
#print axioms MLMC.variance_sample_mean
#print axioms MLMC.giles_theorem1
#print axioms MLMC.nested_cost_lower_bound
#print axioms MLMC.nested_optimal_allocation
#print axioms MLMC.nested_mlmc_mse
