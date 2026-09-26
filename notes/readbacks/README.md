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

