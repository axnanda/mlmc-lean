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

Outcome of the comparison with the papers: every statement matches, with one exception, which was
fixed — `singleTerm_unbiased` did not assume `P` integrable, so for a non-integrable `P` it read
`E[P]` as Lean's junk value `0`; the hypothesis `hP : Integrable P μ` was added (the read-back in
`randomised_nested.md` predates the fix). The read-backs also make explicit some deliberate
generalisations recorded in `notes/statement-audit.md` (pairwise instead of mutual independence;
conditions for sample sizes `n ≥ 1`; no sign conditions on costs).
