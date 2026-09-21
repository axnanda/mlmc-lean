# mlmc-lean — Multilevel Monte Carlo complexity theorems in Lean 4

Machine-checked proofs (Lean 4 + Mathlib) of the complexity results for multilevel Monte Carlo
(MLMC) from

* **[G15]** M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015) 259–328 —
  Theorem 1 and eq. (1.1)–(1.2), (2.1)–(2.3).
* **[HG25]** I.-B. Haas, M.B. Giles, *A nested MLMC framework for efficient simulations on
  FPGAs*, arXiv:2502.07123 (2025) — §2.1–2.2, eq. (6)–(12).

Both papers are in `docs/` (PDF + extracted text).

## What is proved

| File | Content | Paper |
|---|---|---|
| `MlmcLean/Allocation.lean` | Optimal sample allocation. `cost_lower_bound`: for **any** allocation with total variance `≤ τ`, cost `≥ τ⁻¹ (Σ √(V_i C_i))²` (Cauchy–Schwarz — the Lagrange-multiplier value is a true minimum). `optimalN_variance` / `optimalN_cost`: the rounded-up optimal `N_i = ⌈τ⁻¹ √(V_i/C_i) Σ√(V_jC_j)⌉` meets the variance target with cost `≤ τ⁻¹ (Σ √(V_iC_i))² + Σ C_i`. | [G15] (1.1)–(1.2); [HG25] (8) |
| `MlmcLean/Estimator.lean` | `mse_eq_variance_add_sq_bias`: `E[(Y−m)²] = Var Y + (E Y − m)²`. `mlmc_mean`: `E[Σ Y_ℓ] = E[P_L]` (telescoping, condition (ii)). `mlmc_variance`: `Var[Σ Y_ℓ] = Σ Var[Y_ℓ]` for pairwise independent `Y_ℓ` (Mathlib `IndepFun.variance_sum`). `mlmc_mse`: their combination. | [G15] (2.1)–(2.3) |
| `MlmcLean/Complexity.lean` | `mlmc_complexity_core`: Giles' Theorem 1 with the probabilistic content stripped out — with `V_ℓ = c₂2^{−βℓ}`, `C_ℓ = c₃2^{γℓ}`, for every `0<ε<e⁻¹` there are `L` and integers `N_ℓ ≥ 1` with `(c₁2^{−αL})² + Σ V_ℓ/N_ℓ < ε²` and `Σ N_ℓ C_ℓ ≤ c₄·bound(ε)` in all three regimes `β>γ`, `β=γ`, `β<γ`. Follows Giles' proof: `L = ⌈log₂(2c₁/ε)/α⌉`, `N_ℓ` from (1.2) rounded up, geometric-sum estimates, and `α ≥ ½min(β,γ)` to absorb the `Σ C_ℓ = O(ε^{−γ/α})` rounding term. | [G15] Thm 1 |
| `MlmcLean/Theorem1.lean` | `giles_theorem1`: **Theorem 1 as stated in the paper**, on an arbitrary probability space, with hypotheses (i)–(iv) verbatim and conclusion `MSE < ε²` and cost bound. `variance_sample_mean`: `Var[N⁻¹ Σ X_n] = v/N` for pairwise-independent samples (how `V[Y_ℓ] = V_ℓ/N_ℓ` arises). | [G15] Thm 1 |
| `MlmcLean/Nested.lean` | Haas–Giles nested estimator. `nested_cost_lower_bound` and `nested_optimal_allocation`: eq. (12) as a two-sided statement (lower bound for all allocations; integer allocation attaining it up to the rounding overhead `Σ(C̃_ℓ + C^Δ_ℓ)`). `nested_mlmc_mse`: (9)–(11), mean `E[P_L]`, variance `Σ(Var Ỹ_ℓ + Var Y^Δ_ℓ)`, MSE. | [HG25] (9)–(12) |

No `sorry`, no extra axioms (see `lake build` and `#print axioms` below).

## Modelling choices (read this before uploading anywhere)

* **Estimators are the primitive.** Following Giles' own statement ("independent estimators
  `Y_ℓ` based on `N_ℓ` Monte Carlo samples, each with expected cost `C_ℓ` and variance `V_ℓ`"),
  `giles_theorem1` takes `Y ℓ N : Ω → ℝ` for every level `ℓ` and sample size `N`, with
  `Var[Y ℓ N] = V ℓ / N` (Giles (2.3)) and pairwise independence across levels for every choice
  of `N`.  `variance_sample_mean` shows this is what a Monte Carlo average of independent
  samples gives.
* **Cost is deterministic per sample.** Giles allows the per-sample cost to be random with
  expectation `C_ℓ`; since only `E[C] = Σ N_ℓ C_ℓ` enters, we take `C_ℓ` itself.
* **Strict `MSE < ε²`.** Obtained with bias `≤ ε/2` and variance `≤ ε²/2` (Giles uses
  `ε/√2` and `ε²/2`; the constant `c₄` absorbs the difference).
* **`c₄` is explicit** in each regime (see the `refine ⟨…, by positivity, ?_⟩` lines in
  `mlmc_complexity_core`).
* **Haas–Giles (12)** is an optimal-allocation formula, not a rate theorem; the paper derives it by
  Lagrange multipliers "ignoring the small increase in the cost when `N_ℓ` are rounded up".
  We prove it as: lower bound for every allocation + achievable up to exactly that rounding term.

## Build

```
# needs elan (https://github.com/leanprover/elan); toolchain pinned in lean-toolchain
lake exe cache get      # Mathlib oleans (a few GB)
lake build              # builds everything; ~20–30 s per file once the Mathlib cache is warm
```

Each file imports only the Mathlib modules it needs (variance/independence, `logb`/`rpow`,
geometric sums, floor, Cauchy–Schwarz), not all of Mathlib, so builds stay fast.

## Verification

```
lake env lean scripts/AxiomCheck.lean
```

prints `#print axioms` for every theorem in the project.  Each must list only
`propext`, `Classical.choice`, `Quot.sound` — the standard axioms — and in particular no
`sorryAx`.  `grep -rn sorry MlmcLean/` must be empty.

## Layout

```
MlmcLean.lean            root module
MlmcLean/Allocation.lean
MlmcLean/Estimator.lean
MlmcLean/Complexity.lean
MlmcLean/Theorem1.lean
MlmcLean/Nested.lean
docs/                    the two papers (pdf + txt)
```
