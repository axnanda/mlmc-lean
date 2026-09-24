# mlmc-lean: multilevel Monte Carlo in Lean 4, plus research notes

A research repo (Sept 2026) with four parts:

| Path | What it is |
|---|---|
| `MlmcLean/` | Machine-checked **Lean 4 + Mathlib proofs** of Giles' MLMC complexity theorem and the Haas–Giles nested-MLMC cost formula. Zero `sorry`. |
| `PLAN.md` | Next formalisation milestones (randomised MLMC, MIMC, level-dependent precision) and ground rules. **Start here for new work.** |
| `notes/research-notes.md` | Evaluation of ternary/low-precision inputs for the Haas–Giles framework, the weak-vs-strong ("path") argument, AWS F2/Trainium notes, strategy and open directions. |
| `experiments/quantization/` | The two numerical checks behind the notes (Python), with saved outputs in `results/`. |
| `docs/` | The two papers: PDFs, extracted text and the Haas–Giles arXiv LaTeX source. |

## Lean formalisation

Machine-checked proofs (Lean 4 + Mathlib) of the complexity results for MLMC from:

* **[G15]** M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015) 259–328.
  Theorem 1 and eq. (1.1)–(1.2), (2.1)–(2.3).
* **[HG25]** I.-B. Haas, M.B. Giles, *A nested MLMC framework for efficient simulations on
  FPGAs*, arXiv:2502.07123 (2025). §2.1–2.2, eq. (6)–(12).

### What is proved

| File | Content | Paper |
|---|---|---|
| `MlmcLean/Allocation.lean` | Optimal sample allocation. `cost_lower_bound`: for **any** allocation with total variance `≤ τ`, cost `≥ τ⁻¹ (Σ √(V_i C_i))²`, by Cauchy–Schwarz, so the Lagrange-multiplier value is a true minimum. `optimalN_variance` / `optimalN_cost`: the rounded-up optimal `N_i = ⌈τ⁻¹ √(V_i/C_i) Σ√(V_jC_j)⌉` meets the variance target with cost `≤ τ⁻¹ (Σ √(V_iC_i))² + Σ C_i`. | [G15] (1.1)–(1.2); [HG25] (8) |
| `MlmcLean/Estimator.lean` | `mse_eq_variance_add_sq_bias`: `E[(Y−m)²] = Var Y + (E Y − m)²`. `mlmc_mean`: `E[Σ Y_ℓ] = E[P_L]` (telescoping, condition (ii)). `mlmc_variance`: `Var[Σ Y_ℓ] = Σ Var[Y_ℓ]` for pairwise independent `Y_ℓ` (Mathlib `IndepFun.variance_sum`). `mlmc_mse`: their combination. | [G15] (2.1)–(2.3) |
| `MlmcLean/Complexity.lean` | `mlmc_complexity_core`: Giles' Theorem 1 with the probabilistic content stripped out. With `V_ℓ = c₂2^{−βℓ}` and `C_ℓ = c₃2^{γℓ}`, for every `0<ε<e⁻¹` there are `L` and integers `N_ℓ ≥ 1` with `(c₁2^{−αL})² + Σ V_ℓ/N_ℓ < ε²` and `Σ N_ℓ C_ℓ ≤ c₄·bound(ε)`, in all three regimes `β>γ`, `β=γ`, `β<γ`. Follows Giles' proof: `L = ⌈log₂(2c₁/ε)/α⌉`, `N_ℓ` from (1.2) rounded up, geometric-sum estimates, and `α ≥ ½min(β,γ)` to absorb the `Σ C_ℓ = O(ε^{−γ/α})` rounding term. | [G15] Thm 1 |
| `MlmcLean/Theorem1.lean` | `giles_theorem1`: **Theorem 1 as stated in the paper**, on an arbitrary probability space, with hypotheses (i)–(iv) verbatim and the conclusion `MSE < ε²` plus the cost bound. `variance_sample_mean`: `Var[N⁻¹ Σ X_n] = v/N` for pairwise-independent samples (how `V[Y_ℓ] = V_ℓ/N_ℓ` arises). | [G15] Thm 1 |
| `MlmcLean/Nested.lean` | Haas–Giles nested estimator. `nested_cost_lower_bound` and `nested_optimal_allocation`: eq. (12) as a two-sided statement (a lower bound for all allocations, and an integer allocation attaining it up to the rounding overhead `Σ(C̃_ℓ + C^Δ_ℓ)`). `nested_mlmc_mse`: (9)–(11), with mean `E[P_L]`, variance `Σ(Var Ỹ_ℓ + Var Y^Δ_ℓ)` and the MSE. | [HG25] (9)–(12) |

No `sorry` and no extra axioms (see Verification below).

### Modelling choices

* **Estimators are the primitive.** Following Giles' own statement ("independent estimators
  `Y_ℓ` based on `N_ℓ` Monte Carlo samples, each with expected cost `C_ℓ` and variance `V_ℓ`"),
  `giles_theorem1` takes `Y ℓ N : Ω → ℝ` for every level `ℓ` and sample size `N`, with
  `Var[Y ℓ N] = V ℓ / N` (Giles (2.3)) and pairwise independence across levels for every choice
  of `N`. `variance_sample_mean` shows this is what a Monte Carlo average of independent
  samples gives.
* **Cost is deterministic per sample.** Giles allows the per-sample cost to be random with
  expectation `C_ℓ`. Since only `E[C] = Σ N_ℓ C_ℓ` enters, we take `C_ℓ` itself (generalising
  this is PLAN.md M1).
* **Strict `MSE < ε²`.** This comes from bias `≤ ε/2` and variance `≤ ε²/2`. Giles uses `ε/√2`
  and `ε²/2`; the constant `c₄` absorbs the difference.
* **`c₄` is explicit** in each regime (see the `refine ⟨…, by positivity, ?_⟩` lines in
  `mlmc_complexity_core`).
* **Haas–Giles (12)** is an optimal-allocation formula, not a rate theorem. The paper derives it
  with Lagrange multipliers, "ignoring the small increase in the cost when `N_ℓ` are rounded up".
  We prove it as a lower bound for every allocation that is achievable up to exactly that
  rounding term.

### Build

```
# needs elan (https://github.com/leanprover/elan); the toolchain is pinned in lean-toolchain
lake exe cache get      # Mathlib build cache (a few GB) from cache.mathlib.org
lake build              # ~20–30 s per file once the Mathlib cache is warm
```

Each file imports only the Mathlib modules it needs (variance/independence, `logb`/`rpow`,
geometric sums, floor, Cauchy–Schwarz), not all of Mathlib, so builds stay fast.

### Verification

```
lake env lean scripts/AxiomCheck.lean
```

This prints `#print axioms` for every main theorem. Each one must list only `propext`,
`Classical.choice` and `Quot.sound`, the standard axioms, and in particular no `sorryAx`.
GitHub Actions runs the build and this audit on every push (`.github/workflows/lean_action_ci.yml`).

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
MlmcLean/Nested.lean              Haas–Giles nested MLMC (9)–(12)
scripts/AxiomCheck.lean           axiom audit (run in CI)
PLAN.md, CLAUDE.md                next milestones; instructions for Claude sessions
notes/research-notes.md           research notes (quantization, hardware, strategy)
experiments/quantization/         numerical checks + results/
docs/                             papers: PDF, extracted text, Haas–Giles LaTeX source
```
