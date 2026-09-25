# mlmc-lean: multilevel Monte Carlo in Lean 4, plus research notes

A research repo (Sept 2026) with four parts:

| Path | What it is |
|---|---|
| `MlmcLean/` | Machine-checked **Lean 4 + Mathlib proofs** of Giles' MLMC complexity theorem (Theorem 1), randomised MLMC, the Multi-Index Monte Carlo theorem (Theorem 2) and the Haas–Giles nested-MLMC cost formula. Zero `sorry`. |
| `PLAN.md` | Formalisation milestones (M0–M3 done; M4, level-dependent precision, awaits sign-off) and ground rules. **Start here for new work.** |
| `notes/research-notes.md` | Evaluation of ternary/low-precision inputs for the Haas–Giles framework, the weak-vs-strong ("path") argument, AWS F2/Trainium notes, strategy and open directions. |
| `experiments/quantization/` | The two numerical checks behind the notes (Python), with saved outputs in `results/`. |
| `docs/` | The two papers: PDFs, extracted text and the Haas–Giles arXiv LaTeX source. |

## Lean formalisation

Machine-checked proofs (Lean 4 + Mathlib) of the complexity results for MLMC from:

* **[G15]** M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015) 259–328.
  §1.3 (eq. (1.1) and the optimal allocation on p. 4), §2.1 (eq. (2.1)–(2.3), Theorem 1),
  §2.2 (randomised MLMC), §2.4 (Multi-Index Monte Carlo, Theorem 2).
* **[HG25]** I.-B. Haas, M.B. Giles, *A nested MLMC framework for efficient simulations on
  FPGAs*, arXiv:2502.07123 (2025). §2.1–2.2, eq. (6)–(12).

The statement-by-statement comparison with the papers, including every deviation, is in
`notes/statement-audit.md`.

### What is proved

| File | Content | Paper |
|---|---|---|
| `MlmcLean/Allocation.lean` | Optimal sample allocation. `cost_lower_bound` / `optimal_cost_isLeast`: over **all** real allocations with total variance `≤ τ`, the least cost is `τ⁻¹(Σ√(V_iC_i))²` (Cauchy–Schwarz), attained by the Lagrange allocation, so the stationary point of the paper is the global minimum. `optimalN_variance` / `optimalN_cost`: the rounded-up `N_i = ⌈τ⁻¹√(V_i/C_i)Σ√(V_jC_j)⌉` meets the variance target with cost `≤ τ⁻¹(Σ√(V_iC_i))² + ΣC_i`. | [G15] (1.1), §1.3 p. 4; [HG25] (8) |
| `MlmcLean/Estimator.lean` | `mse_eq_variance_add_sq_bias`: `E[(Y−m)²] = V[Y] + (E[Y]−m)²`. `mlmc_mean`: `E[ΣY_ℓ] = E[P_L]` (telescoping). `mlmc_variance`: `V[ΣY_ℓ] = ΣV[Y_ℓ]` for pairwise independent `Y_ℓ`. `mlmc_mse`: their combination. | [G15] (2.1), (2.3) |
| `MlmcLean/Complexity.lean` | `mlmc_complexity_core`: the deterministic core of Theorem 1 in all three regimes `β > γ`, `β = γ`, `β < γ`, with `c₄` depending only on `α, β, γ, c₁, c₂, c₃`. | [G15] Thm 1 (proof, p. 7) |
| `MlmcLean/Theorem1.lean` | `giles_theorem1`: **Theorem 1 as stated**, on an arbitrary probability space, with random per-sample costs: `MSE < ε²` and `E[C] ≤ c₄·(ε⁻², ε⁻²(log ε)², ε^{−2−(γ−β)/α})`. `giles_theorem1_cost_sum` (the same for `Σ N_ℓC_ℓ`), `giles_theorem1_isBigO` (each regime as `IsBigO` as `ε → 0⁺`), `variance_sample_mean` (`V[N⁻¹ΣX_n] = v/N`). | [G15] Thm 1 |
| `MlmcLean/StandardEstimator.lean` | Theorem 1 for the actual estimator (2.2) `Y_ℓ = N_ℓ⁻¹Σ_n(P_ℓ − P_{ℓ−1})(ω^{(ℓ,n)})` built from independent inputs: unbiasedness, `V[Y_ℓ] = V_ℓ/N_ℓ` and independence across levels are **proved** (`integral_levelEstimator`, `variance_levelEstimator`, `indepFun_levelEstimator`); `giles_theorem1_standard`; `giles_theorem1_iid` on the product space `(Ω₀^{ℕ×ℕ}, ν^{⊗ℕ×ℕ})`, where no independence assumption remains (`exists_iid_inputs`). | [G15] (2.2), (2.3), Thm 1 |
| `MlmcLean/Randomised.lean` | Randomised single-term MLMC: `singleTerm_unbiased` (`E[Y] = E[P]`), `singleTerm_variance` (`V[Y] = Σp_ℓ⁻¹(V_ℓ + E_ℓ²) − (ΣE_ℓ)²` with `E_ℓ = E[P_ℓ − P_{ℓ−1}]`), `singleTerm_variance_ge` (`V[Y] ≥ Σp_ℓ⁻¹V_ℓ`), `summable_of_memLp_singleTerm` (finite variance forces `Σp_ℓ⁻¹V_ℓ < ∞`), `randomised_summable` / `randomised_not_summable` (possible iff `β > γ`), `randomised_optimal_p` / `_eq` (optimal `p_ℓ ∝ √(V_ℓ/C_ℓ)`), `randomised_mlmc_finite`. | [G15] §2.2 (Rhee–Glynn) |
| `MlmcLean/MultiIndex.lean` | Multi-indices `ℓ ∈ ℕ^D`, the cross-difference `ΔP_ℓ = (∏_dΔ_d)P_ℓ` (`crossDiff`, with Figure 2.1's `ΔP_{(5,4)}` as a check) and telescoping over boxes, `sum_crossDiff`. | [G15] §2.4 |
| `MlmcLean/Lattice.lean` | Lattice sums over the MIMC index sets `{θ·ℓ ≤ L}`: `slab_bound`, `tail_bound`, `inner_bound` (with the polynomial factor `(1+L)^{#critical directions − 1}`), `card_indexSet_le`. | [G15] §2.4 (proof) |
| `MlmcLean/Theorem2.lean` | `giles_theorem2`: **Theorem 2 (MIMC) as stated**, for all `D ≥ 1` and all three regimes `η < 0`, `η = 0`, `η > 0`, with the paper's exponents `e₁ = 2D₂`, `e₂ = (D₂−1)(2+η)` when `α_d > ½β_d`. `giles_theorem2_boundary`: the case `α_d ≥ ½β_d`, whose exponents the paper leaves open, with `e₁ = 2D₂ + D`, `e₂ = (D₂−1)(2+η) + D`. Deterministic forms `mimc_complexity`, `mimc_complexity_boundary`, `mimc_complexity_core`. | [G15] Thm 2 |
| `MlmcLean/Nested.lean` | Haas–Giles nested estimator. `nested_cost_lower_bound` and `nested_optimal_allocation`: eq. (12) as a two-sided statement (a lower bound for all allocations, and an integer allocation attaining it up to the rounding overhead `Σ(C̃_ℓ + C^Δ_ℓ)`). `nested_mlmc_mse`: (9)–(11). | [HG25] (9)–(12) |

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
  unbiased, so the conditions are required for sample sizes `n ≥ 1`, the only ones the theorems
  use.
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
  that Giles mentions on p. 7.

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
(titles, statements, sources) is in `prove2me/metadata.json`.

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
scripts/AxiomCheck.lean           axiom audit (run in CI)
scripts/prove2me/                 prove2.me packaging: extractors, generator, validator, uploader
PLAN.md, CLAUDE.md                milestones; instructions for Claude sessions
notes/statement-audit.md          statement-by-statement comparison with the papers
notes/research-notes.md           research notes (quantization, hardware, strategy)
experiments/quantization/         numerical checks + results/
docs/                             papers: PDF, extracted text, Haas–Giles LaTeX source
```
