# Statement-fidelity audit (PLAN.md M0)

Date: 2026-09-25. Sources: the PDFs and text in `docs/` only — Giles, *Multilevel Monte Carlo
methods*, Acta Numerica 24 (2015) [G15], and Haas–Giles, *A nested MLMC framework for efficient
simulations on FPGAs*, arXiv:2502.07123 [HG25] (PDF text and LaTeX source). Every paper statement
below was read from the typeset PDF (G15 pp. 3–16) or the LaTeX source (HG25 §2).

A compiling proof shows that the *Lean* statement is true. This audit checks, in both directions,
that each Lean statement says what the paper says: every hypothesis and conclusion of the paper is
in the Lean statement, and every Lean hypothesis is either in the paper or a standing convention
the paper relies on implicitly (listed as such).

## Mechanical checks

* `lake build` succeeds and `lake env lean scripts/AxiomCheck.lean` lists only `propext`,
  `Classical.choice`, `Quot.sound` for every theorem — verified in GitHub Actions on `master`
  (run 36082613038) and, after re-pinning to the prove2.me environment (Lean v4.33.1, Mathlib
  `0df444a`), on the working branch.
* No `sorry`, `admit`, `axiom` or `native_decide` in `MlmcLean/`.

## Findings that required changes

| # | Where | Finding | Resolution |
|---|---|---|---|
| 1 | `Allocation.lean`, `Complexity.lean`, README | Cited "Giles (1.2)". G15 has **no equation (1.2)**: §1.3 numbers only the cost (1.1); the allocation `N_ℓ = μ√(V_ℓ/C_ℓ)`, `μ = ε⁻²∑√(V_ℓC_ℓ)` is unnumbered (p. 4). | Citations corrected to "§1.3, p. 4". |
| 2 | `Estimator.lean` header | Labelled the telescoping identity `E[P_L] = E[P_0] + ∑ E[P_ℓ − P_{ℓ−1}]` as (2.1). In G15, (2.1) is the MSE identity; the telescoping identity is unnumbered (p. 4). | Header and docstrings corrected; `mse_eq_variance_add_sq_bias` now cites (2.1). |
| 3 | `giles_theorem1` | Condition (ii) was required for **every** sample size `n`, including `n = 0`. The estimator (2.2) with zero samples is `0⁻¹·0 = 0`, which is not unbiased, so the paper's own estimator did not satisfy the Lean hypothesis. | (ii) and cross-level independence are now required only for `n ≥ 1` (the theorem only uses sample sizes `N_ℓ ≥ 1`). |
| 4 | `giles_theorem1` | The conclusion bounded `∑ N_ℓ C_ℓ`, a number. G15 bounds `E[C]`, the expectation of the random total cost, and says the theorem was generalised "to allow for applications in which the simulation cost of individual samples is itself random" (p. 7). | `giles_theorem1` now has random costs `Cost ℓ n` with `E[Cost ℓ n] = n·C_ℓ` and bounds `E[∑_ℓ Cost ℓ (N ℓ)]`. The former statement is `giles_theorem1_cost_sum`. |
| 5 | Theorem 1 as a whole | The hypotheses of `giles_theorem1` (unbiasedness, `V[Y_ℓ] = V_ℓ/N_ℓ`, independence across levels) are *properties* of the estimator (2.2) that the paper derives from independent sampling. A formalisation that only assumes them does not show that MLMC with the standard estimator works. | New `StandardEstimator.lean`: builds (2.2) from independent inputs `ω^{(ℓ,n)}`, derives all three properties, proves Theorem 1 for it (`giles_theorem1_standard`), and on the infinite product space removes the independence assumption altogether (`giles_theorem1_iid`, `exists_iid_inputs`). |

## Theorem-by-theorem audit

### Giles (2015) Theorem 1 — `giles_theorem1` (`MlmcLean/Theorem1.lean`)

Paper (G15 p. 6–7): *Let P denote a random variable, and let P_ℓ denote the corresponding level ℓ
numerical approximation. If there exist independent estimators Y_ℓ based on N_ℓ Monte Carlo
samples, each with expected cost C_ℓ and variance V_ℓ, and positive constants α, β, γ, c₁, c₂, c₃
such that α ≥ ½ min(β,γ) and (i) |E[P_ℓ − P]| ≤ c₁2^{−αℓ}, (ii) E[Y_ℓ] = E[P_0] (ℓ = 0),
E[P_ℓ − P_{ℓ−1}] (ℓ > 0), (iii) V_ℓ ≤ c₂2^{−βℓ}, (iv) C_ℓ ≤ c₃2^{γℓ}, then there exists a positive
constant c₄ such that for any ε < e⁻¹ there are values L and N_ℓ for which the multilevel estimator
Y = ∑_{ℓ=0}^{L} Y_ℓ has MSE ≡ E[(Y − E[P])²] < ε² with a computational complexity C with bound
E[C] ≤ c₄ε⁻² (β > γ), c₄ε⁻²(log ε)² (β = γ), c₄ε^{−2−(γ−β)/α} (β < γ).*

| Paper | Lean | Match |
|---|---|---|
| random variable `P`, approximations `P_ℓ` | `P : Ω → ℝ`, `Pℓ : ℕ → Ω → ℝ` on a probability space `(Ω, μ)`, integrable | ✓ (integrability is needed for `E[P]` to exist; standing convention) |
| estimators `Y_ℓ` based on `N_ℓ` samples | `Y ℓ n`, for every sample size `n` — the theorem chooses `N_ℓ`, so the estimators must be given for every `n` | ✓ |
| "each [sample] with variance `V_ℓ`" | `V[Y ℓ n] = V ℓ / n` for `n ≥ 1`; `V_ℓ` is the per-sample variance, as in §1.3 and (2.3) | ✓ (reading of "each") |
| "each [sample] with expected cost `C_ℓ`" | random cost `Cost ℓ n` of `Y ℓ n` with `E[Cost ℓ n] = n C_ℓ` | ✓ |
| "independent estimators" | `Y i (N i)` and `Y j (N j)` independent for `i ≠ j`, for every choice of `N ≥ 1` | ✓ pairwise, which is weaker than mutual independence, so the Lean theorem is (slightly) more general |
| finite variance | `Y ℓ n ∈ L²` | ✓ standing convention |
| positive `α, β, γ, c₁, c₂, c₃`, `α ≥ ½ min(β,γ)` | `hα … hc₃`, `hαβγ : min β γ / 2 ≤ α` | ✓ (`β > 0` is not used by the proof; kept for fidelity) |
| (i)–(iv) | `h_i`, `h_ii₀`/`h_ii` (for `n ≥ 1`), `h_iii`, `h_iv` | ✓ |
| "for any ε < e⁻¹" | `∀ ε, 0 < ε → ε < exp(−1) →` | ✓ (`ε > 0` is implicit: `log ε` appears) |
| `∃ c₄ > 0` before `∀ ε` | same order | ✓ `c₄` does not depend on `ε`. As in the paper it may depend on the data; `mlmc_complexity_core` shows it depends only on `α, β, γ, c₁, c₂, c₃` |
| `∃ L, N_ℓ` | `∃ L N, ∀ ℓ, 0 < N ℓ` | ✓ (Lean adds that each `N_ℓ ≥ 1`) |
| `MSE ≡ E[(Y − E[P])²] < ε²` | `μ[(∑_{ℓ≤L} Y ℓ (N ℓ) − μ[P])²] < ε²` | ✓ |
| `E[C] ≤ c₄·(three cases)` | `μ[∑_{ℓ≤L} Cost ℓ (N ℓ)] ≤ c₄ · complexityBound α β γ ε` with `complexityBound` = `ε^{−2}`, `ε^{−2}(log ε)²`, `ε^{−2−(γ−β)/α}` for `γ < β`, `β = γ`, `β < γ` | ✓ |

Proof details that are **not** part of the statement: Lean splits the error budget as
`bias ≤ ε/2`, `variance ≤ ε²/2` (total `≤ ¾ε² < ε²`); Giles splits it as `ε²/2 + ε²/2`. Only the
constant `c₄` is affected.

Variants: `giles_theorem1_cost_sum` (conclusion `∑ N_ℓ C_ℓ ≤ …`, which equals `E[C]`);
`giles_theorem1_isBigO` (each regime as `IsBigO` as `ε → 0⁺`; adds `C_ℓ ≥ 0`, needed because
`IsBigO` compares absolute values).

### Theorem 1 for the estimator (2.2) — `giles_theorem1_standard`, `giles_theorem1_iid`

Paper: (2.2) `Y_ℓ = N_ℓ⁻¹ ∑_{n=1}^{N_ℓ} (P_ℓ^{(ℓ,n)} − P_{ℓ−1}^{(ℓ,n)})`, `P_{−1} ≡ 0`, "with the
inclusion of the level ℓ in the superscript (ℓ,n) indicating that independent samples are used at
each level of correction" (p. 4); `V_ℓ ≡ V[P_ℓ − P_{ℓ−1}]` (2.3).

Lean: inputs `ω (ℓ, n) : Ω → Ω₀`, mutually independent (`iIndepFun`), each with law `ν`
(`MeasurePreserving`); `P_ℓ^{(ℓ,n)} = Pl ℓ (ω (ℓ, n) x)`. Level approximations are measurable and
square-integrable under `ν` (standing conventions; measurability is needed for independence to
pass to functions of the inputs). Conditions (i), (iii), (iv) are stated for `ν`; condition (ii),
`V[Y_ℓ] = V_ℓ/N_ℓ` and independence across levels are **proved** (`integral_levelEstimator`,
`variance_levelEstimator`, `indepFun_levelEstimator`). `giles_theorem1_iid` states the result on
`(Ω₀^{ℕ×ℕ}, ν^{⊗(ℕ×ℕ)})` with coordinate inputs and per-sample costs `κ_ℓ(ω^{(ℓ,n)})`,
`C_ℓ = E[κ_ℓ]`, so no independence or existence assumption remains.

### Eq. (1.1) / HG25 (8) — `optimal_cost_isLeast`, `cost_lower_bound`, `optimalN_*`

Paper (G15 p. 4): minimising `∑ N_ℓ C_ℓ` for fixed variance `∑ N_ℓ⁻¹ V_ℓ = ε²`, "treating the
integers as real variables" with a Lagrange multiplier, gives `N_ℓ = μ√(V_ℓ/C_ℓ)`,
`μ = ε⁻²∑√(V_ℓC_ℓ)` and the cost `C = ε⁻²(∑√(V_ℓC_ℓ))²` (1.1). HG25 (8) is the same with
`λ = ε⁻²∑√(V_ℓC_ℓ)`.

Lean: `optimal_cost_isLeast` — for `V_i, C_i > 0` and `τ > 0`, the value `τ⁻¹(∑√(V_iC_i))²` is the
**least** cost over all real allocations `n_i > 0` with variance `≤ τ`, and it is attained by the
Lagrange allocation (with variance exactly `τ`). With `τ = ε²` this is (1.1)/(8). The Lagrange
derivation only gives a stationary point; the Lean statement proves it is the global minimum
(Cauchy–Schwarz, `cost_lower_bound`). Variance `≤ τ` instead of `= τ` does not change the minimum.
`optimalN_variance`/`optimalN_cost` cover the rounding up to integers that Theorem 1's proof
mentions ("the optimal value is rounded up to the nearest integer", p. 7), with overhead `∑ C_i`.

### Eq. (2.1), (2.3) — `mse_eq_variance_add_sq_bias`, `mlmc_mean`, `mlmc_variance`, `mlmc_mse`, `variance_sample_mean`

* (2.1) `MSE = V[Y] + (E[Y] − E[P])²`: `mse_eq_variance_add_sq_bias` for any `Y ∈ L²` and any real
  target `m` (the paper's `m = E[P]`). ✓
* (2.3) `E[Y] = E[P_L]`: `mlmc_mean`, from condition (ii) by telescoping. ✓
* (2.3) `V[Y] = ∑_ℓ N_ℓ⁻¹ V_ℓ`: `mlmc_variance` (`V[∑Y_ℓ] = ∑V[Y_ℓ]` for pairwise independent
  `Y_ℓ`) combined with `variance_sample_mean` (`V[N⁻¹∑X_n] = v/N` for pairwise independent samples
  of variance `v`). ✓ Pairwise independence is weaker than the paper's independence.

### Randomised MLMC, G15 §2.2 — `Randomised.lean` (M2)

Paper (p. 9–11): single-term estimator `Y = p_{ℓ'}⁻¹(P_{ℓ'} − P_{ℓ'−1})`, level `ℓ'` chosen with
probability `p_ℓ`; `E[Y] = ∑ E[P_ℓ − P_{ℓ−1}] = E[P]`; `V[Y] = ∑ p_ℓ⁻¹(V_ℓ + E_ℓ²) − (∑E_ℓ)² ≥
∑ p_ℓ⁻¹V_ℓ`; finite variance and expected cost need `∑p_ℓ⁻¹V_ℓ < ∞`, `∑p_ℓC_ℓ < ∞`; possible for
`β > γ` with `p_ℓ ∝ 2^{−(γ+β)ℓ/2}`, impossible for `β ≤ γ`; optimal `p_ℓ ∝ √(V_ℓ/C_ℓ)`.

Lean: `singleTerm_unbiased`, `singleTerm_variance`, `singleTerm_variance_ge`,
`summable_of_memLp_singleTerm` (necessity), `randomised_summable`, `randomised_not_summable`,
`randomised_optimal_p`, `randomised_optimal_p_eq`, `randomised_mlmc_finite`.

Deviations and implicit assumptions made explicit:

* The paper does not state integrability conditions. Unbiasedness assumes
  `∑ E|P_ℓ − P_{ℓ−1}| < ∞` (equivalent to `E|Y| < ∞`) and `E[P_L] → E[P]`; the variance formula
  assumes `∑ p_ℓ⁻¹E[(P_ℓ − P_{ℓ−1})²] < ∞` (equivalent to `E[Y²] < ∞`). The level is assumed
  independent of each `P_ℓ − P_{ℓ−1}` and the approximations measurable.
* "Not possible when β ≤ γ" needs the rates to be attained, `V_ℓ ≥ c₂2^{−βℓ}`, `C_ℓ ≥ c₃2^{γℓ}`
  (the paper's "∝"); upper bounds alone cannot rule anything out.
* The paper's "optimal choice for p_ℓ" comes from minimising the approximate cost
  `N∑p_ℓC_ℓ` with `N ≈ ε⁻²∑V_ℓ/p_ℓ`; Lean proves the exact statement behind it: the product
  `(∑V_ℓ/p_ℓ)(∑p_ℓC_ℓ)` is at least `(∑√(V_ℓC_ℓ))²` for every positive `p`, with equality at
  `p_ℓ ∝ √(V_ℓ/C_ℓ)`. The "≈" statements themselves are heuristics and are not formalised.
* **PLAN.md M2 overstates the paper.** PLAN says "with β > γ … both the variance and the expected
  cost are finite". The paper only says the two *necessary* series can be made finite. The
  variance also contains `∑ p_ℓ⁻¹E_ℓ²`, which can diverge under (i)–(iv): take `α = γ/2 < β/2`
  and `P_ℓ − P_{ℓ−1} ≡ 2^{−αℓ}` deterministic; then (i)–(iv) hold with `V_ℓ = 0`, but with
  `p_ℓ ∝ 2^{−(β+γ)ℓ/2}` one gets `p_ℓ⁻¹E_ℓ² ∝ 2^{(β−γ)ℓ/2} → ∞`. `randomised_mlmc_finite` proves
  finiteness under the second-moment form of (iii) that Giles mentions on p. 7.

### Haas–Giles (2025) eq. (9)–(12) — `Nested.lean`

Paper (HG25 §2.2): (9) `E[P_L] = ∑_ℓ E[Δ̃P_ℓ] + E[ΔP_ℓ − Δ̃P_ℓ]`; (10) `Cost = ∑ Ñ_ℓC̃_ℓ +
N^Δ_ℓC^Δ_ℓ`; (11) `Variance = ∑ Ñ_ℓ⁻¹Ṽ_ℓ + (N^Δ_ℓ)⁻¹V^Δ_ℓ`; minimising under `Variance = ε²` with a
Lagrange multiplier gives (12) `Cost_nested = ε⁻²(∑√(Ṽ_ℓC̃_ℓ) + √(V^Δ_ℓC^Δ_ℓ))²`.

Lean: `nested_cost_lower_bound` (every real allocation with variance (11) `≤ ε²` costs at least
(12)), `nested_optimal_allocation` (integer allocation with variance `≤ ε²` and cost `≤` (12)
plus the rounding overhead `∑(C̃_ℓ + C^Δ_ℓ)`, which the paper explicitly ignores), and
`nested_mlmc_mse` ((9) for the means and (11) in terms of the component-estimator variances; the
per-sample form follows from `variance_sample_mean`). Deviations: variance `≤ ε²` instead of
`= ε²` (same minimum); `C^Δ_ℓ = C_ℓ + C̃_ℓ` is not imposed (the statements hold for any
`C^Δ_ℓ > 0`, so this is a generalisation).

### Giles (2015) Theorem 2 (MIMC) — `giles_theorem2`, `giles_theorem2_boundary` (`MlmcLean/Theorem2.lean`, M3)

Paper (G15 §2.4, pp. 12–14, read from the typeset PDF): backward differences
`Δ_d P_ℓ ≡ P_ℓ − P_{ℓ−e_d}`, cross-difference `ΔP_ℓ ≡ (∏_{d=1}^D Δ_d) P_ℓ`, telescoping
`E[P] = ∑_{ℓ≥0} E[ΔP_ℓ]`. *Theorem 2. If there exist independent estimators Y_ℓ based on N_ℓ
Monte Carlo samples, each with expected cost C_ℓ and variance V_ℓ, and positive D-dimensional
vectors α, β, γ, with α_d ≥ ½β_d, and also positive constants c₁, c₂, c₃ such that
i) |E[P_ℓ − P]| → 0 as min_d ℓ_d → ∞, iii) E[Y_ℓ] = E[ΔP_ℓ], ii) |E[Y_ℓ]| ≤ c₁2^{−α·ℓ},
iv) V_ℓ ≤ c₂2^{−β·ℓ}, v) C_ℓ ≤ c₃2^{γ·ℓ}, then there exists a positive constant c₄ such that for
any ε < e⁻¹ there is a set of levels 𝓛, and integers N_ℓ for which the multilevel estimator
Y = ∑_{ℓ∈𝓛} Y_ℓ has MSE ≡ E[(Y − E[P])²] < ε² with a computational complexity C with bound
E[C] ≤ c₄ε⁻² (η < 0), c₄ε⁻²|log ε|^{e₁} (η = 0), c₄ε^{−2−η}|log ε|^{e₂} (η > 0), where
η = max_d (γ_d − β_d)/α_d. When α_d > ½β_d for all d, the exponents for the logarithmic terms are
e₁ = 2D₂, e₂ = (D₂ − 1)(2 + η), where D₂ is the number of dimensions d for which
(γ_d − β_d)/α_d = η. The form of the exponents is more complicated when α_d = ½β_d for some d.*

| Paper | Lean | Match |
|---|---|---|
| level index `ℓ ∈ ℕ^D` | `ℓ : Fin D → ℕ`, `[NeZero D]` | ✓ (`D ≥ 1` is implicit: `η` is a maximum over the directions) |
| `Δ_d P_ℓ = P_ℓ − P_{ℓ−e_d}`, `ΔP_ℓ = (∏_d Δ_d) P_ℓ` | `crossDiff p ℓ`, defined by recursion on `D`, with `P_{ℓ−e_d}` read as `0` when `ℓ_d = 0` (the paper's `P_{−1} ≡ 0` in each direction); `crossDiff_one` is the `D = 1` case `P_ℓ − P_{ℓ−1}`, and an `example` checks Figure 2.1 (`ΔP_{(5,4)}` uses the four values at `(5,4), (4,4), (5,3), (4,3)`) | ✓ |
| telescoping `E[P] = ∑_{ℓ≥0} E[ΔP_ℓ]` | `sum_crossDiff`: `∑_{ℓ ≤ k} ΔP_ℓ = P_k` over every box; the proof uses this finite identity and condition i) | ✓ (the infinite-sum form is not needed) |
| independent `Y_ℓ`, `N_ℓ` samples, expected cost `C_ℓ`, variance `V_ℓ` | as for Theorem 1: `Y ℓ n`, random costs `Cost ℓ n` with `E[Cost ℓ n] = n C_ℓ`, `V[Y ℓ n] = V_ℓ/n` for `n ≥ 1`, pairwise independence across levels for every `N ≥ 1`, `Y ℓ n ∈ L²` | ✓ (same reading as Theorem 1; pairwise independence is weaker than the paper's) |
| positive `α, β, γ` with `α_d ≥ ½β_d`, positive `c₁, c₂, c₃` | `hα hβ hγ`, `hαβ : β d / 2 < α d` (`giles_theorem2`) or `β d / 2 ≤ α d` (`giles_theorem2_boundary`); `hc₁ hc₂ hc₃` | ✓ (`β_d > 0` is unused by the proof; kept for fidelity) |
| i) `|E[P_ℓ − P]| → 0` as `min_d ℓ_d → ∞` | `h_i : ∀ δ > 0, ∃ n₀, ∀ ℓ, (∀ d, n₀ ≤ ℓ_d) → |E[P_ℓ − P]| < δ` | ✓ (the definition of this limit) |
| iii) `E[Y_ℓ] = E[ΔP_ℓ]` | `h_iii` (for `n ≥ 1`, as in Theorem 1, finding 3) | ✓ |
| ii) `|E[Y_ℓ]| ≤ c₁2^{−α·ℓ}` | `h_ii` (for `n ≥ 1`) | ✓ |
| iv), v) | `h_iv`, `h_v` with `dot a ℓ = ∑_d a_d ℓ_d` | ✓ |
| `∃ c₄ > 0 ∀ ε < e⁻¹ ∃ 𝓛, N_ℓ` | `∃ c₄, 0 < c₄ ∧ ∀ ε, 0 < ε → ε < exp(−1) → ∃ (𝓛 : Finset _) N, (∀ ℓ, 0 < N ℓ) ∧ …` | ✓ (`𝓛` finite, `N_ℓ ≥ 1`) |
| `MSE < ε²` | `μ[(∑_{ℓ∈𝓛} Y ℓ (N ℓ) − μ[P])²] < ε²` | ✓ |
| `E[C] ≤ c₄ · (three regimes)`, `e₁ = 2D₂`, `e₂ = (D₂−1)(2+η)` for `α_d > ½β_d` | `μ[∑_{ℓ∈𝓛} Cost ℓ (N ℓ)] ≤ c₄ · mimcBound η (2D₂) ((D₂−1)(2+η)) ε` with `mimcBound η e₁ e₂ ε = ε⁻²`, `ε⁻²|log ε|^{e₁}`, `ε^{−2−η}|log ε|^{e₂}` for `η < 0`, `= 0`, `> 0`; `η = mimcEta`, `D₂ = mimcD2` | ✓ |
| exponents when some `α_d = ½β_d`: "more complicated", not stated | `giles_theorem2_boundary`: `e₁ = 2D₂ + D`, `e₂ = (D₂−1)(2+η) + D` | not a paper statement: a valid (not necessarily sharp) bound for the case the paper leaves open |

**Label typo in the paper.** The statement lists the conditions as i), iii), ii), iv), v): "iii)"
is the unbiasedness `E[Y_ℓ] = E[ΔP_ℓ]` and "ii)" is the decay `|E[Y_ℓ]| ≤ c₁2^{−α·ℓ}`, while the
Notes that follow call unbiasedness ii) and the weak-error rate iii). The Lean hypothesis names
follow the statement (`h_iii` is unbiasedness, `h_ii` the decay), and the docstrings say so.

Lemmas behind the proof, not paper statements: the summation region is a simplex
`{θ·ℓ ≤ L}` ("of the form `ℓ·n ≤ L` … with strictly positive components", p. 15);
`slab_bound`, `tail_bound`, `inner_bound`, `card_indexSet_le` (lattice sums over it, with the
multiplicity of the critical directions); `mimc_complexity_core`, `mimc_complexity`,
`mimc_complexity_boundary` (the deterministic statements: bias, variance and cost with
`V_ℓ = c₂2^{−β·ℓ}`, `C_ℓ = c₃2^{γ·ℓ}`); `mimc_mse_cost` (from the deterministic form to the
probability space, for any bound function); `integrable_integral_crossDiff`
(`E[ΔP_ℓ] = Δ(E[P_·])_ℓ`).

### Deterministic core — `mlmc_complexity_core`, `exists_L_N`

Not paper statements; they are the steps of the proof sketch on p. 7 ("L is chosen so that
(E[Y] − E[P])² < ½ε² …, N_ℓ … rounded up"). `mlmc_complexity_core` shows `c₄` depends only on
`α, β, γ, c₁, c₂, c₃`, which is stronger than the paper's statement.

## Out of scope (as in PLAN.md)

The rate conditions (i)–(iv) are hypotheses, exactly as in the papers; proving them for
Euler–Maruyama or Milstein needs Itô calculus.
