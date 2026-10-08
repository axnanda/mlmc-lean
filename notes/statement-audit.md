# Statement-fidelity audit (PLAN.md M0)

Date: 2026-09-25, updated 2026-09-26 (review-fix batch). Sources: the PDFs and text in `docs/` only — Giles, *Multilevel Monte Carlo
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
| finite variance | `Y ℓ n ∈ L²` for `n ≥ 1` | ✓ standing convention |
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

Paper (G15 p. 4): minimising `∑ N_ℓ C_ℓ` for fixed variance `∑ N_ℓ⁻¹ V_ℓ = ε²` with a Lagrange
multiplier gives `N_ℓ = μ√(V_ℓ/C_ℓ)`, `μ = ε⁻²∑√(V_ℓC_ℓ)` and the cost `C = ε⁻²(∑√(V_ℓC_ℓ))²`
(1.1). (The phrase "treating the integers N₀, N₁ as real variables" is in the two-level
discussion of §1.2, p. 3.) HG25 (8) is the same with `λ = ε⁻²∑√(V_ℓC_ℓ)`.

Lean: `optimal_cost_isLeast` — for `s` nonempty, `V_i, C_i > 0` and `τ > 0`, the value
`τ⁻¹(∑√(V_iC_i))²` is the **least** cost over all real allocations `n_i > 0` with variance `≤ τ`;
it is attained by the Lagrange allocation `lagrangeN` (`n_i = τ⁻¹√(V_i/C_i)∑√(V_jC_j)`, with
variance exactly `τ`, `lagrangeN_variance_cost`) and by no other allocation (`lagrangeN_unique`).
With `τ = ε²` this is (1.1)/(8). The Lagrange derivation only gives a stationary point; the Lean
statement proves it is the unique global minimum (Cauchy–Schwarz, `cost_lower_bound`). Variance
`≤ τ` instead of `= τ` does not change the minimum.

§1.2 (p. 3, two levels): "the variance is minimised for a fixed cost by choosing
`N₁/N₀ = √(V₁/C₁)/√(V₀/C₀)`". Lean: `optimal_variance_isLeast` (the dual problem for any finite
index set: least variance `B⁻¹(∑√(V_iC_i))²` for cost `≤ B`, unique minimiser
`B√(V_i/C_i)/∑√(V_jC_j)`) and `twoLevel_optimal_ratio` (for two levels and cost exactly `B`: a
pair minimises the variance **iff** the ratio holds). ✓, with the paper's real relaxation.
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
`summable_of_memLp_singleTerm` and `randomised_necessary` (necessity of both series:
"For both the variance and the expected cost to be finite, it is necessary that …", p. 10),
`integral_cost_level` (the expected cost of one sample is `∑p_ℓ E[κ_ℓ]`, finite iff the series
converges, when the level cost `κ_ℓ ≥ 0` is independent of the level), `singleTermN_mean_variance`
(the estimator with `N` independent samples, p. 9: unbiased with variance `V[Y]/N`),
`randomised_summable`, `randomised_not_summable`, `randomised_optimal_p`,
`randomised_optimal_p_eq`, `randomised_optimal_p_isLeast` (the paper's optimal `p_ℓ` minimises
`(∑p_ℓ⁻¹V_ℓ)(∑p_ℓC_ℓ)`), `randomised_mlmc_finite`.

Deviations and implicit assumptions made explicit:

* The paper does not state integrability conditions. Unbiasedness assumes
  `∑ E|P_ℓ − P_{ℓ−1}| < ∞` (equivalent to `E|Y| < ∞`) and `E[P_L] → E[P]`; the variance formula
  assumes `∑ p_ℓ⁻¹E[(P_ℓ − P_{ℓ−1})²] < ∞` (equivalent to `E[Y²] < ∞`). The level is assumed
  independent of each `P_ℓ − P_{ℓ−1}` and the approximations measurable.
* `singleTerm_unbiased` assumes `P` integrable. The proof does not need it, but without it the
  blind read-back showed a degenerate reading: for non-integrable `P`, `E[P]` is Lean's junk value
  `0` and the statement says `E[P_L] → 0 ⇒ E[Y] = 0`. The paper's `P` has a mean, so the
  hypothesis is the paper's (added 2026-09-25 after the read-back).
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

Lean: `nested_cost_isLeast` ((12) is the least cost over all real allocations with variance (11)
`≤ ε²`, attained by the paper's `λ_M` allocation), `nested_cost_lower_bound` (the lower half),
`nested_optimal_allocation` (integer allocation with variance `≤ ε²` and cost `≤` (12) plus the
rounding overhead `∑(C̃_ℓ + C^Δ_ℓ)`, which the paper explicitly ignores),
`nestedEstimator_mean_variance` (the nested estimator built from independent inputs has mean
`E[P_L]`, the identity (9), and variance (11) with the per-sample variances `Ṽ_ℓ = V[Δ̃P_ℓ]`,
`V^Δ_ℓ = V[ΔP_ℓ − Δ̃P_ℓ]`), `nestedCost_mean` (its expected cost is (10)) and `nested_mlmc_mse`
(mean, variance and MSE for abstract component estimators). `nested_saving` makes the claim of
p. 4 ("a computational saving of a factor approximately `max_ℓ C̃_ℓ/C^Δ_ℓ`") precise: if
`C̃_ℓ/C^Δ_ℓ ≤ r`, `V^Δ_ℓ ≤ δ²(C̃_ℓ/C^Δ_ℓ)Ṽ_ℓ`, `Ṽ_ℓ ≤ θV_ℓ` and `C^Δ_ℓ ≤ (1+κ)C_ℓ`, then
(12) `≤ (1+δ)²θ(1+κ)r ·` (8); the paper's "≈" is the regime `δ, κ → 0`, `θ → 1`. Deviations: variance `≤ ε²` instead of
`= ε²` (same minimum); `C^Δ_ℓ = C_ℓ + C̃_ℓ` is not imposed (the statements hold for any
`C^Δ_ℓ > 0`, so this is a generalisation).

### Giles (2015) Theorem 2 (MIMC) — `giles_theorem2_full`, `giles_theorem2`, `giles_theorem2_boundary` (`MlmcLean/Theorem2.lean`, M3)

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
| telescoping `E[P] = ∑_{ℓ≥0} E[ΔP_ℓ]` | `sum_crossDiff`: `∑_{ℓ ≤ k} ΔP_ℓ = P_k` over every box; `tendsto_sum_box_integral_crossDiff`: the box sums of `E[ΔP_ℓ]` tend to `E[P]` as `min_d k_d → ∞`, from condition i); `hasSum_integral_crossDiff`: under i)–iii) the series converges absolutely (unconditionally) with sum `E[P]` | ✓ |
| independent `Y_ℓ`, `N_ℓ` samples, expected cost `C_ℓ`, variance `V_ℓ` | as for Theorem 1: `Y ℓ n`, random costs `Cost ℓ n` with `E[Cost ℓ n] = n C_ℓ`, `V[Y ℓ n] = V_ℓ/n` and `Y ℓ n ∈ L²` for `n ≥ 1`, pairwise independence across levels for every `N ≥ 1` | ✓ (same reading as Theorem 1; pairwise independence is weaker than the paper's) |
| positive `α, β, γ` with `α_d ≥ ½β_d`, positive `c₁, c₂, c₃` | `hα hβ hγ`, `hαβ : β d / 2 < α d` (`giles_theorem2`) or `β d / 2 ≤ α d` (`giles_theorem2_boundary`); `hc₁ hc₂ hc₃` | ✓ (`β_d > 0` is unused by the proof; kept for fidelity) |
| i) `|E[P_ℓ − P]| → 0` as `min_d ℓ_d → ∞` | `h_i : ∀ δ > 0, ∃ n₀, ∀ ℓ, (∀ d, n₀ ≤ ℓ_d) → |E[P_ℓ − P]| < δ` | ✓ (the definition of this limit) |
| iii) `E[Y_ℓ] = E[ΔP_ℓ]` | `h_iii` (for `n ≥ 1`, as in Theorem 1, finding 3) | ✓ |
| ii) `|E[Y_ℓ]| ≤ c₁2^{−α·ℓ}` | `h_ii` (for `n ≥ 1`) | ✓ |
| iv), v) | `h_iv`, `h_v` with `dot a ℓ = ∑_d a_d ℓ_d` | ✓ |
| `∃ c₄ > 0 ∀ ε < e⁻¹ ∃ 𝓛, N_ℓ` | `∃ c₄, 0 < c₄ ∧ ∀ ε, 0 < ε → ε < exp(−1) → ∃ (𝓛 : Finset _) N, (∀ ℓ, 0 < N ℓ) ∧ …` | ✓ (`𝓛` finite, `N_ℓ ≥ 1`) |
| `MSE < ε²` | `μ[(∑_{ℓ∈𝓛} Y ℓ (N ℓ) − μ[P])²] < ε²` | ✓ |
| `E[C] ≤ c₄ · (three regimes)`, `e₁ = 2D₂`, `e₂ = (D₂−1)(2+η)` for `α_d > ½β_d` | `μ[∑_{ℓ∈𝓛} Cost ℓ (N ℓ)] ≤ c₄ · mimcBound η (2D₂) ((D₂−1)(2+η)) ε` with `mimcBound η e₁ e₂ ε = ε⁻²`, `ε⁻²|log ε|^{e₁}`, `ε^{−2−η}|log ε|^{e₂}` for `η < 0`, `= 0`, `> 0`; `η = mimcEta`, `D₂ = mimcD2` | ✓ |
| exponents when some `α_d = ½β_d`: "more complicated", not stated | `giles_theorem2_full` (the goal): under `α_d ≥ ½β_d`, `∃ e₁ e₂`, chosen before the probability space and the constants, with `e₁ = 2D₂`, `e₂ = (D₂−1)(2+η)` when every `α_d > ½β_d` — exactly the paper's claim. `giles_theorem2_boundary` gives explicit exponents: `e₁ = 2D₂ + (D₃−3)⁺`, `e₂ = (D₂−1)(2+η) + (D₃−1)⁺` with `D₃ = mimcD3 = #{d : α_d = ½β_d}` (natural-number subtraction) | `giles_theorem2_full` ✓; the explicit boundary exponents are not a paper statement: a valid bound for the case the paper leaves open, not claimed sharp; for `D₃ = 0` (every `α_d > ½β_d`) they are the paper's |

**Label typo in the paper.** The statement lists the conditions as i), iii), ii), iv), v): "iii)"
is the unbiasedness `E[Y_ℓ] = E[ΔP_ℓ]` and "ii)" is the decay `|E[Y_ℓ]| ≤ c₁2^{−α·ℓ}`, while the
Notes that follow call unbiasedness ii) and the weak-error rate iii). The Lean hypothesis names
follow the statement (`h_iii` is unbiasedness, `h_ii` the decay), and the docstrings say so.

Lemmas behind the proof, not paper statements: the summation region is a simplex
`{θ·ℓ ≤ L}` ("of the form `ℓ·n ≤ L` … with strictly positive components", p. 15);
`slab_bound`, `tail_bound`, `inner_bound` (lattice sums over it, with the multiplicity of the
critical directions); `mimc_complexity_core`, `mimc_complexity`,
`mimc_complexity_boundary` (the deterministic statements: bias, variance and cost with
`V_ℓ = c₂2^{−β·ℓ}`, `C_ℓ = c₃2^{γ·ℓ}`); `mimc_mse_cost` (from the deterministic form to the
probability space, for any bound function); `integrable_integral_crossDiff`
(`E[ΔP_ℓ] = Δ(E[P_·])_ℓ`).

### Deterministic core — `mlmc_complexity_core`, `exists_L_N`

Not paper statements; they are the steps of the proof sketch on p. 7 ("L is chosen so that
(E[Y] − E[P])² < ½ε² …, N_ℓ … rounded up"). `mlmc_complexity_core` shows `c₄` depends only on
`α, β, γ, c₁, c₂, c₃`, which is stronger than the paper's statement.

## Round 10 (2026-09-29): coverage re-audit of both papers

Five independent auditors re-read Giles (2015) §1–§11 and Haas–Giles (2025) in full and classified
all 644 claims against the Lean statements (tables in `notes/coverage/`; each row gives the claim,
the Lean name and the status). No Lean statement misstates a paper. The claims found missing or
partial were formalised in this round; `notes/coverage/README.md` maps every one of them to its
Lean statement or to the reason it is not formalised. The deviations of the new statements:

* **ML2R (G15 §2.3; `ML2RTheorem.lean`).** The paper's "`O(2^{−αℓL})`" in the weak-error
  expansion is read with one constant `K` for all `L` and `ℓ ≤ L` (implicit in the paper: `L`
  grows as `ε → 0`, and with a constant growing with `L` the bias need not be small). Under it the
  bias is at most `C_α K 2^{−αL(L+1)/2}` (`ml2r_bias_le`); the printed `O(2^{−αL²})` cannot hold
  uniformly (`ml2r_bias`: the expansion `2^{−α(L+1)ℓ}` has bias exactly `±2^{−αL(L+1)/2}`), so
  the `β < γ` cost exponent is `√(2|log₂ ε|/α)`, `√2` times the printed one. The complexity
  (`ml2r_theorem_eq`, `ml2r_theorem_lt`) is stated for the mean square error of the estimator
  itself; the earlier `ml2r_complexity_eq`/`_lt` are its deterministic core.
* **Theorem 2's index set (G15 §2.4, p. 15).** `giles_theorem2_indexSet` and
  `giles_theorem2_boundary_indexSet` state Theorem 2 on the simplex `{θ·ℓ ≤ L}`,
  `θ_d = α_d + (γ_d − β_d)/2` (the paper's "of the form `ℓ·n ≤ L`"; it does not say which `n`).
  That this shape is *optimal* among all index sets is not formalised.
* **Asymptotic normality (G15 §2.1, p. 8; `AsymptoticNormal.lean`).** Proved for each level
  estimator and, for a fixed number of levels with `N_ℓ = m_ℓ n`, for the MLMC estimator. Collier
  et al. let `L` grow as `ε → 0`; that needs a Lindeberg–Feller central limit theorem, which
  Mathlib does not have, and their confidence-interval theorem is only cited by Giles.
* **Randomised MLMC "≈" (G15 §2.2).** "If `E_ℓ² ≪ V_ℓ` … `N ≈ ε⁻² Σ V_ℓ/p_ℓ`" is made exact:
  `E_ℓ² ≤ δV_ℓ` puts `V[Y]` between `Σ V_ℓ/p_ℓ` and `(1 + δ) Σ V_ℓ/p_ℓ`
  (`singleTerm_variance_le_of_sq_le`, `singleTermN_samples_of_sq_le`).
* **Splitting "to leading order" (G15 §5.2).** The implicit condition is identified:
  splitting keeps the variance to leading order at negligible extra cost iff
  `E[v]/V[m] = o(h⁻¹)` (`splitting_leading_order`), with the cost model of `h⁻¹ − 1 + M` steps.
* **Random-shift QMC (G15 §3.5).** Formalised on the torus `(ℝ/ℤ)^d`, i.e. for the periodic
  extension of the integrand; the points are arbitrary (a rank-1 lattice is one choice).
* **Markov chains, `N_ℓ` linear (G15 §10.1).** `markov_linear_levels` gives conditions (iii)–(iv)
  of Theorem 1; the paper's "the decay is exponential in `N_ℓ − N_{ℓ−1}`" should read `N_{ℓ−1}`
  (with linear `N_ℓ` the difference is constant; `variance_levels_le`).
* **The limit law of a Markov chain (G15 §10.1; `MarkovLimitLaw.lean`).** The chain contracts on
  average in `L^p`, `E[d(φ(x, ξ), φ(y, ξ))^p] ≤ ρ d(x, y)^p` with `p = 2γ` (the paper's condition,
  `ρ` its supremum), on a complete separable metric space. The limit law is the unique invariant
  law (`existsUnique_invariant`); for the example it is `U[0, 2]` (`halfStep_limit_uniform`,
  `halfStep_invariant_unique`); the level bias decays like `(√ρ)^{N_ℓ}` and MLMC for `E[f(X_∞)]`
  has cost `O(ε⁻²)` (`markov_mlmc_theorem1`) or is unbiased with the randomised estimator
  (`markov_randomised_mlmc`). The paper's `γ ∈ (0, 1)` is relaxed to `0 < γ ≤ 1`.
* **Digital options (G15 §5.1–§5.2; `SDEDigital.lean`).** "`V_ℓ = O(h^{1/2})`" needs more than the
  mean-square strong rate: from `E[(Ŝ − S)²] = O(h)` and a bounded density alone the variance is
  `O(h^{1/3})`, and this is sharp (`variance_digital_rate`); with Gaussian tails of the error it is
  `O(√(h log(1/h)))` (`digital_mismatch_le_of_tail`). The antithetic call's `O(h^{3/2})` (§5.3)
  is proved when, given `|A − B|`, the average `½(A + B)` of the fine and antithetic values has a
  bounded density (`variance_call_antithetic_le`); marginal information alone gives a weaker rate
  (`variance_call_antithetic_le_holder`). For GBM, `β = 1/3` holds with no assumption
  (`gbm_digital_variance_le`).
* **Super-linear drift (G15 §5.6; `SDEMisc.lean`).** Deterministic analogues: the explicit Euler
  step for the drift `−S³` diverges iff `h S₀² > 2` (`eulerCubic_growth`,
  `eulerCubic_tendsto_atTop`, `eulerCubic_bounded`), and the tamed step stays bounded
  (`tamedCubic_bounded`). The moment bounds for the SDE (Hutzenthaler–Jentzen–Kloeden) are not
  formalised.
* **Poisson counts on union grids (G15 §8, §5.6; `PoissonGrids.lean`).** Deterministic grids only;
  the adaptive grids of §5.6 depend on the path and need a martingale argument. The tau-leaping
  statements compare the law of the state at one grid time (payoffs of the terminal state);
  path functionals are covered when the rate does not depend on the state (`unionGrid_2_4`).
* **Elliptic PDE with a random coefficient (G15 §7.1; `ApplicationExtras.lean`).** A deterministic
  `K` with `|P − P_ℓ| < K h_ℓ²` is impossible for the example (`not_ae_abs_gaussian_sq_mul_le`);
  with a random `K`, `E[K²] < ∞`, the rates `α = 2`, `β = 4` follow (`elliptic_rates_random`).
* **Nested simulation with discretised inner paths (G15 §9.1–§9.2; `NestedRates.lean`).** The
  weak and strong orders of the inner discretisation (Milstein) are hypotheses on the inner
  approximations `g_ℓ`; from them `α = 1`, `β = 2`, `γ = 2` and cost `O(ε⁻²(log ε)²)`
  (`nested_sde_mlmc_complexity`). The piecewise-linear `f` of Bujok, Hambly and Reisinger gives
  `β = 3/2` and `O(ε⁻²)` if the inner mean has little mass near the kink, e.g. a bounded density
  (`nested_kink_variance_rate_of_density`, `nested_kink_mlmc_complexity`), and the conditional
  fourth moments `E_W[g(z, W)⁴]` are bounded uniformly in `z` (raw moments, a simplification that
  also bounds the conditional mean); the bias rate proved there is `α = ½`, which is what
  Theorem 1 needs with `β = 3/2`, `γ = 1`. The MIMC rates
  `E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})`, `V_ℓ = O(2^{−2ℓ₁−2ℓ₂})` need `f″` Lipschitz and `L⁴` strong
  convergence (`nested_mimc_mean_rate`, `nested_mimc_variance_rate`); the paper's intermediate
  "`Δg_{1,ℓ₂} + Δg_{1,ℓ₂−1} = O(2^{−ℓ₁/2})`" holds only after re-centring.
* **Haas–Giles §6 (`HaasGilesRemarks.lean`).** "The cost factor is smaller than 1, which means that
  the nested framework is cheaper" is exact for (34) but, for the nested cost (32), a factor `ρ`
  on every level needs `ρ²(1 + ρ²) < 1` (sufficient; the sharp threshold is `ρ ≈ 0.943`), and a
  factor `99/100` can make (32) more expensive than (8) (`exists_costFactor_lt_one_nestedCost_gt`).
  Under the paper's own assumptions (26) is an equality (`variance_linearised_indep_eq`). With
  fixed bit-widths, the paper's "`O(h⁻¹ 2^{e−d})`" rounding error is the worst case; under the
  model (22) the root mean square is of order `h^{−1/2} 2^{e−d}`
  (`integral_sq_perturbed_path_sub_bounds`), which still dominates the `O(h^{1/2})` strong error
  for small `h` (`strongError_lt_integral_sq_perturbed_path_sub`).
* **The central limit theorem with a growing number of levels (G15 §2.1, p. 8;
  `MLMCCentralLimit.lean`, round 12).** The paper cites Collier et al. and states no hypotheses.
  The Lean statements assume finite centred moments `M_ℓ = E|ΔP_ℓ − E[ΔP_ℓ]|^{2+δ}` on the levels
  used and Lyapunov's condition `∑_{ℓ ≤ L_k} M_ℓ N_{k,ℓ}^{−1−δ}/σ_k^{2+δ} → 0`, or a uniform bound
  `M_ℓ ≤ K V_ℓ^{1+δ/2}` with `min_ℓ N_{k,ℓ} → ∞`. Some such hypothesis is needed: with a growing
  `L` the paper's "each `Y_ℓ` is asymptotically normal, and therefore so is `Y`" fails (module
  docstring: `ΔP_ℓ = ±2^{ℓ/2}` with probability `2^{−ℓ−1}` each, `L_k = k`, `N_{k,k} = k + 1`,
  `N_{k,ℓ} = (k + 1)³`; the normalised error tends to `0`). The confidence intervals use the exact
  standard deviation `σ_k`; intervals built from estimated variances are not formalised. Around
  `E[P]` the bias must be `o(σ_k)`, or split from the tolerance as Collier et al. do.
* **QMC in one dimension (G15 §1, §2.7, §3.5; `QMC1D.lean`, round 12).** Only `d = 1`, integrands of
  bounded variation on `[0, 1]`, and the rank-1 lattice `{i/N}` (one point per cell); the shift
  modulo `1` is `Int.fract` on `ℝ`, linked to the torus version of `RandomShiftQMC.lean` by
  `rank1Lattice_torus_replicates`. The MLQMC complexity takes level variances `≤ (V(f_ℓ)/N_ℓ)²`
  with `V(f_ℓ) = O(2^{−bℓ})`: cost `O(ε^{−max(1, g/a)})` when `b > g` (or `a ≤ b`, `a < g`) and
  `O(ε^{−max(1 + (g−b)/a, g/a)})` when `b < g`; the boundary `b = g ≤ a`
  (`O(ε⁻¹|log ε|^{3/2})`) and lower bounds are not formalised. The paper's "under certain
  conditions … `p < 2`" gives no conditions; in this model `g < 2a` and `g < a + b` suffice
  (`mlqmc_complexity_lt_two`).
* **The consistency check with empirical variances (G15 §3.3, p. 22; `ConsistencyCheck.lean`,
  round 13).** The `0.3%` (`P(|Z| > 3) ≈ 0.0027`) needs `a − b + c` normal and the variances
  exact. With empirical variances it holds only in the limit of many samples: the failure
  probability is at most `P(|Z| ≥ 3) + η` for all large sample sizes, at any rates
  (`consistency_check_empirical`), so eventually `< 0.003` (`consistency_check_empirical_lt`),
  and the limit is attained (`consistency_check_empirical_sharp`). For a fixed sample size it can
  fail: with `P^f = 0` on both levels and `P^c_ℓ ~ N(0, 1)` the failure probability is `0.280` for
  `N = 2` and exceeds `0.003` for every `N ≤ 274`. The paper's levels `ℓ − 1, ℓ` are `ℓ, ℓ + 1`
  in Lean; no hypothesis on `P^f_{ℓ+1}` and no non-degeneracy is needed.
* **Nested simulation with a kink and inner time steps (G15 §9.2, p. 60; `NestedKinkSde.lean`,
  round 13).** Only `f(x) = a₀ + a₁x + c·max(x − k, 0)` (one kink; several kinks add up if each
  has a small-ball bound; curved pieces are not covered). The hypotheses are this
  formalisation's: a small ball for the exact conditional mean near the kink, bounded centred
  conditional fourth moments, weak order 1 uniformly in the outer sample and strong order 1/4 in
  mean square of the inner discretisation (Euler–Maruyama suffices). Then `α = 1`, `β = 3/2` and
  the cost is `O(ε^{−5/2})`, as the paper says. Its MIMC claim `β₁ = β₂ = 1.5` (hence `O(ε⁻²)`)
  is false: in an explicit example meeting every hypothesis (`kinkInnerApprox_hypotheses`), the
  weak error shifts the kink seen by the two inner approximations by `O(2^{−ℓ₂})`, which matters
  on the straddling event of probability `O(2^{−ℓ₁/2})`, and `V[Y_ℓ] ≥ 2^{−(2ℓ₂ + j + 17)}` at
  `ℓ = (2j + 1, ℓ₂ + 1)` (`kinkMimc_variance_ge`), so no rates with `2β₁ + β₂ > 3` hold
  (`nested_mimc_kink_rates_false`).
* **Confidence intervals with estimated variances (G15 §2.1, p. 8; `MLMCConfidenceEstimated.lean`,
  round 14).** `σ̂_k² = ∑_ℓ s_ℓ²/N_{k,ℓ}` with the biased empirical variances of the samples the
  estimator uses. For a growing number of levels the consistency of `σ̂_k` assumes a uniform
  kurtosis bound (with `E|s_N² − V| ≤ (√((κ−1)/N) + 1/N) V`, an `L¹` analogue of the paper's
  §3.3 heuristic for the standard deviation of `s_N²`, which itself needs a larger `O(1/N)` term).
  `L_k` and `N_{k,ℓ}` are deterministic: the test `zσ̂_k ≤ θ TOL_k` is evaluated at a fixed `k`,
  not at the random stopping index of the adaptive algorithm, which is not formalised.
* **The MIMC rates for a piecewise linear `f` (G15 §9.2, p. 60; `NestedMimcKink.lean`, round
  14).** The corrected rates are `V = O(2^{−ℓ₁−ℓ₂})` (strong order `½` in mean square; sharp along
  `ℓ₁ = 2ℓ₂`) and `|E[Y]| = O(2^{−ℓ₁/2−ℓ₂})` (first-order strong convergence; the smooth-case
  `O(2^{−ℓ₁−ℓ₂})` fails numerically when the weak error depends on the outer sample). With
  `β = γ = (1, 1)` Theorem 2 gives `O(ε⁻²|log ε|⁴)`, an upper bound; whether another index set
  reaches `O(ε⁻²)` is not decided.
* **The lookup-table asymptotics (HG25 §3.4, p. 7; `LUTAsymptotics.lean`, round 14).** Method 3:
  the values on each dyadic interval are the least-squares affine fit (19) to the LUT values
  (15), with `j = 0` joined to the group `{0, 1}`; the MSE converges to `C = 2∑_k E_k > 0`
  (assuming `f(1 − u) = −f(u)` and strong concavity on one dyadic interval, as for `Φ⁻¹`). The
  paper's "when `d` increases by 1 the MSE is reduced only in the interval closest to 0" is only
  asymptotic: the error on every dyadic interval decreases with `d` (exactly, for quadratic
  pieces, by `f′(c_k)²|D_k|4^{−d}/12`). Method 1: under block-wise bounds on the increments of
  `f` (which `Φ⁻¹` satisfies) the MSE is of order `2^{−d}/d`, so `log(MSE)/d → −log 2`; the exact
  halving ratio and method 2 are not formalised.
* **Super-linear drift (G15 §5.6, p. 44; `EulerSuperlinear.lean`, round 15).** The paper cites
  Hutzenthaler, Jentzen and Kloeden for "numerical instability if a uniform timestep is used"; the
  Lean statements are their divergence theorem for the paper's example `dS = −S³dt + dW` only
  (`E|X_N|^p → ∞` for every `p > 0`, with Gaussian inputs independent within each `N`), and, for
  the tamed scheme, the second-moment bound `E X_N² ≤ x₀² + T` for `T ≤ 54N` (the condition is
  needed for this exact bound when `N = 1`; for larger `N` it only restricts the coarse levels). The moments of the exact solution and the general theorems are
  not formalised.
* **The MLQMC boundary case (G15 §2.7, §3.5; `MLQMCBoundary.lean`, round 15).** In the
  one-dimensional model of `QMC1D.lean`, `b = g ≤ a` gives cost `Θ(ε⁻¹|log ε|^{3/2})`: the upper
  bound by the Lagrange allocation, and lower bounds for every allocation and every `L`. The
  finest-level bound shows that `g < 2a` is necessary for the paper's `p < 2` in this model.
* **Optimal bit-widths (HG25 §6.1, p. 12; `BitWidthOptimum.lean`, round 16).** The paper says
  "we can see that the resulting function is convex which ensures the existence of an optimum",
  the function being the λ-function of Figure 3. Existence holds without convexity (continuity and
  coercivity of (34) in relaxed bit-widths). For other parameters than the paper's the λ-function
  need not be convex (numerical examples in the module docstring, not formalised); (34) itself is strictly convex in the
  bit-widths without additions, but not in general. Bit-widths are real, not integers.
* **The elliptic example (G15 §7.1; `EllipticFD.lean`, round 16).** The paper leaves the scheme and
  the computation of `P_ℓ` unspecified; the Lean reading is the standard flux-form central
  difference and the trapezoidal rule, with `h_ℓ = 2^{−(ℓ+1)}`. As noted before, the constant `K`
  must be random (`K = (50/3) Z²`).
* **Small corollaries (`GilesCorollaries.lean`, round 16).** Contracting SDEs with a fixed step
  only (the level-dependent steps of §10.1 need SDE strong convergence); the lookup-table streams
  for the method-1 tables only.
* **Path-dependent payoffs for GBM (`GBMPathDependent.lean`, round 17).** Table 5.2's Asian and
  lookback options are continuously monitored; the Lean options are monitored at `m` fixed dates
  `kT/m` that lie on every grid (level `j` has `m 2^j` steps), so the hierarchy starts at
  `ℓ₀ = log₂ m`.  The Euler–Maruyama weak order proved is `½`, not the paper's `1`; Theorem 1
  only needs `α ≥ ½ min(β, γ)`.  The `O(h_ℓ)` variance of §5.2, p. 38, concerns the maximum over
  all time steps of a level and does not contradict the `O(h²)` proved here for fixed dates.
* **SPDE stability (`SPDEStability.lean`, round 17).** The paper states no condition and cites
  Giles–Reisinger (2012), not in `docs/`; the condition `λ(1 + 2ρ²) ≤ 1`, `λ = k/h²`, is derived
  here (von Neumann analysis on `ℤ` and on periodic grids, not on the half line with `p(0) = 0`).
* **Drift-implicit methods (`DriftImplicit.lean`, round 17).** §5.6 only names the remedies; the
  Lean results are the elementary facts behind them, with additive noise, moments of order 2 and 4,
  and the integrating factor for a linear drift only (not the Heston treatment).
* **Brownian paths (`BrownianPaths.lean`, round 17).** Union grids are deterministic (the adaptive
  grids of §5.6 depend on the path); time reversal is proved for the finite-dimensional laws
  (`IsPreBrownianReal`), not for path continuity.
* **The digital option for GBM (`GBMDigital.lean`, round 18).** The rates proved are those the
  mean-square strong error gives (`h^{1/3}` for Euler–Maruyama, `h^{2/3}` for Milstein), not the
  paper's `O(h^{1/2})` and `O(h)`, which need `L^p` strong errors (round 20, below); the exponent is
  the best mean square gives (`digital_mismatch_exponent_sharp`). The kurtosis bounds use the raw
  fourth moment (the paper's definition is for zero-mean `X`). The law equality for the smoothed
  coarse payoff is for autonomous coefficients `a(S)`, `b(S)`.
* **Tau-leaping against the exact chain (`TauLeapingExact.lean`, round 18).** The exact chain is
  built by uniformisation for bounded propensities `λ ≤ Λ` and identified by its master equation;
  the weak rate is for bounded payoffs.  The pathwise SSA coupling of §8 is not formalised.
* **`Φ⁻¹` (`InverseNormal.lean`, round 18).** `normCDFInv` is defined on all of `ℝ` with a junk value
  outside `(0, 1)`; every statement about it restricts to `(0, 1)` or to a uniform variable.  The
  dyadic lower bound is proved for the cells `k ≥ 2` (the paper's claims need one such cell).
* **End-to-end instances (`EndToEndInstances.lean`, round 18).** GBM with refinement factor `M`
  uses `α = ½ log₂ M` from the strong error, not the paper's weak order `log₂ M`; §10.2's rounding
  is Mathlib's `round` (ties up) or truncation to a grid.
* **Jump processes (`JumpProcesses.lean`, round 19).** No Poisson or Lévy process is constructed:
  the Asian results take i.i.d. increments with the needed exponential moments on uniform steps (a
  discrete analogue of Table 6.3's Asian row; the target is the limit of the level means, not the
  continuously averaged price), and the jump-adapted results take any measurable jump data
  independent of the Brownian increments.  The thinning results are conditional on the candidates.
* **Estimator remarks (`EstimatorRemarks.lean`, round 19).** G2.1-36 is imprecise rather than wrong:
  with a growing number of levels the inference needs a Lindeberg-type condition, and the
  counterexample shows it can fail.  For the consistency check only `N = 1` and `N = 2` are proved;
  the failure probability above `0.003` for `N ≤ 274` is numerical.
* **SDE extensions (`SDEExtensions.lean`, round 19).** The time-reversed path is a Brownian motion
  in Mathlib's sense (`IsBrownianReal`: almost surely continuous paths); the several-kinks theorems
  need a small-ball bound at every kink.
* **Contracting levels (`ContractingLevels.lean`, round 19).** One dimension, Lipschitz payoffs, the
  target is the limit of the means of the discretised chains; the cost per sample grows like
  `ℓ 2^ℓ`, so the complexity is `O(ε^{−2−η})` for every `η > 0` (round 20: `O(ε⁻²|log ε|³)`,
  `contracting_levels_mlmc_log`).
* **Adaptive grids (`AdaptiveGrids.lean`, round 20).** Step sizes are multiples of a fixed base
  spacing `δ` (for `h_ℓ = 2^{−ℓ}H(Ŝ_n)`: `H` with values in `2^{−m₀}Tℕ`), so the union grid lies in a
  base grid and only i.i.d. base increments are needed; real-valued step sizes would need Brownian
  motion at stopping times.  Algorithm 3 is modelled with steps of at least one base interval and an
  unbounded loop (stopping at `T` is part of the rule).  The Poisson results have a constant rate.
* **Lattice rules in `d` dimensions (`LatticeRuleD.lean`, round 20).** The MLQMC theorems assume the
  decay of the dual-lattice sums for `N = 2^m` points (the existence of good generating vectors is
  not formalised); the generating vector may depend on `N`, and for `d ≥ 2` it must.  Parseval's
  identity on `𝕋^d` is re-proved, since Mathlib's `AddCircleMulti` is not in this project's build.
* **Theorem 1 with a polylogarithmic cost (`Theorem1Log.lean`, round 20).** An extension the paper
  does not state, needed for §10.1: condition iv) becomes `C_ℓ ≤ c₃(ℓ+1)^κ 2^{γℓ}` with `κ ≥ 0`
  (needed except in `giles_theorem1_log_of_lt`); Giles' `β > 0` is dropped.  The §10.1 corollary
  keeps the deviations of `ContractingLevels.lean`.
* **`L^p` strong errors for GBM (`GBMStrongLp.lean`, round 20).** The strong errors are proved at
  grid points, with explicit but loose constants (for `m = 2` at the paper's parameters a factor of
  about `2·10⁶` (EM) and `1.5·10⁹` (Milstein) above the exact ratio), so the digital exponents
  improve on `GBMDigital.lean` only asymptotically.  Every exponent below the paper's `½` and `1` is
  reached; the endpoints, the `log h` of Table 5.2 and the kurtosis upper bounds are not.  The
  payoff factors `10e^{−rT}` and `25e^{−rT}` are omitted.

### Corrections to the papers recorded elsewhere, collected

| Paper | Where | Printed | Correct | Lean |
|---|---|---|---|---|
| G15 | §1.3, p. 4 | `ε⁻²L²V₀C₀` | `ε⁻²(L+1)²V₀C₀` (levels `0, …, L`) | `optimal_cost_const_product` |
| G15 | §2.3, p. 11 | weights with `∑ w_ℓ 2^{−nαℓ} = 1` | `= 0` | `ml2r_weights` |
| G15 | §2.3, p. 12 | bias `O(2^{−αL²})`, exponent `√(|log₂ ε|/α)` | `O(2^{−αL(L+1)/2})`, `√(2|log₂ ε|/α)` | `ml2r_bias`, `ml2r_bias_le`, `ml2r_theorem_lt` |
| G15 | §2.4, pp. 13–14 | conditions labelled i), iii), ii), iv), v) | labels as in the Notes | hypothesis names follow the statement |
| G15 | §2.4, p. 15 | rectangles "optimal order" | only for `O(ε⁻²)` | `mimc_rect_lower_bounds` |
| G15 | §3.1, p. 21 | (3.1) gives variance `< ½ε²` | `≤ ½ε²` | `allocation_eq_3_1` |
| G15 | §3.3, p. 23 | "`p, q → 0` due to weak convergence" | needs `E[X²] → 0` | `consistency_mean` |
| G15 | §3.3, p. 22 | the check fails with probability `< 0.3%` | only as the sample sizes grow; `> 0.003` for every `N ≤ 274` in an example | `consistency_check_empirical`, `ConsistencyCheck.lean` |
| G15 | §5, p. 29 | `h_ℓ = h₀M^ℓ` | `h₀M^{−ℓ}` | `timestep_rate` |
| G15 | §5.2, p. 36 | coarse numerator `b√h_ℓ`; `Φ(…/(b√h_ℓ))`; digital constant `25` | `b ΔW_{N−2}`; `|b|` in the denominator; `10` as on p. 30 | `digital_smoothing_coarse`, `integral_digital_final_step` |
| G15 | §5.2, p. 38 | "`O(h_ℓ)` difference on average" | `O(h_ℓ^{1/2})` | — |
| G15 | §5.3, p. 39 | `b(Ŝ^c_n, c_n)` | `b(Ŝ^c_n, t_n)` | — |
| G15 | §6.1, p. 47 | "this introduces a Radon-Nikodym into the payoff evaluation" | "a Radon–Nikodym derivative" | — |
| G15 | §7.1, p. 49 | a constant `K` with `|P − P_ℓ| < K h_ℓ²` | impossible for the example (error `∝ Z²`); a random `K` with `E[K²] < ∞` | `elliptic_rates` (literal), `ApplicationExtras.lean` (random `K`) |
| G15 | §5.6, p. 44 | "a change or variables" | "a change of variables" | — |
| G15 | §7.3, p. 54 | `√h Z_n` | `√k Z_n` | `ApplicationExtras.lean`, `spdeStep_eq_milstein` |
| G15 | §9.1, p. 58; §9.2, p. 60 | `−1/(4N_ℓ)` | `−1/(8N_ℓ)` | `antithetic_quadratic`, `NestedRates.lean` |
| G15 | §9.2, p. 59 | `O(ε⁻²(log ε)⁻²)` | `O(ε⁻²(log ε)²)` | `nested_complexity` |
| G15 | §9.2, p. 60 | MIMC with a kink: `β₁ = β₂ = 1.5`, cost `O(ε⁻²)` | false: no `β₁, β₂` with `2β₁ + β₂ > 3` (counterexample); the isotropic rates `β₁ = β₂ = 1` hold and are sharp along `ℓ₁ = 2ℓ₂` | `nested_mimc_kink_rates_false`, `nested_mimc_kink_variance_rate` |
| G15 | §10.1, p. 61 | decay exponential in `N_ℓ − N_{ℓ−1}` | in `N_{ℓ−1}` | `variance_levels_le`, `markov_linear_levels` |
| G15 | §10.2, p. 62 | `U_n = (I_n + ½)/I_max` | `(I_n + ½)/(I_max + 1)` (the printed `U_n` exceeds `1` for `I_n = I_max`) | — |
| HG25 | (21) | `E[δx²] = 4^{e−d−1}` | `≤` | `integral_sq_roundError_le` |
| HG25 | (25) | `2 ∑_{i≠j} Cov` | correct over unordered pairs (as (27) reads it); over ordered pairs no factor 2 | `variance_sum_eq` |
| HG25 | (27) | derived under perfect correlation | holds for every joint law | `variance_linearised_corr` |
| HG25 | (28) | factor `1/12` on the MSE term | no factor `1/12` | `variance_extended_indep` |
| HG25 | Fig. 3, 5 captions | `√(Ṽ/V)` | `√(V^Δ/V)` | `HaasGilesRemarks.lean` |
| HG25 | §3, p. 4 | "the inverse normal CDF `Φ`" | `Φ⁻¹` (`Φ` is the CDF, as in §3.1) | `normCDF`, `normCDFInv` |
| HG25 | §3, p. 4 | "The first and the third methods … PWC on uniform intervals … The second … PWL on dyadic intervals" | the numbering does not match §3.1–§3.4, where method 3 is the dyadic one | `LUTLimits.lean`, `LUTAsymptotics.lean` (follow §3.1–§3.4) |
| HG25 | §3.4, p. 7 | dyadic tables: "the MSE is reduced only in the interval closest to 0" | only asymptotically; the error on every dyadic interval decreases with `d` | `dyadic_groupMSE_eq`, `groupMSE_odd_quadratic` |
| HG25 | §6.1, p. 12 | cost factor `< 1` ⇒ nested framework cheaper | true for (34); for (32) e.g. `ρ²(1 + ρ²) < 1` | `nestedCost_lt_of_costFactor_le`, `exists_costFactor_lt_one_nestedCost_gt` |
| HG25 | §6.1, p. 12 | "the resulting function is convex which ensures the existence of an optimum" | the λ-function need not be convex for other parameters (numerically); the optimum exists anyway | `exists_isMinOn_bitLevelCost_of_nonneg` |
| HG25 | §6.2, p. 13 | "first round down the solution to `d*_{i,ℓ} = d_{i,ℓ}`" | `d*_{i,ℓ} = ⌊d_{i,ℓ}⌋` | `greedy_rounding_feasible` |
| HG25 | §6.3, p. 14 | fixed-precision rounding error `O(h⁻¹2^{e−d})` | worst case; root mean square `Θ(h^{−1/2}2^{e−d})` under (22) | `integral_sq_perturbed_path_sub_bounds` |

"—" marks typos that no Lean statement depends on.

## Out of scope (as in PLAN.md)

The rate conditions (i)–(iv) are hypotheses, exactly as in the papers; proving them for
Euler–Maruyama or Milstein for a general SDE needs Itô calculus.  For geometric Brownian motion,
whose solution is explicit, they are proved (`GBMEulerMaruyama.lean`: strong error `O(h)` in mean
square, `α = ½`, `β = 1`; `GBMMilstein.lean`: strong error `O(h²)` in mean square, `α = 1`,
`β = 2`), and Theorem 1 holds with no assumed rate.
