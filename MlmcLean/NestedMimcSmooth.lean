import MlmcLean.NestedMimcKink

/-!
# Nested MIMC with a smooth payoff: the rates on `ℕ²` and the cost `O(ε⁻²)` (Giles 2015, §9.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §9.2 "MIMC
treatment" (pp. 59–60) of the author's version.

§9.2, p. 60: "Combining these results we obtain `(Δg_{1,ℓ₂} − Δg_{2,ℓ₂})² −
(Δg_{1,ℓ₂−1} − Δg_{2,ℓ₂−1})² = O(2^{−ℓ₁−ℓ₂})` and therefore `E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` and
`V_ℓ = O(2^{−2ℓ₁−2ℓ₂})` with a cost per sample which is `O(2^{ℓ₁+ℓ₂})`. In Theorem 2 this
corresponds to `α₁ = α₂ = 1, β₁ = β₂ = 2`, and `γ₁ = γ₂ = 1`, so the overall complexity is
`O(ε⁻²)`."

`MlmcLean/NestedRates.lean` proves the two rates for `ℓ₁, ℓ₂ ≥ 1` (`nested_mimc_variance_rate`,
`nested_mimc_mean_rate`), and `nested_mimc_complexity` (`MlmcLean/NestedSimulation.lean`) only
evaluates the bound of Theorem 2 for these exponents.  This file applies Theorem 2 to the nested
MIMC estimator itself.  Level `ℓ = (ℓ₁, ℓ₂)` uses `2^{ℓ₁}` inner samples of the level-`ℓ₂`
approximation `g_{ℓ₂}` of the inner quantity, and `Y_ℓ` is the correction `nestedMimcDelta`:

* **The boundary levels** (Theorem 2 needs the rates on all of `ℕ²`).  At `(0, 0)`,
  `Y = f(g₀(Z, W))` (`nested_mimc_smooth_origin`); at `(ℓ₁, 0)`, `ℓ₁ ≥ 1`, the §9.1 antithetic
  correction of `g₀` (`nested_variance_rate`); at `(0, ℓ₂)`, `ℓ₂ ≥ 1`, one inner sample and
  `Y = f(g_{ℓ₂}(Z, W)) − f(g_{ℓ₂−1}(Z, W))`, which is `O(2^{−ℓ₂})` in `L²` by the strong
  convergence in `L⁴` (`nested_mimc_smooth_column`).
* **The rates on `ℕ²`** (`nested_mimc_smooth_variance_rate`, `nested_mimc_smooth_mean_rate`):
  every `Y_ℓ` is square-integrable, `4^{ℓ₁+ℓ₂} E[Y_ℓ²] ≤ B` and `2^{ℓ₁+ℓ₂} |E[Y_ℓ]| ≤ (B + 1)/2` for
  every `ℓ ∈ ℕ²`, with an explicit `B`.
* **The bias** (`nested_mimc_smooth_bias`): `|E[P_ℓ] − E_Z[f(E_W[g(Z, W)])]| = O(2^{−ℓ₁} + 2^{−ℓ₂})`
  for the exact inner quantity `g`, so hypothesis (i) of Theorem 2 holds.
* **The cost** (`nested_mimc_smooth_complexity`): Theorem 2 (`giles_theorem2_boundary_indexSet`,
  which allows `α_d = ½β_d`) with `α = (1, 1)`, `β = (2, 2)`, `γ = (1, 1)`, `η = −1`, gives mean
  square error `< ε²` at expected cost `O(ε⁻²)` on the simplex `{ℓ : ℓ₁ + ℓ₂ ≤ 2Λ}`.

Hypotheses (this formalisation's; Itô calculus and the Milstein scheme are not in Mathlib, so the
orders of the inner discretisation are hypotheses), those of `nested_mimc_variance_rate`: `f′` is
`K`-Lipschitz and `f″` is `L`-Lipschitz (the paper's "twice differentiable" does not control the
Taylor remainder), `E[g_ℓ(Z, W)⁴] ≤ m₄`, first order strong convergence in `L⁴`
(`(2^ℓ)⁴ E[(g_{ℓ+1} − g_ℓ)⁴] ≤ cₛ`), and first order weak convergence uniformly in the outer sample
(of the level differences for the rates; to the exact `g`,
`2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w`, for the complexity).  `L⁴` rather than `L²` strong
convergence, weak convergence uniformly in `z` rather than on average, and fourth moments uniform
in `ℓ` are stronger than the paper's "first order weak and strong convergence"; the docstring of
`nested_mimc_smooth_variance_rate` says why they are needed.  Nothing is assumed about the exact
`g`: `E_W[g(z, W)]` is the Bochner integral, identified with `lim_ℓ E_W[g_ℓ(z, W)]` by the weak
convergence.  The cost per sample `O(2^{ℓ₁+ℓ₂})` is a hypothesis on the cost model.
-/

open MeasureTheory ProbabilityTheory Finset Filter

namespace MLMC

section Rates

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **The level `(0, 0)`** (Giles 2015, §9.2: one inner sample of the coarsest approximation):
if `f′` is `K`-Lipschitz and `E[g(Z, W)⁴] ≤ m₄`, then `P₀ = f(g(Z, W⁽⁰⁾))` is square-integrable
and `E[P₀²] ≤ 2 f(0)² + 16 |f′(0)|⁴ + (2 + K²) m₄`, from
`f(A)² ≤ 2 f(0)² + 2 (f(A) − f(0))²` and `sq_sub_le_of_lipschitz_deriv`. -/
lemma nested_mimc_smooth_origin {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hK : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ : ℝ}
    (hm₄ : ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄) :
    MemLp (nestedP f g 0) 2 (nestedLaw ν ρ) ∧
      ∫ p, nestedP f g 0 p ^ 2 ∂(nestedLaw ν ρ) ≤
        2 * f 0 ^ 2 + 16 * |f' 0| ^ 4 + (2 + K ^ 2) * m₄ := by
  have hP := memLp_nestedP ν ρ hf hK hg hg4 0
  refine ⟨hP, ?_⟩
  set A : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => innerMean g (2 ^ 0) p.1 p.2 with hAdef
  have hA4 : Integrable (fun p => A p ^ 4) (nestedLaw ν ρ) :=
    integrable_innerMean_pow_four ν ρ hg hg4 (by positivity)
  have hA4le : ∫ p, A p ^ 4 ∂(nestedLaw ν ρ) ≤ m₄ :=
    (integral_innerMean_pow_four_le ν ρ hg hg4 (by positivity)).trans hm₄
  have hpt : ∀ p, nestedP f g 0 p ^ 2 ≤
      2 * f 0 ^ 2 + 16 * |f' 0| ^ 4 + (2 + K ^ 2) * A p ^ 4 := fun p => by
    have h := sq_sub_le_of_lipschitz_deriv hf hK (A p) 0 one_pos
    show f (A p) ^ 2 ≤ _
    nlinarith [sq_nonneg (f (A p) - 2 * f 0)]
  have i1 : Integrable (fun p => 2 * f 0 ^ 2 + 16 * |f' 0| ^ 4 + (2 + K ^ 2) * A p ^ 4)
      (nestedLaw ν ρ) := (integrable_const _).add (hA4.const_mul _)
  calc ∫ p, nestedP f g 0 p ^ 2 ∂(nestedLaw ν ρ)
      ≤ ∫ p, (2 * f 0 ^ 2 + 16 * |f' 0| ^ 4 + (2 + K ^ 2) * A p ^ 4) ∂(nestedLaw ν ρ) :=
        integral_mono hP.integrable_sq i1 hpt
    _ = 2 * f 0 ^ 2 + 16 * |f' 0| ^ 4 + (2 + K ^ 2) * ∫ p, A p ^ 4 ∂(nestedLaw ν ρ) := by
        rw [integral_add (integrable_const _) (hA4.const_mul _), integral_const,
          integral_const_mul, probReal_univ, one_smul]
    _ ≤ _ := by gcongr

/-- **The boundary column `(0, ℓ₂ + 1)`** (Giles 2015, §9.2: one inner sample, the inner
discretisation refined once).  Here `Y = f(g_{ℓ₂+1}(Z, W⁽⁰⁾)) − f(g_{ℓ₂}(Z, W⁽⁰⁾))`.  If `f′` is
`K`-Lipschitz, `E[g_ℓ(Z, W)⁴] ≤ m₄` and `(2^ℓ)⁴ E[(g_{ℓ+1} − g_ℓ)⁴] ≤ cₛ` (first order strong
convergence in `L⁴`), then `Y` is square-integrable and
`(2^{ℓ₂})² E[Y²] ≤ 8(|f′(0)|⁴ + K⁴ m₄) + (1 + K²/2) cₛ` (`sq_sub_le_of_lipschitz_deriv` with
`s = 4^{ℓ₂}`, as in `nested_sde_variance_rate`). -/
lemma nested_mimc_smooth_column {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hK : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ cₛ : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ) (b : ℕ) :
    MemLp (nestedMimcDelta f gh 0 (b + 1)) 2 (nestedLaw ν ρ) ∧
      ((2 : ℝ) ^ b) ^ 2 * ∫ p, nestedMimcDelta f gh 0 (b + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2) * cₛ := by
  set A : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => innerMean (gh (b + 1)) (2 ^ 0) p.1 p.2 with hAdef
  set B : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => innerMean (gh b) (2 ^ 0) p.1 p.2 with hBdef
  have hY : ∀ p, nestedMimcDelta f gh 0 (b + 1) p = f (A p) - f (B p) := fun p => rfl
  have hY2 : MemLp (nestedMimcDelta f gh 0 (b + 1)) 2 (nestedLaw ν ρ) :=
    (memLp_nestedP ν ρ hf hK (hgh (b + 1)) (hgh4 (b + 1)) 0).sub
      (memLp_nestedP ν ρ hf hK (hgh b) (hgh4 b) 0)
  refine ⟨hY2, ?_⟩
  -- the fourth moments of `B` and of `A − B`
  have hdiff : Measurable (Function.uncurry fun z v => gh (b + 1) z v - gh b z v) :=
    (hgh (b + 1)).sub (hgh b)
  have hdiff4 : Integrable (fun p : 𝒵 × 𝒲 => (gh (b + 1) p.1 p.2 - gh b p.1 p.2) ^ 4)
      (ν.prod ρ) := by
    refine (((hgh4 (b + 1)).add (hgh4 b)).const_mul 8).mono'
      ((hdiff.pow_const 4).aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact sub_pow_four_le _ _
  have hB4 : Integrable (fun p => B p ^ 4) (nestedLaw ν ρ) :=
    integrable_innerMean_pow_four ν ρ (hgh b) (hgh4 b) (by positivity)
  have hB4le : ∫ p, B p ^ 4 ∂(nestedLaw ν ρ) ≤ m₄ :=
    (integral_innerMean_pow_four_le ν ρ (hgh b) (hgh4 b) (by positivity)).trans (hm₄ b)
  have hAB : ∀ p, A p - B p =
      innerMean (fun z v => gh (b + 1) z v - gh b z v) (2 ^ 0) p.1 p.2 :=
    fun p => innerMean_sub _ _ _ p.1 p.2
  have hAB4 : Integrable (fun p => (A p - B p) ^ 4) (nestedLaw ν ρ) := by
    simp only [hAB]
    exact integrable_innerMean_pow_four ν ρ hdiff hdiff4 (by positivity)
  have hAB4le : ((2 : ℝ) ^ b) ^ 4 * ∫ p, (A p - B p) ^ 4 ∂(nestedLaw ν ρ) ≤ cₛ := by
    simp only [hAB]
    refine le_trans ?_ (hs b)
    gcongr
    exact integral_innerMean_pow_four_le ν ρ hdiff hdiff4 (by positivity)
  -- `E[Y²] ≤ 8(|f′(0)|⁴ + K⁴ m₄)/s + (s + K²/2) E[(A − B)⁴]`, `s = 4^b`
  set s : ℝ := ((2 : ℝ) ^ b) ^ 2 with hs_def
  have hs0 : 0 < s := by positivity
  have hs1 : (1 : ℝ) ≤ s := by
    rw [hs_def]
    exact one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hYpt : ∀ p, nestedMimcDelta f gh 0 (b + 1) p ^ 2 ≤
      8 * (|f' 0| ^ 4 + K ^ 4 * B p ^ 4) / s + (s + K ^ 2 / 2) * (A p - B p) ^ 4 := fun p => by
    rw [hY p]
    exact sq_sub_le_of_lipschitz_deriv hf hK (A p) (B p) hs0
  have iC : Integrable (fun p => |f' 0| ^ 4 + K ^ 4 * B p ^ 4) (nestedLaw ν ρ) :=
    (integrable_const _).add (hB4.const_mul _)
  have i1 : Integrable (fun p => 8 * (|f' 0| ^ 4 + K ^ 4 * B p ^ 4) / s) (nestedLaw ν ρ) :=
    (iC.const_mul 8).div_const s
  have i2 : Integrable (fun p => (s + K ^ 2 / 2) * (A p - B p) ^ 4) (nestedLaw ν ρ) :=
    hAB4.const_mul _
  have iB : Integrable (fun p => K ^ 4 * B p ^ 4) (nestedLaw ν ρ) := hB4.const_mul _
  have hcs : 0 ≤ cₛ := le_trans (by positivity) hAB4le
  have h4 : ∫ p, (A p - B p) ^ 4 ∂(nestedLaw ν ρ) ≤ cₛ / ((2 : ℝ) ^ b) ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hYle : ∫ p, nestedMimcDelta f gh 0 (b + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
      8 * (|f' 0| ^ 4 + K ^ 4 * m₄) / s + (s + K ^ 2 / 2) * (cₛ / ((2 : ℝ) ^ b) ^ 4) := by
    have i12 : Integrable (fun p => 8 * (|f' 0| ^ 4 + K ^ 4 * B p ^ 4) / s +
        (s + K ^ 2 / 2) * (A p - B p) ^ 4) (nestedLaw ν ρ) := i1.add i2
    refine (integral_mono hY2.integrable_sq i12 hYpt).trans ?_
    rw [integral_add i1 i2, integral_div, integral_const_mul, integral_add (integrable_const _) iB,
      integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul]
    gcongr
  have e : s * (8 * (|f' 0| ^ 4 + K ^ 4 * m₄) / s + (s + K ^ 2 / 2) * (cₛ / ((2 : ℝ) ^ b) ^ 4))
      = 8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2 / s) * cₛ := by
    rw [hs_def]
    field_simp
  have hK2 : K ^ 2 / 2 / s ≤ K ^ 2 / 2 := div_le_self (by positivity) hs1
  calc s * ∫ p, nestedMimcDelta f gh 0 (b + 1) p ^ 2 ∂(nestedLaw ν ρ)
      ≤ s * (8 * (|f' 0| ^ 4 + K ^ 4 * m₄) / s +
          (s + K ^ 2 / 2) * (cₛ / ((2 : ℝ) ^ b) ^ 4)) :=
        mul_le_mul_of_nonneg_left hYle hs0.le
    _ = 8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2 / s) * cₛ := e
    _ ≤ 8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2) * cₛ := by gcongr

/-- **`V_ℓ = O(2^{−2ℓ₁−2ℓ₂})` on all of `ℕ²`** (Giles 2015, §9.2, p. 60: "and therefore
`E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` and `V_ℓ = O(2^{−2ℓ₁−2ℓ₂})` with a cost per sample which is
`O(2^{ℓ₁+ℓ₂})`. In Theorem 2 this corresponds to `α₁ = α₂ = 1, β₁ = β₂ = 2`").  Level
`ℓ = (ℓ₁, ℓ₂)` uses `2^{ℓ₁}` inner samples of the level-`ℓ₂` approximation `g_{ℓ₂}`, and `Y_ℓ` is
`nestedMimcDelta` (the paper's six-term correction for `ℓ₁, ℓ₂ > 0`; on the boundary `ℓ₂ = 0` the
§9.1 correction of `g₀`, on `ℓ₁ = 0` the difference `f(g_{ℓ₂}) − f(g_{ℓ₂−1})` with one inner
sample).  Hypotheses (this formalisation's, as in `nested_mimc_variance_rate`; the orders of the
time discretisation are hypotheses because Itô calculus is not in Mathlib): `f′` (with derivative
`f″`) is `K`-Lipschitz and `f″` is `L`-Lipschitz (the paper's "twice differentiable" does not
control the Taylor remainder); `E[g_ℓ(Z, W)⁴] ≤ m₄`; first order strong convergence in `L⁴`,
`(2^ℓ)⁴ E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))⁴] ≤ cₛ`; first order weak convergence of the level
differences uniformly in the outer sample, `2^ℓ |E_W[g_{ℓ+1}(z, W) − g_ℓ(z, W)]| ≤ c_w` for
`ν`-a.e. `z`.  Three of these are stronger than the paper's Milstein assumptions ("first order
weak and strong convergence", p. 59; strong convergence is conventionally in `L²`, weak
convergence a statement about expectations): strong convergence in `L⁴` rather than `L²`, because
`f′(g_ℓ)` is unbounded for a merely Lipschitz `f′` (as explained in `nested_sde_variance_rate`);
weak convergence uniformly in `z` rather than on average, because the conditional mean
`μ = E_W[g_{ℓ₂+1}(z, W) − g_{ℓ₂}(z, W)]` enters pathwise, through the re-centring term
`(L/8) δ² |μ|` of `abs_mimc_antithetic_le_of_deriv2` (as explained in
`nested_mimc_variance_rate`); and fourth moments bounded uniformly in `ℓ`, which the paper's `O(·)`
leaves implicit.  Then every `Y_ℓ`, `ℓ ∈ ℕ²`, is square-integrable and
`4^{ℓ₁+ℓ₂} E[Y_ℓ²] ≤ 2 f(0)² + 48 |f′(0)|⁴ + (2 + 3375 K² + 32 K⁴ + 336 L² c_w²) m₄ +
(4 + 434 K²) cₛ`, a bound on the second moment and hence on `V_ℓ`: the sum of the bounds of
`nested_mimc_smooth_origin` at `(0, 0)`, `nested_variance_rate` at `(ℓ₁, 0)`,
`nested_mimc_smooth_column` at `(0, ℓ₂)` and `nested_mimc_variance_rate` at `ℓ₁, ℓ₂ ≥ 1`. -/
theorem nested_mimc_smooth_variance_rate {f f' f'' : ℝ → ℝ} {K L : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hK : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x))
    (hL : ∀ x y, x ≤ y → |f'' y - f'' x| ≤ L * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ cₛ c_w : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ)
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, (gh (ℓ + 1) z v - gh ℓ z v) ∂ρ| ≤ c_w)
    (ℓ₁ ℓ₂ : ℕ) :
    MemLp (nestedMimcDelta f gh ℓ₁ ℓ₂) 2 (nestedLaw ν ρ) ∧
      ((2 : ℝ) ^ (ℓ₁ + ℓ₂)) ^ 2 * ∫ p, nestedMimcDelta f gh ℓ₁ ℓ₂ p ^ 2 ∂(nestedLaw ν ρ) ≤
        2 * f 0 ^ 2 + 48 * |f' 0| ^ 4 +
          (2 + 3375 * K ^ 2 + 32 * K ^ 4 + 336 * L ^ 2 * c_w ^ 2) * m₄ +
          (4 + 434 * K ^ 2) * cₛ := by
  have hm0 : 0 ≤ m₄ := (integral_nonneg fun p => by positivity).trans (hm₄ 0)
  have hc0 : 0 ≤ cₛ :=
    le_trans (mul_nonneg (by positivity) (integral_nonneg fun p => by positivity)) (hs 0)
  have n1 : 0 ≤ f 0 ^ 2 := sq_nonneg _
  have n2 : 0 ≤ |f' 0| ^ 4 := by positivity
  have n3 : 0 ≤ K ^ 2 * m₄ := by positivity
  have n4 : 0 ≤ K ^ 4 * m₄ := by positivity
  have n5 : 0 ≤ L ^ 2 * c_w ^ 2 * m₄ := by positivity
  have n6 : 0 ≤ K ^ 2 * cₛ := by positivity
  rcases ℓ₁ with _ | a <;> rcases ℓ₂ with _ | b
  · -- `(0, 0)`: `Y = P₀`
    obtain ⟨h1, h2⟩ := nested_mimc_smooth_origin ν ρ hf hK (hgh 0) (hgh4 0) (hm₄ 0)
    have e : nestedMimcDelta f gh 0 0 = nestedP f (gh 0) 0 := rfl
    rw [e]
    refine ⟨h1, ?_⟩
    rw [pow_zero, one_pow, one_mul]
    nlinarith
  · -- `(0, b + 1)`: one inner sample
    obtain ⟨h1, h2⟩ := nested_mimc_smooth_column ν ρ hf hK hgh hgh4 hm₄ hs b
    refine ⟨h1, ?_⟩
    have e : ((2 : ℝ) ^ (0 + (b + 1))) ^ 2 = 4 * ((2 : ℝ) ^ b) ^ 2 := by
      rw [zero_add, pow_succ]
      ring
    rw [e, mul_assoc]
    nlinarith
  · -- `(a + 1, 0)`: the §9.1 correction of `g₀`
    obtain ⟨h1, h2⟩ := nested_variance_rate ν ρ hf hK (hgh 0) (hgh4 0) a
    have e : nestedMimcDelta f gh (a + 1) 0 = nestedDelta f (gh 0) (a + 1) := rfl
    rw [e]
    refine ⟨h1, ?_⟩
    have e2 : ((2 : ℝ) ^ (a + 1 + 0)) ^ 2 = 4 * ((2 : ℝ) ^ a) ^ 2 := by
      rw [add_zero, pow_succ]
      ring
    have h3 : (K / 8) ^ 2 * (224 * ∫ p, gh 0 p.1 p.2 ^ 4 ∂(ν.prod ρ)) ≤
        (K / 8) ^ 2 * (224 * m₄) := by
      gcongr
      exact hm₄ 0
    rw [e2, mul_assoc]
    nlinarith
  · -- `(a + 1, b + 1)`: `nested_mimc_variance_rate`
    obtain ⟨h1, h2⟩ := nested_mimc_variance_rate ν ρ hf hf' hK hL hgh hgh4 hm₄ hs hw a b
    refine ⟨h1, ?_⟩
    have e : ((2 : ℝ) ^ (a + 1 + (b + 1))) ^ 2 = 16 * ((2 : ℝ) ^ (a + b)) ^ 2 := by
      rw [show a + 1 + (b + 1) = a + b + 2 by ring, pow_add]
      ring
    rw [e, mul_assoc]
    nlinarith

/-- **`E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` on all of `ℕ²`** (Giles 2015, §9.2, p. 60: "and therefore
`E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` … In Theorem 2 this corresponds to `α₁ = α₂ = 1`").  Under the
hypotheses of `nested_mimc_smooth_variance_rate`, with `B` its bound, every `Y_ℓ` is integrable
(so `E[Y_ℓ]` is a genuine Bochner integral) and `2^{ℓ₁+ℓ₂} |E[Y_ℓ]| ≤ (B + 1)/2` for every
`ℓ ∈ ℕ²`, the boundary included (`Y_ℓ ∈ L²` by `nested_mimc_smooth_variance_rate`, then
`mul_abs_integral_le_of_memLp`). -/
theorem nested_mimc_smooth_mean_rate {f f' f'' : ℝ → ℝ} {K L : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hK : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x))
    (hL : ∀ x y, x ≤ y → |f'' y - f'' x| ≤ L * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ cₛ c_w : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ)
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, (gh (ℓ + 1) z v - gh ℓ z v) ∂ρ| ≤ c_w)
    (ℓ₁ ℓ₂ : ℕ) :
    Integrable (nestedMimcDelta f gh ℓ₁ ℓ₂) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ (ℓ₁ + ℓ₂) * |∫ p, nestedMimcDelta f gh ℓ₁ ℓ₂ p ∂(nestedLaw ν ρ)| ≤
        (2 * f 0 ^ 2 + 48 * |f' 0| ^ 4 +
            (2 + 3375 * K ^ 2 + 32 * K ^ 4 + 336 * L ^ 2 * c_w ^ 2) * m₄ +
            (4 + 434 * K ^ 2) * cₛ + 1) / 2 := by
  obtain ⟨hY2, hV⟩ := nested_mimc_smooth_variance_rate ν ρ hf hf' hK hL hgh hgh4 hm₄ hs hw ℓ₁ ℓ₂
  refine ⟨hY2.integrable one_le_two, (mul_abs_integral_le_of_memLp hY2
    (by positivity : (0 : ℝ) < 2 ^ (ℓ₁ + ℓ₂))).trans ?_⟩
  gcongr

/-- **Weak convergence to `g` gives weak convergence of the level differences** (Giles 2015, §9.2,
the first order weak convergence of the inner discretisation): if
`2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w` for every `ℓ` and `ν`-a.e. `z`, and
`E[g_ℓ(Z, W)⁴] < ∞`, then `2^ℓ |E_W[g_{ℓ+1}(z, W) − g_ℓ(z, W)]| ≤ (3/2) c_w` for `ν`-a.e. `z`. -/
lemma weak_levelDiff_of_weak {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ))
    {g : 𝒵 → 𝒲 → ℝ} {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w) (ℓ : ℕ) :
    ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, (gh (ℓ + 1) z v - gh ℓ z v) ∂ρ| ≤ 3 / 2 * c_w := by
  have hi : ∀ j, ∀ᵐ z ∂ν, Integrable (gh j z) ρ := fun j =>
    (fourth_moment_fibers ν ρ (hgh4 j)).1.mono fun z hz => by
      simpa using integrable_pow_of_pow_four (hgh j).of_uncurry_left hz (k := 1) (by norm_num)
  filter_upwards [hw ℓ, hw (ℓ + 1), hi ℓ, hi (ℓ + 1)] with z h0 h1 i0 i1
  rw [integral_sub i1 i0]
  have hq : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [pow_succ] at h1
  have t := abs_sub_le (∫ v, gh (ℓ + 1) z v ∂ρ) (∫ v, g z v ∂ρ) (∫ v, gh ℓ z v ∂ρ)
  rw [abs_sub_comm (∫ v, g z v ∂ρ)] at t
  nlinarith [mul_le_mul_of_nonneg_left t hq.le]

/-- **The bias of `P_{(ℓ₁,ℓ₂)}` is `O(2^{−ℓ₁} + 2^{−ℓ₂})`** (Giles 2015, §9.2: `2^{ℓ₁}` inner
samples of `g_{ℓ₂}`; hypothesis (i) of Theorem 2).  Let `f′` be `K`-Lipschitz,
`E[g_ℓ(Z, W)⁴] ≤ m₄`, and let the inner approximations converge weakly to the exact inner
quantity `g` with first order, uniformly in the outer sample:
`2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w` for `ν`-a.e. `z`.  No measurability or moment of `g`
is assumed: `E_W[g(z, W)]` is the Bochner integral `∫ v, g z v ∂ρ`, which `hw` identifies with
`lim_ℓ E_W[g_ℓ(z, W)]` for `ν`-a.e. `z` (where `g z` is not `ρ`-integrable it is Lean's `0`, and
`hw` then forces `E_W[g_ℓ(z, W)] → 0`).  Then `P_{(ℓ₁,ℓ₂)} − f(E_W[g(Z, W)])` is integrable and
`|E[P_{(ℓ₁,ℓ₂)} − f(E_W[g(Z, W)])]| ≤ (K/2)(1 + 16 m₄) 2^{−ℓ₁} +
c_w (|f′(0)| + K(1 + m₄) + (K/2) c_w) 2^{−ℓ₂}`: the inner sampling error (`nested_bias_rate`)
plus the discretisation error, by the Taylor bound `abs_sub_le_of_lipschitz_deriv` around
`E_W[g_{ℓ₂}(z, W)]` and `E|E_W[g_{ℓ₂}(Z, W)]| ≤ E|g_{ℓ₂}(Z, W)| ≤ 1 + m₄`. -/
lemma nested_mimc_smooth_bias {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hK : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄) {g : 𝒵 → 𝒲 → ℝ} {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w) (ℓ₁ ℓ₂ : ℕ) :
    Integrable (fun p => nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f g ρ p) (nestedLaw ν ρ) ∧
      |∫ p, (nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
        K / 2 * (1 + 16 * m₄) / 2 ^ ℓ₁ +
          c_w * (|f' 0| + K * (1 + m₄) + K / 2 * c_w) / 2 ^ ℓ₂ := by
  have hK0 : 0 ≤ K := lipschitz_const_nonneg hK
  have hcw : 0 ≤ c_w := by
    obtain ⟨z, hz⟩ := (hw 0).exists
    exact le_trans (by positivity) hz
  have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hfm : Measurable f := hfd.continuous.measurable
  set q : ℝ := (2 : ℝ) ^ ℓ₂ with hq
  have hq0 : 0 < q := by positivity
  have hq1 : 1 ≤ q := one_le_pow₀ (by norm_num)
  -- the conditional means `G_{ℓ₂}(z) = E_W[g_{ℓ₂}(z, W)]` and `G(z) = E_W[g(z, W)]`
  obtain ⟨hGbm, hGb4⟩ := integrable_condMean_pow_four ν ρ (hgh ℓ₂) (hgh4 ℓ₂)
  have hGm : AEMeasurable (fun z => ∫ v, g z v ∂ρ) ν := aemeasurable_condMean_of_weak ν ρ hgh hw
  have hwl : ∀ᵐ z ∂ν, |∫ v, g z v ∂ρ - ∫ v, gh ℓ₂ z v ∂ρ| ≤ c_w / q :=
    (hw ℓ₂).mono fun z hz => by
      rw [abs_sub_comm, le_div_iff₀ hq0, mul_comm]
      exact hz
  -- `E|G_{ℓ₂}| ≤ 1 + m₄`, from `|x| ≤ 1 + x⁴`
  have habs4 : ∀ x : ℝ, |x| ≤ 1 + x ^ 4 := fun x => by
    have e : |x| ^ 4 = x ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
    rcases le_total |x| 1 with h | h
    · have : 0 ≤ x ^ 4 := by positivity
      linarith
    · have h1 : |x| ^ 1 ≤ |x| ^ 4 := pow_le_pow_right₀ h (by norm_num)
      rw [pow_one, e] at h1
      linarith
  have hg1 : Integrable (fun p : 𝒵 × 𝒲 => |gh ℓ₂ p.1 p.2|) (ν.prod ρ) :=
    ((integrable_const (1 : ℝ)).add (hgh4 ℓ₂)).mono'
      (continuous_abs.measurable.comp (hgh ℓ₂)).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]
        exact habs4 _)
  have hI : Integrable (fun z => ∫ v, |gh ℓ₂ z v| ∂ρ) ν := hg1.integral_prod_left
  have hGb1 : Integrable (fun z => |∫ v, gh ℓ₂ z v ∂ρ|) ν :=
    hI.mono' (continuous_abs.measurable.comp hGbm).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]
        exact abs_integral_le_integral_abs)
  have hGbE : ∫ z, |∫ v, gh ℓ₂ z v ∂ρ| ∂ν ≤ 1 + m₄ := by
    calc ∫ z, |∫ v, gh ℓ₂ z v ∂ρ| ∂ν ≤ ∫ z, ∫ v, |gh ℓ₂ z v| ∂ρ ∂ν :=
          integral_mono hGb1 hI fun z => abs_integral_le_integral_abs
      _ = ∫ p, |gh ℓ₂ p.1 p.2| ∂(ν.prod ρ) := (integral_prod _ hg1).symm
      _ ≤ ∫ p, (1 + gh ℓ₂ p.1 p.2 ^ 4) ∂(ν.prod ρ) :=
          integral_mono hg1 ((integrable_const 1).add (hgh4 ℓ₂))
            fun p => habs4 _
      _ = 1 + ∫ p, gh ℓ₂ p.1 p.2 ^ 4 ∂(ν.prod ρ) := by
          rw [integral_add (integrable_const _) (hgh4 ℓ₂), integral_const, probReal_univ,
            one_smul]
      _ ≤ 1 + m₄ := by linarith [hm₄ ℓ₂]
  -- the discretisation error, pointwise: `|f(G_{ℓ₂}) − f(G)| ≤ c₀ + c₁ |G_{ℓ₂}|`
  set c₀ : ℝ := (|f' 0| + K / 2 * c_w) * (c_w / q) with hc₀
  set c₁ : ℝ := K * (c_w / q) with hc₁
  have hcq : 0 ≤ c_w / q := div_nonneg hcw hq0.le
  have hpt : ∀ᵐ z ∂ν, |f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)| ≤
      c₀ + c₁ * |∫ v, gh ℓ₂ z v ∂ρ| :=
    hwl.mono fun z hz => by
      have h := abs_sub_le_of_lipschitz_deriv hf hK (∫ v, g z v ∂ρ) (∫ v, gh ℓ₂ z v ∂ρ)
      rw [abs_sub_comm] at h
      have h1 : (∫ v, g z v ∂ρ - ∫ v, gh ℓ₂ z v ∂ρ) ^ 2 ≤ c_w * (c_w / q) := by
        rw [← sq_abs, sq]
        exact mul_le_mul (hz.trans (div_le_self hcw hq1)) hz (abs_nonneg _) hcw
      have hX : 0 ≤ |f' 0| + K * |∫ v, gh ℓ₂ z v ∂ρ| := by positivity
      calc _ ≤ (|f' 0| + K * |∫ v, gh ℓ₂ z v ∂ρ|) * |∫ v, g z v ∂ρ - ∫ v, gh ℓ₂ z v ∂ρ| +
            K / 2 * (∫ v, g z v ∂ρ - ∫ v, gh ℓ₂ z v ∂ρ) ^ 2 := h
        _ ≤ (|f' 0| + K * |∫ v, gh ℓ₂ z v ∂ρ|) * (c_w / q) + K / 2 * (c_w * (c_w / q)) :=
            add_le_add (mul_le_mul_of_nonneg_left hz hX)
              (mul_le_mul_of_nonneg_left h1 (by positivity))
        _ = c₀ + c₁ * |∫ v, gh ℓ₂ z v ∂ρ| := by rw [hc₀, hc₁]; ring
  have hbound : Integrable (fun z => c₀ + c₁ * |∫ v, gh ℓ₂ z v ∂ρ|) ν :=
    (integrable_const _).add (hGb1.const_mul _)
  have hfGb : Integrable (fun z => f (∫ v, gh ℓ₂ z v ∂ρ)) ν :=
    (memLp_two_comp_of_pow_four hf hK hGbm hGb4).integrable one_le_two
  have hD : Integrable (fun z => f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ν :=
    hbound.mono' ((hfm.comp hGbm).aemeasurable.sub
      (hfm.comp_aemeasurable hGm)).aestronglyMeasurable
      (hpt.mono fun z hz => by rw [Real.norm_eq_abs]; exact hz)
  have hfG : Integrable (fun z => f (∫ v, g z v ∂ρ)) ν :=
    (hfGb.sub hD).congr (Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]
      ring)
  -- split into the inner sampling error and the discretisation error
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hP : Integrable (nestedP f (gh ℓ₂) ℓ₁) (nestedLaw ν ρ) :=
    (memLp_nestedP ν ρ hf hK (hgh ℓ₂) (hgh4 ℓ₂) ℓ₁).integrable one_le_two
  have hTb : Integrable (nestedTarget f (gh ℓ₂) ρ) (nestedLaw ν ρ) :=
    (memLp_nestedTarget ν ρ hf hK (hgh ℓ₂) (hgh4 ℓ₂)).integrable one_le_two
  have hT : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) :=
    hfst.integrable_comp_of_integrable hfG
  refine ⟨hP.sub hT, ?_⟩
  have i1 : Integrable (fun p => nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f (gh ℓ₂) ρ p)
      (nestedLaw ν ρ) := hP.sub hTb
  have i2 : Integrable (fun p => nestedTarget f (gh ℓ₂) ρ p - nestedTarget f g ρ p)
      (nestedLaw ν ρ) := hTb.sub hT
  have e2 : ∫ p, (nestedTarget f (gh ℓ₂) ρ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ z, (f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν :=
    integral_comp_of_measurePreserving hfst hD.aestronglyMeasurable
  have e1 : ∫ p, (nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ p, (nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f (gh ℓ₂) ρ p) ∂(nestedLaw ν ρ) +
        ∫ z, (f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν := by
    rw [← e2, ← integral_add i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun p => by ring)
  -- the inner sampling error
  have hb1 : |∫ p, (nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f (gh ℓ₂) ρ p) ∂(nestedLaw ν ρ)| ≤
      K / 2 * (1 + 16 * m₄) / 2 ^ ℓ₁ := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact (nested_bias_rate ν ρ hf hK (hgh ℓ₂) (hgh4 ℓ₂) ℓ₁).trans (by gcongr; exact hm₄ ℓ₂)
  -- the discretisation error
  have hb2 : |∫ z, (f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν| ≤
      c_w * (|f' 0| + K * (1 + m₄) + K / 2 * c_w) / q := by
    have hc1 : 0 ≤ c₁ := by positivity
    calc |∫ z, (f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν|
        ≤ ∫ z, |f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ z, (c₀ + c₁ * |∫ v, gh ℓ₂ z v ∂ρ|) ∂ν := integral_mono_ae hD.abs hbound hpt
      _ = c₀ + c₁ * ∫ z, |∫ v, gh ℓ₂ z v ∂ρ| ∂ν := by
          rw [integral_add (integrable_const _) (hGb1.const_mul _), integral_const,
            probReal_univ, one_smul, integral_const_mul]
      _ ≤ c₀ + c₁ * (1 + m₄) := by gcongr
      _ = c_w * (|f' 0| + K * (1 + m₄) + K / 2 * c_w) / q := by
          rw [hc₀, hc₁]
          field_simp
          ring
  rw [e1]
  exact (abs_add_le _ _).trans (add_le_add hb1 hb2)

end Rates

section Cost

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **Theorem 2 for nested MIMC with a smooth `f`: cost `O(ε⁻²)`** (Giles 2015, §9.2, p. 60:
"and therefore `E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` and `V_ℓ = O(2^{−2ℓ₁−2ℓ₂})` with a cost per sample which
is `O(2^{ℓ₁+ℓ₂})`. In Theorem 2 this corresponds to `α₁ = α₂ = 1, β₁ = β₂ = 2`, and
`γ₁ = γ₂ = 1`, so the overall complexity is `O(ε⁻²)`.").  Let level `ℓ = (ℓ₁, ℓ₂)` use `2^{ℓ₁}`
inner samples of the level-`ℓ₂` approximation `g_{ℓ₂}` of the inner quantity, and let `Y_ℓ` be
the correction `nestedMimcDelta` (the paper's six-term `Y_ℓ` for `ℓ₁, ℓ₂ > 0`).  Hypotheses (this
formalisation's; the orders of the inner time discretisation are hypotheses because Itô calculus
is not in Mathlib): `f′` (with derivative `f″`) is `K`-Lipschitz and `f″` is `L`-Lipschitz (the
paper's "twice differentiable" does not control the Taylor remainder of its expansion of `Y_ℓ`,
see `abs_mimc_antithetic_le_of_deriv2`); `E[g_ℓ(Z, W)⁴] ≤ m₄`; first order strong convergence in
`L⁴`, `(2^ℓ)⁴ E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))⁴] ≤ cₛ`; first order weak convergence to the exact inner
quantity `g`, uniformly in the outer sample, `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w` for
`ν`-a.e. `z`.  Three of these are stronger than the paper's Milstein assumptions ("first order
weak and strong convergence", p. 59; strong convergence is conventionally in `L²`, weak
convergence a statement about expectations): strong convergence in `L⁴` rather than `L²`, because
`f′(g_ℓ)` is unbounded for a merely Lipschitz `f′` (as explained in `nested_sde_variance_rate`);
weak convergence uniformly in `z` rather than on average, because the conditional mean
`μ = E_W[g_{ℓ₂+1}(z, W) − g_{ℓ₂}(z, W)]` enters pathwise, through the re-centring term
`(L/8) δ² |μ|` of `abs_mimc_antithetic_le_of_deriv2` (as explained in
`nested_mimc_variance_rate`; the pointwise Taylor bound on `f(E_W[g_{ℓ₂}(z, W)]) − f(E_W[g(z, W)])`
in `nested_mimc_smooth_bias` uses it too); and fourth moments bounded uniformly in `ℓ`, which the
paper's `O(·)` leaves implicit.  Nothing is assumed about `g` itself (neither measurability nor
moments): `E_W[g(z, W)]` is the Bochner integral `∫ v, g z v ∂ρ`, and the weak-convergence
hypothesis identifies it, for `ν`-a.e. `z`, with `lim_ℓ E_W[g_ℓ(z, W)]`.  If `g z` is
`ρ`-integrable for `ν`-a.e. `z` (the meaningful case), the target below is the paper's
`E_Z[f(E_W[g(Z, W)])]`; otherwise `∫ v, g z v ∂ρ` is Lean's value `0` on the exceptional set, and
there the hypothesis forces `E_W[g_ℓ(z, W)] → 0`, so the estimator still converges to the stated
target for a genuine reason.  Let the inputs `ω^{(ℓ,n)}` (an outer sample and its inner samples)
be independent with law `ν ⊗ ρ^{⊗ℕ}`, and let a level-`ℓ` sample cost `C_ℓ ≤ c₃ 2^{ℓ₁+ℓ₂}` on
average.  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `Λ ∈ ℝ` and
`N_ℓ ≥ 1` for which the MIMC estimator `∑_{ℓ∈𝓛} N_ℓ⁻¹ ∑_{n<N_ℓ} Y_ℓ(ω^{(ℓ,n)})` over the simplex
`𝓛 = indexSet (½, ½) Λ = {ℓ : (ℓ₁ + ℓ₂)/2 ≤ Λ}` (the index set `{θ·ℓ ≤ Λ}`,
`θ_d = α_d + (γ_d − β_d)/2`, of Theorem 2) has a square-integrable error and mean square error
`< ε²` as an estimator of `E_Z[f(E_W[g(Z, W)])]`, at expected cost `≤ c₄ ε⁻²`.  Proof: Theorem 2 in
the form `giles_theorem2_boundary_indexSet` (the paper's `α_d = ½β_d` is on the boundary of its
condition `α_d ≥ ½β_d`) with `α = (1, 1)`, `β = (2, 2)`, `γ = (1, 1)`, so `η = −1 < 0` and the bound
is `ε⁻²` (`nested_mimc_complexity`); the variances on all of `ℕ²` are bounded by
`nested_mimc_smooth_variance_rate` (with the weak constant `(3/2) c_w` of the level differences,
`weak_levelDiff_of_weak`) and the means follow from them as in `nested_mimc_smooth_mean_rate`; the
bias is `nested_mimc_smooth_bias`, and `E[Y_ℓ] = E[ΔP_ℓ]` is `integral_nestedMimcDelta_eq`.
The paper's claim holds as stated, under these hypotheses. -/
theorem nested_mimc_smooth_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f f' f'' : ℝ → ℝ} {K L : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hK : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x))
    (hL : ∀ x y, x ≤ y → |f'' y - f'' x| ≤ L * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ cₛ c_w : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ)
    {g : 𝒵 → 𝒲 → ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (ω : (Fin 2 → ℕ) × ℕ → Ω → 𝒵 × (ℕ → 𝒲))
    (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw ν ρ)) (hind : iIndepFun ω μ)
    (cost : (Fin 2 → ℕ) → ℕ → Ω → ℝ) (C : (Fin 2 → ℕ) → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : Fin 2 → ℕ, C ℓ ≤ c₃ * 2 ^ (ℓ 0 + ℓ 1)) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (Λ : ℝ) (N : (Fin 2 → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ indexSet (fun _ => (1 / 2 : ℝ)) Λ,
          blockMean (fun ℓ : Fin 2 → ℕ => nestedMimcDelta f gh (ℓ 0) (ℓ 1)) ω ℓ (N ℓ) x -
            ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2) μ ∧
        μ[fun x => (∑ ℓ ∈ indexSet (fun _ => (1 / 2 : ℝ)) Λ,
          blockMean (fun ℓ : Fin 2 → ℕ => nestedMimcDelta f gh (ℓ 0) (ℓ 1)) ω ℓ (N ℓ) x -
            ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2] < ε ^ 2 ∧
        μ[fun x => ∑ ℓ ∈ indexSet (fun _ => (1 / 2 : ℝ)) Λ, ∑ n ∈ range (N ℓ), cost ℓ n x] ≤
          c₄ * ε ^ (-2 : ℝ) := by
  have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hfm : Measurable f := hfd.continuous.measurable
  have hK0 : 0 ≤ K := lipschitz_const_nonneg hK
  have hcw : 0 ≤ c_w := by
    obtain ⟨z, hz⟩ := (hw 0).exists
    exact le_trans (by positivity) hz
  have hm0 : 0 ≤ m₄ := (integral_nonneg fun p => by positivity).trans (hm₄ 0)
  set Δ : (Fin 2 → ℕ) → 𝒵 × (ℕ → 𝒲) → ℝ := fun ℓ => nestedMimcDelta f gh (ℓ 0) (ℓ 1)
    with hΔdef
  -- the rates on all of `ℕ²`, with the weak constant `(3/2) c_w` of the level differences
  have hrate := nested_mimc_smooth_variance_rate ν ρ hf hf' hK hL hgh hgh4 hm₄ hs
    (weak_levelDiff_of_weak ν ρ hgh hgh4 hw)
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℕ,
      MemLp (nestedMimcDelta f gh a b) 2 (nestedLaw ν ρ) ∧
        ((2 : ℝ) ^ (a + b)) ^ 2 * ∫ p, nestedMimcDelta f gh a b p ^ 2 ∂(nestedLaw ν ρ) ≤ B :=
    ⟨_, le_trans (mul_nonneg (by positivity) (integral_nonneg fun p => sq_nonneg _))
      (hrate 0 0).2, hrate⟩
  have hΔm : ∀ ℓ, Measurable (Δ ℓ) := fun ℓ => measurable_nestedMimcDelta hfm hgh _ _
  have hΔ : ∀ ℓ, MemLp (Δ ℓ) 2 (nestedLaw ν ρ) := fun ℓ => (hB _ _).1
  -- integrability of the quantity of interest and of every approximation `P_{(a,b)}`
  have hint : ∀ a b, Integrable (nestedP f (gh b) a) (nestedLaw ν ρ) := fun a b =>
    (memLp_nestedP ν ρ hf hK (hgh b) (hgh4 b) a).integrable one_le_two
  have hbias := fun a b => nested_mimc_smooth_bias ν ρ hf hK hgh hgh4 hm₄ hw a b
  have hPt : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) :=
    ((hint 0 0).sub (hbias 0 0).1).congr (Eventually.of_forall fun p => by simp)
  -- transport to `Ω` along the input `ω (0, 0)`
  have hφ := hω (0, 0)
  have tr : ∀ F : 𝒵 × (ℕ → 𝒲) → ℝ, Integrable F (nestedLaw ν ρ) →
      ∫ x, F (ω (0, 0) x) ∂μ = ∫ y, F y ∂(nestedLaw ν ρ) := fun F hF =>
    integral_comp_of_measurePreserving hφ hF.aestronglyMeasurable
  set P : Ω → ℝ := fun x => nestedTarget f g ρ (ω (0, 0) x) with hPdef
  set Pℓ : (Fin 2 → ℕ) → Ω → ℝ := fun ℓ x => nestedP f (gh (ℓ 1)) (ℓ 0) (ω (0, 0) x)
    with hPℓdef
  have hPμ : Integrable P μ := hφ.integrable_comp_of_integrable hPt
  have hPℓμ : ∀ ℓ, Integrable (Pℓ ℓ) μ := fun ℓ => hφ.integrable_comp_of_integrable (hint _ _)
  have hdot : ∀ (a : ℝ) (ℓ : Fin 2 → ℕ), dot (fun _ => a) ℓ = a * ((ℓ 0 : ℝ) + ℓ 1) := by
    intro a ℓ
    simp only [dot, Fin.sum_univ_two]
    ring
  -- (i) the bias tends to zero
  have h_i : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ ℓ : Fin 2 → ℕ, (∀ d, n₀ ≤ ℓ d) →
      |μ[fun x => Pℓ ℓ x - P x]| < δ := by
    intro δ hδ
    set K₁ : ℝ := K / 2 * (1 + 16 * m₄) with hK₁
    set K₂ : ℝ := c_w * (|f' 0| + K * (1 + m₄) + K / 2 * c_w) with hK₂
    have hK₁0 : 0 ≤ K₁ := by positivity
    have hK₂0 : 0 ≤ K₂ := by positivity
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (K₁ + K₂ + 1) by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨m, fun ℓ hℓ => ?_⟩
    have e : μ[fun x => Pℓ ℓ x - P x] =
        ∫ p, (nestedP f (gh (ℓ 1)) (ℓ 0) p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) :=
      tr _ (hbias (ℓ 0) (ℓ 1)).1
    rw [e]
    have hb := (hbias (ℓ 0) (ℓ 1)).2
    have hpm : (0 : ℝ) < 2 ^ m := by positivity
    have b1 : K₁ / 2 ^ (ℓ 0) ≤ K₁ * (1 / 2) ^ m := by
      rw [one_div_pow, ← div_eq_mul_one_div]
      exact div_le_div_of_nonneg_left hK₁0 hpm (pow_le_pow_right₀ (by norm_num) (hℓ 0))
    have b2 : K₂ / 2 ^ (ℓ 1) ≤ K₂ * (1 / 2) ^ m := by
      rw [one_div_pow, ← div_eq_mul_one_div]
      exact div_le_div_of_nonneg_left hK₂0 hpm (pow_le_pow_right₀ (by norm_num) (hℓ 1))
    have hlt : (K₁ + K₂ + 1) * (1 / 2) ^ m < δ := by
      rw [lt_div_iff₀ (by positivity)] at hm
      linarith
    have hpos : (0 : ℝ) < (1 / 2) ^ m := by positivity
    calc _ ≤ K₁ / 2 ^ (ℓ 0) + K₂ / 2 ^ (ℓ 1) := hb
      _ ≤ K₁ * (1 / 2) ^ m + K₂ * (1 / 2) ^ m := add_le_add b1 b2
      _ < δ := by nlinarith
  -- (iii) the corrections have the right means: `E[Y_ℓ] = E[ΔP_ℓ]`
  have h_iii : ∀ (ℓ : Fin 2 → ℕ) (n : ℕ), 0 < n →
      μ[blockMean Δ ω ℓ n] = μ[fun x => crossDiff (fun m => Pℓ m x) ℓ] := by
    intro ℓ n hn
    rw [integral_blockMean hω (fun i => (hΔ i).integrable one_le_two) ℓ hn,
      (integrable_integral_crossDiff Pℓ hPℓμ ℓ).2]
    have e : (fun m => μ[Pℓ m]) = fun m : Fin 2 → ℕ =>
        ∫ p, nestedP f (gh (m 1)) (m 0) p ∂(nestedLaw ν ρ) :=
      funext fun m => tr _ (hint _ _)
    rw [e, crossDiff_two_eq (fun a b => ∫ p, nestedP f (gh b) a p ∂(nestedLaw ν ρ)) ℓ]
    exact integral_nestedMimcDelta_eq ν ρ hint (ℓ 0) (ℓ 1)
  -- (ii) the means, `α = (1, 1)`
  have h_ii : ∀ (ℓ : Fin 2 → ℕ) (n : ℕ), 0 < n → |μ[blockMean Δ ω ℓ n]| ≤
      (B + 1) / 2 * (2 : ℝ) ^ (-dot (fun _ => (1 : ℝ)) ℓ) := by
    intro ℓ n hn
    rw [integral_blockMean hω (fun i => (hΔ i).integrable one_le_two) ℓ hn]
    have hs0 : (0 : ℝ) < 2 ^ (ℓ 0 + ℓ 1) := by positivity
    have h1 := mul_abs_integral_le_of_memLp (hΔ ℓ) hs0
    have h2 : ((2 : ℝ) ^ (ℓ 0 + ℓ 1)) ^ 2 * ∫ x, Δ ℓ x ^ 2 ∂(nestedLaw ν ρ) ≤ B := (hB _ _).2
    have e : (2 : ℝ) ^ (-dot (fun _ => (1 : ℝ)) ℓ) = ((2 : ℝ) ^ (ℓ 0 + ℓ 1))⁻¹ := by
      rw [hdot, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
      congr 1
      push_cast
      ring
    rw [e, ← div_eq_mul_inv, le_div_iff₀ hs0]
    linarith
  -- (iv) the variances, `β = (2, 2)`
  have h_iv : ∀ ℓ : Fin 2 → ℕ, variance (Δ ℓ) (nestedLaw ν ρ) ≤
      (B + 1) * (2 : ℝ) ^ (-dot (fun _ => (2 : ℝ)) ℓ) := by
    intro ℓ
    have hv : variance (Δ ℓ) (nestedLaw ν ρ) ≤ ∫ x, Δ ℓ x ^ 2 ∂(nestedLaw ν ρ) := by
      simpa only [Pi.pow_apply] using variance_le_expectation_sq (hΔm ℓ).aestronglyMeasurable
    have h2 : ((2 : ℝ) ^ (ℓ 0 + ℓ 1)) ^ 2 * ∫ x, Δ ℓ x ^ 2 ∂(nestedLaw ν ρ) ≤ B := (hB _ _).2
    have hs0 : (0 : ℝ) < ((2 : ℝ) ^ (ℓ 0 + ℓ 1)) ^ 2 := by positivity
    have e : (2 : ℝ) ^ (-dot (fun _ => (2 : ℝ)) ℓ) = (((2 : ℝ) ^ (ℓ 0 + ℓ 1)) ^ 2)⁻¹ := by
      rw [hdot, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
      congr 1
      push_cast
      ring
    rw [e, ← div_eq_mul_inv, le_div_iff₀ hs0]
    have := mul_le_mul_of_nonneg_left hv hs0.le
    linarith
  -- (v) the cost, `γ = (1, 1)`
  have h_v : ∀ ℓ : Fin 2 → ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ dot (fun _ => (1 : ℝ)) ℓ := by
    intro ℓ
    have e : (2 : ℝ) ^ dot (fun _ => (1 : ℝ)) ℓ = 2 ^ (ℓ 0 + ℓ 1) := by
      rw [hdot, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rw [e]
    exact hC ℓ
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem2_boundary_indexSet (μ := μ) (D := 2) P Pℓ
    (fun ℓ n => blockMean Δ ω ℓ n) (fun ℓ n x => ∑ k ∈ range n, cost ℓ k x)
    (fun ℓ => variance (Δ ℓ) (nestedLaw ν ρ)) C (α := fun _ => 1) (β := fun _ => 2)
    (γ := fun _ => 1) (c₁ := (B + 1) / 2) (c₂ := B + 1) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (by positivity)
    (by positivity) hc₃ hPμ hPℓμ (fun ℓ n _ => memLp_blockMean hω hΔ ℓ n)
    (fun N _ i j hij => indepFun_blockMean (fun p => (hω p).measurable) hind hΔm hij _ _)
    (fun ℓ n _ => integrable_finsetSum _ fun k _ => hcost ℓ k)
    (fun ℓ n _ => by
      rw [integral_finsetSum _ fun k _ => hcost ℓ k]
      simp [hcostC])
    (fun ℓ n hn => variance_blockMean hω hind hΔm hΔ ℓ hn) h_i h_iii h_ii h_iv h_v
  -- the quantity of interest, the index set and the exponents
  have hGm : AEMeasurable (fun z => ∫ v, g z v ∂ρ) ν := aemeasurable_condMean_of_weak ν ρ hgh hw
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hPint : μ[P] = ∫ z, f (∫ v, g z v ∂ρ) ∂ν := by
    rw [hPdef, tr _ hPt]
    exact integral_comp_of_measurePreserving hfst
      (hfm.comp_aemeasurable hGm).aestronglyMeasurable
  have hθ : (fun d : Fin 2 => (1 : ℝ) + (1 - 2) / 2) = fun _ => (1 / 2 : ℝ) := by
    funext d
    norm_num
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨Λ, N, hN, hmse, hcost'⟩ := h ε hε hε1
  rw [hPint, hθ] at hmse
  rw [hθ, (nested_mimc_complexity _ _ ε).2.2.1] at hcost'
  exact ⟨Λ, N, hN, ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω hΔ ℓ (N ℓ)).sub
    (memLp_const _)).integrable_sq, hmse, hcost'⟩

end Cost

end MLMC
