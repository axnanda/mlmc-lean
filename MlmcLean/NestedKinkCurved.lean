import MlmcLean.SDEExtensions
import MlmcLean.NestedMimcKink

/-!
# Nested simulation with inner time steps for an `f` with several kinks and curved pieces
(Giles 2015, §9.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §9.1 "MLMC
treatment" (pp. 57–58) and §9.2 "MIMC treatment" (pp. 59–60) of the author's version.  Line numbers
refer to the text `docs/giles2015.txt`.

§9.2, p. 60, l. 2687–2690: "Following the analysis in (Bujok et al. 2013), if the function `f` is
continuous and piecewise differentiable, rather than being twice differentiable, then in the MLMC
treatment we would get `β = 1.5`, and hence an overall complexity which is `O(ε^{−2.5})`."  Level
`ℓ` uses `2^ℓ` inner samples of an inner approximation `g_ℓ` with `2^ℓ` time steps (`nestedSdeP`,
`nestedSdeDelta`), so this is Theorem 1 with `α = 1`, `β = 3/2` and `γ = 2`.
`MlmcLean/NestedKinkSde.lean` proves it for one linear kink (`nested_kink_sde_bias_rate`,
`nested_kink_sde_variance_rate`, `nested_kink_sde_mlmc_complexity`), `MlmcLean/NestedRates.lean`
for a smooth `f` (`nested_sde_bias_rate`, `nested_sde_variance_rate`, `nested_sde_mlmc_complexity`)
and `MlmcLean/SDEExtensions.lean` for several kinks and curved pieces without time steps
(`nested_kinks_variance_rate`, `nested_kinks_mlmc_complexity`).  This file combines them for
`f = f₀ + ∑_{i ∈ ι} c_i max(· − k_i, 0)` with finitely many kinks `k_i`:

* **Linearity in `f`** (`nestedSdeDelta_succ_kinks`, `nested_sde_bias_kinks_add`,
  `nested_sde_variance_kinks_add`): the correction `Y_{ℓ+1}` and the bias integrand of `f` are
  those of `f₀` plus `∑_i c_i` times those of the hinge `max(· − k_i, 0)`, so the rates add (with
  `(a + ∑_i b_i)² ≤ (|ι| + 1)(a² + ∑_i b_i²)`, `sq_add_sum_le`), and Theorem 1 then follows from
  the two rates (`nested_sde_mlmc_complexity_of_rates`).
* **Curved pieces**, `f₀` differentiable with a Lipschitz derivative (every continuous `f` that is
  `C^{1,1}` on each closed interval between consecutive kinks has this form, `c_i` being the jump
  of `f′` at `k_i`): `α = 1` (`nested_kinks_sde_bias_rate`; the smooth part by
  `nested_sde_bias_le_of_weak`, a variant of `nested_sde_bias_rate` that, like the kink results,
  assumes no measurability or moment of the exact inner quantity `g`), `β = 3/2`
  (`nested_kinks_sde_variance_rate`; the smooth part is `O(2^{−ℓ})` in `L²` by
  `nested_sde_variance_rate`) and the complexity `O(ε^{−2.5})`
  (`nested_kinks_sde_mlmc_complexity`).
* **Piecewise linear `f`**, `f₀` affine and at least one kink: the same three results under the
  hypotheses of the one-kink results (`nested_piecewise_linear_sde_bias_rate`,
  `nested_piecewise_linear_sde_variance_rate`, `nested_piecewise_linear_sde_mlmc_complexity`),
  which they extend to several kinks.

Hypotheses (this formalisation's; the paper states none for this case, and the orders of the time
discretisation are not formalised).  For a piecewise linear `f`, those of the one-kink results:
bounded centred conditional fourth moments `E_W[(g_ℓ(z, W) − E_W[g_ℓ(z, W)])⁴] ≤ κ₄` for `ν`-a.e.
`z` (so the conditional mean may be unbounded); first order weak convergence uniformly in the outer
sample, `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w`; strong order `¼` in `L²`,
`2^{ℓ/2} E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))²] ≤ cₛ`, which the strong order `½` of the Euler–Maruyama
scheme implies; `E[g₀(Z, W)²] < ∞` for the complexity; and a small-ball bound
`ν{|E_W[g(Z, W)] − k_i| ≤ t} ≤ c_{d,i} t` at each kink, for the exact conditional mean only.  With
curved pieces, those of the smooth results are added for the curved part: joint fourth moments
`E[g_ℓ(Z, W)⁴] ≤ m₄`, and first order strong convergence in `L⁴`,
`(2^ℓ)⁴ E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))⁴] ≤ cₛ`, the Milstein-level hypothesis of
`nested_sde_variance_rate`, which implies the strong order `¼` in `L²`
(`strong_quarter_of_strong_four`).  These are strictly stronger: they exclude the Euler–Maruyama
scheme and an outer state with `E[g⁴] = ∞` (e.g. Student-`t` with three degrees of freedom), so
the results with curved pieces do not contain the piecewise linear ones, even for `f₀` affine.
Deviation: `f` is given through the decomposition above rather than as a continuous, piecewise
differentiable function.

**MIMC on the two axes for the kink example** (l. 2690–2692: "On the other hand, with MIMC we would
have `β₁ = β₂ = 1.5` and so the complexity would remain `O(ε⁻²)`").  These rates are false
(`nested_mimc_kink_rates_false`), and Theorem 2 with the corrected rates gives only
`O(ε⁻² |log ε|⁴)` (`nested_mimc_kink_complexity`).  For the counterexample itself
(`kinkInnerApprox`) the cost `O(ε⁻²)` is nevertheless reached, by the MIMC estimator on the index
set made of the two axes (`kinkInnerApprox_mimc_axes_complexity`): its mixed corrections have mean
zero, so `E[P_{(a,b)}]` is additive in `(a, b)` (`kinkExample_mean_additive`) and the axes
estimator has the bias of the full box; on the axes the variances decay faster than the costs grow
(`kinkExample_axis_one`: `β₁ = 3/2`; `kinkExample_axis_two`: `β₂ = 2`; `γ₁ = γ₂ = 1`); grouping
`(k, 0)` and `(0, k)` into one level gives Theorem 1 with `β = 3/2 > γ = 1`
(`indepFun_sum_blockMean` for the independence of the groups).  This uses the vanishing means of
the mixed corrections, which is special to the example; whether MIMC reaches `O(ε⁻²)` for a
general piecewise linear `f` is not decided here.
-/

open MeasureTheory ProbabilityTheory Finset Filter

namespace MLMC

section KinksSde

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲]

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
/-- **The discretised correction is linear in `f`** (Giles 2015, §9.2, p. 60, l. 2687–2690, for an
`f` with several kinks; §9.1, p. 57): if `f = f₀ + ∑_i c_i max(· − k_i, 0)`, then
`Y_{ℓ+1}(f) = Y_{ℓ+1}(f₀) + ∑_i c_i Y_{ℓ+1}(max(· − k_i, 0))` pointwise (`nestedSdeDelta`), as for
exact inner samples (`nestedDelta_succ_kinks`). -/
lemma nestedSdeDelta_succ_kinks {ι : Type*} [Fintype ι] {f f₀ : ℝ → ℝ} {c k : ι → ℝ}
    (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0) (gh : ℕ → 𝒵 → 𝒲 → ℝ) (ℓ : ℕ)
    (p : 𝒵 × (ℕ → 𝒲)) :
    nestedSdeDelta f gh (ℓ + 1) p = nestedSdeDelta f₀ gh (ℓ + 1) p +
      ∑ i, c i * nestedSdeDelta (fun x => max (x - k i) 0) gh (ℓ + 1) p := by
  set A := innerMean (gh (ℓ + 1)) (2 ^ (ℓ + 1)) p.1 p.2
  set B := innerMean (gh ℓ) (2 ^ ℓ) p.1 p.2
  set C := innerMean (gh ℓ) (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)
  have e : ∀ F : ℝ → ℝ, nestedSdeDelta F gh (ℓ + 1) p = F A - F B / 2 - F C / 2 := fun F => rfl
  have h1 : ∑ i, c i * (max (A - k i) 0 - max (B - k i) 0 / 2 - max (C - k i) 0 / 2) =
      ∑ i, c i * max (A - k i) 0 - (∑ i, c i * max (B - k i) 0) / 2 -
        (∑ i, c i * max (C - k i) 0) / 2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, e, hf A, hf B, hf C]
  simp only [e]
  rw [h1]
  ring

variable (ν : Measure 𝒵) [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **First order strong convergence in `L⁴` gives strong order `¼` in `L²`** (Giles 2015, §9.2,
p. 59, l. 2574–2575: the Milstein discretisation gives "first order weak and strong convergence";
the kink results need only `2^{ℓ/2} E[(g_{ℓ+1} − g_ℓ)²] ≤ cₛ′`).  If `E[g_ℓ(Z, W)⁴] < ∞` for
every `ℓ` and `(2^ℓ)⁴ E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))⁴] ≤ cₛ`, then
`2^{ℓ/2} E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))²] ≤ (1 + cₛ)/2`, from `X² ≤ (q⁻² + q² X⁴)/2` with
`q = 2^ℓ`. -/
lemma strong_quarter_of_strong_four {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {cₛ : ℝ}
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ) (ℓ : ℕ) :
    (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ (1 + cₛ) / 2 := by
  set X : 𝒵 × 𝒲 → ℝ := fun p => gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2 with hX
  have hXm : Measurable X := (hgh (ℓ + 1)).sub (hgh ℓ)
  have hX4 : Integrable (fun p => X p ^ 4) (ν.prod ρ) := by
    refine (((hgh4 (ℓ + 1)).add (hgh4 ℓ)).const_mul 8).mono' (hXm.pow_const 4).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact sub_pow_four_le _ _
  have hX2 : Integrable (fun p => X p ^ 2) (ν.prod ρ) :=
    integrable_pow_of_pow_four hXm hX4 (by norm_num)
  set q : ℝ := (2 : ℝ) ^ ℓ with hq
  have hq1 : 1 ≤ q := one_le_pow₀ (by norm_num)
  have hq0 : 0 < q := by positivity
  have hE4 : 0 ≤ ∫ p, X p ^ 4 ∂(ν.prod ρ) := integral_nonneg fun p => by positivity
  have hcs : 0 ≤ cₛ := le_trans (by positivity) (hs ℓ)
  -- `X² ≤ (q⁻² + q² X⁴)/2`
  have hpt : ∀ p, X p ^ 2 ≤ (1 / q ^ 2 + q ^ 2 * X p ^ 4) / 2 := fun p => by
    have h := sq_nonneg (q * X p ^ 2 - 1 / q)
    have e : (q * X p ^ 2 - 1 / q) ^ 2 = q ^ 2 * X p ^ 4 - 2 * X p ^ 2 + 1 / q ^ 2 := by
      field_simp
      ring
    rw [e] at h
    linarith
  have hint : Integrable (fun p => (1 / q ^ 2 + q ^ 2 * X p ^ 4) / 2) (ν.prod ρ) :=
    ((integrable_const _).add (hX4.const_mul _)).div_const 2
  have h1 : ∫ p, X p ^ 2 ∂(ν.prod ρ) ≤ (1 + cₛ) / (2 * q ^ 2) := by
    refine (integral_mono hX2 hint hpt).trans ?_
    rw [integral_div, integral_add (integrable_const _) (hX4.const_mul _), integral_const,
      probReal_univ, one_smul, integral_const_mul]
    have h4 : q ^ 2 * ∫ p, X p ^ 4 ∂(ν.prod ρ) ≤ cₛ / q ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have e : q ^ 2 * (∫ p, X p ^ 4 ∂(ν.prod ρ)) * q ^ 2 =
          q ^ 4 * ∫ p, X p ^ 4 ∂(ν.prod ρ) := by
        ring
      rw [e]
      exact hs ℓ
    have e : (1 + cₛ) / (2 * q ^ 2) = (1 / q ^ 2 + cₛ / q ^ 2) / 2 := by
      field_simp
    rw [e]
    linarith
  -- `2^{ℓ/2} ≤ q ≤ q²`
  have hr : (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) ≤ q ^ 2 := by
    rw [hq, ← pow_mul, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hE2 : 0 ≤ ∫ p, X p ^ 2 ∂(ν.prod ρ) := integral_nonneg fun p => sq_nonneg _
  calc (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) * ∫ p, X p ^ 2 ∂(ν.prod ρ)
      ≤ q ^ 2 * ((1 + cₛ) / (2 * q ^ 2)) := mul_le_mul hr h1 hE2 (by positivity)
    _ = (1 + cₛ) / 2 := by field_simp

/-- **`α = 1` for a smooth `f` with `2^ℓ` timesteps, without measurability of the exact `g`**
(Giles 2015, §9.2, p. 59, l. 2574–2576: "When using the Milstein discretisation (giving first order
weak and strong convergence) this would still give `α = 1`").  Let `f` be differentiable with a
`K`-Lipschitz derivative `f′`, let level `ℓ` use `2^ℓ` inner samples of the level-`ℓ` approximation
`g_ℓ` of the inner quantity `g` (`nestedSdeP`), and assume `E[g_ℓ(Z, W)⁴] ≤ m₄` and first order
weak convergence uniformly in the outer sample, `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w` for
`ν`-a.e. `z` (this formalisation's hypotheses, standing in for the weak order of the Milstein
scheme, which is not formalised).  Then `P_ℓ − f(E_W[g(Z, W)])` is integrable and
`2^ℓ |E[P_ℓ − f(E_W[g(Z, W)])]| ≤ (K/2)(1 + 16 m₄) + c_w (|f′(0)| + K (1 + m₄)) + (K/2) c_w²`.
Compared with `nested_sde_bias_rate`, no measurability or moment of the exact `g` is assumed (as in
`nested_kink_sde_bias_rate`, `g` enters only through its conditional mean `E_W[g(z, W)]`, the a.e.
limit of the `E_W[g_ℓ(z, W)]` by the weak-error hypothesis, `aemeasurable_condMean_of_weak`), the
bound is an explicit constant (`E_Z|f′(E_W[g(Z, W)])|` is replaced by `|f′(0)| + K (1 + m₄)`), and
the integrability of the bias integrand is proved.  Proof: the inner sampling error
(`nested_bias_rate`) plus the discretisation error, by the Taylor bound
`|f(G) − f(G_ℓ)| ≤ |f′(G_ℓ)| |G − G_ℓ| + (K/2)(G − G_ℓ)²` (`abs_taylor_first_le`) at the
approximate conditional mean `G_ℓ`, with `E|G_ℓ| ≤ E|g_ℓ(Z, W)| ≤ 1 + m₄`. -/
theorem nested_sde_bias_le_of_weak {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄) {g : 𝒵 → 𝒲 → ℝ} {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w) (ℓ : ℕ) :
    Integrable (fun p => nestedSdeP f gh ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
        K / 2 * (1 + 16 * m₄) + c_w * (|f' 0| + K * (1 + m₄)) + K / 2 * c_w ^ 2 := by
  have hK := lipschitz_const_nonneg hf'
  have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hfm : Measurable f := hfd.continuous.measurable
  have hf'm : Measurable f' := (continuous_of_lipschitz_deriv hf').measurable
  have h2l : (1 : ℝ) ≤ (2 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
  have h2l0 : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  have hcw : 0 ≤ c_w := by
    obtain ⟨z, hz⟩ := (hw ℓ).exists
    exact le_trans (by positivity) hz
  -- the conditional means `G_ℓ(z) = E_W[g_ℓ(z, W)]` and `G(z) = E_W[g(z, W)]`
  obtain ⟨hGlm, hGl4⟩ := integrable_condMean_pow_four ν ρ (hgh ℓ) (hgh4 ℓ)
  have hGm : AEMeasurable (fun z => ∫ v, g z v ∂ρ) ν := aemeasurable_condMean_of_weak ν ρ hgh hw
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  -- `E|G_ℓ| ≤ E|g_ℓ(Z, W)| ≤ 1 + m₄`
  have hgl1 : Integrable (fun p : 𝒵 × 𝒲 => |gh ℓ p.1 p.2|) (ν.prod ρ) := by
    have h := integrable_pow_of_pow_four (hgh ℓ) (hgh4 ℓ) (k := 1) (by norm_num)
    simp only [pow_one] at h
    exact h.abs
  have hGl1 : Integrable (fun z => ∫ v, gh ℓ z v ∂ρ) ν := by
    have h := integrable_pow_of_pow_four hGlm hGl4 (k := 1) (by norm_num)
    simpa only [pow_one] using h
  have hEG : ∫ z, |∫ v, gh ℓ z v ∂ρ| ∂ν ≤ 1 + m₄ := by
    have i1 : Integrable (fun z => ∫ v, |gh ℓ z v| ∂ρ) ν := hgl1.integral_prod_left
    have i2 : Integrable (fun p : 𝒵 × 𝒲 => 1 + gh ℓ p.1 p.2 ^ 4) (ν.prod ρ) :=
      (integrable_const 1).add (hgh4 ℓ)
    calc ∫ z, |∫ v, gh ℓ z v ∂ρ| ∂ν ≤ ∫ z, ∫ v, |gh ℓ z v| ∂ρ ∂ν :=
          integral_mono hGl1.abs i1 fun z => abs_integral_le_integral_abs
      _ = ∫ p, |gh ℓ p.1 p.2| ∂(ν.prod ρ) := (integral_prod _ hgl1).symm
      _ ≤ ∫ p, (1 + gh ℓ p.1 p.2 ^ 4) ∂(ν.prod ρ) := integral_mono hgl1 i2 fun p => by
          have h4 : 0 ≤ gh ℓ p.1 p.2 ^ 4 := by positivity
          rcases le_total (|gh ℓ p.1 p.2|) 1 with h | h
          · show |gh ℓ p.1 p.2| ≤ 1 + gh ℓ p.1 p.2 ^ 4
            linarith
          · show |gh ℓ p.1 p.2| ≤ 1 + gh ℓ p.1 p.2 ^ 4
            have e : gh ℓ p.1 p.2 ^ 4 = |gh ℓ p.1 p.2| ^ 4 := by
              rw [← abs_pow, abs_of_nonneg h4]
            have h3 : |gh ℓ p.1 p.2| ≤ |gh ℓ p.1 p.2| ^ 4 := by
              calc |gh ℓ p.1 p.2| = |gh ℓ p.1 p.2| ^ 1 := (pow_one _).symm
                _ ≤ |gh ℓ p.1 p.2| ^ 4 := pow_le_pow_right₀ h (by norm_num)
            linarith
      _ = 1 + ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) := by
          rw [integral_add (integrable_const 1) (hgh4 ℓ), integral_const, probReal_univ,
            one_smul]
      _ ≤ 1 + m₄ := by linarith [hm₄ ℓ]
  -- `|f′(G_ℓ)| ≤ |f′(0)| + K |G_ℓ|` is integrable with mean at most `|f′(0)| + K (1 + m₄)`
  have hf'abs : ∀ x, |f' x| ≤ |f' 0| + K * |x| := fun x => by
    have h := abs_sub_abs_le_abs_sub (f' x) (f' 0)
    have h' : |f' x - f' 0| ≤ K * |x| := by
      rcases le_total 0 x with h0 | h0
      · rw [abs_of_nonneg h0]
        simpa using hf' 0 x h0
      · rw [abs_sub_comm, abs_of_nonpos h0]
        simpa using hf' x 0 h0
    linarith
  have hf'G : Integrable (fun z => |f' (∫ v, gh ℓ z v ∂ρ)|) ν :=
    ((integrable_const |f' 0|).add (hGl1.abs.const_mul K)).mono'
      (continuous_abs.measurable.comp (hf'm.comp hGlm)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]
        exact hf'abs _)
  have hEf'G : ∫ z, |f' (∫ v, gh ℓ z v ∂ρ)| ∂ν ≤ |f' 0| + K * (1 + m₄) := by
    have i : Integrable (fun z => |f' 0| + K * |∫ v, gh ℓ z v ∂ρ|) ν :=
      (integrable_const _).add (hGl1.abs.const_mul K)
    refine (integral_mono hf'G i fun z => hf'abs _).trans ?_
    rw [integral_add (integrable_const _) (hGl1.abs.const_mul K), integral_const, probReal_univ,
      one_smul, integral_const_mul]
    gcongr
  -- the discretisation error, pointwise
  set d : ℝ := c_w / 2 ^ ℓ with hd
  have hpt : ∀ᵐ z ∂ν, |f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)| ≤
      |f' (∫ v, gh ℓ z v ∂ρ)| * d + K / 2 * d ^ 2 := by
    filter_upwards [hw ℓ] with z hz
    set a := ∫ v, gh ℓ z v ∂ρ
    set b := ∫ v, g z v ∂ρ
    have ht := abs_taylor_first_le hf hf' a b
    have hab : |b - a| ≤ d := by
      rw [hd, le_div_iff₀ h2l0, mul_comm, abs_sub_comm]
      exact hz
    have hsq : (b - a) ^ 2 ≤ d ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    calc |f a - f b| = |-(f' a * (b - a)) - (f b - f a - f' a * (b - a))| := by
          congr 1
          ring
      _ ≤ |f' a * (b - a)| + |f b - f a - f' a * (b - a)| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_neg]
      _ ≤ |f' a| * d + K / 2 * d ^ 2 := by
          rw [abs_mul]
          gcongr
          exact ht.trans (by gcongr)
  -- integrability
  have hfGl : MemLp (fun z => f (∫ v, gh ℓ z v ∂ρ)) 2 ν :=
    memLp_two_comp_of_pow_four hf hf' hGlm hGl4
  have hdom : Integrable (fun z => |f' (∫ v, gh ℓ z v ∂ρ)| * d + K / 2 * d ^ 2) ν :=
    (hf'G.mul_const d).add (integrable_const _)
  have hD : Integrable (fun z => f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ν :=
    hdom.mono' ((hfm.comp hGlm).aemeasurable.sub (hfm.comp_aemeasurable hGm)).aestronglyMeasurable
      (hpt.mono fun z hz => by rw [Real.norm_eq_abs]; exact hz)
  have i1 : Integrable (fun p => nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p)
      (nestedLaw ν ρ) :=
    ((memLp_nestedP ν ρ hf hf' (hgh ℓ) (hgh4 ℓ) ℓ).integrable one_le_two).sub
      ((memLp_nestedTarget ν ρ hf hf' (hgh ℓ) (hgh4 ℓ)).integrable one_le_two)
  have i2 : Integrable (fun p => nestedTarget f (gh ℓ) ρ p - nestedTarget f g ρ p)
      (nestedLaw ν ρ) :=
    hfst.integrable_comp_of_integrable hD
  have hint : Integrable (fun p => nestedSdeP f gh ℓ p - nestedTarget f g ρ p)
      (nestedLaw ν ρ) :=
    (i1.add i2).congr (Eventually.of_forall fun p => by
      simp only [Pi.add_apply, nestedSdeP, nestedP]
      ring)
  refine ⟨hint, ?_⟩
  -- split into the inner sampling error and the discretisation error
  have e1 : ∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p) ∂(nestedLaw ν ρ) +
        ∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν := by
    have e2 : ∫ p, (nestedTarget f (gh ℓ) ρ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
        ∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν :=
      integral_comp_of_measurePreserving hfst hD.aestronglyMeasurable
    rw [← e2, ← integral_add i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun p => by
      simp only [nestedSdeP, nestedP]
      ring)
  have hb1 : (2 : ℝ) ^ ℓ * |∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p)
      ∂(nestedLaw ν ρ)| ≤ K / 2 * (1 + 16 * m₄) :=
    (nested_bias_rate ν ρ hf hf' (hgh ℓ) (hgh4 ℓ) ℓ).trans (by gcongr; exact hm₄ ℓ)
  have hb2 : (2 : ℝ) ^ ℓ * |∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν| ≤
      c_w * (|f' 0| + K * (1 + m₄)) + K / 2 * c_w ^ 2 := by
    have h := integral_mono_ae hD.abs hdom hpt
    rw [integral_add (hf'G.mul_const d) (integrable_const _), integral_mul_const, integral_const,
      probReal_univ, one_smul] at h
    have hd0 : 0 ≤ d := by positivity
    have e : (2 : ℝ) ^ ℓ * ((∫ z, |f' (∫ v, gh ℓ z v ∂ρ)| ∂ν) * d + K / 2 * d ^ 2) =
        c_w * ∫ z, |f' (∫ v, gh ℓ z v ∂ρ)| ∂ν + K / 2 * c_w ^ 2 / 2 ^ ℓ := by
      rw [hd]
      field_simp
    calc (2 : ℝ) ^ ℓ * |∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν|
        ≤ (2 : ℝ) ^ ℓ * ((∫ z, |f' (∫ v, gh ℓ z v ∂ρ)| ∂ν) * d + K / 2 * d ^ 2) :=
          mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs.trans h) h2l0.le
      _ = c_w * ∫ z, |f' (∫ v, gh ℓ z v ∂ρ)| ∂ν + K / 2 * c_w ^ 2 / 2 ^ ℓ := e
      _ ≤ c_w * (|f' 0| + K * (1 + m₄)) + K / 2 * c_w ^ 2 := by
          gcongr
          exact div_le_self (by positivity) h2l
  rw [e1]
  calc (2 : ℝ) ^ ℓ * |∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p) ∂(nestedLaw ν ρ) +
        ∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν|
      ≤ (2 : ℝ) ^ ℓ * |∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p)
          ∂(nestedLaw ν ρ)| +
        (2 : ℝ) ^ ℓ * |∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν| := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) h2l0.le
    _ ≤ K / 2 * (1 + 16 * m₄) + (c_w * (|f' 0| + K * (1 + m₄)) + K / 2 * c_w ^ 2) :=
        add_le_add hb1 hb2
    _ = _ := by ring

/-! #### Linearity in `f` -/

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] in
/-- **The bias is linear in `f`** (Giles 2015, §9.2, p. 60, l. 2687–2690, for an `f` with several
kinks): if `f = f₀ + ∑_i c_i max(· − k_i, 0)` and the bias integrands `P_ℓ − f(E_W[g(Z, W)])`
(`nestedSdeP`, `nestedTarget`) of `f₀` and of each hinge `max(· − k_i, 0)` are integrable with
`2^ℓ |E[·]|` at most `b₀` and `b_i`, then that of `f` is integrable and
`2^ℓ |E[P_ℓ − f(E_W[g(Z, W)])]| ≤ b₀ + ∑_i |c_i| b_i`. -/
lemma nested_sde_bias_kinks_add {ι : Type*} [Fintype ι] {f f₀ : ℝ → ℝ} {c k : ι → ℝ}
    (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    {g : 𝒵 → 𝒲 → ℝ} {ℓ : ℕ} {b₀ : ℝ} {b : ι → ℝ}
    (h₀ : Integrable (fun p => nestedSdeP f₀ gh ℓ p - nestedTarget f₀ g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP f₀ gh ℓ p - nestedTarget f₀ g ρ p) ∂(nestedLaw ν ρ)| ≤ b₀)
    (hi : ∀ i, Integrable (fun p => nestedSdeP (fun x => max (x - k i) 0) gh ℓ p -
        nestedTarget (fun x => max (x - k i) 0) g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP (fun x => max (x - k i) 0) gh ℓ p -
        nestedTarget (fun x => max (x - k i) 0) g ρ p) ∂(nestedLaw ν ρ)| ≤ b i) :
    Integrable (fun p => nestedSdeP f gh ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
        b₀ + ∑ i, |c i| * b i := by
  obtain ⟨i0, b0⟩ := h₀
  set D₀ : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => nestedSdeP f₀ gh ℓ p - nestedTarget f₀ g ρ p
  set D : ι → 𝒵 × (ℕ → 𝒲) → ℝ := fun i p =>
    nestedSdeP (fun x => max (x - k i) 0) gh ℓ p - nestedTarget (fun x => max (x - k i) 0) g ρ p
  have hD : ∀ p, nestedSdeP f gh ℓ p - nestedTarget f g ρ p = D₀ p + ∑ i, c i * D i p := by
    intro p
    have e1 : nestedSdeP f gh ℓ p = nestedSdeP f₀ gh ℓ p +
        ∑ i, c i * nestedSdeP (fun x => max (x - k i) 0) gh ℓ p := hf _
    have e2 : nestedTarget f g ρ p = nestedTarget f₀ g ρ p +
        ∑ i, c i * nestedTarget (fun x => max (x - k i) 0) g ρ p := hf _
    rw [e1, e2]
    simp only [D₀, D, mul_sub, Finset.sum_sub_distrib]
    ring
  have iS : Integrable (fun p => ∑ i, c i * D i p) (nestedLaw ν ρ) :=
    integrable_finsetSum _ fun i _ => ((hi i).1).const_mul (c i)
  have hint : Integrable (fun p => nestedSdeP f gh ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) :=
    (i0.add iS).congr (Eventually.of_forall fun p => (hD p).symm)
  refine ⟨hint, ?_⟩
  have e : ∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ p, D₀ p ∂(nestedLaw ν ρ) + ∑ i, c i * ∫ p, D i p ∂(nestedLaw ν ρ) := by
    rw [integral_congr_ae (Eventually.of_forall hD), integral_add i0 iS,
      integral_finsetSum _ fun i _ => ((hi i).1).const_mul (c i)]
    simp only [integral_const_mul]
    rfl
  have hbi : ∀ i, (2 : ℝ) ^ ℓ * |c i * ∫ p, D i p ∂(nestedLaw ν ρ)| ≤ |c i| * b i := fun i => by
    rw [abs_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hi i).2 (abs_nonneg _)
  have h2l0 : (0 : ℝ) ≤ 2 ^ ℓ := by positivity
  rw [e]
  calc (2 : ℝ) ^ ℓ * |∫ p, D₀ p ∂(nestedLaw ν ρ) + ∑ i, c i * ∫ p, D i p ∂(nestedLaw ν ρ)|
      ≤ (2 : ℝ) ^ ℓ * (|∫ p, D₀ p ∂(nestedLaw ν ρ)| +
          ∑ i, |c i * ∫ p, D i p ∂(nestedLaw ν ρ)|) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
          (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)) h2l0
    _ = (2 : ℝ) ^ ℓ * |∫ p, D₀ p ∂(nestedLaw ν ρ)| +
          ∑ i, (2 : ℝ) ^ ℓ * |c i * ∫ p, D i p ∂(nestedLaw ν ρ)| := by
        rw [mul_add, Finset.mul_sum]
    _ ≤ b₀ + ∑ i, |c i| * b i := add_le_add b0 (Finset.sum_le_sum fun i _ => hbi i)

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] in
/-- **The correction is linear in `f`, and so are its `L²` rates** (Giles 2015, §9.2, p. 60,
l. 2687–2690, for an `f` with several kinks): if `f = f₀ + ∑_i c_i max(· − k_i, 0)` and the
corrections `Y_{ℓ+1}` (`nestedSdeDelta`) of `f₀` and of each hinge `max(· − k_i, 0)` are
square-integrable with `2^{3ℓ/2} E[Y_{ℓ+1}²]` at most `B₀` and `B_i`, then that of `f` is
square-integrable and `2^{3ℓ/2} E[Y_{ℓ+1}²] ≤ (|ι| + 1)(B₀ + ∑_i c_i² B_i)`, by
`nestedSdeDelta_succ_kinks` and `(a + ∑_i b_i)² ≤ (|ι| + 1)(a² + ∑_i b_i²)` (`sq_add_sum_le`). -/
lemma nested_sde_variance_kinks_add {ι : Type*} [Fintype ι] {f f₀ : ℝ → ℝ} {c k : ι → ℝ}
    (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ} {ℓ : ℕ}
    {B₀ : ℝ} {B : ι → ℝ}
    (h₀ : MemLp (nestedSdeDelta f₀ gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedSdeDelta f₀ gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        B₀)
    (hi : ∀ i, MemLp (nestedSdeDelta (fun x => max (x - k i) 0) gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) *
        ∫ p, nestedSdeDelta (fun x => max (x - k i) 0) gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤ B i) :
    MemLp (nestedSdeDelta f gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        (Fintype.card ι + 1) * (B₀ + ∑ i, c i ^ 2 * B i) := by
  obtain ⟨h0m, hb0⟩ := h₀
  set Y₀ := nestedSdeDelta f₀ gh (ℓ + 1)
  set Y : ι → 𝒵 × (ℕ → 𝒲) → ℝ := fun i => nestedSdeDelta (fun x => max (x - k i) 0) gh (ℓ + 1)
  have hY : ∀ p, nestedSdeDelta f gh (ℓ + 1) p = Y₀ p + ∑ i, c i * Y i p :=
    nestedSdeDelta_succ_kinks hf gh ℓ
  have hmem : MemLp (nestedSdeDelta f gh (ℓ + 1)) 2 (nestedLaw ν ρ) := by
    have hsum := h0m.add (memLp_finsetSum Finset.univ fun i _ => (hi i).1.const_mul (c i))
    convert hsum using 1
    funext p
    exact hY p
  refine ⟨hmem, ?_⟩
  -- pointwise Cauchy–Schwarz, integrated
  have i0 : Integrable (fun p => Y₀ p ^ 2) (nestedLaw ν ρ) := h0m.integrable_sq
  have ii : ∀ i, Integrable (fun p => Y i p ^ 2) (nestedLaw ν ρ) := fun i =>
    (hi i).1.integrable_sq
  have iS : Integrable (fun p => ∑ i, c i ^ 2 * Y i p ^ 2) (nestedLaw ν ρ) :=
    integrable_finsetSum _ fun i _ => (ii i).const_mul _
  have iF : Integrable (fun p => (Fintype.card ι + 1 : ℝ) * (Y₀ p ^ 2 +
      ∑ i, c i ^ 2 * Y i p ^ 2)) (nestedLaw ν ρ) := (i0.add iS).const_mul _
  have hpt : ∀ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ≤
      (Fintype.card ι + 1 : ℝ) * (Y₀ p ^ 2 + ∑ i, c i ^ 2 * Y i p ^ 2) := fun p => by
    rw [hY p]
    have h := sq_add_sum_le (Y₀ p) fun i => c i * Y i p
    simp only [mul_pow] at h
    exact h
  have hint : ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
      (Fintype.card ι + 1 : ℝ) * (∫ p, Y₀ p ^ 2 ∂(nestedLaw ν ρ) +
        ∑ i, c i ^ 2 * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ)) := by
    have h := integral_mono hmem.integrable_sq iF hpt
    rw [integral_const_mul, integral_add i0 iS,
      integral_finsetSum _ fun i _ => (ii i).const_mul _] at h
    simpa only [integral_const_mul] using h
  set r : ℝ := (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ)
  have hr0 : 0 ≤ r := by positivity
  have hbi : ∀ i, r * (c i ^ 2 * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ)) ≤ c i ^ 2 * B i := fun i =>
    calc r * (c i ^ 2 * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ))
        = c i ^ 2 * (r * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ)) := by ring
      _ ≤ c i ^ 2 * B i := mul_le_mul_of_nonneg_left (hi i).2 (sq_nonneg _)
  have hcard : (0 : ℝ) ≤ Fintype.card ι + 1 := by positivity
  calc r * ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)
      ≤ r * ((Fintype.card ι + 1 : ℝ) * (∫ p, Y₀ p ^ 2 ∂(nestedLaw ν ρ) +
        ∑ i, c i ^ 2 * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ))) := mul_le_mul_of_nonneg_left hint hr0
    _ = (Fintype.card ι + 1 : ℝ) * (r * ∫ p, Y₀ p ^ 2 ∂(nestedLaw ν ρ) +
        ∑ i, r * (c i ^ 2 * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ))) := by
          rw [← Finset.mul_sum]
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hb0 (Finset.sum_le_sum fun i _ => hbi i)) hcard

/-- **Theorem 1 for nested simulation with `2^ℓ` timesteps, from the rates `α = 1` and `β = 3/2`**
(Giles 2015, §9.2, p. 60, l. 2687–2690: "we would get `β = 1.5`, and hence an overall complexity
which is `O(ε^{−2.5})`"; Theorem 1 of §2.1 with `γ = 2`).  If `P₀ ∈ L²`, the bias integrands
`P_ℓ − f(E_W[g(Z, W)])` are integrable with `2^ℓ |E[·]| ≤ B₁`, the corrections `Y_{ℓ+1}`
(`nestedSdeDelta`) are square-integrable with `2^{3ℓ/2} E[Y_{ℓ+1}²] ≤ B₂`, and the inner
approximations converge weakly uniformly in the outer sample (so that `E_W[g(Z, W)]` is
a.e.-measurable, `aemeasurable_condMean_of_weak`), then for independent inputs of law
`ν ⊗ ρ^{⊗ℕ}` and level costs of mean `C_ℓ ≤ c₃ 4^ℓ` there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the squared error of the MLMC estimator of
`E_Z[f(E_W[g(Z, W)])]` is integrable, its mean is `< ε²` and the expected cost is
`≤ c₄ ε^{−2.5}` (`giles_theorem1_corrections`, with `ε^{−2−(γ−β)/α} = ε^{−2.5}`). -/
lemma nested_sde_mlmc_complexity_of_rates {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ℝ → ℝ} (hfm : Measurable f) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {g : 𝒵 → 𝒲 → ℝ} {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w) {B₁ B₂ : ℝ}
    (hP0 : MemLp (nestedSdeP f gh 0) 2 (nestedLaw ν ρ))
    (hbias : ∀ ℓ, Integrable (fun p => nestedSdeP f gh ℓ p - nestedTarget f g ρ p)
        (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤ B₁)
    (hvar : ∀ ℓ, MemLp (nestedSdeDelta f gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤ B₂)
    (ω : ℕ × ℕ → Ω → 𝒵 × (ℕ → 𝒲)) (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw ν ρ))
    (hind : iIndepFun ω μ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * 4 ^ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedSdeDelta f gh) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2) μ ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedSdeDelta f gh) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * ε ^ (-2.5 : ℝ) := by
  have hμ : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  -- integrability: `f(E_W[g])` and every `P_ℓ` through the bias integrands
  have hP : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) :=
    ((hP0.integrable one_le_two).sub (hbias 0).1).congr (Eventually.of_forall fun p => by simp)
  have hPl : ∀ ℓ, Integrable (nestedSdeP f gh ℓ) (nestedLaw ν ρ) := fun ℓ =>
    ((hbias ℓ).1.add hP).congr (Eventually.of_forall fun p => by simp)
  have hGm : AEMeasurable (fun z => ∫ v, g z v ∂ρ) ν := aemeasurable_condMean_of_weak ν ρ hgh hw
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hΔm : ∀ ℓ, Measurable (nestedSdeDelta f gh ℓ) := measurable_nestedSdeDelta hfm hgh
  have hΔ : ∀ ℓ, MemLp (nestedSdeDelta f gh ℓ) 2 (nestedLaw ν ρ) := fun ℓ => by
    cases ℓ with
    | zero => exact hP0
    | succ ℓ => exact (hvar ℓ).1
  -- (i) the bias, `α = 1`
  have h_i : ∀ ℓ : ℕ, |∫ y, nestedSdeP f gh ℓ y - nestedTarget f g ρ y ∂(nestedLaw ν ρ)| ≤
      (|B₁| + 1) * (2 : ℝ) ^ (-((1 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hb := (hbias ℓ).2
    rw [one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast 2 ℓ,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    linarith [le_abs_self B₁]
  -- (iii) the variance, `β = 3/2`
  have h_iii : ∀ ℓ : ℕ, variance (nestedSdeDelta f gh ℓ) (nestedLaw ν ρ) ≤
      (variance (nestedSdeDelta f gh 0) (nestedLaw ν ρ) + 3 * |B₂| + 1) *
        (2 : ℝ) ^ (-((3 / 2 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hv0 := variance_nonneg (nestedSdeDelta f gh 0) (nestedLaw ν ρ)
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← div_eq_mul_inv]
    cases ℓ with
    | zero =>
      rw [Nat.cast_zero, mul_zero, Real.rpow_zero, div_one]
      linarith [abs_nonneg B₂]
    | succ ℓ =>
      have hv : variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) ≤
          ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) := by
        simpa only [Pi.pow_apply] using
          variance_le_expectation_sq (hΔm (ℓ + 1)).aestronglyMeasurable
      have hr := (hvar ℓ).2
      -- `2^{3(ℓ+1)/2} = 2^{3/2} 2^{3ℓ/2} ≤ 3 · 2^{3ℓ/2}`
      have h32 : (2 : ℝ) ^ ((3 / 2 : ℝ) * ((ℓ + 1 : ℕ) : ℝ)) ≤
          3 * (2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ)) := by
        have e : (3 / 2 : ℝ) * ((ℓ + 1 : ℕ) : ℝ) = 3 / 2 + (3 / 2 : ℝ) * (ℓ : ℝ) := by
          push_cast
          ring
        rw [e, Real.rpow_add (by norm_num)]
        gcongr
        have h8 : (2 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt 8 := by
          rw [Real.sqrt_eq_rpow, show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [h8, Real.sqrt_le_left (by norm_num)]
        norm_num
      rw [le_div_iff₀ (by positivity)]
      have hvnn : 0 ≤ variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) :=
        variance_nonneg _ _
      calc variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) *
            (2 : ℝ) ^ ((3 / 2 : ℝ) * ((ℓ + 1 : ℕ) : ℝ))
          ≤ variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) *
            (3 * (2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ))) := mul_le_mul_of_nonneg_left h32 hvnn
        _ = 3 * ((2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ)) *
            variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ)) := by ring
        _ ≤ 3 * ((2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ)) *
            ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)) := by gcongr
        _ ≤ 3 * B₂ := by linarith
        _ ≤ variance (nestedSdeDelta f gh 0) (nestedLaw ν ρ) + 3 * |B₂| + 1 := by
            linarith [le_abs_self B₂]
  -- (iv) the cost, `γ = 2`
  have h_iv : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ ((2 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, Real.rpow_natCast]
    norm_num
    exact hC ℓ
  have hc₁ : 0 < |B₁| + 1 := by positivity
  have hc₂ : 0 < variance (nestedSdeDelta f gh 0) (nestedLaw ν ρ) + 3 * |B₂| + 1 := by
    have := variance_nonneg (nestedSdeDelta f gh 0) (nestedLaw ν ρ)
    positivity
  have hαβγ : min (3 / 2 : ℝ) 2 / 2 ≤ 1 := by norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_corrections (nestedTarget f g ρ) (nestedSdeP f gh)
    (nestedSdeDelta f gh) ω cost C one_pos (by norm_num) two_pos hc₁ hc₂ hc₃ hαβγ hω hind hP hPl
    hΔm hΔ hcost hcostC h_i (integral_nestedSdeDelta ν ρ f gh hPl) h_iii h_iv
  -- the quantity of interest is `E_Z[f(E_W[g(Z, W)])]`
  have hPint : ∫ y, nestedTarget f g ρ y ∂(nestedLaw ν ρ) = ∫ z, f (∫ v, g z v ∂ρ) ∂ν :=
    integral_comp_of_measurePreserving hfst (hfm.comp_aemeasurable hGm).aestronglyMeasurable
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost'⟩ := h ε hε hε1
  rw [hPint] at hmse
  rw [complexityBound_of_gt (by norm_num) ε, show (-2 - (2 - 3 / 2) / 1 : ℝ) = -2.5 by norm_num]
    at hcost'
  exact ⟨L, N, hN, ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω hΔ ℓ (N ℓ)).sub
    (memLp_const _)).integrable_sq, hmse, hcost'⟩

/-! #### Curved pieces -/

/-- **`α = 1` for an `f` with several kinks and curved pieces, with `2^ℓ` timesteps** (Giles 2015,
§9.2, p. 60, l. 2687–2690: "if the function `f` is continuous and piecewise differentiable, rather
than being twice differentiable, then in the MLMC treatment we would get `β = 1.5`, and hence an
overall complexity which is `O(ε^{−2.5})`", which is Theorem 1 with `α = 1`, `β = 1.5`, `γ = 2`).
Let `f = f₀ + ∑_{i ∈ ι} c_i max(· − k_i, 0)` with finitely many kinks `k_i` and `f₀` differentiable
with a `K`-Lipschitz derivative, and let level `ℓ` use `2^ℓ` inner samples of the level-`ℓ`
approximation `g_ℓ` of the inner quantity `g` (`nestedSdeP`).  Hypotheses (this formalisation's;
the paper states none for this case, and the weak order of the time discretisation is not
formalised): `E[g_ℓ(Z, W)⁴] ≤ m₄`; the centred conditional fourth moments are bounded,
`E_W[(g_ℓ(z, W) − E_W[g_ℓ(z, W)])⁴] ≤ κ₄` for `ν`-a.e. `z`; first order weak convergence uniformly
in the outer sample, `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w`; and the small-ball bounds
`ν{|E_W[g(Z, W)] − k_i| ≤ t} ≤ c_{d,i} t` at each kink, for the exact conditional mean only.  (By
the others, `hm₄` holds with `m₄ = 8κ₄ + 64(E[g₀(Z, W)⁴] + 16 c_w⁴)`, and `hgh4 ℓ` for `ℓ ≥ 1`
adds to them only the integrability of `g_ℓ(z, ·)⁴` for `ν`-a.e. `z`; they are kept to name the
constant `m₄`.)  Then `P_ℓ − f(E_W[g(Z, W)])` is integrable and
`2^ℓ |E[P_ℓ − f(E_W[g(Z, W)])]| ≤ (K/2)(1 + 16 m₄) + c_w (|f₀′(0)| + K (1 + m₄)) + (K/2) c_w² +
∑_i |c_i| (4 c_{d,i} (1 + 80 κ₄)(1 + c_w) + c_w)`.
Proof: the bias is linear in `f` (`nested_sde_bias_kinks_add`); the curved part has bias
`O(2^{−ℓ})` (`nested_sde_bias_le_of_weak`) and so has each hinge (`nested_kink_sde_bias_rate`).
No measurability or moment of the exact `g` is assumed: it enters only through its conditional
mean, the a.e. limit of the `E_W[g_ℓ(z, W)]`.  For `f₀` affine (`K = 0`) and one kink the bound
is that of `nested_kink_sde_bias_rate`, but the hypotheses are stronger: the joint fourth moments
(`hgh4`) exclude an outer state with `E[g⁴] = ∞` (e.g. Student-`t` with three degrees of freedom),
which the one-kink result allows; `nested_piecewise_linear_sde_bias_rate` covers a piecewise
linear `f` with several kinks under the one-kink hypotheses.  Deviation: `f` is given through the
decomposition above rather than as a continuous, piecewise differentiable function. -/
theorem nested_kinks_sde_bias_rate {ι : Type*} [Fintype ι] {f f₀ f₀' : ℝ → ℝ} {K : ℝ}
    {c k c_d : ι → ℝ} (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0)
    (hf₀ : ∀ x, HasDerivAt f₀ (f₀' x) x) (hf₀' : ∀ x y, x ≤ y → |f₀' y - f₀' x| ≤ K * (y - x))
    {gh : ℕ → 𝒵 → 𝒲 → ℝ} (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ κ₄ : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hcent : ∀ ℓ, ∀ᵐ z ∂ν, ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ κ₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ i, ∀ t : ℝ, 0 < t →
      ν {z | |∫ v, g z v ∂ρ - k i| ≤ t} ≤ ENNReal.ofReal (c_d i * t)) (ℓ : ℕ) :
    Integrable (fun p => nestedSdeP f gh ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
        K / 2 * (1 + 16 * m₄) + c_w * (|f₀' 0| + K * (1 + m₄)) + K / 2 * c_w ^ 2 +
          ∑ i, |c i| * (4 * c_d i * (1 + 80 * κ₄) * (1 + c_w) + c_w) := by
  have hhinge : ∀ i, ∀ x, (fun x => max (x - k i) 0) x = 0 + 0 * x + 1 * max (x - k i) 0 :=
    fun i x => by ring
  have hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ κ₄ := fun ℓ =>
    ((hgh4 ℓ).prod_right_ae.and (hcent ℓ)).mono fun z hz => hz
  have hi : ∀ i, Integrable (fun p => nestedSdeP (fun x => max (x - k i) 0) gh ℓ p -
        nestedTarget (fun x => max (x - k i) 0) g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP (fun x => max (x - k i) 0) gh ℓ p -
        nestedTarget (fun x => max (x - k i) 0) g ρ p) ∂(nestedLaw ν ρ)| ≤
          4 * c_d i * (1 + 80 * κ₄) * (1 + c_w) + c_w := fun i => by
    obtain ⟨h1, h2⟩ := nested_kink_sde_bias_rate ν ρ (hhinge i) hgh hfib hw (hball i) ℓ
    rw [abs_one, abs_zero, zero_add, mul_one, one_mul] at h2
    exact ⟨h1, h2⟩
  exact nested_sde_bias_kinks_add ν ρ hf (nested_sde_bias_le_of_weak ν ρ hf₀ hf₀' hgh hgh4 hm₄ hw ℓ)
    hi

/-- **`β = 3/2` for an `f` with several kinks and curved pieces, with `2^ℓ` timesteps** (Giles 2015,
§9.2, p. 60, l. 2687–2690: "if the function `f` is continuous and piecewise differentiable, rather
than being twice differentiable, then in the MLMC treatment we would get `β = 1.5`").  Let
`f = f₀ + ∑_{i ∈ ι} c_i max(· − k_i, 0)` with finitely many kinks `k_i` and `f₀` differentiable with
a `K`-Lipschitz derivative, and let level `ℓ + 1` use the correction `Y_{ℓ+1}` with `2^{ℓ+1}` inner
samples of `g_{ℓ+1}` and twice `2^ℓ` of `g_ℓ` (`nestedSdeDelta`).  Hypotheses (this formalisation's;
the paper states none for this case, and the orders of the time discretisation are not formalised):
`E[g_ℓ(Z, W)⁴] ≤ m₄`; first order strong convergence in `L⁴`,
`(2^ℓ)⁴ E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))⁴] ≤ cₛ`; bounded centred conditional fourth moments
`E_W[(g_ℓ(z, W) − E_W[g_ℓ(z, W)])⁴] ≤ κ₄` for `ν`-a.e. `z`; first order weak convergence uniformly
in the outer sample, `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w`; and the small-ball bounds
`ν{|E_W[g(Z, W)] − k_i| ≤ t} ≤ c_{d,i} t`.  (`hm₄` and `hgh4` are as in
`nested_kinks_sde_bias_rate`.)  Then `Y_{ℓ+1}` is square-integrable and
`2^{3ℓ/2} E[Y_{ℓ+1}²] ≤ (|ι| + 1)(B₀ + ∑_i c_i² B_i)` with
`B₀ = 3 (K/8)² 224 m₄ + (3/2)(8(|f₀′(0)|⁴ + K⁴ m₄) + (1 + K²/2) cₛ)` and
`B_i = 6 c_{d,i} (1 + 16 κ₄)(1 + c_w) + (3/2)((9/4) c_w² + (1 + cₛ)/2)`, i.e. `V_ℓ = O(2^{−3ℓ/2})`.
Proof: `Y_{ℓ+1}` is linear in `f` (`nested_sde_variance_kinks_add`); its curved part is
`O(2^{−ℓ})` in `L²` (`nested_sde_variance_rate`, `β = 2`), each hinge part `O(2^{−3ℓ/4})`
(`nested_kink_sde_variance_rate`, with the strong order `¼` in `L²` from
`strong_quarter_of_strong_four`).  The hypothesis `hs` is the Milstein-level one of
`nested_sde_variance_rate`, where it gives `β = 2` for the curved part; it is stronger than
`β = 3/2` needs (the hinges need only the strong order `¼` in `L²`, which it implies with a large
margin, and for the curved part the averaging over `2^ℓ` inner samples would let a lower strong
order do; not formalised), and it excludes the Euler–Maruyama scheme (strong order `½`).  So, even
for `f₀` affine
and one kink, the hypotheses are stronger than those of `nested_kink_sde_variance_rate` (also by
the joint fourth moments `hgh4`); `nested_piecewise_linear_sde_variance_rate` covers a piecewise
linear `f` with several kinks under the one-kink hypotheses.  Deviation: `f` is given through the
decomposition above rather than as a continuous, piecewise differentiable function. -/
theorem nested_kinks_sde_variance_rate {ι : Type*} [Fintype ι] {f f₀ f₀' : ℝ → ℝ} {K : ℝ}
    {c k c_d : ι → ℝ} (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0)
    (hf₀ : ∀ x, HasDerivAt f₀ (f₀' x) x) (hf₀' : ∀ x y, x ≤ y → |f₀' y - f₀' x| ≤ K * (y - x))
    {gh : ℕ → 𝒵 → 𝒲 → ℝ} (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ κ₄ cₛ : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hcent : ∀ ℓ, ∀ᵐ z ∂ν, ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ κ₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ)
    {g : 𝒵 → 𝒲 → ℝ} {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ i, ∀ t : ℝ, 0 < t →
      ν {z | |∫ v, g z v ∂ρ - k i| ≤ t} ≤ ENNReal.ofReal (c_d i * t)) (ℓ : ℕ) :
    MemLp (nestedSdeDelta f gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        (Fintype.card ι + 1) * (3 * ((K / 8) ^ 2 * (224 * m₄)) +
          3 / 2 * (8 * (|f₀' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2) * cₛ) +
          ∑ i, c i ^ 2 * (6 * c_d i * (1 + 16 * κ₄) * (1 + c_w) +
            3 / 2 * (9 / 4 * c_w ^ 2 + (1 + cₛ) / 2))) := by
  have hhinge : ∀ i, ∀ x, (fun x => max (x - k i) 0) x = 0 + 0 * x + 1 * max (x - k i) 0 :=
    fun i x => by ring
  have hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ κ₄ := fun ℓ =>
    ((hgh4 ℓ).prod_right_ae.and (hcent ℓ)).mono fun z hz => hz
  have hs2 := strong_quarter_of_strong_four ν ρ hgh hgh4 hs
  -- the curved part: `(2^ℓ)² E[Y(f₀)²] ≤ B₀` and `2^{3ℓ/2} ≤ (2^ℓ)²`
  have h0 : MemLp (nestedSdeDelta f₀ gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedSdeDelta f₀ gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        3 * ((K / 8) ^ 2 * (224 * m₄)) +
          3 / 2 * (8 * (|f₀' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2) * cₛ) := by
    obtain ⟨h0m, h0b⟩ := nested_sde_variance_rate ν ρ hf₀ hf₀' hgh hgh4 hm₄ hs ℓ
    have hr4 : (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) ≤ ((2 : ℝ) ^ ℓ) ^ 2 := by
      rw [← pow_mul, ← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) ℓ]
    have hY0 : 0 ≤ ∫ p, nestedSdeDelta f₀ gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) :=
      integral_nonneg fun p => sq_nonneg _
    exact ⟨h0m, (mul_le_mul_of_nonneg_right hr4 hY0).trans h0b⟩
  -- the hinges
  have hi : ∀ i, MemLp (nestedSdeDelta (fun x => max (x - k i) 0) gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) *
        ∫ p, nestedSdeDelta (fun x => max (x - k i) 0) gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
          6 * c_d i * (1 + 16 * κ₄) * (1 + c_w) + 3 / 2 * (9 / 4 * c_w ^ 2 + (1 + cₛ) / 2) :=
    fun i => by
      obtain ⟨h1, h2⟩ := nested_kink_sde_variance_rate ν ρ (hhinge i) hgh hfib hw (hball i) hs2 ℓ
      simp only [one_pow, mul_one, abs_zero, abs_one, zero_add] at h2
      exact ⟨h1, h2⟩
  exact nested_sde_variance_kinks_add ν ρ hf h0 hi

/-- **MLMC for nested simulation with `2^ℓ` timesteps and an `f` with several kinks and curved
pieces has complexity `O(ε^{−2.5})`** (Giles 2015, §9.2, p. 60, l. 2687–2690: "Following the
analysis in (Bujok et al. 2013), if the function `f` is continuous and piecewise differentiable,
rather than being twice differentiable, then in the MLMC treatment we would get `β = 1.5`, and
hence an overall complexity which is `O(ε^{−2.5})`").  Let `f = f₀ + ∑_{i ∈ ι} c_i max(· − k_i, 0)`
with finitely many kinks `k_i` and `f₀` differentiable with a `K`-Lipschitz derivative, and let
level `ℓ` use `2^ℓ` inner samples of the level-`ℓ` approximation `g_ℓ` (`nestedSdeP`,
`nestedSdeDelta`), under the hypotheses of `nested_kinks_sde_bias_rate` and
`nested_kinks_sde_variance_rate` (this formalisation's: `E[g_ℓ(Z, W)⁴] ≤ m₄`, first order strong
convergence in `L⁴`, bounded centred conditional fourth moments, first order weak convergence
uniformly in the outer sample, and a small-ball bound for the exact conditional mean `E_W[g(Z, W)]`
at each kink).  Let the inputs `ω^{(ℓ,n)}` be independent with law `ν ⊗ ρ^{⊗ℕ}` and let the
level-`ℓ` cost have mean `C_ℓ ≤ c₃ 4^ℓ` (twice as many timesteps and twice as many inner samples per
level).  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for
which the squared error of the MLMC estimator of `E_Z[f(E_W[g(Z, W)])]` is integrable, its mean
(the mean square error) is `< ε²`, and the expected cost is `≤ c₄ ε^{−2.5}`: Theorem 1
(`nested_sde_mlmc_complexity_of_rates`) with `α = 1` (`nested_kinks_sde_bias_rate`), `β = 3/2`
(`nested_kinks_sde_variance_rate`) and `γ = 2`, so `ε^{−2−(γ−β)/α} = ε^{−2.5}`.  That `μ` is a
probability measure follows from the independence of the inputs.  This combines
`nested_sde_mlmc_complexity` (smooth `f`) and `nested_kink_sde_mlmc_complexity` (one kink, `f`
piecewise linear), and is the analogue with discretised inner samples (`γ = 2`) of
`nested_kinks_mlmc_complexity` (exact inner samples, `γ = 1`, `O(ε⁻²)`).  It does not contain the
one-kink result: even for `f₀` affine, its hypotheses are stronger (joint fourth moments and first
order strong convergence in `L⁴`, which exclude the Euler–Maruyama scheme and an outer state with
`E[g⁴] = ∞`); `nested_piecewise_linear_sde_mlmc_complexity` covers a piecewise linear `f` with
several kinks under the one-kink hypotheses.  Deviation: `f` is given through the decomposition
above rather than as a continuous, piecewise differentiable function. -/
theorem nested_kinks_sde_mlmc_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} [Fintype ι] {f f₀ f₀' : ℝ → ℝ} {K : ℝ}
    {c k c_d : ι → ℝ} (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0)
    (hf₀ : ∀ x, HasDerivAt f₀ (f₀' x) x) (hf₀' : ∀ x y, x ≤ y → |f₀' y - f₀' x| ≤ K * (y - x))
    {gh : ℕ → 𝒵 → 𝒲 → ℝ} (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ κ₄ cₛ : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hcent : ∀ ℓ, ∀ᵐ z ∂ν, ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ κ₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ)
    {g : 𝒵 → 𝒲 → ℝ} {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ i, ∀ t : ℝ, 0 < t →
      ν {z | |∫ v, g z v ∂ρ - k i| ≤ t} ≤ ENNReal.ofReal (c_d i * t))
    (ω : ℕ × ℕ → Ω → 𝒵 × (ℕ → 𝒲)) (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw ν ρ))
    (hind : iIndepFun ω μ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * 4 ^ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedSdeDelta f gh) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2) μ ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedSdeDelta f gh) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * ε ^ (-2.5 : ℝ) :=
  nested_sde_mlmc_complexity_of_rates ν ρ (continuous_kinks hf hf₀).measurable hgh hw
    ((memLp_nestedP_kinks ν ρ hf hf₀ hf₀' (hgh 0) (hgh4 0)).1 0)
    (nested_kinks_sde_bias_rate ν ρ hf hf₀ hf₀' hgh hgh4 hm₄ hcent hw hball)
    (nested_kinks_sde_variance_rate ν ρ hf hf₀ hf₀' hgh hgh4 hm₄ hcent hs hw hball)
    ω hω hind cost C hc₃ hcost hcostC hC

/-! #### A piecewise linear `f` under the one-kink hypotheses -/

/-- **`α = 1` for a piecewise linear `f` with several kinks, with `2^ℓ` timesteps** (Giles 2015,
§9.2, p. 60, l. 2687–2690: "if the function `f` is continuous and piecewise differentiable, rather
than being twice differentiable, then in the MLMC treatment we would get `β = 1.5`, and hence an
overall complexity which is `O(ε^{−2.5})`", which is Theorem 1 with `α = 1`, `β = 1.5`, `γ = 2`).
Let `f(x) = a₀ + a₁x + ∑_{i ∈ ι} c_i max(x − k_i, 0)` with finitely many kinks `k_i`, at least one
(`ι` nonempty), and let level `ℓ` use `2^ℓ` inner samples of the level-`ℓ` approximation `g_ℓ` of
the inner quantity `g` (`nestedSdeP`).  Hypotheses: those of `nested_kink_sde_bias_rate`, with a
small ball at each kink (this formalisation's; the paper states none for this case, and the weak
order of the time discretisation is not formalised): the centred conditional fourth moments are
bounded, `E_W[(g_ℓ(z, W) − E_W[g_ℓ(z, W)])⁴] ≤ κ₄` for `ν`-a.e. `z` (with `g_ℓ(z, ·)⁴`
integrable), so the conditional mean may be unbounded and `E[g_ℓ(Z, W)⁴]` may be infinite; first
order weak convergence uniformly in the outer sample, `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w`;
and `ν{|E_W[g(Z, W)] − k_i| ≤ t} ≤ c_{d,i} t` at each kink, for the exact conditional mean only.
Then `P_ℓ − f(E_W[g(Z, W)])` is integrable and
`2^ℓ |E[P_ℓ − f(E_W[g(Z, W)])]| ≤ |a₁| c_w + ∑_i |c_i| (4 c_{d,i} (1 + 80 κ₄)(1 + c_w) + c_w)`;
with one kink this is the bound of `nested_kink_sde_bias_rate`, which it extends to several kinks.
Proof: the bias is linear in `f` (`nested_sde_bias_kinks_add`), and `nested_kink_sde_bias_rate`
applies to the affine part (as a kink with coefficient `0` at one of the `k_i`) and to each hinge.
Deviation: `f` is piecewise linear rather than continuous and piecewise differentiable (see
`nested_kinks_sde_bias_rate` for curved pieces, under stronger hypotheses). -/
theorem nested_piecewise_linear_sde_bias_rate {ι : Type*} [Fintype ι] [Nonempty ι] {f : ℝ → ℝ}
    {a₀ a₁ : ℝ} {c k c_d : ι → ℝ} (hf : ∀ x, f x = a₀ + a₁ * x + ∑ i, c i * max (x - k i) 0)
    {gh : ℕ → 𝒵 → 𝒲 → ℝ} (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {κ₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ κ₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ i, ∀ t : ℝ, 0 < t →
      ν {z | |∫ v, g z v ∂ρ - k i| ≤ t} ≤ ENNReal.ofReal (c_d i * t)) (ℓ : ℕ) :
    Integrable (fun p => nestedSdeP f gh ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
        |a₁| * c_w + ∑ i, |c i| * (4 * c_d i * (1 + 80 * κ₄) * (1 + c_w) + c_w) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hF : ∀ x, (fun x => a₀ + a₁ * x) x = a₀ + a₁ * x + 0 * max (x - k i₀) 0 :=
    fun x => by ring
  have hhinge : ∀ i, ∀ x, (fun x => max (x - k i) 0) x = 0 + 0 * x + 1 * max (x - k i) 0 :=
    fun i x => by ring
  have h0 : Integrable (fun p => nestedSdeP (fun x => a₀ + a₁ * x) gh ℓ p -
        nestedTarget (fun x => a₀ + a₁ * x) g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP (fun x => a₀ + a₁ * x) gh ℓ p -
        nestedTarget (fun x => a₀ + a₁ * x) g ρ p) ∂(nestedLaw ν ρ)| ≤ |a₁| * c_w := by
    obtain ⟨h1, h2⟩ := nested_kink_sde_bias_rate ν ρ hF hgh hfib hw (hball i₀) ℓ
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    rw [abs_zero, add_zero]
    ring
  have hi : ∀ i, Integrable (fun p => nestedSdeP (fun x => max (x - k i) 0) gh ℓ p -
        nestedTarget (fun x => max (x - k i) 0) g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP (fun x => max (x - k i) 0) gh ℓ p -
        nestedTarget (fun x => max (x - k i) 0) g ρ p) ∂(nestedLaw ν ρ)| ≤
          4 * c_d i * (1 + 80 * κ₄) * (1 + c_w) + c_w := fun i => by
    obtain ⟨h1, h2⟩ := nested_kink_sde_bias_rate ν ρ (hhinge i) hgh hfib hw (hball i) ℓ
    rw [abs_one, abs_zero, zero_add, mul_one, one_mul] at h2
    exact ⟨h1, h2⟩
  exact nested_sde_bias_kinks_add ν ρ (f₀ := fun x => a₀ + a₁ * x) hf h0 hi

/-- **`β = 3/2` for a piecewise linear `f` with several kinks, with `2^ℓ` timesteps** (Giles 2015,
§9.2, p. 60, l. 2687–2690: "if the function `f` is continuous and piecewise differentiable, rather
than being twice differentiable, then in the MLMC treatment we would get `β = 1.5`").  Let
`f(x) = a₀ + a₁x + ∑_{i ∈ ι} c_i max(x − k_i, 0)` with finitely many kinks `k_i`, at least one, and
let level `ℓ + 1` use the correction `Y_{ℓ+1}` with `2^{ℓ+1}` inner samples of `g_{ℓ+1}` and twice
`2^ℓ` of `g_ℓ` (`nestedSdeDelta`).  Hypotheses: those of `nested_kink_sde_variance_rate`, with a
small ball at each kink (this formalisation's; the paper states none for this case, and the orders
of the time discretisation are not formalised): bounded centred conditional fourth moments
`E_W[(g_ℓ(z, W) − E_W[g_ℓ(z, W)])⁴] ≤ κ₄` for `ν`-a.e. `z`; first order weak convergence uniformly
in the outer sample, `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w`; strong convergence of order `¼`
in `L²`, `2^{ℓ/2} E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))²] ≤ cₛ`, which the strong order `½` of the
Euler–Maruyama scheme already implies; and `ν{|E_W[g(Z, W)] − k_i| ≤ t} ≤ c_{d,i} t` at each kink.
Then `Y_{ℓ+1}` is square-integrable and
`2^{3ℓ/2} E[Y_{ℓ+1}²] ≤ (|ι| + 1)((3/2) a₁² ((9/4) c_w² + cₛ) +
∑_i c_i² (6 c_{d,i} (1 + 16 κ₄)(1 + c_w) + (3/2)((9/4) c_w² + cₛ)))`, i.e. `V_ℓ = O(2^{−3ℓ/2})`.
This extends `nested_kink_sde_variance_rate` to several kinks: with one kink the hypotheses are the
same and the constant is at most twice its constant (`(|a₁| + |c|)² ≤ 2(a₁² + c²)`).
Proof: `Y_{ℓ+1}` is linear in `f`
(`nested_sde_variance_kinks_add`), and `nested_kink_sde_variance_rate` applies to the affine part
(as a kink with coefficient `0` at one of the `k_i`) and to each hinge.  Deviation: `f` is
piecewise linear rather than continuous and piecewise differentiable (see
`nested_kinks_sde_variance_rate` for curved pieces, under stronger hypotheses). -/
theorem nested_piecewise_linear_sde_variance_rate {ι : Type*} [Fintype ι] [Nonempty ι]
    {f : ℝ → ℝ} {a₀ a₁ : ℝ} {c k c_d : ι → ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + ∑ i, c i * max (x - k i) 0)
    {gh : ℕ → 𝒵 → 𝒲 → ℝ} (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {κ₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ κ₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w cₛ : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ i, ∀ t : ℝ, 0 < t →
      ν {z | |∫ v, g z v ∂ρ - k i| ≤ t} ≤ ENNReal.ofReal (c_d i * t))
    (hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ cₛ) (ℓ : ℕ) :
    MemLp (nestedSdeDelta f gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        (Fintype.card ι + 1) * (3 / 2 * a₁ ^ 2 * (9 / 4 * c_w ^ 2 + cₛ) +
          ∑ i, c i ^ 2 * (6 * c_d i * (1 + 16 * κ₄) * (1 + c_w) +
            3 / 2 * (9 / 4 * c_w ^ 2 + cₛ))) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hF : ∀ x, (fun x => a₀ + a₁ * x) x = a₀ + a₁ * x + 0 * max (x - k i₀) 0 :=
    fun x => by ring
  have hhinge : ∀ i, ∀ x, (fun x => max (x - k i) 0) x = 0 + 0 * x + 1 * max (x - k i) 0 :=
    fun i x => by ring
  have h0 : MemLp (nestedSdeDelta (fun x => a₀ + a₁ * x) gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedSdeDelta (fun x => a₀ + a₁ * x) gh (ℓ + 1) p ^ 2
        ∂(nestedLaw ν ρ) ≤ 3 / 2 * a₁ ^ 2 * (9 / 4 * c_w ^ 2 + cₛ) := by
    obtain ⟨h1, h2⟩ := nested_kink_sde_variance_rate ν ρ hF hgh hfib hw (hball i₀) hs ℓ
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    rw [abs_zero, add_zero, sq_abs]
    ring
  have hi : ∀ i, MemLp (nestedSdeDelta (fun x => max (x - k i) 0) gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) *
        ∫ p, nestedSdeDelta (fun x => max (x - k i) 0) gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
          6 * c_d i * (1 + 16 * κ₄) * (1 + c_w) + 3 / 2 * (9 / 4 * c_w ^ 2 + cₛ) := fun i => by
    obtain ⟨h1, h2⟩ := nested_kink_sde_variance_rate ν ρ (hhinge i) hgh hfib hw (hball i) hs ℓ
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    rw [abs_zero, abs_one, zero_add]
    ring
  exact nested_sde_variance_kinks_add ν ρ (f₀ := fun x => a₀ + a₁ * x) hf h0 hi

/-- **MLMC for nested simulation with `2^ℓ` timesteps and a piecewise linear `f` with several
kinks has complexity `O(ε^{−2.5})`** (Giles 2015, §9.2, p. 60, l. 2687–2690: "Following the
analysis in (Bujok et al. 2013), if the function `f` is continuous and piecewise differentiable,
rather than being twice differentiable, then in the MLMC treatment we would get `β = 1.5`, and
hence an overall complexity which is `O(ε^{−2.5})`").  Let `f(x) = a₀ + a₁x + ∑_{i ∈ ι} c_i
max(x − k_i, 0)` with finitely many kinks `k_i`, at least one, and let level `ℓ` use `2^ℓ` inner
samples of the level-`ℓ` approximation `g_ℓ` (`nestedSdeP`, `nestedSdeDelta`), under the hypotheses
of `nested_kink_sde_mlmc_complexity` with a small ball at each kink (this formalisation's: bounded
centred conditional fourth moments, first order weak convergence uniformly in the outer sample,
strong convergence of order `¼` in `L²`, implied by the Euler–Maruyama scheme, the small-ball bound
for the exact conditional mean `E_W[g(Z, W)]` at each kink, and `E[g₀(Z, W)²] < ∞`).  Let the inputs
`ω^{(ℓ,n)}` be independent with law `ν ⊗ ρ^{⊗ℕ}` and let the level-`ℓ` cost have mean
`C_ℓ ≤ c₃ 4^ℓ`.  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and
`N_ℓ ≥ 1` for which the squared error of the MLMC estimator of `E_Z[f(E_W[g(Z, W)])]` is
integrable, its mean is `< ε²`, and the expected cost is `≤ c₄ ε^{−2.5}`: Theorem 1
(`nested_sde_mlmc_complexity_of_rates`) with `α = 1` (`nested_piecewise_linear_sde_bias_rate`),
`β = 3/2` (`nested_piecewise_linear_sde_variance_rate`) and `γ = 2`; `P₀ ∈ L²` because each piece
of `f` is Lipschitz (`memLp_two_kink_comp`).  That `μ` is a probability measure follows from the
independence of the inputs.  This extends `nested_kink_sde_mlmc_complexity` to several kinks.
Deviation: `f` is piecewise linear rather than continuous and piecewise differentiable (see
`nested_kinks_sde_mlmc_complexity` for curved pieces, under stronger hypotheses). -/
theorem nested_piecewise_linear_sde_mlmc_complexity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ι : Type*} [Fintype ι] [Nonempty ι] {f : ℝ → ℝ} {a₀ a₁ : ℝ}
    {c k c_d : ι → ℝ} (hf : ∀ x, f x = a₀ + a₁ * x + ∑ i, c i * max (x - k i) 0)
    {gh : ℕ → 𝒵 → 𝒲 → ℝ} (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {κ₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ κ₄)
    (hg0 : Integrable (fun p : 𝒵 × 𝒲 => gh 0 p.1 p.2 ^ 2) (ν.prod ρ))
    {g : 𝒵 → 𝒲 → ℝ} {c_w cₛ : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ i, ∀ t : ℝ, 0 < t →
      ν {z | |∫ v, g z v ∂ρ - k i| ≤ t} ≤ ENNReal.ofReal (c_d i * t))
    (hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ cₛ)
    (ω : ℕ × ℕ → Ω → 𝒵 × (ℕ → 𝒲)) (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw ν ρ))
    (hind : iIndepFun ω μ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * 4 ^ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedSdeDelta f gh) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2) μ ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedSdeDelta f gh) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * ε ^ (-2.5 : ℝ) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hF : ∀ x, (fun x => a₀ + a₁ * x) x = a₀ + a₁ * x + 0 * max (x - k i₀) 0 :=
    fun x => by ring
  have hhinge : ∀ i, ∀ x, (fun x => max (x - k i) 0) x = 0 + 0 * x + 1 * max (x - k i) 0 :=
    fun i x => by ring
  have hfc : Continuous f := by
    rw [show f = fun x => a₀ + a₁ * x + ∑ i, c i * max (x - k i) 0 from funext hf]
    fun_prop
  -- `P₀ ∈ L²`: each piece of `f` is Lipschitz and `E[g₀(Z, W)²] < ∞`
  have hX := measurable_innerMean (hgh 0) (2 ^ 0) measurable_id
  have hX2 := (integral_innerMean_sq_le ν ρ (hgh 0) hg0 (M := 2 ^ 0) (by positivity)).1
  have hP0 : MemLp (nestedSdeP f gh 0) 2 (nestedLaw ν ρ) := by
    have h := (memLp_two_kink_comp hF hX hX2).add (memLp_finsetSum Finset.univ fun i _ =>
      (memLp_two_kink_comp (hhinge i) hX hX2).const_mul (c i))
    convert h using 1
    funext p
    exact hf _
  exact nested_sde_mlmc_complexity_of_rates ν ρ hfc.measurable hgh hw hP0
    (nested_piecewise_linear_sde_bias_rate ν ρ hf hgh hfib hw hball)
    (nested_piecewise_linear_sde_variance_rate ν ρ hf hgh hfib hw hball hs)
    ω hω hind cost C hc₃ hcost hcostC hC

end KinksSde


/-! ### §9.2: MIMC on the two axes for the kink example -/

section Blocks

variable {ι Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {μ : Measure Ω}

omit [MeasurableSpace Ω₀] [MeasurableSpace Ω] in
/-- A sum of Monte Carlo averages over the blocks `i ∈ S` (Giles 2015, §2.4: the MIMC estimator
is a sum of such averages) is a function of the inputs `ω (i, n)`, `i ∈ S`, `n < M`. -/
lemma sum_blockMean_eq_comp (f : ι → Ω₀ → ℝ) (ω : ι × ℕ → Ω → Ω₀) (S : Finset ι) (M : ℕ) :
    (∑ i ∈ S, blockMean f ω i M) =
      (fun t : (S ×ˢ range M : Finset (ι × ℕ)) → Ω₀ =>
        (M : ℝ)⁻¹ * ∑ p : (S ×ˢ range M : Finset (ι × ℕ)), f p.1.1 (t p)) ∘
      (fun x (p : (S ×ˢ range M : Finset (ι × ℕ))) => ω p x) := by
  funext x
  simp only [Finset.sum_apply, blockMean, Function.comp_apply]
  rw [← Finset.mul_sum, Finset.sum_coe_sort (s := S ×ˢ range M) (f := fun p => f p.1 (ω p x)),
    Finset.sum_product]

/-- **Sums of Monte Carlo averages over disjoint sets of blocks are independent** (Giles 2015,
§1.3, p. 4: "independent samples are used at each level of correction", and §2.4 for MIMC): for
mutually independent inputs `ω (i, n)` and disjoint `S`, `T`, the sums
`∑_{i ∈ S} N⁻¹ ∑_{n<N} f_i(ω^{(i,n)})` and `∑_{i ∈ T} N′⁻¹ ∑_{n<N′} f_i(ω^{(i,n)})` are
independent (`indepFun_blockMean` for single blocks). -/
lemma indepFun_sum_blockMean {f : ι → Ω₀ → ℝ} {ω : ι × ℕ → Ω → Ω₀}
    (hωm : ∀ q, Measurable (ω q)) (hind : iIndepFun ω μ) (hfm : ∀ i, Measurable (f i))
    {S T : Finset ι} (hST : Disjoint S T) (M M' : ℕ) :
    IndepFun (∑ i ∈ S, blockMean f ω i M) (∑ i ∈ T, blockMean f ω i M') μ := by
  have hST' : Disjoint (S ×ˢ range M) (T ×ˢ range M') := Finset.disjoint_product.2 (Or.inl hST)
  have hmeas : ∀ (U : Finset ι) (K : ℕ),
      Measurable fun t : (U ×ˢ range K : Finset (ι × ℕ)) → Ω₀ =>
        (K : ℝ)⁻¹ * ∑ p : (U ×ˢ range K : Finset (ι × ℕ)), f p.1.1 (t p) :=
    fun U K => Measurable.const_mul (Finset.measurable_sum _ fun p _ =>
      (hfm p.1.1).comp (measurable_pi_apply p)) _
  rw [sum_blockMean_eq_comp f ω S M, sum_blockMean_eq_comp f ω T M']
  exact (hind.indepFun_finset _ _ hST' hωm).comp (hmeas S M) (hmeas T M')

end Blocks

section KinkAxes

/-- **The level approximations of the kink example are integrable** (Giles 2015, §9.2: the
example `kinkInnerApprox`, `f(x) = max(x − ½, 0)`, `Z` uniform on `[0, 1]`, fair inner signs,
`g_ℓ = g + 2^{−ℓ}/8`): the quantity of interest `f(E_W[g(Z, W)])` and every
`P_{(a,b)} = f(A_{2^a}(g_b))` are integrable (`nested_mimc_kink_bias`, `memLp_two_kink_comp`). -/
lemma kinkExample_integrable :
    Integrable (nestedTarget (fun x => max (x - 1 / 2) 0) kinkInner kinkCoin)
        (nestedLaw kinkOuter kinkCoin) ∧
      ∀ a b, Integrable (nestedP (fun x => max (x - 1 / 2) 0) (kinkInnerApprox b) a)
        (nestedLaw kinkOuter kinkCoin) := by
  have := isProbabilityMeasure_kinkOuter
  obtain ⟨hm, hmom, hg0, hweak, hball, -⟩ := kinkInnerApprox_hypotheses
  have hf : ∀ x : ℝ, max (x - 1 / 2) 0 = 0 + 0 * x + 1 * max (x - 1 / 2) 0 := fun x => by ring
  have hfib : ∀ ℓ, ∀ᵐ z ∂kinkOuter, Integrable (fun v => kinkInnerApprox ℓ z v ^ 4) kinkCoin ∧
      ∫ v, (kinkInnerApprox ℓ z v - ∫ u, kinkInnerApprox ℓ z u ∂kinkCoin) ^ 4 ∂kinkCoin ≤
        1 / 4096 :=
    fun ℓ => Eventually.of_forall fun z => ⟨(hmom ℓ z).1, (hmom ℓ z).2.le⟩
  have hw : ∀ ℓ, ∀ᵐ z ∂kinkOuter, (2 : ℝ) ^ ℓ *
      |∫ v, kinkInnerApprox ℓ z v ∂kinkCoin - ∫ v, kinkInner z v ∂kinkCoin| ≤ 1 / 8 :=
    fun ℓ => Eventually.of_forall fun z => (hweak ℓ z).le
  have hbias := fun a b => nested_mimc_kink_bias kinkOuter kinkCoin hf hm hfib hw hball a b
  have hP0 : MemLp (nestedP (fun x => max (x - 1 / 2) 0) (kinkInnerApprox 0) 0) 2
      (nestedLaw kinkOuter kinkCoin) :=
    memLp_two_kink_comp hf (measurable_innerMean (s := id) (hm 0) _ measurable_id)
      (integral_innerMean_sq_le kinkOuter kinkCoin (hm 0) hg0 (M := 2 ^ 0) (by positivity)).1
  have hPt : Integrable (nestedTarget (fun x => max (x - 1 / 2) 0) kinkInner kinkCoin)
      (nestedLaw kinkOuter kinkCoin) :=
    ((hP0.integrable one_le_two).sub (hbias 0 0).1).congr
      (Eventually.of_forall fun p => by simp)
  exact ⟨hPt, fun a b => ((hbias a b).1.add hPt).congr (Eventually.of_forall fun p => by simp)⟩

/-- **The mean of `P_{(a,b)}` is additive in the two level indices, for the kink example**
(Giles 2015, §9.2, p. 60; the example `kinkInnerApprox`): `E[P_{(a,b)}] = E[P_{(a,0)}] +
E[P_{(0,b)}] − E[P_{(0,0)}]` for all `a, b`, because every mixed MIMC correction has mean zero
(`integral_kinkMimc`, `integral_nestedMimcDelta_eq`).  (In closed form
`E[P_{(a,b)}] = (½ + 2^{−b}/8)²/2 + 2^{−a}/128`; not needed.)  So the corrections off the two axes
contribute nothing to the mean, and an index set made of the two axes has the bias of the full
box. -/
lemma kinkExample_mean_additive (a b : ℕ) :
    ∫ p, nestedP (fun x => max (x - 1 / 2) 0) (kinkInnerApprox b) a p
        ∂(nestedLaw kinkOuter kinkCoin) =
      ∫ p, nestedP (fun x => max (x - 1 / 2) 0) (kinkInnerApprox 0) a p
          ∂(nestedLaw kinkOuter kinkCoin) +
        ∫ p, nestedP (fun x => max (x - 1 / 2) 0) (kinkInnerApprox b) 0 p
          ∂(nestedLaw kinkOuter kinkCoin) -
        ∫ p, nestedP (fun x => max (x - 1 / 2) 0) (kinkInnerApprox 0) 0 p
          ∂(nestedLaw kinkOuter kinkCoin) := by
  have := isProbabilityMeasure_kinkOuter
  have hint := kinkExample_integrable.2
  set pE : ℕ → ℕ → ℝ := fun a b => ∫ p, nestedP (fun x => max (x - 1 / 2) 0)
    (kinkInnerApprox b) a p ∂(nestedLaw kinkOuter kinkCoin) with hpE
  have hstep : ∀ i j, pE (i + 1) (j + 1) - pE i (j + 1) = pE (i + 1) j - pE i j := by
    intro i j
    have h0 := integral_kinkMimc i j
    rw [integral_nestedMimcDelta_eq kinkOuter kinkCoin hint] at h0
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at h0
    simp only [hpE]
    linarith
  have hcol : ∀ i j, pE (i + 1) j - pE i j = pE (i + 1) 0 - pE i 0 := by
    intro i j
    induction j with
    | zero => rfl
    | succ j ih => rw [hstep, ih]
  have key : ∀ i j, pE i j = pE i 0 + pE 0 j - pE 0 0 := by
    intro i j
    induction i with
    | zero => ring
    | succ i ih => linarith [hcol i j]
  exact key a b

/-- **The corrections along the first axis of the kink example have `β₁ = 3/2`** (Giles 2015,
§9.1, p. 58: "the function `f` was piecewise linear, not twice differentiable, and so the rate of
variance convergence was slightly lower, with `β = 1.5`"; the example `kinkInnerApprox`).  On the
axis `ℓ₂ = 0` the MIMC correction `Y_{(k+1, 0)}` is the §9.1 antithetic correction of the level-`0`
inner approximation `g₀(z, b) = z + s(b)/8 + 1/8`, whose conditional mean `Z + 1/8` has the
small-ball bound `ν{|Z + 1/8 − ½| ≤ t} ≤ 2t`; so `Y_{(k+1,0)}` is square-integrable and
`2^{3k/2} E[Y_{(k+1,0)}²] ≤ 257/64` (`kink_variance_le_of_small_ball` with `c_d = 2`, `c = 1`,
`m₄ = 1/4096`). -/
lemma kinkExample_axis_one (k : ℕ) :
    MemLp (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (k + 1) 0) 2
        (nestedLaw kinkOuter kinkCoin) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * k) * ∫ p, nestedMimcDelta (fun x => max (x - 1 / 2) 0)
        kinkInnerApprox (k + 1) 0 p ^ 2 ∂(nestedLaw kinkOuter kinkCoin) ≤ 257 / 64 := by
  have := isProbabilityMeasure_kinkOuter
  obtain ⟨hm, hmom, -, -, -, -⟩ := kinkInnerApprox_hypotheses
  have hf : ∀ x : ℝ, max (x - 1 / 2) 0 = 0 + 0 * x + 1 * max (x - 1 / 2) 0 := fun x => by ring
  have hfib : ∀ᵐ z ∂kinkOuter, Integrable (fun v => kinkInnerApprox 0 z v ^ 4) kinkCoin ∧
      ∫ v, (kinkInnerApprox 0 z v - ∫ u, kinkInnerApprox 0 z u ∂kinkCoin) ^ 4 ∂kinkCoin ≤
        1 / 4096 :=
    Eventually.of_forall fun z => ⟨(hmom 0 z).1, (hmom 0 z).2.le⟩
  have hG : ∀ z, ∫ v, kinkInnerApprox 0 z v ∂kinkCoin = z + 1 / 8 := fun z => by
    rw [integral_kinkCoin]
    simp only [kinkInnerApprox, kinkSign]
    norm_num
    ring
  have hball : ∀ t : ℝ, 0 < t →
      kinkOuter {z | |∫ v, kinkInnerApprox 0 z v ∂kinkCoin - 1 / 2| ≤ t} ≤
        ENNReal.ofReal (2 * t) := fun t _ => by
    simp only [hG]
    calc kinkOuter {z | |z + 1 / 8 - 1 / 2| ≤ t} ≤ volume {z : ℝ | |z + 1 / 8 - 1 / 2| ≤ t} :=
          Measure.restrict_le_self _
      _ ≤ volume (Set.Icc (3 / 8 - t) (3 / 8 + t)) := measure_mono fun z hz => by
          have := abs_le.1 (show |z + 1 / 8 - 1 / 2| ≤ t from hz)
          exact ⟨by linarith [this.1], by linarith [this.2]⟩
      _ = ENNReal.ofReal (2 * t) := by rw [Real.volume_Icc]; ring_nf
  obtain ⟨h1, h2⟩ := kink_variance_le_of_small_ball kinkOuter kinkCoin hf (hm 0) hfib
    (u := fun z => ∫ v, kinkInnerApprox 0 z v ∂kinkCoin - 1 / 2) (δ := 0)
    (Eventually.of_forall fun z => by simp) hball k (R := 1) (by norm_num) (by norm_num)
  exact ⟨h1, h2.trans (by norm_num)⟩

/-- **The corrections along the second axis of the kink example have `β₂ = 2`** (Giles 2015, §9.2,
p. 59; the example `kinkInnerApprox`, whose inner approximations satisfy
`g_{k+1} − g_k = −2^{−k}/16`): on the axis `ℓ₁ = 0` (one inner sample) the MIMC correction is
`Y_{(0, k+1)} = f(g_{k+1}(Z, W)) − f(g_k(Z, W))`, and `f` is `1`-Lipschitz, so
`|Y_{(0,k+1)}| ≤ 2^{−k}/16` pointwise. -/
lemma kinkExample_axis_two (k : ℕ) (p : ℝ × (ℕ → Bool)) :
    |nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox 0 (k + 1) p| ≤
      ((2 : ℝ) ^ k)⁻¹ / 16 := by
  have hM : 0 < 2 ^ 0 := by positivity
  show |max (innerMean (kinkInnerApprox (k + 1)) (2 ^ 0) p.1 p.2 - 1 / 2) 0 -
    max (innerMean (kinkInnerApprox k) (2 ^ 0) p.1 p.2 - 1 / 2) 0| ≤ _
  rw [innerMean_kinkInnerApprox _ hM, innerMean_kinkInnerApprox _ hM]
  refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
  have e : p.1 + ((2 : ℝ) ^ (k + 1))⁻¹ / 8 +
      innerMean (fun _ b => kinkSign b) (2 ^ 0) p.1 p.2 / 8 - 1 / 2 -
      (p.1 + ((2 : ℝ) ^ k)⁻¹ / 8 + innerMean (fun _ b => kinkSign b) (2 ^ 0) p.1 p.2 / 8 -
        1 / 2) = -(((2 : ℝ) ^ k)⁻¹ / 16) := by
    rw [pow_succ]
    field_simp
    ring
  rw [e, abs_neg, abs_of_pos (by positivity)]

/-- **MIMC on the two axes reaches the cost `O(ε⁻²)` for the kink example** (Giles 2015, §9.2,
p. 60, l. 2690–2692: "On the other hand, with MIMC we would have `β₁ = β₂ = 1.5` and so the
complexity would remain `O(ε⁻²)`. This illustrates the benefit of the MIMC approach compared to
standard MLMC").  For the example of `MlmcLean/NestedKinkSde.lean` (`kinkInnerApprox`:
`f(x) = max(x − ½, 0)`, `Z` uniform on `[0, 1]`, fair inner signs, `g_ℓ = g + 2^{−ℓ}/8`), whose
MIMC rates `β₁ = β₂ = 1.5` are false (`nested_mimc_kink_rates_false`) and for which Theorem 2 on
the full index sets gives only `O(ε⁻² |log ε|⁴)` (`nested_mimc_kink_complexity`), the MIMC
estimator on the index set made of the two axes, `{(a, 0) : a ≤ L} ∪ {(0, b) : 1 ≤ b ≤ L}`, with
the MIMC corrections `Y_ℓ` (`nestedMimcDelta`; on the axes, `Y_{(a,0)}` is the §9.1 antithetic
correction of `g₀` and `Y_{(0,b)} = f(g_b(Z, W⁰)) − f(g_{b−1}(Z, W⁰))` the difference of
single-sample values) averaged over `N_ℓ` independent inputs of law `ν ⊗ ρ^{⊗ℕ}` and a level-`ℓ`
cost of mean `C_ℓ ≤ c₃ 2^{ℓ₁+ℓ₂}`, attains the cost `O(ε⁻²)`: there is
`c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the squared error
of the estimator of `E_Z[f(E_W[g(Z, W)])]` is integrable, its mean is `< ε²` and the expected cost
is `≤ c₄ ε⁻²`.  Proof: the mixed corrections of the example have mean zero (`integral_kinkMimc`),
so `E[P_{(a,b)}] = E[P_{(a,0)}] + E[P_{(0,b)}] − E[P_{(0,0)}]` (`kinkExample_mean_additive`) and the
axes estimator has the bias of `P_{(L,L)}`, `O(2^{−L})` (`kinkInnerApprox_mlmc_rates`); on the first
axis `V = O(2^{−3ℓ₁/2})` (`kinkExample_axis_one`), on the second `V = O(2^{−2ℓ₂})`
(`kinkExample_axis_two`), with cost `O(2^{ℓ})` on both.  Grouping `(k, 0)` and `(0, k)` into one
level `k` gives Theorem 1 (`giles_theorem1_cost_sum`) with `α = 1`, `β = 3/2 > γ = 1`, the
independence of the groups coming from `indepFun_sum_blockMean`.  Deviation: the paper's claim is
for a general continuous, piecewise differentiable `f` and full MIMC; here it is proved for this
one example and on the index set of the two axes (the sample sizes constructed satisfy
`N_{(k,0)} = N_{(0,k)}`).  It relies on the vanishing means of the mixed corrections, which is
special to the example (the weak error of `g_ℓ` does not depend on the outer sample).  In general
the omitted mixed corrections leave a bias that does not vanish as `L → ∞`: for `f(x) = max(x, 0)`,
`Z` uniform on `[−1, 1]`, `g = Z + s(W)/8` and `g_ℓ = g + 2^{−ℓ} Z/8` (first order weak
convergence uniformly in `Z`, with `c_w = 1/8`), their means add up to
`E f(E_W g) − E f(E_W g₀) − E f(g) + E f(g₀) = 1/4 − 9/32 − 65/256 + 41/144 = −1/2304`, so the
axes estimator has the limiting bias `1/2304 ≈ 4.3 · 10⁻⁴` (computed exactly; not formalised). -/
theorem kinkInnerApprox_mimc_axes_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ω : (Fin 2 → ℕ) × ℕ → Ω → ℝ × (ℕ → Bool))
    (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw kinkOuter kinkCoin)) (hind : iIndepFun ω μ)
    (cost : (Fin 2 → ℕ) → ℕ → Ω → ℝ) (C : (Fin 2 → ℕ) → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : Fin 2 → ℕ, C ℓ ≤ c₃ * 2 ^ (ℓ 0 + ℓ 1)) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : (Fin 2 → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ a ∈ range (L + 1), blockMean (fun ℓ : Fin 2 → ℕ =>
            nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox (ℓ 0) (ℓ 1)) ω ![a, 0]
            (N ![a, 0]) x + ∑ b ∈ range L, blockMean (fun ℓ : Fin 2 → ℕ =>
            nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox (ℓ 0) (ℓ 1)) ω
            ![0, b + 1] (N ![0, b + 1]) x -
          ∫ z, max (∫ v, kinkInner z v ∂kinkCoin - 1 / 2) 0 ∂kinkOuter) ^ 2) μ ∧
        μ[fun x => (∑ a ∈ range (L + 1), blockMean (fun ℓ : Fin 2 → ℕ =>
            nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox (ℓ 0) (ℓ 1)) ω ![a, 0]
            (N ![a, 0]) x + ∑ b ∈ range L, blockMean (fun ℓ : Fin 2 → ℕ =>
            nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox (ℓ 0) (ℓ 1)) ω
            ![0, b + 1] (N ![0, b + 1]) x -
          ∫ z, max (∫ v, kinkInner z v ∂kinkCoin - 1 / 2) 0 ∂kinkOuter) ^ 2] < ε ^ 2 ∧
        μ[fun x => ∑ a ∈ range (L + 1), ∑ n ∈ range (N ![a, 0]), cost ![a, 0] n x +
          ∑ b ∈ range L, ∑ n ∈ range (N ![0, b + 1]), cost ![0, b + 1] n x] ≤
          c₄ * ε ^ (-2 : ℝ) := by
  have hμ : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have := isProbabilityMeasure_kinkOuter
  obtain ⟨hm, hmom, hg0, hweak, hball, hstrong⟩ := kinkInnerApprox_hypotheses
  have hf : ∀ x : ℝ, max (x - 1 / 2) 0 = 0 + 0 * x + 1 * max (x - 1 / 2) 0 := fun x => by ring
  have hfm : Measurable fun x : ℝ => max (x - 1 / 2) 0 := (continuous_kink hf).measurable
  have hfib : ∀ ℓ, ∀ᵐ z ∂kinkOuter, Integrable (fun v => kinkInnerApprox ℓ z v ^ 4) kinkCoin ∧
      ∫ v, (kinkInnerApprox ℓ z v - ∫ u, kinkInnerApprox ℓ z u ∂kinkCoin) ^ 4 ∂kinkCoin ≤
        1 / 4096 :=
    fun ℓ => Eventually.of_forall fun z => ⟨(hmom ℓ z).1, (hmom ℓ z).2.le⟩
  have hw : ∀ ℓ, ∀ᵐ z ∂kinkOuter, (2 : ℝ) ^ ℓ *
      |∫ v, kinkInnerApprox ℓ z v ∂kinkCoin - ∫ v, kinkInner z v ∂kinkCoin| ≤ 1 / 8 :=
    fun ℓ => Eventually.of_forall fun z => (hweak ℓ z).le
  have hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ * ∫ p, (kinkInnerApprox (ℓ + 1) p.1 p.2 -
      kinkInnerApprox ℓ p.1 p.2) ^ 2 ∂(kinkOuter.prod kinkCoin) ≤ 1 / 256 := fun ℓ => by
    simp_rw [hstrong]
    rw [integral_const, probReal_univ, one_smul]
    have h2 : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    calc (2 : ℝ) ^ ℓ * (-(((2 : ℝ) ^ ℓ)⁻¹ / 16)) ^ 2 = ((2 : ℝ) ^ ℓ)⁻¹ / 256 := by
          field_simp
          ring
      _ ≤ 1 / 256 := by
          gcongr
          exact inv_le_one_of_one_le₀ h2
  obtain ⟨Bv, -, hBv⟩ := nested_mimc_kink_all_levels kinkOuter kinkCoin hf hm hfib hg0 hw hball hs
  set Δ : (Fin 2 → ℕ) → ℝ × (ℕ → Bool) → ℝ := fun ℓ =>
    nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox (ℓ 0) (ℓ 1) with hΔdef
  have hΔeq : ∀ a b : ℕ, Δ ![a, b] =
      nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox a b := fun a b => rfl
  have hΔm : ∀ ℓ, Measurable (Δ ℓ) := fun ℓ => measurable_nestedMimcDelta hfm hm _ _
  have hΔ : ∀ ℓ, MemLp (Δ ℓ) 2 (nestedLaw kinkOuter kinkCoin) := fun ℓ => (hBv _ _).1
  have hΔi : ∀ ℓ, Integrable (Δ ℓ) (nestedLaw kinkOuter kinkCoin) := fun ℓ =>
    (hΔ ℓ).integrable one_le_two
  -- the means of the approximations and of the corrections on the axes
  obtain ⟨hPt, hint⟩ := kinkExample_integrable
  set pE : ℕ → ℕ → ℝ := fun a b => ∫ p, nestedP (fun x => max (x - 1 / 2) 0)
    (kinkInnerApprox b) a p ∂(nestedLaw kinkOuter kinkCoin) with hpE
  set T : ℝ := ∫ p, nestedTarget (fun x => max (x - 1 / 2) 0) kinkInner kinkCoin p
    ∂(nestedLaw kinkOuter kinkCoin) with hT
  have hEΔ := integral_nestedMimcDelta_eq kinkOuter kinkCoin hint
  have hE00 : ∫ p, Δ ![0, 0] p ∂(nestedLaw kinkOuter kinkCoin) = pE 0 0 := by
    have h := hEΔ 0 0
    simp only [if_true, sub_zero] at h
    rw [hΔeq]
    exact h
  have hE1 : ∀ k : ℕ, ∫ p, Δ ![k + 1, 0] p ∂(nestedLaw kinkOuter kinkCoin) =
      pE (k + 1) 0 - pE k 0 := fun k => by
    have h := hEΔ (k + 1) 0
    simp only [Nat.add_one_ne_zero, if_true, if_false, Nat.add_sub_cancel, sub_zero] at h
    rw [hΔeq]
    exact h
  have hE2 : ∀ k : ℕ, ∫ p, Δ ![0, k + 1] p ∂(nestedLaw kinkOuter kinkCoin) =
      pE 0 (k + 1) - pE 0 k := fun k => by
    have h := hEΔ 0 (k + 1)
    simp only [Nat.add_one_ne_zero, if_true, if_false, Nat.add_sub_cancel, sub_zero] at h
    rw [hΔeq]
    exact h
  -- the bias of `P_{(k,k)}`, `O(2^{−k})`
  have hdiag : ∀ k : ℕ, |pE k k - T| ≤ 10 * (2 : ℝ) ^ (-((1 : ℝ) * (k : ℝ))) := fun k => by
    have h := (kinkInnerApprox_mlmc_rates k).1
    have e : ∫ p, (nestedSdeP (fun x => max (x - 1 / 2) 0) kinkInnerApprox k p -
        nestedTarget (fun x => max (x - 1 / 2) 0) kinkInner kinkCoin p)
        ∂(nestedLaw kinkOuter kinkCoin) = pE k k - T := integral_sub (hint k k) hPt
    rw [e] at h
    rw [one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h
  -- the groups of levels `{(k, 0), (0, k)}`
  set Bk : ℕ → Finset (Fin 2 → ℕ) := fun k => {![k, 0], ![0, k]} with hBk
  have hBsum : ∀ k, ∀ ℓ ∈ Bk k, ℓ 0 + ℓ 1 = k := by
    intro k ℓ h
    simp only [hBk, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> simp
  have hB0 : Bk 0 = {![0, 0]} := by
    simp only [hBk]
    exact Finset.insert_eq_of_mem (Finset.mem_singleton_self _)
  have hne : ∀ k : ℕ, (![k + 1, 0] : Fin 2 → ℕ) ≠ ![0, k + 1] := fun k h => by
    have := congr_fun h 0
    simp at this
  have hB1 : ∀ k : ℕ, Bk (k + 1) = {![k + 1, 0], ![0, k + 1]} := fun k => rfl
  have hdisj : ∀ i j, i ≠ j → Disjoint (Bk i) (Bk j) := fun i j hij => by
    rw [Finset.disjoint_left]
    intro ℓ hi hj
    exact hij ((hBsum i ℓ hi).symm.trans (hBsum j ℓ hj))
  set Y : ℕ → ℕ → Ω → ℝ := fun k M => ∑ ℓ ∈ Bk k, blockMean Δ ω ℓ M with hYdef
  set V : ℕ → ℝ := fun k => ∑ ℓ ∈ Bk k, variance (Δ ℓ) (nestedLaw kinkOuter kinkCoin) with hVdef
  set C' : ℕ → ℝ := fun k => ∑ ℓ ∈ Bk k, C ℓ with hC'def
  set q : ℕ → ℝ := fun k => pE k 0 + pE 0 k - pE 0 0 with hq
  have hωm : ∀ p, Measurable (ω p) := fun p => (hω p).measurable
  have hY0 : ∀ M x, Y 0 M x = blockMean Δ ω ![0, 0] M x := fun M x => by
    simp only [hYdef, Finset.sum_apply, hB0, Finset.sum_singleton]
  have hYs : ∀ k M x, Y (k + 1) M x =
      blockMean Δ ω ![k + 1, 0] M x + blockMean Δ ω ![0, k + 1] M x := fun k M x => by
    simp only [hYdef, Finset.sum_apply, hB1]
    exact Finset.sum_pair (hne k)
  have hYmem : ∀ k n, MemLp (Y k n) 2 μ := fun k n =>
    memLp_finsetSum' _ fun ℓ _ => memLp_blockMean hω hΔ ℓ n
  have hYind : ∀ N : ℕ → ℕ, (∀ k, 0 < N k) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ :=
    fun N _ i j hij => indepFun_sum_blockMean hωm hind hΔm (hdisj i j hij) _ _
  have hYmean : ∀ k n, 0 < n →
      μ[Y k n] = ∑ ℓ ∈ Bk k, ∫ p, Δ ℓ p ∂(nestedLaw kinkOuter kinkCoin) := by
    intro k n hn
    simp only [hYdef, Finset.sum_apply]
    rw [integral_finsetSum _ fun ℓ _ => (memLp_blockMean hω hΔ ℓ n).integrable one_le_two]
    exact Finset.sum_congr rfl fun ℓ _ => integral_blockMean hω hΔi ℓ hn
  have hYvar : ∀ k n, 0 < n → variance (Y k n) μ = V k / n := by
    intro k n hn
    simp only [hYdef, hVdef]
    rw [IndepFun.variance_sum (fun ℓ _ => memLp_blockMean hω hΔ ℓ n)
      (fun i _ j _ hij => indepFun_blockMean hωm hind hΔm hij n n), Finset.sum_div]
    exact Finset.sum_congr rfl fun ℓ _ => variance_blockMean hω hind hΔm hΔ ℓ hn
  -- the hypotheses of Theorem 1 for the grouped levels
  have h_i : ∀ k : ℕ, |μ[fun _ => q k - T]| ≤ 10 * (2 : ℝ) ^ (-((1 : ℝ) * (k : ℝ))) :=
    fun k => by
      rw [integral_const, probReal_univ, one_smul]
      have e : q k = pE k k := by
        simp only [hq, hpE]
        exact (kinkExample_mean_additive k k).symm
      rw [e]
      exact hdiag k
  have h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[fun _ : Ω => q 0] := fun n hn => by
    rw [hYmean 0 n hn, integral_const, probReal_univ, one_smul, hB0, Finset.sum_singleton, hE00]
    simp only [hq]
    ring
  have h_ii : ∀ k n, 0 < n → μ[Y (k + 1) n] = μ[fun _ : Ω => q (k + 1) - q k] :=
    fun k n hn => by
      rw [hYmean (k + 1) n hn, integral_const, probReal_univ, one_smul, hB1,
        Finset.sum_pair (hne k), hE1, hE2]
      simp only [hq]
      ring
  have hv0 := variance_nonneg (Δ ![0, 0]) (nestedLaw kinkOuter kinkCoin)
  have h_iii : ∀ k : ℕ, V k ≤ (variance (Δ ![0, 0]) (nestedLaw kinkOuter kinkCoin) + 13) *
      (2 : ℝ) ^ (-((3 / 2 : ℝ) * (k : ℝ))) := fun k => by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← div_eq_mul_inv]
    cases k with
    | zero =>
      simp only [hVdef, hB0, Finset.sum_singleton, Nat.cast_zero, mul_zero, Real.rpow_zero,
        div_one]
      linarith
    | succ j =>
      simp only [hVdef, hB1]
      rw [Finset.sum_pair (hne j), hΔeq, hΔeq]
      obtain ⟨hm1, h1⟩ := kinkExample_axis_one j
      have hv1 := variance_le_expectation_sq (μ := nestedLaw kinkOuter kinkCoin)
        hm1.aestronglyMeasurable
      have hm2 : MemLp (nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox 0 (j + 1))
          2 (nestedLaw kinkOuter kinkCoin) := hΔ ![0, j + 1]
      have hv2 := variance_le_expectation_sq (μ := nestedLaw kinkOuter kinkCoin)
        hm2.aestronglyMeasurable
      simp only [Pi.pow_apply] at hv1 hv2
      have h2 : ∫ p, nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox 0 (j + 1) p ^ 2
          ∂(nestedLaw kinkOuter kinkCoin) ≤ (((2 : ℝ) ^ j)⁻¹ / 16) ^ 2 := by
        have hb : ∀ p, nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox 0 (j + 1) p
            ^ 2 ≤ (((2 : ℝ) ^ j)⁻¹ / 16) ^ 2 := fun p => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (kinkExample_axis_two j p) 2
        calc _ ≤ ∫ _p, (((2 : ℝ) ^ j)⁻¹ / 16) ^ 2 ∂(nestedLaw kinkOuter kinkCoin) :=
              integral_mono hm2.integrable_sq (integrable_const _) hb
          _ = _ := by rw [integral_const, probReal_univ, one_smul]
      -- `2^{3(j+1)/2} ≤ 3 · 2^{3j/2}` and `2^{3(j+1)/2} ≤ 4 · 4^j`
      have h32 : (2 : ℝ) ^ ((3 / 2 : ℝ) * ((j + 1 : ℕ) : ℝ)) ≤
          3 * (2 : ℝ) ^ ((3 / 2 : ℝ) * (j : ℝ)) := by
        have e : (3 / 2 : ℝ) * ((j + 1 : ℕ) : ℝ) = 3 / 2 + (3 / 2 : ℝ) * (j : ℝ) := by
          push_cast
          ring
        rw [e, Real.rpow_add (by norm_num)]
        gcongr
        have h8 : (2 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt 8 := by
          rw [Real.sqrt_eq_rpow, show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [h8, Real.sqrt_le_left (by norm_num)]
        norm_num
      have h44 : (2 : ℝ) ^ ((3 / 2 : ℝ) * ((j + 1 : ℕ) : ℝ)) ≤ 4 * ((2 : ℝ) ^ j) ^ 2 := by
        calc (2 : ℝ) ^ ((3 / 2 : ℝ) * ((j + 1 : ℕ) : ℝ))
            ≤ (2 : ℝ) ^ (((2 * (j + 1) : ℕ) : ℝ)) := by
              refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
              push_cast
              nlinarith [Nat.cast_nonneg (α := ℝ) j]
          _ = 4 * ((2 : ℝ) ^ j) ^ 2 := by
              rw [Real.rpow_natCast]
              ring
      set r := (2 : ℝ) ^ ((3 / 2 : ℝ) * ((j + 1 : ℕ) : ℝ)) with hr
      have hr0 : 0 < r := by positivity
      have hs0 : 0 < (2 : ℝ) ^ ((3 / 2 : ℝ) * (j : ℝ)) := by positivity
      have hq0 : 0 < (2 : ℝ) ^ j := by positivity
      have hE1' : 0 ≤ ∫ p, nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox (j + 1) 0
          p ^ 2 ∂(nestedLaw kinkOuter kinkCoin) := integral_nonneg fun p => sq_nonneg _
      have hvar1 : variance (nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox (j + 1)
          0) (nestedLaw kinkOuter kinkCoin) * r ≤ 3 * (257 / 64) :=
        calc _ ≤ (∫ p, nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox (j + 1) 0
              p ^ 2 ∂(nestedLaw kinkOuter kinkCoin)) * (3 * (2 : ℝ) ^ ((3 / 2 : ℝ) * (j : ℝ))) :=
              mul_le_mul hv1 h32 hr0.le hE1'
          _ = 3 * ((2 : ℝ) ^ ((3 / 2 : ℝ) * (j : ℝ)) * ∫ p, nestedMimcDelta
              (fun y => max (y - 1 / 2) 0) kinkInnerApprox (j + 1) 0 p ^ 2
              ∂(nestedLaw kinkOuter kinkCoin)) := by ring
          _ ≤ 3 * (257 / 64) := by gcongr
      have hvar2 : variance (nestedMimcDelta (fun y => max (y - 1 / 2) 0) kinkInnerApprox 0
          (j + 1)) (nestedLaw kinkOuter kinkCoin) * r ≤ 1 / 64 :=
        calc _ ≤ (((2 : ℝ) ^ j)⁻¹ / 16) ^ 2 * (4 * ((2 : ℝ) ^ j) ^ 2) :=
              mul_le_mul (hv2.trans h2) h44 hr0.le (sq_nonneg _)
          _ = 1 / 64 := by field_simp; norm_num
      rw [le_div_iff₀ hr0, add_mul]
      linarith
  have h_iv : ∀ k : ℕ, C' k ≤ (2 * c₃) * (2 : ℝ) ^ ((1 : ℝ) * (k : ℝ)) := fun k => by
    rw [one_mul, Real.rpow_natCast]
    have hle : ∀ ℓ ∈ Bk k, C ℓ ≤ c₃ * 2 ^ k := fun ℓ hℓ => by
      have h := hC ℓ
      rwa [hBsum k ℓ hℓ] at h
    have hcard : ((Bk k).card : ℝ) ≤ 2 := by
      exact_mod_cast (Finset.card_le_two : (({![k, 0], ![0, k]} : Finset (Fin 2 → ℕ))).card ≤ 2)
    calc C' k ≤ (Bk k).card • (c₃ * 2 ^ k) := Finset.sum_le_card_nsmul _ _ _ hle
      _ = ((Bk k).card : ℝ) * (c₃ * 2 ^ k) := nsmul_eq_mul _ _
      _ ≤ 2 * (c₃ * 2 ^ k) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * c₃ * 2 ^ k := by ring
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_cost_sum (μ := μ) (fun _ : Ω => T) (fun k _ => q k) Y V C'
    (α := 1) (β := 3 / 2) (γ := 1) one_pos (by norm_num) one_pos (by norm_num : (0 : ℝ) < 10)
    (by linarith : 0 < variance (Δ ![0, 0]) (nestedLaw kinkOuter kinkCoin) + 13)
    (by positivity : 0 < 2 * c₃) (by norm_num) (integrable_const T)
    (fun k => integrable_const (q k)) (fun k n _ => hYmem k n) hYind h_i h_ii₀ h_ii hYvar
    h_iii h_iv
  -- back to the axes estimator
  have hfst : MeasurePreserving (Prod.fst : ℝ × (ℕ → Bool) → ℝ) (nestedLaw kinkOuter kinkCoin)
      kinkOuter := measurePreserving_fst
  have hGm : AEMeasurable (fun z => ∫ v, kinkInner z v ∂kinkCoin) kinkOuter :=
    aemeasurable_condMean_of_weak kinkOuter kinkCoin hm hw
  have hFm : AEStronglyMeasurable (fun z => max (∫ v, kinkInner z v ∂kinkCoin - 1 / 2) 0)
      kinkOuter := (hfm.comp_aemeasurable hGm).aestronglyMeasurable
  have hTz : T = ∫ z, max (∫ v, kinkInner z v ∂kinkCoin - 1 / 2) 0 ∂kinkOuter :=
    integral_comp_of_measurePreserving hfst hFm
  have hPμ : μ[fun _ : Ω => T] = T := by rw [integral_const, probReal_univ, one_smul]
  have hC'0 : C' 0 = C ![0, 0] := by simp only [hC'def, hB0, Finset.sum_singleton]
  have hC's : ∀ k : ℕ, C' (k + 1) = C ![k + 1, 0] + C ![0, k + 1] := fun k => by
    simp only [hC'def, hB1]
    exact Finset.sum_pair (hne k)
  have hcostI : ∀ ℓ (M : ℕ), Integrable (fun x => ∑ n ∈ range M, cost ℓ n x) μ := fun ℓ M =>
    integrable_finsetSum _ fun n _ => hcost ℓ n
  have hcostE : ∀ ℓ (M : ℕ), μ[fun x => ∑ n ∈ range M, cost ℓ n x] = (M : ℝ) * C ℓ :=
      fun ℓ M => by
    rw [integral_finsetSum _ fun n _ => hcost ℓ n]
    simp only [hcostC, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcs⟩ := h ε hε hε1
  refine ⟨L, fun ℓ => N (ℓ 0 + ℓ 1), fun ℓ => hN _, ?_⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, zero_add]
  have hsum : ∀ x, ∑ a ∈ range (L + 1), blockMean Δ ω ![a, 0] (N a) x +
      ∑ b ∈ range L, blockMean Δ ω ![0, b + 1] (N (b + 1)) x =
      ∑ k ∈ range (L + 1), Y k (N k) x := fun x => by
    rw [Finset.sum_range_succ' (fun k => Y k (N k) x),
      Finset.sum_range_succ' (fun a => blockMean Δ ω ![a, 0] (N a) x)]
    simp only [hY0, hYs, Finset.sum_add_distrib]
    ring
  have hfun : (fun x => (∑ a ∈ range (L + 1), blockMean Δ ω ![a, 0] (N a) x +
      ∑ b ∈ range L, blockMean Δ ω ![0, b + 1] (N (b + 1)) x -
      ∫ z, max (∫ v, kinkInner z v ∂kinkCoin - 1 / 2) 0 ∂kinkOuter) ^ 2) =
      fun x => (∑ k ∈ range (L + 1), Y k (N k) x - μ[fun _ : Ω => T]) ^ 2 := by
    funext x
    rw [hsum x, hPμ, hTz]
  have hcostT : μ[fun x => ∑ a ∈ range (L + 1), ∑ n ∈ range (N a), cost ![a, 0] n x +
      ∑ b ∈ range L, ∑ n ∈ range (N (b + 1)), cost ![0, b + 1] n x] =
      ∑ k ∈ range (L + 1), (N k : ℝ) * C' k := by
    rw [integral_add (integrable_finsetSum _ fun a _ => hcostI _ _)
      (integrable_finsetSum _ fun b _ => hcostI _ _),
      integral_finsetSum _ fun a _ => hcostI _ _, integral_finsetSum _ fun b _ => hcostI _ _]
    simp only [hcostE]
    rw [Finset.sum_range_succ' (fun k => (N k : ℝ) * C' k),
      Finset.sum_range_succ' (fun a => (N a : ℝ) * C ![a, 0])]
    simp only [hC'0, hC's, mul_add, Finset.sum_add_distrib]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact ((memLp_finsetSum _ fun k _ => hYmem k (N k)).sub (memLp_const _)).integrable_sq
  · rw [hfun]
    exact hmse
  · rw [hcostT]
    rw [complexityBound_of_lt (by norm_num) ε] at hcs
    exact hcs

end KinkAxes

end MLMC
