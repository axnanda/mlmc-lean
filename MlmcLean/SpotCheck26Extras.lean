import MlmcLean.BanachTheorem1
import MlmcLean.GBMSensitivities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic

/-!
# Spot-check 26 extras: the sharp type-2 constant of `ℓ^∞_2` and `V₀ = 0` for the digital delta

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015).

**1. §2.5, pp. 17–18, l. 772–787 of `docs/giles2015.txt`.**  "When using the 2-norm, this
extends to independent random vectors `a` and `b`, each with zero mean, since
`E[‖a+b‖²] = E[‖a‖²] + E[‖b‖²]` … However this does not necessarily apply for other norms …
Nevertheless, the theory can be extended to the use of other norms by using results from Banach
space theory for the sums of independent random variables (Ledoux and Talagrand 1991, Heinrich
1998)" (l. 772–787).  For `ℝ × ℝ` with the maximum norm (Mathlib's norm on a product) the type-2
inequality `E‖∑ X_i‖² ≤ τ² ∑ E‖X_i‖²` holds with `τ = √2`.  Here `√2` is shown to be the least
such constant: the independent random signs `X₁ = ε₁ (1, 1)`, `X₂ = ε₂ (1, −1)` (on the product of
two fair coins) have `‖X₁ + X₂‖ = 2` and `‖X₁‖ = ‖X₂‖ = 1` on every sample, so the inequality
forces `4 ≤ 2τ²`.
* `two_le_sq_of_hasType2_prod`: type 2 with constant `τ` for `ℝ × ℝ` forces `τ² ≥ 2`;
* `not_hasType2_prod_of_lt_sqrt_two`: no constant `|τ| < √2` works;
* `hasType2_prod_iff`: type 2 with constant `τ` holds iff `√2 ≤ |τ|`;
* `isLeast_hasType2_prod`: `√2` is the least nonnegative type-2 constant of `ℝ × ℝ`.

**2. §5.4, p. 42, l. 1819–1835.**  "Sensitivities for digital options can be obtained by first
using the conditional expectation approach described previously, and then applying pathwise
sensitivity analysis to this" (l. 1829–1832).  For the payoff itself the paper notes that "there
is zero variance on the coarsest level. This is because there is only one timestep on the
coarsest level, and therefore the conditional expectation is taken immediately and every sample
gives the same payoff" (§5.2, p. 36, l. 1580–1583).  The same holds for its pathwise delta:
* `gbm_digital_condExp_delta_level_zero`: the level-`0` correction of the digital delta (the fine
  delta with one step of size `T`) takes the same value on every sample, is square integrable and
  has variance `0`, for all parameters.

**Deviations.**  The counterexample space is the product of two fair coins lifted to the universe
`u` of the type-2 predicate; the paper gives no constant for other norms.  The level-`0` delta
needs no hypotheses; for `s₀ ≠ 0`, `σ ≠ 0`, `T > 0` it is the derivative in `s₀` of the level-`0`
payoff, otherwise it is just the value of the formula.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

universe u

/-! ### The type-2 constant `√2` of `ℝ × ℝ` with the maximum norm is sharp -/

/-- **Type 2 is monotone in the constant** (Giles 2015, §2.5, pp. 17–18, l. 782–787: "the
theory can be extended to the use of other norms by using results from Banach space theory for
the sums of independent random variables").  If `E‖∑ X_i‖² ≤ τ² ∑ E‖X_i‖²` always holds and
`τ² ≤ τ'²`, then it holds with `τ'`, as the right-hand side sums nonnegative terms. -/
lemma HasType2.mono_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] {τ τ' : ℝ} (hE : HasType2.{u} E τ) (hττ' : τ ^ 2 ≤ τ' ^ 2) :
    HasType2.{u} E τ' := by
  intro Ω _ μ _ n X hind hX hX0
  exact (hE Ω μ n X hind hX hX0).trans (mul_le_mul_of_nonneg_right hττ'
    (sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _))

/-- **A type-2 constant of `ℝ × ℝ` with the maximum norm satisfies `τ² ≥ 2`** (Giles 2015, §2.5,
pp. 17–18, l. 772–787: the 2-norm identity `E[‖a+b‖²] = E[‖a‖²] + E[‖b‖²]` "does not
necessarily apply for other norms").  On the product of two fair coins, lifted to the universe
`u`, the independent mean-zero vectors `X₁ = ε₁ (1, 1)` and `X₂ = ε₂ (1, −1)` with random signs
`ε₁`, `ε₂` have `‖X₁ + X₂‖_∞ = 2` and `‖X₁‖_∞ = ‖X₂‖_∞ = 1` on every sample, so the type-2
inequality reads `4 ≤ τ² (1 + 1)`. -/
theorem two_le_sq_of_hasType2_prod {τ : ℝ} (hτ : HasType2.{u} (ℝ × ℝ) τ) : 2 ≤ τ ^ 2 := by
  let ε : ULift.{u} Bool → ℝ := fun b => if b.down then 1 else -1
  have hε : Measurable ε :=
    (Measurable.of_discrete (f := fun c : Bool => if c then (1 : ℝ) else -1)).comp
      measurable_down
  let μ₁ : Measure (ULift.{u} Bool) :=
    (2⁻¹ : ENNReal) • (Measure.dirac (ULift.up true) + Measure.dirac (ULift.up false))
  have : IsProbabilityMeasure μ₁ := ⟨by
    simp only [μ₁, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩
  have hε0 : ∫ x, ε x ∂μ₁ = 0 := by
    have hsm : StronglyMeasurable ε := hε.stronglyMeasurable
    have hi : ∀ a : ULift.{u} Bool, Integrable ε (Measure.dirac a) := fun a =>
      Integrable.of_bound hsm.aestronglyMeasurable 1 (ae_of_all _ fun x => by
        by_cases h : x.down <;> simp [ε, h])
    rw [integral_smul_measure, integral_add_measure (hi _) (hi _), integral_dirac' _ _ hsm,
      integral_dirac' _ _ hsm]
    simp [ε]
  let v : Fin 2 → ℝ × ℝ := ![(1, 1), (1, -1)]
  let Y : Fin 2 → ULift.{u} Bool → ℝ × ℝ := fun i x => ε x • v i
  have hY : ∀ i, Measurable (Y i) := fun i =>
    ((continuous_id.smul continuous_const).measurable).comp hε
  let μ : Measure (Fin 2 → ULift.{u} Bool) := Measure.pi fun _ => μ₁
  let X : Fin 2 → (Fin 2 → ULift.{u} Bool) → ℝ × ℝ := fun i ω => Y i (ω i)
  have hind : iIndepFun X μ := iIndepFun_pi fun i => (hY i).aemeasurable
  have hnormY : ∀ i x, ‖Y i x‖ = 1 := by
    intro i x
    fin_cases i <;> by_cases h : x.down <;> simp [Y, ε, v, h]
  have hXm : ∀ i, MemLp (X i) 2 μ := fun i =>
    MemLp.of_bound ((hY i).comp (measurable_pi_apply i)).aestronglyMeasurable 1
      (ae_of_all _ fun ω => (hnormY i (ω i)).le)
  have hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0 := fun i => by
    show ∫ ω, Y i (ω i) ∂μ = 0
    rw [integral_comp_eval (hY i).aestronglyMeasurable]
    show ∫ x, ε x • v i ∂μ₁ = 0
    rw [integral_smul_const, hε0, zero_smul]
  have hsum : ∀ ω, ‖∑ i, X i ω‖ = 2 := by
    intro ω
    rw [Fin.sum_univ_two]
    show ‖Y 0 (ω 0) + Y 1 (ω 1)‖ = 2
    by_cases h0 : (ω 0).down <;> by_cases h1 : (ω 1).down <;> norm_num [Y, ε, v, h0, h1]
  have h := hτ _ μ 2 X hind hXm hX0
  have hnormX : ∀ i ω, ‖X i ω‖ = 1 := fun i ω => hnormY i (ω i)
  simp only [hsum] at h
  simp only [hnormX, integral_const, probReal_univ, smul_eq_mul, one_mul,
    Fin.sum_univ_two] at h
  linarith

/-- **The type-2 constant `√2` of `ℝ × ℝ` with the maximum norm cannot be lowered** (Giles 2015,
§2.5, pp. 17–18, l. 776–787: "However this does not necessarily apply for other norms, and so
the variance for the combined multilevel estimator can not necessarily be expressed in the usual
form as `∑_ℓ N_ℓ⁻¹ V_ℓ`").  For `|τ| < √2` the type-2 inequality
`E‖∑ X_i‖² ≤ τ² ∑ E‖X_i‖²` fails for `ℝ × ℝ` with `‖(x, y)‖ = max |x| |y|`: the random signs
`ε₁ (1, 1)`, `ε₂ (1, −1)` give `E‖X₁ + X₂‖² = 4 > 2τ² = τ² (E‖X₁‖² + E‖X₂‖²)`. -/
theorem not_hasType2_prod_of_lt_sqrt_two {τ : ℝ} (hτ : |τ| < Real.sqrt 2) :
    ¬ HasType2.{u} (ℝ × ℝ) τ := by
  intro h
  have h2 := two_le_sq_of_hasType2_prod h
  have hsq : τ ^ 2 < Real.sqrt 2 ^ 2 := by
    rw [← sq_abs τ]
    exact pow_lt_pow_left₀ hτ (abs_nonneg τ) two_ne_zero
  rw [Real.sq_sqrt (by norm_num)] at hsq
  linarith

/-- **The type-2 constants of `ℝ × ℝ` with the maximum norm are exactly `|τ| ≥ √2`** (Giles 2015,
§2.5, pp. 17–18, l. 776–787: "the theory can be extended to the use of other norms by using
results from Banach space theory for the sums of independent random variables").  The
inequality `E‖∑ X_i‖² ≤ τ² ∑ E‖X_i‖²` holds for all independent, square-integrable, mean-zero
`ℝ × ℝ`-valued `X_i` iff `√2 ≤ |τ|`: sufficiency from the comparison
`‖x‖_∞ ≤ ‖x‖₂ ≤ √2 ‖x‖_∞` with the Euclidean norm, necessity from the random signs
`ε₁ (1, 1)`, `ε₂ (1, −1)`. -/
theorem hasType2_prod_iff {τ : ℝ} : HasType2.{u} (ℝ × ℝ) τ ↔ Real.sqrt 2 ≤ |τ| := by
  constructor
  · intro h
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (two_le_sq_of_hasType2_prod h)
  · intro h
    refine hasType2_prod_sqrt_two.mono_sq ?_
    rw [← sq_abs τ]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg 2) h 2

/-- **`√2` is the least type-2 constant of `ℝ × ℝ` with the maximum norm** (Giles 2015, §2.5,
pp. 17–18, l. 776–787: "However this does not necessarily apply for other norms … Nevertheless,
the theory can be extended to the use of other norms by using results from Banach space theory
for the sums of independent random variables").  Among the nonnegative `τ` with
`E‖∑ X_i‖² ≤ τ² ∑ E‖X_i‖²` for all independent, square-integrable, mean-zero `ℝ × ℝ`-valued
`X_i`, the least is `√2`; the MSE bound of the type-2 version of Theorem 1 thus carries the
factor `τ² = 2` for the maximum norm of two outputs, and no smaller factor from this inequality.
-/
theorem isLeast_hasType2_prod :
    IsLeast {τ : ℝ | 0 ≤ τ ∧ HasType2.{u} (ℝ × ℝ) τ} (Real.sqrt 2) :=
  ⟨⟨Real.sqrt_nonneg 2, hasType2_prod_sqrt_two⟩, fun _ hτ =>
    (hasType2_prod_iff.1 hτ.2).trans_eq (abs_of_nonneg hτ.1)⟩

/-! ### Zero variance of the digital-delta correction on the coarsest level -/

/-- **Zero variance of the digital-delta correction on the coarsest level** (Giles 2015, §5.4,
p. 42, l. 1819–1835: "Sensitivities for digital options can be obtained by first using the
conditional expectation approach described previously, and then applying pathwise sensitivity
analysis to this"; for the payoff, §5.2, p. 36, l. 1580–1583: "there is zero variance on the
coarsest level. This is because there is only one timestep on the coarsest level, and therefore
the conditional expectation is taken immediately and every sample gives the same payoff").  On
level `0` (one step of size `T`) the path before the last step is `S_0 = s₀`, so the level-`0`
correction `∂P^f_0/∂s₀ = φ((m_f − K)/s_f) K/(s₀ s_f)`, with `m_f = s₀ + r s₀ T` and
`s_f = |σ s₀| √T`, is the same number for every sample: it is square integrable and `V_0 = 0`.
No hypotheses are needed (for `s₀ ≠ 0`, `σ ≠ 0`, `T > 0` it is the pathwise delta; if `σ s₀ = 0` or
`T ≤ 0` then `s_f = 0` and the value is Lean's junk value `0`). -/
theorem gbm_digital_condExp_delta_level_zero (r σ s₀ K T : ℝ) :
    (∀ z, fineCoarseDiff (gbmDigitalCondFineDelta r σ T s₀ K)
        (gbmDigitalCondCoarseDelta r σ T s₀ K) 0 z =
      gaussianPDFReal 0 1 ((s₀ + r * s₀ * T - K) / (|σ * s₀| * Real.sqrt T)) *
        (K / (s₀ * (|σ * s₀| * Real.sqrt T)))) ∧
    MemLp (fineCoarseDiff (gbmDigitalCondFineDelta r σ T s₀ K)
      (gbmDigitalCondCoarseDelta r σ T s₀ K) 0) 2 stdNormalSeq ∧
    variance (fineCoarseDiff (gbmDigitalCondFineDelta r σ T s₀ K)
      (gbmDigitalCondCoarseDelta r σ T s₀ K) 0) stdNormalSeq = 0 := by
  have hz : ∀ z, fineCoarseDiff (gbmDigitalCondFineDelta r σ T s₀ K)
      (gbmDigitalCondCoarseDelta r σ T s₀ K) 0 z =
      gaussianPDFReal 0 1 ((s₀ + r * s₀ * T - K) / (|σ * s₀| * Real.sqrt T)) *
        (K / (s₀ * (|σ * s₀| * Real.sqrt T))) := fun z => by
    show gbmDigitalCondFineDelta r σ T s₀ K 0 z = _
    unfold gbmDigitalCondFineDelta gbmCondMeanFine gbmCondStdFine
    rw [pow_zero, pow_zero, div_one, Nat.sub_self]
    rfl
  refine ⟨hz, ?_, variance_eq_zero_of_forall_eq hz⟩
  rw [funext hz]
  exact memLp_const _

end MLMC
