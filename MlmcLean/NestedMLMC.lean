import MlmcLean.NestedSimulation
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The MLMC estimator for nested simulation (Giles 2015, §9.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §9.1 "MLMC
treatment" (pp. 57–58) of the author's version.

**The model.**  The outer variable `Z` has law `ν` on `𝒵`; the inner samples `W⁽⁰⁾, W⁽¹⁾, …` are
independent of `Z` and of each other, each with law `ρ` on `𝒲`, so that their joint law is the
product `ν ⊗ ρ^{⊗ℕ}` (`nestedLaw`) on `𝒵 × 𝒲^ℕ`.  For `g : 𝒵 → 𝒲 → ℝ` and `f : ℝ → ℝ` the
quantity of interest is `E_Z[f(E_W[g(Z, W)])]`.  The level-`ℓ` approximation is
`P_ℓ = f(A_{M_ℓ})`, `M_ℓ = 2^ℓ`, with the inner mean `A_M = M⁻¹ ∑_{m<M} g(Z, W⁽ᵐ⁾)` (`nestedP`),
and the level-`ℓ` correction is the antithetic difference of the paper (`nestedDelta`),

  `Y_ℓ = f(A_{2M}) − ½ f(A_M) − ½ f(A'_M)`,   `M = M_{ℓ−1}`,

where `A'_M` is the mean of the second half `W⁽ᴹ⁾, …, W⁽²ᴹ⁻¹⁾` of the inner samples.

* `integral_nestedDelta`: "this has the correct expectation, i.e. `E[Y_ℓ] = E[P_ℓ − P_{ℓ−1}]`",
  because the second half of the inner samples has the law of the first
  (`measurePreserving_shiftSeq`);
* `innerMean_two_mul`: the fine inner mean is the average of the two coarse ones;
* `fiber_sum_moments`, `fiber_nested_moments`: for a fixed outer sample `z` with
  `E_W[g(z, W)⁴] < ∞`, `A_M − A'_M` and `A_M − E_W[g(z, W)]` are signed sums of independent
  centred terms (`signed_sum_eq`, `centred_sum_eq`), so their second moments are `O(M⁻¹)` and the
  fourth moment of `A_M − A'_M` is `O(M⁻²)` (`moments_sum_indep`): the quantitative form of the
  paper's "By the Central Limit Theorem, `Δg₁⁽ⁿ⁾, Δg₂⁽ⁿ⁾ = O(M_ℓ^{−1/2})`".
-/

open MeasureTheory ProbabilityTheory Finset Filter

namespace MLMC

/-! ### Centred moments -/

/-- `(x − y)⁴ ≤ 8 (x⁴ + y⁴)` (Giles 2015, §9.1: bounding the centred fourth moment of the inner
samples): `8x⁴ + 8y⁴ − (x − y)⁴ = (x + y)⁴ + 6(x² − y²)²`. -/
lemma sub_pow_four_le (x y : ℝ) : (x - y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  nlinarith [sq_nonneg ((x + y) ^ 2), sq_nonneg (x ^ 2 - y ^ 2)]

section Centred

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `E[X]² ≤ E[X²]` on a probability space (Giles 2015, §9.1: bounding the moments of the inner
samples). -/
lemma sq_integral_le_integral_sq {X : Ω → ℝ} (hXm : Measurable X)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) : (∫ ω, X ω ∂μ) ^ 2 ≤ ∫ ω, X ω ^ 2 ∂μ := by
  have hX : MemLp X 2 μ := (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).2 hX2
  have h : ∫ ω, X ω ^ 2 ∂μ = variance X μ + (∫ ω, X ω ∂μ) ^ 2 := by
    rw [variance_eq_sub hX]
    simp only [Pi.pow_apply]
    ring
  linarith [variance_nonneg X μ]

/-- **Centred moments** (Giles 2015, §9.1: the inner samples enter through
`Δg = g(Z, W) − E_W[g(Z, W)]`).  For a measurable `Y` with `E[Y⁴] < ∞` on a probability space and
`a = E[Y]`: `(Y − a)⁴` is integrable, `E[(Y − a)⁴] ≤ 16 E[Y⁴]`, `E[(Y − a)²]² ≤ E[(Y − a)⁴]` and
`E[(Y − a)²] ≤ 1 + 16 E[Y⁴]`. -/
theorem centred_moments_le {Y : Ω → ℝ} (hY : Measurable Y)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ) :
    Integrable (fun ω => (Y ω - ∫ x, Y x ∂μ) ^ 4) μ ∧
      ∫ ω, (Y ω - ∫ x, Y x ∂μ) ^ 4 ∂μ ≤ 16 * ∫ ω, Y ω ^ 4 ∂μ ∧
      (∫ ω, (Y ω - ∫ x, Y x ∂μ) ^ 2 ∂μ) ^ 2 ≤ ∫ ω, (Y ω - ∫ x, Y x ∂μ) ^ 4 ∂μ ∧
      ∫ ω, (Y ω - ∫ x, Y x ∂μ) ^ 2 ∂μ ≤ 1 + 16 * ∫ ω, Y ω ^ 4 ∂μ := by
  obtain ⟨a, ha⟩ : ∃ a, a = ∫ x, Y x ∂μ := ⟨_, rfl⟩
  rw [← ha]
  have hY2 : Integrable (fun ω => Y ω ^ 2) μ := integrable_pow_of_pow_four hY h4 (by norm_num)
  have hZm : Measurable fun ω => Y ω - a := hY.sub_const a
  -- `(Y − a)⁴ ≤ 8 (Y⁴ + a⁴)`
  have hdom : Integrable (fun ω => 8 * (Y ω ^ 4 + a ^ 4)) μ :=
    (h4.add (integrable_const (a ^ 4))).const_mul 8
  have hZ4 : Integrable (fun ω => (Y ω - a) ^ 4) μ :=
    hdom.mono' (hZm.pow_const 4).aestronglyMeasurable (Eventually.of_forall fun ω => by
      show ‖(Y ω - a) ^ 4‖ ≤ 8 * (Y ω ^ 4 + a ^ 4)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact sub_pow_four_le _ _)
  -- Jensen for squares: `a² ≤ E[Y²]`, `E[Y²]² ≤ E[Y⁴]` and `E[(Y − a)²]² ≤ E[(Y − a)⁴]`
  have j1 : a ^ 2 ≤ ∫ ω, Y ω ^ 2 ∂μ := by
    rw [ha]
    exact sq_integral_le_integral_sq hY hY2
  have e4 : ∀ ω, Y ω ^ 4 = (Y ω ^ 2) ^ 2 := fun ω => by ring
  have j2 : (∫ ω, Y ω ^ 2 ∂μ) ^ 2 ≤ ∫ ω, Y ω ^ 4 ∂μ := by
    have h := sq_integral_le_integral_sq (hY.pow_const 2) (h4.congr (Eventually.of_forall e4))
    simp only [← e4] at h
    exact h
  have e4' : ∀ ω, (Y ω - a) ^ 4 = ((Y ω - a) ^ 2) ^ 2 := fun ω => by ring
  have j3 : (∫ ω, (Y ω - a) ^ 2 ∂μ) ^ 2 ≤ ∫ ω, (Y ω - a) ^ 4 ∂μ := by
    have h := sq_integral_le_integral_sq (hZm.pow_const 2) (hZ4.congr (Eventually.of_forall e4'))
    simp only [← e4'] at h
    exact h
  have ha4 : a ^ 4 ≤ ∫ ω, Y ω ^ 4 ∂μ :=
    calc a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ ≤ (∫ ω, Y ω ^ 2 ∂μ) ^ 2 := pow_le_pow_left₀ (sq_nonneg a) j1 2
      _ ≤ ∫ ω, Y ω ^ 4 ∂μ := j2
  have hk : ∫ ω, (Y ω - a) ^ 4 ∂μ ≤ 16 * ∫ ω, Y ω ^ 4 ∂μ := by
    have h := integral_mono hZ4 hdom fun ω => sub_pow_four_le (Y ω) a
    rw [integral_const_mul, integral_add h4 (integrable_const _), integral_const, probReal_univ,
      one_smul] at h
    linarith
  have hs0 : 0 ≤ ∫ ω, (Y ω - a) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hm0 : 0 ≤ ∫ ω, Y ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
  refine ⟨hZ4, hk, j3, ?_⟩
  nlinarith [sq_nonneg (∫ ω, (Y ω - a) ^ 2 ∂μ - 1)]

end Centred

/-! ### The nested model -/

section Model

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲]

/-- The mean `M⁻¹ ∑_{m<M} g(z, w_m)` of the first `M` inner samples (Giles 2015, §9.1:
"`M⁻¹ ∑_{m=1}^{M} g(Z⁽ⁿ⁾, W⁽ᵐ'ⁿ⁾)`"). -/
noncomputable def innerMean (g : 𝒵 → 𝒲 → ℝ) (M : ℕ) (z : 𝒵) (w : ℕ → 𝒲) : ℝ :=
  (M : ℝ)⁻¹ * ∑ m ∈ range M, g z (w m)

/-- The inner samples from the `M`-th on, `m ↦ w_{M+m}` (Giles 2015, §9.1: with `M = M_{ℓ−1}`,
the second half "`m = M_{ℓ−1}+1, …, M_ℓ`" of the level-`ℓ` inner samples). -/
def shiftSeq (M : ℕ) (w : ℕ → 𝒲) : ℕ → 𝒲 := fun m => w (M + m)

/-- The sign `+1` on the first `M` inner samples and `−1` on the others (Giles 2015, §9.1: the
difference `A_M − A'_M` of the two coarse inner means). -/
noncomputable def nestedSign (M m : ℕ) : ℝ := if m < M then 1 else -1

/-- The law of the inner samples `W⁽⁰⁾, W⁽¹⁾, …`, independent with law `ρ` (Giles 2015, §9.1). -/
noncomputable abbrev innerLaw (ρ : Measure 𝒲) : Measure (ℕ → 𝒲) :=
  Measure.infinitePi fun _ : ℕ => ρ

/-- The joint law `ν ⊗ ρ^{⊗ℕ}` of the outer variable `Z ~ ν` and the independent inner samples
`W⁽⁰⁾, W⁽¹⁾, … ~ ρ` (Giles 2015, §9.1). -/
noncomputable abbrev nestedLaw (ν : Measure 𝒵) (ρ : Measure 𝒲) : Measure (𝒵 × (ℕ → 𝒲)) :=
  ν.prod (innerLaw ρ)

/-- The level-`ℓ` approximation `P_ℓ = f(M_ℓ⁻¹ ∑_{m<M_ℓ} g(Z, W⁽ᵐ⁾))`, `M_ℓ = 2^ℓ` (Giles 2015,
§9.1: "`E[P_ℓ] ≡ E_Z[f(M_ℓ⁻¹ ∑_m g(Z, W⁽ᵐ⁾))]`" and "on level `ℓ` we can use `M_ℓ = 2^ℓ` inner
samples"). -/
noncomputable def nestedP (f : ℝ → ℝ) (g : 𝒵 → 𝒲 → ℝ) (ℓ : ℕ) (p : 𝒵 × (ℕ → 𝒲)) : ℝ :=
  f (innerMean g (2 ^ ℓ) p.1 p.2)

/-- The antithetic level correction for one outer sample (Giles 2015, §9.1, p. 57): `P₀` on level
`0` and, on level `ℓ + 1` with `M = 2^ℓ`, `f(A_{2M}) − ½ f(A_M) − ½ f(A'_M)`, where `A_M` and
`A'_M` are the means of the first and of the second `M` of the `2M` inner samples. -/
noncomputable def nestedDelta (f : ℝ → ℝ) (g : 𝒵 → 𝒲 → ℝ) : ℕ → 𝒵 × (ℕ → 𝒲) → ℝ
  | 0 => nestedP f g 0
  | ℓ + 1 => fun p => f (innerMean g (2 ^ (ℓ + 1)) p.1 p.2) -
      f (innerMean g (2 ^ ℓ) p.1 p.2) / 2 - f (innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2

lemma nestedSign_sq (M m : ℕ) : nestedSign M m ^ 2 = 1 := by
  unfold nestedSign
  split_ifs <;> norm_num

/-- **The fine inner mean is the average of the two coarse ones** (Giles 2015, §9.1: "split the
`M_ℓ` samples of `W` for the fine value into two subsets of size `M_{ℓ−1}` for the coarse
value"): `A_{2M} = ½ (A_M + A'_M)`. -/
theorem innerMean_two_mul (g : 𝒵 → 𝒲 → ℝ) (M : ℕ) (z : 𝒵) (w : ℕ → 𝒲) :
    innerMean g (2 * M) z w = (innerMean g M z w + innerMean g M z (shiftSeq M w)) / 2 := by
  simp only [innerMean, shiftSeq]
  rw [two_mul, Finset.sum_range_add, Nat.cast_add, ← two_mul, mul_inv]
  ring

/-- **The two coarse means as a signed sum** (Giles 2015, §9.1): for every `a`,
`A_M − A'_M = M⁻¹ ∑_{m<2M} s_m (g(z, w_m) − a)` with `s_m = +1` for `m < M` and `−1` otherwise. -/
lemma signed_sum_eq (g : 𝒵 → 𝒲 → ℝ) (M : ℕ) (z : 𝒵) (w : ℕ → 𝒲) (a : ℝ) :
    innerMean g M z w - innerMean g M z (shiftSeq M w) =
      (M : ℝ)⁻¹ * ∑ m ∈ range (2 * M), nestedSign M m * (g z (w m) - a) := by
  rw [two_mul, Finset.sum_range_add]
  have h1 : ∑ m ∈ range M, nestedSign M m * (g z (w m) - a) = ∑ m ∈ range M, (g z (w m) - a) :=
    Finset.sum_congr rfl fun m hm => by
      rw [nestedSign, if_pos (Finset.mem_range.1 hm), one_mul]
  have h2 : ∑ m ∈ range M, nestedSign M (M + m) * (g z (w (M + m)) - a) =
      -∑ m ∈ range M, (g z (w (M + m)) - a) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [nestedSign, if_neg (by omega), neg_one_mul]
  rw [h1, h2, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [innerMean, shiftSeq]
  ring

/-- **The inner mean minus a constant as a sum** (Giles 2015, §9.1): for `M ≥ 1` and every `a`,
`A_M − a = M⁻¹ ∑_{m<M} (g(z, w_m) − a)` (written with the sign `s_m = +1`, `m < M`). -/
lemma centred_sum_eq (g : 𝒵 → 𝒲 → ℝ) {M : ℕ} (hM : 0 < M) (z : 𝒵) (w : ℕ → 𝒲) (a : ℝ) :
    innerMean g M z w - a = (M : ℝ)⁻¹ * ∑ m ∈ range M, nestedSign M m * (g z (w m) - a) := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have h0 : ∑ m ∈ range M, nestedSign M m * (g z (w m) - a) = ∑ m ∈ range M, (g z (w m) - a) :=
    Finset.sum_congr rfl fun m hm => by
      rw [nestedSign, if_pos (Finset.mem_range.1 hm), one_mul]
  rw [h0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, innerMean,
    mul_sub, ← mul_assoc, inv_mul_cancel₀ hM', one_mul]

/-- The inner mean is measurable on `𝒵 × 𝒲^ℕ` (after a measurable map of the inner samples). -/
lemma measurable_innerMean {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g)) (M : ℕ)
    {s : (ℕ → 𝒲) → ℕ → 𝒲} (hs : Measurable s) :
    Measurable fun p : 𝒵 × (ℕ → 𝒲) => innerMean g M p.1 (s p.2) := by
  unfold innerMean
  refine Measurable.const_mul (Finset.measurable_sum _ fun m _ => ?_) _
  exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply m).comp (hs.comp measurable_snd)))

lemma measurable_shiftSeq (M : ℕ) : Measurable (shiftSeq (𝒲 := 𝒲) M) :=
  measurable_pi_lambda _ fun m => measurable_pi_apply (M + m)

/-- **The second half of the inner samples has the law of the first** (Giles 2015, §9.1): the
shift `w ↦ (w_{M+m})_m` preserves `ρ^{⊗ℕ}`. -/
theorem measurePreserving_shiftSeq (ρ : Measure 𝒲) [IsProbabilityMeasure ρ] (M : ℕ) :
    MeasurePreserving (shiftSeq M) (innerLaw ρ) (innerLaw ρ) :=
  ⟨measurable_shiftSeq M, Measure.map_infinitePi_infinitePi_of_inj (add_right_injective M)⟩

/-- **The antithetic correction has the correct expectation** (Giles 2015, §9.1, p. 57: "Note that
this has the correct expectation, i.e. `E[Y_ℓ] = E[P_ℓ − P_{ℓ−1}]`").  If every `P_ℓ` is
integrable, then `E[Y_ℓ] = E[P_ℓ − P_{ℓ−1}]` for every `ℓ` (`P_{−1} ≡ 0`), because the second half
of the inner samples has the same law as the first. -/
theorem integral_nestedDelta (ν : Measure 𝒵) [IsProbabilityMeasure ν] (ρ : Measure 𝒲)
    [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (g : 𝒵 → 𝒲 → ℝ)
    (hint : ∀ ℓ, Integrable (nestedP f g ℓ) (nestedLaw ν ρ)) (ℓ : ℕ) :
    ∫ p, nestedDelta f g ℓ p ∂(nestedLaw ν ρ) =
      ∫ p, levelDiff (nestedP f g) ℓ p ∂(nestedLaw ν ρ) := by
  cases ℓ with
  | zero => rfl
  | succ ℓ =>
    have hφ : MeasurePreserving (fun p : 𝒵 × (ℕ → 𝒲) => (p.1, shiftSeq (2 ^ ℓ) p.2))
        (nestedLaw ν ρ) (nestedLaw ν ρ) :=
      (MeasurePreserving.id ν).prod (measurePreserving_shiftSeq ρ (2 ^ ℓ))
    have hsame : ∫ p, f (innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ∂(nestedLaw ν ρ) =
        ∫ p, nestedP f g ℓ p ∂(nestedLaw ν ρ) :=
      integral_comp_of_measurePreserving hφ (hint ℓ).aestronglyMeasurable
    have hint2 : Integrable (fun p : 𝒵 × (ℕ → 𝒲) =>
        f (innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2))) (nestedLaw ν ρ) :=
      hφ.integrable_comp_of_integrable (hint ℓ)
    have hA : Integrable (fun p => nestedP f g (ℓ + 1) p - nestedP f g ℓ p / 2)
        (nestedLaw ν ρ) :=
      (hint (ℓ + 1)).sub ((hint ℓ).div_const 2)
    show ∫ p, (nestedP f g (ℓ + 1) p - nestedP f g ℓ p / 2 -
        f (innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2) ∂(nestedLaw ν ρ) =
      ∫ p, (nestedP f g (ℓ + 1) p - nestedP f g ℓ p) ∂(nestedLaw ν ρ)
    rw [integral_sub hA (hint2.div_const 2), integral_sub (hint (ℓ + 1)) ((hint ℓ).div_const 2),
      integral_div, integral_div, hsame, integral_sub (hint (ℓ + 1)) (hint ℓ)]
    ring

end Model

/-! ### Moments of the inner means for a fixed outer sample -/

section Fiber

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ρ : Measure 𝒲)
  [IsProbabilityMeasure ρ]

/-- **Moments of a signed sum of centred inner samples** (Giles 2015, §9.1, p. 58: "By the Central
Limit Theorem, `Δg₁⁽ⁿ⁾, Δg₂⁽ⁿ⁾ = O(M_ℓ^{−1/2})`").  Let `h : 𝒲 → ℝ` be measurable with
`E[h(W)⁴] < ∞`, `a = E[h(W)]`, and let `c_m = ±1`.  For independent `W⁽ᵐ⁾ ~ ρ`, the sum
`S_n = ∑_{m<n} c_m (h(W⁽ᵐ⁾) − a)` has `S_n⁴` integrable, `E[S_n] = 0`, `E[S_n²] = n σ²` and
`E[S_n⁴] ≤ n κ + 3 n² σ⁴`, where `σ² = E[(h(W) − a)²]` and `κ = E[(h(W) − a)⁴]`. -/
theorem fiber_sum_moments {h : 𝒲 → ℝ} (hh : Measurable h)
    (h4 : Integrable (fun v => h v ^ 4) ρ) (c : ℕ → ℝ) (hc : ∀ m, c m ^ 2 = 1) (n : ℕ) :
    Integrable (fun w : ℕ → 𝒲 => (∑ m ∈ range n, c m * (h (w m) - ∫ v, h v ∂ρ)) ^ 4)
        (innerLaw ρ) ∧
      ∫ w, ∑ m ∈ range n, c m * (h (w m) - ∫ v, h v ∂ρ) ∂(innerLaw ρ) = 0 ∧
      ∫ w, (∑ m ∈ range n, c m * (h (w m) - ∫ v, h v ∂ρ)) ^ 2 ∂(innerLaw ρ) =
        n * ∫ v, (h v - ∫ u, h u ∂ρ) ^ 2 ∂ρ ∧
      ∫ w, (∑ m ∈ range n, c m * (h (w m) - ∫ v, h v ∂ρ)) ^ 4 ∂(innerLaw ρ) ≤
        n * ∫ v, (h v - ∫ u, h u ∂ρ) ^ 4 ∂ρ +
          3 * n ^ 2 * (∫ v, (h v - ∫ u, h u ∂ρ) ^ 2 ∂ρ) ^ 2 := by
  obtain ⟨hZ4, -, -, -⟩ := centred_moments_le hh h4
  obtain ⟨a, ha⟩ : ∃ a, a = ∫ v, h v ∂ρ := ⟨_, rfl⟩
  rw [← ha] at hZ4 ⊢
  have hh1 : Integrable h ρ := by
    simpa using integrable_pow_of_pow_four hh h4 (k := 1) (by norm_num)
  have hc2 : ∀ m x, (c m * x) ^ 2 = x ^ 2 := fun m x => by rw [mul_pow, hc m, one_mul]
  have hc4 : ∀ m x, (c m * x) ^ 4 = x ^ 4 := fun m x => by
    rw [mul_pow, show c m ^ 4 = (c m ^ 2) ^ 2 by ring, hc m, one_pow, one_mul]
  have hev : ∀ m, MeasurePreserving (Function.eval m) (innerLaw ρ) ρ := fun m =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => ρ) m
  have hind : iIndepFun (fun m (w : ℕ → 𝒲) => c m * (h (w m) - a)) (innerLaw ρ) :=
    iIndepFun_infinitePi (X := fun m v => c m * (h v - a)) fun m =>
      (hh.sub_const a).const_mul (c m)
  have hXm : ∀ m, Measurable fun w : ℕ → 𝒲 => c m * (h (w m) - a) := fun m =>
    ((hh.comp (measurable_pi_apply m)).sub_const a).const_mul (c m)
  have hX4 : ∀ m, Integrable (fun w : ℕ → 𝒲 => (c m * (h (w m) - a)) ^ 4) (innerLaw ρ) :=
    fun m => by
      have h1 : Integrable (fun w : ℕ → 𝒲 => (h (w m) - a) ^ 4) (innerLaw ρ) :=
        (hev m).integrable_comp_of_integrable hZ4
      exact h1.congr (Eventually.of_forall fun w => (hc4 m _).symm)
  have hX0 : ∀ m, ∫ w, c m * (h (w m) - a) ∂(innerLaw ρ) = 0 := fun m => by
    have e : ∫ w, c m * (h (w m) - a) ∂(innerLaw ρ) = ∫ v, c m * (h v - a) ∂ρ :=
      integral_comp_of_measurePreserving (hev m)
        ((hh.sub_const a).const_mul (c m)).aestronglyMeasurable
    rw [e, integral_const_mul, integral_sub hh1 (integrable_const a), integral_const,
      probReal_univ, one_smul, ← ha, sub_self, mul_zero]
  have hv : ∀ m, ∫ w, (c m * (h (w m) - a)) ^ 2 ∂(innerLaw ρ) = ∫ v, (h v - a) ^ 2 ∂ρ :=
    fun m => by
      simp_rw [hc2]
      exact integral_comp_of_measurePreserving (hev m)
        ((hh.sub_const a).pow_const 2).aestronglyMeasurable
  have hq : ∀ m, ∫ w, (c m * (h (w m) - a)) ^ 4 ∂(innerLaw ρ) ≤ ∫ v, (h v - a) ^ 4 ∂ρ :=
    fun m => by
      simp_rw [hc4]
      exact (integral_comp_of_measurePreserving (hev m)
        ((hh.sub_const a).pow_const 4).aestronglyMeasurable).le
  obtain ⟨m4, m2, m4le⟩ := moments_sum_indep hind hXm hX4 hX0 hv hq n
  have hX1 : ∀ m, Integrable (fun w : ℕ → 𝒲 => c m * (h (w m) - a)) (innerLaw ρ) := fun m => by
    simpa using integrable_pow_of_pow_four (hXm m) (hX4 m) (k := 1) (by norm_num)
  refine ⟨m4, ?_, m2, m4le⟩
  rw [integral_finset_sum _ fun m _ => hX1 m]
  exact Finset.sum_eq_zero fun m _ => hX0 m

/-- **The moments of the nested differences for a fixed outer sample** (Giles 2015, §9.1, p. 58:
"By the Central Limit Theorem, `Δg₁⁽ⁿ⁾, Δg₂⁽ⁿ⁾ = O(M_ℓ^{−1/2})` and therefore
`f″(E[g(Z⁽ⁿ⁾, W)])(Δg₁⁽ⁿ⁾ − Δg₂⁽ⁿ⁾)² = O(M_ℓ⁻¹)`").  Fix `z` with `E_W[g(z, W)⁴] =: m₄ < ∞`, let
`G = E_W[g(z, W)]`, and let `M ≥ 1`.  Then, over the inner samples,
`(A_M − A'_M)⁴` and `(A_M − G)⁴` are integrable, `M E[(A_M − A'_M)²] ≤ 2(1 + 16 m₄)`,
`M² E[(A_M − A'_M)⁴] ≤ 224 m₄`, `M E[(A_M − G)²] ≤ 1 + 16 m₄` and `E[A_M − G] = 0`. -/
theorem fiber_nested_moments (g : 𝒵 → 𝒲 → ℝ) (z : 𝒵) (hgz : Measurable (g z))
    (hgz4 : Integrable (fun v => g z v ^ 4) ρ) {M : ℕ} (hM : 0 < M) :
    Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 4)
        (innerLaw ρ) ∧
      (M : ℝ) * ∫ w, (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 2 ∂(innerLaw ρ) ≤
        2 * (1 + 16 * ∫ v, g z v ^ 4 ∂ρ) ∧
      (M : ℝ) ^ 2 * ∫ w, (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 4
          ∂(innerLaw ρ) ≤ 224 * ∫ v, g z v ^ 4 ∂ρ ∧
      Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 4) (innerLaw ρ) ∧
      (M : ℝ) * ∫ w, (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 2 ∂(innerLaw ρ) ≤
        1 + 16 * ∫ v, g z v ^ 4 ∂ρ ∧
      ∫ w, (innerMean g M z w - ∫ v, g z v ∂ρ) ∂(innerLaw ρ) = 0 := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have ht : (M : ℝ)⁻¹ * M = 1 := inv_mul_cancel₀ hMr.ne'
  have ht1 : (M : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Nat.one_le_cast.2 hM)
  obtain ⟨-, hk, hsk, hs⟩ := centred_moments_le hgz hgz4
  obtain ⟨i4, -, e2, e4⟩ :=
    fiber_sum_moments ρ hgz hgz4 (nestedSign M) (nestedSign_sq M) (2 * M)
  obtain ⟨j4, j1, f2, -⟩ := fiber_sum_moments ρ hgz hgz4 (nestedSign M) (nestedSign_sq M) M
  obtain ⟨G, hG⟩ : ∃ G, G = ∫ v, g z v ∂ρ := ⟨_, rfl⟩
  rw [← hG] at hk hsk hs i4 e2 e4 j4 j1 f2 ⊢
  have hD : ∀ w, innerMean g M z w - innerMean g M z (shiftSeq M w) =
      (M : ℝ)⁻¹ * ∑ m ∈ range (2 * M), nestedSign M m * (g z (w m) - G) :=
    fun w => signed_sum_eq g M z w G
  have hE : ∀ w, innerMean g M z w - G =
      (M : ℝ)⁻¹ * ∑ m ∈ range M, nestedSign M m * (g z (w m) - G) :=
    fun w => centred_sum_eq g hM z w G
  simp only [hD, hE, mul_pow]
  have hk0 : 0 ≤ ∫ v, (g z v - G) ^ 4 ∂ρ := integral_nonneg fun v => by positivity
  have hm0 : 0 ≤ ∫ v, g z v ^ 4 ∂ρ := integral_nonneg fun v => by positivity
  refine ⟨i4.const_mul _, ?_, ?_, j4.const_mul _, ?_, ?_⟩
  · rw [integral_const_mul, e2]
    push_cast
    calc (M : ℝ) * ((M : ℝ)⁻¹ ^ 2 * (2 * M * ∫ v, (g z v - G) ^ 2 ∂ρ))
        = 2 * (∫ v, (g z v - G) ^ 2 ∂ρ) * ((M : ℝ)⁻¹ * M) ^ 2 := by ring
      _ ≤ 2 * (1 + 16 * ∫ v, g z v ^ 4 ∂ρ) := by rw [ht]; linarith
  · rw [integral_const_mul]
    have e4' : ∫ w, (∑ m ∈ range (2 * M), nestedSign M m * (g z (w m) - G)) ^ 4 ∂(innerLaw ρ) ≤
        2 * M * (∫ v, (g z v - G) ^ 4 ∂ρ) +
          3 * (2 * M) ^ 2 * (∫ v, (g z v - G) ^ 2 ∂ρ) ^ 2 := by
      have h := e4
      push_cast at h
      linarith
    calc (M : ℝ) ^ 2 * ((M : ℝ)⁻¹ ^ 4 *
          ∫ w, (∑ m ∈ range (2 * M), nestedSign M m * (g z (w m) - G)) ^ 4 ∂(innerLaw ρ))
        ≤ (M : ℝ) ^ 2 * ((M : ℝ)⁻¹ ^ 4 * (2 * M * (∫ v, (g z v - G) ^ 4 ∂ρ) +
          3 * (2 * M) ^ 2 * (∫ v, (g z v - G) ^ 2 ∂ρ) ^ 2)) := by gcongr
      _ = 2 * (M : ℝ)⁻¹ * (∫ v, (g z v - G) ^ 4 ∂ρ) * ((M : ℝ)⁻¹ * M) ^ 3 +
          12 * (∫ v, (g z v - G) ^ 2 ∂ρ) ^ 2 * ((M : ℝ)⁻¹ * M) ^ 4 := by ring
      _ ≤ 224 * ∫ v, g z v ^ 4 ∂ρ := by
          simp only [ht, one_pow, mul_one]
          linarith [mul_le_mul_of_nonneg_right ht1 hk0]
  · rw [integral_const_mul, f2]
    calc (M : ℝ) * ((M : ℝ)⁻¹ ^ 2 * (M * ∫ v, (g z v - G) ^ 2 ∂ρ))
        = (∫ v, (g z v - G) ^ 2 ∂ρ) * ((M : ℝ)⁻¹ * M) ^ 2 := by ring
      _ ≤ 1 + 16 * ∫ v, g z v ^ 4 ∂ρ := by rw [ht]; linarith
  · rw [integral_const_mul, j1, mul_zero]

end Fiber

end MLMC
