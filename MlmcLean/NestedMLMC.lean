import MlmcLean.NestedSimulation
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul

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

**The rates and the complexity.**  The paper assumes `f` twice differentiable and argues with a
Taylor expansion and the Central Limit Theorem.  Here `f` is differentiable with a `K`-Lipschitz
derivative (for instance `|f″| ≤ K`) and `E[g(Z, W)⁴] < ∞`; then, with explicit constants,

* `nested_mean_rate`, `nested_variance_rate`: "`E[Y_ℓ] = O(M_ℓ⁻¹)` and `V_ℓ = O(M_ℓ⁻²)`", from
  the pointwise bound `|Y_{ℓ+1}| ≤ (K/8)(A_M − A'_M)²` (`abs_nestedDelta_le`) and the fibre
  moments, averaged over the outer sample (`integrable_of_fiber_bound`);
* `nested_bias_rate`: the bias `|E[P_ℓ] − E_Z[f(E_W[g(Z, W)])]|` of the level-`ℓ` approximation
  is `O(M_ℓ⁻¹)` (`fiber_bias_le`), which is the rate `α = 1` of the MLMC theorem;
* `nested_mlmc_complexity`: "this corresponds to `α = 1`, `β = 2`, `γ = 1`, so the complexity is
  `O(ε⁻²)`" — Giles' Theorem 1 (`giles_theorem1_corrections`) for the antithetic nested estimator
  with independent samples, every hypothesis of the theorem being derived; with the samples
  realised as the coordinates of a product space (`nested_mlmc_complexity_iid`), nothing is
  assumed beyond `f`, `g` and the laws `ν`, `ρ`.
-/

open MeasureTheory ProbabilityTheory Finset Filter

namespace MLMC

/-! ### Centred moments -/

/-- `(x − y)⁴ ≤ 8 (x⁴ + y⁴)` (Giles 2015, §9.1: bounding the centred fourth moment of the inner
samples): `8x⁴ + 8y⁴ − (x − y)⁴ = (x + y)⁴ + 6(x² − y²)²`. -/
lemma sub_pow_four_le (x y : ℝ) : (x - y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  nlinarith [sq_nonneg ((x + y) ^ 2), sq_nonneg (x ^ 2 - y ^ 2)]

/-- The Lipschitz constant of a derivative is nonnegative (Giles 2015, §9.1: `|f″| ≤ K`). -/
lemma lipschitz_const_nonneg {f' : ℝ → ℝ} {K : ℝ}
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) : 0 ≤ K := by
  have h := hf' 0 1 zero_le_one
  have h0 := abs_nonneg (f' 1 - f' 0)
  linarith

/-- **Quadratic growth** (Giles 2015, §9.1: `f` with a bounded second derivative).  If `f′` is
`K`-Lipschitz, then `|f(y)| ≤ |f(0)| + |f′(0)| + (|f′(0)| + K/2) y²` for every `y`. -/
lemma abs_le_quadratic {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) (y : ℝ) :
    |f y| ≤ |f 0| + |f' 0| + (|f' 0| + K / 2) * y ^ 2 := by
  have h := abs_taylor_first_le hf hf' 0 y
  rw [sub_zero] at h
  have hy : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y, abs_nonneg y]
  have h1 : |f' 0 * y| ≤ |f' 0| + |f' 0| * y ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hy (abs_nonneg (f' 0))]
  have t1 := abs_add_le (f y - f 0 - f' 0 * y + f 0) (f' 0 * y)
  have t2 := abs_add_le (f y - f 0 - f' 0 * y) (f 0)
  have e : f y - f 0 - f' 0 * y + f 0 + f' 0 * y = f y := by ring
  rw [e] at t1
  linarith

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

/-- **Square-integrability of `f(X)`** (Giles 2015, §9.1: the level approximations `f(A_M)` and
the quantity of interest `f(E_W[g(Z, W)])`).  If `f′` is `K`-Lipschitz and `E[X⁴] < ∞`, then
`f(X)` is square-integrable, because `f` grows at most quadratically (`abs_le_quadratic`). -/
lemma memLp_two_comp_of_pow_four {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {X : Ω → ℝ} (hX : Measurable X)
    (hX4 : Integrable (fun ω => X ω ^ 4) μ) : MemLp (fun ω => f (X ω)) 2 μ := by
  have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hfX : Measurable fun ω => f (X ω) := hfd.continuous.measurable.comp hX
  refine (memLp_two_iff_integrable_sq hfX.aestronglyMeasurable).2 ?_
  refine ((integrable_const (2 * (|f 0| + |f' 0|) ^ 2)).add
    (hX4.const_mul (2 * (|f' 0| + K / 2) ^ 2))).mono' (hfX.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  show ‖f (X ω) ^ 2‖ ≤ 2 * (|f 0| + |f' 0|) ^ 2 + 2 * (|f' 0| + K / 2) ^ 2 * X ω ^ 4
  have hq := abs_le_quadratic hf hf' (X ω)
  have hsq : f (X ω) ^ 2 ≤ (|f 0| + |f' 0| + (|f' 0| + K / 2) * X ω ^ 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hq 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (|f 0| + |f' 0| - (|f' 0| + K / 2) * X ω ^ 2)]

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

/-- The quantity of interest for one outer sample, `f(E_W[g(z, W)])` (Giles 2015, §9.1: the
quantity to be estimated is "`E_Z[f(E_W[g(Z, W)])]`"), as a function on `𝒵 × 𝒲^ℕ` that ignores the
inner samples. -/
noncomputable def nestedTarget (f : ℝ → ℝ) (g : 𝒵 → 𝒲 → ℝ) (ρ : Measure 𝒲)
    (p : 𝒵 × (ℕ → 𝒲)) : ℝ :=
  f (∫ v, g p.1 v ∂ρ)

lemma nestedSign_sq (M m : ℕ) : nestedSign M m ^ 2 = 1 := by
  unfold nestedSign
  split_ifs <;> norm_num

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
/-- **The fine inner mean is the average of the two coarse ones** (Giles 2015, §9.1: "split the
`M_ℓ` samples of `W` for the fine value into two subsets of size `M_{ℓ−1}` for the coarse
value"): `A_{2M} = ½ (A_M + A'_M)`. -/
theorem innerMean_two_mul (g : 𝒵 → 𝒲 → ℝ) (M : ℕ) (z : 𝒵) (w : ℕ → 𝒲) :
    innerMean g (2 * M) z w = (innerMean g M z w + innerMean g M z (shiftSeq M w)) / 2 := by
  simp only [innerMean, shiftSeq]
  rw [two_mul, Finset.sum_range_add, Nat.cast_add, ← two_mul, mul_inv]
  ring

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
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

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
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

omit [MeasurableSpace 𝒵] in
/-- For a fixed outer sample the inner mean is measurable in the inner samples. -/
lemma measurable_innerMean_right {g : 𝒵 → 𝒲 → ℝ} {z : 𝒵} (hgz : Measurable (g z)) (M : ℕ) :
    Measurable fun w : ℕ → 𝒲 => innerMean g M z w := by
  unfold innerMean
  refine Measurable.const_mul (Finset.measurable_sum _ fun m _ => ?_) _
  exact hgz.comp (measurable_pi_apply m)

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
  rw [integral_finsetSum _ fun m _ => hX1 m]
  exact Finset.sum_eq_zero fun m _ => hX0 m

omit [MeasurableSpace 𝒵] in
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

omit [MeasurableSpace 𝒵] in
/-- **The bias for a fixed outer sample** (Giles 2015, §9.1, p. 58: the Taylor expansion of `f`
about `E[g(Z⁽ⁿ⁾, W)]` together with "`Δg = O(M_ℓ^{−1/2})`"; the first-order term has mean zero).
Let `f′` be `K`-Lipschitz, fix `z` with `E_W[g(z, W)⁴] =: m₄ < ∞`, let `G = E_W[g(z, W)]` and
`M ≥ 1`.  Then `M |E_W[f(A_M) − f(G)]| ≤ (K/2)(1 + 16 m₄)`. -/
theorem fiber_bias_le {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) (g : 𝒵 → 𝒲 → ℝ) (z : 𝒵)
    (hgz : Measurable (g z)) (hgz4 : Integrable (fun v => g z v ^ 4) ρ) {M : ℕ} (hM : 0 < M) :
    (M : ℝ) * |∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ)| ≤
      K / 2 * (1 + 16 * ∫ v, g z v ^ 4 ∂ρ) := by
  have hK := lipschitz_const_nonneg hf'
  have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hfm : Measurable f := hfd.continuous.measurable
  obtain ⟨-, -, -, i4, h2, h0⟩ := fiber_nested_moments ρ g z hgz hgz4 hM
  obtain ⟨G, hG⟩ : ∃ G, G = ∫ v, g z v ∂ρ := ⟨_, rfl⟩
  rw [← hG] at i4 h2 h0 ⊢
  have hA : Measurable fun w : ℕ → 𝒲 => innerMean g M z w := measurable_innerMean_right hgz M
  have hAG : Measurable fun w : ℕ → 𝒲 => innerMean g M z w - G := hA.sub_const G
  have hA1 : Integrable (fun w : ℕ → 𝒲 => innerMean g M z w - G) (innerLaw ρ) := by
    simpa using integrable_pow_of_pow_four hAG i4 (k := 1) (by norm_num)
  have hA2 : Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - G) ^ 2) (innerLaw ρ) :=
    integrable_pow_of_pow_four hAG i4 (by norm_num)
  -- the remainder of the first-order Taylor expansion about `G`
  have hRb : ∀ w : ℕ → 𝒲, |f (innerMean g M z w) - f G - f' G * (innerMean g M z w - G)| ≤
      K / 2 * (innerMean g M z w - G) ^ 2 := fun w => abs_taylor_first_le hf hf' G _
  have hR : Integrable (fun w : ℕ → 𝒲 =>
      f (innerMean g M z w) - f G - f' G * (innerMean g M z w - G)) (innerLaw ρ) :=
    (hA2.const_mul (K / 2)).mono'
      (((hfm.comp hA).sub_const (f G)).sub (hAG.const_mul (f' G))).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        exact hRb w)
  have e : ∫ w, (f (innerMean g M z w) - f G) ∂(innerLaw ρ) =
      ∫ w, (f' G * (innerMean g M z w - G) +
        (f (innerMean g M z w) - f G - f' G * (innerMean g M z w - G))) ∂(innerLaw ρ) :=
    integral_congr_ae (Eventually.of_forall fun w => by ring)
  rw [e, integral_add (hA1.const_mul (f' G)) hR, integral_const_mul, h0, mul_zero, zero_add]
  have hRint : ∫ w, |f (innerMean g M z w) - f G - f' G * (innerMean g M z w - G)|
      ∂(innerLaw ρ) ≤ K / 2 * ∫ w, (innerMean g M z w - G) ^ 2 ∂(innerLaw ρ) := by
    rw [← integral_const_mul]
    exact integral_mono hR.abs (hA2.const_mul _) hRb
  have hK2 : 0 ≤ K / 2 := div_nonneg hK (by norm_num)
  calc (M : ℝ) * |∫ w, (f (innerMean g M z w) - f G - f' G * (innerMean g M z w - G))
        ∂(innerLaw ρ)|
      ≤ (M : ℝ) * (K / 2 * ∫ w, (innerMean g M z w - G) ^ 2 ∂(innerLaw ρ)) :=
        mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs.trans hRint) (Nat.cast_nonneg M)
    _ = K / 2 * ((M : ℝ) * ∫ w, (innerMean g M z w - G) ^ 2 ∂(innerLaw ρ)) := by ring
    _ ≤ K / 2 * (1 + 16 * ∫ v, g z v ^ 4 ∂ρ) := mul_le_mul_of_nonneg_left h2 hK2

end Fiber

/-! ### The rates on `𝒵 × 𝒲^ℕ` -/

section Product

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **Averaging fibre bounds over the outer sample** (Giles 2015, §9.1: the moments conditional on
the outer sample `Z` are averaged over `Z`; Fubini–Tonelli).  A measurable `F ≥ 0` on `𝒵 × 𝒲^ℕ`
whose fibre integrals are `ν`-a.e. finite and bounded by an integrable `B` is integrable for
`ν ⊗ ρ^{⊗ℕ}`, and `∫ F ≤ ∫ B`. -/
lemma integrable_of_fiber_bound {F : 𝒵 × (ℕ → 𝒲) → ℝ} (hFm : Measurable F)
    (hF0 : ∀ p, 0 ≤ F p) {B : 𝒵 → ℝ} (hB : Integrable B ν)
    (hfib : ∀ᵐ z ∂ν, Integrable (fun w => F (z, w)) (innerLaw ρ) ∧
      ∫ w, F (z, w) ∂(innerLaw ρ) ≤ B z) :
    Integrable F (nestedLaw ν ρ) ∧ ∫ p, F p ∂(nestedLaw ν ρ) ≤ ∫ z, B z ∂ν := by
  have hFae : AEStronglyMeasurable F (ν.prod (innerLaw ρ)) := hFm.aestronglyMeasurable
  have hint : Integrable F (nestedLaw ν ρ) := by
    refine (integrable_prod_iff hFae).2 ⟨hfib.mono fun z hz => hz.1, ?_⟩
    refine hB.mono' hFae.norm.integral_prod_right' (hfib.mono fun z hz => ?_)
    show ‖∫ w, ‖F (z, w)‖ ∂(innerLaw ρ)‖ ≤ B z
    have e1 : ∫ w, ‖F (z, w)‖ ∂(innerLaw ρ) = ∫ w, F (z, w) ∂(innerLaw ρ) :=
      integral_congr_ae (Eventually.of_forall fun w => Real.norm_of_nonneg (hF0 _))
    have e2 : ‖∫ w, F (z, w) ∂(innerLaw ρ)‖ = ∫ w, F (z, w) ∂(innerLaw ρ) :=
      Real.norm_of_nonneg (integral_nonneg fun w => hF0 _)
    rw [e1, e2]
    exact hz.2
  exact ⟨hint, (integral_prod F hint).trans_le
    (integral_mono_ae hint.integral_prod_left hB (hfib.mono fun z hz => hz.2))⟩

/-- **The fourth moment of `g`, fibre by fibre** (Giles 2015, §9.1).  If `E[g(Z, W)⁴] < ∞` for
`(Z, W) ~ ν ⊗ ρ`, then `E_W[g(z, W)⁴] < ∞` for `ν`-a.e. `z`, and `z ↦ E_W[g(z, W)⁴]` is
`ν`-integrable with integral `E[g(Z, W)⁴]` (Fubini). -/
lemma fourth_moment_fibers {g : 𝒵 → 𝒲 → ℝ}
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) :
    (∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ) ∧
      Integrable (fun z => ∫ v, g z v ^ 4 ∂ρ) ν ∧
      ∫ z, ∫ v, g z v ^ 4 ∂ρ ∂ν = ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ) :=
  ⟨hg4.prod_right_ae, hg4.integral_prod_left, (integral_prod _ hg4).symm⟩

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
/-- **The antithetic correction is at most `(K/8)(A_M − A'_M)²`** (Giles 2015, §9.1, p. 58: the
Taylor expansion of `Y_ℓ`, with `A_M − A'_M = Δg₁ − Δg₂`): if `f′` is `K`-Lipschitz, then
`|Y_{ℓ+1}| ≤ (K/8)(A_M − A'_M)²` pointwise, `M = 2^ℓ`. -/
lemma abs_nestedDelta_le {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) (g : 𝒵 → 𝒲 → ℝ) (ℓ : ℕ)
    (p : 𝒵 × (ℕ → 𝒲)) :
    |nestedDelta f g (ℓ + 1) p| ≤ K / 8 *
      (innerMean g (2 ^ ℓ) p.1 p.2 - innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ^ 2 := by
  have e : innerMean g (2 ^ (ℓ + 1)) p.1 p.2 = (innerMean g (2 ^ ℓ) p.1 p.2 +
      innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2 := by
    rw [show (2 : ℕ) ^ (ℓ + 1) = 2 * 2 ^ ℓ from pow_succ' 2 ℓ, innerMean_two_mul]
  show |f (innerMean g (2 ^ (ℓ + 1)) p.1 p.2) - f (innerMean g (2 ^ ℓ) p.1 p.2) / 2 -
      f (innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2| ≤ _
  rw [e]
  exact abs_midpoint_sub_avg_le hf hf' _ _

/-- The antithetic correction is measurable. -/
lemma measurable_nestedDelta {f : ℝ → ℝ} (hfm : Measurable f) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g)) (ℓ : ℕ) : Measurable (nestedDelta f g ℓ) := by
  have hA : ∀ M, Measurable fun p : 𝒵 × (ℕ → 𝒲) => f (innerMean g M p.1 p.2) := fun M =>
    hfm.comp (measurable_innerMean hg M measurable_id)
  cases ℓ with
  | zero => exact hA (2 ^ 0)
  | succ ℓ =>
    have h3 : Measurable fun p : 𝒵 × (ℕ → 𝒲) =>
        f (innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) :=
      hfm.comp (measurable_innerMean hg (2 ^ ℓ) (measurable_shiftSeq (2 ^ ℓ)))
    show Measurable fun p : 𝒵 × (ℕ → 𝒲) => f (innerMean g (2 ^ (ℓ + 1)) p.1 p.2) -
      f (innerMean g (2 ^ ℓ) p.1 p.2) / 2 - f (innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2
    exact ((hA (2 ^ (ℓ + 1))).sub ((hA (2 ^ ℓ)).div_const 2)).sub (h3.div_const 2)

/-- **The variance of the nested correction is `O(M_ℓ⁻²)`** (Giles 2015, §9.1, p. 58: "It follows
that `E[Y_ℓ] = O(M_ℓ⁻¹)` and `V_ℓ = O(M_ℓ⁻²)`").  Let `f′` be `K`-Lipschitz and `g` measurable
with `E[g(Z, W)⁴] < ∞`.  Then the correction `Y_{ℓ+1}` (`M = 2^ℓ` coarse inner samples) is
square-integrable and `(2^ℓ)² E[Y_{ℓ+1}²] ≤ (K/8)² · 224 E[g(Z, W)⁴]`. -/
theorem nested_variance_rate {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) (ℓ : ℕ) :
    MemLp (nestedDelta f g (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      ((2 : ℝ) ^ ℓ) ^ 2 * ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        (K / 8) ^ 2 * (224 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) := by
  obtain ⟨hfib4, hm4, hE4⟩ := fourth_moment_fibers ν ρ hg4
  have hM : 0 < 2 ^ ℓ := by positivity
  have hMc : ((2 ^ ℓ : ℕ) : ℝ) = (2 : ℝ) ^ ℓ := by norm_num
  have hM2 : (0 : ℝ) < ((2 ^ ℓ : ℕ) : ℝ) ^ 2 := by positivity
  have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hfm : Measurable f := hfd.continuous.measurable
  have hDm : Measurable fun p : 𝒵 × (ℕ → 𝒲) =>
      innerMean g (2 ^ ℓ) p.1 p.2 - innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2) :=
    (measurable_innerMean hg (2 ^ ℓ) measurable_id).sub
      (measurable_innerMean hg (2 ^ ℓ) (measurable_shiftSeq (2 ^ ℓ)))
  -- `E[(A_M − A'_M)⁴] ≤ 224 E[g⁴] / M²`, fibre by fibre and then over the outer sample
  have hB : Integrable (fun z => 224 * (∫ v, g z v ^ 4 ∂ρ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2) ν :=
    (hm4.const_mul 224).div_const _
  obtain ⟨hD4, hD4le⟩ := integrable_of_fiber_bound ν ρ
    (F := fun p => (innerMean g (2 ^ ℓ) p.1 p.2 -
      innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ^ 4)
    (hDm.pow_const 4) (fun p => Even.pow_nonneg (by decide) _) hB
    (hfib4.mono fun z hz => by
      obtain ⟨i4, -, h4, -⟩ := fiber_nested_moments ρ g z hg.of_uncurry_left hz hM
      refine ⟨i4, ?_⟩
      show ∫ w, (innerMean g (2 ^ ℓ) z w - innerMean g (2 ^ ℓ) z (shiftSeq (2 ^ ℓ) w)) ^ 4
          ∂(innerLaw ρ) ≤ 224 * (∫ v, g z v ^ 4 ∂ρ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2
      rw [le_div_iff₀ hM2]
      linarith)
  -- `Y² ≤ (K/8)² (A_M − A'_M)⁴`
  have hsq : ∀ p : 𝒵 × (ℕ → 𝒲), nestedDelta f g (ℓ + 1) p ^ 2 ≤ (K / 8) ^ 2 *
      (innerMean g (2 ^ ℓ) p.1 p.2 - innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ^ 4 :=
    fun p => by
      have h := abs_nestedDelta_le hf hf' g ℓ p
      calc nestedDelta f g (ℓ + 1) p ^ 2 = |nestedDelta f g (ℓ + 1) p| ^ 2 := (sq_abs _).symm
        _ ≤ (K / 8 * (innerMean g (2 ^ ℓ) p.1 p.2 -
            innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = (K / 8) ^ 2 * (innerMean g (2 ^ ℓ) p.1 p.2 -
            innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ^ 4 := by ring
  have hΔm := measurable_nestedDelta hfm hg (ℓ + 1)
  have hdom : Integrable (fun p : 𝒵 × (ℕ → 𝒲) => (K / 8) ^ 2 *
      (innerMean g (2 ^ ℓ) p.1 p.2 - innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ^ 4)
      (nestedLaw ν ρ) := hD4.const_mul _
  have hΔ2 : Integrable (fun p => nestedDelta f g (ℓ + 1) p ^ 2) (nestedLaw ν ρ) :=
    hdom.mono' (hΔm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hsq p)
  refine ⟨(memLp_two_iff_integrable_sq hΔm.aestronglyMeasurable).2 hΔ2, ?_⟩
  have h1 : ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
      (K / 8) ^ 2 * ∫ p, (innerMean g (2 ^ ℓ) p.1 p.2 -
        innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ^ 4 ∂(nestedLaw ν ρ) := by
    rw [← integral_const_mul]
    exact integral_mono hΔ2 hdom hsq
  have h2 : ∫ z, 224 * (∫ v, g z v ^ 4 ∂ρ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 ∂ν =
      224 * (∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 := by
    rw [integral_div, integral_const_mul, hE4]
  rw [h2] at hD4le
  have hK2 : 0 ≤ (K / 8) ^ 2 := sq_nonneg _
  have hc : ((2 : ℝ) ^ ℓ) ^ 2 ≠ 0 := by positivity
  calc ((2 : ℝ) ^ ℓ) ^ 2 * ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)
      ≤ ((2 : ℝ) ^ ℓ) ^ 2 * ((K / 8) ^ 2 *
          (224 * (∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hD4le hK2))
          (by positivity)
    _ = (K / 8) ^ 2 * (224 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) *
          (((2 : ℝ) ^ ℓ) ^ 2 / ((2 : ℝ) ^ ℓ) ^ 2) := by
        rw [hMc]
        ring
    _ = (K / 8) ^ 2 * (224 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) := by
        rw [div_self hc, mul_one]

/-- **The mean of the nested correction is `O(M_ℓ⁻¹)`** (Giles 2015, §9.1, p. 58: "It follows that
`E[Y_ℓ] = O(M_ℓ⁻¹)`").  Under the hypotheses of `nested_variance_rate`,
`2^ℓ |E[Y_{ℓ+1}]| ≤ (K/4)(1 + 16 E[g(Z, W)⁴])`. -/
theorem nested_mean_rate {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) (ℓ : ℕ) :
    (2 : ℝ) ^ ℓ * |∫ p, nestedDelta f g (ℓ + 1) p ∂(nestedLaw ν ρ)| ≤
      K / 4 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) := by
  obtain ⟨hfib4, hm4, hE4⟩ := fourth_moment_fibers ν ρ hg4
  have hK := lipschitz_const_nonneg hf'
  have hM : 0 < 2 ^ ℓ := by positivity
  have hMc : ((2 ^ ℓ : ℕ) : ℝ) = (2 : ℝ) ^ ℓ := by norm_num
  have hMr : (0 : ℝ) < ((2 ^ ℓ : ℕ) : ℝ) := by positivity
  have hDm : Measurable fun p : 𝒵 × (ℕ → 𝒲) =>
      innerMean g (2 ^ ℓ) p.1 p.2 - innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2) :=
    (measurable_innerMean hg (2 ^ ℓ) measurable_id).sub
      (measurable_innerMean hg (2 ^ ℓ) (measurable_shiftSeq (2 ^ ℓ)))
  -- `E[(A_M − A'_M)²] ≤ 2 (1 + 16 E[g⁴]) / M`, fibre by fibre and then over the outer sample
  have hB : Integrable (fun z => 2 * (1 + 16 * ∫ v, g z v ^ 4 ∂ρ) / ((2 ^ ℓ : ℕ) : ℝ)) ν :=
    (((integrable_const (1 : ℝ)).add (hm4.const_mul 16)).const_mul 2).div_const _
  obtain ⟨hD2, hD2le⟩ := integrable_of_fiber_bound ν ρ
    (F := fun p => (innerMean g (2 ^ ℓ) p.1 p.2 -
      innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ^ 2)
    (hDm.pow_const 2) (fun p => sq_nonneg _) hB
    (hfib4.mono fun z hz => by
      obtain ⟨i4, h2, -, -⟩ := fiber_nested_moments ρ g z hg.of_uncurry_left hz hM
      have hDz : Measurable fun w : ℕ → 𝒲 =>
          innerMean g (2 ^ ℓ) z w - innerMean g (2 ^ ℓ) z (shiftSeq (2 ^ ℓ) w) :=
        hDm.comp measurable_prodMk_left
      refine ⟨integrable_pow_of_pow_four hDz i4 (by norm_num), ?_⟩
      show ∫ w, (innerMean g (2 ^ ℓ) z w - innerMean g (2 ^ ℓ) z (shiftSeq (2 ^ ℓ) w)) ^ 2
          ∂(innerLaw ρ) ≤ 2 * (1 + 16 * ∫ v, g z v ^ 4 ∂ρ) / ((2 ^ ℓ : ℕ) : ℝ)
      rw [le_div_iff₀ hMr]
      linarith)
  have h2 : ∫ z, 2 * (1 + 16 * ∫ v, g z v ^ 4 ∂ρ) / ((2 ^ ℓ : ℕ) : ℝ) ∂ν =
      2 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) / ((2 ^ ℓ : ℕ) : ℝ) := by
    rw [integral_div, integral_const_mul, integral_add (integrable_const _) (hm4.const_mul 16),
      integral_const, probReal_univ, one_smul, integral_const_mul, hE4]
  rw [h2] at hD2le
  -- `|E[Y]| ≤ E|Y| ≤ (K/8) E[(A_M − A'_M)²]`
  have h1 : |∫ p, nestedDelta f g (ℓ + 1) p ∂(nestedLaw ν ρ)| ≤
      K / 8 * ∫ p, (innerMean g (2 ^ ℓ) p.1 p.2 -
        innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ^ 2 ∂(nestedLaw ν ρ) := by
    rw [← integral_const_mul]
    exact abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
      (Eventually.of_forall fun p => abs_nonneg _) (hD2.const_mul _)
      (Eventually.of_forall fun p => abs_nestedDelta_le hf hf' g ℓ p))
  have hc : (2 : ℝ) ^ ℓ ≠ 0 := by positivity
  calc (2 : ℝ) ^ ℓ * |∫ p, nestedDelta f g (ℓ + 1) p ∂(nestedLaw ν ρ)|
      ≤ (2 : ℝ) ^ ℓ * (K / 8 *
          (2 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) / ((2 ^ ℓ : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (h1.trans (mul_le_mul_of_nonneg_left hD2le (div_nonneg hK (by norm_num))))
          (by positivity)
    _ = K / 4 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) * ((2 : ℝ) ^ ℓ / (2 : ℝ) ^ ℓ) := by
        rw [hMc]
        ring
    _ = K / 4 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) := by
        rw [div_self hc, mul_one]

/-- **The inner means have finite fourth moments** (Giles 2015, §9.1): by Jensen's inequality
`A_M⁴ ≤ M⁻¹ ∑_{m<M} g(Z, W⁽ᵐ⁾)⁴`, and each `(Z, W⁽ᵐ⁾)` has the law `ν ⊗ ρ` of `(Z, W)`, so
`E[A_M⁴] < ∞` when `E[g(Z, W)⁴] < ∞` (`M ≥ 1`). -/
lemma integrable_innerMean_pow_four {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) {M : ℕ} (hM : 0 < M) :
    Integrable (fun p : 𝒵 × (ℕ → 𝒲) => innerMean g M p.1 p.2 ^ 4) (nestedLaw ν ρ) := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hev : ∀ m, MeasurePreserving (Function.eval m) (innerLaw ρ) ρ := fun m =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => ρ) m
  have hcoord : ∀ m, MeasurePreserving (fun p : 𝒵 × (ℕ → 𝒲) => (p.1, p.2 m)) (nestedLaw ν ρ)
      (ν.prod ρ) := fun m => (MeasurePreserving.id ν).prod (hev m)
  have hgm : ∀ m, Integrable (fun p : 𝒵 × (ℕ → 𝒲) => g p.1 (p.2 m) ^ 4) (nestedLaw ν ρ) :=
    fun m => (hcoord m).integrable_comp_of_integrable hg4
  have hdom : Integrable (fun p : 𝒵 × (ℕ → 𝒲) => (M : ℝ)⁻¹ * ∑ m ∈ range M, g p.1 (p.2 m) ^ 4)
      (nestedLaw ν ρ) :=
    (integrable_finsetSum (range M) fun m _ => hgm m).const_mul _
  -- Jensen: `(M⁻¹ ∑ x_m)⁴ ≤ M⁻¹ ∑ x_m⁴`
  have hJ : ∀ x : ℕ → ℝ, ((M : ℝ)⁻¹ * ∑ m ∈ range M, x m) ^ 4 ≤
      (M : ℝ)⁻¹ * ∑ m ∈ range M, x m ^ 4 := fun x => by
    have h := (Even.convexOn_pow (𝕜 := ℝ) (n := 4) (by decide)).map_sum_le (t := range M)
      (w := fun _ => (M : ℝ)⁻¹) (p := x) (fun _ _ => inv_nonneg.2 (Nat.cast_nonneg M))
      (by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_inv_cancel₀ hM')
      (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul, ← Finset.mul_sum] at h
    exact h
  refine hdom.mono' ((measurable_innerMean hg M measurable_id).pow_const 4).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  show ‖innerMean g M p.1 p.2 ^ 4‖ ≤ (M : ℝ)⁻¹ * ∑ m ∈ range M, g p.1 (p.2 m) ^ 4
  rw [Real.norm_of_nonneg (by positivity)]
  exact hJ fun m => g p.1 (p.2 m)

/-- **The conditional mean has a finite fourth moment** (Giles 2015, §9.1: the argument
`E_W[g(Z, W)]` of `f` in the quantity of interest).  `z ↦ E_W[g(z, W)]` is measurable and, by
Jensen's inequality `(E_W[g(z, W)])⁴ ≤ E_W[g(z, W)⁴]`, its fourth power is `ν`-integrable when
`E[g(Z, W)⁴] < ∞`. -/
lemma integrable_condMean_pow_four {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) :
    Measurable (fun z => ∫ v, g z v ∂ρ) ∧ Integrable (fun z => (∫ v, g z v ∂ρ) ^ 4) ν := by
  obtain ⟨hfib4, hm4, -⟩ := fourth_moment_fibers ν ρ hg4
  have hGm : Measurable fun z => ∫ v, g z v ∂ρ :=
    (hg.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  refine ⟨hGm, hm4.mono' (hGm.pow_const 4).aestronglyMeasurable (hfib4.mono fun z hz => ?_)⟩
  have hgz : Measurable (g z) := hg.of_uncurry_left
  have h2 : Integrable (fun v => g z v ^ 2) ρ := integrable_pow_of_pow_four hgz hz (by norm_num)
  have j1 := sq_integral_le_integral_sq hgz h2
  have e4 : ∀ v, g z v ^ 4 = (g z v ^ 2) ^ 2 := fun v => by ring
  have j2 : (∫ v, g z v ^ 2 ∂ρ) ^ 2 ≤ ∫ v, g z v ^ 4 ∂ρ := by
    have h := sq_integral_le_integral_sq (hgz.pow_const 2) (hz.congr (Eventually.of_forall e4))
    simp only [← e4] at h
    exact h
  show ‖(∫ v, g z v ∂ρ) ^ 4‖ ≤ ∫ v, g z v ^ 4 ∂ρ
  rw [Real.norm_of_nonneg (by positivity)]
  calc (∫ v, g z v ∂ρ) ^ 4 = ((∫ v, g z v ∂ρ) ^ 2) ^ 2 := by ring
    _ ≤ (∫ v, g z v ^ 2 ∂ρ) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) j1 2
    _ ≤ ∫ v, g z v ^ 4 ∂ρ := j2

/-- **The level approximations are square-integrable** (Giles 2015, §9.1): `P_ℓ = f(A_{2^ℓ})` with
`f′` `K`-Lipschitz and `E[g(Z, W)⁴] < ∞`. -/
lemma memLp_nestedP {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) (ℓ : ℕ) :
    MemLp (nestedP f g ℓ) 2 (nestedLaw ν ρ) :=
  memLp_two_comp_of_pow_four hf hf' (measurable_innerMean hg (2 ^ ℓ) measurable_id)
    (integrable_innerMean_pow_four ν ρ hg hg4 (by positivity))

/-- **The quantity of interest is square-integrable** (Giles 2015, §9.1): `f(E_W[g(Z, W)])` with
`f′` `K`-Lipschitz and `E[g(Z, W)⁴] < ∞`. -/
lemma memLp_nestedTarget {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) :
    MemLp (nestedTarget f g ρ) 2 (nestedLaw ν ρ) := by
  obtain ⟨hGm, hG4⟩ := integrable_condMean_pow_four ν ρ hg hg4
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  exact (memLp_two_comp_of_pow_four hf hf' hGm hG4).comp_measurePreserving hfst

/-- **The bias of the nested approximation is `O(M_ℓ⁻¹)`** (Giles 2015, §9.1: `P_ℓ = f(A_{M_ℓ})`
approximates the quantity of interest `f(E_W[g(Z, W)])` with weak error `O(M_ℓ⁻¹)`, the rate
`α = 1` of the MLMC theorem).  Under the hypotheses of `nested_variance_rate`,
`2^ℓ |E[f(A_{2^ℓ}) − f(E_W[g(Z, W)])]| ≤ (K/2)(1 + 16 E[g(Z, W)⁴])`. -/
theorem nested_bias_rate {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) (ℓ : ℕ) :
    (2 : ℝ) ^ ℓ * |∫ p, (nestedP f g ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
      K / 2 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) := by
  obtain ⟨hfib4, hm4, hE4⟩ := fourth_moment_fibers ν ρ hg4
  have hK := lipschitz_const_nonneg hf'
  have hM : 0 < 2 ^ ℓ := by positivity
  have hMr : (0 : ℝ) < ((2 ^ ℓ : ℕ) : ℝ) := by positivity
  have hMc : ((2 ^ ℓ : ℕ) : ℝ) = (2 : ℝ) ^ ℓ := by norm_num
  have hint : Integrable (fun p => nestedP f g ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) :=
    ((memLp_nestedP ν ρ hf hf' hg hg4 ℓ).integrable one_le_two).sub
      ((memLp_nestedTarget ν ρ hf hf' hg hg4).integrable one_le_two)
  -- Fubini: integrate over the inner samples first
  have e : ∫ p, (nestedP f g ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ z, ∫ w, (f (innerMean g (2 ^ ℓ) z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ) ∂ν :=
    integral_prod _ hint
  have hB : Integrable (fun z => K / 2 * (1 + 16 * ∫ v, g z v ^ 4 ∂ρ) / ((2 ^ ℓ : ℕ) : ℝ)) ν :=
    (((integrable_const (1 : ℝ)).add (hm4.const_mul 16)).const_mul (K / 2)).div_const _
  have hfib : ∀ᵐ z ∂ν, |∫ w, (f (innerMean g (2 ^ ℓ) z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ)| ≤
      K / 2 * (1 + 16 * ∫ v, g z v ^ 4 ∂ρ) / ((2 ^ ℓ : ℕ) : ℝ) :=
    hfib4.mono fun z hz => by
      rw [le_div_iff₀' hMr]
      exact fiber_bias_le ρ hf hf' g z hg.of_uncurry_left hz hM
  have h2 : ∫ z, K / 2 * (1 + 16 * ∫ v, g z v ^ 4 ∂ρ) / ((2 ^ ℓ : ℕ) : ℝ) ∂ν =
      K / 2 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) / ((2 ^ ℓ : ℕ) : ℝ) := by
    rw [integral_div, integral_const_mul, integral_add (integrable_const _) (hm4.const_mul 16),
      integral_const, probReal_univ, one_smul, integral_const_mul, hE4]
  have h1 : |∫ z, ∫ w, (f (innerMean g (2 ^ ℓ) z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ) ∂ν| ≤
      K / 2 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) / ((2 ^ ℓ : ℕ) : ℝ) := by
    rw [← h2]
    exact abs_integral_le_integral_abs.trans
      (integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hB hfib)
  have hc : (2 : ℝ) ^ ℓ ≠ 0 := by positivity
  rw [e]
  calc (2 : ℝ) ^ ℓ * |∫ z, ∫ w, (f (innerMean g (2 ^ ℓ) z w) - f (∫ v, g z v ∂ρ))
        ∂(innerLaw ρ) ∂ν|
      ≤ (2 : ℝ) ^ ℓ * (K / 2 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) /
          ((2 ^ ℓ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K / 2 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) * ((2 : ℝ) ^ ℓ / (2 : ℝ) ^ ℓ) := by
        rw [hMc]
        ring
    _ = K / 2 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) := by
        rw [div_self hc, mul_one]

/-- **MLMC for nested simulation has complexity `O(ε⁻²)`** (Giles 2015, §9.1, p. 58: "It follows
that `E[Y_ℓ] = O(M_ℓ⁻¹)` and `V_ℓ = O(M_ℓ⁻²)`.  For the MLMC theorem, this corresponds to `α = 1`,
`β = 2`, `γ = 1`, so the complexity is `O(ε⁻²)`").  Let `f′` be `K`-Lipschitz (e.g. `|f″| ≤ K`)
and `g` measurable with `E[g(Z, W)⁴] < ∞` for independent `Z ~ ν`, `W ~ ρ`.  Let the inputs
`ω^{(ℓ,n)}` (an outer sample and its inner samples) be independent with law `ν ⊗ ρ^{⊗ℕ}`, and let
the `n`-th level-`ℓ` sample cost `cost ℓ n` with mean `C_ℓ ≤ c₃ 2^ℓ` (`M_ℓ = 2^ℓ` inner samples).
Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the
MLMC estimator `∑_{ℓ ≤ L} N_ℓ⁻¹ ∑_{n < N_ℓ} Y_ℓ(ω^{(ℓ,n)})` of `E_Z[f(E_W[g(Z, W)])]` has a
square-integrable error with mean square `< ε²`, and expected cost `≤ c₄ ε⁻²`. -/
theorem nested_mlmc_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ))
    (ω : ℕ × ℕ → Ω → 𝒵 × (ℕ → 𝒲)) (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw ν ρ))
    (hind : iIndepFun ω μ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * 2 ^ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedDelta f g) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2) μ ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedDelta f g) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * ε ^ (-2 : ℝ) := by
  have hK := lipschitz_const_nonneg hf'
  have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hfm : Measurable f := hfd.continuous.measurable
  obtain ⟨E, hE⟩ : ∃ E, E = ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact integral_nonneg fun p => by positivity
  -- the level approximations, the corrections and the quantity of interest
  have hPl : ∀ ℓ, Integrable (nestedP f g ℓ) (nestedLaw ν ρ) := fun ℓ =>
    (memLp_nestedP ν ρ hf hf' hg hg4 ℓ).integrable one_le_two
  have hP : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) :=
    (memLp_nestedTarget ν ρ hf hf' hg hg4).integrable one_le_two
  have hΔm : ∀ ℓ, Measurable (nestedDelta f g ℓ) := measurable_nestedDelta hfm hg
  have hΔ : ∀ ℓ, MemLp (nestedDelta f g ℓ) 2 (nestedLaw ν ρ) := fun ℓ => by
    cases ℓ with
    | zero => exact memLp_nestedP ν ρ hf hf' hg hg4 0
    | succ ℓ => exact (nested_variance_rate ν ρ hf hf' hg hg4 ℓ).1
  -- (i) the bias, `α = 1`
  have h_i : ∀ ℓ : ℕ, |∫ y, nestedP f g ℓ y - nestedTarget f g ρ y ∂(nestedLaw ν ρ)| ≤
      (K / 2 * (1 + 16 * E) + 1) * (2 : ℝ) ^ (-((1 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hb := nested_bias_rate ν ρ hf hf' hg hg4 ℓ
    rw [← hE] at hb
    rw [one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast 2 ℓ,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  -- (iii) the variance, `β = 2`
  have h_iii : ∀ ℓ : ℕ, variance (nestedDelta f g ℓ) (nestedLaw ν ρ) ≤
      (variance (nestedDelta f g 0) (nestedLaw ν ρ) + 4 * ((K / 8) ^ 2 * (224 * E)) + 1) *
        (2 : ℝ) ^ (-((2 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hv0 := variance_nonneg (nestedDelta f g 0) (nestedLaw ν ρ)
    have hB0 : 0 ≤ (K / 8) ^ 2 * (224 * E) := by positivity
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), mul_comm (2 : ℝ) (ℓ : ℝ),
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (ℓ : ℝ) 2, Real.rpow_natCast 2 ℓ,
      Real.rpow_two ((2 : ℝ) ^ ℓ), ← div_eq_mul_inv]
    cases ℓ with
    | zero =>
      rw [pow_zero, one_pow, div_one]
      linarith
    | succ ℓ =>
      have hv : variance (nestedDelta f g (ℓ + 1)) (nestedLaw ν ρ) ≤
          ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) := by
        simpa only [Pi.pow_apply] using
          variance_le_expectation_sq (hΔm (ℓ + 1)).aestronglyMeasurable
      have hr := (nested_variance_rate ν ρ hf hf' hg hg4 ℓ).2
      rw [← hE] at hr
      have h4 : variance (nestedDelta f g (ℓ + 1)) (nestedLaw ν ρ) * ((2 : ℝ) ^ ℓ) ^ 2 ≤
          (∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)) * ((2 : ℝ) ^ ℓ) ^ 2 :=
        mul_le_mul_of_nonneg_right hv (by positivity)
      rw [le_div_iff₀ (by positivity), pow_succ (2 : ℝ) ℓ]
      linarith
  -- (iv) the cost, `γ = 1`
  have h_iv : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, Real.rpow_natCast 2 ℓ]
    exact hC ℓ
  have hc₁ : 0 < K / 2 * (1 + 16 * E) + 1 := by positivity
  have hc₂ : 0 < variance (nestedDelta f g 0) (nestedLaw ν ρ) +
      4 * ((K / 8) ^ 2 * (224 * E)) + 1 := by
    have := variance_nonneg (nestedDelta f g 0) (nestedLaw ν ρ)
    positivity
  have hαβγ : min (2 : ℝ) 1 / 2 ≤ 1 := by
    rw [min_eq_right (by norm_num : (1 : ℝ) ≤ 2)]
    norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_corrections (nestedTarget f g ρ) (nestedP f g)
    (nestedDelta f g) ω cost C one_pos two_pos one_pos hc₁ hc₂ hc₃ hαβγ hω hind hP hPl hΔm hΔ
    hcost hcostC h_i (integral_nestedDelta ν ρ f g hPl) h_iii h_iv
  -- the quantity of interest is `E_Z[f(E_W[g(Z, W)])]`
  have hGm : Measurable fun z => ∫ v, g z v ∂ρ := (integrable_condMean_pow_four ν ρ hg hg4).1
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hPint : ∫ y, nestedTarget f g ρ y ∂(nestedLaw ν ρ) = ∫ z, f (∫ v, g z v ∂ρ) ∂ν :=
    integral_comp_of_measurePreserving hfst (hfm.comp hGm).aestronglyMeasurable
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost'⟩ := h ε hε hε1
  rw [hPint] at hmse
  rw [complexityBound_of_lt (by norm_num) ε] at hcost'
  exact ⟨L, N, hN, ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω hΔ ℓ (N ℓ)).sub
    (memLp_const _)).integrable_sq, hmse, hcost'⟩

/-- **MLMC for nested simulation from independent samples** (Giles 2015, §9.1: "an MLMC
implementation is straightforward; on level `ℓ` we can use `M_ℓ = 2^ℓ` inner samples", with
complexity `O(ε⁻²)`).  With independent copies `ω^{(ℓ,n)}` of the nested sample
`(Z, W⁽⁰⁾, W⁽¹⁾, …)` as the coordinates of the product space `(𝒵 × 𝒲^ℕ)^{ℕ×ℕ}`, and the cost
`M_ℓ = 2^ℓ` (the number of inner samples) of a level-`ℓ` sample, there is `c₄ > 0` such that for
every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the MLMC estimator has a
square-integrable error with mean square `< ε²`, and cost `≤ c₄ ε⁻²`.  Nothing is assumed about the
samples: their independence is proved. -/
theorem nested_mlmc_complexity_iid {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (nestedDelta f g) (fun p x => x p) ℓ (N ℓ) x -
            ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => nestedLaw ν ρ) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (nestedDelta f g) (fun p x => x p) ℓ (N ℓ) x -
            ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => nestedLaw ν ρ) < ε ^ 2 ∧
        ∫ x, totalCost (fun ℓ _ _ => (2 : ℝ) ^ ℓ) L N x
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => nestedLaw ν ρ) ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs (nestedLaw ν ρ)
  exact nested_mlmc_complexity ν ρ (μ := Measure.infinitePi fun _ : ℕ × ℕ => nestedLaw ν ρ)
    hf hf' hg hg4 (fun p x => x p) hω hind (fun ℓ _ _ => (2 : ℝ) ^ ℓ) (fun ℓ => (2 : ℝ) ^ ℓ)
    one_pos (fun _ _ => integrable_const _) (fun _ _ => by simp [probReal_univ]) (fun _ => by simp)

end Product

end MLMC
