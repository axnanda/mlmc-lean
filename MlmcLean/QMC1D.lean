import MlmcLean.RandomShiftQMC
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Quasi-Monte Carlo in one dimension: error `O(N⁻¹)` and MLQMC complexity (Giles 2015, §2.7, §3.5)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015).
* §1, p. 2: Monte Carlo has variance `N⁻¹V[P]`, "so the r.m.s. error is `O(N^{−1/2})`"; with
  quasi-Monte Carlo "the samples are not chosen randomly and independently, but are instead
  selected very carefully to reduce the error.  In the best cases, the error may be `O(N⁻¹)`, up to
  logarithmic terms".
* §2.7, p. 20 (MLQMC): "These theoretical developments are very encouraging, showing that under
  certain conditions they lead to multilevel methods with a complexity which is `O(ε^{−p})` with
  `p < 2`."
* §3.5, p. 26: the `N_ℓ` points are constructed "using well-established QMC techniques such as
  rank-1 lattices (Dick et al. 2007) or Sobol sequences … In the best cases, this results in the
  approximate numerical integration error being `O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})`
  error which comes from Monte Carlo sampling.  …  To regain a confidence interval one uses
  randomised QMC in which the set of points is gives [sic] a random shift (for rank-1 lattice
  rules) …"; p. 27: "from these 32 random independent values the variance of their average, `V_ℓ`,
  can be estimated in the usual way."

This file proves the rigorous best case of these claims **in one dimension only**: integrands of
bounded variation on `[0, 1]`, one point in each of the cells `[i/N, (i + 1)/N]`, and the
(randomly shifted) rank-1 lattice `{i/N}`.  QMC error theory in `d` dimensions (the
Koksma–Hlawka inequality, discrepancy of low-discrepancy sequences, Sobol points and digital
scrambling, the weighted function spaces behind the MLQMC results the paper cites) is not
formalised.  The total variation of `f` on `[0, 1]` is Mathlib's `eVariationOn f (Set.Icc 0 1)`,
finite by the hypothesis `BoundedVariationOn f (Set.Icc 0 1)`; a shift `U` "uniform on `[0, 1]`" is
a map that is measure preserving from the probability space to Lebesgue measure on `[0, 1]`.  The
shift modulo `1` of `RandomShiftQMC.lean` (`shiftedQMC` on the torus `UnitAddTorus d`) is modelled
on `ℝ` with `Int.fract`; `rank1Lattice_torus_replicates` is the bridge to `shiftedQMC` and
`randomShift_replicates` for `d = 1`.

* `qmc_error_le_of_monotoneOn`: for `f` monotone on `[0, 1]` and `x_i ∈ [i/N, (i + 1)/N]`,
  `|N⁻¹ ∑_{i<N} f(x_i) − ∫_0^1 f| ≤ (f(1) − f(0))/N`.
* `qmc_error_le_of_boundedVariationOn`: the same with bound `V(f)/N` for `f` of bounded variation.
* `latticeRule` (`N⁻¹ ∑_{i<N} f((i + u)/N)`): error `≤ max(u, 1 − u) V(f)/N` for every shift
  `u ∈ [0, 1]` (`latticeRule_error_le`, `latticeRule_error_le_variation_div`), `≤ V(f)/(2N)` for
  the centred lattice (`latticeRule_half_error_le`).  `shiftedLatticeRule`
  (`N⁻¹ ∑_{i<N} f(frac(i/N + Δ))`, the shift modulo `1`) is a `latticeRule`
  (`shiftedLatticeRule_eq_latticeRule`), with error `≤ V(f)/N` for every `Δ ∈ ℝ`
  (`shiftedLatticeRule_error_le`).
* `latticeRule_randomShift`, `shiftedLatticeRule_randomShift`: with a uniform random shift the rule
  is unbiased, with error `≤ V(f)/N` almost surely and mean square error and variance
  `≤ V(f)²/N²`; `latticeRule_replicates`: `R` independent shifts give an unbiased average of
  variance `≤ V(f)²/(RN²)` and an unbiased variance estimate; `latticeRule_vs_monteCarlo`: plain
  Monte Carlo with `N` samples has variance `Var[f(U)]/N`, so the ratio of the two mean square
  errors is `≤ V(f)²/(N Var[f(U)])`; `variance_latticeRule_id_vs_mc`: exactly `1/(12N)` against
  `1/(12N²)` for `f(x) = x`.
* `rank1Lattice_torus_replicates`: on the circle `𝕋¹ = ℝ/ℤ`, with the rank-1 lattice `i/N` and the
  integrand `F(y) = f(y mod 1)`, `shiftedQMC F x N` is `shiftedLatticeRule f N`,
  `∫_{𝕋¹} F = ∫_0^1 f`, and the variance `V₁` of one set average in `randomShift_replicates` is
  `≤ V(f)²/N²`.
* `mlqmc_complexity_core`, `mlqmc_complexity`: MLQMC with one randomly shifted lattice per level,
  level corrections of total variation `O(2^{−bℓ})`, cost `O(2^{gℓ})` per point and bias
  `O(2^{−aL})` has mean square error `< ε²` at cost `O(ε^{−max(1, g/a)})` when `b > g`, or `a ≤ b`
  and `a < g`; `mlqmc_complexity_core_of_lt`, `mlqmc_complexity_of_lt`: cost
  `O(ε^{−max(1 + (g − b)/a, g/a)})` when `b < g`; `mlqmc_complexity_lt_two`: the paper's
  `O(ε^{−p})` with `p < 2` whenever `g < 2a` and `g < a + b`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### One cell -/

/-- **The error of one point on one cell.**  If `|f y − f x| ≤ g y − g x` for `a ≤ x ≤ y ≤ b`
(`g` dominates the increments of `f` on `[a, b]`) and `f` is integrable on `[a, b]`, then for every
`p ∈ [a, b]`, `|(b − a) f(p) − ∫_a^b f| ≤ (p − a)(g p − g a) + (b − p)(g b − g p)`. -/
lemma abs_cell_error_le {f g : ℝ → ℝ} {a p b : ℝ} (hap : a ≤ p) (hpb : p ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hdom : ∀ x y, a ≤ x → x ≤ y → y ≤ b → |f y - f x| ≤ g y - g x) :
    |(b - a) * f p - ∫ x in a..b, f x| ≤ (p - a) * (g p - g a) + (b - p) * (g b - g p) := by
  have hab : a ≤ b := hap.trans hpb
  have h1 : IntervalIntegrable f volume a p := hf.mono_set (by
    rw [Set.uIcc_of_le hap, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc_right hpb)
  have h2 : IntervalIntegrable f volume p b := hf.mono_set (by
    rw [Set.uIcc_of_le hpb, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc_left hap)
  have e1 : (p - a) * f p - ∫ x in a..p, f x = ∫ x in a..p, (f p - f x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const h1,
      intervalIntegral.integral_const, smul_eq_mul]
  have e2 : (b - p) * f p - ∫ x in p..b, f x = ∫ x in p..b, (f p - f x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const h2,
      intervalIntegral.integral_const, smul_eq_mul]
  have b1 : |∫ x in a..p, (f p - f x)| ≤ (g p - g a) * |p - a| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := p)
      (C := g p - g a) (f := fun x => f p - f x) (fun x hx => by
        rw [Set.uIoc_of_le hap] at hx
        have hx1 := hdom x p hx.1.le hx.2 hpb
        have hx2 := hdom a x le_rfl hx.1.le (hx.2.trans hpb)
        rw [Real.norm_eq_abs]
        linarith [abs_nonneg (f x - f a)])
    simpa only [Real.norm_eq_abs] using h
  have b2 : |∫ x in p..b, (f p - f x)| ≤ (g b - g p) * |b - p| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := b)
      (C := g b - g p) (f := fun x => f p - f x) (fun x hx => by
        rw [Set.uIoc_of_le hpb] at hx
        have hx1 := hdom p x hap hx.1.le hx.2
        have hx2 := hdom x b (hap.trans hx.1.le) hx.2 le_rfl
        rw [Real.norm_eq_abs, abs_sub_comm]
        linarith [abs_nonneg (f b - f x)])
    simpa only [Real.norm_eq_abs] using h
  rw [abs_of_nonneg (sub_nonneg.2 hap)] at b1
  rw [abs_of_nonneg (sub_nonneg.2 hpb)] at b2
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    show (b - a) * f p - ((∫ x in a..p, f x) + ∫ x in p..b, f x) =
      ((p - a) * f p - ∫ x in a..p, f x) + ((b - p) * f p - ∫ x in p..b, f x) by ring, e1, e2]
  calc _ ≤ |∫ x in a..p, (f p - f x)| + |∫ x in p..b, (f p - f x)| := abs_add_le _ _
    _ ≤ (g p - g a) * (p - a) + (g b - g p) * (b - p) := add_le_add b1 b2
    _ = _ := by ring

/-! ### `N` cells -/

/-- **One point per cell, general form.**  Let `N ≥ 1`, let `x_i ∈ [i/N, (i + 1)/N]` for `i < N`,
with `x_i − i/N ≤ θ/N` and `(i + 1)/N − x_i ≤ θ/N`, let `f` be integrable on `[0, 1]` and let `g`
dominate the increments of `f` on `[0, 1]` (`|f y − f x| ≤ g y − g x` for `0 ≤ x ≤ y ≤ 1`).  Then
`|N⁻¹ ∑_{i<N} f(x_i) − ∫_0^1 f| ≤ θ (g 1 − g 0)/N`: on each cell `abs_cell_error_le`, and the sum of
the increments of `g` over the cells telescopes. -/
lemma abs_qmc_sub_integral_le {f g : ℝ → ℝ} {N : ℕ} (hN : 0 < N) {x : ℕ → ℝ} {θ : ℝ}
    (hx : ∀ i < N, (i : ℝ) / N ≤ x i ∧ x i ≤ (i + 1) / N)
    (hθ : ∀ i < N, x i - i / N ≤ θ / N ∧ (i + 1) / N - x i ≤ θ / N)
    (hf : IntervalIntegrable f volume 0 1)
    (hdom : ∀ x y, 0 ≤ x → x ≤ y → y ≤ 1 → |f y - f x| ≤ g y - g x) :
    |(N : ℝ)⁻¹ * ∑ i ∈ range N, f (x i) - ∫ y in (0 : ℝ)..1, f y| ≤ θ * (g 1 - g 0) / N := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have ha0 : ((0 : ℕ) : ℝ) / N = 0 := by simp
  have haN : ((N : ℕ) : ℝ) / N = 1 := div_self hN'.ne'
  have hamem : ∀ k ≤ N, 0 ≤ (k : ℝ) / N ∧ (k : ℝ) / N ≤ 1 := fun k hk =>
    ⟨by positivity, by rw [div_le_one hN']; exact_mod_cast hk⟩
  have hsucc : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / N = ((k : ℝ) + 1) / N := fun k => by push_cast; rfl
  have hle : ∀ k : ℕ, (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N := fun k => by
    rw [hsucc]
    gcongr
    linarith
  have hint : ∀ k < N, IntervalIntegrable f volume ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) :=
    fun k hk => hf.mono_set (by
      rw [Set.uIcc_of_le (hle k), Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc (hamem k hk.le).1 (hamem (k + 1) hk).2)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) / N)
    (μ := volume) (f := f) hint
  simp only [ha0, haN] at hsum
  rw [← hsum, mul_sum, ← sum_sub_distrib]
  have hcell : ∀ i ∈ range N, |(N : ℝ)⁻¹ * f (x i) - ∫ y in (i : ℝ) / N..((i + 1 : ℕ) : ℝ) / N,
      f y| ≤ θ / N * (g (((i + 1 : ℕ) : ℝ) / N) - g ((i : ℝ) / N)) := by
    intro i hi
    rw [mem_range] at hi
    have hxi := hx i hi
    have hθi := hθ i hi
    have hdi : ((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N = (N : ℝ)⁻¹ := by
      rw [hsucc]
      field_simp
      ring
    have hdom' : ∀ y z, (i : ℝ) / N ≤ y → y ≤ z → z ≤ ((i + 1 : ℕ) : ℝ) / N →
        |f z - f y| ≤ g z - g y := fun y z hy hyz hz =>
      hdom y z ((hamem i hi.le).1.trans hy) hyz (hz.trans (hamem (i + 1) hi).2)
    have hxi2 : x i ≤ ((i + 1 : ℕ) : ℝ) / N := by rw [hsucc]; exact hxi.2
    have hc := abs_cell_error_le hxi.1 hxi2 (hint i hi) hdom'
    rw [hdi] at hc
    have hg1 : 0 ≤ g (x i) - g ((i : ℝ) / N) :=
      (abs_nonneg _).trans (hdom' _ _ le_rfl hxi.1 hxi2)
    have hg2 : 0 ≤ g (((i + 1 : ℕ) : ℝ) / N) - g (x i) :=
      (abs_nonneg _).trans (hdom' _ _ hxi.1 hxi2 le_rfl)
    have hw1 : x i - (i : ℝ) / N ≤ θ / N := hθi.1
    have hw2 : ((i + 1 : ℕ) : ℝ) / N - x i ≤ θ / N := by rw [hsucc]; exact hθi.2
    calc _ ≤ _ := hc
      _ ≤ θ / N * (g (x i) - g ((i : ℝ) / N)) +
          θ / N * (g (((i + 1 : ℕ) : ℝ) / N) - g (x i)) := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ i ∈ range N, |(N : ℝ)⁻¹ * f (x i) -
        ∫ y in (i : ℝ) / N..((i + 1 : ℕ) : ℝ) / N, f y| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range N, θ / N * (g (((i + 1 : ℕ) : ℝ) / N) - g ((i : ℝ) / N)) := sum_le_sum hcell
    _ = θ / N * (g (((N : ℕ) : ℝ) / N) - g (((0 : ℕ) : ℝ) / N)) := by
        rw [← mul_sum, sum_range_sub (fun k : ℕ => g ((k : ℝ) / N))]
    _ = _ := by
        rw [ha0, haN]
        ring

/-- `x_i ∈ [i/N, (i + 1)/N]` forces `x_i − i/N ≤ 1/N` and `(i + 1)/N − x_i ≤ 1/N`. -/
lemma cell_width_le {N : ℕ} {x : ℕ → ℝ} (hx : ∀ i < N, (i : ℝ) / N ≤ x i ∧ x i ≤ (i + 1) / N) :
    ∀ i < N, x i - i / N ≤ 1 / N ∧ (i + 1) / N - x i ≤ 1 / N := fun i hi => by
  have h := hx i hi
  have e : ((i : ℝ) + 1) / N = i / N + 1 / N := add_div _ _ _
  constructor <;> linarith

/-- **QMC with one point per cell for a monotone integrand: error `≤ (f(1) − f(0))/N`** (Giles 2015,
§3.5, p. 26: "In the best cases, this results in the approximate numerical integration error being
`O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})` error which comes from Monte Carlo sampling"; §1,
p. 2: "In the best cases, the error may be `O(N⁻¹)`").  One dimension only: QMC error theory in `d`
dimensions (Koksma–Hlawka, low-discrepancy and Sobol points) is not formalised.  Let `f` be
monotone on `[0, 1]`, `N ≥ 1`, and let `x_i ∈ [i/N, (i + 1)/N]` for `i < N` (one point in each of
the `N` cells).  Then `|N⁻¹ ∑_{i<N} f(x_i) − ∫_0^1 f| ≤ (f(1) − f(0))/N`: on the cell of `x_i`,
`|f(x_i) − f(x)| ≤ f((i + 1)/N) − f(i/N)`, and these increments telescope.  The constant cannot
be improved: for the step function `f = 1_{[c, 1]}`, `0 < c < 1/N`, and `x_i = i/N` the error is
`1/N − c`. -/
theorem qmc_error_le_of_monotoneOn {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc 0 1)) {N : ℕ}
    (hN : 0 < N) {x : ℕ → ℝ} (hx : ∀ i < N, (i : ℝ) / N ≤ x i ∧ x i ≤ (i + 1) / N) :
    |(N : ℝ)⁻¹ * ∑ i ∈ range N, f (x i) - ∫ y in (0 : ℝ)..1, f y| ≤ (f 1 - f 0) / N := by
  have hint : IntervalIntegrable f volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le zero_le_one])
  have h := abs_qmc_sub_integral_le (g := f) hN hx (cell_width_le hx) hint
    fun x y hx hxy hy => by
      rw [abs_of_nonneg (sub_nonneg.2 (hf ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy))]
  rwa [one_mul] at h

/-! ### Bounded variation -/

/-- A function of bounded variation on `[a, b]` is integrable on `[a, b]` (it is a difference of
two monotone functions there). -/
lemma intervalIntegrable_of_boundedVariationOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Set.Icc a b)) : IntervalIntegrable f volume a b := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  rw [← Set.uIcc_of_le hab] at hp hq
  exact hp.intervalIntegrable.sub hq.intervalIntegrable

/-- **One point per cell for an integrand of bounded variation, general form.**  With `V` the total
variation of `f` on `[0, 1]` and `x_i` as in `abs_qmc_sub_integral_le` (within `θ/N` of both ends of
its cell), `|N⁻¹ ∑_{i<N} f(x_i) − ∫_0^1 f| ≤ θ V/N`.  The variation function
`x ↦ V_{[0, x]}(f)` dominates the increments of `f`. -/
lemma abs_qmc_sub_integral_le_of_bv {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {N : ℕ} (hN : 0 < N) {x : ℕ → ℝ} {θ : ℝ}
    (hx : ∀ i < N, (i : ℝ) / N ≤ x i ∧ x i ≤ (i + 1) / N)
    (hθ : ∀ i < N, x i - i / N ≤ θ / N ∧ (i + 1) / N - x i ≤ θ / N) :
    |(N : ℝ)⁻¹ * ∑ i ∈ range N, f (x i) - ∫ y in (0 : ℝ)..1, f y| ≤
      θ * (eVariationOn f (Set.Icc 0 1)).toReal / N := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h := abs_qmc_sub_integral_le (g := variationOnFromTo f (Set.Icc 0 1) 0) hN hx hθ
    (intervalIntegrable_of_boundedVariationOn zero_le_one hf)
    fun x y hx hxy hy => variationOnFromTo.abs_sub_le_sub_of_le hf.locallyBoundedVariationOn h0
      ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy
  rwa [variationOnFromTo.self, variationOnFromTo.eq_of_le _ _ zero_le_one, Set.inter_self,
    sub_zero] at h

/-- **QMC with one point per cell for an integrand of bounded variation: error `≤ V(f)/N`** (Giles
2015, §3.5, p. 26: "In the best cases, this results in the approximate numerical integration error
being `O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})` error which comes from Monte Carlo
sampling").  One dimension only: QMC error theory in `d` dimensions (Koksma–Hlawka, low-discrepancy
and Sobol points) is not formalised.  Let `f` have bounded variation on `[0, 1]`, with total
variation `V = V_{[0,1]}(f)` (Mathlib's `eVariationOn`, finite by hypothesis), let `N ≥ 1` and
`x_i ∈ [i/N, (i + 1)/N]` for `i < N`.  Then `|N⁻¹ ∑_{i<N} f(x_i) − ∫_0^1 f| ≤ V/N`.  (In `d`
dimensions the analogue is the Koksma–Hlawka inequality, with the star discrepancy of the points
and the Hardy–Krause variation.) -/
theorem qmc_error_le_of_boundedVariationOn {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {N : ℕ} (hN : 0 < N) {x : ℕ → ℝ} (hx : ∀ i < N, (i : ℝ) / N ≤ x i ∧ x i ≤ (i + 1) / N) :
    |(N : ℝ)⁻¹ * ∑ i ∈ range N, f (x i) - ∫ y in (0 : ℝ)..1, f y| ≤
      (eVariationOn f (Set.Icc 0 1)).toReal / N := by
  have h := abs_qmc_sub_integral_le_of_bv hf hN hx (cell_width_le hx)
  rwa [one_mul] at h

/-! ### The shifted rank-1 lattice rule -/

/-- **The shifted rank-1 lattice rule in one dimension** (Giles 2015, §3.5, p. 26: "rank-1 lattices
(Dick et al. 2007)", randomised by "a random shift"): `N⁻¹ ∑_{i<N} f((i + u)/N)`, the average of `f`
over the `N` points `(i + u)/N`, i.e. the lattice `{0, 1/N, …, (N − 1)/N}` shifted by `u/N`.  For
`u ∈ [0, 1)` every point lies in `[0, 1)`, one in each cell `[i/N, (i + 1)/N)`. -/
noncomputable def latticeRule (f : ℝ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ range N, f ((i + u) / N)

/-- The points `(i + u)/N`, `u ∈ [0, 1]`, are within `max(u, 1 − u)/N` of both ends of their
cells. -/
lemma latticeRule_points {N : ℕ} {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i < N, (i : ℝ) / N ≤ (i + u) / N ∧ (i + u) / N ≤ (i + 1) / N) ∧
      ∀ i < N, (i + u) / N - i / N ≤ max u (1 - u) / N ∧
        (i + 1) / N - (i + u) / N ≤ max u (1 - u) / N := by
  refine ⟨fun i _ => ⟨?_, ?_⟩, fun i _ => ⟨?_, ?_⟩⟩
  · gcongr
    linarith [hu.1]
  · gcongr
    exact hu.2
  · rw [← sub_div]
    gcongr
    linarith [le_max_left u (1 - u)]
  · rw [← sub_div]
    gcongr
    linarith [le_max_right u (1 - u)]

/-- **Every shift of the rank-1 lattice: error `≤ max(u, 1 − u) V(f)/N`** (Giles 2015, §3.5, p. 26:
QMC "In the best cases … `O(N_ℓ⁻¹)`").  One dimension only: QMC error theory in `d` dimensions
(Koksma–Hlawka, low-discrepancy and Sobol points) is not formalised.  For `f` of bounded variation
on `[0, 1]` with total variation `V`, `N ≥ 1` and every shift `u ∈ [0, 1]`, the shifted lattice
rule `N⁻¹ ∑_{i<N} f((i + u)/N)` has `|N⁻¹ ∑_{i<N} f((i + u)/N) − ∫_0^1 f| ≤ max(u, 1 − u) V/N`;
in particular `≤ V/N` for every shift (`latticeRule_error_le_variation_div`), and `≤ V/(2N)` for
the centred lattice `u = 1/2` (`latticeRule_half_error_le`). -/
theorem latticeRule_error_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1)) {N : ℕ}
    (hN : 0 < N) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |latticeRule f N u - ∫ y in (0 : ℝ)..1, f y| ≤
      max u (1 - u) * (eVariationOn f (Set.Icc 0 1)).toReal / N :=
  abs_qmc_sub_integral_le_of_bv hf hN (latticeRule_points hu).1 (latticeRule_points hu).2

/-- **The error bound `V(f)/N` holds for every shift of the rank-1 lattice** (Giles 2015, §3.5,
p. 26: "In the best cases, this results in the approximate numerical integration error being
`O(N_ℓ⁻¹)`").  One dimension only: QMC error theory in `d` dimensions (Koksma–Hlawka,
low-discrepancy and Sobol points) is not formalised.  For `f` of bounded variation on `[0, 1]`
with total variation `V`, `N ≥ 1` and every `u ∈ [0, 1]`,
`|N⁻¹ ∑_{i<N} f((i + u)/N) − ∫_0^1 f| ≤ V/N` (`latticeRule_error_le` and `max(u, 1 − u) ≤ 1`). -/
theorem latticeRule_error_le_variation_div {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {N : ℕ} (hN : 0 < N) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |latticeRule f N u - ∫ y in (0 : ℝ)..1, f y| ≤ (eVariationOn f (Set.Icc 0 1)).toReal / N := by
  refine (latticeRule_error_le hf hN hu).trans ?_
  have hm : max u (1 - u) ≤ 1 := max_le hu.2 (by linarith [hu.1])
  gcongr
  calc max u (1 - u) * (eVariationOn f (Set.Icc 0 1)).toReal
      ≤ 1 * (eVariationOn f (Set.Icc 0 1)).toReal := by gcongr
    _ = _ := one_mul _

/-- **The centred lattice (midpoint rule): error `≤ V(f)/(2N)`** (Giles 2015, §3.5, p. 26: "In the
best cases … `O(N_ℓ⁻¹)`").  One dimension only: QMC error theory in `d` dimensions (Koksma–Hlawka,
low-discrepancy and Sobol points) is not formalised.  For `f` of bounded variation on `[0, 1]` with
total variation `V` and `N ≥ 1`, the centred lattice `x_i = (i + 1/2)/N` has
`|N⁻¹ ∑_{i<N} f((i + 1/2)/N) − ∫_0^1 f| ≤ V/(2N)`, half the bound `V/N` for an arbitrary point in
each cell (`qmc_error_le_of_boundedVariationOn`, whose constant cannot be improved). -/
theorem latticeRule_half_error_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1)) {N : ℕ}
    (hN : 0 < N) :
    |latticeRule f N (1 / 2) - ∫ y in (0 : ℝ)..1, f y| ≤
      (eVariationOn f (Set.Icc 0 1)).toReal / (2 * N) := by
  have h := latticeRule_error_le hf hN (u := 1 / 2) ⟨by norm_num, by norm_num⟩
  rw [show max (1 / 2 : ℝ) (1 - 1 / 2) = 1 / 2 by norm_num] at h
  calc _ ≤ _ := h
    _ = _ := by
        have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
        field_simp

/-- **The rank-1 lattice shifted modulo `1`** (Giles 2015, §3.5, p. 26: "rank-1 lattices (Dick et
al. 2007)", randomised by "a random shift"): `N⁻¹ ∑_{i<N} f(frac(i/N + Δ))`, the average of `f`
over the lattice `{i/N : i < N}` shifted by `Δ ∈ ℝ` modulo `1`.  This is the convention of
`shiftedQMC` on the torus, modelled here on `ℝ` with `Int.fract`; `rank1Lattice_torus_replicates`
proves that `shiftedQMC` on `𝕋¹` with the points `i/N` is this rule. -/
noncomputable def shiftedLatticeRule (f : ℝ → ℝ) (N : ℕ) (Δ : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ range N, f (Int.fract ((i : ℝ) / N + Δ))

/-- **The usual shift of a rank-1 lattice is a shift of the points `(i + u)/N`.**  For every
`Δ ∈ ℝ` the points `i/N + Δ mod 1`, `i < N` (the lattice `{i/N}` shifted by `Δ` on the circle
`ℝ/ℤ`), are, up to order, the points `(j + u)/N`, `j < N`, with `u = frac(NΔ) ∈ [0, 1)`: both sides
are `1/N`-periodic in `Δ` and agree for `0 ≤ Δ < 1/N`. -/
lemma sum_fract_add_eq (F : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (Δ : ℝ) :
    ∑ i ∈ range N, F (Int.fract ((i : ℝ) / N + Δ)) =
      ∑ j ∈ range N, F ((j + Int.fract (N * Δ)) / N) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hS : Function.Periodic (fun Δ : ℝ => ∑ i ∈ range N, F (Int.fract ((i : ℝ) / N + Δ)))
      (1 / N) := fun Δ => by
    have h : ∀ i : ℕ, (i : ℝ) / N + (Δ + 1 / N) = ((i + 1 : ℕ) : ℝ) / N + Δ := fun i => by
      push_cast
      ring
    simp only [h]
    have e1 := sum_range_succ' (fun k : ℕ => F (Int.fract ((k : ℝ) / N + Δ))) N
    have e2 := sum_range_succ (fun k : ℕ => F (Int.fract ((k : ℝ) / N + Δ))) N
    have hN0 : F (Int.fract (((N : ℕ) : ℝ) / N + Δ)) =
        F (Int.fract (((0 : ℕ) : ℝ) / N + Δ)) := by
      rw [div_self hN', Nat.cast_zero, zero_div, zero_add, add_comm, Int.fract_add_one]
    linarith
  have hT : Function.Periodic (fun Δ : ℝ => ∑ j ∈ range N, F ((j + Int.fract (N * Δ)) / N))
      (1 / N) := fun Δ => by
    simp only [mul_add, mul_one_div_cancel hN', Int.fract_add_one]
  have hbase : ∀ δ : ℝ, 0 ≤ δ → δ < 1 / N → ∑ i ∈ range N, F (Int.fract ((i : ℝ) / N + δ)) =
      ∑ j ∈ range N, F ((j + Int.fract (N * δ)) / N) := by
    intro δ h0 h1
    have hNδ : Int.fract ((N : ℝ) * δ) = N * δ := Int.fract_eq_self.2
      ⟨by positivity, by rwa [lt_div_iff₀ hNpos, mul_comm] at h1⟩
    refine sum_congr rfl fun i hi => ?_
    have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast mem_range.1 hi
    have hlt : (i : ℝ) / N + δ < 1 := by
      calc (i : ℝ) / N + δ < i / N + 1 / N := by linarith
        _ = (i + 1) / N := by ring
        _ ≤ 1 := by rw [div_le_one hNpos]; exact hi'
    rw [hNδ, Int.fract_eq_self.2 ⟨by positivity, hlt⟩]
    congr 1
    field_simp
  have hdec : Δ = Int.fract (N * Δ) / N + (⌊(N : ℝ) * Δ⌋ : ℝ) * (1 / N) := by
    calc Δ = ((N : ℝ) * Δ) / N := by field_simp
      _ = (Int.fract ((N : ℝ) * Δ) + ⌊(N : ℝ) * Δ⌋) / N := by rw [Int.fract_add_floor]
      _ = _ := by ring
  have h0 : 0 ≤ Int.fract ((N : ℝ) * Δ) / N := div_nonneg (Int.fract_nonneg _) hNpos.le
  have h1 : Int.fract ((N : ℝ) * Δ) / N < 1 / N :=
    div_lt_div_of_pos_right (Int.fract_lt_one _) hNpos
  calc ∑ i ∈ range N, F (Int.fract ((i : ℝ) / N + Δ))
      = ∑ i ∈ range N, F (Int.fract ((i : ℝ) / N +
          (Int.fract (N * Δ) / N + (⌊(N : ℝ) * Δ⌋ : ℝ) * (1 / N)))) := by rw [← hdec]
    _ = ∑ i ∈ range N, F (Int.fract ((i : ℝ) / N + Int.fract (N * Δ) / N)) :=
        hS.int_mul _ _
    _ = ∑ j ∈ range N, F ((j + Int.fract (N * (Int.fract (N * Δ) / N))) / N) := hbase _ h0 h1
    _ = ∑ j ∈ range N, F ((j + Int.fract (N * (Int.fract (N * Δ) / N +
          (⌊(N : ℝ) * Δ⌋ : ℝ) * (1 / N)))) / N) := (hT.int_mul _ _).symm
    _ = ∑ j ∈ range N, F ((j + Int.fract (N * Δ)) / N) := by rw [← hdec]

/-- The lattice shifted by `Δ` modulo `1` is the lattice `(j + u)/N` with `u = frac(NΔ)`
(`sum_fract_add_eq`). -/
lemma shiftedLatticeRule_eq_latticeRule (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (Δ : ℝ) :
    shiftedLatticeRule f N Δ = latticeRule f N (Int.fract (N * Δ)) := by
  unfold shiftedLatticeRule latticeRule
  rw [sum_fract_add_eq f hN Δ]

/-- **Every shift of the rank-1 lattice modulo `1`: error `≤ V(f)/N`** (Giles 2015, §3.5, p. 26:
QMC with "rank-1 lattices (Dick et al. 2007)", randomised by "a random shift", has "In the best
cases … error … `O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})`").  One dimension only: QMC error
theory in `d` dimensions (Koksma–Hlawka, low-discrepancy and Sobol points) is not formalised.  The
rank-1 lattice rule with `N` points in one dimension uses the points `i/N`, `i < N`, and its shift
by `Δ ∈ ℝ` the points `frac(i/N + Δ)` (addition modulo `1`, as for `shiftedQMC` on the torus).
For `f` of bounded variation on `[0, 1]` with total variation `V`, `N ≥ 1` and every `Δ ∈ ℝ`,
`|N⁻¹ ∑_{i<N} f(frac(i/N + Δ)) − ∫_0^1 f| ≤ V/N` (`shiftedLatticeRule_eq_latticeRule`,
`latticeRule_error_le_variation_div`). -/
theorem shiftedLatticeRule_error_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1)) {N : ℕ}
    (hN : 0 < N) (Δ : ℝ) :
    |shiftedLatticeRule f N Δ - ∫ y in (0 : ℝ)..1, f y| ≤
      (eVariationOn f (Set.Icc 0 1)).toReal / N := by
  rw [shiftedLatticeRule_eq_latticeRule f hN Δ]
  exact latticeRule_error_le_variation_div hf hN ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

/-! ### The random shift -/

/-- A function of bounded variation on `[0, 1]` agrees on `[0, 1]` with a difference of two
monotone functions on `ℝ` (the monotone parts of its Jordan decomposition, extended constantly
outside `[0, 1]`). -/
lemma exists_monotone_sub_eqOn {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    ∃ P Q : ℝ → ℝ, Monotone P ∧ Monotone Q ∧ Set.EqOn f (fun x => P x - Q x) (Set.Icc 0 1) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hcmem : ∀ x : ℝ, max 0 (min x 1) ∈ Set.Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hcmono : Monotone fun x : ℝ => max 0 (min x 1) := fun x y hxy =>
    max_le_max le_rfl (min_le_min hxy le_rfl)
  refine ⟨fun x => p (max 0 (min x 1)), fun x => q (max 0 (min x 1)),
    fun x y hxy => hp (hcmem x) (hcmem y) (hcmono hxy),
    fun x y hxy => hq (hcmem x) (hcmem y) (hcmono hxy), fun x hx => ?_⟩
  simp only [min_eq_left hx.2, max_eq_right hx.1, hpq, Pi.sub_apply]

/-- A function of bounded variation on `[0, 1]` agrees on `[0, 1]` with a bounded measurable
function on `ℝ` (the difference of the monotone parts of `exists_monotone_sub_eqOn`, evaluated at
the point of `[0, 1]` nearest to `x`). -/
lemma exists_measurable_bounded_eqOn {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    ∃ H : ℝ → ℝ, Measurable H ∧ (∃ B : ℝ, ∀ x, |H x| ≤ B) ∧ Set.EqOn f H (Set.Icc 0 1) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := exists_monotone_sub_eqOn hf
  have hc : Continuous fun x : ℝ => max 0 (min x 1) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hcmem : ∀ x : ℝ, max 0 (min x 1) ∈ Set.Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  refine ⟨fun x => P (max 0 (min x 1)) - Q (max 0 (min x 1)),
    (hP.measurable.comp hc.measurable).sub (hQ.measurable.comp hc.measurable),
    ⟨|P 0| + |P 1| + (|Q 0| + |Q 1|), fun x => ?_⟩, fun x hx => ?_⟩
  · have hp0 := hP (hcmem x).1
    have hp1 := hP (hcmem x).2
    have hq0 := hQ (hcmem x).1
    have hq1 := hQ (hcmem x).2
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (P 0), le_abs_self (P 1), neg_abs_le (Q 0),
      le_abs_self (Q 1), abs_nonneg (P 0), abs_nonneg (P 1), abs_nonneg (Q 0), abs_nonneg (Q 1)]
  · simp only [min_eq_left hx.2, max_eq_right hx.1]
    exact hPQ hx

/-- The lattice rule only sees `f` on `[0, 1]` when the shift is in `[0, 1]`. -/
lemma latticeRule_congr {f F : ℝ → ℝ} (h : Set.EqOn f F (Set.Icc 0 1)) (N : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : latticeRule f N u = latticeRule F N u := by
  unfold latticeRule
  congr 1
  refine sum_congr rfl fun i hi => h ⟨div_nonneg (by linarith [hu.1, (i.cast_nonneg : (0 : ℝ) ≤ i)])
    N.cast_nonneg, div_le_one_of_le₀ ?_ N.cast_nonneg⟩
  have : (i : ℝ) + 1 ≤ N := by exact_mod_cast mem_range.1 hi
  linarith [hu.2]

/-- The lattice rule of a difference of monotone functions is measurable in the shift. -/
lemma measurable_latticeRule {P Q : ℝ → ℝ} (hP : Monotone P) (hQ : Monotone Q) (N : ℕ) :
    Measurable (latticeRule (fun x => P x - Q x) N) := by
  have ha : ∀ i : ℕ, Measurable fun u : ℝ => ((i : ℝ) + u) / N := fun i =>
    (measurable_const_add _).div_const _
  exact (Finset.measurable_sum _ fun i _ =>
    (hP.measurable.comp (ha i)).sub (hQ.measurable.comp (ha i))).const_mul _

/-- **The randomly shifted lattice rule is unbiased (exact integral over the shift).**  For a
difference `F = P − Q` of monotone functions and `N ≥ 1`,
`∫_0^1 N⁻¹ ∑_{i<N} F((i + u)/N) du = ∫_0^1 F`: the substitution `y = (i + u)/N` maps `[0, 1]` onto
the `i`-th cell. -/
lemma integral_latticeRule {P Q : ℝ → ℝ} (hP : Monotone P) (hQ : Monotone Q) {N : ℕ}
    (hN : 0 < N) :
    ∫ u in (0 : ℝ)..1, latticeRule (fun x => P x - Q x) N u = ∫ y in (0 : ℝ)..1, P y - Q y := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hmono : ∀ i : ℕ, Monotone fun u : ℝ => ((i : ℝ) + u) / N := fun i x y hxy => by
    simp only
    gcongr
  have hint : ∀ i : ℕ, IntervalIntegrable (fun u : ℝ => P ((i + u) / N) - Q ((i + u) / N))
      volume 0 1 := fun i =>
    (hP.comp (hmono i)).intervalIntegrable.sub (hQ.comp (hmono i)).intervalIntegrable
  have hcell : ∀ i : ℕ, ∫ u in (0 : ℝ)..1, (P ((i + u) / N) - Q ((i + u) / N)) =
      N * ∫ y in (i : ℝ) / N..((i + 1 : ℕ) : ℝ) / N, (P y - Q y) := by
    intro i
    have e := intervalIntegral.integral_comp_div_add (fun y => P y - Q y) (a := 0) (b := 1) hN'
      ((i : ℝ) / N)
    simp only [zero_div, zero_add, smul_eq_mul] at e
    rw [show ((i + 1 : ℕ) : ℝ) / N = 1 / N + i / N by push_cast; ring, ← e]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [show ((i : ℝ) + u) / N = u / N + i / N by ring]
  have hcellint : ∀ k < N, IntervalIntegrable (fun y => P y - Q y) volume ((k : ℝ) / N)
      (((k + 1 : ℕ) : ℝ) / N) := fun k _ => hP.intervalIntegrable.sub hQ.intervalIntegrable
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) / N)
    (μ := volume) hcellint
  simp only [Nat.cast_zero, zero_div, div_self hN'] at hsum
  unfold latticeRule
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun i _ => hint i]
  simp only [hcell, ← mul_sum, hsum]
  field_simp

/-- A random variable uniform on `[0, 1]` lives on a probability space. -/
lemma isProbabilityMeasure_of_uniform01 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Ω → ℝ} (hU : MeasurePreserving U μ (volume.restrict (Set.Icc 0 1))) :
    IsProbabilityMeasure μ := by
  constructor
  have h := hU.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simpa [Real.volume_Icc] using h

/-- Only the shifts `U_0, …, U_{R−1}` matter: extend them to a sequence of shifts with the same law,
`W_r = U_r` for `r < R` and `W_r = U_0` for `r ≥ R`. -/
lemma exists_extend_of_lt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ν : Measure ℝ}
    {U : ℕ → Ω → ℝ} {R : ℕ} (hR : 0 < R) (hU : ∀ r < R, MeasurePreserving (U r) μ ν)
    (hind : Set.Pairwise ↑(range R) fun i j => IndepFun (U i) (U j) μ) :
    ∃ W : ℕ → Ω → ℝ, (∀ r, MeasurePreserving (W r) μ ν) ∧
      (Set.Pairwise ↑(range R) fun i j => IndepFun (W i) (W j) μ) ∧ ∀ r < R, W r = U r := by
  refine ⟨fun r => if r < R then U r else U 0, fun r => ?_, fun i hi j hj hij => ?_,
    fun r hr => if_pos hr⟩
  · dsimp only
    split_ifs with h
    exacts [hU r h, hU 0 hR]
  · simp only [if_pos (mem_range.1 (mem_coe.1 hi)), if_pos (mem_range.1 (mem_coe.1 hj))]
    exact hind hi hj hij

/-- **The randomly shifted lattice rule: unbiased, with root-mean-square error `≤ V(f)/N`** (Giles
2015, §3.5, p. 26: "To regain a confidence interval one uses randomised QMC in which the set of
points is gives [sic] a random shift (for rank-1 lattice rules)", and "In the best cases, this
results in the approximate numerical integration error being `O(N_ℓ⁻¹)` rather than the usual
`O(N_ℓ^{−1/2})` error which comes from Monte Carlo sampling").  One dimension only: QMC error
theory in `d` dimensions (Koksma–Hlawka, low-discrepancy and Sobol points) is not formalised.  Let
`f` have bounded variation on `[0, 1]` with total variation `V`, let `N ≥ 1` and let the shift `U`
be uniform on `[0, 1]` (its law is Lebesgue measure on `[0, 1]`).  Then the randomly shifted
lattice rule `Q = N⁻¹ ∑_{i<N} f((i + U)/N)`
* has error `|Q − ∫_0^1 f| ≤ V/N` almost surely (`latticeRule_error_le_variation_div`, for every
  shift);
* is square-integrable and unbiased, `E[Q] = ∫_0^1 f`;
* has mean square error `E[(Q − ∫_0^1 f)²] ≤ V²/N²`, so variance `Var[Q] ≤ V²/N²`.
So the root-mean-square error is `O(N⁻¹)`, whereas `N` independent uniform samples (plain Monte
Carlo) give variance `Var[f(U)]/N` (`variance_sample_mean`, `latticeRule_vs_monteCarlo`),
root-mean-square error `O(N^{−1/2})`.  The shift is here the uniform `u` of the points
`(i + u)/N`; the usual shift `Δ` of the points `i/N + Δ mod 1` is
`shiftedLatticeRule_randomShift`. -/
theorem latticeRule_randomShift {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : Ω → ℝ}
    (hU : MeasurePreserving U μ (volume.restrict (Set.Icc 0 1))) {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) {N : ℕ} (hN : 0 < N) :
    (∀ᵐ ω ∂μ, |latticeRule f N (U ω) - ∫ y in (0 : ℝ)..1, f y| ≤
        (eVariationOn f (Set.Icc 0 1)).toReal / N) ∧
      MemLp (fun ω => latticeRule f N (U ω)) 2 μ ∧
      ∫ ω, latticeRule f N (U ω) ∂μ = ∫ y in (0 : ℝ)..1, f y ∧
      ∫ ω, (latticeRule f N (U ω) - ∫ y in (0 : ℝ)..1, f y) ^ 2 ∂μ ≤
        ((eVariationOn f (Set.Icc 0 1)).toReal / N) ^ 2 ∧
      variance (fun ω => latticeRule f N (U ω)) μ ≤
        ((eVariationOn f (Set.Icc 0 1)).toReal / N) ^ 2 := by
  have := isProbabilityMeasure_of_uniform01 hU
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := exists_monotone_sub_eqOn hf
  set V := (eVariationOn f (Set.Icc 0 1)).toReal
  set I := ∫ y in (0 : ℝ)..1, f y with hI
  have hmem : ∀ᵐ ω ∂μ, U ω ∈ Set.Icc (0 : ℝ) 1 :=
    hU.quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)
  have hG := measurable_latticeRule hP hQ N
  have hae : (fun ω => latticeRule f N (U ω)) =ᵐ[μ]
      fun ω => latticeRule (fun x => P x - Q x) N (U ω) :=
    hmem.mono fun ω h => latticeRule_congr hPQ N h
  have hbound : ∀ᵐ ω ∂μ, |latticeRule f N (U ω) - I| ≤ V / N :=
    hmem.mono fun ω h => latticeRule_error_le_variation_div hf hN h
  have hsm : AEStronglyMeasurable (fun ω => latticeRule f N (U ω)) μ :=
    (hG.comp hU.measurable).aestronglyMeasurable.congr hae.symm
  have hL2 : MemLp (fun ω => latticeRule f N (U ω)) 2 μ :=
    MemLp.of_bound hsm (|I| + V / N) (hbound.mono fun ω h => by
      rw [Real.norm_eq_abs]
      calc |latticeRule f N (U ω)| = |(latticeRule f N (U ω) - I) + I| := by
            rw [sub_add_cancel]
        _ ≤ |latticeRule f N (U ω) - I| + |I| := abs_add_le _ _
        _ ≤ _ := by linarith)
  have hmean : ∫ ω, latticeRule f N (U ω) ∂μ = I := by
    rw [integral_congr_ae hae, integral_comp_of_measurePreserving hU hG.aestronglyMeasurable,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_latticeRule hP hQ hN, hI]
    exact intervalIntegral.integral_congr fun y hy =>
      (hPQ (by rwa [Set.uIcc_of_le zero_le_one] at hy)).symm
  have hmse : ∫ ω, (latticeRule f N (U ω) - I) ^ 2 ∂μ ≤ (V / N) ^ 2 := by
    calc ∫ ω, (latticeRule f N (U ω) - I) ^ 2 ∂μ ≤ ∫ _ω, (V / N) ^ 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
            (integrable_const _) (hbound.mono fun ω h => by
              show (latticeRule f N (U ω) - I) ^ 2 ≤ (V / N) ^ 2
              rw [← sq_abs (latticeRule f N (U ω) - I)]
              exact pow_le_pow_left₀ (abs_nonneg _) h 2)
      _ = (V / N) ^ 2 := by simp
  refine ⟨hbound, hL2, hmean, hmse, ?_⟩
  rw [variance_eq_integral hsm.aemeasurable, hmean]
  exact hmse

/-- `R` independent random shifts, with the shifts uniform and independent for all indices (the
helper behind `latticeRule_replicates`, which only constrains `U_0, …, U_{R−1}`). -/
lemma latticeRule_replicates_aux {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : ℕ → Ω → ℝ} (hU : ∀ r, MeasurePreserving (U r) μ (volume.restrict (Set.Icc 0 1)))
    {N R : ℕ} (hUind : Set.Pairwise ↑(range R) fun i j => IndepFun (U i) (U j) μ) {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) (hN : 0 < N) (hR : 0 < R) :
    ∫ ω, (R : ℝ)⁻¹ * ∑ r ∈ range R, latticeRule f N (U r ω) ∂μ = ∫ y in (0 : ℝ)..1, f y ∧
      variance (fun ω => (R : ℝ)⁻¹ * ∑ r ∈ range R, latticeRule f N (U r ω)) μ ≤
        ((eVariationOn f (Set.Icc 0 1)).toReal / N) ^ 2 / R ∧
      (2 ≤ R → ∫ ω, ((R : ℝ) * (R - 1))⁻¹ * ∑ r ∈ range R, (latticeRule f N (U r ω) -
          (R : ℝ)⁻¹ * ∑ s ∈ range R, latticeRule f N (U s ω)) ^ 2 ∂μ =
        variance (fun ω => (R : ℝ)⁻¹ * ∑ r ∈ range R, latticeRule f N (U r ω)) μ) := by
  have := isProbabilityMeasure_of_uniform01 (hU 0)
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := exists_monotone_sub_eqOn hf
  have hG := measurable_latticeRule hP hQ N
  have hone := fun r => latticeRule_randomShift (hU r) hf hN
  have hae : ∀ r, (fun ω => latticeRule f N (U r ω)) =ᵐ[μ]
      fun ω => latticeRule (fun x => P x - Q x) N (U r ω) := fun r =>
    ((hU r).quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)).mono
      fun ω h => latticeRule_congr hPQ N h
  have hvar : ∀ r, variance (fun ω => latticeRule f N (U r ω)) μ =
      variance (latticeRule (fun x => P x - Q x) N) (volume.restrict (Set.Icc 0 1)) := fun r => by
    rw [variance_congr (hae r)]
    exact (hU r).variance_fun_comp hG.aemeasurable
  have hpair : Set.Pairwise ↑(range R) fun i j =>
      IndepFun (fun ω => latticeRule f N (U i ω)) (fun ω => latticeRule f N (U j ω)) μ :=
    fun i hi j hj hij => ((hUind hi hj hij).comp hG hG).congr (hae i).symm (hae j).symm
  have hL2 := fun r => (hone r).2.1
  have hmean := fun r => (hone r).2.2.1
  have hR' : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hR.ne'
  have havg := variance_sample_mean _ R hR _ hL2 hvar hpair
  refine ⟨?_, ?_, fun hR2 => ?_⟩
  · rw [integral_const_mul, integral_finsetSum _ fun r _ => (hL2 r).integrable one_le_two]
    simp only [hmean, sum_const, card_range, nsmul_eq_mul]
    field_simp
  · rw [havg, ← hvar 0]
    gcongr
    exact (hone 0).2.2.2.2
  · have hR1 : (R : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ R := by exact_mod_cast hR2
      linarith
    rw [integral_const_mul, integral_sum_sq_sub_mean _ hR hL2 hmean hvar hpair, havg]
    field_simp

/-- **`R` independent random shifts: unbiased average, variance `≤ V(f)²/(R N²)`, and the usual
variance estimate** (Giles 2015, §3.5, pp. 26–27: "Using 32 sets of points, each collectively
randomised, yields 32 set averages for the quantity of interest, `Y_ℓ`, and from these 32 random
independent values the variance of their average, `V_ℓ`, can be estimated in the usual way").
One dimension only: QMC error theory in `d` dimensions (Koksma–Hlawka, low-discrepancy and Sobol
points) is not formalised; the analogue on the torus `𝕋^d` for arbitrary points is
`randomShift_replicates`.  Let `f` have bounded variation on `[0, 1]` with total variation `V`, let
`N, R ≥ 1` and let `U_0, …, U_{R−1}` be pairwise independent shifts, each uniform on `[0, 1]` (only
these `R` shifts are constrained, and pairwise independence suffices).  The `R` set averages
`Y_r = N⁻¹ ∑_{i<N} f((i + U_r)/N)` have an unbiased average `Ȳ = R⁻¹ ∑_{r<R} Y_r`,
`E[Ȳ] = ∫_0^1 f`, with `Var[Ȳ] ≤ V²/(R N²)`; and for `R ≥ 2` the usual estimate
`(R(R − 1))⁻¹ ∑_{r<R} (Y_r − Ȳ)²` of `Var[Ȳ]` is unbiased (`integral_sum_sq_sub_mean`). -/
theorem latticeRule_replicates {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N R : ℕ}
    (hN : 0 < N) (hR : 0 < R) {U : ℕ → Ω → ℝ}
    (hU : ∀ r < R, MeasurePreserving (U r) μ (volume.restrict (Set.Icc 0 1)))
    (hUind : Set.Pairwise ↑(range R) fun i j => IndepFun (U i) (U j) μ) {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    ∫ ω, (R : ℝ)⁻¹ * ∑ r ∈ range R, latticeRule f N (U r ω) ∂μ = ∫ y in (0 : ℝ)..1, f y ∧
      variance (fun ω => (R : ℝ)⁻¹ * ∑ r ∈ range R, latticeRule f N (U r ω)) μ ≤
        ((eVariationOn f (Set.Icc 0 1)).toReal / N) ^ 2 / R ∧
      (2 ≤ R → ∫ ω, ((R : ℝ) * (R - 1))⁻¹ * ∑ r ∈ range R, (latticeRule f N (U r ω) -
          (R : ℝ)⁻¹ * ∑ s ∈ range R, latticeRule f N (U s ω)) ^ 2 ∂μ =
        variance (fun ω => (R : ℝ)⁻¹ * ∑ r ∈ range R, latticeRule f N (U r ω)) μ) := by
  obtain ⟨W, hW, hWind, hWU⟩ := exists_extend_of_lt hR hU hUind
  have hs : ∀ ω, ∑ r ∈ range R, latticeRule f N (U r ω) =
      ∑ r ∈ range R, latticeRule f N (W r ω) :=
    fun ω => sum_congr rfl fun r hr => by rw [hWU r (mem_range.1 hr)]
  have hs2 : ∀ ω (x : ℝ), ∑ r ∈ range R, (latticeRule f N (U r ω) - x) ^ 2 =
      ∑ r ∈ range R, (latticeRule f N (W r ω) - x) ^ 2 :=
    fun ω x => sum_congr rfl fun r hr => by rw [hWU r (mem_range.1 hr)]
  simp only [hs, hs2]
  exact latticeRule_replicates_aux hW hWind hf hN hR

/-- **The random shift of the rank-1 lattice modulo `1`: unbiased, with root-mean-square error
`≤ V(f)/N`** (Giles 2015, §3.5, p. 26: "To regain a confidence interval one uses randomised QMC in
which the set of points is gives [sic] a random shift (for rank-1 lattice rules)", with error "In
the best cases … `O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})`").  One dimension only: QMC error
theory in `d` dimensions (Koksma–Hlawka, low-discrepancy and Sobol points) is not formalised.  In
the convention of `shiftedQMC` (addition modulo `1`, modelled on `ℝ` with `Int.fract`; the bridge
to `shiftedQMC` on `𝕋¹` is `rank1Lattice_torus_replicates`): the rank-1 lattice `{i/N : i < N}`
shifted by a uniform `Δ ∈ [0, 1]`, `Q = N⁻¹ ∑_{i<N} f(frac(i/N + Δ))`.  For `f` of bounded
variation on `[0, 1]` with total variation `V` and `N ≥ 1`, `|Q − ∫_0^1 f| ≤ V/N` for every
outcome (`shiftedLatticeRule_error_le`), `Q` is square-integrable and unbiased, `E[Q] = ∫_0^1 f`,
`E[(Q − ∫_0^1 f)²] ≤ V²/N²` and `Var[Q] ≤ V²/N²`. -/
theorem shiftedLatticeRule_randomShift {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Δ : Ω → ℝ} (hΔ : MeasurePreserving Δ μ (volume.restrict (Set.Icc 0 1))) {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) {N : ℕ} (hN : 0 < N) :
    (∀ ω, |shiftedLatticeRule f N (Δ ω) - ∫ y in (0 : ℝ)..1, f y| ≤
        (eVariationOn f (Set.Icc 0 1)).toReal / N) ∧
      MemLp (fun ω => shiftedLatticeRule f N (Δ ω)) 2 μ ∧
      ∫ ω, shiftedLatticeRule f N (Δ ω) ∂μ = ∫ y in (0 : ℝ)..1, f y ∧
      ∫ ω, (shiftedLatticeRule f N (Δ ω) - ∫ y in (0 : ℝ)..1, f y) ^ 2 ∂μ ≤
        ((eVariationOn f (Set.Icc 0 1)).toReal / N) ^ 2 ∧
      variance (fun ω => shiftedLatticeRule f N (Δ ω)) μ ≤
        ((eVariationOn f (Set.Icc 0 1)).toReal / N) ^ 2 := by
  have := isProbabilityMeasure_of_uniform01 hΔ
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := exists_monotone_sub_eqOn hf
  set V := (eVariationOn f (Set.Icc 0 1)).toReal
  set I := ∫ y in (0 : ℝ)..1, f y with hI
  have hfr : ∀ y : ℝ, Int.fract y ∈ Set.Icc (0 : ℝ) 1 := fun y =>
    ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩
  -- the estimator through the measurable `P − Q`
  set G : ℝ → ℝ := fun x => (N : ℝ)⁻¹ * ∑ i ∈ range N,
    (P (Int.fract ((i : ℝ) / N + x)) - Q (Int.fract ((i : ℝ) / N + x))) with hGdef
  have hXG : ∀ ω, shiftedLatticeRule f N (Δ ω) = G (Δ ω) :=
    fun ω => by
      simp only [shiftedLatticeRule, hGdef]
      congr 1
      exact sum_congr rfl fun i _ => hPQ (hfr _)
  have hmf : ∀ c : ℝ, Measurable fun x : ℝ => Int.fract (c + x) := fun c =>
    measurable_fract.comp (measurable_const_add c)
  have hG : Measurable G := (Finset.measurable_sum _ fun i _ =>
    (hP.measurable.comp (hmf _)).sub (hQ.measurable.comp (hmf _))).const_mul _
  have hbound : ∀ ω, |G (Δ ω) - I| ≤ V / N := fun ω => by
    rw [← hXG]
    exact shiftedLatticeRule_error_le hf hN (Δ ω)
  have hL2 : MemLp (fun ω => G (Δ ω)) 2 μ :=
    MemLp.of_bound (hG.comp hΔ.measurable).aestronglyMeasurable (|I| + V / N)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        calc |G (Δ ω)| = |(G (Δ ω) - I) + I| := by rw [sub_add_cancel]
          _ ≤ |G (Δ ω) - I| + |I| := abs_add_le _ _
          _ ≤ _ := by linarith [hbound ω])
  -- `x ↦ (P − Q)(frac x)` is `1`-periodic and bounded
  have hH : Function.Periodic (fun x => P (Int.fract x) - Q (Int.fract x)) 1 := fun x => by
    simp only [Int.fract_add_one]
  have hHb : ∀ x : ℝ, ‖P (Int.fract x) - Q (Int.fract x)‖ ≤ |P 0| + |P 1| + (|Q 0| + |Q 1|) :=
    fun x => by
      have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
      have h1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
      have hp0 := hP h0
      have hp1 := hP h1
      have hq0 := hQ h0
      have hq1 := hQ h1
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [neg_abs_le (P 0), le_abs_self (P 1), neg_abs_le (Q 0),
        le_abs_self (Q 1), abs_nonneg (P 0), abs_nonneg (P 1), abs_nonneg (Q 0),
        abs_nonneg (Q 1)]
  have hHint : ∀ c : ℝ, IntervalIntegrable
      (fun x => P (Int.fract (c + x)) - Q (Int.fract (c + x))) volume 0 1 := fun c =>
    (intervalIntegrable_const (c := |P 0| + |P 1| + (|Q 0| + |Q 1|))).mono_fun
      ((hP.measurable.comp (hmf c)).sub (hQ.measurable.comp (hmf c))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (hHb (c + x)).trans (le_abs_self _))
  have hcell : ∀ c : ℝ, ∫ x in (0 : ℝ)..1, (P (Int.fract (c + x)) - Q (Int.fract (c + x))) =
      ∫ y in (0 : ℝ)..1, (P y - Q y) := by
    intro c
    have e1 := intervalIntegral.integral_comp_add_right
      (fun x => P (Int.fract x) - Q (Int.fract x)) c (a := 0) (b := 1)
    have e2 := hH.intervalIntegral_add_eq c 0
    simp only [zero_add] at e1 e2
    rw [add_comm 1 c] at e1
    calc ∫ x in (0 : ℝ)..1, (P (Int.fract (c + x)) - Q (Int.fract (c + x)))
        = ∫ x in (0 : ℝ)..1, (P (Int.fract (x + c)) - Q (Int.fract (x + c))) := by
          simp only [add_comm c]
      _ = ∫ x in (0 : ℝ)..1, (P (Int.fract x) - Q (Int.fract x)) := e1.trans e2
      _ = ∫ y in (0 : ℝ)..1, (P y - Q y) := by
          rw [intervalIntegral.integral_of_le zero_le_one,
            intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
            integral_Ioc_eq_integral_Ioo]
          exact setIntegral_congr_fun measurableSet_Ioo fun x hx => by
            simp only [Int.fract_eq_self.2 ⟨hx.1.le, hx.2⟩]
  have hmean : ∫ ω, G (Δ ω) ∂μ = I := by
    rw [integral_comp_of_measurePreserving hΔ hG.aestronglyMeasurable,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    simp only [hGdef]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum fun i _ => hHint _]
    simp only [hcell, sum_const, card_range, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hN', one_mul, hI]
    exact intervalIntegral.integral_congr fun y hy =>
      (hPQ (by rwa [Set.uIcc_of_le zero_le_one] at hy)).symm
  have hmse : ∫ ω, (G (Δ ω) - I) ^ 2 ∂μ ≤ (V / N) ^ 2 := by
    calc ∫ ω, (G (Δ ω) - I) ^ 2 ∂μ ≤ ∫ _ω, (V / N) ^ 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun ω => by
              show (G (Δ ω) - I) ^ 2 ≤ (V / N) ^ 2
              rw [← sq_abs (G (Δ ω) - I)]
              exact pow_le_pow_left₀ (abs_nonneg _) (hbound ω) 2)
      _ = (V / N) ^ 2 := by simp
  simp only [hXG]
  refine ⟨hbound, hL2, hmean, hmse, ?_⟩
  rw [variance_eq_integral hL2.1.aemeasurable, hmean]
  exact hmse

/-- **Monte Carlo `O(N^{−1/2})` versus the randomly shifted lattice `O(N⁻¹)`, for every integrand of
bounded variation** (Giles 2015, §3.5, p. 26: "In the best cases, this results in the approximate
numerical integration error being `O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})` error which comes
from Monte Carlo sampling"; §1, p. 2: Monte Carlo has variance `N⁻¹V[P]`, "so the r.m.s. error is
`O(N^{−1/2})`").  One dimension only: QMC error theory in `d` dimensions (Koksma–Hlawka,
low-discrepancy and Sobol points) is not formalised.  Let `f` have bounded variation on `[0, 1]`
with total variation `V`, let `N ≥ 1` and let `U_0, …, U_{N−1}` be pairwise independent and
uniform on `[0, 1]`.  Plain Monte Carlo with `N` samples, `N⁻¹ ∑_{n<N} f(U_n)`, is unbiased with
variance exactly `σ²/N`, `σ² = Var[f(U_0)]` (`variance_sample_mean`), while the randomly shifted
lattice rule `N⁻¹ ∑_{i<N} f((i + U_0)/N)` with the same number of points has mean square error
`≤ V²/N²` (`latticeRule_randomShift`).  So, when `σ² > 0`, the ratio of the lattice mean square
error to the Monte Carlo one is `≤ V²/(N σ²)`, which tends to `0` as `N → ∞`. -/
theorem latticeRule_vs_monteCarlo {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : ℕ}
    (hN : 0 < N) {U : ℕ → Ω → ℝ}
    (hU : ∀ n < N, MeasurePreserving (U n) μ (volume.restrict (Set.Icc 0 1)))
    (hUind : Set.Pairwise ↑(range N) fun i j => IndepFun (U i) (U j) μ) {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    ∫ ω, (N : ℝ)⁻¹ * ∑ n ∈ range N, f (U n ω) ∂μ = ∫ y in (0 : ℝ)..1, f y ∧
      variance (fun ω => (N : ℝ)⁻¹ * ∑ n ∈ range N, f (U n ω)) μ =
        variance (fun ω => f (U 0 ω)) μ / N ∧
      ∫ ω, (latticeRule f N (U 0 ω) - ∫ y in (0 : ℝ)..1, f y) ^ 2 ∂μ ≤
        ((eVariationOn f (Set.Icc 0 1)).toReal / N) ^ 2 ∧
      (0 < variance (fun ω => f (U 0 ω)) μ →
        (∫ ω, (latticeRule f N (U 0 ω) - ∫ y in (0 : ℝ)..1, f y) ^ 2 ∂μ) /
            variance (fun ω => (N : ℝ)⁻¹ * ∑ n ∈ range N, f (U n ω)) μ ≤
          (eVariationOn f (Set.Icc 0 1)).toReal ^ 2 /
            (N * variance (fun ω => f (U 0 ω)) μ)) := by
  obtain ⟨W, hW, hWind, hWU⟩ := exists_extend_of_lt hN hU hUind
  have hs : ∀ ω, ∑ n ∈ range N, f (U n ω) = ∑ n ∈ range N, f (W n ω) :=
    fun ω => sum_congr rfl fun n hn => by rw [hWU n (mem_range.1 hn)]
  simp only [hs, ← hWU 0 hN]
  have := isProbabilityMeasure_of_uniform01 (hW 0)
  obtain ⟨H, hHm, ⟨B, hB⟩, hfH⟩ := exists_measurable_bounded_eqOn hf
  set I := ∫ y in (0 : ℝ)..1, f y with hI
  set V := (eVariationOn f (Set.Icc 0 1)).toReal
  have hae : ∀ n, (fun ω => f (W n ω)) =ᵐ[μ] fun ω => H (W n ω) := fun n =>
    ((hW n).quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)).mono
      fun ω h => hfH h
  have hL2 : ∀ n, MemLp (fun ω => f (W n ω)) 2 μ := fun n =>
    MemLp.of_bound ((hHm.comp (hW n).measurable).aestronglyMeasurable.congr (hae n).symm) B
      ((hae n).mono fun ω (h : f (W n ω) = H (W n ω)) => by
        rw [h, Real.norm_eq_abs]
        exact hB _)
  have hvar : ∀ n, variance (fun ω => f (W n ω)) μ =
      variance H (volume.restrict (Set.Icc 0 1)) := fun n => by
    rw [variance_congr (hae n)]
    exact (hW n).variance_fun_comp hHm.aemeasurable
  have hpair : Set.Pairwise ↑(range N) fun i j =>
      IndepFun (fun ω => f (W i ω)) (fun ω => f (W j ω)) μ :=
    fun i hi j hj hij => ((hWind hi hj hij).comp hHm hHm).congr (hae i).symm (hae j).symm
  have hmean1 : ∀ n, ∫ ω, f (W n ω) ∂μ = I := fun n => by
    rw [integral_congr_ae (hae n),
      integral_comp_of_measurePreserving (hW n) hHm.aestronglyMeasurable,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, hI]
    exact intervalIntegral.integral_congr fun y hy =>
      (hfH (by rwa [Set.uIcc_of_le zero_le_one] at hy)).symm
  have hvarMC : variance (fun ω => (N : ℝ)⁻¹ * ∑ n ∈ range N, f (W n ω)) μ =
      variance (fun ω => f (W 0 ω)) μ / N := by
    rw [variance_sample_mean _ N hN _ hL2 hvar hpair, hvar 0]
  have hmse := (latticeRule_randomShift (hW 0) hf hN).2.2.2.1
  refine ⟨?_, hvarMC, hmse, fun hσ => ?_⟩
  · have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [integral_const_mul, integral_finsetSum _ fun n _ => (hL2 n).integrable one_le_two]
    simp only [hmean1, sum_const, card_range, nsmul_eq_mul]
    field_simp
  · have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
    rw [hvarMC]
    calc _ ≤ (V / N) ^ 2 / (variance (fun ω => f (W 0 ω)) μ / N) :=
          (div_le_div_iff_of_pos_right (div_pos hσ hNpos)).2 hmse
      _ = V ^ 2 / (N * variance (fun ω => f (W 0 ω)) μ) := by
          field_simp

/-- A random variable uniform on `[0, 1]` has variance `1/12`. -/
lemma variance_uniform01 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : Ω → ℝ}
    (hU : MeasurePreserving U μ (volume.restrict (Set.Icc 0 1))) : variance U μ = 1 / 12 := by
  have hν : ∀ φ : ℝ → ℝ, ∫ x, φ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
      ∫ x in (0 : ℝ)..1, φ x := fun φ => by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  have hmean : ∫ x, id x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 1 / 2 := by
    rw [hν id]
    simp only [id, integral_id]
    norm_num
  have h := hU.variance_fun_comp (f := id) measurable_id.aemeasurable
  rw [show (fun ω => id (U ω)) = U from rfl] at h
  rw [h, variance_eq_integral measurable_id.aemeasurable, hmean, hν (fun x => (id x - 1 / 2) ^ 2)]
  simp only [id]
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ 2), integral_pow]
  norm_num

/-- `∑_{i<N} i = N(N − 1)/2` in `ℝ`. -/
lemma sum_range_natCast_real (N : ℕ) : ∑ i ∈ range N, (i : ℝ) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- For `f(x) = x` the shifted lattice rule is `(N − 1)/(2N) + u/N`. -/
lemma latticeRule_id {N : ℕ} (hN : 0 < N) (u : ℝ) :
    latticeRule id N u = u * (N : ℝ)⁻¹ + (N - 1) / (2 * N) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  unfold latticeRule
  simp only [id, ← sum_div, sum_add_distrib, sum_range_natCast_real, sum_const, card_range,
    nsmul_eq_mul]
  field_simp
  ring

/-- **Monte Carlo `O(N^{−1/2})` versus the randomly shifted lattice `O(N⁻¹)`, exactly, for
`f(x) = x`** (Giles 2015, §3.5, p. 26: "In the best cases, this results in the approximate
numerical integration error being `O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})` error which comes
from Monte Carlo sampling"; §1, p. 2: Monte Carlo has variance `N⁻¹V[P]`, "so the r.m.s. error is
`O(N^{−1/2})`").  One dimension only: QMC error theory in `d` dimensions (Koksma–Hlawka,
low-discrepancy and Sobol points) is not formalised.  Let `N ≥ 1` and let `U_0, …, U_{N−1}` be
pairwise independent and uniform on `[0, 1]`.  For the integrand `f(x) = x` (total variation `1`,
`∫_0^1 f = 1/2`), plain Monte Carlo with `N` samples, `N⁻¹ ∑_{n<N} U_n`, has variance exactly
`1/(12N)` (`variance_sample_mean`), while the randomly shifted lattice rule
`N⁻¹ ∑_{i<N} (i + U_0)/N` with the same number of points has variance exactly `1/(12N²)`:
root-mean-square errors `1/√(12N)` and `1/(√12 N)`.  (`latticeRule_vs_monteCarlo` gives the
inequality version for every integrand of bounded variation.) -/
theorem variance_latticeRule_id_vs_mc {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : ℕ}
    (hN : 0 < N) {U : ℕ → Ω → ℝ}
    (hU : ∀ n < N, MeasurePreserving (U n) μ (volume.restrict (Set.Icc 0 1)))
    (hUind : Set.Pairwise ↑(range N) fun i j => IndepFun (U i) (U j) μ) :
    variance (fun ω => (N : ℝ)⁻¹ * ∑ n ∈ range N, U n ω) μ = 1 / (12 * N) ∧
      variance (fun ω => latticeRule id N (U 0 ω)) μ = 1 / (12 * N ^ 2) := by
  obtain ⟨W, hW, hWind, hWU⟩ := exists_extend_of_lt hN hU hUind
  have hs : ∀ ω, ∑ n ∈ range N, U n ω = ∑ n ∈ range N, W n ω :=
    fun ω => sum_congr rfl fun n hn => by rw [hWU n (mem_range.1 hn)]
  simp only [hs, ← hWU 0 hN]
  have := isProbabilityMeasure_of_uniform01 (hW 0)
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hL2 : ∀ n, MemLp (W n) 2 μ := fun n =>
    memLp_of_bounded ((hW n).quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc))
      (hW n).measurable.aestronglyMeasurable 2
  refine ⟨?_, ?_⟩
  · rw [variance_sample_mean W N hN (1 / 12) hL2 (fun n => variance_uniform01 (hW n)) hWind]
    field_simp
  · simp only [latticeRule_id hN]
    rw [variance_add_const ((hW 0).measurable.aestronglyMeasurable.mul_const _),
      variance_mul_const, variance_uniform01 (hW 0)]
    field_simp

/-! ### The bridge to `shiftedQMC` on the circle `𝕋¹` -/

/-- **The integrand on the circle `𝕋¹ = ℝ/ℤ`** (Mathlib's `UnitAddTorus (Fin 1)`) of a function
`f` on `[0, 1)`: `F(y) = f(y mod 1)`, where `y mod 1 ∈ [0, 1)` is the representative of `y`
(`AddCircle.equivIco 1 0`). -/
noncomputable def torusLift (f : ℝ → ℝ) (y : UnitAddTorus (Fin 1)) : ℝ :=
  f (AddCircle.equivIco 1 0 (y 0))

/-- **The rank-1 lattice on the circle `𝕋¹`** (Giles 2015, §3.5, p. 26: "rank-1 lattices (Dick et
al. 2007)"): the points `x_i = i/N mod 1`. -/
noncomputable def torusLattice (N i : ℕ) : UnitAddTorus (Fin 1) :=
  fun _ => (((i : ℝ) / N : ℝ) : UnitAddCircle)

/-- The randomly shifted QMC average `shiftedQMC` of `RandomShiftQMC.lean`, for the lattice
`i/N` on `𝕋¹` shifted by `u mod 1`, is the shifted lattice rule `shiftedLatticeRule f N u`. -/
lemma shiftedQMC_torusLift (f : ℝ → ℝ) (N : ℕ) (u : ℝ) :
    shiftedQMC (torusLift f) (torusLattice N) N (fun _ => (u : UnitAddCircle)) =
      shiftedLatticeRule f N u := by
  unfold shiftedQMC torusLift torusLattice shiftedLatticeRule
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, ← AddCircle.coe_add, AddCircle.coe_equivIco_mk_apply, div_one, mul_one]

/-- The covering map `t ↦ t mod 1` from `(0, 1]` with Lebesgue measure onto the circle `𝕋¹` with
its Haar probability measure is measure preserving. -/
lemma measurePreserving_coe_torus :
    MeasurePreserving (fun t : ℝ => (fun _ : Fin 1 => (t : UnitAddCircle)))
      (volume.restrict (Set.Ioc 0 (0 + 1))) (volume : Measure (UnitAddTorus (Fin 1))) :=
  (volume_preserving_funUnique (Fin 1) UnitAddCircle).symm.comp
    (UnitAddCircle.measurePreserving_mk 0)

/-- **The rank-1 lattice on `𝕋¹` in `randomShift_replicates`: `V₁ ≤ V(f)²/N²`** (Giles 2015, §3.5,
pp. 26–27: "To regain a confidence interval one uses randomised QMC in which the set of points is
gives [sic] a random shift (for rank-1 lattice rules) … the variance of their average, `V_ℓ`, can
be estimated in the usual way"; "In the best cases … `O(N_ℓ⁻¹)`").  One dimension only: QMC error
theory in `d` dimensions (Koksma–Hlawka, low-discrepancy and Sobol points) is not formalised.  This
links the shift modulo `1` on `ℝ` (`shiftedLatticeRule`) with `shiftedQMC` on the torus `𝕋^d`,
`d = 1`.  Let `f` have bounded variation on `[0, 1]` with total variation `V`, let `F = torusLift f`
(`F(y) = f(y mod 1)`) and let `x = torusLattice N` (`x_i = i/N mod 1`), `N, R ≥ 1`.  Then
* `shiftedQMC F x N (u mod 1) = shiftedLatticeRule f N u` for every `u ∈ ℝ`;
* `F` is measurable and square-integrable on `𝕋¹`, with `∫_{𝕋¹} F = ∫_0^1 f`;
* the variance `V₁` of one set average over a uniform shift, the quantity of
  `randomShift_replicates`, satisfies `V₁ ≤ V²/N²` (`shiftedLatticeRule_randomShift`);
* with independent shifts `U_0, U_1, …` uniform on `𝕋¹` (the hypotheses of
  `randomShift_replicates`), the average `Ȳ` of the `R` set averages has `E[Ȳ] = ∫_0^1 f` and
  `Var[Ȳ] = V₁/R ≤ V²/(R N²)`. -/
theorem rank1Lattice_torus_replicates {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : ℕ → Ω → UnitAddTorus (Fin 1)} (hU : ∀ r, MeasurePreserving (U r) μ volume)
    (hUind : iIndepFun U μ) {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1)) {N R : ℕ}
    (hN : 0 < N) (hR : 0 < R) :
    (∀ u : ℝ, shiftedQMC (torusLift f) (torusLattice N) N (fun _ => (u : UnitAddCircle)) =
        shiftedLatticeRule f N u) ∧
      Measurable (torusLift f) ∧ MemLp (torusLift f) 2 volume ∧
      ∫ y, torusLift f y = ∫ y in (0 : ℝ)..1, f y ∧
      variance (shiftedQMC (torusLift f) (torusLattice N) N) volume ≤
        ((eVariationOn f (Set.Icc 0 1)).toReal / N) ^ 2 ∧
      ∫ ω, (R : ℝ)⁻¹ * ∑ r ∈ range R, shiftedQMC (torusLift f) (torusLattice N) N (U r ω) ∂μ =
        ∫ y in (0 : ℝ)..1, f y ∧
      variance (fun ω => (R : ℝ)⁻¹ * ∑ r ∈ range R,
          shiftedQMC (torusLift f) (torusLattice N) N (U r ω)) μ ≤
        ((eVariationOn f (Set.Icc 0 1)).toReal / N) ^ 2 / R := by
  have hμ : IsProbabilityMeasure μ := by
    constructor
    have h := (hU 0).measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    rw [Set.preimage_univ, volume_pi, Measure.pi_univ] at h
    simpa using h
  obtain ⟨H, hHm, ⟨B, hB⟩, hfH⟩ := exists_measurable_bounded_eqOn hf
  have hrep : ∀ y : UnitAddCircle, (AddCircle.equivIco 1 0 y : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    fun y => by
      have h := (AddCircle.equivIco 1 0 y).2
      exact ⟨h.1, (lt_of_lt_of_eq h.2 (zero_add 1)).le⟩
  have hFH : torusLift f = torusLift H := funext fun y => hfH (hrep (y 0))
  have hrepm : Measurable fun y : UnitAddCircle => (AddCircle.equivIco 1 0 y : ℝ) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  have hFm : Measurable (torusLift f) := by
    rw [hFH]
    exact hHm.comp (hrepm.comp (measurable_pi_apply 0))
  have hF2 : MemLp (torusLift f) 2 volume :=
    MemLp.of_bound hFm.aestronglyMeasurable B (Filter.Eventually.of_forall fun y => by
      rw [hFH, Real.norm_eq_abs]
      exact hB _)
  have hφ := measurePreserving_coe_torus
  have hint : ∫ y, torusLift f y = ∫ y in (0 : ℝ)..1, f y := by
    rw [← integral_comp_of_measurePreserving hφ hFm.aestronglyMeasurable]
    simp only [torusLift, AddCircle.coe_equivIco_mk_apply, div_one, mul_one]
    rw [zero_add, integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
      simp only [Int.fract_eq_self.2 ⟨ht.1.le, ht.2⟩]
  have hQm := measurable_shiftedQMC hFm (torusLattice N) N
  have hvar1 : variance (shiftedQMC (torusLift f) (torusLattice N) N) volume ≤
      ((eVariationOn f (Set.Icc 0 1)).toReal / N) ^ 2 := by
    rw [← hφ.variance_fun_comp hQm.aemeasurable]
    simp only [shiftedQMC_torusLift]
    have hid : MeasurePreserving (fun t : ℝ => t) (volume.restrict (Set.Ioc 0 (0 + 1)))
        (volume.restrict (Set.Icc 0 1)) := by
      rw [zero_add, Measure.restrict_congr_set Ioc_ae_eq_Icc]
      exact MeasurePreserving.id _
    exact (shiftedLatticeRule_randomShift hid hf hN).2.2.2.2
  obtain ⟨-, -, -, hmeanR, hvarR, -⟩ :=
    randomShift_replicates hU hUind (torusLattice N) hFm hF2 hN hR
  refine ⟨shiftedQMC_torusLift f N, hFm, hF2, hint, hvar1, hmeanR.trans hint, ?_⟩
  rw [hvarR]
  gcongr

/-! ### MLQMC complexity in one dimension -/

/-- `2^{aL} ≤ K1 a c₁ / ε` for `L = levelL a c₁ (ε/2)` and `0 < ε < 1` (as in `exists_L_N`). -/
lemma two_rpow_levelL_half_le {a c₁ ε : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) (hε : 0 < ε)
    (hε1 : ε < 1) : (2 : ℝ) ^ (a * (levelL a c₁ (ε / 2) : ℝ)) ≤ K1 a c₁ / ε := by
  have h := two_rpow_levelL_le ha hc₁ (half_pos hε)
  have hmax : max 1 (c₁ / (ε / 2)) ≤ (1 + 2 * c₁) / ε := by
    rw [show c₁ / (ε / 2) = 2 * c₁ / ε by rw [div_div_eq_mul_div, mul_comm]]
    apply max_le
    · rw [le_div_iff₀ hε]
      linarith
    · rw [div_le_div_iff_of_pos_right hε]
      linarith
  calc (2 : ℝ) ^ (a * (levelL a c₁ (ε / 2) : ℝ)) ≤ 2 ^ a * max 1 (c₁ / (ε / 2)) := h
    _ ≤ 2 ^ a * ((1 + 2 * c₁) / ε) := by gcongr
    _ = K1 a c₁ / ε := by unfold K1; ring

/-- **The rounding-up overhead, for every `g ∈ ℝ`.**  For `a, K > 0` there is `K₀ > 0` with
`∑_{ℓ≤L} 2^{gℓ} ≤ K₀ ε^{−max(1, g/a)}` whenever `0 < ε < 1` and `2^{aL} ≤ K/ε`: for `g > 0` this
is `tail_cost_bound`; for `g ≤ 0` the sum is at most `L + 1 ≤ 2^a/(2^a − 1) · 2^{aL}` (Bernoulli's
inequality). -/
lemma exists_sum_two_rpow_le {a K : ℝ} (g : ℝ) (ha : 0 < a) (hK : 0 < K) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ L : ℕ, (2 : ℝ) ^ (a * (L : ℝ)) ≤ K / ε →
      ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ g) ^ ℓ ≤ K₀ * ε ^ (-max 1 (g / a)) := by
  rcases lt_or_ge 0 g with hg | hg
  · have hg1 : 1 < (2 : ℝ) ^ g := Real.one_lt_rpow one_lt_two hg
    have hg1' : 0 < (2 : ℝ) ^ g - 1 := by linarith
    have hK0 : 0 < 2 ^ g / (2 ^ g - 1) * K ^ (g / a) :=
      mul_pos (div_pos (by positivity) hg1') (Real.rpow_pos_of_pos hK _)
    refine ⟨2 ^ g / (2 ^ g - 1) * K ^ (g / a), hK0, fun ε hε hε1 L hL => ?_⟩
    have h := tail_cost_bound ha hg one_pos hK hε L hL
    have hp : ε ^ (-(g / a)) ≤ ε ^ (-max 1 (g / a)) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1.le (neg_le_neg (le_max_right _ _))
    calc ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ g) ^ ℓ
        ≤ 2 ^ g / (2 ^ g - 1) * K ^ (g / a) * ε ^ (-(g / a)) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hK0.le
  · have ha1 : 1 < (2 : ℝ) ^ a := Real.one_lt_rpow one_lt_two ha
    have ha1' : 0 < (2 : ℝ) ^ a - 1 := by linarith
    have hK0 : 0 < 2 ^ a / (2 ^ a - 1) * K := mul_pos (div_pos (by positivity) ha1') hK
    refine ⟨2 ^ a / (2 ^ a - 1) * K, hK0, fun ε hε hε1 L hL => ?_⟩
    have hle1 : ∀ ℓ : ℕ, ((2 : ℝ) ^ g) ^ ℓ ≤ 1 := fun ℓ =>
      pow_le_one₀ (Real.rpow_nonneg zero_le_two _)
        (Real.rpow_le_one_of_one_le_of_nonpos one_le_two hg)
    have hbern : 1 + (L : ℝ) * ((2 : ℝ) ^ a - 1) ≤ (2 : ℝ) ^ (a * (L : ℝ)) := by
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 2 ^ a - 1 by linarith) L
      rwa [show (1 : ℝ) + (2 ^ a - 1) = 2 ^ a by ring, ← two_rpow_mul_nat] at h
    have h1 : (1 : ℝ) ≤ 2 ^ (a * (L : ℝ)) := Real.one_le_rpow one_le_two (by positivity)
    have h2 : (2 : ℝ) ^ a * 2 ^ (a * (L : ℝ)) ≤ 2 ^ a * (K / ε) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have hL1 : ((L : ℝ) + 1) * (2 ^ a - 1) ≤ 2 ^ a * (K / ε) := by
      nlinarith [mul_nonneg ha1'.le (sub_nonneg.2 h1)]
    have hsum : ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ g) ^ ℓ ≤ L + 1 := by
      calc _ ≤ ∑ ℓ ∈ range (L + 1), (1 : ℝ) := sum_le_sum fun ℓ _ => hle1 ℓ
        _ = L + 1 := by simp
    have hp : ε⁻¹ ≤ ε ^ (-max 1 (g / a)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (neg_le_neg (le_max_left _ _))
    calc _ ≤ (L : ℝ) + 1 := hsum
      _ ≤ 2 ^ a * (K / ε) / (2 ^ a - 1) := by rw [le_div_iff₀ ha1']; exact hL1
      _ = 2 ^ a / (2 ^ a - 1) * K * ε⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hK0.le

/-- `2^{−bℓ} ≤ 2^{−b'ℓ}` for `b' ≤ b` and `ℓ ∈ ℕ`. -/
lemma two_rpow_neg_mul_le {b b' : ℝ} (h : b' ≤ b) (ℓ : ℕ) :
    (2 : ℝ) ^ (-(b * (ℓ : ℝ))) ≤ 2 ^ (-(b' * (ℓ : ℝ))) :=
  Real.rpow_le_rpow_of_exponent_le one_le_two
    (neg_le_neg (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg ℓ)))

/-- The MLQMC complexity bound in the regime `b > g` (the helper behind `mlqmc_complexity_core`):
`L = levelL a c₁ (ε/2)` and `N_ℓ = ⌈A ε⁻¹ 2^{−(b+g)ℓ/2}⌉` with `A = 2c₂/(1 − 2^{−(b−g)/2})`; the
main cost is `O(ε⁻¹)` and the rounding up costs `O(ε^{−max(1, g/a)})`
(`exists_sum_two_rpow_le`). -/
lemma mlqmc_core_of_gt {a b g c₁ c₂ c₃ : ℝ} (ha : 0 < a) (hgb : g < b) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N ℓ) ^ 2 < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          K * ε ^ (-max 1 (g / a)) := by
  set t : ℝ := (2 : ℝ) ^ (-((b - g) / 2)) with ht
  set w : ℝ := (2 : ℝ) ^ (-((b + g) / 2)) with hw
  have ht0 : 0 < t := Real.rpow_pos_of_pos two_pos _
  have ht1 : t < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have h1t : 0 < 1 - t := by linarith
  have hw0 : 0 < w := Real.rpow_pos_of_pos two_pos _
  have hB : ∀ ℓ : ℕ, (2 : ℝ) ^ (-(b * (ℓ : ℝ))) = w ^ ℓ * t ^ ℓ := fun ℓ => by
    rw [← mul_pow, hw, ht, ← Real.rpow_add two_pos, ← two_rpow_mul_nat]
    congr 1
    ring
  have hG : ∀ ℓ : ℕ, w ^ ℓ * (2 : ℝ) ^ (g * (ℓ : ℝ)) = t ^ ℓ := fun ℓ => by
    rw [two_rpow_mul_nat, ← mul_pow, hw, ht, ← Real.rpow_add two_pos]
    congr 2
    ring
  set A : ℝ := 2 * c₂ / (1 - t) with hA
  have hA0 : 0 < A := div_pos (by positivity) h1t
  obtain ⟨K₀, hK₀, hround⟩ := exists_sum_two_rpow_le g ha (K1_pos (α := a) hc₁)
  refine ⟨A * c₃ / (1 - t) + c₃ * K₀, add_pos (div_pos (mul_pos hA0 hc₃) h1t) (mul_pos hc₃ hK₀),
    fun ε hε hε1 => ⟨levelL a c₁ (ε / 2), fun ℓ => ⌈A / ε * w ^ ℓ⌉₊,
      fun ℓ => Nat.ceil_pos.2 (by positivity), ?_, ?_⟩⟩
  · -- the mean square error
    have hbias : (c₁ * (2 : ℝ) ^ (-(a * (levelL a c₁ (ε / 2) : ℝ)))) ^ 2 ≤ ε ^ 2 / 4 := by
      have hb := levelL_bias ha hc₁ (half_pos hε)
      calc _ ≤ (ε / 2) ^ 2 := by gcongr
        _ = ε ^ 2 / 4 := by ring
    have hterm : ∀ ℓ ∈ range (levelL a c₁ (ε / 2) + 1),
        (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈A / ε * w ^ ℓ⌉₊ : ℕ) : ℝ)) ^ 2 ≤
          (ε * (1 - t) / 2) ^ 2 * (t ^ 2) ^ ℓ := by
      intro ℓ _
      have hN : A / ε * w ^ ℓ ≤ ((⌈A / ε * w ^ ℓ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have hpos : 0 < A / ε * w ^ ℓ := by positivity
      have h1 : c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈A / ε * w ^ ℓ⌉₊ : ℕ) : ℝ) ≤
          ε * (1 - t) / 2 * t ^ ℓ := by
        rw [hB, div_le_iff₀ (hpos.trans_le hN)]
        calc c₂ * (w ^ ℓ * t ^ ℓ) = ε * (1 - t) / 2 * t ^ ℓ * (A / ε * w ^ ℓ) := by
              rw [hA]
              field_simp
          _ ≤ ε * (1 - t) / 2 * t ^ ℓ * ((⌈A / ε * w ^ ℓ⌉₊ : ℕ) : ℝ) := by gcongr
      have h0 : 0 ≤ c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈A / ε * w ^ ℓ⌉₊ : ℕ) : ℝ) := by
        positivity
      calc _ ≤ (ε * (1 - t) / 2 * t ^ ℓ) ^ 2 := by gcongr
        _ = _ := by ring
    have hgeo := geom_sum_le_of_lt_one (sq_nonneg t) (by nlinarith) (levelL a c₁ (ε / 2) + 1)
    have hvar : ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1),
        (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈A / ε * w ^ ℓ⌉₊ : ℕ) : ℝ)) ^ 2 ≤ ε ^ 2 / 4 := by
      calc _ ≤ ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1), (ε * (1 - t) / 2) ^ 2 * (t ^ 2) ^ ℓ :=
            sum_le_sum hterm
        _ = (ε * (1 - t) / 2) ^ 2 * ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1), (t ^ 2) ^ ℓ := by
            rw [mul_sum]
        _ ≤ (ε * (1 - t) / 2) ^ 2 * (1 - t ^ 2)⁻¹ := by gcongr
        _ = ε ^ 2 / 4 * ((1 - t) / (1 + t)) := by
            have h1t' : 1 - t ^ 2 = (1 - t) * (1 + t) := by ring
            rw [h1t']
            field_simp
            norm_num
        _ ≤ ε ^ 2 / 4 * 1 := by
            gcongr
            rw [div_le_one (by linarith)]
            linarith
        _ = ε ^ 2 / 4 := mul_one _
    nlinarith [sq_pos_of_pos hε]
  · -- the cost
    have hL2 := two_rpow_levelL_half_le ha hc₁ hε hε1
    have hterm : ∀ ℓ ∈ range (levelL a c₁ (ε / 2) + 1),
        ((⌈A / ε * w ^ ℓ⌉₊ : ℕ) : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          A * c₃ / ε * t ^ ℓ + c₃ * ((2 : ℝ) ^ g) ^ ℓ := by
      intro ℓ _
      have hN : ((⌈A / ε * w ^ ℓ⌉₊ : ℕ) : ℝ) ≤ A / ε * w ^ ℓ + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      calc _ ≤ (A / ε * w ^ ℓ + 1) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) := by gcongr
        _ = A * c₃ / ε * (w ^ ℓ * (2 : ℝ) ^ (g * (ℓ : ℝ))) + c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ)) := by
            ring
        _ = _ := by rw [hG, two_rpow_mul_nat]
    have hround' := hround ε hε hε1 _ hL2
    have hgeo := geom_sum_le_of_lt_one ht0.le ht1 (levelL a c₁ (ε / 2) + 1)
    have hp1 : ε⁻¹ ≤ ε ^ (-max 1 (g / a)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (neg_le_neg (le_max_left _ _))
    calc _ ≤ ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1),
          (A * c₃ / ε * t ^ ℓ + c₃ * ((2 : ℝ) ^ g) ^ ℓ) := sum_le_sum hterm
      _ = A * c₃ / ε * ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1), t ^ ℓ +
          c₃ * ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1), ((2 : ℝ) ^ g) ^ ℓ := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ A * c₃ / ε * (1 - t)⁻¹ + c₃ * (K₀ * ε ^ (-max 1 (g / a))) := by gcongr
      _ = A * c₃ / (1 - t) * ε⁻¹ + c₃ * K₀ * ε ^ (-max 1 (g / a)) := by ring
      _ ≤ A * c₃ / (1 - t) * ε ^ (-max 1 (g / a)) + c₃ * K₀ * ε ^ (-max 1 (g / a)) := by
          gcongr
      _ = _ := by ring

/-- **MLQMC complexity when the total variations decay more slowly than the cost per point grows
(`b < g`), the real-analysis core** (Giles 2015, §2.7, p. 20: theoretical developments for MLQMC
show "that under certain conditions they lead to multilevel methods with a complexity which is
`O(ε^{−p})` with `p < 2`").  One dimension only: QMC error theory in `d` dimensions
(Koksma–Hlawka, low-discrepancy and Sobol points) is not formalised.  Let `a > 0`, `b < g` (no
sign conditions on `b` and `g`) and `c₁, c₂, c₃ > 0`: a bias `c₁ 2^{−aL}` at finest level `L`,
level-`ℓ` corrections whose randomly shifted lattice rule with `N_ℓ` points has root-mean-square
error `≤ c₂ 2^{−bℓ}/N_ℓ` (`latticeRule_randomShift` with total variation `V_ℓ ≤ c₂ 2^{−bℓ}`) and a
cost `c₃ 2^{gℓ}` per point.  There is `K > 0` such that for every `0 < ε < 1` there are `L` and
`N_ℓ ≥ 1` with `(c₁ 2^{−aL})² + ∑_{ℓ≤L} (c₂ 2^{−bℓ}/N_ℓ)² < ε²` and
`∑_{ℓ≤L} N_ℓ c₃ 2^{gℓ} ≤ K ε^{−p}`, `p = max(1 + (g − b)/a, g/a)`.  So `p = g/a` when `a ≤ b`, and
`p < 2` iff `g < 2a` and `g < a + b` (`mlqmc_complexity_lt_two`).  Proof: `L = levelL a c₁ (ε/2)`
and the allocation `N_ℓ ∝ (V_ℓ²/C_ℓ)^{1/3}` that minimises `∑ N_ℓ C_ℓ` subject to
`∑ V_ℓ²/N_ℓ² ≤ ε²/4`, namely `N_ℓ = ⌈A ε⁻¹ q^L 2^{−(2b+g)ℓ/3}⌉` with `q = 2^{(g−b)/3}` and
`A = 2c₂q²/(q² − 1)`: the main cost is `O(ε⁻¹ 2^{(g−b)L}) = O(ε^{−1−(g−b)/a})` and the rounding up
costs `O(ε^{−max(1, g/a)})` (`exists_sum_two_rpow_le`). -/
theorem mlqmc_complexity_core_of_lt {a b g c₁ c₂ c₃ : ℝ} (ha : 0 < a) (hbg : b < g)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N ℓ) ^ 2 < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          K * ε ^ (-max (1 + (g - b) / a) (g / a)) := by
  set q : ℝ := (2 : ℝ) ^ ((g - b) / 3) with hq
  set w : ℝ := (2 : ℝ) ^ (-((2 * b + g) / 3)) with hw
  have hq1 : 1 < q := Real.one_lt_rpow one_lt_two (by linarith)
  have hq0 : 0 < q := by linarith
  have hw0 : 0 < w := Real.rpow_pos_of_pos two_pos _
  have hq21 : 1 < q ^ 2 := by nlinarith
  have hq21' : 0 < q ^ 2 - 1 := by linarith
  have hq2 : q ^ 2 = (2 : ℝ) ^ (2 * (g - b) / 3) := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    congr 1
    push_cast
    ring
  have hB : ∀ ℓ : ℕ, (2 : ℝ) ^ (-(b * (ℓ : ℝ))) = w ^ ℓ * q ^ ℓ := fun ℓ => by
    rw [← mul_pow, hw, hq, ← Real.rpow_add two_pos, ← two_rpow_mul_nat]
    congr 1
    ring
  have hG : ∀ ℓ : ℕ, w ^ ℓ * (2 : ℝ) ^ (g * (ℓ : ℝ)) = (q ^ 2) ^ ℓ := fun ℓ => by
    rw [two_rpow_mul_nat, ← mul_pow, hq2, hw, ← Real.rpow_add two_pos]
    congr 2
    ring
  have hq3 : ∀ L : ℕ, q ^ L * (q ^ 2) ^ L = (2 : ℝ) ^ ((g - b) * (L : ℝ)) := fun L => by
    have h3 : q * q ^ 2 = (2 : ℝ) ^ (g - b) := by
      rw [hq2, hq, ← Real.rpow_add two_pos]
      congr 1
      ring
    rw [← mul_pow, h3, two_rpow_mul_nat]
  set A : ℝ := 2 * c₂ * q ^ 2 / (q ^ 2 - 1) with hA
  have hA0 : 0 < A := div_pos (by positivity) hq21'
  have hK1 := K1_pos (α := a) hc₁
  obtain ⟨K₀, hK₀, hround⟩ := exists_sum_two_rpow_le g ha hK1
  have hKpos : 0 < A * c₃ * (q ^ 2 / (q ^ 2 - 1)) * K1 a c₁ ^ ((g - b) / a) + c₃ * K₀ :=
    add_pos (mul_pos (mul_pos (mul_pos hA0 hc₃) (div_pos (by positivity) hq21'))
      (Real.rpow_pos_of_pos hK1 _)) (mul_pos hc₃ hK₀)
  refine ⟨_, hKpos, fun ε hε hε1 => ⟨levelL a c₁ (ε / 2),
    fun ℓ => ⌈A / ε * q ^ levelL a c₁ (ε / 2) * w ^ ℓ⌉₊,
    fun ℓ => Nat.ceil_pos.2 (by positivity), ?_, ?_⟩⟩
  · -- the mean square error
    set L := levelL a c₁ (ε / 2) with hL
    have hbias : (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 ≤ ε ^ 2 / 4 := by
      have hb := levelL_bias ha hc₁ (half_pos hε)
      calc _ ≤ (ε / 2) ^ 2 := by gcongr
        _ = ε ^ 2 / 4 := by ring
    have hterm : ∀ ℓ ∈ range (L + 1),
        (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈A / ε * q ^ L * w ^ ℓ⌉₊ : ℕ) : ℝ)) ^ 2 ≤
          (c₂ * ε / (A * q ^ L)) ^ 2 * (q ^ 2) ^ ℓ := by
      intro ℓ _
      have hN : A / ε * q ^ L * w ^ ℓ ≤ ((⌈A / ε * q ^ L * w ^ ℓ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have hpos : 0 < A / ε * q ^ L * w ^ ℓ := by positivity
      have h1 : c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈A / ε * q ^ L * w ^ ℓ⌉₊ : ℕ) : ℝ) ≤
          c₂ * ε / (A * q ^ L) * q ^ ℓ := by
        rw [hB, div_le_iff₀ (hpos.trans_le hN)]
        calc c₂ * (w ^ ℓ * q ^ ℓ) = c₂ * ε / (A * q ^ L) * q ^ ℓ * (A / ε * q ^ L * w ^ ℓ) := by
              field_simp
          _ ≤ c₂ * ε / (A * q ^ L) * q ^ ℓ * ((⌈A / ε * q ^ L * w ^ ℓ⌉₊ : ℕ) : ℝ) := by gcongr
      have h0 : 0 ≤ c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈A / ε * q ^ L * w ^ ℓ⌉₊ : ℕ) : ℝ) := by
        positivity
      calc _ ≤ (c₂ * ε / (A * q ^ L) * q ^ ℓ) ^ 2 := by gcongr
        _ = _ := by ring
    have hgeo := geom_sum_le_of_one_lt hq21 L
    have hvar : ∑ ℓ ∈ range (L + 1),
        (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈A / ε * q ^ L * w ^ ℓ⌉₊ : ℕ) : ℝ)) ^ 2 ≤
          ε ^ 2 / 4 := by
      calc _ ≤ ∑ ℓ ∈ range (L + 1), (c₂ * ε / (A * q ^ L)) ^ 2 * (q ^ 2) ^ ℓ :=
            sum_le_sum hterm
        _ = (c₂ * ε / (A * q ^ L)) ^ 2 * ∑ ℓ ∈ range (L + 1), (q ^ 2) ^ ℓ := by
            rw [mul_sum]
        _ ≤ (c₂ * ε / (A * q ^ L)) ^ 2 * ((q ^ 2) ^ L * (q ^ 2 / (q ^ 2 - 1))) := by gcongr
        _ = ε ^ 2 / 4 * ((q ^ 2 - 1) / q ^ 2) := by
            rw [hA]
            field_simp
            ring
        _ ≤ ε ^ 2 / 4 * 1 := by
            gcongr
            rw [div_le_one (by positivity)]
            linarith
        _ = ε ^ 2 / 4 := mul_one _
    nlinarith [sq_pos_of_pos hε]
  · -- the cost
    set L := levelL a c₁ (ε / 2) with hL
    have hL2 : (2 : ℝ) ^ (a * (L : ℝ)) ≤ K1 a c₁ / ε := two_rpow_levelL_half_le ha hc₁ hε hε1
    have hterm : ∀ ℓ ∈ range (L + 1),
        ((⌈A / ε * q ^ L * w ^ ℓ⌉₊ : ℕ) : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          A * c₃ / ε * q ^ L * (q ^ 2) ^ ℓ + c₃ * ((2 : ℝ) ^ g) ^ ℓ := by
      intro ℓ _
      have hN : ((⌈A / ε * q ^ L * w ^ ℓ⌉₊ : ℕ) : ℝ) ≤ A / ε * q ^ L * w ^ ℓ + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      calc _ ≤ (A / ε * q ^ L * w ^ ℓ + 1) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) := by gcongr
        _ = A * c₃ / ε * q ^ L * (w ^ ℓ * (2 : ℝ) ^ (g * (ℓ : ℝ))) +
            c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ)) := by ring
        _ = _ := by rw [hG, two_rpow_mul_nat]
    have hround' := hround ε hε hε1 L hL2
    have hgeo := geom_sum_le_of_one_lt hq21 L
    have h2L := two_rpow_L_le ha (by linarith : 0 ≤ g - b) hK1 hε hL2
    have hp1 : ε ^ (-(1 + (g - b) / a)) ≤ ε ^ (-max (1 + (g - b) / a) (g / a)) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1.le (neg_le_neg (le_max_left _ _))
    have hp2 : ε ^ (-max 1 (g / a)) ≤ ε ^ (-max (1 + (g - b) / a) (g / a)) := by
      have hgba : 0 ≤ (g - b) / a := div_nonneg (by linarith) ha.le
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (neg_le_neg (max_le
        ((le_add_of_nonneg_right hgba).trans (le_max_left _ _)) (le_max_right _ _)))
    have hcoef : 0 ≤ A * c₃ * (q ^ 2 / (q ^ 2 - 1)) * ε⁻¹ :=
      (mul_pos (mul_pos (mul_pos hA0 hc₃) (div_pos (by positivity) hq21'))
        (inv_pos.2 hε)).le
    have hcoef' : 0 ≤ A * c₃ * (q ^ 2 / (q ^ 2 - 1)) * K1 a c₁ ^ ((g - b) / a) :=
      (mul_pos (mul_pos (mul_pos hA0 hc₃) (div_pos (by positivity) hq21'))
        (Real.rpow_pos_of_pos hK1 _)).le
    calc _ ≤ ∑ ℓ ∈ range (L + 1), (A * c₃ / ε * q ^ L * (q ^ 2) ^ ℓ + c₃ * ((2 : ℝ) ^ g) ^ ℓ) :=
          sum_le_sum hterm
      _ = A * c₃ / ε * q ^ L * ∑ ℓ ∈ range (L + 1), (q ^ 2) ^ ℓ +
          c₃ * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ g) ^ ℓ := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ A * c₃ / ε * q ^ L * ((q ^ 2) ^ L * (q ^ 2 / (q ^ 2 - 1))) +
          c₃ * (K₀ * ε ^ (-max 1 (g / a))) := by gcongr
      _ = A * c₃ * (q ^ 2 / (q ^ 2 - 1)) * ε⁻¹ * (q ^ L * (q ^ 2) ^ L) +
          c₃ * K₀ * ε ^ (-max 1 (g / a)) := by ring
      _ = A * c₃ * (q ^ 2 / (q ^ 2 - 1)) * ε⁻¹ * (2 : ℝ) ^ ((g - b) * (L : ℝ)) +
          c₃ * K₀ * ε ^ (-max 1 (g / a)) := by rw [hq3]
      _ ≤ A * c₃ * (q ^ 2 / (q ^ 2 - 1)) * ε⁻¹ *
            (K1 a c₁ ^ ((g - b) / a) * ε ^ (-((g - b) / a))) +
          c₃ * K₀ * ε ^ (-max 1 (g / a)) := by
          gcongr
      _ = A * c₃ * (q ^ 2 / (q ^ 2 - 1)) * K1 a c₁ ^ ((g - b) / a) *
            ε ^ (-(1 + (g - b) / a)) + c₃ * K₀ * ε ^ (-max 1 (g / a)) := by
          rw [neg_add, Real.rpow_add hε, Real.rpow_neg_one]
          ring
      _ ≤ A * c₃ * (q ^ 2 / (q ^ 2 - 1)) * K1 a c₁ ^ ((g - b) / a) *
            ε ^ (-max (1 + (g - b) / a) (g / a)) +
          c₃ * K₀ * ε ^ (-max (1 + (g - b) / a) (g / a)) := by
          gcongr
      _ = _ := by ring

/-- **MLQMC complexity `O(ε^{−max(1, g/a)})` in one dimension, the real-analysis core** (Giles
2015, §2.7, p. 20: theoretical developments for MLQMC show "that under certain conditions they lead
to multilevel methods with a complexity which is `O(ε^{−p})` with `p < 2`").  One dimension only:
QMC error theory in `d` dimensions (Koksma–Hlawka, low-discrepancy and Sobol points) is not
formalised.  Let `a > 0` and `c₁, c₂, c₃ > 0`: a bias `c₁ 2^{−aL}` at finest level `L`, level-`ℓ`
corrections whose randomly shifted lattice rule with `N_ℓ` points has root-mean-square error
`≤ c₂ 2^{−bℓ}/N_ℓ` (`latticeRule_randomShift` with total variation `V_ℓ ≤ c₂ 2^{−bℓ}`) and a cost
`c₃ 2^{gℓ}` per point, where either `b > g`, or `a ≤ b` and `a < g` (no sign condition on `g`:
Giles' Theorem 1 assumes `γ > 0`, which is not needed here).  There is `K > 0` such that for every
`0 < ε < 1` there are `L` and `N_ℓ ≥ 1` with `(c₁ 2^{−aL})² + ∑_{ℓ≤L} (c₂ 2^{−bℓ}/N_ℓ)² < ε²` and
`∑_{ℓ≤L} N_ℓ c₃ 2^{gℓ} ≤ K ε^{−max(1, g/a)}`; the exponent `p = max(1, g/a)` is `< 2` iff
`g < 2a`.  Proof: for `b > g`, `L = levelL a c₁ (ε/2)` and `N_ℓ = ⌈A ε⁻¹ 2^{−(b+g)ℓ/2}⌉` with
`A = 2c₂/(1 − 2^{−(b−g)/2})`, main cost `O(ε⁻¹)` and rounding-up cost `O(ε^{−max(1, g/a)})`
(`exists_sum_two_rpow_le`); for `a ≤ b`, `a < g`, the bound `2^{−bℓ} ≤ 2^{−aℓ}` and
`mlqmc_complexity_core_of_lt` with `b = a`, exponent `max(1 + (g − a)/a, g/a) = g/a`.  In the
remaining regimes: for `b < g` and `b < a` the same method gives the exponent
`max(1 + (g − b)/a, g/a) > g/a` (`mlqmc_complexity_core_of_lt`); for `b = g ≤ a` the optimal
allocation gives `O(ε⁻¹ |log ε|^{3/2})`, which is not formalised (`mlqmc_complexity_core_of_lt`
with any `b' < b` gives `O(ε^{−1−(g−b')/a})`).  For comparison, Monte Carlo sampling of the same
corrections has variances `Var[f_ℓ(U)] ≤ V_ℓ² = O(2^{−2bℓ})`, so Giles' Theorem 1
(`mlmc_complexity_core`) applies with `β = 2b` and `γ = g` when `b, g > 0` and `a ≥ ½ min(2b, g)`
(its conditions `β, γ > 0` and `α ≥ ½ min(β, γ)`) and gives cost `O(ε⁻²)` when `2b > g` (in
particular for `b > g`); the gain `p < 2` over `p = 2` is real exactly when `g < 2a` (for `g = 2a`
both exponents are `2`).  The paper states no conditions; this is the one-dimensional case with
geometric decay of the total variations. -/
theorem mlqmc_complexity_core {a b g c₁ c₂ c₃ : ℝ} (ha : 0 < a) (hgb : g < b ∨ (a ≤ b ∧ a < g))
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N ℓ) ^ 2 < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          K * ε ^ (-max 1 (g / a)) := by
  rcases hgb with hgb | ⟨hab, hag⟩
  · exact mlqmc_core_of_gt ha hgb hc₁ hc₂ hc₃
  · obtain ⟨K, hK, h⟩ := mlqmc_complexity_core_of_lt (b := a) ha hag hc₁ hc₂ hc₃
    have hp : max (1 + (g - a) / a) (g / a) = max 1 (g / a) := by
      have e : 1 + (g - a) / a = g / a := by
        field_simp
        ring
      have h1 : 1 ≤ g / a := by
        rw [le_div_iff₀ ha]
        linarith
      rw [e, max_self, max_eq_right h1]
    refine ⟨K, hK, fun ε hε hε1 => ?_⟩
    obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
    refine ⟨L, N, hN, lt_of_le_of_lt ?_ hmse, by rw [← hp]; exact hcost⟩
    refine add_le_add le_rfl (sum_le_sum fun ℓ _ => ?_)
    have h2 := two_rpow_neg_mul_le hab ℓ
    gcongr

/-- **The mean square error of the one-dimensional MLQMC estimator.**  With independent shifts
`U_ℓ` uniform on `[0, 1]`, level corrections `f_ℓ` of bounded variation with total variation
`V_ℓ ≤ v_ℓ`, `N_ℓ ≥ 1` and bias `|∑_{ℓ≤L} ∫_0^1 f_ℓ − I| ≤ B`, the estimator
`Y = ∑_{ℓ≤L} N_ℓ⁻¹ ∑_{i<N_ℓ} f_ℓ((i + U_ℓ)/N_ℓ)` has `E[(Y − I)²] ≤ B² + ∑_{ℓ≤L} (v_ℓ/N_ℓ)²`
(`mse_eq_variance_add_sq_bias`, `IndepFun.variance_sum`, `latticeRule_randomShift`). -/
lemma mlqmc_mse_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : ℕ → Ω → ℝ}
    (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ (volume.restrict (Set.Icc 0 1)))
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → ℝ → ℝ}
    (hf : ∀ ℓ, BoundedVariationOn (f ℓ) (Set.Icc 0 1)) {L : ℕ} {N : ℕ → ℕ} (hN : ∀ ℓ, 0 < N ℓ)
    {I B : ℝ} {v : ℕ → ℝ} (hbias : |∑ ℓ ∈ range (L + 1), (∫ y in (0 : ℝ)..1, f ℓ y) - I| ≤ B)
    (hV : ∀ ℓ, (eVariationOn (f ℓ) (Set.Icc 0 1)).toReal ≤ v ℓ) :
    ∫ ω, (∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ ≤
      B ^ 2 + ∑ ℓ ∈ range (L + 1), (v ℓ / N ℓ) ^ 2 := by
  have := isProbabilityMeasure_of_uniform01 (hU 0)
  choose P Q hP hQ hPQ using fun ℓ => exists_monotone_sub_eqOn (hf ℓ)
  have hone := fun ℓ => latticeRule_randomShift (hU ℓ) (hf ℓ) (hN ℓ)
  have hL2 : ∀ ℓ, MemLp (fun ω => latticeRule (f ℓ) (N ℓ) (U ℓ ω)) 2 μ := fun ℓ => (hone ℓ).2.1
  have hae : ∀ ℓ, (fun ω => latticeRule (f ℓ) (N ℓ) (U ℓ ω)) =ᵐ[μ]
      fun ω => latticeRule (fun x => P ℓ x - Q ℓ x) (N ℓ) (U ℓ ω) := fun ℓ =>
    ((hU ℓ).quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)).mono
      fun ω h => latticeRule_congr (hPQ ℓ) (N ℓ) h
  have hpair : Set.Pairwise ↑(range (L + 1)) fun i j =>
      IndepFun (fun ω => latticeRule (f i) (N i) (U i ω))
        (fun ω => latticeRule (f j) (N j) (U j ω)) μ :=
    fun i _ j _ hij => ((hUind hij).comp (measurable_latticeRule (hP i) (hQ i) (N i))
      (measurable_latticeRule (hP j) (hQ j) (N j))).congr (hae i).symm (hae j).symm
  have hsumfun : (fun ω => ∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω)) =
      ∑ ℓ ∈ range (L + 1), fun ω => latticeRule (f ℓ) (N ℓ) (U ℓ ω) := by
    ext ω
    simp [Finset.sum_apply]
  have hY : MemLp (fun ω => ∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω)) 2 μ :=
    memLp_finsetSum _ fun ℓ _ => hL2 ℓ
  have hvar : variance (fun ω => ∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω)) μ ≤
      ∑ ℓ ∈ range (L + 1), (v ℓ / N ℓ) ^ 2 := by
    rw [hsumfun, IndepFun.variance_sum (fun ℓ _ => hL2 ℓ) hpair]
    refine sum_le_sum fun ℓ _ => (hone ℓ).2.2.2.2.trans ?_
    have hNℓ : (0 : ℝ) < N ℓ := Nat.cast_pos.2 (hN ℓ)
    gcongr
    exact hV ℓ
  have hmean : ∫ ω, ∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω) ∂μ =
      ∑ ℓ ∈ range (L + 1), ∫ y in (0 : ℝ)..1, f ℓ y := by
    rw [integral_finsetSum _ fun ℓ _ => (hL2 ℓ).integrable one_le_two]
    exact sum_congr rfl fun ℓ _ => (hone ℓ).2.2.1
  have hb : (∑ ℓ ∈ range (L + 1), (∫ y in (0 : ℝ)..1, f ℓ y) - I) ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hbias 2
  have hdec := mse_eq_variance_add_sq_bias hY I
  rw [hmean] at hdec
  calc ∫ ω, (∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ
      = variance (fun ω => ∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω)) μ +
        (∑ ℓ ∈ range (L + 1), (∫ y in (0 : ℝ)..1, f ℓ y) - I) ^ 2 := hdec
    _ ≤ ∑ ℓ ∈ range (L + 1), (v ℓ / N ℓ) ^ 2 + B ^ 2 := add_le_add hvar hb
    _ = _ := add_comm _ _

/-- From a real-analysis complexity bound to the MLQMC estimator: if the allocation `(L, N_ℓ)` of
`hcore` makes `(c₁ 2^{−aL})² + ∑_{ℓ≤L} (c₂ 2^{−bℓ}/N_ℓ)² < ε²` at cost `≤ K ε^{−p}`, the randomly
shifted MLQMC estimator with this allocation has mean square error `< ε²` at the same cost bound
(`mlqmc_mse_le`). -/
lemma mlqmc_of_core {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : ℕ → Ω → ℝ}
    (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ (volume.restrict (Set.Icc 0 1)))
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → ℝ → ℝ}
    (hf : ∀ ℓ, BoundedVariationOn (f ℓ) (Set.Icc 0 1)) {C : ℕ → ℝ} {I a b g c₁ c₂ c₃ p : ℝ}
    (hbias : ∀ L : ℕ, |∑ ℓ ∈ range (L + 1), (∫ y in (0 : ℝ)..1, f ℓ y) - I| ≤
      c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))))
    (hV : ∀ ℓ : ℕ, (eVariationOn (f ℓ) (Set.Icc 0 1)).toReal ≤ c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))))
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ)))
    (hcore : ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N ℓ) ^ 2 < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤ K * ε ^ (-p)) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      ∫ ω, (∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ < ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ K * ε ^ (-p) := by
  obtain ⟨K, hK, hcore⟩ := hcore
  refine ⟨K, hK, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := hcore ε hε hε1
  refine ⟨L, N, hN, (mlqmc_mse_le hU hUind hf hN (hbias L) hV).trans_lt hmse, ?_⟩
  calc ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ
      ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :=
        sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (hC ℓ) (Nat.cast_nonneg _)
    _ ≤ _ := hcost

/-- `y ≤ c x` with `x ≥ 0` gives `y ≤ max(c, 1) x`: the constants of the MLQMC theorems need not
be assumed positive. -/
lemma le_max_one_mul {x y c : ℝ} (hx : 0 ≤ x) (h : y ≤ c * x) : y ≤ max c 1 * x :=
  h.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) hx)

/-- **MLQMC with randomly shifted lattice rules in one dimension: mean square error `< ε²` at cost
`O(ε^{−max(1, g/a)})`** (Giles 2015, §2.7, p. 20: "under certain conditions they lead to multilevel
methods with a complexity which is `O(ε^{−p})` with `p < 2`"; §3.5, p. 26: MLQMC with "a random
shift (for rank-1 lattice rules)" and error "In the best cases … `O(N_ℓ⁻¹)` rather than the usual
`O(N_ℓ^{−1/2})`").  One dimension only: the level-`ℓ` correction is a function `f_ℓ` of one uniform
input `u ∈ [0, 1]` (for instance `P_ℓ − P_{ℓ−1}` computed from one uniform random number); QMC
error theory in `d` dimensions (Koksma–Hlawka, low-discrepancy and Sobol points), needed for the
paper's applications, is not formalised.  Assume
* each `f_ℓ` has bounded variation on `[0, 1]`, with total variation `V_ℓ ≤ c₂ 2^{−bℓ}`;
* the bias at finest level `L` is `|∑_{ℓ≤L} ∫_0^1 f_ℓ − I| ≤ c₁ 2^{−aL}` (`I = E[P]`, and
  `∑_{ℓ≤L} ∫_0^1 f_ℓ = E[P_L]` by telescoping);
* a point on level `ℓ` costs `C_ℓ ≤ c₃ 2^{gℓ}`, with `a > 0` and either `b > g`, or `a ≤ b` and
  `a < g` (no sign conditions on `g` or on the constants `c₁, c₂, c₃`);
* the shifts `U_0, U_1, …` (one per level) are pairwise independent and uniform on `[0, 1]`.
Then there is `K > 0` such that for every `0 < ε < 1` there are `L` and `N_ℓ ≥ 1` for which the
MLQMC estimator `Y = ∑_{ℓ≤L} N_ℓ⁻¹ ∑_{i<N_ℓ} f_ℓ((i + U_ℓ)/N_ℓ)` has `E[(Y − I)²] < ε²` and cost
`∑_{ℓ≤L} N_ℓ C_ℓ ≤ K ε^{−max(1, g/a)}`, so `p = max(1, g/a) < 2` whenever `g < 2a`
(`mlqmc_complexity_core`; `mlqmc_complexity_of_lt` treats `b < g`, `mlqmc_complexity_lt_two` the
paper's `p < 2`).  For comparison, Giles' Theorem 1 gives `O(ε⁻²)` for the same corrections
sampled by Monte Carlo when `b > g > 0` and `a ≥ g/2` (`β = 2b > γ = g > 0`, and its condition
`α ≥ ½ min(β, γ)`).  Each level uses one randomly shifted lattice; the `32` replicates of
Algorithm 2 (`latticeRule_replicates`) change only the constant. -/
theorem mlqmc_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : ℕ → Ω → ℝ}
    (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ (volume.restrict (Set.Icc 0 1)))
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → ℝ → ℝ}
    (hf : ∀ ℓ, BoundedVariationOn (f ℓ) (Set.Icc 0 1)) {C : ℕ → ℝ} {I a b g c₁ c₂ c₃ : ℝ}
    (ha : 0 < a) (hgb : g < b ∨ (a ≤ b ∧ a < g))
    (hbias : ∀ L : ℕ, |∑ ℓ ∈ range (L + 1), (∫ y in (0 : ℝ)..1, f ℓ y) - I| ≤
      c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))))
    (hV : ∀ ℓ : ℕ, (eVariationOn (f ℓ) (Set.Icc 0 1)).toReal ≤ c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))))
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      ∫ ω, (∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ < ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ K * ε ^ (-max 1 (g / a)) :=
  mlqmc_of_core hU hUind hf (fun L => le_max_one_mul (by positivity) (hbias L))
    (fun ℓ => le_max_one_mul (by positivity) (hV ℓ))
    (fun ℓ => le_max_one_mul (by positivity) (hC ℓ))
    (mlqmc_complexity_core ha hgb (lt_max_of_lt_right one_pos) (lt_max_of_lt_right one_pos)
      (lt_max_of_lt_right one_pos))

/-- **MLQMC with randomly shifted lattice rules in one dimension when `b < g`: cost
`O(ε^{−max(1 + (g − b)/a, g/a)})`** (Giles 2015, §2.7, p. 20: "under certain conditions they lead
to multilevel methods with a complexity which is `O(ε^{−p})` with `p < 2`").  One dimension only:
QMC error theory in `d` dimensions (Koksma–Hlawka, low-discrepancy and Sobol points) is not
formalised.  The setting of `mlqmc_complexity` (corrections `f_ℓ` of one uniform input with total
variation `V_ℓ ≤ c₂ 2^{−bℓ}`, bias `≤ c₁ 2^{−aL}`, cost per point `C_ℓ ≤ c₃ 2^{gℓ}`, pairwise
independent uniform shifts, `a > 0`, no sign conditions on `b`, `g` or the constants), now with
`b < g`.  There is `K > 0` such that for every `0 < ε < 1` there are `L` and `N_ℓ ≥ 1` for which the
MLQMC estimator `Y = ∑_{ℓ≤L} N_ℓ⁻¹ ∑_{i<N_ℓ} f_ℓ((i + U_ℓ)/N_ℓ)` has `E[(Y − I)²] < ε²` and cost
`∑_{ℓ≤L} N_ℓ C_ℓ ≤ K ε^{−p}`, `p = max(1 + (g − b)/a, g/a)` (`mlqmc_complexity_core_of_lt`, with the
allocation `N_ℓ ∝ (V_ℓ²/C_ℓ)^{1/3}`); `p < 2` iff `g < 2a` and `g < a + b`. -/
theorem mlqmc_complexity_of_lt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : ℕ → Ω → ℝ}
    (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ (volume.restrict (Set.Icc 0 1)))
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → ℝ → ℝ}
    (hf : ∀ ℓ, BoundedVariationOn (f ℓ) (Set.Icc 0 1)) {C : ℕ → ℝ} {I a b g c₁ c₂ c₃ : ℝ}
    (ha : 0 < a) (hbg : b < g)
    (hbias : ∀ L : ℕ, |∑ ℓ ∈ range (L + 1), (∫ y in (0 : ℝ)..1, f ℓ y) - I| ≤
      c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))))
    (hV : ∀ ℓ : ℕ, (eVariationOn (f ℓ) (Set.Icc 0 1)).toReal ≤ c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))))
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      ∫ ω, (∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ < ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ K * ε ^ (-max (1 + (g - b) / a) (g / a)) :=
  mlqmc_of_core hU hUind hf (fun L => le_max_one_mul (by positivity) (hbias L))
    (fun ℓ => le_max_one_mul (by positivity) (hV ℓ))
    (fun ℓ => le_max_one_mul (by positivity) (hC ℓ))
    (mlqmc_complexity_core_of_lt ha hbg (lt_max_of_lt_right one_pos) (lt_max_of_lt_right one_pos)
      (lt_max_of_lt_right one_pos))

/-- **MLQMC in one dimension has complexity `O(ε^{−p})` with `p < 2` whenever `g < 2a` and
`g < a + b`** (Giles 2015, §2.7, p. 20: "These theoretical developments are very encouraging,
showing that under certain conditions they lead to multilevel methods with a complexity which is
`O(ε^{−p})` with `p < 2`").  One dimension only: QMC error theory in `d` dimensions
(Koksma–Hlawka, low-discrepancy and Sobol points) is not formalised.  In the setting of
`mlqmc_complexity` (corrections `f_ℓ` of one uniform input with total variation
`V_ℓ ≤ c₂ 2^{−bℓ}`, bias `≤ c₁ 2^{−aL}`, cost per point `C_ℓ ≤ c₃ 2^{gℓ}`, pairwise independent
uniform shifts), assume only `a > 0`, `g < 2a` and `g < a + b`.  Then there are `p < 2` and `K > 0`
such that for every `0 < ε < 1` there are `L` and `N_ℓ ≥ 1` for which the MLQMC estimator
`Y = ∑_{ℓ≤L} N_ℓ⁻¹ ∑_{i<N_ℓ} f_ℓ((i + U_ℓ)/N_ℓ)` has `E[(Y − I)²] < ε²` at cost
`∑_{ℓ≤L} N_ℓ C_ℓ ≤ K ε^{−p}`.  Proof: since `V_ℓ ≤ c₂ 2^{−bℓ} ≤ c₂ 2^{−b'ℓ}` for
`b' = min(b, g − a/2) < g`, `mlqmc_complexity_of_lt` gives `p = max(1 + (g − b')/a, g/a)`, and
`g − b' < a`.  (Sharper exponents: `max(1, g/a)` when `b > g`, or `a ≤ b` and `a < g`
(`mlqmc_complexity`); `max(1 + (g − b)/a, g/a)` when `b < g` (`mlqmc_complexity_of_lt`).  If the
level errors and costs were exactly `V_ℓ/N_ℓ` and `c₃ 2^{gℓ}`, the two conditions would also be
necessary: `g ≥ 2a` makes the cost of one point per level `≍ ε^{−g/a}`, and `g ≥ a + b` (so
`b < g`) makes the optimally allocated main cost `≍ ε^{−1−(g−b)/a}`, with `1 + (g − b)/a ≥ 2`; this
is not formalised.) -/
theorem mlqmc_complexity_lt_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : ℕ → Ω → ℝ}
    (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ (volume.restrict (Set.Icc 0 1)))
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → ℝ → ℝ}
    (hf : ∀ ℓ, BoundedVariationOn (f ℓ) (Set.Icc 0 1)) {C : ℕ → ℝ} {I a b g c₁ c₂ c₃ : ℝ}
    (ha : 0 < a) (h2a : g < 2 * a) (hgab : g < a + b)
    (hbias : ∀ L : ℕ, |∑ ℓ ∈ range (L + 1), (∫ y in (0 : ℝ)..1, f ℓ y) - I| ≤
      c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))))
    (hV : ∀ ℓ : ℕ, (eVariationOn (f ℓ) (Set.Icc 0 1)).toReal ≤ c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))))
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :
    ∃ p : ℝ, p < 2 ∧ ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ),
      (∀ ℓ, 0 < N ℓ) ∧
      ∫ ω, (∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ < ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ K * ε ^ (-p) := by
  have hga : g / a < 2 := by
    rw [div_lt_iff₀ ha]
    linarith
  have hb'g : min b (g - a / 2) < g := (min_le_right _ _).trans_lt (by linarith)
  have hgb' : (g - min b (g - a / 2)) / a < 1 := by
    rw [div_lt_one ha]
    have : g - a < min b (g - a / 2) := lt_min (by linarith) (by linarith)
    linarith
  have hV' : ∀ ℓ : ℕ, (eVariationOn (f ℓ) (Set.Icc 0 1)).toReal ≤
      max c₂ 1 * (2 : ℝ) ^ (-(min b (g - a / 2) * (ℓ : ℝ))) := fun ℓ =>
    (le_max_one_mul (by positivity) (hV ℓ)).trans (mul_le_mul_of_nonneg_left
      (two_rpow_neg_mul_le (min_le_left _ _) ℓ) (zero_le_one.trans (le_max_right _ _)))
  exact ⟨max (1 + (g - min b (g - a / 2)) / a) (g / a), max_lt (by linarith) hga,
    mlqmc_complexity_of_lt hU hUind hf ha hb'g hbias hV' hC⟩

end MLMC
