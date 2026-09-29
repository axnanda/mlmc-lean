import MlmcLean.StandardEstimator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.Integral

/-!
# Randomised QMC by a random shift of the points (Giles 2015, §3.5)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §3.5 "MLQMC
algorithm", pp. 26–27: "Using just one set of `N_ℓ` points gives good accuracy, but no confidence
interval.  To regain a confidence interval one uses randomised QMC in which the set of points is
gives [sic] a random shift (for rank-1 lattice rules) or a digital scrambling (for Sobol sequences).
Using 32 sets of points, each collectively randomised, yields 32 set averages for the quantity of
interest, `Y_ℓ`, and from these 32 random independent values the variance of their average, `V_ℓ`,
can be estimated in the usual way."

The integration region is the unit torus `𝕋^d = (ℝ/ℤ)^d` (Mathlib's `UnitAddTorus d`): the unit
cube with addition modulo `1` in each coordinate.  Its measure `volume` is the product of the Haar
probability measures of the circles, so it is the uniform distribution and it is invariant under
translations.  A QMC rule uses points `x_0, …, x_{N−1}` of `𝕋^d` (for a rank-1 lattice rule,
`x_i = i z/N mod 1` for an integer generating vector `z`); the random shift replaces them by
`x_i + U` with `U` uniform on `𝕋^d`.

* `shiftedQMC_unbiased`: for any points and any integrable `f`, every shifted point `x_i + U` is
  uniform on `𝕋^d`, so the shifted average `N⁻¹ ∑_i f(x_i + U)` has mean `∫_{𝕋^d} f`.
* `randomShift_replicates`: with `R` independent shifts (the paper's `R = 32`) the `R` set averages
  are independent and identically distributed with mean `∫ f`; their average is unbiased with
  variance `V₁/R`, `V₁` the variance of one set average; and the usual estimate
  `(R(R − 1))⁻¹ ∑_r (Y_r − Ȳ)²` of this variance is unbiased (`integral_sum_sq_sub_mean`).

The digital scrambling of Sobol sequences is not formalised.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### The usual variance estimate -/

section sampleVariance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The usual variance estimate is unbiased** (Bessel's correction, the "usual way" of Giles 2015,
§3.5, p. 27).  For `R ≥ 1` pairwise independent square-integrable random variables
`Y_0, …, Y_{R−1}` with a common mean `m` and a common variance `v`, and their average
`Ȳ = R⁻¹ ∑_{r<R} Y_r`, `E[∑_{r<R} (Y_r − Ȳ)²] = (R − 1) v`. -/
lemma integral_sum_sq_sub_mean (Y : ℕ → Ω → ℝ) {R : ℕ} (hR : 0 < R) {m v : ℝ}
    (hY : ∀ r, MemLp (Y r) 2 μ) (hm : ∀ r, ∫ ω, Y r ω ∂μ = m) (hv : ∀ r, variance (Y r) μ = v)
    (hind : Set.Pairwise ↑(range R) fun i j => IndepFun (Y i) (Y j) μ) :
    ∫ ω, ∑ r ∈ range R, (Y r ω - (R : ℝ)⁻¹ * ∑ s ∈ range R, Y s ω) ^ 2 ∂μ = (R - 1) * v := by
  have hR' : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hR.ne'
  -- the average `Ȳ`: square-integrable, mean `m`, variance `v/R`
  have hYbar : MemLp (fun ω => (R : ℝ)⁻¹ * ∑ s ∈ range R, Y s ω) 2 μ :=
    (memLp_finsetSum _ fun s _ => hY s).const_mul _
  have hmean : ∫ ω, (R : ℝ)⁻¹ * ∑ s ∈ range R, Y s ω ∂μ = m := by
    rw [integral_const_mul, integral_finsetSum _ fun s _ => (hY s).integrable one_le_two]
    simp only [hm, sum_const, card_range, nsmul_eq_mul]
    field_simp
  have hvar : variance (fun ω => (R : ℝ)⁻¹ * ∑ s ∈ range R, Y s ω) μ = v / R :=
    variance_sample_mean Y R hR v hY hv hind
  -- second moments
  have hsq : ∀ {X : Ω → ℝ}, MemLp X 2 μ → ∫ ω, X ω ^ 2 ∂μ = variance X μ + (∫ ω, X ω ∂μ) ^ 2 :=
    fun {X} hX => by
      rw [variance_eq_sub hX]
      simp only [Pi.pow_apply]
      ring
  -- `∑_r (Y_r − Ȳ)² = ∑_r Y_r² − R Ȳ²`
  have hpt : ∀ ω, ∑ r ∈ range R, (Y r ω - (R : ℝ)⁻¹ * ∑ s ∈ range R, Y s ω) ^ 2 =
      ∑ r ∈ range R, Y r ω ^ 2 - R * ((R : ℝ)⁻¹ * ∑ s ∈ range R, Y s ω) ^ 2 := by
    intro ω
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      ← sum_mul, ← mul_sum]
    field_simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub (integrable_finsetSum _ fun r _ => (hY r).integrable_sq)
      (hYbar.integrable_sq.const_mul _),
    integral_finsetSum _ fun r _ => (hY r).integrable_sq, integral_const_mul, hsq hYbar, hvar,
    hmean]
  simp only [fun r => hsq (hY r), hv, hm, sum_const, card_range, nsmul_eq_mul]
  field_simp
  ring

end sampleVariance

/-! ### The random shift on the torus -/

/-- **The randomly shifted QMC average** (Giles 2015, §3.5, p. 26): `N⁻¹ ∑_{i<N} f(x_i + u)`, the
average of `f` over the points `x_0, …, x_{N−1}` of the torus `𝕋^d = (ℝ/ℤ)^d`, all shifted by the
same `u ∈ 𝕋^d` (addition modulo `1` in each coordinate). -/
noncomputable def shiftedQMC {d : Type*} (f : UnitAddTorus d → ℝ) (x : ℕ → UnitAddTorus d)
    (N : ℕ) (u : UnitAddTorus d) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ range N, f (x i + u)

variable {d : Type*} [Fintype d]

omit [Fintype d] in
/-- A shifted QMC average of a measurable `f` is a measurable function of the shift. -/
lemma measurable_shiftedQMC {f : UnitAddTorus d → ℝ} (hf : Measurable f)
    (x : ℕ → UnitAddTorus d) (N : ℕ) : Measurable (shiftedQMC f x N) :=
  (Finset.measurable_sum _ fun i _ => hf.comp (measurable_const_add (x i))).const_mul _

/-- A shifted QMC average of a square-integrable `f` is square-integrable on `𝕋^d`. -/
lemma memLp_shiftedQMC {f : UnitAddTorus d → ℝ} (hf : MemLp f 2 volume)
    (x : ℕ → UnitAddTorus d) (N : ℕ) : MemLp (shiftedQMC f x N) 2 volume :=
  (memLp_finsetSum _ fun i _ =>
    hf.comp_measurePreserving (measurePreserving_add_left volume (x i))).const_mul _

/-- **A random shift makes a QMC rule unbiased** (Giles 2015, §3.5, p. 26: "To regain a confidence
interval one uses randomised QMC in which the set of points is gives [sic] a random shift (for
rank-1 lattice rules)").  Let `x_0, …, x_{N−1}` be any `N ≥ 1` points of the torus `𝕋^d` (for
instance a rank-1 lattice) and let the shift `U` be uniformly distributed on `𝕋^d` (its law is the
Haar probability measure `volume`).  Then every shifted point `x_i + U` is again uniform on
`𝕋^d`, and for every integrable `f` the randomly shifted average `N⁻¹ ∑_i f(x_i + U)` is integrable
with mean `∫_{𝕋^d} f`. -/
theorem shiftedQMC_unbiased {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Ω → UnitAddTorus d} (hU : MeasurePreserving U μ volume) (x : ℕ → UnitAddTorus d)
    {f : UnitAddTorus d → ℝ} (hf : Integrable f volume) {N : ℕ} (hN : 0 < N) :
    (∀ i, MeasurePreserving (fun ω => x i + U ω) μ volume) ∧
      Integrable (fun ω => shiftedQMC f x N (U ω)) μ ∧
      ∫ ω, shiftedQMC f x N (U ω) ∂μ = ∫ y, f y := by
  have hadd : ∀ i, MeasurePreserving (fun u : UnitAddTorus d => x i + u) volume volume :=
    fun i => measurePreserving_add_left volume (x i)
  have hint : ∀ i, Integrable (fun u => f (x i + u)) volume := fun i =>
    ((hadd i).integrable_comp hf.aestronglyMeasurable).2 hf
  have hQ : Integrable (shiftedQMC f x N) volume :=
    (integrable_finsetSum _ fun i _ => hint i).const_mul _
  refine ⟨fun i => (hadd i).comp hU, (hU.integrable_comp hQ.aestronglyMeasurable).2 hQ, ?_⟩
  rw [integral_comp_of_measurePreserving hU hQ.aestronglyMeasurable]
  simp only [shiftedQMC]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]
  simp only [integral_add_left_eq_self, sum_const, card_range, nsmul_eq_mul]
  field_simp

/-- **Independent random shifts: `32` independent unbiased values and the variance of their
average** (Giles 2015, §3.5, pp. 26–27: "Using 32 sets of points, each collectively randomised,
yields 32 set averages for the quantity of interest, `Y_ℓ`, and from these 32 random independent
values the variance of their average, `V_ℓ`, can be estimated in the usual way").  Let
`U_0, U_1, …` be independent shifts, each uniform on `𝕋^d`, let `f` be measurable and
square-integrable, and let `x_0, …, x_{N−1}` be any `N ≥ 1` points.  With `R ≥ 1` replicates (the
paper's `R = 32`), the set averages `Y_r = N⁻¹ ∑_i f(x_i + U_r)`
* are independent and identically distributed, each with mean `∫_{𝕋^d} f`;
* have an unbiased average `Ȳ = R⁻¹ ∑_{r<R} Y_r`, `E[Ȳ] = ∫ f`, with variance `V[Ȳ] = V₁/R`,
  where `V₁` is the variance of one set average;
* and, for `R ≥ 2`, the usual estimate `(R(R − 1))⁻¹ ∑_{r<R} (Y_r − Ȳ)²` of `V[Ȳ]` is unbiased.
-/
theorem randomShift_replicates {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {U : ℕ → Ω → UnitAddTorus d}
    (hU : ∀ r, MeasurePreserving (U r) μ volume) (hUind : iIndepFun U μ)
    (x : ℕ → UnitAddTorus d) {f : UnitAddTorus d → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) {N R : ℕ} (hN : 0 < N) (hR : 0 < R) :
    iIndepFun (fun r ω => shiftedQMC f x N (U r ω)) μ ∧
      (∀ r, μ.map (fun ω => shiftedQMC f x N (U r ω)) = volume.map (shiftedQMC f x N)) ∧
      (∀ r, ∫ ω, shiftedQMC f x N (U r ω) ∂μ = ∫ y, f y) ∧
      ∫ ω, (R : ℝ)⁻¹ * ∑ r ∈ range R, shiftedQMC f x N (U r ω) ∂μ = ∫ y, f y ∧
      variance (fun ω => (R : ℝ)⁻¹ * ∑ r ∈ range R, shiftedQMC f x N (U r ω)) μ =
        variance (shiftedQMC f x N) volume / R ∧
      (2 ≤ R → ∫ ω, ((R : ℝ) * (R - 1))⁻¹ * ∑ r ∈ range R, (shiftedQMC f x N (U r ω) -
          (R : ℝ)⁻¹ * ∑ s ∈ range R, shiftedQMC f x N (U s ω)) ^ 2 ∂μ =
        variance (shiftedQMC f x N) volume / R) := by
  have hQm := measurable_shiftedQMC hfm x N
  have hQ2 := memLp_shiftedQMC hf x N
  have hYind : iIndepFun (fun r ω => shiftedQMC f x N (U r ω)) μ :=
    hUind.comp (fun _ => shiftedQMC f x N) (fun _ => hQm)
  have hY2 : ∀ r, MemLp (fun ω => shiftedQMC f x N (U r ω)) 2 μ := fun r =>
    hQ2.comp_measurePreserving (hU r)
  have hmean : ∀ r, ∫ ω, shiftedQMC f x N (U r ω) ∂μ = ∫ y, f y := fun r =>
    (shiftedQMC_unbiased (hU r) x (hf.integrable one_le_two) hN).2.2
  have hvar : ∀ r, variance (fun ω => shiftedQMC f x N (U r ω)) μ =
      variance (shiftedQMC f x N) volume := fun r =>
    (hU r).variance_fun_comp hQm.aemeasurable
  have hpair : Set.Pairwise ↑(range R) fun i j =>
      IndepFun (fun ω => shiftedQMC f x N (U i ω)) (fun ω => shiftedQMC f x N (U j ω)) μ :=
    fun i _ j _ hij => hYind.indepFun hij
  have hR' : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hR.ne'
  refine ⟨hYind, fun r => ?_, hmean, ?_, variance_sample_mean _ R hR _ hY2 hvar hpair,
    fun hR2 => ?_⟩
  · rw [← (hU r).map_eq, Measure.map_map hQm (hU r).measurable]
    rfl
  · rw [integral_const_mul, integral_finsetSum _ fun r _ => (hY2 r).integrable one_le_two]
    simp only [hmean, sum_const, card_range, nsmul_eq_mul]
    field_simp
  · have hR1 : (R : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ R := by exact_mod_cast hR2
      linarith
    rw [integral_const_mul, integral_sum_sq_sub_mean _ hR hY2 hmean hvar hpair]
    field_simp

end MLMC
