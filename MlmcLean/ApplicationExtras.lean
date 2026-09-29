import MlmcLean.EulerMaruyama
import MlmcLean.RoundingError
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Variance

/-!
# Further applications (Giles 2015, §6.2, §7.1, §7.3, §10.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §6.2 "More
general processes" (pp. 47–48), §7.1 "Two simple examples" (pp. 49–51), §7.3 "Parabolic SPDE"
(pp. 53–54) and §10.2 "Variable precision arithmetic" (p. 62).

* **§6.2, Lévy processes** (p. 48: "the increments of the driving Lévy process for the coarse
  path can be obtained trivially by summing the increments for the fine path").  If the increments
  over one fine step have the law `ν` and those over two fine steps the law `ν ∗ ν` (a Lévy
  process), then summing pairs of independent fine increments, `z ↦ (z_{2k} + z_{2k+1})_k`, maps
  `ν^{⊗ℕ}` to `(ν ∗ ν)^{⊗ℕ}` (`measurePreserving_levyPairSum`; `measurePreserving_pairAvg` of
  `MlmcLean.EulerMaruyama` is the normalised Brownian case).  The coarse path is the fine path at
  the coarse times (`levyPath_levyPairSum`) and has the law of the path on the level below
  (`map_levyPath_levyPairSum`), so (2.4) holds for every functional of the increments
  (`integral_levyCoarse`) and the expectations telescope (`levy_telescoping`).  Brownian motion
  and the Poisson process satisfy the hypothesis (`gaussian_increments_conv`,
  `poisson_increments_conv`).
* **§6.2, random terminal times** (p. 48: "by using multiple shorter random periods it is
  possible, because of the Central Limit Theorem, to get closer to a desired fixed terminal
  time").  The sum `τ_n` of `n` independent exponential periods of rate `n/T` has mean `T` and
  variance `T²/n`, so it concentrates at `T` (`sum_exponential_periods`), and
  `(√n/T)(τ_n − T) → N(0, 1)` in distribution (`exponential_periods_clt`).
* **§7.1, finite elements** (p. 49: "A simple second order central difference approximation is
  used (equivalent to a finite element approximation with a 1-point quadrature)").  For hat
  functions on a uniform mesh, with the midpoint rule on every element, the stiffness row of node
  `j` is `h` times the conservative central difference
  `−(c_{j+½}(u_{j+1} − u_j) − c_{j−½}(u_j − u_{j−1}))/h²` and the load is `h (f_{j−½} + f_{j+½})/2`,
  i.e. `h f` for the constant forcing of the example (`fe_eq_centralDiff`).
* **§7.1, the elliptic example** (p. 49: "there is a constant `K` such that `|P − P_ℓ| < K h_ℓ²`
  and therefore we have `α = 2`, `β = 4`").  Since the forcing is `−50 Z²` with `Z` Gaussian, the
  error is `Z²` times the error of the problem with the forcing `−50`, and no deterministic `K`
  exists (`not_ae_abs_gaussian_sq_mul_le`).  A random `K` with `E[K²] < ∞` suffices:
  `|E[P_ℓ − P]| ≤ E[K] h_ℓ²` and `V[P_{ℓ+1} − P_ℓ] ≤ E[(P_{ℓ+1} − P_ℓ)²] ≤ 25 E[K²] h_{ℓ+1}⁴`
  (`elliptic_rates_random`, from `rates_of_pathwise_random`).
* **§7.3, the credit SPDE** `dp = −μ p_x dt + ½ p_xx dt − √ρ p_x dM` (pp. 53–54).  One Milstein
  step in time, `p + A p k + B p ΔM + ½ B(B p)(ΔM² − k)` with `B = −√ρ ∂_x`, `B² = ρ ∂_xx` and
  `ΔM = √k Z`, is `p − (μk + √(ρk) Z) p_x + ((1 − ρ)k + ρk Z²)/2 p_xx` (`spdeMilsteinStep_eq`),
  and the printed fully discrete scheme is exactly this step with `p_x`, `p_xx` replaced by the
  central differences (`spdeScheme_eq_milstein`).  The paper writes "`√h Z_n`" for the Brownian
  increment where `√k Z_n` is meant (`h` is the mesh width, `k` the time step).
* **§10.2, variable precision** (p. 62: "The Brownian path being generated for level `ℓ` is then
  exactly the same, regardless of whether it is the finer or coarser of the two levels being
  simulated for a particular multilevel correction.  Hence, the telescoping sum will be
  respected").  The Brownian-bridge construction `bbPath` refines level `ℓ` by midpoints
  (`bbPath_nested`) and its level-`ℓ` values use only the first `2^ℓ` inputs (`bbPath_congr`).
  So the level-`ℓ` path computed at level-`ℓ` precision from the random integers of a
  level-`(ℓ + 1)` sample is the one computed from their first `2^ℓ` (`vpPath_castLE`), (2.4)
  holds (`integral_vpCoarse`) and the expectations telescope (`vp_telescoping`); with the same
  arithmetic on all levels the coarse path is the fine path at the even points and the
  telescoping is pathwise (`bb_telescoping`).  By contrast, rounding the fine increments to `B_ℓ`
  bits and summing them (with the truncation to `B_{ℓ−1}` bits before or after the summation)
  does not reproduce the level-`(ℓ − 1)` increment (`roundFixed_sum_inconsistent`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MLMC

/-! ### §6.2: Lévy increments summed over pairs of fine steps -/

section levy

/-- The coarse increments of a Lévy-driven path (Giles 2015, §6.2, p. 48): the increment over a
coarse step is the sum of the increments over the two fine steps it contains,
`z ↦ (z_{2k} + z_{2k+1})_k`. -/
def levyPairSum {M : Type*} [Add M] (z : ℕ → M) (k : ℕ) : M := z (2 * k) + z (2 * k + 1)

/-- The values of a process at the grid points `t_n`, `L_n = z_0 + ⋯ + z_{n−1}`, built from its
increments `z_i` over the steps (Giles 2015, §6.2). -/
def levyPath {M : Type*} [AddCommMonoid M] (z : ℕ → M) (n : ℕ) : M := ∑ i ∈ range n, z i

/-- **The coarse path is the fine path at the coarse times** (Giles 2015, §6.2, p. 48: "the
increments of the driving Lévy process for the coarse path can be obtained trivially by summing
the increments for the fine path"): `L^c_m = L_{2m}`. -/
theorem levyPath_levyPairSum {M : Type*} [AddCommMonoid M] (z : ℕ → M) (m : ℕ) :
    levyPath (levyPairSum z) m = levyPath z (2 * m) := by
  induction m with
  | zero => simp [levyPath]
  | succ m ih =>
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    simp only [levyPath] at ih ⊢
    rw [sum_range_succ, ih, e, sum_range_succ, sum_range_succ, levyPairSum, add_assoc]

variable {M : Type*} [AddMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M]

/-- The sum of the two coordinates of `ν^{⊗2}` has the law `ν ∗ ν`. -/
lemma map_add_infinitePi_fin_two (ν : Measure M) [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : Fin 2 => ν).map (fun y => y 0 + y 1) = ν ∗ ν := by
  rw [Measure.infinitePi_eq_pi]
  have e : (fun y : Fin 2 → M => y 0 + y 1) =
      (fun p : M × M => p.1 + p.2) ∘ MeasurableEquiv.finTwoArrow := rfl
  rw [e, ← Measure.map_map measurable_add MeasurableEquiv.finTwoArrow.measurable,
    (measurePreserving_finTwoArrow ν).map_eq]
  rfl

/-- **Summed fine increments are independent coarse increments** (Giles 2015, §6.2, p. 48: the
increments of a Lévy process are simulated "over a set of uniform timesteps …, in exactly the same
way as one simulates Brownian increments", and "the increments of the driving Lévy process for the
coarse path can be obtained trivially by summing the increments for the fine path").  If the fine
increments are independent with law `ν`, the summed increments `(z_{2k} + z_{2k+1})_k` are
independent with law `ν ∗ ν`: the map preserves `ν^{⊗ℕ} → (ν ∗ ν)^{⊗ℕ}`.  This generalises
`measurePreserving_pairAvg` (the normalised Gaussian case `(Z_{2k} + Z_{2k+1})/√2`) to any
increment law on any measurable additive monoid (`ℝ`, `ℝ^d`, `ℕ`, …). -/
theorem measurePreserving_levyPairSum (ν : Measure M) [IsProbabilityMeasure ν] :
    MeasurePreserving levyPairSum (Measure.infinitePi fun _ : ℕ => ν)
      (Measure.infinitePi fun _ : ℕ => ν ∗ ν) := by
  have hf : Function.Injective (fun p : ℕ × Fin 2 => 2 * p.1 + (p.2 : ℕ)) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    change 2 * a + (i : ℕ) = 2 * b + (j : ℕ) at h
    have hi := i.isLt
    have hj := j.isLt
    obtain rfl : a = b := by omega
    obtain rfl : i = j := Fin.ext (by omega)
    rfl
  -- reindex the coordinates by the pairs `(k, i) ↦ 2k + i`
  have m1 : MeasurePreserving (fun (z : ℕ → M) (p : ℕ × Fin 2) => z (2 * p.1 + (p.2 : ℕ)))
      (Measure.infinitePi fun _ : ℕ => ν) (Measure.infinitePi fun _ : ℕ × Fin 2 => ν) :=
    ⟨measurable_pi_lambda _ fun p => measurable_pi_apply _,
      Measure.map_infinitePi_infinitePi_of_inj hf⟩
  -- curry: a sequence of independent pairs
  have m2 : MeasurePreserving (MeasurableEquiv.curry ℕ (Fin 2) M)
      (Measure.infinitePi fun _ : ℕ × Fin 2 => ν)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Fin 2 => ν) :=
    ⟨(MeasurableEquiv.curry ℕ (Fin 2) M).measurable,
      Measure.infinitePi_map_curry (fun _ _ => ν)⟩
  -- map each pair to its sum
  have m3 : MeasurePreserving (fun (x : ℕ → Fin 2 → M) (k : ℕ) => x k 0 + x k 1)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Fin 2 => ν)
      (Measure.infinitePi fun _ : ℕ => ν ∗ ν) := by
    refine ⟨measurable_pi_lambda _ fun k => ?_, ?_⟩
    · have h0 : Measurable fun x : ℕ → Fin 2 → M => x k 0 := (measurable_pi_apply k).eval
      have h1 : Measurable fun x : ℕ → Fin 2 → M => x k 1 := (measurable_pi_apply k).eval
      exact h0.add h1
    · refine (Measure.infinitePi_map_pi _ (f := fun _ (y : Fin 2 → M) => y 0 + y 1)
        (fun _ => (measurable_pi_apply 0).add (measurable_pi_apply 1))).trans ?_
      simp only [map_add_infinitePi_fin_two]
  have h := (m3.comp m2).comp m1
  have e : ((fun (x : ℕ → Fin 2 → M) (k : ℕ) => x k 0 + x k 1) ∘
      (MeasurableEquiv.curry ℕ (Fin 2) M)) ∘
      (fun (z : ℕ → M) (p : ℕ × Fin 2) => z (2 * p.1 + (p.2 : ℕ))) = levyPairSum := by
    funext z k
    simp [levyPairSum, MeasurableEquiv.coe_curry, Function.curry]
  rwa [e] at h

/-- `measurePreserving_levyPairSum` with the coarse law `ν₂ = ν ∗ ν` given by a hypothesis. -/
lemma measurePreserving_levyPairSum' {ν ν₂ : Measure M} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν₂] (h : ν ∗ ν = ν₂) :
    MeasurePreserving levyPairSum (Measure.infinitePi fun _ : ℕ => ν)
      (Measure.infinitePi fun _ : ℕ => ν₂) := by
  subst h
  exact measurePreserving_levyPairSum ν

/-- **(2.4) for Lévy-driven paths** (Giles 2015, §2.1, (2.4) "`E[P^f_ℓ] = E[P^c_ℓ]`", and §6.2,
p. 48).  Let the increments of a level-`(ℓ + 1)` sample be independent with law `ν`, and those of
a level-`ℓ` sample independent with law `ν₂ = ν ∗ ν` (the increment over a coarse step, two fine
steps long).  For any functional `F` of the increments (a payoff of an Euler scheme driven by
them, say), the coarse approximation of a level-`(ℓ + 1)` sample, `F` of the summed increments,
has the expectation of the fine approximation `F` of a level-`ℓ` sample. -/
theorem integral_levyCoarse {ν ν₂ : Measure M} [IsProbabilityMeasure ν] [IsProbabilityMeasure ν₂]
    (h : ν ∗ ν = ν₂) {F : (ℕ → M) → ℝ}
    (hF : AEStronglyMeasurable F (Measure.infinitePi fun _ : ℕ => ν₂)) :
    ∫ z, F (levyPairSum z) ∂(Measure.infinitePi fun _ : ℕ => ν) =
      ∫ z, F z ∂(Measure.infinitePi fun _ : ℕ => ν₂) :=
  integral_comp_of_measurePreserving (measurePreserving_levyPairSum' h) hF

/-- **The telescoping sum for Lévy-driven paths** (Giles 2015, §1.3 and (2.4), with §6.2, p. 48:
summing the fine increments "to achieve a perfect coupling between the coarse and fine path
simulations").  With level-`ℓ` increments independent of law `ν_ℓ`, `ν_{ℓ+1} ∗ ν_{ℓ+1} = ν_ℓ`, fine
payoffs `P^f_ℓ = F_ℓ(z)` and coarse payoffs `P^c_ℓ = F_ℓ((z_{2k} + z_{2k+1})_k)` computed on the
level-`(ℓ + 1)` sample, integrable `F_ℓ`:
`E[P^f_0] + ∑_{ℓ<L} E[P^f_{ℓ+1} − P^c_ℓ] = E[P^f_L]`. -/
theorem levy_telescoping (ν : ℕ → Measure M) [∀ ℓ, IsProbabilityMeasure (ν ℓ)]
    (hν : ∀ ℓ, ν (ℓ + 1) ∗ ν (ℓ + 1) = ν ℓ) (F : ℕ → (ℕ → M) → ℝ)
    (hF : ∀ ℓ, Integrable (F ℓ) (Measure.infinitePi fun _ : ℕ => ν ℓ)) (L : ℕ) :
    ∫ z, F 0 z ∂(Measure.infinitePi fun _ : ℕ => ν 0) +
      ∑ ℓ ∈ range L, ∫ z, (F (ℓ + 1) z - F ℓ (levyPairSum z))
        ∂(Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) =
      ∫ z, F L z ∂(Measure.infinitePi fun _ : ℕ => ν L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hc : Integrable (fun z => F L (levyPairSum z))
        (Measure.infinitePi fun _ : ℕ => ν (L + 1)) :=
      ((measurePreserving_levyPairSum' (hν L)).integrable_comp (hF L).aestronglyMeasurable).2
        (hF L)
    rw [sum_range_succ, ← add_assoc, ih, integral_sub (hF (L + 1)) hc,
      integral_levyCoarse (hν L) (hF L).aestronglyMeasurable]
    ring

/-- **Brownian increments** satisfy the hypothesis of `levy_telescoping` (Giles 2015, §6.2: "in
exactly the same way as one simulates Brownian increments"): with `h_ℓ = T 2^{−ℓ}`,
`N(0, h_{ℓ+1}) ∗ N(0, h_{ℓ+1}) = N(0, h_ℓ)`. -/
lemma gaussian_increments_conv (T : ℝ≥0) (ℓ : ℕ) :
    gaussianReal 0 (T / 2 ^ (ℓ + 1)) ∗ gaussianReal 0 (T / 2 ^ (ℓ + 1)) =
      gaussianReal 0 (T / 2 ^ ℓ) := by
  rw [gaussianReal_conv_gaussianReal, add_zero, pow_succ, ← div_div, add_halves]

/-- **Poisson increments** satisfy the hypothesis of `levy_telescoping` (Giles 2015, §6.2, with
values in `ℕ`): for a Poisson process of intensity `λ`, `h_ℓ = T 2^{−ℓ}`,
`Poisson(λ h_{ℓ+1}) ∗ Poisson(λ h_{ℓ+1}) = Poisson(λ h_ℓ)`. -/
lemma poisson_increments_conv (lam T : ℝ≥0) (ℓ : ℕ) :
    poissonMeasure (lam * (T / 2 ^ (ℓ + 1))) ∗ poissonMeasure (lam * (T / 2 ^ (ℓ + 1))) =
      poissonMeasure (lam * (T / 2 ^ ℓ)) := by
  rw [poissonMeasure_conv_poissonMeasure, ← mul_add, pow_succ, ← div_div, add_halves]

end levy

/-- **The coarse Lévy path has the law of the path on the level below** (Giles 2015, §6.2, p. 48).
If the fine increments are independent with law `ν`, the fine path at the coarse times,
`(L_{2m})_m`, has the law of the path built from independent increments of law `ν ∗ ν`. -/
theorem map_levyPath_levyPairSum {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] (ν : Measure M) [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : ℕ => ν).map (fun z m => levyPath z (2 * m)) =
      (Measure.infinitePi fun _ : ℕ => ν ∗ ν).map levyPath := by
  have hmeas : Measurable (levyPath : (ℕ → M) → ℕ → M) :=
    measurable_pi_lambda _ fun _ => Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have e : (fun (z : ℕ → M) (m : ℕ) => levyPath z (2 * m)) = levyPath ∘ levyPairSum :=
    funext fun z => funext fun m => (levyPath_levyPairSum z m).symm
  rw [e, ← Measure.map_map hmeas (measurePreserving_levyPairSum ν).measurable,
    (measurePreserving_levyPairSum ν).map_eq]

/-! ### §6.2: a terminal time made of many short exponential periods -/

section exponential

/-- The moments of the exponential law of rate `r > 0`: `∫ xᵐ d(Exp(r)) = m!/rᵐ`. -/
lemma integral_pow_expMeasure {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∫ x, x ^ m ∂(expMeasure r) = m.factorial / r ^ m := by
  have h1 : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  have hpdf : ∀ x, (exponentialPDF r x).toReal • x ^ m =
      Set.indicator (Set.Ici 0) (fun x => r * (x ^ m * Real.exp (-(r * x)))) x := by
    intro x
    rw [exponentialPDF_eq, ENNReal.toReal_ofReal (by split_ifs <;> positivity), smul_eq_mul]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, Set.indicator_of_mem (Set.mem_Ici.2 hx)]
      ring
    · rw [if_neg hx, Set.indicator_of_notMem (fun h => hx (Set.mem_Ici.1 h)), zero_mul]
  rw [h1, integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF r)
      (measurable_exponentialPDFReal r).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [hpdf]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul]
  have hc : ∫ x in Set.Ioi (0 : ℝ), x ^ m * Real.exp (-(r * x)) =
      ∫ x in Set.Ioi (0 : ℝ), x ^ (((m + 1 : ℕ) : ℝ) - 1) * Real.exp (-(r * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast]
  rw [hc, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr, Real.rpow_natCast,
    Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial]
  have hr0 : r ≠ 0 := hr.ne'
  rw [one_div, inv_pow]
  field_simp
  ring

/-- The exponential law of rate `r > 0` has a finite second moment, the mean `1/r` and the
variance `1/r²`. -/
lemma expMeasure_moments {r : ℝ} (hr : 0 < r) :
    MemLp id 2 (expMeasure r) ∧ ∫ x, x ∂(expMeasure r) = 1 / r ∧
      variance id (expMeasure r) = 1 / r ^ 2 := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h1 : ∫ x, x ∂(expMeasure r) = 1 / r := by
    simpa using integral_pow_expMeasure hr 1
  have h2 : ∫ x, x ^ 2 ∂(expMeasure r) = 2 / r ^ 2 := by
    simpa using integral_pow_expMeasure hr 2
  -- a non-integrable square would have the integral `0`
  have hi : Integrable (fun x : ℝ => x ^ 2) (expMeasure r) := by
    by_contra hni
    rw [integral_undef hni] at h2
    have : (0 : ℝ) < 2 / r ^ 2 := by positivity
    linarith
  have hm : MemLp id 2 (expMeasure r) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 hi
  refine ⟨hm, h1, ?_⟩
  rw [variance_eq_sub hm]
  simp only [Pi.pow_apply, id]
  rw [h2, h1]
  ring

/-- Scaling an exponential variable of rate `r` by `c > 0` gives an exponential variable of rate
`r/c`. -/
lemma map_const_mul_expMeasure {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (expMeasure r).map (fun x => c * x) = expMeasure (r / c) := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have : IsProbabilityMeasure (expMeasure (r / c)) :=
    isProbabilityMeasure_expMeasure (by positivity)
  have hm : Measurable fun x : ℝ => c * x := measurable_const_mul c
  have : IsProbabilityMeasure ((expMeasure r).map (fun x => c * x)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  refine Measure.ext_of_Iic _ _ fun a => ?_
  have hpre : (fun x : ℝ => c * x) ⁻¹' Set.Iic a = Set.Iic (a / c) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [le_div_iff₀ hc, mul_comm]
  rw [Measure.map_apply hm measurableSet_Iic, hpre, ← ofReal_cdf, ← ofReal_cdf,
    cdf_expMeasure_eq hr, cdf_expMeasure_eq (by positivity)]
  have h1 : 0 ≤ a / c ↔ 0 ≤ a := (le_div_iff₀ hc).trans (by rw [zero_mul])
  have h2 : r * (a / c) = r / c * a := by ring
  simp only [h1, h2]

/-- **Many shorter random periods get closer to the fixed terminal time** (Giles 2015, §6.2, p. 48:
Ferreiro-Castilla et al. "sample exactly from the joint distribution of the terminal value of a
Lévy process at an exponential random stopping time … The particularly novel aspect here is the
random terminal time; by using multiple shorter random periods it is possible, because of the
Central Limit Theorem, to get closer to a desired fixed terminal time, but at an increased cost").
If the terminal time is the sum `τ = X_1 + ⋯ + X_n` of `n ≥ 1` pairwise independent exponential
periods of rate `n/T` (mean `T/n`), then `E[τ] = T` and `V[τ] = T²/n`, so by Chebyshev's
inequality `P(|τ − T| ≥ δ) ≤ T²/(n δ²)`: the random terminal time concentrates at `T` as the
number `n` of periods, and the cost, grows.  (The Central Limit Theorem, which the paper invokes,
adds that `(τ − T) √n / T` is asymptotically standard normal: `exponential_periods_clt`.) -/
theorem sum_exponential_periods {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (expMeasure (n / T)) μ)
    (hind : Pairwise fun i j => IndepFun (X i) (X j) μ) :
    ∫ ω, ∑ i, X i ω ∂μ = T ∧ variance (fun ω => ∑ i, X i ω) μ = T ^ 2 / n ∧
      ∀ δ > 0, μ {ω | δ ≤ |∑ i, X i ω - T|} ≤ ENNReal.ofReal (T ^ 2 / (n * δ ^ 2)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hr : (0 : ℝ) < n / T := div_pos hn' hT
  obtain ⟨hm, h1, hv⟩ := expMeasure_moments hr
  have hXm : ∀ i, MemLp (X i) 2 μ := fun i =>
    (memLp_map_measure_iff (g := id) (by rw [(hX i).map_eq]; exact aestronglyMeasurable_id)
      (hX i).aemeasurable).1 (by rw [(hX i).map_eq]; exact hm)
  have hE : ∀ i, ∫ ω, X i ω ∂μ = T / n := fun i => by
    rw [(hX i).integral_eq, h1]
    field_simp
  have hV : ∀ i, variance (X i) μ = T ^ 2 / n ^ 2 := fun i => by
    rw [(hX i).variance_eq, hv]
    field_simp
  have hS : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    rw [Finset.sum_apply]
  have hmean : ∫ ω, ∑ i, X i ω ∂μ = T := by
    rw [integral_finsetSum _ fun i _ => (hXm i).integrable one_le_two]
    simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hvar : variance (fun ω => ∑ i, X i ω) μ = T ^ 2 / n := by
    rw [hS, IndepFun.variance_sum (fun i _ => hXm i) (fun i _ j _ hij => hind hij)]
    simp only [hV, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨hmean, hvar, fun δ hδ => ?_⟩
  have hSm : MemLp (fun ω => ∑ i, X i ω) 2 μ := memLp_finsetSum _ fun i _ => hXm i
  have h := meas_ge_le_variance_div_sq hSm hδ
  rw [hmean, hvar] at h
  refine h.trans_eq ?_
  congr 1
  field_simp

/-- **The Central Limit Theorem for the random terminal time** (Giles 2015, §6.2, p. 48: "by using
multiple shorter random periods it is possible, because of the Central Limit Theorem, to get closer
to a desired fixed terminal time, but at an increased cost").  Let `E_0, E_1, …` be independent
exponential variables of rate `1`.  For `n ≥ 1` the `n` periods `(T/n) E_k`, `k < n`, are
exponential of rate `n/T` (mean `T/n`), and the terminal time `τ_n = ∑_{k<n} (T/n) E_k` satisfies
`(√n/T)(τ_n − T) → N(0, 1)` in distribution as `n → ∞`: `τ_n ≈ T + (T/√n) N(0, 1)`.  (Mathlib's
Central Limit Theorem applies to one sequence of variables, so the periods for all `n` are built
from the same `E_k`; `sum_exponential_periods` gives the mean and the variance for each `n`.) -/
theorem exponential_periods_clt {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {E : ℕ → Ω → ℝ} {Y : Ω' → ℝ} (hE : ∀ k, HasLaw (E k) (expMeasure 1) P)
    (hind : iIndepFun E P) (hY : HasLaw Y (gaussianReal 0 1) P') {T : ℝ} (hT : 0 < T) :
    (∀ n : ℕ, 0 < n → ∀ k, HasLaw (fun ω => T / n * E k ω) (expMeasure (n / T)) P) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => Real.sqrt n / T * (∑ k ∈ range n, T / n * E k ω - T)) Filter.atTop Y
        (fun _ => P) P' := by
  obtain ⟨hm, h1, hv⟩ := expMeasure_moments one_pos
  refine ⟨fun n hn k => ?_, ?_⟩
  · have hc : (0 : ℝ) < T / n := div_pos hT (Nat.cast_pos.2 hn)
    have hmp : MeasurePreserving (fun x : ℝ => T / n * x) (expMeasure 1) (expMeasure (n / T)) :=
      ⟨measurable_const_mul _, by rw [map_const_mul_expMeasure one_pos hc, one_div_div]⟩
    exact hmp.fun_comp_hasLaw (hE k)
  have hE0 : MemLp (E 0) 2 P :=
    (memLp_map_measure_iff (g := id) (by rw [(hE 0).map_eq]; exact aestronglyMeasurable_id)
      (hE 0).aemeasurable).1 (by rw [(hE 0).map_eq]; exact hm)
  have hmean : ∫ ω, E 0 ω ∂P = 1 := by
    rw [(hE 0).integral_eq, h1]
    norm_num
  have hvar : variance (E 0) P = 1 := by
    rw [(hE 0).variance_eq, hv]
    norm_num
  have hident : ∀ i, IdentDistrib (E i) (E 0) P P := fun i =>
    ⟨(hE i).aemeasurable, (hE 0).aemeasurable, by rw [(hE i).map_eq, (hE 0).map_eq]⟩
  -- the centred variables `E_k − 1` have mean `0` and variance `1`
  have h0 : P[fun ω => E 0 ω - 1] = 0 := by
    rw [integral_sub (hE0.integrable one_le_two) (integrable_const 1), hmean]
    simp
  have h1' : P[(fun ω => E 0 ω - 1) ^ 2] = 1 := by
    have h := variance_eq_integral (hE 0).aemeasurable (μ := P)
    rw [hmean, hvar] at h
    exact h.symm
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum (X := fun k ω => E k ω - 1) hY h0 h1'
    (hind.comp (fun _ x => x - 1) (fun _ => measurable_id.sub_const 1))
    (fun i => (hident i).comp (measurable_id.sub_const 1))
  convert hclt using 2 with n
  funext ω
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hs : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt hn'.le).symm
    have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn').ne'
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    set s := Real.sqrt n
    rw [hs]
    field_simp

end exponential

/-! ### §7.1: finite elements with one-point quadrature -/

section fem

/-- The nodal values of the hat function `φ_j` of a uniform mesh: `φ_j(x_i) = δ_{ij}`. -/
def hatNodal (j i : ℕ) : ℝ := if i = j then 1 else 0

/-- The stiffness row of node `j` for `−(c u′)′ = f` with piecewise-linear finite elements on the
uniform mesh `x_i = i h` of `[0, N h]` and the one-point (midpoint) quadrature on every element
(Giles 2015, §7.1): `∑_e |e| c(m_e) u_h′|_e φ_j′|_e`, where on the element `e = [x_e, x_{e+1}]` of
midpoint `m_e = (e + ½) h` the slopes of `u_h = ∑_i u_i φ_i` and `φ_j` are the differences of their
nodal values divided by `h`. -/
noncomputable def feStiffness (N : ℕ) (h : ℝ) (c : ℝ → ℝ) (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ e ∈ range N, h * c ((e + 1 / 2) * h) * ((u (e + 1) - u e) / h) *
    ((hatNodal j (e + 1) - hatNodal j e) / h)

/-- The load of node `j`, `∫ f φ_j`, with the one-point (midpoint) quadrature on every element
(Giles 2015, §7.1): `∑_e |e| f(m_e) φ_j(m_e)`, where `φ_j(m_e)` is the average of the nodal values
of `φ_j` at the ends of `e`. -/
noncomputable def feLoad (N : ℕ) (h : ℝ) (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∑ e ∈ range N, h * f ((e + 1 / 2) * h) * ((hatNodal j (e + 1) + hatNodal j e) / 2)

/-- Only the two elements `[x_{j−1}, x_j]` and `[x_j, x_{j+1}]` meet the support of `φ_j`. -/
lemma sum_range_hatNodal {N j : ℕ} (hj : 1 ≤ j) (hjN : j < N) (a : ℕ → ℝ) :
    ∑ e ∈ range N, a e * hatNodal j (e + 1) = a (j - 1) ∧
      ∑ e ∈ range N, a e * hatNodal j e = a j := by
  constructor
  · have e1 : ∀ e ∈ range N, a e * hatNodal j (e + 1) = if e = j - 1 then a e else 0 := by
      intro e _
      simp only [hatNodal]
      by_cases h : e = j - 1
      · rw [if_pos (by omega), if_pos h, mul_one]
      · rw [if_neg (by omega), if_neg h, mul_zero]
    rw [sum_congr rfl e1, sum_ite_eq' (range N) (j - 1) a, if_pos (mem_range.2 (by omega))]
  · have e1 : ∀ e ∈ range N, a e * hatNodal j e = if e = j then a e else 0 := by
      intro e _
      simp only [hatNodal]
      split_ifs <;> simp
    rw [sum_congr rfl e1, sum_ite_eq' (range N) j a, if_pos (mem_range.2 hjN)]

/-- **Finite elements with one-point quadrature are central differences** (Giles 2015, §7.1,
p. 49: "A simple second order central difference approximation is used (equivalent to a finite
element approximation with a 1-point quadrature)").  At an interior node `x_j = j h`
(`1 ≤ j < N`), the finite-element stiffness row is `h` times the conservative central difference
`−(c_{j+½}(u_{j+1} − u_j) − c_{j−½}(u_j − u_{j−1}))/h²` of `−(c u′)′` (for `c ≡ 1`, the usual
`−(u_{j+1} − 2u_j + u_{j−1})/h²`), and the load is `h (f_{j−½} + f_{j+½})/2`, which is `h f` for
the constant forcing `f = 50 Z²` of the example; so the two discrete equations coincide after
division by `h`. -/
theorem fe_eq_centralDiff {N j : ℕ} (hj : 1 ≤ j) (hjN : j < N) {h : ℝ} (hh : h ≠ 0)
    (c f : ℝ → ℝ) (u : ℕ → ℝ) :
    feStiffness N h c u j = h * (-(c ((j + 1 / 2) * h) * (u (j + 1) - u j) -
        c ((j - 1 / 2) * h) * (u j - u (j - 1))) / h ^ 2) ∧
      feLoad N h f j = h * ((f ((j - 1 / 2) * h) + f ((j + 1 / 2) * h)) / 2) := by
  have hc : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj, Nat.cast_one]
  have hj1 : j - 1 + 1 = j := by omega
  constructor
  · obtain ⟨s1, s2⟩ := sum_range_hatNodal hj hjN
      (fun e => c ((e + 1 / 2) * h) * ((u (e + 1) - u e) / h))
    have e : feStiffness N h c u j =
        ∑ e ∈ range N, c ((e + 1 / 2) * h) * ((u (e + 1) - u e) / h) * hatNodal j (e + 1) -
          ∑ e ∈ range N, c ((e + 1 / 2) * h) * ((u (e + 1) - u e) / h) * hatNodal j e := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun e _ => ?_
      field_simp
    rw [e, s1, s2, hc, hj1]
    field_simp
    ring_nf
  · obtain ⟨s1, s2⟩ := sum_range_hatNodal hj hjN (fun e => h * f ((e + 1 / 2) * h) / 2)
    have e : feLoad N h f j =
        ∑ e ∈ range N, h * f ((e + 1 / 2) * h) / 2 * hatNodal j (e + 1) +
          ∑ e ∈ range N, h * f ((e + 1 / 2) * h) / 2 * hatNodal j e := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun e _ => ?_
      ring
    rw [e, s1, s2, hc]
    ring_nf

end fem

/-! ### §7.1: the elliptic example with a random constant -/

section rates

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Pathwise errors with a random constant give the weak and the variance rates** (Giles 2015,
§7.1, p. 49, corrected: see `elliptic_rates_random`).  If `|P − P_ℓ| ≤ K e_ℓ` almost surely for
every level, with a random `K` of finite second moment and deterministic `e_ℓ`, then
`P_ℓ − P` is integrable with `|E[P_ℓ − P]| ≤ E[K] e_ℓ`, and `P_{ℓ+1} − P_ℓ` is square integrable
with `V[P_{ℓ+1} − P_ℓ] ≤ E[(P_{ℓ+1} − P_ℓ)²] ≤ E[K²] (e_{ℓ+1} + e_ℓ)²`.  (`rates_of_pathwise` of
`MlmcLean.PDEExamples` is the case of a deterministic `K` and `e_ℓ = 2^{−pℓ}`.) -/
theorem rates_of_pathwise_random [IsProbabilityMeasure μ] {P : Ω → ℝ} {Pl : ℕ → Ω → ℝ}
    {K : Ω → ℝ} {e : ℕ → ℝ} (hP : AEStronglyMeasurable P μ)
    (hPl : ∀ ℓ, AEStronglyMeasurable (Pl ℓ) μ) (hK : MemLp K 2 μ)
    (herr : ∀ ℓ, ∀ᵐ ω ∂μ, |P ω - Pl ℓ ω| ≤ K ω * e ℓ) :
    ∀ ℓ : ℕ, Integrable (fun ω => Pl ℓ ω - P ω) μ ∧
      |∫ ω, (Pl ℓ ω - P ω) ∂μ| ≤ (∫ ω, K ω ∂μ) * e ℓ ∧
      MemLp (fun ω => Pl (ℓ + 1) ω - Pl ℓ ω) 2 μ ∧
      variance (fun ω => Pl (ℓ + 1) ω - Pl ℓ ω) μ ≤ ∫ ω, (Pl (ℓ + 1) ω - Pl ℓ ω) ^ 2 ∂μ ∧
      ∫ ω, (Pl (ℓ + 1) ω - Pl ℓ ω) ^ 2 ∂μ ≤ (∫ ω, K ω ^ 2 ∂μ) * (e (ℓ + 1) + e ℓ) ^ 2 := by
  intro ℓ
  have hK1 : Integrable K μ := hK.integrable one_le_two
  have hK2 : Integrable (fun ω => K ω ^ 2) μ := hK.integrable_sq
  -- the weak error
  have hle : ∀ᵐ ω ∂μ, |Pl ℓ ω - P ω| ≤ K ω * e ℓ :=
    (herr ℓ).mono fun ω h => (abs_sub_comm _ _).trans_le h
  have hint : Integrable (fun ω => Pl ℓ ω - P ω) μ :=
    (hK1.mul_const _).mono' ((hPl ℓ).sub hP) (hle.mono fun ω h => by rwa [Real.norm_eq_abs])
  -- the correction, pointwise
  have hpt : ∀ᵐ ω ∂μ, (Pl (ℓ + 1) ω - Pl ℓ ω) ^ 2 ≤ (e (ℓ + 1) + e ℓ) ^ 2 * K ω ^ 2 := by
    filter_upwards [herr (ℓ + 1), herr ℓ] with ω h1 h0
    have hb : |Pl (ℓ + 1) ω - Pl ℓ ω| ≤ (e (ℓ + 1) + e ℓ) * K ω := by
      calc |Pl (ℓ + 1) ω - Pl ℓ ω| ≤ |P ω - Pl (ℓ + 1) ω| + |P ω - Pl ℓ ω| := by
            rw [show Pl (ℓ + 1) ω - Pl ℓ ω = (P ω - Pl ℓ ω) - (P ω - Pl (ℓ + 1) ω) by ring]
            exact (abs_sub _ _).trans_eq (add_comm _ _)
        _ ≤ K ω * e (ℓ + 1) + K ω * e ℓ := add_le_add h1 h0
        _ = (e (ℓ + 1) + e ℓ) * K ω := by ring
    rw [← sq_abs]
    calc |Pl (ℓ + 1) ω - Pl ℓ ω| ^ 2 ≤ ((e (ℓ + 1) + e ℓ) * K ω) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = (e (ℓ + 1) + e ℓ) ^ 2 * K ω ^ 2 := by ring
  have hm : AEStronglyMeasurable (fun ω => Pl (ℓ + 1) ω - Pl ℓ ω) μ := (hPl (ℓ + 1)).sub (hPl ℓ)
  have hsq : Integrable (fun ω => (Pl (ℓ + 1) ω - Pl ℓ ω) ^ 2) μ :=
    (hK2.const_mul _).mono' (hm.pow 2) (hpt.mono fun ω h => by
      rwa [Real.norm_of_nonneg (sq_nonneg _)])
  refine ⟨hint, ?_, (memLp_two_iff_integrable_sq hm).2 hsq, variance_le_expectation_sq hm, ?_⟩
  · calc |∫ ω, (Pl ℓ ω - P ω) ∂μ| ≤ ∫ ω, |Pl ℓ ω - P ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, K ω * e ℓ ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
            (hK1.mul_const _) hle
      _ = (∫ ω, K ω ∂μ) * e ℓ := integral_mul_const _ _
  · calc ∫ ω, (Pl (ℓ + 1) ω - Pl ℓ ω) ^ 2 ∂μ ≤ ∫ ω, (e (ℓ + 1) + e ℓ) ^ 2 * K ω ^ 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
            (hK2.const_mul _) hpt
      _ = (∫ ω, K ω ^ 2 ∂μ) * (e (ℓ + 1) + e ℓ) ^ 2 := by
          rw [integral_const_mul]
          ring

/-- **The elliptic example, with a random constant** (Giles 2015, §7.1, p. 49: "Level `ℓ` uses a
uniform grid with spacing `h_ℓ = 2^{−(ℓ+1)}` … The uniform second order accuracy means that there
is a constant `K` such that `|P − P_ℓ| < K h_ℓ²` and therefore we have `α = 2`, `β = 4`").  The
forcing of the example is `−50 Z²` with `Z` standard normal, so `P − P_ℓ` is `Z²` times the error
of the problem with the forcing `−50`, and no deterministic `K` exists
(`not_ae_abs_gaussian_sq_mul_le`); `elliptic_rates` of `MlmcLean.PDEExamples` assumes one.  The
rates hold with a random `K`, for instance `K = c Z²`, as long as `E[K²] < ∞`: if
`|P − P_ℓ| ≤ K h_ℓ²` almost surely, then `|E[P_ℓ − P]| ≤ E[K] h_ℓ² = (E[K]/4) 2^{−2ℓ}` (`α = 2`)
and `V[P_{ℓ+1} − P_ℓ] ≤ E[(P_{ℓ+1} − P_ℓ)²] ≤ 25 E[K²] h_{ℓ+1}⁴ = (25/256) E[K²] 2^{−4ℓ}`
(`β = 4`). -/
theorem elliptic_rates_random [IsProbabilityMeasure μ] {P : Ω → ℝ} {Pl : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hP : AEStronglyMeasurable P μ) (hPl : ∀ ℓ, AEStronglyMeasurable (Pl ℓ) μ)
    (hK : MemLp K 2 μ)
    (herr : ∀ ℓ : ℕ, ∀ᵐ ω ∂μ, |P ω - Pl ℓ ω| ≤ K ω * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2) :
    ∀ ℓ : ℕ, |∫ ω, (Pl ℓ ω - P ω) ∂μ| ≤ (∫ ω, K ω ∂μ) * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 ∧
      variance (fun ω => Pl (ℓ + 1) ω - Pl ℓ ω) μ ≤ ∫ ω, (Pl (ℓ + 1) ω - Pl ℓ ω) ^ 2 ∂μ ∧
      ∫ ω, (Pl (ℓ + 1) ω - Pl ℓ ω) ^ 2 ∂μ ≤
        25 * (∫ ω, K ω ^ 2 ∂μ) * ((1 / 2 : ℝ) ^ (ℓ + 2)) ^ 4 := by
  intro ℓ
  obtain ⟨-, h1, -, h2, h3⟩ := rates_of_pathwise_random hP hPl hK herr ℓ
  refine ⟨h1, h2, h3.trans_eq ?_⟩
  rw [pow_succ (1 / 2 : ℝ) (ℓ + 1)]
  ring

/-- **No deterministic constant in the elliptic example** (Giles 2015, §7.1, p. 49: "there is a
constant `K` such that `|P − P_ℓ| < K h_ℓ²`").  The equation `(c u′)′ = −50 Z²` is linear in the
forcing, so `P − P_ℓ = Z² e` where `e` is the error of the problem with the forcing `−50`; if
`e ≠ 0`, no constant bounds it almost surely, because `Z²` is unbounded for a standard normal `Z`:
`¬ (|Z² e| ≤ K a.s.)` for every `K`. -/
theorem not_ae_abs_gaussian_sq_mul_le {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ)
    {e : ℝ} (he : e ≠ 0) (K : ℝ) : ¬ ∀ᵐ ω ∂μ, |Z ω ^ 2 * e| ≤ K := by
  intro h
  have hS : MeasurableSet {z : ℝ | K < |z ^ 2 * e|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have h0 : μ {ω | K < |Z ω ^ 2 * e|} = 0 := by
    rw [ae_iff] at h
    simpa only [not_le] using h
  rw [hZ.measure_eq hS] at h0
  -- the standard normal law charges every half-line
  have h1 : volume {z : ℝ | K < |z ^ 2 * e|} = 0 :=
    gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
  have he' : 0 < |e| := abs_pos.2 he
  have h2 : Set.Ioi (|K| / |e| + 1) ⊆ {z : ℝ | K < |z ^ 2 * e|} := by
    intro z hz
    simp only [Set.mem_Ioi] at hz
    simp only [Set.mem_ofPred_eq, abs_mul, abs_pow, sq_abs]
    have hK0 : 0 ≤ |K| / |e| := div_nonneg (abs_nonneg K) he'.le
    have hz1 : 1 < z := by linarith
    have hzz : z ≤ z ^ 2 := by nlinarith
    have hlt : |K| < z ^ 2 * |e| := by
      rw [← div_lt_iff₀ he']
      linarith
    exact (le_abs_self K).trans_lt hlt
  have h3 := measure_mono_null h2 h1
  rw [Real.volume_Ioi] at h3
  exact ENNReal.top_ne_zero h3

end rates

/-! ### §7.3: the Milstein scheme for the credit SPDE -/

section spde

/-- The central first difference `D₁p_j = (p_{j+1} − p_{j−1})/(2h)` (Giles 2015, §7.3). -/
noncomputable def spdeD1 (h : ℝ) (p : ℤ → ℝ) (j : ℤ) : ℝ := (p (j + 1) - p (j - 1)) / (2 * h)

/-- The central second difference `D₂p_j = (p_{j+1} − 2p_j + p_{j−1})/h²` (Giles 2015, §7.3). -/
noncomputable def spdeD2 (h : ℝ) (p : ℤ → ℝ) (j : ℤ) : ℝ :=
  (p (j + 1) - 2 * p j + p (j - 1)) / h ^ 2

/-- The noise operator `B p = −√ρ ∂p/∂x` of the SPDE `dp = −μ p_x dt + ½ p_xx dt − √ρ p_x dM`
(Giles 2015, §7.3). -/
noncomputable def spdeNoiseOp (ρ : ℝ) (p : ℝ → ℝ) : ℝ → ℝ := fun x => -Real.sqrt ρ * deriv p x

/-- The operator of the Milstein correction: `B(B p) = ρ ∂²p/∂x²` for `ρ ≥ 0` (Giles 2015,
§7.3). -/
lemma spdeNoiseOp_twice {ρ : ℝ} (hρ : 0 ≤ ρ) (p : ℝ → ℝ) :
    spdeNoiseOp ρ (spdeNoiseOp ρ p) = fun x => ρ * deriv (deriv p) x := by
  funext x
  have h := Real.mul_self_sqrt hρ
  unfold spdeNoiseOp
  rw [deriv_const_mul_field']
  linear_combination (deriv (deriv p) x) * h

/-- One Milstein time step of size `k` for the SPDE `dp = A p dt + B p dM` of Giles 2015, §7.3,
with `A p = −μ p_x + ½ p_xx` and `B p = −√ρ p_x`: `p + A p k + B p ΔM + ½ B(B p) (ΔM² − k)`
(the Milstein correction `½ b′(p)[b(p)] (ΔM² − k)` of §5.2, `b = B` being linear). -/
noncomputable def spdeMilsteinStep (μ ρ k dM : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  p x + (-μ * deriv p x + 1 / 2 * deriv (deriv p) x) * k + spdeNoiseOp ρ p x * dM +
    1 / 2 * spdeNoiseOp ρ (spdeNoiseOp ρ p) x * (dM ^ 2 - k)

/-- **The Milstein time step for the credit SPDE** (Giles 2015, §7.3, p. 53: "`dp = −μ ∂p/∂x dt +
½ ∂²p/∂x² dt − √ρ ∂p/∂x dM_t` … A Milstein time discretisation with timestep `k` …").  With the
Brownian increment `ΔM = √k Z`, `ρ ≥ 0` and `k ≥ 0`, one Milstein step is
`p − (μk + √(ρk) Z) ∂p/∂x + ((1 − ρ)k + ρk Z²)/2 ∂²p/∂x²`. -/
theorem spdeMilsteinStep_eq {μ ρ k : ℝ} (hρ : 0 ≤ ρ) (hk : 0 ≤ k) (Z : ℝ) (p : ℝ → ℝ) (x : ℝ) :
    spdeMilsteinStep μ ρ k (Real.sqrt k * Z) p x =
      p x - (μ * k + Real.sqrt (ρ * k) * Z) * deriv p x +
        ((1 - ρ) * k + ρ * k * Z ^ 2) / 2 * deriv (deriv p) x := by
  have h1 : Real.sqrt (ρ * k) = Real.sqrt ρ * Real.sqrt k := Real.sqrt_mul hρ k
  have h2 : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk
  unfold spdeMilsteinStep
  rw [spdeNoiseOp_twice hρ, h1]
  simp only [spdeNoiseOp]
  linear_combination (1 / 2 * ρ * Z ^ 2 * deriv (deriv p) x) * h2

/-- The fully discrete scheme printed in Giles 2015, §7.3, p. 54:
`p^{n+1}_j = p^n_j − (μk + √(ρk) Z_n)/(2h) (p^n_{j+1} − p^n_{j−1})
  + ((1 − ρ)k + ρk Z_n²)/(2h²) (p^n_{j+1} − 2p^n_j + p^n_{j−1})`. -/
noncomputable def spdeScheme (μ ρ h k Z : ℝ) (p : ℤ → ℝ) (j : ℤ) : ℝ :=
  p j - (μ * k + Real.sqrt (ρ * k) * Z) / (2 * h) * (p (j + 1) - p (j - 1)) +
    ((1 - ρ) * k + ρ * k * Z ^ 2) / (2 * h ^ 2) * (p (j + 1) - 2 * p j + p (j - 1))

/-- **The printed scheme is one Milstein step with central differences** (Giles 2015, §7.3,
pp. 53–54: "A Milstein time discretisation with timestep `k`, and a central space discretisation of
the spatial derivatives with uniform spacing `h` gives the numerical approximation
`p^{n+1}_j = p^n_j − (μk + √(ρk) Z_n)/(2h) (p^n_{j+1} − p^n_{j−1}) + ((1 − ρ)k + ρk Z_n²)/(2h²)
(p^n_{j+1} − 2p^n_j + p^n_{j−1})` where … the `Z_n` are standard Normal random variables so that
`√h Z_n` corresponds to an increment of the driving scalar Brownian motion").  For `ρ, k ≥ 0` the
scheme is the Milstein step of `spdeMilsteinStep_eq` with `∂_x`, `∂_xx` replaced by the central
differences `D₁`, `D₂`, i.e. `p + (−μ D₁p + ½ D₂p) k + (−√ρ D₁p) ΔM + ½ ρ D₂p (ΔM² − k)` with
`ΔM = √k Z_n`: the Brownian increment is `√k Z_n` (the paper's "`√h Z_n`" is a misprint, `h` being
the mesh width).  The Milstein correction uses the compact `D₂` for `B² = ρ ∂_xx`, not the square
of the discrete `−√ρ D₁`. -/
theorem spdeScheme_eq_milstein {μ ρ h k : ℝ} (hρ : 0 ≤ ρ) (hk : 0 ≤ k) (Z : ℝ) (p : ℤ → ℝ)
    (j : ℤ) :
    spdeScheme μ ρ h k Z p j =
        p j - (μ * k + Real.sqrt (ρ * k) * Z) * spdeD1 h p j +
          ((1 - ρ) * k + ρ * k * Z ^ 2) / 2 * spdeD2 h p j ∧
      spdeScheme μ ρ h k Z p j =
        p j + (-μ * spdeD1 h p j + 1 / 2 * spdeD2 h p j) * k +
          -Real.sqrt ρ * spdeD1 h p j * (Real.sqrt k * Z) +
          1 / 2 * (ρ * spdeD2 h p j) * ((Real.sqrt k * Z) ^ 2 - k) := by
  have h1 : Real.sqrt (ρ * k) = Real.sqrt ρ * Real.sqrt k := Real.sqrt_mul hρ k
  have h2 : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk
  unfold spdeScheme spdeD1 spdeD2
  constructor
  · ring
  · rw [h1]
    linear_combination (-(1 / 2) * ρ * Z ^ 2 * ((p (j + 1) - 2 * p j + p (j - 1)) / h ^ 2)) * h2

end spde

/-! ### §10.2: variable precision and the Brownian-bridge construction -/

section bridge

/-- The Brownian-bridge (Lévy–Ciesielski) construction of the Brownian values `W(i T 2^{−ℓ})`,
`0 ≤ i ≤ 2^ℓ`, from the normal inputs `Z_0, Z_1, …` (Giles 2015, §10.2): `W(0) = 0`,
`W(T) = √T Z_0`, and level `ℓ + 1` keeps the level-`ℓ` values at the even points and adds the
midpoints of the level-`ℓ` intervals,
`W(t_{2m+1}) = ½(W(t_{2m}) + W(t_{2m+2})) + ½ √(T 2^{−ℓ}) Z_{2^ℓ+m}`.  Every new value is rounded
by `r` (the arithmetic of the level; `r = id` is exact arithmetic). -/
noncomputable def bbPath (r : ℝ → ℝ) (T : ℝ) (Z : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, i => if i = 0 then 0 else r (Real.sqrt T * Z 0)
  | ℓ + 1, i =>
    if i % 2 = 0 then bbPath r T Z ℓ (i / 2)
    else r ((bbPath r T Z ℓ (i / 2) + bbPath r T Z ℓ (i / 2 + 1)) / 2 +
      Real.sqrt (T / 2 ^ ℓ) / 2 * Z (2 ^ ℓ + i / 2))

section exact

variable (r : ℝ → ℝ) (T : ℝ)

/-- The refinement keeps the level-`ℓ` values at the even points. -/
lemma bbPath_succ_two_mul (Z : ℕ → ℝ) (ℓ i : ℕ) :
    bbPath r T Z (ℓ + 1) (2 * i) = bbPath r T Z ℓ i := by
  have e1 : 2 * i % 2 = 0 := by omega
  have e2 : 2 * i / 2 = i := by omega
  rw [bbPath, if_pos e1, e2]

/-- The refinement adds the midpoints: the Brownian-bridge step. -/
lemma bbPath_succ_two_mul_add_one (Z : ℕ → ℝ) (ℓ i : ℕ) :
    bbPath r T Z (ℓ + 1) (2 * i + 1) =
      r ((bbPath r T Z ℓ i + bbPath r T Z ℓ (i + 1)) / 2 +
        Real.sqrt (T / 2 ^ ℓ) / 2 * Z (2 ^ ℓ + i)) := by
  have e1 : ¬(2 * i + 1) % 2 = 0 := by omega
  have e2 : (2 * i + 1) / 2 = i := by omega
  rw [bbPath, if_neg e1, e2]

/-- **The finer constructions contain the coarser ones** (Giles 2015, §10.2): the level-`ℓ` values
computed inside the level-`(ℓ + m)` construction coincide with the level-`ℓ` construction,
`W^{(ℓ+m)}(2^m i) = W^{(ℓ)}(i)`, when both use the same arithmetic. -/
theorem bbPath_nested (Z : ℕ → ℝ) (ℓ m i : ℕ) :
    bbPath r T Z (ℓ + m) (2 ^ m * i) = bbPath r T Z ℓ i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, pow_succ, mul_comm (2 ^ m) 2, mul_assoc, bbPath_succ_two_mul, ih]

/-- **The level-`ℓ` values use only the first `2^ℓ` inputs** (Giles 2015, §10.2): if two input
sequences agree on `Z_0, …, Z_{2^ℓ−1}`, the level-`ℓ` constructions agree at all the points
`0 ≤ i ≤ 2^ℓ`, whatever the rounding `r`. -/
theorem bbPath_congr {Z₁ Z₂ : ℕ → ℝ} {ℓ : ℕ} (h : ∀ n < 2 ^ ℓ, Z₁ n = Z₂ n) {i : ℕ}
    (hi : i ≤ 2 ^ ℓ) : bbPath r T Z₁ ℓ i = bbPath r T Z₂ ℓ i := by
  induction ℓ generalizing i with
  | zero =>
    have h0 : Z₁ 0 = Z₂ 0 := h 0 (by norm_num)
    simp only [bbPath, h0]
  | succ ℓ ih =>
    have h' : ∀ n < 2 ^ ℓ, Z₁ n = Z₂ n := fun n hn => h n (by rw [pow_succ]; omega)
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [bbPath_succ_two_mul, bbPath_succ_two_mul]
      exact ih h' (by rw [pow_succ] at hi; omega)
    · have hm : m < 2 ^ ℓ := by rw [pow_succ] at hi; omega
      rw [bbPath_succ_two_mul_add_one, bbPath_succ_two_mul_add_one, ih h' hm.le, ih h' hm,
        h (2 ^ ℓ + m) (by rw [pow_succ]; omega)]

/-- With the same arithmetic on both levels, the coarse path of a level-`(ℓ + 1)` sample (the fine
path at the even points) is the level-`ℓ` path. -/
lemma bbCoarse_eq_fine (Z : ℕ → ℝ) (ℓ : ℕ) (F : (Fin (2 ^ ℓ + 1) → ℝ) → ℝ) :
    F (fun i => bbPath r T Z (ℓ + 1) (2 * i)) = F (fun i => bbPath r T Z ℓ i) :=
  congrArg F (funext fun i => bbPath_succ_two_mul r T Z ℓ i)

/-- **The telescoping sum holds pathwise for the Brownian-bridge construction** (Giles 2015,
§10.2: "The Brownian path being generated for level `ℓ` is then exactly the same, regardless of
whether it is the finer or coarser of the two levels … Hence, the telescoping sum will be
respected"), here with the same arithmetic on all levels.  With a payoff `F_ℓ` of the level-`ℓ`
values `(W(i T 2^{−ℓ}))_{i ≤ 2^ℓ}`, the fine payoff `P^f_ℓ = F_ℓ(W^{(ℓ)})` and the coarse payoff
`P^c_ℓ = F_ℓ((W^{(ℓ+1)}(2i))_i)` of a level-`(ℓ + 1)` sample, for every input sequence:
`P^f_0 + ∑_{ℓ<L} (P^f_{ℓ+1} − P^c_ℓ) = P^f_L`.  Indeed `P^c_ℓ = P^f_ℓ` pathwise
(`bbCoarse_eq_fine`), so also `E[P^c_ℓ] = E[P^f_ℓ]` whatever the law of the inputs. -/
theorem bb_telescoping (Z : ℕ → ℝ) (F : (ℓ : ℕ) → (Fin (2 ^ ℓ + 1) → ℝ) → ℝ) (L : ℕ) :
    F 0 (fun i => bbPath r T Z 0 i) +
      ∑ ℓ ∈ range L, (F (ℓ + 1) (fun i => bbPath r T Z (ℓ + 1) i) -
        F ℓ (fun i => bbPath r T Z (ℓ + 1) (2 * i))) = F L (fun i => bbPath r T Z L i) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ← add_assoc, ih, bbCoarse_eq_fine r T Z L (F L)]
    ring

end exact

/-- The normal inputs of a sample made of the random integers `I_0, …, I_{m−1}` (padded with
zeros), converted by the generator `G` of the level (Giles 2015, §10.2: "`I_n → U_n → Z_n` where
`I_n` is a random integer on a range `[0, I_max]`, `U_n = (I_n + ½)/I_max` is a random,
approximately uniformly-distributed variable on the interval `(0, 1)`, and `Z_n = Φ⁻¹(U_n)`";
`G` is arbitrary, for instance `Φ⁻¹` evaluated in the precision of the level; `U_n` should read
`(I_n + ½)/(I_max + 1)`, since `(I_max + ½)/I_max > 1`). -/
noncomputable def vpInputs (G : ℕ → ℝ) {m : ℕ} (I : Fin m → ℕ) (n : ℕ) : ℝ :=
  if h : n < m then G (I ⟨n, h⟩) else 0

/-- The level-`ℓ` Brownian values `(W(i T 2^{−ℓ}))_{i ≤ 2^ℓ}` computed in the precision of level
`ℓ` (rounding `rnd ℓ`, generator `G ℓ`) from the random integers `I` of a sample (Giles 2015,
§10.2). -/
noncomputable def vpPath (rnd : ℕ → ℝ → ℝ) (G : ℕ → ℕ → ℝ) (T : ℝ) (ℓ : ℕ) {m : ℕ}
    (I : Fin m → ℕ) (i : Fin (2 ^ ℓ + 1)) : ℝ :=
  bbPath (rnd ℓ) T (vpInputs (G ℓ) I) ℓ i

/-- **The level-`ℓ` path is the same whether it is the finer or the coarser level** (Giles 2015,
§10.2, p. 62: "When using a Brownian Bridge construction, as long as the `I_n` are generated in
exactly the same way for each level, the other two steps can be performed with the level of
accuracy appropriate to the level of the path … The Brownian path being generated for level `ℓ`
is then exactly the same, regardless of whether it is the finer or coarser of the two levels being
simulated for a particular multilevel correction").  For any roundings `rnd ℓ` and generators
`G ℓ`, the level-`ℓ` path computed in level-`ℓ` precision from the `m ≥ 2^ℓ` integers of a sample
(for instance the coarse path of a level-`(ℓ + 1)` correction, `m = 2^{ℓ+1}`) is the level-`ℓ`
path of the sample made of their first `2^ℓ` integers (the fine path of a level-`ℓ` correction). -/
theorem vpPath_castLE (rnd : ℕ → ℝ → ℝ) (G : ℕ → ℕ → ℝ) (T : ℝ) (ℓ : ℕ) {m : ℕ}
    (hm : 2 ^ ℓ ≤ m) (I : Fin m → ℕ) :
    vpPath rnd G T ℓ I = vpPath rnd G T ℓ (fun n : Fin (2 ^ ℓ) => I (Fin.castLE hm n)) := by
  funext i
  refine bbPath_congr (rnd ℓ) T (fun n hn => ?_) (Nat.lt_succ_iff.1 i.2)
  simp only [vpInputs, dif_pos hn, dif_pos (lt_of_lt_of_le hn hm)]
  rfl

/-- The first `n` of `m ≥ n` independent integers of law `ν` are independent of law `ν`. -/
lemma measurePreserving_restrictFin (ν : Measure ℕ) [IsProbabilityMeasure ν] {n m : ℕ}
    (h : n ≤ m) :
    MeasurePreserving (fun (I : Fin m → ℕ) (k : Fin n) => I (Fin.castLE h k))
      (Measure.infinitePi fun _ : Fin m => ν) (Measure.infinitePi fun _ : Fin n => ν) :=
  ⟨measurable_pi_lambda _ fun _ => measurable_pi_apply _,
    Measure.map_infinitePi_infinitePi_of_inj (Fin.castLE_injective h)⟩

/-- **(2.4) in variable precision** (Giles 2015, §2.1, (2.4) "`E[P^f_ℓ] = E[P^c_ℓ]`", and §10.2,
p. 62).  If the random integers are independent with the same law `ν` on every level, then for
any roundings `rnd ℓ`, generators `G ℓ` and payoff `F`, the coarse payoff `F(W^{(ℓ)})` of a
level-`(ℓ + 1)` sample (`2^{ℓ+1}` integers) has the expectation of the fine payoff `F(W^{(ℓ)})`
of a level-`ℓ` sample (`2^ℓ` integers). -/
theorem integral_vpCoarse (rnd : ℕ → ℝ → ℝ) (G : ℕ → ℕ → ℝ) (T : ℝ) (ν : Measure ℕ)
    [IsProbabilityMeasure ν] (ℓ : ℕ) (F : (Fin (2 ^ ℓ + 1) → ℝ) → ℝ) :
    ∫ I, F (vpPath rnd G T ℓ I) ∂(Measure.infinitePi fun _ : Fin (2 ^ (ℓ + 1)) => ν) =
      ∫ I, F (vpPath rnd G T ℓ I) ∂(Measure.infinitePi fun _ : Fin (2 ^ ℓ) => ν) := by
  have hm : 2 ^ ℓ ≤ 2 ^ (ℓ + 1) := Nat.pow_le_pow_right two_pos (Nat.le_succ ℓ)
  simp_rw [vpPath_castLE rnd G T ℓ hm]
  exact integral_comp_of_measurePreserving (f := fun I => F (vpPath rnd G T ℓ I))
    (measurePreserving_restrictFin ν hm) Measurable.of_discrete.aestronglyMeasurable

/-- **The telescoping sum in variable precision** (Giles 2015, §10.2, p. 62: "Hence, the
telescoping sum will be respected").  A level-`ℓ` sample consists of `2^ℓ` independent random
integers of law `ν`; the level-`(ℓ + 1)` correction is `F_{ℓ+1}(W^{(ℓ+1)}) − F_ℓ(W^{(ℓ)})`, both
paths computed from the same `2^{ℓ+1}` integers, each in the precision of its own level.  If the
level-`ℓ` payoffs are integrable, `E[P_0] + ∑_{ℓ<L} E[P_{ℓ+1} − P^c_ℓ] = E[P_L]`. -/
theorem vp_telescoping (rnd : ℕ → ℝ → ℝ) (G : ℕ → ℕ → ℝ) (T : ℝ) (ν : Measure ℕ)
    [IsProbabilityMeasure ν] (F : (ℓ : ℕ) → (Fin (2 ^ ℓ + 1) → ℝ) → ℝ)
    (hF : ∀ ℓ, Integrable (fun I => F ℓ (vpPath rnd G T ℓ I))
      (Measure.infinitePi fun _ : Fin (2 ^ ℓ) => ν)) (L : ℕ) :
    ∫ I, F 0 (vpPath rnd G T 0 I) ∂(Measure.infinitePi fun _ : Fin (2 ^ 0) => ν) +
      ∑ ℓ ∈ range L, ∫ I, (F (ℓ + 1) (vpPath rnd G T (ℓ + 1) I) - F ℓ (vpPath rnd G T ℓ I))
        ∂(Measure.infinitePi fun _ : Fin (2 ^ (ℓ + 1)) => ν) =
      ∫ I, F L (vpPath rnd G T L I) ∂(Measure.infinitePi fun _ : Fin (2 ^ L) => ν) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hm : 2 ^ L ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right two_pos (Nat.le_succ L)
    have hc : Integrable (fun I => F L (vpPath rnd G T L I))
        (Measure.infinitePi fun _ : Fin (2 ^ (L + 1)) => ν) := by
      simp_rw [vpPath_castLE rnd G T L hm]
      exact ((measurePreserving_restrictFin ν hm).integrable_comp
        (hF L).aestronglyMeasurable).2 (hF L)
    rw [sum_range_succ, ← add_assoc, ih, integral_sub (hF (L + 1)) hc, integral_vpCoarse]
    ring

end bridge

/-! ### §10.2: rounded fine increments do not sum to the rounded coarse increment -/

/-- Evaluating `roundFixed` from the floor characterisation of `round`. -/
lemma roundFixed_eq_of_floor {e : ℤ} {d : ℕ} {x : ℝ} {n : ℤ}
    (h : (n : ℝ) ≤ x / (2 : ℝ) ^ (e - d) + 1 / 2 ∧ x / (2 : ℝ) ^ (e - d) + 1 / 2 < n + 1) :
    roundFixed e d x = (2 : ℝ) ^ (e - d) * n := by
  rw [roundFixed, round_eq, Int.floor_eq_iff.2 h]

/-- **Rounded fine increments are inconsistent with the rounded coarse increment** (Giles 2015,
§10.2, p. 62: "This would not be the case if the increments on level `ℓ` were generated with
`B_ℓ` bits of accuracy, then summed to give increments for level `ℓ−1`, regardless of whether the
truncation to the lower accuracy `B_{ℓ−1}` took place before or after the summation").  In fixed
point with exponent `0`, `B_ℓ = 2` and `B_{ℓ−1} = 1` bits (`roundFixed`, grids `¼ℤ` and `½ℤ`),
let the two fine Brownian increments be `ΔW₁ ∈ (0, 1/20)` and `ΔW₂ ∈ (3/20, 1/5)` (for instance
`ΔW₁ = 1/100`, `ΔW₂ = 1/5`).  A level-`(ℓ − 1)` simulation of the same Brownian path rounds the
coarse increment `ΔW₁ + ΔW₂` to `0`, whereas summing the fine increments rounded to `B_ℓ` bits
gives `1/2`, with the truncation to `B_{ℓ−1}` bits before or after the summation.  This is a
pathwise statement, on a rectangle of increments of positive probability for Brownian increments;
the laws of the two coarse increments are not computed.  Compare `vpPath_castLE`. -/
theorem roundFixed_sum_inconsistent {x y : ℝ} (hx : 0 < x) (hx' : x < 1 / 20) (hy : 3 / 20 < y)
    (hy' : y < 1 / 5) :
    roundFixed 0 1 (x + y) = 0 ∧
      roundFixed 0 1 (roundFixed 0 2 x) + roundFixed 0 1 (roundFixed 0 2 y) = 1 / 2 ∧
      roundFixed 0 1 (roundFixed 0 2 x + roundFixed 0 2 y) = 1 / 2 := by
  have a1 : roundFixed 0 2 x = 0 := by
    rw [roundFixed_eq_of_floor (n := 0) (by constructor <;> norm_num <;> linarith)]
    norm_num
  have a2 : roundFixed 0 2 y = 1 / 4 := by
    rw [roundFixed_eq_of_floor (n := 1) (by constructor <;> norm_num <;> linarith)]
    norm_num
  have b0 : roundFixed 0 1 0 = 0 := by
    rw [roundFixed_eq_of_floor (n := 0) (by norm_num)]
    norm_num
  have b1 : roundFixed 0 1 (1 / 4) = 1 / 2 := by
    rw [roundFixed_eq_of_floor (n := 1) (by norm_num)]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [roundFixed_eq_of_floor (n := 0) (by constructor <;> norm_num <;> linarith)]
    norm_num
  · rw [a1, a2, b0, b1, zero_add]
  · rw [a1, a2, zero_add, b1]

end MLMC
