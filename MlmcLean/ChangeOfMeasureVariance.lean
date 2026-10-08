import MlmcLean.SDEDigital
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Finite variance of the change-of-measure correction (Giles 2015, §5.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.2, p. 38
(`docs/giles2015.txt`, l. 1637–1649; the line numbers below refer to it).  Row G5.2-21.

**Setting.**  "Using the Euler-Maruyama approximation for the final timestep, the fine and coarse
path conditional distributions at maturity are two very similar Gaussian distributions.  Instead of
following the splitting approach of taking corresponding samples from these two distributions, we
can take a sample from a third Gaussian distribution (with a mean and variance perhaps equal to the
average of the other two).  This leads to the introduction of a Radon-Nikodym derivative for each
path, and the difference in the payoffs from the two paths is then due to the difference in their
Radon-Nikodym derivatives" (l. 1637–1646).  With fine and coarse conditional laws `N(m_f, v_f)`,
`N(m_c, v_c)`, the sampling law `N(m, v)` (all variances nonzero, `ℝ≥0` as in Mathlib's
`gaussianReal`), the densities `φ_{m,v} = gaussianPDFReal m v` and the weights
`L_f = φ_{m_f,v_f}/φ_{m,v}`, `L_c = φ_{m_c,v_c}/φ_{m,v}`, the level correction is
`g(Z)(L_f(Z) − L_c(Z))`, `Z ∼ N(m, v)`.  Its unbiasedness is `gaussian_change_of_measure`,
`integral_mul_likelihoodRatio` and `integral_mul_sub_likelihoodRatio` (`MlmcLean.SDEDigital`, same
notation).  This file proves that each weight `L_f` is in `L²` exactly when `v_f < 2v`, that the
correction is in `L²` when `v_f, v_c < 2v` (bounded `g`), and that it is not in `L²` when exactly
one of these conditions fails (for `|g| ≥ c > 0`).  For the correction itself the condition is
sufficient but not necessary in general: the trivial case `m_f = m_c`, `v_f = v_c` gives the
correction `0`, and for the digital payoff `g = 1_{z>0}` with `m = 0`, `v = 1`, `m_f = −1`,
`v_f = 2`, `m_c = 0`, `v_c = 1` the correction is in `L²` although `v_f = 2v`.

* `memLp_two_likelihoodRatio_iff`: `L_f ∈ L²(N(m, v))` iff `v_f < 2v`.
* `integral_likelihoodRatio_sq`: then `E[L_f²] = v/√(v_f(2v − v_f)) · exp((m_f − m)²/(2v − v_f))`.
* `memLp_two_mul_sub_likelihoodRatio`: for bounded measurable `g`, `v_f < 2v` and `v_c < 2v`, the
  correction `g(Z)(L_f(Z) − L_c(Z))` is in `L²(N(m, v))`.
* `changeOfMeasure_average_memLp_two`: the paper's choice `m = (m_f + m_c)/2`,
  `v = (v_f + v_c)/2` always satisfies `v_f, v_c < 2v`; so the correction is in `L²` and its mean is
  `E_{N(m_f,v_f)}[g] − E_{N(m_c,v_c)}[g]`.
* `not_memLp_two_mul_sub_likelihoodRatio`: for payoffs bounded away from `0` the condition is
  needed: if `v_f ≥ 2v` and `v_c < 2v`, the correction is not in `L²` for any `g` with
  `|g| ≥ c > 0` (e.g. `g ≡ 1`).

**Deviations.**  The payoff `g` is bounded and measurable (as the digital payoff `1_{x > K}` of
§5.2 is); the converse is stated for payoffs bounded away from `0`, which excludes the digital
payoff (it vanishes on a half-line).  The means and variances are arbitrary; the specific values
produced by the final Euler–Maruyama step are not substituted.  All statements are conditional on
the path, i.e. for fixed `m_f, v_f, m_c, v_c`: with the averaged choice
`E[L_f²] = (v_f + v_c)/(2√(v_f v_c)) · exp((m_f − m_c)²/(4v_c))`, which is unbounded as
`v_c/v_f → 0`, so finiteness of the variance after averaging over the paths does not follow
from these results.

**Not proved.**  The variance rate of the change-of-measure estimator for the digital option
("the resulting variance is no better", l. 1647–1649) and its cost.
-/
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MLMC

/-! ### The second moment of one Radon–Nikodym weight -/

/-- `φ_{m,v} (φ_{m_f,v_f}/φ_{m,v})² = φ_{m_f,v_f}²/φ_{m,v}` written out (Giles 2015, §5.2, p. 38,
l. 1643–1644: "This leads to the introduction of a Radon-Nikodym derivative for each path"). -/
lemma pdf_mul_likelihoodRatio_sq {m mf : ℝ} {v vf : ℝ≥0} (hv : v ≠ 0) (hvf : vf ≠ 0) (z : ℝ) :
    gaussianPDFReal m v z * (gaussianPDFReal mf vf z / gaussianPDFReal m v z) ^ 2 =
      Real.sqrt (2 * Real.pi * v) / (2 * Real.pi * vf) *
        Real.exp (-(z - mf) ^ 2 / vf + (z - m) ^ 2 / (2 * v)) := by
  have hφ := (gaussianPDFReal_pos m v z hv).ne'
  have hv' : (0 : ℝ) < v := by positivity
  have hvf' : (0 : ℝ) < vf := by positivity
  have h1 : gaussianPDFReal m v z * (gaussianPDFReal mf vf z / gaussianPDFReal m v z) ^ 2 =
      gaussianPDFReal mf vf z ^ 2 / gaussianPDFReal m v z := by
    field_simp
  rw [h1]
  simp only [gaussianPDFReal]
  have hexp : Real.exp (-(z - mf) ^ 2 / vf + (z - m) ^ 2 / (2 * v)) =
      Real.exp (-(z - mf) ^ 2 / (2 * vf)) ^ 2 / Real.exp (-(z - m) ^ 2 / (2 * v)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    push_cast
    field_simp
    ring
  rw [hexp]
  have hs : Real.sqrt (2 * Real.pi * vf) ^ 2 = 2 * Real.pi * vf := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * Real.pi * v) ≠ 0 := by positivity
  have hs1 : Real.sqrt (2 * Real.pi * vf) ≠ 0 := by positivity
  field_simp
  rw [hs]

/-- Completing the square in the exponent of `φ_f²/φ` (for Giles 2015, §5.2, p. 38,
l. 1643–1644). -/
lemma likelihoodRatio_exponent_completeSquare {m mf a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : b ≠ 2 * a) (z : ℝ) :
    -(z - mf) ^ 2 / b + (z - m) ^ 2 / (2 * a) =
      -((2 * a - b) / (2 * a * b)) * (z - (2 * a * mf - b * m) / (2 * a - b)) ^ 2 +
        (mf - m) ^ 2 / (2 * a - b) := by
  have h2 : 2 * a - b ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  field_simp
  ring

/-- For `v_f ≥ 2v` the exponent of `φ_f²/φ` is at least a linear function (for Giles 2015, §5.2,
p. 38, l. 1643–1644). -/
lemma likelihoodRatio_exponent_ge {m mf a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : 2 * a ≤ b)
    (z : ℝ) :
    (mf - m) * (2 * z - m - mf) / b ≤ -(z - mf) ^ 2 / b + (z - m) ^ 2 / (2 * a) := by
  have h1 : (z - m) ^ 2 / b ≤ (z - m) ^ 2 / (2 * a) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hab
  have h2 : (mf - m) * (2 * z - m - mf) / b = -(z - mf) ^ 2 / b + (z - m) ^ 2 / b := by
    field_simp
    ring
  linarith

/-- For `v_f < 2v`, `∫ φ_f²/φ dz` is a Gaussian integral (for Giles 2015, §5.2, p. 38,
l. 1641–1644). -/
lemma integral_pdf_mul_likelihoodRatio_sq {m mf : ℝ} {v vf : ℝ≥0} (hv : v ≠ 0) (hvf : vf ≠ 0)
    (h : vf < 2 * v) :
    Integrable (fun z => gaussianPDFReal m v z *
        (gaussianPDFReal mf vf z / gaussianPDFReal m v z) ^ 2) ∧
      ∫ z, gaussianPDFReal m v z * (gaussianPDFReal mf vf z / gaussianPDFReal m v z) ^ 2 =
        v / Real.sqrt (vf * (2 * v - vf)) * Real.exp ((mf - m) ^ 2 / (2 * v - vf)) := by
  have ha : (0 : ℝ) < v := by positivity
  have hb : (0 : ℝ) < vf := by positivity
  have hlt : (vf : ℝ) < 2 * v := by exact_mod_cast h
  have hd : (0 : ℝ) < 2 * v - vf := by linarith
  set α : ℝ := (2 * v - vf) / (2 * v * vf) with hα
  have hα0 : 0 < α := by positivity
  set c : ℝ := (2 * v * mf - vf * m) / (2 * v - vf)
  set d : ℝ := (mf - m) ^ 2 / (2 * v - vf)
  set C : ℝ := Real.sqrt (2 * Real.pi * v) / (2 * Real.pi * vf)
  have hfun : (fun z => gaussianPDFReal m v z *
      (gaussianPDFReal mf vf z / gaussianPDFReal m v z) ^ 2) =
      fun z => C * Real.exp d * Real.exp (-α * (z - c) ^ 2) := by
    funext z
    rw [pdf_mul_likelihoodRatio_sq hv hvf, likelihoodRatio_exponent_completeSquare ha hb hlt.ne,
      Real.exp_add]
    ring
  rw [hfun]
  refine ⟨((integrable_exp_neg_mul_sq hα0).comp_sub_right c).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub_right_eq_self (fun z => Real.exp (-α * z ^ 2)) c,
    integral_gaussian]
  have hkey : C * Real.sqrt (Real.pi / α) = v / Real.sqrt (vf * (2 * v - vf)) := by
    have hC : 0 ≤ C := by positivity
    rw [← sq_eq_sq₀ (by positivity) (by positivity), mul_pow, div_pow, div_pow,
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    rw [hα]
    field_simp
  rw [← hkey]
  ring

/-- For `v_f ≥ 2v`, `φ_f²/φ` is bounded below on a half-line, so it is not Lebesgue integrable
(for Giles 2015, §5.2, p. 38, l. 1641–1644). -/
lemma not_integrable_pdf_mul_likelihoodRatio_sq {m mf : ℝ} {v vf : ℝ≥0} (hv : v ≠ 0)
    (hvf : vf ≠ 0) (h : 2 * v ≤ vf) :
    ¬ Integrable (fun z => gaussianPDFReal m v z *
        (gaussianPDFReal mf vf z / gaussianPDFReal m v z) ^ 2) := by
  have ha : (0 : ℝ) < v := by positivity
  have hb : (0 : ℝ) < vf := by positivity
  have hle : 2 * (v : ℝ) ≤ vf := by exact_mod_cast h
  set C : ℝ := Real.sqrt (2 * Real.pi * v) / (2 * Real.pi * vf)
  have hC : 0 < C := by positivity
  intro hint
  have hfin := hint.measure_norm_ge_lt_top hC
  set S : Set ℝ := {z | 0 ≤ (mf - m) * (2 * z - m - mf)}
  have hsub : S ⊆ {z | C ≤ ‖gaussianPDFReal m v z *
      (gaussianPDFReal mf vf z / gaussianPDFReal m v z) ^ 2‖} := by
    intro z hz
    have hz' : 0 ≤ (mf - m) * (2 * z - m - mf) := hz
    show C ≤ _
    rw [pdf_mul_likelihoodRatio_sq hv hvf, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    have hq : 0 ≤ -(z - mf) ^ 2 / vf + (z - m) ^ 2 / (2 * v) :=
      le_trans (div_nonneg hz' hb.le) (likelihoodRatio_exponent_ge ha hb hle z)
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp (-(z - mf) ^ 2 / vf + (z - m) ^ 2 / (2 * v)) := by
        gcongr
        exact Real.one_le_exp hq
  have htop : volume S = ⊤ := by
    rcases le_total m mf with hm | hm
    · refine measure_mono_top (fun z hz => ?_) (Real.volume_Ici (a := (m + mf) / 2))
      have hz' : (m + mf) / 2 ≤ z := hz
      show 0 ≤ (mf - m) * (2 * z - m - mf)
      nlinarith
    · refine measure_mono_top (fun z hz => ?_) (Real.volume_Iic (a := (m + mf) / 2))
      have hz' : z ≤ (m + mf) / 2 := hz
      show 0 ≤ (mf - m) * (2 * z - m - mf)
      nlinarith
  exact (measure_mono_top hsub htop).not_lt hfin |>.elim

/-- **The Radon–Nikodym weight has finite variance iff the sampling Gaussian is wide enough**
(Giles 2015, §5.2, p. 38, l. 1641–1644: "we can take a sample from a third Gaussian distribution …
This leads to the introduction of a Radon-Nikodym derivative for each path").  For nonzero
variances, the weight `L = φ_{m_f,v_f}/φ_{m,v}` (`= dN(m_f, v_f)/dN(m, v)`) of a sample
`Z ∼ N(m, v)` is in `L²(N(m, v))` if and only if `v_f < 2v`. -/
theorem memLp_two_likelihoodRatio_iff {m mf : ℝ} {v vf : ℝ≥0} (hv : v ≠ 0) (hvf : vf ≠ 0) :
    MemLp (fun z => gaussianPDFReal mf vf z / gaussianPDFReal m v z) 2 (gaussianReal m v) ↔
      vf < 2 * v := by
  have hmeas : AEStronglyMeasurable (fun z => gaussianPDFReal mf vf z / gaussianPDFReal m v z)
      (gaussianReal m v) :=
    ((measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas, integrable_gaussianReal_iff_mul_pdf hv]
  constructor
  · intro hint
    by_contra hle
    exact not_integrable_pdf_mul_likelihoodRatio_sq hv hvf (not_lt.1 hle) hint
  · exact fun h => (integral_pdf_mul_likelihoodRatio_sq hv hvf h).1

/-- **The second moment of the Radon–Nikodym weight** (Giles 2015, §5.2, p. 38, l. 1641–1644:
"a sample from a third Gaussian distribution … This leads to the introduction of a Radon-Nikodym
derivative for each path").  For nonzero variances with `v_f < 2v`, `L = φ_{m_f,v_f}/φ_{m,v}`
has `L²` integrable under `N(m, v)` and
`E_{N(m,v)}[L²] = v/√(v_f(2v − v_f)) · exp((m_f − m)²/(2v − v_f))`. -/
theorem integral_likelihoodRatio_sq {m mf : ℝ} {v vf : ℝ≥0} (hv : v ≠ 0) (hvf : vf ≠ 0)
    (h : vf < 2 * v) :
    Integrable (fun z => (gaussianPDFReal mf vf z / gaussianPDFReal m v z) ^ 2)
        (gaussianReal m v) ∧
      ∫ z, (gaussianPDFReal mf vf z / gaussianPDFReal m v z) ^ 2 ∂gaussianReal m v =
        v / Real.sqrt (vf * (2 * v - vf)) * Real.exp ((mf - m) ^ 2 / (2 * v - vf)) := by
  obtain ⟨hi, he⟩ := integral_pdf_mul_likelihoodRatio_sq (m := m) (mf := mf) hv hvf h
  refine ⟨(integrable_gaussianReal_iff_mul_pdf hv).2 hi, ?_⟩
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  exact he

/-! ### The level correction -/

/-- **The change-of-measure correction has finite variance** (Giles 2015, §5.2, p. 38,
l. 1641–1646: "we can take a sample from a third Gaussian distribution … the difference in the
payoffs from the two paths is then due to the difference in their Radon-Nikodym derivatives").
For nonzero variances with `v_f < 2v` and `v_c < 2v` and a bounded measurable payoff `g`, the
correction `g(Z)(φ_{m_f,v_f}(Z)/φ_{m,v}(Z) − φ_{m_c,v_c}(Z)/φ_{m,v}(Z))` is in
`L²(N(m, v))`. -/
theorem memLp_two_mul_sub_likelihoodRatio {m mf mc : ℝ} {v vf vc : ℝ≥0} (hv : v ≠ 0)
    (hvf : vf ≠ 0) (hvc : vc ≠ 0) (hf : vf < 2 * v) (hc : vc < 2 * v) {g : ℝ → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ z, |g z| ≤ C) :
    MemLp (fun z => g z * (gaussianPDFReal mf vf z / gaussianPDFReal m v z -
      gaussianPDFReal mc vc z / gaussianPDFReal m v z)) 2 (gaussianReal m v) := by
  have hLf := (memLp_two_likelihoodRatio_iff (m := m) (mf := mf) hv hvf).2 hf
  have hLc := (memLp_two_likelihoodRatio_iff (m := m) (mf := mc) hv hvc).2 hc
  have hD := (hLf.sub hLc).const_mul C
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine hD.of_le ?_ (ae_of_all _ fun z => ?_)
  · exact (hg.mul (((measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _)).sub
      ((measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _)))).aestronglyMeasurable
  · simp only [Pi.sub_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC0]
    exact mul_le_mul_of_nonneg_right (hC z) (abs_nonneg _)

/-- **The paper's third Gaussian gives an unbiased correction with finite variance** (Giles 2015,
§5.2, p. 38, l. 1641–1646: "we can take a sample from a third Gaussian distribution (with a mean
and variance perhaps equal to the average of the other two). This leads to the introduction of a
Radon-Nikodym derivative for each path, and the difference in the payoffs from the two paths is
then due to the difference in their Radon-Nikodym derivatives").  For nonzero `v_f, v_c`, the
sampling law `N((m_f + m_c)/2, (v_f + v_c)/2)` satisfies `v_f < 2v` and `v_c < 2v`, so for every
bounded measurable `g` the correction `g(Z)(L_f(Z) − L_c(Z))` is in `L²` and has the mean
`E_{N(m_f,v_f)}[g] − E_{N(m_c,v_c)}[g]` of the fine minus the coarse payoff. -/
theorem changeOfMeasure_average_memLp_two {mf mc : ℝ} {vf vc : ℝ≥0} (hvf : vf ≠ 0)
    (hvc : vc ≠ 0) {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ z, |g z| ≤ C) :
    vf < 2 * ((vf + vc) / 2) ∧ vc < 2 * ((vf + vc) / 2) ∧
      MemLp (fun z => g z *
        (gaussianPDFReal mf vf z / gaussianPDFReal ((mf + mc) / 2) ((vf + vc) / 2) z -
          gaussianPDFReal mc vc z / gaussianPDFReal ((mf + mc) / 2) ((vf + vc) / 2) z)) 2
        (gaussianReal ((mf + mc) / 2) ((vf + vc) / 2)) ∧
      ∫ z, g z * (gaussianPDFReal mf vf z / gaussianPDFReal ((mf + mc) / 2) ((vf + vc) / 2) z -
          gaussianPDFReal mc vc z / gaussianPDFReal ((mf + mc) / 2) ((vf + vc) / 2) z)
          ∂gaussianReal ((mf + mc) / 2) ((vf + vc) / 2) =
        ∫ z, g z ∂gaussianReal mf vf - ∫ z, g z ∂gaussianReal mc vc := by
  have h2 : 2 * ((vf + vc) / 2) = vf + vc := mul_div_cancel₀ _ two_ne_zero
  have hf : vf < 2 * ((vf + vc) / 2) := by
    rw [h2]
    exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hvc)
  have hc : vc < 2 * ((vf + vc) / 2) := by
    rw [h2]
    exact lt_add_of_pos_left _ (pos_iff_ne_zero.2 hvf)
  have hv : (vf + vc) / 2 ≠ 0 :=
    div_ne_zero (fun h0 => hvf (add_eq_zero.1 h0).1) two_ne_zero
  have hgi : ∀ m' (v' : ℝ≥0), Integrable g (gaussianReal m' v') := fun m' v' =>
    Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ fun z => (hC z))
  exact ⟨hf, hc, memLp_two_mul_sub_likelihoodRatio hv hvf hvc hf hc hg hC,
    integral_mul_sub_likelihoodRatio hv hvf hvc (hgi _ _) (hgi _ _)⟩

/-- **A too narrow sampling Gaussian gives infinite variance** (Giles 2015, §5.2, p. 38,
l. 1641–1646: "we can take a sample from a third Gaussian distribution (with a mean and variance
perhaps equal to the average of the other two)").  If `v_f ≥ 2v` while `v_c < 2v`, then for every
payoff with `|g| ≥ c > 0` (for example `g ≡ 1`) the correction
`g(Z)(φ_{m_f,v_f}(Z)/φ_{m,v}(Z) − φ_{m_c,v_c}(Z)/φ_{m,v}(Z))` is not in `L²(N(m, v))`. -/
theorem not_memLp_two_mul_sub_likelihoodRatio {m mf mc : ℝ} {v vf vc : ℝ≥0} (hv : v ≠ 0)
    (hvf : vf ≠ 0) (hvc : vc ≠ 0) (hf : 2 * v ≤ vf) (hc : vc < 2 * v) {g : ℝ → ℝ} {c : ℝ}
    (hc0 : 0 < c) (hgc : ∀ z, c ≤ |g z|) :
    ¬ MemLp (fun z => g z * (gaussianPDFReal mf vf z / gaussianPDFReal m v z -
      gaussianPDFReal mc vc z / gaussianPDFReal m v z)) 2 (gaussianReal m v) := by
  intro hG
  have hLc := (memLp_two_likelihoodRatio_iff (m := m) (mf := mc) hv hvc).2 hc
  have hmeas : AEStronglyMeasurable (fun z => gaussianPDFReal mf vf z / gaussianPDFReal m v z -
      gaussianPDFReal mc vc z / gaussianPDFReal m v z) (gaussianReal m v) :=
    (((measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _)).sub
      ((measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _))).aestronglyMeasurable
  have hD : MemLp (fun z => gaussianPDFReal mf vf z / gaussianPDFReal m v z -
      gaussianPDFReal mc vc z / gaussianPDFReal m v z) 2 (gaussianReal m v) := by
    refine (hG.const_mul c⁻¹).of_le hmeas (ae_of_all _ fun z => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hc0]
    calc |gaussianPDFReal mf vf z / gaussianPDFReal m v z -
          gaussianPDFReal mc vc z / gaussianPDFReal m v z|
        = c⁻¹ * (c * |gaussianPDFReal mf vf z / gaussianPDFReal m v z -
          gaussianPDFReal mc vc z / gaussianPDFReal m v z|) := by field_simp
      _ ≤ c⁻¹ * (|g z| * |gaussianPDFReal mf vf z / gaussianPDFReal m v z -
          gaussianPDFReal mc vc z / gaussianPDFReal m v z|) := by
        gcongr
        exact hgc z
  have hLf : MemLp (fun z => gaussianPDFReal mf vf z / gaussianPDFReal m v z) 2
      (gaussianReal m v) := by
    refine (hD.add hLc).ae_eq (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply, sub_add_cancel]
  exact (not_lt.2 hf) ((memLp_two_likelihoodRatio_iff hv hvf).1 hLf)

end MLMC
