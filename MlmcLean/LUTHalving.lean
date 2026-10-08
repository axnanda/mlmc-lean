import MlmcLean.InverseNormal
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# The method-1 MSE for `Φ⁻¹` halves per bit: `MSE(d + 1)/MSE(d) → 1/2` (Haas–Giles 2025, §3.4)

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), §3.4 "Comparison of the three inversion methods", p. 7
(`docs/haas_giles2025.txt`, l. 351–379; coverage row H3-30): "The Figure 1 also illustrates that
both method 1 and 2 have their MSE divided by 2 each time `d` increases by 1. This was
theoretically expected for method 1 (see [12])" (l. 377–379).  Method 1 (§3.1, p. 5, l. 248–264)
replaces `Φ⁻¹` on each uniform cell `I_j = [2^{−d} j, 2^{−d}(j + 1)]` by its mean
`Z_j = 2^d ∫_{I_j} Φ⁻¹` ((15)), the minimiser of the cell MSE (14); `method1MSE Φ⁻¹ d` is the sum
of the cell errors `E_j(d) = ∫_{I_j} (Z_j − Φ⁻¹)²` over the `2^d` cells of `[0, 1]`.

`MlmcLean/LUTAsymptotics.lean` and `MlmcLean/InverseNormal.lean` prove the order
`c 2^{−d}/d ≤ MSE(d) ≤ K 2^{−d}/d` (`method1MSE_order_normCDFInv`), which gives the halving only
up to a bounded factor.  This file proves the exact limit.

**Main results** (all for the actual `f = Φ⁻¹ = normCDFInv`, with no hypotheses):
* `tendsto_mul_method1MSE_normCDFInv`: `d 2^d MSE(d) → κ = S/log 2`, `S = ∑_{j ≥ 0} V_j`, where
  `V_j = ∫_j^{j+1} (log t)² dt − (∫_j^{j+1} log t dt)²` is the variance of `log` on `[j, j + 1]`
  (`logCellVar`; the series converges, `summable_logCellVar`); `κ > 0`
  (`method1MSE_normCDFInv_const_pos`); equivalently `MSE(d) ~ κ 2^{−d}/d`
  (`isEquivalent_method1MSE_normCDFInv`);
* `tendsto_method1MSE_succ_div_normCDFInv`: `MSE(d + 1)/MSE(d) → 1/2`, the paper's halving.

**Which cells carry the error.**  Not the interior: there `E_j ≈ 2^{−3d} (Φ⁻¹)'(u_j)²/12`, and since
`(Φ⁻¹)'(u) ≈ 1/(u √(2 log(1/u)))`, the cells `2^{⌊d/2⌋} ≤ j < 2^{d−1}` (and their mirror images)
together give only `O(2^{−d} 2^{−d/2})` (`method1_tail_le`).  The MSE sits in the cells within a
bounded distance of the ends, each with a definite share: `d 2^d E_j(d) → V_j/(2 log 2)` for every
fixed `j` (`tendsto_method1CellErr_normCDFInv`; by the sign bit the cells at `1` mirror those at
`0`). The reason is the profile of `Φ⁻¹` near `0`: with `G_d(t) = (Φ⁻¹(t 2^{−d}) − Φ⁻¹(2^{−d}))
|Φ⁻¹(2^{−d})|`, `G_d(t) → log t` for every `t > 0` (`tendsto_lutScaled`) and
`Φ⁻¹(2^{−d})² ~ 2 d log 2` (`tendsto_natCast_div_sq_normCDFInv`), and
`d 2^d E_j(d) = (d/Φ⁻¹(2^{−d})²) (∫_j^{j+1} G_d² − (∫_j^{j+1} G_d)²)`
(`lutScaled_cell_identity`).  The two end cells carry `V_0/S = 1/S ≈ 93 %` of the limit; the
cells `j ≥ 1` (`V_j ≈ 1/(12 (j + 1/2)²)`, the interior formula `h² (Φ⁻¹)'²/12` in the variable
`t`) carry the remaining `≈ 7 %`, so the leading term comes from a whole range of cells near the
ends; the cells `j ≥ J` still carry about `1/(12 J S)` of the limit, so the shares are tight
rather than supported on a range of bounded length.

**Proof.**
1. *Sharp Mills ratio* (`neg_mul_gaussianPDFReal_le_one_add_sq_mul`):
   `|x| φ(x) ≤ (1 + x²) Φ(x)` for `x ≤ 0`, complementing `|x| Φ(x) ≤ φ(x)`
   (`neg_mul_normCDF_le`).
2. *Two-point bounds* (mean value theorem for `log Φ`, whose derivative `φ/Φ` lies in
   `[|ξ|, |ξ| + 1/|ξ|]`): for `0 < u ≤ v < 1/2`, with `x = Φ⁻¹(u) ≤ y = Φ⁻¹(v) < 0`,
   `(y − x)|y| ≤ log(v/u) ≤ (y − x)(|x| + 1/|y|)` (`normCDFInv_sub_mul_le`,
   `log_sub_le_normCDFInv_sub_mul`).  They give `|G_d(t) − log t| ≤ ((log t)² + |log t|)/
   Φ⁻¹(max(t, 1) 2^{−d})²` and the domination `|G_d| ≤ 2 |log|` on each cell, eventually.
3. *Growth*: `Φ⁻¹(u)² ≤ −2 log u` and `−2 log u ≤ (1 − Φ⁻¹(u))² + 2 log 4` for small `u`.
4. *Each cell*: dominated convergence on `[j, j + 1]` (`(log)²` is integrable on `[0, 1]`).
5. *All cells*: Tannery's theorem (`tendsto_sum_range_of_dominated`) over `j < 2^{⌊d/2⌋}` with the
   summable bound `B/(j + 1)²` (`method1CellErr_dom`, from the two-point bound and, for `j = 0`,
   `end_cell_method1_le`), and `d 2^d · (blocks beyond) ≤ (K/2) d 2^{−⌊d/2⌋} → 0`
   (`group_method1_le`).  Then the ratio is
   `MSE(d + 1)/MSE(d) = [(d + 1) 2^{d+1} MSE(d + 1)]/[d 2^d MSE(d)] · d/(2(d + 1)) → 1/2`.

**Numerical check** (mpmath; not part of the proof).  `S = 1.0803270395…`, `κ = S/log 2 =
1.5585824624…` (`V_0 = 1`, `V_1 = 0.03909`, `V_2 = 0.01359`).  From the exact cell integrals
(`∫ Φ⁻¹ = −φ(Φ⁻¹)`, `∫ (Φ⁻¹)² = u − Φ⁻¹ φ(Φ⁻¹)`): `d 2^d MSE(d) = 1.5328, 1.5525, 1.5568` for
`d = 10, 16, 18`, and (first 400 cells exactly, the rest by `h² ∫ (Φ⁻¹)'²/12`) `1.5743, 1.5734,
1.5603, 1.5592, 1.5587, 1.55859` for `d = 50, 100, 3000, 10⁴, 10⁵, 10⁶`: the limit `κ` is
approached slowly (relative corrections numerically of order `log d/d`) and not monotonically.
`MSE(d + 1)/MSE(d) = 0.4514, 0.4695, 0.4728` for `d = 9, 15, 17`, i.e. `≈ ½ · d/(d + 1)`.  A
heuristic replacing `S` by `1 + 1/12` gives `13/(12 log 2) ≈ 1.5629`, `0.28 %` too high; the
exact constant is `S/log 2 ≈ 1.5586`.

**The MSE.**  `method1MSE` sums over all `2^d` cells of `[0, 1]`; the paper's table covers
`[0, 1/2]` and gets `[1/2, 1]` from the sign bit (§3.1, l. 249–253).  By the odd symmetry of `Φ⁻¹`,
`method1MSE` is exactly the paper's MSE `E|Z − Z̃|²` (§4, l. 506), twice the sum of (14) over the
`2^{d−1}` table cells; it reproduces the method-1 values of Figure 1 to 4–5 digits.

**Deviations.**  The paper's statement is read from Figure 1 (`d = 8, …, 16`); what is proved is the
limit `d → ∞`, and at finite `d` the ratio is numerically below `1/2` (within `0.4 %` of
`½ · d/(d + 1)` for `d = 9, …, 17`).  The constant `κ` is given as the series `S/log 2`, not in
closed form.  `normCDFInv` takes the junk value `0` outside `(0, 1)` and `log 0 = 0`; both only
occur on null sets inside the integrals.

**Not proved.**  A rate of convergence (e.g. `MSE(d + 1)/MSE(d) = ½ (1 − 1/d) + O(log d/d²)`, as
the numerical values suggest), a closed form of `S`, and the halving for method 2 (H3-31, which
the paper calls only "intuitively true for method 2 after the optimisation stage", l. 379–380).
-/

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace MLMC

/-! ### The sharp Mills ratio and two-point bounds for `log Φ` -/

/-- The auxiliary function `g(z) = (1 + z²) Φ(z) + z φ(z)` of the lower Mills-ratio bound has
derivative `2 (φ(z) + z Φ(z))` (from `Φ' = φ` and `φ' = −z φ`). -/
lemma hasDerivAt_millsLowerAux (z : ℝ) :
    HasDerivAt (fun w => (1 + w ^ 2) * normCDF w + w * gaussianPDFReal 0 1 w)
      (2 * (gaussianPDFReal 0 1 z + z * normCDF z)) z := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + w ^ 2) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z).const_add 1
  have h2 := h1.mul (hasDerivAt_normCDF z)
  have h3 := (hasDerivAt_id z).mul (hasDerivAt_gaussianPDFReal_std z)
  refine (h2.add h3).congr_deriv ?_
  simp only [id]
  ring

/-- `z² φ(z) ≤ 1` for every real `z` (as `z² e^{−z²/2} ≤ 2` and `√(2π) ≥ 2`). -/
lemma sq_mul_gaussianPDFReal_le (w : ℝ) : w ^ 2 * gaussianPDFReal 0 1 w ≤ 1 := by
  rw [gaussianPDFReal_std]
  have hs : (2 : ℝ) ≤ √(2 * π) := (Real.le_sqrt' (by norm_num)).2 (by nlinarith [two_le_pi])
  have hinv : (√(2 * π))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have he := Real.add_one_le_exp (w ^ 2 / 2)
  have hm : Real.exp (-w ^ 2 / 2) * Real.exp (w ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hpos := Real.exp_pos (-w ^ 2 / 2)
  have h2 : w ^ 2 * Real.exp (-w ^ 2 / 2) ≤ 2 := by nlinarith [sq_nonneg w]
  have h0 : 0 ≤ w ^ 2 * Real.exp (-w ^ 2 / 2) := by positivity
  have hi0 : 0 ≤ (√(2 * π))⁻¹ := by positivity
  calc w ^ 2 * ((√(2 * π))⁻¹ * Real.exp (-w ^ 2 / 2))
      = (√(2 * π))⁻¹ * (w ^ 2 * Real.exp (-w ^ 2 / 2)) := by ring
    _ ≤ 1 / 2 * 2 := mul_le_mul hinv h2 h0 (by norm_num)
    _ = 1 := by norm_num

/-- **The sharp lower Mills-ratio bound** (a standard estimate, not stated in the paper; used here
for Haas–Giles 2025, §3.4, p. 7, l. 377–379, H3-30: "The Figure 1 also illustrates that both method
1 and 2 have their MSE divided by 2 each time `d` increases by 1. This was theoretically expected
for method 1 (see [12])"): `|z| φ(z) ≤ (1 + z²) Φ(z)` for `z ≤ 0`, i.e. `Φ(z) ≥ φ(z) |z|/(1 + z²)`
(the statement holds, trivially, for `z ≥ 0` too). Together with the upper bound `|z| Φ(z) ≤ φ(z)`
it gives `Φ(z) ~ φ(z)/|z|` as `z → −∞`. Proof: `g(z) = (1 + z²) Φ(z) + z φ(z)` has
`g' = 2(φ + zΦ) ≥ 0`, and `g(w) ≥ w φ(w) ≥ −1/|w| → 0` as `w → −∞`. -/
theorem neg_mul_gaussianPDFReal_le_one_add_sq_mul (z : ℝ) :
    -z * gaussianPDFReal 0 1 z ≤ (1 + z ^ 2) * normCDF z := by
  set g : ℝ → ℝ := fun w => (1 + w ^ 2) * normCDF w + w * gaussianPDFReal 0 1 w with hg
  have hmono : Monotone g := by
    refine monotone_of_deriv_nonneg (fun w => (hasDerivAt_millsLowerAux w).differentiableAt)
      fun w => ?_
    rw [(hasDerivAt_millsLowerAux w).deriv]
    have := neg_mul_normCDF_le w
    linarith
  suffices h : 0 ≤ g z by simp only [hg] at h; linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set w : ℝ := -(|z| + 1 / ε + 1) with hw
  have hw0 : 0 < -w := by rw [hw, neg_neg]; positivity
  have hwz : w ≤ z := by rw [hw]; linarith [neg_abs_le z, one_div_pos.2 hε]
  have hwε : 1 / ε ≤ -w := by rw [hw]; linarith [abs_nonneg z]
  have hφ := gaussianPDFReal_pos 0 1 w one_ne_zero
  have hsq := sq_mul_gaussianPDFReal_le w
  have h1 : -w * gaussianPDFReal 0 1 w ≤ ε := by
    have h2 : -w * gaussianPDFReal 0 1 w * (-w) ≤ 1 := by nlinarith
    have h3 : 1 ≤ ε * -w := by
      rw [div_le_iff₀ hε] at hwε; linarith
    nlinarith
  have hgw : w * gaussianPDFReal 0 1 w ≤ g w := by
    have : 0 ≤ (1 + w ^ 2) * normCDF w :=
      mul_nonneg (by positivity) (normCDF_mem_Ioo w).1.le
    simp only [hg]; linarith
  have := hmono hwz
  linarith

/-- The mean value theorem for `log Φ`, whose derivative is `φ/Φ`: for `x < y` there is
`ξ ∈ (x, y)` with `log Φ(y) − log Φ(x) = (y − x) φ(ξ)/Φ(ξ)`. -/
lemma exists_log_normCDF_slope {x y : ℝ} (hxy : x < y) : ∃ ξ ∈ Set.Ioo x y,
    Real.log (normCDF y) - Real.log (normCDF x) =
      (y - x) * (gaussianPDFReal 0 1 ξ / normCDF ξ) := by
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope (fun z => Real.log (normCDF z))
    (fun z => gaussianPDFReal 0 1 z / normCDF z) hxy
    (continuous_normCDF.continuousOn.log fun z _ => (normCDF_mem_Ioo z).1.ne')
    fun z _ => (hasDerivAt_normCDF z).log (normCDF_mem_Ioo z).1.ne'
  refine ⟨ξ, hξ, ?_⟩
  rw [hξd]
  field_simp [(sub_pos.2 hxy).ne']

/-- The lower two-point bound for `log Φ`: for `x ≤ y`,
`(y − x)(−y) ≤ log Φ(y) − log Φ(x)` (as `φ/Φ ≥ −ξ ≥ −y` on `[x, y]`, by `−ξ Φ(ξ) ≤ φ(ξ)`). -/
lemma mul_neg_le_log_normCDF_sub {x y : ℝ} (hxy : x ≤ y) :
    (y - x) * -y ≤ Real.log (normCDF y) - Real.log (normCDF x) := by
  rcases hxy.eq_or_lt with h | h
  · rw [h, sub_self, sub_self, zero_mul]
  obtain ⟨ξ, hξ, e⟩ := exists_log_normCDF_slope h
  have hΦ := (normCDF_mem_Ioo ξ).1
  have hr : -ξ ≤ gaussianPDFReal 0 1 ξ / normCDF ξ := by
    rw [le_div_iff₀ hΦ]; exact neg_mul_normCDF_le ξ
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith [hξ.2]) (sub_pos.2 h).le

/-- The upper two-point bound for `log Φ`: for `x ≤ y < 0`,
`log Φ(y) − log Φ(x) ≤ (y − x)(−x + 1/(−y))` (as `φ/Φ ≤ −ξ + 1/(−ξ)` by the sharp lower Mills
bound, and `−ξ ≤ −x`, `1/(−ξ) ≤ 1/(−y)` on `[x, y]`). -/
lemma log_normCDF_sub_le {x y : ℝ} (hxy : x ≤ y) (hy : y < 0) :
    Real.log (normCDF y) - Real.log (normCDF x) ≤ (y - x) * (-x + (-y)⁻¹) := by
  rcases hxy.eq_or_lt with h | h
  · rw [h, sub_self, sub_self, zero_mul]
  obtain ⟨ξ, hξ, e⟩ := exists_log_normCDF_slope h
  have hΦ := (normCDF_mem_Ioo ξ).1
  have hξ0 : 0 < -ξ := by linarith [hξ.2]
  have hM := neg_mul_gaussianPDFReal_le_one_add_sq_mul ξ
  have hr : gaussianPDFReal 0 1 ξ / normCDF ξ ≤ -ξ + (-ξ)⁻¹ := by
    rw [div_le_iff₀ hΦ]
    have e2 : (-ξ + (-ξ)⁻¹) * normCDF ξ = (1 + ξ ^ 2) * normCDF ξ / -ξ := by
      field_simp; ring
    rw [e2, le_div_iff₀ hξ0]
    linarith
  have hr2 : -ξ + (-ξ)⁻¹ ≤ -x + (-y)⁻¹ := by
    have h1 : (-ξ)⁻¹ ≤ (-y)⁻¹ := inv_anti₀ (by linarith) (by linarith [hξ.2])
    linarith [hξ.1]
  rw [e]
  exact mul_le_mul_of_nonneg_left (hr.trans hr2) (sub_pos.2 h).le

/-! ### Two-point bounds and growth of `Φ⁻¹` near `0` -/

/-- `Φ⁻¹(1/2) = 0`. -/
lemma normCDFInv_half : normCDFInv (1 / 2) = 0 := by
  rw [← normCDF_zero, normCDFInv_normCDF]

/-- `Φ⁻¹(v) < 0` for `0 < v < 1/2`. -/
lemma normCDFInv_neg {v : ℝ} (hv0 : 0 < v) (hv : v < 1 / 2) : normCDFInv v < 0 := by
  have h := strictMonoOn_normCDFInv ⟨hv0, by linarith⟩ ⟨by norm_num, by norm_num⟩ hv
  rwa [normCDFInv_half] at h

/-- `Φ⁻¹(v) ≤ 0` for `0 < v ≤ 1/2`. -/
lemma normCDFInv_nonpos {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 2) : normCDFInv v ≤ 0 := by
  rcases hv.lt_or_eq with h | h
  · exact (normCDFInv_neg hv0 h).le
  · rw [h, normCDFInv_half]

/-- `Φ⁻¹` is monotone on `(0, 1)`: `Φ⁻¹(u) ≤ Φ⁻¹(v)` for `0 < u ≤ v < 1`. -/
lemma normCDFInv_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) :
    normCDFInv u ≤ normCDFInv v :=
  strictMonoOn_normCDFInv.monotoneOn ⟨hu, by linarith⟩ ⟨by linarith, hv⟩ huv

/-- **The two-point bound for `Φ⁻¹`, upper half** (not stated in the paper; used here for Haas–Giles
2025, §3.4, p. 7, l. 377–379, H3-30: "The Figure 1 also illustrates that both method 1 and 2 have
their MSE divided by 2 each time `d` increases by 1. This was theoretically expected for method 1
(see [12])"): for `0 < u ≤ v < 1`, `(Φ⁻¹(v) − Φ⁻¹(u)) (−Φ⁻¹(v)) ≤ log v − log u`. So near `0` the
increments of `Φ⁻¹` are at most `log(v/u)/|Φ⁻¹(v)|`. -/
theorem normCDFInv_sub_mul_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) :
    (normCDFInv v - normCDFInv u) * -normCDFInv v ≤ Real.log v - Real.log u := by
  have h := mul_neg_le_log_normCDF_sub (normCDFInv_mono hu huv hv)
  rwa [normCDF_normCDFInv ⟨hu, by linarith⟩, normCDF_normCDFInv ⟨by linarith, hv⟩] at h

/-- **The two-point bound for `Φ⁻¹`, lower half** (not stated in the paper; used here for Haas–Giles
2025, §3.4, p. 7, l. 377–379, H3-30: "The Figure 1 also illustrates that both method 1 and 2 have
their MSE divided by 2 each time `d` increases by 1. This was theoretically expected for method 1
(see [12])"): for `0 < u ≤ v < 1/2`, `log v − log u ≤ (Φ⁻¹(v) − Φ⁻¹(u)) (−Φ⁻¹(u) + 1/(−Φ⁻¹(v)))`.
With the upper half it gives
`Φ⁻¹(v) − Φ⁻¹(u) = log(v/u)/|Φ⁻¹(v)| · (1 + O((1 + log(v/u))/Φ⁻¹(v)²))`. -/
theorem log_sub_le_normCDFInv_sub_mul {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1 / 2) :
    Real.log v - Real.log u ≤
      (normCDFInv v - normCDFInv u) * (-normCDFInv u + (-normCDFInv v)⁻¹) := by
  have h := log_normCDF_sub_le (normCDFInv_mono hu huv (by linarith))
    (normCDFInv_neg (by linarith) hv)
  rwa [normCDF_normCDFInv ⟨hu, by linarith⟩, normCDF_normCDFInv ⟨by linarith, by linarith⟩] at h

/-- `1/32 ≤ Φ(−1)` (from `Φ(−1) ≥ φ(−2) = e^{−2}/√(2π) ≥ (1/8)(1/4)`). -/
lemma inv_thirtytwo_le_normCDF_neg_one : (1 / 32 : ℝ) ≤ normCDF (-1) := by
  refine le_trans ?_ (gaussianPDFReal_sub_one_le_normCDF (by norm_num : (-1 : ℝ) ≤ 0))
  rw [gaussianPDFReal_std]
  have hs : √(2 * π) ≤ 4 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [pi_le_four]
  have hs0 : 0 < √(2 * π) := by positivity
  have hinv : 1 / 4 ≤ (√(2 * π))⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hs0 hs
  have he : 1 / 8 ≤ Real.exp (-(-1 - 1) ^ 2 / 2) := by
    have e : -(-1 - 1 : ℝ) ^ 2 / 2 = -2 := by norm_num
    rw [e, Real.exp_neg, one_div]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    exact inv_anti₀ (Real.exp_pos 2) (by nlinarith)
  nlinarith

/-- `Φ⁻¹(u) ≤ −1` for `0 < u ≤ 1/32`. -/
lemma normCDFInv_le_neg_one {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 32) : normCDFInv u ≤ -1 := by
  rw [normCDFInv_le_iff ⟨hu0, by linarith⟩]
  exact hu.trans inv_thirtytwo_le_normCDF_neg_one

/-- `Φ⁻¹(u)² ≤ −2 log u` for `0 < u ≤ 1/32` (from `Φ(x) ≤ φ(x)/|x| ≤ e^{−x²/2}` for
`x ≤ −1`). -/
lemma sq_normCDFInv_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 32) :
    normCDFInv u ^ 2 ≤ -2 * Real.log u := by
  have hx := normCDFInv_le_neg_one hu0 hu
  set x := normCDFInv u with hxdef
  have hΦ : normCDF x = u := normCDF_normCDFInv ⟨hu0, by linarith⟩
  have hM := neg_mul_normCDF_le x
  have hφe : gaussianPDFReal 0 1 x ≤ Real.exp (-x ^ 2 / 2) := by
    rw [gaussianPDFReal_std]
    have hs : (1 : ℝ) ≤ √(2 * π) := by
      rw [Real.one_le_sqrt]
      nlinarith [two_le_pi]
    have hinv : (√(2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
    have := Real.exp_pos (-x ^ 2 / 2)
    nlinarith
  have hle : u ≤ Real.exp (-x ^ 2 / 2) := by
    rw [← hΦ]; nlinarith
  have hlog := Real.log_le_log hu0 hle
  rw [Real.log_exp] at hlog
  linarith

/-- `−2 log u ≤ (1 − Φ⁻¹(u))² + 2 log 4` for `0 < u ≤ 1/2` (from
`Φ(x) ≥ φ(x − 1) ≥ e^{−(x−1)²/2}/4` for `x ≤ 0`). -/
lemma neg_two_mul_log_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) :
    -2 * Real.log u ≤ (1 - normCDFInv u) ^ 2 + 2 * Real.log 4 := by
  set x := normCDFInv u with hxdef
  have hx : x ≤ 0 := normCDFInv_nonpos hu0 hu
  have hΦ : normCDF x = u := normCDF_normCDFInv ⟨hu0, by linarith⟩
  have h1 := gaussianPDFReal_sub_one_le_normCDF hx
  rw [hΦ, gaussianPDFReal_std] at h1
  have hs : √(2 * π) ≤ 4 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [pi_le_four]
  have hs0 : 0 < √(2 * π) := by positivity
  have hinv : 1 / 4 ≤ (√(2 * π))⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hs0 hs
  have h2 : Real.exp (-(x - 1) ^ 2 / 2) / 4 ≤ u := by
    have := Real.exp_pos (-(x - 1) ^ 2 / 2)
    nlinarith
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h3
  nlinarith

/-- `−log u ≤ 4 Φ⁻¹(u)²` for `0 < u ≤ 1/32`. -/
lemma neg_log_le_four_mul_sq {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 32) :
    -Real.log u ≤ 4 * normCDFInv u ^ 2 := by
  have h1 := neg_two_mul_log_le hu0 (by linarith)
  have hx := normCDFInv_le_neg_one hu0 hu
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl := Real.log_two_lt_d9
  nlinarith

/-! ### The rescaled profile `G_d(t) → log t` -/

/-- The rescaled profile of `Φ⁻¹` near `0` at resolution `2^{−d}`:
`G_d(t) = (Φ⁻¹(t/2^d) − Φ⁻¹(1/2^d)) · (−Φ⁻¹(1/2^d))`, for `t > 0` (Haas–Giles 2025, §3.1, p. 5,
l. 249–251: the cell `I_j` of method 1 is `t ∈ [j, j + 1]` in the variable `t = 2^d u`).  As
`d → ∞` it tends to `log t`; for `t ≤ 0` it only involves the junk value of `normCDFInv`, which
the integrals over the cells never see (the point `t = 0` is a null set). -/
noncomputable def lutScaled (d : ℕ) (t : ℝ) : ℝ :=
  (normCDFInv (t / 2 ^ d) - normCDFInv (1 / 2 ^ d)) * -normCDFInv (1 / 2 ^ d)

/-- `log(1/2^d) − log(t/2^d) = −log t` for `t > 0`. -/
lemma log_one_div_two_pow_sub {t : ℝ} (ht : 0 < t) (d : ℕ) :
    Real.log (1 / 2 ^ d) - Real.log (t / 2 ^ d) = -Real.log t := by
  rw [Real.log_div one_ne_zero (by positivity), Real.log_div ht.ne' (by positivity), Real.log_one]
  ring

/-- `log(t/2^d) − log(1/2^d) = log t` for `t > 0`. -/
lemma log_div_two_pow_sub_one {t : ℝ} (ht : 0 < t) (d : ℕ) :
    Real.log (t / 2 ^ d) - Real.log (1 / 2 ^ d) = Real.log t := by
  rw [← neg_sub, log_one_div_two_pow_sub ht, neg_neg]

/-- `1/2^d ≤ 1/2` for `d ≥ 1`. -/
lemma one_div_two_pow_le_half {d : ℕ} (hd : 1 ≤ d) : (1 : ℝ) / 2 ^ d ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ 2 ^ d := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2

/-- `|G_d(t)| ≤ −log t` for `0 < t ≤ 1` and `d ≥ 1` (the upper two-point bound with
`u = t/2^d`, `v = 1/2^d`). -/
lemma abs_lutScaled_le_of_le_one {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |lutScaled d t| ≤ -Real.log t := by
  have hp : (0 : ℝ) < 2 ^ d := by positivity
  have hv := one_div_two_pow_le_half hd
  have hu0 : 0 < t / 2 ^ d := by positivity
  have huv : t / 2 ^ d ≤ 1 / 2 ^ d := div_le_div_of_nonneg_right ht1 hp.le
  have hM := normCDFInv_sub_mul_le hu0 huv (by linarith)
  rw [log_one_div_two_pow_sub ht0] at hM
  have hy := normCDFInv_nonpos (by positivity) hv
  have hxy := normCDFInv_mono hu0 huv (by linarith)
  have hl := Real.log_nonpos ht0.le ht1
  have hD : 0 ≤ (normCDFInv (1 / 2 ^ d) - normCDFInv (t / 2 ^ d)) * -normCDFInv (1 / 2 ^ d) :=
    mul_nonneg (by linarith) (by linarith)
  rw [lutScaled, abs_le]
  constructor <;> nlinarith

/-- `0 ≤ G_d(t) ≤ log t + (log t)²/Φ⁻¹(t/2^d)²` for `t ≥ 1` and `t/2^d ≤ 1/32`. -/
lemma lutScaled_le_of_one_le {d : ℕ} {t : ℝ} (ht1 : 1 ≤ t) (ht : t / 2 ^ d ≤ 1 / 32) :
    0 ≤ lutScaled d t ∧
      lutScaled d t ≤ Real.log t + Real.log t ^ 2 / normCDFInv (t / 2 ^ d) ^ 2 := by
  have hp : (0 : ℝ) < 2 ^ d := by positivity
  have hu0 : (0 : ℝ) < 1 / 2 ^ d := by positivity
  have huv : 1 / 2 ^ d ≤ t / 2 ^ d := div_le_div_of_nonneg_right ht1 hp.le
  have hM := normCDFInv_sub_mul_le hu0 huv (by linarith)
  rw [log_div_two_pow_sub_one (by linarith)] at hM
  have hy := normCDFInv_le_neg_one (by positivity) ht
  have hxy := normCDFInv_mono hu0 huv (by linarith)
  set x := normCDFInv (1 / 2 ^ d)
  set y := normCDFInv (t / 2 ^ d)
  have hD : 0 ≤ (y - x) * -y := mul_nonneg (by linarith) (by linarith)
  have hY : 0 < y ^ 2 := by nlinarith
  rw [lutScaled]
  refine ⟨mul_nonneg (by linarith) (by linarith), ?_⟩
  have hsq : (y - x) ^ 2 ≤ Real.log t ^ 2 / y ^ 2 := by
    rw [le_div_iff₀ hY]
    have : (y - x) ^ 2 * y ^ 2 = ((y - x) * -y) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ hD hM 2
  have e : (y - x) * -x = (y - x) * -y + (y - x) ^ 2 := by ring
  rw [e]
  linarith

/-- `|G_d(t) − log t| ≤ ((log t)² − log t)/Φ⁻¹(1/2^d)²` for `0 < t ≤ 1` and
`1/2^d ≤ 1/32` (both two-point bounds with `u = t/2^d`, `v = 1/2^d`). -/
lemma abs_lutScaled_sub_log_le_of_le_one {d : ℕ} (hd : (1 : ℝ) / 2 ^ d ≤ 1 / 32) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |lutScaled d t - Real.log t| ≤
      (Real.log t ^ 2 - Real.log t) / normCDFInv (1 / 2 ^ d) ^ 2 := by
  have hp : (0 : ℝ) < 2 ^ d := by positivity
  have hu0 : 0 < t / 2 ^ d := by positivity
  have huv : t / 2 ^ d ≤ 1 / 2 ^ d := div_le_div_of_nonneg_right ht1 hp.le
  have hM := normCDFInv_sub_mul_le hu0 huv (by linarith)
  have hM2 := log_sub_le_normCDFInv_sub_mul hu0 huv (by linarith)
  rw [log_one_div_two_pow_sub ht0] at hM hM2
  have hy := normCDFInv_le_neg_one (by positivity) hd
  have hxy := normCDFInv_mono hu0 huv (by linarith)
  have hl := Real.log_nonpos ht0.le ht1
  set x := normCDFInv (t / 2 ^ d)
  set y := normCDFInv (1 / 2 ^ d)
  set L := -Real.log t with hL
  have hD : 0 ≤ (y - x) * -y := mul_nonneg (by linarith) (by linarith)
  have hY : 0 < y ^ 2 := by nlinarith
  have e : (y - x) * (-x + (-y)⁻¹) * y ^ 2 =
      ((y - x) * -y) * y ^ 2 + ((y - x) * -y) ^ 2 + (y - x) * -y := by
    have hy0 : y ≠ 0 := by linarith
    field_simp
    ring
  have hM2' : L * y ^ 2 ≤ ((y - x) * -y) * y ^ 2 + ((y - x) * -y) ^ 2 + (y - x) * -y := by
    rw [← e]; exact mul_le_mul_of_nonneg_right hM2 hY.le
  have hDL : ((y - x) * -y) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hD hM 2
  have hG : lutScaled d t - Real.log t = L - (y - x) * -y := by
    rw [lutScaled, hL]; ring
  rw [hG, abs_of_nonneg (by linarith), le_div_iff₀ hY]
  have e2 : Real.log t ^ 2 - Real.log t = L ^ 2 + L := by rw [hL]; ring
  rw [e2]
  nlinarith

/-- `|G_d(t) − log t| ≤ ((log t)² + log t)/Φ⁻¹(t/2^d)²` for `t ≥ 1` and `t/2^d ≤ 1/32`
(both two-point bounds with `u = 1/2^d`, `v = t/2^d`). -/
lemma abs_lutScaled_sub_log_le_of_one_le {d : ℕ} {t : ℝ} (ht1 : 1 ≤ t)
    (ht : t / 2 ^ d ≤ 1 / 32) :
    |lutScaled d t - Real.log t| ≤
      (Real.log t ^ 2 + Real.log t) / normCDFInv (t / 2 ^ d) ^ 2 := by
  have hp : (0 : ℝ) < 2 ^ d := by positivity
  have hu0 : (0 : ℝ) < 1 / 2 ^ d := by positivity
  have huv : 1 / 2 ^ d ≤ t / 2 ^ d := div_le_div_of_nonneg_right ht1 hp.le
  have hM := normCDFInv_sub_mul_le hu0 huv (by linarith)
  have hM2 := log_sub_le_normCDFInv_sub_mul hu0 huv (by linarith)
  rw [log_div_two_pow_sub_one (by linarith)] at hM hM2
  have hy := normCDFInv_le_neg_one (by positivity) ht
  have hxy := normCDFInv_mono hu0 huv (by linarith)
  have hl := Real.log_nonneg ht1
  set x := normCDFInv (1 / 2 ^ d)
  set y := normCDFInv (t / 2 ^ d)
  set L := Real.log t with hL
  have hD : 0 ≤ (y - x) * -y := mul_nonneg (by linarith) (by linarith)
  have hY : 0 < y ^ 2 := by nlinarith
  have e : (y - x) * (-x + (-y)⁻¹) * y ^ 2 =
      ((y - x) * -y) * y ^ 2 + ((y - x) * -y) ^ 2 + (y - x) * -y := by
    have hy0 : y ≠ 0 := by linarith
    field_simp
    ring
  have hM2' : L * y ^ 2 ≤ ((y - x) * -y) * y ^ 2 + ((y - x) * -y) ^ 2 + (y - x) * -y := by
    rw [← e]; exact mul_le_mul_of_nonneg_right hM2 hY.le
  have hDL : ((y - x) * -y) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hD hM 2
  have hG : (lutScaled d t - L) * y ^ 2 = ((y - x) * -y - L) * y ^ 2 + ((y - x) * -y) ^ 2 := by
    rw [lutScaled]; ring
  have hneg : ((y - x) * -y - L) * y ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hY.le
  have h1 : (lutScaled d t - L) * y ^ 2 ≤ L ^ 2 + L := by rw [hG]; nlinarith
  have h2 : -(L ^ 2 + L) ≤ (lutScaled d t - L) * y ^ 2 := by rw [hG]; nlinarith
  rw [le_div_iff₀ hY, ← abs_of_pos hY, ← abs_mul]
  exact abs_le.2 ⟨h2, h1⟩

/-- `s/2^d → 0`. -/
lemma tendsto_div_two_pow (s : ℝ) : Tendsto (fun d : ℕ => s / 2 ^ d) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Eventually `s/2^d ≤ 1/32`. -/
lemma eventually_div_two_pow_le (s : ℝ) : ∀ᶠ d : ℕ in atTop, s / 2 ^ d ≤ 1 / 32 :=
  (tendsto_div_two_pow s).eventually (ge_mem_nhds (by norm_num))

/-- `−log(s/2^d) = d log 2 − log s` for `s > 0`. -/
lemma neg_log_div_two_pow {s : ℝ} (hs : 0 < s) (d : ℕ) :
    -Real.log (s / 2 ^ d) = d * Real.log 2 - Real.log s := by
  rw [Real.log_div hs.ne' (by positivity), Real.log_pow]
  ring

/-- `Φ⁻¹(s/2^d)² → ∞` for every `s > 0` (as `Φ⁻¹(u)² ≥ −log(u)/4` for `u ≤ 1/32`). -/
lemma tendsto_sq_normCDFInv_div_two_pow {s : ℝ} (hs : 0 < s) :
    Tendsto (fun d : ℕ => normCDFInv (s / 2 ^ d) ^ 2) atTop atTop := by
  have hlow : Tendsto (fun d : ℕ => ((d : ℝ) * Real.log 2 + -Real.log s) / 4) atTop atTop :=
    (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const
      (Real.log_pos one_lt_two))).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [eventually_div_two_pow_le s] with d hd
  have h := neg_log_le_four_mul_sq (by positivity) hd
  rw [neg_log_div_two_pow hs] at h
  linarith

/-- **The profile of `Φ⁻¹` near `0`** (not stated in the paper; used here for Haas–Giles 2025, §3.4,
p. 7, l. 377–379, H3-30: "The Figure 1 also illustrates that both method 1 and 2 have their MSE
divided by 2 each time `d` increases by 1. This was theoretically expected for method 1 (see
[12])"): for every `t > 0`, `G_d(t) = (Φ⁻¹(t/2^d) − Φ⁻¹(1/2^d)) |Φ⁻¹(1/2^d)| → log t` as `d → ∞`,
with the error at most `((log t)² + |log t|)/Φ⁻¹(max(t, 1)/2^d)²`. -/
theorem tendsto_lutScaled {t : ℝ} (ht : 0 < t) :
    Tendsto (fun d : ℕ => lutScaled d t) atTop (𝓝 (Real.log t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rcases le_total t 1 with ht1 | ht1
  · refine squeeze_zero_norm' ?_ ((tendsto_const_nhds
      (x := Real.log t ^ 2 - Real.log t)).div_atTop (tendsto_sq_normCDFInv_div_two_pow one_pos))
    filter_upwards [eventually_div_two_pow_le 1] with d hd
    rw [Real.norm_eq_abs, abs_norm]
    exact abs_lutScaled_sub_log_le_of_le_one hd ht ht1
  · refine squeeze_zero_norm' ?_ ((tendsto_const_nhds
      (x := Real.log t ^ 2 + Real.log t)).div_atTop (tendsto_sq_normCDFInv_div_two_pow ht))
    filter_upwards [eventually_div_two_pow_le t] with d hd
    rw [Real.norm_eq_abs, abs_norm]
    exact abs_lutScaled_sub_log_le_of_one_le ht1 hd

/-- **The growth of `Φ⁻¹` at the dyadic points** (not stated in the paper; used here for Haas–Giles
2025, §3.4, p. 7, l. 377–379, H3-30: "The Figure 1 also illustrates that both method 1 and 2 have
their MSE divided by 2 each time `d` increases by 1. This was theoretically expected for method 1
(see [12])"): `d/Φ⁻¹(2^{−d})² → 1/(2 log 2)`, i.e. `Φ⁻¹(2^{−d})² ~ 2 d log 2`, from
`2 d log 2 − 2 log 4 − 1 + 2Φ⁻¹(2^{−d}) ≤ Φ⁻¹(2^{−d})² ≤ 2 d log 2` and
`|Φ⁻¹(2^{−d})|/d ≤ √(2 log 2/d)`. -/
theorem tendsto_natCast_div_sq_normCDFInv :
    Tendsto (fun d : ℕ => (d : ℝ) / normCDFInv (1 / 2 ^ d) ^ 2) atTop
      (𝓝 (1 / (2 * Real.log 2))) := by
  have hl2 := Real.log_pos one_lt_two
  -- `a_d = −y_d/d → 0`, as `a_d² ≤ 2 log 2/d`
  have ha : Tendsto (fun d : ℕ => -normCDFInv (1 / 2 ^ d) / d) atTop (𝓝 0) := by
    have hs : Tendsto (fun d : ℕ => √(2 * Real.log 2 / d)) atTop (𝓝 0) := by
      have h := (tendsto_const_nhds (x := 2 * Real.log 2)).div_atTop
        tendsto_natCast_atTop_atTop |>.sqrt
      rwa [Real.sqrt_zero] at h
    refine squeeze_zero' ?_ ?_ hs
    · filter_upwards [eventually_ge_atTop 1] with d hd
      have h := normCDFInv_nonpos (v := 1 / 2 ^ d) (by positivity) (one_div_two_pow_le_half hd)
      exact div_nonneg (by linarith) (Nat.cast_nonneg d)
    · filter_upwards [eventually_div_two_pow_le 1, eventually_ge_atTop 1] with d hd hd1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
      have h := sq_normCDFInv_le (by positivity) hd
      rw [show -2 * Real.log (1 / 2 ^ d) = 2 * -Real.log (1 / 2 ^ d) by ring,
        neg_log_div_two_pow one_pos, Real.log_one, sub_zero] at h
      refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
      rw [div_pow, div_le_div_iff₀ (by positivity) hdR, neg_sq]
      nlinarith
  -- `y_d²/d → 2 log 2`
  have hq : Tendsto (fun d : ℕ => normCDFInv (1 / 2 ^ d) ^ 2 / d) atTop (𝓝 (2 * Real.log 2)) := by
    have hlow : Tendsto (fun d : ℕ => 2 * Real.log 2 - (2 * Real.log 4 + 1) / d -
        2 * (-normCDFInv (1 / 2 ^ d) / d)) atTop (𝓝 (2 * Real.log 2)) := by
      have h := ((tendsto_const_nhds (x := 2 * Real.log 2)).sub ((tendsto_const_nhds
        (x := 2 * Real.log 4 + 1)).div_atTop tendsto_natCast_atTop_atTop)).sub (ha.const_mul 2)
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_div_two_pow_le 1, eventually_ge_atTop 1] with d hd hd1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
      have h := neg_two_mul_log_le (u := 1 / 2 ^ d) (by positivity) (by linarith)
      rw [show -2 * Real.log (1 / 2 ^ d) = 2 * -Real.log (1 / 2 ^ d) by ring,
        neg_log_div_two_pow one_pos, Real.log_one, sub_zero] at h
      have e : 2 * Real.log 2 - (2 * Real.log 4 + 1) / d - 2 * (-normCDFInv (1 / 2 ^ d) / d) =
          (2 * d * Real.log 2 - 2 * Real.log 4 - 1 + 2 * normCDFInv (1 / 2 ^ d)) / d := by
        field_simp
        ring
      rw [e, div_le_div_iff_of_pos_right hdR]
      nlinarith
    · filter_upwards [eventually_div_two_pow_le 1, eventually_ge_atTop 1] with d hd hd1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
      have h := sq_normCDFInv_le (by positivity) hd
      rw [show -2 * Real.log (1 / 2 ^ d) = 2 * -Real.log (1 / 2 ^ d) by ring,
        neg_log_div_two_pow one_pos, Real.log_one, sub_zero] at h
      rw [div_le_iff₀ hdR]
      linarith
  have h := hq.inv₀ (by positivity)
  refine (h.congr fun d => ?_).trans (by rw [one_div])
  rw [inv_div]

/-! ### Dominated convergence on one cell -/

/-- `(log t)²` is integrable on `[0, 1]` (it is at most `16 t^{−1/2}` there). -/
lemma intervalIntegrable_log_sq_zero_one :
    IntervalIntegrable (fun t => Real.log t ^ 2) volume 0 1 := by
  have hg : IntervalIntegrable (fun t : ℝ => 16 * t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 16
  refine hg.mono_fun' ((Real.measurable_log.pow_const 2).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun t ht => ?_)
  rw [Set.uIoc_of_le zero_le_one] at ht
  have ht0 := ht.1
  have hl := Real.log_le_rpow_div (x := t⁻¹) (ε := 1 / 4) (by positivity) (by norm_num)
  have hl0 : 0 ≤ Real.log t⁻¹ := by
    rw [Real.log_inv]; linarith [Real.log_nonpos ht0.le ht.2]
  have hsq := pow_le_pow_left₀ hl0 hl 2
  rw [Real.log_inv, neg_sq] at hsq
  show ‖Real.log t ^ 2‖ ≤ 16 * t ^ (-(1 / 2 : ℝ))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine hsq.trans (le_of_eq ?_)
  rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.inv_rpow ht0.le,
    Real.rpow_neg ht0.le]
  norm_num
  ring

/-- `(log t)²` is integrable on every `[j, j + 1]`, `j ∈ ℕ`. -/
lemma intervalIntegrable_log_sq (j : ℕ) :
    IntervalIntegrable (fun t => Real.log t ^ 2) volume (j : ℝ) (j + 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa using intervalIntegrable_log_sq_zero_one
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    refine ContinuousOn.intervalIntegrable ?_
    refine (Real.continuousOn_log.mono fun t ht => ?_).pow 2
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1]

/-- `G_d` is measurable. -/
lemma measurable_lutScaled (d : ℕ) : Measurable (lutScaled d) :=
  ((measurable_normCDFInv.comp (measurable_id.div_const _)).sub_const _).mul_const _

/-- The domination of `G_d` on the cell `(j, j + 1]`: eventually in `d`,
`|G_d(t)| ≤ 2 |log t|` there. -/
lemma eventually_abs_lutScaled_le (j : ℕ) : ∀ᶠ d : ℕ in atTop,
    ∀ t ∈ Set.Ioc (j : ℝ) (j + 1), |lutScaled d t| ≤ 2 * |Real.log t| := by
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  have hY := (tendsto_sq_normCDFInv_div_two_pow hj1).eventually
    (eventually_ge_atTop (Real.log (j + 1)))
  filter_upwards [eventually_ge_atTop 1, eventually_div_two_pow_le ((j : ℝ) + 1), hY]
    with d hd hdj hYd t ht
  have ht0 : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg j) ht.1
  rcases le_total t 1 with ht1 | ht1
  · have h := abs_lutScaled_le_of_le_one hd ht0 ht1
    have hl := Real.log_nonpos ht0.le ht1
    rw [abs_of_nonpos hl]
    linarith
  · have hp : (0 : ℝ) < 2 ^ d := by positivity
    have htj : t / 2 ^ d ≤ ((j : ℝ) + 1) / 2 ^ d := div_le_div_of_nonneg_right ht.2 hp.le
    obtain ⟨h0, h1⟩ := lutScaled_le_of_one_le ht1 (htj.trans hdj)
    have hl := Real.log_nonneg ht1
    have hmono := normCDFInv_mono (by positivity) htj (by linarith)
    have hneg := normCDFInv_le_neg_one (u := ((j : ℝ) + 1) / 2 ^ d) (by positivity) hdj
    have hsq : normCDFInv (((j : ℝ) + 1) / 2 ^ d) ^ 2 ≤ normCDFInv (t / 2 ^ d) ^ 2 := by
      nlinarith
    have hlt : Real.log t ≤ Real.log (j + 1) := Real.log_le_log ht0 ht.2
    have hY0 : 0 < normCDFInv (t / 2 ^ d) ^ 2 := by nlinarith
    have hq : Real.log t ^ 2 / normCDFInv (t / 2 ^ d) ^ 2 ≤ Real.log t := by
      rw [div_le_iff₀ hY0]
      nlinarith
    rw [abs_of_nonneg h0, abs_of_nonneg hl]
    linarith

/-- `∫_j^{j+1} G_d → ∫_j^{j+1} log` (dominated convergence, bound `2|log t|`). -/
lemma tendsto_integral_lutScaled (j : ℕ) :
    Tendsto (fun d : ℕ => ∫ t in (j : ℝ)..j + 1, lutScaled d t) atTop
      (𝓝 (∫ t in (j : ℝ)..j + 1, Real.log t)) := by
  have hjj : (j : ℝ) ≤ j + 1 := by linarith
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => 2 * |Real.log t|)
    (Eventually.of_forall fun d => (measurable_lutScaled d).aestronglyMeasurable) ?_
    (intervalIntegral.intervalIntegrable_log'.abs.const_mul 2) ?_
  · filter_upwards [eventually_abs_lutScaled_le j] with d hd
    refine Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hjj] at ht
    rw [Real.norm_eq_abs]
    exact hd t ht
  · refine Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hjj] at ht
    exact tendsto_lutScaled (lt_of_le_of_lt (Nat.cast_nonneg j) ht.1)

/-- `∫_j^{j+1} G_d² → ∫_j^{j+1} (log)²` (dominated convergence, bound `4 (log t)²`). -/
lemma tendsto_integral_lutScaled_sq (j : ℕ) :
    Tendsto (fun d : ℕ => ∫ t in (j : ℝ)..j + 1, lutScaled d t ^ 2) atTop
      (𝓝 (∫ t in (j : ℝ)..j + 1, Real.log t ^ 2)) := by
  have hjj : (j : ℝ) ≤ j + 1 := by linarith
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => 4 * Real.log t ^ 2)
    (Eventually.of_forall fun d => ((measurable_lutScaled d).pow_const 2).aestronglyMeasurable)
    ?_ ((intervalIntegrable_log_sq j).const_mul 4) ?_
  · filter_upwards [eventually_abs_lutScaled_le j] with d hd
    refine Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hjj] at ht
    have h := hd t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    linarith
  · refine Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hjj] at ht
    exact (tendsto_lutScaled (lt_of_le_of_lt (Nat.cast_nonneg j) ht.1)).pow 2

/-! ### The cell errors of method 1 near `0` -/

/-- The mean-square error of method 1 for `Φ⁻¹` on the cell `I_j = [2^{−d} j, 2^{−d}(j + 1)]`
(Haas–Giles 2025, §3.1, (14), p. 5, l. 258–261: "the mean squared error (MSE)
`∫_{u_j}^{u_{j+1}} (Z_j − Φ⁻¹(u))² du`", with the optimal value (15) `Z_j`): the within-cell
variance `∫_{I_j} (Z_j − Φ⁻¹)²`. -/
noncomputable def method1CellErr (d j : ℕ) : ℝ :=
  ∫ u in gridPt d j..gridPt d (j + 1), (lutValue normCDFInv d j - normCDFInv u) ^ 2

/-- The variance of `log` on `[j, j + 1]` (times the cell length `1`):
`V_j = ∫_j^{j+1} (log t)² dt − (∫_j^{j+1} log t dt)²`, `2 log 2` times the limit of the rescaled
cell errors of method 1 near `0` (Haas–Giles 2025, §3.4, p. 7, l. 377–379).  `V_0 = 1` and
`V_j ≈ 1/(12 (j + 1/2)²)`; the value of `log` at `0` is the junk value `0`, on a null set. -/
noncomputable def logCellVar (j : ℕ) : ℝ :=
  (∫ t in (j : ℝ)..j + 1, Real.log t ^ 2) - (∫ t in (j : ℝ)..j + 1, Real.log t) ^ 2

/-- The cell error in the rescaled variable `t = 2^d u`: for `j < 2^d`,
`∫_j^{j+1} G_d² − (∫_j^{j+1} G_d)² = 2^d Φ⁻¹(1/2^d)² E_j(d)`, where `E_j(d)` is the error on
`I_j` (the variance is shift invariant and `Φ⁻¹(1/2^d)` is a fixed reference value). -/
lemma lutScaled_cell_identity {d j : ℕ} (hj : j < 2 ^ d) :
    (∫ t in (j : ℝ)..j + 1, lutScaled d t ^ 2) - (∫ t in (j : ℝ)..j + 1, lutScaled d t) ^ 2 =
      2 ^ d * normCDFInv (1 / 2 ^ d) ^ 2 * method1CellErr d j := by
  have hp : (2 : ℝ) ^ d ≠ 0 := by positivity
  have ha : gridPt d j = (j : ℝ) / 2 ^ d := rfl
  have hb : gridPt d (j + 1) = ((j : ℝ) + 1) / 2 ^ d := by unfold gridPt; push_cast; ring
  have hf := intervalIntegrable_cell intervalIntegrable_normCDFInv.1 hj
  have hf2 := intervalIntegrable_cell intervalIntegrable_normCDFInv.2 hj
  rw [ha, hb] at hf hf2
  set c := normCDFInv (1 / 2 ^ d) with hc
  set A := ∫ u in (j : ℝ) / 2 ^ d..((j : ℝ) + 1) / 2 ^ d, normCDFInv u with hA
  set B := ∫ u in (j : ℝ) / 2 ^ d..((j : ℝ) + 1) / 2 ^ d, normCDFInv u ^ 2 with hB
  have hlen : ((j : ℝ) + 1) / 2 ^ d - (j : ℝ) / 2 ^ d = (2 ^ d)⁻¹ := by field_simp; ring
  have h1 : ∫ t in (j : ℝ)..j + 1, lutScaled d t = (2 ^ d * (A - (2 ^ d)⁻¹ * c)) * -c := by
    unfold lutScaled
    rw [intervalIntegral.integral_mul_const]
    have h := intervalIntegral.integral_comp_div (fun u => normCDFInv u - c) hp
      (a := (j : ℝ)) (b := (j : ℝ) + 1)
    rw [h, intervalIntegral.integral_sub hf intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul, hlen]
  have h2 : ∫ t in (j : ℝ)..j + 1, lutScaled d t ^ 2 =
      (2 ^ d * ((2 ^ d)⁻¹ * c ^ 2 - 2 * c * A + B)) * c ^ 2 := by
    have e : ∀ t, lutScaled d t ^ 2 = (c - normCDFInv (t / 2 ^ d)) ^ 2 * c ^ 2 := fun t => by
      unfold lutScaled; ring
    simp_rw [e]
    rw [intervalIntegral.integral_mul_const]
    have h := intervalIntegral.integral_comp_div (fun u => (c - normCDFInv u) ^ 2) hp
      (a := (j : ℝ)) (b := (j : ℝ) + 1)
    rw [h, integral_sq_sub_const hf hf2 c, hlen, smul_eq_mul]
  have h3 : method1CellErr d j = (2 ^ d)⁻¹ * (2 ^ d * A) ^ 2 - 2 * (2 ^ d * A) * A + B := by
    unfold method1CellErr
    rw [lutValue, ha, hb, integral_sq_sub_const hf hf2, hlen]
  rw [h1, h2, h3]
  field_simp
  ring

/-- **Each cell near `0` carries a definite share of the MSE** (not stated in the paper; used for
Haas–Giles 2025, §3.4, p. 7, l. 377–379, H3-30: "The Figure 1 also illustrates that both method 1
and 2 have their MSE divided by 2 each time `d` increases by 1. This was theoretically expected for
method 1 (see [12])"): for every fixed `j`, `d 2^d E_j(d) → V_j/(2 log 2)`, where `E_j(d)` is the
error of method 1 on the cell `[2^{−d} j, 2^{−d}(j + 1)]` and `V_j` the variance of `log` on
`[j, j + 1]`. So the cell at `0` carries `1/S ≈ 93 %` of the limit and the cells `j ≥ 1` the rest
(`S = ∑ V_j ≈ 1.0803`, numerical value). -/
theorem tendsto_method1CellErr_normCDFInv (j : ℕ) :
    Tendsto (fun d : ℕ => (d : ℝ) * 2 ^ d * method1CellErr d j) atTop
      (𝓝 (logCellVar j / (2 * Real.log 2))) := by
  have hW : Tendsto (fun d : ℕ => (∫ t in (j : ℝ)..j + 1, lutScaled d t ^ 2) -
      (∫ t in (j : ℝ)..j + 1, lutScaled d t) ^ 2) atTop (𝓝 (logCellVar j)) :=
    (tendsto_integral_lutScaled_sq j).sub ((tendsto_integral_lutScaled j).pow 2)
  have h := tendsto_natCast_div_sq_normCDFInv.mul hW
  rw [show logCellVar j / (2 * Real.log 2) = 1 / (2 * Real.log 2) * logCellVar j by ring]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop j, eventually_div_two_pow_le 1] with d hd hd'
  have hj : j < 2 ^ d := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right two_pos hd)
  have hc := normCDFInv_le_neg_one (u := 1 / 2 ^ d) (by positivity) hd'
  have hc0 : normCDFInv (1 / 2 ^ d) ≠ 0 := by linarith
  rw [lutScaled_cell_identity hj]
  field_simp

/-! ### Summable domination and the cells away from `0` -/

/-- The cell errors are nonnegative. -/
lemma method1CellErr_nonneg (d j : ℕ) : 0 ≤ method1CellErr d j :=
  intervalIntegral.integral_nonneg (gridPt_lt d j).le fun _ _ => sq_nonneg _

/-- The domination of the cells `1 ≤ j < 2^{⌊d/2⌋}`, `d ≥ 10`: `d 2^d E_j(d) ≤ 16/j²`
(the two-point bound gives `(Φ⁻¹(v) − Φ⁻¹(u))² ≤ 1/(j² Φ⁻¹(v)²)` and `Φ⁻¹(v)² ≥ d/16` there). -/
lemma method1CellErr_bound {d j : ℕ} (hd : 10 ≤ d) (hj1 : 1 ≤ j) (hj : j < 2 ^ (d / 2)) :
    (d : ℝ) * 2 ^ d * method1CellErr d j ≤ 16 / (j : ℝ) ^ 2 := by
  have hp : (0 : ℝ) < 2 ^ d := by positivity
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hdR : (10 : ℝ) ≤ d := by exact_mod_cast hd
  -- the cell lies in `(0, 1/32]`
  have h32 : 32 * (j + 1) ≤ 2 ^ d := by
    calc 32 * (j + 1) ≤ 2 ^ 5 * 2 ^ (d / 2) := by norm_num; omega
      _ = 2 ^ (5 + d / 2) := by rw [pow_add]
      _ ≤ 2 ^ d := Nat.pow_le_pow_right two_pos (by omega)
  have h32R : (32 : ℝ) * ((j : ℝ) + 1) ≤ 2 ^ d := by exact_mod_cast h32
  have hjd : j < 2 ^ d := by omega
  have hu : gridPt d j = (j : ℝ) / 2 ^ d := rfl
  have hv : gridPt d (j + 1) = ((j : ℝ) + 1) / 2 ^ d := by unfold gridPt; push_cast; ring
  have hu0 : 0 < gridPt d j := by rw [hu]; positivity
  have huv : gridPt d j ≤ gridPt d (j + 1) := (gridPt_lt d j).le
  have hv32 : gridPt d (j + 1) ≤ 1 / 32 := by
    rw [hv, div_le_div_iff₀ hp (by norm_num)]; linarith
  have hmono : MonotoneOn normCDFInv (Set.Icc (gridPt d j) (gridPt d (j + 1))) :=
    strictMonoOn_normCDFInv.monotoneOn.mono fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hE := integral_sq_sub_lutValue_le hmono
    (intervalIntegrable_cell intervalIntegrable_normCDFInv.1 hjd)
    (intervalIntegrable_cell intervalIntegrable_normCDFInv.2 hjd)
  -- the two-point bound: `(Φ⁻¹(v) − Φ⁻¹(u)) |Φ⁻¹(v)| ≤ log(v/u) ≤ 1/j`
  have hM := normCDFInv_sub_mul_le hu0 huv (by linarith)
  have hlog : Real.log (gridPt d (j + 1)) - Real.log (gridPt d j) ≤ 1 / j := by
    rw [← Real.log_div (by linarith) hu0.ne', hu, hv, div_div_div_cancel_right₀ hp.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp
    ring
  have hfv := normCDFInv_le_neg_one (by linarith) hv32
  have hfuv := normCDFInv_mono hu0 huv (by linarith)
  -- `Φ⁻¹(v)² ≥ d/16`
  have hY : (d : ℝ) / 16 ≤ normCDFInv (gridPt d (j + 1)) ^ 2 := by
    have h1 := neg_log_le_four_mul_sq (by linarith) hv32
    rw [hv]
    rw [hv, neg_log_div_two_pow (by positivity)] at h1
    have hj2 : ((j : ℝ) + 1) ≤ 2 ^ (d / 2) := by exact_mod_cast hj
    have h2 : Real.log ((j : ℝ) + 1) ≤ ((d / 2 : ℕ) : ℝ) * Real.log 2 := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hj2
    have h3 : ((d / 2 : ℕ) : ℝ) ≤ (d : ℝ) / 2 := by
      have := Nat.cast_div_le (α := ℝ) (m := d) (n := 2)
      simpa using this
    have hl2 := Real.log_two_gt_d9
    nlinarith
  set X := normCDFInv (gridPt d (j + 1)) - normCDFInv (gridPt d j)
  have hX0 : 0 ≤ X := by linarith
  have hD : X * -normCDFInv (gridPt d (j + 1)) ≤ 1 / j := hM.trans hlog
  have hsq : X ^ 2 * normCDFInv (gridPt d (j + 1)) ^ 2 ≤ 1 / (j : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg hX0 (by linarith)) hD 2
    rw [div_pow, one_pow] at h
    nlinarith
  have hkey : (d : ℝ) * X ^ 2 ≤ 16 / (j : ℝ) ^ 2 := by
    have h1 : (d : ℝ) * X ^ 2 ≤ 16 * (X ^ 2 * normCDFInv (gridPt d (j + 1)) ^ 2) := by
      nlinarith [sq_nonneg X]
    calc (d : ℝ) * X ^ 2 ≤ 16 * (X ^ 2 * normCDFInv (gridPt d (j + 1)) ^ 2) := h1
      _ ≤ 16 * (1 / (j : ℝ) ^ 2) := by linarith
      _ = 16 / (j : ℝ) ^ 2 := by ring
  unfold method1CellErr
  calc (d : ℝ) * 2 ^ d * ∫ u in gridPt d j..gridPt d (j + 1),
        (lutValue normCDFInv d j - normCDFInv u) ^ 2
      ≤ (d : ℝ) * 2 ^ d * ((2 ^ d)⁻¹ * X ^ 2) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (d : ℝ) * X ^ 2 := by field_simp
    _ ≤ 16 / (j : ℝ) ^ 2 := hkey

/-- The domination of the end cell: `d 2^d E_0(d) ≤ (3/2) K` for `d ≥ 1`, with the constant
`K = 8 (4 + φ(1)⁻²)` of the block bounds of `Φ⁻¹`. -/
lemma method1CellErr_zero_bound {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) * 2 ^ d * method1CellErr d 0 ≤
      3 / 2 * (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2)) := by
  have h := end_cell_method1_le intervalIntegrable_normCDFInv.1 intervalIntegrable_normCDFInv.2
    (K := 8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2))
    (fun _ hm _ _ hu huv hv => (normCDFInv_block_bounds hm hu huv hv).2) hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold method1CellErr
  calc (d : ℝ) * 2 ^ d * ∫ u in gridPt d 0..gridPt d (0 + 1),
        (lutValue normCDFInv d 0 - normCDFInv u) ^ 2
      ≤ (d : ℝ) * 2 ^ d * ((2 ^ d)⁻¹ * (3 / 2 * (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2)) / d)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 3 / 2 * (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2)) := by field_simp

/-- The summable domination: `d 2^d E_j(d) ≤ B/(j + 1)²` for `d ≥ 10` and `j < 2^{⌊d/2⌋}`, with
`B = (3/2) K + 64`. -/
lemma method1CellErr_dom {d j : ℕ} (hd : 10 ≤ d) (hj : j < 2 ^ (d / 2)) :
    (d : ℝ) * 2 ^ d * method1CellErr d j ≤
      (3 / 2 * (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2)) + 64) / ((j : ℝ) + 1) ^ 2 := by
  have hK : 0 ≤ 3 / 2 * (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2)) := by positivity
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · have h := method1CellErr_zero_bound (d := d) (by omega)
    rw [Nat.cast_zero, zero_add, one_pow, div_one]
    linarith
  · have h := method1CellErr_bound hd hj1 hj
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    refine h.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- `∑_{n ≤ i < N} 2^{−i} ≤ 2 · 2^{−n}`. -/
lemma sum_Ico_inv_two_pow_le (n N : ℕ) :
    ∑ i ∈ Finset.Ico n N, ((2 : ℝ) ^ i)⁻¹ ≤ 2 * ((2 : ℝ) ^ n)⁻¹ := by
  rw [Finset.sum_Ico_eq_sum_range]
  have e : ∀ k, ((2 : ℝ) ^ (n + k))⁻¹ = ((2 : ℝ) ^ n)⁻¹ * (1 / 2) ^ k := fun k => by
    rw [pow_add, mul_inv, one_div, inv_pow]
  simp_rw [e]
  rw [← Finset.mul_sum, mul_comm]
  exact mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (by positivity)

/-- The cells away from `0`: the blocks `⌊d/2⌋ ≤ i < d − 1` (the cells
`2^{⌊d/2⌋} ≤ j < 2^{d−1}`) contribute at most `2^{−d} (K/2) 2^{−⌊d/2⌋}` for `d ≥ 2`. -/
lemma method1_tail_le {d : ℕ} (hd : 2 ≤ d) :
    ∑ i ∈ Finset.Ico (d / 2) (d - 1), ∑ j ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), method1CellErr d j ≤
      (2 ^ d)⁻¹ * (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2) / 2 * ((2 : ℝ) ^ (d / 2))⁻¹) := by
  set K := 8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2) with hKdef
  have hK : 0 ≤ K := by positivity
  have hblock : ∀ i ∈ Finset.Ico (d / 2) (d - 1),
      ∑ j ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), method1CellErr d j ≤
        (2 ^ d)⁻¹ * (K / 4) * ((2 : ℝ) ^ i)⁻¹ := by
    intro i hi
    have hi' := (Finset.mem_Ico.1 hi).2
    have h := group_method1_le intervalIntegrable_normCDFInv.1 intervalIntegrable_normCDFInv.2
      (K := K) (fun _ hm _ _ hu huv hv => (normCDFInv_block_bounds hm hu huv hv).2)
      (d := d) (i := i) (m := d - 1 - i) (by omega) (by omega)
    unfold method1CellErr
    refine h.trans ?_
    have hm : (1 : ℝ) ≤ ((d - 1 - i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d - 1 - i by omega)
    have hp : (0 : ℝ) < (2 ^ d)⁻¹ := by positivity
    have hq : (0 : ℝ) < ((2 : ℝ) ^ i)⁻¹ := by positivity
    have hdiv : K * ((2 : ℝ) ^ i)⁻¹ / (4 * ((d - 1 - i : ℕ) : ℝ)) ≤ K / 4 * ((2 : ℝ) ^ i)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hK hq.le]
    calc (2 ^ d)⁻¹ * (K * ((2 : ℝ) ^ i)⁻¹ / (4 * ((d - 1 - i : ℕ) : ℝ)))
        ≤ (2 ^ d)⁻¹ * (K / 4 * ((2 : ℝ) ^ i)⁻¹) := mul_le_mul_of_nonneg_left hdiv hp.le
      _ = (2 ^ d)⁻¹ * (K / 4) * ((2 : ℝ) ^ i)⁻¹ := by ring
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [← Finset.mul_sum]
  have h := sum_Ico_inv_two_pow_le (d / 2) (d - 1)
  have hp : (0 : ℝ) ≤ (2 ^ d)⁻¹ * (K / 4) := by positivity
  calc (2 ^ d)⁻¹ * (K / 4) * ∑ i ∈ Finset.Ico (d / 2) (d - 1), ((2 : ℝ) ^ i)⁻¹
      ≤ (2 ^ d)⁻¹ * (K / 4) * (2 * ((2 : ℝ) ^ (d / 2))⁻¹) := mul_le_mul_of_nonneg_left h hp
    _ = (2 ^ d)⁻¹ * (K / 2 * ((2 : ℝ) ^ (d / 2))⁻¹) := by ring

/-- `d 2^{−⌊d/2⌋} → 0`. -/
lemma tendsto_natCast_mul_inv_two_pow_half :
    Tendsto (fun d : ℕ => (d : ℝ) * ((2 : ℝ) ^ (d / 2))⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => 2 * ((k : ℝ) * (1 / 2) ^ k) + (1 / 2) ^ k) atTop (𝓝 0) := by
    have := ((tendsto_self_mul_const_pow_of_lt_one (by norm_num)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1))
    simpa using this
  have h2 := h1.comp (Nat.tendsto_div_const_atTop two_ne_zero)
  refine squeeze_zero (fun d => by positivity) (fun d => ?_) h2
  have hd : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
    have : d ≤ 2 * (d / 2) + 1 := by omega
    exact_mod_cast this
  simp only [Function.comp_apply, one_div, inv_pow]
  have hq : (0 : ℝ) ≤ ((2 : ℝ) ^ (d / 2))⁻¹ := by positivity
  nlinarith

/-! ### The asymptotics of the MSE and the halving per bit -/

/-- The split of the method-1 MSE of `Φ⁻¹` (sign bit, then cells near `0` and dyadic blocks):
for `d ≥ 1`,
`MSE(d) = 2 (∑_{j < 2^{⌊d/2⌋}} E_j(d) + ∑_{⌊d/2⌋ ≤ i < d−1} ∑_{2^i ≤ j < 2^{i+1}} E_j(d))`. -/
lemma method1MSE_normCDFInv_split {d : ℕ} (hd : 1 ≤ d) :
    method1MSE normCDFInv d = 2 * ((∑ j ∈ Finset.range (2 ^ (d / 2)), method1CellErr d j) +
      ∑ i ∈ Finset.Ico (d / 2) (d - 1), ∑ j ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)),
        method1CellErr d j) := by
  rw [method1MSE_eq_two_mul normCDFInv_one_sub_forall hd]
  have e : ∑ j ∈ Finset.range (2 ^ (d - 1)), ∫ u in gridPt d j..gridPt d (j + 1),
      (lutValue normCDFInv d j - normCDFInv u) ^ 2 =
      ∑ j ∈ Finset.range (2 ^ (d - 1)), method1CellErr d j := rfl
  rw [e, sum_range_two_pow_dyadic _ (d - 1), sum_range_two_pow_dyadic _ (d / 2),
    ← Finset.sum_range_add_sum_Ico _ (show d / 2 ≤ d - 1 by omega)]
  ring

/-- `j ↦ B/(j + 1)²` is summable. -/
lemma summable_inv_add_one_sq (B : ℝ) : Summable fun j : ℕ => B / ((j : ℝ) + 1) ^ 2 := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine (h.mul_left B).congr fun j => ?_
  push_cast
  ring

/-- **The series of the cell variances converges** (Haas–Giles 2025, §3.4, p. 7, l. 377–379, H3-30:
"The Figure 1 also illustrates that both method 1 and 2 have their MSE divided by 2 each time `d`
increases by 1. This was theoretically expected for method 1 (see [12])"): `∑_j V_j < ∞` with
`V_j = ∫_j^{j+1} (log t)² dt − (∫_j^{j+1} log t dt)²`, as `0 ≤ V_j/(2 log 2) ≤ B/(j + 1)²` (the
limits of the dominated rescaled cell errors). So the `tsum` in the constant `κ` is a genuine sum,
not the junk value of a divergent series. -/
theorem summable_logCellVar : Summable logCellVar := by
  set B := 3 / 2 * (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2)) + 64 with hB
  have hl2 : 0 < 2 * Real.log 2 := by have := Real.log_pos one_lt_two; positivity
  have hφ : Tendsto (fun d : ℕ => 2 ^ (d / 2)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (Nat.tendsto_div_const_atTop two_ne_zero)
  have hbd : ∀ j : ℕ, 0 ≤ logCellVar j / (2 * Real.log 2) ∧
      logCellVar j / (2 * Real.log 2) ≤ B / ((j : ℝ) + 1) ^ 2 := by
    intro j
    have hev : ∀ᶠ d : ℕ in atTop, 10 ≤ d ∧ j < 2 ^ (d / 2) :=
      (eventually_ge_atTop 10).and (hφ.eventually (eventually_gt_atTop j))
    refine ⟨ge_of_tendsto (tendsto_method1CellErr_normCDFInv j)
        (hev.mono fun d hd => mul_nonneg (by positivity) (method1CellErr_nonneg _ _)),
      le_of_tendsto (tendsto_method1CellErr_normCDFInv j)
        (hev.mono fun d hd => method1CellErr_dom hd.1 hd.2)⟩
  have h := (summable_inv_add_one_sq B).of_nonneg_of_le (fun j => (hbd j).1) (fun j => (hbd j).2)
  refine (h.mul_right (2 * Real.log 2)).congr fun j => ?_
  field_simp

/-- **The exact asymptotics of the method-1 MSE for `Φ⁻¹`** (Haas–Giles 2025, §3.4, p. 7, l.
377–379, H3-30: "The Figure 1 also illustrates that both method 1 and 2 have their MSE divided by 2
each time `d` increases by 1. This was theoretically expected for method 1 (see [12])"; §3.4, p. 7,
l. 366–367: "the uniform intervals give `MSE → 0`"): `d 2^d MSE(d) → κ = (∑_j V_j)/log 2`, where
`V_j = ∫_j^{j+1} (log t)² dt − (∫_j^{j+1} log t dt)²` is the variance of `log` on `[j, j + 1]`.
Numerically `∑_j V_j ≈ 1.080327` and `κ ≈ 1.558582`. The limit is approached slowly and not
monotonically (`d 2^d MSE(d) ≈ 1.5328, 1.5568, 1.5743, 1.5603, 1.5587` at
`d = 10, 18, 50, 3000, 10⁵`; numerical values). -/
theorem tendsto_mul_method1MSE_normCDFInv :
    Tendsto (fun d : ℕ => (d : ℝ) * 2 ^ d * method1MSE normCDFInv d) atTop
      (𝓝 ((∑' j, logCellVar j) / Real.log 2)) := by
  set B := 3 / 2 * (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2)) + 64 with hB
  have hφ : Tendsto (fun d : ℕ => 2 ^ ((d + 10) / 2)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp
      ((Nat.tendsto_div_const_atTop two_ne_zero).comp (tendsto_add_atTop_nat 10))
  have hT := tendsto_sum_range_of_dominated
    (F := fun d j => ((d + 10 : ℕ) : ℝ) * 2 ^ (d + 10) * method1CellErr (d + 10) j)
    (g := fun j => logCellVar j / (2 * Real.log 2)) (b := fun j => B / ((j : ℝ) + 1) ^ 2)
    (φ := fun d => 2 ^ ((d + 10) / 2)) hφ (summable_inv_add_one_sq B)
    (fun d j _ => mul_nonneg (by positivity) (method1CellErr_nonneg _ _))
    (fun d j hj => method1CellErr_dom (by omega) hj)
    (fun j => (tendsto_method1CellErr_normCDFInv j).comp (tendsto_add_atTop_nat 10))
  have hR : Tendsto (fun d : ℕ => ((d + 10 : ℕ) : ℝ) * 2 ^ (d + 10) *
      ∑ i ∈ Finset.Ico ((d + 10) / 2) (d + 10 - 1),
        ∑ j ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), method1CellErr (d + 10) j) atTop (𝓝 0) := by
    have h0 := (tendsto_natCast_mul_inv_two_pow_half.comp (tendsto_add_atTop_nat 10)).const_mul
      (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2) / 2)
    rw [mul_zero] at h0
    refine squeeze_zero (fun d => ?_) (fun d => ?_) h0
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => method1CellErr_nonneg _ _)
    · have h := method1_tail_le (d := d + 10) (by omega)
      have hp : (0 : ℝ) < ((d + 10 : ℕ) : ℝ) * 2 ^ (d + 10) := by positivity
      calc ((d + 10 : ℕ) : ℝ) * 2 ^ (d + 10) * ∑ i ∈ Finset.Ico ((d + 10) / 2) (d + 10 - 1),
            ∑ j ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), method1CellErr (d + 10) j
          ≤ ((d + 10 : ℕ) : ℝ) * 2 ^ (d + 10) * ((2 ^ (d + 10))⁻¹ *
            (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2) / 2 * ((2 : ℝ) ^ ((d + 10) / 2))⁻¹)) :=
            mul_le_mul_of_nonneg_left h hp.le
        _ = _ := by simp only [Function.comp_apply]; field_simp
  have hsum := (hT.add hR).const_mul 2
  rw [← tendsto_add_atTop_iff_nat 10]
  have hlim : 2 * ((∑' j, logCellVar j / (2 * Real.log 2)) + 0) =
      (∑' j, logCellVar j) / Real.log 2 := by
    rw [tsum_div_const, add_zero]
    have := Real.log_pos one_lt_two
    field_simp
  rw [← hlim]
  refine hsum.congr fun d => ?_
  rw [method1MSE_normCDFInv_split (d := d + 10) (by omega), ← Finset.mul_sum]
  ring

/-- **The constant of the asymptotics is positive** (Haas–Giles 2025, §3.4, p. 7, l. 377–379, H3-30:
"The Figure 1 also illustrates that both method 1 and 2 have their MSE divided by 2 each time `d`
increases by 1. This was theoretically expected for method 1 (see [12])"):
`κ = (∑_j V_j)/log 2 > 0`, from the lower bound `c 2^{−d}/d ≤ MSE(d)` of the order of the MSE. -/
theorem method1MSE_normCDFInv_const_pos : 0 < (∑' j, logCellVar j) / Real.log 2 := by
  obtain ⟨c, K, hc, -, hb⟩ := method1MSE_order_normCDFInv
  refine lt_of_lt_of_le hc (ge_of_tendsto tendsto_mul_method1MSE_normCDFInv ?_)
  filter_upwards [eventually_ge_atTop 2] with d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h := (hb d hd).1
  have hp : (0 : ℝ) < 2 ^ d := by positivity
  calc c = (d : ℝ) * 2 ^ d * (c * ((2 ^ d)⁻¹ / d)) := by field_simp
    _ ≤ (d : ℝ) * 2 ^ d * method1MSE normCDFInv d :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- **The method-1 MSE of `Φ⁻¹` is divided by 2 each time `d` increases by 1** (Haas–Giles 2025,
§3.4, p. 7, l. 377–379, H3-30: "The Figure 1 also illustrates that both method 1 and 2 have their
MSE divided by 2 each time `d` increases by 1. This was theoretically expected for method 1 (see
[12])"): `MSE(d + 1)/MSE(d) → 1/2`. This is the asymptotic form of the claim; at finite `d` the
ratio is `≈ ½ · d/(d + 1)` (`0.4514, 0.4695, 0.4728` at `d = 9, 15, 17`, numerical values), below
`½`. -/
theorem tendsto_method1MSE_succ_div_normCDFInv :
    Tendsto (fun d : ℕ => method1MSE normCDFInv (d + 1) / method1MSE normCDFInv d) atTop
      (𝓝 (1 / 2)) := by
  have hκ := method1MSE_normCDFInv_const_pos
  have ha := tendsto_mul_method1MSE_normCDFInv
  have h1 := ((tendsto_add_atTop_iff_nat 1).2 ha).div ha hκ.ne'
  rw [div_self hκ.ne'] at h1
  have h2 := (h1.mul (tendsto_natCast_div_add_atTop (1 : ℝ))).div_const 2
  rw [one_mul] at h2
  refine h2.congr' ?_
  obtain ⟨c, K, hc, -, hb⟩ := method1MSE_order_normCDFInv
  filter_upwards [eventually_ge_atTop 2] with d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hM : 0 < method1MSE normCDFInv d :=
    lt_of_lt_of_le (by positivity) (hb d hd).1
  simp only [Pi.div_apply]
  push_cast
  field_simp
  ring

/-- **`MSE(d) ~ κ 2^{−d}/d`** (Haas–Giles 2025, §3.4, p. 7, l. 377–379, H3-30: "The Figure 1 also
illustrates that both method 1 and 2 have their MSE divided by 2 each time `d` increases by 1. This
was theoretically expected for method 1 (see [12])"): the method-1 MSE of `Φ⁻¹` is asymptotically
equivalent to `κ 2^{−d}/d` with `κ = (∑_j V_j)/log 2 ≈ 1.5586`. -/
theorem isEquivalent_method1MSE_normCDFInv :
    Asymptotics.IsEquivalent atTop (method1MSE normCDFInv)
      (fun d : ℕ => (∑' j, logCellVar j) / Real.log 2 * ((2 ^ d)⁻¹ / d)) := by
  have hκ := method1MSE_normCDFInv_const_pos
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have h := tendsto_mul_method1MSE_normCDFInv.div_const ((∑' j, logCellVar j) / Real.log 2)
  rw [div_self hκ.ne'] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [Pi.div_apply]
  field_simp

end MLMC
