import MlmcLean.GilesCorollaries
import MlmcLean.LUTAsymptotics
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The normal CDF `Φ`, its inverse `Φ⁻¹`, and the lookup tables for `f = Φ⁻¹` (Haas–Giles 2025, §3)

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), §3 "Approximate random normally distributed numbers", pp. 4–8
(`docs/haas_giles2025.txt`, l. 224–394): the three inversion methods are "based on applying an
approximation of the inverse normal CDF `Φ` [sic: `Φ⁻¹`] to a random uniform variable `U`"
(l. 227–228), and §3.4 compares them as `d → ∞`.  Two slips of that §3 introduction (p. 4,
l. 227–232; tex `sections/3_approximateNormals.tex`, l. 3) are not followed here: it calls `Φ`
"the inverse normal CDF" (`Φ` is the CDF, `Φ⁻¹` its inverse, as in §3.1, l. 249: "the inverse CDF
`Φ⁻¹`"), and it swaps the descriptions of methods 2 and 3 ("The first and the third methods
approximate `Φ⁻¹` by a … PWC function on uniform intervals … The second method … by a … PWL
function on dyadic intervals"), whereas in §3.1–§3.4 method 2 sums PWC tables and method 3 is the
dyadic PWL one (recorded in `notes/statement-audit.md`).  This file follows §3.1–§3.4.

The lookup-table modules `MlmcLean/ApproxNormal.lean`, `MlmcLean/LUTLimits.lean`,
`MlmcLean/LUTAsymptotics.lean` and the streams of `MlmcLean/GilesCorollaries.lean` state their
results for a general `f : ℝ → ℝ` standing for `Φ⁻¹`, with the properties of `Φ⁻¹` they need as
hypotheses (Mathlib has `cdf (gaussianReal 0 1)` but no `Φ⁻¹`).  This file defines `Φ⁻¹`, proves
those properties, and so makes the results unconditional for the actual `f = Φ⁻¹`.  The paper
uses the elementary properties of `Φ` and `Φ⁻¹` (continuity, monotonicity, derivatives, strong
concavity near `0`) without stating them; the docstrings below cite the sentences that rely on
them.

* **`Φ`** (`normCDF x = cdf (gaussianReal 0 1) x`): `Φ' = φ` with `φ(x) = e^{−x²/2}/√(2π)`
  (`hasDerivAt_normCDF`), continuous and strictly increasing, `Φ → 0` at `−∞` and `→ 1` at `∞`,
  and `Φ(−x) = 1 − Φ(x)` (`normCDF_neg`).
* **`Φ⁻¹`** (`normCDFInv`, the inverse of `Φ : ℝ → (0, 1)` on `(0, 1)`, with the junk value `0`
  outside `(0, 1)`): `Φ(Φ⁻¹(u)) = u`, `Φ⁻¹(Φ(x)) = x`, strictly increasing on `(0, 1)`,
  `Φ⁻¹(1 − u) = −Φ⁻¹(u)` for `u ∈ (0, 1)` (`normCDFInv_one_sub`; through the junk value also for
  every real `u`, `normCDFInv_one_sub_forall`, the form the table theorems take as a hypothesis),
  `Φ⁻¹(U) ~ N(0, 1)` for `U` uniform on `(0, 1)` (`map_normCDFInv`, `hasLaw_normCDFInv`), and
  `Φ⁻¹`, `(Φ⁻¹)²` are integrable on `[0, 1]`.
* **Derivatives** (`deriv_normCDFInv`): `(Φ⁻¹)' = 1/φ(Φ⁻¹)` and `(Φ⁻¹)'' = Φ⁻¹/φ(Φ⁻¹)²`; on
  `(0, 1/4]`, `(Φ⁻¹)'' ≤ −π` (`deriv_deriv_normCDFInv_le`: `Φ⁻¹ ≤ −1/2` there, as
  `Φ(1/2) ≤ 1/2 + 1/(2√(2π)) ≤ 3/4`, and `φ² ≤ 1/(2π)`), so `Φ⁻¹ + (π/2) u²` is concave there
  and `2Φ⁻¹(u + s) − Φ⁻¹(u) − Φ⁻¹(u + 2s) ≥ π s²` on every dyadic interval `[2^{−(k+1)}, 2^{−k}]`,
  `k ≥ 2` (`normCDFInv_dyadic_concave`).  (Numerically the best constant on `(0, 1/4]` is
  `−(Φ⁻¹)''(1/4) ≈ 6.68`; `π` is enough.  For `k = 1` this concavity hypothesis fails for every
  `μ > 0`, as `(Φ⁻¹)''(1/2) = 0`, and for `k = 0` too, as `Φ⁻¹` is convex on `[1/2, 1)`; this does
  not mean that the MSE bounds below fail for `k ∈ {0, 1}`, see `dyadic_mse_ge_normCDFInv`.)
* **The lookup tables for `f = Φ⁻¹`**, with no hypothesis on `f`:
  - the sign bit (§3, §3.1): `Z_{2^d−1−j} = −Z_j`, so a table on `[0, 1/2]` suffices
    (`lutValue_mirror_normCDFInv`, `lutValue_upper_half_normCDFInv`);
  - method 1, uniform intervals: `MSE → 0` (`tendsto_method1MSE_normCDFInv`, H3-24), and
    `c 2^{−d}/d ≤ MSE ≤ K 2^{−d}/d` for `d ≥ 2` (`method1MSE_order_normCDFInv`, H3-30) with
    `log(MSE)/d → −log 2` (`tendsto_log_method1MSE_normCDFInv`): the block hypotheses of
    `method1MSE_order` follow from the mean value theorem and the Mills-ratio bounds
    `e^{−3/2} φ(x) ≤ |x| Φ(x) ≤ φ(x)` for `x ≤ −1` (`exp_mul_gaussianPDFReal_le`,
    `neg_mul_normCDF_le`) and `φ(x − 1) ≤ Φ(x)` for `x ≤ 0`, which give `(2^m φ(x))² ≍ m` when
    `Φ(x) ∈ [2^{−(m+1)}, 2^{−m}]` (`normCDFInv_block_bounds`, constants `c = 1/(4e⁴)` and
    `K = 8 (4 + φ(1)⁻²)`).  Numerically `m (2^{−m} (Φ⁻¹)'(u))²` lies in `(1/(2 ln 2), 3.18]` for
    `u` in these blocks, i.e. between `≈ 0.721` (the infimum, approached as `m → ∞` at
    `u = 2^{−m}`) and `≈ 3.179` (the maximum, at `m = 6`, `u = 2^{−7}`);
  - method 2, the streams: the method-1 table of `Φ⁻¹` read at `⌊2^d U⌋` converges in distribution
    to `N(0, 1)`, and the sum of `n` independent streams scaled by `n^{−1/2}` too
    (`lutStream_normCDFInv_tendstoInDistribution`,
    `lutStreams_sum_normCDFInv_tendstoInDistribution`, the premise of H3-07);
  - method 3, dyadic intervals: the MSE on `[2^{−(k+1)}, 2^{−k}]`, `k ≥ 2`, stays above `c > 0`
    (`dyadic_mse_ge_normCDFInv`, `method3_mse_ge_normCDFInv`, H3-34), and the MSE of method 3
    converges to `C = method3Limit Φ⁻¹ > 0` (`tendsto_method3MSE_normCDFInv`, H3-25).

Deviations: `normCDFInv` is `0` outside `(0, 1)` (a junk value; every statement about the tables
only uses `Φ⁻¹` on `(0, 1)` up to null sets, and the value `0` keeps `Φ⁻¹(1 − u) = −Φ⁻¹(u)` exact
for all `u`, as `exists_tendsto_method3MSE` asks); for H3-30 only the order `2^{−d}/d` (and the
halving on average) is proved, not the exact ratio `MSE(d + 1)/MSE(d) → 1/2`; the dyadic lower
bounds are proved for the intervals `[2^{−(k+1)}, 2^{−k}]` with `k ≥ 2`, which suffices for H3-25
and H3-34; the other deviations are those of the general theorems that are instantiated here.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace MLMC

/-! ### The standard normal distribution function `Φ` -/

section NormCDF

/-- The standard normal distribution function `Φ(x) = P(Z ≤ x)`, `Z ~ N(0, 1)` (Haas–Giles 2025,
§3, pp. 4–5, l. 227–249: the normal CDF `Φ`, whose inverse is "the inverse CDF `Φ⁻¹`" (l. 249);
Giles 2015, §5.2, p. 36, l. 1559: "where `Φ` is the Normal cumulative distribution function"), as
Mathlib's `cdf (gaussianReal 0 1)`. -/
noncomputable def normCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The standard normal density in closed form: `φ(x) = e^{−x²/2}/√(2π)`. -/
lemma gaussianPDFReal_std (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  rw [gaussianPDFReal]
  simp

/-- `φ` is continuous. -/
lemma continuous_gaussianPDFReal_std : Continuous (gaussianPDFReal 0 1) := by
  have e : gaussianPDFReal 0 1 = fun x => (√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) :=
    funext gaussianPDFReal_std
  rw [e]
  fun_prop

/-- `φ' = −x φ`. -/
lemma hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have e : gaussianPDFReal 0 1 = fun x => (√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) :=
    funext gaussianPDFReal_std
  have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have e2 : (fun y : ℝ => -y ^ 2 / 2) = fun y => -1 / 2 * y ^ 2 := by
      funext y
      ring
    rw [e2]
    exact (h1.const_mul (-1 / 2 : ℝ)).congr_deriv (by ring)
  rw [e]
  exact ((h.exp).const_mul (√(2 * π))⁻¹).congr_deriv (by ring)

/-- `φ(x) ≤ φ(0) = 1/√(2π)`. -/
lemma gaussianPDFReal_std_le (x : ℝ) : gaussianPDFReal 0 1 x ≤ (√(2 * π))⁻¹ := by
  rw [gaussianPDFReal_std]
  have h : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  have h0 : 0 ≤ (√(2 * π))⁻¹ := by positivity
  nlinarith

/-- `φ` is even and decreasing in `|x|`: if `y² ≤ x²` then `φ(x) ≤ φ(y)`. -/
lemma gaussianPDFReal_std_le_of_sq_le {x y : ℝ} (h : y ^ 2 ≤ x ^ 2) :
    gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 y := by
  rw [gaussianPDFReal_std, gaussianPDFReal_std]
  have h0 : 0 ≤ (√(2 * π))⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) h0

/-- `Φ(x) = ∫_{−∞}^x φ`: `N(0, 1)` has the density `φ`. -/
lemma normCDF_eq_integral (x : ℝ) : normCDF x = ∫ t in Iic x, gaussianPDFReal 0 1 t := by
  rw [normCDF, cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg fun t => gaussianPDFReal_nonneg 0 1 t)]

/-- `Φ(x) = Φ(0) + ∫_0^x φ`. -/
lemma normCDF_eq_add_integral (x : ℝ) :
    normCDF x = normCDF 0 + ∫ t in (0 : ℝ)..x, gaussianPDFReal 0 1 t := by
  have hi : ∀ a : ℝ, IntegrableOn (gaussianPDFReal 0 1) (Iic a) := fun a =>
    (integrable_gaussianPDFReal 0 1).integrableOn
  rw [normCDF_eq_integral, normCDF_eq_integral,
    ← intervalIntegral.integral_Iic_sub_Iic (hi 0) (hi x)]
  ring

/-- **`Φ' = φ`** (a standard fact, not stated in the paper; used implicitly in Haas–Giles 2025, §3,
p. 4, l. 227–228, whose inversion methods apply "an approximation of the inverse normal CDF `Φ`
[sic: `Φ⁻¹`] to a random uniform variable `U`", and in Giles 2015, §5.2, p. 36, l. 1559: "where `Φ`
is the Normal cumulative distribution function"): the standard normal distribution function has
the derivative `φ(x) = e^{−x²/2}/√(2π)` at every `x`. -/
theorem hasDerivAt_normCDF (x : ℝ) : HasDerivAt normCDF (gaussianPDFReal 0 1 x) x :=
  (((continuous_gaussianPDFReal_std.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add
    (normCDF 0)).congr_of_eventuallyEq (Eventually.of_forall normCDF_eq_add_integral)

/-- **`Φ` is continuous** (a standard fact, used implicitly in Haas–Giles 2025, §3, p. 5, l. 249:
"the inverse CDF `Φ⁻¹`", which needs `Φ : ℝ → (0, 1)` to be a continuous bijection). -/
theorem continuous_normCDF : Continuous normCDF :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_normCDF x).continuousAt

/-- **`Φ` is strictly increasing** (a standard fact, used implicitly in Haas–Giles 2025, §3.1,
p. 5, l. 249: "the inverse CDF `Φ⁻¹`", which needs `Φ` to be invertible), since `Φ' = φ > 0`. -/
theorem strictMono_normCDF : StrictMono normCDF :=
  strictMono_of_hasDerivAt_pos hasDerivAt_normCDF fun x => gaussianPDFReal_pos 0 1 x one_ne_zero

/-- **`Φ(x) → 0` as `x → −∞`** (a standard fact, used implicitly in Haas–Giles 2025, §3, p. 4,
l. 231–232, where dyadic intervals are "progressively divided by 2 as we get closer to the
singularities of `Φ⁻¹`": the singularity of `Φ⁻¹` at `0`). -/
theorem tendsto_normCDF_atBot : Tendsto normCDF atBot (𝓝 0) :=
  tendsto_cdf_atBot (gaussianReal 0 1)

/-- **`Φ(x) → 1` as `x → ∞`** (a standard fact, used implicitly in Haas–Giles 2025, §3, p. 4,
l. 231–232, "the singularities of `Φ⁻¹`": the singularity of `Φ⁻¹` at `1`). -/
theorem tendsto_normCDF_atTop : Tendsto normCDF atTop (𝓝 1) :=
  tendsto_cdf_atTop (gaussianReal 0 1)

/-- `0 < Φ(x) < 1`: `0 ≤ Φ(x − 1) < Φ(x) < Φ(x + 1) ≤ 1`. -/
lemma normCDF_mem_Ioo (x : ℝ) : normCDF x ∈ Ioo 0 1 :=
  ⟨(cdf_nonneg (gaussianReal 0 1) (x - 1)).trans_lt (strictMono_normCDF (sub_one_lt x)),
    (strictMono_normCDF (lt_add_one x)).trans_le (cdf_le_one (gaussianReal 0 1) (x + 1))⟩

/-- **The symmetry of `Φ`** (Haas–Giles 2025, §3, p. 5, l. 236: "we exploit the symmetry of `Φ⁻¹`"):
`Φ(−x) = 1 − Φ(x)`, since `N(0, 1)` is symmetric and has no atoms. -/
theorem normCDF_neg (x : ℝ) : normCDF (-x) = 1 - normCDF x := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hmap : (gaussianReal 0 1).map (fun y : ℝ => -y) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have hpre : (fun y : ℝ => -y) ⁻¹' Iic (-x) = Ici x := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_Ici, neg_le_neg_iff]
  have h1 : (gaussianReal 0 1).real (Iic (-x)) = (gaussianReal 0 1).real (Ici x) := by
    calc (gaussianReal 0 1).real (Iic (-x))
        = ((gaussianReal 0 1).map (fun y : ℝ => -y)).real (Iic (-x)) := by rw [hmap]
      _ = (gaussianReal 0 1).real (Ici x) := by
          rw [map_measureReal_apply measurable_neg measurableSet_Iic, hpre]
  unfold normCDF
  rw [cdf_eq_real, cdf_eq_real, h1, measureReal_congr Ioi_ae_eq_Ici.symm, ← compl_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic]

/-- `Φ(0) = 1/2`. -/
lemma normCDF_zero : normCDF 0 = 1 / 2 := by
  have h := normCDF_neg 0
  rw [neg_zero] at h
  linarith

end NormCDF

/-! ### The inverse normal CDF `Φ⁻¹` -/

section NormCDFInv

/-- The inverse normal CDF `Φ⁻¹ : (0, 1) → ℝ` (Haas–Giles 2025, §3.1, p. 5, l. 249: "the inverse
CDF `Φ⁻¹`"; §3, p. 4, l. 227–228: "applying an approximation of the inverse normal CDF `Φ` [sic:
`Φ⁻¹`; the paper's `Φ` is the CDF] to a random uniform variable `U`"), the inverse of the
bijection `normCDF : ℝ → (0, 1)`.  Outside `(0, 1)`, where `Φ⁻¹` is not defined (it tends to
`∓∞` at `0` and `1`), `normCDFInv` takes the junk value `0`; this choice keeps the symmetry
`Φ⁻¹(1 − u) = −Φ⁻¹(u)` true for every real `u` (`normCDFInv_one_sub_forall`). -/
noncomputable def normCDFInv (u : ℝ) : ℝ := (Ioo (0 : ℝ) 1).indicator (Function.invFun normCDF) u

/-- Every `u ∈ (0, 1)` is a value of `Φ` (intermediate value theorem). -/
lemma exists_normCDF_eq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : ∃ x, normCDF x = u := by
  obtain ⟨a, ha⟩ := (tendsto_normCDF_atBot.eventually (gt_mem_nhds hu.1)).exists
  obtain ⟨b, hb⟩ := (tendsto_normCDF_atTop.eventually (lt_mem_nhds hu.2)).exists
  exact intermediate_value_univ a b continuous_normCDF ⟨ha.le, hb.le⟩

/-- **`Φ(Φ⁻¹(u)) = u`** for `u ∈ (0, 1)` (the defining property of "the inverse CDF `Φ⁻¹`",
Haas–Giles 2025, §3.1, p. 5, l. 249, which the paper uses without proof). -/
theorem normCDF_normCDFInv {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : normCDF (normCDFInv u) = u := by
  rw [normCDFInv, indicator_of_mem hu]
  exact Function.invFun_eq (exists_normCDF_eq hu)

/-- **`Φ⁻¹(Φ(x)) = x`** for every real `x` (the other half of "the inverse CDF `Φ⁻¹`",
Haas–Giles 2025, §3.1, p. 5, l. 249, used without proof in the paper). -/
theorem normCDFInv_normCDF (x : ℝ) : normCDFInv (normCDF x) = x := by
  rw [normCDFInv, indicator_of_mem (normCDF_mem_Ioo x)]
  exact Function.leftInverse_invFun strictMono_normCDF.injective x

/-- The junk value: `normCDFInv u = 0` for `u ∉ (0, 1)`. -/
lemma normCDFInv_of_notMem {u : ℝ} (hu : u ∉ Ioo (0 : ℝ) 1) : normCDFInv u = 0 := by
  rw [normCDFInv, indicator_of_notMem hu]

/-- `Φ⁻¹(u) ≤ x ↔ u ≤ Φ(x)` for `u ∈ (0, 1)`. -/
lemma normCDFInv_le_iff {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    normCDFInv u ≤ x ↔ u ≤ normCDF x := by
  rw [← strictMono_normCDF.le_iff_le, normCDF_normCDFInv hu]

/-- **`Φ⁻¹` is strictly increasing on `(0, 1)`** (a standard fact, used implicitly in Haas–Giles
2025, §3.1, p. 5, l. 249–250: "the inverse CDF `Φ⁻¹` is approximated by a constant value on uniform
intervals", and in the analysis of the tables, which needs `Φ⁻¹` monotone). -/
theorem strictMonoOn_normCDFInv : StrictMonoOn normCDFInv (Ioo (0 : ℝ) 1) := fun u hu v hv huv => by
  rw [← strictMono_normCDF.lt_iff_lt, normCDF_normCDFInv hu, normCDF_normCDFInv hv]
  exact huv

/-- **The symmetry of `Φ⁻¹`** (Haas–Giles 2025, §3, p. 5, l. 236–237: "we exploit the symmetry of
`Φ⁻¹` so we only need to approximate it on `[0, 1/2]`"; §3.1: "The leading bit of `j` gives the
sign"): `Φ⁻¹(1 − u) = −Φ⁻¹(u)` for `u ∈ (0, 1)`, from `Φ(−x) = 1 − Φ(x)` (`normCDF_neg`). The form
for every real `u`, which the table theorems take as a hypothesis, is
`normCDFInv_one_sub_forall`. -/
theorem normCDFInv_one_sub {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    normCDFInv (1 - u) = -normCDFInv u := by
  have h : normCDF (-normCDFInv u) = 1 - u := by rw [normCDF_neg, normCDF_normCDFInv hu]
  rw [← h, normCDFInv_normCDF]

/-- The symmetry `Φ⁻¹(1 − u) = −Φ⁻¹(u)` for every real `u`, in the form of the hypothesis
`hf`/`hodd` of `lutValue_mirror`, `tendsto_method3MSE` and `method1MSE_order`: for `u ∈ (0, 1)`
it is `normCDFInv_one_sub`; outside `(0, 1)` both sides are the junk value `0` (inside the
integrals over `[0, 1]` that these theorems take, this junk part only concerns the null set
`{0, 1}`). -/
lemma normCDFInv_one_sub_forall (u : ℝ) : normCDFInv (1 - u) = -normCDFInv u := by
  by_cases hu : u ∈ Ioo (0 : ℝ) 1
  · exact normCDFInv_one_sub hu
  · have h1 : 1 - u ∉ Ioo (0 : ℝ) 1 := fun h => hu ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [normCDFInv_of_notMem hu, normCDFInv_of_notMem h1, neg_zero]

/-- `Φ⁻¹` is measurable. -/
lemma measurable_normCDFInv : Measurable normCDFInv := by
  refine measurable_of_Iic fun x => ?_
  have e : normCDFInv ⁻¹' Iic x =
      (Ioo 0 1 ∩ Iic (normCDF x)) ∪ ((Ioo 0 1)ᶜ ∩ {_u | 0 ≤ x}) := by
    ext u
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · rw [normCDFInv_le_iff hu]
      tauto
    · rw [normCDFInv_of_notMem hu]
      tauto
  rw [e]
  exact (measurableSet_Ioo.inter measurableSet_Iic).union
    (measurableSet_Ioo.compl.inter (MeasurableSet.const _))

/-- **`Φ⁻¹(U) ~ N(0, 1)` for `U` uniform on `(0, 1)`** (Haas–Giles 2025, §3, p. 4, l. 226–228: "All
methods below are classified as inversion methods, because they are based on applying an
approximation of the inverse normal CDF `Φ` [sic: `Φ⁻¹`] to a random uniform variable `U`"; the
paper uses this inversion principle without proof): the image of the Lebesgue measure on `(0, 1)`
under `Φ⁻¹` is `N(0, 1)`. -/
theorem map_normCDFInv : (volume.restrict (Ioo (0 : ℝ) 1)).map normCDFInv = gaussianReal 0 1 := by
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply measurable_normCDFInv measurableSet_Iic,
    Measure.restrict_apply (measurable_normCDFInv measurableSet_Iic)]
  have e : normCDFInv ⁻¹' Iic x ∩ Ioo 0 1 = Ioc 0 (normCDF x) := by
    ext u
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2.1, (normCDFInv_le_iff h2 x).1 h1⟩
    · rintro ⟨h1, h2⟩
      have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨h1, lt_of_le_of_lt h2 (normCDF_mem_Ioo x).2⟩
      exact ⟨(normCDFInv_le_iff hu x).2 h2, hu⟩
  rw [e, Real.volume_Ioc, sub_zero]
  exact ofReal_cdf (gaussianReal 0 1) x

/-- **`Φ⁻¹` has law `N(0, 1)` under the uniform law on `(0, 1)`** (Haas–Giles 2025, §3, p. 4,
l. 226–228: "inversion methods … applying an approximation of the inverse normal CDF `Φ` [sic:
`Φ⁻¹`] to a random uniform variable `U`"), in the form of the hypothesis of
`lutStream_tendstoInDistribution`. -/
theorem hasLaw_normCDFInv : HasLaw normCDFInv (gaussianReal 0 1) (volume.restrict (Ioo 0 1)) :=
  ⟨measurable_normCDFInv.aemeasurable, map_normCDFInv⟩

/-- **Inversion sampling** (Haas–Giles 2025, §3, p. 4, l. 226–228: "inversion methods … applying an
approximation of the inverse normal CDF `Φ` [sic: `Φ⁻¹`] to a random uniform variable `U`"): if `U`
is uniform on `(0, 1)` then `Z = Φ⁻¹(U) ~ N(0, 1)`. -/
theorem hasLaw_normCDFInv_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U (volume.restrict (Ioo 0 1)) P) :
    HasLaw (fun ω => normCDFInv (U ω)) (gaussianReal 0 1) P :=
  hasLaw_normCDFInv.comp hU

/-- **`Φ⁻¹` and `(Φ⁻¹)²` are integrable on `[0, 1]`** (the standing assumption on `f = Φ⁻¹` behind
Haas–Giles 2025, §3.1, (14)–(15), p. 5, l. 258–264: "the mean squared error (MSE)
`∫_{u_j}^{u_{j+1}} (Z_j − Φ⁻¹(u))² du` … This gives that `Z_j` is the mean of `Φ⁻¹` over the
interval `I_j`"; the paper does not state it): a standard normal variable has finite first and
second moments. -/
theorem intervalIntegrable_normCDFInv : IntervalIntegrable normCDFInv volume 0 1 ∧
    IntervalIntegrable (fun u => normCDFInv u ^ 2) volume 0 1 :=
  intervalIntegrable_of_hasLaw_gaussian hasLaw_normCDFInv

end NormCDFInv

/-! ### The derivatives of `Φ⁻¹` and its strong concavity near `0` -/

section Derivatives

/-- `Φ⁻¹` is continuous on `(0, 1)`: it is monotone there and maps `(0, 1)` onto `ℝ`. -/
lemma continuousOn_normCDFInv : ContinuousOn normCDFInv (Ioo (0 : ℝ) 1) := by
  have himg : normCDFInv '' Ioo 0 1 = univ :=
    eq_univ_of_forall fun x => ⟨normCDF x, normCDF_mem_Ioo x, normCDFInv_normCDF x⟩
  intro u hu
  refine (continuousAt_of_monotoneOn_of_image_mem_nhds strictMonoOn_normCDFInv.monotoneOn
    (isOpen_Ioo.mem_nhds hu) ?_).continuousWithinAt
  rw [himg]
  exact univ_mem

/-- **The derivative of `Φ⁻¹`** (a standard fact, not stated in the paper; used implicitly in
Haas–Giles 2025, §3.4, p. 7, l. 366–368, through the convergence analysis of [12]): `(Φ⁻¹)'(u) =
1/φ(Φ⁻¹(u))` for `u ∈ (0, 1)`, by the inverse function rule and `Φ' = φ > 0`. -/
theorem hasDerivAt_normCDFInv {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt normCDFInv (gaussianPDFReal 0 1 (normCDFInv u))⁻¹ u :=
  HasDerivAt.of_local_left_inverse (continuousOn_normCDFInv.continuousAt (isOpen_Ioo.mem_nhds hu))
    (hasDerivAt_normCDF _) (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne'
    (eventually_of_mem (isOpen_Ioo.mem_nhds hu) fun _ hv => normCDF_normCDFInv hv)

/-- The derivative of `u ↦ 1/φ(Φ⁻¹(u))` is `Φ⁻¹(u)/φ(Φ⁻¹(u))²` on `(0, 1)` (from `φ' = −xφ`). -/
lemma hasDerivAt_inv_gaussianPDFReal_normCDFInv {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun v => (gaussianPDFReal 0 1 (normCDFInv v))⁻¹)
      (normCDFInv u / gaussianPDFReal 0 1 (normCDFInv u) ^ 2) u := by
  have hφ : gaussianPDFReal 0 1 (normCDFInv u) ≠ 0 := (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne'
  have h1 := (hasDerivAt_gaussianPDFReal_std (normCDFInv u)).comp u (hasDerivAt_normCDFInv hu)
  refine (h1.inv hφ).congr_deriv ?_
  simp only [Function.comp_apply]
  field_simp

/-- **The first two derivatives of `Φ⁻¹`** (standard facts, not stated in the paper; they quantify
Haas–Giles 2025, §3, p. 4, l. 231–232: dyadic intervals are "progressively divided by 2 as we get
closer to the singularities of `Φ⁻¹`"): for `u ∈ (0, 1)` and `x = Φ⁻¹(u)`, `(Φ⁻¹)'(u) = 1/φ(x)`
and `(Φ⁻¹)''(u) = x/φ(x)²`, where `φ(x) = e^{−x²/2}/√(2π)` (so `(Φ⁻¹)'' = 2π x e^{x²}`). -/
theorem deriv_normCDFInv {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    deriv normCDFInv u = (gaussianPDFReal 0 1 (normCDFInv u))⁻¹ ∧
      HasDerivAt (deriv normCDFInv)
        (normCDFInv u / gaussianPDFReal 0 1 (normCDFInv u) ^ 2) u ∧
      deriv (deriv normCDFInv) u = normCDFInv u / gaussianPDFReal 0 1 (normCDFInv u) ^ 2 := by
  have h2 : HasDerivAt (deriv normCDFInv)
      (normCDFInv u / gaussianPDFReal 0 1 (normCDFInv u) ^ 2) u :=
    (hasDerivAt_inv_gaussianPDFReal_normCDFInv hu).congr_of_eventuallyEq
      (eventually_of_mem (isOpen_Ioo.mem_nhds hu) fun _ hv => (hasDerivAt_normCDFInv hv).deriv)
  exact ⟨(hasDerivAt_normCDFInv hu).deriv, h2, h2.deriv⟩

/-- `Φ(1/2) ≤ 3/4`: `Φ(1/2) − Φ(0) = ∫_0^{1/2} φ ≤ φ(0)/2 = 1/(2√(2π)) ≤ 1/4`. -/
lemma normCDF_half_le : normCDF (1 / 2) ≤ 3 / 4 := by
  have hint : ∫ t in (0 : ℝ)..(1 / 2), gaussianPDFReal 0 1 t ≤
      ∫ _ in (0 : ℝ)..(1 / 2), (√(2 * π))⁻¹ :=
    intervalIntegral.integral_mono_on (by norm_num)
      (continuous_gaussianPDFReal_std.intervalIntegrable _ _) intervalIntegrable_const
      fun t _ => gaussianPDFReal_std_le t
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hs : (2 : ℝ) ≤ √(2 * π) := (Real.le_sqrt' (by norm_num)).2 (by nlinarith [two_le_pi])
  have hinv : (√(2 * π))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  rw [normCDF_eq_add_integral, normCDF_zero]
  linarith

/-- `Φ⁻¹(u) ≤ −1/2` for `0 < u ≤ 1/4`. -/
lemma normCDFInv_le_neg_half {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 4) :
    normCDFInv u ≤ -(1 / 2) := by
  rw [normCDFInv_le_iff ⟨hu0, by linarith⟩, normCDF_neg]
  linarith [normCDF_half_le]

/-- `(Φ⁻¹)''(u) = x/φ(x)² ≤ −π` for `0 < u ≤ 1/4`, `x = Φ⁻¹(u) ≤ −1/2`: `φ(x)² ≤ 1/(2π)`. -/
lemma normCDFInv_div_sq_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 4) :
    normCDFInv u / gaussianPDFReal 0 1 (normCDFInv u) ^ 2 ≤ -π := by
  have hxle : normCDFInv u ≤ -(1 / 2) := normCDFInv_le_neg_half hu0 hu
  have hφ : 0 < gaussianPDFReal 0 1 (normCDFInv u) := gaussianPDFReal_pos 0 1 _ one_ne_zero
  have hsq : gaussianPDFReal 0 1 (normCDFInv u) ^ 2 ≤ (2 * π)⁻¹ := by
    calc gaussianPDFReal 0 1 (normCDFInv u) ^ 2 ≤ ((√(2 * π))⁻¹) ^ 2 :=
          pow_le_pow_left₀ hφ.le (gaussianPDFReal_std_le _) 2
      _ = (2 * π)⁻¹ := by rw [inv_pow, Real.sq_sqrt (by positivity)]
  have hpi : π * gaussianPDFReal 0 1 (normCDFInv u) ^ 2 ≤ 1 / 2 := by
    have hπ := pi_pos.ne'
    calc π * gaussianPDFReal 0 1 (normCDFInv u) ^ 2 ≤ π * (2 * π)⁻¹ :=
          mul_le_mul_of_nonneg_left hsq pi_pos.le
      _ = 1 / 2 := by field_simp
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **`(Φ⁻¹)'' ≤ −π` on `(0, 1/4]`** (not stated in the paper; the strong concavity of `Φ⁻¹` near
its singularity at `0` behind Haas–Giles 2025, §3.4, p. 7, l. 366–368: "the dyadic intervals give
`MSE → C`, for some positive constant `C`"): for `0 < u ≤ 1/4`, `(Φ⁻¹)''(u) = x/φ(x)² ≤ −π`, since
`x = Φ⁻¹(u) ≤ −1/2` and `φ(x)² ≤ 1/(2π)`. -/
theorem deriv_deriv_normCDFInv_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 4) :
    deriv (deriv normCDFInv) u ≤ -π := by
  rw [(deriv_normCDFInv ⟨hu0, by linarith⟩).2.2]
  exact normCDFInv_div_sq_le hu0 hu

/-- **`Φ⁻¹` is strongly concave on `(0, 1/4]`** (not stated in the paper; the property of `Φ⁻¹`
behind Haas–Giles 2025, §3.4, p. 7, l. 366–368: "the dyadic intervals give `MSE → C`, for some
positive constant `C`"): `u ↦ Φ⁻¹(u) + (π/2) u²` is concave on `(0, 1/4]`, i.e. `(Φ⁻¹)'' ≤ −π`
there. -/
theorem concaveOn_normCDFInv_add_sq :
    ConcaveOn ℝ (Ioc 0 (1 / 4)) (fun u => normCDFInv u + π / 2 * u ^ 2) := by
  have hsub : Ioc (0 : ℝ) (1 / 4) ⊆ Ioo 0 1 := fun u hu => ⟨hu.1, by linarith [hu.2]⟩
  have hint : interior (Ioc (0 : ℝ) (1 / 4)) = Ioo 0 (1 / 4) := interior_Ioc
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioc 0 (1 / 4))
    (f' := fun u => (gaussianPDFReal 0 1 (normCDFInv u))⁻¹ + π * u)
    (f'' := fun u => normCDFInv u / gaussianPDFReal 0 1 (normCDFInv u) ^ 2 + π) ?_ ?_ ?_ ?_
  · exact (continuousOn_normCDFInv.mono hsub).add (by fun_prop)
  · intro x hx
    rw [hint] at hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h2 : HasDerivAt (fun u : ℝ => π / 2 * u ^ 2) (π * x) x :=
      (h1.const_mul (π / 2)).congr_deriv (by ring)
    exact ((hasDerivAt_normCDFInv hx').add h2).hasDerivWithinAt
  · intro x hx
    rw [hint] at hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    have h2 : HasDerivAt (fun u : ℝ => π * u) π x := by
      simpa using (hasDerivAt_id x).const_mul π
    exact ((hasDerivAt_inv_gaussianPDFReal_normCDFInv hx').add h2).hasDerivWithinAt
  · intro x hx
    rw [hint] at hx
    linarith [normCDFInv_div_sq_le hx.1 hx.2.le]

/-- **The strong concavity of `Φ⁻¹` as second differences** (not stated in the paper; the property
of `Φ⁻¹` behind Haas–Giles 2025, §3.4, p. 7, l. 366–368: "the dyadic intervals give `MSE → C`, for
some positive constant `C`"): for `0 < u` and `0 ≤ s` with `u + 2s ≤ 1/4`,
`2Φ⁻¹(u + s) − Φ⁻¹(u) − Φ⁻¹(u + 2s) ≥ π s²`. -/
theorem normCDFInv_second_diff {u s : ℝ} (hu : 0 < u) (hs : 0 ≤ s) (hus : u + 2 * s ≤ 1 / 4) :
    π * s ^ 2 ≤ 2 * normCDFInv (u + s) - normCDFInv u - normCDFInv (u + 2 * s) := by
  have h := concaveOn_normCDFInv_add_sq.2 (show u ∈ Ioc (0 : ℝ) (1 / 4) from ⟨hu, by linarith⟩)
    (show u + 2 * s ∈ Ioc (0 : ℝ) (1 / 4) from ⟨by linarith, hus⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1 / 2 * u + 1 / 2 * (u + 2 * s) = u + s := by ring
  rw [e] at h
  linarith

/-- **`Φ⁻¹` is strongly concave on every dyadic interval `[2^{−(k+1)}, 2^{−k}]`, `k ≥ 2`** (not
stated in the paper; the property of `Φ⁻¹` behind Haas–Giles 2025, §3.4, p. 7, l. 366–368: "the
dyadic intervals give `MSE → C`, for some positive constant `C`"): the hypothesis `hconc` of
`dyadic_mse_ge`, `method3_mse_ge` and `exists_tendsto_method3MSE` holds for `f = Φ⁻¹` with
`μ = π`.  It fails for `k ∈ {0, 1}` (for every `μ > 0`): `(Φ⁻¹)''(1/2) = 0`, and `Φ⁻¹` is convex
on `[1/2, 1)`. -/
theorem normCDFInv_dyadic_concave {k : ℕ} (hk : 2 ≤ k) (u s : ℝ)
    (hu : ((2 : ℝ) ^ (k + 1))⁻¹ ≤ u) (hs : 0 ≤ s) (hus : u + 2 * s ≤ ((2 : ℝ) ^ k)⁻¹) :
    π * s ^ 2 ≤ 2 * normCDFInv (u + s) - normCDFInv u - normCDFInv (u + 2 * s) := by
  have h4 : ((2 : ℝ) ^ k)⁻¹ ≤ 1 / 4 := (inv_two_pow_anti hk).trans (by norm_num)
  exact normCDFInv_second_diff (lt_of_lt_of_le (by positivity) hu) hs (hus.trans h4)

end Derivatives

/-! ### The lookup-table results for `f = Φ⁻¹` -/

section LUT

/-- **The LUT values of `Φ⁻¹` on mirrored intervals are opposite** (Haas–Giles 2025, §3, p. 5,
l. 236–237: "we exploit the symmetry of `Φ⁻¹` so we only need to approximate it on `[0, 1/2]`"):
for `j < 2^d`, `Z_{2^d−1−j} = −Z_j`, where `Z_j = 2^d ∫_{I_j} Φ⁻¹` is the LUT value (15).
`lutValue_mirror` with `f = Φ⁻¹`, whose hypothesis `f(1 − u) = −f(u)` is
`normCDFInv_one_sub_forall`. -/
theorem lutValue_mirror_normCDFInv {d j : ℕ} (hj : j < 2 ^ d) :
    lutValue normCDFInv d (2 ^ d - 1 - j) = -lutValue normCDFInv d j :=
  lutValue_mirror normCDFInv_one_sub_forall hj

/-- **For `Φ⁻¹`, a LUT on `[0, 1/2]` and a sign bit suffice** (Haas–Giles 2025, §3.1, p. 5,
l. 250–253: "We simply construct a Look-Up-Table (LUT) of size `2^{d−1}` … The leading bit of `j`
gives the sign of the normal increment, which allows us to extend the approximation of `Φ⁻¹` on
the interval `[1/2, 1]`"): for `d ≥ 1` and `2^{d−1} ≤ j < 2^d`, the mirror index `2^d − 1 − j` is in
the LUT range `[0, 2^{d−1})` and `Z_j = −Z_{2^d−1−j}`.  `lutValue_upper_half` with `f = Φ⁻¹`. -/
theorem lutValue_upper_half_normCDFInv {d j : ℕ} (hd : 1 ≤ d) (hj1 : 2 ^ (d - 1) ≤ j)
    (hj : j < 2 ^ d) :
    2 ^ d - 1 - j < 2 ^ (d - 1) ∧
      lutValue normCDFInv d j = -lutValue normCDFInv d (2 ^ d - 1 - j) :=
  lutValue_upper_half normCDFInv_one_sub_forall hd hj1 hj

/-- **Uniform intervals give `MSE → 0` for `Φ⁻¹`** (Haas–Giles 2025, §3.4, p. 7, l. 366–367, H3-24:
"as `d` tends to infinity, the uniform intervals give `MSE → 0`"): `tendsto_method1MSE` with
`f = Φ⁻¹`, whose hypotheses (monotone on `(0, 1)`, `f` and `f²` integrable) are proved here. -/
theorem tendsto_method1MSE_normCDFInv : Tendsto (method1MSE normCDFInv) atTop (𝓝 0) :=
  tendsto_method1MSE strictMonoOn_normCDFInv.monotoneOn intervalIntegrable_normCDFInv.1
    intervalIntegrable_normCDFInv.2

/-- **The lookup-table stream of `Φ⁻¹` converges in distribution to `N(0, 1)`** (Haas–Giles 2025,
§3.2, p. 5, l. 278, the premise of H3-07: "each `X^{(i)}` follows approximately the distribution
`N(0,1/n)`"; the table is that of method 1, §3.1, (15)).  For `U` uniform on `(0, 1)`, the method-1
table `Z_j = 2^d ∫_{I_j} Φ⁻¹` read at `j = ⌊2^d U⌋` converges in distribution to `N(0, 1)` as
`d → ∞`: `lutStream_tendstoInDistribution` with no hypothesis on `f`. -/
theorem lutStream_normCDFInv_tendstoInDistribution {Ω Ω' : Type*} [MeasurableSpace Ω]
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {U : Ω → ℝ} (hU : HasLaw U (volume.restrict (Ioo 0 1)) P)
    {G : Ω' → ℝ} (hG : HasLaw G (gaussianReal 0 1) P') :
    TendstoInDistribution (fun (d : ℕ) ω => lutValue normCDFInv d ⌊(2 : ℝ) ^ d * U ω⌋₊) atTop G
      (fun _ => P) P' :=
  lutStream_tendstoInDistribution strictMonoOn_normCDFInv.monotoneOn hasLaw_normCDFInv hU hG

/-- **The sum of `n` lookup-table streams of `Φ⁻¹` is approximately `N(0, 1)`** (Haas–Giles 2025,
§3.2, p. 5, l. 276–280, H3-07: "produce an approximate random number `X^{(1)}` from the first `d/n`
bits of `j`, then `X^{(2)}` from the next `d/n` bits and so on, where each `X^{(i)}` follows
approximately the distribution `N(0,1/n)`. Then `∑_{i=1}^n X^{(i)}` has approximately the
distribution `N(0,1)`"). For independent `U_1, …, U_n` uniform on `(0, 1)`, `n ≥ 1`, the streams
`X_d^{(i)} = n^{−1/2} Z_{⌊2^d U_i⌋}` of the method-1 table of `Φ⁻¹` converge in distribution to
`N(0, 1/n)` and their sum to `N(0, 1)`: `lutStreams_sum_tendstoInDistribution` with no hypothesis on
`f` (same deviations: the scaled method-1 table, not the table optimised by (16)). -/
theorem lutStreams_sum_normCDFInv_tendstoInDistribution {Ω Ω' : Type*} [MeasurableSpace Ω]
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {n : ℕ} (hn : 0 < n) {U : Fin n → Ω → ℝ}
    (hU : ∀ i, HasLaw (U i) (volume.restrict (Ioo 0 1)) P) (hind : iIndepFun U P)
    {G : Ω' → ℝ} (hG : HasLaw G (gaussianReal 0 1) P') :
    (∀ i, TendstoInDistribution
      (fun (d : ℕ) ω => (√(n : ℝ))⁻¹ * lutValue normCDFInv d ⌊(2 : ℝ) ^ d * U i ω⌋₊) atTop id
      (fun _ => P) (gaussianReal 0 (n : ℝ≥0)⁻¹)) ∧
    TendstoInDistribution
      (fun (d : ℕ) ω => ∑ i, (√(n : ℝ))⁻¹ * lutValue normCDFInv d ⌊(2 : ℝ) ^ d * U i ω⌋₊) atTop G
      (fun _ => P) P' :=
  lutStreams_sum_tendstoInDistribution strictMonoOn_normCDFInv.monotoneOn hasLaw_normCDFInv hn hU
    hind hG

/-- **Dyadic intervals keep a positive mean-square error for `Φ⁻¹`** (Haas–Giles 2025, §3.4, p. 7,
l. 367–368: "the dyadic intervals give `MSE → C`, for some positive constant `C`"; H3-25, H3-34).
For every `k ≥ 2` there is `c > 0` such that for every `d ≥ k + 3` and all `a`, `b`, the mean-square
error of the values `a + b j` against `Φ⁻¹` on the cells of `[2^{−(k+1)}, 2^{−k}]` is at least `c`:
`dyadic_mse_ge` with `μ = π` (`normCDFInv_dyadic_concave`).  The same lower bound holds for
`k ∈ {0, 1}` too (numerically, the least such sum decreases with `d` to the least affine error
`E_0 ≈ 1.8·10⁻²` on `[1/2, 1]` resp. `E_1 ≈ 7.9·10⁻⁶` on `[1/4, 1/2]`), but it is not covered here,
because the concavity hypothesis of `dyadic_mse_ge` fails there; `k = 2` already gives H3-34 and
H3-25. -/
theorem dyadic_mse_ge_normCDFInv {k : ℕ} (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, k + 3 ≤ d → ∀ a b : ℝ,
      c ≤ ∑ j ∈ Finset.Ico (2 ^ (d - k - 1) : ℕ) (2 ^ (d - k)),
        ∫ u in gridPt d j..gridPt d (j + 1), (a + b * j - normCDFInv u) ^ 2 :=
  dyadic_mse_ge intervalIntegrable_normCDFInv.1 intervalIntegrable_normCDFInv.2 pi_pos
    (normCDFInv_dyadic_concave hk)

/-- **With dyadic intervals the MSE of `Φ⁻¹` cannot be arbitrarily small** (Haas–Giles 2025, §3.4,
p. 8, l. 393–394, H3-34: "with dyadic intervals, the MSE value cannot be arbitrarily small"). For
every `k ≥ 2` there is `c > 0` such that for every `d ≥ k + 3`, every approximation taking the
values `w_j` on the cells `I_j`, `j < 2^d`, with `w_j = a + b j` on the cells of
`[2^{−(k+1)}, 2^{−k}]` (as method 3 does), has `∑_j ∫_{I_j} (w_j − Φ⁻¹)² ≥ c`; in particular the MSE
does not tend to `0`. `method3_mse_ge` and `method3_mse_not_tendsto_zero` with `f = Φ⁻¹`.  As in
`dyadic_mse_ge_normCDFInv`, the bound also holds (numerically) for `k ∈ {0, 1}` but is not covered,
since the library's concavity hypothesis fails there; one `k` (e.g. `k = 2`) suffices for the
paper's claim. -/
theorem method3_mse_ge_normCDFInv {k : ℕ} (hk : 2 ≤ k) :
    (∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, k + 3 ≤ d → ∀ w : ℕ → ℝ,
      (∃ a b : ℝ, ∀ j ∈ Finset.Ico (2 ^ (d - k - 1)) (2 ^ (d - k)), w j = a + b * j) →
        c ≤ ∑ j ∈ Finset.range (2 ^ d),
          ∫ u in gridPt d j..gridPt d (j + 1), (w j - normCDFInv u) ^ 2) ∧
    ∀ w : ℕ → ℕ → ℝ,
      (∀ d, ∃ a b : ℝ, ∀ j ∈ Finset.Ico (2 ^ (d - k - 1)) (2 ^ (d - k)), w d j = a + b * j) →
      ¬ Tendsto (fun d => ∑ j ∈ Finset.range (2 ^ d),
        ∫ u in gridPt d j..gridPt d (j + 1), (w d j - normCDFInv u) ^ 2) atTop (𝓝 0) :=
  ⟨method3_mse_ge intervalIntegrable_normCDFInv.1 intervalIntegrable_normCDFInv.2 pi_pos
      (normCDFInv_dyadic_concave hk),
    fun w hw => method3_mse_not_tendsto_zero intervalIntegrable_normCDFInv.1
      intervalIntegrable_normCDFInv.2 pi_pos (normCDFInv_dyadic_concave hk) w hw⟩

/-- **Dyadic intervals give `MSE → C > 0` for `Φ⁻¹`** (Haas–Giles 2025, §3.4, p. 7, l. 366–368,
H3-25: "as `d` tends to infinity, … the dyadic intervals give `MSE → C`, for some positive constant
`C`"). The mean-square error of method 3 (the least-squares fit (19) on each dyadic interval, the
sign bit on `[1/2, 1]`) for `f = Φ⁻¹` converges to `C = method3Limit Φ⁻¹ = 2 ∑_{k≥1} E_k > 0`:
`tendsto_method3MSE` and `method3Limit_pos` with `f = Φ⁻¹`, whose hypotheses (integrability, the
symmetry `Φ⁻¹(1 − u) = −Φ⁻¹(u)` and strong concavity on `[1/8, 1/4]`) are proved here. -/
theorem tendsto_method3MSE_normCDFInv :
    0 < method3Limit normCDFInv ∧
      Tendsto (method3MSE normCDFInv) atTop (𝓝 (method3Limit normCDFInv)) :=
  ⟨method3Limit_pos intervalIntegrable_normCDFInv.1 intervalIntegrable_normCDFInv.2
      (k := 2) (by norm_num) pi_pos (normCDFInv_dyadic_concave le_rfl),
    tendsto_method3MSE intervalIntegrable_normCDFInv.1 intervalIntegrable_normCDFInv.2
      normCDFInv_one_sub_forall⟩

end LUT

/-! ### Mills-ratio bounds and the order `2^{−d}/d` of the method-1 error for `Φ⁻¹` -/

section Mills

/-- `φ` is even: `φ(−x) = φ(x)`. -/
lemma gaussianPDFReal_std_neg (x : ℝ) : gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  rw [gaussianPDFReal_std, gaussianPDFReal_std, neg_sq]

/-- For `a ≤ b ≤ 0`, `(b − a) φ(a) ≤ Φ(b) − Φ(a)` (mean value theorem; `φ` increases on
`(−∞, 0]`). -/
lemma mul_gaussianPDFReal_le_normCDF_sub {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    (b - a) * gaussianPDFReal 0 1 a ≤ normCDF b - normCDF a := by
  rcases hab.eq_or_lt with h | h
  · rw [h, sub_self, sub_self, zero_mul]
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope normCDF (gaussianPDFReal 0 1) h
    continuous_normCDF.continuousOn fun x _ => hasDerivAt_normCDF x
  have hle : gaussianPDFReal 0 1 a ≤ gaussianPDFReal 0 1 c :=
    gaussianPDFReal_std_le_of_sq_le (by nlinarith [hc.1, hc.2])
  rw [hcd, le_div_iff₀ (sub_pos.2 h)] at hle
  linarith

/-- `φ(x − 1) ≤ Φ(x)` for `x ≤ 0`. -/
lemma gaussianPDFReal_sub_one_le_normCDF {x : ℝ} (hx : x ≤ 0) :
    gaussianPDFReal 0 1 (x - 1) ≤ normCDF x := by
  have h := mul_gaussianPDFReal_le_normCDF_sub (show x - 1 ≤ x by linarith) hx
  have h0 := (normCDF_mem_Ioo (x - 1)).1
  rw [sub_sub_cancel, one_mul] at h
  linarith

/-- **A lower Mills-ratio bound** (a standard estimate, not stated in the paper; it is used here for
Haas–Giles 2025, §3.4, p. 7, l. 378–379, H3-30: "both method 1 and 2 have their MSE divided by 2
each time `d` increases by 1. This was theoretically expected for method 1 (see [12])"):
`e^{−3/2} φ(x) ≤ |x| Φ(x)` for `x ≤ −1`, by comparing `Φ(x)` with the integral of `φ` over
`[x − 1/|x|, x]`. -/
theorem exp_mul_gaussianPDFReal_le {x : ℝ} (hx : x ≤ -1) :
    Real.exp (-(3 / 2)) * gaussianPDFReal 0 1 x ≤ -x * normCDF x := by
  have hx0 : x < 0 := by linarith
  have hx0' : x ≠ 0 := hx0.ne
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hinv0 : 1 / x < 0 := by rw [one_div]; exact inv_lt_zero.2 hx0
  have h := mul_gaussianPDFReal_le_normCDF_sub (show x + 1 / x ≤ x by linarith) hx0.le
  have h0 := (normCDF_mem_Ioo (x + 1 / x)).1
  -- `φ(x + 1/x) ≥ e^{−3/2} φ(x)`
  have hφ : Real.exp (-(3 / 2)) * gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 (x + 1 / x) := by
    rw [gaussianPDFReal_std, gaussianPDFReal_std]
    have hC : 0 ≤ (√(2 * π))⁻¹ := by positivity
    have hexp : Real.exp (-(3 / 2)) * Real.exp (-x ^ 2 / 2) ≤
        Real.exp (-(x + 1 / x) ^ 2 / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have e : (x + 1 / x) ^ 2 = x ^ 2 + 2 + 1 / x ^ 2 := by
        field_simp
        ring
      have h1 : 1 / x ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hx2
      rw [e]
      linarith
    calc Real.exp (-(3 / 2)) * ((√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2))
        = (√(2 * π))⁻¹ * (Real.exp (-(3 / 2)) * Real.exp (-x ^ 2 / 2)) := by ring
      _ ≤ (√(2 * π))⁻¹ * Real.exp (-(x + 1 / x) ^ 2 / 2) := mul_le_mul_of_nonneg_left hexp hC
  have e2 : x - (x + 1 / x) = -(1 / x) := by ring
  rw [e2] at h
  have key : -(1 / x) * gaussianPDFReal 0 1 (x + 1 / x) ≤ normCDF x := by linarith
  have hm : -x * -(1 / x) = 1 := by field_simp
  calc Real.exp (-(3 / 2)) * gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 (x + 1 / x) := hφ
    _ = -x * (-(1 / x) * gaussianPDFReal 0 1 (x + 1 / x)) := by rw [← mul_assoc, hm, one_mul]
    _ ≤ -x * normCDF x := mul_le_mul_of_nonneg_left key (by linarith)

/-- **The upper Mills bound** `t (1 − Φ(t)) ≤ φ(t)` (of interest for `t > 0`): `T ↦ t Φ(T) + φ(T)`
decreases on `[t, ∞)` (its derivative is `(t − T) φ(T)`), and `Φ(T) → 1`. -/
lemma mul_one_sub_normCDF_le (t : ℝ) :
    t * (1 - normCDF t) ≤ gaussianPDFReal 0 1 t := by
  have hT : ∀ T, t < T → t * (normCDF T - normCDF t) ≤ gaussianPDFReal 0 1 t := by
    intro T hT
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope
      (fun y => t * normCDF y + gaussianPDFReal 0 1 y)
      (fun y => t * gaussianPDFReal 0 1 y + -y * gaussianPDFReal 0 1 y) hT
      ((continuous_const.mul continuous_normCDF).add continuous_gaussianPDFReal_std).continuousOn
      fun y _ => ((hasDerivAt_normCDF y).const_mul t).add (hasDerivAt_gaussianPDFReal_std y)
    have hcd' : t * gaussianPDFReal 0 1 c + -c * gaussianPDFReal 0 1 c =
        (t * normCDF T + gaussianPDFReal 0 1 T - (t * normCDF t + gaussianPDFReal 0 1 t)) /
          (T - t) := hcd
    have hφc := gaussianPDFReal_pos 0 1 c one_ne_zero
    have hneg : t * gaussianPDFReal 0 1 c + -c * gaussianPDFReal 0 1 c ≤ 0 := by
      nlinarith [mul_pos (sub_pos.2 hc.1) hφc]
    rw [hcd', div_le_iff₀ (sub_pos.2 hT), zero_mul] at hneg
    have hφT := gaussianPDFReal_nonneg 0 1 T
    linarith
  have hlim : Tendsto (fun T => t * (normCDF T - normCDF t)) atTop (𝓝 (t * (1 - normCDF t))) :=
    (tendsto_normCDF_atTop.sub_const _).const_mul t
  exact le_of_tendsto hlim ((eventually_gt_atTop t).mono hT)

/-- **The upper Mills-ratio bound in the left tail** (a standard estimate, not stated in the paper;
it is used here for Haas–Giles 2025, §3.4, p. 7, l. 378–379, H3-30: method 1 has its "MSE divided
by 2 each time `d` increases by 1. This was theoretically expected for method 1 (see [12])"):
`−x Φ(x) ≤ φ(x)` for every real `x` (of interest for `x < 0`; for `x ≥ 0` it is trivial), the
mirror image of `t (1 − Φ(t)) ≤ φ(t)` (`mul_one_sub_normCDF_le`). -/
theorem neg_mul_normCDF_le (x : ℝ) : -x * normCDF x ≤ gaussianPDFReal 0 1 x := by
  have h := mul_one_sub_normCDF_le (-x)
  have e : normCDF x = 1 - normCDF (-x) := by
    have h' := normCDF_neg (-x)
    rw [neg_neg] at h'
    exact h'
  rw [e, ← gaussianPDFReal_std_neg x]
  exact h

/-- `2^n ≤ e^n`. -/
lemma two_pow_le_exp_natCast (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  calc (2 : ℝ) ^ n ≤ Real.exp 1 ^ n := pow_le_pow_left₀ (by norm_num) h2 n
    _ = Real.exp n := by rw [← Real.exp_nat_mul, mul_one]

/-- `e^{n/2} ≤ 2^n` (as `e^{1/2} < 1/(1 − 1/2) = 2`). -/
lemma exp_natCast_half_le_two_pow (n : ℕ) : Real.exp (n / 2) ≤ (2 : ℝ) ^ n := by
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h.le
  calc Real.exp (n / 2) = Real.exp (1 / 2) ^ n := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le h2 n

/-- **The lower block bound** (for Haas–Giles 2025, §3.4, H3-30): if `m ≥ 1`, `x ≤ 0` and
`2^{−(m+1)} ≤ Φ(x) ≤ 2^{−m}`, then `(2^m φ(x))² ≤ 4 e⁴ m`. -/
lemma sq_two_pow_mul_gaussianPDFReal_le {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : x ≤ 0)
    (h1 : ((2 : ℝ) ^ (m + 1))⁻¹ ≤ normCDF x) (h2 : normCDF x ≤ ((2 : ℝ) ^ m)⁻¹) :
    ((2 : ℝ) ^ m * gaussianPDFReal 0 1 x) ^ 2 ≤ 4 * Real.exp 4 * m := by
  have hp0 : (0 : ℝ) < 2 ^ m := by positivity
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hξ := normCDF_mem_Ioo x
  have hφ := gaussianPDFReal_pos 0 1 x one_ne_zero
  have hpξ : 2 ^ m * normCDF x ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left h2 hp0.le
    rwa [mul_inv_cancel₀ hp0.ne'] at h
  have he4 : (1 : ℝ) ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
  rcases le_or_gt x (-1) with hx1 | hx1
  · -- `x ≤ −1`: `2^m φ(x) ≤ e^{3/2} |x|` and `x² ≤ 4m`
    have hA := exp_mul_gaussianPDFReal_le hx1
    have hB : 2 ^ m * gaussianPDFReal 0 1 x ≤ Real.exp (3 / 2) * -x := by
      have he : Real.exp (3 / 2) * Real.exp (-(3 / 2)) = 1 := by
        rw [← Real.exp_add]; norm_num
      have hφle : gaussianPDFReal 0 1 x ≤ Real.exp (3 / 2) * (-x * normCDF x) := by
        calc gaussianPDFReal 0 1 x
            = Real.exp (3 / 2) * (Real.exp (-(3 / 2)) * gaussianPDFReal 0 1 x) := by
              rw [← mul_assoc, he, one_mul]
          _ ≤ Real.exp (3 / 2) * (-x * normCDF x) :=
              mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
      have hpos : 0 ≤ Real.exp (3 / 2) * -x := mul_nonneg (Real.exp_pos _).le (by linarith)
      calc 2 ^ m * gaussianPDFReal 0 1 x ≤ 2 ^ m * (Real.exp (3 / 2) * (-x * normCDF x)) :=
            mul_le_mul_of_nonneg_left hφle hp0.le
        _ = Real.exp (3 / 2) * -x * (2 ^ m * normCDF x) := by ring
        _ ≤ Real.exp (3 / 2) * -x * 1 := mul_le_mul_of_nonneg_left hpξ hpos
        _ = Real.exp (3 / 2) * -x := mul_one _
    -- `x² ≤ 4m` from `2^{−(m+1)} ≤ Φ(x) ≤ φ(x)/|x| ≤ e^{−x²/2}`
    have hC := neg_mul_normCDF_le x
    have hφe : gaussianPDFReal 0 1 x ≤ Real.exp (-x ^ 2 / 2) := by
      rw [gaussianPDFReal_std]
      have hs : (1 : ℝ) ≤ √(2 * π) := by
        rw [Real.one_le_sqrt]
        nlinarith [two_le_pi]
      have hinv : (√(2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
      have := Real.exp_pos (-x ^ 2 / 2)
      nlinarith
    have hξe : ((2 : ℝ) ^ (m + 1))⁻¹ ≤ Real.exp (-x ^ 2 / 2) := by nlinarith
    have hx2 : x ^ 2 ≤ 4 * m := by
      have h3 : Real.exp (x ^ 2 / 2) ≤ 2 ^ (m + 1) := by
        have hq : (0 : ℝ) < 2 ^ (m + 1) := by positivity
        have h4 := mul_le_mul_of_nonneg_left hξe (Real.exp_pos (x ^ 2 / 2)).le
        rw [← Real.exp_add, show x ^ 2 / 2 + -x ^ 2 / 2 = 0 by ring, Real.exp_zero] at h4
        rwa [mul_inv_le_iff₀ hq, one_mul] at h4
      have h5 := h3.trans (two_pow_le_exp_natCast (m + 1))
      rw [Real.exp_le_exp] at h5
      push_cast at h5
      linarith
    have hB2 : (2 ^ m * gaussianPDFReal 0 1 x) ^ 2 ≤ (Real.exp (3 / 2) * -x) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hB 2
    have he3 : Real.exp (3 / 2) ^ 2 ≤ Real.exp 4 := by
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.2 (by norm_num)
    calc (2 ^ m * gaussianPDFReal 0 1 x) ^ 2 ≤ (Real.exp (3 / 2) * -x) ^ 2 := hB2
      _ = Real.exp (3 / 2) ^ 2 * x ^ 2 := by ring
      _ ≤ Real.exp 4 * (4 * m) := mul_le_mul he3 hx2 (sq_nonneg _) (by positivity)
      _ = 4 * Real.exp 4 * m := by ring
  · -- `−1 < x ≤ 0`: `φ(x) ≤ φ(0) = e² φ(2) ≤ e² φ(x − 1) ≤ e² Φ(x)`
    have h2' : gaussianPDFReal 0 1 2 ≤ normCDF x :=
      (gaussianPDFReal_std_le_of_sq_le (by nlinarith)).trans (gaussianPDFReal_sub_one_le_normCDF hx)
    have hφ2 : gaussianPDFReal 0 1 x ≤ Real.exp 2 * gaussianPDFReal 0 1 2 := by
      rw [gaussianPDFReal_std 2]
      have e : Real.exp 2 * ((√(2 * π))⁻¹ * Real.exp (-2 ^ 2 / 2)) = (√(2 * π))⁻¹ := by
        rw [mul_left_comm, ← Real.exp_add]
        norm_num
      rw [e]
      exact gaussianPDFReal_std_le x
    have hB : 2 ^ m * gaussianPDFReal 0 1 x ≤ Real.exp 2 := by
      calc 2 ^ m * gaussianPDFReal 0 1 x ≤ 2 ^ m * (Real.exp 2 * normCDF x) :=
            mul_le_mul_of_nonneg_left (hφ2.trans
              (mul_le_mul_of_nonneg_left h2' (Real.exp_pos _).le)) hp0.le
        _ = Real.exp 2 * (2 ^ m * normCDF x) := by ring
        _ ≤ Real.exp 2 * 1 := mul_le_mul_of_nonneg_left hpξ (Real.exp_pos _).le
        _ = Real.exp 2 := mul_one _
    have hB2 : (2 ^ m * gaussianPDFReal 0 1 x) ^ 2 ≤ Real.exp 2 ^ 2 :=
      pow_le_pow_left₀ (by positivity) hB 2
    have he : Real.exp 2 ^ 2 = Real.exp 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he] at hB2
    nlinarith

/-- **The upper block bound** (for Haas–Giles 2025, §3.4, H3-30): if `m ≥ 1`, `x ≤ 0` and
`2^{−(m+1)} ≤ Φ(x) ≤ 2^{−m}`, then `m ≤ 8 (4 + φ(1)⁻²) (2^m φ(x))²`. -/
lemma le_sq_two_pow_mul_gaussianPDFReal {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : x ≤ 0)
    (h1 : ((2 : ℝ) ^ (m + 1))⁻¹ ≤ normCDF x) (h2 : normCDF x ≤ ((2 : ℝ) ^ m)⁻¹) :
    (m : ℝ) ≤
      8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2) * ((2 : ℝ) ^ m * gaussianPDFReal 0 1 x) ^ 2 := by
  have hp0 : (0 : ℝ) < 2 ^ m := by positivity
  have hp2 : (2 : ℝ) ≤ 2 ^ m := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hξ := normCDF_mem_Ioo x
  have hφ := gaussianPDFReal_pos 0 1 x one_ne_zero
  have hφ1 := gaussianPDFReal_pos 0 1 1 one_ne_zero
  have hpξ : 2 ^ m * normCDF x ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left h2 hp0.le
    rwa [mul_inv_cancel₀ hp0.ne'] at h
  have h2pξ : 1 ≤ 2 * 2 ^ m * normCDF x := by
    have hq : (0 : ℝ) < 2 ^ (m + 1) := by positivity
    have h := mul_le_mul_of_nonneg_left h1 hq.le
    rw [mul_inv_cancel₀ hq.ne'] at h
    calc (1 : ℝ) ≤ 2 ^ (m + 1) * normCDF x := h
      _ = 2 * 2 ^ m * normCDF x := by ring
  -- `m ≤ 2x² + 6`, from `2^{−m} ≥ Φ(x) ≥ φ(x − 1) ≥ e^{−x²−1}/4`
  have hm6 : (m : ℝ) ≤ 2 * x ^ 2 + 6 := by
    have hlow : Real.exp (-x ^ 2 - 1) / 4 ≤ normCDF x := by
      refine le_trans ?_ (gaussianPDFReal_sub_one_le_normCDF hx)
      rw [gaussianPDFReal_std]
      have hs : √(2 * π) ≤ 4 := by
        rw [Real.sqrt_le_left (by norm_num)]
        nlinarith [pi_le_four]
      have hs0 : 0 < √(2 * π) := by positivity
      have hinv : 1 / 4 ≤ (√(2 * π))⁻¹ := by
        rw [one_div]
        exact inv_anti₀ hs0 hs
      have hexp : Real.exp (-x ^ 2 - 1) ≤ Real.exp (-(x - 1) ^ 2 / 2) :=
        Real.exp_le_exp.2 (by nlinarith [sq_nonneg (x + 1)])
      have := Real.exp_pos (-x ^ 2 - 1)
      nlinarith
    -- `2^m ≤ 4 e^{x²+1} ≤ e^{x²+3}`
    have hpe : (2 : ℝ) ^ m ≤ Real.exp (x ^ 2 + 3) := by
      have h4 : (4 : ℝ) ≤ Real.exp 2 := by
        have h := Real.add_one_le_exp 1
        have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      have hmul : 2 ^ m * Real.exp (-x ^ 2 - 1) ≤ 4 := by nlinarith
      have he : Real.exp (x ^ 2 + 3) = Real.exp 2 * Real.exp (x ^ 2 + 1) := by
        rw [← Real.exp_add]; ring_nf
      have he' : Real.exp (x ^ 2 + 1) * Real.exp (-x ^ 2 - 1) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have hpos := Real.exp_pos (x ^ 2 + 1)
      calc (2 : ℝ) ^ m = 2 ^ m * Real.exp (-x ^ 2 - 1) * Real.exp (x ^ 2 + 1) := by
            rw [mul_assoc, mul_comm (Real.exp (-x ^ 2 - 1)), he', mul_one]
        _ ≤ 4 * Real.exp (x ^ 2 + 1) := mul_le_mul_of_nonneg_right hmul hpos.le
        _ ≤ Real.exp 2 * Real.exp (x ^ 2 + 1) := mul_le_mul_of_nonneg_right h4 hpos.le
        _ = Real.exp (x ^ 2 + 3) := he.symm
    have h5 := (exp_natCast_half_le_two_pow m).trans hpe
    rw [Real.exp_le_exp] at h5
    linarith
  have hK : 0 ≤ (gaussianPDFReal 0 1 1)⁻¹ ^ 2 := sq_nonneg _
  rcases le_or_gt x (-1) with hx1 | hx1
  · -- `x ≤ −1`: `|x| Φ(x) ≤ φ(x)`, so `x² ≤ 4 (2^m φ(x))²`
    have hC := neg_mul_normCDF_le x
    have hx2 : 1 ≤ x ^ 2 := by nlinarith
    have hsq : x ^ 2 ≤ 4 * (2 ^ m * gaussianPDFReal 0 1 x) ^ 2 := by
      have h3 : -x ≤ -x * (2 * 2 ^ m * normCDF x) := le_mul_of_one_le_right (by linarith) h2pξ
      have h4 : -x * (2 * 2 ^ m * normCDF x) ≤ 2 * (2 ^ m * gaussianPDFReal 0 1 x) := by
        calc -x * (2 * 2 ^ m * normCDF x) = 2 * 2 ^ m * (-x * normCDF x) := by ring
          _ ≤ 2 * 2 ^ m * gaussianPDFReal 0 1 x :=
              mul_le_mul_of_nonneg_left hC (by positivity)
          _ = 2 * (2 ^ m * gaussianPDFReal 0 1 x) := by ring
      have h5 : -x ≤ 2 * (2 ^ m * gaussianPDFReal 0 1 x) := h3.trans h4
      have h6 := pow_le_pow_left₀ (by linarith) h5 2
      nlinarith
    nlinarith
  · -- `−1 < x ≤ 0`: `φ(x) ≥ φ(1)` and `2^m ≥ 1`
    have hφx : gaussianPDFReal 0 1 1 ≤ gaussianPDFReal 0 1 x :=
      gaussianPDFReal_std_le_of_sq_le (by nlinarith)
    have h3 : gaussianPDFReal 0 1 1 ≤ 2 ^ m * gaussianPDFReal 0 1 x := by nlinarith
    have h4 : gaussianPDFReal 0 1 1 ^ 2 ≤ (2 ^ m * gaussianPDFReal 0 1 x) ^ 2 :=
      pow_le_pow_left₀ hφ1.le h3 2
    have h5 : (gaussianPDFReal 0 1 1)⁻¹ ^ 2 * gaussianPDFReal 0 1 1 ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hφ1.ne', one_pow]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have h6 : 8 ≤
        8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2) * (2 ^ m * gaussianPDFReal 0 1 x) ^ 2 := by
      have h7 : (gaussianPDFReal 0 1 1)⁻¹ ^ 2 * gaussianPDFReal 0 1 1 ^ 2 ≤
          (gaussianPDFReal 0 1 1)⁻¹ ^ 2 * (2 ^ m * gaussianPDFReal 0 1 x) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 hK
      have h8 : 0 ≤ 4 * (2 ^ m * gaussianPDFReal 0 1 x) ^ 2 := by positivity
      nlinarith
    linarith

/-- **The block bounds for `Φ⁻¹`** (not stated in the paper; the hypotheses `hlo`, `hup` of
`method1MSE_order`, which give Haas–Giles 2025, §3.4, p. 7, l. 378–379, H3-30: "both method 1 and 2
have their MSE divided by 2 each time `d` increases by 1. This was theoretically expected for
method 1 (see [12])"): for `m ≥ 1` and `2^{−(m+1)} ≤ u ≤ v ≤ 2^{−m}`,
`c (2^m (v − u))² ≤ m (Φ⁻¹(v) − Φ⁻¹(u))² ≤ K (2^m (v − u))²` with `c = 1/(4e⁴)` and
`K = 8 (4 + φ(1)⁻²)`: by the mean value theorem `Φ⁻¹(v) − Φ⁻¹(u) = (v − u)/φ(x)` with
`Φ(x) ∈ [2^{−(m+1)}, 2^{−m}]`, and the Mills-ratio bounds (`exp_mul_gaussianPDFReal_le`,
`neg_mul_normCDF_le`) give `(2^m φ(x))² ≍ m`.  Numerically `m (2^{−m} (Φ⁻¹)'(u))²` ranges over
`(1/(2 ln 2), 3.18]` (`≈ 0.721` to `≈ 3.179`) on these blocks, so the constants are not sharp. -/
theorem normCDFInv_block_bounds {m : ℕ} (hm : 1 ≤ m) {u v : ℝ} (hu : ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u)
    (huv : u ≤ v) (hv : v ≤ ((2 : ℝ) ^ m)⁻¹) :
    (4 * Real.exp 4)⁻¹ * ((2 : ℝ) ^ m * (v - u)) ^ 2 ≤
        (m : ℝ) * (normCDFInv v - normCDFInv u) ^ 2 ∧
      (m : ℝ) * (normCDFInv v - normCDFInv u) ^ 2 ≤
        8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2) * ((2 : ℝ) ^ m * (v - u)) ^ 2 := by
  rcases huv.eq_or_lt with h | h
  · rw [h, sub_self, sub_self, mul_zero]
    norm_num
  have hpos : 0 < ((2 : ℝ) ^ (m + 1))⁻¹ := by positivity
  have hhalf : ((2 : ℝ) ^ m)⁻¹ ≤ 1 / 2 := (inv_two_pow_anti hm).trans (by norm_num)
  have hsub : Icc u v ⊆ Ioo (0 : ℝ) 1 := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope normCDFInv
    (fun y => (gaussianPDFReal 0 1 (normCDFInv y))⁻¹) h (continuousOn_normCDFInv.mono hsub)
    fun y hy => hasDerivAt_normCDFInv (hsub (Ioo_subset_Icc_self hy))
  have hξ01 : ξ ∈ Ioo (0 : ℝ) 1 := hsub (Ioo_subset_Icc_self hξ)
  have hΦx : normCDF (normCDFInv ξ) = ξ := normCDF_normCDFInv hξ01
  have hx0 : normCDFInv ξ ≤ 0 := by
    rw [normCDFInv_le_iff hξ01, normCDF_zero]
    linarith [hξ.2]
  have h1 : ((2 : ℝ) ^ (m + 1))⁻¹ ≤ normCDF (normCDFInv ξ) := by rw [hΦx]; linarith [hξ.1]
  have h2 : normCDF (normCDFInv ξ) ≤ ((2 : ℝ) ^ m)⁻¹ := by rw [hΦx]; linarith [hξ.2]
  have hφ := gaussianPDFReal_pos 0 1 (normCDFInv ξ) one_ne_zero
  have hdiff : normCDFInv v - normCDFInv u = (v - u) / gaussianPDFReal 0 1 (normCDFInv ξ) := by
    have hξd' : (gaussianPDFReal 0 1 (normCDFInv ξ))⁻¹ =
        (normCDFInv v - normCDFInv u) / (v - u) := hξd
    rw [eq_div_iff (sub_pos.2 h).ne'] at hξd'
    rw [← hξd', inv_mul_eq_div]
  have hL := sq_two_pow_mul_gaussianPDFReal_le hm hx0 h1 h2
  have hU := le_sq_two_pow_mul_gaussianPDFReal hm hx0 h1 h2
  have hsplit : ((2 : ℝ) ^ m * (v - u)) ^ 2 =
      ((2 : ℝ) ^ m * gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2 *
        ((v - u) / gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2 := by
    field_simp
  rw [hdiff, hsplit]
  constructor
  · have hL' : (4 * Real.exp 4)⁻¹ * ((2 : ℝ) ^ m * gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2 ≤ m := by
      rw [inv_mul_le_iff₀ (by positivity)]
      exact hL
    calc (4 * Real.exp 4)⁻¹ * (((2 : ℝ) ^ m * gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2 *
          ((v - u) / gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2)
        = ((4 * Real.exp 4)⁻¹ * ((2 : ℝ) ^ m * gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2) *
          ((v - u) / gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2 := by ring
      _ ≤ m * ((v - u) / gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hL' (sq_nonneg _)
  · calc (m : ℝ) * ((v - u) / gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2
        ≤ (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2) *
          ((2 : ℝ) ^ m * gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2) *
          ((v - u) / gaussianPDFReal 0 1 (normCDFInv ξ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hU (sq_nonneg _)
      _ = _ := by ring

/-- **The method-1 MSE of `Φ⁻¹` is of order `2^{−d}/d`** (Haas–Giles 2025, §3.4, p. 7, l. 378–379,
H3-30: "both method 1 and 2 have their MSE divided by 2 each time `d` increases by 1. This was
theoretically expected for method 1"). There are `c, K > 0` such that for every `d ≥ 2`,
`c 2^{−d}/d ≤ ∑_{j<2^d} ∫_{I_j} (Z_j − Φ⁻¹)² ≤ K 2^{−d}/d` (with `c = 1/(256 e⁴)` and
`K = 48 (4 + φ(1)⁻²)`): `method1MSE_order` with `f = Φ⁻¹`, whose block hypotheses are proved by
Mills-ratio estimates (`normCDFInv_block_bounds`). Deviation: only the order is proved, so the exact
halving `MSE(d + 1)/MSE(d) → 1/2` is not (see `tendsto_log_method1MSE_normCDFInv` for the halving on
average). -/
theorem method1MSE_order_normCDFInv : ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ d : ℕ, 2 ≤ d →
    c * ((2 ^ d)⁻¹ / d) ≤ method1MSE normCDFInv d ∧
      method1MSE normCDFInv d ≤ K * ((2 ^ d)⁻¹ / d) := by
  obtain ⟨-, hb⟩ := method1MSE_order intervalIntegrable_normCDFInv.1
    intervalIntegrable_normCDFInv.2 normCDFInv_one_sub_forall (c := (4 * Real.exp 4)⁻¹)
    (K := 8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2)) (by positivity)
    (fun _ hm _ _ hu huv hv => (normCDFInv_block_bounds hm hu huv hv).1)
    (fun _ hm _ _ hu huv hv => (normCDFInv_block_bounds hm hu huv hv).2)
  exact ⟨(4 * Real.exp 4)⁻¹ / 64, 6 * (8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2)), by positivity,
    by positivity, hb⟩

/-- **The method-1 MSE of `Φ⁻¹` halves per bit on average** (Haas–Giles 2025, §3.4, p. 7, l.
378–379, H3-30: method 1 has its "MSE divided by 2 each time `d` increases by 1"):
`log(MSE(d))/d → −log 2`, i.e. `MSE(d)^{1/d} → 1/2`. `tendsto_log_method1MSE_div` with `f = Φ⁻¹`. -/
theorem tendsto_log_method1MSE_normCDFInv :
    Tendsto (fun d : ℕ => Real.log (method1MSE normCDFInv d) / d) atTop (𝓝 (-Real.log 2)) :=
  tendsto_log_method1MSE_div intervalIntegrable_normCDFInv.1 intervalIntegrable_normCDFInv.2
    normCDFInv_one_sub_forall (c := (4 * Real.exp 4)⁻¹)
    (K := 8 * (4 + (gaussianPDFReal 0 1 1)⁻¹ ^ 2)) (by positivity)
    (fun _ hm _ _ hu huv hv => (normCDFInv_block_bounds hm hu huv hv).1)
    (fun _ hm _ _ hu huv hv => (normCDFInv_block_bounds hm hu huv hv).2)

end Mills

end MLMC
