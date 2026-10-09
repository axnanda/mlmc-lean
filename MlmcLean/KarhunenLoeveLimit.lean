import MlmcLean.KarhunenLoeve
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The untruncated Karhunen–Loève field and diffusivity (Giles 2015, §7.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §7.2 "Elliptic
SPDE", pp. 51–53 (`docs/giles2015.txt`, l. 2213–2279; the line numbers below refer to it).  Rows
G7.2-02 (the log-normal diffusivity, l. 2219–2220, 2254–2255), G7.2-03 (the Karhunen–Loève
expansion, l. 2255–2262), and in part G7.2-05 (the truncation, l. 2266–2268) and G7.2-07 ("the
diffusivity is unbounded", l. 2274–2275).

**Setting.**  As in `MlmcLean.KarhunenLoeve`: the `ξ_n = z n` are the coordinates under
`stdNormalSeq = N(0, 1)^{⊗ℕ}` (independent unit normal variables), `θ_n ≥ 0`, and
`klField θ f K z x = ∑_{n<K} √θ_n z_n f_n(x)` is the truncated field `Y_K`, `κ_K = exp Y_K`.  The
paper models `log κ` as "a Gaussian field with a uniform mean (which we will take to be zero for
simplicity) and a covariance function of the general form `R(x, y) = r(x − y)`" (l. 2220,
2254–2255) and writes it as the full series "`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`"
(l. 2257–2259).  Here that series is `klLimit θ f z x`, the limit of the partial sums `Y_K(z, x)` as
`K → ∞`, and `klLimitDiffusivity θ f z x = exp (klLimit θ f z x)` is the untruncated diffusivity
`κ`.  The covariance enters only through its Mercer expansion `R(x, y) = ∑ θ_n f_n(x) f_n(y)`
(`HasSum` hypotheses at the points used).

**What is proved.**
* `klLimit_tendsto`: if `∑ θ_n f_n(x)² < ∞`, the series converges almost surely (an
  `L¹`-bounded martingale, `kl_ae_exists_tendsto_sum_mul_eval`), its sum `Y(x)` is in `L²`, and
  `E[(Y(x) − Y_K(x))²] = ∑_{n≥K} θ_n f_n(x)² → 0`.
* `map_klLimit_eq_gaussianReal`: `Y(x) ∼ N(0, R(x, x))` (the characteristic functions of the
  Gaussian partial sums converge to those of `Y(x)` and of `N(0, R(x, x))`).
* `integral_klLimit_mul`: `E[Y(x) Y(y)] = R(x, y)`.
* `map_sum_klLimit_eq_gaussianReal`, `isGaussian_map_klLimit`: every linear combination
  `∑ a_i Y(x_i)` is `N(0, ∑ a_i a_j R(x_i, x_j))`, so `(Y(x_1), …, Y(x_m))` is jointly Gaussian.
* `klLimitDiffusivity_moment`: for every real `p`, `κ(x)^p` is integrable and
  `E[κ(x)^p] = exp(p² R(x, x)/2)`.
* `tendsto_integral_abs_klDiffusivity_rpow_sub`: `κ_K(x)^p → κ(x)^p` in `L¹`, and the moments
  converge.
* `klLimitDiffusivity_unbounded`: if `R(x, x) > 0`, neither `κ(x)` nor `1/κ(x)` is essentially
  bounded ("the diffusivity is unbounded", l. 2275).
* `klLimit_ae_eq_L2_limit`: under the hypotheses of `exists_klField_limit`,
  `∑ θ_n f_n(x)² < ∞` for `ν`-a.e. `x` and the series converges `(P ⊗ ν)`-a.e.; `klLimit` is in
  `L²(P ⊗ ν)` with `E ∫ (Y − Y_K)² dν = ∑_{n≥K} θ_n`, and every `L²(P ⊗ ν)` limit of the `Y_K`
  (in particular the field of `exists_klField_limit`) equals it `(P ⊗ ν)`-a.e.

**Deviations.**  Mercer's theorem stays a hypothesis (the `HasSum` expansions of `R` and the
orthonormality of the `f_n`); the paper's stationary covariance `r(x − y)` is the special case
`R(x, y) = r(x − y)` of a general `R`.  The ordering `θ_0 ≥ θ_1 ≥ …` is not used.  `klLimit` is
defined as the limit (`limUnder`) of the partial sums; where they diverge its value is unspecified,
which happens only on a null set (`klLimit_tendsto`), so every statement about it is an almost sure
or distributional one.  The pointwise theorems use only the `HasSum` (or summability) hypotheses
at the points involved: no orthonormality, no `∑ θ_n < ∞` and no eigen-relation; `HasSum` forces
`R(x, x) ≥ 0`, so the `toNNReal` in the Gaussian laws never clips.

**Not proved here.**  The identification of the joint law with
`multivariateGaussian 0 (R(x_i, x_j))_{ij}` (here joint Gaussianity and the covariance are proved
separately) is in `MlmcLean.LimitLawExtras` (`map_klLimit_eq_multivariateGaussian`, with the
positive semidefinite covariance matrix `posSemidef_klCov`).  Not proved: Mercer's theorem
itself; regularity of `x ↦ κ(x)` and the moments of `max_x κ` and `1/min_x κ` used in the
analysis of the elliptic PDE (Charrier, Scheichl & Teckentrup, l. 2275–2279); the PDE itself.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal ENNReal

namespace MLMC

/-! ### Gaussian series `∑ c_n ξ_n` -/

/-- `E[(∑_{n∈s} a_n ξ_n)(∑_{n∈s} b_n ξ_n)] = ∑_{n∈s} a_n b_n` for independent unit normal `ξ_n`
(Giles 2015, §7.2, p. 53, l. 2261–2262: "`ξ_n` are independent unit Normal random variables"). -/
lemma kl_integral_sum_mul_eval_mul_sum (s : Finset ℕ) (a b : ℕ → ℝ) :
    Integrable (fun z : ℕ → ℝ => (∑ n ∈ s, a n * z n) * (∑ n ∈ s, b n * z n)) stdNormalSeq ∧
      ∫ z, (∑ n ∈ s, a n * z n) * (∑ n ∈ s, b n * z n) ∂stdNormalSeq = ∑ n ∈ s, a n * b n := by
  have hexp : ∀ z : ℕ → ℝ, (∑ n ∈ s, a n * z n) * (∑ n ∈ s, b n * z n) =
      ∑ n ∈ s, ∑ m ∈ s, (a n * b m) * (z n * z m) := by
    intro z
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
  simp_rw [hexp]
  have hint : ∀ n m, Integrable (fun z : ℕ → ℝ => (a n * b m) * (z n * z m)) stdNormalSeq :=
    fun n m => (integral_mul_eval_stdNormalSeq n m).1.const_mul _
  refine ⟨integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m, ?_⟩
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_finsetSum _ fun m _ => hint n m]
  simp_rw [integral_const_mul, (integral_mul_eval_stdNormalSeq n _).2, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq s n, if_pos hn]

/-- A finite sum `∑_{n∈s} a_n ξ_n` is in `L²` (Giles 2015, §7.2, p. 53, l. 2257–2262). -/
lemma kl_memLp_sum_mul_eval (s : Finset ℕ) (a : ℕ → ℝ) :
    MemLp (fun z : ℕ → ℝ => ∑ n ∈ s, a n * z n) 2 stdNormalSeq :=
  memLp_finsetSum s fun n _ => (memLp_eval_stdNormalSeq n (p := 2) (by simp)).const_mul (a n)

/-- `(E|g|)² ≤ E[g²]` on `N(0, 1)^{⊗ℕ}` (used for Giles 2015, §7.2, p. 53, l. 2257–2262). -/
lemma kl_sq_integral_abs_le {g : (ℕ → ℝ) → ℝ} (hg : MemLp g 2 stdNormalSeq) :
    (∫ z, |g z| ∂stdNormalSeq) ^ 2 ≤ ∫ z, g z ^ 2 ∂stdNormalSeq := by
  have hg' : MemLp (fun z => |g z|) 2 stdNormalSeq := hg.abs
  have h := variance_nonneg (fun z => |g z|) stdNormalSeq
  rw [variance_eq_sub hg'] at h
  simp only [Pi.pow_apply, sq_abs] at h
  linarith

/-- `E|g| ≤ (E[g²])^{1/2}` on `N(0, 1)^{⊗ℕ}` (used for Giles 2015, §7.2, p. 53,
l. 2257–2262). -/
lemma kl_integral_abs_le_sqrt {g : (ℕ → ℝ) → ℝ} (hg : MemLp g 2 stdNormalSeq) :
    ∫ z, |g z| ∂stdNormalSeq ≤ Real.sqrt (∫ z, g z ^ 2 ∂stdNormalSeq) :=
  Real.le_sqrt_of_sq_le (kl_sq_integral_abs_le hg)

/-- **Almost sure convergence of a Gaussian series** (for Giles 2015, §7.2, p. 53, l. 2257–2262:
"`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)` … `ξ_n` are independent unit Normal random
variables").  If `∑ c_n² < ∞`, the partial sums `∑_{n<K} c_n ξ_n` converge almost surely: shifted
by one they form a martingale for the natural filtration of the `ξ_n`, bounded in `L¹` by
`(∑ c_n²)^{1/2}`, so the martingale convergence theorem applies. -/
lemma kl_ae_exists_tendsto_sum_mul_eval {c : ℕ → ℝ} (hc : Summable fun n => c n ^ 2) :
    ∀ᵐ z ∂stdNormalSeq, ∃ a, Tendsto (fun K => ∑ n ∈ range K, c n * z n) atTop (𝓝 a) := by
  have hum : ∀ j, StronglyMeasurable (fun z : ℕ → ℝ => z j) :=
    fun j => (measurable_pi_apply j).stronglyMeasurable
  set ℱ := Filtration.natural (fun j (z : ℕ → ℝ) => z j) hum
  set M : ℕ → (ℕ → ℝ) → ℝ := fun K z => ∑ n ∈ range (K + 1), c n * z n with hM
  have hadp : StronglyAdapted ℱ M := by
    intro K
    have h : ∀ n ∈ range (K + 1), StronglyMeasurable[ℱ K] (fun z : ℕ → ℝ => c n * z n) := by
      intro n hn
      have h1 : StronglyMeasurable[ℱ n] (fun z : ℕ → ℝ => z n) :=
        Filtration.stronglyAdapted_natural hum n
      have h2 : StronglyMeasurable[ℱ K] (fun z : ℕ → ℝ => z n) :=
        h1.mono (ℱ.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)))
      exact h2.const_mul (c n)
    exact Finset.stronglyMeasurable_fun_sum _ h
  have hint : ∀ K, Integrable (M K) stdNormalSeq := fun K =>
    (kl_memLp_sum_mul_eval (range (K + 1)) c).integrable (by norm_num)
  have hiIndep : iIndep (fun j => MeasurableSpace.comap (fun z : ℕ → ℝ => z j) inferInstance)
      stdNormalSeq :=
    (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
      (X := fun _ (y : ℝ) => y) fun _ => measurable_id)
  have hindep : ∀ K, Indep (ℱ K)
      (MeasurableSpace.comap (fun z : ℕ → ℝ => z (K + 1)) inferInstance) stdNormalSeq := by
    intro K
    have h := indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le) hiIndep
      (S := Set.Iic K) (T := {K + 1}) (by simp)
    rw [_root_.iSup_singleton] at h
    exact h
  have hmart : Martingale M ℱ stdNormalSeq := by
    refine martingale_of_setIntegral_eq_succ hadp hint fun K s hs => ?_
    have hsplit : M (K + 1) = fun z => M K z + c (K + 1) * z (K + 1) := by
      funext z
      simp only [hM]
      rw [Finset.sum_range_succ]
    have hg : Integrable (fun z : ℕ → ℝ => c (K + 1) * z (K + 1)) stdNormalSeq :=
      ((memLp_eval_stdNormalSeq (K + 1) (p := 1) (by simp)).integrable le_rfl).const_mul _
    rw [hsplit, integral_add (hint K).integrableOn hg.integrableOn]
    have hs' : MeasurableSet s := ℱ.le K s hs
    have h0 : ∫ z in s, c (K + 1) * z (K + 1) ∂stdNormalSeq = 0 := by
      rw [← integral_indicator hs']
      have hind : IndepFun (s.indicator fun _ => (1 : ℝ))
          (fun z : ℕ → ℝ => c (K + 1) * z (K + 1)) stdNormalSeq := by
        rw [IndepFun_iff_Indep]
        refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (hindep K) ?_) ?_
        · exact (Measurable.indicator measurable_const hs).comap_le
        · exact ((comap_measurable (fun z : ℕ → ℝ => z (K + 1))).const_mul _).comap_le
      have hfun : s.indicator (fun z : ℕ → ℝ => c (K + 1) * z (K + 1)) =
          (s.indicator fun _ => (1 : ℝ)) * fun z => c (K + 1) * z (K + 1) := by
        funext z
        by_cases hz : z ∈ s <;> simp [hz]
      rw [hfun, hind.integral_mul_eq_mul_integral
        ((measurable_const.indicator hs').aestronglyMeasurable) hg.aestronglyMeasurable,
        integral_const_mul]
      have hmean : ∫ z, z (K + 1) ∂stdNormalSeq = 0 := by
        rw [integral_comp_eval_stdNormalSeq (K + 1) (g := fun y => y)
          measurable_id.stronglyMeasurable]
        exact integral_id_gaussianReal
      rw [hmean, mul_zero, mul_zero]
    rw [h0, add_zero]
  have hbdd : ∀ K, eLpNorm (M K) 1 stdNormalSeq ≤ ENNReal.ofReal (Real.sqrt (∑' n, c n ^ 2)) := by
    intro K
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hint K)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := kl_sq_integral_abs_le (kl_memLp_sum_mul_eval (range (K + 1)) c)
    have h2 := (kl_integral_sum_mul_eval_mul_sum (range (K + 1)) c c).2
    simp only [← sq] at h2
    rw [h2] at h1
    have h3 : ∑ n ∈ range (K + 1), c n ^ 2 ≤ ∑' n, c n ^ 2 :=
      hc.sum_le_tsum _ fun n _ => sq_nonneg _
    simp only [Real.norm_eq_abs]
    exact Real.le_sqrt_of_sq_le (h1.trans h3)
  filter_upwards [hmart.submartingale.ae_tendsto_limitProcess hbdd] with z hz
  exact ⟨_, (tendsto_add_atTop_iff_nat 1).1 hz⟩

/-- **The almost sure sum of a Gaussian series is its `L²` sum** (for Giles 2015, §7.2, p. 53,
l. 2257–2262).  If `∑ c_n² < ∞` and the partial sums converge almost surely to `Y`, then `Y ∈ L²`
and `E[(Y − ∑_{n<K} c_n ξ_n)²] = ∑_{n≥K} c_n²`. -/
lemma kl_memLp_integral_sq_sub_of_ae_tendsto {c : ℕ → ℝ} (hc : Summable fun n => c n ^ 2)
    {Y : (ℕ → ℝ) → ℝ}
    (hY : ∀ᵐ z ∂stdNormalSeq, Tendsto (fun K => ∑ n ∈ range K, c n * z n) atTop (𝓝 (Y z))) :
    MemLp Y 2 stdNormalSeq ∧ ∀ K, ∫ z, (Y z - ∑ n ∈ range K, c n * z n) ^ 2 ∂stdNormalSeq =
      ∑' n, c (n + K) ^ 2 := by
  set S : ℕ → (ℕ → ℝ) → ℝ := fun K z => ∑ n ∈ range K, c n * z n with hS
  have hSm : ∀ K, MemLp (S K) 2 stdNormalSeq := fun K => kl_memLp_sum_mul_eval (range K) c
  set F : ℕ → Lp ℝ 2 stdNormalSeq := fun K => (hSm K).toLp _ with hF
  have hnorm : ∀ K M, K ≤ M → ‖F M - F K‖ ^ 2 = ∑ n ∈ Ico K M, c n ^ 2 := by
    intro K M hKM
    rw [hF, ← MemLp.toLp_sub, klNorm_toLp_sq]
    have hsub : ∀ z, (S M - S K) z = ∑ n ∈ Ico K M, c n * z n := by
      intro z
      simp only [Pi.sub_apply, hS]
      rw [Finset.sum_Ico_eq_sub _ hKM]
    have h := (kl_integral_sum_mul_eval_mul_sum (Ico K M) c c).2
    simp only [← sq] at h
    simp only [hsub]
    exact h
  have htail : ∀ K, Summable fun n => c (n + K) ^ 2 := fun K =>
    (summable_nat_add_iff K).2 hc
  have hle : ∀ K M, K ≤ M → ‖F M - F K‖ ^ 2 ≤ ∑' n, c (n + K) ^ 2 := by
    intro K M hKM
    rw [hnorm K M hKM, kl_sum_Ico_eq_sum_range_add (fun n => c n ^ 2)]
    exact (htail K).sum_le_tsum _ fun n _ => sq_nonneg _
  have hcauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (tendsto_order.1 (tendsto_sum_nat_add fun n => c n ^ 2)).2 (ε ^ 2)
      (by positivity) |>.exists_forall_of_atTop
    refine ⟨N, fun M hM => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le ((hle N M hM).trans_lt (hN N le_rfl))
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hmeas : TendstoInMeasure stdNormalSeq S atTop G := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun K => (hSm K).aestronglyMeasurable) (Lp.aestronglyMeasurable G) ?_
    refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' F G).1 hG).congr fun K => eLpNorm_congr_ae ?_
    filter_upwards [(hSm K).coeFn_toLp] with z hz
    simp only [Pi.sub_apply, hF, hz]
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hYG : Y =ᵐ[stdNormalSeq] G := by
    filter_upwards [hY, hae] with z h1 h2
    exact tendsto_nhds_unique (h1.comp hns.tendsto_atTop) h2
  refine ⟨(Lp.memLp G).ae_eq hYG.symm, fun K => ?_⟩
  have h1 : Tendsto (fun M => ‖F M - F K‖ ^ 2) atTop (𝓝 (‖G - F K‖ ^ 2)) :=
    ((hG.sub_const (F K)).norm).pow 2
  have h2 : Tendsto (fun M => ‖F M - F K‖ ^ 2) atTop (𝓝 (∑' n, c (n + K) ^ 2)) := by
    have h3 : Tendsto (fun M => ∑ n ∈ range (M - K), c (n + K) ^ 2) atTop
        (𝓝 (∑' n, c (n + K) ^ 2)) :=
      (htail K).hasSum.tendsto_sum_nat.comp (tendsto_sub_atTop_nat K)
    refine h3.congr' ((eventually_ge_atTop K).mono fun M hM => ?_)
    change _ = ‖F M - F K‖ ^ 2
    rw [hnorm K M hM, kl_sum_Ico_eq_sum_range_add (fun n => c n ^ 2)]
  rw [← tendsto_nhds_unique h1 h2]
  have hGK : G - F K = ((Lp.memLp G).sub (hSm K)).toLp _ := by
    rw [MemLp.toLp_sub (Lp.memLp G) (hSm K), Lp.toLp_coeFn]
  rw [hGK, klNorm_toLp_sq]
  refine integral_congr_ae ?_
  filter_upwards [hYG] with z hz
  simp only [Pi.sub_apply, hz, hS]

/-! ### The untruncated field -/

variable {D : Type*}

/-- **The untruncated Karhunen–Loève field** `Y(z, x) = ∑_{n≥0} √θ_n z_n f_n(x)`, defined as the
limit of the partial sums `∑_{n<K} √θ_n z_n f_n(x)` as `K → ∞` (Giles 2015, §7.2, p. 53,
l. 2257–2262: "`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`", with `ξ_n = z n`).  Where the partial
sums diverge the value is unspecified; this happens only on a null set when
`∑ θ_n f_n(x)² < ∞`. -/
noncomputable def klLimit (θ : ℕ → ℝ) (f : ℕ → D → ℝ) (z : ℕ → ℝ) (x : D) : ℝ :=
  limUnder atTop fun K => klField θ f K z x

/-- **The untruncated diffusivity** `κ = exp Y` (Giles 2015, §7.2, pp. 51–53, l. 2219–2220:
"`κ` is often modelled as a lognormal random field, i.e. `log κ` is a Gaussian field", with
`log κ` the full Karhunen–Loève series of l. 2257–2259). -/
noncomputable def klLimitDiffusivity (θ : ℕ → ℝ) (f : ℕ → D → ℝ) (z : ℕ → ℝ) (x : D) : ℝ :=
  Real.exp (klLimit θ f z x)

/-- The truncated field as a Gaussian series `∑_{n<K} c_n ξ_n` with `c_n = √θ_n f_n(x)`
(Giles 2015, §7.2, p. 53, l. 2257–2262). -/
lemma klField_eq_sum_mul (θ : ℕ → ℝ) (f : ℕ → D → ℝ) (K : ℕ) (z : ℕ → ℝ) (x : D) :
    klField θ f K z x = ∑ n ∈ range K, (Real.sqrt (θ n) * f n x) * z n := by
  rw [klField]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- `c_n² = θ_n f_n(x)²` for `c_n = √θ_n f_n(x)` (Giles 2015, §7.2, p. 53, l. 2257–2262). -/
lemma kl_coeff_sq {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) (f : ℕ → D → ℝ) (x : D) (n : ℕ) :
    (Real.sqrt (θ n) * f n x) ^ 2 = θ n * f n x ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (hθ n)]

/-- The truncated field at a point is in `L²` (Giles 2015, §7.2, p. 53, l. 2266–2267). -/
lemma memLp_klField_apply (θ : ℕ → ℝ) (f : ℕ → D → ℝ) (K : ℕ) (x : D) :
    MemLp (fun z => klField θ f K z x) 2 stdNormalSeq := by
  simp only [klField_eq_sum_mul]
  exact kl_memLp_sum_mul_eval _ _

/-- **The Karhunen–Loève series converges almost surely and in `L²` at each point** (Giles 2015,
§7.2, p. 53, l. 2257–2262: "`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`, where `θ_n` are the
eigenvalues of `R(x, y)` …, `f_n` are the corresponding eigenfunctions, and `ξ_n` are independent
unit Normal random variables", and l. 2266–2267: "the expansion is truncated after `K_ℓ` terms").
For `θ_n ≥ 0` and a point `x` with `∑ θ_n f_n(x)² < ∞` (under Mercer's expansion this sum is
`R(x, x)`), the partial sums `Y_K(x)` converge almost surely to `Y(x) = klLimit θ f · x`, which is
square integrable, and the truncation error is the tail of the series:
`E[(Y(x) − Y_K(x))²] = ∑_{n≥K} θ_n f_n(x)²` (written `∑' n, θ (n + K) * f (n + K) x ^ 2`), which
tends to `0` as `K → ∞`. -/
theorem klLimit_tendsto {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) {f : ℕ → D → ℝ} {x : D}
    (hx : Summable fun n => θ n * f n x ^ 2) :
    (∀ᵐ z ∂stdNormalSeq, Tendsto (fun K => klField θ f K z x) atTop (𝓝 (klLimit θ f z x))) ∧
      MemLp (fun z => klLimit θ f z x) 2 stdNormalSeq ∧
      (∀ K, Integrable (fun z => (klLimit θ f z x - klField θ f K z x) ^ 2) stdNormalSeq ∧
        ∫ z, (klLimit θ f z x - klField θ f K z x) ^ 2 ∂stdNormalSeq =
          ∑' n, θ (n + K) * f (n + K) x ^ 2) ∧
      Tendsto (fun K => ∫ z, (klLimit θ f z x - klField θ f K z x) ^ 2 ∂stdNormalSeq) atTop
        (𝓝 0) := by
  set c : ℕ → ℝ := fun n => Real.sqrt (θ n) * f n x with hc
  have hcs : Summable fun n => c n ^ 2 := by
    simp only [hc, kl_coeff_sq hθ]
    exact hx
  have hae : ∀ᵐ z ∂stdNormalSeq,
      Tendsto (fun K => klField θ f K z x) atTop (𝓝 (klLimit θ f z x)) := by
    filter_upwards [kl_ae_exists_tendsto_sum_mul_eval hcs] with z hz
    have hfun : (fun K => klField θ f K z x) = fun K => ∑ n ∈ range K, c n * z n :=
      funext fun K => klField_eq_sum_mul θ f K z x
    rw [klLimit, hfun]
    exact tendsto_nhds_limUnder hz
  have hae' : ∀ᵐ z ∂stdNormalSeq, Tendsto (fun K => ∑ n ∈ range K, c n * z n) atTop
      (𝓝 (klLimit θ f z x)) := by
    filter_upwards [hae] with z hz
    simpa only [klField_eq_sum_mul] using hz
  obtain ⟨hmem, hint⟩ := kl_memLp_integral_sq_sub_of_ae_tendsto hcs hae'
  have hK : ∀ K, ∫ z, (klLimit θ f z x - klField θ f K z x) ^ 2 ∂stdNormalSeq =
      ∑' n, θ (n + K) * f (n + K) x ^ 2 := by
    intro K
    simp only [klField_eq_sum_mul]
    rw [hint K]
    exact tsum_congr fun n => kl_coeff_sq hθ f x (n + K)
  refine ⟨hae, hmem, fun K => ⟨?_, hK K⟩, ?_⟩
  · exact (hmem.sub (memLp_klField_apply θ f K x)).integrable_sq
  · simp_rw [hK]
    exact tendsto_sum_nat_add fun n => θ n * f n x ^ 2

/-- `|e^{ita} − e^{itb}| ≤ |t| |a − b|` (used for Giles 2015, §7.2, p. 53, l. 2257–2262). -/
lemma kl_norm_cexp_sub_le (t a b : ℝ) :
    ‖Complex.exp (t * a * Complex.I) - Complex.exp (t * b * Complex.I)‖ ≤ |t| * |a - b| := by
  have h : Complex.exp (t * a * Complex.I) - Complex.exp (t * b * Complex.I) =
      Complex.exp ((t * b : ℝ) * Complex.I) *
        (Complex.exp (Complex.I * (t * (a - b) : ℝ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc _ ≤ ‖t * (a - b)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |t| * |a - b| := by rw [Real.norm_eq_abs, abs_mul]

/-- Characteristic functions of laws of close random variables are close:
`|φ_X(t) − φ_Y(t)| ≤ |t| E|X − Y|` (used for Giles 2015, §7.2, p. 53, l. 2257–2262). -/
lemma kl_norm_charFun_map_sub_le {X Y : (ℕ → ℝ) → ℝ} (hX : AEMeasurable X stdNormalSeq)
    (hY : AEMeasurable Y stdNormalSeq) (hXY : Integrable (fun z => X z - Y z) stdNormalSeq)
    (t : ℝ) :
    ‖charFun (stdNormalSeq.map X) t - charFun (stdNormalSeq.map Y) t‖ ≤
      |t| * ∫ z, |X z - Y z| ∂stdNormalSeq := by
  have hc : Continuous fun y : ℝ => Complex.exp (t * y * Complex.I) := by fun_prop
  rw [charFun_apply_real, charFun_apply_real, integral_map hX hc.aestronglyMeasurable,
    integral_map hY hc.aestronglyMeasurable]
  have hb : ∀ W : (ℕ → ℝ) → ℝ, AEMeasurable W stdNormalSeq →
      Integrable (fun z => Complex.exp (t * W z * Complex.I)) stdNormalSeq := by
    intro W hW
    refine (integrable_const (1 : ℝ)).mono'
      (hc.measurable.comp_aemeasurable hW).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    have : (t : ℂ) * (W z : ℂ) * Complex.I = ((t * W z : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [← integral_sub (hb X hX) (hb Y hY), ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hXY.abs.const_mul _)
    (ae_of_all _ fun z => kl_norm_cexp_sub_le t (X z) (Y z))

/-- **The untruncated field is Gaussian with variance `R(x, x)`** (Giles 2015, §7.2, pp. 51–53,
l. 2220, 2254–2255: "`log κ` is a Gaussian field with a uniform mean (which we will take to be
zero for simplicity) and a covariance function of the general form `R(x, y)`", and l. 2257–2259:
"`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`").  For `θ_n ≥ 0` and a point `x` where Mercer's
expansion `R(x, x) = ∑ θ_n f_n(x)²` holds, the law of `Y(x) = klLimit θ f · x` is
`N(0, R(x, x))`. -/
theorem map_klLimit_eq_gaussianReal {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) {f : ℕ → D → ℝ}
    {R : D → D → ℝ} {x : D} (hR : HasSum (fun n => θ n * f n x * f n x) (R x x)) :
    stdNormalSeq.map (fun z => klLimit θ f z x) = gaussianReal 0 (R x x).toNNReal := by
  have hR' : HasSum (fun n => θ n * f n x ^ 2) (R x x) := by
    refine hR.congr_fun fun n => ?_
    ring
  obtain ⟨-, hmem, hK, hlim⟩ := klLimit_tendsto hθ hR'.summable
  have hR0 : 0 ≤ R x x := hR'.nonneg fun n => mul_nonneg (hθ n) (sq_nonneg _)
  have hYm : AEMeasurable (fun z => klLimit θ f z x) stdNormalSeq :=
    hmem.aestronglyMeasurable.aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have h1 : Tendsto (fun K => charFun (stdNormalSeq.map (fun z => klField θ f K z x)) t) atTop
      (𝓝 (charFun (stdNormalSeq.map (fun z => klLimit θ f z x)) t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun K => |t| * Real.sqrt
        (∫ z, (klLimit θ f z x - klField θ f K z x) ^ 2 ∂stdNormalSeq)) atTop (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp hlim).const_mul |t|
      simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using this
    refine squeeze_zero (fun K => norm_nonneg _) (fun K => ?_) hsq
    have hd : MemLp (fun z => klField θ f K z x - klLimit θ f z x) 2 stdNormalSeq :=
      (memLp_klField_apply θ f K x).sub hmem
    refine (kl_norm_charFun_map_sub_le
      (memLp_klField_apply θ f K x).aestronglyMeasurable.aemeasurable hYm
      (hd.integrable (by norm_num)) t).trans ?_
    refine mul_le_mul_of_nonneg_left ((kl_integral_abs_le_sqrt hd).trans_eq ?_) (abs_nonneg t)
    congr 1
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  have h2 : Tendsto (fun K => charFun (stdNormalSeq.map (fun z => klField θ f K z x)) t) atTop
      (𝓝 (charFun (gaussianReal 0 (R x x).toNNReal) t)) := by
    simp_rw [map_klField_eq_gaussianReal hθ f _ x, charFun_gaussianReal]
    refine (Complex.continuous_exp.tendsto _).comp ?_
    have hσ : Tendsto (fun K => ((∑ n ∈ range K, θ n * f n x ^ 2).toNNReal : ℂ)) atTop
        (𝓝 ((R x x).toNNReal : ℂ)) := by
      have h3 := (NNReal.continuous_coe.tendsto _).comp
        ((continuous_real_toNNReal.tendsto _).comp hR'.tendsto_sum_nat)
      exact (Complex.continuous_ofReal.tendsto _).comp h3
    exact tendsto_const_nhds.sub ((hσ.mul_const _).div_const _)
  exact tendsto_nhds_unique h1 h2

/-- `⟪[u], [v]⟫ = ∫ u v` in `L²` (used for Giles 2015, §7.2, p. 53, l. 2255–2262). -/
lemma kl_inner_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {u v : Ω → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    @inner ℝ _ _ (hu.toLp u) (hv.toLp v) = ∫ ω, u ω * v ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with z h1 h2
  simp [h1, h2, mul_comm]

/-- Cauchy–Schwarz: `∫ u v ≤ (∫ u²)^{1/2} (∫ v²)^{1/2}` (used for Giles 2015, §7.2, p. 53,
l. 2255–2262). -/
lemma kl_integral_mul_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {u v : Ω → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ∫ ω, u ω * v ω ∂μ ≤ Real.sqrt (∫ ω, u ω ^ 2 ∂μ) * Real.sqrt (∫ ω, v ω ^ 2 ∂μ) := by
  rw [← kl_inner_toLp hu hv, ← klNorm_toLp_sq hu, ← klNorm_toLp_sq hv,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact real_inner_le_norm _ _

/-- The truncated fields converge to the untruncated one in `L²` (Giles 2015, §7.2, p. 53,
l. 2257–2267). -/
lemma tendsto_toLp_klField {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) {f : ℕ → D → ℝ} {x : D}
    (hx : Summable fun n => θ n * f n x ^ 2) :
    Tendsto (fun K => (memLp_klField_apply θ f K x).toLp _) atTop
      (𝓝 ((klLimit_tendsto hθ hx).2.1.toLp _)) := by
  obtain ⟨-, hmem, -, hlim⟩ := klLimit_tendsto hθ hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun K => Real.sqrt
      (∫ z, (klLimit θ f z x - klField θ f K z x) ^ 2 ∂stdNormalSeq)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    simpa only [Function.comp_def, Real.sqrt_zero] using this
  refine hsq.congr fun K => ?_
  rw [← MemLp.toLp_sub, ← Real.sqrt_sq (norm_nonneg _), klNorm_toLp_sq]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun z => by simp only [Pi.sub_apply]; ring)

/-- **The covariance of the untruncated field is `R`** (Giles 2015, §7.2, p. 53, l. 2254–2262:
"a covariance function of the general form `R(x, y)` … `log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`,
where `θ_n` are the eigenvalues of `R(x, y)` …, `f_n` are the corresponding eigenfunctions").  For
`θ_n ≥ 0`, points `x, y` with `∑ θ_n f_n(x)² < ∞`, `∑ θ_n f_n(y)² < ∞`, and Mercer's expansion
`R(x, y) = ∑ θ_n f_n(x) f_n(y)`, the fields `Y(x), Y(y)` are square integrable and
`E[Y(x) Y(y)] = R(x, y)`. -/
theorem integral_klLimit_mul {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) {f : ℕ → D → ℝ}
    {R : D → D → ℝ} {x y : D} (hx : Summable fun n => θ n * f n x ^ 2)
    (hy : Summable fun n => θ n * f n y ^ 2)
    (hxy : HasSum (fun n => θ n * f n x * f n y) (R x y)) :
    MemLp (fun z => klLimit θ f z x) 2 stdNormalSeq ∧
      MemLp (fun z => klLimit θ f z y) 2 stdNormalSeq ∧
      Integrable (fun z => klLimit θ f z x * klLimit θ f z y) stdNormalSeq ∧
      ∫ z, klLimit θ f z x * klLimit θ f z y ∂stdNormalSeq = R x y := by
  have hmx := (klLimit_tendsto hθ hx).2.1
  have hmy := (klLimit_tendsto hθ hy).2.1
  refine ⟨hmx, hmy, hmx.integrable_mul hmy, ?_⟩
  have h1 := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_toLp_klField hθ hx)
    (tendsto_toLp_klField hθ hy)
  simp only [kl_inner_toLp] at h1
  exact tendsto_nhds_unique h1 (tendsto_integral_klField_mul hθ f hxy)

/-- **The moments of the untruncated diffusivity** (Giles 2015, §7.2, pp. 51–53, l. 2219–2220:
"`κ` is often modelled as a lognormal random field", l. 2257–2259:
"`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`", and l. 2275: "the diffusivity is unbounded").
For `θ_n ≥ 0`, every real `p` and a point `x` where Mercer's expansion `R(x, x) = ∑ θ_n f_n(x)²`
holds, `κ(x)^p` is integrable and `E[κ(x)^p] = E[exp(p Y(x))] = exp(p² R(x, x)/2)`. -/
theorem klLimitDiffusivity_moment {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) {f : ℕ → D → ℝ}
    {R : D → D → ℝ} {x : D} (hR : HasSum (fun n => θ n * f n x * f n x) (R x x)) (p : ℝ) :
    Integrable (fun z => klLimitDiffusivity θ f z x ^ p) stdNormalSeq ∧
      ∫ z, klLimitDiffusivity θ f z x ^ p ∂stdNormalSeq = Real.exp (p ^ 2 * R x x / 2) := by
  have hpow : ∀ z, klLimitDiffusivity θ f z x ^ p = Real.exp (p * klLimit θ f z x) := by
    intro z
    rw [klLimitDiffusivity, ← Real.exp_mul, mul_comm]
  simp_rw [hpow]
  have hR0 : 0 ≤ R x x := hR.nonneg fun n => by nlinarith [hθ n, sq_nonneg (f n x)]
  have hmgf := mgf_gaussianReal (map_klLimit_eq_gaussianReal hθ hR) p
  rw [Real.coe_toNNReal _ hR0, zero_mul, zero_add] at hmgf
  refine ⟨mgf_pos_iff.1 (hmgf ▸ Real.exp_pos _), ?_⟩
  have hval : Real.exp (R x x * p ^ 2 / 2) = Real.exp (p ^ 2 * R x x / 2) := by
    congr 1
    ring
  rw [← hval, ← hmgf]
  rfl

/-- `|e^a − e^b| ≤ |a − b| (e^a + e^b)` (used for Giles 2015, §7.2, p. 53, l. 2266–2268). -/
lemma kl_abs_exp_sub_exp_le (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ |a - b| * (Real.exp a + Real.exp b) := by
  wlog hab : b ≤ a generalizing a b
  · have := this b a (le_of_not_ge hab)
    rw [abs_sub_comm, abs_sub_comm b a, add_comm] at this
    exact this
  have h1 : Real.exp b ≤ Real.exp a := Real.exp_le_exp.2 hab
  have h2 : 1 - (a - b) ≤ Real.exp (b - a) := by
    have := Real.add_one_le_exp (b - a)
    linarith
  have h3 : Real.exp a * Real.exp (b - a) = Real.exp b := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 hab)]
  have h4 : 0 ≤ Real.exp a := (Real.exp_pos a).le
  nlinarith [Real.exp_pos b]

/-- **The truncated diffusivity converges to the untruncated one in `L¹`, with all moments**
(Giles 2015, §7.2, pp. 51–53, l. 2219–2220: "`κ` is often modelled as a lognormal random field",
and l. 2266–2268: "the expansion is truncated after `K_ℓ` terms, with `K_ℓ` increasing with
level").  For `θ_n ≥ 0`, every real `p` and a point `x` with `∑ θ_n f_n(x)² < ∞`,
`κ_K(x)^p` and `κ(x)^p` are integrable, `κ_K(x)^p → κ(x)^p` in `L¹`: `E|κ_K(x)^p − κ(x)^p| → 0`,
and so `E[κ_K(x)^p] → E[κ(x)^p]`. -/
theorem tendsto_integral_abs_klDiffusivity_rpow_sub {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n)
    {f : ℕ → D → ℝ} {x : D} (hx : Summable fun n => θ n * f n x ^ 2) (p : ℝ) :
    (∀ K, Integrable (fun z => klDiffusivity θ f K z x ^ p) stdNormalSeq) ∧
      Integrable (fun z => klLimitDiffusivity θ f z x ^ p) stdNormalSeq ∧
      (∀ K, Integrable (fun z => |klDiffusivity θ f K z x ^ p - klLimitDiffusivity θ f z x ^ p|)
        stdNormalSeq) ∧
      Tendsto (fun K => ∫ z, |klDiffusivity θ f K z x ^ p - klLimitDiffusivity θ f z x ^ p|
        ∂stdNormalSeq) atTop (𝓝 0) ∧
      Tendsto (fun K => ∫ z, klDiffusivity θ f K z x ^ p ∂stdNormalSeq) atTop
        (𝓝 (∫ z, klLimitDiffusivity θ f z x ^ p ∂stdNormalSeq)) := by
  set σ2 := ∑' n, θ n * f n x ^ 2
  have hR : HasSum (fun n => θ n * f n x * f n x) ((fun (_ _ : D) => σ2) x x) := by
    refine hx.hasSum.congr_fun fun n => ?_
    ring
  have hY := fun q => klLimitDiffusivity_moment hθ (f := f) (R := fun _ _ => σ2) (x := x) hR q
  have hS := fun K q => klDiffusivity_moment hθ f (R := fun _ _ => σ2) (x := x) hR q K
  have hpowY : ∀ q z, klLimitDiffusivity θ f z x ^ q = Real.exp (q * klLimit θ f z x) := by
    intro q z
    rw [klLimitDiffusivity, ← Real.exp_mul, mul_comm]
  have hpowS : ∀ q K z, klDiffusivity θ f K z x ^ q = Real.exp (q * klField θ f K z x) := by
    intro q K z
    rw [klDiffusivity, ← Real.exp_mul, mul_comm]
  obtain ⟨-, hmem, -, hlim⟩ := klLimit_tendsto hθ hx
  have hint : ∀ K, Integrable
      (fun z => |klDiffusivity θ f K z x ^ p - klLimitDiffusivity θ f z x ^ p|) stdNormalSeq :=
    fun K => ((hS K p).1.sub (hY p).1).abs
  refine ⟨fun K => (hS K p).1, (hY p).1, hint, ?_⟩
  set C := Real.sqrt (4 * Real.exp ((2 * p) ^ 2 * σ2 / 2))
  have hbound : ∀ K, ∫ z, |klDiffusivity θ f K z x ^ p - klLimitDiffusivity θ f z x ^ p|
      ∂stdNormalSeq ≤
        |p| * Real.sqrt (∫ z, (klLimit θ f z x - klField θ f K z x) ^ 2 ∂stdNormalSeq) * C := by
    intro K
    have hSm := memLp_klField_apply θ f K x
    have hd : MemLp (fun z => |klField θ f K z x - klLimit θ f z x|) 2 stdNormalSeq :=
      (hSm.sub hmem).abs
    have hES : MemLp (fun z => Real.exp (p * klField θ f K z x)) 2 stdNormalSeq := by
      have hm : AEStronglyMeasurable (fun z => Real.exp (p * klField θ f K z x)) stdNormalSeq :=
        (Real.measurable_exp.comp_aemeasurable
          (hSm.aestronglyMeasurable.aemeasurable.const_mul p)).aestronglyMeasurable
      rw [memLp_two_iff_integrable_sq hm]
      refine (hS K (2 * p)).1.congr (ae_of_all _ fun z => ?_)
      simp only
      rw [hpowS, sq, ← Real.exp_add]
      ring_nf
    have hEY : MemLp (fun z => Real.exp (p * klLimit θ f z x)) 2 stdNormalSeq := by
      have hm : AEStronglyMeasurable (fun z => Real.exp (p * klLimit θ f z x)) stdNormalSeq :=
        (Real.measurable_exp.comp_aemeasurable
          (hmem.aestronglyMeasurable.aemeasurable.const_mul p)).aestronglyMeasurable
      rw [memLp_two_iff_integrable_sq hm]
      refine (hY (2 * p)).1.congr (ae_of_all _ fun z => ?_)
      simp only
      rw [hpowY, sq, ← Real.exp_add]
      ring_nf
    have hE := hES.add hEY
    have hsq : ∫ z, (Real.exp (p * klField θ f K z x) + Real.exp (p * klLimit θ f z x)) ^ 2
        ∂stdNormalSeq ≤ 4 * Real.exp ((2 * p) ^ 2 * σ2 / 2) := by
      have hi1 : Integrable (fun z => Real.exp (p * klField θ f K z x) ^ 2) stdNormalSeq :=
        hES.integrable_sq
      have hi2 : Integrable (fun z => Real.exp (p * klLimit θ f z x) ^ 2) stdNormalSeq :=
        hEY.integrable_sq
      have h1 : ∫ z, Real.exp (p * klField θ f K z x) ^ 2 ∂stdNormalSeq =
          Real.exp ((2 * p) ^ 2 * (∑ n ∈ range K, θ n * f n x ^ 2) / 2) := by
        rw [← (hS K (2 * p)).2.1]
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only
        rw [hpowS, sq, ← Real.exp_add]
        ring_nf
      have h2 : ∫ z, Real.exp (p * klLimit θ f z x) ^ 2 ∂stdNormalSeq =
          Real.exp ((2 * p) ^ 2 * σ2 / 2) := by
        rw [← (hY (2 * p)).2]
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only
        rw [hpowY, sq, ← Real.exp_add]
        ring_nf
      have h3 := (hS K (2 * p)).2.2
      calc _ ≤ ∫ z, (2 * Real.exp (p * klField θ f K z x) ^ 2 +
            2 * Real.exp (p * klLimit θ f z x) ^ 2) ∂stdNormalSeq := by
            refine integral_mono hE.integrable_sq ((hi1.const_mul 2).add (hi2.const_mul 2))
              fun z => ?_
            nlinarith [sq_nonneg (Real.exp (p * klField θ f K z x) -
              Real.exp (p * klLimit θ f z x))]
        _ = 2 * Real.exp ((2 * p) ^ 2 * (∑ n ∈ range K, θ n * f n x ^ 2) / 2) +
            2 * Real.exp ((2 * p) ^ 2 * σ2 / 2) := by
            rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
              integral_const_mul, h1, h2]
        _ ≤ 4 * Real.exp ((2 * p) ^ 2 * σ2 / 2) := by linarith
    have hpt : ∀ z, |klDiffusivity θ f K z x ^ p - klLimitDiffusivity θ f z x ^ p| ≤
        |p| * (|klField θ f K z x - klLimit θ f z x| *
          (Real.exp (p * klField θ f K z x) + Real.exp (p * klLimit θ f z x))) := by
      intro z
      rw [hpowS, hpowY, ← mul_assoc, ← abs_mul, mul_sub]
      exact kl_abs_exp_sub_exp_le _ _
    calc _ ≤ ∫ z, |p| * (|klField θ f K z x - klLimit θ f z x| *
          (Real.exp (p * klField θ f K z x) + Real.exp (p * klLimit θ f z x))) ∂stdNormalSeq :=
          integral_mono (hint K) ((hd.integrable_mul hE).const_mul _) hpt
      _ = |p| * ∫ z, |klField θ f K z x - klLimit θ f z x| *
          (Real.exp (p * klField θ f K z x) + Real.exp (p * klLimit θ f z x)) ∂stdNormalSeq :=
          integral_const_mul _ _
      _ ≤ |p| * (Real.sqrt (∫ z, |klField θ f K z x - klLimit θ f z x| ^ 2 ∂stdNormalSeq) *
          Real.sqrt (∫ z, (Real.exp (p * klField θ f K z x) +
            Real.exp (p * klLimit θ f z x)) ^ 2 ∂stdNormalSeq)) :=
          mul_le_mul_of_nonneg_left (kl_integral_mul_le_sqrt hd hE) (abs_nonneg p)
      _ ≤ |p| * (Real.sqrt (∫ z, (klLimit θ f z x - klField θ f K z x) ^ 2 ∂stdNormalSeq) *
          C) := by
          have he : ∫ z, |klField θ f K z x - klLimit θ f z x| ^ 2 ∂stdNormalSeq =
              ∫ z, (klLimit θ f z x - klField θ f K z x) ^ 2 ∂stdNormalSeq :=
            integral_congr_ae (ae_of_all _ fun z => by simp only [sq_abs]; ring)
          rw [he]
          gcongr
          exact Real.sqrt_le_sqrt hsq
      _ = _ := by ring
  have hlim' : Tendsto (fun K => |p| * Real.sqrt
      (∫ z, (klLimit θ f z x - klField θ f K z x) ^ 2 ∂stdNormalSeq) * C) atTop (𝓝 0) := by
    have := (((Real.continuous_sqrt.tendsto 0).comp hlim).const_mul |p|).mul_const C
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, zero_mul] using this
  have hL1 := squeeze_zero (fun K => integral_nonneg fun z => abs_nonneg _) hbound hlim'
  refine ⟨hL1, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun K => norm_nonneg _) (fun K => ?_) hL1
  rw [← integral_sub (hS K p).1 (hY p).1]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [Real.norm_eq_abs]

/-! ### Joint law, unboundedness, and the field on `Ω × D` -/

/-- A linear combination of the truncated field at finitely many points is a truncated field with
combined eigenfunctions (Giles 2015, §7.2, p. 53, l. 2257–2262). -/
lemma sum_mul_klField {ι : Type*} (s : Finset ι) (a : ι → ℝ) (x : ι → D) (θ : ℕ → ℝ)
    (f : ℕ → D → ℝ) (K : ℕ) (z : ℕ → ℝ) :
    ∑ i ∈ s, a i * klField θ f K z (x i) =
      klField θ (fun n (_ : Unit) => ∑ i ∈ s, a i * f n (x i)) K z () := by
  unfold klField
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Linear combinations of the untruncated field are Gaussian** (Giles 2015, §7.2, pp. 51–53,
l. 2220, 2254–2255: "`log κ` is a Gaussian field with a uniform mean (which we will take to be
zero for simplicity) and a covariance function of the general form `R(x, y)`", and l. 2257–2259:
"`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`").  For `θ_n ≥ 0`, finitely many points `x_i` where
Mercer's expansion `R(x_i, x_j) = ∑ θ_n f_n(x_i) f_n(x_j)` holds, and real `a_i`, the law of
`∑ a_i Y(x_i)` is `N(0, ∑_{i,j} a_i a_j R(x_i, x_j))`. -/
theorem map_sum_klLimit_eq_gaussianReal {ι : Type*} [Fintype ι] {θ : ℕ → ℝ}
    (hθ : ∀ n, 0 ≤ θ n) {f : ℕ → D → ℝ} {R : D → D → ℝ} (x : ι → D)
    (hR : ∀ i j, HasSum (fun n => θ n * f n (x i) * f n (x j)) (R (x i) (x j))) (a : ι → ℝ) :
    stdNormalSeq.map (fun z => ∑ i, a i * klLimit θ f z (x i)) =
      gaussianReal 0 (∑ i, ∑ j, a i * a j * R (x i) (x j)).toNNReal := by
  set g : ℕ → Unit → ℝ := fun n _ => ∑ i, a i * f n (x i) with hg
  have hgs : HasSum (fun n => θ n * g n () * g n ()) (∑ i, ∑ j, a i * a j * R (x i) (x j)) := by
    have h := hasSum_sum fun i (_ : i ∈ Finset.univ) =>
      hasSum_sum fun j (_ : j ∈ Finset.univ) => (hR i j).mul_left (a i * a j)
    refine h.congr_fun fun n => ?_
    simp only [hg]
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmap := map_klLimit_eq_gaussianReal hθ (f := g)
    (R := fun _ _ => ∑ i, ∑ j, a i * a j * R (x i) (x j)) (x := ()) hgs
  rw [← hmap]
  refine Measure.map_congr ?_
  have hsx : ∀ i, Summable fun n => θ n * f n (x i) ^ 2 := fun i =>
    (hR i i).summable.congr fun n => by ring
  have hsg : Summable fun n => θ n * g n () ^ 2 := hgs.summable.congr fun n => by ring
  have hall : ∀ᵐ z ∂stdNormalSeq, ∀ i,
      Tendsto (fun K => klField θ f K z (x i)) atTop (𝓝 (klLimit θ f z (x i))) :=
    ae_all_iff.2 fun i => (klLimit_tendsto hθ (hsx i)).1
  filter_upwards [hall, (klLimit_tendsto hθ hsg).1] with z hz hzg
  have h1 : Tendsto (fun K => ∑ i, a i * klField θ f K z (x i)) atTop
      (𝓝 (∑ i, a i * klLimit θ f z (x i))) :=
    tendsto_finsetSum _ fun i _ => (hz i).const_mul (a i)
  simp_rw [sum_mul_klField] at h1
  exact tendsto_nhds_unique h1 hzg

/-- **The untruncated field is jointly Gaussian** (Giles 2015, §7.2, pp. 51–53, l. 2220: "`log κ`
is a Gaussian field", and l. 2257–2259: "`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`").  For
`θ_n ≥ 0` and finitely many points `x_i` where Mercer's expansion
`R(x_i, x_j) = ∑ θ_n f_n(x_i) f_n(x_j)` holds, the law of the vector `(Y(x_i))_i` is a Gaussian
measure on `ι → ℝ` (its image under every continuous linear form is a real Gaussian), its
coordinates are square integrable, its mean is `0` and its covariance matrix is `R(x_i, x_j)`. -/
theorem isGaussian_map_klLimit {ι : Type*} [Fintype ι] {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n)
    {f : ℕ → D → ℝ} {R : D → D → ℝ} (x : ι → D)
    (hR : ∀ i j, HasSum (fun n => θ n * f n (x i) * f n (x j)) (R (x i) (x j))) :
    IsGaussian (stdNormalSeq.map fun z k => klLimit θ f z (x k)) ∧
      (∀ i, MemLp (fun v : ι → ℝ => v i) 2 (stdNormalSeq.map fun z k => klLimit θ f z (x k))) ∧
      (∀ i, ∫ v, v i ∂(stdNormalSeq.map fun z k => klLimit θ f z (x k)) = 0) ∧
      ∀ i j, ∫ v, v i * v j ∂(stdNormalSeq.map fun z k => klLimit θ f z (x k)) =
        R (x i) (x j) := by
  classical
  have hsx : ∀ i, Summable fun n => θ n * f n (x i) ^ 2 := fun i =>
    (hR i i).summable.congr fun n => by ring
  have hYi : ∀ i, AEMeasurable (fun z => klLimit θ f z (x i)) stdNormalSeq := fun i =>
    (klLimit_tendsto hθ (hsx i)).2.1.aestronglyMeasurable.aemeasurable
  have hV : AEMeasurable (fun z k => klLimit θ f z (x k)) stdNormalSeq :=
    aemeasurable_pi_lambda _ hYi
  refine ⟨?_, fun i => ?_, fun i => ?_, fun i j => ?_⟩
  rotate_left
  · rw [memLp_map_measure_iff (continuous_apply i).aestronglyMeasurable hV]
    exact (klLimit_tendsto hθ (hsx i)).2.1
  · rw [integral_map hV (continuous_apply i).aestronglyMeasurable,
      ← integral_map (hYi i) (f := fun y : ℝ => y) aestronglyMeasurable_id,
      map_klLimit_eq_gaussianReal hθ (hR i i)]
    exact integral_id_gaussianReal
  · rw [integral_map hV (f := fun v : ι → ℝ => v i * v j)
      ((continuous_apply i).mul (continuous_apply j)).aestronglyMeasurable]
    exact (integral_klLimit_mul hθ (hsx i) (hsx j) (hR i j)).2.2.2
  refine isGaussian_of_map_eq_gaussianReal fun L => ?_
  set a : ι → ℝ := fun i => L fun j => if i = j then 1 else 0
  refine ⟨0, (∑ i, ∑ j, a i * a j * R (x i) (x j)).toNNReal, ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hV]
  have hL : (⇑L ∘ fun z k => klLimit θ f z (x k)) = fun z =>
      ∑ i, a i * klLimit θ f z (x i) := by
    funext z
    simp only [Function.comp_apply]
    have h := (L : (ι → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ (fun i => klLimit θ f z (x i))
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  rw [hL]
  exact map_sum_klLimit_eq_gaussianReal hθ x hR _

/-- **The diffusivity is unbounded** (Giles 2015, §7.2, p. 53, l. 2274–2275: "The numerical
analysis of the multilevel approach for these elliptic SPDE applications is challenging because the
diffusivity is unbounded").  For `θ_n ≥ 0` and a point `x` with Mercer's expansion
`R(x, x) = ∑ θ_n f_n(x)²` and `R(x, x) > 0`, for every threshold `M` both `κ(x) > M` and
`1/κ(x) > M` have positive probability: neither `κ(x)` nor `1/κ(x)` is essentially bounded. -/
theorem klLimitDiffusivity_unbounded {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) {f : ℕ → D → ℝ}
    {R : D → D → ℝ} {x : D} (hR : HasSum (fun n => θ n * f n x * f n x) (R x x))
    (hpos : 0 < R x x) (M : ℝ) :
    0 < stdNormalSeq {z | M < klLimitDiffusivity θ f z x} ∧
      0 < stdNormalSeq {z | M < (klLimitDiffusivity θ f z x)⁻¹} := by
  have hmap := map_klLimit_eq_gaussianReal hθ hR
  have hR' : Summable fun n => θ n * f n x ^ 2 := hR.summable.congr fun n => by ring
  have hYm : AEMeasurable (fun z => klLimit θ f z x) stdNormalSeq :=
    (klLimit_tendsto hθ hR').2.1.aestronglyMeasurable.aemeasurable
  have hv : (R x x).toNNReal ≠ 0 := by simpa using hpos
  have hpos' : ∀ s : Set ℝ, MeasurableSet s → volume s ≠ 0 →
      0 < stdNormalSeq ((fun z => klLimit θ f z x) ⁻¹' s) := by
    intro s hs hvol
    rw [← Measure.map_apply_of_aemeasurable hYm hs, hmap]
    exact pos_iff_ne_zero.2 fun h => hvol (gaussianReal_absolutelyContinuous' 0 hv h)
  set c := Real.log (max M 1) with hc
  have hexp : M ≤ Real.exp c := by
    rw [hc, Real.exp_log (lt_of_lt_of_le one_pos (le_max_right M 1))]
    exact le_max_left M 1
  constructor
  · refine (hpos' (Set.Ioi c) measurableSet_Ioi (by simp)).trans_le (measure_mono ?_)
    intro z hz
    simp only [Set.mem_preimage, Set.mem_Ioi] at hz
    show M < Real.exp (klLimit θ f z x)
    exact hexp.trans_lt (Real.exp_lt_exp.2 hz)
  · refine (hpos' (Set.Iio (-c)) measurableSet_Iio (by simp)).trans_le (measure_mono ?_)
    intro z hz
    simp only [Set.mem_preimage, Set.mem_Iio] at hz
    show M < (Real.exp (klLimit θ f z x))⁻¹
    rw [← Real.exp_neg]
    exact hexp.trans_lt (Real.exp_lt_exp.2 (by linarith))

/-- An `L²` limit and an almost sure limit of the same sequence agree almost everywhere (used for
Giles 2015, §7.2, p. 53, l. 2257–2267). -/
lemma kl_ae_eq_of_tendsto_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S : ℕ → Ω → ℝ} {Y Z : Ω → ℝ} (hS : ∀ K, MemLp (S K) 2 μ) (hY : MemLp Y 2 μ)
    (hlim : Tendsto (fun K => ∫ ω, (Y ω - S K ω) ^ 2 ∂μ) atTop (𝓝 0))
    (hZ : ∀ᵐ ω ∂μ, Tendsto (fun K => S K ω) atTop (𝓝 (Z ω))) : Y =ᵐ[μ] Z := by
  have hmeas : TendstoInMeasure μ S atTop Y := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun K => (hS K).aestronglyMeasurable) hY.aestronglyMeasurable ?_
    have he : ∀ K, eLpNorm (S K - Y) 2 μ =
        ENNReal.ofReal (Real.sqrt (∫ ω, (Y ω - S K ω) ^ 2 ∂μ)) := by
      intro K
      have hd := (hS K).sub hY
      rw [← ENNReal.ofReal_toReal hd.eLpNorm_ne_top, ← Lp.norm_toLp _ hd,
        ← Real.sqrt_sq (norm_nonneg _), klNorm_toLp_sq]
      congr 2
      exact integral_congr_ae (ae_of_all _ fun ω => by simp only [Pi.sub_apply]; ring)
    simp_rw [he]
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    simpa only [Function.comp_def, Real.sqrt_zero] using this
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  filter_upwards [hZ, hae] with ω h1 h2
  exact tendsto_nhds_unique h2 (h1.comp hns.tendsto_atTop)

/-- **The pointwise series is the `L²(P ⊗ ν)` limit field** (Giles 2015, §7.2, p. 53,
l. 2257–2262: "`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`", and l. 2266–2267: "the expansion is
truncated after `K_ℓ` terms").  With orthonormal `f_n ∈ L²(ν)` and summable `θ_n ≥ 0` (the
hypotheses of the `L²(P ⊗ ν)` construction), `∑ θ_n f_n(x)² < ∞` for `ν`-a.e. `x`; the partial
sums converge `(P ⊗ ν)`-a.e. to `klLimit`; `klLimit ∈ L²(P ⊗ ν)` with
`E ∫ (Y − Y_K)² dν = ∑_{n≥K} θ_n`; and every `Y ∈ L²(P ⊗ ν)` with `E ∫ (Y − Y_K)² dν → 0` equals
`klLimit` `(P ⊗ ν)`-a.e. -/
theorem klLimit_ae_eq_L2_limit [MeasurableSpace D] {ν : Measure D} [SFinite ν] {θ : ℕ → ℝ}
    (hθ : ∀ n, 0 ≤ θ n) (hθs : Summable θ) {f : ℕ → D → ℝ} (hf : ∀ n, MemLp (f n) 2 ν)
    (hfo : ∀ n m, ∫ x, f n x * f m x ∂ν = if n = m then 1 else 0) :
    (∀ᵐ x ∂ν, Summable fun n => θ n * f n x ^ 2) ∧
      (∀ᵐ p ∂(stdNormalSeq.prod ν), Tendsto (fun K => klField θ f K p.1 p.2) atTop
        (𝓝 (klLimit θ f p.1 p.2))) ∧
      MemLp (fun p : (ℕ → ℝ) × D => klLimit θ f p.1 p.2) 2 (stdNormalSeq.prod ν) ∧
      (∀ K, Integrable (fun p : (ℕ → ℝ) × D => (klLimit θ f p.1 p.2 - klField θ f K p.1 p.2) ^ 2)
          (stdNormalSeq.prod ν) ∧
        ∫ p, (klLimit θ f p.1 p.2 - klField θ f K p.1 p.2) ^ 2 ∂(stdNormalSeq.prod ν) =
          ∑' n, θ (n + K)) ∧
      ∀ Y : (ℕ → ℝ) × D → ℝ, MemLp Y 2 (stdNormalSeq.prod ν) →
        Tendsto (fun K => ∫ p, (Y p - klField θ f K p.1 p.2) ^ 2 ∂(stdNormalSeq.prod ν)) atTop
          (𝓝 0) →
        Y =ᵐ[stdNormalSeq.prod ν] fun p => klLimit θ f p.1 p.2 := by
  -- a.e. summability of `∑ θ_n f_n(x)²`
  have hnorm : ∀ n, ∫ x, f n x ^ 2 ∂ν = 1 := by
    intro n
    have h := hfo n n
    rw [if_pos rfl] at h
    simpa only [sq] using h
  have hterm : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (θ n * f n x ^ 2)) ν := fun n =>
    (((hf n).aestronglyMeasurable.aemeasurable.pow_const 2).const_mul (θ n)).ennreal_ofReal
  have hlin : ∫⁻ x, ∑' n, ENNReal.ofReal (θ n * f n x ^ 2) ∂ν = ∑' n, ENNReal.ofReal (θ n) := by
    rw [lintegral_tsum hterm]
    refine tsum_congr fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal ((hf n).integrable_sq.const_mul (θ n))
      (ae_of_all _ fun x => mul_nonneg (hθ n) (sq_nonneg _)), integral_const_mul, hnorm, mul_one]
  have hfin : ∑' n, ENNReal.ofReal (θ n) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hθ hθs]
    exact ENNReal.ofReal_ne_top
  have hsum : ∀ᵐ x ∂ν, Summable fun n => θ n * f n x ^ 2 := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hterm) (hlin ▸ hfin)] with x hx
    refine (ENNReal.summable_toReal hx.ne).congr fun n => ?_
    exact ENNReal.toReal_ofReal (mul_nonneg (hθ n) (sq_nonneg _))
  -- a.e. convergence on the product, through measurable versions of the `f_n`
  set f' : ℕ → D → ℝ := fun n => (hf n).aestronglyMeasurable.mk (f n)
  have hf'm : ∀ n, Measurable (f' n) := fun n =>
    (hf n).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hG : ∀ᵐ x ∂ν, ∀ n, f n x = f' n x :=
    ae_all_iff.2 fun n => (hf n).aestronglyMeasurable.ae_eq_mk
  have hSm : ∀ K, Measurable fun p : (ℕ → ℝ) × D => klField θ f' K p.1 p.2 := by
    intro K
    show Measurable fun p : (ℕ → ℝ) × D => ∑ n ∈ range K, Real.sqrt (θ n) * p.1 n * f' n p.2
    exact Finset.measurable_fun_sum _ fun n _ =>
      (measurable_const.mul ((measurable_pi_apply n).comp measurable_fst)).mul
        ((hf'm n).comp measurable_snd)
  set A : Set ((ℕ → ℝ) × D) :=
    {p | ∃ c, Tendsto (fun K => klField θ f' K p.1 p.2) atTop (𝓝 c)}
  have hAm : MeasurableSet A := measurableSet_exists_tendsto hSm
  have hxA : ∀ᵐ x ∂ν, ∀ᵐ z ∂stdNormalSeq, (z, x) ∈ A := by
    filter_upwards [hG, hsum] with x hx1 hx2
    filter_upwards [(klLimit_tendsto hθ hx2).1] with z hz
    refine ⟨klLimit θ f z x, ?_⟩
    have h : (fun K => klField θ f' K z x) = fun K => klField θ f K z x := by
      funext K
      unfold klField
      simp only [hx1]
    rw [h]
    exact hz
  have hpA : ∀ᵐ p ∂(stdNormalSeq.prod ν), p ∈ A := by
    refine (Measure.ae_prod_iff_ae_ae (p := (· ∈ A)) hAm).2 ?_
    exact (Measure.ae_ae_comm (p := fun z x => (z, x) ∈ A) hAm).2 hxA
  have hpG : ∀ᵐ p ∂(stdNormalSeq.prod ν), ∀ n, f n p.2 = f' n p.2 :=
    Measure.quasiMeasurePreserving_snd.ae hG
  have hconv : ∀ᵐ p ∂(stdNormalSeq.prod ν), Tendsto (fun K => klField θ f K p.1 p.2) atTop
      (𝓝 (klLimit θ f p.1 p.2)) := by
    filter_upwards [hpA, hpG] with p hp1 hp2
    have h : (fun K => klField θ f K p.1 p.2) = fun K => klField θ f' K p.1 p.2 := by
      funext K
      unfold klField
      simp only [hp2]
    rw [klLimit, h]
    exact tendsto_nhds_limUnder hp1
  -- identification with the `L²` limit
  have hS2 := memLp_klField θ hf (ν := ν)
  have hid : ∀ Y : (ℕ → ℝ) × D → ℝ, MemLp Y 2 (stdNormalSeq.prod ν) →
      Tendsto (fun K => ∫ p, (Y p - klField θ f K p.1 p.2) ^ 2 ∂(stdNormalSeq.prod ν)) atTop
        (𝓝 0) →
      Y =ᵐ[stdNormalSeq.prod ν] fun p => klLimit θ f p.1 p.2 :=
    fun Y hY hlim => kl_ae_eq_of_tendsto_integral_sq hS2 hY hlim hconv
  obtain ⟨Y₀, hY₀, hY₀K, hY₀lim⟩ := exists_klField_limit hθ hθs hf hfo
  have heq := hid Y₀ hY₀ hY₀lim
  refine ⟨hsum, hconv, hY₀.ae_eq heq, fun K => ⟨?_, ?_⟩, hid⟩
  · refine (hY₀K K).1.congr ?_
    filter_upwards [heq] with p hp
    rw [hp]
  · rw [← (hY₀K K).2]
    refine integral_congr_ae ?_
    filter_upwards [heq] with p hp
    rw [hp]

end MLMC
