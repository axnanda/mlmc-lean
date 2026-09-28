import MlmcLean.StandardEstimator
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Randomised multilevel Monte Carlo: the single-term estimator

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.2 (p. 9–11),
presenting the estimator of C.-H. Rhee and P.W. Glynn (2012, 2013).

The single-term estimator uses `N` samples in total; for each sample it draws a random level `ℓ'`
with `P(ℓ' = ℓ) = p_ℓ`, independently of the path simulation, and averages
`p_{ℓ'}⁻¹ (P_{ℓ'} − P_{ℓ'−1})` (with `P_{−1} ≡ 0`) over the `N` samples (p. 9).  `singleTerm` is one
sample (`N = 1`); `singleTermN` is the average of `N` independent samples.  Writing
`E_ℓ = E[P_ℓ − P_{ℓ−1}]` and `V_ℓ = V[P_ℓ − P_{ℓ−1}]`, Giles states on p. 10:

* `E[Y] = ∑_ℓ E[P_ℓ − P_{ℓ−1}] = E[P]` — `singleTerm_unbiased` (one sample) and
  `singleTermN_mean_variance` (`N` samples, `V[Y_N] = V[Y]/N`);
* `V[Y] = ∑_ℓ p_ℓ⁻¹ (V_ℓ + E_ℓ²) − (∑_ℓ E_ℓ)² ≥ ∑_ℓ p_ℓ⁻¹ V_ℓ` "due to Jensen's inequality" —
  `singleTerm_variance`, `singleTerm_variance_ge`;
* "for both the variance and the expected cost to be finite, it is necessary that
  `∑ p_ℓ⁻¹ V_ℓ < ∞` and `∑ p_ℓ C_ℓ < ∞`" — `randomised_necessary`, built on
  `summable_of_memLp_singleTerm` (variance) and `integral_cost_level` (the expected cost of one
  sample is `∑ p_ℓ C_ℓ` when the cost of a level-`ℓ` sample is independent of the level);
* under the conditions of Theorem 1 "this is possible when `β > γ` by choosing
  `p_ℓ ∝ 2^{−(γ+β)ℓ/2}`, so that `p_ℓ⁻¹ V_ℓ ∝ 2^{−(β−γ)ℓ/2}` and `p_ℓ C_ℓ ∝ 2^{−(β−γ)ℓ/2}`" —
  `randomised_summable`; "it is not possible when `β ≤ γ`" — `randomised_not_summable`, when the
  rates are attained;
* "the optimal choice for `p_ℓ` is `p_ℓ = √(V_ℓ/C_ℓ) (∑ √(V_ℓ'/C_ℓ'))⁻¹`": it minimises the product
  `(∑ p_ℓ⁻¹ V_ℓ)(∑ p_ℓ C_ℓ)`, which, when `E_ℓ² ≪ V_ℓ`, is approximately `ε²` times the cost of
  reaching variance `ε²` (p. 10), with minimum `(∑ √(V_ℓ C_ℓ))²` — `randomised_optimal_p_isLeast`
  (built on the Cauchy–Schwarz inequality `randomised_optimal_p`, which the paper does not state,
  and on `randomised_optimal_p_eq`).

**Standing assumptions made explicit.**  The paper leaves the integrability behind these
identities implicit.  We assume the level approximations are measurable and the level `K` is
independent of each `P_ℓ − P_{ℓ−1}`; unbiasedness needs `∑_ℓ E|P_ℓ − P_{ℓ−1}| < ∞` (exactly
`E|Y| < ∞`) and `E[P_L] → E[P]` (implied by condition (i) of Theorem 1); the variance formula needs
`∑_ℓ p_ℓ⁻¹ E[(P_ℓ − P_{ℓ−1})²] < ∞` (exactly `E[Y²] < ∞`).  The two summability conditions in
the paper are *necessary* for finite variance and finite expected cost respectively; they are not
sufficient for finite variance, because the variance also contains `∑ p_ℓ⁻¹ E_ℓ²`.  With the
second-moment form of condition (iii) that Giles mentions on p. 7, the estimator has finite
variance and finite expected cost (`randomised_mlmc_finite`).
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace MLMC

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [MeasurableSpace Ω] in
/-- One sample (`N = 1`) of the single-term estimator of Rhee and Glynn (Giles 2015, §2.2, p. 9):
`Y = p_K⁻¹ (P_K − P_{K−1})` for the random level `K`, with `P_{−1} ≡ 0`. -/
noncomputable def singleTerm (Pl : ℕ → Ω → ℝ) (K : Ω → ℕ) (p : ℕ → ℝ) (ω : Ω) : ℝ :=
  (p (K ω))⁻¹ * levelDiff Pl (K ω) ω

lemma measurable_comp_level {K : Ω → ℕ} (hK : Measurable K) {g : ℕ → Ω → ℝ}
    (hgm : ∀ ℓ, Measurable (g ℓ)) : Measurable fun ω => g (K ω) ω := by
  have h : Measurable fun q : Ω × ℕ => g q.2 q.1 :=
    measurable_from_prod_countable_left fun n => hgm n
  exact h.comp (measurable_id.prodMk hK)

section levelSelection

variable [IsProbabilityMeasure μ] {K : Ω → ℕ}

omit [IsProbabilityMeasure μ] in
/-- If the level `K` is independent of `h`, then `∫_{K = ℓ} h = P(K = ℓ) E[h]`. -/
lemma setIntegral_level (hK : Measurable K) {h : Ω → ℝ} (hm : Measurable h)
    (hi : IndepFun K h μ) (ℓ : ℕ) :
    ∫ ω in {ω | K ω = ℓ}, h ω ∂μ = μ.real {ω | K ω = ℓ} * ∫ ω, h ω ∂μ := by
  have hs : MeasurableSet {ω | K ω = ℓ} := hK (measurableSet_singleton ℓ)
  let φ : ℕ → ℝ := fun n => if n = ℓ then 1 else 0
  have hφm : Measurable φ := measurable_from_top
  have hind : IndepFun (φ ∘ K) h μ := hi.comp hφm measurable_id
  have hφK : φ ∘ K = {ω | K ω = ℓ}.indicator 1 := by
    funext ω
    by_cases hω : K ω = ℓ <;> simp [φ, Set.indicator, hω]
  calc ∫ ω in {ω | K ω = ℓ}, h ω ∂μ
      = ∫ ω, (φ ∘ K) ω * h ω ∂μ := by
        rw [← integral_indicator hs, hφK]
        congr 1
        funext ω
        by_cases hω : K ω = ℓ <;> simp [Set.indicator, hω]
    _ = (∫ ω, (φ ∘ K) ω ∂μ) * ∫ ω, h ω ∂μ :=
        hind.integral_fun_mul_eq_mul_integral (hφm.comp hK).aestronglyMeasurable
          hm.aestronglyMeasurable
    _ = μ.real {ω | K ω = ℓ} * ∫ ω, h ω ∂μ := by
        rw [hφK, integral_indicator_one hs]

omit [MeasurableSpace Ω] in
lemma iUnion_level_eq_univ (K : Ω → ℕ) : ⋃ ℓ, {ω | K ω = ℓ} = Set.univ :=
  Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K ω, rfl⟩

omit [MeasurableSpace Ω] in
lemma pairwise_disjoint_level (K : Ω → ℕ) :
    Pairwise (Function.onFun Disjoint fun ℓ => {ω | K ω = ℓ}) := fun i j hij =>
  Set.disjoint_left.2 fun ω (hi : K ω = i) (hj : K ω = j) => hij (hi.symm.trans hj)

/-- The level probabilities `P(K = ℓ)` sum to one. -/
lemma hasSum_measureReal_level (hK : Measurable K) :
    HasSum (fun ℓ => μ.real {ω | K ω = ℓ}) 1 := by
  have hs : ∀ ℓ, MeasurableSet {ω | K ω = ℓ} := fun ℓ => hK (measurableSet_singleton ℓ)
  have hint : IntegrableOn (fun _ => (1 : ℝ)) (⋃ ℓ, {ω | K ω = ℓ}) μ := by
    rw [iUnion_level_eq_univ K]
    exact integrableOn_const
  have h := hasSum_integral_iUnion hs (pairwise_disjoint_level K) hint
  have e1 : ∀ ℓ, ∫ _ in {ω | K ω = ℓ}, (1 : ℝ) ∂μ = μ.real {ω | K ω = ℓ} := fun ℓ => by
    rw [setIntegral_const, smul_eq_mul, mul_one]
  have e2 : ∫ _ in ⋃ ℓ, {ω | K ω = ℓ}, (1 : ℝ) ∂μ = 1 := by
    rw [iUnion_level_eq_univ K, setIntegral_const, smul_eq_mul, mul_one, probReal_univ]
  rw [e2] at h
  simp only [e1] at h
  exact h

omit [IsProbabilityMeasure μ] in
/-- **Expectation over a random level.**  Let the level `K` be independent of each `g ℓ`.  If
`∑_ℓ P(K = ℓ) E|g_ℓ| < ∞`, then `g_K` is integrable and `E[g_K] = ∑_ℓ P(K = ℓ) E[g_ℓ]`. -/
theorem integral_comp_level (hK : Measurable K) (g : ℕ → Ω → ℝ) (hgm : ∀ ℓ, Measurable (g ℓ))
    (hgi : ∀ ℓ, Integrable (g ℓ) μ) (hind : ∀ ℓ, IndepFun K (g ℓ) μ)
    (hsum : Summable fun ℓ => μ.real {ω | K ω = ℓ} * ∫ ω, |g ℓ ω| ∂μ) :
    Integrable (fun ω => g (K ω) ω) μ ∧
      ∫ ω, g (K ω) ω ∂μ = ∑' ℓ, μ.real {ω | K ω = ℓ} * ∫ ω, g ℓ ω ∂μ := by
  have hs : ∀ ℓ, MeasurableSet {ω | K ω = ℓ} := fun ℓ => hK (measurableSet_singleton ℓ)
  have heq : ∀ ℓ, Set.EqOn (fun ω => g (K ω) ω) (g ℓ) {ω | K ω = ℓ} :=
    fun ℓ ω (hω : K ω = ℓ) => by simp only [hω]
  have hon : ∀ ℓ, IntegrableOn (fun ω => g (K ω) ω) {ω | K ω = ℓ} μ :=
    fun ℓ => (hgi ℓ).integrableOn.congr_fun (heq ℓ).symm (hs ℓ)
  have hnorm : ∀ ℓ, ∫ ω in {ω | K ω = ℓ}, ‖g (K ω) ω‖ ∂μ =
      μ.real {ω | K ω = ℓ} * ∫ ω, |g ℓ ω| ∂μ := fun ℓ => by
    rw [setIntegral_congr_fun (hs ℓ) (f := fun ω => ‖g (K ω) ω‖) (g := fun ω => |g ℓ ω|)
      (fun ω (hω : K ω = ℓ) => by simp only [hω, Real.norm_eq_abs])]
    exact setIntegral_level (h := fun ω => |g ℓ ω|) hK (continuous_abs.measurable.comp (hgm ℓ))
      ((hind ℓ).comp measurable_id continuous_abs.measurable) ℓ
  have hint : IntegrableOn (fun ω => g (K ω) ω) (⋃ ℓ, {ω | K ω = ℓ}) μ :=
    integrableOn_iUnion_of_summable_integral_norm hon (hsum.congr fun ℓ => (hnorm ℓ).symm)
  have hint' : Integrable (fun ω => g (K ω) ω) μ := by
    rw [iUnion_level_eq_univ K, integrableOn_univ] at hint
    exact hint
  refine ⟨hint', ?_⟩
  rw [← setIntegral_univ, ← iUnion_level_eq_univ K,
    integral_iUnion hs (pairwise_disjoint_level K) hint]
  refine tsum_congr fun ℓ => ?_
  rw [setIntegral_congr_fun (hs ℓ) (heq ℓ), setIntegral_level hK (hgm ℓ) (hind ℓ) ℓ]

variable {Pl : ℕ → Ω → ℝ} {p : ℕ → ℝ}

omit [IsProbabilityMeasure μ] in
/-- **Expected cost of one sample of the single-term estimator** (Giles 2015, §2.2, p. 10, where the
expected cost per sample is `∑_ℓ p_ℓ C_ℓ`).  Let `κ ℓ ≥ 0` be the random cost of a level-`ℓ` sample,
measurable, integrable and independent of the level `K`, where `P(K = ℓ) = p_ℓ`.  Then the cost
`κ_K` of one sample is integrable if and only if `∑_ℓ p_ℓ E[κ_ℓ] < ∞`, and then
`E[κ_K] = ∑_ℓ p_ℓ E[κ_ℓ]`. -/
theorem integral_cost_level (hK : Measurable K) {κ : ℕ → Ω → ℝ} (hκm : ∀ ℓ, Measurable (κ ℓ))
    (hκ0 : ∀ ℓ ω, 0 ≤ κ ℓ ω) (hκi : ∀ ℓ, Integrable (κ ℓ) μ) (hind : ∀ ℓ, IndepFun K (κ ℓ) μ)
    (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) :
    (Integrable (fun ω => κ (K ω) ω) μ ↔ Summable fun ℓ => p ℓ * ∫ ω, κ ℓ ω ∂μ) ∧
      (Summable (fun ℓ => p ℓ * ∫ ω, κ ℓ ω ∂μ) →
        ∫ ω, κ (K ω) ω ∂μ = ∑' ℓ, p ℓ * ∫ ω, κ ℓ ω ∂μ) := by
  have habs : ∀ ℓ, ∫ ω, |κ ℓ ω| ∂μ = ∫ ω, κ ℓ ω ∂μ := fun ℓ =>
    integral_congr_ae (Eventually.of_forall fun ω => abs_of_nonneg (hκ0 ℓ ω))
  have hsum_iff : (Summable fun ℓ => μ.real {ω | K ω = ℓ} * ∫ ω, |κ ℓ ω| ∂μ) ↔
      Summable fun ℓ => p ℓ * ∫ ω, κ ℓ ω ∂μ := by
    simp only [hp, habs]
  have hfwd : Summable (fun ℓ => p ℓ * ∫ ω, κ ℓ ω ∂μ) →
      Integrable (fun ω => κ (K ω) ω) μ ∧
        ∫ ω, κ (K ω) ω ∂μ = ∑' ℓ, p ℓ * ∫ ω, κ ℓ ω ∂μ := by
    intro hs
    obtain ⟨h1, h2⟩ := integral_comp_level hK κ hκm hκi hind (hsum_iff.2 hs)
    exact ⟨h1, h2.trans (tsum_congr fun ℓ => by rw [hp ℓ])⟩
  refine ⟨⟨fun hint => ?_, fun hs => (hfwd hs).1⟩, fun hs => (hfwd hs).2⟩
  -- only if: the integrals of `κ_K` over the level sets `{K = ℓ}` sum to `E[κ_K]`
  have hs : ∀ ℓ, MeasurableSet {ω | K ω = ℓ} := fun ℓ => hK (measurableSet_singleton ℓ)
  have hsum := hasSum_integral_iUnion (f := fun ω => κ (K ω) ω) hs (pairwise_disjoint_level K)
    (by rw [iUnion_level_eq_univ K]; exact hint.integrableOn)
  have hterm : ∀ ℓ, ∫ ω in {ω | K ω = ℓ}, κ (K ω) ω ∂μ = p ℓ * ∫ ω, κ ℓ ω ∂μ := fun ℓ => by
    rw [setIntegral_congr_fun (hs ℓ) (f := fun ω => κ (K ω) ω) (g := κ ℓ)
      (fun ω (hω : K ω = ℓ) => by simp only [hω]), setIntegral_level hK (hκm ℓ) (hind ℓ) ℓ,
      hp ℓ]
  exact hsum.summable.congr hterm

omit [IsProbabilityMeasure μ] in
/-- `E|Y| < ∞` and `E[Y] = ∑_ℓ E[P_ℓ − P_{ℓ−1}]` for one sample of the single-term estimator
(Giles 2015, §2.2, p. 10, the middle step of the unbiasedness computation). -/
theorem integral_singleTerm (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ))
    (hPl : ∀ ℓ, Integrable (Pl ℓ) μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ)
    (hp0 : ∀ ℓ, 0 < p ℓ) (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ)
    (hsum : Summable fun ℓ => ∫ ω, |levelDiff Pl ℓ ω| ∂μ) :
    Integrable (singleTerm Pl K p) μ ∧
      ∫ ω, singleTerm Pl K p ω ∂μ = ∑' ℓ, ∫ ω, levelDiff Pl ℓ ω ∂μ := by
  have hsum' : Summable fun ℓ =>
      μ.real {ω | K ω = ℓ} * ∫ ω, |(p ℓ)⁻¹ * levelDiff Pl ℓ ω| ∂μ := by
    refine hsum.congr fun ℓ => ?_
    simp_rw [abs_mul, abs_inv, abs_of_pos (hp0 ℓ)]
    rw [hp ℓ, integral_const_mul, ← mul_assoc, mul_inv_cancel₀ (hp0 ℓ).ne', one_mul]
  have key : Integrable (fun ω => (p (K ω))⁻¹ * levelDiff Pl (K ω) ω) μ ∧
      ∫ ω, (p (K ω))⁻¹ * levelDiff Pl (K ω) ω ∂μ =
        ∑' ℓ, μ.real {ω | K ω = ℓ} * ∫ ω, (p ℓ)⁻¹ * levelDiff Pl ℓ ω ∂μ :=
    integral_comp_level hK (fun ℓ ω => (p ℓ)⁻¹ * levelDiff Pl ℓ ω)
      (fun ℓ => (measurable_levelDiff hPlm ℓ).const_mul _)
      (fun ℓ => (integrable_levelDiff hPl ℓ).const_mul _)
      (fun ℓ => (hind ℓ).comp measurable_id (measurable_id.const_mul _)) hsum'
  refine ⟨key.1, ?_⟩
  change ∫ ω, (p (K ω))⁻¹ * levelDiff Pl (K ω) ω ∂μ = _
  rw [key.2]
  refine tsum_congr fun ℓ => ?_
  rw [hp ℓ, integral_const_mul, ← mul_assoc, mul_inv_cancel₀ (hp0 ℓ).ne', one_mul]

-- `hP`: `P` is the quantity whose mean `E[P]` is estimated (Giles 2015, §2.2), so it is integrable;
-- the proof does not use it (without it, `E[P]` would be read as the junk value `0`).
omit [IsProbabilityMeasure μ] in
set_option linter.unusedVariables false in
/-- **Unbiasedness of the single-term estimator** (Giles 2015, §2.2, p. 10): one sample `Y` is
integrable and `E[Y] = E[P]` (the paper's middle step `E[Y] = ∑_ℓ E[P_ℓ − P_{ℓ−1}]` is
`integral_singleTerm`).  The measure `μ` is not assumed to be a probability measure: the
hypotheses `hp`, `hp0` and `hind` force `μ(Ω) = 1`. -/
theorem singleTerm_unbiased (P : Ω → ℝ) (hP : Integrable P μ) (hK : Measurable K)
    (hPlm : ∀ ℓ, Measurable (Pl ℓ))
    (hPl : ∀ ℓ, Integrable (Pl ℓ) μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ)
    (hp0 : ∀ ℓ, 0 < p ℓ) (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ)
    (hsum : Summable fun ℓ => ∫ ω, |levelDiff Pl ℓ ω| ∂μ)
    (hconv : Tendsto (fun L => ∫ ω, Pl L ω ∂μ) atTop (𝓝 (∫ ω, P ω ∂μ))) :
    Integrable (singleTerm Pl K p) μ ∧ ∫ ω, singleTerm Pl K p ω ∂μ = ∫ ω, P ω ∂μ := by
  obtain ⟨hint, heq⟩ := integral_singleTerm hK hPlm hPl hp hp0 hind hsum
  refine ⟨hint, ?_⟩
  have ha : Summable fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ :=
    Summable.of_norm_bounded hsum fun ℓ => by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (levelDiff Pl ℓ)
  have h1 : Tendsto (fun L => ∑ ℓ ∈ range (L + 1), ∫ ω, levelDiff Pl ℓ ω ∂μ) atTop
      (𝓝 (∑' ℓ, ∫ ω, levelDiff Pl ℓ ω ∂μ)) :=
    ha.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2 : (fun L => ∑ ℓ ∈ range (L + 1), ∫ ω, levelDiff Pl ℓ ω ∂μ) =
      fun L => ∫ ω, Pl L ω ∂μ := funext (sum_integral_levelDiff hPl)
  rw [h2] at h1
  rw [heq]
  exact tendsto_nhds_unique h1 hconv

/-- `E[X²] = V[X] + E[X]²`. -/
lemma integral_sq_eq {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ∫ ω, X ω ^ 2 ∂μ = variance X μ + (∫ ω, X ω ∂μ) ^ 2 := by
  rw [variance_eq_sub hX]
  simp only [Pi.pow_apply]
  ring

/-- `E|X| ≤ (t + E[X²]/t)/2` for every `t > 0` (from `2t|x| ≤ t² + x²`). -/
lemma integral_abs_le_of_sq {X : Ω → ℝ} (hX : MemLp X 2 μ) {t : ℝ} (ht : 0 < t) :
    ∫ ω, |X ω| ∂μ ≤ (t + (∫ ω, X ω ^ 2 ∂μ) / t) / 2 := by
  have hX1 : Integrable X μ := hX.integrable one_le_two
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
  have hpt : ∀ ω, |X ω| ≤ (t + X ω ^ 2 / t) / 2 := fun ω => by
    rw [le_div_iff₀ two_pos, add_div' _ _ _ ht.ne', le_div_iff₀ ht]
    nlinarith [sq_nonneg (|X ω| - t), sq_abs (X ω)]
  calc ∫ ω, |X ω| ∂μ ≤ ∫ ω, (t + X ω ^ 2 / t) / 2 ∂μ :=
        integral_mono hX1.abs ((integrable_const t |>.add (hX2.div_const t)).div_const 2) hpt
    _ = (t + (∫ ω, X ω ^ 2 ∂μ) / t) / 2 := by
        rw [integral_div, integral_add (integrable_const t) (hX2.div_const t), integral_div,
          integral_const, probReal_univ, one_smul]

/-- A finite second-moment series `∑ p_ℓ⁻¹ E[(P_ℓ − P_{ℓ−1})²] < ∞` implies the first-moment series
`∑ E|P_ℓ − P_{ℓ−1}| < ∞` (the level probabilities sum to one). -/
lemma summable_abs_of_summable_sq (hK : Measurable K) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ)
    (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) (hp0 : ∀ ℓ, 0 < p ℓ)
    (hsum2 : Summable fun ℓ => (∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ) / p ℓ) :
    Summable fun ℓ => ∫ ω, |levelDiff Pl ℓ ω| ∂μ := by
  have hpsum : Summable p := by
    have := (hasSum_measureReal_level (μ := μ) hK).summable
    exact this.congr hp
  refine Summable.of_nonneg_of_le (fun ℓ => integral_nonneg fun ω => abs_nonneg _)
    (fun ℓ => integral_abs_le_of_sq (memLp_levelDiff hPl ℓ) (hp0 ℓ)) ?_
  exact ((hpsum.add hsum2).div_const 2)

/-- Jensen's (Cauchy–Schwarz) inequality for a probability vector `p`:
`(∑ a_ℓ)² ≤ ∑ a_ℓ² / p_ℓ`. -/
lemma sq_tsum_le_tsum_sq_div {a q : ℕ → ℝ} (hq : ∀ ℓ, 0 < q ℓ) (hq1 : HasSum q 1)
    (ha : Summable a) (ha2 : Summable fun ℓ => a ℓ ^ 2 / q ℓ) :
    (∑' ℓ, a ℓ) ^ 2 ≤ ∑' ℓ, a ℓ ^ 2 / q ℓ := by
  have hfin : ∀ n, (∑ ℓ ∈ range n, a ℓ) ^ 2 ≤ ∑' ℓ, a ℓ ^ 2 / q ℓ := fun n => by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range n) (fun ℓ => Real.sqrt (q ℓ))
      (fun ℓ => a ℓ / Real.sqrt (q ℓ))
    have e1 : ∀ ℓ, Real.sqrt (q ℓ) * (a ℓ / Real.sqrt (q ℓ)) = a ℓ := fun ℓ =>
      mul_div_cancel₀ _ (Real.sqrt_pos.2 (hq ℓ)).ne'
    have e2 : ∀ ℓ, (a ℓ / Real.sqrt (q ℓ)) ^ 2 = a ℓ ^ 2 / q ℓ := fun ℓ => by
      rw [div_pow, Real.sq_sqrt (hq ℓ).le]
    have e3 : ∀ ℓ, Real.sqrt (q ℓ) ^ 2 = q ℓ := fun ℓ => Real.sq_sqrt (hq ℓ).le
    simp only [e1, e2, e3] at hcs
    have hq_le : ∑ ℓ ∈ range n, q ℓ ≤ 1 := by
      rw [← hq1.tsum_eq]
      exact hq1.summable.sum_le_tsum _ fun ℓ _ => (hq ℓ).le
    have h2 : ∑ ℓ ∈ range n, a ℓ ^ 2 / q ℓ ≤ ∑' ℓ, a ℓ ^ 2 / q ℓ :=
      ha2.sum_le_tsum _ fun ℓ _ => div_nonneg (sq_nonneg _) (hq ℓ).le
    have h3 : 0 ≤ ∑ ℓ ∈ range n, a ℓ ^ 2 / q ℓ :=
      Finset.sum_nonneg fun ℓ _ => div_nonneg (sq_nonneg _) (hq ℓ).le
    nlinarith
  exact le_of_tendsto' ((ha.hasSum.tendsto_sum_nat).pow 2) hfin

/-- **Variance of the single-term estimator** (Giles 2015, §2.2, p. 10):
if `∑_ℓ p_ℓ⁻¹ E[(P_ℓ − P_{ℓ−1})²] < ∞` then `Y` has finite variance and
`V[Y] = ∑_ℓ p_ℓ⁻¹ (V_ℓ + E_ℓ²) − (∑_ℓ E_ℓ)²`. -/
theorem singleTerm_variance (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ))
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) (hp0 : ∀ ℓ, 0 < p ℓ)
    (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ)
    (hsum2 : Summable fun ℓ => (∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ) / p ℓ) :
    MemLp (singleTerm Pl K p) 2 μ ∧
      variance (singleTerm Pl K p) μ =
        ∑' ℓ, (variance (levelDiff Pl ℓ) μ + (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2) / p ℓ -
          (∑' ℓ, ∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2 := by
  have hΔ := memLp_levelDiff hPl
  have hsum := summable_abs_of_summable_sq hK hPl hp hp0 hsum2
  obtain ⟨-, hmean⟩ := integral_singleTerm hK hPlm (fun ℓ => (hPl ℓ).integrable one_le_two) hp
    hp0 hind hsum
  -- the second moment, by `integral_comp_level` applied to the squares
  have hsq' : Summable fun ℓ =>
      μ.real {ω | K ω = ℓ} * ∫ ω, |((p ℓ)⁻¹ * levelDiff Pl ℓ ω) ^ 2| ∂μ := by
    refine hsum2.congr fun ℓ => ?_
    simp_rw [abs_pow, abs_mul, abs_inv, abs_of_pos (hp0 ℓ), mul_pow, sq_abs]
    rw [hp ℓ, integral_const_mul]
    field_simp [(hp0 ℓ).ne']
  have key : Integrable (fun ω => ((p (K ω))⁻¹ * levelDiff Pl (K ω) ω) ^ 2) μ ∧
      ∫ ω, ((p (K ω))⁻¹ * levelDiff Pl (K ω) ω) ^ 2 ∂μ =
        ∑' ℓ, μ.real {ω | K ω = ℓ} * ∫ ω, ((p ℓ)⁻¹ * levelDiff Pl ℓ ω) ^ 2 ∂μ :=
    integral_comp_level hK (fun ℓ ω => ((p ℓ)⁻¹ * levelDiff Pl ℓ ω) ^ 2)
      (fun ℓ => ((measurable_levelDiff hPlm ℓ).const_mul _).pow_const 2)
      (fun ℓ => ((hΔ ℓ).const_mul _).integrable_sq)
      (fun ℓ => (hind ℓ).comp measurable_id ((measurable_id.const_mul _).pow_const 2)) hsq'
  have hY : MemLp (singleTerm Pl K p) 2 μ :=
    (memLp_two_iff_integrable_sq
      (measurable_comp_level hK fun ℓ =>
        (measurable_levelDiff hPlm ℓ).const_mul (p ℓ)⁻¹).aestronglyMeasurable).2 key.1
  refine ⟨hY, ?_⟩
  rw [variance_eq_sub hY]
  have h2 : μ[singleTerm Pl K p ^ 2] =
      ∑' ℓ, (variance (levelDiff Pl ℓ) μ + (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2) / p ℓ := by
    change ∫ ω, ((p (K ω))⁻¹ * levelDiff Pl (K ω) ω) ^ 2 ∂μ = _
    rw [key.2]
    refine tsum_congr fun ℓ => ?_
    simp_rw [mul_pow]
    rw [hp ℓ, integral_const_mul, integral_sq_eq (hΔ ℓ)]
    field_simp [(hp0 ℓ).ne']
  rw [h2, hmean]

/-- The variance bound `V[Y] ≥ ∑_ℓ p_ℓ⁻¹ V_ℓ` (Giles 2015, §2.2, p. 10, "due to Jensen's
inequality"), for one sample with finite second moment (`hsum2`; without it `V[Y] = ∞` and the
bound is trivial in `[0, ∞]`). -/
theorem singleTerm_variance_ge (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ))
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) (hp0 : ∀ ℓ, 0 < p ℓ)
    (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ)
    (hsum2 : Summable fun ℓ => (∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ) / p ℓ) :
    ∑' ℓ, variance (levelDiff Pl ℓ) μ / p ℓ ≤ variance (singleTerm Pl K p) μ := by
  have hΔ := memLp_levelDiff hPl
  have hsum := summable_abs_of_summable_sq hK hPl hp hp0 hsum2
  have hp1 : HasSum p 1 := by
    have h := hasSum_measureReal_level (μ := μ) hK
    simp only [hp] at h
    exact h
  have hVs : Summable fun ℓ => variance (levelDiff Pl ℓ) μ / p ℓ :=
    Summable.of_nonneg_of_le (fun ℓ => div_nonneg (variance_nonneg _ _) (hp0 ℓ).le)
      (fun ℓ => div_le_div_of_nonneg_right
        (by rw [integral_sq_eq (hΔ ℓ)]; exact le_add_of_nonneg_right (sq_nonneg _)) (hp0 ℓ).le)
      hsum2
  have hEs : Summable fun ℓ => (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2 / p ℓ :=
    Summable.of_nonneg_of_le (fun ℓ => div_nonneg (sq_nonneg _) (hp0 ℓ).le)
      (fun ℓ => div_le_div_of_nonneg_right
        (by rw [integral_sq_eq (hΔ ℓ)]; exact le_add_of_nonneg_left (variance_nonneg _ _))
        (hp0 ℓ).le) hsum2
  have ha : Summable fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ :=
    Summable.of_norm_bounded hsum fun ℓ => by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (levelDiff Pl ℓ)
  -- Jensen's inequality for the level distribution: `(∑ E_ℓ)² ≤ ∑ E_ℓ²/p_ℓ`
  have hjensen := sq_tsum_le_tsum_sq_div hp0 hp1 ha hEs
  rw [(singleTerm_variance hK hPlm hPl hp hp0 hind hsum2).2]
  have hsplit : ∑' ℓ, (variance (levelDiff Pl ℓ) μ + (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2) / p ℓ =
      ∑' ℓ, variance (levelDiff Pl ℓ) μ / p ℓ + ∑' ℓ, (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2 / p ℓ := by
    rw [← hVs.tsum_add hEs]
    exact tsum_congr fun ℓ => add_div _ _ _
  rw [hsplit]
  linarith

/-- **Necessity, variance half** (Giles 2015, §2.2, p. 10): if one sample of the single-term
estimator has finite variance, then `∑_ℓ p_ℓ⁻¹ V_ℓ < ∞`. -/
theorem summable_of_memLp_singleTerm (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ))
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) (hp0 : ∀ ℓ, 0 < p ℓ)
    (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ) (hY : MemLp (singleTerm Pl K p) 2 μ) :
    Summable fun ℓ => variance (levelDiff Pl ℓ) μ / p ℓ := by
  have hΔ := memLp_levelDiff hPl
  have hs : ∀ ℓ, MeasurableSet {ω | K ω = ℓ} := fun ℓ => hK (measurableSet_singleton ℓ)
  have hY2 : Integrable (fun ω => singleTerm Pl K p ω ^ 2) μ := hY.integrable_sq
  have hsum := hasSum_integral_iUnion (f := fun ω => singleTerm Pl K p ω ^ 2) hs
    (pairwise_disjoint_level K) (by rw [iUnion_level_eq_univ K]; exact hY2.integrableOn)
  have hterm : ∀ ℓ, ∫ ω in {ω | K ω = ℓ}, singleTerm Pl K p ω ^ 2 ∂μ =
      (∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ) / p ℓ := fun ℓ => by
    rw [setIntegral_congr_fun (hs ℓ) (f := fun ω => singleTerm Pl K p ω ^ 2)
        (g := fun ω => ((p ℓ)⁻¹ * levelDiff Pl ℓ ω) ^ 2)
        (fun ω (hω : K ω = ℓ) => by simp only [singleTerm, hω]),
      setIntegral_level (h := fun ω => ((p ℓ)⁻¹ * levelDiff Pl ℓ ω) ^ 2) hK
        (((measurable_levelDiff hPlm ℓ).const_mul (p ℓ)⁻¹).pow_const 2)
        ((hind ℓ).comp measurable_id ((measurable_id.const_mul (p ℓ)⁻¹).pow_const 2)) ℓ, hp ℓ]
    simp_rw [mul_pow]
    rw [integral_const_mul]
    field_simp [(hp0 ℓ).ne']
  have h2 : Summable fun ℓ => (∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ) / p ℓ :=
    hsum.summable.congr hterm
  refine Summable.of_nonneg_of_le (fun ℓ => div_nonneg (variance_nonneg _ _) (hp0 ℓ).le)
    (fun ℓ => div_le_div_of_nonneg_right ?_ (hp0 ℓ).le) h2
  exact variance_le_expectation_sq (hΔ ℓ).aestronglyMeasurable

/-- **Necessity** (Giles 2015, §2.2, p. 10): "For both the variance and the expected cost to be
finite, it is necessary that `∑_ℓ p_ℓ⁻¹ V_ℓ < ∞` and `∑_ℓ p_ℓ C_ℓ < ∞`".  If one sample of the
single-term estimator has finite variance and its cost `κ_K` has finite expectation, where the cost
`κ_ℓ ≥ 0` of a level-`ℓ` sample is measurable and integrable with mean `C_ℓ` and independent of the
level `K`, then both series converge. -/
theorem randomised_necessary (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ))
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) (hp0 : ∀ ℓ, 0 < p ℓ)
    (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ) {κ : ℕ → Ω → ℝ} {C : ℕ → ℝ}
    (hκm : ∀ ℓ, Measurable (κ ℓ)) (hκ0 : ∀ ℓ ω, 0 ≤ κ ℓ ω) (hκi : ∀ ℓ, Integrable (κ ℓ) μ)
    (hκind : ∀ ℓ, IndepFun K (κ ℓ) μ) (hC : ∀ ℓ, ∫ ω, κ ℓ ω ∂μ = C ℓ)
    (hY : MemLp (singleTerm Pl K p) 2 μ) (hcost : Integrable (fun ω => κ (K ω) ω) μ) :
    Summable (fun ℓ => variance (levelDiff Pl ℓ) μ / p ℓ) ∧ Summable (fun ℓ => p ℓ * C ℓ) := by
  refine ⟨summable_of_memLp_singleTerm hK hPlm hPl hp hp0 hind hY, ?_⟩
  have h := (integral_cost_level hK hκm hκ0 hκi hκind hp).1.1 hcost
  exact h.congr fun ℓ => by rw [hC ℓ]

end levelSelection

/-! ### The single-term estimator with `N` samples -/

section Nsamples

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- The single-term estimator with `N` samples (Giles 2015, §2.2, p. 9):
`Y_N = N⁻¹ ∑_{n<N} p_{K_n}⁻¹ (P_{K_n} − P_{K_n−1})`, where the `n`-th sample — a path together with
its random level — is the input `ξ n` (the paper's `n = 1, …, N` shifted to `0, …, N−1`). -/
noncomputable def singleTermN (Pl : ℕ → Ω → ℝ) (K : Ω → ℕ) (p : ℕ → ℝ) (ξ : ℕ → Ω' → Ω)
    (N : ℕ) (x : Ω') : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ range N, singleTerm Pl K p (ξ n x)

/-- **The single-term estimator with `N` samples** (Giles 2015, §2.2, pp. 9–10): with `N ≥ 1`
independent samples `ξ n` of law `μ`, each a path together with its random level `K`, and under the
hypotheses of `singleTerm_unbiased` and `singleTerm_variance` for one sample, the estimator `Y_N` is
unbiased, `E[Y_N] = E[P]`, and has variance `V[Y_N] = V[Y]/N`, where `V[Y]` is the variance of one
sample given by `singleTerm_variance`. -/
theorem singleTermN_mean_variance [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {K : Ω → ℕ} {Pl : ℕ → Ω → ℝ} {p : ℕ → ℝ} (P : Ω → ℝ) (hP : Integrable P μ)
    (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ)
    (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) (hp0 : ∀ ℓ, 0 < p ℓ)
    (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ)
    (hsum2 : Summable fun ℓ => (∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ) / p ℓ)
    (hconv : Tendsto (fun L => ∫ ω, Pl L ω ∂μ) atTop (𝓝 (∫ ω, P ω ∂μ)))
    {ξ : ℕ → Ω' → Ω} (hξ : ∀ n, MeasurePreserving (ξ n) μ' μ) (hξind : iIndepFun ξ μ')
    {N : ℕ} (hN : 0 < N) :
    ∫ x, singleTermN Pl K p ξ N x ∂μ' = ∫ ω, P ω ∂μ ∧
      variance (singleTermN Pl K p ξ N) μ' = variance (singleTerm Pl K p) μ / N := by
  have hsum := summable_abs_of_summable_sq hK hPl hp hp0 hsum2
  obtain ⟨hint, hmean⟩ := singleTerm_unbiased P hP hK hPlm
    (fun ℓ => (hPl ℓ).integrable one_le_two) hp hp0 hind hsum hconv
  have hY2 : MemLp (singleTerm Pl K p) 2 μ := (singleTerm_variance hK hPlm hPl hp hp0 hind hsum2).1
  have hYm : Measurable (singleTerm Pl K p) :=
    measurable_comp_level hK fun ℓ => (measurable_levelDiff hPlm ℓ).const_mul (p ℓ)⁻¹
  have hXint : ∀ n, Integrable (fun x => singleTerm Pl K p (ξ n x)) μ' := fun n =>
    ((hξ n).integrable_comp hint.aestronglyMeasurable).2 hint
  constructor
  · simp only [singleTermN]
    rw [integral_const_mul, integral_finsetSum _ fun n _ => hXint n]
    have hterm : ∀ n, ∫ x, singleTerm Pl K p (ξ n x) ∂μ' = ∫ ω, P ω ∂μ := fun n => by
      rw [integral_comp_of_measurePreserving (hξ n) hint.aestronglyMeasurable, hmean]
    simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [← mul_assoc, inv_mul_cancel₀ hN', one_mul]
  · have hX : iIndepFun (fun n => singleTerm Pl K p ∘ ξ n) μ' :=
      hξind.comp (fun _ => singleTerm Pl K p) (fun _ => hYm)
    exact variance_sample_mean (fun n x => singleTerm Pl K p (ξ n x)) N hN _
      (fun n => hY2.comp_measurePreserving (hξ n))
      (fun n => (hξ n).variance_fun_comp hYm.aemeasurable)
      (fun a _ b _ hab => hX.indepFun hab)

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **The single-term estimator grouped by level** (Giles 2015, §2.2, p. 9: "Another way of
describing it is `Y = ∑_ℓ (p_ℓ N)⁻¹ ∑_{n=1}^{N_ℓ} (P_ℓ^{(n)} − P_{ℓ−1}^{(n)})` where `N_ℓ` is the
number of samples on level `ℓ`, with `∑_ℓ N_ℓ = N`").  For every outcome `x` and every finite set
`S` of levels containing the levels `K(ξ_n x)` of the `N` samples, the `N`-sample estimator is
`∑_{ℓ ∈ S} (p_ℓ N)⁻¹ ∑_{n : K(ξ_n x) = ℓ} (P_ℓ − P_{ℓ−1})(ξ_n x)`, and the level counts
`N_ℓ = #{n < N : K(ξ_n x) = ℓ}` add up to `N`. -/
theorem singleTermN_eq_sum_levels (Pl : ℕ → Ω → ℝ) (K : Ω → ℕ) (p : ℕ → ℝ)
    (ξ : ℕ → Ω' → Ω) (N : ℕ) (x : Ω') {S : Finset ℕ} (hS : ∀ n ∈ range N, K (ξ n x) ∈ S) :
    singleTermN Pl K p ξ N x = ∑ ℓ ∈ S, (p ℓ * N)⁻¹ *
        ∑ n ∈ (range N).filter (fun n => K (ξ n x) = ℓ), levelDiff Pl ℓ (ξ n x) ∧
      ∑ ℓ ∈ S, (((range N).filter (fun n => K (ξ n x) = ℓ)).card : ℝ) = N := by
  constructor
  · unfold singleTermN singleTerm
    rw [← Finset.sum_fiberwise_of_maps_to hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [(Finset.mem_filter.1 hn).2, mul_inv]
    ring
  · rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (fun n hn => hS n hn),
      Finset.card_range]

/-- **The expected level counts** (Giles 2015, §2.2, p. 9: "`E[N_ℓ] = p_ℓ N`").  If the `N`
samples `ξ_n` each have law `μ`, under which the level `K` takes the value `ℓ` with probability
`p_ℓ = μ(K = ℓ)`, then the number `N_ℓ = #{n < N : K(ξ_n) = ℓ}` of samples on level `ℓ` has
expectation `N p_ℓ`. -/
theorem integral_levelCount [IsProbabilityMeasure μ'] {K : Ω → ℕ} (hK : Measurable K)
    {ξ : ℕ → Ω' → Ω} (hξ : ∀ n, MeasurePreserving (ξ n) μ' μ) (N ℓ : ℕ) :
    ∫ x, (((range N).filter (fun n => K (ξ n x) = ℓ)).card : ℝ) ∂μ' =
      N * μ.real {ω | K ω = ℓ} := by
  have hset : ∀ n, MeasurableSet {x | K (ξ n x) = ℓ} := fun n =>
    (hK.comp (hξ n).measurable) (measurableSet_singleton ℓ)
  have hind : ∀ n, (fun x => if K (ξ n x) = ℓ then (1 : ℝ) else 0) =
      Set.indicator {x | K (ξ n x) = ℓ} 1 := fun n => by
    funext x
    by_cases h : K (ξ n x) = ℓ <;> simp [Set.indicator, h]
  have hint : ∀ n ∈ range N, Integrable (fun x => if K (ξ n x) = ℓ then (1 : ℝ) else 0) μ' :=
    fun n _ => by
      rw [hind n]
      exact (integrable_const (1 : ℝ)).indicator (hset n)
  have hterm : ∀ n, ∫ x, (if K (ξ n x) = ℓ then (1 : ℝ) else 0) ∂μ' = μ.real {ω | K ω = ℓ} :=
    fun n => by
      rw [hind n, integral_indicator_one (hset n)]
      exact congrArg ENNReal.toReal
        ((hξ n).measure_preimage (hK (measurableSet_singleton ℓ)).nullMeasurableSet)
  have hcard : ∀ x, (((range N).filter (fun n => K (ξ n x) = ℓ)).card : ℝ) =
      ∑ n ∈ range N, (if K (ξ n x) = ℓ then (1 : ℝ) else 0) := fun x =>
    Finset.natCast_card_filter _ _
  simp_rw [hcard]
  rw [integral_finsetSum _ hint]
  simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Nsamples

/-! ### The choice of level probabilities (pure real analysis) -/

/-- The level distribution `p_ℓ = (1 − r) r^ℓ` with `r = 2^{−(β+γ)/2}`, i.e.
`p_ℓ ∝ 2^{−(β+γ)ℓ/2}` (Giles 2015, §2.2, p. 10); a probability distribution when `β + γ > 0`. -/
noncomputable def geomLevelProb (β γ : ℝ) (ℓ : ℕ) : ℝ :=
  (1 - (2 : ℝ) ^ (-(β + γ) / 2)) * ((2 : ℝ) ^ (-(β + γ) / 2)) ^ ℓ

lemma geomLevelProb_pos {β γ : ℝ} (hβγ : 0 < β + γ) (ℓ : ℕ) : 0 < geomLevelProb β γ ℓ := by
  have hr : (2 : ℝ) ^ (-(β + γ) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold geomLevelProb
  exact mul_pos (by linarith) (pow_pos (Real.rpow_pos_of_pos two_pos _) _)

lemma hasSum_geomLevelProb {β γ : ℝ} (hβγ : 0 < β + γ) : HasSum (geomLevelProb β γ) 1 := by
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(β + γ) / 2) := (Real.rpow_pos_of_pos two_pos _).le
  have hr : (2 : ℝ) ^ (-(β + γ) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h := (hasSum_geometric_of_lt_one hr0 hr).mul_left (1 - (2 : ℝ) ^ (-(β + γ) / 2))
  rwa [mul_inv_cancel₀ (by linarith)] at h

/-- `2^{−βℓ} = q^ℓ r^ℓ` and `r^ℓ 2^{γℓ} = q^ℓ`, with `r = 2^{−(β+γ)/2}`, `q = 2^{−(β−γ)/2}`. -/
lemma geom_identities (β γ : ℝ) (ℓ : ℕ) :
    (2 : ℝ) ^ (-(β * (ℓ : ℝ))) =
        ((2 : ℝ) ^ (-(β - γ) / 2)) ^ ℓ * ((2 : ℝ) ^ (-(β + γ) / 2)) ^ ℓ ∧
      ((2 : ℝ) ^ (-(β + γ) / 2)) ^ ℓ * (2 : ℝ) ^ (γ * (ℓ : ℝ)) =
        ((2 : ℝ) ^ (-(β - γ) / 2)) ^ ℓ := by
  have h2 : (0 : ℝ) < 2 := two_pos
  constructor
  · rw [← mul_pow, ← Real.rpow_add h2, ← two_rpow_mul_nat]
    congr 1
    ring
  · rw [two_rpow_mul_nat γ ℓ, ← mul_pow, ← Real.rpow_add h2]
    congr 2
    ring

/-- Giles 2015, §2.2, p. 10: under conditions (iii), (iv) of Theorem 1 with `β > γ`, the choice
`p_ℓ ∝ 2^{−(β+γ)ℓ/2}` is a probability distribution with `∑_ℓ p_ℓ⁻¹ V_ℓ < ∞` and
`∑_ℓ p_ℓ C_ℓ < ∞`. -/
theorem randomised_summable {β γ c₂ c₃ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) {V C : ℕ → ℝ}
    (hV : ∀ ℓ, 0 ≤ V ℓ) (hC : ∀ ℓ, 0 ≤ C ℓ)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    (∀ ℓ, 0 < geomLevelProb β γ ℓ) ∧ HasSum (geomLevelProb β γ) 1 ∧
      Summable (fun ℓ => V ℓ / geomLevelProb β γ ℓ) ∧
      Summable (fun ℓ => geomLevelProb β γ ℓ * C ℓ) := by
  have hβγ : 0 < β + γ := by linarith
  set r : ℝ := (2 : ℝ) ^ (-(β + γ) / 2) with hr_def
  set q : ℝ := (2 : ℝ) ^ (-(β - γ) / 2) with hq_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos two_pos _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos two_pos _).le
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo := summable_geometric_of_lt_one hq0 hq1
  have hp := geomLevelProb_pos hβγ
  refine ⟨hp, hasSum_geomLevelProb hβγ, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun ℓ => div_nonneg (hV ℓ) (hp ℓ).le) (fun ℓ => ?_)
      (hgeo.mul_left (c₂ / (1 - r)))
    have hid := (geom_identities β γ ℓ).1
    rw [← hr_def, ← hq_def] at hid
    calc V ℓ / geomLevelProb β γ ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) / geomLevelProb β γ ℓ :=
          div_le_div_of_nonneg_right (h_iii ℓ) (hp ℓ).le
      _ = c₂ / (1 - r) * q ^ ℓ := by
          unfold geomLevelProb
          rw [← hr_def, hid]
          field_simp [(show (0 : ℝ) < 1 - r by linarith).ne', (pow_pos hr0 ℓ).ne']
  · refine Summable.of_nonneg_of_le (fun ℓ => mul_nonneg (hp ℓ).le (hC ℓ)) (fun ℓ => ?_)
      (hgeo.mul_left ((1 - r) * c₃))
    have hid := (geom_identities β γ ℓ).2
    rw [← hr_def, ← hq_def] at hid
    calc geomLevelProb β γ ℓ * C ℓ ≤ geomLevelProb β γ ℓ * (c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :=
          mul_le_mul_of_nonneg_left (h_iv ℓ) (hp ℓ).le
      _ = (1 - r) * c₃ * q ^ ℓ := by
          unfold geomLevelProb
          rw [← hr_def, ← hid]
          ring

/-- Giles 2015, §2.2, p. 10: "It is not possible when `β ≤ γ`": if `V_ℓ ≥ c₂ 2^{−βℓ}` and
`C_ℓ ≥ c₃ 2^{γℓ}` (the rates are attained) with `β ≤ γ`, then no choice of positive `p_ℓ` makes both
`∑_ℓ p_ℓ⁻¹ V_ℓ` and `∑_ℓ p_ℓ C_ℓ` finite. -/
theorem randomised_not_summable {β γ c₂ c₃ : ℝ} (hβγ : β ≤ γ) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    {V C p : ℕ → ℝ} (hp : ∀ ℓ, 0 < p ℓ)
    (hV : ∀ ℓ : ℕ, c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) ≤ V ℓ)
    (hC : ∀ ℓ : ℕ, c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ)) ≤ C ℓ) :
    ¬ (Summable (fun ℓ => V ℓ / p ℓ) ∧ Summable (fun ℓ => p ℓ * C ℓ)) := by
  rintro ⟨h1, h2⟩
  have hlim : Tendsto (fun ℓ => V ℓ / p ℓ * (p ℓ * C ℓ)) atTop (𝓝 0) := by
    have h := h1.tendsto_atTop_zero.mul h2.tendsto_atTop_zero
    rwa [mul_zero] at h
  have hlow : ∀ ℓ : ℕ, c₂ * c₃ ≤ V ℓ / p ℓ * (p ℓ * C ℓ) := fun ℓ => by
    have e : V ℓ / p ℓ * (p ℓ * C ℓ) = V ℓ * C ℓ := by field_simp [(hp ℓ).ne']
    rw [e]
    have h1' : 1 ≤ (2 : ℝ) ^ (-(β * (ℓ : ℝ))) * (2 : ℝ) ^ (γ * (ℓ : ℝ)) := by
      rw [← Real.rpow_add two_pos]
      exact Real.one_le_rpow (by norm_num) (by nlinarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)])
    have hV0 : 0 ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) := by positivity
    have hC0 : 0 ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ)) := by positivity
    calc c₂ * c₃ = c₂ * c₃ * 1 := (mul_one _).symm
      _ ≤ c₂ * c₃ * ((2 : ℝ) ^ (-(β * (ℓ : ℝ))) * (2 : ℝ) ^ (γ * (ℓ : ℝ))) := by gcongr
      _ = (c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) * (c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) := by ring
      _ ≤ V ℓ * C ℓ := mul_le_mul (hV ℓ) (hC ℓ) hC0 (hV0.trans (hV ℓ))
  have := ge_of_tendsto hlim (Eventually.of_forall hlow)
  have hpos : 0 < c₂ * c₃ := mul_pos hc₂ hc₃
  linarith

/-- Cauchy–Schwarz for the level distribution: for any positive `p_ℓ`,
`(∑_ℓ √(V_ℓ C_ℓ))² ≤ (∑_ℓ p_ℓ⁻¹ V_ℓ)(∑_ℓ p_ℓ C_ℓ)`.  Not stated in the paper: it is the exact
inequality behind the optimal choice of `p_ℓ` on p. 10 of Giles 2015, §2.2. -/
theorem randomised_optimal_p {V C p : ℕ → ℝ} (hV : ∀ ℓ, 0 ≤ V ℓ) (hC : ∀ ℓ, 0 ≤ C ℓ)
    (hp : ∀ ℓ, 0 < p ℓ) (h1 : Summable fun ℓ => V ℓ / p ℓ) (h2 : Summable fun ℓ => p ℓ * C ℓ) :
    Summable (fun ℓ => Real.sqrt (V ℓ * C ℓ)) ∧
      (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2 ≤ (∑' ℓ, V ℓ / p ℓ) * ∑' ℓ, p ℓ * C ℓ := by
  have hprod : ∀ ℓ, V ℓ * C ℓ = V ℓ / p ℓ * (p ℓ * C ℓ) := fun ℓ => by
    field_simp [(hp ℓ).ne']
  have hamgm : ∀ ℓ, Real.sqrt (V ℓ * C ℓ) ≤ (V ℓ / p ℓ + p ℓ * C ℓ) / 2 := fun ℓ => by
    have ha : 0 ≤ V ℓ / p ℓ := div_nonneg (hV ℓ) (hp ℓ).le
    have hb : 0 ≤ p ℓ * C ℓ := mul_nonneg (hp ℓ).le (hC ℓ)
    rw [hprod ℓ, Real.sqrt_le_left (by linarith)]
    nlinarith [sq_nonneg (V ℓ / p ℓ - p ℓ * C ℓ)]
  have hS : Summable fun ℓ => Real.sqrt (V ℓ * C ℓ) :=
    Summable.of_nonneg_of_le (fun ℓ => Real.sqrt_nonneg _) hamgm ((h1.add h2).div_const 2)
  refine ⟨hS, ?_⟩
  have hfin : ∀ n, (∑ ℓ ∈ range n, Real.sqrt (V ℓ * C ℓ)) ^ 2 ≤
      (∑' ℓ, V ℓ / p ℓ) * ∑' ℓ, p ℓ * C ℓ := fun n => by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range n) (fun ℓ => Real.sqrt (V ℓ / p ℓ))
      (fun ℓ => Real.sqrt (p ℓ * C ℓ))
    have e1 : ∀ ℓ, Real.sqrt (V ℓ / p ℓ) * Real.sqrt (p ℓ * C ℓ) = Real.sqrt (V ℓ * C ℓ) :=
      fun ℓ => by rw [← Real.sqrt_mul (div_nonneg (hV ℓ) (hp ℓ).le), ← hprod ℓ]
    have e2 : ∀ ℓ, Real.sqrt (V ℓ / p ℓ) ^ 2 = V ℓ / p ℓ :=
      fun ℓ => Real.sq_sqrt (div_nonneg (hV ℓ) (hp ℓ).le)
    have e3 : ∀ ℓ, Real.sqrt (p ℓ * C ℓ) ^ 2 = p ℓ * C ℓ :=
      fun ℓ => Real.sq_sqrt (mul_nonneg (hp ℓ).le (hC ℓ))
    simp only [e1, e2, e3] at hcs
    refine hcs.trans (mul_le_mul ?_ ?_ ?_ ?_)
    · exact h1.sum_le_tsum _ fun ℓ _ => div_nonneg (hV ℓ) (hp ℓ).le
    · exact h2.sum_le_tsum _ fun ℓ _ => mul_nonneg (hp ℓ).le (hC ℓ)
    · exact Finset.sum_nonneg fun ℓ _ => mul_nonneg (hp ℓ).le (hC ℓ)
    · exact tsum_nonneg fun ℓ => div_nonneg (hV ℓ) (hp ℓ).le
  exact le_of_tendsto' ((hS.hasSum.tendsto_sum_nat).pow 2) hfin

/-- The optimal level distribution `p_ℓ = √(V_ℓ/C_ℓ) / ∑_k √(V_k/C_k)` (Giles 2015, §2.2, p. 10). -/
noncomputable def optimalLevelProb (V C : ℕ → ℝ) (ℓ : ℕ) : ℝ :=
  Real.sqrt (V ℓ / C ℓ) / ∑' k, Real.sqrt (V k / C k)

/-- Giles 2015, §2.2, p. 10: the level distribution `p_ℓ ∝ √(V_ℓ/C_ℓ)` attains the bound of
`randomised_optimal_p`: `(∑ p_ℓ⁻¹ V_ℓ)(∑ p_ℓ C_ℓ) = (∑ √(V_ℓ C_ℓ))²`. -/
theorem randomised_optimal_p_eq {V C : ℕ → ℝ} (hV : ∀ ℓ, 0 < V ℓ) (hC : ∀ ℓ, 0 < C ℓ)
    (hS : Summable fun ℓ => Real.sqrt (V ℓ * C ℓ)) (hZ : Summable fun ℓ => Real.sqrt (V ℓ / C ℓ)) :
    (∀ ℓ, 0 < optimalLevelProb V C ℓ) ∧ HasSum (optimalLevelProb V C) 1 ∧
      Summable (fun ℓ => V ℓ / optimalLevelProb V C ℓ) ∧
      Summable (fun ℓ => optimalLevelProb V C ℓ * C ℓ) ∧
      (∑' ℓ, V ℓ / optimalLevelProb V C ℓ) * (∑' ℓ, optimalLevelProb V C ℓ * C ℓ) =
        (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2 := by
  set Z := ∑' k, Real.sqrt (V k / C k) with hZ_def
  have hq : ∀ ℓ, 0 < Real.sqrt (V ℓ / C ℓ) := fun ℓ => Real.sqrt_pos.2 (div_pos (hV ℓ) (hC ℓ))
  have hZ0 : 0 < Z := hZ.tsum_pos (fun ℓ => (hq ℓ).le) 0 (hq 0)
  have hpos : ∀ ℓ, 0 < optimalLevelProb V C ℓ := fun ℓ => div_pos (hq ℓ) hZ0
  have e1 : ∀ ℓ, V ℓ / optimalLevelProb V C ℓ = Z * Real.sqrt (V ℓ * C ℓ) := fun ℓ => by
    unfold optimalLevelProb
    rw [← hZ_def, div_div_eq_mul_div, div_eq_iff (hq ℓ).ne']
    have hid := sqrt_div_mul_sqrt_mul (hV ℓ).le (hC ℓ)
    linear_combination (-Z) * hid
  have e2 : ∀ ℓ, optimalLevelProb V C ℓ * C ℓ = Real.sqrt (V ℓ * C ℓ) / Z := fun ℓ => by
    unfold optimalLevelProb
    rw [← hZ_def, ← sqrt_div_mul (hV ℓ).le (hC ℓ)]
    ring
  refine ⟨hpos, ?_, (hS.mul_left Z).congr fun ℓ => (e1 ℓ).symm,
    (hS.div_const Z).congr fun ℓ => (e2 ℓ).symm, ?_⟩
  · have h := hZ.hasSum.div_const Z
    rw [← hZ_def, div_self hZ0.ne'] at h
    exact h
  · simp_rw [e1, e2]
    rw [tsum_mul_left, tsum_div_const]
    field_simp [hZ0.ne']

/-- **The sample count and the cost with the optimal level distribution** (Giles 2015, §2.2, p. 10:
"If `E_ℓ² ≪ V_ℓ`, then the condition that the variance of the estimator is approximately equal to
`ε²` gives `N ≈ ε⁻² ∑_ℓ V_ℓ/p_ℓ ≈ ε⁻² (∑_ℓ √(V_ℓ C_ℓ))(∑_ℓ' √(V_ℓ'/C_ℓ'))` and therefore the total
cost is `C = N ∑_ℓ p_ℓ C_ℓ ≈ ε⁻² (∑_ℓ √(V_ℓ C_ℓ))²`").  For `p = optimalLevelProb V C` the
identities are exact: `∑ V_ℓ/p_ℓ = (∑ √(V_ℓ C_ℓ))(∑ √(V_ℓ/C_ℓ))`, the expected cost of one sample is
`∑ p_ℓ C_ℓ = (∑ √(V_ℓ C_ℓ)) / (∑ √(V_ℓ/C_ℓ))`, and `ε⁻² (∑ V_ℓ/p_ℓ)(∑ p_ℓ C_ℓ) = ε⁻² (∑ √(V_ℓ C_ℓ))²`.
The approximations `≈` of the paper are the neglect of `E_ℓ²` in the variance
(`singleTermN_mean_variance`) and the rounding of `N` to an integer. -/
theorem randomised_optimal_cost {V C : ℕ → ℝ} (hV : ∀ ℓ, 0 < V ℓ) (hC : ∀ ℓ, 0 < C ℓ)
    (hS : Summable fun ℓ => Real.sqrt (V ℓ * C ℓ)) (hZ : Summable fun ℓ => Real.sqrt (V ℓ / C ℓ))
    (ε : ℝ) :
    ∑' ℓ, V ℓ / optimalLevelProb V C ℓ =
        (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) * ∑' ℓ, Real.sqrt (V ℓ / C ℓ) ∧
      ∑' ℓ, optimalLevelProb V C ℓ * C ℓ =
        (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) / ∑' ℓ, Real.sqrt (V ℓ / C ℓ) ∧
      (ε ^ 2)⁻¹ * (∑' ℓ, V ℓ / optimalLevelProb V C ℓ) * ∑' ℓ, optimalLevelProb V C ℓ * C ℓ =
        (ε ^ 2)⁻¹ * (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2 := by
  have hprod := (randomised_optimal_p_eq hV hC hS hZ).2.2.2.2
  set Z := ∑' k, Real.sqrt (V k / C k) with hZ_def
  have hq : ∀ ℓ, 0 < Real.sqrt (V ℓ / C ℓ) := fun ℓ => Real.sqrt_pos.2 (div_pos (hV ℓ) (hC ℓ))
  have e1 : ∀ ℓ, V ℓ / optimalLevelProb V C ℓ = Z * Real.sqrt (V ℓ * C ℓ) := fun ℓ => by
    unfold optimalLevelProb
    rw [← hZ_def, div_div_eq_mul_div, div_eq_iff (hq ℓ).ne']
    have hid := sqrt_div_mul_sqrt_mul (hV ℓ).le (hC ℓ)
    linear_combination (-Z) * hid
  have e2 : ∀ ℓ, optimalLevelProb V C ℓ * C ℓ = Real.sqrt (V ℓ * C ℓ) / Z := fun ℓ => by
    unfold optimalLevelProb
    rw [← hZ_def, ← sqrt_div_mul (hV ℓ).le (hC ℓ)]
    ring
  have h1 : ∑' ℓ, V ℓ / optimalLevelProb V C ℓ = (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) * Z := by
    simp_rw [e1]
    rw [tsum_mul_left]
    exact mul_comm _ _
  have h2 : ∑' ℓ, optimalLevelProb V C ℓ * C ℓ = (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) / Z := by
    simp_rw [e2]
    rw [tsum_div_const]
  exact ⟨h1, h2, by rw [mul_assoc, hprod]⟩

/-- **The optimal level distribution** (Giles 2015, §2.2, p. 10: "the optimal choice for `p_ℓ` is
`p_ℓ = √(V_ℓ/C_ℓ) (∑ √(V_ℓ'/C_ℓ'))⁻¹`").  For positive `V_ℓ, C_ℓ` with `∑ √(V_ℓ C_ℓ) < ∞` and
`∑ √(V_ℓ/C_ℓ) < ∞` (the paper's proviso is `β > γ`), the least value of the product
`(∑ p_ℓ⁻¹ V_ℓ)(∑ p_ℓ C_ℓ)` over all probability distributions `p_ℓ > 0` for which both series
converge is `(∑ √(V_ℓ C_ℓ))²`, and it is attained by `optimalLevelProb`. -/
theorem randomised_optimal_p_isLeast {V C : ℕ → ℝ} (hV : ∀ ℓ, 0 < V ℓ) (hC : ∀ ℓ, 0 < C ℓ)
    (hS : Summable fun ℓ => Real.sqrt (V ℓ * C ℓ))
    (hZ : Summable fun ℓ => Real.sqrt (V ℓ / C ℓ)) :
    IsLeast {x | ∃ p : ℕ → ℝ, (∀ ℓ, 0 < p ℓ) ∧ HasSum p 1 ∧ Summable (fun ℓ => V ℓ / p ℓ) ∧
        Summable (fun ℓ => p ℓ * C ℓ) ∧ x = (∑' ℓ, V ℓ / p ℓ) * ∑' ℓ, p ℓ * C ℓ}
      ((∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2) ∧
    (∀ ℓ, 0 < optimalLevelProb V C ℓ) ∧ HasSum (optimalLevelProb V C) 1 ∧
      (∑' ℓ, V ℓ / optimalLevelProb V C ℓ) * (∑' ℓ, optimalLevelProb V C ℓ * C ℓ) =
        (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2 := by
  obtain ⟨hpos, h1, hVs, hCs, heq⟩ := randomised_optimal_p_eq hV hC hS hZ
  refine ⟨⟨⟨optimalLevelProb V C, hpos, h1, hVs, hCs, heq.symm⟩, ?_⟩, hpos, h1, heq⟩
  rintro x ⟨p, hp, -, h1, h2, rfl⟩
  exact (randomised_optimal_p (fun ℓ => (hV ℓ).le) (fun ℓ => (hC ℓ).le) hp h1 h2).2

/-- **Finite variance and finite expected cost with the tightened condition (iii)** (derived from
Giles 2015, §2.2, p. 10, with the second-moment form of (iii) from p. 7; the combined statement is
not stated in the paper).  Suppose the level `K` has the distribution `p_ℓ ∝ 2^{−(β+γ)ℓ/2}` and is
independent of each `P_ℓ − P_{ℓ−1}` and of each level cost `κ_ℓ`; that the `P_ℓ` are measurable
and square-integrable, `P` is integrable, `E[(P_ℓ − P_{ℓ−1})²] ≤ c₂ 2^{−βℓ}`,
`|E[P_ℓ − P]| ≤ c₁ 2^{−αℓ}`, and the cost `κ_ℓ ≥ 0` of a level-`ℓ` sample is measurable and
integrable with `E[κ_ℓ] ≤ c₃ 2^{γℓ}`, with `0 < γ < β` and `α > 0`.  Then one sample of the
single-term estimator is unbiased, `E[Y] = E[P]`, has finite variance, and its cost `κ_K` has
finite expectation `E[κ_K] = ∑_ℓ p_ℓ E[κ_ℓ]`. -/
theorem randomised_mlmc_finite [IsProbabilityMeasure μ] {K : Ω → ℕ} {Pl : ℕ → Ω → ℝ}
    (P : Ω → ℝ) {κ : ℕ → Ω → ℝ} {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hγβ : γ < β)
    (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ)
    (hP : Integrable P μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = geomLevelProb β γ ℓ)
    (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ)
    (h_i : ∀ ℓ : ℕ, |∫ ω, Pl ℓ ω - P ω ∂μ| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, ∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (hκm : ∀ ℓ, Measurable (κ ℓ)) (hκ0 : ∀ ℓ ω, 0 ≤ κ ℓ ω) (hκi : ∀ ℓ, Integrable (κ ℓ) μ)
    (hκind : ∀ ℓ, IndepFun K (κ ℓ) μ)
    (h_iv : ∀ ℓ, ∫ ω, κ ℓ ω ∂μ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    Integrable (singleTerm Pl K (geomLevelProb β γ)) μ ∧
      ∫ ω, singleTerm Pl K (geomLevelProb β γ) ω ∂μ = ∫ ω, P ω ∂μ ∧
      MemLp (singleTerm Pl K (geomLevelProb β γ)) 2 μ ∧
      Integrable (fun ω => κ (K ω) ω) μ ∧
      ∫ ω, κ (K ω) ω ∂μ = ∑' ℓ, geomLevelProb β γ ℓ * ∫ ω, κ ℓ ω ∂μ := by
  have hβγ : 0 < β + γ := by linarith
  have hp0 := geomLevelProb_pos hβγ
  obtain ⟨-, -, hVs, hCs⟩ := randomised_summable (c₂ := c₂) hγ hγβ
    (fun ℓ => integral_nonneg fun ω => sq_nonneg (levelDiff Pl ℓ ω))
    (fun ℓ => integral_nonneg fun ω => hκ0 ℓ ω) h_iii h_iv
  have hsum := summable_abs_of_summable_sq hK hPl hp hp0 hVs
  -- `E[P_L] → E[P]` from condition (i)
  have hconv : Tendsto (fun L => ∫ ω, Pl L ω ∂μ) atTop (𝓝 (∫ ω, P ω ∂μ)) := by
    have hPl1 : ∀ ℓ, Integrable (Pl ℓ) μ := fun ℓ => (hPl ℓ).integrable one_le_two
    have hq : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hlim : Tendsto (fun L : ℕ => c₁ * ((2 : ℝ) ^ (-α)) ^ L) atTop (𝓝 (c₁ * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_pos_of_pos two_pos _).le hq).const_mul c₁
    rw [mul_zero] at hlim
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun L => norm_nonneg _) (fun L => ?_)
      hlim)
    rw [Real.norm_eq_abs, ← integral_sub (hPl1 L) hP, ← two_rpow_mul_nat, neg_mul]
    exact h_i L
  obtain ⟨hint, hmean⟩ := singleTerm_unbiased P hP hK hPlm (fun ℓ => (hPl ℓ).integrable one_le_two)
    hp hp0 hind hsum hconv
  obtain ⟨hcostiff, hcosteq⟩ := integral_cost_level hK hκm hκ0 hκi hκind hp
  exact ⟨hint, hmean, (singleTerm_variance hK hPlm hPl hp hp0 hind hVs).1, hcostiff.2 hCs,
    hcosteq hCs⟩

/-- **Infinite expected cost when `β ≤ γ`** (Giles 2015, §2.2, p. 10: "for these cases the
estimators constructed by Rhee and Glynn (2013) have infinite expected cost").  If the rates are
attained, `V_ℓ = V[P_ℓ − P_{ℓ−1}] ≥ c₂ 2^{−βℓ}` and `C_ℓ ≥ c₃ 2^{γℓ}` with `β ≤ γ`, then every
single-term estimator whose sample `Y` has finite variance has infinite expected cost: the cost
`κ_K ≥ 0` of a sample (with `E[κ_ℓ] = C_ℓ`, independent of the level `K`) has
`E[κ_K] = ∫ κ_K dμ = ∞`. -/
theorem randomised_infinite_cost [IsProbabilityMeasure μ] {K : Ω → ℕ} {Pl : ℕ → Ω → ℝ}
    {p : ℕ → ℝ} (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ))
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) (hp0 : ∀ ℓ, 0 < p ℓ)
    (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ) {κ : ℕ → Ω → ℝ} {C : ℕ → ℝ}
    (hκm : ∀ ℓ, Measurable (κ ℓ)) (hκ0 : ∀ ℓ ω, 0 ≤ κ ℓ ω) (hκi : ∀ ℓ, Integrable (κ ℓ) μ)
    (hκind : ∀ ℓ, IndepFun K (κ ℓ) μ) (hC : ∀ ℓ, ∫ ω, κ ℓ ω ∂μ = C ℓ)
    {β γ c₂ c₃ : ℝ} (hβγ : β ≤ γ) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hV : ∀ ℓ : ℕ, c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) ≤ variance (levelDiff Pl ℓ) μ)
    (hCb : ∀ ℓ : ℕ, c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ)) ≤ C ℓ) (hY : MemLp (singleTerm Pl K p) 2 μ) :
    ∫⁻ ω, ENNReal.ofReal (κ (K ω) ω) ∂μ = ⊤ := by
  by_contra hfin
  have hm : Measurable fun ω => κ (K ω) ω := measurable_comp_level hK hκm
  have hcost : Integrable (fun ω => κ (K ω) ω) μ :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun ω => hκ0 (K ω) ω)).2 (lt_top_iff_ne_top.2 hfin)⟩
  exact randomised_not_summable hβγ hc₂ hc₃ hp0 hV hCb
    (randomised_necessary hK hPlm hPl hp hp0 hind hκm hκ0 hκi hκind hC hY hcost)

end MLMC
