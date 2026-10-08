import MlmcLean.Randomised
import MlmcLean.LevelDropping
import MlmcLean.MarkovChain
import MlmcLean.SDEExtras

/-!
# Quantitative remarks of Giles (2015): randomised MLMC, level dropping, splitting, Markov chains

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.2 (p. 10),
§2.6 (p. 19), §5.2 (pp. 36–38) and §10.1 (p. 61).  Each remark is stated in the paper with `≈`,
"to leading order" or "it is appropriate"; here it is made precise.

* **§2.2, p. 10** (`singleTerm_variance_le_of_sq_le`, `singleTermN_samples_of_sq_le`): "If
  `E_ℓ² ≪ V_ℓ`, then the condition that the variance of the estimator is approximately equal to
  `ε²` gives `N ≈ ε⁻² ∑_ℓ V_ℓ/p_ℓ`".  If `E_ℓ² ≤ δ V_ℓ` on every level, the variance of one sample
  of the single-term estimator lies between `∑_ℓ V_ℓ/p_ℓ` and `(1 + δ) ∑_ℓ V_ℓ/p_ℓ`, so the number
  of samples needed for variance `ε²` is within the factor `1 + δ` of `ε⁻² ∑_ℓ V_ℓ/p_ℓ`.
* **§2.6, p. 19** (`levelKeep_ratio`, `levelKeep_combined`): at the optimal ratio
  `N_ℓ = N_{ℓ+1} √(V_ℓ/V_{ℓ+1} · C_{ℓ+1}/C_ℓ)` the combined variance of the two estimators that
  involve level `ℓ` is `V_{ℓ+1}/N_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))` and their combined cost
  is `N_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))`.
* **§5.2, pp. 36–38** (`splitting_variance_le`, `splitting_leading_order`): with `M` sub-samples of
  the final Brownian increment, "the variance is the same, to leading order, without any increase
  in the computational cost, again to leading order".  `M ≥ E[v]/(θ V[m])` gives variance at most
  `(1 + θ) V[m]`; and a choice `M(h)` with variance `V[m](1 + o(1))` and cost `h⁻¹(1 + o(1))`
  exists if and only if `E[v]/V[m] = o(h⁻¹)`.
* **§10.1, p. 61** (`markov_linear_levels`): "it is appropriate to choose `N_ℓ` to increase linearly
  with level".  With `N_ℓ = aℓ + b` the multilevel correction variance decays geometrically,
  `V_ℓ ≤ c₂ 2^{−βℓ}` with `β = a log₂(1/ρ)` (condition (iii) of Theorem 1), while the number of
  steps `N_ℓ` is `O(2^{γ'ℓ})` for every `γ' > 0` (condition (iv)).  The paper attributes the decay
  to `N_ℓ − N_{ℓ−1}`; it is in fact exponential in `N_{ℓ−1}` (see the docstring).

**Elsewhere.**  The remark of §5.2, p. 36, that with the conditional expectation "there is zero
variance on the coarsest level … because there is only one timestep on the coarsest level, and
therefore the conditional expectation is taken immediately and every sample gives the same
payoff", is `digital_smoothing_level_zero` in `MlmcLean.SDEDigital`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

namespace MLMC

/-! ### §2.2: the single-term estimator when `E_ℓ² ≪ V_ℓ` -/

section randomised

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {K : Ω → ℕ}
  {Pl : ℕ → Ω → ℝ} {p : ℕ → ℝ}

/-- **The variance of the single-term estimator when `E_ℓ² ≪ V_ℓ`** (Giles 2015, §2.2, p. 10: "If
`E_ℓ² ≪ V_ℓ`, then the condition that the variance of the estimator is approximately equal to `ε²`
gives `N ≈ ε⁻² ∑_ℓ V_ℓ/p_ℓ`").  Under the hypotheses of `singleTerm_variance`, with
`V_ℓ = V[P_ℓ − P_{ℓ−1}]` and `E_ℓ = E[P_ℓ − P_{ℓ−1}]`: if `E_ℓ² ≤ δ V_ℓ` on every level, then one
sample `Y` of the single-term estimator has `∑_ℓ V_ℓ/p_ℓ ≤ V[Y] ≤ (1 + δ) ∑_ℓ V_ℓ/p_ℓ`.  The lower
bound is the paper's "`V[Y] ≥ ∑_ℓ V_ℓ/p_ℓ`, due to Jensen's inequality" (`singleTerm_variance_ge`,
no hypothesis on `E_ℓ`); the upper bound, not stated in the paper, makes its `≈` quantitative. -/
theorem singleTerm_variance_le_of_sq_le (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ))
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) (hp0 : ∀ ℓ, 0 < p ℓ)
    (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ)
    (hsum2 : Summable fun ℓ => (∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ) / p ℓ) {δ : ℝ}
    (hE : ∀ ℓ, (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2 ≤ δ * variance (levelDiff Pl ℓ) μ) :
    ∑' ℓ, variance (levelDiff Pl ℓ) μ / p ℓ ≤ variance (singleTerm Pl K p) μ ∧
      variance (singleTerm Pl K p) μ ≤ (1 + δ) * ∑' ℓ, variance (levelDiff Pl ℓ) μ / p ℓ := by
  have hΔ := memLp_levelDiff hPl
  refine ⟨singleTerm_variance_ge hK hPlm hPl hp hp0 hind hsum2, ?_⟩
  have hVs : Summable fun ℓ => variance (levelDiff Pl ℓ) μ / p ℓ :=
    Summable.of_nonneg_of_le (fun ℓ => div_nonneg (variance_nonneg _ _) (hp0 ℓ).le)
      (fun ℓ => div_le_div_of_nonneg_right
        (by rw [integral_sq_eq (hΔ ℓ)]; exact le_add_of_nonneg_right (sq_nonneg _)) (hp0 ℓ).le)
      hsum2
  have h2 : Summable fun ℓ =>
      (variance (levelDiff Pl ℓ) μ + (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2) / p ℓ :=
    hsum2.congr fun ℓ => by rw [integral_sq_eq (hΔ ℓ)]
  rw [(singleTerm_variance hK hPlm hPl hp hp0 hind hsum2).2]
  calc ∑' ℓ, (variance (levelDiff Pl ℓ) μ + (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2) / p ℓ -
        (∑' ℓ, ∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2
      ≤ ∑' ℓ, (variance (levelDiff Pl ℓ) μ + (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2) / p ℓ :=
        sub_le_self _ (sq_nonneg _)
    _ ≤ ∑' ℓ, (1 + δ) * (variance (levelDiff Pl ℓ) μ / p ℓ) := by
        refine h2.tsum_le_tsum (fun ℓ => ?_) (hVs.mul_left _)
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith [hE ℓ]) (hp0 ℓ).le
    _ = (1 + δ) * ∑' ℓ, variance (levelDiff Pl ℓ) μ / p ℓ := tsum_mul_left

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}

/-- The variance of the single-term estimator with `N ≥ 1` independent samples is `V[Y]/N` (Giles
2015, §2.2; the variance half of `singleTermN_mean_variance`, which does not need the target `P`).
-/
lemma variance_singleTermN (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ))
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) (hp0 : ∀ ℓ, 0 < p ℓ)
    (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ)
    (hsum2 : Summable fun ℓ => (∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ) / p ℓ)
    {ξ : ℕ → Ω' → Ω} (hξ : ∀ n, MeasurePreserving (ξ n) μ' μ) (hξind : iIndepFun ξ μ')
    {N : ℕ} (hN : 0 < N) :
    variance (singleTermN Pl K p ξ N) μ' = variance (singleTerm Pl K p) μ / N := by
  have hY2 : MemLp (singleTerm Pl K p) 2 μ :=
    (singleTerm_variance hK hPlm hPl hp hp0 hind hsum2).1
  have hYm : Measurable (singleTerm Pl K p) :=
    measurable_comp_level hK fun ℓ => (measurable_levelDiff hPlm ℓ).const_mul (p ℓ)⁻¹
  have hX : iIndepFun (fun n => singleTerm Pl K p ∘ ξ n) μ' :=
    hξind.comp (fun _ => singleTerm Pl K p) (fun _ => hYm)
  exact variance_sample_mean (fun n x => singleTerm Pl K p (ξ n x)) N hN _
    (fun n => hY2.comp_measurePreserving (hξ n))
    (fun n => (hξ n).variance_fun_comp hYm.aemeasurable)
    (fun a _ b _ hab => hX.indepFun hab)

/-- **The number of samples of the single-term estimator when `E_ℓ² ≪ V_ℓ`** (Giles 2015, §2.2,
p. 10: "If `E_ℓ² ≪ V_ℓ`, then the condition that the variance of the estimator is approximately
equal to `ε²` gives `N ≈ ε⁻² ∑_{ℓ=0}^∞ V_ℓ/p_ℓ`").  Under the hypotheses of `singleTerm_variance`,
with `N ≥ 1` independent samples `ξ_n` of law `μ` (each a path together with its random level), the
estimator `Y_N` has variance `V[Y]/N`.  If `E_ℓ² ≤ δ V_ℓ` on every level, the number of samples
needed for variance `ε²` is within the factor `1 + δ` of `ε⁻² ∑_ℓ V_ℓ/p_ℓ`: `V[Y_N] ≤ ε²` forces
`N ≥ ε⁻² ∑_ℓ V_ℓ/p_ℓ`, and `N ≥ (1 + δ) ε⁻² ∑_ℓ V_ℓ/p_ℓ` is enough for `V[Y_N] ≤ ε²`.  (The least
real `N` with `V[Y]/N ≤ ε²` is `ε⁻² V[Y]`, which `singleTerm_variance_le_of_sq_le` places between
the two bounds.) -/
theorem singleTermN_samples_of_sq_le (hK : Measurable K) (hPlm : ∀ ℓ, Measurable (Pl ℓ))
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ) (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = p ℓ) (hp0 : ∀ ℓ, 0 < p ℓ)
    (hind : ∀ ℓ, IndepFun K (levelDiff Pl ℓ) μ)
    (hsum2 : Summable fun ℓ => (∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ) / p ℓ) {δ : ℝ}
    (hE : ∀ ℓ, (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2 ≤ δ * variance (levelDiff Pl ℓ) μ)
    {ξ : ℕ → Ω' → Ω} (hξ : ∀ n, MeasurePreserving (ξ n) μ' μ) (hξind : iIndepFun ξ μ')
    {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    variance (singleTermN Pl K p ξ N) μ' = variance (singleTerm Pl K p) μ / N ∧
      (variance (singleTermN Pl K p ξ N) μ' ≤ ε ^ 2 →
        (ε ^ 2)⁻¹ * ∑' ℓ, variance (levelDiff Pl ℓ) μ / p ℓ ≤ N) ∧
      ((1 + δ) * (ε ^ 2)⁻¹ * ∑' ℓ, variance (levelDiff Pl ℓ) μ / p ℓ ≤ N →
        variance (singleTermN Pl K p ξ N) μ' ≤ ε ^ 2) := by
  have hvar := variance_singleTermN hK hPlm hPl hp hp0 hind hsum2 hξ hξind hN
  obtain ⟨hlo, hup⟩ := singleTerm_variance_le_of_sq_le hK hPlm hPl hp hp0 hind hsum2 hE
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  refine ⟨hvar, fun h => ?_, fun h => ?_⟩
  · rw [hvar, div_le_iff₀ hN'] at h
    rw [inv_mul_le_iff₀ hε2]
    linarith
  · rw [hvar, div_le_iff₀ hN']
    have h' := mul_le_mul_of_nonneg_left h hε2.le
    rw [show ε ^ 2 * ((1 + δ) * (ε ^ 2)⁻¹ * ∑' ℓ, variance (levelDiff Pl ℓ) μ / p ℓ) =
      (1 + δ) * ∑' ℓ, variance (levelDiff Pl ℓ) μ / p ℓ by field_simp] at h'
    linarith

end randomised

/-! ### §2.6: keeping level `ℓ` at the optimal ratio of sample numbers -/

section levelKeep

/-- Giles 2015, §2.6, pp. 18–19: "The usual multilevel analysis shows that for optimality
`N_ℓ ∝ √(V_ℓ/C_ℓ)` … Hence we have `N_ℓ = N_{ℓ+1} √(V_ℓ/V_{ℓ+1} · C_{ℓ+1}/C_ℓ)`": sample numbers
`k √(V_ℓ/C_ℓ)` and `k √(V_{ℓ+1}/C_{ℓ+1})` have this ratio. -/
lemma levelKeep_ratio {Vℓ Vℓ₁ Cℓ Cℓ₁ : ℝ} (hV : 0 < Vℓ) (hV₁ : 0 < Vℓ₁) (hC : 0 < Cℓ)
    (hC₁ : 0 < Cℓ₁) (k : ℝ) :
    k * Real.sqrt (Vℓ / Cℓ) =
      k * Real.sqrt (Vℓ₁ / Cℓ₁) * Real.sqrt (Vℓ / Vℓ₁ * (Cℓ₁ / Cℓ)) := by
  rw [mul_assoc, ← Real.sqrt_mul (div_nonneg hV₁.le hC₁.le)]
  congr 2
  field_simp

/-- **Keeping level `ℓ`: the combined variance and the combined cost** (Giles 2015, §2.6, p. 19:
"Hence we have `N_ℓ = N_{ℓ+1} √(V_ℓ/V_{ℓ+1} · C_{ℓ+1}/C_ℓ)`.  The combined variance from the two
terms is `N_ℓ⁻¹ V_ℓ + N_{ℓ+1}⁻¹ V_{ℓ+1} = V_{ℓ+1}/N_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))`, and
the combined cost is `N_ℓ C_ℓ + N_{ℓ+1} C_{ℓ+1} = N_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1}
C_{ℓ+1})))`, and so the product of the combined variance and combined cost is
`V_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`").  The two terms are the estimators of
`E[P_ℓ − P_{ℓ−1}]` and `E[P_{ℓ+1} − P_ℓ]` with `N_ℓ` and `N_{ℓ+1}` samples; `V_ℓ`, `V_{ℓ+1}` are
their per-sample variances and `C_ℓ`, `C_{ℓ+1}` their per-sample costs.  For positive `V`, `C` and
`N_{ℓ+1}`, and `N_ℓ` at the optimal ratio (for instance `N ∝ √(V/C)`, `levelKeep_ratio`), the
three identities hold; the product is the least value of `levelKeep_product`. -/
theorem levelKeep_combined {Vℓ Vℓ₁ Cℓ Cℓ₁ n n₁ : ℝ} (hV : 0 < Vℓ) (hV₁ : 0 < Vℓ₁) (hC : 0 < Cℓ)
    (hC₁ : 0 < Cℓ₁) (hn₁ : 0 < n₁) (hn : n = n₁ * Real.sqrt (Vℓ / Vℓ₁ * (Cℓ₁ / Cℓ))) :
    Vℓ / n + Vℓ₁ / n₁ = Vℓ₁ / n₁ * (1 + Real.sqrt (Vℓ * Cℓ / (Vℓ₁ * Cℓ₁))) ∧
      n * Cℓ + n₁ * Cℓ₁ = n₁ * Cℓ₁ * (1 + Real.sqrt (Vℓ * Cℓ / (Vℓ₁ * Cℓ₁))) ∧
      (Vℓ / n + Vℓ₁ / n₁) * (n * Cℓ + n₁ * Cℓ₁) =
        Vℓ₁ * Cℓ₁ * (1 + Real.sqrt (Vℓ * Cℓ / (Vℓ₁ * Cℓ₁))) ^ 2 := by
  set r := Real.sqrt (Vℓ * Cℓ / (Vℓ₁ * Cℓ₁))
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = Vℓ * Cℓ / (Vℓ₁ * Cℓ₁) := Real.sq_sqrt (by positivity)
  have hs : Real.sqrt (Vℓ / Vℓ₁ * (Cℓ₁ / Cℓ)) = Cℓ₁ / Cℓ * r := by
    refine (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2 ?_
    rw [mul_pow, hr2]
    field_simp
  have hn' : n = n₁ * (Cℓ₁ / Cℓ * r) := by rw [hn, hs]
  have hv : Vℓ / n + Vℓ₁ / n₁ = Vℓ₁ / n₁ * (1 + r) := by
    rw [hn']
    field_simp
    field_simp at hr2
    linear_combination (-1 : ℝ) * hr2
  have hc : n * Cℓ + n₁ * Cℓ₁ = n₁ * Cℓ₁ * (1 + r) := by
    rw [hn']
    field_simp
    ring
  refine ⟨hv, hc, ?_⟩
  rw [hv, hc]
  field_simp

end levelKeep

/-! ### §5.2: splitting -/

section splitting

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {μ : Measure Ω₁}
  [IsProbabilityMeasure μ] {ν : Measure Ω₂} [IsProbabilityMeasure ν]

/-- **Splitting with enough sub-samples** (Giles 2015, §5.2, p. 36: "If the number of sub-samples is
chosen appropriately, the variance is the same, to leading order").  In the setting of
`splitting_mean_variance` (outer sample `x ∼ μ`, independent sub-samples `z_j ∼ ν` of the final
Brownian increment, square-integrable payoff `g(x, z)`), let `m(x) = ∫ g(x, z) dν(z)` be the
conditional expectation, with `V[m] > 0`, and `v(x) = ∫ (g(x, z) − m(x))² dν(z)` the conditional
variance.  For `θ > 0` and `M ≥ E[v]/(θ V[m])` sub-samples, the splitting estimator
`S_M = M⁻¹ ∑_{j<M} g(x, z_j)` has `V[m] ≤ V[S_M] ≤ (1 + θ) V[m]`. -/
theorem splitting_variance_le {g : Ω₁ → Ω₂ → ℝ} (hg : Measurable (Function.uncurry g))
    (hg2 : Integrable (fun q : Ω₁ × Ω₂ => g q.1 q.2 ^ 2) (μ.prod ν)) {M : ℕ} (hM : 0 < M)
    {θ : ℝ} (hθ : 0 < θ) (hVm : 0 < variance (fun x => ∫ z, g x z ∂ν) μ)
    (hMθ : (∫ x, ∫ z, (g x z - ∫ z', g x z' ∂ν) ^ 2 ∂ν ∂μ) /
      (θ * variance (fun x => ∫ z, g x z ∂ν) μ) ≤ M) :
    variance (fun x => ∫ z, g x z ∂ν) μ ≤
        variance (fun q : Ω₁ × (ℕ → Ω₂) => (∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M)
          (μ.prod (Measure.infinitePi fun _ => ν)) ∧
      variance (fun q : Ω₁ × (ℕ → Ω₂) => (∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M)
          (μ.prod (Measure.infinitePi fun _ => ν)) ≤
        (1 + θ) * variance (fun x => ∫ z, g x z ∂ν) μ := by
  rw [(splitting_mean_variance hg hg2 hM).2]
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hv0 : 0 ≤ ∫ x, ∫ z, (g x z - ∫ z', g x z' ∂ν) ^ 2 ∂ν ∂μ :=
    integral_nonneg fun x => integral_nonneg fun z => sq_nonneg _
  refine ⟨le_add_of_nonneg_right (div_nonneg hv0 hM'.le), ?_⟩
  rw [div_le_iff₀ (mul_pos hθ hVm)] at hMθ
  have h : (∫ x, ∫ z, (g x z - ∫ z', g x z' ∂ν) ^ 2 ∂ν ∂μ) / M ≤
      θ * variance (fun x => ∫ z, g x z ∂ν) μ := by
    rw [div_le_iff₀ hM']
    linarith
  linarith

/-- The number of sub-samples (the real analysis behind `splitting_leading_order`): for timesteps
`h_i > 0` with `h_i → 0` and ratios `q_i ≥ 0`, there are sub-sample numbers `M_i ≥ 1` with
`q_i/M_i → 0` and `(M_i − 1) h_i → 0` if and only if `h_i q_i → 0`; one choice is
`M_i = max(⌈√(q_i/h_i)⌉, 1)`. -/
lemma exists_subsamples_iff {ι : Type*} {l : Filter ι} {h q : ι → ℝ} (hh0 : ∀ i, 0 < h i)
    (hh : Tendsto h l (𝓝 0)) (hq : ∀ i, 0 ≤ q i) :
    (∃ M : ι → ℕ, (∀ i, 0 < M i) ∧ Tendsto (fun i => q i / M i) l (𝓝 0) ∧
      Tendsto (fun i => ((M i : ℝ) - 1) * h i) l (𝓝 0)) ↔
      Tendsto (fun i => h i * q i) l (𝓝 0) := by
  constructor
  · rintro ⟨M, hM, h1, h2⟩
    have e : (fun i => h i * q i) = fun i => q i / M i * (((M i : ℝ) - 1) * h i + h i) := by
      funext i
      have : (M i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hM i).ne'
      field_simp
      ring
    rw [e]
    simpa using h1.mul (h2.add hh)
  · intro hr
    have hsq : Tendsto (fun i => Real.sqrt (h i * q i)) l (𝓝 0) := by
      simpa using hr.sqrt
    -- `M_i ≥ 1`, `M_i ≥ √(q_i/h_i)` and `M_i ≤ √(q_i/h_i) + 1`
    have hM1 : ∀ i, (1 : ℝ) ≤ (max ⌈Real.sqrt (q i / h i)⌉₊ 1 : ℕ) := fun i => by
      exact_mod_cast le_max_right _ _
    have hMx : ∀ i, Real.sqrt (q i / h i) ≤ (max ⌈Real.sqrt (q i / h i)⌉₊ 1 : ℕ) := fun i =>
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
    have hMle : ∀ i, ((max ⌈Real.sqrt (q i / h i)⌉₊ 1 : ℕ) : ℝ) ≤ Real.sqrt (q i / h i) + 1 :=
      fun i => by
        rw [Nat.cast_max, Nat.cast_one]
        exact max_le (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
          (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    have hqh : ∀ i, Real.sqrt (q i / h i) ^ 2 = q i / h i := fun i =>
      Real.sq_sqrt (div_nonneg (hq i) (hh0 i).le)
    refine ⟨fun i => max ⌈Real.sqrt (q i / h i)⌉₊ 1, fun i => lt_max_of_lt_right one_pos, ?_, ?_⟩
    · refine squeeze_zero (fun i => div_nonneg (hq i) (by positivity)) (fun i => ?_) hsq
      have hM0 : (0 : ℝ) < (max ⌈Real.sqrt (q i / h i)⌉₊ 1 : ℕ) := by linarith [hM1 i]
      -- `q_i ≤ h_i M_i²`, hence `(q_i/M_i)² ≤ h_i q_i`
      have hq2 : q i ≤ h i * ((max ⌈Real.sqrt (q i / h i)⌉₊ 1 : ℕ) : ℝ) ^ 2 := by
        have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hMx i) 2
        rw [hqh, div_le_iff₀ (hh0 i)] at h2
        linarith
      rw [Real.le_sqrt (div_nonneg (hq i) hM0.le) (mul_nonneg (hh0 i).le (hq i)), div_pow,
        div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hq2 (hq i)]
    · refine squeeze_zero (fun i => mul_nonneg (by linarith [hM1 i]) (hh0 i).le) (fun i => ?_)
        hsq
      have hM0 : (0 : ℝ) ≤ ((max ⌈Real.sqrt (q i / h i)⌉₊ 1 : ℕ) : ℝ) - 1 := by linarith [hM1 i]
      have hMs : ((max ⌈Real.sqrt (q i / h i)⌉₊ 1 : ℕ) : ℝ) - 1 ≤ Real.sqrt (q i / h i) := by
        linarith [hMle i]
      rw [Real.le_sqrt (mul_nonneg hM0 (hh0 i).le) (mul_nonneg (hh0 i).le (hq i)), mul_pow]
      have h2 := pow_le_pow_left₀ hM0 hMs 2
      rw [hqh] at h2
      calc (((max ⌈Real.sqrt (q i / h i)⌉₊ 1 : ℕ) : ℝ) - 1) ^ 2 * h i ^ 2
          ≤ q i / h i * h i ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = h i * q i := by
          field_simp [(hh0 i).ne']

/-- **Splitting to leading order** (Giles 2015, §5.2, p. 36: "one uses a number of samples of
the final Brownian increment to produce an average payoff.  If the number of sub-samples is chosen
appropriately, the variance is the same, to leading order, without any increase in the
computational cost, again to leading order").  Take a family of payoffs `g_i` (e.g. the levels of an
MLMC hierarchy) with timesteps `h_i > 0`, `h_i → 0` along a filter `l`, each in the setting of
`splitting_variance_le` with `V[m_i] > 0`, where `m_i` is the conditional expectation and `v_i` the
conditional variance (the sample spaces are fixed: e.g. `x ∈ ℝ^ℕ` holds all the Brownian
increments before the final one, and the final increment is `√h_i z` with `z ∼ N(0, 1)`).  A path
with `M` sub-samples of the final increment costs `h_i⁻¹ − 1 + M` timesteps, against `h_i⁻¹` for
one path.  Then sub-sample numbers `M_i ≥ 1` exist for which the variance is the same to leading
order, `V[S_{M_i}]/V[m_i] → 1`, and so is the cost, `(h_i⁻¹ − 1 + M_i)/h_i⁻¹ → 1`, if and only if
`E[v_i]/V[m_i] = o(h_i⁻¹)`, i.e. `h_i E[v_i]/V[m_i] → 0`.  The paper leaves this condition
implicit; it is exactly what "chosen appropriately" requires, and then
`M_i = max(⌈√(E[v_i]/(h_i V[m_i]))⌉, 1)` works (`exists_subsamples_iff`). -/
theorem splitting_leading_order {ι : Type*} {l : Filter ι} {h : ι → ℝ} (hh0 : ∀ i, 0 < h i)
    (hh : Tendsto h l (𝓝 0)) {g : ι → Ω₁ → Ω₂ → ℝ}
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (hg2 : ∀ i, Integrable (fun q : Ω₁ × Ω₂ => g i q.1 q.2 ^ 2) (μ.prod ν))
    (hVm : ∀ i, 0 < variance (fun x => ∫ z, g i x z ∂ν) μ) :
    (∃ M : ι → ℕ, (∀ i, 0 < M i) ∧
      Tendsto (fun i => variance (fun q : Ω₁ × (ℕ → Ω₂) =>
          (∑ j ∈ Finset.range (M i), g i q.1 (q.2 j)) / M i)
          (μ.prod (Measure.infinitePi fun _ => ν)) /
        variance (fun x => ∫ z, g i x z ∂ν) μ) l (𝓝 1) ∧
      Tendsto (fun i => ((h i)⁻¹ - 1 + M i) / (h i)⁻¹) l (𝓝 1)) ↔
    Tendsto (fun i => h i * (∫ x, ∫ z, (g i x z - ∫ z', g i x z' ∂ν) ^ 2 ∂ν ∂μ) /
      variance (fun x => ∫ z, g i x z ∂ν) μ) l (𝓝 0) := by
  have hq : ∀ i, 0 ≤ (∫ x, ∫ z, (g i x z - ∫ z', g i x z' ∂ν) ^ 2 ∂ν ∂μ) /
      variance (fun x => ∫ z, g i x z ∂ν) μ := fun i =>
    div_nonneg (integral_nonneg fun x => integral_nonneg fun z => sq_nonneg _) (hVm i).le
  have key := exists_subsamples_iff hh0 hh hq
  -- the variance ratio is `1 + q_i/M_i`, the cost ratio `1 + (M_i − 1) h_i`
  have e1 : ∀ M : ι → ℕ, (∀ i, 0 < M i) → ∀ i,
      variance (fun q : Ω₁ × (ℕ → Ω₂) => (∑ j ∈ Finset.range (M i), g i q.1 (q.2 j)) / M i)
          (μ.prod (Measure.infinitePi fun _ => ν)) / variance (fun x => ∫ z, g i x z ∂ν) μ =
        1 + (∫ x, ∫ z, (g i x z - ∫ z', g i x z' ∂ν) ^ 2 ∂ν ∂μ) /
          variance (fun x => ∫ z, g i x z ∂ν) μ / M i := by
    intro M hM i
    rw [(splitting_mean_variance (hg i) (hg2 i) (hM i)).2]
    field_simp [(hVm i).ne', (Nat.cast_pos.2 (hM i)).ne']
  have e2 : ∀ (M : ι → ℕ) i, ((h i)⁻¹ - 1 + M i) / (h i)⁻¹ = 1 + ((M i : ℝ) - 1) * h i := by
    intro M i
    field_simp [(hh0 i).ne']
    ring
  have one_add : ∀ u : ι → ℝ, Tendsto (fun i => 1 + u i) l (𝓝 1) ↔ Tendsto u l (𝓝 0) := by
    intro u
    constructor
    · intro hu
      simpa using hu.sub_const 1
    · intro hu
      simpa using hu.const_add 1
  rw [show (fun i => h i * (∫ x, ∫ z, (g i x z - ∫ z', g i x z' ∂ν) ^ 2 ∂ν ∂μ) /
      variance (fun x => ∫ z, g i x z ∂ν) μ) = fun i => h i *
        ((∫ x, ∫ z, (g i x z - ∫ z', g i x z' ∂ν) ^ 2 ∂ν ∂μ) /
          variance (fun x => ∫ z, g i x z ∂ν) μ) from funext fun i => mul_div_assoc _ _ _,
    ← key]
  constructor
  · rintro ⟨M, hM, hV, hC⟩
    refine ⟨M, hM, (one_add _).1 ?_, (one_add _).1 ?_⟩
    · simpa only [e1 M hM] using hV
    · simpa only [e2 M] using hC
  · rintro ⟨M, hM, hV, hC⟩
    refine ⟨M, hM, ?_, ?_⟩
    · simp only [e1 M hM]
      exact (one_add _).2 hV
    · simp only [e2 M]
      exact (one_add _).2 hC

end splitting

/-! ### §10.1: starting times that increase linearly with the level -/

section markov

/-- `ρ^{aℓ} = 2^{−βℓ}` with `β = a log₂(1/ρ)`, for `ρ > 0`. -/
lemma pow_mul_eq_two_rpow {ρ : ℝ} (hρ : 0 < ρ) (a ℓ : ℕ) :
    ρ ^ (a * ℓ) = (2 : ℝ) ^ (-((a : ℝ) * Real.logb 2 ρ⁻¹ * ℓ)) := by
  have h2 : (2 : ℝ) ^ Real.logb 2 ρ⁻¹ = ρ⁻¹ :=
    Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.2 hρ)
  rw [show -((a : ℝ) * Real.logb 2 ρ⁻¹ * ℓ) = Real.logb 2 ρ⁻¹ * (-((a * ℓ : ℕ) : ℝ)) by
      push_cast; ring,
    Real.rpow_mul (by norm_num), h2, Real.rpow_neg (inv_nonneg.2 hρ.le), Real.rpow_natCast,
    inv_pow, inv_inv]

/-- A number of steps growing linearly with the level is `O(2^{γℓ})` for every `γ > 0`:
`aℓ + b ≤ (b + a/(γ log 2)) 2^{γℓ}` for `a, b ≥ 0` (from `e^x ≥ 1 + x`). -/
lemma linear_le_two_rpow {a b γ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 < γ) (ℓ : ℕ) :
    a * ℓ + b ≤ (b + a / (γ * Real.log 2)) * (2 : ℝ) ^ (γ * ℓ) := by
  have hl : 0 < γ * Real.log 2 := mul_pos hγ (Real.log_pos one_lt_two)
  have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hc : 0 ≤ a / (γ * Real.log 2) := div_nonneg ha hl.le
  have h1 : 1 + γ * Real.log 2 * ℓ ≤ (2 : ℝ) ^ (γ * ℓ) := by
    rw [Real.rpow_def_of_pos two_pos]
    have h := Real.add_one_le_exp (Real.log 2 * (γ * ℓ))
    linarith
  calc a * ℓ + b = b + a / (γ * Real.log 2) * (γ * Real.log 2 * ℓ) := by
        field_simp
        ring
    _ ≤ (b + a / (γ * Real.log 2)) * (1 + γ * Real.log 2 * ℓ) := by
        nlinarith [mul_nonneg hb (mul_nonneg hl.le hℓ)]
    _ ≤ (b + a / (γ * Real.log 2)) * (2 : ℝ) ^ (γ * ℓ) :=
        mul_le_mul_of_nonneg_left h1 (add_nonneg hb hc)

variable {α E Ω : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [SecondCountableTopology α] [MeasurableSpace E] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ν : Measure E} {φ : α → E → α} {ξ : ℕ → Ω → E}

/-- **Starting times that increase linearly with the level** (Giles 2015, §10.1, p. 61: "This gives
a coupling with a multilevel correction variance which decays as `ℓ` increases.  Because the decay
is exponential in `N_ℓ − N_{ℓ−1}`, it is appropriate to choose `N_ℓ` to increase linearly with
level").  With the hypotheses of `variance_levels_le` and `0 < ρ < 1`, let the level-`ℓ` path start
`N_ℓ = aℓ + b` steps in the past (`a ≥ 1`, `b ≥ 0`), so `P_ℓ = f(X^{(N_ℓ)})`, and let
`c = E[d(x₀, φ(x₀, ξ))^{2γ}] < ∞`.  Then:
* the multilevel corrections `P_ℓ − P_{ℓ−1}` (`P_{−1} = 0`) satisfy condition (iii) of Theorem 1,
  `V_ℓ ≤ c₂ 2^{−βℓ}` for every `ℓ ≥ 0`, with `β = a log₂(1/ρ) > 0` and `c₂ = 4c/((1 − ρ)² ρ^a)`;
* the number of steps `N_ℓ`, and hence a cost per sample `C_ℓ ∝ N_ℓ`, satisfies condition (iv) for
  every rate `γ' > 0`: `N_ℓ ≤ c₃ 2^{γ'ℓ}`.  So (iii) and (iv) hold with `β > γ'`, the favourable
  case `β > γ` of Theorem 1 (its condition (i) on the bias is not considered here).

**Correction to the paper.**  The decay is exponential in `N_{ℓ−1}`, the number of steps that the
two paths share (`variance_levels_le`), not in `N_ℓ − N_{ℓ−1}`: with `N_ℓ` linear in `ℓ` the
difference `N_ℓ − N_{ℓ−1} = a` is constant, and it is `N_{ℓ−1} = a(ℓ − 1) + b` that grows.  For the
paper's example `X_{n+1} = X_n/2 + ξ_n` (`P(ξ_n = 0) = P(ξ_n = 1) = ½`) with `x₀ = 0` and
`f(x) = x`, the level-`ℓ` value is `∑_{k<N_ℓ} ξ_k 2^{−k}`, so
`V[P_ℓ − P_{ℓ−1}] = ¼ ∑_{N_{ℓ−1} ≤ k < N_ℓ} 4^{−k} ≥ 4^{−N_{ℓ−1}}/4` whenever `N_ℓ > N_{ℓ−1}`,
however large `N_ℓ − N_{ℓ−1}` is. -/
theorem markov_linear_levels (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞)
    {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ)
    {a : ℕ} (ha : 0 < a) (b : ℕ) :
    0 < (a : ℝ) * Real.logb 2 ρ⁻¹ ∧
      (∀ ℓ : ℕ, variance (levelDiff (fun n ω => f (backIter φ (a * n + b) (fun k => ξ k ω) x₀))
          ℓ) μ ≤ 4 / (1 - ρ) ^ 2 *
            (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal / ρ ^ a *
          (2 : ℝ) ^ (-((a : ℝ) * Real.logb 2 ρ⁻¹ * ℓ))) ∧
      ∀ γ' : ℝ, 0 < γ' → ∃ c₃ : ℝ, 0 < c₃ ∧
        ∀ ℓ : ℕ, ((a * ℓ + b : ℕ) : ℝ) ≤ c₃ * (2 : ℝ) ^ (γ' * ℓ) := by
  have hK0 : 0 ≤ 4 / (1 - ρ) ^ 2 *
      (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal :=
    mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _)) ENNReal.toReal_nonneg
  have hρa : 0 < ρ ^ a := pow_pos hρ0 a
  have hρa1 : ρ ^ a ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
  have hX : ∀ n, Measurable fun ω => backIter φ n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_backIter_shift hφm ξ n 0 (U := fun _ => x₀) measurable_const).mono
      (noiseFrom_le hξm _) le_rfl
  refine ⟨mul_pos (Nat.cast_pos.2 ha)
    (Real.logb_pos one_lt_two (one_lt_inv₀ hρ0 |>.2 hρ1)), fun ℓ => ?_, fun γ' hγ' => ?_⟩
  · cases ℓ with
    | zero =>
      -- level `0`: `V[P_0] = V[f(X^{(b)}) − f(x₀)] ≤ 4c/(1 − ρ)²`
      have h := (variance_levels_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0.le hρ1 x₀ hc hfm hf
        (Nat.zero_le b)).2
      have e : variance (fun ω => f (backIter φ b (fun k => ξ k ω) x₀) -
          f (backIter φ 0 (fun k => ξ k ω) x₀)) μ =
          variance (fun ω => f (backIter φ b (fun k => ξ k ω) x₀)) μ :=
        variance_sub_const (hfm.comp (hX b)).aestronglyMeasurable (f x₀)
      rw [e, pow_zero, mul_one] at h
      simp only [levelDiff_zero, mul_zero, zero_add, Nat.cast_zero, neg_zero, Real.rpow_zero,
        mul_one]
      exact h.trans (le_div_self hK0 hρa hρa1)
    | succ ℓ =>
      have h := (variance_levels_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0.le hρ1 x₀ hc hfm hf
        (N := a * (ℓ + 1) + b) (N' := a * ℓ + b) (by nlinarith)).2
      rw [levelDiff_succ, ← pow_mul_eq_two_rpow hρ0 a (ℓ + 1)]
      refine h.trans ?_
      have e : ∀ K : ℝ, K / ρ ^ a * (ρ ^ a * ρ ^ (a * ℓ)) = K * ρ ^ (a * ℓ) := fun K => by
        field_simp
      rw [show a * (ℓ + 1) = a + a * ℓ by ring, pow_add, pow_add, e]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (pow_nonneg hρ0.le _) (pow_le_one₀ hρ0.le hρ1.le)) hK0
  · have hl : 0 < γ' * Real.log 2 := mul_pos hγ' (Real.log_pos one_lt_two)
    refine ⟨b + a / (γ' * Real.log 2),
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg b) (div_pos (Nat.cast_pos.2 ha) hl),
      fun ℓ => ?_⟩
    push_cast
    exact linear_le_two_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b) hγ' ℓ

end markov

end MLMC
