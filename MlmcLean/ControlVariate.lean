import MlmcLean.Estimator
import MlmcLean.StandardEstimator
import Mathlib.Probability.Moments.Covariance

/-!
# Monte Carlo, control variates and the cost of MLMC (Giles 2015, §1.1–§1.3)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §1.1 (p. 2),
§1.2 (p. 3) and §1.3 (p. 4) of the author's version.

* **§1.1.** "A simple Monte Carlo estimate is just an average of values `P(ω)` for `N` independent
  samples … `N⁻¹ ∑_{n=1}^{N} P(ω⁽ⁿ⁾)`.  The variance of this estimate is `N⁻¹V[P]`, so the r.m.s.
  error is `O(N^{−1/2})` and an accuracy of `ε` requires `N = O(ε⁻²)` samples."  `mc_estimate`
  proves the exact form: the estimate is unbiased with variance and mean-square error `V[P]/N`,
  and its r.m.s. error is at most `ε` exactly when `N ≥ ε⁻² V[P]`.
* **§1.2.** "We can use the following unbiased estimator for `E[f]` based on `N` independent
  samples `ω⁽ⁿ⁾`: `N⁻¹ ∑_{n=1}^{N} {f(ω⁽ⁿ⁾) − λ (g(ω⁽ⁿ⁾) − E[g])}`.  The optimal value for `λ` is
  `ρ √(V[f]/V[g])`, where `ρ` is the correlation between `f` and `g`, and the variance of the
  control variate estimator is reduced by factor `1 − ρ²` compared to the standard estimator"
  (`controlVariate_mean`, `controlVariate_variance`, `controlVariate_optimal`,
  `controlVariate_estimator`).  The two-level estimator that follows in §1.2 is the case `L = 1`
  of (2.2) (`mlmcEstimator_mean_variance`, `twoLevel_optimal_ratio`).
* **§1.3.** After (1.1): "If the product `V_ℓ C_ℓ` increases with level … then we have
  `C ≈ ε⁻² V_L C_L`, whereas if it decreases … then `C ≈ ε⁻² V₀ C₀`", and "if the product
  `V_ℓ C_ℓ` does not vary with level, then the total cost is `ε⁻² L² V₀ C₀`".  With levels
  `0, …, L` the exact cost (1.1) in the last case is `ε⁻² (L+1)² V₀ C₀`
  (`optimal_cost_const_product`); for geometric growth or decay of `√(V_ℓ C_ℓ)` the cost (1.1)
  is within a constant factor of `ε⁻² V_L C_L` or `ε⁻² V₀ C₀` (`optimal_cost_increasing`,
  `optimal_cost_decreasing`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### §1.1: plain Monte Carlo -/

section mc

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω}

/-- **Plain Monte Carlo** (Giles 2015, §1.1, p. 2): for `N ≥ 1` independent inputs `ω⁽ⁿ⁾` with
law `ν` and a square-integrable `P`, the estimate `N⁻¹ ∑_{n<N} P(ω⁽ⁿ⁾)` has mean `E[P]`, variance
`N⁻¹ V[P]` and mean-square error `E[(N⁻¹ ∑ P(ω⁽ⁿ⁾) − E[P])²] = N⁻¹ V[P]`; hence its r.m.s. error is
at most `ε > 0` if and only if `N ≥ ε⁻² V[P]` ("the r.m.s. error is `O(N^{−1/2})` and an accuracy
of `ε` requires `N = O(ε⁻²)` samples"). -/
theorem mc_estimate [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {P : Ω₀ → ℝ}
    (hPm : Measurable P) (hP : MemLp P 2 ν) {N : ℕ} (hN : 0 < N) :
    μ[fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x)] = ∫ y, P y ∂ν ∧
      variance (fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x)) μ = variance P ν / N ∧
      μ[fun x => ((N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x) - ∫ y, P y ∂ν) ^ 2] =
        variance P ν / N ∧
      ∀ ε : ℝ, 0 < ε →
        (Real.sqrt (μ[fun x => ((N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x) - ∫ y, P y ∂ν) ^ 2]) ≤ ε ↔
          variance P ν / ε ^ 2 ≤ N) := by
  -- the law `ν` of the inputs is a probability measure, as the image of `μ`
  haveI : IsProbabilityMeasure ν := by
    rw [← (hω 0).map_eq]
    exact Measure.isProbabilityMeasure_map (hω 0).measurable.aemeasurable
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hPi : Integrable P ν := hP.integrable one_le_two
  have hterm : ∀ n, MemLp (fun x => P (ω n x)) 2 μ := fun n => hP.comp_measurePreserving (hω n)
  have hmem : MemLp (fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x)) 2 μ :=
    (memLp_finsetSum _ fun n _ => hterm n).const_mul _
  have hmean : μ[fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x)] = ∫ y, P y ∂ν := by
    have hint : ∀ n, Integrable (fun x => P (ω n x)) μ := fun n =>
      (hterm n).integrable one_le_two
    have h1 : ∀ n, ∫ x, P (ω n x) ∂μ = ∫ y, P y ∂ν := fun n =>
      integral_comp_of_measurePreserving (hω n) hPi.aestronglyMeasurable
    rw [integral_const_mul, integral_finsetSum _ fun n _ => hint n]
    simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
  have hX : iIndepFun (fun n => P ∘ ω n) μ := hind.comp (fun _ => P) (fun _ => hPm)
  have hvar : variance (fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x)) μ = variance P ν / N :=
    variance_sample_mean (fun n x => P (ω n x)) N hN _ hterm
      (fun n => (hω n).variance_fun_comp hPm.aemeasurable) (fun a _ b _ hab => hX.indepFun hab)
  have hmse : μ[fun x => ((N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x) - ∫ y, P y ∂ν) ^ 2] =
      variance P ν / N := by
    rw [mse_eq_variance_add_sq_bias hmem (∫ y, P y ∂ν), hvar, hmean, sub_self]
    ring
  refine ⟨hmean, hvar, hmse, fun ε hε => ?_⟩
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  rw [hmse, Real.sqrt_le_left hε.le, div_le_iff₀ hNpos, div_le_iff₀ hε2, mul_comm]

end mc

/-! ### §1.2: control variates -/

section corr

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The correlation `ρ = Cov[f, g] / √(V[f] V[g])` of two real random variables (Giles 2015,
§1.2, p. 3). -/
noncomputable def correlation (f g : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  covariance f g μ / Real.sqrt (variance f μ * variance g μ)

end corr

section cv

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {f g : Ω → ℝ}

/-- A control variate does not change the mean (Giles 2015, §1.2, p. 3): for integrable `f`, `g`
and every `λ`, `E[f − λ (g − E[g])] = E[f]`. -/
theorem controlVariate_mean (hf : Integrable f μ) (hg : Integrable g μ) (lam : ℝ) :
    μ[fun ω => f ω - lam * (g ω - μ[g])] = μ[f] := by
  have h1 : Integrable (fun ω => lam * (g ω - μ[g])) μ :=
    (hg.sub (integrable_const _)).const_mul lam
  rw [integral_sub hf h1, integral_const_mul, integral_sub hg (integrable_const _),
    integral_const]
  simp

/-- The variance of a control-variate sample (Giles 2015, §1.2, p. 3):
`V[f − λ (g − E[g])] = V[f] − 2λ Cov[f, g] + λ² V[g]`. -/
theorem controlVariate_variance (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (lam : ℝ) :
    variance (fun ω => f ω - lam * (g ω - μ[g])) μ =
      variance f μ - 2 * lam * covariance f g μ + lam ^ 2 * variance g μ := by
  have hgl : MemLp (fun ω => lam * g ω) 2 μ := hg.const_mul lam
  have hm : AEStronglyMeasurable (fun ω => f ω - lam * g ω) μ :=
    hf.aestronglyMeasurable.sub hgl.aestronglyMeasurable
  have hfun : (fun ω => f ω - lam * (g ω - μ[g])) = fun ω => f ω - lam * g ω + lam * μ[g] := by
    ext ω
    ring
  rw [hfun, variance_add_const hm, variance_fun_sub hf hgl, covariance_const_mul_right,
    variance_const_mul]
  ring

/-- **The optimal control variate** (Giles 2015, §1.2, p. 3): "The optimal value for `λ` is
`ρ √(V[f]/V[g])`, where `ρ` is the correlation between `f` and `g`, and the variance of the control
variate estimator is reduced by factor `1 − ρ²` compared to the standard estimator."  For
square-integrable `f`, `g` with `V[f], V[g] > 0`, the least value of `V[f − λ (g − E[g])]` over
`λ ∈ ℝ` is `(1 − ρ²) V[f]`, and it is attained exactly at `λ = ρ √(V[f]/V[g])`. -/
theorem controlVariate_optimal (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hVf : 0 < variance f μ) (hVg : 0 < variance g μ) :
    IsLeast (Set.range fun lam : ℝ => variance (fun ω => f ω - lam * (g ω - μ[g])) μ)
        ((1 - correlation f g μ ^ 2) * variance f μ) ∧
      ∀ lam : ℝ, variance (fun ω => f ω - lam * (g ω - μ[g])) μ =
          (1 - correlation f g μ ^ 2) * variance f μ ↔
        lam = correlation f g μ * Real.sqrt (variance f μ / variance g μ) := by
  simp only [controlVariate_variance hf hg, correlation]
  generalize variance f μ = Vf at hVf ⊢
  generalize variance g μ = Vg at hVg ⊢
  generalize covariance f g μ = K
  -- write `Cov[f, g] = t V[g]`; the optimal `λ` is `t`
  obtain ⟨t, rfl⟩ : ∃ t, K = t * Vg := ⟨K / Vg, (div_mul_cancel₀ K hVg.ne').symm⟩
  have hsf : 0 < Real.sqrt Vf := Real.sqrt_pos.2 hVf
  have hsg : 0 < Real.sqrt Vg := Real.sqrt_pos.2 hVg
  have hρ : t * Vg / Real.sqrt (Vf * Vg) * Real.sqrt (Vf / Vg) = t := by
    rw [Real.sqrt_mul hVf.le, Real.sqrt_div hVf.le, div_mul_div_comm,
      div_eq_iff (mul_pos (mul_pos hsf hsg) hsg).ne', mul_assoc (Real.sqrt Vf),
      Real.mul_self_sqrt hVg.le]
    ring
  have hmin : (1 - (t * Vg / Real.sqrt (Vf * Vg)) ^ 2) * Vf = Vf - t ^ 2 * Vg := by
    rw [div_pow, Real.sq_sqrt (mul_nonneg hVf.le hVg.le), sub_mul, one_mul]
    congr 1
    rw [div_mul_eq_mul_div, div_eq_iff (mul_pos hVf hVg).ne']
    ring
  have key : ∀ lam : ℝ, Vf - 2 * lam * (t * Vg) + lam ^ 2 * Vg =
      Vf - t ^ 2 * Vg + Vg * (lam - t) ^ 2 := fun lam => by ring
  rw [hρ, hmin]
  simp only [key]
  refine ⟨⟨⟨t, by simp⟩, ?_⟩, fun lam => ⟨fun h => ?_, fun h => by rw [h]; simp⟩⟩
  · rintro v ⟨lam, rfl⟩
    show Vf - t ^ 2 * Vg ≤ Vf - t ^ 2 * Vg + Vg * (lam - t) ^ 2
    have := mul_nonneg hVg.le (sq_nonneg (lam - t))
    linarith
  · have h2 : Vg * (lam - t) ^ 2 = 0 := by linarith
    have h3 : (lam - t) ^ 2 = 0 := (mul_eq_zero.1 h2).resolve_left hVg.ne'
    have h4 : lam - t = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h3
    linarith

end cv

section cvEstimator

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω}

/-- **The control-variate estimator** (Giles 2015, §1.2, p. 3): for `N ≥ 1` independent inputs
`ω⁽ⁿ⁾` with law `ν`, the estimator `N⁻¹ ∑_{n<N} {f(ω⁽ⁿ⁾) − λ (g(ω⁽ⁿ⁾) − E[g])}` is unbiased for
`E[f]` and has variance `N⁻¹ V[f − λ (g − E[g])]`; for `V[f], V[g] > 0` and the optimal
`λ = ρ √(V[f]/V[g])` this variance is `1 − ρ²` times the variance of the standard estimator
`N⁻¹ ∑_{n<N} f(ω⁽ⁿ⁾)`. -/
theorem controlVariate_estimator [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {f g : Ω₀ → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    {N : ℕ} (hN : 0 < N) (lam : ℝ) :
    μ[fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, (f (ω n x) - lam * (g (ω n x) - ∫ z, g z ∂ν))] =
        ∫ y, f y ∂ν ∧
      variance (fun x => (N : ℝ)⁻¹ *
          ∑ n ∈ range N, (f (ω n x) - lam * (g (ω n x) - ∫ z, g z ∂ν))) μ =
        variance (fun y => f y - lam * (g y - ∫ z, g z ∂ν)) ν / N ∧
      (0 < variance f ν → 0 < variance g ν →
        lam = correlation f g ν * Real.sqrt (variance f ν / variance g ν) →
        variance (fun x => (N : ℝ)⁻¹ *
            ∑ n ∈ range N, (f (ω n x) - lam * (g (ω n x) - ∫ z, g z ∂ν))) μ =
          (1 - correlation f g ν ^ 2) *
            variance (fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, f (ω n x)) μ) := by
  haveI : IsProbabilityMeasure ν := by
    rw [← (hω 0).map_eq]
    exact Measure.isProbabilityMeasure_map (hω 0).measurable.aemeasurable
  -- the control-variate sample `h = f − λ (g − E[g])` as a single random variable
  have hhm : Measurable fun y => f y - lam * (g y - ∫ z, g z ∂ν) :=
    hfm.sub ((hgm.sub measurable_const).const_mul lam)
  have hh : MemLp (fun y => f y - lam * (g y - ∫ z, g z ∂ν)) 2 ν :=
    hf.sub ((hg.sub (memLp_const _)).const_mul lam)
  obtain ⟨hmean, hvar, -, -⟩ := mc_estimate ω hω hind hhm hh hN
  obtain ⟨-, hvarf, -, -⟩ := mc_estimate ω hω hind hfm hf hN
  refine ⟨?_, hvar, fun hVf hVg hlam => ?_⟩
  · rw [hmean]
    exact controlVariate_mean (hf.integrable one_le_two) (hg.integrable one_le_two) lam
  · rw [hvar, hvarf, ((controlVariate_optimal hf hg hVf hVg).2 lam).2 hlam]
    ring

end cvEstimator

/-! ### §1.3: the cost (1.1) when `V_ℓ C_ℓ` is constant, increasing or decreasing -/

/-- Giles 2015, §1.3, p. 4: "If the product `V_ℓ C_ℓ` does not vary with level, then the total cost
is `ε⁻² L² V₀ C₀`."  With levels `0, …, L` the cost (1.1), `τ⁻¹ (∑_{ℓ=0}^{L} √(V_ℓ C_ℓ))²`
(`τ = ε²`), is exactly `τ⁻¹ (L+1)² V₀ C₀`; the paper's `L²` is its leading order. -/
theorem optimal_cost_const_product {V C : ℕ → ℝ} (L : ℕ) (τ : ℝ) (hV0 : 0 ≤ V 0)
    (hC0 : 0 ≤ C 0) (h : ∀ ℓ ≤ L, V ℓ * C ℓ = V 0 * C 0) :
    τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 = τ⁻¹ * (L + 1) ^ 2 * (V 0 * C 0) := by
  have hsum : ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) =
      ∑ _ℓ ∈ range (L + 1), Real.sqrt (V 0 * C 0) :=
    Finset.sum_congr rfl fun ℓ hℓ => by rw [h ℓ (Nat.le_of_lt_succ (Finset.mem_range.1 hℓ))]
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_pow,
    Real.sq_sqrt (mul_nonneg hV0 hC0)]
  push_cast
  ring

-- a sum dominated by its last term: `(r − 1) ∑_{ℓ ≤ L} s_ℓ ≤ r s_L` if `s_{ℓ+1} ≥ r s_ℓ ≥ 0`
lemma sum_range_le_of_growth {s : ℕ → ℝ} {r : ℝ} (hr : 1 < r) (hs : ∀ ℓ, 0 ≤ s ℓ)
    (hgrow : ∀ ℓ, r * s ℓ ≤ s (ℓ + 1)) (L : ℕ) :
    (r - 1) * ∑ ℓ ∈ range (L + 1), s ℓ ≤ r * s L := by
  induction L with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    nlinarith [hs 0]
  | succ L ih =>
    rw [Finset.sum_range_succ, mul_add]
    nlinarith [hgrow L, hs (L + 1)]

-- a sum dominated by its first term: `(1 − r) ∑_{ℓ ≤ L} s_ℓ ≤ s_0` if `0 ≤ s_{ℓ+1} ≤ r s_ℓ`
lemma sum_range_le_of_decay {s : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hs : ∀ ℓ, 0 ≤ s ℓ)
    (hdecay : ∀ ℓ, s (ℓ + 1) ≤ r * s ℓ) (L : ℕ) :
    (1 - r) * ∑ ℓ ∈ range (L + 1), s ℓ ≤ s 0 := by
  -- `s_ℓ ≤ r^ℓ s_0`, and `∑_{ℓ ≤ L} r^ℓ ≤ (1 − r)⁻¹`
  have hpow : ∀ ℓ, s ℓ ≤ r ^ ℓ * s 0 := by
    intro ℓ
    induction ℓ with
    | zero => simp
    | succ ℓ ih =>
      calc s (ℓ + 1) ≤ r * s ℓ := hdecay ℓ
        _ ≤ r * (r ^ ℓ * s 0) := mul_le_mul_of_nonneg_left ih hr0
        _ = r ^ (ℓ + 1) * s 0 := by ring
  have hgeom := geom_sum_le_of_lt_one hr0 hr (L + 1)
  have h1r : 0 < 1 - r := by linarith
  calc (1 - r) * ∑ ℓ ∈ range (L + 1), s ℓ ≤ (1 - r) * ∑ ℓ ∈ range (L + 1), r ^ ℓ * s 0 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ => hpow ℓ) h1r.le
    _ = (1 - r) * (∑ ℓ ∈ range (L + 1), r ^ ℓ) * s 0 := by rw [← Finset.sum_mul]; ring
    _ ≤ (1 - r) * (1 - r)⁻¹ * s 0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom h1r.le) (hs 0)
    _ = s 0 := by rw [mul_inv_cancel₀ h1r.ne', one_mul]

/-- Giles 2015, §1.3, p. 4: "If the product increases with level, so that the dominant
contribution to the cost comes from `V_L C_L` then we have `C ≈ ε⁻² V_L C_L`."  Rigorous form: if
`√(V_ℓ C_ℓ)` grows at least geometrically, `√(V_{ℓ+1} C_{ℓ+1}) ≥ r √(V_ℓ C_ℓ)` with `r > 1`, then the
cost (1.1), `τ⁻¹ (∑_{ℓ=0}^{L} √(V_ℓ C_ℓ))²` (`τ = ε²`), lies between `τ⁻¹ V_L C_L` and
`(r/(r−1))² τ⁻¹ V_L C_L`. -/
theorem optimal_cost_increasing {V C : ℕ → ℝ} {r τ : ℝ} (hr : 1 < r) (hτ : 0 < τ)
    (hV : ∀ ℓ, 0 ≤ V ℓ) (hC : ∀ ℓ, 0 ≤ C ℓ)
    (hgrow : ∀ ℓ, r * Real.sqrt (V ℓ * C ℓ) ≤ Real.sqrt (V (ℓ + 1) * C (ℓ + 1))) (L : ℕ) :
    τ⁻¹ * (V L * C L) ≤ τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 ∧
      τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 ≤
        (r / (r - 1)) ^ 2 * (τ⁻¹ * (V L * C L)) := by
  have hs : ∀ ℓ, 0 ≤ Real.sqrt (V ℓ * C ℓ) := fun ℓ => Real.sqrt_nonneg _
  have hsq : Real.sqrt (V L * C L) ^ 2 = V L * C L := Real.sq_sqrt (mul_nonneg (hV L) (hC L))
  have hτi : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  have hr1 : 0 < r - 1 := by linarith
  -- the sum lies between its last term and `r/(r−1)` times it
  have hlow : Real.sqrt (V L * C L) ≤ ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) :=
    Finset.single_le_sum (fun ℓ _ => hs ℓ) (Finset.self_mem_range_succ L)
  have hup : ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) ≤ r / (r - 1) * Real.sqrt (V L * C L) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr1, mul_comm]
    exact sum_range_le_of_growth hr hs hgrow L
  constructor
  · rw [← hsq]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hs L) hlow 2) hτi
  · calc τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2
        ≤ τ⁻¹ * (r / (r - 1) * Real.sqrt (V L * C L)) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Finset.sum_nonneg fun ℓ _ => hs ℓ) hup 2) hτi
      _ = (r / (r - 1)) ^ 2 * (τ⁻¹ * (V L * C L)) := by rw [mul_pow, hsq]; ring

/-- Giles 2015, §1.3, p. 4: "whereas if it decreases and the dominant contribution comes from
`V₀ C₀` then `C ≈ ε⁻² V₀ C₀`."  Rigorous form: if `√(V_ℓ C_ℓ)` decays at least geometrically,
`√(V_{ℓ+1} C_{ℓ+1}) ≤ r √(V_ℓ C_ℓ)` with `0 ≤ r < 1`, then for every `L` the cost (1.1),
`τ⁻¹ (∑_{ℓ=0}^{L} √(V_ℓ C_ℓ))²` (`τ = ε²`), lies between `τ⁻¹ V₀ C₀` and `(1 − r)⁻² τ⁻¹ V₀ C₀`. -/
theorem optimal_cost_decreasing {V C : ℕ → ℝ} {r τ : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hτ : 0 < τ)
    (hV : ∀ ℓ, 0 ≤ V ℓ) (hC : ∀ ℓ, 0 ≤ C ℓ)
    (hdecay : ∀ ℓ, Real.sqrt (V (ℓ + 1) * C (ℓ + 1)) ≤ r * Real.sqrt (V ℓ * C ℓ)) (L : ℕ) :
    τ⁻¹ * (V 0 * C 0) ≤ τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 ∧
      τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 ≤
        ((1 - r)⁻¹) ^ 2 * (τ⁻¹ * (V 0 * C 0)) := by
  have hs : ∀ ℓ, 0 ≤ Real.sqrt (V ℓ * C ℓ) := fun ℓ => Real.sqrt_nonneg _
  have hsq : Real.sqrt (V 0 * C 0) ^ 2 = V 0 * C 0 := Real.sq_sqrt (mul_nonneg (hV 0) (hC 0))
  have hτi : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  have h1r : 0 < 1 - r := by linarith
  -- the sum lies between its first term and `(1 − r)⁻¹` times it
  have hlow : Real.sqrt (V 0 * C 0) ≤ ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) :=
    Finset.single_le_sum (fun ℓ _ => hs ℓ) (Finset.mem_range.2 (Nat.succ_pos L))
  have hup : ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) ≤ (1 - r)⁻¹ * Real.sqrt (V 0 * C 0) := by
    rw [← div_eq_inv_mul, le_div_iff₀ h1r, mul_comm]
    exact sum_range_le_of_decay hr0 hr hs hdecay L
  constructor
  · rw [← hsq]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hs 0) hlow 2) hτi
  · calc τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2
        ≤ τ⁻¹ * ((1 - r)⁻¹ * Real.sqrt (V 0 * C 0)) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Finset.sum_nonneg fun ℓ _ => hs ℓ) hup 2) hτi
      _ = ((1 - r)⁻¹) ^ 2 * (τ⁻¹ * (V 0 * C 0)) := by rw [mul_pow, hsq]; ring

end MLMC
