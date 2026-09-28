import MlmcLean.MarkovChain
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The limiting distribution of a contracting Markov chain (Giles 2015, §10.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §10.1 "Markov
chains and limiting distributions", p. 61: "the Markov chain `{X_n}` in a metric space with metric
`d` is defined by `X_0 = x`, `X_{n+1} = φ_n(X_n)`, `n ≥ 0`, where `{φ_n}` is a sequence of iid
random functions.  Furthermore, it is assumed that the `φ`'s are contracting on average in the
sense that `sup_{x≠y} E[(d(φ_n(x), φ_n(y))/d(x, y))^{2γ}] < 1` for some `γ ∈ (0, 1)`.  Under these
conditions, it is known that the distribution of `X_n` converges weakly to that of a limit random
variable `X_∞`" (after Glynn and Rhee 2014).

The model is that of `MlmcLean/MarkovChain.lean`: `φ_n = φ(·, ξ_n)` with a jointly measurable
`φ : α × E → α` and independent noises `ξ_n` of law `ν`.  The contraction hypothesis is
`E[d(φ(x, ξ), φ(y, ξ))^p] ≤ ρ d(x, y)^p` for all `x, y`, with `p > 0` (Giles: `p = 2γ`) and
`0 ≤ ρ < 1`; the first step from `x₀` has a finite moment, `E[d(x₀, φ(x₀, ξ))^p] < ∞`; and the
state space `α` is a complete separable metric space.

* `fwdIter`: the chain `X_0 = x₀`, `X_{n+1} = φ(X_n, ξ_n)`.
* `backIter_eq_fwdIter_rev`, `map_backIter_eq_map_fwdIter`: the chain started `n` steps in the
  past (`backIter`, the level samples of Glynn and Rhee) is the forward chain driven by the first
  `n` noises in reverse order, so it has the law of `X_n`: reversing i.i.d. noises does not change
  their joint law (`map_revPerm_infinitePi`).
* `ae_tendsto_backIter`: the chain started in the past converges almost surely as its starting
  time goes to `−∞`: by the contraction `E[d(Z_n, Z_{n+1})^p] ≤ ρ^n c`, so
  `∑_n θ^{−n} d(Z_n, Z_{n+1})^p` has a finite mean for `ρ < θ < 1`, hence is finite almost surely,
  and then `d(Z_n, Z_{n+1}) ≤ S^{1/p} (θ^{1/p})^n` is summable.
* `tendstoInDistribution_fwdIter`: **the distribution of `X_n` converges weakly to that of a
  limit random variable `X_∞`**, the almost sure limit of the chains started in the past.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace MLMC

/-! ### The forward chain and the reversal of the noises -/

section forward

variable {α E : Type*}

/-- **The chain of Giles 2015, §10.1**: `X_0 = x`, `X_{n+1} = φ_n(X_n)` with `φ_n = φ(·, e_n)`. -/
def fwdIter (φ : α → E → α) : ℕ → (ℕ → E) → α → α
  | 0, _, x => x
  | n + 1, e, x => φ (fwdIter φ n e x) (e n)

lemma fwdIter_zero (φ : α → E → α) (e : ℕ → E) (x : α) : fwdIter φ 0 e x = x := rfl

lemma fwdIter_succ (φ : α → E → α) (n : ℕ) (e : ℕ → E) (x : α) :
    fwdIter φ (n + 1) e x = φ (fwdIter φ n e x) (e n) := rfl

/-- The first `n` steps of the chain use only the noises `e_0, …, e_{n−1}`. -/
lemma fwdIter_congr (φ : α → E → α) {n : ℕ} {e e' : ℕ → E} (h : ∀ i < n, e i = e' i) (x : α) :
    fwdIter φ n e x = fwdIter φ n e' x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fwdIter_succ, fwdIter_succ, ih fun i hi => h i (by omega), h n (by omega)]

/-- **The chain started in the past is the forward chain driven by the reversed noises**
(Giles 2015, §10.1): `backIter φ n e x = fwdIter φ n (e_{n−1}, e_{n−2}, …, e_0, …) x`. -/
lemma backIter_eq_fwdIter (φ : α → E → α) (n : ℕ) (e : ℕ → E) (x : α) :
    backIter φ n e x = fwdIter φ n (fun i => e (n - 1 - i)) x := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    rw [backIter_succ, ih, fwdIter_succ, show n + 1 - 1 - n = 0 by omega]
    congr 1
    exact fwdIter_congr φ (e := fun i => e (n - 1 - i + 1)) (e' := fun i => e (n + 1 - 1 - i))
      (fun i hi => show e (n - 1 - i + 1) = e (n + 1 - 1 - i) from congrArg e (by omega)) x

/-- The reversal `i ↦ n − 1 − i` of the first `n` indices (the other indices are fixed). -/
def revFun (n i : ℕ) : ℕ := if i < n then n - 1 - i else i

lemma revFun_involutive (n : ℕ) : Function.Involutive (revFun n) := by
  intro i
  unfold revFun
  split_ifs <;> omega

/-- The reversal of the first `n` indices as a permutation of `ℕ`. -/
def revPerm (n : ℕ) : Equiv.Perm ℕ := Function.Involutive.toPerm (revFun n) (revFun_involutive n)

/-- `backIter φ n e x = fwdIter φ n (e ∘ σ_n) x`, `σ_n` the reversal of the first `n` indices. -/
lemma backIter_eq_fwdIter_rev (φ : α → E → α) (n : ℕ) (e : ℕ → E) (x : α) :
    backIter φ n e x = fwdIter φ n (fun i => e (revPerm n i)) x := by
  rw [backIter_eq_fwdIter]
  exact fwdIter_congr φ (e := fun i => e (n - 1 - i)) (e' := fun i => e (revPerm n i))
    (fun i hi => show e (n - 1 - i) = e (revFun n i) by rw [revFun, if_pos hi]) x

variable [MeasurableSpace E]

/-- **Reversing i.i.d. noises does not change their joint law**: under the product measure
`ν^ℕ`, the reindexed sequence `(e_{σ_n(i)})_i` has law `ν^ℕ`. -/
lemma map_revPerm_infinitePi (ν : Measure E) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν).map (fun e i => e (revPerm n i)) =
      Measure.infinitePi fun _ : ℕ => ν := by
  have h := Measure.infinitePi_map_piCongrLeft (μ := fun _ : ℕ => ν) (revPerm n)
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq] at h
  have e : (fun (e : ℕ → E) (i : ℕ) => e (revPerm n i)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℕ => E) (revPerm n)).symm := by
    funext g i
    rfl
  rw [e]
  exact h.symm

variable [MeasurableSpace α]

/-- The chain after `n` steps is a measurable function of the noises. -/
lemma measurable_fwdIter {φ : α → E → α} (hφm : Measurable fun q : α × E => φ q.1 q.2)
    (n : ℕ) (x : α) : Measurable fun e : ℕ → E => fwdIter φ n e x := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have e : (fun e : ℕ → E => fwdIter φ (n + 1) e x) = fun e => φ (fwdIter φ n e x) (e n) := rfl
    rw [e]
    exact hφm.comp (ih.prodMk (measurable_pi_apply n))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure E}
  {φ : α → E → α} {ξ : ℕ → Ω → E}

/-- **The chain started `n` steps in the past has the law of `X_n`** (Giles 2015, §10.1): for
independent noises `ξ_k` of law `ν`, `backIter φ n ξ x₀` and `fwdIter φ n ξ x₀` have the same
law. -/
theorem map_backIter_eq_map_fwdIter (hφm : Measurable fun q : α × E => φ q.1 q.2)
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν) (n : ℕ)
    (x₀ : α) :
    μ.map (fun ω => backIter φ n (fun k => ξ k ω) x₀) =
      μ.map (fun ω => fwdIter φ n (fun k => ξ k ω) x₀) := by
  have : IsProbabilityMeasure ν := hlaw 0 ▸ Measure.isProbabilityMeasure_map (hξm 0).aemeasurable
  have hΞ : Measurable fun ω (k : ℕ) => ξ k ω := measurable_pi_lambda _ hξm
  have hjoint : μ.map (fun ω (k : ℕ) => ξ k ω) = Measure.infinitePi fun _ : ℕ => ν := by
    rw [hξ.map_fun_eq_infinitePi_map₀ hΞ.aemeasurable]
    simp only [hlaw]
  have hF := measurable_fwdIter hφm n x₀
  have hR : Measurable fun (e : ℕ → E) (i : ℕ) => e (revPerm n i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have eB : (fun ω => backIter φ n (fun k => ξ k ω) x₀) =
      (fun e => fwdIter φ n e x₀) ∘ (fun (e : ℕ → E) (i : ℕ) => e (revPerm n i)) ∘
        fun ω (k : ℕ) => ξ k ω :=
    funext fun ω => backIter_eq_fwdIter_rev φ n _ x₀
  have eF : (fun ω => fwdIter φ n (fun k => ξ k ω) x₀) =
      (fun e => fwdIter φ n e x₀) ∘ fun ω (k : ℕ) => ξ k ω := rfl
  rw [eB, eF, ← Measure.map_map hF (hR.comp hΞ), ← Measure.map_map hR hΞ, hjoint,
    map_revPerm_infinitePi, ← Measure.map_map hF hΞ, hjoint]

end forward

/-! ### Almost sure convergence of the chain started in the past -/

section limit

variable {α E Ω : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [MeasurableSpace E] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ν : Measure E} {φ : α → E → α} {ξ : ℕ → Ω → E}

/-- **One more step in the past moves the chain little** (Giles 2015, §10.1): with the hypotheses
of `lintegral_dist_backIter_le`, `E[d(Z_n, Z_{n+1})^p] ≤ ρ^n E[d(x₀, φ(x₀, ξ))^p]` for the chains
`Z_n` started `n` steps in the past at `x₀`. -/
lemma lintegral_dist_backIter_succ_le (hφm : Measurable fun q : α × E => φ q.1 q.2) {p ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ p) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ p))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν) (x₀ : α)
    (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (dist (backIter φ n (fun k => ξ (k + 0) ω) x₀)
        (backIter φ (n + 1) (fun k => ξ (k + 0) ω) x₀) ^ p) ∂μ ≤
      ENNReal.ofReal ρ ^ n * ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν := by
  have hφx : Measurable fun e : E => φ x₀ e := hφm.comp measurable_prodMk_left
  have hV : Measurable[noiseFrom ξ (0 + n)] fun ω => φ x₀ (ξ (n + 0) ω) :=
    hφx.comp (measurable_noise ξ (by omega : 0 + n ≤ n + 0))
  have h := lintegral_dist_backIter_le hφm hφ hξ hξm hlaw n 0 (U := fun _ => x₀)
    measurable_const hV
  have hlaw' : ∫⁻ ω, ENNReal.ofReal (dist x₀ (φ x₀ (ξ (n + 0) ω)) ^ p) ∂μ =
      ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν := by
    rw [← hlaw (n + 0), lintegral_map _ (hξm (n + 0))]
    exact ((measurable_const.dist hφx).pow_const _).ennreal_ofReal
  rw [← hlaw']
  refine (lintegral_congr fun ω => ?_).trans_le h
  rw [backIter_succ' φ n (fun k => ξ (k + 0) ω) x₀]

/-- **The chain started in the past converges almost surely** (Giles 2015, §10.1, after Glynn and
Rhee 2014).  Let `φ` contract on average, `E[d(φ(x, ξ), φ(y, ξ))^p] ≤ ρ d(x, y)^p` with `p > 0` and
`0 ≤ ρ < 1`, let the noises `ξ_k` be independent with law `ν`, and let
`E[d(x₀, φ(x₀, ξ))^p] < ∞`.  In a complete separable metric space, for almost every `ω` the chains
`Z_n(ω)` started `n` steps in the past at `x₀` converge as `n → ∞`. -/
theorem ae_tendsto_backIter [CompleteSpace α] (hφm : Measurable fun q : α × E => φ q.1 q.2)
    {p ρ : ℝ} (hp : 0 < p) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ p) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ p))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ x, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 x) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 + ρ) / 2 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  have hρθ : ρ < θ := by rw [hθ]; linarith
  have hZm : ∀ n, Measurable fun ω => backIter φ n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_backIter_shift hφm ξ n 0 (U := fun _ => x₀) measurable_const).mono
      (noiseFrom_le hξm _) le_rfl
  have hDm : ∀ n, Measurable fun ω => ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀)
      (backIter φ (n + 1) (fun k => ξ k ω) x₀) ^ p) := fun n =>
    (((hZm n).dist (hZm (n + 1))).pow_const _).ennreal_ofReal
  have hD : ∀ n, ∫⁻ ω, ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀)
      (backIter φ (n + 1) (fun k => ξ k ω) x₀) ^ p) ∂μ ≤
      ENNReal.ofReal ρ ^ n * ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν := by
    intro n
    have h := lintegral_dist_backIter_succ_le hφm hφ hξ hξm hlaw x₀ n
    simp only [add_zero] at h
    exact h
  -- the weighted sum `W = ∑_n θ^{−n} d(Z_n, Z_{n+1})^p` has a finite mean
  have hr1 : ENNReal.ofReal (ρ / θ) < 1 := ENNReal.ofReal_lt_one.2 ((div_lt_one hθ0).2 hρθ)
  have hW : ∫⁻ ω, ∑' n, ENNReal.ofReal θ⁻¹ ^ n *
      ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀)
        (backIter φ (n + 1) (fun k => ξ k ω) x₀) ^ p) ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun n => ((hDm n).const_mul (ENNReal.ofReal θ⁻¹ ^ n)).aemeasurable]
    have hle : ∑' n, ∫⁻ ω, ENNReal.ofReal θ⁻¹ ^ n *
        ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀)
          (backIter φ (n + 1) (fun k => ξ k ω) x₀) ^ p) ∂μ ≤
        (1 - ENNReal.ofReal (ρ / θ))⁻¹ * ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν :=
      calc ∑' n, ∫⁻ ω, ENNReal.ofReal θ⁻¹ ^ n *
            ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀)
              (backIter φ (n + 1) (fun k => ξ k ω) x₀) ^ p) ∂μ
          = ∑' n, ENNReal.ofReal θ⁻¹ ^ n *
              ∫⁻ ω, ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀)
                (backIter φ (n + 1) (fun k => ξ k ω) x₀) ^ p) ∂μ :=
            tsum_congr fun n => lintegral_const_mul _ (hDm n)
        _ ≤ ∑' n, ENNReal.ofReal θ⁻¹ ^ n *
              (ENNReal.ofReal ρ ^ n * ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν) :=
            ENNReal.tsum_le_tsum fun n => mul_le_mul_left' (hD n) _
        _ = ∑' n, ENNReal.ofReal (ρ / θ) ^ n *
              ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν := by
            refine tsum_congr fun n => ?_
            rw [← mul_assoc, ← mul_pow, ← ENNReal.ofReal_mul (inv_nonneg.2 hθ0.le),
              inv_mul_eq_div]
        _ = (1 - ENNReal.ofReal (ρ / θ))⁻¹ * ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν := by
            rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ?_ hc) hle
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr1).ne'
  have hWm : Measurable fun ω => ∑' n, ENNReal.ofReal θ⁻¹ ^ n *
      ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀)
        (backIter φ (n + 1) (fun k => ξ k ω) x₀) ^ p) :=
    Measurable.ennreal_tsum fun n => (hDm n).const_mul _
  filter_upwards [ae_lt_top hWm hW] with ω hω
  -- `d(Z_n, Z_{n+1})^p ≤ θ^n S` with `S = W(ω) < ∞`
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (∑' n, ENNReal.ofReal θ⁻¹ ^ n *
      ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀)
        (backIter φ (n + 1) (fun k => ξ k ω) x₀) ^ p)).toReal := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact ENNReal.toReal_nonneg
  have hbound : ∀ n, dist (backIter φ n (fun k => ξ k ω) x₀)
      (backIter φ (n + 1) (fun k => ξ k ω) x₀) ≤ (θ ^ p⁻¹) ^ n * S ^ p⁻¹ := by
    intro n
    have h1 := ENNReal.le_tsum (f := fun n => ENNReal.ofReal θ⁻¹ ^ n *
      ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀)
        (backIter φ (n + 1) (fun k => ξ k ω) x₀) ^ p)) n
    rw [← ENNReal.ofReal_pow (inv_nonneg.2 hθ0.le),
      ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hθ0.le) n),
      ENNReal.ofReal_le_iff_le_toReal hω.ne, ← hS] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hθ0.le n)
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hθ0.ne', one_pow, one_mul] at h2
    have hd0 : 0 ≤ dist (backIter φ n (fun k => ξ k ω) x₀)
        (backIter φ (n + 1) (fun k => ξ k ω) x₀) := dist_nonneg
    calc dist (backIter φ n (fun k => ξ k ω) x₀) (backIter φ (n + 1) (fun k => ξ k ω) x₀)
        = (dist (backIter φ n (fun k => ξ k ω) x₀)
            (backIter φ (n + 1) (fun k => ξ k ω) x₀) ^ p) ^ p⁻¹ :=
          (Real.rpow_rpow_inv hd0 hp.ne').symm
      _ ≤ (θ ^ n * S) ^ p⁻¹ :=
          Real.rpow_le_rpow (Real.rpow_nonneg hd0 _) h2 (inv_nonneg.2 hp.le)
      _ = (θ ^ p⁻¹) ^ n * S ^ p⁻¹ := by
          rw [Real.mul_rpow (pow_nonneg hθ0.le n) hS0, Real.rpow_pow_comm hθ0.le]
  have hsum : Summable fun n => dist (backIter φ n (fun k => ξ k ω) x₀)
      (backIter φ (n + 1) (fun k => ξ k ω) x₀) :=
    Summable.of_nonneg_of_le (fun n => dist_nonneg) hbound
      ((summable_geometric_of_lt_one (Real.rpow_nonneg hθ0.le _)
        (Real.rpow_lt_one hθ0.le hθ1 (inv_pos.2 hp))).mul_right _)
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)

/-- **The distribution of the chain converges weakly** (Giles 2015, §10.1, p. 61: "Under these
conditions, it is known that the distribution of `X_n` converges weakly to that of a limit random
variable `X_∞`").  Let `φ` contract on average, `E[d(φ(x, ξ), φ(y, ξ))^p] ≤ ρ d(x, y)^p` with
`p > 0` (`p = 2γ` in the paper) and `0 ≤ ρ < 1`, let the noises `ξ_k` be independent with law `ν`,
and let `E[d(x₀, φ(x₀, ξ))^p] < ∞`, in a complete separable metric space.  Then there is a random
variable `X_∞` such that the chains started `n` steps in the past converge to `X_∞` almost surely,
and the chain `X_0 = x₀`, `X_{n+1} = φ(X_n, ξ_n)` converges to `X_∞` in distribution. -/
theorem tendstoInDistribution_fwdIter [CompleteSpace α]
    (hφm : Measurable fun q : α × E => φ q.1 q.2) {p ρ : ℝ} (hp : 0 < p) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ p) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ p))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν ≠ ∞) :
    ∃ X : Ω → α, AEMeasurable X μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω))) ∧
      TendstoInDistribution (fun n ω => fwdIter φ n (fun k => ξ k ω) x₀) atTop X
        (fun _ => μ) μ := by
  have : Nonempty α := ⟨x₀⟩
  have hae := ae_tendsto_backIter hφm hp hρ0 hρ1 hφ hξ hξm hlaw x₀ hc
  have hZm : ∀ n, Measurable fun ω => backIter φ n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_backIter_shift hφm ξ n 0 (U := fun _ => x₀) measurable_const).mono
      (noiseFrom_le hξm _) le_rfl
  have hFm : ∀ n, Measurable fun ω => fwdIter φ n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_fwdIter hφm n x₀).comp (measurable_pi_lambda _ hξm)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop
      (𝓝 (limUnder atTop fun n => backIter φ n (fun k => ξ k ω) x₀)) :=
    hae.mono fun ω hω => tendsto_nhds_limUnder hω
  have hXm : AEMeasurable (fun ω => limUnder atTop fun n => backIter φ n (fun k => ξ k ω) x₀) μ :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hZm n).aemeasurable) hlim
  refine ⟨fun ω => limUnder atTop fun n => backIter φ n (fun k => ξ k ω) x₀, hXm, hlim, ?_⟩
  have hZ := tendstoInDistribution_of_ae_tendsto (fun n => (hZm n).aemeasurable) hXm hlim
  exact ⟨fun n => (hFm n).aemeasurable, hXm, hZ.tendsto.congr fun n =>
    Subtype.ext (map_backIter_eq_map_fwdIter hφm hξ hξm hlaw n x₀)⟩

end limit

end MLMC
