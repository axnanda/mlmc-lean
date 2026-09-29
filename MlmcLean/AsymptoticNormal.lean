import MlmcLean.StandardEstimator
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Asymptotic normality of the multilevel estimator and of sums of approximate normals

References: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1, p. 8 of
the author's version; I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations
on FPGAs*, arXiv:2502.07123 (2025), §3.2 "Sum of several variables (Method 2)", p. 5.

**Giles (2015), §2.1, p. 8.** "Collier, Haji-Ali, Nobile, von Schwerin and Tempone (2014) have
developed a modified version of the Theorem. Instead of bounding the Mean Square Error, they prefer
to use the Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence. This exploits the fact that the multilevel correction `Y_ℓ` on each
level is asymptotically Normally-distributed, and therefore so is `Y`."

For the estimator (2.2) built from independent inputs `ω^{(ℓ,n)}` of law `ν` (`levelEstimator`,
`mlmcEstimator` in `MlmcLean/StandardEstimator.lean`), with `V_ℓ = V[P_ℓ − P_{ℓ−1}]`:

* `tendstoInDistribution_levelEstimator`: `√N (Y_ℓ − E[P_ℓ − P_{ℓ−1}]) → N(0, V_ℓ)` in
  distribution as `N → ∞`, whenever `P_ℓ − P_{ℓ−1}` is square integrable (Mathlib's central limit
  theorem `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`);
* `tendstoInDistribution_mlmcEstimator`: for a fixed finest level `L` and `N_ℓ = m_ℓ n` samples
  with fixed integers `m_ℓ ≥ 1`, `√n (Y − E[P_L]) → N(0, ∑_{ℓ=0}^{L} V_ℓ/m_ℓ)` in distribution
  as `n → ∞`.  The characteristic function of the sum over the levels is the product of those of
  the levels (`charFun_map_sum_sum`: all of them are products over the independent samples), each
  factor converges by the level CLT (`tendsto_charFun_levelEstimator`), and Lévy's continuity
  theorem (`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`) concludes.

This is the statement for a fixed number of levels and sample sizes proportional to a common `n`.
Collier et al. let the number of levels grow as the tolerance `ε → 0`, so that the number of
levels, the laws of the corrections and the sample sizes all change together; asymptotic normality
in that regime is a Lindeberg–Feller central limit theorem for triangular arrays, which Mathlib
does not have.

**Haas–Giles (2025), §3.2, p. 5.** "For example take an integer `n` that divides `d` and produce
an approximate random number `X^{(1)}` from the first `d/n` bits of `j`, then `X^{(2)}` from the
next `d/n` bits and so on, where each `X^{(i)}` follows approximately the distribution
`N(0,1/n)`. Then `∑_{i=1}^n X^{(i)}` has approximately the distribution `N(0,1)`."

* `sum_gaussian_hasLaw`: the exact case: if `X^{(1)}, …, X^{(n)}` (`n ≥ 1`) are independent with law
  `N(0, 1/n)`, then `∑ X^{(i)}` has law `N(0, 1)` (`hasLaw_finsetSum_gaussianReal`: a sum of
  independent Gaussians is Gaussian with the summed means and variances);
* `tendstoInDistribution_sum_of_approxNormal`: "approximately" as convergence in distribution for
  fixed `n`: if for every `d` the `X_d^{(1)}, …, X_d^{(n)}` are independent and each converges in
  distribution to `N(0, 1/n)` as `d → ∞`, then `∑_i X_d^{(i)} → N(0, 1)` in distribution;
* `tendstoInDistribution_sum_inv_sqrt_mul`: the central-limit form: for `Z_1, Z_2, …` i.i.d. with
  mean `0` and variance `1` and `X_i^{(n)} = n^{−1/2} Z_i`, `∑_{i=1}^n X_i^{(n)} → N(0, 1)` in
  distribution as `n → ∞`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal

namespace MLMC

/-! ### Gaussian characteristic functions -/

/-- The characteristic function of `N(0, v)`, `v ≥ 0`, is `t ↦ exp(−v t²/2)` (the limit laws of
Giles 2015, §2.1, p. 8). -/
lemma charFun_gaussianReal_zero {v : ℝ} (hv : 0 ≤ v) (t : ℝ) :
    charFun (gaussianReal 0 v.toNNReal) t = Complex.exp ((-(v * t ^ 2 / 2) : ℝ) : ℂ) := by
  rw [charFun_gaussianReal, Real.coe_toNNReal v hv]
  push_cast
  ring_nf

/-- The characteristic function of `N(∑ m_i, ∑ v_i)` is the product of those of the
`N(m_i, v_i)` (used for the sums of Haas–Giles 2025, §3.2, p. 5). -/
lemma charFun_gaussianReal_sum {ι : Type*} (s : Finset ι) (m : ι → ℝ) (v : ι → ℝ≥0) (t : ℝ) :
    charFun (gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i)) t =
      ∏ i ∈ s, charFun (gaussianReal (m i) (v i)) t := by
  simp only [charFun_gaussianReal, ← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]

/-! ### The central limit theorem for the multilevel estimator (Giles 2015, §2.1) -/

/-- Telescoping with integrability only up to the finest level (Giles 2015, §1.3, p. 4):
`∑_{ℓ=0}^{L} E[P_ℓ − P_{ℓ−1}] = E[P_L]` whenever `P_0, …, P_L` are integrable
(`sum_integral_levelDiff` assumes integrability on every level). -/
lemma sum_integral_levelDiff_of_le {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀}
    {Pl : ℕ → Ω₀ → ℝ} {L : ℕ} (hPl : ∀ ℓ ≤ L, Integrable (Pl ℓ) ν) :
    ∑ ℓ ∈ range (L + 1), ∫ y, levelDiff Pl ℓ y ∂ν = ∫ y, Pl L y ∂ν := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih fun ℓ hℓ => hPl ℓ (by omega), levelDiff_succ,
      integral_sub (hPl (L + 1) le_rfl) (hPl L (by omega))]
    ring

/-- The rescaled error of the level estimator (2.2) with `m n` samples, `m ≥ 1`, is a sum over its
samples: `√n (Y_ℓ − E) = ∑_{k < mn} (√n/(mn)) (ΔP_ℓ(ω^{(ℓ,k)}) − E)` (both sides vanish for
`n = 0`). -/
lemma sqrt_mul_levelEstimator_sub {Ω₀ Ω : Type*} (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀)
    (ℓ : ℕ) {m : ℕ} (hm : 0 < m) (n : ℕ) (E : ℝ) (x : Ω) :
    √(n : ℝ) * (levelEstimator Pl ω ℓ (m * n) x - E) =
      ∑ k ∈ range (m * n), √(n : ℝ) / ((m * n : ℕ) : ℝ) * (levelDiff Pl ℓ (ω (ℓ, k) x) - E) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hN : ((m * n : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    positivity
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
    levelEstimator]
  field_simp

section Inputs

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω} {ω : ℕ × ℕ → Ω → Ω₀}

/-- Functions of distinct independent inputs are independent (Giles 2015, §1.3, p. 4:
"independent samples are used at each level of correction"): if the inputs `ω^{(p)}` are
independent with law `ν`, `e` is injective and every `g i` is `ν`-a.e. measurable, then the samples
`g_i(ω^{(e i)})` are independent. -/
lemma iIndepFun_comp_inputs (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {ι : Type*} {e : ι → ℕ × ℕ} (he : e.Injective) {g : ι → Ω₀ → ℝ}
    (hg : ∀ i, AEMeasurable (g i) ν) :
    iIndepFun (fun i x => g i (ω (e i) x)) μ :=
  (hind.precomp he).comp₀ g (fun i => (hω (e i)).measurable.aemeasurable)
    fun i => by rw [(hω (e i)).map_eq]; exact hg i

/-- A sample `g(ω^{(p)})` of a `ν`-a.e. measurable `g` is a.e. measurable (the samples of Giles
2015, (2.2)). -/
lemma aemeasurable_comp_input (hω : ∀ p, MeasurePreserving (ω p) μ ν) {g : Ω₀ → ℝ}
    (hg : AEMeasurable g ν) (p : ℕ × ℕ) : AEMeasurable (fun x => g (ω p x)) μ :=
  hg.comp_quasiMeasurePreserving (hω p).quasiMeasurePreserving

/-- The level estimator (2.2) is a.e. measurable when `P_ℓ − P_{ℓ−1}` is `ν`-a.e. measurable. -/
lemma aemeasurable_levelEstimator (hω : ∀ p, MeasurePreserving (ω p) μ ν) {Pl : ℕ → Ω₀ → ℝ}
    {ℓ : ℕ} (hg : AEMeasurable (levelDiff Pl ℓ) ν) (N : ℕ) :
    AEMeasurable (levelEstimator Pl ω ℓ N) μ :=
  (Finset.aemeasurable_fun_sum _ fun k _ => aemeasurable_comp_input hω hg (ℓ, k)).const_mul _

/-- **Independent levels multiply characteristic functions** (Giles 2015, §1.3, p. 4: "independent
samples are used at each level of correction").  For independent inputs `ω^{(ℓ,k)}` with law `ν`
and `ν`-a.e. measurable `g_ℓ`, the characteristic function of
`∑_{ℓ ∈ s} ∑_{k < N_ℓ} g_ℓ(ω^{(ℓ,k)})` is the product over `ℓ ∈ s` of those of the level sums
`∑_{k < N_ℓ} g_ℓ(ω^{(ℓ,k)})`: both sides are the product over all the samples. -/
lemma charFun_map_sum_sum (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    (s : Finset ℕ) (N : ℕ → ℕ) {g : ℕ → Ω₀ → ℝ} (hg : ∀ ℓ ∈ s, AEMeasurable (g ℓ) ν)
    (t : ℝ) :
    charFun (μ.map fun x => ∑ ℓ ∈ s, ∑ k ∈ range (N ℓ), g ℓ (ω (ℓ, k) x)) t =
      ∏ ℓ ∈ s, charFun (μ.map fun x => ∑ k ∈ range (N ℓ), g ℓ (ω (ℓ, k) x)) t := by
  classical
  -- all the samples, indexed by `{(ℓ, k) : ℓ ∈ s, k < N_ℓ}`, are independent
  have hXind : iIndepFun ((s.sigma fun ℓ => range (N ℓ)).restrict
      fun (q : Σ _ : ℕ, ℕ) x => g q.1 (ω (q.1, q.2) x)) μ := by
    refine iIndepFun_comp_inputs hω hind
      (e := fun q : (s.sigma fun ℓ => range (N ℓ)) => (q.1.1, q.1.2)) ?_
      (g := fun q => g q.1.1) fun q => hg _ (Finset.mem_sigma.1 q.2).1
    rintro ⟨⟨a, b⟩, _⟩ ⟨⟨c, d⟩, _⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  have hsum : (fun x => ∑ ℓ ∈ s, ∑ k ∈ range (N ℓ), g ℓ (ω (ℓ, k) x)) =
      fun x => ∑ q ∈ s.sigma fun ℓ => range (N ℓ), g q.1 (ω (q.1, q.2) x) := by
    funext x
    rw [Finset.sum_sigma]
  rw [hsum, hXind.charFun_map_fun_finsetSum_eq_prod fun q hq =>
      aemeasurable_comp_input hω (hg q.1 (Finset.mem_sigma.1 hq).1) (q.1, q.2),
    Finset.prod_apply, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun ℓ hℓ => ?_
  -- the samples of level `ℓ` are independent
  have hYind : iIndepFun ((range (N ℓ)).restrict fun k x => g ℓ (ω (ℓ, k) x)) μ :=
    iIndepFun_comp_inputs hω hind (e := fun k : range (N ℓ) => (ℓ, k.1))
      (fun a b h => Subtype.ext (Prod.mk.inj h).2) (g := fun _ => g ℓ) fun _ => hg ℓ hℓ
  rw [hYind.charFun_map_fun_finsetSum_eq_prod fun k _ => aemeasurable_comp_input hω (hg ℓ hℓ) _,
    Finset.prod_apply]

/-- **The level estimator is asymptotically normal** (Giles 2015, §2.1, p. 8: "This exploits the
fact that the multilevel correction `Y_ℓ` on each level is asymptotically Normally-distributed").
Let the inputs `ω^{(ℓ,n)}` be independent with law `ν`, and let `ΔP_ℓ = P_ℓ − P_{ℓ−1}` be square
integrable under `ν`, with variance `V_ℓ`.  Then the level estimator (2.2) with `N` samples,
`Y_ℓ = N⁻¹ ∑_{n<N} ΔP_ℓ(ω^{(ℓ,n)})`, satisfies `√N (Y_ℓ − E[ΔP_ℓ]) → N(0, V_ℓ)` in distribution
as `N → ∞`: the sequence converges in distribution to every random variable `Z` with law
`N(0, V_ℓ)`, on any probability space.  This is Mathlib's central limit theorem
`tendstoInDistribution_inv_sqrt_mul_sum_sub` for the i.i.d. samples `ΔP_ℓ(ω^{(ℓ,n)})`, `n ∈ ℕ`;
no measurability beyond that implied by square integrability is assumed. -/
theorem tendstoInDistribution_levelEstimator {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure P'] {Pl : ℕ → Ω₀ → ℝ}
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {ℓ : ℕ}
    (hPl : MemLp (levelDiff Pl ℓ) 2 ν) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (variance (levelDiff Pl ℓ) ν).toNNReal) P') :
    TendstoInDistribution
      (fun (N : ℕ) x => √(N : ℝ) * (levelEstimator Pl ω ℓ N x - ∫ y, levelDiff Pl ℓ y ∂ν))
      atTop Z (fun _ => μ) P' := by
  have hg : AEMeasurable (levelDiff Pl ℓ) ν := hPl.aestronglyMeasurable.aemeasurable
  -- the samples `ΔP_ℓ(ω^{(ℓ,k)})` are i.i.d. with the law of `ΔP_ℓ` under `ν`
  have hlaw : ∀ k, HasLaw (fun x => levelDiff Pl ℓ (ω (ℓ, k) x)) (ν.map (levelDiff Pl ℓ)) μ :=
    fun k => HasLaw.fun_comp ⟨hg, rfl⟩ (hω (ℓ, k)).hasLaw
  have hindX : iIndepFun (fun k x => levelDiff Pl ℓ (ω (ℓ, k) x)) μ :=
    iIndepFun_comp_inputs hω hind (e := fun k => (ℓ, k)) (fun a b h => (Prod.mk.inj h).2)
      (g := fun _ => levelDiff Pl ℓ) fun _ => hg
  have hident : ∀ k, IdentDistrib (fun x => levelDiff Pl ℓ (ω (ℓ, k) x))
      (fun x => levelDiff Pl ℓ (ω (ℓ, 0) x)) μ μ := fun k =>
    ⟨(hlaw k).aemeasurable, (hlaw 0).aemeasurable, (hlaw k).map_eq.trans (hlaw 0).map_eq.symm⟩
  have hmean : ∫ x, levelDiff Pl ℓ (ω (ℓ, 0) x) ∂μ = ∫ y, levelDiff Pl ℓ y ∂ν :=
    integral_comp_of_measurePreserving (hω (ℓ, 0)) hPl.aestronglyMeasurable
  have hZ' : HasLaw Z
      (gaussianReal 0 (Var[fun x => levelDiff Pl ℓ (ω (ℓ, 0) x); μ]).toNNReal) P' := by
    rw [(hω (ℓ, 0)).variance_fun_comp hg]
    exact hZ
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun k x => levelDiff Pl ℓ (ω (ℓ, k) x)) hZ'
    (hPl.comp_measurePreserving (hω (ℓ, 0))) hindX hident
  -- `√N (N⁻¹ S − E) = (√N)⁻¹ (S − N E)`
  have heq : (fun (N : ℕ) x => √(N : ℝ) * (levelEstimator Pl ω ℓ N x -
      ∫ y, levelDiff Pl ℓ y ∂ν)) = fun (N : ℕ) x => (√(N : ℝ))⁻¹ *
        (∑ k ∈ range N, levelDiff Pl ℓ (ω (ℓ, k) x) -
          N * ∫ x, levelDiff Pl ℓ (ω (ℓ, 0) x) ∂μ) := by
    funext N x
    rw [hmean, levelEstimator]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hs : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
      have hs0 : √(N : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      apply mul_left_cancel₀ hs0
      rw [← mul_assoc, hs, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul, mul_sub, ← mul_assoc,
        mul_inv_cancel₀ hN0, one_mul]
  rw [heq]
  exact h

/-- The level CLT in characteristic-function form along `N = m n`, `m ≥ 1` (Giles 2015, §2.1,
p. 8): the characteristic function of `√n (Y_ℓ − E[ΔP_ℓ])` with `m n` samples converges to
`exp(−(V_ℓ/m) t²/2)`, that of `N(0, V_ℓ/m)`.  From `tendstoInDistribution_levelEstimator`, Lévy's
continuity theorem, `√n = m^{−1/2} √(mn)` and the subsequence `N = mn`. -/
lemma tendsto_charFun_levelEstimator [IsProbabilityMeasure μ] {Pl : ℕ → Ω₀ → ℝ}
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {ℓ : ℕ}
    (hPl : MemLp (levelDiff Pl ℓ) 2 ν) {m : ℕ} (hm : 0 < m) (t : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun x =>
        √(n : ℝ) * (levelEstimator Pl ω ℓ (m * n) x - ∫ y, levelDiff Pl ℓ y ∂ν)) t) atTop
      (𝓝 (Complex.exp ((-(variance (levelDiff Pl ℓ) ν / m * t ^ 2 / 2) : ℝ) : ℂ))) := by
  have hV := variance_nonneg (levelDiff Pl ℓ) ν
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  -- the level CLT with the limit `id` on `(ℝ, N(0, V_ℓ))`, at `(√m)⁻¹ t` and along `N = m n`
  have h := tendstoInDistribution_levelEstimator
    (P' := gaussianReal 0 (variance (levelDiff Pl ℓ) ν).toNNReal) (Z := id) hω hind hPl HasLaw.id
  have hc := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 h.tendsto
    ((√(m : ℝ))⁻¹ * t)).comp ((tendsto_id (α := ℕ)).const_mul_atTop' hm)
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id, Function.comp_def, id] at hc
  rw [charFun_gaussianReal_zero hV] at hc
  have hY : ∀ N : ℕ, AEMeasurable (fun x => √(N : ℝ) *
      (levelEstimator Pl ω ℓ N x - ∫ y, levelDiff Pl ℓ y ∂ν)) μ := fun N =>
    ((aemeasurable_levelEstimator hω hPl.aestronglyMeasurable.aemeasurable N).sub_const
      _).const_mul _
  have key : ∀ n : ℕ, charFun (μ.map fun x =>
      √(n : ℝ) * (levelEstimator Pl ω ℓ (m * n) x - ∫ y, levelDiff Pl ℓ y ∂ν)) t =
      charFun (μ.map fun x => √((m * n : ℕ) : ℝ) *
        (levelEstimator Pl ω ℓ (m * n) x - ∫ y, levelDiff Pl ℓ y ∂ν)) ((√(m : ℝ))⁻¹ * t) := by
    intro n
    rw [← charFun_map_mul_comp (hY (m * n))]
    congr 2
    funext x
    rw [Nat.cast_mul, Real.sqrt_mul hm'.le, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel₀ (Real.sqrt_pos.2 hm').ne', one_mul]
  have hlim : -(variance (levelDiff Pl ℓ) ν * ((√(m : ℝ))⁻¹ * t) ^ 2 / 2) =
      -(variance (levelDiff Pl ℓ) ν / m * t ^ 2 / 2) := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hm'.le]
    ring
  rw [hlim] at hc
  exact hc.congr fun n => (key n).symm

/-- **The multilevel estimator is asymptotically normal** (Giles 2015, §2.1, p. 8: "Collier,
Haji-Ali, Nobile, von Schwerin and Tempone (2014) have developed a modified version of the Theorem.
Instead of bounding the Mean Square Error, they prefer to use the Central Limit Theorem to construct
a confidence interval which bounds `E[P]` with a user-prescribed confidence. This exploits the fact
that the multilevel correction `Y_ℓ` on each level is asymptotically Normally-distributed, and
therefore so is `Y`.").  Fix the finest level `L` and integers `m_ℓ ≥ 1`, and use `N_ℓ = m_ℓ n`
samples on level `ℓ ≤ L`.  If the inputs `ω^{(ℓ,k)}` are independent with law `ν` and
`P_0, …, P_L` are square integrable under `ν`, then as `n → ∞` the estimator (2.2)
`Y = ∑_{ℓ=0}^{L} Y_ℓ` satisfies `√n (Y − E[P_L]) → N(0, ∑_{ℓ=0}^{L} V_ℓ/m_ℓ)` in distribution,
`V_ℓ = V[P_ℓ − P_{ℓ−1}]`: the sequence converges in distribution to every random variable `Z` with
that law.  Informally, `Y − E[P_L]` is approximately `N(0, ∑_ℓ V_ℓ/N_ℓ) = N(0, V[Y])`, see (2.3).
The characteristic function of `√n (Y − E[P_L])` is the product over the levels of those of
`√n (Y_ℓ − E[ΔP_ℓ])` (`charFun_map_sum_sum`), each factor converges by the level CLT
(`tendsto_charFun_levelEstimator`), and Lévy's continuity theorem concludes.

This is the statement for a fixed number of levels and sample sizes proportional to a common `n`.
Collier et al. let `L` grow as the tolerance `ε → 0`, with the `N_ℓ` depending on `ε`, so the
number of summands, their laws and the number of levels change together; normality in that regime
is a Lindeberg–Feller central limit theorem for triangular arrays, which Mathlib does not have. -/
theorem tendstoInDistribution_mlmcEstimator {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure P'] {Pl : ℕ → Ω₀ → ℝ}
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {L : ℕ}
    (hPl : ∀ ℓ ≤ L, MemLp (Pl ℓ) 2 ν) {m : ℕ → ℕ} (hm : ∀ ℓ ≤ L, 0 < m ℓ) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0
      (∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / m ℓ).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) x => √(n : ℝ) *
        (mlmcEstimator Pl ω L (fun ℓ => m ℓ * n) x - ∫ y, Pl L y ∂ν))
      atTop Z (fun _ => μ) P' := by
  -- the law `ν` of the inputs is a probability measure, as the image of `μ`
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  have hle : ∀ ℓ ∈ range (L + 1), ℓ ≤ L := fun ℓ hℓ =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
  have hD : ∀ ℓ ∈ range (L + 1), MemLp (levelDiff Pl ℓ) 2 ν := by
    intro ℓ hℓ
    cases ℓ with
    | zero => exact hPl 0 (Nat.zero_le L)
    | succ k => exact (hPl (k + 1) (hle _ hℓ)).sub (hPl k (by have := hle _ hℓ; omega))
  have hDm : ∀ ℓ ∈ range (L + 1), AEMeasurable (levelDiff Pl ℓ) ν := fun ℓ hℓ =>
    (hD ℓ hℓ).aestronglyMeasurable.aemeasurable
  have htel : ∫ y, Pl L y ∂ν = ∑ ℓ ∈ range (L + 1), ∫ y, levelDiff Pl ℓ y ∂ν :=
    (sum_integral_levelDiff_of_le fun ℓ hℓ => (hPl ℓ hℓ).integrable one_le_two).symm
  -- `√n (Y − E[P_L]) = ∑_ℓ √n (Y_ℓ − E[ΔP_ℓ])`
  have hsplit : ∀ (n : ℕ) (x : Ω), √(n : ℝ) *
      (mlmcEstimator Pl ω L (fun ℓ => m ℓ * n) x - ∫ y, Pl L y ∂ν) =
      ∑ ℓ ∈ range (L + 1), √(n : ℝ) *
        (levelEstimator Pl ω ℓ (m ℓ * n) x - ∫ y, levelDiff Pl ℓ y ∂ν) := by
    intro n x
    rw [htel, mlmcEstimator, ← Finset.sum_sub_distrib, Finset.mul_sum]
  have hmeas : ∀ n : ℕ, AEMeasurable (fun x => √(n : ℝ) *
      (mlmcEstimator Pl ω L (fun ℓ => m ℓ * n) x - ∫ y, Pl L y ∂ν)) μ := by
    intro n
    simp only [mlmcEstimator]
    exact ((Finset.aemeasurable_fun_sum _ fun ℓ hℓ =>
      aemeasurable_levelEstimator hω (hDm ℓ hℓ) _).sub_const _).const_mul _
  refine ⟨hmeas, hZ.aemeasurable, ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_⟩
  simp only [ProbabilityMeasure.coe_mk]
  rw [hZ.map_eq, charFun_gaussianReal_zero (Finset.sum_nonneg fun ℓ _ =>
    div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _))]
  -- the characteristic function factorises over the levels
  have hfac : ∀ n : ℕ, charFun (μ.map fun x => √(n : ℝ) *
      (mlmcEstimator Pl ω L (fun ℓ => m ℓ * n) x - ∫ y, Pl L y ∂ν)) t =
      ∏ ℓ ∈ range (L + 1), charFun (μ.map fun x => √(n : ℝ) *
        (levelEstimator Pl ω ℓ (m ℓ * n) x - ∫ y, levelDiff Pl ℓ y ∂ν)) t := by
    intro n
    have e1 : (fun x => √(n : ℝ) *
        (mlmcEstimator Pl ω L (fun ℓ => m ℓ * n) x - ∫ y, Pl L y ∂ν)) =
        fun x => ∑ ℓ ∈ range (L + 1), ∑ k ∈ range (m ℓ * n),
          (fun ℓ y => √(n : ℝ) / ((m ℓ * n : ℕ) : ℝ) *
            (levelDiff Pl ℓ y - ∫ y, levelDiff Pl ℓ y ∂ν)) ℓ (ω (ℓ, k) x) := by
      funext x
      rw [hsplit]
      exact Finset.sum_congr rfl fun ℓ hℓ =>
        sqrt_mul_levelEstimator_sub Pl ω ℓ (hm ℓ (hle ℓ hℓ)) n _ x
    rw [e1, charFun_map_sum_sum hω hind _ (fun ℓ => m ℓ * n)
      (fun ℓ hℓ => ((hDm ℓ hℓ).sub_const _).const_mul _) t]
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    congr 2
    funext x
    exact (sqrt_mul_levelEstimator_sub Pl ω ℓ (hm ℓ (hle ℓ hℓ)) n _ x).symm
  -- the product of the limits `exp(−(V_ℓ/m_ℓ) t²/2)` is `exp(−(∑_ℓ V_ℓ/m_ℓ) t²/2)`
  have hlim : ∏ ℓ ∈ range (L + 1),
      Complex.exp ((-(variance (levelDiff Pl ℓ) ν / m ℓ * t ^ 2 / 2) : ℝ) : ℂ) =
      Complex.exp ((-((∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / m ℓ) *
        t ^ 2 / 2) : ℝ) : ℂ) := by
    rw [← Complex.exp_sum, ← Complex.ofReal_sum, Finset.sum_mul, Finset.sum_div,
      ← Finset.sum_neg_distrib]
  rw [← hlim]
  exact (tendsto_finsetProd _ fun ℓ hℓ => tendsto_charFun_levelEstimator hω hind (hD ℓ hℓ)
    (hm ℓ (hle ℓ hℓ)) t).congr fun n => (hfac n).symm

end Inputs

/-! ### Sums of approximate normal random variables (Haas–Giles 2025, §3.2) -/

section ApproxNormal

variable {Ω Ω' : Type*} [MeasurableSpace Ω] {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {P' : Measure Ω'}

/-- A sum of independent real Gaussian random variables is Gaussian with the summed means and
variances: if the `X i` are independent with laws `N(m_i, v_i)`, then `∑_{i ∈ s} X i` has law
`N(∑_{i ∈ s} m_i, ∑_{i ∈ s} v_i)` (induction on `s` with
`gaussianReal_add_gaussianReal_of_indepFun`). -/
lemma hasLaw_finsetSum_gaussianReal {ι : Type*} {X : ι → Ω → ℝ} {m : ι → ℝ} {v : ι → ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P) (hind : iIndepFun X P)
    (s : Finset ι) :
    HasLaw (fun ω => ∑ i ∈ s, X i ω) (gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i)) P := by
  classical
  have := hind.isProbabilityMeasure
  induction s using Finset.induction_on with
  | empty =>
    simpa [gaussianReal_zero_var] using hasLaw_dirac_of_ae_eq (P := P) (x := (0 : ℝ))
      (Filter.EventuallyEq.refl _ _)
  | insert a s ha ih =>
    have hindep : IndepFun (∑ j ∈ s, X j) (X a) P :=
      hind.indepFun_finsetSum_of_notMem₀ (fun i => (hX i).aemeasurable) ha
    have hfun : (fun ω => ∑ i ∈ insert a s, X i ω) = (∑ j ∈ s, X j) + X a := by
      funext ω
      simp [Finset.sum_insert ha, add_comm]
    have hmap : P.map (∑ j ∈ s, X j) = gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i) := by
      rw [Finset.sum_fn]
      exact ih.map_eq
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact (Finset.sum_fn s X ▸ ih.aemeasurable).add (hX a).aemeasurable
    · rw [hfun, gaussianReal_add_gaussianReal_of_indepFun hindep hmap (hX a).map_eq,
        Finset.sum_insert ha, Finset.sum_insert ha, add_comm (m a), add_comm (v a)]

/-- **A sum of `n` independent `N(0, 1/n)` variables is `N(0, 1)`** (Haas–Giles 2025, §3.2, p. 5:
"For example take an integer `n` that divides `d` and produce an approximate random number
`X^{(1)}` from the first `d/n` bits of `j`, then `X^{(2)}` from the next `d/n` bits and so on,
where each `X^{(i)}` follows approximately the distribution `N(0,1/n)`. Then `∑_{i=1}^n X^{(i)}`
has approximately the distribution `N(0,1)`.").  The exact case: if `X^{(1)}, …, X^{(n)}`,
`n ≥ 1`, are independent (in the paper they are read from disjoint bits of the same uniform
integer `j`) and each has law exactly `N(0, 1/n)`, then `∑_i X^{(i)}` has law exactly `N(0, 1)`.
For "approximately" see `tendstoInDistribution_sum_of_approxNormal` (fixed `n`) and
`tendstoInDistribution_sum_inv_sqrt_mul` (`n → ∞`). -/
theorem sum_gaussian_hasLaw {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 (n : ℝ≥0)⁻¹) P) (hind : iIndepFun X P) :
    HasLaw (fun ω => ∑ i, X i ω) (gaussianReal 0 1) P := by
  have h := hasLaw_finsetSum_gaussianReal hX hind Finset.univ
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_inv_cancel₀ hn'] using h

/-- Independent sums are continuous at Gaussian laws: if for every `d` the random variables
`X_d^{(i)}`, `i ∈ ι` (finite), are independent, and each `X_d^{(i)}` converges in distribution to
`N(m_i, v_i)` as `d → ∞` (with the identity on `(ℝ, N(m_i, v_i))` as the limit variable), then
`∑_i X_d^{(i)}` converges in distribution to `N(∑ m_i, ∑ v_i)`: the characteristic function of
the sum is the product of those of the summands, and Lévy's continuity theorem applies. -/
lemma tendstoInDistribution_fun_sum_gaussianReal [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {ι : Type*} [Fintype ι] {X : ℕ → ι → Ω → ℝ} {m : ι → ℝ}
    {v : ι → ℝ≥0} (hind : ∀ d, iIndepFun (X d) P)
    (hX : ∀ i, TendstoInDistribution (fun d => X d i) atTop id (fun _ => P)
      (gaussianReal (m i) (v i)))
    {G : Ω' → ℝ} (hG : HasLaw G (gaussianReal (∑ i, m i) (∑ i, v i)) P') :
    TendstoInDistribution (fun d ω => ∑ i, X d i ω) atTop G (fun _ => P) P' := by
  refine ⟨fun d => Finset.aemeasurable_fun_sum _ fun i _ => (hX i).forall_aemeasurable d,
    hG.aemeasurable, ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_⟩
  simp only [ProbabilityMeasure.coe_mk]
  rw [hG.map_eq, charFun_gaussianReal_sum]
  have hfac : ∀ d, charFun (P.map fun ω => ∑ i, X d i ω) t = ∏ i, charFun (P.map (X d i)) t :=
    fun d => by
      rw [(hind d).charFun_map_fun_sum_eq_prod fun i => (hX i).forall_aemeasurable d,
        Finset.prod_apply]
  refine (tendsto_finsetProd _ fun i _ => ?_).congr fun d => (hfac d).symm
  simpa using ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 (hX i).tendsto t

/-- **Approximately `N(0, 1/n)` summands give an approximately `N(0, 1)` sum** (Haas–Giles 2025,
§3.2, p. 5: "… where each `X^{(i)}` follows approximately the distribution `N(0,1/n)`. Then
`∑_{i=1}^n X^{(i)}` has approximately the distribution `N(0,1)`."), with "approximately" read as
convergence in distribution as the approximation is refined (for the lookup tables of §3.2, as the
bit width `d → ∞` with `n` fixed).  For fixed `n ≥ 1`, let `X_d^{(1)}, …, X_d^{(n)}` be
independent for every `d` (the paper reads them from disjoint bits of the same uniform integer
`j`), and let each `X_d^{(i)}` converge in distribution to `N(0, 1/n)` as `d → ∞` (with the
identity on `(ℝ, N(0, 1/n))` as the limit variable).  Then `∑_i X_d^{(i)}` converges in
distribution to `N(0, 1)`.  That the lookup-table variables themselves converge to `N(0, 1/n)` is
the hypothesis, not proved here. -/
theorem tendstoInDistribution_sum_of_approxNormal [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {n : ℕ} (hn : 0 < n) {X : ℕ → Fin n → Ω → ℝ}
    (hind : ∀ d, iIndepFun (X d) P)
    (hX : ∀ i, TendstoInDistribution (fun d => X d i) atTop id (fun _ => P)
      (gaussianReal 0 (n : ℝ≥0)⁻¹))
    {G : Ω' → ℝ} (hG : HasLaw G (gaussianReal 0 1) P') :
    TendstoInDistribution (fun d ω => ∑ i, X d i ω) atTop G (fun _ => P) P' := by
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  refine tendstoInDistribution_fun_sum_gaussianReal (m := fun _ => 0) hind hX ?_
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_inv_cancel₀ hn'] using hG

/-- **The central-limit form of "approximately `N(0, 1)`"** (Haas–Giles 2025, §3.2, p. 5: "…
where each `X^{(i)}` follows approximately the distribution `N(0,1/n)`. Then `∑_{i=1}^n X^{(i)}`
has approximately the distribution `N(0,1)`.").  Let `Z_1, Z_2, …` be independent and identically
distributed with mean `0` and variance `1`, for instance the values of a fixed lookup table at
independent uniform indices, rescaled to unit variance.  Then `X_i^{(n)} = n^{−1/2} Z_i` has mean
`0` and variance `1/n`, and `∑_{i=1}^n X_i^{(n)}` converges in distribution to `N(0, 1)` as
`n → ∞`, whatever the law of the `Z_i` (Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum`; the
indices are shifted to `0, …, n − 1`).  In the paper `n` is small and fixed (`n = 8, 4, 2` in the
works it cites) and "approximately" refers to the accuracy of the lookup table (see
`tendstoInDistribution_sum_of_approxNormal`); this is the complementary statement that summing
more variables also improves the approximation. -/
theorem tendstoInDistribution_sum_inv_sqrt_mul [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℝ} (hind : iIndepFun Z P) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (h0 : P[Z 0] = 0) (h1 : Var[Z 0; P] = 1) {G : Ω' → ℝ}
    (hG : HasLaw G (gaussianReal 0 1) P') :
    TendstoInDistribution (fun (n : ℕ) ω => ∑ i ∈ range n, (√(n : ℝ))⁻¹ * Z i ω) atTop G
      (fun _ => P) P' := by
  have h2 : P[Z 0 ^ 2] = 1 := by
    rw [← h1, variance_of_integral_eq_zero (hident 0).aemeasurable_fst h0]
    rfl
  simpa only [Finset.mul_sum] using tendstoInDistribution_inv_sqrt_mul_sum hG h0 h2 hind hident

end ApproxNormal

end MLMC
