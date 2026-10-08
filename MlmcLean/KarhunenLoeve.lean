import MlmcLean.EulerMaruyama
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Integration

/-!
# Truncated Karhunen–Loève inputs for the log-normal elliptic SPDE (Giles 2015, §7.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §7.2 "Elliptic
SPDE", pp. 51–53 (`docs/giles2015.txt`, l. 2213–2279; the line numbers below refer to it).  Rows
G7.2-03 (the Karhunen–Loève expansion, l. 2255–2262) and G7.2-05 (its truncation after `K_ℓ`
terms, l. 2265–2268).

**Setting.**  The paper models `log κ` as a centred Gaussian field with covariance `R(x, y)`
(l. 2219–2221, 2254–2255) and samples it by "a Karhunen-Loève expansion:
`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`, where `θ_n` are the eigenvalues of `R(x, y)` in
decreasing order, `f_n` are the corresponding eigenfunctions, and `ξ_n` are independent unit Normal
random variables" (l. 2255–2262); on level `ℓ` "the expansion is truncated after `K_ℓ` terms, with
`K_ℓ` increasing with level" (l. 2266–2268).  Mercer's theorem is not formalised; what it
provides is taken as hypotheses: an s-finite measure space `(D, ν)`, functions `f_n ∈ L²(ν)` with
`∫ f_n f_m dν = δ_{nm}`, weights `θ_n ≥ 0` with `∑ θ_n < ∞` and, where needed, the pointwise
expansion `R(x, y) = ∑ θ_n f_n(x) f_n(y)` (`HasSum`).  The `ξ_n` are the coordinates `z n` under
`stdNormalSeq = N(0, 1)^{⊗ℕ}`, so they are independent standard normal variables.

* `klField θ f K z x = ∑_{n<K} √θ_n z_n f_n(x)` is the truncated field `Y_K` (the level-`ℓ` input
  for `K = K_ℓ`) and `klDiffusivity θ f K z x = exp (Y_K)` the truncated diffusivity `κ_K`.
* `klField_levelCorrection`: `E ∫ (Y_M − Y_K)² dν = ∑_{K≤n<M} θ_n` for `K ≤ M` — the size of the
  level correction of the input for `K = K_{ℓ−1}`, `M = K_ℓ`.
* `exists_klField_limit`: the series converges in `L²(P ⊗ ν)` to a field `Y` with
  `E ∫ (Y − Y_K)² dν = ∑_{n≥K} θ_n`, which tends to `0` as `K → ∞` (truncation error).
* `map_klField_eq_gaussianReal`: for each `x`, `Y_K(·, x) ∼ N(0, ∑_{n<K} θ_n f_n(x)²)`.
* `klDiffusivity_moment`: `E[κ_K(x)^p] = exp(p² σ_K(x)²/2) ≤ exp(p² R(x, x)/2)` for every real
  `p`: the moments of the (unbounded, l. 2275–2276) truncated diffusivity are bounded uniformly in
  the level.
* `integral_klField_mul`, `tendsto_integral_klField_mul`: `E[Y_K(x) Y_K(y)] = ∑_{n<K} θ_n f_n(x)
  f_n(y) → R(x, y)`.
* `kl_hypotheses_satisfiable`: the hypotheses are satisfiable (counting measure on `ℕ`,
  `f_n = 1_{{n}}`, `R(x, y) = θ_x δ_{xy}`).

The coupling `ξ_ℓ = (ξ_{ℓ−1}, z_ℓ)` of l. 2270–2273 is built into `klField`: all levels use the
same `z_0, z_1, …`, the coarse field uses the first `K_{ℓ−1}` of them.  Its consequence (2.4) for
truncated vectors of independent inputs is `nested_vector_inputs_mlmc` (`MlmcLean.SpotCheckRemarks`,
not imported here).

**Deviations.**  The ordering `θ_0 ≥ θ_1 ≥ …` is not needed and not assumed.  The limit field is
an `L²(P ⊗ ν)` limit (a representative of the limit class); the almost sure pointwise convergence
of the series and the identification of the limits are in `MlmcLean.KarhunenLoeveLimit`
(`klLimit_tendsto`, `klLimit_ae_eq_L2_limit`).  The paper's stationary covariance
`R(x, y) = r(x − y)` (l. 2255) is replaced by a general `R` given by its expansion.

**Not proved.**  Mercer's theorem (existence of the eigenpairs and of the expansion of `R`), the
circulant embedding generation (l. 2262–2264), the identification with the paper's log-normal
diffusivity on a specific domain `D` and covariance `r`, and the multilevel analysis of the elliptic
PDE itself (Charrier, Scheichl & Teckentrup, l. 2275–2279); the moments of `max_x κ` and
`1/min_x κ` that the analysis of the elliptic PDE needs.  The law of the limit field `Y` (Gaussian
with covariance `R`) and the moments of the untruncated `κ = exp Y` are in
`MlmcLean.KarhunenLoeveLimit` (`map_klLimit_eq_gaussianReal`, `klLimitDiffusivity_moment`).
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal ENNReal

namespace MLMC

/-! ### Independent standard normal coordinates -/

/-- The coordinate `z ↦ z n` maps `N(0, 1)^{⊗ℕ}` to `N(0, 1)` (Giles 2015, §7.2, p. 53,
l. 2261–2262: "`ξ_n` are independent unit Normal random variables"). -/
lemma measurePreserving_eval_stdNormalSeq (n : ℕ) :
    MeasurePreserving (fun z : ℕ → ℝ => z n) stdNormalSeq (gaussianReal 0 1) :=
  ⟨measurable_pi_apply n, Measure.infinitePi_map_eval _ n⟩

/-- Each coordinate `ξ_n = z n` has all finite moments (Giles 2015, §7.2, p. 53, l. 2261–2262). -/
lemma memLp_eval_stdNormalSeq (n : ℕ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun z : ℕ → ℝ => z n) p stdNormalSeq :=
  (memLp_id_gaussianReal' (μ := 0) (v := 1) p hp).comp_measurePreserving
    (measurePreserving_eval_stdNormalSeq n)

/-- Change of variables for one coordinate of `N(0, 1)^{⊗ℕ}` (Giles 2015, §7.2, p. 53,
l. 2261–2262). -/
lemma integral_comp_eval_stdNormalSeq (n : ℕ) {g : ℝ → ℝ} (hg : StronglyMeasurable g) :
    ∫ z, g (z n) ∂stdNormalSeq = ∫ y, g y ∂gaussianReal 0 1 := by
  rw [← (measurePreserving_eval_stdNormalSeq n).map_eq,
    integral_map (measurable_pi_apply n).aemeasurable hg.aestronglyMeasurable]

/-- `E[ξ_n ξ_m] = δ_{nm}` for independent unit normal `ξ_n` (Giles 2015, §7.2, p. 53,
l. 2261–2262: "`ξ_n` are independent unit Normal random variables"). -/
lemma integral_mul_eval_stdNormalSeq (n m : ℕ) :
    Integrable (fun z : ℕ → ℝ => z n * z m) stdNormalSeq ∧
      ∫ z, z n * z m ∂stdNormalSeq = if n = m then 1 else 0 := by
  refine ⟨(memLp_eval_stdNormalSeq n (p := 2) (by simp)).integrable_mul
    (memLp_eval_stdNormalSeq m (p := 2) (by simp)), ?_⟩
  split_ifs with h
  · subst h
    have hv := variance_eq_integral (X := id) (μ := gaussianReal 0 1) aemeasurable_id
    rw [variance_id_gaussianReal] at hv
    have h0 : ∫ x, id x ∂gaussianReal 0 1 = 0 := integral_id_gaussianReal
    rw [h0] at hv
    rw [integral_comp_eval_stdNormalSeq n (g := fun y => y * y)
      (measurable_id.mul measurable_id).stronglyMeasurable]
    simp only [id, sub_zero] at hv
    simp only [← sq]
    rw [← hv]
    simp
  · have hind : IndepFun (fun z : ℕ → ℝ => z n) (fun z => z m) stdNormalSeq :=
      (iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ x => x)
        fun _ => measurable_id).indepFun h
    rw [hind.integral_fun_mul_eq_mul_integral (measurable_pi_apply n).aestronglyMeasurable
      (measurable_pi_apply m).aestronglyMeasurable]
    have h0 : ∫ z, z n ∂stdNormalSeq = 0 := by
      rw [integral_comp_eval_stdNormalSeq n (g := fun y => y) measurable_id.stronglyMeasurable]
      exact integral_id_gaussianReal
    rw [h0, zero_mul]

/-! ### The truncated field -/

variable {D : Type*}

/-- **The truncated Karhunen–Loève field** `Y_K(z, x) = ∑_{n<K} √θ_n z_n f_n(x)` (Giles 2015, §7.2,
p. 53, l. 2255–2262: "`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`", and l. 2266–2267: "the expansion
is truncated after `K_ℓ` terms").  Here `ξ_n = z n`; the level-`ℓ` input is `K = K_ℓ`. -/
noncomputable def klField (θ : ℕ → ℝ) (f : ℕ → D → ℝ) (K : ℕ) (z : ℕ → ℝ) (x : D) : ℝ :=
  ∑ n ∈ range K, Real.sqrt (θ n) * z n * f n x

/-- **The truncated diffusivity** `κ_K = exp Y_K` (Giles 2015, §7.2, pp. 51–53, l. 2219–2220: "the
diffusivity (or permeability) `κ` is often modelled as a lognormal random field, i.e. `log κ` is a
Gaussian field", with `log κ` truncated after `K` terms, l. 2266–2267). -/
noncomputable def klDiffusivity (θ : ℕ → ℝ) (f : ℕ → D → ℝ) (K : ℕ) (z : ℕ → ℝ) (x : D) : ℝ :=
  Real.exp (klField θ f K z x)

/-- One term `c ξ_n g(x)` of the expansion is in `L²(P ⊗ ν)` when `g ∈ L²(ν)` (Giles 2015, §7.2,
p. 53, l. 2255–2262). -/
lemma memLp_klTerm [MeasurableSpace D] {ν : Measure D} [SFinite ν] {g : D → ℝ}
    (hg : MemLp g 2 ν) (c : ℝ) (n : ℕ) :
    MemLp (fun p : (ℕ → ℝ) × D => c * p.1 n * g p.2) 2 (stdNormalSeq.prod ν) := by
  have hA : AEStronglyMeasurable (fun p : (ℕ → ℝ) × D => c * p.1 n) (stdNormalSeq.prod ν) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hB : AEStronglyMeasurable (fun p : (ℕ → ℝ) × D => g p.2) (stdNormalSeq.prod ν) :=
    hg.aestronglyMeasurable.comp_snd
  have hm : AEStronglyMeasurable (fun p : (ℕ → ℝ) × D => c * p.1 n * g p.2)
      (stdNormalSeq.prod ν) := hA.mul hB
  rw [memLp_two_iff_integrable_sq hm]
  have h1 : Integrable (fun z : ℕ → ℝ => (c * z n) ^ 2) stdNormalSeq :=
    ((memLp_eval_stdNormalSeq n (p := 2) (by simp)).const_mul c).integrable_sq
  have := h1.mul_prod hg.integrable_sq
  refine this.congr (ae_of_all _ fun p => ?_)
  simp only
  ring

/-- **Orthogonality of the expansion**: for orthonormal `f_n` and independent unit normal `ξ_n`,
`E ∫ (∑_{n∈s} c_n ξ_n f_n)² dν = ∑_{n∈s} c_n²` (Giles 2015, §7.2, p. 53, l. 2255–2262). -/
lemma integral_sq_sum_klTerm [MeasurableSpace D] {ν : Measure D} [SFinite ν] {f : ℕ → D → ℝ}
    (hf : ∀ n, MemLp (f n) 2 ν)
    (hfo : ∀ n m, ∫ x, f n x * f m x ∂ν = if n = m then 1 else 0) (s : Finset ℕ) (c : ℕ → ℝ) :
    MemLp (fun p : (ℕ → ℝ) × D => ∑ n ∈ s, c n * p.1 n * f n p.2) 2 (stdNormalSeq.prod ν) ∧
      ∫ p, (∑ n ∈ s, c n * p.1 n * f n p.2) ^ 2 ∂(stdNormalSeq.prod ν) = ∑ n ∈ s, c n ^ 2 := by
  have hterm := fun n => memLp_klTerm (hf n) (c n) n
  refine ⟨memLp_finsetSum s fun n _ => hterm n, ?_⟩
  have hexp : ∀ p : (ℕ → ℝ) × D, (∑ n ∈ s, c n * p.1 n * f n p.2) ^ 2 =
      ∑ n ∈ s, ∑ m ∈ s, (c n * c m * (p.1 n * p.1 m)) * (f n p.2 * f m p.2) := by
    intro p
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [hexp]
  have hint : ∀ n m, Integrable (fun p : (ℕ → ℝ) × D =>
      (c n * c m * (p.1 n * p.1 m)) * (f n p.2 * f m p.2)) (stdNormalSeq.prod ν) := by
    intro n m
    refine ((hterm n).integrable_mul (hterm m)).congr (ae_of_all _ fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  rw [integral_finsetSum s fun n _ => integrable_finsetSum s fun m _ => hint n m]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_finsetSum s fun m _ => hint n m]
  have hnm : ∀ m, ∫ p : (ℕ → ℝ) × D, (c n * c m * (p.1 n * p.1 m)) * (f n p.2 * f m p.2)
      ∂(stdNormalSeq.prod ν) = if n = m then c n ^ 2 else 0 := by
    intro m
    rw [integral_prod_mul (fun z : ℕ → ℝ => c n * c m * (z n * z m))
      (fun x => f n x * f m x), integral_const_mul, (integral_mul_eval_stdNormalSeq n m).2, hfo]
    split_ifs with h
    · subst h; ring
    · ring
  simp_rw [hnm]
  rw [Finset.sum_ite_eq s n, if_pos hn]

/-- The level correction of the input is the block of terms `K ≤ n < M` (Giles 2015, §7.2, p. 53,
l. 2266–2273). -/
lemma klField_sub {θ : ℕ → ℝ} {f : ℕ → D → ℝ} {K M : ℕ} (hKM : K ≤ M) (z : ℕ → ℝ) (x : D) :
    klField θ f M z x - klField θ f K z x = ∑ n ∈ Ico K M, Real.sqrt (θ n) * z n * f n x := by
  rw [klField, klField, Finset.sum_Ico_eq_sub _ hKM]

/-- The truncated field is in `L²(P ⊗ ν)` (Giles 2015, §7.2, p. 53, l. 2266–2267). -/
lemma memLp_klField [MeasurableSpace D] {ν : Measure D} [SFinite ν] (θ : ℕ → ℝ)
    {f : ℕ → D → ℝ} (hf : ∀ n, MemLp (f n) 2 ν) (K : ℕ) :
    MemLp (fun p : (ℕ → ℝ) × D => klField θ f K p.1 p.2) 2 (stdNormalSeq.prod ν) :=
  memLp_finsetSum (range K) fun n _ => memLp_klTerm (hf n) (Real.sqrt (θ n)) n

/-- **The level correction of the truncated Karhunen–Loève input** (Giles 2015, §7.2, p. 53,
l. 2266–2268: "Using the Karhunen-Loève generation, the expansion is truncated after `K_ℓ` terms,
with `K_ℓ` increasing with level").  With orthonormal `f_n ∈ L²(ν)` and `θ_n ≥ 0`, for `K ≤ M` the
difference `Y_M − Y_K` of the truncated fields (both driven by the same `ξ_n`, as in
`ξ_ℓ = (ξ_{ℓ−1}, z_ℓ)`, l. 2269–2273) is square integrable and
`E ∫ (Y_M − Y_K)² dν = ∑_{K≤n<M} θ_n`; for `K = K_{ℓ−1}`, `M = K_ℓ` this is the mean square of
the level-`ℓ` input correction. -/
theorem klField_levelCorrection [MeasurableSpace D] {ν : Measure D} [SFinite ν] {θ : ℕ → ℝ}
    (hθ : ∀ n, 0 ≤ θ n) {f : ℕ → D → ℝ} (hf : ∀ n, MemLp (f n) 2 ν)
    (hfo : ∀ n m, ∫ x, f n x * f m x ∂ν = if n = m then 1 else 0) {K M : ℕ} (hKM : K ≤ M) :
    Integrable (fun p : (ℕ → ℝ) × D => (klField θ f M p.1 p.2 - klField θ f K p.1 p.2) ^ 2)
        (stdNormalSeq.prod ν) ∧
      ∫ p, (klField θ f M p.1 p.2 - klField θ f K p.1 p.2) ^ 2 ∂(stdNormalSeq.prod ν) =
        ∑ n ∈ Ico K M, θ n := by
  simp_rw [klField_sub hKM]
  obtain ⟨hm, hi⟩ := integral_sq_sum_klTerm hf hfo (Ico K M) fun n => Real.sqrt (θ n)
  refine ⟨hm.integrable_sq, ?_⟩
  rw [hi]
  exact Finset.sum_congr rfl fun n _ => Real.sq_sqrt (hθ n)

/-- `‖[g]‖² = ∫ g²` in `L²` (used for Giles 2015, §7.2, p. 53, l. 2255–2268). -/
lemma klNorm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : MemLp g 2 μ) : ‖hg.toLp g‖ ^ 2 = ∫ a, g a ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (hg.coeFn_toLp.mono fun a ha => ?_)
  simp [ha, sq]

/-- Reindexing of the block `K ≤ n < M` (used for Giles 2015, §7.2, p. 53, l. 2266–2268). -/
lemma kl_sum_Ico_eq_sum_range_add (θ : ℕ → ℝ) (K M : ℕ) :
    ∑ n ∈ Ico K M, θ n = ∑ n ∈ range (M - K), θ (n + K) := by
  rw [Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl fun n _ => by rw [add_comm]

/-- **The Karhunen–Loève expansion converges and its truncation error is the eigenvalue tail**
(Giles 2015, §7.2, p. 53, l. 2255–2262: "`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`", and
l. 2266–2267: "the expansion is truncated after `K_ℓ` terms").  With orthonormal `f_n ∈ L²(ν)` and
summable `θ_n ≥ 0`, there is a field `Y ∈ L²(P ⊗ ν)` (the full expansion, as an `L²` limit) such
that for every `K` the truncation error `(Y − Y_K)²` is integrable with
`E ∫ (Y − Y_K)² dν = ∑_{n≥K} θ_n` (written `∑' n, θ (n + K)`), and this tends to `0` as
`K → ∞`. -/
theorem exists_klField_limit [MeasurableSpace D] {ν : Measure D} [SFinite ν] {θ : ℕ → ℝ}
    (hθ : ∀ n, 0 ≤ θ n) (hθs : Summable θ) {f : ℕ → D → ℝ} (hf : ∀ n, MemLp (f n) 2 ν)
    (hfo : ∀ n m, ∫ x, f n x * f m x ∂ν = if n = m then 1 else 0) :
    ∃ Y : (ℕ → ℝ) × D → ℝ, MemLp Y 2 (stdNormalSeq.prod ν) ∧
      (∀ K, Integrable (fun p : (ℕ → ℝ) × D => (Y p - klField θ f K p.1 p.2) ^ 2)
          (stdNormalSeq.prod ν) ∧
        ∫ p, (Y p - klField θ f K p.1 p.2) ^ 2 ∂(stdNormalSeq.prod ν) = ∑' n, θ (n + K)) ∧
      Tendsto (fun K => ∫ p, (Y p - klField θ f K p.1 p.2) ^ 2 ∂(stdNormalSeq.prod ν)) atTop
        (𝓝 0) := by
  set μ := stdNormalSeq.prod ν with hμ
  have hY := memLp_klField θ hf (ν := ν)
  set F : ℕ → Lp ℝ 2 μ := fun K => (hY K).toLp _ with hF
  have hnorm : ∀ K M, K ≤ M → ‖F M - F K‖ ^ 2 = ∑ n ∈ Ico K M, θ n := by
    intro K M hKM
    rw [hF, ← MemLp.toLp_sub, klNorm_toLp_sq]
    exact (klField_levelCorrection hθ hf hfo hKM).2
  have htail : ∀ K, Summable fun n => θ (n + K) := fun K => (summable_nat_add_iff K).2 hθs
  have hle : ∀ K M, K ≤ M → ‖F M - F K‖ ^ 2 ≤ ∑' n, θ (n + K) := by
    intro K M hKM
    rw [hnorm K M hKM, kl_sum_Ico_eq_sum_range_add θ]
    exact (htail K).sum_le_tsum _ fun n _ => hθ _
  have hcauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (tendsto_order.1 (tendsto_sum_nat_add θ)).2 (ε ^ 2) (by positivity)
      |>.exists_forall_of_atTop
    refine ⟨N, fun M hM => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le ((hle N M hM).trans_lt (hN N le_rfl))
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlimK : ∀ K, ∫ p, (G p - klField θ f K p.1 p.2) ^ 2 ∂μ = ∑' n, θ (n + K) := by
    intro K
    have h1 : Tendsto (fun M => ‖F M - F K‖ ^ 2) atTop (𝓝 (‖G - F K‖ ^ 2)) :=
      ((hG.sub_const (F K)).norm).pow 2
    have h2 : Tendsto (fun M => ‖F M - F K‖ ^ 2) atTop (𝓝 (∑' n, θ (n + K))) := by
      have h3 : Tendsto (fun M => ∑ n ∈ range (M - K), θ (n + K)) atTop
          (𝓝 (∑' n, θ (n + K))) :=
        (htail K).hasSum.tendsto_sum_nat.comp (tendsto_sub_atTop_nat K)
      refine h3.congr' ((eventually_ge_atTop K).mono fun M hM => ?_)
      change _ = ‖F M - F K‖ ^ 2
      rw [hnorm K M hM, kl_sum_Ico_eq_sum_range_add θ]
    rw [← tendsto_nhds_unique h1 h2]
    have hGK : G - F K = ((Lp.memLp G).sub (hY K)).toLp _ := by
      rw [MemLp.toLp_sub (Lp.memLp G) (hY K), Lp.toLp_coeFn]
    rw [hGK, klNorm_toLp_sq]
    rfl
  refine ⟨G, Lp.memLp G, fun K => ⟨((Lp.memLp G).sub (hY K)).integrable_sq, hlimK K⟩, ?_⟩
  simp_rw [hlimK]
  exact tendsto_sum_nat_add θ

/-! ### Pointwise law, moments of the diffusivity, covariance -/

/-- One term `√θ_n ξ_n f_n(x)` is `N(0, θ_n f_n(x)²)` (Giles 2015, §7.2, p. 53, l. 2255–2262). -/
lemma map_klTerm {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) (f : ℕ → D → ℝ) (x : D) (n : ℕ) :
    stdNormalSeq.map (fun z : ℕ → ℝ => Real.sqrt (θ n) * z n * f n x) =
      gaussianReal 0 (θ n * f n x ^ 2).toNNReal := by
  have hcomp : (fun z : ℕ → ℝ => Real.sqrt (θ n) * z n * f n x) =
      (fun y => (Real.sqrt (θ n) * f n x) * y) ∘ (fun z : ℕ → ℝ => z n) := by
    funext z
    simp only [Function.comp_apply]
    ring
  rw [hcomp, ← Measure.map_map (by fun_prop) (measurePreserving_eval_stdNormalSeq n).measurable,
    (measurePreserving_eval_stdNormalSeq n).map_eq, gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp only [NNReal.coe_mk, mul_one, Real.coe_toNNReal', mul_pow, Real.sq_sqrt (hθ n)]
  exact (max_eq_left (mul_nonneg (hθ n) (sq_nonneg _))).symm

/-- **The truncated field is Gaussian at each point** (Giles 2015, §7.2, p. 53, l. 2255–2262:
"`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)` … `ξ_n` are independent unit Normal random
variables", truncated after `K` terms, l. 2266–2267).  For `θ_n ≥ 0` and every `x`, `Y_K(·, x)`, a
sum of independent Gaussians, has law `N(0, ∑_{n<K} θ_n f_n(x)²)`. -/
theorem map_klField_eq_gaussianReal {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) (f : ℕ → D → ℝ) (K : ℕ)
    (x : D) :
    stdNormalSeq.map (fun z => klField θ f K z x) =
      gaussianReal 0 (∑ n ∈ range K, θ n * f n x ^ 2).toNNReal := by
  set X : ℕ → (ℕ → ℝ) → ℝ := fun n z => Real.sqrt (θ n) * z n * f n x with hXdef
  have hind : iIndepFun X stdNormalSeq :=
    iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
      (X := fun n y => Real.sqrt (θ n) * y * f n x) fun n => by fun_prop
  have hmeas : ∀ n, Measurable (X n) := fun n => by fun_prop
  have hfun : ∀ K, (fun z => klField θ f K z x) = ∑ j ∈ range K, X j := by
    intro K
    funext z
    rw [klField, Finset.sum_apply]
  induction K with
  | zero =>
    have h0 : (fun z => klField θ f 0 z x) = fun _ => 0 := by
      funext z
      rw [klField, Finset.sum_range_zero]
    rw [h0, Measure.map_const, measure_univ, one_smul, Finset.sum_range_zero,
      Real.toNNReal_zero, gaussianReal_zero_var]
  | succ K ih =>
    rw [hfun, Finset.sum_range_succ, gaussianReal_add_gaussianReal_of_indepFun
      (hind.indepFun_finsetSum_of_notMem hmeas Finset.notMem_range_self)
      (by rw [← hfun]; exact ih) (map_klTerm hθ f x K), add_zero, Finset.sum_range_succ,
      Real.toNNReal_add (Finset.sum_nonneg fun n _ => mul_nonneg (hθ n) (sq_nonneg _))
        (mul_nonneg (hθ K) (sq_nonneg _))]

/-- **The moments of the truncated diffusivity are bounded uniformly in the level** (Giles 2015,
§7.2, pp. 51–53, l. 2219–2220: "`κ` is often modelled as a lognormal random field", l. 2255–2268:
its logarithm is the Karhunen–Loève expansion "truncated after `K_ℓ` terms", and l. 2275–2276:
"the diffusivity is unbounded").  For `θ_n ≥ 0`, every real `p` and every `K`, `κ_K(x)^p` is
integrable and `E[κ_K(x)^p] = E[exp(p Y_K(x))] = exp(p² σ_K(x)²/2)` with
`σ_K(x)² = ∑_{n<K} θ_n f_n(x)²`; under the Mercer expansion `R(x, x) = ∑ θ_n f_n(x)²` this is at
most `exp(p² R(x, x)/2)`, a bound independent of `K`. -/
theorem klDiffusivity_moment {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) (f : ℕ → D → ℝ)
    {R : D → D → ℝ} {x : D} (hR : HasSum (fun n => θ n * f n x * f n x) (R x x)) (p : ℝ)
    (K : ℕ) :
    Integrable (fun z => klDiffusivity θ f K z x ^ p) stdNormalSeq ∧
      ∫ z, klDiffusivity θ f K z x ^ p ∂stdNormalSeq =
        Real.exp (p ^ 2 * (∑ n ∈ range K, θ n * f n x ^ 2) / 2) ∧
      Real.exp (p ^ 2 * (∑ n ∈ range K, θ n * f n x ^ 2) / 2) ≤ Real.exp (p ^ 2 * R x x / 2) := by
  have hpow : ∀ z, klDiffusivity θ f K z x ^ p = Real.exp (p * klField θ f K z x) := by
    intro z
    rw [klDiffusivity, ← Real.exp_mul, mul_comm]
  simp_rw [hpow]
  have hnn : 0 ≤ ∑ n ∈ range K, θ n * f n x ^ 2 :=
    Finset.sum_nonneg fun n _ => mul_nonneg (hθ n) (sq_nonneg _)
  have hmgf := mgf_gaussianReal (map_klField_eq_gaussianReal hθ f K x) p
  rw [Real.coe_toNNReal _ hnn, zero_mul, zero_add] at hmgf
  have hval : Real.exp ((∑ n ∈ range K, θ n * f n x ^ 2) * p ^ 2 / 2) =
      Real.exp (p ^ 2 * (∑ n ∈ range K, θ n * f n x ^ 2) / 2) := by
    congr 1
    ring
  refine ⟨mgf_pos_iff.1 (hmgf ▸ Real.exp_pos _), ?_, ?_⟩
  · rw [← hval, ← hmgf]
    rfl
  · have hle : ∑ n ∈ range K, θ n * f n x ^ 2 ≤ R x x := by
      have h' : ∑ n ∈ range K, θ n * f n x ^ 2 = ∑ n ∈ range K, θ n * f n x * f n x :=
        Finset.sum_congr rfl fun n _ => by ring
      rw [h']
      exact sum_le_hasSum (range K) (fun n _ => by nlinarith [hθ n, sq_nonneg (f n x)]) hR
    gcongr

/-- Expansion of `Y_K(x) Y_K(y)` (used for Giles 2015, §7.2, p. 53, l. 2255–2262). -/
lemma klField_mul_eq (θ : ℕ → ℝ) (f : ℕ → D → ℝ) (K : ℕ) (x y : D) (z : ℕ → ℝ) :
    klField θ f K z x * klField θ f K z y = ∑ n ∈ range K, ∑ m ∈ range K,
      (Real.sqrt (θ n) * f n x * (Real.sqrt (θ m) * f m y)) * (z n * z m) := by
  rw [klField, klField, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring

/-- **The covariance of the truncated field** (Giles 2015, §7.2, p. 53, l. 2255–2262: "`R(x, y)` …
`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`, where `θ_n` are the eigenvalues of `R(x, y)` …, `f_n`
are the corresponding eigenfunctions, and `ξ_n` are independent unit Normal random variables").
For `θ_n ≥ 0` and all `x, y`, `Y_K(x) Y_K(y)` is integrable and
`E[Y_K(x) Y_K(y)] = ∑_{n<K} θ_n f_n(x) f_n(y)`. -/
theorem integral_klField_mul {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) (f : ℕ → D → ℝ) (K : ℕ)
    (x y : D) :
    Integrable (fun z => klField θ f K z x * klField θ f K z y) stdNormalSeq ∧
      ∫ z, klField θ f K z x * klField θ f K z y ∂stdNormalSeq =
        ∑ n ∈ range K, θ n * f n x * f n y := by
  simp_rw [klField_mul_eq]
  have hint : ∀ n m, Integrable (fun z : ℕ → ℝ =>
      (Real.sqrt (θ n) * f n x * (Real.sqrt (θ m) * f m y)) * (z n * z m)) stdNormalSeq :=
    fun n m => (integral_mul_eval_stdNormalSeq n m).1.const_mul _
  refine ⟨integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m, ?_⟩
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_finsetSum _ fun m _ => hint n m]
  simp_rw [integral_const_mul, (integral_mul_eval_stdNormalSeq n _).2, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq (range K) n, if_pos hn]
  have := Real.mul_self_sqrt (hθ n)
  linear_combination f n x * f n y * this

/-- **The truncated covariance tends to `R`** (Giles 2015, §7.2, p. 53, l. 2255–2262, and
l. 2266–2268: "the expansion is truncated after `K_ℓ` terms, with `K_ℓ` increasing with level").
Under the Mercer expansion `R(x, y) = ∑ θ_n f_n(x) f_n(y)`,
`E[Y_K(x) Y_K(y)] → R(x, y)` as `K → ∞`. -/
theorem tendsto_integral_klField_mul {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) (f : ℕ → D → ℝ)
    {R : D → D → ℝ} {x y : D} (hR : HasSum (fun n => θ n * f n x * f n y) (R x y)) :
    Tendsto (fun K => ∫ z, klField θ f K z x * klField θ f K z y ∂stdNormalSeq) atTop
      (𝓝 (R x y)) := by
  simp_rw [fun K => (integral_klField_mul hθ f K x y).2]
  exact hR.tendsto_sum_nat

/-- **The Karhunen–Loève hypotheses are satisfiable** (for Giles 2015, §7.2, p. 53,
l. 2256–2262: "`θ_n` are the eigenvalues of `R(x, y)` …, `f_n` are the corresponding
eigenfunctions").  On `D = ℕ` with the (s-finite) counting measure, `f_n = 1_{{n}}` is an
orthonormal family in `L²`, and for every `θ` it is an eigenfunction of the integral operator of
`R(x, y) = θ_x δ_{xy}` with eigenvalue `θ_n` (`∫ R(x, y) f_n(y) dy = θ_n f_n(x)`), and the expansion
`∑ θ_n f_n(x) f_n(y)` converges to `R(x, y)`.  This witness is a discrete diagonal kernel, not a
stationary covariance `r(x − y)` on a domain of `ℝ^d`. -/
theorem kl_hypotheses_satisfiable :
    SFinite (Measure.count : Measure ℕ) ∧
    ∃ f : ℕ → ℕ → ℝ, (∀ n, MemLp (f n) 2 Measure.count) ∧
      (∀ n m, ∫ x, f n x * f m x ∂Measure.count = if n = m then 1 else 0) ∧
      (∀ θ : ℕ → ℝ, ∀ n x,
        ∫ y, (if x = y then θ x else 0) * f n y ∂Measure.count = θ n * f n x) ∧
      ∀ θ : ℕ → ℝ, ∀ x y, HasSum (fun n => θ n * f n x * f n y) (if x = y then θ x else 0) := by
  refine ⟨inferInstance, fun n => ({n} : Set ℕ).indicator fun _ => (1 : ℝ), fun n => ?_,
    fun n m => ?_, fun θ n x => ?_, fun θ x y => ?_⟩
  · exact memLp_indicator_const 2 (measurableSet_singleton n) 1 (Or.inr (by simp))
  · split_ifs with h
    · subst h
      have hsq : (fun x => ({n} : Set ℕ).indicator (fun _ => (1 : ℝ)) x *
          ({n} : Set ℕ).indicator (fun _ => (1 : ℝ)) x) =
          ({n} : Set ℕ).indicator fun _ => (1 : ℝ) := by
        funext x
        by_cases hx : x = n <;> simp [Set.indicator, hx]
      rw [hsq, integral_indicator_const _ (measurableSet_singleton n)]
      simp [measureReal_def]
    · have h0 : (fun x => ({n} : Set ℕ).indicator (fun _ => (1 : ℝ)) x *
          ({m} : Set ℕ).indicator (fun _ => (1 : ℝ)) x) = fun _ => 0 := by
        funext x
        by_cases hx : x = n
        · subst hx
          simp [Set.indicator, h]
        · simp [Set.indicator, hx]
      rw [h0, integral_zero]
  · have h : (fun y => (if x = y then θ x else 0) * ({n} : Set ℕ).indicator (fun _ => (1 : ℝ)) y) =
        ({x} : Set ℕ).indicator fun _ => θ n * ({n} : Set ℕ).indicator (fun _ => (1 : ℝ)) x := by
      funext y
      by_cases hxy : x = y
      · subst hxy
        by_cases hn : x = n
        · subst hn
          simp
        · simp [Set.indicator, hn]
      · simp [Set.indicator, hxy, Ne.symm hxy]
    rw [h, integral_indicator_const _ (measurableSet_singleton x)]
    simp [measureReal_def]
  · have := hasSum_single (f := fun n => θ n * ({n} : Set ℕ).indicator (fun _ => (1 : ℝ)) x *
      ({n} : Set ℕ).indicator (fun _ => (1 : ℝ)) y) x
      (fun b hb => by simp [Set.indicator, Ne.symm hb])
    convert this using 1
    by_cases hxy : x = y
    · subst hxy
      simp
    · simp [hxy, Set.indicator, Ne.symm hxy]

end MLMC
