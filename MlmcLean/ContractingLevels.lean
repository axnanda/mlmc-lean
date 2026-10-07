import MlmcLean.GilesCorollaries

/-!
# Contracting SDEs with level-dependent time steps (Giles 2015, §10.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §10.1 "Markov
chains and limiting distributions" (p. 61): "A very similar approach can also be used for
contracting SDEs which converge to a limiting distribution.  For these, the level `ℓ` path will
perform a simulation for the time interval `[−T_ℓ, 0]`, using timestep `h_ℓ`.  The coarse and
fine paths will share the same driving Brownian path for the overlapping time interval
`[−T_{ℓ−1}, 0]`, and the contraction property will ensure that the multilevel variance decays
with level."  `contracting_sde_mlmc` (`MlmcLean/GilesCorollaries.lean`) treats a fixed time step;
here the step halves from level to level.

**Setting.**  `dX = a(X) dt + b(X) dW` in one dimension, with a `K_a`-Lipschitz dissipative drift,
`(x − y)(a(x) − a(y)) ≤ −κ (x − y)²`, a `K_b`-Lipschitz volatility (`K_b = 0`: additive noise),
and steps `h ≤ H` with the margin `K_b² + 2K_a²H + δ ≤ 2κ`, `δ > 0`.  The Euler–Maruyama step is
`emStep a b h x ΔW = x + a(x) h + b(x) ΔW`.

**The coupling.**  The `ξ_k ~ N(0, h)` are independent, `ξ_k` being the Brownian increment over
`[−(k + 1)h, −kh]`.  The fine path starts at `x₀` at time `−T_f = −N_f h` and its step ending at
time `−kh` uses `ξ_k`; the coarse path, with step `2h`, starts at `x₀` at time `−T_c = −2N_c h`
(`2N_c ≤ N_f`) and its step ending at time `−2kh` uses `ξ_{2k} + ξ_{2k+1}`.  The two paths share
the Brownian path on `[−T_c, 0]`; the fine path's initial segment `[−T_f, −T_c]` uses the
increments `ξ_{2N_c}, …, ξ_{N_f − 1}`, which the coarse path does not see.

**Results** (all constants explicit: `contractM`, `contractL`, `contractC₁`, `contractC₂`).
* `lintegral_sq_backIter_sub_le`: the chain is bounded in mean square, `E[(X − x₀)²] ≤ M`,
  uniformly in the number of steps and in `h ≤ H`.
* `lintegral_sq_fine_sub_coarse_le`, `integral_sq_fine_sub_coarse_le`:
  `E[(X^f_0 − X^c_0)²] ≤ C₁ h + C₂ (1 − hδ/4)^{N_c} ≤ C₁ h + C₂ e^{−δ T_c/8}`.  Proof: sampled
  every coarse step, the pair is a Markov chain driven by the pairs `(ξ_{2k+1}, ξ_{2k})`
  (`pairEM`, `backIter_two_mul`), and `W = (x − y)² + λ (x − x₀)²` satisfies
  `E[W'] ≤ (1 − hδ/4) W + O(h²)` (`lintegral_pairEM_drift`): one coarse step contracts `(x − y)²`
  by `1 − 2hδ` (`coarse_contraction_sq`), two fine steps differ from one coarse step by an `O(h²)`
  mean-square local error whose cross term with the contraction part is small because the second
  increment has mean zero (`pair_step_sq`, `pair_integrated_le`), and the drift bound for chains
  started in the past (`lintegral_backIter_drift`) iterates it.
* `variance_contractLevels_le`: with `h_ℓ = h₀ 2^{−ℓ}`, `N_ℓ` steps on level `ℓ`,
  `T_ℓ = N_ℓ h_ℓ`, `2N_ℓ ≤ N_{ℓ+1}`, and the level paths driven by standard normals
  (`contractPath`; the coarse path of a level-`(ℓ + 1)` sample is `contractPath ℓ (pairAvg z)`),
  `V_{ℓ+1} ≤ K_f² (C₁ h_{ℓ+1} + C₂ e^{−δ T_ℓ/8})` for `K_f`-Lipschitz payoffs.
* `variance_contractLevels_le_two_pow`: `β = 1` when `T_ℓ ≥ c ℓ` with `c δ ≥ 8 log 2`.
* `contracting_levels_mlmc`: Theorem 1 end to end.  The level means converge to some `P`, which
  is also the limit of the means under the stationary laws of the Euler–Maruyama chains with the
  steps `h_ℓ` (`contractLimit`, `tendsto_integral_contractPath_sub_limit`), and the multilevel
  estimator reaches mean square error `ε²` at cost `O(ε^{−2−2η})` for every `η > 0`.

**Deviations from the paper.**  One dimension.  The paper's "contracting SDEs" are made precise
by the Lipschitz, dissipativity and margin hypotheses.  The constants are explicit but not
optimised.  The cost of a sample is counted as its `N_ℓ` fine steps (the coarse path adds at most
half as many); since `T_ℓ` grows linearly, `N_ℓ` grows like `ℓ 2^ℓ`, so Theorem 1 is applied with
`γ = 1 + η`.  The target `P` is the limit along `h_ℓ → 0` of the means under the limiting
distributions of the discretised chains; that `P` is the mean under the invariant law of the SDE
is not proved: it needs SDE theory (the convergence of the invariant laws of the scheme as
`h → 0`) that the library does not have.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace MLMC

/-! ### The constants -/

/-- **The uniform mean-square bound of the Euler–Maruyama chain of a dissipative SDE** (Giles 2015,
§10.1, p. 61: "contracting SDEs which converge to a limiting distribution"):
`M = (2/δ)(2G²/δ + a(x₀)² H + b(x₀)²)` with `G = |a(x₀)|(1 + H K_a) + |b(x₀)| K_b`.  It bounds
`E[(X − x₀)²]` for the chain started at `x₀`, whatever the number of steps and the step `h ≤ H`
(`lintegral_sq_backIter_sub_le`). -/
noncomputable def contractM (a b : ℝ → ℝ) (Ka Kb : ℝ≥0) (δ H x₀ : ℝ) : ℝ :=
  2 / δ * (2 * (|a x₀| * (1 + H * Ka) + |b x₀| * Kb) ^ 2 / δ + (a x₀ ^ 2 * H + b x₀ ^ 2))

/-- **The local-error factor of the coupling** (Giles 2015, §10.1, p. 61):
`L = ((1 + K_b²)/δ + H) K_a² + (1 + (1 + K_b²)/δ) K_b²`.  Two fine Euler–Maruyama steps and one
coarse step from nearby points differ, beyond the contraction, by at most `h² L (a(x)² h + b(x)²)`
in mean square over the two Brownian increments (`pair_step_sq`, `pair_integrated_le`). -/
noncomputable def contractL (Ka Kb : ℝ≥0) (δ H : ℝ) : ℝ :=
  ((1 + (Kb : ℝ) ^ 2) / δ + H) * (Ka : ℝ) ^ 2 + (1 + (1 + (Kb : ℝ) ^ 2) / δ) * (Kb : ℝ) ^ 2

/-- **The constant `C₁`** of the bound `E[(X^f − X^c)²] ≤ C₁ h + C₂ (1 − hδ/4)^{N_c}` (Giles 2015,
§10.1, p. 61; `lintegral_sq_fine_sub_coarse_le`):
`C₁ = (8/δ) L (a(x₀)² H + b(x₀)² + 4 (K_a² H + K_b²) M)`, `L = contractL`, `M = contractM`. -/
noncomputable def contractC₁ (a b : ℝ → ℝ) (Ka Kb : ℝ≥0) (δ H x₀ : ℝ) : ℝ :=
  8 / δ * contractL Ka Kb δ H * (a x₀ ^ 2 * H + b x₀ ^ 2 +
    4 * ((Ka : ℝ) ^ 2 * H + (Kb : ℝ) ^ 2) * contractM a b Ka Kb δ H x₀)

/-- **The constant `C₂`** of the bound `E[(X^f − X^c)²] ≤ C₁ h + C₂ (1 − hδ/4)^{N_c}` (Giles 2015,
§10.1, p. 61; `lintegral_sq_fine_sub_coarse_le`): `C₂ = (1 + 8 H L (K_a² H + K_b²)/δ) M`,
`L = contractL`, `M = contractM`. -/
noncomputable def contractC₂ (a b : ℝ → ℝ) (Ka Kb : ℝ≥0) (δ H x₀ : ℝ) : ℝ :=
  (1 + 8 * H * contractL Ka Kb δ H * ((Ka : ℝ) ^ 2 * H + (Kb : ℝ) ^ 2) / δ) *
    contractM a b Ka Kb δ H x₀

/-- `contractM ≥ 0` for `δ > 0` and `H ≥ 0`. -/
lemma contractM_nonneg (a b : ℝ → ℝ) (Ka Kb : ℝ≥0) {δ H : ℝ} (hδ : 0 < δ) (hH : 0 ≤ H)
    (x₀ : ℝ) : 0 ≤ contractM a b Ka Kb δ H x₀ := by
  unfold contractM
  positivity

/-- `contractL ≥ 0` for `δ > 0` and `H ≥ 0`. -/
lemma contractL_nonneg (Ka Kb : ℝ≥0) {δ H : ℝ} (hδ : 0 < δ) (hH : 0 ≤ H) :
    0 ≤ contractL Ka Kb δ H := by
  unfold contractL
  positivity

/-- `contractC₁ ≥ 0` for `δ > 0` and `H ≥ 0`. -/
lemma contractC₁_nonneg (a b : ℝ → ℝ) (Ka Kb : ℝ≥0) {δ H : ℝ} (hδ : 0 < δ) (hH : 0 ≤ H)
    (x₀ : ℝ) : 0 ≤ contractC₁ a b Ka Kb δ H x₀ := by
  have := contractL_nonneg Ka Kb hδ hH
  have := contractM_nonneg a b Ka Kb hδ hH x₀
  unfold contractC₁
  positivity

/-- `contractC₂ ≥ 0` for `δ > 0` and `H ≥ 0`. -/
lemma contractC₂_nonneg (a b : ℝ → ℝ) (Ka Kb : ℝ≥0) {δ H : ℝ} (hδ : 0 < δ) (hH : 0 ≤ H)
    (x₀ : ℝ) : 0 ≤ contractC₂ a b Ka Kb δ H x₀ := by
  have := contractL_nonneg Ka Kb hδ hH
  have := contractM_nonneg a b Ka Kb hδ hH x₀
  unfold contractC₂
  positivity

/-! ### Gaussian moments -/

/-- `E[α₀ + α₁ W + α₂ W²] = α₀ + α₂ v` for `W ~ N(0, v)`, as a lower Lebesgue integral of a
nonnegative quadratic (used for the Brownian increments of Giles 2015, §10.1). -/
lemma lintegral_quadratic_gaussianReal (α₀ α₁ α₂ : ℝ) (v : ℝ≥0)
    (hpos : ∀ w, 0 ≤ α₀ + α₁ * w + α₂ * w ^ 2) :
    ∫⁻ w, ENNReal.ofReal (α₀ + α₁ * w + α₂ * w ^ 2) ∂gaussianReal 0 v =
      ENNReal.ofReal (α₀ + α₂ * v) := by
  have hL2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := memLp_id_gaussianReal' 2 (by norm_num)
  have h1 : Integrable (fun w : ℝ => w) (gaussianReal 0 v) := hL2.integrable one_le_two
  have h2 : Integrable (fun w : ℝ => w ^ 2) (gaussianReal 0 v) := hL2.integrable_sq
  have hmean : ∫ w, w ∂gaussianReal 0 v = 0 := integral_id_gaussianReal
  have hsq : ∫ w, w ^ 2 ∂gaussianReal 0 v = v := by
    simpa using integral_sq_affine_gaussianReal 0 1 v
  have i1 : Integrable (fun w : ℝ => α₀ + α₁ * w) (gaussianReal 0 v) :=
    (integrable_const _).add (h1.const_mul _)
  have i2 : Integrable (fun w : ℝ => α₂ * w ^ 2) (gaussianReal 0 v) := h2.const_mul _
  have hint : Integrable (fun w : ℝ => α₀ + α₁ * w + α₂ * w ^ 2) (gaussianReal 0 v) := i1.add i2
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hpos), integral_add i1 i2,
    integral_add (integrable_const _) (h1.const_mul _), integral_const, integral_const_mul,
    integral_const_mul, hmean, hsq]
  simp

/-- Three weighted squares of affine functions of `W ~ N(0, v)` and a constant:
`E[∑ cᵢ (Aᵢ + Bᵢ W)² + c₀] = ∑ cᵢ (Aᵢ² + Bᵢ² v) + c₀` for nonnegative weights (used for the
Brownian increments of Giles 2015, §10.1). -/
lemma lintegral_three_sq_gaussianReal {c₁ c₂ c₃ c₀ : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (h₃ : 0 ≤ c₃) (h₀ : 0 ≤ c₀) (A₁ B₁ A₂ B₂ A₃ B₃ : ℝ) (v : ℝ≥0) :
    ∫⁻ w, ENNReal.ofReal (c₁ * (A₁ + B₁ * w) ^ 2 + c₂ * (A₂ + B₂ * w) ^ 2 +
        c₃ * (A₃ + B₃ * w) ^ 2 + c₀) ∂gaussianReal 0 v =
      ENNReal.ofReal (c₁ * (A₁ ^ 2 + B₁ ^ 2 * v) + c₂ * (A₂ ^ 2 + B₂ ^ 2 * v) +
        c₃ * (A₃ ^ 2 + B₃ ^ 2 * v) + c₀) := by
  have e : ∀ w : ℝ, c₁ * (A₁ + B₁ * w) ^ 2 + c₂ * (A₂ + B₂ * w) ^ 2 + c₃ * (A₃ + B₃ * w) ^ 2 + c₀ =
      (c₁ * A₁ ^ 2 + c₂ * A₂ ^ 2 + c₃ * A₃ ^ 2 + c₀) +
        (2 * (c₁ * A₁ * B₁ + c₂ * A₂ * B₂ + c₃ * A₃ * B₃)) * w +
        (c₁ * B₁ ^ 2 + c₂ * B₂ ^ 2 + c₃ * B₃ ^ 2) * w ^ 2 := fun w => by ring
  simp_rw [e]
  rw [lintegral_quadratic_gaussianReal]
  · congr 1
    ring
  · intro w
    rw [← e]
    positivity

/-! ### A drift bound for chains started in the past -/

section drift

variable {α E Ω : Type*} [MeasurableSpace α] [mE : MeasurableSpace E] [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- The chain started `n` steps before time `−m` (Giles 2015, §10.1, Figure 10.12), from a starting
point that is measurable for `𝓕 (m + n)`, is measurable for `𝓕 m`, when the noise `ζ_k` is
`𝓕 k`-measurable and the σ-algebras `𝓕` decrease. -/
lemma measurable_backIter_filtration {Φ : α → E → α}
    (hΦ : Measurable fun q : α × E => Φ q.1 q.2) (𝓕 : ℕ → MeasurableSpace Ω)
    (hanti : ∀ m, 𝓕 (m + 1) ≤ 𝓕 m) {ζ : ℕ → Ω → E} (hζ : ∀ m, Measurable[𝓕 m] (ζ m)) (n : ℕ) :
    ∀ (m : ℕ) {U : Ω → α}, Measurable[𝓕 (m + n)] U →
      Measurable[𝓕 m] fun ω => backIter Φ n (fun k => ζ (k + m) ω) (U ω) := by
  induction n with
  | zero =>
    intro m U hU
    exact hU
  | succ n ih =>
    intro m U hU
    have h1 : Measurable[𝓕 (m + 1)] fun ω => backIter Φ n (fun k => ζ (k + (m + 1)) ω) (U ω) :=
      ih (m + 1) (by rwa [show m + 1 + n = m + (n + 1) by omega])
    have h2 := h1.mono (hanti m) le_rfl
    have e : (fun ω => backIter Φ (n + 1) (fun k => ζ (k + m) ω) (U ω)) =
        fun ω => Φ (backIter Φ n (fun k => ζ (k + (m + 1)) ω) (U ω)) (ζ m ω) :=
      funext fun ω => backIter_succ_shift Φ n m (fun k => ζ k ω) (U ω)
    rw [e]
    exact hΦ.comp (h2.prodMk (hζ m))

/-- **A drift (Lyapunov) bound for a chain started in the past** (Giles 2015, §10.1, Figure 10.12).
Let the step `Φ(·, e)` satisfy `E[V(Φ(z, ζ))] ≤ r V(z) + K` for every `z`, where the noise `ζ`
has law `ν`, and let the noises `ζ_k` be `𝓕 k`-measurable for decreasing σ-algebras `𝓕 k` such
that `𝓕 (k + 1)` is independent of `ζ_k`.  Then the chain started `n` steps before time `−m` at
a point `U` that is `𝓕 (m + n)`-measurable satisfies `E[V(X)] ≤ rⁿ E[V(U)] + K ∑_{j<n} r^j`. -/
lemma lintegral_backIter_drift {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure E}
    {Φ : α → E → α} (hΦ : Measurable fun q : α × E => Φ q.1 q.2) {V : α → ℝ≥0∞}
    (hV : Measurable V) {r K : ℝ≥0∞} (hdrift : ∀ z, ∫⁻ e, V (Φ z e) ∂ν ≤ r * V z + K)
    (𝓕 : ℕ → MeasurableSpace Ω) (h𝓕 : ∀ m, 𝓕 m ≤ mΩ) (hanti : ∀ m, 𝓕 (m + 1) ≤ 𝓕 m)
    {ζ : ℕ → Ω → E} (hζ : ∀ m, Measurable[𝓕 m] (ζ m))
    (hind : ∀ m, Indep (𝓕 (m + 1)) (MeasurableSpace.comap (ζ m) mE) μ)
    (hlaw : ∀ m, μ.map (ζ m) = ν) (n : ℕ) :
    ∀ (m : ℕ) {U : Ω → α}, Measurable[𝓕 (m + n)] U →
      ∫⁻ ω, V (backIter Φ n (fun k => ζ (k + m) ω) (U ω)) ∂μ ≤
        r ^ n * ∫⁻ ω, V (U ω) ∂μ + K * ∑ j ∈ range n, r ^ j := by
  have : IsProbabilityMeasure ν := by
    rw [← hlaw 0]
    exact Measure.isProbabilityMeasure_map ((hζ 0).mono (h𝓕 0) le_rfl).aemeasurable
  induction n with
  | zero =>
    intro m U _
    rw [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    exact le_of_eq (lintegral_congr fun ω => by rw [backIter_zero])
  | succ n ih =>
    intro m U hU
    have hU' : Measurable[𝓕 (m + 1 + n)] U := by rwa [show m + 1 + n = m + (n + 1) by omega]
    obtain ⟨Y, hY_def⟩ : ∃ Y : Ω → α,
        Y = fun ω => backIter Φ n (fun k => ζ (k + (m + 1)) ω) (U ω) := ⟨_, rfl⟩
    have hY : Measurable[𝓕 (m + 1)] Y := by
      rw [hY_def]
      exact measurable_backIter_filtration hΦ 𝓕 hanti hζ n (m + 1) hU'
    have hYm : Measurable Y := hY.mono (h𝓕 _) le_rfl
    have hζm : Measurable (ζ m) := (hζ m).mono (h𝓕 m) le_rfl
    have hindY : IndepFun Y (ζ m) μ := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left (hind m) hY.comap_le
    have hmap : μ.map (fun ω => (Y ω, ζ m ω)) = (μ.map Y).prod ν := by
      rw [← hlaw m]
      exact (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hζm.aemeasurable).1 hindY
    have hVΦ : Measurable fun q : α × E => V (Φ q.1 q.2) := hV.comp hΦ
    have : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hYm.aemeasurable
    have hstep : ∀ ω, V (backIter Φ (n + 1) (fun k => ζ (k + m) ω) (U ω)) = V (Φ (Y ω) (ζ m ω)) :=
      fun ω => by rw [backIter_succ_shift Φ n m (fun k => ζ k ω) (U ω), hY_def]
    calc ∫⁻ ω, V (backIter Φ (n + 1) (fun k => ζ (k + m) ω) (U ω)) ∂μ
        = ∫⁻ ω, V (Φ (Y ω) (ζ m ω)) ∂μ := lintegral_congr hstep
      _ = ∫⁻ q, V (Φ q.1 q.2) ∂(μ.map fun ω => (Y ω, ζ m ω)) :=
          (lintegral_map hVΦ (hYm.prodMk hζm)).symm
      _ = ∫⁻ q, V (Φ q.1 q.2) ∂((μ.map Y).prod ν) := by rw [hmap]
      _ = ∫⁻ y, ∫⁻ e, V (Φ y e) ∂ν ∂(μ.map Y) := lintegral_prod _ hVΦ.aemeasurable
      _ ≤ ∫⁻ y, (r * V y + K) ∂(μ.map Y) := lintegral_mono fun y => hdrift y
      _ = r * ∫⁻ ω, V (Y ω) ∂μ + K := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hV, lintegral_const,
            measure_univ, mul_one, lintegral_map hV hYm]
      _ ≤ r * (r ^ n * ∫⁻ ω, V (U ω) ∂μ + K * ∑ j ∈ range n, r ^ j) + K := by
          gcongr
          rw [hY_def]
          exact ih (m + 1) hU'
      _ = r ^ (n + 1) * ∫⁻ ω, V (U ω) ∂μ + K * ∑ j ∈ range (n + 1), r ^ j := by
          have hs : ∑ j ∈ range (n + 1), r ^ j = (∑ j ∈ range n, r ^ j) * r + 1 := by
            rw [Finset.sum_range_succ', Finset.sum_mul]
            simp [pow_succ]
          rw [hs]
          ring

end drift

/-- `K ∑_{j<n} r^j ≤ K/(1 − r)` in `ℝ≥0∞`, for `K ≥ 0` and `0 ≤ r < 1`. -/
lemma ofReal_mul_geom_le {K r : ℝ} (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ENNReal.ofReal K * ∑ j ∈ range n, ENNReal.ofReal r ^ j ≤ ENNReal.ofReal (K / (1 - r)) := by
  have e : ∑ j ∈ range n, ENNReal.ofReal r ^ j = ENNReal.ofReal (∑ j ∈ range n, r ^ j) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => pow_nonneg hr0 j)]
    exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_pow hr0 j).symm
  rw [e, ← ENNReal.ofReal_mul hK]
  apply ENNReal.ofReal_le_ofReal
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (geom_sum_le_of_lt_one hr0 hr1 n) hK

/-! ### One coarse step against two fine steps -/

section algebra

variable {a b : ℝ → ℝ} {Ka Kb : ℝ≥0} {κ δ H : ℝ}

/-- `(g x − g y)² ≤ K² (x − y)²` for a `K`-Lipschitz function `g`. -/
lemma sq_sub_le_of_lipschitzWith {g : ℝ → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (x y : ℝ) :
    (g x - g y) ^ 2 ≤ (K : ℝ) ^ 2 * (x - y) ^ 2 := by
  have h1 := hg.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq] at h1
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rwa [mul_pow, sq_abs, sq_abs] at h2

/-- `|g x − g y| ≤ K |x − y|` for a `K`-Lipschitz function `g`. -/
lemma abs_sub_le_of_lipschitzWith {g : ℝ → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (x y : ℝ) :
    |g x - g y| ≤ K * |x - y| := by
  have h1 := hg.dist_le_mul x y
  rwa [Real.dist_eq, Real.dist_eq] at h1

/-- A dissipative `K_a`-Lipschitz drift, `(x − y)(a(x) − a(y)) ≤ −κ (x − y)²`, has `κ ≤ K_a`. -/
lemma le_of_dissipative (ha : LipschitzWith Ka a)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) : κ ≤ Ka := by
  have h1 := hdiss 1 0
  have h2 := abs_sub_le_of_lipschitzWith ha 1 0
  norm_num at h1 h2
  linarith [neg_abs_le (a 1 - a 0)]

/-- With the margin `K_b² + 2K_a²H + δ ≤ 2κ`, a dissipative `K_a`-Lipschitz drift and
`0 ≤ h ≤ H`: `hδ ≤ 1/2`. -/
lemma mul_le_half_of_margin (ha : LipschitzWith Ka a)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) {h : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * H + δ ≤ 2 * κ) :
    h * δ ≤ 1 / 2 := by
  have s1 : δ ≤ 2 * κ - 2 * (Ka : ℝ) ^ 2 * H := by nlinarith [sq_nonneg (Kb : ℝ)]
  have s2 := mul_le_mul_of_nonneg_left s1 hh
  have s3 := mul_le_mul_of_nonneg_left (le_of_dissipative ha hdiss) hh
  have s4 : h * h * (Ka : ℝ) ^ 2 ≤ h * H * (Ka : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhH hh) (sq_nonneg _)
  nlinarith [sq_nonneg (h * Ka - 1 / 2)]

/-- **One Euler–Maruyama step of a dissipative SDE drifts towards the start** (Giles 2015, §10.1,
p. 61): for `ΔW ~ N(0, h)`, `0 ≤ h ≤ H` and the margin `K_b² + 2K_a²H + δ ≤ 2κ`,
`E[(x + a(x)h + b(x)ΔW − x₀)²] = (x − x₀ + a(x) h)² + b(x)² h ≤ (1 − hδ/2)(x − x₀)² + hδM/2`,
`M = contractM`. -/
lemma emStep_drift_sq (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h : ℝ}
    (hh : 0 ≤ h) (hhH : h ≤ H) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * H + δ ≤ 2 * κ)
    (x₀ x : ℝ) :
    (x - x₀ + a x * h) ^ 2 + b x ^ 2 * h ≤
      (1 - h * δ / 2) * (x - x₀) ^ 2 + h * δ * contractM a b Ka Kb δ H x₀ / 2 := by
  obtain ⟨A, hA⟩ : ∃ A, A = a x₀ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = b x₀ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = x - x₀ := ⟨_, rfl⟩
  obtain ⟨dA, hdA⟩ : ∃ dA, dA = a x - a x₀ := ⟨_, rfl⟩
  obtain ⟨dB, hdB⟩ : ∃ dB, dB = b x - b x₀ := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = |A| * (1 + H * Ka) + |B| * Kb := ⟨_, rfl⟩
  have hax : a x = A + dA := by rw [hA, hdA]; ring
  have hbx : b x = B + dB := by rw [hB, hdB]; ring
  have hM : h * δ * contractM a b Ka Kb δ H x₀ / 2 =
      2 * h * G ^ 2 / δ + h * (A ^ 2 * H + B ^ 2) := by
    rw [contractM, ← hA, ← hB, ← hG]
    field_simp
  have hKa : (0 : ℝ) ≤ Ka := Ka.2
  have hKb : (0 : ℝ) ≤ Kb := Kb.2
  have h1 : u * dA ≤ -(κ * u ^ 2) := by rw [hu, hdA]; exact hdiss x x₀
  have h2 : |dA| ≤ Ka * |u| := by rw [hu, hdA]; exact abs_sub_le_of_lipschitzWith ha x x₀
  have h3 : |dB| ≤ Kb * |u| := by rw [hu, hdB]; exact abs_sub_le_of_lipschitzWith hb x x₀
  have hdA2 : dA ^ 2 ≤ (Ka : ℝ) ^ 2 * u ^ 2 := by
    rw [← sq_abs dA, ← sq_abs u, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hdB2 : dB ^ 2 ≤ (Kb : ℝ) ^ 2 * u ^ 2 := by
    rw [← sq_abs dB, ← sq_abs u, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hAdA : A * dA ≤ |A| * (Ka * |u|) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
  have hBdB : B * dB ≤ |B| * (Kb * |u|) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
  have hAu : A * u ≤ |A| * |u| := by rw [← abs_mul]; exact le_abs_self _
  -- the contraction factor
  have hρ : 1 - 2 * h * κ + h ^ 2 * (Ka : ℝ) ^ 2 + h * (Kb : ℝ) ^ 2 ≤ 1 - h * δ := by
    have : h * ((Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * H + δ) ≤ h * (2 * κ) :=
      mul_le_mul_of_nonneg_left hmargin hh
    have : h * (h * (Ka : ℝ) ^ 2) ≤ h * (H * (Ka : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hhH (sq_nonneg _)) hh
    nlinarith [mul_nonneg (mul_nonneg hh hh) (sq_nonneg (Ka : ℝ))]
  -- the linear term
  have hlin : |A| + h * |A| * Ka + |B| * Kb ≤ G := by
    rw [hG]
    nlinarith [mul_le_mul_of_nonneg_left hhH (mul_nonneg (abs_nonneg A) hKa)]
  have hyoung : 2 * h * |u| * G ≤ h * δ / 2 * u ^ 2 + 2 * h * G ^ 2 / δ := by
    have : 0 ≤ h / (2 * δ) * (δ * |u| - 2 * G) ^ 2 := by positivity
    have e : h / (2 * δ) * (δ * |u| - 2 * G) ^ 2 =
        h * δ / 2 * |u| ^ 2 - 2 * h * |u| * G + 2 * h * G ^ 2 / δ := by
      field_simp
      ring
    rw [sq_abs] at e
    linarith
  have hconst : h ^ 2 * A ^ 2 + h * B ^ 2 ≤ h * (A ^ 2 * H + B ^ 2) := by
    have : h * (h * A ^ 2) ≤ h * (H * A ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hhH (sq_nonneg A)) hh
    linarith
  rw [hax, hbx, ← hu, hM]
  calc (u + (A + dA) * h) ^ 2 + (B + dB) ^ 2 * h
      = u ^ 2 + 2 * h * (u * dA) + 2 * h * (A * u) + h ^ 2 * (A ^ 2 + 2 * (A * dA) + dA ^ 2) +
          h * (B ^ 2 + 2 * (B * dB) + dB ^ 2) := by ring
    _ ≤ u ^ 2 + 2 * h * (-(κ * u ^ 2)) + 2 * h * (|A| * |u|) +
          h ^ 2 * (A ^ 2 + 2 * (|A| * (Ka * |u|)) + (Ka : ℝ) ^ 2 * u ^ 2) +
          h * (B ^ 2 + 2 * (|B| * (Kb * |u|)) + (Kb : ℝ) ^ 2 * u ^ 2) := by
        have e1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * h)
        have e2 := mul_le_mul_of_nonneg_left hAu (by linarith : (0 : ℝ) ≤ 2 * h)
        have e3 : h ^ 2 * (A ^ 2 + 2 * (A * dA) + dA ^ 2) ≤
            h ^ 2 * (A ^ 2 + 2 * (|A| * (Ka * |u|)) + (Ka : ℝ) ^ 2 * u ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg h)
        have e4 : h * (B ^ 2 + 2 * (B * dB) + dB ^ 2) ≤
            h * (B ^ 2 + 2 * (|B| * (Kb * |u|)) + (Kb : ℝ) ^ 2 * u ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hh
        linarith
    _ = (1 - 2 * h * κ + h ^ 2 * (Ka : ℝ) ^ 2 + h * (Kb : ℝ) ^ 2) * u ^ 2 +
          2 * h * |u| * (|A| + h * |A| * Ka + |B| * Kb) + (h ^ 2 * A ^ 2 + h * B ^ 2) := by ring
    _ ≤ (1 - h * δ) * u ^ 2 + 2 * h * |u| * G + h * (A ^ 2 * H + B ^ 2) := by
        have e1 := mul_le_mul_of_nonneg_right hρ (sq_nonneg u)
        have e2 := mul_le_mul_of_nonneg_left hlin
          (mul_nonneg (by linarith) (abs_nonneg u) : (0 : ℝ) ≤ 2 * h * |u|)
        linarith
    _ ≤ (1 - h * δ / 2) * u ^ 2 + (2 * h * G ^ 2 / δ + h * (A ^ 2 * H + B ^ 2)) := by
        linarith

/-- **One coarse Euler–Maruyama step contracts the difference in mean square** (Giles 2015, §10.1,
p. 61: "the contraction property"): for the step `2h`, `0 ≤ h ≤ H` and the margin
`K_b² + 2K_a²H + δ ≤ 2κ`,
`(x − y + 2h(a(x) − a(y)))² + 2h(b(x) − b(y))² ≤ (1 − 2hδ)(x − y)²`. -/
lemma coarse_contraction_sq (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) {h : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * H + δ ≤ 2 * κ) (x y : ℝ) :
    (x - y + 2 * h * (a x - a y)) ^ 2 + 2 * h * (b x - b y) ^ 2 ≤
      (1 - 2 * h * δ) * (x - y) ^ 2 := by
  have e1 := mul_le_mul_of_nonneg_left (hdiss x y) (by linarith : (0 : ℝ) ≤ 4 * h)
  have e2 := mul_le_mul_of_nonneg_left (sq_sub_le_of_lipschitzWith ha x y)
    (by positivity : (0 : ℝ) ≤ 4 * h ^ 2)
  have e3 := mul_le_mul_of_nonneg_left (sq_sub_le_of_lipschitzWith hb x y)
    (by linarith : (0 : ℝ) ≤ 2 * h)
  have e4 := mul_le_mul_of_nonneg_left hmargin
    (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * h) (sq_nonneg (x - y)))
  have e5 : 4 * h ^ 2 * (Ka : ℝ) ^ 2 * (x - y) ^ 2 ≤ 4 * h * H * (Ka : ℝ) ^ 2 * (x - y) ^ 2 := by
    have : h * h ≤ h * H := mul_le_mul_of_nonneg_left hhH hh
    have h0 : 0 ≤ 4 * (Ka : ℝ) ^ 2 * (x - y) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  linarith

/-- **The local error of two fine steps against one coarse step, pointwise in the first
increment** (Giles 2015, §10.1, p. 61).  With `x₁ = x + a(x) h + b(x) u` (the first fine step),
`θ ι = 1` and `θ > 0`, the coefficients of the second increment `v` in `x₂ − y₂ = P + Q v` (two
fine steps from `x` against one coarse step from `y` with the increment `u + v`),
`P = x₁ + a(x₁)h − y − 2a(y)h − b(y)u` and `Q = b(x₁) − b(y)`, satisfy
`P² + Q² h ≤ (1 + θh)(C + βu)² + (1 + θ) h β² + h((ι + H)K_a² + (1 + ι)K_b²)(a(x)h + b(x)u)²`,
`C = x − y + 2h(a(x) − a(y))`, `β = b(x) − b(y)`.  The local error `h(a(x₁) − a(x))` is coupled
to the contraction part by Young's inequality with weight `θh`; the noise mismatch
`(b(x₁) − b(x)) v` only through `β`, since the second increment has mean zero. -/
lemma pair_step_sq (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b) {θ ι : ℝ} (hθ : 0 < θ)
    (hθι : θ * ι = 1) {h : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) (x y u : ℝ) :
    (emStep a b h x u + a (emStep a b h x u) * h - y - 2 * a y * h - b y * u) ^ 2 +
        (b (emStep a b h x u) - b y) ^ 2 * h ≤
      (1 + θ * h) * ((x - y + 2 * h * (a x - a y)) + (b x - b y) * u) ^ 2 +
        (1 + θ) * h * (b x - b y) ^ 2 +
        h * ((ι + H) * (Ka : ℝ) ^ 2 + (1 + ι) * (Kb : ℝ) ^ 2) * (a x * h + b x * u) ^ 2 := by
  have hι : 0 < ι := by
    by_contra hneg
    have : θ * ι ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ.le (not_lt.1 hneg)
    linarith
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ = emStep a b h x u := ⟨_, rfl⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, P₀ = (x - y + 2 * h * (a x - a y)) + (b x - b y) * u := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = a x₁ - a x := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = b x₁ - b x := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = b x - b y := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = a x * h + b x * u := ⟨_, rfl⟩
  have hxS : x₁ - x = S := by rw [hx₁, hS, emStep]; ring
  have eP : x₁ + a x₁ * h - y - 2 * a y * h - b y * u = P₀ + h * A := by
    rw [hP₀, hA, hx₁, emStep]; ring
  have eQ : b x₁ - b y = β + B := by rw [hβ, hB]; ring
  have hA2 : A ^ 2 ≤ (Ka : ℝ) ^ 2 * S ^ 2 := by
    rw [hA, ← hxS]; exact sq_sub_le_of_lipschitzWith ha x₁ x
  have hB2 : B ^ 2 ≤ (Kb : ℝ) ^ 2 * S ^ 2 := by
    rw [hB, ← hxS]; exact sq_sub_le_of_lipschitzWith hb x₁ x
  have y1 : 2 * h * P₀ * A ≤ h * θ * P₀ ^ 2 + h * ι * A ^ 2 := by
    have h0 : 0 ≤ h * ι * (θ * P₀ - A) ^ 2 := by positivity
    have e : h * ι * (θ * P₀ - A) ^ 2 =
        h * (θ * ι) * θ * P₀ ^ 2 - 2 * h * (θ * ι) * P₀ * A + h * ι * A ^ 2 := by ring
    rw [hθι] at e
    linarith
  have y2 : 2 * β * B ≤ θ * β ^ 2 + ι * B ^ 2 := by
    have h0 : 0 ≤ ι * (θ * β - B) ^ 2 := by positivity
    have e : ι * (θ * β - B) ^ 2 = (θ * ι) * θ * β ^ 2 - 2 * (θ * ι) * β * B + ι * B ^ 2 := by
      ring
    rw [hθι] at e
    linarith
  rw [← hx₁, eP, eQ, ← hP₀, ← hβ, ← hS]
  have e1 := mul_le_mul_of_nonneg_left y2 hh
  have e2 := mul_le_mul_of_nonneg_left hA2 (by positivity : (0 : ℝ) ≤ h * ι + h ^ 2)
  have e3 := mul_le_mul_of_nonneg_left hB2 (by positivity : (0 : ℝ) ≤ h * (1 + ι))
  have e4 : (h * ι + h ^ 2) * ((Ka : ℝ) ^ 2 * S ^ 2) ≤ h * (ι + H) * ((Ka : ℝ) ^ 2 * S ^ 2) := by
    have : h * ι + h ^ 2 ≤ h * (ι + H) := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  nlinarith

/-- **The Lyapunov bound for one coarse step of the coupled pair, after integrating out both
increments** (Giles 2015, §10.1, p. 61; the real-arithmetic part of `lintegral_pairEM_drift`).
With `θ (1 + K_b²) = δ`, `λ δ = 8 h L K₂` (`L = contractL`, `K₂ = K_a² H + K_b²`),
`r₁ = 1 − hδ/2` and `M = contractM`, the bound on the expectation of
`(x₂ − y₂)² + λ (x₂ − x₀)²` given by `pair_step_sq` and `emStep_drift_sq` is at most
`(1 − hδ/4)((x − y)² + λ (x − x₀)²) + 2h² L (S + 4 K₂ M)`, `S = a(x₀)² H + b(x₀)²`. -/
lemma pair_integrated_le (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h : ℝ}
    (hh : 0 ≤ h) (hhH : h ≤ H) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * H + δ ≤ 2 * κ)
    {θ lam : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ * (1 + (Kb : ℝ) ^ 2) = δ) (hlam0 : 0 ≤ lam)
    (hlam : lam * δ = 8 * h * contractL Ka Kb δ H * ((Ka : ℝ) ^ 2 * H + (Kb : ℝ) ^ 2))
    (x₀ x y : ℝ) :
    (1 + θ * h) * ((x - y + 2 * h * (a x - a y)) ^ 2 + (b x - b y) ^ 2 * h) +
        h * contractL Ka Kb δ H * ((a x * h) ^ 2 + b x ^ 2 * h) +
        lam * (1 - h * δ / 2) * ((x - x₀ + a x * h) ^ 2 + b x ^ 2 * h) +
        ((1 + θ) * h * (b x - b y) ^ 2 + lam * (h * δ * contractM a b Ka Kb δ H x₀ / 2)) ≤
      (1 - h * δ / 4) * ((x - y) ^ 2 + lam * (x - x₀) ^ 2) +
        2 * h ^ 2 * contractL Ka Kb δ H * (a x₀ ^ 2 * H + b x₀ ^ 2 +
          4 * ((Ka : ℝ) ^ 2 * H + (Kb : ℝ) ^ 2) * contractM a b Ka Kb δ H x₀) := by
  have hH : 0 ≤ H := hh.trans hhH
  obtain ⟨L, hL⟩ : ∃ L, L = contractL Ka Kb δ H := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = contractM a b Ka Kb δ H x₀ := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = (Ka : ℝ) ^ 2 * H + (Kb : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = x - y := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = x - x₀ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = x - y + 2 * h * (a x - a y) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = b x - b y := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := hL ▸ contractL_nonneg Ka Kb hδ hH
  have hM0 : 0 ≤ M := hM ▸ contractM_nonneg a b Ka Kb hδ hH x₀
  have F1 : C ^ 2 + 2 * h * β ^ 2 ≤ (1 - 2 * h * δ) * D ^ 2 := by
    rw [hC, hβ, hD]; exact coarse_contraction_sq ha hb hdiss hh hhH hmargin x y
  have F2 : β ^ 2 ≤ (Kb : ℝ) ^ 2 * D ^ 2 := by
    rw [hβ, hD]; exact sq_sub_le_of_lipschitzWith hb x y
  have F3 : (u + a x * h) ^ 2 + b x ^ 2 * h ≤ (1 - h * δ / 2) * u ^ 2 + h * δ * M / 2 := by
    rw [hu, hM]; exact emStep_drift_sq ha hb hdiss hδ hh hhH hmargin x₀ x
  have F4 : a x ^ 2 ≤ 2 * a x₀ ^ 2 + 2 * (Ka : ℝ) ^ 2 * u ^ 2 := by
    have := sq_sub_le_of_lipschitzWith ha x x₀
    rw [← hu] at this
    linarith [sq_nonneg (2 * a x₀ - a x)]
  have F5 : b x ^ 2 ≤ 2 * b x₀ ^ 2 + 2 * (Kb : ℝ) ^ 2 * u ^ 2 := by
    have := sq_sub_le_of_lipschitzWith hb x x₀
    rw [← hu] at this
    linarith [sq_nonneg (2 * b x₀ - b x)]
  -- `hδ ≤ 1/2`, so `r₁ = 1 − hδ/2 ∈ [0, 1]`
  have hhδ : h * δ ≤ 2 := by
    have s1 : δ ≤ 2 * κ - 2 * (Ka : ℝ) ^ 2 * H := by nlinarith [sq_nonneg (Kb : ℝ)]
    have s2 := mul_le_mul_of_nonneg_left s1 hh
    have s3 := mul_le_mul_of_nonneg_left (le_of_dissipative ha hdiss) hh
    have s4 : h * h * (Ka : ℝ) ^ 2 ≤ h * H * (Ka : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhH hh) (sq_nonneg _)
    nlinarith [sq_nonneg (h * Ka - 1 / 2)]
  have hr0 : 0 ≤ 1 - h * δ / 2 := by linarith
  have hr1 : 1 - h * δ / 2 ≤ 1 := by
    have := mul_nonneg hh hδ.le
    linarith
  -- T1: the contraction part
  have T1 : (1 + θ * h) * (C ^ 2 + β ^ 2 * h) + (1 + θ) * h * β ^ 2 ≤ (1 - h * δ) * D ^ 2 := by
    have P1 := mul_le_mul_of_nonneg_left F1 (by positivity : (0 : ℝ) ≤ 1 + θ * h)
    have P2 := mul_le_mul_of_nonneg_left F2 (by positivity : (0 : ℝ) ≤ θ * h)
    have P3 : 0 ≤ θ * h ^ 2 * β ^ 2 := by positivity
    have P4 : 0 ≤ θ * h ^ 2 * δ * D ^ 2 := by positivity
    have E1 : θ * (1 + (Kb : ℝ) ^ 2) * h * D ^ 2 = δ * h * D ^ 2 := by rw [hθ]
    linarith
  -- T2: the local error
  have T2 : h * L * ((a x * h) ^ 2 + b x ^ 2 * h) ≤
      h * L * (h * (2 * (a x₀ ^ 2 * H + b x₀ ^ 2) + 2 * K₂ * u ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hh hL0)
    have Q1 := mul_le_mul_of_nonneg_left F4 (sq_nonneg h)
    have Q2 := mul_le_mul_of_nonneg_left F5 hh
    have Q3 : h ^ 2 * (2 * a x₀ ^ 2 + 2 * (Ka : ℝ) ^ 2 * u ^ 2) ≤
        h * H * (2 * a x₀ ^ 2 + 2 * (Ka : ℝ) ^ 2 * u ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [sq]
      exact mul_le_mul_of_nonneg_left hhH hh
    rw [hK₂]
    linarith
  -- T3: the drift of the fine chain
  have T3 : lam * (1 - h * δ / 2) * ((u + a x * h) ^ 2 + b x ^ 2 * h) ≤
      lam * (1 - h * δ / 2) * u ^ 2 + lam * (h * δ * M / 2) := by
    have R1 := mul_le_mul_of_nonneg_left F3 (mul_nonneg hlam0 hr0)
    have R2 : (1 - h * δ / 2) * ((1 - h * δ / 2) * u ^ 2) ≤ 1 * ((1 - h * δ / 2) * u ^ 2) :=
      mul_le_mul_of_nonneg_right hr1 (mul_nonneg hr0 (sq_nonneg u))
    have R2' := mul_le_mul_of_nonneg_left R2 hlam0
    have hM' : 0 ≤ h * δ * M / 2 := by positivity
    have R3 := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hlam0 hM')
    linarith
  rw [← hL, ← hK₂] at hlam
  have E2 : lam * δ * h * u ^ 2 = 8 * h * L * K₂ * h * u ^ 2 := by rw [hlam]
  have E3 : lam * δ * h * M = 8 * h * L * K₂ * h * M := by rw [hlam]
  have P5 : 0 ≤ h * δ * D ^ 2 := by positivity
  rw [← hL, ← hM, ← hK₂, ← hC, ← hβ, ← hD, ← hu]
  linarith

end algebra

/-! ### The coupled fine and coarse chains -/

/-- **One step of the coupled fine and coarse Euler–Maruyama chains** (Giles 2015, §10.1, p. 61:
"The coarse and fine paths will share the same driving Brownian path"): from `z = (x, y)`, the fine
chain takes two steps of size `h` with the Brownian increments `p.1` (first) and `p.2`, and the
coarse chain one step of size `2h` with the summed increment `p.1 + p.2`. -/
noncomputable def pairEM (a b : ℝ → ℝ) (h : ℝ) (z p : ℝ × ℝ) : ℝ × ℝ :=
  (emStep a b h (emStep a b h z.1 p.1) p.2, emStep a b (2 * h) z.2 (p.1 + p.2))

/-- `2n` steps of `φ` are `n` steps of the two-step map, whose noise pairs the step ending at time
`−(2k + 1)` (applied first) with the one ending at time `−2k` (Giles 2015, §10.1). -/
lemma backIter_two_mul {α E : Type*} (φ : α → E → α) (n : ℕ) (e : ℕ → E) (x : α) :
    backIter φ (2 * n) e x =
      backIter (fun y (p : E × E) => φ (φ y p.1) p.2) n (fun k => (e (2 * k + 1), e (2 * k)))
        x := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, backIter_succ, backIter_succ, ih,
      backIter_succ]
    have e1 : (fun k => (e (2 * k + 1 + 1 + 1), e (2 * k + 1 + 1))) =
        fun k => (e (2 * (k + 1) + 1), e (2 * (k + 1))) := by
      funext k
      rw [show 2 * k + 1 + 1 + 1 = 2 * (k + 1) + 1 by ring,
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    exact congrArg (fun w => φ (φ (backIter (fun y (p : E × E) => φ (φ y p.1) p.2) n w x) (e 1))
      (e 0)) e1

/-- The chain of a product map is the product of the chains. -/
lemma backIter_prodMap {α β E : Type*} (F : α → E → α) (G : β → E → β) (n : ℕ) (e : ℕ → E)
    (z : α × β) :
    backIter (fun (w : α × β) p => (F w.1 p, G w.2 p)) n e z =
      (backIter F n e z.1, backIter G n e z.2) := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih => rw [backIter_succ, ih, backIter_succ, backIter_succ]

section coupling

variable {a b : ℝ → ℝ} {Ka Kb : ℝ≥0} {κ δ H : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- The noises `ξ_{m+1}, ξ_{m+2}, …` are independent of `ξ_m`. -/
lemma indep_noiseFrom_succ (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (m : ℕ) :
    Indep (noiseFrom ξ (m + 1)) (MeasurableSpace.comap (ξ m) inferInstance) μ := by
  have h := indep_iSup_of_disjoint (fun i => (hξm i).comap_le) hξ.iIndep
    (S := Set.Ici (m + 1)) (T := {m}) (Set.disjoint_singleton_right.2 (by simp))
  refine indep_of_indep_of_le_right h ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ ({m} : Set ℕ)) =>
    MeasurableSpace.comap (ξ i) inferInstance) m (Set.mem_singleton m)

omit [IsProbabilityMeasure μ] in
/-- The noises `ξ_{2m+2}, ξ_{2m+3}, …` are independent of the pair `(ξ_{2m+1}, ξ_{2m})`. -/
lemma indep_noiseFrom_pair (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (m : ℕ) :
    Indep (noiseFrom ξ (2 * (m + 1)))
      (MeasurableSpace.comap (fun ω => (ξ (2 * m + 1) ω, ξ (2 * m) ω)) inferInstance) μ := by
  have hdisj : Disjoint (Set.Ici (2 * (m + 1))) ({2 * m + 1, 2 * m} : Set ℕ) := by
    rw [Set.disjoint_left]
    intro i hi hi'
    rw [Set.mem_Ici] at hi
    rcases hi' with rfl | rfl <;> omega
  have h := indep_iSup_of_disjoint (fun i => (hξm i).comap_le) hξ.iIndep hdisj
  refine indep_of_indep_of_le_right h (Measurable.comap_le ?_)
  have h1 : ∀ i ∈ ({2 * m + 1, 2 * m} : Set ℕ), Measurable[⨆ j ∈ ({2 * m + 1, 2 * m} : Set ℕ),
      MeasurableSpace.comap (ξ j) inferInstance] (ξ i) := fun i hi =>
    (comap_measurable (ξ i)).mono (le_iSup₂ (f := fun j (_ : j ∈ ({2 * m + 1, 2 * m} : Set ℕ)) =>
      MeasurableSpace.comap (ξ j) inferInstance) i hi) le_rfl
  exact (h1 _ (by simp)).prodMk (h1 _ (by simp))

/-- **The fine Euler–Maruyama step drifts towards the start** (Giles 2015, §10.1), in `ℝ≥0∞`:
`E[(φ_h(x, ΔW) − x₀)²] ≤ (1 − hδ/2)(x − x₀)² + hδM/2` for `ΔW ~ N(0, h)`, `M = contractM`. -/
lemma lintegral_emStep_drift (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h : ℝ≥0}
    (hhH : (h : ℝ) ≤ H) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * H + δ ≤ 2 * κ)
    (x₀ x : ℝ) :
    ∫⁻ w, ENNReal.ofReal ((emStep a b h x w - x₀) ^ 2) ∂gaussianReal 0 h ≤
      ENNReal.ofReal (1 - h * δ / 2) * ENNReal.ofReal ((x - x₀) ^ 2) +
        ENNReal.ofReal (h * δ * contractM a b Ka Kb δ H x₀ / 2) := by
  have e : ∀ w, emStep a b h x w - x₀ = (x - x₀ + a x * h) + b x * w := fun w => by
    unfold emStep
    ring
  simp_rw [e]
  rw [lintegral_sq_affine_gaussianReal, ← ENNReal.ofReal_mul' (sq_nonneg _)]
  exact (ENNReal.ofReal_le_ofReal
    (emStep_drift_sq ha hb hdiss hδ h.coe_nonneg hhH hmargin x₀ x)).trans ENNReal.ofReal_add_le

/-- **The Euler–Maruyama chain of a dissipative SDE is bounded in mean square uniformly in the
number of steps and in the step** (Giles 2015, §10.1, p. 61: "contracting SDEs which converge to
a limiting distribution").  With independent increments `ξ_k ~ N(0, h)`, `0 < h ≤ H` and the
margin `K_b² + 2K_a²H + δ ≤ 2κ`, the chain started `n` steps before time `−m` at `x₀` satisfies
`E[(X − x₀)²] ≤ M = contractM`, whatever `n`, `m` and `h`
(`lintegral_backIter_drift` with `emStep_drift_sq`). -/
lemma lintegral_sq_backIter_sub_le (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h : ℝ≥0}
    (hh : 0 < h) (hhH : (h : ℝ) ≤ H) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * H + δ ≤ 2 * κ)
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = gaussianReal 0 h) (x₀ : ℝ) (n m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((backIter (emStep a b h) n (fun k => ξ (k + m) ω) x₀ - x₀) ^ 2) ∂μ ≤
      ENNReal.ofReal (contractM a b Ka Kb δ H x₀) := by
  have hma : Measurable a := ha.continuous.measurable
  have hmb : Measurable b := hb.continuous.measurable
  have hφm : Measurable fun q : ℝ × ℝ => emStep a b h q.1 q.2 := by
    unfold emStep
    fun_prop
  have hV : Measurable fun x : ℝ => ENNReal.ofReal ((x - x₀) ^ 2) :=
    ((measurable_id.sub_const x₀).pow_const 2).ennreal_ofReal
  have hd := lintegral_backIter_drift (μ := μ) (ν := gaussianReal 0 h) hφm hV
    (lintegral_emStep_drift ha hb hdiss hδ hhH hmargin x₀) (noiseFrom ξ) (noiseFrom_le hξm)
    (fun m => noiseFrom_anti ξ (Nat.le_succ m)) (fun m => measurable_noise ξ le_rfl)
    (indep_noiseFrom_succ hξ hξm) hlaw n m (U := fun _ => x₀) measurable_const
  have h0 : ∫⁻ _ : Ω, ENNReal.ofReal ((x₀ - x₀) ^ 2) ∂μ = 0 := by simp
  rw [h0, mul_zero, zero_add] at hd
  have hh' : (0 : ℝ) < h := hh
  have hhδ := mul_le_half_of_margin ha hdiss h.coe_nonneg hhH hmargin
  have hHδ : 0 < (h : ℝ) * δ := mul_pos hh' hδ
  have hM0 := contractM_nonneg a b Ka Kb hδ (h.coe_nonneg.trans hhH) x₀
  refine hd.trans ((ofReal_mul_geom_le (by positivity) (by linarith) (by linarith) n).trans
    (le_of_eq ?_))
  congr 1
  field_simp
  ring

/-- **The Lyapunov drift of the coupled pair over one coarse step** (Giles 2015, §10.1, p. 61).
For `W(x, y) = (x − y)² + λ (x − x₀)²` with `λ δ = 8 h L K₂` (`L = contractL`,
`K₂ = K_a² H + K_b²`) and independent increments `p.1, p.2 ~ N(0, h)`:
`E[W(pairEM(z, p))] ≤ (1 − hδ/4) W(z) + 2h² L (a(x₀)² H + b(x₀)² + 4 K₂ M)`, `M = contractM`.
The second increment is integrated exactly (`lintegral_three_sq_gaussianReal`); the first after
the pointwise bounds `pair_step_sq` and `emStep_drift_sq`. -/
lemma lintegral_pairEM_drift (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h : ℝ≥0}
    (hhH : (h : ℝ) ≤ H) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * H + δ ≤ 2 * κ) {lam : ℝ}
    (hlam0 : 0 ≤ lam)
    (hlam : lam * δ = 8 * h * contractL Ka Kb δ H * ((Ka : ℝ) ^ 2 * H + (Kb : ℝ) ^ 2))
    (x₀ : ℝ) (z : ℝ × ℝ) :
    ∫⁻ p, ENNReal.ofReal (((pairEM a b h z p).1 - (pairEM a b h z p).2) ^ 2 +
        lam * ((pairEM a b h z p).1 - x₀) ^ 2) ∂((gaussianReal 0 h).prod (gaussianReal 0 h)) ≤
      ENNReal.ofReal (1 - h * δ / 4) * ENNReal.ofReal ((z.1 - z.2) ^ 2 + lam * (z.1 - x₀) ^ 2) +
        ENNReal.ofReal (2 * h ^ 2 * contractL Ka Kb δ H * (a x₀ ^ 2 * H + b x₀ ^ 2 +
          4 * ((Ka : ℝ) ^ 2 * H + (Kb : ℝ) ^ 2) * contractM a b Ka Kb δ H x₀)) := by
  obtain ⟨x, y⟩ := z
  have hma : Measurable a := ha.continuous.measurable
  have hmb : Measurable b := hb.continuous.measurable
  have hh : (0 : ℝ) ≤ h := h.coe_nonneg
  have hH : 0 ≤ H := hh.trans hhH
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = δ / (1 + (Kb : ℝ) ^ 2) := ⟨_, rfl⟩
  obtain ⟨ι, hιdef⟩ : ∃ ι : ℝ, ι = (1 + (Kb : ℝ) ^ 2) / δ := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθι : θ * ι = 1 := by rw [hθdef, hιdef]; field_simp
  have hθ : θ * (1 + (Kb : ℝ) ^ 2) = δ := by rw [hθdef]; field_simp
  have hL : (ι + H) * (Ka : ℝ) ^ 2 + (1 + ι) * (Kb : ℝ) ^ 2 = contractL Ka Kb δ H := by
    rw [contractL, hιdef]
  have hFm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal
      (((pairEM a b h (x, y) p).1 - (pairEM a b h (x, y) p).2) ^ 2 +
        lam * ((pairEM a b h (x, y) p).1 - x₀) ^ 2) := by
    unfold pairEM emStep
    fun_prop
  rw [lintegral_prod _ hFm.aemeasurable]
  -- the second increment, exactly
  have hinner : ∀ u : ℝ, ∫⁻ v, ENNReal.ofReal
      (((pairEM a b h (x, y) (u, v)).1 - (pairEM a b h (x, y) (u, v)).2) ^ 2 +
        lam * ((pairEM a b h (x, y) (u, v)).1 - x₀) ^ 2) ∂gaussianReal 0 h =
      ENNReal.ofReal ((emStep a b h x u + a (emStep a b h x u) * h - y - 2 * a y * h - b y * u) ^ 2
        + (b (emStep a b h x u) - b y) ^ 2 * h + lam * ((emStep a b h x u - x₀ +
          a (emStep a b h x u) * h) ^ 2 + b (emStep a b h x u) ^ 2 * h)) := by
    intro u
    have e : ∀ v, ((pairEM a b h (x, y) (u, v)).1 - (pairEM a b h (x, y) (u, v)).2) ^ 2 +
        lam * ((pairEM a b h (x, y) (u, v)).1 - x₀) ^ 2 =
        1 * ((emStep a b h x u + a (emStep a b h x u) * h - y - 2 * a y * h - b y * u) +
          (b (emStep a b h x u) - b y) * v) ^ 2 +
        lam * ((emStep a b h x u - x₀ + a (emStep a b h x u) * h) + b (emStep a b h x u) * v) ^ 2 +
        0 * (0 + 0 * v) ^ 2 + 0 := by
      intro v
      rw [pairEM]
      unfold emStep
      ring
    simp_rw [e]
    rw [lintegral_three_sq_gaussianReal zero_le_one hlam0 le_rfl le_rfl]
    congr 1
    ring
  simp_rw [hinner]
  -- the first increment, after the pointwise bounds
  have hpt : ∀ u : ℝ,
      (emStep a b h x u + a (emStep a b h x u) * h - y - 2 * a y * h - b y * u) ^ 2 +
        (b (emStep a b h x u) - b y) ^ 2 * h + lam * ((emStep a b h x u - x₀ +
          a (emStep a b h x u) * h) ^ 2 + b (emStep a b h x u) ^ 2 * h) ≤
      (1 + θ * h) * ((x - y + 2 * h * (a x - a y)) + (b x - b y) * u) ^ 2 +
        h * contractL Ka Kb δ H * (a x * h + b x * u) ^ 2 +
        lam * (1 - h * δ / 2) * ((x - x₀ + a x * h) + b x * u) ^ 2 +
        ((1 + θ) * h * (b x - b y) ^ 2 + lam * (h * δ * contractM a b Ka Kb δ H x₀ / 2)) := by
    intro u
    have h1 := pair_step_sq ha hb hθ0 hθι hh hhH x y u
    have h2 := emStep_drift_sq ha hb hdiss hδ hh hhH hmargin x₀ (emStep a b h x u)
    have e : emStep a b h x u - x₀ = (x - x₀ + a x * h) + b x * u := by
      unfold emStep
      ring
    have h2' : (emStep a b h x u - x₀ + a (emStep a b h x u) * h) ^ 2 +
        b (emStep a b h x u) ^ 2 * h ≤ (1 - h * δ / 2) * ((x - x₀ + a x * h) + b x * u) ^ 2 +
          h * δ * contractM a b Ka Kb δ H x₀ / 2 := by
      rw [← e]
      exact h2
    rw [hL] at h1
    have h3 := mul_le_mul_of_nonneg_left h2' hlam0
    linarith
  have hr1 := mul_le_half_of_margin ha hdiss hh hhH hmargin
  have hM0 := contractM_nonneg a b Ka Kb hδ hH x₀
  have hL0 := contractL_nonneg Ka Kb hδ hH
  refine (lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hpt u)).trans ?_
  rw [lintegral_three_sq_gaussianReal (by positivity) (mul_nonneg hh hL0)
    (mul_nonneg hlam0 (by linarith)) (by positivity)]
  rw [← ENNReal.ofReal_mul' (by positivity)]
  exact (ENNReal.ofReal_le_ofReal (pair_integrated_le ha hb hdiss hδ hh hhH hmargin hθ0.le hθ
    hlam0 hlam x₀ x y)).trans ENNReal.ofReal_add_le

/-- **Contracting SDEs with level-dependent time steps: the fine and the coarse path are
`O(h)`-close in mean square** (Giles 2015, §10.1, p. 61: "A very similar approach can also be
used for contracting SDEs which converge to a limiting distribution.  For these, the level `ℓ`
path will perform a simulation for the time interval `[−T_ℓ, 0]`, using timestep `h_ℓ`.  The
coarse and fine paths will share the same driving Brownian path for the overlapping time interval
`[−T_{ℓ−1}, 0]`, and the contraction property will ensure that the multilevel variance decays
with level").  Let `dX = a(X) dt + b(X) dW` have a `K_a`-Lipschitz dissipative drift,
`(x − y)(a(x) − a(y)) ≤ −κ (x − y)²`, and a `K_b`-Lipschitz volatility (`K_b = 0`: additive
noise), and let `0 < h ≤ H` with the margin `K_b² + 2 K_a² H + δ ≤ 2κ`, `δ > 0` (so that the
coarse step `2h` contracts).  Let the `ξ_k ~ N(0, h)` be independent: `ξ_k` is the Brownian
increment over `[−(k + 1)h, −kh]`.  The fine path is the Euler–Maruyama chain with step `h`
started at `x₀` at time `−T_f = −N_f h`, whose step ending at time `−kh` uses `ξ_k`; the coarse
path is the chain with step `2h` started at `x₀` at time `−T_c = −2N_c h`, `2N_c ≤ N_f`, whose
step ending at time `−2kh` uses `ξ_{2k} + ξ_{2k+1}`, the Brownian increment over
`[−(2k + 2)h, −2kh]`.  So the two paths share the Brownian path on `[−T_c, 0]`, i.e. the
increments `ξ_0, …, ξ_{2N_c − 1}`; the fine path's initial segment `[−T_f, −T_c]` uses
`ξ_{2N_c}, …, ξ_{N_f − 1}`, which the coarse path does not see.  Then
`E[(X^f_0 − X^c_0)²] ≤ C₁ h + C₂ (1 − hδ/4)^{N_c}` with the explicit constants `contractC₁`,
`contractC₂`, which depend only on `a(x₀), b(x₀), K_a, K_b, δ, H`.  The first term is the local
error of two fine steps against one coarse step (`O(h²)` per coarse step in mean square, damped by
the contraction over `O(1/h)` steps); the second is the contracted effect of the fine path's
initial segment (its distance from `x₀` at time `−T_c` is bounded in mean square,
`lintegral_sq_backIter_sub_le`).  Deviations: one dimension; the Lipschitz, dissipativity and
margin conditions are explicit hypotheses for the paper's "contracting SDEs"; the constants and
the rate `1 − hδ/4` per coarse step are not optimised. -/
theorem lintegral_sq_fine_sub_coarse_le (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h : ℝ≥0}
    (hh : 0 < h) (hhH : (h : ℝ) ≤ H) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * H + δ ≤ 2 * κ)
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = gaussianReal 0 h) (x₀ : ℝ) {Nf Nc : ℕ} (hN : 2 * Nc ≤ Nf) :
    ∫⁻ ω, ENNReal.ofReal ((backIter (emStep a b h) Nf (fun k => ξ k ω) x₀ -
        backIter (emStep a b (2 * h)) Nc (fun k => ξ (2 * k) ω + ξ (2 * k + 1) ω) x₀) ^ 2) ∂μ ≤
      ENNReal.ofReal (contractC₁ a b Ka Kb δ H x₀ * h +
        contractC₂ a b Ka Kb δ H x₀ * (1 - h * δ / 4) ^ Nc) := by
  have hma : Measurable a := ha.continuous.measurable
  have hmb : Measurable b := hb.continuous.measurable
  have hh0 : (0 : ℝ) ≤ h := h.coe_nonneg
  have hhpos : (0 : ℝ) < h := hh
  have hH : 0 ≤ H := hh0.trans hhH
  have hhδ := mul_le_half_of_margin ha hdiss hh0 hhH hmargin
  have hhδpos : 0 < (h : ℝ) * δ := mul_pos hhpos hδ
  obtain ⟨L, hL⟩ : ∃ L, L = contractL Ka Kb δ H := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = contractM a b Ka Kb δ H x₀ := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = (Ka : ℝ) ^ 2 * H + (Kb : ℝ) ^ 2 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := hL ▸ contractL_nonneg Ka Kb hδ hH
  have hM0 : 0 ≤ M := hM ▸ contractM_nonneg a b Ka Kb hδ hH x₀
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = 8 * h * L * K₂ / δ := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlamdef]; positivity
  have hlam : lam * δ = 8 * h * contractL Ka Kb δ H * ((Ka : ℝ) ^ 2 * H + (Kb : ℝ) ^ 2) := by
    rw [hlamdef, ← hL, ← hK₂]
    field_simp
  -- the step maps are measurable
  have hφm : Measurable fun q : ℝ × ℝ => emStep a b h q.1 q.2 := by
    unfold emStep
    fun_prop
  have hΦm : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => pairEM a b h q.1 q.2 := by
    unfold pairEM emStep
    fun_prop
  have hW : Measurable fun z : ℝ × ℝ =>
      ENNReal.ofReal ((z.1 - z.2) ^ 2 + lam * (z.1 - x₀) ^ 2) := by
    fun_prop
  -- the fine path at time `−2hN_c`: the start of the coupled pair
  obtain ⟨U, hUdef⟩ : ∃ U : Ω → ℝ,
      U = fun ω => backIter (emStep a b h) (Nf - 2 * Nc) (fun k => ξ (k + 2 * Nc) ω) x₀ :=
    ⟨_, rfl⟩
  have hU : Measurable[noiseFrom ξ (2 * (0 + Nc))] fun ω => (U ω, x₀) := by
    rw [zero_add, hUdef]
    exact (measurable_backIter_shift hφm ξ (Nf - 2 * Nc) (2 * Nc) (U := fun _ => x₀)
      measurable_const).prodMk measurable_const
  -- the pairs of fine increments
  have hζm : ∀ m, Measurable[noiseFrom ξ (2 * m)] fun ω => (ξ (2 * m + 1) ω, ξ (2 * m) ω) :=
    fun m => (measurable_noise ξ (by omega)).prodMk (measurable_noise ξ le_rfl)
  have hζlaw : ∀ m, μ.map (fun ω => (ξ (2 * m + 1) ω, ξ (2 * m) ω)) =
      (gaussianReal 0 h).prod (gaussianReal 0 h) := fun m => by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hξm _).aemeasurable (hξm _).aemeasurable).1
      (hξ.indepFun (by omega : 2 * m + 1 ≠ 2 * m)), hlaw, hlaw]
  have hd := lintegral_backIter_drift (μ := μ) (ν := (gaussianReal 0 h).prod (gaussianReal 0 h))
    hΦm hW (lintegral_pairEM_drift ha hb hdiss hδ hhH hmargin hlam0 hlam x₀)
    (fun m => noiseFrom ξ (2 * m)) (fun m => noiseFrom_le hξm _)
    (fun m => noiseFrom_anti ξ (by omega)) hζm (fun m => indep_noiseFrom_pair hξ hξm m) hζlaw
    Nc 0 hU
  -- the coupled pair is `(X^f, X^c)`
  obtain ⟨Ff, hFf⟩ : ∃ Ff : ℝ → ℝ × ℝ → ℝ,
      Ff = fun y q => emStep a b h (emStep a b h y q.1) q.2 := ⟨_, rfl⟩
  obtain ⟨Gc, hGc⟩ : ∃ Gc : ℝ → ℝ × ℝ → ℝ, Gc = fun y q => emStep a b (2 * h) y (q.1 + q.2) :=
    ⟨_, rfl⟩
  have e1 : pairEM a b h = fun (w : ℝ × ℝ) (p : ℝ × ℝ) => (Ff w.1 p, Gc w.2 p) := by
    rw [hFf, hGc]
    rfl
  have hpair : ∀ ω, backIter (pairEM a b h) Nc
      (fun k => (ξ (2 * (k + 0) + 1) ω, ξ (2 * (k + 0)) ω)) (U ω, x₀) =
      (backIter (emStep a b h) Nf (fun k => ξ k ω) x₀,
        backIter (emStep a b (2 * h)) Nc (fun k => ξ (2 * k) ω + ξ (2 * k + 1) ω) x₀) := by
    intro ω
    rw [e1, backIter_prodMap Ff Gc]
    refine Prod.ext ?_ ?_
    · have hf := backIter_add (emStep a b h) (Nf - 2 * Nc) (2 * Nc) (fun k => ξ k ω) x₀
      rw [Nat.sub_add_cancel hN, backIter_two_mul] at hf
      rw [hFf, hUdef]
      exact hf.symm
    · have hc := backIter_comp_noise (emStep a b (2 * h)) (fun q : ℝ × ℝ => q.1 + q.2) Nc
        (fun k => (ξ (2 * k + 1) ω, ξ (2 * k) ω)) x₀
      rw [hGc]
      refine hc.trans ?_
      congr 1
      funext k
      exact add_comm _ _
  -- the start of the pair: `E[W(U, x₀)] ≤ (1 + λ) M`
  have hstart : ∫⁻ ω, ENNReal.ofReal (((U ω, x₀).1 - (U ω, x₀).2) ^ 2 +
      lam * ((U ω, x₀).1 - x₀) ^ 2) ∂μ ≤ ENNReal.ofReal (1 + lam) * ENNReal.ofReal M := by
    have hUm : Measurable U := hU.fst.mono (noiseFrom_le hξm _) le_rfl
    have e2 : ∀ ω, ENNReal.ofReal (((U ω, x₀).1 - (U ω, x₀).2) ^ 2 +
        lam * ((U ω, x₀).1 - x₀) ^ 2) =
        ENNReal.ofReal (1 + lam) * ENNReal.ofReal ((U ω - x₀) ^ 2) := fun ω => by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [lintegral_congr e2, lintegral_const_mul _ ((hUm.sub_const x₀).pow_const 2).ennreal_ofReal]
    gcongr
    rw [hM, hUdef]
    exact lintegral_sq_backIter_sub_le ha hb hdiss hδ hh hhH hmargin hξ hξm hlaw x₀ _ _
  have hr0 : 0 ≤ 1 - (h : ℝ) * δ / 4 := by linarith
  have hr1 : 1 - (h : ℝ) * δ / 4 < 1 := by linarith
  have hKW0 : 0 ≤ 2 * (h : ℝ) ^ 2 * contractL Ka Kb δ H * (a x₀ ^ 2 * H + b x₀ ^ 2 +
      4 * ((Ka : ℝ) ^ 2 * H + (Kb : ℝ) ^ 2) * contractM a b Ka Kb δ H x₀) := by
    rw [← hL, ← hM, ← hK₂]
    positivity
  have step1 : ENNReal.ofReal (1 - h * δ / 4) ^ Nc * ∫⁻ ω, ENNReal.ofReal
      (((U ω, x₀).1 - (U ω, x₀).2) ^ 2 + lam * ((U ω, x₀).1 - x₀) ^ 2) ∂μ ≤
      ENNReal.ofReal ((1 - h * δ / 4) ^ Nc * ((1 + lam) * M)) := by
    rw [ENNReal.ofReal_mul (pow_nonneg hr0 _), ENNReal.ofReal_pow hr0,
      ENNReal.ofReal_mul (by positivity)]
    gcongr
  have step2 := ofReal_mul_geom_le hKW0 hr0 hr1 Nc
  refine le_trans (lintegral_mono fun ω => ?_) (hd.trans ((add_le_add step1 step2).trans ?_))
  · rw [hpair ω]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (mul_nonneg hlam0 (sq_nonneg _)))
  rw [← ENNReal.ofReal_add (by positivity) (div_nonneg hKW0 (by linarith))]
  apply ENNReal.ofReal_le_ofReal
  rw [← hL, ← hM, ← hK₂]
  have hC₁ : contractC₁ a b Ka Kb δ H x₀ = 8 / δ * L * (a x₀ ^ 2 * H + b x₀ ^ 2 + 4 * K₂ * M) := by
    rw [contractC₁, hL, hM, hK₂]
  have hC₂ : contractC₂ a b Ka Kb δ H x₀ = (1 + 8 * H * L * K₂ / δ) * M := by
    rw [contractC₂, hL, hM, hK₂]
  have hlamH : lam ≤ 8 * H * L * K₂ / δ := by
    rw [hlamdef]
    apply div_le_div_of_nonneg_right _ hδ.le
    have := mul_le_mul_of_nonneg_right hhH (by positivity : (0 : ℝ) ≤ 8 * L * K₂)
    linarith
  have hKW : 2 * (h : ℝ) ^ 2 * L * (a x₀ ^ 2 * H + b x₀ ^ 2 + 4 * K₂ * M) /
      (1 - (1 - h * δ / 4)) = 8 / δ * L * (a x₀ ^ 2 * H + b x₀ ^ 2 + 4 * K₂ * M) * h := by
    field_simp
    ring
  rw [hC₁, hC₂, hKW]
  have : (1 - (h : ℝ) * δ / 4) ^ Nc * ((1 + lam) * M) ≤
      (1 + 8 * H * L * K₂ / δ) * M * (1 - h * δ / 4) ^ Nc := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hM0)
      (pow_nonneg hr0 _)
  linarith

/-- **Contracting SDEs with level-dependent time steps, in terms of the shared time** (Giles 2015,
§10.1, p. 61: "the contraction property will ensure that the multilevel variance decays with
level").  With the hypotheses and the coupling of `lintegral_sq_fine_sub_coarse_le`,
`(X^f_0 − X^c_0)²` is integrable and
`E[(X^f_0 − X^c_0)²] ≤ C₁ h + C₂ (1 − hδ/4)^{N_c} ≤ C₁ h + C₂ e^{−δ T_c/8}`, where `T_c = 2h N_c`
is the length of the shared interval `[−T_c, 0]`: an `O(h)` term plus a term that is
exponentially small in `T_c`, uniformly in `h`. -/
theorem integral_sq_fine_sub_coarse_le (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h : ℝ≥0}
    (hh : 0 < h) (hhH : (h : ℝ) ≤ H) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * H + δ ≤ 2 * κ)
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = gaussianReal 0 h) (x₀ : ℝ) {Nf Nc : ℕ} (hN : 2 * Nc ≤ Nf) :
    Integrable (fun ω => (backIter (emStep a b h) Nf (fun k => ξ k ω) x₀ -
        backIter (emStep a b (2 * h)) Nc (fun k => ξ (2 * k) ω + ξ (2 * k + 1) ω) x₀) ^ 2) μ ∧
      ∫ ω, (backIter (emStep a b h) Nf (fun k => ξ k ω) x₀ -
          backIter (emStep a b (2 * h)) Nc (fun k => ξ (2 * k) ω + ξ (2 * k + 1) ω) x₀) ^ 2 ∂μ ≤
        contractC₁ a b Ka Kb δ H x₀ * h + contractC₂ a b Ka Kb δ H x₀ * (1 - h * δ / 4) ^ Nc ∧
      ∫ ω, (backIter (emStep a b h) Nf (fun k => ξ k ω) x₀ -
          backIter (emStep a b (2 * h)) Nc (fun k => ξ (2 * k) ω + ξ (2 * k + 1) ω) x₀) ^ 2 ∂μ ≤
        contractC₁ a b Ka Kb δ H x₀ * h +
          contractC₂ a b Ka Kb δ H x₀ * Real.exp (-(δ * (2 * h * Nc)) / 8) := by
  have hma : Measurable a := ha.continuous.measurable
  have hmb : Measurable b := hb.continuous.measurable
  have hh0 : (0 : ℝ) ≤ h := h.coe_nonneg
  have hH : 0 ≤ H := hh0.trans hhH
  have hhδ := mul_le_half_of_margin ha hdiss hh0 hhH hmargin
  have hl := lintegral_sq_fine_sub_coarse_le ha hb hdiss hδ hh hhH hmargin hξ hξm hlaw x₀ hN
  have hC₁ := contractC₁_nonneg a b Ka Kb hδ hH x₀
  have hC₂ := contractC₂_nonneg a b Ka Kb hδ hH x₀
  have hr0 : 0 ≤ 1 - (h : ℝ) * δ / 4 := by linarith
  have hm : Measurable fun ω => (backIter (emStep a b h) Nf (fun k => ξ k ω) x₀ -
      backIter (emStep a b (2 * h)) Nc (fun k => ξ (2 * k) ω + ξ (2 * k + 1) ω) x₀) ^ 2 := by
    have h1 : Measurable fun q : ℝ × ℝ => emStep a b h q.1 q.2 := by
      unfold emStep
      fun_prop
    have h2 : Measurable fun q : ℝ × ℝ => emStep a b (2 * h) q.1 q.2 := by
      unfold emStep
      fun_prop
    have hf := (measurable_backIter_pi h1 Nf x₀).comp (measurable_pi_lambda _ hξm)
    have hc := (measurable_backIter_pi h2 Nc x₀).comp (measurable_pi_lambda
      (fun ω k => ξ (2 * k) ω + ξ (2 * k + 1) ω) fun k => (hξm _).add (hξm _))
    exact (hf.sub hc).pow_const 2
  have hI : ∫ ω, (backIter (emStep a b h) Nf (fun k => ξ k ω) x₀ -
      backIter (emStep a b (2 * h)) Nc (fun k => ξ (2 * k) ω + ξ (2 * k + 1) ω) x₀) ^ 2 ∂μ ≤
      contractC₁ a b Ka Kb δ H x₀ * h + contractC₂ a b Ka Kb δ H x₀ * (1 - h * δ / 4) ^ Nc := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hl
  refine ⟨⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun ω => sq_nonneg _)).2 (hl.trans_lt ENNReal.ofReal_lt_top)⟩, hI,
    hI.trans ?_⟩
  have he : (1 - (h : ℝ) * δ / 4) ^ Nc ≤ Real.exp (-(δ * (2 * h * Nc)) / 8) := by
    have h1 : 1 - (h : ℝ) * δ / 4 ≤ Real.exp (-(h * δ / 4)) := by
      linarith [Real.add_one_le_exp (-((h : ℝ) * δ / 4))]
    calc (1 - (h : ℝ) * δ / 4) ^ Nc ≤ Real.exp (-(h * δ / 4)) ^ Nc :=
          pow_le_pow_left₀ hr0 h1 Nc
      _ = Real.exp (-(δ * (2 * h * Nc)) / 8) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have := mul_le_mul_of_nonneg_left he hC₂
  linarith

end coupling

/-! ### The levels, the variance decay and Theorem 1 -/

section levels

variable {a b : ℝ → ℝ} {Ka Kb : ℝ≥0} {κ δ : ℝ}

/-- **The level-`ℓ` path of the multilevel method for a contracting SDE** (Giles 2015, §10.1,
p. 61: "the level `ℓ` path will perform a simulation for the time interval `[−T_ℓ, 0]`, using
timestep `h_ℓ`").  The Euler–Maruyama chain with step `h_ℓ = h₀ 2^{−ℓ}`, started at `x₀` at time
`−T_ℓ = −N_ℓ h_ℓ`, whose step ending at time `−k h_ℓ` uses the Brownian increment `√h_ℓ z_k`
(`z` a sequence of standard normals); its value at time `0`. -/
noncomputable def contractPath (a b : ℝ → ℝ) (h₀ x₀ : ℝ) (N : ℕ → ℕ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  backIter (emStep a b (h₀ / 2 ^ ℓ)) (N ℓ) (fun k => Real.sqrt (h₀ / 2 ^ ℓ) * z k) x₀

/-- The level-`ℓ` path driven by the coarse increments `(z_{2k} + z_{2k+1})/√2` is the
Euler–Maruyama chain with step `2h`, `h = h_{ℓ+1}`, driven by the sums of pairs of the fine
Brownian increments `√h z_k` (Giles 2015, §10.1: the coarse and fine paths share the Brownian
path). -/
lemma contractPath_pairAvg (a b : ℝ → ℝ) (h₀ x₀ : ℝ) (N : ℕ → ℕ) (ℓ : ℕ) (z : ℕ → ℝ) :
    contractPath a b h₀ x₀ N ℓ (pairAvg z) =
      backIter (emStep a b (2 * (h₀ / 2 ^ (ℓ + 1)))) (N ℓ)
        (fun k => Real.sqrt (h₀ / 2 ^ (ℓ + 1)) * z (2 * k) +
          Real.sqrt (h₀ / 2 ^ (ℓ + 1)) * z (2 * k + 1)) x₀ := by
  have e1 : h₀ / 2 ^ ℓ = 2 * (h₀ / 2 ^ (ℓ + 1)) := by
    rw [pow_succ]
    field_simp
  have e2 : ∀ k, Real.sqrt (2 * (h₀ / 2 ^ (ℓ + 1))) * pairAvg z k =
      Real.sqrt (h₀ / 2 ^ (ℓ + 1)) * z (2 * k) + Real.sqrt (h₀ / 2 ^ (ℓ + 1)) * z (2 * k + 1) := by
    intro k
    rw [Real.sqrt_mul (by norm_num), pairAvg]
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  unfold contractPath
  rw [e1]
  exact congrArg (fun e => backIter (emStep a b (2 * (h₀ / 2 ^ (ℓ + 1)))) (N ℓ) e x₀)
    (funext e2)

/-- The scaled standard normals `√v z_k` on `(ℝ^ℕ, N(0, 1)^{⊗ℕ})` are independent `N(0, v)`. -/
lemma scaled_stdNormal (v : ℝ≥0) :
    iIndepFun (fun k (z : ℕ → ℝ) => Real.sqrt v * z k) stdNormalSeq ∧
      (∀ k, Measurable fun z : ℕ → ℝ => Real.sqrt v * z k) ∧
      ∀ k, stdNormalSeq.map (fun z : ℕ → ℝ => Real.sqrt v * z k) = gaussianReal 0 v := by
  refine ⟨iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
    (X := fun _ x => Real.sqrt v * x) fun _ => measurable_const_mul _,
    fun k => (measurable_pi_apply k).const_mul _, fun k => ?_⟩
  have e : (fun z : ℕ → ℝ => Real.sqrt v * z k) = (fun x => Real.sqrt v * x) ∘ fun z => z k :=
    rfl
  rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), Measure.infinitePi_map_eval,
    gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp [Real.sq_sqrt v.coe_nonneg]

/-- **The fine and the coarse path of a level-`(ℓ + 1)` sample** (Giles 2015, §10.1), on the
canonical space: with the hypotheses of `integral_sq_fine_sub_coarse_le` for `H = h₀` and
`2N_ℓ ≤ N_{ℓ+1}`, `E[(X^f_{ℓ+1} − X^c_ℓ)²] ≤ C₁ h_{ℓ+1} + C₂ e^{−δ T_ℓ/8}`, `T_ℓ = N_ℓ h_ℓ`. -/
lemma contractPath_sq_le (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h₀ : ℝ}
    (hh₀ : 0 < h₀) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * h₀ + δ ≤ 2 * κ) (x₀ : ℝ)
    {N : ℕ → ℕ} (hN : ∀ ℓ, 2 * N ℓ ≤ N (ℓ + 1)) (ℓ : ℕ) :
    Integrable (fun z => (contractPath a b h₀ x₀ N (ℓ + 1) z -
        contractPath a b h₀ x₀ N ℓ (pairAvg z)) ^ 2) stdNormalSeq ∧
      ∫ z, (contractPath a b h₀ x₀ N (ℓ + 1) z - contractPath a b h₀ x₀ N ℓ (pairAvg z)) ^ 2
          ∂stdNormalSeq ≤
        contractC₁ a b Ka Kb δ h₀ x₀ * (h₀ / 2 ^ (ℓ + 1)) +
          contractC₂ a b Ka Kb δ h₀ x₀ * Real.exp (-(δ * (N ℓ * (h₀ / 2 ^ ℓ))) / 8) := by
  have hpos : 0 < h₀ / 2 ^ (ℓ + 1) := by positivity
  obtain ⟨hξ, hξm, hlaw⟩ := scaled_stdNormal ⟨h₀ / 2 ^ (ℓ + 1), hpos.le⟩
  have hle : h₀ / 2 ^ (ℓ + 1) ≤ h₀ := div_le_self hh₀.le (one_le_pow₀ (by norm_num))
  obtain ⟨hint, -, hI⟩ := integral_sq_fine_sub_coarse_le (μ := stdNormalSeq)
    (h := ⟨h₀ / 2 ^ (ℓ + 1), hpos.le⟩) ha hb hdiss hδ hpos hle hmargin hξ hξm hlaw x₀ (hN ℓ)
  have e : ∀ z, contractPath a b h₀ x₀ N ℓ (pairAvg z) =
      backIter (emStep a b (2 * (h₀ / 2 ^ (ℓ + 1)))) (N ℓ)
        (fun k => Real.sqrt (h₀ / 2 ^ (ℓ + 1)) * z (2 * k) +
          Real.sqrt (h₀ / 2 ^ (ℓ + 1)) * z (2 * k + 1)) x₀ :=
    contractPath_pairAvg a b h₀ x₀ N ℓ
  have eT : 2 * (h₀ / 2 ^ (ℓ + 1)) * (N ℓ : ℝ) = N ℓ * (h₀ / 2 ^ ℓ) := by
    rw [pow_succ]
    field_simp
  simp_rw [e]
  refine ⟨hint, hI.trans (le_of_eq ?_)⟩
  show contractC₁ a b Ka Kb δ h₀ x₀ * (h₀ / 2 ^ (ℓ + 1)) + contractC₂ a b Ka Kb δ h₀ x₀ *
    Real.exp (-(δ * (2 * (h₀ / 2 ^ (ℓ + 1)) * N ℓ)) / 8) = _
  rw [eT]

/-- The level-`ℓ` path is a measurable function of the normal increments. -/
lemma measurable_contractPath (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (h₀ x₀ : ℝ) (N : ℕ → ℕ) (ℓ : ℕ) : Measurable (contractPath a b h₀ x₀ N ℓ) := by
  have hma : Measurable a := ha.continuous.measurable
  have hmb : Measurable b := hb.continuous.measurable
  have hφ : Measurable fun q : ℝ × ℝ => emStep a b (h₀ / 2 ^ ℓ) q.1 q.2 := by
    unfold emStep
    fun_prop
  exact (measurable_backIter_pi hφ (N ℓ) x₀).comp
    (measurable_pi_lambda _ fun k => (measurable_pi_apply k).const_mul _)

/-- The level paths are bounded in mean square uniformly in the level (Giles 2015, §10.1):
`E[(X^{(ℓ)} − x₀)²] ≤ M` (`lintegral_sq_backIter_sub_le` with `h = h_ℓ ≤ h₀`). -/
lemma lintegral_sq_contractPath_sub_le (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h₀ : ℝ}
    (hh₀ : 0 < h₀) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * h₀ + δ ≤ 2 * κ) (x₀ : ℝ)
    (N : ℕ → ℕ) (ℓ : ℕ) :
    ∫⁻ z, ENNReal.ofReal ((contractPath a b h₀ x₀ N ℓ z - x₀) ^ 2) ∂stdNormalSeq ≤
      ENNReal.ofReal (contractM a b Ka Kb δ h₀ x₀) := by
  have hpos : 0 < h₀ / 2 ^ ℓ := by positivity
  obtain ⟨hξ, hξm, hlaw⟩ := scaled_stdNormal ⟨h₀ / 2 ^ ℓ, hpos.le⟩
  have hle : h₀ / 2 ^ ℓ ≤ h₀ := div_le_self hh₀.le (one_le_pow₀ (by norm_num))
  exact lintegral_sq_backIter_sub_le (μ := stdNormalSeq) (h := ⟨h₀ / 2 ^ ℓ, hpos.le⟩) ha hb hdiss
    hδ hpos hle hmargin hξ hξm hlaw x₀ (N ℓ) 0

/-- A Lipschitz payoff of a level path is square integrable, with
`E[(f(X^{(ℓ)}) − f(x₀))²] ≤ K_f² M` (Giles 2015, §10.1). -/
lemma memLp_contractPath (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h₀ : ℝ}
    (hh₀ : 0 < h₀) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * h₀ + δ ≤ 2 * κ) (x₀ : ℝ)
    (N : ℕ → ℕ) {f : ℝ → ℝ} {Kf : ℝ≥0} (hf : LipschitzWith Kf f) (ℓ : ℕ) :
    MemLp (fun z => f (contractPath a b h₀ x₀ N ℓ z)) 2 stdNormalSeq ∧
      ∫ z, (f (contractPath a b h₀ x₀ N ℓ z) - f x₀) ^ 2 ∂stdNormalSeq ≤
        (Kf : ℝ) ^ 2 * contractM a b Ka Kb δ h₀ x₀ := by
  have hX := measurable_contractPath ha hb h₀ x₀ N ℓ
  have hM := lintegral_sq_contractPath_sub_le ha hb hdiss hδ hh₀ hmargin x₀ N ℓ
  have hM0 := contractM_nonneg a b Ka Kb hδ hh₀.le x₀
  have hYm : Measurable fun z => (contractPath a b h₀ x₀ N ℓ z - x₀) ^ 2 :=
    (hX.sub_const x₀).pow_const 2
  have hYint : Integrable (fun z => (contractPath a b h₀ x₀ N ℓ z - x₀) ^ 2) stdNormalSeq :=
    ⟨hYm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)).2
      (hM.trans_lt ENNReal.ofReal_lt_top)⟩
  have hY : MemLp (fun z => contractPath a b h₀ x₀ N ℓ z - x₀) 2 stdNormalSeq :=
    (memLp_two_iff_integrable_sq (hX.sub_const x₀).aestronglyMeasurable).2 hYint
  have hfm : Measurable f := hf.continuous.measurable
  have hsub : MemLp (fun z => f (contractPath a b h₀ x₀ N ℓ z) - f x₀) 2 stdNormalSeq := by
    refine (hY.const_mul (Kf : ℝ)).of_le ((hfm.comp hX).sub_const _).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg Kf.coe_nonneg]
    exact abs_sub_le_of_lipschitzWith hf _ _
  refine ⟨?_, ?_⟩
  · convert hsub.add (memLp_const (f x₀)) using 1
    funext z
    simp
  · calc ∫ z, (f (contractPath a b h₀ x₀ N ℓ z) - f x₀) ^ 2 ∂stdNormalSeq
        ≤ ∫ z, (Kf : ℝ) ^ 2 * (contractPath a b h₀ x₀ N ℓ z - x₀) ^ 2 ∂stdNormalSeq :=
          integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _) (hYint.const_mul _)
            (ae_of_all _ fun z => sq_sub_le_of_lipschitzWith hf _ _)
      _ = (Kf : ℝ) ^ 2 * ∫ z, (contractPath a b h₀ x₀ N ℓ z - x₀) ^ 2 ∂stdNormalSeq :=
          integral_const_mul _ _
      _ ≤ (Kf : ℝ) ^ 2 * contractM a b Ka Kb δ h₀ x₀ := by
          gcongr
          rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
            hYm.aestronglyMeasurable]
          exact ENNReal.toReal_le_of_le_ofReal hM0 hM

/-- The second moment of the level correction `f(X^f_{ℓ+1}) − f(X^c_ℓ)` for a `K_f`-Lipschitz
payoff (Giles 2015, §10.1): `E[(f(X^f) − f(X^c))²] ≤ K_f² (C₁ h_{ℓ+1} + C₂ e^{−δ T_ℓ/8})`,
`T_ℓ = N_ℓ h_ℓ`. -/
lemma integral_sq_contractDiff_le (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h₀ : ℝ}
    (hh₀ : 0 < h₀) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * h₀ + δ ≤ 2 * κ) (x₀ : ℝ)
    {N : ℕ → ℕ} (hN : ∀ ℓ, 2 * N ℓ ≤ N (ℓ + 1)) {f : ℝ → ℝ} {Kf : ℝ≥0}
    (hf : LipschitzWith Kf f) (ℓ : ℕ) :
    ∫ z, (f (contractPath a b h₀ x₀ N (ℓ + 1) z) -
        f (contractPath a b h₀ x₀ N ℓ (pairAvg z))) ^ 2 ∂stdNormalSeq ≤
      (Kf : ℝ) ^ 2 * (contractC₁ a b Ka Kb δ h₀ x₀ * (h₀ / 2 ^ (ℓ + 1)) +
        contractC₂ a b Ka Kb δ h₀ x₀ * Real.exp (-(δ * (N ℓ * (h₀ / 2 ^ ℓ))) / 8)) := by
  obtain ⟨hint, hI⟩ := contractPath_sq_le ha hb hdiss hδ hh₀ hmargin x₀ hN ℓ
  calc ∫ z, (f (contractPath a b h₀ x₀ N (ℓ + 1) z) -
        f (contractPath a b h₀ x₀ N ℓ (pairAvg z))) ^ 2 ∂stdNormalSeq
      ≤ ∫ z, (Kf : ℝ) ^ 2 * (contractPath a b h₀ x₀ N (ℓ + 1) z -
          contractPath a b h₀ x₀ N ℓ (pairAvg z)) ^ 2 ∂stdNormalSeq :=
        integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _) (hint.const_mul _)
          (ae_of_all _ fun z => sq_sub_le_of_lipschitzWith hf _ _)
    _ = (Kf : ℝ) ^ 2 * ∫ z, (contractPath a b h₀ x₀ N (ℓ + 1) z -
          contractPath a b h₀ x₀ N ℓ (pairAvg z)) ^ 2 ∂stdNormalSeq := integral_const_mul _ _
    _ ≤ _ := by gcongr

/-- **The multilevel variance of a contracting SDE with level-dependent time steps** (Giles 2015,
§10.1, p. 61: "the level `ℓ` path will perform a simulation for the time interval `[−T_ℓ, 0]`,
using timestep `h_ℓ`.  The coarse and fine paths will share the same driving Brownian path for
the overlapping time interval `[−T_{ℓ−1}, 0]`, and the contraction property will ensure that the
multilevel variance decays with level").  Let the steps be `h_ℓ = h₀ 2^{−ℓ}` and let level `ℓ`
take `N_ℓ` steps, `T_ℓ = N_ℓ h_ℓ`, with `2N_ℓ ≤ N_{ℓ+1}` (so `T_ℓ ≤ T_{ℓ+1}`), all driven by
one sequence `z` of standard normals: the fine path of a level-`(ℓ + 1)` sample uses the
increments `√h_{ℓ+1} z_k` (`contractPath (ℓ + 1) z`), and its coarse path is the level-`ℓ` path
driven by `(z_{2k} + z_{2k+1})/√2` (`contractPath ℓ (pairAvg z)`), i.e. by the sums of pairs of
the fine Brownian increments (`contractPath_pairAvg`), which have the law of the level-`ℓ`
increments (`measurePreserving_pairAvg`).  With the hypotheses of
`lintegral_sq_fine_sub_coarse_le` for `H = h₀` and a `K_f`-Lipschitz payoff `f`:
`V_{ℓ+1} = V[f(X^f_{ℓ+1}) − f(X^c_ℓ)] ≤ K_f² (C₁ h_{ℓ+1} + C₂ e^{−δ T_ℓ/8})`.  Deviations as in
`lintegral_sq_fine_sub_coarse_le`; the payoff is Lipschitz. -/
theorem variance_contractLevels_le (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h₀ : ℝ}
    (hh₀ : 0 < h₀) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * h₀ + δ ≤ 2 * κ) (x₀ : ℝ)
    {N : ℕ → ℕ} (hN : ∀ ℓ, 2 * N ℓ ≤ N (ℓ + 1)) {f : ℝ → ℝ} {Kf : ℝ≥0}
    (hf : LipschitzWith Kf f) (ℓ : ℕ) :
    variance (fun z => f (contractPath a b h₀ x₀ N (ℓ + 1) z) -
        f (contractPath a b h₀ x₀ N ℓ (pairAvg z))) stdNormalSeq ≤
      (Kf : ℝ) ^ 2 * (contractC₁ a b Ka Kb δ h₀ x₀ * (h₀ / 2 ^ (ℓ + 1)) +
        contractC₂ a b Ka Kb δ h₀ x₀ * Real.exp (-(δ * (N ℓ * (h₀ / 2 ^ ℓ))) / 8)) := by
  have hfm : Measurable f := hf.continuous.measurable
  have hm : Measurable fun z => f (contractPath a b h₀ x₀ N (ℓ + 1) z) -
      f (contractPath a b h₀ x₀ N ℓ (pairAvg z)) :=
    (hfm.comp (measurable_contractPath ha hb h₀ x₀ N (ℓ + 1))).sub
      (hfm.comp ((measurable_contractPath ha hb h₀ x₀ N ℓ).comp
        measurePreserving_pairAvg.measurable))
  have hv := variance_le_expectation_sq (μ := stdNormalSeq) hm.aestronglyMeasurable
  simp only [Pi.pow_apply] at hv
  exact hv.trans (integral_sq_contractDiff_le ha hb hdiss hδ hh₀ hmargin x₀ hN hf ℓ)

/-- With `T_ℓ = N_ℓ h_ℓ ≥ c ℓ` and `c δ ≥ 8 log 2`:
`C₁ h_{ℓ+1} + C₂ e^{−δ T_ℓ/8} ≤ (C₁ h₀ + 2 C₂) 2^{−(ℓ+1)}` (Giles 2015, §10.1). -/
lemma contract_bound_le_two_pow {C₁ C₂ h₀ δ c : ℝ} (hC₂ : 0 ≤ C₂) (hδ : 0 < δ)
    {N : ℕ → ℕ} (hc : 8 * Real.log 2 ≤ c * δ) (hT : ∀ ℓ : ℕ, c * ℓ ≤ N ℓ * (h₀ / 2 ^ ℓ))
    (ℓ : ℕ) :
    C₁ * (h₀ / 2 ^ (ℓ + 1)) + C₂ * Real.exp (-(δ * (N ℓ * (h₀ / 2 ^ ℓ))) / 8) ≤
      (C₁ * h₀ + 2 * C₂) * (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) := by
  have h2 : (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) = (2 ^ (ℓ + 1))⁻¹ := by
    rw [Real.rpow_neg zero_le_two, Real.rpow_natCast]
  have hexp : Real.exp (-(δ * (N ℓ * (h₀ / 2 ^ ℓ))) / 8) ≤
      2 * (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) := by
    have e1 : 2 * (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) = Real.exp (Real.log 2 * (-(ℓ : ℝ))) := by
      rw [← Real.rpow_def_of_pos two_pos,
        show (-((ℓ + 1 : ℕ) : ℝ)) = -(ℓ : ℝ) + (-1) by push_cast; ring,
        Real.rpow_add two_pos, Real.rpow_neg_one]
      ring
    rw [e1, Real.exp_le_exp]
    have h3 : 8 * Real.log 2 * ℓ ≤ c * δ * ℓ := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg ℓ)
    have h4 := mul_le_mul_of_nonneg_left (hT ℓ) hδ.le
    linarith
  have hh : h₀ / 2 ^ (ℓ + 1) = h₀ * (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) := by
    rw [h2, div_eq_mul_inv]
  rw [hh]
  nlinarith [mul_le_mul_of_nonneg_left hexp hC₂]

/-- **`β = 1` for a linearly growing simulation interval** (Giles 2015, §10.1, p. 61: "it is
appropriate to choose `N_ℓ` to increase linearly with level", said for Markov chains; for the SDE
the analogue is `T_ℓ` linear in `ℓ`).  With the hypotheses of `variance_contractLevels_le`, if
`T_ℓ = N_ℓ h_ℓ ≥ c ℓ` with `c δ ≥ 8 log 2`, then
`V_{ℓ+1} ≤ K_f² (C₁ h₀ + 2 C₂) 2^{−(ℓ+1)}`: the variance rate is `β = 1`, that of the `O(h)`
mean-square difference of the Euler–Maruyama coupling, and the effect of the fine path's initial
segment decays at least as fast.  For example `N_ℓ = m (ℓ + 1) 2^ℓ` (`T_ℓ = m h₀ (ℓ + 1)`) with
`m h₀ δ ≥ 8 log 2`. -/
theorem variance_contractLevels_le_two_pow (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h₀ : ℝ}
    (hh₀ : 0 < h₀) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * h₀ + δ ≤ 2 * κ) (x₀ : ℝ)
    {N : ℕ → ℕ} (hN : ∀ ℓ, 2 * N ℓ ≤ N (ℓ + 1)) {c : ℝ} (hc : 8 * Real.log 2 ≤ c * δ)
    (hT : ∀ ℓ : ℕ, c * ℓ ≤ N ℓ * (h₀ / 2 ^ ℓ)) {f : ℝ → ℝ} {Kf : ℝ≥0}
    (hf : LipschitzWith Kf f) (ℓ : ℕ) :
    variance (fun z => f (contractPath a b h₀ x₀ N (ℓ + 1) z) -
        f (contractPath a b h₀ x₀ N ℓ (pairAvg z))) stdNormalSeq ≤
      (Kf : ℝ) ^ 2 * (contractC₁ a b Ka Kb δ h₀ x₀ * h₀ + 2 * contractC₂ a b Ka Kb δ h₀ x₀) *
        (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) := by
  refine (variance_contractLevels_le ha hb hdiss hδ hh₀ hmargin x₀ hN hf ℓ).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (contract_bound_le_two_pow
    (contractC₂_nonneg a b Ka Kb hδ hh₀.le x₀) hδ hc hT ℓ) (sq_nonneg _)

/-- **Linearly growing simulation intervals satisfy the hypotheses** (Giles 2015, §10.1, p. 61: "it
is appropriate to choose `N_ℓ` to increase linearly with level"): the levels `N_ℓ = m (ℓ + 1) 2^ℓ`,
i.e. `T_ℓ = N_ℓ h_ℓ = m h₀ (ℓ + 1)`, satisfy `2 N_ℓ ≤ N_{ℓ+1}` and `T_ℓ ≥ c ℓ` with `c = m h₀`,
as `variance_contractLevels_le_two_pow` and `contracting_levels_mlmc` require (with
`m h₀ δ ≥ 8 log 2`); the bound `N_ℓ ≤ m (ℓ + 1) 2^ℓ` holds with equality. -/
lemma linear_levels (m : ℕ) {h₀ : ℝ} (hh₀ : 0 ≤ h₀) :
    (∀ ℓ, 2 * (m * (ℓ + 1) * 2 ^ ℓ) ≤ m * (ℓ + 1 + 1) * 2 ^ (ℓ + 1)) ∧
      ∀ ℓ : ℕ, m * h₀ * ℓ ≤ ((m * (ℓ + 1) * 2 ^ ℓ : ℕ) : ℝ) * (h₀ / 2 ^ ℓ) := by
  refine ⟨fun ℓ => ?_, fun ℓ => ?_⟩
  · have h1 : m * (ℓ + 1) ≤ m * (ℓ + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    calc 2 * (m * (ℓ + 1) * 2 ^ ℓ) = m * (ℓ + 1) * 2 ^ (ℓ + 1) := by ring
      _ ≤ m * (ℓ + 1 + 1) * 2 ^ (ℓ + 1) := Nat.mul_le_mul_right _ h1
  · have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
    have e : ((m * (ℓ + 1) * 2 ^ ℓ : ℕ) : ℝ) * (h₀ / 2 ^ ℓ) = m * h₀ * ((ℓ : ℝ) + 1) := by
      push_cast
      field_simp
    rw [e]
    have : 0 ≤ (m : ℝ) * h₀ := by positivity
    nlinarith

/-- **The stationary Euler–Maruyama chain of level `ℓ`** (Giles 2015, §10.1, p. 61: "contracting
SDEs which converge to a limiting distribution"): the limit, as the starting time recedes to
`−∞`, of the Euler–Maruyama chain with step `h_ℓ = h₀ 2^{−ℓ}` started at `x₀`, whose step ending
at time `−k h_ℓ` uses the Brownian increment `√h_ℓ z_k` (`limUnder`; the limit exists almost
surely, `sq_integral_backIter_sub_limit_le`).  Its law is the limiting (invariant) distribution of
the discretised chain (`MlmcLean/MarkovLimitLaw.lean`). -/
noncomputable def contractLimit (a b : ℝ → ℝ) (h₀ x₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  limUnder atTop fun n =>
    backIter (emStep a b (h₀ / 2 ^ ℓ)) n (fun k => Real.sqrt (h₀ / 2 ^ ℓ) * z k) x₀

/-- **The chain started in the past is close to the stationary chain of the same step** (Giles 2015,
§10.1, p. 61).  For the Euler–Maruyama chain with step `0 < v ≤ h₀` driven by `√v z_k`, the
chains started `n` steps in the past converge almost surely as `n → ∞`, and for a
`K_f`-Lipschitz payoff, with `K = max(K_f, 1)`:
`(E[f(X^v_n)] − E[f(X^v_∞)])² ≤ 4K² (a(x₀)² h₀ + b(x₀)²)/(δ² v) · e^{−δ n v}`
(`sq_integral_sub_limit_le` with the mean-square contraction `emStep_meanSquare_contraction`). -/
lemma sq_integral_backIter_sub_limit_le (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h₀ : ℝ}
    (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * h₀ + δ ≤ 2 * κ) (x₀ : ℝ) {v : ℝ≥0}
    (hv0 : 0 < v) (hvle : (v : ℝ) ≤ h₀) (n : ℕ) {f : ℝ → ℝ} {Kf : ℝ≥0}
    (hf : LipschitzWith Kf f) :
    (∀ᵐ z ∂stdNormalSeq, Tendsto (fun n => backIter (emStep a b v) n
        (fun k => Real.sqrt v * z k) x₀) atTop (𝓝 (limUnder atTop fun n =>
          backIter (emStep a b v) n (fun k => Real.sqrt v * z k) x₀))) ∧
      (∫ z, f (backIter (emStep a b v) n (fun k => Real.sqrt v * z k) x₀) ∂stdNormalSeq -
          ∫ z, f (limUnder atTop fun n =>
            backIter (emStep a b v) n (fun k => Real.sqrt v * z k) x₀) ∂stdNormalSeq) ^ 2 ≤
        4 * max (Kf : ℝ) 1 ^ 2 * (a x₀ ^ 2 * h₀ + b x₀ ^ 2) / (δ ^ 2 * v) *
          Real.exp (-(δ * (n * v))) := by
  have hpos : (0 : ℝ) < v := hv0
  obtain ⟨hξ, hξm, hlaw⟩ := scaled_stdNormal v
  have hstep : (Kb : ℝ) ^ 2 + (Ka : ℝ) ^ 2 * v < 2 * κ := by
    have h1 := mul_le_mul_of_nonneg_left hvle (sq_nonneg (Ka : ℝ))
    have h2 : (0 : ℝ) ≤ (Ka : ℝ) ^ 2 * h₀ := by nlinarith [sq_nonneg (Ka : ℝ)]
    linarith
  obtain ⟨hρ0, hρ1, hcon⟩ := emStep_meanSquare_contraction ha hb hdiss hv0 hstep
  have hma : Measurable a := ha.continuous.measurable
  have hmb : Measurable b := hb.continuous.measurable
  have hφm : Measurable fun q : ℝ × ℝ => emStep a b v q.1 q.2 := by
    unfold emStep
    fun_prop
  have hφw : ∀ x, Measurable (emStep a b v x) := fun x => by
    unfold emStep
    fun_prop
  have hφ := lintegral_dist_rpow_le_of_sq hφw hρ0 hcon one_pos le_rfl
  have hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (emStep a b v x₀ e) ^ (2 * (1 : ℝ)))
      ∂gaussianReal 0 v = ENNReal.ofReal ((a x₀ * v) ^ 2 + b x₀ ^ 2 * v) := by
    have e1 : ∀ e, dist x₀ (emStep a b v x₀ e) ^ (2 * (1 : ℝ)) =
        (-(a x₀ * v) + (-b x₀) * e) ^ 2 := fun e => by
      rw [mul_one, Real.rpow_two, Real.dist_eq, sq_abs]
      unfold emStep
      ring
    simp_rw [e1]
    rw [lintegral_sq_affine_gaussianReal]
    congr 1
    ring
  have hcfin : ∫⁻ e, ENNReal.ofReal (dist x₀ (emStep a b v x₀ e) ^ (2 * (1 : ℝ)))
      ∂gaussianReal 0 v ≠ ∞ := by
    rw [hc]
    exact ENNReal.ofReal_ne_top
  have hρ'0 := Real.rpow_nonneg hρ0 (1 : ℝ)
  have hρ'1 := Real.rpow_lt_one hρ0 hρ1 one_pos
  have hX : ∀ᵐ z ∂stdNormalSeq, Tendsto (fun n => backIter (emStep a b v) n
      (fun k => Real.sqrt v * z k) x₀) atTop (𝓝 (limUnder atTop fun n =>
        backIter (emStep a b v) n (fun k => Real.sqrt v * z k) x₀)) :=
    (ae_tendsto_backIter hφm (by norm_num) hρ'0 hρ'1 hφ hξ hξm hlaw x₀ hcfin).mono
      fun z hz => tendsto_nhds_limUnder hz
  refine ⟨hX, ?_⟩
  -- the payoff normalised to a `1`-Lipschitz function
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max (Kf : ℝ) 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK ▸ le_max_right _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hgm : Measurable fun x => f x / K := hf.continuous.measurable.div_const K
  have hg : ∀ x y, |f x / K - f y / K| ≤ dist x y ^ (1 : ℝ) := fun x y => by
    rw [← sub_div, abs_div, abs_of_pos hK0, div_le_iff₀ hK0, Real.rpow_one, Real.dist_eq]
    calc |f x - f y| ≤ Kf * |x - y| := abs_sub_le_of_lipschitzWith hf x y
      _ ≤ |x - y| * K := by
        rw [mul_comm, hK]
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg _)
  have key := sq_integral_sub_limit_le hφm hφ hξ hξm hlaw one_pos le_rfl hρ'0 hρ'1 x₀ hcfin hgm hg
    hX n
  rw [hc, integral_div, integral_div, ← sub_div, div_pow, div_le_iff₀ (by positivity),
    Real.rpow_one, ENNReal.toReal_ofReal (by positivity)] at key
  rw [← hK]
  -- the constants of the contraction
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = 1 - 2 * κ * v + (Ka : ℝ) ^ 2 * (v : ℝ) ^ 2 +
      (Kb : ℝ) ^ 2 * v := ⟨_, rfl⟩
  rw [← hρdef] at key
  have hρ0' : 0 ≤ ρ := by rw [hρdef]; exact hρ0
  have hρδ : ρ ≤ 1 - v * δ := by
    rw [hρdef]
    have h1 := mul_le_mul_of_nonneg_left hmargin hpos.le
    have h2 : (v : ℝ) * (v * (Ka : ℝ) ^ 2) ≤ v * (h₀ * (Ka : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvle (sq_nonneg _)) hpos.le
    nlinarith [mul_nonneg (mul_nonneg hpos.le hpos.le) (sq_nonneg (Ka : ℝ))]
  have h1ρ : (v : ℝ) * δ ≤ 1 - ρ := by linarith
  have hhδ : 0 < (v : ℝ) * δ := mul_pos hpos hδ
  have hcS : (a x₀ * v) ^ 2 + b x₀ ^ 2 * v ≤ v * (a x₀ ^ 2 * h₀ + b x₀ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hvle (mul_nonneg hpos.le (sq_nonneg (a x₀)))
    nlinarith
  have hsq1ρ : ((v : ℝ) * δ) ^ 2 ≤ (1 - ρ) ^ 2 := pow_le_pow_left₀ hhδ.le h1ρ 2
  have hρN : ρ ^ n ≤ Real.exp (-(δ * (n * v))) := by
    have h1 : ρ ≤ Real.exp (-(v * δ)) := by
      linarith [Real.add_one_le_exp (-((v : ℝ) * δ))]
    calc ρ ^ n ≤ Real.exp (-(v * δ)) ^ n := pow_le_pow_left₀ hρ0' h1 _
      _ = Real.exp (-(δ * (n * v))) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hS0 : 0 ≤ a x₀ ^ 2 * h₀ + b x₀ ^ 2 := by
    have : 0 ≤ h₀ := hpos.le.trans hvle
    positivity
  have hS1 : 0 ≤ 4 * (a x₀ ^ 2 * h₀ + b x₀ ^ 2) / (δ ^ 2 * v) :=
    div_nonneg (mul_nonneg (by norm_num) hS0) (by positivity)
  have hfrac : 4 / (1 - ρ) ^ 2 * ((a x₀ * v) ^ 2 + b x₀ ^ 2 * v) ≤
      4 * (a x₀ ^ 2 * h₀ + b x₀ ^ 2) / (δ ^ 2 * v) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hsq1ρ
      (by positivity : (0 : ℝ) ≤ 4 * (a x₀ ^ 2 * h₀ + b x₀ ^ 2))
    have h2 := mul_le_mul_of_nonneg_right hcS (by positivity : (0 : ℝ) ≤ 4 * δ ^ 2 * v)
    nlinarith
  calc (∫ z, f (backIter (emStep a b v) n (fun k => Real.sqrt v * z k) x₀) ∂stdNormalSeq -
        ∫ z, f (limUnder atTop fun n =>
          backIter (emStep a b v) n (fun k => Real.sqrt v * z k) x₀) ∂stdNormalSeq) ^ 2
      ≤ 4 / (1 - ρ) ^ 2 * ((a x₀ * v) ^ 2 + b x₀ ^ 2 * v) * ρ ^ n * K ^ 2 := key
    _ ≤ 4 * (a x₀ ^ 2 * h₀ + b x₀ ^ 2) / (δ ^ 2 * v) * Real.exp (-(δ * (n * v))) * K ^ 2 := by
        gcongr
    _ = 4 * K ^ 2 * (a x₀ ^ 2 * h₀ + b x₀ ^ 2) / (δ ^ 2 * v) * Real.exp (-(δ * (n * v))) := by
        ring

/-- **The level paths and the stationary chains of the level steps have the same limiting mean**
(Giles 2015, §10.1, p. 61): if `T_ℓ = N_ℓ h_ℓ ≥ c ℓ` with `c δ ≥ 8 log 2`, then
`E[f(X^{(ℓ)})] − E[f(X^{h_ℓ}_∞)] → 0` for every Lipschitz payoff `f`
(`sq_integral_backIter_sub_limit_le`: the square is at most
`4K² (a(x₀)² h₀ + b(x₀)²)/(δ² h₀) · 128^{−ℓ}`). -/
lemma tendsto_integral_contractPath_sub_limit (ha : LipschitzWith Ka a)
    (hb : LipschitzWith Kb b) (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2))
    (hδ : 0 < δ) {h₀ : ℝ} (hh₀ : 0 < h₀)
    (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * h₀ + δ ≤ 2 * κ) (x₀ : ℝ) {N : ℕ → ℕ} {c : ℝ}
    (hc : 8 * Real.log 2 ≤ c * δ) (hT : ∀ ℓ : ℕ, c * ℓ ≤ N ℓ * (h₀ / 2 ^ ℓ)) {f : ℝ → ℝ}
    {Kf : ℝ≥0} (hf : LipschitzWith Kf f) :
    Tendsto (fun ℓ => ∫ z, f (contractPath a b h₀ x₀ N ℓ z) ∂stdNormalSeq -
      ∫ z, f (contractLimit a b h₀ x₀ ℓ z) ∂stdNormalSeq) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = 4 * max (Kf : ℝ) 1 ^ 2 * (a x₀ ^ 2 * h₀ + b x₀ ^ 2) / (δ ^ 2 * h₀) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have e256 : Real.exp (-(8 * Real.log 2)) = 1 / 256 := by
    rw [Real.exp_neg, show (8 : ℝ) * Real.log 2 = ((8 : ℕ) : ℝ) * Real.log 2 by norm_num,
      Real.exp_nat_mul, Real.exp_log two_pos]
    norm_num
  have hbound : ∀ ℓ : ℕ, (∫ z, f (contractPath a b h₀ x₀ N ℓ z) ∂stdNormalSeq -
      ∫ z, f (contractLimit a b h₀ x₀ ℓ z) ∂stdNormalSeq) ^ 2 ≤ C * (1 / 128) ^ ℓ := by
    intro ℓ
    have hpos : 0 < h₀ / 2 ^ ℓ := by positivity
    have hle : h₀ / 2 ^ ℓ ≤ h₀ := div_le_self hh₀.le (one_le_pow₀ (by norm_num))
    have h1 := (sq_integral_backIter_sub_limit_le ha hb hdiss hδ hmargin x₀
      (v := ⟨h₀ / 2 ^ ℓ, hpos.le⟩) hpos hle (N ℓ) hf).2
    refine h1.trans ?_
    show 4 * max (Kf : ℝ) 1 ^ 2 * (a x₀ ^ 2 * h₀ + b x₀ ^ 2) / (δ ^ 2 * (h₀ / 2 ^ ℓ)) *
      Real.exp (-(δ * (N ℓ * (h₀ / 2 ^ ℓ)))) ≤ C * (1 / 128) ^ ℓ
    have hexp : Real.exp (-(δ * (N ℓ * (h₀ / 2 ^ ℓ)))) ≤ (1 / 256) ^ ℓ := by
      rw [← e256, ← Real.exp_nat_mul, Real.exp_le_exp]
      have h3 : 8 * Real.log 2 * ℓ ≤ c * δ * ℓ :=
        mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg ℓ)
      have h4 := mul_le_mul_of_nonneg_left (hT ℓ) hδ.le
      linarith
    have hS0 : 0 ≤ 4 * max (Kf : ℝ) 1 ^ 2 * (a x₀ ^ 2 * h₀ + b x₀ ^ 2) /
        (δ ^ 2 * (h₀ / 2 ^ ℓ)) := by positivity
    have e2 : 4 * max (Kf : ℝ) 1 ^ 2 * (a x₀ ^ 2 * h₀ + b x₀ ^ 2) / (δ ^ 2 * (h₀ / 2 ^ ℓ)) *
        (1 / 256) ^ ℓ = C * (1 / 128) ^ ℓ := by
      rw [hC, show (1 / 128 : ℝ) = 2 * (1 / 256) by norm_num, mul_pow]
      field_simp
    rw [← e2]
    exact mul_le_mul_of_nonneg_left hexp hS0
  have hlim : Tendsto (fun ℓ : ℕ => Real.sqrt (C * (1 / 128) ^ ℓ)) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 128)
      (by norm_num)).const_mul C)
    rw [mul_zero] at h
    have h' := (Real.continuous_sqrt.tendsto 0).comp h
    rwa [Real.sqrt_zero] at h'
  refine squeeze_zero_norm (fun ℓ => ?_) hlim
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (hbound ℓ)

/-- **Theorem 1 end to end for a contracting SDE with level-dependent time steps** (Giles 2015,
§10.1, p. 61: "A very similar approach can also be used for contracting SDEs which converge to a
limiting distribution.  For these, the level `ℓ` path will perform a simulation for the time
interval `[−T_ℓ, 0]`, using timestep `h_ℓ` …", with §2.1, Theorem 1).  With the hypotheses of
`variance_contractLevels_le_two_pow` (dissipative Lipschitz drift, Lipschitz volatility, margin
`K_b² + 2K_a²h₀ + δ ≤ 2κ`, `h_ℓ = h₀ 2^{−ℓ}`, `2N_ℓ ≤ N_{ℓ+1}`, `T_ℓ = N_ℓ h_ℓ ≥ c ℓ` with
`c δ ≥ 8 log 2`, a `K_f`-Lipschitz payoff `f`) and `N_ℓ ≤ m (ℓ + 1) 2^ℓ`:
(1) the level means converge, `E[f(X^{(ℓ)})] → P`, and also `E[f(X^{h_ℓ}_∞)] → P`, where
`X^h_∞` is the stationary Euler–Maruyama chain with step `h` (`contractLimit`, the almost sure
limit of the chain started further and further in the past): `P` is the limit, along
`h_ℓ → 0`, of the means under the limiting distributions of the discretised chains;
(2) for every `η > 0` there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and
sample sizes `M_ℓ ≥ 1` for which the multilevel estimator
`∑_{ℓ ≤ L} M_ℓ⁻¹ ∑_{n < M_ℓ} (f(X^f_ℓ) − f(X^c_{ℓ−1}))(z^{(ℓ,n)})` (with `f(X^c_{−1}) ≡ 0` and
independent copies `z^{(ℓ,n)}` of the normal sequence) has mean square error `< ε²` about `P`,
at cost `∑_{ℓ ≤ L} M_ℓ N_ℓ ≤ c₄ ε^{−2−2η}`.
Theorem 1 is applied with `α = 1/2` (the means form a Cauchy sequence with
`|E[f(X^{(ℓ+1)})] − E[f(X^{(ℓ)})]| = O(2^{−ℓ/2})`, by (2.4) and the variance bound), `β = 1`
and `γ = 1 + η`.  Deviations: the cost of a sample is counted as the `N_ℓ` steps of its fine
path (the coarse path adds `N_{ℓ−1} ≤ N_ℓ/2` more); the cost `N_ℓ ≍ T_ℓ/h_ℓ` grows like `ℓ 2^ℓ`,
not like `2^ℓ`, so Theorem 1 (which needs `C_ℓ ≤ c₃ 2^{γℓ}`) gives `ε^{−2−2η}` for every
`η > 0`; the target `P` is identified with the limit of the means under the limiting
distributions of the Euler–Maruyama chains, not with the mean under the invariant law of the
SDE: that identification needs SDE theory (convergence of the invariant laws of the scheme as
`h → 0`) that the library does not have. -/
theorem contracting_levels_mlmc (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h₀ : ℝ}
    (hh₀ : 0 < h₀) (hmargin : (Kb : ℝ) ^ 2 + 2 * (Ka : ℝ) ^ 2 * h₀ + δ ≤ 2 * κ) (x₀ : ℝ)
    {N : ℕ → ℕ} (hN : ∀ ℓ, 2 * N ℓ ≤ N (ℓ + 1)) {c : ℝ} (hc : 8 * Real.log 2 ≤ c * δ)
    (hT : ∀ ℓ : ℕ, c * ℓ ≤ N ℓ * (h₀ / 2 ^ ℓ)) {m : ℕ}
    (hNm : ∀ ℓ, N ℓ ≤ m * (ℓ + 1) * 2 ^ ℓ) {f : ℝ → ℝ} {Kf : ℝ≥0} (hf : LipschitzWith Kf f)
    {η : ℝ} (hη : 0 < η) :
    ∃ P : ℝ, Tendsto (fun ℓ => ∫ z, f (contractPath a b h₀ x₀ N ℓ z) ∂stdNormalSeq) atTop
        (𝓝 P) ∧
      Tendsto (fun ℓ => ∫ z, f (contractLimit a b h₀ x₀ ℓ z) ∂stdNormalSeq) atTop (𝓝 P) ∧
      ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (M : ℕ → ℕ), (∀ ℓ, 0 < M ℓ) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ z => f (contractPath a b h₀ x₀ N ℓ z))
              (fun ℓ z => f (contractPath a b h₀ x₀ N ℓ (pairAvg z)))) (fun p x => x p) ℓ
                (M ℓ) x - P) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
          ∫ x, totalCost (fun ℓ _ _ => (N ℓ : ℝ)) L M x
              ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ≤
            c₄ * ε ^ (-2 - 2 * η) := by
  -- the level approximations
  obtain ⟨Pf, hPfdef⟩ : ∃ Pf : ℕ → (ℕ → ℝ) → ℝ,
      Pf = fun ℓ z => f (contractPath a b h₀ x₀ N ℓ z) := ⟨_, rfl⟩
  obtain ⟨Pc, hPcdef⟩ : ∃ Pc : ℕ → (ℕ → ℝ) → ℝ,
      Pc = fun ℓ z => f (contractPath a b h₀ x₀ N ℓ (pairAvg z)) := ⟨_, rfl⟩
  have hfm : Measurable f := hf.continuous.measurable
  have hPfm : ∀ ℓ, Measurable (Pf ℓ) := fun ℓ => by
    rw [hPfdef]
    exact hfm.comp (measurable_contractPath ha hb h₀ x₀ N ℓ)
  have hPcPf : ∀ ℓ, Pc ℓ = Pf ℓ ∘ pairAvg := fun ℓ => by
    rw [hPcdef, hPfdef]
    rfl
  have hPcm : ∀ ℓ, Measurable (Pc ℓ) := fun ℓ => by
    rw [hPcPf]
    exact (hPfm ℓ).comp measurePreserving_pairAvg.measurable
  have hPf : ∀ ℓ, MemLp (Pf ℓ) 2 stdNormalSeq := fun ℓ => by
    rw [hPfdef]
    exact (memLp_contractPath ha hb hdiss hδ hh₀ hmargin x₀ N hf ℓ).1
  have hPc : ∀ ℓ, MemLp (Pc ℓ) 2 stdNormalSeq := fun ℓ => by
    rw [hPcPf]
    exact (hPf ℓ).comp_measurePreserving measurePreserving_pairAvg
  have h24 : ∀ ℓ, ∫ z, Pf ℓ z ∂stdNormalSeq = ∫ z, Pc ℓ z ∂stdNormalSeq := fun ℓ => by
    rw [hPcPf]
    exact (integral_comp_of_measurePreserving measurePreserving_pairAvg
      (hPfm ℓ).aestronglyMeasurable).symm
  -- the constants
  have hC₁ := contractC₁_nonneg a b Ka Kb hδ hh₀.le x₀
  have hC₂ := contractC₂_nonneg a b Ka Kb hδ hh₀.le x₀
  have hM₀ := contractM_nonneg a b Ka Kb hδ hh₀.le x₀
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (Kf : ℝ) ^ 2 *
      (contractC₁ a b Ka Kb δ h₀ x₀ * h₀ + 2 * contractC₂ a b Ka Kb δ h₀ x₀) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  -- the second moments of the corrections decay like `2^{−ℓ}`
  have hsq : ∀ ℓ : ℕ, ∫ z, (Pf (ℓ + 1) z - Pc ℓ z) ^ 2 ∂stdNormalSeq ≤
      B * (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) := fun ℓ => by
    rw [hPfdef, hPcdef, hB, mul_assoc]
    exact (integral_sq_contractDiff_le ha hb hdiss hδ hh₀ hmargin x₀ hN hf ℓ).trans
      (mul_le_mul_of_nonneg_left (contract_bound_le_two_pow hC₂ hδ hc hT ℓ) (sq_nonneg _))
  -- the means of the levels form a Cauchy sequence: condition (i) with `α = 1/2`
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  have hr2 : ∀ ℓ : ℕ, (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) ≤ (r ^ ℓ) ^ 2 := fun ℓ => by
    have hr2' : r ^ 2 = 2⁻¹ := by
      rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
      norm_num
    have e1 : (r ^ ℓ) ^ 2 = (2 ^ ℓ)⁻¹ := by
      rw [← pow_mul, mul_comm, pow_mul, hr2', inv_pow]
    rw [e1, Real.rpow_neg zero_le_two, Real.rpow_natCast, pow_succ]
    apply inv_anti₀ (by positivity)
    have : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    linarith
  have hmean : ∀ ℓ : ℕ, dist (∫ z, Pf ℓ z ∂stdNormalSeq) (∫ z, Pf (ℓ + 1) z ∂stdNormalSeq) ≤
      Real.sqrt B * r ^ ℓ := fun ℓ => by
    have hY : MemLp (fun z => Pf (ℓ + 1) z - Pc ℓ z) 2 stdNormalSeq := (hPf (ℓ + 1)).sub (hPc ℓ)
    have hvar := variance_nonneg (fun z => Pf (ℓ + 1) z - Pc ℓ z) stdNormalSeq
    rw [variance_eq_sub hY] at hvar
    simp only [Pi.pow_apply] at hvar
    have hsub : ∫ z, (Pf (ℓ + 1) z - Pc ℓ z) ∂stdNormalSeq =
        ∫ z, Pf (ℓ + 1) z ∂stdNormalSeq - ∫ z, Pc ℓ z ∂stdNormalSeq :=
      integral_sub ((hPf _).integrable one_le_two) ((hPc _).integrable one_le_two)
    rw [Real.dist_eq, abs_sub_comm, h24 ℓ, ← hsub]
    apply abs_le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, Real.sq_sqrt hB0]
    have := mul_le_mul_of_nonneg_left (hr2 ℓ) hB0
    linarith [hsq ℓ]
  obtain ⟨P, hP⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric r _ hr1 hmean)
  have hrpow : ∀ ℓ : ℕ, r ^ ℓ = (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) := fun ℓ => by
    rw [hrdef, show -(1 / 2 * (ℓ : ℝ)) = -(1 / 2) * (ℓ : ℝ) by ring,
      Real.rpow_mul_natCast zero_le_two]
  -- Theorem 1 on the product space of independent copies of the noise
  obtain ⟨hprob, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have h2η : 1 < (2 : ℝ) ^ η := Real.one_lt_rpow one_lt_two hη
  obtain ⟨c₄, hc₄, H⟩ := giles_theorem1_fineCoarse (μ := Measure.infinitePi fun _ : ℕ × ℕ =>
      stdNormalSeq) (ν := stdNormalSeq) (fun _ => P) Pf Pc (fun p x => x p)
    (fun ℓ _ _ => (N ℓ : ℝ)) (fun ℓ => (N ℓ : ℝ)) (α := 1 / 2) (β := 1) (γ := 1 + η)
    (c₁ := Real.sqrt B / (1 - r) + 1) (c₂ := (Kf : ℝ) ^ 2 * contractM a b Ka Kb δ h₀ x₀ + B + 1)
    (c₃ := m * (1 + ((2 : ℝ) ^ η - 1)⁻¹) + 1) (by norm_num) one_pos (by linarith)
    (by have : 0 < 1 - r := by linarith
        positivity)
    (by positivity) (by have : 0 < (2 : ℝ) ^ η - 1 := by linarith
                        positivity)
    (by rw [min_eq_left (by linarith)]) hω hind (integrable_const P) hPfm hPcm hPf hPc h24
    (fun _ _ => integrable_const _)
    (fun ℓ _ => by rw [integral_const, probReal_univ, one_smul])
    (fun ℓ => by
      have hd := dist_le_of_le_geometric_of_tendsto r _ hr1 hmean hP ℓ
      rw [Real.dist_eq] at hd
      rw [integral_sub ((hPf ℓ).integrable one_le_two) (integrable_const P), integral_const,
        probReal_univ, one_smul, ← hrpow ℓ]
      have h1r : 0 < 1 - r := by linarith
      calc |∫ z, Pf ℓ z ∂stdNormalSeq - P| ≤ Real.sqrt B * r ^ ℓ / (1 - r) := hd
        _ = Real.sqrt B / (1 - r) * r ^ ℓ := by ring
        _ ≤ (Real.sqrt B / (1 - r) + 1) * r ^ ℓ :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0 ℓ))
    (fun ℓ => by
      cases ℓ with
      | zero =>
        have hv0 := variance_le_expectation_sq (μ := stdNormalSeq)
          ((hPfm 0).sub_const (f x₀)).aestronglyMeasurable
        rw [variance_sub_const (hPfm 0).aestronglyMeasurable] at hv0
        simp only [Pi.pow_apply] at hv0
        have h0 : ∫ z, (Pf 0 z - f x₀) ^ 2 ∂stdNormalSeq ≤
            (Kf : ℝ) ^ 2 * contractM a b Ka Kb δ h₀ x₀ := by
          rw [hPfdef]
          exact (memLp_contractPath ha hb hdiss hδ hh₀ hmargin x₀ N hf 0).2
        show variance (Pf 0) stdNormalSeq ≤ _
        rw [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one]
        linarith
      | succ ℓ =>
        have hm : Measurable fun z => Pf (ℓ + 1) z - Pc ℓ z := (hPfm _).sub (hPcm _)
        have hv := variance_le_expectation_sq (μ := stdNormalSeq) hm.aestronglyMeasurable
        simp only [Pi.pow_apply] at hv
        show variance (fun z => Pf (ℓ + 1) z - Pc ℓ z) stdNormalSeq ≤ _
        have hp : 0 ≤ (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) := by positivity
        rw [one_mul]
        have : (Kf : ℝ) ^ 2 * contractM a b Ka Kb δ h₀ x₀ * (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) +
            (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) ≥ 0 := by positivity
        nlinarith [hsq ℓ])
    (fun ℓ => by
      have h1 : (N ℓ : ℝ) ≤ m * ((ℓ : ℝ) + 1) * 2 ^ ℓ := by exact_mod_cast hNm ℓ
      have h2 := succ_le_two_rpow hη ℓ
      have h3 : (2 : ℝ) ^ (η * (ℓ : ℝ)) * 2 ^ ℓ = (2 : ℝ) ^ ((1 + η) * (ℓ : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add two_pos]
        congr 1
        ring
      have h4 : 0 ≤ (2 : ℝ) ^ ((1 + η) * (ℓ : ℝ)) := by positivity
      have h5 : (0 : ℝ) ≤ 2 ^ ℓ := by positivity
      have h6 := mul_le_mul_of_nonneg_right h2 h5
      have h7 := mul_le_mul_of_nonneg_left h6 (Nat.cast_nonneg m)
      calc (N ℓ : ℝ) ≤ m * ((ℓ : ℝ) + 1) * 2 ^ ℓ := h1
        _ ≤ m * ((1 + ((2 : ℝ) ^ η - 1)⁻¹) * 2 ^ (η * (ℓ : ℝ)) * 2 ^ ℓ) := by
            rw [mul_assoc]
            exact h7
        _ = m * (1 + ((2 : ℝ) ^ η - 1)⁻¹) * 2 ^ ((1 + η) * (ℓ : ℝ)) := by
            rw [← h3]
            ring
        _ ≤ (m * (1 + ((2 : ℝ) ^ η - 1)⁻¹) + 1) * 2 ^ ((1 + η) * (ℓ : ℝ)) := by
            nlinarith)
  subst hPfdef hPcdef
  have hlimP : Tendsto (fun ℓ => ∫ z, f (contractLimit a b h₀ x₀ ℓ z) ∂stdNormalSeq) atTop
      (𝓝 P) := by
    have h := hP.sub (tendsto_integral_contractPath_sub_limit ha hb hdiss hδ hh₀ hmargin x₀ hc
      hT hf)
    rw [sub_zero] at h
    exact h.congr fun ℓ => sub_sub_cancel _ _
  refine ⟨P, hP, hlimP, c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, M, hM, hmse, hcost⟩ := H ε hε hε1
  refine ⟨L, M, hM, ?_, ?_⟩
  · rw [integral_const, probReal_univ, one_smul] at hmse
    exact hmse
  · rw [complexityBound_of_gt (by linarith : (1 : ℝ) < 1 + η),
      show (-2 - (1 + η - 1) / (1 / 2) : ℝ) = -2 - 2 * η by ring] at hcost
    exact hcost

end levels

end MLMC
