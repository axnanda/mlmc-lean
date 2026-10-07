import MlmcLean.NestedRates

/-!
# Nested simulation with a piecewise linear `f` and discretised inner paths (Giles 2015, §9.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §9.1 "MLMC
treatment" (p. 58) and §9.2 "MIMC treatment" (p. 60) of the author's version.

§9.2, p. 60: "Following the analysis in (Bujok et al. 2013), if the function `f` is continuous
and piecewise differentiable, rather than being twice differentiable, then in the MLMC treatment
we would get `β = 1.5`, and hence an overall complexity which is `O(ε^{−2.5})`."  This is
Theorem 1 with `α = 1`, `β = 3/2` and `γ = 2` (`2^ℓ` inner samples of an inner approximation with
`2^ℓ` time steps).  `MlmcLean/NestedRates.lean` proves `β = 3/2` for exact inner samples
(`nested_kink_variance_rate`) but only `α = ½` (`nested_kink_bias_rate`), which is below the
`α ≥ ½ min(β, γ) = ¾` that Theorem 1 needs when `γ = 2` (with `α = ½` it applies only with `β`
lowered to `1`, and gives `O(ε⁻⁴)`).  This file proves the missing rates, for
`f(x) = a₀ + a₁x + c max(x − k, 0)`:

* **`α = 1` for exact inner samples** (`nested_kink_bias_rate_one`): if the centred conditional
  fourth moments are bounded and `E_W[g(Z, W)]` puts little mass near the kink,
  `ν{|E_W[g(Z, W)] − k| ≤ t} ≤ c_d t`, then `2^ℓ |E[f(A_{2^ℓ}) − f(E_W[g(Z, W)])]| ≤ C`.
  The linear part of `f` has no bias; for one outer sample the kink contributes
  `|c| E[h]` with `h = (X + e)⁺ − X⁺ − 1{X > 0} e`, `X = E_W[g(z, W)] − k`, `e` the inner sampling
  error, and `0 ≤ h ≤ |e|`, `X² h ≤ |e|³` (`kink_remainder_bounds`), so the conditional bias is
  `O(M^{−1/2})` and `X²` times it is `O(M^{−3/2})` (`fiber_kink_bias_le`); the small ball turns
  these into `O(M⁻¹)` (`integral_le_of_small_ball`).
* **`α = 1` and `β = 3/2` with discretised inner paths** (`nested_kink_sde_bias_rate`,
  `nested_kink_sde_variance_rate`), level `ℓ` using `2^ℓ` inner samples of `g_ℓ` (`nestedSdeP`,
  `nestedSdeDelta`).  The weak and strong orders of the time discretisation are hypotheses (Itô
  calculus is not in Mathlib): first order weak convergence uniformly in the outer sample, and
  strong convergence of order only `¼` in `L²`, `2^{ℓ/2} E[(g_{ℓ+1} − g_ℓ)²] ≤ cₛ`
  (the Euler–Maruyama scheme's strong order `½` implies it), because averaging `2^ℓ` inner samples
  divides the variance of `g_{ℓ+1} − g_ℓ` by `2^ℓ` (`fiber_innerMean_sq_le`,
  `integral_innerMean_levelDiff_sq_le`).  The small-ball hypothesis is made for the exact
  conditional mean only: within the weak error of `E_W[g_ℓ(Z, W)]`
  (`integral_le_of_small_ball_near`).  No measurability or moment of the exact `g` is assumed.
* **The complexity `O(ε^{−2.5})`** (`nested_kink_sde_mlmc_complexity`): Theorem 1
  (`giles_theorem1_corrections`) with `α = 1`, `β = 3/2`, `γ = 2`.
* **The MIMC rates `β₁ = β₂ = 1.5` of the same paragraph are false** ("On the other hand, with MIMC
  we would have `β₁ = β₂ = 1.5` and so the complexity would remain `O(ε⁻²)`"): for an explicit
  example (`kinkInnerApprox`: `Z` uniform on `[0, 1]`, fair inner signs, `g_ℓ = g + 2^{−ℓ}/8`,
  `f(x) = max(x − ½, 0)`) that satisfies all the hypotheses above (`kinkInnerApprox_hypotheses`)
  and has the MLMC rates `α = 1`, `β = 3/2` (`kinkInnerApprox_mlmc_rates`),
  the MIMC correction has mean zero and variance at least `2^{−(2ℓ₂ + j + 17)}` at
  `(2j + 1, ℓ₂ + 1)` for `ℓ₂ ≥ j + 1` (`kinkMimc_variance_ge`), so no bound `C 2^{−β₁ℓ₁ − β₂ℓ₂}`
  with `2β₁ + β₂ > 3` holds (`nested_mimc_kink_rates_false`): not `β₁ = β₂ = 1.5`
  (`nested_mimc_kink_three_halves_false`), nor any `β₁, β₂ > γ₁ = γ₂ = 1`, which Theorem 2 needs
  for the cost `O(ε⁻²)`.  The weak error of the inner discretisation shifts the kink between the
  two inner approximations, and this is not damped by the antithetic difference.

The paper states no hypotheses for this case; the small-ball bound, the bounded centred
conditional fourth moments (centred, so that the conditional mean may be unbounded, e.g. for a
Gaussian or log-normal outer state), and the weak and strong orders of the inner discretisation
are this formalisation's.  Deviation: the paper's `f` is continuous and piecewise
differentiable; here `f` is piecewise linear with one kink, the setting of
`nested_kink_variance_rate`.  Several kinks or curved pieces are not covered (several kinks would
follow by summing the hinge terms, given a small-ball bound at each kink).
-/

open MeasureTheory ProbabilityTheory Finset Filter

namespace MLMC

/-! ### Pointwise inequalities -/

/-- **The remainder of the kink after its linear part** (Giles 2015, §9.2, p. 60, the analysis of
Bujok et al. for a piecewise linear `f`): with `σ = 1{X > 0}`, the remainder
`h = max(X + e, 0) − max(X, 0) − σ e` satisfies `0 ≤ h ≤ |e|` and `X² h ≤ |e|³`; it vanishes
unless `|e| > |X|`, i.e. unless the error `e` carries `X` across the kink. -/
lemma kink_remainder_bounds (X e : ℝ) :
    0 ≤ max (X + e) 0 - max X 0 - (if 0 < X then (1 : ℝ) else 0) * e ∧
      max (X + e) 0 - max X 0 - (if 0 < X then (1 : ℝ) else 0) * e ≤ |e| ∧
      X ^ 2 * (max (X + e) 0 - max X 0 - (if 0 < X then (1 : ℝ) else 0) * e) ≤ |e| ^ 3 := by
  split_ifs with hX
  · rw [max_eq_left hX.le, one_mul]
    rcases le_total 0 (X + e) with h | h
    · rw [max_eq_left h]
      have h3 : 0 ≤ |e| ^ 3 := by positivity
      refine ⟨by linarith, by linarith [abs_nonneg e], by nlinarith⟩
    · rw [max_eq_right h]
      have he : |e| = -e := abs_of_neg (by linarith)
      rw [he]
      have hXe : X ^ 2 ≤ e ^ 2 := by nlinarith
      refine ⟨by linarith, by linarith, ?_⟩
      nlinarith
  · rw [not_lt] at hX
    rw [max_eq_right hX, zero_mul]
    rcases le_total 0 (X + e) with h | h
    · rw [max_eq_left h]
      have he : |e| = e := abs_of_nonneg (by linarith)
      rw [he]
      have hXe : X ^ 2 ≤ e ^ 2 := by nlinarith
      refine ⟨by linarith, by linarith, ?_⟩
      nlinarith
    · rw [max_eq_right h]
      have h3 : 0 ≤ |e| ^ 3 := by positivity
      refine ⟨by linarith, by linarith [abs_nonneg e], by nlinarith⟩

/-- `2 s |e| ≤ s² e² + 1` and `2 s |e|³ ≤ e² + s² e⁴` (AM–GM), for every `s`. -/
lemma two_mul_abs_le_and_cube (s e : ℝ) :
    2 * s * |e| ≤ s ^ 2 * e ^ 2 + 1 ∧ 2 * s * |e| ^ 3 ≤ e ^ 2 + s ^ 2 * e ^ 4 := by
  have h2 : |e| ^ 2 = e ^ 2 := sq_abs e
  constructor
  · nlinarith [sq_nonneg (s * |e| - 1)]
  · have h4 : e ^ 4 = (|e| ^ 2) ^ 2 := by rw [h2]; ring
    rw [h4, ← h2]
    nlinarith [mul_nonneg (sq_nonneg |e|) (sq_nonneg (s * |e| - 1))]

/-- **The small-ball estimate near a shifted centre** (Giles 2015, §9.2: the small-ball bound for
the exact conditional mean transferred to an approximate one).  As `integral_le_of_small_ball`,
with `F ≤ A` and `v² F ≤ B` a.e., but with the small-ball bound for a `u` within `δ` of `v`:
`ν{|u| ≤ t} ≤ c t` and `|u − v| ≤ δ` a.e.  Then `∫ F dν ≤ 2c √(A (2B + 2δ²A))`, since
`u² ≤ 2v² + 2δ²`. -/
lemma integral_le_of_small_ball_near {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {F u v : α → ℝ} {A B c δ : ℝ} (hFm : AEMeasurable F ν) (hF0 : ∀ᵐ z ∂ν, 0 ≤ F z)
    (hFA : ∀ᵐ z ∂ν, F z ≤ A) (hFB : ∀ᵐ z ∂ν, v z ^ 2 * F z ≤ B)
    (huv : ∀ᵐ z ∂ν, |u z - v z| ≤ δ) (hc : 0 ≤ c)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |u z| ≤ t} ≤ ENNReal.ofReal (c * t)) :
    ∫ z, F z ∂ν ≤ 2 * c * Real.sqrt (A * (2 * B + 2 * δ ^ 2 * A)) := by
  refine integral_le_of_small_ball hFm hF0 hFA ?_ hc hball
  filter_upwards [hF0, hFA, hFB, huv] with z h0 hA hB hd
  have h1 : (u z - v z) ^ 2 ≤ δ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have h2 : u z ^ 2 ≤ 2 * v z ^ 2 + 2 * δ ^ 2 := by nlinarith [sq_nonneg (u z - 2 * v z)]
  calc u z ^ 2 * F z ≤ (2 * v z ^ 2 + 2 * δ ^ 2) * F z := mul_le_mul_of_nonneg_right h2 h0
    _ = 2 * (v z ^ 2 * F z) + 2 * δ ^ 2 * F z := by ring
    _ ≤ 2 * B + 2 * δ ^ 2 * A := by gcongr

/-! ### The fibres: one outer sample -/

section Fiber

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒲] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

omit [MeasurableSpace 𝒲] in
/-- The inner mean of `g − a` is the inner mean of `g` minus `a` (`M ≥ 1`). -/
lemma innerMean_sub_const (g : 𝒵 → 𝒲 → ℝ) {M : ℕ} (hM : 0 < M) (a : ℝ) (z : 𝒵)
    (w : ℕ → 𝒲) : innerMean (fun z v => g z v - a) M z w = innerMean g M z w - a := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  simp only [innerMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hM', one_mul]

/-- **The moments of the inner sampling error, with centred conditional moments** (Giles 2015,
§9.1, p. 58: "By the Central Limit Theorem, `Δg₁⁽ⁿ⁾, Δg₂⁽ⁿ⁾ = O(M_ℓ^{−1/2})`").  Fix `z` with
`E_W[g(z, W)⁴] < ∞`, let `G = E_W[g(z, W)]`, `κ = E_W[(g(z, W) − G)⁴]` and `M ≥ 1`.  Then
`(A_M − A′_M)⁴` and `(A_M − G)⁴` are integrable, `M E[(A_M − A′_M)²] ≤ 2(1 + 16κ)`,
`M E[(A_M − G)²] ≤ 1 + 16κ`, `M² E[(A_M − G)⁴] ≤ 64κ` and `E[A_M − G] = 0`:
`fiber_nested_moments` and `fiber_centred_fourth_moment` applied to `g − G`, whose raw moments
are the centred moments of `g`. -/
lemma fiber_centred_moments (g : 𝒵 → 𝒲 → ℝ) (z : 𝒵) (hgz : Measurable (g z))
    (hgz4 : Integrable (fun v => g z v ^ 4) ρ) {M : ℕ} (hM : 0 < M) :
    Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 4)
        (innerLaw ρ) ∧
      (M : ℝ) * ∫ w, (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 2 ∂(innerLaw ρ) ≤
        2 * (1 + 16 * ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ) ∧
      Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 4) (innerLaw ρ) ∧
      (M : ℝ) * ∫ w, (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 2 ∂(innerLaw ρ) ≤
        1 + 16 * ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ ∧
      (M : ℝ) ^ 2 * ∫ w, (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 4 ∂(innerLaw ρ) ≤
        64 * ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ ∧
      ∫ w, (innerMean g M z w - ∫ v, g z v ∂ρ) ∂(innerLaw ρ) = 0 := by
  obtain ⟨G, hG⟩ : ∃ G, G = ∫ v, g z v ∂ρ := ⟨_, rfl⟩
  rw [← hG]
  obtain ⟨hc4, -, -, -⟩ := centred_moments_le (μ := ρ) hgz hgz4
  rw [← hG] at hc4
  have hgz1 : Integrable (g z) ρ := by
    simpa using integrable_pow_of_pow_four hgz hgz4 (k := 1) (by norm_num)
  set g' : 𝒵 → 𝒲 → ℝ := fun z v => g z v - G with hg'
  have hg'z : Measurable (g' z) := hgz.sub_const G
  have hg'4 : Integrable (fun v => g' z v ^ 4) ρ := hc4
  have hG0 : ∫ v, g' z v ∂ρ = 0 := by
    rw [hg', integral_sub hgz1 (integrable_const G), integral_const, probReal_univ, one_smul,
      ← hG, sub_self]
  have hmean : ∀ w, innerMean g' M z w = innerMean g M z w - G := fun w =>
    innerMean_sub_const g hM G z w
  obtain ⟨i4, h2, -, j4, k2, k0⟩ := fiber_nested_moments ρ g' z hg'z hg'4 hM
  obtain ⟨-, h4⟩ := fiber_centred_fourth_moment ρ g' z hg'z hg'4 hM
  simp only [hG0, sub_zero, hmean, sub_sub_sub_cancel_right] at i4 h2 j4 k2 k0 h4
  exact ⟨i4, h2, j4, k2, h4, k0⟩

/-- **The conditional bias at a kink** (Giles 2015, §9.2, p. 60, the analysis of Bujok et al.).
Let `f(x) = a₀ + a₁x + c max(x − k, 0)`, fix an outer sample `z` with `E_W[g(z, W)⁴] < ∞`, let
`G = E_W[g(z, W)]`, `κ = E_W[(g(z, W) − G)⁴]`, `M ≥ 1` and `s > 0` with `s² = M`.  Then the
conditional bias `b = E_W[f(A_M) − f(G)]` satisfies `s |b| ≤ |c| (1 + 80 κ)` and
`s³ (G − k)² |b| ≤ |c| (1 + 80 κ)`: `b = c E[h]` with `h` the remainder of
`kink_remainder_bounds` (the linear part has mean zero), `h ≤ |e|` and `(G − k)² h ≤ |e|³` with
`e = A_M − G`, and `M E[e²] ≤ 1 + 16 κ`, `M² E[e⁴] ≤ 64 κ` (`fiber_centred_moments`). -/
lemma fiber_kink_bias_le {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) (g : 𝒵 → 𝒲 → ℝ) (z : 𝒵)
    (hgz : Measurable (g z)) (hgz4 : Integrable (fun v => g z v ^ 4) ρ) {M : ℕ} (hM : 0 < M)
    {s : ℝ} (hs : 0 < s) (hsM : s ^ 2 = M) :
    s * |∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ)| ≤
        |c| * (1 + 80 * ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ) ∧
      s ^ 3 * ((∫ v, g z v ∂ρ - k) ^ 2 *
          |∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ)|) ≤
        |c| * (1 + 80 * ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ) := by
  obtain ⟨-, -, i4, h2, h4, h0⟩ := fiber_centred_moments ρ g z hgz hgz4 hM
  obtain ⟨G, hG⟩ : ∃ G, G = ∫ v, g z v ∂ρ := ⟨_, rfl⟩
  rw [← hG] at i4 h2 h4 h0 ⊢
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ v, (g z v - G) ^ 4 ∂ρ := ⟨_, rfl⟩
  rw [← hm] at h2 h4 ⊢
  have hm0 : 0 ≤ m := by rw [hm]; exact integral_nonneg fun v => by positivity
  set σ : ℝ := if 0 < G - k then 1 else 0
  -- the inner sampling error and the kink remainder
  have hem : Measurable fun w : ℕ → 𝒲 => innerMean g M z w - G :=
    (measurable_innerMean_right hgz M).sub_const G
  have ie1 : Integrable (fun w : ℕ → 𝒲 => innerMean g M z w - G) (innerLaw ρ) := by
    simpa using integrable_pow_of_pow_four hem i4 (k := 1) (by norm_num)
  have ie2 : Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - G) ^ 2) (innerLaw ρ) :=
    integrable_pow_of_pow_four hem i4 (by norm_num)
  set h : (ℕ → 𝒲) → ℝ := fun w =>
    max (G - k + (innerMean g M z w - G)) 0 - max (G - k) 0 - σ * (innerMean g M z w - G)
    with hh
  have hb : ∀ w, 0 ≤ h w ∧ h w ≤ |innerMean g M z w - G| ∧
      (G - k) ^ 2 * h w ≤ |innerMean g M z w - G| ^ 3 := fun w =>
    kink_remainder_bounds (G - k) (innerMean g M z w - G)
  have hhm : Measurable h := by
    rw [hh]
    exact (((hem.const_add (G - k)).max measurable_const).sub_const _).sub (hem.const_mul σ)
  have ih : Integrable h (innerLaw ρ) :=
    ie1.abs.mono' hhm.aestronglyMeasurable (Eventually.of_forall fun w => by
      rw [Real.norm_of_nonneg (hb w).1]
      exact (hb w).2.1)
  have hpt : ∀ w, f (innerMean g M z w) - f G =
      (a₁ + c * σ) * (innerMean g M z w - G) + c * h w := fun w => by
    rw [hh]
    simp only
    rw [show G - k + (innerMean g M z w - G) = innerMean g M z w - k by ring, hf, hf]
    ring
  have hI : ∫ w, (f (innerMean g M z w) - f G) ∂(innerLaw ρ) = c * ∫ w, h w ∂(innerLaw ρ) := by
    simp only [hpt]
    rw [integral_add (ie1.const_mul _) (ih.const_mul c), integral_const_mul, integral_const_mul,
      h0, mul_zero, zero_add]
  have hI0 : 0 ≤ ∫ w, h w ∂(innerLaw ρ) := integral_nonneg fun w => (hb w).1
  rw [hI, abs_mul, abs_of_nonneg hI0]
  -- the two moment bounds
  have hMr : (M : ℝ) = s ^ 2 := hsM.symm
  have i1 : Integrable (fun w => (s ^ 2 * (innerMean g M z w - G) ^ 2 + 1) / 2) (innerLaw ρ) :=
    ((ie2.const_mul _).add (integrable_const _)).div_const 2
  have i2 : Integrable (fun w => ((innerMean g M z w - G) ^ 2 +
      s ^ 2 * (innerMean g M z w - G) ^ 4) / 2) (innerLaw ρ) :=
    (ie2.add (i4.const_mul _)).div_const 2
  have hB1 : s * ∫ w, h w ∂(innerLaw ρ) ≤ 1 + 8 * m := by
    rw [← integral_const_mul]
    have := integral_mono (ih.const_mul s) i1 fun w => by
      have := (two_mul_abs_le_and_cube s (innerMean g M z w - G)).1
      have := (hb w).2.1
      show s * h w ≤ (s ^ 2 * (innerMean g M z w - G) ^ 2 + 1) / 2
      nlinarith
    refine this.trans ?_
    rw [integral_div, integral_add (ie2.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul, ← hMr]
    linarith
  have hB2 : s ^ 3 * ((G - k) ^ 2 * ∫ w, h w ∂(innerLaw ρ)) ≤ (1 + 80 * m) / 2 := by
    have hX : s * ((G - k) ^ 2 * ∫ w, h w ∂(innerLaw ρ)) ≤
        (∫ w, (innerMean g M z w - G) ^ 2 ∂(innerLaw ρ) +
          s ^ 2 * ∫ w, (innerMean g M z w - G) ^ 4 ∂(innerLaw ρ)) / 2 := by
      rw [← integral_const_mul, ← integral_const_mul]
      have := integral_mono ((ih.const_mul _).const_mul s) i2 fun w => by
        have := (two_mul_abs_le_and_cube s (innerMean g M z w - G)).2
        have := (hb w).2.2
        show s * ((G - k) ^ 2 * h w) ≤ ((innerMean g M z w - G) ^ 2 +
          s ^ 2 * (innerMean g M z w - G) ^ 4) / 2
        nlinarith
      refine this.trans ?_
      rw [integral_div, integral_add ie2 (i4.const_mul _), integral_const_mul]
    have e3 : s ^ 3 * ((G - k) ^ 2 * ∫ w, h w ∂(innerLaw ρ)) =
        s ^ 2 * (s * ((G - k) ^ 2 * ∫ w, h w ∂(innerLaw ρ))) := by ring
    rw [e3]
    calc s ^ 2 * (s * ((G - k) ^ 2 * ∫ w, h w ∂(innerLaw ρ)))
        ≤ s ^ 2 * ((∫ w, (innerMean g M z w - G) ^ 2 ∂(innerLaw ρ) +
          s ^ 2 * ∫ w, (innerMean g M z w - G) ^ 4 ∂(innerLaw ρ)) / 2) := by gcongr
      _ = ((M : ℝ) * ∫ w, (innerMean g M z w - G) ^ 2 ∂(innerLaw ρ) +
          (M : ℝ) ^ 2 * ∫ w, (innerMean g M z w - G) ^ 4 ∂(innerLaw ρ)) / 2 := by
          rw [hMr]; ring
      _ ≤ (1 + 80 * m) / 2 := by linarith
  constructor
  · calc s * (|c| * ∫ w, h w ∂(innerLaw ρ)) = |c| * (s * ∫ w, h w ∂(innerLaw ρ)) := by ring
      _ ≤ |c| * (1 + 80 * m) := by gcongr; linarith
  · calc s ^ 3 * ((G - k) ^ 2 * (|c| * ∫ w, h w ∂(innerLaw ρ)))
        = |c| * (s ^ 3 * ((G - k) ^ 2 * ∫ w, h w ∂(innerLaw ρ))) := by ring
      _ ≤ |c| * (1 + 80 * m) := by gcongr; linarith

/-- **The inner sampling error of a Lipschitz `f` is `O(1)` in `L¹`, for one outer sample**
(Giles 2015, §9.1).  Let `f(x) = a₀ + a₁x + c max(x − k, 0)`, fix `z` with `E_W[g(z, W)⁴] < ∞`,
`G = E_W[g(z, W)]`, `κ = E_W[(g(z, W) − G)⁴]` and `M ≥ 1`.  Then `|f(A_M) − f(G)|` is integrable
and `E_W|f(A_M) − f(G)| ≤ (|a₁| + |c|)(1 + 8κ)`, since `|e| ≤ (1 + e²)/2` and
`E[(A_M − G)²] ≤ 1 + 16κ` (`fiber_centred_moments`).  This makes the bias integrand integrable
without any moment of the conditional mean `G` itself. -/
lemma fiber_kink_abs_le {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) (g : 𝒵 → 𝒲 → ℝ) (z : 𝒵)
    (hgz : Measurable (g z)) (hgz4 : Integrable (fun v => g z v ^ 4) ρ) {M : ℕ} (hM : 0 < M) :
    Integrable (fun w => |f (innerMean g M z w) - f (∫ v, g z v ∂ρ)|) (innerLaw ρ) ∧
      ∫ w, |f (innerMean g M z w) - f (∫ v, g z v ∂ρ)| ∂(innerLaw ρ) ≤
        (|a₁| + |c|) * (1 + 8 * ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ) := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  obtain ⟨-, -, i4, h2, -, -⟩ := fiber_centred_moments ρ g z hgz hgz4 hM
  obtain ⟨G, hG⟩ : ∃ G, G = ∫ v, g z v ∂ρ := ⟨_, rfl⟩
  rw [← hG] at i4 h2 ⊢
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ v, (g z v - G) ^ 4 ∂ρ := ⟨_, rfl⟩
  rw [← hm] at h2 ⊢
  have hM1 : (1 : ℝ) ≤ M := Nat.one_le_cast.2 hM
  have hA : Measurable fun w : ℕ → 𝒲 => innerMean g M z w := measurable_innerMean_right hgz M
  have ie2 : Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - G) ^ 2) (innerLaw ρ) :=
    integrable_pow_of_pow_four (hA.sub_const G) i4 (by norm_num)
  have hL : 0 ≤ |a₁| + |c| := by positivity
  have hpt : ∀ w, |f (innerMean g M z w) - f G| ≤
      (|a₁| + |c|) * ((1 + (innerMean g M z w - G) ^ 2) / 2) := fun w => by
    refine (abs_kink_sub_le hf _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
    nlinarith [sq_nonneg (|innerMean g M z w - G| - 1), sq_abs (innerMean g M z w - G)]
  have hdom : Integrable (fun w => (|a₁| + |c|) * ((1 + (innerMean g M z w - G) ^ 2) / 2))
      (innerLaw ρ) := (((integrable_const 1).add ie2).div_const 2).const_mul _
  have hint : Integrable (fun w => |f (innerMean g M z w) - f G|) (innerLaw ρ) :=
    hdom.mono' (continuous_abs.measurable.comp ((hfm.comp hA).sub_const _)).aestronglyMeasurable
      (Eventually.of_forall fun w => by rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hpt w)
  refine ⟨hint, (integral_mono hint hdom hpt).trans ?_⟩
  rw [integral_const_mul, integral_div, integral_add (integrable_const 1) ie2, integral_const,
    probReal_univ, one_smul]
  have h2' : ∫ w, (innerMean g M z w - G) ^ 2 ∂(innerLaw ρ) ≤ 1 + 16 * m := by
    have h0 : 0 ≤ ∫ w, (innerMean g M z w - G) ^ 2 ∂(innerLaw ρ) :=
      integral_nonneg fun w => sq_nonneg _
    nlinarith
  gcongr
  linarith

/-- **The antithetic correction at a kink, for one outer sample** (Giles 2015, §9.1, p. 58: "the
function `f` was piecewise linear, not twice differentiable, and so the rate of variance
convergence was slightly lower, with `β = 1.5`"; the fibre bounds of
`nested_kink_variance_rate`, with centred moments).  Let `f(x) = a₀ + a₁x + c max(x − k, 0)`, fix
`z` with `E_W[g(z, W)⁴] < ∞`, let `G = E_W[g(z, W)]` and `κ = E_W[(g(z, W) − G)⁴]`.  The
correction `Y_{ℓ+1}` (`2^ℓ` coarse inner samples) satisfies `E_W[Y²] ≤ c² (1 + 16 κ)/(8 · 2^ℓ)`
and `(G − k)² E_W[Y²] ≤ 64 c² κ/4^ℓ` (`sq_antithetic_kink_le`, `fiber_centred_moments`). -/
lemma fiber_kink_antithetic_le {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) (g : 𝒵 → 𝒲 → ℝ) (z : 𝒵)
    (hgz : Measurable (g z)) (hgz4 : Integrable (fun v => g z v ^ 4) ρ) (ℓ : ℕ) :
    Integrable (fun w => nestedDelta f g (ℓ + 1) (z, w) ^ 2) (innerLaw ρ) ∧
      ∫ w, nestedDelta f g (ℓ + 1) (z, w) ^ 2 ∂(innerLaw ρ) ≤
        c ^ 2 * (1 + 16 * ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ) / (8 * 2 ^ ℓ) ∧
      (∫ v, g z v ∂ρ - k) ^ 2 * ∫ w, nestedDelta f g (ℓ + 1) (z, w) ^ 2 ∂(innerLaw ρ) ≤
        64 * c ^ 2 * (∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ) / ((2 : ℝ) ^ ℓ) ^ 2 := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  set M : ℕ := 2 ^ ℓ with hMdef
  have hM : 0 < M := by positivity
  have hMr : (M : ℝ) = (2 : ℝ) ^ ℓ := by rw [hMdef]; push_cast; ring
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.2 hM
  rw [← hMr]
  obtain ⟨i4, h2, j4, -, h4, -⟩ := fiber_centred_moments ρ g z hgz hgz4 hM
  set G := ∫ v, g z v ∂ρ
  set m := ∫ v, (g z v - G) ^ 4 ∂ρ
  have hA : Measurable fun w : ℕ → 𝒲 => innerMean g M z w := measurable_innerMean_right hgz M
  have hA' : Measurable fun w : ℕ → 𝒲 => innerMean g M z (shiftSeq M w) :=
    hA.comp (measurable_shiftSeq M)
  have hsh : MeasurePreserving (shiftSeq (𝒲 := 𝒲) M) (innerLaw ρ) (innerLaw ρ) :=
    measurePreserving_shiftSeq ρ M
  have hYeq : ∀ w : ℕ → 𝒲, nestedDelta f g (ℓ + 1) (z, w) =
      f ((innerMean g M z w + innerMean g M z (shiftSeq M w)) / 2) -
        f (innerMean g M z w) / 2 - f (innerMean g M z (shiftSeq M w)) / 2 :=
    fun w => nestedDelta_succ_eq f g ℓ (z, w)
  have hYz : Measurable fun w => nestedDelta f g (ℓ + 1) (z, w) := by
    simp only [hYeq]
    exact ((hfm.comp ((hA.add hA').div_const 2)).sub ((hfm.comp hA).div_const 2)).sub
      ((hfm.comp hA').div_const 2)
  have hD2 : Integrable (fun w => (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 2)
      (innerLaw ρ) := integrable_pow_of_pow_four (hA.sub hA') i4 (by norm_num)
  have j4' : Integrable (fun w => (innerMean g M z (shiftSeq M w) - G) ^ 4) (innerLaw ρ) :=
    hsh.integrable_comp_of_integrable j4
  have e4' : ∫ w, (innerMean g M z (shiftSeq M w) - G) ^ 4 ∂(innerLaw ρ) =
      ∫ w, (innerMean g M z w - G) ^ 4 ∂(innerLaw ρ) :=
    integral_comp_of_measurePreserving hsh j4.aestronglyMeasurable
  have hP1 : ∀ w, nestedDelta f g (ℓ + 1) (z, w) ^ 2 ≤ c ^ 2 / 16 *
      (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 2 := fun w => by
    rw [hYeq]
    exact (sq_antithetic_kink_le hf G _ _).1
  have hP2 : ∀ w, (G - k) ^ 2 * nestedDelta f g (ℓ + 1) (z, w) ^ 2 ≤ c ^ 2 / 2 *
      ((innerMean g M z w - G) ^ 4 + (innerMean g M z (shiftSeq M w) - G) ^ 4) := fun w => by
    rw [hYeq]
    exact (sq_antithetic_kink_le hf G _ _).2
  have hY2 : Integrable (fun w => nestedDelta f g (ℓ + 1) (z, w) ^ 2) (innerLaw ρ) :=
    (hD2.const_mul (c ^ 2 / 16)).mono' (hYz.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hP1 w)
  refine ⟨hY2, ?_, ?_⟩
  · calc ∫ w, nestedDelta f g (ℓ + 1) (z, w) ^ 2 ∂(innerLaw ρ)
        ≤ ∫ w, c ^ 2 / 16 * (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 2
            ∂(innerLaw ρ) := integral_mono hY2 (hD2.const_mul _) hP1
      _ = c ^ 2 / 16 * ∫ w, (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 2
            ∂(innerLaw ρ) := integral_const_mul _ _
      _ ≤ c ^ 2 / 16 * (2 * (1 + 16 * m) / M) := by
          gcongr
          rw [le_div_iff₀ hM0, mul_comm]
          linarith
      _ = c ^ 2 * (1 + 16 * m) / (8 * M) := by field_simp; ring
  · have i2 : Integrable (fun w => c ^ 2 / 2 *
        ((innerMean g M z w - G) ^ 4 + (innerMean g M z (shiftSeq M w) - G) ^ 4))
        (innerLaw ρ) := (j4.add j4').const_mul _
    calc (G - k) ^ 2 * ∫ w, nestedDelta f g (ℓ + 1) (z, w) ^ 2 ∂(innerLaw ρ)
        = ∫ w, (G - k) ^ 2 * nestedDelta f g (ℓ + 1) (z, w) ^ 2 ∂(innerLaw ρ) :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ w, c ^ 2 / 2 *
            ((innerMean g M z w - G) ^ 4 + (innerMean g M z (shiftSeq M w) - G) ^ 4)
            ∂(innerLaw ρ) := integral_mono (hY2.const_mul _) i2 hP2
      _ = c ^ 2 * ∫ w, (innerMean g M z w - G) ^ 4 ∂(innerLaw ρ) := by
          rw [integral_const_mul, integral_add j4 j4', e4']
          ring
      _ ≤ c ^ 2 * (64 * m / M ^ 2) := by
          gcongr
          rw [le_div_iff₀ (by positivity), mul_comm]
          linarith
      _ = 64 * c ^ 2 * m / M ^ 2 := by ring

/-- **The second moment of the inner mean, for one outer sample**: fix `z` with
`E_W[h(z, W)⁴] < ∞` and `M ≥ 1`.  Then `E_W[A_M(h)²] = E_W[h(z, W)]² + Var_W[h(z, W)]/M ≤
E_W[h(z, W)]² + E_W[h(z, W)²]/M`: the mean of `M` independent samples keeps the square of the
mean and divides the variance by `M` (`fiber_sum_moments`). -/
lemma fiber_innerMean_sq_le (h : 𝒵 → 𝒲 → ℝ) (z : 𝒵) (hhz : Measurable (h z))
    (hhz4 : Integrable (fun v => h z v ^ 4) ρ) {M : ℕ} (hM : 0 < M) :
    Integrable (fun w => innerMean h M z w ^ 2) (innerLaw ρ) ∧
      ∫ w, innerMean h M z w ^ 2 ∂(innerLaw ρ) ≤
        (∫ v, h z v ∂ρ) ^ 2 + (∫ v, h z v ^ 2 ∂ρ) / M := by
  obtain ⟨j4, j1, f2, -⟩ := fiber_sum_moments ρ hhz hhz4 (nestedSign M) (nestedSign_sq M) M
  have hσ : ∫ v, (h z v - ∫ u, h z u ∂ρ) ^ 2 ∂ρ ≤ ∫ v, h z v ^ 2 ∂ρ := by
    have := variance_le_expectation_sq (μ := ρ) hhz.aestronglyMeasurable
    rw [variance_eq_integral hhz.aemeasurable] at this
    simpa only [Pi.pow_apply] using this
  obtain ⟨G, hG⟩ : ∃ G, G = ∫ v, h z v ∂ρ := ⟨_, rfl⟩
  rw [← hG] at j4 j1 f2 hσ ⊢
  have hSm : Measurable fun w : ℕ → 𝒲 => ∑ m ∈ range M, nestedSign M m * (h z (w m) - G) :=
    Finset.measurable_sum _ fun m _ =>
      ((hhz.comp (measurable_pi_apply m)).sub_const G).const_mul _
  have hS2 : Integrable (fun w : ℕ → 𝒲 => (∑ m ∈ range M, nestedSign M m * (h z (w m) - G)) ^ 2)
      (innerLaw ρ) := integrable_pow_of_pow_four hSm j4 (by norm_num)
  have hS1 : Integrable (fun w : ℕ → 𝒲 => ∑ m ∈ range M, nestedSign M m * (h z (w m) - G))
      (innerLaw ρ) := by
    simpa using integrable_pow_of_pow_four hSm j4 (k := 1) (by norm_num)
  have e : ∀ w, innerMean h M z w ^ 2 = G ^ 2 +
      2 * G * (M : ℝ)⁻¹ * ∑ m ∈ range M, nestedSign M m * (h z (w m) - G) +
      (M : ℝ)⁻¹ ^ 2 * (∑ m ∈ range M, nestedSign M m * (h z (w m) - G)) ^ 2 := fun w => by
    have := centred_sum_eq h hM z w G
    rw [show innerMean h M z w = G + (innerMean h M z w - G) by ring, this]
    ring
  have i1 : Integrable (fun w : ℕ → 𝒲 => G ^ 2 +
      2 * G * (M : ℝ)⁻¹ * ∑ m ∈ range M, nestedSign M m * (h z (w m) - G)) (innerLaw ρ) :=
    (integrable_const _).add (hS1.const_mul _)
  have i2 : Integrable (fun w : ℕ → 𝒲 => (M : ℝ)⁻¹ ^ 2 *
      (∑ m ∈ range M, nestedSign M m * (h z (w m) - G)) ^ 2) (innerLaw ρ) := hS2.const_mul _
  refine ⟨(i1.add i2).congr (Eventually.of_forall fun w => (e w).symm), ?_⟩
  simp only [e]
  rw [integral_add i1 i2, integral_add (integrable_const _) (hS1.const_mul _), integral_const_mul,
    integral_const_mul, j1, f2, integral_const, probReal_univ, one_smul, mul_zero, add_zero]
  have e2 : (M : ℝ)⁻¹ ^ 2 * (M * ∫ v, (h z v - G) ^ 2 ∂ρ) = (∫ v, (h z v - G) ^ 2 ∂ρ) / M := by
    field_simp
  rw [e2]
  gcongr

end Fiber

/-! ### The rates on `𝒵 × 𝒲^ℕ`, with the small ball near a shifted centre -/

section Product

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **A fibre bound gives joint integrability on `𝒵 × 𝒲`** (Giles 2015, §9.1: the moments
conditional on the outer sample are averaged over it; Fubini–Tonelli, as
`integrable_pow_four_of_fiber`): a measurable `F ≥ 0` on `𝒵 × 𝒲` whose fibre integrals
`E_W[F(z, W)]` are `ν`-a.e. finite and at most `B` is `ν ⊗ ρ`-integrable. -/
lemma integrable_prod_of_fiber_bound {F : 𝒵 × 𝒲 → ℝ} (hFm : Measurable F) (hF0 : ∀ p, 0 ≤ F p)
    {B : ℝ} (hfib : ∀ᵐ z ∂ν, Integrable (fun v => F (z, v)) ρ ∧ ∫ v, F (z, v) ∂ρ ≤ B) :
    Integrable F (ν.prod ρ) := by
  refine (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨hfib.mono fun z hz => hz.1, ?_⟩
  refine (integrable_const B).mono'
    (hFm.norm.stronglyMeasurable.integral_prod_right' (ν := ρ)).aestronglyMeasurable
    (hfib.mono fun z hz => ?_)
  have e : ∫ v, ‖F (z, v)‖ ∂ρ = ∫ v, F (z, v) ∂ρ :=
    integral_congr_ae (Eventually.of_forall fun v => Real.norm_of_nonneg (hF0 _))
  rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _), e]
  exact hz.2

omit [IsProbabilityMeasure ν] in
/-- **The exact conditional mean is a.e. measurable** (Giles 2015, §9.2: the inner quantity is
known only through its approximations `g_ℓ`).  If the conditional means `E_W[g_ℓ(z, W)]` of
measurable approximations satisfy `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w` for every `ℓ` and
`ν`-a.e. `z`, then `z ↦ E_W[g(z, W)]` is `ν`-a.e. measurable, as an a.e. limit of measurable
functions; no measurability of the exact `g` is needed. -/
lemma aemeasurable_condMean_of_weak {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {g : 𝒵 → 𝒲 → ℝ} {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w) :
    AEMeasurable (fun z => ∫ v, g z v ∂ρ) ν := by
  refine aemeasurable_of_tendsto_metrizable_ae atTop (f := fun ℓ z => ∫ v, gh ℓ z v ∂ρ)
    (fun ℓ => ((hgh ℓ).stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable.aemeasurable)
    ?_
  filter_upwards [ae_all_iff.2 hw] with z hz
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul c_w
  rw [mul_zero] at ht
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun ℓ => dist_nonneg) (fun ℓ => ?_) ht
  rw [Real.dist_eq, one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact hz ℓ

/-- **The kink bias is `O(2^{−ℓ})`, with a shifted small ball** (Giles 2015, §9.2, p. 60).  Let
`f(x) = a₀ + a₁x + c max(x − k, 0)`, let the centred conditional fourth moments be bounded,
`E_W[(g(z, W) − E_W[g(z, W)])⁴] ≤ m₄` for `ν`-a.e. `z`, and let `u` be within `δ` of
`E_W[g(z, W)] − k` with `ν{|u| ≤ t} ≤ c_d t` for all `t > 0`.  If `R ≥ 0` and
`2 (1 + 2^ℓ δ²) ≤ R²`, then `P_ℓ − f(E_W[g(Z, W)])` is integrable (`fiber_kink_abs_le`) and
`2^ℓ |E[P_ℓ − f(E_W[g(Z, W)])]| ≤ 2 c_d |c| (1 + 80 m₄) R` (`fiber_kink_bias_le`,
`integral_le_of_small_ball_near`). -/
lemma kink_bias_le_of_small_ball {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g)) {m₄ : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧
      ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {u : 𝒵 → ℝ} {δ c_d R : ℝ} (hδ : ∀ᵐ z ∂ν, |u z - (∫ v, g z v ∂ρ - k)| ≤ δ)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |u z| ≤ t} ≤ ENNReal.ofReal (c_d * t)) (ℓ : ℕ)
    (hR : 0 ≤ R) (hR2 : 2 * (1 + 2 ^ ℓ * δ ^ 2) ≤ R ^ 2) :
    Integrable (fun p => nestedP f g ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedP f g ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
        2 * c_d * |c| * (1 + 80 * m₄) * R := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  obtain ⟨z₀, hz₀⟩ := hfib.exists
  have hm₄ : 0 ≤ m₄ := le_trans (integral_nonneg fun v => by positivity) hz₀.2
  have hcd : 0 ≤ c_d := nonneg_of_small_ball hball
  set M : ℕ := 2 ^ ℓ with hMdef
  have hM : 0 < M := by positivity
  have hMr : (M : ℝ) = (2 : ℝ) ^ ℓ := by rw [hMdef]; push_cast; ring
  set s : ℝ := Real.sqrt M
  have hs0 : 0 < s := Real.sqrt_pos.2 (Nat.cast_pos.2 hM)
  have hsM : s ^ 2 = M := Real.sq_sqrt (Nat.cast_nonneg M)
  -- integrability of `P_ℓ − f(E_W[g])`, fibre by fibre, and Fubini
  have hGm : Measurable fun z => ∫ v, g z v ∂ρ :=
    (hg.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  have hA : Measurable fun p : 𝒵 × (ℕ → 𝒲) => innerMean g M p.1 p.2 :=
    measurable_innerMean hg M measurable_id
  have hDm : Measurable fun p : 𝒵 × (ℕ → 𝒲) => nestedP f g ℓ p - nestedTarget f g ρ p :=
    (hfm.comp hA).sub (hfm.comp (hGm.comp measurable_fst))
  obtain ⟨hDabs, -⟩ := integrable_of_fiber_bound ν ρ
    (F := fun p => ‖nestedP f g ℓ p - nestedTarget f g ρ p‖) hDm.norm (fun p => norm_nonneg _)
    (integrable_const ((|a₁| + |c|) * (1 + 8 * m₄)))
    (hfib.mono fun z hz => by
      obtain ⟨i, b⟩ := fiber_kink_abs_le ρ hf g z hg.of_uncurry_left hz.1 hM
      refine ⟨i, b.trans ?_⟩
      gcongr
      exact hz.2)
  have hD : Integrable (fun p => nestedP f g ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) :=
    (integrable_norm_iff hDm.aestronglyMeasurable).1 hDabs
  have e : ∫ p, (nestedP f g ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ z, ∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ) ∂ν :=
    integral_prod _ hD
  refine ⟨hD, ?_⟩
  -- the fibre bounds
  set F : 𝒵 → ℝ := fun z =>
    |∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ)|
  have hFm : AEMeasurable F ν := by
    have hm : Measurable fun p : 𝒵 × (ℕ → 𝒲) =>
        f (innerMean g M p.1 p.2) - f (∫ v, g p.1 v ∂ρ) :=
      (hfm.comp hA).sub (hfm.comp (hGm.comp measurable_fst))
    exact (continuous_abs.measurable.comp
      (hm.stronglyMeasurable.integral_prod_right' (ν := innerLaw ρ)).measurable).aemeasurable
  set K : ℝ := |c| * (1 + 80 * m₄) with hK
  have hfibF : ∀ᵐ z ∂ν, F z ≤ K / s ∧ (∫ v, g z v ∂ρ - k) ^ 2 * F z ≤ K / s ^ 3 := by
    filter_upwards [hfib] with z ⟨hz4, hzm⟩
    obtain ⟨b1, b2⟩ := fiber_kink_bias_le ρ hf g z hg.of_uncurry_left hz4 hM hs0 hsM
    have hKz : |c| * (1 + 80 * ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ) ≤ K := by rw [hK]; gcongr
    constructor
    · rw [le_div_iff₀ hs0, mul_comm]
      exact b1.trans hKz
    · rw [le_div_iff₀ (by positivity), mul_comm]
      exact b2.trans hKz
  have key := integral_le_of_small_ball_near (v := fun z => ∫ v, g z v ∂ρ - k) hFm
    (Eventually.of_forall fun z => abs_nonneg _) (hfibF.mono fun z hz => hz.1)
    (hfibF.mono fun z hz => hz.2) hδ hcd hball
  -- the constant: `√(A (2B + 2δ²A)) ≤ K R/s²`
  have hsq : Real.sqrt (K / s * (2 * (K / s ^ 3) + 2 * δ ^ 2 * (K / s))) ≤ K * R / s ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have e1 : K / s * (2 * (K / s ^ 3) + 2 * δ ^ 2 * (K / s)) =
        K ^ 2 * (2 * (1 + s ^ 2 * δ ^ 2)) / s ^ 4 := by
      field_simp
    have e2 : (K * R / s ^ 2) ^ 2 = K ^ 2 * R ^ 2 / s ^ 4 := by ring
    rw [e1, e2, hsM, hMr]
    gcongr
  have hint : |∫ z, ∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ) ∂ν| ≤
      ∫ z, F z ∂ν := abs_integral_le_integral_abs
  rw [e, ← hMr, ← hsM]
  calc s ^ 2 * |∫ z, ∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ) ∂ν|
      ≤ s ^ 2 * (2 * c_d * (K * R / s ^ 2)) := by
        gcongr
        exact hint.trans (key.trans (by gcongr))
    _ = 2 * c_d * |c| * (1 + 80 * m₄) * R := by
        rw [hK]
        field_simp

/-- **The kink variance is `O(2^{−3ℓ/2})`, with a shifted small ball** (Giles 2015, §9.1, p. 58 and
§9.2, p. 60: "`β = 1.5`").  Let `f(x) = a₀ + a₁x + c max(x − k, 0)`, let the centred conditional
fourth moments be bounded, `E_W[(g(z, W) − E_W[g(z, W)])⁴] ≤ m₄` for `ν`-a.e. `z`, and let `u` be
within `δ` of `E_W[g(z, W)] − k` with `ν{|u| ≤ t} ≤ c_d t` for all `t > 0`.  If `R ≥ 0` and
`1 + 2^ℓ δ²/32 ≤ R²`, then the §9.1 correction `Y_{ℓ+1}` (`2^ℓ` coarse inner samples) is
square-integrable and `2^{3ℓ/2} E[Y_{ℓ+1}²] ≤ 2 c_d c² (1 + 16 m₄) R`
(`fiber_kink_antithetic_le`, `integral_le_of_small_ball_near`). -/
lemma kink_variance_le_of_small_ball {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g)) {m₄ : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧
      ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {u : 𝒵 → ℝ} {δ c_d R : ℝ} (hδ : ∀ᵐ z ∂ν, |u z - (∫ v, g z v ∂ρ - k)| ≤ δ)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |u z| ≤ t} ≤ ENNReal.ofReal (c_d * t)) (ℓ : ℕ)
    (hR : 0 ≤ R) (hR2 : 1 + 2 ^ ℓ * δ ^ 2 / 32 ≤ R ^ 2) :
    MemLp (nestedDelta f g (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        2 * c_d * c ^ 2 * (1 + 16 * m₄) * R := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  obtain ⟨z₀, hz₀⟩ := hfib.exists
  have hm₄ : 0 ≤ m₄ := le_trans (integral_nonneg fun v => by positivity) hz₀.2
  have hcd : 0 ≤ c_d := nonneg_of_small_ball hball
  set q : ℝ := (2 : ℝ) ^ ℓ with hq
  set Y := nestedDelta f g (ℓ + 1)
  have hYm : Measurable Y := measurable_nestedDelta hfm hg (ℓ + 1)
  set A : ℝ := c ^ 2 * (1 + 16 * m₄) / (8 * q) with hA
  set B : ℝ := 64 * c ^ 2 * m₄ / q ^ 2 with hB
  -- the fibre bounds, for almost every outer sample
  have hfibY : ∀ᵐ z ∂ν, Integrable (fun w => Y (z, w) ^ 2) (innerLaw ρ) ∧
      ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ) ≤ A ∧
      (∫ v, g z v ∂ρ - k) ^ 2 * ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ) ≤ B := by
    filter_upwards [hfib] with z ⟨hz4, hzm⟩
    obtain ⟨i, h1, h2⟩ := fiber_kink_antithetic_le ρ hf g z hg.of_uncurry_left hz4 ℓ
    refine ⟨i, h1.trans ?_, h2.trans ?_⟩
    · rw [hA]
      gcongr
    · rw [hB]
      gcongr
  -- integrability on the product and Fubini
  obtain ⟨hY2int, -⟩ := integrable_of_fiber_bound ν ρ (F := fun p => Y p ^ 2)
    (hYm.pow_const 2) (fun p => sq_nonneg _) (integrable_const A)
    (hfibY.mono fun z hz => ⟨hz.1, hz.2.1⟩)
  have hMemLp : MemLp Y 2 (nestedLaw ν ρ) :=
    (memLp_two_iff_integrable_sq hYm.aestronglyMeasurable).2 hY2int
  refine ⟨hMemLp, ?_⟩
  have hFub : ∫ p, Y p ^ 2 ∂(nestedLaw ν ρ) = ∫ z, ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ) ∂ν :=
    integral_prod _ hY2int
  have hFm : AEMeasurable (fun z => ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ)) ν :=
    ((hYm.pow_const 2).stronglyMeasurable.integral_prod_right' (ν := innerLaw ρ)).measurable
      |>.aemeasurable
  have key := integral_le_of_small_ball_near (v := fun z => ∫ v, g z v ∂ρ - k) hFm
    (Eventually.of_forall fun z => integral_nonneg fun w => sq_nonneg _)
    (hfibY.mono fun z hz => hz.2.1) (hfibY.mono fun z hz => hz.2.2) hδ hcd hball
  rw [hFub]
  -- the constant: `2^{3ℓ/2} √(A (2B + 2δ²A)) ≤ c² (1 + 16 m₄) R`
  set r : ℝ := (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) with hr
  have hr0 : 0 < r := by positivity
  have hr2 : r ^ 2 = q ^ 3 := by
    rw [hr, hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have hsq : Real.sqrt (A * (2 * B + 2 * δ ^ 2 * A)) ≤ c ^ 2 * (1 + 16 * m₄) * R / r := by
    rw [Real.sqrt_le_left (by positivity)]
    have e1 : A * (2 * B + 2 * δ ^ 2 * A) = (c ^ 2) ^ 2 * (1 + 16 * m₄) *
        (16 * m₄ + q * δ ^ 2 * (1 + 16 * m₄) / 32) / q ^ 3 := by
      rw [hA, hB]
      field_simp
      ring
    have e2 : (c ^ 2 * (1 + 16 * m₄) * R / r) ^ 2 =
        (c ^ 2) ^ 2 * (1 + 16 * m₄) * ((1 + 16 * m₄) * R ^ 2) / q ^ 3 := by
      rw [div_pow, hr2]
      ring
    rw [e1, e2]
    gcongr
    have h16 : 0 ≤ 1 + 16 * m₄ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hR2 h16, sq_nonneg δ]
  calc r * ∫ z, ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ) ∂ν
      ≤ r * (2 * c_d * (c ^ 2 * (1 + 16 * m₄) * R / r)) := by
        gcongr
        exact key.trans (by gcongr)
    _ = 2 * c_d * c ^ 2 * (1 + 16 * m₄) * R := by field_simp

/-- **Jensen's inequality for the square of the inner mean** (Giles 2015, §9.1–§9.2: the inner
means `A_M = M⁻¹ ∑_{m<M} h(Z, W⁽ᵐ⁾)` of the level approximations): `A_M² ≤ M⁻¹ ∑ h(Z, W⁽ᵐ⁾)²` and
each `(Z, W⁽ᵐ⁾)` has the law of `(Z, W)`, so `E[A_M²] ≤ E[h(Z, W)²]` (`M ≥ 1`).  Used for the
square-integrability of the level-`0` approximation in `nested_kink_sde_mlmc_complexity`. -/
lemma integral_innerMean_sq_le {h : 𝒵 → 𝒲 → ℝ} (hh : Measurable (Function.uncurry h))
    (hh2 : Integrable (fun p : 𝒵 × 𝒲 => h p.1 p.2 ^ 2) (ν.prod ρ)) {M : ℕ} (hM : 0 < M) :
    Integrable (fun p : 𝒵 × (ℕ → 𝒲) => innerMean h M p.1 p.2 ^ 2) (nestedLaw ν ρ) ∧
      ∫ p, innerMean h M p.1 p.2 ^ 2 ∂(nestedLaw ν ρ) ≤ ∫ p, h p.1 p.2 ^ 2 ∂(ν.prod ρ) := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hev : ∀ m, MeasurePreserving (Function.eval m) (innerLaw ρ) ρ := fun m =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => ρ) m
  have hcoord : ∀ m, MeasurePreserving (fun p : 𝒵 × (ℕ → 𝒲) => (p.1, p.2 m)) (nestedLaw ν ρ)
      (ν.prod ρ) := fun m => (MeasurePreserving.id ν).prod (hev m)
  have hgm : ∀ m, Integrable (fun p : 𝒵 × (ℕ → 𝒲) => h p.1 (p.2 m) ^ 2) (nestedLaw ν ρ) :=
    fun m => (hcoord m).integrable_comp_of_integrable hh2
  have hgi : ∀ m, ∫ p, h p.1 (p.2 m) ^ 2 ∂(nestedLaw ν ρ) = ∫ p, h p.1 p.2 ^ 2 ∂(ν.prod ρ) :=
    fun m => integral_comp_of_measurePreserving (hcoord m) hh2.aestronglyMeasurable
  have hJ : ∀ x : ℕ → ℝ, ((M : ℝ)⁻¹ * ∑ m ∈ range M, x m) ^ 2 ≤
      (M : ℝ)⁻¹ * ∑ m ∈ range M, x m ^ 2 := fun x => by
    have h := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) (by decide)).map_sum_le (t := range M)
      (w := fun _ => (M : ℝ)⁻¹) (p := x) (fun _ _ => inv_nonneg.2 (Nat.cast_nonneg M))
      (by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_inv_cancel₀ hM')
      (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul, ← Finset.mul_sum] at h
    exact h
  have hdom : Integrable (fun p : 𝒵 × (ℕ → 𝒲) => (M : ℝ)⁻¹ * ∑ m ∈ range M, h p.1 (p.2 m) ^ 2)
      (nestedLaw ν ρ) :=
    (integrable_finsetSum (range M) fun m _ => hgm m).const_mul _
  have hint : Integrable (fun p : 𝒵 × (ℕ → 𝒲) => innerMean h M p.1 p.2 ^ 2) (nestedLaw ν ρ) :=
    hdom.mono' ((measurable_innerMean hh M measurable_id).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        show ‖innerMean h M p.1 p.2 ^ 2‖ ≤ (M : ℝ)⁻¹ * ∑ m ∈ range M, h p.1 (p.2 m) ^ 2
        rw [Real.norm_of_nonneg (by positivity)]
        exact hJ fun m => h p.1 (p.2 m))
  refine ⟨hint, ?_⟩
  calc ∫ p, innerMean h M p.1 p.2 ^ 2 ∂(nestedLaw ν ρ)
      ≤ ∫ p, (M : ℝ)⁻¹ * ∑ m ∈ range M, h p.1 (p.2 m) ^ 2 ∂(nestedLaw ν ρ) :=
        integral_mono hint hdom fun p => hJ fun m => h p.1 (p.2 m)
    _ = ∫ p, h p.1 p.2 ^ 2 ∂(ν.prod ρ) := by
        rw [integral_const_mul, integral_finsetSum _ fun m _ => hgm m]
        simp only [hgi, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

end Product

/-! ### `α = 1` for exact inner samples -/

section Exact

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **`α = 1` for a piecewise linear `f`** (Giles 2015, §9.2, p. 60: "Following the analysis in
(Bujok et al. 2013), if the function `f` is continuous and piecewise differentiable, rather than
being twice differentiable, then in the MLMC treatment we would get `β = 1.5`, and hence an overall
complexity which is `O(ε^{−2.5})`", which is Theorem 1 with `α = 1`; §9.1, p. 58, for exact inner
samples: "the function `f` was piecewise linear").  Let `f(x) = a₀ + a₁x + c max(x − k, 0)`, let
the centred conditional fourth moments be bounded, `E_W[(g(z, W) − E_W[g(z, W)])⁴] ≤ m₄` for
`ν`-a.e. `z`, and let the conditional mean put little mass near the kink,
`ν{|E_W[g(Z, W)] − k| ≤ t} ≤ c_d t` for all `t > 0`.  Then for the level-`ℓ` approximation
`P_ℓ = f(A_{2^ℓ})` the bias integrand `P_ℓ − f(E_W[g(Z, W)])` is integrable and
`2^ℓ |E[P_ℓ − f(E_W[g(Z, W)])]| ≤ 3 c_d |c| (1 + 80 m₄)`, i.e. `α = 1`, improving
`nested_kink_bias_rate` (`α = ½`, which needs no small ball).  Proof: the linear part of `f` has
no bias, and for one outer sample, with `X = E_W[g(z, W)] − k`, the conditional bias `b` satisfies
`|b| = O(M^{−1/2})` and `X² |b| = O(M^{−3/2})` (`fiber_kink_bias_le`: the kink contributes only
when the inner sampling error exceeds `|X|`); the small ball turns these into `O(M⁻¹)`
(`integral_le_of_small_ball`).  Hypotheses: the paper states none for this case; the small-ball
bound and the bounded conditional fourth moments are this formalisation's.  The moments are
centred, so the conditional mean may be unbounded (e.g. `g(Z, W) = Z + W` with a Gaussian `Z`),
and no moment of `E_W[g(Z, W)]` is needed, since `f` is Lipschitz (`fiber_kink_abs_le`).
Deviation: the paper's `f` is continuous and piecewise differentiable; here `f` is piecewise
linear with one kink, as in `nested_kink_variance_rate`; several kinks or curved pieces are not
covered (several kinks would follow by summing the hinge terms, given a small-ball bound at each
kink). -/
theorem nested_kink_bias_rate_one {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g)) {m₄ c_d : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧
      ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (ℓ : ℕ) :
    Integrable (fun p => nestedP f g ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedP f g ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
        3 * c_d * |c| * (1 + 80 * m₄) := by
  obtain ⟨hD, h⟩ := kink_bias_le_of_small_ball ν ρ hf hg hfib
    (u := fun z => ∫ v, g z v ∂ρ - k) (δ := 0) (Eventually.of_forall fun z => by simp) hball ℓ
    (R := 3 / 2) (by norm_num) (by norm_num)
  exact ⟨hD, by linarith⟩

end Exact

/-! ### §9.2: `α = 1` and `β = 3/2` with discretised inner paths -/

section Discretised

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **`α = 1` for a piecewise linear `f` with `2^ℓ` timesteps** (Giles 2015, §9.2, p. 60: "if the
function `f` is continuous and piecewise differentiable, rather than being twice differentiable,
then in the MLMC treatment we would get `β = 1.5`, and hence an overall complexity which is
`O(ε^{−2.5})`", which is Theorem 1 with `α = 1`, `β = 1.5`, `γ = 2`).  Level `ℓ` uses `2^ℓ` inner
samples of the level-`ℓ` approximation `g_ℓ` of the inner quantity `g` (`nestedSdeP`), and
`f(x) = a₀ + a₁x + c max(x − k, 0)`.  Hypotheses (this formalisation's; the paper states none for
this case, and the weak order of the time discretisation is not formalised): the centred
conditional fourth moments of `g_ℓ` are bounded uniformly in `ℓ` and the outer sample,
`E_W[(g_ℓ(z, W) − E_W[g_ℓ(z, W)])⁴] ≤ m₄`; first order weak convergence uniformly in the outer
sample, `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w` (as in `nested_sde_bias_rate`); and the
small-ball bound `ν{|E_W[g(Z, W)] − k| ≤ t} ≤ c_d t` for the exact conditional mean only.  Then
`P_ℓ − f(E_W[g(Z, W)])` is integrable and
`2^ℓ |E[P_ℓ − f(E_W[g(Z, W)])]| ≤ 4 c_d |c| (1 + 80 m₄)(1 + c_w) + (|a₁| + |c|) c_w`.
Proof: the inner sampling error of `g_ℓ` is handled as in `nested_kink_bias_rate_one`, with the
small ball for `E_W[g_ℓ(Z, W)]` replaced by that for `E_W[g(Z, W)]`, which lies within
`c_w 2^{−ℓ}` of it (`kink_bias_le_of_small_ball`); the discretisation error is at most
`(|a₁| + |c|) c_w 2^{−ℓ}` because `f` is Lipschitz.  The exact `g` enters only through its
conditional mean `E_W[g(z, W)]`, the a.e. limit of the `E_W[g_ℓ(z, W)]` by the weak-error
hypothesis (`aemeasurable_condMean_of_weak`), so no measurability or moment of `g` is assumed.
The moments are centred, so the conditional mean may be unbounded (e.g. a Gaussian or log-normal
outer state).  Deviation: the paper's `f` is continuous and piecewise differentiable; here `f` is
piecewise linear with one kink, as in `nested_kink_variance_rate`; several kinks or curved pieces
are not covered (several kinks would follow by summing the hinge terms, given a small-ball bound
at each kink). -/
theorem nested_kink_sde_bias_rate {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w c_d : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (ℓ : ℕ) :
    Integrable (fun p => nestedSdeP f gh ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
        4 * c_d * |c| * (1 + 80 * m₄) * (1 + c_w) + (|a₁| + |c|) * c_w := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  have h2l0 : (0 : ℝ) < 2 ^ ℓ := by positivity
  have h2l : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
  have hcw : 0 ≤ c_w := by
    obtain ⟨z, hz⟩ := (hw ℓ).exists
    exact le_trans (by positivity) hz
  -- the weak error, `|E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w 2^{−ℓ}`
  have hwl : ∀ᵐ z ∂ν, |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w / 2 ^ ℓ :=
    (hw ℓ).mono fun z hz => by
      rw [le_div_iff₀ h2l0, mul_comm]
      exact hz
  -- the inner sampling error of `g_ℓ`
  have hR2 : 2 * (1 + 2 ^ ℓ * (c_w / 2 ^ ℓ) ^ 2) ≤ (2 * (1 + c_w)) ^ 2 := by
    have e : (2 : ℝ) ^ ℓ * (c_w / 2 ^ ℓ) ^ 2 = c_w ^ 2 / 2 ^ ℓ := by
      field_simp
    have h1 : c_w ^ 2 / 2 ^ ℓ ≤ c_w ^ 2 := div_le_self (sq_nonneg _) h2l
    rw [e]
    nlinarith
  obtain ⟨i1, hb1⟩ := kink_bias_le_of_small_ball ν ρ hf (hgh ℓ) (hfib ℓ)
    (u := fun z => ∫ v, g z v ∂ρ - k) (δ := c_w / 2 ^ ℓ)
    (hwl.mono fun z hz => by
      rw [show ∫ v, g z v ∂ρ - k - (∫ v, gh ℓ z v ∂ρ - k) =
        -(∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ) by ring, abs_neg]
      exact hz) hball ℓ (R := 2 * (1 + c_w)) (by positivity) hR2
  -- the discretisation error
  have hGlm : Measurable fun z => ∫ v, gh ℓ z v ∂ρ :=
    ((hgh ℓ).stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  have hGm : AEMeasurable (fun z => ∫ v, g z v ∂ρ) ν := aemeasurable_condMean_of_weak ν ρ hgh hw
  have hpt : ∀ᵐ z ∂ν, |f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)| ≤
      (|a₁| + |c|) * (c_w / 2 ^ ℓ) :=
    hwl.mono fun z hz => (abs_kink_sub_le hf _ _).trans (by gcongr)
  have hD : Integrable (fun z => f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ν :=
    (integrable_const ((|a₁| + |c|) * (c_w / 2 ^ ℓ))).mono'
      ((hfm.comp hGlm).aemeasurable.sub (hfm.comp_aemeasurable hGm)).aestronglyMeasurable
      (hpt.mono fun z hz => by rw [Real.norm_eq_abs]; exact hz)
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have i2 : Integrable (fun p => nestedTarget f (gh ℓ) ρ p - nestedTarget f g ρ p)
      (nestedLaw ν ρ) :=
    hfst.integrable_comp_of_integrable hD
  have hint : Integrable (fun p => nestedSdeP f gh ℓ p - nestedTarget f g ρ p)
      (nestedLaw ν ρ) :=
    (i1.add i2).congr (Eventually.of_forall fun p => by
      simp only [Pi.add_apply, nestedSdeP, nestedP]
      ring)
  refine ⟨hint, ?_⟩
  -- split into the inner sampling error and the discretisation error
  have e1 : ∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p) ∂(nestedLaw ν ρ) +
        ∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν := by
    have e2 : ∫ p, (nestedTarget f (gh ℓ) ρ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
        ∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν :=
      integral_comp_of_measurePreserving hfst hD.aestronglyMeasurable
    rw [← e2, ← integral_add i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun p => by
      simp only [nestedSdeP, nestedP]
      ring)
  have hb2 : (2 : ℝ) ^ ℓ * |∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν| ≤
      (|a₁| + |c|) * c_w := by
    have h := integral_mono_ae hD.abs (integrable_const ((|a₁| + |c|) * (c_w / 2 ^ ℓ))) hpt
    rw [integral_const, probReal_univ, one_smul] at h
    calc (2 : ℝ) ^ ℓ * |∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν|
        ≤ (2 : ℝ) ^ ℓ * ((|a₁| + |c|) * (c_w / 2 ^ ℓ)) :=
          mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs.trans h) h2l0.le
      _ = (|a₁| + |c|) * c_w := by field_simp
  rw [e1]
  calc (2 : ℝ) ^ ℓ * |∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p) ∂(nestedLaw ν ρ) +
        ∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν|
      ≤ (2 : ℝ) ^ ℓ * |∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p)
          ∂(nestedLaw ν ρ)| +
        (2 : ℝ) ^ ℓ * |∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν| := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) h2l0.le
    _ ≤ 2 * c_d * |c| * (1 + 80 * m₄) * (2 * (1 + c_w)) + (|a₁| + |c|) * c_w :=
        add_le_add hb1 hb2
    _ = 4 * c_d * |c| * (1 + 80 * m₄) * (1 + c_w) + (|a₁| + |c|) * c_w := by ring

/-- `(x − y + w)² ≤ (3/2)(1 + x⁴) + (3/2)(1 + y⁴) + 3w²`: `(x − y + w)² ≤ 3(x² + y² + w²)` and
`x² ≤ (1 + x⁴)/2` (bounding the second moment of a level difference by centred fourth moments). -/
lemma sq_sub_add_le (x y w : ℝ) :
    (x - y + w) ^ 2 ≤ 3 / 2 * (1 + x ^ 4) + 3 / 2 * (1 + y ^ 4) + 3 * w ^ 2 := by
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - w), sq_nonneg (y + w), sq_nonneg (x ^ 2 - 1),
    sq_nonneg (y ^ 2 - 1)]

/-- **The level difference of the inner means is `O(2^{−3ℓ/4})` in `L²`** (Giles 2015, §9.2: the
inner means of `g_{ℓ+1}` and `g_ℓ` over the same `2^ℓ` inner samples).  Let `H = g_{ℓ+1} − g_ℓ`,
let the centred conditional fourth moments of every `g_j` be at most `m₄`, the weak errors
`2^j |E_W[g_j(z, W)] − E_W[g(z, W)]| ≤ c_w` and the strong errors
`2^{j/2} E[(g_{j+1}(Z, W) − g_j(Z, W))²] ≤ cₛ`.  Then the inner mean `A_{2^ℓ}(H)` is
square-integrable and `2^{3ℓ/2} E[A_{2^ℓ}(H)²] ≤ (9/4) c_w² + cₛ`: for one outer sample
`E_W[A(H)²] ≤ E_W[H]² + E_W[H²]/2^ℓ` (`fiber_innerMean_sq_le`) with `|E_W[H]| ≤ (3/2) c_w 2^{−ℓ}`
by the weak order, and `E_W[H²]` is bounded, so `H²` is integrable
(`integrable_prod_of_fiber_bound`).  Averaging over the inner samples divides the variance of
`H` by `2^ℓ`, so the strong order `¼` in `L²` is enough. -/
lemma integral_innerMean_levelDiff_sq_le {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w cₛ : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ cₛ) (ℓ : ℕ) :
    Integrable (fun p : 𝒵 × (ℕ → 𝒲) =>
        innerMean (fun z v => gh (ℓ + 1) z v - gh ℓ z v) (2 ^ ℓ) p.1 p.2 ^ 2) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, innerMean (fun z v => gh (ℓ + 1) z v - gh ℓ z v)
        (2 ^ ℓ) p.1 p.2 ^ 2 ∂(nestedLaw ν ρ) ≤ 9 / 4 * c_w ^ 2 + cₛ := by
  set M : ℕ := 2 ^ ℓ with hMdef
  have hM : 0 < M := by positivity
  set r : ℝ := (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) with hr
  -- the level difference `H = g_{ℓ+1} − g_ℓ`, fibre by fibre: a fourth moment, the mean
  -- `|E_W[H]| ≤ d = (3/2) c_w 2^{−ℓ}` (weak order) and a bounded second moment
  set q : ℝ := (2 : ℝ) ^ ℓ with hq
  have hq0 : 0 < q := by positivity
  have hMq : (M : ℝ) = q := by rw [hMdef, hq]; push_cast; ring
  set d : ℝ := 3 / 2 * c_w / q with hd
  set H : 𝒵 → 𝒲 → ℝ := fun z v => gh (ℓ + 1) z v - gh ℓ z v
  have hHm : Measurable (Function.uncurry H) := (hgh (ℓ + 1)).sub (hgh ℓ)
  have hfibH : ∀ᵐ z ∂ν, Integrable (fun v => H z v ^ 4) ρ ∧ |∫ v, H z v ∂ρ| ≤ d ∧
      ∫ v, H z v ^ 2 ∂ρ ≤ 3 * (1 + m₄) + 3 * d ^ 2 := by
    filter_upwards [hfib ℓ, hfib (ℓ + 1), hw ℓ, hw (ℓ + 1)] with z h0 h1 w0 w1
    have ha : Measurable (gh (ℓ + 1) z) := (hgh (ℓ + 1)).of_uncurry_left
    have hb : Measurable (gh ℓ z) := (hgh ℓ).of_uncurry_left
    obtain ⟨ca4, -, -, -⟩ := centred_moments_le (μ := ρ) ha h1.1
    obtain ⟨cb4, -, -, -⟩ := centred_moments_le (μ := ρ) hb h0.1
    have ia : Integrable (gh (ℓ + 1) z) ρ := by
      simpa using integrable_pow_of_pow_four ha h1.1 (k := 1) (by norm_num)
    have ib : Integrable (gh ℓ z) ρ := by
      simpa using integrable_pow_of_pow_four hb h0.1 (k := 1) (by norm_num)
    set A := ∫ v, gh (ℓ + 1) z v ∂ρ
    set B := ∫ v, gh ℓ z v ∂ρ
    set G := ∫ v, g z v ∂ρ
    have hH4 : Integrable (fun v => H z v ^ 4) ρ :=
      ((h1.1.add h0.1).const_mul 8).mono' ((ha.sub hb).pow_const 4).aestronglyMeasurable
        (Eventually.of_forall fun v => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact sub_pow_four_le _ _)
    have hmean : ∫ v, H z v ∂ρ = A - B := integral_sub ia ib
    have hAB : |A - B| ≤ d := by
      have e1 : |A - G| ≤ c_w / (2 * q) := by
        have e : (2 : ℝ) ^ (ℓ + 1) = 2 * q := by rw [pow_succ', hq]
        rw [e] at w1
        rw [le_div_iff₀ (by positivity), mul_comm]
        exact w1
      have e2 : |B - G| ≤ c_w / q := by
        rw [le_div_iff₀ hq0, mul_comm]
        exact w0
      have e3 : |A - B| ≤ |A - G| + |B - G| := by
        rw [show A - B = (A - G) - (B - G) by ring]
        exact abs_sub _ _
      have e4 : c_w / (2 * q) + c_w / q = d := by
        rw [hd]
        field_simp
        ring
      linarith
    refine ⟨hH4, hmean ▸ hAB, ?_⟩
    -- `H = (g_{ℓ+1} − A) − (g_ℓ − B) + (A − B)` and `x² ≤ (1 + x⁴)/2`
    have hpt : ∀ v, H z v ^ 2 ≤ 3 / 2 * (1 + (gh (ℓ + 1) z v - A) ^ 4) +
        3 / 2 * (1 + (gh ℓ z v - B) ^ 4) + 3 * (A - B) ^ 2 := fun v => by
      have e : H z v = (gh (ℓ + 1) z v - A) - (gh ℓ z v - B) + (A - B) := by
        simp only [H]
        ring
      rw [e]
      exact sq_sub_add_le _ _ _
    have j1 : Integrable (fun v => 3 / 2 * (1 + (gh (ℓ + 1) z v - A) ^ 4)) ρ :=
      ((integrable_const 1).add ca4).const_mul _
    have j2 : Integrable (fun v => 3 / 2 * (1 + (gh ℓ z v - B) ^ 4)) ρ :=
      ((integrable_const 1).add cb4).const_mul _
    have j12 : Integrable (fun v => 3 / 2 * (1 + (gh (ℓ + 1) z v - A) ^ 4) +
        3 / 2 * (1 + (gh ℓ z v - B) ^ 4)) ρ := j1.add j2
    have jall : Integrable (fun v => 3 / 2 * (1 + (gh (ℓ + 1) z v - A) ^ 4) +
        3 / 2 * (1 + (gh ℓ z v - B) ^ 4) + 3 * (A - B) ^ 2) ρ := j12.add (integrable_const _)
    have hH2 : Integrable (fun v => H z v ^ 2) ρ :=
      integrable_pow_of_pow_four (ha.sub hb) hH4 (by norm_num)
    have := integral_mono hH2 jall hpt
    rw [integral_add j12 (integrable_const _), integral_add j1 j2, integral_const_mul,
      integral_const_mul, integral_add (integrable_const 1) ca4,
      integral_add (integrable_const 1) cb4] at this
    simp only [integral_const, probReal_univ, one_smul] at this
    have hd2 : (A - B) ^ 2 ≤ d ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hAB 2
    linarith [h0.2, h1.2]
  have hH2 : Integrable (fun p : 𝒵 × 𝒲 => H p.1 p.2 ^ 2) (ν.prod ρ) :=
    integrable_prod_of_fiber_bound ν ρ (F := fun p => H p.1 p.2 ^ 2) (hHm.pow_const 2)
      (fun p => sq_nonneg _) (hfibH.mono fun z hz =>
        ⟨integrable_pow_of_pow_four hHm.of_uncurry_left hz.1 (by norm_num), hz.2.2⟩)
  -- `E[(A − B)²] ≤ d² + E[H²]/2^ℓ`
  have hB : Integrable (fun z => d ^ 2 + (∫ v, H z v ^ 2 ∂ρ) / M) ν :=
    (integrable_const _).add (hH2.integral_prod_left.div_const _)
  obtain ⟨hI2, hIle⟩ := integrable_of_fiber_bound ν ρ
    (F := fun p => innerMean H M p.1 p.2 ^ 2)
    ((measurable_innerMean hHm M measurable_id).pow_const 2) (fun p => sq_nonneg _) hB
    (hfibH.mono fun z hz => by
      obtain ⟨i, b⟩ := fiber_innerMean_sq_le ρ H z hHm.of_uncurry_left hz.1 hM
      refine ⟨i, b.trans ?_⟩
      have : (∫ v, H z v ∂ρ) ^ 2 ≤ d ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hz.2.1 2
      linarith)
  have hFubH : ∫ z, ∫ v, H z v ^ 2 ∂ρ ∂ν = ∫ p, H p.1 p.2 ^ 2 ∂(ν.prod ρ) :=
    (integral_prod _ hH2).symm
  rw [integral_add (integrable_const _) (hH2.integral_prod_left.div_const _), integral_const,
    probReal_univ, one_smul, integral_div, hFubH, hMq] at hIle
  refine ⟨hI2, ?_⟩
  -- `σ = 2^{ℓ/2}`, `r = σ³`, `q = σ²`
  set σ : ℝ := (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) with hσ
  have hσ1 : 1 ≤ σ := Real.one_le_rpow (by norm_num) (by positivity)
  have hrσ : r = σ ^ 3 := by
    rw [hr, hσ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have hqσ : q = σ ^ 2 := by
    rw [hq, hσ, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have e1 : r * d ^ 2 = 9 / 4 * c_w ^ 2 / σ := by
    rw [hrσ, hd, hqσ]
    field_simp
    ring
  have e2 : r * ((∫ p, H p.1 p.2 ^ 2 ∂(ν.prod ρ)) / q) = σ * ∫ p, H p.1 p.2 ^ 2 ∂(ν.prod ρ) := by
    rw [hrσ, hqσ]
    field_simp
  have h2 : 9 / 4 * c_w ^ 2 / σ ≤ 9 / 4 * c_w ^ 2 := div_le_self (by positivity) hσ1
  have h3 : σ * ∫ p, H p.1 p.2 ^ 2 ∂(ν.prod ρ) ≤ cₛ := hs ℓ
  calc r * ∫ p, innerMean H M p.1 p.2 ^ 2 ∂(nestedLaw ν ρ)
      ≤ r * (d ^ 2 + (∫ p, H p.1 p.2 ^ 2 ∂(ν.prod ρ)) / q) := by gcongr
    _ = r * d ^ 2 + r * ((∫ p, H p.1 p.2 ^ 2 ∂(ν.prod ρ)) / q) := by ring
    _ ≤ 9 / 4 * c_w ^ 2 + cₛ := by
        rw [e1, e2]
        exact add_le_add h2 h3

/-- **`β = 3/2` for a piecewise linear `f` with `2^ℓ` timesteps** (Giles 2015, §9.2, p. 60: "if
the function `f` is continuous and piecewise differentiable, rather than being twice
differentiable, then in the MLMC treatment we would get `β = 1.5`").  Level `ℓ` uses `2^ℓ` inner
samples of the level-`ℓ` approximation `g_ℓ` (`nestedSdeDelta`: the fine value with `g_{ℓ+1}`, the
two coarse values with `g_ℓ`, on the same inner samples), and `f(x) = a₀ + a₁x + c max(x − k, 0)`.
Hypotheses (this formalisation's; the paper states none for this case, and the orders of the time
discretisation are not formalised): centred conditional fourth moments
`E_W[(g_ℓ(z, W) − E_W[g_ℓ(z, W)])⁴] ≤ m₄` uniformly in `ℓ` and `z`; first order weak convergence
uniformly in `z`, `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w`; the small-ball bound
`ν{|E_W[g(Z, W)] − k| ≤ t} ≤ c_d t` for the exact conditional mean only; and strong convergence of
order `¼` in `L²`, `2^{ℓ/2} E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))²] ≤ cₛ` (integrated over `Z` and `W`;
the other hypotheses make `(g_{ℓ+1} − g_ℓ)²` integrable), which the strong order `½` of the
Euler–Maruyama scheme (`2^ℓ E[(g_{ℓ+1} − g_ℓ)²] ≤ cₛ`) already implies, not only the first order
of the Milstein scheme.  Then `Y_{ℓ+1}` is square-integrable and
`2^{3ℓ/2} E[Y_{ℓ+1}²] ≤ 6 c_d c² (1 + 16 m₄)(1 + c_w) + (3/2)(|a₁| + |c|)² ((9/4) c_w² + cₛ)`,
i.e. `V_ℓ = O(2^{−3ℓ/2})`.  Proof: `Y_{ℓ+1}` is the §9.1 correction of `g_{ℓ+1}`, `O(2^{−3ℓ/4})`
in `L²` by the kink argument of `nested_kink_variance_rate` with the small ball for
`E_W[g_{ℓ+1}(Z, W)]` replaced by that for `E_W[g(Z, W)]` (`kink_variance_le_of_small_ball`), plus
`½(f(A) − f(B)) + ½(f(A′) − f(B′))` with `|f(A) − f(B)| ≤ (|a₁| + |c|) |A − B|` and `A − B` the
inner mean of `H = g_{ℓ+1} − g_ℓ` (`nestedSdeDelta_succ_eq`).  For one outer sample
`E_W[(A − B)²] ≤ E_W[H]² + E_W[H²]/2^ℓ` (`fiber_innerMean_sq_le`): the weak order gives
`|E_W[H]| ≤ (3/2) c_w 2^{−ℓ}`, and averaging `2^ℓ` inner samples divides the variance by `2^ℓ`,
which is why order `¼` suffices.  Deviation: the paper's `f` is continuous and piecewise
differentiable; here `f` is piecewise linear with one kink, as in `nested_kink_variance_rate`;
several kinks or curved pieces are not covered (several kinks would follow by summing the hinge
terms, given a small-ball bound at each kink). -/
theorem nested_kink_sde_variance_rate {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w c_d cₛ : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ cₛ) (ℓ : ℕ) :
    MemLp (nestedSdeDelta f gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        6 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w) +
          3 / 2 * (|a₁| + |c|) ^ 2 * (9 / 4 * c_w ^ 2 + cₛ) := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  have h2l : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
  have hcw : 0 ≤ c_w := by
    obtain ⟨z, hz⟩ := (hw (ℓ + 1)).exists
    exact le_trans (by positivity) hz
  obtain ⟨hI2, hIle⟩ := integral_innerMean_levelDiff_sq_le ν ρ hgh hfib hw hs ℓ
  set M : ℕ := 2 ^ ℓ
  set r : ℝ := (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ)
  have hr0 : 0 < r := by positivity
  set L : ℝ := |a₁| + |c| with hL
  -- the kink term: the §9.1 correction of `g_{ℓ+1}`
  have h2l1 : (0 : ℝ) < 2 ^ (ℓ + 1) := by positivity
  have hδ : ∀ᵐ z ∂ν, |∫ v, g z v ∂ρ - k - (∫ v, gh (ℓ + 1) z v ∂ρ - k)| ≤
      c_w / 2 ^ (ℓ + 1) :=
    (hw (ℓ + 1)).mono fun z hz => by
      rw [show ∫ v, g z v ∂ρ - k - (∫ v, gh (ℓ + 1) z v ∂ρ - k) =
        -(∫ v, gh (ℓ + 1) z v ∂ρ - ∫ v, g z v ∂ρ) by ring, abs_neg, le_div_iff₀ h2l1, mul_comm]
      exact hz
  have hR2 : 1 + 2 ^ ℓ * (c_w / 2 ^ (ℓ + 1)) ^ 2 / 32 ≤ (1 + c_w) ^ 2 := by
    have e : (2 : ℝ) ^ ℓ * (c_w / 2 ^ (ℓ + 1)) ^ 2 = c_w ^ 2 / (4 * 2 ^ ℓ) := by
      rw [pow_succ]
      field_simp
      ring
    have h1 : c_w ^ 2 / (4 * 2 ^ ℓ) ≤ c_w ^ 2 := div_le_self (sq_nonneg _) (by linarith)
    rw [e]
    nlinarith
  obtain ⟨hN2, hNle⟩ := kink_variance_le_of_small_ball ν ρ hf (hgh (ℓ + 1)) (hfib (ℓ + 1))
    (u := fun z => ∫ v, g z v ∂ρ - k) hδ hball ℓ (R := 1 + c_w) (by positivity) hR2
  -- the Lipschitz term: `U = f(A) − f(B)`, `A − B` the inner mean of `H = g_{ℓ+1} − g_ℓ`
  set H : 𝒵 → 𝒲 → ℝ := fun z v => gh (ℓ + 1) z v - gh ℓ z v
  set A : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => innerMean (gh (ℓ + 1)) M p.1 p.2
  set B : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => innerMean (gh ℓ) M p.1 p.2
  set φ : 𝒵 × (ℕ → 𝒲) → 𝒵 × (ℕ → 𝒲) := fun p => (p.1, shiftSeq M p.2)
  have hφ : MeasurePreserving φ (nestedLaw ν ρ) (nestedLaw ν ρ) :=
    (MeasurePreserving.id ν).prod (measurePreserving_shiftSeq ρ M)
  set U : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => f (A p) - f (B p)
  have hUm : Measurable U :=
    (hfm.comp (measurable_innerMean (hgh (ℓ + 1)) M measurable_id)).sub
      (hfm.comp (measurable_innerMean (hgh ℓ) M measurable_id))
  have hUpt : ∀ p, U p ^ 2 ≤ L ^ 2 * innerMean H M p.1 p.2 ^ 2 := fun p => by
    have h1 := abs_kink_sub_le hf (A p) (B p)
    have e : A p - B p = innerMean H M p.1 p.2 := innerMean_sub _ _ M p.1 p.2
    rw [e] at h1
    calc U p ^ 2 = |U p| ^ 2 := (sq_abs _).symm
      _ ≤ (L * |innerMean H M p.1 p.2|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = L ^ 2 * innerMean H M p.1 p.2 ^ 2 := by rw [mul_pow, sq_abs]
  have hU2i : Integrable (fun p => U p ^ 2) (nestedLaw ν ρ) :=
    (hI2.const_mul (L ^ 2)).mono' (hUm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hUpt p)
  have hU2 : MemLp U 2 (nestedLaw ν ρ) :=
    (memLp_two_iff_integrable_sq hUm.aestronglyMeasurable).2 hU2i
  have hUφ : MemLp (fun p => U (φ p)) 2 (nestedLaw ν ρ) := hU2.comp_measurePreserving hφ
  have hUle : r * ∫ p, U p ^ 2 ∂(nestedLaw ν ρ) ≤ L ^ 2 * (9 / 4 * c_w ^ 2 + cₛ) :=
    calc r * ∫ p, U p ^ 2 ∂(nestedLaw ν ρ)
        ≤ r * ∫ p, L ^ 2 * innerMean H M p.1 p.2 ^ 2 ∂(nestedLaw ν ρ) :=
          mul_le_mul_of_nonneg_left (integral_mono hU2i (hI2.const_mul _) hUpt) hr0.le
      _ = L ^ 2 * (r * ∫ p, innerMean H M p.1 p.2 ^ 2 ∂(nestedLaw ν ρ)) := by
          rw [integral_const_mul]
          ring
      _ ≤ L ^ 2 * (9 / 4 * c_w ^ 2 + cₛ) := by gcongr
  have hUφle : ∫ p, U (φ p) ^ 2 ∂(nestedLaw ν ρ) = ∫ p, U p ^ 2 ∂(nestedLaw ν ρ) :=
    integral_comp_of_measurePreserving hφ hU2i.aestronglyMeasurable
  -- the decomposition `Y = N + U/2 + U ∘ φ/2`
  have hdec : ∀ p, nestedSdeDelta f gh (ℓ + 1) p =
      nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p + U p / 2 + U (φ p) / 2 := fun p =>
    nestedSdeDelta_succ_eq f gh ℓ p
  have hY2 : MemLp (nestedSdeDelta f gh (ℓ + 1)) 2 (nestedLaw ν ρ) := by
    have e : nestedSdeDelta f gh (ℓ + 1) = fun p =>
        nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p + 2⁻¹ * U p + 2⁻¹ * U (φ p) := by
      funext p
      rw [hdec p]
      ring
    rw [e]
    exact (hN2.add (hU2.const_mul 2⁻¹)).add (hUφ.const_mul 2⁻¹)
  refine ⟨hY2, ?_⟩
  have hYpt : ∀ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ≤
      3 * nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 + 3 / 4 * U p ^ 2 + 3 / 4 * U (φ p) ^ 2 :=
    fun p => by
      rw [hdec p]
      nlinarith [sq_nonneg (nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p - U p / 2),
        sq_nonneg (nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p - U (φ p) / 2),
        sq_nonneg (U p / 2 - U (φ p) / 2)]
  have j1 : Integrable (fun p => 3 * nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2) (nestedLaw ν ρ) :=
    hN2.integrable_sq.const_mul 3
  have j2 : Integrable (fun p => 3 / 4 * U p ^ 2) (nestedLaw ν ρ) := hU2i.const_mul _
  have j3 : Integrable (fun p => 3 / 4 * U (φ p) ^ 2) (nestedLaw ν ρ) :=
    hUφ.integrable_sq.const_mul _
  have j12 : Integrable (fun p => 3 * nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 + 3 / 4 * U p ^ 2)
      (nestedLaw ν ρ) := j1.add j2
  have j123 : Integrable (fun p => 3 * nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 +
      3 / 4 * U p ^ 2 + 3 / 4 * U (φ p) ^ 2) (nestedLaw ν ρ) := j12.add j3
  have hY2le := integral_mono hY2.integrable_sq j123 hYpt
  rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
    integral_const_mul, hUφle] at hY2le
  calc r * ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)
      ≤ r * (3 * ∫ p, nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) +
          3 / 4 * ∫ p, U p ^ 2 ∂(nestedLaw ν ρ) + 3 / 4 * ∫ p, U p ^ 2 ∂(nestedLaw ν ρ)) :=
        mul_le_mul_of_nonneg_left hY2le hr0.le
    _ = 3 * (r * ∫ p, nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)) +
          3 / 2 * (r * ∫ p, U p ^ 2 ∂(nestedLaw ν ρ)) := by ring
    _ ≤ 3 * (2 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w)) +
          3 / 2 * (L ^ 2 * (9 / 4 * c_w ^ 2 + cₛ)) := by
        gcongr
    _ = 6 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w) +
          3 / 2 * (|a₁| + |c|) ^ 2 * (9 / 4 * c_w ^ 2 + cₛ) := by
        rw [hL]
        ring

/-- **MLMC for nested simulation with a piecewise linear `f` and `2^ℓ` timesteps has complexity
`O(ε^{−2.5})`** (Giles 2015, §9.2, p. 60: "Following the analysis in (Bujok et al. 2013), if the
function `f` is continuous and piecewise differentiable, rather than being twice differentiable,
then in the MLMC treatment we would get `β = 1.5`, and hence an overall complexity which is
`O(ε^{−2.5})`").  Let `f(x) = a₀ + a₁x + c max(x − k, 0)` and let level `ℓ` use `2^ℓ` inner samples
of the level-`ℓ` approximation `g_ℓ` (`nestedSdeP`, `nestedSdeDelta`), under the hypotheses of
`nested_kink_sde_bias_rate` and `nested_kink_sde_variance_rate` (this formalisation's: bounded
centred conditional fourth moments of `g_ℓ`, first order weak convergence uniformly in the outer
sample, strong convergence of order `¼` in `L²`, and the small-ball bound for the exact
conditional mean `E_W[g(Z, W)]` near the kink `k`), and let `E[g₀(Z, W)²] < ∞`, so that the
level-`0` term `Y₀ = P₀` has a finite variance.  Let the inputs `ω^{(ℓ,n)}` be independent with
law `ν ⊗ ρ^{⊗ℕ}` and let the level-`ℓ` cost have mean `C_ℓ ≤ c₃ 4^ℓ` (twice as many timesteps and
twice as many inner samples per level).  Then there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the MLMC estimator of
`E_Z[f(E_W[g(Z, W)])]` has mean square error `< ε²` and expected cost `≤ c₄ ε^{−2.5}`: Theorem 1
(`giles_theorem1_corrections`) with `α = 1`, `β = 3/2`, `γ = 2`, so `ε^{−2−(γ−β)/α} = ε^{−2.5}`.
The rate `α = ½` of `nested_kink_bias_rate` would not do: Theorem 1 needs `α ≥ ½ min(β, γ)`, so
with `α = ½` it applies only with `β` lowered to `1`, and gives `O(ε⁻⁴)`.  Deviation: the paper's
`f` is continuous and piecewise differentiable; here `f` is piecewise linear with one kink, as in
`nested_kink_variance_rate`; several kinks or curved pieces are not covered (several kinks would
follow by summing the hinge terms, given a small-ball bound at each kink). -/
theorem nested_kink_sde_mlmc_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    (hg0 : Integrable (fun p : 𝒵 × 𝒲 => gh 0 p.1 p.2 ^ 2) (ν.prod ρ))
    {g : 𝒵 → 𝒲 → ℝ} {c_w c_d cₛ : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ cₛ)
    (ω : ℕ × ℕ → Ω → 𝒵 × (ℕ → 𝒲)) (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw ν ρ))
    (hind : iIndepFun ω μ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * 4 ^ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedSdeDelta f gh) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * ε ^ (-2.5 : ℝ) := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  have hbias := fun ℓ => nested_kink_sde_bias_rate ν ρ hf hgh hfib hw hball ℓ
  -- integrability: `P₀ ∈ L²`, then `f(E_W[g])` and every `P_ℓ` through the bias integrands
  have hP0 : MemLp (nestedSdeP f gh 0) 2 (nestedLaw ν ρ) :=
    memLp_two_kink_comp hf (measurable_innerMean (hgh 0) _ measurable_id)
      (integral_innerMean_sq_le ν ρ (hgh 0) hg0 (M := 2 ^ 0) (by positivity)).1
  have hP : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) :=
    ((hP0.integrable one_le_two).sub (hbias 0).1).congr
      (Eventually.of_forall fun p => by simp)
  have hPl : ∀ ℓ, Integrable (nestedSdeP f gh ℓ) (nestedLaw ν ρ) := fun ℓ =>
    ((hbias ℓ).1.add hP).congr (Eventually.of_forall fun p => by simp)
  have hGm : AEMeasurable (fun z => ∫ v, g z v ∂ρ) ν := aemeasurable_condMean_of_weak ν ρ hgh hw
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hΔm : ∀ ℓ, Measurable (nestedSdeDelta f gh ℓ) := measurable_nestedSdeDelta hfm hgh
  have hΔ : ∀ ℓ, MemLp (nestedSdeDelta f gh ℓ) 2 (nestedLaw ν ρ) := fun ℓ => by
    cases ℓ with
    | zero => exact hP0
    | succ ℓ => exact (nested_kink_sde_variance_rate ν ρ hf hgh hfib hw hball hs ℓ).1
  -- (i) the bias, `α = 1`
  obtain ⟨B₁, hB₁⟩ : ∃ B, B =
      4 * c_d * |c| * (1 + 80 * m₄) * (1 + c_w) + (|a₁| + |c|) * c_w := ⟨_, rfl⟩
  have h_i : ∀ ℓ : ℕ, |∫ y, nestedSdeP f gh ℓ y - nestedTarget f g ρ y ∂(nestedLaw ν ρ)| ≤
      (|B₁| + 1) * (2 : ℝ) ^ (-((1 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hb := (hbias ℓ).2
    rw [← hB₁] at hb
    rw [one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast 2 ℓ,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    linarith [le_abs_self B₁]
  -- (iii) the variance, `β = 3/2`
  obtain ⟨B₂, hB₂⟩ : ∃ B, B = 6 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w) +
      3 / 2 * (|a₁| + |c|) ^ 2 * (9 / 4 * c_w ^ 2 + cₛ) := ⟨_, rfl⟩
  have h_iii : ∀ ℓ : ℕ, variance (nestedSdeDelta f gh ℓ) (nestedLaw ν ρ) ≤
      (variance (nestedSdeDelta f gh 0) (nestedLaw ν ρ) + 3 * |B₂| + 1) *
        (2 : ℝ) ^ (-((3 / 2 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hv0 := variance_nonneg (nestedSdeDelta f gh 0) (nestedLaw ν ρ)
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← div_eq_mul_inv]
    cases ℓ with
    | zero =>
      rw [Nat.cast_zero, mul_zero, Real.rpow_zero, div_one]
      linarith [abs_nonneg B₂]
    | succ ℓ =>
      have hv : variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) ≤
          ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) := by
        simpa only [Pi.pow_apply] using
          variance_le_expectation_sq (hΔm (ℓ + 1)).aestronglyMeasurable
      have hr := (nested_kink_sde_variance_rate ν ρ hf hgh hfib hw hball hs ℓ).2
      rw [← hB₂] at hr
      -- `2^{3(ℓ+1)/2} = 2^{3/2} 2^{3ℓ/2} ≤ 3 · 2^{3ℓ/2}`
      have h32 : (2 : ℝ) ^ ((3 / 2 : ℝ) * ((ℓ + 1 : ℕ) : ℝ)) ≤
          3 * (2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ)) := by
        have e : (3 / 2 : ℝ) * ((ℓ + 1 : ℕ) : ℝ) = 3 / 2 + (3 / 2 : ℝ) * (ℓ : ℝ) := by
          push_cast
          ring
        rw [e, Real.rpow_add (by norm_num)]
        gcongr
        have h8 : (2 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt 8 := by
          rw [Real.sqrt_eq_rpow, show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [h8, Real.sqrt_le_left (by norm_num)]
        norm_num
      rw [le_div_iff₀ (by positivity)]
      have hvnn : 0 ≤ variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) :=
        variance_nonneg _ _
      calc variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) *
            (2 : ℝ) ^ ((3 / 2 : ℝ) * ((ℓ + 1 : ℕ) : ℝ))
          ≤ variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) *
            (3 * (2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ))) := mul_le_mul_of_nonneg_left h32 hvnn
        _ = 3 * ((2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ)) *
            variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ)) := by ring
        _ ≤ 3 * ((2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ)) *
            ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)) := by gcongr
        _ ≤ 3 * B₂ := by linarith
        _ ≤ variance (nestedSdeDelta f gh 0) (nestedLaw ν ρ) + 3 * |B₂| + 1 := by
            linarith [le_abs_self B₂]
  -- (iv) the cost, `γ = 2`
  have h_iv : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ ((2 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, Real.rpow_natCast]
    norm_num
    exact hC ℓ
  have hc₁ : 0 < |B₁| + 1 := by positivity
  have hc₂ : 0 < variance (nestedSdeDelta f gh 0) (nestedLaw ν ρ) + 3 * |B₂| + 1 := by
    have := variance_nonneg (nestedSdeDelta f gh 0) (nestedLaw ν ρ)
    positivity
  have hαβγ : min (3 / 2 : ℝ) 2 / 2 ≤ 1 := by norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_corrections (nestedTarget f g ρ) (nestedSdeP f gh)
    (nestedSdeDelta f gh) ω cost C one_pos (by norm_num) two_pos hc₁ hc₂ hc₃ hαβγ hω hind hP hPl
    hΔm hΔ hcost hcostC h_i (integral_nestedSdeDelta ν ρ f gh hPl) h_iii h_iv
  -- the quantity of interest is `E_Z[f(E_W[g(Z, W)])]`
  have hPint : ∫ y, nestedTarget f g ρ y ∂(nestedLaw ν ρ) = ∫ z, f (∫ v, g z v ∂ρ) ∂ν :=
    integral_comp_of_measurePreserving hfst (hfm.comp_aemeasurable hGm).aestronglyMeasurable
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost'⟩ := h ε hε hε1
  rw [hPint] at hmse
  rw [complexityBound_of_gt (by norm_num) ε, show (-2 - (2 - 3 / 2) / 1 : ℝ) = -2.5 by norm_num]
    at hcost'
  exact ⟨L, N, hN, hmse, hcost'⟩

end Discretised

/-! ### §9.2: the MIMC rates `β₁ = β₂ = 1.5` fail for a piecewise linear `f` -/

section MIMCKink

open scoped ENNReal

/-- The sign `+1` or `−1` of a fair coin `b : Bool` (the inner noise of the example
`kinkInnerApprox`). -/
def kinkSign (b : Bool) : ℝ := if b then 1 else -1

/-- The fair coin on `Bool`: the law of an inner sample in the example `kinkInnerApprox`. -/
noncomputable def kinkCoin : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

/-- The uniform law on `[0, 1]`: the law of the outer sample in the example `kinkInnerApprox`. -/
noncomputable def kinkOuter : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- The exact inner quantity of the example: `g(z, b) = z + s(b)/8` with the fair sign
`s(b) = ±1`, so that `E_W[g(z, W)] = z`. -/
noncomputable def kinkInner (z : ℝ) (b : Bool) : ℝ := z + kinkSign b / 8

/-- The level-`ℓ` inner approximation of the example: `g_ℓ(z, b) = z + s(b)/8 + 2^{−ℓ}/8`, whose
weak and strong errors `2^{−ℓ}/8` are of first order (a discretisation with a deterministic
first-order bias). -/
noncomputable def kinkInnerApprox (ℓ : ℕ) (z : ℝ) (b : Bool) : ℝ :=
  z + kinkSign b / 8 + ((2 : ℝ) ^ ℓ)⁻¹ / 8

/-- The fair coin is a probability measure. -/
instance : IsProbabilityMeasure kinkCoin := by
  constructor
  rw [kinkCoin, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    ← two_mul, mul_one, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The uniform law on `[0, 1]` is a probability measure. -/
instance : IsProbabilityMeasure kinkOuter := by
  constructor
  rw [kinkOuter, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

/-- The mean under the fair coin: `E[φ(W)] = (φ(true) + φ(false))/2`. -/
lemma integral_kinkCoin (φ : Bool → ℝ) : ∫ b, φ b ∂kinkCoin = (φ true + φ false) / 2 := by
  rw [kinkCoin, integral_smul_measure, integral_add_measure Integrable.of_finite
    Integrable.of_finite, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- The fair sign has mean `0`, second and fourth moments `1`, and modulus `1`. -/
lemma kinkSign_moments :
    ∫ b, kinkSign b ∂kinkCoin = 0 ∧ ∫ b, (kinkSign b - 0) ^ 2 ∂kinkCoin = 1 ∧
      ∫ b, (kinkSign b - 0) ^ 4 ∂kinkCoin = 1 ∧ ∀ b, |kinkSign b| = 1 := by
  refine ⟨?_, ?_, ?_, fun b => ?_⟩
  · rw [integral_kinkCoin]; norm_num [kinkSign]
  · rw [integral_kinkCoin]; norm_num [kinkSign]
  · rw [integral_kinkCoin]; norm_num [kinkSign]
  · cases b <;> norm_num [kinkSign]

/-- The inner mean of the example's level-`ℓ` approximation: for `M ≥ 1`,
`M⁻¹ ∑_{m<M} g_ℓ(z, w_m) = z + 2^{−ℓ}/8 + S_M(w)/8`, with `S_M(w) = M⁻¹ ∑_{m<M} s(w_m)`. -/
lemma innerMean_kinkInnerApprox (ℓ : ℕ) {M : ℕ} (hM : 0 < M) (z : ℝ) (w : ℕ → Bool) :
    innerMean (kinkInnerApprox ℓ) M z w =
      z + ((2 : ℝ) ^ ℓ)⁻¹ / 8 + innerMean (fun _ b => kinkSign b) M z w / 8 := by
  simp only [innerMean, kinkInnerApprox, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.sum_div]
  field_simp
  ring

/-- The mean of `M ≥ 1` fair signs lies in `[−1, 1]`. -/
lemma abs_innerMean_kinkSign_le {𝒵' : Type*} {M : ℕ} (hM : 0 < M) (z : 𝒵') (w : ℕ → Bool) :
    |innerMean (fun _ b => kinkSign b) M z w| ≤ 1 := by
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.2 hM
  unfold innerMean
  rw [abs_mul, abs_inv, abs_of_pos hM0, inv_mul_le_iff₀ hM0, mul_one]
  calc |∑ m ∈ range M, kinkSign (w m)| ≤ ∑ m ∈ range M, |kinkSign (w m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = M := by simp [kinkSign_moments.2.2.2]

/-- The antithetic difference of the hinge `x ↦ max(x, 0)` at the two coarse values `x + e₁`,
`x + e₂`: `max(x + (e₁ + e₂)/2, 0) − ½ max(x + e₁, 0) − ½ max(x + e₂, 0)` (Giles 2015, §9.1). -/
noncomputable def hingeAntithetic (e₁ e₂ x : ℝ) : ℝ :=
  max (x + (e₁ + e₂) / 2) 0 - max (x + e₁) 0 / 2 - max (x + e₂) 0 / 2

/-- The hinge antithetic difference vanishes when both coarse values lie on the same side of the
kink, it is continuous, and it has slope `−½` on the segment from `−max(e₁, e₂)` to `−(e₁ + e₂)/2`:
there, `H(x₁) − H(x₂) = (x₂ − x₁)/2` for `x₁ ≤ x₂`. -/
lemma hingeAntithetic_props (e₁ e₂ : ℝ) :
    (∀ x, x + e₁ ≤ 0 → x + e₂ ≤ 0 → hingeAntithetic e₁ e₂ x = 0) ∧
      (∀ x, 0 ≤ x + e₁ → 0 ≤ x + e₂ → hingeAntithetic e₁ e₂ x = 0) ∧
      Continuous (hingeAntithetic e₁ e₂) ∧
      (∀ x₁ x₂, -max e₁ e₂ ≤ x₁ → x₁ ≤ x₂ → x₂ ≤ -((e₁ + e₂) / 2) →
        hingeAntithetic e₁ e₂ x₁ - hingeAntithetic e₁ e₂ x₂ = (x₂ - x₁) / 2) := by
  refine ⟨fun x h1 h2 => ?_, fun x h1 h2 => ?_, ?_, fun x₁ x₂ h1 h12 h2 => ?_⟩
  · rw [hingeAntithetic, max_eq_right h1, max_eq_right h2, max_eq_right (by linarith)]
    ring
  · rw [hingeAntithetic, max_eq_left h1, max_eq_left h2, max_eq_left (by linarith)]
    ring
  · unfold hingeAntithetic
    fun_prop
  · unfold hingeAntithetic
    rcases le_total e₁ e₂ with h | h
    · rw [max_eq_right h] at h1
      rw [max_eq_right (show x₁ + (e₁ + e₂) / 2 ≤ 0 by linarith),
        max_eq_right (show x₂ + (e₁ + e₂) / 2 ≤ 0 by linarith),
        max_eq_right (show x₁ + e₁ ≤ 0 by linarith), max_eq_right (show x₂ + e₁ ≤ 0 by linarith),
        max_eq_left (show 0 ≤ x₁ + e₂ by linarith), max_eq_left (show 0 ≤ x₂ + e₂ by linarith)]
      ring
    · rw [max_eq_left h] at h1
      rw [max_eq_right (show x₁ + (e₁ + e₂) / 2 ≤ 0 by linarith),
        max_eq_right (show x₂ + (e₁ + e₂) / 2 ≤ 0 by linarith),
        max_eq_right (show x₁ + e₂ ≤ 0 by linarith), max_eq_right (show x₂ + e₂ ≤ 0 by linarith),
        max_eq_left (show 0 ≤ x₁ + e₁ by linarith), max_eq_left (show 0 ≤ x₂ + e₁ by linarith)]
      ring

/-- **The MIMC correction of the example** (Giles 2015, §9.2, p. 59, the six-term `Y_ℓ`): for
`f(x) = max(x − ½, 0)` and the inner approximations `kinkInnerApprox`, with `M = 2^{ℓ₁}`,
`e = S_M(w)/8` and `e′ = S_M(w′)/8` the scaled sign means of the two halves of the inner samples
and `μ_ℓ = 2^{−ℓ}/8`, the correction at `(ℓ₁ + 1, ℓ₂ + 1)` is
`H(z + μ_{ℓ₂+1} − ½) − H(z + μ_{ℓ₂} − ½)` with `H = hingeAntithetic e e′`. -/
lemma nestedMimcDelta_kink_eq (ℓ₁ ℓ₂ : ℕ) (z : ℝ) (w : ℕ → Bool) :
    nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1) (ℓ₂ + 1) (z, w) =
      hingeAntithetic (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) w / 8)
          (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) (shiftSeq (2 ^ ℓ₁) w) / 8)
          (z + ((2 : ℝ) ^ (ℓ₂ + 1))⁻¹ / 8 - 1 / 2) -
        hingeAntithetic (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) w / 8)
          (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) (shiftSeq (2 ^ ℓ₁) w) / 8)
          (z + ((2 : ℝ) ^ ℓ₂)⁻¹ / 8 - 1 / 2) := by
  have hM : 0 < 2 ^ ℓ₁ := by positivity
  have h0 : innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) z w =
      innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) w := rfl
  have h0' : innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) z (shiftSeq (2 ^ ℓ₁) w) =
      innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) (shiftSeq (2 ^ ℓ₁) w) := rfl
  show nestedDelta _ (kinkInnerApprox (ℓ₂ + 1)) (ℓ₁ + 1) (z, w) -
    nestedDelta _ (kinkInnerApprox ℓ₂) (ℓ₁ + 1) (z, w) = _
  rw [nestedDelta_succ_eq, nestedDelta_succ_eq]
  simp only [innerMean_kinkInnerApprox _ hM, hingeAntithetic, h0, h0']
  ring_nf

/-- **Shifting the outer sample does not change the mean of the hinge difference** (the example
of `kinkInnerApprox`): if `|e₁|, |e₂| ≤ 1/8` and `−7/8 ≤ c ≤ −1/8`, then for `Z` uniform on
`[0, 1]`, `E[H(Z + c)] = ∫_{−1/8}^{1/8} H`, where `H = hingeAntithetic e₁ e₂` vanishes outside
`[−1/8, 1/8]`. -/
lemma integral_hingeAntithetic_shift {e₁ e₂ c : ℝ} (h1 : |e₁| ≤ 1 / 8) (h2 : |e₂| ≤ 1 / 8)
    (hc : c ≤ -1 / 8) (hc' : -7 / 8 ≤ c) :
    ∫ z, hingeAntithetic e₁ e₂ (z + c) ∂kinkOuter =
      ∫ u in (-1 / 8 : ℝ)..(1 / 8), hingeAntithetic e₁ e₂ u := by
  obtain ⟨hz1, hz2, hcont, -⟩ := hingeAntithetic_props e₁ e₂
  obtain ⟨h1l, h1r⟩ := abs_le.1 h1
  obtain ⟨h2l, h2r⟩ := abs_le.1 h2
  rw [kinkOuter, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_add_right, zero_add,
    ← intervalIntegral.integral_add_adjacent_intervals (b := -1 / 8)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := -1 / 8) (b := 1 / 8)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hl : ∫ u in c..(-1 / 8 : ℝ), hingeAntithetic e₁ e₂ u = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_,
      intervalIntegral.integral_zero]
    rw [Set.uIcc_of_le hc] at hu
    exact hz1 u (by linarith [hu.2]) (by linarith [hu.2])
  have hr : ∫ u in (1 / 8 : ℝ)..(1 + c), hingeAntithetic e₁ e₂ u = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_,
      intervalIntegral.integral_zero]
    rw [Set.uIcc_of_le (by linarith)] at hu
    exact hz2 u (by linarith [hu.1]) (by linarith [hu.1])
  rw [hl, hr]
  ring

/-- **The hinge difference changes by half the shift on a segment of length `|e₁ − e₂|/2 − d`**
(the example of `kinkInnerApprox`): if `|e₁|, |e₂| ≤ 1/8`, `c₁ ≤ c₀`, `c₁ ≤ −1/8` and
`−7/8 ≤ c₀`, then for `Z` uniform on `[0, 1]` and `d = c₀ − c₁`,
`E[(H(Z + c₁) − H(Z + c₀))²] ≥ (d²/4)(|e₁ − e₂|/2 − d)`, since the difference is `d/2` for
`Z ∈ [−max(e₁, e₂) − c₁, −(e₁ + e₂)/2 − c₀] ⊆ [0, 1]`. -/
lemma integral_sq_hingeAntithetic_sub_ge {e₁ e₂ c₀ c₁ : ℝ} (h1 : |e₁| ≤ 1 / 8)
    (h2 : |e₂| ≤ 1 / 8) (hc : c₁ ≤ c₀) (hc₁ : c₁ ≤ -1 / 8) (hc₀ : -7 / 8 ≤ c₀) :
    (c₀ - c₁) ^ 2 / 4 * (|e₁ - e₂| / 2 - (c₀ - c₁)) ≤
      ∫ z, (hingeAntithetic e₁ e₂ (z + c₁) - hingeAntithetic e₁ e₂ (z + c₀)) ^ 2
        ∂kinkOuter := by
  obtain ⟨-, -, hcont, hslope⟩ := hingeAntithetic_props e₁ e₂
  obtain ⟨h1l, h1r⟩ := abs_le.1 h1
  obtain ⟨h2l, h2r⟩ := abs_le.1 h2
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = -max e₁ e₂ - c₁ := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = -((e₁ + e₂) / 2) - c₀ := ⟨_, rfl⟩
  have hmax : max e₁ e₂ ≤ 1 / 8 := max_le h1r h2r
  have hF : Continuous fun z =>
      (hingeAntithetic e₁ e₂ (z + c₁) - hingeAntithetic e₁ e₂ (z + c₀)) ^ 2 := by
    fun_prop
  have hFi : Integrable (fun z =>
      (hingeAntithetic e₁ e₂ (z + c₁) - hingeAntithetic e₁ e₂ (z + c₀)) ^ 2) kinkOuter :=
    hF.integrableOn_Icc
  have hsub : Set.Icc α β ⊆ Set.Icc 0 1 := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hreal : kinkOuter.real (Set.Icc α β) = max (β - α) 0 := by
    rw [measureReal_def, kinkOuter, Measure.restrict_apply measurableSet_Icc,
      Set.inter_eq_left.2 hsub, Real.volume_Icc, ENNReal.toReal_ofReal']
  have hβα : β - α = |e₁ - e₂| / 2 - (c₀ - c₁) := by
    rw [hα, hβ]
    rcases le_total e₁ e₂ with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]
      ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]
      ring
  calc (c₀ - c₁) ^ 2 / 4 * (|e₁ - e₂| / 2 - (c₀ - c₁))
      ≤ kinkOuter.real (Set.Icc α β) * ((c₀ - c₁) ^ 2 / 4) := by
        rw [hreal, ← hβα, mul_comm]
        gcongr
        exact le_max_left _ _
    _ = ∫ z in Set.Icc α β, (c₀ - c₁) ^ 2 / 4 ∂kinkOuter := by
        rw [setIntegral_const, smul_eq_mul]
    _ = ∫ z in Set.Icc α β,
          (hingeAntithetic e₁ e₂ (z + c₁) - hingeAntithetic e₁ e₂ (z + c₀)) ^ 2 ∂kinkOuter := by
        refine setIntegral_congr_fun measurableSet_Icc fun z hz => ?_
        have := hslope (z + c₁) (z + c₀) (by linarith [hz.1]) (by linarith)
          (by linarith [hz.2])
        rw [this]
        ring
    _ ≤ ∫ z, (hingeAntithetic e₁ e₂ (z + c₁) - hingeAntithetic e₁ e₂ (z + c₀)) ^ 2
          ∂kinkOuter :=
        setIntegral_le_integral hFi (Eventually.of_forall fun z => sq_nonneg _)

/-- **The two coarse sign means are `2^{−j}` apart on average** (Khintchine's inequality for fair
signs): for `M = 4^j` fair signs in each half, `E|S_M(W) − S_M(W′)| ≥ (5/8) 2^{−j}`.  Proof: with
`X = S_M(W) − S_M(W′)` and `t = 2^{−j}`, `16 t³ |X| ≥ 12 t² X² − X⁴` pointwise (it is
`|X| (|X| − 2t)² (|X| + 4t) ≥ 0`), `E[X²] = 2/M` and `E[X⁴] ≤ 14/M²` (`fiber_sum_moments`). -/
lemma integral_abs_kinkSignMean_sub_ge (j : ℕ) (z : ℝ) :
    5 / 8 * ((2 : ℝ) ^ j)⁻¹ ≤ ∫ w, |innerMean (fun _ b => kinkSign b) (2 ^ (2 * j)) z w -
        innerMean (fun _ b => kinkSign b) (2 ^ (2 * j)) z (shiftSeq (2 ^ (2 * j)) w)|
        ∂(innerLaw kinkCoin) := by
  set M : ℕ := 2 ^ (2 * j) with hMdef
  set t : ℝ := ((2 : ℝ) ^ j)⁻¹ with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hMt : (M : ℝ) = (t ^ 2)⁻¹ := by
    rw [hMdef, ht]
    push_cast
    rw [inv_pow, inv_inv, ← pow_mul, mul_comm]
  obtain ⟨hσ0, hσ2, hσ4, -⟩ := kinkSign_moments
  have hσm : Measurable kinkSign := Measurable.of_discrete
  have hσ4i : Integrable (fun b => kinkSign b ^ 4) kinkCoin := Integrable.of_finite
  obtain ⟨i4, -, e2, e4⟩ :=
    fiber_sum_moments kinkCoin hσm hσ4i (nestedSign M) (nestedSign_sq M) (2 * M)
  rw [hσ0] at i4 e2 e4
  rw [hσ2] at e2
  rw [hσ2, hσ4] at e4
  set S : (ℕ → Bool) → ℝ := fun w => ∑ m ∈ range (2 * M), nestedSign M m * (kinkSign (w m) - 0)
    with hS
  have hX : ∀ w : ℕ → Bool, innerMean (fun _ b => kinkSign b) M z w -
      innerMean (fun _ b => kinkSign b) M z (shiftSeq M w) = (M : ℝ)⁻¹ * S w := fun w =>
    signed_sum_eq (fun _ b => kinkSign b) M z w 0
  simp only [hX]
  have hSm : Measurable S := by
    rw [hS]
    exact Finset.measurable_sum _ fun m _ =>
      ((hσm.comp (measurable_pi_apply m)).sub_const 0).const_mul _
  have i2 : Integrable (fun w => S w ^ 2) (innerLaw kinkCoin) :=
    integrable_pow_of_pow_four hSm i4 (by norm_num)
  have i1 : Integrable (fun w => |(M : ℝ)⁻¹ * S w|) (innerLaw kinkCoin) := by
    have := integrable_pow_of_pow_four hSm i4 (k := 1) (by norm_num)
    simp only [pow_one] at this
    exact (this.const_mul _).abs
  -- the pointwise inequality, integrated
  have hpt : ∀ w, 12 * t ^ 2 * ((M : ℝ)⁻¹ ^ 2 * S w ^ 2) - (M : ℝ)⁻¹ ^ 4 * S w ^ 4 ≤
      16 * t ^ 3 * |(M : ℝ)⁻¹ * S w| := fun w => by
    set u := |(M : ℝ)⁻¹ * S w|
    have hu : 0 ≤ u := abs_nonneg _
    have hu2 : u ^ 2 = (M : ℝ)⁻¹ ^ 2 * S w ^ 2 := by rw [sq_abs, mul_pow]
    have hu4 : u ^ 4 = (M : ℝ)⁻¹ ^ 4 * S w ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hu2]
      ring
    rw [← hu2, ← hu4]
    nlinarith [mul_nonneg (mul_nonneg hu (sq_nonneg (u - 2 * t))) (by linarith : 0 ≤ u + 4 * t)]
  have j1 : Integrable (fun w => 12 * t ^ 2 * ((M : ℝ)⁻¹ ^ 2 * S w ^ 2)) (innerLaw kinkCoin) :=
    (i2.const_mul _).const_mul _
  have j2 : Integrable (fun w => (M : ℝ)⁻¹ ^ 4 * S w ^ 4) (innerLaw kinkCoin) := i4.const_mul _
  have hint : ∫ w, (12 * t ^ 2 * ((M : ℝ)⁻¹ ^ 2 * S w ^ 2) - (M : ℝ)⁻¹ ^ 4 * S w ^ 4)
      ∂(innerLaw kinkCoin) ≤ ∫ w, 16 * t ^ 3 * |(M : ℝ)⁻¹ * S w| ∂(innerLaw kinkCoin) :=
    integral_mono (j1.sub j2) (i1.const_mul _) hpt
  rw [integral_sub j1 j2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, e2] at hint
  have hinv : (M : ℝ)⁻¹ = t ^ 2 := by rw [hMt, inv_inv]
  have h4 : (M : ℝ)⁻¹ ^ 4 * ∫ w, S w ^ 4 ∂(innerLaw kinkCoin) ≤
      (M : ℝ)⁻¹ ^ 4 * (((2 * M : ℕ) : ℝ) * 1 + 3 * ((2 * M : ℕ) : ℝ) ^ 2 * 1 ^ 2) := by
    gcongr
  have hval : 12 * t ^ 2 * ((M : ℝ)⁻¹ ^ 2 * (((2 * M : ℕ) : ℝ) * 1)) -
      (M : ℝ)⁻¹ ^ 4 * (((2 * M : ℕ) : ℝ) * 1 + 3 * ((2 * M : ℕ) : ℝ) ^ 2 * 1 ^ 2) =
      12 * t ^ 4 - 2 * t ^ 6 := by
    push_cast
    rw [hinv, hMt]
    field_simp
    ring
  have h10 : 10 * t ^ 4 ≤ 16 * t ^ 3 * ∫ w, |(M : ℝ)⁻¹ * S w| ∂(innerLaw kinkCoin) := by
    have ht2 : t ^ 6 ≤ t ^ 4 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
    linarith
  have h16 : 0 < 16 * t ^ 3 := by positivity
  rw [← mul_le_mul_iff_of_pos_left h16]
  calc 16 * t ^ 3 * (5 / 8 * t) = 10 * t ^ 4 := by ring
    _ ≤ _ := h10

/-- The hinge antithetic difference is at most `1/8` in absolute value when `|e₁|, |e₂| ≤ 1/8`
(it is `1`-Lipschitz in each coarse value). -/
lemma abs_hingeAntithetic_le {e₁ e₂ : ℝ} (h1 : |e₁| ≤ 1 / 8) (h2 : |e₂| ≤ 1 / 8) (x : ℝ) :
    |hingeAntithetic e₁ e₂ x| ≤ 1 / 8 := by
  have a1 := abs_max_sub_max_le_abs (x + (e₁ + e₂) / 2) (x + e₁) 0
  have a2 := abs_max_sub_max_le_abs (x + (e₁ + e₂) / 2) (x + e₂) 0
  rw [show x + (e₁ + e₂) / 2 - (x + e₁) = (e₂ - e₁) / 2 by ring] at a1
  rw [show x + (e₁ + e₂) / 2 - (x + e₂) = (e₁ - e₂) / 2 by ring] at a2
  have e : hingeAntithetic e₁ e₂ x = (max (x + (e₁ + e₂) / 2) 0 - max (x + e₁) 0) / 2 +
      (max (x + (e₁ + e₂) / 2) 0 - max (x + e₂) 0) / 2 := by
    unfold hingeAntithetic
    ring
  rw [e]
  have b1 : |(e₂ - e₁) / 2| ≤ 1 / 8 := by
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have b2 : |(e₁ - e₂) / 2| ≤ 1 / 8 := by
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  calc |(max (x + (e₁ + e₂) / 2) 0 - max (x + e₁) 0) / 2 +
        (max (x + (e₁ + e₂) / 2) 0 - max (x + e₂) 0) / 2|
      ≤ |(max (x + (e₁ + e₂) / 2) 0 - max (x + e₁) 0) / 2| +
        |(max (x + (e₁ + e₂) / 2) 0 - max (x + e₂) 0) / 2| := abs_add_le _ _
    _ ≤ 1 / 8 / 2 + 1 / 8 / 2 := by
        rw [abs_div, abs_div, abs_two]
        gcongr
        · exact a1.trans b1
        · exact a2.trans b2
    _ = 1 / 8 := by norm_num

/-- The scaled sign means of the example lie in `[−1/8, 1/8]`. -/
lemma abs_kinkSignMean_div_le {M : ℕ} (hM : 0 < M) (z : ℝ) (w : ℕ → Bool) :
    |innerMean (fun _ b => kinkSign b) M z w / 8| ≤ 1 / 8 := by
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  exact div_le_div_of_nonneg_right (abs_innerMean_kinkSign_le hM z w) (by norm_num)

/-- The level approximations of the example are measurable. -/
lemma measurable_kinkInnerApprox (ℓ : ℕ) : Measurable (Function.uncurry (kinkInnerApprox ℓ)) := by
  have hσ : Measurable fun p : ℝ × Bool => kinkSign p.2 :=
    (Measurable.of_discrete : Measurable kinkSign).comp measurable_snd
  exact (measurable_fst.add (hσ.div_const 8)).add_const _

/-- **The MIMC correction of the example is bounded and measurable** (`|Y| ≤ 1/4`). -/
lemma kinkMimc_bound (ℓ₁ ℓ₂ : ℕ) :
    Measurable (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1) (ℓ₂ + 1)) ∧
      ∀ p, |nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1) (ℓ₂ + 1) p|
        ≤ 1 / 4 := by
  have hfm : Measurable fun x : ℝ => max (x - 1 / 2) 0 := by fun_prop
  refine ⟨(measurable_nestedDelta hfm (measurable_kinkInnerApprox (ℓ₂ + 1)) (ℓ₁ + 1)).sub
    (measurable_nestedDelta hfm (measurable_kinkInnerApprox ℓ₂) (ℓ₁ + 1)), fun p => ?_⟩
  have hM : 0 < 2 ^ ℓ₁ := by positivity
  obtain ⟨z, w⟩ := p
  rw [nestedMimcDelta_kink_eq]
  have h1 := abs_kinkSignMean_div_le hM 0 w
  have h2 := abs_kinkSignMean_div_le hM 0 (shiftSeq (2 ^ ℓ₁) w)
  calc _ ≤ |hingeAntithetic (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) w / 8)
          (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) (shiftSeq (2 ^ ℓ₁) w) / 8)
          (z + ((2 : ℝ) ^ (ℓ₂ + 1))⁻¹ / 8 - 1 / 2)| +
        |hingeAntithetic (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) w / 8)
          (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) (shiftSeq (2 ^ ℓ₁) w) / 8)
          (z + ((2 : ℝ) ^ ℓ₂)⁻¹ / 8 - 1 / 2)| := abs_sub _ _
    _ ≤ 1 / 8 + 1 / 8 :=
        add_le_add (abs_hingeAntithetic_le h1 h2 _) (abs_hingeAntithetic_le h1 h2 _)
    _ = 1 / 4 := by norm_num

/-- The shifts of the example: `μ_ℓ − ½ = 2^{−ℓ}/8 − ½ ∈ [−7/8, −1/8]`, and
`μ_ℓ − μ_{ℓ+1} = 2^{−ℓ}/16`. -/
lemma kink_shift_bounds (ℓ : ℕ) :
    ((2 : ℝ) ^ ℓ)⁻¹ / 8 - 1 / 2 ≤ -1 / 8 ∧ -7 / 8 ≤ ((2 : ℝ) ^ ℓ)⁻¹ / 8 - 1 / 2 ∧
      ((2 : ℝ) ^ ℓ)⁻¹ / 8 - 1 / 2 - (((2 : ℝ) ^ (ℓ + 1))⁻¹ / 8 - 1 / 2) =
        ((2 : ℝ) ^ ℓ)⁻¹ / 16 := by
  have h0 : 0 < ((2 : ℝ) ^ ℓ)⁻¹ := by positivity
  have h1 : ((2 : ℝ) ^ ℓ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  refine ⟨by linarith, by linarith, ?_⟩
  rw [pow_succ]
  field_simp
  ring

/-- **The MIMC correction of the example has mean zero**: for each inner sample, the outer
sample `Z` uniform on `[0, 1]` sees the same hinge difference at both shifts
(`integral_hingeAntithetic_shift`). -/
lemma integral_kinkMimc (ℓ₁ ℓ₂ : ℕ) :
    ∫ p, nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1) (ℓ₂ + 1) p
      ∂(nestedLaw kinkOuter kinkCoin) = 0 := by
  obtain ⟨hYm, hYb⟩ := kinkMimc_bound ℓ₁ ℓ₂
  have hYi : Integrable (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1)
      (ℓ₂ + 1)) (nestedLaw kinkOuter kinkCoin) :=
    (integrable_const (1 / 4 : ℝ)).mono' hYm.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hYb p)
  rw [integral_prod_symm _ hYi]
  have hM : 0 < 2 ^ ℓ₁ := by positivity
  have hw : ∀ w : ℕ → Bool, ∫ z, nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox
      (ℓ₁ + 1) (ℓ₂ + 1) (z, w) ∂kinkOuter = 0 := fun w => by
    have h1 := abs_kinkSignMean_div_le hM 0 w
    have h2 := abs_kinkSignMean_div_le hM 0 (shiftSeq (2 ^ ℓ₁) w)
    obtain ⟨-, -, hcont, -⟩ := hingeAntithetic_props
      (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) w / 8)
      (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) (shiftSeq (2 ^ ℓ₁) w) / 8)
    obtain ⟨a1, a2, -⟩ := kink_shift_bounds (ℓ₂ + 1)
    obtain ⟨b1, b2, -⟩ := kink_shift_bounds ℓ₂
    have hi : ∀ c, Integrable (fun z => hingeAntithetic
        (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) w / 8)
        (innerMean (fun _ b => kinkSign b) (2 ^ ℓ₁) (0 : ℝ) (shiftSeq (2 ^ ℓ₁) w) / 8) (z + c))
        kinkOuter := fun c => (by fun_prop : Continuous _).integrableOn_Icc
    simp only [nestedMimcDelta_kink_eq, add_sub_assoc]
    rw [integral_sub (hi _) (hi _), integral_hingeAntithetic_shift h1 h2 a1 a2,
      integral_hingeAntithetic_shift h1 h2 b1 b2, sub_self]
  simp only [hw, integral_zero]

/-- **A lower bound for the second moment of the example's MIMC correction**: for `ℓ₁ = 2j` and
`ℓ₂ ≥ j + 1`, `E[Y_{(ℓ₁+1, ℓ₂+1)}²] ≥ 2^{−(2ℓ₂ + j + 17)}`.  For each inner sample the correction
is half the shift difference `d = 2^{−ℓ₂}/16` on an interval of outer samples of length
`|e − e′|/2 − d` (`integral_sq_hingeAntithetic_sub_ge`), and `E|e − e′| ≥ (5/64) 2^{−j}`
(`integral_abs_kinkSignMean_sub_ge`), while `d ≤ 2^{−j}/32`. -/
lemma integral_sq_kinkMimc_ge {j ℓ₂ : ℕ} (h : j + 1 ≤ ℓ₂) :
    ((2 : ℝ) ^ (2 * ℓ₂ + j + 17))⁻¹ ≤
      ∫ p, nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (2 * j + 1) (ℓ₂ + 1) p ^ 2
        ∂(nestedLaw kinkOuter kinkCoin) := by
  obtain ⟨hYm, hYb⟩ := kinkMimc_bound (2 * j) ℓ₂
  have hY2i : Integrable (fun p => nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox
      (2 * j + 1) (ℓ₂ + 1) p ^ 2) (nestedLaw kinkOuter kinkCoin) :=
    (integrable_const (1 / 16 : ℝ)).mono' (hYm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_pow]
        have := hYb p
        have h0 := abs_nonneg (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox
          (2 * j + 1) (ℓ₂ + 1) p)
        nlinarith)
  rw [integral_prod_symm _ hY2i]
  set M : ℕ := 2 ^ (2 * j)
  have hM : 0 < M := by positivity
  set d : ℝ := ((2 : ℝ) ^ ℓ₂)⁻¹ / 16 with hd
  set X : (ℕ → Bool) → ℝ := fun w => innerMean (fun _ b => kinkSign b) M (0 : ℝ) w -
    innerMean (fun _ b => kinkSign b) M (0 : ℝ) (shiftSeq M w) with hX
  obtain ⟨a1, -, -⟩ := kink_shift_bounds (ℓ₂ + 1)
  obtain ⟨-, b2, hab⟩ := kink_shift_bounds ℓ₂
  -- the bound for each inner sample
  have hw : ∀ w : ℕ → Bool, d ^ 2 / 4 * (|X w| / 16 - d) ≤
      ∫ z, nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (2 * j + 1) (ℓ₂ + 1)
        (z, w) ^ 2 ∂kinkOuter := fun w => by
    have h1 := abs_kinkSignMean_div_le hM 0 w
    have h2 := abs_kinkSignMean_div_le hM 0 (shiftSeq M w)
    simp only [nestedMimcDelta_kink_eq, add_sub_assoc]
    have key := integral_sq_hingeAntithetic_sub_ge h1 h2 (by rw [← sub_nonneg, hab]; positivity)
      a1 b2
    rw [hab] at key
    convert key using 3
    rw [hX, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    ring
  -- integrate over the inner samples
  have hXm : Measurable X := by
    have hσ : Measurable fun b : Bool => kinkSign b := Measurable.of_discrete
    exact (measurable_innerMean_right (g := fun (_ : ℝ) b => kinkSign b) (z := 0) hσ M).sub
      ((measurable_innerMean_right (g := fun (_ : ℝ) b => kinkSign b) (z := 0) hσ M).comp
        (measurable_shiftSeq M))
  have hXb : ∀ w, |X w| ≤ 2 := fun w => by
    have h1 := abs_innerMean_kinkSign_le hM (0 : ℝ) w
    have h2 := abs_innerMean_kinkSign_le hM (0 : ℝ) (shiftSeq M w)
    exact (abs_sub _ _).trans (by linarith)
  have hXi : Integrable (fun w => |X w|) (innerLaw kinkCoin) :=
    (integrable_const (2 : ℝ)).mono' (continuous_abs.measurable.comp hXm).aestronglyMeasurable
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs, abs_abs]; exact hXb w)
  have hlow : Integrable (fun w => d ^ 2 / 4 * (|X w| / 16 - d)) (innerLaw kinkCoin) :=
    ((hXi.div_const 16).sub (integrable_const d)).const_mul _
  have hmono := integral_mono hlow hY2i.integral_prod_right hw
  rw [integral_const_mul, integral_sub (hXi.div_const 16) (integrable_const d), integral_div,
    integral_const, probReal_univ, one_smul] at hmono
  refine le_trans ?_ hmono
  -- the constants: `E|X| ≥ (5/8) t`, `d ≤ t/32` with `t = 2^{−j}`
  have hK := integral_abs_kinkSignMean_sub_ge j 0
  set t : ℝ := ((2 : ℝ) ^ j)⁻¹ with ht
  have hdt : d ≤ t / 32 := by
    have hp : (2 : ℝ) ^ (j + 1) ≤ 2 ^ ℓ₂ := pow_le_pow_right₀ (by norm_num) h
    have : ((2 : ℝ) ^ ℓ₂)⁻¹ ≤ ((2 : ℝ) ^ (j + 1))⁻¹ := inv_anti₀ (by positivity) hp
    rw [hd, ht]
    rw [pow_succ, mul_inv] at this
    linarith
  have hval : ((2 : ℝ) ^ (2 * ℓ₂ + j + 17))⁻¹ = d ^ 2 / 4 * (t / 128) := by
    rw [hd, ht, show 2 * ℓ₂ + j + 17 = ℓ₂ + ℓ₂ + j + 17 by ring, pow_add, pow_add, pow_add]
    field_simp
    norm_num
  rw [hval]
  have hE : t / 128 ≤ (∫ w, |X w| ∂(innerLaw kinkCoin)) / 16 - d := by
    linarith
  gcongr

/-- **The example satisfies the hypotheses of the kink analysis** (Giles 2015, §9.2, p. 60: "if the
function `f` is continuous and piecewise differentiable … with MIMC we would have
`β₁ = β₂ = 1.5`").  For `f(x) = max(x − ½, 0)`, the outer sample `Z` uniform on `[0, 1]`
(`kinkOuter`), fair signs as inner samples (`kinkCoin`), the exact inner quantity
`g(z, b) = z + s(b)/8` (`kinkInner`) and its level-`ℓ` approximations
`g_ℓ(z, b) = g(z, b) + 2^{−ℓ}/8` (`kinkInnerApprox`): the `g_ℓ` are measurable; the centred
conditional fourth moments are `E_W[(g_ℓ(z, W) − E_W[g_ℓ(z, W)])⁴] = 1/4096`; `E[g₀(Z, W)²] < ∞`;
the weak error is exactly of first order uniformly in the outer sample,
`2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| = 1/8`; `E_W[g(Z, W)] = Z` has the small-ball bound
`ν{|E_W[g(Z, W)] − ½| ≤ t} ≤ 2t`; and the strong error is of first order pathwise,
`g_{ℓ+1} − g_ℓ = −2^{−ℓ}/16` (so every `Lᵖ` strong order and the weak order of the level
differences are of first order).  So the example satisfies the hypotheses of
`nested_kink_sde_bias_rate`, `nested_kink_sde_variance_rate` and
`nested_kink_sde_mlmc_complexity` (`kinkInnerApprox_mlmc_rates`), and those of
`nested_mimc_variance_rate`, the MIMC rate theorem, except its smoothness of `f` (`|g_ℓ| ≤ 5/4` on
the support of `Z`). -/
theorem kinkInnerApprox_hypotheses :
    (∀ ℓ, Measurable (Function.uncurry (kinkInnerApprox ℓ))) ∧
      (∀ ℓ z, Integrable (fun v => kinkInnerApprox ℓ z v ^ 4) kinkCoin ∧
        ∫ v, (kinkInnerApprox ℓ z v - ∫ u, kinkInnerApprox ℓ z u ∂kinkCoin) ^ 4 ∂kinkCoin =
          1 / 4096) ∧
      Integrable (fun p : ℝ × Bool => kinkInnerApprox 0 p.1 p.2 ^ 2) (kinkOuter.prod kinkCoin) ∧
      (∀ ℓ z, (2 : ℝ) ^ ℓ * |∫ v, kinkInnerApprox ℓ z v ∂kinkCoin - ∫ v, kinkInner z v ∂kinkCoin|
        = 1 / 8) ∧
      (∀ t : ℝ, 0 < t →
        kinkOuter {z | |∫ v, kinkInner z v ∂kinkCoin - 1 / 2| ≤ t} ≤ ENNReal.ofReal (2 * t)) ∧
      (∀ ℓ z b, kinkInnerApprox (ℓ + 1) z b - kinkInnerApprox ℓ z b = -(((2 : ℝ) ^ ℓ)⁻¹ / 16)) := by
  have hG : ∀ z, ∫ v, kinkInner z v ∂kinkCoin = z := fun z => by
    rw [integral_kinkCoin]
    simp only [kinkInner, kinkSign]
    norm_num
    ring
  have hGl : ∀ ℓ z, ∫ v, kinkInnerApprox ℓ z v ∂kinkCoin = z + ((2 : ℝ) ^ ℓ)⁻¹ / 8 :=
    fun ℓ z => by
      rw [integral_kinkCoin]
      simp only [kinkInnerApprox, kinkSign]
      norm_num
      ring
  refine ⟨measurable_kinkInnerApprox, fun ℓ z => ⟨Integrable.of_finite, ?_⟩, ?_, fun ℓ z => ?_,
    fun t ht => ?_, fun ℓ z b => ?_⟩
  · rw [hGl, integral_kinkCoin]
    simp only [kinkInnerApprox, kinkSign]
    norm_num
  · have hm : Measurable fun p : ℝ × Bool => kinkInnerApprox 0 p.1 p.2 ^ 2 :=
      (measurable_kinkInnerApprox 0).pow_const 2
    refine (integrable_prod_iff hm.aestronglyMeasurable).2
      ⟨Eventually.of_forall fun z => Integrable.of_finite, ?_⟩
    have e : (fun z => ∫ v, ‖kinkInnerApprox 0 z v ^ 2‖ ∂kinkCoin) = fun z =>
        (‖kinkInnerApprox 0 z true ^ 2‖ + ‖kinkInnerApprox 0 z false ^ 2‖) / 2 :=
      funext fun z => integral_kinkCoin _
    rw [e]
    exact Continuous.integrableOn_Icc (by unfold kinkInnerApprox; fun_prop)
  · rw [hGl, hG, show z + ((2 : ℝ) ^ ℓ)⁻¹ / 8 - z = ((2 : ℝ) ^ ℓ)⁻¹ / 8 by ring,
      abs_of_pos (by positivity)]
    field_simp
  · simp only [hG]
    calc kinkOuter {z | |z - 1 / 2| ≤ t} ≤ volume {z : ℝ | |z - 1 / 2| ≤ t} :=
          Measure.restrict_le_self _
      _ ≤ volume (Set.Icc (1 / 2 - t) (1 / 2 + t)) := measure_mono fun z hz => by
          have := abs_le.1 (show |z - 1 / 2| ≤ t from hz)
          exact ⟨by linarith [this.1], by linarith [this.2]⟩
      _ = ENNReal.ofReal (2 * t) := by rw [Real.volume_Icc]; ring_nf
  · simp only [kinkInnerApprox]
    rw [pow_succ]
    field_simp
    ring

/-- **The MLMC rates `α = 1`, `β = 3/2` hold for the example** (Giles 2015, §9.2, p. 60: "in the
MLMC treatment we would get `β = 1.5`, and hence an overall complexity which is
`O(ε^{−2.5})`"): for `f(x) = max(x − ½, 0)` and the example `kinkInnerApprox`
(`kinkInnerApprox_hypotheses`), `nested_kink_sde_bias_rate` and `nested_kink_sde_variance_rate`
apply with `a₀ = a₁ = 0`, `c = 1`, `k = ½`, `m₄ = 1/4096`, `c_w = 1/8`, `c_d = 2` and
`cₛ = 1/256`, and give `2^ℓ |E[P_ℓ − f(E_W[g(Z, W)])]| ≤ 10` and `2^{3ℓ/2} E[Y_{ℓ+1}²] ≤ 14` for
every `ℓ`.  So the hypotheses of the MLMC theorems of this file can be met, and on the same
example the paper's MIMC rates fail (`nested_mimc_kink_rates_false`). -/
theorem kinkInnerApprox_mlmc_rates (ℓ : ℕ) :
    (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP (fun x => max (x - 1 / 2) 0) kinkInnerApprox ℓ p -
        nestedTarget (fun x => max (x - 1 / 2) 0) kinkInner kinkCoin p)
        ∂(nestedLaw kinkOuter kinkCoin)| ≤ 10 ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedSdeDelta (fun x => max (x - 1 / 2) 0)
        kinkInnerApprox (ℓ + 1) p ^ 2 ∂(nestedLaw kinkOuter kinkCoin) ≤ 14 := by
  obtain ⟨hm, hmom, -, hweak, hball, hstrong⟩ := kinkInnerApprox_hypotheses
  have hf : ∀ x : ℝ, max (x - 1 / 2) 0 = 0 + 0 * x + 1 * max (x - 1 / 2) 0 := fun x => by ring
  have hfib : ∀ ℓ, ∀ᵐ z ∂kinkOuter, Integrable (fun v => kinkInnerApprox ℓ z v ^ 4) kinkCoin ∧
      ∫ v, (kinkInnerApprox ℓ z v - ∫ u, kinkInnerApprox ℓ z u ∂kinkCoin) ^ 4 ∂kinkCoin ≤
        1 / 4096 :=
    fun ℓ => Eventually.of_forall fun z => ⟨(hmom ℓ z).1, (hmom ℓ z).2.le⟩
  have hw : ∀ ℓ, ∀ᵐ z ∂kinkOuter, (2 : ℝ) ^ ℓ *
      |∫ v, kinkInnerApprox ℓ z v ∂kinkCoin - ∫ v, kinkInner z v ∂kinkCoin| ≤ 1 / 8 :=
    fun ℓ => Eventually.of_forall fun z => (hweak ℓ z).le
  have hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) * ∫ p, (kinkInnerApprox (ℓ + 1) p.1 p.2 -
      kinkInnerApprox ℓ p.1 p.2) ^ 2 ∂(kinkOuter.prod kinkCoin) ≤ 1 / 256 := fun ℓ => by
    simp_rw [hstrong]
    rw [integral_const, probReal_univ, one_smul]
    have h1 : (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) ≤ 2 ^ ℓ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have := Nat.cast_nonneg (α := ℝ) ℓ; linarith)
    have h2 : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    calc (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) * (-(((2 : ℝ) ^ ℓ)⁻¹ / 16)) ^ 2
        = (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) * (((2 : ℝ) ^ ℓ)⁻¹) ^ 2 / 256 := by ring
      _ ≤ (2 : ℝ) ^ ℓ * (((2 : ℝ) ^ ℓ)⁻¹) ^ 2 / 256 := by gcongr
      _ = ((2 : ℝ) ^ ℓ)⁻¹ / 256 := by field_simp
      _ ≤ 1 / 256 := by
          gcongr
          exact inv_le_one_of_one_le₀ h2
  obtain ⟨-, hb⟩ := nested_kink_sde_bias_rate kinkOuter kinkCoin hf hm hfib hw hball ℓ
  obtain ⟨-, hv⟩ := nested_kink_sde_variance_rate kinkOuter kinkCoin hf hm hfib hw hball hs ℓ
  refine ⟨hb.trans ?_, hv.trans ?_⟩ <;> norm_num

/-- **A lower bound for the variance of the example's MIMC correction** (Giles 2015, §9.2,
p. 60: "with MIMC we would have `β₁ = β₂ = 1.5`"): for `f(x) = max(x − ½, 0)` and the inner
approximations `kinkInnerApprox`, which satisfy the hypotheses of the kink analysis
(`kinkInnerApprox_hypotheses`), the MIMC correction `Y_ℓ` (`nestedMimcDelta`) at
`ℓ = (2j + 1, ℓ₂ + 1)` with `ℓ₂ ≥ j + 1` has mean zero and `V[Y_ℓ] ≥ 2^{−(2ℓ₂ + j + 17)}`.
Mechanism: the first-order weak error shifts the kink seen by the two inner approximations by
`d = 2^{−ℓ₂}/16`, and on the event (of probability of order `2^{−j} = M^{−1/2}`) that the two
coarse inner means straddle the kink the correction is `d/2`; so `V ≈ d² M^{−1/2}`, which is not
`O(2^{−3ℓ₁/2 − 3ℓ₂/2})`. -/
theorem kinkMimc_variance_ge {j ℓ₂ : ℕ} (h : j + 1 ≤ ℓ₂) :
    ∫ p, nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (2 * j + 1) (ℓ₂ + 1) p
        ∂(nestedLaw kinkOuter kinkCoin) = 0 ∧
      ((2 : ℝ) ^ (2 * ℓ₂ + j + 17))⁻¹ ≤
        variance (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (2 * j + 1)
          (ℓ₂ + 1)) (nestedLaw kinkOuter kinkCoin) := by
  have h0 := integral_kinkMimc (2 * j) ℓ₂
  refine ⟨h0, ?_⟩
  obtain ⟨hYm, hYb⟩ := kinkMimc_bound (2 * j) ℓ₂
  have hY2 : MemLp (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (2 * j + 1)
      (ℓ₂ + 1)) 2 (nestedLaw kinkOuter kinkCoin) := by
    refine (memLp_two_iff_integrable_sq hYm.aestronglyMeasurable).2 ?_
    refine (integrable_const (1 / 16 : ℝ)).mono' (hYm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    have := hYb p
    have h0 := abs_nonneg (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox
      (2 * j + 1) (ℓ₂ + 1) p)
    nlinarith
  rw [variance_eq_sub hY2, h0]
  simp only [Pi.pow_apply]
  have := integral_sq_kinkMimc_ge h
  linarith

/-- **The MIMC rates `β₁ = β₂ = 1.5` claimed for a piecewise linear `f` are false** (Giles 2015,
§9.2, p. 60: "if the function `f` is continuous and piecewise differentiable, rather than being
twice differentiable, then in the MLMC treatment we would get `β = 1.5` … On the other hand, with
MIMC we would have `β₁ = β₂ = 1.5` and so the complexity would remain `O(ε⁻²)`").  For the example
`kinkInnerApprox` (`f(x) = max(x − ½, 0)`, `Z` uniform on `[0, 1]`, fair inner signs, first order
weak and strong errors, a small ball for `E_W[g(Z, W)]`: `kinkInnerApprox_hypotheses`), there are
no `β₁, β₂` with `2β₁ + β₂ > 3` and `C` such that the MIMC correction (`nestedMimcDelta`, the
paper's six-term `Y_ℓ`) satisfies `V[Y_{(ℓ₁+1, ℓ₂+1)}] ≤ C 2^{−β₁ℓ₁ − β₂ℓ₂}` for all `ℓ₁, ℓ₂`;
in particular not with `β₁ = β₂ = 1.5` (`nested_mimc_kink_three_halves_false`), nor with any
`β₁, β₂ > 1 = γ₁ = γ₂`, which Theorem 2 needs for the cost `O(ε⁻²)` (`mimcEta < 0`), so the
paper's conclusion does not follow from Theorem 2 either.  Proof: along `ℓ₁ = 2j`,
`ℓ₂ = j + 1` the variance is at least `2^{−(3j + 19)}` (`kinkMimc_variance_ge`), while the bound
is `C 2^{−(2β₁ + β₂) j − β₂}`.  The paper's heuristic transfers the smooth case: the kink seen by
the level-`ℓ₂` and level-`(ℓ₂ − 1)` inner approximations is shifted by their weak error
`O(2^{−ℓ₂})`, which changes the antithetic difference by `O(2^{−ℓ₂})` whenever the coarse inner
means straddle the kink, an event of probability `O(2^{−ℓ₁/2})` that does not shrink with `ℓ₂`. -/
theorem nested_mimc_kink_rates_false {β₁ β₂ : ℝ} (hβ : 3 < 2 * β₁ + β₂) :
    ¬ ∃ C : ℝ, ∀ ℓ₁ ℓ₂ : ℕ,
      variance (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1) (ℓ₂ + 1))
          (nestedLaw kinkOuter kinkCoin) ≤ C * (2 : ℝ) ^ (-(β₁ * ℓ₁ + β₂ * ℓ₂)) := by
  rintro ⟨C, hC⟩
  set δ : ℝ := 2 * β₁ + β₂ - 3 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set x : ℝ := (2 : ℝ) ^ δ with hx
  have hx1 : 1 < x := Real.one_lt_rpow (by norm_num) hδ
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (C * (2 : ℝ) ^ (19 - β₂)) hx1
  have h1 := (kinkMimc_variance_ge (j := j) (ℓ₂ := j + 1) le_rfl).2
  have h2 := hC (2 * j) (j + 1)
  set P : ℝ := (2 : ℝ) ^ (2 * (j + 1) + j + 17) with hP
  have hP0 : 0 < P := by positivity
  have hxj : 0 < x ^ j := by positivity
  have e : (2 : ℝ) ^ (-(β₁ * ((2 * j : ℕ) : ℝ) + β₂ * ((j + 1 : ℕ) : ℝ))) =
      (x ^ j)⁻¹ * (2 : ℝ) ^ (19 - β₂) * P⁻¹ := by
    rw [hx, hP, ← Real.rpow_natCast ((2 : ℝ) ^ δ) j, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (2 : ℝ) (2 * (j + 1) + j + 17), ← Real.rpow_neg (by norm_num),
      ← Real.rpow_neg (by norm_num), ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    congr 1
    rw [hδdef]
    push_cast
    ring
  rw [e] at h2
  have h3 : P⁻¹ ≤ C * ((x ^ j)⁻¹ * (2 : ℝ) ^ (19 - β₂) * P⁻¹) := h1.trans h2
  have h4 : 1 ≤ C * (2 : ℝ) ^ (19 - β₂) * (x ^ j)⁻¹ := by
    have h5 : P⁻¹ * 1 ≤ P⁻¹ * (C * (2 : ℝ) ^ (19 - β₂) * (x ^ j)⁻¹) := by
      calc P⁻¹ * 1 = P⁻¹ := mul_one _
        _ ≤ C * ((x ^ j)⁻¹ * (2 : ℝ) ^ (19 - β₂) * P⁻¹) := h3
        _ = P⁻¹ * (C * (2 : ℝ) ^ (19 - β₂) * (x ^ j)⁻¹) := by ring
    exact le_of_mul_le_mul_left h5 (inv_pos.2 hP0)
  have h6 : x ^ j ≤ C * (2 : ℝ) ^ (19 - β₂) := by
    have := mul_le_mul_of_nonneg_right h4 hxj.le
    rwa [one_mul, mul_assoc, inv_mul_cancel₀ hxj.ne', mul_one] at this
  linarith

/-- **The paper's MIMC rates `β₁ = β₂ = 1.5` for a piecewise linear `f` fail** (Giles 2015, §9.2,
p. 60: "with MIMC we would have `β₁ = β₂ = 1.5` and so the complexity would remain `O(ε⁻²)`"):
for the example `kinkInnerApprox` (`kinkInnerApprox_hypotheses`) there is no `C` with
`V[Y_{(ℓ₁+1, ℓ₂+1)}] ≤ C 2^{−1.5ℓ₁ − 1.5ℓ₂}` for all `ℓ₁, ℓ₂`; the special case
`2 · 1.5 + 1.5 > 3` of `nested_mimc_kink_rates_false`. -/
theorem nested_mimc_kink_three_halves_false :
    ¬ ∃ C : ℝ, ∀ ℓ₁ ℓ₂ : ℕ,
      variance (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1) (ℓ₂ + 1))
          (nestedLaw kinkOuter kinkCoin) ≤
        C * (2 : ℝ) ^ (-((3 / 2 : ℝ) * ℓ₁ + (3 / 2 : ℝ) * ℓ₂)) :=
  nested_mimc_kink_rates_false (by norm_num)

end MIMCKink

end MLMC
