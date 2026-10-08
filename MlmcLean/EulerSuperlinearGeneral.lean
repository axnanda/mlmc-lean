import MlmcLean.EulerSuperlinear

/-!
# Giles 2015, §5.6: explicit Euler–Maruyama diverges under HJK's super-linear growth condition

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.6 "Stiff and
highly nonlinear SDEs" (pp. 43–44), p. 44 (lines 1892–1897 of `docs/giles2015.txt`): "A related
problem is addressed by Hutzenthaler, Jentzen and Kloeden (2013), who are concerned with SDEs such
as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the volatility.
This again leads to numerical instability if a uniform timestep is used."

The survey states no theorem.  The rigorous form of "numerical instability" is the
divergence theorem of Hutzenthaler, Jentzen and Kloeden (Proc. R. Soc. A 467 (2011), 1563–1576;
their 2013 paper cited by Giles builds on it).  That paper is not in `docs/`; its hypotheses are,
for a scalar SDE `dX = a(X) dt + b(X) dW`: `max(|a(x)|, |b(x)|) ≥ |x|^β/C` and
`min(|a(x)|, |b(x)|) ≤ C|x|^α` for `|x| ≥ C`, with `β > α > 1`, and an initial value `ξ` with
`P(b(ξ) ≠ 0) > 0`; the conclusion is `E|Y_N|^p → ∞` (`p ≥ 1`) for the explicit Euler
approximations `Y_N` of `X_T` with `N` steps.  `MlmcLean/EulerSuperlinear.lean` proves this for the
paper's example `dS = −S³ dt + dW` (`emCubic_moment_tendsto_atTop`); this file proves it in general
for the scheme `emPath` (`X_{n+1} = X_n + a(X_n, t_n) h + b(X_n, t_n) √h Z_n`), with HJK's
argument.

* `hjk_abs_ge_doubleExp`, `hjk_step_ge`: if `|x| ≥ C` is large compared with `h` (in the sense of
  `hjkRadius`) and `1/2 ≤ |z| ≤ 1` (only `|z| ≤ 1` where the drift dominates), one explicit step
  gives `|x + a h + b √h z| ≥ h|x|^β/(4C)`; iterating, `|X_n|` grows doubly exponentially.
* `emPath_superlinear_abs_ge` (HJK's coefficient hypothesis) and `emPath_drift_superlinear_abs_ge`
  (drift-dominated, `|b(x)| ≤ C|x|^α`, e.g. bounded or sub-linear volatility, `b = 1`): **pathwise
  growth**: if `|b(x₀,0)| √h |z_0| ≥ hjkRadius C α β · h^{−e} + |x₀| + |a(x₀,0)|` and
  `1/2 ≤ |z_k| ≤ 1` (resp. `|z_k| ≤ 1`) for `1 ≤ k ≤ M`, then `|X_{M+1}| ≥ 2^{β^M}`.
* `emPath_superlinear_lintegral_ge`: `E|X_N|^p ≥ P(Z ≥ t_N) P(1/2 ≤ Z ≤ 1)^{N−1} (2^{β^{N−1}})^p`
  (Gaussian tail and independence; `hjk_gaussian_event_measure` is the factorisation of the
  probability of the event); `hjk_event_prob_ge`, `hjk_divergence_event_measure_ge`: that
  probability is at least `exp(−c N^{2e+1})`; `emPath_superlinear_lintegral_ge_exp`: hence
  `E|X_N|^p ≥ exp(−c N^{2e+1}) (2^{β^{N−1}})^p`.  The event has probability `exp(−Θ(N^{2e+1}))`,
  and the pathwise lemma needs `e ≥ max(1/(β−1), 1/(2(β−α)))`, so the rate `exp(−c N²)` of the
  cubic example holds only when `β ≥ 3` and `β − α ≥ 1`; for the drift `−x|x|` it is
  `exp(−Θ(N³))`, and no event of this shape does better there (`hjk_event_prob_ge`).
* `emPath_superlinear_moment_lintegral_tendsto`: **the theorem of Hutzenthaler, Jentzen and
  Kloeden**: `E|X_N|^p → ∞` in `[0, ∞]` for every `p > 0`, with no measurability or integrability
  assumption; `emPath_superlinear_payoff_lintegral_tendsto`,
  `emPath_superlinear_payoff_integral_tendsto`: the same for `E|P(X_N)|` when `|P(x)| ≥ |x|^q/D`
  for `|x| ≥ D`; `mlmc_level_payoff_lintegral_tendsto`, `mlmc_level_payoff_sq_lintegral_tendsto`:
  on level `ℓ` of an MLMC hierarchy (`N₀ 2^ℓ` steps), `E|P_ℓ| → ∞` and `E[P_ℓ²] → ∞`.
* `memLp_emPath_of_polyGrowth`, `emPath_superlinear_moment_tendsto_atTop`,
  `emPath_superlinear_integral_abs_tendsto_atTop`: for measurable, polynomially bounded
  coefficients `X_N` has moments of every order, and `E|X_N|^p → ∞`, `E|X_N| → ∞` as real numbers.
* `hjk_cubic_moment_tendsto_atTop`: the paper's example; its statement is that of
  `emCubic_moment_tendsto_atTop`, recovered as a special case (checked by `rfl` below).
  `hjk_xabs_moment_tendsto_atTop`: `dS = −S|S| dt + dW`; `hjk_ginzburgLandau_moment_tendsto_atTop`:
  the stochastic Ginzburg–Landau equation `dS = (S − S³) dt + σS dW` (multiplicative noise); these
  three are drift-dominated.  `hjk_quadVol_moment_tendsto_atTop`: `dS = −S dt + S² dW`, where the
  volatility dominates.

Deviations from HJK: any `α < β` is allowed (HJK need `α > 1`; this is no restriction, since for
`|x| ≥ max(C, 1)` a bound `C|x|^α` with `α ≤ 1` implies the bound `C|x|^{α'}` for every
`α' ∈ (1, β)`); the coefficients may depend on time (with bounds uniform in `t`); every `p > 0`
(HJK: `p ≥ 1`); the initial value is deterministic, with `b(x₀, 0) ≠ 0` (HJK: a random `ξ` with
`P(b(ξ) ≠ 0) > 0`).  The event is `{Z_0 ≥ t_N, 1/2 ≤ Z_k ≤ 1 for 1 ≤ k < N}`: the lower bound
`1/2` is needed only at points where the volatility dominates.

Not covered: several dimensions; random initial values `ξ` independent of the noise with
`P(b(ξ, 0) ≠ 0) > 0`; coefficients outside HJK's condition, e.g. `b ≡ 0` (for `dX = −X³ dt` the
explicit iterates satisfy `|X_n| ≤ |x₀|` once `h x₀² ≤ 2`) or equal growth (`a = −x³`, `b = x³`,
where no `α < β` works); HJK's comparison with the exact solution (strong and weak divergence
`E|X_T − Y_N|^p → ∞`, `|E|X_T|^p − E|Y_N|^p| → ∞`), which needs the finiteness of the moments of
the exact solution (SDE theory, not available here; given it, both follow from `E|Y_N|^p → ∞`);
the MLMC level means `E[P_ℓ − P_{ℓ−1}]` and level variances `V_ℓ` (see
`mlmc_level_payoff_sq_lintegral_tendsto`); the divergence of the MLMC Euler estimator itself, the
subject of HJK's 2013 paper cited by Giles.
-/

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal Topology

namespace MLMC

/-! ### Pathwise growth of the explicit scheme -/

/-- The doubly exponential recursion behind the divergence proof of Hutzenthaler, Jentzen and
Kloeden, Proc. R. Soc. A 467 (2011): if `γ > 0`, `β ≥ 1`, `γ|x_0| ≥ 1`, `R ≤ |x_0|` and
`(γ|x_k|)^β ≤ γ|x_{k+1}|` whenever `R ≤ |x_k|` (`k < n`), then `γ|x_n| ≥ (γ|x_0|)^{β^n}`; along the
way `|x_k|` never decreases, so the step condition keeps applying. -/
lemma hjk_abs_ge_doubleExp {β γ R : ℝ} (hβ : 1 ≤ β) (hγ : 0 < γ) {x : ℕ → ℝ} {n : ℕ}
    (hstep : ∀ k < n, R ≤ |x k| → (γ * |x k|) ^ β ≤ γ * |x (k + 1)|)
    (hR : R ≤ |x 0|) (h1 : 1 ≤ γ * |x 0|) :
    (γ * |x 0|) ^ β ^ n ≤ γ * |x n| := by
  have key : ∀ k ≤ n, (γ * |x 0|) ^ β ^ k ≤ γ * |x k| ∧ |x 0| ≤ |x k| := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hs := hstep k (by omega) (hR.trans ih2)
      have hge1 : 1 ≤ γ * |x k| := h1.trans (by gcongr)
      refine ⟨?_, ?_⟩
      · calc (γ * |x 0|) ^ β ^ (k + 1) = ((γ * |x 0|) ^ β ^ k) ^ β := by
              rw [pow_succ, Real.rpow_mul (by positivity)]
          _ ≤ (γ * |x k|) ^ β := by gcongr
          _ ≤ _ := hs
      · have : γ * |x k| ≤ γ * |x (k + 1)| :=
          calc γ * |x k| = (γ * |x k|) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (γ * |x k|) ^ β := Real.rpow_le_rpow_of_exponent_le hge1 hβ
            _ ≤ _ := hs
        exact ih2.trans (le_of_mul_le_mul_left this hγ)
  exact (key n le_rfl).1

/-- One explicit Euler–Maruyama step for a super-linear coefficient (the pathwise step of
Hutzenthaler, Jentzen and Kloeden, Proc. R. Soc. A 467 (2011)).  Let `C ≥ 1`, `0 < h ≤ 1`,
`|x| ≥ C`, `h|x|^{β−1} ≥ 8C` and `√h|x|^{β−α} ≥ 8C²`, and `|z| ≤ 1`.  If either the drift dominates
at `x` (`|x|^β ≤ C|a|`, `|b| ≤ C|x|^α`) or the volatility dominates and the noise is not small
(`|x|^β ≤ C|b|`, `|a| ≤ C|x|^α`, `|z| ≥ 1/2`), then `h|x|^β ≤ 4C|x + a h + b √h z|`: the dominant
term is at least `h|x|^β/C` (resp. `√h|x|^β/(2C)`) and each of the two others is at most an eighth
(resp. a quarter) of that bound, so the sum is at least `3h|x|^β/(4C)` (resp. `√h|x|^β/(4C)`). -/
lemma hjk_step_ge {C α β h x a b z : ℝ} (hC : 1 ≤ C) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hxC : C ≤ |x|) (hx1 : 8 * C ≤ h * |x| ^ (β - 1)) (hx2 : 8 * C ^ 2 ≤ √h * |x| ^ (β - α))
    (hcase : (|x| ^ β ≤ C * |a| ∧ |b| ≤ C * |x| ^ α) ∨
      (|x| ^ β ≤ C * |b| ∧ |a| ≤ C * |x| ^ α ∧ 1 / 2 ≤ |z|)) (hz : |z| ≤ 1) :
    h * |x| ^ β ≤ 4 * C * |x + a * h + b * √h * z| := by
  have hy0 : 0 < |x| := by linarith
  have hs0 : 0 < √h := Real.sqrt_pos.mpr hh0
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh0.le
  have hs1 : √h ≤ 1 := Real.sqrt_le_one.mpr hh1
  have hP0 : 0 < |x| ^ β := Real.rpow_pos_of_pos hy0 β
  have hQ0 : 0 < |x| ^ α := Real.rpow_pos_of_pos hy0 α
  -- `8 C |x| ≤ h |x|^β`
  have F1 : 8 * C * |x| ≤ h * |x| ^ β := by
    have e : |x| ^ β = |x| ^ (β - 1) * |x| := by
      rw [← Real.rpow_add_one hy0.ne', sub_add_cancel]
    rw [e]
    nlinarith
  -- `8 C² |x|^α ≤ √h |x|^β`
  have F2 : 8 * C ^ 2 * |x| ^ α ≤ √h * |x| ^ β := by
    have e : |x| ^ β = |x| ^ (β - α) * |x| ^ α := by
      rw [← Real.rpow_add hy0, sub_add_cancel]
    rw [e]
    nlinarith
  have htri : |a| * h ≤ |x + a * h + b * √h * z| + |x| + |b| * √h * |z| := by
    have h1 := abs_add_three (x + a * h + b * √h * z) (-x) (-(b * √h * z))
    have e : x + a * h + b * √h * z + -x + -(b * √h * z) = a * h := by ring
    rw [e, abs_neg, abs_neg, abs_mul, abs_of_pos hh0, abs_mul, abs_mul, abs_of_pos hs0] at h1
    exact h1
  have htri' : |b| * √h * |z| ≤ |x + a * h + b * √h * z| + |x| + |a| * h := by
    have h1 := abs_add_three (x + a * h + b * √h * z) (-x) (-(a * h))
    have e : x + a * h + b * √h * z + -x + -(a * h) = b * √h * z := by ring
    rw [e, abs_neg, abs_neg, abs_mul, abs_mul, abs_of_pos hs0, abs_mul, abs_of_pos hh0] at h1
    exact h1
  have hA := abs_nonneg a
  have hB := abs_nonneg b
  have hZ := abs_nonneg z
  rcases hcase with ⟨hPa, hbQ⟩ | ⟨hPb, haQ, hz1⟩
  · -- drift-dominated: `h|a| ≥ h|x|^β/C` beats `|x| + √h|b|`
    have hbz : |b| * √h * |z| ≤ |b| * √h := by
      have := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ |b| * √h)
      linarith
    have hb2 : 4 * C * (|b| * √h) ≤ h * |x| ^ β / 2 := by
      have := mul_le_mul_of_nonneg_left hbQ (by positivity : 0 ≤ 4 * C * √h)
      nlinarith
    have ha2 : 4 * h * |x| ^ β ≤ 4 * C * (|a| * h) := by nlinarith
    nlinarith
  · -- diffusion-dominated: `√h|b||z| ≥ √h|x|^β/(2C)` beats `|x| + h|a|`
    have hb2 : 2 * √h * |x| ^ β ≤ 4 * C * (|b| * √h * |z|) := by
      have := mul_le_mul_of_nonneg_left hz1 (by positivity : 0 ≤ 4 * C * |b| * √h)
      nlinarith
    have hhs : h ≤ √h := by nlinarith
    have hhP : h * |x| ^ β ≤ √h * |x| ^ β := mul_le_mul_of_nonneg_right hhs hP0.le
    have ha2 : 4 * C * (|a| * h) ≤ √h * |x| ^ β / 2 := by
      have h1 := mul_le_mul_of_nonneg_left haQ (by positivity : 0 ≤ 4 * C * h)
      have h2 : 4 * C * h * (C * |x| ^ α) ≤ h * (√h * |x| ^ β / 2) := by nlinarith
      have h3 : h * (√h * |x| ^ β / 2) ≤ √h * |x| ^ β / 2 := by
        have : 0 ≤ √h * |x| ^ β / 2 := by positivity
        nlinarith
      nlinarith
    have hx3 : 4 * C * |x| ≤ √h * |x| ^ β / 2 := by linarith
    nlinarith

/-- The explicit radius of the divergence argument of Hutzenthaler, Jentzen and Kloeden,
Proc. R. Soc. A 467 (2011) (behind Giles 2015, §5.6, p. 44):
`K(C, α, β) = C' + 2(8C')^{1/(β−1)} + (8C'²)^{1/(β−α)}` with `C' = max(C, 1)`.  A first value
`|X_1| ≥ K h^{−e}`, with `e(β − 1) ≥ 1` and `2e(β − α) ≥ 1`, is beyond the range where an explicit
step can fail to raise `|x|` to the power `β` up to a constant (`hjk_step_ge`, `hjkRadius_spec`),
and starts the doubly exponential growth. -/
noncomputable def hjkRadius (C α β : ℝ) : ℝ :=
  max C 1 + 2 * (8 * max C 1) ^ (β - 1)⁻¹ + (8 * max C 1 ^ 2) ^ (β - α)⁻¹

/-- If `y ≥ hjkRadius C α β · h^{−e}` with `0 < h ≤ 1`, `e(β − 1) ≥ 1` and `2e(β − α) ≥ 1`, then `y`
satisfies the three size conditions of `hjk_step_ge` with `C' = max(C, 1)`, the second one with the
extra factor `2^{β−1}` that gives `γy ≥ 2` for `γ = (h/(4C'))^{1/(β−1)}`. -/
lemma hjkRadius_spec {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β) {e : ℝ} (he1 : 1 ≤ e * (β - 1))
    (he2 : 1 ≤ 2 * e * (β - α)) {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) {y : ℝ}
    (hy : hjkRadius C α β * h⁻¹ ^ e ≤ y) :
    max C 1 ≤ y ∧ 8 * max C 1 * 2 ^ (β - 1) ≤ h * y ^ (β - 1) ∧
      8 * max C 1 ^ 2 ≤ √h * y ^ (β - α) := by
  set D := max C 1 with hD
  have hD1 : 1 ≤ D := le_max_right C 1
  have hb1 : 0 < β - 1 := by linarith
  have hba : 0 < β - α := by linarith
  have he : 0 < e := by nlinarith
  have hu : 1 ≤ h⁻¹ := (one_le_inv₀ hh0).mpr hh1
  have hue : 1 ≤ h⁻¹ ^ e := Real.one_le_rpow hu he.le
  have hA : 0 ≤ 2 * (8 * D) ^ (β - 1)⁻¹ := by positivity
  have hB : 0 ≤ (8 * D ^ 2) ^ (β - α)⁻¹ := by positivity
  have hK : hjkRadius C α β = D + 2 * (8 * D) ^ (β - 1)⁻¹ + (8 * D ^ 2) ^ (β - α)⁻¹ := rfl
  have hKy : hjkRadius C α β ≤ y := by
    have : hjkRadius C α β ≤ hjkRadius C α β * h⁻¹ ^ e := by
      have : 0 ≤ hjkRadius C α β := by rw [hK]; positivity
      nlinarith
    linarith
  refine ⟨by linarith, ?_, ?_⟩
  · have hw : 2 * (8 * D) ^ (β - 1)⁻¹ * h⁻¹ ^ e ≤ y := by
      have : 2 * (8 * D) ^ (β - 1)⁻¹ * h⁻¹ ^ e ≤ hjkRadius C α β * h⁻¹ ^ e :=
        mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (by positivity)
      linarith
    have hpow := Real.rpow_le_rpow (by positivity) hw hb1.le
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity), Real.rpow_inv_rpow (by positivity) hb1.ne',
      ← Real.rpow_mul (zero_le_one.trans hu)] at hpow
    have h1 : h⁻¹ ≤ h⁻¹ ^ (e * (β - 1)) := by
      calc h⁻¹ = h⁻¹ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hu he1
    have h2 : 0 < 2 ^ (β - 1) * (8 * D) := by positivity
    have h3 : 2 ^ (β - 1) * (8 * D) * h⁻¹ ≤ y ^ (β - 1) := by nlinarith
    have h4 : h * (2 ^ (β - 1) * (8 * D) * h⁻¹) = 2 ^ (β - 1) * (8 * D) := by
      field_simp
    nlinarith
  · have hw : (8 * D ^ 2) ^ (β - α)⁻¹ * h⁻¹ ^ e ≤ y := by
      have : (8 * D ^ 2) ^ (β - α)⁻¹ * h⁻¹ ^ e ≤ hjkRadius C α β * h⁻¹ ^ e :=
        mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (by positivity)
      linarith
    have hpow := Real.rpow_le_rpow (by positivity) hw hba.le
    rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_inv_rpow (by positivity) hba.ne',
      ← Real.rpow_mul (zero_le_one.trans hu)] at hpow
    have h1 : √(h⁻¹) ≤ h⁻¹ ^ (e * (β - α)) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hu (by linarith)
    have h4 : √h * √(h⁻¹) = 1 := by
      rw [← Real.sqrt_mul hh0.le, mul_inv_cancel₀ hh0.ne', Real.sqrt_one]
    have hs0 : 0 ≤ √h := Real.sqrt_nonneg h
    have h5 : 8 * D ^ 2 * √(h⁻¹) ≤ y ^ (β - α) := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * D ^ 2)
      linarith
    nlinarith

/-- The pathwise growth of `emPath` from its first value: if `|X_1|` satisfies the size conditions
of `hjk_step_ge` (with the factor `2^{β−1}`), every later step is covered by one of its two cases,
and `|z_k| ≤ 1` for `1 ≤ k ≤ M`, then `|X_{M+1}| ≥ 2^{β^M}` (`hjk_abs_ge_doubleExp` with
`γ = (h/(4C))^{1/(β−1)} ≤ 1`). -/
lemma emPath_doubleExp_core {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hC : 1 ≤ C) (hβ : 1 < β)
    (hαβ : α < β) {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) {x₀ : ℝ} {z : ℕ → ℝ} {M : ℕ}
    (hX1C : C ≤ |emPath a b h x₀ z 1|)
    (hX1a : 8 * C * 2 ^ (β - 1) ≤ h * |emPath a b h x₀ z 1| ^ (β - 1))
    (hX1b : 8 * C ^ 2 ≤ √h * |emPath a b h x₀ z 1| ^ (β - α))
    (hcase : ∀ k, 1 ≤ k → k ≤ M → ∀ y, |emPath a b h x₀ z 1| ≤ |y| →
      (|y| ^ β ≤ C * |a y (k * h)| ∧ |b y (k * h)| ≤ C * |y| ^ α) ∨
      (|y| ^ β ≤ C * |b y (k * h)| ∧ |a y (k * h)| ≤ C * |y| ^ α ∧ 1 / 2 ≤ |z k|))
    (hz : ∀ k, 1 ≤ k → k ≤ M → |z k| ≤ 1) :
    (2 : ℝ) ^ β ^ M ≤ |emPath a b h x₀ z (M + 1)| := by
  set X := emPath a b h x₀ z with hXdef
  set R := |X 1| with hR
  have hb1 : 0 < β - 1 := by linarith
  have hba : 0 < β - α := by linarith
  have hR0 : 0 < R := by linarith
  have hκ0 : 0 < h / (4 * C) := by positivity
  have hκ1 : h / (4 * C) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  set γ := (h / (4 * C)) ^ (β - 1)⁻¹ with hγ
  have hγ0 : 0 < γ := Real.rpow_pos_of_pos hκ0 _
  have hγ1 : γ ≤ 1 := Real.rpow_le_one hκ0.le hκ1 (by positivity)
  have hγβ1 : γ ^ (β - 1) = h / (4 * C) := Real.rpow_inv_rpow hκ0.le hb1.ne'
  have hγβ : γ ^ β = γ * (h / (4 * C)) := by
    rw [← hγβ1, ← Real.rpow_one_add' hγ0.le (by linarith)]
    congr 1
    ring
  have hstep : ∀ k < M, R ≤ |X (k + 1)| →
      (γ * |X (k + 1)|) ^ β ≤ γ * |X (k + 1 + 1)| := by
    intro k hk hRk
    set y := X (k + 1) with hy
    have hyC : C ≤ |y| := hX1C.trans hRk
    have hy1 : 8 * C ≤ h * |y| ^ (β - 1) := by
      have h1 : R ^ (β - 1) ≤ |y| ^ (β - 1) := Real.rpow_le_rpow hR0.le hRk hb1.le
      have h2 : 1 ≤ (2 : ℝ) ^ (β - 1) := Real.one_le_rpow (by norm_num) hb1.le
      nlinarith
    have hy2 : 8 * C ^ 2 ≤ √h * |y| ^ (β - α) := by
      have h1 : R ^ (β - α) ≤ |y| ^ (β - α) := Real.rpow_le_rpow hR0.le hRk hba.le
      have h2 : 0 ≤ √h := Real.sqrt_nonneg h
      nlinarith
    have hs := hjk_step_ge hC hh0 hh1 hyC hy1 hy2
      (hcase (k + 1) (by omega) (by omega) y hRk) (hz (k + 1) (by omega) (by omega))
    rw [← emPath_succ] at hs
    rw [Real.mul_rpow hγ0.le (abs_nonneg _), hγβ]
    have h4C : 0 < 4 * C := by positivity
    calc γ * (h / (4 * C)) * |y| ^ β = γ * (h * |y| ^ β) / (4 * C) := by ring
      _ ≤ γ * (4 * C * |X (k + 1 + 1)|) / (4 * C) := by gcongr
      _ = γ * |X (k + 1 + 1)| := by field_simp
  have h2R : 2 ≤ γ * R := by
    have h1 : (2 : ℝ) ^ (β - 1) ≤ (γ * R) ^ (β - 1) := by
      rw [Real.mul_rpow hγ0.le hR0.le, hγβ1]
      have h2 : 1 ≤ (2 : ℝ) ^ (β - 1) := Real.one_le_rpow (by norm_num) hb1.le
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    exact (Real.rpow_le_rpow_iff (by norm_num) (by positivity) hb1).mp h1
  have hg := hjk_abs_ge_doubleExp (x := fun k => X (k + 1)) (n := M) hβ.le hγ0 hstep le_rfl
    (by linarith)
  calc (2 : ℝ) ^ β ^ M ≤ (γ * R) ^ β ^ M :=
        Real.rpow_le_rpow (by norm_num) h2R (by positivity)
    _ ≤ γ * |X (M + 1)| := hg
    _ ≤ |X (M + 1)| := mul_le_of_le_one_left (abs_nonneg _) hγ1

/-- The first step of `emPath`: for `0 < h ≤ 1`, if `|b(x₀,0)| √h |z_0| ≥ L + |x₀| + |a(x₀,0)|` then
`|X_1| ≥ L`.  A large first normal increment makes the first value large, provided `b(x₀, 0) ≠ 0`.
-/
lemma emPath_one_abs_ge {a b : ℝ → ℝ → ℝ} {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) {x₀ L : ℝ}
    {z : ℕ → ℝ} (hz0 : L + |x₀| + |a x₀ 0| ≤ |b x₀ 0| * √h * |z 0|) :
    L ≤ |emPath a b h x₀ z 1| := by
  have e1 : emPath a b h x₀ z 1 = x₀ + a x₀ 0 * h + b x₀ 0 * √h * z 0 := by
    have := emPath_succ a b h x₀ z 0
    rw [Nat.cast_zero, zero_mul] at this
    exact this
  rw [e1]
  have h1 := abs_add_three (x₀ + a x₀ 0 * h + b x₀ 0 * √h * z 0) (-x₀) (-(a x₀ 0 * h))
  have e : x₀ + a x₀ 0 * h + b x₀ 0 * √h * z 0 + -x₀ + -(a x₀ 0 * h) = b x₀ 0 * √h * z 0 := by
    ring
  rw [e, abs_neg, abs_neg, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg h), abs_mul,
    abs_of_pos hh0] at h1
  have h2 : |a x₀ 0| * h ≤ |a x₀ 0| := mul_le_of_le_one_right (abs_nonneg _) hh1
  linarith

/-- **Pathwise doubly exponential growth of the explicit scheme for super-linear coefficients**
(Giles 2015, §5.6, p. 44: "SDEs such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth
in the drift and/or the volatility.  This again leads to numerical instability if a uniform timestep
is used"; the pathwise step of the divergence theorem of Hutzenthaler, Jentzen and Kloeden,
Proc. R. Soc. A 467 (2011)).  Let the coefficients satisfy HJK's growth condition: for `|x| ≥ C` and
all `t`, `|x|^β ≤ C max(|a(x,t)|, |b(x,t)|)` and `min(|a(x,t)|, |b(x,t)|) ≤ C|x|^α`, with `1 < β`,
`α < β`.  Let `0 < h ≤ 1` and `e(β − 1) ≥ 1`, `2e(β − α) ≥ 1`.  If the first normal increment is
large, `|b(x₀,0)| √h |z_0| ≥ K h^{−e} + |x₀| + |a(x₀,0)|` with `K = hjkRadius C α β`, and the next
ones satisfy `1/2 ≤ |z_k| ≤ 1` for `1 ≤ k ≤ M`, then the explicit Euler–Maruyama path
`emPath a b h x₀ z` satisfies `|X_{M+1}| ≥ 2^{β^M}`.  The lower bound `|z_k| ≥ 1/2` is used only at
points where the volatility dominates (`emPath_drift_superlinear_abs_ge` drops it when the drift
dominates everywhere).  HJK assume `α > 1`; any `α < β` is allowed here, and `C` is any real number.
-/
theorem emPath_superlinear_abs_ge {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    {e : ℝ} (he1 : 1 ≤ e * (β - 1)) (he2 : 1 ≤ 2 * e * (β - α)) {h : ℝ} (hh0 : 0 < h)
    (hh1 : h ≤ 1) {x₀ : ℝ} {z : ℕ → ℝ} {M : ℕ}
    (hz0 : hjkRadius C α β * h⁻¹ ^ e + |x₀| + |a x₀ 0| ≤ |b x₀ 0| * √h * |z 0|)
    (hz : ∀ k, 1 ≤ k → k ≤ M → 1 / 2 ≤ |z k| ∧ |z k| ≤ 1) :
    (2 : ℝ) ^ β ^ M ≤ |emPath a b h x₀ z (M + 1)| := by
  obtain ⟨hX1C, hX1a, hX1b⟩ := hjkRadius_spec hβ hαβ he1 he2 hh0 hh1
    (emPath_one_abs_ge hh0 hh1 hz0)
  refine emPath_doubleExp_core (le_max_right C 1) hβ hαβ hh0 hh1 hX1C hX1a hX1b ?_
    fun k hk1 hkM => (hz k hk1 hkM).2
  intro k hk1 hkM y hy
  have hc := hcoef y (k * h) ((le_max_left C 1).trans (hX1C.trans hy))
  have hCC : 0 ≤ max C 1 - C := by linarith [le_max_left C 1]
  rcases le_total |b y (k * h)| |a y (k * h)| with hab | hab
  · left
    rw [max_eq_left hab, min_eq_right hab] at hc
    constructor
    · nlinarith [abs_nonneg (a y (k * h))]
    · nlinarith [Real.rpow_nonneg (abs_nonneg y) α]
  · right
    rw [max_eq_right hab, min_eq_left hab] at hc
    refine ⟨?_, ?_, (hz k hk1 hkM).1⟩
    · nlinarith [abs_nonneg (b y (k * h))]
    · nlinarith [Real.rpow_nonneg (abs_nonneg y) α]

/-- **Pathwise doubly exponential growth for a super-linear drift** (Giles 2015, §5.6, p. 44: "SDEs
such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the
volatility.  This again leads to numerical instability if a uniform timestep is used"; Hutzenthaler,
Jentzen and Kloeden, Proc. R. Soc. A 467 (2011)).  The drift-dominated case of
`emPath_superlinear_abs_ge`: if `|x|^β ≤ C|a(x,t)|` and `|b(x,t)| ≤ C|x|^α` for `|x| ≥ C` (`1 < β`,
`α < β`; e.g. a bounded volatility such as `b = 1`, with `α = 0`, or a sub-linear one), `0 < h ≤ 1`,
`e(β − 1) ≥ 1`, `2e(β − α) ≥ 1`, the first increment is large,
`|b(x₀,0)| √h |z_0| ≥ K h^{−e} + |x₀| + |a(x₀,0)|` with `K = hjkRadius C α β`, and `|z_k| ≤ 1` for
`1 ≤ k ≤ M`, then `|X_{M+1}| ≥ 2^{β^M}`.  For `dS = −S³ dt + dW` this is `emCubic_abs_ge` with
another threshold for `z_0`. -/
theorem emPath_drift_superlinear_abs_ge {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β)
    (hαβ : α < β) (hcoef : ∀ x t, C ≤ |x| → |x| ^ β ≤ C * |a x t| ∧ |b x t| ≤ C * |x| ^ α)
    {e : ℝ} (he1 : 1 ≤ e * (β - 1)) (he2 : 1 ≤ 2 * e * (β - α)) {h : ℝ} (hh0 : 0 < h)
    (hh1 : h ≤ 1) {x₀ : ℝ} {z : ℕ → ℝ} {M : ℕ}
    (hz0 : hjkRadius C α β * h⁻¹ ^ e + |x₀| + |a x₀ 0| ≤ |b x₀ 0| * √h * |z 0|)
    (hz : ∀ k, 1 ≤ k → k ≤ M → |z k| ≤ 1) :
    (2 : ℝ) ^ β ^ M ≤ |emPath a b h x₀ z (M + 1)| := by
  obtain ⟨hX1C, hX1a, hX1b⟩ := hjkRadius_spec hβ hαβ he1 he2 hh0 hh1
    (emPath_one_abs_ge hh0 hh1 hz0)
  refine emPath_doubleExp_core (le_max_right C 1) hβ hαβ hh0 hh1 hX1C hX1a hX1b ?_ hz
  intro k _ _ y hy
  have hc := hcoef y (k * h) ((le_max_left C 1).trans (hX1C.trans hy))
  have hCC : 0 ≤ max C 1 - C := by linarith [le_max_left C 1]
  left
  constructor
  · nlinarith [abs_nonneg (a y (k * h))]
  · nlinarith [Real.rpow_nonneg (abs_nonneg y) α]

/-! ### The divergence event and the lower bound for the moments -/

/-- The probability of the divergence event factorises (the probabilistic step of the divergence
proof of Hutzenthaler, Jentzen and Kloeden, Proc. R. Soc. A 467 (2011)): if `Z_0, …, Z_M` are
independent with law `N(0, 1)`, the event `E = {Z_0 ∈ s₀, Z_k ∈ s for 1 ≤ k ≤ M}` is
null-measurable (the `Z_k` have a law) and `μ(E) = P(Z ∈ s₀) P(Z ∈ s)^M` for `Z ∼ N(0, 1)`. -/
lemma hjk_gaussian_event_measure {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {M : ℕ}
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n < M + 1, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin (M + 1) => Z n) μ) {s₀ s : Set ℝ} (hs₀ : MeasurableSet s₀)
    (hs : MeasurableSet s) :
    NullMeasurableSet {ω | Z 0 ω ∈ s₀ ∧ ∀ k, 1 ≤ k → k ≤ M → Z k ω ∈ s} μ ∧
      μ {ω | Z 0 ω ∈ s₀ ∧ ∀ k, 1 ≤ k → k ≤ M → Z k ω ∈ s} =
        gaussianReal 0 1 s₀ * gaussianReal 0 1 s ^ M := by
  have hm : ∀ n < M + 1, AEMeasurable (Z n) μ := fun n hn =>
    aemeasurable_of_map_eq_gaussianReal (hZ n hn)
  let S : Fin (M + 1) → Set ℝ := fun i => if (i : ℕ) = 0 then s₀ else s
  have hSm : ∀ i, MeasurableSet (S i) := fun i => by
    simp only [S]
    split_ifs
    exacts [hs₀, hs]
  have hEq : {ω | Z 0 ω ∈ s₀ ∧ ∀ k, 1 ≤ k → k ≤ M → Z k ω ∈ s} =
      ⋂ i ∈ (Finset.univ : Finset (Fin (M + 1))), (fun n : Fin (M + 1) => Z n) i ⁻¹' S i := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_univ, Set.mem_preimage,
      forall_const]
    constructor
    · rintro ⟨h0, hk⟩ i
      show Z i ω ∈ (if (i : ℕ) = 0 then s₀ else s)
      by_cases hi : (i : ℕ) = 0
      · rw [if_pos hi, hi]
        exact h0
      · rw [if_neg hi]
        exact hk i (Nat.one_le_iff_ne_zero.mpr hi) (Nat.lt_succ_iff.mp i.2)
    · intro h
      refine ⟨by simpa [S] using h 0, fun k hk1 hkM => ?_⟩
      have := h ⟨k, by omega⟩
      have hk0 : k ≠ 0 := by omega
      simpa [S, hk0] using this
  refine ⟨by rw [hEq]; exact Finset.nullMeasurableSet_biInter _ fun i _ =>
    (hm i i.2).nullMeasurableSet_preimage (hSm i), ?_⟩
  have h1 := hind.measure_inter_preimage_eq_mul Finset.univ (sets := S) (fun i _ => hSm i)
  have h2 : ∀ i : Fin (M + 1), μ (Z i ⁻¹' S i) = gaussianReal 0 1 (S i) := fun i => by
    rw [← hZ i i.2, Measure.map_apply_of_aemeasurable (hm i i.2) (hSm i)]
  rw [hEq, h1]
  simp only [h2, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, S, if_true,
    Nat.add_one_ne_zero, if_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The probabilistic step of the divergence proof: if `Z_0, …, Z_M` are independent with law
`N(0, 1)` and `F ≥ v` on the event `{Z_0 ∈ s₀, Z_k ∈ s for 1 ≤ k ≤ M}`, then
`∫⁻ F dμ ≥ P(Z ∈ s₀) P(Z ∈ s)^M v` for `Z ∼ N(0, 1)` (`hjk_gaussian_event_measure`).  No
measurability of `F` is needed (the lower Lebesgue integral is monotone). -/
lemma hjk_gaussian_event_le_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {M : ℕ}
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n < M + 1, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin (M + 1) => Z n) μ) {s₀ s : Set ℝ} (hs₀ : MeasurableSet s₀)
    (hs : MeasurableSet s) (F : Ω → ℝ≥0∞) (v : ℝ≥0∞)
    (hF : ∀ ω, Z 0 ω ∈ s₀ → (∀ k, 1 ≤ k → k ≤ M → Z k ω ∈ s) → v ≤ F ω) :
    gaussianReal 0 1 s₀ * gaussianReal 0 1 s ^ M * v ≤ ∫⁻ ω, F ω ∂μ := by
  obtain ⟨hEm, hμE⟩ := hjk_gaussian_event_measure Z hZ hind hs₀ hs
  set E := {ω | Z 0 ω ∈ s₀ ∧ ∀ k, 1 ≤ k → k ≤ M → Z k ω ∈ s}
  calc gaussianReal 0 1 s₀ * gaussianReal 0 1 s ^ M * v
      = ∫⁻ ω, E.indicator (fun _ => v) ω ∂μ := by
        rw [lintegral_indicator_const₀ hEm, hμE, mul_comm]
    _ ≤ ∫⁻ ω, F ω ∂μ := lintegral_mono fun ω => by
        by_cases hω : ω ∈ E
        · rw [Set.indicator_of_mem hω]
          exact hF ω hω.1 hω.2
        · rw [Set.indicator_of_notMem hω]
          exact zero_le

/-- The lower bound of `emPath_superlinear_lintegral_ge` for a general functional `F` of `X_N`,
under HJK's growth condition: if `F(x) ≥ v` whenever `|x| ≥ 2^{β^{N−1}}`, then
`∫⁻ F(X_N) dμ ≥ P(Z ≥ t_N) P(1/2 ≤ Z ≤ 1)^{N−1} v`. -/
lemma emPath_superlinear_le_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    {e : ℝ} (he1 : 1 ≤ e * (β - 1)) (he2 : 1 ≤ 2 * e * (β - α)) {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0)
    {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : T ≤ N) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1) (hind : iIndepFun (fun n : Fin N => Z n) μ)
    (F : ℝ → ℝ≥0∞) (v : ℝ≥0∞) (hF : ∀ x, (2 : ℝ) ^ β ^ (N - 1) ≤ |x| → v ≤ F x) :
    gaussianReal 0 1 (Set.Ici ((hjkRadius C α β * (N / T) ^ e + |x₀| + |a x₀ 0|) /
        (|b x₀ 0| * √(T / N)))) * gaussianReal 0 1 (Set.Icc (1 / 2) 1) ^ (N - 1) * v ≤
      ∫⁻ ω, F (emPath a b (T / N) x₀ (fun n => Z n ω) N) ∂μ := by
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) < N := hT.trans_le hN
    exact_mod_cast this
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hF ⊢
  set h := T / ((M + 1 : ℕ) : ℝ) with hh
  have hN' : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have hh0 : 0 < h := div_pos hT hN'
  have hh1 : h ≤ 1 := (div_le_one hN').mpr hN
  have hb0' : 0 < |b x₀ 0| * √h := mul_pos (abs_pos.mpr hb0) (Real.sqrt_pos.mpr hh0)
  have hinv : h⁻¹ = ((M + 1 : ℕ) : ℝ) / T := by rw [hh, inv_div]
  refine hjk_gaussian_event_le_lintegral Z hZ hind measurableSet_Ici measurableSet_Icc _ v ?_
  intro ω hz0 hzk
  apply hF
  refine emPath_superlinear_abs_ge hβ hαβ hcoef he1 he2 hh0 hh1 ?_ ?_
  · rw [hinv]
    have := (Set.mem_Ici.mp hz0).trans (le_abs_self _)
    rw [div_le_iff₀ hb0'] at this
    linarith
  · intro k hk1 hkM
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp (hzk k hk1 hkM)
    exact ⟨h1.trans (le_abs_self _), abs_le.mpr ⟨by linarith, h2⟩⟩

/-- **An explicit lower bound for the moments of the explicit scheme** (Giles 2015, §5.6, p. 44:
"SDEs such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the
volatility.  This again leads to numerical instability if a uniform timestep is used"; the argument
of Hutzenthaler, Jentzen and Kloeden, Proc. R. Soc. A 467 (2011)).  Under HJK's growth condition (as
in `emPath_superlinear_abs_ge`), with `b(x₀, 0) ≠ 0`, `T > 0`, `N ≥ T` steps of size `h = T/N`,
`p ≥ 0`, `e(β − 1) ≥ 1`, `2e(β − α) ≥ 1`, and `Z_0, …, Z_{N−1}` independent with law `N(0, 1)`
(Brownian increments `√h Z_n`): `E|X_N|^p ≥ P(Z ≥ t_N) · P(1/2 ≤ Z ≤ 1)^{N−1} · (2^{β^{N−1}})^p`
with `t_N = (K (N/T)^e + |x₀| + |a(x₀,0)|)/(|b(x₀,0)| √(T/N))`, `K = hjkRadius C α β`, and
`Z ∼ N(0, 1)`.  On the event `{Z_0 ≥ t_N, 1/2 ≤ Z_k ≤ 1 for 1 ≤ k < N}` one has
`|X_N| ≥ 2^{β^{N−1}}` (`emPath_superlinear_abs_ge`), and its probability factorises by independence.
The expectation is the lower Lebesgue integral in `[0, ∞]`, so no measurability or integrability of
`X_N` is assumed; `hjk_event_prob_ge` bounds the probability below by `exp(−c N^{2e+1})`.
Measurability of the `Z_n` and that `μ` is a probability measure follow from the laws. -/
theorem emPath_superlinear_lintegral_ge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    {e : ℝ} (he1 : 1 ≤ e * (β - 1)) (he2 : 1 ≤ 2 * e * (β - α)) {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0)
    {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 0 ≤ p) {N : ℕ} (hN : T ≤ N) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1) (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    gaussianReal 0 1 (Set.Ici ((hjkRadius C α β * (N / T) ^ e + |x₀| + |a x₀ 0|) /
        (|b x₀ 0| * √(T / N)))) * gaussianReal 0 1 (Set.Icc (1 / 2) 1) ^ (N - 1) *
        ENNReal.ofReal (((2 : ℝ) ^ β ^ (N - 1)) ^ p) ≤
      ∫⁻ ω, ENNReal.ofReal (|emPath a b (T / N) x₀ (fun n => Z n ω) N| ^ p) ∂μ :=
  emPath_superlinear_le_lintegral hβ hαβ hcoef he1 he2 hb0 hT hN Z hZ hind
    (fun x => ENNReal.ofReal (|x| ^ p)) _ fun _ hx =>
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hx hp)

/-- **The probability of the divergence event is at least `exp(−c N^{2e+1})`** (Giles 2015,
§5.6, p. 44: "This again leads to numerical instability if a uniform timestep is used"; the event of
Hutzenthaler, Jentzen and Kloeden, Proc. R. Soc. A 467 (2011)).  For `K, B ≥ 0`, `c₀ > 0`, `T > 0`
and `e ≥ 0` there is `c ≥ 0` such that `P(Z ≥ t_N) · P(1/2 ≤ Z ≤ 1)^{N−1} ≥ exp(−c N^{2e+1})` for
every `N ≥ 1`, where `t_N = (K (N/T)^e + B)/(c₀ √(T/N))` and `Z ∼ N(0, 1)`: `t_N + 1 ≤ A N^{e+1/2}`
and `P(Z ≥ t) ≥ e^{−(t+1)²/2}/√(2π)` (`le_gaussianReal_real_Ici`).  With `K = hjkRadius C α β`,
`B = |x₀| + |a(x₀,0)|` and `c₀ = |b(x₀,0)|` this is the probability of the event of
`emPath_superlinear_lintegral_ge`; for the paper's example `dS = −S³ dt + dW` (`β = 3`, `α = 0`,
`e = 1/2`) the bound is `exp(−c N²)`, as in `emCubic_moment_ge`.  The exponent `2e + 1` is sharp
for this event: `P(Z ≥ t) ≤ e^{−t²/2}` and `t_N ≥ (K/c₀)(N/T)^{e+1/2}`, so for `K > 0` it has
probability `exp(−Θ(N^{2e+1}))`, and `exp(−c N²)` holds only when `e ≤ 1/2`, i.e. (with the `e` of
`emPath_superlinear_abs_ge`) `β ≥ 3` and `β − α ≥ 1`.  For the drift `−x|x|` (`β = 2`) with
`b = 1` no event of this shape does better: while `h|x| ≤ 2` an explicit step with `|z| ≤ 1` raises
`|x|` by at most `√h`, so the path can only take off if `|X_1| ≳ 2/h`, i.e. `|Z_0| ≳ 2(N/T)^{3/2}`,
which has probability `exp(−Θ(N³))`. -/
theorem hjk_event_prob_ge {K B c₀ T e : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hc₀ : 0 < c₀)
    (hT : 0 < T) (he : 0 ≤ e) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ N : ℕ, 1 ≤ N →
      ENNReal.ofReal (Real.exp (-c * (N : ℝ) ^ (2 * e + 1))) ≤
        gaussianReal 0 1 (Set.Ici ((K * (N / T) ^ e + B) / (c₀ * √(T / N)))) *
          gaussianReal 0 1 (Set.Icc (1 / 2) 1) ^ (N - 1) := by
  set q := (gaussianReal 0 1).real (Set.Icc (1 / 2) 1) with hq
  have hq0 : 0 < q := by
    refine lt_of_lt_of_le ?_ (le_gaussianReal_real_Icc (1 / 2) 1)
    positivity
  set A₀ := (K / T ^ e + B) / (c₀ * √T) with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  set l := Real.log √(2 * π) with hl
  have hπ : 1 ≤ √(2 * π) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.two_le_pi]
  have hl0 : 0 ≤ l := Real.log_nonneg hπ
  refine ⟨(A₀ + 1) ^ 2 / 2 + l + |Real.log q|, by positivity, fun N hN => ?_⟩
  set n : ℝ := (N : ℝ) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast hN
  have hn0 : 0 < n := by linarith
  set X := n ^ (2 * e + 1) with hX
  have hnX : n ≤ X := by
    calc n = n ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ X := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  set t := (K * (n / T) ^ e + B) / (c₀ * √(T / n)) with ht
  have hne : 1 ≤ n ^ e := Real.one_le_rpow hn1 he
  have hsn : 1 ≤ √n := by rw [Real.one_le_sqrt]; exact hn1
  set Y := n ^ e * √n with hY
  have hY1 : 1 ≤ Y := by nlinarith
  have hY2 : Y ^ 2 = X := by
    rw [hY, mul_pow, Real.sq_sqrt hn0.le, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, hX,
      ← Real.rpow_add_one hn0.ne']
    norm_num
    ring_nf
  have ht0 : 0 ≤ t := by positivity
  have htY : t ≤ A₀ * Y := by
    have hsT : 0 < √T := Real.sqrt_pos.mpr hT
    have hTe : 0 < T ^ e := Real.rpow_pos_of_pos hT e
    have hsn0 : 0 < √n := by linarith
    have e1 : t = (K * n ^ e / T ^ e + B) * (√n / (c₀ * √T)) := by
      rw [ht, Real.div_rpow hn0.le hT.le, Real.sqrt_div' _ hn0.le]
      field_simp
    have e2 : A₀ * Y = (K / T ^ e + B) * n ^ e * (√n / (c₀ * √T)) := by
      rw [hA₀, hY]
      field_simp
    have h1 : K * n ^ e / T ^ e + B ≤ (K / T ^ e + B) * n ^ e := by
      have := mul_le_mul_of_nonneg_left hne hB
      rw [add_mul, div_mul_eq_mul_div]
      linarith
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have ht1 : (t + 1) ^ 2 ≤ (A₀ + 1) ^ 2 * X := by
    rw [← hY2, ← mul_pow]
    have : t + 1 ≤ (A₀ + 1) * Y := by nlinarith
    exact pow_le_pow_left₀ (by positivity) this 2
  -- the first factor
  have hG1 : Real.exp (-((A₀ + 1) ^ 2 / 2 + l) * X) ≤ (gaussianReal 0 1).real (Set.Ici t) := by
    have h := le_gaussianReal_real_Ici t
    rw [abs_of_nonneg ht0] at h
    refine le_trans ?_ h
    rw [← Real.exp_log (by positivity : (0 : ℝ) < √(2 * π)), ← Real.exp_sub, ← hl]
    apply Real.exp_le_exp.mpr
    nlinarith
  -- the other factors
  have hG2 : Real.exp (-|Real.log q| * X) ≤ q ^ (N - 1) := by
    rw [show q ^ (N - 1) = Real.exp ((N - 1 : ℕ) * Real.log q) by
      rw [Real.exp_nat_mul, Real.exp_log hq0]]
    apply Real.exp_le_exp.mpr
    have hN1 : ((N - 1 : ℕ) : ℝ) ≤ X := by
      have : ((N - 1 : ℕ) : ℝ) ≤ n := by rw [hn]; exact_mod_cast Nat.sub_le N 1
      linarith
    have := neg_abs_le (Real.log q)
    have hq1 : Real.log q ≤ 0 := Real.log_nonpos hq0.le (by
      rw [hq]; exact measureReal_le_one)
    rw [abs_of_nonpos hq1]
    nlinarith
  have hfin : ∀ s : Set ℝ, gaussianReal 0 1 s = ENNReal.ofReal ((gaussianReal 0 1).real s) :=
    fun s => (ofReal_measureReal).symm
  rw [hfin, hfin, ← ENNReal.ofReal_pow hq0.le, ← ENNReal.ofReal_mul measureReal_nonneg]
  apply ENNReal.ofReal_le_ofReal
  calc Real.exp (-((A₀ + 1) ^ 2 / 2 + l + |Real.log q|) * X)
      = Real.exp (-((A₀ + 1) ^ 2 / 2 + l) * X) * Real.exp (-|Real.log q| * X) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ (gaussianReal 0 1).real (Set.Ici t) * q ^ (N - 1) :=
        mul_le_mul hG1 hG2 (by positivity) measureReal_nonneg

/-- **The probability of the divergence event in `Ω`** (Giles 2015, §5.6, p. 44: "This again leads
to numerical instability if a uniform timestep is used"; the event of Hutzenthaler, Jentzen and
Kloeden, Proc. R. Soc. A 467 (2011)).  For `K, B ≥ 0`, `c₀ > 0`, `T > 0` and `e ≥ 0` there is
`c ≥ 0` such that for every `N ≥ 1` and all independent `Z_0, …, Z_{N−1}` with law `N(0, 1)`,
`μ{Z_0 ≥ t_N, 1/2 ≤ Z_k ≤ 1 for 1 ≤ k < N} ≥ exp(−c N^{2e+1})` with
`t_N = (K (N/T)^e + B)/(c₀ √(T/N))`; `c` depends neither on `N` nor on the `Z_k`.  The event is
null-measurable and its probability is `P(Z ≥ t_N) P(1/2 ≤ Z ≤ 1)^{N−1}`
(`hjk_gaussian_event_measure`), which `hjk_event_prob_ge` bounds.  With `K = hjkRadius C α β`,
`B = |x₀| + |a(x₀,0)|`, `c₀ = |b(x₀,0)|` and `N ≥ T`, on this event `|X_N| ≥ 2^{β^{N−1}}`
(`emPath_superlinear_abs_ge` with `h = T/N`). -/
theorem hjk_divergence_event_measure_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K B c₀ T e : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hc₀ : 0 < c₀) (hT : 0 < T) (he : 0 ≤ e) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ N : ℕ, 1 ≤ N → ∀ Z : ℕ → Ω → ℝ,
      (∀ n < N, μ.map (Z n) = gaussianReal 0 1) → iIndepFun (fun n : Fin N => Z n) μ →
      ENNReal.ofReal (Real.exp (-c * (N : ℝ) ^ (2 * e + 1))) ≤
        μ {ω | (K * (N / T) ^ e + B) / (c₀ * √(T / N)) ≤ Z 0 ω ∧
          ∀ k, 1 ≤ k → k < N → 1 / 2 ≤ Z k ω ∧ Z k ω ≤ 1} := by
  obtain ⟨c, hc0, hc⟩ := hjk_event_prob_ge hK hB hc₀ hT he
  refine ⟨c, hc0, fun N hN Z hZ hind => ?_⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  refine (hc (M + 1) hN).trans (le_of_eq ?_)
  rw [Nat.add_sub_cancel, ← (hjk_gaussian_event_measure Z hZ hind measurableSet_Ici
    measurableSet_Icc).2]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_Ici, Set.mem_Icc, Nat.lt_succ_iff]

/-- **An explicit lower bound `exp(−c N^{2e+1}) (2^{β^{N−1}})^p` for the moments of the explicit
scheme** (Giles 2015, §5.6, p. 44: "SDEs such as `dS_t = −S_t³ dt + dW_t`, which have a
super-linear growth in the drift and/or the volatility.  This again leads to numerical instability
if a uniform timestep is used"; the argument of Hutzenthaler, Jentzen and Kloeden,
Proc. R. Soc. A 467 (2011)).  Under HJK's growth condition (as in `emPath_superlinear_abs_ge`), with
`b(x₀, 0) ≠ 0`, `T > 0`, `e(β − 1) ≥ 1` and `2e(β − α) ≥ 1`, there is `c ≥ 0` such that for every
`p ≥ 0`, every `N ≥ T` and all independent `Z_0, …, Z_{N−1}` with law `N(0, 1)`, the explicit
scheme with `h = T/N` satisfies `E|X_N|^p ≥ exp(−c N^{2e+1}) (2^{β^{N−1}})^p` (lower Lebesgue
integral in `[0, ∞]`; `c` depends neither on `p`, `N` nor on the `Z_k`):
`emPath_superlinear_lintegral_ge` and `hjk_event_prob_ge`.  For the paper's example (`β = 3`,
`α = 0`, `e = 1/2`) this is `exp(p 3^{N−1} log 2 − c N²)`; `emCubic_moment_ge` has
`exp(p 2^{N−1} log 2 − O(N²))`. -/
theorem emPath_superlinear_lintegral_ge_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    {e : ℝ} (he1 : 1 ≤ e * (β - 1)) (he2 : 1 ≤ 2 * e * (β - α)) {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0)
    {T : ℝ} (hT : 0 < T) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p : ℝ, 0 ≤ p → ∀ N : ℕ, T ≤ N → ∀ Z : ℕ → Ω → ℝ,
      (∀ n < N, μ.map (Z n) = gaussianReal 0 1) → iIndepFun (fun n : Fin N => Z n) μ →
      ENNReal.ofReal (Real.exp (-c * (N : ℝ) ^ (2 * e + 1)) * ((2 : ℝ) ^ β ^ (N - 1)) ^ p) ≤
        ∫⁻ ω, ENNReal.ofReal (|emPath a b (T / N) x₀ (fun n => Z n ω) N| ^ p) ∂μ := by
  have he : 0 ≤ e := by nlinarith
  have hK : 0 ≤ hjkRadius C α β := by unfold hjkRadius; positivity
  obtain ⟨c, hc0, hc⟩ := hjk_event_prob_ge hK (by positivity : 0 ≤ |x₀| + |a x₀ 0|)
    (abs_pos.mpr hb0) hT he
  refine ⟨c, hc0, fun p hp N hN Z hZ hind => ?_⟩
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) < N := hT.trans_le hN
    exact_mod_cast this
  have hP := hc N hN1
  rw [← add_assoc] at hP
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact (mul_le_mul_left hP _).trans
    (emPath_superlinear_lintegral_ge hβ hαβ hcoef he1 he2 hb0 hT hp hN Z hZ hind)

/-! ### Divergence of the moments and of the payoffs -/

/-- A double exponential beats a polynomial: `c₁ β^M − c₂ (M + 1)^j − c₃ → ∞` as `M → ∞`, for
`β > 1` and `c₁ > 0`. -/
lemma hjk_tendsto_mul_pow_sub_poly {β : ℝ} (hβ : 1 < β) {c₁ : ℝ} (hc₁ : 0 < c₁) (c₂ c₃ : ℝ)
    (j : ℕ) : Tendsto (fun M : ℕ => c₁ * β ^ M - c₂ * ((M : ℝ) + 1) ^ j - c₃) atTop atTop := by
  have hβ0 : 0 < β := by linarith
  have key : ∀ i : ℕ, Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ i / β ^ M) atTop (𝓝 0) := by
    intro i
    have h := ((tendsto_pow_const_div_const_pow_of_one_lt i hβ).comp
      (tendsto_add_atTop_nat 1)).const_mul β
    rw [mul_zero] at h
    refine h.congr fun M => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hB := ((tendsto_const_nhds (x := c₁)).sub ((key j).const_mul c₂)).sub
    ((key 0).const_mul c₃)
  simp only [mul_zero, sub_zero] at hB
  refine ((tendsto_pow_atTop_atTop_of_one_lt hβ).atTop_mul_pos hc₁ hB).congr fun M => ?_
  have : (0 : ℝ) < β ^ M := pow_pos hβ0 M
  field_simp

/-- The lower bound of the divergence proof tends to infinity:
`exp(−c N^{2e+1}) (2^{β^{N−1}})^q / D → ∞` for `β > 1`, `c ≥ 0`, `q > 0`, `D > 0`. -/
lemma tendsto_hjk_lower {β : ℝ} (hβ : 1 < β) {c e q D : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (hD : 0 < D) :
    Tendsto (fun N : ℕ => Real.exp (-c * (N : ℝ) ^ (2 * e + 1)) * ((2 : ℝ) ^ β ^ (N - 1)) ^ q / D)
      atTop atTop := by
  rw [← tendsto_add_atTop_iff_nat 1]
  set j := ⌈2 * e + 1⌉₊
  have hg := hjk_tendsto_mul_pow_sub_poly hβ (by positivity : 0 < Real.log 2 * q) c (Real.log D) j
  refine tendsto_atTop_mono (fun M => ?_) (Real.tendsto_exp_atTop.comp hg)
  simp only [Function.comp_apply, Nat.add_sub_cancel]
  have hM1 : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 M
  have hpow : ((M + 1 : ℕ) : ℝ) ^ (2 * e + 1) ≤ ((M : ℝ) + 1) ^ j := by
    rw [← Real.rpow_natCast]
    push_cast
    exact Real.rpow_le_rpow_of_exponent_le (by push_cast at hM1; linarith) (Nat.le_ceil _)
  have e1 : ((2 : ℝ) ^ β ^ M) ^ q = Real.exp (Real.log 2 * q * β ^ M) := by
    rw [← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  rw [e1, div_eq_mul_inv, show D⁻¹ = Real.exp (-Real.log D) by rw [Real.exp_neg, Real.exp_log hD],
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- An explicit real lower bound behind the divergence of `E|P(X_N)|`, for a payoff with
`|x|^q ≤ D|P(x)|` when `|x| ≥ D`: eventually
`E|P(X_N)| ≥ exp(−c N^{2e+1}) (2^{β^{N−1}})^q / max(D, 1)`, with `e = max(1/(β−1), 1/(2(β−α)))`, and
this bound tends to infinity. -/
lemma exists_payoff_lower {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0) {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} {q D : ℝ} (hq : 0 < q)
    (hg : ∀ x, D ≤ |x| → |x| ^ q ≤ D * |g x|) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    ∃ Λ : ℕ → ℝ, Tendsto Λ atTop atTop ∧ ∀ᶠ N in atTop, ENNReal.ofReal (Λ N) ≤
      ∫⁻ ω, ENNReal.ofReal |g (emPath a b (T / N) x₀ (fun n => Z N n ω) N)| ∂μ := by
  set e := max (β - 1)⁻¹ (2 * (β - α))⁻¹ with he
  have hb1 : 0 < β - 1 := by linarith
  have hba : 0 < 2 * (β - α) := by linarith
  have he1 : 1 ≤ e * (β - 1) := by
    have : (β - 1)⁻¹ * (β - 1) ≤ e * (β - 1) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hb1.le
    rwa [inv_mul_cancel₀ hb1.ne'] at this
  have he2 : 1 ≤ 2 * e * (β - α) := by
    have : (2 * (β - α))⁻¹ * (2 * (β - α)) ≤ e * (2 * (β - α)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hba.le
    rw [inv_mul_cancel₀ hba.ne'] at this
    linarith
  have he0 : 0 ≤ e := le_max_of_le_left (inv_nonneg.mpr hb1.le)
  have hK : 0 ≤ hjkRadius C α β := by unfold hjkRadius; positivity
  obtain ⟨c, hc0, hc⟩ := hjk_event_prob_ge hK (by positivity : 0 ≤ |x₀| + |a x₀ 0|)
    (abs_pos.mpr hb0) hT he0
  set D' := max D 1 with hD'
  have hD'0 : 0 < D' := lt_of_lt_of_le one_pos (le_max_right D 1)
  refine ⟨fun N => Real.exp (-c * (N : ℝ) ^ (2 * e + 1)) * ((2 : ℝ) ^ β ^ (N - 1)) ^ q / D',
    tendsto_hjk_lower hβ hc0 hq hD'0, ?_⟩
  have hV : Tendsto (fun N : ℕ => (2 : ℝ) ^ β ^ (N - 1)) atTop atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 2 one_lt_two).comp
      ((tendsto_pow_atTop_atTop_of_one_lt hβ).comp (tendsto_sub_atTop_nat 1))
  filter_upwards [hV.eventually_ge_atTop D', eventually_ge_atTop ⌈T⌉₊,
    eventually_ge_atTop 1] with N hND hNT hN1
  have hTN : T ≤ N := (Nat.le_ceil T).trans (by exact_mod_cast hNT)
  set V := (2 : ℝ) ^ β ^ (N - 1) with hVdef
  have hV0 : 0 ≤ V := by positivity
  have hP := hc N hN1
  rw [← add_assoc] at hP
  rw [mul_div_assoc, ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine (mul_le_mul_left hP _).trans ?_
  refine emPath_superlinear_le_lintegral hβ hαβ hcoef he1 he2 hb0 hT hTN (Z N) (hZ N) (hind N)
    (fun x => ENNReal.ofReal |g x|) _ fun x hx => ENNReal.ofReal_le_ofReal ?_
  have hxD : D ≤ |x| := (le_max_left D 1).trans (hND.trans hx)
  have h1 : V ^ q ≤ |x| ^ q := Real.rpow_le_rpow hV0 hx hq.le
  have h2 : D * |g x| ≤ D' * |g x| := mul_le_mul_of_nonneg_right (le_max_left D 1) (abs_nonneg _)
  rw [div_le_iff₀ hD'0, mul_comm]
  linarith [hg x hxD]

/-- **The expected payoff of the explicit scheme diverges** (Giles 2015, §5.6, p. 44: "SDEs such as
`dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the volatility.  This
again leads to numerical instability if a uniform timestep is used"; Hutzenthaler, Jentzen and
Kloeden, Proc. R. Soc. A 467 (2011)).  Under HJK's growth condition on the coefficients
(`|x|^β ≤ C max(|a|, |b|)`, `min(|a|, |b|) ≤ C|x|^α` for `|x| ≥ C`, `1 < β`, `α < β`), with
`b(x₀, 0) ≠ 0` and `T > 0`: if for each `N` the variables `Z_{N,0}, …, Z_{N,N−1}` are independent
with law `N(0, 1)` (the couplings across `N` are arbitrary), then for every payoff with
`|x|^q ≤ D|P(x)|` for `|x| ≥ D` (`q > 0`; e.g. `P(x) = x²` or `|x|`), `E|P(X_N)| → ∞` as `N → ∞` for
the explicit scheme with `h = T/N`, in `[0, ∞]` and without measurability assumptions.  One-sided
payoffs such as a call are not covered: the sign of `X_N` on the divergence event is not controlled.
-/
theorem emPath_superlinear_payoff_lintegral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0) {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} {q D : ℝ} (hq : 0 < q)
    (hg : ∀ x, D ≤ |x| → |x| ^ q ≤ D * |g x|) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    Tendsto (fun N : ℕ => ∫⁻ ω, ENNReal.ofReal |g (emPath a b (T / N) x₀
      (fun n => Z N n ω) N)| ∂μ) atTop (𝓝 ∞) := by
  obtain ⟨Λ, hΛ, hev⟩ := exists_payoff_lower hβ hαβ hcoef hb0 hT hq hg Z hZ hind
  exact tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp hΛ) hev

/-- **The expected payoff of the explicit scheme diverges, as a real number** (Giles 2015,
§5.6, p. 44: "SDEs such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift
and/or the volatility.  This again leads to numerical instability if a uniform timestep is used";
Hutzenthaler, Jentzen and Kloeden, Proc. R. Soc. A 467 (2011)).  The Bochner-integral form of
`emPath_superlinear_payoff_lintegral_tendsto`, under the same hypotheses and the integrability of
`P(X_N)` for all large `N`: `E|P(X_N)| → ∞`.  (Without the integrability hypothesis the Bochner
integral of a non-integrable function would be `0`.) -/
theorem emPath_superlinear_payoff_integral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0) {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} {q D : ℝ} (hq : 0 < q)
    (hg : ∀ x, D ≤ |x| → |x| ^ q ≤ D * |g x|) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ)
    (hint : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => g (emPath a b (T / N) x₀ (fun n => Z N n ω) N)) μ) :
    Tendsto (fun N : ℕ => ∫ ω, |g (emPath a b (T / N) x₀ (fun n => Z N n ω) N)| ∂μ)
      atTop atTop := by
  obtain ⟨Λ, hΛ, hev⟩ := exists_payoff_lower hβ hαβ hcoef hb0 hT hq hg Z hZ hind
  refine tendsto_atTop_mono' atTop ?_ hΛ
  filter_upwards [hev, hint] with N hN hiN
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => abs_nonneg _)
    hiN.abs.aestronglyMeasurable]
  exact (ENNReal.ofReal_le_iff_le_toReal hiN.abs.lintegral_lt_top.ne).mp hN

/-- **The theorem of Hutzenthaler, Jentzen and Kloeden: the moments of the explicit scheme diverge**
(Giles 2015, §5.6, p. 44: "Hutzenthaler, Jentzen and Kloeden (2013), who are concerned with SDEs
such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the
volatility.  This again leads to numerical instability if a uniform timestep is used"; the theorem
is Hutzenthaler, Jentzen and Kloeden, Proc. R. Soc. A 467 (2011), on which the cited 2013 paper
builds).  If the coefficients satisfy HJK's growth condition, `|x|^β ≤ C max(|a(x,t)|, |b(x,t)|)`
and `min(|a(x,t)|, |b(x,t)|) ≤ C|x|^α` for `|x| ≥ C` (`1 < β`, `α < β`), `b(x₀, 0) ≠ 0`, `T > 0`,
and for each `N` the variables `Z_{N,0}, …, Z_{N,N−1}` are independent with law `N(0, 1)` (Brownian
increments `√(T/N) Z_{N,n}`), then the explicit Euler–Maruyama approximation `X_N` of `S_T` with `N`
steps satisfies `E|X_N|^p → ∞` for every `p > 0`.  The expectation is taken in `[0, ∞]`, as in HJK
(no measurability or integrability is assumed); HJK state it for `p ≥ 1`, a random initial value and
time-independent coefficients. -/
theorem emPath_superlinear_moment_lintegral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0) {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 0 < p)
    (Z : ℕ → ℕ → Ω → ℝ) (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    Tendsto (fun N : ℕ => ∫⁻ ω, ENNReal.ofReal (|emPath a b (T / N) x₀
      (fun n => Z N n ω) N| ^ p) ∂μ) atTop (𝓝 ∞) := by
  have h := emPath_superlinear_payoff_lintegral_tendsto hβ hαβ hcoef hb0 hT hp
    (g := fun x => |x| ^ p) (D := 1)
    (fun x _ => by rw [one_mul]; exact le_abs_self _) Z hZ hind
  refine h.congr fun N => lintegral_congr fun ω => ?_
  rw [abs_of_nonneg (by positivity)]

/-- **The expected absolute payoff on MLMC level `ℓ` diverges** (Giles 2015, §5.6, p. 44: "SDEs such
as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the volatility.
This again leads to numerical instability if a uniform timestep is used"; Hutzenthaler, Jentzen and
Kloeden, Proc. R. Soc. A 467 (2011)).  On level `ℓ` of an MLMC hierarchy with `N₀ 2^ℓ` uniform time
steps (`h_ℓ = T/(N₀ 2^ℓ)`, `N₀ ≥ 1`), under the hypotheses of
`emPath_superlinear_payoff_lintegral_tendsto`, the expected absolute payoff `E|P_ℓ|` of the
single level-`ℓ` explicit path tends to infinity as `ℓ → ∞` (in `[0, ∞]`).  So for a nonnegative
payoff the quantity `E[P_L]` that MLMC estimates on its finest level diverges as `L → ∞`.  Nothing
is proved here about the level means `E[P_ℓ − P_{ℓ−1}]` (the coupled fine and coarse paths) or the
level variances `V_ℓ`; see `mlmc_level_payoff_sq_lintegral_tendsto`. -/
theorem mlmc_level_payoff_lintegral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0) {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} {q D : ℝ} (hq : 0 < q)
    (hg : ∀ x, D ≤ |x| → |x| ^ q ≤ D * |g x|) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) :
    Tendsto (fun ℓ : ℕ => ∫⁻ ω, ENNReal.ofReal |g (emPath a b (T / (N₀ * 2 ^ ℓ : ℕ)) x₀
      (fun n => Z (N₀ * 2 ^ ℓ) n ω) (N₀ * 2 ^ ℓ))| ∂μ) atTop (𝓝 ∞) := by
  have hlev : Tendsto (fun ℓ : ℕ => N₀ * 2 ^ ℓ) atTop atTop :=
    tendsto_atTop_mono (fun ℓ => Nat.le_mul_of_pos_left _ hN₀)
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  exact (emPath_superlinear_payoff_lintegral_tendsto hβ hαβ hcoef hb0 hT hq hg Z hZ hind).comp hlev

/-- **The second moment of the payoff on MLMC level `ℓ` diverges** (Giles 2015, §5.6, p. 44: "SDEs
such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the
volatility.  This again leads to numerical instability if a uniform timestep is used"; Hutzenthaler,
Jentzen and Kloeden, Proc. R. Soc. A 467 (2011)).  Under the hypotheses of
`mlmc_level_payoff_lintegral_tendsto`, `E[P_ℓ²] → ∞` as `ℓ → ∞` (in `[0, ∞]`): apply it to `P²`,
which satisfies `|x|^{2q} ≤ max(D, D²) P(x)²` for `|x| ≥ max(D, D²)`.  Neither
`Var(P_ℓ) = E[P_ℓ²] − (E P_ℓ)²` nor the level variance `V_ℓ = Var(P_ℓ − P_{ℓ−1})` is covered: the
first is a difference of two divergent quantities, and a lower bound for it would need an upper
bound on `E|P_ℓ|` or a lower bound on `P(|P_ℓ| ≤ R)` (convergence in probability of the scheme),
neither of which is available here. -/
theorem mlmc_level_payoff_sq_lintegral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0) {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} {q D : ℝ} (hq : 0 < q)
    (hg : ∀ x, D ≤ |x| → |x| ^ q ≤ D * |g x|) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) :
    Tendsto (fun ℓ : ℕ => ∫⁻ ω, ENNReal.ofReal (g (emPath a b (T / (N₀ * 2 ^ ℓ : ℕ)) x₀
      (fun n => Z (N₀ * 2 ^ ℓ) n ω) (N₀ * 2 ^ ℓ)) ^ 2) ∂μ) atTop (𝓝 ∞) := by
  have hg2 : ∀ x, max D (D ^ 2) ≤ |x| → |x| ^ (2 * q) ≤ max D (D ^ 2) * |g x ^ 2| := by
    intro x hx
    have h1 := hg x ((le_max_left _ _).trans hx)
    have h0 : 0 ≤ |x| ^ q := by positivity
    rw [show (2 : ℝ) * q = q * 2 from mul_comm _ _, Real.rpow_mul (abs_nonneg x), Real.rpow_two,
      abs_pow]
    calc (|x| ^ q) ^ 2 ≤ (D * |g x|) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = D ^ 2 * |g x| ^ 2 := mul_pow _ _ 2
      _ ≤ max D (D ^ 2) * |g x| ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have h := mlmc_level_payoff_lintegral_tendsto hβ hαβ hcoef hb0 hT (g := fun x => g x ^ 2)
    (by positivity : 0 < 2 * q) hg2 Z hZ hind hN₀
  refine h.congr fun ℓ => lintegral_congr fun ω => ?_
  rw [abs_of_nonneg (sq_nonneg _)]

/-! ### Integrability, and the moments as real numbers -/

/-- Powers of a random variable with finite moments of every order have finite moments of every
order (`memLp_mul_of_forall`). -/
lemma hjk_memLp_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : ∀ q : ℝ≥0∞, q ≠ ∞ → MemLp f q μ) (r : ℕ) (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (fun ω => f ω ^ r) q μ := by
  induction r generalizing q with
  | zero => simpa using memLp_const (1 : ℝ)
  | succ r ih =>
    simp only [pow_succ]
    exact memLp_mul_of_forall ih hf q hq

/-- For coefficients measurable in `x` and bounded by `K(1 + |x|^r)`, the explicit scheme has finite
moments of every order at every step when the normal variables do (generalising `memLp_emCubic`). -/
lemma memLp_emPath_of_polyGrowth {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {a b : ℝ → ℝ → ℝ} (ham : ∀ t, Measurable fun x => a x t)
    (hbm : ∀ t, Measurable fun x => b x t) {K : ℝ} {r : ℕ}
    (hpoly : ∀ x t, |a x t| ≤ K * (1 + |x| ^ r) ∧ |b x t| ≤ K * (1 + |x| ^ r)) (h x₀ : ℝ)
    {Z : ℕ → Ω → ℝ} {n : ℕ} (hZ : ∀ k < n, ∀ q : ℝ≥0∞, q ≠ ∞ → MemLp (Z k) q μ)
    (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (fun ω => emPath a b h x₀ (fun k => Z k ω) n) q μ := by
  induction n generalizing q with
  | zero => exact memLp_const x₀
  | succ n ih =>
    have ih' := ih fun k hk => hZ k (Nat.lt_succ_of_lt hk)
    set X := fun ω => emPath a b h x₀ (fun k => Z k ω) n with hX
    have hXm : AEMeasurable X μ := (ih' 1 ENNReal.one_ne_top).aestronglyMeasurable.aemeasurable
    have hbound : ∀ q : ℝ≥0∞, q ≠ ∞ → MemLp (fun ω => K * (1 + |X ω ^ r|)) q μ := by
      intro q hq
      have h1 : MemLp (fun ω => |X ω ^ r|) q μ := (hjk_memLp_pow ih' r q hq).abs
      have h2 : MemLp (fun _ : Ω => (1 : ℝ)) q μ := memLp_const 1
      exact (h2.add h1).const_mul K
    have hA : ∀ q : ℝ≥0∞, q ≠ ∞ → MemLp (fun ω => a (X ω) (n * h)) q μ := fun q hq =>
      (hbound q hq).of_le ((ham _).comp_aemeasurable hXm).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
          exact (hpoly (X ω) _).1.trans (le_abs_self _))
    have hB : ∀ q : ℝ≥0∞, q ≠ ∞ → MemLp (fun ω => b (X ω) (n * h) * √h) q μ := fun q hq =>
      ((hbound q hq).of_le ((hbm _).comp_aemeasurable hXm).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
          exact (hpoly (X ω) _).2.trans (le_abs_self _))).mul_const √h
    have e : (fun ω => emPath a b h x₀ (fun k => Z k ω) (n + 1)) =
        fun ω => X ω + a (X ω) (n * h) * h + b (X ω) (n * h) * √h * Z n ω :=
      funext fun ω => emPath_succ a b h x₀ (fun k => Z k ω) n
    rw [e]
    exact ((ih' q hq).add ((hA q hq).mul_const h)).add
      (memLp_mul_of_forall hB (hZ n (Nat.lt_succ_self n)) q hq)

/-- **The moments of the explicit scheme diverge, as real numbers** (Giles 2015, §5.6, p. 44: "SDEs
such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the
volatility.  This again leads to numerical instability if a uniform timestep is used"; the theorem
of Hutzenthaler, Jentzen and Kloeden, Proc. R. Soc. A 467 (2011)).  The Bochner-integral form of
`emPath_superlinear_moment_lintegral_tendsto`: if moreover the coefficients are measurable in `x`
and polynomially bounded, `|a(x,t)|, |b(x,t)| ≤ K(1 + |x|^r)` (so that `X_N` has finite moments of
every order, `memLp_emPath_of_polyGrowth`), then `E|X_N|^p → ∞` for every `p > 0`. -/
theorem emPath_superlinear_moment_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    (ham : ∀ t, Measurable fun x => a x t) (hbm : ∀ t, Measurable fun x => b x t) {K : ℝ}
    {r : ℕ} (hpoly : ∀ x t, |a x t| ≤ K * (1 + |x| ^ r) ∧ |b x t| ≤ K * (1 + |x| ^ r))
    {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0) {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 0 < p)
    (Z : ℕ → ℕ → Ω → ℝ) (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    Tendsto (fun N : ℕ => ∫ ω, |emPath a b (T / N) x₀ (fun n => Z N n ω) N| ^ p ∂μ)
      atTop atTop := by
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff
    (aemeasurable_of_map_eq_gaussianReal (hZ 1 0 one_pos))).mp
    (by rw [hZ 1 0 one_pos]; infer_instance)
  have hint : ∀ N : ℕ, Integrable
      (fun ω => |emPath a b (T / N) x₀ (fun n => Z N n ω) N| ^ p) μ := fun N => by
    have hmem := memLp_emPath_of_polyGrowth ham hbm hpoly (T / N) x₀ (Z := Z N) (n := N)
      (fun k hk q hq => memLp_of_map_eq_gaussianReal (hZ N k hk) q hq) (ENNReal.ofReal p)
      ENNReal.ofReal_ne_top
    have := hmem.integrable_norm_rpow (by simpa using hp) ENNReal.ofReal_ne_top
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le] using this
  have h := emPath_superlinear_payoff_integral_tendsto hβ hαβ hcoef hb0 hT hp
    (g := fun x => |x| ^ p) (D := 1) (fun x _ => by rw [one_mul]; exact le_abs_self _) Z hZ hind
    (Eventually.of_forall hint)
  refine h.congr fun N => integral_congr_ae (Eventually.of_forall fun ω => ?_)
  exact abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)

/-- **The mean absolute value of the explicit scheme diverges** (Giles 2015, §5.6, p. 44: "SDEs such
as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the volatility.
This again leads to numerical instability if a uniform timestep is used"; Hutzenthaler, Jentzen and
Kloeden, Proc. R. Soc. A 467 (2011)).  The case `p = 1` of
`emPath_superlinear_moment_tendsto_atTop`: `E|X_N| → ∞` for measurable, polynomially bounded
coefficients satisfying HJK's growth condition, with `b(x₀, 0) ≠ 0`. -/
theorem emPath_superlinear_integral_abs_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ → ℝ → ℝ} {C α β : ℝ} (hβ : 1 < β) (hαβ : α < β)
    (hcoef : ∀ x t, C ≤ |x| →
      |x| ^ β ≤ C * max |a x t| |b x t| ∧ min |a x t| |b x t| ≤ C * |x| ^ α)
    (ham : ∀ t, Measurable fun x => a x t) (hbm : ∀ t, Measurable fun x => b x t) {K : ℝ}
    {r : ℕ} (hpoly : ∀ x t, |a x t| ≤ K * (1 + |x| ^ r) ∧ |b x t| ≤ K * (1 + |x| ^ r))
    {x₀ : ℝ} (hb0 : b x₀ 0 ≠ 0) {T : ℝ} (hT : 0 < T)
    (Z : ℕ → ℕ → Ω → ℝ) (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    Tendsto (fun N : ℕ => ∫ ω, |emPath a b (T / N) x₀ (fun n => Z N n ω) N| ∂μ)
      atTop atTop := by
  simpa using emPath_superlinear_moment_tendsto_atTop hβ hαβ hcoef ham hbm hpoly hb0 hT one_pos
    Z hZ hind

/-! ### Examples -/

/-- **The paper's example as a special case** (Giles 2015, §5.6, p. 44: "SDEs such as
`dS_t = −S_t³ dt + dW_t` … This again leads to numerical instability if a uniform timestep is used";
Hutzenthaler, Jentzen and Kloeden, Proc. R. Soc. A 467 (2011)).
`emPath_superlinear_moment_tendsto_atTop` with `a(S) = −S³`, `b = 1`, `C = 1`, `α = 0`, `β = 3`,
`K = 1`, `r = 3`: for every `x₀`, `T > 0` and `p > 0`, `E|X_N|^p → ∞`.  The statement is identical
to `emCubic_moment_tendsto_atTop` (`MlmcLean/EulerSuperlinear.lean`), which is thus recovered from
the general theorem. -/
theorem hjk_cubic_moment_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (x₀ : ℝ)
    {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 0 < p) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    Tendsto (fun N : ℕ => ∫ ω, |emPath (fun S _ => -S ^ 3) (fun _ _ => 1) (T / N) x₀
      (fun n => Z N n ω) N| ^ p ∂μ) atTop atTop := by
  refine emPath_superlinear_moment_tendsto_atTop (C := 1) (α := 0) (β := 3) (K := 1) (r := 3)
    (by norm_num) (by norm_num) (fun x _ _ => ?_) (fun _ => by fun_prop) (fun _ => by fun_prop)
    (fun x _ => ⟨?_, ?_⟩) one_ne_zero hT hp Z hZ hind
  · rw [one_mul, one_mul, Real.rpow_zero, abs_neg, abs_pow, abs_one, Real.rpow_ofNat]
    exact ⟨le_max_left _ _, min_le_right _ _⟩
  · rw [abs_neg, abs_pow]
    linarith
  · rw [abs_one]
    nlinarith [pow_nonneg (abs_nonneg x) 3]

/-- `hjk_cubic_moment_tendsto_atTop` has exactly the statement of `emCubic_moment_tendsto_atTop`
(`MlmcLean/EulerSuperlinear.lean`): the two propositions are syntactically equal, so the two proofs
are equal by `rfl` (proof irrelevance). -/
example : @hjk_cubic_moment_tendsto_atTop = @emCubic_moment_tendsto_atTop := rfl

/-- **Divergence for the drift `−S|S|`** (Giles 2015, §5.6, p. 44: "SDEs such as
`dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the volatility.  This
again leads to numerical instability if a uniform timestep is used"; Hutzenthaler, Jentzen and
Kloeden, Proc. R. Soc. A 467 (2011)).  For `dS = −S|S| dt + dW` (quadratic growth, `β = 2`, `α = 0`,
`C = 1`), every `x₀`, `T > 0` and `p > 0`, the explicit Euler–Maruyama scheme with `h = T/N` and
i.i.d.  `N(0, T/N)` increments satisfies `E|X_N|^p → ∞`. -/
theorem hjk_xabs_moment_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (x₀ : ℝ)
    {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 0 < p) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    Tendsto (fun N : ℕ => ∫ ω, |emPath (fun S _ => -(S * |S|)) (fun _ _ => 1) (T / N) x₀
      (fun n => Z N n ω) N| ^ p ∂μ) atTop atTop := by
  have habs : ∀ x : ℝ, |-(x * |x|)| = |x| ^ 2 := fun x => by
    rw [abs_neg, abs_mul, abs_abs, sq]
  refine emPath_superlinear_moment_tendsto_atTop (C := 1) (α := 0) (β := 2) (K := 1) (r := 2)
    (by norm_num) (by norm_num) (fun x _ _ => ?_) (fun _ => by fun_prop) (fun _ => by fun_prop)
    (fun x _ => ⟨?_, ?_⟩) one_ne_zero hT hp Z hZ hind
  · rw [one_mul, one_mul, Real.rpow_zero, habs, abs_one, Real.rpow_two]
    exact ⟨le_max_left _ _, min_le_right _ _⟩
  · rw [habs]
    linarith
  · rw [abs_one]
    nlinarith [sq_nonneg |x|]

/-- **Divergence for the stochastic Ginzburg–Landau equation** (Giles 2015, §5.6, p. 44: "SDEs such
as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the volatility.
This again leads to numerical instability if a uniform timestep is used"; Hutzenthaler, Jentzen and
Kloeden, Proc. R. Soc. A 467 (2011)).  For `dS = (S − S³) dt + σS dW` with `σ ≠ 0` (multiplicative
noise: `β = 3`, `α = 1`, `C = 2 + |σ|`), every `x₀ ≠ 0`, `T > 0` and `p > 0`, the explicit
Euler–Maruyama scheme with `h = T/N` satisfies `E|X_N|^p → ∞`.  (For `x₀ = 0` the scheme stays at
`0`, so `x₀ ≠ 0`, i.e. `b(x₀) ≠ 0`, is needed.) -/
theorem hjk_ginzburgLandau_moment_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {σ x₀ : ℝ} (hσ : σ ≠ 0) (hx₀ : x₀ ≠ 0) {T : ℝ} (hT : 0 < T) {p : ℝ}
    (hp : 0 < p) (Z : ℕ → ℕ → Ω → ℝ) (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    Tendsto (fun N : ℕ => ∫ ω, |emPath (fun S _ => S - S ^ 3) (fun S _ => σ * S) (T / N) x₀
      (fun n => Z N n ω) N| ^ p ∂μ) atTop atTop := by
  have hs := abs_nonneg σ
  have hcube : ∀ x : ℝ, |x| ≤ 1 + |x| ^ 3 := fun x => by
    nlinarith [abs_nonneg x, sq_nonneg (|x| - 1), mul_nonneg (abs_nonneg x) (sq_nonneg (|x| - 1))]
  refine emPath_superlinear_moment_tendsto_atTop (a := fun S _ => S - S ^ 3)
    (b := fun S _ => σ * S) (x₀ := x₀) (C := 2 + |σ|) (α := 1) (β := 3)
    (K := 2 + |σ|) (r := 3) (by norm_num) (by norm_num) (fun x _ hx => ?_)
    (fun _ => by fun_prop) (fun _ => by fun_prop) (fun x _ => ⟨?_, ?_⟩) (mul_ne_zero hσ hx₀) hT
    hp Z hZ hind
  · rw [Real.rpow_one, Real.rpow_ofNat]
    have hx2 : 2 ≤ |x| := by linarith
    have hx3 : |x - x ^ 3| = |x| ^ 3 - |x| := by
      have e : x - x ^ 3 = -(x * (x ^ 2 - 1)) := by ring
      rw [e, abs_neg, abs_mul, abs_of_nonneg (by nlinarith [sq_abs x] : (0 : ℝ) ≤ x ^ 2 - 1),
        ← sq_abs x]
      ring
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
      rw [hx3]
      have h1 : 2 * |x| ≤ |x| ^ 3 := by
        have : 0 ≤ |x| * (|x| ^ 2 - 2) := mul_nonneg (abs_nonneg x) (by nlinarith)
        nlinarith
      have h2 : 0 ≤ |σ| * (|x| ^ 3 - |x|) := mul_nonneg hs (by linarith)
      nlinarith
    · refine (min_le_right _ _).trans ?_
      rw [abs_mul]
      nlinarith [abs_nonneg x]
  · have := abs_sub (x) (x ^ 3)
    rw [abs_pow] at this
    nlinarith [hcube x, pow_nonneg (abs_nonneg x) 3]
  · rw [abs_mul]
    nlinarith [hcube x, pow_nonneg (abs_nonneg x) 3, abs_nonneg x]

/-- **Divergence when the volatility dominates: `dS = −S dt + S² dW`** (Giles 2015, §5.6, p. 44:
"SDEs such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the
volatility.  This again leads to numerical instability if a uniform timestep is used"; Hutzenthaler,
Jentzen and Kloeden, Proc. R. Soc. A 467 (2011)).  For `dS = −S dt + S² dW` (linear drift,
quadratic volatility: `β = 2`, `α = 1`, `C = 1`), every `x₀ ≠ 0`, `T > 0` and `p > 0`, the explicit
Euler–Maruyama scheme with `h = T/N` satisfies `E|X_N|^p → ∞`.  Here `|b(x)| = x² ≥ |a(x)| = |x|`
for `|x| ≥ 1`, so every step of the divergence argument is in the volatility case of `hjk_step_ge`,
which uses `|Z_k| ≥ 1/2`.  (For `x₀ = 0` the scheme stays at `0`.) -/
theorem hjk_quadVol_moment_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {x₀ : ℝ} (hx₀ : x₀ ≠ 0) {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 0 < p) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    Tendsto (fun N : ℕ => ∫ ω, |emPath (fun S _ => -S) (fun S _ => S ^ 2) (T / N) x₀
      (fun n => Z N n ω) N| ^ p ∂μ) atTop atTop := by
  refine emPath_superlinear_moment_tendsto_atTop (a := fun S _ => -S) (b := fun S _ => S ^ 2)
    (C := 1) (α := 1) (β := 2) (K := 1) (r := 2) (by norm_num) (by norm_num) (fun x _ _ => ?_)
    (fun _ => by fun_prop) (fun _ => by fun_prop) (fun x _ => ⟨?_, ?_⟩) (pow_ne_zero 2 hx₀) hT
    hp Z hZ hind
  · rw [one_mul, one_mul, Real.rpow_one, Real.rpow_two, abs_neg, abs_pow]
    exact ⟨le_max_right _ _, min_le_left _ _⟩
  · rw [abs_neg, one_mul]
    nlinarith [sq_nonneg (|x| - 1)]
  · rw [abs_pow, one_mul]
    linarith

end MLMC
