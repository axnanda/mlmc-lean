import MlmcLean.SDEMisc
import MlmcLean.GBMEulerMaruyama

/-!
# Giles 2015, §5.6: the explicit Euler–Maruyama scheme diverges for a super-linear drift

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.6 "Stiff and
highly nonlinear SDEs" (pp. 43–44), p. 44: "A related problem is addressed by Hutzenthaler, Jentzen
and Kloeden (2013), who are concerned with SDEs such as `dS_t = −S_t³ dt + dW_t`, which have a
super-linear growth in the drift and/or the volatility.  This again leads to numerical instability
if a uniform timestep is used.  Their solution is to introduce a slight modification to the
Euler-Maruyama discretisation which limits the size of the drift term on each level of
approximation when `S_t` is large, to avoid this instability."

The survey states no theorem.  The rigorous form of "numerical instability" is the theorem of
Hutzenthaler, Jentzen and Kloeden (Proc. R. Soc. A 467 (2011), 1563–1576), on which their 2013
paper cited by Giles builds: the explicit Euler–Maruyama approximations `X_N` at time `T` of an SDE
with a super-linearly growing coefficient satisfy `E|X_N|^p → ∞` as the number of steps `N → ∞`.
This file proves it for the paper's example `dS_t = −S_t³ dt + dW_t`, for every initial value, every
horizon `T > 0` and every `p > 0`, with HJK's argument: with probability at least
`P(Z ≥ cN/T) P(|Z| ≤ 1)^{N−1} ≥ e^{−O(N²)}` the first increment is large and the others are small,
and on that event `|X_N| ≥ 2^{2^{N−1}}`.  `MlmcLean/SDEMisc.lean` has the noise-free part
(`eulerCubic_growth`, `eulerCubic_tendsto_atTop`, `tamedCubic_bounded`).

* `eulerCubic_noise_growth`: if `x_{k+1} = x_k − h x_k³ + w_k` with `h w_k² ≤ 1` (in particular
  `|w_k| ≤ 1` when `h ≤ 1`) and `h x_0² ≥ 4`, then `h x_n² ≥ (h x_0²)^{2ⁿ}`: bounded noise cannot
  stop the doubly exponential growth of the explicit step.
* `le_gaussianReal_real_Icc`, `le_gaussianReal_real_Ici`: the Gaussian lower bounds
  `P(a ≤ Z ≤ b) ≥ (b − a) e^{−max(a², b²)/2}/√(2π)` and `P(Z ≥ x) ≥ e^{−(|x|+1)²/2}/√(2π)`.
* `emCubic_moment_ge`: the explicit lower bound
  `E|X_N|^p ≥ P(Z ≥ (2 + |x₀| + |x₀|³)N/T) · P(|Z| ≤ 1)^{N−1} · 2^{p 2^{N−1}}` for `N ≥ T`.
* `emCubic_moment_tendsto_atTop`, `emCubic_integral_abs_tendsto_atTop`: **the theorem of
  Hutzenthaler, Jentzen and Kloeden** for `dS = −S³ dt + dW`: `E|X_N|^p → ∞` for every `p > 0`, for
  any i.i.d. `N(0, T/N)` increments on any probability space.
* `tamedPath_integral_abs_le`: for the tamed scheme
  `X_{n+1} = X_n + h b(X_n)/(1 + h|b(X_n)|) + ΔW_n` with an inward drift (`S b(S) ≤ 0`),
  `E|X_N| ≤ max(|x₀|, 1) + √(TN)`, with no independence;
  `abs_tamedCubic_le`, `tamedCubic_nonexpansive_iff`: the tamed cubic step does not increase `|S|`
  if and only if `h ≤ 54`; `tamedCubic_second_moment_le`: hence `E X_N² ≤ x₀² + T` uniformly in
  `N ≥ T/54` (the exact solution satisfies the same bound, by Itô's formula).  Taming removes the
  mechanism.

Not formalised: the general HJK theorem (arbitrary super-linearly growing coefficients), the
finiteness of the moments of the exact solution (SDE theory), and the uniform `p`-th moment bounds
of the tamed scheme for `p > 2`.
-/

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal

namespace MLMC

/-! ### Pathwise growth of the explicit step with bounded noise -/

/-- One explicit step `s ↦ s − s³ + t` (in the rescaled variables `s = √h x`, `t = √h w`) squares
`s²` when `s² ≥ 4` and `t² ≤ 1`: `|s − s³ + t| ≥ |s|³ − |s| − 1 ≥ s²`. -/
lemma cubic_step_sq_ge {s t : ℝ} (hs : 4 ≤ s ^ 2) (ht : t ^ 2 ≤ 1) :
    (s ^ 2) ^ 2 ≤ (s - s ^ 3 + t) ^ 2 := by
  have ha : 2 ≤ |s| := by nlinarith [abs_nonneg s, sq_abs s]
  have ht1 : |t| ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  have e1 : |s - s ^ 3| = |s| ^ 3 - |s| := by
    have : s - s ^ 3 = -(s * (s ^ 2 - 1)) := by ring
    rw [this, abs_neg, abs_mul, abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ s ^ 2 - 1), ← sq_abs s]
    ring
  have h1 : |s| ^ 3 - |s| - 1 ≤ |s - s ^ 3 + t| := by
    have := abs_sub_abs_le_abs_sub (s - s ^ 3) (-t)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have h2 : |s| ^ 2 ≤ |s - s ^ 3 + t| := by nlinarith
  calc (s ^ 2) ^ 2 = (|s| ^ 2) ^ 2 := by rw [sq_abs]
    _ ≤ |s - s ^ 3 + t| ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    _ = (s - s ^ 3 + t) ^ 2 := sq_abs _

/-- **Bounded noise cannot stop the explosion of the explicit step** (Giles 2015, §5.6, p. 44: SDEs
"such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the
volatility.  This again leads to numerical instability if a uniform timestep is used").  Let
`x_{k+1} = x_k − h x_k³ + w_k` for `k < n` (the explicit Euler step `eulerDriftStep` for the drift
`−S³` plus a perturbation `w_k`, e.g. a Brownian increment).  If `h x_0² ≥ 4` and `h w_k² ≤ 1` for
`k < n` (e.g. `|w_k| ≤ 1` and `h ≤ 1`), then `h x_n² ≥ (h x_0²)^{2ⁿ}`: the growth is doubly
exponential.  This is the pathwise step of the divergence proof of Hutzenthaler, Jentzen and
Kloeden (Proc. R. Soc. A 467 (2011)); it extends the noise-free `eulerCubic_growth`.  (`h > 0`
follows from `h x_0² ≥ 4`.) -/
theorem eulerCubic_noise_growth {h : ℝ} {x w : ℕ → ℝ} {n : ℕ}
    (hx : ∀ k < n, x (k + 1) = eulerDriftStep (fun S => -S ^ 3) h (x k) + w k)
    (h4 : 4 ≤ h * x 0 ^ 2) (hw : ∀ k < n, h * w k ^ 2 ≤ 1) :
    (h * x 0 ^ 2) ^ 2 ^ n ≤ h * x n ^ 2 := by
  have hh : 0 ≤ h := by
    by_contra hneg
    nlinarith [sq_nonneg (x 0)]
  obtain ⟨r, rfl⟩ : ∃ r, h = r ^ 2 := ⟨√h, (Real.sq_sqrt hh).symm⟩
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun k hk => hx k (Nat.lt_succ_of_lt hk))
      fun k hk => hw k (Nat.lt_succ_of_lt hk)
    have hs : 4 ≤ (r * x n) ^ 2 := by
      have : r ^ 2 * x 0 ^ 2 ≤ (r ^ 2 * x 0 ^ 2) ^ 2 ^ n :=
        le_self_pow₀ (by linarith) (by positivity)
      nlinarith
    have ht : (r * w n) ^ 2 ≤ 1 := by nlinarith [hw n (Nat.lt_succ_self n)]
    have e : r ^ 2 * x (n + 1) ^ 2 = (r * x n - (r * x n) ^ 3 + r * w n) ^ 2 := by
      rw [hx n (Nat.lt_succ_self n)]
      unfold eulerDriftStep
      ring
    rw [e, pow_succ (2 : ℕ) n, pow_mul]
    calc ((r ^ 2 * x 0 ^ 2) ^ 2 ^ n) ^ 2 ≤ ((r * x n) ^ 2) ^ 2 := by
          have : (r * x n) ^ 2 = r ^ 2 * x n ^ 2 := by ring
          rw [this]
          exact pow_le_pow_left₀ (by positivity) ih' 2
      _ ≤ _ := cubic_step_sq_ge hs ht

/-! ### Gaussian lower bounds -/

/-- **A lower bound for Gaussian interval probabilities** (Giles 2015, §5.6, p. 44: "This again
leads to numerical instability if a uniform timestep is used").  An auxiliary Gaussian fact that the
survey does not state: the divergence proof of Hutzenthaler, Jentzen and Kloeden behind this
sentence needs it.  For a standard normal `Z` and all `a, b`,
`P(a ≤ Z ≤ b) ≥ (b − a) e^{−max(a², b²)/2}/√(2π)`: the density is at least its value at the
endpoint farther from `0` (for `b < a` the left side is negative). -/
theorem le_gaussianReal_real_Icc (a b : ℝ) :
    (b - a) * (Real.exp (-max (a ^ 2) (b ^ 2) / 2) / √(2 * π)) ≤
      (gaussianReal 0 1).real (Set.Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)).trans measureReal_nonneg
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
      fun x _ => gaussianPDFReal_nonneg 0 1 x),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hm : ∀ x ∈ Set.Icc a b,
      Real.exp (-max (a ^ 2) (b ^ 2) / 2) / √(2 * π) ≤ gaussianPDFReal 0 1 x := by
    intro x hx
    have hx2 : x ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
      rcases le_total 0 x with h0 | h0
      · exact le_max_of_le_right (by nlinarith [hx.2])
      · exact le_max_of_le_left (by nlinarith [hx.1])
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [div_eq_inv_mul]
    gcongr
  calc (b - a) * (Real.exp (-max (a ^ 2) (b ^ 2) / 2) / √(2 * π)) =
      ∫ _ in a..b, Real.exp (-max (a ^ 2) (b ^ 2) / 2) / √(2 * π) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ ∫ x in a..b, gaussianPDFReal 0 1 x :=
        intervalIntegral.integral_mono_on hab intervalIntegrable_const
          (integrable_gaussianPDFReal 0 1).intervalIntegrable hm

/-- **A Gaussian tail lower bound** (Giles 2015, §5.6, p. 44: "This again leads to numerical
instability if a uniform timestep is used").  An auxiliary Gaussian fact that the survey does not
state: the divergence proof of Hutzenthaler, Jentzen and Kloeden behind this sentence needs it (for
the large first increment).  For a standard normal `Z` and every `x`,
`P(Z ≥ x) ≥ e^{−(|x|+1)²/2}/√(2π)`; for `x ≥ 0` this is `P(Z ≥ x) ≥ P(x ≤ Z ≤ x + 1) ≥
e^{−(x+1)²/2}/√(2π)`, and for `x < 0` it follows from `P(0 ≤ Z ≤ 1) ≥ e^{−1/2}/√(2π)`. -/
theorem le_gaussianReal_real_Ici (x : ℝ) :
    Real.exp (-(|x| + 1) ^ 2 / 2) / √(2 * π) ≤ (gaussianReal 0 1).real (Set.Ici x) := by
  rcases le_total 0 x with hx | hx
  · have h := le_gaussianReal_real_Icc x (x + 1)
    rw [max_eq_right (by nlinarith), add_sub_cancel_left, one_mul] at h
    rw [abs_of_nonneg hx]
    exact h.trans (measureReal_mono Set.Icc_subset_Ici_self)
  · have h := le_gaussianReal_real_Icc 0 1
    rw [max_eq_right (by norm_num), sub_zero, one_mul, one_pow] at h
    have h1 : Real.exp (-(|x| + 1) ^ 2 / 2) ≤ Real.exp (-1 / 2) := by
      gcongr
      nlinarith [abs_nonneg x]
    calc Real.exp (-(|x| + 1) ^ 2 / 2) / √(2 * π) ≤ Real.exp (-1 / 2) / √(2 * π) := by gcongr
      _ ≤ _ := h.trans (measureReal_mono fun y hy => Set.mem_Ici.2 (hx.trans hy.1))

/-! ### The explicit Euler–Maruyama scheme for `dS = −S³ dt + dW` -/

/-- The pathwise estimate on the event of the divergence proof: for the explicit scheme
`X_{n+1} = X_n − h X_n³ + ΔW_n`, `ΔW_n = √h z_n` (`emPath` with drift `−S³` and volatility `1`),
`0 < h ≤ 1`, a large first increment, `√h ΔW_0 = h z_0 ≥ 2 + |x₀| + |x₀|³` (which forces
`h X_1² ≥ 4`), and `|z_k| ≤ 1` for `1 ≤ k ≤ M` give `|X_{M+1}| ≥ 2^{2^M}`
(`eulerCubic_noise_growth`). -/
lemma emCubic_abs_ge {h x₀ : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) {z : ℕ → ℝ} {M : ℕ}
    (hz0 : 2 + |x₀| + |x₀| ^ 3 ≤ h * z 0) (hz : ∀ k, 1 ≤ k → k ≤ M → |z k| ≤ 1) :
    (2 : ℝ) ^ 2 ^ M ≤ |emPath (fun S _ => -S ^ 3) (fun _ _ => 1) h x₀ z (M + 1)| := by
  set X := emPath (fun S _ => -S ^ 3) (fun _ _ => 1) h x₀ z with hXdef
  have hrec : ∀ k, X (k + 1) = eulerDriftStep (fun S => -S ^ 3) h (X k) + √h * z k := by
    intro k
    simp only [hXdef, emPath_succ, eulerDriftStep]
    ring
  have h4 : 4 ≤ h * X 1 ^ 2 := by
    have e1 : X 1 = x₀ - h * x₀ ^ 3 + √h * z 0 := by
      rw [hrec 0]
      simp only [hXdef, emPath, eulerDriftStep]
      ring
    set s := √h with hs
    have hs2 : s ^ 2 = h := Real.sq_sqrt hh0.le
    have hs0 : 0 ≤ s := Real.sqrt_nonneg h
    have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr hh1
    have hx3 : x₀ ^ 3 ≤ |x₀| ^ 3 := by
      rw [← abs_pow]
      exact le_abs_self _
    have hx1 : x₀ ≥ -|x₀| := neg_abs_le x₀
    have ha0 : 0 ≤ |x₀| := abs_nonneg x₀
    have key : 2 ≤ s * X 1 := by
      rw [e1, ← hs2]
      have h1 : s * |x₀| ≤ |x₀| := mul_le_of_le_one_left ha0 hs1
      have h2 : s ^ 3 * |x₀| ^ 3 ≤ |x₀| ^ 3 :=
        mul_le_of_le_one_left (by positivity) (pow_le_one₀ hs0 hs1)
      have h3 : s ^ 3 * x₀ ^ 3 ≤ s ^ 3 * |x₀| ^ 3 :=
        mul_le_mul_of_nonneg_left hx3 (by positivity)
      have h5 : -(s * |x₀|) ≤ s * x₀ := by nlinarith
      rw [← hs2] at hz0
      nlinarith
    have : h * X 1 ^ 2 = (s * X 1) ^ 2 := by rw [mul_pow, hs2]
    rw [this]
    nlinarith
  have hw : ∀ k < M, h * (√h * z (k + 1)) ^ 2 ≤ 1 := by
    intro k hk
    have hzk := hz (k + 1) (by omega) (by omega)
    have hz2 : z (k + 1) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (z (k + 1)), sq_abs (z (k + 1))]
    rw [mul_pow, Real.sq_sqrt hh0.le]
    have : h * h ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (z (k + 1))]
  have hg := eulerCubic_noise_growth (x := fun k => X (k + 1)) (w := fun k => √h * z (k + 1))
    (fun k _ => hrec (k + 1)) h4 hw
  have h44 : (4 : ℝ) ^ 2 ^ M ≤ (h * X 1 ^ 2) ^ 2 ^ M := pow_le_pow_left₀ (by norm_num) h4 _
  have hX2 : h * X (M + 1) ^ 2 ≤ X (M + 1) ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) hh1
  have hsq : ((2 : ℝ) ^ 2 ^ M) ^ 2 ≤ X (M + 1) ^ 2 := by
    have e4 : ((2 : ℝ) ^ 2 ^ M) ^ 2 = (4 : ℝ) ^ 2 ^ M := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    linarith
  have := sq_le_sq.mp hsq
  rwa [abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 2 ^ M)] at this

/-- Random variables with finite moments of every order form an algebra: if `f` and `g` are in
every `Lᵠ`, `q < ∞`, so is `fg` (Hölder with `1/(2q) + 1/(2q) = 1/q`). -/
lemma memLp_mul_of_forall {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : ∀ q : ℝ≥0∞, q ≠ ∞ → MemLp f q μ) (hg : ∀ q : ℝ≥0∞, q ≠ ∞ → MemLp g q μ)
    (q : ℝ≥0∞) (hq : q ≠ ∞) : MemLp (fun ω => f ω * g ω) q μ := by
  have h2 : 2 * q ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hq
  exact (hg (2 * q) h2).mul' (hf (2 * q) h2) (hpqr := ⟨by
    rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul]⟩)

/-- A random variable with law `N(0, 1)` is almost everywhere measurable: otherwise its image
measure `μ.map Y` would be `0`. -/
lemma aemeasurable_of_map_eq_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} (hY : μ.map Y = gaussianReal 0 1) : AEMeasurable Y μ :=
  AEMeasurable.of_map_ne_zero (by rw [hY]; exact IsProbabilityMeasure.ne_zero _)

/-- A random variable with law `N(0, 1)` has finite moments of every order. -/
lemma memLp_of_map_eq_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}
    (hY : μ.map Y = gaussianReal 0 1) (q : ℝ≥0∞) (hq : q ≠ ∞) : MemLp Y q μ := by
  have h := memLp_id_gaussianReal' (μ := 0) (v := 1) q hq
  rw [← hY] at h
  exact h.comp_of_map (aemeasurable_of_map_eq_gaussianReal hY)

/-- The explicit scheme for `dS = −S³ dt + dW` has finite moments of every order at every step: it
is a polynomial in the increments, which have finite moments of every order. -/
lemma memLp_emCubic {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (h x₀ : ℝ) {Z : ℕ → Ω → ℝ} {n : ℕ} (hZ : ∀ k < n, ∀ q : ℝ≥0∞, q ≠ ∞ → MemLp (Z k) q μ)
    (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (fun ω => emPath (fun S _ => -S ^ 3) (fun _ _ => 1) h x₀ (fun k => Z k ω) n) q μ := by
  induction n generalizing q with
  | zero => exact memLp_const x₀
  | succ n ih =>
    have ih' := ih fun k hk => hZ k (Nat.lt_succ_of_lt hk)
    have hcube : ∀ q : ℝ≥0∞, q ≠ ∞ → MemLp (fun ω =>
        emPath (fun S _ => -S ^ 3) (fun _ _ => 1) h x₀ (fun k => Z k ω) n ^ 3) q μ := by
      intro q hq
      convert memLp_mul_of_forall ih' (memLp_mul_of_forall ih' ih') q hq using 2 with ω
      ring
    simp only [emPath_succ]
    exact ((ih' q hq).add ((hcube q hq).neg.mul_const h)).add
      ((hZ n (Nat.lt_succ_self n) q hq).const_mul (1 * √h))

/-- **An explicit lower bound for the moments of the explicit scheme** (Giles 2015, §5.6, p. 44:
"This again leads to numerical instability if a uniform timestep is used"; the argument is that of
Hutzenthaler, Jentzen and Kloeden, Proc. R. Soc. A 467 (2011), cited by the survey through their
2013 paper).  Let `T > 0`, `N ≥ T` (so `h = T/N ≤ 1`), `p ≥ 0`, and let `Z_0, …, Z_{N−1}` be
independent with law `N(0, 1)`, so that `ΔW_n = √h Z_n` are i.i.d. `N(0, h)`.  The explicit
Euler–Maruyama scheme `X_{n+1} = X_n − h X_n³ + ΔW_n`, `X_0 = x₀`, for `dS = −S³ dt + dW` (`emPath`
with drift `−S³` and volatility `1`) satisfies, with `c = 2 + |x₀| + |x₀|³`,
`E|X_N|^p ≥ P(Z ≥ cN/T) · P(|Z| ≤ 1)^{N−1} · (2^{2^{N−1}})^p`: on the event `{Z_0 ≥ cN/T,
|Z_k| ≤ 1 for 1 ≤ k < N}` one has `|X_N| ≥ 2^{2^{N−1}}` (`emCubic_abs_ge`), and the probability of
the event factorises by independence.  With `le_gaussianReal_real_Ici` the first factor is at least
`e^{−(cN/T + 1)²/2}/√(2π)`, so the bound grows like `exp(p 2^{N−1} log 2 − O(N²))`.  Neither the
measurability of the `Z_n` nor that `μ` is a probability measure is assumed: both follow from the
laws (`N ≥ 1` since `T > 0`). -/
theorem emCubic_moment_ge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (x₀ : ℝ) {T : ℝ}
    (hT : 0 < T) {p : ℝ} (hp : 0 ≤ p) {N : ℕ} (hN : T ≤ N) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    (gaussianReal 0 1).real (Set.Ici ((2 + |x₀| + |x₀| ^ 3) * N / T)) *
        (gaussianReal 0 1).real (Set.Icc (-1) 1) ^ (N - 1) * ((2 : ℝ) ^ 2 ^ (N - 1)) ^ p ≤
      ∫ ω, |emPath (fun S _ => -S ^ 3) (fun _ _ => 1) (T / N) x₀ (fun n => Z n ω) N| ^ p ∂μ := by
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) < N := hT.trans_le hN
    exact_mod_cast this
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hm : ∀ n < M + 1, AEMeasurable (Z n) μ := fun n hn =>
    aemeasurable_of_map_eq_gaussianReal (hZ n hn)
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff (hm 0 (by omega))).mp
    (by rw [hZ 0 (by omega)]; infer_instance)
  set c := 2 + |x₀| + |x₀| ^ 3 with hc
  set h := T / ((M + 1 : ℕ) : ℝ) with hh
  have hN' : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have hh0 : 0 < h := div_pos hT hN'
  have hh1 : h ≤ 1 := (div_le_one hN').mpr hN
  set a := c * ((M + 1 : ℕ) : ℝ) / T with ha
  have hha : h * a = c := by
    rw [hh, ha]
    field_simp
  set ε := ((2 : ℝ) ^ 2 ^ M) ^ p
  let S : Fin (M + 1) → Set ℝ := fun i => if (i : ℕ) = 0 then Set.Ici a else Set.Icc (-1) 1
  have hSm : ∀ i, MeasurableSet (S i) := fun i => by
    simp only [S]
    split_ifs
    exacts [measurableSet_Ici, measurableSet_Icc]
  set E := ⋂ i ∈ (Finset.univ : Finset (Fin (M + 1))), (fun n : Fin (M + 1) => Z n) i ⁻¹' S i
    with hE
  have hμE : μ.real E = (gaussianReal 0 1).real (Set.Ici a) *
      (gaussianReal 0 1).real (Set.Icc (-1) 1) ^ M := by
    have h1 := hind.measure_inter_preimage_eq_mul Finset.univ (sets := S) (fun i _ => hSm i)
    have h2 : ∀ i : Fin (M + 1), μ (Z i ⁻¹' S i) = gaussianReal 0 1 (S i) := fun i => by
      rw [← hZ i i.2, Measure.map_apply_of_aemeasurable (hm i i.2) (hSm i)]
    rw [measureReal_def, hE, h1]
    simp only [h2, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, S, if_true,
      Nat.add_one_ne_zero, if_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.toReal_mul, ENNReal.toReal_pow, measureReal_def]
  have hsub : E ⊆ {ω | ε ≤ |emPath (fun S _ => -S ^ 3) (fun _ _ => 1) h x₀
      (fun n => Z n ω) (M + 1)| ^ p} := by
    intro ω hω
    have hmem : ∀ i : Fin (M + 1), Z i ω ∈ S i := fun i =>
      Set.mem_iInter₂.mp hω i (Finset.mem_univ i)
    have hz0 : a ≤ Z 0 ω := by simpa [S] using hmem 0
    have hzk : ∀ k, 1 ≤ k → k ≤ M → |Z k ω| ≤ 1 := by
      intro k hk1 hkM
      have := hmem ⟨k, by omega⟩
      have hk0 : k ≠ 0 := by omega
      simp only [S, hk0, if_false] at this
      exact abs_le.mpr this
    have hgrow := emCubic_abs_ge (x₀ := x₀) hh0 hh1 (z := fun n => Z n ω) (M := M)
      (by rw [← hc, ← hha]; exact mul_le_mul_of_nonneg_left hz0 hh0.le) hzk
    exact Real.rpow_le_rpow (by positivity) hgrow hp
  have hint : Integrable (fun ω => |emPath (fun S _ => -S ^ 3) (fun _ _ => 1) h x₀
      (fun n => Z n ω) (M + 1)| ^ p) μ := by
    rcases hp.eq_or_lt with h0 | h0
    · simp only [← h0, Real.rpow_zero]
      exact integrable_const 1
    · have hmem := memLp_emCubic h x₀ (Z := Z) (n := M + 1)
        (fun k hk q hq => memLp_of_map_eq_gaussianReal (hZ k hk) q hq) (ENNReal.ofReal p)
        ENNReal.ofReal_ne_top
      have := hmem.integrable_norm_rpow (by simpa using h0) ENNReal.ofReal_ne_top
      simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal h0.le] using this
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => by positivity) hint ε
  calc (gaussianReal 0 1).real (Set.Ici a) * (gaussianReal 0 1).real (Set.Icc (-1) 1) ^ M * ε
      = μ.real E * ε := by rw [hμE]
    _ ≤ ε * μ.real {ω | ε ≤ |emPath (fun S _ => -S ^ 3) (fun _ _ => 1) h x₀
          (fun n => Z n ω) (M + 1)| ^ p} := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)
    _ ≤ _ := hmarkov

/-- **The moments of the explicit Euler–Maruyama scheme for `dS = −S³ dt + dW` diverge** (Giles
2015, §5.6, p. 44: "Hutzenthaler, Jentzen and Kloeden (2013), who are concerned with SDEs such as
`dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the volatility.  This
again leads to numerical instability if a uniform timestep is used").  The theorem is Hutzenthaler,
Jentzen and Kloeden's (Proc. R. Soc. A 467 (2011), 1563–1576), not the survey's, which cites it.
For every initial value `x₀`, horizon `T > 0` and exponent `p > 0`: if for each number of steps `N`
the variables `Z_{N,0}, …, Z_{N,N−1}` are independent with law `N(0, 1)`, so that the Brownian
increments `ΔW_n = √(T/N) Z_{N,n}` are i.i.d. `N(0, T/N)`, then the explicit scheme
`X_{n+1} = X_n − h X_n³ + ΔW_n`, `X_0 = x₀`, `h = T/N` (`emPath` with drift `−S³` and volatility
`1`) satisfies `E|X_N|^p → ∞` as `N → ∞`.  HJK state it for `p ≥ 1` and general super-linearly
growing coefficients; this is the paper's example, for every `p > 0`.  The proof is the bound
`emCubic_moment_ge`, which grows like `exp(p 2^{N−1} log 2 − O(N²))`.  The variables for different
`N` may be coupled arbitrarily; measurability and `μ` being a probability measure follow from the
laws.  (The exact solution has finite moments of every order, which is not formalised here.) -/
theorem emCubic_moment_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (x₀ : ℝ)
    {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 0 < p) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    Tendsto (fun N : ℕ => ∫ ω, |emPath (fun S _ => -S ^ 3) (fun _ _ => 1) (T / N) x₀
      (fun n => Z N n ω) N| ^ p ∂μ) atTop atTop := by
  rw [← tendsto_add_atTop_iff_nat 1]
  set c := 2 + |x₀| + |x₀| ^ 3
  set q := (gaussianReal 0 1).real (Set.Icc (-1) 1)
  have hq0 : 0 < q := by
    refine lt_of_lt_of_le ?_ (le_gaussianReal_real_Icc (-1) 1)
    positivity
  set α := c / T with hα
  set β := c / T + 1 with hβ
  let Φ : ℕ → ℝ := fun M => -(α * M + β) ^ 2 / 2 + M * Real.log q + 2 ^ M * Real.log 2 * p
  have hΦ : Tendsto Φ atTop atTop := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (one_lt_two : (1 : ℝ) < 2)
    have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 (one_lt_two : (1 : ℝ) < 2)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (one_lt_two : (1 : ℝ) < 2)
    have hB := (tendsto_const_nhds (x := Real.log 2 * p)).add
      (((h1.const_mul (Real.log q - α * β)).sub (h2.const_mul (α ^ 2 / 2))).sub
        (h0.const_mul (β ^ 2 / 2)))
    simp only [mul_zero, sub_zero, add_zero] at hB
    have := (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)).atTop_mul_pos
      (by positivity : 0 < Real.log 2 * p) hB
    refine this.congr fun M => ?_
    simp only [Φ]
    field_simp
    ring
  have hL : Tendsto (fun M : ℕ => (√(2 * π))⁻¹ * Real.exp (Φ M)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp hΦ).const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hL
  filter_upwards [eventually_ge_atTop ⌈T⌉₊] with M hM
  have hTM : T ≤ ((M + 1 : ℕ) : ℝ) := by
    have h1 := Nat.le_ceil T
    have h2 : (⌈T⌉₊ : ℝ) ≤ M := Nat.cast_le.mpr hM
    push_cast
    linarith
  have hb := emCubic_moment_ge x₀ hT hp.le hTM (Z (M + 1)) (hZ (M + 1)) (hind (M + 1))
  simp only [Nat.add_sub_cancel] at hb
  refine le_trans ?_ hb
  have ha0 : 0 ≤ c * ((M + 1 : ℕ) : ℝ) / T := by positivity
  have htail := le_gaussianReal_real_Ici (c * ((M + 1 : ℕ) : ℝ) / T)
  rw [abs_of_nonneg ha0] at htail
  have e1 : c * ((M + 1 : ℕ) : ℝ) / T + 1 = α * M + β := by
    rw [hα, hβ]
    push_cast
    field_simp
    ring
  rw [e1] at htail
  have e2 : (√(2 * π))⁻¹ * Real.exp (Φ M) = Real.exp (-(α * M + β) ^ 2 / 2) / √(2 * π) *
      q ^ M * ((2 : ℝ) ^ 2 ^ M) ^ p := by
    simp only [Φ]
    rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos (by positivity), Real.log_pow,
      Real.exp_nat_mul, Real.exp_log hq0]
    push_cast
    ring
  rw [e2]
  gcongr

/-- **The mean absolute value of the explicit scheme for `dS = −S³ dt + dW` diverges** (Giles 2015,
§5.6, p. 44: "This again leads to numerical instability if a uniform timestep is used"; theorem of
Hutzenthaler, Jentzen and Kloeden, Proc. R. Soc. A 467 (2011), cited by the survey through their
2013 paper).  The case `p = 1` of `emCubic_moment_tendsto_atTop`: with i.i.d. `N(0, T/N)` increments
`√(T/N) Z_{N,n}`, the explicit Euler–Maruyama approximation `X_N` of `S_T` satisfies
`E|X_N| → ∞` as `N → ∞`, for every `x₀` and `T > 0`. -/
theorem emCubic_integral_abs_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (x₀ : ℝ) {T : ℝ} (hT : 0 < T) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    Tendsto (fun N : ℕ => ∫ ω, |emPath (fun S _ => -S ^ 3) (fun _ _ => 1) (T / N) x₀
      (fun n => Z N n ω) N| ∂μ) atTop atTop := by
  simpa using emCubic_moment_tendsto_atTop x₀ hT one_pos Z hZ hind

/-! ### The tamed scheme -/

/-- The tamed Euler–Maruyama scheme (Giles 2015, §5.6, p. 44: "a slight modification to the
Euler-Maruyama discretisation which limits the size of the drift term on each level of
approximation when `S_t` is large"; the taming of Hutzenthaler, Jentzen and Kloeden, Ann. Appl.
Probab. 22 (2012)): `X_0 = x₀` and `X_{n+1} = X_n + h b(X_n)/(1 + h|b(X_n)|) + √h z_n`, i.e. the
tamed drift step `tamedDriftStep` plus the Brownian increment `√h z_n`. -/
noncomputable def tamedPath (b : ℝ → ℝ) (h x₀ : ℝ) (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => tamedDriftStep b h (tamedPath b h x₀ z n) + √h * z n

/-- For an inward drift (`S b(S) ≤ 0`) and `h ≥ 0`, the tamed scheme never leaves
`max(|x₀|, 1) + ∑_{k<n} √h |z_k|`: a tamed step does not leave `[−max(|S|, 1), max(|S|, 1)]`
(`abs_tamedDriftStep_le`). -/
lemma tamedPath_abs_le {b : ℝ → ℝ} (hb : ∀ S, S * b S ≤ 0) {h : ℝ} (hh : 0 ≤ h) (x₀ : ℝ)
    (z : ℕ → ℝ) (n : ℕ) :
    |tamedPath b h x₀ z n| ≤ max |x₀| 1 + ∑ k ∈ Finset.range n, √h * |z k| := by
  induction n with
  | zero => simp [tamedPath]
  | succ n ih =>
    show |tamedDriftStep b h (tamedPath b h x₀ z n) + √h * z n| ≤ _
    rw [Finset.sum_range_succ]
    have h1 := abs_tamedDriftStep_le hb hh (tamedPath b h x₀ z n)
    have h2 : 0 ≤ ∑ k ∈ Finset.range n, √h * |z k| :=
      Finset.sum_nonneg fun k _ => by positivity
    have h3 : max |tamedPath b h x₀ z n| 1 ≤ max |x₀| 1 + ∑ k ∈ Finset.range n, √h * |z k| :=
      max_le ih (by linarith [le_max_right |x₀| 1])
    have h4 := abs_add_le (tamedDriftStep b h (tamedPath b h x₀ z n)) (√h * z n)
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg h)] at h4
    linarith

/-- The tamed scheme at step `n` depends only on the increments `z_0, …, z_{n−1}`. -/
lemma tamedPath_congr (b : ℝ → ℝ) (h x₀ : ℝ) {z z' : ℕ → ℝ} {n : ℕ}
    (hz : ∀ k < n, z k = z' k) : tamedPath b h x₀ z n = tamedPath b h x₀ z' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show tamedDriftStep b h (tamedPath b h x₀ z n) + √h * z n =
      tamedDriftStep b h (tamedPath b h x₀ z' n) + √h * z' n
    rw [ih fun k hk => hz k (by omega), hz n (by omega)]

/-- The tamed step is measurable for a measurable drift. -/
lemma measurable_tamedDriftStep {b : ℝ → ℝ} (hbm : Measurable b) (h : ℝ) :
    Measurable (tamedDriftStep b h) := by
  unfold tamedDriftStep
  fun_prop

/-- The tamed scheme at step `n` is a measurable function of the increments. -/
lemma measurable_tamedPath {b : ℝ → ℝ} (hbm : Measurable b) (h x₀ : ℝ) (n : ℕ) :
    Measurable fun z : ℕ → ℝ => tamedPath b h x₀ z n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ((measurable_tamedDriftStep hbm h).comp ih).add
      (measurable_const.mul (measurable_pi_apply n))

/-- `E|Z| ≤ 1` for a standard normal `Z` (from `|z| ≤ (1 + z²)/2` and `E Z² = 1`). -/
lemma integral_abs_gaussian_le_one : ∫ x, |x| ∂gaussianReal 0 1 ≤ 1 := by
  have hi : Integrable (fun x : ℝ => (1 + x ^ 2) / 2) (gaussianReal 0 1) :=
    ((integrable_const 1).add integrable_sq_gaussian).div_const 2
  calc ∫ x, |x| ∂gaussianReal 0 1 ≤ ∫ x, (1 + x ^ 2) / 2 ∂gaussianReal 0 1 :=
        integral_mono integrable_id_gaussian.abs hi
          (fun x => by nlinarith [sq_nonneg (|x| - 1), sq_abs x])
    _ = 1 := by
        rw [integral_div, integral_add (integrable_const 1) integrable_sq_gaussian,
          integral_sq_gaussian]
        simp

/-- **The tamed scheme does not explode** (Giles 2015, §5.6, p. 44: "Their solution is to introduce
a slight modification to the Euler-Maruyama discretisation which limits the size of the drift term
on each level of approximation when `S_t` is large, to avoid this instability"; the tamed scheme is
that of Hutzenthaler, Jentzen and Kloeden, Ann. Appl. Probab. 22 (2012)).  For every measurable
drift pointing towards `0` (`S b(S) ≤ 0`, as `b(S) = −S³`), `T ≥ 0`, `N` steps of size `h = T/N`
and increments `√h Z_n` with `Z_n ∼ N(0, 1)` (independence is not needed), the tamed scheme
`tamedPath` is integrable and `E|X_N| ≤ max(|x₀|, 1) + √(TN)`, a bound growing like `√N`, against
`E|X_N| → ∞` doubly exponentially fast for the explicit scheme (`emCubic_moment_ge`,
`emCubic_moment_tendsto_atTop`).  The uniform bound for the cubic drift is
`tamedCubic_second_moment_le`; the uniform moment bounds of HJK for general drifts are not
formalised. -/
theorem tamedPath_integral_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {b : ℝ → ℝ} (hb : ∀ S, S * b S ≤ 0) (hbm : Measurable b) (x₀ : ℝ)
    {T : ℝ} (hT : 0 ≤ T) (N : ℕ) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1) :
    Integrable (fun ω => tamedPath b (T / N) x₀ (fun n => Z n ω) N) μ ∧
      ∫ ω, |tamedPath b (T / N) x₀ (fun n => Z n ω) N| ∂μ ≤ max |x₀| 1 + √(T * N) := by
  set h := T / (N : ℝ) with hhdef
  have hh : 0 ≤ h := by positivity
  have hm : ∀ n < N, AEMeasurable (Z n) μ := fun n hn =>
    aemeasurable_of_map_eq_gaussianReal (hZ n hn)
  have hZi : ∀ n < N, Integrable (fun ω => |Z n ω|) μ := fun n hn =>
    ((memLp_of_map_eq_gaussianReal (hZ n hn) 1 ENNReal.one_ne_top).integrable le_rfl).abs
  have hEZ : ∀ n < N, ∫ ω, |Z n ω| ∂μ ≤ 1 := fun n hn => by
    rw [← integral_map (hm n hn) continuous_abs.aestronglyMeasurable, hZ n hn]
    exact integral_abs_gaussian_le_one
  have hstep := measurable_tamedDriftStep hbm h
  have hXm : ∀ k ≤ N, AEMeasurable (fun ω => tamedPath b h x₀ (fun n => Z n ω) k) μ := by
    intro k
    induction k with
    | zero => intro _; exact aemeasurable_const
    | succ k ih =>
      intro hk
      exact (hstep.comp_aemeasurable (ih (by omega))).add ((hm k (by omega)).const_mul _)
  have hsum : Integrable (fun ω => ∑ k ∈ Finset.range N, √h * |Z k ω|) μ :=
    integrable_finsetSum _ fun k hk => (hZi k (Finset.mem_range.mp hk)).const_mul _
  have hg : Integrable (fun ω => max |x₀| 1 + ∑ k ∈ Finset.range N, √h * |Z k ω|) μ :=
    (integrable_const _).add hsum
  have hbound : ∀ ω, |tamedPath b h x₀ (fun n => Z n ω) N| ≤
      max |x₀| 1 + ∑ k ∈ Finset.range N, √h * |Z k ω| := fun ω =>
    tamedPath_abs_le hb hh x₀ _ N
  have hint : Integrable (fun ω => tamedPath b h x₀ (fun n => Z n ω) N) μ :=
    hg.mono' (hXm N le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbound ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, |tamedPath b h x₀ (fun n => Z n ω) N| ∂μ
      ≤ ∫ ω, (max |x₀| 1 + ∑ k ∈ Finset.range N, √h * |Z k ω|) ∂μ :=
        integral_mono hint.abs hg hbound
    _ = max |x₀| 1 + ∑ k ∈ Finset.range N, √h * ∫ ω, |Z k ω| ∂μ := by
        rw [integral_add (integrable_const _) hsum, integral_const, probReal_univ, one_smul,
          integral_finsetSum _ fun k hk => (hZi k (Finset.mem_range.mp hk)).const_mul _]
        simp_rw [integral_const_mul]
    _ ≤ max |x₀| 1 + ∑ k ∈ Finset.range N, √h * 1 := by
        gcongr with k hk
        exact hEZ k (Finset.mem_range.mp hk)
    _ = max |x₀| 1 + √(T * N) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · simp [h0]
        · have hN0 : (0 : ℝ) < N := by exact_mod_cast h0
          have e : T * N = h * (N : ℝ) ^ 2 := by
            rw [hhdef]
            field_simp
          rw [e, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hN0.le]
          ring

/-- For `0 ≤ h ≤ 54` the tamed step for the drift `−S³` does not increase `|S|`: it is
`S(1 − u)` with `u = hS²/(1 + h|S|³) ∈ [0, 2]`, since `h(|S|² − 2|S|³) ≤ h/27 ≤ 2`. -/
lemma abs_tamedCubic_le {h : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 54) (S : ℝ) :
    |tamedDriftStep (fun S => -S ^ 3) h S| ≤ |S| := by
  unfold tamedDriftStep
  have hD : 0 < 1 + h * |-S ^ 3| := by positivity
  have e : S + h * -S ^ 3 / (1 + h * |-S ^ 3|) =
      S * ((1 + h * |-S ^ 3| - h * S ^ 2) / (1 + h * |-S ^ 3|)) := by
    field_simp
    ring
  have ha : |-S ^ 3| = |S| ^ 3 := by rw [abs_neg, abs_pow]
  have hS2 : S ^ 2 = |S| ^ 2 := (sq_abs S).symm
  have key : h * |S| ^ 2 ≤ 2 + 2 * (h * |S| ^ 3) := by
    have h0 : 0 ≤ h * ((1 - 3 * |S|) ^ 2 * (1 + 6 * |S|)) :=
      mul_nonneg hh0 (mul_nonneg (sq_nonneg _) (by positivity))
    nlinarith
  have hnum : |1 + h * |-S ^ 3| - h * S ^ 2| ≤ 1 + h * |-S ^ 3| := by
    rw [abs_le]
    constructor
    · rw [ha, hS2]
      linarith
    · nlinarith [sq_nonneg S]
  rw [e, abs_mul, abs_div, abs_of_pos hD]
  calc |S| * (|1 + h * |-S ^ 3| - h * S ^ 2| / (1 + h * |-S ^ 3|)) ≤ |S| * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_one hD).mpr hnum) (abs_nonneg _)
    _ = |S| := mul_one _

/-- **The tamed cubic step is non-expansive exactly for `h ≤ 54`** (Giles 2015, §5.6, p. 44: the
taming "limits the size of the drift term on each level of approximation when `S_t` is large, to
avoid this instability").  For the drift `−S³` and `h ≥ 0`, the tamed step
`S ↦ S − hS³/(1 + h|S|³)` satisfies `|tamedDriftStep(S)| ≤ |S|` for every `S` if and only if
`h ≤ 54`; for `h > 54` it fails at `S = 1/3`.  The explicit step `S ↦ S − hS³` is non-expansive
only for `hS² ≤ 2` (`eulerCubic_bounded`, `eulerCubic_tendsto_atTop`): no timestep `h > 0` makes
it non-expansive on all of `ℝ`. -/
theorem tamedCubic_nonexpansive_iff {h : ℝ} (hh0 : 0 ≤ h) :
    (∀ S, |tamedDriftStep (fun S => -S ^ 3) h S| ≤ |S|) ↔ h ≤ 54 := by
  refine ⟨fun H => le_of_not_gt fun hlt => ?_, fun hh S => abs_tamedCubic_le hh0 hh S⟩
  have h27 : 0 < 27 + h := by linarith
  have e : tamedDriftStep (fun S => -S ^ 3) h (1 / 3) = 1 / 3 - h / (27 + h) := by
    unfold tamedDriftStep
    rw [show |-((1 : ℝ) / 3) ^ 3| = 1 / 27 by norm_num]
    field_simp
    ring
  have h1 : 2 / 3 < h / (27 + h) := by
    rw [lt_div_iff₀ h27]
    linarith
  have h2 := H (1 / 3)
  rw [e, abs_of_neg (by linarith), abs_of_pos (by norm_num)] at h2
  linarith

/-- **Taming removes the instability: a uniform second-moment bound** (Giles 2015, §5.6, p. 44:
"Their solution is to introduce a slight modification to the Euler-Maruyama discretisation which
limits the size of the drift term on each level of approximation when `S_t` is large, to avoid this
instability"; the tamed scheme is that of Hutzenthaler, Jentzen and Kloeden, Ann. Appl. Probab. 22
(2012)).  For `dS = −S³ dt + dW`, `T ≥ 0` and `N ≥ T/54` steps of size `h = T/N`, driven by
independent `Z_0, …, Z_{N−1}` with law `N(0, 1)` (increments `√h Z_n`), the tamed scheme
`X_{n+1} = X_n − hX_n³/(1 + h|X_n|³) + √h Z_n` (`tamedPath`) is square integrable and
`E X_N² ≤ x₀² + T`, uniformly in `N` (the bound that Itô's formula gives for the exact solution,
not formalised here), against `E|X_N| → ∞` for the explicit scheme
(`emCubic_moment_tendsto_atTop`).  Proof: the tamed step does not increase `|S|` for `h ≤ 54`
(`tamedCubic_nonexpansive_iff`), and `X_n` is independent of `Z_n`, so
`E X_{n+1}² ≤ E X_n² + h`.  The condition `N ≥ T/54` only excludes very coarse grids, but this
exact bound needs it: for `N = 1`, `T = 60`, `x₀ = 1/3` the tamed step maps `1/3` to `−31/87` and
`E X_1² = (31/87)² + 60 = x₀² + T + 40/2523`.  HJK's bounds on all moments for general drifts are
not formalised. -/
theorem tamedCubic_second_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (x₀ : ℝ)
    {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (hN : T ≤ 54 * N) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    MemLp (fun ω => tamedPath (fun S => -S ^ 3) (T / N) x₀ (fun n => Z n ω) N) 2 μ ∧
      ∫ ω, tamedPath (fun S => -S ^ 3) (T / N) x₀ (fun n => Z n ω) N ^ 2 ∂μ ≤ x₀ ^ 2 + T := by
  have hprob : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  set h := T / (N : ℝ) with hhdef
  have hh0 : 0 ≤ h := by positivity
  have hh54 : h ≤ 54 := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [hhdef, h0]
    · rw [hhdef, div_le_iff₀ (by exact_mod_cast h0)]
      linarith
  set b : ℝ → ℝ := fun S => -S ^ 3
  have hbm : Measurable b := by fun_prop
  have hm : ∀ n < N, AEMeasurable (Z n) μ := fun n hn =>
    aemeasurable_of_map_eq_gaussianReal (hZ n hn)
  have hZ2 : ∀ n < N, MemLp (Z n) 2 μ := fun n hn =>
    memLp_of_map_eq_gaussianReal (hZ n hn) 2 ENNReal.ofNat_ne_top
  have hEZ : ∀ n < N, ∫ ω, Z n ω ∂μ = 0 := fun n hn => by
    have h1 : ∫ y, y ∂(μ.map (Z n)) = ∫ ω, Z n ω ∂μ :=
      integral_map (hm n hn) aestronglyMeasurable_id
    rw [← h1, hZ n hn, integral_id_gaussianReal]
  have hEZ2 : ∀ n < N, ∫ ω, Z n ω ^ 2 ∂μ = 1 := fun n hn => by
    rw [← integral_map (hm n hn) (continuous_pow 2).aestronglyMeasurable, hZ n hn,
      integral_sq_gaussian]
  have hstep := measurable_tamedDriftStep hbm h
  have hcontr : ∀ S, |tamedDriftStep b h S| ≤ |S| := abs_tamedCubic_le hh0 hh54
  have hY2 : ∀ n, MemLp (fun ω => tamedPath b h x₀ (fun k => Z k ω) n) 2 μ →
      MemLp (fun ω => tamedDriftStep b h (tamedPath b h x₀ (fun k => Z k ω) n)) 2 μ :=
    fun n hX => hX.of_le (hstep.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simp only [Real.norm_eq_abs]; exact hcontr _)
  have hX2 : ∀ n ≤ N, MemLp (fun ω => tamedPath b h x₀ (fun k => Z k ω) n) 2 μ := by
    intro n
    induction n with
    | zero => intro _; exact memLp_const x₀
    | succ n ih =>
      intro hn
      exact (hY2 n (ih (by omega))).add ((hZ2 n (by omega)).const_mul √h)
  have hindep : ∀ n < N, IndepFun
      (fun ω => tamedDriftStep b h (tamedPath b h x₀ (fun k => Z k ω) n)) (Z n) μ := by
    intro n hn
    let S : Finset (Fin N) := Finset.Iio ⟨n, hn⟩
    let S' : Finset (Fin N) := {⟨n, hn⟩}
    have hSS : Disjoint S S' := by simp [S, S']
    have h1 := hind.indepFun_finset₀ S S' hSS (fun i => hm i i.2)
    let ext : (S → ℝ) → ℕ → ℝ := fun y k =>
      if hk : k < n then y ⟨⟨k, by omega⟩, Finset.mem_Iio.mpr hk⟩ else 0
    have hext : Measurable ext := by
      refine measurable_pi_lambda _ fun k => ?_
      by_cases hk : k < n
      · simp only [ext, dif_pos hk]
        exact measurable_pi_apply _
      · simp only [ext, dif_neg hk]
        exact measurable_const
    let φ : (S → ℝ) → ℝ := fun y => tamedDriftStep b h (tamedPath b h x₀ (ext y) n)
    let ψ : (S' → ℝ) → ℝ := fun y => y ⟨⟨n, hn⟩, Finset.mem_singleton_self _⟩
    have hφ : Measurable φ := hstep.comp ((measurable_tamedPath hbm h x₀ n).comp hext)
    have hψ : Measurable ψ := measurable_pi_apply _
    have h2 := h1.comp hφ hψ
    convert h2 using 1
    · funext ω
      simp only [Function.comp, φ]
      congr 1
      exact tamedPath_congr b h x₀ fun k hk => by simp [ext, hk]
    · rfl
  have hrec : ∀ n ≤ N, ∫ ω, tamedPath b h x₀ (fun k => Z k ω) n ^ 2 ∂μ ≤ x₀ ^ 2 + n * h := by
    intro n
    induction n with
    | zero =>
      intro _
      simp [tamedPath]
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      set Y := fun ω => tamedDriftStep b h (tamedPath b h x₀ (fun k => Z k ω) n)
      have hYm := hY2 n (hX2 n hn'.le)
      have hYZ : ∫ ω, Y ω * Z n ω ∂μ = 0 := by
        rw [(hindep n hn').integral_fun_mul_eq_mul_integral hYm.aestronglyMeasurable
          (hm n hn').aestronglyMeasurable, hEZ n hn', mul_zero]
      have e : ∀ ω, tamedPath b h x₀ (fun k => Z k ω) (n + 1) ^ 2 =
          Y ω ^ 2 + 2 * √h * (Y ω * Z n ω) + h * Z n ω ^ 2 := fun ω => by
        show (Y ω + √h * Z n ω) ^ 2 = _
        rw [add_sq, mul_pow, Real.sq_sqrt hh0]
        ring
      have iY2 : Integrable (fun ω => Y ω ^ 2) μ := hYm.integrable_sq
      have iYZ : Integrable (fun ω => Y ω * Z n ω) μ := hYm.integrable_mul (hZ2 n hn')
      have iZ2 : Integrable (fun ω => Z n ω ^ 2) μ := (hZ2 n hn').integrable_sq
      have i1 : Integrable (fun ω => Y ω ^ 2 + 2 * √h * (Y ω * Z n ω)) μ :=
        iY2.add (iYZ.const_mul _)
      calc ∫ ω, tamedPath b h x₀ (fun k => Z k ω) (n + 1) ^ 2 ∂μ
          = ∫ ω, Y ω ^ 2 ∂μ + 2 * √h * ∫ ω, Y ω * Z n ω ∂μ + h * ∫ ω, Z n ω ^ 2 ∂μ := by
            simp_rw [e]
            rw [integral_add i1 (iZ2.const_mul _),
              integral_add iY2 (iYZ.const_mul _), integral_const_mul, integral_const_mul]
        _ = ∫ ω, Y ω ^ 2 ∂μ + h := by rw [hYZ, hEZ2 n hn']; ring
        _ ≤ ∫ ω, tamedPath b h x₀ (fun k => Z k ω) n ^ 2 ∂μ + h :=
            add_le_add_left (integral_mono iY2 (hX2 n hn'.le).integrable_sq
              fun ω => sq_le_sq.mpr (hcontr _)) h
        _ ≤ x₀ ^ 2 + n * h + h := by linarith [ih hn'.le]
        _ = x₀ ^ 2 + ((n + 1 : ℕ) : ℝ) * h := by push_cast; ring
  refine ⟨hX2 N le_rfl, (hrec N le_rfl).trans ?_⟩
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · simp [h0]
    simp [h0] at hN
    linarith
  · rw [hhdef, mul_div_cancel₀ _ (by exact_mod_cast h0.ne')]

end MLMC
