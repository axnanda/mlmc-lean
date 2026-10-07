import MlmcLean.EulerSuperlinear
import MlmcLean.GBMMilstein

/-!
# Giles 2015, §5.6: drift-implicit and integrating-factor schemes

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.6 "Stiff and
highly nonlinear SDEs" (pp. 43–44), p. 44: "Other approaches to these problems include the use of
drift-implicit methods (Dereich, Neuenkirch and Szpruch 2012, Higham, Mao and Stuart 2002), or a
change or [sic] variables equivalent to the use of an integrating factor in ODEs (see the Heston
treatment in (Giles 2008a) which was suggested by Mark Broadie)."  ("change or variables", for
"change of variables", is a typo in the survey, docs/giles2015.txt l. 1903; it is marked `[sic]` in
every quotation below.)  "These problems" are the instability of the explicit Euler–Maruyama scheme
for a stiff mean-reverting drift (`emMeanRevert_unbounded` in `MlmcLean/SDEExtras.lean`) and for
the super-linear drift of `dS_t = −S_t³ dt + dW_t` (`eulerCubic_tendsto_atTop`,
`emCubic_moment_tendsto_atTop`).  The survey states no theorem; this file proves the elementary
facts behind the two remedies it names.

* **Well-posedness of the implicit step.**  For a continuous drift `a` with a one-sided Lipschitz
  constant `K`, `(a(x) − a(y))(x − y) ≤ K(x − y)²` (Higham, Mao and Stuart's condition; `K = 0` for
  a non-increasing drift such as `−S³`), and `0 ≤ h`, `hK < 1`, the implicit equation
  `y = x + h a(y) + c` has exactly one solution, `implicitStep a h (x + c)`
  (`existsUnique_implicitStep`), which is `1/(1 − hK)`-Lipschitz in `x + c`
  (`abs_implicitStep_sub_le`), hence continuous and measurable in `(x, c)`
  (`continuous_implicitStep_add`).  For a continuous drift pointing towards `0`, `y a(y) ≤ 0`, and
  `h ≥ 0`, the equation `y = r + h a(y)` has a solution (unique or not) and
  `|implicitStep a h r| ≤ |r|`, with no one-sided Lipschitz condition (`abs_implicitStep_le`).
* **The deterministic analogue** (`σ = 0`, `a(x) = −x³`).  The implicit Euler iterates do not
  increase `|x|` and tend to `0` for every `h > 0` (`implicitCubic_abs_antitone`,
  `implicitCubic_tendsto_zero`), like the solutions of `x′ = −x³`, while the explicit iterates are
  bounded if and only if `h x₀² ≤ 2`, and tend to `∞` in absolute value when `h x₀² > 2`
  (`implicitCubic_stable_explicitCubic_threshold`).
* **Moment bounds uniform in the timestep.**  The drift-implicit path
  `X_{n+1} = implicitStep a h (X_n + σ√h Z_n)` (`implicitPath`), i.e.
  `X_{n+1} = X_n + h a(X_{n+1}) + σ√h Z_n` (`implicitPath_succ_eq`), with `Z_n` independent
  `N(0, 1)` and additive noise (constant `σ`), has a finite fourth moment and satisfies
  `E X_n² ≤ x₀² + σ²nh` and `E X_n⁴ ≤ x₀⁴ + 6x₀²σ²nh + 3σ⁴(nh)²`, the moments of
  `x₀ + σW_{nh}` (`implicitPath_moments_le`); for `dS = −S³ dt + dW` these bounds hold for every
  number of steps, while the moments of the explicit scheme diverge (`implicitCubic_moments_le`,
  `implicit_vs_explicit_cubic_moments`).
* **The integrating factor for a stiff linear drift** `a(x) = −Lx`.  The scheme
  `X_{n+1} = e^{−Lh}(X_n + σ√h Z_n)` (`intFactorPath`) is square integrable with
  `E X_n² ≤ max(x₀², σ²/(2L))` for every `h ≥ 0` and `n` (`intFactorPath_second_moment_le`), with
  an exact formula (`intFactorPath_second_moment_eq`), while the mean square of the explicit
  Euler–Maruyama scheme tends to `∞` when `Lh > 2` (`emLinear_second_moment_tendsto_atTop`).

Not formalised: the strong convergence orders of drift-implicit schemes for general SDEs (Higham,
Mao and Stuart 2002; Dereich, Neuenkirch and Szpruch 2012), which need Itô calculus and the
continuous-time solution; state-dependent (multiplicative) noise; and the Heston treatment of
Giles (2008a).
-/

open MeasureTheory ProbabilityTheory Filter Real Topology
open scoped ENNReal

namespace MLMC

/-! ### The implicit step -/

/-- The drift-implicit (backward Euler) step for the drift `a` and the timestep `h` (Giles 2015,
§5.6, p. 44: "the use of drift-implicit methods"): `implicitStep a h r` is a solution `y` of the
implicit equation `y = r + h a(y)`, i.e. a preimage of `r` under `y ↦ y − h a(y)` (Mathlib's
`Function.invFun`).  One step of the
drift-implicit Euler–Maruyama scheme from `x` with Brownian increment `c` is
`implicitStep a h (x + c)`.  The equation is uniquely solvable under the hypotheses of
`existsUnique_implicitStep`, and solvable (perhaps not uniquely) for a continuous drift with
`y a(y) ≤ 0` and `h ≥ 0` (`exists_implicit_of_dissipative`); `implicitStep` then returns a solution
(`implicitStep_eq_of_exists`).  When there is no solution the value is unspecified. -/
noncomputable def implicitStep (a : ℝ → ℝ) (h r : ℝ) : ℝ :=
  Function.invFun (fun y => y - h * a y) r

/-- The one-sided Lipschitz condition makes `y ↦ y − h a(y)` strongly monotone:
`(1 − hK)(x − y)² ≤ ((x − h a(x)) − (y − h a(y)))(x − y)` for `h ≥ 0`. -/
lemma implicitResidual_monotone {a : ℝ → ℝ} {K h : ℝ}
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hh : 0 ≤ h) (x y : ℝ) :
    (1 - h * K) * (x - y) ^ 2 ≤ ((x - h * a x) - (y - h * a y)) * (x - y) := by
  have e : ((x - h * a x) - (y - h * a y)) * (x - y) =
      (x - y) ^ 2 - h * ((a x - a y) * (x - y)) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left (hK x y) hh]

/-- Moving the argument up by `d ≥ 0` moves `y − h a(y)` up by at least `(1 − hK) d`. -/
lemma implicitResidual_ge {a : ℝ → ℝ} {K h : ℝ}
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hh : 0 ≤ h) (x : ℝ) {d : ℝ}
    (hd : 0 ≤ d) :
    (1 - h * K) * d ≤ ((x + d) - h * a (x + d)) - (x - h * a x) := by
  rcases hd.eq_or_lt with rfl | hd
  · simp
  have h1 := implicitResidual_monotone hK hh (x + d) x
  rw [add_sub_cancel_left] at h1
  refine le_of_mul_le_mul_right ?_ hd
  nlinarith

/-- Existence for the implicit equation: under the hypotheses of `existsUnique_implicitStep`,
`y − h a(y) = r` has a solution (intermediate value theorem on `[−d, d]`,
`d = |r − (0 − h a(0))|/(1 − hK)`). -/
lemma exists_implicit {a : ℝ → ℝ} {K h : ℝ} (ha : Continuous a)
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hh : 0 ≤ h) (hhK : h * K < 1)
    (r : ℝ) : ∃ y, y - h * a y = r := by
  set g : ℝ → ℝ := fun y => y - h * a y with hg
  have hgc : Continuous g := continuous_id.sub (continuous_const.mul ha)
  have hc : 0 < 1 - h * K := by linarith
  set d := |r - g 0| / (1 - h * K) with hd
  have hd0 : 0 ≤ d := by positivity
  have hcd : (1 - h * K) * d = |r - g 0| := by rw [hd]; field_simp
  have hup := implicitResidual_ge hK hh 0 hd0
  have hlo := implicitResidual_ge hK hh (-d) hd0
  rw [zero_add] at hup
  rw [neg_add_cancel] at hlo
  have h1 : g (-d) ≤ r := by
    have := neg_abs_le (r - g 0)
    simp only [hg] at this ⊢
    linarith
  have h2 : r ≤ g d := by
    have := le_abs_self (r - g 0)
    simp only [hg] at this ⊢
    linarith
  obtain ⟨y, -, hy⟩ := intermediate_value_Icc (by linarith : -d ≤ d) hgc.continuousOn ⟨h1, h2⟩
  exact ⟨y, hy⟩

/-- Existence for the implicit equation for a drift pointing towards `0`: if `a` is continuous,
`y a(y) ≤ 0` for all `y` and `h ≥ 0`, then `y − h a(y) = r` has a solution, with no one-sided
Lipschitz condition (intermediate value theorem on `[−b, b]`, `b = |r| + 1`: `a(b) ≤ 0 ≤ a(−b)`
gives `−b − h a(−b) ≤ −b < r < b ≤ b − h a(b)`). -/
lemma exists_implicit_of_dissipative {a : ℝ → ℝ} {h : ℝ} (ha : Continuous a)
    (hdiss : ∀ y, y * a y ≤ 0) (hh : 0 ≤ h) (r : ℝ) : ∃ y, y - h * a y = r := by
  have hb0 : 0 < |r| + 1 := by positivity
  have hab : a (|r| + 1) ≤ 0 := nonpos_of_mul_nonpos_right (hdiss _) hb0
  have hanb : 0 ≤ a (-(|r| + 1)) := nonneg_of_mul_nonpos_right (hdiss _) (by linarith)
  have hgc : Continuous (fun y => y - h * a y) := continuous_id.sub (continuous_const.mul ha)
  have h1 : -(|r| + 1) - h * a (-(|r| + 1)) ≤ r := by
    have := neg_abs_le r
    nlinarith [mul_nonneg hh hanb]
  have h2 : r ≤ (|r| + 1) - h * a (|r| + 1) := by
    have := le_abs_self r
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hh hab]
  obtain ⟨y, -, hy⟩ :=
    intermediate_value_Icc (by linarith : -(|r| + 1) ≤ |r| + 1) hgc.continuousOn ⟨h1, h2⟩
  exact ⟨y, hy⟩

/-- Whenever the implicit equation `y − h a(y) = r` has a solution, `implicitStep a h r` is one:
`implicitStep a h r = r + h a(implicitStep a h r)` (`Function.invFun_eq`). -/
lemma implicitStep_eq_of_exists {a : ℝ → ℝ} {h r : ℝ} (hex : ∃ y, y - h * a y = r) :
    implicitStep a h r = r + h * a (implicitStep a h r) := by
  have := Function.invFun_eq (f := fun y => y - h * a y) hex
  have e : implicitStep a h r - h * a (implicitStep a h r) = r := this
  linarith

/-- The implicit step solves its equation: `implicitStep a h r = r + h a(implicitStep a h r)`. -/
lemma implicitStep_eq {a : ℝ → ℝ} {K h : ℝ} (ha : Continuous a)
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hh : 0 ≤ h) (hhK : h * K < 1)
    (r : ℝ) : implicitStep a h r = r + h * a (implicitStep a h r) :=
  implicitStep_eq_of_exists (exists_implicit ha hK hh hhK r)

/-- Uniqueness for the implicit equation: two solutions of `y = r + h a(y)` coincide when `h ≥ 0`
and `hK < 1`. -/
lemma implicit_unique {a : ℝ → ℝ} {K h : ℝ}
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hh : 0 ≤ h) (hhK : h * K < 1)
    {r y y' : ℝ} (hy : y = r + h * a y) (hy' : y' = r + h * a y') : y = y' := by
  have h1 := implicitResidual_monotone hK hh y y'
  have e : (y - h * a y) - (y' - h * a y') = 0 := by linarith
  rw [e, zero_mul] at h1
  have hc : 0 < 1 - h * K := by linarith
  have h2 : (y - y') ^ 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith) hc) (sq_nonneg _)
  linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h2]

/-- **The drift-implicit step is well defined** (Giles 2015, §5.6, p. 44: "Other approaches to these
problems include the use of drift-implicit methods (Dereich, Neuenkirch and Szpruch 2012, Higham,
Mao and Stuart 2002)").  The survey gives no formula; one step of the drift-implicit Euler scheme
from `x` with increment `c` solves `y = x + h a(y) + c`.  For a continuous drift `a` satisfying the
one-sided Lipschitz condition `(a(x) − a(y))(x − y) ≤ K(x − y)²` (Higham, Mao and Stuart's
hypothesis; `K = 0` for every non-increasing drift, e.g. `a(y) = −y³` of the paper's example
`dS_t = −S_t³ dt + dW_t`), every `h ≥ 0` with `hK < 1` (every `h ≥ 0` when `K ≤ 0`) and all
`x, c`, this equation has exactly one solution, and it is `implicitStep a h (x + c)`.  Existence is
the intermediate value theorem, uniqueness the strong monotonicity of `y ↦ y − h a(y)`. -/
theorem existsUnique_implicitStep {a : ℝ → ℝ} {K h : ℝ} (ha : Continuous a)
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hh : 0 ≤ h) (hhK : h * K < 1)
    (x c : ℝ) :
    (∃! y, y = x + h * a y + c) ∧
      implicitStep a h (x + c) = x + h * a (implicitStep a h (x + c)) + c := by
  have hs := implicitStep_eq ha hK hh hhK (x + c)
  have hs' : implicitStep a h (x + c) = x + h * a (implicitStep a h (x + c)) + c := by linarith
  refine ⟨⟨implicitStep a h (x + c), hs', fun y hy => ?_⟩, hs'⟩
  exact implicit_unique hK hh hhK (r := x + c) (by linarith) hs

/-- **The drift-implicit step depends Lipschitz-continuously on the data** (Giles 2015, §5.6,
p. 44: "the use of drift-implicit methods").  Under the hypotheses of `existsUnique_implicitStep`,
`|implicitStep a h r − implicitStep a h r'| ≤ |r − r'|/(1 − hK)`; for a non-increasing drift
(`K = 0`) the step is non-expansive. -/
theorem abs_implicitStep_sub_le {a : ℝ → ℝ} {K h : ℝ} (ha : Continuous a)
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hh : 0 ≤ h) (hhK : h * K < 1)
    (r r' : ℝ) :
    |implicitStep a h r - implicitStep a h r'| ≤ |r - r'| / (1 - h * K) := by
  have hc : 0 < 1 - h * K := by linarith
  have hy := implicitStep_eq ha hK hh hhK r
  have hy' := implicitStep_eq ha hK hh hhK r'
  set y := implicitStep a h r
  set y' := implicitStep a h r'
  have h1 := implicitResidual_monotone hK hh y y'
  have e : (y - h * a y) - (y' - h * a y') = r - r' := by linarith
  rw [e] at h1
  rw [le_div_iff₀ hc]
  rcases (abs_nonneg (y - y')).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]
    exact abs_nonneg _
  refine le_of_mul_le_mul_right ?_ h0
  have h2 : (r - r') * (y - y') ≤ |r - r'| * |y - y'| := by
    rw [← abs_mul]
    exact le_abs_self _
  calc |y - y'| * (1 - h * K) * |y - y'| = (1 - h * K) * (y - y') ^ 2 := by
        rw [← sq_abs (y - y')]
        ring
    _ ≤ |r - r'| * |y - y'| := h1.trans h2

/-- Under the hypotheses of `existsUnique_implicitStep` the implicit step is continuous. -/
lemma continuous_implicitStep {a : ℝ → ℝ} {K h : ℝ} (ha : Continuous a)
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hh : 0 ≤ h) (hhK : h * K < 1) :
    Continuous (implicitStep a h) := by
  have hc : 0 < 1 - h * K := by linarith
  refine (LipschitzWith.of_dist_le' (K := (1 - h * K)⁻¹) fun r r' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, ← div_eq_inv_mul]
  exact abs_implicitStep_sub_le ha hK hh hhK r r'

/-- **The drift-implicit step is continuous, hence measurable, in `(x, c)`** (Giles 2015, §5.6,
p. 44: "the use of drift-implicit methods").  Under the hypotheses of `existsUnique_implicitStep`
the solution `(x, c) ↦ implicitStep a h (x + c)` of `y = x + h a(y) + c` is continuous and Borel
measurable, so the drift-implicit scheme driven by random increments is a random variable. -/
theorem continuous_implicitStep_add {a : ℝ → ℝ} {K h : ℝ} (ha : Continuous a)
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hh : 0 ≤ h) (hhK : h * K < 1) :
    Continuous (fun p : ℝ × ℝ => implicitStep a h (p.1 + p.2)) ∧
      Measurable (fun p : ℝ × ℝ => implicitStep a h (p.1 + p.2)) := by
  have hc : Continuous (fun p : ℝ × ℝ => implicitStep a h (p.1 + p.2)) :=
    (continuous_implicitStep ha hK hh hhK).comp (continuous_fst.add continuous_snd)
  exact ⟨hc, hc.measurable⟩

/-- **The drift-implicit step does not increase `|S|` for an inward drift** (Giles 2015, §5.6,
p. 44: "drift-implicit methods").  If the drift `a` is continuous and points towards `0`,
`y a(y) ≤ 0` for all `y` (as `a(y) = −y³`), then `|implicitStep a h r| ≤ |r|` for every `r` and
every `h ≥ 0`, however large.  No one-sided Lipschitz condition is needed here: the implicit
equation `y = r + h a(y)` has a solution by the intermediate value theorem
(`exists_implicit_of_dissipative`), so `implicitStep a h r` is one, and every solution satisfies
`y² = ry + h y a(y) ≤ |r||y|`.  (Without such a condition the solution may fail to be unique, and
the one-sided Lipschitz condition of `existsUnique_implicitStep` is used elsewhere for uniqueness
and measurability.)  Continuity and `h ≥ 0` are needed: for `h < 0`, or for a discontinuous drift
such as `−sign(y)`, the equation can have no solution or solutions with `|y| > |r|`.  The explicit
step `S ↦ S + h a(S)` has no such property (`eulerCubic_tendsto_atTop`). -/
theorem abs_implicitStep_le {a : ℝ → ℝ} {h : ℝ} (ha : Continuous a) (hdiss : ∀ y, y * a y ≤ 0)
    (hh : 0 ≤ h) (r : ℝ) : |implicitStep a h r| ≤ |r| := by
  have hy := implicitStep_eq_of_exists (exists_implicit_of_dissipative ha hdiss hh r)
  set y := implicitStep a h r
  have h1 : y ^ 2 ≤ r * y := by
    have e : y ^ 2 = r * y + h * (y * a y) := by linear_combination y * hy
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hh (hdiss y)]
  have h2 : |y| ^ 2 ≤ |r| * |y| := by
    rw [sq_abs, ← abs_mul]
    exact h1.trans (le_abs_self _)
  rcases (abs_nonneg y).eq_or_lt with h0 | h0
  · rw [← h0]
    exact abs_nonneg r
  · exact le_of_mul_le_mul_right (by nlinarith) h0

/-! ### The deterministic analogue: implicit against explicit Euler for `x′ = −x³` -/

/-- The cubic drift `−y³` is non-increasing: it satisfies the one-sided Lipschitz condition with
`K = 0`, since `(−x³ + y³)(x − y) = −(x − y)²((x + y/2)² + 3y²/4)`. -/
lemma cubic_oneSidedLipschitz (x y : ℝ) :
    ((fun y : ℝ => -y ^ 3) x - (fun y : ℝ => -y ^ 3) y) * (x - y) ≤ 0 * (x - y) ^ 2 := by
  have e : (-x ^ 3 - -y ^ 3) * (x - y) = -((x - y) ^ 2 * ((x + y / 2) ^ 2 + 3 / 4 * y ^ 2)) := by
    ring
  simp only [e, zero_mul, neg_nonpos]
  positivity

/-- The cubic drift `−y³` is continuous. -/
lemma continuous_cubicDrift : Continuous (fun y : ℝ => -y ^ 3) := by fun_prop

/-- The cubic drift `−y³` points towards `0`: `y · (−y³) = −y⁴ ≤ 0`. -/
lemma cubic_dissipative (y : ℝ) : y * (fun y : ℝ => -y ^ 3) y ≤ 0 := by
  have e : y * -y ^ 3 = -(y ^ 2) ^ 2 := by ring
  simp only [e, neg_nonpos]
  positivity

/-- One implicit step for the drift `−y³` from `r` to `y` satisfies `|r| = |y| + h|y|³`: from
`r = y(1 + hy²)`. -/
lemma implicitCubic_abs_eq {h : ℝ} (hh : 0 ≤ h) (r : ℝ) :
    |r| = |implicitStep (fun y => -y ^ 3) h r| +
      h * |implicitStep (fun y => -y ^ 3) h r| ^ 3 := by
  have hy := implicitStep_eq continuous_cubicDrift cubic_oneSidedLipschitz hh
    (by norm_num : h * 0 < 1) r
  set y := implicitStep (fun y => -y ^ 3) h r
  have e : r = y * (1 + h * |y| ^ 2) := by
    rw [sq_abs]
    linear_combination -hy
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + h * |y| ^ 2)]
  ring

/-- **Implicit Euler does not increase `|x|` for `x′ = −x³`, for every timestep** (Giles 2015,
§5.6, p. 44: "Other approaches to these problems include the use of drift-implicit methods"; the
deterministic analogue of the paper's example `dS_t = −S_t³ dt + dW_t`).  For every `h ≥ 0` and
every starting value `x₀`, the implicit Euler iterates `x_{n+1} = x_n − h x_{n+1}³`
(`implicitStep` for the drift `−x³`, iterated) satisfy `|x_{n+1}| ≤ |x_n|`, in particular
`|x_n| ≤ |x₀|`, whereas the explicit iterates `x_{n+1} = x_n − h x_n³` explode as soon as
`h x₀² > 2` (`eulerCubic_tendsto_atTop`). -/
theorem implicitCubic_abs_antitone {h : ℝ} (hh : 0 ≤ h) (x₀ : ℝ) :
    Antitone fun n => |(implicitStep (fun y => -y ^ 3) h)^[n] x₀| := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [Function.iterate_succ_apply']
  exact abs_implicitStep_le continuous_cubicDrift cubic_dissipative hh _

/-- **Implicit Euler for `x′ = −x³` decays to `0` for every timestep** (Giles 2015, §5.6, p. 44:
"the use of drift-implicit methods", deterministic analogue).  For every `h > 0` and every `x₀` the
implicit Euler iterates `x_{n+1} = x_n − h x_{n+1}³` tend to `0`, like the exact solutions
`x(t) = x₀/√(1 + 2x₀²t)` of `x′ = −x³`: `|x_n|` is non-increasing (`implicitCubic_abs_antitone`),
and its limit `ℓ` satisfies `ℓ = ℓ + hℓ³` (`implicitCubic_abs_eq`), so `ℓ = 0`. -/
theorem implicitCubic_tendsto_zero {h : ℝ} (hh : 0 < h) (x₀ : ℝ) :
    Tendsto (fun n => (implicitStep (fun y => -y ^ 3) h)^[n] x₀) atTop (𝓝 0) := by
  set u : ℕ → ℝ := fun n => |(implicitStep (fun y => -y ^ 3) h)^[n] x₀| with hu
  have hanti : Antitone u := implicitCubic_abs_antitone hh.le x₀
  have hbdd : BddBelow (Set.range u) := ⟨0, by rintro _ ⟨n, rfl⟩; exact abs_nonneg _⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set ℓ := ⨅ n, u n
  have hrel : ∀ n, u (n + 1) + h * u (n + 1) ^ 3 = u n := fun n => by
    simp only [hu]
    rw [Function.iterate_succ_apply']
    exact (implicitCubic_abs_eq hh.le _).symm
  have hlim1 : Tendsto (fun n => u (n + 1)) atTop (𝓝 ℓ) := hlim.comp (tendsto_add_atTop_nat 1)
  have hlim2 : Tendsto (fun n => u (n + 1) + h * u (n + 1) ^ 3) atTop (𝓝 (ℓ + h * ℓ ^ 3)) :=
    hlim1.add ((hlim1.pow 3).const_mul h)
  have heq : ℓ + h * ℓ ^ 3 = ℓ := tendsto_nhds_unique (hlim2.congr hrel) hlim
  have hℓ : ℓ = 0 := by
    have h3 : h * ℓ ^ 3 = 0 := by linarith
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
      ((mul_eq_zero.mp h3).resolve_left hh.ne')
  rw [hℓ] at hlim
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using hlim

/-- **Implicit against explicit Euler for `x′ = −x³`** (Giles 2015, §5.6, p. 44: "This again
leads to numerical instability if a uniform timestep is used. … Other approaches to these problems
include the use of drift-implicit methods").  The deterministic analogue (`σ = 0`) of the paper's
example `dS_t = −S_t³ dt + dW_t`, for every timestep `h ≥ 0` and every starting value `x₀`:
the implicit Euler iterates stay within `|x₀|`, while the explicit Euler iterates
`x_{n+1} = x_n − h x_n³` (`eulerDriftStep`) are bounded if and only if `h x₀² ≤ 2`, and for
`h x₀² > 2` they tend to `∞` in absolute value (`eulerCubic_tendsto_atTop`); for `h x₀² = 2` they
form the 2-cycle `x₀, −x₀` (the threshold is exact; checked numerically too).  So no uniform
timestep makes the explicit scheme stable for all starting values, and every timestep makes the
implicit one stable (for `h > 0` the implicit iterates even tend to `0`:
`implicitCubic_tendsto_zero`). -/
theorem implicitCubic_stable_explicitCubic_threshold {h : ℝ} (hh : 0 ≤ h) (x₀ : ℝ) :
    (∀ n, |(implicitStep (fun y => -y ^ 3) h)^[n] x₀| ≤ |x₀|) ∧
      ((∃ C, ∀ n, |(eulerDriftStep (fun S => -S ^ 3) h)^[n] x₀| ≤ C) ↔ h * x₀ ^ 2 ≤ 2) ∧
      (2 < h * x₀ ^ 2 →
        Tendsto (fun n => |(eulerDriftStep (fun S => -S ^ 3) h)^[n] x₀|) atTop atTop) := by
  refine ⟨fun n => implicitCubic_abs_antitone hh x₀ (Nat.zero_le n), ⟨fun ⟨C, hC⟩ => ?_,
    fun hs => ⟨|x₀|, eulerCubic_bounded hh hs⟩⟩, eulerCubic_tendsto_atTop⟩
  by_contra hlt
  obtain ⟨n, hn⟩ := ((eulerCubic_tendsto_atTop (not_le.mp hlt)).eventually_gt_atTop C).exists
  exact absurd (hC n) (not_le.mpr hn)

/-! ### Moments of a step driven by an independent Gaussian increment -/

/-- A measurable function of the first `n` of the variables `Z_0, …, Z_{N−1}` is independent of
`Z_n` when these are independent (`n < N`). -/
lemma indepFun_of_forall_lt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N n : ℕ}
    (hn : n < N) {F : (ℕ → ℝ) → ℝ} (hF : Measurable F)
    (hdep : ∀ z z' : ℕ → ℝ, (∀ k < n, z k = z' k) → F z = F z') {Z : ℕ → Ω → ℝ}
    (hm : ∀ k < N, AEMeasurable (Z k) μ) (hind : iIndepFun (fun k : Fin N => Z k) μ) :
    IndepFun (fun ω => F (fun k => Z k ω)) (Z n) μ := by
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
  let ψ : (S' → ℝ) → ℝ := fun y => y ⟨⟨n, hn⟩, Finset.mem_singleton_self _⟩
  have hψ : Measurable ψ := measurable_pi_apply _
  have h2 := h1.comp (hF.comp hext) hψ
  convert h2 using 1
  · funext ω
    simp only [Function.comp]
    exact hdep _ _ fun k hk => by simp [ext, hk]
  · rfl

/-- On a probability space, `|X^k| ≤ 1 + X⁴` for `k ≤ 4` makes every power `X^k`, `k ≤ 4`, of a
random variable with a finite fourth moment integrable. -/
lemma integrable_pow_of_memLp_four {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 4 μ) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => X ω ^ k) μ := by
  have h4 : MemLp X ((4 : ℕ) : ℝ≥0∞) μ := by exact_mod_cast hX
  have i4 : Integrable (fun ω => X ω ^ 4) μ :=
    (h4.integrable_norm_pow (by norm_num)).congr (ae_of_all _ fun ω => by
      simp only [Real.norm_eq_abs]
      exact Even.pow_abs (⟨2, rfl⟩ : Even 4) _)
  refine ((integrable_const 1).add i4).mono'
    ((continuous_pow k).comp_aestronglyMeasurable hX.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  have he4 : Even 4 := ⟨2, rfl⟩
  simp only [Real.norm_eq_abs, abs_pow, Pi.add_apply]
  rcases le_total |X ω| 1 with h | h
  · have := pow_le_one₀ (abs_nonneg (X ω)) h (n := k)
    nlinarith [pow_two_nonneg (X ω ^ 2)]
  · have := pow_le_pow_right₀ h hk
    rw [Even.pow_abs he4] at this
    linarith

/-- If `X` is square integrable and independent of `Y ∼ N(0, 1)`, then
`E[(ρX + sY)²] = ρ² E[X²] + s²` (the cross term vanishes because `E Y = 0`). -/
lemma integral_mul_add_mul_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : μ.map Y = gaussianReal 0 1) (hXY : IndepFun X Y μ) (ρ s : ℝ) :
    ∫ ω, (ρ * X ω + s * Y ω) ^ 2 ∂μ = ρ ^ 2 * ∫ ω, X ω ^ 2 ∂μ + s ^ 2 := by
  have hYm := aemeasurable_of_map_eq_gaussianReal hY
  have hY2 : MemLp Y 2 μ := memLp_of_map_eq_gaussianReal hY 2 ENNReal.ofNat_ne_top
  have hEY : ∫ ω, Y ω ∂μ = 0 := by
    have h1 : ∫ y, y ∂(μ.map Y) = ∫ ω, Y ω ∂μ := integral_map hYm aestronglyMeasurable_id
    rw [← h1, hY, integral_id_gaussianReal]
  have hEY2 : ∫ ω, Y ω ^ 2 ∂μ = 1 := by
    rw [← integral_map hYm (continuous_pow 2).aestronglyMeasurable, hY, integral_sq_gaussian]
  have hXY0 : ∫ ω, X ω * Y ω ∂μ = 0 := by
    rw [hXY.integral_fun_mul_eq_mul_integral hX.aestronglyMeasurable hYm.aestronglyMeasurable,
      hEY, mul_zero]
  have iX2 : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
  have iXY : Integrable (fun ω => X ω * Y ω) μ := hX.integrable_mul hY2
  have iY2 : Integrable (fun ω => Y ω ^ 2) μ := hY2.integrable_sq
  have e : (fun ω => (ρ * X ω + s * Y ω) ^ 2) =
      fun ω => ρ ^ 2 * X ω ^ 2 + 2 * ρ * s * (X ω * Y ω) + s ^ 2 * Y ω ^ 2 := by
    funext ω
    ring
  have iA : Integrable (fun ω => ρ ^ 2 * X ω ^ 2 + 2 * ρ * s * (X ω * Y ω)) μ :=
    (iX2.const_mul _).add (iXY.const_mul _)
  rw [e, integral_add iA (iY2.const_mul _),
    integral_add (iX2.const_mul _) (iXY.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, hXY0, hEY2]
  ring

/-- If `X` has a finite fourth moment and is independent of `Y ∼ N(0, 1)`, then
`E[(X + sY)⁴] = E[X⁴] + 6s² E[X²] + 3s⁴` (the odd moments of `Y` vanish, `E Y² = 1`,
`E Y⁴ = 3`). -/
lemma integral_add_mul_pow_four {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 4 μ)
    (hY : μ.map Y = gaussianReal 0 1) (hXY : IndepFun X Y μ) (s : ℝ) :
    ∫ ω, (X ω + s * Y ω) ^ 4 ∂μ = ∫ ω, X ω ^ 4 ∂μ + 6 * s ^ 2 * ∫ ω, X ω ^ 2 ∂μ + 3 * s ^ 4 := by
  have hYm := aemeasurable_of_map_eq_gaussianReal hY
  have iYk : ∀ k : ℕ, Integrable (fun ω => Y ω ^ k) μ := fun k => by
    have := integrable_pow_gaussian k
    rw [← hY] at this
    exact this.comp_aemeasurable hYm
  have hEYk : ∀ k : ℕ, ∫ ω, Y ω ^ k ∂μ = ∫ x, x ^ k ∂gaussianReal 0 1 := fun k => by
    rw [← hY, integral_map hYm (continuous_pow k).aestronglyMeasurable]
  have iXk : ∀ k ≤ 4, Integrable (fun ω => X ω ^ k) μ := fun k hk =>
    integrable_pow_of_memLp_four hX hk
  have hind : ∀ i j : ℕ, IndepFun (fun ω => X ω ^ i) (fun ω => Y ω ^ j) μ := fun i j =>
    hXY.comp (measurable_id.pow_const i) (measurable_id.pow_const j)
  have hprod : ∀ i j : ℕ, ∫ ω, X ω ^ i * Y ω ^ j ∂μ = (∫ ω, X ω ^ i ∂μ) * ∫ ω, Y ω ^ j ∂μ :=
    fun i j => (hind i j).integral_fun_mul_eq_mul_integral
      ((continuous_pow i).comp_aestronglyMeasurable hX.aestronglyMeasurable)
      ((continuous_pow j).comp_aestronglyMeasurable hYm.aestronglyMeasurable)
  have iprod : ∀ i j : ℕ, i ≤ 4 → Integrable (fun ω => X ω ^ i * Y ω ^ j) μ := fun i j hi =>
    (hind i j).integrable_mul (iXk i hi) (iYk j)
  have m1 : ∫ ω, Y ω ^ 1 ∂μ = 0 := by
    rw [hEYk 1]
    simp only [pow_one]
    exact integral_id_gaussianReal
  have m2 : ∫ ω, Y ω ^ 2 ∂μ = 1 := by rw [hEYk 2, integral_sq_gaussian]
  have m3 : ∫ ω, Y ω ^ 3 ∂μ = 0 := by rw [hEYk 3, integral_pow_three_gaussian]
  have m4 : ∫ ω, Y ω ^ 4 ∂μ = 3 := by rw [hEYk 4, integral_pow_four_gaussian]
  have e : (fun ω => (X ω + s * Y ω) ^ 4) = fun ω => X ω ^ 4 + 4 * s * (X ω ^ 3 * Y ω ^ 1) +
      6 * s ^ 2 * (X ω ^ 2 * Y ω ^ 2) + 4 * s ^ 3 * (X ω ^ 1 * Y ω ^ 3) + s ^ 4 * Y ω ^ 4 := by
    funext ω
    ring
  have i1 := iXk 4 le_rfl
  have i2 := (iprod 3 1 (by norm_num)).const_mul (4 * s)
  have i3 := (iprod 2 2 (by norm_num)).const_mul (6 * s ^ 2)
  have i4 := (iprod 1 3 (by norm_num)).const_mul (4 * s ^ 3)
  have i5 := (iYk 4).const_mul (s ^ 4)
  have i12 : Integrable (fun ω => X ω ^ 4 + 4 * s * (X ω ^ 3 * Y ω ^ 1)) μ := i1.add i2
  have i123 : Integrable (fun ω => X ω ^ 4 + 4 * s * (X ω ^ 3 * Y ω ^ 1) +
      6 * s ^ 2 * (X ω ^ 2 * Y ω ^ 2)) μ := i12.add i3
  have i1234 : Integrable (fun ω => X ω ^ 4 + 4 * s * (X ω ^ 3 * Y ω ^ 1) +
      6 * s ^ 2 * (X ω ^ 2 * Y ω ^ 2) + 4 * s ^ 3 * (X ω ^ 1 * Y ω ^ 3)) μ := i123.add i4
  rw [e, integral_add i1234 i5, integral_add i123 i4,
    integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hprod, hprod, hprod, m1, m2, m3, m4]
  ring

/-! ### The drift-implicit Euler–Maruyama scheme -/

/-- The drift-implicit Euler–Maruyama scheme (Giles 2015, §5.6, p. 44: "the use of drift-implicit
methods (Dereich, Neuenkirch and Szpruch 2012, Higham, Mao and Stuart 2002)") for the SDE
`dX_t = a(X_t) dt + σ dW_t` with timestep `h`, driven by the normal variables
`z = (Z_0, Z_1, …)` (Brownian increments `ΔW_n = √h Z_n`): `X_0 = x₀` and
`X_{n+1} = X_n + h a(X_{n+1}) + σ√h Z_n`, i.e. `X_{n+1} = implicitStep a h (X_n + σ√h Z_n)`.  The
drift is evaluated at the new point, the noise at the old one. -/
noncomputable def implicitPath (a : ℝ → ℝ) (h σ x₀ : ℝ) (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => implicitStep a h (implicitPath a h σ x₀ z n + σ * √h * z n)

/-- The drift-implicit path satisfies its implicit recursion
`X_{n+1} = X_n + h a(X_{n+1}) + σ√h z_n` under the hypotheses of `existsUnique_implicitStep`
(which says that `X_{n+1}` is the only solution; take `x = X_n`, `c = σ√h z_n` there). -/
lemma implicitPath_succ_eq {a : ℝ → ℝ} {K h : ℝ} (ha : Continuous a)
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hh : 0 ≤ h) (hhK : h * K < 1)
    (σ x₀ : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    implicitPath a h σ x₀ z (n + 1) =
      implicitPath a h σ x₀ z n + h * a (implicitPath a h σ x₀ z (n + 1)) + σ * √h * z n :=
  (existsUnique_implicitStep ha hK hh hhK _ _).2

/-- The drift-implicit path at step `n` depends only on `z_0, …, z_{n−1}`. -/
lemma implicitPath_congr (a : ℝ → ℝ) (h σ x₀ : ℝ) {z z' : ℕ → ℝ} {n : ℕ}
    (hz : ∀ k < n, z k = z' k) : implicitPath a h σ x₀ z n = implicitPath a h σ x₀ z' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show implicitStep a h (implicitPath a h σ x₀ z n + σ * √h * z n) =
      implicitStep a h (implicitPath a h σ x₀ z' n + σ * √h * z' n)
    rw [ih fun k hk => hz k (by omega), hz n (by omega)]

/-- For a measurable implicit step, the drift-implicit path at step `n` is a measurable function
of the normal variables. -/
lemma measurable_implicitPath {a : ℝ → ℝ} {h : ℝ} (hm : Measurable (implicitStep a h))
    (σ x₀ : ℝ) (n : ℕ) : Measurable fun z : ℕ → ℝ => implicitPath a h σ x₀ z n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact hm.comp (ih.add (measurable_const.mul (measurable_pi_apply n)))

/-- **Moment bounds for the drift-implicit scheme, uniform in the timestep** (Giles 2015, §5.6,
p. 44: "Other approaches to these problems include the use of drift-implicit methods (Dereich,
Neuenkirch and Szpruch 2012, Higham, Mao and Stuart 2002)").  Let `a` be a continuous drift with a
one-sided Lipschitz constant `K` that points towards `0` (`y a(y) ≤ 0`; e.g. `a(y) = −y³`, `K = 0`),
`h ≥ 0` with `hK < 1`, and let `Z_0, …, Z_{N−1}` be independent with law `N(0, 1)`.  Then the
drift-implicit scheme `X_{n+1} = X_n + h a(X_{n+1}) + σ√h Z_n`, `X_0 = x₀` (`implicitPath`; the
recursion is `implicitPath_succ_eq`) has a finite fourth moment and
`E X_N² ≤ x₀² + σ²Nh`, `E X_N⁴ ≤ x₀⁴ + 6x₀²σ²Nh + 3σ⁴(Nh)²`:
the second and fourth moments of `x₀ + σW_{Nh}`, the drift-free solution, so they are bounded for
`Nh ≤ T` independently of the timestep.  The proof: `|X_{n+1}| ≤ |X_n + σ√h Z_n|`
(`abs_implicitStep_le`), and `X_n` is independent of `Z_n`, so
`E X_{n+1}² ≤ E X_n² + σ²h` and `E X_{n+1}⁴ ≤ E X_n⁴ + 6σ²h E X_n² + 3σ⁴h²`.  For the explicit
scheme the moments diverge as `h → 0` for `a(y) = −y³` (`emCubic_moment_tendsto_atTop`, the theorem
of Hutzenthaler, Jentzen and Kloeden); see `implicit_vs_explicit_cubic_moments`.  Only additive
noise (a constant volatility `σ`) is treated: a state-dependent volatility `b(X_t)`, as in the
cited papers, is not covered.  The one-sided Lipschitz condition is used for the uniqueness of the
step and for the measurability of `X_N` (via `continuous_implicitStep`); the bound
`|X_{n+1}| ≤ |X_n + σ√h Z_n|` needs only `y a(y) ≤ 0`.  The strong convergence of the
drift-implicit scheme to the SDE (Higham, Mao and Stuart 2002) needs Itô calculus and is not
formalised.  Neither the measurability of the `Z_n` nor that `μ` is a probability measure is
assumed: both follow from the laws and the independence. -/
theorem implicitPath_moments_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {a : ℝ → ℝ}
    {K h : ℝ} (ha : Continuous a) (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2)
    (hdiss : ∀ y, y * a y ≤ 0) (hh : 0 ≤ h) (hhK : h * K < 1) (σ x₀ : ℝ) {N : ℕ}
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    MemLp (fun ω => implicitPath a h σ x₀ (fun n => Z n ω) N) 4 μ ∧
      ∫ ω, implicitPath a h σ x₀ (fun n => Z n ω) N ^ 2 ∂μ ≤ x₀ ^ 2 + σ ^ 2 * (N * h) ∧
      ∫ ω, implicitPath a h σ x₀ (fun n => Z n ω) N ^ 4 ∂μ ≤
        x₀ ^ 4 + 6 * x₀ ^ 2 * σ ^ 2 * (N * h) + 3 * σ ^ 4 * (N * h) ^ 2 := by
  have hprob : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have hm : ∀ n < N, AEMeasurable (Z n) μ := fun n hn =>
    aemeasurable_of_map_eq_gaussianReal (hZ n hn)
  have hcont := continuous_implicitStep ha hK hh hhK
  have hstep : ∀ r, |implicitStep a h r| ≤ |r| := abs_implicitStep_le ha hdiss hh
  have hsq : (σ * √h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  have key : ∀ n ≤ N, MemLp (fun ω => implicitPath a h σ x₀ (fun k => Z k ω) n) 4 μ ∧
      ∫ ω, implicitPath a h σ x₀ (fun k => Z k ω) n ^ 2 ∂μ ≤ x₀ ^ 2 + σ ^ 2 * (n * h) ∧
      ∫ ω, implicitPath a h σ x₀ (fun k => Z k ω) n ^ 4 ∂μ ≤
        x₀ ^ 4 + 6 * x₀ ^ 2 * σ ^ 2 * (n * h) + 3 * σ ^ 4 * (n * h) ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨memLp_const x₀, ?_, ?_⟩ <;> simp [implicitPath]
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      obtain ⟨hX4, hX2, hX4'⟩ := ih hn'.le
      set X := fun ω => implicitPath a h σ x₀ (fun k => Z k ω) n with hXdef
      have hXZ : IndepFun X (Z n) μ :=
        indepFun_of_forall_lt hn' (measurable_implicitPath hcont.measurable σ x₀ n)
          (fun z z' hz => implicitPath_congr a h σ x₀ hz) hm hind
      have hZ4 : MemLp (Z n) 4 μ := memLp_of_map_eq_gaussianReal (hZ n hn') 4 (by norm_num)
      have hY4 : MemLp (fun ω => X ω + σ * √h * Z n ω) 4 μ := hX4.add (hZ4.const_mul _)
      have hle : ∀ ω, |implicitPath a h σ x₀ (fun k => Z k ω) (n + 1)| ≤
          |X ω + σ * √h * Z n ω| := fun ω => hstep _
      have hXm : AEStronglyMeasurable
          (fun ω => implicitPath a h σ x₀ (fun k => Z k ω) (n + 1)) μ :=
        hcont.comp_aestronglyMeasurable hY4.aestronglyMeasurable
      have hX4n : MemLp (fun ω => implicitPath a h σ x₀ (fun k => Z k ω) (n + 1)) 4 μ :=
        hY4.of_le hXm (ae_of_all _ fun ω => by simp only [Real.norm_eq_abs]; exact hle ω)
      have e2 := integral_mul_add_mul_sq (hX4.mono_exponent (by norm_num)) (hZ n hn') hXZ 1
        (σ * √h)
      simp only [one_mul, one_pow] at e2
      have e4 := integral_add_mul_pow_four hX4 (hZ n hn') hXZ (σ * √h)
      have b2 : ∫ ω, implicitPath a h σ x₀ (fun k => Z k ω) (n + 1) ^ 2 ∂μ ≤
          ∫ ω, (X ω + σ * √h * Z n ω) ^ 2 ∂μ :=
        integral_mono (integrable_pow_of_memLp_four hX4n (by norm_num))
          (integrable_pow_of_memLp_four hY4 (by norm_num)) fun ω => sq_le_sq.mpr (hle ω)
      have b4 : ∫ ω, implicitPath a h σ x₀ (fun k => Z k ω) (n + 1) ^ 4 ∂μ ≤
          ∫ ω, (X ω + σ * √h * Z n ω) ^ 4 ∂μ := by
        refine integral_mono (integrable_pow_of_memLp_four hX4n le_rfl)
          (integrable_pow_of_memLp_four hY4 le_rfl) fun ω => ?_
        have := pow_le_pow_left₀ (abs_nonneg _) (hle ω) 4
        rwa [Even.pow_abs (⟨2, rfl⟩ : Even 4), Even.pow_abs (⟨2, rfl⟩ : Even 4)] at this
      rw [hsq] at e2 e4
      have h6 : 6 * (σ ^ 2 * h) * ∫ ω, X ω ^ 2 ∂μ ≤ 6 * (σ ^ 2 * h) * (x₀ ^ 2 + σ ^ 2 * (n * h)) :=
        mul_le_mul_of_nonneg_left hX2 (by positivity)
      push_cast
      refine ⟨hX4n, ?_, ?_⟩
      · rw [e2] at b2
        nlinarith
      · rw [e4] at b4
        nlinarith
  exact key N le_rfl

/-- **The drift-implicit scheme for `dS = −S³ dt + dW` has moments bounded uniformly in the number
of steps** (Giles 2015, §5.6, p. 44: "Hutzenthaler, Jentzen and Kloeden (2013), who are concerned
with SDEs such as `dS_t = −S_t³ dt + dW_t` … Other approaches to these problems include the use of
drift-implicit methods").  For `T ≥ 0`, every number of steps `N` (no lower bound on `N`, unlike
the tamed scheme's `N ≥ T/54` in `tamedCubic_second_moment_le`) and independent
`Z_0, …, Z_{N−1}` with law `N(0, 1)`, the drift-implicit scheme
`X_{n+1} = X_n − h X_{n+1}³ + √h Z_n`, `h = T/N` (`implicitPath` with drift `−S³`, `σ = 1`)
has a finite fourth moment (so the integrals below are genuine expectations, not Lean's junk value
`0` for a non-integrable function) and satisfies `E X_N² ≤ x₀² + T` and
`E X_N⁴ ≤ x₀⁴ + 6x₀²T + 3T²`, the moments of `x₀ + W_T` (`implicitPath_moments_le`).  The explicit
scheme has `E|X_N|^p → ∞` (`emCubic_moment_tendsto_atTop`; see
`implicit_vs_explicit_cubic_moments`). -/
theorem implicitCubic_moments_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (x₀ : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (N : ℕ) (Z : ℕ → Ω → ℝ) (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    MemLp (fun ω => implicitPath (fun y => -y ^ 3) (T / N) 1 x₀ (fun n => Z n ω) N) 4 μ ∧
      ∫ ω, implicitPath (fun y => -y ^ 3) (T / N) 1 x₀ (fun n => Z n ω) N ^ 2 ∂μ ≤ x₀ ^ 2 + T ∧
      ∫ ω, implicitPath (fun y => -y ^ 3) (T / N) 1 x₀ (fun n => Z n ω) N ^ 4 ∂μ ≤
        x₀ ^ 4 + 6 * x₀ ^ 2 * T + 3 * T ^ 2 := by
  have hh : 0 ≤ T / N := by positivity
  obtain ⟨hmem, h2, h4⟩ := implicitPath_moments_le continuous_cubicDrift cubic_oneSidedLipschitz
    cubic_dissipative hh (by norm_num : T / N * 0 < 1) 1 x₀ Z hZ hind
  have hNT : (N : ℝ) * (T / N) ≤ T := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [h0, hT]
    · rw [mul_div_cancel₀ _ (by exact_mod_cast h0.ne')]
  have hNT0 : 0 ≤ (N : ℝ) * (T / N) := by positivity
  simp only [one_pow, one_mul, mul_one] at h2 h4
  refine ⟨hmem, by linarith, h4.trans ?_⟩
  have : (N * (T / N) : ℝ) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hNT0 hNT 2
  nlinarith [sq_nonneg x₀]

/-- `|x|^k` as a real power equals `x^k` for even `k`. -/
lemma abs_rpow_natCast_of_even {k : ℕ} (hk : Even k) (x : ℝ) : |x| ^ (k : ℝ) = x ^ k := by
  rw [Real.rpow_natCast, Even.pow_abs hk]

/-- **Drift-implicit against explicit Euler–Maruyama for `dS = −S³ dt + dW`** (Giles 2015, §5.6,
p. 44: "Hutzenthaler, Jentzen and Kloeden (2013), who are concerned with SDEs such as
`dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the volatility.
This again leads to numerical instability if a uniform timestep is used. … Other approaches to
these problems include the use of drift-implicit methods (Dereich, Neuenkirch and Szpruch 2012,
Higham, Mao and Stuart 2002)").  Fix `x₀`, `T > 0`, and for each number of steps `N` independent
`Z_{N,0}, …, Z_{N,N−1}` with law `N(0, 1)` (increments `√(T/N) Z_{N,n}`, `h = T/N`).  Driven by the
same variables, the drift-implicit scheme `X_{n+1} = X_n − h X_{n+1}³ + √h Z_{N,n}` has a finite
fourth moment, with second and fourth moments bounded by `x₀² + T` and `x₀⁴ + 6x₀²T + 3T²`, for
every `N` (`implicitCubic_moments_le`), while the second and fourth moments of the explicit scheme
`X_{n+1} = X_n − h X_n³ + √h Z_{N,n}` (`emPath`) tend to `∞` as `N → ∞` (the theorem of
Hutzenthaler, Jentzen and Kloeden, `emCubic_moment_tendsto_atTop`). -/
theorem implicit_vs_explicit_cubic_moments {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (x₀ : ℝ) {T : ℝ} (hT : 0 < T) (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N, ∀ n < N, μ.map (Z N n) = gaussianReal 0 1)
    (hind : ∀ N, iIndepFun (fun n : Fin N => Z N n) μ) :
    (∀ N : ℕ,
      MemLp (fun ω => implicitPath (fun y => -y ^ 3) (T / N) 1 x₀ (fun n => Z N n ω) N) 4 μ ∧
      ∫ ω, implicitPath (fun y => -y ^ 3) (T / N) 1 x₀ (fun n => Z N n ω) N ^ 2 ∂μ ≤
        x₀ ^ 2 + T ∧
      ∫ ω, implicitPath (fun y => -y ^ 3) (T / N) 1 x₀ (fun n => Z N n ω) N ^ 4 ∂μ ≤
        x₀ ^ 4 + 6 * x₀ ^ 2 * T + 3 * T ^ 2) ∧
    Tendsto (fun N : ℕ => ∫ ω, emPath (fun S _ => -S ^ 3) (fun _ _ => 1) (T / N) x₀
      (fun n => Z N n ω) N ^ 2 ∂μ) atTop atTop ∧
    Tendsto (fun N : ℕ => ∫ ω, emPath (fun S _ => -S ^ 3) (fun _ _ => 1) (T / N) x₀
      (fun n => Z N n ω) N ^ 4 ∂μ) atTop atTop := by
  refine ⟨fun N => implicitCubic_moments_le x₀ hT.le N (Z N) (hZ N) (hind N), ?_, ?_⟩
  · have := emCubic_moment_tendsto_atTop x₀ hT (by norm_num : (0 : ℝ) < ((2 : ℕ) : ℝ)) Z hZ hind
    simpa only [abs_rpow_natCast_of_even (⟨1, rfl⟩ : Even 2)] using this
  · have := emCubic_moment_tendsto_atTop x₀ hT (by norm_num : (0 : ℝ) < ((4 : ℕ) : ℝ)) Z hZ hind
    simpa only [abs_rpow_natCast_of_even (⟨2, rfl⟩ : Even 4)] using this

/-! ### The integrating factor for a stiff linear drift -/

/-- The affine recursion `X_{n+1} = ρ X_n + s z_n`, `X_0 = x₀`.  Both the integrating-factor scheme
(`intFactorPath`) and the explicit Euler–Maruyama scheme (`emPath`) for the linear SDE
`dX_t = −L X_t dt + σ dW_t` have this form (`intFactorPath_eq_linRecPath`,
`emPath_linear_eq_linRecPath`). -/
def linRecPath (ρ s x₀ : ℝ) (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => ρ * linRecPath ρ s x₀ z n + s * z n

/-- The affine recursion at step `n` depends only on `z_0, …, z_{n−1}`. -/
lemma linRecPath_congr (ρ s x₀ : ℝ) {z z' : ℕ → ℝ} {n : ℕ} (hz : ∀ k < n, z k = z' k) :
    linRecPath ρ s x₀ z n = linRecPath ρ s x₀ z' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ρ * linRecPath ρ s x₀ z n + s * z n = ρ * linRecPath ρ s x₀ z' n + s * z' n
    rw [ih fun k hk => hz k (by omega), hz n (by omega)]

/-- The affine recursion at step `n` is a measurable function of the inputs. -/
lemma measurable_linRecPath (ρ s x₀ : ℝ) (n : ℕ) :
    Measurable fun z : ℕ → ℝ => linRecPath ρ s x₀ z n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (measurable_const.mul ih).add (measurable_const.mul (measurable_pi_apply n))

/-- The mean square of the affine recursion `X_{n+1} = ρX_n + sZ_n` driven by independent
`Z_n ∼ N(0, 1)`: `X_N` is square integrable and `E X_N² = (ρ²)^N x₀² + s² ∑_{k<N} (ρ²)^k`, from
`E X_{n+1}² = ρ² E X_n² + s²` (`integral_mul_add_mul_sq`). -/
lemma linRecPath_second_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (ρ s x₀ : ℝ)
    {N : ℕ} (Z : ℕ → Ω → ℝ) (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    MemLp (fun ω => linRecPath ρ s x₀ (fun n => Z n ω) N) 2 μ ∧
      ∫ ω, linRecPath ρ s x₀ (fun n => Z n ω) N ^ 2 ∂μ =
        (ρ ^ 2) ^ N * x₀ ^ 2 + s ^ 2 * ∑ k ∈ Finset.range N, (ρ ^ 2) ^ k := by
  have hprob : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have hm : ∀ n < N, AEMeasurable (Z n) μ := fun n hn =>
    aemeasurable_of_map_eq_gaussianReal (hZ n hn)
  have key : ∀ n ≤ N, MemLp (fun ω => linRecPath ρ s x₀ (fun k => Z k ω) n) 2 μ ∧
      ∫ ω, linRecPath ρ s x₀ (fun k => Z k ω) n ^ 2 ∂μ =
        (ρ ^ 2) ^ n * x₀ ^ 2 + s ^ 2 * ∑ k ∈ Finset.range n, (ρ ^ 2) ^ k := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨memLp_const x₀, ?_⟩
      simp [linRecPath]
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      obtain ⟨hX2, hE⟩ := ih hn'.le
      have hXZ : IndepFun (fun ω => linRecPath ρ s x₀ (fun k => Z k ω) n) (Z n) μ :=
        indepFun_of_forall_lt hn' (measurable_linRecPath ρ s x₀ n)
          (fun z z' hz => linRecPath_congr ρ s x₀ hz) hm hind
      have hZ2 : MemLp (Z n) 2 μ := memLp_of_map_eq_gaussianReal (hZ n hn') 2 ENNReal.ofNat_ne_top
      refine ⟨(hX2.const_mul ρ).add (hZ2.const_mul s), ?_⟩
      show ∫ ω, (ρ * linRecPath ρ s x₀ (fun k => Z k ω) n + s * Z n ω) ^ 2 ∂μ = _
      rw [integral_mul_add_mul_sq hX2 (hZ n hn') hXZ ρ s, hE, geom_sum_succ]
      ring
  exact key N le_rfl

/-- The integrating-factor scheme for the linear SDE `dX_t = −L X_t dt + σ dW_t` (Giles 2015,
§5.6, p. 44: "a change or [sic] variables equivalent to the use of an integrating factor in ODEs
(see the Heston treatment in (Giles 2008a) which was suggested by Mark Broadie)").  With
`Y_t = e^{Lt} X_t` one has `dY_t = e^{Lt} σ dW_t`; one Euler step for `Y`, mapped back, gives
`X_0 = x₀` and `X_{n+1} = e^{−Lh}(X_n + σ√h Z_n)`, driven by the normal variables
`z = (Z_0, Z_1, …)`.  The survey states the idea in general and refers to the Heston treatment of
Giles (2008a) as its example; this is its simplest instance, a stiff mean-reverting drift `−LX`
with `L` large. -/
noncomputable def intFactorPath (L h σ x₀ : ℝ) (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => Real.exp (-L * h) * (intFactorPath L h σ x₀ z n + σ * √h * z n)

/-- The integrating-factor scheme is the affine recursion with `ρ = e^{−Lh}`,
`s = e^{−Lh} σ√h`. -/
lemma intFactorPath_eq_linRecPath (L h σ x₀ : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    intFactorPath L h σ x₀ z n =
      linRecPath (Real.exp (-L * h)) (Real.exp (-L * h) * (σ * √h)) x₀ z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Real.exp (-L * h) * (intFactorPath L h σ x₀ z n + σ * √h * z n) =
      Real.exp (-L * h) * linRecPath (Real.exp (-L * h)) (Real.exp (-L * h) * (σ * √h)) x₀ z n +
        Real.exp (-L * h) * (σ * √h) * z n
    rw [ih]
    ring

/-- **The mean square of the integrating-factor scheme** (Giles 2015, §5.6, p. 44: "a change or
[sic] variables equivalent to the use of an integrating factor in ODEs").  For
`dX_t = −L X_t dt + σ dW_t`, `h ≥ 0` and independent `Z_0, …, Z_{N−1}` with law `N(0, 1)`, the
scheme `X_{n+1} = e^{−Lh}(X_n + σ√h Z_n)` (`intFactorPath`) satisfies, with `q = e^{−2Lh}`,
`E X_N² = q^N x₀² + q σ² h ∑_{k<N} q^k`.  For the exact solution (Ornstein–Uhlenbeck),
`E X_{Nh}² = q^N x₀² + σ² ∫_0^{Nh} e^{−2Ls} ds`, of which `q σ² h ∑_{k<N} q^k` is a right-endpoint
Riemann sum (the exact solution is not formalised here).  For `σ = 0` (the deterministic analogue)
the scheme is exact: `X_N = e^{−LNh} x₀`. -/
theorem intFactorPath_second_moment_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (L σ x₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) {N : ℕ} (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    ∫ ω, intFactorPath L h σ x₀ (fun n => Z n ω) N ^ 2 ∂μ =
      Real.exp (-2 * L * h) ^ N * x₀ ^ 2 +
        Real.exp (-2 * L * h) * σ ^ 2 * h * ∑ k ∈ Finset.range N, Real.exp (-2 * L * h) ^ k := by
  have e : (fun ω => intFactorPath L h σ x₀ (fun n => Z n ω) N ^ 2) = fun ω =>
      linRecPath (Real.exp (-L * h)) (Real.exp (-L * h) * (σ * √h)) x₀ (fun n => Z n ω) N ^ 2 :=
    funext fun ω => by rw [intFactorPath_eq_linRecPath]
  have hq : Real.exp (-L * h) ^ 2 = Real.exp (-2 * L * h) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e, (linRecPath_second_moment _ _ x₀ Z hZ hind).2, hq, mul_pow, hq, mul_pow,
    Real.sq_sqrt hh]
  ring

/-- **The integrating-factor scheme is mean-square stable for every timestep** (Giles 2015, §5.6,
pp. 43–44: "If the drift term has a characteristic time-scale of `τ`, as in a mean-reverting drift
`(θ − S_t)/τ`, then when using the explicit Euler-Maruyama discretisation the timestep `h₀` on the
coarsest level cannot be much larger than `τ` without encountering severe numerical stability
problems. … Other approaches to these problems include … a change or [sic] variables equivalent
to the use of an integrating factor in ODEs").  For `dX_t = −L X_t dt + σ dW_t` with `L > 0`
(time-scale `τ = 1/L`), every timestep `h ≥ 0`, every number of steps `N` and independent
`Z_0, …, Z_{N−1}` with law `N(0, 1)`, the scheme `X_{n+1} = e^{−Lh}(X_n + σ√h Z_n)`
(`intFactorPath`) is square integrable and satisfies `E X_N² ≤ max(x₀², σ²/(2L))`, uniformly in
`h` and `N`; the exact
solution satisfies the same bound, `σ²/(2L)` being its stationary variance.  Proof: from
`intFactorPath_second_moment_eq`, `m_{n+1} = e^{−2Lh}(m_n + σ²h)`, and
`e^{−2Lh}(M + σ²h) ≤ M` because `e^{2Lh} ≥ 1 + 2Lh` and `2LM ≥ σ²`.  Compare
`emLinear_second_moment_tendsto_atTop`: the explicit scheme is mean-square unstable for `Lh > 2`. -/
theorem intFactorPath_second_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {L : ℝ} (hL : 0 < L) (σ x₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) {N : ℕ} (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    MemLp (fun ω => intFactorPath L h σ x₀ (fun n => Z n ω) N) 2 μ ∧
      ∫ ω, intFactorPath L h σ x₀ (fun n => Z n ω) N ^ 2 ∂μ ≤ max (x₀ ^ 2) (σ ^ 2 / (2 * L)) := by
  have e : (fun ω => intFactorPath L h σ x₀ (fun n => Z n ω) N) = fun ω =>
      linRecPath (Real.exp (-L * h)) (Real.exp (-L * h) * (σ * √h)) x₀ (fun n => Z n ω) N :=
    funext fun ω => intFactorPath_eq_linRecPath L h σ x₀ _ N
  refine ⟨e ▸ (linRecPath_second_moment _ _ x₀ Z hZ hind).1, ?_⟩
  rw [intFactorPath_second_moment_eq L σ x₀ hh Z hZ hind]
  set q := Real.exp (-2 * L * h) with hqdef
  set M := max (x₀ ^ 2) (σ ^ 2 / (2 * L)) with hMdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hM0 : 0 ≤ M := le_max_of_le_left (sq_nonneg _)
  have hstep : q * (M + σ ^ 2 * h) ≤ M := by
    have h1 : σ ^ 2 ≤ 2 * L * M := by
      have := le_max_right (x₀ ^ 2) (σ ^ 2 / (2 * L))
      rw [← hMdef, div_le_iff₀ (by positivity)] at this
      linarith
    have h2 : (2 * L * h + 1) * M ≤ Real.exp (2 * L * h) * M :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) hM0
    have h3 : q * Real.exp (2 * L * h) = 1 := by
      rw [hqdef, ← Real.exp_add, show -2 * L * h + 2 * L * h = 0 by ring, Real.exp_zero]
    have h4 : M + σ ^ 2 * h ≤ Real.exp (2 * L * h) * M := by
      nlinarith [mul_le_mul_of_nonneg_right h1 hh]
    calc q * (M + σ ^ 2 * h) ≤ q * (Real.exp (2 * L * h) * M) :=
          mul_le_mul_of_nonneg_left h4 hq0
      _ = M := by rw [← mul_assoc, h3, one_mul]
  have key : ∀ n : ℕ, q ^ n * x₀ ^ 2 + q * σ ^ 2 * h * ∑ k ∈ Finset.range n, q ^ k ≤ M := by
    intro n
    induction n with
    | zero => simp [hMdef]
    | succ n ih =>
      have e : q ^ (n + 1) * x₀ ^ 2 + q * σ ^ 2 * h * ∑ k ∈ Finset.range (n + 1), q ^ k =
          q * ((q ^ n * x₀ ^ 2 + q * σ ^ 2 * h * ∑ k ∈ Finset.range n, q ^ k) + σ ^ 2 * h) := by
        rw [geom_sum_succ]
        ring
      rw [e]
      exact (mul_le_mul_of_nonneg_left (by linarith) hq0).trans hstep
  exact key N

/-- The explicit Euler–Maruyama scheme for `dX_t = −L X_t dt + σ dW_t` is the affine recursion
with `ρ = 1 − Lh`, `s = σ√h`. -/
lemma emPath_linear_eq_linRecPath (L σ h x₀ : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    emPath (fun S _ => -L * S) (fun _ _ => σ) h x₀ z n =
      linRecPath (1 - L * h) (σ * √h) x₀ z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [emPath_succ, ih]
    show linRecPath (1 - L * h) (σ * √h) x₀ z n + -L * linRecPath (1 - L * h) (σ * √h) x₀ z n * h +
        σ * √h * z n = (1 - L * h) * linRecPath (1 - L * h) (σ * √h) x₀ z n + σ * √h * z n
    ring

/-- **The mean square of the explicit Euler–Maruyama scheme for a linear drift** (Giles 2015, §5.6,
pp. 43–44: "when using the explicit Euler-Maruyama discretisation the timestep `h₀` on the coarsest
level cannot be much larger than `τ` without encountering severe numerical stability problems").
For `dX_t = −L X_t dt + σ dW_t`, `h ≥ 0` and independent `Z_0, …, Z_{N−1}` with law `N(0, 1)`, the
explicit scheme `X_{n+1} = (1 − Lh)X_n + σ√h Z_n` (`emPath`) satisfies
`E X_N² = ((1 − Lh)²)^N x₀² + σ² h ∑_{k<N} ((1 − Lh)²)^k`. -/
theorem emLinear_second_moment_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (L σ x₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) {N : ℕ} (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    ∫ ω, emPath (fun S _ => -L * S) (fun _ _ => σ) h x₀ (fun n => Z n ω) N ^ 2 ∂μ =
      ((1 - L * h) ^ 2) ^ N * x₀ ^ 2 + σ ^ 2 * h * ∑ k ∈ Finset.range N, ((1 - L * h) ^ 2) ^ k := by
  have e : (fun ω => emPath (fun S _ => -L * S) (fun _ _ => σ) h x₀ (fun n => Z n ω) N ^ 2) =
      fun ω => linRecPath (1 - L * h) (σ * √h) x₀ (fun n => Z n ω) N ^ 2 :=
    funext fun ω => by rw [emPath_linear_eq_linRecPath]
  rw [e, (linRecPath_second_moment _ _ x₀ Z hZ hind).2, mul_pow, Real.sq_sqrt hh]

/-- **The explicit Euler–Maruyama scheme is mean-square unstable for `Lh > 2`** (Giles 2015, §5.6,
pp. 43–44: "If the drift term has a characteristic time-scale of `τ`, as in a mean-reverting drift
`(θ − S_t)/τ`, then when using the explicit Euler-Maruyama discretisation the timestep `h₀` on the
coarsest level cannot be much larger than `τ` without encountering severe numerical stability
problems").  For `dX_t = −L X_t dt + σ dW_t` (`τ = 1/L`), a timestep `h > 0` with `Lh > 2`, i.e.
`(1 − Lh)² > 1`, a nontrivial problem (`x₀ ≠ 0` or `σ ≠ 0`) and i.i.d. `Z_n ∼ N(0, 1)`, the mean
square `E X_N²` of the explicit scheme (`emPath`) tends to `∞` as `N → ∞`
(`emLinear_second_moment_eq`), while the integrating-factor scheme stays below
`max(x₀², σ²/(2L))` for every `h` (`intFactorPath_second_moment_le`).  The deterministic analogue
is `emMeanRevert_unbounded`. -/
theorem emLinear_second_moment_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {L σ x₀ h : ℝ} (hh : 0 < h) (hLh : 2 < L * h) (hne : x₀ ≠ 0 ∨ σ ≠ 0) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n, μ.map (Z n) = gaussianReal 0 1) (hind : iIndepFun Z μ) :
    Tendsto (fun N : ℕ => ∫ ω, emPath (fun S _ => -L * S) (fun _ _ => σ) h x₀
      (fun n => Z n ω) N ^ 2 ∂μ) atTop atTop := by
  have hq : 1 < (1 - L * h) ^ 2 := by nlinarith
  have hform : ∀ N : ℕ, ((1 - L * h) ^ 2) ^ N * x₀ ^ 2 +
      σ ^ 2 * h * ∑ k ∈ Finset.range N, ((1 - L * h) ^ 2) ^ k =
      ∫ ω, emPath (fun S _ => -L * S) (fun _ _ => σ) h x₀ (fun n => Z n ω) N ^ 2 ∂μ :=
    fun N => (emLinear_second_moment_eq L σ x₀ hh.le Z (fun n _ => hZ n)
      (hind.precomp Fin.val_injective)).symm
  refine Tendsto.congr hform ?_
  have hsum : ∀ N : ℕ, (N : ℝ) ≤ ∑ k ∈ Finset.range N, ((1 - L * h) ^ 2) ^ k := fun N => by
    calc (N : ℝ) = ∑ _k ∈ Finset.range N, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun k _ => one_le_pow₀ hq.le
  rcases hne with hx | hσ
  · have hx2 : 0 < x₀ ^ 2 := by positivity
    refine tendsto_atTop_mono (fun N => ?_)
      ((tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const hx2)
    have : 0 ≤ σ ^ 2 * h * ∑ k ∈ Finset.range N, ((1 - L * h) ^ 2) ^ k := by positivity
    linarith
  · have hs : 0 < σ ^ 2 * h := by positivity
    refine tendsto_atTop_mono (fun N => ?_)
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hs)
    have := mul_le_mul_of_nonneg_left (hsum N) hs.le
    have : 0 ≤ ((1 - L * h) ^ 2) ^ N * x₀ ^ 2 := by positivity
    linarith

end MLMC
