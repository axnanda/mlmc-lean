import MlmcLean.NestedKinkSde

/-!
# Nested MIMC with a piecewise linear `f`: the corrected rates (Giles 2015, §9.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §9.2 "MIMC
treatment" (pp. 59–60) of the author's version.

§9.2, p. 60: "Following the analysis in (Bujok et al. 2013), if the function `f` is continuous and
piecewise differentiable, rather than being twice differentiable, then in the MLMC treatment we
would get `β = 1.5`, and hence an overall complexity which is `O(ε^{−2.5})`. On the other hand,
with MIMC we would have `β₁ = β₂ = 1.5` and so the complexity would remain `O(ε⁻²)`. This
illustrates the benefit of the MIMC approach compared to standard MLMC."  The MLMC part is proved
in `MlmcLean/NestedKinkSde.lean` (`nested_kink_sde_mlmc_complexity`); the MIMC part is false: the
example `kinkInnerApprox` satisfies all the kink hypotheses, yet no `β₁, β₂` with `2β₁ + β₂ > 3`
bound its MIMC variances (`nested_mimc_kink_rates_false`).  The first-order weak error of the inner
discretisation moves the kink seen by `g_{ℓ₂}` and `g_{ℓ₂+1}` by `O(2^{−ℓ₂})`, and on the event that
the two coarse inner means straddle the kink (probability `O(2^{−ℓ₁/2})`) this changes the
antithetic difference by `O(2^{−ℓ₂})`; the antithetic construction does not damp it.  This file
proves the corrected statements, for `f(x) = a₀ + a₁x + c max(x − k, 0)` and the six-term MIMC
correction `Y_ℓ` of p. 59 (`nestedMimcDelta`):

* **`V_ℓ = O(2^{−ℓ₁−ℓ₂})`, i.e. `β₁ = β₂ = 1`** (`nested_mimc_kink_variance_rate`).  Each of the two
  §9.1 corrections in `Y` gives `E[Y²] = O(2^{−3ℓ₁/2} + 2^{−ℓ₁−ℓ₂})`.  Alternatively `Y = c (P + T)`
  (`mimc_hinge_le`), where `|P|` is at most the inner sampling fluctuations of `g_{ℓ₂+1} − g_{ℓ₂}`,
  `O(2^{−ℓ₁/2−ℓ₂/2})` in `L²` already for strong order `½` (`integral_centred_innerMean_sq_le`), and
  `T` is the change of the antithetic difference when the kink moves by the weak error
  `μ = O(2^{−ℓ₂})`: `|T| ≤ |μ|/2` and `T = 0` away from the kink, so the small ball gives
  `E[T²] = O(2^{−2ℓ₂−ℓ₁/2} + 2^{−3ℓ₂})` (`mimc_shift_term_le`).  The minimum of the two bounds is
  `O(2^{−ℓ₁−ℓ₂})` (`min(x, y) ≤ √(xy)`, `mimc_kink_rate_combine`).
* **`|E[Y_ℓ]| = O(2^{−ℓ₁/2−ℓ₂})`** with first-order strong convergence
  (`nested_mimc_kink_mean_rate`); the smooth-case `O(2^{−ℓ₁−ℓ₂})` of p. 60 is not claimed (it
  fails, numerically, when the weak error depends on the outer sample).
* **Sharpness** (`nested_mimc_kink_rate_sharp`): for `kinkInnerApprox`, `2^{ℓ₁+ℓ₂} V[Y_ℓ] ≤ 19` for
  all `ℓ`, `≥ 2^{−18}` along `ℓ₁ = 2j`, `ℓ₂ = j + 1` (`kinkMimc_variance_ge`), and `E[Y_ℓ] = 0`;
  `(β₁, β₂) = (1, 1)` is on the boundary `2β₁ + β₂ = 3` of `nested_mimc_kink_rates_false`.  The
  sharpness is along this ray and for rates of the form `2^{−β₁ℓ₁−β₂ℓ₂}`: away from the ray
  `ℓ₁ = 2ℓ₂` the example's variance is much smaller (numerically
  `V[Y_ℓ] ≍ min(2^{−3ℓ₁/2}, 2^{−2ℓ₂−ℓ₁/2})`, not formalised).
* **The cost** (`nested_mimc_kink_exponents`, `nested_mimc_kink_complexity`): Theorem 2
  (`giles_theorem2_boundary`) with `α = (½, ½)` and the corrected `β = γ = (1, 1)` (`η = 0`,
  `D₂ = 2`) gives mean square error `< ε²` at cost `O(ε⁻² |log ε|⁴)`.  The paper's derivation of
  `O(ε⁻²)` from Theorem 2 (which needs `β_d > γ_d`) fails; whether `O(ε⁻²)` is attainable with
  another index set is not decided here.  The bound is still `o(ε^{−2.5})`, below the MLMC cost
  bound `O(ε^{−2.5})` of `nested_kink_sde_mlmc_complexity` (`nested_mimc_kink_beats_mlmc`): at
  the level of the guaranteed cost bounds MIMC beats MLMC here, as the paper says, by a smaller
  margin.

Hypotheses (this formalisation's; the paper states none for this case), those of
`MlmcLean/NestedKinkSde.lean`: bounded centred conditional fourth moments of the inner
approximations `g_ℓ`, first order weak convergence uniformly in the outer sample, and the
small-ball bound `ν{|E_W[g(Z, W)] − k| ≤ t} ≤ c_d t` for the exact conditional mean only; but
strong convergence in `L²` of order `½` (`2^ℓ E[(g_{ℓ+1} − g_ℓ)²] ≤ cₛ`, for the variance and the
cost) instead of the order `¼` (`2^{ℓ/2} E[(g_{ℓ+1} − g_ℓ)²] ≤ cₛ`) that the MLMC theorems there
need, or of order `1` (for the mean rate).  The paper assumes first order strong convergence
(Milstein).  Deviation: the paper's `f` is continuous and piecewise differentiable; here it is
piecewise linear with one kink, as in `nested_kink_variance_rate`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace MLMC

/-! ### Pointwise inequalities -/

/-- The hinge antithetic difference
`H(e₁, e₂; x) = max(x + (e₁ + e₂)/2, 0) − ½ max(x + e₁, 0) − ½ max(x + e₂, 0)` of Giles 2015,
§9.1 (`hingeAntithetic`, with the kink at `0` and the coarse values `x + e₁`, `x + e₂`) is
`1`-Lipschitz in the coarse errors: `|H(e₁, e₂; x) − H(e₁′, e₂′; x)| ≤ |e₁ − e₁′| + |e₂ − e₂′|`. -/
lemma hingeAntithetic_sub_le (e₁ e₂ e₁' e₂' x : ℝ) :
    |hingeAntithetic e₁ e₂ x - hingeAntithetic e₁' e₂' x| ≤ |e₁ - e₁'| + |e₂ - e₂'| := by
  have a0 := abs_max_sub_max_le_abs (x + (e₁ + e₂) / 2) (x + (e₁' + e₂') / 2) 0
  have a1 := abs_max_sub_max_le_abs (x + e₁) (x + e₁') 0
  have a2 := abs_max_sub_max_le_abs (x + e₂) (x + e₂') 0
  rw [show x + (e₁ + e₂) / 2 - (x + (e₁' + e₂') / 2) = ((e₁ - e₁') + (e₂ - e₂')) / 2 by ring]
    at a0
  rw [show x + e₁ - (x + e₁') = e₁ - e₁' by ring] at a1
  rw [show x + e₂ - (x + e₂') = e₂ - e₂' by ring] at a2
  have b0 : |((e₁ - e₁') + (e₂ - e₂')) / 2| ≤ (|e₁ - e₁'| + |e₂ - e₂'|) / 2 := by
    rw [abs_div, abs_two]
    gcongr
    exact abs_add_le _ _
  have e : hingeAntithetic e₁ e₂ x - hingeAntithetic e₁' e₂' x =
      (max (x + (e₁ + e₂) / 2) 0 - max (x + (e₁' + e₂') / 2) 0) -
        (max (x + e₁) 0 - max (x + e₁') 0) / 2 - (max (x + e₂) 0 - max (x + e₂') 0) / 2 := by
    unfold hingeAntithetic
    ring
  rw [e]
  have t1 := abs_sub (max (x + (e₁ + e₂) / 2) 0 - max (x + (e₁' + e₂') / 2) 0 -
    (max (x + e₁) 0 - max (x + e₁') 0) / 2) ((max (x + e₂) 0 - max (x + e₂') 0) / 2)
  have t2 := abs_sub (max (x + (e₁ + e₂) / 2) 0 - max (x + (e₁' + e₂') / 2) 0)
    ((max (x + e₁) 0 - max (x + e₁') 0) / 2)
  rw [abs_div, abs_two] at t1 t2
  linarith

/-- Moving the kink is moving both coarse values (Giles 2015, §9.2):
`H(e₁, e₂; x + μ) = H(e₁ + μ, e₂ + μ; x)`. -/
lemma hingeAntithetic_add (e₁ e₂ x μ : ℝ) :
    hingeAntithetic e₁ e₂ (x + μ) = hingeAntithetic (e₁ + μ) (e₂ + μ) x := by
  unfold hingeAntithetic
  rw [show x + μ + (e₁ + e₂) / 2 = x + (e₁ + μ + (e₂ + μ)) / 2 by ring,
    show x + μ + e₁ = x + (e₁ + μ) by ring, show x + μ + e₂ = x + (e₂ + μ) by ring]

/-- **Moving the kink changes the antithetic difference by at most half the shift** (Giles 2015,
§9.2: the weak error of the inner discretisation moves the kink between the inner
approximations): `|H(e₁, e₂; x + μ) − H(e₁, e₂; x)| ≤ |μ|/2`, because `x ↦ H(e₁, e₂; x)` has
slope in `[−½, ½]`. -/
lemma abs_hingeAntithetic_shift_le (e₁ e₂ x μ : ℝ) :
    |hingeAntithetic e₁ e₂ (x + μ) - hingeAntithetic e₁ e₂ x| ≤ |μ| / 2 := by
  unfold hingeAntithetic
  rw [abs_le]
  rcases abs_cases μ with ⟨hμ, _⟩ | ⟨hμ, _⟩ <;> rw [hμ] <;>
    simp only [max_def] <;> split_ifs <;> constructor <;> linarith

/-- Moving the kink does not change the antithetic difference if the kink stays away from both
coarse values (Giles 2015, §9.2): if `|e₁| + |e₂| + |μ| ≤ |x|`, then
`H(e₁, e₂; x + μ) = H(e₁, e₂; x)` (both vanish, `hingeAntithetic_props`). -/
lemma hingeAntithetic_shift_eq {e₁ e₂ x μ : ℝ} (h : |e₁| + |e₂| + |μ| ≤ |x|) :
    hingeAntithetic e₁ e₂ (x + μ) - hingeAntithetic e₁ e₂ x = 0 := by
  obtain ⟨hz1, hz2, -, -⟩ := hingeAntithetic_props e₁ e₂
  have a1 := neg_abs_le e₁
  have a2 := neg_abs_le e₂
  have a3 := neg_abs_le μ
  have b1 := le_abs_self e₁
  have b2 := le_abs_self e₂
  have b3 := le_abs_self μ
  rcases abs_cases x with ⟨hx, hx0⟩ | ⟨hx, hx0⟩ <;> rw [hx] at h
  · rw [hz2 (x + μ) (by linarith) (by linarith), hz2 x (by linarith) (by linarith), sub_self]
  · rw [hz1 (x + μ) (by linarith) (by linarith), hz1 x (by linarith) (by linarith), sub_self]

/-- **The shift term lives near the kink** (Giles 2015, §9.2): with
`T = H(e₁, e₂; x + μ) − H(e₁, e₂; x)`, `x² T² ≤ (3/4)(e₁² + e₂² + μ²) μ²` and
`x² |T| ≤ (3/2)(e₁² + e₂² + μ²) |μ|`, since `T = 0` unless `|x| < |e₁| + |e₂| + |μ|`
(`hingeAntithetic_shift_eq`) and `|T| ≤ |μ|/2` (`abs_hingeAntithetic_shift_le`). -/
lemma sq_mul_sq_hingeAntithetic_shift_le (e₁ e₂ x μ : ℝ) :
    x ^ 2 * (hingeAntithetic e₁ e₂ (x + μ) - hingeAntithetic e₁ e₂ x) ^ 2 ≤
      3 / 4 * (e₁ ^ 2 + e₂ ^ 2 + μ ^ 2) * μ ^ 2 ∧
    x ^ 2 * |hingeAntithetic e₁ e₂ (x + μ) - hingeAntithetic e₁ e₂ x| ≤
      3 / 2 * (e₁ ^ 2 + e₂ ^ 2 + μ ^ 2) * |μ| := by
  set T := hingeAntithetic e₁ e₂ (x + μ) - hingeAntithetic e₁ e₂ x
  set s := |e₁| + |e₂| + |μ|
  have hs2 : s ^ 2 ≤ 3 * (e₁ ^ 2 + e₂ ^ 2 + μ ^ 2) := by
    have h1 := sq_abs e₁
    have h2 := sq_abs e₂
    have h3 := sq_abs μ
    nlinarith [sq_nonneg (|e₁| - |e₂|), sq_nonneg (|e₁| - |μ|), sq_nonneg (|e₂| - |μ|)]
  have hT := abs_hingeAntithetic_shift_le e₁ e₂ x μ
  have hT2 : T ^ 2 ≤ μ ^ 2 / 4 := by
    have := pow_le_pow_left₀ (abs_nonneg T) hT 2
    rw [sq_abs, div_pow, sq_abs] at this
    linarith
  have hR : 0 ≤ e₁ ^ 2 + e₂ ^ 2 + μ ^ 2 := by positivity
  by_cases h : s ≤ |x|
  · have h0 : T = 0 := hingeAntithetic_shift_eq h
    rw [h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, abs_zero]
    constructor <;> positivity
  · rw [not_le] at h
    have hx2 : x ^ 2 ≤ s ^ 2 := by
      rw [← sq_abs x]
      exact pow_le_pow_left₀ (abs_nonneg _) h.le 2
    have hx3 : x ^ 2 ≤ 3 * (e₁ ^ 2 + e₂ ^ 2 + μ ^ 2) := hx2.trans hs2
    constructor
    · calc x ^ 2 * T ^ 2 ≤ 3 * (e₁ ^ 2 + e₂ ^ 2 + μ ^ 2) * (μ ^ 2 / 4) :=
            mul_le_mul hx3 hT2 (sq_nonneg _) (by positivity)
        _ = 3 / 4 * (e₁ ^ 2 + e₂ ^ 2 + μ ^ 2) * μ ^ 2 := by ring
    · calc x ^ 2 * |T| ≤ 3 * (e₁ ^ 2 + e₂ ^ 2 + μ ^ 2) * (|μ| / 2) :=
            mul_le_mul hx3 hT (abs_nonneg _) (by positivity)
        _ = 3 / 2 * (e₁ ^ 2 + e₂ ^ 2 + μ ^ 2) * |μ| := by ring

/-- For `f(x) = a₀ + a₁x + c max(x − k, 0)` the antithetic difference of Giles 2015, §9.1, is
`c` times the hinge one, centred at any `G`:
`f(½(A + A′)) − ½ f(A) − ½ f(A′) = c H(A − G, A′ − G; G − k)` (the linear part of `f` cancels). -/
lemma kink_antithetic_eq_hinge {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) (G A A' : ℝ) :
    f ((A + A') / 2) - f A / 2 - f A' / 2 = c * hingeAntithetic (A - G) (A' - G) (G - k) := by
  rw [hf, hf, hf]
  unfold hingeAntithetic
  rw [show G - k + (A - G + (A' - G)) / 2 = (A + A') / 2 - k by ring,
    show G - k + (A - G) = A - k by ring, show G - k + (A' - G) = A' - k by ring]
  ring

/-- **The pathwise decomposition of the MIMC correction at a kink** (Giles 2015, §9.2, p. 59:
the six-term `Y_ℓ`).  Let `A₀, A₀′` be the two coarse inner means of `g_{ℓ₂}` and `A₁, A₁′`
those of `g_{ℓ₂+1}` (on the same inner samples), `G` a centre and `μ` a shift.  The difference
`H(A₁ − G, A₁′ − G; G − k) − H(A₀ − G, A₀′ − G; G − k)` is `P + T` with
`|P| ≤ |A₁ − A₀ − μ| + |A₁′ − A₀′ − μ|` (`hingeAntithetic_sub_le`, `hingeAntithetic_add`) and
the shift term `T = H(A₀ − G, A₀′ − G; G − k + μ) − H(A₀ − G, A₀′ − G; G − k)`.  Hence the bound
on its absolute value, and its square is at most `4(A₁ − A₀ − μ)² + 4(A₁′ − A₀′ − μ)² + 2T²`. -/
lemma mimc_hinge_le (G k μ A₀ A₀' A₁ A₁' : ℝ) :
    |hingeAntithetic (A₁ - G) (A₁' - G) (G - k) - hingeAntithetic (A₀ - G) (A₀' - G) (G - k)| ≤
        |A₁ - A₀ - μ| + |A₁' - A₀' - μ| +
          |hingeAntithetic (A₀ - G) (A₀' - G) (G - k + μ) -
            hingeAntithetic (A₀ - G) (A₀' - G) (G - k)| ∧
      (hingeAntithetic (A₁ - G) (A₁' - G) (G - k) -
          hingeAntithetic (A₀ - G) (A₀' - G) (G - k)) ^ 2 ≤
        4 * (A₁ - A₀ - μ) ^ 2 + 4 * (A₁' - A₀' - μ) ^ 2 +
          2 * (hingeAntithetic (A₀ - G) (A₀' - G) (G - k + μ) -
            hingeAntithetic (A₀ - G) (A₀' - G) (G - k)) ^ 2 := by
  set T := hingeAntithetic (A₀ - G) (A₀' - G) (G - k + μ) -
    hingeAntithetic (A₀ - G) (A₀' - G) (G - k)
  have hP := hingeAntithetic_sub_le (A₁ - G) (A₁' - G) (A₀ - G + μ) (A₀' - G + μ) (G - k)
  rw [← hingeAntithetic_add, show A₁ - G - (A₀ - G + μ) = A₁ - A₀ - μ by ring,
    show A₁' - G - (A₀' - G + μ) = A₁' - A₀' - μ by ring] at hP
  set P := hingeAntithetic (A₁ - G) (A₁' - G) (G - k) -
    hingeAntithetic (A₀ - G) (A₀' - G) (G - k + μ)
  have e : hingeAntithetic (A₁ - G) (A₁' - G) (G - k) -
      hingeAntithetic (A₀ - G) (A₀' - G) (G - k) = P + T := by
    simp only [P, T]
    ring
  rw [e]
  refine ⟨(abs_add_le P T).trans (by linarith), ?_⟩
  have hP2 : P ^ 2 ≤ (|A₁ - A₀ - μ| + |A₁' - A₀' - μ|) ^ 2 := by
    rw [← sq_abs P]
    exact pow_le_pow_left₀ (abs_nonneg _) hP 2
  have h1 := sq_abs (A₁ - A₀ - μ)
  have h2 := sq_abs (A₁' - A₀' - μ)
  nlinarith [sq_nonneg (P - T), sq_nonneg (|A₁ - A₀ - μ| - |A₁' - A₀' - μ|)]

/-- The hinge antithetic difference of measurable functions is measurable (Giles 2015, §9.1). -/
lemma measurable_hingeAntithetic_comp {α : Type*} [MeasurableSpace α] {a b x : α → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hx : Measurable x) :
    Measurable fun p => hingeAntithetic (a p) (b p) (x p) := by
  have hc : Continuous fun q : ℝ × ℝ × ℝ => hingeAntithetic q.1 q.2.1 q.2.2 := by
    unfold hingeAntithetic
    fun_prop
  exact hc.measurable.comp (ha.prodMk (hb.prodMk hx))

/-- **Combining two variance bounds** (`min(x, y) ≤ √(xy)`, the last step of
`nested_mimc_kink_variance_rate`): if `r ≥ 1`, `q > 0`, the constants are nonnegative,
`E ≤ K₁ (r⁻³ + c_w/(r²q))` and `E ≤ b/(q²r) + d/q³`, then `r² q E ≤ K₁ (1 + c_w) + (b + d)/2`.
For `q ≤ r` the first bound suffices; for `r < q` the second is at most `(b + d)/(q²r)`, and
`min(K₁/r³, K₂/(q²r)) ≤ √(K₁K₂)/(r²q)`.  With `r = 2^{ℓ₁/2}` and `q = 2^{ℓ₂}` this is
`E = O(2^{−ℓ₁−ℓ₂})`. -/
lemma mimc_kink_rate_combine {E K₁ b d c_w r q : ℝ} (hr : 1 ≤ r) (hq : 0 < q)
    (hK₁ : 0 ≤ K₁) (hb : 0 ≤ b) (hd : 0 ≤ d) (hcw : 0 ≤ c_w)
    (h1 : E ≤ K₁ * (1 / r ^ 3 + c_w / (r ^ 2 * q)))
    (h2 : E ≤ b / (q ^ 2 * r) + d / q ^ 3) :
    r ^ 2 * q * E ≤ K₁ * (1 + c_w) + (b + d) / 2 := by
  have hr0 : 0 < r := by linarith
  have h1' : r ^ 2 * q * E ≤ K₁ * (q / r + c_w) := by
    calc r ^ 2 * q * E ≤ r ^ 2 * q * (K₁ * (1 / r ^ 3 + c_w / (r ^ 2 * q))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K₁ * (q / r + c_w) := by field_simp
  have hK₂ : 0 ≤ b + d := by positivity
  rcases le_or_gt q r with hqr | hrq
  · have : q / r ≤ 1 := (div_le_one hr0).2 hqr
    have : K₁ * (q / r + c_w) ≤ K₁ * (1 + c_w) := by gcongr
    linarith
  · have h2' : r ^ 2 * q * E ≤ (b + d) * (r / q) := by
      have hrq1 : r / q ≤ 1 := (div_le_one hq).2 hrq.le
      have hrq0 : 0 ≤ r / q := by positivity
      calc r ^ 2 * q * E ≤ r ^ 2 * q * (b / (q ^ 2 * r) + d / q ^ 3) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = b * (r / q) + d * (r / q) ^ 2 := by field_simp
        _ ≤ b * (r / q) + d * (r / q) := by
            gcongr
            nlinarith
        _ = (b + d) * (r / q) := by ring
    set X := r ^ 2 * q * E - K₁ * c_w with hX
    have hX1 : X ≤ K₁ * (q / r) := by rw [hX]; linarith
    have hX2 : X ≤ (b + d) * (r / q) := by
      rw [hX]
      have : 0 ≤ K₁ * c_w := by positivity
      linarith
    rcases le_or_gt X 0 with hX0 | hX0
    · have : 0 ≤ K₁ + (b + d) / 2 := by positivity
      nlinarith
    · have hprod : X * X ≤ K₁ * (q / r) * ((b + d) * (r / q)) :=
        mul_le_mul hX1 hX2 hX0.le (by positivity)
      have e : K₁ * (q / r) * ((b + d) * (r / q)) = K₁ * (b + d) := by
        field_simp
      rw [e] at hprod
      have : X ≤ (K₁ + (b + d)) / 2 := by
        nlinarith [sq_nonneg (K₁ - (b + d)), sq_nonneg (X - (K₁ + (b + d)) / 2)]
      nlinarith

/-- `r = 2^{ℓ/2}` satisfies `r > 0`, `r ≥ 1`, `r² = 2^ℓ` and `r³ = 2^{3ℓ/2}` (the square root of
the number `2^ℓ` of inner samples, Giles 2015, §9.1–§9.2). -/
lemma two_rpow_half_props (ℓ : ℕ) :
    0 < (2 : ℝ) ^ ((ℓ : ℝ) / 2) ∧ 1 ≤ (2 : ℝ) ^ ((ℓ : ℝ) / 2) ∧
      ((2 : ℝ) ^ ((ℓ : ℝ) / 2)) ^ 2 = 2 ^ ℓ ∧
      ((2 : ℝ) ^ ((ℓ : ℝ) / 2)) ^ 3 = (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) := by
  refine ⟨by positivity, Real.one_le_rpow (by norm_num) (by positivity), ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring

/-- **The cross-difference in two dimensions, boundary cases included** (Giles 2015, §2.4): for
`ℓ = (ℓ₁, ℓ₂)`,
`ΔP_ℓ = (P_{ℓ₁,ℓ₂} − [ℓ₁ > 0] P_{ℓ₁−1,ℓ₂}) − [ℓ₂ > 0](P_{ℓ₁,ℓ₂−1} − [ℓ₁ > 0] P_{ℓ₁−1,ℓ₂−1})`. -/
lemma crossDiff_two_eq (E : ℕ → ℕ → ℝ) (ℓ : Fin 2 → ℕ) :
    crossDiff (fun m => E (m 0) (m 1)) ℓ =
      (E (ℓ 0) (ℓ 1) - if ℓ 0 = 0 then 0 else E (ℓ 0 - 1) (ℓ 1)) -
        if ℓ 1 = 0 then 0 else
          (E (ℓ 0) (ℓ 1 - 1) - if ℓ 0 = 0 then 0 else E (ℓ 0 - 1) (ℓ 1 - 1)) := by
  rw [crossDiff_succ, crossDiff_one, crossDiff_one]
  simp only [Fin.cons_zero, Fin.cons_one, Fin.tail_def, Fin.succ_zero_eq_one]
  split_ifs <;> ring

/-! ### One outer sample -/

section Fiber

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒲] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **The inner sampling fluctuation, for one outer sample** (Giles 2015, §9.1:
"`Δg = O(M^{−1/2})`", in `L²`): if `E_W[h(z, W)⁴] < ∞` and `M ≥ 1`, then
`M E[(A_M(h) − E_W[h(z, W)])²] = Var_W[h(z, W)] ≤ E_W[h(z, W)²]` (`fiber_sum_moments`). -/
lemma fiber_centred_sq_le (h : 𝒵 → 𝒲 → ℝ) (z : 𝒵) (hhz : Measurable (h z))
    (hh4 : Integrable (fun v => h z v ^ 4) ρ) {M : ℕ} (hM : 0 < M) :
    Integrable (fun w : ℕ → 𝒲 => (innerMean h M z w - ∫ v, h z v ∂ρ) ^ 2) (innerLaw ρ) ∧
      (M : ℝ) * ∫ w, (innerMean h M z w - ∫ v, h z v ∂ρ) ^ 2 ∂(innerLaw ρ) ≤
        ∫ v, h z v ^ 2 ∂ρ := by
  obtain ⟨i4, -, e2, -⟩ := fiber_sum_moments ρ hhz hh4 (nestedSign M) (nestedSign_sq M) M
  obtain ⟨a, ha⟩ : ∃ a, a = ∫ v, h z v ∂ρ := ⟨_, rfl⟩
  rw [← ha] at i4 e2 ⊢
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hE : ∀ w, innerMean h M z w - a =
      (M : ℝ)⁻¹ * ∑ m ∈ range M, nestedSign M m * (h z (w m) - a) :=
    fun w => centred_sum_eq h hM z w a
  simp only [hE, mul_pow]
  set S : (ℕ → 𝒲) → ℝ := fun w => ∑ m ∈ range M, nestedSign M m * (h z (w m) - a) with hS
  have hSm : Measurable S := by
    rw [hS]
    exact Finset.measurable_sum _ fun m _ =>
      ((hhz.comp (measurable_pi_apply m)).sub_const a).const_mul _
  have i2 : Integrable (fun w => S w ^ 2) (innerLaw ρ) :=
    integrable_pow_of_pow_four hSm i4 (by norm_num)
  refine ⟨i2.const_mul _, ?_⟩
  rw [integral_const_mul, e2]
  have hvar : ∫ v, (h z v - a) ^ 2 ∂ρ ≤ ∫ v, h z v ^ 2 ∂ρ := by
    have h1 := variance_le_expectation_sq (μ := ρ) hhz.aestronglyMeasurable
    rw [variance_eq_integral hhz.aemeasurable] at h1
    simpa only [Pi.pow_apply, ← ha] using h1
  calc (M : ℝ) * ((M : ℝ)⁻¹ ^ 2 * (M * ∫ v, (h z v - a) ^ 2 ∂ρ))
      = ∫ v, (h z v - a) ^ 2 ∂ρ := by field_simp
    _ ≤ ∫ v, h z v ^ 2 ∂ρ := hvar

/-- The two coarse inner means of one outer sample, centred at `G = E_W[g(z, W)]` (Giles 2015,
§9.1): if `E_W[g(z, W)⁴] < ∞` and `M ≥ 1`, then `M E[(A_M − G)² + (A′_M − G)²] ≤ 2(1 + 16κ)`
with `κ = E_W[(g(z, W) − G)⁴]` (`fiber_centred_moments`; the second half of the inner samples
has the law of the first). -/
lemma fiber_two_halves_sq_le (g : 𝒵 → 𝒲 → ℝ) (z : 𝒵) (hgz : Measurable (g z))
    (hgz4 : Integrable (fun v => g z v ^ 4) ρ) {M : ℕ} (hM : 0 < M) :
    Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 2 +
        (innerMean g M z (shiftSeq M w) - ∫ v, g z v ∂ρ) ^ 2) (innerLaw ρ) ∧
      (M : ℝ) * ∫ w, ((innerMean g M z w - ∫ v, g z v ∂ρ) ^ 2 +
        (innerMean g M z (shiftSeq M w) - ∫ v, g z v ∂ρ) ^ 2) ∂(innerLaw ρ) ≤
        2 * (1 + 16 * ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ) := by
  obtain ⟨-, -, i4, h2, -, -⟩ := fiber_centred_moments ρ g z hgz hgz4 hM
  have hsh : MeasurePreserving (shiftSeq (𝒲 := 𝒲) M) (innerLaw ρ) (innerLaw ρ) :=
    measurePreserving_shiftSeq ρ M
  have hem : Measurable fun w : ℕ → 𝒲 => innerMean g M z w - ∫ v, g z v ∂ρ :=
    (measurable_innerMean_right hgz M).sub_const _
  have ie : Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 2)
      (innerLaw ρ) := integrable_pow_of_pow_four hem i4 (by norm_num)
  have ie' : Integrable (fun w : ℕ → 𝒲 => (innerMean g M z (shiftSeq M w) - ∫ v, g z v ∂ρ) ^ 2)
      (innerLaw ρ) := hsh.integrable_comp_of_integrable ie
  have ee : ∫ w, (innerMean g M z (shiftSeq M w) - ∫ v, g z v ∂ρ) ^ 2 ∂(innerLaw ρ) =
      ∫ w, (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 2 ∂(innerLaw ρ) :=
    integral_comp_of_measurePreserving hsh ie.aestronglyMeasurable
  refine ⟨ie.add ie', ?_⟩
  rw [integral_add ie ie', ee]
  linarith

end Fiber

/-! ### Averaging over the outer sample: the fluctuation and the shift of the kink -/

section Product

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **The inner sampling fluctuation, averaged over the outer sample** (Giles 2015, §9.2): if
`E_W[h(z, W)⁴] < ∞` for `ν`-a.e. `z`, `E[h(Z, W)²] < ∞` and `M ≥ 1`, then
`M E[(A_M(h) − E_W[h(Z, W)])²] ≤ E[h(Z, W)²]` (`fiber_centred_sq_le`, Fubini).  For
`h = g_{ℓ₂+1} − g_{ℓ₂}` the inner sampling divides the strong error by the number of inner
samples. -/
lemma integral_centred_innerMean_sq_le {h : 𝒵 → 𝒲 → ℝ} (hh : Measurable (Function.uncurry h))
    (hh4 : ∀ᵐ z ∂ν, Integrable (fun v => h z v ^ 4) ρ)
    (hh2 : Integrable (fun p : 𝒵 × 𝒲 => h p.1 p.2 ^ 2) (ν.prod ρ)) {M : ℕ} (hM : 0 < M) :
    Integrable (fun p : 𝒵 × (ℕ → 𝒲) => (innerMean h M p.1 p.2 - ∫ v, h p.1 v ∂ρ) ^ 2)
        (nestedLaw ν ρ) ∧
      (M : ℝ) * ∫ p, (innerMean h M p.1 p.2 - ∫ v, h p.1 v ∂ρ) ^ 2 ∂(nestedLaw ν ρ) ≤
        ∫ p, h p.1 p.2 ^ 2 ∂(ν.prod ρ) := by
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hGm : Measurable fun z => ∫ v, h z v ∂ρ :=
    (hh.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  have hFm : Measurable fun p : 𝒵 × (ℕ → 𝒲) => (innerMean h M p.1 p.2 - ∫ v, h p.1 v ∂ρ) ^ 2 :=
    ((measurable_innerMean hh M measurable_id).sub (hGm.comp measurable_fst)).pow_const 2
  obtain ⟨hint, hle⟩ := integrable_of_fiber_bound ν ρ
    (F := fun p => (innerMean h M p.1 p.2 - ∫ v, h p.1 v ∂ρ) ^ 2) hFm (fun p => sq_nonneg _)
    (hh2.integral_prod_left.div_const (M : ℝ))
    (hh4.mono fun z hz => by
      obtain ⟨i, hb⟩ := fiber_centred_sq_le ρ h z hh.of_uncurry_left hz hM
      refine ⟨i, ?_⟩
      show ∫ w, (innerMean h M z w - ∫ v, h z v ∂ρ) ^ 2 ∂(innerLaw ρ) ≤
        (∫ v, h z v ^ 2 ∂ρ) / M
      rw [le_div_iff₀ hM0, mul_comm]
      exact hb)
  refine ⟨hint, ?_⟩
  rw [integral_div, ← integral_prod _ hh2, le_div_iff₀ hM0] at hle
  linarith

/-- **The small-ball estimate for a function of the outer and the inner samples** (Giles 2015,
§9.1–§9.2).  If `F ≥ 0` is measurable, and for `ν`-a.e. `z` `F(z, w) ≤ A` for all `w` and
`v(z)² E_W[F(z, W)] ≤ B`, and `u` is within `δ` of `v` a.e. with `ν{|u| ≤ t} ≤ c t` for all
`t > 0`, then `F` is integrable and `E[F] ≤ 2c √(A (2B + 2δ²A))`
(`integral_le_of_small_ball_near`, Fubini). -/
lemma integral_le_of_fiber_small_ball {F : 𝒵 × (ℕ → 𝒲) → ℝ} (hFm : Measurable F)
    (hF0 : ∀ p, 0 ≤ F p) {A B δ c_d : ℝ} {u v : 𝒵 → ℝ}
    (hfib : ∀ᵐ z ∂ν, (∀ w, F (z, w) ≤ A) ∧ v z ^ 2 * ∫ w, F (z, w) ∂(innerLaw ρ) ≤ B)
    (huv : ∀ᵐ z ∂ν, |u z - v z| ≤ δ)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |u z| ≤ t} ≤ ENNReal.ofReal (c_d * t)) :
    Integrable F (nestedLaw ν ρ) ∧
      ∫ p, F p ∂(nestedLaw ν ρ) ≤ 2 * c_d * Real.sqrt (A * (2 * B + 2 * δ ^ 2 * A)) := by
  have hfibA : ∀ᵐ z ∂ν, Integrable (fun w => F (z, w)) (innerLaw ρ) ∧
      ∫ w, F (z, w) ∂(innerLaw ρ) ≤ A := hfib.mono fun z hz => by
    have hi : Integrable (fun w => F (z, w)) (innerLaw ρ) :=
      (integrable_const A).mono' (hFm.comp measurable_prodMk_left).aestronglyMeasurable
        (Eventually.of_forall fun w => by
          rw [Real.norm_of_nonneg (hF0 _)]
          exact hz.1 w)
    refine ⟨hi, ?_⟩
    have := integral_mono hi (integrable_const A) fun w => hz.1 w
    rwa [integral_const, probReal_univ, one_smul] at this
  obtain ⟨hint, -⟩ := integrable_of_fiber_bound ν ρ hFm hF0 (integrable_const A) hfibA
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  have hGm : AEMeasurable (fun z => ∫ w, F (z, w) ∂(innerLaw ρ)) ν :=
    (hFm.stronglyMeasurable.integral_prod_right' (ν := innerLaw ρ)).measurable.aemeasurable
  refine integral_le_of_small_ball_near hGm
    (Eventually.of_forall fun z => integral_nonneg fun w => hF0 _)
    (hfibA.mono fun z hz => hz.2) (hfib.mono fun z hz => hz.2) huv (nonneg_of_small_ball hball)
    hball

/-- **The shift term is `O(2^{−ℓ₂})` on a set of probability `O(2^{−ℓ₁/2} + 2^{−ℓ₂})`** (Giles
2015, §9.2).  Let `G₀(z) = E_W[g₀(z, W)]`, let the centred conditional fourth moments of `g₀` be
at most `m₄` for `ν`-a.e. `z`, let `|μ| ≤ μ_max` a.e., and let `u` be within `δ` of `G₀ − k`
a.e. with `ν{|u| ≤ t} ≤ c_d t`.  For `M ≥ 1` inner samples and `R ≥ 0` with
`6(1 + 16m₄)/M + 3μ_max² + δ² ≤ R²`, the shift term
`T = H(A − G₀, A′ − G₀; G₀ − k + μ) − H(A − G₀, A′ − G₀; G₀ − k)` (`A, A′` the two coarse inner
means of `g₀`) is measurable, `E[T²] ≤ c_d μ_max² R` and `E|T| ≤ 2 c_d μ_max R`
(`sq_mul_sq_hingeAntithetic_shift_le`, `fiber_two_halves_sq_le`,
`integral_le_of_fiber_small_ball`). -/
lemma mimc_shift_term_le {g₀ : 𝒵 → 𝒲 → ℝ} (hg₀ : Measurable (Function.uncurry g₀)) {m₄ : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g₀ z v ^ 4) ρ ∧
      ∫ v, (g₀ z v - ∫ u, g₀ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {μ : 𝒵 → ℝ} (hμm : Measurable μ) {μmax : ℝ} (hμ : ∀ᵐ z ∂ν, |μ z| ≤ μmax)
    {k δ c_d R : ℝ} {u : 𝒵 → ℝ} (hδ : ∀ᵐ z ∂ν, |u z - (∫ v, g₀ z v ∂ρ - k)| ≤ δ)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |u z| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    {M : ℕ} (hM : 0 < M) (hR : 0 ≤ R)
    (hR2 : 6 * (1 + 16 * m₄) / M + 3 * μmax ^ 2 + δ ^ 2 ≤ R ^ 2)
    (T : 𝒵 × (ℕ → 𝒲) → ℝ)
    (hT : ∀ p, T p = hingeAntithetic (innerMean g₀ M p.1 p.2 - ∫ v, g₀ p.1 v ∂ρ)
        (innerMean g₀ M p.1 (shiftSeq M p.2) - ∫ v, g₀ p.1 v ∂ρ) (∫ v, g₀ p.1 v ∂ρ - k + μ p.1) -
      hingeAntithetic (innerMean g₀ M p.1 p.2 - ∫ v, g₀ p.1 v ∂ρ)
        (innerMean g₀ M p.1 (shiftSeq M p.2) - ∫ v, g₀ p.1 v ∂ρ) (∫ v, g₀ p.1 v ∂ρ - k)) :
    Measurable T ∧ Integrable (fun p => T p ^ 2) (nestedLaw ν ρ) ∧
      ∫ p, T p ^ 2 ∂(nestedLaw ν ρ) ≤ c_d * μmax ^ 2 * R ∧
      Integrable (fun p => |T p|) (nestedLaw ν ρ) ∧
      ∫ p, |T p| ∂(nestedLaw ν ρ) ≤ 2 * c_d * μmax * R := by
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hcd : 0 ≤ c_d := nonneg_of_small_ball hball
  have hμ0 : 0 ≤ μmax := by
    obtain ⟨z, hz⟩ := hμ.exists
    exact (abs_nonneg _).trans hz
  have hm₄ : 0 ≤ m₄ := by
    obtain ⟨z, hz⟩ := hfib.exists
    exact (integral_nonneg fun v => by positivity).trans hz.2
  have hGm : Measurable fun z => ∫ v, g₀ z v ∂ρ :=
    (hg₀.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  have hA : Measurable fun p : 𝒵 × (ℕ → 𝒲) => innerMean g₀ M p.1 p.2 - ∫ v, g₀ p.1 v ∂ρ :=
    (measurable_innerMean hg₀ M measurable_id).sub (hGm.comp measurable_fst)
  have hA' : Measurable fun p : 𝒵 × (ℕ → 𝒲) =>
      innerMean g₀ M p.1 (shiftSeq M p.2) - ∫ v, g₀ p.1 v ∂ρ :=
    (measurable_innerMean hg₀ M (measurable_shiftSeq M)).sub (hGm.comp measurable_fst)
  have hTm : Measurable T := by
    have e : T = fun p => hingeAntithetic (innerMean g₀ M p.1 p.2 - ∫ v, g₀ p.1 v ∂ρ)
        (innerMean g₀ M p.1 (shiftSeq M p.2) - ∫ v, g₀ p.1 v ∂ρ) (∫ v, g₀ p.1 v ∂ρ - k + μ p.1) -
      hingeAntithetic (innerMean g₀ M p.1 p.2 - ∫ v, g₀ p.1 v ∂ρ)
        (innerMean g₀ M p.1 (shiftSeq M p.2) - ∫ v, g₀ p.1 v ∂ρ) (∫ v, g₀ p.1 v ∂ρ - k) :=
      funext hT
    rw [e]
    exact (measurable_hingeAntithetic_comp hA hA'
      (((hGm.comp measurable_fst).sub_const k).add (hμm.comp measurable_fst))).sub
      (measurable_hingeAntithetic_comp hA hA' ((hGm.comp measurable_fst).sub_const k))
  -- the fibre bounds
  set K : ℝ := 2 * (1 + 16 * m₄) / M with hK
  have hfibT : ∀ᵐ z ∂ν, (∀ w, |T (z, w)| ≤ μmax / 2) ∧
      Integrable (fun w => T (z, w) ^ 2) (innerLaw ρ) ∧
      Integrable (fun w => |T (z, w)|) (innerLaw ρ) ∧
      (∫ v, g₀ z v ∂ρ - k) ^ 2 * ∫ w, T (z, w) ^ 2 ∂(innerLaw ρ) ≤
        3 / 4 * μmax ^ 2 * (K + μmax ^ 2) ∧
      (∫ v, g₀ z v ∂ρ - k) ^ 2 * ∫ w, |T (z, w)| ∂(innerLaw ρ) ≤
        3 / 2 * μmax * (K + μmax ^ 2) := by
    filter_upwards [hfib, hμ] with z ⟨hz4, hzm⟩ hμz
    obtain ⟨iS, hS⟩ := fiber_two_halves_sq_le ρ g₀ z hg₀.of_uncurry_left hz4 hM
    set G := ∫ v, g₀ z v ∂ρ
    set S : (ℕ → 𝒲) → ℝ := fun w => (innerMean g₀ M z w - G) ^ 2 +
      (innerMean g₀ M z (shiftSeq M w) - G) ^ 2 with hSdef
    have hSK : ∫ w, S w ∂(innerLaw ρ) ≤ K := by
      rw [hK, le_div_iff₀ hM0, mul_comm]
      refine hS.trans ?_
      gcongr
    have hb : ∀ w, |T (z, w)| ≤ μmax / 2 := fun w => by
      rw [hT]
      exact (abs_hingeAntithetic_shift_le _ _ _ _).trans (by linarith)
    have hTzm : Measurable fun w => T (z, w) := hTm.comp measurable_prodMk_left
    have i2 : Integrable (fun w => T (z, w) ^ 2) (innerLaw ρ) :=
      (integrable_const ((μmax / 2) ^ 2)).mono' (hTzm.pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun w => by
          rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hb w) 2)
    have i1 : Integrable (fun w => |T (z, w)|) (innerLaw ρ) :=
      (integrable_const (μmax / 2)).mono' (continuous_abs.measurable.comp hTzm).aestronglyMeasurable
        (Eventually.of_forall fun w => by rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hb w)
    have hμ2 : μ z ^ 2 ≤ μmax ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hμz 2
    have hpt : ∀ w, (G - k) ^ 2 * T (z, w) ^ 2 ≤ 3 / 4 * (S w + μ z ^ 2) * μ z ^ 2 ∧
        (G - k) ^ 2 * |T (z, w)| ≤ 3 / 2 * (S w + μ z ^ 2) * |μ z| := fun w => by
      rw [hT]
      have := sq_mul_sq_hingeAntithetic_shift_le (innerMean g₀ M z w - G)
        (innerMean g₀ M z (shiftSeq M w) - G) (G - k) (μ z)
      simp only [hSdef]
      exact this
    have j : Integrable (fun w => S w + μ z ^ 2) (innerLaw ρ) := iS.add (integrable_const _)
    have hS0 : 0 ≤ ∫ w, S w ∂(innerLaw ρ) := integral_nonneg fun w => by positivity
    refine ⟨hb, i2, i1, ?_, ?_⟩
    · rw [← integral_const_mul]
      refine (integral_mono (i2.const_mul _) ((j.const_mul _).mul_const _)
        fun w => (hpt w).1).trans ?_
      rw [integral_mul_const, integral_const_mul, integral_add iS (integrable_const _),
        integral_const, probReal_univ, one_smul]
      calc 3 / 4 * (∫ w, S w ∂(innerLaw ρ) + μ z ^ 2) * μ z ^ 2
          ≤ 3 / 4 * (K + μmax ^ 2) * μmax ^ 2 := by gcongr
        _ = 3 / 4 * μmax ^ 2 * (K + μmax ^ 2) := by ring
    · rw [← integral_const_mul]
      refine (integral_mono (i1.const_mul _) ((j.const_mul _).mul_const _)
        fun w => (hpt w).2).trans ?_
      rw [integral_mul_const, integral_const_mul, integral_add iS (integrable_const _),
        integral_const, probReal_univ, one_smul]
      calc 3 / 2 * (∫ w, S w ∂(innerLaw ρ) + μ z ^ 2) * |μ z|
          ≤ 3 / 2 * (K + μmax ^ 2) * μmax := by gcongr
        _ = 3 / 2 * μmax * (K + μmax ^ 2) := by ring
  have huv : ∀ᵐ z ∂ν, |u z - (∫ v, g₀ z v ∂ρ - k)| ≤ δ := hδ
  have hK0 : 0 ≤ K := by positivity
  have hX : K * 3 + 3 * μmax ^ 2 + δ ^ 2 ≤ R ^ 2 := by
    have : K * 3 = 6 * (1 + 16 * m₄) / M := by rw [hK]; ring
    linarith
  -- the square
  obtain ⟨hT2i, hT2⟩ := integral_le_of_fiber_small_ball ν ρ (hTm.pow_const 2)
    (fun p => sq_nonneg _) (A := (μmax / 2) ^ 2) (B := 3 / 4 * μmax ^ 2 * (K + μmax ^ 2))
    (v := fun z => ∫ v, g₀ z v ∂ρ - k)
    (hfibT.mono fun z hz => ⟨fun w => by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hz.1 w) 2, hz.2.2.2.1⟩) huv hball
  -- the absolute value
  obtain ⟨hT1i, hT1⟩ := integral_le_of_fiber_small_ball ν ρ (continuous_abs.measurable.comp hTm)
    (fun p => abs_nonneg _)
    (A := μmax / 2) (B := 3 / 2 * μmax * (K + μmax ^ 2)) (v := fun z => ∫ v, g₀ z v ∂ρ - k)
    (hfibT.mono fun z hz => ⟨hz.1, hz.2.2.2.2⟩) huv hball
  refine ⟨hTm, hT2i, hT2.trans ?_, hT1i, hT1.trans ?_⟩
  · have hs : Real.sqrt ((μmax / 2) ^ 2 * (2 * (3 / 4 * μmax ^ 2 * (K + μmax ^ 2)) +
        2 * δ ^ 2 * (μmax / 2) ^ 2)) ≤ μmax ^ 2 * R / 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      have e : (μmax / 2) ^ 2 * (2 * (3 / 4 * μmax ^ 2 * (K + μmax ^ 2)) +
          2 * δ ^ 2 * (μmax / 2) ^ 2) = μmax ^ 4 / 8 * (K * 3 + 3 * μmax ^ 2 + δ ^ 2) := by ring
      rw [e]
      calc μmax ^ 4 / 8 * (K * 3 + 3 * μmax ^ 2 + δ ^ 2) ≤ μmax ^ 4 / 8 * R ^ 2 := by gcongr
        _ ≤ (μmax ^ 2 * R / 2) ^ 2 := by
            have : 0 ≤ μmax ^ 4 * R ^ 2 := by positivity
            nlinarith
    calc 2 * c_d * Real.sqrt ((μmax / 2) ^ 2 * (2 * (3 / 4 * μmax ^ 2 * (K + μmax ^ 2)) +
          2 * δ ^ 2 * (μmax / 2) ^ 2)) ≤ 2 * c_d * (μmax ^ 2 * R / 2) := by gcongr
      _ = c_d * μmax ^ 2 * R := by ring
  · have hs : Real.sqrt (μmax / 2 * (2 * (3 / 2 * μmax * (K + μmax ^ 2)) +
        2 * δ ^ 2 * (μmax / 2))) ≤ μmax * R := by
      rw [Real.sqrt_le_left (by positivity)]
      have e : μmax / 2 * (2 * (3 / 2 * μmax * (K + μmax ^ 2)) + 2 * δ ^ 2 * (μmax / 2)) =
          μmax ^ 2 / 2 * (K * 3 + 3 * μmax ^ 2 + δ ^ 2) := by ring
      rw [e]
      calc μmax ^ 2 / 2 * (K * 3 + 3 * μmax ^ 2 + δ ^ 2) ≤ μmax ^ 2 / 2 * R ^ 2 := by gcongr
        _ ≤ (μmax * R) ^ 2 := by
            have : 0 ≤ μmax ^ 2 * R ^ 2 := by positivity
            nlinarith
    calc 2 * c_d * Real.sqrt (μmax / 2 * (2 * (3 / 2 * μmax * (K + μmax ^ 2)) +
          2 * δ ^ 2 * (μmax / 2))) ≤ 2 * c_d * (μmax * R) := by gcongr
      _ = 2 * c_d * μmax * R := by ring

/-- **The level difference of the inner approximations, for one outer sample** (Giles 2015,
§9.2): if the centred conditional fourth moments of every `g_j` are at most `m₄` and
`2^j |E_W[g_j(z, W)] − E_W[g(z, W)]| ≤ c_w` (`ν`-a.e.), then `H = g_{ℓ+1} − g_ℓ` has, for
`ν`-a.e. `z`, `E_W[H⁴] < ∞`, `|E_W[H]| ≤ (3/2) c_w 2^{−ℓ}` and
`E_W[H²] ≤ 3(1 + m₄) + 3((3/2) c_w 2^{−ℓ})²`, and `H²` is `ν ⊗ ρ`-integrable (the fibre bounds
of `integral_innerMean_levelDiff_sq_le`). -/
lemma levelDiff_fiber_bounds {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w) (ℓ : ℕ) :
    (∀ᵐ z ∂ν, Integrable (fun v => (gh (ℓ + 1) z v - gh ℓ z v) ^ 4) ρ ∧
      |∫ v, (gh (ℓ + 1) z v - gh ℓ z v) ∂ρ| ≤ 3 * c_w / (2 * 2 ^ ℓ) ∧
      ∫ v, (gh (ℓ + 1) z v - gh ℓ z v) ^ 2 ∂ρ ≤
        3 * (1 + m₄) + 3 * (3 * c_w / (2 * 2 ^ ℓ)) ^ 2) ∧
    Integrable (fun p : 𝒵 × 𝒲 => (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2) (ν.prod ρ) := by
  set q : ℝ := (2 : ℝ) ^ ℓ with hq
  have hq0 : 0 < q := by positivity
  set d : ℝ := 3 * c_w / (2 * q) with hd
  set H : 𝒵 → 𝒲 → ℝ := fun z v => gh (ℓ + 1) z v - gh ℓ z v with hH
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
  refine ⟨hfibH, ?_⟩
  exact integrable_prod_of_fiber_bound ν ρ (F := fun p => H p.1 p.2 ^ 2) (hHm.pow_const 2)
    (fun p => sq_nonneg _) (hfibH.mono fun z hz =>
      ⟨integrable_pow_of_pow_four hHm.of_uncurry_left hz.1 (by norm_num), hz.2.2⟩)

/-- **The decomposition behind the corrected rate** (Giles 2015, §9.2, pp. 59–60).  Let
`f(x) = a₀ + a₁x + c max(x − k, 0)`, with the centred conditional fourth moments, the weak error
and the small ball of `nested_mimc_kink_variance_rate`.  Then for `Y = Y_{(ℓ₁+1, ℓ₂+1)}`
(`nestedMimcDelta`) there are `ε, ε′, T` with `|Y| ≤ |c|(|ε| + |ε′| + |T|)` and
`Y² ≤ 4c²ε² + 4c²ε′² + 2c²T²`: `ε, ε′` are the inner sampling fluctuations of
`g_{ℓ₂+1} − g_{ℓ₂}` over the two halves of the `2^{ℓ₁+1}` inner samples, with `E[ε′²] = E[ε²]`
and `2^{ℓ₁} E[ε²] ≤ E[(g_{ℓ₂+1} − g_{ℓ₂})²]` (`integral_centred_innerMean_sq_le`), and `T` is
the shift term of `mimc_shift_term_le` for the weak error `μ = E_W[g_{ℓ₂+1} − g_{ℓ₂}]`, with
`μ_max = (3/2) c_w 2^{−ℓ₂}` and `R = (7 + 96 m₄) 2^{−ℓ₁/2} + 3 c_w 2^{−ℓ₂}` (`mimc_hinge_le`). -/
lemma mimc_kink_split {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w c_d : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (ℓ₁ ℓ₂ : ℕ) :
    ∃ ε ε' T : 𝒵 × (ℕ → 𝒲) → ℝ, Measurable ε ∧ Measurable ε' ∧
      (∀ p, |nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) p| ≤ |c| * (|ε p| + |ε' p| + |T p|)) ∧
      (∀ p, nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) p ^ 2 ≤
        4 * c ^ 2 * ε p ^ 2 + 4 * c ^ 2 * ε' p ^ 2 + 2 * c ^ 2 * T p ^ 2) ∧
      Integrable (fun p => ε p ^ 2) (nestedLaw ν ρ) ∧
      Integrable (fun p => ε' p ^ 2) (nestedLaw ν ρ) ∧
      ∫ p, ε' p ^ 2 ∂(nestedLaw ν ρ) = ∫ p, ε p ^ 2 ∂(nestedLaw ν ρ) ∧
      Integrable (fun p : 𝒵 × 𝒲 => (gh (ℓ₂ + 1) p.1 p.2 - gh ℓ₂ p.1 p.2) ^ 2) (ν.prod ρ) ∧
      (2 : ℝ) ^ ℓ₁ * ∫ p, ε p ^ 2 ∂(nestedLaw ν ρ) ≤
        ∫ p, (gh (ℓ₂ + 1) p.1 p.2 - gh ℓ₂ p.1 p.2) ^ 2 ∂(ν.prod ρ) ∧
      Integrable (fun p => T p ^ 2) (nestedLaw ν ρ) ∧
      ∫ p, T p ^ 2 ∂(nestedLaw ν ρ) ≤ c_d * (3 * c_w / (2 * 2 ^ ℓ₂)) ^ 2 *
        ((7 + 96 * m₄) / (2 : ℝ) ^ ((ℓ₁ : ℝ) / 2) + 3 * c_w / 2 ^ ℓ₂) ∧
      Integrable (fun p => |T p|) (nestedLaw ν ρ) ∧
      ∫ p, |T p| ∂(nestedLaw ν ρ) ≤ 2 * c_d * (3 * c_w / (2 * 2 ^ ℓ₂)) *
        ((7 + 96 * m₄) / (2 : ℝ) ^ ((ℓ₁ : ℝ) / 2) + 3 * c_w / 2 ^ ℓ₂) := by
  have hcw : 0 ≤ c_w := by
    obtain ⟨z, hz⟩ := (hw 0).exists
    exact le_trans (by positivity) hz
  have hm₄ : 0 ≤ m₄ := by
    obtain ⟨z, hz⟩ := (hfib 0).exists
    exact (integral_nonneg fun v => by positivity).trans hz.2
  set M : ℕ := 2 ^ ℓ₁ with hMdef
  have hM : 0 < M := by positivity
  set q : ℝ := (2 : ℝ) ^ ℓ₂ with hq
  have hq0 : 0 < q := by positivity
  obtain ⟨hr0, -, hr2, -⟩ := two_rpow_half_props ℓ₁
  set r : ℝ := (2 : ℝ) ^ ((ℓ₁ : ℝ) / 2) with hr
  have hMr : (M : ℝ) = r ^ 2 := by rw [hr2, hMdef]; push_cast; ring
  set H : 𝒵 → 𝒲 → ℝ := fun z v => gh (ℓ₂ + 1) z v - gh ℓ₂ z v with hHdef
  have hHm : Measurable (Function.uncurry H) := (hgh (ℓ₂ + 1)).sub (hgh ℓ₂)
  obtain ⟨hfibH, hH2⟩ := levelDiff_fiber_bounds ν ρ hgh hfib hw ℓ₂
  obtain ⟨iε, hε⟩ := integral_centred_innerMean_sq_le ν ρ hHm (hfibH.mono fun z hz => hz.1)
    hH2 hM
  set μ : 𝒵 → ℝ := fun z => ∫ v, H z v ∂ρ with hμdef
  have hμm : Measurable μ := (hHm.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  have hμ : ∀ᵐ z ∂ν, |μ z| ≤ 3 * c_w / (2 * q) := hfibH.mono fun z hz => hz.2.1
  set T : 𝒵 × (ℕ → 𝒲) → ℝ := fun p =>
    hingeAntithetic (innerMean (gh ℓ₂) M p.1 p.2 - ∫ v, gh ℓ₂ p.1 v ∂ρ)
        (innerMean (gh ℓ₂) M p.1 (shiftSeq M p.2) - ∫ v, gh ℓ₂ p.1 v ∂ρ)
        (∫ v, gh ℓ₂ p.1 v ∂ρ - k + μ p.1) -
      hingeAntithetic (innerMean (gh ℓ₂) M p.1 p.2 - ∫ v, gh ℓ₂ p.1 v ∂ρ)
        (innerMean (gh ℓ₂) M p.1 (shiftSeq M p.2) - ∫ v, gh ℓ₂ p.1 v ∂ρ)
        (∫ v, gh ℓ₂ p.1 v ∂ρ - k) with hTdef
  set R : ℝ := (7 + 96 * m₄) / r + 3 * c_w / q with hRdef
  have hR2 : 6 * (1 + 16 * m₄) / M + 3 * (3 * c_w / (2 * q)) ^ 2 + (c_w / q) ^ 2 ≤ R ^ 2 := by
    rw [hMr, hRdef]
    have h1 : 6 * (1 + 16 * m₄) / r ^ 2 ≤ ((7 + 96 * m₄) / r) ^ 2 := by
      rw [div_pow]
      gcongr
      nlinarith
    have h2 : 3 * (3 * c_w / (2 * q)) ^ 2 + (c_w / q) ^ 2 ≤ (3 * c_w / q) ^ 2 := by
      have e1 : 3 * (3 * c_w / (2 * q)) ^ 2 + (c_w / q) ^ 2 = 31 / 4 * (c_w / q) ^ 2 := by
        field_simp
        ring
      have e2 : (3 * c_w / q) ^ 2 = 9 * (c_w / q) ^ 2 := by ring
      rw [e1, e2]
      nlinarith [sq_nonneg (c_w / q)]
    have h3 : 0 ≤ (7 + 96 * m₄) / r * (3 * c_w / q) := by positivity
    nlinarith
  have hδ : ∀ᵐ z ∂ν, |(∫ v, g z v ∂ρ - k) - (∫ v, gh ℓ₂ z v ∂ρ - k)| ≤ c_w / q :=
    (hw ℓ₂).mono fun z hz => by
      rw [show ∫ v, g z v ∂ρ - k - (∫ v, gh ℓ₂ z v ∂ρ - k) =
        -(∫ v, gh ℓ₂ z v ∂ρ - ∫ v, g z v ∂ρ) by ring, abs_neg, le_div_iff₀ hq0, mul_comm]
      exact hz
  obtain ⟨-, iT, hT2, iT1, hT1⟩ := mimc_shift_term_le ν ρ (hgh ℓ₂) (hfib ℓ₂) hμm hμ
    (k := k) (u := fun z => ∫ v, g z v ∂ρ - k) hδ hball hM (R := R) (by positivity) hR2 T
    (fun p => rfl)
  -- the fluctuation of the inner mean of `H` and its shifted copy
  set φ : 𝒵 × (ℕ → 𝒲) → 𝒵 × (ℕ → 𝒲) := fun p => (p.1, shiftSeq M p.2)
  have hφ : MeasurePreserving φ (nestedLaw ν ρ) (nestedLaw ν ρ) :=
    (MeasurePreserving.id ν).prod (measurePreserving_shiftSeq ρ M)
  set ε : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => innerMean H M p.1 p.2 - ∫ v, H p.1 v ∂ρ with hεdef
  have hεm : Measurable ε :=
    (measurable_innerMean hHm M measurable_id).sub (hμm.comp measurable_fst)
  refine ⟨ε, fun p => ε (φ p), T, hεm, hεm.comp hφ.measurable, fun p => ?_, fun p => ?_, iε,
    hφ.integrable_comp_of_integrable iε,
    integral_comp_of_measurePreserving hφ iε.aestronglyMeasurable, hH2, ?_, iT, hT2, iT1, hT1⟩
  · show |nestedDelta f (gh (ℓ₂ + 1)) (ℓ₁ + 1) p - nestedDelta f (gh ℓ₂) (ℓ₁ + 1) p| ≤ _
    rw [nestedDelta_succ_eq, nestedDelta_succ_eq,
      kink_antithetic_eq_hinge hf (∫ v, gh ℓ₂ p.1 v ∂ρ),
      kink_antithetic_eq_hinge hf (∫ v, gh ℓ₂ p.1 v ∂ρ), ← mul_sub, abs_mul]
    have h := (mimc_hinge_le (∫ v, gh ℓ₂ p.1 v ∂ρ) k (μ p.1) (innerMean (gh ℓ₂) M p.1 p.2)
      (innerMean (gh ℓ₂) M p.1 (shiftSeq M p.2)) (innerMean (gh (ℓ₂ + 1)) M p.1 p.2)
      (innerMean (gh (ℓ₂ + 1)) M p.1 (shiftSeq M p.2))).1
    rw [innerMean_sub, innerMean_sub] at h
    exact mul_le_mul_of_nonneg_left h (abs_nonneg c)
  · show (nestedDelta f (gh (ℓ₂ + 1)) (ℓ₁ + 1) p - nestedDelta f (gh ℓ₂) (ℓ₁ + 1) p) ^ 2 ≤ _
    rw [nestedDelta_succ_eq, nestedDelta_succ_eq,
      kink_antithetic_eq_hinge hf (∫ v, gh ℓ₂ p.1 v ∂ρ),
      kink_antithetic_eq_hinge hf (∫ v, gh ℓ₂ p.1 v ∂ρ), ← mul_sub, mul_pow]
    have h := (mimc_hinge_le (∫ v, gh ℓ₂ p.1 v ∂ρ) k (μ p.1) (innerMean (gh ℓ₂) M p.1 p.2)
      (innerMean (gh ℓ₂) M p.1 (shiftSeq M p.2)) (innerMean (gh (ℓ₂ + 1)) M p.1 p.2)
      (innerMean (gh (ℓ₂ + 1)) M p.1 (shiftSeq M p.2))).2
    rw [innerMean_sub, innerMean_sub] at h
    calc _ ≤ c ^ 2 * (4 * ε p ^ 2 + 4 * ε (φ p) ^ 2 + 2 * T p ^ 2) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg c)
      _ = _ := by ring
  · have e : (2 : ℝ) ^ ℓ₁ = M := by rw [hMdef]; push_cast; ring
    rw [e]
    exact hε

end Product

/-! ### §9.2: the corrected rates -/

section Rates

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **The corrected MIMC variance rate for a piecewise linear `f`: `V_ℓ = O(2^{−ℓ₁−ℓ₂})`**
(Giles 2015, §9.2, p. 60: "if the function `f` is continuous and piecewise differentiable,
rather than being twice differentiable, then in the MLMC treatment we would get `β = 1.5` … On
the other hand, with MIMC we would have `β₁ = β₂ = 1.5`"; the MIMC claim is false,
`nested_mimc_kink_rates_false`).  Let `f(x) = a₀ + a₁x + c max(x − k, 0)` and let
`Y_{(ℓ₁+1, ℓ₂+1)}` be the six-term MIMC correction of p. 59 (`nestedMimcDelta`: `2^{ℓ₁+1}` inner
samples split into two halves, with the inner approximations `g_{ℓ₂+1}` and `g_{ℓ₂}`).
Hypotheses (this formalisation's; the paper states none for this case), those of
`nested_kink_sde_variance_rate`, but with strong order `½` in `L²` instead of `¼`: centred
conditional fourth moments `E_W[(g_ℓ(z, W) − E_W[g_ℓ(z, W)])⁴] ≤ m₄`; first order weak
convergence uniformly in the outer sample, `2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w`; the small
ball `ν{|E_W[g(Z, W)] − k| ≤ t} ≤ c_d t` for the exact conditional mean; and strong convergence of
order `½` in `L²`, `2^ℓ E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))²] ≤ cₛ` (`nested_kink_sde_variance_rate`
assumes only `2^{ℓ/2} E[(g_{ℓ+1} − g_ℓ)²] ≤ cₛ`, with which the inner-sampling fluctuation term
would give only `O(2^{−ℓ₁−ℓ₂/2})`; Euler–Maruyama satisfies order `½`, and the paper assumes
first order).  Then `Y` is square-integrable and
`2^{ℓ₁+ℓ₂} E[Y²] ≤ 8 c_d c² (1 + 16 m₄)(1 + c_w) + c² (8 cₛ + (9/4) c_d c_w² (7 + 96 m₄ + 3 c_w))`,
so `V_ℓ ≤ E[Y_ℓ²] = O(2^{−ℓ₁−ℓ₂})`: `β₁ = β₂ = 1`, not `1.5`, and this is sharp
(`nested_mimc_kink_rate_sharp`).

Proof: the two §9.1 corrections in `Y` are each `O(2^{−3ℓ₁/4} + 2^{−(ℓ₁+ℓ₂)/2})` in `L²`
(`kink_variance_le_of_small_ball`, with the kink seen within the weak error `c_w 2^{−ℓ₂}`), so
`E[Y²] = O(2^{−3ℓ₁/2} + 2^{−ℓ₁−ℓ₂})`; and by `mimc_kink_split`
`E[Y²] = O(2^{−ℓ₁−ℓ₂} + 2^{−2ℓ₂−ℓ₁/2} + 2^{−3ℓ₂})`.  The minimum of the two is `O(2^{−ℓ₁−ℓ₂})`
(`mimc_kink_rate_combine`).  Correction: the paper's heuristic treats the kink like the smooth
case, but the weak error moves the kink between `g_{ℓ₂}` and `g_{ℓ₂+1}` by `O(2^{−ℓ₂})`, and on
the event that the coarse inner means straddle it (probability `O(2^{−ℓ₁/2})`) the antithetic
difference changes by `O(2^{−ℓ₂})`, which the antithetic construction does not damp.  Deviation:
the paper's `f` is continuous and piecewise differentiable; here `f` is piecewise linear with
one kink, as in `nested_kink_variance_rate`. -/
theorem nested_mimc_kink_variance_rate {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w c_d cₛ : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ cₛ) (ℓ₁ ℓ₂ : ℕ) :
    MemLp (nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ (ℓ₁ + ℓ₂) * ∫ p, nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        8 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w) +
          c ^ 2 * (8 * cₛ + 9 / 4 * c_d * c_w ^ 2 * (7 + 96 * m₄ + 3 * c_w)) := by
  have hcd : 0 ≤ c_d := nonneg_of_small_ball hball
  have hcw : 0 ≤ c_w := by
    obtain ⟨z, hz⟩ := (hw 0).exists
    exact le_trans (by positivity) hz
  have hm₄ : 0 ≤ m₄ := by
    obtain ⟨z, hz⟩ := (hfib 0).exists
    exact (integral_nonneg fun v => by positivity).trans hz.2
  have hcs : 0 ≤ cₛ :=
    le_trans (mul_nonneg (by positivity) (integral_nonneg fun p => sq_nonneg _)) (hs 0)
  set q : ℝ := (2 : ℝ) ^ ℓ₂ with hq
  have hq0 : 0 < q := by positivity
  obtain ⟨hr0, hr1, hr2, hr3⟩ := two_rpow_half_props ℓ₁
  set r : ℝ := (2 : ℝ) ^ ((ℓ₁ : ℝ) / 2) with hr
  set Y := nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) with hYdef
  -- (E1) the two §9.1 corrections, each `O(2^{−3ℓ₁/2} + 2^{−ℓ₁−ℓ₂})`
  have hδ : ∀ j, ∀ᵐ z ∂ν, |(∫ v, g z v ∂ρ - k) - (∫ v, gh j z v ∂ρ - k)| ≤ c_w / 2 ^ j :=
    fun j => (hw j).mono fun z hz => by
      rw [show ∫ v, g z v ∂ρ - k - (∫ v, gh j z v ∂ρ - k) =
        -(∫ v, gh j z v ∂ρ - ∫ v, g z v ∂ρ) by ring, abs_neg, le_div_iff₀ (by positivity),
        mul_comm]
      exact hz
  have hR1 : ∀ j, ℓ₂ ≤ j → 1 + 2 ^ ℓ₁ * (c_w / 2 ^ j) ^ 2 / 32 ≤ (1 + c_w * r / q) ^ 2 :=
    fun j hj => by
      have hqj : q ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
      have h1 : (c_w / 2 ^ j) ^ 2 ≤ (c_w / q) ^ 2 := by gcongr
      have h2 : (2 : ℝ) ^ ℓ₁ * (c_w / q) ^ 2 = (c_w * r / q) ^ 2 := by
        rw [← hr2]
        ring
      have h3 : 0 ≤ c_w * r / q := by positivity
      have h4 : (2 : ℝ) ^ ℓ₁ * (c_w / 2 ^ j) ^ 2 ≤ (c_w * r / q) ^ 2 := by
        rw [← h2]
        gcongr
      nlinarith
  obtain ⟨hN1, hN1le⟩ := kink_variance_le_of_small_ball ν ρ hf (hgh (ℓ₂ + 1)) (hfib (ℓ₂ + 1))
    (u := fun z => ∫ v, g z v ∂ρ - k) (hδ (ℓ₂ + 1)) hball ℓ₁ (R := 1 + c_w * r / q)
    (by positivity) (hR1 _ (by omega))
  obtain ⟨hN0, hN0le⟩ := kink_variance_le_of_small_ball ν ρ hf (hgh ℓ₂) (hfib ℓ₂)
    (u := fun z => ∫ v, g z v ∂ρ - k) (hδ ℓ₂) hball ℓ₁ (R := 1 + c_w * r / q)
    (by positivity) (hR1 _ le_rfl)
  rw [← hr3] at hN1le hN0le
  have hY : ∀ p, Y p = nestedDelta f (gh (ℓ₂ + 1)) (ℓ₁ + 1) p -
      nestedDelta f (gh ℓ₂) (ℓ₁ + 1) p := fun p => rfl
  have hYfun : Y = fun p => nestedDelta f (gh (ℓ₂ + 1)) (ℓ₁ + 1) p -
      nestedDelta f (gh ℓ₂) (ℓ₁ + 1) p := funext hY
  have hY2 : MemLp Y 2 (nestedLaw ν ρ) := by rw [hYfun]; exact hN1.sub hN0
  refine ⟨hY2, ?_⟩
  set K₁ : ℝ := 8 * c_d * c ^ 2 * (1 + 16 * m₄) with hK₁
  have hE1 : ∫ p, Y p ^ 2 ∂(nestedLaw ν ρ) ≤ K₁ * (1 / r ^ 3 + c_w / (r ^ 2 * q)) := by
    have hpt : ∀ p, Y p ^ 2 ≤ 2 * nestedDelta f (gh (ℓ₂ + 1)) (ℓ₁ + 1) p ^ 2 +
        2 * nestedDelta f (gh ℓ₂) (ℓ₁ + 1) p ^ 2 := fun p => by
      rw [hY]
      nlinarith [sq_nonneg (nestedDelta f (gh (ℓ₂ + 1)) (ℓ₁ + 1) p +
        nestedDelta f (gh ℓ₂) (ℓ₁ + 1) p)]
    have i1 := hN1.integrable_sq.const_mul 2
    have i0 := hN0.integrable_sq.const_mul 2
    have i10 : Integrable (fun p => 2 * nestedDelta f (gh (ℓ₂ + 1)) (ℓ₁ + 1) p ^ 2 +
        2 * nestedDelta f (gh ℓ₂) (ℓ₁ + 1) p ^ 2) (nestedLaw ν ρ) := i1.add i0
    have h := integral_mono hY2.integrable_sq i10 hpt
    rw [integral_add i1 i0, integral_const_mul, integral_const_mul] at h
    have hr30 : 0 < r ^ 3 := by positivity
    have b1 : ∫ p, nestedDelta f (gh (ℓ₂ + 1)) (ℓ₁ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        2 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w * r / q) / r ^ 3 := by
      rw [le_div_iff₀ hr30, mul_comm]
      exact hN1le
    have b0 : ∫ p, nestedDelta f (gh ℓ₂) (ℓ₁ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        2 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w * r / q) / r ^ 3 := by
      rw [le_div_iff₀ hr30, mul_comm]
      exact hN0le
    have e : 2 * (2 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w * r / q) / r ^ 3) +
        2 * (2 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w * r / q) / r ^ 3) =
        K₁ * (1 / r ^ 3 + c_w / (r ^ 2 * q)) := by
      rw [hK₁]
      field_simp
      ring
    linarith
  -- (E2) the inner-sampling fluctuation of `g_{ℓ₂+1} − g_{ℓ₂}` and the shift of the kink
  obtain ⟨ε, ε', T, -, -, -, hpt, iε, iε', eε', -, hε, iT, hT2, -, -⟩ :=
    mimc_kink_split ν ρ hf hgh hfib hw hball ℓ₁ ℓ₂
  rw [← hr, ← hq] at hT2
  rw [← hr2] at hε
  have j1 : Integrable (fun p => 4 * c ^ 2 * ε p ^ 2) (nestedLaw ν ρ) := iε.const_mul _
  have j2 : Integrable (fun p => 4 * c ^ 2 * ε' p ^ 2) (nestedLaw ν ρ) := iε'.const_mul _
  have j3 : Integrable (fun p => 2 * c ^ 2 * T p ^ 2) (nestedLaw ν ρ) := iT.const_mul _
  have j12 : Integrable (fun p => 4 * c ^ 2 * ε p ^ 2 + 4 * c ^ 2 * ε' p ^ 2)
      (nestedLaw ν ρ) := j1.add j2
  have j123 : Integrable (fun p => 4 * c ^ 2 * ε p ^ 2 + 4 * c ^ 2 * ε' p ^ 2 +
      2 * c ^ 2 * T p ^ 2) (nestedLaw ν ρ) := j12.add j3
  have hE2' := integral_mono hY2.integrable_sq j123 hpt
  rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
    integral_const_mul, eε'] at hE2'
  have hεle : ∫ p, ε p ^ 2 ∂(nestedLaw ν ρ) ≤ cₛ / (r ^ 2 * q) := by
    have h := hs ℓ₂
    rw [← hq] at h
    rw [le_div_iff₀ (by positivity)]
    calc (∫ p, ε p ^ 2 ∂(nestedLaw ν ρ)) * (r ^ 2 * q)
        = q * (r ^ 2 * ∫ p, ε p ^ 2 ∂(nestedLaw ν ρ)) := by ring
      _ ≤ q * ∫ p, (gh (ℓ₂ + 1) p.1 p.2 - gh ℓ₂ p.1 p.2) ^ 2 ∂(ν.prod ρ) := by gcongr
      _ ≤ cₛ := h
  -- separate the fluctuation term, then combine the two bounds
  set R : ℝ := (7 + 96 * m₄) / r + 3 * c_w / q with hRdef
  set a : ℝ := 8 * c ^ 2 * cₛ with ha
  have hE2 : ∫ p, Y p ^ 2 ∂(nestedLaw ν ρ) - a / (r ^ 2 * q) ≤
      9 / 2 * c ^ 2 * c_d * c_w ^ 2 * (7 + 96 * m₄) / (q ^ 2 * r) +
      27 / 2 * c ^ 2 * c_d * c_w ^ 3 / q ^ 3 := by
    have e : 9 / 2 * c ^ 2 * c_d * c_w ^ 2 * (7 + 96 * m₄) / (q ^ 2 * r) +
        27 / 2 * c ^ 2 * c_d * c_w ^ 3 / q ^ 3 =
        2 * c ^ 2 * (c_d * (3 * c_w / (2 * q)) ^ 2 * R) := by
      rw [hRdef]
      field_simp
      ring
    have e' : a / (r ^ 2 * q) =
        4 * c ^ 2 * (cₛ / (r ^ 2 * q)) + 4 * c ^ 2 * (cₛ / (r ^ 2 * q)) := by
      rw [ha]
      ring
    rw [e, e']
    have h4 : 4 * c ^ 2 * ∫ p, ε p ^ 2 ∂(nestedLaw ν ρ) ≤ 4 * c ^ 2 * (cₛ / (r ^ 2 * q)) := by
      gcongr
    have h5 : 2 * c ^ 2 * ∫ p, T p ^ 2 ∂(nestedLaw ν ρ) ≤
        2 * c ^ 2 * (c_d * (3 * c_w / (2 * q)) ^ 2 * R) := by gcongr
    linarith
  have hE1' : ∫ p, Y p ^ 2 ∂(nestedLaw ν ρ) - a / (r ^ 2 * q) ≤
      K₁ * (1 / r ^ 3 + c_w / (r ^ 2 * q)) := by
    have : 0 ≤ a / (r ^ 2 * q) := by positivity
    linarith
  have hcomb := mimc_kink_rate_combine hr1 hq0 (by positivity : (0 : ℝ) ≤ K₁)
    (by positivity : (0 : ℝ) ≤ 9 / 2 * c ^ 2 * c_d * c_w ^ 2 * (7 + 96 * m₄))
    (by positivity : (0 : ℝ) ≤ 27 / 2 * c ^ 2 * c_d * c_w ^ 3) hcw hE1' hE2
  have e2 : (2 : ℝ) ^ (ℓ₁ + ℓ₂) = r ^ 2 * q := by rw [pow_add, hr2]
  have e3 : r ^ 2 * q * (a / (r ^ 2 * q)) = a := by field_simp
  rw [e2]
  have : r ^ 2 * q * ∫ p, Y p ^ 2 ∂(nestedLaw ν ρ) ≤ a + (K₁ * (1 + c_w) +
      (9 / 2 * c ^ 2 * c_d * c_w ^ 2 * (7 + 96 * m₄) + 27 / 2 * c ^ 2 * c_d * c_w ^ 3) / 2) := by
    have := hcomb
    rw [mul_sub, e3] at this
    linarith
  refine this.trans_eq ?_
  rw [hK₁, ha]
  ring

/-- **The MIMC mean rate for a piecewise linear `f`: `|E[Y_ℓ]| = O(2^{−ℓ₁/2−ℓ₂})`** (Giles 2015,
§9.2, p. 60: for a twice differentiable `f`, "`E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})`"; for a piecewise
differentiable `f` the paper states no mean rate).  Under the hypotheses of
`nested_mimc_kink_variance_rate`, but with first order strong convergence in `L²`,
`4^ℓ E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))²] ≤ cₛ` (the paper's "first order strong convergence"),
`Y_{(ℓ₁+1, ℓ₂+1)}` is square-integrable (`nested_mimc_kink_variance_rate`) and
`2^{ℓ₁/2+ℓ₂} |E[Y_{(ℓ₁+1, ℓ₂+1)}]| ≤ C_E` with
`C_E = 12 c_d |c| (1 + 80 m₄)(1 + c_w) + |c| (1 + cₛ + 3 c_d c_w (7 + 96 m₄ + 3 c_w))`, i.e.
`α₁ = ½`, `α₂ = 1`, which is enough for Theorem 2 (`α_d ≥ β_d/2`).  Proof: `E[Y]` is the
difference of the bias increments `E[P_{ℓ₁+1}] − E[P_{ℓ₁}]` for `g_{ℓ₂+1}` and `g_{ℓ₂}`, each
`O(2^{−ℓ₁} + 2^{−ℓ₁/2−ℓ₂})` (`kink_bias_le_of_small_ball`), and
`|E[Y]| ≤ E|Y| = O(2^{−ℓ₁/2−ℓ₂} + 2^{−2ℓ₂})` (`mimc_kink_split`); the minimum is
`O(2^{−ℓ₁/2−ℓ₂})`.  The smooth-case rate `O(2^{−ℓ₁−ℓ₂})` is not claimed, and it fails under
these hypotheses when the weak error depends on the outer sample: for
`g_ℓ = g + clamp(½ − Z, −2^{−ℓ}/8, 2^{−ℓ}/8)` (otherwise as `kinkInnerApprox`), which puts
`E_W[g_ℓ(Z, W)]` on the kink with probability `2^{−ℓ}/4`, a numerical evaluation gives
`2^{ℓ₁/2+ℓ₂} E[Y] → 1.8 · 10⁻³` (not formalised).  For the example `kinkInnerApprox` itself
`E[Y_ℓ] = 0` (`nested_mimc_kink_rate_sharp`). -/
theorem nested_mimc_kink_mean_rate {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w c_d cₛ : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (hs : ∀ ℓ : ℕ, ((2 : ℝ) ^ ℓ) ^ 2 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ cₛ) (ℓ₁ ℓ₂ : ℕ) :
    MemLp (nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((ℓ₁ : ℝ) / 2 + ℓ₂) *
          |∫ p, nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) p ∂(nestedLaw ν ρ)| ≤
        12 * c_d * |c| * (1 + 80 * m₄) * (1 + c_w) +
          |c| * (1 + cₛ + 3 * c_d * c_w * (7 + 96 * m₄ + 3 * c_w)) := by
  have hcd : 0 ≤ c_d := nonneg_of_small_ball hball
  have hcw : 0 ≤ c_w := by
    obtain ⟨z, hz⟩ := (hw 0).exists
    exact le_trans (by positivity) hz
  have hm₄ : 0 ≤ m₄ := by
    obtain ⟨z, hz⟩ := (hfib 0).exists
    exact (integral_nonneg fun v => by positivity).trans hz.2
  have hcs : 0 ≤ cₛ :=
    le_trans (mul_nonneg (by positivity) (integral_nonneg fun p => sq_nonneg _)) (hs 0)
  have hs' : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ cₛ := fun ℓ => by
    have h1 : (2 : ℝ) ^ ℓ ≤ ((2 : ℝ) ^ ℓ) ^ 2 := by
      have : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
      nlinarith
    have h0 : 0 ≤ ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) :=
      integral_nonneg fun p => sq_nonneg _
    exact (mul_le_mul_of_nonneg_right h1 h0).trans (hs ℓ)
  set q : ℝ := (2 : ℝ) ^ ℓ₂ with hq
  have hq0 : 0 < q := by positivity
  obtain ⟨hr0, hr1, hr2, -⟩ := two_rpow_half_props ℓ₁
  set r : ℝ := (2 : ℝ) ^ ((ℓ₁ : ℝ) / 2) with hr
  set Y := nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) with hYdef
  have hY2 : MemLp Y 2 (nestedLaw ν ρ) :=
    (nested_mimc_kink_variance_rate ν ρ hf hgh hfib hw hball hs' ℓ₁ ℓ₂).1
  have hY1 : Integrable Y (nestedLaw ν ρ) := hY2.integrable one_le_two
  refine ⟨hY2, ?_⟩
  have erq : (2 : ℝ) ^ ((ℓ₁ : ℝ) / 2 + ℓ₂) = r * q := by
    rw [Real.rpow_add two_pos, Real.rpow_natCast]
  rw [erq]
  -- (M1) the bias route: `E[N_j]` is a difference of two biases, each `O(2^{−ℓ₁})`
  have hδ : ∀ j, ∀ᵐ z ∂ν, |(∫ v, g z v ∂ρ - k) - (∫ v, gh j z v ∂ρ - k)| ≤ c_w / 2 ^ j :=
    fun j => (hw j).mono fun z hz => by
      rw [show ∫ v, g z v ∂ρ - k - (∫ v, gh j z v ∂ρ - k) =
        -(∫ v, gh j z v ∂ρ - ∫ v, g z v ∂ρ) by ring, abs_neg, le_div_iff₀ (by positivity),
        mul_comm]
      exact hz
  set φ : 𝒵 × (ℕ → 𝒲) → 𝒵 × (ℕ → 𝒲) := fun p => (p.1, shiftSeq (2 ^ ℓ₁) p.2)
  have hφ : MeasurePreserving φ (nestedLaw ν ρ) (nestedLaw ν ρ) :=
    (MeasurePreserving.id ν).prod (measurePreserving_shiftSeq ρ _)
  have hM1 : ∀ j, ℓ₂ ≤ j → Integrable (nestedDelta f (gh j) (ℓ₁ + 1)) (nestedLaw ν ρ) ∧
      |∫ p, nestedDelta f (gh j) (ℓ₁ + 1) p ∂(nestedLaw ν ρ)| ≤
        6 * c_d * |c| * (1 + 80 * m₄) * (1 / r ^ 2 + c_w / (r * q)) := fun j hj => by
    have hqj : q ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
    have hx : (c_w / 2 ^ j) ^ 2 ≤ (c_w / q) ^ 2 := by gcongr
    have hx0 : 0 ≤ c_w * r / q := by positivity
    have e : (2 : ℝ) ^ ℓ₁ * (c_w / q) ^ 2 = (c_w * r / q) ^ 2 := by rw [← hr2]; ring
    have hRa : 2 * (1 + 2 ^ (ℓ₁ + 1) * (c_w / 2 ^ j) ^ 2) ≤ (2 * (1 + c_w * r / q)) ^ 2 := by
      have : (2 : ℝ) ^ (ℓ₁ + 1) * (c_w / 2 ^ j) ^ 2 ≤ 2 * (c_w * r / q) ^ 2 := by
        rw [← e, pow_succ]
        have : (0 : ℝ) ≤ 2 ^ ℓ₁ * 2 := by positivity
        nlinarith
      nlinarith
    have hRb : 2 * (1 + 2 ^ ℓ₁ * (c_w / 2 ^ j) ^ 2) ≤ (2 * (1 + c_w * r / q)) ^ 2 := by
      have : (2 : ℝ) ^ ℓ₁ * (c_w / 2 ^ j) ^ 2 ≤ (c_w * r / q) ^ 2 := by
        rw [← e]
        gcongr
      nlinarith
    obtain ⟨iD1, hD1⟩ := kink_bias_le_of_small_ball ν ρ hf (hgh j) (hfib j)
      (u := fun z => ∫ v, g z v ∂ρ - k) (hδ j) hball (ℓ₁ + 1) (by positivity) hRa
    obtain ⟨iD0, hD0⟩ := kink_bias_le_of_small_ball ν ρ hf (hgh j) (hfib j)
      (u := fun z => ∫ v, g z v ∂ρ - k) (hδ j) hball ℓ₁ (by positivity) hRb
    set D : ℕ → 𝒵 × (ℕ → 𝒲) → ℝ := fun ℓ p => nestedP f (gh j) ℓ p - nestedTarget f (gh j) ρ p
      with hD
    have iD0φ : Integrable (fun p => D ℓ₁ (φ p)) (nestedLaw ν ρ) :=
      hφ.integrable_comp_of_integrable iD0
    have eφ : ∫ p, D ℓ₁ (φ p) ∂(nestedLaw ν ρ) = ∫ p, D ℓ₁ p ∂(nestedLaw ν ρ) :=
      integral_comp_of_measurePreserving hφ iD0.aestronglyMeasurable
    have hpt : ∀ p, nestedDelta f (gh j) (ℓ₁ + 1) p =
        D (ℓ₁ + 1) p - D ℓ₁ p / 2 - D ℓ₁ (φ p) / 2 := fun p => by
      simp only [hD, nestedDelta, nestedP, nestedTarget, φ]
      ring
    have i1 : Integrable (fun p => D (ℓ₁ + 1) p - D ℓ₁ p / 2) (nestedLaw ν ρ) :=
      iD1.sub (iD0.div_const 2)
    have i2 : Integrable (fun p => D ℓ₁ (φ p) / 2) (nestedLaw ν ρ) := iD0φ.div_const 2
    have hN : nestedDelta f (gh j) (ℓ₁ + 1) = fun p => D (ℓ₁ + 1) p - D ℓ₁ p / 2 - D ℓ₁ (φ p) / 2 :=
      funext hpt
    refine ⟨by rw [hN]; exact i1.sub i2, ?_⟩
    rw [hN, integral_sub i1 i2, integral_sub iD1 (iD0.div_const 2), integral_div, integral_div,
      eφ]
    have e2 : (2 : ℝ) ^ (ℓ₁ + 1) = 2 * r ^ 2 := by rw [pow_succ, hr2]; ring
    rw [e2] at hD1
    rw [← hr2] at hD0
    have b1 : |∫ p, D (ℓ₁ + 1) p ∂(nestedLaw ν ρ)| ≤
        2 * c_d * |c| * (1 + 80 * m₄) * (2 * (1 + c_w * r / q)) / (2 * r ^ 2) := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hD1
    have b0 : |∫ p, D ℓ₁ p ∂(nestedLaw ν ρ)| ≤
        2 * c_d * |c| * (1 + 80 * m₄) * (2 * (1 + c_w * r / q)) / r ^ 2 := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hD0
    have e3 : 2 * c_d * |c| * (1 + 80 * m₄) * (2 * (1 + c_w * r / q)) / (2 * r ^ 2) +
        2 * c_d * |c| * (1 + 80 * m₄) * (2 * (1 + c_w * r / q)) / r ^ 2 =
        6 * c_d * |c| * (1 + 80 * m₄) * (1 / r ^ 2 + c_w / (r * q)) := by
      field_simp
      ring
    calc |∫ p, D (ℓ₁ + 1) p ∂(nestedLaw ν ρ) - (∫ p, D ℓ₁ p ∂(nestedLaw ν ρ)) / 2 -
          (∫ p, D ℓ₁ p ∂(nestedLaw ν ρ)) / 2|
        = |∫ p, D (ℓ₁ + 1) p ∂(nestedLaw ν ρ) - ∫ p, D ℓ₁ p ∂(nestedLaw ν ρ)| := by ring_nf
      _ ≤ |∫ p, D (ℓ₁ + 1) p ∂(nestedLaw ν ρ)| + |∫ p, D ℓ₁ p ∂(nestedLaw ν ρ)| := abs_sub _ _
      _ ≤ _ := by rw [← e3]; exact add_le_add b1 b0
  obtain ⟨iN1, bN1⟩ := hM1 (ℓ₂ + 1) (by omega)
  obtain ⟨iN0, bN0⟩ := hM1 ℓ₂ le_rfl
  have hB1 : |∫ p, Y p ∂(nestedLaw ν ρ)| ≤
      12 * c_d * |c| * (1 + 80 * m₄) * (1 / r ^ 2 + c_w / (r * q)) := by
    have e : ∫ p, Y p ∂(nestedLaw ν ρ) = ∫ p, nestedDelta f (gh (ℓ₂ + 1)) (ℓ₁ + 1) p
        ∂(nestedLaw ν ρ) - ∫ p, nestedDelta f (gh ℓ₂) (ℓ₁ + 1) p ∂(nestedLaw ν ρ) :=
      integral_sub iN1 iN0
    rw [e]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ _ := add_le_add bN1 bN0
      _ = _ := by ring
  -- (M2) the `L¹` route through the decomposition of `mimc_kink_split`
  obtain ⟨ε, ε', T, hεm, hε'm, habs, -, iε, iε', eε', -, hε, -, -, iT1, hT1⟩ :=
    mimc_kink_split ν ρ hf hgh hfib hw hball ℓ₁ ℓ₂
  rw [← hr, ← hq] at hT1
  rw [← hr2] at hε
  have hεle : ∫ p, ε p ^ 2 ∂(nestedLaw ν ρ) ≤ cₛ / (r * q) ^ 2 := by
    have h := hs ℓ₂
    rw [← hq] at h
    rw [le_div_iff₀ (by positivity)]
    calc (∫ p, ε p ^ 2 ∂(nestedLaw ν ρ)) * (r * q) ^ 2
        = q ^ 2 * (r ^ 2 * ∫ p, ε p ^ 2 ∂(nestedLaw ν ρ)) := by ring
      _ ≤ q ^ 2 * ∫ p, (gh (ℓ₂ + 1) p.1 p.2 - gh ℓ₂ p.1 p.2) ^ 2 ∂(ν.prod ρ) := by gcongr
      _ ≤ cₛ := h
  set s : ℝ := r * q with hsdef
  have hs0 : 0 < s := by positivity
  have hamgm : ∀ y : ℝ, |y| ≤ (s * y ^ 2 + 1 / s) / 2 := fun y => by
    have e : (s * y ^ 2 + 1 / s) / 2 - |y| = (s * |y| - 1) ^ 2 / (2 * s) := by
      rw [← sq_abs y]
      field_simp
      ring
    have : 0 ≤ (s * |y| - 1) ^ 2 / (2 * s) := by positivity
    linarith
  have hL1 : ∀ (X : 𝒵 × (ℕ → 𝒲) → ℝ), Measurable X → Integrable (fun p => X p ^ 2) (nestedLaw ν ρ) →
      ∫ p, X p ^ 2 ∂(nestedLaw ν ρ) ≤ cₛ / s ^ 2 →
      Integrable (fun p => |X p|) (nestedLaw ν ρ) ∧
        ∫ p, |X p| ∂(nestedLaw ν ρ) ≤ (cₛ + 1) / (2 * s) := fun X hXm hX2 hXle => by
    have hX : MemLp X 2 (nestedLaw ν ρ) :=
      (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).2 hX2
    have i1 : Integrable (fun p => |X p|) (nestedLaw ν ρ) := (hX.integrable one_le_two).abs
    have i2 : Integrable (fun p => (s * X p ^ 2 + 1 / s) / 2) (nestedLaw ν ρ) :=
      ((hX2.const_mul s).add (integrable_const _)).div_const 2
    refine ⟨i1, (integral_mono i1 i2 fun p => hamgm _).trans ?_⟩
    rw [integral_div, integral_add (hX2.const_mul s) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    have : s * ∫ p, X p ^ 2 ∂(nestedLaw ν ρ) ≤ cₛ / s := by
      calc s * ∫ p, X p ^ 2 ∂(nestedLaw ν ρ) ≤ s * (cₛ / s ^ 2) := by gcongr
        _ = cₛ / s := by field_simp
    calc (s * ∫ p, X p ^ 2 ∂(nestedLaw ν ρ) + 1 / s) / 2 ≤ (cₛ / s + 1 / s) / 2 := by gcongr
      _ = (cₛ + 1) / (2 * s) := by field_simp
  obtain ⟨j1, b1⟩ := hL1 ε hεm iε hεle
  obtain ⟨j2, b2⟩ := hL1 ε' hε'm iε' (by rw [eε']; exact hεle)
  have hB2 : |∫ p, Y p ∂(nestedLaw ν ρ)| ≤
      |c| * ((cₛ + 1) / s + 2 * c_d * (3 * c_w / (2 * q)) * ((7 + 96 * m₄) / r + 3 * c_w / q)) := by
    have j12 : Integrable (fun p => |ε p| + |ε' p|) (nestedLaw ν ρ) := j1.add j2
    have j123 : Integrable (fun p => |ε p| + |ε' p| + |T p|) (nestedLaw ν ρ) := j12.add iT1
    have hmono := integral_mono hY1.abs (j123.const_mul |c|) habs
    rw [integral_const_mul, integral_add j12 iT1, integral_add j1 j2] at hmono
    calc |∫ p, Y p ∂(nestedLaw ν ρ)| ≤ ∫ p, |Y p| ∂(nestedLaw ν ρ) :=
          abs_integral_le_integral_abs
      _ ≤ _ := hmono
      _ ≤ |c| * ((cₛ + 1) / (2 * s) + (cₛ + 1) / (2 * s) +
          2 * c_d * (3 * c_w / (2 * q)) * ((7 + 96 * m₄) / r + 3 * c_w / q)) := by gcongr
      _ = _ := by ring
  -- combine the two routes
  have hK1 : 0 ≤ 12 * c_d * |c| * (1 + 80 * m₄) * (1 + c_w) := by positivity
  have hK2 : 0 ≤ |c| * (1 + cₛ + 3 * c_d * c_w * (7 + 96 * m₄ + 3 * c_w)) := by positivity
  rcases le_or_gt q r with hqr | hrq
  · have : r * q * |∫ p, Y p ∂(nestedLaw ν ρ)| ≤ 12 * c_d * |c| * (1 + 80 * m₄) * (1 + c_w) := by
      have hqr1 : q / r ≤ 1 := (div_le_one hr0).2 hqr
      calc r * q * |∫ p, Y p ∂(nestedLaw ν ρ)|
          ≤ r * q * (12 * c_d * |c| * (1 + 80 * m₄) * (1 / r ^ 2 + c_w / (r * q))) := by
            gcongr
        _ = 12 * c_d * |c| * (1 + 80 * m₄) * (q / r + c_w) := by field_simp
        _ ≤ 12 * c_d * |c| * (1 + 80 * m₄) * (1 + c_w) := by gcongr
    linarith
  · have : r * q * |∫ p, Y p ∂(nestedLaw ν ρ)| ≤
        |c| * (1 + cₛ + 3 * c_d * c_w * (7 + 96 * m₄ + 3 * c_w)) := by
      have hrq1 : r / q ≤ 1 := (div_le_one hq0).2 hrq.le
      calc r * q * |∫ p, Y p ∂(nestedLaw ν ρ)|
          ≤ r * q * (|c| * ((cₛ + 1) / s + 2 * c_d * (3 * c_w / (2 * q)) *
            ((7 + 96 * m₄) / r + 3 * c_w / q))) := by gcongr
        _ = |c| * (1 + cₛ + 3 * c_d * c_w * (7 + 96 * m₄) + 9 * c_d * c_w ^ 2 * (r / q)) := by
            rw [hsdef]
            field_simp
            ring
        _ ≤ |c| * (1 + cₛ + 3 * c_d * c_w * (7 + 96 * m₄) + 9 * c_d * c_w ^ 2 * 1) := by
            gcongr
        _ = |c| * (1 + cₛ + 3 * c_d * c_w * (7 + 96 * m₄ + 3 * c_w)) := by ring
    linarith

end Rates

/-! ### Sharpness: the example of `NestedKinkSde.lean` -/

/-- **The corrected rate is sharp** (Giles 2015, §9.2, p. 60: "with MIMC we would have
`β₁ = β₂ = 1.5`").  For the example of `MlmcLean/NestedKinkSde.lean` (`kinkInnerApprox`:
`f(x) = max(x − ½, 0)`, `Z` uniform on `[0, 1]`, fair inner signs, `g_ℓ = g + 2^{−ℓ}/8`), which
satisfies the hypotheses of `nested_mimc_kink_variance_rate` with `c = 1`, `c_d = 2`,
`m₄ = 1/4096`, `c_w = 1/8`, `cₛ = 1/256` (`kinkInnerApprox_hypotheses`): every MIMC correction
`Y_{(ℓ₁+1, ℓ₂+1)}` is square-integrable, has mean zero (`integral_kinkMimc`) and
`2^{ℓ₁+ℓ₂} V[Y] ≤ 19`; along `ℓ₁ = 2j`, `ℓ₂ = j + 1`, `2^{ℓ₁+ℓ₂} V[Y] ≥ 2^{−18}`
(`kinkMimc_variance_ge`); and for no `β > 1` is `V[Y] ≤ C 2^{−β(ℓ₁+ℓ₂)}`
(`nested_mimc_kink_rates_false`).  So `V ≍ 2^{−ℓ₁−ℓ₂}` along this ray, and
`(β₁, β₂) = (1, 1)` lies on the boundary `2β₁ + β₂ = 3` of the rates that
`nested_mimc_kink_rates_false` excludes.  The sharpness is along this ray, for isotropic or
product-form rates `2^{−β₁ℓ₁−β₂ℓ₂}`: away from the direction `ℓ₁ = 2ℓ₂` the example's variance
is much smaller.  Numerically (from the exact law of the inner means; not formalised)
`V[Y_{(ℓ₁+1, ℓ₂+1)}] ≍ min(2^{−3ℓ₁/2}, 2^{−2ℓ₂−ℓ₁/2})` and `2^{ℓ₁+ℓ₂} V[Y] ≤ 1.1 · 10⁻⁴`, so
every `(β₁, β₂)` with `2β₁ + β₂ = 3` and `½ ≤ β₁ ≤ 3/2` holds for it, e.g. `(3/2, 0)` or
`(½, 2)`.  Among these, `(1, 1)` is singled out by Theorem 2, which needs `β_d ≥ γ_d = 1`,
together with the general `nested_mimc_kink_variance_rate`, not by the example. -/
theorem nested_mimc_kink_rate_sharp :
    (∀ ℓ₁ ℓ₂ : ℕ, MemLp (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1)
        (ℓ₂ + 1)) 2 (nestedLaw kinkOuter kinkCoin) ∧
      ∫ p, nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1)
        (ℓ₂ + 1) p ∂(nestedLaw kinkOuter kinkCoin) = 0 ∧
      (2 : ℝ) ^ (ℓ₁ + ℓ₂) * variance (nestedMimcDelta (fun x => max (x - 1 / 2) 0)
        kinkInnerApprox (ℓ₁ + 1) (ℓ₂ + 1)) (nestedLaw kinkOuter kinkCoin) ≤ 19) ∧
      (∀ j : ℕ, ((2 : ℝ) ^ 18)⁻¹ ≤ (2 : ℝ) ^ (2 * j + (j + 1)) *
        variance (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (2 * j + 1)
          (j + 1 + 1)) (nestedLaw kinkOuter kinkCoin)) ∧
      (∀ β : ℝ, 1 < β → ¬ ∃ C : ℝ, ∀ ℓ₁ ℓ₂ : ℕ,
        variance (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1) (ℓ₂ + 1))
          (nestedLaw kinkOuter kinkCoin) ≤ C * (2 : ℝ) ^ (-(β * ℓ₁ + β * ℓ₂))) := by
  have := isProbabilityMeasure_kinkOuter
  obtain ⟨hm, hmom, -, hweak, hball, hstrong⟩ := kinkInnerApprox_hypotheses
  have hf : ∀ x : ℝ, max (x - 1 / 2) 0 = 0 + 0 * x + 1 * max (x - 1 / 2) 0 := fun x => by ring
  have hfib : ∀ ℓ, ∀ᵐ z ∂kinkOuter, Integrable (fun v => kinkInnerApprox ℓ z v ^ 4) kinkCoin ∧
      ∫ v, (kinkInnerApprox ℓ z v - ∫ u, kinkInnerApprox ℓ z u ∂kinkCoin) ^ 4 ∂kinkCoin ≤
        1 / 4096 :=
    fun ℓ => Eventually.of_forall fun z => ⟨(hmom ℓ z).1, (hmom ℓ z).2.le⟩
  have hw : ∀ ℓ, ∀ᵐ z ∂kinkOuter, (2 : ℝ) ^ ℓ *
      |∫ v, kinkInnerApprox ℓ z v ∂kinkCoin - ∫ v, kinkInner z v ∂kinkCoin| ≤ 1 / 8 :=
    fun ℓ => Eventually.of_forall fun z => (hweak ℓ z).le
  have hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ * ∫ p, (kinkInnerApprox (ℓ + 1) p.1 p.2 -
      kinkInnerApprox ℓ p.1 p.2) ^ 2 ∂(kinkOuter.prod kinkCoin) ≤ 1 / 256 := fun ℓ => by
    simp_rw [hstrong]
    rw [integral_const, probReal_univ, one_smul]
    have h2 : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    calc (2 : ℝ) ^ ℓ * (-(((2 : ℝ) ^ ℓ)⁻¹ / 16)) ^ 2 = ((2 : ℝ) ^ ℓ)⁻¹ / 256 := by
          field_simp
          ring
      _ ≤ 1 / 256 := by
          gcongr
          exact inv_le_one_of_one_le₀ h2
  refine ⟨fun ℓ₁ ℓ₂ => ?_, fun j => ?_, fun β hβ => nested_mimc_kink_rates_false (by linarith)⟩
  · obtain ⟨hY2, hV⟩ := nested_mimc_kink_variance_rate kinkOuter kinkCoin hf hm hfib hw hball hs
      ℓ₁ ℓ₂
    refine ⟨hY2, integral_kinkMimc ℓ₁ ℓ₂, ?_⟩
    have hv : variance (nestedMimcDelta (fun x => max (x - 1 / 2) 0) kinkInnerApprox (ℓ₁ + 1)
        (ℓ₂ + 1)) (nestedLaw kinkOuter kinkCoin) ≤ ∫ p, nestedMimcDelta (fun x => max (x - 1 / 2) 0)
          kinkInnerApprox (ℓ₁ + 1) (ℓ₂ + 1) p ^ 2 ∂(nestedLaw kinkOuter kinkCoin) := by
      simpa only [Pi.pow_apply] using variance_le_expectation_sq hY2.aestronglyMeasurable
    calc _ ≤ (2 : ℝ) ^ (ℓ₁ + ℓ₂) * ∫ p, nestedMimcDelta (fun x => max (x - 1 / 2) 0)
          kinkInnerApprox (ℓ₁ + 1) (ℓ₂ + 1) p ^ 2 ∂(nestedLaw kinkOuter kinkCoin) := by gcongr
      _ ≤ _ := hV
      _ ≤ 19 := by norm_num
  · have h1 := (kinkMimc_variance_ge (j := j) (ℓ₂ := j + 1) le_rfl).2
    have e : (2 : ℝ) ^ (2 * (j + 1) + j + 17) = 2 ^ (2 * j + (j + 1)) * 2 ^ 18 := by
      rw [← pow_add]
      congr 1
      ring
    rw [e, mul_inv] at h1
    have hp : (0 : ℝ) < 2 ^ (2 * j + (j + 1)) := by positivity
    calc ((2 : ℝ) ^ 18)⁻¹ = 2 ^ (2 * j + (j + 1)) * ((2 ^ (2 * j + (j + 1)))⁻¹ * (2 ^ 18)⁻¹) := by
          field_simp
      _ ≤ _ := by gcongr

/-! ### The cost: Theorem 2 with `β = γ` -/

section Complexity

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **The bias of `P_{(ℓ₁,ℓ₂)}`** (Giles 2015, §9.2: `2^{ℓ₁}` inner samples of `g_{ℓ₂}`).  Under
the centred conditional fourth moments, the weak error and the small ball of
`nested_mimc_kink_variance_rate`, `P_{(ℓ₁,ℓ₂)} − f(E_W[g(Z, W)])` is integrable and
`|E[P_{(ℓ₁,ℓ₂)} − f(E_W[g(Z, W)])]|` is at most
`4 c_d |c| (1 + 80 m₄)(1 + c_w) 2^{−ℓ₁/2} + (|a₁| + |c|) c_w 2^{−ℓ₂}`: the inner sampling error
by `kink_bias_le_of_small_ball`, the discretisation error because `f` is Lipschitz.  It tends to
`0` as `min(ℓ₁, ℓ₂) → ∞`. -/
lemma nested_mimc_kink_bias {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    {g : 𝒵 → 𝒲 → ℝ} {c_w c_d : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (ℓ₁ ℓ₂ : ℕ) :
    Integrable (fun p => nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f g ρ p) (nestedLaw ν ρ) ∧
      |∫ p, (nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
        4 * c_d * |c| * (1 + 80 * m₄) * (1 + c_w) / 2 ^ ((ℓ₁ : ℝ) / 2) +
          (|a₁| + |c|) * c_w / 2 ^ ℓ₂ := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  have hcd : 0 ≤ c_d := nonneg_of_small_ball hball
  have hcw : 0 ≤ c_w := by
    obtain ⟨z, hz⟩ := (hw 0).exists
    exact le_trans (by positivity) hz
  have hm₄ : 0 ≤ m₄ := by
    obtain ⟨z, hz⟩ := (hfib 0).exists
    exact (integral_nonneg fun v => by positivity).trans hz.2
  set q : ℝ := (2 : ℝ) ^ ℓ₂ with hq
  have hq0 : 0 < q := by positivity
  have hq1 : 1 ≤ q := one_le_pow₀ (by norm_num)
  obtain ⟨hr0, hr1, hr2, -⟩ := two_rpow_half_props ℓ₁
  set r : ℝ := (2 : ℝ) ^ ((ℓ₁ : ℝ) / 2) with hr
  -- the weak error, `|E_W[g_{ℓ₂}(z, W)] − E_W[g(z, W)]| ≤ c_w / q`
  have hwl : ∀ᵐ z ∂ν, |∫ v, gh ℓ₂ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w / q :=
    (hw ℓ₂).mono fun z hz => by
      rw [le_div_iff₀ hq0, mul_comm]
      exact hz
  -- the inner sampling error of `g_{ℓ₂}` with `2^{ℓ₁}` inner samples
  have hR2 : 2 * (1 + 2 ^ ℓ₁ * (c_w / q) ^ 2) ≤ (2 * (1 + c_w * r / q)) ^ 2 := by
    have e : (2 : ℝ) ^ ℓ₁ * (c_w / q) ^ 2 = (c_w * r / q) ^ 2 := by rw [← hr2]; ring
    have h0 : 0 ≤ c_w * r / q := by positivity
    rw [e]
    nlinarith
  obtain ⟨i1, hb1⟩ := kink_bias_le_of_small_ball ν ρ hf (hgh ℓ₂) (hfib ℓ₂)
    (u := fun z => ∫ v, g z v ∂ρ - k) (δ := c_w / q)
    (hwl.mono fun z hz => by
      rw [show ∫ v, g z v ∂ρ - k - (∫ v, gh ℓ₂ z v ∂ρ - k) =
        -(∫ v, gh ℓ₂ z v ∂ρ - ∫ v, g z v ∂ρ) by ring, abs_neg]
      exact hz) hball ℓ₁ (R := 2 * (1 + c_w * r / q)) (by positivity) hR2
  -- the discretisation error
  have hGlm : Measurable fun z => ∫ v, gh ℓ₂ z v ∂ρ :=
    ((hgh ℓ₂).stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  have hGm : AEMeasurable (fun z => ∫ v, g z v ∂ρ) ν := aemeasurable_condMean_of_weak ν ρ hgh hw
  have hpt : ∀ᵐ z ∂ν, |f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)| ≤ (|a₁| + |c|) * (c_w / q) :=
    hwl.mono fun z hz => (abs_kink_sub_le hf _ _).trans (by gcongr)
  have hD : Integrable (fun z => f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ν :=
    (integrable_const ((|a₁| + |c|) * (c_w / q))).mono'
      ((hfm.comp hGlm).aemeasurable.sub (hfm.comp_aemeasurable hGm)).aestronglyMeasurable
      (hpt.mono fun z hz => by rw [Real.norm_eq_abs]; exact hz)
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have i2 : Integrable (fun p => nestedTarget f (gh ℓ₂) ρ p - nestedTarget f g ρ p)
      (nestedLaw ν ρ) := hfst.integrable_comp_of_integrable hD
  have hint : Integrable (fun p => nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f g ρ p)
      (nestedLaw ν ρ) :=
    (i1.add i2).congr (Eventually.of_forall fun p => by
      simp only [Pi.add_apply]
      ring)
  refine ⟨hint, ?_⟩
  have e1 : ∫ p, (nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ p, (nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f (gh ℓ₂) ρ p) ∂(nestedLaw ν ρ) +
        ∫ z, (f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν := by
    have e2 : ∫ p, (nestedTarget f (gh ℓ₂) ρ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
        ∫ z, (f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν :=
      integral_comp_of_measurePreserving hfst hD.aestronglyMeasurable
    rw [← e2, ← integral_add i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun p => by ring)
  have hb2 : |∫ z, (f (∫ v, gh ℓ₂ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν| ≤ (|a₁| + |c|) * c_w / q := by
    have h := integral_mono_ae hD.abs (integrable_const ((|a₁| + |c|) * (c_w / q))) hpt
    rw [integral_const, probReal_univ, one_smul] at h
    rw [mul_div_assoc]
    exact abs_integral_le_integral_abs.trans h
  have hb1' : |∫ p, (nestedP f (gh ℓ₂) ℓ₁ p - nestedTarget f (gh ℓ₂) ρ p) ∂(nestedLaw ν ρ)| ≤
      4 * c_d * |c| * (1 + 80 * m₄) * (1 + c_w) / r := by
    rw [← hr2] at hb1
    have hK : 0 ≤ 2 * c_d * |c| * (1 + 80 * m₄) := by positivity
    have h1 : 2 * (1 + c_w * r / q) / r ^ 2 ≤ 2 * (1 + c_w) / r := by
      rw [div_le_div_iff₀ (by positivity) hr0]
      have : c_w * r / q ≤ c_w * r := div_le_self (by positivity) hq1
      nlinarith
    calc _ ≤ 2 * c_d * |c| * (1 + 80 * m₄) * (2 * (1 + c_w * r / q)) / r ^ 2 := by
          rw [le_div_iff₀ (by positivity), mul_comm]
          exact hb1
      _ = 2 * c_d * |c| * (1 + 80 * m₄) * (2 * (1 + c_w * r / q) / r ^ 2) := by ring
      _ ≤ 2 * c_d * |c| * (1 + 80 * m₄) * (2 * (1 + c_w) / r) := by gcongr
      _ = _ := by ring
  rw [e1]
  exact (abs_add_le _ _).trans (add_le_add hb1' hb2)

/-- The §9.1 correction is integrable if every level approximation `P_ℓ` is (Giles 2015, §9.1). -/
lemma integrable_nestedDelta_of {f : ℝ → ℝ} {g : 𝒵 → 𝒲 → ℝ}
    (hint : ∀ ℓ, Integrable (nestedP f g ℓ) (nestedLaw ν ρ)) (ℓ : ℕ) :
    Integrable (nestedDelta f g ℓ) (nestedLaw ν ρ) := by
  cases ℓ with
  | zero => exact hint 0
  | succ ℓ =>
    have hφ : MeasurePreserving (fun p : 𝒵 × (ℕ → 𝒲) => (p.1, shiftSeq (2 ^ ℓ) p.2))
        (nestedLaw ν ρ) (nestedLaw ν ρ) :=
      (MeasurePreserving.id ν).prod (measurePreserving_shiftSeq ρ (2 ^ ℓ))
    have h2 : Integrable (fun p : 𝒵 × (ℕ → 𝒲) =>
        f (innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2))) (nestedLaw ν ρ) :=
      hφ.integrable_comp_of_integrable (hint ℓ)
    exact ((hint (ℓ + 1)).sub ((hint ℓ).div_const 2)).sub (h2.div_const 2)

/-- **The MIMC correction has the right expectation** (Giles 2015, §9.2, p. 59, and §2.4:
`E[Y_ℓ] = E[ΔP_ℓ]`): if every `P_{(a,b)} = f(A_{2^a}(g_b))` is integrable, then `E[Y_{(a,b)}]`
is `(E[P_{a,b}] − [a > 0] E[P_{a−1,b}])` minus `[b > 0] (E[P_{a,b−1}] − [a > 0] E[P_{a−1,b−1}])`
(`integral_nestedDelta`). -/
lemma integral_nestedMimcDelta_eq {f : ℝ → ℝ} {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hint : ∀ a b, Integrable (nestedP f (gh b) a) (nestedLaw ν ρ)) (a b : ℕ) :
    ∫ p, nestedMimcDelta f gh a b p ∂(nestedLaw ν ρ) =
      ((∫ p, nestedP f (gh b) a p ∂(nestedLaw ν ρ)) -
        if a = 0 then 0 else ∫ p, nestedP f (gh b) (a - 1) p ∂(nestedLaw ν ρ)) -
      if b = 0 then 0 else
        ((∫ p, nestedP f (gh (b - 1)) a p ∂(nestedLaw ν ρ)) -
          if a = 0 then 0 else ∫ p, nestedP f (gh (b - 1)) (a - 1) p ∂(nestedLaw ν ρ)) := by
  have hE : ∀ j i, ∫ p, nestedDelta f (gh j) i p ∂(nestedLaw ν ρ) =
      (∫ p, nestedP f (gh j) i p ∂(nestedLaw ν ρ)) -
        if i = 0 then 0 else ∫ p, nestedP f (gh j) (i - 1) p ∂(nestedLaw ν ρ) := fun j i => by
    rw [integral_nestedDelta ν ρ f (gh j) (fun ℓ => hint ℓ j) i]
    cases i with
    | zero => simp [levelDiff]
    | succ i =>
      simp only [levelDiff_succ, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      exact integral_sub (hint (i + 1) j) (hint i j)
  cases b with
  | zero =>
    show ∫ p, nestedDelta f (gh 0) a p ∂(nestedLaw ν ρ) = _
    rw [hE, if_pos rfl, sub_zero]
  | succ b =>
    show ∫ p, (nestedDelta f (gh (b + 1)) a p - nestedDelta f (gh b) a p) ∂(nestedLaw ν ρ) = _
    rw [integral_sub (integrable_nestedDelta_of ν ρ (fun ℓ => hint ℓ (b + 1)) a)
      (integrable_nestedDelta_of ν ρ (fun ℓ => hint ℓ b) a), hE, hE,
      if_neg (Nat.add_one_ne_zero b), Nat.add_sub_cancel]

/-- The MIMC correction (Giles 2015, §9.2, p. 59) is measurable. -/
lemma measurable_nestedMimcDelta {f : ℝ → ℝ} (hfm : Measurable f) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) (a b : ℕ) :
    Measurable (nestedMimcDelta f gh a b) := by
  cases b with
  | zero => exact measurable_nestedDelta hfm (hgh 0) a
  | succ b =>
    exact (measurable_nestedDelta hfm (hgh (b + 1)) a).sub (measurable_nestedDelta hfm (hgh b) a)

/-- **`V_ℓ = O(2^{−ℓ₁−ℓ₂})` on every level, the boundary levels included** (Giles 2015, §9.2;
Theorem 2 needs the rates for every `ℓ ∈ ℕ²`).  Under the hypotheses of
`nested_mimc_kink_variance_rate` and `E[g₀(Z, W)²] < ∞` there is `B ≥ 0` such that every
`Y_{(a,b)}` is square-integrable and `2^{a+b} E[Y_{(a,b)}²] ≤ B`: at `(0, 0)`, `Y = P₀`; at
`(a + 1, 0)`, the §9.1 correction of `g₀` (`kink_variance_le_of_small_ball`); at `(0, b + 1)`,
one inner sample and `|Y| ≤ (|a₁| + |c|) |g_{b+1} − g_b|`; otherwise
`nested_mimc_kink_variance_rate`. -/
lemma nested_mimc_kink_all_levels {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    (hg0 : Integrable (fun p : 𝒵 × 𝒲 => gh 0 p.1 p.2 ^ 2) (ν.prod ρ))
    {g : 𝒵 → 𝒲 → ℝ} {c_w c_d cₛ : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ cₛ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℕ, MemLp (nestedMimcDelta f gh a b) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ (a + b) * ∫ p, nestedMimcDelta f gh a b p ^ 2 ∂(nestedLaw ν ρ) ≤ B := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  have hcd : 0 ≤ c_d := nonneg_of_small_ball hball
  have hcw : 0 ≤ c_w := by
    obtain ⟨z, hz⟩ := (hw 0).exists
    exact le_trans (by positivity) hz
  have hm₄ : 0 ≤ m₄ := by
    obtain ⟨z, hz⟩ := (hfib 0).exists
    exact (integral_nonneg fun v => by positivity).trans hz.2
  have hcs : 0 ≤ cₛ :=
    le_trans (mul_nonneg (by positivity) (integral_nonneg fun p => sq_nonneg _)) (hs 0)
  have hP0 : MemLp (nestedP f (gh 0) 0) 2 (nestedLaw ν ρ) :=
    memLp_two_kink_comp hf (measurable_innerMean (hgh 0) _ measurable_id)
      (integral_innerMean_sq_le ν ρ (hgh 0) hg0 (M := 2 ^ 0) (by positivity)).1
  set B₀ : ℝ := ∫ p, nestedP f (gh 0) 0 p ^ 2 ∂(nestedLaw ν ρ) with hB₀
  set Ka : ℝ := 4 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w) with hKa
  set Kb : ℝ := 2 * (|a₁| + |c|) ^ 2 * cₛ with hKb
  set Kab : ℝ := 4 * (8 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w) +
    c ^ 2 * (8 * cₛ + 9 / 4 * c_d * c_w ^ 2 * (7 + 96 * m₄ + 3 * c_w))) with hKab
  have hB0 : 0 ≤ B₀ := integral_nonneg fun p => sq_nonneg _
  have hKa0 : 0 ≤ Ka := by positivity
  have hKb0 : 0 ≤ Kb := by positivity
  have hKab0 : 0 ≤ Kab := by positivity
  refine ⟨B₀ + Ka + Kb + Kab, by positivity, fun a b => ?_⟩
  have hδ : ∀ j, ∀ᵐ z ∂ν, |(∫ v, g z v ∂ρ - k) - (∫ v, gh j z v ∂ρ - k)| ≤ c_w / 2 ^ j :=
    fun j => (hw j).mono fun z hz => by
      rw [show ∫ v, g z v ∂ρ - k - (∫ v, gh j z v ∂ρ - k) =
        -(∫ v, gh j z v ∂ρ - ∫ v, g z v ∂ρ) by ring, abs_neg, le_div_iff₀ (by positivity),
        mul_comm]
      exact hz
  rcases a with _ | a <;> rcases b with _ | b
  · -- `(0, 0)`: the plain nested estimator `P₀`
    refine ⟨hP0, ?_⟩
    show (2 : ℝ) ^ (0 + 0) * ∫ p, nestedP f (gh 0) 0 p ^ 2 ∂(nestedLaw ν ρ) ≤ _
    rw [pow_zero, one_mul]
    linarith
  · -- `(0, b + 1)`: one inner sample, `|Y| ≤ (|a₁| + |c|) |g_{b+1} − g_b|`
    set L : ℝ := |a₁| + |c| with hL
    set H : 𝒵 → 𝒲 → ℝ := fun z v => gh (b + 1) z v - gh b z v with hHdef
    have hHm : Measurable (Function.uncurry H) := (hgh (b + 1)).sub (hgh b)
    have hH2 := (levelDiff_fiber_bounds ν ρ hgh hfib hw b).2
    obtain ⟨hI2, hIle⟩ := integral_innerMean_sq_le ν ρ hHm hH2 (M := 2 ^ 0) (by positivity)
    have hpt : ∀ p, nestedMimcDelta f gh 0 (b + 1) p ^ 2 ≤
        L ^ 2 * innerMean H (2 ^ 0) p.1 p.2 ^ 2 := fun p => by
      show (f (innerMean (gh (b + 1)) (2 ^ 0) p.1 p.2) -
        f (innerMean (gh b) (2 ^ 0) p.1 p.2)) ^ 2 ≤ _
      have h1 := abs_kink_sub_le hf (innerMean (gh (b + 1)) (2 ^ 0) p.1 p.2)
        (innerMean (gh b) (2 ^ 0) p.1 p.2)
      rw [innerMean_sub] at h1
      calc _ = |f (innerMean (gh (b + 1)) (2 ^ 0) p.1 p.2) -
            f (innerMean (gh b) (2 ^ 0) p.1 p.2)| ^ 2 := (sq_abs _).symm
        _ ≤ (L * |innerMean H (2 ^ 0) p.1 p.2|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = L ^ 2 * innerMean H (2 ^ 0) p.1 p.2 ^ 2 := by rw [mul_pow, sq_abs]
    have hYm := measurable_nestedMimcDelta hfm hgh 0 (b + 1)
    have hY2i : Integrable (fun p => nestedMimcDelta f gh 0 (b + 1) p ^ 2) (nestedLaw ν ρ) :=
      (hI2.const_mul (L ^ 2)).mono' (hYm.pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun p => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact hpt p)
    refine ⟨(memLp_two_iff_integrable_sq hYm.aestronglyMeasurable).2 hY2i, ?_⟩
    have h1 : ∫ p, nestedMimcDelta f gh 0 (b + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        L ^ 2 * ∫ p, H p.1 p.2 ^ 2 ∂(ν.prod ρ) := by
      calc _ ≤ ∫ p, L ^ 2 * innerMean H (2 ^ 0) p.1 p.2 ^ 2 ∂(nestedLaw ν ρ) :=
            integral_mono hY2i (hI2.const_mul _) hpt
        _ = L ^ 2 * ∫ p, innerMean H (2 ^ 0) p.1 p.2 ^ 2 ∂(nestedLaw ν ρ) :=
            integral_const_mul _ _
        _ ≤ L ^ 2 * ∫ p, H p.1 p.2 ^ 2 ∂(ν.prod ρ) := by gcongr
    have h2 := hs b
    have e : (2 : ℝ) ^ (0 + (b + 1)) = 2 * 2 ^ b := by rw [zero_add, pow_succ]; ring
    rw [e]
    have : 2 * 2 ^ b * ∫ p, nestedMimcDelta f gh 0 (b + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤ Kb := by
      calc 2 * 2 ^ b * ∫ p, nestedMimcDelta f gh 0 (b + 1) p ^ 2 ∂(nestedLaw ν ρ)
          ≤ 2 * 2 ^ b * (L ^ 2 * ∫ p, H p.1 p.2 ^ 2 ∂(ν.prod ρ)) := by gcongr
        _ = 2 * L ^ 2 * (2 ^ b * ∫ p, H p.1 p.2 ^ 2 ∂(ν.prod ρ)) := by ring
        _ ≤ 2 * L ^ 2 * cₛ := by gcongr
        _ = Kb := by rw [hKb]
    linarith
  · -- `(a + 1, 0)`: the §9.1 correction of `g₀`
    obtain ⟨hr0, hr1, hr2, hr3⟩ := two_rpow_half_props a
    set r : ℝ := (2 : ℝ) ^ ((a : ℝ) / 2) with hr
    have hR2 : 1 + 2 ^ a * (c_w / 2 ^ 0) ^ 2 / 32 ≤ (1 + c_w * r) ^ 2 := by
      rw [pow_zero, div_one, ← hr2]
      have : 0 ≤ c_w * r := by positivity
      nlinarith
    obtain ⟨hN, hNle⟩ := kink_variance_le_of_small_ball ν ρ hf (hgh 0) (hfib 0)
      (u := fun z => ∫ v, g z v ∂ρ - k) (hδ 0) hball a (R := 1 + c_w * r) (by positivity) hR2
    refine ⟨hN, ?_⟩
    rw [← hr3] at hNle
    show (2 : ℝ) ^ (a + 1 + 0) * ∫ p, nestedDelta f (gh 0) (a + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤ _
    have e : (2 : ℝ) ^ (a + 1 + 0) = 2 * r ^ 2 := by rw [add_zero, pow_succ, hr2]; ring
    rw [e]
    have hI0 : 0 ≤ ∫ p, nestedDelta f (gh 0) (a + 1) p ^ 2 ∂(nestedLaw ν ρ) :=
      integral_nonneg fun p => sq_nonneg _
    have : 2 * r ^ 2 * ∫ p, nestedDelta f (gh 0) (a + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤ Ka := by
      have h3 : r * (2 * r ^ 2 * ∫ p, nestedDelta f (gh 0) (a + 1) p ^ 2 ∂(nestedLaw ν ρ)) ≤
          r * Ka := by
        calc r * (2 * r ^ 2 * ∫ p, nestedDelta f (gh 0) (a + 1) p ^ 2 ∂(nestedLaw ν ρ))
            = 2 * (r ^ 3 * ∫ p, nestedDelta f (gh 0) (a + 1) p ^ 2 ∂(nestedLaw ν ρ)) := by ring
          _ ≤ 2 * (2 * c_d * c ^ 2 * (1 + 16 * m₄) * (1 + c_w * r)) := by gcongr
          _ ≤ r * Ka := by
              rw [hKa]
              have : 0 ≤ c_d * c ^ 2 * (1 + 16 * m₄) := by positivity
              nlinarith
      exact le_of_mul_le_mul_left h3 hr0
    linarith
  · -- `(a + 1, b + 1)`: `nested_mimc_kink_variance_rate`
    obtain ⟨hY, hV⟩ := nested_mimc_kink_variance_rate ν ρ hf hgh hfib hw hball hs a b
    refine ⟨hY, ?_⟩
    have e : (2 : ℝ) ^ (a + 1 + (b + 1)) = 4 * 2 ^ (a + b) := by
      rw [show a + 1 + (b + 1) = a + b + 2 by ring, pow_add]
      ring
    rw [e, mul_assoc]
    have : 4 * ((2 : ℝ) ^ (a + b) * ∫ p, nestedMimcDelta f gh (a + 1) (b + 1) p ^ 2
        ∂(nestedLaw ν ρ)) ≤ Kab := by
      rw [hKab]
      gcongr
    linarith

end Complexity

/-- **The exponents of Theorem 2 for the corrected rates** (Giles 2015, §9.2, p. 60: "In Theorem
2 this corresponds to `α₁ = α₂ = 1, β₁ = β₂ = 2`, and `γ₁ = γ₂ = 1`, so the overall complexity
is `O(ε⁻²)`", and for a piecewise differentiable `f` "with MIMC we would have `β₁ = β₂ = 1.5`
and so the complexity would remain `O(ε⁻²)`").  With the corrected `β = (1, 1)` and
`γ = (1, 1)`, `η = max_d (γ_d − β_d)/α_d = 0` is attained in both directions (`D₂ = 2`), and the
bound of Theorem 2 (`giles_theorem2_boundary`) is `ε⁻² |log ε|^{e₁}` with
`e₁ = 2D₂ + (D₃ − 3)⁺ = 4`, both for `α = (½, ½)` (`D₃ = 2`, used in
`nested_mimc_kink_complexity`) and for `α = (1, 1)` (`D₃ = 0`, Giles' `e₁ = 2D₂`).  So Theorem 2
with the corrected rates gives only the bound `O(ε⁻² |log ε|⁴)`, whereas with the paper's rates
`β_d > γ_d` it gives `O(ε⁻²)` (compare `nested_mimc_complexity`, which evaluates the paper's
rates); a better mean rate would not change the exponent.  This is an upper bound: whether
`O(ε⁻²)` is attainable with another index set is not decided here. -/
theorem nested_mimc_kink_exponents :
    mimcEta (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) (fun _ => 1) = 0 ∧
      mimcD2 (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) (fun _ => 1) = 2 ∧
      mimcD3 (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) = 2 ∧
      mimcD3 (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1) = 0 ∧
      ∀ ε : ℝ,
        mimcBound (mimcEta (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) (fun _ => 1))
            (2 * (mimcD2 (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) (fun _ => 1) : ℝ) +
              ((mimcD3 (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) - 3 : ℕ) : ℝ))
            (((mimcD2 (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) (fun _ => 1) : ℝ) - 1) *
                (2 + mimcEta (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) (fun _ => 1)) +
              ((mimcD3 (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) - 1 : ℕ) : ℝ)) ε =
          ε ^ (-2 : ℝ) * |Real.log ε| ^ (4 : ℝ) ∧
        mimcBound (mimcEta (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1) (fun _ => 1))
            (2 * (mimcD2 (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1) (fun _ => 1) : ℝ) +
              ((mimcD3 (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1) - 3 : ℕ) : ℝ))
            (((mimcD2 (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1) (fun _ => 1) : ℝ) - 1) *
                (2 + mimcEta (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1) (fun _ => 1)) +
              ((mimcD3 (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1) - 1 : ℕ) : ℝ)) ε =
          ε ^ (-2 : ℝ) * |Real.log ε| ^ (4 : ℝ) := by
  have h1 : mimcEta (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) (fun _ => 1) = 0 := by
    simp only [mimcEta, Finset.sup'_const]
    norm_num
  have h1' : mimcEta (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1) (fun _ => 1) = 0 := by
    simp only [mimcEta, Finset.sup'_const]
    norm_num
  have h2 : mimcD2 (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) (fun _ => 1) = 2 := by
    simp only [mimcD2, h1]
    norm_num
  have h2' : mimcD2 (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1) (fun _ => 1) = 2 := by
    simp only [mimcD2, h1']
    norm_num
  have h3 : mimcD3 (D := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => 1) = 2 := by
    simp only [mimcD3]
    norm_num
  have h3' : mimcD3 (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1) = 0 := by
    simp only [mimcD3]
    norm_num
  refine ⟨h1, h2, h3, h3', fun ε => ⟨?_, ?_⟩⟩
  · rw [h1, h2, h3, mimcBound_of_eq rfl,
      show (2 * ((2 : ℕ) : ℝ) + ((2 - 3 : ℕ) : ℝ)) = 4 by norm_num]
  · rw [h1', h2', h3', mimcBound_of_eq rfl,
      show (2 * ((2 : ℕ) : ℝ) + ((0 - 3 : ℕ) : ℝ)) = 4 by norm_num]

section Cost

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **Theorem 2 for nested MIMC with a piecewise linear `f`: cost `O(ε⁻² |log ε|⁴)`** (Giles
2015, §9.2, p. 60: "On the other hand, with MIMC we would have `β₁ = β₂ = 1.5` and so the
complexity would remain `O(ε⁻²)`. This illustrates the benefit of the MIMC approach compared to
standard MLMC.").  Let `f(x) = a₀ + a₁x + c max(x − k, 0)`, let level `ℓ = (ℓ₁, ℓ₂)` use
`2^{ℓ₁}` inner samples of the level-`ℓ₂` approximation `g_{ℓ₂}`, and let `Y_ℓ` be the six-term
correction (`nestedMimcDelta`), under the hypotheses of `nested_mimc_kink_variance_rate`
(bounded centred conditional fourth moments, first order weak convergence uniformly in the outer
sample, strong order `½` in `L²`, the small ball for `E_W[g(Z, W)]` at the kink) and
`E[g₀(Z, W)²] < ∞`.  Let the inputs `ω^{(ℓ,n)}` be independent with law `ν ⊗ ρ^{⊗ℕ}` and let a
level-`ℓ` sample cost `C_ℓ ≤ c₃ 2^{ℓ₁+ℓ₂}` on average.  Then there is `c₄ > 0` such that for
every `0 < ε < e⁻¹` there are a finite set of levels `𝓛 ⊂ ℕ²` and `N_ℓ ≥ 1` for which the MIMC
estimator `∑_{ℓ∈𝓛} N_ℓ⁻¹ ∑_{n<N_ℓ} Y_ℓ(ω^{(ℓ,n)})` of `E_Z[f(E_W[g(Z, W)])]` has mean square
error `< ε²` at expected cost `≤ c₄ ε⁻² |log ε|⁴`.  Proof: Theorem 2 (`giles_theorem2_boundary`)
with `α = (½, ½)`, `β = γ = (1, 1)` (`nested_mimc_kink_all_levels`, `nested_mimc_kink_bias`,
`integral_nestedMimcDelta_eq`, `nested_mimc_kink_exponents`).  Correction: the paper derives
`O(ε⁻²)` from Theorem 2 with `β_d = 1.5 > γ_d = 1`; these rates are false
(`nested_mimc_kink_rates_false`), and with the corrected `β = γ` Theorem 2 gives only the bound
`O(ε⁻² |log ε|⁴)`.  This is an upper bound: whether `O(ε⁻²)` is attainable with another index
set is not decided here (for `kinkInnerApprox` itself, whose corrections off the two axes have
mean zero, the index set made of the two axes appears to attain it; not formalised).  The bound
is still below the MLMC cost bound `O(ε^{−2.5})` of `nested_kink_sde_mlmc_complexity`
(`nested_mimc_kink_beats_mlmc`).  The mean rate `α = (½, ½)` follows from the variance; the
better `α₂ = 1` of `nested_mimc_kink_mean_rate` would need first order strong convergence and
would not change the exponent.  Deviation: as in `nested_mimc_kink_variance_rate`. -/
theorem nested_mimc_kink_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) {m₄ : ℝ}
    (hfib : ∀ ℓ, ∀ᵐ z ∂ν, Integrable (fun v => gh ℓ z v ^ 4) ρ ∧
      ∫ v, (gh ℓ z v - ∫ u, gh ℓ z u ∂ρ) ^ 4 ∂ρ ≤ m₄)
    (hg0 : Integrable (fun p : 𝒵 × 𝒲 => gh 0 p.1 p.2 ^ 2) (ν.prod ρ))
    {g : 𝒵 → 𝒲 → ℝ} {c_w c_d cₛ : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (hs : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 2 ∂(ν.prod ρ) ≤ cₛ)
    (ω : (Fin 2 → ℕ) × ℕ → Ω → 𝒵 × (ℕ → 𝒲))
    (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw ν ρ)) (hind : iIndepFun ω μ)
    (cost : (Fin 2 → ℕ) → ℕ → Ω → ℝ) (C : (Fin 2 → ℕ) → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : Fin 2 → ℕ, C ℓ ≤ c₃ * 2 ^ (ℓ 0 + ℓ 1)) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (𝓛 : Finset (Fin 2 → ℕ)) (N : (Fin 2 → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (∑ ℓ ∈ 𝓛, blockMean (fun ℓ : Fin 2 → ℕ => nestedMimcDelta f gh (ℓ 0) (ℓ 1))
          ω ℓ (N ℓ) x - ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2] < ε ^ 2 ∧
        μ[fun x => ∑ ℓ ∈ 𝓛, ∑ n ∈ range (N ℓ), cost ℓ n x] ≤
          c₄ * (ε ^ (-2 : ℝ) * |Real.log ε| ^ (4 : ℝ)) := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  set Δ : (Fin 2 → ℕ) → 𝒵 × (ℕ → 𝒲) → ℝ := fun ℓ => nestedMimcDelta f gh (ℓ 0) (ℓ 1)
    with hΔdef
  obtain ⟨B, hB0, hB⟩ := nested_mimc_kink_all_levels ν ρ hf hgh hfib hg0 hw hball hs
  have hΔm : ∀ ℓ, Measurable (Δ ℓ) := fun ℓ => measurable_nestedMimcDelta hfm hgh _ _
  have hΔ : ∀ ℓ, MemLp (Δ ℓ) 2 (nestedLaw ν ρ) := fun ℓ => (hB _ _).1
  -- integrability of the quantity of interest and of every approximation `P_{(a,b)}`
  have hbias := fun a b => nested_mimc_kink_bias ν ρ hf hgh hfib hw hball a b
  have hP0 : MemLp (nestedP f (gh 0) 0) 2 (nestedLaw ν ρ) :=
    memLp_two_kink_comp hf (measurable_innerMean (hgh 0) _ measurable_id)
      (integral_innerMean_sq_le ν ρ (hgh 0) hg0 (M := 2 ^ 0) (by positivity)).1
  have hPt : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) :=
    ((hP0.integrable one_le_two).sub (hbias 0 0).1).congr
      (Eventually.of_forall fun p => by simp)
  have hint : ∀ a b, Integrable (nestedP f (gh b) a) (nestedLaw ν ρ) := fun a b =>
    ((hbias a b).1.add hPt).congr (Eventually.of_forall fun p => by simp)
  -- transport to `Ω` along the input `ω (0, 0)`
  have hφ := hω (0, 0)
  have tr : ∀ F : 𝒵 × (ℕ → 𝒲) → ℝ, Integrable F (nestedLaw ν ρ) →
      ∫ x, F (ω (0, 0) x) ∂μ = ∫ y, F y ∂(nestedLaw ν ρ) := fun F hF =>
    integral_comp_of_measurePreserving hφ hF.aestronglyMeasurable
  set P : Ω → ℝ := fun x => nestedTarget f g ρ (ω (0, 0) x) with hPdef
  set Pℓ : (Fin 2 → ℕ) → Ω → ℝ := fun ℓ x => nestedP f (gh (ℓ 1)) (ℓ 0) (ω (0, 0) x)
    with hPℓdef
  have hPμ : Integrable P μ := hφ.integrable_comp_of_integrable hPt
  have hPℓμ : ∀ ℓ, Integrable (Pℓ ℓ) μ := fun ℓ => hφ.integrable_comp_of_integrable (hint _ _)
  have hdot : ∀ (a : ℝ) (ℓ : Fin 2 → ℕ), dot (fun _ => a) ℓ = a * ((ℓ 0 : ℝ) + ℓ 1) := by
    intro a ℓ
    simp only [dot, Fin.sum_univ_two]
    ring
  -- (i) the bias tends to zero
  have h_i : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ ℓ : Fin 2 → ℕ, (∀ d, n₀ ≤ ℓ d) →
      |μ[fun x => Pℓ ℓ x - P x]| < δ := by
    intro δ hδ
    set K : ℝ := 4 * c_d * |c| * (1 + 80 * m₄) * (1 + c_w) with hK
    set K' : ℝ := (|a₁| + |c|) * c_w with hK'
    have hcd : 0 ≤ c_d := nonneg_of_small_ball hball
    have hcw : 0 ≤ c_w := by
      obtain ⟨z, hz⟩ := (hw 0).exists
      exact le_trans (by positivity) hz
    have hm₄ : 0 ≤ m₄ := by
      obtain ⟨z, hz⟩ := (hfib 0).exists
      exact (integral_nonneg fun v => by positivity).trans hz.2
    have hK0 : 0 ≤ K := by positivity
    have hK'0 : 0 ≤ K' := by positivity
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (K + K' + 1) by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨2 * m, fun ℓ hℓ => ?_⟩
    have e : μ[fun x => Pℓ ℓ x - P x] =
        ∫ p, (nestedP f (gh (ℓ 1)) (ℓ 0) p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) :=
      tr _ (hbias (ℓ 0) (ℓ 1)).1
    rw [e]
    have hb := (hbias (ℓ 0) (ℓ 1)).2
    have h2m : (2 : ℝ) ^ m ≤ 2 ^ ((ℓ 0 : ℝ) / 2) := by
      rw [← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have := hℓ 0
      have : (2 * m : ℝ) ≤ ℓ 0 := by exact_mod_cast this
      linarith
    have h2m' : (2 : ℝ) ^ m ≤ 2 ^ (ℓ 1) :=
      pow_le_pow_right₀ (by norm_num) (by have := hℓ 1; omega)
    have hpm : (0 : ℝ) < 2 ^ m := by positivity
    have b1 : K / 2 ^ ((ℓ 0 : ℝ) / 2) ≤ K * (1 / 2) ^ m := by
      rw [one_div_pow, ← div_eq_mul_one_div]
      exact div_le_div_of_nonneg_left hK0 hpm h2m
    have b2 : K' / 2 ^ (ℓ 1) ≤ K' * (1 / 2) ^ m := by
      rw [one_div_pow, ← div_eq_mul_one_div]
      exact div_le_div_of_nonneg_left hK'0 hpm h2m'
    have hlt : (K + K' + 1) * (1 / 2) ^ m < δ := by
      rw [lt_div_iff₀ (by positivity)] at hm
      linarith
    have hpos : (0 : ℝ) < (1 / 2) ^ m := by positivity
    calc _ ≤ K / 2 ^ ((ℓ 0 : ℝ) / 2) + K' / 2 ^ (ℓ 1) := hb
      _ ≤ K * (1 / 2) ^ m + K' * (1 / 2) ^ m := add_le_add b1 b2
      _ < δ := by nlinarith
  -- (iii) the corrections have the right means: `E[Y_ℓ] = E[ΔP_ℓ]`
  have h_iii : ∀ (ℓ : Fin 2 → ℕ) (n : ℕ), 0 < n →
      μ[blockMean Δ ω ℓ n] = μ[fun x => crossDiff (fun m => Pℓ m x) ℓ] := by
    intro ℓ n hn
    rw [integral_blockMean hω (fun i => (hΔ i).integrable one_le_two) ℓ hn,
      (integrable_integral_crossDiff Pℓ hPℓμ ℓ).2]
    have e : (fun m => μ[Pℓ m]) = fun m : Fin 2 → ℕ =>
        ∫ p, nestedP f (gh (m 1)) (m 0) p ∂(nestedLaw ν ρ) :=
      funext fun m => tr _ (hint _ _)
    rw [e, crossDiff_two_eq (fun a b => ∫ p, nestedP f (gh b) a p ∂(nestedLaw ν ρ)) ℓ]
    exact integral_nestedMimcDelta_eq ν ρ hint (ℓ 0) (ℓ 1)
  -- (ii) the means, `α = (½, ½)`, from the second moments
  have h_ii : ∀ (ℓ : Fin 2 → ℕ) (n : ℕ), 0 < n → |μ[blockMean Δ ω ℓ n]| ≤
      (B + 1) / 2 * (2 : ℝ) ^ (-dot (fun _ => (1 / 2 : ℝ)) ℓ) := by
    intro ℓ n hn
    rw [integral_blockMean hω (fun i => (hΔ i).integrable one_le_two) ℓ hn]
    obtain ⟨hs0, -, hs2, -⟩ := two_rpow_half_props (ℓ 0 + ℓ 1)
    set s : ℝ := (2 : ℝ) ^ (((ℓ 0 + ℓ 1 : ℕ) : ℝ) / 2) with hsdef
    have h1 := mul_abs_integral_le_of_memLp (hΔ ℓ) hs0
    rw [hs2] at h1
    have h2 : (2 : ℝ) ^ (ℓ 0 + ℓ 1) * ∫ x, Δ ℓ x ^ 2 ∂(nestedLaw ν ρ) ≤ B := (hB _ _).2
    have e : (2 : ℝ) ^ (-dot (fun _ => (1 / 2 : ℝ)) ℓ) = s⁻¹ := by
      rw [hdot, hsdef, ← Real.rpow_neg (by norm_num)]
      congr 1
      push_cast
      ring
    rw [e, ← div_eq_mul_inv, le_div_iff₀ hs0, mul_comm]
    linarith
  -- (iv) the variances, `β = (1, 1)`
  have h_iv : ∀ ℓ : Fin 2 → ℕ, variance (Δ ℓ) (nestedLaw ν ρ) ≤
      (B + 1) * (2 : ℝ) ^ (-dot (fun _ => (1 : ℝ)) ℓ) := by
    intro ℓ
    have hv : variance (Δ ℓ) (nestedLaw ν ρ) ≤ ∫ x, Δ ℓ x ^ 2 ∂(nestedLaw ν ρ) := by
      simpa only [Pi.pow_apply] using variance_le_expectation_sq (hΔm ℓ).aestronglyMeasurable
    have h2 : (2 : ℝ) ^ (ℓ 0 + ℓ 1) * ∫ x, Δ ℓ x ^ 2 ∂(nestedLaw ν ρ) ≤ B := (hB _ _).2
    have e : (2 : ℝ) ^ (-dot (fun _ => (1 : ℝ)) ℓ) = ((2 : ℝ) ^ (ℓ 0 + ℓ 1))⁻¹ := by
      rw [hdot, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
      congr 1
      push_cast
      ring
    rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hv (by positivity : (0 : ℝ) ≤ 2 ^ (ℓ 0 + ℓ 1))
    linarith
  -- (v) the cost, `γ = (1, 1)`
  have h_v : ∀ ℓ : Fin 2 → ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ dot (fun _ => (1 : ℝ)) ℓ := by
    intro ℓ
    have e : (2 : ℝ) ^ dot (fun _ => (1 : ℝ)) ℓ = 2 ^ (ℓ 0 + ℓ 1) := by
      rw [hdot, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rw [e]
    exact hC ℓ
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem2_boundary (μ := μ) (D := 2) P Pℓ
    (fun ℓ n => blockMean Δ ω ℓ n) (fun ℓ n x => ∑ k ∈ range n, cost ℓ k x)
    (fun ℓ => variance (Δ ℓ) (nestedLaw ν ρ)) C (α := fun _ => 1 / 2) (β := fun _ => 1)
    (γ := fun _ => 1) (c₁ := (B + 1) / 2) (c₂ := B + 1) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (by positivity)
    (by positivity) hc₃ hPμ hPℓμ (fun ℓ n _ => memLp_blockMean hω hΔ ℓ n)
    (fun N _ i j hij => indepFun_blockMean (fun p => (hω p).measurable) hind hΔm hij _ _)
    (fun ℓ n _ => integrable_finsetSum _ fun k _ => hcost ℓ k)
    (fun ℓ n _ => by
      rw [integral_finsetSum _ fun k _ => hcost ℓ k]
      simp [hcostC])
    (fun ℓ n hn => variance_blockMean hω hind hΔm hΔ ℓ hn) h_i h_iii h_ii h_iv h_v
  -- the quantity of interest and the exponents
  have hGm : AEMeasurable (fun z => ∫ v, g z v ∂ρ) ν := aemeasurable_condMean_of_weak ν ρ hgh hw
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hPint : μ[P] = ∫ z, f (∫ v, g z v ∂ρ) ∂ν := by
    rw [hPdef, tr _ hPt]
    exact integral_comp_of_measurePreserving hfst
      (hfm.comp_aemeasurable hGm).aestronglyMeasurable
  obtain ⟨-, -, -, -, hbd⟩ := nested_mimc_kink_exponents
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨𝓛, N, hN, hmse, hcost'⟩ := h ε hε hε1
  rw [hPint] at hmse
  rw [(hbd ε).1] at hcost'
  exact ⟨𝓛, N, hN, hmse, hcost'⟩

end Cost

/-- The two elementary bounds behind `nested_mimc_kink_beats_mlmc` (Giles 2015, §9.2, p. 60):
for `0 < ε ≤ 1`, `ε⁻² |log ε|⁴ ≤ 384 ε^{−2.5}` and `ε⁻² |log ε|⁴ ≤ 98304 ε^{3/8} ε^{−2.5}`.
Proof: with `x = |log ε|`, `x⁴ ≤ 4! · 2⁴ e^{x/2}` and `x⁴ ≤ 4! · 8⁴ e^{x/8}`
(`Real.pow_div_factorial_le_exp`). -/
lemma rpow_neg_two_mul_abs_log_pow_four_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ (-2 : ℝ) * |Real.log ε| ^ (4 : ℝ) ≤ 384 * ε ^ (-2.5 : ℝ) ∧
      ε ^ (-2 : ℝ) * |Real.log ε| ^ (4 : ℝ) ≤ 98304 * ε ^ (3 / 8 : ℝ) * ε ^ (-2.5 : ℝ) := by
  have hl : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  set x : ℝ := -Real.log ε with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have habs : |Real.log ε| = x := by rw [abs_of_nonpos hl]
  have h4 : |Real.log ε| ^ (4 : ℝ) = x ^ 4 := by
    rw [habs, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpow : ∀ a : ℝ, ε ^ a = Real.exp (-(a * x)) := fun a => by
    rw [Real.rpow_def_of_pos hε, hx]
    ring_nf
  have e25 : ε ^ (-2.5 : ℝ) = ε ^ (-2 : ℝ) * Real.exp (x / 2) := by
    rw [hpow, hpow (-2), ← Real.exp_add]
    ring_nf
  have e38 : ε ^ (3 / 8 : ℝ) * ε ^ (-2.5 : ℝ) = ε ^ (-2 : ℝ) * Real.exp (x / 8) := by
    rw [hpow, hpow (-2.5), hpow (-2), ← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hε2 : 0 < ε ^ (-2 : ℝ) := Real.rpow_pos_of_pos hε _
  have b1 : x ^ 4 ≤ 384 * Real.exp (x / 2) := by
    have h := Real.pow_div_factorial_le_exp (x / 2) (by positivity) 4
    norm_num [Nat.factorial] at h
    nlinarith
  have b2 : x ^ 4 ≤ 98304 * Real.exp (x / 8) := by
    have h := Real.pow_div_factorial_le_exp (x / 8) (by positivity) 4
    norm_num [Nat.factorial] at h
    nlinarith
  rw [h4]
  constructor
  · rw [e25]
    calc ε ^ (-2 : ℝ) * x ^ 4 ≤ ε ^ (-2 : ℝ) * (384 * Real.exp (x / 2)) := by gcongr
      _ = 384 * (ε ^ (-2 : ℝ) * Real.exp (x / 2)) := by ring
  · rw [mul_assoc, e38]
    calc ε ^ (-2 : ℝ) * x ^ 4 ≤ ε ^ (-2 : ℝ) * (98304 * Real.exp (x / 8)) := by gcongr
      _ = 98304 * (ε ^ (-2 : ℝ) * Real.exp (x / 8)) := by ring

/-- **MIMC still beats MLMC for a piecewise linear `f`, at the level of the cost bounds** (Giles
2015, §9.2, p. 60: "in the MLMC treatment we would get `β = 1.5`, and hence an overall complexity
which is `O(ε^{−2.5})`. … This illustrates the benefit of the MIMC approach compared to standard
MLMC"): the MIMC cost bound `ε⁻² |log ε|⁴` of `nested_mimc_kink_complexity` is at most
`384 ε^{−2.5}` for `0 < ε ≤ 1`, and it is `o(ε^{−2.5})` as `ε → 0⁺`, where `O(ε^{−2.5})` is the
MLMC cost bound of `nested_kink_sde_mlmc_complexity`.  Both are upper bounds (from Theorem 2 and
Theorem 1); no lower bound on the MLMC cost is proved, so "MIMC beats MLMC" holds at the level of
the guaranteed bounds, which is also the level of the paper's claim.  Proof:
`rpow_neg_two_mul_abs_log_pow_four_le` and `ε^{3/8} → 0`. -/
theorem nested_mimc_kink_beats_mlmc :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ε ^ (-2 : ℝ) * |Real.log ε| ^ (4 : ℝ) ≤ 384 * ε ^ (-2.5 : ℝ)) ∧
      (fun ε : ℝ => ε ^ (-2 : ℝ) * |Real.log ε| ^ (4 : ℝ)) =o[𝓝[>] 0]
        fun ε => ε ^ (-2.5 : ℝ) := by
  refine ⟨fun ε hε hε1 => (rpow_neg_two_mul_abs_log_pow_four_le hε hε1).1, ?_⟩
  have ht : Tendsto (fun ε : ℝ => ε ^ (3 / 8 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (3 / 8) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at h
    exact h.mono_left nhdsWithin_le_nhds
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [(tendsto_order.1 ht).2 (c / 98304) (by positivity), self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hεc hε0 hε1
  have hε : (0 : ℝ) < ε := hε0
  have hb := (rpow_neg_two_mul_abs_log_pow_four_le hε hε1.2.le).2
  have h25 : 0 < ε ^ (-2.5 : ℝ) := Real.rpow_pos_of_pos hε _
  have hl : 0 ≤ ε ^ (-2 : ℝ) * |Real.log ε| ^ (4 : ℝ) := by positivity
  rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg h25.le]
  calc ε ^ (-2 : ℝ) * |Real.log ε| ^ (4 : ℝ) ≤ 98304 * ε ^ (3 / 8 : ℝ) * ε ^ (-2.5 : ℝ) := hb
    _ ≤ 98304 * (c / 98304) * ε ^ (-2.5 : ℝ) := by gcongr
    _ = c * ε ^ (-2.5 : ℝ) := by ring

end MLMC
