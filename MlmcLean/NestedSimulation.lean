import MlmcLean.Corrections
import MlmcLean.Theorem2
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Probability.Independence.Integration

/-!
# Nested simulation (Giles 2015, §9)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §9.1 "MLMC
treatment" (pp. 57–58) and §9.2 "MIMC treatment" (pp. 59–60) of the author's version.

Nested simulation estimates `E_Z[f(E_W[g(Z, W)])]`.  On level `ℓ` the inner expectation is
replaced by the mean of `M_ℓ = 2^ℓ` inner samples, and one outer sample of the level-`ℓ`
correction is the antithetic difference `f(½(A₁ + A₂)) − ½ f(A₁) − ½ f(A₂)`, where `A₁`, `A₂` are
the means of the two halves of the inner samples.  With `A_i = E[g(Z, W)] + Δg_i` the paper
states: "if `f` is twice differentiable a Taylor series expansion gives
`Y_ℓ ≈ −(1/(4N_ℓ)) ∑_n f″(E[g(Z⁽ⁿ⁾, W)]) (Δg₁⁽ⁿ⁾ − Δg₂⁽ⁿ⁾)²`", and then, by the Central Limit
Theorem, `E[Y_ℓ] = O(M_ℓ⁻¹)` and `V_ℓ = O(M_ℓ⁻²)`.

* `antithetic_quadratic`: for quadratic `f` (`f″ ≡ K`) the antithetic difference is exactly
  `−(K/8)(A₁ − A₂)²`; it equals `−(K/4)(A₁ − A₂)²` only if `K = 0` or `A₁ = A₂`.  So the
  coefficient of the paper's expansion should be `−1/8`, not `−1/4`; the orders of magnitude
  derived from it are unaffected.
* `abs_midpoint_sub_avg_le`: if `f′` is `K`-Lipschitz (e.g. `|f″| ≤ K`,
  `abs_midpoint_sub_avg_le_of_deriv2`), then `|f(½(A + B)) − ½ f(A) − ½ f(B)| ≤ (K/8)(A − B)²`,
  a rigorous form of the expansion; `abs_taylor_first_le` is the first-order analogue.
* `moments_add_indep`, `moments_sum_indep`: for independent centred `X_i` with `E[X_i²] = v` and
  `E[X_i⁴] ≤ q`, `E[(∑_{i<n} X_i)²] = n v` and `E[(∑_{i<n} X_i)⁴] ≤ n q + 3 n² v²`.  These moment
  bounds replace the Central Limit Theorem in the paper's "`Δg = O(M^{−1/2})`".
* `nested_complexity`, `nested_mimc_complexity`: the exponents of §9.1 and §9.2 in Theorems 1
  and 2.
* `mimc_diff_sq`, `abs_mimc_diff_sq_le`, `abs_mimc_diff_sq_le_rpow`: the difference of squares of
  §9.2 and its order `O(2^{−ℓ₁−ℓ₂})`.
-/

open MeasureTheory ProbabilityTheory Finset Filter

namespace MLMC

/-! ### The antithetic second difference -/

/-- **The antithetic nested difference for quadratic `f`** (Giles 2015, §9.1, p. 58: "if `f` is
twice differentiable a Taylor series expansion gives
`Y_ℓ ≈ −(1/(4N_ℓ)) ∑_n f″(E[g(Z⁽ⁿ⁾, W)]) (Δg₁⁽ⁿ⁾ − Δg₂⁽ⁿ⁾)²`").  With `A = E[g] + Δg₁` and
`B = E[g] + Δg₂` the fine inner mean is `½(A + B)`, and one outer sample contributes
`f(½(A + B)) − ½ f(A) − ½ f(B)`.  For `f(x) = c₀ + c₁x + (K/2)x²` (so `f″ ≡ K`) this is exactly
`−(K/8)(A − B)²`, and it equals `−(K/4)(A − B)²` only if `K = 0` or `A = B`.  So the coefficient
of the paper's expansion should be `−1/8`; the orders of magnitude are unaffected. -/
theorem antithetic_quadratic {f : ℝ → ℝ} {c₀ c₁ K : ℝ}
    (hf : ∀ x, f x = c₀ + c₁ * x + K / 2 * x ^ 2) (A B : ℝ) :
    f ((A + B) / 2) - f A / 2 - f B / 2 = -(K / 8) * (A - B) ^ 2 ∧
      (K ≠ 0 → A ≠ B → f ((A + B) / 2) - f A / 2 - f B / 2 ≠ -(K / 4) * (A - B) ^ 2) := by
  have e : f ((A + B) / 2) - f A / 2 - f B / 2 = -(K / 8) * (A - B) ^ 2 := by
    simp only [hf]
    ring
  refine ⟨e, fun hK hAB h => ?_⟩
  rw [e] at h
  have hsq : (A - B) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hAB)
  exact mul_ne_zero hK hsq (by linarith)

/-- If `f′` is `K`-Lipschitz, then `K x²/2 − f` and `K x²/2 + f` are convex on `ℝ`: their
derivatives `K x ∓ f′(x)` are monotone (Giles 2015, §9.1, used for the expansion on p. 58). -/
lemma convexOn_half_sq_sub_add {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) :
    ConvexOn ℝ Set.univ (fun x => K / 2 * x ^ 2 - f x) ∧
      ConvexOn ℝ Set.univ (fun x => K / 2 * x ^ 2 + f x) := by
  have hsq : ∀ x : ℝ, HasDerivAt (fun y => y ^ 2) (2 * x) x := fun x => by
    simpa using hasDerivAt_pow 2 x
  have hd1 : ∀ x, HasDerivAt (fun y => K / 2 * y ^ 2 - f y) (K / 2 * (2 * x) - f' x) x :=
    fun x => ((hsq x).const_mul (K / 2)).sub (hf x)
  have hd2 : ∀ x, HasDerivAt (fun y => K / 2 * y ^ 2 + f y) (K / 2 * (2 * x) + f' x) x :=
    fun x => ((hsq x).const_mul (K / 2)).add (hf x)
  constructor
  · refine Monotone.convexOn_univ_of_deriv (fun x => (hd1 x).differentiableAt) ?_
    rw [show deriv (fun y => K / 2 * y ^ 2 - f y) = fun x => K / 2 * (2 * x) - f' x from
      funext fun x => (hd1 x).deriv]
    intro x y hxy
    have h := (abs_le.1 (hf' x y hxy)).2
    show K / 2 * (2 * x) - f' x ≤ K / 2 * (2 * y) - f' y
    linarith
  · refine Monotone.convexOn_univ_of_deriv (fun x => (hd2 x).differentiableAt) ?_
    rw [show deriv (fun y => K / 2 * y ^ 2 + f y) = fun x => K / 2 * (2 * x) + f' x from
      funext fun x => (hd2 x).deriv]
    intro x y hxy
    have h := (abs_le.1 (hf' x y hxy)).1
    show K / 2 * (2 * x) + f' x ≤ K / 2 * (2 * y) + f' y
    linarith

/-- **The antithetic second difference** (Giles 2015, §9.1, p. 58, a rigorous form of the Taylor
expansion "`Y_ℓ ≈ −(1/(4N_ℓ)) ∑_n f″(E[g(Z⁽ⁿ⁾, W)]) (Δg₁⁽ⁿ⁾ − Δg₂⁽ⁿ⁾)²`").  If `f` is
differentiable and its derivative is `K`-Lipschitz, `|f′(y) − f′(x)| ≤ K (y − x)` for `x ≤ y`,
then `|f(½(A + B)) − ½ f(A) − ½ f(B)| ≤ (K/8)(A − B)²` for all `A, B`. -/
theorem abs_midpoint_sub_avg_le {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) (A B : ℝ) :
    |f ((A + B) / 2) - f A / 2 - f B / 2| ≤ K / 8 * (A - B) ^ 2 := by
  obtain ⟨h1, h2⟩ := convexOn_half_sq_sub_add hf hf'
  have hmid : (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B = (A + B) / 2 := by
    rw [smul_eq_mul, smul_eq_mul]
    ring
  have k1 := h1.2 (Set.mem_univ A) (Set.mem_univ B) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have k2 := h2.2 (Set.mem_univ A) (Set.mem_univ B) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [hmid] at k1 k2
  simp only [smul_eq_mul] at k1 k2
  rw [abs_le]
  constructor <;> linarith

/-- **First-order Taylor bound** (Giles 2015, §9.1: the bias of the nested approximation `P_ℓ`).
If `f` is differentiable and its derivative is `K`-Lipschitz, then
`|f(y) − f(x) − f′(x)(y − x)| ≤ (K/2)(y − x)²`. -/
theorem abs_taylor_first_le {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) (x y : ℝ) :
    |f y - f x - f' x * (y - x)| ≤ K / 2 * (y - x) ^ 2 := by
  obtain ⟨h1, h2⟩ := convexOn_half_sq_sub_add hf hf'
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  -- the tangent-line inequality for a differentiable convex function
  have tangent : ∀ {φ : ℝ → ℝ} {d : ℝ}, ConvexOn ℝ Set.univ φ → HasDerivAt φ d x →
      φ x + d * (y - x) ≤ φ y := by
    intro φ d hφ hd
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) hxy hd
      rw [slope_def_field, le_div_iff₀ (sub_pos.2 hxy)] at h
      linarith
    · subst hxy
      simp
    · have h := hφ.slope_le_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) hxy hd
      rw [slope_def_field, div_le_iff₀ (sub_pos.2 hxy)] at h
      linarith
  have t1 : K / 2 * x ^ 2 - f x + (K / 2 * (2 * x) - f' x) * (y - x) ≤ K / 2 * y ^ 2 - f y :=
    tangent h1 ((hsq.const_mul (K / 2)).sub (hf x))
  have t2 : K / 2 * x ^ 2 + f x + (K / 2 * (2 * x) + f' x) * (y - x) ≤ K / 2 * y ^ 2 + f y :=
    tangent h2 ((hsq.const_mul (K / 2)).add (hf x))
  rw [abs_le]
  constructor <;> linarith

/-- A bounded second derivative makes the derivative Lipschitz (Giles 2015, §9.1, "if `f` is twice
differentiable"): if `f′` has derivative `f″` with `|f″| ≤ K`, then `|f′(y) − f′(x)| ≤ K (y − x)`
for `x ≤ y` (mean value theorem). -/
theorem abs_deriv_sub_le_of_deriv2 {f' f'' : ℝ → ℝ} {K : ℝ}
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hK : ∀ x, |f'' x| ≤ K) (x y : ℝ) (hxy : x ≤ y) :
    |f' y - f' x| ≤ K * (y - x) := by
  have hd : Differentiable ℝ f' := fun z => (hf' z).differentiableAt
  have hup : f' y - f' x ≤ K * (y - x) :=
    image_sub_le_mul_sub_of_deriv_le hd
      (fun z => by rw [(hf' z).deriv]; exact (abs_le.1 (hK z)).2) hxy
  have hlo : -K * (y - x) ≤ f' y - f' x :=
    mul_sub_le_image_sub_of_le_deriv hd
      (fun z => by rw [(hf' z).deriv]; exact (abs_le.1 (hK z)).1) hxy
  rw [abs_le]
  constructor <;> linarith

/-- **The antithetic second difference for `|f″| ≤ K`** (Giles 2015, §9.1, p. 58: "if `f` is twice
differentiable a Taylor series expansion gives …"): if `f` is twice differentiable with
`|f″| ≤ K`, then `|f(½(A + B)) − ½ f(A) − ½ f(B)| ≤ (K/8)(A − B)²`. -/
theorem abs_midpoint_sub_avg_le_of_deriv2 {f f' f'' : ℝ → ℝ} {K : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hK : ∀ x, |f'' x| ≤ K) (A B : ℝ) :
    |f ((A + B) / 2) - f A / 2 - f B / 2| ≤ K / 8 * (A - B) ^ 2 :=
  abs_midpoint_sub_avg_le hf (abs_deriv_sub_le_of_deriv2 hf' hK) A B

/-! ### The MIMC treatment: the difference of squares -/

/-- **The difference of squares of §9.2** (Giles 2015, §9.2, p. 60: "The difference of squares
can be re-arranged as …").  With `a₁ = Δg_{1,ℓ₂}`, `a₂ = Δg_{1,ℓ₂−1}`, `b₁ = Δg_{2,ℓ₂}` and
`b₂ = Δg_{2,ℓ₂−1}`:
`(a₁ − b₁)² − (a₂ − b₂)² = ((a₁ + a₂) − (b₁ + b₂)) ((a₁ − a₂) − (b₁ − b₂))`. -/
theorem mimc_diff_sq (a₁ a₂ b₁ b₂ : ℝ) :
    (a₁ - b₁) ^ 2 - (a₂ - b₂) ^ 2 = ((a₁ + a₂) - (b₁ + b₂)) * ((a₁ - a₂) - (b₁ - b₂)) := by
  ring

/-- **The order of the §9.2 difference of squares** (Giles 2015, §9.2, p. 60: "Due to the Central
Limit Theorem, we have `Δg_{1,ℓ₂} + Δg_{1,ℓ₂−1} = O(2^{−ℓ₁/2})` … and assuming first order strong
convergence we also have `Δg_{1,ℓ₂} − Δg_{1,ℓ₂−1} = O(2^{−ℓ₁/2−ℓ₂})` … Combining these results we
obtain" the order `O(2^{−ℓ₁−ℓ₂})`).  If `|a₁ + a₂|, |b₁ + b₂| ≤ s` and `|a₁ − a₂|, |b₁ − b₂| ≤ t`,
then `|(a₁ − b₁)² − (a₂ − b₂)²| ≤ 4 s t`. -/
theorem abs_mimc_diff_sq_le {a₁ a₂ b₁ b₂ s t : ℝ} (ha : |a₁ + a₂| ≤ s) (hb : |b₁ + b₂| ≤ s)
    (ha' : |a₁ - a₂| ≤ t) (hb' : |b₁ - b₂| ≤ t) :
    |(a₁ - b₁) ^ 2 - (a₂ - b₂) ^ 2| ≤ 4 * s * t := by
  rw [mimc_diff_sq, abs_mul]
  obtain ⟨h1, h2⟩ := abs_le.1 ha
  obtain ⟨h3, h4⟩ := abs_le.1 hb
  obtain ⟨h5, h6⟩ := abs_le.1 ha'
  obtain ⟨h7, h8⟩ := abs_le.1 hb'
  have hs : |(a₁ + a₂) - (b₁ + b₂)| ≤ 2 * s := abs_le.2 ⟨by linarith, by linarith⟩
  have ht : |(a₁ - a₂) - (b₁ - b₂)| ≤ 2 * t := abs_le.2 ⟨by linarith, by linarith⟩
  have hs0 : 0 ≤ 2 * s := by linarith [abs_nonneg (a₁ + a₂)]
  calc |(a₁ + a₂) - (b₁ + b₂)| * |(a₁ - a₂) - (b₁ - b₂)| ≤ (2 * s) * (2 * t) :=
        mul_le_mul hs ht (abs_nonneg _) hs0
    _ = 4 * s * t := by ring

/-- **The §9.2 difference of squares is `O(2^{−ℓ₁−ℓ₂})`** (Giles 2015, §9.2, p. 60).  If
`|a₁ + a₂|, |b₁ + b₂| ≤ c 2^{−ℓ₁/2}` and `|a₁ − a₂|, |b₁ − b₂| ≤ c 2^{−ℓ₁/2−ℓ₂}`, then
`|(a₁ − b₁)² − (a₂ − b₂)²| ≤ 4 c² 2^{−ℓ₁−ℓ₂}`. -/
theorem abs_mimc_diff_sq_le_rpow {a₁ a₂ b₁ b₂ c ℓ₁ ℓ₂ : ℝ}
    (ha : |a₁ + a₂| ≤ c * (2 : ℝ) ^ (-(ℓ₁ / 2))) (hb : |b₁ + b₂| ≤ c * (2 : ℝ) ^ (-(ℓ₁ / 2)))
    (ha' : |a₁ - a₂| ≤ c * (2 : ℝ) ^ (-(ℓ₁ / 2) - ℓ₂))
    (hb' : |b₁ - b₂| ≤ c * (2 : ℝ) ^ (-(ℓ₁ / 2) - ℓ₂)) :
    |(a₁ - b₁) ^ 2 - (a₂ - b₂) ^ 2| ≤ 4 * c ^ 2 * (2 : ℝ) ^ (-ℓ₁ - ℓ₂) := by
  have h := abs_mimc_diff_sq_le ha hb ha' hb'
  have e : 4 * (c * (2 : ℝ) ^ (-(ℓ₁ / 2))) * (c * (2 : ℝ) ^ (-(ℓ₁ / 2) - ℓ₂)) =
      4 * c ^ 2 * (2 : ℝ) ^ (-ℓ₁ - ℓ₂) := by
    rw [show -ℓ₁ - ℓ₂ = -(ℓ₁ / 2) + (-(ℓ₁ / 2) - ℓ₂) by ring, Real.rpow_add two_pos]
    ring
  rwa [e] at h

/-! ### The exponents of §9.1 and §9.2 -/

/-- **The complexity of nested simulation with MLMC** (Giles 2015, §9.1, p. 58: "For the MLMC
theorem, this corresponds to `α = 1, β = 2, γ = 1`, so the complexity is `O(ε⁻²)`"; for Bujok et
al., "`β = 1.5`. However, this is still sufficiently large to achieve an overall complexity which
is `O(ε⁻²)`"; §9.2, p. 59: with `2^ℓ` timesteps as well "this would still give `α = 1, β = 2`.
However, we would now have `γ = 2` … This then leads to an overall MLMC complexity which is
`O(ε⁻²(log ε)⁻²)`"; p. 60: "if the function `f` is continuous and piecewise differentiable … in
the MLMC treatment we would get `β = 1.5`, and hence an overall complexity which is
`O(ε^{−2.5})`").  The bound of Theorem 1 (`complexityBound`) is `ε⁻²` for
`(α, β, γ) = (1, 2, 1)` and `(1, 1.5, 1)`, `ε⁻² (log ε)²` for `(1, 2, 2)` (the exponent of
`log ε` printed in the paper, `−2`, should be `2`), and `ε^{−2.5}` for `(1, 1.5, 2)`. -/
theorem nested_complexity (ε : ℝ) :
    complexityBound 1 2 1 ε = ε ^ (-2 : ℝ) ∧ complexityBound 1 1.5 1 ε = ε ^ (-2 : ℝ) ∧
      complexityBound 1 2 2 ε = ε ^ (-2 : ℝ) * Real.log ε ^ 2 ∧
      complexityBound 1 1.5 2 ε = ε ^ (-2.5 : ℝ) := by
  refine ⟨complexityBound_of_lt (by norm_num) ε, complexityBound_of_lt (by norm_num) ε,
    complexityBound_of_eq rfl ε, ?_⟩
  rw [complexityBound_of_gt (by norm_num) ε]
  congr 1
  norm_num

/-- **The complexity of nested simulation with MIMC** (Giles 2015, §9.2, p. 60: "In Theorem 2
this corresponds to `α₁ = α₂ = 1, β₁ = β₂ = 2`, and `γ₁ = γ₂ = 1`, so the overall complexity is
`O(ε⁻²)`"; "with MIMC we would have `β₁ = β₂ = 1.5` and so the complexity would remain
`O(ε⁻²)`").  For `D = 2`, `α = (1, 1)`, `γ = (1, 1)` and `β = (2, 2)` resp. `(1.5, 1.5)`, the
exponent of Theorem 2 is `η = max_d (γ_d − β_d)/α_d = −1` resp. `−½`, so the bound of Theorem 2
(`mimcBound`, in `giles_theorem2_boundary`, which allows `α_d = ½β_d`) is `ε⁻²` whatever the
logarithmic exponents `e₁`, `e₂`. -/
theorem nested_mimc_complexity (e₁ e₂ ε : ℝ) :
    mimcEta (D := 2) (fun _ => 1) (fun _ => 2) (fun _ => 1) = -1 ∧
      mimcEta (D := 2) (fun _ => 1) (fun _ => 1.5) (fun _ => 1) = -1 / 2 ∧
      mimcBound (mimcEta (D := 2) (fun _ => 1) (fun _ => 2) (fun _ => 1)) e₁ e₂ ε =
        ε ^ (-2 : ℝ) ∧
      mimcBound (mimcEta (D := 2) (fun _ => 1) (fun _ => 1.5) (fun _ => 1)) e₁ e₂ ε =
        ε ^ (-2 : ℝ) := by
  have h1 : mimcEta (D := 2) (fun _ => (1 : ℝ)) (fun _ => 2) (fun _ => 1) = -1 := by
    simp only [mimcEta, Finset.sup'_const]
    norm_num
  have h2 : mimcEta (D := 2) (fun _ => (1 : ℝ)) (fun _ => 1.5) (fun _ => 1) = -1 / 2 := by
    simp only [mimcEta, Finset.sup'_const]
    norm_num
  exact ⟨h1, h2, mimcBound_of_neg (by rw [h1]; norm_num),
    mimcBound_of_neg (by rw [h2]; norm_num)⟩

/-! ### Moments of sums of independent centred variables -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- On a finite measure space, the powers `Y^k`, `k ≤ 4`, of a measurable `Y` with `E[Y⁴] < ∞`
are integrable (Giles 2015, §9.1: the moments behind "`Δg = O(M^{−1/2})`"). -/
lemma integrable_pow_of_pow_four [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => Y ω ^ k) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add h4)
    (hY.pow_const k).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  show ‖Y ω ^ k‖ ≤ 1 + Y ω ^ 4
  rw [Real.norm_eq_abs, abs_pow]
  have ha : 0 ≤ |Y ω| := abs_nonneg _
  have e4 : |Y ω| ^ 4 = Y ω ^ 4 := by
    rw [← abs_pow]
    exact abs_of_nonneg (by positivity)
  rcases le_total (|Y ω|) 1 with h | h
  · have h1 : |Y ω| ^ k ≤ 1 := pow_le_one₀ ha h
    have h2 : 0 ≤ Y ω ^ 4 := by positivity
    linarith
  · have h1 : |Y ω| ^ k ≤ |Y ω| ^ 4 := pow_le_pow_right₀ h hk
    linarith

/-- **One step of the moment recursion** (Giles 2015, §9.1, the moments behind
"`Δg = O(M^{−1/2})`").  For independent `S` and `X` with `E[S] = E[X] = 0` and finite fourth
moments, `(S + X)⁴` is integrable, `E[(S + X)²] = E[S²] + E[X²]` and
`E[(S + X)⁴] = E[S⁴] + 6 E[S²] E[X²] + E[X⁴]`. -/
theorem moments_add_indep [IsProbabilityMeasure μ] {S X : Ω → ℝ} (hSX : IndepFun S X μ)
    (hSm : Measurable S) (hXm : Measurable X) (hS4 : Integrable (fun ω => S ω ^ 4) μ)
    (hX4 : Integrable (fun ω => X ω ^ 4) μ) (hS0 : ∫ ω, S ω ∂μ = 0) (hX0 : ∫ ω, X ω ∂μ = 0) :
    Integrable (fun ω => (S ω + X ω) ^ 4) μ ∧
      ∫ ω, (S ω + X ω) ^ 2 ∂μ = ∫ ω, S ω ^ 2 ∂μ + ∫ ω, X ω ^ 2 ∂μ ∧
      ∫ ω, (S ω + X ω) ^ 4 ∂μ =
        ∫ ω, S ω ^ 4 ∂μ + 6 * ((∫ ω, S ω ^ 2 ∂μ) * ∫ ω, X ω ^ 2 ∂μ) + ∫ ω, X ω ^ 4 ∂μ := by
  have p2 : Measurable fun x : ℝ => x ^ 2 := (continuous_pow 2).measurable
  have p3 : Measurable fun x : ℝ => x ^ 3 := (continuous_pow 3).measurable
  have hS1 : Integrable S μ := by
    simpa using integrable_pow_of_pow_four hSm hS4 (k := 1) (by norm_num)
  have hX1 : Integrable X μ := by
    simpa using integrable_pow_of_pow_four hXm hX4 (k := 1) (by norm_num)
  have hS2 : Integrable (fun ω => S ω ^ 2) μ := integrable_pow_of_pow_four hSm hS4 (by norm_num)
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := integrable_pow_of_pow_four hXm hX4 (by norm_num)
  have hS3 : Integrable (fun ω => S ω ^ 3) μ := integrable_pow_of_pow_four hSm hS4 (by norm_num)
  have hX3 : Integrable (fun ω => X ω ^ 3) μ := integrable_pow_of_pow_four hXm hX4 (by norm_num)
  -- the mixed moments are integrable and factorise
  have i11 : Integrable (fun ω => S ω * X ω) μ := hSX.integrable_mul hS1 hX1
  have i31 : Integrable (fun ω => S ω ^ 3 * X ω) μ :=
    (hSX.comp p3 measurable_id).integrable_mul hS3 hX1
  have i22 : Integrable (fun ω => S ω ^ 2 * X ω ^ 2) μ :=
    (hSX.comp p2 p2).integrable_mul hS2 hX2
  have i13 : Integrable (fun ω => S ω * X ω ^ 3) μ :=
    (hSX.comp measurable_id p3).integrable_mul hS1 hX3
  have e11 : ∫ ω, S ω * X ω ∂μ = (∫ ω, S ω ∂μ) * ∫ ω, X ω ∂μ :=
    hSX.integral_fun_mul_eq_mul_integral hS1.aestronglyMeasurable hX1.aestronglyMeasurable
  have e31 : ∫ ω, S ω ^ 3 * X ω ∂μ = (∫ ω, S ω ^ 3 ∂μ) * ∫ ω, X ω ∂μ :=
    (hSX.comp p3 measurable_id).integral_fun_mul_eq_mul_integral hS3.aestronglyMeasurable
      hX1.aestronglyMeasurable
  have e22 : ∫ ω, S ω ^ 2 * X ω ^ 2 ∂μ = (∫ ω, S ω ^ 2 ∂μ) * ∫ ω, X ω ^ 2 ∂μ :=
    (hSX.comp p2 p2).integral_fun_mul_eq_mul_integral hS2.aestronglyMeasurable
      hX2.aestronglyMeasurable
  have e13 : ∫ ω, S ω * X ω ^ 3 ∂μ = (∫ ω, S ω ∂μ) * ∫ ω, X ω ^ 3 ∂μ :=
    (hSX.comp measurable_id p3).integral_fun_mul_eq_mul_integral hS1.aestronglyMeasurable
      hX3.aestronglyMeasurable
  -- expand the powers
  have h2 : ∀ ω, (S ω + X ω) ^ 2 = S ω ^ 2 + 2 * (S ω * X ω) + X ω ^ 2 := fun ω => by ring
  have h4 : ∀ ω, (S ω + X ω) ^ 4 = S ω ^ 4 + 4 * (S ω ^ 3 * X ω) + 6 * (S ω ^ 2 * X ω ^ 2) +
      4 * (S ω * X ω ^ 3) + X ω ^ 4 := fun ω => by ring
  have j1 : Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * X ω)) μ := hS4.add (i31.const_mul 4)
  have j2 : Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * X ω) + 6 * (S ω ^ 2 * X ω ^ 2)) μ :=
    j1.add (i22.const_mul 6)
  have j3 : Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * X ω) + 6 * (S ω ^ 2 * X ω ^ 2) +
      4 * (S ω * X ω ^ 3)) μ := j2.add (i13.const_mul 4)
  have j4 : Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * X ω) + 6 * (S ω ^ 2 * X ω ^ 2) +
      4 * (S ω * X ω ^ 3) + X ω ^ 4) μ := j3.add hX4
  have k1 : Integrable (fun ω => S ω ^ 2 + 2 * (S ω * X ω)) μ := hS2.add (i11.const_mul 2)
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [h4]
    exact j4
  · simp_rw [h2]
    rw [integral_add k1 hX2, integral_add hS2 (i11.const_mul 2), integral_const_mul, e11, hS0]
    ring
  · simp_rw [h4]
    rw [integral_add j3 hX4, integral_add j2 (i13.const_mul 4), integral_add j1 (i22.const_mul 6),
      integral_add hS4 (i31.const_mul 4), integral_const_mul, integral_const_mul,
      integral_const_mul, e31, e22, e13, hS0, hX0]
    ring

/-- **Moments of a sum of independent centred variables** (Giles 2015, §9.1, p. 58: the paper's
"By the Central Limit Theorem, `Δg₁⁽ⁿ⁾, Δg₂⁽ⁿ⁾ = O(M_ℓ^{−1/2})`" made quantitative without the
Central Limit Theorem).  Let `X₀, X₁, …` be mutually independent and measurable with
`E[X_i] = 0`, `E[X_i²] = v` and `E[X_i⁴] ≤ q < ∞`.  Then for every `n`, `(∑_{i<n} X_i)⁴` is
integrable, `E[(∑_{i<n} X_i)²] = n v` and `E[(∑_{i<n} X_i)⁴] ≤ n q + 3 n² v²`. -/
theorem moments_sum_indep [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hind : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (hX4 : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (hX0 : ∀ i, ∫ ω, X i ω ∂μ = 0) {v q : ℝ} (hv : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = v)
    (hq : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ q) (n : ℕ) :
    Integrable (fun ω => (∑ i ∈ range n, X i ω) ^ 4) μ ∧
      ∫ ω, (∑ i ∈ range n, X i ω) ^ 2 ∂μ = n * v ∧
      ∫ ω, (∑ i ∈ range n, X i ω) ^ 4 ∂μ ≤ n * q + 3 * n ^ 2 * v ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hS4, hS2, hS4le⟩ := ih
    have hSm : Measurable fun ω => ∑ i ∈ range n, X i ω :=
      Finset.measurable_sum _ fun i _ => hXm i
    have hSX : IndepFun (fun ω => ∑ i ∈ range n, X i ω) (X n) μ := by
      have h := hind.indepFun_finsetSum_of_notMem hXm (Finset.notMem_range_self (n := n))
      convert h using 1
      funext ω
      simp only [Finset.sum_apply]
    have hX1 : ∀ i, Integrable (X i) μ := fun i => by
      simpa using integrable_pow_of_pow_four (hXm i) (hX4 i) (k := 1) (by norm_num)
    have hS0 : ∫ ω, ∑ i ∈ range n, X i ω ∂μ = 0 := by
      rw [integral_finsetSum _ fun i _ => hX1 i]
      simp [hX0]
    obtain ⟨h4, e2, e4⟩ := moments_add_indep hSX hSm (hXm n) hS4 (hX4 n) hS0 (hX0 n)
    simp only [Finset.sum_range_succ]
    refine ⟨h4, ?_, ?_⟩
    · rw [e2, hS2, hv n]
      push_cast
      ring
    · rw [e4, hS2, hv n]
      have hqn := hq n
      push_cast
      nlinarith [sq_nonneg v]

end Moments

end MLMC
