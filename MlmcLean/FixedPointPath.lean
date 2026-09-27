import MlmcLean.RoundingError
import Mathlib.Probability.Independence.Integration

/-!
# Haas–Giles §4.1 and §6.3: the GBM path of Algorithm 1, the size of its variables, and the
accumulation of rounding errors

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), (13) (§2, p. 4), Algorithm 1 (§4.1, p. 8) and §6.3 (pp. 13–14).

* **Algorithm 1** decomposes a time step of the geometric Brownian motion path into the elementary
  operations `con1 ← r × h`, `con2 ← √h × σ`, `mul1_i ← con2 × Z̃_i`, `sum1_i ← con1 + mul1_i`,
  `mul2_i ← S_i × sum1_i`, `S_{i+1} ← S_i + mul2_i` (`gbmStep`).  It computes the step (13) with
  `a(S, t) = rS`, `b(S, t) = σS` (`gbmStep_eq`), so the path is
  `S_n = S_0 ∏_{i<n} (1 + sum1_i)` (`gbmPath_eq_prod`).
* **(39)–(41)** (§6.3, p. 13: "assume that `h ≪ √h` and `σ, r, S_0, Z_i = O(1)`, then we obtain
  `con2, mul1, sum1, mul2 ∼ √h` (39), `con1 ∼ h` (40), `S ∼ 1` (41)").  With independent
  increments `Z̃_i` of mean 0 and second moment at most 1 (normal increments, or the approximate
  normals of §3) and `0 ≤ h ≤ 1`: `|con1| = |r| h` and `|con2| = |σ| √h` (`abs_con1_con2`), and in
  mean square `E[mul1_i²] ≤ σ² h`, `E[sum1_i²] ≤ (r² + σ²) h`, `E[S_n²] ≤ S_0² e^{c n h}` and
  `E[mul2_i²] ≤ S_0² e^{c i h} (r² + σ²) h`, where `c = 2|r| + r² + σ²` (`integral_sq_mul1_le`,
  `integral_sq_sum1_le`, `integral_sq_gbmPath_le`, `integral_sq_mul2_le`).  Over a time horizon
  `nh = T` these are `O(h)`, `O(h)`, `O(1)` and `O(h)`.
* **The accumulation of rounding errors** (§6.3, p. 14: "in the fixed precision case the rounding
  error at each time step of the Euler-Maruyama scheme is of order `O(h⁻¹ 2^{e_{S,ℓ} − d_{S,ℓ}})`").
  A path with local errors `ρ_k`, `S̃_{k+1} = S̃_k (1 + sum1_k) + ρ_k`, differs from the exact path
  by `∑_k ρ_k ∏_{k<j<n} (1 + sum1_j)` (`perturbed_sub_eq`, `abs_perturbed_sub_le`).  If
  `|ρ_k| ≤ u`, then `E|S̃_n − S_n| ≤ u n e^{c n h}` (`integral_abs_perturbed_sub_le`).  So with
  `n = T/h` steps and `S` rounded to nearest in its fixed-point format after every step
  (`u = 2^{e−d−1}`, (20)), `E|S̃_N − S_N| ≤ (T/h) 2^{e−d−1} e^{cT}`
  (`integral_abs_roundFixed_path_sub_le`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### Algorithm 1 -/

/-- **Haas–Giles (2025), §4.1, p. 8, Algorithm 1**: one time step of the geometric Brownian motion
path, "decomposed in elementary operations to show the intermediary fixed-point variables":
`con1 ← r × h`, `con2 ← √h × σ`, `mul1_i ← con2 × Z̃_i`, `sum1_i ← con1 + mul1_i`,
`mul2_i ← S_i × sum1_i`, `S_{i+1} ← S_i + mul2_i` (here in exact arithmetic). -/
noncomputable def gbmStep (r σ h S Z : ℝ) : ℝ :=
  let con1 := r * h
  let con2 := Real.sqrt h * σ
  let mul1 := con2 * Z
  let sum1 := con1 + mul1
  let mul2 := S * sum1
  S + mul2

/-- **Algorithm 1 computes the step (13)** (Haas–Giles 2025, §4.1, p. 8: "This algorithm details how
we decomposed the operations to compute each time step from (13)"): with the drift `a(S, t) = rS`
and the volatility `b(S, t) = σS` of geometric Brownian motion,
`S̃_{i+1} = S̃_i + a(S̃_i, t_i) h + b(S̃_i, t_i) √h Z̃_i` (13). -/
theorem gbmStep_eq (r σ h S Z : ℝ) :
    gbmStep r σ h S Z = S + r * S * h + σ * S * Real.sqrt h * Z := by
  simp only [gbmStep]
  ring

/-- The path of Algorithm 1 (Haas–Giles 2025, §4.1): `S_0 = s₀` and `S_{i+1}` is one step of
`gbmStep` from `S_i` with the increment `Z̃_i = Z i`. -/
noncomputable def gbmPath (r σ h s₀ : ℝ) (Z : ℕ → ℝ) : ℕ → ℝ
  | 0 => s₀
  | i + 1 => gbmStep r σ h (gbmPath r σ h s₀ Z i) (Z i)

/-- One step of Algorithm 1 multiplies `S_i` by `1 + sum1_i = 1 + rh + √h σ Z̃_i`. -/
theorem gbmPath_succ (r σ h s₀ : ℝ) (Z : ℕ → ℝ) (i : ℕ) :
    gbmPath r σ h s₀ Z (i + 1) =
      gbmPath r σ h s₀ Z i * (1 + r * h + Real.sqrt h * σ * Z i) := by
  rw [show gbmPath r σ h s₀ Z (i + 1) = gbmStep r σ h (gbmPath r σ h s₀ Z i) (Z i) from rfl,
    gbmStep_eq]
  ring

/-- **The path of Algorithm 1 as a product** (Haas–Giles 2025, §4.1):
`S_n = S_0 ∏_{i<n} (1 + rh + √h σ Z̃_i)`. -/
theorem gbmPath_eq_prod (r σ h s₀ : ℝ) (Z : ℕ → ℝ) (n : ℕ) :
    gbmPath r σ h s₀ Z n = s₀ * ∏ i ∈ range n, (1 + r * h + Real.sqrt h * σ * Z i) := by
  induction n with
  | zero => simp [gbmPath]
  | succ n ih =>
    rw [gbmPath_succ, ih, Finset.prod_range_succ]
    ring

/-! ### The size of the variables: (39)–(41) -/

/-- **Haas–Giles (2025), §6.3, p. 13, (40) and (39) for the constants**: `con1 = r × h` has size
`|r| h` ("`con1 ∼ h`" (40)) and `con2 = √h × σ` has size `|σ| √h` ("`con2 ∼ √h`" (39)). -/
theorem abs_con1_con2 {r σ h : ℝ} (hh : 0 ≤ h) :
    |r * h| = |r| * h ∧ |Real.sqrt h * σ| = |σ| * Real.sqrt h := by
  refine ⟨by rw [abs_mul, abs_of_nonneg hh], ?_⟩
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg h), mul_comm]

section size

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The second moment of an affine function of a centred variable of second moment at most 1:
`E[(a + bY)²] ≤ a² + b²`. -/
lemma integral_sq_affine_le {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (hmean : ∫ ω, Y ω ∂μ = 0)
    (hvar : ∫ ω, Y ω ^ 2 ∂μ ≤ 1) (a b : ℝ) :
    ∫ ω, (a + b * Y ω) ^ 2 ∂μ ≤ a ^ 2 + b ^ 2 := by
  have hint : Integrable Y μ := hY.integrable one_le_two
  have hi1 : Integrable (fun ω => 2 * a * b * Y ω) μ := hint.const_mul _
  have hi2 : Integrable (fun ω => b ^ 2 * Y ω ^ 2) μ := hY.integrable_sq.const_mul _
  have hi12 : Integrable (fun ω => 2 * a * b * Y ω + b ^ 2 * Y ω ^ 2) μ := hi1.add hi2
  have hexp : (fun ω => (a + b * Y ω) ^ 2) =
      fun ω => a ^ 2 + (2 * a * b * Y ω + b ^ 2 * Y ω ^ 2) := by
    funext ω
    ring
  rw [hexp, integral_add (integrable_const _) hi12, integral_add hi1 hi2, integral_const,
    integral_const_mul, integral_const_mul, hmean]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, zero_add]
  linarith [mul_le_mul_of_nonneg_left hvar (sq_nonneg b)]

omit [IsProbabilityMeasure μ] in
/-- **Haas–Giles (2025), §6.3, p. 13, (39) for `mul1`**: "`mul1 ∼ √h`".  If the increment `Y = Z̃_i`
has second moment at most 1, then `mul1_i = √h σ Z̃_i` has `E[mul1_i²] ≤ σ² h` (for any measure). -/
theorem integral_sq_mul1_le {Y : Ω → ℝ} (hvar : ∫ ω, Y ω ^ 2 ∂μ ≤ 1) {σ h : ℝ} (hh : 0 ≤ h) :
    ∫ ω, (Real.sqrt h * σ * Y ω) ^ 2 ∂μ ≤ σ ^ 2 * h := by
  have e : (fun ω => (Real.sqrt h * σ * Y ω) ^ 2) = fun ω => σ ^ 2 * h * Y ω ^ 2 := by
    funext ω
    rw [show (Real.sqrt h * σ * Y ω) ^ 2 = Real.sqrt h ^ 2 * σ ^ 2 * Y ω ^ 2 by ring,
      Real.sq_sqrt hh]
    ring
  rw [e, integral_const_mul]
  exact mul_le_of_le_one_right (mul_nonneg (sq_nonneg σ) hh) hvar

/-- **Haas–Giles (2025), §6.3, p. 13, (39) for `sum1`**: "`sum1 ∼ √h`" (using `h ≪ √h`).  If the
increment `Y = Z̃_i` has mean 0 and second moment at most 1 and `0 ≤ h ≤ 1`, then
`sum1_i = rh + √h σ Z̃_i` has `E[sum1_i²] ≤ (r² + σ²) h`. -/
theorem integral_sq_sum1_le {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (hmean : ∫ ω, Y ω ∂μ = 0)
    (hvar : ∫ ω, Y ω ^ 2 ∂μ ≤ 1) {r σ h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    ∫ ω, (r * h + Real.sqrt h * σ * Y ω) ^ 2 ∂μ ≤ (r ^ 2 + σ ^ 2) * h := by
  have h1 := integral_sq_affine_le hY hmean hvar (r * h) (Real.sqrt h * σ)
  rw [mul_pow, mul_pow, Real.sq_sqrt hh0] at h1
  have h2 : r ^ 2 * h ^ 2 ≤ r ^ 2 * h :=
    mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg r)
  linarith

/-- The second moment of one factor `1 + sum1_i` of the path: for `0 ≤ h ≤ 1`,
`E[(1 + rh + √h σ Z̃_i)²] ≤ e^{(2|r| + r² + σ²) h}`. -/
lemma integral_sq_factor_le {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (hmean : ∫ ω, Y ω ∂μ = 0)
    (hvar : ∫ ω, Y ω ^ 2 ∂μ ≤ 1) {r σ h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    ∫ ω, (1 + r * h + Real.sqrt h * σ * Y ω) ^ 2 ∂μ ≤
      Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * h) := by
  have h1 := integral_sq_affine_le hY hmean hvar (1 + r * h) (Real.sqrt h * σ)
  rw [mul_pow, Real.sq_sqrt hh0] at h1
  have hr : r * h ≤ |r| * h := mul_le_mul_of_nonneg_right (le_abs_self r) hh0
  have hr2 : r ^ 2 * h ^ 2 ≤ r ^ 2 * h :=
    mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg r)
  have h2 : (1 + r * h) ^ 2 + h * σ ^ 2 ≤ (2 * |r| + r ^ 2 + σ ^ 2) * h + 1 := by nlinarith
  exact h1.trans (h2.trans (Real.add_one_le_exp _))

/-- The product of the second moments of the factors over `n` steps: for `0 ≤ h ≤ 1`,
`∏_{i<n} E[(1 + rh + √h σ Z̃_i)²] ≤ e^{(2|r| + r² + σ²) n h}`. -/
lemma prod_integral_sq_factor_le {Z : ℕ → Ω → ℝ} (hZ2 : ∀ i, MemLp (Z i) 2 μ)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ 1) {r σ h : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (s : Finset ℕ) :
    ∏ i ∈ s, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z i ω) ^ 2 ∂μ ≤
      Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * (s.card * h)) := by
  calc ∏ i ∈ s, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z i ω) ^ 2 ∂μ
      ≤ ∏ _i ∈ s, Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * h) :=
        Finset.prod_le_prod (fun i _ => integral_nonneg fun ω => sq_nonneg _)
          fun i _ => integral_sq_factor_le (hZ2 i) (hmean i) (hvar i) hh0 hh1
    _ = Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * (s.card * h)) := by
        rw [Finset.prod_const, ← Real.exp_nat_mul,
          show (s.card : ℝ) * ((2 * |r| + r ^ 2 + σ ^ 2) * h) =
            (2 * |r| + r ^ 2 + σ ^ 2) * (s.card * h) by ring]

/-- The mean of a product of independent real random variables is the product of the means. -/
lemma integral_prod_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (s : Finset ι) :
    ∫ ω, ∏ i ∈ s, X i ω ∂μ = ∏ i ∈ s, ∫ ω, X i ω ∂μ := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  have hind : IndepFun (X i) (fun ω => ∏ j ∈ s, X j ω) μ := by
    have h := (hX.indepFun_finsetProd_of_notMem hm hi).symm
    have e : (∏ j ∈ s, X j) = fun ω => ∏ j ∈ s, X j ω := by
      funext ω
      exact Finset.prod_apply ω s X
    rwa [e] at h
  rw [Finset.prod_insert hi, ← ih]
  simp only [Finset.prod_insert hi]
  exact hind.integral_fun_mul_eq_mul_integral (hm i).aestronglyMeasurable
    (Finset.measurable_prod s fun j _ => hm j).aestronglyMeasurable

/-- A product of independent integrable real random variables is integrable. -/
lemma integrable_prod_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (hi : ∀ i, Integrable (X i) μ) (s : Finset ι) :
    Integrable (fun ω => ∏ i ∈ s, X i ω) μ := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s his ih
  have hind : IndepFun (X i) (fun ω => ∏ j ∈ s, X j ω) μ := by
    have h := (hX.indepFun_finsetProd_of_notMem hm his).symm
    have e : (∏ j ∈ s, X j) = fun ω => ∏ j ∈ s, X j ω := by
      funext ω
      exact Finset.prod_apply ω s X
    rwa [e] at h
  refine (hind.integrable_mul (hi i) ih).congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.mul_apply, Finset.prod_insert his]

variable {Z : ℕ → Ω → ℝ}

/-- The second moment of the path of Algorithm 1 with independent increments: `E[S_n²]` is `S_0²`
times the product of the second moments of the factors `1 + sum1_i`. -/
lemma integral_sq_gbmPath_eq (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i)) (r σ h s₀ : ℝ)
    (n : ℕ) :
    ∫ ω, gbmPath r σ h s₀ (fun i => Z i ω) n ^ 2 ∂μ =
      s₀ ^ 2 * ∏ i ∈ range n, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z i ω) ^ 2 ∂μ := by
  have hg : Measurable fun z : ℝ => (1 + r * h + Real.sqrt h * σ * z) ^ 2 := by fun_prop
  have hWm : ∀ i, Measurable fun ω => (1 + r * h + Real.sqrt h * σ * Z i ω) ^ 2 :=
    fun i => hg.comp (hm i)
  have hWind : iIndepFun (fun i ω => (1 + r * h + Real.sqrt h * σ * Z i ω) ^ 2) μ :=
    hZ.comp _ fun _ => hg
  have hsq : ∀ ω, gbmPath r σ h s₀ (fun i => Z i ω) n ^ 2 =
      s₀ ^ 2 * ∏ i ∈ range n, (1 + r * h + Real.sqrt h * σ * Z i ω) ^ 2 := by
    intro ω
    rw [gbmPath_eq_prod, mul_pow, Finset.prod_pow]
  simp_rw [hsq]
  rw [integral_const_mul, integral_prod_of_iIndepFun hWind hWm]

/-- **Haas–Giles (2025), §6.3, p. 13, (41)**: "`S ∼ 1`".  With independent increments `Z̃_i` of
mean 0 and second moment at most 1 and `0 ≤ h ≤ 1`, the path of Algorithm 1 has
`E[S_n²] ≤ S_0² e^{(2|r| + r² + σ²) n h}`, which is bounded over a fixed horizon `nh ≤ T`. -/
theorem integral_sq_gbmPath_le (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ 1) {r σ h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (s₀ : ℝ)
    (n : ℕ) :
    ∫ ω, gbmPath r σ h s₀ (fun i => Z i ω) n ^ 2 ∂μ ≤
      s₀ ^ 2 * Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * (n * h)) := by
  rw [integral_sq_gbmPath_eq hZ hm]
  have h := prod_integral_sq_factor_le hZ2 hmean hvar hh0 hh1 (range n) (r := r) (σ := σ)
  rw [Finset.card_range] at h
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- **Haas–Giles (2025), §6.3, p. 13, (39) for `mul2`**: "`mul2 ∼ √h`".  With independent
increments `Z̃_i` of mean 0 and second moment at most 1 and `0 ≤ h ≤ 1`,
`mul2_i = S_i × sum1_i` has `E[mul2_i²] ≤ S_0² e^{(2|r| + r² + σ²) i h} (r² + σ²) h`. -/
theorem integral_sq_mul2_le (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ 1) {r σ h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (s₀ : ℝ)
    (i : ℕ) :
    ∫ ω, (gbmPath r σ h s₀ (fun j => Z j ω) i * (r * h + Real.sqrt h * σ * Z i ω)) ^ 2 ∂μ ≤
      s₀ ^ 2 * (Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * (i * h)) * ((r ^ 2 + σ ^ 2) * h)) := by
  obtain ⟨g, hg_def⟩ : ∃ g : ℕ → ℝ → ℝ, g = fun j z =>
      if j < i then (1 + r * h + Real.sqrt h * σ * z) ^ 2 else (r * h + Real.sqrt h * σ * z) ^ 2 :=
    ⟨_, rfl⟩
  have hgm : ∀ j, Measurable (g j) := by
    intro j
    rw [hg_def]
    by_cases hj : j < i
    · simp only [hj, ↓reduceIte]
      fun_prop
    · simp only [hj, ↓reduceIte]
      fun_prop
  have hGind : iIndepFun (fun j ω => g j (Z j ω)) μ := hZ.comp g hgm
  have hGm : ∀ j, Measurable fun ω => g j (Z j ω) := fun j => (hgm j).comp (hm j)
  have hlt : ∀ j ∈ range i, ∀ z, g j z = (1 + r * h + Real.sqrt h * σ * z) ^ 2 := by
    intro j hj z
    rw [hg_def]
    exact if_pos (Finset.mem_range.1 hj)
  have hself : ∀ z, g i z = (r * h + Real.sqrt h * σ * z) ^ 2 := by
    intro z
    rw [hg_def]
    exact if_neg (lt_irrefl i)
  have hprod : ∀ ω,
      (gbmPath r σ h s₀ (fun j => Z j ω) i * (r * h + Real.sqrt h * σ * Z i ω)) ^ 2 =
        s₀ ^ 2 * ∏ j ∈ range (i + 1), g j (Z j ω) := by
    intro ω
    rw [Finset.prod_range_succ, hself, Finset.prod_congr rfl fun j hj => hlt j hj (Z j ω),
      Finset.prod_pow, gbmPath_eq_prod]
    ring
  have hfac : ∫ ω, (r * h + Real.sqrt h * σ * Z i ω) ^ 2 ∂μ ≤ (r ^ 2 + σ ^ 2) * h :=
    integral_sq_sum1_le (hZ2 i) (hmean i) (hvar i) hh0 hh1
  have hP := prod_integral_sq_factor_le hZ2 hmean hvar hh0 hh1 (range i) (r := r) (σ := σ)
  rw [Finset.card_range] at hP
  simp_rw [hprod]
  rw [integral_const_mul, integral_prod_of_iIndepFun hGind hGm, Finset.prod_range_succ,
    Finset.prod_congr rfl fun j hj =>
      integral_congr_ae (Filter.Eventually.of_forall fun ω => hlt j hj (Z j ω)),
    integral_congr_ae (Filter.Eventually.of_forall fun ω => hself (Z i ω))]
  refine mul_le_mul_of_nonneg_left (mul_le_mul hP hfac (integral_nonneg fun ω => sq_nonneg _)
    (Real.exp_pos _).le) (sq_nonneg _)

end size

/-! ### The accumulation of rounding errors (§6.3) -/

/-- **The error of a perturbed product recursion** (Haas–Giles 2025, §6.3): if the exact path
satisfies `S_{k+1} = S_k m_k` and the perturbed one `S̃_{k+1} = S̃_k m_k + ρ_k` with `S̃_0 = S_0`,
then `S̃_n − S_n = ∑_{k<n} ρ_k ∏_{k<j<n} m_j`: each local error is propagated by the later
multipliers. -/
theorem perturbed_sub_eq (m ρ S St : ℕ → ℝ) (hS : ∀ k, S (k + 1) = S k * m k)
    (hSt : ∀ k, St (k + 1) = St k * m k + ρ k) (h0 : St 0 = S 0) (n : ℕ) :
    St n - S n = ∑ k ∈ range n, ρ k * ∏ j ∈ Ico (k + 1) n, m j := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hsum : ∑ k ∈ range n, ρ k * ∏ j ∈ Ico (k + 1) (n + 1), m j =
        (∑ k ∈ range n, ρ k * ∏ j ∈ Ico (k + 1) n, m j) * m n := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.prod_Ico_succ_top (Finset.mem_range.1 hk)]
      ring
    rw [hSt, hS, Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one, hsum, ← ih]
    ring

/-- **The accumulated error is at most the sum of the propagated local errors** (Haas–Giles 2025,
§6.3): if every local error satisfies `|ρ_k| ≤ u`, then
`|S̃_n − S_n| ≤ u ∑_{k<n} |∏_{k<j<n} m_j|`. -/
theorem abs_perturbed_sub_le (m ρ S St : ℕ → ℝ) (hS : ∀ k, S (k + 1) = S k * m k)
    (hSt : ∀ k, St (k + 1) = St k * m k + ρ k) (h0 : St 0 = S 0) {u : ℝ}
    (hρ : ∀ k, |ρ k| ≤ u) (n : ℕ) :
    |St n - S n| ≤ u * ∑ k ∈ range n, |∏ j ∈ Ico (k + 1) n, m j| := by
  rw [perturbed_sub_eq m ρ S St hS hSt h0 n, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hρ k) (abs_nonneg _)

section accumulation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Z : ℕ → Ω → ℝ}

/-- **Haas–Giles (2025), §6.3, p. 14: rounding errors accumulate like `O(h⁻¹ 2^{e−d})`.**  Let the
increments `Z̃_i` be independent, of mean 0 and second moment at most 1, and `0 ≤ h ≤ 1`.  Let `S̃`
be a path of Algorithm 1 perturbed at every step by an error of size at most `u`,
`S̃_{k+1} = S̃_k (1 + rh + √h σ Z̃_k) + ρ_k`, `|ρ_k| ≤ u`, `S̃_0 = S_0`.  Then after `n` steps
`E|S̃_n − S_n| ≤ u n e^{(2|r| + r² + σ²) n h}`: the error grows linearly in the number
`n = T/h` of time steps. -/
theorem integral_abs_perturbed_sub_le (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ 1) {r σ h u : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hu : 0 ≤ u) (s₀ : ℝ) (St ρ : ℕ → Ω → ℝ) (hSt0 : ∀ ω, St 0 ω = s₀)
    (hSt : ∀ k ω, St (k + 1) ω = St k ω * (1 + r * h + Real.sqrt h * σ * Z k ω) + ρ k ω)
    (hρ : ∀ k ω, |ρ k ω| ≤ u) (n : ℕ) :
    ∫ ω, |St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n| ∂μ ≤
      u * n * Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * (n * h)) := by
  have hg : Measurable fun z : ℝ => (1 + r * h + Real.sqrt h * σ * z) ^ 2 := by fun_prop
  have hWm : ∀ j, Measurable fun ω => (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 :=
    fun j => hg.comp (hm j)
  have hWind : iIndepFun (fun j ω => (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2) μ :=
    hZ.comp _ fun _ => hg
  have hWi : ∀ j, Integrable (fun ω => (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2) μ :=
    fun j => ((memLp_const (1 + r * h)).add ((hZ2 j).const_mul (Real.sqrt h * σ))).integrable_sq
  have hPi : ∀ k, Integrable
      (fun ω => ∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2) μ :=
    fun k => integrable_prod_of_iIndepFun hWind hWm hWi _
  have hc0 : 0 ≤ (2 * |r| + r ^ 2 + σ ^ 2) * (n * h) :=
    mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg n) hh0)
  have hPmean : ∀ k, ∫ ω, ∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ ≤
      Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * (n * h)) := by
    intro k
    rw [integral_prod_of_iIndepFun hWind hWm]
    refine (prod_integral_sq_factor_le hZ2 hmean hvar hh0 hh1 _).trans
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by positivity)))
    rw [Nat.card_Ico]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n (k + 1)) hh0
  have hpt : ∀ ω, |St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n| ≤
      u * ∑ k ∈ range n,
        (1 + ∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2) / 2 := by
    intro ω
    refine (abs_perturbed_sub_le (fun k => 1 + r * h + Real.sqrt h * σ * Z k ω)
      (fun k => ρ k ω) (fun k => gbmPath r σ h s₀ (fun j => Z j ω) k) (fun k => St k ω)
      (fun k => gbmPath_succ r σ h s₀ _ k) (fun k => hSt k ω) (by simp [hSt0, gbmPath])
      (fun k => hρ k ω) n).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hu
    rw [Finset.prod_pow]
    nlinarith [sq_nonneg (|∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω)| - 1),
      sq_abs (∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω))]
  have hterm : ∀ k ∈ range n, Integrable
      (fun ω => (1 + ∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2) / 2) μ :=
    fun k _ => ((integrable_const 1).add (hPi k)).div_const 2
  have hgi : Integrable (fun ω => u * ∑ k ∈ range n,
      (1 + ∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2) / 2) μ :=
    (integrable_finsetSum _ hterm).const_mul u
  calc ∫ ω, |St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n| ∂μ
      ≤ ∫ ω, u * ∑ k ∈ range n,
          (1 + ∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2) / 2 ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _) hgi
          (Filter.Eventually.of_forall hpt)
    _ = u * ∑ k ∈ range n,
          (1 + ∫ ω, ∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ) / 2 := by
        rw [integral_const_mul, integral_finsetSum _ hterm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_div, integral_add (integrable_const 1) (hPi k), integral_const, probReal_univ,
          one_smul]
    _ ≤ u * ∑ _k ∈ range n, Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * (n * h)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hu
        have h1 := hPmean k
        have h2 := Real.one_le_exp hc0
        linarith
    _ = u * n * Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * (n * h)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- **Haas–Giles (2025), §6.3, p. 14, in fixed-point arithmetic**: "in the fixed precision case the
rounding error at each time step of the Euler-Maruyama scheme is of order
`O(h⁻¹ 2^{e_{S,ℓ} − d_{S,ℓ}})`".  If the path of Algorithm 1 rounds `S` to nearest in the
fixed-point format with exponent `e` and bit-width `d` after every step (`roundFixed`, error at
most `2^{e−d−1}` by (20)), then after `n = T/h` steps (`0 < h ≤ 1`), with independent increments of
mean 0 and second moment at most 1,
`E|S̃_n − S_n| ≤ (T/h) 2^{e−d−1} e^{(2|r| + r² + σ²) T}`. -/
theorem integral_abs_roundFixed_path_sub_le (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ 1) {r σ h T : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (s₀ : ℝ)
    (e : ℤ) (d : ℕ) (St : ℕ → Ω → ℝ) (hSt0 : ∀ ω, St 0 ω = s₀)
    (hSt : ∀ k ω, St (k + 1) ω = roundFixed e d (gbmStep r σ h (St k ω) (Z k ω))) {n : ℕ}
    (hT : (n : ℝ) * h = T) :
    ∫ ω, |St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n| ∂μ ≤
      T / h * (2 : ℝ) ^ (e - d - 1) * Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * T) := by
  have hSt' : ∀ k ω, St (k + 1) ω = St k ω * (1 + r * h + Real.sqrt h * σ * Z k ω) +
      (St (k + 1) ω - St k ω * (1 + r * h + Real.sqrt h * σ * Z k ω)) := fun k ω => by ring
  have hρ : ∀ k ω, |St (k + 1) ω - St k ω * (1 + r * h + Real.sqrt h * σ * Z k ω)| ≤
      (2 : ℝ) ^ (e - d - 1) := by
    intro k ω
    have hstep : St k ω * (1 + r * h + Real.sqrt h * σ * Z k ω) =
        gbmStep r σ h (St k ω) (Z k ω) := by
      rw [gbmStep_eq]
      ring
    rw [hSt k ω, hstep, abs_sub_comm]
    exact abs_sub_roundFixed_le e d _
  have hacc := integral_abs_perturbed_sub_le hZ hm hZ2 hmean hvar hh0.le hh1
    (zpow_pos two_pos _).le s₀ St _ hSt0 hSt' hρ n
  have hn : (n : ℝ) = T / h := by
    rw [← hT, mul_div_cancel_right₀ _ hh0.ne']
  rw [hT, hn] at hacc
  exact hacc.trans_eq (by ring)

end accumulation

end MLMC
