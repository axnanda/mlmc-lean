import MlmcLean.GBMPathDependent
import MlmcLean.ApplicationExtras
import MlmcLean.BrownianPaths

/-!
# Jump processes: exponential Lévy Asian options, jump-adapted grids, thinning (Giles 2015, §6)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §6.1
"Jump-diffusion processes" (p. 47) and §6.2 "More general processes" (pp. 47–48, Table 6.3).  Line
numbers refer to the text `docs/giles2015.txt` (coverage rows G6-02, G6-05 and G6-09).  No Lévy–Itô
theory is needed: everything concerns the values of the processes on the time grids.

**§6.2, Table 6.3, the Asian row** (l. 2057: "Asian O(h²) O(h²) O(h²)" for the Variance-Gamma, NIG
and spectrally negative α-stable processes; l. 2060: "convergence rates for the multilevel variance
`V_ℓ ≡ V[P_ℓ − P_{ℓ−1}]`"; l. 2063–2064: "directly simulate the increments of the Lévy process over
a set of uniform timesteps"; l. 2078–2079: "the increments of the driving Lévy process for the
coarse path can be obtained trivially by summing the increments for the fine path").  The log-price
on the fine grid is `X_k = Y_0 + ⋯ + Y_{k−1}` (`levyPath`), with independent increments `Y_i` over
one fine step `h`; the only assumptions on their laws are the exponential moments of an exponential
Lévy model, `E e^{Y_i} = e^{hκ₁}` and `E e^{2Y_i} = e^{hκ₂}` (`κ₁ = ψ(1)`, `κ₂ = ψ(2)` for the
Laplace exponent `ψ`); they need not be identically distributed.  The price is `S_k = s₀ e^{X_k}`,
and the Asian payoff `g(A)` uses the trapezoidal average `A_N = N⁻¹ ∑_{k<N} (S_k + S_{k+1})/2` over
`N` steps (`levyAsianTrap`): the fine average over the `2n` fine steps, the coarse one over the `n`
coarse steps of the same path, whose increments are the pair sums `Y_{2j} + Y_{2j+1}`
(`levyPairSum`).
* `levyAsianTrap_sub`: `A^f − A^c = s₀/(2n) ∑_{j<n} e^{X_{2j}} D(Y_{2j}, Y_{2j+1})` with
  `D(a, b) = e^a − (1 + e^{a+b})/2` (`levyTrapPair`), the midpoint value minus the mean of the
  endpoint values on each coarse step.
* `levyPairDiffSum_moments`: by the recursion `G_{n+1} = D(Y_0, Y_1) + e^{Y_0+Y_1} G_n(Y_2, Y_3, …)`
  and independence, `E[G_{n+1}] = d₁ + u² E[G_n]` and `E[G_{n+1}²] = d₂ + 2c E[G_n] + v² E[G_n²]`
  (`u = e^{hκ₁}`, `v = e^{hκ₂}`), where `d₁ = −(u − 1)²/2` and `c = −(u − v)²/2` are `O(h²)` and
  `d₂ = O(h)`: the steps have small means and orthogonal fluctuations.
* `levy_asian_avg_sq_le`, `levy_asian_payoff_sq_le`: **`E[(g(A^f) − g(A^c))²] ≤ K² s₀² C h²`** for a
  `K`-Lipschitz `g` (the correction is in `L²`), with an explicit `C = levyAsianConst κ₁ κ₂ T`,
  `T = 2nh`: `V_ℓ = O(h_ℓ²)`, `β = 2`.  This is the multilevel correction of the trapezoidal Asian
  payoff with exact increments.
* `levy_asian_theorem1`: **Theorem 1 end to end** for level laws `ν_ℓ` with
  `ν_{ℓ+1} ∗ ν_{ℓ+1} = ν_ℓ` (the laws of the increments of a Lévy process over `h_ℓ = T 2^{−ℓ}`, for
  any horizon `T > 0`; this gives (2.4)) and `∫ e^{2x} dν_0 < ∞`: the level expectations converge to
  some `P` at the rate `|E[P_ℓ] − P| ≤ c 2^{−ℓ}` (`α = 1`, from `β = 2`), and the MLMC estimator of
  `P` has mean square error `< ε²` at cost `O(ε⁻²)` (`β = 2 > γ = 1`).
* `jumpDiffLaw_conv`, `jumpDiffusion_asian_theorem1`: the same for the exponential jump-diffusion
  `X_t = bt + σW_t + aN_t` (`N` Poisson, constant jump size `a`) with its increments over uniform
  steps simulated exactly (the §6.2 approach, not the jump-adapted discretisation of §6.1); all
  hypotheses of `levy_asian_theorem1` are proved (`jumpDiffLaw_conv`,
  `integral_exp_mul_jumpDiffLaw`): a model with jumps where Theorem 1 holds with no assumption at
  all.

The discrete-time aspect: the paper's Asian option averages `S` continuously over `[0, T]`, which
involves the Lévy process between the grid points.  With the trapezoidal approximation of the
average used here (the paper does not say which quadrature its references use), the correction
`P_ℓ − P_{ℓ−1}` only involves grid values; the target of Theorem 1 is the limit of the level
expectations (for a càdlàg Lévy process it is `E[g(T⁻¹ ∫₀ᵀ S_t dt)]`, which is not proved here).  A
numerical check (Gaussian, Poisson and Merton-type increments; the exact value of `E[(A^f − A^c)²]`
from a moment recursion and from a double sum, and Monte Carlo) gives `E[(A^f − A^c)²]/h²` constant
in `h`, so the order `h²` is sharp.  The constant `C` is not: it grows like
`e^{6T(|κ₁| + |κ₂|)}` and can exceed the exact value of `E[(A^f − A^c)²]/(s₀² h²)` by many orders
of magnitude.  For illustration, the factor is between 20 and 2·10⁴ for the three models above with
small `κ` and `T = 1`, but about 2·10⁸ for `σ = 1`, `b = 0` (`κ₁ = 1/2`, `κ₂ = 2`) with `T = 1`,
2·10²¹ for the same model with `T = 3`, and 3·10¹⁷ for jumps of size `−1/2` at rate `5` with
`T = 1`.

**§6.1, constant jump rate** (l. 2020–2025: "If the jump activity rate is constant, then for each
stochastic sample ω the jumps on the coarse and fine paths will occur at the same time, and
therefore the extension of the multilevel method is straightforward with the coarse and fine paths
using the same underlying Brownian paths, and the same random variables to determine the jump times
and strengths").  In the jump-adapted discretisation (l. 2014–2019) the grid of a level is the
uniform grid with the jump times added (`jumpGrid`).
* `jumpGrid_coupling` (a lemma; it holds by construction, both levels using the same jump times):
  the jump times lie on both grids and the coarse grid is part of the fine one, so the coarse path's
  Brownian increments are sums of the fine ones.
* `jumpAdapted_coarse_map_eq`: **conditionally on the jump times** (a fixed finite set merged into
  both grids), the coarse path's increments have exactly the law of independent `N(0, Δt)`
  increments on its own jump-adapted grid (by `unionGridBM_map_eq` of `BrownianPaths.lean`); with
  the same jump strengths for both paths, (2.4) holds.
* `unionGridBM_map_eq_nat`, `jumpAdapted_map_eq`, `jumpAdapted_2_4`: **random grids**.  For jump
  data `R` (times and strengths) independent of the normal variates and any grids that are
  measurable functions of `R` with monotone values, (jump data, coarse Brownian increments) has the
  joint law of (jump data, increments simulated on the coarse grid alone), so every payoff of the
  jumps and of the coarse path has the expectation of the single-level simulation: (2.4).
* `jumpAdapted_random_map_eq`, `jumpAdapted_random_2_4`: **random jump times**, the instance for the
  jump-adapted grids.  For a random number `M(R)` of jump times `S(R)_0, S(R)_1, …` (e.g. the jumps
  of a Poisson process in `[0, T]`), the fine grid `jaGrid h (2n)` is the sorted tuple
  (`Tuple.sort`) of the uniform times `kh` and the jump times, whose set of values is `jumpGrid`
  (`image_jaGrid`), the coarse grid `jaGrid (2h) n` is that of the times `k·2h` and the same jump
  times, and `jaPos` locates the coarse times in the fine grid.  Their measurability in the jump
  data and their monotonicity are proved, so (2.4) holds with random jump times independent of the
  Brownian path.

**§6.1, path-dependent jump rate** (l. 2026–2036: the thinning approach, "in which a set of
candidate jump times is simulated based on the constant upper bound, and then a subset of these are
selected to be real jumps"; "Xia and Giles (2012) avoid this by using a change of measure to ensure
that the jump times are the same for both paths; this introduces a Radon-Nikodym into the payoff
evaluation").  Conditionally on the candidate times, candidate `i` is accepted with a probability
`p_i` that may depend on the earlier decisions (the path); `thinLaw p` is the law of the decisions
and `thinLR p q` the Radon–Nikodym derivative of the target law `p` with respect to a sampling law
`q`.
* `thinLaw_isProb`: for adapted `p` with values in `[0, 1]`, `thinLaw p` is a probability law.
* `thinning_lr_unbiased`: `E_q[F · LR] = E_p[F]` for every payoff `F`: the estimator is unbiased.
* `thinning_mlmc_correction`: when the decisions are sampled once, from a common `q`, for the fine
  and the coarse path, `E_q[F^f LR^f − F^c LR^c] = E_{p^f}[F^f] − E_{p^c}[F^c]`, so the telescoping
  sum is respected.  The variance reduction claimed at l. 2036 is empirical and not formalised.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MLMC

/-! ### §6.2: the trapezoidal Asian average of an exponential Lévy model -/

/-- The trapezoidal Asian average of the exponential-Lévy price over `N` steps (Giles 2015, §6.2,
p. 48, Table 6.3, l. 2057, the "Asian" row; the option averages the price over `[0, T]`, here by the
trapezoidal rule on the time grid, a discrete-time analogue of `T⁻¹ ∫₀ᵀ S_t dt`):
`A_N(y) = N⁻¹ ∑_{k<N} (S_k + S_{k+1})/2` with `S_k = s₀ e^{X_k}`, where `X_k = y_0 + ⋯ + y_{k−1}`
(`levyPath`) is the log-price built from the increments `y_i` over the steps. -/
noncomputable def levyAsianTrap (s₀ : ℝ) (N : ℕ) (y : ℕ → ℝ) : ℝ :=
  (∑ k ∈ range N, (s₀ * Real.exp (levyPath y k) + s₀ * Real.exp (levyPath y (k + 1))) / 2) / N

/-- The contribution of one coarse step to the difference of the fine and the coarse trapezoidal
averages, relative to the price at its left end (Giles 2015, §6.2, Table 6.3): for the fine
increments `a`, `b` over its two halves, `D(a, b) = e^a − (1 + e^{a+b})/2`, the value of `e^X` at
the midpoint minus the mean of its values at the two ends. -/
noncomputable def levyTrapPair (a b : ℝ) : ℝ := Real.exp a - (1 + Real.exp (a + b)) / 2

/-- The sum `G_n(y) = ∑_{j<n} e^{X_{2j}} D(y_{2j}, y_{2j+1})` over the `n` coarse steps (Giles 2015,
§6.2, Table 6.3), so that `A^f − A^c = s₀/(2n) G_n` (`levyAsianTrap_sub`). -/
noncomputable def levyPairDiffSum (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, Real.exp (levyPath y (2 * j)) * levyTrapPair (y (2 * j)) (y (2 * j + 1))

/-- One more step of the log-price: `X_{k+1} = X_k + y_k` (Giles 2015, §6.2). -/
lemma levyPath_succ (y : ℕ → ℝ) (k : ℕ) : levyPath y (k + 1) = levyPath y k + y k :=
  Finset.sum_range_succ y k

/-- The log-price after the first two steps is that of the shifted increments (Giles 2015, §6.2):
`X_{k+2}(y) = y_0 + y_1 + X_k(y_2, y_3, …)`. -/
lemma levyPath_add_two (y : ℕ → ℝ) (k : ℕ) :
    levyPath y (k + 2) = y 0 + y 1 + levyPath (fun i => y (i + 2)) k := by
  unfold levyPath
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  ring

/-- The fine minus the coarse Asian average (Giles 2015, §6.2, p. 48, l. 2078–2079: "the
increments of the driving Lévy process for the coarse path can be obtained trivially by summing the
increments for the fine path").  For `2n` fine steps and the `n` coarse steps of the same path
(increments `levyPairSum y`), `A_{2n}(y) − A_n(levyPairSum y) = s₀/(2n) G_n(y)` (`levyPairDiffSum`).
-/
lemma levyAsianTrap_sub (s₀ : ℝ) (y : ℕ → ℝ) (n : ℕ) :
    levyAsianTrap s₀ (2 * n) y - levyAsianTrap s₀ n (levyPairSum y) =
      s₀ / (2 * n) * levyPairDiffSum y n := by
  unfold levyAsianTrap levyPairDiffSum
  simp only [levyPath_levyPairSum]
  rw [sum_range_two_mul]
  have key : ∀ j : ℕ,
      ((s₀ * Real.exp (levyPath y (2 * j)) + s₀ * Real.exp (levyPath y (2 * j + 1))) / 2 +
        (s₀ * Real.exp (levyPath y (2 * j + 1)) + s₀ * Real.exp (levyPath y (2 * j + 1 + 1))) / 2)
        - 2 * ((s₀ * Real.exp (levyPath y (2 * j)) + s₀ * Real.exp (levyPath y (2 * (j + 1)))) / 2)
        = s₀ * (Real.exp (levyPath y (2 * j)) * levyTrapPair (y (2 * j)) (y (2 * j + 1))) := by
    intro j
    have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e, levyPath_succ y (2 * j + 1), levyPath_succ y (2 * j), levyTrapPair, Real.exp_add,
      Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  calc _ = (∑ j ∈ range n,
        (((s₀ * Real.exp (levyPath y (2 * j)) + s₀ * Real.exp (levyPath y (2 * j + 1))) / 2 +
        (s₀ * Real.exp (levyPath y (2 * j + 1)) + s₀ * Real.exp (levyPath y (2 * j + 1 + 1))) / 2)
        - 2 * ((s₀ * Real.exp (levyPath y (2 * j)) + s₀ * Real.exp (levyPath y (2 * (j + 1)))) /
          2))) / (2 * n) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        push_cast
        field_simp
    _ = _ := by
        simp_rw [key]
        rw [← Finset.mul_sum]
        ring

/-- The recursion over the first coarse step (Giles 2015, §6.2):
`G_{n+1}(y) = D(y_0, y_1) + e^{y_0+y_1} G_n(y_2, y_3, …)`. -/
lemma levyPairDiffSum_succ (y : ℕ → ℝ) (n : ℕ) :
    levyPairDiffSum y (n + 1) = levyTrapPair (y 0) (y 1) +
      Real.exp (y 0 + y 1) * levyPairDiffSum (fun i => y (i + 2)) n := by
  unfold levyPairDiffSum
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have e0 : levyPath y (2 * 0) = 0 := by simp [levyPath]
  rw [e0, Real.exp_zero, one_mul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : 2 * (j + 1) = 2 * j + 2 := by ring
  have e2 : 2 * j + 2 + 1 = 2 * j + 1 + 2 := by ring
  rw [e1, e2, levyPath_add_two, Real.exp_add]
  ring

/-- The log-price `X_k` is a measurable function of the increments (Giles 2015, §6.2). -/
lemma measurable_levyPath (k : ℕ) : Measurable (fun y : ℕ → ℝ => levyPath y k) :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- `G_n` is a measurable function of the increments (Giles 2015, §6.2). -/
lemma measurable_levyPairDiffSum (n : ℕ) : Measurable (fun y : ℕ → ℝ => levyPairDiffSum y n) := by
  unfold levyPairDiffSum levyTrapPair
  refine Finset.measurable_sum _ fun j _ => ?_
  have h1 := measurable_levyPath (2 * j)
  have h2 : Measurable fun y : ℕ → ℝ => y (2 * j) := measurable_pi_apply _
  have h3 : Measurable fun y : ℕ → ℝ => y (2 * j + 1) := measurable_pi_apply _
  fun_prop

/-- The trapezoidal average is a measurable function of the increments (Giles 2015, §6.2). -/
lemma measurable_levyAsianTrap (s₀ : ℝ) (N : ℕ) :
    Measurable (fun y : ℕ → ℝ => levyAsianTrap s₀ N y) := by
  unfold levyAsianTrap
  refine (Finset.measurable_sum _ fun k _ => ?_).div_const _
  have h1 := measurable_levyPath k
  have h2 := measurable_levyPath (k + 1)
  fun_prop

/-- Summing the increments in pairs is measurable (Giles 2015, §6.2, l. 2078–2079). -/
lemma measurable_levyPairSum : Measurable (levyPairSum : (ℕ → ℝ) → ℕ → ℝ) :=
  measurable_pi_lambda _ fun k => (measurable_pi_apply (2 * k)).add (measurable_pi_apply _)

/-- `G_n` only depends on the first `2n` increments (Giles 2015, §6.2). -/
lemma levyPairDiffSum_congr {y y' : ℕ → ℝ} {n : ℕ} (h : ∀ i < 2 * n, y i = y' i) :
    levyPairDiffSum y n = levyPairDiffSum y' n := by
  unfold levyPairDiffSum levyPath
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [Finset.sum_congr rfl fun i hi => h i (by have := Finset.mem_range.1 hi; omega),
    h (2 * j) (by omega), h (2 * j + 1) (by omega)]

/-! ### The moments of the difference of the averages -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A function of the first two of independent increments `Y_0, Y_1, …` is independent of a function
of the shifted increments `(Y_2, Y_3, …)` that only depends on finitely many of them (the
independence of the increments of a Lévy process over disjoint steps, Giles 2015, §6.2). -/
lemma indepFun_pair_tail {Y : ℕ → Ω → ℝ} (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (k : ℕ) {φ : ℝ × ℝ → ℝ} (hφ : Measurable φ) {ψ : (ℕ → ℝ) → ℝ}
    (hψ : Measurable ψ) (hψk : ∀ y y' : ℕ → ℝ, (∀ i < k, y i = y' i) → ψ y = ψ y') :
    IndepFun (fun ω => φ (Y 0 ω, Y 1 ω)) (fun ω => ψ (fun i => Y (i + 2) ω)) μ := by
  classical
  have hST : Disjoint ({0, 1} : Finset ℕ) (Finset.Ico 2 (k + 2)) := by
    refine Finset.disjoint_left.2 fun i hi hi' => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico] at hi hi'
    omega
  have h := hind.indepFun_finset {0, 1} (Finset.Ico 2 (k + 2)) hST hY
  have h0 : (0 : ℕ) ∈ ({0, 1} : Finset ℕ) := by simp
  have h1 : (1 : ℕ) ∈ ({0, 1} : Finset ℕ) := by simp
  have hΦ : Measurable fun x : ({0, 1} : Finset ℕ) → ℝ => φ (x ⟨0, h0⟩, x ⟨1, h1⟩) :=
    hφ.comp ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
  have hΨ : Measurable fun x : (Finset.Ico 2 (k + 2)) → ℝ =>
      ψ (fun i => if hi : i + 2 ∈ Finset.Ico 2 (k + 2) then x ⟨i + 2, hi⟩ else 0) := by
    refine hψ.comp (measurable_pi_lambda _ fun i => ?_)
    by_cases hi : i + 2 ∈ Finset.Ico 2 (k + 2)
    · simp only [hi, dif_pos]
      exact measurable_pi_apply _
    · simp only [hi, dif_neg, not_false_eq_true]
      exact measurable_const
  have h' := h.comp hΦ hΨ
  have e : ((fun x : (Finset.Ico 2 (k + 2)) → ℝ =>
      ψ (fun i => if hi : i + 2 ∈ Finset.Ico 2 (k + 2) then x ⟨i + 2, hi⟩ else 0)) ∘
      fun ω (i : Finset.Ico 2 (k + 2)) => Y i ω) = fun ω => ψ (fun i => Y (i + 2) ω) := by
    funext ω
    refine hψk _ _ fun i hi => ?_
    have hi' : i + 2 ∈ Finset.Ico 2 (k + 2) := by
      simp only [Finset.mem_Ico]
      omega
    simp [hi']
  rw [e] at h'
  exact h'

/-- The exponential moments of independent variables multiply (Giles 2015, §6.2):
`E[e^{iX} e^{jZ}] = E[e^{iX}] E[e^{jZ}]`, the product being integrable. -/
lemma integral_exp_pow_mul_exp_pow {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z μ) (i j : ℕ) (hi : Integrable (fun ω => Real.exp (X ω) ^ i) μ)
    (hj : Integrable (fun ω => Real.exp (Z ω) ^ j) μ) :
    Integrable (fun ω => Real.exp (X ω) ^ i * Real.exp (Z ω) ^ j) μ ∧
      ∫ ω, Real.exp (X ω) ^ i * Real.exp (Z ω) ^ j ∂μ =
        (∫ ω, Real.exp (X ω) ^ i ∂μ) * ∫ ω, Real.exp (Z ω) ^ j ∂μ := by
  have h := hXZ.comp (φ := fun x => Real.exp x ^ i) (ψ := fun x => Real.exp x ^ j)
    (by fun_prop) (by fun_prop)
  exact ⟨h.integrable_mul hi hj, h.integral_fun_mul_eq_mul_integral
    (hX.exp.pow_const i).aestronglyMeasurable (hZ.exp.pow_const j).aestronglyMeasurable⟩

/-- The moments of one coarse step (Giles 2015, §6.2, Table 6.3).  For independent increments `X`,
`Z` with `E e^X = E e^Z = u` and `E e^{2X} = E e^{2Z} = v`, the step term `D = D(X, Z)` and the
growth factor `R = e^{X+Z}` are square integrable, with `E[D] = u − ½ − u²/2`,
`E[D²] = v + ¼ + v²/4 − u − uv + u²/2`, `E[D R] = uv − u²/2 − v²/2`, `E[R] = u²`, `E[R²] = v²`. -/
lemma trapPair_moments [IsProbabilityMeasure μ] {X Z : Ω → ℝ} (hX : Measurable X)
    (hZ : Measurable Z) (hXZ : IndepFun X Z μ) {u v : ℝ}
    (hX2 : Integrable (fun ω => Real.exp (X ω) ^ 2) μ)
    (hZ2 : Integrable (fun ω => Real.exp (Z ω) ^ 2) μ)
    (hXu : ∫ ω, Real.exp (X ω) ∂μ = u) (hZu : ∫ ω, Real.exp (Z ω) ∂μ = u)
    (hXv : ∫ ω, Real.exp (X ω) ^ 2 ∂μ = v) (hZv : ∫ ω, Real.exp (Z ω) ^ 2 ∂μ = v) :
    Integrable (fun ω => levyTrapPair (X ω) (Z ω)) μ ∧
    Integrable (fun ω => Real.exp (X ω + Z ω)) μ ∧
    Integrable (fun ω => levyTrapPair (X ω) (Z ω) ^ 2) μ ∧
    Integrable (fun ω => levyTrapPair (X ω) (Z ω) * Real.exp (X ω + Z ω)) μ ∧
    Integrable (fun ω => Real.exp (X ω + Z ω) ^ 2) μ ∧
    ∫ ω, levyTrapPair (X ω) (Z ω) ∂μ = u - 1 / 2 - u ^ 2 / 2 ∧
    ∫ ω, levyTrapPair (X ω) (Z ω) ^ 2 ∂μ = v + 1 / 4 + v ^ 2 / 4 - u - u * v + u ^ 2 / 2 ∧
    ∫ ω, levyTrapPair (X ω) (Z ω) * Real.exp (X ω + Z ω) ∂μ = u * v - u ^ 2 / 2 - v ^ 2 / 2 ∧
    ∫ ω, Real.exp (X ω + Z ω) ∂μ = u ^ 2 ∧
    ∫ ω, Real.exp (X ω + Z ω) ^ 2 ∂μ = v ^ 2 := by
  have hX1 : Integrable (fun ω => Real.exp (X ω)) μ :=
    ((memLp_two_iff_integrable_sq hX.exp.aestronglyMeasurable).2 hX2).integrable one_le_two
  have hZ1 : Integrable (fun ω => Real.exp (Z ω)) μ :=
    ((memLp_two_iff_integrable_sq hZ.exp.aestronglyMeasurable).2 hZ2).integrable one_le_two
  have hX1' : Integrable (fun ω => Real.exp (X ω) ^ 1) μ := by simpa using hX1
  have hZ1' : Integrable (fun ω => Real.exp (Z ω) ^ 1) μ := by simpa using hZ1
  obtain ⟨i11, e11⟩ := integral_exp_pow_mul_exp_pow hX hZ hXZ 1 1 hX1' hZ1'
  obtain ⟨i21, e21⟩ := integral_exp_pow_mul_exp_pow hX hZ hXZ 2 1 hX2 hZ1'
  obtain ⟨i22, e22⟩ := integral_exp_pow_mul_exp_pow hX hZ hXZ 2 2 hX2 hZ2
  simp only [pow_one] at i11 e11 i21 e21
  rw [hXu, hZu] at e11
  rw [hXv, hZu] at e21
  rw [hXv, hZv] at e22
  have eR : ∀ ω, Real.exp (X ω + Z ω) = Real.exp (X ω) * Real.exp (Z ω) := fun ω =>
    Real.exp_add _ _
  have eR2 : ∀ ω, Real.exp (X ω + Z ω) ^ 2 = Real.exp (X ω) ^ 2 * Real.exp (Z ω) ^ 2 :=
    fun ω => by rw [eR, mul_pow]
  have eD : ∀ ω, levyTrapPair (X ω) (Z ω) =
      Real.exp (X ω) - 1 / 2 - Real.exp (X ω) * Real.exp (Z ω) / 2 := fun ω => by
    rw [levyTrapPair, eR]
    ring
  have eD2 : ∀ ω, levyTrapPair (X ω) (Z ω) ^ 2 =
      Real.exp (X ω) ^ 2 + 1 / 4 + Real.exp (X ω) ^ 2 * Real.exp (Z ω) ^ 2 / 4 - Real.exp (X ω)
        - Real.exp (X ω) ^ 2 * Real.exp (Z ω) + Real.exp (X ω) * Real.exp (Z ω) / 2 :=
    fun ω => by rw [eD]; ring
  have eDR : ∀ ω, levyTrapPair (X ω) (Z ω) * Real.exp (X ω + Z ω) =
      Real.exp (X ω) ^ 2 * Real.exp (Z ω) - Real.exp (X ω) * Real.exp (Z ω) / 2
        - Real.exp (X ω) ^ 2 * Real.exp (Z ω) ^ 2 / 2 := fun ω => by rw [eD, eR]; ring
  simp_rw [eD2, eDR, eR2, eR]
  refine ⟨by simp_rw [eD]; fun_prop, i11, by fun_prop, by fun_prop, i22, ?_, ?_, ?_,
    e11.trans (sq u).symm,
    e22.trans (sq v).symm⟩
  · simp_rw [eD]
    rw [integral_sub (by fun_prop) (by fun_prop), integral_sub hX1 (integrable_const _)]
    simp only [integral_div, integral_const, probReal_univ, one_smul]
    rw [e11, hXu]
    ring
  · rw [integral_add (by fun_prop) (by fun_prop), integral_sub (by fun_prop) (by fun_prop),
      integral_sub (by fun_prop) (by fun_prop), integral_add (by fun_prop) (by fun_prop),
      integral_add (by fun_prop) (by fun_prop)]
    simp only [integral_div, integral_const, probReal_univ, one_smul]
    rw [e11, e21, e22, hXu, hXv]
    ring
  · rw [integral_sub (by fun_prop) (by fun_prop), integral_sub (by fun_prop) (by fun_prop)]
    simp only [integral_div]
    rw [e11, e21, e22]
    ring

/-- The moment recursion for the difference of the Asian averages (Giles 2015, §6.2, Table 6.3,
l. 2057).  Let `Y_0, Y_1, …` be independent with `E e^{Y_i} = u` and `E e^{2Y_i} = v` for every `i`,
and `A ≥ max(1, v²)`, `B ≥ max(1, u²)`.  Then `G_n ∈ L²`, `|E[G_n]| ≤ n |d₁| Bⁿ` and
`E[G_n²] ≤ n Aⁿ (d₂ + 2|c| n |d₁| Bⁿ)`, with `d₁ = u − ½ − u²/2`,
`d₂ = v + ¼ + v²/4 − u − uv + u²/2` and `c = uv − u²/2 − v²/2`.  The proof is by induction over all
such families, through `E[G_{n+1}] = d₁ + u² E[G_n(Y_{·+2})]` and
`E[G_{n+1}²] = d₂ + 2c E[G_n(Y_{·+2})] + v² E[G_n(Y_{·+2})²]` (`levyPairDiffSum_succ`). -/
lemma levyPairDiffSum_moments [IsProbabilityMeasure μ] {u v A B : ℝ} (hA : 1 ≤ A)
    (hB : 1 ≤ B) (hvA : v ^ 2 ≤ A) (huB : u ^ 2 ≤ B) (n : ℕ) :
    ∀ Y : ℕ → Ω → ℝ, (∀ i, Measurable (Y i)) → iIndepFun Y μ →
      (∀ i, Integrable (fun ω => Real.exp (Y i ω) ^ 2) μ) →
      (∀ i, ∫ ω, Real.exp (Y i ω) ∂μ = u) → (∀ i, ∫ ω, Real.exp (Y i ω) ^ 2 ∂μ = v) →
      Integrable (fun ω => levyPairDiffSum (Y · ω) n ^ 2) μ ∧
      |∫ ω, levyPairDiffSum (Y · ω) n ∂μ| ≤ n * |u - 1 / 2 - u ^ 2 / 2| * B ^ n ∧
      ∫ ω, levyPairDiffSum (Y · ω) n ^ 2 ∂μ ≤
        n * A ^ n * ((v + 1 / 4 + v ^ 2 / 4 - u - u * v + u ^ 2 / 2) +
          2 * |u * v - u ^ 2 / 2 - v ^ 2 / 2| * n * |u - 1 / 2 - u ^ 2 / 2| * B ^ n) := by
  induction n with
  | zero =>
    intro Y _ _ _ _ _
    simp [levyPairDiffSum]
  | succ n ih =>
    intro Y hY hind h2 hu hv
    obtain ⟨hGi, hGm, hGq⟩ := ih (fun i => Y (i + 2)) (fun i => hY (i + 2))
      (hind.precomp (add_left_injective 2)) (fun i => h2 (i + 2)) (fun i => hu (i + 2))
      (fun i => hv (i + 2))
    set d1 := u - 1 / 2 - u ^ 2 / 2 with hd1
    set d2 := v + 1 / 4 + v ^ 2 / 4 - u - u * v + u ^ 2 / 2 with hd2
    set c := u * v - u ^ 2 / 2 - v ^ 2 / 2 with hc
    set G : Ω → ℝ := fun ω => levyPairDiffSum (fun i => Y (i + 2) ω) n with hGdef
    have hGmeas : Measurable G :=
      (measurable_levyPairDiffSum n).comp (measurable_pi_lambda _ fun i => hY (i + 2))
    have hG2 : MemLp G 2 μ := (memLp_two_iff_integrable_sq hGmeas.aestronglyMeasurable).2 hGi
    have hG1 : Integrable G μ := hG2.integrable one_le_two
    obtain ⟨iD, iR, iD2, iDR, iR2, eD, eD2, eDR, eR, eR2⟩ := trapPair_moments (hY 0) (hY 1)
      (hind.indepFun zero_ne_one) (h2 0) (h2 1) (hu 0) (hu 1) (hv 0) (hv 1)
    have hcong : ∀ y y' : ℕ → ℝ, (∀ i < 2 * n, y i = y' i) →
        levyPairDiffSum y n = levyPairDiffSum y' n := fun y y' h => levyPairDiffSum_congr h
    have I1 := indepFun_pair_tail hY hind (2 * n) (φ := fun p => Real.exp (p.1 + p.2))
      (by fun_prop) (measurable_levyPairDiffSum n) hcong
    have I2 := indepFun_pair_tail hY hind (2 * n)
      (φ := fun p => levyTrapPair p.1 p.2 * Real.exp (p.1 + p.2))
      (by unfold levyTrapPair; fun_prop) (measurable_levyPairDiffSum n) hcong
    have I3 := indepFun_pair_tail hY hind (2 * n) (φ := fun p => Real.exp (p.1 + p.2) ^ 2)
      (by fun_prop) ((measurable_levyPairDiffSum n).pow_const 2)
      (fun y y' h => by rw [levyPairDiffSum_congr h])
    have mR : Measurable fun ω => Real.exp (Y 0 ω + Y 1 ω) := by
      have := hY 0
      have := hY 1
      fun_prop
    have mDR : Measurable fun ω => levyTrapPair (Y 0 ω) (Y 1 ω) * Real.exp (Y 0 ω + Y 1 ω) := by
      have := hY 0
      have := hY 1
      unfold levyTrapPair
      fun_prop
    have iRG : Integrable (fun ω => Real.exp (Y 0 ω + Y 1 ω) * G ω) μ := I1.integrable_mul iR hG1
    have iDRG : Integrable (fun ω => levyTrapPair (Y 0 ω) (Y 1 ω) * Real.exp (Y 0 ω + Y 1 ω) *
        G ω) μ := I2.integrable_mul iDR hG1
    have iRG2 : Integrable (fun ω => Real.exp (Y 0 ω + Y 1 ω) ^ 2 * G ω ^ 2) μ :=
      I3.integrable_mul iR2 hGi
    have jRG : ∫ ω, Real.exp (Y 0 ω + Y 1 ω) * G ω ∂μ = u ^ 2 * ∫ ω, G ω ∂μ := by
      rw [I1.integral_fun_mul_eq_mul_integral mR.aestronglyMeasurable
        hGmeas.aestronglyMeasurable, eR]
    have jDRG : ∫ ω, levyTrapPair (Y 0 ω) (Y 1 ω) * Real.exp (Y 0 ω + Y 1 ω) * G ω ∂μ =
        c * ∫ ω, G ω ∂μ := by
      rw [I2.integral_fun_mul_eq_mul_integral mDR.aestronglyMeasurable
        hGmeas.aestronglyMeasurable, eDR]
    have jRG2 : ∫ ω, Real.exp (Y 0 ω + Y 1 ω) ^ 2 * G ω ^ 2 ∂μ = v ^ 2 * ∫ ω, G ω ^ 2 ∂μ := by
      rw [I3.integral_fun_mul_eq_mul_integral (mR.pow_const 2).aestronglyMeasurable
        (hGmeas.pow_const 2).aestronglyMeasurable, eR2]
    have erec : ∀ ω, levyPairDiffSum (Y · ω) (n + 1) =
        levyTrapPair (Y 0 ω) (Y 1 ω) + Real.exp (Y 0 ω + Y 1 ω) * G ω := fun ω =>
      levyPairDiffSum_succ _ n
    have erec2 : ∀ ω, levyPairDiffSum (Y · ω) (n + 1) ^ 2 =
        levyTrapPair (Y 0 ω) (Y 1 ω) ^ 2 +
          2 * (levyTrapPair (Y 0 ω) (Y 1 ω) * Real.exp (Y 0 ω + Y 1 ω) * G ω) +
          Real.exp (Y 0 ω + Y 1 ω) ^ 2 * G ω ^ 2 := fun ω => by rw [erec]; ring
    have hm : ∫ ω, levyPairDiffSum (Y · ω) (n + 1) ∂μ = d1 + u ^ 2 * ∫ ω, G ω ∂μ := by
      simp_rw [erec]
      rw [integral_add iD iRG, eD, jRG]
    have hq : ∫ ω, levyPairDiffSum (Y · ω) (n + 1) ^ 2 ∂μ =
        d2 + 2 * (c * ∫ ω, G ω ∂μ) + v ^ 2 * ∫ ω, G ω ^ 2 ∂μ := by
      simp_rw [erec2]
      rw [integral_add (by fun_prop) iRG2, integral_add iD2 (by fun_prop),
        integral_const_mul, eD2, jDRG, jRG2]
    have hd2n : 0 ≤ d2 := by
      rw [hd2, ← eD2]
      exact integral_nonneg fun ω => sq_nonneg _
    have hq0 : 0 ≤ ∫ ω, G ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have hBn : 1 ≤ B ^ n := one_le_pow₀ hB
    have hA1 : 1 ≤ A ^ (n + 1) := one_le_pow₀ hA
    have hnB : (n : ℝ) * B ^ n ≤ ((n + 1 : ℕ) : ℝ) * B ^ (n + 1) := by
      have h1 : B ^ n ≤ B ^ (n + 1) := pow_le_pow_right₀ hB (Nat.le_succ n)
      have h2 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact mul_le_mul h2 h1 (by positivity) (by positivity)
    refine ⟨?_, ?_, ?_⟩
    · simp_rw [erec2]
      fun_prop
    · rw [hm]
      have h1 : |d1 + u ^ 2 * ∫ ω, G ω ∂μ| ≤ |d1| + u ^ 2 * |∫ ω, G ω ∂μ| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
      have h2 : u ^ 2 * |∫ ω, G ω ∂μ| ≤ B * (n * |d1| * B ^ n) :=
        mul_le_mul huB hGm (abs_nonneg _) (by linarith)
      have h3 : |d1| ≤ |d1| * B ^ (n + 1) :=
        le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ hB)
      have h4 : |d1| * B ^ (n + 1) + B * (n * |d1| * B ^ n) =
          ((n + 1 : ℕ) : ℝ) * |d1| * B ^ (n + 1) := by push_cast; ring
      linarith
    · rw [hq]
      set X := d2 + 2 * |c| * n * |d1| * B ^ n with hX
      set X' := d2 + 2 * |c| * ((n + 1 : ℕ) : ℝ) * |d1| * B ^ (n + 1) with hX'
      have hXX : X ≤ X' := by
        have e : X' - X = 2 * |c| * |d1| * (((n + 1 : ℕ) : ℝ) * B ^ (n + 1) - n * B ^ n) := by
          rw [hX, hX']
          ring
        have : 0 ≤ 2 * |c| * |d1| * (((n + 1 : ℕ) : ℝ) * B ^ (n + 1) - n * B ^ n) :=
          mul_nonneg (by positivity) (by linarith)
        linarith
      have hX'0 : 0 ≤ X' := by positivity
      have hcm : 2 * (c * ∫ ω, G ω ∂μ) ≤ 2 * |c| * (n * |d1| * B ^ n) := by
        have h1 : c * ∫ ω, G ω ∂μ ≤ |c| * |∫ ω, G ω ∂μ| := by
          rw [← abs_mul]
          exact le_abs_self _
        have h2 : |c| * |∫ ω, G ω ∂μ| ≤ |c| * (n * |d1| * B ^ n) :=
          mul_le_mul_of_nonneg_left hGm (abs_nonneg c)
        linarith
      have hvq : v ^ 2 * ∫ ω, G ω ^ 2 ∂μ ≤ A * (n * A ^ n * X) :=
        mul_le_mul hvA hGq hq0 (by linarith)
      have eX : X = d2 + 2 * |c| * (n * |d1| * B ^ n) := by rw [hX]; ring
      have h1 : X ≤ A ^ (n + 1) * X' := hXX.trans (le_mul_of_one_le_left hX'0 hA1)
      have h2 : A * (n * A ^ n * X) ≤ n * A ^ (n + 1) * X' := by
        have e : A * (n * A ^ n * X) = n * A ^ (n + 1) * X := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left hXX (by positivity)
      have e3 : A ^ (n + 1) * X' + n * A ^ (n + 1) * X' = ((n + 1 : ℕ) : ℝ) * A ^ (n + 1) * X' := by
        push_cast
        ring
      linarith

end Moments

/-! ### The `O(h²)` bound -/

/-- `|e^x − 1| ≤ |x| e^{|x|}` (Giles 2015, §6.2: the exponential moments `e^{hκ}` are `1 + O(h)`).
-/
lemma abs_exp_sub_one_le_mul_exp (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_or_gt 0 x with hx | hx
  · have h1 := Real.add_one_le_exp (-x)
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have h3 : 1 ≤ Real.exp x := Real.one_le_exp hx
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hx]
    nlinarith [Real.exp_pos x]
  · have h1 := Real.add_one_le_exp x
    have h3 : Real.exp x < 1 := Real.exp_lt_one_iff.2 hx
    have h4 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    rw [abs_of_neg (by linarith), abs_of_neg hx]
    calc -(Real.exp x - 1) ≤ -x * 1 := by linarith
      _ ≤ -x * Real.exp (-x) := mul_le_mul_of_nonneg_left h4 (by linarith)

/-- The scalar estimate behind `levy_asian_avg_sq_le` (Giles 2015, §6.2, Table 6.3).  For `n ≥ 1`,
`h > 0`, `T = 2nh`, `k ≥ 0`, `E = e^{Tk}` and `|p|, |q| ≤ hkE` (`p = u − 1`, `q = v − 1`),
`(s₀/(2n))² · n E (d₂ + 2|c| n |d₁| E) ≤ s₀² e^{6Tk} (k/T + k² + T²k⁴) h²`, where `d₂`, `|c|` and
`|d₁|` are written in terms of `p` and `q`. -/
lemma levyAsian_scalar_bound {s₀ h T k E p q : ℝ} {n : ℕ} (hn : 0 < n) (hh : 0 < h)
    (hT : T = 2 * n * h) (hk : 0 ≤ k) (hE : E = Real.exp (T * k)) (hp : |p| ≤ h * k * E)
    (hq : |q| ≤ h * k * E) :
    (s₀ / (2 * n)) ^ 2 * (n * E * ((q / 2 - p + q ^ 2 / 4 - p * q + p ^ 2 / 2) +
      2 * ((p - q) ^ 2 / 2) * n * (p ^ 2 / 2) * E)) ≤
      s₀ ^ 2 * (Real.exp (6 * T * k) * (k / T + k ^ 2 + T ^ 2 * k ^ 4)) * h ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hTpos : 0 < T := by rw [hT]; positivity
  have h2h : 2 * h ≤ T := by
    have := mul_le_mul_of_nonneg_right hn1 (by positivity : (0 : ℝ) ≤ 2 * h)
    rw [hT]
    linarith
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (mul_nonneg hTpos.le hk)
  have hE6 : Real.exp (6 * T * k) = E ^ 6 := by
    rw [hE, ← Real.exp_nat_mul]
    ring_nf
  set a := h * k * E with ha
  have ha0 : 0 ≤ a := by positivity
  have hp2 : p ^ 2 ≤ a ^ 2 := sq_le_sq' (abs_le.1 hp).1 (abs_le.1 hp).2
  have hq2 : q ^ 2 ≤ a ^ 2 := sq_le_sq' (abs_le.1 hq).1 (abs_le.1 hq).2
  have epq : (p + q) ^ 2 = p ^ 2 + 2 * (p * q) + q ^ 2 := by ring
  have hpq0 := sq_nonneg (p + q)
  have hpq : (p - q) ^ 2 ≤ 4 * a ^ 2 := by
    have e : (p - q) ^ 2 = p ^ 2 - 2 * (p * q) + q ^ 2 := by ring
    linarith
  have hd2 : q / 2 - p + q ^ 2 / 4 - p * q + p ^ 2 / 2 ≤ 3 * a / 2 + 7 * a ^ 2 / 4 := by
    have h1 : q ≤ a := (abs_le.1 hq).2
    have h2 : -p ≤ a := by linarith [(abs_le.1 hp).1]
    linarith
  have hcd : 2 * ((p - q) ^ 2 / 2) * n * (p ^ 2 / 2) * E ≤ 2 * n * a ^ 4 * E := by
    have h1 : (p - q) ^ 2 * p ^ 2 ≤ 4 * a ^ 2 * a ^ 2 :=
      mul_le_mul hpq hp2 (sq_nonneg p) (by positivity)
    have e1 : 2 * ((p - q) ^ 2 / 2) * n * (p ^ 2 / 2) * E = (p - q) ^ 2 * p ^ 2 * (n * E / 2) := by
      ring
    have e2 : 2 * n * a ^ 4 * E = 4 * a ^ 2 * a ^ 2 * (n * E / 2) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hsum : (s₀ / (2 * n)) ^ 2 * (n * E * ((q / 2 - p + q ^ 2 / 4 - p * q + p ^ 2 / 2) +
      2 * ((p - q) ^ 2 / 2) * n * (p ^ 2 / 2) * E)) ≤
      (s₀ / (2 * n)) ^ 2 * (n * E * (3 * a / 2 + 7 * a ^ 2 / 4 + 2 * n * a ^ 4 * E)) := by
    gcongr
  refine hsum.trans ?_
  have e1 : (s₀ / (2 * n)) ^ 2 * (n * E * (3 * a / 2 + 7 * a ^ 2 / 4 + 2 * n * a ^ 4 * E)) =
      s₀ ^ 2 * E * (3 * a / (8 * n) + 7 * a ^ 2 / (16 * n) + a ^ 4 * E / 2) := by
    field_simp
    ring
  rw [e1, hE6]
  have hinvn : 1 / (n : ℝ) = 2 * h / T := by
    rw [hT]
    field_simp
  have t1 : 3 * a / (8 * n) = 3 * h ^ 2 * k * E / (4 * T) := by
    have : 3 * a / (8 * n) = 3 * a / 8 * (1 / n) := by ring
    rw [this, hinvn, ha]
    field_simp
    ring
  have t2 : 7 * a ^ 2 / (16 * n) ≤ 7 * h ^ 2 * k ^ 2 * E ^ 2 / 16 := by
    have h1 : 7 * a ^ 2 / (16 * n) ≤ 7 * a ^ 2 / 16 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have e : 7 * a ^ 2 / 16 = 7 * h ^ 2 * k ^ 2 * E ^ 2 / 16 := by rw [ha]; ring
    linarith
  have t3 : a ^ 4 * E / 2 ≤ h ^ 2 * T ^ 2 * k ^ 4 * E ^ 5 / 8 := by
    have hh2 : h ^ 2 ≤ T ^ 2 / 4 := by
      have := pow_le_pow_left₀ (by positivity) h2h 2
      have e : (2 * h) ^ 2 = 4 * h ^ 2 := by ring
      linarith
    have e : a ^ 4 * E / 2 = h ^ 2 * (h ^ 2 * (k ^ 4 * E ^ 5 / 2)) := by rw [ha]; ring
    rw [e]
    have h0 : 0 ≤ k ^ 4 * E ^ 5 / 2 := by positivity
    calc h ^ 2 * (h ^ 2 * (k ^ 4 * E ^ 5 / 2)) ≤ h ^ 2 * (T ^ 2 / 4 * (k ^ 4 * E ^ 5 / 2)) := by
          gcongr
      _ = _ := by ring
  rw [t1]
  have hkT : 0 ≤ k / T := by positivity
  have key : ∀ (X c : ℝ) (m : ℕ), 0 ≤ X → 0 ≤ c → c ≤ 1 → m ≤ 6 →
      c * X * E ^ m ≤ X * E ^ 6 := fun X c m hX hc0 hc1 hm => by
    have h1 : E ^ m ≤ E ^ 6 := pow_le_pow_right₀ hE1 hm
    have h2 : 0 ≤ X * E ^ m := by positivity
    calc c * X * E ^ m = c * (X * E ^ m) := by ring
      _ ≤ 1 * (X * E ^ m) := by gcongr
      _ = X * E ^ m := one_mul _
      _ ≤ X * E ^ 6 := by gcongr
  have k1 := key (k / T) (3 / 4) 2 hkT (by norm_num) (by norm_num) (by norm_num)
  have k2 := key (k ^ 2) (7 / 16) 3 (sq_nonneg k) (by norm_num) (by norm_num) (by norm_num)
  have k3 := key (T ^ 2 * k ^ 4) (1 / 8) 6 (by positivity) (by norm_num) (by norm_num) le_rfl
  have hs0 : 0 ≤ s₀ ^ 2 * E := by positivity
  have hsum2 : 3 * h ^ 2 * k * E / (4 * T) + 7 * a ^ 2 / (16 * n) + a ^ 4 * E / 2 ≤
      3 * h ^ 2 * k * E / (4 * T) + 7 * h ^ 2 * k ^ 2 * E ^ 2 / 16 +
        h ^ 2 * T ^ 2 * k ^ 4 * E ^ 5 / 8 := by linarith
  have e2 : s₀ ^ 2 * E * (3 * h ^ 2 * k * E / (4 * T) + 7 * h ^ 2 * k ^ 2 * E ^ 2 / 16 +
        h ^ 2 * T ^ 2 * k ^ 4 * E ^ 5 / 8) = s₀ ^ 2 * h ^ 2 * (3 / 4 * (k / T) * E ^ 2 +
        7 / 16 * k ^ 2 * E ^ 3 + 1 / 8 * (T ^ 2 * k ^ 4) * E ^ 6) := by
    field_simp
  have e3 : s₀ ^ 2 * h ^ 2 * ((k / T) * E ^ 6 + k ^ 2 * E ^ 6 + (T ^ 2 * k ^ 4) * E ^ 6) =
      s₀ ^ 2 * (E ^ 6 * (k / T + k ^ 2 + T ^ 2 * k ^ 4)) * h ^ 2 := by ring
  have hs1 : 0 ≤ s₀ ^ 2 * h ^ 2 := by positivity
  calc s₀ ^ 2 * E * (3 * h ^ 2 * k * E / (4 * T) + 7 * a ^ 2 / (16 * n) + a ^ 4 * E / 2)
      ≤ s₀ ^ 2 * E * (3 * h ^ 2 * k * E / (4 * T) + 7 * h ^ 2 * k ^ 2 * E ^ 2 / 16 +
          h ^ 2 * T ^ 2 * k ^ 4 * E ^ 5 / 8) := mul_le_mul_of_nonneg_left hsum2 hs0
    _ = s₀ ^ 2 * h ^ 2 * (3 / 4 * (k / T) * E ^ 2 + 7 / 16 * k ^ 2 * E ^ 3 +
          1 / 8 * (T ^ 2 * k ^ 4) * E ^ 6) := e2
    _ ≤ s₀ ^ 2 * h ^ 2 * ((k / T) * E ^ 6 + k ^ 2 * E ^ 6 + (T ^ 2 * k ^ 4) * E ^ 6) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add k1 k2) k3) hs1
    _ = _ := e3

/-- The constant of the `O(h²)` bound for the exponential-Lévy Asian option (Giles 2015, §6.2,
Table 6.3, l. 2057): `C(κ₁, κ₂, T) = e^{6Tk} (k/T + k² + T²k⁴)` with `k = |κ₁| + |κ₂|`.  Only the
order `h²` of the bound is sharp: `C` is exponential in `Tk` and can exceed the exact value of
`E[(A^f − A^c)²]/(s₀² h²)` by many orders of magnitude (by a factor 20 to 2·10⁴ for small `κ` and
`T = 1`, but about 2·10⁸ for `κ₁ = 1/2`, `κ₂ = 2`, `T = 1`, and 2·10²¹ for `T = 3`). -/
noncomputable def levyAsianConst (κ₁ κ₂ T : ℝ) : ℝ :=
  Real.exp (6 * T * (|κ₁| + |κ₂|)) *
    ((|κ₁| + |κ₂|) / T + (|κ₁| + |κ₂|) ^ 2 + T ^ 2 * (|κ₁| + |κ₂|) ^ 4)

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `(e^x)² = e^{2x}` (Giles 2015, §6.2: the second exponential moment `E e^{2Y} = E[(e^Y)²]` of
an increment). -/
lemma exp_sq_eq_exp_two_mul (x : ℝ) : Real.exp x ^ 2 = Real.exp (2 * x) := by
  rw [sq, ← Real.exp_add, two_mul]

/-- **The fine and the coarse Asian averages differ by `O(h)` in root mean square:
`E[(A^f − A^c)²] = O(h²)`** (Giles 2015, §6.2, p. 48, Table 6.3, l. 2057: "Asian O(h²) O(h²) O(h²)",
for the variance `V_ℓ ≡ V[P_ℓ − P_{ℓ−1}]` (l. 2060) of exponential Lévy models whose increments over
uniform timesteps are simulated exactly (l. 2063–2064) and summed in pairs for the coarse path
(l. 2078–2079)).  Let `Y_0, Y_1, …` be independent with `E e^{Y_i} = e^{hκ₁}` and
`E e^{2Y_i} = e^{hκ₂}` for every `i` (the increments of a Lévy process over one fine step `h > 0`;
they need not be identically distributed), `n ≥ 1` and `T = 2nh`.  The trapezoidal averages of
`S = s₀ e^X` over the `2n` fine steps and over the `n` coarse steps (built from the pair sums of the
same increments) satisfy `E[(A^f − A^c)²] ≤ s₀² C h²`, `C = levyAsianConst κ₁ κ₂ T`, which only
depends on `κ₁`, `κ₂`, `T` (the independence of the `Y_i` makes `μ` a probability measure).
Discrete-time analogue: only grid values enter (see the module docstring). -/
theorem levy_asian_avg_sq_le {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ) {h κ₁ κ₂ T : ℝ} (hh : 0 < h)
    (h1 : ∀ i, ∫ ω, Real.exp (Y i ω) ∂μ = Real.exp (h * κ₁))
    (h2 : ∀ i, ∫ ω, Real.exp (2 * Y i ω) ∂μ = Real.exp (h * κ₂)) (s₀ : ℝ) {n : ℕ}
    (hn : 0 < n) (hT : 2 * n * h = T) :
    Integrable (fun ω => (levyAsianTrap s₀ (2 * n) (Y · ω) -
      levyAsianTrap s₀ n (levyPairSum (Y · ω))) ^ 2) μ ∧
    ∫ ω, (levyAsianTrap s₀ (2 * n) (Y · ω) - levyAsianTrap s₀ n (levyPairSum (Y · ω))) ^ 2 ∂μ ≤
      s₀ ^ 2 * levyAsianConst κ₁ κ₂ T * h ^ 2 := by
  have := hind.isProbabilityMeasure
  set k := |κ₁| + |κ₂| with hk
  have hk0 : 0 ≤ k := by positivity
  have h2' : ∀ i, ∫ ω, Real.exp (Y i ω) ^ 2 ∂μ = Real.exp (h * κ₂) := fun i => by
    simp_rw [exp_sq_eq_exp_two_mul]
    exact h2 i
  have hint : ∀ i, Integrable (fun ω => Real.exp (Y i ω) ^ 2) μ := fun i =>
    Integrable.of_integral_ne_zero (by rw [h2' i]; exact (Real.exp_pos _).ne')
  have hA1 : 1 ≤ Real.exp (2 * h * k) := Real.one_le_exp (by positivity)
  have hvA : Real.exp (h * κ₂) ^ 2 ≤ Real.exp (2 * h * k) := by
    rw [exp_sq_eq_exp_two_mul, Real.exp_le_exp]
    have : κ₂ ≤ k := (le_abs_self κ₂).trans (by rw [hk]; linarith [abs_nonneg κ₁])
    nlinarith
  have huB : Real.exp (h * κ₁) ^ 2 ≤ Real.exp (2 * h * k) := by
    rw [exp_sq_eq_exp_two_mul, Real.exp_le_exp]
    have : κ₁ ≤ k := (le_abs_self κ₁).trans (by rw [hk]; linarith [abs_nonneg κ₂])
    nlinarith
  obtain ⟨hGi, -, hGq⟩ := levyPairDiffSum_moments hA1 hA1 hvA huB n Y hY hind hint h1 h2'
  have e : ∀ ω, (levyAsianTrap s₀ (2 * n) (Y · ω) - levyAsianTrap s₀ n (levyPairSum (Y · ω))) ^ 2
      = (s₀ / (2 * n)) ^ 2 * levyPairDiffSum (Y · ω) n ^ 2 := fun ω => by
    rw [levyAsianTrap_sub, mul_pow]
  simp_rw [e]
  refine ⟨hGi.const_mul _, ?_⟩
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hGq (sq_nonneg _)).trans ?_
  have hE : Real.exp (2 * h * k) ^ n = Real.exp (T * k) := by
    rw [← Real.exp_nat_mul, ← hT]
    ring_nf
  rw [hE]
  set p := Real.exp (h * κ₁) - 1 with hp
  set q := Real.exp (h * κ₂) - 1 with hq
  have hu : Real.exp (h * κ₁) = 1 + p := by rw [hp]; ring
  have hv : Real.exp (h * κ₂) = 1 + q := by rw [hq]; ring
  have hTpos : 0 < T := by rw [← hT]; positivity
  have hpb : ∀ κ : ℝ, |κ| ≤ k → |Real.exp (h * κ) - 1| ≤ h * k * Real.exp (T * k) := by
    intro κ hκ
    refine (abs_exp_sub_one_le_mul_exp _).trans ?_
    have hhk : |h * κ| ≤ h * k := by
      rw [abs_mul, abs_of_pos hh]
      exact mul_le_mul_of_nonneg_left hκ hh.le
    have hhT : h * k ≤ T * k := by
      have : h ≤ T := by
        rw [← hT]
        have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
        nlinarith
      exact mul_le_mul_of_nonneg_right this hk0
    exact mul_le_mul hhk (Real.exp_le_exp.2 (hhk.trans hhT)) (Real.exp_pos _).le (by positivity)
  have hpk : |p| ≤ h * k * Real.exp (T * k) := hpb κ₁ (by rw [hk]; linarith [abs_nonneg κ₂])
  have hqk : |q| ≤ h * k * Real.exp (T * k) := hpb κ₂ (by rw [hk]; linarith [abs_nonneg κ₁])
  have hd1 : |Real.exp (h * κ₁) - 1 / 2 - Real.exp (h * κ₁) ^ 2 / 2| = p ^ 2 / 2 := by
    rw [hu, show (1 + p) - 1 / 2 - (1 + p) ^ 2 / 2 = -(p ^ 2 / 2) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
  have hc : |Real.exp (h * κ₁) * Real.exp (h * κ₂) - Real.exp (h * κ₁) ^ 2 / 2 -
      Real.exp (h * κ₂) ^ 2 / 2| = (p - q) ^ 2 / 2 := by
    rw [hu, hv, show (1 + p) * (1 + q) - (1 + p) ^ 2 / 2 - (1 + q) ^ 2 / 2 = -((p - q) ^ 2 / 2)
      by ring, abs_neg, abs_of_nonneg (by positivity)]
  have hd2 : Real.exp (h * κ₂) + 1 / 4 + Real.exp (h * κ₂) ^ 2 / 4 - Real.exp (h * κ₁) -
      Real.exp (h * κ₁) * Real.exp (h * κ₂) + Real.exp (h * κ₁) ^ 2 / 2 =
      q / 2 - p + q ^ 2 / 4 - p * q + p ^ 2 / 2 := by
    rw [hu, hv]
    ring
  rw [hd1, hc, hd2, levyAsianConst, ← hk]
  have hT' : T = 2 * n * h := hT.symm
  exact levyAsian_scalar_bound hn hh hT' hk0 rfl hpk hqk

/-- **`V_ℓ = O(h²)` for the Asian option of an exponential Lévy model: `β = 2`** (Giles 2015, §6.2,
p. 48, Table 6.3, l. 2057–2060: "Asian O(h²) O(h²) O(h²)", "Numerical analysis convergence rates for
the multilevel variance `V_ℓ ≡ V[P_ℓ − P_{ℓ−1}]`").  In the setting of `levy_asian_avg_sq_le`, for a
`K`-Lipschitz payoff `g` of the trapezoidal average (e.g. the Asian call `e^{−rT} max(A − K', 0)`),
the multilevel correction `g(A^f) − g(A^c)` is in `L²` and satisfies
`E[(g(A^f) − g(A^c))²] ≤ K² s₀² C h²` and `V[g(A^f) − g(A^c)] ≤ K² s₀² C h²`: `β = 2` for every
exponential Lévy model with `E e^{2X_t} < ∞` (Variance-Gamma, NIG and spectrally negative
`α`-stable processes alike, the three columns of the table, whenever this exponential moment is
finite; without it the Asian call itself need not have a finite variance).  The continuously
monitored average of the paper is replaced by the trapezoidal average of the grid values. -/
theorem levy_asian_payoff_sq_le {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ) {h κ₁ κ₂ T : ℝ} (hh : 0 < h)
    (h1 : ∀ i, ∫ ω, Real.exp (Y i ω) ∂μ = Real.exp (h * κ₁))
    (h2 : ∀ i, ∫ ω, Real.exp (2 * Y i ω) ∂μ = Real.exp (h * κ₂)) {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (s₀ : ℝ) {n : ℕ} (hn : 0 < n)
    (hT : 2 * n * h = T) :
    MemLp (fun ω => g (levyAsianTrap s₀ (2 * n) (Y · ω)) -
      g (levyAsianTrap s₀ n (levyPairSum (Y · ω)))) 2 μ ∧
    ∫ ω, (g (levyAsianTrap s₀ (2 * n) (Y · ω)) -
      g (levyAsianTrap s₀ n (levyPairSum (Y · ω)))) ^ 2 ∂μ ≤
      K ^ 2 * s₀ ^ 2 * levyAsianConst κ₁ κ₂ T * h ^ 2 ∧
    variance (fun ω => g (levyAsianTrap s₀ (2 * n) (Y · ω)) -
      g (levyAsianTrap s₀ n (levyPairSum (Y · ω)))) μ ≤
      K ^ 2 * s₀ ^ 2 * levyAsianConst κ₁ κ₂ T * h ^ 2 := by
  have := hind.isProbabilityMeasure
  obtain ⟨hi, hb⟩ := levy_asian_avg_sq_le hY hind hh h1 h2 s₀ hn hT
  have hpt : ∀ ω, (g (levyAsianTrap s₀ (2 * n) (Y · ω)) -
      g (levyAsianTrap s₀ n (levyPairSum (Y · ω)))) ^ 2 ≤
      K ^ 2 * (levyAsianTrap s₀ (2 * n) (Y · ω) - levyAsianTrap s₀ n (levyPairSum (Y · ω))) ^ 2 :=
    fun ω => sq_sub_le_of_lipschitz_mon hg _ _
  have hsq : ∫ ω, (g (levyAsianTrap s₀ (2 * n) (Y · ω)) -
      g (levyAsianTrap s₀ n (levyPairSum (Y · ω)))) ^ 2 ∂μ ≤
      K ^ 2 * s₀ ^ 2 * levyAsianConst κ₁ κ₂ T * h ^ 2 :=
    calc _ ≤ ∫ ω, K ^ 2 * (levyAsianTrap s₀ (2 * n) (Y · ω) -
          levyAsianTrap s₀ n (levyPairSum (Y · ω))) ^ 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
            (hi.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = K ^ 2 * ∫ ω, (levyAsianTrap s₀ (2 * n) (Y · ω) -
          levyAsianTrap s₀ n (levyPairSum (Y · ω))) ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ K ^ 2 * (s₀ ^ 2 * levyAsianConst κ₁ κ₂ T * h ^ 2) :=
          mul_le_mul_of_nonneg_left hb (sq_nonneg K)
      _ = _ := by ring
  obtain ⟨-, hgc⟩ := continuous_of_abs_sub_le hg
  have hYm : Measurable fun ω => (Y · ω) := measurable_pi_lambda _ hY
  have hmeas : Measurable (fun ω => g (levyAsianTrap s₀ (2 * n) (Y · ω)) -
      g (levyAsianTrap s₀ n (levyPairSum (Y · ω)))) :=
    (hgc.measurable.comp ((measurable_levyAsianTrap s₀ (2 * n)).comp hYm)).sub
      (hgc.measurable.comp (((measurable_levyAsianTrap s₀ n).comp
        measurable_levyPairSum).comp hYm))
  have hm := hmeas.aestronglyMeasurable (μ := μ)
  have hint : Integrable (fun ω => (g (levyAsianTrap s₀ (2 * n) (Y · ω)) -
      g (levyAsianTrap s₀ n (levyPairSum (Y · ω)))) ^ 2) μ := by
    refine (hi.const_mul (K ^ 2)).mono' (hmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨(memLp_two_iff_integrable_sq hm).2 hint, hsq, ?_⟩
  refine (variance_le_expectation_sq hm).trans ?_
  simp only [Pi.pow_apply]
  exact hsq

/-- `e^{2X_k}` is integrable for independent increments with `E e^{2Y_i} < ∞` (Giles 2015, §6.2): it
is the product of the independent integrable `e^{2Y_i}`, `i < k`. -/
lemma integrable_exp_levyPath_sq {Y : ℕ → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (hint : ∀ i, Integrable (fun ω => Real.exp (Y i ω) ^ 2) μ) (k : ℕ) :
    Integrable (fun ω => Real.exp (levyPath (Y · ω) k) ^ 2) μ := by
  have hind2 : iIndepFun (fun i ω => Real.exp (Y i ω) ^ 2) μ :=
    hind.comp (fun _ x => Real.exp x ^ 2) fun _ => by fun_prop
  have hm : ∀ i, Measurable fun ω => Real.exp (Y i ω) ^ 2 := fun i => (hY i).exp.pow_const 2
  have := hind.isProbabilityMeasure
  have key : ∀ k, Integrable (∏ i ∈ range k, fun ω => Real.exp (Y i ω) ^ 2) μ := by
    intro k
    induction k with
    | zero =>
      rw [Finset.prod_range_zero]
      exact integrable_const (1 : ℝ)
    | succ k ih =>
      rw [Finset.prod_range_succ]
      exact (hind2.indepFun_prod_range_succ hm k).integrable_mul ih (hint k)
  have e : ∀ ω, Real.exp (levyPath (Y · ω) k) ^ 2 =
      (∏ i ∈ range k, fun ω => Real.exp (Y i ω) ^ 2) ω := fun ω => by
    rw [Finset.prod_apply, levyPath, Real.exp_sum, ← Finset.prod_pow]
  simp_rw [e]
  exact key k

/-- The trapezoidal average is square integrable (Giles 2015, §6.2). -/
lemma memLp_levyAsianTrap {Y : ℕ → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (hint : ∀ i, Integrable (fun ω => Real.exp (Y i ω) ^ 2) μ)
    (s₀ : ℝ) (N : ℕ) : MemLp (fun ω => levyAsianTrap s₀ N (Y · ω)) 2 μ := by
  have hX : ∀ k, MemLp (fun ω => Real.exp (levyPath (Y · ω) k)) 2 μ := fun k =>
    (memLp_two_iff_integrable_sq ((measurable_levyPath k).comp
      (measurable_pi_lambda _ hY)).exp.aestronglyMeasurable).2
      (integrable_exp_levyPath_sq hY hind hint k)
  unfold levyAsianTrap
  simp_rw [div_eq_mul_inv]
  refine MemLp.mul_const ?_ _
  exact memLp_finsetSum (range N) (f := fun k ω => (s₀ * Real.exp (levyPath (Y · ω) k) +
    s₀ * Real.exp (levyPath (Y · ω) (k + 1))) * 2⁻¹) fun k _ =>
    ((((hX k).const_mul s₀).add ((hX (k + 1)).const_mul s₀)).mul_const 2⁻¹)

/-- The exponential moments of a convolution multiply (Giles 2015, §6.2: the exponential moments of
independent increments multiply): `∫ e^{θx} d(μ ∗ ν) = ∫ e^{θx} dμ · ∫ e^{θx} dν`. -/
lemma integral_exp_mul_conv (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (θ : ℝ) :
    ∫ x, Real.exp (θ * x) ∂(μ ∗ ν) = (∫ x, Real.exp (θ * x) ∂μ) * ∫ x, Real.exp (θ * x) ∂ν := by
  unfold Measure.conv
  rw [integral_map (measurable_add (M := ℝ)).aemeasurable (by fun_prop)]
  simp_rw [mul_add, Real.exp_add]
  exact integral_prod_mul (fun x => Real.exp (θ * x)) (fun x => Real.exp (θ * x))

/-- The exponential moments on every level of a Lévy process (Giles 2015, §6.2: the increments over
`h_ℓ = T 2^{−ℓ}` with `ν_{ℓ+1} ∗ ν_{ℓ+1} = ν_ℓ`): if `∫ e^{θx} dν_0 = e^{Tκ}`, then
`∫ e^{θx} dν_ℓ = e^{h_ℓ κ}` for every `ℓ`, since `(∫ e^{θx} dν_{ℓ+1})² = ∫ e^{θx} dν_ℓ` and the left
factor is nonnegative. -/
lemma integral_exp_levels (ν : ℕ → Measure ℝ) [∀ ℓ, IsProbabilityMeasure (ν ℓ)]
    (hconv : ∀ ℓ, ν (ℓ + 1) ∗ ν (ℓ + 1) = ν ℓ) {T θ κ : ℝ}
    (h0 : ∫ x, Real.exp (θ * x) ∂ν 0 = Real.exp (T * κ)) (ℓ : ℕ) :
    ∫ x, Real.exp (θ * x) ∂ν ℓ = Real.exp (T / 2 ^ ℓ * κ) := by
  induction ℓ with
  | zero => rw [h0, pow_zero, div_one]
  | succ ℓ ih =>
    have hsq : (∫ x, Real.exp (θ * x) ∂ν (ℓ + 1)) ^ 2 = Real.exp (T / 2 ^ (ℓ + 1) * κ) ^ 2 := by
      rw [sq, ← integral_exp_mul_conv, hconv ℓ, ih, ← Real.exp_nat_mul]
      congr 1
      rw [pow_succ]
      field_simp
      ring
    have hnn : 0 ≤ ∫ x, Real.exp (θ * x) ∂ν (ℓ + 1) :=
      integral_nonneg fun x => (Real.exp_pos _).le
    exact (pow_left_inj₀ hnn (Real.exp_pos _).le two_ne_zero).1 hsq

/-- **Theorem 1 for the Asian option of an exponential Lévy model with exact increments**
(Giles 2015, §6.2, p. 48, l. 2063–2069 and 2078–2079: "directly simulate the increments of the Lévy
process over a set of uniform timesteps … multilevel is still very useful for path-dependent
financial options such as Asian, lookback and barrier options"; "the increments of the driving Lévy
process for the coarse path can be obtained trivially by summing the increments for the fine path";
Table 6.3, l. 2057; Theorem 1 and (2.4), §2.1).  Let `ν_ℓ` be probability laws on `ℝ` with
`ν_{ℓ+1} ∗ ν_{ℓ+1} = ν_ℓ` and `∫ e^{2x} dν_0 < ∞`: the laws of the increments of a Lévy process `X`
over `h_ℓ = T 2^{−ℓ}`, for a horizon `T > 0`, with `E e^{2X_T} < ∞` (the statement does not involve
`T`: every horizon gives the same class of level laws; the exponential moments `∫ e^x dν_ℓ` and
`∫ e^{2x} dν_ℓ` on all levels follow, `integral_exp_levels`).  Level `ℓ` uses `2^ℓ` independent
increments of law `ν_ℓ` and the payoff `P_ℓ = g(A_{2^ℓ})` of the trapezoidal average
(`levyAsianTrap`), `g` `K`-Lipschitz; the coarse payoff of a level-`(ℓ + 1)` sample uses the pair
sums of its increments (`levyPairSum`).  A sample is `w = (w_ℓ)_ℓ`, one increment sequence per level
(law `⊗_ℓ ν_ℓ^{⊗ℕ}`; level `ℓ` only reads `w_ℓ`), the samples are independent, and a level-`ℓ`
sample costs `2^ℓ`.  Then `E[P_ℓ]` converges to some `P`, with `|E[P_ℓ] − P| ≤ c 2^{−ℓ}` (`α = 1`,
from `β = 2` and the telescoping sum), and there is `c₄ > 0` such that for every `0 < ε < e⁻¹`
there are `L` and `N_ℓ ≥ 1` for which the MLMC estimator of `P` has mean square error `< ε²` and
cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²`.  No rate is assumed: `β = 2` (`levy_asian_payoff_sq_le`), (2.4)
(`integral_levyCoarse`) and `α = 1` are proved.  Discrete-time analogue: `P` is the limit of the
level expectations; that it equals `E[g(T⁻¹ ∫₀ᵀ S_t dt)]` for the continuous-time model is not
proved here. -/
theorem levy_asian_theorem1 (ν : ℕ → Measure ℝ) [∀ ℓ, IsProbabilityMeasure (ν ℓ)]
    (hconv : ∀ ℓ, ν (ℓ + 1) ∗ ν (ℓ + 1) = ν ℓ)
    (hexp : Integrable (fun x => Real.exp (2 * x)) (ν 0))
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (s₀ : ℝ) :
    ∃ P : ℝ, Filter.Tendsto (fun ℓ => ∫ y, g (levyAsianTrap s₀ (2 ^ ℓ) y)
        ∂(Measure.infinitePi fun _ : ℕ => ν ℓ)) Filter.atTop (nhds P) ∧
      (∃ c : ℝ, ∀ ℓ : ℕ, |∫ y, g (levyAsianTrap s₀ (2 ^ ℓ) y)
        ∂(Measure.infinitePi fun _ : ℕ => ν ℓ) - P| ≤ c / 2 ^ ℓ) ∧
      ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ)))
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))))
              (fun p x => x p) ℓ (N ℓ) x - P) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ =>
              Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ) < ε ^ 2 ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  -- the exponential moments of level `0`, written as `e^{Tκ₁}` and `e^{Tκ₂}` with `T = 1`
  obtain ⟨T, κ₁, κ₂, hT, h1, h2⟩ : ∃ T κ₁ κ₂ : ℝ, 0 < T ∧
      ∫ x, Real.exp x ∂ν 0 = Real.exp (T * κ₁) ∧
      ∫ x, Real.exp (2 * x) ∂ν 0 = Real.exp (T * κ₂) := by
    have hexp1 : Integrable (fun x : ℝ => Real.exp x) (ν 0) := by
      refine ((memLp_two_iff_integrable_sq
        Real.continuous_exp.aestronglyMeasurable).2 ?_).integrable one_le_two
      simp_rw [exp_sq_eq_exp_two_mul]
      exact hexp
    refine ⟨1, Real.log (∫ x, Real.exp x ∂ν 0), Real.log (∫ x, Real.exp (2 * x) ∂ν 0), one_pos,
      ?_, ?_⟩
    · rw [one_mul, Real.exp_log (integral_exp_pos hexp1)]
    · rw [one_mul, Real.exp_log (integral_exp_pos hexp)]
  obtain ⟨hK, hgc⟩ := continuous_of_abs_sub_le hg
  -- the level laws `μ ℓ = ν_ℓ^{⊗ℕ}` and the coordinates
  have hev : ∀ ℓ i, MeasurePreserving (fun y : ℕ → ℝ => y i)
      (Measure.infinitePi fun _ : ℕ => ν ℓ) (ν ℓ) := fun ℓ i =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => ν ℓ) i
  have hYm : ∀ i, Measurable (fun y : ℕ → ℝ => y i) := fun i => measurable_pi_apply i
  have hYind : ∀ ℓ, iIndepFun (fun i (y : ℕ → ℝ) => y i)
      (Measure.infinitePi fun _ : ℕ => ν ℓ) := fun ℓ =>
    iIndepFun_infinitePi (P := fun _ : ℕ => ν ℓ) (X := fun _ => id) (fun _ => measurable_id)
  -- the exponential moments on every level, from those on level `0` and the convolutions
  have h1' : ∀ ℓ, ∫ x, Real.exp x ∂ν ℓ = Real.exp (T / 2 ^ ℓ * κ₁) := fun ℓ => by
    have h := integral_exp_levels ν hconv (θ := 1) (by simpa using h1) ℓ
    simpa using h
  have h2' : ∀ ℓ, ∫ x, Real.exp (2 * x) ∂ν ℓ = Real.exp (T / 2 ^ ℓ * κ₂) :=
    integral_exp_levels ν hconv h2
  have hm1 : ∀ ℓ i, ∫ y, Real.exp (y i) ∂(Measure.infinitePi fun _ : ℕ => ν ℓ) =
      Real.exp (T / 2 ^ ℓ * κ₁) := fun ℓ i =>
    (integral_comp_of_measurePreserving (hev ℓ i) (f := Real.exp)
      Real.continuous_exp.aestronglyMeasurable).trans (h1' ℓ)
  have hm2 : ∀ ℓ i, ∫ y, Real.exp (2 * y i) ∂(Measure.infinitePi fun _ : ℕ => ν ℓ) =
      Real.exp (T / 2 ^ ℓ * κ₂) := fun ℓ i =>
    (integral_comp_of_measurePreserving (hev ℓ i) (f := fun x => Real.exp (2 * x))
      (by fun_prop)).trans (h2' ℓ)
  have hint : ∀ ℓ i, Integrable (fun y : ℕ → ℝ => Real.exp (y i) ^ 2)
      (Measure.infinitePi fun _ : ℕ => ν ℓ) := fun ℓ i => by
    refine Integrable.of_integral_ne_zero ?_
    simp_rw [exp_sq_eq_exp_two_mul]
    rw [hm2 ℓ i]
    exact (Real.exp_pos _).ne'
  have hA : ∀ ℓ N, MemLp (fun y => g (levyAsianTrap s₀ N y)) 2
      (Measure.infinitePi fun _ : ℕ => ν ℓ) := fun ℓ N =>
    memLp_two_comp_of_abs_sub_le hg (memLp_levyAsianTrap hYm (hYind ℓ) (hint ℓ) s₀ N)
  have hAm : ∀ N, Measurable (fun y => g (levyAsianTrap s₀ N y)) := fun N =>
    hgc.measurable.comp (measurable_levyAsianTrap s₀ N)
  have hps : ∀ ℓ, MeasurePreserving levyPairSum (Measure.infinitePi fun _ : ℕ => ν (ℓ + 1))
      (Measure.infinitePi fun _ : ℕ => ν ℓ) := fun ℓ => measurePreserving_levyPairSum' (hconv ℓ)
  -- the constant of the variance bound
  set Kc := levyAsianConst κ₁ κ₂ T with hKc
  have hKc0 : 0 ≤ Kc := by
    rw [hKc, levyAsianConst]
    positivity
  set M := |K| * |s₀| * Real.sqrt Kc * T with hM
  have hM0 : 0 ≤ M := by positivity
  have hM2 : M ^ 2 = K ^ 2 * s₀ ^ 2 * Kc * T ^ 2 := by
    rw [hM, mul_pow, mul_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hKc0]
  -- `β = 2`: the second moment of the level-`(ℓ + 1)` correction
  have hβ : ∀ ℓ : ℕ, ∫ y, (g (levyAsianTrap s₀ (2 ^ (ℓ + 1)) y) -
      g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y))) ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) ≤ M ^ 2 * ((4 : ℝ) ^ (ℓ + 1))⁻¹ := by
    intro ℓ
    have hTn : 2 * ((2 ^ ℓ : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)) = T := by
      push_cast
      field_simp
      ring
    have h := (levy_asian_payoff_sq_le hYm (hYind (ℓ + 1)) (h := T / 2 ^ (ℓ + 1))
      (by positivity) (hm1 (ℓ + 1)) (hm2 (ℓ + 1)) hg s₀ (n := 2 ^ ℓ) (by positivity) hTn).2.1
    rw [pow_succ' 2 ℓ]
    refine h.trans (le_of_eq ?_)
    have e4 : ((2 : ℝ) ^ (ℓ + 1)) ^ 2 = 4 ^ (ℓ + 1) := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [hM2, div_pow, e4, ← hKc, div_eq_mul_inv]
    ring
  -- the level expectations `E[P_ℓ]` converge, at the rate `α = 1`
  set a : ℕ → ℝ := fun ℓ => ∫ y, g (levyAsianTrap s₀ (2 ^ ℓ) y)
    ∂(Measure.infinitePi fun _ : ℕ => ν ℓ) with ha
  have hAc : ∀ ℓ, MemLp (fun y => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y))) 2
      (Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) := fun ℓ =>
    (hA ℓ _).comp_measurePreserving (hps ℓ)
  have hDm : ∀ ℓ, MemLp (fun y => g (levyAsianTrap s₀ (2 ^ (ℓ + 1)) y) -
      g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y))) 2
      (Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) := fun ℓ => (hA (ℓ + 1) _).sub (hAc ℓ)
  have hdiff : ∀ ℓ, a (ℓ + 1) - a ℓ = ∫ y, (g (levyAsianTrap s₀ (2 ^ (ℓ + 1)) y) -
      g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y)))
        ∂(Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) := by
    intro ℓ
    rw [integral_sub ((hA (ℓ + 1) _).integrable one_le_two) ((hAc ℓ).integrable one_le_two),
      integral_levyCoarse (hconv ℓ) (hAm _).aestronglyMeasurable]
  have hstep : ∀ ℓ, dist (a ℓ) (a (ℓ + 1)) ≤ M / 2 / 2 ^ ℓ := by
    intro ℓ
    rw [dist_comm, Real.dist_eq, hdiff ℓ]
    have hsq := (sq_integral_le_integral_sq_of_memLp (hDm ℓ)).trans (hβ ℓ)
    have e : M ^ 2 * ((4 : ℝ) ^ (ℓ + 1))⁻¹ = (M / 2 / 2 ^ ℓ) ^ 2 := by
      have e4 : (4 : ℝ) ^ (ℓ + 1) = (2 * 2 ^ ℓ) ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm ℓ 2, pow_mul, pow_succ]
        norm_num
        ring
      rw [e4]
      field_simp
    rw [e] at hsq
    exact abs_le_of_sq_le_sq hsq (by positivity)
  obtain ⟨P, hP⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hstep)
  have hbias : ∀ ℓ, |a ℓ - P| ≤ M / 2 ^ ℓ := fun ℓ => by
    rw [← Real.dist_eq]
    exact dist_le_of_le_geometric_two_of_tendsto hstep hP ℓ
  refine ⟨P, hP, ⟨M, hbias⟩, ?_⟩
  -- the input space: one sequence of increments for each level
  have hWev : ∀ ℓ, MeasurePreserving (fun w : ℕ → ℕ → ℝ => w ℓ)
      (Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ)
      (Measure.infinitePi fun _ : ℕ => ν ℓ) := fun ℓ =>
    measurePreserving_eval_infinitePi (fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ) ℓ
  obtain ⟨-, hind, hω⟩ :=
    exists_iid_inputs (Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ)
  have hPfm : ∀ ℓ, Measurable (fun w : ℕ → ℕ → ℝ => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ))) :=
    fun ℓ => (hAm _).comp (measurable_pi_apply ℓ)
  have hPcm : ∀ ℓ, Measurable (fun w : ℕ → ℕ → ℝ =>
      g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))) := fun ℓ =>
    ((hAm _).comp measurable_levyPairSum).comp (measurable_pi_apply (ℓ + 1))
  have hPfL : ∀ ℓ, MemLp (fun w : ℕ → ℕ → ℝ => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ))) 2
      (Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ) := fun ℓ =>
    (hA ℓ _).comp_measurePreserving (hWev ℓ)
  have hPcL : ∀ ℓ, MemLp (fun w : ℕ → ℕ → ℝ =>
      g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))) 2
      (Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ) := fun ℓ =>
    (hAc ℓ).comp_measurePreserving (hWev (ℓ + 1))
  have hPfI : ∀ ℓ, ∫ w, g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ))
      ∂(Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ) = a ℓ := fun ℓ =>
    integral_comp_of_measurePreserving (hWev ℓ) (hAm _).aestronglyMeasurable
  have h24 : ∀ ℓ, ∫ w, g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ))
      ∂(Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ) =
      ∫ w, g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))
      ∂(Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ) := fun ℓ => by
    rw [hPfI, integral_comp_of_measurePreserving (hWev (ℓ + 1))
      (f := fun y => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y)))
      ((hAm _).comp measurable_levyPairSum).aestronglyMeasurable,
      integral_levyCoarse (hconv ℓ) (hAm _).aestronglyMeasurable]
  -- (i): `α = 1`
  have hc₁ : 0 < M + 1 := by linarith
  have h_i : ∀ ℓ : ℕ, |∫ w, g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ)) - (fun _ => P) w
      ∂(Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ)| ≤
      (M + 1) * (2 : ℝ) ^ (-(1 * (ℓ : ℝ))) := by
    intro ℓ
    rw [integral_sub ((hPfL ℓ).integrable one_le_two) (integrable_const P), hPfI, integral_const,
      probReal_univ, one_smul, one_mul, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    calc |a ℓ - P| ≤ M / 2 ^ ℓ := hbias ℓ
      _ ≤ (M + 1) * ((2 : ℝ) ^ ℓ)⁻¹ := by
          rw [div_eq_mul_inv]
          gcongr
          linarith
  -- (iii): `β = 2`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (fineCoarseDiff
      (fun ℓ (w : ℕ → ℕ → ℝ) => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ)))
      (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))) 0)
      (Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ) := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by
    rw [hV₀]
    exact variance_nonneg _ _
  have hc₂ : 0 < V₀ + M ^ 2 + 1 := by positivity
  have h_iii : ∀ ℓ, variance (fineCoarseDiff
      (fun ℓ (w : ℕ → ℕ → ℝ) => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ)))
      (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))) ℓ)
      (Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ) ≤
      (V₀ + M ^ 2 + 1) * (2 : ℝ) ^ (-(2 * (ℓ : ℝ))) := by
    intro ℓ
    rw [two_rpow_neg_two_mul ℓ]
    cases ℓ with
    | zero =>
      rw [← hV₀, pow_zero, inv_one, mul_one]
      nlinarith [sq_nonneg M]
    | succ ℓ =>
      have hm := (measurable_fineCoarseDiff hPfm hPcm (ℓ + 1)).aestronglyMeasurable
        (μ := Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ)
      refine (variance_le_expectation_sq hm).trans ?_
      have hFm : Measurable fun y : ℕ → ℝ => (g (levyAsianTrap s₀ (2 ^ (ℓ + 1)) y) -
          g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y))) ^ 2 :=
        ((hAm _).sub ((hAm _).comp measurable_levyPairSum)).pow_const 2
      have e := integral_comp_of_measurePreserving (hWev (ℓ + 1)) hFm.aestronglyMeasurable
      refine (le_of_eq e).trans ((hβ ℓ).trans ?_)
      have hinv : 0 ≤ ((4 : ℝ) ^ (ℓ + 1))⁻¹ := by positivity
      nlinarith
  -- (iv): a level-`ℓ` sample costs `2^ℓ`
  have h_iv : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ 1 * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, one_mul, Real.rpow_natCast]
  have hαβγ : min (2 : ℝ) 1 / 2 ≤ 1 := by
    rw [min_eq_right (by norm_num : (1 : ℝ) ≤ 2)]
    norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ =>
      Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ => ν ℓ)
    (fun _ => P) (fun ℓ (w : ℕ → ℕ → ℝ) => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ)))
    (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))) (fun p x => x p)
    (fun ℓ _ _ => (2 : ℝ) ^ ℓ) (fun ℓ => (2 : ℝ) ^ ℓ) (α := 1) (β := 2) (γ := 1)
    one_pos two_pos one_pos hc₁ hc₂ one_pos hαβγ hω hind (integrable_const P) hPfm hPcm hPfL
    hPcL h24 (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, ?_, ?_⟩
  · simpa only [integral_const, probReal_univ, one_smul] using hmse
  · simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
      probReal_univ, one_smul] at hcost
    rw [complexityBound_of_lt (by norm_num : (1 : ℝ) < 2) ε] at hcost
    exact hcost

end Main

/-! ### §6.2: an exponential jump-diffusion with exact increments -/

/-- The law of the increment over a time `h ≥ 0` of the jump-diffusion `X_t = bt + σW_t + aN_t`,
where `N` is a Poisson process of rate `λ ≥ 0` independent of the Brownian motion `W` (Giles 2015,
§6.1, p. 47, l. 2013–2015: "finite activity jump-diffusion processes, such as in the Merton model",
here with a constant jump size `a`; §6.2, l. 2063–2064: the increments are simulated exactly over
uniform timesteps): `N(bh, σ²h) ∗ (a·)₊ Poisson(λh)`, the convolution of the Gaussian law and the
image of the Poisson law under `n ↦ an`.  The real parameters `σ²h` and `λh` enter through
`Real.toNNReal`, which is exact when `h ≥ 0` and `λ ≥ 0`, as the theorems assume. -/
noncomputable def jumpDiffLaw (b σ a lam h : ℝ) : Measure ℝ :=
  gaussianReal (b * h) (σ ^ 2 * h).toNNReal ∗
    (poissonMeasure (lam * h).toNNReal).map (fun n : ℕ => a * n)

/-- The law of `aN`, `N` Poisson, is a probability law (Giles 2015, §6.1). -/
lemma isProbabilityMeasure_poissonScaled (a : ℝ) (r : ℝ≥0) :
    IsProbabilityMeasure ((poissonMeasure r).map (fun n : ℕ => a * (n : ℝ))) :=
  Measure.isProbabilityMeasure_map (Measurable.of_discrete).aemeasurable

/-- The jump-diffusion increment law is a probability law (Giles 2015, §6.1). -/
lemma isProbabilityMeasure_jumpDiffLaw (b σ a lam h : ℝ) :
    IsProbabilityMeasure (jumpDiffLaw b σ a lam h) := by
  have := isProbabilityMeasure_poissonScaled a (lam * h).toNNReal
  unfold jumpDiffLaw
  infer_instance

/-- The exponential moments of a Gaussian law: `∫ e^{θx} dN(m, v) = e^{mθ + vθ²/2}` (Giles 2015,
§6.1, the diffusion part). -/
lemma integral_exp_mul_gaussianReal (m : ℝ) (v : ℝ≥0) (θ : ℝ) :
    ∫ x, Real.exp (θ * x) ∂gaussianReal m v = Real.exp (m * θ + v * θ ^ 2 / 2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := m) (v := v)) θ
  simpa [mgf] using h

/-- The exponential moments of the Poisson jumps: `E e^{θaN} = e^{r(e^{θa} − 1)}` for `N` Poisson of
mean `r` (Giles 2015, §6.1, the jump part). -/
lemma integral_exp_mul_poisson (r : ℝ≥0) (a θ : ℝ) :
    ∫ x, Real.exp (θ * x) ∂((poissonMeasure r).map (fun n : ℕ => a * n)) =
      Real.exp (r * (Real.exp (θ * a) - 1)) := by
  rw [integral_map (Measurable.of_discrete).aemeasurable (by fun_prop), integral_poissonMeasure]
  have e : ∀ n : ℕ, (Real.exp (-r) * r ^ n / n.factorial) • Real.exp (θ * (a * n)) =
      Real.exp (-r) * ((r * Real.exp (θ * a)) ^ n / n.factorial) := fun n => by
    rw [smul_eq_mul, mul_pow, ← Real.exp_nat_mul]
    ring_nf
  simp_rw [e]
  rw [tsum_mul_left, (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp (θ * a))).tsum_eq,
    ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
  ring_nf

/-- The exponential moments of the jump-diffusion increment (Giles 2015, §6.2): for `h ≥ 0`,
`E e^{θX_h} = e^{hψ(θ)}` with the Laplace exponent `ψ(θ) = θb + σ²θ²/2 + λ(e^{θa} − 1)`. -/
lemma integral_exp_mul_jumpDiffLaw (b σ a lam : ℝ) (hlam : 0 ≤ lam) {h : ℝ} (hh : 0 ≤ h)
    (θ : ℝ) : ∫ x, Real.exp (θ * x) ∂jumpDiffLaw b σ a lam h =
      Real.exp (h * (θ * b + σ ^ 2 * θ ^ 2 / 2 + lam * (Real.exp (θ * a) - 1))) := by
  have := isProbabilityMeasure_poissonScaled a (lam * h).toNNReal
  unfold jumpDiffLaw
  rw [integral_exp_mul_conv, integral_exp_mul_gaussianReal, integral_exp_mul_poisson,
    ← Real.exp_add, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  ring_nf

/-- `(A ∗ B) ∗ (C ∗ D) = (A ∗ C) ∗ (B ∗ D)` for s-finite measures on `ℝ` (Giles 2015, §6.2:
regrouping the Gaussian and the Poisson factors of two jump-diffusion increments). -/
lemma measure_conv_conv_comm (A B C D : Measure ℝ) [SFinite A] [SFinite B] [SFinite C] [SFinite D] :
    (A ∗ B) ∗ (C ∗ D) = (A ∗ C) ∗ (B ∗ D) := by
  rw [Measure.conv_assoc, ← Measure.conv_assoc B, Measure.conv_comm B C, Measure.conv_assoc C,
    ← Measure.conv_assoc A]

/-- Sums of independent scaled Poisson variables: `(a·)₊Po(r₁) ∗ (a·)₊Po(r₂) = (a·)₊Po(r₁ + r₂)`
(Giles 2015, §6.1). -/
lemma poissonScaled_conv (a : ℝ) (r₁ r₂ : ℝ≥0) :
    (poissonMeasure r₁).map (fun n : ℕ => a * (n : ℝ)) ∗
      (poissonMeasure r₂).map (fun n : ℕ => a * (n : ℝ)) =
      (poissonMeasure (r₁ + r₂)).map (fun n : ℕ => a * (n : ℝ)) := by
  have hL : ((AddMonoidHom.mulLeft a).comp (Nat.castAddMonoidHom ℝ) : ℕ → ℝ) =
      fun n : ℕ => a * (n : ℝ) := rfl
  rw [← hL, ← Measure.map_conv_addMonoidHom _ Measurable.of_discrete,
    poissonMeasure_conv_poissonMeasure]

/-- **The jump-diffusion increments form a convolution semigroup** (Giles 2015, §6.2, p. 48,
l. 2078–2079: "the increments of the driving Lévy process for the coarse path can be obtained
trivially by summing the increments for the fine path").  For the jump-diffusion
`X_t = bt + σW_t + aN_t` with a Poisson rate `λ ≥ 0` and `h₁, h₂ ≥ 0`, the increment over `h₁ + h₂`
has the law of the sum of independent increments over `h₁` and `h₂`:
`jumpDiffLaw b σ a λ h₁ ∗ jumpDiffLaw b σ a λ h₂ = jumpDiffLaw b σ a λ (h₁ + h₂)`, so the pair sums
of the fine increments are exact coarse increments ((2.4) for `jumpDiffusion_asian_theorem1`). -/
theorem jumpDiffLaw_conv (b σ a lam : ℝ) (hlam : 0 ≤ lam) {h₁ h₂ : ℝ} (hh₁ : 0 ≤ h₁)
    (hh₂ : 0 ≤ h₂) :
    jumpDiffLaw b σ a lam h₁ ∗ jumpDiffLaw b σ a lam h₂ = jumpDiffLaw b σ a lam (h₁ + h₂) := by
  have := isProbabilityMeasure_poissonScaled a (lam * h₁).toNNReal
  have := isProbabilityMeasure_poissonScaled a (lam * h₂).toNNReal
  unfold jumpDiffLaw
  rw [measure_conv_conv_comm, gaussianReal_conv_gaussianReal, poissonScaled_conv,
    ← Real.toNNReal_add (by positivity) (by positivity),
    ← Real.toNNReal_add (by positivity) (by positivity), ← mul_add, ← mul_add, ← mul_add]

/-- **Theorem 1 end to end for the Asian option of an exponential jump-diffusion** (Giles 2015,
§6.1, p. 47, l. 2013–2015: "finite activity jump-diffusion processes, such as in the Merton model",
here with a constant jump size; §6.2, p. 48, l. 2063–2064: "directly simulate the increments of the
Lévy process over a set of uniform timesteps (Schoutens 2003), in exactly the same way as one
simulates Brownian increments", and l. 2078–2079; Table 6.3, l. 2057; Theorem 1, §2.1).  For the
jump-diffusion `X_t = bt + σW_t + aN_t` (jumps of size `a` at the times of a Poisson process of rate
`λ ≥ 0`), the price `S = s₀ e^X`, a horizon `T ≥ 0`, and a `K`-Lipschitz payoff `g` of the
trapezoidal average, level `ℓ` simulates the exact increments of `X` over the uniform steps
`h_ℓ = T 2^{−ℓ}` (law `jumpDiffLaw b σ a λ h_ℓ`).  This is the §6.2 approach applied to a
jump-diffusion, not the jump-adapted Euler–Maruyama or Milstein discretisation of §6.1
(l. 2014–2019; for its coupling see `jumpAdapted_random_2_4`): the steps do not depend on the jump
times, and there is no discretisation error between the grid points.  The conclusion of
`levy_asian_theorem1` holds: the level expectations converge to some `P` at the rate
`|E[P_ℓ] − P| ≤ c 2^{−ℓ}`, and the MLMC estimator of `P` reaches mean square error `< ε²` at cost
`O(ε⁻²)`.  Every hypothesis of `levy_asian_theorem1` is proved: the convolution property
(`jumpDiffLaw_conv`) and `E e^{2X_T} = e^{T(2b + 2σ² + λ(e^{2a} − 1))} < ∞`
(`integral_exp_mul_jumpDiffLaw`).  As in `levy_asian_theorem1`, `P` is the limit of the level
expectations (the continuous-time average is not formalised). -/
theorem jumpDiffusion_asian_theorem1 (b σ a lam : ℝ) (hlam : 0 ≤ lam) {T : ℝ} (hT : 0 ≤ T)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (s₀ : ℝ) :
    ∃ P : ℝ, Filter.Tendsto (fun ℓ => ∫ y, g (levyAsianTrap s₀ (2 ^ ℓ) y)
        ∂(Measure.infinitePi fun _ : ℕ => jumpDiffLaw b σ a lam (T / 2 ^ ℓ))) Filter.atTop
        (nhds P) ∧
      (∃ c : ℝ, ∀ ℓ : ℕ, |∫ y, g (levyAsianTrap s₀ (2 ^ ℓ) y)
        ∂(Measure.infinitePi fun _ : ℕ => jumpDiffLaw b σ a lam (T / 2 ^ ℓ)) - P| ≤ c / 2 ^ ℓ) ∧
      ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ)))
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))))
              (fun p x => x p) ℓ (N ℓ) x - P) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ =>
              Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ =>
                jumpDiffLaw b σ a lam (T / 2 ^ ℓ)) < ε ^ 2 ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  have hP : ∀ ℓ : ℕ, IsProbabilityMeasure (jumpDiffLaw b σ a lam (T / 2 ^ ℓ)) := fun ℓ =>
    isProbabilityMeasure_jumpDiffLaw _ _ _ _ _
  have hconv : ∀ ℓ : ℕ, jumpDiffLaw b σ a lam (T / 2 ^ (ℓ + 1)) ∗
      jumpDiffLaw b σ a lam (T / 2 ^ (ℓ + 1)) = jumpDiffLaw b σ a lam (T / 2 ^ ℓ) := fun ℓ => by
    rw [jumpDiffLaw_conv b σ a lam hlam (by positivity) (by positivity)]
    congr 1
    rw [pow_succ]
    field_simp
    ring
  have h2 : Integrable (fun x => Real.exp (2 * x)) (jumpDiffLaw b σ a lam (T / 2 ^ 0)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [integral_exp_mul_jumpDiffLaw b σ a lam hlam (by positivity)]
    exact (Real.exp_pos _).ne'
  exact levy_asian_theorem1 (fun ℓ => jumpDiffLaw b σ a lam (T / 2 ^ ℓ)) hconv h2 hg s₀

/-! ### §6.1: the Brownian path on grids of any length -/

/-- Mixing over independent data (Giles 2015, §6.1, for random jump times): if `Φ(a, ·)` and
`Ψ(a, ·)` push `Q` forward to the same law for every `a`, then `(a, z) ↦ (a, Φ(a, z))` and
`(a, z) ↦ (a, Ψ(a, z))` push `P ⊗ Q` forward to the same law. -/
lemma map_prodMk_eq_of_map_eq {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (P : Measure α) (Q : Measure β) [SFinite Q] {Φ Ψ : α → β → γ}
    (hΦ : Measurable (Function.uncurry Φ)) (hΨ : Measurable (Function.uncurry Ψ))
    (h : ∀ a, Q.map (Φ a) = Q.map (Ψ a)) :
    (P.prod Q).map (fun p => (p.1, Φ p.1 p.2)) = (P.prod Q).map (fun p => (p.1, Ψ p.1 p.2)) := by
  have hF : Measurable fun p : α × β => (p.1, Φ p.1 p.2) := measurable_fst.prodMk hΦ
  have hG : Measurable fun p : α × β => (p.1, Ψ p.1 p.2) := measurable_fst.prodMk hΨ
  ext s hs
  rw [Measure.map_apply hF hs, Measure.map_apply hG hs, Measure.prod_apply (hF hs),
    Measure.prod_apply (hG hs)]
  refine lintegral_congr fun a => ?_
  have hΦa : Measurable (Φ a) := hΦ.comp measurable_prodMk_left
  have hΨa : Measurable (Ψ a) := hΨ.comp measurable_prodMk_left
  have hsa : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
  have e1 : Prod.mk a ⁻¹' ((fun p : α × β => (p.1, Φ p.1 p.2)) ⁻¹' s) =
      Φ a ⁻¹' (Prod.mk a ⁻¹' s) := rfl
  have e2 : Prod.mk a ⁻¹' ((fun p : α × β => (p.1, Ψ p.1 p.2)) ⁻¹' s) =
      Ψ a ⁻¹' (Prod.mk a ⁻¹' s) := rfl
  rw [e1, e2, ← Measure.map_apply hΦa hsa, ← Measure.map_apply hΨa hsa, h a]

/-- **The Brownian increments of a path on a union grid have the single-level law, for grids of any
length** (Giles 2015, §5.6, p. 44, l. 1926–1929: "The underlying Brownian path needs to be sampled
at a set of times which are the union of the simulation times used by the coarse and fine path. The
independent Brownian increments can be simulated for each time interval, and summed to give `W(t)`
at the required times"; in §6.1, p. 47, l. 2020–2025, the grids also contain the jump times).  With
`Z ~ N(0,1)^{⊗ℕ}` (`stdNormalSeq`), a monotone union grid `u` and monotone indices `τ` of the times
`t_j = u_{τ(j)}` of one path, the increments `W(t_{j+1}) − W(t_j)`, `j ∈ ℕ` (`unionGridBM`), have
the law of the increments `√(t_{j+1} − t_j) Z_j` simulated on the path's own grid.  Unlike in
`unionGridBM_map_eq` the number of steps is not part of the type (a finite grid is extended by
constant times, which give zero increments), so the grids may depend on random jump times
(`jumpAdapted_map_eq`). -/
theorem unionGridBM_map_eq_nat {u : ℕ → ℝ} (hu : Monotone u) {τ : ℕ → ℕ} (hτ : Monotone τ) :
    stdNormalSeq.map (fun z (j : ℕ) => unionGridBM u z (τ (j + 1)) - unionGridBM u z (τ j)) =
      stdNormalSeq.map (fun z j => Real.sqrt (u (τ (j + 1)) - u (τ j)) * z j) := by
  have hind : iIndepFun (fun i (z : ℕ → ℝ) => z i) stdNormalSeq :=
    iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ => id)
      (fun _ => measurable_id)
  have hlaw : ∀ i, HasLaw (fun z : ℕ → ℝ => z i) (gaussianReal 0 1) stdNormalSeq := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable,
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i).map_eq⟩
  have hindX : iIndepFun (fun i (z : ℕ → ℝ) => Real.sqrt (u (i + 1) - u i) * z i)
      stdNormalSeq := hind.comp (fun i x => Real.sqrt (u (i + 1) - u i) * x) fun _ => by fun_prop
  have hX : ∀ i, HasLaw (fun z : ℕ → ℝ => Real.sqrt (u (i + 1) - u i) * z i)
      (gaussianReal 0 (u (i + 1) - u i).toNNReal) stdNormalSeq := fun i =>
    hasLaw_sqrt_mul (sub_nonneg.2 (hu (Nat.le_succ i))) (hlaw i)
  have hdisj : Pairwise (Function.onFun Disjoint fun j : ℕ => Ico (τ j) (τ (j + 1))) := by
    intro j l hjl
    rcases lt_or_gt_of_ne hjl with h | h
    · exact Finset.disjoint_left.2 fun i hi hi' => by
        have := hτ (show j + 1 ≤ l by omega)
        simp only [Finset.mem_Ico] at hi hi'
        omega
    · exact Finset.disjoint_left.2 fun i hi hi' => by
        have := hτ (show l + 1 ≤ j by omega)
        simp only [Finset.mem_Ico] at hi hi'
        omega
  obtain ⟨h1, h2⟩ := iIndepFun_blockSum hindX hX _ hdisj
  have e : ∀ (z : ℕ → ℝ) (j : ℕ), unionGridBM u z (τ (j + 1)) - unionGridBM u z (τ j) =
      ∑ i ∈ Ico (τ j) (τ (j + 1)), Real.sqrt (u (i + 1) - u i) * z i := fun z j =>
    unionGridBM_sub_eq_sum u z (hτ (Nat.le_succ j))
  have hL : HasLaw (fun (z : ℕ → ℝ) (j : ℕ) =>
      ∑ i ∈ Ico (τ j) (τ (j + 1)), Real.sqrt (u (i + 1) - u i) * z i)
      (Measure.infinitePi fun j => gaussianReal 0 (u (τ (j + 1)) - u (τ j)).toNNReal)
      stdNormalSeq := by
    refine h1.hasLaw_infinitePi (fun j => ?_) (Measurable.aemeasurable ?_)
    · have h2j := h2 j
      rw [Finset.sum_const_zero, sum_toNNReal_Ico hu (hτ (Nat.le_succ j))] at h2j
      exact h2j
    · exact measurable_pi_lambda _ fun j => Finset.measurable_sum _ fun i _ =>
        (measurable_pi_apply i).const_mul _
  have hR : HasLaw (fun (z : ℕ → ℝ) (j : ℕ) => Real.sqrt (u (τ (j + 1)) - u (τ j)) * z j)
      (Measure.infinitePi fun j => gaussianReal 0 (u (τ (j + 1)) - u (τ j)).toNNReal)
      stdNormalSeq := by
    refine (hind.comp (fun j x => Real.sqrt (u (τ (j + 1)) - u (τ j)) * x)
      fun _ => by fun_prop).hasLaw_infinitePi (fun j => hasLaw_sqrt_mul
        (sub_nonneg.2 (hu (hτ (Nat.le_succ j)))) (hlaw j)) (Measurable.aemeasurable ?_)
    exact measurable_pi_lambda _ fun j => (measurable_pi_apply j).const_mul _
  simp_rw [e]
  rw [hL.map_eq, hR.map_eq]

/-! ### §6.1: jump-adapted grids with a constant jump rate -/

/-- The jump-adapted time grid of a level with step `h` (Giles 2015, §6.1, p. 47, l. 2014–2019: "a
jump-adapted discretisation … in which the Brownian diffusion between each jump is approximated
using an Euler-Maruyama or Milstein approximation, and then each jump is simulated exactly"): the
uniform times `k h`, `k = 0, …, N`, together with the jump times `J`. -/
noncomputable def jumpGrid (h : ℝ) (N : ℕ) (J : Finset ℝ) : Finset ℝ :=
  (range (N + 1)).image (fun k : ℕ => (k : ℝ) * h) ∪ J

/-- The coarse jump-adapted grid (step `2h`, `n` steps) is part of the fine one (step `h`, `2n`
steps), for the same jump times (Giles 2015, §6.1, l. 2020–2022). -/
lemma jumpGrid_coarse_subset (h : ℝ) (n : ℕ) (J : Finset ℝ) :
    jumpGrid (2 * h) n J ⊆ jumpGrid h (2 * n) J := by
  intro t ht
  simp only [jumpGrid, Finset.mem_union, Finset.mem_image, Finset.mem_range] at ht ⊢
  rcases ht with ⟨k, hk, rfl⟩ | hJ
  · exact Or.inl ⟨2 * k, by omega, by push_cast; ring⟩
  · exact Or.inr hJ

/-- The jump times lie on the jump-adapted grid of every level (Giles 2015, §6.1, l. 2020–2022). -/
lemma subset_jumpGrid (h : ℝ) (N : ℕ) (J : Finset ℝ) : J ⊆ jumpGrid h N J :=
  Finset.subset_union_right

/-- The jumps occur at the same times on the coarse and the fine path (Giles 2015, §6.1, p. 47,
l. 2020–2022: "for each stochastic sample ω the jumps on the coarse and fine paths will occur at the
same time").  The jump times `J` lie on the fine grid (step `h`, `2n` steps) and on the coarse grid
(step `2h`, `n` steps), and the coarse grid is part of the fine one, so the Brownian increments of
the coarse path are sums of those of the fine path.  This holds by construction: both levels use
the same jump times `J` (`subset_jumpGrid`), and `k · 2h = (2k) · h` (`jumpGrid_coarse_subset`).
The paper's point, that with a constant rate the jump times do not depend on the path (unlike with
thinning), is built into the model, not proved. -/
lemma jumpGrid_coupling (h : ℝ) (n : ℕ) (J : Finset ℝ) :
    J ⊆ jumpGrid h (2 * n) J ∧ J ⊆ jumpGrid (2 * h) n J ∧
      jumpGrid (2 * h) n J ⊆ jumpGrid h (2 * n) J :=
  ⟨subset_jumpGrid h (2 * n) J, subset_jumpGrid (2 * h) n J, jumpGrid_coarse_subset h n J⟩

/-- The times of a finite grid `F` with `K + 1` points in increasing order, `t_0 < ⋯ < t_K`,
extended by `t_i = t_K` for `i > K` (Giles 2015, §5.6 and §6.1: a grid as a monotone sequence of
times, as `unionGridBM` takes it). -/
noncomputable def gridSeq (F : Finset ℝ) {K : ℕ} (hF : F.card = K + 1) (i : ℕ) : ℝ :=
  F.orderEmbOfFin hF ⟨min i K, Nat.lt_succ_of_le (min_le_right i K)⟩

/-- The index, in the increasing enumeration of the grid `F`, of the `c`-th time of the grid `C`
(Giles 2015, §6.1: where the coarse times lie on the fine jump-adapted grid); for `C ⊆ F`,
`gridSeq F (gridIdx C F c)` is the `c`-th time of `C` (`gridSeq_gridIdx`). -/
noncomputable def gridIdx (C F : Finset ℝ) {Kc : ℕ} (hC : C.card = Kc + 1) (c : Fin (Kc + 1)) :
    ℕ :=
  (F.sort).idxOf (C.orderEmbOfFin hC c)

/-- The enumeration of a grid is monotone (Giles 2015, §6.1). -/
lemma gridSeq_mono (F : Finset ℝ) {K : ℕ} (hF : F.card = K + 1) : Monotone (gridSeq F hF) :=
  fun i j hij => (F.orderEmbOfFin hF).monotone (by
    simp only [Fin.mk_le_mk]
    exact min_le_min_right _ hij)

/-- For `C ⊆ F`, `gridIdx` is the inverse of the enumeration of `F` at the times of `C` (Giles 2015,
§6.1). -/
lemma gridIdx_eq {C F : Finset ℝ} (hCF : C ⊆ F) {Kc Kf : ℕ} (hC : C.card = Kc + 1)
    (hF : F.card = Kf + 1) (c : Fin (Kc + 1)) :
    gridIdx C F hC c = ((F.orderIsoOfFin hF).symm
      ⟨C.orderEmbOfFin hC c, hCF (C.orderEmbOfFin_mem hC c)⟩ : Fin (Kf + 1)) :=
  (Finset.orderIsoOfFin_symm_apply F hF
    ⟨C.orderEmbOfFin hC c, hCF (C.orderEmbOfFin_mem hC c)⟩).symm

/-- For `C ⊆ F`, the indices of the times of `C` in `F` increase (Giles 2015, §6.1). -/
lemma gridIdx_mono {C F : Finset ℝ} (hCF : C ⊆ F) {Kc Kf : ℕ} (hC : C.card = Kc + 1)
    (hF : F.card = Kf + 1) : Monotone (gridIdx C F hC) := fun c c' hcc' => by
  rw [gridIdx_eq hCF hC hF, gridIdx_eq hCF hC hF]
  exact (F.orderIsoOfFin hF).symm.monotone (show
    (⟨C.orderEmbOfFin hC c, hCF (C.orderEmbOfFin_mem hC c)⟩ : F) ≤
      ⟨C.orderEmbOfFin hC c', hCF (C.orderEmbOfFin_mem hC c')⟩ from
    (C.orderEmbOfFin hC).monotone hcc')

/-- For `C ⊆ F`, the `gridIdx C F c`-th time of `F` is the `c`-th time of `C` (Giles 2015, §6.1). -/
lemma gridSeq_gridIdx {C F : Finset ℝ} (hCF : C ⊆ F) {Kc Kf : ℕ} (hC : C.card = Kc + 1)
    (hF : F.card = Kf + 1) (c : Fin (Kc + 1)) :
    gridSeq F hF (gridIdx C F hC c) = C.orderEmbOfFin hC c := by
  rw [gridIdx_eq hCF hC hF]
  set x := (F.orderIsoOfFin hF).symm ⟨C.orderEmbOfFin hC c, hCF (C.orderEmbOfFin_mem hC c)⟩
    with hx
  have hxK : (x : ℕ) ≤ Kf := Nat.lt_succ_iff.1 x.2
  unfold gridSeq
  have e : (⟨min (x : ℕ) Kf, Nat.lt_succ_of_le (min_le_right _ Kf)⟩ : Fin (Kf + 1)) = x :=
    Fin.ext (min_eq_left hxK)
  rw [e, ← Finset.coe_orderIsoOfFin_apply, hx, OrderIso.apply_symm_apply]

/-- **Jump-adapted grids with a constant jump rate, conditionally on the jump times** (Giles 2015,
§6.1, p. 47, l. 2020–2025: "the extension of the multilevel method is straightforward with the
coarse and fine paths using the same underlying Brownian paths, and the same random variables to
determine the jump times and strengths"; via §5.6, l. 1926–1929).  Let `J` be the (fixed, finite)
set of jump times, the fine grid `jumpGrid h (2n) J` (`K_f + 1` times) and the coarse grid
`jumpGrid (2h) n J` (`K_c + 1` times).  The fine path's Brownian increments are `√Δt Z_i` on the
fine grid (`unionGridBM` with the enumeration `gridSeq` of the fine grid), and the coarse path uses
their sums over its own steps.  Then the coarse increments have the law of the increments
`√Δt^c Z_j` simulated on the coarse jump-adapted grid alone, which is the level below: with the same
jump times and strengths for both paths, (2.4) `E[P^f_ℓ] = E[P^c_ℓ]` holds conditionally on the jump
times.  For random jump times see `jumpAdapted_random_2_4`. -/
theorem jumpAdapted_coarse_map_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : ℕ → Ω → ℝ} (hZ : iIndepFun Z μ) (hZ1 : ∀ i, HasLaw (Z i) (gaussianReal 0 1) μ)
    (h : ℝ) (n : ℕ) (J : Finset ℝ) {Kc Kf : ℕ} (hC : (jumpGrid (2 * h) n J).card = Kc + 1)
    (hF : (jumpGrid h (2 * n) J).card = Kf + 1) :
    μ.map (fun ω (j : Fin Kc) =>
        unionGridBM (gridSeq (jumpGrid h (2 * n) J) hF) (Z · ω)
          (gridIdx (jumpGrid (2 * h) n J) (jumpGrid h (2 * n) J) hC j.succ) -
        unionGridBM (gridSeq (jumpGrid h (2 * n) J) hF) (Z · ω)
          (gridIdx (jumpGrid (2 * h) n J) (jumpGrid h (2 * n) J) hC j.castSucc)) =
      μ.map (fun ω (j : Fin Kc) => Real.sqrt ((jumpGrid (2 * h) n J).orderEmbOfFin hC j.succ -
        (jumpGrid (2 * h) n J).orderEmbOfFin hC j.castSucc) * Z j ω) := by
  have hCF := jumpGrid_coarse_subset h n J
  rw [unionGridBM_map_eq hZ hZ1 (gridSeq_mono _ hF) (gridIdx_mono hCF hC hF)]
  simp_rw [gridSeq_gridIdx hCF hC hF]

section JumpAdapted

variable {E : Type*} [MeasurableSpace E]

/-- The union-grid Brownian path is jointly measurable in the grid data and the normal variates
(Giles 2015, §6.1, random jump-adapted grids). -/
lemma measurable_unionGridBM_data {u : E → ℕ → ℝ} (hum : Measurable u) {κ : E → ℕ}
    (hκ : Measurable κ) : Measurable fun p : E × (ℕ → ℝ) => unionGridBM (u p.1) p.2 (κ p.1) := by
  have hG : Measurable fun q : (E × (ℕ → ℝ)) × ℕ => unionGridBM (u q.1.1) q.1.2 q.2 := by
    refine measurable_from_prod_countable_left fun k => ?_
    show Measurable fun p : E × (ℕ → ℝ) => unionGridBM (u p.1) p.2 k
    unfold unionGridBM
    refine Finset.measurable_sum (range k) fun i _ => ?_
    have h1 : Measurable fun p : E × (ℕ → ℝ) => u p.1 (i + 1) :=
      (measurable_pi_apply (i + 1)).comp (hum.comp measurable_fst)
    have h2 : Measurable fun p : E × (ℕ → ℝ) => u p.1 i :=
      (measurable_pi_apply i).comp (hum.comp measurable_fst)
    have h3 : Measurable fun p : E × (ℕ → ℝ) => p.2 i := (measurable_pi_apply i).comp measurable_snd
    exact (h1.sub h2).sqrt.mul h3
  exact hG.comp (measurable_id.prodMk (hκ.comp measurable_fst))

/-- A grid time with a random index is measurable in the grid data (Giles 2015, §6.1). -/
lemma measurable_grid_data {u : E → ℕ → ℝ} (hum : Measurable u) {κ : E → ℕ}
    (hκ : Measurable κ) : Measurable fun r => u r (κ r) := by
  have hG : Measurable fun q : E × ℕ => u q.1 q.2 :=
    measurable_from_prod_countable_left fun k => (measurable_pi_apply k).comp hum
  exact hG.comp (measurable_id.prodMk hκ)

/-- A law equal to `stdNormalSeq` is the image of a probability measure under an a.e.-measurable
map (Giles 2015, §6.1: the normal variates driving the Brownian path): if `μ.map Z = stdNormalSeq`,
then `Z` is a.e.-measurable (otherwise the image would be `0`) and `μ` is a probability measure. -/
lemma aemeasurable_of_map_eq_stdNormalSeq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : Ω → ℕ → ℝ} (hZlaw : μ.map Z = stdNormalSeq) :
    AEMeasurable Z μ ∧ IsProbabilityMeasure μ := by
  have hZ : AEMeasurable Z μ := by
    by_contra hZ
    have h1 : stdNormalSeq (Set.univ : Set (ℕ → ℝ)) = 1 := measure_univ
    rw [← hZlaw, Measure.map_of_not_aemeasurable hZ] at h1
    simp at h1
  refine ⟨hZ, ⟨?_⟩⟩
  have h1 : μ.map Z Set.univ = 1 := by
    rw [hZlaw]
    exact measure_univ
  rwa [Measure.map_apply_of_aemeasurable hZ MeasurableSet.univ, Set.preimage_univ] at h1

/-- **Random grids independent of the Brownian path: the coarse path has the single-level law**
(Giles 2015, §6.1, p. 47, l. 2020–2025: "If the jump activity rate is constant, then for each
stochastic sample ω the jumps on the coarse and fine paths will occur at the same time, and
therefore the extension of the multilevel method is straightforward with the coarse and fine paths
using the same underlying Brownian paths, and the same random variables to determine the jump times
and strengths").  The jump data `R` (jump times and strengths of a constant-rate jump process, with
values in a measurable space `E`) is independent of the standard normal variates `Z`
(`μ.map Z = stdNormalSeq`, which makes `μ` a probability measure and `Z` a.e.-measurable) that
drive the Brownian path.  The union grid `u(R)` (for jump-adapted grids: the fine grid, which
contains the coarse one) and the indices `τ(R)` of the coarse times in it are measurable functions
of `R`, with monotone values.  Then (jump data, coarse Brownian increments obtained by summing the
union-grid increments) has the joint law of (jump data, increments `√Δt Z_j` simulated on the
coarse grid alone).  For the jump-adapted grids these hypotheses are proved in
`jumpAdapted_random_map_eq`. -/
theorem jumpAdapted_map_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {R : Ω → E} {Z : Ω → ℕ → ℝ} (hR : Measurable R) (hZlaw : μ.map Z = stdNormalSeq)
    (hRZ : IndepFun R Z μ) {u : E → ℕ → ℝ} {τ : E → ℕ → ℕ} (hum : Measurable u)
    (hτm : Measurable τ) (hu : ∀ r, Monotone (u r)) (hτ : ∀ r, Monotone (τ r)) :
    μ.map (fun ω => (R ω, fun j => unionGridBM (u (R ω)) (Z ω) (τ (R ω) (j + 1)) -
        unionGridBM (u (R ω)) (Z ω) (τ (R ω) j))) =
      μ.map (fun ω => (R ω, fun j =>
        Real.sqrt (u (R ω) (τ (R ω) (j + 1)) - u (R ω) (τ (R ω) j)) * Z ω j)) := by
  obtain ⟨hZ, hμ⟩ := aemeasurable_of_map_eq_stdNormalSeq hZlaw
  have hΦ : Measurable (Function.uncurry fun (r : E) (z : ℕ → ℝ) (j : ℕ) =>
      unionGridBM (u r) z (τ r (j + 1)) - unionGridBM (u r) z (τ r j)) :=
    measurable_pi_lambda _ fun j =>
      (measurable_unionGridBM_data hum ((measurable_pi_apply (j + 1)).comp hτm)).sub
        (measurable_unionGridBM_data hum ((measurable_pi_apply j).comp hτm))
  have hΨ : Measurable (Function.uncurry fun (r : E) (z : ℕ → ℝ) (j : ℕ) =>
      Real.sqrt (u r (τ r (j + 1)) - u r (τ r j)) * z j) := by
    refine measurable_pi_lambda _ fun j => ?_
    have h1 : Measurable fun p : E × (ℕ → ℝ) => u p.1 (τ p.1 (j + 1)) :=
      (measurable_grid_data hum ((measurable_pi_apply (j + 1)).comp hτm)).comp measurable_fst
    have h2 : Measurable fun p : E × (ℕ → ℝ) => u p.1 (τ p.1 j) :=
      (measurable_grid_data hum ((measurable_pi_apply j).comp hτm)).comp measurable_fst
    exact (h1.sub h2).sqrt.mul ((measurable_pi_apply j).comp measurable_snd)
  have hjoint : μ.map (fun ω => (R ω, Z ω)) = (μ.map R).prod stdNormalSeq := by
    rw [← hZlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hR.aemeasurable hZ).1 hRZ
  have hRZm : AEMeasurable (fun ω => (R ω, Z ω)) μ := hR.aemeasurable.prodMk hZ
  have hΦ' : Measurable fun p : E × (ℕ → ℝ) => (p.1, fun j =>
      unionGridBM (u p.1) p.2 (τ p.1 (j + 1)) - unionGridBM (u p.1) p.2 (τ p.1 j)) :=
    measurable_fst.prodMk hΦ
  have hΨ' : Measurable fun p : E × (ℕ → ℝ) => (p.1, fun j =>
      Real.sqrt (u p.1 (τ p.1 (j + 1)) - u p.1 (τ p.1 j)) * p.2 j) :=
    measurable_fst.prodMk hΨ
  calc μ.map (fun ω => (R ω, fun j => unionGridBM (u (R ω)) (Z ω) (τ (R ω) (j + 1)) -
        unionGridBM (u (R ω)) (Z ω) (τ (R ω) j)))
      = (μ.map (fun ω => (R ω, Z ω))).map (fun p => (p.1, fun j =>
          unionGridBM (u p.1) p.2 (τ p.1 (j + 1)) - unionGridBM (u p.1) p.2 (τ p.1 j))) := by
        rw [AEMeasurable.map_map_of_aemeasurable hΦ'.aemeasurable hRZm]
        rfl
    _ = (μ.map (fun ω => (R ω, Z ω))).map (fun p => (p.1, fun j =>
          Real.sqrt (u p.1 (τ p.1 (j + 1)) - u p.1 (τ p.1 j)) * p.2 j)) := by
        rw [hjoint]
        exact map_prodMk_eq_of_map_eq _ _ hΦ hΨ fun r => unionGridBM_map_eq_nat (hu r) (hτ r)
    _ = _ := by
        rw [AEMeasurable.map_map_of_aemeasurable hΨ'.aemeasurable hRZm]
        rfl

/-- **(2.4) for random grids independent of the Brownian path** (Giles 2015, §6.1, p. 47,
l. 2020–2025, with (2.4), §2.1, p. 8, l. 378–382: "Provided we maintain the identity
`E[P^f_ℓ] = E[P^c_ℓ]` so that the expectation on level `ℓ` is the same for the two
approximations").  In the setting of `jumpAdapted_map_eq`, for every measurable payoff `F(r, ΔW)` of
the jump data and of the Brownian increments of the coarse path (for instance an Euler–Maruyama or
Milstein path between the jumps, the jumps simulated exactly from `r`), the coarse approximation of
a level-`(ℓ + 1)` sample is integrable iff the level-`ℓ` approximation simulated on its own grid is,
and they have the same expectation: `E[F(R, ΔW^c)] = E[F(R, √Δt Z)]`.  For the jump-adapted grids
see `jumpAdapted_random_2_4`. -/
theorem jumpAdapted_2_4 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {R : Ω → E} {Z : Ω → ℕ → ℝ} (hR : Measurable R) (hZlaw : μ.map Z = stdNormalSeq)
    (hRZ : IndepFun R Z μ) {u : E → ℕ → ℝ} {τ : E → ℕ → ℕ} (hum : Measurable u)
    (hτm : Measurable τ) (hu : ∀ r, Monotone (u r)) (hτ : ∀ r, Monotone (τ r))
    {F : E → (ℕ → ℝ) → ℝ} (hF : Measurable (Function.uncurry F)) :
    (Integrable (fun ω => F (R ω) (fun j => unionGridBM (u (R ω)) (Z ω) (τ (R ω) (j + 1)) -
        unionGridBM (u (R ω)) (Z ω) (τ (R ω) j))) μ ↔
      Integrable (fun ω => F (R ω) (fun j =>
        Real.sqrt (u (R ω) (τ (R ω) (j + 1)) - u (R ω) (τ (R ω) j)) * Z ω j)) μ) ∧
    ∫ ω, F (R ω) (fun j => unionGridBM (u (R ω)) (Z ω) (τ (R ω) (j + 1)) -
        unionGridBM (u (R ω)) (Z ω) (τ (R ω) j)) ∂μ =
      ∫ ω, F (R ω) (fun j =>
        Real.sqrt (u (R ω) (τ (R ω) (j + 1)) - u (R ω) (τ (R ω) j)) * Z ω j) ∂μ := by
  have h := jumpAdapted_map_eq hR hZlaw hRZ hum hτm hu hτ
  have hRZm : AEMeasurable (fun ω => (R ω, Z ω)) μ :=
    hR.aemeasurable.prodMk (aemeasurable_of_map_eq_stdNormalSeq hZlaw).1
  have hm1 : AEMeasurable (fun ω => (R ω, fun j =>
      unionGridBM (u (R ω)) (Z ω) (τ (R ω) (j + 1)) -
        unionGridBM (u (R ω)) (Z ω) (τ (R ω) j))) μ := by
    refine Measurable.comp_aemeasurable (f := fun ω => (R ω, Z ω))
      (g := fun p : E × (ℕ → ℝ) => (p.1, fun j =>
        unionGridBM (u p.1) p.2 (τ p.1 (j + 1)) - unionGridBM (u p.1) p.2 (τ p.1 j))) ?_ hRZm
    exact measurable_fst.prodMk (measurable_pi_lambda _ fun j =>
      (measurable_unionGridBM_data hum ((measurable_pi_apply (j + 1)).comp hτm)).sub
        (measurable_unionGridBM_data hum ((measurable_pi_apply j).comp hτm)))
  have hm2 : AEMeasurable (fun ω => (R ω, fun j =>
      Real.sqrt (u (R ω) (τ (R ω) (j + 1)) - u (R ω) (τ (R ω) j)) * Z ω j)) μ := by
    refine Measurable.comp_aemeasurable (f := fun ω => (R ω, Z ω))
      (g := fun p : E × (ℕ → ℝ) => (p.1, fun j =>
        Real.sqrt (u p.1 (τ p.1 (j + 1)) - u p.1 (τ p.1 j)) * p.2 j)) ?_ hRZm
    refine measurable_fst.prodMk (measurable_pi_lambda _ fun j => ?_)
    have h1 : Measurable fun p : E × (ℕ → ℝ) => u p.1 (τ p.1 (j + 1)) :=
      (measurable_grid_data hum ((measurable_pi_apply (j + 1)).comp hτm)).comp measurable_fst
    have h2 : Measurable fun p : E × (ℕ → ℝ) => u p.1 (τ p.1 j) :=
      (measurable_grid_data hum ((measurable_pi_apply j).comp hτm)).comp measurable_fst
    exact (h1.sub h2).sqrt.mul ((measurable_pi_apply j).comp measurable_snd)
  have i1 := integrable_map_measure (g := Function.uncurry F) hF.aestronglyMeasurable hm1
  have i2 := integrable_map_measure (g := Function.uncurry F) hF.aestronglyMeasurable hm2
  rw [h] at i1
  refine ⟨i1.symm.trans i2, ?_⟩
  calc _ = ∫ p, Function.uncurry F p ∂(μ.map fun ω => (R ω, fun j =>
          unionGridBM (u (R ω)) (Z ω) (τ (R ω) (j + 1)) -
            unionGridBM (u (R ω)) (Z ω) (τ (R ω) j))) :=
        (integral_map hm1 hF.aestronglyMeasurable).symm
    _ = ∫ p, Function.uncurry F p ∂(μ.map fun ω => (R ω, fun j =>
          Real.sqrt (u (R ω) (τ (R ω) (j + 1)) - u (R ω) (τ (R ω) j)) * Z ω j)) := by rw [h]
    _ = _ := integral_map hm2 hF.aestronglyMeasurable

end JumpAdapted

/-! ### §6.1: jump-adapted grids with random jump times -/

/-- The times of a jump-adapted grid before sorting (Giles 2015, §6.1, p. 47, l. 2014–2019: "a
jump-adapted discretisation … in which the Brownian diffusion between each jump is approximated
using an Euler-Maruyama or Milstein approximation"): the `N + 1` uniform times `k h`, `k ≤ N`,
followed by the `m` jump times `s_0, …, s_{m−1}`. -/
noncomputable def jaTimes (h : ℝ) (N m : ℕ) (s : ℕ → ℝ) (i : Fin (N + 1 + m)) : ℝ :=
  if (i : ℕ) ≤ N then (i : ℝ) * h else s (i - (N + 1))

/-- The jump-adapted grid with `m` jump times (Giles 2015, §6.1, p. 47, l. 2014–2019): the
`N + 1 + m` times `jaTimes h N m s` in increasing order (`Tuple.sort`), `t_0 ≤ ⋯ ≤ t_{N+m}`,
extended by `t_i = t_{N+m}` for `i > N + m`, as `unionGridBM` takes a grid.  Its set of values is
`jumpGrid h N {s_0, …, s_{m−1}}` (`image_jaGrid`).  A jump at a uniform time, or two equal jump
times, give a repeated time: a step of length `0`, whose Brownian increment is `0`. -/
noncomputable def jaGrid (h : ℝ) (N m : ℕ) (s : ℕ → ℝ) (i : ℕ) : ℝ :=
  jaTimes h N m s (Tuple.sort (jaTimes h N m s) ⟨min i (N + m), by omega⟩)

/-- Where the unsorted coarse times lie among the unsorted fine times (Giles 2015, §6.1,
l. 2020–2022: the coarse grid is part of the fine one): the coarse uniform time `k · 2h` is the
fine uniform time `(2k) h`, and the `t`-th jump time is the `t`-th jump time of the fine grid. -/
def jaCoarseIdx (n m : ℕ) (i : Fin (n + 1 + m)) : Fin (2 * n + 1 + m) :=
  ⟨if (i : ℕ) ≤ n then 2 * i else i + n, by split_ifs <;> omega⟩

/-- The position of the `j`-th time of the coarse jump-adapted grid (step `2h`, `n` uniform steps)
in the fine jump-adapted grid (step `h`, `2n` uniform steps) with the same `m` jump times `s`
(Giles 2015, §6.1, l. 2020–2025: the coarse path's Brownian increments are sums of the fine ones),
constant for `j ≥ n + m`; `jaGrid h (2n) m s (jaPos h n m s j) = jaGrid (2h) n m s j`
(`jaGrid_jaPos`). -/
noncomputable def jaPos (h : ℝ) (n m : ℕ) (s : ℕ → ℝ) (j : ℕ) : ℕ :=
  ((Tuple.sort (jaTimes h (2 * n) m s)).symm
    (jaCoarseIdx n m (Tuple.sort (jaTimes (2 * h) n m s) ⟨min j (n + m), by omega⟩)) : ℕ)

/-- The coarse times are fine times (Giles 2015, §6.1, l. 2020–2022): `(2k) h = k (2h)`, and the
jump times are the same. -/
lemma jaTimes_coarseIdx (h : ℝ) (n m : ℕ) (s : ℕ → ℝ) (i : Fin (n + 1 + m)) :
    jaTimes h (2 * n) m s (jaCoarseIdx n m i) = jaTimes (2 * h) n m s i := by
  have hv : ((jaCoarseIdx n m i : Fin (2 * n + 1 + m)) : ℕ) =
      if (i : ℕ) ≤ n then 2 * (i : ℕ) else (i : ℕ) + n := rfl
  unfold jaTimes
  rw [hv]
  by_cases hi : (i : ℕ) ≤ n
  · rw [if_pos hi, if_pos hi, if_pos (by omega)]
    push_cast
    ring
  · rw [if_neg hi, if_neg hi, if_neg (by omega)]
    congr 1
    omega

/-- The embedding of the coarse times into the fine ones preserves their order (Giles 2015, §6.1).
-/
lemma jaCoarseIdx_strictMono (n m : ℕ) : StrictMono (jaCoarseIdx n m) := by
  intro i j hij
  have h' : (i : ℕ) < j := hij
  show (jaCoarseIdx n m i : ℕ) < jaCoarseIdx n m j
  simp only [jaCoarseIdx]
  split_ifs <;> omega

/-- The jump-adapted grid is increasing (Giles 2015, §6.1). -/
lemma jaGrid_mono (h : ℝ) (N m : ℕ) (s : ℕ → ℝ) : Monotone (jaGrid h N m s) := fun _ _ hij =>
  Tuple.monotone_sort (jaTimes h N m s) (Fin.mk_le_mk.2 (min_le_min_right _ hij))

/-- The positions of the coarse times in the fine grid increase strictly (Giles 2015, §6.1): two
coarse times in the wrong order would be equal, and the order of equal times in `Tuple.sort`
follows their indices, which `jaCoarseIdx` preserves. -/
lemma jaPos_aux_strictMono (h : ℝ) (n m : ℕ) (s : ℕ → ℝ) :
    StrictMono fun j : Fin (n + 1 + m) => (Tuple.sort (jaTimes h (2 * n) m s)).symm
      (jaCoarseIdx n m (Tuple.sort (jaTimes (2 * h) n m s) j)) := by
  set F := jaTimes h (2 * n) m s with hF
  set C := jaTimes (2 * h) n m s with hC
  set σf := Tuple.sort F with hσf
  set σc := Tuple.sort C with hσc
  have hFC : ∀ i, F (jaCoarseIdx n m i) = C i := jaTimes_coarseIdx h n m s
  obtain ⟨hFm, hFt⟩ := Tuple.eq_sort_iff.1 hσf
  obtain ⟨hCm, hCt⟩ := Tuple.eq_sort_iff.1 hσc
  intro j j' hjj'
  by_contra hle'
  have hle : σf.symm (jaCoarseIdx n m (σc j')) ≤ σf.symm (jaCoarseIdx n m (σc j)) :=
    not_lt.1 hle'
  have hp : σf (σf.symm (jaCoarseIdx n m (σc j))) = jaCoarseIdx n m (σc j) :=
    σf.apply_symm_apply _
  have hp' : σf (σf.symm (jaCoarseIdx n m (σc j'))) = jaCoarseIdx n m (σc j') :=
    σf.apply_symm_apply _
  have v1 : C (σc j) ≤ C (σc j') := hCm hjj'.le
  have v2 := hFm hle
  simp only [Function.comp_apply, hp, hp', hFC] at v2
  have veq : C (σc j) = C (σc j') := le_antisymm v1 v2
  have hι : jaCoarseIdx n m (σc j) < jaCoarseIdx n m (σc j') :=
    jaCoarseIdx_strictMono n m (hCt j j' hjj' veq)
  rcases hle.lt_or_eq with hlt | heq
  · have := hFt _ _ hlt (by rw [hp, hp', hFC, hFC]; exact veq.symm)
    rw [hp, hp'] at this
    exact absurd hι (not_lt.2 this.le)
  · exact absurd (σf.symm.injective heq) hι.ne'

/-- The positions of the coarse times in the fine grid increase (Giles 2015, §6.1). -/
lemma jaPos_mono (h : ℝ) (n m : ℕ) (s : ℕ → ℝ) : Monotone (jaPos h n m s) := fun _ _ hij =>
  (jaPos_aux_strictMono h n m s).monotone (Fin.mk_le_mk.2 (min_le_min_right _ hij))

/-- The `jaPos h n m s j`-th fine time is the `j`-th coarse time (Giles 2015, §6.1,
l. 2020–2022). -/
lemma jaGrid_jaPos (h : ℝ) (n m : ℕ) (s : ℕ → ℝ) (j : ℕ) :
    jaGrid h (2 * n) m s (jaPos h n m s j) = jaGrid (2 * h) n m s j := by
  unfold jaGrid jaPos
  set x := (Tuple.sort (jaTimes h (2 * n) m s)).symm
    (jaCoarseIdx n m (Tuple.sort (jaTimes (2 * h) n m s) ⟨min j (n + m), by omega⟩)) with hx
  have e : (⟨min (x : ℕ) (2 * n + m), by omega⟩ : Fin (2 * n + 1 + m)) = x :=
    Fin.ext (min_eq_left (by have := x.2; omega))
  rw [e, hx, Equiv.apply_symm_apply, jaTimes_coarseIdx]

/-- The time of the jump-adapted grid at the sorted position of an unsorted time is that time
(Giles 2015, §6.1). -/
lemma jaGrid_symm (h : ℝ) (N m : ℕ) (s : ℕ → ℝ) (i : Fin (N + 1 + m)) :
    jaGrid h N m s ((Tuple.sort (jaTimes h N m s)).symm i) = jaTimes h N m s i := by
  unfold jaGrid
  set x := (Tuple.sort (jaTimes h N m s)).symm i with hx
  have e : (⟨min (x : ℕ) (N + m), by omega⟩ : Fin (N + 1 + m)) = x :=
    Fin.ext (min_eq_left (by have := x.2; omega))
  rw [e, hx, Equiv.apply_symm_apply]

/-- The sorted tuple `jaGrid h N m s` enumerates the jump-adapted grid `jumpGrid h N J` of the jump
times `J = {s_0, …, s_{m−1}}` (Giles 2015, §6.1, l. 2014–2019): its values at `0, …, N + m` are
exactly the uniform times `k h`, `k ≤ N`, and the jump times. -/
lemma image_jaGrid (h : ℝ) (N m : ℕ) (s : ℕ → ℝ) :
    (range (N + m + 1)).image (jaGrid h N m s) = jumpGrid h N ((range m).image s) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_range, jumpGrid, Finset.mem_union]
  constructor
  · rintro ⟨i, -, rfl⟩
    unfold jaGrid
    set k := Tuple.sort (jaTimes h N m s) ⟨min i (N + m), by omega⟩
    unfold jaTimes
    by_cases hk : (k : ℕ) ≤ N
    · rw [if_pos hk]
      exact Or.inl ⟨k, by omega, rfl⟩
    · rw [if_neg hk]
      exact Or.inr ⟨k - (N + 1), by omega, rfl⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨t, ht, rfl⟩)
    · refine ⟨(Tuple.sort (jaTimes h N m s)).symm ⟨k, by omega⟩, by omega, ?_⟩
      rw [jaGrid_symm]
      unfold jaTimes
      rw [if_pos (by simp only; omega)]
    · refine ⟨(Tuple.sort (jaTimes h N m s)).symm ⟨N + 1 + t, by omega⟩, by omega, ?_⟩
      rw [jaGrid_symm]
      unfold jaTimes
      rw [if_neg (by simp only; omega)]
      congr 1
      simp only
      omega

/-- The set of data for which `Tuple.sort` returns a given permutation is measurable (Giles 2015,
§6.1: the jump-adapted grid depends measurably on the jump times).  By `Tuple.eq_sort_iff` it is
cut out by finitely many comparisons of the coordinates. -/
lemma measurableSet_sort_eq {E : Type*} [MeasurableSpace E] {N : ℕ} {F : E → Fin N → ℝ}
    (hF : ∀ i, Measurable fun r => F r i) (π : Equiv.Perm (Fin N)) :
    MeasurableSet {r | Tuple.sort (F r) = π} := by
  have e : {r | Tuple.sort (F r) = π} =
      (⋂ a, ⋂ b, {r | a ≤ b → F r (π a) ≤ F r (π b)}) ∩
        ⋂ a, ⋂ b, {r | a < b → F r (π a) = F r (π b) → π a < π b} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    rfl
  rw [e]
  refine (MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_).inter
    (MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_)
  · by_cases hab : a ≤ b
    · simpa only [hab, true_implies] using measurableSet_le (hF (π a)) (hF (π b))
    · simp only [hab, false_implies, Set.ofPred_true, MeasurableSet.univ]
  · by_cases hab : a < b
    · by_cases hπ : π a < π b
      · simp only [hπ, implies_true, Set.ofPred_true, MeasurableSet.univ]
      · have := (measurableSet_eq_fun (hF (π a)) (hF (π b))).compl
        simpa only [hab, hπ, true_implies, imp_false, Set.compl_ofPred] using this
    · simp only [hab, false_implies, Set.ofPred_true, MeasurableSet.univ]

/-- A function of measurable data and of the permutation that sorts them is measurable (Giles 2015,
§6.1): it is measurable on each of the finitely many measurable pieces where the permutation is
constant (`measurableSet_sort_eq`). -/
lemma measurable_comp_sort {E β : Type*} [MeasurableSpace E] [MeasurableSpace β] {N : ℕ}
    {F : E → Fin N → ℝ} (hF : ∀ i, Measurable fun r => F r i)
    {G : Equiv.Perm (Fin N) → E → β} (hG : ∀ π, Measurable (G π)) :
    Measurable fun r => G (Tuple.sort (F r)) r := by
  intro B hB
  have e : (fun r => G (Tuple.sort (F r)) r) ⁻¹' B =
      ⋃ π : Equiv.Perm (Fin N), {r | Tuple.sort (F r) = π} ∩ G π ⁻¹' B := by
    ext r
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨π, hπ, h⟩ => hπ ▸ h⟩
  rw [e]
  exact MeasurableSet.iUnion fun π => (measurableSet_sort_eq hF π).inter (hG π hB)

/-- Each unsorted time is a measurable function of the jump times (Giles 2015, §6.1). -/
lemma measurable_jaTimes (h : ℝ) (N m : ℕ) (i : Fin (N + 1 + m)) :
    Measurable fun s : ℕ → ℝ => jaTimes h N m s i := by
  unfold jaTimes
  split_ifs
  · exact measurable_const
  · exact measurable_pi_apply _

/-- The jump-adapted grid is a measurable function of the number and the times of the jumps (Giles
2015, §6.1). -/
lemma measurable_jaGrid (h : ℝ) (N : ℕ) : Measurable fun p : ℕ × (ℕ → ℝ) =>
    fun i => jaGrid h N p.1 p.2 i := by
  refine measurable_pi_lambda _ fun i => ?_
  refine measurable_from_prod_countable_right fun m => ?_
  exact measurable_comp_sort (measurable_jaTimes h N m)
    (G := fun π s => jaTimes h N m s (π ⟨min i (N + m), by omega⟩))
    fun π => measurable_jaTimes h N m _

/-- The positions of the coarse times in the fine grid are measurable functions of the number and
the times of the jumps (Giles 2015, §6.1). -/
lemma measurable_jaPos (h : ℝ) (n : ℕ) : Measurable fun p : ℕ × (ℕ → ℝ) =>
    fun j => jaPos h n p.1 p.2 j := by
  refine measurable_pi_lambda _ fun j => ?_
  refine measurable_from_prod_countable_right fun m => ?_
  refine measurable_comp_sort (measurable_jaTimes h (2 * n) m)
    (G := fun π s => ((π.symm (jaCoarseIdx n m (Tuple.sort (jaTimes (2 * h) n m s)
      ⟨min j (n + m), by omega⟩))) : ℕ)) fun π => ?_
  exact measurable_comp_sort (measurable_jaTimes (2 * h) n m)
    (G := fun π' _ => ((π.symm (jaCoarseIdx n m (π' ⟨min j (n + m), by omega⟩))) : ℕ))
    fun _ => measurable_const

/-- The jump-adapted grid of random jump data is measurable (Giles 2015, §6.1). -/
lemma measurable_jaGrid_of {E : Type*} [MeasurableSpace E] {M : E → ℕ} {S : E → ℕ → ℝ}
    (hM : Measurable M) (hS : Measurable S) (h : ℝ) (N : ℕ) :
    Measurable fun r => jaGrid h N (M r) (S r) := by
  have h1 := (measurable_jaGrid h N).comp (hM.prodMk hS)
  exact h1

/-- The positions of the coarse times of random jump data are measurable (Giles 2015, §6.1). -/
lemma measurable_jaPos_of {E : Type*} [MeasurableSpace E] {M : E → ℕ} {S : E → ℕ → ℝ}
    (hM : Measurable M) (hS : Measurable S) (h : ℝ) (n : ℕ) :
    Measurable fun r => jaPos h n (M r) (S r) := by
  have h1 := (measurable_jaPos h n).comp (hM.prodMk hS)
  exact h1

/-- The Brownian increments of the coarse path over its jump-adapted grid, obtained by summing those
of the fine path (Giles 2015, §6.1, l. 2020–2025, and §5.6, l. 1926–1929):
`W(t^c_{j+1}) − W(t^c_j)`, where `W` is the union-grid path (`unionGridBM`) on the fine grid
`jaGrid h (2n) m s` driven by the normal variates `z`, and `t^c_j = jaGrid (2h) n m s j` is its
`jaPos h n m s j`-th time. -/
noncomputable def jaCoarseInc (h : ℝ) (n m : ℕ) (s z : ℕ → ℝ) (j : ℕ) : ℝ :=
  unionGridBM (jaGrid h (2 * n) m s) z (jaPos h n m s (j + 1)) -
    unionGridBM (jaGrid h (2 * n) m s) z (jaPos h n m s j)

/-- The Brownian increments `√(t_{j+1} − t_j) z_j` simulated directly on the jump-adapted grid
`t = jaGrid h N m s` (Giles 2015, §6.1, l. 2014–2019: the increments that the Euler–Maruyama or
Milstein approximation between the jumps uses). -/
noncomputable def jaOwnInc (h : ℝ) (N m : ℕ) (s z : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (jaGrid h N m s (j + 1) - jaGrid h N m s j) * z j

/-- **Jump-adapted MLMC with a constant jump rate and random jump times: the coarse path has the
single-level law** (Giles 2015, §6.1, p. 47, l. 2020–2025: "If the jump activity rate is constant,
then for each stochastic sample ω the jumps on the coarse and fine paths will occur at the same
time, and therefore the extension of the multilevel method is straightforward with the coarse and
fine paths using the same underlying Brownian paths, and the same random variables to determine the
jump times and strengths").  The jump data `R` (values in a measurable space `E`, e.g. the arrival
times and strengths of the jumps of a Poisson process) is independent of the standard normal
variates `Z` (`μ.map Z = stdNormalSeq`); `M(R)` is the number of jumps and
`S(R)_0, …, S(R)_{M(R)−1}` their times (`M`, `S` measurable).  A level-`(ℓ + 1)` sample uses the
fine jump-adapted grid `jaGrid h (2n) M(R) S(R)` (step `h`, `2n` uniform steps and the jump times;
as a set, `jumpGrid h (2n) J`, `image_jaGrid`) with its Brownian increments `√Δt Z_i`, and the
coarse path on `jaGrid (2h) n M(R) S(R)`, the jump-adapted grid of level `ℓ`, with the summed
increments `jaCoarseInc`.  Then (jump data, coarse Brownian increments) has the joint law of
(jump data, increments `jaOwnInc (2h) n` simulated on the level-`ℓ` grid alone).  This is
`jumpAdapted_map_eq` for the jump-adapted grids, whose measurability in the jump data
(`measurable_jaGrid_of`, `measurable_jaPos_of`, through `Tuple.sort`) and monotonicity
(`jaGrid_mono`, `jaPos_mono`) are proved; the jump times need not lie in `[0, T]` or be distinct.
-/
theorem jumpAdapted_random_map_eq {E : Type*} [MeasurableSpace E] {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {R : Ω → E} {Z : Ω → ℕ → ℝ} (hR : Measurable R)
    (hZlaw : μ.map Z = stdNormalSeq) (hRZ : IndepFun R Z μ) {M : E → ℕ} {S : E → ℕ → ℝ}
    (hM : Measurable M) (hS : Measurable S) (h : ℝ) (n : ℕ) :
    μ.map (fun ω => (R ω, jaCoarseInc h n (M (R ω)) (S (R ω)) (Z ω))) =
      μ.map (fun ω => (R ω, jaOwnInc (2 * h) n (M (R ω)) (S (R ω)) (Z ω))) := by
  have h1 := jumpAdapted_map_eq hR hZlaw hRZ (measurable_jaGrid_of hM hS h (2 * n))
    (measurable_jaPos_of hM hS h n) (fun _ => jaGrid_mono _ _ _ _) (fun _ => jaPos_mono _ _ _ _)
  have e : ∀ r j, jaGrid h (2 * n) (M r) (S r) (jaPos h n (M r) (S r) j) =
      jaGrid (2 * h) n (M r) (S r) j := fun r j => jaGrid_jaPos h n _ _ j
  simp only [e] at h1
  unfold jaCoarseInc jaOwnInc
  exact h1

/-- **(2.4) for jump-adapted MLMC with a constant jump rate and random jump times** (Giles 2015,
§6.1, p. 47, l. 2020–2025, with (2.4), §2.1, p. 8, l. 378–382: "Provided we maintain the identity
`E[P^f_ℓ] = E[P^c_ℓ]` so that the expectation on level `ℓ` is the same for the two
approximations").  In the setting of `jumpAdapted_random_map_eq`, let `F(r, ΔW)` be a measurable
payoff of the jump data and of the Brownian increments of a path on the coarse grid (e.g. an
Euler–Maruyama or Milstein path between the jumps, the jumps simulated exactly from `r`).  The
coarse payoff `F(R, jaCoarseInc …)` of a level-`(ℓ + 1)` sample is integrable iff the level-`ℓ`
payoff `F(R, jaOwnInc (2h) n …)`, simulated on its own grid, is, and they have the same
expectation: `E[P^c_{ℓ+1}] = E[P^f_ℓ]`, with random jump times independent of the Brownian path.
-/
theorem jumpAdapted_random_2_4 {E : Type*} [MeasurableSpace E] {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {R : Ω → E} {Z : Ω → ℕ → ℝ} (hR : Measurable R)
    (hZlaw : μ.map Z = stdNormalSeq) (hRZ : IndepFun R Z μ) {M : E → ℕ} {S : E → ℕ → ℝ}
    (hM : Measurable M) (hS : Measurable S) (h : ℝ) (n : ℕ) {F : E → (ℕ → ℝ) → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    (Integrable (fun ω => F (R ω) (jaCoarseInc h n (M (R ω)) (S (R ω)) (Z ω))) μ ↔
      Integrable (fun ω => F (R ω) (jaOwnInc (2 * h) n (M (R ω)) (S (R ω)) (Z ω))) μ) ∧
    ∫ ω, F (R ω) (jaCoarseInc h n (M (R ω)) (S (R ω)) (Z ω)) ∂μ =
      ∫ ω, F (R ω) (jaOwnInc (2 * h) n (M (R ω)) (S (R ω)) (Z ω)) ∂μ := by
  have h1 := jumpAdapted_2_4 hR hZlaw hRZ (measurable_jaGrid_of hM hS h (2 * n))
    (measurable_jaPos_of hM hS h n) (fun _ => jaGrid_mono _ _ _ _) (fun _ => jaPos_mono _ _ _ _)
    hF
  have e : ∀ r j, jaGrid h (2 * n) (M r) (S r) (jaPos h n (M r) (S r) j) =
      jaGrid (2 * h) n (M r) (S r) j := fun r j => jaGrid_jaPos h n _ _ j
  simp only [e] at h1
  unfold jaCoarseInc jaOwnInc
  exact h1

/-! ### §6.1: thinning with a path-dependent jump rate and the change of measure -/

/-- The law of the acceptance decisions in thinning (Giles 2015, §6.1, p. 47, l. 2026–2030: "a set
of candidate jump times is simulated based on the constant upper bound, and then a subset of these
are selected to be real jumps").  Conditionally on `m` candidate jump times, candidate `i` is
accepted (`a_i = true`) with probability `p_i(a)`, which may depend on the earlier decisions `a_j`,
`j < i` (a path-dependent rate, `p_i = λ(t_i, X(t_i−))/λ_max`); the decisions `a` have probability
`∏_i (p_i(a) if a_i, 1 − p_i(a) otherwise)`. -/
noncomputable def thinLaw {m : ℕ} (p : Fin m → (Fin m → Bool) → ℝ) (a : Fin m → Bool) : ℝ :=
  ∏ i, if a i then p i a else 1 - p i a

/-- The likelihood ratio of the thinning law `p` with respect to the sampling law `q` (Giles 2015,
§6.1, p. 47, l. 2033–2035: "Xia and Giles (2012) avoid this by using a change of measure to ensure
that the jump times are the same for both paths; this introduces a Radon-Nikodym into the payoff
evaluation"): `∏_i (p_i/q_i if a_i, (1 − p_i)/(1 − q_i) otherwise)`. -/
noncomputable def thinLR {m : ℕ} (p q : Fin m → (Fin m → Bool) → ℝ) (a : Fin m → Bool) : ℝ :=
  ∏ i, if a i then p i a / q i a else (1 - p i a) / (1 - q i a)

/-- `P_q(a) · LR(a) = P_p(a)` when no `q_i` is `0` or `1` (Giles 2015, §6.1, l. 2033–2035). -/
lemma thinLaw_mul_thinLR {m : ℕ} (p : Fin m → (Fin m → Bool) → ℝ)
    {q : Fin m → (Fin m → Bool) → ℝ} (hq : ∀ i a, q i a ≠ 0 ∧ q i a ≠ 1) (a : Fin m → Bool) :
    thinLaw q a * thinLR p q a = thinLaw p a := by
  unfold thinLaw thinLR
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : 1 - q i a ≠ 0 := sub_ne_zero.2 (hq i a).2.symm
  split_ifs
  · field_simp [(hq i a).1]
  · field_simp [h1]

/-- **The change of measure for thinning is unbiased** (Giles 2015, §6.1, p. 47, l. 2033–2036: "a
change of measure to ensure that the jump times are the same for both paths; this introduces a
Radon-Nikodym into the payoff evaluation").  If the acceptance decisions are sampled with the
probabilities `q_i(a) ∉ {0, 1}` instead of the target probabilities `p_i(a)`, then for every payoff
`F` of the decisions, `E_q[F · LR] = ∑_a P_q(a) F(a) LR(a) = ∑_a P_p(a) F(a) = E_p[F]`.  The
statement is conditional on the candidate times and on the rest of the simulation (Brownian path,
jump strengths), on which `p`, `q` and `F` may depend; the variance reduction claimed at l. 2036 is
empirical and not formalised. -/
theorem thinning_lr_unbiased {m : ℕ} (p : Fin m → (Fin m → Bool) → ℝ)
    {q : Fin m → (Fin m → Bool) → ℝ} (hq : ∀ i a, q i a ≠ 0 ∧ q i a ≠ 1)
    (F : (Fin m → Bool) → ℝ) :
    ∑ a, thinLaw q a * (F a * thinLR p q a) = ∑ a, thinLaw p a * F a := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← thinLaw_mul_thinLR p hq a]
  ring

/-- The probabilities of the decisions sum to `1` when each acceptance probability only depends on
the earlier decisions (Giles 2015, §6.1, l. 2026–2030); summing out the first decision and
induction. -/
lemma thinLaw_sum_eq_one (m : ℕ) : ∀ p : Fin m → (Fin m → Bool) → ℝ,
    (∀ i a a', (∀ j, j < i → a j = a' j) → p i a = p i a') → ∑ a, thinLaw p a = 1 := by
  induction m with
  | zero => intro p _; simp [thinLaw]
  | succ m ih =>
    intro p had
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Bool).sum_comp, Fintype.sum_prod_type]
    have key : ∀ (x : Bool) (y : Fin m → Bool),
        thinLaw p ((Fin.consEquiv fun _ : Fin (m + 1) => Bool) (x, y)) =
          (if x then p 0 (Fin.cons x y) else 1 - p 0 (Fin.cons x y)) *
            thinLaw (fun i y => p i.succ (Fin.cons x y)) y := by
      intro x y
      simp only [Fin.consEquiv_apply, thinLaw, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rfl
    have h0 : ∀ (x : Bool) (y : Fin m → Bool), p 0 (Fin.cons x y) = p 0 (fun _ => false) :=
      fun x y => had 0 _ _ fun j hj => absurd hj (Fin.not_lt_zero j)
    have hsum : ∀ x : Bool, ∑ y, thinLaw (fun i y => p i.succ (Fin.cons x y)) y = 1 := by
      intro x
      refine ih _ fun i y y' hyy => had i.succ _ _ fun j hj => ?_
      refine Fin.cases (by simp) (fun j' hj' => ?_) j hj
      simp only [Fin.cons_succ]
      exact hyy j' (Fin.succ_lt_succ_iff.1 hj')
    simp_rw [key, h0, ← Finset.mul_sum, hsum]
    simp

/-- **The thinning law is a probability law** (Giles 2015, §6.1, p. 47, l. 2026–2030: "If there is
a known upper bound to the jump rate, then one can use the 'thinning' approach of Glasserman and
Merener (2004) in which a set of candidate jump times is simulated based on the constant upper
bound, and then a subset of these are selected to be real jumps").  If every acceptance probability
`p_i(a) ∈ [0, 1]` only depends on the earlier decisions `a_j`, `j < i` (a path-dependent rate), then
`P_p(a) ≥ 0` and `∑_a P_p(a) = 1`: `thinLaw p` is the law of the sequentially sampled decisions, and
the sums in `thinning_lr_unbiased` are expectations. -/
theorem thinLaw_isProb {m : ℕ} {p : Fin m → (Fin m → Bool) → ℝ}
    (hp : ∀ i a, 0 ≤ p i a ∧ p i a ≤ 1)
    (had : ∀ i a a', (∀ j, j < i → a j = a' j) → p i a = p i a') :
    (∀ a, 0 ≤ thinLaw p a) ∧ ∑ a, thinLaw p a = 1 := by
  refine ⟨fun a => Finset.prod_nonneg fun i _ => ?_, thinLaw_sum_eq_one m p had⟩
  split_ifs
  · exact (hp i a).1
  · linarith [(hp i a).2]

/-- **The thinning change of measure respects the telescoping sum** (Giles 2015, §6.1, p. 47,
l. 2030–2036: without it "some candidate jumps will be selected for the coarse path but not for the
fine path, or vice versa, leading to an `O(1)` difference in the paths and hence the payoffs"; with
it "the jump times are the same for both paths").  The fine and the coarse path accept the same
candidates, sampled once with probabilities `q`, and each path's payoff is weighted by its own
likelihood ratio (target probabilities `p^f`, `p^c`).  Then
`E_q[F^f LR^f − F^c LR^c] = E_{p^f}[F^f] − E_{p^c}[F^c]`: the correction has the mean of the
difference of the two levels, as Theorem 1 (ii) requires. -/
theorem thinning_mlmc_correction {m : ℕ} (pf pc : Fin m → (Fin m → Bool) → ℝ)
    {q : Fin m → (Fin m → Bool) → ℝ} (hq : ∀ i a, q i a ≠ 0 ∧ q i a ≠ 1)
    (Ff Fc : (Fin m → Bool) → ℝ) :
    ∑ a, thinLaw q a * (Ff a * thinLR pf q a - Fc a * thinLR pc q a) =
      ∑ a, thinLaw pf a * Ff a - ∑ a, thinLaw pc a * Fc a := by
  rw [← thinning_lr_unbiased pf hq Ff, ← thinning_lr_unbiased pc hq Fc,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end MLMC
