import MlmcLean.ErrorAnalysis

/-!
# The MLMC algorithm (Giles 2015, §3.1 and §3.4)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §3.1
(Algorithm 1, p. 21) and §3.4 (the driver routine `mlmc.m`, pp. 23–26) of the author's version.

```
Algorithm 1 MLMC algorithm
  start with L = 2, and initial target of N₀ samples on levels ℓ = 0, 1, 2
  while extra samples need to be evaluated do
    evaluate extra samples on each level
    compute/update estimates for V_ℓ, ℓ = 0, …, L
    define optimal N_ℓ, ℓ = 0, …, L                                          (3.1)
    test for weak convergence
    if not converged, set L := L + 1, and initialise target N_L
  end while
```

The algorithm is analysed here with the exact means `m_ℓ = E[P_ℓ − P_{ℓ−1}]` (`P_{−1} ≡ 0`) and
the exact variances `V_ℓ` in place of their sample estimates (the *idealised* algorithm).  With
exact values one round of extra samples reaches every target, so the pass with finest level `L`
ends with `N_ℓ = max(previous N_ℓ, target (3.1))`, followed by the convergence test.

* **The robust convergence test** (p. 21, and the `rem` line of `mlmc.m`, p. 26):
  `alg1Rem m α L = max(|m_L|, |m_{L−1}| 2^{−α}, |m_{L−2}| 2^{−2α})/(2^α − 1)`.  It is at least the
  one-point estimate `|m_L|/(2^α − 1)` of `remaining_error` (`abs_div_le_alg1Rem`).  If the
  corrections beyond `L` decay at least geometrically (`abs_tail_le`, an inequality form of
  `remaining_error`) from one of the three anchors `L, L − 1, L − 2`, it bounds the remaining
  error `|E[P − P_L]|` (`abs_tail_le_alg1Rem`, `abs_integral_sub_le_alg1Rem`), and a passing test
  gives `MSE < ε²` (`robust_test_mse`).
* **The loop.** `alg1Samples` are the sample counts after the passes `2, …, L`, and `alg1Level` is
  the first `L ≥ 2` at which the test passes, the level at which Algorithm 1 stops.
  - Termination: the loop stops whenever `m_ℓ → 0` (`alg1_terminates`), at a level at most
    `max 2 (levelL α (c₁/(2^α − 1)) (ε/√2))` when `|m_ℓ| ≤ c₁ 2^{−αℓ}` (`alg1Level_le`).
  - At exit the variance is at most `½ε²` (`alg1_variance`), and the MSE is at most `ε²` when the
    remaining error is bounded by the robust estimate (`alg1_mse`).  The driver stops on
    `rem ≤ ε/√2`, which gives `≤`; the text's strict test gives `<` (`robust_test_mse`).
  - Under the conditions of Theorem 1 the final cost is `O(complexityBound α β γ ε)`, the order
    of Theorem 1 (`alg1_complexity`).
* **Algorithm 1 is heuristic** (p. 21): the test can pass while the bias is arbitrarily large
  (`alg1_not_guaranteed`).
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace MLMC

/-! ### The robust convergence test -/

/-- **The robust estimate of the remaining error** used by Algorithm 1 (Giles 2015, §3.1, p. 21:
"we extend this check to extrapolate from the previous two data points `E[P_{L−1} − P_{L−2}]`,
`E[P_{L−2} − P_{L−3}]`, and take the maximum over all three as the estimated remaining error"; the
driver computes `rem = max(ml(L+1+range).*2.^(alpha*range))/(2^alpha - 1)` with `range = -2:0`,
p. 26): `max(|m_L|, |m_{L−1}| 2^{−α}, |m_{L−2}| 2^{−2α})/(2^α − 1)`, where `m_ℓ` is the mean of the
level-`ℓ` correction. -/
noncomputable def alg1Rem (m : ℕ → ℝ) (α : ℝ) (L : ℕ) : ℝ :=
  max (max (|m (L - 2)| * (2 : ℝ) ^ (-(2 * α))) (|m (L - 1)| * (2 : ℝ) ^ (-α))) |m L| /
    ((2 : ℝ) ^ α - 1)

lemma two_rpow_sub_one_pos {α : ℝ} (hα : 0 < α) : 0 < (2 : ℝ) ^ α - 1 := by
  have := Real.one_lt_rpow one_lt_two hα
  linarith

/-- The robust test is more conservative than the one-point test of `remaining_error`
(Giles 2015, §3.1, p. 21): `|m_L|/(2^α − 1) ≤ alg1Rem m α L`. -/
lemma abs_div_le_alg1Rem (m : ℕ → ℝ) {α : ℝ} (hα : 0 < α) (L : ℕ) :
    |m L| / ((2 : ℝ) ^ α - 1) ≤ alg1Rem m α L :=
  div_le_div_of_nonneg_right (le_max_right _ _) (two_rpow_sub_one_pos hα).le

/-- Each of the three extrapolations of the robust test (Giles 2015, §3.1, p. 21) is at most
`alg1Rem`: `|m_{L−k}| 2^{−αk}/(2^α − 1) ≤ alg1Rem m α L` for `k ≤ 2`. -/
lemma anchor_le_alg1Rem (m : ℕ → ℝ) {α : ℝ} (hα : 0 < α) (L : ℕ) {k : ℕ} (hk : k ≤ 2) :
    |m (L - k)| * (2 : ℝ) ^ (-(α * k)) / ((2 : ℝ) ^ α - 1) ≤ alg1Rem m α L := by
  refine div_le_div_of_nonneg_right ?_ (two_rpow_sub_one_pos hα).le
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · simp only [Nat.sub_zero, Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one]
    exact le_max_right _ _
  · simp only [Nat.cast_one, mul_one]
    exact (le_max_right _ _).trans (le_max_left _ _)
  · rw [show α * ((2 : ℕ) : ℝ) = 2 * α by push_cast; ring]
    exact (le_max_left _ _).trans (le_max_left _ _)

/-- **The remaining error under at-least-geometric decay** (an inequality form of the remaining
error of Giles 2015, §3.1, p. 21, "`E[P − P_L] = ∑_{ℓ=L+1}^∞ E[P_ℓ − P_{ℓ−1}] =
E[P_L − P_{L−1}]/(2^α − 1)`"; `remaining_error` is the exact form).  Let `q_ℓ → q'` (in
Algorithm 1, `q_ℓ = E[P_ℓ]` and `q' = E[P]`).  If the corrections beyond `L` satisfy
`|q_ℓ − q_{ℓ−1}| ≤ A 2^{−α(ℓ−L)}` for all `ℓ > L`, with `α > 0`, then
`|q' − q_L| ≤ A/(2^α − 1)`. -/
theorem abs_tail_le {q : ℕ → ℝ} {q' : ℝ} (hq : Tendsto q atTop (𝓝 q')) {α A : ℝ} (hα : 0 < α)
    {L : ℕ} (hdecay : ∀ ℓ : ℕ, L < ℓ →
      |q ℓ - q (ℓ - 1)| ≤ A * (2 : ℝ) ^ (-(α * ((ℓ : ℝ) - L)))) :
    |q' - q L| ≤ A / ((2 : ℝ) ^ α - 1) := by
  set r : ℝ := (2 : ℝ) ^ (-α) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos two_pos _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  -- the corrections beyond `L` in the form `A r^{k+1}`
  have hstep : ∀ k : ℕ, |q (L + (k + 1)) - q (L + k)| ≤ A * r ^ (k + 1) := fun k => by
    have h := hdecay (L + (k + 1)) (by omega)
    have e1 : L + (k + 1) - 1 = L + k := by omega
    have e2 : (2 : ℝ) ^ (-(α * (((L + (k + 1) : ℕ) : ℝ) - L))) = r ^ (k + 1) := by
      rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    rw [e1, e2] at h
    exact h
  have hA : 0 ≤ A := by
    have h := (abs_nonneg _).trans (hstep 0)
    rw [zero_add, pow_one] at h
    by_contra hneg
    have : A * r < 0 := mul_neg_of_neg_of_pos (not_le.1 hneg) hr0
    linarith
  -- the partial sums telescope and are bounded by `A r/(1 − r)`
  have hpart : ∀ n : ℕ, |q (L + n) - q L| ≤ A * r / (1 - r) := fun n => by
    have htel : q (L + n) - q L = ∑ k ∈ range n, (q (L + (k + 1)) - q (L + k)) :=
      (Finset.sum_range_sub (fun i => q (L + i)) n).symm
    rw [htel]
    calc |∑ k ∈ range n, (q (L + (k + 1)) - q (L + k))|
        ≤ ∑ k ∈ range n, |q (L + (k + 1)) - q (L + k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range n, A * r ^ (k + 1) := Finset.sum_le_sum fun k _ => hstep k
      _ = A * r * ∑ k ∈ range n, r ^ k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ A * r * (1 - r)⁻¹ :=
          mul_le_mul_of_nonneg_left (geom_sum_le_of_lt_one hr0.le hr1 n) (mul_nonneg hA hr0.le)
      _ = A * r / (1 - r) := (div_eq_mul_inv _ _).symm
  -- pass to the limit
  have hlim : Tendsto (fun n => |q (L + n) - q L|) atTop (𝓝 |q' - q L|) := by
    have h1 : Tendsto (fun n => q (L + n)) atTop (𝓝 q') :=
      (hq.comp (tendsto_add_atTop_nat L)).congr fun n => by
        show q (n + L) = q (L + n)
        rw [Nat.add_comm]
    exact (h1.sub_const (q L)).abs
  have hx0 : (2 : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos two_pos α).ne'
  have hrx : r = ((2 : ℝ) ^ α)⁻¹ := by rw [hr_def, Real.rpow_neg zero_le_two]
  have e : 1 - ((2 : ℝ) ^ α)⁻¹ = ((2 : ℝ) ^ α - 1) * ((2 : ℝ) ^ α)⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hx0, one_mul]
  calc |q' - q L| ≤ A * r / (1 - r) := le_of_tendsto' hlim hpart
    _ = A / ((2 : ℝ) ^ α - 1) := by
        rw [hrx, e, mul_div_mul_right _ _ (inv_ne_zero hx0)]

/-- **The robust test bounds the remaining error** (Giles 2015, §3.1, p. 21, and the `rem` line of
`mlmc.m`, p. 26).  Let `q_ℓ → q'`, let `m` be any sequence (the level means used by the test) and
`L ≥ k` with `k ≤ 2`.  If the corrections beyond `L` decay at least geometrically from the anchor
`L − k`, `|q_ℓ − q_{ℓ−1}| ≤ |m_{L−k}| 2^{−α(ℓ−(L−k))}` for all `ℓ > L`, then
`|q' − q_L| ≤ alg1Rem m α L`. -/
theorem abs_tail_le_alg1Rem {q m : ℕ → ℝ} {q' : ℝ} (hq : Tendsto q atTop (𝓝 q')) {α : ℝ}
    (hα : 0 < α) {L k : ℕ} (hk : k ≤ 2) (hkL : k ≤ L)
    (hdecay : ∀ ℓ : ℕ, L < ℓ →
      |q ℓ - q (ℓ - 1)| ≤ |m (L - k)| * (2 : ℝ) ^ (-(α * ((ℓ : ℝ) - (L - k : ℕ))))) :
    |q' - q L| ≤ alg1Rem m α L := by
  refine (abs_tail_le hq hα (A := |m (L - k)| * (2 : ℝ) ^ (-(α * k))) fun ℓ hℓ => ?_).trans
    (anchor_le_alg1Rem m hα L hk)
  calc |q ℓ - q (ℓ - 1)| ≤ |m (L - k)| * (2 : ℝ) ^ (-(α * ((ℓ : ℝ) - (L - k : ℕ)))) := hdecay ℓ hℓ
    _ = |m (L - k)| * (2 : ℝ) ^ (-(α * k)) * (2 : ℝ) ^ (-(α * ((ℓ : ℝ) - L))) := by
        rw [Nat.cast_sub hkL,
          show -(α * ((ℓ : ℝ) - ((L : ℝ) - k))) = -(α * k) + -(α * ((ℓ : ℝ) - L)) by ring,
          Real.rpow_add two_pos, mul_assoc]

/-- `alg1Rem m α L ≤ c 2^{−αL}/(2^α − 1)` for `L ≥ 2` when `|m_ℓ| ≤ c 2^{−αℓ}` for every `ℓ`
(condition i) of Theorem 1 for the corrections; Giles 2015, §3.1). -/
lemma alg1Rem_le {m : ℕ → ℝ} {α c : ℝ} (hα : 0 < α)
    (hm : ∀ ℓ : ℕ, |m ℓ| ≤ c * (2 : ℝ) ^ (-(α * ℓ))) {L : ℕ} (hL : 2 ≤ L) :
    alg1Rem m α L ≤ c * (2 : ℝ) ^ (-(α * L)) / ((2 : ℝ) ^ α - 1) := by
  refine div_le_div_of_nonneg_right ?_ (two_rpow_sub_one_pos hα).le
  have hL2 : ((L - 2 : ℕ) : ℝ) = (L : ℝ) - 2 := by rw [Nat.cast_sub hL, Nat.cast_ofNat]
  have hL1 : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have e2 : (2 : ℝ) ^ (-(α * ((L - 2 : ℕ) : ℝ))) * (2 : ℝ) ^ (-(2 * α)) =
      (2 : ℝ) ^ (-(α * L)) := by
    rw [← Real.rpow_add two_pos, hL2]
    congr 1
    ring
  have e1 : (2 : ℝ) ^ (-(α * ((L - 1 : ℕ) : ℝ))) * (2 : ℝ) ^ (-α) = (2 : ℝ) ^ (-(α * L)) := by
    rw [← Real.rpow_add two_pos, hL1]
    congr 1
    ring
  refine max_le (max_le ?_ ?_) (hm L)
  · calc |m (L - 2)| * (2 : ℝ) ^ (-(2 * α))
        ≤ c * (2 : ℝ) ^ (-(α * ((L - 2 : ℕ) : ℝ))) * (2 : ℝ) ^ (-(2 * α)) :=
          mul_le_mul_of_nonneg_right (hm (L - 2)) (Real.rpow_nonneg zero_le_two _)
      _ = c * (2 : ℝ) ^ (-(α * L)) := by rw [mul_assoc, e2]
  · calc |m (L - 1)| * (2 : ℝ) ^ (-α)
        ≤ c * (2 : ℝ) ^ (-(α * ((L - 1 : ℕ) : ℝ))) * (2 : ℝ) ^ (-α) :=
          mul_le_mul_of_nonneg_right (hm (L - 1)) (Real.rpow_nonneg zero_le_two _)
      _ = c * (2 : ℝ) ^ (-(α * L)) := by rw [mul_assoc, e1]

/-! ### The idealised loop -/

/-- The initial samples of Algorithm 1: `N₀` on each of the levels `0, 1, 2` (Giles 2015, §3.1:
"start with `L = 2`, and initial target of `N₀` samples on levels `ℓ = 0, 1, 2`"). -/
def alg1Init (N₀ ℓ : ℕ) : ℕ := if ℓ ≤ 2 then N₀ else 0

/-- **The sample counts of the idealised Algorithm 1** (Giles 2015, §3.1, and the driver `mlmc.m`,
§3.4): `alg1Samples N₀ V C ε L ℓ` is the number of samples on level `ℓ` after the passes with
finest levels `2, …, L` (for `L ≤ 1`, before the first pass).  Each pass tops every level `ℓ ≤ L`
up to its target (3.1), `optimalN (range (L + 1)) V C (ε²/2) ℓ` (`allocation_eq_3_1`): the driver
computes the extra samples as `dNl = max(0, Ns - Nl)`, so the count becomes `max(Nl, Ns)`. -/
noncomputable def alg1Samples (N₀ : ℕ) (V C : ℕ → ℝ) (ε : ℝ) : ℕ → ℕ → ℕ
  | 0, ℓ => alg1Init N₀ ℓ
  | L + 1, ℓ => max (alg1Samples N₀ V C ε L ℓ)
      (if 2 ≤ L + 1 ∧ ℓ ≤ L + 1 then optimalN (range (L + 2)) V C (ε ^ 2 / 2) ℓ else 0)

/-- The last pass reaches the targets (3.1): for `2 ≤ L` and `ℓ ≤ L`, the number of samples on
level `ℓ` is at least `optimalN (range (L + 1)) V C (ε²/2) ℓ` (Giles 2015, §3.1). -/
lemma optimalN_le_alg1Samples (N₀ : ℕ) (V C : ℕ → ℝ) (ε : ℝ) {L ℓ : ℕ} (hL : 2 ≤ L)
    (hℓ : ℓ ≤ L) : optimalN (range (L + 1)) V C (ε ^ 2 / 2) ℓ ≤ alg1Samples N₀ V C ε L ℓ := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [alg1Samples, if_pos ⟨hL, hℓ⟩]
  exact le_max_right _ _

/-- The targets (3.1) grow with the finest level `L` (the sum `∑_{ℓ' ≤ L} √(V_ℓ' C_ℓ')` grows):
`optimalN (range (L + 1)) V C τ ℓ` is monotone in `L` (Giles 2015, §3.1). -/
lemma optimalN_mono_range (V C : ℕ → ℝ) {τ : ℝ} (hτ : 0 < τ) {L L' : ℕ} (h : L ≤ L') (ℓ : ℕ) :
    optimalN (range (L + 1)) V C τ ℓ ≤ optimalN (range (L' + 1)) V C τ ℓ := by
  unfold optimalN lagrangeN sumSqrtVC
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset.2 (by omega))
      fun i _ _ => Real.sqrt_nonneg _)
    (mul_nonneg (inv_nonneg.2 hτ.le) (Real.sqrt_nonneg _)))

/-- The counts of Algorithm 1 are at most the initial samples plus the final targets (3.1):
`alg1Samples N₀ V C ε L ℓ ≤ alg1Init N₀ ℓ + optimalN (range (L + 1)) V C (ε²/2) ℓ`, because the
targets grow with `L` (Giles 2015, §3.1). -/
lemma alg1Samples_le (N₀ : ℕ) (V C : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) : ∀ L ℓ : ℕ,
    alg1Samples N₀ V C ε L ℓ ≤ alg1Init N₀ ℓ + optimalN (range (L + 1)) V C (ε ^ 2 / 2) ℓ
  | 0, ℓ => by
      rw [alg1Samples]
      exact Nat.le_add_right _ _
  | L + 1, ℓ => by
      rw [alg1Samples]
      have hτ : 0 < ε ^ 2 / 2 := by positivity
      have hmono := optimalN_mono_range V C hτ (Nat.le_succ L) ℓ
      apply max_le
      · exact (alg1Samples_le N₀ V C hε L ℓ).trans (Nat.add_le_add_left hmono _)
      · split_ifs
        · exact Nat.le_add_left _ _
        · exact Nat.zero_le _

open Classical in
/-- **The level at which Algorithm 1 stops** (Giles 2015, §3.1): starting from `L = 2`, the driver
adds a level while `rem > ε/√2` (`mlmc.m`, p. 26), so it stops at the least `L ≥ 2` with
`alg1Rem m α L ≤ ε/√2`; `0` if the test never passes (see `alg1_terminates`). -/
noncomputable def alg1Level (m : ℕ → ℝ) (α ε : ℝ) : ℕ :=
  if h : ∃ L, 2 ≤ L ∧ alg1Rem m α L ≤ ε / Real.sqrt 2 then Nat.find h else 0

lemma alg1Level_spec {m : ℕ → ℝ} {α ε : ℝ} (h : ∃ L, 2 ≤ L ∧ alg1Rem m α L ≤ ε / Real.sqrt 2) :
    2 ≤ alg1Level m α ε ∧ alg1Rem m α (alg1Level m α ε) ≤ ε / Real.sqrt 2 := by
  rw [alg1Level, dif_pos h]
  exact Nat.find_spec h

lemma alg1Level_le_of {m : ℕ → ℝ} {α ε : ℝ} {L : ℕ} (hL : 2 ≤ L)
    (hrem : alg1Rem m α L ≤ ε / Real.sqrt 2) : alg1Level m α ε ≤ L := by
  have h : ∃ L, 2 ≤ L ∧ alg1Rem m α L ≤ ε / Real.sqrt 2 := ⟨L, hL, hrem⟩
  rw [alg1Level, dif_pos h]
  exact Nat.find_min' h ⟨hL, hrem⟩

/-- **Algorithm 1 terminates whenever the corrections tend to zero** (Giles 2015, §3.1, with exact
means): if `m_ℓ → 0`, some `L ≥ 2` passes the convergence test `rem ≤ ε/√2` for every `ε > 0`,
so the loop stops, at `alg1Level m α ε`. -/
theorem alg1_terminates {m : ℕ → ℝ} (hm : Tendsto m atTop (𝓝 0)) {α ε : ℝ} (hα : 0 < α)
    (hε : 0 < ε) : ∃ L, 2 ≤ L ∧ alg1Rem m α L ≤ ε / Real.sqrt 2 := by
  have h2α := two_rpow_sub_one_pos hα
  set δ : ℝ := ((2 : ℝ) ^ α - 1) * (ε / Real.sqrt 2) with hδ_def
  have hδ : 0 < δ := mul_pos h2α (div_pos hε (Real.sqrt_pos.2 two_pos))
  obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.1 hm) δ hδ
  have hsmall : ∀ ℓ, n₀ ≤ ℓ → |m ℓ| ≤ δ := fun ℓ hℓ => by
    have h := hn₀ ℓ hℓ
    rw [Real.dist_eq, sub_zero] at h
    exact h.le
  refine ⟨n₀ + 2, by omega, ?_⟩
  have hr1 : (2 : ℝ) ^ (-α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)
  have hr2 : (2 : ℝ) ^ (-(2 * α)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)
  have h1 : |m (n₀ + 2 - 2)| * (2 : ℝ) ^ (-(2 * α)) ≤ δ :=
    calc |m (n₀ + 2 - 2)| * (2 : ℝ) ^ (-(2 * α)) ≤ |m (n₀ + 2 - 2)| * 1 :=
          mul_le_mul_of_nonneg_left hr2 (abs_nonneg _)
      _ ≤ δ := by rw [mul_one]; exact hsmall _ (by omega)
  have h2 : |m (n₀ + 2 - 1)| * (2 : ℝ) ^ (-α) ≤ δ :=
    calc |m (n₀ + 2 - 1)| * (2 : ℝ) ^ (-α) ≤ |m (n₀ + 2 - 1)| * 1 :=
          mul_le_mul_of_nonneg_left hr1 (abs_nonneg _)
      _ ≤ δ := by rw [mul_one]; exact hsmall _ (by omega)
  have h3 : |m (n₀ + 2)| ≤ δ := hsmall _ (by omega)
  unfold alg1Rem
  rw [div_le_iff₀ h2α]
  refine (max_le (max_le h1 h2) h3).trans (le_of_eq ?_)
  rw [hδ_def, mul_comm]

/-- **Algorithm 1 stops no later than the level of Theorem 1** (Giles 2015, §3.1, under condition
i) of Theorem 1 for the corrections): if `|m_ℓ| ≤ c 2^{−αℓ}` for every `ℓ` (with `α, c, ε > 0`),
the test passes at `alg1Level m α ε ≥ 2`, and
`alg1Level m α ε ≤ max 2 (levelL α (c/(2^α − 1)) (ε/√2))`. -/
theorem alg1Level_le {m : ℕ → ℝ} {α c ε : ℝ} (hα : 0 < α) (hc : 0 < c) (hε : 0 < ε)
    (hm : ∀ ℓ : ℕ, |m ℓ| ≤ c * (2 : ℝ) ^ (-(α * ℓ))) :
    2 ≤ alg1Level m α ε ∧ alg1Rem m α (alg1Level m α ε) ≤ ε / Real.sqrt 2 ∧
      alg1Level m α ε ≤ max 2 (levelL α (c / ((2 : ℝ) ^ α - 1)) (ε / Real.sqrt 2)) := by
  have h2α := two_rpow_sub_one_pos hα
  have hδ : 0 < ε / Real.sqrt 2 := div_pos hε (Real.sqrt_pos.2 two_pos)
  have hc' : 0 < c / ((2 : ℝ) ^ α - 1) := div_pos hc h2α
  set ℓ₁ : ℕ := levelL α (c / ((2 : ℝ) ^ α - 1)) (ε / Real.sqrt 2) with hℓ₁
  have hL₀2 : 2 ≤ max 2 ℓ₁ := le_max_left _ _
  have hpass : alg1Rem m α (max 2 ℓ₁) ≤ ε / Real.sqrt 2 := by
    refine (alg1Rem_le hα hm hL₀2).trans ?_
    have hb := levelL_bias hα hc' hδ
    have hmono : (2 : ℝ) ^ (-(α * ((max 2 ℓ₁ : ℕ) : ℝ))) ≤ (2 : ℝ) ^ (-(α * (ℓ₁ : ℝ))) := by
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      have h : (ℓ₁ : ℝ) ≤ ((max 2 ℓ₁ : ℕ) : ℝ) := Nat.cast_le.2 (le_max_right _ _)
      exact neg_le_neg (mul_le_mul_of_nonneg_left h hα.le)
    calc c * (2 : ℝ) ^ (-(α * ((max 2 ℓ₁ : ℕ) : ℝ))) / ((2 : ℝ) ^ α - 1)
        = c / ((2 : ℝ) ^ α - 1) * (2 : ℝ) ^ (-(α * ((max 2 ℓ₁ : ℕ) : ℝ))) := by ring
      _ ≤ c / ((2 : ℝ) ^ α - 1) * (2 : ℝ) ^ (-(α * (ℓ₁ : ℝ))) :=
          mul_le_mul_of_nonneg_left hmono hc'.le
      _ ≤ ε / Real.sqrt 2 := hb
  obtain ⟨h1, h2⟩ := alg1Level_spec ⟨max 2 ℓ₁, hL₀2, hpass⟩
  exact ⟨h1, h2, alg1Level_le_of hL₀2 hpass⟩

/-- **At exit the variance target is met** (Giles 2015, §3.1: (3.1) "ensures that the … variance
of the combined multilevel estimator is less than `½ε²`"; here `≤`): after the passes up to
`L ≥ 2`, `∑_{ℓ ≤ L} V_ℓ/N_ℓ ≤ ε²/2` for the counts `N_ℓ = alg1Samples N₀ V C ε L ℓ`. -/
theorem alg1_variance (N₀ : ℕ) {V C : ℕ → ℝ} (hV : ∀ ℓ, 0 < V ℓ) (hC : ∀ ℓ, 0 < C ℓ) {ε : ℝ}
    (hε : 0 < ε) {L : ℕ} (hL : 2 ≤ L) :
    ∑ ℓ ∈ range (L + 1), V ℓ / (alg1Samples N₀ V C ε L ℓ : ℝ) ≤ ε ^ 2 / 2 := by
  have hτ : 0 < ε ^ 2 / 2 := by positivity
  have hs : (range (L + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos L)⟩
  refine le_trans (Finset.sum_le_sum fun ℓ hℓ => ?_)
    (optimalN_variance hs (fun ℓ _ => hV ℓ) (fun ℓ _ => hC ℓ) hτ)
  have hpos : (0 : ℝ) < optimalN (range (L + 1)) V C (ε ^ 2 / 2) ℓ :=
    Nat.cast_pos.2 (optimalN_pos hs hV hC hτ ℓ)
  have hle : (optimalN (range (L + 1)) V C (ε ^ 2 / 2) ℓ : ℝ) ≤ alg1Samples N₀ V C ε L ℓ :=
    Nat.cast_le.2 (optimalN_le_alg1Samples N₀ V C ε hL
      (Nat.lt_add_one_iff.1 (Finset.mem_range.1 hℓ)))
  exact div_le_div_of_nonneg_left (hV ℓ).le hpos hle

/-! ### The mean-square error at exit -/

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The robust test bounds the bias of the finest level (Giles 2015, §3.1): with
`m_ℓ = E[P_ℓ − P_{ℓ−1}]`, `E[P_ℓ] → E[P]` and at-least-geometric decay of the corrections beyond
`L` from an anchor `L − k`, `k ≤ 2`, `|E[P] − E[P_L]| ≤ alg1Rem m α L`. -/
theorem abs_integral_sub_le_alg1Rem {P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} {α : ℝ} {L k : ℕ}
    (hα : 0 < α) (hk : k ≤ 2) (hkL : k ≤ L) (hPl : ∀ ℓ, Integrable (Pl ℓ) μ)
    (hlim : Tendsto (fun ℓ => μ[Pl ℓ]) atTop (𝓝 (μ[P])))
    (hdecay : ∀ ℓ : ℕ, L < ℓ → |∫ ω, levelDiff Pl ℓ ω ∂μ| ≤
      |∫ ω, levelDiff Pl (L - k) ω ∂μ| * (2 : ℝ) ^ (-(α * ((ℓ : ℝ) - (L - k : ℕ))))) :
    |μ[P] - μ[Pl L]| ≤ alg1Rem (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) α L := by
  refine abs_tail_le_alg1Rem (q := fun ℓ => μ[Pl ℓ]) (m := fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ)
    hlim hα hk hkL fun ℓ hℓ => ?_
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  have e : μ[Pl (j + 1)] - μ[Pl (j + 1 - 1)] = ∫ ω, levelDiff Pl (j + 1) ω ∂μ := by
    rw [levelDiff_succ, integral_sub (hPl _) (hPl _), Nat.add_sub_cancel]
  calc |μ[Pl (j + 1)] - μ[Pl (j + 1 - 1)]| = |∫ ω, levelDiff Pl (j + 1) ω ∂μ| := by rw [e]
    _ ≤ _ := hdecay (j + 1) hℓ

/-- **The robust convergence test gives `MSE < ε²`** (Giles 2015, §3.1, p. 21: "The test for weak
convergence tries to ensure that `|E[P − P_L]| < ε/√2`, to achieve an MSE which is less than
`ε²`", with the robust three-point test).  If `E[P_ℓ] → E[P]`, the corrections beyond `L` decay at
least geometrically from one of the anchors `L, L − 1, L − 2`, the estimator `Y` has
`E[Y] = E[P_L]` and `V[Y] ≤ ½ε²`, and the test `alg1Rem < ε/√2` passes, then
`E[(Y − E[P])²] < ε²`. -/
theorem robust_test_mse {Y P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} {α ε : ℝ} {L k : ℕ} (hα : 0 < α)
    (hk : k ≤ 2) (hkL : k ≤ L) (hY : MemLp Y 2 μ) (hPl : ∀ ℓ, Integrable (Pl ℓ) μ)
    (hlim : Tendsto (fun ℓ => μ[Pl ℓ]) atTop (𝓝 (μ[P])))
    (hdecay : ∀ ℓ : ℕ, L < ℓ → |∫ ω, levelDiff Pl ℓ ω ∂μ| ≤
      |∫ ω, levelDiff Pl (L - k) ω ∂μ| * (2 : ℝ) ^ (-(α * ((ℓ : ℝ) - (L - k : ℕ)))))
    (hmean : μ[Y] = μ[Pl L]) (hV : variance Y μ ≤ ε ^ 2 / 2)
    (htest : alg1Rem (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) α L < ε / Real.sqrt 2) :
    μ[fun ω => (Y ω - μ[P]) ^ 2] < ε ^ 2 := by
  have hb := (abs_integral_sub_le_alg1Rem hα hk hkL hPl hlim hdecay).trans_lt htest
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hbias2 : (μ[P] - μ[Pl L]) ^ 2 < ε ^ 2 / 2 :=
    calc (μ[P] - μ[Pl L]) ^ 2 = |μ[P] - μ[Pl L]| ^ 2 := (sq_abs _).symm
      _ < (ε / Real.sqrt 2) ^ 2 := pow_lt_pow_left₀ hb (abs_nonneg _) two_ne_zero
      _ = ε ^ 2 / 2 := by rw [div_pow, hs2]
  rw [mse_eq_variance_add_sq_bias hY (μ[P]), hmean]
  have e : (μ[Pl L] - μ[P]) ^ 2 = (μ[P] - μ[Pl L]) ^ 2 := by ring
  rw [e]
  linarith

/-- **The MSE at exit of Algorithm 1** (Giles 2015, §3.1 and the driver `mlmc.m`, which stops on
`rem ≤ ε/√2`): if the robust test passes non-strictly, `alg1Rem ≤ ε/√2`, and the other hypotheses
of `robust_test_mse` hold, then `E[(Y − E[P])²] ≤ ε²`.  With `L = alg1Level` (`alg1Level_spec`)
and the multilevel estimator on the counts `alg1Samples` (`alg1_variance`), this is the guarantee
of the idealised Algorithm 1. -/
theorem alg1_mse {Y P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} {α ε : ℝ} {L k : ℕ} (hα : 0 < α)
    (hk : k ≤ 2) (hkL : k ≤ L) (hY : MemLp Y 2 μ) (hPl : ∀ ℓ, Integrable (Pl ℓ) μ)
    (hlim : Tendsto (fun ℓ => μ[Pl ℓ]) atTop (𝓝 (μ[P])))
    (hdecay : ∀ ℓ : ℕ, L < ℓ → |∫ ω, levelDiff Pl ℓ ω ∂μ| ≤
      |∫ ω, levelDiff Pl (L - k) ω ∂μ| * (2 : ℝ) ^ (-(α * ((ℓ : ℝ) - (L - k : ℕ)))))
    (hmean : μ[Y] = μ[Pl L]) (hV : variance Y μ ≤ ε ^ 2 / 2)
    (htest : alg1Rem (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) α L ≤ ε / Real.sqrt 2) :
    μ[fun ω => (Y ω - μ[P]) ^ 2] ≤ ε ^ 2 := by
  have hb := (abs_integral_sub_le_alg1Rem hα hk hkL hPl hlim hdecay).trans htest
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hbias2 : (μ[P] - μ[Pl L]) ^ 2 ≤ ε ^ 2 / 2 :=
    calc (μ[P] - μ[Pl L]) ^ 2 = |μ[P] - μ[Pl L]| ^ 2 := (sq_abs _).symm
      _ ≤ (ε / Real.sqrt 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = ε ^ 2 / 2 := by rw [div_pow, hs2]
  rw [mse_eq_variance_add_sq_bias hY (μ[P]), hmean]
  have e : (μ[Pl L] - μ[P]) ^ 2 = (μ[P] - μ[Pl L]) ^ 2 := by ring
  rw [e]
  linarith

/-- **Algorithm 1 is heuristic** (Giles 2015, §3.1, p. 21: "It is important to note that this
algorithm is heuristic; it is not guaranteed to achieve a MSE error which is less than `ε²`").  On
every probability space, for all `α`, `ε > 0` and `B`, there are integrable level approximations
`P_ℓ` with `E[P_ℓ] → E[P]` for which Algorithm 1 stops at `L = 2` (the corrections `E[P_ℓ − P_{ℓ−1}]`
inspected by the test vanish) while every estimator `Y` with `E[Y] = E[P_2]` has MSE at least
`B`. -/
theorem alg1_not_guaranteed (α : ℝ) {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∃ (P : Ω → ℝ) (Pl : ℕ → Ω → ℝ), Integrable P μ ∧ (∀ ℓ, Integrable (Pl ℓ) μ) ∧
      Tendsto (fun ℓ => μ[Pl ℓ]) atTop (𝓝 (μ[P])) ∧
      alg1Level (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) α ε = 2 ∧
      ∀ Y : Ω → ℝ, MemLp Y 2 μ → μ[Y] = μ[Pl 2] → B ≤ μ[fun ω => (Y ω - μ[P]) ^ 2] := by
  set b : ℝ := |B| + 1 with hb_def
  set c : ℕ → ℝ := fun ℓ => if ℓ ≤ 2 then 0 else b with hc_def
  have hint : ∀ x : ℝ, ∫ _ : Ω, x ∂μ = x := fun x => by simp
  have hc0 : ∀ j ≤ 2, c j = 0 := fun j hj => if_pos hj
  refine ⟨fun _ => b, fun ℓ _ => c ℓ, integrable_const _, fun ℓ => integrable_const _, ?_, ?_,
    ?_⟩
  · -- `E[P_ℓ] = b` for `ℓ ≥ 3`
    show Tendsto (fun ℓ => ∫ _ : Ω, c ℓ ∂μ) atTop (𝓝 (∫ _ : Ω, b ∂μ))
    simp only [hint]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with ℓ hℓ
    show b = if ℓ ≤ 2 then 0 else b
    rw [if_neg (by omega)]
  · -- the test passes at `L = 2`, where all inspected corrections vanish
    have hm : ∀ ℓ ≤ 2, ∫ ω, levelDiff (fun ℓ (_ : Ω) => c ℓ) ℓ ω ∂μ = 0 := by
      intro ℓ hℓ
      rcases (by omega : ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2) with rfl | rfl | rfl
      · simp [hc0 0 (by norm_num)]
      · simp [levelDiff, hc0 0 (by norm_num), hc0 1 (by norm_num)]
      · simp [levelDiff, hc0 1 (by norm_num), hc0 2 (by norm_num)]
    have hrem : alg1Rem (fun ℓ => ∫ ω, levelDiff (fun ℓ (_ : Ω) => c ℓ) ℓ ω ∂μ) α 2 = 0 := by
      have h0 := hm 0 (by norm_num)
      have h1 := hm 1 (by norm_num)
      have h2 := hm 2 le_rfl
      simp [alg1Rem, h0, h1, h2]
    have hpass : alg1Rem (fun ℓ => ∫ ω, levelDiff (fun ℓ (_ : Ω) => c ℓ) ℓ ω ∂μ) α 2 ≤
        ε / Real.sqrt 2 := by
      rw [hrem]
      positivity
    exact le_antisymm (alg1Level_le_of le_rfl hpass) (alg1Level_spec ⟨2, le_rfl, hpass⟩).1
  · -- the bias is `b ≥ B`
    intro Y hY hmean
    have hP2 : μ[fun _ : Ω => c 2] = 0 := by simp [hc0 2 le_rfl]
    have hPb : μ[fun _ : Ω => b] = b := by simp
    rw [mse_eq_variance_add_sq_bias hY, hmean, hP2, hPb]
    have hv := variance_nonneg Y μ
    have hb1 : 1 ≤ b := by rw [hb_def]; linarith [abs_nonneg B]
    have hBb : B ≤ b := by rw [hb_def]; linarith [le_abs_self B]
    nlinarith [sq_nonneg (b - 1)]

end Probability

/-! ### The cost of the idealised algorithm -/

/-- **The cost of Algorithm 1 has the order of Theorem 1** (Giles 2015, §3.1, under the hypotheses
of Theorem 1, §2.1).  Let `α, γ, c₁, c₂, c₃ > 0` with `α ≥ ½ min(β, γ)`, and `N₀ ∈ ℕ`.  There is
`c₄ > 0` such that for every `0 < ε < e⁻¹` and all exact level data — corrections with
`|m_ℓ| ≤ c₁ 2^{−αℓ}` (condition i)), variances `0 < V_ℓ ≤ c₂ 2^{−βℓ}` (iii)) and costs
`0 < C_ℓ ≤ c₃ 2^{γℓ}` (iv)) — the idealised Algorithm 1 stops at `L = alg1Level m α ε` with total
cost `∑_{ℓ ≤ L} N_ℓ C_ℓ ≤ c₄ · complexityBound α β γ ε`, where `N_ℓ = alg1Samples N₀ V C ε L ℓ`
are its sample counts. -/
theorem alg1_complexity {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α) (N₀ : ℕ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) → ∀ m V C : ℕ → ℝ,
      (∀ ℓ : ℕ, |m ℓ| ≤ c₁ * (2 : ℝ) ^ (-(α * ℓ))) →
      (∀ ℓ, 0 < V ℓ) → (∀ ℓ, V ℓ ≤ Vb β c₂ ℓ) → (∀ ℓ, 0 < C ℓ) → (∀ ℓ, C ℓ ≤ Cb γ c₃ ℓ) →
      ∑ ℓ ∈ range (alg1Level m α ε + 1),
          (alg1Samples N₀ V C ε (alg1Level m α ε) ℓ : ℝ) * C ℓ ≤
        c₄ * complexityBound α β γ ε := by
  have h2α := two_rpow_sub_one_pos hα
  set c' : ℝ := c₁ / ((2 : ℝ) ^ α - 1) with hc'_def
  have hc' : 0 < c' := div_pos hc₁ h2α
  set K : ℝ := (2 : ℝ) ^ (2 * α) + (2 : ℝ) ^ α * (1 + Real.sqrt 2 * c') with hK_def
  have hK : 0 < K := by rw [hK_def]; positivity
  obtain ⟨c₄, hc₄, hcost⟩ := cost_le_of_level (β := β) hα hγ hc₂ hc₃ hK hαβγ
  set A : ℝ := (N₀ : ℝ) * (Cb γ c₃ 0 + Cb γ c₃ 1 + Cb γ c₃ 2) with hA_def
  have hA : 0 ≤ A := by
    have h0 := Cb_pos (γ := γ) hc₃ 0
    have h1 := Cb_pos (γ := γ) hc₃ 1
    have h2 := Cb_pos (γ := γ) hc₃ 2
    rw [hA_def]
    positivity
  refine ⟨A + c₄, by positivity, fun ε hε hε1 m V C hm hV0 hV hC0 hC => ?_⟩
  have hε1' : ε < 1 := eps_lt_one hε1
  have hδ : 0 < ε / Real.sqrt 2 := div_pos hε (Real.sqrt_pos.2 two_pos)
  obtain ⟨hL2, -, hLle⟩ := alg1Level_le hα hc₁ hε hm
  set L := alg1Level m α ε with hL_def
  -- `2^{αL} ≤ K/ε`
  have hLK : (2 : ℝ) ^ (α * (L : ℝ)) ≤ K / ε := by
    set ℓ₁ : ℕ := levelL α c' (ε / Real.sqrt 2) with hℓ₁
    have hmono : (2 : ℝ) ^ (α * (L : ℝ)) ≤ (2 : ℝ) ^ (α * ((max 2 ℓ₁ : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two
        (mul_le_mul_of_nonneg_left (Nat.cast_le.2 hLle) hα.le)
    have hℓ₁b : (2 : ℝ) ^ (α * (ℓ₁ : ℝ)) ≤ 2 ^ α * max 1 (c' / (ε / Real.sqrt 2)) :=
      two_rpow_levelL_le hα hc' hδ
    have hs : 0 ≤ Real.sqrt 2 * c' := mul_nonneg (Real.sqrt_nonneg 2) hc'.le
    have hmax : max 1 (c' / (ε / Real.sqrt 2)) ≤ (1 + Real.sqrt 2 * c') / ε := by
      apply max_le
      · rw [le_div_iff₀ hε]
        linarith
      · rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hε, mul_comm c']
        linarith
    have h2 : (2 : ℝ) ^ (α * ((max 2 ℓ₁ : ℕ) : ℝ)) ≤
        (2 : ℝ) ^ (2 * α) + (2 : ℝ) ^ (α * (ℓ₁ : ℝ)) := by
      rcases le_total 2 ℓ₁ with h | h
      · rw [max_eq_right h]
        linarith [Real.rpow_pos_of_pos two_pos (2 * α)]
      · rw [max_eq_left h, show α * ((2 : ℕ) : ℝ) = 2 * α by push_cast; ring]
        linarith [Real.rpow_pos_of_pos two_pos (α * (ℓ₁ : ℝ))]
    have h4 : (2 : ℝ) ^ (2 * α) ≤ (2 : ℝ) ^ (2 * α) / ε := by
      rw [le_div_iff₀ hε]
      nlinarith [Real.rpow_pos_of_pos two_pos (2 * α)]
    calc (2 : ℝ) ^ (α * (L : ℝ)) ≤ (2 : ℝ) ^ (α * ((max 2 ℓ₁ : ℕ) : ℝ)) := hmono
      _ ≤ (2 : ℝ) ^ (2 * α) + (2 : ℝ) ^ (α * (ℓ₁ : ℝ)) := h2
      _ ≤ (2 : ℝ) ^ (2 * α) / ε + 2 ^ α * ((1 + Real.sqrt 2 * c') / ε) :=
          add_le_add h4
            (hℓ₁b.trans (mul_le_mul_of_nonneg_left hmax (Real.rpow_pos_of_pos two_pos _).le))
      _ = K / ε := by rw [hK_def]; ring
  -- the cost splits into the initial samples and the targets (3.1)
  have hsplit : ∑ ℓ ∈ range (L + 1), (alg1Samples N₀ V C ε L ℓ : ℝ) * C ℓ ≤
      ∑ ℓ ∈ range (L + 1), (alg1Init N₀ ℓ : ℝ) * C ℓ +
        ∑ ℓ ∈ range (L + 1), (optimalN (range (L + 1)) V C (ε ^ 2 / 2) ℓ : ℝ) * C ℓ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ℓ _ => ?_
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hC0 ℓ).le
    exact_mod_cast alg1Samples_le N₀ V C hε L ℓ
  -- the initial samples cost at most `N₀ (C₀ + C₁ + C₂) ≤ A`
  have hinit : ∑ ℓ ∈ range (L + 1), (alg1Init N₀ ℓ : ℝ) * C ℓ ≤ A := by
    have hsub : ∑ ℓ ∈ range (L + 1), (alg1Init N₀ ℓ : ℝ) * C ℓ =
        ∑ ℓ ∈ range 3, (N₀ : ℝ) * C ℓ := by
      rw [← Finset.sum_range_add_sum_Ico _ (by omega : 3 ≤ L + 1)]
      have h0 : ∑ ℓ ∈ Ico 3 (L + 1), (alg1Init N₀ ℓ : ℝ) * C ℓ = 0 :=
        Finset.sum_eq_zero fun ℓ hℓ => by
          have h3 := (Finset.mem_Ico.1 hℓ).1
          rw [alg1Init, if_neg (by omega), Nat.cast_zero, zero_mul]
      rw [h0, add_zero]
      exact Finset.sum_congr rfl fun ℓ hℓ => by
        have h3 := Finset.mem_range.1 hℓ
        rw [alg1Init, if_pos (by omega)]
    rw [hsub, hA_def, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    linarith [hC 0, hC 1, hC 2]
  -- the targets cost at most the bound of `optimalN_cost` with the model rates
  have htarget : ∑ ℓ ∈ range (L + 1), (optimalN (range (L + 1)) V C (ε ^ 2 / 2) ℓ : ℝ) * C ℓ ≤
      2 * ε⁻¹ ^ 2 * (c₂ * c₃) * (∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) ^ 2
        + c₃ * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ γ) ^ ℓ := by
    have hτ : 0 < ε ^ 2 / 2 := by positivity
    have hs : (range (L + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos L)⟩
    have hc := optimalN_cost hs (fun ℓ _ => hV0 ℓ) (fun ℓ _ => hC0 ℓ) hτ
    have hS : ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) ≤
        Real.sqrt (c₂ * c₃) * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ℓ _ => ?_
      rw [← sqrt_Vb_mul_Cb hc₂ hc₃ ℓ]
      exact Real.sqrt_le_sqrt (mul_le_mul (hV ℓ) (hC ℓ) (hC0 ℓ).le (Vb_pos hc₂ ℓ).le)
    have hS0 : 0 ≤ ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) :=
      Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
    have hCs : ∑ ℓ ∈ range (L + 1), C ℓ ≤ c₃ * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ γ) ^ ℓ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ℓ _ => ?_
      calc C ℓ ≤ Cb γ c₃ ℓ := hC ℓ
        _ = c₃ * ((2 : ℝ) ^ γ) ^ ℓ := by unfold Cb; rw [two_rpow_mul_nat]
    have hτinv : (ε ^ 2 / 2)⁻¹ = 2 * ε⁻¹ ^ 2 := by
      rw [inv_div, inv_pow]
      ring
    calc ∑ ℓ ∈ range (L + 1), (optimalN (range (L + 1)) V C (ε ^ 2 / 2) ℓ : ℝ) * C ℓ
        ≤ (ε ^ 2 / 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 +
            ∑ ℓ ∈ range (L + 1), C ℓ := hc
      _ ≤ (ε ^ 2 / 2)⁻¹ *
            (Real.sqrt (c₂ * c₃) * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) ^ 2
            + c₃ * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ γ) ^ ℓ := by
          gcongr
      _ = 2 * ε⁻¹ ^ 2 * (c₂ * c₃) * (∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) ^ 2
            + c₃ * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ γ) ^ ℓ := by
          rw [hτinv, mul_pow, Real.sq_sqrt (mul_pos hc₂ hc₃).le]
          ring
  have h1 := one_le_complexityBound (β := β) (γ := γ) hα hε hε1
  calc ∑ ℓ ∈ range (L + 1), (alg1Samples N₀ V C ε L ℓ : ℝ) * C ℓ
      ≤ ∑ ℓ ∈ range (L + 1), (alg1Init N₀ ℓ : ℝ) * C ℓ +
          ∑ ℓ ∈ range (L + 1), (optimalN (range (L + 1)) V C (ε ^ 2 / 2) ℓ : ℝ) * C ℓ := hsplit
    _ ≤ A + c₄ * complexityBound α β γ ε :=
        add_le_add hinit (htarget.trans (hcost ε hε hε1 L hLK))
    _ ≤ (A + c₄) * complexityBound α β γ ε := by
        rw [add_mul]
        exact add_le_add_right (le_mul_of_one_le_right hA h1) _

end MLMC
