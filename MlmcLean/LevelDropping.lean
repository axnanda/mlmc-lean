import MlmcLean.ControlVariate

/-!
# Non-geometric MLMC: when to drop a level (Giles 2015, §2.6)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.6
(pp. 18–20 of the author's version).

"MLMC does not require the use of a geometric sequence of grids."  Given levels `0, …, L`, Giles
asks whether it is better to keep a level `ℓ` or to drop it and jump from `ℓ − 1` to `ℓ + 1`.  With
`V_ℓ = V[P_ℓ − P_{ℓ−1}]`, `C_ℓ` its cost, `Ṽ_{ℓ+1} = V[P_{ℓ+1} − P_{ℓ−1}]` and `C̃_{ℓ+1}` its cost:

* keeping level `ℓ`, the product of the combined variance and the combined cost of the two
  estimators that involve level `ℓ` is at best `V_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`
  (`levelKeep_product`), while dropping it gives `Ṽ_{ℓ+1} C̃_{ℓ+1}`;
* the test (2.5), `Ṽ_{ℓ+1} C̃_{ℓ+1} < V_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`, holds
  exactly when dropping level `ℓ` lowers the optimal cost (1.1) of the whole hierarchy for a given
  variance, equivalently the optimal variance for a given cost (`levelDrop_test`);
* `Ṽ_{ℓ+1} = V_{ℓ+1} + 2ρ √(V_ℓ V_{ℓ+1}) + V_ℓ` with `ρ` the correlation of the two increments
  (`levelDrop_variance`); for `ρ = 1` and `C_ℓ ≤ C_{ℓ+1} = C̃_{ℓ+1}` the test fails, so level `ℓ` is
  kept (`levelDrop_perfect_correlation`); for `ρ = 0` it reads
  `1 + V_ℓ/V_{ℓ+1} < (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²` (`levelDrop_uncorrelated`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

-- `x (1 + √(y/x))² = (√y + √x)²` for `x > 0`
lemma mul_one_add_sqrt_div_sq {x y : ℝ} (hx : 0 < x) :
    x * (1 + Real.sqrt (y / x)) ^ 2 = (Real.sqrt y + Real.sqrt x) ^ 2 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 : (1 + Real.sqrt y / Real.sqrt x) * Real.sqrt x = Real.sqrt y + Real.sqrt x := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ hs.ne', add_comm]
  rw [Real.sqrt_div' y hx.le, ← h1, mul_pow, Real.sq_sqrt hx.le, mul_comm]

/-- **Keeping level `ℓ`** (Giles 2015, §2.6, pp. 18–19): "If we keep level `ℓ` then the contribution
to the overall multilevel estimator due to samples involving level `ℓ` is
`N_ℓ⁻¹ ∑ (P_ℓ − P_{ℓ−1}) + N_{ℓ+1}⁻¹ ∑ (P_{ℓ+1} − P_ℓ)` … and so the product of the combined
variance and combined cost is `V_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`" for the optimal
ratio of `N_ℓ` to `N_{ℓ+1}`.  For positive `V_ℓ, V_{ℓ+1}, C_ℓ, C_{ℓ+1}` this value is the least
product `(V_ℓ/N_ℓ + V_{ℓ+1}/N_{ℓ+1})(N_ℓ C_ℓ + N_{ℓ+1} C_{ℓ+1})` over all real
`N_ℓ, N_{ℓ+1} > 0`. -/
theorem levelKeep_product {Vℓ Vℓ₁ Cℓ Cℓ₁ : ℝ} (hV : 0 < Vℓ) (hV₁ : 0 < Vℓ₁) (hC : 0 < Cℓ)
    (hC₁ : 0 < Cℓ₁) :
    IsLeast {x | ∃ n n₁ : ℝ, 0 < n ∧ 0 < n₁ ∧ x = (Vℓ / n + Vℓ₁ / n₁) * (n * Cℓ + n₁ * Cℓ₁)}
      (Vℓ₁ * Cℓ₁ * (1 + Real.sqrt (Vℓ * Cℓ / (Vℓ₁ * Cℓ₁))) ^ 2) := by
  rw [mul_one_add_sqrt_div_sq (mul_pos hV₁ hC₁)]
  have two : ∀ a b : ℝ, 0 < a → 0 < b → ∀ i, 0 < (![a, b] : Fin 2 → ℝ) i := fun a b ha hb =>
    (Fin.forall_fin_two (p := fun j => 0 < (![a, b] : Fin 2 → ℝ) j)).2 ⟨ha, hb⟩
  refine ⟨⟨Real.sqrt (Vℓ / Cℓ), Real.sqrt (Vℓ₁ / Cℓ₁), Real.sqrt_pos.2 (div_pos hV hC),
    Real.sqrt_pos.2 (div_pos hV₁ hC₁), ?_⟩, ?_⟩
  · -- the optimal allocation `N ∝ √(V/C)`: variance and cost both equal `∑ √(V C)`
    have hr₀ : 0 < Real.sqrt (Vℓ / Cℓ) := Real.sqrt_pos.2 (div_pos hV hC)
    have hr₁ : 0 < Real.sqrt (Vℓ₁ / Cℓ₁) := Real.sqrt_pos.2 (div_pos hV₁ hC₁)
    have e0 : Vℓ / Real.sqrt (Vℓ / Cℓ) = Real.sqrt (Vℓ * Cℓ) := by
      rw [div_eq_iff hr₀.ne']
      linear_combination -(sqrt_div_mul_sqrt_mul hV.le hC)
    have e1 : Vℓ₁ / Real.sqrt (Vℓ₁ / Cℓ₁) = Real.sqrt (Vℓ₁ * Cℓ₁) := by
      rw [div_eq_iff hr₁.ne']
      linear_combination -(sqrt_div_mul_sqrt_mul hV₁.le hC₁)
    rw [e0, e1, sqrt_div_mul hV.le hC, sqrt_div_mul hV₁.le hC₁]
    ring
  · -- every allocation: Cauchy–Schwarz, `(∑ √(V C))² ≤ (∑ V/N)(∑ N C)`
    rintro x ⟨n, n₁, hn, hn₁, rfl⟩
    have hτ : 0 < Vℓ / n + Vℓ₁ / n₁ := add_pos (div_pos hV hn) (div_pos hV₁ hn₁)
    have h := cost_lower_bound (Finset.univ : Finset (Fin 2)) ![Vℓ, Vℓ₁] ![Cℓ, Cℓ₁] ![n, n₁] hτ
      (fun i _ => (two Vℓ Vℓ₁ hV hV₁ i).le) (fun i _ => (two Cℓ Cℓ₁ hC hC₁ i).le)
      (fun i _ => two n n₁ hn hn₁ i) (by rw [Fin.sum_univ_two]; exact le_rfl)
    rw [Fin.sum_univ_two, Fin.sum_univ_two, inv_mul_le_iff₀ hτ] at h
    exact h

/-- **The level-dropping test (2.5)** (Giles 2015, §2.6, p. 19): "The question now is whether
`Ṽ_{ℓ+1} C̃_{ℓ+1} < V_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`  (2.5).  If this test is
true, then it is best to drop level `ℓ`, because for a fixed computational cost this will deliver
the lower variance, or for a fixed variance it can be achieved at a lower computational cost."
Let the levels other than `ℓ` and `ℓ + 1` be indexed by a finite set `s`, with per-sample variances
`V_i` and costs `C_i`.  By (1.1) the least cost for a variance target `τ > 0` is `τ⁻¹ (∑ √(V C))²`
over the levels used, and the least variance for a cost budget `τ` has the same form
(`optimal_cost_isLeast`, `optimal_variance_isLeast`).  Replacing the corrections on levels `ℓ` and
`ℓ + 1` by the single correction `P_{ℓ+1} − P_{ℓ−1}` (variance `Ṽ`, cost `C̃`) makes this value
strictly smaller if and only if (2.5) holds. -/
theorem levelDrop_test {ι : Type*} (s : Finset ι) (V C : ι → ℝ) {Vℓ Vℓ₁ Cℓ Cℓ₁ Vd Cd τ : ℝ}
    (hV₁ : 0 < Vℓ₁) (hC₁ : 0 < Cℓ₁) (hτ : 0 < τ) :
    τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i) + Real.sqrt (Vd * Cd)) ^ 2 <
        τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i) + Real.sqrt (Vℓ * Cℓ) +
          Real.sqrt (Vℓ₁ * Cℓ₁)) ^ 2 ↔
      Vd * Cd < Vℓ₁ * Cℓ₁ * (1 + Real.sqrt (Vℓ * Cℓ / (Vℓ₁ * Cℓ₁))) ^ 2 := by
  have hS0 : 0 ≤ ∑ i ∈ s, Real.sqrt (V i * C i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have ha := Real.sqrt_nonneg (Vℓ * Cℓ)
  have hb : 0 < Real.sqrt (Vℓ₁ * Cℓ₁) := Real.sqrt_pos.2 (mul_pos hV₁ hC₁)
  have hd := Real.sqrt_nonneg (Vd * Cd)
  rw [mul_one_add_sqrt_div_sq (mul_pos hV₁ hC₁), mul_lt_mul_iff_of_pos_left (inv_pos.2 hτ),
    pow_lt_pow_iff_left₀ (add_nonneg hS0 hd) (add_nonneg (add_nonneg hS0 ha) hb.le) two_ne_zero,
    add_assoc, add_lt_add_iff_left, Real.sqrt_lt' (add_pos_of_nonneg_of_pos ha hb)]

section prob

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Giles 2015, §2.6, p. 20: "Using the standard result for the variance of a sum of two random
variables, we have `Ṽ_{ℓ+1} = V_{ℓ+1} + 2ρ √(V_ℓ V_{ℓ+1}) + V_ℓ`, where `ρ` is the correlation
between `P_{ℓ+1} − P_ℓ` and `P_ℓ − P_{ℓ−1}`."  Here `X = P_{ℓ+1} − P_ℓ` and `Y = P_ℓ − P_{ℓ−1}`
are square-integrable with positive variances, so `X + Y = P_{ℓ+1} − P_{ℓ−1}`. -/
theorem levelDrop_variance {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hVX : 0 < variance X μ) (hVY : 0 < variance Y μ) :
    variance (fun ω => X ω + Y ω) μ = variance X μ +
      2 * correlation X Y μ * Real.sqrt (variance Y μ * variance X μ) + variance Y μ := by
  rw [variance_fun_add hX hY, correlation, mul_comm (variance Y μ) (variance X μ), mul_assoc 2,
    div_mul_cancel₀ _ (Real.sqrt_pos.2 (mul_pos hVX hVY)).ne']

/-- **Perfectly correlated increments: keep the level** (Giles 2015, §2.6, p. 20): "If `ρ = 1`, and
so we have perfect correlation between the increments at different levels, then
`Ṽ_{ℓ+1} = V_{ℓ+1} (1 + √(V_ℓ/V_{ℓ+1}))²`.  Since `C_ℓ < C_{ℓ+1}`, it follows that the test (2.5)
is never satisfied, and so it is best to retain level `ℓ`."  With `X = P_{ℓ+1} − P_ℓ`,
`Y = P_ℓ − P_{ℓ−1}`, correlation `1`, `0 < C_ℓ ≤ C_{ℓ+1}` and the paper's approximation
`C̃_{ℓ+1} = C_{ℓ+1}`, the test (2.5) fails. -/
theorem levelDrop_perfect_correlation {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hVX : 0 < variance X μ) (hVY : 0 < variance Y μ) (hρ : correlation X Y μ = 1)
    {Cℓ Cℓ₁ : ℝ} (hC : 0 < Cℓ) (hCC : Cℓ ≤ Cℓ₁) :
    variance (fun ω => X ω + Y ω) μ =
        variance X μ * (1 + Real.sqrt (variance Y μ / variance X μ)) ^ 2 ∧
      ¬ variance (fun ω => X ω + Y ω) μ * Cℓ₁ <
        variance X μ * Cℓ₁ * (1 + Real.sqrt (variance Y μ * Cℓ / (variance X μ * Cℓ₁))) ^ 2 := by
  have hC₁ : 0 < Cℓ₁ := hC.trans_le hCC
  have hsum : variance (fun ω => X ω + Y ω) μ =
      variance X μ * (1 + Real.sqrt (variance Y μ / variance X μ)) ^ 2 := by
    rw [levelDrop_variance hX hY hVX hVY, hρ, mul_one, mul_one_add_sqrt_div_sq hVX, add_sq,
      Real.sq_sqrt hVY.le, Real.sq_sqrt hVX.le, Real.sqrt_mul hVY.le]
    ring
  refine ⟨hsum, fun h => ?_⟩
  -- `√(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})) ≤ √(V_ℓ/V_{ℓ+1})` because `C_ℓ ≤ C_{ℓ+1}`
  have hq : Real.sqrt (variance Y μ * Cℓ / (variance X μ * Cℓ₁)) ≤
      Real.sqrt (variance Y μ / variance X μ) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (mul_pos hVX hC₁) hVX]
    nlinarith [mul_le_mul_of_nonneg_left hCC (mul_nonneg hVY.le hVX.le)]
  have hq0 := Real.sqrt_nonneg (variance Y μ * Cℓ / (variance X μ * Cℓ₁))
  have hsq : (1 + Real.sqrt (variance Y μ * Cℓ / (variance X μ * Cℓ₁))) ^ 2 ≤
      (1 + Real.sqrt (variance Y μ / variance X μ)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hle := mul_le_mul_of_nonneg_left hsq (mul_pos hVX hC₁).le
  rw [hsum] at h
  linarith

/-- **Uncorrelated increments** (Giles 2015, §2.6, p. 20): "if `ρ = 0`, and so the increments at
different levels are independent, then `Ṽ_{ℓ+1} = V_{ℓ+1} + V_ℓ` and so we drop level `ℓ` if
`1 + V_ℓ/V_{ℓ+1} < (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`."  With `X = P_{ℓ+1} − P_ℓ`,
`Y = P_ℓ − P_{ℓ−1}`, correlation `0` and `C̃_{ℓ+1} = C_{ℓ+1}`, the test (2.5) is equivalent to this
inequality. -/
theorem levelDrop_uncorrelated {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hVX : 0 < variance X μ) (hVY : 0 < variance Y μ) (hρ : correlation X Y μ = 0)
    {Cℓ Cℓ₁ : ℝ} (hC₁ : 0 < Cℓ₁) :
    variance (fun ω => X ω + Y ω) μ = variance X μ + variance Y μ ∧
      (variance (fun ω => X ω + Y ω) μ * Cℓ₁ <
          variance X μ * Cℓ₁ * (1 + Real.sqrt (variance Y μ * Cℓ / (variance X μ * Cℓ₁))) ^ 2 ↔
        1 + variance Y μ / variance X μ <
          (1 + Real.sqrt (variance Y μ * Cℓ / (variance X μ * Cℓ₁))) ^ 2) := by
  have hsum : variance (fun ω => X ω + Y ω) μ = variance X μ + variance Y μ := by
    rw [levelDrop_variance hX hY hVX hVY, hρ]
    ring
  refine ⟨hsum, ?_⟩
  have hdiv : variance Y μ / variance X μ * variance X μ = variance Y μ :=
    div_mul_cancel₀ _ hVX.ne'
  have e : (variance X μ + variance Y μ) * Cℓ₁ =
      variance X μ * Cℓ₁ * (1 + variance Y μ / variance X μ) := by
    linear_combination (-Cℓ₁) * hdiv
  rw [hsum, e, mul_lt_mul_iff_of_pos_left (mul_pos hVX hC₁)]

end prob

end MLMC
