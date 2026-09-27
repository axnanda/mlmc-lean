import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import MlmcLean.Allocation

/-!
# Giles' MLMC complexity theorem — the real-analysis core

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1, Theorem 1
(pp. 6–7 of the author's version; per p. 7, "a slight generalisation of the original theorem in
(Giles 2008b)", corresponding to the theorem of Cliffe, Giles, Scheichl and Teckentrup (2011) up to
the use of expected costs).

**Theorem 1 (Giles).** Let `P` be a random variable and `P_ℓ` its level-`ℓ` approximation.
If there exist independent estimators `Y_ℓ` based on `N_ℓ` Monte Carlo samples, each with
expected cost `C_ℓ` and variance `V_ℓ`, and positive constants `α, β, γ, c₁, c₂, c₃` with
`α ≥ ½ min(β, γ)` and

  (i)   `|E[P_ℓ − P]| ≤ c₁ 2^{−αℓ}`
  (ii)  `E[Y_ℓ] = E[P_0]` (ℓ = 0), `E[P_ℓ − P_{ℓ−1}]` (ℓ > 0)
  (iii) `V_ℓ ≤ c₂ 2^{−βℓ}`
  (iv)  `C_ℓ ≤ c₃ 2^{γℓ}`,

then there is a constant `c₄ > 0` such that for every `ε < e⁻¹` there are `L` and `N_ℓ` for which
`Y = ∑_{ℓ=0}^{L} Y_ℓ` has `MSE < ε²` and expected cost
`E[C] ≤ c₄ ε⁻²` (β > γ), `c₄ ε⁻² (log ε)²` (β = γ), `c₄ ε^{−2−(γ−β)/α}` (β < γ).

By `MlmcLean/Estimator.lean`, `MSE = ∑ V_ℓ/N_ℓ + (E[P_L] − E[P])²`, so — as in Giles' proof
sketch (p. 7) — everything reduces to the following deterministic statement, proved in this file as
`mlmc_complexity_core`: with `V_ℓ := c₂ 2^{−βℓ}` and `C_ℓ := c₃ 2^{γℓ}` there are `L` and
integers `N_ℓ ≥ 1` with

  `(c₁ 2^{−αL})² + ∑_{ℓ ≤ L} V_ℓ / N_ℓ < ε²`  and  `∑_{ℓ ≤ L} N_ℓ C_ℓ ≤ c₄ · bound(ε)`.

The proof follows the strategy of Giles' sketch (p. 7: "L is chosen so that
`(E[Y]−E[P])² < ½ε²`, and the constant of proportionality for `N_ℓ` is chosen so that
`V[Y] < ½ε²` … the optimal value is rounded up"), with the error split `bias ≤ ε/2`,
`variance ≤ ε²/2` and explicit constants of our own:
1. choose `L = ⌈log₂(2c₁/ε)/α⌉₊` so that the bias bound `c₁ 2^{−αL}` is `≤ ε/2`;
2. choose `N_ℓ = ⌈τ⁻¹ √(V_ℓ/C_ℓ) ∑ √(V_k C_k)⌉₊` with `τ = ε²/2` (the allocation of §1.3, p. 4,
   rounded up), which makes the variance `≤ ε²/2` and the cost `≤ τ⁻¹ (∑ √(V_ℓ C_ℓ))² + ∑ C_ℓ`
   (`MlmcLean/Allocation.lean`);
3. `√(V_ℓ C_ℓ) = √(c₂c₃) · 2^{(γ−β)ℓ/2}` is a geometric sequence, and the three regimes
   `β > γ`, `β = γ`, `β < γ` are the three behaviours of its partial sums; the rounding-up
   overhead `∑ C_ℓ` is `O(2^{γL}) = O(ε^{−γ/α})`, absorbed using `α ≥ ½ min(β,γ)`.
-/

open Finset Real

namespace MLMC

/-- The three complexity regimes of Giles' Theorem 1 (Giles 2015, §2.1, p. 7): `ε⁻²` for
`β > γ`, `ε⁻² (log ε)²` for `β = γ`, `ε^{−2−(γ−β)/α}` for `β < γ`. -/
noncomputable def complexityBound (α β γ ε : ℝ) : ℝ :=
  if γ < β then ε ^ (-2 : ℝ)
  else if β = γ then ε ^ (-2 : ℝ) * (Real.log ε) ^ 2
  else ε ^ (-2 - (γ - β) / α)

lemma complexityBound_of_lt {α β γ : ℝ} (h : γ < β) (ε : ℝ) :
    complexityBound α β γ ε = ε ^ (-2 : ℝ) := by
  simp [complexityBound, h]

lemma complexityBound_of_eq {α β γ : ℝ} (h : β = γ) (ε : ℝ) :
    complexityBound α β γ ε = ε ^ (-2 : ℝ) * (Real.log ε) ^ 2 := by
  simp [complexityBound, h]

lemma complexityBound_of_gt {α β γ : ℝ} (h : β < γ) (ε : ℝ) :
    complexityBound α β γ ε = ε ^ (-2 - (γ - β) / α) := by
  simp [complexityBound, h.ne, not_lt.2 h.le]

lemma complexityBound_nonneg {α β γ ε : ℝ} (hε : 0 < ε) : 0 ≤ complexityBound α β γ ε := by
  unfold complexityBound
  split_ifs <;> positivity

/-- The bound of condition (iii) of Giles' Theorem 1 (Giles 2015, §2.1) on the per-sample variance
at level `ℓ`: `c₂ 2^{−βℓ}`. -/
noncomputable def Vb (β c₂ : ℝ) (ℓ : ℕ) : ℝ := c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))

/-- The bound of condition (iv) of Giles' Theorem 1 (Giles 2015, §2.1) on the per-sample cost at
level `ℓ`: `c₃ 2^{γℓ}`. -/
noncomputable def Cb (γ c₃ : ℝ) (ℓ : ℕ) : ℝ := c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))

lemma Vb_pos {β c₂ : ℝ} (hc₂ : 0 < c₂) (ℓ : ℕ) : 0 < Vb β c₂ ℓ :=
  mul_pos hc₂ (Real.rpow_pos_of_pos two_pos _)

lemma Cb_pos {γ c₃ : ℝ} (hc₃ : 0 < c₃) (ℓ : ℕ) : 0 < Cb γ c₃ ℓ :=
  mul_pos hc₃ (Real.rpow_pos_of_pos two_pos _)

/-! ### Elementary facts about `2^x` and geometric sums -/

lemma two_rpow_mul_nat (y : ℝ) (n : ℕ) : (2 : ℝ) ^ (y * n) = ((2 : ℝ) ^ y) ^ n :=
  Real.rpow_mul_natCast (by norm_num) y n

/-- `√(V_ℓ C_ℓ) = √(c₂ c₃) · r^ℓ` with `r = 2^{(γ−β)/2}` (Giles 2015, p. 7: "the cost on level
`ℓ` is proportional to `2^{(γ−β)ℓ/2}`"). -/
lemma sqrt_Vb_mul_Cb {β γ c₂ c₃ : ℝ} (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (ℓ : ℕ) :
    Real.sqrt (Vb β c₂ ℓ * Cb γ c₃ ℓ) =
      Real.sqrt (c₂ * c₃) * ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hr : ((2 : ℝ) ^ ((γ - β) / 2)) ^ (2 * ℓ) = (2 : ℝ) ^ ((γ - β) * ℓ) := by
    rw [← Real.rpow_mul_natCast h2]
    congr 1
    push_cast
    ring
  have hsq : Vb β c₂ ℓ * Cb γ c₃ ℓ =
      (Real.sqrt (c₂ * c₃) * ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc₂ hc₃).le, ← pow_mul', hr]
    unfold Vb Cb
    rw [show c₂ * 2 ^ (-(β * (ℓ : ℝ))) * (c₃ * 2 ^ (γ * (ℓ : ℝ))) =
        c₂ * c₃ * (2 ^ (-(β * (ℓ : ℝ))) * 2 ^ (γ * (ℓ : ℝ))) by ring,
      ← Real.rpow_add two_pos]
    congr 2
    ring
  rw [hsq, Real.sqrt_sq (by positivity)]

lemma geom_sum_le_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ range n, r ^ i ≤ (1 - r)⁻¹ := by
  rw [geom_sum_eq hr1.ne n]
  have h : 0 < 1 - r := by linarith
  rw [div_le_iff_of_neg (by linarith : r - 1 < 0)]
  -- goal : (1 - r)⁻¹ * (r - 1) ≤ r ^ n - 1
  have : (1 - r)⁻¹ * (r - 1) = -1 := by
    rw [show r - 1 = -(1 - r) by ring, mul_neg, inv_mul_cancel₀ h.ne']
  rw [this]
  have := pow_nonneg hr0 n
  linarith

lemma geom_sum_le_of_one_lt {r : ℝ} (hr : 1 < r) (n : ℕ) :
    ∑ i ∈ range (n + 1), r ^ i ≤ r ^ n * (r / (r - 1)) := by
  rw [geom_sum_eq hr.ne' (n + 1)]
  have h : 0 < r - 1 := by linarith
  rw [div_le_iff₀ h]
  have : r ^ n * (r / (r - 1)) * (r - 1) = r ^ (n + 1) := by
    calc r ^ n * (r / (r - 1)) * (r - 1) = r ^ n * r * ((r - 1) / (r - 1)) := by ring
      _ = r ^ (n + 1) := by rw [div_self h.ne', mul_one, pow_succ]
  rw [this]
  linarith

/-! ### Step 1 — choice of the finest level `L` -/

/-- The finest level used in the proof of Theorem 1 (Giles 2015, p. 7): for `α, c₁, δ > 0`, the
least natural number `L` with `c₁ 2^{−αL} ≤ δ`, i.e. `⌈log₂(c₁/δ)/α⌉₊`.  The proof takes
`δ = ε/2`; Giles' sketch only requires `(E[Y] − E[P])² < ½ε²`. -/
noncomputable def levelL (α c₁ δ : ℝ) : ℕ := ⌈Real.logb 2 (c₁ / δ) / α⌉₊

lemma alpha_mul_div {α : ℝ} (hα : 0 < α) (l : ℝ) : α * (l / α) = l := by
  calc α * (l / α) = l * (α / α) := by ring
    _ = l := by rw [div_self hα.ne', mul_one]

/-- The bias bound at the level `levelL` is at most `δ` (proof of Theorem 1, Giles 2015, p. 7). -/
lemma levelL_bias {α c₁ δ : ℝ} (hα : 0 < α) (hc₁ : 0 < c₁) (hδ : 0 < δ) :
    c₁ * (2 : ℝ) ^ (-(α * (levelL α c₁ δ : ℝ))) ≤ δ := by
  have hx : Real.logb 2 (c₁ / δ) / α ≤ (levelL α c₁ δ : ℝ) := Nat.le_ceil _
  have h1 : Real.logb 2 (c₁ / δ) ≤ α * (levelL α c₁ δ : ℝ) := by
    have := mul_le_mul_of_nonneg_left hx hα.le
    rwa [alpha_mul_div hα] at this
  have h2 : c₁ / δ ≤ (2 : ℝ) ^ (α * (levelL α c₁ δ : ℝ)) :=
    (Real.logb_le_iff_le_rpow (by norm_num) (div_pos hc₁ hδ)).1 h1
  have hp : 0 < (2 : ℝ) ^ (α * (levelL α c₁ δ : ℝ)) := Real.rpow_pos_of_pos two_pos _
  rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv, div_le_iff₀ hp]
  rwa [div_le_iff₀ hδ, mul_comm] at h2

/-- `L < max 0 (log₂(c₁/δ)/α) + 1` for `L = levelL α c₁ δ` (proof of Theorem 1, Giles 2015,
p. 7). -/
lemma levelL_lt (α c₁ δ : ℝ) :
    (levelL α c₁ δ : ℝ) < max 0 (Real.logb 2 (c₁ / δ) / α) + 1 := by
  rcases le_or_gt 0 (Real.logb 2 (c₁ / δ) / α) with h | h
  · calc (levelL α c₁ δ : ℝ) < Real.logb 2 (c₁ / δ) / α + 1 := Nat.ceil_lt_add_one h
      _ ≤ max 0 (Real.logb 2 (c₁ / δ) / α) + 1 := by
          have := le_max_right 0 (Real.logb 2 (c₁ / δ) / α)
          linarith
  · have h0 : levelL α c₁ δ = 0 := Nat.ceil_eq_zero.2 h.le
    rw [h0]
    have := le_max_left 0 (Real.logb 2 (c₁ / δ) / α)
    push_cast
    linarith

/-- `2^{αL} ≤ 2^α · max 1 (c₁/δ)` for `L = levelL α c₁ δ` (proof of Theorem 1, Giles 2015,
p. 7: "`2^{−αL} = O(ε)`"). -/
lemma two_rpow_levelL_le {α c₁ δ : ℝ} (hα : 0 < α) (hc₁ : 0 < c₁) (hδ : 0 < δ) :
    (2 : ℝ) ^ (α * (levelL α c₁ δ : ℝ)) ≤ 2 ^ α * max 1 (c₁ / δ) := by
  have hL := levelL_lt α c₁ δ
  have hcd : 0 < c₁ / δ := div_pos hc₁ hδ
  have h1 : (2 : ℝ) ^ (α * (levelL α c₁ δ : ℝ)) ≤
      2 ^ (α * (max 0 (Real.logb 2 (c₁ / δ) / α) + 1)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hL.le hα.le)
  have h2 : (2 : ℝ) ^ (α * (max 0 (Real.logb 2 (c₁ / δ) / α) + 1)) = 2 ^ α * max 1 (c₁ / δ) := by
    rw [mul_add, mul_one, Real.rpow_add two_pos, mul_comm]
    congr 1
    rcases le_or_gt 0 (Real.logb 2 (c₁ / δ) / α) with h | h
    · have hlog : 0 ≤ Real.logb 2 (c₁ / δ) := by
        by_contra hneg
        have := div_neg_of_neg_of_pos (not_le.1 hneg) hα
        linarith
      have hge : 1 ≤ c₁ / δ := (Real.logb_nonneg_iff (by norm_num) hcd).1 hlog
      rw [max_eq_right h, alpha_mul_div hα, Real.rpow_logb (by norm_num) (by norm_num) hcd,
        max_eq_right hge]
    · have hlog : Real.logb 2 (c₁ / δ) < 0 := by
        by_contra hnn
        have := div_nonneg (not_lt.1 hnn) hα.le
        linarith
      have hle : c₁ / δ ≤ 1 := by
        by_contra hgt
        have h' : 0 ≤ Real.logb 2 (c₁ / δ) :=
          (Real.logb_nonneg_iff (by norm_num) hcd).2 (not_le.1 hgt).le
        linarith
      rw [max_eq_left h.le, mul_zero, Real.rpow_zero, max_eq_left hle]
  rw [h2] at h1
  exact h1

/-! ### Step 2 — the ε-dependent choice of `L` and `N_ℓ` -/

/-- The constant `K1 = 2^α (1 + 2c₁)`, a device of this formalisation of the proof of Theorem 1
(Giles 2015, p. 7): `2^{αL} ≤ K1/ε`. -/
noncomputable def K1 (α c₁ : ℝ) : ℝ := 2 ^ α * (1 + 2 * c₁)

/-- The constant `K2`, a device of this formalisation of the proof of Theorem 1 (Giles 2015,
p. 7): `L + 1 ≤ K2 · |log ε|`. -/
noncomputable def K2 (α c₁ : ℝ) : ℝ := (|Real.log (2 * c₁)| + 1) / (α * Real.log 2) + 2

lemma K1_pos {α c₁ : ℝ} (hc₁ : 0 < c₁) : 0 < K1 α c₁ := by
  unfold K1; positivity

lemma K2_pos {α c₁ : ℝ} (hα : 0 < α) : 0 < K2 α c₁ := by
  unfold K2
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

lemma eps_lt_one {ε : ℝ} (hε1 : ε < Real.exp (-1)) : ε < 1 :=
  lt_trans hε1 (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by norm_num))

lemma one_le_neg_log {ε : ℝ} (hε : 0 < ε) (hε1 : ε < Real.exp (-1)) : 1 ≤ -Real.log ε := by
  have := Real.log_lt_log hε hε1
  rw [Real.log_exp] at this
  linarith

/-- **The choice of `L` and `N_ℓ`** in this formalisation of the proof of Theorem 1 (Giles 2015,
p. 7): `L = levelL α c₁ (ε/2)` and the rounded-up optimal allocation, with five estimates:
bias² `≤ ε²/4`, variance `≤ ε²/2`, the cost, `2^{αL} ≤ K1/ε` and `L + 1 ≤ K2 |log ε|`. -/
theorem exists_L_N {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₃ : 0 < c₃) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 ≤ ε ^ 2 / 4 ∧
      ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) ≤ ε ^ 2 / 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ ≤
        2 * ε⁻¹ ^ 2 * (c₂ * c₃) * (∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) ^ 2
          + c₃ * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ γ) ^ ℓ ∧
      (2 : ℝ) ^ (α * (L : ℝ)) ≤ K1 α c₁ / ε ∧
      (L : ℝ) + 1 ≤ K2 α c₁ * (-Real.log ε) := by
  have hδpos : 0 < ε / 2 := by positivity
  have hτpos : 0 < ε ^ 2 / 2 := by positivity
  have hVpos : ∀ ℓ, 0 < Vb β c₂ ℓ := Vb_pos hc₂
  have hCpos : ∀ ℓ, 0 < Cb γ c₃ ℓ := Cb_pos hc₃
  have hs : (range (levelL α c₁ (ε / 2) + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
  refine ⟨levelL α c₁ (ε / 2),
    optimalN (range (levelL α c₁ (ε / 2) + 1)) (Vb β c₂) (Cb γ c₃) (ε ^ 2 / 2),
    fun ℓ => optimalN_pos hs hVpos hCpos hτpos ℓ, ?_, ?_, ?_, ?_, ?_⟩
  · -- bias
    have hb := levelL_bias hα hc₁ hδpos
    have h0 : 0 ≤ c₁ * (2 : ℝ) ^ (-(α * (levelL α c₁ (ε / 2) : ℝ))) := by positivity
    calc (c₁ * (2 : ℝ) ^ (-(α * (levelL α c₁ (ε / 2) : ℝ)))) ^ 2 ≤ (ε / 2) ^ 2 := by gcongr
      _ = ε ^ 2 / 4 := by ring
  · -- variance
    exact optimalN_variance hs (fun ℓ _ => hVpos ℓ) (fun ℓ _ => hCpos ℓ) hτpos
  · -- cost
    have hc := optimalN_cost hs (fun ℓ _ => hVpos ℓ) (fun ℓ _ => hCpos ℓ) hτpos
    have hS : ∑ ℓ ∈ range (levelL α c₁ (ε / 2) + 1), Real.sqrt (Vb β c₂ ℓ * Cb γ c₃ ℓ) =
        Real.sqrt (c₂ * c₃) *
          ∑ ℓ ∈ range (levelL α c₁ (ε / 2) + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => sqrt_Vb_mul_Cb hc₂ hc₃ ℓ
    have hτinv : (ε ^ 2 / 2)⁻¹ = 2 * ε⁻¹ ^ 2 := by
      rw [inv_div, inv_pow]
      ring
    have hCsum : ∑ ℓ ∈ range (levelL α c₁ (ε / 2) + 1), Cb γ c₃ ℓ =
        c₃ * ∑ ℓ ∈ range (levelL α c₁ (ε / 2) + 1), ((2 : ℝ) ^ γ) ^ ℓ := by
      unfold Cb
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by rw [two_rpow_mul_nat]
    rw [hS, hτinv, hCsum, mul_pow, Real.sq_sqrt (mul_pos hc₂ hc₃).le] at hc
    calc _ ≤ _ := hc
      _ = _ := by ring
  · -- 2^{αL} ≤ K1/ε
    have h := two_rpow_levelL_le hα hc₁ hδpos
    have hε1' : ε < 1 := eps_lt_one hε1
    have hmax : max 1 (c₁ / (ε / 2)) ≤ (1 + 2 * c₁) / ε := by
      have e : c₁ / (ε / 2) = 2 * c₁ / ε := by
        rw [div_div_eq_mul_div, mul_comm]
      rw [e]
      apply max_le
      · rw [le_div_iff₀ hε]; linarith
      · rw [div_le_div_iff_of_pos_right hε]; linarith
    calc (2 : ℝ) ^ (α * (levelL α c₁ (ε / 2) : ℝ)) ≤ 2 ^ α * max 1 (c₁ / (ε / 2)) := h
      _ ≤ 2 ^ α * ((1 + 2 * c₁) / ε) := by gcongr
      _ = K1 α c₁ / ε := by unfold K1; ring
  · -- L + 1 ≤ K2 |log ε|
    have hL' := levelL_lt α c₁ (ε / 2)
    have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hx : Real.logb 2 (c₁ / (ε / 2)) / α =
        (Real.log (2 * c₁) + -Real.log ε) / (α * Real.log 2) := by
      rw [← Real.log_div_log, show c₁ / (ε / 2) = 2 * c₁ / ε by
        rw [div_div_eq_mul_div, mul_comm], Real.log_div (by positivity) hε.ne']
      rw [div_div]
      ring
    have hxle : Real.logb 2 (c₁ / (ε / 2)) / α ≤
        (|Real.log (2 * c₁)| + 1) / (α * Real.log 2) * (-Real.log ε) := by
      rw [hx, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      have h1 : Real.log (2 * c₁) ≤ |Real.log (2 * c₁)| := le_abs_self _
      have h2 : |Real.log (2 * c₁)| ≤ |Real.log (2 * c₁)| * (-Real.log ε) :=
        le_mul_of_one_le_right (abs_nonneg _) ht
      nlinarith
    have hmax0 : max 0 (Real.logb 2 (c₁ / (ε / 2)) / α) ≤
        (|Real.log (2 * c₁)| + 1) / (α * Real.log 2) * (-Real.log ε) :=
      max_le (mul_nonneg (div_nonneg (by positivity) (mul_pos hα hlog2).le) (by linarith)) hxle
    calc (levelL α c₁ (ε / 2) : ℝ) + 1 ≤ max 0 (Real.logb 2 (c₁ / (ε / 2)) / α) + 2 := by
          linarith
      _ ≤ (|Real.log (2 * c₁)| + 1) / (α * Real.log 2) * (-Real.log ε) + 2 * (-Real.log ε) :=
          add_le_add hmax0 (by linarith)
      _ = K2 α c₁ * (-Real.log ε) := by unfold K2; ring

/-! ### Step 3 — the three regimes -/

/-- `2^{pL} ≤ K^{p/α} ε^{−p/α}` whenever `2^{αL} ≤ K/ε` and `p ≥ 0` (proof of Theorem 1,
Giles 2015, p. 7). -/
lemma two_rpow_L_le {α p K ε L : ℝ} (hα : 0 < α) (hp : 0 ≤ p) (hK : 0 < K) (hε : 0 < ε)
    (h : (2 : ℝ) ^ (α * L) ≤ K / ε) :
    (2 : ℝ) ^ (p * L) ≤ K ^ (p / α) * ε ^ (-(p / α)) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have e : (2 : ℝ) ^ (p * L) = ((2 : ℝ) ^ (α * L)) ^ (p / α) := by
    rw [← Real.rpow_mul h2]
    congr 1
    calc p * L = (p / α) * (α * L) := by rw [← mul_assoc, div_mul_cancel₀ p hα.ne']
      _ = α * L * (p / α) := by ring
  rw [e, Real.rpow_neg hε.le, ← div_eq_mul_inv, ← Real.div_rpow hK.le hε.le]
  exact Real.rpow_le_rpow (Real.rpow_nonneg h2 _) h (div_nonneg hp hα.le)

/-- The rounding-up overhead `∑_{ℓ≤L} C_ℓ` (proof of Theorem 1, Giles 2015, p. 7: "the optimal
value is rounded up"): `c₃ ∑_{ℓ≤L} 2^{γℓ} ≤ c₃ (2^γ/(2^γ−1)) K^{γ/α} ε^{−γ/α}` whenever
`2^{αL} ≤ K/ε`. -/
lemma tail_cost_bound {α γ c₃ K ε : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hc₃ : 0 < c₃) (hK : 0 < K)
    (hε : 0 < ε) (L : ℕ) (hL : (2 : ℝ) ^ (α * (L : ℝ)) ≤ K / ε) :
    c₃ * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ γ) ^ ℓ ≤
      c₃ * (2 ^ γ / (2 ^ γ - 1)) * (K ^ (γ / α) * ε ^ (-(γ / α))) := by
  have hg : 1 < (2 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
  have hg1 : 0 < (2 : ℝ) ^ γ - 1 := by linarith
  have h1 := geom_sum_le_of_one_lt hg L
  have h2 : ((2 : ℝ) ^ γ) ^ L = 2 ^ (γ * (L : ℝ)) := (two_rpow_mul_nat γ L).symm
  have h3 := two_rpow_L_le hα hγ.le hK hε hL
  have hpos : 0 ≤ c₃ * (2 ^ γ / (2 ^ γ - 1)) := by positivity
  calc c₃ * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ γ) ^ ℓ
      ≤ c₃ * (((2 : ℝ) ^ γ) ^ L * (2 ^ γ / (2 ^ γ - 1))) := by gcongr
    _ = c₃ * (2 ^ γ / (2 ^ γ - 1)) * 2 ^ (γ * (L : ℝ)) := by rw [h2]; ring
    _ ≤ c₃ * (2 ^ γ / (2 ^ γ - 1)) * (K ^ (γ / α) * ε ^ (-(γ / α))) :=
        mul_le_mul_of_nonneg_left h3 hpos

lemma eps_inv_sq_eq {ε : ℝ} (hε : 0 < ε) : ε⁻¹ ^ 2 = ε ^ (-2 : ℝ) := by
  rw [Real.rpow_neg hε.le, Real.rpow_two, inv_pow]

/-- `L + 1 ≤ K' |log ε|` whenever `2^{αL} ≤ K/ε` and `0 < ε < e⁻¹`, with
`K' = (|log K| + 1)/(α log 2) + 1` (the number of levels is `O(|log ε|)`; proof of Theorem 1,
Giles 2015, p. 7). -/
lemma level_add_one_le {α K ε : ℝ} (hα : 0 < α) (hK : 0 < K) (hε : 0 < ε)
    (hε1 : ε < Real.exp (-1)) {L : ℕ} (hL : (2 : ℝ) ^ (α * (L : ℝ)) ≤ K / ε) :
    (L : ℝ) + 1 ≤ ((|Real.log K| + 1) / (α * Real.log 2) + 1) * (-Real.log ε) := by
  have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
  have hαl : 0 < α * Real.log 2 := mul_pos hα (Real.log_pos one_lt_two)
  have h1 : α * (L : ℝ) * Real.log 2 ≤ Real.log K - Real.log ε := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos two_pos _) hL
    rwa [Real.log_rpow two_pos, Real.log_div hK.ne' hε.ne'] at h
  have h2 : (L : ℝ) * (α * Real.log 2) ≤ (|Real.log K| + 1) * (-Real.log ε) := by
    have h3 : Real.log K ≤ |Real.log K| * (-Real.log ε) :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) ht)
    have e1 : (L : ℝ) * (α * Real.log 2) = α * (L : ℝ) * Real.log 2 := by ring
    have e2 : (|Real.log K| + 1) * (-Real.log ε) = |Real.log K| * (-Real.log ε) + -Real.log ε := by
      ring
    rw [e1, e2]
    linarith
  have h4 : (L : ℝ) ≤ (|Real.log K| + 1) / (α * Real.log 2) * (-Real.log ε) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hαl]
    exact h2
  rw [add_mul, one_mul]
  linarith

/-- `complexityBound α β γ ε ≥ 1` for `α > 0` and `0 < ε < e⁻¹` (each of the three regimes of
Theorem 1, Giles 2015, p. 7, is at least `ε⁻²`). -/
lemma one_le_complexityBound {α β γ ε : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (hε1 : ε < Real.exp (-1)) : 1 ≤ complexityBound α β γ ε := by
  have hε1' : ε < 1 := eps_lt_one hε1
  have h2 : 1 ≤ ε ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1'.le (by norm_num)
  rcases lt_trichotomy γ β with hlt | heq | hgt
  · rw [complexityBound_of_lt hlt]
    exact h2
  · rw [complexityBound_of_eq heq]
    have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
    have hl : 1 ≤ Real.log ε ^ 2 := by nlinarith
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ ε ^ (-2 : ℝ) * Real.log ε ^ 2 := mul_le_mul h2 hl zero_le_one (by linarith)
  · rw [complexityBound_of_gt hgt]
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1'.le
    have : 0 ≤ (γ - β) / α := div_nonneg (by linarith) hα.le
    linarith

/-- **The cost bound of the three regimes, for any finest level with `2^{αL} ≤ K/ε`** (a step of
this formalisation's proof of Giles 2015, §2.1, Theorem 1; not stated in the paper).  Let
`α, γ, c₂, c₃, K > 0` and `α ≥ ½ min(β, γ)`.  There is `c₄ > 0` such that for every `0 < ε < e⁻¹`
and every `L` with `2^{αL} ≤ K/ε`, the cost of the rounded-up optimal allocation for
`V_ℓ = c₂ 2^{−βℓ}`, `C_ℓ = c₃ 2^{γℓ}` and the variance target `ε²/2`, as bounded by
`optimalN_cost` — `2ε⁻² c₂ c₃ (∑_{ℓ≤L} r^ℓ)² + c₃ ∑_{ℓ≤L} (2^γ)^ℓ` with `r = 2^{(γ−β)/2}` — is at
most `c₄ · complexityBound α β γ ε`.  The constant depends on `α, β, γ, c₂, c₃, K` only. -/
theorem cost_le_of_level {α β γ c₂ c₃ K : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hc₂ : 0 < c₂)
    (hc₃ : 0 < c₃) (hK : 0 < K) (hαβγ : min β γ / 2 ≤ α) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) → ∀ L : ℕ,
      (2 : ℝ) ^ (α * (L : ℝ)) ≤ K / ε →
      2 * ε⁻¹ ^ 2 * (c₂ * c₃) * (∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) ^ 2
          + c₃ * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ γ) ^ ℓ ≤ c₄ * complexityBound α β γ ε := by
  -- notation
  set r : ℝ := (2 : ℝ) ^ ((γ - β) / 2) with hr_def
  set g : ℝ := (2 : ℝ) ^ γ with hg_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos two_pos _
  have hg : 1 < g := Real.one_lt_rpow (by norm_num) hγ
  have hg1 : 0 < g - 1 := by linarith
  set K' : ℝ := (|Real.log K| + 1) / (α * Real.log 2) + 1
  -- the tail constant, common to all three cases
  set T : ℝ := c₃ * (g / (g - 1)) * K ^ (γ / α) with hT_def
  have hT : 0 < T := by rw [hT_def]; positivity
  rcases lt_trichotomy γ β with hlt | heq | hgt
  · -- ### Case β > γ : cost ≤ c₄ ε⁻²
    have hmin : min β γ = γ := min_eq_right hlt.le
    have hγα : γ / α ≤ 2 := by
      rw [hmin] at hαβγ
      rw [div_le_iff₀ hα]; linarith
    have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have h1r : 0 < 1 - r := by linarith
    refine ⟨2 * (c₂ * c₃) * (1 - r)⁻¹ ^ 2 + T, by positivity, ?_⟩
    intro ε hε hε1 L hL
    have hε1' : ε < 1 := eps_lt_one hε1
    have hA : (∑ ℓ ∈ range (L + 1), r ^ ℓ) ^ 2 ≤ (1 - r)⁻¹ ^ 2 := by
      have := geom_sum_le_of_lt_one hr0.le hr1 (L + 1)
      have h0 : 0 ≤ ∑ ℓ ∈ range (L + 1), r ^ ℓ := Finset.sum_nonneg fun _ _ => pow_nonneg hr0.le _
      gcongr
    have hB := tail_cost_bound hα hγ hc₃ hK hε L hL
    have hε2 : ε ^ (-(γ / α)) ≤ ε ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1'.le (by linarith)
    have hbound : complexityBound α β γ ε = ε ^ (-2 : ℝ) := by
      unfold complexityBound; simp [hlt]
    rw [hbound]
    have hKp : 0 ≤ K ^ (γ / α) := Real.rpow_nonneg hK.le _
    calc 2 * ε⁻¹ ^ 2 * (c₂ * c₃) * (∑ ℓ ∈ range (L + 1), r ^ ℓ) ^ 2
            + c₃ * ∑ ℓ ∈ range (L + 1), g ^ ℓ
        ≤ 2 * ε⁻¹ ^ 2 * (c₂ * c₃) * (1 - r)⁻¹ ^ 2
            + c₃ * (g / (g - 1)) * (K ^ (γ / α) * ε ^ (-(γ / α))) := by
          gcongr
      _ ≤ 2 * ε ^ (-2 : ℝ) * (c₂ * c₃) * (1 - r)⁻¹ ^ 2
            + c₃ * (g / (g - 1)) * (K ^ (γ / α) * ε ^ (-2 : ℝ)) := by
          rw [eps_inv_sq_eq hε]
          gcongr
      _ = (2 * (c₂ * c₃) * (1 - r)⁻¹ ^ 2 + T) * ε ^ (-2 : ℝ) := by
          rw [hT_def]; ring
  · -- ### Case β = γ : cost ≤ c₄ ε⁻² (log ε)²
    have hmin : min β γ = γ := by rw [heq, min_self]
    have hγα : γ / α ≤ 2 := by
      rw [hmin] at hαβγ
      rw [div_le_iff₀ hα]; linarith
    have hr1 : r = 1 := by
      rw [hr_def, heq, sub_self, zero_div, Real.rpow_zero]
    refine ⟨2 * (c₂ * c₃) * K' ^ 2 + T, by positivity, ?_⟩
    intro ε hε hε1 L hL
    have hL1 : (L : ℝ) + 1 ≤ K' * (-Real.log ε) := level_add_one_le hα hK hε hε1 hL
    have hε1' : ε < 1 := eps_lt_one hε1
    have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
    have hsum : ∑ ℓ ∈ range (L + 1), r ^ ℓ = (L : ℝ) + 1 := by
      rw [hr1]; simp
    have hA : (∑ ℓ ∈ range (L + 1), r ^ ℓ) ^ 2 ≤ (K' * (-Real.log ε)) ^ 2 := by
      rw [hsum]
      have h0 : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
      gcongr
    have hB := tail_cost_bound hα hγ hc₃ hK hε L hL
    have ht2 : 1 ≤ (Real.log ε) ^ 2 := by
      have : (-Real.log ε) ^ 2 = (Real.log ε) ^ 2 := by ring
      rw [← this]
      exact one_le_pow₀ ht
    have hε2 : ε ^ (-(γ / α)) ≤ ε ^ (-2 : ℝ) * (Real.log ε) ^ 2 := by
      calc ε ^ (-(γ / α)) ≤ ε ^ (-2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hε hε1'.le (by linarith)
        _ = ε ^ (-2 : ℝ) * 1 := by ring
        _ ≤ ε ^ (-2 : ℝ) * (Real.log ε) ^ 2 := by gcongr
    have hbound : complexityBound α β γ ε = ε ^ (-2 : ℝ) * (Real.log ε) ^ 2 := by
      unfold complexityBound; simp [heq]
    rw [hbound]
    have hKp : 0 ≤ K ^ (γ / α) := Real.rpow_nonneg hK.le _
    calc 2 * ε⁻¹ ^ 2 * (c₂ * c₃) * (∑ ℓ ∈ range (L + 1), r ^ ℓ) ^ 2
            + c₃ * ∑ ℓ ∈ range (L + 1), g ^ ℓ
        ≤ 2 * ε⁻¹ ^ 2 * (c₂ * c₃) * (K' * (-Real.log ε)) ^ 2
            + c₃ * (g / (g - 1)) * (K ^ (γ / α) * ε ^ (-(γ / α))) := by
          gcongr
      _ ≤ 2 * ε ^ (-2 : ℝ) * (c₂ * c₃) * (K' * (-Real.log ε)) ^ 2
            + c₃ * (g / (g - 1)) * (K ^ (γ / α) * (ε ^ (-2 : ℝ) * (Real.log ε) ^ 2)) := by
          rw [eps_inv_sq_eq hε]
          gcongr
      _ = (2 * (c₂ * c₃) * K' ^ 2 + T) * (ε ^ (-2 : ℝ) * (Real.log ε) ^ 2) := by
          rw [hT_def]; ring
  · -- ### Case β < γ : cost ≤ c₄ ε^{−2−(γ−β)/α}
    have hmin : min β γ = β := min_eq_left hgt.le
    have hβα : β / α ≤ 2 := by
      rw [hmin] at hαβγ
      rw [div_le_iff₀ hα]; linarith
    have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by linarith)
    have hr1' : 0 < r - 1 := by linarith
    have hγβ : 0 ≤ γ - β := by linarith
    refine ⟨2 * (c₂ * c₃) * (r / (r - 1)) ^ 2 * K ^ ((γ - β) / α) + T, by positivity, ?_⟩
    intro ε hε hε1 L hL
    have hε1' : ε < 1 := eps_lt_one hε1
    -- (∑ r^ℓ)² ≤ r^{2L} (r/(r−1))² and r^{2L} = 2^{(γ−β)L} ≤ K1^{(γ−β)/α} ε^{−(γ−β)/α}
    have hr2L : r ^ (2 * L) = (2 : ℝ) ^ ((γ - β) * (L : ℝ)) := by
      rw [hr_def, ← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      push_cast
      ring
    have hpow := two_rpow_L_le hα hγβ hK hε hL
    have hA : (∑ ℓ ∈ range (L + 1), r ^ ℓ) ^ 2 ≤
        (r / (r - 1)) ^ 2 * (K ^ ((γ - β) / α) * ε ^ (-((γ - β) / α))) := by
      have h0 : 0 ≤ ∑ ℓ ∈ range (L + 1), r ^ ℓ := Finset.sum_nonneg fun _ _ => pow_nonneg hr0.le _
      calc (∑ ℓ ∈ range (L + 1), r ^ ℓ) ^ 2 ≤ (r ^ L * (r / (r - 1))) ^ 2 := by
            gcongr
            exact geom_sum_le_of_one_lt hr1 L
        _ = (r / (r - 1)) ^ 2 * r ^ (2 * L) := by ring
        _ = (r / (r - 1)) ^ 2 * (2 : ℝ) ^ ((γ - β) * (L : ℝ)) := by rw [hr2L]
        _ ≤ (r / (r - 1)) ^ 2 * (K ^ ((γ - β) / α) * ε ^ (-((γ - β) / α))) := by
            gcongr
    have hB := tail_cost_bound hα hγ hc₃ hK hε L hL
    -- exponent bookkeeping
    have hexp : ε ^ (-2 : ℝ) * ε ^ (-((γ - β) / α)) = ε ^ (-2 - (γ - β) / α) := by
      rw [show (-2 : ℝ) - (γ - β) / α = -2 + -((γ - β) / α) by ring, Real.rpow_add hε]
    have hε2 : ε ^ (-(γ / α)) ≤ ε ^ (-2 - (γ - β) / α) := by
      apply Real.rpow_le_rpow_of_exponent_ge hε hε1'.le
      -- -2 - (γ-β)/α ≤ -(γ/α)  ⟺  β/α ≤ 2
      have : (γ - β) / α = γ / α - β / α := by ring
      rw [this]; linarith
    have hbound : complexityBound α β γ ε = ε ^ (-2 - (γ - β) / α) := by
      unfold complexityBound; simp [hgt.ne, not_lt.2 hgt.le]
    rw [hbound]
    have hKp : 0 ≤ K ^ (γ / α) := Real.rpow_nonneg hK.le _
    calc 2 * ε⁻¹ ^ 2 * (c₂ * c₃) * (∑ ℓ ∈ range (L + 1), r ^ ℓ) ^ 2
            + c₃ * ∑ ℓ ∈ range (L + 1), g ^ ℓ
        ≤ 2 * ε⁻¹ ^ 2 * (c₂ * c₃) *
            ((r / (r - 1)) ^ 2 * (K ^ ((γ - β) / α) * ε ^ (-((γ - β) / α))))
            + c₃ * (g / (g - 1)) * (K ^ (γ / α) * ε ^ (-(γ / α))) := by
          gcongr
      _ = 2 * (c₂ * c₃) * (r / (r - 1)) ^ 2 * K ^ ((γ - β) / α) *
            (ε ^ (-2 : ℝ) * ε ^ (-((γ - β) / α)))
            + c₃ * (g / (g - 1)) * K ^ (γ / α) * ε ^ (-(γ / α)) := by
          rw [eps_inv_sq_eq hε]; ring
      _ ≤ 2 * (c₂ * c₃) * (r / (r - 1)) ^ 2 * K ^ ((γ - β) / α) *
            ε ^ (-2 - (γ - β) / α)
            + c₃ * (g / (g - 1)) * K ^ (γ / α) * ε ^ (-2 - (γ - β) / α) := by
          rw [hexp]
          gcongr
      _ = (2 * (c₂ * c₃) * (r / (r - 1)) ^ 2 * K ^ ((γ - β) / α) + T) *
            ε ^ (-2 - (γ - β) / α) := by
          rw [hT_def]; ring

set_option linter.unusedVariables false in
/-- **Giles' Theorem 1 — deterministic core** (a step of this formalisation's proof of Giles 2015,
§2.1, Theorem 1; not stated in the paper).  Under the hypotheses of Theorem 1, with
`V_ℓ = c₂ 2^{−βℓ}` and `C_ℓ = c₃ 2^{γℓ}`, there is `c₄ > 0` such that for every `0 < ε < e⁻¹`
there are `L` and `N_ℓ ≥ 1` with `(bias bound)² + ∑ V_ℓ/N_ℓ < ε²` and
`∑ N_ℓ C_ℓ ≤ c₄ · complexityBound α β γ ε`.  The hypothesis `β > 0` is one of Giles'; the proof
does not use it (only `α ≥ ½ min(β,γ)` and `γ > 0` enter). -/
theorem mlmc_complexity_core {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ ≤ c₄ * complexityBound α β γ ε := by
  obtain ⟨c₄, hc₄, hcost⟩ := cost_le_of_level (β := β) hα hγ hc₂ hc₃ (K1_pos (α := α) hc₁) hαβγ
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hbias, hvar, hcost', hL, -⟩ :=
    exists_L_N (β := β) (γ := γ) hα hc₁ hc₂ hc₃ hε hε1
  exact ⟨L, N, hN, by have := pow_pos hε 2; linarith, hcost'.trans (hcost ε hε hε1 L hL)⟩

end MLMC
