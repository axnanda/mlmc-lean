import MlmcLean.MultiIndex
import MlmcLean.Complexity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat

/-!
# Lattice sums over the MIMC index sets `{ℓ ∈ ℕ^D : θ·ℓ ≤ L}`

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.4, Theorem 2
and the discussion on p. 15: the optimal summation region is "of the form `ℓ·n ≤ L` for a
particular choice of direction vector `n` with strictly positive components".  Giles notes that
"the proof of the theorem is significantly harder than for the MLMC theorem"; the extra work is
the lattice-point counting in this file.

For `θ_d > 0`, `δ_d ≥ 0` let `m = crit δ` be the number of directions with `δ_d = 0`.  Directions
with `δ_d > 0` contribute a convergent geometric factor, and each further direction with
`δ_d = 0` contributes one power of the level:

* `slab_bound` — `∑_{x ≤ θ·ℓ ≤ x+1} 2^{−δ·ℓ} ≤ K (1 + x)^{m−1}` (and the full sum is finite if
  `m = 0`);
* `tail_bound` — `∑_{θ·ℓ > L} 2^{−aθ·ℓ − δ·ℓ} ≤ K (1+L)^{m−1} 2^{−aL}` (the bias);
* `inner_bound` — `∑_{θ·ℓ ≤ L} 2^{cθ·ℓ − δ·ℓ} ≤ K (1+L)^{m−1} ∑_{j ≤ L} 2^{c(L−j)}` (the cost);
* `sum_box_two_rpow_le_prod` — `∑_ℓ 2^{g·ℓ} ≤ ∏_d (1 − 2^{g_d})⁻¹` for `g < 0`;
* `card_indexSet_le` — `#{θ·ℓ ≤ L} ≤ (1+L)^D ∏_d (1/θ_d + 1)`.

All sums are finite sums over boxes `{0, …, n−1}^D`, with bounds uniform in `n`.
-/

open Finset Real

namespace MLMC

variable {D : ℕ}

/-! ### Multi-indices -/

/-- The pairing `a·ℓ = ∑_d a_d ℓ_d` of a real vector with a multi-index. -/
noncomputable def dot (a : Fin D → ℝ) (ℓ : Fin D → ℕ) : ℝ := ∑ d, a d * (ℓ d : ℝ)

/-- The box `{0, …, n − 1}^D` of multi-indices. -/
def box (D n : ℕ) : Finset (Fin D → ℕ) := Fintype.piFinset fun _ => range n

/-- The number of directions `d` with `δ_d = 0`. -/
noncomputable def crit (δ : Fin D → ℝ) : ℕ := (univ.filter fun d => δ d = 0).card

lemma mem_box {n : ℕ} {ℓ : Fin D → ℕ} : ℓ ∈ box D n ↔ ∀ d, ℓ d < n := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_range]

lemma box_mono {n n' : ℕ} (h : n ≤ n') : box D n ⊆ box D n' := fun _ hℓ =>
  mem_box.2 fun d => lt_of_lt_of_le (mem_box.1 hℓ d) h

lemma dot_nonneg {a : Fin D → ℝ} (ha : ∀ d, 0 ≤ a d) (ℓ : Fin D → ℕ) : 0 ≤ dot a ℓ :=
  Finset.sum_nonneg fun d _ => mul_nonneg (ha d) (Nat.cast_nonneg _)

lemma dot_cons (a : Fin (D + 1) → ℝ) (k : ℕ) (ℓ : Fin D → ℕ) :
    dot a (Fin.cons k ℓ) = a 0 * k + dot (Fin.tail a) ℓ := by
  simp only [dot, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

lemma sum_box_succ (n : ℕ) (f : (Fin (D + 1) → ℕ) → ℝ) :
    ∑ ℓ ∈ box (D + 1) n, f ℓ = ∑ k ∈ range n, ∑ ℓ ∈ box D n, f (Fin.cons k ℓ) := by
  unfold box
  exact sum_piFinset_succ (fun _ => range n) f

lemma crit_succ (δ : Fin (D + 1) → ℝ) :
    crit δ = (if δ 0 = 0 then 1 else 0) + crit (Fin.tail δ) := by
  unfold crit
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  rfl

/-- Every finite set of multi-indices lies in a box. -/
lemma exists_subset_box (s : Finset (Fin D → ℕ)) : ∃ n, s ⊆ box D n := by
  refine ⟨s.sup (fun ℓ => univ.sup ℓ) + 1, fun ℓ hℓ => mem_box.2 fun d => ?_⟩
  have h1 : ℓ d ≤ univ.sup ℓ := Finset.le_sup (f := ℓ) (Finset.mem_univ d)
  have h2 : univ.sup ℓ ≤ s.sup (fun ℓ => univ.sup ℓ) :=
    Finset.le_sup (f := fun ℓ : Fin D → ℕ => univ.sup ℓ) hℓ
  omega

/-! ### One-dimensional counting -/

/-- At most `1/θ₀ + 1` multiples `θ₀ k` lie in an interval `[y, y + 1]`. -/
lemma card_filter_slab_le {θ₀ : ℝ} (hθ : 0 < θ₀) (y : ℝ) (n : ℕ) :
    (((range n).filter fun k : ℕ => y ≤ θ₀ * k ∧ θ₀ * k ≤ y + 1).card : ℝ) ≤ 1 / θ₀ + 1 := by
  set s := (range n).filter fun k : ℕ => y ≤ θ₀ * k ∧ θ₀ * k ≤ y + 1 with hs
  rcases s.eq_empty_or_nonempty with h | h
  · rw [h, Finset.card_empty, Nat.cast_zero]
    have := div_nonneg zero_le_one hθ.le
    linarith
  · have hk₀ := s.min'_mem h
    have hsub : s ⊆ Finset.Icc (s.min' h) (s.min' h + ⌊1 / θ₀⌋₊) := by
      intro k hk
      have hle : s.min' h ≤ k := s.min'_le k hk
      rw [Finset.mem_Icc]
      refine ⟨hle, ?_⟩
      have h1 := (Finset.mem_filter.1 hk).2.2
      have h2 := (Finset.mem_filter.1 hk₀).2.1
      have h3 : ((k - s.min' h : ℕ) : ℝ) ≤ 1 / θ₀ := by
        rw [Nat.cast_sub hle, le_div_iff₀ hθ]
        linarith
      have := Nat.le_floor h3
      omega
    calc (s.card : ℝ) ≤ (Finset.Icc (s.min' h) (s.min' h + ⌊1 / θ₀⌋₊)).card := by
          exact_mod_cast Finset.card_le_card hsub
      _ = ⌊1 / θ₀⌋₊ + 1 := by
          rw [Nat.card_Icc, show s.min' h + ⌊1 / θ₀⌋₊ + 1 - s.min' h = ⌊1 / θ₀⌋₊ + 1 by omega,
            Nat.cast_add, Nat.cast_one]
      _ ≤ 1 / θ₀ + 1 := by
          have := Nat.floor_le (div_nonneg zero_le_one hθ.le)
          linarith

/-- At most `max z 0 / θ₀ + 1` multiples `θ₀ k` (`k ∈ ℕ`) are `≤ z`. -/
lemma card_filter_mul_le {θ₀ : ℝ} (hθ : 0 < θ₀) (z : ℝ) (n : ℕ) :
    (((range n).filter fun k : ℕ => θ₀ * k ≤ z).card : ℝ) ≤ max z 0 / θ₀ + 1 := by
  have hz : 0 ≤ max z 0 / θ₀ := div_nonneg (le_max_right _ _) hθ.le
  have hsub : (range n).filter (fun k : ℕ => θ₀ * k ≤ z) ⊆ range (⌊max z 0 / θ₀⌋₊ + 1) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_range, Nat.lt_add_one_iff]
    apply Nat.le_floor
    rw [le_div_iff₀ hθ]
    have := le_max_left z 0
    linarith [hk.2]
  calc (((range n).filter fun k : ℕ => θ₀ * k ≤ z).card : ℝ)
      ≤ (range (⌊max z 0 / θ₀⌋₊ + 1)).card := by exact_mod_cast Finset.card_le_card hsub
    _ = ⌊max z 0 / θ₀⌋₊ + 1 := by rw [Finset.card_range, Nat.cast_add, Nat.cast_one]
    _ ≤ max z 0 / θ₀ + 1 := by linarith [Nat.floor_le hz]

/-! ### Polynomials against exponentials -/

/-- For `p ≥ 0` and `κ > 0` there is `K` with `(1 + x)^p ≤ K e^{κx}` for all `x ≥ 0`. -/
lemma one_add_rpow_le_exp {p κ : ℝ} (hp : 0 ≤ p) (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ p ≤ K * Real.exp (κ * x) := by
  rcases hp.eq_or_lt with h0 | hpos
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [← h0, Real.rpow_zero, one_mul]
    exact Real.one_le_exp (mul_nonneg hκ.le hx)
  · have hp0 : p ≠ 0 := hpos.ne'
    have hκp : 0 ≤ κ / p := (div_pos hκ hpos).le
    set M := max 1 (p / κ) with hM
    have hM1 : 1 ≤ M := le_max_left _ _
    have hMp : p / κ ≤ M := le_max_right _ _
    refine ⟨M ^ p, Real.rpow_pos_of_pos (by linarith) _, fun x hx => ?_⟩
    have hx1 : 0 ≤ 1 + κ / p * x := by have := mul_nonneg hκp hx; linarith
    have hMk : 1 ≤ M * (κ / p) := by
      have e : p / κ * (κ / p) = 1 := by
        rw [div_mul_div_comm, mul_comm κ p]
        exact div_self (mul_ne_zero hp0 hκ.ne')
      calc (1 : ℝ) = p / κ * (κ / p) := e.symm
        _ ≤ M * (κ / p) := mul_le_mul_of_nonneg_right hMp hκp
    have h1 : 1 + x ≤ M * (1 + κ / p * x) := by
      have hx' : x ≤ M * (κ / p) * x := le_mul_of_one_le_left hx hMk
      calc 1 + x ≤ M + M * (κ / p) * x := by linarith
        _ = M * (1 + κ / p * x) := by ring
    have h2 : (1 + κ / p * x) ^ p ≤ Real.exp (κ * x) := by
      have h3 : 1 + κ / p * x ≤ Real.exp (κ / p * x) := by
        linarith [Real.add_one_le_exp (κ / p * x)]
      calc (1 + κ / p * x) ^ p ≤ (Real.exp (κ / p * x)) ^ p :=
            Real.rpow_le_rpow hx1 h3 hp
        _ = Real.exp (κ * x) := by
            rw [← Real.exp_mul]
            congr 1
            field_simp
    calc (1 + x) ^ p ≤ (M * (1 + κ / p * x)) ^ p := Real.rpow_le_rpow (by linarith) h1 hp
      _ = M ^ p * (1 + κ / p * x) ^ p := Real.mul_rpow (by linarith) hx1
      _ ≤ M ^ p * Real.exp (κ * x) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by linarith) _)

/-- For `p ≥ 0` and `κ > 0`, `|log ε|^p ε^κ` is bounded on `0 < ε < 1`. -/
lemma neg_log_rpow_mul_rpow_le {p κ : ℝ} (hp : 0 ≤ p) (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → (-Real.log ε) ^ p * ε ^ κ ≤ K := by
  obtain ⟨K, hK, h⟩ := one_add_rpow_le_exp hp hκ
  refine ⟨K, hK, fun ε hε hε1 => ?_⟩
  have ht : 0 ≤ -Real.log ε := by linarith [Real.log_neg hε hε1]
  have h1 : (-Real.log ε) ^ p ≤ (1 + -Real.log ε) ^ p := Real.rpow_le_rpow ht (by linarith) hp
  have h2 := h (-Real.log ε) ht
  have h3 : ε ^ κ = Real.exp (-(κ * -Real.log ε)) := by
    rw [Real.rpow_def_of_pos hε]
    congr 1
    ring
  calc (-Real.log ε) ^ p * ε ^ κ
      ≤ (K * Real.exp (κ * -Real.log ε)) * Real.exp (-(κ * -Real.log ε)) := by
        rw [h3]
        exact mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
    _ = K := by
        rw [mul_assoc, ← Real.exp_add]
        simp

/-- For `p ≥ 0` and `κ > 0` there is `K` with `(1 + x)^p ≤ K 2^{κx}` for all `x ≥ 0`. -/
lemma one_add_rpow_le_two_rpow {p κ : ℝ} (hp : 0 ≤ p) (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ p ≤ K * (2 : ℝ) ^ (κ * x) := by
  obtain ⟨K, hK, h⟩ := one_add_rpow_le_exp hp (mul_pos (Real.log_pos one_lt_two) hκ)
  refine ⟨K, hK, fun x hx => ?_⟩
  rw [Real.rpow_def_of_pos two_pos, ← mul_assoc]
  exact h x hx

/-! ### Slab sums -/

/-- **Slab sums.**  Let `θ_d > 0`, `δ_d ≥ 0`, and let `m = crit δ` be the number of directions
with `δ_d = 0`.  Uniformly in the box size `n` and the level `x`,
`∑_{ℓ : x ≤ θ·ℓ ≤ x + 1} 2^{−δ·ℓ} ≤ K (1 + max x 0)^{m − 1}`; and if `m = 0`, the full sum
`∑_ℓ 2^{−δ·ℓ}` is at most `K`. -/
theorem slab_bound : ∀ {D : ℕ} (θ δ : Fin D → ℝ), (∀ d, 0 < θ d) → (∀ d, 0 ≤ δ d) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (x : ℝ),
      (crit δ = 0 → ∑ ℓ ∈ box D n, (2 : ℝ) ^ (-dot δ ℓ) ≤ K) ∧
      ∑ ℓ ∈ box D n, (if x ≤ dot θ ℓ ∧ dot θ ℓ ≤ x + 1 then (2 : ℝ) ^ (-dot δ ℓ) else 0) ≤
        K * (1 + max x 0) ^ (crit δ - 1)
  | 0, θ, δ, _, _ => by
    refine ⟨1, zero_le_one, fun n x => ?_⟩
    have hdot : ∀ (a : Fin 0 → ℝ) (ℓ : Fin 0 → ℕ), dot a ℓ = 0 := fun a ℓ => by simp [dot]
    have hcard : (box 0 n).card = 1 := by simp [box]
    have htot : ∑ ℓ ∈ box 0 n, (2 : ℝ) ^ (-dot δ ℓ) = 1 := by
      have h1 : ∀ ℓ ∈ box 0 n, (2 : ℝ) ^ (-dot δ ℓ) = 1 := fun ℓ _ => by
        rw [hdot, neg_zero, Real.rpow_zero]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, hcard, one_smul]
    have hcrit : crit δ = 0 := by simp [crit]
    refine ⟨fun _ => htot.le, ?_⟩
    rw [hcrit, Nat.zero_sub, pow_zero, mul_one]
    refine le_trans (Finset.sum_le_sum fun ℓ _ => ?_) htot.le
    split_ifs
    · exact le_rfl
    · exact (Real.rpow_pos_of_pos two_pos _).le
  | D + 1, θ, δ, hθ, hδ => by
    obtain ⟨K', hK', hIH⟩ := slab_bound (Fin.tail θ) (Fin.tail δ) (fun d => hθ d.succ)
      (fun d => hδ d.succ)
    have hθ0 : 0 < θ 0 := hθ 0
    have hdθ : ∀ ℓ : Fin D → ℕ, 0 ≤ dot (Fin.tail θ) ℓ := dot_nonneg fun d => (hθ d.succ).le
    -- splitting off the first coordinate
    have hsplit_tot : ∀ n, ∑ ℓ ∈ box (D + 1) n, (2 : ℝ) ^ (-dot δ ℓ) =
        ∑ k ∈ range n, ((2 : ℝ) ^ (-δ 0)) ^ k *
          ∑ ℓ ∈ box D n, (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ) := by
      intro n
      rw [sum_box_succ]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [dot_cons, neg_add, Real.rpow_add two_pos, ← two_rpow_mul_nat, neg_mul]
    have hsplit_slab : ∀ (n : ℕ) (x : ℝ), ∑ ℓ ∈ box (D + 1) n,
        (if x ≤ dot θ ℓ ∧ dot θ ℓ ≤ x + 1 then (2 : ℝ) ^ (-dot δ ℓ) else 0) =
        ∑ k ∈ range n, ((2 : ℝ) ^ (-δ 0)) ^ k * ∑ ℓ ∈ box D n,
          (if x - θ 0 * k ≤ dot (Fin.tail θ) ℓ ∧ dot (Fin.tail θ) ℓ ≤ x - θ 0 * k + 1 then
            (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ) else 0) := by
      intro n x
      rw [sum_box_succ]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [dot_cons, dot_cons]
      by_cases h : x ≤ θ 0 * k + dot (Fin.tail θ) ℓ ∧ θ 0 * k + dot (Fin.tail θ) ℓ ≤ x + 1
      · have h' : x - θ 0 * k ≤ dot (Fin.tail θ) ℓ ∧ dot (Fin.tail θ) ℓ ≤ x - θ 0 * k + 1 :=
          ⟨by linarith [h.1], by linarith [h.2]⟩
        rw [if_pos h, if_pos h', neg_add, Real.rpow_add two_pos, ← two_rpow_mul_nat, neg_mul]
      · have h' : ¬(x - θ 0 * k ≤ dot (Fin.tail θ) ℓ ∧
            dot (Fin.tail θ) ℓ ≤ x - θ 0 * k + 1) :=
          fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩
        rw [if_neg h, if_neg h', mul_zero]
    by_cases hδ0 : δ 0 = 0
    · -- a critical direction: the weight does not depend on the first coordinate
      have hcrit : crit δ = crit (Fin.tail δ) + 1 := by
        rw [crit_succ, if_pos hδ0, add_comm]
      have hq : (2 : ℝ) ^ (-δ 0) = 1 := by rw [hδ0, neg_zero, Real.rpow_zero]
      have hθinv : 0 ≤ 1 / θ 0 + 1 := by
        have := div_nonneg zero_le_one hθ0.le
        linarith
      refine ⟨K' * (1 / θ 0 + 1), mul_nonneg hK' hθinv, fun n x =>
        ⟨fun h => absurd (hcrit.symm.trans h) (Nat.add_one_ne_zero _), ?_⟩⟩
      rw [hsplit_slab, hcrit, Nat.add_sub_cancel]
      simp only [hq, one_pow, one_mul]
      by_cases hm : crit (Fin.tail δ) = 0
      · -- no further critical direction: count the admissible first coordinates
        rw [hm, pow_zero, mul_one, Finset.sum_comm]
        have hcount : ∀ ℓ : Fin D → ℕ, ∑ k ∈ range n,
            (if x - θ 0 * k ≤ dot (Fin.tail θ) ℓ ∧ dot (Fin.tail θ) ℓ ≤ x - θ 0 * k + 1 then
              (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ) else 0) ≤
            (1 / θ 0 + 1) * (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ) := by
          intro ℓ
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos two_pos _).le
          refine le_trans ?_ (card_filter_slab_le hθ0 (x - dot (Fin.tail θ) ℓ) n)
          exact_mod_cast Finset.card_le_card fun k hk => by
            simp only [Finset.mem_filter] at hk ⊢
            exact ⟨hk.1, by linarith [hk.2.1], by linarith [hk.2.2]⟩
        calc ∑ ℓ ∈ box D n, ∑ k ∈ range n,
              (if x - θ 0 * k ≤ dot (Fin.tail θ) ℓ ∧ dot (Fin.tail θ) ℓ ≤ x - θ 0 * k + 1 then
                (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ) else 0)
            ≤ ∑ ℓ ∈ box D n, (1 / θ 0 + 1) * (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ) :=
              Finset.sum_le_sum fun ℓ _ => hcount ℓ
          _ = (1 / θ 0 + 1) * ∑ ℓ ∈ box D n, (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ) := by
              rw [Finset.mul_sum]
          _ ≤ (1 / θ 0 + 1) * K' :=
              mul_le_mul_of_nonneg_left ((hIH n 0).1 hm) hθinv
          _ = K' * (1 / θ 0 + 1) := by ring
      · -- further critical directions: each admissible first coordinate gives a slab
        have hpt : ∀ k : ℕ, ∑ ℓ ∈ box D n,
            (if x - θ 0 * k ≤ dot (Fin.tail θ) ℓ ∧ dot (Fin.tail θ) ℓ ≤ x - θ 0 * k + 1 then
              (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ) else 0) ≤
            if θ 0 * k ≤ x + 1 then K' * (1 + max x 0) ^ (crit (Fin.tail δ) - 1) else 0 := by
          intro k
          split_ifs with hk
          · refine ((hIH n (x - θ 0 * k)).2).trans ?_
            apply mul_le_mul_of_nonneg_left _ hK'
            apply pow_le_pow_left₀ (by linarith [le_max_right (x - θ 0 * k) 0])
            have hk0 : (0 : ℝ) ≤ θ 0 * k := mul_nonneg hθ0.le (Nat.cast_nonneg k)
            have : max (x - θ 0 * k) 0 ≤ max x 0 := max_le_max (by linarith) le_rfl
            linarith
          · apply le_of_eq
            apply Finset.sum_eq_zero
            intro ℓ _
            have hne : ¬(x - θ 0 * k ≤ dot (Fin.tail θ) ℓ ∧
                dot (Fin.tail θ) ℓ ≤ x - θ 0 * k + 1) := by
              rintro ⟨-, h2⟩
              have := hdθ ℓ
              exact hk (by linarith)
            rw [if_neg hne]
        have hpow : (1 + max x 0) ^ crit (Fin.tail δ) =
            (1 + max x 0) ^ (crit (Fin.tail δ) - 1) * (1 + max x 0) := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm)]
        have hM : 0 ≤ max x 0 := le_max_right x 0
        calc ∑ k ∈ range n, ∑ ℓ ∈ box D n,
              (if x - θ 0 * k ≤ dot (Fin.tail θ) ℓ ∧ dot (Fin.tail θ) ℓ ≤ x - θ 0 * k + 1 then
                (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ) else 0)
            ≤ ∑ k ∈ range n,
                (if θ 0 * k ≤ x + 1 then K' * (1 + max x 0) ^ (crit (Fin.tail δ) - 1) else 0) :=
              Finset.sum_le_sum fun k _ => hpt k
          _ = (((range n).filter fun k : ℕ => θ 0 * k ≤ x + 1).card : ℝ) *
                (K' * (1 + max x 0) ^ (crit (Fin.tail δ) - 1)) := by
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((1 + max x 0) * (1 / θ 0 + 1)) *
                (K' * (1 + max x 0) ^ (crit (Fin.tail δ) - 1)) := by
              apply mul_le_mul_of_nonneg_right _ (mul_nonneg hK' (pow_nonneg (by linarith) _))
              refine (card_filter_mul_le hθ0 (x + 1) n).trans ?_
              have h1 : max (x + 1) 0 ≤ 1 + max x 0 :=
                max_le (by linarith [le_max_left x 0]) (by linarith)
              have h2 : max (x + 1) 0 / θ 0 ≤ (1 + max x 0) / θ 0 :=
                div_le_div_of_nonneg_right h1 hθ0.le
              have h3 : (1 + max x 0) * (1 / θ 0 + 1) = (1 + max x 0) / θ 0 + (1 + max x 0) := by
                ring
              rw [h3]
              linarith
          _ = K' * (1 / θ 0 + 1) * (1 + max x 0) ^ crit (Fin.tail δ) := by
              rw [hpow]
              ring
    · -- a non-critical direction: a convergent geometric factor
      have hδ0' : 0 < δ 0 := lt_of_le_of_ne (hδ 0) (Ne.symm hδ0)
      have hcrit : crit δ = crit (Fin.tail δ) := by rw [crit_succ, if_neg hδ0, zero_add]
      have hq0 : 0 ≤ (2 : ℝ) ^ (-δ 0) := (Real.rpow_pos_of_pos two_pos _).le
      have hq1 : (2 : ℝ) ^ (-δ 0) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
      have h1q : 0 < 1 - (2 : ℝ) ^ (-δ 0) := by linarith
      have hgeom : ∀ n, ∑ k ∈ range n, ((2 : ℝ) ^ (-δ 0)) ^ k ≤ (1 - (2 : ℝ) ^ (-δ 0))⁻¹ :=
        geom_sum_le_of_lt_one hq0 hq1
      refine ⟨K' * (1 - (2 : ℝ) ^ (-δ 0))⁻¹, mul_nonneg hK' (inv_nonneg.2 h1q.le),
        fun n x => ⟨fun h => ?_, ?_⟩⟩
      · rw [hcrit] at h
        rw [hsplit_tot]
        calc ∑ k ∈ range n, ((2 : ℝ) ^ (-δ 0)) ^ k *
              ∑ ℓ ∈ box D n, (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ)
            ≤ ∑ k ∈ range n, ((2 : ℝ) ^ (-δ 0)) ^ k * K' :=
              Finset.sum_le_sum fun k _ =>
                mul_le_mul_of_nonneg_left ((hIH n 0).1 h) (pow_nonneg hq0 k)
          _ = K' * ∑ k ∈ range n, ((2 : ℝ) ^ (-δ 0)) ^ k := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun k _ => by ring
          _ ≤ K' * (1 - (2 : ℝ) ^ (-δ 0))⁻¹ := mul_le_mul_of_nonneg_left (hgeom n) hK'
      · rw [hsplit_slab, hcrit]
        have hB : 0 ≤ K' * (1 + max x 0) ^ (crit (Fin.tail δ) - 1) :=
          mul_nonneg hK' (pow_nonneg (by linarith [le_max_right x 0]) _)
        calc ∑ k ∈ range n, ((2 : ℝ) ^ (-δ 0)) ^ k * ∑ ℓ ∈ box D n,
              (if x - θ 0 * k ≤ dot (Fin.tail θ) ℓ ∧ dot (Fin.tail θ) ℓ ≤ x - θ 0 * k + 1 then
                (2 : ℝ) ^ (-dot (Fin.tail δ) ℓ) else 0)
            ≤ ∑ k ∈ range n, ((2 : ℝ) ^ (-δ 0)) ^ k *
                (K' * (1 + max x 0) ^ (crit (Fin.tail δ) - 1)) := by
              refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 k)
              refine ((hIH n (x - θ 0 * k)).2).trans ?_
              apply mul_le_mul_of_nonneg_left _ hK'
              apply pow_le_pow_left₀ (by linarith [le_max_right (x - θ 0 * k) 0])
              have hk0 : (0 : ℝ) ≤ θ 0 * k := mul_nonneg hθ0.le (Nat.cast_nonneg k)
              have : max (x - θ 0 * k) 0 ≤ max x 0 := max_le_max (by linarith) le_rfl
              linarith
          _ = (K' * (1 + max x 0) ^ (crit (Fin.tail δ) - 1)) *
                ∑ k ∈ range n, ((2 : ℝ) ^ (-δ 0)) ^ k := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun k _ => by ring
          _ ≤ (K' * (1 + max x 0) ^ (crit (Fin.tail δ) - 1)) * (1 - (2 : ℝ) ^ (-δ 0))⁻¹ :=
              mul_le_mul_of_nonneg_left (hgeom n) hB
          _ = K' * (1 - (2 : ℝ) ^ (-δ 0))⁻¹ * (1 + max x 0) ^ (crit (Fin.tail δ) - 1) := by ring

/-! ### Tail and inner sums -/

/-- **Tail sums** (the MIMC bias).  With `θ, δ, m` as in `slab_bound` and `a > 0`, uniformly in
the box size `n` and in `L ≥ 0`: `∑_{θ·ℓ > L} 2^{−aθ·ℓ − δ·ℓ} ≤ K (1 + L)^{m−1} 2^{−aL}`. -/
theorem tail_bound {θ δ : Fin D → ℝ} (hθ : ∀ d, 0 < θ d) (hδ : ∀ d, 0 ≤ δ d) {a : ℝ}
    (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (L : ℝ), 0 ≤ L →
      ∑ ℓ ∈ box D n, (if L < dot θ ℓ then (2 : ℝ) ^ (-(a * dot θ ℓ) - dot δ ℓ) else 0) ≤
        K * (1 + L) ^ (crit δ - 1) * (2 : ℝ) ^ (-(a * L)) := by
  obtain ⟨Ks, hKs, hslab⟩ := slab_bound θ δ hθ hδ
  -- `∑_j (1+j)^{m−1} 2^{−aj}` is bounded uniformly over finite sets of `j`
  obtain ⟨K_A, hK_A, hA⟩ := one_add_rpow_le_two_rpow
    (Nat.cast_nonneg (crit δ - 1) : (0 : ℝ) ≤ ((crit δ - 1 : ℕ) : ℝ)) (half_pos ha)
  have hq0' : 0 ≤ (2 : ℝ) ^ (-(a / 2)) := (Real.rpow_pos_of_pos two_pos _).le
  have hq1' : (2 : ℝ) ^ (-(a / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set G : ℝ := K_A * (1 - (2 : ℝ) ^ (-(a / 2)))⁻¹ with hG
  have hG0 : 0 ≤ G := mul_nonneg hK_A.le (inv_nonneg.2 (by linarith))
  have hgeom : ∀ T : Finset ℕ,
      ∑ j ∈ T, ((j : ℝ) + 1) ^ (crit δ - 1) * ((2 : ℝ) ^ (-a)) ^ j ≤ G := by
    intro T
    have hpt : ∀ j : ℕ, ((j : ℝ) + 1) ^ (crit δ - 1) * ((2 : ℝ) ^ (-a)) ^ j ≤
        K_A * ((2 : ℝ) ^ (-(a / 2))) ^ j := by
      intro j
      have h1 : ((j : ℝ) + 1) ^ (crit δ - 1) ≤ K_A * (2 : ℝ) ^ (a / 2 * j) := by
        rw [add_comm, ← Real.rpow_natCast]
        exact hA j (Nat.cast_nonneg j)
      have h2 : (2 : ℝ) ^ (a / 2 * j) * ((2 : ℝ) ^ (-a)) ^ j = ((2 : ℝ) ^ (-(a / 2))) ^ j := by
        rw [← two_rpow_mul_nat, ← two_rpow_mul_nat, ← Real.rpow_add two_pos]
        congr 1
        ring
      calc ((j : ℝ) + 1) ^ (crit δ - 1) * ((2 : ℝ) ^ (-a)) ^ j
          ≤ K_A * (2 : ℝ) ^ (a / 2 * j) * ((2 : ℝ) ^ (-a)) ^ j :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg (Real.rpow_pos_of_pos two_pos _).le _)
        _ = K_A * ((2 : ℝ) ^ (-(a / 2))) ^ j := by rw [mul_assoc, h2]
    calc ∑ j ∈ T, ((j : ℝ) + 1) ^ (crit δ - 1) * ((2 : ℝ) ^ (-a)) ^ j
        ≤ ∑ j ∈ T, K_A * ((2 : ℝ) ^ (-(a / 2))) ^ j := Finset.sum_le_sum fun j _ => hpt j
      _ ≤ ∑ j ∈ range (T.sup id + 1), K_A * ((2 : ℝ) ^ (-(a / 2))) ^ j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            rw [Finset.mem_range, Nat.lt_add_one_iff]
            exact Finset.le_sup (f := id) hj
          · intro j _ _
            exact mul_nonneg hK_A.le (pow_nonneg hq0' _)
      _ = K_A * ∑ j ∈ range (T.sup id + 1), ((2 : ℝ) ^ (-(a / 2))) ^ j := by
          rw [Finset.mul_sum]
      _ ≤ G := mul_le_mul_of_nonneg_left (geom_sum_le_of_lt_one hq0' hq1' _) hK_A.le
  refine ⟨Ks * G, mul_nonneg hKs hG0, fun n L hL => ?_⟩
  -- each fibre `{⌊θ·ℓ − L⌋₊ = j}` of the tail lies in the slab `L + j ≤ θ·ℓ ≤ L + j + 1`
  have hfib : ∀ j : ℕ, ∑ ℓ ∈ (box D n).filter (fun ℓ => ⌊dot θ ℓ - L⌋₊ = j),
      (if L < dot θ ℓ then (2 : ℝ) ^ (-(a * dot θ ℓ) - dot δ ℓ) else 0) ≤
      (2 : ℝ) ^ (-(a * L)) * (Ks * (1 + L) ^ (crit δ - 1)) *
        (((j : ℝ) + 1) ^ (crit δ - 1) * ((2 : ℝ) ^ (-a)) ^ j) := by
    intro j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    calc ∑ ℓ ∈ (box D n).filter (fun ℓ => ⌊dot θ ℓ - L⌋₊ = j),
          (if L < dot θ ℓ then (2 : ℝ) ^ (-(a * dot θ ℓ) - dot δ ℓ) else 0)
        ≤ ∑ ℓ ∈ box D n, (2 : ℝ) ^ (-(a * (L + j))) *
            (if L + j ≤ dot θ ℓ ∧ dot θ ℓ ≤ L + j + 1 then (2 : ℝ) ^ (-dot δ ℓ) else 0) := by
          rw [Finset.sum_filter]
          refine Finset.sum_le_sum fun ℓ _ => ?_
          have hR : 0 ≤ (2 : ℝ) ^ (-(a * (L + j))) *
              (if L + j ≤ dot θ ℓ ∧ dot θ ℓ ≤ L + j + 1 then (2 : ℝ) ^ (-dot δ ℓ) else 0) := by
            apply mul_nonneg (Real.rpow_pos_of_pos two_pos _).le
            split_ifs
            · exact (Real.rpow_pos_of_pos two_pos _).le
            · exact le_rfl
          by_cases hj : ⌊dot θ ℓ - L⌋₊ = j
          · rw [if_pos hj]
            by_cases hL : L < dot θ ℓ
            · have hu : 0 ≤ dot θ ℓ - L := by linarith
              have h1 : (j : ℝ) ≤ dot θ ℓ - L := by rw [← hj]; exact Nat.floor_le hu
              have h2 : dot θ ℓ - L < j + 1 := by rw [← hj]; exact Nat.lt_floor_add_one _
              have hc : L + j ≤ dot θ ℓ ∧ dot θ ℓ ≤ L + j + 1 := ⟨by linarith, by linarith⟩
              rw [if_pos hL, if_pos hc, sub_eq_add_neg, Real.rpow_add two_pos]
              have hexp : -(a * dot θ ℓ) ≤ -(a * (L + j)) := by
                have := mul_le_mul_of_nonneg_left hc.1 ha.le
                linarith
              exact mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_exponent_le one_le_two hexp)
                (Real.rpow_pos_of_pos two_pos _).le
            · rw [if_neg hL]
              exact hR
          · rw [if_neg hj]
            exact hR
      _ = (2 : ℝ) ^ (-(a * (L + j))) * ∑ ℓ ∈ box D n,
            (if L + j ≤ dot θ ℓ ∧ dot θ ℓ ≤ L + j + 1 then (2 : ℝ) ^ (-dot δ ℓ) else 0) := by
          rw [Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ (-(a * (L + j))) * (Ks * (1 + max (L + j) 0) ^ (crit δ - 1)) :=
          mul_le_mul_of_nonneg_left (hslab n (L + j)).2 (Real.rpow_pos_of_pos two_pos _).le
      _ ≤ ((2 : ℝ) ^ (-(a * L)) * ((2 : ℝ) ^ (-a)) ^ j) *
            (Ks * ((1 + L) ^ (crit δ - 1) * ((j : ℝ) + 1) ^ (crit δ - 1))) := by
          have e1 : (2 : ℝ) ^ (-(a * (L + j))) = (2 : ℝ) ^ (-(a * L)) * ((2 : ℝ) ^ (-a)) ^ j := by
            rw [← two_rpow_mul_nat, ← Real.rpow_add two_pos]
            congr 1
            ring
          have e2 : max (L + j) 0 = L + j := max_eq_left (by linarith)
          have e3 : (1 + (L + j)) ^ (crit δ - 1) ≤
              (1 + L) ^ (crit δ - 1) * ((j : ℝ) + 1) ^ (crit δ - 1) := by
            rw [← mul_pow]
            apply pow_le_pow_left₀ (by linarith)
            nlinarith
          rw [e1, e2]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left e3 hKs
      _ = (2 : ℝ) ^ (-(a * L)) * (Ks * (1 + L) ^ (crit δ - 1)) *
            (((j : ℝ) + 1) ^ (crit δ - 1) * ((2 : ℝ) ^ (-a)) ^ j) := by ring
  calc ∑ ℓ ∈ box D n, (if L < dot θ ℓ then (2 : ℝ) ^ (-(a * dot θ ℓ) - dot δ ℓ) else 0)
      = ∑ j ∈ (box D n).image (fun ℓ => ⌊dot θ ℓ - L⌋₊),
          ∑ ℓ ∈ (box D n).filter (fun ℓ => ⌊dot θ ℓ - L⌋₊ = j),
            (if L < dot θ ℓ then (2 : ℝ) ^ (-(a * dot θ ℓ) - dot δ ℓ) else 0) :=
        (Finset.sum_fiberwise_of_maps_to (g := fun ℓ => ⌊dot θ ℓ - L⌋₊)
          (fun ℓ hℓ => Finset.mem_image_of_mem (fun ℓ => ⌊dot θ ℓ - L⌋₊) hℓ) _).symm
    _ ≤ ∑ j ∈ (box D n).image (fun ℓ => ⌊dot θ ℓ - L⌋₊),
          (2 : ℝ) ^ (-(a * L)) * (Ks * (1 + L) ^ (crit δ - 1)) *
            (((j : ℝ) + 1) ^ (crit δ - 1) * ((2 : ℝ) ^ (-a)) ^ j) :=
        Finset.sum_le_sum fun j _ => hfib j
    _ = (2 : ℝ) ^ (-(a * L)) * (Ks * (1 + L) ^ (crit δ - 1)) *
          ∑ j ∈ (box D n).image (fun ℓ => ⌊dot θ ℓ - L⌋₊),
            ((j : ℝ) + 1) ^ (crit δ - 1) * ((2 : ℝ) ^ (-a)) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (-(a * L)) * (Ks * (1 + L) ^ (crit δ - 1)) * G := by
        exact mul_le_mul_of_nonneg_left (hgeom _) (mul_nonneg (Real.rpow_pos_of_pos two_pos _).le
          (mul_nonneg hKs (pow_nonneg (by linarith) _)))
    _ = Ks * G * (1 + L) ^ (crit δ - 1) * (2 : ℝ) ^ (-(a * L)) := by ring

/-- **Inner sums** (the MIMC cost).  With `θ, δ, m` as in `slab_bound` and `c ≥ 0`, uniformly in
the box size `n` and in `L ≥ 0`:
`∑_{θ·ℓ ≤ L} 2^{cθ·ℓ − δ·ℓ} ≤ K (1 + L)^{m−1} ∑_{j=0}^{⌊L⌋} 2^{c(L − j)}`. -/
theorem inner_bound {θ δ : Fin D → ℝ} (hθ : ∀ d, 0 < θ d) (hδ : ∀ d, 0 ≤ δ d) {c : ℝ}
    (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (L : ℝ), 0 ≤ L →
      ∑ ℓ ∈ box D n, (if dot θ ℓ ≤ L then (2 : ℝ) ^ (c * dot θ ℓ - dot δ ℓ) else 0) ≤
        K * (1 + L) ^ (crit δ - 1) * ∑ j ∈ range (⌊L⌋₊ + 1), (2 : ℝ) ^ (c * (L - j)) := by
  obtain ⟨Ks, hKs, hslab⟩ := slab_bound θ δ hθ hδ
  refine ⟨Ks, hKs, fun n L hL => ?_⟩
  have hg : ∀ ℓ ∈ box D n, ⌊L - dot θ ℓ⌋₊ ∈ range (⌊L⌋₊ + 1) := by
    intro ℓ _
    rw [Finset.mem_range, Nat.lt_add_one_iff]
    exact Nat.floor_mono (by linarith [dot_nonneg (fun d => (hθ d).le) ℓ])
  -- each fibre `{⌊L − θ·ℓ⌋₊ = j}` lies in the slab `L − j − 1 ≤ θ·ℓ ≤ L − j`
  have hfib : ∀ j : ℕ, ∑ ℓ ∈ (box D n).filter (fun ℓ => ⌊L - dot θ ℓ⌋₊ = j),
      (if dot θ ℓ ≤ L then (2 : ℝ) ^ (c * dot θ ℓ - dot δ ℓ) else 0) ≤
      (2 : ℝ) ^ (c * (L - j)) * (Ks * (1 + L) ^ (crit δ - 1)) := by
    intro j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    calc ∑ ℓ ∈ (box D n).filter (fun ℓ => ⌊L - dot θ ℓ⌋₊ = j),
          (if dot θ ℓ ≤ L then (2 : ℝ) ^ (c * dot θ ℓ - dot δ ℓ) else 0)
        ≤ ∑ ℓ ∈ box D n, (2 : ℝ) ^ (c * (L - j)) *
            (if L - j - 1 ≤ dot θ ℓ ∧ dot θ ℓ ≤ L - j - 1 + 1 then (2 : ℝ) ^ (-dot δ ℓ)
              else 0) := by
          rw [Finset.sum_filter]
          refine Finset.sum_le_sum fun ℓ _ => ?_
          have hR : 0 ≤ (2 : ℝ) ^ (c * (L - j)) *
              (if L - j - 1 ≤ dot θ ℓ ∧ dot θ ℓ ≤ L - j - 1 + 1 then (2 : ℝ) ^ (-dot δ ℓ)
                else 0) := by
            apply mul_nonneg (Real.rpow_pos_of_pos two_pos _).le
            split_ifs
            · exact (Real.rpow_pos_of_pos two_pos _).le
            · exact le_rfl
          by_cases hj : ⌊L - dot θ ℓ⌋₊ = j
          · rw [if_pos hj]
            by_cases hL : dot θ ℓ ≤ L
            · have hu : 0 ≤ L - dot θ ℓ := by linarith
              have h1 : (j : ℝ) ≤ L - dot θ ℓ := by rw [← hj]; exact Nat.floor_le hu
              have h2 : L - dot θ ℓ < j + 1 := by rw [← hj]; exact Nat.lt_floor_add_one _
              have hc' : L - j - 1 ≤ dot θ ℓ ∧ dot θ ℓ ≤ L - j - 1 + 1 :=
                ⟨by linarith, by linarith⟩
              rw [if_pos hL, if_pos hc', sub_eq_add_neg, Real.rpow_add two_pos]
              have hexp : c * dot θ ℓ ≤ c * (L - j) := mul_le_mul_of_nonneg_left (by linarith) hc
              exact mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_exponent_le one_le_two hexp)
                (Real.rpow_pos_of_pos two_pos _).le
            · rw [if_neg hL]
              exact hR
          · rw [if_neg hj]
            exact hR
      _ = (2 : ℝ) ^ (c * (L - j)) * ∑ ℓ ∈ box D n,
            (if L - j - 1 ≤ dot θ ℓ ∧ dot θ ℓ ≤ L - j - 1 + 1 then (2 : ℝ) ^ (-dot δ ℓ)
              else 0) := by
          rw [Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ (c * (L - j)) * (Ks * (1 + max (L - j - 1) 0) ^ (crit δ - 1)) :=
          mul_le_mul_of_nonneg_left (hslab n (L - j - 1)).2 (Real.rpow_pos_of_pos two_pos _).le
      _ ≤ (2 : ℝ) ^ (c * (L - j)) * (Ks * (1 + L) ^ (crit δ - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos two_pos _).le
          apply mul_le_mul_of_nonneg_left _ hKs
          apply pow_le_pow_left₀ (by linarith [le_max_right (L - j - 1) 0])
          have : max (L - j - 1) 0 ≤ L := max_le (by linarith) hL
          linarith
  calc ∑ ℓ ∈ box D n, (if dot θ ℓ ≤ L then (2 : ℝ) ^ (c * dot θ ℓ - dot δ ℓ) else 0)
      = ∑ j ∈ range (⌊L⌋₊ + 1), ∑ ℓ ∈ (box D n).filter (fun ℓ => ⌊L - dot θ ℓ⌋₊ = j),
          (if dot θ ℓ ≤ L then (2 : ℝ) ^ (c * dot θ ℓ - dot δ ℓ) else 0) :=
        (Finset.sum_fiberwise_of_maps_to (g := fun ℓ => ⌊L - dot θ ℓ⌋₊) hg _).symm
    _ ≤ ∑ j ∈ range (⌊L⌋₊ + 1), (2 : ℝ) ^ (c * (L - j)) * (Ks * (1 + L) ^ (crit δ - 1)) :=
        Finset.sum_le_sum fun j _ => hfib j
    _ = Ks * (1 + L) ^ (crit δ - 1) * ∑ j ∈ range (⌊L⌋₊ + 1), (2 : ℝ) ^ (c * (L - j)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- For `c > 0`: `∑_{j=0}^{⌊L⌋} 2^{c(L−j)} ≤ 2^{cL} / (1 − 2^{−c})`. -/
lemma sum_two_rpow_sub_le {c : ℝ} (hc : 0 < c) (L : ℝ) :
    ∑ j ∈ range (⌊L⌋₊ + 1), (2 : ℝ) ^ (c * (L - j)) ≤
      (2 : ℝ) ^ (c * L) * (1 - (2 : ℝ) ^ (-c))⁻¹ := by
  have hq0 : 0 ≤ (2 : ℝ) ^ (-c) := (Real.rpow_pos_of_pos two_pos _).le
  have hq1 : (2 : ℝ) ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have h : ∀ j : ℕ, (2 : ℝ) ^ (c * (L - j)) = (2 : ℝ) ^ (c * L) * ((2 : ℝ) ^ (-c)) ^ j := by
    intro j
    rw [← two_rpow_mul_nat, ← Real.rpow_add two_pos]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun j _ => h j, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (geom_sum_le_of_lt_one hq0 hq1 _)
    (Real.rpow_pos_of_pos two_pos _).le

/-- For `c = 0`: `∑_{j=0}^{⌊L⌋} 2^{0} ≤ 1 + L`. -/
lemma sum_two_rpow_zero_le {L : ℝ} (hL : 0 ≤ L) :
    ∑ j ∈ range (⌊L⌋₊ + 1), (2 : ℝ) ^ ((0 : ℝ) * (L - j)) ≤ 1 + L := by
  simp only [zero_mul, Real.rpow_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, Nat.cast_add, Nat.cast_one]
  linarith [Nat.floor_le hL]

/-! ### Products and cardinalities -/

/-- For `g_d < 0`: `∑_{ℓ ∈ box n} 2^{g·ℓ} ≤ ∏_d (1 − 2^{g_d})⁻¹`. -/
lemma sum_box_two_rpow_le_prod {g : Fin D → ℝ} (hg : ∀ d, g d < 0) (n : ℕ) :
    ∑ ℓ ∈ box D n, (2 : ℝ) ^ dot g ℓ ≤ ∏ d, (1 - (2 : ℝ) ^ g d)⁻¹ := by
  have h : ∀ ℓ : Fin D → ℕ, (2 : ℝ) ^ dot g ℓ = ∏ d, ((2 : ℝ) ^ g d) ^ ℓ d := by
    intro ℓ
    rw [dot, Real.rpow_sum_of_pos two_pos]
    exact Finset.prod_congr rfl fun d _ => two_rpow_mul_nat (g d) (ℓ d)
  rw [Finset.sum_congr rfl fun ℓ _ => h ℓ, box, ← Finset.prod_univ_sum]
  apply Finset.prod_le_prod
  · intro d _
    exact Finset.sum_nonneg fun k _ => pow_nonneg (Real.rpow_pos_of_pos two_pos _).le _
  · intro d _
    exact geom_sum_le_of_lt_one (Real.rpow_pos_of_pos two_pos _).le
      (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (hg d)) n

/-- The MIMC index set `{ℓ ∈ ℕ^D : θ·ℓ ≤ L}` (Giles 2015, p. 15), as a finite set. -/
noncomputable def indexSet (θ : Fin D → ℝ) (L : ℝ) : Finset (Fin D → ℕ) :=
  (Fintype.piFinset fun d => range (⌊L / θ d⌋₊ + 1)).filter fun ℓ => dot θ ℓ ≤ L

lemma mem_indexSet {θ : Fin D → ℝ} (hθ : ∀ d, 0 < θ d) {L : ℝ} {ℓ : Fin D → ℕ} :
    ℓ ∈ indexSet θ L ↔ dot θ ℓ ≤ L := by
  refine ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨?_, h⟩⟩
  rw [Fintype.mem_piFinset]
  intro d
  rw [Finset.mem_range, Nat.lt_add_one_iff]
  apply Nat.le_floor
  rw [le_div_iff₀ (hθ d)]
  have h1 : θ d * ℓ d ≤ dot θ ℓ :=
    Finset.single_le_sum (f := fun d => θ d * (ℓ d : ℝ))
      (fun d _ => mul_nonneg (hθ d).le (Nat.cast_nonneg _)) (Finset.mem_univ d)
  linarith

/-- For a large enough box, the index set is the part of the box below the level `L`. -/
lemma indexSet_eq_filter_box {θ : Fin D → ℝ} (hθ : ∀ d, 0 < θ d) {L : ℝ} {n : ℕ}
    (hn : ∀ d, ⌊L / θ d⌋₊ + 1 ≤ n) :
    indexSet θ L = (box D n).filter fun ℓ => dot θ ℓ ≤ L := by
  ext ℓ
  rw [Finset.mem_filter, mem_box]
  constructor
  · intro h
    refine ⟨fun d => ?_, (mem_indexSet hθ).1 h⟩
    have h1 := (Fintype.mem_piFinset.1 (Finset.mem_filter.1 h).1) d
    rw [Finset.mem_range] at h1
    exact lt_of_lt_of_le h1 (hn d)
  · exact fun h => (mem_indexSet hθ).2 h.2

/-- A box size containing the index set. -/
noncomputable def boxSize (θ : Fin D → ℝ) (L : ℝ) : ℕ := ∑ d, (⌊L / θ d⌋₊ + 1)

lemma le_boxSize (θ : Fin D → ℝ) (L : ℝ) (d : Fin D) : ⌊L / θ d⌋₊ + 1 ≤ boxSize θ L :=
  Finset.single_le_sum (f := fun d => ⌊L / θ d⌋₊ + 1) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ d)

/-- Sums over the index set as box sums. -/
lemma sum_indexSet_eq {θ : Fin D → ℝ} (hθ : ∀ d, 0 < θ d) (L : ℝ) (f : (Fin D → ℕ) → ℝ) :
    ∑ ℓ ∈ indexSet θ L, f ℓ =
      ∑ ℓ ∈ box D (boxSize θ L), (if dot θ ℓ ≤ L then f ℓ else 0) := by
  rw [indexSet_eq_filter_box hθ (le_boxSize θ L), Finset.sum_filter]

/-- `#{ℓ : θ·ℓ ≤ L} ≤ (1 + L)^D ∏_d (1/θ_d + 1)`. -/
lemma card_indexSet_le {θ : Fin D → ℝ} (hθ : ∀ d, 0 < θ d) {L : ℝ} (hL : 0 ≤ L) :
    ((indexSet θ L).card : ℝ) ≤ (1 + L) ^ D * ∏ d, (1 / θ d + 1) := by
  calc ((indexSet θ L).card : ℝ)
      ≤ ((Fintype.piFinset fun d => range (⌊L / θ d⌋₊ + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = ∏ d, ((⌊L / θ d⌋₊ : ℝ) + 1) := by
        rw [Fintype.card_piFinset]
        simp only [Finset.card_range, Nat.cast_prod, Nat.cast_add, Nat.cast_one]
    _ ≤ ∏ d, ((1 + L) * (1 / θ d + 1)) := by
        apply Finset.prod_le_prod (fun d _ => by positivity)
        intro d _
        have h1 : (⌊L / θ d⌋₊ : ℝ) ≤ L / θ d := Nat.floor_le (div_nonneg hL (hθ d).le)
        have h2 : L / θ d = L * (1 / θ d) := by ring
        have h3 : 0 ≤ 1 / θ d := div_nonneg zero_le_one (hθ d).le
        nlinarith
    _ = (1 + L) ^ D * ∏ d, (1 / θ d + 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end MLMC
