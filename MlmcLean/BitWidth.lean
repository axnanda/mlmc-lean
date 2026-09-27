import MlmcLean.RoundingError
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Haas–Giles §5–§6: the cost model and the optimisation of the bit-widths

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), §5 (p. 11) and §6 (pp. 11–13).

* **(30) ≤ (31)** (§5).  The cost of a fixed-point path is
  `C̃ = ∑_{(i,j) ∈ 𝓜} d_i d_j + ∑_{(i,j) ∈ 𝓢} max(d_i, d_j)` (30), over the multiplications `𝓜`
  and the additions `𝓢`; "replacing `d_i d_j` by its upper bound `½(d_i² + d_j²)`, and
  `max(d_i, d_j)` by its upper bound `d_i + d_j`" gives `C̃ = ½ ∑_i M_i d_i² + ∑_i M'_i d_i` (31),
  where `M_i` (`M'_i`) counts the multiplications (additions) involving `x_i`
  (`opCost_le_sepCost`).
* **(33)** (§6).  The total cost `ε⁻² (∑_ℓ g_ℓ)²`, with `g_ℓ` depending only on the bit-widths of
  level `ℓ`, is minimised exactly when every `g_ℓ` is minimised, and this "is independent of the
  overall desired accuracy `ε`" (`levelwise_optimisation`).
* **(35) is a set of uncoupled scalar equations** (§6.1).  With the variance bound (26) and the
  cost (31), `∂V_indep/∂d_i` and `∂C̃/∂d_i` depend on `d_i` only
  (`hasDerivAt_vIndepR_update`, `hasDerivAt_sepCost_update`), and each equation
  `∂V_indep/∂d_i + λ ∂C̃/∂d_i = 0` has exactly one real solution (`exists_unique_bitWidth`).
* **(36)** (§6.1).  The derivative of the level cost `√(V_ℓ C̃_ℓ) + √(V^Δ_ℓ C_ℓ)` is
  `½ (√(C_ℓ/V^Δ_ℓ) ∂V^Δ_ℓ + √(V_ℓ/C̃_ℓ) ∂C̃_ℓ)`, and it vanishes exactly when (35) holds with
  `λ = √(V_ℓ V^Δ_ℓ / (C_ℓ C̃_ℓ))` (`hasDerivAt_levelCost`, `levelCost_stationary_iff`).
* **(38)** (§6.2).  Rounding the real bit-widths down and adding one bit at a time, in any order,
  reaches a feasible configuration after at most one bit per variable
  (`greedy_rounding_feasible`, with `vIndepR_antitone`).

The variance bound with real bit-widths is `vIndepR`; at natural bit-widths it is `vIndep` of
`MlmcLean.RoundingError` (`vIndepR_natCast`).
-/

open Finset

namespace MLMC

/-! ### §5: the cost model -/

section costModel

variable {ι κ κ' : Type*}

/-- **The cost model (30)** of Haas–Giles (2025, §5, p. 11), after Lee et al. (2006): the cost of
a fixed-point path with bit-widths `d_i` is
`∑_{(i,j) ∈ 𝓜} d_i d_j + ∑_{(i,j) ∈ 𝓢} max(d_i, d_j)`.  The multiplications are indexed by `mul`,
the `k`-th multiplying `x_{a k}` and `x_{b k}`; the additions are indexed by `add`, the `k`-th
adding `x_{a' k}` and `x_{b' k}` (so an operation may occur several times). -/
noncomputable def opCost (mul : Finset κ) (a b : κ → ι) (add : Finset κ') (a' b' : κ' → ι)
    (d : ι → ℝ) : ℝ :=
  ∑ k ∈ mul, d (a k) * d (b k) + ∑ k ∈ add, max (d (a' k)) (d (b' k))

/-- The number of operations of `ops` (with operands `a k` and `b k`) in which the variable
`x_i` is involved, counted once per operand, so that a square `x_i x_i` counts twice: `M_i` for
the multiplications and `M'_i` for the additions (Haas–Giles 2025, §5, p. 11). -/
def opCount [DecidableEq ι] (ops : Finset κ) (a b : κ → ι) (i : ι) : ℕ :=
  (ops.filter fun k => a k = i).card + (ops.filter fun k => b k = i).card

/-- **The separable cost model (31)** of Haas–Giles (2025, §5, p. 11):
`C̃ = ½ ∑_i M_i d_i² + ∑_i M'_i d_i`, a sum of terms each depending on one bit-width `d_i`. -/
noncomputable def sepCost (vars : Finset ι) (M M' : ι → ℝ) (d : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ i ∈ vars, M i * d i ^ 2 + ∑ i ∈ vars, M' i * d i

/-- Double counting: a sum over the operations of a function of one operand is the sum over the
variables, each weighted by the number of operations in which it is that operand. -/
lemma sum_comp_eq_sum_card [DecidableEq ι] (s : Finset κ) (g : κ → ι) {vars : Finset ι}
    (hg : ∀ k ∈ s, g k ∈ vars) (f : ι → ℝ) :
    ∑ k ∈ s, f (g k) = ∑ i ∈ vars, ((s.filter fun k => g k = i).card : ℝ) * f i := by
  rw [← Finset.sum_fiberwise_of_maps_to hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑ k ∈ s.filter (fun k => g k = i), f (g k) = ∑ k ∈ s.filter (fun k => g k = i), f i :=
        Finset.sum_congr rfl fun k hk => by rw [(Finset.mem_filter.1 hk).2]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Haas–Giles (2025), §5, p. 11: the cost (31) bounds the cost (30).**  "Replacing
`d_{i,ℓ} d_{j,ℓ}` by its upper bound `½(d²_{i,ℓ} + d²_{j,ℓ})`, and `max(d_{i,ℓ}, d_{j,ℓ})` by its
upper bound `d_{i,ℓ} + d_{j,ℓ}` we instead use the following form for the cost:
`C̃_ℓ = ½ ∑_i M_{i,ℓ} d²_{i,ℓ} + ∑_i M'_{i,ℓ} d_{i,ℓ}` (31)."  For nonnegative bit-widths of the
variables `vars` (which contain every operand), the cost (30) is at most the cost (31) with
`M_i`, `M'_i` the numbers of multiplications and additions involving `x_i` (`opCount`). -/
theorem opCost_le_sepCost [DecidableEq ι] (vars : Finset ι) (mul : Finset κ) (a b : κ → ι)
    (add : Finset κ') (a' b' : κ' → ι) (hmul : ∀ k ∈ mul, a k ∈ vars ∧ b k ∈ vars)
    (hadd : ∀ k ∈ add, a' k ∈ vars ∧ b' k ∈ vars) {d : ι → ℝ} (hd : ∀ i ∈ vars, 0 ≤ d i) :
    opCost mul a b add a' b' d ≤
      sepCost vars (fun i => (opCount mul a b i : ℝ)) (fun i => (opCount add a' b' i : ℝ)) d := by
  have hM : ∑ k ∈ mul, (d (a k) ^ 2 + d (b k) ^ 2) =
      ∑ i ∈ vars, (opCount mul a b i : ℝ) * d i ^ 2 := by
    rw [Finset.sum_add_distrib,
      sum_comp_eq_sum_card mul a (fun k hk => (hmul k hk).1) (fun i => d i ^ 2),
      sum_comp_eq_sum_card mul b (fun k hk => (hmul k hk).2) (fun i => d i ^ 2),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [opCount, Nat.cast_add]
    ring
  have hA : ∑ k ∈ add, (d (a' k) + d (b' k)) = ∑ i ∈ vars, (opCount add a' b' i : ℝ) * d i := by
    rw [Finset.sum_add_distrib,
      sum_comp_eq_sum_card add a' (fun k hk => (hadd k hk).1) d,
      sum_comp_eq_sum_card add b' (fun k hk => (hadd k hk).2) d,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [opCount, Nat.cast_add]
    ring
  have h1 : ∑ k ∈ mul, d (a k) * d (b k) ≤ (1 / 2) * ∑ k ∈ mul, (d (a k) ^ 2 + d (b k) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (d (a k) - d (b k))]
  have h2 : ∑ k ∈ add, max (d (a' k)) (d (b' k)) ≤ ∑ k ∈ add, (d (a' k) + d (b' k)) :=
    Finset.sum_le_sum fun k hk => max_le_add_of_nonneg (hd _ (hadd k hk).1) (hd _ (hadd k hk).2)
  calc opCost mul a b add a' b' d
      = ∑ k ∈ mul, d (a k) * d (b k) + ∑ k ∈ add, max (d (a' k)) (d (b' k)) := rfl
    _ ≤ (1 / 2) * ∑ k ∈ mul, (d (a k) ^ 2 + d (b k) ^ 2) + ∑ k ∈ add, (d (a' k) + d (b' k)) :=
        add_le_add h1 h2
    _ = sepCost vars (fun i => (opCount mul a b i : ℝ)) (fun i => (opCount add a' b' i : ℝ)) d := by
        rw [hM, hA]
        rfl

end costModel

/-! ### §6: the optimisation of the bit-widths -/

/-- **Haas–Giles (2025), §6, p. 11, (33): the levels are optimised separately, independently of
`ε`.**  After the optimal choice of the sample numbers the total cost is
`ε⁻² (∑_{ℓ=0}^{L} (√(Ṽ_ℓ C̃_ℓ) + √(V^Δ_ℓ C^Δ_ℓ)))²`, and each summand depends only on the bit-widths
of level `ℓ`: "Therefore the bit-widths of all variables of level `ℓ` can be optimised
independently of the other levels by minimising `√(Ṽ_ℓ C̃_ℓ) + √(V^Δ_ℓ C^Δ_ℓ)` (33)", and "this
optimisation is independent of the overall desired accuracy `ε`".  For nonnegative level terms
`g ℓ` of the level configurations `d ℓ ∈ S ℓ`, a configuration minimises `ε⁻² (∑_ℓ g_ℓ(d_ℓ))²` if
and only if each `d ℓ` minimises `g ℓ` over `S ℓ` (a condition that does not involve `ε`). -/
theorem levelwise_optimisation {X : Type*} (L : ℕ) (S : ℕ → Set X) (g : ℕ → X → ℝ)
    (hg : ∀ ℓ x, 0 ≤ g ℓ x) {ε : ℝ} (hε : 0 < ε) {d : ℕ → X} (hd : ∀ ℓ, d ℓ ∈ S ℓ) :
    (∀ d' : ℕ → X, (∀ ℓ, d' ℓ ∈ S ℓ) →
        ε⁻¹ ^ 2 * (∑ ℓ ∈ range (L + 1), g ℓ (d ℓ)) ^ 2 ≤
          ε⁻¹ ^ 2 * (∑ ℓ ∈ range (L + 1), g ℓ (d' ℓ)) ^ 2) ↔
      ∀ ℓ ∈ range (L + 1), ∀ x ∈ S ℓ, g ℓ (d ℓ) ≤ g ℓ x := by
  have hε2 : 0 < ε⁻¹ ^ 2 := by positivity
  constructor
  · intro h ℓ hℓ x hx
    by_contra hlt
    push_neg at hlt
    have hd' : ∀ ℓ', Function.update d ℓ x ℓ' ∈ S ℓ' := by
      intro ℓ'
      rcases eq_or_ne ℓ' ℓ with rfl | h'
      · rw [Function.update_self]
        exact hx
      · rw [Function.update_of_ne h']
        exact hd ℓ'
    have hsum : ∑ ℓ' ∈ range (L + 1), g ℓ' (Function.update d ℓ x ℓ') <
        ∑ ℓ' ∈ range (L + 1), g ℓ' (d ℓ') := by
      refine Finset.sum_lt_sum (fun ℓ' _ => ?_) ⟨ℓ, hℓ, ?_⟩
      · rcases eq_or_ne ℓ' ℓ with rfl | h'
        · rw [Function.update_self]
          exact hlt.le
        · rw [Function.update_of_ne h']
      · rw [Function.update_self]
        exact hlt
    have h0 : 0 ≤ ∑ ℓ' ∈ range (L + 1), g ℓ' (Function.update d ℓ x ℓ') :=
      Finset.sum_nonneg fun _ _ => hg _ _
    have hsq := pow_lt_pow_left₀ hsum h0 two_ne_zero
    exact absurd (h _ hd') (not_le.2 (mul_lt_mul_of_pos_left hsq hε2))
  · intro h d' hd'
    have hle : ∑ ℓ ∈ range (L + 1), g ℓ (d ℓ) ≤ ∑ ℓ ∈ range (L + 1), g ℓ (d' ℓ) :=
      Finset.sum_le_sum fun ℓ hℓ => h ℓ hℓ (d' ℓ) (hd' ℓ)
    have h0 : 0 ≤ ∑ ℓ ∈ range (L + 1), g ℓ (d ℓ) := Finset.sum_nonneg fun _ _ => hg _ _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hle 2) hε2.le

section bitWidths

variable {ι : Type*}

/-- The variance bound (26) of Haas–Giles (2025, §4.2, p. 9) as a function of real bit-widths
`d_i`, as it is used in the optimisation of §6.1:
`V_indep(d) = (1/12) ∑_i E[x̄_i²] 4^{e_i − d_i}`, with `E i = E[x̄_i²]`. -/
noncomputable def vIndepR (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (d : ι → ℝ) : ℝ :=
  (1 / 12) * ∑ i ∈ s, E i * (4 : ℝ) ^ ((e i : ℝ) - d i)

/-- At natural bit-widths the real-variable bound `vIndepR` is the bound `vIndep` of Haas–Giles
(2025, §4.2, p. 9, (26)). -/
theorem vIndepR_natCast (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (d : ι → ℕ) :
    vIndepR s E e (fun i => (d i : ℝ)) = vIndep s E e d := by
  simp only [vIndepR, vIndep]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (e i : ℝ) - (d i : ℝ) = ((e i - d i : ℤ) : ℝ) by push_cast, Real.rpow_intCast]

/-- **(35) is uncoupled: the variance part** (Haas–Giles 2025, §6.1, p. 12: "because of the form
of the variance bound (26) and cost (31), equation (35) gives a set of uncoupled nonlinear scalar
equations").  As a function of one bit-width `d_i` (the others fixed),
`∂V_indep/∂d_i = −(log 4) E[x̄_i²] 4^{e_i − d_i} / 12`, which depends on `d_i` only. -/
theorem hasDerivAt_vIndepR_update [DecidableEq ι] (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ)
    (d : ι → ℝ) {i : ι} (hi : i ∈ s) (t : ℝ) :
    HasDerivAt (fun t => vIndepR s E e (Function.update d i t))
      (-(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - t) / 12)) t := by
  have hsplit : (fun t => vIndepR s E e (Function.update d i t)) = fun t =>
      (1 / 12) * (E i * (4 : ℝ) ^ ((e i : ℝ) - t) +
        ∑ j ∈ s.erase i, E j * (4 : ℝ) ^ ((e j : ℝ) - d j)) := by
    funext t
    have hrest : ∑ j ∈ s.erase i, E j * (4 : ℝ) ^ ((e j : ℝ) - Function.update d i t j) =
        ∑ j ∈ s.erase i, E j * (4 : ℝ) ^ ((e j : ℝ) - d j) :=
      Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    unfold vIndepR
    rw [← Finset.add_sum_erase s (fun j => E j * (4 : ℝ) ^ ((e j : ℝ) - Function.update d i t j))
      hi, Function.update_self, hrest]
  rw [hsplit]
  have h1 : HasDerivAt (fun t => (4 : ℝ) ^ ((e i : ℝ) - t))
      (Real.log 4 * (-1) * (4 : ℝ) ^ ((e i : ℝ) - t)) t :=
    ((hasDerivAt_id' (x := t)).const_sub (e i : ℝ)).const_rpow (by norm_num)
  have h2 := ((h1.const_mul (E i)).add_const
    (∑ j ∈ s.erase i, E j * (4 : ℝ) ^ ((e j : ℝ) - d j))).const_mul (1 / 12)
  convert h2 using 1
  ring

/-- **(35) is uncoupled: the cost part** (Haas–Giles 2025, §6.1, p. 12).  As a function of one
bit-width `d_i` (the others fixed), the cost (31) has `∂C̃/∂d_i = M_i d_i + M'_i`, which depends on
`d_i` only. -/
theorem hasDerivAt_sepCost_update [DecidableEq ι] (vars : Finset ι) (M M' : ι → ℝ) (d : ι → ℝ)
    {i : ι} (hi : i ∈ vars) (t : ℝ) :
    HasDerivAt (fun t => sepCost vars M M' (Function.update d i t)) (M i * t + M' i) t := by
  have hsplit : (fun t => sepCost vars M M' (Function.update d i t)) = fun t =>
      (1 / 2) * (M i * t ^ 2 + ∑ j ∈ vars.erase i, M j * d j ^ 2) +
        (M' i * t + ∑ j ∈ vars.erase i, M' j * d j) := by
    funext t
    have h1 : ∑ j ∈ vars.erase i, M j * Function.update d i t j ^ 2 =
        ∑ j ∈ vars.erase i, M j * d j ^ 2 :=
      Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have h2 : ∑ j ∈ vars.erase i, M' j * Function.update d i t j =
        ∑ j ∈ vars.erase i, M' j * d j :=
      Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    unfold sepCost
    rw [← Finset.add_sum_erase vars (fun j => M j * Function.update d i t j ^ 2) hi,
      ← Finset.add_sum_erase vars (fun j => M' j * Function.update d i t j) hi,
      Function.update_self, h1, h2]
  rw [hsplit]
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hq := ((hsq.const_mul (M i)).add_const (∑ j ∈ vars.erase i, M j * d j ^ 2)).const_mul
    (1 / 2)
  have hl := ((hasDerivAt_id' (x := t)).const_mul (M' i)).add_const
    (∑ j ∈ vars.erase i, M' j * d j)
  convert hq.add hl using 1
  ring

/-- **Each equation (35) has exactly one solution** (Haas–Giles 2025, §6.1, p. 12: (35) "gives a
set of uncoupled nonlinear scalar equations for each pair `i, ℓ`, which are easily solved to obtain
`d_{i,ℓ}`").  With the partial derivatives of `hasDerivAt_vIndepR_update` and
`hasDerivAt_sepCost_update`, equation (35) for the variable `x_i` reads
`−(log 4) E 4^{e − d} / 12 + λ (M d + M') = 0`.  For `λ > 0`, `E = E[x̄_i²] > 0` and operation
counts `M, M' ≥ 0`, not both zero, it has exactly one real solution `d`. -/
theorem exists_unique_bitWidth {lam E M M' : ℝ} (e : ℤ) (hlam : 0 < lam) (hE : 0 < E)
    (hM : 0 ≤ M) (hM' : 0 ≤ M') (hMM : 0 < M + M') :
    ∃! t : ℝ, -(Real.log 4 * E * (4 : ℝ) ^ ((e : ℝ) - t) / 12) + lam * (M * t + M') = 0 := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 4 * E / 12 := by positivity
  set c : ℝ := Real.log 4 * E / 12 with hc_def
  let φ : ℝ → ℝ := fun t => lam * (M * t + M') - c * (4 : ℝ) ^ ((e : ℝ) - t)
  have key : ∀ t : ℝ,
      -(Real.log 4 * E * (4 : ℝ) ^ ((e : ℝ) - t) / 12) + lam * (M * t + M') = φ t := fun t => by
    simp only [φ, hc_def]
    ring
  simp only [key]
  have hmono : StrictMono φ := by
    intro s t hst
    have h4 : (4 : ℝ) ^ ((e : ℝ) - t) < (4 : ℝ) ^ ((e : ℝ) - s) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    have hMst : M * s ≤ M * t := mul_le_mul_of_nonneg_left hst.le hM
    have h5 := mul_lt_mul_of_pos_left h4 hc
    have h6 := mul_le_mul_of_nonneg_left hMst hlam.le
    show lam * (M * s + M') - c * (4 : ℝ) ^ ((e : ℝ) - s) <
      lam * (M * t + M') - c * (4 : ℝ) ^ ((e : ℝ) - t)
    nlinarith
  have hcont : Continuous φ := by
    have h4 : Continuous fun t : ℝ => (4 : ℝ) ^ ((e : ℝ) - t) :=
      continuous_const.rpow (continuous_const.sub continuous_id) fun _ => Or.inl (by norm_num)
    exact (continuous_const.mul ((continuous_const.mul continuous_id).add continuous_const)).sub
      (continuous_const.mul h4)
  -- a point where `φ > 0`
  obtain ⟨t₂, ht₂1, ht₂⟩ : ∃ t₂ : ℝ, 1 ≤ t₂ ∧ 0 < φ t₂ := by
    have hA : 0 < lam * (M + M') := mul_pos hlam hMM
    refine ⟨max 1 ((e : ℝ) - Real.logb 4 (lam * (M + M') / c) + 1), le_max_left _ _, ?_⟩
    set t₂ := max 1 ((e : ℝ) - Real.logb 4 (lam * (M + M') / c) + 1) with ht₂def
    have h1 : 1 ≤ t₂ := le_max_left _ _
    have h2 : (e : ℝ) - Real.logb 4 (lam * (M + M') / c) + 1 ≤ t₂ := le_max_right _ _
    have h4 : (4 : ℝ) ^ ((e : ℝ) - t₂) < lam * (M + M') / c :=
      calc (4 : ℝ) ^ ((e : ℝ) - t₂) < (4 : ℝ) ^ (Real.logb 4 (lam * (M + M') / c)) :=
            Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
        _ = lam * (M + M') / c := Real.rpow_logb (by norm_num) (by norm_num) (div_pos hA hc)
    have h5 : c * (4 : ℝ) ^ ((e : ℝ) - t₂) < lam * (M + M') := by
      rw [mul_comm c]
      exact (lt_div_iff₀ hc).1 h4
    have h6 : M * 1 ≤ M * t₂ := mul_le_mul_of_nonneg_left h1 hM
    have h7 : lam * (M + M') ≤ lam * (M * t₂ + M') :=
      mul_le_mul_of_nonneg_left (by linarith) hlam.le
    show 0 < lam * (M * t₂ + M') - c * (4 : ℝ) ^ ((e : ℝ) - t₂)
    linarith
  -- a point where `φ < 0`
  obtain ⟨t₁, ht₁0, ht₁⟩ : ∃ t₁ : ℝ, t₁ ≤ 0 ∧ φ t₁ < 0 := by
    have hB : 0 < lam * M' + 1 := by positivity
    refine ⟨min 0 ((e : ℝ) - Real.logb 4 ((lam * M' + 1) / c)), min_le_left _ _, ?_⟩
    set t₁ := min 0 ((e : ℝ) - Real.logb 4 ((lam * M' + 1) / c)) with ht₁def
    have h1 : t₁ ≤ 0 := min_le_left _ _
    have h2 : t₁ ≤ (e : ℝ) - Real.logb 4 ((lam * M' + 1) / c) := min_le_right _ _
    have h4 : (lam * M' + 1) / c ≤ (4 : ℝ) ^ ((e : ℝ) - t₁) :=
      calc (lam * M' + 1) / c = (4 : ℝ) ^ (Real.logb 4 ((lam * M' + 1) / c)) :=
            (Real.rpow_logb (by norm_num) (by norm_num) (div_pos hB hc)).symm
        _ ≤ (4 : ℝ) ^ ((e : ℝ) - t₁) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h5 : lam * M' + 1 ≤ c * (4 : ℝ) ^ ((e : ℝ) - t₁) := by
      rw [mul_comm c]
      exact (div_le_iff₀ hc).1 h4
    have h6 : M * t₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM h1
    have h7 : lam * (M * t₁ + M') ≤ lam * M' := by nlinarith
    show lam * (M * t₁ + M') - c * (4 : ℝ) ^ ((e : ℝ) - t₁) < 0
    linarith
  have hle : t₁ ≤ t₂ := by linarith
  obtain ⟨t₀, -, ht₀⟩ := intermediate_value_Icc hle hcont.continuousOn
    (Set.mem_Icc.2 ⟨ht₁.le, ht₂.le⟩)
  exact ⟨t₀, ht₀, fun t ht => hmono.injective (ht.trans ht₀.symm)⟩

/-- The rewriting of the derivative of `√(x · f)` used for (36): for `x, y > 0`,
`x z / (2 √(x y)) = √(x / y) z / 2`. -/
lemma mul_div_two_sqrt_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℝ) :
    x * z / (2 * Real.sqrt (x * y)) = Real.sqrt (x / y) * z / 2 := by
  have key : Real.sqrt (x / y) * Real.sqrt (x * y) = x := by
    rw [← Real.sqrt_mul (div_pos hx hy).le,
      show x / y * (x * y) = x * x by
        rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ x hy.ne'],
      Real.sqrt_mul_self hx.le]
  rw [div_eq_div_iff (mul_pos two_pos (Real.sqrt_pos.2 (mul_pos hx hy))).ne' two_ne_zero]
  linear_combination (-2 * z) * key

/-- **Haas–Giles (2025), §6.1, p. 12, (36).**  "Minimising (34) [the level cost
`√(V_ℓ C̃_ℓ) + √(V^Δ_ℓ C_ℓ)`] by equating its derivative to zero gives
`√(C_ℓ/V^Δ_ℓ(d)) ∂V^Δ_ℓ/∂d_{i,ℓ} + √(V_ℓ/C̃_ℓ(d)) ∂C̃_ℓ/∂d_{i,ℓ} = 0` (36)."  If, as functions of
one bit-width `t`, the cost `C̃(t) > 0` and the variance `V^Δ(t) > 0` have derivatives `C̃'` and
`V^Δ'`, then the level cost has derivative `½ (√(C/V^Δ) V^Δ' + √(V/C̃) C̃')` (for `V, C > 0`), so
it vanishes exactly when (36) holds. -/
theorem hasDerivAt_levelCost {Ct Vd : ℝ → ℝ} {Ct' Vd' V C t : ℝ} (hV : 0 < V) (hC : 0 < C)
    (hCt : 0 < Ct t) (hVd : 0 < Vd t) (hdC : HasDerivAt Ct Ct' t) (hdV : HasDerivAt Vd Vd' t) :
    HasDerivAt (fun t => Real.sqrt (V * Ct t) + Real.sqrt (Vd t * C))
      ((Real.sqrt (C / Vd t) * Vd' + Real.sqrt (V / Ct t) * Ct') / 2) t := by
  have h1 := (hdC.const_mul V).sqrt (mul_pos hV hCt).ne'
  have h2 := (hdV.mul_const C).sqrt (mul_pos hVd hC).ne'
  convert h1.add h2 using 1
  rw [mul_div_two_sqrt_mul hV hCt, mul_comm (Vd t) C, mul_comm Vd' C,
    mul_div_two_sqrt_mul hC hVd]
  ring

/-- **(36) is (35) with `λ = √(V_ℓ V^Δ_ℓ / (C_ℓ C̃_ℓ))`** (Haas–Giles 2025, §6.1, p. 12: "so it is
again of the form (35), where `λ = √(V_ℓ V^Δ_ℓ(d) / C_ℓ C̃_ℓ(d))` gives the optimal trade-off
between cost and variance").  For positive `V, C, C̃, V^Δ`, the derivative of the level cost in
`hasDerivAt_levelCost` vanishes if and only if `V^Δ' + λ C̃' = 0` with
`λ = √(V V^Δ / (C C̃))`. -/
theorem levelCost_stationary_iff {V C Ct Vd Ct' Vd' : ℝ} (hV : 0 < V) (hC : 0 < C)
    (hCt : 0 < Ct) (hVd : 0 < Vd) :
    (Real.sqrt (C / Vd) * Vd' + Real.sqrt (V / Ct) * Ct') / 2 = 0 ↔
      Vd' + Real.sqrt (V * Vd / (C * Ct)) * Ct' = 0 := by
  have ha : 0 < Real.sqrt (C / Vd) := Real.sqrt_pos.2 (div_pos hC hVd)
  have key : Real.sqrt (C / Vd) * Real.sqrt (V * Vd / (C * Ct)) = Real.sqrt (V / Ct) := by
    rw [← Real.sqrt_mul (div_pos hC hVd).le]
    congr 1
    rw [div_mul_div_comm, div_eq_div_iff (mul_pos hVd (mul_pos hC hCt)).ne' hCt.ne']
    ring
  have hfac : Real.sqrt (C / Vd) * Vd' + Real.sqrt (V / Ct) * Ct' =
      Real.sqrt (C / Vd) * (Vd' + Real.sqrt (V * Vd / (C * Ct)) * Ct') := by
    rw [mul_add, ← mul_assoc, key]
  rw [hfac, div_eq_zero_iff, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h ha.ne'
    · exact h
    · exact absurd h two_ne_zero
  · intro h
    exact Or.inl (Or.inr h)

/-- The variance bound decreases when bits are added: `vIndepR` is antitone in the bit-widths
(Haas–Giles 2025, §4.2, (26), with `E[x̄_i²] ≥ 0`). -/
theorem vIndepR_antitone (s : Finset ι) {E : ι → ℝ} (hE : ∀ i ∈ s, 0 ≤ E i) (e : ι → ℤ) :
    Antitone (vIndepR s E e) := by
  intro d d' hdd'
  unfold vIndepR
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by norm_num)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hdd' i])) (hE i hi)

/-- **The rounding of the bit-widths is feasible** (Haas–Giles 2025, §6.2, p. 13, with (38):
"For each level `ℓ` and each variable `i`, first round down the solution ... Then order the ratios
in decreasing order and add one bit to the variables with the highest ratio until the constraint
on the error is satisfied.  This heuristic ... is guaranteed to obtain a feasible solution").  Let
the real bit-widths `d` satisfy the variance constraint `V(d) ≤ τ` for a variance bound `V` that
decreases when bits are added (such as `vIndepR`, `vIndepR_antitone`).  For any order `σ` of the
`n` variables (the order of the ratios (38)), let `d^{(k)}` be `⌊d⌋` with one bit added to the
first `k` variables.  Then some `k ≤ n` gives a configuration that satisfies the constraint. -/
theorem greedy_rounding_feasible {n : ℕ} (σ : ι ≃ Fin n) {V : (ι → ℝ) → ℝ} (hV : Antitone V)
    {d : ι → ℝ} {τ : ℝ} (hd : V d ≤ τ) :
    ∃ k ≤ n, V (fun i => (⌊d i⌋ : ℝ) + if ((σ i : ℕ) < k) then 1 else 0) ≤ τ := by
  refine ⟨n, le_rfl, ?_⟩
  have hle : d ≤ fun i => (⌊d i⌋ : ℝ) + if ((σ i : ℕ) < n) then 1 else 0 := by
    intro i
    show d i ≤ (⌊d i⌋ : ℝ) + if ((σ i : ℕ) < n) then 1 else 0
    rw [if_pos (σ i).isLt]
    exact (Int.lt_floor_add_one (d i)).le
  exact (hV hle).trans hd

end bitWidths

end MLMC
