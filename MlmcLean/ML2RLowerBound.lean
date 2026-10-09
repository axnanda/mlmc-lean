import MlmcLean.ML2RTheorem
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# A lower bound on the cost of ML2R: the printed exponent fails (Giles 2015, §2.3)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.3
(pp. 11–12 of the author's version; `docs/giles2015.txt`, l. 529–564), presenting the multilevel
Richardson–Romberg (ML2R) estimator of Lemaire and Pagès (2013):

"Assuming that the weak error has a regular expansion
`E[P_ℓ] − E[P] = ∑_{n=1}^{L} a_n 2^{−nαℓ} + O(2^{−αℓL})`, they first determine the unique set of
weights `w_ℓ`, `ℓ = 0, 1, …, L` …" (p. 11, l. 529–532) "so that
`(∑_{ℓ=0}^{L} w_ℓ E[P_ℓ]) − E[P] = ∑_{ℓ=0}^{L} w_ℓ (E[P_ℓ] − E[P]) = O(2^{−αL²})`" (p. 12,
l. 539–543); "Because the remaining error is `O(2^{−αL²})`, rather than the usual `O(2^{−αL})`, it
is possible to obtain the usual `O(ε)` weak error with a value of `L` which is the square root of
the usual value.  Hence, in the case `β = γ` they prove that the overall cost is reduced to
`O(ε⁻² |log ε|)`, while for `β < γ` the cost is reduced much more to
`O(ε⁻² 2^{(γ−β)√(|log₂ ε|/α)})`." (p. 12, l. 559–564).

`MlmcLean/ML2RTheorem.lean` proves the upper bound `O(ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)})`
(`ml2r_theorem_lt`), with `√2` times the printed exponent, because the bias is
`O(2^{−αL(L+1)/2})` (`ml2r_bias_le`) and not the printed `O(2^{−αL²})` (`ml2r_bias`,
`ml2r_bias_not_attainable`).  This file proves a matching lower bound: the printed cost exponent is
false, and the corrected one is sharp up to an additive constant in the exponent.

* **The lower bound** (`ml2r_cost_lower`).  Setting of `ml2r_theorem_lt`: mutually independent
  inputs `ω (ℓ, n)` of law `ν`, measurable square-integrable `P_ℓ`, the ML2R estimator
  `Y = ml2rEstimator α Pl ω L N` and a target `EP`.  If the bias of the extrapolated mean is at
  least `b 2^{−αL(L+1)/2}` for every `L` (`b > 0`), `V[P_ℓ − P_{ℓ−1}] ≥ c₂ 2^{−βℓ}` and
  `C_ℓ ≥ c₃ 2^{γℓ}` (`c₃ ≥ 0`), then for every `ε > 0`, **every** `L` and `N_ℓ ≥ 1` with
  `E[(Y − EP)²] ≤ ε²` have `αL(L+1)/2 ≥ log₂(b/ε)` and cost
  `∑_{ℓ≤L} N_ℓ C_ℓ ≥ c₂ c₃ ε⁻² 2^{(γ−β)L}`.  Proof: `E[(Y − EP)²] = ∑_ℓ v_ℓ² V_ℓ/N_ℓ + bias²`
  (`ml2rEstimator_mse`); the bias term gives the first claim; on the finest level
  `v_L = w_L ≥ 1` (`one_le_ml2rWeight_self`), so `N_L ≥ V_L/ε²` and the cost is at least
  `N_L C_L`.
* **In terms of `ε`** (`ml2r_cost_lower_sqrt`): if moreover `b ≤ 1`, `β ≤ γ` and `c₂, c₃ > 0`,
  then for `0 < ε < 1` every admissible `L` is at least `√(2 log₂(1/ε)/α) − κ`,
  `κ = ½ + √(2 log₂(1/b)/α)`, and the cost is at least
  `c₂ c₃ 2^{−(γ−β)κ} ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}`.
* **The printed bound is false** (`ml2r_printed_cost_fails`): under the hypotheses of the lower
  bound with `β < γ` and `c₂, c₃ > 0`, there are no `c` and `ε₀ > 0` such that for every
  `0 < ε < ε₀` some `L` and `N_ℓ ≥ 1` reach `E[(Y − EP)²] ≤ ε²` at cost
  `≤ c ε⁻² 2^{(γ−β)√(|log₂ ε|/α)}`.
* **A concrete instance** (`ml2r_instance_hypotheses`, `ml2r_instance_cost`,
  `ml2r_instance_printed_cost_false`): one standard normal input `z ∼ N(0, 1)` per sample,
  `P_ℓ(z) = x_ℓ/(1 + x_ℓ) + s_ℓ z` with `x_ℓ = 2^{−αℓ}` and `s_ℓ = ∑_{j=0}^{ℓ} 2^{−βj/2}`
  (`ml2rInstPl`), target `E[P] = 0`, per-sample cost `C_ℓ = 2^{γℓ}`, and the samples the
  coordinates of `(ℝ^{ℕ×ℕ}, N(0, 1)^{⊗(ℕ×ℕ)})`.  Its weak error `x_ℓ/(1 + x_ℓ)` has the paper's
  expansion `∑_{n=1}^{L} (−1)^{n+1} 2^{−nαℓ} + R_ℓ` with `|R_ℓ| ≤ 2^{−αℓL}` for every `L` (all
  `a_n ≠ 0`, `O`-constant `1` independent of `L`), `V[P_ℓ − P_{ℓ−1}] = 2^{−βℓ}` exactly, and its
  ML2R bias is exactly `∏_{k=0}^{L} x_k/(1 + x_k)` (`ml2r_sum_weight_mul_div_one_add`), between
  `e^{−1/(1−2^{−α})} 2^{−αL(L+1)/2}` and `2^{−αL(L+1)/2}`.  It satisfies the hypotheses of
  `ml2r_theorem_lt` and of the lower bound, so for `β < γ`, `γ > 0`, the least cost of mean square
  error `ε²` lies between `c₅ ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}` and
  `c₄ ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}`, and the printed bound is false for it.

Form of the results: these are statements about the mean square error of the ML2R estimator
built from independent samples (the setting of `ml2r_theorem_lt`), not only a deterministic core;
the deterministic step is `ml2r_lower_core`.  Not covered: the cost is the repository's
`∑_{ℓ≤L} N_ℓ C_ℓ` with sample sizes `N_ℓ ≥ 1` fixed in advance (no random or adaptive `N_ℓ`); the
lower bound is for the ML2R weights `ml2rWeight α L` with the `α` of the expansion (the paper's
second weight condition "`= 1`" read as "`= 0`", see `ml2r_weights`), not for other weights or
other estimators; the case `β = γ` is not addressed (the bound gives `ε⁻²`, not `ε⁻² |log ε|`).
For `β > 0` the example's `P_ℓ` converge in `L²` to `P = s_∞ z`, with `E[P] = 0` (a remark, not
formalised; the setting of `ml2r_theorem_lt` only uses the number `E[P]`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### The weights -/

section weights

/-- The ML2R nodes `x_k = 2^{−αk}` are positive (Giles 2015, §2.3, p. 11, l. 529–531). -/
lemma ml2rNode_pos (α : ℝ) (k : ℕ) : 0 < ml2rNode α k := Real.rpow_pos_of_pos two_pos _

/-- For `α > 0` the ML2R nodes `x_k = 2^{−αk}` decrease strictly in `k` (Giles 2015, §2.3,
p. 11, l. 529–531). -/
lemma ml2rNode_lt_ml2rNode {α : ℝ} (hα : 0 < α) {k ℓ : ℕ} (hkℓ : k < ℓ) :
    ml2rNode α ℓ < ml2rNode α k := by
  rw [ml2rNode, ml2rNode]
  refine Real.rpow_lt_rpow_of_exponent_lt one_lt_two ?_
  have : (k : ℝ) < ℓ := Nat.cast_lt.2 hkℓ
  nlinarith

/-- For `α > 0` the ML2R nodes satisfy `x_k = 2^{−αk} ≤ 1` (Giles 2015, §2.3, p. 11,
l. 529–531). -/
lemma ml2rNode_le_one {α : ℝ} (hα : 0 < α) (k : ℕ) : ml2rNode α k ≤ 1 := by
  rw [ml2rNode]
  exact Real.rpow_le_one_of_one_le_of_nonpos one_le_two
    (neg_nonpos.2 (mul_nonneg hα.le (Nat.cast_nonneg k)))

/-- **The ML2R weight of the finest level is at least `1`** (Giles 2015, §2.3, p. 11: Lemaire and
Pagès "first determine the unique set of weights `w_ℓ`, `ℓ = 0, 1, …, L`"; see `ml2r_weights`).
For `α > 0`, `w_L = ∏_{k<L} x_k/(x_k − x_L) ≥ 1`, since `x_k > x_L > 0` for `k < L`.  As
`v_L = ∑_{ℓ'=L}^{L} w_ℓ' = w_L`, the finest level of the ML2R estimator enters its variance with a
factor `v_L² ≥ 1`. -/
lemma one_le_ml2rWeight_self {α : ℝ} (hα : 0 < α) (L : ℕ) : 1 ≤ ml2rWeight α L L := by
  rw [ml2rWeight]
  have h : ∏ k ∈ (range (L + 1)).erase L, (1 : ℝ) ≤
      ∏ k ∈ (range (L + 1)).erase L, ml2rNode α k / (ml2rNode α k - ml2rNode α L) := by
    refine Finset.prod_le_prod (fun _ _ => zero_le_one) fun k hk => ?_
    have hkL : k < L := by
      have h1 := Finset.mem_erase.1 hk
      have h2 := Finset.mem_range.1 h1.2
      omega
    have hlt := ml2rNode_lt_ml2rNode hα hkL
    have hpos := ml2rNode_pos α L
    rw [one_le_div (by linarith)]
    linarith
  rwa [Finset.prod_const_one] at h

/-- `∑_{ℓ=0}^{L} w_ℓ/(1 + x_ℓ) = 1 − ∏_{k=0}^{L} x_k/(1 + x_k)` for the ML2R weights and nodes
`x_k = 2^{−αk}` (Giles 2015, §2.3).  Proof: with `Q = ∏_k (X − x_k)` and `c = Q(−1)`, the
polynomial `S = (Q − c)/(X + 1)` has degree `≤ L`, `S(x_ℓ) = −c/(1 + x_ℓ)` and `S(0) = Q(0) − c`,
and the weights evaluate polynomials of degree `≤ L` at `0` (`ml2r_sum_eval`). -/
lemma ml2r_sum_weight_inv_one_add {α : ℝ} (hα : 0 < α) (L : ℕ) :
    ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * (1 + ml2rNode α ℓ)⁻¹ =
      1 - ∏ k ∈ range (L + 1), ml2rNode α k / (1 + ml2rNode α k) := by
  set Q := Lagrange.nodal (range (L + 1)) (ml2rNode α) with hQ
  set c := Q.eval (-1) with hc
  have hQdeg : Q.degree = ((L + 1 : ℕ) : WithBot ℕ) := by
    rw [hQ, Lagrange.degree_nodal, card_range]
  have hpdeg : (Q - Polynomial.C c).degree = ((L + 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_sub_C (by rw [hQdeg]; exact WithBot.coe_pos.2 (Nat.succ_pos L)), hQdeg]
  have hp0 : Q - Polynomial.C c ≠ 0 := fun h => by
    rw [h, Polynomial.degree_zero] at hpdeg
    exact WithBot.bot_ne_coe hpdeg
  have hroot : (Q - Polynomial.C c).IsRoot (-1) := by
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C, hc, sub_self]
  set S := (Q - Polynomial.C c) /ₘ (Polynomial.X - Polynomial.C (-1)) with hS
  have hmul : (Polynomial.X - Polynomial.C (-1)) * S = Q - Polynomial.C c :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hSdeg : S.degree < ((L + 1 : ℕ) : WithBot ℕ) := by
    rw [← hpdeg]
    exact Polynomial.degree_divByMonic_lt _ _ hp0
      (by rw [Polynomial.degree_X_sub_C]; exact zero_lt_one)
  have heval : ∀ x : ℝ, (x + 1) * S.eval x = Q.eval x - c := fun x => by
    have h := congrArg (Polynomial.eval x) hmul
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_C, sub_neg_eq_add] at h
    exact h
  have hnode : ∀ ℓ ∈ range (L + 1),
      ml2rWeight α L ℓ * S.eval (ml2rNode α ℓ) =
        -c * (ml2rWeight α L ℓ * (1 + ml2rNode α ℓ)⁻¹) := fun ℓ hℓ => by
    have h := heval (ml2rNode α ℓ)
    rw [hQ, Lagrange.eval_nodal_at_node hℓ, zero_sub] at h
    have hx : ml2rNode α ℓ + 1 ≠ 0 := by linarith [ml2rNode_pos α ℓ]
    have hS' : S.eval (ml2rNode α ℓ) = -c * (1 + ml2rNode α ℓ)⁻¹ := by
      rw [add_comm 1, ← div_eq_mul_inv, eq_div_iff hx, mul_comm]
      exact h
    rw [hS']
    ring
  have h0 : S.eval 0 = Q.eval 0 - c := by
    have h := heval 0
    rwa [zero_add, one_mul] at h
  have hsum := ml2r_sum_eval hα L hSdeg
  rw [Finset.sum_congr rfl hnode, ← Finset.mul_sum, h0] at hsum
  have hc' : c = ∏ k ∈ range (L + 1), (-1 - ml2rNode α k) := by
    rw [hc, hQ, Lagrange.eval_nodal]
  have hQ0 : Q.eval 0 = ∏ k ∈ range (L + 1), (0 - ml2rNode α k) := by
    rw [hQ, Lagrange.eval_nodal]
  have hc0 : c ≠ 0 := by
    rw [hc']
    exact Finset.prod_ne_zero_iff.2 fun k _ => by linarith [ml2rNode_pos α k]
  have hratio : Q.eval 0 / c = ∏ k ∈ range (L + 1), ml2rNode α k / (1 + ml2rNode α k) := by
    rw [hQ0, hc', ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zero_sub, show (-1 - ml2rNode α k) = -(1 + ml2rNode α k) by ring, neg_div_neg_eq]
  rw [← hratio]
  refine mul_left_cancel₀ hc0 ?_
  rw [mul_sub, mul_one, mul_div_cancel₀ _ hc0]
  linarith

/-- **The ML2R bias of the weak error `x/(1 + x)`** (Giles 2015, §2.3, p. 12, l. 539–543:
"`(∑_{ℓ=0}^{L} w_ℓ E[P_ℓ]) − E[P] = ∑_{ℓ=0}^{L} w_ℓ (E[P_ℓ] − E[P]) = O(2^{−αL²})`").  If
`E[P_ℓ] − E[P] = x_ℓ/(1 + x_ℓ)` with `x_ℓ = 2^{−αℓ}`, the bias of the extrapolated mean is exactly
`∑_{ℓ=0}^{L} w_ℓ x_ℓ/(1 + x_ℓ) = ∏_{k=0}^{L} x_k/(1 + x_k)`, of order `2^{−αL(L+1)/2}`. -/
theorem ml2r_sum_weight_mul_div_one_add {α : ℝ} (hα : 0 < α) (L : ℕ) :
    ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * (ml2rNode α ℓ / (1 + ml2rNode α ℓ)) =
      ∏ k ∈ range (L + 1), ml2rNode α k / (1 + ml2rNode α k) := by
  have hsum1 : ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ = 1 := by
    have h := (ml2r_weights hα L).1 0 (Nat.zero_le L)
    rw [if_pos rfl] at h
    rw [← h]
    exact Finset.sum_congr rfl fun ℓ _ => by rw [pow_zero, mul_one]
  have e : ∀ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * (ml2rNode α ℓ / (1 + ml2rNode α ℓ)) =
      ml2rWeight α L ℓ - ml2rWeight α L ℓ * (1 + ml2rNode α ℓ)⁻¹ := fun ℓ _ => by
    have hx : 1 + ml2rNode α ℓ ≠ 0 := by linarith [ml2rNode_pos α ℓ]
    field_simp
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, hsum1, ml2r_sum_weight_inv_one_add hα L]
  ring

/-- `e^{−1/(1−2^{−α})} 2^{−αL(L+1)/2} ≤ ∏_{k=0}^{L} x_k/(1 + x_k) ≤ 2^{−αL(L+1)/2}` for the nodes
`x_k = 2^{−αk}`, `α > 0` (Giles 2015, §2.3): `1 ≤ ∏_k (1 + x_k) ≤ e^{∑_k x_k}` and
`∑_k x_k ≤ 1/(1 − 2^{−α})`. -/
lemma prod_ml2rNode_div_one_add_mem {α : ℝ} (hα : 0 < α) (L : ℕ) :
    Real.exp (-(1 - (2 : ℝ) ^ (-α))⁻¹) * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) ≤
        ∏ k ∈ range (L + 1), ml2rNode α k / (1 + ml2rNode α k) ∧
      ∏ k ∈ range (L + 1), ml2rNode α k / (1 + ml2rNode α k) ≤
        (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-α) := (Real.rpow_pos_of_pos two_pos _).le
  have hr1 : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hprod : ∏ k ∈ range (L + 1), ml2rNode α k / (1 + ml2rNode α k) =
      (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) / ∏ k ∈ range (L + 1), (1 + ml2rNode α k) := by
    rw [Finset.prod_div_distrib, prod_ml2rNode]
  have hP1 : 1 ≤ ∏ k ∈ range (L + 1), (1 + ml2rNode α k) := by
    have h : ∏ k ∈ range (L + 1), (1 : ℝ) ≤ ∏ k ∈ range (L + 1), (1 + ml2rNode α k) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) fun k _ => by linarith [ml2rNode_pos α k]
    rwa [Finset.prod_const_one] at h
  have hPexp : ∏ k ∈ range (L + 1), (1 + ml2rNode α k) ≤ Real.exp ((1 - (2 : ℝ) ^ (-α))⁻¹) := by
    calc ∏ k ∈ range (L + 1), (1 + ml2rNode α k)
        ≤ ∏ k ∈ range (L + 1), Real.exp (ml2rNode α k) :=
          Finset.prod_le_prod (fun k _ => by linarith [ml2rNode_pos α k])
            fun k _ => by linarith [Real.add_one_le_exp (ml2rNode α k)]
      _ = Real.exp (∑ k ∈ range (L + 1), ml2rNode α k) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp ((1 - (2 : ℝ) ^ (-α))⁻¹) := by
          refine Real.exp_le_exp.2 ?_
          rw [Finset.sum_congr rfl fun k _ => ml2rNode_eq α k]
          exact geom_sum_le_of_lt_one hr0 hr1 _
  have h2 : 0 < (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) := Real.rpow_pos_of_pos two_pos _
  rw [hprod]
  refine ⟨?_, div_le_self h2.le hP1⟩
  rw [Real.exp_neg, mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left h2.le (by linarith) hPexp

/-- The weak error `x/(1 + x)` has the expansion `∑_{n=1}^{L} (−1)^{n+1} x^n` with remainder
`(−1)^L x^{L+1}/(1 + x)`, for `x ≠ −1` and every `L` (Giles 2015, §2.3, l. 529–531). -/
lemma div_one_add_sub_sum (x : ℝ) (hx : 1 + x ≠ 0) (L : ℕ) :
    x / (1 + x) - ∑ n ∈ Icc 1 L, (-1 : ℝ) ^ (n + 1) * x ^ n = (-1) ^ L * x ^ (L + 1) / (1 + x) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ L + 1), ← sub_sub, ih]
    field_simp
    ring

end weights

/-! ### The lower bound -/

section core

/-- **The deterministic core of the ML2R cost lower bound** (Giles 2015, §2.3, p. 12, l. 559–564).
If the mean square error `w² V/n + B² ≤ ε²` (the finest-level variance term `v_L² V_L/N_L` with
`v_L = w ≥ 1`, and the bias `B`), the bias is at least `b 2^{−αL(L+1)/2}`, `V ≥ c₂ 2^{−βL}` and the
cost `T` is at least `n C` with `C ≥ c₃ 2^{γL}`, then `αL(L+1)/2 ≥ log₂(b/ε)` and
`T ≥ c₂ c₃ ε⁻² 2^{(γ−β)L}`. -/
lemma ml2r_lower_core {α β γ b c₂ c₃ ε B w V n C T : ℝ} {L : ℕ} (hb : 0 < b) (hε : 0 < ε)
    (hc₃ : 0 ≤ c₃) (hV0 : 0 ≤ V) (hn : 0 < n) (hw : 1 ≤ w) (hmse : w ^ 2 * V / n + B ^ 2 ≤ ε ^ 2)
    (hbias : b * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) ≤ |B|)
    (hV : c₂ * (2 : ℝ) ^ (-(β * (L : ℝ))) ≤ V) (hC : c₃ * (2 : ℝ) ^ (γ * (L : ℝ)) ≤ C)
    (hT : n * C ≤ T) :
    Real.logb 2 (b / ε) ≤ α * ((L : ℝ) * (L + 1) / 2) ∧
      c₂ * c₃ * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * (L : ℝ))) ≤ T := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hT0 : 0 ≤ w ^ 2 * V / n := div_nonneg (mul_nonneg (sq_nonneg w) hV0) hn.le
  have hB : |B| ≤ ε := by
    have h : B ^ 2 ≤ ε ^ 2 := by linarith
    have h' := sq_le_sq.1 h
    rwa [abs_of_pos hε] at h'
  constructor
  · rw [Real.logb_le_iff_le_rpow one_lt_two (div_pos hb hε), div_le_iff₀ hε]
    have h2t : (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) *
        (2 : ℝ) ^ (α * ((L : ℝ) * (L + 1) / 2)) = 1 := by
      rw [← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero]
    have h := mul_le_mul_of_nonneg_right (hbias.trans hB)
      (Real.rpow_pos_of_pos two_pos (α * ((L : ℝ) * (L + 1) / 2))).le
    rw [mul_assoc, h2t, mul_one] at h
    linarith
  · have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw
    have hVn : V ≤ ε ^ 2 * n := by
      have h1 : w ^ 2 * V / n ≤ ε ^ 2 := by linarith [sq_nonneg B]
      rw [div_le_iff₀ hn] at h1
      nlinarith
    have hc3 : 0 ≤ c₃ * (2 : ℝ) ^ (γ * (L : ℝ)) :=
      mul_nonneg hc₃ (Real.rpow_pos_of_pos two_pos _).le
    have key : c₂ * (2 : ℝ) ^ (-(β * (L : ℝ))) * (c₃ * (2 : ℝ) ^ (γ * (L : ℝ))) ≤ ε ^ 2 * T :=
      calc c₂ * (2 : ℝ) ^ (-(β * (L : ℝ))) * (c₃ * (2 : ℝ) ^ (γ * (L : ℝ)))
          ≤ (ε ^ 2 * n) * C := mul_le_mul (hV.trans hVn) hC hc3 (by positivity)
        _ = ε ^ 2 * (n * C) := by ring
        _ ≤ ε ^ 2 * T := mul_le_mul_of_nonneg_left hT hε2.le
    have he : ε ^ (-2 : ℝ) = (ε ^ 2)⁻¹ := by rw [Real.rpow_neg hε.le, Real.rpow_two]
    have hp : (2 : ℝ) ^ ((γ - β) * (L : ℝ)) =
        (2 : ℝ) ^ (-(β * (L : ℝ))) * (2 : ℝ) ^ (γ * (L : ℝ)) := by
      rw [← Real.rpow_add two_pos]
      congr 1
      ring
    have hgoal : c₂ * c₃ * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * (L : ℝ))) =
        c₂ * (2 : ℝ) ^ (-(β * (L : ℝ))) * (c₃ * (2 : ℝ) ^ (γ * (L : ℝ))) / ε ^ 2 := by
      rw [he, hp, div_eq_mul_inv]
      ring
    rw [hgoal, div_le_iff₀ hε2]
    linarith

/-- From `αL(L+1)/2 ≥ log₂(b/ε)` with `0 < b ≤ 1`: `L ≥ √(2 log₂(1/ε)/α) − ½ − √(2 log₂(1/b)/α)`
(Giles 2015, §2.3: "a value of `L` which is the square root of the usual value"). -/
lemma ml2r_sqrt_le_level {α b ε : ℝ} {L : ℕ} (hα : 0 < α) (hb : 0 < b) (hb1 : b ≤ 1)
    (hε : 0 < ε) (hlev : Real.logb 2 (b / ε) ≤ α * ((L : ℝ) * (L + 1) / 2)) :
    Real.sqrt (2 * Real.logb 2 ε⁻¹ / α) - (1 / 2 + Real.sqrt (2 * Real.logb 2 b⁻¹ / α)) ≤ L := by
  have hy : 0 ≤ 2 * Real.logb 2 b⁻¹ / α := by
    refine div_nonneg (mul_nonneg zero_le_two ?_) hα.le
    exact Real.logb_nonneg one_lt_two (one_le_inv₀ hb |>.2 hb1)
  have hsplit : 2 * Real.logb 2 ε⁻¹ / α =
      2 * Real.logb 2 (b / ε) / α + 2 * Real.logb 2 b⁻¹ / α := by
    have h : ε⁻¹ = b / ε * b⁻¹ := by field_simp
    rw [h, Real.logb_mul (div_pos hb hε).ne' (inv_pos.2 hb).ne', mul_add, add_div]
  have hL0 : (0 : ℝ) ≤ (L : ℝ) + 1 / 2 := by positivity
  have hx : max (2 * Real.logb 2 (b / ε) / α) 0 ≤ ((L : ℝ) + 1 / 2) ^ 2 := by
    refine max_le ?_ (sq_nonneg _)
    rw [div_le_iff₀ hα]
    nlinarith
  have h1 : Real.sqrt (2 * Real.logb 2 ε⁻¹ / α) ≤
      Real.sqrt (max (2 * Real.logb 2 (b / ε) / α) 0) + Real.sqrt (2 * Real.logb 2 b⁻¹ / α) := by
    rw [hsplit]
    calc Real.sqrt (2 * Real.logb 2 (b / ε) / α + 2 * Real.logb 2 b⁻¹ / α)
        ≤ Real.sqrt (max (2 * Real.logb 2 (b / ε) / α) 0 + 2 * Real.logb 2 b⁻¹ / α) :=
          Real.sqrt_le_sqrt (by linarith [le_max_left (2 * Real.logb 2 (b / ε) / α) 0])
      _ ≤ _ := sqrt_add_le_sqrt_add_sqrt (le_max_right _ _) hy
  have h2 : Real.sqrt (max (2 * Real.logb 2 (b / ε) / α) 0) ≤ (L : ℝ) + 1 / 2 :=
    (Real.sqrt_le_left hL0).2 hx
  linarith

end core

section estimator

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω} {Pl : ℕ → Ω₀ → ℝ} {ω : ℕ × ℕ → Ω → Ω₀}

/-- **A lower bound on the cost of ML2R** (Giles 2015, §2.3, p. 12, l. 559–564: "Because the
remaining error is `O(2^{−αL²})`, rather than the usual `O(2^{−αL})`, it is possible to obtain the
usual `O(ε)` weak error with a value of `L` which is the square root of the usual value. … for
`β < γ` the cost is reduced much more to `O(ε⁻² 2^{(γ−β)√(|log₂ ε|/α)})`").

Setting of `ml2r_theorem_lt`: mutually independent inputs `ω (ℓ, n)` of law `ν` on a probability
space `(Ω, μ)`, measurable square-integrable `P_ℓ = Pl ℓ`, the ML2R estimator
`Y = ml2rEstimator α Pl ω L N` (weights `w = ml2rWeight α L`) and a target `EP`.  Let `α > 0`,
`b > 0`, `c₃ ≥ 0`, and assume
* the bias of the extrapolated mean is at least `b 2^{−αL(L+1)/2}` for every `L`:
  `|∑_{ℓ=0}^{L} w_ℓ E[P_ℓ] − EP| ≥ b 2^{−αL(L+1)/2}`;
* `V[P_ℓ − P_{ℓ−1}] ≥ c₂ 2^{−βℓ}` and `C_ℓ ≥ c₃ 2^{γℓ}` for every `ℓ`.
Then for every `ε > 0`, every `L` and every `N_ℓ ≥ 1` with `E[(Y − EP)²] ≤ ε²` satisfy
`αL(L+1)/2 ≥ log₂(b/ε)` (so `L` grows like `√(2 log₂(1/ε)/α)`, not `√(log₂(1/ε)/α)`) and have cost
`∑_{ℓ=0}^{L} N_ℓ C_ℓ ≥ c₂ c₃ ε⁻² 2^{(γ−β)L}`.  The bias hypothesis says that the upper bound
`O(2^{−αL(L+1)/2})` of `ml2r_bias_le` is attained for every `L`; it holds for the concrete
`ml2rInstPl` (`ml2r_instance_hypotheses`), and for the level means of `ml2r_bias_not_attainable`.
-/
theorem ml2r_cost_lower [IsProbabilityMeasure μ] (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    {EP α β γ b c₂ c₃ : ℝ} {C : ℕ → ℝ} (hα : 0 < α) (hb : 0 < b) (hc₃ : 0 ≤ c₃)
    (hbias : ∀ L : ℕ, b * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) ≤
      |∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * ∫ y, Pl ℓ y ∂ν - EP|)
    (hV : ∀ ℓ : ℕ, c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) ≤ variance (levelDiff Pl ℓ) ν)
    (hC : ∀ ℓ : ℕ, c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ)) ≤ C ℓ) :
    ∀ ε : ℝ, 0 < ε → ∀ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) →
      μ[fun x => (ml2rEstimator α Pl ω L N x - EP) ^ 2] ≤ ε ^ 2 →
        Real.logb 2 (b / ε) ≤ α * ((L : ℝ) * (L + 1) / 2) ∧
        c₂ * c₃ * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * (L : ℝ))) ≤
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := by
  intro ε hε L N hN hmse
  rw [ml2rEstimator_mse hω hind hPlm hPl α L hN EP] at hmse
  have hL : L ∈ range (L + 1) := Finset.mem_range.2 (Nat.lt_succ_self L)
  have hsingle := Finset.single_le_sum (f := fun ℓ =>
    (∑ k ∈ Ico ℓ (L + 1), ml2rWeight α L k) ^ 2 * variance (levelDiff Pl ℓ) ν / (N ℓ : ℝ))
    (fun ℓ _ => div_nonneg (mul_nonneg (sq_nonneg _) (variance_nonneg _ _)) (Nat.cast_nonneg _))
    hL
  have hcost := Finset.single_le_sum (f := fun ℓ => (N ℓ : ℝ) * C ℓ)
    (fun ℓ _ => mul_nonneg (Nat.cast_nonneg _)
      ((mul_nonneg hc₃ (Real.rpow_pos_of_pos two_pos _).le).trans (hC ℓ))) hL
  have hw : 1 ≤ ∑ k ∈ Ico L (L + 1), ml2rWeight α L k := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
    exact one_le_ml2rWeight_self hα L
  exact ml2r_lower_core hb hε hc₃ (variance_nonneg _ _) (Nat.cast_pos.2 (hN L)) hw
    (by linarith) (hbias L) (hV L) (hC L) hcost

/-- **The ML2R cost lower bound in terms of `ε`** (Giles 2015, §2.3, p. 12, l. 559–564: "for
`β < γ` the cost is reduced much more to `O(ε⁻² 2^{(γ−β)√(|log₂ ε|/α)})`").  Under the hypotheses
of `ml2r_cost_lower`, with moreover `b ≤ 1`, `β ≤ γ` and `c₂, c₃ > 0`: for every `0 < ε < 1`, every
`L` and `N_ℓ ≥ 1` with `E[(Y − EP)²] ≤ ε²` satisfy `L ≥ √(2 log₂(1/ε)/α) − κ` with
`κ = ½ + √(2 log₂(1/b)/α)`, and their cost is at least
`c₂ c₃ 2^{−(γ−β)κ} · ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}` (for `b = 1`, `κ = ½`).  With the upper bound
`ml2r_theorem_lt`, the exponent `(γ−β)√(2 log₂(1/ε)/α)` is sharp up to an additive constant.
The restriction `ε < 1` only keeps `log₂(1/ε) > 0` under the square root. -/
theorem ml2r_cost_lower_sqrt [IsProbabilityMeasure μ] (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    {EP α β γ b c₂ c₃ : ℝ} {C : ℕ → ℝ} (hα : 0 < α) (hβγ : β ≤ γ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hbias : ∀ L : ℕ, b * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) ≤
      |∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * ∫ y, Pl ℓ y ∂ν - EP|)
    (hV : ∀ ℓ : ℕ, c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) ≤ variance (levelDiff Pl ℓ) ν)
    (hC : ∀ ℓ : ℕ, c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ)) ≤ C ℓ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) →
      μ[fun x => (ml2rEstimator α Pl ω L N x - EP) ^ 2] ≤ ε ^ 2 →
        Real.sqrt (2 * Real.logb 2 ε⁻¹ / α) - (1 / 2 + Real.sqrt (2 * Real.logb 2 b⁻¹ / α)) ≤
          L ∧
        c₂ * c₃ * (2 : ℝ) ^ (-((γ - β) * (1 / 2 + Real.sqrt (2 * Real.logb 2 b⁻¹ / α)))) *
            (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α))) ≤
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := by
  intro ε hε _ L N hN hmse
  obtain ⟨hlev, hcost⟩ :=
    ml2r_cost_lower hω hind hPlm hPl hα hb hc₃.le hbias hV hC ε hε L N hN hmse
  have hL := ml2r_sqrt_le_level hα hb hb1 hε hlev
  refine ⟨hL, le_trans ?_ hcost⟩
  have hδ : 0 ≤ γ - β := by linarith
  have hexp : (2 : ℝ) ^ (-((γ - β) * (1 / 2 + Real.sqrt (2 * Real.logb 2 b⁻¹ / α)))) *
      (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α)) ≤
      (2 : ℝ) ^ ((γ - β) * (L : ℝ)) := by
    rw [← Real.rpow_add two_pos]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    nlinarith [mul_le_mul_of_nonneg_left hL hδ]
  have hc : 0 ≤ c₂ * c₃ * ε ^ (-2 : ℝ) :=
    mul_nonneg (mul_pos hc₂ hc₃).le (Real.rpow_pos_of_pos hε _).le
  calc c₂ * c₃ * (2 : ℝ) ^ (-((γ - β) * (1 / 2 + Real.sqrt (2 * Real.logb 2 b⁻¹ / α)))) *
        (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α)))
      = c₂ * c₃ * ε ^ (-2 : ℝ) *
          ((2 : ℝ) ^ (-((γ - β) * (1 / 2 + Real.sqrt (2 * Real.logb 2 b⁻¹ / α)))) *
            (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α))) := by ring
    _ ≤ c₂ * c₃ * ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp hc
    _ = c₂ * c₃ * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * (L : ℝ))) := by ring

/-- **The printed ML2R cost is not attained** (Giles 2015, §2.3, p. 12, l. 559–564: "while for
`β < γ` the cost is reduced much more to `O(ε⁻² 2^{(γ−β)√(|log₂ ε|/α)})`").  Under the hypotheses
of `ml2r_cost_lower` with `β < γ` and `c₂, c₃ > 0`, there are **no** constant `c` and threshold
`ε₀ > 0` such that for every `0 < ε < ε₀` some `L` and `N_ℓ ≥ 1` reach `E[(Y − EP)²] ≤ ε²` at cost
`∑_{ℓ=0}^{L} N_ℓ C_ℓ ≤ c ε⁻² 2^{(γ−β)√(|log₂ ε|/α)}`.  Indeed for some `c' > 0` every admissible
choice costs at least `c' ε⁻² 2^{(γ−β)√2 √(log₂(1/ε)/α)}` (`ml2r_cost_lower_sqrt`), and
`2^{(γ−β)(√2 − 1)√(log₂(1/ε)/α)} → ∞` as `ε → 0`.  The hypotheses are satisfiable, also together
with those of `ml2r_theorem_lt` (`ml2r_instance_hypotheses`). -/
theorem ml2r_printed_cost_fails [IsProbabilityMeasure μ] (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    {EP α β γ b c₂ c₃ : ℝ} {C : ℕ → ℝ} (hα : 0 < α) (hβγ : β < γ) (hb : 0 < b)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hbias : ∀ L : ℕ, b * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) ≤
      |∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * ∫ y, Pl ℓ y ∂ν - EP|)
    (hV : ∀ ℓ : ℕ, c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) ≤ variance (levelDiff Pl ℓ) ν)
    (hC : ∀ ℓ : ℕ, c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ)) ≤ C ℓ) :
    ¬ ∃ c ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (ml2rEstimator α Pl ω L N x - EP) ^ 2] ≤ ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤
          c * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * Real.sqrt (|Real.logb 2 ε| / α))) := by
  rintro ⟨c, ε₀, hε₀, h⟩
  -- the lower bound with `b' = min b 1 ≤ 1`
  set b' := min b 1 with hb'
  have hb'0 : 0 < b' := lt_min hb one_pos
  have hbias' : ∀ L : ℕ, b' * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) ≤
      |∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * ∫ y, Pl ℓ y ∂ν - EP| := fun L =>
    (mul_le_mul_of_nonneg_right (min_le_left b 1) (Real.rpow_pos_of_pos two_pos _).le).trans
      (hbias L)
  have hlow := ml2r_cost_lower_sqrt hω hind hPlm hPl hα hβγ.le hb'0 (min_le_right b 1) hc₂ hc₃
    hbias' hV hC
  set δ := γ - β with hδdef
  have hδ : 0 < δ := by linarith
  set c' := c₂ * c₃ * (2 : ℝ) ^ (-(δ * (1 / 2 + Real.sqrt (2 * Real.logb 2 b'⁻¹ / α))))
    with hc'def
  have hc' : 0 < c' := mul_pos (mul_pos hc₂ hc₃) (Real.rpow_pos_of_pos two_pos _)
  -- `t = δ(√2 − 1) > 0` and the threshold `S` with `2^{tS} = max 1 (c/c')`
  have hs2 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt zero_le_one one_lt_two
  set t := δ * (Real.sqrt 2 - 1) with htdef
  have ht : 0 < t := mul_pos hδ (by linarith)
  set M := max 1 (c / c') with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  set S := Real.logb 2 M / t with hSdef
  have hS0 : 0 ≤ S := div_nonneg (Real.logb_nonneg one_lt_two hM1) ht.le
  -- a small `ε`
  set ε := min (ε₀ / 2) ((2 : ℝ) ^ (-(α * S ^ 2)) / 2) with hεdef
  have h2S : 0 < (2 : ℝ) ^ (-(α * S ^ 2)) := Real.rpow_pos_of_pos two_pos _
  have h2S1 : (2 : ℝ) ^ (-(α * S ^ 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos one_le_two
      (neg_nonpos.2 (mul_nonneg hα.le (sq_nonneg S)))
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεS : ε < (2 : ℝ) ^ (-(α * S ^ 2)) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hε1 : ε < 1 := lt_of_lt_of_le hεS h2S1
  -- `λ = log₂(1/ε) > αS²`, so `s = √(λ/α) > S`
  set lam := Real.logb 2 ε⁻¹ with hlamdef
  have hlam : α * S ^ 2 < lam := by
    have h1 : Real.logb 2 ε < -(α * S ^ 2) := by
      rw [Real.logb_lt_iff_lt_rpow one_lt_two hε]
      exact hεS
    rw [hlamdef, Real.logb_inv]
    linarith
  have habs : |Real.logb 2 ε| = lam := by
    rw [hlamdef, Real.logb_inv, abs_of_neg (Real.logb_neg one_lt_two hε hε1)]
  set s := Real.sqrt (lam / α) with hsdef
  have hsS : S < s := by
    rw [hsdef, Real.lt_sqrt hS0, lt_div_iff₀ hα]
    linarith
  have hsqrt2 : Real.sqrt (2 * lam / α) = Real.sqrt 2 * s := by
    rw [hsdef, mul_div_assoc, Real.sqrt_mul zero_le_two]
  -- `c < c' 2^{ts}`
  have hcM : c ≤ c' * M := by
    have h1 : c / c' ≤ M := le_max_right _ _
    rw [div_le_iff₀ hc'] at h1
    linarith
  have hMlt : M < (2 : ℝ) ^ (t * s) := by
    have h1 : (2 : ℝ) ^ (t * S) = M := by
      rw [hSdef, mul_div_cancel₀ _ ht.ne', Real.rpow_logb two_pos (by norm_num)
        (by linarith)]
    rw [← h1]
    exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two (mul_lt_mul_of_pos_left hsS ht)
  have hcc : c < c' * (2 : ℝ) ^ (t * s) := lt_of_le_of_lt hcM (mul_lt_mul_of_pos_left hMlt hc')
  -- the contradiction
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hεε₀
  obtain ⟨-, hlow'⟩ := hlow ε hε hε1 L N hN hmse
  rw [habs] at hcost
  rw [hsqrt2] at hlow'
  have hE : 0 < ε ^ (-2 : ℝ) * (2 : ℝ) ^ (δ * s) :=
    mul_pos (Real.rpow_pos_of_pos hε _) (Real.rpow_pos_of_pos two_pos _)
  have hsplit2 : (2 : ℝ) ^ (δ * (Real.sqrt 2 * s)) = (2 : ℝ) ^ (t * s) * (2 : ℝ) ^ (δ * s) := by
    rw [← Real.rpow_add two_pos, htdef]
    congr 1
    ring
  have hlt : c * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ (δ * s)) <
      c' * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ (δ * (Real.sqrt 2 * s))) := by
    rw [hsplit2]
    have h1 := mul_lt_mul_of_pos_right hcc hE
    calc c * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ (δ * s))
        < c' * (2 : ℝ) ^ (t * s) * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ (δ * s)) := h1
      _ = c' * (ε ^ (-2 : ℝ) * ((2 : ℝ) ^ (t * s) * (2 : ℝ) ^ (δ * s))) := by ring
  linarith

end estimator

/-! ### A concrete instance -/

section instance_

/-- **The level approximations of the ML2R lower-bound instance** (Giles 2015, §2.3): for a
standard normal input `z`, `P_ℓ(z) = x_ℓ/(1 + x_ℓ) + s_ℓ z` with the ML2R nodes `x_ℓ = 2^{−αℓ}` and
`s_ℓ = ∑_{j=0}^{ℓ} 2^{−βj/2}`.  So `E[P_ℓ] = x_ℓ/(1 + x_ℓ)` (the weak error, with `E[P] = 0`) and
`P_ℓ − P_{ℓ−1} = (x_ℓ/(1 + x_ℓ) − x_{ℓ−1}/(1 + x_{ℓ−1})) + 2^{−βℓ/2} z` has variance `2^{−βℓ}`. -/
noncomputable def ml2rInstPl (α β : ℝ) (ℓ : ℕ) (z : ℝ) : ℝ :=
  ml2rNode α ℓ / (1 + ml2rNode α ℓ) + (∑ j ∈ range (ℓ + 1), (2 : ℝ) ^ (-(β * (j : ℝ)) / 2)) * z

/-- The level approximations of the lower-bound instance are measurable (Giles 2015, §2.3). -/
lemma measurable_ml2rInstPl (α β : ℝ) (ℓ : ℕ) : Measurable (ml2rInstPl α β ℓ) :=
  measurable_const.add (measurable_const.mul measurable_id)

/-- The level approximations of the lower-bound instance are square integrable under `N(0, 1)`
(Giles 2015, §2.3). -/
lemma memLp_ml2rInstPl (α β : ℝ) (ℓ : ℕ) : MemLp (ml2rInstPl α β ℓ) 2 (gaussianReal 0 1) := by
  have h0 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal' 2 (by norm_num)
  have h : MemLp (fun z : ℝ => (∑ j ∈ range (ℓ + 1), (2 : ℝ) ^ (-(β * (j : ℝ)) / 2)) * id z) 2
      (gaussianReal 0 1) := h0.const_mul _
  have h2 := (memLp_const (μ := gaussianReal 0 1) (p := 2)
    (ml2rNode α ℓ / (1 + ml2rNode α ℓ))).add h
  have e : ml2rInstPl α β ℓ = (fun _ : ℝ => ml2rNode α ℓ / (1 + ml2rNode α ℓ)) +
      fun z : ℝ => (∑ j ∈ range (ℓ + 1), (2 : ℝ) ^ (-(β * (j : ℝ)) / 2)) * id z := by
    funext z
    rw [ml2rInstPl, Pi.add_apply, id]
  rw [e]
  exact h2

/-- The mean of the level-`ℓ` approximation of the lower-bound instance is `x_ℓ/(1 + x_ℓ)`
(Giles 2015, §2.3, p. 11, l. 529–531: the weak error, with `E[P] = 0`). -/
lemma integral_ml2rInstPl (α β : ℝ) (ℓ : ℕ) :
    ∫ z, ml2rInstPl α β ℓ z ∂(gaussianReal 0 1) = ml2rNode α ℓ / (1 + ml2rNode α ℓ) := by
  have hi : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable one_le_two
  rw [show ml2rInstPl α β ℓ = fun z => ml2rNode α ℓ / (1 + ml2rNode α ℓ) +
      (∑ j ∈ range (ℓ + 1), (2 : ℝ) ^ (-(β * (j : ℝ)) / 2)) * z from rfl,
    integral_add (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul,
    integral_id_gaussianReal, probReal_univ, one_smul, mul_zero, add_zero]

/-- Under `N(0, 1)`, `z ↦ a + c z` has variance `c²` (used for the variances `V_ℓ` of the
lower-bound instance, Giles 2015, §2.3). -/
lemma variance_const_add_mul_gaussianReal (a c : ℝ) :
    variance (fun z : ℝ => a + c * z) (gaussianReal 0 1) = c ^ 2 := by
  have hm : AEStronglyMeasurable (fun z : ℝ => c * z) (gaussianReal 0 1) :=
    (measurable_id.const_mul c).aestronglyMeasurable
  rw [variance_const_add hm a]
  calc variance (fun z : ℝ => c * z) (gaussianReal 0 1)
      = variance (fun z : ℝ => c * id z) (gaussianReal 0 1) := rfl
    _ = c ^ 2 * variance id (gaussianReal 0 1) := variance_const_mul c id _
    _ = c ^ 2 := by rw [variance_id_gaussianReal]; push_cast; ring

/-- The level differences of the lower-bound instance have variance `V_ℓ = 2^{−βℓ}` (Giles 2015,
§2.3; the condition `V_ℓ ≤ c₂ 2^{−βℓ}` of Theorem 1, §2.1, p. 6, here with equality). -/
lemma variance_levelDiff_ml2rInstPl (α β : ℝ) (ℓ : ℕ) :
    variance (levelDiff (ml2rInstPl α β) ℓ) (gaussianReal 0 1) =
      (2 : ℝ) ^ (-(β * (ℓ : ℝ))) := by
  have hsq : ∀ j : ℕ, ((2 : ℝ) ^ (-(β * (j : ℝ)) / 2)) ^ 2 = (2 : ℝ) ^ (-(β * (j : ℝ))) :=
    fun j => by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
  cases ℓ with
  | zero =>
    rw [levelDiff_zero]
    have h : ml2rInstPl α β 0 = fun z => ml2rNode α 0 / (1 + ml2rNode α 0) +
        (2 : ℝ) ^ (-(β * ((0 : ℕ) : ℝ)) / 2) * z := by
      funext z
      rw [ml2rInstPl, Finset.sum_range_one]
    rw [h, variance_const_add_mul_gaussianReal, hsq]
  | succ ℓ =>
    rw [levelDiff_succ]
    have h : (fun z => ml2rInstPl α β (ℓ + 1) z - ml2rInstPl α β ℓ z) = fun z =>
        (ml2rNode α (ℓ + 1) / (1 + ml2rNode α (ℓ + 1)) - ml2rNode α ℓ / (1 + ml2rNode α ℓ)) +
          (2 : ℝ) ^ (-(β * ((ℓ + 1 : ℕ) : ℝ)) / 2) * z := by
      funext z
      rw [ml2rInstPl, ml2rInstPl, Finset.sum_range_succ _ (ℓ + 1)]
      ring
    rw [h, variance_const_add_mul_gaussianReal, hsq]

/-- **The ML2R lower-bound instance satisfies all the hypotheses** (Giles 2015, §2.3, pp. 11–12,
l. 529–543: "Assuming that the weak error has a regular expansion
`E[P_ℓ] − E[P] = ∑_{n=1}^{L} a_n 2^{−nαℓ} + O(2^{−αℓL})` … `= O(2^{−αL²})`").  For `α > 0`, any
`β`, the standard normal input law `ν = N(0, 1)` and `P_ℓ = ml2rInstPl α β ℓ`, with `E[P] = 0`:
1. the expansion holds for every `L` with `a_n = (−1)^{n+1}` and the `L`-independent constant
   `K = 1`: `|E[P_ℓ] − E[P] − ∑_{n=1}^{L} a_n 2^{−nαℓ}| ≤ 2^{−αℓL}` for `ℓ ≤ L` (the hypothesis
   `hexp` of `ml2r_theorem_lt`);
2. `V[P_ℓ − P_{ℓ−1}] = 2^{−βℓ}` for every `ℓ` (both `hV` of `ml2r_theorem_lt` with `c₂ = 1` and
   `hV` of `ml2r_cost_lower` with `c₂ = 1`);
3. the ML2R bias is exactly `∑_{ℓ=0}^{L} w_ℓ E[P_ℓ] − E[P] = ∏_{k=0}^{L} x_k/(1 + x_k)`,
   `x_k = 2^{−αk}`;
4. and it lies between `e^{−1/(1−2^{−α})} 2^{−αL(L+1)/2}` and `2^{−αL(L+1)/2}` (the hypothesis
   `hbias` of `ml2r_cost_lower` with `b = e^{−1/(1−2^{−α})} ∈ (0, 1]`): the bias is of exact
   order `2^{−αL(L+1)/2}`, not `O(2^{−αL²})`. -/
theorem ml2r_instance_hypotheses {α : ℝ} (hα : 0 < α) (β : ℝ) :
    (∀ L : ℕ, ∀ ℓ ≤ L, |∫ z, ml2rInstPl α β ℓ z ∂(gaussianReal 0 1) - 0 -
        ∑ n ∈ Icc 1 L, (-1 : ℝ) ^ (n + 1) * ml2rNode α ℓ ^ n| ≤ 1 * ml2rNode α ℓ ^ L) ∧
    (∀ ℓ : ℕ, variance (levelDiff (ml2rInstPl α β) ℓ) (gaussianReal 0 1) =
      (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) ∧
    (∀ L : ℕ, ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ *
        ∫ z, ml2rInstPl α β ℓ z ∂(gaussianReal 0 1) - 0 =
      ∏ k ∈ range (L + 1), ml2rNode α k / (1 + ml2rNode α k)) ∧
    (∀ L : ℕ, Real.exp (-(1 - (2 : ℝ) ^ (-α))⁻¹) * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) ≤
        |∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ *
          ∫ z, ml2rInstPl α β ℓ z ∂(gaussianReal 0 1) - 0| ∧
      |∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ *
          ∫ z, ml2rInstPl α β ℓ z ∂(gaussianReal 0 1) - 0| ≤
        (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2)))) := by
  have hbias : ∀ L : ℕ, ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ *
      ∫ z, ml2rInstPl α β ℓ z ∂(gaussianReal 0 1) - 0 =
        ∏ k ∈ range (L + 1), ml2rNode α k / (1 + ml2rNode α k) := fun L => by
    simp only [integral_ml2rInstPl, sub_zero]
    exact ml2r_sum_weight_mul_div_one_add hα L
  refine ⟨fun L ℓ _ => ?_, variance_levelDiff_ml2rInstPl α β, hbias, fun L => ?_⟩
  · have hx := ml2rNode_pos α ℓ
    have hx1 := ml2rNode_le_one hα ℓ
    rw [integral_ml2rInstPl, sub_zero, div_one_add_sub_sum _ (by linarith) L, abs_div, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (pow_pos hx _),
      abs_of_pos (by linarith : 0 < 1 + ml2rNode α ℓ),
      one_mul, div_le_iff₀ (by linarith), pow_succ]
    have hxL : 0 ≤ ml2rNode α ℓ ^ L := pow_nonneg hx.le L
    nlinarith
  · obtain ⟨h1, h2⟩ := prod_ml2rNode_div_one_add_mem hα L
    have hpos : 0 ≤ ∏ k ∈ range (L + 1), ml2rNode α k / (1 + ml2rNode α k) :=
      Finset.prod_nonneg fun k _ => div_nonneg (ml2rNode_pos α k).le
        (by linarith [ml2rNode_pos α k])
    rw [hbias L, abs_of_nonneg hpos]
    exact ⟨h1, h2⟩

/-- **The cost of ML2R on the instance: matching upper and lower bounds** (Giles 2015, §2.3,
p. 12, l. 559–564: "while for `β < γ` the cost is reduced much more to
`O(ε⁻² 2^{(γ−β)√(|log₂ ε|/α)})`").  Take the instance `P_ℓ = ml2rInstPl α β ℓ` with a standard
normal input, `E[P] = 0`, per-sample cost `C_ℓ = 2^{γℓ}`, the samples the coordinates of
`(ℝ^{ℕ×ℕ}, N(0, 1)^{⊗(ℕ×ℕ)})` (independent, each `N(0, 1)`), and `Y = ml2rEstimator`; let `α > 0`,
`γ > 0`, `β < γ`.  There are `c₄, c₅ > 0` and `κ` such that for every `0 < ε < e⁻¹`:
* (upper bound, from `ml2r_theorem_lt`) some `L` and `N_ℓ ≥ 1` give `E[Y²] < ε²` at cost
  `∑_{ℓ≤L} N_ℓ 2^{γℓ} ≤ c₄ ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}`;
* (lower bound, from `ml2r_cost_lower_sqrt`) every `L` and `N_ℓ ≥ 1` with `E[Y²] ≤ ε²` have
  `L ≥ √(2 log₂(1/ε)/α) − κ` and cost at least `c₅ ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}`.
So on this example the least cost of ML2R for mean square error `ε²` is
`Θ(ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)})`: the corrected exponent `√(2|log₂ ε|/α)` of
`ml2r_theorem_lt` is the right one.  The upper part also certifies that `Y²` is integrable, so the
mean square is not a junk value. -/
theorem ml2r_instance_cost {α β γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hβγ : β < γ) :
    ∃ c₄ c₅ κ : ℝ, 0 < c₄ ∧ 0 < c₅ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      (∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => ml2rEstimator α (ml2rInstPl α β) (fun p x => x p) L N x ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => gaussianReal 0 1) ∧
        ∫ x, ml2rEstimator α (ml2rInstPl α β) (fun p x => x p) L N x ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => gaussianReal 0 1) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (2 : ℝ) ^ (γ * (ℓ : ℝ)) ≤
          c₄ * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α)))) ∧
      ∀ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) →
        ∫ x, ml2rEstimator α (ml2rInstPl α β) (fun p x => x p) L N x ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => gaussianReal 0 1) ≤ ε ^ 2 →
        Real.sqrt (2 * Real.logb 2 ε⁻¹ / α) - κ ≤ L ∧
        c₅ * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α))) ≤
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (2 : ℝ) ^ (γ * (ℓ : ℝ)) := by
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs (gaussianReal 0 1)
  obtain ⟨hexp, hvar, -, hbias⟩ := ml2r_instance_hypotheses hα β
  have hr1 : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hb : 0 < Real.exp (-(1 - (2 : ℝ) ^ (-α))⁻¹) := Real.exp_pos _
  have hb1 : Real.exp (-(1 - (2 : ℝ) ^ (-α))⁻¹) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (inv_nonneg.2 (by linarith)))
  obtain ⟨c₄, hc₄, hup⟩ := ml2r_theorem_lt hω hind (measurable_ml2rInstPl α β)
    (memLp_ml2rInstPl α β) (EP := 0) (K := 1) (c₂ := 1) (c₃ := 1)
    (a := fun n => (-1 : ℝ) ^ (n + 1)) (C := fun ℓ => (2 : ℝ) ^ (γ * (ℓ : ℝ))) hα hγ hβγ
    one_pos one_pos hexp (fun ℓ => by rw [hvar ℓ, one_mul]) (fun ℓ => by rw [one_mul])
  have hlow := ml2r_cost_lower_sqrt hω hind (measurable_ml2rInstPl α β) (memLp_ml2rInstPl α β)
    (EP := 0) (c₂ := 1) (c₃ := 1) (C := fun ℓ => (2 : ℝ) ^ (γ * (ℓ : ℝ))) hα hβγ.le hb hb1
    one_pos one_pos (fun L => (hbias L).1) (fun ℓ => by rw [hvar ℓ, one_mul])
    (fun ℓ => by rw [one_mul])
  refine ⟨c₄, 1 * 1 * (2 : ℝ) ^ (-((γ - β) * (1 / 2 + Real.sqrt (2 * Real.logb 2
      (Real.exp (-(1 - (2 : ℝ) ^ (-α))⁻¹))⁻¹ / α)))), 1 / 2 + Real.sqrt (2 * Real.logb 2
      (Real.exp (-(1 - (2 : ℝ) ^ (-α))⁻¹))⁻¹ / α), hc₄,
    mul_pos (mul_pos one_pos one_pos) (Real.rpow_pos_of_pos two_pos _), fun ε hε hε1 => ?_⟩
  refine ⟨?_, fun L N hN hmse => ?_⟩
  · obtain ⟨L, N, hN, hmse, hcost⟩ := hup ε hε hε1
    have hY : MemLp (ml2rEstimator α (ml2rInstPl α β) (fun p x => x p) L N) 2
        (Measure.infinitePi fun _ : ℕ × ℕ => gaussianReal 0 1) :=
      memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω
        (fun ℓ => (memLp_levelDiff (memLp_ml2rInstPl α β) ℓ).const_mul _) ℓ (N ℓ)
    refine ⟨L, N, hN, hY.integrable_sq, ?_, hcost⟩
    simpa only [sub_zero] using hmse
  · have hmse' : ∫ x, (ml2rEstimator α (ml2rInstPl α β) (fun p x => x p) L N x - 0) ^ 2
        ∂(Measure.infinitePi fun _ : ℕ × ℕ => gaussianReal 0 1) ≤ ε ^ 2 := by
      simpa only [sub_zero] using hmse
    obtain ⟨hL, hcost⟩ := hlow ε hε (eps_lt_one hε1) L N hN hmse'
    exact ⟨hL, hcost⟩

/-- **The printed ML2R cost is false for the instance** (Giles 2015, §2.3, p. 12, l. 559–564:
"while for `β < γ` the cost is reduced much more to `O(ε⁻² 2^{(γ−β)√(|log₂ ε|/α)})`").  For the
example of `ml2r_instance_cost` (`P_ℓ = ml2rInstPl α β ℓ`, standard normal inputs, `E[P] = 0`,
`C_ℓ = 2^{γℓ}`), which satisfies the paper's expansion with an `L`-independent constant
(`ml2r_instance_hypotheses`), and any `α > 0`, `β < γ`: there are no `c` and `ε₀ > 0` such that for
every `0 < ε < ε₀` some `L` and `N_ℓ ≥ 1` reach `E[(Y − E[P])²] ≤ ε²` at cost
`∑_{ℓ≤L} N_ℓ C_ℓ ≤ c ε⁻² 2^{(γ−β)√(|log₂ ε|/α)}`. -/
theorem ml2r_instance_printed_cost_false {α β γ : ℝ} (hα : 0 < α) (hβγ : β < γ) :
    ¬ ∃ c ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        ∫ x, ml2rEstimator α (ml2rInstPl α β) (fun p x => x p) L N x ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => gaussianReal 0 1) ≤ ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (2 : ℝ) ^ (γ * (ℓ : ℝ)) ≤
          c * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * Real.sqrt (|Real.logb 2 ε| / α))) := by
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs (gaussianReal 0 1)
  obtain ⟨-, hvar, -, hbias⟩ := ml2r_instance_hypotheses hα β
  have hfail := ml2r_printed_cost_fails hω hind (measurable_ml2rInstPl α β)
    (memLp_ml2rInstPl α β) (EP := 0) (c₂ := 1) (c₃ := 1)
    (C := fun ℓ => (2 : ℝ) ^ (γ * (ℓ : ℝ))) hα hβγ (Real.exp_pos _) one_pos one_pos
    (fun L => (hbias L).1) (fun ℓ => by rw [hvar ℓ, one_mul]) (fun ℓ => by rw [one_mul])
  rintro ⟨c, ε₀, hε₀, h⟩
  refine hfail ⟨c, ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hεε₀
  exact ⟨L, N, hN, by simpa only [sub_zero] using hmse, hcost⟩

end instance_

end MLMC
