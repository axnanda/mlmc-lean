import MlmcLean.SampleMean
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Richardson extrapolation and multilevel Richardson–Romberg extrapolation (Giles 2015, §2.3)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.3
(pp. 11–12 of the author's version), presenting the ML2R estimator of Lemaire and Pagès (2013).

* **Richardson extrapolation.** "Given a numerical approximation `P_h` … which leads to an error
  `P_h − P = a h^α + O(h^{2α})` … the extrapolated value `P̃ = (2^α P_h − P_{2h})/(2^α − 1)`
  satisfies `P̃ − P = O(h^{2α})`" (`richardson_extrapolation`).
* **The ML2R weights.**  "They first determine the unique set of weights `w_ℓ`, `ℓ = 0, …, L`,
  such that `∑ w_ℓ = 1`, `∑ w_ℓ 2^{−nαℓ} = 1`, `n = 1, …, L`."  The second condition must read
  `= 0` (with `= 1` the only solution is `w = e₀`, no extrapolation).  With `= 0` the weights exist,
  are unique, and are the values at `0` of the Lagrange basis polynomials of the nodes
  `x_ℓ = 2^{−αℓ}`: `w_ℓ = ∏_{k ≠ ℓ} x_k/(x_k − x_ℓ)` (`ml2r_weights`).
* **The bias.**  "so that `(∑ w_ℓ E[P_ℓ]) − E[P] = ∑ w_ℓ (E[P_ℓ] − E[P]) = O(2^{−αL²})`."  If the
  weak error has an expansion `E[P_ℓ] − E[P] = ∑_{n=1}^{L+1} a_n 2^{−nαℓ}` on the levels used, the
  bias is exactly `(−1)^L a_{L+1} 2^{−αL(L+1)/2}` (`ml2r_moment_succ`, `ml2r_bias`): of order
  `2^{−αL(L+1)/2}`, the square root of the printed `2^{−αL²}` up to a factor `2^{−αL/2}`.
* **The estimator.**  "Next, they re-arrange terms to give `∑ w_ℓ E[P_ℓ] = ∑ v_ℓ E[P_ℓ − P_{ℓ−1}]`
  where … `v_ℓ = ∑_{ℓ'=ℓ}^{L} w_ℓ'`" (`ml2r_rearrange`); the estimator
  `Y = ∑_ℓ N_ℓ⁻¹ v_ℓ ∑_n (P_ℓ^{(ℓ,n)} − P_{ℓ−1}^{(ℓ,n)})` built from independent samples has mean
  `∑ w_ℓ E[P_ℓ]` and variance `∑ v_ℓ² V_ℓ / N_ℓ` (`ml2r_estimator_mean_variance`).
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Asymptotics

namespace MLMC

/-! ### Richardson extrapolation -/

/-- **Richardson extrapolation** (Giles 2015, §2.3, p. 11): "Given a numerical approximation `P_h`
based on a discretisation parameter `h` which leads to an error `P_h − P = a h^α + O(h^{2α})`, it
follows that `P_{2h} − P = a (2h)^α + O(h^{2α})`, and hence the extrapolated value
`P̃ = 2^α/(2^α − 1) P_h − 1/(2^α − 1) P_{2h}` satisfies `P̃ − P = O(h^{2α})`."  Here `F h = P_h`,
and `O(·)` is taken as `h → 0⁺`. -/
theorem richardson_extrapolation {F : ℝ → ℝ} {P a α : ℝ} (hα : 0 < α)
    (hF : (fun h => F h - P - a * h ^ α) =O[𝓝[>] 0] fun h => h ^ (2 * α)) :
    (fun h => (2 ^ α * F h - F (2 * h)) / (2 ^ α - 1) - P) =O[𝓝[>] 0] fun h => h ^ (2 * α) := by
  have h2α : (2 : ℝ) ^ α - 1 ≠ 0 := (sub_pos.2 (Real.one_lt_rpow one_lt_two hα)).ne'
  have hc : ((2 : ℝ) ^ α - 1)⁻¹ * ((2 : ℝ) ^ α - 1) = 1 := inv_mul_cancel₀ h2α
  -- `h ↦ 2h` maps `𝓝[>] 0` to itself
  have htend : Tendsto (fun h : ℝ => 2 * h) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun h hh => ?_⟩
    · have h0 : Tendsto (fun h : ℝ => 2 * h) (𝓝 0) (𝓝 (2 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h0
      exact tendsto_nhdsWithin_of_tendsto_nhds h0
    · exact Set.mem_Ioi.2 (mul_pos two_pos (Set.mem_Ioi.1 hh))
  -- the remainder at `2h` is still `O(h^{2α})`
  have hR2 : (fun h => F (2 * h) - P - a * (2 * h) ^ α) =O[𝓝[>] 0] fun h => h ^ (2 * α) := by
    have h1 : (fun h => F (2 * h) - P - a * (2 * h) ^ α) =O[𝓝[>] 0]
        fun h => (2 * h) ^ (2 * α) := hF.comp_tendsto htend
    have e : (fun h : ℝ => (2 : ℝ) ^ (2 * α) * h ^ (2 * α)) =ᶠ[𝓝[>] 0]
        fun h => (2 * h) ^ (2 * α) :=
      eventually_nhdsWithin_of_forall fun h hh =>
        (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Set.mem_Ioi.1 hh).le).symm
    exact h1.trans ((isBigO_const_mul_self _ _ _).congr' e EventuallyEq.rfl)
  -- for `h > 0` the extrapolation error is `(2^α R(h) − R(2h))/(2^α − 1)`
  have key : ∀ h : ℝ, 0 < h → ((2 : ℝ) ^ α - 1)⁻¹ * ((2 : ℝ) ^ α * (F h - P - a * h ^ α) -
      (F (2 * h) - P - a * (2 * h) ^ α)) = (2 ^ α * F h - F (2 * h)) / (2 ^ α - 1) - P := by
    intro h hh
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hh.le]
    linear_combination -P * hc
  have heq : (fun h => ((2 : ℝ) ^ α - 1)⁻¹ * ((2 : ℝ) ^ α * (F h - P - a * h ^ α) -
      (F (2 * h) - P - a * (2 * h) ^ α))) =ᶠ[𝓝[>] 0]
      fun h => (2 ^ α * F h - F (2 * h)) / (2 ^ α - 1) - P :=
    eventually_nhdsWithin_of_forall fun h hh => key h (Set.mem_Ioi.1 hh)
  exact (((hF.const_mul_left ((2 : ℝ) ^ α)).sub hR2).const_mul_left
    ((2 : ℝ) ^ α - 1)⁻¹).congr' heq EventuallyEq.rfl

/-! ### The weights of multilevel Richardson–Romberg extrapolation -/

/-- The nodes `x_ℓ = 2^{−αℓ}` of multilevel Richardson–Romberg extrapolation (Giles 2015, §2.3). -/
noncomputable def ml2rNode (α : ℝ) (ℓ : ℕ) : ℝ := (2 : ℝ) ^ (-(α * ℓ))

/-- The ML2R weights (Giles 2015, §2.3, p. 11): `w_ℓ = ∏_{k ≤ L, k ≠ ℓ} x_k/(x_k − x_ℓ)` with
`x_k = 2^{−αk}`, the value at `0` of the Lagrange basis polynomial of the node `x_ℓ`. -/
noncomputable def ml2rWeight (α : ℝ) (L ℓ : ℕ) : ℝ :=
  ∏ k ∈ (range (L + 1)).erase ℓ, ml2rNode α k / (ml2rNode α k - ml2rNode α ℓ)

lemma ml2rNode_eq (α : ℝ) (k : ℕ) : ml2rNode α k = ((2 : ℝ) ^ (-α)) ^ k := by
  rw [ml2rNode, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), neg_mul]

lemma ml2rNode_injective {α : ℝ} (hα : 0 < α) : Function.Injective (ml2rNode α) := by
  have hr0 : 0 < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos two_pos _
  have hr1 : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  intro i j hij
  rw [ml2rNode_eq, ml2rNode_eq] at hij
  exact pow_right_injective₀ hr0 hr1.ne hij

-- the ML2R weight is the value at `0` of the Lagrange basis polynomial
lemma ml2rWeight_eq_eval_basis (α : ℝ) (L ℓ : ℕ) :
    ml2rWeight α L ℓ = (Lagrange.basis (range (L + 1)) (ml2rNode α) ℓ).eval 0 := by
  rw [ml2rWeight, Lagrange.basis, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, div_eq_mul_inv, ← neg_sub (ml2rNode α ℓ) (ml2rNode α k),
    inv_neg]
  ring

-- evaluation at `0` of a polynomial of degree `≤ L` from its values at the nodes
lemma ml2r_sum_eval {α : ℝ} (hα : 0 < α) (L : ℕ) {f : Polynomial ℝ}
    (hf : f.degree < ((L + 1 : ℕ) : WithBot ℕ)) :
    ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * f.eval (ml2rNode α ℓ) = f.eval 0 := by
  have hinj : Set.InjOn (ml2rNode α) (range (L + 1)) :=
    (ml2rNode_injective hα).injOn
  have h := Lagrange.eq_interpolate (f := f) hinj (by rwa [card_range])
  conv_rhs => rw [h]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, ml2rWeight_eq_eval_basis, mul_comm]

/-- **The ML2R weights** (Giles 2015, §2.3, p. 11): Lemaire and Pagès "first determine the unique
set of weights `w_ℓ`, `ℓ = 0, 1, …, L`, such that `∑_{ℓ=0}^{L} w_ℓ = 1`,
`∑_{ℓ=0}^{L} w_ℓ 2^{−nαℓ} = 1`, `n = 1, …, L`".  The printed right-hand side `1` must be `0`
(otherwise the only solution is `w = (1, 0, …, 0)`); with `0`, for every `α > 0` the weights
`ml2rWeight α L` satisfy `∑_ℓ w_ℓ (2^{−αℓ})^n = [n = 0]` for `0 ≤ n ≤ L`, and they are the only
weights on `ℓ = 0, …, L` that do. -/
theorem ml2r_weights {α : ℝ} (hα : 0 < α) (L : ℕ) :
    (∀ n ≤ L, ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * ml2rNode α ℓ ^ n =
      if n = 0 then 1 else 0) ∧
    ∀ w : ℕ → ℝ, (∀ n ≤ L, ∑ ℓ ∈ range (L + 1), w ℓ * ml2rNode α ℓ ^ n =
        if n = 0 then 1 else 0) →
      ∀ ℓ ∈ range (L + 1), w ℓ = ml2rWeight α L ℓ := by
  have hinj : Set.InjOn (ml2rNode α) (range (L + 1)) := (ml2rNode_injective hα).injOn
  refine ⟨fun n hn => ?_, fun w hw k hk => ?_⟩
  · -- exactness on the monomial `X^n`, `n ≤ L`
    have hdeg : (Polynomial.X ^ n : Polynomial ℝ).degree < ((L + 1 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_X_pow]
      exact Nat.cast_lt.2 (Nat.lt_succ_of_le hn)
    have h := ml2r_sum_eval hα L hdeg
    simp only [Polynomial.eval_pow, Polynomial.eval_X] at h
    rw [h, zero_pow_eq]
  · -- uniqueness: test the moment conditions on the Lagrange basis polynomial of the node `k`
    set p := Lagrange.basis (range (L + 1)) (ml2rNode α) k with hp
    have hdeg : p.natDegree < L + 1 := by
      rw [hp, Lagrange.natDegree_basis hinj hk, card_range]
      omega
    have h1 : ∑ ℓ ∈ range (L + 1), w ℓ * p.eval (ml2rNode α ℓ) = w k := by
      rw [Finset.sum_eq_single k]
      · rw [hp, Lagrange.eval_basis_self hinj hk, mul_one]
      · intro ℓ hℓ hne
        rw [hp, Lagrange.eval_basis_of_ne (Ne.symm hne) hℓ, mul_zero]
      · intro h
        exact absurd hk h
    have e : ∀ ℓ, w ℓ * p.eval (ml2rNode α ℓ) =
        ∑ i ∈ range (L + 1), p.coeff i * (w ℓ * ml2rNode α ℓ ^ i) := fun ℓ => by
      rw [Polynomial.eval_eq_sum_range' hdeg, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ ℓ ∈ range (L + 1), w ℓ * p.eval (ml2rNode α ℓ) = p.eval 0 := by
      rw [Finset.sum_congr rfl fun ℓ _ => e ℓ, Finset.sum_comm]
      have e2 : ∀ i ∈ range (L + 1), ∑ ℓ ∈ range (L + 1), p.coeff i * (w ℓ * ml2rNode α ℓ ^ i) =
          p.coeff i * if i = 0 then 1 else 0 := fun i hi => by
        rw [← Finset.mul_sum, hw i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
      rw [Finset.sum_congr rfl e2, Finset.sum_eq_single 0]
      · rw [if_pos rfl, mul_one, Polynomial.coeff_zero_eq_eval_zero]
      · intro i _ hi
        rw [if_neg hi, mul_zero]
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.succ_pos L)) h
    rw [← h1, h2, hp, ← ml2rWeight_eq_eval_basis]

/-- **The first moment that the ML2R weights do not cancel** (Giles 2015, §2.3, p. 12): with the
nodes `x_ℓ = 2^{−αℓ}`, `∑_{ℓ=0}^{L} w_ℓ x_ℓ^{L+1} = (−1)^L ∏_{k=0}^{L} x_k`.  This is the factor by
which the first uncancelled term of the weak-error expansion enters the ML2R bias. -/
theorem ml2r_moment_succ {α : ℝ} (hα : 0 < α) (L : ℕ) :
    ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * ml2rNode α ℓ ^ (L + 1) =
      (-1) ^ L * ∏ k ∈ range (L + 1), ml2rNode α k := by
  -- `X^{L+1} − ∏_k (X − x_k)` has degree `≤ L`, value `x_ℓ^{L+1}` at the nodes and
  -- `(−1)^L ∏_k x_k` at `0`
  have hX : (Polynomial.X ^ (L + 1) : Polynomial ℝ).degree = ((L + 1 : ℕ) : WithBot ℕ) :=
    Polynomial.degree_X_pow _
  have hN : (Lagrange.nodal (range (L + 1)) (ml2rNode α)).degree = ((L + 1 : ℕ) : WithBot ℕ) := by
    rw [Lagrange.degree_nodal, card_range]
  have hdeg : (Polynomial.X ^ (L + 1) - Lagrange.nodal (range (L + 1)) (ml2rNode α)).degree <
      ((L + 1 : ℕ) : WithBot ℕ) := by
    rw [← hX]
    exact Polynomial.degree_sub_lt_left (hX.trans hN.symm)
      (pow_ne_zero _ Polynomial.X_ne_zero)
      (by rw [Polynomial.leadingCoeff_X_pow, Lagrange.nodal_monic.leadingCoeff])
  have h := ml2r_sum_eval hα L hdeg
  have hnode : ∀ ℓ ∈ range (L + 1),
      ml2rWeight α L ℓ * (Polynomial.X ^ (L + 1) -
        Lagrange.nodal (range (L + 1)) (ml2rNode α)).eval (ml2rNode α ℓ) =
      ml2rWeight α L ℓ * ml2rNode α ℓ ^ (L + 1) := fun ℓ hℓ => by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Lagrange.eval_nodal_at_node hℓ, sub_zero]
  rw [Finset.sum_congr rfl hnode] at h
  rw [h, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Lagrange.eval_nodal]
  simp only [zero_sub, Finset.prod_neg, card_range]
  rw [zero_pow (by omega : L + 1 ≠ 0), pow_succ]
  ring

lemma prod_ml2rNode (α : ℝ) (L : ℕ) :
    ∏ k ∈ range (L + 1), ml2rNode α k = (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) := by
  induction L with
  | zero => simp [ml2rNode]
  | succ L ih =>
    rw [Finset.prod_range_succ, ih, ml2rNode, ← Real.rpow_add two_pos]
    congr 1
    push_cast
    ring

/-- **The ML2R bias, remainder form** (Giles 2015, §2.3, pp. 11–12): "Assuming that the weak error
has a regular expansion `E[P_ℓ] − E[P] = ∑_{n=1}^{L} a_n 2^{−nαℓ} + O(2^{−αℓL})`", the weights give
"`(∑_{ℓ=0}^{L} w_ℓ E[P_ℓ]) − E[P] = ∑_{ℓ=0}^{L} w_ℓ (E[P_ℓ] − E[P])`".  If on the levels
`ℓ = 0, …, L` the weak error is `E[P_ℓ] − E[P] = ∑_{n=1}^{L} a_n 2^{−nαℓ} + R_ℓ`, the weights
cancel the whole expansion and the bias of the extrapolated mean is exactly
`∑_{ℓ=0}^{L} w_ℓ R_ℓ`.  Here `EPl ℓ = E[P_ℓ]` and `EP = E[P]`. -/
theorem ml2r_bias_eq {α : ℝ} (hα : 0 < α) (L : ℕ) (EPl : ℕ → ℝ) (EP : ℝ) (a R : ℕ → ℝ)
    (hexp : ∀ ℓ ∈ range (L + 1),
      EPl ℓ - EP = ∑ n ∈ Icc 1 L, a n * ml2rNode α ℓ ^ n + R ℓ) :
    ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * EPl ℓ - EP =
      ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * R ℓ := by
  obtain ⟨hmom, -⟩ := ml2r_weights hα L
  have hsum1 : ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ = 1 := by
    have h := hmom 0 (Nat.zero_le L)
    simpa using h
  have hzero : ∀ n ∈ Icc 1 L,
      a n * ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * ml2rNode α ℓ ^ n = 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [hmom n hn.2, if_neg (by omega), mul_zero]
  calc ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * EPl ℓ - EP
      = ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * (EPl ℓ - EP) := by
        rw [Finset.sum_congr rfl fun ℓ _ => mul_sub (ml2rWeight α L ℓ) (EPl ℓ) EP,
          Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul]
    _ = ∑ ℓ ∈ range (L + 1), (∑ n ∈ Icc 1 L, a n * (ml2rWeight α L ℓ * ml2rNode α ℓ ^ n) +
          ml2rWeight α L ℓ * R ℓ) := by
        refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        rw [hexp ℓ hℓ, mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun n _ => by ring
    _ = ∑ n ∈ Icc 1 L, a n * ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * ml2rNode α ℓ ^ n +
          ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * R ℓ := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun n _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * R ℓ := by
        rw [Finset.sum_eq_zero hzero, zero_add]

/-- **The ML2R bias** (Giles 2015, §2.3, p. 12): "`(∑_{ℓ=0}^{L} w_ℓ E[P_ℓ]) − E[P] =
∑_{ℓ=0}^{L} w_ℓ (E[P_ℓ] − E[P]) = O(2^{−αL²})`."  If on the levels `ℓ = 0, …, L` the weak error has
the expansion `E[P_ℓ] − E[P] = ∑_{n=1}^{L+1} a_n 2^{−nαℓ}`, the bias of the extrapolated mean is
exactly `(−1)^L a_{L+1} 2^{−αL(L+1)/2}`: the terms `n ≤ L` cancel and the first remaining term is of
order `2^{−αL(L+1)/2}` (the printed `2^{−αL²}` overstates the rate for `L ≥ 2`).  Here
`EPl ℓ = E[P_ℓ]` and `EP = E[P]`. -/
theorem ml2r_bias {α : ℝ} (hα : 0 < α) (L : ℕ) (EPl : ℕ → ℝ) (EP : ℝ) (a : ℕ → ℝ)
    (hexp : ∀ ℓ ∈ range (L + 1),
      EPl ℓ - EP = ∑ n ∈ Icc 1 (L + 1), a n * ml2rNode α ℓ ^ n) :
    ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * EPl ℓ - EP =
      (-1) ^ L * a (L + 1) * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) := by
  have hexp' : ∀ ℓ ∈ range (L + 1), EPl ℓ - EP =
      ∑ n ∈ Icc 1 L, a n * ml2rNode α ℓ ^ n + a (L + 1) * ml2rNode α ℓ ^ (L + 1) :=
    fun ℓ hℓ => by rw [hexp ℓ hℓ, Finset.sum_Icc_succ_top (by omega : 1 ≤ L + 1)]
  have h : ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * (a (L + 1) * ml2rNode α ℓ ^ (L + 1)) =
      a (L + 1) * ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * ml2rNode α ℓ ^ (L + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  rw [ml2r_bias_eq hα L EPl EP a _ hexp', h, ml2r_moment_succ hα L, prod_ml2rNode]
  ring

/-! ### The ML2R estimator -/

section estimator

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω}

/-- **Re-arranging the extrapolated mean as a multilevel sum** (Giles 2015, §2.3, p. 12): "they
re-arrange terms to give `∑_{ℓ=0}^{L} w_ℓ E[P_ℓ] = ∑_{ℓ=0}^{L} v_ℓ E[P_ℓ − P_{ℓ−1}]` where as usual
`P_{−1} ≡ 0`, and the coefficients `v_ℓ` are defined by `w_ℓ = v_ℓ − v_{ℓ+1}`, with
`v_{L+1} ≡ 0`, and hence `v_ℓ = ∑_{ℓ'=ℓ}^{L} w_ℓ'`."  This holds for any weights `w`. -/
theorem ml2r_rearrange {Pl : ℕ → Ω₀ → ℝ} (hPl : ∀ ℓ, Integrable (Pl ℓ) ν) (w : ℕ → ℝ) (L : ℕ) :
    ∑ ℓ ∈ range (L + 1), w ℓ * ∫ y, Pl ℓ y ∂ν =
      ∑ ℓ ∈ range (L + 1), (∑ k ∈ Ico ℓ (L + 1), w k) * ∫ y, levelDiff Pl ℓ y ∂ν := by
  have htel : ∀ ℓ, ∫ y, Pl ℓ y ∂ν = ∑ j ∈ range (ℓ + 1), ∫ y, levelDiff Pl j y ∂ν := fun ℓ =>
    (sum_integral_levelDiff hPl ℓ).symm
  have h := Finset.sum_Ico_Ico_comm 0 (L + 1) fun i j => w j * ∫ y, levelDiff Pl i y ∂ν
  simp only [← Finset.range_eq_Ico] at h
  simp only [htel, Finset.mul_sum]
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm

/-- **The ML2R estimator** (Giles 2015, §2.3, p. 12): "This leads to their Multilevel
Richardson–Romberg extrapolation estimator, `Y = ∑_{ℓ=0}^{L} Y_ℓ`,
`Y_ℓ = N_ℓ⁻¹ v_ℓ ∑_n (P_ℓ^{(ℓ,n)} − P_{ℓ−1}^{(ℓ,n)})`."  With `v_ℓ = ∑_{ℓ'=ℓ}^{L} w_ℓ'`, `N_ℓ ≥ 1`
and mutually independent inputs `ω^{(ℓ,n)}` of law `ν`, `E[Y] = ∑_ℓ w_ℓ E[P_ℓ]` (the extrapolated
mean) and `V[Y] = ∑_ℓ v_ℓ² V_ℓ / N_ℓ` with `V_ℓ = V[P_ℓ − P_{ℓ−1}]`, for any weights `w`. -/
theorem ml2r_estimator_mean_variance [IsProbabilityMeasure μ] {Pl : ℕ → Ω₀ → ℝ}
    {ω : ℕ × ℕ → Ω → Ω₀} (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν) (w : ℕ → ℝ) (L : ℕ)
    {N : ℕ → ℕ} (hN : ∀ ℓ, 0 < N ℓ) :
    μ[fun x => ∑ ℓ ∈ range (L + 1), blockMean (fun ℓ y => (∑ k ∈ Ico ℓ (L + 1), w k) *
        levelDiff Pl ℓ y) ω ℓ (N ℓ) x] = ∑ ℓ ∈ range (L + 1), w ℓ * ∫ y, Pl ℓ y ∂ν ∧
      variance (fun x => ∑ ℓ ∈ range (L + 1), blockMean (fun ℓ y => (∑ k ∈ Ico ℓ (L + 1), w k) *
        levelDiff Pl ℓ y) ω ℓ (N ℓ) x) μ =
        ∑ ℓ ∈ range (L + 1),
          (∑ k ∈ Ico ℓ (L + 1), w k) ^ 2 * variance (levelDiff Pl ℓ) ν / N ℓ := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  set f : ℕ → Ω₀ → ℝ := fun ℓ y => (∑ k ∈ Ico ℓ (L + 1), w k) * levelDiff Pl ℓ y with hf
  have hPl1 : ∀ ℓ, Integrable (Pl ℓ) ν := fun ℓ => (hPl ℓ).integrable one_le_two
  have hfm : ∀ ℓ, Measurable (f ℓ) := fun ℓ => (measurable_levelDiff hPlm ℓ).const_mul _
  have hfL : ∀ ℓ, MemLp (f ℓ) 2 ν := fun ℓ => (memLp_levelDiff hPl ℓ).const_mul _
  have hf1 : ∀ ℓ, Integrable (f ℓ) ν := fun ℓ => (hfL ℓ).integrable one_le_two
  constructor
  · rw [integral_finsetSum _ fun ℓ _ => (memLp_blockMean hω hfL ℓ (N ℓ)).integrable one_le_two,
      Finset.sum_congr rfl fun ℓ _ => integral_blockMean hω hf1 ℓ (hN ℓ), ml2r_rearrange hPl1]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [hf, integral_const_mul]
  · have hfun : (fun x => ∑ ℓ ∈ range (L + 1), blockMean f ω ℓ (N ℓ) x) =
        ∑ ℓ ∈ range (L + 1), blockMean f ω ℓ (N ℓ) := by
      funext x
      simp only [Finset.sum_apply]
    rw [hfun, IndepFun.variance_sum (fun ℓ _ => memLp_blockMean hω hfL ℓ (N ℓ))
      (fun i _ j _ hij => indepFun_blockMean (fun p => (hω p).measurable) hind hfm hij _ _)]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [variance_blockMean hω hind hfm hfL ℓ (hN ℓ), hf, variance_const_mul]

end estimator

end MLMC
