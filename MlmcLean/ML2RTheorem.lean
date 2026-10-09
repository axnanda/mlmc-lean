import MlmcLean.ML2RComplexity
import MlmcLean.Estimator

/-!
# The ML2R theorem: bias and complexity of the ML2R estimator (Giles 2015, §2.3)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.3
(pp. 11–12 of the author's version), presenting the multilevel Richardson–Romberg (ML2R)
estimator of Lemaire and Pagès (2013):

"Assuming that the weak error has a regular expansion
`E[P_ℓ] − E[P] = ∑_{n=1}^{L} a_n 2^{−nαℓ} + O(2^{−αℓL})`, they first determine the unique set of
weights `w_ℓ` … so that `(∑_{ℓ=0}^{L} w_ℓ E[P_ℓ]) − E[P] = ∑_{ℓ=0}^{L} w_ℓ (E[P_ℓ] − E[P]) =
O(2^{−αL²})`. … Hence, in the case `β = γ` they prove that the overall cost is reduced to
`O(ε⁻² |log ε|)`, while for `β < γ` the cost is reduced much more to
`O(ε⁻² 2^{(γ−β)√(|log₂ ε|/α)})`."

`MlmcLean/Richardson.lean` computes the bias for an exact expansion (`ml2r_bias`) and the mean and
variance of the ML2R estimator (`ml2r_estimator_mean_variance`); `MlmcLean/ML2RComplexity.lean`
proves the complexity for an *assumed* remaining-error bound `c₁ 2^{−αL(L+1)/2}`
(`ml2r_complexity_eq`, `ml2r_complexity_lt`).  This file derives that bound from the expansion
hypothesis and states the complexity for the mean square error of the estimator itself.

* **Sharp weight bound** (`abs_ml2rWeight_le_sharp`): with `r = 2^{−α}` and `B = e^{r/(1−r)²}`,
  `|w_ℓ| ≤ B² r^{(L−ℓ)(L−ℓ+1)/2}` for `ℓ ≤ L`.
* **The bias from the expansion** (`ml2r_bias_le`): if the remainder of the expansion is at most
  `K 2^{−αℓL}` on the levels `ℓ ≤ L`, the bias is at most `ml2rBiasConst α · K · 2^{−αL(L+1)/2}`,
  with a constant depending only on `α`.  The rate is `2^{−αL(L+1)/2}`, not the printed
  `2^{−αL²}`, and cannot be improved (`ml2r_bias`).
* **The ML2R theorem** (`ml2r_theorem_eq`, `ml2r_theorem_lt`): if the `O(2^{−αℓL})` of the
  expansion holds with a constant independent of `L` (implicit in the paper), the estimator
  `ml2rEstimator`, built from independent samples, reaches mean square error
  `E[(Y − E[P])²] < ε²` at cost `O(ε⁻² |log ε|)` if `β = γ`, and
  `O(ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)})` if `β < γ` (the exponent is `√2` times the printed one,
  because the bias is `2^{−αL(L+1)/2}`), with no assumed bias constant.

`MlmcLean/ML2RLowerBound.lean` proves that this exponent cannot be improved in general and that
the printed one fails: if the bias is at least `b 2^{−αL(L+1)/2}` for every `L` (`0 < b ≤ 1`)
and `V_ℓ`, `C_ℓ` are at least positive multiples of `2^{−βℓ}`, `2^{γℓ}`, then for `0 < ε < 1`
every `L` and `N_ℓ ≥ 1` with `E[(Y − E[P])²] ≤ ε²` cost at least a positive multiple of
`ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}` (`ml2r_cost_lower_sqrt`, `ml2r_printed_cost_fails`), and an
example that satisfies the expansion with an `L`-independent constant has such a bias
(`ml2r_instance_hypotheses`, `ml2r_instance_cost`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### A sharp bound on the ML2R weights -/

section weights

/-- The factors of the weight `w_ℓ` from the nodes `x_k = r^k`, `ℓ < k ≤ L`, are
`r^{k−ℓ}/(1 − r^{k−ℓ})` (`abs_ml2r_factor_of_gt`); their product is at most
`e^{r/(1−r)²} ∏_{k=ℓ+1}^{L} r^{k−ℓ}`. -/
lemma prod_ml2r_factor_gt_le_prod {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ℓ L : ℕ) :
    ∏ k ∈ Ico (ℓ + 1) (L + 1), |r ^ k / (r ^ k - r ^ ℓ)| ≤
      Real.exp (r / (1 - r) ^ 2) * ∏ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) := by
  have h1 : 0 < 1 - r := by linarith
  have hkℓ : ∀ k ∈ Ico (ℓ + 1) (L + 1), ℓ < k := fun k hk => by
    have := (Finset.mem_Ico.1 hk).1
    omega
  have hq : ∀ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) < 1 := fun k hk =>
    pow_lt_one₀ hr0.le hr1 (Nat.sub_ne_zero_of_lt (hkℓ k hk))
  have hinv : ∏ k ∈ Ico (ℓ + 1) (L + 1), (1 - r ^ (k - ℓ))⁻¹ ≤ Real.exp (r / (1 - r) ^ 2) :=
    calc ∏ k ∈ Ico (ℓ + 1) (L + 1), (1 - r ^ (k - ℓ))⁻¹
        ≤ ∏ k ∈ Ico (ℓ + 1) (L + 1), Real.exp (r ^ (k - ℓ) / (1 - r)) := by
          refine Finset.prod_le_prod (fun k hk => ?_) fun k hk => ?_
          · exact inv_nonneg.2 (by linarith [hq k hk])
          · exact inv_one_sub_le_exp (pow_nonneg hr0.le _)
              (pow_le_of_le_one hr0.le hr1.le (Nat.sub_ne_zero_of_lt (hkℓ k hk))) hr1
      _ = Real.exp (∑ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) / (1 - r)) :=
          (Real.exp_sum _ _).symm
      _ ≤ Real.exp (r / (1 - r) ^ 2) := by
          refine Real.exp_le_exp.2 ?_
          have hre : ∑ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) =
              ∑ j ∈ range (L + 1 - (ℓ + 1)), r ^ (j + 1) := by
            rw [Finset.sum_Ico_eq_sum_range]
            refine Finset.sum_congr rfl fun j _ => ?_
            congr 1
            omega
          rw [← Finset.sum_div, hre, sq, ← div_div]
          exact div_le_div_of_nonneg_right (sum_pow_succ_le hr0.le hr1 _) h1.le
  calc ∏ k ∈ Ico (ℓ + 1) (L + 1), |r ^ k / (r ^ k - r ^ ℓ)|
      = (∏ k ∈ Ico (ℓ + 1) (L + 1), (1 - r ^ (k - ℓ))⁻¹) *
          ∏ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun k hk => by
          rw [abs_ml2r_factor_of_gt hr0 hr1 (hkℓ k hk), mul_comm]
    _ ≤ Real.exp (r / (1 - r) ^ 2) * ∏ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) :=
        mul_le_mul_of_nonneg_right hinv (Finset.prod_nonneg fun k _ => pow_nonneg hr0.le _)

/-- For `r = 2^{−α}` the powers `r^{k−ℓ}`, `ℓ < k ≤ L`, multiply to
`r^{1 + 2 + ⋯ + (L−ℓ)} = 2^{−α(L−ℓ)(L−ℓ+1)/2}`. -/
lemma prod_ml2r_pow_gt (α : ℝ) {ℓ L : ℕ} (hℓ : ℓ ≤ L) :
    ∏ k ∈ Ico (ℓ + 1) (L + 1), ((2 : ℝ) ^ (-α)) ^ (k - ℓ) =
      (2 : ℝ) ^ (-(α * (((L : ℝ) - ℓ) * ((L : ℝ) - ℓ + 1) / 2))) := by
  have h1 : ∏ k ∈ Ico (ℓ + 1) (L + 1), ((2 : ℝ) ^ (-α)) ^ (k - ℓ) =
      ∏ j ∈ range (L - ℓ), ml2rNode α (j + 1) := by
    rw [Finset.prod_Ico_eq_prod_range, show L + 1 - (ℓ + 1) = L - ℓ by omega]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ml2rNode_eq]
    congr 1
    omega
  have h2 : ∏ j ∈ range (L - ℓ), ml2rNode α (j + 1) =
      ∏ k ∈ range (L - ℓ + 1), ml2rNode α k := by
    rw [Finset.prod_range_succ' (fun k => ml2rNode α k), show ml2rNode α 0 = 1 by simp [ml2rNode],
      mul_one]
  rw [h1, h2, prod_ml2rNode, Nat.cast_sub hℓ]

/-- **The ML2R weights decay like `r^{(L−ℓ)(L−ℓ+1)/2}`** (Giles 2015, §2.3, p. 11: Lemaire and
Pagès "first determine the unique set of weights `w_ℓ`, `ℓ = 0, 1, …, L`"; see `ml2r_weights`).
With `r = 2^{−α}` (`α > 0`) and `B = e^{r/(1−r)²}`, the weight of level `ℓ ≤ L` satisfies
`|w_ℓ| ≤ B² r^{(L−ℓ)(L−ℓ+1)/2} = B² 2^{−α(L−ℓ)(L−ℓ+1)/2}`, uniformly in `L`.  This sharpens
`abs_ml2rWeight_le` (`|w_ℓ| ≤ B² r^{L−ℓ}`): the factors `x_k/(x_k − x_ℓ)`, `k > ℓ`, of
`w_ℓ = ∏_{k ≠ ℓ} x_k/(x_k − x_ℓ)` are `r^{k−ℓ}/(1 − r^{k−ℓ})`, whose powers of `r` multiply to
`r^{1 + 2 + ⋯ + (L−ℓ)}`.  The paper gives no bound on the weights; this one is what makes the
bias uniformly small (`ml2r_bias_le`). -/
theorem abs_ml2rWeight_le_sharp {α : ℝ} (hα : 0 < α) {L ℓ : ℕ} (hℓ : ℓ ≤ L) :
    |ml2rWeight α L ℓ| ≤ Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) ^ 2 *
      (2 : ℝ) ^ (-(α * (((L : ℝ) - ℓ) * ((L : ℝ) - ℓ + 1) / 2))) := by
  have hr0 : 0 < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos two_pos _
  have hr1 : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hsplit : (range (L + 1)).erase ℓ = range ℓ ∪ Ico (ℓ + 1) (L + 1) := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (range ℓ) (Ico (ℓ + 1) (L + 1)) := by
    refine Finset.disjoint_left.2 fun k h1 h2 => ?_
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2
    omega
  rw [ml2rWeight_eq_prod, Finset.abs_prod, hsplit, Finset.prod_union hdisj,
    ← prod_ml2r_pow_gt α hℓ]
  calc _ ≤ Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) *
        (Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) *
          ∏ k ∈ Ico (ℓ + 1) (L + 1), ((2 : ℝ) ^ (-α)) ^ (k - ℓ)) :=
        mul_le_mul (prod_ml2r_factor_lt_le hr0 hr1 ℓ) (prod_ml2r_factor_gt_le_prod hr0 hr1 ℓ L)
          (Finset.prod_nonneg fun k _ => abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

end weights

/-! ### The bias of ML2R from the weak-error expansion -/

section bias

/-- The constant `B² (1 + (1 − r)⁻¹)` of the ML2R bias bound `ml2r_bias_le`, with `r = 2^{−α}`
and `B = e^{r/(1−r)²}` (Giles 2015, §2.3).  It depends only on `α`. -/
noncomputable def ml2rBiasConst (α : ℝ) : ℝ :=
  Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) ^ 2 * (1 + (1 - (2 : ℝ) ^ (-α))⁻¹)

/-- `ml2rBiasConst α > 0` for `α > 0`. -/
lemma ml2rBiasConst_pos {α : ℝ} (hα : 0 < α) : 0 < ml2rBiasConst α := by
  have hr1 : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have h : 0 < (1 - (2 : ℝ) ^ (-α))⁻¹ := inv_pos.2 (by linarith)
  exact mul_pos (pow_pos (Real.exp_pos _) 2) (by linarith)

/-- `2^{−α(L−ℓ)(L−ℓ+1)/2} x_ℓ^L = 2^{−αL(L+1)/2} 2^{−αℓ(ℓ−1)/2}` for the nodes `x_ℓ = 2^{−αℓ}`:
the exponents satisfy `(L−ℓ)(L−ℓ+1)/2 + ℓL = L(L+1)/2 + ℓ(ℓ−1)/2`. -/
lemma two_rpow_mul_ml2rNode_pow (α : ℝ) (L ℓ : ℕ) :
    (2 : ℝ) ^ (-(α * (((L : ℝ) - ℓ) * ((L : ℝ) - ℓ + 1) / 2))) * ml2rNode α ℓ ^ L =
      (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) *
        (2 : ℝ) ^ (-(α * ((ℓ : ℝ) * (ℓ - 1) / 2))) := by
  rw [ml2rNode, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
  congr 1
  ring

/-- `∑_{ℓ=0}^{L} 2^{−αℓ(ℓ−1)/2} ≤ 1 + (1 − 2^{−α})⁻¹` for `α > 0`, whatever `L`. -/
lemma ml2r_sum_triangle_le {α : ℝ} (hα : 0 < α) (L : ℕ) :
    ∑ ℓ ∈ range (L + 1), (2 : ℝ) ^ (-(α * ((ℓ : ℝ) * (ℓ - 1) / 2))) ≤
      1 + (1 - (2 : ℝ) ^ (-α))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-α) := (Real.rpow_pos_of_pos two_pos _).le
  have hr1 : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hj : ∀ j ∈ range L,
      (2 : ℝ) ^ (-(α * (((j + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) - 1) / 2))) ≤ ((2 : ℝ) ^ (-α)) ^ j := by
    intro j _
    rw [← two_rpow_mul_nat]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    push_cast
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h
      simp
    · have hj1 : (1 : ℝ) ≤ j := Nat.one_le_cast.2 h
      nlinarith [mul_nonneg hα.le (mul_nonneg hj0 (sub_nonneg.2 hj1))]
  rw [Finset.sum_range_succ', add_comm]
  refine add_le_add (le_of_eq (by simp)) ((Finset.sum_le_sum hj).trans ?_)
  exact geom_sum_le_of_lt_one hr0 hr1 L

/-- **The ML2R bias is uniformly small** (Giles 2015, §2.3, pp. 11–12): "Assuming that the weak
error has a regular expansion `E[P_ℓ] − E[P] = ∑_{n=1}^{L} a_n 2^{−nαℓ} + O(2^{−αℓL})`, … so that
`(∑_{ℓ=0}^{L} w_ℓ E[P_ℓ]) − E[P] = ∑_{ℓ=0}^{L} w_ℓ (E[P_ℓ] − E[P]) = O(2^{−αL²})`."  Here
`EPl ℓ = E[P_ℓ]`, `EP = E[P]` and `w = ml2rWeight α L`.  If the remainder of the expansion is at
most `K 2^{−αℓL}` on the levels used, `|E[P_ℓ] − E[P] − ∑_{n=1}^{L} a_n 2^{−nαℓ}| ≤ K 2^{−αℓL}`
for `ℓ = 0, …, L`, then
`|∑_{ℓ=0}^{L} w_ℓ E[P_ℓ] − E[P]| ≤ ml2rBiasConst α · K · 2^{−αL(L+1)/2}`,
where `ml2rBiasConst α` depends only on `α`: the bias is `O(2^{−αL(L+1)/2})` uniformly in `L`
whenever `K` does not depend on `L`.

**Correction.** The rate is `2^{−αL(L+1)/2}`, not the printed `2^{−αL²}`, and it cannot be
improved: `E[P_ℓ] − E[P] = 2^{−α(L+1)ℓ}` satisfies the hypothesis with `a = 0` and `K = 1`, and
its bias is exactly `(−1)^L 2^{−αL(L+1)/2}` (`ml2r_bias`), `2^{αL(L−1)/2}` times the printed
`2^{−αL²}`; so no bound `C K 2^{−αL²}` with `C` independent of `L` holds.

Proof: by `ml2r_bias_eq` the bias is `∑_ℓ w_ℓ R_ℓ` with `|R_ℓ| ≤ K 2^{−αℓL}`; by
`abs_ml2rWeight_le_sharp`, `|w_ℓ| 2^{−αℓL} ≤ B² 2^{−αL(L+1)/2} 2^{−αℓ(ℓ−1)/2}`, and
`∑_ℓ 2^{−αℓ(ℓ−1)/2} ≤ 1 + (1 − 2^{−α})⁻¹`. -/
theorem ml2r_bias_le {α : ℝ} (hα : 0 < α) (L : ℕ) (EPl : ℕ → ℝ) (EP : ℝ) (a : ℕ → ℝ) (K : ℝ)
    (hexp : ∀ ℓ ≤ L,
      |EPl ℓ - EP - ∑ n ∈ Icc 1 L, a n * ml2rNode α ℓ ^ n| ≤ K * ml2rNode α ℓ ^ L) :
    |∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * EPl ℓ - EP| ≤
      ml2rBiasConst α * K * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) := by
  have hK : 0 ≤ K := by
    have h := hexp 0 (Nat.zero_le L)
    rw [show ml2rNode α 0 = 1 by simp [ml2rNode], one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hE : 0 ≤ Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) ^ 2 * K *
      (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) := by positivity
  rw [ml2r_bias_eq hα L EPl EP a (fun ℓ => EPl ℓ - EP - ∑ n ∈ Icc 1 L, a n * ml2rNode α ℓ ^ n)
    (fun ℓ _ => by ring)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ ℓ ∈ range (L + 1),
        |ml2rWeight α L ℓ * (EPl ℓ - EP - ∑ n ∈ Icc 1 L, a n * ml2rNode α ℓ ^ n)|
      ≤ ∑ ℓ ∈ range (L + 1), Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) ^ 2 * K *
          (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) *
            (2 : ℝ) ^ (-(α * ((ℓ : ℝ) * (ℓ - 1) / 2))) := by
        refine Finset.sum_le_sum fun ℓ hℓ => ?_
        have hℓL : ℓ ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
        rw [abs_mul]
        calc |ml2rWeight α L ℓ| * |EPl ℓ - EP - ∑ n ∈ Icc 1 L, a n * ml2rNode α ℓ ^ n|
            ≤ Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) ^ 2 *
                (2 : ℝ) ^ (-(α * (((L : ℝ) - ℓ) * ((L : ℝ) - ℓ + 1) / 2))) *
                  (K * ml2rNode α ℓ ^ L) :=
              mul_le_mul (abs_ml2rWeight_le_sharp hα hℓL) (hexp ℓ hℓL) (abs_nonneg _)
                (by positivity)
          _ = Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) ^ 2 * K *
                ((2 : ℝ) ^ (-(α * (((L : ℝ) - ℓ) * ((L : ℝ) - ℓ + 1) / 2))) *
                  ml2rNode α ℓ ^ L) := by ring
          _ = _ := by rw [two_rpow_mul_ml2rNode_pow]; ring
    _ = Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) ^ 2 * K *
          (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) *
            ∑ ℓ ∈ range (L + 1), (2 : ℝ) ^ (-(α * ((ℓ : ℝ) * (ℓ - 1) / 2))) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) ^ 2 * K *
          (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) * (1 + (1 - (2 : ℝ) ^ (-α))⁻¹) :=
        mul_le_mul_of_nonneg_left (ml2r_sum_triangle_le hα L) hE
    _ = ml2rBiasConst α * K * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) := by
        rw [ml2rBiasConst]
        ring

end bias

/-! ### The ML2R estimator and its mean square error -/

section defs

variable {Ω₀ Ω : Type*}

/-- **The ML2R estimator** (Giles 2015, §2.3, p. 12): "`Y = ∑_{ℓ=0}^{L} Y_ℓ`,
`Y_ℓ = N_ℓ⁻¹ v_ℓ ∑_n (P_ℓ^{(ℓ,n)} − P_{ℓ−1}^{(ℓ,n)})`" with `v_ℓ = ∑_{ℓ'=ℓ}^{L} w_ℓ'` and the ML2R
weights `w = ml2rWeight α L`.  The level-`ℓ` term is the Monte Carlo average (`blockMean`) of
`v_ℓ (P_ℓ − P_{ℓ−1})` over the inputs `ω (ℓ, 0), …, ω (ℓ, N_ℓ − 1)` (samples numbered from `0`);
this is the estimator of `ml2r_estimator_mean_variance` for these weights. -/
noncomputable def ml2rEstimator (α : ℝ) (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (L : ℕ)
    (N : ℕ → ℕ) (x : Ω) : ℝ :=
  ∑ ℓ ∈ range (L + 1),
    blockMean (fun ℓ y => (∑ k ∈ Ico ℓ (L + 1), ml2rWeight α L k) * levelDiff Pl ℓ y) ω ℓ (N ℓ) x

end defs

section estimator

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω} {Pl : ℕ → Ω₀ → ℝ} {ω : ℕ × ℕ → Ω → Ω₀}

/-- The mean square error of the ML2R estimator (Giles 2015, (2.1) and §2.3): with independent
inputs of law `ν` and `N_ℓ ≥ 1`, for any target `m`,
`E[(Y − m)²] = ∑_ℓ v_ℓ² V_ℓ/N_ℓ + (∑_ℓ w_ℓ E[P_ℓ] − m)²`, `V_ℓ = V[P_ℓ − P_{ℓ−1}]`. -/
lemma ml2rEstimator_mse [IsProbabilityMeasure μ] (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    (α : ℝ) (L : ℕ) {N : ℕ → ℕ} (hN : ∀ ℓ, 0 < N ℓ) (m : ℝ) :
    μ[fun x => (ml2rEstimator α Pl ω L N x - m) ^ 2] =
      ∑ ℓ ∈ range (L + 1),
          (∑ k ∈ Ico ℓ (L + 1), ml2rWeight α L k) ^ 2 * variance (levelDiff Pl ℓ) ν / N ℓ +
        (∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * ∫ y, Pl ℓ y ∂ν - m) ^ 2 := by
  obtain ⟨hmean, hvar⟩ := ml2r_estimator_mean_variance hω hind hPlm hPl (ml2rWeight α L) L hN
  have hY : MemLp (ml2rEstimator α Pl ω L N) 2 μ :=
    memLp_finsetSum _ fun ℓ _ =>
      memLp_blockMean hω (fun ℓ => (memLp_levelDiff hPl ℓ).const_mul _) ℓ (N ℓ)
  rw [mse_eq_variance_add_sq_bias hY m]
  exact congrArg₂ (fun u v => u + (v - m) ^ 2) hvar hmean

/-- The mean square error of the ML2R estimator is at most
`(c₁ 2^{−αL(L+1)/2})² + ∑_ℓ v_ℓ² c₂ 2^{−βℓ}/N_ℓ` if the weak-error expansion holds on the levels
`ℓ ≤ L` with remainder constant `K`, `ml2rBiasConst α · K ≤ c₁` and `V_ℓ ≤ c₂ 2^{−βℓ}`
(Giles 2015, §2.3; the bias is bounded by `ml2r_bias_le`). -/
lemma ml2rEstimator_mse_le [IsProbabilityMeasure μ] (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    {EP K α β c₁ c₂ : ℝ} {a : ℕ → ℝ} (hα : 0 < α) (L : ℕ) {N : ℕ → ℕ} (hN : ∀ ℓ, 0 < N ℓ)
    (hexp : ∀ ℓ ≤ L,
      |∫ y, Pl ℓ y ∂ν - EP - ∑ n ∈ Icc 1 L, a n * ml2rNode α ℓ ^ n| ≤ K * ml2rNode α ℓ ^ L)
    (hc₁ : ml2rBiasConst α * K ≤ c₁)
    (hV : ∀ ℓ, variance (levelDiff Pl ℓ) ν ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) :
    μ[fun x => (ml2rEstimator α Pl ω L N x - EP) ^ 2] ≤
      (c₁ * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2)))) ^ 2 +
        ∑ ℓ ∈ range (L + 1),
          (∑ k ∈ Ico ℓ (L + 1), ml2rWeight α L k) ^ 2 * Vb β c₂ ℓ / (N ℓ : ℝ) := by
  rw [ml2rEstimator_mse hω hind hPlm hPl α L hN EP, add_comm]
  refine add_le_add ?_ (Finset.sum_le_sum fun ℓ _ => ?_)
  · have hb := ml2r_bias_le hα L (fun ℓ => ∫ y, Pl ℓ y ∂ν) EP a K hexp
    have h2 : 0 ≤ (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) := Real.rpow_nonneg (by norm_num) _
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb.trans (mul_le_mul_of_nonneg_right hc₁ h2)) 2
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hV ℓ) (sq_nonneg _))
      (Nat.cast_nonneg _)

/-- **The ML2R theorem, `β = γ`** (Giles 2015, §2.3, pp. 11–12, after Lemaire and Pagès 2013):
"Assuming that the weak error has a regular expansion
`E[P_ℓ] − E[P] = ∑_{n=1}^{L} a_n 2^{−nαℓ} + O(2^{−αℓL})` … Hence, in the case `β = γ` they prove
that the overall cost is reduced to `O(ε⁻² |log ε|)`."

Setting of `ml2r_estimator_mean_variance`: mutually independent inputs `ω (ℓ, n)` of law `ν` on a
probability space `(Ω, μ)`, measurable square-integrable level approximations `P_ℓ = Pl ℓ`, the
ML2R estimator `Y = ml2rEstimator α Pl ω L N` and a target `EP` (Giles: `E[P]`).  Let `α, γ > 0`,
`β = γ`, `c₂, c₃ > 0`, and assume
* the weak-error expansion with an `O`-constant `K` independent of `L` and `ℓ`: for every `L` and
  `ℓ ≤ L`, `|E[P_ℓ] − EP − ∑_{n=1}^{L} a_n 2^{−nαℓ}| ≤ K 2^{−αℓL}`;
* `V[P_ℓ − P_{ℓ−1}] ≤ c₂ 2^{−βℓ}`, and per-sample costs `C_ℓ ≤ c₃ 2^{γℓ}` (as in Theorem 1).

Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with
`E[(Y − EP)²] < ε²` and cost `∑_{ℓ=0}^{L} N_ℓ C_ℓ ≤ c₄ ε⁻² |log ε|`.  The constant `c₄` depends
only on `α, β, γ, K, c₂, c₃`: it is the constant of `ml2r_complexity_eq` for
`c₁ = ml2rBiasConst α · max K 1`, independent of `a`, `EP`, `ν`, `Pl`, `ω` and `C`.

Deviations from the paper: the uniformity of the `O(2^{−αℓL})` in `L` is an explicit hypothesis
(the paper leaves it implicit, but `L` grows as `ε → 0`, and with a constant `K_L` growing with `L`
the bias need not be small); the bias is `O(2^{−αL(L+1)/2})` rather than the printed
`O(2^{−αL²})` (`ml2r_bias_le`), which changes the constant but not the order of the cost in this
case.  No sign condition on `K` or on `C_ℓ` is needed.  Standard MLMC costs `ε⁻² (log ε)²` here
(`giles_theorem1`). -/
theorem ml2r_theorem_eq [IsProbabilityMeasure μ] (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    {EP K α β γ c₂ c₃ : ℝ} {a C : ℕ → ℝ} (hα : 0 < α) (hγ : 0 < γ) (hβγ : β = γ)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hexp : ∀ L, ∀ ℓ ≤ L,
      |∫ y, Pl ℓ y ∂ν - EP - ∑ n ∈ Icc 1 L, a n * ml2rNode α ℓ ^ n| ≤ K * ml2rNode α ℓ ^ L)
    (hV : ∀ ℓ, variance (levelDiff Pl ℓ) ν ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (hC : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (ml2rEstimator α Pl ω L N x - EP) ^ 2] < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * |Real.log ε|) := by
  have hc₁ : 0 < ml2rBiasConst α * max K 1 :=
    mul_pos (ml2rBiasConst_pos hα) (lt_of_lt_of_le one_pos (le_max_right _ _))
  obtain ⟨c₄, hc₄, h⟩ := ml2r_complexity_eq (β := β) hα hγ hβγ hc₁ hc₂ hc₃
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, (ml2rEstimator_mse_le hω hind hPlm hPl hα L hN (hexp L)
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (ml2rBiasConst_pos hα).le) hV).trans_lt hmse,
    (Finset.sum_le_sum fun ℓ _ =>
      mul_le_mul_of_nonneg_left (hC ℓ) (Nat.cast_nonneg _)).trans hcost⟩

/-- **The ML2R theorem, `β < γ`** (Giles 2015, §2.3, pp. 11–12, after Lemaire and Pagès 2013):
"Assuming that the weak error has a regular expansion
`E[P_ℓ] − E[P] = ∑_{n=1}^{L} a_n 2^{−nαℓ} + O(2^{−αℓL})` … while for `β < γ` the cost is reduced
much more to `O(ε⁻² 2^{(γ−β)√(|log₂ ε|/α)})`."

Setting and hypotheses as in `ml2r_theorem_eq`, with `β < γ` (and `α, γ, c₂, c₃ > 0`; the weak-error
expansion with an `O`-constant `K` independent of `L` and `ℓ`).  Then there is `c₄ > 0` such that
for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with `E[(Y − EP)²] < ε²` and cost
`∑_{ℓ=0}^{L} N_ℓ C_ℓ ≤ c₄ ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}`.  The constant `c₄` depends only on
`α, β, γ, K, c₂, c₃`: it is the constant of `ml2r_complexity_lt` for
`c₁ = ml2rBiasConst α · max K 1`, independent of `a`, `EP`, `ν`, `Pl`, `ω` and `C`.

**Correction.** The exponent is `√(2|log₂ ε|/α)`, `√2` times the printed `√(|log₂ ε|/α)`: the
printed exponent comes from the printed bias `O(2^{−αL²})`, but the bias is only
`O(2^{−αL(L+1)/2})` (`ml2r_bias_le`, sharp by `ml2r_bias`), so a weak error `ε` needs
`L ≈ √(2 log₂(1/ε)/α)` levels in general, and the cost is of order `ε⁻² 2^{(γ−β)L}`.  Both are
proved as lower bounds in `MlmcLean.ML2RLowerBound`: if moreover the bias is at least
`b 2^{−αL(L+1)/2}` for every `L` (`0 < b ≤ 1`) and `V_ℓ`, `C_ℓ` are at least positive multiples
of `2^{−βℓ}`, `2^{γℓ}`, then for `0 < ε < 1` every `L` and `N_ℓ ≥ 1` with `E[(Y − EP)²] ≤ ε²`
have `L ≥ √(2 log₂(1/ε)/α) − κ` and cost at least a positive multiple of
`ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}` (`ml2r_cost_lower_sqrt`), so the printed exponent fails
(`ml2r_printed_cost_fails`); an example satisfies these hypotheses and those above, and on it
the least cost of mean square error `ε²` is of exact order `ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}`
(`ml2r_instance_cost`, `ml2r_instance_printed_cost_false`).  The exponent is still
`o(log(1/ε))`, so the cost is `O(ε^{−2−δ})` for every `δ > 0`, against `ε^{−2−(γ−β)/α}` for
standard MLMC (`giles_theorem1`).  As in `ml2r_theorem_eq`, the uniformity of the `O(2^{−αℓL})`
in `L` is an explicit hypothesis, and no sign condition on `K` or on `C_ℓ` is needed. -/
theorem ml2r_theorem_lt [IsProbabilityMeasure μ] (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    {EP K α β γ c₂ c₃ : ℝ} {a C : ℕ → ℝ} (hα : 0 < α) (hγ : 0 < γ) (hβγ : β < γ)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hexp : ∀ L, ∀ ℓ ≤ L,
      |∫ y, Pl ℓ y ∂ν - EP - ∑ n ∈ Icc 1 L, a n * ml2rNode α ℓ ^ n| ≤ K * ml2rNode α ℓ ^ L)
    (hV : ∀ ℓ, variance (levelDiff Pl ℓ) ν ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (hC : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (ml2rEstimator α Pl ω L N x - EP) ^ 2] < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤
          c₄ * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α))) := by
  have hc₁ : 0 < ml2rBiasConst α * max K 1 :=
    mul_pos (ml2rBiasConst_pos hα) (lt_of_lt_of_le one_pos (le_max_right _ _))
  obtain ⟨c₄, hc₄, h⟩ := ml2r_complexity_lt hα hγ hβγ hc₁ hc₂ hc₃
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, (ml2rEstimator_mse_le hω hind hPlm hPl hα L hN (hexp L)
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (ml2rBiasConst_pos hα).le) hV).trans_lt hmse,
    (Finset.sum_le_sum fun ℓ _ =>
      mul_le_mul_of_nonneg_left (hC ℓ) (Nat.cast_nonneg _)).trans hcost⟩

end estimator

end MLMC
