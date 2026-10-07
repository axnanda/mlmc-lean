import MlmcLean.QMC1D

/-!
# One-dimensional MLQMC in the boundary case `b = g ≤ a`: cost `Θ(ε⁻¹ |log ε|^{3/2})`

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015).
* §2.7, p. 20 (MLQMC): "These theoretical developments are very encouraging, showing that under
  certain conditions they lead to multilevel methods with a complexity which is `O(ε^{−p})` with
  `p < 2`."
* §3.5, p. 26: "In the best cases, this results in the approximate numerical integration error
  being `O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})` error which comes from Monte Carlo
  sampling."

`MlmcLean/QMC1D.lean` proves the MLQMC complexity in one dimension for the model: bias `c₁ 2^{−aL}`
at finest level `L`, level-`ℓ` error `c₂ 2^{−bℓ}/N_ℓ` (a randomly shifted `N_ℓ`-point lattice rule
for a correction of total variation `≤ c₂ 2^{−bℓ}`), cost `c₃ 2^{gℓ}` per point, with mean square
error `(c₁ 2^{−aL})² + ∑_{ℓ≤L} (c₂ 2^{−bℓ}/N_ℓ)²`.  It covers `b > g`, `a ≤ b` with `a < g`,
and `b < g`, and leaves out the boundary case `b = g ≤ a`.  This file treats it.

For `b = g` the products `v_ℓ C_ℓ = c₂ c₃` (`v_ℓ = c₂ 2^{−bℓ}`, `C_ℓ = c₃ 2^{gℓ}`) do not depend
on `ℓ`.  The Lagrange allocation `N_ℓ ∝ (v_ℓ²/C_ℓ)^{1/3} ∝ 2^{−gℓ}`, which minimises
`∑ N_ℓ C_ℓ` subject to `∑ (v_ℓ/N_ℓ)² ≤ τ`, has cost
`(∑_{ℓ≤L} (v_ℓ C_ℓ)^{2/3})^{3/2} τ^{−1/2} = c₂ c₃ (L + 1)^{3/2} τ^{−1/2}`, and `L ≍ log₂(1/ε)/a`.
So the optimal cost is `≍ ε⁻¹ |log ε|^{3/2}`; for the optimal real allocation
`ε · cost / |log ε|^{3/2}` tends to `c₂ c₃ (a log 2)^{−3/2}` (checked numerically with `mpmath`
down to `ε = 10^{−120}`).

* `mlqmc_boundary_complexity_core`: for `a > 0`, `g ≤ a` and `g ≤ b` there is `K` such that every
  `0 < ε < e⁻¹` admits `L` and `N_ℓ ≥ 1` with mean square error `< ε²` and cost
  `≤ K ε⁻¹ |log ε|^{3/2}` (`N_ℓ = ⌈2c₂ √(L + 1) ε⁻¹ 2^{−gℓ}⌉`).
* `mlqmc_boundary_complexity`: the same for the MLQMC estimator with one randomly shifted lattice
  rule per level (as `mlqmc_complexity`).
* `mlqmc_boundary_cost_lower`: for `b ≤ g` (any `a` and `g`, `c₁, c₂ ≠ 0`, `c₃ > 0`), every real
  allocation `N_ℓ > 0` with mean square error `≤ ε²` costs `≥ k ε⁻¹ |log ε|^{3/2}` for
  `0 < ε < 1` (Hölder's inequality `(L + 1)³ ≤ (∑ x_ℓ⁻¹)² ∑ x_ℓ²`, proved by a tangent-line bound).
* `mlqmc_boundary_exponents_optimal`: hence no bound `K ε^{−p} |log ε|^q` with `p < 1`, or with
  `p = 1` and `q < 3/2`, is achievable when `b ≤ g`: for `b = g ≤ a` both exponents of
  `mlqmc_boundary_complexity_core` are sharp.
* `mlqmc_finest_level_cost_lower`: for `a > 0` and `g ≥ 0` the points on the finest level `L`
  already cost `≥ c₃ 2^{gL} ≥ c₃ (|c₁|/ε)^{g/a}`.
* `mlqmc_finest_level_exponent_optimal`: hence no bound `K ε^{−p} |log ε|^q` with `p < g/a` is
  achievable.  So the condition `g ≤ a` of `mlqmc_boundary_complexity_core` cannot be dropped, the
  order `ε^{−g/a}` of `mlqmc_complexity_core` (`a ≤ b`, `a < g`) is sharp, and the paper's `p < 2`
  needs `g < 2a`.

The paper states no lower bounds: the last four results go beyond it.  One dimension only, as in
`MlmcLean/QMC1D.lean`: QMC error theory in `d` dimensions is not formalised.  The paper states no
conditions for its `p < 2`; here `p = 1` up to the factor `|log ε|^{3/2}`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### Hölder's inequality for `∑ x_ℓ⁻¹` against `∑ x_ℓ²` -/

/-- The tangent-line bound behind Hölder's inequality: for `x, s > 0`,
`3/(2s) − x²/(2s³) ≤ x⁻¹`, since `2s³x (x⁻¹ − 3/(2s) + x²/(2s³)) = (x − s)² (x + 2s) ≥ 0`. -/
lemma mlqmc_boundary_tangent_le_inv {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    3 / (2 * s) - x ^ 2 / (2 * s ^ 3) ≤ x⁻¹ := by
  have e : x⁻¹ - (3 / (2 * s) - x ^ 2 / (2 * s ^ 3)) =
      (x - s) ^ 2 * (x + 2 * s) / (2 * s ^ 3 * x) := by
    field_simp
    ring
  have h : 0 ≤ (x - s) ^ 2 * (x + 2 * s) / (2 * s ^ 3 * x) := by positivity
  linarith

/-- **Hölder's inequality `n³ ≤ (∑ x_i⁻¹)² ∑ x_i²`**, in the form used for the MLQMC lower bound:
if `x_i > 0` on a finite set of `n` indices and `∑ x_i² ≤ E²` with `E > 0`, then
`n √n ≤ E ∑ x_i⁻¹`.  Proof: sum `mlqmc_boundary_tangent_le_inv` with `s = E/√n`. -/
lemma mlqmc_boundary_card_mul_sqrt_le {ι : Type*} (s : Finset ι) {x : ι → ℝ} {E : ℝ}
    (hE : 0 < E) (hx : ∀ i ∈ s, 0 < x i) (hsum : ∑ i ∈ s, x i ^ 2 ≤ E ^ 2) :
    (s.card : ℝ) * Real.sqrt s.card ≤ E * ∑ i ∈ s, (x i)⁻¹ := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hn : (0 : ℝ) < s.card := Nat.cast_pos.2 hne.card_pos
  set σ : ℝ := Real.sqrt s.card
  have hσ : 0 < σ := Real.sqrt_pos.2 hn
  have hσ2 : σ ^ 2 = s.card := Real.sq_sqrt hn.le
  have hr : 0 < E / σ := div_pos hE hσ
  have h1 : ∑ i ∈ s, (3 / (2 * (E / σ)) - x i ^ 2 / (2 * (E / σ) ^ 3)) ≤ ∑ i ∈ s, (x i)⁻¹ :=
    sum_le_sum fun i hi => mlqmc_boundary_tangent_le_inv (hx i hi) hr
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_div] at h1
  have h2 : (∑ i ∈ s, x i ^ 2) / (2 * (E / σ) ^ 3) ≤ E ^ 2 / (2 * (E / σ) ^ 3) := by gcongr
  have h3 : (s.card : ℝ) * (3 / (2 * (E / σ))) - E ^ 2 / (2 * (E / σ) ^ 3) =
      s.card * σ / E := by
    rw [← hσ2]
    field_simp
    ring
  have h4 : (s.card : ℝ) * σ / E ≤ ∑ i ∈ s, (x i)⁻¹ := by linarith
  rw [div_le_iff₀ hE] at h4
  linarith

/-- `t^{3/2} = t √t` for `t ≥ 0`. -/
lemma mlqmc_boundary_rpow_three_halves {t : ℝ} (ht : 0 ≤ t) :
    t ^ ((3 : ℝ) / 2) = t * Real.sqrt t := by
  rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
    Real.rpow_add' ht (by norm_num), Real.rpow_one]

/-- **The number of levels is at least of order `|log ε|`.**  If `c₁ > 0`, `0 < ε < 1` and the
bias bound at level `L` is `c₁ 2^{−aL} < ε` (any `a ∈ ℝ`), then `k |log ε| ≤ L + 1` with
`k = min(1/(2 max(a, 1) log 2), 1/(2|log c₁| + 1))`.  For `|log ε| ≥ 2|log c₁|` the bias bound
gives `a L log 2 > |log ε|/2`; otherwise `k |log ε| < 1`. -/
lemma mlqmc_boundary_level_add_one_ge {a c₁ ε : ℝ} (hc₁ : 0 < c₁) (hε : 0 < ε) (hε1 : ε < 1)
    {L : ℕ} (hL : c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))) < ε) :
    min (1 / (2 * max a 1 * Real.log 2)) (1 / (2 * |Real.log c₁| + 1)) * (-Real.log ε) ≤
      (L : ℝ) + 1 := by
  have ht : 0 < -Real.log ε := neg_pos.2 (Real.log_neg hε hε1)
  have hp : 0 < (2 : ℝ) ^ (a * (L : ℝ)) := Real.rpow_pos_of_pos two_pos _
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hm : 0 < max a 1 := lt_max_of_lt_right one_pos
  have h1 : c₁ < ε * (2 : ℝ) ^ (a * (L : ℝ)) := by
    rw [Real.rpow_neg zero_le_two, ← div_eq_mul_inv, div_lt_iff₀ hp] at hL
    exact hL
  have h2 : Real.log c₁ < Real.log ε + a * (L : ℝ) * Real.log 2 := by
    have h := Real.log_lt_log hc₁ h1
    rwa [Real.log_mul hε.ne' hp.ne', Real.log_rpow two_pos] at h
  rcases le_or_gt (2 * |Real.log c₁|) (-Real.log ε) with hbig | hsmall
  · -- `|log ε| ≥ 2 |log c₁|`: then `a L log 2 > log c₁ + |log ε| ≥ |log ε|/2`
    have h3 : -Real.log ε < 2 * a * Real.log 2 * L := by
      have := neg_abs_le (Real.log c₁)
      nlinarith
    have h3' : -Real.log ε < 2 * max a 1 * Real.log 2 * L := by
      have : a * (L : ℝ) ≤ max a 1 * L :=
        mul_le_mul_of_nonneg_right (le_max_left a 1) (Nat.cast_nonneg L)
      nlinarith
    have h4 : 1 / (2 * max a 1 * Real.log 2) * (-Real.log ε) ≤ L := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (mul_pos (mul_pos two_pos hm) hl2)]
      linarith
    calc _ ≤ 1 / (2 * max a 1 * Real.log 2) * (-Real.log ε) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) ht.le
      _ ≤ L := h4
      _ ≤ (L : ℝ) + 1 := by linarith
  · -- `|log ε| < 2 |log c₁|`: then `k |log ε| < 1 ≤ L + 1`
    have h4 : 1 / (2 * |Real.log c₁| + 1) * (-Real.log ε) ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    calc _ ≤ 1 / (2 * |Real.log c₁| + 1) * (-Real.log ε) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) ht.le
      _ ≤ 1 := h4
      _ ≤ (L : ℝ) + 1 := by linarith

/-- **A rate `ε^{−p} |log ε|^q` is eventually below a larger rate `ε^{−p'} |log ε|^{q'}`.**  If
`k > 0`, `ε₀ > 0`, and `p < p'`, or `p = p'` and `q < q'`, then for every `K` there is
`0 < ε < min(ε₀, 1)` with `K ε^{−p} |log ε|^q < k ε^{−p'} |log ε|^{q'}`.  Proof: with
`ε = e^{−t}` the left-hand side is `≤ max(K, 0) t^{q−q'} e^{−(p'−p)t} · ε^{−p'} t^{q'}`, and
`t^{q−q'} e^{−(p'−p)t} → 0` as `t → ∞` (`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`,
`tendsto_rpow_neg_atTop`). -/
lemma mlqmc_boundary_exists_eps_lt {k K p q p' q' ε₀ : ℝ} (hk : 0 < k) (hε₀ : 0 < ε₀)
    (hpq : p < p' ∨ (p = p' ∧ q < q')) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧ ε < 1 ∧
      K * ε ^ (-p) * (-Real.log ε) ^ q < k * ε ^ (-p') * (-Real.log ε) ^ q' := by
  set K' : ℝ := max K 0
  -- `t^{q − q'} e^{−(p'−p)t} → 0`
  have hF : Filter.Tendsto (fun t : ℝ => t ^ (q - q') * Real.exp (-(p' - p) * t))
      Filter.atTop (nhds 0) := by
    rcases hpq with hp1 | ⟨hp1, hq⟩
    · exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by linarith)
    · have e : (fun t : ℝ => t ^ (q - q') * Real.exp (-(p' - p) * t)) =
          fun t : ℝ => t ^ (-(q' - q)) := by
        funext t
        rw [hp1, sub_self, neg_zero, zero_mul, Real.exp_zero, mul_one, neg_sub]
      rw [e]
      exact tendsto_rpow_neg_atTop (by linarith)
  have hF' := (hF.const_mul K').eventually (gt_mem_nhds (by rw [mul_zero]; exact hk))
  obtain ⟨t, hlt, ht⟩ :=
    (hF'.and (Filter.eventually_gt_atTop (max (-Real.log ε₀) 0))).exists
  have ht0 : 0 < t := (le_max_right _ _).trans_lt ht
  refine ⟨Real.exp (-t), Real.exp_pos _, ?_, Real.exp_lt_one_iff.2 (by linarith), ?_⟩
  · rw [← Real.exp_log hε₀]
    exact Real.exp_lt_exp.2 (by linarith [le_max_left (-Real.log ε₀) 0])
  -- `K ε^{−p} t^q ≤ K' ε^{−p} t^q = K' t^{q−q'} e^{−(p'−p)t} · ε^{−p'} t^{q'}`
  have hεp : ∀ r : ℝ, Real.exp (-t) ^ (-r) = Real.exp (r * t) := fun r => by
    rw [← Real.exp_mul]
    congr 1
    ring
  have htq : t ^ q = t ^ (q - q') * t ^ q' := by rw [← Real.rpow_add ht0, sub_add_cancel]
  have hexp : Real.exp (-(p' - p) * t) * Real.exp (p' * t) = Real.exp (p * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpos : 0 < Real.exp (p' * t) * t ^ q' :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht0 _)
  rw [Real.log_exp, neg_neg, hεp, hεp]
  calc K * Real.exp (p * t) * t ^ q ≤ K' * Real.exp (p * t) * t ^ q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.exp_pos _).le) (Real.rpow_pos_of_pos ht0 q).le
    _ = K' * (t ^ (q - q') * Real.exp (-(p' - p) * t)) * (Real.exp (p' * t) * t ^ q') := by
        rw [htq, ← hexp]
        ring
    _ < k * (Real.exp (p' * t) * t ^ q') := mul_lt_mul_of_pos_right hlt hpos
    _ = _ := by ring

/-! ### The upper bound -/

/-- **MLQMC complexity `O(ε⁻¹ |log ε|^{3/2})` in the boundary case `b = g ≤ a`, the real-analysis
core** (Giles 2015, §2.7, p. 20: theoretical developments for MLQMC show "that under certain
conditions they lead to multilevel methods with a complexity which is `O(ε^{−p})` with `p < 2`").
One dimension only: QMC error theory in `d` dimensions (Koksma–Hlawka, low-discrepancy and Sobol
points) is not formalised.  Let `a > 0`, `g ≤ a`, `g ≤ b` (no sign condition on `g`) and
`c₁, c₂, c₃ > 0` (as in `mlqmc_complexity_core`; the probabilistic `mlqmc_boundary_complexity`
needs no sign conditions on the constants): a bias `c₁ 2^{−aL}` at finest level `L`, level-`ℓ`
corrections whose randomly shifted lattice rule with `N_ℓ` points has root-mean-square error
`≤ c₂ 2^{−bℓ}/N_ℓ` (`latticeRule_randomShift` with total variation `V_ℓ ≤ c₂ 2^{−bℓ}`) and a cost
`c₃ 2^{gℓ}` per point.  There is `K > 0` such that for every `0 < ε < e⁻¹` there are `L` and
`N_ℓ ≥ 1` with `(c₁ 2^{−aL})² + ∑_{ℓ≤L} (c₂ 2^{−bℓ}/N_ℓ)² < ε²` and
`∑_{ℓ≤L} N_ℓ c₃ 2^{gℓ} ≤ K ε⁻¹ |log ε|^{3/2}`.  This is the regime that `mlqmc_complexity_core`
leaves out; for `g < b` that theorem gives the better `O(ε⁻¹)`, and for `b = g` the bound here is
sharp (`mlqmc_boundary_cost_lower`, `mlqmc_boundary_exponents_optimal`).  The condition `g ≤ a`
cannot be dropped: for `a < g` the points on level `L` already cost
`≥ c₃ 2^{gL} ≥ c₃ (c₁/ε)^{g/a}` (`mlqmc_finest_level_cost_lower`), so no bound `O(ε^{−p})` with
`p < g/a` holds (`mlqmc_finest_level_exponent_optimal`), while `O(ε^{−g/a})` is attained
(`mlqmc_complexity_core`, as `a < g ≤ b`): the cost is then `Θ(ε^{−g/a})`.  The range `ε < e⁻¹`
makes `|log ε| ≥ 1`.  Proof:
`L = levelL a c₁ (ε/2)`, so `L + 1 ≤ K' |log ε|` (`level_add_one_le`), and
`N_ℓ = ⌈2c₂ √(L + 1) ε⁻¹ 2^{−gℓ}⌉`, the Lagrange allocation for `b = g`,
`N_ℓ ∝ (v_ℓ²/C_ℓ)^{1/3} ∝ 2^{−gℓ}` (for `g < b` the same allocation, with
`2^{−bℓ} ≤ 2^{−gℓ}`): each level contributes `≤ ε²/(4(L + 1))` to the mean square error, the
main cost is `2c₂c₃ (L + 1)^{3/2} ε⁻¹` and the rounding up costs `c₃ ∑_{ℓ≤L} 2^{gℓ} = O(ε⁻¹)`
(`exists_sum_two_rpow_le`, `g ≤ a`). -/
theorem mlqmc_boundary_complexity_core {a b g c₁ c₂ c₃ : ℝ} (ha : 0 < a) (hga : g ≤ a)
    (hgb : g ≤ b) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) → ∃ (L : ℕ) (N : ℕ → ℕ),
      (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N ℓ) ^ 2 < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          K * ε⁻¹ * (-Real.log ε) ^ ((3 : ℝ) / 2) := by
  have hK1 := K1_pos (α := a) hc₁
  set Kp : ℝ := (|Real.log (K1 a c₁)| + 1) / (a * Real.log 2) + 1
  have hKp : 0 < Kp := by positivity
  obtain ⟨K₀, hK₀, hround⟩ := exists_sum_two_rpow_le g ha hK1
  refine ⟨2 * c₂ * c₃ * (Kp * Real.sqrt Kp) + c₃ * K₀, by positivity, fun ε hε hε1 => ?_⟩
  have hε1' : ε < 1 := eps_lt_one hε1
  have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
  set L := levelL a c₁ (ε / 2)
  set n : ℝ := (L : ℝ) + 1 with hndef
  have hn0 : 0 < n := by positivity
  set M : ℝ := 2 * c₂ * Real.sqrt n / ε with hMdef
  have hM0 : 0 < M := by positivity
  refine ⟨L, fun ℓ => ⌈M * (2 : ℝ) ^ (-(g * (ℓ : ℝ)))⌉₊,
    fun ℓ => Nat.ceil_pos.2 (by positivity), ?_, ?_⟩
  · -- the mean square error
    have hbias : (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 ≤ ε ^ 2 / 4 := by
      have hb := levelL_bias ha hc₁ (half_pos hε)
      calc _ ≤ (ε / 2) ^ 2 := by gcongr
        _ = ε ^ 2 / 4 := by ring
    have hterm : ∀ ℓ ∈ range (L + 1),
        (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) /
          ((⌈M * (2 : ℝ) ^ (-(g * (ℓ : ℝ)))⌉₊ : ℕ) : ℝ)) ^ 2 ≤ ε ^ 2 / (4 * n) := by
      intro ℓ _
      have hN : M * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) ≤
          ((⌈M * (2 : ℝ) ^ (-(g * (ℓ : ℝ)))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have hpos : 0 < M * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) := by positivity
      have h1 : c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) /
          ((⌈M * (2 : ℝ) ^ (-(g * (ℓ : ℝ)))⌉₊ : ℕ) : ℝ) ≤ ε / (2 * Real.sqrt n) := by
        rw [div_le_iff₀ (hpos.trans_le hN)]
        calc c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) ≤ c₂ * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) :=
              mul_le_mul_of_nonneg_left (two_rpow_neg_mul_le hgb ℓ) hc₂.le
          _ = ε / (2 * Real.sqrt n) * (M * (2 : ℝ) ^ (-(g * (ℓ : ℝ)))) := by
              rw [hMdef]
              field_simp
          _ ≤ ε / (2 * Real.sqrt n) * ((⌈M * (2 : ℝ) ^ (-(g * (ℓ : ℝ)))⌉₊ : ℕ) : ℝ) := by
              gcongr
      have h0 : 0 ≤ c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) /
          ((⌈M * (2 : ℝ) ^ (-(g * (ℓ : ℝ)))⌉₊ : ℕ) : ℝ) := by positivity
      calc _ ≤ (ε / (2 * Real.sqrt n)) ^ 2 := by gcongr
        _ = ε ^ 2 / (4 * n) := by
            rw [div_pow, mul_pow, Real.sq_sqrt hn0.le]
            ring
    have hvar : ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) /
        ((⌈M * (2 : ℝ) ^ (-(g * (ℓ : ℝ)))⌉₊ : ℕ) : ℝ)) ^ 2 ≤ ε ^ 2 / 4 := by
      calc _ ≤ ∑ ℓ ∈ range (L + 1), ε ^ 2 / (4 * n) := sum_le_sum hterm
        _ = ε ^ 2 / 4 := by
            rw [sum_const, card_range, nsmul_eq_mul]
            push_cast
            rw [← hndef]
            field_simp
    nlinarith [sq_pos_of_pos hε]
  · -- the cost
    have hL2 := two_rpow_levelL_half_le ha hc₁ hε hε1'
    have hnle : n ≤ Kp * (-Real.log ε) := level_add_one_le ha hK1 hε hε1 hL2
    have hterm : ∀ ℓ ∈ range (L + 1),
        ((⌈M * (2 : ℝ) ^ (-(g * (ℓ : ℝ)))⌉₊ : ℕ) : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          M * c₃ + c₃ * ((2 : ℝ) ^ g) ^ ℓ := by
      intro ℓ _
      have hN : ((⌈M * (2 : ℝ) ^ (-(g * (ℓ : ℝ)))⌉₊ : ℕ) : ℝ) ≤
          M * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
      have e : (2 : ℝ) ^ (-(g * (ℓ : ℝ))) * (2 : ℝ) ^ (g * (ℓ : ℝ)) = 1 := by
        rw [← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero]
      calc _ ≤ (M * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) + 1) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) := by
            gcongr
        _ = M * c₃ * ((2 : ℝ) ^ (-(g * (ℓ : ℝ))) * (2 : ℝ) ^ (g * (ℓ : ℝ))) +
            c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ)) := by ring
        _ = _ := by rw [e, two_rpow_mul_nat, mul_one]
    have hround' := hround ε hε hε1' L hL2
    have hmax : max 1 (g / a) = 1 := max_eq_left ((div_le_one ha).2 hga)
    rw [hmax, Real.rpow_neg_one] at hround'
    have hsq : Real.sqrt n ≤ Real.sqrt Kp * Real.sqrt (-Real.log ε) := by
      rw [← Real.sqrt_mul hKp.le]
      exact Real.sqrt_le_sqrt hnle
    have hprod : n * Real.sqrt n ≤
        (Kp * Real.sqrt Kp) * ((-Real.log ε) * Real.sqrt (-Real.log ε)) := by
      calc n * Real.sqrt n ≤ (Kp * (-Real.log ε)) * (Real.sqrt Kp * Real.sqrt (-Real.log ε)) :=
            mul_le_mul hnle hsq (Real.sqrt_nonneg _) (by positivity)
        _ = _ := by ring
    have h1 : 1 ≤ (-Real.log ε) * Real.sqrt (-Real.log ε) := by
      have : 1 ≤ Real.sqrt (-Real.log ε) := Real.one_le_sqrt.2 ht
      nlinarith
    have hεi : 0 < ε⁻¹ := inv_pos.2 hε
    rw [mlqmc_boundary_rpow_three_halves (by linarith)]
    calc _ ≤ ∑ ℓ ∈ range (L + 1), (M * c₃ + c₃ * ((2 : ℝ) ^ g) ^ ℓ) := sum_le_sum hterm
      _ = n * M * c₃ + c₃ * ∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ g) ^ ℓ := by
          rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
          push_cast
          ring
      _ ≤ n * M * c₃ + c₃ * (K₀ * ε⁻¹) := by gcongr
      _ = 2 * c₂ * c₃ * (n * Real.sqrt n) * ε⁻¹ + c₃ * K₀ * ε⁻¹ := by
          rw [hMdef]
          ring
      _ ≤ 2 * c₂ * c₃ * ((Kp * Real.sqrt Kp) * ((-Real.log ε) * Real.sqrt (-Real.log ε))) *
            ε⁻¹ + c₃ * K₀ * ((-Real.log ε) * Real.sqrt (-Real.log ε)) * ε⁻¹ := by
          have hA : 2 * c₂ * c₃ * (n * Real.sqrt n) * ε⁻¹ ≤ 2 * c₂ * c₃ *
              ((Kp * Real.sqrt Kp) * ((-Real.log ε) * Real.sqrt (-Real.log ε))) * ε⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity)) hεi.le
          have hB : c₃ * K₀ * ε⁻¹ ≤ c₃ * K₀ * ((-Real.log ε) * Real.sqrt (-Real.log ε)) * ε⁻¹ :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) h1) hεi.le
          exact add_le_add hA hB
      _ = _ := by ring

/-- **MLQMC with randomly shifted lattice rules in one dimension, boundary case `b = g ≤ a`: mean
square error `< ε²` at cost `O(ε⁻¹ |log ε|^{3/2})`** (Giles 2015, §2.7, p. 20: "under certain
conditions they lead to multilevel methods with a complexity which is `O(ε^{−p})` with `p < 2`";
§3.5, p. 26: MLQMC with "a random shift (for rank-1 lattice rules)" and error "In the best cases
… `O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})`").  One dimension only: the level-`ℓ`
correction is a function `f_ℓ` of one uniform input `u ∈ [0, 1]`; QMC error theory in `d`
dimensions (Koksma–Hlawka, low-discrepancy and Sobol points) is not formalised.  Assume
* each `f_ℓ` has bounded variation on `[0, 1]`, with total variation `V_ℓ ≤ c₂ 2^{−bℓ}`;
* the bias at finest level `L` is `|∑_{ℓ≤L} ∫_0^1 f_ℓ − I| ≤ c₁ 2^{−aL}`;
* a point on level `ℓ` costs `C_ℓ ≤ c₃ 2^{gℓ}`, with `a > 0`, `g ≤ a` and `g ≤ b` (no sign
  conditions on `g` or on the constants `c₁, c₂, c₃`);
* the shifts `U_0, U_1, …` (one per level) are pairwise independent and uniform on `[0, 1]`.
Then there is `K > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the
MLQMC estimator `Y = ∑_{ℓ≤L} N_ℓ⁻¹ ∑_{i<N_ℓ} f_ℓ((i + U_ℓ)/N_ℓ)` has `E[(Y − I)²] < ε²` and cost
`∑_{ℓ≤L} N_ℓ C_ℓ ≤ K ε⁻¹ |log ε|^{3/2}` (so `O(ε^{−p})` for every `p > 1`).
This is the regime `b = g ≤ a` left out by `mlqmc_complexity` (which gives `O(ε⁻¹)` when `g < b`);
when the rates are attained with `b = g` the bound is sharp (`mlqmc_boundary_cost_lower`,
`mlqmc_boundary_exponents_optimal`).  Proof:
`mlqmc_boundary_complexity_core` and `mlqmc_mse_le`. -/
theorem mlqmc_boundary_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : ℕ → Ω → ℝ} (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ (volume.restrict (Set.Icc 0 1)))
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → ℝ → ℝ}
    (hf : ∀ ℓ, BoundedVariationOn (f ℓ) (Set.Icc 0 1)) {C : ℕ → ℝ} {I a b g c₁ c₂ c₃ : ℝ}
    (ha : 0 < a) (hga : g ≤ a) (hgb : g ≤ b)
    (hbias : ∀ L : ℕ, |∑ ℓ ∈ range (L + 1), (∫ y in (0 : ℝ)..1, f ℓ y) - I| ≤
      c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))))
    (hV : ∀ ℓ : ℕ, (eVariationOn (f ℓ) (Set.Icc 0 1)).toReal ≤ c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))))
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) → ∃ (L : ℕ) (N : ℕ → ℕ),
      (∀ ℓ, 0 < N ℓ) ∧
      ∫ ω, (∑ ℓ ∈ range (L + 1), latticeRule (f ℓ) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ < ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ K * ε⁻¹ * (-Real.log ε) ^ ((3 : ℝ) / 2) := by
  obtain ⟨K, hK, hcore⟩ := mlqmc_boundary_complexity_core ha hga hgb
    (lt_max_of_lt_right one_pos : (0 : ℝ) < max c₁ 1)
    (lt_max_of_lt_right one_pos : (0 : ℝ) < max c₂ 1)
    (lt_max_of_lt_right one_pos : (0 : ℝ) < max c₃ 1)
  refine ⟨K, hK, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := hcore ε hε hε1
  refine ⟨L, N, hN, (mlqmc_mse_le hU hUind hf hN
    (le_max_one_mul (by positivity) (hbias L))
    (v := fun ℓ => max c₂ 1 * (2 : ℝ) ^ (-(b * (ℓ : ℝ))))
    (fun ℓ => le_max_one_mul (by positivity) (hV ℓ))).trans_lt hmse, ?_⟩
  calc ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ
      ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (max c₃ 1 * (2 : ℝ) ^ (g * (ℓ : ℝ))) :=
        sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left
          (le_max_one_mul (by positivity) (hC ℓ)) (Nat.cast_nonneg _)
    _ ≤ _ := hcost

/-! ### The lower bounds -/

/-- **Every allocation costs `≥ k ε⁻¹ |log ε|^{3/2}` when `b ≤ g`** (the converse of the MLQMC
complexity in the boundary case; Giles 2015, §2.7, p. 20: "a complexity which is `O(ε^{−p})` with
`p < 2`").  The paper states no lower bound: this result goes beyond it, and shows that in the
one-dimensional boundary case its `p < 2` cannot be improved to `p = 1` without the factor
`|log ε|^{3/2}`.  One dimension only, as in `mlqmc_boundary_complexity_core`, with the level errors
and costs attained: level-`ℓ` root-mean-square error exactly `c₂ 2^{−bℓ}/N_ℓ` and cost `c₃ 2^{gℓ}`
per point with `b ≤ g` (the boundary case is `b = g`; a slower decay `b < g` only makes the level
errors larger), bias `c₁ 2^{−aL}`.  Only `c₁ ≠ 0`, `c₂ ≠ 0` and `c₃ > 0` are assumed, with any
`a, g ∈ ℝ` (the model's standing assumptions `a > 0`, `c₁, c₂ > 0` are not needed: for `a ≤ 0`
the bias condition forces `|c₁| < ε`; for `c₁ = 0` the single level `L = 0` costs `O(ε⁻¹)`, and
for `c₂ = 0` the cost can be arbitrarily small).  There is `k > 0` (depending only on `a`, `c₁`,
`c₂`, `c₃`) such that for every `0 < ε < 1`, every `L` and every real allocation with `N_ℓ > 0`
for `ℓ ≤ L` (in particular every `N_ℓ ∈ ℕ`, `N_ℓ ≥ 1`) with
`(c₁ 2^{−aL})² + ∑_{ℓ≤L} (c₂ 2^{−bℓ}/N_ℓ)² ≤ ε²` (so also for `< ε²`), the cost is
`∑_{ℓ≤L} N_ℓ c₃ 2^{gℓ} ≥ k ε⁻¹ |log ε|^{3/2}`.  So for `b = g` the exponents of `ε` and of
`|log ε|` in `mlqmc_boundary_complexity_core` cannot be improved
(`mlqmc_boundary_exponents_optimal`).  Proof: `2^{−gℓ} ≤ 2^{−bℓ}` reduces to `b = g`; with
`x_ℓ = |c₂| 2^{−gℓ}/N_ℓ > 0` the cost is `|c₂| c₃ ∑ x_ℓ⁻¹`, and Hölder's inequality
(`mlqmc_boundary_card_mul_sqrt_le`) gives `(L + 1)^{3/2} ≤ ε ∑ x_ℓ⁻¹`; since `∑ x_ℓ² > 0`, the
bias satisfies `|c₁| 2^{−aL} < ε`, which gives `L + 1 ≥ k₀ |log ε|` with
`k₀ = min(1/(2 max(a, 1) log 2), 1/(2|log |c₁|| + 1))` (`mlqmc_boundary_level_add_one_ge`), and
`k = |c₂| c₃ k₀^{3/2}`. -/
theorem mlqmc_boundary_cost_lower {a b g c₁ c₂ c₃ : ℝ} (hbg : b ≤ g) (hc₁ : c₁ ≠ 0)
    (hc₂ : c₂ ≠ 0) (hc₃ : 0 < c₃) :
    ∃ k : ℝ, 0 < k ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (L : ℕ) (N : ℕ → ℝ), (∀ ℓ ≤ L, 0 < N ℓ) →
      (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N ℓ) ^ 2 ≤ ε ^ 2 →
        k * ε⁻¹ * (-Real.log ε) ^ ((3 : ℝ) / 2) ≤
          ∑ ℓ ∈ range (L + 1), N ℓ * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) := by
  have hc₁' : 0 < |c₁| := abs_pos.2 hc₁
  have hc₂' : 0 < |c₂| := abs_pos.2 hc₂
  set k₀ : ℝ := min (1 / (2 * max a 1 * Real.log 2)) (1 / (2 * |Real.log c₁| + 1))
  have hm : 0 < max a 1 := lt_max_of_lt_right one_pos
  have hk₀ : 0 < k₀ := lt_min (by positivity) (by positivity)
  refine ⟨|c₂| * c₃ * (k₀ * Real.sqrt k₀), by positivity, fun ε hε hε1 L N hN hmse' => ?_⟩
  have ht : 0 < -Real.log ε := neg_pos.2 (Real.log_neg hε hε1)
  have hNr : ∀ ℓ ∈ range (L + 1), 0 < N ℓ := fun ℓ hℓ =>
    hN ℓ (Nat.lt_add_one_iff.1 (mem_range.1 hℓ))
  -- the slower decay `b ≤ g` only increases the level errors
  have hmse : (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 +
      ∑ ℓ ∈ range (L + 1), (|c₂| * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) / N ℓ) ^ 2 ≤ ε ^ 2 := by
    refine le_trans (add_le_add le_rfl (sum_le_sum fun ℓ hℓ => ?_)) hmse'
    have h2 := two_rpow_neg_mul_le hbg ℓ
    have hN0 := (hNr ℓ hℓ).le
    simp only [div_pow, mul_pow, sq_abs]
    gcongr
  have hx : ∀ ℓ ∈ range (L + 1), 0 < |c₂| * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) / N ℓ := fun ℓ hℓ =>
    div_pos (mul_pos hc₂' (Real.rpow_pos_of_pos two_pos _)) (hNr ℓ hℓ)
  have hsum0 : 0 < ∑ ℓ ∈ range (L + 1), (|c₂| * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) / N ℓ) ^ 2 :=
    sum_pos (fun ℓ hℓ => pow_pos (hx ℓ hℓ) 2) nonempty_range_add_one
  -- the bias condition and the number of levels
  have hbias : |c₁| * (2 : ℝ) ^ (-(a * (L : ℝ))) < ε := by
    have h1 := abs_lt_of_sq_lt_sq
      (show (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 < ε ^ 2 by linarith) hε.le
    rwa [abs_mul, abs_of_pos (Real.rpow_pos_of_pos two_pos _)] at h1
  have hlev := mlqmc_boundary_level_add_one_ge hc₁' hε hε1 hbias
  rw [Real.log_abs] at hlev
  -- Hölder's inequality
  have hvar : ∑ ℓ ∈ range (L + 1), (|c₂| * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) / N ℓ) ^ 2 ≤ ε ^ 2 := by
    linarith [sq_nonneg (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))))]
  have hhol := mlqmc_boundary_card_mul_sqrt_le (range (L + 1)) hε hx hvar
  rw [card_range] at hhol
  push_cast at hhol
  have hcost : ∑ ℓ ∈ range (L + 1), N ℓ * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) =
      |c₂| * c₃ * ∑ ℓ ∈ range (L + 1), (|c₂| * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) / N ℓ)⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl fun ℓ hℓ => ?_
    have hN0 := (hNr ℓ hℓ).ne'
    have hc0 := hc₂'.ne'
    have hp0 : (2 : ℝ) ^ (g * (ℓ : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
    rw [Real.rpow_neg zero_le_two, inv_div]
    field_simp
  have hsq : Real.sqrt k₀ * Real.sqrt (-Real.log ε) ≤ Real.sqrt ((L : ℝ) + 1) := by
    rw [← Real.sqrt_mul hk₀.le]
    exact Real.sqrt_le_sqrt hlev
  have hprod : (k₀ * Real.sqrt k₀) * ((-Real.log ε) * Real.sqrt (-Real.log ε)) ≤
      ((L : ℝ) + 1) * Real.sqrt ((L : ℝ) + 1) := by
    calc (k₀ * Real.sqrt k₀) * ((-Real.log ε) * Real.sqrt (-Real.log ε))
        = (k₀ * (-Real.log ε)) * (Real.sqrt k₀ * Real.sqrt (-Real.log ε)) := by ring
      _ ≤ ((L : ℝ) + 1) * Real.sqrt ((L : ℝ) + 1) :=
          mul_le_mul hlev hsq (by positivity) (by positivity)
  rw [mlqmc_boundary_rpow_three_halves ht.le, hcost]
  have hεi : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
  calc |c₂| * c₃ * (k₀ * Real.sqrt k₀) * ε⁻¹ * ((-Real.log ε) * Real.sqrt (-Real.log ε))
      = |c₂| * c₃ * ε⁻¹ * ((k₀ * Real.sqrt k₀) * ((-Real.log ε) * Real.sqrt (-Real.log ε))) := by
        ring
    _ ≤ |c₂| * c₃ * ε⁻¹ * (((L : ℝ) + 1) * Real.sqrt ((L : ℝ) + 1)) := by gcongr
    _ ≤ |c₂| * c₃ * ε⁻¹ * (ε * ∑ ℓ ∈ range (L + 1),
          (|c₂| * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) / N ℓ)⁻¹) := by gcongr
    _ = _ := by
        rw [show |c₂| * c₃ * ε⁻¹ * (ε * ∑ ℓ ∈ range (L + 1),
            (|c₂| * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) / N ℓ)⁻¹) = |c₂| * c₃ * (ε⁻¹ * ε) *
              ∑ ℓ ∈ range (L + 1), (|c₂| * (2 : ℝ) ^ (-(g * (ℓ : ℝ))) / N ℓ)⁻¹ by ring, hεi,
          mul_one]

/-- **Both exponents of the boundary-case MLQMC complexity are sharp** (Giles 2015, §2.7, p. 20:
"a complexity which is `O(ε^{−p})` with `p < 2`"; here, for `b = g`, the exact order).  The paper
states no lower bound: this result goes beyond it, and shows that in the one-dimensional boundary
case its `p < 2` cannot be improved to `p = 1` without a logarithmic factor, nor the factor
`|log ε|^{3/2}` to a smaller power.  One dimension only, in the attained model of
`mlqmc_boundary_cost_lower` (`b ≤ g`, the boundary case being `b = g`; `c₁, c₂ ≠ 0`, `c₃ > 0`, any
`a` and `g`).  If `p < 1` (any `q`), or `p = 1` and `q < 3/2`, there are no `K` and `ε₀ > 0` such
that every `0 < ε < ε₀` admits `L` and `N_ℓ ≥ 1` with
`(c₁ 2^{−aL})² + ∑_{ℓ≤L} (c₂ 2^{−bℓ}/N_ℓ)² ≤ ε²` (a fortiori with `< ε²`) and cost
`∑_{ℓ≤L} N_ℓ c₃ 2^{gℓ} ≤ K ε^{−p} |log ε|^q`.  Together with `mlqmc_boundary_complexity_core`
(achievable with `p = 1`, `q = 3/2` when `g ≤ a`) the optimal cost is `Θ(ε⁻¹ |log ε|^{3/2})`.
Proof: `mlqmc_boundary_cost_lower` gives `k ε⁻¹ |log ε|^{3/2} ≤ K ε^{−p} |log ε|^q` for all small
`ε`, which fails for some small `ε` (`mlqmc_boundary_exists_eps_lt`). -/
theorem mlqmc_boundary_exponents_optimal {a b g c₁ c₂ c₃ p q : ℝ} (hbg : b ≤ g)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : 0 < c₃) (hpq : p < 1 ∨ (p = 1 ∧ q < 3 / 2)) :
    ¬ ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ (L : ℕ) (N : ℕ → ℕ),
      (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N ℓ) ^ 2 ≤ ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          K * ε ^ (-p) * (-Real.log ε) ^ q := by
  rintro ⟨K, ε₀, hε₀, h⟩
  obtain ⟨k, hk, hlow⟩ := mlqmc_boundary_cost_lower (a := a) hbg hc₁ hc₂ hc₃
  obtain ⟨ε, hε, hεε₀, hε1, hlt⟩ :=
    mlqmc_boundary_exists_eps_lt (K := K) (q' := (3 : ℝ) / 2) hk hε₀ hpq
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hεε₀
  have hlow' : k * ε⁻¹ * (-Real.log ε) ^ ((3 : ℝ) / 2) ≤
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :=
    hlow ε hε hε1 L (fun ℓ => (N ℓ : ℝ)) (fun ℓ _ => Nat.cast_pos.2 (hN ℓ)) hmse
  rw [Real.rpow_neg_one] at hlt
  linarith

/-- **The points on the finest level cost `≥ c₃ (|c₁|/ε)^{g/a}`** (Giles 2015, §2.7, p. 20:
"under certain conditions they lead to multilevel methods with a complexity which is `O(ε^{−p})`
with `p < 2`").  The paper states no lower bound: this result goes beyond it, and shows that its
"certain conditions" must include `g < 2a` (see `mlqmc_finest_level_exponent_optimal`).  One
dimension only, in the model of `mlqmc_boundary_complexity_core`: bias `c₁ 2^{−aL}` at finest
level `L` and cost `c₃ 2^{gℓ}` per point on level `ℓ`, with `a > 0` (the model's standing
assumption, which makes the exponent `g/a` meaningful; the bound fails for `a < 0`), `g ≥ 0` and
`c₃ ≥ 0`; any `c₁`.  If
`0 < ε`, `N_ℓ ≥ 0` for `ℓ ≤ L`, at least one point is used on the finest level (`N_L ≥ 1`), and the
bias is `|c₁| 2^{−aL} ≤ ε` (which holds whenever the mean square error
`(c₁ 2^{−aL})² + ∑_{ℓ≤L} (c₂ 2^{−bℓ}/N_ℓ)²` is `≤ ε²`), then
`∑_{ℓ≤L} N_ℓ c₃ 2^{gℓ} ≥ c₃ 2^{gL} ≥ c₃ (|c₁|/ε)^{g/a}`.  For `g < 0` the bound fails (with
`N_ℓ = 0` for `ℓ < L` and `L` large the cost `c₃ 2^{gL}` is small).  Proof: `2^{aL} ≥ |c₁|/ε`, so
`2^{gL} = (2^{aL})^{g/a} ≥ (|c₁|/ε)^{g/a}` (`Real.rpow_le_rpow`), and the cost is at least its
level-`L` term (`Finset.single_le_sum`). -/
theorem mlqmc_finest_level_cost_lower {a g c₁ c₃ : ℝ} (ha : 0 < a) (hg : 0 ≤ g) (hc₃ : 0 ≤ c₃) :
    ∀ ε : ℝ, 0 < ε → ∀ (L : ℕ) (N : ℕ → ℝ), (∀ ℓ ≤ L, 0 ≤ N ℓ) → 1 ≤ N L →
      |c₁| * (2 : ℝ) ^ (-(a * (L : ℝ))) ≤ ε →
        c₃ * (|c₁| / ε) ^ (g / a) ≤
          ∑ ℓ ∈ range (L + 1), N ℓ * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) := by
  intro ε hε L N hN hNL hbias
  have hp : 0 < (2 : ℝ) ^ (a * (L : ℝ)) := Real.rpow_pos_of_pos two_pos _
  have h1 : |c₁| / ε ≤ (2 : ℝ) ^ (a * (L : ℝ)) := by
    rw [Real.rpow_neg zero_le_two, ← div_eq_mul_inv, div_le_iff₀ hp] at hbias
    rw [div_le_iff₀ hε]
    linarith
  have h2 : (|c₁| / ε) ^ (g / a) ≤ (2 : ℝ) ^ (g * (L : ℝ)) := by
    calc (|c₁| / ε) ^ (g / a) ≤ ((2 : ℝ) ^ (a * (L : ℝ))) ^ (g / a) :=
          Real.rpow_le_rpow (by positivity) h1 (div_nonneg hg ha.le)
      _ = (2 : ℝ) ^ (g * (L : ℝ)) := by
          rw [← Real.rpow_mul zero_le_two]
          congr 1
          field_simp
  have hterm : ∀ ℓ ∈ range (L + 1), 0 ≤ N ℓ * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) := fun ℓ hℓ =>
    mul_nonneg (hN ℓ (Nat.lt_add_one_iff.1 (mem_range.1 hℓ))) (by positivity)
  calc c₃ * (|c₁| / ε) ^ (g / a) ≤ c₃ * (2 : ℝ) ^ (g * (L : ℝ)) := by gcongr
    _ ≤ N L * (c₃ * (2 : ℝ) ^ (g * (L : ℝ))) := le_mul_of_one_le_left (by positivity) hNL
    _ ≤ _ := single_le_sum hterm (self_mem_range_succ L)

/-- **The cost exponent is at least `g/a`; the condition `g ≤ a` is necessary** (Giles 2015, §2.7,
p. 20: "under certain conditions they lead to multilevel methods with a complexity which is
`O(ε^{−p})` with `p < 2`").  The paper states no lower bound: this result goes beyond it.  It
shows that the "certain conditions" must include `g < 2a` (for `g ≥ 2a` no `p < 2` is possible),
that the condition `g ≤ a` of `mlqmc_boundary_complexity_core` cannot be dropped (for `a < g` even
`p = 1` with any power of `|log ε|` fails), and that the order `ε^{−g/a}` of
`mlqmc_complexity_core` (`a ≤ b`, `a < g`) is sharp.  One dimension only, in the model of
`mlqmc_boundary_complexity_core` with the bias and costs attained: `a > 0` (the model's standing
assumption, which makes `g/a` meaningful; for `a ≤ 0` no allocation exists once `ε < |c₁|`),
`c₁ ≠ 0` (for `c₁ = 0` the single level `L = 0` costs `O(ε⁻¹)`), `c₃ > 0`, and any `b`, `c₂`,
`g`.  If `p < g/a` (any `q`), or `p = g/a` and `q < 0`,
there are no `K` and `ε₀ > 0` such that every `0 < ε < ε₀` admits `L` and `N_ℓ ≥ 1` with
`(c₁ 2^{−aL})² + ∑_{ℓ≤L} (c₂ 2^{−bℓ}/N_ℓ)² ≤ ε²` (a fortiori with `< ε²`) and cost
`∑_{ℓ≤L} N_ℓ c₃ 2^{gℓ} ≤ K ε^{−p} |log ε|^q`.  Proof: for `g ≥ 0`,
`mlqmc_finest_level_cost_lower` gives the cost `≥ c₃ |c₁|^{g/a} ε^{−g/a}`; for `g < 0` (then
`p < 0`) the level-`0` term gives the cost `≥ c₃`; either bound fails the assumed one for some
small `ε` (`mlqmc_boundary_exists_eps_lt`). -/
theorem mlqmc_finest_level_exponent_optimal {a b g c₁ c₂ c₃ p q : ℝ} (ha : 0 < a)
    (hc₁ : c₁ ≠ 0) (hc₃ : 0 < c₃) (hpq : p < g / a ∨ (p = g / a ∧ q < 0)) :
    ¬ ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ (L : ℕ) (N : ℕ → ℕ),
      (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N ℓ) ^ 2 ≤ ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          K * ε ^ (-p) * (-Real.log ε) ^ q := by
  rintro ⟨K, ε₀, hε₀, h⟩
  have hc₁' : 0 < |c₁| := abs_pos.2 hc₁
  rcases le_or_gt 0 g with hg | hg
  · -- `g ≥ 0`: the finest level alone costs `≥ c₃ |c₁|^{g/a} ε^{−g/a}`
    obtain ⟨ε, hε, hεε₀, -, hlt⟩ := mlqmc_boundary_exists_eps_lt (K := K)
      (k := c₃ * |c₁| ^ (g / a)) (q' := 0) (mul_pos hc₃ (Real.rpow_pos_of_pos hc₁' _)) hε₀ hpq
    obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hεε₀
    have hbias : |c₁| * (2 : ℝ) ^ (-(a * (L : ℝ))) ≤ ε := by
      have h0 : 0 ≤ ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N ℓ) ^ 2 :=
        sum_nonneg fun ℓ _ => sq_nonneg _
      have h1 := abs_le_of_sq_le_sq
        (show (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 ≤ ε ^ 2 by linarith) hε.le
      rwa [abs_mul, abs_of_pos (Real.rpow_pos_of_pos two_pos _)] at h1
    have hlow : c₃ * (|c₁| / ε) ^ (g / a) ≤
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :=
      mlqmc_finest_level_cost_lower ha hg hc₃.le ε hε L (fun ℓ => (N ℓ : ℝ))
        (fun ℓ _ => Nat.cast_nonneg _) (Nat.one_le_cast.2 (hN L)) hbias
    rw [Real.div_rpow hc₁'.le hε.le, div_eq_mul_inv, ← mul_assoc] at hlow
    rw [Real.rpow_zero, mul_one, Real.rpow_neg hε.le (g / a)] at hlt
    linarith
  · -- `g < 0`: then `p < 0`, and the coarsest level alone costs `≥ c₃`
    have hga : g / a < 0 := div_neg_of_neg_of_pos hg ha
    have hp : p < 0 ∨ (p = 0 ∧ q < 0) := Or.inl (by rcases hpq with h | ⟨h, -⟩ <;> linarith)
    obtain ⟨ε, hε, hεε₀, -, hlt⟩ := mlqmc_boundary_exists_eps_lt (K := K)
      (k := c₃) (q' := 0) hc₃ hε₀ hp
    obtain ⟨L, N, hN, -, hcost⟩ := h ε hε hεε₀
    simp only [neg_zero, Real.rpow_zero, mul_one] at hlt
    have hterm : ∀ ℓ ∈ range (L + 1), 0 ≤ (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :=
      fun ℓ _ => by positivity
    have h0 := single_le_sum hterm (mem_range.2 (Nat.succ_pos L))
    rw [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at h0
    have hN0 : c₃ ≤ (N 0 : ℝ) * c₃ := le_mul_of_one_le_left hc₃.le (Nat.one_le_cast.2 (hN 0))
    linarith

end MLMC
