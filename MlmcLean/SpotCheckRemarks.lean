import MlmcLean.InverseNormal
import MlmcLean.SDEExtras
import MlmcLean.ML2RTheorem
import MlmcLean.GBMWeakOrder

/-!
# Small items from the spot checks of Giles 2015 (§§2.3–10.2) and Haas–Giles 2025 (§2.1)

References: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015) 259–328
(`docs/giles2015.txt`; the line numbers below refer to it), and I.-B. Haas, M.B. Giles, *A nested
MLMC framework for efficient simulations on FPGAs*, arXiv:2502.07123 (2025)
(`docs/haas_giles2025.txt`, tex `docs/haas_giles2025_arxiv_src/sections/`).

* **§2.3, ML2R** (pp. 11–12, l. 529–543: "… `= O(2^{−αL²})`"): `ml2r_bias_not_attainable`.  The
  level means `E[P_ℓ] = E[P] + d [ℓ = 0]` satisfy the weak-error expansion with `a = 0` and the
  `L`-independent constant `K = |d|`, exactly as `ml2r_theorem_eq` assumes, and their ML2R bias is
  `w_0 d` with `|w_0| = r^{L(L+1)/2}/∏_{k=1}^{L}(1 − r^k)`, `r = 2^{−α}`: it is at least
  `|d| 2^{−αL(L+1)/2}` and is not `O(2^{−αL²})`.
* **§5.7, smoothed CDF** (p. 46, l. 1985–1993): `variance_smoothCDF_correction_le`, the bound
  `V[g((x − P_ℓ)/δ) − g((x − P_{ℓ−1})/δ)] ≤ (Lip g/δ)² E[(P_ℓ − P_{ℓ−1})²]`, and
  `tendsto_variance_smoothCDF_correction`: as `δ → 0` this variance tends to that of the
  indicator correction `1_{P_ℓ<x} − 1_{P_{ℓ−1}<x}`.
* **§7.1, the explicit heat scheme with Dirichlet boundary values** (p. 51, l. 2190–2201):
  `dirichletHeatStep`, `dirichletHeat_stable` (max-norm non-expansive for `0 ≤ λ ≤ ½`, with the
  noise), `dirichletHeatStep_sin` (the discrete sine modes) and `dirichletHeat_unstable` (an
  unstable mode for every `λ > ½` on fine grids).  `MlmcLean.PDEExamples` has the scheme on `ℤ`.
* **§7.2, nested inputs** (p. 53, l. 2263–2273): `nested_inputs_mlmc` (`ξ_ℓ = (ξ_{ℓ−1}, z_ℓ)` with
  an independent block `z_ℓ`) and `nested_vector_inputs_mlmc` (truncated vectors of independent
  variables): the coarse payoff on the truncated fine input has the law of the coarse level's
  payoff, hence (2.4) and the telescoping sum.
* **§9.1, standard nested Monte Carlo** (p. 57, l. 2462–2474): `nested_mc_cost_upper` (the
  explicit `M = max(1, ⌈2c/ε⌉)`, `N = max(1, ⌈2v/ε²⌉)` reach the mean square error `ε²` at cost
  `N M ≤ (2v + 1)(2c + 1)ε⁻³`) and `nested_mc_cost_lower` (every `N, M` that reach it cost at
  least `c v ε⁻³`): with bias `c/M` and variance `v/N` the cost `N M` is `Θ(ε⁻³)`.
* **§10.1, contracting SDEs** (p. 61, l. 2738–2743): for the Ornstein–Uhlenbeck SDE the
  Euler–Maruyama chain `X_{n+1} = (1 − κh)X_n + σ√h Z_n` has the unique invariant law
  `N(0, σ²/(κ(2 − κh)))` for `0 < κh < 2` (`ouEM_invariant`), which tends to `N(0, σ²/(2κ))` as
  `h → 0` (`tendsto_ouEM_invariant`).
* **§10.2, reduced-precision inputs** (p. 62, l. 2775–2781):
  `tendstoInDistribution_normCDFInv_midpoint`: with the corrected `U = (I + ½)/(I_max + 1)` and
  `I` uniform on `{0, …, I_max}`, `Φ⁻¹(U)` tends in distribution to `N(0, 1)`; the printed
  `U = (I + ½)/I_max` exceeds `1` at `I = I_max`.
* **Haas–Giles 2025, §2.1** (p. 3, l. 159–164): for GBM, Euler–Maruyama and the Lipschitz payoff
  `g(x) = x`, `s₀²σ⁴T²e^{−4|r|T}/4 · 2^{−ℓ} ≤ V_{ℓ+1} ≤ 6C(T)T 2^{−(ℓ+1)}` if `|r|T ≤ 2^ℓ`
  (`gbm_em_identity_variance_two_sided`) and `V_{ℓ+1} ≥ s₀²(σ²T 2^{−(ℓ+1)})^{2^{ℓ+1}}` at every
  level (`gbm_em_identity_variance_ge_pow`), so `V_ℓC_ℓ` with `C_ℓ = 2^ℓ` stays between two positive
  constants at all levels (`gbm_em_identity_variance_cost`).  So the paper's case "`V_ℓC_ℓ`
  decreases with level", read as the geometric decay (`β > γ`) that gives the cost
  `≈ ε⁻²V_0C_0`, does not hold for the Euler–Maruyama scheme: `V_ℓC_ℓ` does not tend to `0`.  It
  can increase with `ℓ` (`r = 0.05`, `σ = 0.2`, `T = 1`) or decrease towards a positive limit
  (`r = −0.5`, `σ = 0.2`, `T = 1`: monotonically for `ℓ ≤ 13`); either way the cost (8) is of
  order `ε⁻²(L + 1)²`.

Not in this file: the §7.1 (p. 49) corollary "no deterministic `K` with `|P − P_ℓ| ≤ K h_ℓ²` almost
surely" for the elliptic example itself is already `not_ae_abs_ellipticP_sub_le`
(`MlmcLean.EllipticFD`).

**Deviations.**  §5.7: the variance bound assumes `g` Lipschitz (the paper's `g` is only
continuous); the limit statement uses exactly the paper's `g` and assumes no atom of `P_ℓ`,
`P_{ℓ−1}` at `x`.  §7.1: the Dirichlet scheme is on the grid `j = 0, …, J`; the instability
needs `J ≥ J₀(λ)` (with one interior node the step is `u_1 ↦ (1 − 2λ)u_1`, stable up to `λ = 1`).
§9.1: the nested estimator is modelled by its outer samples `P_M` with the bias and variance
rates as hypotheses (for smooth `f`, `nested_bias_rate` of `MlmcLean.NestedMLMC` gives the bias
rate for `M = 2^ℓ`).
§10.1: only the discretised chain is treated; that `σ²/(2κ)` is the variance of the stationary
law of the SDE is not proved (SDE theory).  §10.2: `I_max` is the index `n` of the sequence.
HG §2.1: the explicit lower bound `∝ 2^{−ℓ}` is proved for the levels with `|r|T ≤ 2^ℓ` (all
levels if `r = 0`; numerically it holds at every level); at the finitely many other levels the
variance is still positive, which is all the cost statement needs.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

namespace MLMC

/-! ### §2.3: the ML2R bias rate `2^{−αL²}` is not attained -/

section ml2r

/-- `{0, …, L} ∖ {0} = {1, …, L}` (for the ML2R weight `w_0`, Giles 2015, §2.3). -/
lemma range_succ_erase_zero (L : ℕ) : (range (L + 1)).erase 0 = Icc 1 L := by
  ext k
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
  omega

/-- The ML2R nodes `x_k = 2^{−αk}`, `k ≥ 1`, lie in `(0, 1)` for `α > 0` (Giles 2015, §2.3). -/
lemma ml2rNode_mem_Ioo {α : ℝ} (hα : 0 < α) {k : ℕ} (hk : 1 ≤ k) :
    ml2rNode α k ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [ml2rNode_eq]
  have hr0 : 0 < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos two_pos _
  have hr1 : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  exact ⟨pow_pos hr0 k, pow_lt_one₀ hr0.le hr1 (by omega)⟩

/-- The weight of the coarsest level in ML2R (Giles 2015, §2.3, p. 11): with `r = 2^{−α}`,
`|w_0| = ∏_{k=1}^{L} r^k/(1 − r^k) = r^{L(L+1)/2}/∏_{k=1}^{L}(1 − r^k)`. -/
lemma abs_ml2rWeight_zero {α : ℝ} (hα : 0 < α) (L : ℕ) :
    |ml2rWeight α L 0| = (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) /
      ∏ k ∈ Icc 1 L, (1 - ml2rNode α k) := by
  have h0 : ml2rNode α 0 = 1 := by simp [ml2rNode]
  have hprod : ∏ k ∈ Icc 1 L, ml2rNode α k = (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) := by
    rw [← prod_ml2rNode, ← range_succ_erase_zero, ← Finset.prod_erase_mul _ _
      (Finset.mem_range.2 (Nat.succ_pos L)), h0, mul_one]
  rw [ml2rWeight, range_succ_erase_zero, Finset.abs_prod, ← hprod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk1 := ml2rNode_mem_Ioo hα (Finset.mem_Icc.1 hk).1
  rw [h0, abs_div, abs_of_pos hk1.1, abs_of_neg (by linarith [hk1.2]), neg_sub]

/-- **The printed ML2R bias rate `2^{−αL²}` is not attained** (Giles 2015, §2.3, pp. 11–12,
l. 529–543: "Assuming that the weak error has a regular expansion
`E[P_ℓ] − E[P] = ∑_{n=1}^{L} a_n 2^{−nαℓ} + O(2^{−αℓL})` … so that
`(∑_{ℓ=0}^{L} w_ℓ E[P_ℓ]) − E[P] = ∑_{ℓ=0}^{L} w_ℓ (E[P_ℓ] − E[P]) = O(2^{−αL²})`").  Let `α > 0`,
`d ≠ 0` and let the level means be `E[P_ℓ] = E[P] + d [ℓ = 0]` (`EPl ℓ`, `EP`; for instance
constant `P_ℓ`: an inexact coarsest level and exact finer levels).  Then
1. the expansion holds for every `L` with `a = 0` and the `L`-independent constant `K = |d|`, in
   the form of the hypothesis `hexp` of `ml2r_theorem_eq`:
   `|E[P_ℓ] − E[P] − ∑_{n=1}^{L} 0 · 2^{−nαℓ}| ≤ |d| 2^{−αℓL}` for `ℓ ≤ L`;
2. the ML2R bias is exactly `w_0 d` (`w = ml2rWeight α L`);
3. `|w_0| = 2^{−αL(L+1)/2}/∏_{k=1}^{L}(1 − 2^{−αk})`;
4. so the bias is at least `|d| 2^{−αL(L+1)/2}`: the rate of `ml2r_bias_le` is attained;
5. and `|bias_L| / 2^{−αL²} → ∞`: the bias is not `O(2^{−αL²})`.
Unlike the example in the docstring of `ml2r_bias_le` (`E[P_ℓ] − E[P] = 2^{−α(L+1)ℓ}`, which depends
on `L`), this one sequence of level means satisfies the expansion uniformly in `L`, as
`ml2r_theorem_eq` and `ml2r_theorem_lt` assume, so the corrected rate in those theorems is needed
under their own hypotheses. -/
theorem ml2r_bias_not_attainable {α : ℝ} (hα : 0 < α) {EP d : ℝ} (hd : d ≠ 0) {EPl : ℕ → ℝ}
    (hEPl : ∀ ℓ, EPl ℓ = EP + if ℓ = 0 then d else 0) :
    (∀ L : ℕ, ∀ ℓ ≤ L, |EPl ℓ - EP - ∑ n ∈ Icc 1 L, (0 : ℝ) * ml2rNode α ℓ ^ n| ≤
      |d| * ml2rNode α ℓ ^ L) ∧
    (∀ L : ℕ, ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * EPl ℓ - EP = ml2rWeight α L 0 * d) ∧
    (∀ L : ℕ, |ml2rWeight α L 0| = (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) /
      ∏ k ∈ Icc 1 L, (1 - ml2rNode α k)) ∧
    (∀ L : ℕ, |d| * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) ≤
      |∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * EPl ℓ - EP|) ∧
    Tendsto (fun L : ℕ => |∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * EPl ℓ - EP| /
      (2 : ℝ) ^ (-(α * (L : ℝ) ^ 2))) atTop atTop := by
  have hexp : ∀ L, ∀ ℓ ≤ L, |EPl ℓ - EP - ∑ n ∈ Icc 1 L, (0 : ℝ) * ml2rNode α ℓ ^ n| ≤
      |d| * ml2rNode α ℓ ^ L := fun L ℓ _ => by
    simp only [zero_mul, Finset.sum_const_zero, sub_zero, hEPl, add_sub_cancel_left]
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · subst h
      simp [ml2rNode]
    · rw [if_neg h.ne', abs_zero]
      exact mul_nonneg (abs_nonneg d) (pow_nonneg (ml2rNode_mem_Ioo hα h).1.le L)
  have hbias : ∀ L, ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * EPl ℓ - EP =
      ml2rWeight α L 0 * d := fun L => by
    have hsum1 : ∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ = 1 := by
      have h := (ml2r_weights hα L).1 0 (Nat.zero_le L)
      simpa using h
    simp only [hEPl, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum1, one_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.succ_pos L, if_true]
    ring
  have hw := abs_ml2rWeight_zero hα
  have hlow : ∀ L : ℕ, |d| * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) ≤
      |∑ ℓ ∈ range (L + 1), ml2rWeight α L ℓ * EPl ℓ - EP| := fun L => by
    rw [hbias L, abs_mul, hw L, mul_comm]
    have hpos : 0 < ∏ k ∈ Icc 1 L, (1 - ml2rNode α k) := Finset.prod_pos fun k hk => by
      linarith [(ml2rNode_mem_Ioo hα (Finset.mem_Icc.1 hk).1).2]
    have hle : ∏ k ∈ Icc 1 L, (1 - ml2rNode α k) ≤ 1 := Finset.prod_le_one
      (fun k hk => by linarith [(ml2rNode_mem_Ioo hα (Finset.mem_Icc.1 hk).1).2])
      (fun k hk => by linarith [(ml2rNode_mem_Ioo hα (Finset.mem_Icc.1 hk).1).1])
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg d)
    exact le_div_self (Real.rpow_nonneg (by norm_num) _) hpos hle
  refine ⟨hexp, hbias, hw, hlow, ?_⟩
  -- the ratio to `2^{−αL²}` is at least `|d| 2^{−α} (2^α)^L`
  have h2a : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow one_lt_two hα
  have hdpos : 0 < |d| * (2 : ℝ) ^ (-α) :=
    mul_pos (abs_pos.2 hd) (Real.rpow_pos_of_pos two_pos _)
  refine tendsto_atTop_mono (fun L => ?_)
    ((tendsto_pow_atTop_atTop_of_one_lt h2a).const_mul_atTop hdpos)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(α * (L : ℝ) ^ 2)) := Real.rpow_pos_of_pos two_pos _
  rw [le_div_iff₀ hpos]
  refine le_trans ?_ (hlow L)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_assoc,
    ← Real.rpow_add two_pos, mul_assoc, ← Real.rpow_add two_pos]
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    (abs_nonneg d)
  have hL : ((L : ℝ) - 1) * ((L : ℝ) - 2) ≥ 0 := by
    rcases Nat.lt_or_ge L 2 with h | h
    · interval_cases L <;> norm_num
    · have : (2 : ℝ) ≤ L := by exact_mod_cast h
      nlinarith
  nlinarith [mul_nonneg hα.le hL]

end ml2r

/-! ### §5.7: the variance of the smoothed-CDF correction -/

section cdf

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The variance of the smoothed-CDF correction** (Giles 2015, §5.7, p. 46, l. 1985–1993:
"`C_δ(x) = E[(g((x−P)/δ)]` … As `δ → 0`, `g(x/δ) → H(x)`, and the accuracy improves but the variance
of the multilevel estimator increases").  If `g` is `K`-Lipschitz, `P_ℓ`, `P_{ℓ−1}` (`Pf`, `Pc`)
are a.e. strongly measurable and `P_ℓ − P_{ℓ−1}` is square integrable, then for `δ > 0` the
multilevel correction `g((x − P_ℓ)/δ) − g((x − P_{ℓ−1})/δ)` is square integrable and
`V[g((x − P_ℓ)/δ) − g((x − P_{ℓ−1})/δ)] ≤ (K/δ)² E[(P_ℓ − P_{ℓ−1})²]`.  The bound grows like `δ⁻²`
as `δ → 0`; `tendsto_variance_smoothCDF_correction` gives the limit of the variance itself.
Deviation: the paper asks `g` only to be continuous; the Lipschitz constant is what makes the
correction variance a multiple of `E[(P_ℓ − P_{ℓ−1})²]`. -/
theorem variance_smoothCDF_correction_le {Pf Pc : Ω → ℝ} (hPf : AEStronglyMeasurable Pf μ)
    (hPc : AEStronglyMeasurable Pc μ) (hd : MemLp (fun ω => Pf ω - Pc ω) 2 μ) {g : ℝ → ℝ}
    {K : ℝ≥0} (hg : LipschitzWith K g) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    MemLp (fun ω => g ((x - Pf ω) / δ) - g ((x - Pc ω) / δ)) 2 μ ∧
      variance (fun ω => g ((x - Pf ω) / δ) - g ((x - Pc ω) / δ)) μ ≤
        ((K : ℝ) / δ) ^ 2 * ∫ ω, (Pf ω - Pc ω) ^ 2 ∂μ := by
  have hKδ : (0 : ℝ) ≤ K / δ := div_nonneg K.coe_nonneg hδ.le
  have hpt : ∀ ω, |g ((x - Pf ω) / δ) - g ((x - Pc ω) / δ)| ≤ K / δ * |Pf ω - Pc ω| := by
    intro ω
    have h := hg.dist_le_mul ((x - Pf ω) / δ) ((x - Pc ω) / δ)
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hδ,
      show x - Pf ω - (x - Pc ω) = -(Pf ω - Pc ω) by ring, abs_neg] at h
    calc _ ≤ K * (|Pf ω - Pc ω| / δ) := h
      _ = K / δ * |Pf ω - Pc ω| := by ring
  have hm : AEStronglyMeasurable (fun ω => g ((x - Pf ω) / δ) - g ((x - Pc ω) / δ)) μ :=
    (hg.continuous.comp_aestronglyMeasurable
      ((aemeasurable_const.sub hPf.aemeasurable).div_const δ).aestronglyMeasurable).sub
      (hg.continuous.comp_aestronglyMeasurable
        ((aemeasurable_const.sub hPc.aemeasurable).div_const δ).aestronglyMeasurable)
  have hY : MemLp (fun ω => g ((x - Pf ω) / δ) - g ((x - Pc ω) / δ)) 2 μ :=
    (hd.const_mul (K / δ)).of_le hm (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hKδ]
      exact hpt ω)
  refine ⟨hY, (variance_le_expectation_sq hm).trans ?_⟩
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
    (hd.integrable_sq.const_mul _) (Eventually.of_forall fun ω => ?_)
  have h := pow_le_pow_left₀ (abs_nonneg _) (hpt ω) 2
  simp only [Pi.pow_apply]
  rwa [sq_abs, mul_pow, sq_abs] at h

/-- **As `δ → 0` the smoothed correction loses its smoothing** (Giles 2015, §5.7, p. 46,
l. 1987–1993: "where `g(x)` is a continuous function with `g(x) = 0` for `x < −1`, and `g(x) = 1`
for `x > 1` … As `δ → 0`, `g(x/δ) → H(x)`, and the accuracy improves but the variance of the
multilevel estimator increases").  For every such `g` (continuous, hence bounded), if `P_ℓ` and
`P_{ℓ−1}` (`Pf`, `Pc`, a.e. measurable) have no atom at `x`, then the corrections are square
integrable for `δ > 0` and as `δ → 0⁺` the variance of `g((x − P_ℓ)/δ) − g((x − P_{ℓ−1})/δ)`
tends to the variance of the indicator correction `1_{P_ℓ < x} − 1_{P_{ℓ−1} < x}` of the
unsmoothed CDF, the correction of the discontinuous payoff `H(x − P)`.  (The Lipschitz bound of
`variance_smoothCDF_correction_le` blows up like `δ⁻²`.) -/
theorem tendsto_variance_smoothCDF_correction {Pf Pc : Ω → ℝ} (hPf : AEMeasurable Pf μ)
    (hPc : AEMeasurable Pc μ) {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ y < -1, g y = 0)
    (hg1 : ∀ y > 1, g y = 1) (x : ℝ) (hxf : μ {ω | Pf ω = x} = 0)
    (hxc : μ {ω | Pc ω = x} = 0) :
    (∀ δ, 0 < δ → MemLp (fun ω => g ((x - Pf ω) / δ) - g ((x - Pc ω) / δ)) 2 μ) ∧
    MemLp (fun ω => (if Pf ω < x then (1 : ℝ) else 0) - (if Pc ω < x then (1 : ℝ) else 0)) 2 μ ∧
    Tendsto (fun δ => variance (fun ω => g ((x - Pf ω) / δ) - g ((x - Pc ω) / δ)) μ) (𝓝[>] 0)
      (𝓝 (variance (fun ω => (if Pf ω < x then (1 : ℝ) else 0) -
        (if Pc ω < x then (1 : ℝ) else 0)) μ)) := by
  -- `g` is bounded, by compactness of `[−1, 1]`
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hg.continuousOn
  have hgB : ∀ y, |g y| ≤ max M 1 := fun y => by
    by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
    · exact ((Real.norm_eq_abs _).symm.trans_le (hM y hy)).trans (le_max_left _ _)
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
      rcases hy with hy | hy
      · rw [hg0 y hy, abs_zero]
        exact zero_le_one.trans (le_max_right _ _)
      · rw [hg1 y hy, abs_one]
        exact le_max_right _ _
  set B := max M 1 with hB
  have hB0 : 0 ≤ B := zero_le_one.trans (le_max_right _ _)
  set Y : ℝ → Ω → ℝ := fun δ ω => g ((x - Pf ω) / δ) - g ((x - Pc ω) / δ) with hYdef
  set Y₀ : Ω → ℝ := fun ω => (if Pf ω < x then (1 : ℝ) else 0) -
    (if Pc ω < x then (1 : ℝ) else 0) with hY₀
  have hYm : ∀ δ, AEStronglyMeasurable (Y δ) μ := fun δ =>
    ((hg.measurable.comp_aemeasurable ((aemeasurable_const.sub hPf).div_const δ)).sub
      (hg.measurable.comp_aemeasurable ((aemeasurable_const.sub hPc).div_const δ))
      ).aestronglyMeasurable
  have hH : Measurable fun y : ℝ => if y < x then (1 : ℝ) else 0 :=
    Measurable.ite (measurableSet_Iio : MeasurableSet {y : ℝ | y < x}) measurable_const
      measurable_const
  have hY₀m : AEStronglyMeasurable Y₀ μ :=
    ((hH.comp_aemeasurable hPf).sub (hH.comp_aemeasurable hPc)).aestronglyMeasurable
  have hYB : ∀ δ ω, |Y δ ω| ≤ 2 * B := fun δ ω => by
    refine (abs_sub _ _).trans ?_
    linarith [hgB ((x - Pf ω) / δ), hgB ((x - Pc ω) / δ)]
  have hY₀B : ∀ ω, |Y₀ ω| ≤ 2 := fun ω => by
    simp only [hY₀]
    split_ifs <;> norm_num
  have hmem : ∀ δ, MemLp (Y δ) 2 μ := fun δ =>
    memLp_of_bounded (a := -(2 * B)) (b := 2 * B) (Eventually.of_forall fun ω =>
      abs_le.1 (hYB δ ω)) (hYm δ) 2
  have hmem₀ : MemLp Y₀ 2 μ :=
    memLp_of_bounded (a := -2) (b := 2) (Eventually.of_forall fun ω => abs_le.1 (hY₀B ω))
      hY₀m 2
  -- pointwise convergence off the atoms
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun δ => Y δ ω) (𝓝[>] 0) (𝓝 (Y₀ ω)) := by
    have hf : ∀ᵐ ω ∂μ, Pf ω ≠ x := measure_eq_zero_iff_ae_notMem.1 hxf
    have hc : ∀ᵐ ω ∂μ, Pc ω ≠ x := measure_eq_zero_iff_ae_notMem.1 hxc
    filter_upwards [hf, hc] with ω h1 h2
    have e1 := smooth_step_eventually hg0 hg1 (sub_ne_zero.2 (Ne.symm h1))
    have e2 := smooth_step_eventually hg0 hg1 (sub_ne_zero.2 (Ne.symm h2))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [e1, e2] with δ d1 d2
    simp only [hYdef, hY₀, d1, d2, sub_pos]
  have hI1 : Tendsto (fun δ => ∫ ω, Y δ ω ∂μ) (𝓝[>] 0) (𝓝 (∫ ω, Y₀ ω ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * B)
      (Eventually.of_forall fun δ => hYm δ)
      (Eventually.of_forall fun δ => Eventually.of_forall fun ω =>
        (Real.norm_eq_abs _).trans_le (hYB δ ω)) (integrable_const _) hlim
  have hI2 : Tendsto (fun δ => ∫ ω, Y δ ω ^ 2 ∂μ) (𝓝[>] 0) (𝓝 (∫ ω, Y₀ ω ^ 2 ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence (fun _ => (2 * B) ^ 2)
      (Eventually.of_forall fun δ => (hYm δ).pow 2)
      (Eventually.of_forall fun δ => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hYB δ ω) 2) (integrable_const _)
      (hlim.mono fun ω h => h.pow 2)
  have e : ∀ δ, variance (Y δ) μ = ∫ ω, Y δ ω ^ 2 ∂μ - (∫ ω, Y δ ω ∂μ) ^ 2 := fun δ => by
    rw [variance_eq_sub (hmem δ)]
    rfl
  refine ⟨fun δ _ => hmem δ, hmem₀, ?_⟩
  rw [variance_eq_sub hmem₀]
  exact (hI2.sub (hI1.pow 2)).congr fun δ => (e δ).symm

end cdf

/-! ### §7.1: the explicit heat scheme with Dirichlet boundary values -/

section heat

/-- One step of the explicit scheme of Giles 2015, §7.1 (p. 51, l. 2190–2195:
"`u^{n+1}_j = u^n_j + (k/h²)(u^n_{j+1} − 2u^n_j + u^n_{j−1}) + 10ΔW_n`", with "boundary data
`u(0, t) = u(1, t) = 0`") on the grid `j = 0, …, J` (`h = 1/J`) with Dirichlet boundary values:
the interior nodes `0 < j < J` get `u_j + λ(u_{j+1} − 2u_j + u_{j−1}) + w_j` (`λ = k/h²`, `w_j`
the noise, `10ΔW_n` in the paper), the boundary nodes `j = 0, J` keep their values.  The values
at `j > J` are carried along and never used. -/
def dirichletHeatStep (lam : ℝ) (J : ℕ) (w u : ℕ → ℝ) (j : ℕ) : ℝ :=
  if 0 < j ∧ j < J then u j + lam * (u (j + 1) - 2 * u j + u (j - 1)) + w j else u j

/-- **The explicit scheme with Dirichlet boundary values is max-norm stable for `λ ≤ ½`** (Giles
2015, §7.1, p. 51, l. 2190–2201: "`u^{n+1}_j = u^n_j + (k/h²)(u^n_{j+1} − 2u^n_j + u^n_{j−1}) +
10ΔW_n` … Keeping `k_ℓ/h_ℓ² = ¼` ensures the explicit numerical discretisation is stable on all
levels").  On the grid `j = 0, …, J` with `λ = k/h² ∈ [0, ½]`, let `U^n` and `V^n` solve the scheme
`dirichletHeatStep` driven by the same noise `w^n` (any interior forcing, e.g. `10ΔW_n`).  Then the
boundary values of `U^n` stay those of `U^0`, and if `|U^0_j − V^0_j| ≤ M` for `j ≤ J` then
`|U^n_j − V^n_j| ≤ M` for `j ≤ J` and all `n`: perturbations do not grow in the maximum norm, on
every grid, in particular for the paper's `λ = ¼`.  This is the Dirichlet version of
`abs_heatStep_le` and `heatStep_sub` of `MlmcLean.PDEExamples`, which are on `ℤ`. -/
theorem dirichletHeat_stable {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1 / 2) {J : ℕ}
    {w U V : ℕ → ℕ → ℝ} (hU : ∀ n, U (n + 1) = dirichletHeatStep lam J (w n) (U n))
    (hV : ∀ n, V (n + 1) = dirichletHeatStep lam J (w n) (V n)) {M : ℝ}
    (hM : ∀ j ≤ J, |U 0 j - V 0 j| ≤ M) (n : ℕ) :
    U n 0 = U 0 0 ∧ U n J = U 0 J ∧ ∀ j ≤ J, |U n j - V n j| ≤ M := by
  have h2 : 0 ≤ 1 - 2 * lam := by linarith
  induction n with
  | zero => exact ⟨rfl, rfl, hM⟩
  | succ n ih =>
    obtain ⟨ih0, ihJ, ihM⟩ := ih
    refine ⟨?_, ?_, fun j hj => ?_⟩
    · rw [hU, dirichletHeatStep, if_neg (by omega), ih0]
    · rw [hU, dirichletHeatStep, if_neg (by omega), ihJ]
    · rw [hU, hV, dirichletHeatStep, dirichletHeatStep]
      split_ifs with hjJ
      · have e : U n j + lam * (U n (j + 1) - 2 * U n j + U n (j - 1)) + w n j -
            (V n j + lam * (V n (j + 1) - 2 * V n j + V n (j - 1)) + w n j) =
            lam * (U n (j - 1) - V n (j - 1)) + (1 - 2 * lam) * (U n j - V n j) +
              lam * (U n (j + 1) - V n (j + 1)) := by ring
        rw [e]
        have a1 := ihM (j - 1) (by omega)
        have a2 := ihM j hj
        have a3 := ihM (j + 1) (by omega)
        calc _ ≤ |lam * (U n (j - 1) - V n (j - 1))| + |(1 - 2 * lam) * (U n j - V n j)| +
              |lam * (U n (j + 1) - V n (j + 1))| :=
              (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
          _ = lam * |U n (j - 1) - V n (j - 1)| + (1 - 2 * lam) * |U n j - V n j| +
              lam * |U n (j + 1) - V n (j + 1)| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h2]
          _ ≤ lam * M + (1 - 2 * lam) * M + lam * M :=
              add_le_add (add_le_add (mul_le_mul_of_nonneg_left a1 h0)
                (mul_le_mul_of_nonneg_left a2 h2)) (mul_le_mul_of_nonneg_left a3 h0)
          _ = M := by ring
      · exact ihM j hj

/-- The discrete sine modes are eigenvectors of the Dirichlet scheme (Giles 2015, §7.1, p. 51):
if `sin(θJ) = 0` (e.g. `θ = πm/J`), then on the nodes `j ≤ J` the noise-free step maps
`v_j = sin(θj)` to `(1 − 4λ sin²(θ/2)) v_j`. -/
lemma dirichletHeatStep_sin {lam θ : ℝ} {J : ℕ} (hθ : Real.sin (θ * J) = 0) {j : ℕ}
    (hj : j ≤ J) :
    dirichletHeatStep lam J (fun _ => 0) (fun i => Real.sin (θ * i)) j =
      (1 - 4 * lam * Real.sin (θ / 2) ^ 2) * Real.sin (θ * j) := by
  rw [dirichletHeatStep]
  split_ifs with h
  · have hc : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have e1 : Real.sin (θ * ((j + 1 : ℕ) : ℝ)) =
        Real.sin (θ * j) * Real.cos θ + Real.cos (θ * j) * Real.sin θ := by
      rw [Nat.cast_succ, mul_add, mul_one, Real.sin_add]
    have e2 : Real.sin (θ * ((j - 1 : ℕ) : ℝ)) =
        Real.sin (θ * j) * Real.cos θ - Real.cos (θ * j) * Real.sin θ := by
      rw [hc, mul_sub, mul_one, Real.sin_sub]
    have e3 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h2 := Real.sin_sq_add_cos_sq (θ / 2)
      have h3 : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
      rw [h3, Real.cos_two_mul]
      linarith
    rw [e1, e2, e3]
    ring
  · have hj' : j = 0 ∨ j = J := by omega
    rcases hj' with rfl | rfl
    · simp
    · rw [hθ, mul_zero]

/-- The noise-free Dirichlet step is homogeneous on the nodes `j ≤ J` (Giles 2015, §7.1): if
`u_i = a v_i` for `i ≤ J`, then `(S u)_j = a (S v)_j` for `j ≤ J`. -/
lemma dirichletHeatStep_smul {lam a : ℝ} {J : ℕ} {u v : ℕ → ℝ} (h : ∀ i ≤ J, u i = a * v i)
    {j : ℕ} (hj : j ≤ J) :
    dirichletHeatStep lam J (fun _ => 0) u j = a * dirichletHeatStep lam J (fun _ => 0) v j := by
  rw [dirichletHeatStep, dirichletHeatStep]
  split_ifs with hjJ
  · rw [h j hj, h (j + 1) (by omega), h (j - 1) (by omega)]
    ring
  · exact h j hj

/-- **For `λ > ½` the Dirichlet scheme has an unstable mode** (Giles 2015, §7.1, p. 51,
l. 2199–2201, the converse of "Keeping `k_ℓ/h_ℓ² = ¼` ensures the explicit numerical discretisation
is stable on all levels").  For every `λ > ½` there is `J₀` such that on every grid with `J ≥ J₀`
intervals some initial data `v` with `v_0 = v_J = 0` and `|v_j| ≤ 1` have an unbounded noise-free
solution: `|u^n_1| → ∞`.  The mode is the discrete sine `v_j = sin(π(J − 1)j/J)`, which each step
multiplies by `1 − 4λcos²(π/(2J)) < −1` once `cos²(π/(2J)) > 1/(2λ)` (`dirichletHeatStep_sin`).
So the threshold `λ ≤ ½` of `dirichletHeat_stable` is sharp on fine grids; on coarse grids it is
not (with one interior node the step is `u_1 ↦ (1 − 2λ)u_1`, stable for `λ ≤ 1`), hence `J₀`. -/
theorem dirichletHeat_unstable {lam : ℝ} (hlam : 1 / 2 < lam) :
    ∃ J₀ : ℕ, ∀ J ≥ J₀, ∃ v : ℕ → ℝ, v 0 = 0 ∧ v J = 0 ∧ (∀ j, |v j| ≤ 1) ∧
      Tendsto (fun n => |(dirichletHeatStep lam J (fun _ => 0))^[n] v 1|) atTop atTop := by
  set c : ℝ := 1 / (2 * lam) with hc
  have hlam0 : 0 < lam := by linarith
  have hc1 : c < 1 := by
    rw [hc, div_lt_one (by linarith)]
    linarith
  obtain ⟨J₁, hJ₁⟩ := exists_nat_gt (4 / (1 - c))
  refine ⟨J₁ + 2, fun J hJ => ?_⟩
  have hJ2 : (2 : ℝ) ≤ J := by exact_mod_cast (by omega : 2 ≤ J)
  have hJpos : (0 : ℝ) < J := by linarith
  have hJ4 : 4 / (1 - c) < J := hJ₁.trans_le (by exact_mod_cast (by omega : J₁ ≤ J))
  set θ : ℝ := Real.pi * ((J : ℝ) - 1) / J with hθ
  set ρ : ℝ := 1 - 4 * lam * Real.sin (θ / 2) ^ 2 with hρ
  have hθJ : Real.sin (θ * J) = 0 := by
    have e : θ * J = ((J - 1 : ℕ) : ℝ) * Real.pi := by
      rw [hθ, Nat.cast_sub (by omega), Nat.cast_one]
      field_simp
    rw [e, Real.sin_nat_mul_pi]
  -- the mode `sin(θ j)` is multiplied by `ρ` at every step
  have hiter : ∀ n, ∀ j ≤ J, (dirichletHeatStep lam J (fun _ => 0))^[n]
      (fun i : ℕ => Real.sin (θ * i)) j = ρ ^ n * Real.sin (θ * j) := by
    intro n
    induction n with
    | zero => intro j _; simp
    | succ n ih =>
      intro j hj
      rw [Function.iterate_succ_apply', dirichletHeatStep_smul ih hj,
        dirichletHeatStep_sin hθJ hj, pow_succ]
      ring
  -- `|ρ| > 1`: `sin(θ/2) = cos(π/(2J))` and `cos² (π/(2J)) > 1/(2λ)`
  have hhalf : Real.sin (θ / 2) = Real.cos (Real.pi / (2 * J)) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    rw [hθ]
    field_simp
  set x : ℝ := Real.pi / (2 * J) with hx
  have hx2 : x ^ 2 < 1 - c := by
    have hpi := Real.pi_le_four
    have hpi0 := Real.pi_pos
    have h1 : x ^ 2 ≤ 4 / J := by
      have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith
      rw [hx, div_pow, div_le_div_iff₀ (by positivity) hJpos]
      nlinarith [mul_le_mul_of_nonneg_right hpi2 hJpos.le]
    have h2 : 4 / (J : ℝ) < 1 - c := by
      rw [div_lt_iff₀ hJpos]
      rw [div_lt_iff₀ (by linarith)] at hJ4
      linarith
    linarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcos2 : c < Real.cos x ^ 2 := by
    have hpos : 0 ≤ 1 - x ^ 2 / 2 := by nlinarith
    have := pow_le_pow_left₀ hpos hcos 2
    nlinarith
  have hρ1 : 1 < |ρ| := by
    rw [hρ, hhalf]
    have h4 : 2 < 4 * lam * Real.cos x ^ 2 := by
      have := mul_lt_mul_of_pos_left hcos2 (by linarith : (0 : ℝ) < 4 * lam)
      rw [hc] at this
      field_simp at this
      linarith
    rw [abs_of_neg (by linarith)]
    linarith
  -- the value at the first interior node
  have hv1 : 0 < Real.sin (θ * ((1 : ℕ) : ℝ)) := by
    have e : θ * ((1 : ℕ) : ℝ) = Real.pi - Real.pi / J := by
      rw [hθ]
      field_simp
      ring
    rw [e, Real.sin_pi_sub]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (div_lt_self Real.pi_pos (by linarith))
  refine ⟨fun i => Real.sin (θ * i), by simp, hθJ, fun j => Real.abs_sin_le_one _, ?_⟩
  have e : (fun n => |(dirichletHeatStep lam J (fun _ => 0))^[n]
      (fun i : ℕ => Real.sin (θ * i)) 1|) = fun n => |ρ| ^ n * Real.sin (θ * ((1 : ℕ) : ℝ)) :=
    funext fun n => by
      rw [hiter n 1 (by omega), abs_mul, abs_pow, abs_of_pos hv1]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hρ1).atTop_mul_const hv1

end heat

/-! ### §7.2: nested inputs `ξ_ℓ = (ξ_{ℓ−1}, z_ℓ)` give (2.4) -/

section nestedInputs

variable {X : ℕ → Type*} [∀ ℓ, MeasurableSpace (X ℓ)]

/-- The telescoping sum for coarse payoffs computed on projected inputs (Giles 2015, §1.3 and
(2.4)): if the projection `proj_ℓ` of a level-`(ℓ + 1)` input to a level-`ℓ` input is measure
preserving, then `E[P_0] + ∑_{ℓ<L} E[P_{ℓ+1} − P_ℓ ∘ proj_ℓ] = E[P_L]`. -/
lemma nested_proj_telescoping {ν : ∀ ℓ, Measure (X ℓ)} {proj : ∀ ℓ, X (ℓ + 1) → X ℓ}
    (hproj : ∀ ℓ, MeasurePreserving (proj ℓ) (ν (ℓ + 1)) (ν ℓ)) {P : ∀ ℓ, X ℓ → ℝ}
    (hP : ∀ ℓ, Integrable (P ℓ) (ν ℓ)) (L : ℕ) :
    ∫ ξ, P 0 ξ ∂ν 0 + ∑ ℓ ∈ range L, ∫ ξ, (P (ℓ + 1) ξ - P ℓ (proj ℓ ξ)) ∂ν (ℓ + 1) =
      ∫ ξ, P L ξ ∂ν L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hc : Integrable (fun ξ => P L (proj L ξ)) (ν (L + 1)) :=
      ((hproj L).integrable_comp (hP L).aestronglyMeasurable).2 (hP L)
    rw [sum_range_succ, ← add_assoc, ih, integral_sub (hP (L + 1)) hc,
      integral_comp_of_measurePreserving (hproj L) (hP L).aestronglyMeasurable]
    ring

/-- (2.4) in law (Giles 2015, §2.1, (2.4)): if `proj_ℓ` is measure preserving, the coarse payoff
`P_ℓ ∘ proj_ℓ` of a level-`(ℓ + 1)` sample has the law of the payoff `P_ℓ` of a level-`ℓ`
sample. -/
lemma nested_proj_map_eq {ν : ∀ ℓ, Measure (X ℓ)} {proj : ∀ ℓ, X (ℓ + 1) → X ℓ}
    (hproj : ∀ ℓ, MeasurePreserving (proj ℓ) (ν (ℓ + 1)) (ν ℓ)) {P : ∀ ℓ, X ℓ → ℝ}
    (hPm : ∀ ℓ, AEMeasurable (P ℓ) (ν ℓ)) (ℓ : ℕ) :
    (ν (ℓ + 1)).map (fun ξ => P ℓ (proj ℓ ξ)) = (ν ℓ).map (P ℓ) := by
  have h := AEMeasurable.map_map_of_aemeasurable (f := proj ℓ) (g := P ℓ)
    (by rw [(hproj ℓ).map_eq]; exact hPm ℓ) (hproj ℓ).measurable.aemeasurable
  rw [(hproj ℓ).map_eq] at h
  exact h.symm

/-- **Nested inputs give (2.4) and the telescoping sum** (Giles 2015, §7.2, p. 53, l. 2270–2273:
"In both cases, `log κ` is generated using a row-vector of independent unit Normal random variables
`ξ`. The variables for the fine level can be partitioned into those for the coarse level `ξ_{ℓ−1}`,
plus some additional variables `z_ℓ`, giving `ξ_ℓ = (ξ_{ℓ−1}, z_ℓ)`"; (2.4), §2.1, p. 8).  Let the
level-`(ℓ + 1)` input be split, by a measure-preserving map `split_ℓ`, into a level-`ℓ` input and
an independent block `z_{ℓ+1}` (`ν_{ℓ+1} ↦ ν_ℓ ⊗ ρ_ℓ`, `ρ_ℓ` a probability measure), and let the
level payoffs `P_ℓ` be integrable.  Then the coarse payoff evaluated on the truncated fine input,
`P_ℓ((split_ℓ ξ_{ℓ+1}).1)`, has the law of the level-`ℓ` payoff `P_ℓ(ξ_ℓ)`; so (2.4)
`E[P^c_ℓ] = E[P^f_ℓ]` holds, and `E[P_0] + ∑_{ℓ<L} E[P_{ℓ+1} − P_ℓ((split_ℓ ξ_{ℓ+1}).1)] = E[P_L]`.
The projection to the first factor of a product of probability measures is measure preserving
(`measurePreserving_fst`). -/
theorem nested_inputs_mlmc {Z : ℕ → Type*} [∀ ℓ, MeasurableSpace (Z ℓ)]
    {ν : ∀ ℓ, Measure (X ℓ)} {ρ : ∀ ℓ, Measure (Z ℓ)} [∀ ℓ, IsProbabilityMeasure (ρ ℓ)]
    {split : ∀ ℓ, X (ℓ + 1) → X ℓ × Z ℓ}
    (hsplit : ∀ ℓ, MeasurePreserving (split ℓ) (ν (ℓ + 1)) ((ν ℓ).prod (ρ ℓ)))
    {P : ∀ ℓ, X ℓ → ℝ} (hP : ∀ ℓ, Integrable (P ℓ) (ν ℓ)) :
    (∀ ℓ, (ν (ℓ + 1)).map (fun ξ => P ℓ (split ℓ ξ).1) = (ν ℓ).map (P ℓ)) ∧
    (∀ ℓ, ∫ ξ, P ℓ (split ℓ ξ).1 ∂ν (ℓ + 1) = ∫ ξ, P ℓ ξ ∂ν ℓ) ∧
    ∀ L, ∫ ξ, P 0 ξ ∂ν 0 +
      ∑ ℓ ∈ range L, ∫ ξ, (P (ℓ + 1) ξ - P ℓ (split ℓ ξ).1) ∂ν (ℓ + 1) = ∫ ξ, P L ξ ∂ν L := by
  have hproj : ∀ ℓ, MeasurePreserving (fun ξ => (split ℓ ξ).1) (ν (ℓ + 1)) (ν ℓ) := fun ℓ =>
    measurePreserving_fst.comp (hsplit ℓ)
  exact ⟨nested_proj_map_eq hproj fun ℓ => (hP ℓ).aemeasurable,
    fun ℓ => integral_comp_of_measurePreserving (hproj ℓ) (hP ℓ).aestronglyMeasurable,
    nested_proj_telescoping hproj hP⟩

/-- Truncating a finite product of probability measures to its first `m` coordinates is measure
preserving (for the truncated Karhunen–Loève inputs of Giles 2015, §7.2, p. 53): the map
`(ξ_i)_{i<n} ↦ (ξ_i)_{i<m}` sends `⊗_{i<n} η_i` to `⊗_{i<m} η_i` for `m ≤ n`. -/
lemma measurePreserving_truncFin {E : Type*} [MeasurableSpace E] (η : ℕ → Measure E)
    [∀ i, IsProbabilityMeasure (η i)] {m n : ℕ} (hmn : m ≤ n) :
    MeasurePreserving (fun (ξ : Fin n → E) (i : Fin m) => ξ (Fin.castLE hmn i))
      (Measure.pi fun i : Fin n => η i) (Measure.pi fun i : Fin m => η i) := by
  classical
  have hmeas : Measurable fun (ξ : Fin n → E) (i : Fin m) => ξ (Fin.castLE hmn i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  refine ⟨hmeas, (Measure.pi_eq fun s hs => ?_).symm⟩
  set F : ℕ → ℝ≥0∞ := fun k => η k (if h : k < m then s ⟨k, h⟩ else Set.univ) with hF
  have hpre : (fun (ξ : Fin n → E) (i : Fin m) => ξ (Fin.castLE hmn i)) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun j : Fin n => if h : (j : ℕ) < m then s ⟨j, h⟩ else Set.univ := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hξ j
      split_ifs with h
      · exact hξ ⟨j, h⟩
      · exact Set.mem_univ _
    · intro hξ i
      have := hξ (Fin.castLE hmn i)
      rw [dif_pos (show ((Fin.castLE hmn i : Fin n) : ℕ) < m from i.isLt)] at this
      exact this
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
  have e1 : ∏ j : Fin n, η j (if h : (j : ℕ) < m then s ⟨j, h⟩ else Set.univ) =
      ∏ k ∈ range n, F k := Fin.prod_univ_eq_prod_range F n
  have e2 : ∏ i : Fin m, η i (s i) = ∏ k ∈ range m, F k := by
    rw [← Fin.prod_univ_eq_prod_range F m]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hF, dif_pos i.isLt, Fin.eta]
  have e3 : ∏ k ∈ Ico m n, F k = 1 := Finset.prod_eq_one fun k hk => by
    simp only [hF, dif_neg (not_lt.2 (Finset.mem_Ico.1 hk).1), measure_univ]
  rw [e1, e2, ← Finset.prod_range_mul_prod_Ico F hmn, e3, mul_one]

/-- **Truncated vectors of independent inputs give (2.4)** (Giles 2015, §7.2, p. 53,
l. 2263–2273: "Using the Karhunen-Loève generation, the expansion is truncated after `K_ℓ` terms,
with `K_ℓ` increasing with level … `log κ` is generated using a row-vector of independent unit
Normal random variables `ξ` … giving `ξ_ℓ = (ξ_{ℓ−1}, z_ℓ)`").  Let the level-`ℓ` input be the
vector `ξ_ℓ = (ξ_i)_{i < K_ℓ}` (`Fin (K ℓ) → E`) of independent variables with laws `η_i`
(`η_i = N(0, 1)` in the paper), with `K_ℓ ≤ K_{ℓ+1}`, and let the coarse payoff of a
level-`(ℓ + 1)` sample be `P_ℓ` of its first `K_ℓ` coordinates, `(ξ_i)_{i < K_ℓ}`
(`ξ ∘ Fin.castLE`).  Then, for integrable `P_ℓ`, the coarse payoff has the law of the level-`ℓ`
payoff, (2.4) holds, and the telescoping sum holds.  The truncation of a finite product of
probability measures is measure preserving (`measurePreserving_truncFin`). -/
theorem nested_vector_inputs_mlmc {E : Type*} [MeasurableSpace E] (η : ℕ → Measure E)
    [∀ i, IsProbabilityMeasure (η i)] {K : ℕ → ℕ} (hK : ∀ ℓ, K ℓ ≤ K (ℓ + 1))
    {P : ∀ ℓ, (Fin (K ℓ) → E) → ℝ}
    (hP : ∀ ℓ, Integrable (P ℓ) (Measure.pi fun i : Fin (K ℓ) => η i)) :
    (∀ ℓ, (Measure.pi fun i : Fin (K (ℓ + 1)) => η i).map
        (fun ξ => P ℓ (fun i => ξ (Fin.castLE (hK ℓ) i))) =
      (Measure.pi fun i : Fin (K ℓ) => η i).map (P ℓ)) ∧
    (∀ ℓ, ∫ ξ, P ℓ (fun i => ξ (Fin.castLE (hK ℓ) i))
        ∂(Measure.pi fun i : Fin (K (ℓ + 1)) => η i) =
      ∫ ξ, P ℓ ξ ∂(Measure.pi fun i : Fin (K ℓ) => η i)) ∧
    ∀ L, ∫ ξ, P 0 ξ ∂(Measure.pi fun i : Fin (K 0) => η i) +
      ∑ ℓ ∈ range L, ∫ ξ, (P (ℓ + 1) ξ - P ℓ (fun i => ξ (Fin.castLE (hK ℓ) i)))
        ∂(Measure.pi fun i : Fin (K (ℓ + 1)) => η i) =
      ∫ ξ, P L ξ ∂(Measure.pi fun i : Fin (K L) => η i) := by
  have hproj : ∀ ℓ, MeasurePreserving
      (fun (ξ : Fin (K (ℓ + 1)) → E) (i : Fin (K ℓ)) => ξ (Fin.castLE (hK ℓ) i))
      (Measure.pi fun i : Fin (K (ℓ + 1)) => η i) (Measure.pi fun i : Fin (K ℓ) => η i) :=
    fun ℓ => measurePreserving_truncFin η (hK ℓ)
  exact ⟨nested_proj_map_eq (X := fun ℓ => Fin (K ℓ) → E) hproj
      fun ℓ => (hP ℓ).aemeasurable,
    fun ℓ => integral_comp_of_measurePreserving (hproj ℓ) (hP ℓ).aestronglyMeasurable,
    nested_proj_telescoping (X := fun ℓ => Fin (K ℓ) → E) hproj hP⟩

end nestedInputs

/-! ### §9.1: standard nested Monte Carlo costs `Θ(ε⁻³)` -/

section nestedMC

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω}

/-- The mean square error of standard Monte Carlo with a biased sample (Giles 2015, §9.1, (1.1)):
for `N ≥ 1` independent samples of a square-integrable `P` and any target `EP`, the squared error
is integrable and `E[(N⁻¹∑_n P(ω_n) − EP)²] = V[P]/N + (E[P] − EP)²`. -/
lemma nested_mc_mse [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {P : Ω₀ → ℝ}
    (hPm : Measurable P) (hP : MemLp P 2 ν) {N : ℕ} (hN : 0 < N) (EP : ℝ) :
    Integrable (fun x => ((N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x) - EP) ^ 2) μ ∧
      ∫ x, ((N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x) - EP) ^ 2 ∂μ =
        variance P ν / N + (∫ y, P y ∂ν - EP) ^ 2 := by
  obtain ⟨hmean, hvarY, -, -⟩ := mc_estimate ω hω hind hPm hP hN
  have hY : MemLp (fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x)) 2 μ :=
    (memLp_finsetSum _ fun n _ => hP.comp_measurePreserving (hω n)).const_mul _
  refine ⟨(hY.sub (memLp_const EP)).integrable_sq, ?_⟩
  rw [mse_eq_variance_add_sq_bias hY, hmean, hvarY]

/-- **Standard nested Monte Carlo costs `O(ε⁻³)`** (Giles 2015, §9.1, p. 57, l. 2462–2474: "This
can be simulated using nested Monte Carlo simulation with `N` outer samples `Z⁽ⁿ⁾`, `M` inner
samples `W^{(m,n)}` and a standard Monte Carlo estimator
`Y = N⁻¹ ∑_{n=1}^{N} f(M⁻¹ ∑_{m=1}^{M} g(Z⁽ⁿ⁾, W^{(m,n)}))`.  Note that to improve the accuracy
of the estimate we need to increase both `M` and `N`, and this will significantly increase the
cost").
Let `P_M` be an outer sample with `M` inner samples (`f(M⁻¹∑_m g(Z, W_m))` as a function of the
input of law `ν`), measurable and square integrable, with bias `|E[P_M] − E[P]| ≤ c/M` and
variance `V[P_M] ≤ v` for all `M ≥ 1`, and let `Y` be the mean of `N` independent samples of
`P_M`, at cost `N M`.  Then for every `0 < ε ≤ 1` the explicit choice `M = max(1, ⌈2c/ε⌉)`,
`N = max(1, ⌈2v/ε²⌉)` gives `N, M ≥ 1`, an integrable squared error with `E[(Y − E[P])²] ≤ ε²`,
and the cost `N M ≤ (2v + 1)(2c + 1) ε⁻³`.  For twice differentiable `f` the bias rate is
`nested_bias_rate` of `MlmcLean.NestedMLMC` (for `M = 2^ℓ`); the paper does not write out the
order `ε⁻³`. -/
theorem nested_mc_cost_upper [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {PM : ℕ → Ω₀ → ℝ}
    (hPMm : ∀ M : ℕ, 0 < M → Measurable (PM M)) (hPM : ∀ M : ℕ, 0 < M → MemLp (PM M) 2 ν)
    {EP c v : ℝ} (hbias : ∀ M : ℕ, 0 < M → |∫ y, PM M y ∂ν - EP| ≤ c / M)
    (hvar : ∀ M : ℕ, 0 < M → variance (PM M) ν ≤ v) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ N M : ℕ, N = max 1 ⌈2 * v / ε ^ 2⌉₊ ∧
      M = max 1 ⌈2 * c / ε⌉₊ ∧ 0 < N ∧ 0 < M ∧
      Integrable (fun x => ((N : ℝ)⁻¹ * ∑ n ∈ range N, PM M (ω n x) - EP) ^ 2) μ ∧
      ∫ x, ((N : ℝ)⁻¹ * ∑ n ∈ range N, PM M (ω n x) - EP) ^ 2 ∂μ ≤ ε ^ 2 ∧
      (N : ℝ) * M ≤ (2 * v + 1) * (2 * c + 1) * ε ^ (-3 : ℝ) := by
  have hc : 0 ≤ c := by
    have h := hbias 1 one_pos
    rw [Nat.cast_one, div_one] at h
    exact (abs_nonneg _).trans h
  have hv : 0 ≤ v := (variance_nonneg _ _).trans (hvar 1 one_pos)
  intro ε hε hε1
  set M : ℕ := max 1 ⌈2 * c / ε⌉₊ with hM
  set N : ℕ := max 1 ⌈2 * v / ε ^ 2⌉₊ with hN
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hN0 : 0 < N := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM0
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN0
  have hε2 : 0 < ε ^ 2 := by positivity
  -- `2c/ε ≤ M ≤ 2c/ε + 1` and `2v/ε² ≤ N ≤ 2v/ε² + 1`
  have hMlo : 2 * c / ε ≤ M := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have hNlo : 2 * v / ε ^ 2 ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have hMhi : (M : ℝ) ≤ 2 * c / ε + 1 := by
    rw [hM, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith [div_nonneg (mul_nonneg zero_le_two hc) hε.le])
      (Nat.ceil_lt_add_one (by positivity)).le
  have hNhi : (N : ℝ) ≤ 2 * v / ε ^ 2 + 1 := by
    rw [hN, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith [div_nonneg (mul_nonneg zero_le_two hv) hε2.le])
      (Nat.ceil_lt_add_one (by positivity)).le
  obtain ⟨hint, hmse⟩ := nested_mc_mse ω hω hind (hPMm M hM0) (hPM M hM0) hN0 EP
  refine ⟨N, M, rfl, rfl, hN0, hM0, hint, ?_, ?_⟩
  · rw [hmse]
    have h1 : variance (PM M) ν / N ≤ ε ^ 2 / 2 := by
      rw [div_le_iff₀ hNr]
      have := hvar M hM0
      rw [div_le_iff₀ hε2] at hNlo
      nlinarith
    have h2 : (∫ y, PM M y ∂ν - EP) ^ 2 ≤ ε ^ 2 / 2 := by
      have hb := hbias M hM0
      have hcM : c / M ≤ ε / 2 := by
        rw [div_le_iff₀ hMr]
        rw [div_le_iff₀ hε] at hMlo
        linarith
      have := pow_le_pow_left₀ (abs_nonneg _) (hb.trans hcM) 2
      rw [sq_abs] at this
      nlinarith
    linarith
  · have e3 : ε ^ (-3 : ℝ) = (ε ^ 2)⁻¹ * ε⁻¹ := by
      rw [Real.rpow_neg hε.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        pow_succ, mul_inv]
    have hA : (N : ℝ) ≤ (2 * v + 1) * (ε ^ 2)⁻¹ := by
      have : (1 : ℝ) ≤ (ε ^ 2)⁻¹ := one_le_inv₀ hε2 |>.2 (pow_le_one₀ hε.le hε1)
      calc (N : ℝ) ≤ 2 * v / ε ^ 2 + 1 := hNhi
        _ ≤ 2 * v * (ε ^ 2)⁻¹ + (ε ^ 2)⁻¹ := by rw [div_eq_mul_inv]; linarith
        _ = _ := by ring
    have hB : (M : ℝ) ≤ (2 * c + 1) * ε⁻¹ := by
      have : (1 : ℝ) ≤ ε⁻¹ := one_le_inv₀ hε |>.2 hε1
      calc (M : ℝ) ≤ 2 * c / ε + 1 := hMhi
        _ ≤ 2 * c * ε⁻¹ + ε⁻¹ := by rw [div_eq_mul_inv]; linarith
        _ = _ := by ring
    rw [e3]
    calc (N : ℝ) * M ≤ ((2 * v + 1) * (ε ^ 2)⁻¹) * ((2 * c + 1) * ε⁻¹) :=
          mul_le_mul hA hB hMr.le (by positivity)
      _ = _ := by ring

/-- **Standard nested Monte Carlo costs at least `c v ε⁻³`** (Giles 2015, §9.1, p. 57,
l. 2473–2474: "to improve the accuracy of the estimate we need to increase both `M` and `N`, and
this will significantly increase the cost").  With the notation of `nested_mc_cost_upper`, if the
rates are attained, `|E[P_M] − E[P]| ≥ c/M` (`c ≥ 0`) and `V[P_M] ≥ v`, then every `N, M ≥ 1` with
`E[(Y − E[P])²] ≤ ε²`, `ε > 0`, cost `N M ≥ c v ε⁻³`: the mean square error is
`V[P_M]/N + (E[P_M] − E[P])²` (`nested_mc_mse`), which forces `N ≥ v ε⁻²` and `M ≥ c ε⁻¹`.  With
`nested_mc_cost_upper` the cost is `Θ(ε⁻³)`, against `O(ε⁻²)` for the multilevel treatment
(`nested_complexity`). -/
theorem nested_mc_cost_lower [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {P : Ω₀ → ℝ}
    (hPm : Measurable P) (hP : MemLp P 2 ν) {EP c v ε : ℝ} {N M : ℕ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hε : 0 < ε)
    (hbias : c / M ≤ |∫ y, P y ∂ν - EP|) (hvar : v ≤ variance P ν)
    (hmse : ∫ x, ((N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x) - EP) ^ 2 ∂μ ≤ ε ^ 2) :
    c * v * ε ^ (-3 : ℝ) ≤ (N : ℝ) * M := by
  obtain ⟨-, hmse'⟩ := nested_mc_mse ω hω hind hPm hP hN EP
  rw [hmse'] at hmse
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hVN : 0 ≤ variance P ν / N := div_nonneg (variance_nonneg _ _) hNr.le
  have e3 : ε ^ (-3 : ℝ) = (ε ^ 2)⁻¹ * ε⁻¹ := by
    rw [Real.rpow_neg hε.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      pow_succ, mul_inv]
  rcases le_or_gt v 0 with hv0 | hv0
  · have : c * v * ε ^ (-3 : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc hv0)
        (Real.rpow_nonneg hε.le _)
    exact this.trans (by positivity)
  · -- the sample size: `v ≤ N ε²`
    have hvN : v * (ε ^ 2)⁻¹ ≤ N := by
      have h2 : variance P ν / N ≤ ε ^ 2 := by nlinarith [sq_nonneg (∫ y, P y ∂ν - EP)]
      rw [div_le_iff₀ hNr] at h2
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      linarith
    -- the inner sample size: `c ≤ M ε`
    have hcM : c * ε⁻¹ ≤ M := by
      have h1 : (c / M) ^ 2 ≤ ε ^ 2 := by
        calc (c / M) ^ 2 ≤ |∫ y, P y ∂ν - EP| ^ 2 :=
              pow_le_pow_left₀ (div_nonneg hc hMr.le) hbias 2
          _ = (∫ y, P y ∂ν - EP) ^ 2 := sq_abs _
          _ ≤ ε ^ 2 := by linarith
      have h2 := (pow_le_pow_iff_left₀ (div_nonneg hc hMr.le) hε.le two_ne_zero).1 h1
      rw [div_le_iff₀ hMr] at h2
      rw [← div_eq_mul_inv, div_le_iff₀ hε]
      linarith
    rw [e3]
    calc c * v * ((ε ^ 2)⁻¹ * ε⁻¹) = (v * (ε ^ 2)⁻¹) * (c * ε⁻¹) := by ring
      _ ≤ N * M := mul_le_mul hvN hcM (by positivity) hNr.le

end nestedMC

/-! ### §10.1: the Euler–Maruyama chain of the Ornstein–Uhlenbeck SDE -/

section ou

/-- `N(0, v) = N(0, 1) ∘ (x ↦ √v x)⁻¹` (for the Gaussian laws of Giles 2015, §10.1). -/
lemma gaussianReal_eq_map_sqrt_mul (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  ext
  simp [Real.sq_sqrt v.coe_nonneg]

/-- `E[f(X)] = E[f(√v Z)]` for `X ~ N(0, v)`, `Z ~ N(0, 1)` and continuous `f` (Giles 2015,
§10.1). -/
lemma integral_gaussianReal_eq (v : ℝ≥0) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂gaussianReal 0 v = ∫ x, f (Real.sqrt v * x) ∂gaussianReal 0 1 := by
  rw [gaussianReal_eq_map_sqrt_mul v]
  exact integral_map (measurable_id.const_mul _).aemeasurable hf.aestronglyMeasurable

/-- **The Euler–Maruyama chain of the Ornstein–Uhlenbeck SDE has the unique invariant law
`N(0, σ²/(κ(2 − κh)))`** (Giles 2015, §10.1, p. 61, l. 2738–2743: "A very similar approach can
also be used for contracting SDEs which converge to a limiting distribution. For these, the level
`ℓ` path will perform a simulation for the time interval `[−T_ℓ, 0]`, using timestep `h_ℓ`").  For
the simplest contracting SDE, `dX = −κX dt + σ dW` with `κ > 0`, the Euler–Maruyama chain with step
`h > 0` is `X_{n+1} = (1 − κh)X_n + σ√h Z_n`, `Z_n ~ N(0, 1)` independent.  If `κh < 2`, then
`N(0, v_h)`, `v_h = σ²/(κ(2 − κh))`, is invariant: `(1 − κh)X + σ√h Z ~ N(0, v_h)` for independent
`X ~ N(0, v_h)`, `Z ~ N(0, 1)`, i.e. `(N(0, v_h) ⊗ N(0, 1)) ∘ φ⁻¹ = N(0, v_h)`; and it is the only
invariant probability measure, since the step contracts on average by `|1 − κh| < 1`
(`invariant_unique`).  So it is the law of the limit `X_∞` of the chain (`map_limit_invariant`). -/
theorem ouEM_invariant {κ σ h : ℝ} (hκ : 0 < κ) (hh : 0 < h) (hκh : κ * h < 2) :
    ((gaussianReal 0 (σ ^ 2 / (κ * (2 - κ * h))).toNNReal).prod (gaussianReal 0 1)).map
        (fun q => (1 - κ * h) * q.1 + σ * Real.sqrt h * q.2) =
      gaussianReal 0 (σ ^ 2 / (κ * (2 - κ * h))).toNNReal ∧
    ∀ π : Measure ℝ, IsProbabilityMeasure π →
      (π.prod (gaussianReal 0 1)).map (fun q => (1 - κ * h) * q.1 + σ * Real.sqrt h * q.2) = π →
      π = gaussianReal 0 (σ ^ 2 / (κ * (2 - κ * h))).toNNReal := by
  set v : ℝ≥0 := (σ ^ 2 / (κ * (2 - κ * h))).toNNReal with hv
  have h2 : 0 < 2 - κ * h := by linarith
  have hκh0 : 0 < κ * h := mul_pos hκ hh
  have hvr : (v : ℝ) = σ ^ 2 / (κ * (2 - κ * h)) := by
    rw [hv, Real.coe_toNNReal _ (by positivity)]
  -- invariance: `(1 − κh)X + σ√h Z ~ N(0, (1 − κh)² v + σ² h) = N(0, v)`
  have hinv : ((gaussianReal 0 v).prod (gaussianReal 0 1)).map
      (fun q => (1 - κ * h) * q.1 + σ * Real.sqrt h * q.2) = gaussianReal 0 v := by
    have hind := indepFun_prod (μ := gaussianReal 0 v) (ν := gaussianReal 0 1)
      (measurable_id.const_mul (1 - κ * h)) (measurable_id.const_mul (σ * Real.sqrt h))
    have hX : ((gaussianReal 0 v).prod (gaussianReal 0 1)).map (fun q => (1 - κ * h) * q.1) =
        gaussianReal 0 (((1 - κ * h) ^ 2).toNNReal * v) := by
      have e : (fun q : ℝ × ℝ => (1 - κ * h) * q.1) = (fun x => (1 - κ * h) * x) ∘ Prod.fst :=
        rfl
      rw [e, ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod,
        measure_univ, one_smul, gaussianReal_map_const_mul, mul_zero]
      congr 1
      ext
      simp [Real.coe_toNNReal _ (sq_nonneg _)]
    have hY : ((gaussianReal 0 v).prod (gaussianReal 0 1)).map
        (fun q => σ * Real.sqrt h * q.2) =
        gaussianReal 0 ((σ * Real.sqrt h) ^ 2).toNNReal := by
      have e : (fun q : ℝ × ℝ => σ * Real.sqrt h * q.2) = (fun x => σ * Real.sqrt h * x) ∘
          Prod.snd := rfl
      rw [e, ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod,
        measure_univ, one_smul, gaussianReal_map_const_mul, mul_zero]
      congr 1
      ext
      simp [Real.coe_toNNReal _ (sq_nonneg _)]
    have h := gaussianReal_add_gaussianReal_of_indepFun hind hX hY
    rw [add_zero] at h
    refine h.trans ?_
    congr 1
    ext
    rw [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _),
      Real.coe_toNNReal _ (sq_nonneg _), mul_pow, Real.sq_sqrt hh.le, hvr]
    field_simp
    ring
  refine ⟨hinv, fun π hπ hπinv => ?_⟩
  -- uniqueness: the step contracts by `|1 − κh| < 1`
  have hρ1 : |1 - κ * h| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  have hφm : Measurable fun q : ℝ × ℝ => (1 - κ * h) * q.1 + σ * Real.sqrt h * q.2 := by
    fun_prop
  refine invariant_unique (φ := fun x e => (1 - κ * h) * x + σ * Real.sqrt h * e)
    (ν := gaussianReal 0 1) hφm one_pos (abs_nonneg _) hρ1 (fun x y => ?_) 0 ?_ hπinv hinv
  · have e : ∀ e : ℝ, dist ((1 - κ * h) * x + σ * Real.sqrt h * e)
        ((1 - κ * h) * y + σ * Real.sqrt h * e) ^ (1 : ℝ) = |1 - κ * h| * dist x y ^ (1 : ℝ) :=
      fun e => by
        rw [Real.rpow_one, Real.rpow_one, Real.dist_eq, Real.dist_eq, ← abs_mul]
        congr 1
        ring
    simp_rw [e]
    rw [lintegral_const, measure_univ, mul_one,
      ENNReal.ofReal_mul (abs_nonneg _)]
  · have hint : Integrable (fun e : ℝ => dist 0 ((1 - κ * h) * 0 + σ * Real.sqrt h * e) ^ (1 : ℝ))
        (gaussianReal 0 1) := by
      have e : (fun e : ℝ => dist 0 ((1 - κ * h) * 0 + σ * Real.sqrt h * e) ^ (1 : ℝ)) =
          fun e => |σ * Real.sqrt h * e| := funext fun e => by
        rw [Real.rpow_one, Real.dist_eq, mul_zero, zero_add, zero_sub, abs_neg]
      rw [e]
      exact ((integrable_id_gaussian).const_mul (σ * Real.sqrt h)).abs
    exact hint.lintegral_lt_top.ne

/-- **The invariant laws of the discretised OU chains tend to `N(0, σ²/(2κ))` as `h → 0`**
(Giles 2015, §10.1, p. 61, l. 2738–2743: "contracting SDEs which converge to a limiting
distribution … using timestep `h_ℓ`").  For `κ > 0`, the invariant laws `N(0, σ²/(κ(2 − κh)))` of
the Euler–Maruyama chains (`ouEM_invariant`) converge weakly to `N(0, σ²/(2κ))` as `h → 0⁺`.
`N(0, σ²/(2κ))` is the stationary law of the SDE `dX = −κX dt + σ dW`, a standard fact that is not
proved here (it needs SDE theory); the statement is about the limit of the discretised chains. -/
theorem tendsto_ouEM_invariant {κ σ : ℝ} (hκ : 0 < κ) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun h : ℝ => ⟨gaussianReal 0 (σ ^ 2 / (κ * (2 - κ * h))).toNNReal, inferInstance⟩)
      (𝓝[>] 0) (𝓝 ⟨gaussianReal 0 (σ ^ 2 / (2 * κ)).toNNReal, inferInstance⟩) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
  simp only [ProbabilityMeasure.coe_mk]
  simp_rw [integral_gaussianReal_eq _ f.continuous]
  -- the variance is continuous at `h = 0`
  have hv : Tendsto (fun h : ℝ => Real.sqrt ((σ ^ 2 / (κ * (2 - κ * h))).toNNReal : ℝ))
      (𝓝[>] 0) (𝓝 (Real.sqrt ((σ ^ 2 / (2 * κ)).toNNReal : ℝ))) := by
    have hc : ContinuousAt (fun h : ℝ => Real.sqrt ((σ ^ 2 / (κ * (2 - κ * h))).toNNReal : ℝ))
        0 := by
      have hd : κ * (2 - κ * 0) ≠ 0 := by
        rw [mul_zero, sub_zero]
        positivity
      fun_prop (disch := exact hd)
    have e : κ * (2 - κ * 0) = 2 * κ := by ring
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [e] at this
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖)
    (Eventually.of_forall fun h => (f.continuous.comp (continuous_const.mul continuous_id)
      ).aestronglyMeasurable)
    (Eventually.of_forall fun h => Eventually.of_forall fun x => f.norm_coe_le_norm _)
    (integrable_const _) (Eventually.of_forall fun x => ?_)
  exact (f.continuous.tendsto _).comp (hv.mul tendsto_const_nhds)

end ou

/-! ### §10.2: reduced-precision normal inputs `Φ⁻¹((I + ½)/(I_max + 1))` -/

section midpoint

/-- If `U` is uniform on `(0, 1)`, then `⌊(n + 1)U⌋` is uniform on `{0, …, n}` (for the integer
inputs of Giles 2015, §10.2). -/
lemma map_floor_uniform (n : ℕ) :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).map (fun u => ⌊((n : ℝ) + 1) * u⌋₊) =
      uniformOn (range (n + 1) : Set ℕ) := by
  have hm : Measurable fun u : ℝ => ⌊((n : ℝ) + 1) * u⌋₊ :=
    (measurable_id.const_mul _).nat_floor
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine Measure.ext_of_singleton fun k => ?_
  have hU : uniformOn (range (n + 1) : Set ℕ) {k} =
      (#(range (n + 1) ∩ {k}) : ℝ≥0∞) / (n + 1 : ℕ) := by
    rw [← Finset.coe_singleton, uniformOn_apply_finset, card_range]
  rw [Measure.map_apply hm (measurableSet_singleton k),
    Measure.restrict_apply (hm (measurableSet_singleton k)), hU]
  by_cases hk : k ≤ n
  · have hint : range (n + 1) ∩ {k} = {k} := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [hint, card_singleton]
    -- the preimage lies between `(k/(n+1), (k+1)/(n+1))` and `[k/(n+1), (k+1)/(n+1))`
    have hsub1 : Set.Ioo ((k : ℝ) / (n + 1)) ((k + 1) / (n + 1)) ⊆
        (fun u : ℝ => ⌊((n : ℝ) + 1) * u⌋₊) ⁻¹' {k} ∩ Set.Ioo 0 1 := by
      intro u ⟨h1, h2⟩
      have hk0 : (0 : ℝ) ≤ k / (n + 1) := by positivity
      have hk1 : ((k : ℝ) + 1) / (n + 1) ≤ 1 := by
        rw [div_le_one hn]
        exact_mod_cast Nat.succ_le_succ hk
      refine ⟨?_, by linarith, by linarith⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff, Nat.floor_eq_iff (by nlinarith)]
      rw [div_lt_iff₀ hn] at h1
      rw [lt_div_iff₀ hn] at h2
      constructor <;> linarith
    have hsub2 : (fun u : ℝ => ⌊((n : ℝ) + 1) * u⌋₊) ⁻¹' {k} ∩ Set.Ioo 0 1 ⊆
        Set.Ico ((k : ℝ) / (n + 1)) ((k + 1) / (n + 1)) := by
      intro u ⟨h1, h2, _⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff, Nat.floor_eq_iff (by nlinarith)] at h1
      rw [Set.mem_Ico, div_le_iff₀ hn, lt_div_iff₀ hn]
      constructor <;> linarith [h1.1, h1.2]
    have hlen : ((k : ℝ) + 1) / (n + 1) - k / (n + 1) = 1 / (n + 1) := by
      field_simp
      ring
    refine le_antisymm ((measure_mono hsub2).trans_eq ?_) (le_trans (le_of_eq ?_)
      (measure_mono hsub1))
    · rw [Real.volume_Ico, hlen, ENNReal.ofReal_div_of_pos hn, ENNReal.ofReal_one]
      norm_cast
    · rw [Real.volume_Ioo, hlen, ENNReal.ofReal_div_of_pos hn, ENNReal.ofReal_one]
      norm_cast
  · have hint : range (n + 1) ∩ {k} = ∅ := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      omega
    rw [hint, card_empty, Nat.cast_zero, ENNReal.zero_div]
    convert measure_empty (μ := volume)
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ioo,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro h hu0 hu1
    have : ⌊((n : ℝ) + 1) * u⌋₊ < n + 1 := by
      rw [Nat.floor_lt (by positivity)]
      push_cast
      nlinarith
    omega

/-- **Reduced-precision normal inputs converge in distribution to `N(0, 1)`** (Giles 2015, §10.2,
p. 62, l. 2775–2781: "Random numbers can be generated in steps by `I_n → U_n → Z_n` where `I_n` is
a random integer on a range `[0, I_max]`, `U_n = (I_n + ½)/I_max` is a random, approximately
uniformly-distributed variable on the interval `(0, 1)`, and `Z_n = Φ⁻¹(U_n)` is the corresponding
`N(0, 1)` random variable").  **Correction.**  For `I_n = I_max ≥ 1` the printed
`U_n = (I_n + ½)/I_max = 1 + 1/(2I_max)` exceeds `1`, where `Φ⁻¹` is undefined (second conjunct);
dividing by `I_max + 1` puts every `U_n` in `(0, 1)` (first conjunct).  With this correction, if
`I` is uniform on `{0, …, I_max}`, then `Φ⁻¹((I + ½)/(I_max + 1))` converges in distribution to
`N(0, 1)` as `I_max → ∞` (third conjunct, `I_max = n`, `normCDFInv` = `Φ⁻¹`): it has the law of
`Φ⁻¹((⌊(I_max + 1)U⌋ + ½)/(I_max + 1))` with `U` uniform on `(0, 1)` (`map_floor_uniform`), which
converges to `Φ⁻¹(U) ~ N(0, 1)` pointwise.  (Numerically the Kolmogorov distance to `N(0, 1)` is
`1/(2(I_max + 1))`.) -/
theorem tendstoInDistribution_normCDFInv_midpoint {Ω Ω' : Type*} [MeasurableSpace Ω]
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {I : ℕ → Ω → ℕ}
    (hI : ∀ n, HasLaw (I n) (uniformOn (range (n + 1) : Set ℕ)) P) {G : Ω' → ℝ}
    (hG : HasLaw G (gaussianReal 0 1) P') :
    (∀ n k : ℕ, k ≤ n → ((k : ℝ) + 1 / 2) / (n + 1) ∈ Set.Ioo 0 1) ∧
    (∀ n : ℕ, 0 < n → 1 < ((n : ℝ) + 1 / 2) / n) ∧
    TendstoInDistribution (fun n ω => normCDFInv (((I n ω : ℝ) + 1 / 2) / (n + 1))) atTop G
      (fun _ => P) P' := by
  have hprob : IsProbabilityMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  set f : ℕ → ℕ → ℝ := fun n k => normCDFInv (((k : ℝ) + 1 / 2) / (n + 1)) with hf
  set J : ℕ → ℝ → ℕ := fun n u => ⌊((n : ℝ) + 1) * u⌋₊ with hJ
  have hfm : ∀ n, Measurable (f n) := fun n => measurable_from_nat
  have hJm : ∀ n, Measurable (J n) := fun n => (measurable_id.const_mul _).nat_floor
  refine ⟨fun n k hk => ⟨by positivity, ?_⟩, fun n hn => ?_, ?_⟩
  · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_one hn]
    have : (k : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [one_lt_div hn']
    linarith
  -- the comparison sequence `f_n(⌊(n + 1) U⌋)` with `U` uniform on `(0, 1)`
  have hY : TendstoInDistribution (fun n u => f n (J n u)) atTop normCDFInv
      (fun _ => volume.restrict (Set.Ioo (0 : ℝ) 1)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    refine TendstoInMeasure.tendstoInDistribution ?_
      fun n => ((hfm n).comp (hJm n)).aemeasurable
    refine tendstoInMeasure_of_tendsto_ae
      (fun n => ((hfm n).comp (hJm n)).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun u hu => ?_
    have hc : ContinuousAt normCDFInv u :=
      continuousOn_normCDFInv.continuousAt (isOpen_Ioo.mem_nhds hu)
    refine hc.tendsto.comp ?_
    -- `|(⌊(n + 1)u⌋ + 1/2)/(n + 1) − u| ≤ 1/(n + 1)`
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlo : Tendsto (fun n : ℕ => u - 1 / ((n : ℝ) + 1)) atTop (𝓝 u) := by
      simpa using tendsto_const_nhds.sub h0
    have hhi : Tendsto (fun n : ℕ => u + 1 / ((n : ℝ) + 1)) atTop (𝓝 u) := by
      simpa using tendsto_const_nhds.add h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n => ?_) (fun n => ?_)
    · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 := Nat.lt_floor_add_one (((n : ℝ) + 1) * u)
      show u - 1 / ((n : ℝ) + 1) ≤ ((⌊((n : ℝ) + 1) * u⌋₊ : ℝ) + 1 / 2) / (n + 1)
      have e : (u - 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = ((n : ℝ) + 1) * u - 1 := by
        field_simp
      rw [le_div_iff₀ hn, e]
      linarith
    · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 := Nat.floor_le (by nlinarith [hu.1] : (0 : ℝ) ≤ ((n : ℝ) + 1) * u)
      show ((⌊((n : ℝ) + 1) * u⌋₊ : ℝ) + 1 / 2) / (n + 1) ≤ u + 1 / ((n : ℝ) + 1)
      have e : (u + 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = ((n : ℝ) + 1) * u + 1 := by
        field_simp
      rw [div_le_iff₀ hn, e]
      linarith
  -- the two sequences have the same laws, and so do the limits
  have hlaw : ∀ n, P.map (fun ω => f n (I n ω)) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).map (fun u => f n (J n u)) := fun n => by
    have e1 : P.map (fun ω => f n (I n ω)) = (P.map (I n)).map (f n) :=
      (AEMeasurable.map_map_of_aemeasurable (hfm n).aemeasurable (hI n).aemeasurable).symm
    have e2 : (volume.restrict (Set.Ioo (0 : ℝ) 1)).map (fun u => f n (J n u)) =
        ((volume.restrict (Set.Ioo (0 : ℝ) 1)).map (J n)).map (f n) :=
      (Measure.map_map (hfm n) (hJm n)).symm
    rw [e1, e2, (hI n).map_eq, hJ, map_floor_uniform n]
  refine ⟨fun n => ((hfm n).comp_aemeasurable (hI n).aemeasurable), hG.aemeasurable, ?_⟩
  have hlim : (⟨P'.map G, Measure.isProbabilityMeasure_map hG.aemeasurable⟩ :
      ProbabilityMeasure ℝ) = ⟨(volume.restrict (Set.Ioo (0 : ℝ) 1)).map normCDFInv,
        Measure.isProbabilityMeasure_map measurable_normCDFInv.aemeasurable⟩ :=
    Subtype.ext (hG.map_eq.trans map_normCDFInv.symm)
  rw [hlim]
  refine hY.tendsto.congr fun n => ?_
  exact Subtype.ext (hlaw n).symm

end midpoint

/-! ### Haas–Giles 2025, §2.1: for GBM and Euler–Maruyama, `V_ℓ C_ℓ` is bounded below -/

section gbmVariance

/-- The pairs `(z_{2k}, z_{2k+1})` of independent standard normal increments are independent pairs
of independent standard normals (Giles 2015, §5.1, the fine increments of a coarse step; Haas–Giles
2025, (5)): `z ↦ (k ↦ (z_{2k+i})_{i<2})` maps `N(0,1)^{⊗ℕ}` to `(N(0,1)^{⊗2})^{⊗ℕ}`. -/
lemma measurePreserving_pairBlocks :
    MeasurePreserving (fun (z : ℕ → ℝ) (k : ℕ) (i : Fin 2) => z (2 * k + i)) stdNormalSeq
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) := by
  have hf : Function.Injective (fun p : ℕ × Fin 2 => 2 * p.1 + (p.2 : ℕ)) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    change 2 * a + (i : ℕ) = 2 * b + (j : ℕ) at h
    have hi := i.isLt
    have hj := j.isLt
    obtain rfl : a = b := by omega
    obtain rfl : i = j := Fin.ext (by omega)
    rfl
  have m1 : MeasurePreserving (fun (z : ℕ → ℝ) (p : ℕ × Fin 2) => z (2 * p.1 + (p.2 : ℕ)))
      stdNormalSeq (Measure.infinitePi fun _ : ℕ × Fin 2 => gaussianReal 0 1) :=
    ⟨measurable_pi_lambda _ fun p => measurable_pi_apply _,
      Measure.map_infinitePi_infinitePi_of_inj hf⟩
  have m2 : MeasurePreserving (MeasurableEquiv.curry ℕ (Fin 2) ℝ)
      (Measure.infinitePi fun _ : ℕ × Fin 2 => gaussianReal 0 1)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) :=
    ⟨(MeasurableEquiv.curry ℕ (Fin 2) ℝ).measurable,
      Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1)⟩
  exact m2.comp m1

/-- Each pair `(z_{2k}, z_{2k+1})` of independent standard normal increments has the law
`N(0,1)^{⊗2}` (Giles 2015, §5.1). -/
lemma map_pairBlock (k : ℕ) :
    stdNormalSeq.map (fun (z : ℕ → ℝ) (i : Fin 2) => z (2 * k + i)) =
      Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1 := by
  have e : (fun (z : ℕ → ℝ) (i : Fin 2) => z (2 * k + i)) =
      (fun W : ℕ → Fin 2 → ℝ => W k) ∘ fun (z : ℕ → ℝ) (k : ℕ) (i : Fin 2) => z (2 * k + i) :=
    rfl
  rw [e, ← Measure.map_map (measurable_pi_apply k) measurePreserving_pairBlocks.measurable,
    measurePreserving_pairBlocks.map_eq, Measure.infinitePi_map_eval]

/-- The pairs `(z_{2k}, z_{2k+1})`, `k ∈ ℕ`, of independent standard normal increments are
mutually independent (Giles 2015, §5.1). -/
lemma iIndepFun_pairBlocks :
    iIndepFun (fun (k : ℕ) (z : ℕ → ℝ) (i : Fin 2) => z (2 * k + i)) stdNormalSeq := by
  have hm : ∀ k : ℕ, Measurable fun (z : ℕ → ℝ) (i : Fin 2) => z (2 * k + i) := fun k =>
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hm]
  simp_rw [map_pairBlock]
  exact measurePreserving_pairBlocks.map_eq

/-- `E[f(X)g(Y)] = E[f(X)]E[g(Y)]` for a pair `(X, Y) ~ N(0,1)^{⊗2}` (Giles 2015, §5.1). -/
lemma integral_pair_mul {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫ w, f (w 0) * g (w 1) ∂(Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) =
      (∫ x, f x ∂gaussianReal 0 1) * ∫ x, g x ∂gaussianReal 0 1 := by
  have hind : IndepFun (fun w : Fin 2 → ℝ => f (w 0)) (fun w => g (w 1))
      (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) :=
    ((iIndepFun_infinitePi (P := fun _ : Fin 2 => gaussianReal 0 1) (X := fun _ x => x)
      fun _ => measurable_id).indepFun (by decide : (0 : Fin 2) ≠ 1)).comp hf hg
  rw [hind.integral_fun_mul_eq_mul_integral
    (hf.comp (measurable_pi_apply 0)).aestronglyMeasurable
    (hg.comp (measurable_pi_apply 1)).aestronglyMeasurable,
    integral_comp_of_measurePreserving (measurePreserving_eval_infinitePi _ 0)
      hf.aestronglyMeasurable,
    integral_comp_of_measurePreserving (measurePreserving_eval_infinitePi _ 1)
      hg.aestronglyMeasurable]

/-- `f(X)g(Y)` is integrable for a pair `(X, Y) ~ N(0,1)^{⊗2}` if `f(X)` and `g(Y)` are (Giles
2015, §5.1). -/
lemma integrable_pair_mul {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f (gaussianReal 0 1)) (hgi : Integrable g (gaussianReal 0 1)) :
    Integrable (fun w : Fin 2 → ℝ => f (w 0) * g (w 1))
      (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) := by
  have hind : IndepFun (fun w : Fin 2 → ℝ => f (w 0)) (fun w => g (w 1))
      (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) :=
    ((iIndepFun_infinitePi (P := fun _ : Fin 2 => gaussianReal 0 1) (X := fun _ x => x)
      fun _ => measurable_id).indepFun (by decide : (0 : Fin 2) ≠ 1)).comp hf hg
  exact hind.integrable_mul
    ((measurePreserving_eval_infinitePi _ 0).integrable_comp_of_integrable hfi)
    ((measurePreserving_eval_infinitePi _ 1).integrable_comp_of_integrable hgi)

/-- The mean of a product over independent pairs with one marked pair (Giles 2015, §5.1): for
`k < n`, `E[∏_{j<n} ψ(z_{2j}, z_{2j+1}) · χ(z_{2k}, z_{2k+1})] = E[ψχ] E[ψ]^{n−1}`, the means on
the right under the pair law `N(0,1)^{⊗2}`. -/
lemma integral_prod_pairBlocks_mul {ψ χ : (Fin 2 → ℝ) → ℝ} (hψ : Measurable ψ)
    (hχ : Measurable χ) {n k : ℕ} (hk : k < n) :
    ∫ z, (∏ j ∈ range n, ψ (fun i : Fin 2 => z (2 * j + i))) *
        χ (fun i : Fin 2 => z (2 * k + i)) ∂stdNormalSeq =
      (∫ w, ψ w * χ w ∂(Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1)) *
        (∫ w, ψ w ∂(Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1)) ^ (n - 1) := by
  set Φ : ℕ → (Fin 2 → ℝ) → ℝ := fun j w => if j = k then ψ w * χ w else ψ w with hΦ
  have hΦm : ∀ j, Measurable (Φ j) := fun j => by
    simp only [hΦ]
    split_ifs
    · exact hψ.mul hχ
    · exact hψ
  have hpt : ∀ z : ℕ → ℝ, (∏ j ∈ range n, ψ (fun i : Fin 2 => z (2 * j + i))) *
      χ (fun i : Fin 2 => z (2 * k + i)) =
      ∏ j ∈ range n, Φ j (fun i : Fin 2 => z (2 * j + i)) := fun z => by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hk),
      ← Finset.mul_prod_erase (range n) (fun j => Φ j (fun i : Fin 2 => z (2 * j + i)))
        (Finset.mem_range.2 hk)]
    have e : ∏ j ∈ (range n).erase k, Φ j (fun i : Fin 2 => z (2 * j + i)) =
        ∏ j ∈ (range n).erase k, ψ (fun i : Fin 2 => z (2 * j + i)) :=
      Finset.prod_congr rfl fun j hj => by
        simp only [hΦ, if_neg (Finset.ne_of_mem_erase hj)]
    rw [e]
    simp only [hΦ, if_pos rfl]
    ring
  have hind : iIndepFun (fun j (z : ℕ → ℝ) => Φ j (fun i : Fin 2 => z (2 * j + i)))
      stdNormalSeq := iIndepFun_pairBlocks.comp Φ hΦm
  have hlaw : ∀ j, ∫ z, Φ j (fun i : Fin 2 => z (2 * j + i)) ∂stdNormalSeq =
      ∫ w, Φ j w ∂(Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) := fun j => by
    rw [← map_pairBlock j, integral_map
      (measurable_pi_lambda _ fun i => measurable_pi_apply _).aemeasurable
      (hΦm j).aestronglyMeasurable]
  simp_rw [hpt]
  rw [integral_prod_of_iIndepFun hind (fun j => (hΦm j).comp
    (measurable_pi_lambda _ fun i => measurable_pi_apply _)), Finset.prod_congr rfl
    fun j _ => hlaw j, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hk)]
  have e : ∏ j ∈ (range n).erase k,
      ∫ w, Φ j w ∂(Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) =
      ∏ _j ∈ (range n).erase k,
        ∫ w, ψ w ∂(Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) :=
    Finset.prod_congr rfl fun j hj => by simp only [hΦ, if_neg (Finset.ne_of_mem_erase hj)]
  rw [e, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_range.2 hk), card_range]
  simp only [hΦ, if_pos rfl]

/-- `∏_{i<2n} f(i) = ∏_{k<n} f(2k) f(2k+1)` (the fine steps of the coarse steps, Giles 2015,
§5.1). -/
lemma prod_range_two_mul (f : ℕ → ℝ) (n : ℕ) :
    ∏ i ∈ range (2 * n), f i = ∏ k ∈ range n, (f (2 * k) * f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ,
      ih, Finset.prod_range_succ]
    ring

/-- The Cauchy–Schwarz inequality for the covariance, in the form used for the lower bound in
`gbm_em_identity_variance_two_sided` (Haas–Giles 2025, §2.1): `cov(X, G)²/V[G] ≤ V[X]` for square
integrable `X`, `G` with `V[G] > 0` (`0 ≤ V[X − tG]` with `t = cov(X, G)/V[G]`). -/
lemma sq_covariance_div_le_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X G : Ω → ℝ} (hX : MemLp X 2 μ) (hG : MemLp G 2 μ)
    (hV : 0 < variance G μ) : covariance X G μ ^ 2 / variance G μ ≤ variance X μ := by
  set t := covariance X G μ / variance G μ with ht
  have h := variance_nonneg (fun ω => X ω - t * G ω) μ
  rw [variance_fun_sub hX (hG.const_mul t), covariance_const_mul_right,
    variance_const_mul] at h
  have e : covariance X G μ ^ 2 / variance G μ =
      2 * (t * covariance X G μ) - t ^ 2 * variance G μ := by
    rw [ht]
    field_simp
    ring
  linarith

/-- `E[(1 + rh + σ√h Z) Z] = σ√h` for `Z ~ N(0, 1)` (one Euler–Maruyama step of GBM, Giles 2015,
§5.1). -/
lemma integral_gbmEMFactor_mul_id (r σ h : ℝ) :
    ∫ x, gbmEMFactor r σ h x * x ∂gaussianReal 0 1 = σ * Real.sqrt h := by
  have e : (fun x => gbmEMFactor r σ h x * x) =
      fun x => (1 + r * h) * x + σ * Real.sqrt h * x ^ 2 :=
    funext fun x => by rw [gbmEMFactor]; ring
  rw [e, integral_add (integrable_id_gaussian.const_mul _) (integrable_sq_gaussian.const_mul _),
    integral_const_mul, integral_const_mul, integral_id_gaussianReal, integral_sq_gaussian]
  ring

/-- The fine Euler–Maruyama path of GBM on level `ℓ + 1` as a product over the pairs of steps
that make up a coarse step (Giles 2015, §5.1). -/
lemma gbmEM_succ_eq_pairs (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmEM r σ T s₀ (ℓ + 1) z = s₀ * ∏ k ∈ range (2 ^ ℓ),
      (fun w : Fin 2 → ℝ => gbmEMFactor r σ (T / 2 ^ (ℓ + 1)) (w 0) *
        gbmEMFactor r σ (T / 2 ^ (ℓ + 1)) (w 1)) (fun i : Fin 2 => z (2 * k + i)) := by
  rw [gbmEM_eq_prod, pow_succ' 2 ℓ, prod_range_two_mul]
  simp

/-- The coarse Euler–Maruyama path of GBM driven by the summed increments, as a product over the
pairs of fine increments (Giles 2015, §5.1; `pairAvg`). -/
lemma gbmEM_pairAvg_eq_pairs (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmEM r σ T s₀ ℓ (pairAvg z) = s₀ * ∏ k ∈ range (2 ^ ℓ),
      (fun w : Fin 2 → ℝ => gbmEMFactor r σ (T / 2 ^ ℓ) ((w 0 + w 1) / Real.sqrt 2))
        (fun i : Fin 2 => z (2 * k + i)) := by
  rw [gbmEM_eq_prod]
  rfl

/-- The fine GBM path is correlated with each product of paired increments (Haas–Giles 2025,
§2.1): `E[Ŝ^f_{ℓ+1} Z_{2k}Z_{2k+1}] = s₀ σ²h ((1 + rh)²)^{2^ℓ−1}`, `h = T 2^{−(ℓ+1)}`, for
`k < 2^ℓ`. -/
lemma integral_gbm_fine_mul_pair (r σ T s₀ : ℝ) (ℓ : ℕ) {k : ℕ} (hk : k < 2 ^ ℓ) :
    ∫ z, gbmEM r σ T s₀ (ℓ + 1) z * (z (2 * k) * z (2 * k + 1)) ∂stdNormalSeq =
      s₀ * (σ * Real.sqrt (T / 2 ^ (ℓ + 1))) ^ 2 *
        ((1 + r * (T / 2 ^ (ℓ + 1))) ^ 2) ^ (2 ^ ℓ - 1) := by
  set A : ℝ → ℝ := fun x => gbmEMFactor r σ (T / 2 ^ (ℓ + 1)) x with hA
  have hAm : Measurable A := measurable_gbmEMFactor r σ _
  have e : ∀ z : ℕ → ℝ, gbmEM r σ T s₀ (ℓ + 1) z * (z (2 * k) * z (2 * k + 1)) =
      s₀ * ((∏ j ∈ range (2 ^ ℓ), (fun w : Fin 2 → ℝ => A (w 0) * A (w 1))
        (fun i : Fin 2 => z (2 * j + i))) *
        (fun w : Fin 2 → ℝ => w 0 * w 1) (fun i : Fin 2 => z (2 * k + i))) := fun z => by
    rw [gbmEM_succ_eq_pairs]
    simp only [hA, Fin.val_zero, Fin.val_one, add_zero]
    ring
  have key := integral_prod_pairBlocks_mul (ψ := fun w : Fin 2 → ℝ => A (w 0) * A (w 1))
    (χ := fun w : Fin 2 → ℝ => w 0 * w 1)
    ((hAm.comp (measurable_pi_apply 0)).mul (hAm.comp (measurable_pi_apply 1)))
    ((measurable_pi_apply 0).mul (measurable_pi_apply 1)) hk
  simp_rw [e]
  rw [integral_const_mul, key]
  have e1 : (fun w : Fin 2 → ℝ => A (w 0) * A (w 1) * (w 0 * w 1)) =
      fun w => (A (w 0) * w 0) * (A (w 1) * w 1) := funext fun w => by ring
  have h1 : ∫ x, gbmEMFactor r σ (T / 2 ^ (ℓ + 1)) x ∂gaussianReal 0 1 =
      1 + r * (T / 2 ^ (ℓ + 1)) := by
    simpa only [pow_one] using integral_gbmEMFactor_pow_one r σ (T / 2 ^ (ℓ + 1))
  rw [e1, integral_pair_mul (f := fun x => A x * x) (g := fun x => A x * x)
    (hAm.mul measurable_id) (hAm.mul measurable_id), integral_pair_mul hAm hAm]
  simp only [hA, integral_gbmEMFactor_mul_id, h1]
  ring

/-- The coarse Euler–Maruyama factor of a pair of fine increments is uncorrelated with their
product (Haas–Giles 2025, §2.1; Giles 2015, §5.1): for `(w₀, w₁) ~ N(0,1)^{⊗2}`,
`E[(1 + rh + σ√h (w₀ + w₁)/√2) w₀w₁] = 0`, as the factor is affine in `w₀ + w₁`. -/
lemma integral_gbmEMFactor_pairSum_mul (r σ h : ℝ) :
    ∫ w, gbmEMFactor r σ h ((w 0 + w 1) / Real.sqrt 2) * (w 0 * w 1)
      ∂(Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) = 0 := by
  set c₀ : ℝ := 1 + r * h with hc₀
  set c₁ : ℝ := σ * Real.sqrt h / Real.sqrt 2 with hc₁
  -- `E[B(w)·w₀w₁] = c₀ E[w₀]E[w₁] + c₁ E[w₀²]E[w₁] + c₁ E[w₀]E[w₁²] = 0`
  have e1 : (fun w : Fin 2 → ℝ => gbmEMFactor r σ h ((w 0 + w 1) / Real.sqrt 2) * (w 0 * w 1)) =
      fun w => (c₀ * (w 0 * w 1) + c₁ * (w 0 ^ 2 * w 1)) + c₁ * (w 0 * w 1 ^ 2) :=
    funext fun w => by
      simp only [hc₀, hc₁, gbmEMFactor]
      ring
  have hid : Measurable fun x : ℝ => x := measurable_id
  have hsq : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have i1 := integrable_pair_mul hid hid integrable_id_gaussian integrable_id_gaussian
  have i2 := integrable_pair_mul hsq hid integrable_sq_gaussian integrable_id_gaussian
  have i3 := integrable_pair_mul hid hsq integrable_id_gaussian integrable_sq_gaussian
  have j12 : Integrable (fun w : Fin 2 → ℝ => c₀ * (w 0 * w 1) + c₁ * (w 0 ^ 2 * w 1))
      (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) :=
    (i1.const_mul c₀).add (i2.const_mul c₁)
  rw [e1, integral_add j12 (i3.const_mul c₁),
    integral_add (i1.const_mul c₀) (i2.const_mul c₁), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_pair_mul hid hid, integral_pair_mul hsq hid,
    integral_pair_mul hid hsq]
  simp [integral_id_gaussianReal]

/-- The coarse GBM path is uncorrelated with each product of paired increments (Haas–Giles 2025,
§2.1): `E[Ŝ^c_ℓ Z_{2k}Z_{2k+1}] = 0`, as the coarse step is affine in `Z_{2k} + Z_{2k+1}`. -/
lemma integral_gbm_coarse_mul_pair (r σ T s₀ : ℝ) (ℓ : ℕ) {k : ℕ} (hk : k < 2 ^ ℓ) :
    ∫ z, gbmEM r σ T s₀ ℓ (pairAvg z) * (z (2 * k) * z (2 * k + 1)) ∂stdNormalSeq = 0 := by
  set B : (Fin 2 → ℝ) → ℝ := fun w => gbmEMFactor r σ (T / 2 ^ ℓ) ((w 0 + w 1) / Real.sqrt 2)
    with hB
  have hBm : Measurable B :=
    (measurable_gbmEMFactor r σ _).comp
      (((measurable_pi_apply 0).add (measurable_pi_apply 1)).div_const _)
  have e : ∀ z : ℕ → ℝ, gbmEM r σ T s₀ ℓ (pairAvg z) * (z (2 * k) * z (2 * k + 1)) =
      s₀ * ((∏ j ∈ range (2 ^ ℓ), B (fun i : Fin 2 => z (2 * j + i))) *
        (fun w : Fin 2 → ℝ => w 0 * w 1) (fun i : Fin 2 => z (2 * k + i))) := fun z => by
    rw [gbmEM_pairAvg_eq_pairs]
    simp only [hB, Fin.val_zero, Fin.val_one, add_zero]
    ring
  have key := integral_prod_pairBlocks_mul (χ := fun w : Fin 2 → ℝ => w 0 * w 1) hBm
    ((measurable_pi_apply 0).mul (measurable_pi_apply 1)) hk
  simp_rw [e]
  rw [integral_const_mul, key]
  simp only [hB, integral_gbmEMFactor_pairSum_mul, zero_mul, mul_zero]

/-- The mean of a product over the independent pairs of increments (Giles 2015, §5.1):
`E[∏_{j<n} Φ(z_{2j}, z_{2j+1})] = E[Φ]^n`, the mean on the right under `N(0,1)^{⊗2}`. -/
lemma integral_prod_pairBlocks {Φ : (Fin 2 → ℝ) → ℝ} (hΦ : Measurable Φ) (n : ℕ) :
    ∫ z, ∏ j ∈ range n, Φ (fun i : Fin 2 => z (2 * j + i)) ∂stdNormalSeq =
      (∫ w, Φ w ∂(Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1)) ^ n := by
  have hind : iIndepFun (fun j (z : ℕ → ℝ) => Φ (fun i : Fin 2 => z (2 * j + i)))
      stdNormalSeq := iIndepFun_pairBlocks.comp (fun _ => Φ) fun _ => hΦ
  have hlaw : ∀ j, ∫ z, Φ (fun i : Fin 2 => z (2 * j + i)) ∂stdNormalSeq =
      ∫ w, Φ w ∂(Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) := fun j => by
    rw [← map_pairBlock j, integral_map
      (measurable_pi_lambda _ fun i => measurable_pi_apply _).aemeasurable
      hΦ.aestronglyMeasurable]
  rw [integral_prod_of_iIndepFun hind fun j => hΦ.comp
    (measurable_pi_lambda _ fun i => measurable_pi_apply _), Finset.prod_congr rfl
    fun j _ => hlaw j, Finset.prod_const, card_range]

/-- A product over the independent pairs of increments of an integrable function of a pair is
integrable (Giles 2015, §5.1). -/
lemma integrable_prod_pairBlocks {Φ : (Fin 2 → ℝ) → ℝ} (hΦ : Measurable Φ)
    (hi : Integrable Φ (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1)) (n : ℕ) :
    Integrable (fun z => ∏ j ∈ range n, Φ (fun i : Fin 2 => z (2 * j + i))) stdNormalSeq :=
  integrable_prod_of_iIndepFun (X := fun j (z : ℕ → ℝ) => Φ (fun i : Fin 2 => z (2 * j + i)))
    (iIndepFun_pairBlocks.comp (fun _ => Φ) fun _ => hΦ)
    (fun _ => hΦ.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _))
    (fun j => (MeasurePreserving.integrable_comp_of_integrable
      ⟨measurable_pi_lambda _ fun _ => measurable_pi_apply _, map_pairBlock j⟩ hi)) _

/-- `e^{−2x} ≤ 1 − x` for `0 ≤ x ≤ ½` (for the lower bound of the GBM correction variance,
Haas–Giles 2025, §2.1). -/
lemma exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have h1 := Real.add_one_le_exp (2 * x)
  have hpos : 0 < 1 + 2 * x := by linarith
  have h2 : Real.exp (-(2 * x)) ≤ (1 + 2 * x)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hpos (by linarith)
  refine h2.trans ?_
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith

/-- **For GBM, Euler–Maruyama and the payoff `P = S_T`, `V_ℓ` is of exact order `2^{−ℓ}`**
(Haas–Giles 2025, §2.1, p. 3, l. 159–164: "if the factor `V_ℓC_ℓ` decreases (resp. increases) with
level then the total cost of MLMC is approximately `ε^{−2}V_0C_0` (resp. `ε^{−2}V_LC_L`) … Since we
know that the cost of a sample increases with level and for Lipschitz payoffs for the
Euler-Maruyama scheme the variance `V_ℓ` decreases exponentially with level, the former leads to
the MLMC estimation being cheaper than the standard Monte Carlo estimation").  Let
`dS = rS dt + σS dW`, `S_0 = s₀`, `T ≥ 0`, and let level `ℓ + 1` use `2^{ℓ+1}` Euler–Maruyama steps,
the coarse path being driven by the summed increments (`gbmEM`, `pairAvg`).  For the Lipschitz
payoff `g(x) = x` the correction `D = Ŝ^f_{ℓ+1} − Ŝ^c_ℓ` is square integrable and, if `|r|T ≤ 2^ℓ`,
`s₀²σ⁴T²e^{−4|r|T}/4 · 2^{−ℓ} ≤ V[D] ≤ 6 C(T) T 2^{−(ℓ+1)}`, `C(T) = gbmStrongConst r σ T s₀`
(the upper bound is `gbm_correction_variance_le`).  So `V_ℓ` decreases exponentially, but only at
the rate `β = 1` at which the cost `C_ℓ = 2^ℓ` grows.  Lower bound: with
`G = ∑_{k<2^ℓ} Z_{2k}Z_{2k+1}`, `V[G] = 2^ℓ` and `V[D] ≥ cov(D, G)²/V[G]`
(`sq_covariance_div_le_variance`); by the independence of the pairs
`cov(D, G) = 2^ℓ s₀σ²h (1 + rh)^{2(2^ℓ−1)}`, `h = T2^{−(ℓ+1)}`
(`integral_gbm_fine_mul_pair`, `integral_gbm_coarse_mul_pair`), and
`(1 + rh)^{4(2^ℓ−1)} ≥ e^{−4|r|T}` for `|r|h ≤ ½`.  (Checked against the exact variance for
`|r| ≤ 3`, `σ ≤ 2`, `T ≤ 3`, `ℓ ≤ 13`; for `r = 0` and `ℓ = 0` the bound before the last step is
the exact variance.)  The hypothesis `|r|T ≤ 2^ℓ` is a restriction of the proof (the last step
needs `|r|h ≤ ½`; at `1 + rh = 0` the covariance with `G` vanishes): numerically the lower bound
holds at every level (exact variance for `r ∈ [−40, 40]` in steps of `½`,
`σ ∈ {0.01, 0.1, 0.5, 1, 3}`, `T ∈ {0.1, 1, 3, 10}`, `ℓ ≤ 7`, `|r|T > 2^ℓ`: ratio `≥ 148`).  At
every level `gbm_em_identity_variance_ge_pow` gives the weaker bound
`V[D] ≥ s₀²(σ²h)^{2^{ℓ+1}}` (`> 0` if `s₀σ ≠ 0` and `T > 0`), which is all
`gbm_em_identity_variance_cost` needs. -/
theorem gbm_em_identity_variance_two_sided (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {ℓ : ℕ}
    (hℓ : |r| * T ≤ 2 ^ ℓ) :
    MemLp (fun z => gbmEM r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ ℓ (pairAvg z)) 2 stdNormalSeq ∧
    s₀ ^ 2 * σ ^ 4 * T ^ 2 * Real.exp (-(4 * |r| * T)) / 4 * ((2 : ℝ) ^ ℓ)⁻¹ ≤
      variance (fun z => gbmEM r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ ℓ (pairAvg z))
        stdNormalSeq ∧
    variance (fun z => gbmEM r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ ℓ (pairAvg z)) stdNormalSeq ≤
      6 * (gbmStrongConst r σ T s₀ * T) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ := by
  set n : ℕ := 2 ^ ℓ with hn
  set h : ℝ := T / 2 ^ (ℓ + 1) with hh
  set D : (ℕ → ℝ) → ℝ := fun z => gbmEM r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ ℓ (pairAvg z)
    with hDdef
  set X : ℕ → (ℕ → ℝ) → ℝ := fun k z => z (2 * k) * z (2 * k + 1) with hXdef
  set π₂ : Measure (Fin 2 → ℝ) := Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1
    with hπ₂
  have hn0 : (0 : ℝ) < n := by rw [hn]; positivity
  have hh0 : 0 ≤ h := by rw [hh]; positivity
  have hD : MemLp D 2 stdNormalSeq :=
    (memLp_gbmEM r σ T s₀ (ℓ + 1)).sub
      ((memLp_gbmEM r σ T s₀ ℓ).comp_measurePreserving measurePreserving_pairAvg)
  -- the test variables `X_k = z_{2k} z_{2k+1}`
  have hid : Measurable fun x : ℝ => x := measurable_id
  have hsq : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have hχm : Measurable fun w : Fin 2 → ℝ => w 0 * w 1 :=
    (measurable_pi_apply 0).mul (measurable_pi_apply 1)
  have hW : ∀ k, MeasurePreserving (fun (z : ℕ → ℝ) (i : Fin 2) => z (2 * k + i))
      stdNormalSeq π₂ := fun k =>
    ⟨measurable_pi_lambda _ fun i => measurable_pi_apply _, map_pairBlock k⟩
  have hχ2 : MemLp (fun w : Fin 2 → ℝ => w 0 * w 1) 2 π₂ := by
    refine (memLp_two_iff_integrable_sq hχm.aestronglyMeasurable).2 ?_
    have e : (fun w : Fin 2 → ℝ => (w 0 * w 1) ^ 2) = fun w => w 0 ^ 2 * w 1 ^ 2 :=
      funext fun w => by ring
    rw [e]
    exact integrable_pair_mul hsq hsq integrable_sq_gaussian integrable_sq_gaussian
  have hX : ∀ k, MemLp (X k) 2 stdNormalSeq := fun k => hχ2.comp_measurePreserving (hW k)
  have hlawX : ∀ k {φ : (Fin 2 → ℝ) → ℝ}, Measurable φ →
      ∫ z, φ (fun i : Fin 2 => z (2 * k + i)) ∂stdNormalSeq = ∫ w, φ w ∂π₂ := fun k φ hφ =>
    integral_comp_of_measurePreserving (hW k) hφ.aestronglyMeasurable
  have hEX : ∀ k, ∫ z, X k z ∂stdNormalSeq = 0 := fun k => by
    have := hlawX k hχm
    simp only [Fin.val_zero, Fin.val_one, add_zero] at this
    rw [this, integral_pair_mul hid hid, integral_id_gaussianReal, zero_mul]
  have hVX : ∀ k, variance (X k) stdNormalSeq = 1 := fun k => by
    rw [variance_eq_sub (hX k), hEX k]
    have h2 : Measurable fun w : Fin 2 → ℝ => (w 0 * w 1) ^ 2 := hχm.pow_const 2
    have := hlawX k h2
    simp only [Fin.val_zero, Fin.val_one, add_zero] at this
    have e : (fun w : Fin 2 → ℝ => (w 0 * w 1) ^ 2) = fun w => w 0 ^ 2 * w 1 ^ 2 :=
      funext fun w => by ring
    rw [e, integral_pair_mul hsq hsq, integral_sq_gaussian] at this
    simp only [Pi.pow_apply]
    rw [this]
    norm_num
  -- `V[G] = n` for `G = ∑_{k<n} X_k`
  have hindX : iIndepFun X stdNormalSeq :=
    iIndepFun_pairBlocks.comp (fun _ (w : Fin 2 → ℝ) => w 0 * w 1) fun _ => hχm
  have hVG : variance (∑ k ∈ range n, X k) stdNormalSeq = n := by
    rw [IndepFun.variance_sum (fun k _ => hX k)
      (fun i _ j _ hij => hindX.indepFun hij)]
    simp [hVX]
  -- `cov(D, G) = n s₀ σ² h (1 + rh)^{2(n−1)}`
  have hcovk : ∀ k ∈ range n, covariance D (X k) stdNormalSeq =
      s₀ * (σ * Real.sqrt h) ^ 2 * ((1 + r * h) ^ 2) ^ (n - 1) := fun k hk => by
    have hkn : k < 2 ^ ℓ := Finset.mem_range.1 hk
    rw [covariance_eq_sub hD (hX k), hEX k, mul_zero, sub_zero]
    have hF : Integrable (fun z => gbmEM r σ T s₀ (ℓ + 1) z * X k z) stdNormalSeq :=
      (memLp_gbmEM r σ T s₀ (ℓ + 1)).integrable_mul (hX k)
    have hC : Integrable (fun z => gbmEM r σ T s₀ ℓ (pairAvg z) * X k z) stdNormalSeq :=
      ((memLp_gbmEM r σ T s₀ ℓ).comp_measurePreserving measurePreserving_pairAvg).integrable_mul
        (hX k)
    have e : (D * X k) = fun z => gbmEM r σ T s₀ (ℓ + 1) z * X k z -
        gbmEM r σ T s₀ ℓ (pairAvg z) * X k z := funext fun z => by
      simp only [Pi.mul_apply, hDdef]
      ring
    rw [e, integral_sub hF hC]
    simp only [hXdef]
    rw [integral_gbm_fine_mul_pair r σ T s₀ ℓ hkn, integral_gbm_coarse_mul_pair r σ T s₀ ℓ hkn,
      sub_zero]
  have hcov : covariance D (∑ k ∈ range n, X k) stdNormalSeq =
      n * (s₀ * (σ * Real.sqrt h) ^ 2 * ((1 + r * h) ^ 2) ^ (n - 1)) := by
    rw [covariance_sum_right' (fun k _ => hX k) hD, Finset.sum_congr rfl hcovk,
      Finset.sum_const, card_range, nsmul_eq_mul]
  have hG : MemLp (∑ k ∈ range n, X k) 2 stdNormalSeq := memLp_finsetSum' _ fun k _ => hX k
  have hlow := sq_covariance_div_le_variance hD hG (by rw [hVG]; exact hn0)
  rw [hcov, hVG] at hlow
  -- the upper bound is `gbm_correction_variance_le` for `g(x) = x`
  have hup := (gbm_correction_variance_le r σ s₀ hT (g := fun x => x) (K := 1)
    (fun x y => by rw [one_mul]) ℓ).2
  rw [one_pow, mul_one] at hup
  refine ⟨hD, le_trans ?_ hlow, hup⟩
  -- `(1 + rh)^{4(n−1)} ≥ e^{−4|r|T}` as `|r|h ≤ 1/2`
  set x : ℝ := |r| * h with hx
  have hx0 : 0 ≤ x := mul_nonneg (abs_nonneg r) hh0
  have hnh : (n : ℝ) * h = T / 2 := by
    rw [hn, hh, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    field_simp
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, hh, mul_div_assoc', div_le_iff₀ (by positivity), pow_succ]
    have e : (1 : ℝ) / 2 * (2 ^ ℓ * 2) = 2 ^ ℓ := by ring
    linarith
  set q : ℝ := ((1 + r * h) ^ 2) ^ (n - 1) with hq
  have he := exp_neg_two_mul_le_one_sub hx0 hx1
  have ha : 1 - x ≤ 1 + r * h := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le r) hh0
    rw [hx]
    linarith
  have ha2 : Real.exp (-(4 * x)) ≤ (1 + r * h) ^ 2 := by
    have e : Real.exp (-(4 * x)) = Real.exp (-(2 * x)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (he.trans ha) 2
  have hq1 : Real.exp (-(4 * x * n)) ≤ q := by
    have e : Real.exp (-(4 * x)) ^ (n - 1) = Real.exp (-(4 * x) * ((n - 1 : ℕ) : ℝ)) := by
      rw [← Real.exp_nat_mul, mul_comm]
    have h1 : Real.exp (-(4 * x) * ((n - 1 : ℕ) : ℝ)) ≤ q := by
      rw [← e, hq]
      exact pow_le_pow_left₀ (Real.exp_pos _).le ha2 _
    refine le_trans (Real.exp_le_exp.2 ?_) h1
    have hn1 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    nlinarith
  have hq0 : 0 ≤ Real.exp (-(4 * x * n)) := (Real.exp_pos _).le
  have hq2 : Real.exp (-(4 * |r| * T)) ≤ q ^ 2 := by
    have e : Real.exp (-(4 * |r| * T)) = Real.exp (-(4 * x * n)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hT2 : T = 2 * ((n : ℝ) * h) := by rw [hnh]; ring
      rw [hx, hT2]
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ hq0 hq1 2
  have hσh : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh0]
  have hn' : ((2 : ℝ) ^ ℓ)⁻¹ = (n : ℝ)⁻¹ := by rw [hn]; push_cast; ring
  have key : ((n : ℝ) * (s₀ * (σ * Real.sqrt h) ^ 2 * q)) ^ 2 / n =
      s₀ ^ 2 * σ ^ 4 * ((n : ℝ) * h) ^ 2 * q ^ 2 / n := by
    rw [hσh]
    field_simp
  rw [key, hnh, hn']
  calc s₀ ^ 2 * σ ^ 4 * T ^ 2 * Real.exp (-(4 * |r| * T)) / 4 * (n : ℝ)⁻¹ =
        s₀ ^ 2 * σ ^ 4 * T ^ 2 / (4 * n) * Real.exp (-(4 * |r| * T)) := by
        field_simp
    _ ≤ s₀ ^ 2 * σ ^ 4 * T ^ 2 / (4 * n) * q ^ 2 :=
        mul_le_mul_of_nonneg_left hq2 (by positivity)
    _ = s₀ ^ 2 * σ ^ 4 * (T / 2) ^ 2 * q ^ 2 / n := by
        field_simp
        ring

/-- The GBM correction variance is positive at every level (Haas–Giles 2025, §2.1): for GBM,
Euler–Maruyama and the payoff `g(x) = x`, `T ≥ 0` and every `ℓ`,
`V[Ŝ^f_{ℓ+1} − Ŝ^c_ℓ] ≥ s₀²(σ²h)^{2^{ℓ+1}}`, `h = T 2^{−(ℓ+1)}`, which is `> 0` if `s₀σ ≠ 0` and
`T > 0`.  The test variable is the product `Y = ∏_{i<2^{ℓ+1}} z_i = ∏_{k<2^ℓ} z_{2k}z_{2k+1}` of
all fine increments: `E[Y] = 0`, `V[Y] = 1`, `E[Ŝ^f Y] = s₀(σ²h)^{2^ℓ}` (each fine factor
contributes `E[(1 + rh + σ√h Z)Z] = σ√h`) and `E[Ŝ^c Y] = 0` (`integral_gbmEMFactor_pairSum_mul`),
so `V[D] ≥ cov(D, Y)²/V[Y]` (`sq_covariance_div_le_variance`).  Unlike the covariance with
`∑_k z_{2k}z_{2k+1}` in `gbm_em_identity_variance_two_sided`, this one never vanishes (also not
at `1 + rh = 0`), but the bound is super-exponentially small in `ℓ`. -/
lemma gbm_em_identity_variance_ge_pow (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (ℓ : ℕ) :
    s₀ ^ 2 * (σ ^ 2 * (T / 2 ^ (ℓ + 1))) ^ 2 ^ (ℓ + 1) ≤
      variance (fun z => gbmEM r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ ℓ (pairAvg z))
        stdNormalSeq := by
  set h : ℝ := T / 2 ^ (ℓ + 1) with hh
  have hh0 : 0 ≤ h := by rw [hh]; positivity
  have hn0 : 2 ^ ℓ ≠ 0 := by positivity
  have hid : Measurable fun x : ℝ => x := measurable_id
  have hsq : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have hχm : Measurable fun w : Fin 2 → ℝ => w 0 * w 1 :=
    (measurable_pi_apply 0).mul (measurable_pi_apply 1)
  have hWm : ∀ j : ℕ, Measurable fun (z : ℕ → ℝ) (i : Fin 2) => z (2 * j + i) := fun _ =>
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hχ2m : Measurable fun w : Fin 2 → ℝ => w 0 ^ 2 * w 1 ^ 2 :=
    ((measurable_pi_apply 0).pow_const 2).mul ((measurable_pi_apply 1).pow_const 2)
  -- the test variable `Y = ∏_{j<2^ℓ} z_{2j} z_{2j+1}`
  obtain ⟨Y, hYdef⟩ : ∃ Y : (ℕ → ℝ) → ℝ, Y = fun z => ∏ j ∈ range (2 ^ ℓ),
      (fun w : Fin 2 → ℝ => w 0 * w 1) (fun i : Fin 2 => z (2 * j + i)) := ⟨_, rfl⟩
  have hYm : Measurable Y := by
    rw [hYdef]
    exact Finset.measurable_prod _ fun j _ => hχm.comp (hWm j)
  have hY2 : (fun z => Y z ^ 2) = fun z => ∏ j ∈ range (2 ^ ℓ),
      (fun w : Fin 2 → ℝ => w 0 ^ 2 * w 1 ^ 2) (fun i : Fin 2 => z (2 * j + i)) :=
    funext fun z => by
      rw [hYdef, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      ring
  have hYL2 : MemLp Y 2 stdNormalSeq := by
    refine (memLp_two_iff_integrable_sq hYm.aestronglyMeasurable).2 ?_
    rw [hY2]
    exact integrable_prod_pairBlocks hχ2m
      (integrable_pair_mul hsq hsq integrable_sq_gaussian integrable_sq_gaussian) _
  have hEY : ∫ z, Y z ∂stdNormalSeq = 0 := by
    rw [hYdef, integral_prod_pairBlocks hχm, integral_pair_mul hid hid, integral_id_gaussianReal,
      zero_mul, zero_pow hn0]
  have hVY : variance Y stdNormalSeq = 1 := by
    rw [variance_eq_sub hYL2, hEY]
    simp only [Pi.pow_apply]
    rw [hY2, integral_prod_pairBlocks hχ2m, integral_pair_mul hsq hsq, integral_sq_gaussian]
    norm_num
  -- `cov(D, Y) = E[Ŝ^f Y] − E[Ŝ^c Y] = s₀ (σ²h)^{2^ℓ} − 0`
  have hD : MemLp (fun z => gbmEM r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ ℓ (pairAvg z)) 2
      stdNormalSeq :=
    (memLp_gbmEM r σ T s₀ (ℓ + 1)).sub
      ((memLp_gbmEM r σ T s₀ ℓ).comp_measurePreserving measurePreserving_pairAvg)
  have hF : Integrable (fun z => gbmEM r σ T s₀ (ℓ + 1) z * Y z) stdNormalSeq :=
    (memLp_gbmEM r σ T s₀ (ℓ + 1)).integrable_mul hYL2
  have hC : Integrable (fun z => gbmEM r σ T s₀ ℓ (pairAvg z) * Y z) stdNormalSeq :=
    ((memLp_gbmEM r σ T s₀ ℓ).comp_measurePreserving measurePreserving_pairAvg).integrable_mul
      hYL2
  have hfine : ∫ z, gbmEM r σ T s₀ (ℓ + 1) z * Y z ∂stdNormalSeq = s₀ * (σ ^ 2 * h) ^ 2 ^ ℓ := by
    have e : (fun z => gbmEM r σ T s₀ (ℓ + 1) z * Y z) = fun z => s₀ * ∏ j ∈ range (2 ^ ℓ),
        (fun w : Fin 2 → ℝ => (gbmEMFactor r σ h (w 0) * w 0) * (gbmEMFactor r σ h (w 1) * w 1))
          (fun i : Fin 2 => z (2 * j + i)) := funext fun z => by
      rw [gbmEM_succ_eq_pairs, hYdef, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      ring
    have hm : Measurable fun w : Fin 2 → ℝ =>
        (gbmEMFactor r σ h (w 0) * w 0) * (gbmEMFactor r σ h (w 1) * w 1) :=
      (((measurable_gbmEMFactor r σ h).comp (measurable_pi_apply 0)).mul
        (measurable_pi_apply 0)).mul
        (((measurable_gbmEMFactor r σ h).comp (measurable_pi_apply 1)).mul
          (measurable_pi_apply 1))
    rw [e, integral_const_mul, integral_prod_pairBlocks hm,
      integral_pair_mul (f := fun x => gbmEMFactor r σ h x * x)
        (g := fun x => gbmEMFactor r σ h x * x) ((measurable_gbmEMFactor r σ h).mul hid)
        ((measurable_gbmEMFactor r σ h).mul hid), integral_gbmEMFactor_mul_id, ← sq, mul_pow,
      Real.sq_sqrt hh0]
  have hcoarse : ∫ z, gbmEM r σ T s₀ ℓ (pairAvg z) * Y z ∂stdNormalSeq = 0 := by
    have e : (fun z => gbmEM r σ T s₀ ℓ (pairAvg z) * Y z) = fun z => s₀ * ∏ j ∈ range (2 ^ ℓ),
        (fun w : Fin 2 → ℝ =>
          gbmEMFactor r σ (T / 2 ^ ℓ) ((w 0 + w 1) / Real.sqrt 2) * (w 0 * w 1))
          (fun i : Fin 2 => z (2 * j + i)) := funext fun z => by
      rw [gbmEM_pairAvg_eq_pairs, hYdef, mul_assoc, ← Finset.prod_mul_distrib]
    have hm : Measurable fun w : Fin 2 → ℝ =>
        gbmEMFactor r σ (T / 2 ^ ℓ) ((w 0 + w 1) / Real.sqrt 2) * (w 0 * w 1) :=
      ((measurable_gbmEMFactor r σ _).comp
        (((measurable_pi_apply 0).add (measurable_pi_apply 1)).div_const _)).mul hχm
    rw [e, integral_const_mul, integral_prod_pairBlocks hm, integral_gbmEMFactor_pairSum_mul,
      zero_pow hn0, mul_zero]
  have hcov : covariance (fun z => gbmEM r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ ℓ (pairAvg z)) Y
      stdNormalSeq = s₀ * (σ ^ 2 * h) ^ 2 ^ ℓ := by
    rw [covariance_eq_sub hD hYL2, hEY, mul_zero, sub_zero]
    have e : ((fun z => gbmEM r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ ℓ (pairAvg z)) * Y) =
        fun z => gbmEM r σ T s₀ (ℓ + 1) z * Y z - gbmEM r σ T s₀ ℓ (pairAvg z) * Y z :=
      funext fun z => by
        simp only [Pi.mul_apply]
        ring
    rw [e, integral_sub hF hC, hfine, hcoarse, sub_zero]
  have hlow := sq_covariance_div_le_variance hD hYL2 (by rw [hVY]; exact one_pos)
  rw [hcov, hVY, div_one] at hlow
  calc s₀ ^ 2 * (σ ^ 2 * h) ^ 2 ^ (ℓ + 1) = (s₀ * (σ ^ 2 * h) ^ 2 ^ ℓ) ^ 2 := by
        rw [mul_pow s₀, ← pow_mul, ← pow_succ]
    _ ≤ _ := hlow

/-- **`V_ℓC_ℓ` stays between two positive constants: the paper's case "`V_ℓC_ℓ` decreases with
level" does not hold** (Haas–Giles 2025, §2.1, p. 3, l. 159–164: "if the factor `V_ℓC_ℓ`
decreases (resp. increases) with level then the total cost of MLMC is approximately
`ε^{−2}V_0C_0` … for Lipschitz payoffs for the Euler-Maruyama scheme the variance `V_ℓ` decreases
exponentially with level, the former leads to the MLMC estimation being cheaper than the standard
Monte Carlo estimation").  For GBM with `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, the Lipschitz payoff
`g(x) = x` and the cost `C_{ℓ+1} = 2^{ℓ+1}` of a level-`(ℓ + 1)` sample, the corrections are
square integrable, and there are `c > 0` and `C` with `c ≤ V_{ℓ+1}C_{ℓ+1} ≤ C` for every level
`ℓ` (`gbm_em_identity_variance_two_sided` for `|r|T ≤ 2^ℓ`, `gbm_em_identity_variance_ge_pow`
for the finitely many other levels); in particular `V_ℓC_ℓ` does not tend to `0`.  So the case
"`V_ℓC_ℓ` decreases with level", in the sense that gives the cost `≈ ε^{−2}V_0C_0` (geometric
decay of `V_ℓC_ℓ`, `β > γ`), does not hold for Euler–Maruyama (`β = γ = 1`), and the cost (8)
`ε^{−2}(∑_ℓ √(V_ℓC_ℓ))²` is of order `ε^{−2}(L + 1)²`.  Numerically `V_ℓC_ℓ` can be monotone
either way: for `r = 0.05`, `σ = 0.2`, `T = 1`, `s₀ = 100`, `V_{ℓ+1}C_{ℓ+1}` increases with `ℓ`,
from `8.5` at `ℓ = 0` to `9.20` at `ℓ = 15`; for `r = −0.5`, `σ = 0.2`, `T = 1`, `s₀ = 1` it
decreases for `ℓ = 0, …, 13` (from `0.0058` to `3.07·10^{−4}`) towards a positive limit.  The
paper's conclusion, that MLMC is cheaper than standard Monte Carlo, still holds asymptotically
(`gbm_mlmc_theorem1`), but not for the reason it gives. -/
theorem gbm_em_identity_variance_cost (r σ s₀ : ℝ) {T : ℝ} (hT : 0 < T) (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) :
    (∀ ℓ : ℕ, MemLp (fun z => gbmEM r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ ℓ (pairAvg z)) 2
      stdNormalSeq) ∧
    ∃ c C : ℝ, 0 < c ∧ (∀ ℓ : ℕ,
      c ≤ 2 ^ (ℓ + 1) * variance (fun z => gbmEM r σ T s₀ (ℓ + 1) z -
        gbmEM r σ T s₀ ℓ (pairAvg z)) stdNormalSeq ∧
      2 ^ (ℓ + 1) * variance (fun z => gbmEM r σ T s₀ (ℓ + 1) z -
        gbmEM r σ T s₀ ℓ (pairAvg z)) stdNormalSeq ≤ C) ∧
    ¬ Tendsto (fun ℓ : ℕ => (2 : ℝ) ^ (ℓ + 1) * variance (fun z => gbmEM r σ T s₀ (ℓ + 1) z -
        gbmEM r σ T s₀ ℓ (pairAvg z)) stdNormalSeq) atTop (𝓝 0) := by
  set f : ℕ → ℝ := fun ℓ => 2 ^ (ℓ + 1) * variance (fun z => gbmEM r σ T s₀ (ℓ + 1) z -
    gbmEM r σ T s₀ ℓ (pairAvg z)) stdNormalSeq with hf
  have hs0 : 0 < s₀ ^ 2 := by positivity
  have hσ0 : 0 < σ ^ 2 := by positivity
  -- `V_{ℓ+1} > 0` at every level
  have hfpos : ∀ ℓ, 0 < f ℓ := fun ℓ => by
    have h := gbm_em_identity_variance_ge_pow r σ s₀ hT.le ℓ
    have hp : 0 < s₀ ^ 2 * (σ ^ 2 * (T / 2 ^ (ℓ + 1))) ^ 2 ^ (ℓ + 1) := by positivity
    simp only [hf]
    positivity [hp.trans_le h]
  -- the upper bound at every level
  have hup : ∀ ℓ, f ℓ ≤ 6 * (gbmStrongConst r σ T s₀ * T) := fun ℓ => by
    have h := (gbm_correction_variance_le r σ s₀ hT.le (g := fun x => x) (K := 1)
      (fun x y => by rw [one_mul]) ℓ).2
    rw [one_pow, mul_one] at h
    have h2 : (0 : ℝ) < 2 ^ (ℓ + 1) := by positivity
    calc f ℓ ≤ 2 ^ (ℓ + 1) * (6 * (gbmStrongConst r σ T s₀ * T) * ((2 : ℝ) ^ (ℓ + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left h h2.le
      _ = _ := by field_simp
  -- the lower bound `c₁` for `|r|T ≤ 2^ℓ`, i.e. for `ℓ ≥ ℓ₀`
  obtain ⟨ℓ₀, hℓ₀⟩ := pow_unbounded_of_one_lt (|r| * T) (one_lt_two : (1 : ℝ) < 2)
  set c₁ : ℝ := s₀ ^ 2 * σ ^ 4 * T ^ 2 * Real.exp (-(4 * |r| * T)) / 2 with hc₁
  have hc₁0 : 0 < c₁ := by
    have : 0 < σ ^ 4 := by positivity
    positivity
  have hlo : ∀ ℓ ≥ ℓ₀, c₁ ≤ f ℓ := fun ℓ hℓ => by
    have hpow : (2 : ℝ) ^ ℓ₀ ≤ 2 ^ ℓ := pow_le_pow_right₀ one_le_two hℓ
    obtain ⟨-, hlo, -⟩ := gbm_em_identity_variance_two_sided r σ s₀ hT.le
      (hℓ₀.le.trans hpow)
    have h2 : (0 : ℝ) < 2 ^ (ℓ + 1) := by positivity
    calc c₁ = 2 ^ (ℓ + 1) * (s₀ ^ 2 * σ ^ 4 * T ^ 2 * Real.exp (-(4 * |r| * T)) / 4 *
          ((2 : ℝ) ^ ℓ)⁻¹) := by
          rw [hc₁, pow_succ]
          field_simp
          ring
      _ ≤ f ℓ := mul_le_mul_of_nonneg_left hlo h2.le
  -- a positive lower bound `c₂` on the finitely many levels `ℓ < ℓ₀`
  have hfin : ∀ m : ℕ, ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ ℓ < m, c₂ ≤ f ℓ := fun m => by
    induction m with
    | zero => exact ⟨1, one_pos, fun ℓ hℓ => absurd hℓ (Nat.not_lt_zero ℓ)⟩
    | succ m ih =>
      obtain ⟨c₂, hc₂, hle⟩ := ih
      refine ⟨min c₂ (f m), lt_min hc₂ (hfpos m), fun ℓ hℓ => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hℓ with h | h
      · exact (min_le_left _ _).trans (hle ℓ h)
      · rw [h]
        exact min_le_right _ _
  obtain ⟨c₂, hc₂, hle₂⟩ := hfin ℓ₀
  have hbd : ∀ ℓ, min c₁ c₂ ≤ f ℓ := fun ℓ => by
    rcases lt_or_ge ℓ ℓ₀ with h | h
    · exact (min_le_right _ _).trans (hle₂ ℓ h)
    · exact (min_le_left _ _).trans (hlo ℓ h)
  refine ⟨fun ℓ => (memLp_gbmEM r σ T s₀ (ℓ + 1)).sub
    ((memLp_gbmEM r σ T s₀ ℓ).comp_measurePreserving measurePreserving_pairAvg),
    min c₁ c₂, 6 * (gbmStrongConst r σ T s₀ * T), lt_min hc₁0 hc₂,
    fun ℓ => ⟨hbd ℓ, hup ℓ⟩, fun hlim => ?_⟩
  have hev := hlim.eventually (gt_mem_nhds (lt_min hc₁0 hc₂))
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exact absurd (hbd N) (not_le.2 (hN N le_rfl))

end gbmVariance

end MLMC
