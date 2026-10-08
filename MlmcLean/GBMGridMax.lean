import MlmcLean.GBMStrongLp
import MlmcLean.GBMPathDependent

/-!
# GBM: the uniform strong error of Euler–Maruyama and lookback options monitored at every step
(Giles 2015, §5.1–§5.2, Table 5.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.1 (p. 29,
l. 1290–1313 of `docs/giles2015.txt`: the coupling by summed Brownian increments, the strong error
"`E[‖S − Ŝ‖²] = O(h)`" and "`V_ℓ = O(h_ℓ)`" for Lipschitz payoffs "such as European, Asian and
lookback options"; p. 30, l. 1319–1321: Theorem 1 gives `O(ε⁻²(log ε)²)`), Table 5.2 (p. 33,
l. 1424–1434, row "lookback", Euler–Maruyama: `O(h)`, `O(h)`; coverage row G5.1-31) and §5.2
(p. 38, l. 1650–1662, "Lookback and barrier options": the estimator "based directly on the minimum
(or maximum) of the values at the discrete timesteps"; coverage row G5.2-23).  Geometric Brownian
motion `dS = rS dt + σS dW` with the exact solution and the Euler–Maruyama path driven by the same
increments `Z_i ∼ N(0,1)` (`stdNormalSeq`).  `MlmcLean.GBMPathDependent` treats a fixed number of
monitoring dates that lie on every grid; here the lookback options are monitored at **every** time
step of each level, so the fine and the coarse payoffs use different sets of times.

* **The uniform strong error** (item (1)).  `gbm_em_grid_max_error`:
  `E[max_{n≤N} (S_{t_n} − Ŝ_n)²] ≤ ((N + 1) C_m(T) h^m)^{1/m}` from the `L^{2m}` errors of
  `MlmcLean.GBMStrongLp` (`gridMax_integral_sup'_sq_le`: `E[max_k X_k²] ≤ (∑_k E[X_k^{2m}])^{1/m}`);
  `gbm_em_grid_max_error_sharp`: the sharp `E[max_{n≤N} (S_{t_n} − Ŝ_n)²] ≤ C h` for all `h ≥ 0`
  and `Nh ≤ T`, by Doob's maximal inequality in `L²`.  Mathlib has only the weak form of Doob's
  inequality; the `L²` form is derived from the pathwise inequality of Acciaio, Beiglböck, Penkner,
  Schachermayer and Temme (2013) (`gridMax_pathwise_doob`) for differences of products of
  independent mean-one factors (`gridMax_doob_prod_martingale`), applied to the martingales
  `S_{t_n} e^{−rnh}` and `Ŝ_n (1 + rh)^{−n}`.
* **The monitoring gap** (item (2)).  `gbm_grid_monitoring_gap_rate`: the maximum (and the
  minimum) of the exact solution over the fine grid minus that over the coarse grid satisfies
  `E[gap²] ≤ C h^{1−δ}` for every `δ > 0`: the gap is at most the largest of `N` one-step
  increments, each `O(h^{1/2})` in every `L^{2m}` (`gbmGrid_expFactor_sub_one_moment`).
* **The lookback correction** (item (3)).  The payoffs `g(max_n Ŝ_n)` (`lookbackPayoff`),
  `g(min_n Ŝ_n)` (`lookbackMinPayoff`) and `g(Ŝ_{2^ℓ} − min_n Ŝ_n)` (`floatLookbackPayoff`) of all
  `2^ℓ + 1` values of the level-`ℓ` path, `g` `K`-Lipschitz:
  `gbm_em_gridLookback_variance_rate`, `gbm_em_gridLookbackMin_variance_rate`,
  `gbm_em_gridFloatLookback_variance_rate`: `V_ℓ = O(h_ℓ^{1−δ})` for every `δ > 0`;
  `gbm_em_gridLookback_mean_converges` (and the min and floating-strike versions): the level means
  converge to a limit `Y`, at rate `O(h_ℓ^{(1−δ)/2})`, and the payoffs of the exact solution
  monitored at the same times have expectations converging to the same `Y`.  This weak rate is
  sharp up to `δ`: monitoring only at the grid times biases the extremum by
  `≈ 0.5826 σ E[max S] h^{1/2}` (Asmussen, Glynn and Pitman 1995; Broadie, Glasserman and Kou
  1997), so the paper's `α = 1` (§5.1, p. 30) does not hold for these payoffs.
* **Theorem 1** (item (4)).  `gbm_em_gridLookback_theorem1` (and the min and floating-strike
  versions): for every `η > 0`, mean square error `< ε²` about `Y` at cost `O(ε^{−2−η})`
  (`α = (1 − δ)/2`, `β = 1 − δ`, `γ = 1`, `δ = η/(2 + η)`).

**How close to the paper.**  The uniform strong error is the paper's `O(h)` (with an existential
constant).  The correction variance is `O(h^{1−δ})` instead of the paper's `O(h)`, hence the cost
`O(ε^{−2−η})` instead of `O(ε⁻²(log ε)²)`: the loss comes only from the monitoring gap of the exact
solution, which is bounded by the maximum of `N` one-step increments.  Removing it needs the
behaviour of the exact path near its maximum (the expected gap is `≈ c σ S h^{1/2}`, as for the
discretely monitored Brownian maximum), which is not formalised.  The weak rate `α = (1 − δ)/2` is
the true order `1/2` up to `δ` (the paper's `α = 1`, p. 30, fails for an extremum monitored at the
grid times, see `gbm_em_gridLookback_mean_converges`); Theorem 1 needs only `α ≥ min(β, γ)/2`,
which `α = 1/2`, `β = γ = 1` satisfy.  A Monte Carlo check at the paper's `r = 0.05`, `σ = 0.2`,
`T = 1` (`S_0 = 1`, 4000 paths per level, `h = 2^{−2}, …, 2^{−9}`) gives
`E[max_n e_n²]/h ≈ 0.0011–0.0017`, `E[gap²]/h ≈ 0.006–0.011` and `V_ℓ/h_ℓ ≈ 0.004–0.008` for
`g(x) = x`, all consistent with `O(h)`.  The limit `Y` is identified with the continuously
monitored price `E[g(max_{0≤t≤T} S_t)]` only informally (the dyadic grids exhaust a dense set of
times and the exact paths are continuous); this needs Brownian paths and is not proved.

**Paper imprecision (§5.2, p. 38, l. 1656–1657).**  "there is an `O(h_ℓ)` difference on average
between the minimum (or maximum) values for the coarse and fine paths": the average difference is
of order `h_ℓ^{1/2}` (in the check above `E[gap]/h^{1/2} ≈ 0.034–0.055` while `E[gap]/h` grows
from `0.07` to `1.8` for `h = 2^{−2}, …, 2^{−10}`); it is the root-mean-square difference
`O(h_ℓ^{1/2})` that gives the paper's `O(h_ℓ)` variance (an `O(h_ℓ)` difference in mean square would
give `O(h_ℓ²)`).

**Milstein.**  The Milstein scheme does not help for the every-step lookback: the monitoring gap of
the exact solution is already of order `h^{1/2}`, so `V_ℓ` stays `O(h)` whatever the scheme.  The
paper's Milstein lookback estimator (§5.2, pp. 38–39, `β = 2`, Table 5.2: `o(h^{2−δ})`) replaces
the discrete maximum by the expected maximum of a Brownian-bridge interpolant within each step
(Giles 2008a); it is not formalised here.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace MLMC

/-- The tangent-line inequality for `t ↦ t^m` on `[0, ∞)`:
`c^m + m c^{m−1} (x − c) ≤ x^m` for `x, c ≥ 0` (Bernoulli's inequality; the Jensen step in the
maximum bound of Giles 2015, §5.1, p. 29, l. 1296–1299 for the uniform strong error). -/
lemma gridMax_pow_tangent_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (m : ℕ) :
    c ^ m + m * c ^ (m - 1) * (x - c) ≤ x ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases hc.eq_or_lt with rfl | hc0
  · rcases Nat.lt_or_ge m 2 with h2 | h2
    · obtain rfl : m = 1 := by omega
      simp
    · rw [zero_pow (by omega), zero_pow (by omega)]
      simp only [mul_zero, zero_mul, add_zero]
      positivity
  · have h1 := one_add_mul_le_pow (a := x / c - 1) (by
      have : 0 ≤ x / c := div_nonneg hx hc0.le
      linarith) m
    have e1 : 1 + (x / c - 1) = x / c := by ring
    rw [e1, div_pow] at h1
    have hcm : 0 < c ^ m := pow_pos hc0 m
    have e2 : c ^ m = c * c ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [le_div_iff₀ hcm] at h1
    have e3 : (1 + m * (x / c - 1)) * c ^ m = c ^ m + m * c ^ (m - 1) * (x - c) := by
      rw [e2]
      field_simp
    linarith

/-- Jensen's inequality for `t ↦ t^m` on `[0, ∞)`: `(E X)^m ≤ E[X^m]` for a nonnegative `X` on a
probability space (from `gridMax_pow_tangent_le`; used to pass from `L^{2m}` bounds to the maximum
over the time grid, Giles 2015, §5.1, p. 29). -/
lemma gridMax_pow_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) (hXi : Integrable X μ) (m : ℕ)
    (hXm : Integrable (fun ω => X ω ^ m) μ) :
    (∫ ω, X ω ∂μ) ^ m ≤ ∫ ω, X ω ^ m ∂μ := by
  set c := ∫ ω, X ω ∂μ with hcdef
  have hc : 0 ≤ c := integral_nonneg hX0
  have hlin : Integrable (fun ω => m * c ^ (m - 1) * (X ω - c)) μ :=
    (hXi.sub (integrable_const c)).const_mul _
  have hint : Integrable (fun ω => c ^ m + m * c ^ (m - 1) * (X ω - c)) μ :=
    (integrable_const _).add hlin
  have hle := integral_mono hint hXm fun ω => gridMax_pow_tangent_le (hX0 ω) hc m
  have he : ∫ ω, (c ^ m + m * c ^ (m - 1) * (X ω - c)) ∂μ = c ^ m := by
    rw [integral_add (integrable_const _) hlin, integral_const_mul,
      integral_sub hXi (integrable_const c)]
    simp [hcdef]
  linarith

/-- **The maximum of finitely many squares from their `2m`-th moments**:
`E[max_{k∈s} X_k²] ≤ (∑_{k∈s} E[X_k^{2m}])^{1/m}` for `m ≥ 1` on a probability space, since
`(max_k X_k²)^m ≤ ∑_k X_k^{2m}` and `(E M)^m ≤ E[M^m]` (Jensen).  This turns the `L^{2m}` strong
errors at the grid times (`gbm_em_moment_error`) into a bound on the maximum over the grid
(Giles 2015, §5.1, p. 29, l. 1296–1299: "the strong error … is `O(h^{1/2})`"); the maximum is
also integrable. -/
lemma gridMax_integral_sup'_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {s : Finset ℕ} (hs : s.Nonempty) {X : ℕ → Ω → ℝ}
    (hXm : ∀ k, Measurable (X k)) {m : ℕ} (hm : 0 < m)
    (hXi : ∀ k ∈ s, Integrable (fun ω => X k ω ^ (2 * m)) μ) :
    Integrable (fun ω => s.sup' hs (fun k => X k ω ^ 2)) μ ∧
    ∫ ω, s.sup' hs (fun k => X k ω ^ 2) ∂μ ≤
      (∑ k ∈ s, ∫ ω, X k ω ^ (2 * m) ∂μ) ^ ((m : ℝ)⁻¹) := by
  set M : Ω → ℝ := fun ω => s.sup' hs (fun k => X k ω ^ 2) with hM
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => by
    obtain ⟨k, hk⟩ := hs
    exact (sq_nonneg (X k ω)).trans (Finset.le_sup' (fun k => X k ω ^ 2) hk)
  have hMm : Measurable M := by
    have := Finset.measurable_sup' hs (f := fun k ω => X k ω ^ 2)
      (fun k _ => (hXm k).pow_const 2)
    convert this using 1
    funext ω
    rw [Finset.sup'_apply]
  have hpt : ∀ ω, M ω ^ m ≤ ∑ k ∈ s, X k ω ^ (2 * m) := fun ω => by
    obtain ⟨k, hk, hke⟩ := Finset.exists_mem_eq_sup' hs (fun k => X k ω ^ 2)
    simp only [hM, hke]
    rw [← pow_mul]
    exact Finset.single_le_sum (f := fun k => X k ω ^ (2 * m))
      (fun j _ => (even_two_mul m).pow_nonneg _) hk
  have hS : Integrable (fun ω => ∑ k ∈ s, X k ω ^ (2 * m)) μ := integrable_finsetSum _ hXi
  have hMmi : Integrable (fun ω => M ω ^ m) μ :=
    hS.mono' (hMm.pow_const m).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (hM0 ω) m)]
      exact hpt ω)
  have hMi : Integrable M μ := by
    refine ((integrable_const (1 : ℝ)).add hMmi).mono' hMm.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (hM0 ω)]
    show M ω ≤ 1 + M ω ^ m
    rcases le_total (M ω) 1 with h1 | h1
    · linarith [pow_nonneg (hM0 ω) m]
    · have : M ω ≤ M ω ^ m := by
        calc M ω = M ω ^ 1 := (pow_one _).symm
          _ ≤ M ω ^ m := pow_le_pow_right₀ h1 hm
      linarith
  have hJ := gridMax_pow_integral_le hM0 hMi m hMmi
  have hI0 : 0 ≤ ∫ ω, M ω ∂μ := integral_nonneg hM0
  have h2 : ∫ ω, M ω ^ m ∂μ ≤ ∑ k ∈ s, ∫ ω, X k ω ^ (2 * m) ∂μ := by
    rw [← integral_finsetSum _ hXi]
    exact integral_mono hMmi hS hpt
  refine ⟨hMi, ?_⟩
  calc ∫ ω, M ω ∂μ = ((∫ ω, M ω ∂μ) ^ m) ^ ((m : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hI0 hm.ne').symm
    _ ≤ (∑ k ∈ s, ∫ ω, X k ω ^ (2 * m) ∂μ) ^ ((m : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg hI0 m) (hJ.trans h2) (by positivity)

/-- `(max_k a_k − max_k b_k)² ≤ max_k (a_k − b_k)²` (the maximum is `1`-Lipschitz for the
sup-norm; Giles 2015, §5.1, p. 29: lookback options are Lipschitz payoffs). -/
lemma gridMax_sq_sup'_sub_le {s : Finset ℕ} (hs : s.Nonempty) (a b : ℕ → ℝ) :
    (s.sup' hs a - s.sup' hs b) ^ 2 ≤ s.sup' hs (fun k => (a k - b k) ^ 2) := by
  obtain ⟨i, hi, hai⟩ := Finset.exists_mem_eq_sup' hs a
  obtain ⟨l, hl, hbl⟩ := Finset.exists_mem_eq_sup' hs b
  have hbi : b i ≤ s.sup' hs b := Finset.le_sup' b hi
  have hal : a l ≤ s.sup' hs a := Finset.le_sup' a hl
  have hsi : (a i - b i) ^ 2 ≤ s.sup' hs (fun k => (a k - b k) ^ 2) :=
    Finset.le_sup' (fun k => (a k - b k) ^ 2) hi
  have hsl : (a l - b l) ^ 2 ≤ s.sup' hs (fun k => (a k - b k) ^ 2) :=
    Finset.le_sup' (fun k => (a k - b k) ^ 2) hl
  rcases le_total (s.sup' hs b) (s.sup' hs a) with h | h
  · have h1 : (s.sup' hs a - s.sup' hs b) ^ 2 ≤ (a i - b i) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    linarith
  · have h1 : (s.sup' hs a - s.sup' hs b) ^ 2 ≤ (b l - a l) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    have e : (b l - a l) ^ 2 = (a l - b l) ^ 2 := by ring
    linarith

/-- `(min_k a_k − min_k b_k)² ≤ max_k (a_k − b_k)²` (the minimum is `1`-Lipschitz for the
sup-norm; Giles 2015, §5.1, p. 29: lookback options are Lipschitz payoffs). -/
lemma gridMax_sq_inf'_sub_le {s : Finset ℕ} (hs : s.Nonempty) (a b : ℕ → ℝ) :
    (s.inf' hs a - s.inf' hs b) ^ 2 ≤ s.sup' hs (fun k => (a k - b k) ^ 2) := by
  obtain ⟨i, hi, hai⟩ := Finset.exists_mem_eq_inf' hs a
  obtain ⟨l, hl, hbl⟩ := Finset.exists_mem_eq_inf' hs b
  have hbi : s.inf' hs b ≤ b i := Finset.inf'_le b hi
  have hal : s.inf' hs a ≤ a l := Finset.inf'_le a hl
  have hsi : (a i - b i) ^ 2 ≤ s.sup' hs (fun k => (a k - b k) ^ 2) :=
    Finset.le_sup' (fun k => (a k - b k) ^ 2) hi
  have hsl : (a l - b l) ^ 2 ≤ s.sup' hs (fun k => (a k - b k) ^ 2) :=
    Finset.le_sup' (fun k => (a k - b k) ^ 2) hl
  rcases le_total (s.inf' hs b) (s.inf' hs a) with h | h
  · have h1 : (s.inf' hs a - s.inf' hs b) ^ 2 ≤ (a l - b l) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    linarith
  · have h1 : (s.inf' hs a - s.inf' hs b) ^ 2 ≤ (b i - a i) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    have e : (b i - a i) ^ 2 = (a i - b i) ^ 2 := by ring
    linarith

/-- The maximum over the coarse grid as a maximum over the fine grid:
`max_{n≤2N} b_{⌊n/2⌋} = max_{k≤N} b_k` (Giles 2015, §5.2, p. 38, l. 1653–1657: the coarse and the
fine minimum or maximum). -/
lemma gridMax_sup'_range_div_two (N : ℕ) (b : ℕ → ℝ) :
    (range (2 * N + 1)).sup' nonempty_range_add_one (fun n => b (n / 2)) =
      (range (N + 1)).sup' nonempty_range_add_one b := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun n hn => ?_
    have : n / 2 ∈ range (N + 1) := by
      rw [mem_range] at hn ⊢
      omega
    exact Finset.le_sup' b this
  · refine Finset.sup'_le _ _ fun k hk => ?_
    have : 2 * k ∈ range (2 * N + 1) := by
      rw [mem_range] at hk ⊢
      omega
    have e : 2 * k / 2 = k := by omega
    have h := Finset.le_sup' (fun n => b (n / 2)) this
    simp only [e] at h
    exact h

/-- The minimum over the coarse grid as a minimum over the fine grid:
`min_{n≤2N} b_{⌊n/2⌋} = min_{k≤N} b_k` (Giles 2015, §5.2, p. 38, l. 1653–1657). -/
lemma gridMax_inf'_range_div_two (N : ℕ) (b : ℕ → ℝ) :
    (range (2 * N + 1)).inf' nonempty_range_add_one (fun n => b (n / 2)) =
      (range (N + 1)).inf' nonempty_range_add_one b := by
  apply le_antisymm
  · refine Finset.le_inf' _ _ fun k hk => ?_
    have : 2 * k ∈ range (2 * N + 1) := by
      rw [mem_range] at hk ⊢
      omega
    have e : 2 * k / 2 = k := by omega
    have h := Finset.inf'_le (fun n => b (n / 2)) this
    simp only [e] at h
    exact h
  · refine Finset.le_inf' _ _ fun n hn => ?_
    have : n / 2 ∈ range (N + 1) := by
      rw [mem_range] at hn ⊢
      omega
    exact Finset.inf'_le b this

/-- `(x − y)^{2m} ≤ 2^{2m−1} (x^{2m} + y^{2m})` (convexity of `t ↦ t^{2m}`; for the moments of
the errors on the grid, Giles 2015, §5.1). -/
lemma gridMax_sub_pow_two_mul_le (x y : ℝ) (m : ℕ) :
    (x - y) ^ (2 * m) ≤ 2 ^ (2 * m - 1) * (x ^ (2 * m) + y ^ (2 * m)) := by
  have he := even_two_mul m
  have h1 : (x - y) ^ (2 * m) ≤ (|x| + |y|) ^ (2 * m) := by
    rw [← he.pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) _
  have h2 := add_pow_le (abs_nonneg x) (abs_nonneg y) (2 * m)
  rw [he.pow_abs, he.pow_abs] at h2
  exact h1.trans h2

/-- `(x + y + w)^{2m} ≤ 3^{2m−1} (x^{2m} + y^{2m} + w^{2m})` (convexity; the splitting of the
fine-minus-coarse difference into two strong errors and a monitoring gap, Giles 2015, §5.1–§5.2). -/
lemma gridMax_add_three_pow_le (x y w : ℝ) (m : ℕ) :
    (x + y + w) ^ (2 * m) ≤ 3 ^ (2 * m - 1) * (x ^ (2 * m) + y ^ (2 * m) + w ^ (2 * m)) := by
  have he := even_two_mul m
  have h1 : (x + y + w) ^ (2 * m) ≤ (|x| + |y| + |w|) ^ (2 * m) := by
    rw [← he.pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans
      (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)) _
  have h2 := add_three_pow_le (abs_nonneg x) (abs_nonneg y) (abs_nonneg w) (2 * m)
  rw [he.pow_abs, he.pow_abs, he.pow_abs] at h2
  exact h1.trans h2

/-- `(X − Y)^{2m}` is integrable if `X^{2m}` and `Y^{2m}` are (Giles 2015, §5.1: moments of
the strong error). -/
lemma gridMax_integrable_sub_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (m : ℕ)
    (hXi : Integrable (fun ω => X ω ^ (2 * m)) μ) (hYi : Integrable (fun ω => Y ω ^ (2 * m)) μ) :
    Integrable (fun ω => (X ω - Y ω) ^ (2 * m)) μ :=
  ((hXi.add hYi).const_mul (2 ^ (2 * m - 1))).mono' ((hX.sub hY).pow _)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg ((even_two_mul m).pow_nonneg _)]
      exact gridMax_sub_pow_two_mul_le _ _ m)

/-! ### The exact solution and the Euler–Maruyama path on the whole time grid -/

/-- **The exact GBM solution at every grid time** (Giles 2015, §5.1, GBM example, p. 30,
l. 1328: `dS_t = r S_t dt + σ S_t dW`, whose solution is `S_t = S_0 exp((r − σ²/2) t + σ W_t)`):
`gbmGridExact r σ h S_0 z n = S_0 exp((r − σ²/2) nh + σ √h ∑_{i<n} z_i)`, the exact solution at
`t_n = nh` with the Brownian increments `W_{t_{i+1}} − W_{t_i} = √h z_i`, the same increments that
drive the Euler–Maruyama path `emPath (gbmDrift r) (gbmVol σ) h S_0 z`. -/
noncomputable def gbmGridExact (r σ h s₀ : ℝ) (z : ℕ → ℝ) (n : ℕ) : ℝ :=
  s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) + σ * (Real.sqrt h * ∑ i ∈ range n, z i))

/-- The exact solution on the grid is a product of i.i.d. one-step factors,
`S_{t_n} = S_0 ∏_{i<n} e^{(r − σ²/2)h + σ√h z_i}` (Giles 2015, §5.1; `gbmExp_eq_prod`). -/
lemma gbmGridExact_eq_prod (r σ h s₀ : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    gbmGridExact r σ h s₀ z n = s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) :=
  gbmExp_eq_prod r σ h s₀ n z

/-- At `t_0 = 0` the exact solution is `S_0` (Giles 2015, §5.1). -/
lemma gbmGridExact_zero (r σ h s₀ : ℝ) (z : ℕ → ℝ) : gbmGridExact r σ h s₀ z 0 = s₀ := by
  simp [gbmGridExact]

/-- **The exact solution is consistent across levels on the whole grid** (Giles 2015, §5.1,
p. 29, l. 1290–1293: "summing the Brownian increments for the fine path timesteps to obtain the
Brownian increments for the coarse timesteps"): the exact solution on the coarse grid of step
`2h`, driven by the coarse increments `(z_{2k} + z_{2k+1})/√2`, is the exact solution on the fine
grid of step `h` at the even times, `S^c_{t_k} = S^f_{t_{2k}}`. -/
lemma gbmGridExact_pairAvg (r σ h s₀ : ℝ) (z : ℕ → ℝ) (k : ℕ) :
    gbmGridExact r σ (2 * h) s₀ (pairAvg z) k = gbmGridExact r σ h s₀ z (2 * k) := by
  have key : Real.sqrt (2 * h) * ∑ i ∈ range k, pairAvg z i =
      Real.sqrt h * ∑ i ∈ range (2 * k), z i := by
    rw [sum_range_two_mul, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [pairAvg]
    rw [← Finset.sum_div]
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  unfold gbmGridExact
  rw [key, Nat.cast_mul, Nat.cast_ofNat, show (2 : ℝ) * k * h = k * (2 * h) by ring]

/-- The exact solution at a grid time is measurable in the increments (Giles 2015, §5.1). -/
lemma measurable_gbmGridExact (r σ h s₀ : ℝ) (n : ℕ) :
    Measurable fun z => gbmGridExact r σ h s₀ z n := by
  simp_rw [gbmGridExact_eq_prod]
  exact measurable_monProd (measurable_gbmExpFactor r σ h) s₀ n

/-- The exact solution on the grid is measurable as a map into `ℕ → ℝ` (Giles 2015, §5.1). -/
lemma measurable_gbmGridExact_pi (r σ h s₀ : ℝ) :
    Measurable fun z => gbmGridExact r σ h s₀ z :=
  measurable_pi_lambda _ fun n => measurable_gbmGridExact r σ h s₀ n

/-- The Euler–Maruyama value of GBM at a grid time is measurable in the increments
(Giles 2015, §5.1). -/
lemma gridMax_measurable_emPath (r σ h s₀ : ℝ) (n : ℕ) :
    Measurable fun z => emPath (gbmDrift r) (gbmVol σ) h s₀ z n := by
  simp_rw [emPath_gbm]
  exact measurable_monProd (measurable_gbmEMFactor r σ h) s₀ n

/-- Every power of the exact solution at a grid time is integrable (Giles 2015, §5.1). -/
lemma integrable_gbmGridExact_pow (r σ h s₀ : ℝ) (n m : ℕ) :
    Integrable (fun z => gbmGridExact r σ h s₀ z n ^ m) stdNormalSeq := by
  simp_rw [gbmGridExact_eq_prod, mul_pow]
  exact (integrable_prod_range_pow (measurable_gbmExpFactor r σ h)
    (integrable_gbmExpFactor_pow r σ h m) n).const_mul _

/-- Every even power of the Euler–Maruyama value of GBM at a grid time is integrable
(Giles 2015, §5.1). -/
lemma gridMax_integrable_emPath_pow (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n m : ℕ) :
    Integrable (fun z => emPath (gbmDrift r) (gbmVol σ) h s₀ z n ^ (2 * m)) stdNormalSeq := by
  simp_rw [emPath_gbm, mul_pow]
  exact (integrable_prod_range_pow (measurable_gbmEMFactor r σ h)
    (integrable_gbmEMFactor_pow r σ hh m) n).const_mul _

/-- The moments of the exact solution on the grid: `E[S_{t_n}^{2m}] ≤ S_0^{2m} e^{ω t_n}` with
`ω = gbmLpRate m r σ` (Giles 2015, §5.1, GBM example). -/
lemma integral_gbmGridExact_pow_le (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n m : ℕ) :
    ∫ z, gbmGridExact r σ h s₀ z n ^ (2 * m) ∂stdNormalSeq ≤
      s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * (n * h)) := by
  simp_rw [gbmGridExact_eq_prod, mul_pow]
  rw [integral_const_mul, integral_prod_range_pow (measurable_gbmExpFactor r σ h)]
  have h1 := integral_gbmExpFactor_pow_le r σ hh m
  rw [Real.sq_sqrt hh] at h1
  have h0 : 0 ≤ ∫ x, gbmExpFactor r σ h x ^ (2 * m) ∂gaussianReal 0 1 :=
    integral_nonneg fun x => (even_two_mul m).pow_nonneg _
  have hs := (even_two_mul m).pow_nonneg s₀
  calc s₀ ^ (2 * m) * (∫ x, gbmExpFactor r σ h x ^ (2 * m) ∂gaussianReal 0 1) ^ n
      ≤ s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * h) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 n) hs
    _ = _ := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- The `L^{2m}` strong error at a grid time `t_n = nh ≤ T`:
`E[(S_{t_n} − Ŝ_n)^{2m}] ≤ C_m(T) h^m` (`gbm_em_moment_error_le` in the notation `gbmGridExact`;
Giles 2015, §5.1, p. 29, l. 1296–1299). -/
lemma integral_gbmGrid_err_pow_le (r σ s₀ : ℝ) {h T : ℝ} (hh : 0 ≤ h) {n : ℕ} (hnT : n * h ≤ T)
    {m : ℕ} (hm : 0 < m) :
    ∫ z, (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m)
      ∂stdNormalSeq ≤ gbmEMMomentConst m r σ T s₀ * h ^ m :=
  gbm_em_moment_error_le r σ s₀ hh n hnT hm

/-- The `2m`-th power of the strong error at a grid time is integrable (Giles 2015, §5.1). -/
lemma integrable_gbmGrid_err_pow (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n m : ℕ) :
    Integrable (fun z => (gbmGridExact r σ h s₀ z n -
      emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m)) stdNormalSeq :=
  gridMax_integrable_sub_pow (measurable_gbmGridExact r σ h s₀ n).aestronglyMeasurable
    (gridMax_measurable_emPath r σ h s₀ n).aestronglyMeasurable m
    (integrable_gbmGridExact_pow r σ h s₀ n (2 * m)) (gridMax_integrable_emPath_pow r σ s₀ hh n m)

/-- **One exact step of GBM moves by `O(h^{1/2})` in every `L^{2m}`**: for `T ≥ 0` and `m ≥ 1` there
is `G` with `E[(e^{(r − σ²/2)h + σ√h Z} − 1)^{2m}] ≤ G h^m` for all `0 ≤ h ≤ T` (Giles 2015, §5.2,
p. 38, l. 1655–1656: "there is an `O(h^{1/2})` variation in the asset value within each timestep of
size `h`").  Write `A − 1 = (B − 1) − (B − A)` with the Euler–Maruyama step `B = 1 + rh + σ√h Z`:
`E[(B − 1)^{2m}] = O(h^m)` (Gaussian moments) and `E[(B − A)^{2m}] = O(h^{2m})`
(`gbm_em_onestep_le`).  The constant is explicit
(`G = 2^{2m−1}(3^{m−1}((2r²T)^m + (2σ²)^m (2m−1)!!) + e^{ωT} E_{2m}(T) T^m)`) and was checked
against the exact moments `E[(A − 1)^{2m}] = ∑_j C(2m, j) (−1)^{2m−j} E[A^j]` (6750 checks with
`m ≤ 3`, `−1 ≤ r ≤ 2`, `σ ≤ 1.5`, `T ≤ 3`, `h = T 2^{−k}`, `k < 25`: ratio at most `0.26`). -/
lemma gbmGrid_expFactor_sub_one_moment (r σ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ h : ℝ, 0 ≤ h → h ≤ T →
      ∫ x, (gbmExpFactor r σ h x - 1) ^ (2 * m) ∂gaussianReal 0 1 ≤ G * h ^ m := by
  have hE : 0 ≤ gbmEMStepConst m r σ T (2 * m) := by
    unfold gbmEMStepConst
    positivity
  refine ⟨2 ^ (2 * m - 1) * (3 ^ (m - 1) * ((2 * r ^ 2 * T) ^ m + (2 * σ ^ 2) ^ m *
    Nat.doubleFactorial (2 * m - 1)) + Real.exp (gbmLpRate m r σ * T) *
      gbmEMStepConst m r σ T (2 * m) * T ^ m), by positivity, fun h hh hhT => ?_⟩
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  -- the Euler–Maruyama step minus one
  obtain ⟨hB1i, hB1⟩ := integral_pow_le_of_le_quartic
    (f := fun x => (gbmEMFactor r σ h x - 1) ^ 2) ((measurable_gbmEMFactor r σ h).sub_const 1
      |>.pow_const 2) (P₀ := 2 * (r * h) ^ 2) (P₁ := 2 * (σ ^ 2 * h)) (P₂ := 0)
    (by positivity) (by positivity) le_rfl (fun x => sq_nonneg _) (fun x => by
      unfold gbmEMFactor
      nlinarith [sq_nonneg (r * h - σ * Real.sqrt h * x), hs]) m
  simp only [← pow_mul] at hB1i hB1
  rw [zero_pow hm.ne', zero_mul, add_zero] at hB1
  have hB1' : ∫ x, (gbmEMFactor r σ h x - 1) ^ (2 * m) ∂gaussianReal 0 1 ≤
      3 ^ (m - 1) * ((2 * r ^ 2 * T) ^ m + (2 * σ ^ 2) ^ m *
        Nat.doubleFactorial (2 * m - 1)) * h ^ m := by
    refine hB1.trans ?_
    have e1 : (2 * (r * h) ^ 2) ^ m = (2 * r ^ 2 * h) ^ m * h ^ m := by
      rw [← mul_pow]
      ring
    have e2 : (2 * (σ ^ 2 * h)) ^ m = (2 * σ ^ 2) ^ m * h ^ m := by
      rw [← mul_pow]
      ring
    have e3 : (2 * r ^ 2 * h) ^ m ≤ (2 * r ^ 2 * T) ^ m :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg r]) m
    rw [e1, e2]
    have : (0 : ℝ) ≤ 3 ^ (m - 1) := by positivity
    have hhm : 0 ≤ h ^ m := pow_nonneg hh m
    nlinarith [mul_le_mul_of_nonneg_right e3 hhm, mul_nonneg this hhm]
  -- the Euler–Maruyama step minus the exact step
  have hBA := gbm_em_onestep_le r σ hh hhT (m := m) (k := 2 * m) (by omega) le_rfl
  simp only [Nat.sub_self, pow_zero, mul_one] at hBA
  have hBAi : Integrable (fun x => (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ (2 * m))
      (gaussianReal 0 1) :=
    gridMax_integrable_sub_pow (measurable_gbmEMFactor r σ h).aestronglyMeasurable
      (measurable_gbmExpFactor r σ h).aestronglyMeasurable m (integrable_gbmEMFactor_pow r σ hh m)
      (integrable_gbmExpFactor_pow r σ h (2 * m))
  have hBA' : ∫ x, (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ (2 * m) ∂gaussianReal 0 1 ≤
      Real.exp (gbmLpRate m r σ * T) * gbmEMStepConst m r σ T (2 * m) * T ^ m * h ^ m := by
    refine (le_abs_self _).trans (hBA.trans ?_)
    have hω := gbmLpRate_nonneg m r σ
    have e1 : Real.exp (gbmLpRate m r σ * h) ≤ Real.exp (gbmLpRate m r σ * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhT hω)
    have e2 : h ^ (2 * m) ≤ T ^ m * h ^ m := by
      rw [two_mul, pow_add]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh hhT m) (pow_nonneg hh m)
    have hh2 : 0 ≤ h ^ (2 * m) := pow_nonneg hh _
    calc Real.exp (gbmLpRate m r σ * h) * gbmEMStepConst m r σ T (2 * m) * h ^ (2 * m)
        ≤ Real.exp (gbmLpRate m r σ * T) * gbmEMStepConst m r σ T (2 * m) * h ^ (2 * m) := by
          gcongr
      _ ≤ Real.exp (gbmLpRate m r σ * T) * gbmEMStepConst m r σ T (2 * m) * (T ^ m * h ^ m) := by
          gcongr
      _ = _ := by ring
  have hpt : ∀ x, (gbmExpFactor r σ h x - 1) ^ (2 * m) ≤ 2 ^ (2 * m - 1) *
      ((gbmEMFactor r σ h x - 1) ^ (2 * m) +
        (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ (2 * m)) := fun x => by
    have := gridMax_sub_pow_two_mul_le (gbmEMFactor r σ h x - 1)
      (gbmEMFactor r σ h x - gbmExpFactor r σ h x) m
    rwa [show gbmEMFactor r σ h x - 1 - (gbmEMFactor r σ h x - gbmExpFactor r σ h x) =
      gbmExpFactor r σ h x - 1 by ring] at this
  calc ∫ x, (gbmExpFactor r σ h x - 1) ^ (2 * m) ∂gaussianReal 0 1
      ≤ ∫ x, 2 ^ (2 * m - 1) * ((gbmEMFactor r σ h x - 1) ^ (2 * m) +
          (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ (2 * m)) ∂gaussianReal 0 1 :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => (even_two_mul m).pow_nonneg _)
          ((hB1i.add hBAi).const_mul _) (Eventually.of_forall hpt)
    _ = 2 ^ (2 * m - 1) * (∫ x, (gbmEMFactor r σ h x - 1) ^ (2 * m) ∂gaussianReal 0 1 +
          ∫ x, (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ (2 * m) ∂gaussianReal 0 1) := by
        rw [integral_const_mul, integral_add hB1i hBAi]
    _ ≤ _ := by
        have : (0 : ℝ) ≤ 2 ^ (2 * m - 1) := by positivity
        nlinarith [add_le_add hB1' hBA']

/-- From `((N + 1) K h^m)^{1/m}` to `C h^{1−δ}`: if `a h ≤ c`, `0 ≤ h ≤ T` and `1/m ≤ δ`, then
`(a K h^m)^{1/m} ≤ (cK)^{1/m} T^{δ − 1/m} h^{1−δ}` (the loss `δ` in the exponents of the maximum
bounds, Giles 2015, §5.1–§5.2). -/
lemma gridMax_rpow_rate_le {a h T K c δ : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (hhT : h ≤ T) (hK : 0 ≤ K)
    (hc : a * h ≤ c) {m : ℕ} (hm : 0 < m) (hδ : (m : ℝ)⁻¹ ≤ δ) :
    (a * K * h ^ m) ^ ((m : ℝ)⁻¹) ≤ (c * K) ^ ((m : ℝ)⁻¹) * T ^ (δ - (m : ℝ)⁻¹) * h ^ (1 - δ) := by
  have hm0 : (m : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hm.ne')
  rcases hh.eq_or_lt with rfl | hpos
  · rw [zero_pow hm.ne', mul_zero, Real.zero_rpow hm0]
    have hc0 : 0 ≤ c := by simpa using hc
    have : 0 ≤ (c * K) ^ ((m : ℝ)⁻¹) := Real.rpow_nonneg (mul_nonneg hc0 hK) _
    have : 0 ≤ T ^ (δ - (m : ℝ)⁻¹) := Real.rpow_nonneg hhT _
    have : 0 ≤ (0 : ℝ) ^ (1 - δ) := Real.rpow_nonneg le_rfl _
    positivity
  have hc0 : 0 ≤ c := (mul_nonneg ha hpos.le).trans hc
  have hm1 : 1 ≤ m := hm
  have e1 : a * K * h ^ m = a * h * K * h ^ (m - 1) := by
    have : h ^ m = h * h ^ (m - 1) := by rw [← pow_succ', Nat.sub_add_cancel hm1]
    rw [this]
    ring
  have h1 : a * K * h ^ m ≤ c * K * h ^ (m - 1) := by
    rw [e1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hK) (pow_nonneg hpos.le _)
  have h2 : (h ^ (m - 1)) ^ ((m : ℝ)⁻¹) = h ^ (1 - δ) * h ^ (δ - (m : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos,
      Nat.cast_sub hm1]
    congr 1
    field_simp
    ring
  have h3 : h ^ (δ - (m : ℝ)⁻¹) ≤ T ^ (δ - (m : ℝ)⁻¹) :=
    Real.rpow_le_rpow hpos.le hhT (sub_nonneg.2 hδ)
  calc (a * K * h ^ m) ^ ((m : ℝ)⁻¹) ≤ (c * K * h ^ (m - 1)) ^ ((m : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = (c * K) ^ ((m : ℝ)⁻¹) * (h ^ (1 - δ) * h ^ (δ - (m : ℝ)⁻¹)) := by
        rw [Real.mul_rpow (mul_nonneg hc0 hK) (pow_nonneg hpos.le _), h2]
    _ ≤ (c * K) ^ ((m : ℝ)⁻¹) * (h ^ (1 - δ) * T ^ (δ - (m : ℝ)⁻¹)) := by
        gcongr
    _ = _ := by ring

/-- For every `δ > 0` there is `m ≥ 1` with `1/m ≤ δ` (the moment order used for the rate
`h^{1−δ}`, Giles 2015, §5.1–§5.2). -/
lemma gridMax_exists_nat_inv_le {δ : ℝ} (hδ : 0 < δ) : ∃ m : ℕ, 0 < m ∧ (m : ℝ)⁻¹ ≤ δ := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, n.succ_pos, ?_⟩
  push_cast
  rw [inv_eq_one_div]
  exact hn.le

/-- **The maximum over `M + 1` grid times from `L^{2m}` bounds**: if `E[X_n^{2m}] ≤ D h^m` for
`n ≤ M`, `(M + 1) h ≤ 2T`, `0 ≤ h ≤ T` and `1/m ≤ δ`, then `max_{n≤M} X_n²` is integrable and
`E[max_{n≤M} X_n²] ≤ (2TD)^{1/m} T^{δ−1/m} h^{1−δ}` (`gridMax_integral_sup'_sq_le`; Giles 2015,
§5.1–§5.2). -/
lemma gridMax_integral_sup'_sq_rate {X : ℕ → (ℕ → ℝ) → ℝ} (hXm : ∀ n, Measurable (X n)) {M : ℕ}
    {h T D δ : ℝ} {m : ℕ} (hm : 0 < m) (hδ : (m : ℝ)⁻¹ ≤ δ) (hh : 0 ≤ h) (hhT : h ≤ T)
    (hMh : (M + 1) * h ≤ 2 * T) (hD : 0 ≤ D)
    (hX : ∀ n ≤ M, Integrable (fun z => X n z ^ (2 * m)) stdNormalSeq ∧
      ∫ z, X n z ^ (2 * m) ∂stdNormalSeq ≤ D * h ^ m) :
    Integrable (fun z => (range (M + 1)).sup' nonempty_range_add_one (fun n => X n z ^ 2))
      stdNormalSeq ∧
    ∫ z, (range (M + 1)).sup' nonempty_range_add_one (fun n => X n z ^ 2) ∂stdNormalSeq ≤
      (2 * T * D) ^ ((m : ℝ)⁻¹) * T ^ (δ - (m : ℝ)⁻¹) * h ^ (1 - δ) := by
  have hmem : ∀ n ∈ range (M + 1), n ≤ M := fun n hn => Nat.lt_succ_iff.1 (mem_range.1 hn)
  obtain ⟨hI, hle⟩ := gridMax_integral_sup'_sq_le nonempty_range_add_one hXm hm
    (fun n hn => (hX n (hmem n hn)).1)
  refine ⟨hI, hle.trans ?_⟩
  have hsum : ∑ n ∈ range (M + 1), ∫ z, X n z ^ (2 * m) ∂stdNormalSeq ≤ (M + 1) * D * h ^ m := by
    calc ∑ n ∈ range (M + 1), ∫ z, X n z ^ (2 * m) ∂stdNormalSeq
        ≤ ∑ _n ∈ range (M + 1), D * h ^ m :=
          Finset.sum_le_sum fun n hn => (hX n (hmem n hn)).2
      _ = (M + 1) * D * h ^ m := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have h0 : 0 ≤ ∑ n ∈ range (M + 1), ∫ z, X n z ^ (2 * m) ∂stdNormalSeq :=
    Finset.sum_nonneg fun n _ => integral_nonneg fun z => (even_two_mul m).pow_nonneg _
  exact (Real.rpow_le_rpow h0 hsum (by positivity)).trans
    (gridMax_rpow_rate_le (by positivity) hh hhT hD hMh hm hδ)

/-- **The strong error of Euler–Maruyama for GBM uniformly over the time grid, from the
`L^{2m}` bounds** (Giles 2015, §5.1, p. 29, l. 1296–1301: "the strong error for the Euler
discretisation with timestep `h` is `O(h^{1/2})`, so that `E[‖S − Ŝ‖²] = O(h)`", for the norm of
the whole discrete path, which the lookback options of Table 5.2, p. 33, need).  For GBM, a step
`h ≥ 0`, `N` steps with `Nh ≤ T` and `m ≥ 1`, the exact solution `S_{t_n}` and the Euler–Maruyama
path `Ŝ_n` driven by the same increments satisfy: `max_{n≤N} (S_{t_n} − Ŝ_n)²` is integrable and
`E[max_{n≤N} (S_{t_n} − Ŝ_n)²] ≤ ((N + 1) C_m(T) h^m)^{1/m}` with the explicit constant
`C_m(T) = gbmEMMomentConst m r σ T S_0` of `gbm_em_moment_error`
(`E[max_n e_n²] ≤ (∑_n E[e_n^{2m}])^{1/m}`).  With `N h = T` this is `O(h^{1−1/m})` for every `m`;
`gbm_em_grid_max_error_sharp` removes the loss. -/
theorem gbm_em_grid_max_error (r σ s₀ : ℝ) {h T : ℝ} (hh : 0 ≤ h) {N : ℕ} (hNT : N * h ≤ T)
    {m : ℕ} (hm : 0 < m) :
    Integrable (fun z => (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2))
      stdNormalSeq ∧
    ∫ z, (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2) ∂stdNormalSeq ≤
      ((N + 1) * gbmEMMomentConst m r σ T s₀ * h ^ m) ^ ((m : ℝ)⁻¹) := by
  have hnT : ∀ n ∈ range (N + 1), n * h ≤ T := fun n hn =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.lt_succ_iff.1 (mem_range.1 hn))) hh).trans hNT
  obtain ⟨hI, hle⟩ := gridMax_integral_sup'_sq_le nonempty_range_add_one
    (X := fun n z => gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n)
    (fun n => (measurable_gbmGridExact r σ h s₀ n).sub (gridMax_measurable_emPath r σ h s₀ n)) hm
    (fun n _ => integrable_gbmGrid_err_pow r σ s₀ hh n m)
  refine ⟨hI, hle.trans (Real.rpow_le_rpow (Finset.sum_nonneg fun n _ =>
    integral_nonneg fun z => (even_two_mul m).pow_nonneg _) ?_ (by positivity))⟩
  calc ∑ n ∈ range (N + 1), ∫ z, (gbmGridExact r σ h s₀ z n -
        emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m) ∂stdNormalSeq
      ≤ ∑ _n ∈ range (N + 1), gbmEMMomentConst m r σ T s₀ * h ^ m :=
        Finset.sum_le_sum fun n hn => integral_gbmGrid_err_pow_le r σ s₀ hh (hnT n hn) hm
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- The uniform strong error at rate `h^{1−δ}`, with integrability: for every `δ > 0` there is `C`
with `E[max_{n≤N} (S_{t_n} − Ŝ_n)²] ≤ C h^{1−δ}` for `0 ≤ h ≤ T`, `Nh ≤ T` (Giles 2015, §5.1,
p. 29, l. 1296–1301; from `gbm_em_grid_max_error`). -/
lemma gbmGrid_err_sup'_rate (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ) (N : ℕ), 0 ≤ h → h ≤ T → N * h ≤ T →
      Integrable (fun z => (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2))
          stdNormalSeq ∧
      ∫ z, (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2)
          ∂stdNormalSeq ≤ C * h ^ (1 - δ) := by
  obtain ⟨m, hm, hmδ⟩ := gridMax_exists_nat_inv_le hδ
  have hC := gbmEMMomentConst_nonneg m r σ s₀ hT
  refine ⟨(2 * T * gbmEMMomentConst m r σ T s₀) ^ ((m : ℝ)⁻¹) * T ^ (δ - (m : ℝ)⁻¹),
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hT _),
    fun h N hh hhT hNT => ?_⟩
  have hnT : ∀ n ≤ N, n * h ≤ T := fun n hn =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hn) hh).trans hNT
  have hMh : ((N : ℝ) + 1) * h ≤ 2 * T := by nlinarith
  exact gridMax_integral_sup'_sq_rate
    (X := fun n z => gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n)
    (fun n => (measurable_gbmGridExact r σ h s₀ n).sub (gridMax_measurable_emPath r σ h s₀ n))
    hm hmδ
    hh hhT hMh hC (fun n hn => ⟨integrable_gbmGrid_err_pow r σ s₀ hh n m,
      integral_gbmGrid_err_pow_le r σ s₀ hh (hnT n hn) hm⟩)

/-! ### Doob's maximal inequality in `L²` for products of independent factors

Mathlib has Doob's maximal inequality only in its weak form (`MeasureTheory.maximal_ineq`).  The
`L²` form used here is derived from the pathwise inequality of Acciaio, Beiglböck, Penkner,
Schachermayer and Temme (2013), `(max_{n≤N} x_n)² ≤ 4 x_N² − 4 ∑_{n<N} (max_{k≤n} x_k)(x_{n+1} −
x_n)` for every real sequence, whose martingale term has mean zero for the martingales met here
(differences of products of independent mean-one factors), with no filtration or stopping time. -/

/-- `(p + q)² ≤ 2p² + 2q²` (used for the splitting of the Euler–Maruyama error of GBM into a
martingale and a drift part, Giles 2015, §5.1). -/
lemma gridMax_add_sq_le (p q : ℝ) : (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
  nlinarith [sq_nonneg (p - q)]

/-- The running maximum: `max_{k≤n+1} x_k = max(max_{k≤n} x_k, x_{n+1})` (for the pathwise
Doob inequality, Giles 2015, §5.1). -/
lemma gridMax_sup'_range_succ (x : ℕ → ℝ) (n : ℕ) :
    (range (n + 2)).sup' nonempty_range_add_one x =
      max ((range (n + 1)).sup' nonempty_range_add_one x) (x (n + 1)) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun k hk => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 (mem_range.1 hk) with h | h
    · exact le_max_of_le_left (Finset.le_sup' x (mem_range.2 h))
    · rw [h]
      exact le_max_right _ _
  · refine max_le (Finset.sup'_le _ _ fun k hk => ?_) ?_
    · exact Finset.le_sup' x (mem_range.2 (by have := mem_range.1 hk; omega))
    · exact Finset.le_sup' x (mem_range.2 (by omega))

/-- The potential of the pathwise Doob inequality: with `M_n = max_{k≤n} x_k`,
`M_N x_N − M_N²/2 − x_0²/2 − ∑_{n<N} M_n (x_{n+1} − x_n) ≥ 0` for every real sequence (it is `0` at
`N = 0` and nondecreasing in `N`; Acciaio et al. 2013; for Giles 2015, §5.1). -/
lemma gridMax_doob_potential_nonneg (x : ℕ → ℝ) (N : ℕ) :
    0 ≤ (range (N + 1)).sup' nonempty_range_add_one x * x N -
      ((range (N + 1)).sup' nonempty_range_add_one x) ^ 2 / 2 - x 0 ^ 2 / 2 -
      ∑ n ∈ range N, (range (n + 1)).sup' nonempty_range_add_one x * (x (n + 1) - x n) := by
  induction N with
  | zero =>
    simp only [zero_add, range_one, sup'_singleton, range_zero, sum_empty]
    nlinarith
  | succ N ih =>
    rw [sum_range_succ, gridMax_sup'_range_succ]
    set M := (range (N + 1)).sup' nonempty_range_add_one x
    rcases le_total M (x (N + 1)) with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg (x (N + 1) - M)]
    · rw [max_eq_left h]
      nlinarith

/-- **The pathwise Doob inequality in `L²`** (Acciaio, Beiglböck, Penkner, Schachermayer, Temme
2013): for every real sequence, `(max_{n≤N} x_n)² ≤ 4 x_N² − 4 ∑_{n<N} (max_{k≤n} x_k)(x_{n+1} −
x_n)`.  Taking expectations for a martingale gives Doob's `E[(max_n x_n)²] ≤ 4 E[x_N²]` (used for
the sharp uniform strong error of Giles 2015, §5.1, p. 29). -/
lemma gridMax_pathwise_doob (x : ℕ → ℝ) (N : ℕ) :
    ((range (N + 1)).sup' nonempty_range_add_one x) ^ 2 ≤
      4 * x N ^ 2 -
        4 * ∑ n ∈ range N, (range (n + 1)).sup' nonempty_range_add_one x * (x (n + 1) - x n) := by
  have h := gridMax_doob_potential_nonneg x N
  nlinarith [sq_nonneg ((range (N + 1)).sup' nonempty_range_add_one x / 2 - x N),
    sq_nonneg (x 0)]

/-- `max_n x_n² ≤ (max_n x_n)² + (max_n (−x_n))²` (the two-sided maximum from the one-sided
ones; Giles 2015, §5.1). -/
lemma gridMax_sup'_sq_le_add (x : ℕ → ℝ) (N : ℕ) :
    (range (N + 1)).sup' nonempty_range_add_one (fun n => x n ^ 2) ≤
      ((range (N + 1)).sup' nonempty_range_add_one x) ^ 2 +
        ((range (N + 1)).sup' nonempty_range_add_one (fun n => -x n)) ^ 2 := by
  refine Finset.sup'_le _ _ fun n hn => ?_
  have h1 : x n ≤ (range (N + 1)).sup' nonempty_range_add_one x := Finset.le_sup' x hn
  have h2 : -x n ≤ (range (N + 1)).sup' nonempty_range_add_one (fun n => -x n) :=
    Finset.le_sup' (fun n => -x n) hn
  rcases le_total 0 (x n) with h | h
  · nlinarith [sq_nonneg ((range (N + 1)).sup' nonempty_range_add_one (fun n => -x n))]
  · nlinarith [sq_nonneg ((range (N + 1)).sup' nonempty_range_add_one x)]

/-- `(max_{n≤N} x_n)² ≤ ∑_{n≤N} x_n²` (integrability of the running maximum; Giles 2015,
§5.1). -/
lemma gridMax_sq_sup'_le_sum (x : ℕ → ℝ) (N : ℕ) :
    ((range (N + 1)).sup' nonempty_range_add_one x) ^ 2 ≤ ∑ n ∈ range (N + 1), x n ^ 2 := by
  obtain ⟨k, hk, hke⟩ := Finset.exists_mem_eq_sup' (nonempty_range_add_one (n := N)) x
  rw [hke]
  exact Finset.single_le_sum (f := fun n => x n ^ 2) (fun n _ => sq_nonneg _) hk

/-- **Doob's inequality for a difference of product martingales, one-sided**: if `F(Z)`, `G(Z)`
are square integrable with `E[F(Z)] = E[G(Z)] = 1`, `Z ∼ N(0,1)`, then
`x_n = p ∏_{i<n} F(Z_i) − q ∏_{i<n} G(Z_i)` satisfies `E[(max_{n≤N} x_n)²] ≤ 4 E[x_N²]`: integrate
`gridMax_pathwise_doob`; the term `E[M_n (x_{n+1} − x_n)]` vanishes since `M_n p ∏_{i<n} F(Z_i)`
depends on `Z_0, …, Z_{n−1}` only and `E[F(Z_n) − 1] = 0` (`integral_mul_comp_eval_of_eq_lt`; for
Giles 2015, §5.1). -/
lemma gridMax_doob_one_sided {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hF2 : Integrable (fun x => F x ^ 2) (gaussianReal 0 1))
    (hG2 : Integrable (fun x => G x ^ 2) (gaussianReal 0 1))
    (hF1 : ∫ x, F x ∂gaussianReal 0 1 = 1) (hG1 : ∫ x, G x ∂gaussianReal 0 1 = 1)
    (p q : ℝ) (N : ℕ) :
    Integrable (fun z => ((range (N + 1)).sup' nonempty_range_add_one (fun n =>
      p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i))) ^ 2) stdNormalSeq ∧
    ∫ z, ((range (N + 1)).sup' nonempty_range_add_one (fun n =>
      p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i))) ^ 2 ∂stdNormalSeq ≤
      4 * ∫ z, (p * ∏ i ∈ range N, F (z i) - q * ∏ i ∈ range N, G (z i)) ^ 2 ∂stdNormalSeq := by
  set X : ℕ → (ℕ → ℝ) → ℝ := fun n z => p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)
    with hXdef
  have hXm : ∀ n, Measurable (X n) := fun n =>
    (measurable_monProd hF p n).sub (measurable_monProd hG q n)
  have hPL : ∀ n, MemLp (fun z => p * ∏ i ∈ range n, F (z i)) 2 stdNormalSeq := fun n =>
    memLp_monProd hF hF2 p n
  have hQL : ∀ n, MemLp (fun z => q * ∏ i ∈ range n, G (z i)) 2 stdNormalSeq := fun n =>
    memLp_monProd hG hG2 q n
  have hXL : ∀ n, MemLp (X n) 2 stdNormalSeq := fun n => (hPL n).sub (hQL n)
  have hX2 : ∀ n, Integrable (fun z => X n z ^ 2) stdNormalSeq := fun n => (hXL n).integrable_sq
  -- the running maximum
  set M : ℕ → (ℕ → ℝ) → ℝ := fun n z => (range (n + 1)).sup' nonempty_range_add_one
    (fun k => X k z) with hMdef
  have hMm : ∀ n, Measurable (M n) := fun n =>
    Finset.measurable_range_sup'' (f := X) fun k _ => hXm k
  have hM2 : ∀ n, Integrable (fun z => M n z ^ 2) stdNormalSeq := fun n =>
    (integrable_finsetSum _ fun k _ => hX2 k).mono' ((hMm n).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact gridMax_sq_sup'_le_sum (fun k => X k z) n)
  have hML : ∀ n, MemLp (M n) 2 stdNormalSeq := fun n =>
    (memLp_two_iff_integrable_sq (hMm n).aestronglyMeasurable).2 (hM2 n)
  have hMdep : ∀ n (z z' : ℕ → ℝ), (∀ i < n, z i = z' i) → M n z = M n z' := fun n z z' h =>
    Finset.sup'_congr _ rfl fun k hk => by
      have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
      have h' : ∀ i < k, z i = z' i := fun i hi => h i (by omega)
      simp only [hXdef]
      rw [prod_range_eq_of_eq_lt F h', prod_range_eq_of_eq_lt G h']
  -- the martingale terms have mean zero
  have hFi : Integrable F (gaussianReal 0 1) :=
    ((memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2 hF2).integrable one_le_two
  have hGi : Integrable G (gaussianReal 0 1) :=
    ((memLp_two_iff_integrable_sq hG.aestronglyMeasurable).2 hG2).integrable one_le_two
  have hF0 : ∫ x, (F x - 1) ∂gaussianReal 0 1 = 0 := by
    rw [integral_sub hFi (integrable_const 1), hF1, integral_const, probReal_univ, one_smul,
      sub_self]
  have hG0 : ∫ x, (G x - 1) ∂gaussianReal 0 1 = 0 := by
    rw [integral_sub hGi (integrable_const 1), hG1, integral_const, probReal_univ, one_smul,
      sub_self]
  have hterm : ∀ n, Integrable (fun z => M n z * (X (n + 1) z - X n z)) stdNormalSeq ∧
      ∫ z, M n z * (X (n + 1) z - X n z) ∂stdNormalSeq = 0 := fun n => by
    have hA1m : Measurable fun z => M n z * (p * ∏ i ∈ range n, F (z i)) :=
      (hMm n).mul (measurable_monProd hF p n)
    have hA2m : Measurable fun z => M n z * (q * ∏ i ∈ range n, G (z i)) :=
      (hMm n).mul (measurable_monProd hG q n)
    have hA1i : Integrable (fun z => M n z * (p * ∏ i ∈ range n, F (z i))) stdNormalSeq :=
      (hML n).integrable_mul (hPL n)
    have hA2i : Integrable (fun z => M n z * (q * ∏ i ∈ range n, G (z i))) stdNormalSeq :=
      (hML n).integrable_mul (hQL n)
    have hA1d : ∀ z z' : ℕ → ℝ, (∀ i < n, z i = z' i) →
        M n z * (p * ∏ i ∈ range n, F (z i)) = M n z' * (p * ∏ i ∈ range n, F (z' i)) :=
      fun z z' h => by rw [hMdep n z z' h, prod_range_eq_of_eq_lt F h]
    have hA2d : ∀ z z' : ℕ → ℝ, (∀ i < n, z i = z' i) →
        M n z * (q * ∏ i ∈ range n, G (z i)) = M n z' * (q * ∏ i ∈ range n, G (z' i)) :=
      fun z z' h => by rw [hMdep n z z' h, prod_range_eq_of_eq_lt G h]
    have e : ∀ z, M n z * (X (n + 1) z - X n z) =
        M n z * (p * ∏ i ∈ range n, F (z i)) * (F (z n) - 1) -
          M n z * (q * ∏ i ∈ range n, G (z i)) * (G (z n) - 1) := fun z => by
      simp only [hXdef, prod_range_succ]
      ring
    have hB1 := integrable_mul_comp_eval_of_eq_lt hA1m hA1d (hF.sub_const 1) hA1i
      (hFi.sub (integrable_const 1))
    have hB2 := integrable_mul_comp_eval_of_eq_lt hA2m hA2d (hG.sub_const 1) hA2i
      (hGi.sub (integrable_const 1))
    simp only [e]
    refine ⟨hB1.sub hB2, ?_⟩
    rw [integral_sub hB1 hB2, integral_mul_comp_eval_of_eq_lt hA1m hA1d (hF.sub_const 1),
      integral_mul_comp_eval_of_eq_lt hA2m hA2d (hG.sub_const 1), hF0, hG0]
    ring
  -- integrate the pathwise inequality
  have hSi : Integrable (fun z => ∑ n ∈ range N, M n z * (X (n + 1) z - X n z)) stdNormalSeq :=
    integrable_finsetSum _ fun n _ => (hterm n).1
  have hS0 : ∫ z, ∑ n ∈ range N, M n z * (X (n + 1) z - X n z) ∂stdNormalSeq = 0 := by
    rw [integral_finsetSum _ fun n _ => (hterm n).1]
    exact Finset.sum_eq_zero fun n _ => (hterm n).2
  refine ⟨hM2 N, ?_⟩
  calc ∫ z, M N z ^ 2 ∂stdNormalSeq
      ≤ ∫ z, (4 * X N z ^ 2 - 4 * ∑ n ∈ range N, M n z * (X (n + 1) z - X n z))
          ∂stdNormalSeq :=
        integral_mono (hM2 N) (((hX2 N).const_mul 4).sub (hSi.const_mul 4))
          fun z => gridMax_pathwise_doob (fun k => X k z) N
    _ = 4 * ∫ z, X N z ^ 2 ∂stdNormalSeq := by
        rw [integral_sub ((hX2 N).const_mul 4) (hSi.const_mul 4), integral_const_mul,
          integral_const_mul, hS0]
        ring

/-- **Doob's `L²` maximal inequality for a difference of product martingales**: in the setting of
`gridMax_doob_one_sided`, `E[max_{n≤N} x_n²] ≤ 8 E[x_N²]`, and the maximum is integrable (apply the
one-sided bound to `x` and `−x`; for the sharp uniform strong error of Giles 2015, §5.1, p. 29). -/
lemma gridMax_doob_prod_martingale {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hF2 : Integrable (fun x => F x ^ 2) (gaussianReal 0 1))
    (hG2 : Integrable (fun x => G x ^ 2) (gaussianReal 0 1))
    (hF1 : ∫ x, F x ∂gaussianReal 0 1 = 1) (hG1 : ∫ x, G x ∂gaussianReal 0 1 = 1)
    (p q : ℝ) (N : ℕ) :
    Integrable (fun z => (range (N + 1)).sup' nonempty_range_add_one (fun n =>
      (p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)) ^ 2)) stdNormalSeq ∧
    ∫ z, (range (N + 1)).sup' nonempty_range_add_one (fun n =>
      (p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)) ^ 2) ∂stdNormalSeq ≤
      8 * ∫ z, (p * ∏ i ∈ range N, F (z i) - q * ∏ i ∈ range N, G (z i)) ^ 2 ∂stdNormalSeq := by
  obtain ⟨h1i, h1⟩ := gridMax_doob_one_sided hF hG hF2 hG2 hF1 hG1 p q N
  obtain ⟨h2i, h2⟩ := gridMax_doob_one_sided hF hG hF2 hG2 hF1 hG1 (-p) (-q) N
  have e : ∀ (z : ℕ → ℝ) (n : ℕ), -p * ∏ i ∈ range n, F (z i) - -q * ∏ i ∈ range n, G (z i) =
      -(p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)) := fun z n => by ring
  simp only [e, neg_sq] at h2i h2
  have hm : Measurable fun (z : ℕ → ℝ) => (range (N + 1)).sup' nonempty_range_add_one (fun n =>
      (p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)) ^ 2) :=
    Finset.measurable_range_sup'' (f := fun (n : ℕ) (z : ℕ → ℝ) =>
      (p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)) ^ 2) fun k _ =>
      ((measurable_monProd hF p k).sub (measurable_monProd hG q k)).pow_const 2
  have hint := h1i.add h2i
  have hpt : ∀ z : ℕ → ℝ, (range (N + 1)).sup' nonempty_range_add_one (fun n =>
      (p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)) ^ 2) ≤
      ((range (N + 1)).sup' nonempty_range_add_one (fun n =>
        p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i))) ^ 2 +
      ((range (N + 1)).sup' nonempty_range_add_one (fun n =>
        -(p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)))) ^ 2 := fun z =>
    gridMax_sup'_sq_le_add (fun n => p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)) N
  have hnn : ∀ z : ℕ → ℝ, 0 ≤ (range (N + 1)).sup' nonempty_range_add_one (fun n =>
      (p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)) ^ 2) := fun z =>
    (sq_nonneg _).trans (Finset.le_sup' (fun n =>
      (p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)) ^ 2) (self_mem_range_succ N))
  refine ⟨hint.mono' hm.aestronglyMeasurable (Eventually.of_forall fun z => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (hnn z)]
    exact hpt z
  · calc _ ≤ ∫ z, (((range (N + 1)).sup' nonempty_range_add_one (fun n =>
          p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i))) ^ 2 +
          ((range (N + 1)).sup' nonempty_range_add_one (fun n =>
            -(p * ∏ i ∈ range n, F (z i) - q * ∏ i ∈ range n, G (z i)))) ^ 2) ∂stdNormalSeq :=
          integral_mono_of_nonneg (Eventually.of_forall hnn) hint (Eventually.of_forall hpt)
      _ = _ := integral_add h1i h2i
      _ ≤ _ := by linarith

/-- `E[e^{(r − σ²/2)h + σ√h Z}] = e^{rh}` (the mean of an exact GBM step; Giles 2015, §5.1). -/
lemma gbmGrid_integral_expFactor (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ x, gbmExpFactor r σ h x ∂gaussianReal 0 1 = Real.exp (r * h) := by
  have h1 := integral_gbmExpFactor_pow r σ h 1
  simp only [pow_one, Nat.cast_one, one_mul] at h1
  rw [h1, mul_pow, Real.sq_sqrt hh]
  congr 1
  ring

/-- `E[1 + rh + σ√h Z] = 1 + rh` (the mean of an Euler–Maruyama step of GBM; Giles 2015,
§5.1). -/
lemma gbmGrid_integral_emFactor (r σ h : ℝ) :
    ∫ x, gbmEMFactor r σ h x ∂gaussianReal 0 1 = 1 + r * h := by
  unfold gbmEMFactor
  rw [integral_add (integrable_const _) (integrable_id_gaussian.const_mul _), integral_const,
    probReal_univ, one_smul, integral_const_mul, integral_id_gaussianReal, mul_zero, add_zero]

/-- The moments of the Euler–Maruyama path of GBM: `E[Ŝ_n^{2m}] ≤ S_0^{2m} e^{ω nh}` with
`ω = gbmLpRate m r σ` (`integral_gbmEMFactor_pow_le`; Giles 2015, §5.1). -/
lemma gbmGrid_integral_emPath_pow_le (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n m : ℕ) :
    ∫ z, emPath (gbmDrift r) (gbmVol σ) h s₀ z n ^ (2 * m) ∂stdNormalSeq ≤
      s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * (n * h)) := by
  simp_rw [emPath_gbm, mul_pow]
  rw [integral_const_mul, integral_prod_range_pow (measurable_gbmEMFactor r σ h)]
  have h1 := integral_gbmEMFactor_pow_le r σ hh m
  have h0 : 0 ≤ ∫ x, gbmEMFactor r σ h x ^ (2 * m) ∂gaussianReal 0 1 :=
    integral_nonneg fun x => (even_two_mul m).pow_nonneg _
  have hs := (even_two_mul m).pow_nonneg s₀
  calc s₀ ^ (2 * m) * (∫ x, gbmEMFactor r σ h x ^ (2 * m) ∂gaussianReal 0 1) ^ n
      ≤ s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * h) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 n) hs
    _ = _ := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- Bounds on the mean factors `a = e^{rh}` and `b = 1 + rh` of the exact and the Euler–Maruyama
steps for `|r| h ≤ 1/2` and `nh ≤ T`: `a^n, a^{−n} ≤ e^{|r|T}`, `b^n > 0`, `b^{−n} ≤ e^{2|r|T}` and
`|a^n − b^n| ≤ r² T e^{2|r|T} h` (the drift part of the Euler–Maruyama error is `O(h)` uniformly on
the grid; Giles 2015, §5.1). -/
lemma gbmGrid_drift_factor_bounds (r : ℝ) {h T : ℝ} (hh : 0 ≤ h) (hr : |r| * h ≤ 1 / 2) {n : ℕ}
    (hnT : n * h ≤ T) :
    Real.exp (r * h) ^ n ≤ Real.exp (|r| * T) ∧ (Real.exp (r * h) ^ n)⁻¹ ≤ Real.exp (|r| * T) ∧
    0 < (1 + r * h) ^ n ∧ ((1 + r * h) ^ n)⁻¹ ≤ Real.exp (2 * |r| * T) ∧
    |Real.exp (r * h) ^ n - (1 + r * h) ^ n| ≤ r ^ 2 * T * Real.exp (2 * |r| * T) * h := by
  have hrh : |r * h| = |r| * h := by rw [abs_mul, abs_of_nonneg hh]
  have hrT : |r| * (n * h) ≤ |r| * T := mul_le_mul_of_nonneg_left hnT (abs_nonneg r)
  have hnh : 0 ≤ (n : ℝ) * h := by positivity
  have hT : 0 ≤ T := hnh.trans hnT
  have e1 : Real.exp (r * h) ^ n = Real.exp (r * (n * h)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hle1 : r * (n * h) ≤ |r| * T := (le_abs_self _).trans (by
    rw [abs_mul, abs_of_nonneg hnh]
    exact hrT)
  have hle2 : -(r * (n * h)) ≤ |r| * T := (neg_le_abs _).trans (by
    rw [abs_mul, abs_of_nonneg hnh]
    exact hrT)
  have hb0 : 1 / 2 ≤ 1 + r * h := by
    have := neg_abs_le (r * h)
    rw [hrh] at this
    linarith
  have hbexp : Real.exp (-(2 * (|r| * h))) ≤ 1 + r * h := by
    have h1 : 1 + 2 * (|r| * h) ≤ Real.exp (2 * (|r| * h)) := by
      linarith [Real.add_one_le_exp (2 * (|r| * h))]
    have h2 : Real.exp (-(2 * (|r| * h))) * Real.exp (2 * (|r| * h)) = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 : 0 ≤ |r| * h := by positivity
    have h4 := neg_abs_le (r * h)
    rw [hrh] at h4
    have h5 : (1 - |r| * h) * (1 + 2 * (|r| * h)) ≥ 1 := by nlinarith
    have hE : 0 < Real.exp (2 * (|r| * h)) := Real.exp_pos _
    nlinarith [Real.exp_pos (-(2 * (|r| * h)))]
  refine ⟨?_, ?_, pow_pos (by linarith) n, ?_, ?_⟩
  · rw [e1]
    exact Real.exp_le_exp.2 hle1
  · rw [e1, ← Real.exp_neg]
    exact Real.exp_le_exp.2 hle2
  · have hbn : Real.exp (-(2 * (|r| * h))) ^ n ≤ (1 + r * h) ^ n :=
      pow_le_pow_left₀ (Real.exp_pos _).le hbexp n
    have e2 : Real.exp (-(2 * (|r| * h))) ^ n = Real.exp (-(2 * |r| * (n * h))) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [e2] at hbn
    have hpos : 0 < Real.exp (-(2 * |r| * (n * h))) := Real.exp_pos _
    calc ((1 + r * h) ^ n)⁻¹ ≤ (Real.exp (-(2 * |r| * (n * h))))⁻¹ := inv_anti₀ hpos hbn
      _ = Real.exp (2 * |r| * (n * h)) := by rw [← Real.exp_neg, neg_neg]
      _ ≤ Real.exp (2 * |r| * T) := Real.exp_le_exp.2 (by nlinarith [abs_nonneg r])
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [pow_zero, sub_self, abs_zero]
      have := Real.exp_pos (2 * |r| * T)
      positivity
    have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
    have hhT : h ≤ T := le_trans (le_mul_of_one_le_left hh hn1) hnT
    have hab := abs_pow_sub_pow_le (a := Real.exp (r * h)) (b := 1 + r * h) (n := n)
    obtain ⟨d0, d1⟩ := exp_sub_one_sub_le_sq_mul_max (r * h)
    have hmax1 : max 1 (Real.exp (r * h)) ≤ Real.exp (|r| * h) := max_le
      (Real.one_le_exp (by positivity)) (Real.exp_le_exp.2 (by rw [← hrh]; exact le_abs_self _))
    have hd : |Real.exp (r * h) - (1 + r * h)| ≤ r ^ 2 * h ^ 2 * Real.exp (|r| * h) := by
      rw [abs_of_nonneg (by linarith)]
      calc Real.exp (r * h) - (1 + r * h) = Real.exp (r * h) - 1 - r * h := by ring
        _ ≤ (r * h) ^ 2 * max 1 (Real.exp (r * h)) := d1
        _ ≤ (r * h) ^ 2 * Real.exp (|r| * h) :=
            mul_le_mul_of_nonneg_left hmax1 (sq_nonneg _)
        _ = _ := by ring
    have hmax2 : max |Real.exp (r * h)| |1 + r * h| ≤ Real.exp (|r| * h) := by
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (by linarith)]
      refine max_le (Real.exp_le_exp.2 (by rw [← hrh]; exact le_abs_self _)) ?_
      calc 1 + r * h ≤ Real.exp (r * h) := by linarith [Real.add_one_le_exp (r * h)]
        _ ≤ _ := Real.exp_le_exp.2 (by rw [← hrh]; exact le_abs_self _)
    have hE1 : 1 ≤ Real.exp (|r| * h) := Real.one_le_exp (by positivity)
    have hpow : max |Real.exp (r * h)| |1 + r * h| ^ (n - 1) ≤ Real.exp (|r| * T) := by
      calc max |Real.exp (r * h)| |1 + r * h| ^ (n - 1) ≤ Real.exp (|r| * h) ^ (n - 1) :=
            pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax2 _
        _ ≤ Real.exp (|r| * h) ^ n := pow_le_pow_right₀ hE1 (Nat.sub_le n 1)
        _ = Real.exp (|r| * (n * h)) := by
            rw [← Real.exp_nat_mul]
            ring_nf
        _ ≤ Real.exp (|r| * T) := Real.exp_le_exp.2 hrT
    have hEh : Real.exp (|r| * h) ≤ Real.exp (|r| * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhT (abs_nonneg r))
    have e3 : Real.exp (2 * |r| * T) = Real.exp (|r| * T) * Real.exp (|r| * T) := by
      rw [← Real.exp_add]
      ring_nf
    calc |Real.exp (r * h) ^ n - (1 + r * h) ^ n|
        ≤ |Real.exp (r * h) - (1 + r * h)| * n * max |Real.exp (r * h)| |1 + r * h| ^ (n - 1) :=
          hab
      _ ≤ r ^ 2 * h ^ 2 * Real.exp (|r| * T) * n * Real.exp (|r| * T) := by
          gcongr
          exact hd.trans (mul_le_mul_of_nonneg_left hEh (by positivity))
      _ = r ^ 2 * (n * h) * Real.exp (2 * |r| * T) * h := by
          rw [e3]
          ring
      _ ≤ r ^ 2 * T * Real.exp (2 * |r| * T) * h := by
          gcongr

/-- The sharp uniform strong error for small steps: there is `K` with
`E[max_{n≤N} (S_{t_n} − Ŝ_n)²] ≤ K h` for `0 ≤ h`, `|r| h ≤ 1/2`, `Nh ≤ T` (Giles 2015, §5.1,
p. 29).  With `a = e^{rh}`, `b = 1 + rh`, `X_n = S_{t_n}/a^n` and `Y_n = Ŝ_n/b^n` are martingales
(products of independent mean-one factors), and
`S_{t_n} − Ŝ_n = a^n (X_n − Y_n) + (a^n − b^n) Y_n`.  Doob's inequality
(`gridMax_doob_prod_martingale`) bounds `E[max_n (X_n − Y_n)²]` by `8 E[(X_N − Y_N)²] = O(h)`
(`gbm_em_moment_error` at the final time) and `E[max_n Y_n²]` by `8 E[Y_N²] = O(1)`, while
`|a^n − b^n| = O(h)` (`gbmGrid_drift_factor_bounds`). -/
lemma gbm_em_grid_max_error_sharp_aux (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℝ) (N : ℕ), 0 ≤ h → |r| * h ≤ 1 / 2 → N * h ≤ T →
      ∫ z, (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2)
          ∂stdNormalSeq ≤ K * h := by
  set E := Real.exp (|r| * T) with hEdef
  set E2 := Real.exp (2 * |r| * T) with hE2def
  set C₁ := gbmEMMomentConst 1 r σ T s₀ with hC₁def
  set W := s₀ ^ 2 * Real.exp (gbmLpRate 1 r σ * T) with hWdef
  set ρ := r ^ 2 * T * E2 with hρdef
  set κ := ρ * E * E2 with hκdef
  have hE : 0 < E := Real.exp_pos _
  have hE2 : 0 < E2 := Real.exp_pos _
  have hC₁ : 0 ≤ C₁ := gbmEMMomentConst_nonneg 1 r σ s₀ hT
  have hW : 0 ≤ W := by positivity
  have hρ : 0 ≤ ρ := by positivity
  refine ⟨32 * E ^ 4 * C₁ + 32 * E ^ 2 * κ ^ 2 * T * W + 16 * ρ ^ 2 * T * E2 ^ 2 * W,
    by positivity, fun h N hh hr hNT => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [zero_add, range_one, sup'_singleton, gbmGridExact_zero]
    simp only [emPath, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
    positivity
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
  have hhT : h ≤ T := le_trans (le_mul_of_one_le_left hh hN1) hNT
  have hnT : ∀ n ≤ N, (n : ℝ) * h ≤ T := fun n hn =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hn) hh).trans hNT
  set a := Real.exp (r * h) with hadef
  set b := 1 + r * h with hbdef
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := by
    have := neg_abs_le (r * h)
    rw [abs_mul, abs_of_nonneg hh] at this
    rw [hbdef]
    linarith
  -- the normalised factors have mean one
  have hFm : Measurable fun x => gbmExpFactor r σ h x / a :=
    (measurable_gbmExpFactor r σ h).div_const a
  have hGm : Measurable fun x => gbmEMFactor r σ h x / b :=
    (measurable_gbmEMFactor r σ h).div_const b
  have hF2 : Integrable (fun x => (gbmExpFactor r σ h x / a) ^ 2) (gaussianReal 0 1) := by
    simp_rw [div_pow]
    exact (integrable_gbmExpFactor_pow r σ h 2).div_const _
  have hG2 : Integrable (fun x => (gbmEMFactor r σ h x / b) ^ 2) (gaussianReal 0 1) := by
    simp_rw [div_pow]
    exact (by simpa using integrable_gbmEMFactor_pow r σ hh 1 :
      Integrable (fun x => gbmEMFactor r σ h x ^ 2) (gaussianReal 0 1)).div_const _
  have hF1 : ∫ x, gbmExpFactor r σ h x / a ∂gaussianReal 0 1 = 1 := by
    rw [integral_div, gbmGrid_integral_expFactor r σ hh, div_self ha0.ne']
  have hG1 : ∫ x, gbmEMFactor r σ h x / b ∂gaussianReal 0 1 = 1 := by
    rw [integral_div, gbmGrid_integral_emFactor, div_self hb0.ne']
  obtain ⟨hI1, hD1⟩ := gridMax_doob_prod_martingale hFm hGm hF2 hG2 hF1 hG1 s₀ s₀ N
  obtain ⟨hI2, hD2⟩ := gridMax_doob_prod_martingale hFm hGm hF2 hG2 hF1 hG1 0 (-s₀) N
  simp only [zero_mul, zero_sub, neg_mul, neg_neg] at hI2 hD2
  -- the exact and the Euler–Maruyama paths in terms of the normalised products
  have hpA : ∀ (z : ℕ → ℝ) (n : ℕ), gbmGridExact r σ h s₀ z n =
      a ^ n * (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) / a) := fun z n => by
    rw [gbmGridExact_eq_prod, prod_div_distrib, prod_const, card_range]
    field_simp
  have hpB : ∀ (z : ℕ → ℝ) (n : ℕ), emPath (gbmDrift r) (gbmVol σ) h s₀ z n =
      b ^ n * (s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) := fun z n => by
    rw [emPath_gbm, prod_div_distrib, prod_const, card_range]
    field_simp
  -- the pointwise bound
  have hpt : ∀ z : ℕ → ℝ, (range (N + 1)).sup' nonempty_range_add_one (fun n =>
      (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2) ≤
      2 * E ^ 2 * (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) / a -
          s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2) +
      2 * (ρ * h) ^ 2 * (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2) := fun z => by
    refine Finset.sup'_le _ _ fun n hn => ?_
    have hn' : n ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hn)
    obtain ⟨hA1, -, -, -, hAB⟩ := gbmGrid_drift_factor_bounds r hh hr (hnT n hn')
    set X := s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) / a
    set Y := s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b
    have hsX : (X - Y) ^ 2 ≤ (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) / a -
          s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2) :=
      Finset.le_sup' (fun n => (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) / a -
          s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2) hn
    have hsY : Y ^ 2 ≤ (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2) :=
      Finset.le_sup' (fun n => (s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2) hn
    rw [hpA, hpB]
    have han : 0 < a ^ n := pow_pos ha0 n
    have h1 : (a ^ n) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ han.le hA1 2
    have h2 : (a ^ n - b ^ n) ^ 2 ≤ (ρ * h) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hAB.trans_eq (by rw [hρdef])) 2
    have e : a ^ n * X - b ^ n * Y = a ^ n * (X - Y) + (a ^ n - b ^ n) * Y := by ring
    rw [e]
    calc (a ^ n * (X - Y) + (a ^ n - b ^ n) * Y) ^ 2
        ≤ 2 * (a ^ n * (X - Y)) ^ 2 + 2 * ((a ^ n - b ^ n) * Y) ^ 2 := gridMax_add_sq_le _ _
      _ = 2 * ((a ^ n) ^ 2 * (X - Y) ^ 2) + 2 * ((a ^ n - b ^ n) ^ 2 * Y ^ 2) := by ring
      _ ≤ 2 * (E ^ 2 * (range (N + 1)).sup' nonempty_range_add_one (fun n =>
          (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) / a -
            s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2)) +
          2 * ((ρ * h) ^ 2 * (range (N + 1)).sup' nonempty_range_add_one (fun n =>
            (s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2)) := by
          gcongr
      _ = _ := by ring
  -- the final value of the martingale difference
  have herr : Integrable (fun z => (gbmGridExact r σ h s₀ z N -
      emPath (gbmDrift r) (gbmVol σ) h s₀ z N) ^ 2) stdNormalSeq := by
    simpa using integrable_gbmGrid_err_pow r σ s₀ hh N 1
  have hem2 : Integrable (fun z => emPath (gbmDrift r) (gbmVol σ) h s₀ z N ^ 2) stdNormalSeq := by
    simpa using gridMax_integrable_emPath_pow r σ s₀ hh N 1
  have hIerr : ∫ z, (gbmGridExact r σ h s₀ z N -
      emPath (gbmDrift r) (gbmVol σ) h s₀ z N) ^ 2 ∂stdNormalSeq ≤ C₁ * h := by
    simpa using integral_gbmGrid_err_pow_le r σ s₀ hh hNT (m := 1) one_pos
  have hIem : ∫ z, emPath (gbmDrift r) (gbmVol σ) h s₀ z N ^ 2 ∂stdNormalSeq ≤ W := by
    have h1 : ∫ z, emPath (gbmDrift r) (gbmVol σ) h s₀ z N ^ 2 ∂stdNormalSeq ≤
        s₀ ^ 2 * Real.exp (gbmLpRate 1 r σ * (N * h)) := by
      simpa using gbmGrid_integral_emPath_pow_le r σ s₀ hh N 1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hNT (gbmLpRate_nonneg 1 r σ))) (sq_nonneg _))
  obtain ⟨-, hAinv, -, hbinv, hAB⟩ := gbmGrid_drift_factor_bounds r hh hr hNT
  have haN : 0 < a ^ N := pow_pos ha0 N
  have hbN : 0 < b ^ N := pow_pos hb0 N
  have hXY : ∫ z, (s₀ * ∏ i ∈ range N, gbmExpFactor r σ h (z i) / a -
      s₀ * ∏ i ∈ range N, gbmEMFactor r σ h (z i) / b) ^ 2 ∂stdNormalSeq ≤
      2 * E ^ 2 * (C₁ * h) + 2 * (κ * h) ^ 2 * W := by
    have hx : ∀ z : ℕ → ℝ, s₀ * ∏ i ∈ range N, gbmExpFactor r σ h (z i) / a -
        s₀ * ∏ i ∈ range N, gbmEMFactor r σ h (z i) / b =
        (a ^ N)⁻¹ * (gbmGridExact r σ h s₀ z N - emPath (gbmDrift r) (gbmVol σ) h s₀ z N) +
          ((a ^ N)⁻¹ - (b ^ N)⁻¹) * emPath (gbmDrift r) (gbmVol σ) h s₀ z N := fun z => by
      rw [hpA z N, hpB z N]
      field_simp
      ring
    have hcoef : ((a ^ N)⁻¹ - (b ^ N)⁻¹) ^ 2 ≤ (κ * h) ^ 2 := by
      have habs : |(a ^ N)⁻¹ - (b ^ N)⁻¹| ≤ κ * h := by
        have e : (a ^ N)⁻¹ - (b ^ N)⁻¹ = (b ^ N - a ^ N) * ((a ^ N)⁻¹ * (b ^ N)⁻¹) := by
          field_simp
        rw [e, abs_mul, abs_sub_comm, abs_of_pos (by positivity : 0 < (a ^ N)⁻¹ * (b ^ N)⁻¹)]
        calc |a ^ N - b ^ N| * ((a ^ N)⁻¹ * (b ^ N)⁻¹) ≤ (ρ * h) * (E * E2) := by
              gcongr
          _ = κ * h := by rw [hκdef]; ring
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hinv2 : ((a ^ N)⁻¹) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (inv_pos.2 haN).le hAinv 2
    have hint := (herr.const_mul (2 * E ^ 2)).add (hem2.const_mul (2 * (κ * h) ^ 2))
    calc _ ≤ ∫ z, (2 * E ^ 2 * (gbmGridExact r σ h s₀ z N -
          emPath (gbmDrift r) (gbmVol σ) h s₀ z N) ^ 2 +
          2 * (κ * h) ^ 2 * emPath (gbmDrift r) (gbmVol σ) h s₀ z N ^ 2) ∂stdNormalSeq := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hint
            (Eventually.of_forall fun z => ?_)
          beta_reduce
          rw [hx z]
          set u := gbmGridExact r σ h s₀ z N - emPath (gbmDrift r) (gbmVol σ) h s₀ z N
          set v := emPath (gbmDrift r) (gbmVol σ) h s₀ z N
          calc ((a ^ N)⁻¹ * u + ((a ^ N)⁻¹ - (b ^ N)⁻¹) * v) ^ 2
              ≤ 2 * ((a ^ N)⁻¹ * u) ^ 2 + 2 * (((a ^ N)⁻¹ - (b ^ N)⁻¹) * v) ^ 2 :=
                gridMax_add_sq_le _ _
            _ = 2 * (((a ^ N)⁻¹) ^ 2 * u ^ 2) + 2 * (((a ^ N)⁻¹ - (b ^ N)⁻¹) ^ 2 * v ^ 2) := by
                ring
            _ ≤ 2 * (E ^ 2 * u ^ 2) + 2 * ((κ * h) ^ 2 * v ^ 2) := by gcongr
            _ = _ := by ring
      _ = 2 * E ^ 2 * ∫ z, (gbmGridExact r σ h s₀ z N -
          emPath (gbmDrift r) (gbmVol σ) h s₀ z N) ^ 2 ∂stdNormalSeq +
          2 * (κ * h) ^ 2 * ∫ z, emPath (gbmDrift r) (gbmVol σ) h s₀ z N ^ 2 ∂stdNormalSeq := by
          rw [integral_add (herr.const_mul _) (hem2.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hIerr (by positivity))
          (mul_le_mul_of_nonneg_left hIem (by positivity))
  have hYb : ∫ z, (s₀ * ∏ i ∈ range N, gbmEMFactor r σ h (z i) / b) ^ 2 ∂stdNormalSeq ≤
      E2 ^ 2 * W := by
    have hy : ∀ z : ℕ → ℝ, (s₀ * ∏ i ∈ range N, gbmEMFactor r σ h (z i) / b) ^ 2 =
        ((b ^ N)⁻¹) ^ 2 * emPath (gbmDrift r) (gbmVol σ) h s₀ z N ^ 2 := fun z => by
      rw [hpB z N]
      field_simp
    simp_rw [hy]
    rw [integral_const_mul]
    exact mul_le_mul (pow_le_pow_left₀ (inv_pos.2 hbN).le hbinv 2) hIem
      (integral_nonneg fun z => sq_nonneg _) (by positivity)
  -- assemble
  have hsupInt := (hI1.const_mul (2 * E ^ 2)).add (hI2.const_mul (2 * (ρ * h) ^ 2))
  have hnn : ∀ z : ℕ → ℝ, 0 ≤ (range (N + 1)).sup' nonempty_range_add_one (fun n =>
      (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2) := fun z =>
    (sq_nonneg _).trans (Finset.le_sup' (fun n =>
      (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2)
      (self_mem_range_succ N))
  have hTh : h ^ 2 ≤ T * h := by nlinarith
  calc _ ≤ ∫ z, (2 * E ^ 2 * (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) / a -
          s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2) +
      2 * (ρ * h) ^ 2 * (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2)) ∂stdNormalSeq :=
        integral_mono_of_nonneg (Eventually.of_forall hnn) hsupInt (Eventually.of_forall hpt)
    _ = 2 * E ^ 2 * ∫ z, (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) / a -
          s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2) ∂stdNormalSeq +
      2 * (ρ * h) ^ 2 * ∫ z, (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) / b) ^ 2) ∂stdNormalSeq := by
        rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * E ^ 2 * (8 * (2 * E ^ 2 * (C₁ * h) + 2 * (κ * h) ^ 2 * W)) +
        2 * (ρ * h) ^ 2 * (8 * (E2 ^ 2 * W)) := by
        gcongr
        · exact hD1.trans (mul_le_mul_of_nonneg_left hXY (by norm_num))
        · exact hD2.trans (mul_le_mul_of_nonneg_left hYb (by norm_num))
    _ = 32 * E ^ 4 * C₁ * h + (32 * E ^ 2 * κ ^ 2 * W + 16 * ρ ^ 2 * E2 ^ 2 * W) * h ^ 2 := by
        ring
    _ ≤ 32 * E ^ 4 * C₁ * h + (32 * E ^ 2 * κ ^ 2 * W + 16 * ρ ^ 2 * E2 ^ 2 * W) * (T * h) := by
        gcongr
    _ = _ := by ring

/-- **The strong error of Euler–Maruyama for GBM uniformly over the time grid is `O(h)` in mean
square** (Giles 2015, §5.1, p. 29, l. 1296–1301: "the strong error for the Euler discretisation
with timestep `h` is `O(h^{1/2})`, so that `E[‖S − Ŝ‖²] = O(h)`", for the maximum norm of the
discrete path that the lookback options of Table 5.2, p. 33, need).  For GBM and `T ≥ 0` there is
`C` such that for every step `h ≥ 0` and every number of steps `N` with `Nh ≤ T`, the exact solution
`S_{t_n}` (`gbmGridExact`) and the Euler–Maruyama path `Ŝ_n` driven by the same increments satisfy:
`max_{0≤n≤N} (S_{t_n} − Ŝ_n)²` is integrable and `E[max_{0≤n≤N} (S_{t_n} − Ŝ_n)²] ≤ C h`.  The
proof is Doob's maximal inequality in `L²`, derived here from the pathwise inequality of Acciaio
et al. (2013) (`gridMax_pathwise_doob`), applied to the martingales `S_{t_n}/e^{rnh}` and
`Ŝ_n/(1 + rh)^n` (`gbm_em_grid_max_error_sharp_aux`, for `|r| h ≤ 1/2`); for `|r| h > 1/2` there
are fewer than `2|r|T` steps and the bound follows from the pointwise one.  A Monte Carlo check
at the paper's `r = 0.05`, `σ = 0.2`, `T = 1`, `S_0 = 1` gives `E[max_n e_n²]/h ≈ 0.0011–0.0017`
for `h = 2^{−2}, …, 2^{−9}`, consistent with the rate. -/
theorem gbm_em_grid_max_error_sharp (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ) (N : ℕ), 0 ≤ h → N * h ≤ T →
      Integrable (fun z => (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2))
          stdNormalSeq ∧
      ∫ z, (range (N + 1)).sup' nonempty_range_add_one (fun n =>
        (gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2)
          ∂stdNormalSeq ≤ C * h := by
  obtain ⟨K, hK, hsmall⟩ := gbm_em_grid_max_error_sharp_aux r σ s₀ hT
  have hC₁ := gbmEMMomentConst_nonneg 1 r σ s₀ hT
  refine ⟨K + (2 * |r| * T + 1) * gbmEMMomentConst 1 r σ T s₀, by positivity,
    fun h N hh hNT => ⟨(gbm_em_grid_max_error r σ s₀ hh hNT (m := 1) one_pos).1, ?_⟩⟩
  rcases le_or_gt (|r| * h) (1 / 2) with hr | hr
  · refine (hsmall h N hh hr hNT).trans ?_
    have : 0 ≤ (2 * |r| * T + 1) * gbmEMMomentConst 1 r σ T s₀ * h := by positivity
    nlinarith
  · have h1 := (gbm_em_grid_max_error r σ s₀ hh hNT (m := 1) one_pos).2
    simp only [Nat.cast_one, inv_one, Real.rpow_one, pow_one] at h1
    refine h1.trans ?_
    have hN : (N : ℝ) ≤ 2 * |r| * T := by
      have h2 : (N : ℝ) * (1 / 2) ≤ N * (|r| * h) :=
        mul_le_mul_of_nonneg_left hr.le (Nat.cast_nonneg N)
      have h3 : (N : ℝ) * (|r| * h) ≤ |r| * T := by
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left hNT (abs_nonneg r)
      linarith
    have hKh : 0 ≤ K * h := mul_nonneg hK hh
    have h4 : ((N : ℝ) + 1) * gbmEMMomentConst 1 r σ T s₀ * h ≤
        (2 * |r| * T + 1) * gbmEMMomentConst 1 r σ T s₀ * h := by
      gcongr
    nlinarith

/-- The one-step monitoring gap in `L^{2m}`: if `E[(A − 1)^{2m}] ≤ G h^m` and `nh ≤ T`, then
`E[(S_{t_n} − S_{t_{2⌊n/2⌋}})^{2m}] ≤ S_0^{2m} e^{ωT} G h^m` (`0` for even `n`; for `n = 2k + 1`
the difference is `S_{t_{2k}} (A_{2k} − 1)` with independent factors; Giles 2015, §5.2, p. 38,
l. 1655–1656). -/
lemma integral_gbmGrid_gap_pow_le (r σ s₀ : ℝ) {h T G : ℝ} (hh : 0 ≤ h) {m : ℕ} (hm : 0 < m)
    (hG : ∫ x, (gbmExpFactor r σ h x - 1) ^ (2 * m) ∂gaussianReal 0 1 ≤ G * h ^ m)
    {n : ℕ} (hnT : n * h ≤ T) :
    ∫ z, (gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z (2 * (n / 2))) ^ (2 * m)
      ∂stdNormalSeq ≤ s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * T) * (G * h ^ m) := by
  have hGh : 0 ≤ G * h ^ m :=
    (integral_nonneg fun x => (even_two_mul m).pow_nonneg _).trans hG
  have hs := (even_two_mul m).pow_nonneg s₀
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e : 2 * (2 * k / 2) = 2 * k := by omega
    simp only [e, sub_self, zero_pow (by omega : 2 * m ≠ 0), integral_zero]
    positivity
  · have e : 2 * ((2 * k + 1) / 2) = 2 * k := by omega
    have hfac : ∀ z, (gbmGridExact r σ h s₀ z (2 * k + 1) - gbmGridExact r σ h s₀ z (2 * k)) ^
        (2 * m) = gbmGridExact r σ h s₀ z (2 * k) ^ (2 * m) *
          (gbmExpFactor r σ h (z (2 * k)) - 1) ^ (2 * m) := fun z => by
      rw [← mul_pow, gbmGridExact_eq_prod, gbmGridExact_eq_prod, prod_range_succ]
      ring_nf
    simp only [e, hfac]
    rw [integral_mul_comp_eval_of_eq_lt (A := fun z => gbmGridExact r σ h s₀ z (2 * k) ^ (2 * m))
      ((measurable_gbmGridExact r σ h s₀ _).pow_const _) (fun z z' hzz => by
        rw [gbmGridExact_eq_prod, gbmGridExact_eq_prod, prod_range_eq_of_eq_lt _ hzz])
      (B := fun x => (gbmExpFactor r σ h x - 1) ^ (2 * m))
      (((measurable_gbmExpFactor r σ h).sub_const 1).pow_const _)]
    have hS := integral_gbmGridExact_pow_le r σ s₀ hh (2 * k) m
    have hω := gbmLpRate_nonneg m r σ
    have hkT : ((2 * k : ℕ) : ℝ) * h ≤ T := by
      refine le_trans (mul_le_mul_of_nonneg_right ?_ hh) hnT
      exact_mod_cast Nat.le_succ (2 * k)
    have hexp : Real.exp (gbmLpRate m r σ * ((2 * k : ℕ) * h)) ≤
        Real.exp (gbmLpRate m r σ * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hkT hω)
    have hS0 : 0 ≤ ∫ z, gbmGridExact r σ h s₀ z (2 * k) ^ (2 * m) ∂stdNormalSeq :=
      integral_nonneg fun z => (even_two_mul m).pow_nonneg _
    calc (∫ z, gbmGridExact r σ h s₀ z (2 * k) ^ (2 * m) ∂stdNormalSeq) *
          ∫ x, (gbmExpFactor r σ h x - 1) ^ (2 * m) ∂gaussianReal 0 1
        ≤ (s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * T)) * (G * h ^ m) :=
          mul_le_mul (hS.trans (mul_le_mul_of_nonneg_left hexp hs)) hG
            (integral_nonneg fun x => (even_two_mul m).pow_nonneg _) (by positivity)
      _ = _ := by ring

/-- The `2m`-th power of the difference of the exact solution at two grid times is integrable
(Giles 2015, §5.2). -/
lemma integrable_gbmGrid_gap_pow (r σ h s₀ : ℝ) (n j m : ℕ) :
    Integrable (fun z => (gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z j) ^ (2 * m))
      stdNormalSeq :=
  gridMax_integrable_sub_pow (measurable_gbmGridExact r σ h s₀ n).aestronglyMeasurable
    (measurable_gbmGridExact r σ h s₀ j).aestronglyMeasurable m
    (integrable_gbmGridExact_pow r σ h s₀ n (2 * m))
    (integrable_gbmGridExact_pow r σ h s₀ j (2 * m))

/-- The maximum of the first `N + 1` values is measurable on `ℕ → ℝ` (Giles 2015, §5.2). -/
lemma gridMax_measurable_range_sup' (N : ℕ) :
    Measurable fun S : ℕ → ℝ => (range (N + 1)).sup' nonempty_range_add_one S :=
  Finset.measurable_range_sup'' (f := fun k (S : ℕ → ℝ) => S k) fun k _ => measurable_pi_apply k

/-- The minimum of the first `N + 1` values is measurable on `ℕ → ℝ` (Giles 2015, §5.2). -/
lemma gridMax_measurable_range_inf' (N : ℕ) :
    Measurable fun S : ℕ → ℝ => (range (N + 1)).inf' nonempty_range_add_one S := by
  have h : Measurable ((range (N + 1)).inf' nonempty_range_add_one (fun k (S : ℕ → ℝ) => S k)) :=
    Finset.inf'_induction _ _ (fun _ hf _ hg => hf.inf hg) fun k _ => measurable_pi_apply k
  convert h using 1
  funext S
  rw [Finset.inf'_apply]

/-- **The monitoring gap of the exact solution: fine-grid minus coarse-grid maximum and minimum**
(Giles 2015, §5.2, p. 38, l. 1653–1658: "A multilevel estimator based directly on the minimum (or
maximum) of the values at the discrete timesteps will have a poor variance.  This is because there
is an `O(h^{1/2})` variation in the asset value within each timestep of size `h`, and therefore
there is an `O(h_ℓ)` difference on average between the minimum (or maximum) values for the coarse
and fine paths.  This results in an `O(h_ℓ)` variance for lookback options").  For GBM, `T ≥ 0` and
every `δ > 0` there is `C` such that for every fine step `h ≥ 0` and `N` with `2Nh ≤ T`, the exact
solution on the fine grid (`2N` steps of size `h`) and on the coarse grid (its even times, i.e. `N`
steps of size `2h` driven by the summed increments, `gbmGridExact_pairAvg`) satisfy
`E[(max_{n≤2N} S_{t_n} − max_{k≤N} S_{t_{2k}})²] ≤ C h^{1−δ}`, and the same for the minima (both
squared gaps are integrable).  The gap
is at most the largest of the `N` one-step increments `S_{t_{2k+1}} − S_{t_{2k}}`, which are
`O(h^{1/2})` in every `L^{2m}` (`gbmGrid_expFactor_sub_one_moment`).  **Deviation**: the paper's
`O(h_ℓ)` variance (`E[gap²] = O(h)`) is not proved; the loss `δ` comes from the maximum of `N`
increments and is not removed by Doob's inequality (the gap is not a martingale).  A Monte Carlo
check (`r = 0.05`, `σ = 0.2`, `T = 1`) gives `E[gap²]/h ≈ 0.006–0.011` for `h = 2^{−2}, …, 2^{−9}`,
i.e. the true rate is `O(h)`.  **Paper imprecision**: the average gap is of order `h^{1/2}`, not
`h_ℓ` (`E[gap]/√h ≈ 0.034–0.055`, `E[gap]/h ≈ 0.07–1.8` for `h = 2^{−2}, …, 2^{−10}` in the same
check); the `O(h_ℓ)` variance follows from the `O(h_ℓ^{1/2})` root-mean-square gap. -/
theorem gbm_grid_monitoring_gap_rate (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ) (N : ℕ), 0 ≤ h → 2 * N * h ≤ T →
      Integrable (fun z => ((range (2 * N + 1)).sup' nonempty_range_add_one
        (gbmGridExact r σ h s₀ z) - (range (N + 1)).sup' nonempty_range_add_one
          (fun k => gbmGridExact r σ h s₀ z (2 * k))) ^ 2) stdNormalSeq ∧
      ∫ z, ((range (2 * N + 1)).sup' nonempty_range_add_one (gbmGridExact r σ h s₀ z) -
        (range (N + 1)).sup' nonempty_range_add_one (fun k => gbmGridExact r σ h s₀ z (2 * k))) ^ 2
          ∂stdNormalSeq ≤ C * h ^ (1 - δ) ∧
      Integrable (fun z => ((range (2 * N + 1)).inf' nonempty_range_add_one
        (gbmGridExact r σ h s₀ z) - (range (N + 1)).inf' nonempty_range_add_one
          (fun k => gbmGridExact r σ h s₀ z (2 * k))) ^ 2) stdNormalSeq ∧
      ∫ z, ((range (2 * N + 1)).inf' nonempty_range_add_one (gbmGridExact r σ h s₀ z) -
        (range (N + 1)).inf' nonempty_range_add_one (fun k => gbmGridExact r σ h s₀ z (2 * k))) ^ 2
          ∂stdNormalSeq ≤ C * h ^ (1 - δ) := by
  obtain ⟨m, hm, hmδ⟩ := gridMax_exists_nat_inv_le hδ
  obtain ⟨G, hG0, hG⟩ := gbmGrid_expFactor_sub_one_moment r σ hT hm
  set D := s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * T) * G with hD
  have hD0 : 0 ≤ D := by
    have := (even_two_mul m).pow_nonneg s₀
    positivity
  refine ⟨(2 * T * D) ^ ((m : ℝ)⁻¹) * T ^ (δ - (m : ℝ)⁻¹),
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hT _),
    fun h N hh hNT => ?_⟩
  have hR0 : 0 ≤ (2 * T * D) ^ ((m : ℝ)⁻¹) * T ^ (δ - (m : ℝ)⁻¹) * h ^ (1 - δ) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hT _))
      (Real.rpow_nonneg hh _)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [mul_zero, zero_add, range_one, sup'_singleton, inf'_singleton, sub_self,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, integrable_fun_zero,
      true_and]
    exact ⟨hR0, hR0⟩
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
  have hhT : h ≤ T := by nlinarith
  have hMh : (((2 * N : ℕ) : ℝ) + 1) * h ≤ 2 * T := by push_cast; nlinarith
  obtain ⟨hI, hle⟩ := gridMax_integral_sup'_sq_rate (M := 2 * N)
    (X := fun n z => gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z (2 * (n / 2)))
    (fun n => (measurable_gbmGridExact r σ h s₀ n).sub (measurable_gbmGridExact r σ h s₀ _))
    hm hmδ hh hhT hMh hD0 (fun n hn => ⟨integrable_gbmGrid_gap_pow r σ h s₀ n _ m,
      (integral_gbmGrid_gap_pow_le r σ s₀ (T := T) hh hm (hG h hh hhT) (by
        have hn' : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn
        nlinarith)).trans_eq (by rw [hD]; ring)⟩)
  have hsup : ∀ z, (range (N + 1)).sup' nonempty_range_add_one
      (fun k => gbmGridExact r σ h s₀ z (2 * k)) = (range (2 * N + 1)).sup' nonempty_range_add_one
        (fun n => gbmGridExact r σ h s₀ z (2 * (n / 2))) := fun z =>
    (gridMax_sup'_range_div_two N (fun k => gbmGridExact r σ h s₀ z (2 * k))).symm
  have hinf : ∀ z, (range (N + 1)).inf' nonempty_range_add_one
      (fun k => gbmGridExact r σ h s₀ z (2 * k)) = (range (2 * N + 1)).inf' nonempty_range_add_one
        (fun n => gbmGridExact r σ h s₀ z (2 * (n / 2))) := fun z =>
    (gridMax_inf'_range_div_two N (fun k => gbmGridExact r σ h s₀ z (2 * k))).symm
  have hcoarse : Measurable fun z k => gbmGridExact r σ h s₀ z (2 * k) :=
    measurable_pi_lambda _ fun k => measurable_gbmGridExact r σ h s₀ (2 * k)
  have hpsup : ∀ z, ((range (2 * N + 1)).sup' nonempty_range_add_one (gbmGridExact r σ h s₀ z) -
      (range (N + 1)).sup' nonempty_range_add_one (fun k => gbmGridExact r σ h s₀ z (2 * k))) ^ 2 ≤
        (range (2 * N + 1)).sup' nonempty_range_add_one (fun n =>
          (gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z (2 * (n / 2))) ^ 2) := fun z => by
    rw [hsup z]
    exact gridMax_sq_sup'_sub_le _ _ _
  have hpinf : ∀ z, ((range (2 * N + 1)).inf' nonempty_range_add_one (gbmGridExact r σ h s₀ z) -
      (range (N + 1)).inf' nonempty_range_add_one (fun k => gbmGridExact r σ h s₀ z (2 * k))) ^ 2 ≤
        (range (2 * N + 1)).sup' nonempty_range_add_one (fun n =>
          (gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z (2 * (n / 2))) ^ 2) := fun z => by
    rw [hinf z]
    exact gridMax_sq_inf'_sub_le _ _ _
  refine ⟨hI.mono' ((((gridMax_measurable_range_sup' (2 * N)).comp
      (measurable_gbmGridExact_pi r σ h s₀)).sub ((gridMax_measurable_range_sup' N).comp
        hcoarse)).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun z => ?_),
    le_trans (integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hI
      (Eventually.of_forall hpsup)) hle,
    hI.mono' ((((gridMax_measurable_range_inf' (2 * N)).comp
      (measurable_gbmGridExact_pi r σ h s₀)).sub ((gridMax_measurable_range_inf' N).comp
        hcoarse)).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun z => ?_),
    le_trans (integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hI
      (Eventually.of_forall hpinf)) hle⟩
  · rw [Real.norm_eq_abs, abs_sq]
    exact hpsup z
  · rw [Real.norm_eq_abs, abs_sq]
    exact hpinf z

/-- **The fine-minus-coarse Euler–Maruyama difference at one fine time in `L^{2m}`**: for
`n ≤ 2N`, `2Nh ≤ T`, the fine path `Ŝ^f_n` (step `h`) and the coarse path `Ŝ^c_{⌊n/2⌋}` (step `2h`,
driven by the summed increments) satisfy `E[(Ŝ^f_n − Ŝ^c_{⌊n/2⌋})^{2m}] ≤ 3^{2m−1}((1 + 2^m)
C_m(T) + S_0^{2m} e^{ωT} G) h^m`: split into the fine strong error, the one-step monitoring gap of
the exact solution and the coarse strong error (`gbmGridExact_pairAvg`; Giles 2015, §5.1, p. 29,
and §5.2, p. 38, l. 1653–1658). -/
lemma gbmGrid_cross_pow_le (r σ s₀ : ℝ) {h T G : ℝ} (hh : 0 ≤ h) {m : ℕ} (hm : 0 < m)
    (hG : ∫ x, (gbmExpFactor r σ h x - 1) ^ (2 * m) ∂gaussianReal 0 1 ≤ G * h ^ m)
    {N : ℕ} (hNT : 2 * N * h ≤ T) {n : ℕ} (hn : n ≤ 2 * N) :
    Integrable (fun z => (emPath (gbmDrift r) (gbmVol σ) h s₀ z n -
        emPath (gbmDrift r) (gbmVol σ) (2 * h) s₀ (pairAvg z) (n / 2)) ^ (2 * m)) stdNormalSeq ∧
    ∫ z, (emPath (gbmDrift r) (gbmVol σ) h s₀ z n -
        emPath (gbmDrift r) (gbmVol σ) (2 * h) s₀ (pairAvg z) (n / 2)) ^ (2 * m) ∂stdNormalSeq ≤
      3 ^ (2 * m - 1) * ((1 + 2 ^ m) * gbmEMMomentConst m r σ T s₀ +
        s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * T) * G) * h ^ m := by
  have h2h : 0 ≤ 2 * h := by positivity
  have hpa := measurePreserving_pairAvg
  have he := even_two_mul m
  have hn' : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn
  have hnT : (n : ℝ) * h ≤ T := by nlinarith
  have hkT : ((n / 2 : ℕ) : ℝ) * (2 * h) ≤ T := by
    have : ((n / 2 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 2
    nlinarith
  -- the coarse values as functions of the coarse increments
  set Fc : (ℕ → ℝ) → ℝ := fun z => emPath (gbmDrift r) (gbmVol σ) (2 * h) s₀ z (n / 2) with hFc
  set Fe : (ℕ → ℝ) → ℝ := fun z => (gbmGridExact r σ (2 * h) s₀ z (n / 2) -
    emPath (gbmDrift r) (gbmVol σ) (2 * h) s₀ z (n / 2)) ^ (2 * m) with hFe
  have hFcm : Measurable Fc := gridMax_measurable_emPath r σ (2 * h) s₀ (n / 2)
  have hFem : Measurable Fe := ((measurable_gbmGridExact r σ (2 * h) s₀ _).sub
    (gridMax_measurable_emPath r σ (2 * h) s₀ _)).pow_const _
  have hFci : Integrable (fun z => Fc z ^ (2 * m)) stdNormalSeq :=
    gridMax_integrable_emPath_pow r σ s₀ h2h (n / 2) m
  have hFei : Integrable Fe stdNormalSeq := integrable_gbmGrid_err_pow r σ s₀ h2h (n / 2) m
  have hEci : Integrable (fun z => Fc (pairAvg z) ^ (2 * m)) stdNormalSeq :=
    (hpa.integrable_comp hFci.aestronglyMeasurable).2 hFci
  have hwi : Integrable (fun z => Fe (pairAvg z)) stdNormalSeq :=
    (hpa.integrable_comp hFei.aestronglyMeasurable).2 hFei
  have hEfi := gridMax_integrable_emPath_pow r σ s₀ hh n m
  refine ⟨gridMax_integrable_sub_pow (gridMax_measurable_emPath r σ h s₀ n).aestronglyMeasurable
    (hFcm.comp hpa.measurable).aestronglyMeasurable m hEfi hEci, ?_⟩
  have hxi : Integrable (fun z => (gbmGridExact r σ h s₀ z n -
      emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m)) stdNormalSeq :=
    integrable_gbmGrid_err_pow r σ s₀ hh n m
  have hyi := integrable_gbmGrid_gap_pow r σ h s₀ n (2 * (n / 2)) m
  -- the pointwise splitting
  have hpt : ∀ z, (emPath (gbmDrift r) (gbmVol σ) h s₀ z n - Fc (pairAvg z)) ^ (2 * m) ≤
      3 ^ (2 * m - 1) * ((gbmGridExact r σ h s₀ z n -
        emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m) +
        (gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z (2 * (n / 2))) ^ (2 * m) +
        Fe (pairAvg z)) := fun z => by
    have hsplit : emPath (gbmDrift r) (gbmVol σ) h s₀ z n - Fc (pairAvg z) =
        -(gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n) +
        (gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z (2 * (n / 2))) +
        (gbmGridExact r σ (2 * h) s₀ (pairAvg z) (n / 2) - Fc (pairAvg z)) := by
      rw [gbmGridExact_pairAvg]
      ring
    rw [hsplit]
    have h3 := gridMax_add_three_pow_le
      (-(gbmGridExact r σ h s₀ z n - emPath (gbmDrift r) (gbmVol σ) h s₀ z n))
      (gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z (2 * (n / 2)))
      (gbmGridExact r σ (2 * h) s₀ (pairAvg z) (n / 2) - Fc (pairAvg z)) m
    rwa [he.neg_pow] at h3
  have hI1 := integral_gbmGrid_err_pow_le r σ s₀ hh hnT hm
  have hI2 := integral_gbmGrid_gap_pow_le r σ s₀ hh hm hG hnT
  have hI3 : ∫ z, Fe (pairAvg z) ∂stdNormalSeq ≤ gbmEMMomentConst m r σ T s₀ * (2 * h) ^ m := by
    rw [integral_comp_of_measurePreserving hpa hFem.aestronglyMeasurable]
    exact integral_gbmGrid_err_pow_le r σ s₀ h2h hkT hm
  have hxy : Integrable (fun z => (gbmGridExact r σ h s₀ z n -
      emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m) +
      (gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z (2 * (n / 2))) ^ (2 * m))
      stdNormalSeq := hxi.add hyi
  have hint := (hxy.add hwi).const_mul (3 ^ (2 * m - 1))
  calc ∫ z, (emPath (gbmDrift r) (gbmVol σ) h s₀ z n - Fc (pairAvg z)) ^ (2 * m) ∂stdNormalSeq
      ≤ ∫ z, 3 ^ (2 * m - 1) * ((gbmGridExact r σ h s₀ z n -
          emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m) +
          (gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z (2 * (n / 2))) ^ (2 * m) +
          Fe (pairAvg z)) ∂stdNormalSeq :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => he.pow_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = 3 ^ (2 * m - 1) * (∫ z, (gbmGridExact r σ h s₀ z n -
          emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m) ∂stdNormalSeq +
          ∫ z, (gbmGridExact r σ h s₀ z n - gbmGridExact r σ h s₀ z (2 * (n / 2))) ^ (2 * m)
            ∂stdNormalSeq + ∫ z, Fe (pairAvg z) ∂stdNormalSeq) := by
        rw [integral_const_mul, integral_add hxy hwi, integral_add hxi hyi]
    _ ≤ 3 ^ (2 * m - 1) * (gbmEMMomentConst m r σ T s₀ * h ^ m +
          s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * T) * (G * h ^ m) +
          gbmEMMomentConst m r σ T s₀ * (2 * h) ^ m) := by
        gcongr
    _ = _ := by
        rw [mul_pow]
        ring

/-- **The maximum over the fine grid of the fine-minus-coarse difference**: for every `δ > 0`
there is `C` with `E[max_{n≤2N} (Ŝ^f_n − Ŝ^c_{⌊n/2⌋})²] ≤ C h^{1−δ}` for `0 ≤ h ≤ T`, `2Nh ≤ T`
(`gbmGrid_cross_pow_le` and `gridMax_integral_sup'_sq_rate`; Giles 2015, §5.1–§5.2). -/
lemma gbmGrid_cross_sup'_rate (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ) (N : ℕ), 0 ≤ h → h ≤ T → 2 * N * h ≤ T →
      Integrable (fun z => (range (2 * N + 1)).sup' nonempty_range_add_one (fun n =>
        (emPath (gbmDrift r) (gbmVol σ) h s₀ z n -
          emPath (gbmDrift r) (gbmVol σ) (2 * h) s₀ (pairAvg z) (n / 2)) ^ 2)) stdNormalSeq ∧
      ∫ z, (range (2 * N + 1)).sup' nonempty_range_add_one (fun n =>
        (emPath (gbmDrift r) (gbmVol σ) h s₀ z n -
          emPath (gbmDrift r) (gbmVol σ) (2 * h) s₀ (pairAvg z) (n / 2)) ^ 2) ∂stdNormalSeq ≤
        C * h ^ (1 - δ) := by
  obtain ⟨m, hm, hmδ⟩ := gridMax_exists_nat_inv_le hδ
  obtain ⟨G, hG0, hG⟩ := gbmGrid_expFactor_sub_one_moment r σ hT hm
  set D := 3 ^ (2 * m - 1) * ((1 + 2 ^ m) * gbmEMMomentConst m r σ T s₀ +
    s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * T) * G) with hD
  have hD0 : 0 ≤ D := by
    have := (even_two_mul m).pow_nonneg s₀
    have := gbmEMMomentConst_nonneg m r σ s₀ hT
    positivity
  refine ⟨(2 * T * D) ^ ((m : ℝ)⁻¹) * T ^ (δ - (m : ℝ)⁻¹),
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hT _),
    fun h N hh hhT hNT => ?_⟩
  have hMh : (((2 * N : ℕ) : ℝ) + 1) * h ≤ 2 * T := by push_cast; nlinarith
  exact gridMax_integral_sup'_sq_rate (M := 2 * N)
    (X := fun n z => emPath (gbmDrift r) (gbmVol σ) h s₀ z n -
      emPath (gbmDrift r) (gbmVol σ) (2 * h) s₀ (pairAvg z) (n / 2))
    (fun n => (gridMax_measurable_emPath r σ h s₀ n).sub
      ((gridMax_measurable_emPath r σ (2 * h) s₀ _).comp measurePreserving_pairAvg.measurable))
    hm hmδ hh hhT hMh hD0 (fun n hn => gbmGrid_cross_pow_le r σ s₀ hh hm (hG h hh hhT)
      hNT hn)

/-! ### Lookback payoffs monitored at every time step -/

/-- The lookback payoff on the minimum, `g(min_{0≤k≤m} S_k)` (Giles 2015, §5.1, p. 33: "the
lookback is based on its maximum or minimum value", l. 1452–1455; §5.2, p. 38, l. 1650–1653).  With
`m = 2^ℓ` and the Euler–Maruyama path of level `ℓ` it is monitored at every time step. -/
noncomputable def lookbackMinPayoff (g : ℝ → ℝ) (m : ℕ) (S : ℕ → ℝ) : ℝ :=
  g ((range (m + 1)).inf' nonempty_range_add_one S)

/-- The maximum of nonnegative numbers is at most their sum (Giles 2015, §5.1). -/
lemma gridMax_sup'_le_sum {s : Finset ℕ} (hs : s.Nonempty) {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) :
    s.sup' hs f ≤ ∑ k ∈ s, f k :=
  Finset.sup'_le _ _ fun _ hk => Finset.single_le_sum (fun j _ => hf j) hk

/-- The lookback payoff on the maximum is Lipschitz for the sup-norm of the path:
`(g(max a) − g(max b))² ≤ K² max_{n≤N} (a_n − b_n)²` (Giles 2015, §5.1, p. 29, l. 1302–1305:
"Lipschitz payoff functions `P` (such as … lookback options …)"). -/
lemma lookbackPayoff_grid_sq_le {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|)
    (N : ℕ) (a b : ℕ → ℝ) :
    (lookbackPayoff g N a - lookbackPayoff g N b) ^ 2 ≤
      K ^ 2 * (range (N + 1)).sup' nonempty_range_add_one (fun n => (a n - b n) ^ 2) :=
  (sq_sub_le_of_lipschitz_mon hg _ _).trans (mul_le_mul_of_nonneg_left
    (gridMax_sq_sup'_sub_le _ a b) (sq_nonneg K))

/-- The fine and the coarse lookback payoffs on the maximum:
`(g(max_{n≤2N} a_n) − g(max_{k≤N} b_k))² ≤ K² max_{n≤2N} (a_n − b_{⌊n/2⌋})²` (the coarse maximum
is a maximum over the fine grid of `b_{⌊n/2⌋}`; Giles 2015, §5.2, p. 38, l. 1653–1658). -/
lemma lookbackPayoff_cross_sq_le {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|)
    (N : ℕ) (a b : ℕ → ℝ) :
    (lookbackPayoff g (2 * N) a - lookbackPayoff g N b) ^ 2 ≤
      K ^ 2 * (range (2 * N + 1)).sup' nonempty_range_add_one (fun n => (a n - b (n / 2)) ^ 2) := by
  unfold lookbackPayoff
  rw [← gridMax_sup'_range_div_two N b]
  exact (sq_sub_le_of_lipschitz_mon hg _ _).trans (mul_le_mul_of_nonneg_left
    (gridMax_sq_sup'_sub_le _ a _) (sq_nonneg K))

/-- The lookback payoff on the minimum is Lipschitz for the sup-norm of the path:
`(g(min a) − g(min b))² ≤ K² max_{n≤N} (a_n − b_n)²` (Giles 2015, §5.1, p. 29, l. 1302–1305). -/
lemma lookbackMinPayoff_grid_sq_le {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|)
    (N : ℕ) (a b : ℕ → ℝ) :
    (lookbackMinPayoff g N a - lookbackMinPayoff g N b) ^ 2 ≤
      K ^ 2 * (range (N + 1)).sup' nonempty_range_add_one (fun n => (a n - b n) ^ 2) :=
  (sq_sub_le_of_lipschitz_mon hg _ _).trans (mul_le_mul_of_nonneg_left
    (gridMax_sq_inf'_sub_le _ a b) (sq_nonneg K))

/-- The fine and the coarse lookback payoffs on the minimum:
`(g(min_{n≤2N} a_n) − g(min_{k≤N} b_k))² ≤ K² max_{n≤2N} (a_n − b_{⌊n/2⌋})²` (Giles 2015, §5.2,
p. 38, l. 1653–1658). -/
lemma lookbackMinPayoff_cross_sq_le {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|)
    (N : ℕ) (a b : ℕ → ℝ) :
    (lookbackMinPayoff g (2 * N) a - lookbackMinPayoff g N b) ^ 2 ≤
      K ^ 2 * (range (2 * N + 1)).sup' nonempty_range_add_one (fun n => (a n - b (n / 2)) ^ 2) := by
  unfold lookbackMinPayoff
  rw [← gridMax_inf'_range_div_two N b]
  exact (sq_sub_le_of_lipschitz_mon hg _ _).trans (mul_le_mul_of_nonneg_left
    (gridMax_sq_inf'_sub_le _ a _) (sq_nonneg K))

/-- The floating-strike lookback payoff `g(S_N − min_{k≤N} S_k)` is Lipschitz for the sup-norm:
`(…)² ≤ 4K² max_{n≤N} (a_n − b_n)²` (Giles 2015, §5.1, p. 29 and p. 33). -/
lemma floatLookbackPayoff_grid_sq_le {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (N : ℕ) (a b : ℕ → ℝ) :
    (floatLookbackPayoff g N a - floatLookbackPayoff g N b) ^ 2 ≤
      4 * K ^ 2 * (range (N + 1)).sup' nonempty_range_add_one (fun n => (a n - b n) ^ 2) := by
  have h1 := gridMax_sq_inf'_sub_le (nonempty_range_add_one (n := N)) a b
  have h2 : (a N - b N) ^ 2 ≤ (range (N + 1)).sup' nonempty_range_add_one
      (fun n => (a n - b n) ^ 2) :=
    Finset.le_sup' (fun n => (a n - b n) ^ 2) (Finset.self_mem_range_succ N)
  unfold floatLookbackPayoff
  refine (sq_sub_le_of_lipschitz_mon hg _ _).trans ?_
  rw [mul_assoc 4, mul_left_comm 4]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
  nlinarith [sq_nonneg (a N - b N + ((range (N + 1)).inf' nonempty_range_add_one a -
    (range (N + 1)).inf' nonempty_range_add_one b))]

/-- The fine and the coarse floating-strike lookback payoffs:
`(g(a_{2N} − min_{n≤2N} a_n) − g(b_N − min_{k≤N} b_k))² ≤ 4K² max_{n≤2N} (a_n − b_{⌊n/2⌋})²`
(the final values are `a_{2N}` and `b_{⌊2N/2⌋}`; Giles 2015, §5.2, p. 38). -/
lemma floatLookbackPayoff_cross_sq_le {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (N : ℕ) (a b : ℕ → ℝ) :
    (floatLookbackPayoff g (2 * N) a - floatLookbackPayoff g N b) ^ 2 ≤
      4 * K ^ 2 * (range (2 * N + 1)).sup' nonempty_range_add_one
        (fun n => (a n - b (n / 2)) ^ 2) := by
  have h1 := gridMax_sq_inf'_sub_le (nonempty_range_add_one (n := 2 * N)) a (fun n => b (n / 2))
  have h2 : (a (2 * N) - b (2 * N / 2)) ^ 2 ≤ (range (2 * N + 1)).sup' nonempty_range_add_one
      (fun n => (a n - b (n / 2)) ^ 2) :=
    Finset.le_sup' (fun n => (a n - b (n / 2)) ^ 2) (Finset.self_mem_range_succ (2 * N))
  have e : 2 * N / 2 = N := by omega
  rw [e] at h2
  unfold floatLookbackPayoff
  rw [← gridMax_inf'_range_div_two N b]
  refine (sq_sub_le_of_lipschitz_mon hg _ _).trans ?_
  rw [mul_assoc 4, mul_left_comm 4]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
  nlinarith [sq_nonneg (a (2 * N) - b N + ((range (2 * N + 1)).inf' nonempty_range_add_one a -
    (range (2 * N + 1)).inf' nonempty_range_add_one (fun n => b (n / 2))))]

/-! ### The multilevel estimator with every-step monitoring

Level `ℓ` uses `2^ℓ` Euler–Maruyama steps of size `h_ℓ = T 2^{−ℓ}` and the payoff
`P_ℓ = Φ_{2^ℓ}(Ŝ_0, …, Ŝ_{2^ℓ})` of all its values; the coarse path of a level-`(ℓ + 1)` sample is
driven by the summed increments (`emCoarse_eq`).  The payoffs `Φ_N` are measurable and satisfy
`(Φ_N(a) − Φ_N(b))² ≤ c max_{n≤N} (a_n − b_n)²` and
`(Φ_{2N}(a) − Φ_N(b))² ≤ c max_{n≤2N} (a_n − b_{⌊n/2⌋})²`; the lookback payoffs on the maximum,
on the minimum and with floating strike do. -/

/-- `2 h_{ℓ+1} = h_ℓ` for `h_ℓ = T 2^{−ℓ}` (Giles 2015, §5.1, p. 29: `h_ℓ = 2^{−ℓ} h_0`). -/
lemma gridMax_two_mul_div_two_pow_succ (T : ℝ) (ℓ : ℕ) : 2 * (T / 2 ^ (ℓ + 1)) = T / 2 ^ ℓ := by
  rw [pow_succ (2 : ℝ) ℓ, ← div_div, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- `(T/2^ℓ)^a = T^a (2^{−a})^ℓ` for `T ≥ 0` (the rates in `h_ℓ` as geometric rates in `ℓ`,
Giles 2015, §2.1, Theorem 1). -/
lemma gridMax_div_two_pow_rpow {T : ℝ} (hT : 0 ≤ T) (a : ℝ) (ℓ : ℕ) :
    (T / 2 ^ ℓ) ^ a = T ^ a * ((2 : ℝ) ^ (-a)) ^ ℓ := by
  rw [Real.div_rpow hT (by positivity), ← Real.rpow_natCast (2 : ℝ) ℓ,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast ((2 : ℝ) ^ (-a)) ℓ,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
  congr 2
  ring

/-- `(2^{−a})^ℓ = 2^{−aℓ}` (Giles 2015, §2.1, Theorem 1). -/
lemma gridMax_two_rpow_neg_pow (a : ℝ) (ℓ : ℕ) : ((2 : ℝ) ^ (-a)) ^ ℓ = (2 : ℝ) ^ (-(a * ℓ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- `√(C x^{1−δ}) = √C x^{(1−δ)/2}` for `C, x ≥ 0` (from the second moment of the correction to
its mean; Giles 2015, §2.1). -/
lemma gridMax_sqrt_mul_rpow {C x : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (δ : ℝ) :
    Real.sqrt (C * x ^ (1 - δ)) = Real.sqrt C * x ^ ((1 - δ) / 2) := by
  have e : x ^ (1 - δ) = (x ^ ((1 - δ) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  rw [e, Real.sqrt_mul hC, Real.sqrt_sq (Real.rpow_nonneg hx _)]

/-- The Euler–Maruyama path of GBM is measurable as a map into `ℕ → ℝ` (Giles 2015, §5.1). -/
lemma gridMax_measurable_emPath_pi (r σ h s₀ : ℝ) :
    Measurable fun z => emPath (gbmDrift r) (gbmVol σ) h s₀ z :=
  measurable_pi_lambda _ fun n => gridMax_measurable_emPath r σ h s₀ n

section Levels

variable {Φ : ℕ → (ℕ → ℝ) → ℝ} {c : ℝ}

/-- A grid payoff of a path that is square integrable at every grid time is square integrable
(Giles 2015, §5.1, p. 29: Lipschitz payoffs of the path). -/
lemma memLp_gridPayoff (hc : 0 ≤ c) (hΦm : ∀ N, Measurable (Φ N))
    (hΦ1 : ∀ N (a b : ℕ → ℝ), (Φ N a - Φ N b) ^ 2 ≤
      c * (range (N + 1)).sup' nonempty_range_add_one (fun n => (a n - b n) ^ 2))
    {X : (ℕ → ℝ) → ℕ → ℝ} (hXm : Measurable X)
    (hX : ∀ n, Integrable (fun z => X z n ^ 2) stdNormalSeq) (N : ℕ) :
    MemLp (fun z => Φ N (X z)) 2 stdNormalSeq := by
  have hm : AEStronglyMeasurable (fun z => Φ N (X z)) stdNormalSeq :=
    ((hΦm N).comp hXm).aestronglyMeasurable
  have hb : Integrable (fun z => 2 * Φ N 0 ^ 2 + 2 * c * ∑ n ∈ range (N + 1), X z n ^ 2)
      stdNormalSeq :=
    (integrable_const _).add ((integrable_finsetSum _ fun n _ => hX n).const_mul _)
  refine (memLp_two_iff_integrable_sq hm).2
    (hb.mono' (hm.pow 2) (Eventually.of_forall fun z => ?_))
  have h1 := hΦ1 N (X z) 0
  simp only [Pi.zero_apply, sub_zero] at h1
  have h2 := gridMax_sup'_le_sum (nonempty_range_add_one (n := N))
    (f := fun n => X z n ^ 2) (fun n => sq_nonneg _)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (Φ N (X z) - 2 * Φ N 0), mul_le_mul_of_nonneg_left h2 hc]

/-- The grid payoff of the Euler–Maruyama path of GBM is square integrable (Giles 2015,
§5.1). -/
lemma memLp_gridPayoff_em (hc : 0 ≤ c) (hΦm : ∀ N, Measurable (Φ N))
    (hΦ1 : ∀ N (a b : ℕ → ℝ), (Φ N a - Φ N b) ^ 2 ≤
      c * (range (N + 1)).sup' nonempty_range_add_one (fun n => (a n - b n) ^ 2))
    (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    MemLp (fun z => Φ N (emPath (gbmDrift r) (gbmVol σ) h s₀ z)) 2 stdNormalSeq :=
  memLp_gridPayoff hc hΦm hΦ1 (gridMax_measurable_emPath_pi r σ h s₀)
    (fun n => by simpa using gridMax_integrable_emPath_pow r σ s₀ hh n 1) N

/-- The grid payoff of the exact solution on the grid is square integrable (Giles 2015, §5.1). -/
lemma memLp_gridPayoff_exact (hc : 0 ≤ c) (hΦm : ∀ N, Measurable (Φ N))
    (hΦ1 : ∀ N (a b : ℕ → ℝ), (Φ N a - Φ N b) ^ 2 ≤
      c * (range (N + 1)).sup' nonempty_range_add_one (fun n => (a n - b n) ^ 2))
    (r σ h s₀ : ℝ) (N : ℕ) :
    MemLp (fun z => Φ N (gbmGridExact r σ h s₀ z)) 2 stdNormalSeq :=
  memLp_gridPayoff hc hΦm hΦ1 (measurable_gbmGridExact_pi r σ h s₀)
    (fun n => integrable_gbmGridExact_pow r σ h s₀ n 2) N

/-- **The second moment of the level correction with every-step monitoring**: for every `δ > 0`
there is `C` with `E[(Φ_{2^{ℓ+1}}(Ŝ^f) − Φ_{2^ℓ}(Ŝ^c))²] ≤ C h_{ℓ+1}^{1−δ}`
(`gbmGrid_cross_sup'_rate`; Giles 2015, §5.2, p. 38, l. 1653–1658). -/
lemma gridPayoff_cross_rate (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hΦ2 : ∀ N (a b : ℕ → ℝ), (Φ (2 * N) a - Φ N b) ^ 2 ≤
      c * (range (2 * N + 1)).sup' nonempty_range_add_one (fun n => (a n - b (n / 2)) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      ∫ z, (Φ (2 ^ (ℓ + 1)) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z) -
        Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ (pairAvg z))) ^ 2
          ∂stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ (1 - δ) := by
  obtain ⟨C, hC, hcross⟩ := gbmGrid_cross_sup'_rate r σ s₀ hT hδ
  refine ⟨c * C, mul_nonneg hc hC, fun ℓ => ?_⟩
  have hh : 0 ≤ T / 2 ^ (ℓ + 1) := div_nonneg hT (by positivity)
  have hhT : T / 2 ^ (ℓ + 1) ≤ T := div_le_self hT (one_le_pow₀ (by norm_num))
  have hNT : 2 * ((2 ^ ℓ : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)) ≤ T := by
    rw [mul_assoc, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, ← pow_succ',
      mul_div_cancel₀ _ (by positivity)]
  obtain ⟨hI, hle⟩ := hcross _ (2 ^ ℓ) hh hhT hNT
  rw [show (2 : ℕ) ^ (ℓ + 1) = 2 * 2 ^ ℓ from pow_succ' 2 ℓ,
    ← gridMax_two_mul_div_two_pow_succ T ℓ]
  calc ∫ z, (Φ (2 * 2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z) -
        Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (2 * (T / 2 ^ (ℓ + 1))) s₀ (pairAvg z))) ^ 2
        ∂stdNormalSeq
      ≤ ∫ z, c * (range (2 * 2 ^ ℓ + 1)).sup' nonempty_range_add_one (fun n =>
          (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z n -
            emPath (gbmDrift r) (gbmVol σ) (2 * (T / 2 ^ (ℓ + 1))) s₀ (pairAvg z) (n / 2)) ^ 2)
          ∂stdNormalSeq :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) (hI.const_mul c)
          (Eventually.of_forall fun z => hΦ2 _ _ _)
    _ ≤ c * (C * (T / 2 ^ (ℓ + 1)) ^ (1 - δ)) := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hle hc
    _ = _ := by ring

/-- The grid payoff of the Euler–Maruyama path against that of the exact solution on the same
grid: for every `δ > 0` there is `C` with `E[(Φ_{2^ℓ}(S) − Φ_{2^ℓ}(Ŝ))²] ≤ C h_ℓ^{1−δ}`
(`gbmGrid_err_sup'_rate`; Giles 2015, §5.1, p. 29, l. 1306–1309). -/
lemma gridPayoff_exact_rate (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hΦ1 : ∀ N (a b : ℕ → ℝ), (Φ N a - Φ N b) ^ 2 ≤
      c * (range (N + 1)).sup' nonempty_range_add_one (fun n => (a n - b n) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      ∫ z, (Φ (2 ^ ℓ) (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z) -
        Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z)) ^ 2
          ∂stdNormalSeq ≤ C * (T / 2 ^ ℓ) ^ (1 - δ) := by
  obtain ⟨C, hC, herr⟩ := gbmGrid_err_sup'_rate r σ s₀ hT hδ
  refine ⟨c * C, mul_nonneg hc hC, fun ℓ => ?_⟩
  have hh : 0 ≤ T / 2 ^ ℓ := div_nonneg hT (by positivity)
  have hhT : T / 2 ^ ℓ ≤ T := div_le_self hT (one_le_pow₀ (by norm_num))
  have hNT : ((2 ^ ℓ : ℕ) : ℝ) * (T / 2 ^ ℓ) ≤ T := by
    rw [Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel₀ _ (by positivity)]
  obtain ⟨hI, hle⟩ := herr _ (2 ^ ℓ) hh hhT hNT
  calc _ ≤ ∫ z, c * (range (2 ^ ℓ + 1)).sup' nonempty_range_add_one (fun n =>
          (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z n -
            emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z n) ^ 2) ∂stdNormalSeq :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) (hI.const_mul c)
          (Eventually.of_forall fun z => hΦ1 _ _ _)
    _ ≤ c * (C * (T / 2 ^ ℓ) ^ (1 - δ)) := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hle hc
    _ = _ := by ring

/-- `|E X| ≤ √B` if `E[X²] ≤ B` (Jensen; the bias from the second moment, Giles 2015, §5.1,
p. 29). -/
lemma gridMax_abs_integral_le_sqrt {X : (ℕ → ℝ) → ℝ} (hX : MemLp X 2 stdNormalSeq) {B : ℝ}
    (hB : ∫ z, X z ^ 2 ∂stdNormalSeq ≤ B) : |∫ z, X z ∂stdNormalSeq| ≤ Real.sqrt B := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt ((sq_integral_le_integral_sq_of_memLp hX).trans hB)

/-- The level means are Cauchy at a geometric rate: for every `δ > 0` there is `C` with
`|E[P_{ℓ+1}] − E[P_ℓ]| ≤ C h_{ℓ+1}^{(1−δ)/2}` (by (2.4), `E[P_ℓ] = E[P^c_ℓ]`, and
`gridPayoff_cross_rate`; Giles 2015, §2.1, (2.4), and §5.1). -/
lemma gridPayoff_mean_step (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hΦm : ∀ N, Measurable (Φ N))
    (hΦ1 : ∀ N (a b : ℕ → ℝ), (Φ N a - Φ N b) ^ 2 ≤
      c * (range (N + 1)).sup' nonempty_range_add_one (fun n => (a n - b n) ^ 2))
    (hΦ2 : ∀ N (a b : ℕ → ℝ), (Φ (2 * N) a - Φ N b) ^ 2 ≤
      c * (range (2 * N + 1)).sup' nonempty_range_add_one (fun n => (a n - b (n / 2)) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      |∫ z, Φ (2 ^ (ℓ + 1)) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z)
          ∂stdNormalSeq -
        ∫ z, Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq| ≤
        C * (T / 2 ^ (ℓ + 1)) ^ ((1 - δ) / 2) := by
  obtain ⟨C, hC, hcross⟩ := gridPayoff_cross_rate r σ s₀ hT hc hΦ2 hδ
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun ℓ => ?_⟩
  have hh : ∀ j : ℕ, 0 ≤ T / 2 ^ j := fun j => div_nonneg hT (by positivity)
  have hPf := memLp_gridPayoff_em hc hΦm hΦ1 r σ s₀ (hh (ℓ + 1)) (2 ^ (ℓ + 1))
  have hPc : MemLp (fun z => Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀
      (pairAvg z))) 2 stdNormalSeq :=
    (memLp_gridPayoff_em hc hΦm hΦ1 r σ s₀ (hh ℓ) (2 ^ ℓ)).comp_measurePreserving
      measurePreserving_pairAvg
  have hPm : Measurable fun z => Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z) :=
    (hΦm _).comp (gridMax_measurable_emPath_pi r σ _ s₀)
  have e : ∫ z, Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq =
      ∫ z, Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ (pairAvg z)) ∂stdNormalSeq :=
    (integral_comp_of_measurePreserving measurePreserving_pairAvg hPm.aestronglyMeasurable).symm
  rw [e, ← integral_sub (hPf.integrable one_le_two) (hPc.integrable one_le_two),
    ← gridMax_sqrt_mul_rpow hC (hh (ℓ + 1))]
  exact gridMax_abs_integral_le_sqrt (hPf.sub hPc) (hcross ℓ)

/-- **The level means of an every-step payoff converge** (Giles 2015, §2.1, Theorem 1 (i), and
§5.1): there is `Y` with `E[P_ℓ] → Y` and `E[Φ_{2^ℓ}(S)] → Y` (the payoff of the exact solution
monitored at every step of level `ℓ`), and `|E[P_ℓ] − Y| ≤ C h_ℓ^{(1−δ)/2}` for every
`0 < δ < 1`. -/
lemma gridPayoff_mean_converges (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hΦm : ∀ N, Measurable (Φ N))
    (hΦ1 : ∀ N (a b : ℕ → ℝ), (Φ N a - Φ N b) ^ 2 ≤
      c * (range (N + 1)).sup' nonempty_range_add_one (fun n => (a n - b n) ^ 2))
    (hΦ2 : ∀ N (a b : ℕ → ℝ), (Φ (2 * N) a - Φ N b) ^ 2 ≤
      c * (range (2 * N + 1)).sup' nonempty_range_add_one (fun n => (a n - b (n / 2)) ^ 2)) :
    ∃ Y : ℝ,
      Tendsto (fun ℓ : ℕ => ∫ z, Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z)
        ∂stdNormalSeq) atTop (𝓝 Y) ∧
      Tendsto (fun ℓ : ℕ => ∫ z, Φ (2 ^ ℓ) (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq)
        atTop (𝓝 Y) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
        |∫ z, Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq - Y| ≤
          C * (T / 2 ^ ℓ) ^ ((1 - δ) / 2) := by
  set u : ℕ → ℝ := fun ℓ => ∫ z, Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z)
    ∂stdNormalSeq with hu
  -- geometric steps for every `δ ∈ (0, 1)`
  have hgeo : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 ≤ C ∧
      (2 : ℝ) ^ (-((1 - δ) / 2)) < 1 ∧ 0 ≤ (2 : ℝ) ^ (-((1 - δ) / 2)) ∧
      ∀ ℓ, dist (u ℓ) (u (ℓ + 1)) ≤
        C * T ^ ((1 - δ) / 2) * (2 : ℝ) ^ (-((1 - δ) / 2)) * ((2 : ℝ) ^ (-((1 - δ) / 2))) ^ ℓ :=
    fun δ hδ hδ1 => by
    obtain ⟨C, hC, hstep⟩ := gridPayoff_mean_step r σ s₀ hT hc hΦm hΦ1 hΦ2 hδ
    refine ⟨C, hC, Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith),
      Real.rpow_nonneg (by norm_num) _, fun ℓ => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    refine (hstep ℓ).trans_eq ?_
    rw [gridMax_div_two_pow_rpow hT, pow_succ]
    ring
  obtain ⟨C₀, -, hθ₀, -, hu₀⟩ := hgeo (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ _ hθ₀ hu₀)
  have hrate : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      |u ℓ - Y| ≤ C * (T / 2 ^ ℓ) ^ ((1 - δ) / 2) := fun δ hδ hδ1 => by
    obtain ⟨C, hC, hθ, hθ0, hstep⟩ := hgeo δ hδ hδ1
    set θ := (2 : ℝ) ^ (-((1 - δ) / 2))
    have h1θ : 0 < 1 - θ := by linarith
    refine ⟨C * θ / (1 - θ), by positivity, fun ℓ => ?_⟩
    have h := dist_le_of_le_geometric_of_tendsto _ _ hθ hstep hY ℓ
    rw [Real.dist_eq] at h
    refine h.trans_eq ?_
    rw [gridMax_div_two_pow_rpow hT]
    ring
  refine ⟨Y, hY, ?_, hrate⟩
  -- the exact prices have the same limit
  obtain ⟨C, hC, hex⟩ := gridPayoff_exact_rate r σ s₀ hT hc hΦ1 (δ := 1 / 2) (by norm_num)
  set θ := (2 : ℝ) ^ (-((1 - 1 / 2 : ℝ) / 2))
  have hθ : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg (by norm_num) _
  have hdiff : ∀ ℓ : ℕ, ‖∫ z, Φ (2 ^ ℓ) (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq - u ℓ‖ ≤
      Real.sqrt C * T ^ ((1 - 1 / 2 : ℝ) / 2) * θ ^ ℓ := fun ℓ => by
    have hh : 0 ≤ T / 2 ^ ℓ := div_nonneg hT (by positivity)
    have hQ := memLp_gridPayoff_exact hc hΦm hΦ1 r σ (T / 2 ^ ℓ) s₀ (2 ^ ℓ)
    have hP := memLp_gridPayoff_em hc hΦm hΦ1 r σ s₀ hh (2 ^ ℓ)
    rw [Real.norm_eq_abs, hu, ← integral_sub (hQ.integrable one_le_two)
      (hP.integrable one_le_two)]
    refine (gridMax_abs_integral_le_sqrt (hQ.sub hP) (hex ℓ)).trans_eq ?_
    rw [gridMax_sqrt_mul_rpow hC hh, gridMax_div_two_pow_rpow hT]
    ring
  have h0 : Tendsto (fun ℓ : ℕ => ∫ z, Φ (2 ^ ℓ) (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z)
      ∂stdNormalSeq - u ℓ) atTop (𝓝 0) := by
    refine squeeze_zero_norm hdiff ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ).const_mul
      (Real.sqrt C * T ^ ((1 - 1 / 2 : ℝ) / 2))
  simpa using hY.add h0

/-- **Theorem 1 for an every-step payoff of GBM with Euler–Maruyama** (Giles 2015, §2.1,
Theorem 1, pp. 6–7, and §5.1–§5.2): with `α = (1 − δ)/2`, `β = 1 − δ`, `γ = 1` and
`δ = η/(2 + η)`, the multilevel estimator with target `Y = lim_ℓ E[Φ_{2^ℓ}(S)]` reaches mean square
error `< ε²` at cost `O(ε^{−2−η})` (`em_mlmc_theorem1`). -/
lemma gridPayoff_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hΦm : ∀ N, Measurable (Φ N))
    (hΦ1 : ∀ N (a b : ℕ → ℝ), (Φ N a - Φ N b) ^ 2 ≤
      c * (range (N + 1)).sup' nonempty_range_add_one (fun n => (a n - b n) ^ 2))
    (hΦ2 : ∀ N (a b : ℕ → ℝ), (Φ (2 * N) a - Φ N b) ^ 2 ≤
      c * (range (2 * N + 1)).sup' nonempty_range_add_one (fun n => (a n - b (n / 2)) ^ 2)) :
    ∃ Y : ℝ,
      Tendsto (fun ℓ : ℕ => ∫ z, Φ (2 ^ ℓ) (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq)
        atTop (𝓝 Y) ∧
      ∀ η : ℝ, 0 < η → ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1),
              blockMean (fineCoarseDiff (emFine (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ)))
                (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ)))) (fun p x => x p) ℓ
                (N ℓ) x - Y) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 - η) := by
  obtain ⟨Y, -, hv, hrate⟩ := gridPayoff_mean_converges r σ s₀ hT hc hΦm hΦ1 hΦ2
  refine ⟨Y, hv, fun η hη => ?_⟩
  set δ := η / (2 + η) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by rw [hδdef, div_lt_one (by linarith)]; linarith
  obtain ⟨C₁, hC₁, hbias⟩ := hrate δ hδ0 hδ1
  obtain ⟨C₂, hC₂, hcross⟩ := gridPayoff_cross_rate r σ s₀ hT hc hΦ2 hδ0
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hh : ∀ j : ℕ, 0 ≤ T / 2 ^ j := fun j => div_nonneg hT (by positivity)
  have hPfm : ∀ ℓ, Measurable (emFine (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ)) ℓ) :=
    fun ℓ => (hΦm _).comp (gridMax_measurable_emPath_pi r σ _ s₀)
  have hPf : ∀ ℓ, MemLp (emFine (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ)) ℓ) 2
      stdNormalSeq := fun ℓ => memLp_gridPayoff_em hc hΦm hΦ1 r σ s₀ (hh ℓ) (2 ^ ℓ)
  -- (i): the weak rate `α = (1 − δ)/2` against the limit `Y`
  have hTa : 0 ≤ T ^ ((1 - δ) / 2) := Real.rpow_nonneg hT _
  have hc₁ : 0 < C₁ * T ^ ((1 - δ) / 2) + 1 := by positivity
  have h_i : ∀ ℓ : ℕ, |∫ z, emFine (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ)) ℓ z -
      (fun _ => Y) z ∂stdNormalSeq| ≤
      (C₁ * T ^ ((1 - δ) / 2) + 1) * (2 : ℝ) ^ (-((1 - δ) / 2 * (ℓ : ℝ))) := fun ℓ => by
    rw [integral_sub ((hPf ℓ).integrable one_le_two) (integrable_const Y), integral_const,
      probReal_univ, one_smul]
    have hb := hbias ℓ
    rw [gridMax_div_two_pow_rpow hT, gridMax_two_rpow_neg_pow] at hb
    have hpos : 0 ≤ (2 : ℝ) ^ (-((1 - δ) / 2 * (ℓ : ℝ))) := by positivity
    calc _ ≤ C₁ * (T ^ ((1 - δ) / 2) * (2 : ℝ) ^ (-((1 - δ) / 2 * (ℓ : ℝ)))) := hb
      _ ≤ _ := by nlinarith
  -- (iii): the variance rate `β = 1 − δ`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance
      (emFine (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ)) 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by
    rw [hV₀]
    exact variance_nonneg _ _
  have hTb : 0 ≤ T ^ (1 - δ) := Real.rpow_nonneg hT _
  have hc₂ : 0 < V₀ + C₂ * T ^ (1 - δ) + 1 := by positivity
  have h_iii : ∀ ℓ, variance (fineCoarseDiff
      (emFine (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ)))
      (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ))) ℓ) stdNormalSeq ≤
      (V₀ + C₂ * T ^ (1 - δ) + 1) * (2 : ℝ) ^ (-((1 - δ) * (ℓ : ℝ))) := by
    intro ℓ
    have hpos : 0 ≤ (2 : ℝ) ^ (-((1 - δ) * (ℓ : ℝ))) := by positivity
    cases ℓ with
    | zero =>
      simp only [fineCoarseDiff, CharP.cast_eq_zero, mul_zero, neg_zero, Real.rpow_zero,
        mul_one]
      rw [← hV₀]
      linarith [mul_nonneg hC₂ hTb]
    | succ ℓ =>
      have e : fineCoarseDiff (emFine (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ)))
          (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ))) (ℓ + 1) =
          fun z => Φ (2 ^ (ℓ + 1)) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z) -
            Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ (pairAvg z)) := by
        funext z
        simp only [fineCoarseDiff, emCoarse_eq]
        rfl
      rw [e]
      have hm : AEStronglyMeasurable (fun z =>
          Φ (2 ^ (ℓ + 1)) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z) -
            Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ (pairAvg z)))
          stdNormalSeq :=
        ((hPfm (ℓ + 1)).sub ((hPfm ℓ).comp measurePreserving_pairAvg.measurable))
          |>.aestronglyMeasurable
      refine (variance_le_expectation_sq hm).trans ?_
      simp only [Pi.pow_apply]
      have hb := hcross ℓ
      rw [gridMax_div_two_pow_rpow hT, gridMax_two_rpow_neg_pow] at hb
      refine hb.trans ?_
      nlinarith [mul_nonneg hV₀0 hpos]
  -- (iv): a level-`ℓ` sample costs `2^ℓ`
  have h_iv : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ 1 * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, one_mul, Real.rpow_natCast]
  have hαβγ : min (1 - δ) 1 / 2 ≤ (1 - δ) / 2 := by
    rw [min_eq_left (by linarith)]
  obtain ⟨c₄, hc₄, h⟩ := em_mlmc_theorem1
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq)
    (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => Φ (2 ^ ℓ)) (fun _ => Y)
    (fun p x => x p) (fun ℓ _ _ => (2 : ℝ) ^ ℓ) (fun ℓ => (2 : ℝ) ^ ℓ) (α := (1 - δ) / 2)
    (β := 1 - δ) (γ := 1) (by linarith) (by linarith) one_pos hc₁ hc₂ one_pos hαβγ hω hind
    (integrable_const Y) hPfm hPf (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, ?_, ?_⟩
  · simpa only [integral_const, probReal_univ, one_smul] using hmse
  · simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
      probReal_univ, one_smul] at hcost
    rw [complexityBound_of_gt (by linarith) ε] at hcost
    have hexp : -2 - (1 - (1 - δ)) / ((1 - δ) / 2) = -2 - η := by
      rw [hδdef]
      field_simp
      ring
    rw [hexp] at hcost
    exact hcost

/-- **The correction variance with every-step monitoring** (Giles 2015, §5.2, p. 38): for every
`δ > 0` there is `C` with `V[Φ_{2^{ℓ+1}}(Ŝ^f) − Φ_{2^ℓ}(Ŝ^c)] ≤ C h_{ℓ+1}^{1−δ}`
(`gridPayoff_cross_rate`). -/
lemma gridPayoff_variance_rate (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hΦm : ∀ N, Measurable (Φ N))
    (hΦ2 : ∀ N (a b : ℕ → ℝ), (Φ (2 * N) a - Φ N b) ^ 2 ≤
      c * (range (2 * N + 1)).sup' nonempty_range_add_one (fun n => (a n - b (n / 2)) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      variance (fun z => Φ (2 ^ (ℓ + 1)) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z) -
        Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ (pairAvg z))) stdNormalSeq ≤
        C * (T / 2 ^ (ℓ + 1)) ^ (1 - δ) := by
  obtain ⟨C, hC, hcross⟩ := gridPayoff_cross_rate r σ s₀ hT hc hΦ2 hδ
  refine ⟨C, hC, fun ℓ => ?_⟩
  have hm : AEStronglyMeasurable (fun z =>
      Φ (2 ^ (ℓ + 1)) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z) -
        Φ (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ (pairAvg z))) stdNormalSeq :=
    (((hΦm _).comp (gridMax_measurable_emPath_pi r σ _ s₀)).sub
      (((hΦm _).comp (gridMax_measurable_emPath_pi r σ _ s₀)).comp
        measurePreserving_pairAvg.measurable)).aestronglyMeasurable
  refine (variance_le_expectation_sq hm).trans ?_
  simp only [Pi.pow_apply]
  exact hcross ℓ

end Levels

/-! ### The lookback options monitored at every time step -/

/-- The lookback payoff on the maximum is measurable for a continuous `g` (Giles 2015, §5.1). -/
lemma gridMax_measurable_lookbackPayoff {g : ℝ → ℝ} (hg : Continuous g) (N : ℕ) :
    Measurable (lookbackPayoff g N) :=
  hg.measurable.comp (gridMax_measurable_range_sup' N)

/-- The lookback payoff on the minimum is measurable for a continuous `g` (Giles 2015, §5.1). -/
lemma gridMax_measurable_lookbackMinPayoff {g : ℝ → ℝ} (hg : Continuous g) (N : ℕ) :
    Measurable (lookbackMinPayoff g N) :=
  hg.measurable.comp (gridMax_measurable_range_inf' N)

/-- The floating-strike lookback payoff is measurable for a continuous `g` (Giles 2015,
§5.1). -/
lemma gridMax_measurable_floatLookbackPayoff {g : ℝ → ℝ} (hg : Continuous g) (N : ℕ) :
    Measurable (floatLookbackPayoff g N) :=
  hg.measurable.comp ((measurable_pi_apply N).sub (gridMax_measurable_range_inf' N))

/-- **The correction variance of the lookback option on the maximum monitored at every time step,
Euler–Maruyama** (Giles 2015, Table 5.2, p. 33, l. 1429, row "lookback", Euler–Maruyama: "`O(h)`";
§5.2, p. 38, l. 1653–1659: "A multilevel estimator based directly on the minimum (or maximum) of the
values at the discrete timesteps … results in an `O(h_ℓ)` variance for lookback options which are a
Lipschitz function of the minimum (or maximum)").  For GBM, `T ≥ 0`, a `K`-Lipschitz `g` and every
`δ > 0` there is `C` such that for every level `ℓ`, the payoff of the Euler–Maruyama path with
`2^{ℓ+1}` steps of size `h_{ℓ+1} = T 2^{−(ℓ+1)}`, monitored at all its `2^{ℓ+1} + 1` times, minus
the same payoff of the coarse path with `2^ℓ` steps driven by the summed increments
`(Z_{2k} + Z_{2k+1})/√2`, monitored at all its times, has variance at most `C h_{ℓ+1}^{1−δ}`.  The
fine and the coarse payoffs use different sets of times; the difference splits into the uniform
strong errors of both paths and the monitoring gap of the exact solution
(`gbm_grid_monitoring_gap_rate`).  **Deviation**: the paper's `O(h)` is reached up to the loss `δ`,
which comes from the monitoring gap (the uniform strong errors are `O(h)`,
`gbm_em_grid_max_error_sharp`); a Monte Carlo check (`r = 0.05`, `σ = 0.2`, `T = 1`, `S_0 = 1`,
`g(x) = x`) gives `V_ℓ/h_ℓ ≈ 0.004–0.008` for `h = 2^{−2}, …, 2^{−9}`, i.e. `O(h)`. -/
theorem gbm_em_gridLookback_variance_rate (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      variance (fun z =>
        lookbackPayoff g (2 ^ (ℓ + 1)) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z) -
        lookbackPayoff g (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ (pairAvg z)))
          stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ (1 - δ) :=
  gridPayoff_variance_rate r σ s₀ hT (sq_nonneg K)
    (gridMax_measurable_lookbackPayoff (continuous_of_abs_sub_le hg).2)
    (lookbackPayoff_cross_sq_le hg) hδ

/-- **The correction variance of the lookback option on the minimum monitored at every time step,
Euler–Maruyama** (Giles 2015, Table 5.2, p. 33, l. 1429; §5.2, p. 38, l. 1653–1659, as in
`gbm_em_gridLookback_variance_rate`).  The payoff is `g(min_{0≤n≤2^ℓ} Ŝ_n)`
(`lookbackMinPayoff`).  For GBM, `T ≥ 0`, a `K`-Lipschitz `g` and every `δ > 0`
there is `C` such that for every level `ℓ`, the payoff of the Euler–Maruyama path with `2^{ℓ+1}`
steps of size `h_{ℓ+1} = T 2^{−(ℓ+1)}`, monitored at all its `2^{ℓ+1} + 1` times, minus the same
payoff of the coarse path with `2^ℓ` steps driven by the summed increments
`(Z_{2k} + Z_{2k+1})/√2`, monitored at all its times, has variance at most `C h_{ℓ+1}^{1−δ}`.  The
fine and the coarse payoffs use different sets of times; the difference splits into the uniform
strong errors of both paths and the monitoring gap of the exact solution
(`gbm_grid_monitoring_gap_rate`).  **Deviation**: the paper's `O(h)` is reached up to the loss
`δ`, which comes from the monitoring gap (the uniform strong errors are `O(h)`,
`gbm_em_grid_max_error_sharp`); a Monte Carlo check (`r = 0.05`, `σ = 0.2`, `T = 1`, `S_0 = 1`,
`g(x) = x`) gives `V_ℓ/h_ℓ ≈ 0.004–0.008` for `h = 2^{−2}, …, 2^{−9}`, i.e. `O(h)`. -/
theorem gbm_em_gridLookbackMin_variance_rate (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      variance (fun z =>
        lookbackMinPayoff g (2 ^ (ℓ + 1)) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z) -
        lookbackMinPayoff g (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ (pairAvg z)))
          stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ (1 - δ) :=
  gridPayoff_variance_rate r σ s₀ hT (sq_nonneg K)
    (gridMax_measurable_lookbackMinPayoff (continuous_of_abs_sub_le hg).2)
    (lookbackMinPayoff_cross_sq_le hg) hδ

/-- **The correction variance of the floating-strike lookback option monitored at every time step,
Euler–Maruyama** (Giles 2015, Table 5.2, p. 33, l. 1429; §5.2, p. 38, l. 1653–1659).  The payoff is
`g(Ŝ_{2^ℓ} − min_{0≤n≤2^ℓ} Ŝ_n)` (`floatLookbackPayoff`, e.g. the call `e^{−rT}(S_T − min S)` with
`g(x) = e^{−rT} x`).  For GBM, `T ≥ 0`, a `K`-Lipschitz `g` and every `δ > 0`
there is `C` such that for every level `ℓ`, the payoff of the Euler–Maruyama path with `2^{ℓ+1}`
steps of size `h_{ℓ+1} = T 2^{−(ℓ+1)}`, monitored at all its `2^{ℓ+1} + 1` times, minus the same
payoff of the coarse path with `2^ℓ` steps driven by the summed increments
`(Z_{2k} + Z_{2k+1})/√2`, monitored at all its times, has variance at most `C h_{ℓ+1}^{1−δ}`.  The
fine and the coarse payoffs use different sets of times; the difference splits into the uniform
strong errors of both paths and the monitoring gap of the exact solution
(`gbm_grid_monitoring_gap_rate`).  **Deviation**: the paper's `O(h)` is reached up to the loss
`δ`, which comes from the monitoring gap (the uniform strong errors are `O(h)`,
`gbm_em_grid_max_error_sharp`); a Monte Carlo check (`r = 0.05`, `σ = 0.2`, `T = 1`, `S_0 = 1`,
`g(x) = x`) gives `V_ℓ/h_ℓ ≈ 0.004–0.008` for `h = 2^{−2}, …, 2^{−9}`, i.e. `O(h)`. -/
theorem gbm_em_gridFloatLookback_variance_rate (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      variance (fun z =>
        floatLookbackPayoff g (2 ^ (ℓ + 1))
          (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ (ℓ + 1)) s₀ z) -
        floatLookbackPayoff g (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ (pairAvg z)))
          stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ (1 - δ) :=
  gridPayoff_variance_rate r σ s₀ hT (by positivity)
    (gridMax_measurable_floatLookbackPayoff (continuous_of_abs_sub_le hg).2)
    (floatLookbackPayoff_cross_sq_le hg) hδ

/-- **The level means of the lookback option on the maximum monitored at every step converge**
(Giles 2015, §2.1, Theorem 1 (i), p. 6; §5.1, p. 29, and §5.2, p. 38, l. 1650–1653: lookback options
"depend on the minimum (or maximum) values of the underlying asset during the whole simulation
interval `[0, T]`").  There is `Y` such that the level means `E[P_ℓ]` of the
Euler–Maruyama payoffs with `2^ℓ` steps of size `h_ℓ = T 2^{−ℓ}`, monitored at every step, converge
to `Y`, the payoffs of the exact solution monitored at the same `2^ℓ + 1` times have expectations
converging to the same `Y`, and `|E[P_ℓ] − Y| ≤ C h_ℓ^{(1−δ)/2}` for every `0 < δ < 1`
(the weak rate `α = (1 − δ)/2`).  The limit is the continuously monitored price
`E[g(max_{0≤t≤T} S_t)]`, since the exact paths are continuous and the dyadic grids exhaust a dense
set; this identification needs Brownian paths and is **not proved** here.  **Weak order**: `α = 1/2`
is the true order of a maximum monitored only at the grid times (e.g. for `g(x) = x`), so the
proved `α = (1 − δ)/2` is sharp up to `δ`: `E[max_{[0,T]} S − max_n S_{t_n}] ≈ 0.5826 σ E[max S]
h^{1/2}` (Asmussen, Glynn and Pitman 1995; Broadie, Glasserman and Kou 1997).  For `r = σ²/2`,
`T = 1`, `σ > 0` the bias of `g(x) = x` is at least `σ S_0 E[max_{[0,1]} W − max_{n≤N} W_{n/N}]`,
and Spitzer's identity gives `E[max_{n≤N} W_{n/N}] = (2πN)^{−1/2} ∑_{k≤N} k^{−1/2}`, so this is
`σ S_0 ((2/π)^{1/2} − (2πN)^{−1/2} ∑_{k≤N} k^{−1/2}) ∼ 0.5826 σ S_0 N^{−1/2}`.  A Monte Carlo check
(`r = 0.05`, `σ = 0.2`, `T = S_0 = 1`, 40000 paths, the exact `Y = 1.2015037`) gives
`(Y − E[P_ℓ])/h_ℓ^{1/2} ≈ 0.115, 0.127, 0.137` for `h_ℓ = 1/4, 1/16, 1/64`, while
`(Y − E[P_ℓ])/h_ℓ` grows.  The paper's `α = 1` (§5.1, p. 30, the weak order of Euler–Maruyama in
general) therefore does not hold here.  Since `α = 1/2 ≥ min(β, γ)/2`, the paper's
`O(ε⁻²(log ε)²)` (p. 30) would still follow from its `β = 1`. -/
theorem gbm_em_gridLookback_mean_converges (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ Y : ℝ,
      Tendsto (fun ℓ : ℕ => ∫ z, lookbackPayoff g (2 ^ ℓ)
        (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq) atTop (𝓝 Y) ∧
      Tendsto (fun ℓ : ℕ => ∫ z, lookbackPayoff g (2 ^ ℓ) (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z)
        ∂stdNormalSeq) atTop (𝓝 Y) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
        |∫ z, lookbackPayoff g (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z)
          ∂stdNormalSeq - Y| ≤ C * (T / 2 ^ ℓ) ^ ((1 - δ) / 2) :=
  gridPayoff_mean_converges r σ s₀ hT (sq_nonneg K)
    (gridMax_measurable_lookbackPayoff (continuous_of_abs_sub_le hg).2)
    (lookbackPayoff_grid_sq_le hg)
    (lookbackPayoff_cross_sq_le hg)

/-- **The level means of the lookback option on the minimum monitored at every step converge**
(Giles 2015, §2.1, Theorem 1 (i); §5.2, p. 38, l. 1650–1653, as in
`gbm_em_gridLookback_mean_converges`).  There is `Y` such that the level means `E[P_ℓ]` of the
Euler–Maruyama payoffs with `2^ℓ` steps of size `h_ℓ = T 2^{−ℓ}`, monitored at every step, converge
to `Y`, the payoffs of the exact solution monitored at the same `2^ℓ + 1` times have expectations
converging to the same `Y`, and `|E[P_ℓ] − Y| ≤ C h_ℓ^{(1−δ)/2}` for every `0 < δ < 1`
(the weak rate `α = (1 − δ)/2`).  The limit is the continuously monitored price
`E[g(min_{0≤t≤T} S_t)]`, since the exact paths are continuous and the dyadic grids exhaust a dense
set; this identification needs Brownian paths and is **not proved** here.  **Weak order**: as for
the maximum (`gbm_em_gridLookback_mean_converges`), `α = 1/2` is the true order of a minimum
monitored only at the grid times (`E[min_n S_{t_n} − min_{[0,T]} S] ≈ 0.5826 σ E[min S] h^{1/2}`,
Broadie, Glasserman and Kou 1997), so the proved `α = (1 − δ)/2` is sharp up to `δ` and the paper's
`α = 1` (§5.1, p. 30) does not hold here; `α = 1/2 ≥ min(β, γ)/2` would still give the paper's
`O(ε⁻²(log ε)²)` with `β = 1`. -/
theorem gbm_em_gridLookbackMin_mean_converges (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ Y : ℝ,
      Tendsto (fun ℓ : ℕ => ∫ z, lookbackMinPayoff g (2 ^ ℓ)
        (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq) atTop (𝓝 Y) ∧
      Tendsto (fun ℓ : ℕ => ∫ z, lookbackMinPayoff g (2 ^ ℓ) (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z)
        ∂stdNormalSeq) atTop (𝓝 Y) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
        |∫ z, lookbackMinPayoff g (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z)
          ∂stdNormalSeq - Y| ≤ C * (T / 2 ^ ℓ) ^ ((1 - δ) / 2) :=
  gridPayoff_mean_converges r σ s₀ hT (sq_nonneg K)
    (gridMax_measurable_lookbackMinPayoff (continuous_of_abs_sub_le hg).2)
    (lookbackMinPayoff_grid_sq_le hg) (lookbackMinPayoff_cross_sq_le hg)

/-- **The level means of the floating-strike lookback option monitored at every step converge**
(Giles 2015, §2.1, Theorem 1 (i); §5.2, p. 38, l. 1650–1653).  There is `Y` such that the level
means `E[P_ℓ]` of the Euler–Maruyama payoffs with `2^ℓ` steps of size `h_ℓ = T 2^{−ℓ}`, monitored at
every step, converge to `Y`, the payoffs of the exact solution monitored at the same `2^ℓ + 1` times
have expectations converging to the same `Y`, and `|E[P_ℓ] − Y| ≤ C h_ℓ^{(1−δ)/2}` for every
`0 < δ < 1` (the weak rate `α = (1 − δ)/2`).  The limit is the continuously monitored price
`E[g(S_T − min_{0≤t≤T} S_t)]`, since the exact paths are continuous and the dyadic grids exhaust a
dense set; this identification needs Brownian paths and is **not proved** here.  **Weak order**: as
for the maximum (`gbm_em_gridLookback_mean_converges`), `α = 1/2` is the true order of a minimum
monitored only at the grid times (`E[min_n S_{t_n} − min_{[0,T]} S] ≈ 0.5826 σ E[min S] h^{1/2}`,
Broadie, Glasserman and Kou 1997), so the proved `α = (1 − δ)/2` is sharp up to `δ` and the paper's
`α = 1` (§5.1, p. 30) does not hold here; `α = 1/2 ≥ min(β, γ)/2` would still give the paper's
`O(ε⁻²(log ε)²)` with `β = 1`. -/
theorem gbm_em_gridFloatLookback_mean_converges (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ Y : ℝ,
      Tendsto (fun ℓ : ℕ => ∫ z, floatLookbackPayoff g (2 ^ ℓ)
        (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq) atTop (𝓝 Y) ∧
      Tendsto (fun ℓ : ℕ => ∫ z, floatLookbackPayoff g (2 ^ ℓ)
        (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq) atTop (𝓝 Y) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
        |∫ z, floatLookbackPayoff g (2 ^ ℓ) (emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z)
          ∂stdNormalSeq - Y| ≤ C * (T / 2 ^ ℓ) ^ ((1 - δ) / 2) :=
  gridPayoff_mean_converges r σ s₀ hT (by positivity)
    (gridMax_measurable_floatLookbackPayoff (continuous_of_abs_sub_le hg).2)
    (floatLookbackPayoff_grid_sq_le hg) (floatLookbackPayoff_cross_sq_le hg)

/-- **Theorem 1 for the Euler–Maruyama lookback option on the maximum monitored at every time step**
(Giles 2015, §2.1, Theorem 1, pp. 6–7; §5.1, p. 30, l. 1319–1321: "Theorem 1 gives the complexity to
achieve a root-mean-square error of `ε` to be `O(ε⁻²(log ε)²)`"; Table 5.2, p. 33, row "lookback";
§5.2, p. 38, l. 1653–1659).  For GBM, `T ≥ 0` and a `K`-Lipschitz `g` there is `Y`, the limit of the
expectations of the payoff of the exact solution monitored at every step of level `ℓ` (see
`gbm_em_gridLookback_mean_converges`; informally `Y = E[g(max_{0≤t≤T} S_t)]`), such that for every
`η > 0` there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which
the multilevel estimator `∑_{ℓ≤L} N_ℓ⁻¹ ∑_n (P^f_ℓ − P^c_{ℓ−1})(ω^{(ℓ,n)})` (level `ℓ`: `2^ℓ`
Euler–Maruyama steps, the payoff of all `2^ℓ + 1` values; the coarse path driven by the summed
increments; independent samples) has mean square error `< ε²` about `Y` and cost
`∑_ℓ N_ℓ 2^ℓ ≤ c₄ ε^{−2−η}`.  The rates are `α = (1 − δ)/2`, `β = 1 − δ`, `γ = 1` with
`δ = η/(2 + η)`, so `(γ − β)/α = η`.  **Deviation**: the paper's `β = 1` (Table 5.2) would give
`O(ε⁻²(log ε)²)`, also with the true weak order `α = 1/2` of the discretely monitored payoff
(`α ≥ min(β, γ)/2`; the paper's `α = 1`, p. 30, does not hold here, see
`gbm_em_gridLookback_mean_converges`); the loss comes from the monitoring gap
(`gbm_grid_monitoring_gap_rate`).  The Milstein scheme does not help here, since the monitoring gap
of the exact solution is already `O(h^{1/2})` in root mean square; the paper's Milstein lookback
estimator (§5.2, pp. 38–39, `β = 2`) uses the Brownian-bridge interpolant of Giles (2008a) within
each step, which is not formalised. -/
theorem gbm_em_gridLookback_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ Y : ℝ,
      Tendsto (fun ℓ : ℕ => ∫ z, lookbackPayoff g (2 ^ ℓ) (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z)
        ∂stdNormalSeq) atTop (𝓝 Y) ∧
      ∀ η : ℝ, 0 < η → ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1),
              blockMean (fineCoarseDiff
                (emFine (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => lookbackPayoff g (2 ^ ℓ)))
                (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => lookbackPayoff g (2 ^ ℓ))))
                (fun p x => x p) ℓ (N ℓ) x - Y) ^ 2
              ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 - η) :=
  gridPayoff_theorem1 r σ s₀ hT (sq_nonneg K)
    (gridMax_measurable_lookbackPayoff (continuous_of_abs_sub_le hg).2)
    (lookbackPayoff_grid_sq_le hg)
    (lookbackPayoff_cross_sq_le hg)

/-- **Theorem 1 for the Euler–Maruyama lookback option on the minimum monitored at every time step**
(Giles 2015, §2.1, Theorem 1; Table 5.2, p. 33; §5.2, p. 38, l. 1653–1659, as in
`gbm_em_gridLookback_theorem1`).  The payoff is `g(min_n Ŝ_n)` (`lookbackMinPayoff`).  For GBM,
`T ≥ 0` and a `K`-Lipschitz `g` there is `Y`, the limit of the expectations of the payoff of the
exact solution monitored at every step of level `ℓ` (see `gbm_em_gridLookbackMin_mean_converges`;
informally `Y = E[g(min_{0≤t≤T} S_t)]`), such that for every `η > 0` there is `c₄ > 0` such that
for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the multilevel estimator
`∑_{ℓ≤L} N_ℓ⁻¹ ∑_n (P^f_ℓ − P^c_{ℓ−1})(ω^{(ℓ,n)})` (level `ℓ`: `2^ℓ` Euler–Maruyama steps, the
payoff of all `2^ℓ + 1` values; the coarse path driven by the summed increments; independent
samples) has mean square error `< ε²` about `Y` and cost `∑_ℓ N_ℓ 2^ℓ ≤ c₄ ε^{−2−η}`.  The rates are
`α = (1 − δ)/2`, `β = 1 − δ`, `γ = 1` with `δ = η/(2 + η)`, so `(γ − β)/α = η`.  **Deviation**: the
paper's `β = 1` (Table 5.2) would give `O(ε⁻²(log ε)²)`, also with the true weak order `α = 1/2`
of the discretely monitored payoff (`α ≥ min(β, γ)/2`; the paper's `α = 1`, p. 30, does not hold
here, see `gbm_em_gridLookbackMin_mean_converges`); the loss comes from the monitoring gap
(`gbm_grid_monitoring_gap_rate`).  The Milstein scheme does not help here, since the monitoring gap
of the exact solution is already `O(h^{1/2})` in root mean square; the paper's Milstein lookback
estimator (§5.2, pp. 38–39, `β = 2`) uses the Brownian-bridge interpolant of Giles (2008a) within
each step, which is not formalised. -/
theorem gbm_em_gridLookbackMin_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ Y : ℝ,
      Tendsto (fun ℓ : ℕ => ∫ z, lookbackMinPayoff g (2 ^ ℓ) (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z)
        ∂stdNormalSeq) atTop (𝓝 Y) ∧
      ∀ η : ℝ, 0 < η → ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1),
              blockMean (fineCoarseDiff
                (emFine (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => lookbackMinPayoff g (2 ^ ℓ)))
                (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => lookbackMinPayoff g (2 ^ ℓ))))
                (fun p x => x p) ℓ (N ℓ) x - Y) ^ 2
              ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 - η) :=
  gridPayoff_theorem1 r σ s₀ hT (sq_nonneg K)
    (gridMax_measurable_lookbackMinPayoff (continuous_of_abs_sub_le hg).2)
    (lookbackMinPayoff_grid_sq_le hg) (lookbackMinPayoff_cross_sq_le hg)

/-- **Theorem 1 for the Euler–Maruyama floating-strike lookback option monitored at every time
step** (Giles 2015, §2.1, Theorem 1; Table 5.2, p. 33; §5.2, p. 38, l. 1653–1659).  The payoff is
`g(Ŝ_{2^ℓ} − min_n Ŝ_n)` (`floatLookbackPayoff`).  For GBM, `T ≥ 0` and a `K`-Lipschitz `g` there is
`Y`, the limit of the expectations of the payoff of the exact solution monitored at every step of
level `ℓ` (see `gbm_em_gridFloatLookback_mean_converges`; informally
`Y = E[g(S_T − min_{0≤t≤T} S_t)]`), such that for every `η > 0` there is `c₄ > 0` such that for
every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the multilevel estimator
`∑_{ℓ≤L} N_ℓ⁻¹ ∑_n (P^f_ℓ − P^c_{ℓ−1})(ω^{(ℓ,n)})` (level `ℓ`: `2^ℓ` Euler–Maruyama steps, the
payoff of all `2^ℓ + 1` values; the coarse path driven by the summed increments; independent
samples) has mean square error `< ε²` about `Y` and cost `∑_ℓ N_ℓ 2^ℓ ≤ c₄ ε^{−2−η}`.  The rates are
`α = (1 − δ)/2`, `β = 1 − δ`, `γ = 1` with `δ = η/(2 + η)`, so `(γ − β)/α = η`.  **Deviation**: the
paper's `β = 1` (Table 5.2) would give `O(ε⁻²(log ε)²)`, also with the true weak order `α = 1/2`
of the discretely monitored payoff (`α ≥ min(β, γ)/2`; the paper's `α = 1`, p. 30, does not hold
here, see `gbm_em_gridFloatLookback_mean_converges`); the loss comes from the monitoring gap
(`gbm_grid_monitoring_gap_rate`).  The Milstein scheme does not help here, since the monitoring gap
of the exact solution is already `O(h^{1/2})` in root mean square; the paper's Milstein lookback
estimator (§5.2, pp. 38–39, `β = 2`) uses the Brownian-bridge interpolant of Giles (2008a) within
each step, which is not formalised. -/
theorem gbm_em_gridFloatLookback_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ Y : ℝ,
      Tendsto (fun ℓ : ℕ => ∫ z, floatLookbackPayoff g (2 ^ ℓ)
        (gbmGridExact r σ (T / 2 ^ ℓ) s₀ z) ∂stdNormalSeq) atTop (𝓝 Y) ∧
      ∀ η : ℝ, 0 < η → ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1),
              blockMean (fineCoarseDiff
                (emFine (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => floatLookbackPayoff g (2 ^ ℓ)))
                (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (fun ℓ => floatLookbackPayoff g (2 ^ ℓ))))
                (fun p x => x p) ℓ (N ℓ) x - Y) ^ 2
              ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 - η) :=
  gridPayoff_theorem1 r σ s₀ hT (by positivity)
    (gridMax_measurable_floatLookbackPayoff (continuous_of_abs_sub_le hg).2)
    (floatLookbackPayoff_grid_sq_le hg) (floatLookbackPayoff_cross_sq_le hg)

end MLMC
