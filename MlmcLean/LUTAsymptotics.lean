import MlmcLean.LUTLimits
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The lookup-table errors as `d → ∞`: limits and rates (Haas–Giles 2025, §3.4)

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), §3.3 (method 3, (18)–(19)) and §3.4 "Comparison of the three
inversion methods", p. 7: "as `d` tends to infinity, the uniform intervals give `MSE → 0` and the
dyadic intervals give `MSE → C`, for some positive constant `C`. The latter is because with our
simple dyadic segmentation, when `d` increases by 1 the MSE is reduced only in the interval closest
to 0, so the error due to the other intervals remains the same", and "both method 1 and 2 have
their MSE divided by 2 each time `d` increases by 1. This was theoretically expected for method 1".

This file completes `MlmcLean/LUTLimits.lean` (`MSE → 0` for method 1, `MSE ≥ c > 0` for
method 3).  As there, `f : ℝ → ℝ` stands for `Φ⁻¹`, which Mathlib does not define; every property
of `Φ⁻¹` used below is a hypothesis on `f`, and each was checked numerically for `Φ⁻¹` (mpmath).
`I_j = [u_j, u_{j+1}]`, `u_j = 2^{−d} j`, are the uniform cells and `Z_j` the LUT values (15).

**Method 3: the MSE converges to a positive constant (H3-25).**  On `[0, ½]` the cells are grouped
into the dyadic intervals `I'_1 = {0, 1}` and `I'_i = [2^{i−1}, 2^i)`, `2 ≤ i ≤ d − 1`
(`dyadicGroup`: the paper's `[[2^{i−1}, 2^i − 1]]`, with `j = 0` joined to `I'_1`, so that the LUT
has `d − 1` entries and "for the first two dyadic intervals there are only two points in each").  On
each `I'_i` the values `Z̄_j = a + b j` are the least-squares fit (19) to the `Z_j` (`lsqFit`,
`sum_sq_lsqFit_le`), and on `[½, 1]` the sign bit gives `−Z̄` of the mirrored cell (`method3Value`).
* `tendsto_method3MSE`, `method3Limit_pos`, `exists_tendsto_method3MSE`: if `f`, `f²` are
  integrable on `[0, 1]` and `f(1 − u) = −f(u)`, the MSE of method 3 converges to
  `C = 2 ∑_{k≥1} E_k`, where `E_k` is the least mean-square error of an affine function of `u` on
  `D_k = [2^{−(k+1)}, 2^{−k}]` (`dyadicAffineErr`, `dyadicAffineErr_isLeast`); and `C > 0` when `f`
  is strongly concave on one `D_k`, `k ≥ 1`, as `Φ⁻¹` is for `k ≥ 2` (`dyadicAffineErr_pos`, from
  `dyadic_mse_ge`; this part needs no oddness, as `C` only depends on `f` on `[0, ½]`).
* **The paper's mechanism is not exact.**  The error of method 3 on `D_k` is, for `d ≥ k + 2`,
  `∫ f² − 2^{k+1}(∫ f)² − 12·8^{k+1} N²/(N² − 1) W_d²` with `N = 2^{d−k−1}` (`dyadic_groupMSE_eq`),
  where `W_d` is a Riemann sum of `∫_{D_k} (u − c_k) f(u) du`: it changes with `d` and only tends to
  `E_k` (`tendsto_dyadic_groupMSE`).  If `f` is quadratic on `D_k` it is exactly
  `E_k + f'(c_k)² 2^{−(k+1)} 4^{−d}/12` (`groupMSE_quadratic`): for `f(u) = (u − ½)|u − ½|`, odd
  about `½` with `C > 0`, the error on every `D_k`, `k ≥ 1`, strictly decreases with `d`
  (`groupMSE_odd_quadratic`), and for `f(u) = u − ½` (where `C = 0`) it is `2^{−(k+1)} 4^{−d}/12`
  (`groupMSE_sub_half`).  For `Φ⁻¹` and `D_1 = [¼, ½]` it is `2.37·10⁻³`, `5.99·10⁻⁴`,
  `1.56·10⁻⁴`, `4.49·10⁻⁵`, `1.71·10⁻⁵`, `1.02·10⁻⁵`, `8.44·10⁻⁶` for `d = 3, …, 9`, with limit
  `E_1 = 7.86·10⁻⁶` (numerical values).  So the paper's statement is right asymptotically but not
  exactly: the excess over `E_k` is `O(4^{k−d})` for `f` quadratic on `D_k` (exactly) and, by the
  same Riemann-sum expansion, heuristically for smooth `f` (for `Φ⁻¹` it is divided by `≈ 4` per
  bit, numerically), so it sits mostly in the intervals closest to `0`.  The limit of the sum over
  the `d − 2` intervals follows by dominated convergence (`tendsto_sum_range_of_dominated`, a
  Tannery theorem) from `0 ≤ error on D_k ≤ ∫_{D_k} f²` (`groupMSE_le`), a summable bound.  For
  `Φ⁻¹`, `C ≈ 4.133·10⁻⁵` (the MSE is `4.81·10⁻⁵` at `d = 14` and `4.28·10⁻⁵` at `d = 16`).

**Method 1: the MSE is of order `2^{−d}/d` (H3-30).**  Assume `f(1 − u) = −f(u)` and, on each
dyadic block `[2^{−(m+1)}, 2^{−m}]`, `m ≥ 1`, the two-sided bounds
`c (2^m (v − u))² ≤ m (f(v) − f(u))² ≤ K (2^m (v − u))²`, i.e. `f' ≍ 2^m/√m ≍ 1/(u √log(1/u))`.
`Φ⁻¹` satisfies them with `c = ½` and `K = 4`: its derivative `1/φ(Φ⁻¹)` decreases on `(0, ½]`, and
`m (2^{−m} (Φ⁻¹)'(2^{−m}))² ≥ 0.721`, `m (2^{−m} (Φ⁻¹)'(2^{−(m+1)}))² ≤ 3.18` (limits `1/(2 ln 2)`
and `2/ln 2`).
* `method1MSE_order`: `(c/64) 2^{−d}/d ≤ MSE ≤ 6K 2^{−d}/d` for every `d ≥ 2`
  (`method1MSE_ge_order`: one cell next to `0` already gives the lower bound;
  `method1MSE_le_order`: the cells of the block `m` contribute `O(2^{−d} 2^{m−d}/m)`, and the end
  cell `[0, 2^{−d}]`, by chaining the blocks `m ≥ d`, `O(2^{−d}/d)`);
* `tendsto_log_method1MSE_div`: `log(MSE)/d → −log 2`, i.e. the MSE is divided by 2 per bit on
  average.
The exact halving `MSE(d + 1)/MSE(d) → ½` is not proved: the order gives it only up to a bounded
factor, and the exact limit needs `MSE(d) ~ κ 2^{−d}/d` with an exact constant `κ`, hence finer
asymptotics of `Φ⁻¹` near `0` (`(Φ⁻¹)'(u) u √(2 log(1/u)) → 1` and the variance of the normal
tail).  Numerically `d 2^d MSE = 1.533, 1.552, 1.557` for `d = 10, 16, 18` (heuristically
`κ = 13/(12 ln 2) ≈ 1.563`), and `MSE(d + 1)/MSE(d) = 0.451, 0.470, 0.473` for `d = 9, 15, 17`,
i.e. `½(1 − 1/d + …)`.  The halving for method 2 (which the paper calls only "intuitively true
for method 2 after the optimisation stage") is not treated here; only method 1 is.
-/

open MeasureTheory Finset Filter Topology

namespace MLMC

variable {f : ℝ → ℝ}

/-! ### Helpers: integrability, dyadic blocks, dominated convergence, the sign bit -/

section Helpers

/-- A function interval-integrable on `[0, 1]` is interval-integrable on every `[a, b]` with
`0 ≤ a ≤ b ≤ 1`. -/
lemma intervalIntegrable_sub01 {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : IntervalIntegrable g volume a b :=
  hg.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨ha, hab.trans hb⟩))
    (Set.mem_uIcc.2 (Or.inl ⟨ha.trans hab, hb⟩)))

/-- `0 ≤ 2^{−m} ≤ 1`. -/
lemma inv_two_pow_mem (m : ℕ) : 0 ≤ ((2 : ℝ) ^ m)⁻¹ ∧ ((2 : ℝ) ^ m)⁻¹ ≤ 1 :=
  ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)⟩

/-- `m ↦ 2^{−m}` is antitone. -/
lemma inv_two_pow_anti {m n : ℕ} (h : m ≤ n) : ((2 : ℝ) ^ n)⁻¹ ≤ ((2 : ℝ) ^ m)⁻¹ :=
  inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two h)

/-- The grid points `u_j = 2^{−d} j` increase with `j`. -/
lemma gridPt_mono (d : ℕ) {a b : ℕ} (h : a ≤ b) : gridPt d a ≤ gridPt d b := by
  unfold gridPt
  gcongr

/-- If `g` is interval-integrable on `[0, 1]` and `x_d → 0` in `[0, 1]`, then `∫₀^{x_d} g → 0`. -/
lemma tendsto_integral_zero {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1)
    {x : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 0)) (hx01 : ∀ d, x d ∈ Set.uIcc (0 : ℝ) 1) :
    Tendsto (fun d => ∫ u in (0 : ℝ)..x d, g u) atTop (𝓝 0) := by
  have hG : ContinuousOn (fun y => ∫ u in (0 : ℝ)..y, g u) (Set.uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval' hg Set.left_mem_uIcc
  have h1 := (hG 0 Set.left_mem_uIcc).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hx01⟩)
  rw [intervalIntegral.integral_same] at h1
  exact h1

/-- The dyadic blocks `[2^{−(r+a+1)}, 2^{−(r+a)}]`, `r < M`, tile `[2^{−(M+a)}, 2^{−a}]`:
`∑_{r<M} ∫_{2^{−(r+a+1)}}^{2^{−(r+a)}} g = ∫_{2^{−(M+a)}}^{2^{−a}} g`. -/
lemma sum_range_blocks {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) (a M : ℕ) :
    ∑ r ∈ range M, ∫ u in ((2 : ℝ) ^ (r + a + 1))⁻¹..((2 : ℝ) ^ (r + a))⁻¹, g u =
      ∫ u in ((2 : ℝ) ^ (M + a))⁻¹..((2 : ℝ) ^ a)⁻¹, g u := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, add_comm, show M + 1 + a = M + a + 1 by ring]
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sub01 hg (inv_two_pow_mem _).1 (inv_two_pow_anti (by omega))
        (inv_two_pow_mem _).2)
      (intervalIntegrable_sub01 hg (inv_two_pow_mem _).1 (inv_two_pow_anti (by omega))
        (inv_two_pow_mem _).2)

/-- The integrals `∫_{D_{k+1}} f²` over the dyadic intervals `D_{k+1} = [2^{−(k+2)}, 2^{−(k+1)}]`
are summable (their partial sums are at most `∫₀¹ f²`). -/
lemma summable_dyadic_sq (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) :
    Summable fun k : ℕ => ∫ u in ((2 : ℝ) ^ (k + 1 + 1))⁻¹..((2 : ℝ) ^ (k + 1))⁻¹, f u ^ 2 := by
  refine summable_of_sum_range_le (c := ∫ u in (0 : ℝ)..1, f u ^ 2)
    (fun k => intervalIntegral.integral_nonneg (inv_two_pow_anti (by omega))
      fun u _ => sq_nonneg _) fun K => ?_
  rw [sum_range_blocks hf2 1 K]
  exact intervalIntegral.integral_mono_interval (by positivity) (inv_two_pow_anti (by omega))
    (inv_two_pow_mem 1).2 (Eventually.of_forall fun u => sq_nonneg _) hf2

/-- For `d ≥ k + 1`, the cells `I_j`, `2^{d−k−1} ≤ j < 2^{d−k}`, tile the dyadic interval
`D_k = [2^{−(k+1)}, 2^{−k}]`: `∑_j ∫_{I_j} g = ∫_{D_k} g`. -/
lemma sum_dyadic_cells {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) {d k : ℕ}
    (hd : k + 1 ≤ d) :
    ∑ j ∈ Ico (2 ^ (d - k - 1)) (2 ^ (d - k)), ∫ u in gridPt d j..gridPt d (j + 1), g u =
      ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, g u := by
  have hle : 2 ^ (d - k - 1) ≤ 2 ^ (d - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hS : ∀ j ∈ Set.Ico (2 ^ (d - k - 1)) (2 ^ (d - k)), j < 2 ^ d := fun j hj =>
    lt_of_lt_of_le hj.2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [intervalIntegral.sum_integral_adjacent_intervals_Ico (a := gridPt d) hle
    fun j hj => intervalIntegrable_cell hg (hS j hj), gridPt_two_pow (k := k + 1) (by omega),
    gridPt_two_pow (k := k) (by omega)]

/-- **Tannery's theorem for nonnegative terms** (dominated convergence for series).  If
`0 ≤ F d k ≤ b k` for `k < φ d`, `b` is summable, `F d k → g k` for every `k` and `φ d → ∞`, then
`∑_{k<φ d} F d k → ∑' k, g k`.  (A special case of Mathlib's
`tendsto_tsum_of_dominated_convergence`, proved directly by an `ε/3` argument to avoid importing
`Mathlib.Analysis.Normed.Group.Tannery`.) -/
lemma tendsto_sum_range_of_dominated {F : ℕ → ℕ → ℝ} {g b : ℕ → ℝ} {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) (hb : Summable b)
    (hF0 : ∀ d k, k < φ d → 0 ≤ F d k) (hFb : ∀ d k, k < φ d → F d k ≤ b k)
    (hlim : ∀ k, Tendsto (fun d => F d k) atTop (𝓝 (g k))) :
    Tendsto (fun d => ∑ k ∈ range (φ d), F d k) atTop (𝓝 (∑' k, g k)) := by
  have hev : ∀ k, ∀ᶠ d in atTop, k < φ d := fun k => hφ.eventually (eventually_gt_atTop k)
  have hg0 : ∀ k, 0 ≤ g k := fun k =>
    ge_of_tendsto (hlim k) ((hev k).mono fun d hd => hF0 d k hd)
  have hgb : ∀ k, g k ≤ b k := fun k =>
    le_of_tendsto (hlim k) ((hev k).mono fun d hd => hFb d k hd)
  have hb0 : ∀ k, 0 ≤ b k := fun k => (hg0 k).trans (hgb k)
  have hg : Summable g := Summable.of_nonneg_of_le hg0 hgb hb
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hb.hasSum.tendsto_sum_nat (ε / 3) (by positivity)
  have hNb : ∑' k, b k - ∑ k ∈ range N, b k < ε / 3 := by
    have h := hN N le_rfl
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.2]
  have hgt : ∑' k, g k - ∑ k ∈ range N, g k ≤ ∑' k, b k - ∑ k ∈ range N, b k := by
    have h := (hb.sub hg).sum_le_tsum (range N) (fun k _ => sub_nonneg.2 (hgb k))
    rw [hb.tsum_sub hg, Finset.sum_sub_distrib] at h
    linarith
  have hg1 : ∑ k ∈ range N, g k ≤ ∑' k, g k := hg.sum_le_tsum (range N) (fun k _ => hg0 k)
  have hfin : Tendsto (fun d => ∑ k ∈ range N, F d k) atTop (𝓝 (∑ k ∈ range N, g k)) :=
    tendsto_finsetSum _ fun k _ => hlim k
  obtain ⟨D, hD⟩ := Metric.tendsto_atTop.1 hfin (ε / 3) (by positivity)
  obtain ⟨D', hD'⟩ := eventually_atTop.1 (hφ.eventually (eventually_ge_atTop N))
  refine ⟨max D D', fun d hd => ?_⟩
  have hNd : N ≤ φ d := hD' d (le_of_max_le_right hd)
  have h1 := hD d (le_of_max_le_left hd)
  rw [Real.dist_eq, abs_sub_lt_iff] at h1
  rw [← Finset.sum_range_add_sum_Ico _ hNd, Real.dist_eq, abs_sub_lt_iff]
  have ht0 : 0 ≤ ∑ k ∈ Ico N (φ d), F d k :=
    Finset.sum_nonneg fun k hk => hF0 d k (Finset.mem_Ico.1 hk).2
  have htb : ∑ k ∈ Ico N (φ d), F d k ≤ ∑ k ∈ Ico N (φ d), b k :=
    Finset.sum_le_sum fun k hk => hFb d k (Finset.mem_Ico.1 hk).2
  have hbt : ∑ k ∈ Ico N (φ d), b k ≤ ∑' k, b k - ∑ k ∈ range N, b k := by
    have h := hb.sum_le_tsum (range (φ d)) (fun k _ => hb0 k)
    rw [← Finset.sum_range_add_sum_Ico _ hNd] at h
    linarith
  constructor <;> linarith

/-- **The sign bit** (Haas–Giles 2025, §3.1, §3.3): if `f(1 − u) = −f(u)`, the value `−w` on the
mirrored cell `I_{2^d−1−j}` has the same mean-square error as `w` on `I_j`. -/
lemma integral_mirror_cell (hodd : ∀ u, f (1 - u) = -f u) {d j : ℕ} (hj : j < 2 ^ d) (w : ℝ) :
    ∫ u in gridPt d (2 ^ d - 1 - j)..gridPt d (2 ^ d - 1 - j + 1), (-w - f u) ^ 2 =
      ∫ u in gridPt d j..gridPt d (j + 1), (w - f u) ^ 2 := by
  have h2 : (0 : ℝ) < 2 ^ d := by positivity
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ d - 1 - j = m := ⟨_, rfl⟩
  have hmR : (m : ℝ) + j + 1 = 2 ^ d := by exact_mod_cast (show m + j + 1 = 2 ^ d by omega)
  rw [hm]
  have hlo : gridPt d m = 1 - gridPt d (j + 1) := by
    unfold gridPt
    rw [div_eq_iff h2.ne', sub_mul, div_mul_cancel₀ _ h2.ne', one_mul]
    push_cast
    linarith
  have hhi : gridPt d (m + 1) = 1 - gridPt d j := by
    unfold gridPt
    rw [div_eq_iff h2.ne', sub_mul, div_mul_cancel₀ _ h2.ne', one_mul]
    push_cast
    linarith
  rw [hlo, hhi, ← intervalIntegral.integral_comp_sub_left (fun u => (-w - f u) ^ 2) 1]
  congr 1
  funext u
  rw [hodd]
  ring

/-- A sum over `j < 2^d` is a sum over the lower half `j < 2^{d−1}` of the pairs `j`,
`2^d − 1 − j` (for `d ≥ 1`). -/
lemma sum_range_two_pow_mirror (F : ℕ → ℝ) {d : ℕ} (hd : 1 ≤ d) :
    ∑ j ∈ range (2 ^ d), F j = ∑ j ∈ range (2 ^ (d - 1)), (F j + F (2 ^ d - 1 - j)) := by
  have h2 : 2 ^ d = 2 ^ (d - 1) + 2 ^ (d - 1) := by
    rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hd]
  rw [Finset.sum_add_distrib, h2, Finset.sum_range_add]
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.1 hj
  congr 1
  omega

/-- The dyadic decomposition of `[0, 2^n)`:
`∑_{j<2^n} F_j = F_0 + ∑_{i<n} ∑_{2^i ≤ j < 2^{i+1}} F_j`. -/
lemma sum_range_two_pow_dyadic (F : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range (2 ^ n), F j = F 0 + ∑ i ∈ range n, ∑ j ∈ Ico (2 ^ i) (2 ^ (i + 1)), F j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Finset.sum_range_add_sum_Ico F (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)),
      ih, Finset.sum_range_succ]
    ring

end Helpers

/-! ### Least squares: the values `a + b j` of method 3 -/

section LeastSquares

/-- The mean `(1/|S|) ∑_{j∈S} y_j` of `y` over a finite set `S` (`0` for `S = ∅`). -/
noncomputable def finMean (S : Finset ℕ) (y : ℕ → ℝ) : ℝ := (∑ j ∈ S, y j) / S.card

/-- The least-squares slope `∑_S (j − j̄) y_j / ∑_S (j − j̄)²` of the data `(j, y_j)`, `j ∈ S`, with
`j̄` the mean of `j` over `S` (`0` if all the `j ∈ S` coincide, i.e. `|S| ≤ 1`). -/
noncomputable def lsqSlope (S : Finset ℕ) (y : ℕ → ℝ) : ℝ :=
  (∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) * y j) /
    ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) ^ 2

/-- **The values of method 3** (Haas–Giles 2025, §3.3: "`Z̄_j = a + bj`, with a separate pair
`(a, b)` for each interval", "the values `(a, b)` are again obtained by minimising the MSE"): the
least-squares line `ȳ + slope·(j − j̄)` through the data `(j, y_j)`, `j ∈ S`.  (The regression
`lsSlope`, `lsIntercept`, `lsFit_le` of `MlmcLean/Implementation.lean` is not reused: importing it
would pull in the algorithm, Gaussian and probability modules, `lsFit_le` excludes the degenerate
case `|S| ≤ 1`, and the centred form in `j − j̄` is the one used in the algebra below.) -/
noncomputable def lsqFit (S : Finset ℕ) (y : ℕ → ℝ) (j : ℕ) : ℝ :=
  finMean S y + lsqSlope S y * ((j : ℝ) - finMean S fun i => (i : ℝ))

/-- Deviations from the mean sum to `0`. -/
lemma sum_sub_finMean (S : Finset ℕ) (y : ℕ → ℝ) : ∑ j ∈ S, (y j - finMean S y) = 0 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, finMean, mul_div_cancel₀ _ hc,
    sub_self]

/-- Expanding the least-squares objective about the means: with `e_j = j − j̄`,
`∑_S (ȳ + α + β e_j − y_j)² = |S| α² + β² ∑ e_j² − 2β ∑ e_j y_j + ∑ (y_j − ȳ)²`. -/
lemma sum_sq_affine_expand (S : Finset ℕ) (y : ℕ → ℝ) (α β : ℝ) :
    ∑ j ∈ S, (finMean S y + α + β * ((j : ℝ) - finMean S fun i => (i : ℝ)) - y j) ^ 2 =
      S.card * α ^ 2 + β ^ 2 * ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) ^ 2 -
        2 * β * ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) * y j +
        ∑ j ∈ S, (y j - finMean S y) ^ 2 := by
  have h1 : ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) = 0 :=
    sum_sub_finMean S fun i => (i : ℝ)
  have h2 : ∑ j ∈ S, (y j - finMean S y) = 0 := sum_sub_finMean S y
  have key : ∀ j ∈ S,
      (finMean S y + α + β * ((j : ℝ) - finMean S fun i => (i : ℝ)) - y j) ^ 2 =
      α ^ 2 + β ^ 2 * ((j : ℝ) - finMean S fun i => (i : ℝ)) ^ 2 -
      2 * β * (((j : ℝ) - finMean S fun i => (i : ℝ)) * y j) + (y j - finMean S y) ^ 2 +
      (2 * α * β + 2 * β * finMean S y) * ((j : ℝ) - finMean S fun i => (i : ℝ)) -
      2 * α * (y j - finMean S y) := fun j _ => by ring
  rw [Finset.sum_congr rfl key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- If `∑_S (j − j̄)² = 0` then `∑_S (j − j̄) y_j = 0`. -/
lemma lsqNum_eq_zero_of_den (S : Finset ℕ) (y : ℕ → ℝ)
    (hQ : ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) ^ 2 = 0) :
    ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) * y j = 0 := by
  have h := (Finset.sum_eq_zero_iff_of_nonneg fun (j : ℕ) _ => sq_nonneg
    ((j : ℝ) - finMean S fun i => (i : ℝ))).1 hQ
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [(pow_eq_zero_iff two_ne_zero).1 (h j hj), zero_mul]

/-- `lsqFit` written as `ȳ + 0 + slope · (j − j̄)`. -/
lemma lsqFit_sub_eq (S : Finset ℕ) (y : ℕ → ℝ) (j : ℕ) :
    lsqFit S y j - y j = finMean S y + 0 + lsqSlope S y * ((j : ℝ) - finMean S fun i => (i : ℝ))
      - y j := by
  rw [lsqFit, add_zero]

/-- The residual of the least-squares line:
`∑_S (Z̄_j − y_j)² = ∑_S (y_j − ȳ)² − (∑_S (j − j̄) y_j)² / ∑_S (j − j̄)²`. -/
lemma sum_sq_lsqFit_sub (S : Finset ℕ) (y : ℕ → ℝ) :
    ∑ j ∈ S, (lsqFit S y j - y j) ^ 2 = ∑ j ∈ S, (y j - finMean S y) ^ 2 -
      (∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) * y j) ^ 2 /
        ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) ^ 2 := by
  simp only [lsqFit_sub_eq]
  rw [sum_sq_affine_expand, lsqSlope]
  set P := ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) * y j
  set Q := ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) ^ 2
  rcases eq_or_ne Q 0 with hQ | hQ
  · have hP : P = 0 := lsqNum_eq_zero_of_den S y hQ
    rw [hQ, hP]
    ring
  · field_simp
    ring

/-- **The values of method 3 minimise (19)** (Haas–Giles 2025, §3.3: "to calculate the pairs
`(a, b)` we only need to minimise `∑_j (Z̄_j − Z_j)²`"): for every `a`, `b`, the least-squares
line `lsqFit S y` has `∑_{j∈S} (Z̄_j − y_j)² ≤ ∑_{j∈S} (a + b j − y_j)²`.  With `y = Z` and by (19)
(`sum_integral_sq_le_iff`), `lsqFit` is the paper's choice of `(a, b)` on each dyadic interval. -/
theorem sum_sq_lsqFit_le (S : Finset ℕ) (y : ℕ → ℝ) (a b : ℝ) :
    ∑ j ∈ S, (lsqFit S y j - y j) ^ 2 ≤ ∑ j ∈ S, (a + b * j - y j) ^ 2 := by
  have e : ∀ j ∈ S, (a + b * j - y j) = finMean S y + (a + b * finMean S (fun i => (i : ℝ))
      - finMean S y) + b * ((j : ℝ) - finMean S fun i => (i : ℝ)) - y j := fun j _ => by ring
  have hR : ∑ j ∈ S, (a + b * j - y j) ^ 2 = ∑ j ∈ S, (finMean S y +
      (a + b * finMean S (fun i => (i : ℝ)) - finMean S y) +
      b * ((j : ℝ) - finMean S fun i => (i : ℝ)) - y j) ^ 2 :=
    Finset.sum_congr rfl fun j hj => by rw [e j hj]
  rw [hR, sum_sq_affine_expand]
  simp only [lsqFit_sub_eq]
  rw [sum_sq_affine_expand, lsqSlope]
  set P := ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) * y j
  set Q := ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) ^ 2
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hα := mul_nonneg (Nat.cast_nonneg (α := ℝ) S.card)
    (sq_nonneg (a + b * finMean S (fun i => (i : ℝ)) - finMean S y))
  rcases eq_or_ne Q 0 with hQ | hQ
  · have hP : P = 0 := lsqNum_eq_zero_of_den S y hQ
    rw [hQ, hP]
    nlinarith
  · have hQp : 0 < Q := lt_of_le_of_ne hQ0 (Ne.symm hQ)
    have key : (P / Q) ^ 2 * Q - 2 * (P / Q) * P ≤ b ^ 2 * Q - 2 * b * P := by
      have h := mul_nonneg hQp.le (sq_nonneg (b - P / Q))
      have e2 : Q * (b - P / Q) ^ 2 = b ^ 2 * Q - 2 * b * P - ((P / Q) ^ 2 * Q - 2 * (P / Q) * P)
          := by field_simp; ring
      linarith
    nlinarith

/-- `lsqFit S y` is affine in `j`. -/
lemma lsqFit_affine (S : Finset ℕ) (y : ℕ → ℝ) : ∃ a b : ℝ, ∀ j, lsqFit S y j = a + b * j :=
  ⟨finMean S y - lsqSlope S y * finMean S (fun i => (i : ℝ)), lsqSlope S y, fun j => by
    rw [lsqFit]; ring⟩

/-- `∑_S (y_j − ȳ)² = ∑_S y_j² − (∑_S y_j)²/|S|`. -/
lemma sum_sq_sub_finMean (S : Finset ℕ) (y : ℕ → ℝ) :
    ∑ j ∈ S, (y j - finMean S y) ^ 2 = ∑ j ∈ S, y j ^ 2 - (∑ j ∈ S, y j) ^ 2 / S.card := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have key : ∀ j ∈ S, (y j - finMean S y) ^ 2 = y j ^ 2 - 2 * finMean S y * y j +
      finMean S y ^ 2 := fun j _ => by ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, finMean]
  field_simp
  ring

/-- `∑_{i<N} i = N(N − 1)/2` in `ℝ`. -/
lemma sum_range_natCast (N : ℕ) : ∑ i ∈ range N, (i : ℝ) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `∑_{i<N} (i − a)² = N(N − 1)(2N − 1)/6 − aN(N − 1) + N a²`. -/
lemma sum_range_sub_sq (N : ℕ) (a : ℝ) : ∑ i ∈ range N, ((i : ℝ) - a) ^ 2 =
    N * (N - 1) * (2 * N - 1) / 6 - a * N * (N - 1) + N * a ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The mean index of `[N, 2N)` is `(3N − 1)/2`. -/
lemma finMean_Ico {N : ℕ} (hN : 1 ≤ N) :
    finMean (Ico N (2 * N)) (fun i => (i : ℝ)) = (3 * N - 1) / 2 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [finMean, Finset.sum_Ico_eq_sum_range, Nat.card_Ico, show 2 * N - N = N by omega]
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    sum_range_natCast]
  field_simp
  ring

/-- `∑_{N ≤ j < 2N} (j − (3N − 1)/2)² = (N³ − N)/12`. -/
lemma sum_sq_Ico_sub {N : ℕ} (hN : 1 ≤ N) :
    ∑ j ∈ Ico N (2 * N), ((j : ℝ) - finMean (Ico N (2 * N)) fun i => (i : ℝ)) ^ 2 =
      ((N : ℝ) ^ 3 - N) / 12 := by
  rw [finMean_Ico hN, Finset.sum_Ico_eq_sum_range, show 2 * N - N = N by omega]
  have e : ∀ i ∈ range N, (((N + i : ℕ) : ℝ) - (3 * N - 1) / 2) ^ 2 =
      ((i : ℝ) - (N - 1) / 2) ^ 2 := fun i _ => by push_cast; ring
  rw [Finset.sum_congr rfl e, sum_range_sub_sq]
  ring

/-- `∑_{i<N} (i − a)³ = N²(N − 1)²/4 − a N(N − 1)(2N − 1)/2 + 3a² N(N − 1)/2 − N a³`. -/
lemma sum_range_sub_cube (N : ℕ) (a : ℝ) : ∑ i ∈ range N, ((i : ℝ) - a) ^ 3 =
    (N : ℝ) ^ 2 * (N - 1) ^ 2 / 4 - a * N * (N - 1) * (2 * N - 1) / 2 +
      3 * a ^ 2 * N * (N - 1) / 2 - N * a ^ 3 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `∑_{N ≤ j < 2N} (j − (3N − 1)/2)³ = 0`: the points are symmetric about their mean. -/
lemma sum_cube_Ico_sub (N : ℕ) :
    ∑ j ∈ Ico N (2 * N), ((j : ℝ) - (3 * N - 1) / 2) ^ 3 = 0 := by
  rw [Finset.sum_Ico_eq_sum_range, show 2 * N - N = N by omega]
  have e : ∀ i ∈ range N, (((N + i : ℕ) : ℝ) - (3 * N - 1) / 2) ^ 3 =
      ((i : ℝ) - (N - 1) / 2) ^ 3 := fun i _ => by push_cast; ring
  rw [Finset.sum_congr rfl e, sum_range_sub_cube]
  ring

end LeastSquares

/-! ### Method 3: the mean-square error converges to `C > 0` -/

section Method3

/-- **The dyadic interval of the index `j`** (Haas–Giles 2025, §3.3: "a separate pair `(a, b)`
for each interval `I'_i = [[2^{i−1}, 2^i − 1]]`, where `i` is the leading non-zero bit of the
integer `j`. The coefficients are stored in a LUT of size `d − 1`"): `{0, 1}` for `j < 2`, and
`[2^i, 2^{i+1})` with `i = ⌊log₂ j⌋` for `j ≥ 2`.  The index `j = 0`, which has no leading bit, is
joined to `{1}`, so that "for the first two dyadic intervals there are only two points in each"
(§3.4) and the `2^{d−1}` indices of `[0, ½]` form `d − 1` intervals. -/
def dyadicGroup (j : ℕ) : Finset ℕ :=
  if j < 2 then range 2 else Ico (2 ^ Nat.log 2 j) (2 ^ (Nat.log 2 j + 1))

/-- The value `Z̄_j` of method 3 on a cell `I_j` of `[0, ½]` (`j < 2^{d−1}`): the least-squares
line (19) through the LUT values `Z_i` of the dyadic interval of `j` (Haas–Giles 2025, §3.3). -/
noncomputable def method3Half (f : ℝ → ℝ) (d j : ℕ) : ℝ :=
  lsqFit (dyadicGroup j) (lutValue f d) j

/-- **The approximation of method 3 on `[0, 1]`** (Haas–Giles 2025, §3.3: "the leading bit of `j`
is a sign bit used to flip the sign of an approximate normal variable when `U > ½`"): `Z̄_j` on
the cells of `[0, ½]` and `−Z̄_{2^d−1−j}` on the mirrored cells of `[½, 1]`. -/
noncomputable def method3Value (f : ℝ → ℝ) (d j : ℕ) : ℝ :=
  if j < 2 ^ (d - 1) then method3Half f d j else -method3Half f d (2 ^ d - 1 - j)

/-- **The mean-square error of method 3** (Haas–Giles 2025, §3.3–§3.4):
`∑_{j<2^d} ∫_{I_j} (Z̄_j − f)²`. -/
noncomputable def method3MSE (f : ℝ → ℝ) (d : ℕ) : ℝ :=
  ∑ j ∈ range (2 ^ d), ∫ u in gridPt d j..gridPt d (j + 1), (method3Value f d j - f u) ^ 2

/-- The mean-square error `∑_{j∈S} ∫_{I_j} (Z̄_j − f)²` of the least-squares line through the LUT
values on the cells of a set `S` of indices (Haas–Giles 2025, §3.3). -/
noncomputable def groupMSE (f : ℝ → ℝ) (d : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ j ∈ S, ∫ u in gridPt d j..gridPt d (j + 1), (lsqFit S (lutValue f d) j - f u) ^ 2

/-- The dyadic interval of `j < 2` is `{0, 1}`. -/
lemma dyadicGroup_of_lt_two {j : ℕ} (hj : j < 2) : dyadicGroup j = range 2 := by
  rw [dyadicGroup, if_pos hj]

/-- The dyadic interval of `j ∈ [2^i, 2^{i+1})`, `i ≥ 1`, is `[2^i, 2^{i+1})`. -/
lemma dyadicGroup_of_mem {i j : ℕ} (hi : 1 ≤ i) (hj : j ∈ Ico (2 ^ i) (2 ^ (i + 1))) :
    dyadicGroup j = Ico (2 ^ i) (2 ^ (i + 1)) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hj
  have h2i : 2 ≤ 2 ^ i := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  rw [dyadicGroup, if_neg (by omega), Nat.log_eq_of_pow_le_of_lt_pow h1 h2]

/-- **The sign bit halves the work** (Haas–Giles 2025, §3, §3.3): if `f(1 − u) = −f(u)`, the
mean-square error of method 3 is twice that on `[0, ½]`. -/
lemma method3MSE_eq_two_mul (hodd : ∀ u, f (1 - u) = -f u) {d : ℕ} (hd : 1 ≤ d) :
    method3MSE f d = 2 * ∑ j ∈ range (2 ^ (d - 1)),
      ∫ u in gridPt d j..gridPt d (j + 1), (method3Half f d j - f u) ^ 2 := by
  have h2 : 2 ^ d = 2 * 2 ^ (d - 1) := by rw [← pow_succ', Nat.sub_add_cancel hd]
  rw [method3MSE, sum_range_two_pow_mirror _ hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 := Finset.mem_range.1 hj
  have hj' : j < 2 ^ d := by omega
  have hv1 : method3Value f d j = method3Half f d j := by rw [method3Value, if_pos hj1]
  have hv2 : method3Value f d (2 ^ d - 1 - j) = -method3Half f d j := by
    rw [method3Value, if_neg (by omega), show 2 ^ d - 1 - (2 ^ d - 1 - j) = j by omega]
  rw [hv1, hv2, integral_mirror_cell hodd hj']
  ring

/-- The mean-square error of method 3 on `[0, ½]` is the sum over the dyadic intervals: the first
one `{0, 1}` and the intervals `[2^{d−k−1}, 2^{d−k})` (in `u`: `D_k = [2^{−(k+1)}, 2^{−k}]`),
`1 ≤ k ≤ d − 2`. -/
lemma method3_half_eq {d : ℕ} (hd : 2 ≤ d) :
    ∑ j ∈ range (2 ^ (d - 1)),
      ∫ u in gridPt d j..gridPt d (j + 1), (method3Half f d j - f u) ^ 2 =
      groupMSE f d (range 2) + ∑ k ∈ range (d - 2),
        groupMSE f d (Ico (2 ^ (d - (k + 1) - 1)) (2 ^ (d - (k + 1)))) := by
  set F : ℕ → ℝ := fun j => ∫ u in gridPt d j..gridPt d (j + 1), (method3Half f d j - f u) ^ 2
  have hd1 : d - 1 = d - 2 + 1 := by omega
  rw [sum_range_two_pow_dyadic F (d - 1), ← Finset.sum_range_reflect, hd1, Finset.sum_range_succ,
    show d - 2 + 1 - 1 - (d - 2) = 0 by omega]
  have h0 : F 0 + ∑ j ∈ Ico (2 ^ 0) (2 ^ (0 + 1)), F j = groupMSE f d (range 2) := by
    rw [groupMSE, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, zero_add, pow_one]
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
    simp only [F, method3Half, dyadicGroup_of_lt_two (show 0 < 2 by norm_num),
      dyadicGroup_of_lt_two (show 1 < 2 by norm_num)]
  have hk : ∀ k ∈ range (d - 2), ∑ j ∈ Ico (2 ^ (d - 2 + 1 - 1 - k)) (2 ^ (d - 2 + 1 - 1 - k + 1)),
      F j = groupMSE f d (Ico (2 ^ (d - (k + 1) - 1)) (2 ^ (d - (k + 1)))) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have e1 : d - 2 + 1 - 1 - k = d - (k + 1) - 1 := by omega
    have e2 : d - (k + 1) - 1 + 1 = d - (k + 1) := by omega
    rw [e1, e2, groupMSE]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ∈ Ico (2 ^ (d - (k + 1) - 1)) (2 ^ (d - (k + 1) - 1 + 1)) := by rwa [e2]
    simp only [F, method3Half]
    rw [dyadicGroup_of_mem (by omega) hj', e2]
  rw [Finset.sum_congr rfl hk, ← h0]
  ring

/-- `∫_{I_j} (Z_j − f)² = ∫_{I_j} f² − 2^{−d} Z_j²`. -/
lemma integral_sq_sub_lutValue_eq {d j : ℕ}
    (hf : IntervalIntegrable f volume (gridPt d j) (gridPt d (j + 1)))
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume (gridPt d j) (gridPt d (j + 1))) :
    ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 =
      (∫ u in gridPt d j..gridPt d (j + 1), f u ^ 2) - (2 ^ d)⁻¹ * lutValue f d j ^ 2 := by
  have hpos : (2 : ℝ) ^ d ≠ 0 := by positivity
  have hI : ∫ u in gridPt d j..gridPt d (j + 1), f u = (2 ^ d)⁻¹ * lutValue f d j := by
    rw [lutValue, ← mul_assoc, inv_mul_cancel₀ hpos, one_mul]
  rw [integral_sq_sub_const hf hf2, gridPt_succ_sub, hI]
  ring

/-- The mean-square error of the least-squares line on the cells of `S`:
`∑_S ∫_{I_j} f² − 2^{−d} ((∑_S Z_j)²/|S| + (∑_S (j − j̄) Z_j)² / ∑_S (j − j̄)²)`. -/
lemma groupMSE_eq (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {d : ℕ} {S : Finset ℕ}
    (hS : ∀ j ∈ S, j < 2 ^ d) :
    groupMSE f d S = ∑ j ∈ S, (∫ u in gridPt d j..gridPt d (j + 1), f u ^ 2) -
      (2 ^ d)⁻¹ * ((∑ j ∈ S, lutValue f d j) ^ 2 / S.card +
        (∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) * lutValue f d j) ^ 2 /
          ∑ j ∈ S, ((j : ℝ) - finMean S fun i => (i : ℝ)) ^ 2) := by
  have hcell : ∀ j ∈ S, ∫ u in gridPt d j..gridPt d (j + 1),
      (lsqFit S (lutValue f d) j - f u) ^ 2 =
      (2 ^ d)⁻¹ * (lsqFit S (lutValue f d) j - lutValue f d j) ^ 2 +
        ((∫ u in gridPt d j..gridPt d (j + 1), f u ^ 2) - (2 ^ d)⁻¹ * lutValue f d j ^ 2) :=
    fun j hj => by
      rw [integral_sq_sub_lutValue (intervalIntegrable_cell hf (hS j hj))
        (intervalIntegrable_cell hf2 (hS j hj)), integral_sq_sub_lutValue_eq
        (intervalIntegrable_cell hf (hS j hj)) (intervalIntegrable_cell hf2 (hS j hj))]
  rw [groupMSE, Finset.sum_congr rfl hcell, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, ← Finset.mul_sum, sum_sq_lsqFit_sub, sum_sq_sub_finMean]
  ring

/-- The mean-square error of a group of cells is nonnegative. -/
lemma groupMSE_nonneg (d : ℕ) (S : Finset ℕ) : 0 ≤ groupMSE f d S :=
  Finset.sum_nonneg fun j _ =>
    intervalIntegral.integral_nonneg (gridPt_lt d j).le fun _ _ => sq_nonneg _

/-- The least-squares line does at least as well as the constant `0`:
the error on the cells of `S` is at most `∑_{j∈S} ∫_{I_j} f²`. -/
lemma groupMSE_le (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {d : ℕ} {S : Finset ℕ}
    (hS : ∀ j ∈ S, j < 2 ^ d) :
    groupMSE f d S ≤ ∑ j ∈ S, ∫ u in gridPt d j..gridPt d (j + 1), f u ^ 2 := by
  have hcell : ∀ w : ℕ → ℝ, ∑ j ∈ S, ∫ u in gridPt d j..gridPt d (j + 1), (w j - f u) ^ 2 =
      (2 ^ d)⁻¹ * ∑ j ∈ S, (w j - lutValue f d j) ^ 2 +
        ∑ j ∈ S, ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj => integral_sq_sub_lutValue
      (intervalIntegrable_cell hf (hS j hj)) (intervalIntegrable_cell hf2 (hS j hj)) (w j)
  have h0 : ∑ j ∈ S, ∫ u in gridPt d j..gridPt d (j + 1), f u ^ 2 =
      ∑ j ∈ S, ∫ u in gridPt d j..gridPt d (j + 1), ((fun _ => (0 : ℝ)) j - f u) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by congr 1; funext u; ring
  rw [groupMSE, hcell (lsqFit S (lutValue f d)), h0, hcell (fun _ => 0)]
  have hle := sum_sq_lsqFit_le S (lutValue f d) 0 0
  simp only [zero_mul, zero_add] at hle
  have hpos : (0 : ℝ) ≤ (2 ^ d)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left hle hpos
  linarith

/-- The Riemann sum `W_d = ∑_j ((j + ½) 2^{−d} − c_k) ∫_{I_j} f`, over the cells
`2^{d−k−1} ≤ j < 2^{d−k}` of `D_k`, of the first moment of `f` about the centre
`c_k = 3·2^{−(k+2)}` of `D_k`. -/
noncomputable def dyadicMoment (f : ℝ → ℝ) (d k : ℕ) : ℝ :=
  ∑ j ∈ Ico (2 ^ (d - k - 1) : ℕ) (2 ^ (d - k)),
    (((j : ℝ) + 1 / 2) / 2 ^ d - 3 / 2 ^ (k + 2)) * ∫ u in gridPt d j..gridPt d (j + 1), f u

/-- **The error of method 3 on a dyadic interval depends on `d`** (Haas–Giles 2025, §3.4,
p. 7, claims that "when `d` increases by 1 the MSE is reduced only in the interval closest to 0, so
the error due to the other intervals remains the same"; this is not exact).  For `d ≥ k + 2`, the
error of the least-squares line on the cells of `D_k = [2^{−(k+1)}, 2^{−k}]` (for `k ≥ 1` the
error of method 3 on `D_k`, `method3_half_eq`) is
`∫_{D_k} f² − 2^{k+1} (∫_{D_k} f)² − 12·8^{k+1} N²/(N² − 1) W_d²`, `N = 2^{d−k−1}`,
where `W_d` (`dyadicMoment`) is a Riemann sum of `∫_{D_k} (u − c_k) f(u) du`.  Both `N²/(N² − 1)`
and `W_d` change with `d` (see `groupMSE_quadratic`, `groupMSE_odd_quadratic`, `groupMSE_sub_half`
for explicit examples). -/
theorem dyadic_groupMSE_eq (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {d k : ℕ} (hd : k + 2 ≤ d) :
    groupMSE f d (Ico (2 ^ (d - k - 1)) (2 ^ (d - k))) =
      (∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u ^ 2) -
        2 ^ (k + 1) * (∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u) ^ 2 -
        12 * 8 ^ (k + 1) * (((2 : ℝ) ^ (d - k - 1)) ^ 2 / (((2 : ℝ) ^ (d - k - 1)) ^ 2 - 1)) *
          dyadicMoment f d k ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = k + 1 + n := ⟨d - (k + 1), by omega⟩
  have hn1 : k + 1 + n - k - 1 = n := by omega
  have hn2 : k + 1 + n - k = n + 1 := by omega
  have hn : 1 ≤ n := by omega
  rw [dyadicMoment, hn1, hn2]
  set N : ℕ := 2 ^ n with hNdef
  have h2N : 2 ^ (n + 1) = 2 * N := by rw [pow_succ]; ring
  rw [h2N]
  have hN2 : 2 ≤ N := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hN1 : 1 ≤ N := by omega
  have hdN : (2 : ℝ) ^ (k + 1 + n) = 2 ^ (k + 1) * N := by
    rw [hNdef, pow_add]; push_cast; ring
  have hS : ∀ j ∈ Ico N (2 * N), j < 2 ^ (k + 1 + n) := fun j hj => by
    have h1 := (Finset.mem_Ico.1 hj).2
    have h2 : 2 * N ≤ 2 ^ (k + 1 + n) := by
      rw [← h2N]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hp : gridPt (k + 1 + n) N = ((2 : ℝ) ^ (k + 1))⁻¹ := gridPt_two_pow rfl
  have hq : gridPt (k + 1 + n) (2 * N) = ((2 : ℝ) ^ k)⁻¹ := by
    rw [← h2N]; exact gridPt_two_pow (by omega)
  have hNle : N ≤ 2 * N := by omega
  -- the sums of integrals over the cells
  have hI2 : ∑ j ∈ Ico N (2 * N), ∫ u in gridPt (k + 1 + n) j..gridPt (k + 1 + n) (j + 1),
      f u ^ 2 = ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u ^ 2 := by
    rw [intervalIntegral.sum_integral_adjacent_intervals_Ico (a := gridPt (k + 1 + n)) hNle
      fun j hj => intervalIntegrable_cell hf2 (hS j (Finset.mem_Ico.2 hj)), hp, hq]
  have hI1 : ∑ j ∈ Ico N (2 * N), ∫ u in gridPt (k + 1 + n) j..gridPt (k + 1 + n) (j + 1),
      f u = ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u := by
    rw [intervalIntegral.sum_integral_adjacent_intervals_Ico (a := gridPt (k + 1 + n)) hNle
      fun j hj => intervalIntegrable_cell hf (hS j (Finset.mem_Ico.2 hj)), hp, hq]
  have hZ : ∑ j ∈ Ico N (2 * N), lutValue f (k + 1 + n) j =
      2 ^ (k + 1 + n) * ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u := by
    rw [← hI1, Finset.mul_sum]
    rfl
  have hP : ∑ j ∈ Ico N (2 * N), ((j : ℝ) - finMean (Ico N (2 * N)) fun i => (i : ℝ)) *
      lutValue f (k + 1 + n) j = (2 ^ (k + 1 + n)) ^ 2 * ∑ j ∈ Ico N (2 * N),
        (((j : ℝ) + 1 / 2) / 2 ^ (k + 1 + n) - 3 / 2 ^ (k + 2)) *
          ∫ u in gridPt (k + 1 + n) j..gridPt (k + 1 + n) (j + 1), f u := by
    rw [Finset.mul_sum, finMean_Ico hN1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lutValue, hdN]
    have h2 : (2 : ℝ) ^ (k + 2) = 2 ^ (k + 1) * 2 := by ring
    have hT : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [h2]
    field_simp
    ring
  rw [groupMSE_eq hf hf2 hS, hI2, hZ, hP, sum_sq_Ico_sub hN1, Nat.card_Ico,
    show 2 * N - N = N by omega, hdN]
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hcast : ((2 : ℝ) ^ n) = (N : ℝ) := by rw [hNdef]; push_cast; ring
  rw [hcast]
  have hN3 : (N : ℝ) ^ 3 - N ≠ 0 := by
    have e : (N : ℝ) ^ 3 - N = N * ((N - 1) * (N + 1)) := by ring
    rw [e]
    exact mul_ne_zero (by positivity) (mul_ne_zero (by linarith) (by linarith))
  have hN4 : (N : ℝ) ^ 2 - 1 ≠ 0 := by
    have e : (N : ℝ) ^ 2 - 1 = (N - 1) * (N + 1) := by ring
    rw [e]
    exact mul_ne_zero (by linarith) (by linarith)
  have hT : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have hNR0 : (N : ℝ) ≠ 0 := by positivity
  have h8 : (8 : ℝ) ^ (k + 1) = (2 ^ (k + 1)) ^ 3 := by
    rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, mul_comm]
  rw [h8]
  generalize ∑ j ∈ Ico N (2 * N), (((j : ℝ) + 1 / 2) / (2 ^ (k + 1) * N) - 3 / 2 ^ (k + 2)) *
    ∫ u in gridPt (k + 1 + n) j..gridPt (k + 1 + n) (j + 1), f u = W
  generalize ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u = I1
  generalize ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u ^ 2 = I2
  field_simp
  ring

/-- The first moment `∫_{D_k} (u − c_k) f(u) du` of `f` about the centre `c_k = 3·2^{−(k+2)}` of
`D_k = [2^{−(k+1)}, 2^{−k}]`. -/
noncomputable def dyadicMomentLim (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, (u - 3 / 2 ^ (k + 2)) * f u

/-- The Riemann sum `W_d` is within `2^{−(d+1)} ∫_{D_k} |f|` of `∫_{D_k} (u − c_k) f(u) du`. -/
lemma abs_dyadicMoment_sub_le (hf : IntervalIntegrable f volume 0 1) {d k : ℕ}
    (hd : k + 1 ≤ d) :
    |dyadicMoment f d k - dyadicMomentLim f k| ≤
      (2 ^ (d + 1))⁻¹ * ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, |f u| := by
  obtain ⟨n, rfl⟩ : ∃ n, d = k + 1 + n := ⟨d - (k + 1), by omega⟩
  have hn1 : k + 1 + n - k - 1 = n := by omega
  have hn2 : k + 1 + n - k = n + 1 := by omega
  rw [dyadicMoment, hn1, hn2]
  set N : ℕ := 2 ^ n with hNdef
  have h2N : 2 ^ (n + 1) = 2 * N := by rw [pow_succ]; ring
  rw [h2N]
  have hNle : N ≤ 2 * N := by omega
  have hS : ∀ j ∈ Ico N (2 * N), j < 2 ^ (k + 1 + n) := fun j hj => by
    have h1 := (Finset.mem_Ico.1 hj).2
    have h2 : 2 * N ≤ 2 ^ (k + 1 + n) := by
      rw [← h2N]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hp : gridPt (k + 1 + n) N = ((2 : ℝ) ^ (k + 1))⁻¹ := gridPt_two_pow rfl
  have hq : gridPt (k + 1 + n) (2 * N) = ((2 : ℝ) ^ k)⁻¹ := by
    rw [← h2N]; exact gridPt_two_pow (by omega)
  set c : ℝ := 3 / 2 ^ (k + 2)
  set e : ℕ := k + 1 + n
  have hcellc : ∀ j ∈ Ico N (2 * N), IntervalIntegrable (fun u => (u - c) * f u) volume
      (gridPt e j) (gridPt e (j + 1)) := fun j hj =>
    (intervalIntegrable_cell hf (hS j hj)).continuousOn_mul
      ((continuous_id.sub continuous_const).continuousOn)
  have hlim : dyadicMomentLim f k = ∑ j ∈ Ico N (2 * N),
      ∫ u in gridPt e j..gridPt e (j + 1), (u - c) * f u := by
    rw [dyadicMomentLim, intervalIntegral.sum_integral_adjacent_intervals_Ico (a := gridPt e) hNle
      fun j hj => hcellc j (Finset.mem_Ico.2 hj), hp, hq]
  have habs : ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, |f u| =
      ∑ j ∈ Ico N (2 * N), ∫ u in gridPt e j..gridPt e (j + 1), |f u| := by
    rw [intervalIntegral.sum_integral_adjacent_intervals_Ico (a := gridPt e) hNle
      fun j hj => (intervalIntegrable_cell hf (hS j (Finset.mem_Ico.2 hj))).abs, hp, hq]
  rw [hlim, habs, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hI := intervalIntegrable_cell hf (hS j hj)
  have hle : gridPt e j ≤ gridPt e (j + 1) := (gridPt_lt e j).le
  have hdiff : (((j : ℝ) + 1 / 2) / 2 ^ e - c) * (∫ u in gridPt e j..gridPt e (j + 1), f u) -
      ∫ u in gridPt e j..gridPt e (j + 1), (u - c) * f u =
      ∫ u in gridPt e j..gridPt e (j + 1), (((j : ℝ) + 1 / 2) / 2 ^ e - u) * f u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hI.const_mul _) (hcellc j hj)]
    congr 1
    funext u
    ring
  rw [hdiff]
  refine (intervalIntegral.abs_integral_le_integral_abs hle).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hle
    ((hI.continuousOn_mul (continuous_const.sub continuous_id).continuousOn).abs)
    (hI.abs.const_mul _) fun u hu => ?_
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have h1 := hu.1
  have h2 := hu.2
  unfold gridPt at h1 h2
  have hpos : (0 : ℝ) < 2 ^ e := by positivity
  rw [abs_le]
  have e1 : ((2 : ℝ) ^ (e + 1))⁻¹ = (1 / 2) / 2 ^ e := by rw [pow_succ]; field_simp
  rw [e1]
  push_cast at h2
  constructor
  · have : ((j : ℝ) + 1) / 2 ^ e = ((j : ℝ) + 1 / 2) / 2 ^ e + (1 / 2) / 2 ^ e := by ring
    linarith
  · have : (j : ℝ) / 2 ^ e = ((j : ℝ) + 1 / 2) / 2 ^ e - (1 / 2) / 2 ^ e := by ring
    linarith

/-- `W_d → ∫_{D_k} (u − c_k) f(u) du` as `d → ∞`. -/
lemma tendsto_dyadicMoment (hf : IntervalIntegrable f volume 0 1) (k : ℕ) :
    Tendsto (fun d => dyadicMoment f d k) atTop (𝓝 (dyadicMomentLim f k)) := by
  set A := ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, |f u|
  have h0 : Tendsto (fun d : ℕ => ((2 : ℝ) ^ (d + 1))⁻¹ * A) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp
      (tendsto_add_atTop_nat 1))).mul_const A
    rw [zero_mul] at h
    exact h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun d => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop (k + 1)] with d hd
  rw [Real.norm_eq_abs]
  exact abs_dyadicMoment_sub_le hf hd

/-- **The limit error on a dyadic interval**: `E_k = ∫_{D_k} f² − 2^{k+1} (∫_{D_k} f)² −
12·8^{k+1} (∫_{D_k} (u − c_k) f(u) du)²`, the least mean-square error of an affine function of `u`
on `D_k = [2^{−(k+1)}, 2^{−k}]` (`dyadicAffineErr_isLeast`). -/
noncomputable def dyadicAffineErr (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u ^ 2) -
    2 ^ (k + 1) * (∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u) ^ 2 -
    12 * 8 ^ (k + 1) * dyadicMomentLim f k ^ 2

/-- **The true mechanism: on each dyadic interval the error of method 3 converges** (Haas–Giles
2025, §3.4, p. 7: "the error due to the other intervals remains the same" holds only in the
limit).  If `f`, `f²` are interval-integrable on `[0, 1]`, the mean-square error of the
least-squares line on the cells of `D_k = [2^{−(k+1)}, 2^{−k}]` (for `k ≥ 1` the error of method 3
on `D_k`, `method3_half_eq`) tends, as `d → ∞`, to `E_k` (`dyadicAffineErr`), the least
mean-square error of an affine function of `u` on `D_k`. -/
theorem tendsto_dyadic_groupMSE (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (k : ℕ) :
    Tendsto (fun d => groupMSE f d (Ico (2 ^ (d - k - 1)) (2 ^ (d - k)))) atTop
      (𝓝 (dyadicAffineErr f k)) := by
  -- `N²/(N² − 1) → 1` for `N = 2^{d−k−1}`
  have hN : Tendsto (fun d : ℕ => ((2 : ℝ) ^ (d - k - 1))) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp
      ((tendsto_sub_atTop_nat 1).comp (tendsto_sub_atTop_nat k))
  have hN2 : Tendsto (fun d : ℕ => ((2 : ℝ) ^ (d - k - 1)) ^ 2 - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_pow_atTop two_ne_zero).comp hN)
  have hr : Tendsto (fun d : ℕ => 1 + (((2 : ℝ) ^ (d - k - 1)) ^ 2 - 1)⁻¹) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hN2.inv_tendsto_atTop
    rw [add_zero] at h
    exact h
  have hlim := ((tendsto_const_nhds (x := (∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹,
      f u ^ 2) - 2 ^ (k + 1) * (∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u) ^ 2)).sub
    (((tendsto_const_nhds (x := (12 : ℝ) * 8 ^ (k + 1))).mul hr).mul
      ((tendsto_dyadicMoment hf k).pow 2)))
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (k + 2)] with d hd
  rw [dyadic_groupMSE_eq hf hf2 hd]
  have h1 : (1 : ℝ) < ((2 : ℝ) ^ (d - k - 1)) ^ 2 := by
    have : (2 : ℝ) ≤ (2 : ℝ) ^ (d - k - 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (d - k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hne : ((2 : ℝ) ^ (d - k - 1)) ^ 2 - 1 ≠ 0 := by linarith
  have e : 1 + (((2 : ℝ) ^ (d - k - 1)) ^ 2 - 1)⁻¹ =
      ((2 : ℝ) ^ (d - k - 1)) ^ 2 / (((2 : ℝ) ^ (d - k - 1)) ^ 2 - 1) := by
    field_simp
    ring
  rw [e]

/-- Expanding `∫_{D_k} (a + β (u − c_k) − f)²` (using `∫_{D_k} (u − c_k) = 0` and
`∫_{D_k} (u − c_k)² = |D_k|³/12`). -/
lemma integral_affine_sub_sq (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (k : ℕ) (a β : ℝ) :
    ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, (a + β * (u - 3 / 2 ^ (k + 2)) - f u) ^ 2 =
      a ^ 2 * ((2 : ℝ) ^ (k + 1))⁻¹ + β ^ 2 * (((2 : ℝ) ^ (k + 1))⁻¹) ^ 3 / 12 -
        2 * a * (∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u) -
        2 * β * dyadicMomentLim f k +
        ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u ^ 2 := by
  rw [dyadicMomentLim]
  have h1 : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  have h2 : (2 : ℝ) ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  set p : ℝ := ((2 : ℝ) ^ (k + 1))⁻¹ with hp
  set q : ℝ := ((2 : ℝ) ^ k)⁻¹ with hq
  set c : ℝ := 3 / 2 ^ (k + 2) with hc
  have hpq : p ≤ q := inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (by omega))
  have hq1 : q ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  have hI := intervalIntegrable_sub01 hf (by positivity) hpq hq1
  have hI2 := intervalIntegrable_sub01 hf2 (by positivity) hpq hq1
  have hIc : IntervalIntegrable (fun u => (u - c) * f u) volume p q :=
    hI.continuousOn_mul (continuous_id.sub continuous_const).continuousOn
  have hpoly : IntervalIntegrable (fun u => a ^ 2 + 2 * a * β * (u - c) + β ^ 2 * (u - c) ^ 2)
      volume p q := by
    apply Continuous.intervalIntegrable
    fun_prop
  have e : ∀ u, (a + β * (u - c) - f u) ^ 2 =
      (a ^ 2 + 2 * a * β * (u - c) + β ^ 2 * (u - c) ^ 2) -
        (2 * a * f u + 2 * β * ((u - c) * f u)) + f u ^ 2 := fun u => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (hpoly.sub ((hI.const_mul _).add (hIc.const_mul _))) hI2,
    intervalIntegral.integral_sub hpoly ((hI.const_mul _).add (hIc.const_mul _)),
    intervalIntegral.integral_add (hI.const_mul _) (hIc.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hpoly_eq : ∫ u in p..q, (a ^ 2 + 2 * a * β * (u - c) + β ^ 2 * (u - c) ^ 2) =
      a ^ 2 * p + β ^ 2 * p ^ 3 / 12 := by
    rw [intervalIntegral.integral_comp_sub_right
      (fun x => a ^ 2 + 2 * a * β * x + β ^ 2 * x ^ 2) c]
    have hqc : q - c = p / 2 := by
      rw [hq, hc, hp, h1, h2]; field_simp; ring
    have hpc : p - c = -(p / 2) := by
      rw [hc, hp, h1, h2]; field_simp; ring
    rw [hqc, hpc, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    · simp only [smul_eq_mul]
      ring
    all_goals
      apply Continuous.intervalIntegrable
      fun_prop
  rw [hpoly_eq]
  ring

/-- `∫_{D_k} (α + β u − f)² = E_k + |D_k| (α + β c_k − 2^{k+1} ∫_{D_k} f)² +
|D_k|³/12 (β − 12·8^{k+1} ∫_{D_k} (u − c_k) f)²`, `|D_k| = 2^{−(k+1)}`. -/
lemma integral_affine_eq (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (k : ℕ) (α β : ℝ) :
    ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, (α + β * u - f u) ^ 2 =
      dyadicAffineErr f k + ((2 : ℝ) ^ (k + 1))⁻¹ * (α + β * (3 / 2 ^ (k + 2)) -
        2 ^ (k + 1) * ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u) ^ 2 +
        (((2 : ℝ) ^ (k + 1))⁻¹) ^ 3 / 12 * (β - 12 * 8 ^ (k + 1) * dyadicMomentLim f k) ^ 2 := by
  have e : ∀ u, (α + β * u - f u) ^ 2 =
      ((α + β * (3 / 2 ^ (k + 2))) + β * (u - 3 / 2 ^ (k + 2)) - f u) ^ 2 := fun u => by ring
  simp_rw [e]
  rw [integral_affine_sub_sq hf hf2, dyadicAffineErr]
  have h8 : (8 : ℝ) ^ (k + 1) = (2 ^ (k + 1)) ^ 3 := by
    rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, mul_comm]
  rw [h8]
  generalize dyadicMomentLim f k = W
  generalize ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u = I0
  generalize ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u ^ 2 = I2
  have hT : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **The limit is the best affine approximation on each dyadic interval** (identifying the
constant of Haas–Giles 2025, §3.4, p. 7: "the dyadic intervals give `MSE → C`").  If `f`, `f²`
are interval-integrable on `[0, 1]`, `E_k` (`dyadicAffineErr`) is the least value of
`∫_{D_k} (α + β u − f(u))² du` over `α, β ∈ ℝ`, `D_k = [2^{−(k+1)}, 2^{−k}]`. -/
theorem dyadicAffineErr_isLeast (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (k : ℕ) :
    IsLeast (Set.range fun ab : ℝ × ℝ =>
      ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, (ab.1 + ab.2 * u - f u) ^ 2)
      (dyadicAffineErr f k) := by
  set β₀ : ℝ := 12 * 8 ^ (k + 1) * dyadicMomentLim f k
  set α₀ : ℝ := 2 ^ (k + 1) * (∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u) -
    β₀ * (3 / 2 ^ (k + 2))
  refine ⟨⟨(α₀, β₀), ?_⟩, ?_⟩
  · simp only
    rw [integral_affine_eq hf hf2]
    simp [α₀, β₀]
  · rintro _ ⟨⟨α, β⟩, rfl⟩
    simp only
    rw [integral_affine_eq hf hf2]
    have h1 : 0 ≤ ((2 : ℝ) ^ (k + 1))⁻¹ * (α + β * (3 / 2 ^ (k + 2)) -
        2 ^ (k + 1) * ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u) ^ 2 := by positivity
    have h2 : 0 ≤ (((2 : ℝ) ^ (k + 1))⁻¹) ^ 3 / 12 *
        (β - 12 * 8 ^ (k + 1) * dyadicMomentLim f k) ^ 2 := by positivity
    linarith

/-- The first dyadic interval `{0, 1}` (the cells of `[0, 2^{1−d}]`) contributes `→ 0`. -/
lemma tendsto_groupMSE_range_two (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) :
    Tendsto (fun d => groupMSE f d (range 2)) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hx : Tendsto (fun d : ℕ => ((2 : ℝ) ^ d)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hx01 : ∀ d : ℕ, ((2 : ℝ) ^ d)⁻¹ ∈ Set.uIcc (0 : ℝ) 1 := fun d => by
    rw [Set.uIcc_of_le zero_le_one]
    exact inv_two_pow_mem d
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_integral_zero hf2 hx hx01) (fun d => groupMSE_nonneg (d + 1) _) fun d => ?_
  have hS : ∀ j ∈ range 2, j < 2 ^ (d + 1) := fun j hj => by
    have h1 := Finset.mem_range.1 hj
    have h2 : 2 ≤ 2 ^ (d + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine (groupMSE_le hf hf2 hS).trans (le_of_eq ?_)
  rw [intervalIntegral.sum_integral_adjacent_intervals (a := gridPt (d + 1))
    fun j hj => intervalIntegrable_cell hf2 (hS j (Finset.mem_range.2 hj))]
  congr 1
  · simp [gridPt]
  · rw [gridPt, pow_succ]
    push_cast
    field_simp

/-- `E_k ≥ 0`: it is the limit of the nonnegative errors `groupMSE`. -/
lemma dyadicAffineErr_nonneg (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (k : ℕ) : 0 ≤ dyadicAffineErr f k :=
  ge_of_tendsto (tendsto_dyadic_groupMSE hf hf2 k)
    (Eventually.of_forall fun d => groupMSE_nonneg d _)

/-- `E_k ≤ ∫_{D_k} f²`: the affine function `0` is a competitor in `dyadicAffineErr_isLeast`. -/
lemma dyadicAffineErr_le (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (k : ℕ) :
    dyadicAffineErr f k ≤ ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u ^ 2 :=
  (dyadicAffineErr_isLeast hf hf2 k).2 ⟨(0, 0), by simp⟩

/-- The limit errors `E_{k+1}` are summable (dominated by `∫_{D_{k+1}} f²`). -/
lemma summable_dyadicAffineErr (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) :
    Summable fun k => dyadicAffineErr f (k + 1) :=
  Summable.of_nonneg_of_le (fun k => dyadicAffineErr_nonneg hf hf2 (k + 1))
    (fun k => dyadicAffineErr_le hf hf2 (k + 1)) (summable_dyadic_sq hf2)

/-- `E_k > 0` if `f` is strongly concave on `D_k = [2^{−(k+1)}, 2^{−k}]`: the errors of the affine
values of method 3 on `D_k` are at least `c > 0` for `d ≥ k + 3` (`dyadic_mse_ge`, LUTLimits), and
they tend to `E_k` (`tendsto_dyadic_groupMSE`). -/
lemma dyadicAffineErr_pos (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {k : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (hconc : ∀ u s : ℝ, ((2 : ℝ) ^ (k + 1))⁻¹ ≤ u → 0 ≤ s → u + 2 * s ≤ ((2 : ℝ) ^ k)⁻¹ →
      μ * s ^ 2 ≤ 2 * f (u + s) - f u - f (u + 2 * s)) :
    0 < dyadicAffineErr f k := by
  obtain ⟨c, hc, hbd⟩ := dyadic_mse_ge hf hf2 hμ hconc
  refine lt_of_lt_of_le hc (ge_of_tendsto (tendsto_dyadic_groupMSE hf hf2 k) ?_)
  filter_upwards [eventually_ge_atTop (k + 3)] with d hd
  obtain ⟨a, b, hab⟩ := lsqFit_affine (Ico (2 ^ (d - k - 1)) (2 ^ (d - k))) (lutValue f d)
  simp only [groupMSE, hab]
  exact hbd d hd a b

/-- **The constant `C` of Haas–Giles 2025, §3.4**: `C = 2 ∑_{k≥1} E_k`, twice the sum over the
dyadic intervals `D_k = [2^{−(k+1)}, 2^{−k}]` of `[0, ½]` of the least mean-square error of an
affine function on `D_k` (`dyadicAffineErr`, `dyadicAffineErr_isLeast`). -/
noncomputable def method3Limit (f : ℝ → ℝ) : ℝ := 2 * ∑' k, dyadicAffineErr f (k + 1)

/-- **Dyadic intervals: the MSE converges** (Haas–Giles 2025, §3.4, p. 7: "as `d` tends to
infinity, ... the dyadic intervals give `MSE → C`").  If `f`, `f²` are interval-integrable on
`[0, 1]` and `f(1 − u) = −f(u)` (as for `Φ⁻¹`), the mean-square error of method 3 tends to
`C = 2 ∑_{k≥1} E_k` (`method3Limit`).  Deviation from the paper's explanation: the error on each
dyadic interval `D_k` is not constant in `d` (`dyadic_groupMSE_eq`, `groupMSE_odd_quadratic`) but
converges to `E_k` (`tendsto_dyadic_groupMSE`), and the sum converges by dominated convergence
(`tendsto_sum_range_of_dominated`), with the summable bound `∫_{D_k} f²` (`groupMSE_le`). -/
theorem tendsto_method3MSE (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (hodd : ∀ u, f (1 - u) = -f u) :
    Tendsto (method3MSE f) atTop (𝓝 (method3Limit f)) := by
  have hT := tendsto_sum_range_of_dominated (φ := fun d => d - 2)
    (F := fun d k => groupMSE f d (Ico (2 ^ (d - (k + 1) - 1)) (2 ^ (d - (k + 1)))))
    (g := fun k => dyadicAffineErr f (k + 1)) (tendsto_sub_atTop_nat 2)
    (summable_dyadic_sq hf2) (fun d k _ => groupMSE_nonneg d _) (fun d k hk => ?_)
    fun k => tendsto_dyadic_groupMSE hf hf2 (k + 1)
  · have hlim := ((tendsto_groupMSE_range_two hf hf2).add hT).const_mul 2
    rw [zero_add] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with d hd
    rw [method3MSE_eq_two_mul hodd (by omega), method3_half_eq hd]
  · have hk' : k + 1 + 1 ≤ d := by omega
    have hS : ∀ j ∈ Ico (2 ^ (d - (k + 1) - 1)) (2 ^ (d - (k + 1))), j < 2 ^ d := fun j hj =>
      lt_of_lt_of_le (Finset.mem_Ico.1 hj).2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine (groupMSE_le hf hf2 hS).trans (le_of_eq ?_)
    rw [sum_dyadic_cells hf2 hk']

/-- **The limit is positive** (Haas–Giles 2025, §3.4, p. 7: "for some positive constant `C`").
If `f`, `f²` are interval-integrable on `[0, 1]` and `f` is strongly concave on one dyadic
interval `[2^{−(k+1)}, 2^{−k}]`, `k ≥ 1`, i.e. `2f(u + s) − f(u) − f(u + 2s) ≥ μ s²` with `μ > 0`
(as `Φ⁻¹` is for `k ≥ 2`, see `method3_mse_ge`), then `C = 2 ∑_{k≥1} E_k > 0`: every `E_k` is
`≥ 0`, they are summable, and the concave one is `> 0` (`dyadicAffineErr_nonneg`,
`summable_dyadicAffineErr`, `dyadicAffineErr_pos`).  No oddness of `f` is needed: `C` only
depends on `f` on `[0, ½]` (oddness is used only for the convergence, `tendsto_method3MSE`). -/
theorem method3Limit_pos (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1)
    {k : ℕ} (hk : 1 ≤ k) {μ : ℝ} (hμ : 0 < μ)
    (hconc : ∀ u s : ℝ, ((2 : ℝ) ^ (k + 1))⁻¹ ≤ u → 0 ≤ s → u + 2 * s ≤ ((2 : ℝ) ^ k)⁻¹ →
      μ * s ^ 2 ≤ 2 * f (u + s) - f u - f (u + 2 * s)) :
    0 < method3Limit f := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact mul_pos two_pos ((summable_dyadicAffineErr hf hf2).tsum_pos
    (fun j => dyadicAffineErr_nonneg hf hf2 (j + 1)) k' (dyadicAffineErr_pos hf hf2 hμ hconc))

/-- **Dyadic intervals give `MSE → C > 0`** (Haas–Giles 2025, §3.4, p. 7: "the dyadic intervals
give `MSE → C`, for some positive constant `C`").  If `f`, `f²` are interval-integrable on
`[0, 1]`, `f(1 − u) = −f(u)` and `f` is strongly concave on one dyadic interval
`[2^{−(k+1)}, 2^{−k}]`, `k ≥ 1` (all true for `Φ⁻¹`, with `k = 2`), the mean-square error of
method 3 converges to a constant `C > 0`. -/
theorem exists_tendsto_method3MSE (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (hodd : ∀ u, f (1 - u) = -f u)
    {k : ℕ} (hk : 1 ≤ k) {μ : ℝ} (hμ : 0 < μ)
    (hconc : ∀ u s : ℝ, ((2 : ℝ) ^ (k + 1))⁻¹ ≤ u → 0 ≤ s → u + 2 * s ≤ ((2 : ℝ) ^ k)⁻¹ →
      μ * s ^ 2 ≤ 2 * f (u + s) - f u - f (u + 2 * s)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (method3MSE f) atTop (𝓝 C) :=
  ⟨method3Limit f, method3Limit_pos hf hf2 hk hμ hconc, tendsto_method3MSE hf hf2 hodd⟩

/-- The LUT values of `f(u) = u − ½` are `Z_j = (j + ½) 2^{−d} − ½`, affine in `j`. -/
lemma lutValue_sub_half (d j : ℕ) :
    lutValue (fun u => u - 1 / 2) d j = ((j : ℝ) + 1 / 2) / 2 ^ d - 1 / 2 := by
  have hid : IntervalIntegrable (fun u : ℝ => u) volume (gridPt d j) (gridPt d (j + 1)) :=
    continuous_id.intervalIntegrable _ _
  rw [lutValue, intervalIntegral.integral_sub hid intervalIntegrable_const, integral_id,
    intervalIntegral.integral_const, smul_eq_mul, gridPt_succ_sub]
  unfold gridPt
  push_cast
  have h : (2 : ℝ) ^ d ≠ 0 := by positivity
  field_simp
  ring

/-- **Counterexample: the error on the other intervals does not remain the same** (Haas–Giles
2025, §3.4, p. 7: "when `d` increases by 1 the MSE is reduced only in the interval closest to 0,
so the error due to the other intervals remains the same").  For `f(u) = u − ½` (which is odd
about `½`, like `Φ⁻¹`) and `d ≥ k + 1`, the error of the least-squares line on the cells of
`D_k = [2^{−(k+1)}, 2^{−k}]` (for `k ≥ 1` the error of method 3 on `D_k`) is
`2^{−(k+1)} 4^{−d}/12`: it is divided by 4 each time `d` increases by 1.  For this `f` every
`E_k` is `0`, so `C = 0`: the example lies outside the regime `MSE → C > 0` of the paper's claim
and only shows that the mechanism is not a structural property of the segmentation; see
`groupMSE_odd_quadratic` for an exact counterexample with `C > 0`.  Numerically, for `Φ⁻¹` the
claim holds up to an excess divided by `≈ 4` per bit: for `k = 1` the error decreases from
`2.37·10⁻³` at `d = 3` to `8.44·10⁻⁶` at `d = 9`, with limit `7.86·10⁻⁶`. -/
theorem groupMSE_sub_half {d k : ℕ} (hd : k + 1 ≤ d) :
    groupMSE (fun u => u - 1 / 2) d (Ico (2 ^ (d - k - 1)) (2 ^ (d - k))) =
      ((2 : ℝ) ^ (k + 1))⁻¹ * (((2 : ℝ) ^ d)⁻¹) ^ 2 / 12 := by
  set S := Ico (2 ^ (d - k - 1)) (2 ^ (d - k))
  set g : ℝ → ℝ := fun u => u - 1 / 2
  -- the LUT values are affine in `j`, so the least-squares fit reproduces them
  have hfit : ∀ j ∈ S, lsqFit S (lutValue g d) j = lutValue g d j := by
    have hle := sum_sq_lsqFit_le S (lutValue g d) ((1 / 2) / 2 ^ d - 1 / 2) ((2 : ℝ) ^ d)⁻¹
    have h0 : ∑ j ∈ S, ((1 / 2) / 2 ^ d - 1 / 2 + ((2 : ℝ) ^ d)⁻¹ * j - lutValue g d j) ^ 2
        = 0 := Finset.sum_eq_zero fun j _ => by
      rw [lutValue_sub_half]; field_simp; ring
    rw [h0] at hle
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg
      (lsqFit S (lutValue g d) j - lutValue g d j)).1 (le_antisymm hle
        (Finset.sum_nonneg fun j _ => sq_nonneg _))
    intro j hj
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (hz j hj))
  have hcell : ∀ j ∈ S, ∫ u in gridPt d j..gridPt d (j + 1), (lsqFit S (lutValue g d) j - g u) ^ 2
      = (((2 : ℝ) ^ d)⁻¹) ^ 3 / 12 := by
    intro j hj
    rw [hfit j hj, lutValue_sub_half]
    have e : ∀ u, (((j : ℝ) + 1 / 2) / 2 ^ d - 1 / 2 - g u) ^ 2 =
        (u - ((j : ℝ) + 1 / 2) / 2 ^ d) ^ 2 := fun u => by simp only [g]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ 2), integral_pow]
    unfold gridPt
    push_cast
    have h : (2 : ℝ) ^ d ≠ 0 := by positivity
    field_simp
    ring
  rw [groupMSE, Finset.sum_congr rfl hcell, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hc : 2 ^ (d - k) - 2 ^ (d - k - 1) = 2 ^ (d - k - 1) := by
    have : 2 ^ (d - k) = 2 * 2 ^ (d - k - 1) := by
      rw [← pow_succ', show d - k - 1 + 1 = d - k by omega]
    omega
  rw [hc]
  push_cast
  have hpow : (2 : ℝ) ^ d = 2 ^ (k + 1) * 2 ^ (d - k - 1) := by
    rw [← pow_add, show k + 1 + (d - k - 1) = d by omega]
  rw [hpow]
  have h1 : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ (d - k - 1) ≠ 0 := by positivity
  field_simp

/-- `∫_p^q (a₀ + a₁ u + a₂ u² + a₃ u³) du`. -/
lemma integral_cubic (p q a₀ a₁ a₂ a₃ : ℝ) :
    ∫ u in p..q, (a₀ + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3) =
      a₀ * (q - p) + a₁ * (q ^ 2 - p ^ 2) / 2 + a₂ * (q ^ 3 - p ^ 3) / 3 +
        a₃ * (q ^ 4 - p ^ 4) / 4 := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow, integral_pow]
  · simp only [smul_eq_mul]
    push_cast
    ring
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

/-- If `f(u) = α + βu + γu²` on `D_k = [2^{−(k+1)}, 2^{−k}]`, then
`∫_{D_k} (u − c_k) f(u) du = (β + 2γ c_k) |D_k|³/12` (`f'(c_k) |D_k|³/12`). -/
lemma dyadicMomentLim_quadratic {k : ℕ} {α β γ : ℝ}
    (hq : ∀ u ∈ Set.Icc ((2 : ℝ) ^ (k + 1))⁻¹ ((2 : ℝ) ^ k)⁻¹, f u = α + β * u + γ * u ^ 2) :
    dyadicMomentLim f k =
      (β + 2 * γ * (3 / 2 ^ (k + 2))) * (((2 : ℝ) ^ (k + 1))⁻¹) ^ 3 / 12 := by
  have hpq : ((2 : ℝ) ^ (k + 1))⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := inv_two_pow_anti (by omega)
  have hcongr : dyadicMomentLim f k = ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹,
      (-(3 / 2 ^ (k + 2) * α) + (α - 3 / 2 ^ (k + 2) * β) * u +
        (β - 3 / 2 ^ (k + 2) * γ) * u ^ 2 + γ * u ^ 3) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hpq] at hu
    rw [hq u hu]
    ring
  rw [hcongr, integral_cubic]
  have hq2 : ((2 : ℝ) ^ k)⁻¹ = 2 * ((2 : ℝ) ^ (k + 1))⁻¹ := by
    rw [pow_succ]; field_simp
  have hc : (3 : ℝ) / 2 ^ (k + 2) = 3 * ((2 : ℝ) ^ (k + 1))⁻¹ / 2 := by
    rw [show k + 2 = k + 1 + 1 by ring, pow_succ]; field_simp
  rw [hq2, hc]
  ring

/-- If `f(u) = α + βu + γu²` on `D_k` and `d ≥ k + 1`, the Riemann sum `W_d` (`dyadicMoment`) is
`(β + 2γ c_k) 2^{−3d} (N³ − N)/12` with `N = 2^{d−k−1}`. -/
lemma dyadicMoment_quadratic {d k : ℕ} {α β γ : ℝ} (hd : k + 1 ≤ d)
    (hq : ∀ u ∈ Set.Icc ((2 : ℝ) ^ (k + 1))⁻¹ ((2 : ℝ) ^ k)⁻¹, f u = α + β * u + γ * u ^ 2) :
    dyadicMoment f d k = (β + 2 * γ * (3 / 2 ^ (k + 2))) * (((2 : ℝ) ^ d)⁻¹) ^ 3 *
      (((2 : ℝ) ^ (d - k - 1)) ^ 3 - 2 ^ (d - k - 1)) / 12 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = k + 1 + n := ⟨d - (k + 1), by omega⟩
  have hn1 : k + 1 + n - k - 1 = n := by omega
  have hn2 : k + 1 + n - k = n + 1 := by omega
  rw [dyadicMoment, hn1, hn2]
  set N : ℕ := 2 ^ n with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have h2N : 2 ^ (n + 1) = 2 * N := by rw [pow_succ]; ring
  have hcast : ((2 : ℝ) ^ n) = (N : ℝ) := by rw [hNdef]; push_cast; ring
  rw [h2N, hcast]
  have hp : gridPt (k + 1 + n) N = ((2 : ℝ) ^ (k + 1))⁻¹ := gridPt_two_pow rfl
  have hq' : gridPt (k + 1 + n) (2 * N) = ((2 : ℝ) ^ k)⁻¹ := by
    rw [← h2N]; exact gridPt_two_pow (by omega)
  set h : ℝ := ((2 : ℝ) ^ (k + 1 + n))⁻¹ with hh
  have hg : ∀ j : ℕ, gridPt (k + 1 + n) j = j * h := fun j => by rw [gridPt, hh, div_eq_mul_inv]
  -- the centre `c_k = 3Nh/2`
  have hc : (3 : ℝ) / 2 ^ (k + 2) = 3 * N * h / 2 := by
    rw [hh, ← hcast, pow_add (2 : ℝ) (k + 1) n]
    field_simp
    ring
  -- each summand, with `y_j = j − (3N − 1)/2`
  have hsum : ∀ j ∈ Ico N (2 * N), (((j : ℝ) + 1 / 2) / 2 ^ (k + 1 + n) - 3 / 2 ^ (k + 2)) *
      ∫ u in gridPt (k + 1 + n) j..gridPt (k + 1 + n) (j + 1), f u =
      h ^ 2 * ((α + β * (3 / 2 ^ (k + 2)) + γ * (3 / 2 ^ (k + 2)) ^ 2 + γ * h ^ 2 / 12) *
        ((j : ℝ) - (3 * N - 1) / 2) + (β + 2 * γ * (3 / 2 ^ (k + 2))) * h *
          ((j : ℝ) - (3 * N - 1) / 2) ^ 2 + γ * h ^ 2 * ((j : ℝ) - (3 * N - 1) / 2) ^ 3) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
    have hlo : ((2 : ℝ) ^ (k + 1))⁻¹ ≤ gridPt (k + 1 + n) j := hp ▸ gridPt_mono _ hj1
    have hhi : gridPt (k + 1 + n) (j + 1) ≤ ((2 : ℝ) ^ k)⁻¹ := hq' ▸ gridPt_mono _ hj2
    have hcongr : ∫ u in gridPt (k + 1 + n) j..gridPt (k + 1 + n) (j + 1), f u =
        ∫ u in gridPt (k + 1 + n) j..gridPt (k + 1 + n) (j + 1),
          (α + β * u + γ * u ^ 2 + 0 * u ^ 3) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (gridPt_lt _ j).le] at hu
      rw [hq u ⟨hlo.trans hu.1, hu.2.trans hhi⟩]
      ring
    rw [hcongr, integral_cubic, hg, hg, div_eq_mul_inv ((j : ℝ) + 1 / 2), ← hh, hc]
    push_cast
    ring
  have hy : ∑ j ∈ Ico N (2 * N), ((j : ℝ) - (3 * N - 1) / 2) = 0 := by
    rw [← finMean_Ico hN1]; exact sum_sub_finMean _ _
  have hy2 : ∑ j ∈ Ico N (2 * N), ((j : ℝ) - (3 * N - 1) / 2) ^ 2 = ((N : ℝ) ^ 3 - N) / 12 := by
    rw [← finMean_Ico hN1]; exact sum_sq_Ico_sub hN1
  rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hy, hy2,
    sum_cube_Ico_sub]
  ring

/-- **The error of method 3 on a dyadic interval where `f` is quadratic** (Haas–Giles 2025, §3.4,
p. 7: "the error due to the other intervals remains the same" is not exact).  If `f`, `f²` are
interval-integrable on `[0, 1]` and `f(u) = α + βu + γu²` on `D_k = [2^{−(k+1)}, 2^{−k}]`, then
for `d ≥ k + 2` the error of the least-squares line on the cells of `D_k` (for `k ≥ 1` the error of
method 3 on `D_k`, `method3_half_eq`) is `E_k + f'(c_k)² |D_k| 4^{−d}/12`, with
`f'(c_k) = β + 2γ c_k`, `c_k = 3·2^{−(k+2)}`, `|D_k| = 2^{−(k+1)}`: it exceeds its limit `E_k`
(`dyadicAffineErr`) by an amount divided by exactly 4 at each bit, unless `f'(c_k) = 0`.  (For
`Φ⁻¹` the excess on `D_1` is also divided by `≈ 4` per bit, numerically.) -/
theorem groupMSE_quadratic (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {d k : ℕ} {α β γ : ℝ}
    (hq : ∀ u ∈ Set.Icc ((2 : ℝ) ^ (k + 1))⁻¹ ((2 : ℝ) ^ k)⁻¹, f u = α + β * u + γ * u ^ 2)
    (hd : k + 2 ≤ d) :
    groupMSE f d (Ico (2 ^ (d - k - 1)) (2 ^ (d - k))) = dyadicAffineErr f k +
      (β + 2 * γ * (3 / 2 ^ (k + 2))) ^ 2 * ((2 : ℝ) ^ (k + 1))⁻¹ * (((2 : ℝ) ^ d)⁻¹) ^ 2 / 12 := by
  rw [dyadic_groupMSE_eq hf hf2 hd, dyadicAffineErr, dyadicMoment_quadratic (by omega) hq,
    dyadicMomentLim_quadratic hq]
  have hM : (2 : ℝ) ≤ (2 : ℝ) ^ (d - k - 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (d - k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hd' : (2 : ℝ) ^ d = 2 ^ (k + 1) * 2 ^ (d - k - 1) := by
    rw [← pow_add]; congr 1; omega
  have h8 : (8 : ℝ) ^ (k + 1) = (2 ^ (k + 1)) ^ 3 := by
    rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, mul_comm]
  rw [hd', h8]
  generalize β + 2 * γ * (3 / 2 ^ (k + 2)) = B
  generalize ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u = I1
  generalize ∫ u in ((2 : ℝ) ^ (k + 1))⁻¹..((2 : ℝ) ^ k)⁻¹, f u ^ 2 = I2
  generalize (2 : ℝ) ^ (d - k - 1) = M at hM ⊢
  have hT : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  generalize (2 : ℝ) ^ (k + 1) = T at hT ⊢
  have hM1 : M ^ 2 - 1 ≠ 0 := by nlinarith
  have hM0 : M ≠ 0 := by positivity
  field_simp
  ring

/-- **Counterexample with `C > 0`: the error on the other intervals does not remain the same**
(Haas–Giles 2025, §3.4, p. 7: "the dyadic intervals give `MSE → C`, for some positive constant
`C`. The latter is because with our simple dyadic segmentation, when `d` increases by 1 the MSE is
reduced only in the interval closest to 0, so the error due to the other intervals remains the
same").  Let `f(u) = (u − ½)|u − ½|`: it is odd about `½` like `Φ⁻¹`, and `f = −(u − ½)²` is
strongly concave on `[0, ½]`.  Then the MSE of method 3 converges to `C = 2 ∑_{k≥1} E_k > 0`, every
`E_k`, `k ≥ 1`, is positive, and yet for `d ≥ k + 2` the error of method 3 on
`D_k = [2^{−(k+1)}, 2^{−k}]` is `E_k + (1 − 3·2^{−(k+1)})² 2^{−(k+1)} 4^{−d}/12`
(`groupMSE_quadratic`, `f'(c_k) = 1 − 3·2^{−(k+1)} > 0`), which strictly decreases with `d` on
every interval, not only on the one closest to `0`. -/
theorem groupMSE_odd_quadratic :
    0 < method3Limit (fun u => (u - 1 / 2) * |u - 1 / 2|) ∧
    Tendsto (method3MSE fun u => (u - 1 / 2) * |u - 1 / 2|) atTop
      (𝓝 (method3Limit fun u => (u - 1 / 2) * |u - 1 / 2|)) ∧
    ∀ k d : ℕ, 1 ≤ k → k + 2 ≤ d →
      0 < dyadicAffineErr (fun u => (u - 1 / 2) * |u - 1 / 2|) k ∧
      groupMSE (fun u => (u - 1 / 2) * |u - 1 / 2|) d (Ico (2 ^ (d - k - 1)) (2 ^ (d - k))) =
        dyadicAffineErr (fun u => (u - 1 / 2) * |u - 1 / 2|) k +
          (1 - 3 / 2 ^ (k + 1)) ^ 2 * ((2 : ℝ) ^ (k + 1))⁻¹ * (((2 : ℝ) ^ d)⁻¹) ^ 2 / 12 := by
  set g : ℝ → ℝ := fun u => (u - 1 / 2) * |u - 1 / 2| with hgdef
  have hgc : Continuous g :=
    (continuous_id.sub continuous_const).mul (continuous_id.sub continuous_const).abs
  have hf : IntervalIntegrable g volume 0 1 := hgc.intervalIntegrable _ _
  have hf2 : IntervalIntegrable (fun u => g u ^ 2) volume 0 1 :=
    (hgc.pow 2).intervalIntegrable _ _
  have hodd : ∀ u, g (1 - u) = -g u := fun u => by
    simp only [hgdef]
    rw [show 1 - u - 1 / 2 = -(u - 1 / 2) by ring, abs_neg]
    ring
  have hhalf : ∀ u, u ≤ 1 / 2 → g u = -1 / 4 + 1 * u + (-1) * u ^ 2 := fun u hu => by
    simp only [hgdef]
    rw [abs_of_nonpos (by linarith)]
    ring
  have hk2 : ∀ k : ℕ, 1 ≤ k → ((2 : ℝ) ^ k)⁻¹ ≤ 1 / 2 := fun k hk => by
    have h := inv_two_pow_anti (m := 1) hk
    rw [pow_one] at h
    rwa [one_div]
  have hconc : ∀ k : ℕ, 1 ≤ k → ∀ u s : ℝ, ((2 : ℝ) ^ (k + 1))⁻¹ ≤ u → 0 ≤ s →
      u + 2 * s ≤ ((2 : ℝ) ^ k)⁻¹ → 2 * s ^ 2 ≤ 2 * g (u + s) - g u - g (u + 2 * s) := by
    intro k hk u s _ hs hus
    have h12 := hk2 k hk
    rw [hhalf u (by linarith), hhalf (u + s) (by linarith), hhalf (u + 2 * s) (by linarith)]
    have e : 2 * (-1 / 4 + 1 * (u + s) + (-1) * (u + s) ^ 2) - (-1 / 4 + 1 * u + (-1) * u ^ 2) -
        (-1 / 4 + 1 * (u + 2 * s) + (-1) * (u + 2 * s) ^ 2) = 2 * s ^ 2 := by ring
    rw [e]
  refine ⟨method3Limit_pos hf hf2 le_rfl two_pos (hconc 1 le_rfl),
    tendsto_method3MSE hf hf2 hodd, fun k d hk hd =>
      ⟨dyadicAffineErr_pos hf hf2 two_pos (hconc k hk), ?_⟩⟩
  rw [groupMSE_quadratic hf hf2 (α := -1 / 4) (β := 1) (γ := -1)
    (fun u hu => hhalf u (hu.2.trans (hk2 k hk))) hd,
    show (2 : ℝ) ^ (k + 2) = 2 * 2 ^ (k + 1) by ring]
  ring

end Method3

/-! ### Method 1: the mean-square error is of order `2^{−d}/d` -/

section Method1

/-- **The sign bit for method 1** (Haas–Giles 2025, §3.1): if `f(1 − u) = −f(u)`, the
mean-square error of method 1 is twice that on `[0, ½]`. -/
lemma method1MSE_eq_two_mul (hodd : ∀ u, f (1 - u) = -f u) {d : ℕ} (hd : 1 ≤ d) :
    method1MSE f d = 2 * ∑ j ∈ range (2 ^ (d - 1)),
      ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 := by
  rw [method1MSE, sum_range_two_pow_mirror _ hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < 2 ^ d := lt_of_lt_of_le (Finset.mem_range.1 hj)
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le d 1))
  rw [lutValue_mirror hodd hj', integral_mirror_cell hodd hj']
  ring

/-- If `(z − f)² ≤ B` on `I_j`, the error of the LUT value on `I_j` is at most `2^{−d} B` (the mean
`Z_j` does at least as well as `z`). -/
lemma cell_mse_le {d j : ℕ} (hf : IntervalIntegrable f volume (gridPt d j) (gridPt d (j + 1)))
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume (gridPt d j) (gridPt d (j + 1)))
    (z B : ℝ) (hB : ∀ u ∈ Set.Icc (gridPt d j) (gridPt d (j + 1)), (z - f u) ^ 2 ≤ B) :
    ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 ≤ (2 ^ d)⁻¹ * B := by
  have hle : gridPt d j ≤ gridPt d (j + 1) := (gridPt_lt d j).le
  rw [lutValue_eq_intervalMean]
  refine (integral_sq_sub_intervalMean_le (gridPt_lt d j) hf hf2 z).trans ?_
  have h := intervalIntegral.integral_mono_on hle (intervalIntegrable_sq_sub hf hf2 z)
    intervalIntegrable_const hB
  rwa [intervalIntegral.integral_const, smul_eq_mul, gridPt_succ_sub] at h

/-- The constant `K` of the upper Lipschitz bound is nonnegative. -/
lemma nonneg_of_dyadic_block_lip_le {K : ℝ}
    (hup : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → (m : ℝ) * (f v - f u) ^ 2 ≤ K * ((2 : ℝ) ^ m * (v - u)) ^ 2) :
    0 ≤ K := by
  have h := hup 1 le_rfl ((2 : ℝ) ^ (1 + 1))⁻¹ ((2 : ℝ) ^ 1)⁻¹ le_rfl (by norm_num) le_rfl
  have h0 : 0 ≤ ((1 : ℕ) : ℝ) * (f ((2 : ℝ) ^ 1)⁻¹ - f ((2 : ℝ) ^ (1 + 1))⁻¹) ^ 2 := by
    positivity
  have h1 : ((2 : ℝ) ^ 1 * (((2 : ℝ) ^ 1)⁻¹ - ((2 : ℝ) ^ (1 + 1))⁻¹)) ^ 2 = 1 / 4 := by norm_num
  rw [h1] at h
  linarith

/-- `∑_{i<n} (i + 2)/2^i = 6 − (2n + 6)/2^n`. -/
lemma sum_range_add_two_div_pow (n : ℕ) :
    ∑ i ∈ range n, ((i : ℝ) + 2) / 2 ^ i = 6 - (2 * n + 6) / 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    field_simp
    ring

/-- `∑_{i<n} 2^{−i}/(n − i) ≤ 6/(n + 1)`. -/
lemma sum_range_inv_pow_div_le (n : ℕ) :
    ∑ i ∈ range n, ((2 : ℝ) ^ i)⁻¹ / ((n - i : ℕ) : ℝ) ≤ 6 / (n + 1) := by
  have hterm : ∀ i ∈ range n, ((2 : ℝ) ^ i)⁻¹ / ((n - i : ℕ) : ℝ) ≤
      (((i : ℝ) + 2) / 2 ^ i) / (n + 1) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hpos : (0 : ℝ) < ((n - i : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - i by omega)
    have hcast : ((n - i : ℕ) : ℝ) = n - i := by rw [Nat.cast_sub hi'.le]
    have hp : (0 : ℝ) < 2 ^ i := by positivity
    rw [div_le_div_iff₀ hpos (by positivity), hcast]
    have hi1 : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi'
    have key : (n : ℝ) + 1 ≤ ((i : ℝ) + 2) * (n - i) := by nlinarith
    calc ((2 : ℝ) ^ i)⁻¹ * (n + 1) ≤ ((2 : ℝ) ^ i)⁻¹ * (((i : ℝ) + 2) * (n - i)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = ((i : ℝ) + 2) / 2 ^ i * (n - i) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_div, sum_range_add_two_div_pow]
  have : 0 ≤ (2 * (n : ℝ) + 6) / 2 ^ n := by positivity
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- **Method 1 on a dyadic block**: under the upper Lipschitz bound, the cells
`2^i ≤ j < 2^{i+1}` (the block `[2^{−(m+1)}, 2^{−m}]`, `d = i + 1 + m`, `m ≥ 1`) contribute at
most `2^{−d} K 2^{−i}/(4m)`. -/
lemma group_method1_le (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {K : ℝ}
    (hup : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → (m : ℝ) * (f v - f u) ^ 2 ≤ K * ((2 : ℝ) ^ m * (v - u)) ^ 2)
    {d i m : ℕ} (hd : d = i + 1 + m) (hm : 1 ≤ m) :
    ∑ j ∈ Ico (2 ^ i) (2 ^ (i + 1)),
      ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 ≤
        (2 ^ d)⁻¹ * (K * ((2 : ℝ) ^ i)⁻¹ / (4 * m)) := by
  have hK : 0 ≤ K := nonneg_of_dyadic_block_lip_le hup
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlo : gridPt d (2 ^ i) = ((2 : ℝ) ^ (m + 1))⁻¹ := gridPt_two_pow (by omega)
  have hhi : gridPt d (2 ^ (i + 1)) = ((2 : ℝ) ^ m)⁻¹ := gridPt_two_pow (by omega)
  have hscale : (2 : ℝ) ^ m * (2 ^ d)⁻¹ = ((2 : ℝ) ^ (i + 1))⁻¹ := by
    rw [hd, pow_add, pow_add]
    field_simp
  have hcell : ∀ j ∈ Ico (2 ^ i) (2 ^ (i + 1)),
      ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 ≤
        (2 ^ d)⁻¹ * (K * (((2 : ℝ) ^ (i + 1))⁻¹) ^ 2 / m) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
    have hjd : j < 2 ^ d := lt_of_lt_of_le hj2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine cell_mse_le (intervalIntegrable_cell hf hjd) (intervalIntegrable_cell hf2 hjd)
      (f (gridPt d j)) _ fun u hu => ?_
    have h1 : ((2 : ℝ) ^ (m + 1))⁻¹ ≤ gridPt d j := hlo ▸ gridPt_mono d hj1
    have h3 : u ≤ ((2 : ℝ) ^ m)⁻¹ := hhi ▸ hu.2.trans (gridPt_mono d hj2)
    have hb := hup m hm (gridPt d j) u h1 hu.1 h3
    have hw : 0 ≤ u - gridPt d j := by linarith [hu.1]
    have hw2 : u - gridPt d j ≤ (2 ^ d)⁻¹ := by
      have := gridPt_succ_sub d j
      linarith [hu.2]
    have hsq : ((2 : ℝ) ^ m * (u - gridPt d j)) ^ 2 ≤ (((2 : ℝ) ^ (i + 1))⁻¹) ^ 2 := by
      rw [← hscale]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hw2 (by positivity)) 2
    rw [le_div_iff₀ hmR]
    calc (f (gridPt d j) - f u) ^ 2 * m = m * (f u - f (gridPt d j)) ^ 2 := by ring
      _ ≤ K * ((2 : ℝ) ^ m * (u - gridPt d j)) ^ 2 := hb
      _ ≤ K * (((2 : ℝ) ^ (i + 1))⁻¹) ^ 2 := mul_le_mul_of_nonneg_left hsq hK
  refine (Finset.sum_le_sum hcell).trans (le_of_eq ?_)
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    show 2 ^ (i + 1) - 2 ^ i = 2 ^ i by rw [pow_succ]; omega]
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- **Method 1 away from `0`**: the cells `1 ≤ j < 2^{d−1}` contribute at most `(3K/2) 2^{−d}/d`. -/
lemma groups_method1_le (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {K : ℝ}
    (hup : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → (m : ℝ) * (f v - f u) ^ 2 ≤ K * ((2 : ℝ) ^ m * (v - u)) ^ 2)
    {d : ℕ} (hd : 1 ≤ d) :
    ∑ i ∈ range (d - 1), ∑ j ∈ Ico (2 ^ i) (2 ^ (i + 1)),
      ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 ≤
        (2 ^ d)⁻¹ * (3 / 2 * K / d) := by
  have hK : 0 ≤ K := nonneg_of_dyadic_block_lip_le hup
  have hterm : ∀ i ∈ range (d - 1), ∑ j ∈ Ico (2 ^ i) (2 ^ (i + 1)),
      ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 ≤
        (2 ^ d)⁻¹ * (K / 4) * (((2 : ℝ) ^ i)⁻¹ / ((d - 1 - i : ℕ) : ℝ)) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    refine (group_method1_le hf hf2 hup (m := d - 1 - i) (by omega) (by omega)).trans
      (le_of_eq ?_)
    ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h6 := sum_range_inv_pow_div_le (d - 1)
  have hcast : ((d - 1 : ℕ) : ℝ) + 1 = d := by
    rw [Nat.cast_sub hd]; push_cast; ring
  rw [hcast] at h6
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc (2 ^ d)⁻¹ * (K / 4) * ∑ i ∈ range (d - 1), ((2 : ℝ) ^ i)⁻¹ / ((d - 1 - i : ℕ) : ℝ)
      ≤ (2 ^ d)⁻¹ * (K / 4) * (6 / d) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = (2 ^ d)⁻¹ * (3 / 2 * K / d) := by ring

/-- `a² ≤ n² c`, `b² ≤ c` imply `(a + b)² ≤ (n + 1)² c` (`n > 0`). -/
lemma sq_add_le_of_sq_le {a b c n : ℝ} (hn : 0 < n) (ha : a ^ 2 ≤ n ^ 2 * c) (hb : b ^ 2 ≤ c) :
    (a + b) ^ 2 ≤ (n + 1) ^ 2 * c := by
  have h1 : 2 * n * (a * b) ≤ 2 * n * (n * c) := by nlinarith [sq_nonneg (a - n * b)]
  have h2 : a * b ≤ n * c := le_of_mul_le_mul_left h1 (by positivity)
  nlinarith

/-- **Chaining the blocks near `0`**: under the upper Lipschitz bound, for `d ≥ 1` and `u` in the
block `[2^{−(r+d+1)}, 2^{−(r+d)}]`, `(f(2^{−d}) − f(u))² ≤ (r + 1)² K/(4d)`. -/
lemma tail_sq_le {K : ℝ}
    (hup : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → (m : ℝ) * (f v - f u) ^ 2 ≤ K * ((2 : ℝ) ^ m * (v - u)) ^ 2)
    {d : ℕ} (hd : 1 ≤ d) (r : ℕ) (u : ℝ) (hu1 : ((2 : ℝ) ^ (r + d + 1))⁻¹ ≤ u)
    (hu2 : u ≤ ((2 : ℝ) ^ (r + d))⁻¹) :
    (f ((2 : ℝ) ^ d)⁻¹ - f u) ^ 2 ≤ ((r : ℝ) + 1) ^ 2 * (K / (4 * d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- one block: `(f(2^{−m}) − f(u))² ≤ K/(4m)` for `u` in `[2^{−(m+1)}, 2^{−m}]`
  have hblock : ∀ m : ℕ, 1 ≤ m → ∀ u : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u →
      u ≤ ((2 : ℝ) ^ m)⁻¹ → (m : ℝ) * (f ((2 : ℝ) ^ m)⁻¹ - f u) ^ 2 ≤ K / 4 := by
    intro m hm u h1 h2
    have hb := hup m hm u ((2 : ℝ) ^ m)⁻¹ h1 h2 le_rfl
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have hw0 : 0 ≤ (2 : ℝ) ^ m * (((2 : ℝ) ^ m)⁻¹ - u) := by
      have : 0 ≤ ((2 : ℝ) ^ m)⁻¹ - u := by linarith
      positivity
    have hw1 : (2 : ℝ) ^ m * (((2 : ℝ) ^ m)⁻¹ - u) ≤ 1 / 2 := by
      have e : (2 : ℝ) ^ m * ((2 : ℝ) ^ (m + 1))⁻¹ = 1 / 2 := by
        rw [pow_succ]; field_simp
      have e2 : (2 : ℝ) ^ m * ((2 : ℝ) ^ m)⁻¹ = 1 := by field_simp
      nlinarith
    have hK : 0 ≤ K := nonneg_of_dyadic_block_lip_le hup
    have hsq : ((2 : ℝ) ^ m * (((2 : ℝ) ^ m)⁻¹ - u)) ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith
  induction r generalizing u with
  | zero =>
    simp only [zero_add] at hu1 hu2 ⊢
    have hb := hblock d hd u hu1 hu2
    rw [Nat.cast_zero, zero_add, one_pow, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  | succ r ih =>
    have hv := ih ((2 : ℝ) ^ (r + d + 1))⁻¹ le_rfl (inv_anti₀ (by positivity)
      (pow_le_pow_right₀ one_le_two (by omega)))
    have hm : 1 ≤ r + d + 1 := by omega
    have hb := hblock (r + d + 1) hm u (by rwa [show r + 1 + d + 1 = r + d + 1 + 1 by ring] at hu1)
      (by rwa [show r + 1 + d = r + d + 1 by ring] at hu2)
    have hK4 : (f ((2 : ℝ) ^ (r + d + 1))⁻¹ - f u) ^ 2 ≤ K / (4 * d) := by
      have hmR : (d : ℝ) ≤ ((r + d + 1 : ℕ) : ℝ) := by exact_mod_cast (show d ≤ r + d + 1 by omega)
      have h0 : 0 ≤ (f ((2 : ℝ) ^ (r + d + 1))⁻¹ - f u) ^ 2 := sq_nonneg _
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have e : f ((2 : ℝ) ^ d)⁻¹ - f u = (f ((2 : ℝ) ^ d)⁻¹ - f ((2 : ℝ) ^ (r + d + 1))⁻¹) +
        (f ((2 : ℝ) ^ (r + d + 1))⁻¹ - f u) := by ring
    rw [e]
    have h := sq_add_le_of_sq_le (n := (r : ℝ) + 1) (by positivity) hv hK4
    push_cast
    linarith

/-- `∑_{r<M} (r + 1)²/2^{r+1} = 6 − (M² + 4M + 6)/2^M`. -/
lemma sum_range_sq_div_pow (M : ℕ) :
    ∑ r ∈ range M, ((r : ℝ) + 1) ^ 2 / 2 ^ (r + 1) = 6 - ((M : ℝ) ^ 2 + 4 * M + 6) / 2 ^ M := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    field_simp
    ring

/-- **Method 1 on the end cell `[0, 2^{−d}]`**: under the upper Lipschitz bound, its error is at
most `(3K/2) 2^{−d}/d` (by `tail_sq_le` on the blocks `m ≥ d` and `M → ∞`). -/
lemma end_cell_method1_le (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {K : ℝ}
    (hup : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → (m : ℝ) * (f v - f u) ^ 2 ≤ K * ((2 : ℝ) ^ m * (v - u)) ^ 2)
    {d : ℕ} (hd : 1 ≤ d) :
    ∫ u in gridPt d 0..gridPt d (0 + 1), (lutValue f d 0 - f u) ^ 2 ≤
      (2 ^ d)⁻¹ * (3 / 2 * K / d) := by
  have hK : 0 ≤ K := nonneg_of_dyadic_block_lip_le hup
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have e0 : gridPt d 0 = 0 := by simp [gridPt]
  have e1 : gridPt d (0 + 1) = ((2 : ℝ) ^ d)⁻¹ := by simp [gridPt]
  set h : ℝ := ((2 : ℝ) ^ d)⁻¹ with hh
  set g : ℝ → ℝ := fun u => (f h - f u) ^ 2 with hgdef
  have hg : IntervalIntegrable g volume 0 1 := intervalIntegrable_sq_sub hf hf2 (f h)
  have hT0 : ∫ u in gridPt d 0..gridPt d (0 + 1), (lutValue f d 0 - f u) ^ 2 ≤
      ∫ u in (0 : ℝ)..h, g u := by
    rw [lutValue_eq_intervalMean]
    have := integral_sq_sub_intervalMean_le (gridPt_lt d 0)
      (intervalIntegrable_cell hf (by positivity)) (intervalIntegrable_cell hf2 (by positivity))
      (f h)
    rwa [e0, e1] at this ⊢
  set B : ℝ := (2 ^ d)⁻¹ * (3 / 2 * K / d)
  -- the integral away from `0`
  have hM : ∀ M : ℕ, ∫ u in ((2 : ℝ) ^ (M + d))⁻¹..h, g u ≤ B := by
    intro M
    rw [hh, ← sum_range_blocks hg d M]
    have hblock : ∀ r ∈ range M, ∫ u in ((2 : ℝ) ^ (r + d + 1))⁻¹..((2 : ℝ) ^ (r + d))⁻¹, g u ≤
        ((2 : ℝ) ^ (r + d + 1))⁻¹ * (((r : ℝ) + 1) ^ 2 * (K / (4 * d))) := by
      intro r _
      have hle : ((2 : ℝ) ^ (r + d + 1))⁻¹ ≤ ((2 : ℝ) ^ (r + d))⁻¹ :=
        inv_two_pow_anti (by omega)
      have hmono := intervalIntegral.integral_mono_on hle
        (intervalIntegrable_sub01 hg (inv_two_pow_mem _).1 hle (inv_two_pow_mem _).2)
        intervalIntegrable_const fun u hu => tail_sq_le hup hd r u hu.1 hu.2
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      have hlen : ((2 : ℝ) ^ (r + d))⁻¹ - ((2 : ℝ) ^ (r + d + 1))⁻¹ =
          ((2 : ℝ) ^ (r + d + 1))⁻¹ := by
        rw [pow_succ]; field_simp; ring
      rwa [hlen] at hmono
    refine (Finset.sum_le_sum hblock).trans ?_
    have hsum : ∑ r ∈ range M, ((2 : ℝ) ^ (r + d + 1))⁻¹ * (((r : ℝ) + 1) ^ 2 * (K / (4 * d))) =
        (2 ^ d)⁻¹ * (K / (4 * d)) * ∑ r ∈ range M, ((r : ℝ) + 1) ^ 2 / 2 ^ (r + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [show r + d + 1 = d + (r + 1) by ring, pow_add]
      field_simp
    rw [hsum, sum_range_sq_div_pow]
    have h0 : 0 ≤ ((M : ℝ) ^ 2 + 4 * M + 6) / 2 ^ M := by positivity
    have hc : 0 ≤ (2 ^ d : ℝ)⁻¹ * (K / (4 * d)) := by positivity
    calc (2 ^ d : ℝ)⁻¹ * (K / (4 * d)) * (6 - ((M : ℝ) ^ 2 + 4 * M + 6) / 2 ^ M)
        ≤ (2 ^ d : ℝ)⁻¹ * (K / (4 * d)) * 6 := mul_le_mul_of_nonneg_left (by linarith) hc
      _ = B := by ring
  -- let `M → ∞`
  have hx : Tendsto (fun M : ℕ => ((2 : ℝ) ^ (M + d))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp
      (tendsto_add_atTop_nat d))
  have hx01 : ∀ M : ℕ, ((2 : ℝ) ^ (M + d))⁻¹ ∈ Set.uIcc (0 : ℝ) 1 := fun M => by
    rw [Set.uIcc_of_le zero_le_one]
    exact inv_two_pow_mem _
  have hlim := (tendsto_integral_zero hg hx hx01).add_const B
  rw [zero_add] at hlim
  refine hT0.trans (ge_of_tendsto' hlim fun M => ?_)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_sub01 hg le_rfl (inv_two_pow_mem (M + d)).1 (inv_two_pow_mem _).2)
    (intervalIntegrable_sub01 hg (inv_two_pow_mem _).1 (inv_two_pow_anti (by omega))
      (inv_two_pow_mem d).2)
  rw [← hsplit]
  linarith [hM M]

/-- **Upper bound `MSE = O(2^{−d}/d)` for method 1** (Haas–Giles 2025, §3.4, p. 7: method 1 has
its "MSE divided by 2 each time `d` increases by 1").  If `f`, `f²` are interval-integrable on
`[0, 1]`, `f(1 − u) = −f(u)` and, on each dyadic block `[2^{−(m+1)}, 2^{−m}]`, `m ≥ 1`,
`m (f(v) − f(u))² ≤ K (2^m (v − u))²` (`Φ⁻¹` satisfies all this with `K = 4`), then for every
`d ≥ 1` the mean-square error of method 1 is at most `6K 2^{−d}/d`. -/
theorem method1MSE_le_order (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (hodd : ∀ u, f (1 - u) = -f u)
    {K : ℝ}
    (hup : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → (m : ℝ) * (f v - f u) ^ 2 ≤ K * ((2 : ℝ) ^ m * (v - u)) ^ 2)
    {d : ℕ} (hd : 1 ≤ d) :
    method1MSE f d ≤ 6 * K * ((2 ^ d)⁻¹ / d) := by
  rw [method1MSE_eq_two_mul hodd hd, sum_range_two_pow_dyadic _ (d - 1)]
  have h1 := end_cell_method1_le hf hf2 hup hd
  have h2 := groups_method1_le hf hf2 hup hd
  have e : 6 * K * (((2 : ℝ) ^ d)⁻¹ / d) = 2 * ((2 ^ d)⁻¹ * (3 / 2 * K / d) +
      (2 ^ d)⁻¹ * (3 / 2 * K / d)) := by ring
  rw [e]
  linarith

/-- **A lower bound for the error of a constant**: if `(f(u + s) − f(u))² ≥ l` for `u ∈ [a, a + s]`,
then `∫_a^{a+2s} (z − f)² ≥ s l/2` for every `z` (pair `u` with `u + s`). -/
lemma half_shift_lower {a s z l : ℝ} (hs : 0 < s)
    (hf : IntervalIntegrable f volume a (a + 2 * s))
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume a (a + 2 * s))
    (hl : ∀ u ∈ Set.Icc a (a + s), l ≤ (f (u + s) - f u) ^ 2) :
    s * l / 2 ≤ ∫ u in a..a + 2 * s, (z - f u) ^ 2 := by
  have hG := intervalIntegrable_sq_sub hf hf2 z
  have hsub : ∀ x y, x ∈ Set.uIcc a (a + 2 * s) → y ∈ Set.uIcc a (a + 2 * s) →
      IntervalIntegrable (fun u => (z - f u) ^ 2) volume x y :=
    fun x y hx hy => hG.mono_set (Set.uIcc_subset_uIcc hx hy)
  have hm : a + s ∈ Set.uIcc a (a + 2 * s) := by
    rw [Set.uIcc_of_le (by linarith)]; constructor <;> linarith
  have h1 := hsub a (a + s) Set.left_mem_uIcc hm
  have h2 := hsub (a + s) (a + 2 * s) hm Set.right_mem_uIcc
  have hshift : ∫ u in (a + s)..(a + 2 * s), (z - f u) ^ 2 =
      ∫ u in a..(a + s), (z - f (u + s)) ^ 2 := by
    rw [intervalIntegral.integral_comp_add_right (fun u => (z - f u) ^ 2) s,
      show a + s + s = a + 2 * s by ring]
  have h2' : IntervalIntegrable (fun u => (z - f (u + s)) ^ 2) volume a (a + s) := by
    have h := h2.comp_add_right s
    rwa [show a + s - s = a by ring, show a + 2 * s - s = a + s by ring] at h
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, hshift,
    ← intervalIntegral.integral_add h1 h2']
  have hmono := intervalIntegral.integral_mono_on (by linarith : a ≤ a + s)
    (intervalIntegrable_const (c := l / 2)) (h1.add h2') fun u hu => by
      have := hl u hu
      nlinarith [sq_nonneg (2 * z - f u - f (u + s))]
  rw [intervalIntegral.integral_const, smul_eq_mul, show a + s - a = s by ring] at hmono
  linarith

/-- **Lower bound `MSE ≥ c' 2^{−d}/d` for method 1** (Haas–Giles 2025, §3.4, p. 7: method 1 has
its "MSE divided by 2 each time `d` increases by 1").  If `f`, `f²` are interval-integrable on
`[0, 1]` and, on each dyadic block `[2^{−(m+1)}, 2^{−m}]`, `m ≥ 1`,
`c (2^m (v − u))² ≤ m (f(v) − f(u))²` with `c ≥ 0` (`Φ⁻¹` satisfies it with `c = ½`), then for
every `d ≥ 2` the mean-square error of method 1 is at least `(c/64) 2^{−d}/d`; the cell
`[2^{−d}, 2^{1−d}]` alone contributes that much. -/
theorem method1MSE_ge_order (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {c : ℝ} (hc : 0 ≤ c)
    (hlo : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → c * ((2 : ℝ) ^ m * (v - u)) ^ 2 ≤ (m : ℝ) * (f v - f u) ^ 2)
    {d : ℕ} (hd : 2 ≤ d) :
    c / 64 * ((2 ^ d)⁻¹ / d) ≤ method1MSE f d := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set h : ℝ := ((2 : ℝ) ^ (m + 1))⁻¹ with hh
  have hpos : 0 < h := by positivity
  have hhm : ((2 : ℝ) ^ m)⁻¹ = 2 * h := by rw [hh, pow_succ]; field_simp
  have hg1 : gridPt (m + 1) 1 = h := by simp [gridPt, hh]
  have hg2 : gridPt (m + 1) (1 + 1) = h + 2 * (h / 2) := by
    rw [gridPt, hh]; push_cast; ring
  have h2 : 1 < 2 ^ (m + 1) := Nat.one_lt_two_pow (by omega)
  -- the cell `I_1 = [h, 2h]` alone
  have hT1 : ∫ u in gridPt (m + 1) 1..gridPt (m + 1) (1 + 1), (lutValue f (m + 1) 1 - f u) ^ 2
      ≤ method1MSE f (m + 1) :=
    Finset.single_le_sum (f := fun j => ∫ u in gridPt (m + 1) j..gridPt (m + 1) (j + 1),
      (lutValue f (m + 1) j - f u) ^ 2)
      (fun j _ => intervalIntegral.integral_nonneg (gridPt_lt _ j).le fun _ _ => sq_nonneg _)
      (Finset.mem_range.2 h2)
  have hI := intervalIntegrable_cell hf h2
  have hI2 := intervalIntegrable_cell hf2 h2
  rw [hg1, hg2] at hI hI2 hT1
  have hl : ∀ u ∈ Set.Icc h (h + h / 2), c / (16 * m) ≤ (f (u + h / 2) - f u) ^ 2 := by
    intro u hu
    have hb := hlo m hm u (u + h / 2) hu.1 (by linarith) (by rw [hhm]; linarith [hu.2])
    have e : (2 : ℝ) ^ m * (u + h / 2 - u) = 1 / 4 := by
      rw [hh, pow_succ]; field_simp; ring
    rw [e] at hb
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlow := half_shift_lower (z := lutValue f (m + 1) 1) (by positivity : 0 < h / 2) hI hI2 hl
  refine le_trans ?_ (hlow.trans hT1)
  push_cast
  have e3 : h / 2 * (c / (16 * m)) / 2 = c / 64 * (h / m) := by field_simp; ring
  rw [e3]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact div_le_div_of_nonneg_left hpos.le (by positivity) (by linarith)

/-- **Method 1: the MSE is of exact order `2^{−d}/d`** (Haas–Giles 2025, §3.4, p. 7: "both method
1 and 2 have their MSE divided by 2 each time `d` increases by 1. This was theoretically expected
for method 1").  If `f`, `f²` are interval-integrable on `[0, 1]`, `f(1 − u) = −f(u)` and, on each
dyadic block `[2^{−(m+1)}, 2^{−m}]`, `m ≥ 1`,
`c (2^m (v − u))² ≤ m (f(v) − f(u))² ≤ K (2^m (v − u))²` with `c > 0` (`Φ⁻¹` satisfies all this
with `c = ½`, `K = 4`), then `K > 0` and for every `d ≥ 2`
`(c/64) 2^{−d}/d ≤ MSE ≤ 6K 2^{−d}/d`.  This gives the halving per bit only up to a bounded
factor: `MSE(d + 1)/MSE(d)` lies between `c/(768K)` and `192K/c` (times `d/(d + 1)`); the exact
limit `½` would need `MSE(d) ~ κ 2^{−d}/d` with an exact `κ`, i.e. finer asymptotics of `Φ⁻¹`
near `0` (numerically `MSE(d + 1)/MSE(d) = ½(1 − 1/d + …)`, `0.473` at `d = 17`). -/
theorem method1MSE_order (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (hodd : ∀ u, f (1 - u) = -f u)
    {c K : ℝ} (hc : 0 < c)
    (hlo : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → c * ((2 : ℝ) ^ m * (v - u)) ^ 2 ≤ (m : ℝ) * (f v - f u) ^ 2)
    (hup : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → (m : ℝ) * (f v - f u) ^ 2 ≤ K * ((2 : ℝ) ^ m * (v - u)) ^ 2) :
    0 < K ∧ ∀ d : ℕ, 2 ≤ d →
      c / 64 * ((2 ^ d)⁻¹ / d) ≤ method1MSE f d ∧ method1MSE f d ≤ 6 * K * ((2 ^ d)⁻¹ / d) := by
  have hb : ∀ d : ℕ, 2 ≤ d →
      c / 64 * ((2 ^ d)⁻¹ / d) ≤ method1MSE f d ∧ method1MSE f d ≤ 6 * K * ((2 ^ d)⁻¹ / d) :=
    fun d hd => ⟨method1MSE_ge_order hf hf2 hc.le hlo hd,
      method1MSE_le_order hf hf2 hodd hup (by omega)⟩
  refine ⟨?_, hb⟩
  obtain ⟨h1, h2⟩ := hb 2 le_rfl
  have h3 : 0 < c / 64 * (((2 : ℝ) ^ 2)⁻¹ / (2 : ℕ)) := by positivity
  have h4 : 0 < ((2 : ℝ) ^ 2)⁻¹ / (2 : ℕ) := by positivity
  nlinarith

/-- **Method 1 halves the MSE per bit on average** (Haas–Giles 2025, §3.4, p. 7: method 1 has
its "MSE divided by 2 each time `d` increases by 1").  Under the hypotheses of
`method1MSE_order`, `log(MSE(d))/d → −log 2`, i.e. `MSE(d)^{1/d} → ½`: the geometric mean of the
ratios `MSE(d + 1)/MSE(d)` tends to `½`.  (The exact limit of the ratio itself is not proved, see
`method1MSE_order`.) -/
theorem tendsto_log_method1MSE_div (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (hodd : ∀ u, f (1 - u) = -f u)
    {c K : ℝ} (hc : 0 < c)
    (hlo : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → c * ((2 : ℝ) ^ m * (v - u)) ^ 2 ≤ (m : ℝ) * (f v - f u) ^ 2)
    (hup : ∀ m : ℕ, 1 ≤ m → ∀ u v : ℝ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ u → u ≤ v →
      v ≤ ((2 : ℝ) ^ m)⁻¹ → (m : ℝ) * (f v - f u) ^ 2 ≤ K * ((2 : ℝ) ^ m * (v - u)) ^ 2) :
    Tendsto (fun d : ℕ => Real.log (method1MSE f d) / d) atTop (𝓝 (-Real.log 2)) := by
  obtain ⟨hK, hb⟩ := method1MSE_order hf hf2 hodd hc hlo hup
  -- `log(a 2^{−d}/d)/d = log a/d − log 2 − log d/d`
  have hlogd : Tendsto (fun d : ℕ => Real.log d / d) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine h.congr fun d => ?_
    simp
  have hlim : ∀ a : ℝ, Tendsto (fun d : ℕ => Real.log a / d - Real.log 2 - Real.log d / d)
      atTop (𝓝 (-Real.log 2)) := by
    intro a
    have h := ((tendsto_const_nhds (x := Real.log a)).div_atTop
      tendsto_natCast_atTop_atTop).sub_const (Real.log 2) |>.sub hlogd
    simpa using h
  have hform : ∀ a : ℝ, 0 < a → ∀ d : ℕ, 1 ≤ d →
      Real.log (a * ((2 ^ d)⁻¹ / d)) / d = Real.log a / d - Real.log 2 - Real.log d / d := by
    intro a ha d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    rw [Real.log_mul ha.ne' (by positivity), Real.log_div (by positivity) hdR.ne',
      Real.log_inv, Real.log_pow]
    field_simp
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (c / 64)) (hlim (6 * K)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    rw [← hform _ (by positivity) d (by omega)]
    exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (hb d hd).1) hdR.le
  · filter_upwards [eventually_ge_atTop 2] with d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    rw [← hform _ (by positivity) d (by omega)]
    exact div_le_div_of_nonneg_right (Real.log_le_log (lt_of_lt_of_le (by positivity)
      (hb d hd).1) (hb d hd).2) hdR.le

end Method1

end MLMC
