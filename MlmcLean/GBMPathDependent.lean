import MlmcLean.GBMMilstein

/-!
# GBM: discretely monitored Asian and lookback options (Giles 2015, §5.1–§5.2, Table 5.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.1 (p. 29) and
§5.2 (pp. 33–39), Table 5.2 (p. 33), the rows "Asian" and "lookback" (coverage rows G5.1-30,
G5.1-31, G5.2-32, G5.2-33):

| option   | Euler–Maruyama: numerics, analysis | Milstein: numerics, analysis |
|----------|------------------------------------|------------------------------|
| Asian    | `O(h)`, `O(h)`                     | `O(h²)`, `O(h²)`             |
| lookback | `O(h)`, `O(h)`                     | `O(h²)`, `o(h^{2−δ})`        |

("Observed and theoretical convergence rates for the multilevel correction variance for scalar
SDEs"; p. 33: "the Asian option is based on the average value of the underlying asset, the
lookback is based on its maximum or minimum value").  §5.1, p. 29, gives the argument: "For
Lipschitz payoff functions `P` (such as European, Asian and lookback options in finance) for which
`|P(S₁) − P(S₂)| ≤ K ‖S₁ − S₂‖`, we have `V[P − P_ℓ] ≤ E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`, and
`V_ℓ ≡ V[P_ℓ − P_{ℓ−1}] ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`, and hence `V_ℓ = O(h_ℓ)`."

**What is proved here.**  Everything for geometric Brownian motion `dS = rS dt + σS dW`
(`S_0 = s₀`) and *discretely monitored* options, with explicit constants and no assumed rate.

* The setting.  The monitoring dates are `t_k = kT/m`, `k = 0, …, m`, for a fixed `m ≥ 1`.  Level
  `j ≥ 0` uses `m 2^j` time steps of size `h_j = T/(m 2^j)`, so every date `t_k` is the grid time
  number `k 2^j` on every level: for `m = 2^{ℓ₀}` level `j` is the paper's level `ℓ = ℓ₀ + j`
  (`h_ℓ = T 2^{−ℓ}`), i.e. the level hierarchy starts at `ℓ₀`; any `m ≥ 1` works.  `gbmMonExact`,
  `gbmMonEM`, `gbmMonMil` are the exact solution, the Euler–Maruyama and the Milstein values at the
  dates, all driven by the same normal increments; the levels are coupled as in `GBMEulerMaruyama`
  and `GBMMilstein` by the coarse increments `(Z_{2i} + Z_{2i+1})/√2` (`gbmMonExact_pairAvg`).
  The target `E[P]` of Theorem 1 is computed from `gbmMonExact … 0`, i.e. (`gbmMonExact_level_zero`)
  `S_{t_k} = s₀ exp((r − σ²/2) kT/m + σ √(T/m) ∑_{i<k} Z_i)`, the exact solution at the dates.
* The case `m = 0` (no monitoring interval) is allowed in the generic and the lookback rate
  statements, which do not need `m ≥ 1`.  There `t_k = kT/0` and `h_j = T/(0 · 2^j)` are Lean's
  junk value `0`, but the statements are degenerate and true for a genuine reason, not through the
  junk value: the only monitored value is `S_{t_0} = s₀` on both paths, and the bounds carry a
  factor `m = 0`.  The Asian statements and all Theorem 1 statements assume `m ≥ 1`.
* The payoffs: `asianPayoff g m S = g((1/m) ∑_{k=1}^m S_{t_k})`,
  `lookbackPayoff g m S = g(max_{0≤k≤m} S_{t_k})` and
  `floatLookbackPayoff g m S = g(S_T − min_{0≤k≤m} S_{t_k})`, with `g` `K`-Lipschitz.  All three
  satisfy `(Φ(a) − Φ(b))² ≤ c ∑_{k=0}^m (a_k − b_k)²`, the paper's
  `|P(S₁) − P(S₂)| ≤ K ‖S₁ − S₂‖` for the Euclidean norm of the monitored values, with
  `c = K²/m` (Jensen), `c = K²` (`|max a − max b| ≤ max |a_k − b_k|`) and `c = 4K²`.
* For every such payoff (`gbm_em_monitored_*`, `gbm_mil_monitored_*`): the mean square error
  `E[(P − P̂_j)²] ≤ c m C(T) h_j` (Euler–Maruyama) and `≤ c m C_M(T) h_j²` (Milstein), from the
  strong error at each monitoring date (`gbm_em_strong_error`, `gbm_mil_strong_error`); the bias
  `|E[P̂_j] − E[P]| = O(h_j^{1/2})`, resp. `O(h_j)`; the correction variance
  `V[P̂^f_{j+1} − P̂^c_j] ≤ 6 c m C(T) h_{j+1}`, resp. `≤ 10 c m C_M(T) h_{j+1}²`; and Theorem 1:
  a square-integrable error with mean square `< ε²` at cost `O(ε⁻²(log ε)²)` (`β = γ = 1`), resp.
  `O(ε⁻²)` (`β = 2 > γ = 1`).
* The same for the Asian and the lookback option by name (`gbm_em_asian_*`, `gbm_mil_asian_*`,
  `gbm_em_lookback_*`, `gbm_mil_lookback_*`): the rates of Table 5.2, `V_ℓ = O(h)` for
  Euler–Maruyama and `V_ℓ = O(h²)` for Milstein; and the correction variance and Theorem 1 for the
  floating-strike lookback (`gbm_em_floatLookback_*`, `gbm_mil_floatLookback_*`).  The lookback
  constants carry a factor `m` from `max_k (a_k − b_k)² ≤ ∑_k (a_k − b_k)²`.  It is not sharp: in a
  Monte Carlo check at a fixed step with `m` up to 64, the lookback mean square error stays below
  about 1.1 times the largest per-date mean square error, while the bound grows like `m`.  It does
  not affect the rate in `j`: since `h_j = T/(m 2^j)`, e.g. `K² m C(T) h_j = K² C(T) T 2^{−j}`.

**The Milstein lookback and §5.2, p. 38.**  On p. 38 the paper says that "a multilevel estimator
based directly on the minimum (or maximum) of the values at the discrete timesteps will have a
poor variance … This results in an `O(h_ℓ)` variance for lookback options".  There the maximum runs
over *all* time steps of each level, so the fine and the coarse payoffs use different sets of
times (and approximate the continuously monitored maximum).  This does not contradict the `O(h²)`
proved here: the `m + 1` monitoring dates are fixed and lie on every grid, so the coarse and the
fine payoffs compare the two paths at the same dates, and the first-order strong convergence of
Milstein at each date gives `O(h_ℓ²)` (a Monte Carlo check confirms `V_ℓ/h_ℓ²` roughly constant for
fixed dates and `V_ℓ/h_ℓ` roughly constant for the maximum over all time steps).

**What is not proved.**  Continuous monitoring: the paper's options use the time average of `S`
over `[0, T]` and its maximum or minimum over `[0, T]`, and their analysis needs the law of the
Brownian path between the grid points, which is out of reach here.  The paper credits the analysis
column of Table 5.2 to Giles, Higham and Mao (2009) for Euler–Maruyama (§5.1, p. 33) and to Giles,
Debrabant and Rößler (2013), "Giles et al. (2013)", for Milstein (§5.2, p. 39); the Milstein
lookback and barrier estimators use the Brownian-bridge interpolant of Giles (2008a) (§5.2,
pp. 38–39: "the outcome is that `β = 2` for lookback options").  In particular the Milstein
lookback rate `o(h^{2−δ})` of Table 5.2 (continuous monitoring) is not proved; for the discretely
monitored lookback the Milstein rate is `O(h²)`, as in the numerics column.  The paper's
Euler–Maruyama weak order `α = 1` (§5.1, p. 30) is not proved either: only `α = ½`, which suffices
for Theorem 1.  General scalar SDEs are not covered (only GBM, whose solution is explicit).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### The monitored paths -/

/-- The exact GBM solution at the monitoring dates `t_k = kT/m` (Giles 2015, §5.1, GBM example:
`S_t = S_0 exp((r − σ²/2)t + σ W_t)`), with the Brownian motion sampled on the level-`j` grid,
`W_{t_k} = √h_j ∑_{i<k2^j} Z_i` with `h_j = T/(m 2^j)`, driven by the same increments `Z_i` as the
level-`j` paths.  At level `0` the increments of `W` between consecutive dates are `√(T/m) Z_k`, so
`k ↦ gbmMonExact r σ T s₀ m 0 z k` is the exact solution at the dates `t_0, …, t_m`; its law does
not depend on the level (`gbmMonExact_pairAvg`). -/
noncomputable def gbmMonExact (r σ T s₀ : ℝ) (m j : ℕ) (z : ℕ → ℝ) (k : ℕ) : ℝ :=
  s₀ * Real.exp ((r - σ ^ 2 / 2) * (k * (T / m)) +
    σ * (Real.sqrt (T / (m * 2 ^ j)) * ∑ i ∈ range (k * 2 ^ j), z i))

/-- The level-`j` Euler–Maruyama approximation of GBM at the monitoring dates (Giles 2015, §5.1):
the Euler–Maruyama path `emPath` with step `h_j = T/(m 2^j)` driven by the increments `Z_i`, read at
the grid time `k 2^j h_j = t_k`. -/
noncomputable def gbmMonEM (r σ T s₀ : ℝ) (m j : ℕ) (z : ℕ → ℝ) (k : ℕ) : ℝ :=
  emPath (gbmDrift r) (gbmVol σ) (T / (m * 2 ^ j)) s₀ z (k * 2 ^ j)

/-- The level-`j` Milstein approximation of GBM at the monitoring dates (Giles 2015, §5.2): the
Milstein path `milsteinPath` with `a(S) = rS`, `b(S) = σS` and step `h_j = T/(m 2^j)`, read at the
grid time `k 2^j h_j = t_k`. -/
noncomputable def gbmMonMil (r σ T s₀ : ℝ) (m j : ℕ) (z : ℕ → ℝ) (k : ℕ) : ℝ :=
  milsteinPath (fun S => r * S) (fun S => σ * S) (T / (m * 2 ^ j)) s₀ z (k * 2 ^ j)

/-- The discretely monitored Asian payoff `g((1/m) ∑_{k=1}^m S_{t_k})` of the monitored values
`S = (S_{t_0}, S_{t_1}, …)` (Giles 2015, §5.1, p. 33: "the Asian option is based on the average
value of the underlying asset"; the paper's option averages `S_t` over `[0, T]` continuously). -/
noncomputable def asianPayoff (g : ℝ → ℝ) (m : ℕ) (S : ℕ → ℝ) : ℝ :=
  g ((∑ k ∈ range m, S (k + 1)) / m)

/-- The discretely monitored lookback payoff `g(max_{0≤k≤m} S_{t_k})` (Giles 2015, §5.1, p. 33: "the
lookback is based on its maximum or minimum value"; the paper's option uses the maximum over
`[0, T]`, which contains `t_0 = 0`). -/
noncomputable def lookbackPayoff (g : ℝ → ℝ) (m : ℕ) (S : ℕ → ℝ) : ℝ :=
  g ((range (m + 1)).sup' nonempty_range_add_one S)

/-- The discretely monitored floating-strike lookback payoff `g(S_{t_m} − min_{0≤k≤m} S_{t_k})`,
`t_m = T` (Giles 2015, §5.1, p. 33, the lookback option "based on its … minimum value", e.g. the
call `e^{−rT}(S_T − min S)` with `g(x) = e^{−rT} x`). -/
noncomputable def floatLookbackPayoff (g : ℝ → ℝ) (m : ℕ) (S : ℕ → ℝ) : ℝ :=
  g (S m - (range (m + 1)).inf' nonempty_range_add_one S)

/-- The monitoring date `t_k` is the grid time number `k 2^j` on level `j`:
`(k 2^j) · T/(m 2^j) = kT/m`. -/
lemma monDate_eq (T : ℝ) (m j k : ℕ) :
    ((k * 2 ^ j : ℕ) : ℝ) * (T / (m * 2 ^ j)) = k * (T / m) := by
  rw [← div_div]
  push_cast
  rw [mul_assoc, mul_div_cancel₀ _ (by positivity : (2 : ℝ) ^ j ≠ 0)]

/-- The monitoring dates lie in `[0, T]`: `0 ≤ kT/m ≤ T` for `k ≤ m`. -/
lemma monDate_mem_Icc {T : ℝ} (hT : 0 ≤ T) {m k : ℕ} (hk : k ≤ m) :
    0 ≤ (k : ℝ) * (T / m) ∧ (k : ℝ) * (T / m) ≤ T := by
  refine ⟨mul_nonneg (Nat.cast_nonneg k) (div_nonneg hT (Nat.cast_nonneg m)), ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hT]
  · calc (k : ℝ) * (T / m) ≤ m * (T / m) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) (div_nonneg hT (Nat.cast_nonneg m))
      _ = T := mul_div_cancel₀ T (Nat.cast_ne_zero.2 hm.ne')

/-- The exact solution at the date `t_k` is the product of `k 2^j` exact one-step factors. -/
lemma gbmMonExact_eq_prod (r σ T s₀ : ℝ) (m j : ℕ) (z : ℕ → ℝ) (k : ℕ) :
    gbmMonExact r σ T s₀ m j z k =
      s₀ * ∏ i ∈ range (k * 2 ^ j), gbmExpFactor r σ (T / (m * 2 ^ j)) (z i) := by
  rw [gbmMonExact, ← monDate_eq T m j k, gbmExp_eq_prod]

/-- The Euler–Maruyama value at the date `t_k` is the product of `k 2^j` one-step factors. -/
lemma gbmMonEM_eq_prod (r σ T s₀ : ℝ) (m j : ℕ) (z : ℕ → ℝ) (k : ℕ) :
    gbmMonEM r σ T s₀ m j z k =
      s₀ * ∏ i ∈ range (k * 2 ^ j), gbmEMFactor r σ (T / (m * 2 ^ j)) (z i) :=
  emPath_gbm r σ (T / (m * 2 ^ j)) s₀ z (k * 2 ^ j)

/-- The Milstein value at the date `t_k` is the product of `k 2^j` one-step factors. -/
lemma gbmMonMil_eq_prod (r σ T s₀ : ℝ) (m j : ℕ) (z : ℕ → ℝ) (k : ℕ) :
    gbmMonMil r σ T s₀ m j z k =
      s₀ * ∏ i ∈ range (k * 2 ^ j), gbmMilFactor r σ (T / (m * 2 ^ j)) (z i) :=
  milsteinPath_gbm r σ (T / (m * 2 ^ j)) s₀ z (k * 2 ^ j)

/-- At the date `t_0 = 0` the exact solution is `s₀`. -/
lemma gbmMonExact_zero (r σ T s₀ : ℝ) (m j : ℕ) (z : ℕ → ℝ) :
    gbmMonExact r σ T s₀ m j z 0 = s₀ := by
  simp [gbmMonExact]

/-- The exact solution at the dates on level `0`, in closed form (Giles 2015, §5.1, GBM example):
`S_{t_k} = s₀ exp((r − σ²/2) kT/m + σ √(T/m) ∑_{i<k} Z_i)`, the Brownian increments between
consecutive dates being `√(T/m) Z_i`.  This is the path whose payoff is the target `E[P]` in the
Theorem 1 statements below. -/
lemma gbmMonExact_level_zero (r σ T s₀ : ℝ) (m : ℕ) (z : ℕ → ℝ) (k : ℕ) :
    gbmMonExact r σ T s₀ m 0 z k =
      s₀ * Real.exp ((r - σ ^ 2 / 2) * (k * (T / m)) +
        σ * (Real.sqrt (T / m) * ∑ i ∈ range k, z i)) := by
  simp only [gbmMonExact, pow_zero, mul_one]

/-- At the date `t_0 = 0` the Euler–Maruyama value is `s₀`. -/
lemma gbmMonEM_zero (r σ T s₀ : ℝ) (m j : ℕ) (z : ℕ → ℝ) :
    gbmMonEM r σ T s₀ m j z 0 = s₀ := by
  unfold gbmMonEM
  rw [zero_mul]
  rfl

/-- At the date `t_0 = 0` the Milstein value is `s₀`. -/
lemma gbmMonMil_zero (r σ T s₀ : ℝ) (m j : ℕ) (z : ℕ → ℝ) :
    gbmMonMil r σ T s₀ m j z 0 = s₀ := by
  unfold gbmMonMil
  rw [zero_mul]
  rfl

/-- `z ↦ s₀ ∏_{i<n} F(z_i)` is measurable for a measurable `F`. -/
lemma measurable_monProd {F : ℝ → ℝ} (hF : Measurable F) (s₀ : ℝ) (n : ℕ) :
    Measurable fun z : ℕ → ℝ => s₀ * ∏ i ∈ range n, F (z i) :=
  (Finset.measurable_prod _ fun i _ => hF.comp (measurable_pi_apply i)).const_mul s₀

/-- `s₀ ∏_{i<n} F(Z_i)` is square integrable for independent standard normal `Z_i` if `F(Z)` is. -/
lemma memLp_monProd {F : ℝ → ℝ} (hF : Measurable F)
    (hF2 : Integrable (fun x => F x ^ 2) (gaussianReal 0 1)) (s₀ : ℝ) (n : ℕ) :
    MemLp (fun z : ℕ → ℝ => s₀ * ∏ i ∈ range n, F (z i)) 2 stdNormalSeq := by
  refine (memLp_two_iff_integrable_sq (measurable_monProd hF s₀ n).aestronglyMeasurable).2 ?_
  have e : (fun z : ℕ → ℝ => (s₀ * ∏ i ∈ range n, F (z i)) ^ 2) =
      fun z => s₀ ^ 2 * ∏ i ∈ range n, F (z i) ^ 2 := by
    funext z
    rw [mul_pow, ← Finset.prod_pow]
  rw [e]
  exact (integrable_prod_stdNormalSeq (hF.pow_const 2) hF2 n).const_mul _

/-- A path whose values are products of one-step factors is measurable (as a map into `ℕ → ℝ`) and
each of its values is square integrable. -/
lemma measurable_memLp_monPath {X : (ℕ → ℝ) → ℕ → ℝ} {F : ℝ → ℝ} {s₀ : ℝ} {n : ℕ → ℕ}
    (hF : Measurable F) (hF2 : Integrable (fun x => F x ^ 2) (gaussianReal 0 1))
    (hX : ∀ z k, X z k = s₀ * ∏ i ∈ range (n k), F (z i)) :
    Measurable X ∧ ∀ k, MemLp (fun z => X z k) 2 stdNormalSeq := by
  have e : ∀ k, (fun z => X z k) = fun z => s₀ * ∏ i ∈ range (n k), F (z i) := fun k =>
    funext fun z => hX z k
  refine ⟨measurable_pi_lambda _ fun k => ?_, fun k => ?_⟩
  · rw [e k]
    exact measurable_monProd hF s₀ (n k)
  · rw [e k]
    exact memLp_monProd hF hF2 s₀ (n k)

/-- The monitored exact solution is measurable and square integrable at every date. -/
lemma measurable_memLp_gbmMonExact (r σ T s₀ : ℝ) (m j : ℕ) :
    Measurable (gbmMonExact r σ T s₀ m j) ∧
      ∀ k, MemLp (fun z => gbmMonExact r σ T s₀ m j z k) 2 stdNormalSeq :=
  measurable_memLp_monPath (measurable_gbmExpFactor r σ _) (integrable_gbmExpFactor_sq r σ _)
    (gbmMonExact_eq_prod r σ T s₀ m j)

/-- The monitored Euler–Maruyama path is measurable and square integrable at every date. -/
lemma measurable_memLp_gbmMonEM (r σ T s₀ : ℝ) (m j : ℕ) :
    Measurable (gbmMonEM r σ T s₀ m j) ∧
      ∀ k, MemLp (fun z => gbmMonEM r σ T s₀ m j z k) 2 stdNormalSeq :=
  measurable_memLp_monPath (measurable_gbmEMFactor r σ _) (integrable_gbmEMFactor_sq r σ _)
    (gbmMonEM_eq_prod r σ T s₀ m j)

/-- The monitored Milstein path is measurable and square integrable at every date. -/
lemma measurable_memLp_gbmMonMil (r σ T s₀ : ℝ) (m j : ℕ) :
    Measurable (gbmMonMil r σ T s₀ m j) ∧
      ∀ k, MemLp (fun z => gbmMonMil r σ T s₀ m j z k) 2 stdNormalSeq :=
  measurable_memLp_monPath (measurable_gbmMilFactor r σ _) (integrable_gbmMilFactor_sq r σ _)
    (gbmMonMil_eq_prod r σ T s₀ m j)

/-- **The monitored exact solution is consistent across levels** (Giles 2015, §5.1: "summing the
Brownian increments for the fine path timesteps to obtain the Brownian increments for the coarse
timesteps").  The exact solution at the dates computed from the coarse increments
`(Z_{2i} + Z_{2i+1})/√2` on the level-`j` grid is the exact solution computed from the increments
`Z_i` on the level-`(j+1)` grid: both use the same Brownian values `W_{t_k}`. -/
theorem gbmMonExact_pairAvg (r σ T s₀ : ℝ) (m j : ℕ) (z : ℕ → ℝ) :
    gbmMonExact r σ T s₀ m j (pairAvg z) = gbmMonExact r σ T s₀ m (j + 1) z := by
  funext k
  have key : Real.sqrt (T / (m * 2 ^ j)) * ∑ i ∈ range (k * 2 ^ j), pairAvg z i =
      Real.sqrt (T / (m * 2 ^ (j + 1))) * ∑ i ∈ range (k * 2 ^ (j + 1)), z i := by
    rw [show k * 2 ^ (j + 1) = 2 * (k * 2 ^ j) by ring,
      show (m : ℝ) * 2 ^ (j + 1) = m * 2 ^ j * 2 by ring, sum_range_two_mul,
      ← div_div T ((m : ℝ) * 2 ^ j) 2, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [pairAvg]
    rw [← Finset.sum_div]
    ring
  unfold gbmMonExact
  rw [key]

/-- The Euler–Maruyama strong-error constant `C(t)` of `gbmStrongConst` is nondecreasing in
`t ≥ 0`. -/
lemma gbmStrongConst_mono (r σ s₀ : ℝ) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    gbmStrongConst r σ t s₀ ≤ gbmStrongConst r σ t' s₀ := by
  unfold gbmStrongConst
  have hq : 0 ≤ |r| + σ ^ 2 := by positivity
  have h1 : 0 ≤ 5 * (|r| + σ ^ 2) * t + 4 := by positivity
  gcongr

/-- The Milstein strong-error constant `C_M(t)` of `gbmMilStrongConst` is nondecreasing in
`t ≥ 0`. -/
lemma gbmMilStrongConst_mono (r σ s₀ : ℝ) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    gbmMilStrongConst r σ t s₀ ≤ gbmMilStrongConst r σ t' s₀ := by
  unfold gbmMilStrongConst
  have hq : 0 ≤ |r| + σ ^ 2 := by positivity
  gcongr

/-- The Euler–Maruyama strong error at every monitoring date (Giles 2015, §5.1, from
`gbm_em_strong_error` at the grid time `k 2^j`): `E[(S_{t_k} − Ŝ_{t_k})²] ≤ C(T) h_j` for
`k ≤ m`. -/
lemma gbm_em_monitored_strong_error (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (m j : ℕ) {k : ℕ}
    (hk : k ≤ m) :
    ∫ z, (gbmMonExact r σ T s₀ m j z k - gbmMonEM r σ T s₀ m j z k) ^ 2 ∂stdNormalSeq ≤
      gbmStrongConst r σ T s₀ * (T / (m * 2 ^ j)) := by
  have hh : 0 ≤ T / (m * 2 ^ j) := div_nonneg hT (by positivity)
  have h := gbm_em_strong_error r σ s₀ hh (k * 2 ^ j)
  rw [monDate_eq] at h
  obtain ⟨h0, h1⟩ := monDate_mem_Icc hT hk
  exact h.trans (mul_le_mul_of_nonneg_right (gbmStrongConst_mono r σ s₀ h0 h1) hh)

/-- The Milstein strong error at every monitoring date (Giles 2015, §5.2, from
`gbm_mil_strong_error` at the grid time `k 2^j`): `E[(S_{t_k} − Ŝ_{t_k})²] ≤ C_M(T) h_j²` for
`k ≤ m`. -/
lemma gbm_mil_monitored_strong_error (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (m j : ℕ) {k : ℕ}
    (hk : k ≤ m) :
    ∫ z, (gbmMonExact r σ T s₀ m j z k - gbmMonMil r σ T s₀ m j z k) ^ 2 ∂stdNormalSeq ≤
      gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ j)) ^ 2 := by
  have hh : 0 ≤ T / (m * 2 ^ j) := div_nonneg hT (by positivity)
  have h := gbm_mil_strong_error r σ s₀ hh (k * 2 ^ j)
  rw [monDate_eq] at h
  obtain ⟨h0, h1⟩ := monDate_mem_Icc hT hk
  exact h.trans (mul_le_mul_of_nonneg_right (gbmMilStrongConst_mono r σ s₀ h0 h1) (sq_nonneg _))

/-! ### Payoffs of the monitored values

The payoffs `Φ` of the monitored values `(S_{t_0}, …, S_{t_m})` considered here satisfy
`(Φ(a) − Φ(b))² ≤ c ∑_{k=0}^m (a_k − b_k)²`, Giles' Lipschitz condition
`|P(S₁) − P(S₂)| ≤ K ‖S₁ − S₂‖` (§5.1, p. 29) for the Euclidean norm of the monitored values. -/

section Abstract

variable {m : ℕ} {Φ : (ℕ → ℝ) → ℝ} {c : ℝ}

/-- The constant of a monitored Lipschitz payoff is nonnegative. -/
lemma monPayoff_const_nonneg
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2) :
    0 ≤ c := by
  have h := hΦ (fun _ => 1) (fun _ => 0)
  simp only [sub_zero, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  exact nonneg_of_mul_nonneg_left ((sq_nonneg _).trans h) (by positivity)

/-- A monitored Lipschitz payoff is measurable: it depends only on the values at `0, …, m`, and
continuously so. -/
lemma measurable_monPayoff
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2) :
    Measurable Φ := by
  have hc := monPayoff_const_nonneg hΦ
  let ext : (Fin (m + 1) → ℝ) → ℕ → ℝ := fun x k => if h : k < m + 1 then x ⟨k, h⟩ else 0
  let proj : (ℕ → ℝ) → Fin (m + 1) → ℝ := fun a i => a i
  have hproj : Measurable proj := measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
  have hcm : 0 ≤ c * (m + 1) := mul_nonneg hc (by positivity)
  have hL : LipschitzWith (Real.sqrt (c * (m + 1))).toNNReal (fun x => Φ (ext x)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), Real.dist_eq]
    have hsum : ∑ k ∈ range (m + 1), (ext x k - ext y k) ^ 2 ≤ (m + 1) * dist x y ^ 2 := by
      have hk : ∀ k ∈ range (m + 1), (ext x k - ext y k) ^ 2 ≤ dist x y ^ 2 := fun k hk => by
        have hk' : k < m + 1 := Finset.mem_range.1 hk
        have h1 := dist_le_pi_dist x y ⟨k, hk'⟩
        rw [Real.dist_eq] at h1
        simp only [ext, dif_pos hk']
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc ∑ k ∈ range (m + 1), (ext x k - ext y k) ^ 2 ≤ ∑ _k ∈ range (m + 1), dist x y ^ 2 :=
            Finset.sum_le_sum hk
        _ = (m + 1) * dist x y ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have h2 : (Φ (ext x) - Φ (ext y)) ^ 2 ≤ (Real.sqrt (c * (m + 1)) * dist x y) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hcm]
      calc _ ≤ c * ∑ k ∈ range (m + 1), (ext x k - ext y k) ^ 2 := hΦ _ _
        _ ≤ c * ((m + 1) * dist x y ^ 2) := mul_le_mul_of_nonneg_left hsum hc
        _ = _ := by ring
    have h3 := sq_le_sq.1 h2
    rwa [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)] at h3
  have e : Φ = (fun x => Φ (ext x)) ∘ proj := by
    funext a
    have h := hΦ a (ext (proj a))
    have hz : ∑ k ∈ range (m + 1), (a k - ext (proj a) k) ^ 2 = 0 :=
      Finset.sum_eq_zero fun k hk => by
        simp only [ext, proj, dif_pos (Finset.mem_range.1 hk), sub_self]
        norm_num
    rw [hz, mul_zero] at h
    have h0 : Φ a - Φ (ext (proj a)) = 0 :=
      (pow_eq_zero_iff two_ne_zero).1 (le_antisymm h (sq_nonneg _))
    exact sub_eq_zero.1 h0
  rw [e]
  exact hL.continuous.measurable.comp hproj

/-- A monitored Lipschitz payoff of a path that is square integrable at every date is square
integrable. -/
lemma memLp_monPayoff
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2)
    {X : (ℕ → ℝ) → ℕ → ℝ} (hXm : Measurable X)
    (hX : ∀ k, MemLp (fun z => X z k) 2 stdNormalSeq) :
    MemLp (fun z => Φ (X z)) 2 stdNormalSeq := by
  have hm : AEStronglyMeasurable (fun z => Φ (X z)) stdNormalSeq :=
    ((measurable_monPayoff hΦ).comp hXm).aestronglyMeasurable
  have hb : Integrable (fun z => 2 * Φ 0 ^ 2 + 2 * c * ∑ k ∈ range (m + 1), X z k ^ 2)
      stdNormalSeq :=
    (integrable_const _).add
      ((integrable_finsetSum _ fun k _ => (hX k).integrable_sq).const_mul _)
  refine (memLp_two_iff_integrable_sq hm).2
    (hb.mono' (hm.pow 2) (Filter.Eventually.of_forall fun z => ?_))
  have h1 := hΦ (X z) 0
  simp only [Pi.zero_apply, sub_zero] at h1
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (Φ (X z) - 2 * Φ 0)]

/-- **Mean square error of a monitored Lipschitz payoff from the strong error at the dates**
(Giles 2015, §5.1: "`E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`"): if the two paths agree at `t_0` and
`E[(X_{t_k} − Y_{t_k})²] ≤ e` at the dates `t_1, …, t_m`, then `E[(Φ(X) − Φ(Y))²] ≤ c m e`. -/
lemma integral_sq_monPayoff_sub_le
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2)
    {X Y : (ℕ → ℝ) → ℕ → ℝ}
    (hX : ∀ k, MemLp (fun z => X z k) 2 stdNormalSeq)
    (hY : ∀ k, MemLp (fun z => Y z k) 2 stdNormalSeq) (h0 : ∀ z, X z 0 = Y z 0) {e : ℝ}
    (hs : ∀ k, k < m → ∫ z, (X z (k + 1) - Y z (k + 1)) ^ 2 ∂stdNormalSeq ≤ e) :
    ∫ z, (Φ (X z) - Φ (Y z)) ^ 2 ∂stdNormalSeq ≤ c * (m * e) := by
  have hc := monPayoff_const_nonneg hΦ
  have hI : ∀ k, Integrable (fun z => (X z k - Y z k) ^ 2) stdNormalSeq := fun k =>
    ((hX k).sub (hY k)).integrable_sq
  have hS : Integrable (fun z => ∑ k ∈ range (m + 1), (X z k - Y z k) ^ 2) stdNormalSeq :=
    integrable_finsetSum _ fun k _ => hI k
  have hsum : ∫ z, ∑ k ∈ range (m + 1), (X z k - Y z k) ^ 2 ∂stdNormalSeq ≤ m * e := by
    rw [integral_finsetSum _ fun k _ => hI k, Finset.sum_range_succ']
    have h00 : ∫ z, (X z 0 - Y z 0) ^ 2 ∂stdNormalSeq = 0 := by simp [h0]
    rw [h00, add_zero]
    calc ∑ k ∈ range m, ∫ z, (X z (k + 1) - Y z (k + 1)) ^ 2 ∂stdNormalSeq
        ≤ ∑ _k ∈ range m, e := Finset.sum_le_sum fun k hk => hs k (Finset.mem_range.1 hk)
      _ = m * e := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∫ z, (Φ (X z) - Φ (Y z)) ^ 2 ∂stdNormalSeq
      ≤ ∫ z, c * ∑ k ∈ range (m + 1), (X z k - Y z k) ^ 2 ∂stdNormalSeq :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
          (hS.const_mul c) (Filter.Eventually.of_forall fun z => hΦ (X z) (Y z))
    _ = c * ∫ z, ∑ k ∈ range (m + 1), (X z k - Y z k) ^ 2 ∂stdNormalSeq :=
        integral_const_mul _ _
    _ ≤ c * (m * e) := mul_le_mul_of_nonneg_left hsum hc

/-- The bias from the mean square error: `|E[Φ(Y) − Φ(X)]| ≤ √(c m e)` under the hypotheses of
`integral_sq_monPayoff_sub_le` (Jensen's inequality). -/
lemma abs_integral_monPayoff_sub_le
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2)
    {X Y : (ℕ → ℝ) → ℕ → ℝ} (hXm : Measurable X) (hYm : Measurable Y)
    (hX : ∀ k, MemLp (fun z => X z k) 2 stdNormalSeq)
    (hY : ∀ k, MemLp (fun z => Y z k) 2 stdNormalSeq) (h0 : ∀ z, X z 0 = Y z 0) {e : ℝ}
    (hs : ∀ k, k < m → ∫ z, (X z (k + 1) - Y z (k + 1)) ^ 2 ∂stdNormalSeq ≤ e) :
    |∫ z, Φ (Y z) - Φ (X z) ∂stdNormalSeq| ≤ Real.sqrt (c * (m * e)) := by
  have hD : MemLp (fun z => Φ (Y z) - Φ (X z)) 2 stdNormalSeq :=
    (memLp_monPayoff hΦ hYm hY).sub (memLp_monPayoff hΦ hXm hX)
  have h1 := sq_integral_le_integral_sq_of_memLp hD
  have h2 := integral_sq_monPayoff_sub_le hΦ hX hY h0 hs
  have e1 : ∫ z, (Φ (Y z) - Φ (X z)) ^ 2 ∂stdNormalSeq =
      ∫ z, (Φ (X z) - Φ (Y z)) ^ 2 ∂stdNormalSeq := by
    congr 1
    funext z
    ring
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (h1.trans (e1.le.trans h2))

/-- The expectation of a measurable function of a level-consistent path does not depend on the
level: if `X_j ∘ pairAvg = X_{j+1}`, then `E[F(X_j)] = E[F(X_0)]` (the coarse increments are again
independent standard normal, `measurePreserving_pairAvg`). -/
lemma integral_comp_monLevel {X : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    (hpair : ∀ j z, X j (pairAvg z) = X (j + 1) z) (hXm : ∀ j, Measurable (X j))
    {F : (ℕ → ℝ) → ℝ} (hF : Measurable F) (j : ℕ) :
    ∫ z, F (X j z) ∂stdNormalSeq = ∫ z, F (X 0 z) ∂stdNormalSeq := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih]
    have e : (fun z => F (X (j + 1) z)) = fun z => F (X j (pairAvg z)) :=
      funext fun z => by rw [hpair]
    rw [e]
    exact integral_comp_of_measurePreserving measurePreserving_pairAvg
      (hF.comp (hXm j)).aestronglyMeasurable

/-- **The correction variance from the mean square errors** (Giles 2015, §5.1:
"`V_ℓ ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`").  For level-consistent exact paths `X_j` and
approximations `Y_j` with `E[(X_{j,t_k} − Y_{j,t_k})²] ≤ e_j` at the dates, the correction
`Φ(Y_{j+1}) − Φ(Y_j ∘ pairAvg)` has variance at most `2 c m e_{j+1} + 2 c m e_j`. -/
lemma variance_monPayoff_sub_le
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2)
    {X Y : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    (hXm : ∀ j, Measurable (X j)) (hYm : ∀ j, Measurable (Y j))
    (hX : ∀ j k, MemLp (fun z => X j z k) 2 stdNormalSeq)
    (hY : ∀ j k, MemLp (fun z => Y j z k) 2 stdNormalSeq) (h0 : ∀ j z, X j z 0 = Y j z 0)
    (hpair : ∀ j z, X j (pairAvg z) = X (j + 1) z) {e : ℕ → ℝ}
    (hs : ∀ j k, k < m → ∫ z, (X j z (k + 1) - Y j z (k + 1)) ^ 2 ∂stdNormalSeq ≤ e j)
    (j : ℕ) :
    variance (fun z => Φ (Y (j + 1) z) - Φ (Y j (pairAvg z))) stdNormalSeq ≤
      2 * (c * (m * e (j + 1))) + 2 * (c * (m * e j)) := by
  have hΦm := measurable_monPayoff hΦ
  have hPX : ∀ j, MemLp (fun z => Φ (X j z)) 2 stdNormalSeq := fun j =>
    memLp_monPayoff hΦ (hXm j) (hX j)
  have hPY : ∀ j, MemLp (fun z => Φ (Y j z)) 2 stdNormalSeq := fun j =>
    memLp_monPayoff hΦ (hYm j) (hY j)
  have hYc : Measurable fun z => Φ (Y j (pairAvg z)) :=
    (hΦm.comp (hYm j)).comp measurePreserving_pairAvg.measurable
  have hm : AEStronglyMeasurable (fun z => Φ (Y (j + 1) z) - Φ (Y j (pairAvg z))) stdNormalSeq :=
    ((hΦm.comp (hYm (j + 1))).sub hYc).aestronglyMeasurable
  refine (variance_le_expectation_sq hm).trans ?_
  simp only [Pi.pow_apply]
  have hI1 : Integrable (fun z => (Φ (X (j + 1) z) - Φ (Y (j + 1) z)) ^ 2) stdNormalSeq :=
    ((hPX (j + 1)).sub (hPY (j + 1))).integrable_sq
  have hI0' : Integrable (fun z => (Φ (X j z) - Φ (Y j z)) ^ 2) stdNormalSeq :=
    ((hPX j).sub (hPY j)).integrable_sq
  have hI0 : Integrable (fun z => (Φ (X j (pairAvg z)) - Φ (Y j (pairAvg z))) ^ 2) stdNormalSeq :=
    (measurePreserving_pairAvg.integrable_comp hI0'.aestronglyMeasurable).2 hI0'
  have hpt : ∀ z, (Φ (Y (j + 1) z) - Φ (Y j (pairAvg z))) ^ 2 ≤
      2 * (Φ (X (j + 1) z) - Φ (Y (j + 1) z)) ^ 2 +
        2 * (Φ (X j (pairAvg z)) - Φ (Y j (pairAvg z))) ^ 2 := fun z => by
    rw [hpair j z]
    nlinarith [sq_nonneg (Φ (X (j + 1) z) - Φ (Y (j + 1) z) +
      (Φ (X (j + 1) z) - Φ (Y j (pairAvg z))))]
  have hs1 := integral_sq_monPayoff_sub_le hΦ (hX (j + 1)) (hY (j + 1)) (h0 (j + 1)) (hs (j + 1))
  have hs0 := integral_sq_monPayoff_sub_le hΦ (hX j) (hY j) (h0 j) (hs j)
  calc ∫ z, (Φ (Y (j + 1) z) - Φ (Y j (pairAvg z))) ^ 2 ∂stdNormalSeq
      ≤ ∫ z, (2 * (Φ (X (j + 1) z) - Φ (Y (j + 1) z)) ^ 2 +
          2 * (Φ (X j (pairAvg z)) - Φ (Y j (pairAvg z))) ^ 2) ∂stdNormalSeq :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
          ((hI1.const_mul 2).add (hI0.const_mul 2)) (Filter.Eventually.of_forall hpt)
    _ = 2 * ∫ z, (Φ (X (j + 1) z) - Φ (Y (j + 1) z)) ^ 2 ∂stdNormalSeq +
          2 * ∫ z, (Φ (X j z) - Φ (Y j z)) ^ 2 ∂stdNormalSeq := by
        rw [integral_add (hI1.const_mul _) (hI0.const_mul _), integral_const_mul,
          integral_const_mul, integral_comp_of_measurePreserving measurePreserving_pairAvg
            hI0'.aestronglyMeasurable]
    _ ≤ 2 * (c * (m * e (j + 1))) + 2 * (c * (m * e j)) :=
        add_le_add (mul_le_mul_of_nonneg_left hs1 zero_le_two)
          (mul_le_mul_of_nonneg_left hs0 zero_le_two)

end Abstract

/-! ### Step-size bounds -/

/-- `h_j = T/(m 2^j) ≤ T 2^{−j}` for `m ≥ 1`. -/
lemma monStep_le {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    T / (m * 2 ^ j) ≤ T * ((2 : ℝ) ^ j)⁻¹ := by
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hT
  exact le_mul_of_one_le_left (by positivity) (Nat.one_le_cast.2 hm)

/-- `h_j² = (T/(m 2^j))² ≤ T² 4^{−j}` for `m ≥ 1`. -/
lemma monStep_sq_le {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    (T / (m * 2 ^ j)) ^ 2 ≤ T ^ 2 * ((4 : ℝ) ^ j)⁻¹ := by
  have h := pow_le_pow_left₀ (div_nonneg hT (by positivity)) (monStep_le hT hm j) 2
  have e4 : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
    rw [pow_right_comm]
    norm_num
  rw [e4, ← inv_pow, ← mul_pow]
  exact h

/-! ### The Euler–Maruyama scheme -/

/-- **Mean square error of a discretely monitored Lipschitz payoff, Euler–Maruyama** (Giles 2015,
§5.1, p. 29: "For Lipschitz payoff functions `P` (such as European, Asian and lookback options …) …
`E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`" and "`E[‖S − Ŝ‖²] = O(h)`").  For GBM, monitoring dates
`t_k = kT/m`, level `j` with `m 2^j` steps of size `h_j = T/(m 2^j)`, and a payoff `Φ` of the
monitored values with `(Φ(a) − Φ(b))² ≤ c ∑_{k=0}^m (a_k − b_k)²`:
`E[(Φ(S) − Φ(Ŝ_j))²] ≤ c m C(T) h_j`, with `C = gbmStrongConst` and `S` the exact solution driven by
the same increments.  Discrete monitoring only (see the module docstring).  For `m = 0` the
statement is degenerate and trivially true (both paths equal `s₀` at the only date `t_0`, and the
bound carries the factor `m = 0`). -/
theorem gbm_em_monitored_mse_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {Φ : (ℕ → ℝ) → ℝ} {c : ℝ}
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2) (j : ℕ) :
    ∫ z, (Φ (gbmMonExact r σ T s₀ m j z) - Φ (gbmMonEM r σ T s₀ m j z)) ^ 2 ∂stdNormalSeq ≤
      c * m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ j)) := by
  have h := integral_sq_monPayoff_sub_le hΦ (measurable_memLp_gbmMonExact r σ T s₀ m j).2
    (measurable_memLp_gbmMonEM r σ T s₀ m j).2
    (fun z => (gbmMonExact_zero r σ T s₀ m j z).trans (gbmMonEM_zero r σ T s₀ m j z).symm)
    (fun k hk => gbm_em_monitored_strong_error r σ s₀ hT m j (k := k + 1) hk)
  exact h.trans_eq (by ring)

/-- **Weak error of a discretely monitored Lipschitz payoff, Euler–Maruyama** (Giles 2015, §5.1,
p. 29; condition (i) of Theorem 1, §2.1, p. 6, with `α = ½`).  In the setting of
`gbm_em_monitored_mse_le`, `|E[Φ(Ŝ_j)] − E[Φ(S)]| ≤ √(c m C(T) h_j)`, where `E[Φ(S)]` is computed
from the exact solution at the dates (`gbmMonExact … 0`, whose law is that of every level).  The
paper's weak order `α = 1` (§5.1, p. 30) is not proved; `α = ½` suffices for Theorem 1.  For
`m = 0` the statement is degenerate and trivially true (see `gbm_em_monitored_mse_le`). -/
theorem gbm_em_monitored_bias_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {Φ : (ℕ → ℝ) → ℝ} {c : ℝ}
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2) (j : ℕ) :
    |∫ z, Φ (gbmMonEM r σ T s₀ m j z) - Φ (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq| ≤
      Real.sqrt (c * m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ j))) := by
  obtain ⟨hXm, hX⟩ := measurable_memLp_gbmMonExact r σ T s₀ m j
  obtain ⟨hYm, hY⟩ := measurable_memLp_gbmMonEM r σ T s₀ m j
  have hPY := memLp_monPayoff hΦ hYm hY
  have hPX : ∀ i, MemLp (fun z => Φ (gbmMonExact r σ T s₀ m i z)) 2 stdNormalSeq := fun i =>
    memLp_monPayoff hΦ (measurable_memLp_gbmMonExact r σ T s₀ m i).1
      (measurable_memLp_gbmMonExact r σ T s₀ m i).2
  have e1 : ∫ z, Φ (gbmMonEM r σ T s₀ m j z) - Φ (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq =
      ∫ z, Φ (gbmMonEM r σ T s₀ m j z) - Φ (gbmMonExact r σ T s₀ m j z) ∂stdNormalSeq := by
    rw [integral_sub (hPY.integrable one_le_two) ((hPX 0).integrable one_le_two),
      integral_sub (hPY.integrable one_le_two) ((hPX j).integrable one_le_two),
      integral_comp_monLevel (gbmMonExact_pairAvg r σ T s₀ m)
        (fun i => (measurable_memLp_gbmMonExact r σ T s₀ m i).1) (measurable_monPayoff hΦ) j]
  rw [e1]
  have h := abs_integral_monPayoff_sub_le hΦ hXm hYm hX hY
    (fun z => (gbmMonExact_zero r σ T s₀ m j z).trans (gbmMonEM_zero r σ T s₀ m j z).symm)
    (fun k hk => gbm_em_monitored_strong_error r σ s₀ hT m j (k := k + 1) hk)
  exact h.trans_eq (by congr 1; ring)

/-- **Correction variance of a discretely monitored Lipschitz payoff, Euler–Maruyama** (Giles 2015,
§5.1, p. 29: "`V_ℓ ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`, and hence `V_ℓ = O(h_ℓ)`"; Table 5.2, p. 33,
Euler–Maruyama column; Theorem 1 (iii) with `β = 1`).  The correction on level `j + 1` is the
payoff of the fine path minus the payoff of the coarse path driven by the summed increments
`(Z_{2i} + Z_{2i+1})/√2`; its variance is at most `6 c m C(T) h_{j+1}`, `h_{j+1} = T/(m 2^{j+1})`.
For `m = 0` the statement is degenerate and trivially true (see `gbm_em_monitored_mse_le`). -/
theorem gbm_em_monitored_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {Φ : (ℕ → ℝ) → ℝ} {c : ℝ}
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2) (j : ℕ) :
    variance (fun z => Φ (gbmMonEM r σ T s₀ m (j + 1) z) - Φ (gbmMonEM r σ T s₀ m j (pairAvg z)))
        stdNormalSeq ≤
      6 * c * m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ (j + 1))) := by
  have h := variance_monPayoff_sub_le hΦ (fun i => (measurable_memLp_gbmMonExact r σ T s₀ m i).1)
    (fun i => (measurable_memLp_gbmMonEM r σ T s₀ m i).1)
    (fun i => (measurable_memLp_gbmMonExact r σ T s₀ m i).2)
    (fun i => (measurable_memLp_gbmMonEM r σ T s₀ m i).2)
    (fun i z => (gbmMonExact_zero r σ T s₀ m i z).trans (gbmMonEM_zero r σ T s₀ m i z).symm)
    (gbmMonExact_pairAvg r σ T s₀ m) (e := fun i => gbmStrongConst r σ T s₀ * (T / (m * 2 ^ i)))
    (fun i k hk => gbm_em_monitored_strong_error r σ s₀ hT m i (k := k + 1) hk) j
  have e2 : T / (m * 2 ^ j) = 2 * (T / (m * 2 ^ (j + 1))) := by
    rw [pow_succ, ← mul_assoc, ← div_div T ((m : ℝ) * 2 ^ j) 2, mul_div_cancel₀ _ two_ne_zero]
  beta_reduce at h
  rw [e2] at h
  exact h.trans_eq (by ring)

/-- **Theorem 1 for the Euler–Maruyama MLMC estimator of a discretely monitored payoff of GBM**
(Giles 2015, §5.1, p. 30: "then `α = 1, β = 1` and `γ = 1`.  In either case, Theorem 1 gives the
complexity to achieve a root-mean-square error of `ε` to be `O(ε⁻²(log ε)²)`", with Theorem 1,
§2.1, pp. 6–7, and (2.4), §2.1, p. 8; Table 5.2, p. 33).  Let `T ≥ 0`, `m ≥ 1` monitoring
intervals, and `Φ` a payoff of the monitored values with
`(Φ(a) − Φ(b))² ≤ c ∑_{k=0}^m (a_k − b_k)²`.  Level `j` uses `m 2^j` Euler–Maruyama steps of size
`h_j = T/(m 2^j)`; its correction is the payoff of the fine path minus the payoff of the coarse path
driven by the summed increments; the samples are independent and a level-`j` sample costs `m 2^j`.
Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_j ≥ 1` with a
square-integrable error, mean square error `< ε²` for `E[Φ(S_{t_0}, …, S_{t_m})]` and cost
`∑_{j≤L} N_j m 2^j ≤ c₄ ε⁻²(log ε)²`; here `S = gbmMonExact … 0`, i.e.
`S_{t_k} = s₀ exp((r − σ²/2) kT/m + σ √(T/m) ∑_{i<k} Z_i)` (`gbmMonExact_level_zero`).  No rate is
assumed: `α = ½` (`gbm_em_monitored_bias_le`), `β = 1` (`gbm_em_monitored_variance_le`) and (2.4)
are proved.  The paper's `α = 1` is not proved; `α = ½` suffices because Theorem 1 only needs
`α ≥ ½ min(β, γ) = ½`. -/
theorem gbm_em_monitored_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {Φ : (ℕ → ℝ) → ℝ} {c : ℝ}
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ j, 0 < N j) ∧
        Integrable (fun x => (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => Φ (gbmMonEM r σ T s₀ m j z))
              (fun j z => Φ (gbmMonEM r σ T s₀ m j (pairAvg z)))) (fun p x => x p) j (N j) x -
            ∫ z, Φ (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => Φ (gbmMonEM r σ T s₀ m j z))
              (fun j z => Φ (gbmMonEM r σ T s₀ m j (pairAvg z)))) (fun p x => x p) j (N j) x -
            ∫ z, Φ (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) ≤
          c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) := by
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hΦm := measurable_monPayoff hΦ
  have hc := monPayoff_const_nonneg hΦ
  have hC := gbmStrongConst_nonneg r σ s₀ hT
  have hcmC : 0 ≤ c * m * gbmStrongConst r σ T s₀ :=
    mul_nonneg (mul_nonneg hc (Nat.cast_nonneg m)) hC
  have hB : 0 ≤ c * m * gbmStrongConst r σ T s₀ * T := mul_nonneg hcmC hT
  have hP : MemLp (fun z => Φ (gbmMonExact r σ T s₀ m 0 z)) 2 stdNormalSeq :=
    memLp_monPayoff hΦ (measurable_memLp_gbmMonExact r σ T s₀ m 0).1
      (measurable_memLp_gbmMonExact r σ T s₀ m 0).2
  have hPf : ∀ j, MemLp (fun z => Φ (gbmMonEM r σ T s₀ m j z)) 2 stdNormalSeq := fun j =>
    memLp_monPayoff hΦ (measurable_memLp_gbmMonEM r σ T s₀ m j).1
      (measurable_memLp_gbmMonEM r σ T s₀ m j).2
  have hPfm : ∀ j, Measurable (fun z => Φ (gbmMonEM r σ T s₀ m j z)) := fun j =>
    hΦm.comp (measurable_memLp_gbmMonEM r σ T s₀ m j).1
  have hPcm : ∀ j, Measurable (fun z => Φ (gbmMonEM r σ T s₀ m j (pairAvg z))) := fun j =>
    (hPfm j).comp measurePreserving_pairAvg.measurable
  have hPc : ∀ j, MemLp (fun z => Φ (gbmMonEM r σ T s₀ m j (pairAvg z))) 2 stdNormalSeq :=
    fun j => (hPf j).comp_measurePreserving measurePreserving_pairAvg
  -- (2.4): the coarse path has the law of the fine path of the level below
  have h24 : ∀ j, ∫ z, Φ (gbmMonEM r σ T s₀ m j z) ∂stdNormalSeq =
      ∫ z, Φ (gbmMonEM r σ T s₀ m j (pairAvg z)) ∂stdNormalSeq := fun j =>
    (integral_comp_of_measurePreserving measurePreserving_pairAvg
      (hPfm j).aestronglyMeasurable).symm
  -- (i): the weak rate `α = ½`
  have hc₁ : 0 < Real.sqrt (c * m * gbmStrongConst r σ T s₀ * T) + 1 := by positivity
  have h_i : ∀ j : ℕ, |∫ z, Φ (gbmMonEM r σ T s₀ m j z) - Φ (gbmMonExact r σ T s₀ m 0 z)
      ∂stdNormalSeq| ≤
      (Real.sqrt (c * m * gbmStrongConst r σ T s₀ * T) + 1) * (2 : ℝ) ^ (-(1 / 2 * (j : ℝ))) :=
    fun j => by
    have h := gbm_em_monitored_bias_le r σ s₀ hT hΦ j
    have hpos : 0 < (2 : ℝ) ^ (-(1 / 2 * (j : ℝ))) := by positivity
    have hs2 : Real.sqrt (((2 : ℝ) ^ j)⁻¹) = (2 : ℝ) ^ (-(1 / 2 * (j : ℝ))) := by
      rw [← rpow_neg_half_mul_sq j, Real.sqrt_sq hpos.le]
    have hle : c * m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ j)) ≤
        c * m * gbmStrongConst r σ T s₀ * T * ((2 : ℝ) ^ j)⁻¹ := by
      rw [mul_assoc (c * m * gbmStrongConst r σ T s₀) T]
      exact mul_le_mul_of_nonneg_left (monStep_le hT hm j) hcmC
    calc _ ≤ _ := h
      _ ≤ Real.sqrt (c * m * gbmStrongConst r σ T s₀ * T * ((2 : ℝ) ^ j)⁻¹) :=
          Real.sqrt_le_sqrt hle
      _ = Real.sqrt (c * m * gbmStrongConst r σ T s₀ * T) * (2 : ℝ) ^ (-(1 / 2 * (j : ℝ))) := by
          rw [Real.sqrt_mul hB, hs2]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hpos.le
  -- (iii): the variance rate `β = 1`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (fineCoarseDiff (fun j z => Φ (gbmMonEM r σ T s₀ m j z))
      (fun j z => Φ (gbmMonEM r σ T s₀ m j (pairAvg z))) 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by
    rw [hV₀]
    exact variance_nonneg _ _
  have hc₂ : 0 < V₀ + 6 * (c * m * gbmStrongConst r σ T s₀ * T) + 1 := by linarith
  have h_iii : ∀ j, variance (fineCoarseDiff (fun j z => Φ (gbmMonEM r σ T s₀ m j z))
      (fun j z => Φ (gbmMonEM r σ T s₀ m j (pairAvg z))) j) stdNormalSeq ≤
      (V₀ + 6 * (c * m * gbmStrongConst r σ T s₀ * T) + 1) * (2 : ℝ) ^ (-(1 * (j : ℝ))) := by
    intro j
    rw [one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    cases j with
    | zero =>
      rw [← hV₀, pow_zero, inv_one, mul_one]
      linarith
    | succ j =>
      have hv := gbm_em_monitored_variance_le r σ s₀ hT hΦ j
      have hle : 6 * c * m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ (j + 1))) ≤
          6 * (c * m * gbmStrongConst r σ T s₀ * T) * ((2 : ℝ) ^ (j + 1))⁻¹ := by
        have h6 : 0 ≤ 6 * c * m * gbmStrongConst r σ T s₀ := by linarith
        exact (mul_le_mul_of_nonneg_left (monStep_le hT hm (j + 1)) h6).trans_eq (by ring)
      have hinv : 0 < ((2 : ℝ) ^ (j + 1))⁻¹ := by positivity
      exact hv.trans (hle.trans (by nlinarith [mul_nonneg hV₀0 hinv.le]))
  -- (iv): a level-`j` sample costs `m 2^j`
  have h_iv : ∀ j : ℕ, (m : ℝ) * 2 ^ j ≤ m * (2 : ℝ) ^ ((1 : ℝ) * (j : ℝ)) := fun j => by
    rw [one_mul, Real.rpow_natCast]
  have hαβγ : min (1 : ℝ) 1 / 2 ≤ 1 / 2 := by norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq)
    (fun z => Φ (gbmMonExact r σ T s₀ m 0 z)) (fun j z => Φ (gbmMonEM r σ T s₀ m j z))
    (fun j z => Φ (gbmMonEM r σ T s₀ m j (pairAvg z))) (fun p x => x p)
    (fun j _ _ => (m : ℝ) * 2 ^ j) (fun j => (m : ℝ) * 2 ^ j) (α := 1 / 2) (β := 1) (γ := 1)
    (by norm_num) one_pos one_pos hc₁ hc₂ (Nat.cast_pos.2 hm) hαβγ hω hind
    (hP.integrable one_le_two) hPfm hPcm hPf hPc h24 (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, ((memLp_finsetSum _ fun j _ =>
    memLp_blockMean hω (memLp_fineCoarseDiff hPf hPc) j (N j)).sub (memLp_const _)).integrable_sq,
    hmse, ?_⟩
  simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul] at hcost
  rw [complexityBound_of_eq rfl ε] at hcost
  exact hcost

/-! ### The Milstein scheme -/

/-- **Mean square error of a discretely monitored Lipschitz payoff, Milstein** (Giles 2015, §5.2,
p. 35: the Milstein discretisation "gives first order strong convergence", and §5.1, p. 29:
"`E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`").  In the setting of `gbm_em_monitored_mse_le` with the
Milstein scheme, `E[(Φ(S) − Φ(Ŝ_j))²] ≤ c m C_M(T) h_j²`, `C_M = gbmMilStrongConst`.  For `m = 0`
the statement is degenerate and trivially true (see `gbm_em_monitored_mse_le`). -/
theorem gbm_mil_monitored_mse_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {Φ : (ℕ → ℝ) → ℝ} {c : ℝ}
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2) (j : ℕ) :
    ∫ z, (Φ (gbmMonExact r σ T s₀ m j z) - Φ (gbmMonMil r σ T s₀ m j z)) ^ 2 ∂stdNormalSeq ≤
      c * m * gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ j)) ^ 2 := by
  have h := integral_sq_monPayoff_sub_le hΦ (measurable_memLp_gbmMonExact r σ T s₀ m j).2
    (measurable_memLp_gbmMonMil r σ T s₀ m j).2
    (fun z => (gbmMonExact_zero r σ T s₀ m j z).trans (gbmMonMil_zero r σ T s₀ m j z).symm)
    (fun k hk => gbm_mil_monitored_strong_error r σ s₀ hT m j (k := k + 1) hk)
  exact h.trans_eq (by ring)

/-- **Weak error of a discretely monitored Lipschitz payoff, Milstein** (Giles 2015, §5.2, p. 35:
"`α = 1`"; Theorem 1 (i), §2.1, p. 6).  In the setting of `gbm_mil_monitored_mse_le`,
`|E[Φ(Ŝ_j)] − E[Φ(S)]| ≤ √(c m C_M(T)) h_j`, with `E[Φ(S)]` computed from `gbmMonExact … 0`.  For
`m = 0` the statement is degenerate and trivially true (see `gbm_em_monitored_mse_le`). -/
theorem gbm_mil_monitored_bias_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {Φ : (ℕ → ℝ) → ℝ} {c : ℝ}
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2) (j : ℕ) :
    |∫ z, Φ (gbmMonMil r σ T s₀ m j z) - Φ (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq| ≤
      Real.sqrt (c * m * gbmMilStrongConst r σ T s₀) * (T / (m * 2 ^ j)) := by
  obtain ⟨hXm, hX⟩ := measurable_memLp_gbmMonExact r σ T s₀ m j
  obtain ⟨hYm, hY⟩ := measurable_memLp_gbmMonMil r σ T s₀ m j
  have hPY := memLp_monPayoff hΦ hYm hY
  have hPX : ∀ i, MemLp (fun z => Φ (gbmMonExact r σ T s₀ m i z)) 2 stdNormalSeq := fun i =>
    memLp_monPayoff hΦ (measurable_memLp_gbmMonExact r σ T s₀ m i).1
      (measurable_memLp_gbmMonExact r σ T s₀ m i).2
  have e1 : ∫ z, Φ (gbmMonMil r σ T s₀ m j z) - Φ (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq =
      ∫ z, Φ (gbmMonMil r σ T s₀ m j z) - Φ (gbmMonExact r σ T s₀ m j z) ∂stdNormalSeq := by
    rw [integral_sub (hPY.integrable one_le_two) ((hPX 0).integrable one_le_two),
      integral_sub (hPY.integrable one_le_two) ((hPX j).integrable one_le_two),
      integral_comp_monLevel (gbmMonExact_pairAvg r σ T s₀ m)
        (fun i => (measurable_memLp_gbmMonExact r σ T s₀ m i).1) (measurable_monPayoff hΦ) j]
  rw [e1]
  have h := abs_integral_monPayoff_sub_le hΦ hXm hYm hX hY
    (fun z => (gbmMonExact_zero r σ T s₀ m j z).trans (gbmMonMil_zero r σ T s₀ m j z).symm)
    (fun k hk => gbm_mil_monitored_strong_error r σ s₀ hT m j (k := k + 1) hk)
  have hcmC : 0 ≤ c * m * gbmMilStrongConst r σ T s₀ :=
    mul_nonneg (mul_nonneg (monPayoff_const_nonneg hΦ) (Nat.cast_nonneg m))
      (gbmMilStrongConst_nonneg r σ s₀ hT)
  have hh : 0 ≤ T / (m * 2 ^ j) := div_nonneg hT (by positivity)
  refine h.trans_eq ?_
  rw [show c * (m * (gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ j)) ^ 2)) =
      c * m * gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ j)) ^ 2 by ring,
    Real.sqrt_mul hcmC, Real.sqrt_sq hh]

/-- **Correction variance of a discretely monitored Lipschitz payoff, Milstein** (Giles 2015, §5.2,
p. 35: "`V_ℓ` is now `O(h_ℓ²)`, leading to `α = 1, β = 2, γ = 1`"; Table 5.2, p. 33, Milstein
column; Theorem 1 (iii) with `β = 2`).  The correction on level `j + 1` (fine path minus coarse path
driven by the summed increments) has variance at most `10 c m C_M(T) h_{j+1}²`.  For `m = 0` the
statement is degenerate and trivially true (see `gbm_em_monitored_mse_le`). -/
theorem gbm_mil_monitored_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {Φ : (ℕ → ℝ) → ℝ} {c : ℝ}
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2) (j : ℕ) :
    variance (fun z => Φ (gbmMonMil r σ T s₀ m (j + 1) z) -
        Φ (gbmMonMil r σ T s₀ m j (pairAvg z))) stdNormalSeq ≤
      10 * c * m * gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ (j + 1))) ^ 2 := by
  have h := variance_monPayoff_sub_le hΦ (fun i => (measurable_memLp_gbmMonExact r σ T s₀ m i).1)
    (fun i => (measurable_memLp_gbmMonMil r σ T s₀ m i).1)
    (fun i => (measurable_memLp_gbmMonExact r σ T s₀ m i).2)
    (fun i => (measurable_memLp_gbmMonMil r σ T s₀ m i).2)
    (fun i z => (gbmMonExact_zero r σ T s₀ m i z).trans (gbmMonMil_zero r σ T s₀ m i z).symm)
    (gbmMonExact_pairAvg r σ T s₀ m)
    (e := fun i => gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ i)) ^ 2)
    (fun i k hk => gbm_mil_monitored_strong_error r σ s₀ hT m i (k := k + 1) hk) j
  have e2 : T / (m * 2 ^ j) = 2 * (T / (m * 2 ^ (j + 1))) := by
    rw [pow_succ, ← mul_assoc, ← div_div T ((m : ℝ) * 2 ^ j) 2, mul_div_cancel₀ _ two_ne_zero]
  beta_reduce at h
  rw [e2] at h
  exact h.trans_eq (by ring)

/-- **Theorem 1 for the Milstein MLMC estimator of a discretely monitored payoff of GBM** (Giles
2015, §5.2, p. 35: "`V_ℓ` is now `O(h_ℓ²)`, leading to `α = 1, β = 2, γ = 1` … Because `β > γ`,
the dominant computational cost is on the coarsest levels", with Theorem 1, §2.1, pp. 6–7 (cost
`c₄ ε⁻²` for `β > γ`), and (2.4), §2.1, p. 8; Table 5.2, p. 33).  In the setting of
`gbm_em_monitored_theorem1` with the Milstein scheme there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_j ≥ 1` with a square-integrable error, mean square error
`< ε²` for `E[Φ(S_{t_0}, …, S_{t_m})]`, `S = gbmMonExact … 0` (closed form in
`gbmMonExact_level_zero`), and cost `∑_{j≤L} N_j m 2^j ≤ c₄ ε⁻²`.  No rate is assumed: `α = 1`
(`gbm_mil_monitored_bias_le`), `β = 2` (`gbm_mil_monitored_variance_le`) and (2.4) are proved. -/
theorem gbm_mil_monitored_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {Φ : (ℕ → ℝ) → ℝ} {c : ℝ}
    (hΦ : ∀ a b : ℕ → ℝ, (Φ a - Φ b) ^ 2 ≤ c * ∑ k ∈ range (m + 1), (a k - b k) ^ 2) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ j, 0 < N j) ∧
        Integrable (fun x => (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => Φ (gbmMonMil r σ T s₀ m j z))
              (fun j z => Φ (gbmMonMil r σ T s₀ m j (pairAvg z)))) (fun p x => x p) j (N j) x -
            ∫ z, Φ (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => Φ (gbmMonMil r σ T s₀ m j z))
              (fun j z => Φ (gbmMonMil r σ T s₀ m j (pairAvg z)))) (fun p x => x p) j (N j) x -
            ∫ z, Φ (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hΦm := measurable_monPayoff hΦ
  have hc := monPayoff_const_nonneg hΦ
  have hC := gbmMilStrongConst_nonneg r σ s₀ hT
  have hcmC : 0 ≤ c * m * gbmMilStrongConst r σ T s₀ :=
    mul_nonneg (mul_nonneg hc (Nat.cast_nonneg m)) hC
  have hP : MemLp (fun z => Φ (gbmMonExact r σ T s₀ m 0 z)) 2 stdNormalSeq :=
    memLp_monPayoff hΦ (measurable_memLp_gbmMonExact r σ T s₀ m 0).1
      (measurable_memLp_gbmMonExact r σ T s₀ m 0).2
  have hPf : ∀ j, MemLp (fun z => Φ (gbmMonMil r σ T s₀ m j z)) 2 stdNormalSeq := fun j =>
    memLp_monPayoff hΦ (measurable_memLp_gbmMonMil r σ T s₀ m j).1
      (measurable_memLp_gbmMonMil r σ T s₀ m j).2
  have hPfm : ∀ j, Measurable (fun z => Φ (gbmMonMil r σ T s₀ m j z)) := fun j =>
    hΦm.comp (measurable_memLp_gbmMonMil r σ T s₀ m j).1
  have hPcm : ∀ j, Measurable (fun z => Φ (gbmMonMil r σ T s₀ m j (pairAvg z))) := fun j =>
    (hPfm j).comp measurePreserving_pairAvg.measurable
  have hPc : ∀ j, MemLp (fun z => Φ (gbmMonMil r σ T s₀ m j (pairAvg z))) 2 stdNormalSeq :=
    fun j => (hPf j).comp_measurePreserving measurePreserving_pairAvg
  -- (2.4): the coarse path has the law of the fine path of the level below
  have h24 : ∀ j, ∫ z, Φ (gbmMonMil r σ T s₀ m j z) ∂stdNormalSeq =
      ∫ z, Φ (gbmMonMil r σ T s₀ m j (pairAvg z)) ∂stdNormalSeq := fun j =>
    (integral_comp_of_measurePreserving measurePreserving_pairAvg
      (hPfm j).aestronglyMeasurable).symm
  -- (i): the weak rate `α = 1`
  have hc₁ : 0 < Real.sqrt (c * m * gbmMilStrongConst r σ T s₀) * T + 1 := by positivity
  have h_i : ∀ j : ℕ, |∫ z, Φ (gbmMonMil r σ T s₀ m j z) - Φ (gbmMonExact r σ T s₀ m 0 z)
      ∂stdNormalSeq| ≤
      (Real.sqrt (c * m * gbmMilStrongConst r σ T s₀) * T + 1) * (2 : ℝ) ^ (-(1 * (j : ℝ))) := by
    intro j
    rw [one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    have h := gbm_mil_monitored_bias_le r σ s₀ hT hΦ j
    have hinv : 0 < ((2 : ℝ) ^ j)⁻¹ := by positivity
    have hle := mul_le_mul_of_nonneg_left (monStep_le hT hm j)
      (Real.sqrt_nonneg (c * m * gbmMilStrongConst r σ T s₀))
    calc _ ≤ _ := h
      _ ≤ _ := hle
      _ ≤ _ := by nlinarith
  -- (iii): the variance rate `β = 2`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (fineCoarseDiff
      (fun j z => Φ (gbmMonMil r σ T s₀ m j z))
      (fun j z => Φ (gbmMonMil r σ T s₀ m j (pairAvg z))) 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by
    rw [hV₀]
    exact variance_nonneg _ _
  have hc₂ : 0 < V₀ + 10 * (c * m * gbmMilStrongConst r σ T s₀ * T ^ 2) + 1 := by
    nlinarith [mul_nonneg hcmC (sq_nonneg T)]
  have h_iii : ∀ j, variance (fineCoarseDiff (fun j z => Φ (gbmMonMil r σ T s₀ m j z))
      (fun j z => Φ (gbmMonMil r σ T s₀ m j (pairAvg z))) j) stdNormalSeq ≤
      (V₀ + 10 * (c * m * gbmMilStrongConst r σ T s₀ * T ^ 2) + 1) *
        (2 : ℝ) ^ (-(2 * (j : ℝ))) := by
    intro j
    rw [two_rpow_neg_two_mul j]
    cases j with
    | zero =>
      rw [← hV₀, pow_zero, inv_one, mul_one]
      nlinarith [mul_nonneg hcmC (sq_nonneg T)]
    | succ j =>
      have hv := gbm_mil_monitored_variance_le r σ s₀ hT hΦ j
      have hle : 10 * c * m * gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ (j + 1))) ^ 2 ≤
          10 * (c * m * gbmMilStrongConst r σ T s₀ * T ^ 2) * ((4 : ℝ) ^ (j + 1))⁻¹ := by
        have h10 : 0 ≤ 10 * c * m * gbmMilStrongConst r σ T s₀ := by linarith
        exact (mul_le_mul_of_nonneg_left (monStep_sq_le hT hm (j + 1)) h10).trans_eq (by ring)
      have hinv : 0 < ((4 : ℝ) ^ (j + 1))⁻¹ := by positivity
      exact hv.trans (hle.trans (by nlinarith [mul_nonneg hV₀0 hinv.le]))
  -- (iv): a level-`j` sample costs `m 2^j`
  have h_iv : ∀ j : ℕ, (m : ℝ) * 2 ^ j ≤ m * (2 : ℝ) ^ ((1 : ℝ) * (j : ℝ)) := fun j => by
    rw [one_mul, Real.rpow_natCast]
  have hαβγ : min (2 : ℝ) 1 / 2 ≤ 1 := by
    rw [min_eq_right (by norm_num : (1 : ℝ) ≤ 2)]
    norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq)
    (fun z => Φ (gbmMonExact r σ T s₀ m 0 z)) (fun j z => Φ (gbmMonMil r σ T s₀ m j z))
    (fun j z => Φ (gbmMonMil r σ T s₀ m j (pairAvg z))) (fun p x => x p)
    (fun j _ _ => (m : ℝ) * 2 ^ j) (fun j => (m : ℝ) * 2 ^ j) (α := 1) (β := 2) (γ := 1)
    one_pos two_pos one_pos hc₁ hc₂ (Nat.cast_pos.2 hm) hαβγ hω hind
    (hP.integrable one_le_two) hPfm hPcm hPf hPc h24 (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, ((memLp_finsetSum _ fun j _ =>
    memLp_blockMean hω (memLp_fineCoarseDiff hPf hPc) j (N j)).sub (memLp_const _)).integrable_sq,
    hmse, ?_⟩
  simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul] at hcost
  rw [complexityBound_of_lt (by norm_num : (1 : ℝ) < 2) ε] at hcost
  exact hcost

/-! ### The Asian and lookback payoffs are Lipschitz in the monitored values -/

/-- `(g(x) − g(y))² ≤ K²(x − y)²` for a `K`-Lipschitz `g`. -/
lemma sq_sub_le_of_lipschitz_mon {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|)
    (x y : ℝ) : (g x - g y) ^ 2 ≤ K ^ 2 * (x - y) ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (hg x y) 2
  rwa [sq_abs, mul_pow, sq_abs] at h

/-- **The discretely monitored Asian payoff is Lipschitz in the monitored values** (Giles 2015,
§5.1, p. 29: "Lipschitz payoff functions `P` (such as European, Asian and lookback options …) for
which `|P(S₁) − P(S₂)| ≤ K ‖S₁ − S₂‖`").  For a `K`-Lipschitz `g` and `m ≥ 1`,
`(g(ā) − g(b̄))² ≤ (K²/m) ∑_{k=0}^m (a_k − b_k)²` with `ā = (1/m) ∑_{k=1}^m a_k` (Jensen's, or the
Cauchy–Schwarz, inequality). -/
theorem asianPayoff_sq_sub_le {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|)
    {m : ℕ} (hm : 0 < m) (a b : ℕ → ℝ) :
    (asianPayoff g m a - asianPayoff g m b) ^ 2 ≤
      K ^ 2 / m * ∑ k ∈ range (m + 1), (a k - b k) ^ 2 := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have h3 : ((∑ k ∈ range m, a (k + 1)) / m - (∑ k ∈ range m, b (k + 1)) / m) ^ 2 ≤
      (∑ k ∈ range m, (a (k + 1) - b (k + 1)) ^ 2) / m := by
    rw [← sub_div, ← Finset.sum_sub_distrib, div_pow, div_le_div_iff₀ (by positivity) hm0]
    have h := Finset.sum_mul_sq_le_sq_mul_sq (range m) (fun _ => (1 : ℝ))
      (fun k => a (k + 1) - b (k + 1))
    simp only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h
    nlinarith [mul_le_mul_of_nonneg_right h hm0.le]
  have h4 : ∑ k ∈ range m, (a (k + 1) - b (k + 1)) ^ 2 ≤
      ∑ k ∈ range (m + 1), (a k - b k) ^ 2 := by
    rw [Finset.sum_range_succ' (fun k => (a k - b k) ^ 2)]
    linarith [sq_nonneg (a 0 - b 0)]
  unfold asianPayoff
  calc _ ≤ K ^ 2 * ((∑ k ∈ range m, a (k + 1)) / m - (∑ k ∈ range m, b (k + 1)) / m) ^ 2 :=
        sq_sub_le_of_lipschitz_mon hg _ _
    _ ≤ K ^ 2 * ((∑ k ∈ range m, (a (k + 1) - b (k + 1)) ^ 2) / m) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg K)
    _ ≤ K ^ 2 * ((∑ k ∈ range (m + 1), (a k - b k) ^ 2) / m) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h4 hm0.le) (sq_nonneg K)
    _ = _ := by ring

/-- `(max_{k∈s} a_k − max_{k∈s} b_k)² ≤ ∑_{k∈s} (a_k − b_k)²`. -/
lemma sq_monMax_sub_le {s : Finset ℕ} (hs : s.Nonempty) (a b : ℕ → ℝ) :
    (s.sup' hs a - s.sup' hs b) ^ 2 ≤ ∑ k ∈ s, (a k - b k) ^ 2 := by
  obtain ⟨i, hi, hai⟩ := Finset.exists_mem_eq_sup' hs a
  obtain ⟨l, hl, hbl⟩ := Finset.exists_mem_eq_sup' hs b
  have hbi : b i ≤ s.sup' hs b := Finset.le_sup' b hi
  have hal : a l ≤ s.sup' hs a := Finset.le_sup' a hl
  have hsi : (a i - b i) ^ 2 ≤ ∑ k ∈ s, (a k - b k) ^ 2 :=
    Finset.single_le_sum (f := fun k => (a k - b k) ^ 2) (fun k _ => sq_nonneg _) hi
  have hsl : (a l - b l) ^ 2 ≤ ∑ k ∈ s, (a k - b k) ^ 2 :=
    Finset.single_le_sum (f := fun k => (a k - b k) ^ 2) (fun k _ => sq_nonneg _) hl
  rcases le_total (s.sup' hs b) (s.sup' hs a) with h | h
  · have h1 : (s.sup' hs a - s.sup' hs b) ^ 2 ≤ (a i - b i) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    linarith
  · have h1 : (s.sup' hs a - s.sup' hs b) ^ 2 ≤ (b l - a l) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    nlinarith

/-- `(min_{k∈s} a_k − min_{k∈s} b_k)² ≤ ∑_{k∈s} (a_k − b_k)²`. -/
lemma sq_monMin_sub_le {s : Finset ℕ} (hs : s.Nonempty) (a b : ℕ → ℝ) :
    (s.inf' hs a - s.inf' hs b) ^ 2 ≤ ∑ k ∈ s, (a k - b k) ^ 2 := by
  obtain ⟨i, hi, hai⟩ := Finset.exists_mem_eq_inf' hs a
  obtain ⟨l, hl, hbl⟩ := Finset.exists_mem_eq_inf' hs b
  have hbi : s.inf' hs b ≤ b i := Finset.inf'_le b hi
  have hal : s.inf' hs a ≤ a l := Finset.inf'_le a hl
  have hsi : (a i - b i) ^ 2 ≤ ∑ k ∈ s, (a k - b k) ^ 2 :=
    Finset.single_le_sum (f := fun k => (a k - b k) ^ 2) (fun k _ => sq_nonneg _) hi
  have hsl : (a l - b l) ^ 2 ≤ ∑ k ∈ s, (a k - b k) ^ 2 :=
    Finset.single_le_sum (f := fun k => (a k - b k) ^ 2) (fun k _ => sq_nonneg _) hl
  rcases le_total (s.inf' hs b) (s.inf' hs a) with h | h
  · have h1 : (s.inf' hs a - s.inf' hs b) ^ 2 ≤ (a l - b l) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    linarith
  · have h1 : (s.inf' hs a - s.inf' hs b) ^ 2 ≤ (b i - a i) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    nlinarith

/-- **The discretely monitored lookback payoff is Lipschitz in the monitored values** (Giles 2015,
§5.1, p. 29: "Lipschitz payoff functions `P` (such as … lookback options …)").  For a
`K`-Lipschitz `g`, `(g(max_k a_k) − g(max_k b_k))² ≤ K² ∑_{k=0}^m (a_k − b_k)²`, since
`|max a − max b| ≤ max_k |a_k − b_k|`. -/
theorem lookbackPayoff_sq_sub_le {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|)
    (m : ℕ) (a b : ℕ → ℝ) :
    (lookbackPayoff g m a - lookbackPayoff g m b) ^ 2 ≤
      K ^ 2 * ∑ k ∈ range (m + 1), (a k - b k) ^ 2 :=
  (sq_sub_le_of_lipschitz_mon hg _ _).trans (mul_le_mul_of_nonneg_left
    (sq_monMax_sub_le nonempty_range_add_one a b) (sq_nonneg K))

/-- **The discretely monitored floating-strike lookback payoff is Lipschitz in the monitored
values** (Giles 2015, §5.1, p. 29 and p. 33, the lookback option "based on its … minimum value").
For a `K`-Lipschitz `g`,
`(g(a_m − min_k a_k) − g(b_m − min_k b_k))² ≤ 4K² ∑_{k=0}^m (a_k − b_k)²`, so all results for
monitored Lipschitz payoffs (`gbm_em_monitored_theorem1`, `gbm_mil_monitored_theorem1`, …) apply
with `c = 4K²` (named versions: `gbm_em_floatLookback_variance_le`,
`gbm_em_floatLookback_theorem1`, `gbm_mil_floatLookback_variance_le`,
`gbm_mil_floatLookback_theorem1`). -/
theorem floatLookbackPayoff_sq_sub_le {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (m : ℕ) (a b : ℕ → ℝ) :
    (floatLookbackPayoff g m a - floatLookbackPayoff g m b) ^ 2 ≤
      4 * K ^ 2 * ∑ k ∈ range (m + 1), (a k - b k) ^ 2 := by
  have h1 := sq_monMin_sub_le (nonempty_range_add_one (n := m)) a b
  have h2 : (a m - b m) ^ 2 ≤ ∑ k ∈ range (m + 1), (a k - b k) ^ 2 :=
    Finset.single_le_sum (f := fun k => (a k - b k) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.self_mem_range_succ m)
  unfold floatLookbackPayoff
  refine (sq_sub_le_of_lipschitz_mon hg _ _).trans ?_
  rw [mul_assoc 4, mul_left_comm 4]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
  nlinarith [sq_nonneg (a m - b m + ((range (m + 1)).inf' nonempty_range_add_one a -
    (range (m + 1)).inf' nonempty_range_add_one b))]

/-! ### The Asian option (Table 5.2, row "Asian") -/

/-- **Mean square error of the discretely monitored Asian option, Euler–Maruyama** (Giles 2015,
§5.1, p. 29: "For Lipschitz payoff functions `P` (such as European, Asian and lookback options …)
… `E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`", with "`E[‖S − Ŝ‖²] = O(h)`"; this is the step towards the
correction variance of Table 5.2, see `gbm_em_asian_variance_le`).  For GBM, `m ≥ 1`
monitoring dates `t_k = kT/m` and a `K`-Lipschitz `g`, the payoff `P = g((1/m) ∑_{k=1}^m S_{t_k})`
and its level-`j` Euler–Maruyama approximation satisfy `E[(P − P̂_j)²] ≤ K² C(T) h_j`,
`h_j = T/(m 2^j)`, `C = gbmStrongConst`.  Discrete monitoring only (the paper's Asian option
averages over `[0, T]` continuously). -/
theorem gbm_em_asian_mse_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    ∫ z, (asianPayoff g m (gbmMonExact r σ T s₀ m j z) -
        asianPayoff g m (gbmMonEM r σ T s₀ m j z)) ^ 2 ∂stdNormalSeq ≤
      K ^ 2 * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ j)) := by
  refine (gbm_em_monitored_mse_le r σ s₀ hT (asianPayoff_sq_sub_le hg hm) j).trans_eq ?_
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hm.ne')]

/-- **Weak error of the discretely monitored Asian option, Euler–Maruyama** (Giles 2015, §5.1,
p. 29; Theorem 1 (i), §2.1, p. 6, with `α = ½`): `|E[P̂_j] − E[P]| ≤ K √(C(T) h_j)` in the setting
of `gbm_em_asian_mse_le`.  The paper's weak order `α = 1` (§5.1, p. 30) is not proved; `α = ½`
suffices for Theorem 1. -/
theorem gbm_em_asian_bias_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    |∫ z, asianPayoff g m (gbmMonEM r σ T s₀ m j z) -
        asianPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq| ≤
      K * Real.sqrt (gbmStrongConst r σ T s₀ * (T / (m * 2 ^ j))) := by
  obtain ⟨hK, -⟩ := continuous_of_abs_sub_le hg
  refine (gbm_em_monitored_bias_le r σ s₀ hT (asianPayoff_sq_sub_le hg hm) j).trans_eq ?_
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hm.ne'), mul_assoc, Real.sqrt_mul (sq_nonneg K),
    Real.sqrt_sq hK]

/-- **Correction variance of the discretely monitored Asian option, Euler–Maruyama** (Giles 2015,
Table 5.2, p. 33, row "Asian", Euler–Maruyama: "`O(h)`"; §5.1, p. 29).  In the setting of
`gbm_em_asian_mse_le`,
`V[P̂^f_{j+1} − P̂^c_j] ≤ 6 K² C(T) h_{j+1}`. -/
theorem gbm_em_asian_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    variance (fun z => asianPayoff g m (gbmMonEM r σ T s₀ m (j + 1) z) -
        asianPayoff g m (gbmMonEM r σ T s₀ m j (pairAvg z))) stdNormalSeq ≤
      6 * K ^ 2 * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ (j + 1))) := by
  refine (gbm_em_monitored_variance_le r σ s₀ hT (asianPayoff_sq_sub_le hg hm) j).trans_eq ?_
  rw [mul_assoc 6 (K ^ 2 / m), div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hm.ne')]

/-- **Theorem 1 for the Euler–Maruyama MLMC estimator of the discretely monitored Asian option**
(Giles 2015, §5.1, p. 30, and Table 5.2, p. 33, row "Asian", with Theorem 1, §2.1, pp. 6–7:
`β = γ = 1`, complexity `O(ε⁻²(log ε)²)`).  For GBM, `m ≥ 1` monitoring dates and
`P = g((1/m) ∑_{k=1}^m S_{t_k})` with a `K`-Lipschitz `g`, there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_j ≥ 1` with a square-integrable error, mean square error
`< ε²`, and cost `∑_{j≤L} N_j m 2^j ≤ c₄ ε⁻²(log ε)²` (levels, coupling and the target `E[P(S)]`,
`S_{t_k} = s₀ exp((r − σ²/2) kT/m + σ √(T/m) ∑_{i<k} Z_i)`, as in `gbm_em_monitored_theorem1`;
`α = ½` is proved, the paper's `α = 1` is not needed). -/
theorem gbm_em_asian_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ j, 0 < N j) ∧
        Integrable (fun x => (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => asianPayoff g m (gbmMonEM r σ T s₀ m j z))
              (fun j z => asianPayoff g m (gbmMonEM r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, asianPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => asianPayoff g m (gbmMonEM r σ T s₀ m j z))
              (fun j z => asianPayoff g m (gbmMonEM r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, asianPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) ≤
          c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) :=
  gbm_em_monitored_theorem1 r σ s₀ hT hm (asianPayoff_sq_sub_le hg hm)

/-- **Mean square error of the discretely monitored Asian option, Milstein** (Giles 2015, §5.1,
p. 29: "`E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`", with the Milstein "first order strong convergence",
§5.2, p. 35; this is the step towards the correction variance of Table 5.2, see
`gbm_mil_asian_variance_le`).  In the setting of `gbm_em_asian_mse_le` with the Milstein scheme,
`E[(P − P̂_j)²] ≤ K² C_M(T) h_j²`, `C_M = gbmMilStrongConst`. -/
theorem gbm_mil_asian_mse_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    ∫ z, (asianPayoff g m (gbmMonExact r σ T s₀ m j z) -
        asianPayoff g m (gbmMonMil r σ T s₀ m j z)) ^ 2 ∂stdNormalSeq ≤
      K ^ 2 * gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ j)) ^ 2 := by
  refine (gbm_mil_monitored_mse_le r σ s₀ hT (asianPayoff_sq_sub_le hg hm) j).trans_eq ?_
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hm.ne')]

/-- **Weak error of the discretely monitored Asian option, Milstein** (Giles 2015, §5.2, p. 35;
Theorem 1 (i), §2.1, p. 6, with `α = 1`): `|E[P̂_j] − E[P]| ≤ K √(C_M(T)) h_j` in the setting of
`gbm_mil_asian_mse_le`. -/
theorem gbm_mil_asian_bias_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    |∫ z, asianPayoff g m (gbmMonMil r σ T s₀ m j z) -
        asianPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq| ≤
      K * Real.sqrt (gbmMilStrongConst r σ T s₀) * (T / (m * 2 ^ j)) := by
  obtain ⟨hK, -⟩ := continuous_of_abs_sub_le hg
  refine (gbm_mil_monitored_bias_le r σ s₀ hT (asianPayoff_sq_sub_le hg hm) j).trans_eq ?_
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hm.ne'), Real.sqrt_mul (sq_nonneg K),
    Real.sqrt_sq hK]

/-- **Correction variance of the discretely monitored Asian option, Milstein** (Giles 2015,
Table 5.2, p. 33, row "Asian", Milstein: "`O(h²)`"; §5.2, p. 35).  In the setting of
`gbm_mil_asian_mse_le`,
`V[P̂^f_{j+1} − P̂^c_j] ≤ 10 K² C_M(T) h_{j+1}²`. -/
theorem gbm_mil_asian_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    variance (fun z => asianPayoff g m (gbmMonMil r σ T s₀ m (j + 1) z) -
        asianPayoff g m (gbmMonMil r σ T s₀ m j (pairAvg z))) stdNormalSeq ≤
      10 * K ^ 2 * gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ (j + 1))) ^ 2 := by
  refine (gbm_mil_monitored_variance_le r σ s₀ hT (asianPayoff_sq_sub_le hg hm) j).trans_eq ?_
  rw [mul_assoc 10 (K ^ 2 / m), div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hm.ne')]

/-- **Theorem 1 for the Milstein MLMC estimator of the discretely monitored Asian option** (Giles
2015, §5.2, p. 35, and Table 5.2, p. 33, row "Asian", with Theorem 1, §2.1, pp. 6–7:
`β = 2 > γ = 1`, complexity `O(ε⁻²)`).  In the setting of `gbm_em_asian_theorem1` (same target
`E[P(S)]`, `S = gbmMonExact … 0`) with the Milstein scheme, the error is again square integrable
with mean square `< ε²`, and the cost is `∑_{j≤L} N_j m 2^j ≤ c₄ ε⁻²`. -/
theorem gbm_mil_asian_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ j, 0 < N j) ∧
        Integrable (fun x => (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => asianPayoff g m (gbmMonMil r σ T s₀ m j z))
              (fun j z => asianPayoff g m (gbmMonMil r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, asianPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => asianPayoff g m (gbmMonMil r σ T s₀ m j z))
              (fun j z => asianPayoff g m (gbmMonMil r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, asianPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) ≤ c₄ * ε ^ (-2 : ℝ) :=
  gbm_mil_monitored_theorem1 r σ s₀ hT hm (asianPayoff_sq_sub_le hg hm)

/-! ### The lookback option (Table 5.2, row "lookback") -/

/-- **Mean square error of the discretely monitored lookback option, Euler–Maruyama** (Giles 2015,
§5.1, p. 29: "For Lipschitz payoff functions `P` (such as European, Asian and lookback options …)
… `E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`", with "`E[‖S − Ŝ‖²] = O(h)`"; this is the step towards the
correction variance of Table 5.2, see `gbm_em_lookback_variance_le`).  For GBM, monitoring
dates `t_k = kT/m` and a `K`-Lipschitz `g`, the payoff `P = g(max_{0≤k≤m} S_{t_k})` and its
level-`j` Euler–Maruyama approximation satisfy `E[(P − P̂_j)²] ≤ K² m C(T) h_j`,
`h_j = T/(m 2^j)`.  The factor `m` (from `max_k (a_k − b_k)² ≤ ∑_k (a_k − b_k)²`) is not sharp; it
does not affect the rate in `j`, as the bound equals `K² C(T) T 2^{−j}`.  Discrete monitoring only
(the paper's lookback uses the maximum over `[0, T]`).  For `m = 0` the statement is degenerate
and trivially true (the only date is `t_0`, where both paths equal `s₀`). -/
theorem gbm_em_lookback_mse_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    ∫ z, (lookbackPayoff g m (gbmMonExact r σ T s₀ m j z) -
        lookbackPayoff g m (gbmMonEM r σ T s₀ m j z)) ^ 2 ∂stdNormalSeq ≤
      K ^ 2 * m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ j)) :=
  gbm_em_monitored_mse_le r σ s₀ hT (lookbackPayoff_sq_sub_le hg m) j

/-- **Weak error of the discretely monitored lookback option, Euler–Maruyama** (Giles 2015, §5.1,
p. 29; Theorem 1 (i), §2.1, p. 6, with `α = ½`): `|E[P̂_j] − E[P]| ≤ K √(m C(T) h_j)` in the
setting of `gbm_em_lookback_mse_le`.  The factor `m` is not sharp; the bound equals
`K √(C(T) T 2^{−j})`.  The paper's weak order `α = 1` (§5.1, p. 30) is not proved; `α = ½`
suffices for Theorem 1.  For `m = 0` the statement is degenerate and trivially true. -/
theorem gbm_em_lookback_bias_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    |∫ z, lookbackPayoff g m (gbmMonEM r σ T s₀ m j z) -
        lookbackPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq| ≤
      K * Real.sqrt (m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ j))) := by
  obtain ⟨hK, -⟩ := continuous_of_abs_sub_le hg
  refine (gbm_em_monitored_bias_le r σ s₀ hT (lookbackPayoff_sq_sub_le hg m) j).trans_eq ?_
  rw [show K ^ 2 * m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ j)) =
      K ^ 2 * (m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ j))) by ring,
    Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]

/-- **Correction variance of the discretely monitored lookback option, Euler–Maruyama** (Giles
2015, Table 5.2, p. 33, row "lookback", Euler–Maruyama: "`O(h)`"; §5.1, p. 29).  In the setting of
`gbm_em_lookback_mse_le`, `V[P̂^f_{j+1} − P̂^c_j] ≤ 6 K² m C(T) h_{j+1}`.  The factor `m` is not
sharp; the bound equals `6 K² C(T) T 2^{−(j+1)}`.  For `m = 0` the statement is degenerate and
trivially true. -/
theorem gbm_em_lookback_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    variance (fun z => lookbackPayoff g m (gbmMonEM r σ T s₀ m (j + 1) z) -
        lookbackPayoff g m (gbmMonEM r σ T s₀ m j (pairAvg z))) stdNormalSeq ≤
      6 * K ^ 2 * m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ (j + 1))) :=
  gbm_em_monitored_variance_le r σ s₀ hT (lookbackPayoff_sq_sub_le hg m) j

/-- **Theorem 1 for the Euler–Maruyama MLMC estimator of the discretely monitored lookback option**
(Giles 2015, §5.1, p. 30, and Table 5.2, p. 33, row "lookback", with Theorem 1, §2.1, pp. 6–7:
`β = γ = 1`, complexity `O(ε⁻²(log ε)²)`).  For GBM, `m ≥ 1` monitoring dates and
`P = g(max_{0≤k≤m} S_{t_k})` with a `K`-Lipschitz `g`, there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_j ≥ 1` with a square-integrable error, mean square error
`< ε²`, and cost `∑_{j≤L} N_j m 2^j ≤ c₄ ε⁻²(log ε)²` (levels, coupling and the target `E[P(S)]`,
`S_{t_k} = s₀ exp((r − σ²/2) kT/m + σ √(T/m) ∑_{i<k} Z_i)`, as in `gbm_em_monitored_theorem1`;
`α = ½` is proved, the paper's `α = 1` is not needed). -/
theorem gbm_em_lookback_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ j, 0 < N j) ∧
        Integrable (fun x => (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => lookbackPayoff g m (gbmMonEM r σ T s₀ m j z))
              (fun j z => lookbackPayoff g m (gbmMonEM r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, lookbackPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => lookbackPayoff g m (gbmMonEM r σ T s₀ m j z))
              (fun j z => lookbackPayoff g m (gbmMonEM r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, lookbackPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) ≤
          c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) :=
  gbm_em_monitored_theorem1 r σ s₀ hT hm (lookbackPayoff_sq_sub_le hg m)

/-- **Mean square error of the discretely monitored lookback option, Milstein** (Giles 2015, §5.1,
p. 29: "`E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`", with the Milstein "first order strong convergence",
§5.2, p. 35; this is the step towards the correction variance, see `gbm_mil_lookback_variance_le`
for Table 5.2 and the p. 38 remark).  In the setting of `gbm_em_lookback_mse_le` with the Milstein
scheme, `E[(P − P̂_j)²] ≤ K² m C_M(T) h_j²`.  The factor `m` is not sharp; the bound equals
`K² C_M(T) T² 4^{−j}/m`.  For `m = 0` the statement is degenerate and trivially true. -/
theorem gbm_mil_lookback_mse_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    ∫ z, (lookbackPayoff g m (gbmMonExact r σ T s₀ m j z) -
        lookbackPayoff g m (gbmMonMil r σ T s₀ m j z)) ^ 2 ∂stdNormalSeq ≤
      K ^ 2 * m * gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ j)) ^ 2 :=
  gbm_mil_monitored_mse_le r σ s₀ hT (lookbackPayoff_sq_sub_le hg m) j

/-- **Weak error of the discretely monitored lookback option, Milstein** (Giles 2015, §5.2, p. 35;
Theorem 1 (i), §2.1, p. 6, with `α = 1`): `|E[P̂_j] − E[P]| ≤ K √(m C_M(T)) h_j` in the setting of
`gbm_mil_lookback_mse_le`.  The factor `m` is not sharp; the bound equals
`K √(C_M(T)) T 2^{−j}/√m`.  For `m = 0` the statement is degenerate and trivially true. -/
theorem gbm_mil_lookback_bias_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    |∫ z, lookbackPayoff g m (gbmMonMil r σ T s₀ m j z) -
        lookbackPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq| ≤
      K * Real.sqrt (m * gbmMilStrongConst r σ T s₀) * (T / (m * 2 ^ j)) := by
  obtain ⟨hK, -⟩ := continuous_of_abs_sub_le hg
  refine (gbm_mil_monitored_bias_le r σ s₀ hT (lookbackPayoff_sq_sub_le hg m) j).trans_eq ?_
  rw [mul_assoc (K ^ 2), Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]

/-- **Correction variance of the discretely monitored lookback option, Milstein** (Giles 2015,
Table 5.2, p. 33, row "lookback", Milstein: numerics "`O(h²)`", analysis "`o(h^{2−δ})`" for
continuous monitoring (Giles et al. 2013, §5.2, p. 39); §5.2, p. 35).  For the discretely
monitored lookback the rate is `O(h²)`: in the setting of `gbm_mil_lookback_mse_le`,
`V[P̂^f_{j+1} − P̂^c_j] ≤ 10 K² m C_M(T) h_{j+1}²` (the factor `m` is not sharp; the bound equals
`10 K² C_M(T) T² 4^{−(j+1)}/m`).  This does not contradict §5.2, p. 38 ("A multilevel estimator
based directly on the minimum (or maximum) of the values at the discrete timesteps will have a
poor variance … This results in an `O(h_ℓ)` variance for lookback options"): there the maximum
runs over all time steps of each level, which differ between the fine and the coarse path and
approximate continuous monitoring; here the monitoring dates are fixed and lie on every grid, so
the coarse and the fine payoffs compare the paths at the same dates, and first-order strong
convergence gives `O(h²)`.  For `m = 0` the statement is degenerate and trivially true. -/
theorem gbm_mil_lookback_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    variance (fun z => lookbackPayoff g m (gbmMonMil r σ T s₀ m (j + 1) z) -
        lookbackPayoff g m (gbmMonMil r σ T s₀ m j (pairAvg z))) stdNormalSeq ≤
      10 * K ^ 2 * m * gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ (j + 1))) ^ 2 :=
  gbm_mil_monitored_variance_le r σ s₀ hT (lookbackPayoff_sq_sub_le hg m) j

/-- **Theorem 1 for the Milstein MLMC estimator of the discretely monitored lookback option**
(Giles 2015, §5.2, p. 35: "Because `β > γ`, the dominant computational cost is on the coarsest
levels", Table 5.2, p. 33, row "lookback", and Theorem 1, §2.1, pp. 6–7: cost `O(ε⁻²)` for
`β > γ`).  In the setting of `gbm_em_lookback_theorem1` (same target `E[P(S)]`,
`S = gbmMonExact … 0`) with the Milstein scheme, the error is again square integrable with mean
square `< ε²`, and the cost is `∑_{j≤L} N_j m 2^j ≤ c₄ ε⁻²`.  Here
`β = 2` comes directly from the Milstein strong error at the fixed dates
(`gbm_mil_lookback_variance_le`).  The paper's §5.2, p. 39 statement "the outcome is that `β = 2`
for lookback options … the overall complexity is `O(ε⁻²)`" concerns a different estimator: the
Brownian-bridge estimator of Giles (2008a) for the continuously monitored lookback, which is not
formalised here. -/
theorem gbm_mil_lookback_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ j, 0 < N j) ∧
        Integrable (fun x => (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => lookbackPayoff g m (gbmMonMil r σ T s₀ m j z))
              (fun j z => lookbackPayoff g m (gbmMonMil r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, lookbackPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => lookbackPayoff g m (gbmMonMil r σ T s₀ m j z))
              (fun j z => lookbackPayoff g m (gbmMonMil r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, lookbackPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) ≤ c₄ * ε ^ (-2 : ℝ) :=
  gbm_mil_monitored_theorem1 r σ s₀ hT hm (lookbackPayoff_sq_sub_le hg m)

/-! ### The floating-strike lookback option (Table 5.2, row "lookback", minimum) -/

/-- **Correction variance of the discretely monitored floating-strike lookback option,
Euler–Maruyama** (Giles 2015, Table 5.2, p. 33, row "lookback", Euler–Maruyama: "`O(h)`"; p. 33:
the lookback "is based on its maximum or minimum value"; §5.1, p. 29).  For GBM, monitoring dates
`t_k = kT/m`, a `K`-Lipschitz `g` and `P = g(S_{t_m} − min_{0≤k≤m} S_{t_k})`, the correction on
level `j + 1` satisfies `V[P̂^f_{j+1} − P̂^c_j] ≤ 24 K² m C(T) h_{j+1}` (`c = 4K²` in
`gbm_em_monitored_variance_le`; the factor `m` is not sharp).  Discrete monitoring only.  For
`m = 0` the statement is degenerate and trivially true. -/
theorem gbm_em_floatLookback_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    variance (fun z => floatLookbackPayoff g m (gbmMonEM r σ T s₀ m (j + 1) z) -
        floatLookbackPayoff g m (gbmMonEM r σ T s₀ m j (pairAvg z))) stdNormalSeq ≤
      24 * K ^ 2 * m * gbmStrongConst r σ T s₀ * (T / (m * 2 ^ (j + 1))) :=
  (gbm_em_monitored_variance_le r σ s₀ hT (floatLookbackPayoff_sq_sub_le hg m) j).trans_eq
    (by ring)

/-- **Theorem 1 for the Euler–Maruyama MLMC estimator of the discretely monitored floating-strike
lookback option** (Giles 2015, §5.1, p. 30, and Table 5.2, p. 33, row "lookback", with Theorem 1,
§2.1, pp. 6–7: `β = γ = 1`, complexity `O(ε⁻²(log ε)²)`).  For GBM, `m ≥ 1` monitoring dates and
`P = g(S_{t_m} − min_{0≤k≤m} S_{t_k})` with a `K`-Lipschitz `g`, there is `c₄ > 0` such that for
every `0 < ε < e⁻¹` there are `L` and `N_j ≥ 1` with a square-integrable error, mean square
error `< ε²`, and cost `∑_{j≤L} N_j m 2^j ≤ c₄ ε⁻²(log ε)²` (levels, coupling and the target
`E[P(S)]`, `S = gbmMonExact … 0`, as in `gbm_em_monitored_theorem1`). -/
theorem gbm_em_floatLookback_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ j, 0 < N j) ∧
        Integrable (fun x => (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun j z => floatLookbackPayoff g m (gbmMonEM r σ T s₀ m j z))
              (fun j z => floatLookbackPayoff g m (gbmMonEM r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, floatLookbackPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun j z => floatLookbackPayoff g m (gbmMonEM r σ T s₀ m j z))
              (fun j z => floatLookbackPayoff g m (gbmMonEM r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, floatLookbackPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) ≤
          c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) :=
  gbm_em_monitored_theorem1 r σ s₀ hT hm (floatLookbackPayoff_sq_sub_le hg m)

/-- **Correction variance of the discretely monitored floating-strike lookback option, Milstein**
(Giles 2015, Table 5.2, p. 33, row "lookback", Milstein: numerics "`O(h²)`"; §5.2, p. 35).  In the
setting of `gbm_em_floatLookback_variance_le` with the Milstein scheme,
`V[P̂^f_{j+1} − P̂^c_j] ≤ 40 K² m C_M(T) h_{j+1}²` (`c = 4K²` in `gbm_mil_monitored_variance_le`;
the factor `m` is not sharp).  As for `gbm_mil_lookback_variance_le`, the dates are fixed and lie
on every grid, so the `O(h_ℓ)` variance of §5.2, p. 38 (minimum over all time steps of a level)
does not apply, and the analysis rate `o(h^{2−δ})` of Table 5.2 (continuous monitoring) is not
proved.  For `m = 0` the statement is degenerate and trivially true. -/
theorem gbm_mil_floatLookback_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ}
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (j : ℕ) :
    variance (fun z => floatLookbackPayoff g m (gbmMonMil r σ T s₀ m (j + 1) z) -
        floatLookbackPayoff g m (gbmMonMil r σ T s₀ m j (pairAvg z))) stdNormalSeq ≤
      40 * K ^ 2 * m * gbmMilStrongConst r σ T s₀ * (T / (m * 2 ^ (j + 1))) ^ 2 :=
  (gbm_mil_monitored_variance_le r σ s₀ hT (floatLookbackPayoff_sq_sub_le hg m) j).trans_eq
    (by ring)

/-- **Theorem 1 for the Milstein MLMC estimator of the discretely monitored floating-strike
lookback option** (Giles 2015, §5.2, p. 35: "Because `β > γ`, the dominant computational cost is
on the coarsest levels", Table 5.2, p. 33, row "lookback", and Theorem 1, §2.1, pp. 6–7: cost
`O(ε⁻²)` for `β > γ`).  In the setting of `gbm_em_floatLookback_theorem1` with the Milstein scheme,
the error is again square integrable with mean square `< ε²`, and the cost is
`∑_{j≤L} N_j m 2^j ≤ c₄ ε⁻²`; `β = 2` comes from the Milstein strong error at the fixed
dates (`gbm_mil_floatLookback_variance_le`), not from the Brownian-bridge estimator of §5.2,
pp. 38–39. -/
theorem gbm_mil_floatLookback_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ j, 0 < N j) ∧
        Integrable (fun x => (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun j z => floatLookbackPayoff g m (gbmMonMil r σ T s₀ m j z))
              (fun j z => floatLookbackPayoff g m (gbmMonMil r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, floatLookbackPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun j z => floatLookbackPayoff g m (gbmMonMil r σ T s₀ m j z))
              (fun j z => floatLookbackPayoff g m (gbmMonMil r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, floatLookbackPayoff g m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) ≤ c₄ * ε ^ (-2 : ℝ) :=
  gbm_mil_monitored_theorem1 r σ s₀ hT hm (floatLookbackPayoff_sq_sub_le hg m)

end MLMC
