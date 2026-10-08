import MlmcLean.TauLeapingExtensions

/-!
# Tau-leaping MLMC with unbounded Lipschitz propensities (Giles 2015, §8)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §8
"Continuous-time Markov chains", pp. 55–56 (`docs/giles2015.txt`, ll. 2366–2417), after Anderson
and Higham (2012).

**Setting.**  One reaction `x → x + 1` with propensity `λ : ℕ → [0, ∞)`; "the 'tau-leaping'
method … gives the discrete equation `x_{n+1} = x_n + P(hλ(x_n))`" (p. 55, ll. 2372–2375;
`tauStep`, `tauChain`), the coarse path makes steps of size `2h`, and the two are coupled by "two
Poisson variates based on the minimum of the two reactions rates, and the absolute difference …
using `P₁` as the Poisson variate for the path with the smaller rate, and `P₁ + P₂` for the path
with the larger rate" (pp. 55–56, ll. 2389–2407; `coupledChain`).  "This elegant approach …
leads to a very effective multilevel algorithm with a correction variance which is `O(h)`,
leading to an `O(ε⁻²(log ε)²)` complexity" (p. 56, ll. 2407–2410).

The library proves the `O(h)` correction variance (`coupledChain_sq_le`,
`variance_tauCorrection_le`) and Theorem 1 (`tauLeaping_mlmc_theorem1`) for a propensity that is
`K`-Lipschitz **and bounded** by `Λ`, which excludes the natural linear birth rate `λ(x) = cx`.
Here the bound `Λ` is removed: the propensity is only `K`-Lipschitz (on `ℕ` this gives the linear
growth `λ(x) ≤ λ(0) + Kx`), so the chain may grow, and the proofs control its moments.

**What is proved.**
* `tauChain_moments_linear`: for `λ(x) ≤ a + bx`, uniformly in the step `h` and the number of
  steps `n` with `nh ≤ T`: `x_n ∈ L²`, `E[x_n] ≤ (1 + x₀) e^{(a+b)T}` and
  `E[x_n²] ≤ (1 + x₀)² e^{(3(a+b) + (a+b)²T)T}` (from the one-step bounds
  `E[(1 + x_{n+1})² | x_n] ≤ (1 + h(3M + hM²))(1 + x_n)²`, `M = a + b`,
  `lintegral_sq_tauStep_le_linear`, `lintegral_sq_tauChain_le_linear`).
* `lintegral_sq_coupledTwoStep_le_rate`, `lintegral_sq_coupledChain_le_rate`: the two-step and
  chain recursions of `PoissonCoupling.lean` with the uniform bound `hλ ≤ ℓ` on the coarse rate
  replaced by the coarse rate `r = hλ(x^c)` itself; its moments `E[r + r²] = O(h)` come from the
  moment bounds of the coarse chain (`coupledChain_snd`).
* `coupledChain_sq_le_lipschitz`: **`E[(x_{2k} − x^c_{2k})²] ≤ c h`** for all `h, k` with
  `2kh ≤ T`, with `c` depending only on `K`, `a ≥ λ(0)`, `T`, `x₀` (uniform over all such
  propensities); `variance_coupledChain_le_lipschitz`: **the correction `Φ(x_{2k}) − Φ(x^c_{2k})` of
  an `L_Φ`-Lipschitz payoff is in `L²`, with second moment and variance `≤ c h`**.
* `variance_tauCorrection_le_lipschitz` (`β = 1` on every level) and
  **`tauLeaping_mlmc_theorem1_lipschitz`: Theorem 1 with an assumed weak rate** — for a
  `K`-Lipschitz, possibly unbounded propensity, a Lipschitz payoff and a weak rate `α ≥ ½`
  (hypothesis), a square-integrable error with mean square error `< ε²` at cost `≤ c₄ ε⁻²(log ε)²`.
* **The linear birth example `λ(x) = cx`**: `tauLeaping_mlmc_linearBirth` (any Lipschitz payoff,
  weak rate assumed); for the payoff `Φ(x) = x` the mean is explicit,
  `E[x_n] = x₀(1 + hc)ⁿ` (`integral_tauChain_linearBirth`), the weak error against
  `x₀ e^{cT}` is `≤ x₀ (cT)² e^{cT}/N` (`tauLeaping_linearBirth_weak_error`, `α = 1`), and
  `tauLeaping_mlmc_linearBirth_mean` is Theorem 1 with **no assumed rate**.  This also shows that
  the weak-rate hypothesis of `tauLeaping_mlmc_theorem1_lipschitz` is satisfiable for an
  unbounded propensity.

**Deviations from the paper.**  One reaction with stoichiometry `+1` (Anderson and Higham treat
several reactions).  The weak rate is a hypothesis of `tauLeaping_mlmc_theorem1_lipschitz` and
`tauLeaping_mlmc_linearBirth` (`α = 1` in the paper): the weak rate against the exact chain needs
the exact continuous-time chain with unbounded rates, which is not constructed
(`TauLeapingExact.lean` uniformises with `Λ < ∞`); the target `x₀ e^{cT}` of
`tauLeaping_mlmc_linearBirth_mean` is the limit of the tau-leaping means (it is also the mean of
the exact linear birth process, which is not formalised).  The constants are far from sharp and
exponential in `T` (in `T²`, as `h ≤ T` is used to absorb `h²` terms), and, unlike the bounded
case, depend on `x₀`.  Level `0` uses one tau-leaping step of size `T` (`tauLevelLaw`).

**Not proved.**  The weak rate of tau-leaping for a general unbounded propensity, against the
exact chain or against the limit of the tau-leaping means (out of scope); the exact chain with
unbounded rates and the unbiased `O(ε⁻²)` estimator coupled to it; several reactions.

**Check.**  An exact computation of the coupled law (`λ(x) = x`, `T = 1`, `x₀ = 1`, truncated
state space, lost mass `< 10⁻¹²`) gives `E[(x^f_T − x^c_T)²]/h = 0.875, 1.611, 2.284, 2.746,
3.016, 3.160, 3.235` for `h = 2^{−1}, …, 2^{−7}` (increasing to `≈ 3.31`; the proved constant
`28e^{10} ≈ 6·10⁵` is far larger), and fine-path means `x₀(1 + h)^{1/h}`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace MLMC

/-! ### Elementary bounds -/

/-- `(1 + u)ⁿ ≤ e^{nu}` for `u ≥ 0` (used for the moment bounds of Giles 2015, §8). -/
lemma one_add_pow_le_exp_mul {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n ≤ Real.exp (n * u) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp u]) n

/-- A nonnegative function on a discrete space whose lower integral is at most `ofReal B` is
integrable with integral at most `B` (used throughout Giles 2015, §8). -/
lemma integral_le_of_lintegral_ofReal_le {α : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] {μ : Measure α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    {B : ℝ} (hB : 0 ≤ B) (hle : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal B) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ B := by
  have hnn : 0 ≤ᵐ[μ] f := ae_of_all _ hf
  refine ⟨⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn]
    exact hle.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn Measurable.of_discrete.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hB hle

/-! ### Moments of the tau-leaping chain for a propensity of linear growth -/

section Moments

variable {lam : ℕ → ℝ≥0} {M : ℝ}

/-- **One step, first moment** (Giles 2015, §8, p. 55, l. 2375: "`x_{n+1} = x_n + P(hλ(x_n))`"):
for `λ(x) ≤ M(1 + x)`, `E[1 + x + P(hλ(x))] ≤ (1 + hM)(1 + x)`. -/
lemma lintegral_tauStep_le_linear (hlin : ∀ x, (lam x : ℝ) ≤ M * (1 + x)) (h : ℝ≥0) (x : ℕ) :
    ∫⁻ y, ENNReal.ofReal (1 + (y : ℝ)) ∂(tauStep lam h x) ≤
      ENNReal.ofReal ((1 + h * M) * (1 + (x : ℝ))) := by
  have hr : ((h * lam x : ℝ≥0) : ℝ) ≤ h * (M * (1 + x)) := by
    rw [NNReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (hlin x) h.coe_nonneg
  rw [tauStep, lintegral_map Measurable.of_discrete Measurable.of_discrete]
  calc ∫⁻ n, ENNReal.ofReal (1 + ((x + n : ℕ) : ℝ)) ∂(poissonMeasure (h * lam x))
      = ∫⁻ n, ENNReal.ofReal ((1 + (x : ℝ)) + 1 * n + 0 * (n : ℝ) ^ 2)
          ∂(poissonMeasure (h * lam x)) := by
        refine lintegral_congr fun n => ?_
        congr 1
        push_cast
        ring
    _ = ENNReal.ofReal ((1 + (x : ℝ)) + 1 * ((h * lam x : ℝ≥0) : ℝ) +
          0 * (((h * lam x : ℝ≥0) : ℝ) + ((h * lam x : ℝ≥0) : ℝ) ^ 2)) :=
        lintegral_poly_poissonMeasure _ (by positivity) zero_le_one le_rfl
    _ ≤ ENNReal.ofReal ((1 + h * M) * (1 + (x : ℝ))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith

/-- **One step, second moment** (Giles 2015, §8, p. 55, l. 2375): for `λ(x) ≤ M(1 + x)`,
`E[(1 + x + P(hλ(x)))²] ≤ (1 + h(3M + hM²))(1 + x)²`. -/
lemma lintegral_sq_tauStep_le_linear (hM : 0 ≤ M) (hlin : ∀ x, (lam x : ℝ) ≤ M * (1 + x))
    (h : ℝ≥0) (x : ℕ) :
    ∫⁻ y, ENNReal.ofReal ((1 + (y : ℝ)) ^ 2) ∂(tauStep lam h x) ≤
      ENNReal.ofReal ((1 + h * (3 * M + h * M ^ 2)) * (1 + (x : ℝ)) ^ 2) := by
  have hr : ((h * lam x : ℝ≥0) : ℝ) ≤ h * (M * (1 + x)) := by
    rw [NNReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (hlin x) h.coe_nonneg
  have hr0 : (0 : ℝ) ≤ ((h * lam x : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hh0 : (0 : ℝ) ≤ h := h.coe_nonneg
  rw [tauStep, lintegral_map Measurable.of_discrete Measurable.of_discrete]
  calc ∫⁻ n, ENNReal.ofReal ((1 + ((x + n : ℕ) : ℝ)) ^ 2) ∂(poissonMeasure (h * lam x))
      = ∫⁻ n, ENNReal.ofReal ((1 + (x : ℝ)) ^ 2 + 2 * (1 + (x : ℝ)) * n + 1 * (n : ℝ) ^ 2)
          ∂(poissonMeasure (h * lam x)) := by
        refine lintegral_congr fun n => ?_
        congr 1
        push_cast
        ring
    _ = ENNReal.ofReal ((1 + (x : ℝ)) ^ 2 + 2 * (1 + (x : ℝ)) * ((h * lam x : ℝ≥0) : ℝ) +
          1 * (((h * lam x : ℝ≥0) : ℝ) + ((h * lam x : ℝ≥0) : ℝ) ^ 2)) :=
        lintegral_poly_poissonMeasure _ (sq_nonneg _) (by positivity) zero_le_one
    _ ≤ ENNReal.ofReal ((1 + h * (3 * M + h * M ^ 2)) * (1 + (x : ℝ)) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        set u : ℝ := 1 + (x : ℝ) with hu
        set r : ℝ := ((h * lam x : ℝ≥0) : ℝ) with hr'
        have hu1 : 1 ≤ u := by
          rw [hu]
          linarith [(Nat.cast_nonneg x : (0 : ℝ) ≤ x)]
        have hhM : 0 ≤ (h : ℝ) * M := mul_nonneg hh0 hM
        have e1 : 2 * u * r ≤ 2 * u * ((h : ℝ) * M * u) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have e2 : r ≤ (h : ℝ) * M * u ^ 2 := by
          have : (h : ℝ) * M * u ≤ (h : ℝ) * M * u ^ 2 :=
            mul_le_mul_of_nonneg_left (by nlinarith) hhM
          linarith
        have e3 : r ^ 2 ≤ ((h : ℝ) * M * u) ^ 2 := pow_le_pow_left₀ hr0 (by linarith) 2
        nlinarith [e1, e2, e3]

/-- **The first moment of the tau-leaping chain** (Giles 2015, §8): for `λ(x) ≤ M(1 + x)`,
`E[1 + x_n] ≤ (1 + hM)ⁿ (1 + x₀)`. -/
lemma lintegral_tauChain_le_linear (hM : 0 ≤ M) (hlin : ∀ x, (lam x : ℝ) ≤ M * (1 + x))
    (h : ℝ≥0) (x₀ : ℕ) : ∀ n,
    ∫⁻ y, ENNReal.ofReal (1 + (y : ℝ)) ∂(tauChain lam h x₀ n) ≤
      ENNReal.ofReal ((1 + h * M) ^ n * (1 + (x₀ : ℝ)))
  | 0 => by
      rw [tauChain, lintegral_dirac, pow_zero, one_mul]
  | n + 1 => by
      have hq : 0 ≤ 1 + (h : ℝ) * M := by positivity
      rw [tauChain, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
      calc ∫⁻ a, ∫⁻ y, ENNReal.ofReal (1 + (y : ℝ)) ∂(tauStep lam h a) ∂(tauChain lam h x₀ n)
          ≤ ∫⁻ a, ENNReal.ofReal (1 + (h : ℝ) * M) * ENNReal.ofReal (1 + (a : ℝ))
              ∂(tauChain lam h x₀ n) :=
            lintegral_mono fun a => by
              rw [← ENNReal.ofReal_mul hq]
              exact lintegral_tauStep_le_linear hlin h a
        _ = ENNReal.ofReal (1 + (h : ℝ) * M) *
              ∫⁻ a, ENNReal.ofReal (1 + (a : ℝ)) ∂(tauChain lam h x₀ n) :=
            lintegral_const_mul _ Measurable.of_discrete
        _ ≤ ENNReal.ofReal (1 + (h : ℝ) * M) *
              ENNReal.ofReal ((1 + h * M) ^ n * (1 + (x₀ : ℝ))) := by
            gcongr
            exact lintegral_tauChain_le_linear hM hlin h x₀ n
        _ = ENNReal.ofReal ((1 + h * M) ^ (n + 1) * (1 + (x₀ : ℝ))) := by
            rw [← ENNReal.ofReal_mul hq]
            congr 1
            ring

/-- **The second moment of the tau-leaping chain** (Giles 2015, §8): for `λ(x) ≤ M(1 + x)`,
`E[(1 + x_n)²] ≤ (1 + h(3M + hM²))ⁿ (1 + x₀)²`. -/
lemma lintegral_sq_tauChain_le_linear (hM : 0 ≤ M) (hlin : ∀ x, (lam x : ℝ) ≤ M * (1 + x))
    (h : ℝ≥0) (x₀ : ℕ) : ∀ n,
    ∫⁻ y, ENNReal.ofReal ((1 + (y : ℝ)) ^ 2) ∂(tauChain lam h x₀ n) ≤
      ENNReal.ofReal ((1 + h * (3 * M + h * M ^ 2)) ^ n * (1 + (x₀ : ℝ)) ^ 2)
  | 0 => by
      rw [tauChain, lintegral_dirac, pow_zero, one_mul]
  | n + 1 => by
      have hq : 0 ≤ 1 + (h : ℝ) * (3 * M + h * M ^ 2) := by positivity
      rw [tauChain, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
      calc ∫⁻ a, ∫⁻ y, ENNReal.ofReal ((1 + (y : ℝ)) ^ 2) ∂(tauStep lam h a)
            ∂(tauChain lam h x₀ n)
          ≤ ∫⁻ a, ENNReal.ofReal (1 + (h : ℝ) * (3 * M + h * M ^ 2)) *
              ENNReal.ofReal ((1 + (a : ℝ)) ^ 2) ∂(tauChain lam h x₀ n) :=
            lintegral_mono fun a => by
              rw [← ENNReal.ofReal_mul hq]
              exact lintegral_sq_tauStep_le_linear hM hlin h a
        _ = ENNReal.ofReal (1 + (h : ℝ) * (3 * M + h * M ^ 2)) *
              ∫⁻ a, ENNReal.ofReal ((1 + (a : ℝ)) ^ 2) ∂(tauChain lam h x₀ n) :=
            lintegral_const_mul _ Measurable.of_discrete
        _ ≤ ENNReal.ofReal (1 + (h : ℝ) * (3 * M + h * M ^ 2)) *
              ENNReal.ofReal ((1 + h * (3 * M + h * M ^ 2)) ^ n * (1 + (x₀ : ℝ)) ^ 2) := by
            gcongr
            exact lintegral_sq_tauChain_le_linear hM hlin h x₀ n
        _ = ENNReal.ofReal ((1 + h * (3 * M + h * M ^ 2)) ^ (n + 1) * (1 + (x₀ : ℝ)) ^ 2) := by
            rw [← ENNReal.ofReal_mul hq]
            congr 1
            ring

/-- `n h · h ≤ T²` when `0 ≤ h` and `n h ≤ T` (if `n ≥ 1` then `h ≤ T`; used in Giles 2015, §8). -/
lemma natCast_mul_mul_le_sq {n : ℕ} {h T : ℝ} (hh : 0 ≤ h) (hnT : n * h ≤ T) :
    n * h * h ≤ T * T := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_mul] at hnT ⊢
    exact mul_nonneg hnT hnT
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hhT : h ≤ T := le_trans (by nlinarith) hnT
    have h0 : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
    calc (n : ℝ) * h * h ≤ T * h := mul_le_mul_of_nonneg_right hnT hh
      _ ≤ T * T := mul_le_mul_of_nonneg_left hhT (h0.trans hnT)

/-- A propensity of linear growth, `λ(x) ≤ a + bx`, satisfies `λ(x) ≤ (a + b)(1 + x)` (Giles 2015,
§8). -/
lemma le_mul_one_add_of_linear {a b : ℝ≥0} (hlin : ∀ x, (lam x : ℝ) ≤ a + b * x) (x : ℕ) :
    (lam x : ℝ) ≤ ((a : ℝ) + b) * (1 + x) := by
  have ha : (0 : ℝ) ≤ a := a.coe_nonneg
  have hb : (0 : ℝ) ≤ b := b.coe_nonneg
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  nlinarith [hlin x, mul_nonneg ha hx]

/-- **Moment bounds for tau-leaping with a propensity of linear growth** (Giles 2015, §8, p. 55,
ll. 2372–2376: "the 'tau-leaping' method … gives the discrete equation
`x_{n+1} = x_n + P(hλ(x_n))`").  Let the propensity grow at most linearly, `λ(x) ≤ a + bx` (every
`K`-Lipschitz propensity on `ℕ` does, with `a = λ(0)`, `b = K`; e.g. the linear birth rate
`λ(x) = cx`, which is unbounded).  Then, uniformly in the time step `h` and the number of steps `n`
with `nh ≤ T`, the chain `x_n` is square integrable and
`E[x_n] ≤ (1 + x₀) e^{(a+b)T}`, `E[x_n²] ≤ (1 + x₀)² e^{(3(a+b) + (a+b)²T)T}`.
The chain may grow, but only exponentially in `T`. -/
theorem tauChain_moments_linear {lam : ℕ → ℝ≥0} {a b : ℝ≥0}
    (hlin : ∀ x, (lam x : ℝ) ≤ a + b * x) (x₀ : ℕ) {T : ℝ} {h : ℝ≥0} {n : ℕ}
    (hnT : n * (h : ℝ) ≤ T) :
    MemLp (fun x : ℕ => (x : ℝ)) 2 (tauChain lam h x₀ n) ∧
      ∫ x, (x : ℝ) ∂(tauChain lam h x₀ n) ≤ (1 + x₀) * Real.exp ((a + b) * T) ∧
      ∫ x, (x : ℝ) ^ 2 ∂(tauChain lam h x₀ n) ≤
        (1 + x₀) ^ 2 * Real.exp ((3 * (a + b) + (a + b) ^ 2 * T) * T) := by
  set M : ℝ := (a : ℝ) + b with hMdef
  have hM : 0 ≤ M := by positivity
  have hl : ∀ x, (lam x : ℝ) ≤ M * (1 + x) := le_mul_one_add_of_linear hlin
  have hh0 : (0 : ℝ) ≤ h := h.coe_nonneg
  have hnh0 : (0 : ℝ) ≤ n * h := mul_nonneg (Nat.cast_nonneg n) hh0
  have hT0 : 0 ≤ T := hnh0.trans hnT
  have hx₀ : (0 : ℝ) ≤ 1 + x₀ := by positivity
  -- the first moment
  have h1 : ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(tauChain lam h x₀ n) ≤
      ENNReal.ofReal ((1 + x₀) * Real.exp (M * T)) := by
    refine (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (by linarith)).trans
      ((lintegral_tauChain_le_linear hM hl h x₀ n).trans (ENNReal.ofReal_le_ofReal ?_))
    calc (1 + (h : ℝ) * M) ^ n * (1 + (x₀ : ℝ))
        ≤ Real.exp (n * ((h : ℝ) * M)) * (1 + x₀) :=
          mul_le_mul_of_nonneg_right (one_add_pow_le_exp_mul (by positivity) n) hx₀
      _ ≤ Real.exp (M * T) * (1 + x₀) := by
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hx₀
          have := mul_le_mul_of_nonneg_left hnT hM
          nlinarith
      _ = (1 + x₀) * Real.exp (M * T) := mul_comm _ _
  -- the second moment
  have h2 : ∫⁻ y, ENNReal.ofReal ((y : ℝ) ^ 2) ∂(tauChain lam h x₀ n) ≤
      ENNReal.ofReal ((1 + x₀) ^ 2 * Real.exp ((3 * M + M ^ 2 * T) * T)) := by
    refine (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_).trans
      ((lintegral_sq_tauChain_le_linear hM hl h x₀ n).trans (ENNReal.ofReal_le_ofReal ?_))
    · have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg y
      nlinarith
    calc (1 + (h : ℝ) * (3 * M + h * M ^ 2)) ^ n * (1 + (x₀ : ℝ)) ^ 2
        ≤ Real.exp (n * ((h : ℝ) * (3 * M + h * M ^ 2))) * (1 + x₀) ^ 2 :=
          mul_le_mul_of_nonneg_right (one_add_pow_le_exp_mul (by positivity) n) (sq_nonneg _)
      _ ≤ Real.exp ((3 * M + M ^ 2 * T) * T) * (1 + x₀) ^ 2 := by
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
          have e0 := mul_le_mul_of_nonneg_left hnT (by positivity : (0 : ℝ) ≤ 3 * M)
          have e1 := natCast_mul_mul_le_sq hh0 hnT
          have e2 : (n : ℝ) * h * h * M ^ 2 ≤ T * T * M ^ 2 :=
            mul_le_mul_of_nonneg_right e1 (sq_nonneg M)
          nlinarith
      _ = (1 + x₀) ^ 2 * Real.exp ((3 * M + M ^ 2 * T) * T) := mul_comm _ _
  obtain ⟨-, hm1⟩ := integral_le_of_lintegral_ofReal_le (fun y => Nat.cast_nonneg y)
    (by positivity) h1
  obtain ⟨hi2, hm2⟩ := integral_le_of_lintegral_ofReal_le (fun y => sq_nonneg _)
    (by positivity) h2
  exact ⟨(memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable).2 hi2, hm1, hm2⟩

end Moments

/-! ### The coupled paths with a state-dependent bound on the coarse rate -/

section Coupled

variable {lam : ℕ → ℝ≥0} {h : ℝ≥0} {κ : ℝ}

/-- **Two coupled fine steps, the coarse rate unbounded** (Giles 2015, §8, p. 55, ll. 2389–2392:
the coarse Poisson variate is expressed "as the sum of two Poisson variates, `P(hλ(x^c_n))`
corresponding to the first and second fine path timesteps", each coupled with the fine one).  As
`lintegral_sq_coupledTwoStep_le`, but the bound `hλ ≤ ℓ` on the coarse rate is replaced by the
coarse rate `r = hλ(x^c)` itself: if `|hλ(x) − hλ(y)| ≤ κ|x − y|`, then from `(x, x^c)`,
`E[(x₂ − x^c₂)²] ≤ (1 + 4κ + 2κ²)² (x − x^c)² + (κ + 2κ²)(r + r²) + κr`. -/
lemma lintegral_sq_coupledTwoStep_le_rate (hκ : 0 ≤ κ)
    (hr : ∀ x y : ℕ, |((h * lam x : ℝ≥0) : ℝ) - ((h * lam y : ℝ≥0) : ℝ)| ≤ κ * |(x : ℝ) - y|)
    (s : ℕ × ℕ) :
    ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledTwoStep lam h s) ≤
      ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2 * ((s.1 : ℝ) - s.2) ^ 2 +
        ((κ + 2 * κ ^ 2) * (((h * lam s.2 : ℝ≥0) : ℝ) + ((h * lam s.2 : ℝ≥0) : ℝ) ^ 2) +
          κ * ((h * lam s.2 : ℝ≥0) : ℝ))) := by
  set ℓ : ℝ := ((h * lam s.2 : ℝ≥0) : ℝ) with hℓdef
  have hℓ : 0 ≤ ℓ := NNReal.coe_nonneg _
  have hα : 0 ≤ 1 + 4 * κ + 2 * κ ^ 2 := by positivity
  -- the second fine step, from the states after the first: the fine rate `hλ(x + i)` against the
  -- frozen coarse rate `hλ(x^c)`
  have hin : ∀ ij : ℕ × ℕ,
      ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2)
          ∂((coupledIncr (h * lam (s.1 + ij.1)) (h * lam s.2)).map fun ij' =>
            (s.1 + ij.1 + ij'.1, s.2 + ij.2 + ij'.2)) ≤
        ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) *
            (((s.1 + ij.1 : ℕ) : ℝ) - ((s.2 + ij.2 : ℕ) : ℝ)) ^ 2 +
          (κ + 2 * κ ^ 2) * (ij.2 : ℝ) ^ 2 + κ * ij.2) := by
    intro ij
    rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
    refine (lintegral_sq_coupledIncr_le _ _ (s.1 + ij.1) (s.2 + ij.2)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    refine coupled_step_bound hκ (abs_nonneg _) ?_ (abs_natCast_sub_le_sq _ _)
    refine (hr _ _).trans (mul_le_mul_of_nonneg_left ?_ hκ)
    have e : ((s.1 + ij.1 : ℕ) : ℝ) - (s.2 : ℝ) =
        (((s.1 + ij.1 : ℕ) : ℝ) - ((s.2 + ij.2 : ℕ) : ℝ)) + ij.2 := by
      push_cast
      ring
    rw [e]
    exact (abs_add_le _ _).trans (by rw [Nat.abs_cast])
  -- the first fine step and the moments of the first coarse increment
  have hd1 : ∫⁻ ij, ENNReal.ofReal ((((s.1 + ij.1 : ℕ) : ℝ) - ((s.2 + ij.2 : ℕ) : ℝ)) ^ 2)
      ∂(coupledIncr (h * lam s.1) (h * lam s.2)) ≤
      ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) * ((s.1 : ℝ) - s.2) ^ 2) := by
    refine (lintegral_sq_coupledIncr_le _ _ s.1 s.2).trans (ENNReal.ofReal_le_ofReal ?_)
    have h0 := coupled_step_bound (d := (s.1 : ℝ) - s.2) (j := 0)
      (R := |((h * lam s.1 : ℝ≥0) : ℝ) - ((h * lam s.2 : ℝ≥0) : ℝ)|) hκ (abs_nonneg _)
      (by rw [add_zero]; exact hr _ _) (abs_natCast_sub_le_sq _ _)
    linarith
  have hj2 : ∫⁻ ij, ENNReal.ofReal ((ij.2 : ℝ) ^ 2) ∂(coupledIncr (h * lam s.1) (h * lam s.2)) =
      ENNReal.ofReal (ℓ + ℓ ^ 2) := by
    rw [lintegral_coupledIncr_snd _ _ fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ 2),
      lintegral_sq_poissonMeasure]
  have hj1 : ∫⁻ ij, ENNReal.ofReal (ij.2 : ℝ) ∂(coupledIncr (h * lam s.1) (h * lam s.2)) =
      ENNReal.ofReal ℓ := by
    rw [lintegral_coupledIncr_snd _ _ fun n : ℕ => ENNReal.ofReal (n : ℝ),
      lintegral_id_poissonMeasure]
  calc ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledTwoStep lam h s)
      ≤ ∫⁻ ij, ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2)
          ∂((coupledIncr (h * lam (s.1 + ij.1)) (h * lam s.2)).map fun ij' =>
            (s.1 + ij.1 + ij'.1, s.2 + ij.2 + ij'.2))
          ∂(coupledIncr (h * lam s.1) (h * lam s.2)) := by
        rw [coupledTwoStep]
        exact Measure.lintegral_bind_le _ _ _
    _ ≤ ∫⁻ ij, ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) *
            (((s.1 + ij.1 : ℕ) : ℝ) - ((s.2 + ij.2 : ℕ) : ℝ)) ^ 2 +
          (κ + 2 * κ ^ 2) * (ij.2 : ℝ) ^ 2 + κ * ij.2)
          ∂(coupledIncr (h * lam s.1) (h * lam s.2)) :=
        lintegral_mono hin
    _ = ENNReal.ofReal (1 + 4 * κ + 2 * κ ^ 2) *
            ∫⁻ ij, ENNReal.ofReal ((((s.1 + ij.1 : ℕ) : ℝ) - ((s.2 + ij.2 : ℕ) : ℝ)) ^ 2)
              ∂(coupledIncr (h * lam s.1) (h * lam s.2)) +
          ENNReal.ofReal (κ + 2 * κ ^ 2) *
            ∫⁻ ij, ENNReal.ofReal ((ij.2 : ℝ) ^ 2) ∂(coupledIncr (h * lam s.1) (h * lam s.2)) +
          ENNReal.ofReal κ *
            ∫⁻ ij, ENNReal.ofReal (ij.2 : ℝ) ∂(coupledIncr (h * lam s.1) (h * lam s.2)) :=
        lintegral_ofReal_add3 _ (fun _ => by positivity) (fun _ => by positivity)
          (fun _ => by positivity) hα (by positivity) hκ
    _ ≤ ENNReal.ofReal (1 + 4 * κ + 2 * κ ^ 2) *
            ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) * ((s.1 : ℝ) - s.2) ^ 2) +
          ENNReal.ofReal (κ + 2 * κ ^ 2) * ENNReal.ofReal (ℓ + ℓ ^ 2) +
          ENNReal.ofReal κ * ENNReal.ofReal ℓ := by
        rw [hj2, hj1]
        gcongr
    _ = ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2 * ((s.1 : ℝ) - s.2) ^ 2 +
          ((κ + 2 * κ ^ 2) * (ℓ + ℓ ^ 2) + κ * ℓ)) := by
        rw [← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hκ,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The mean square difference of the coupled paths, the coarse rate unbounded** (Giles 2015,
§8): with `A = (1 + 4κ + 2κ²)²` and `g(y) = (κ + 2κ²)(r + r²) + κr`, `r = hλ(y)`, if the mean of
`g` at the coarse state of the coupled pair is at most `B` at the start of each of the first `k`
coarse steps, then `E[(x_{2k} − x^c_{2k})²] ≤ B ∑_{i<k} Aⁱ`. -/
lemma lintegral_sq_coupledChain_le_rate (hκ : 0 ≤ κ)
    (hr : ∀ x y : ℕ, |((h * lam x : ℝ≥0) : ℝ) - ((h * lam y : ℝ≥0) : ℝ)| ≤ κ * |(x : ℝ) - y|)
    {B : ℝ} (hB : 0 ≤ B) (x₀ : ℕ) : ∀ k : ℕ,
    (∀ i < k, ∫⁻ s, ENNReal.ofReal ((κ + 2 * κ ^ 2) *
        (((h * lam s.2 : ℝ≥0) : ℝ) + ((h * lam s.2 : ℝ≥0) : ℝ) ^ 2) +
          κ * ((h * lam s.2 : ℝ≥0) : ℝ)) ∂(coupledChain lam h x₀ i) ≤ ENNReal.ofReal B) →
    ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledChain lam h x₀ k) ≤
      ENNReal.ofReal (B * ∑ i ∈ Finset.range k, ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) ^ i)
  | 0, _ => by
      rw [coupledChain, lintegral_dirac]
      simp
  | k + 1, hg => by
      have hA : 0 ≤ (1 + 4 * κ + 2 * κ ^ 2) ^ 2 := by positivity
      have hS : 0 ≤ ∑ i ∈ Finset.range k, ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) ^ i :=
        Finset.sum_nonneg fun i _ => pow_nonneg hA i
      have hgk := hg k (Nat.lt_succ_self k)
      have hprev := lintegral_sq_coupledChain_le_rate hκ hr hB x₀ k
        fun i hi => hg i (Nat.lt_succ_of_lt hi)
      have e : ∀ s : ℕ × ℕ, ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2 * ((s.1 : ℝ) - s.2) ^ 2 +
          ((κ + 2 * κ ^ 2) * (((h * lam s.2 : ℝ≥0) : ℝ) + ((h * lam s.2 : ℝ≥0) : ℝ) ^ 2) +
            κ * ((h * lam s.2 : ℝ≥0) : ℝ))) =
          ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) * ENNReal.ofReal (((s.1 : ℝ) - s.2) ^ 2) +
            ENNReal.ofReal ((κ + 2 * κ ^ 2) *
              (((h * lam s.2 : ℝ≥0) : ℝ) + ((h * lam s.2 : ℝ≥0) : ℝ) ^ 2) +
                κ * ((h * lam s.2 : ℝ≥0) : ℝ)) := fun s => by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hA]
      calc ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledChain lam h x₀ (k + 1))
          ≤ ∫⁻ s, ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledTwoStep lam h s)
              ∂(coupledChain lam h x₀ k) := by
            rw [coupledChain]
            exact Measure.lintegral_bind_le _ _ _
        _ ≤ ∫⁻ s, (ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) *
                ENNReal.ofReal (((s.1 : ℝ) - s.2) ^ 2) +
              ENNReal.ofReal ((κ + 2 * κ ^ 2) *
                (((h * lam s.2 : ℝ≥0) : ℝ) + ((h * lam s.2 : ℝ≥0) : ℝ) ^ 2) +
                  κ * ((h * lam s.2 : ℝ≥0) : ℝ))) ∂(coupledChain lam h x₀ k) :=
            lintegral_mono fun s => (lintegral_sq_coupledTwoStep_le_rate hκ hr s).trans_eq (e s)
        _ = ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) *
              ∫⁻ s, ENNReal.ofReal (((s.1 : ℝ) - s.2) ^ 2) ∂(coupledChain lam h x₀ k) +
            ∫⁻ s, ENNReal.ofReal ((κ + 2 * κ ^ 2) *
                (((h * lam s.2 : ℝ≥0) : ℝ) + ((h * lam s.2 : ℝ≥0) : ℝ) ^ 2) +
                  κ * ((h * lam s.2 : ℝ≥0) : ℝ)) ∂(coupledChain lam h x₀ k) := by
            rw [lintegral_add_left (Measurable.of_discrete.const_mul _),
              lintegral_const_mul _ Measurable.of_discrete]
        _ ≤ ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) *
              ENNReal.ofReal (B * ∑ i ∈ Finset.range k, ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) ^ i) +
            ENNReal.ofReal B := by
            gcongr
        _ = ENNReal.ofReal (B * ∑ i ∈ Finset.range (k + 1), ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) ^ i) := by
            rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add (mul_nonneg hA (mul_nonneg hB hS)) hB,
              geom_sum_succ]
            congr 1
            ring

/-- A `K`-Lipschitz propensity grows at most linearly: `λ(x) ≤ (λ(0) + K)(1 + x)` (Giles 2015,
§8). -/
lemma le_mul_one_add_of_lipschitz {K : ℝ≥0}
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (x : ℕ) :
    (lam x : ℝ) ≤ ((lam 0 : ℝ) + K) * (1 + x) := by
  have h1 := hK x 0
  rw [Nat.cast_zero, sub_zero, Nat.abs_cast] at h1
  have h0 : (0 : ℝ) ≤ lam 0 := (lam 0).coe_nonneg
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  nlinarith [le_abs_self ((lam x : ℝ) - lam 0), mul_nonneg h0 hx]

/-- The defect of one coarse step is `O(h²)` (Giles 2015, §8): if `κ = hK`, `h ≤ T`,
`0 ≤ r ≤ hMu` and `u ≥ 1`, then `(κ + 2κ²)(r + r²) + κr ≤ h² G u²` with
`G = (K + 2TK²)(M + TM²) + KM`. -/
lemma coupled_defect_le {h K M T u r : ℝ} (hh0 : 0 ≤ h) (hK0 : 0 ≤ K) (hM : 0 ≤ M)
    (hhT : h ≤ T) (hu1 : 1 ≤ u) (hr0 : 0 ≤ r) (hrle : r ≤ h * M * u) :
    (h * K + 2 * (h * K) ^ 2) * (r + r ^ 2) + h * K * r ≤
      h ^ 2 * ((K + 2 * T * K ^ 2) * (M + T * M ^ 2) + K * M) * u ^ 2 := by
  have hT0 : 0 ≤ T := hh0.trans hhT
  have huu : u ≤ u ^ 2 := by nlinarith
  have hhM : 0 ≤ h * M := mul_nonneg hh0 hM
  have hhh : h * h ≤ h * T := mul_le_mul_of_nonneg_left hhT hh0
  have f1 : r ≤ h * M * u ^ 2 := hrle.trans (mul_le_mul_of_nonneg_left huu hhM)
  have e1 : r + r ^ 2 ≤ h * (M + T * M ^ 2) * u ^ 2 := by
    have f2 : r ^ 2 ≤ (h * M * u) ^ 2 := pow_le_pow_left₀ hr0 hrle 2
    have f3 : (h * M * u) ^ 2 ≤ h * (T * M ^ 2) * u ^ 2 := by
      have hMu : 0 ≤ M ^ 2 * u ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hhh hMu]
    nlinarith [f1, f2, f3]
  have e2 : h * K + 2 * (h * K) ^ 2 ≤ h * (K + 2 * T * K ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hhh (sq_nonneg K)]
  have e3 : h * K * r ≤ h ^ 2 * (K * M) * u ^ 2 := by
    have := mul_le_mul_of_nonneg_left f1 (mul_nonneg hh0 hK0)
    nlinarith [this]
  have e4 : (h * K + 2 * (h * K) ^ 2) * (r + r ^ 2) ≤
      (h * (K + 2 * T * K ^ 2)) * (h * (M + T * M ^ 2) * u ^ 2) :=
    mul_le_mul e2 e1 (by positivity) (mul_nonneg hh0 (by positivity))
  nlinarith [e4, e3]

/-- The geometric growth factor of the coupled chain is `e^{O(T)}` (Giles 2015, §8): for
`0 ≤ h`, `κ = hK` and `2kh ≤ T`, `((1 + 4κ + 2κ²)²)ᵏ ≤ e^{T(4K + 2TK²)}`. -/
lemma coupled_growth_le {h K T : ℝ} (hh0 : 0 ≤ h) (hK0 : 0 ≤ K) {k : ℕ}
    (hkT : 2 * k * h ≤ T) :
    ((1 + 4 * (h * K) + 2 * (h * K) ^ 2) ^ 2) ^ k ≤ Real.exp (T * (4 * K + 2 * T * K ^ 2)) := by
  rw [← pow_mul]
  have hκ : 0 ≤ h * K := mul_nonneg hh0 hK0
  have hexp := Real.add_one_le_exp (4 * (h * K) + 2 * (h * K) ^ 2)
  refine (pow_le_pow_left₀ (by positivity) (by linarith) _).trans ?_
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  have h2k : ((2 * k : ℕ) : ℝ) * h ≤ T := by
    push_cast
    exact hkT
  have e1 := natCast_mul_mul_le_sq hh0 h2k
  have e2 : ((2 * k : ℕ) : ℝ) * h * h * (2 * K ^ 2) ≤ T * T * (2 * K ^ 2) :=
    mul_le_mul_of_nonneg_right e1 (by positivity)
  have e0 := mul_le_mul_of_nonneg_left h2k (by positivity : (0 : ℝ) ≤ 4 * K)
  push_cast at e0 e2 ⊢
  nlinarith

/-- The second moment of the coarse chain at step `i` with `2ih ≤ T` (Giles 2015, §8):
`(1 + 2h(3M + 2hM²))ⁱ (1 + x₀)² ≤ (1 + x₀)² e^{(3M + M²T)T}`. -/
lemma coarse_moment_factor_le {h M T : ℝ} (hh0 : 0 ≤ h) (hM : 0 ≤ M) {i : ℕ}
    (hiT : i * (2 * h) ≤ T) (x₀ : ℕ) :
    (1 + 2 * h * (3 * M + 2 * h * M ^ 2)) ^ i * (1 + (x₀ : ℝ)) ^ 2 ≤
      (1 + (x₀ : ℝ)) ^ 2 * Real.exp ((3 * M + M ^ 2 * T) * T) := by
  rw [mul_comm ((1 + (x₀ : ℝ)) ^ 2)]
  refine mul_le_mul_of_nonneg_right ((one_add_pow_le_exp_mul (by positivity) i).trans
    (Real.exp_le_exp.2 ?_)) (sq_nonneg _)
  have e1 := natCast_mul_mul_le_sq (by positivity : (0 : ℝ) ≤ 2 * h) hiT
  have e2 : (i : ℝ) * (2 * h) * (2 * h) * M ^ 2 ≤ T * T * M ^ 2 :=
    mul_le_mul_of_nonneg_right e1 (sq_nonneg M)
  have e0 := mul_le_mul_of_nonneg_left hiT (by positivity : (0 : ℝ) ≤ 3 * M)
  nlinarith

end Coupled

/-- **The coupled fine and coarse paths are `O(h)` apart in mean square, for an unbounded
Lipschitz propensity** (Giles 2015, §8, p. 56, ll. 2407–2410: the Poisson coupling "leads to a very
effective multilevel algorithm with a correction variance which is `O(h)`", after Anderson and
Higham 2012).  Let `K ≥ 0`, `a ≥ 0`, a final time `T ≥ 0` and the initial state `x₀` be given.
There is `c ≥ 0` (depending only on `K`, `a`, `T`, `x₀`) such that for every `K`-Lipschitz
propensity `λ` with `λ(0) ≤ a` — unbounded ones such as `λ(x) = Kx` included — every time step
`h` and every number `k` of coarse steps with `2kh ≤ T`, the coupled paths from `x₀` satisfy
`E[(x_{2k} − x^c_{2k})²] ≤ c h`, the difference being square integrable.  Unlike
`coupledChain_sq_le`, no bound `λ ≤ Λ` and no restriction `h ≤ 1` is needed; the constant is
exponential in `T`. -/
theorem coupledChain_sq_le_lipschitz (K a : ℝ≥0) {T : ℝ} (hT : 0 ≤ T) (x₀ : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ lam : ℕ → ℝ≥0,
      (∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) → lam 0 ≤ a →
      ∀ (h : ℝ≥0) (k : ℕ), 2 * k * (h : ℝ) ≤ T →
        MemLp (fun q : ℕ × ℕ => (q.1 : ℝ) - q.2) 2 (coupledChain lam h x₀ k) ∧
          ∫ q, ((q.1 : ℝ) - q.2) ^ 2 ∂(coupledChain lam h x₀ k) ≤ c * h := by
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (a : ℝ) + K := ⟨_, rfl⟩
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  have hM : 0 ≤ M := by
    rw [hMdef]
    positivity
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = ((K : ℝ) + 2 * T * (K : ℝ) ^ 2) * (M + T * M ^ 2) + K * M :=
    ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = (1 + (x₀ : ℝ)) ^ 2 * Real.exp ((3 * M + M ^ 2 * T) * T) :=
    ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (T * (4 * (K : ℝ) + 2 * T * (K : ℝ) ^ 2)) :=
    ⟨_, rfl⟩
  have hG : 0 ≤ G := by
    rw [hGdef]
    have : 0 ≤ (K : ℝ) + 2 * T * (K : ℝ) ^ 2 := by positivity
    have : 0 ≤ M + T * M ^ 2 := by positivity
    positivity
  have hS : 0 ≤ S := by
    rw [hSdef]
    positivity
  have hE : 0 ≤ E := by
    rw [hEdef]
    positivity
  refine ⟨G * S * E * T, by positivity, fun lam hK ha h k hkT => ?_⟩
  have hh0 : (0 : ℝ) ≤ h := h.coe_nonneg
  have hl : ∀ x, (lam x : ℝ) ≤ M * (1 + x) := fun x => by
    refine (le_mul_one_add_of_lipschitz hK x).trans (mul_le_mul_of_nonneg_right ?_
      (by positivity))
    rw [hMdef]
    exact add_le_add (by exact_mod_cast ha) le_rfl
  have hκ : 0 ≤ (h : ℝ) * K := mul_nonneg hh0 hK0
  have hr : ∀ x y : ℕ, |((h * lam x : ℝ≥0) : ℝ) - ((h * lam y : ℝ≥0) : ℝ)| ≤
      (h : ℝ) * K * |(x : ℝ) - y| := by
    intro x y
    rw [NNReal.coe_mul, NNReal.coe_mul, ← mul_sub, abs_mul, NNReal.abs_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK x y) hh0
  -- the defect of one coarse step, at the coarse state, is `O(h²)` in mean
  have hg : ∀ i < k, ∫⁻ s, ENNReal.ofReal (((h : ℝ) * K + 2 * ((h : ℝ) * K) ^ 2) *
      (((h * lam s.2 : ℝ≥0) : ℝ) + ((h * lam s.2 : ℝ≥0) : ℝ) ^ 2) +
        (h : ℝ) * K * ((h * lam s.2 : ℝ≥0) : ℝ)) ∂(coupledChain lam h x₀ i) ≤
      ENNReal.ofReal ((h : ℝ) ^ 2 * G * S) := by
    intro i hi
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_lt_of_lt hi)
    have hhT : (h : ℝ) ≤ T := by nlinarith
    have hiT : (i : ℝ) * (2 * h) ≤ T := by
      have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
      nlinarith
    have hpt : ∀ y : ℕ, ((h : ℝ) * K + 2 * ((h : ℝ) * K) ^ 2) *
        (((h * lam y : ℝ≥0) : ℝ) + ((h * lam y : ℝ≥0) : ℝ) ^ 2) +
          (h : ℝ) * K * ((h * lam y : ℝ≥0) : ℝ) ≤ (h : ℝ) ^ 2 * G * (1 + (y : ℝ)) ^ 2 := by
      intro y
      rw [hGdef]
      refine coupled_defect_le hh0 hK0 hM hhT ?_ (NNReal.coe_nonneg _) ?_
      · linarith [(Nat.cast_nonneg y : (0 : ℝ) ≤ y)]
      · rw [NNReal.coe_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hl y) hh0
    -- the coarse marginal is the coarse chain, whose second moment is bounded
    have hmap := lintegral_map (μ := coupledChain lam h x₀ i)
      (f := fun y : ℕ => ENNReal.ofReal (((h : ℝ) * K + 2 * ((h : ℝ) * K) ^ 2) *
        (((h * lam y : ℝ≥0) : ℝ) + ((h * lam y : ℝ≥0) : ℝ) ^ 2) +
          (h : ℝ) * K * ((h * lam y : ℝ≥0) : ℝ)))
      Measurable.of_discrete measurable_snd
    rw [coupledChain_snd] at hmap
    have hmom := lintegral_sq_tauChain_le_linear hM hl (2 * h) x₀ i
    have hq : (1 + ((2 * h : ℝ≥0) : ℝ) * (3 * M + ((2 * h : ℝ≥0) : ℝ) * M ^ 2)) ^ i *
        (1 + (x₀ : ℝ)) ^ 2 ≤ S := by
      rw [hSdef, NNReal.coe_mul, NNReal.coe_ofNat]
      exact coarse_moment_factor_le hh0 hM hiT x₀
    refine hmap.symm.le.trans ?_
    calc ∫⁻ y, ENNReal.ofReal (((h : ℝ) * K + 2 * ((h : ℝ) * K) ^ 2) *
          (((h * lam y : ℝ≥0) : ℝ) + ((h * lam y : ℝ≥0) : ℝ) ^ 2) +
            (h : ℝ) * K * ((h * lam y : ℝ≥0) : ℝ)) ∂(tauChain lam (2 * h) x₀ i)
        ≤ ∫⁻ y, ENNReal.ofReal ((h : ℝ) ^ 2 * G) * ENNReal.ofReal ((1 + (y : ℝ)) ^ 2)
            ∂(tauChain lam (2 * h) x₀ i) :=
          lintegral_mono fun y => by
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (hpt y)
      _ = ENNReal.ofReal ((h : ℝ) ^ 2 * G) *
            ∫⁻ y, ENNReal.ofReal ((1 + (y : ℝ)) ^ 2) ∂(tauChain lam (2 * h) x₀ i) :=
          lintegral_const_mul _ Measurable.of_discrete
      _ ≤ ENNReal.ofReal ((h : ℝ) ^ 2 * G) * ENNReal.ofReal S := by
          gcongr
          exact hmom.trans (ENNReal.ofReal_le_ofReal hq)
      _ = ENNReal.ofReal ((h : ℝ) ^ 2 * G * S) := (ENNReal.ofReal_mul (by positivity)).symm
  have hl2 := lintegral_sq_coupledChain_le_rate hκ hr (by positivity) x₀ k hg
  -- `h² G S ∑_{i<k} Aⁱ ≤ c h`: `∑_{i<k} Aⁱ ≤ k Aᵏ` and `Aᵏ ≤ E`
  have hA1 : (1 : ℝ) ≤ (1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2 :=
    one_le_pow₀ (by nlinarith)
  have hsum : ∑ i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ i ≤
      k * ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ k := by
    calc ∑ i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ i
        ≤ ∑ _i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ k :=
          Finset.sum_le_sum fun i hi => pow_le_pow_right₀ hA1 (Finset.mem_range.1 hi).le
      _ = k * ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ k := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hAk : ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ k ≤ E := by
    rw [hEdef]
    exact coupled_growth_le hh0 hK0 hkT
  have hkh : (k : ℝ) * h ≤ T := by
    have := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hh0
    linarith
  have hbound : (h : ℝ) ^ 2 * G * S *
      ∑ i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ i ≤
      G * S * E * T * h := by
    calc (h : ℝ) ^ 2 * G * S *
          ∑ i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ i
        ≤ (h : ℝ) ^ 2 * G * S * (k * E) :=
          mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hAk
            (Nat.cast_nonneg k))) (by positivity)
      _ = G * S * E * ((k : ℝ) * h) * h := by ring
      _ ≤ G * S * E * T * h := by gcongr
  obtain ⟨hi, hb⟩ := integral_le_of_lintegral_ofReal_le (fun q => sq_nonneg _) (by positivity)
    (hl2.trans (ENNReal.ofReal_le_ofReal hbound))
  exact ⟨(memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable).2 hi, hb⟩

/-- **The correction variance of tau-leaping MLMC is `O(h)` for an unbounded Lipschitz
propensity** (Giles 2015, §8, p. 56, ll. 2407–2410: "a very effective multilevel algorithm with a
correction variance which is `O(h)`").  Let `K, a ≥ 0`, a final time `T ≥ 0`, the initial state
`x₀` and `L_Φ` be given.  There is `c ≥ 0`, depending only on `K`, `a`, `T`, `x₀` and `L_Φ`, such
that for every `K`-Lipschitz propensity `λ` with `λ(0) ≤ a` (e.g. `λ(x) = Kx`), every
`L_Φ`-Lipschitz payoff `Φ`, every time step `h` and every number `k` of coarse steps with
`2kh ≤ T`, the correction `Φ(x_{2k}) − Φ(x^c_{2k})` of the coupled paths is square integrable,
`E[(Φ(x_{2k}) − Φ(x^c_{2k}))²] ≤ c h`, and its variance is at most `c h`. -/
theorem variance_coupledChain_le_lipschitz (K a : ℝ≥0) {T : ℝ} (hT : 0 ≤ T) (x₀ : ℕ) (LΦ : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ lam : ℕ → ℝ≥0,
      (∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) → lam 0 ≤ a →
      ∀ Φ : ℕ → ℝ, (∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) →
      ∀ (h : ℝ≥0) (k : ℕ), 2 * k * (h : ℝ) ≤ T →
        MemLp (fun q : ℕ × ℕ => Φ q.1 - Φ q.2) 2 (coupledChain lam h x₀ k) ∧
          ∫ q, (Φ q.1 - Φ q.2) ^ 2 ∂(coupledChain lam h x₀ k) ≤ c * h ∧
          variance (fun q : ℕ × ℕ => Φ q.1 - Φ q.2) (coupledChain lam h x₀ k) ≤ c * h := by
  obtain ⟨c, hc, hbd⟩ := coupledChain_sq_le_lipschitz K a hT x₀
  refine ⟨LΦ ^ 2 * c, by positivity, fun lam hK ha Φ hΦ h k hkT => ?_⟩
  obtain ⟨hmem, hle⟩ := hbd lam hK ha h k hkT
  have hint := hmem.integrable_sq
  have : IsProbabilityMeasure (coupledChain lam h x₀ k) := ⟨coupledChain_univ lam h x₀ k⟩
  have hpt : ∀ q : ℕ × ℕ, (Φ q.1 - Φ q.2) ^ 2 ≤ LΦ ^ 2 * ((q.1 : ℝ) - q.2) ^ 2 := fun q => by
    calc (Φ q.1 - Φ q.2) ^ 2 = |Φ q.1 - Φ q.2| ^ 2 := (sq_abs _).symm
      _ ≤ (LΦ * |(q.1 : ℝ) - q.2|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hΦ q.1 q.2) 2
      _ = LΦ ^ 2 * ((q.1 : ℝ) - q.2) ^ 2 := by rw [mul_pow, sq_abs]
  have hm : AEStronglyMeasurable (fun q : ℕ × ℕ => Φ q.1 - Φ q.2) (coupledChain lam h x₀ k) :=
    Measurable.of_discrete.aestronglyMeasurable
  have hsq : ∫ q, (Φ q.1 - Φ q.2) ^ 2 ∂(coupledChain lam h x₀ k) ≤ LΦ ^ 2 * c * h :=
    calc ∫ q, (Φ q.1 - Φ q.2) ^ 2 ∂(coupledChain lam h x₀ k)
        ≤ ∫ q, LΦ ^ 2 * ((q.1 : ℝ) - q.2) ^ 2 ∂(coupledChain lam h x₀ k) :=
          integral_mono_of_nonneg (ae_of_all _ fun q => sq_nonneg _) (hint.const_mul _)
            (ae_of_all _ hpt)
      _ = LΦ ^ 2 * ∫ q, ((q.1 : ℝ) - q.2) ^ 2 ∂(coupledChain lam h x₀ k) :=
          integral_const_mul _ _
      _ ≤ LΦ ^ 2 * (c * h) := mul_le_mul_of_nonneg_left hle (sq_nonneg LΦ)
      _ = LΦ ^ 2 * c * h := by ring
  refine ⟨(memLp_two_iff_integrable_sq hm).2 ((hint.const_mul (LΦ ^ 2)).mono' (hm.pow 2)
    (ae_of_all _ fun q => ?_)), hsq, (variance_le_expectation_sq hm).trans hsq⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hpt q

/-! ### Theorem 1 for tau-leaping MLMC with an unbounded Lipschitz propensity -/

section Theorem1

variable {lam : ℕ → ℝ≥0} {K : ℝ≥0}

/-- **The tau-leaping chain has finite second moments** for a Lipschitz propensity (Giles 2015,
§8): `E[x_n²] < ∞` for every time step and number of steps. -/
lemma lintegral_sq_tauChain_lt_top_of_lipschitz
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (h : ℝ≥0) (x₀ n : ℕ) :
    ∫⁻ x, ENNReal.ofReal ((x : ℝ) ^ 2) ∂(tauChain lam h x₀ n) < ∞ := by
  have hM : (0 : ℝ) ≤ (lam 0 : ℝ) + K := by positivity
  refine lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_)
    ((lintegral_sq_tauChain_le_linear hM (le_mul_one_add_of_lipschitz hK) h x₀ n).trans_lt
      ENNReal.ofReal_lt_top)
  have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  nlinarith

/-- **The payoffs of a level are square integrable** for a Lipschitz propensity and a Lipschitz
payoff (Giles 2015, §8). -/
lemma memLp_tauLevelLaw_of_lipschitz
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {LΦ : ℝ} (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) (ℓ : ℕ) :
    MemLp (fun q : ℕ × ℕ => Φ q.1) 2 (tauLevelLaw lam T x₀ ℓ) ∧
      MemLp (fun q : ℕ × ℕ => Φ q.2) 2 (tauLevelLaw lam T x₀ ℓ) := by
  have hP : ∀ (h : ℝ≥0) (n : ℕ), IsProbabilityMeasure (tauChain lam h x₀ n) :=
    fun h n => isProbabilityMeasure_tauChain lam h x₀ n
  cases ℓ with
  | zero =>
    rw [tauLevelLaw_zero]
    have h := memLp_two_of_lipschitz hΦ (lintegral_sq_tauChain_lt_top_of_lipschitz hK T x₀ 1)
    exact ⟨(memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
        Measurable.of_discrete.aemeasurable).2 h,
      (memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
        Measurable.of_discrete.aemeasurable).2 h⟩
  | succ ℓ =>
    rw [tauLevelLaw_succ]
    constructor
    · have h := memLp_two_of_lipschitz hΦ
        (lintegral_sq_tauChain_lt_top_of_lipschitz hK (T / 2 ^ (ℓ + 1)) x₀ (2 * 2 ^ ℓ))
      rw [← coupledChain_fst] at h
      exact (memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
        measurable_fst.aemeasurable).1 h
    · have h := memLp_two_of_lipschitz hΦ
        (lintegral_sq_tauChain_lt_top_of_lipschitz hK (2 * (T / 2 ^ (ℓ + 1))) x₀ (2 ^ ℓ))
      rw [← coupledChain_snd] at h
      exact (memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
        measurable_snd.aemeasurable).1 h

/-- The fine payoff of every level is square integrable (Giles 2015, §8). -/
lemma memLp_tauFine_of_lipschitz
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {LΦ : ℝ} (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) (ℓ : ℕ) :
    MemLp (tauFine Φ ℓ) 2 (tauInputLaw lam T x₀) :=
  (memLp_tauLevelLaw_of_lipschitz hK T x₀ hΦ ℓ).1.comp_measurePreserving
    (measurePreserving_tauInput lam T x₀ ℓ)

/-- The coarse payoff of every level is square integrable (Giles 2015, §8). -/
lemma memLp_tauCoarse_of_lipschitz
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {LΦ : ℝ} (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) (ℓ : ℕ) :
    MemLp (tauCoarse Φ ℓ) 2 (tauInputLaw lam T x₀) :=
  (memLp_tauLevelLaw_of_lipschitz hK T x₀ hΦ (ℓ + 1)).2.comp_measurePreserving
    (measurePreserving_tauInput lam T x₀ (ℓ + 1))

/-- **`β = 1` on every level for an unbounded Lipschitz propensity** (Giles 2015, §8, p. 56,
ll. 2407–2410: "a correction variance which is `O(h)`").  For a `K`-Lipschitz propensity (not
necessarily bounded, e.g. `λ(x) = Kx`) and an `L_Φ`-Lipschitz payoff, there is `c₂ > 0` such that
the correction of every level `ℓ` is square integrable and has variance at most `c₂ 2^{−ℓ}`.
Unlike `variance_tauCorrection_le`, no bound `λ ≤ Λ` is assumed, and every level `ℓ ≥ 1` obeys
the `O(h)` bound (no restriction `h_ℓ ≤ 1`). -/
theorem variance_tauCorrection_le_lipschitz
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {LΦ : ℝ} (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ ℓ : ℕ,
      MemLp (fineCoarseDiff (tauFine Φ) (tauCoarse Φ) ℓ) 2 (tauInputLaw lam T x₀) ∧
      variance (fineCoarseDiff (tauFine Φ) (tauCoarse Φ) ℓ) (tauInputLaw lam T x₀) ≤
        c₂ * (2 : ℝ) ^ (-(1 * (ℓ : ℝ))) := by
  obtain ⟨c, hc, hbd⟩ := variance_coupledChain_le_lipschitz K (lam 0) T.coe_nonneg x₀ LΦ
  obtain ⟨V₀, hV₀⟩ : ∃ V₀ : ℝ, V₀ =
      variance (fineCoarseDiff (tauFine Φ) (tauCoarse Φ) 0) (tauInputLaw lam T x₀) := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by
    rw [hV₀]
    exact variance_nonneg _ _
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  refine ⟨1 + V₀ + c * T, by positivity, fun ℓ =>
    ⟨memLp_fineCoarseDiff (memLp_tauFine_of_lipschitz hK T x₀ hΦ)
      (memLp_tauCoarse_of_lipschitz hK T x₀ hΦ) ℓ, ?_⟩⟩
  have hpow : (2 : ℝ) ^ (-(1 * (ℓ : ℝ))) = ((2 : ℝ) ^ ℓ)⁻¹ := by
    rw [one_mul, Real.rpow_neg zero_le_two, Real.rpow_natCast]
  rw [hpow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  cases ℓ with
  | zero =>
    rw [← hV₀, pow_zero, mul_one]
    have : 0 ≤ c * T := mul_nonneg hc hT0
    linarith
  | succ k =>
    have hh : ((T / 2 ^ (k + 1) : ℝ≥0) : ℝ) = (T : ℝ) / 2 ^ (k + 1) := by
      rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
    have hkT : 2 * ((2 ^ k : ℕ) : ℝ) * ((T / 2 ^ (k + 1) : ℝ≥0) : ℝ) ≤ T := by
      rw [hh]
      push_cast
      rw [pow_succ', mul_div_cancel₀ _ (by positivity)]
    have hv := (hbd lam hK le_rfl Φ hΦ _ _ hkT).2.2
    rw [← variance_tauCorrection_succ lam T x₀ Φ k, hh] at hv
    have h2 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    have e : c * ((T : ℝ) / 2 ^ (k + 1)) * 2 ^ (k + 1) = c * T := by
      field_simp
    have := mul_le_mul_of_nonneg_right hv h2.le
    nlinarith

/-- **Theorem 1 for tau-leaping MLMC with an unbounded Lipschitz propensity** (Giles 2015, §8,
p. 56, ll. 2407–2410: "a very effective multilevel algorithm with a correction variance which is
`O(h)`, leading to an `O(ε⁻²(log ε)²)` complexity"; Theorem 1 with (2.4), §2.1).  Let the
propensity `λ` be `K`-Lipschitz — not necessarily bounded, e.g. the linear birth rate
`λ(x) = cx` — the payoff `Φ` be `L_Φ`-Lipschitz, and level `ℓ` use the time step `T 2^{−ℓ}`
(`2^ℓ` fine steps, the coarse path coupled by the Poisson coupling).  The samples are independent
inputs of law `tauInputLaw` and a level-`ℓ` sample costs `2^ℓ`.  If the weak error is
`|E[Φ(x^{h_ℓ}_T)] − P| ≤ c₁ 2^{−αℓ}` with `α ≥ ½` (assumed: the weak rate against the exact chain
needs the exact chain with unbounded rates, which is not constructed), then there is `c₄ > 0` such
that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with a square-integrable error, mean
square error `< ε²`, and cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`.  Compared with
`tauLeaping_mlmc_theorem1`, the hypothesis `λ ≤ Λ` is dropped. -/
theorem tauLeaping_mlmc_theorem1_lipschitz
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|)
    (T : ℝ≥0) (x₀ : ℕ) {Φ : ℕ → ℝ} {LΦ : ℝ}
    (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) (P : ℝ) {α c₁ : ℝ} (hα : 1 / 2 ≤ α)
    (hc₁ : 0 < c₁)
    (hweak : ∀ ℓ : ℕ, |∫ x, Φ x ∂(tauChain lam (T / 2 ^ ℓ) x₀ (2 ^ ℓ)) - P| ≤
      c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine Φ) (tauCoarse Φ)) (fun p x => x p) ℓ (N ℓ) x -
              P) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw lam T x₀) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine Φ) (tauCoarse Φ)) (fun p x => x p) ℓ (N ℓ) x -
              P) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw lam T x₀) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) := by
  have hν := isProbabilityMeasure_tauInputLaw lam T x₀
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs (tauInputLaw lam T x₀)
  obtain ⟨c₂, hc₂, hvar⟩ := variance_tauCorrection_le_lipschitz hK T x₀ hΦ
  have h_i : ∀ ℓ : ℕ, |∫ y, tauFine Φ ℓ y - P ∂(tauInputLaw lam T x₀)| ≤
      c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))) := fun ℓ => by
    rw [integral_sub ((memLp_tauFine_of_lipschitz hK T x₀ hΦ ℓ).integrable one_le_two)
      (integrable_const _), integral_const, probReal_univ, one_smul, integral_tauFine]
    exact hweak ℓ
  have h_iv : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ 1 * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, one_mul, Real.rpow_natCast]
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw lam T x₀)
    (ν := tauInputLaw lam T x₀) (fun _ => P) (tauFine Φ) (tauCoarse Φ) (fun p x => x p)
    (fun ℓ _ _ => (2 : ℝ) ^ ℓ) (fun ℓ => (2 : ℝ) ^ ℓ) (α := α) (β := 1) (γ := 1) (c₁ := c₁)
    (c₂ := c₂) (c₃ := 1) (by linarith) one_pos one_pos hc₁ hc₂ one_pos
    (by rw [min_self]; linarith) hω hind (integrable_const _) (measurable_tauFine Φ)
    (measurable_tauCoarse Φ) (memLp_tauFine_of_lipschitz hK T x₀ hΦ)
    (memLp_tauCoarse_of_lipschitz hK T x₀ hΦ)
    (fun ℓ => (integral_tauFine lam T x₀ Φ ℓ).trans (integral_tauCoarse lam T x₀ Φ ℓ).symm)
    (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i (fun ℓ => (hvar ℓ).2)
    h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, ?_, ?_, ?_⟩
  · exact ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω (fun ℓ => (hvar ℓ).1) ℓ (N ℓ)).sub
      (memLp_const _)).integrable_sq
  · rw [integral_const, probReal_univ, one_smul] at hmse
    exact hmse
  · simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
      probReal_univ, one_smul] at hcost
    rw [complexityBound_of_eq rfl ε] at hcost
    exact hcost

end Theorem1

/-! ### The linear birth propensity `λ(x) = cx` -/

section LinearBirth

/-- The linear birth propensity `λ(x) = cx` is `c`-Lipschitz (Giles 2015, §8). -/
lemma lipschitz_linearBirth (c : ℝ≥0) (x y : ℕ) :
    |(((c * (x : ℝ≥0) : ℝ≥0)) : ℝ) - ((c * (y : ℝ≥0) : ℝ≥0) : ℝ)| ≤ c * |(x : ℝ) - y| := by
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast, ← mul_sub, abs_mul,
    NNReal.abs_eq]

/-- **Theorem 1 for tau-leaping MLMC with the linear birth propensity `λ(x) = cx`** (Giles 2015,
§8, p. 56, ll. 2407–2410: "a very effective multilevel algorithm with a correction variance which
is `O(h)`, leading to an `O(ε⁻²(log ε)²)` complexity").  The propensity `λ(x) = cx` (`c ≥ 0`;
unbounded for `c > 0`) is not covered by `tauLeaping_mlmc_theorem1`.  For every
`L_Φ`-Lipschitz payoff `Φ` with weak error `|E[Φ(x^{h_ℓ}_T)] − P| ≤ c₁ 2^{−αℓ}`, `α ≥ ½`
(assumed), the multilevel estimator has a square-integrable error, mean square error `< ε²` and
cost `≤ c₄ ε⁻²(log ε)²` for all `0 < ε < e⁻¹`. -/
theorem tauLeaping_mlmc_linearBirth (c T : ℝ≥0) (x₀ : ℕ) {Φ : ℕ → ℝ} {LΦ : ℝ}
    (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) (P : ℝ) {α c₁ : ℝ} (hα : 1 / 2 ≤ α)
    (hc₁ : 0 < c₁)
    (hweak : ∀ ℓ : ℕ, |∫ x, Φ x ∂(tauChain (fun x : ℕ => c * (x : ℝ≥0)) (T / 2 ^ ℓ) x₀ (2 ^ ℓ)) -
      P| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine Φ) (tauCoarse Φ)) (fun p x => x p) ℓ (N ℓ) x -
              P) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw (fun x : ℕ => c * (x : ℝ≥0)) T x₀) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine Φ) (tauCoarse Φ)) (fun p x => x p) ℓ (N ℓ) x -
              P) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw (fun x : ℕ => c * (x : ℝ≥0)) T x₀) <
            ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) :=
  tauLeaping_mlmc_theorem1_lipschitz (lipschitz_linearBirth c) T x₀ hΦ P hα hc₁ hweak

/-- The mean of one tau-leaping step (Giles 2015, §8, p. 55, l. 2375): `x + P(hλ(x))` is
integrable with mean `x + hλ(x)`. -/
lemma integral_tauStep_natCast (lam : ℕ → ℝ≥0) (h : ℝ≥0) (z : ℕ) :
    Integrable (fun y : ℕ => (y : ℝ)) (tauStep lam h z) ∧
      ∫ y, (y : ℝ) ∂(tauStep lam h z) = z + ((h * lam z : ℝ≥0) : ℝ) := by
  have hl : ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(tauStep lam h z) =
      ENNReal.ofReal ((z : ℝ) + ((h * lam z : ℝ≥0) : ℝ)) := by
    rw [tauStep, lintegral_map Measurable.of_discrete Measurable.of_discrete]
    calc ∫⁻ n, ENNReal.ofReal (((z + n : ℕ) : ℝ)) ∂(poissonMeasure (h * lam z))
        = ∫⁻ n, ENNReal.ofReal ((z : ℝ) + 1 * n + 0 * (n : ℝ) ^ 2)
            ∂(poissonMeasure (h * lam z)) := by
          refine lintegral_congr fun n => ?_
          congr 1
          push_cast
          ring
      _ = ENNReal.ofReal ((z : ℝ) + 1 * ((h * lam z : ℝ≥0) : ℝ) +
            0 * (((h * lam z : ℝ≥0) : ℝ) + ((h * lam z : ℝ≥0) : ℝ) ^ 2)) :=
          lintegral_poly_poissonMeasure _ (Nat.cast_nonneg z) zero_le_one le_rfl
      _ = ENNReal.ofReal ((z : ℝ) + ((h * lam z : ℝ≥0) : ℝ)) := by
          congr 1
          ring
  have hnn : 0 ≤ᵐ[tauStep lam h z] fun y : ℕ => (y : ℝ) := ae_of_all _ fun y => Nat.cast_nonneg y
  refine ⟨(integral_le_of_lintegral_ofReal_le (fun y => Nat.cast_nonneg y) (by positivity)
    hl.le).1, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn Measurable.of_discrete.aestronglyMeasurable, hl,
    ENNReal.toReal_ofReal (by positivity)]

/-- **The mean of the tau-leaping chain for the linear birth propensity** (Giles 2015, §8, p. 55,
l. 2375: "`x_{n+1} = x_n + P(hλ(x_n))`", with `λ(x) = cx`): `x_n` is integrable and
`E[x_n] = x₀ (1 + hc)ⁿ`. -/
theorem integral_tauChain_linearBirth (c h : ℝ≥0) (x₀ : ℕ) (n : ℕ) :
    Integrable (fun x : ℕ => (x : ℝ)) (tauChain (fun x : ℕ => c * (x : ℝ≥0)) h x₀ n) ∧
      ∫ x, (x : ℝ) ∂(tauChain (fun x : ℕ => c * (x : ℝ≥0)) h x₀ n) = x₀ * (1 + h * c) ^ n := by
  refine ⟨?_, ?_⟩
  · have := isProbabilityMeasure_tauChain (fun x : ℕ => c * (x : ℝ≥0)) h x₀ n
    exact (tauChain_moments_linear (a := 0) (b := c) (fun x => by simp) x₀ le_rfl).1.integrable
      one_le_two
  induction n with
  | zero => rw [tauChain, integral_dirac, pow_zero, mul_one]
  | succ n ih =>
      rw [tauChain, integral_bind_of_nonneg_nat (fun y => Nat.cast_nonneg y)
        fun z => (integral_tauStep_natCast _ h z).1]
      calc ∫ z, ∫ y, (y : ℝ) ∂(tauStep (fun x : ℕ => c * (x : ℝ≥0)) h z)
            ∂(tauChain (fun x : ℕ => c * (x : ℝ≥0)) h x₀ n)
          = ∫ z, (1 + (h : ℝ) * c) * (z : ℝ) ∂(tauChain (fun x : ℕ => c * (x : ℝ≥0)) h x₀ n) := by
            refine integral_congr_ae (ae_of_all _ fun z => ?_)
            dsimp only
            rw [(integral_tauStep_natCast _ h z).2, NNReal.coe_mul, NNReal.coe_mul,
              NNReal.coe_natCast]
            ring
        _ = (1 + (h : ℝ) * c) * ∫ z, (z : ℝ) ∂(tauChain (fun x : ℕ => c * (x : ℝ≥0)) h x₀ n) :=
            integral_const_mul _ _
        _ = x₀ * (1 + h * c) ^ (n + 1) := by
            rw [ih]
            ring

/-- `eᵘ − 1 − u ≤ u² eᵘ` for `u ≥ 0` (from `e^{−u} ≥ 1 − u`; used in Giles 2015, §8). -/
lemma exp_sub_one_sub_le_sq_mul_exp {u : ℝ} (hu : 0 ≤ u) :
    Real.exp u - 1 - u ≤ u ^ 2 * Real.exp u := by
  have h1 := Real.add_one_le_exp (-u)
  have h2 : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 + u) * Real.exp u)
  nlinarith [h2, h3]

/-- `aⁿ − bⁿ ≤ n δ aⁿ` for `0 ≤ b ≤ a` with `a − b ≤ δ a` (used in Giles 2015, §8). -/
lemma pow_sub_pow_le_of_sub_le {a b δ : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (hδ : a - b ≤ δ * a) :
    ∀ n : ℕ, a ^ n - b ^ n ≤ n * δ * a ^ n
  | 0 => by simp
  | n + 1 => by
      have ha : 0 ≤ a := hb.trans hba
      have ih := pow_sub_pow_le_of_sub_le hb hba hδ n
      have e1 := mul_le_mul_of_nonneg_left ih ha
      have e2 : b ^ n * (a - b) ≤ a ^ n * (δ * a) :=
        mul_le_mul (pow_le_pow_left₀ hb hba n) hδ (by linarith) (pow_nonneg ha n)
      have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
      have e' : ((n + 1 : ℕ) : ℝ) * δ * a ^ (n + 1) =
          a * (n * δ * a ^ n) + a ^ n * (δ * a) := by
        push_cast
        ring
      rw [e, e']
      linarith [e1, e2]

/-- **The weak error of tau-leaping for the linear birth propensity** (Giles 2015, §8, p. 55,
ll. 2372–2376: the "'tau-leaping' method … gives the discrete equation
`x_{n+1} = x_n + P(hλ(x_n))`", here with `λ(x) = cx` and the payoff `Φ(x) = x`): with `N ≥ 1`
steps of size `T/N`,
`|E[x_N] − x₀ e^{cT}| ≤ x₀ (cT)² e^{cT} / N`.  Here `x₀ e^{cT} = lim_{N→∞} E[x_N]` (it is also the
mean of the exact linear birth process, which is not formalised): weak order `α = 1`. -/
theorem tauLeaping_linearBirth_weak_error (c T : ℝ≥0) (x₀ : ℕ) {N : ℕ} (hN : 0 < N) :
    |∫ x, (x : ℝ) ∂(tauChain (fun x : ℕ => c * (x : ℝ≥0)) (T / N) x₀ N) -
        x₀ * Real.exp (c * T)| ≤ x₀ * ((c : ℝ) * T) ^ 2 * Real.exp (c * T) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (c : ℝ) * T / N := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hstep : ((T / (N : ℝ≥0) : ℝ≥0) : ℝ) * c = u := by
    rw [hu, NNReal.coe_div, NNReal.coe_natCast]
    ring
  have hNu : (N : ℝ) * u = c * T := by
    rw [hu]
    field_simp
  rw [(integral_tauChain_linearBirth _ _ _ _).2, hstep]
  have hb : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hδ : Real.exp u - (1 + u) ≤ u ^ 2 * Real.exp u := by
    linarith [exp_sub_one_sub_le_sq_mul_exp hu0]
  have hpow := pow_sub_pow_le_of_sub_le (by linarith) hb hδ N
  have haN : Real.exp u ^ N = Real.exp (c * T) := by
    rw [← Real.exp_nat_mul, hNu]
  rw [haN] at hpow
  have hbN : (1 + u) ^ N ≤ Real.exp (c * T) := by
    rw [← haN]
    exact pow_le_pow_left₀ (by linarith) hb N
  have hx₀ : (0 : ℝ) ≤ x₀ := Nat.cast_nonneg x₀
  rw [abs_sub_comm, ← mul_sub, abs_mul, Nat.abs_cast,
    abs_of_nonneg (sub_nonneg.2 hbN)]
  have e : (N : ℝ) * u ^ 2 * Real.exp (c * T) = ((c : ℝ) * T) ^ 2 * Real.exp (c * T) / N := by
    rw [hu]
    field_simp
  rw [e] at hpow
  calc (x₀ : ℝ) * (Real.exp (c * T) - (1 + u) ^ N)
      ≤ x₀ * (((c : ℝ) * T) ^ 2 * Real.exp (c * T) / N) := mul_le_mul_of_nonneg_left hpow hx₀
    _ = x₀ * ((c : ℝ) * T) ^ 2 * Real.exp (c * T) / N := by ring

/-- **Theorem 1 for tau-leaping MLMC, end to end, for the linear birth propensity** (Giles 2015, §8,
p. 56, ll. 2407–2410: "a very effective multilevel algorithm with a correction variance which is
`O(h)`, leading to an `O(ε⁻²(log ε)²)` complexity").  One reaction `x → x + 1` with the
unbounded propensity `λ(x) = cx`, initial state `x₀`, final time `T`, payoff `Φ(x) = x`, and the
target `x₀ e^{cT}` (the limit of the tau-leaping means).  Nothing is assumed: the weak rate
`α = 1` is `tauLeaping_linearBirth_weak_error`, `β = 1` is `variance_tauCorrection_le_lipschitz`,
`γ = 1`.  There is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with a
square-integrable error, mean square error `< ε²` and cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`. -/
theorem tauLeaping_mlmc_linearBirth_mean (c T : ℝ≥0) (x₀ : ℕ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine fun x : ℕ => (x : ℝ))
              (tauCoarse fun x : ℕ => (x : ℝ))) (fun p x => x p) ℓ (N ℓ) x -
              x₀ * Real.exp (c * T)) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw (fun x : ℕ => c * (x : ℝ≥0)) T x₀) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine fun x : ℕ => (x : ℝ))
              (tauCoarse fun x : ℕ => (x : ℝ))) (fun p x => x p) ℓ (N ℓ) x -
              x₀ * Real.exp (c * T)) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw (fun x : ℕ => c * (x : ℝ≥0)) T x₀) <
            ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) := by
  have hΦ : ∀ x y : ℕ, |(x : ℝ) - (y : ℝ)| ≤ 1 * |(x : ℝ) - y| := fun x y => by rw [one_mul]
  have hc₁ : 0 < 1 + (x₀ : ℝ) * ((c : ℝ) * T) ^ 2 * Real.exp (c * T) := by positivity
  refine tauLeaping_mlmc_linearBirth c T x₀ hΦ (x₀ * Real.exp (c * T)) (α := 1)
    (by norm_num) hc₁ fun ℓ => ?_
  have hN : ((2 ^ ℓ : ℕ) : ℝ≥0) = 2 ^ ℓ := by push_cast; rfl
  have hw := tauLeaping_linearBirth_weak_error c T x₀ (N := 2 ^ ℓ) (by positivity)
  rw [hN] at hw
  have hpow : (2 : ℝ) ^ (-(1 * (ℓ : ℝ))) = ((2 : ℝ) ^ ℓ)⁻¹ := by
    rw [one_mul, Real.rpow_neg zero_le_two, Real.rpow_natCast]
  rw [hpow, ← div_eq_mul_inv]
  refine hw.trans ?_
  push_cast
  gcongr
  linarith

end LinearBirth

end MLMC
