import MlmcLean.EulerMaruyama
import MlmcLean.NestedSimulation
import MlmcLean.ErrorAnalysis
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The SDE applications of Giles 2015, §5: the parts that do not need SDE theory

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5 "SDEs"
(pp. 29–46).  The convergence orders of the discretisations (strong order `½` of Euler–Maruyama,
order `1` of Milstein, the Brownian-bridge results) are SDE theory and are not formalised; what is
formalised here is every step of the section that follows from them by probability or algebra.

* **§5.1** (`timestep_rate`): with `h_ℓ = h₀ 2^{−kℓ}` a bound `c h_ℓ^q` decays at the rate `kq` and
  the cost `1/h_ℓ` grows at the rate `k` — "if `h_ℓ = 4^{−ℓ}h₀` … `α = 2`, `β = 2` and `γ = 2`
  … if `h_ℓ = 2^{−ℓ}h₀` … `α = 1`, `β = 1` and `γ = 1`" for the weak order `1` and `V_ℓ = O(h_ℓ)`;
  `kurtosis_const_mul`: the kurtosis of the digital option's `P_ℓ − P_{ℓ−1} = ±10e^{−rT}` is that of
  `±1`; `digital_em_complexity`: "`α = 1`, `β = ½`, `γ = 1`, leading to the MLMC complexity being
  `O(ε^{−2.5})`".
* **§5.2** (`milstein_complexity`): `(1, 2, 1)` and `(1, 3/2, 1)` give `O(ε⁻²)`;
  `integral_condExp_eq_of_map_eq`: "It is very important in this conditional expectation
  formulation that `E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]`" — conditional expectations of the payoff of two
  terminal values with the same law have the same mean, so (2.4) holds;
  `bridgeInterp_midpoint`: the coarse Brownian-bridge interpolant at the fine time `t_n + h`.
* **§5.2, splitting** (`splitting_mean_variance`): averaging `M` sub-samples of the final
  increment in place of the conditional expectation gives the same mean and adds the variance
  `E[v]/M`, `v` the conditional variance.
* **§5.3** (`measurePreserving_swapIncrements`): the antithetic path, whose fine Brownian
  increments are swapped within each coarse step, has the law of the original path, so
  `giles_theorem1_antithetic` applies; `abs_antithetic_le`, `variance_antithetic_le`: "the
  average of the fine and antithetic paths is within `O(h)` of the coarse path, and hence the
  multilevel variance is `O(h²)` for smooth payoffs".
* **§5.6** (`emMeanRevert_iterate`, `emMeanRevert_bounded`, `emMeanRevert_unbounded`): for a
  mean-reverting drift `(θ − S)/τ` the explicit Euler step is stable if and only if `h ≤ 2τ`: "the
  timestep `h₀` on the coarsest level cannot be much larger than `τ` without encountering severe
  numerical stability problems".
* **§5.7** (`abs_smoothCDF_sub_le`, `tendsto_smoothCDF`): the smoothed CDF
  `C_δ(x) = E[g((x − P)/δ)]` differs from `C(x) = P(P < x)` by at most `P(|P − x| ≤ δ)`, and
  "as `δ → 0` … the accuracy improves": `C_δ(x) → C(x)` when `P` has no atom at `x`;
  `tendsto_density`: "the density `ρ(x)` of the scalar output `P` is given by
  `ρ(x) = lim_{δ→0} E[δ⁻¹ g((x − P)/δ)]`" when the density is continuous at `x`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace MLMC

/-! ### §5.1: the rates from the timestep -/

/-- **Giles 2015, §5.1: the rates from the timestep.**  With `h_ℓ = h₀ 2^{−kℓ}`, a bound
`c h_ℓ^q` is `c h₀^q 2^{−kqℓ}` (rate `kq`), and the cost `1/h_ℓ = h₀⁻¹ 2^{kℓ}` grows at rate `k`.
For Euler–Maruyama (weak order `1`, `V_ℓ = O(h_ℓ)`, cost `∝ h_ℓ⁻¹`) this gives
`α = β = γ = k`: `k = 2` for `h_ℓ = 4^{−ℓ}h₀` and `k = 1` for `h_ℓ = 2^{−ℓ}h₀`. -/
theorem timestep_rate {h₀ : ℝ} (hh₀ : 0 < h₀) (k q : ℝ) (ℓ : ℕ) :
    (h₀ * (2 : ℝ) ^ (-(k * ℓ))) ^ q = h₀ ^ q * (2 : ℝ) ^ (-(k * q * ℓ)) ∧
      (h₀ * (2 : ℝ) ^ (-(k * ℓ)))⁻¹ = h₀⁻¹ * (2 : ℝ) ^ (k * ℓ) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [Real.mul_rpow hh₀.le (Real.rpow_nonneg h2 _), ← Real.rpow_mul h2]
    congr 2
    ring
  · rw [mul_inv, ← Real.rpow_neg h2, neg_neg]

/-- **The kurtosis does not depend on the scale** (Giles 2015, §5.1: for the digital option with
payoff `10 e^{−rT} H(S_T − K)`, `P_ℓ − P_{ℓ−1} = ±10 e^{−rT}` or `0`, and its kurtosis is that of
the `{−1, 0, 1}`-valued correction, `kurtosis_of_ternary`). -/
theorem kurtosis_const_mul {Ω₀ : Type*} [MeasurableSpace Ω₀] (X : Ω₀ → ℝ) (ν : Measure Ω₀)
    {c : ℝ} (hc : c ≠ 0) : kurtosis (fun y => c * X y) ν = kurtosis X ν := by
  unfold kurtosis
  simp only [mul_pow, integral_const_mul]
  rw [show (c ^ 2) ^ 2 = c ^ 4 by ring, mul_div_mul_left _ _ (pow_ne_zero 4 hc)]

/-- **Giles 2015, §5.1, the digital option with Euler–Maruyama**: "`α = 1`, `β = ½`, `γ = 1`,
leading to the MLMC complexity being `O(ε^{−2.5})`". -/
theorem digital_em_complexity (ε : ℝ) : complexityBound 1 (1 / 2) 1 ε = ε ^ (-(5 / 2 : ℝ)) := by
  rw [complexityBound_of_gt (by norm_num)]
  norm_num

/-- **Giles 2015, §5.2**: the Milstein discretisation, "`α = 1`, `β = 2`, `γ = 1`", and the
conditional expectation treatment of the digital option (and the barrier options, §5.2, and the
exit times of Primozic, §5.5), "`α = 1`, `β = 3/2` and `γ = 1`.  Since `β > γ`, the MLMC complexity
is `O(ε⁻²)`". -/
theorem milstein_complexity (ε : ℝ) :
    complexityBound 1 2 1 ε = ε ^ (-2 : ℝ) ∧ complexityBound 1 (3 / 2) 1 ε = ε ^ (-2 : ℝ) :=
  ⟨complexityBound_of_lt (by norm_num) ε, complexityBound_of_lt (by norm_num) ε⟩

/-! ### §5.2: conditional expectations and the Brownian-bridge interpolant -/

/-- **Giles 2015, §5.2: "It is very important in this conditional expectation formulation that
`E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` … This ensures that the identity in Equation (2.4) is respected"**.
If the fine payoff on level `ℓ − 1` is `E[g(S) | 𝓕]` and the coarse payoff on level `ℓ` is
`E[g(S') | 𝓖]`, and the terminal values `S`, `S'` have the same law, then the two payoffs have the
same mean `E[g(S)]`. -/
theorem integral_condExp_eq_of_map_eq {Ω α : Type*} {m m' m₀ : MeasurableSpace Ω}
    [MeasurableSpace α] {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ m₀) (hm' : m' ≤ m₀)
    {S S' : Ω → α} (hS : Measurable S) (hS' : Measurable S') (hlaw : μ.map S = μ.map S')
    {g : α → ℝ} (hg : StronglyMeasurable g) :
    ∫ ω, (μ[g ∘ S | m]) ω ∂μ = ∫ ω, (μ[g ∘ S' | m']) ω ∂μ := by
  rw [integral_condExp hm, integral_condExp hm']
  change ∫ ω, g (S ω) ∂μ = ∫ ω, g (S' ω) ∂μ
  rw [← integral_map hS.aemeasurable hg.aestronglyMeasurable, hlaw,
    integral_map hS'.aemeasurable hg.aestronglyMeasurable]

/-- The Brownian-bridge interpolant of Giles 2015, §5.2 on a timestep `[t_n, t_n + H]`:
`Ŝ(t) = Ŝ_n + λ(Ŝ_{n+1} − Ŝ_n) + b_n (W(t) − W_n − λ(W_{n+1} − W_n))` with `λ = (t − t_n)/H`. -/
def bridgeInterp (S₀ S₁ b W₀ W₁ Wt lam : ℝ) : ℝ :=
  S₀ + lam * (S₁ - S₀) + b * (Wt - W₀ - lam * (W₁ - W₀))

/-- **Giles 2015, §5.2: the coarse interpolant at the fine time** `t_n + h`: on the coarse step
`[t_n, t_n + 2h]`, `λ = ½` and
`Ŝ^c(t_{n+1}) = ½(Ŝ^c_n + Ŝ^c_{n+2}) + ½ b^c_n((W_{n+1} − W_n) − (W_{n+2} − W_{n+1}))`, "using the
Brownian increments `W_{n+1} − W_n` and `W_{n+2} − W_{n+1}` already generated for the fine path". -/
theorem bridgeInterp_midpoint (Sn Sn2 b Wn Wn1 Wn2 : ℝ) :
    bridgeInterp Sn Sn2 b Wn Wn2 Wn1 (1 / 2) =
      1 / 2 * (Sn + Sn2) + 1 / 2 * b * ((Wn1 - Wn) - (Wn2 - Wn1)) := by
  unfold bridgeInterp
  ring

/-! ### §5.3: the antithetic estimator -/

/-- The permutation `2k ↔ 2k + 1` of the fine timesteps: within each coarse timestep the two fine
increments are exchanged (Giles 2015, §5.3). -/
def pairSwap (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

lemma pairSwap_involutive : Function.Involutive pairSwap := by
  intro i
  unfold pairSwap
  split_ifs <;> omega

/-- The antithetic increments: `z ↦ (z_{pairSwap i})_i`. -/
def swapIncrements (z : ℕ → ℝ) : ℕ → ℝ := fun i => z (pairSwap i)

/-- **The antithetic path has the law of the original path** (Giles 2015, §5.3: "`ωᵃ` is an
antithetic counterpart defined by a time-reversal of the Brownian path within each coarse timestep.
This results in the Brownian increments for the antithetic fine path being swapped relative to the
original path"): exchanging the two fine increments within each coarse step preserves the law of
independent identically distributed increments, for instance `N(0,1)^{⊗ℕ}`.  This is the hypothesis
`ha` of `giles_theorem1_antithetic`. -/
theorem measurePreserving_swapIncrements (P : Measure ℝ) [IsProbabilityMeasure P] :
    MeasurePreserving swapIncrements (Measure.infinitePi fun _ : ℕ => P)
      (Measure.infinitePi fun _ : ℕ => P) :=
  ⟨measurable_pi_lambda _ fun _ => measurable_pi_apply _,
    Measure.map_infinitePi_infinitePi_of_inj pairSwap_involutive.injective⟩

/-- **Giles 2015, §5.3, pointwise**: for `f` with a `K`-Lipschitz derivative (for instance
`|f″| ≤ K`), the antithetic correction of a smooth payoff is controlled by the distance of the
average of the fine and antithetic values `a`, `b` from the coarse value `c` and by the squared
distances: `|½(f(a) + f(b)) − f(c)| ≤ |f′(c)| |½(a + b) − c| + (K/4)((a − c)² + (b − c)²)`. -/
theorem abs_antithetic_le {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) (a b c : ℝ) :
    |(f a + f b) / 2 - f c| ≤
      |f' c| * |(a + b) / 2 - c| + K / 4 * ((a - c) ^ 2 + (b - c) ^ 2) := by
  have ha := abs_taylor_first_le hf hf' c a
  have hb := abs_taylor_first_le hf hf' c b
  have e : (f a + f b) / 2 - f c = (f a - f c - f' c * (a - c)) / 2 +
      (f b - f c - f' c * (b - c)) / 2 + f' c * ((a + b) / 2 - c) := by ring
  rw [e]
  calc |(f a - f c - f' c * (a - c)) / 2 + (f b - f c - f' c * (b - c)) / 2 +
        f' c * ((a + b) / 2 - c)|
      ≤ |(f a - f c - f' c * (a - c)) / 2| + |(f b - f c - f' c * (b - c)) / 2| +
          |f' c * ((a + b) / 2 - c)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |f a - f c - f' c * (a - c)| / 2 + |f b - f c - f' c * (b - c)| / 2 +
          |f' c| * |(a + b) / 2 - c| := by
        rw [abs_div, abs_div, abs_two, abs_mul]
    _ ≤ K / 2 * (a - c) ^ 2 / 2 + K / 2 * (b - c) ^ 2 / 2 + |f' c| * |(a + b) / 2 - c| :=
        add_le_add (add_le_add (div_le_div_of_nonneg_right ha zero_le_two)
          (div_le_div_of_nonneg_right hb zero_le_two)) le_rfl
    _ = |f' c| * |(a + b) / 2 - c| + K / 4 * ((a - c) ^ 2 + (b - c) ^ 2) := by ring

/-- `|Y| ≤ a + κ(s + t)` gives `Y² ≤ 2a² + 4κ²(s² + t²)`. -/
lemma sq_le_of_abs_le_add {Y a κ s t : ℝ} (h : |Y| ≤ a + κ * (s + t)) :
    Y ^ 2 ≤ 2 * a ^ 2 + 4 * κ ^ 2 * (s ^ 2 + t ^ 2) := by
  have h1 : Y ^ 2 ≤ (a + κ * (s + t)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [sq_nonneg (a - κ * (s + t)), mul_nonneg (sq_nonneg κ) (sq_nonneg (s - t))]

/-- **Giles 2015, §5.3: "the average of the fine and antithetic paths is within `O(h)` of the coarse
path, and hence the multilevel variance is `O(h²)` for smooth payoffs"**.  Let `A`, `B` be the fine
and antithetic terminal values and `C` the coarse one, and let `f` have `|f′| ≤ L` and a
`K`-Lipschitz derivative.  If `E[(½(A + B) − C)²] ≤ D₁ h²` and `E[(A − C)⁴], E[(B − C)⁴] ≤ D₂ h²`
(the fourth moments of an `O(h^{1/2})` strong error), then
`V[½(f(A) + f(B)) − f(C)] ≤ (2L²D₁ + K²D₂/2) h²`. -/
theorem variance_antithetic_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f f' : ℝ → ℝ} {K L D₁ D₂ h : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) (hL : ∀ x, |f' x| ≤ L)
    {A B C : Ω → ℝ} (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    (hi1 : Integrable (fun ω => ((A ω + B ω) / 2 - C ω) ^ 2) μ)
    (hi2 : Integrable (fun ω => (A ω - C ω) ^ 4) μ) (hi3 : Integrable (fun ω => (B ω - C ω) ^ 4) μ)
    (h1 : ∫ ω, ((A ω + B ω) / 2 - C ω) ^ 2 ∂μ ≤ D₁ * h ^ 2)
    (h2 : ∫ ω, (A ω - C ω) ^ 4 ∂μ ≤ D₂ * h ^ 2) (h3 : ∫ ω, (B ω - C ω) ^ 4 ∂μ ≤ D₂ * h ^ 2) :
    variance (fun ω => (f (A ω) + f (B ω)) / 2 - f (C ω)) μ ≤
      (2 * L ^ 2 * D₁ + K ^ 2 * D₂ / 2) * h ^ 2 := by
  have hfm : Measurable f :=
    (continuous_iff_continuousAt.2 fun x => (hf x).continuousAt).measurable
  have hYm : Measurable fun ω => (f (A ω) + f (B ω)) / 2 - f (C ω) :=
    (((hfm.comp hA).add (hfm.comp hB)).div_const 2).sub (hfm.comp hC)
  -- the pointwise bound on the square
  have hpt : ∀ ω, ((f (A ω) + f (B ω)) / 2 - f (C ω)) ^ 2 ≤
      2 * L ^ 2 * ((A ω + B ω) / 2 - C ω) ^ 2 +
        K ^ 2 / 4 * ((A ω - C ω) ^ 4 + (B ω - C ω) ^ 4) := by
    intro ω
    have h := abs_antithetic_le hf hf' (A ω) (B ω) (C ω)
    have hb : |(f (A ω) + f (B ω)) / 2 - f (C ω)| ≤
        L * |(A ω + B ω) / 2 - C ω| + |K| / 4 * ((A ω - C ω) ^ 2 + (B ω - C ω) ^ 2) := by
      refine h.trans (add_le_add (mul_le_mul_of_nonneg_right (hL _) (abs_nonneg _)) ?_)
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (by positivity)
    refine (sq_le_of_abs_le_add hb).trans_eq ?_
    rw [mul_pow, sq_abs, div_pow, sq_abs]
    ring
  have hi23 : Integrable (fun ω => (A ω - C ω) ^ 4 + (B ω - C ω) ^ 4) μ := hi2.add hi3
  have hbound : Integrable (fun ω => 2 * L ^ 2 * ((A ω + B ω) / 2 - C ω) ^ 2 +
      K ^ 2 / 4 * ((A ω - C ω) ^ 4 + (B ω - C ω) ^ 4)) μ :=
    (hi1.const_mul (2 * L ^ 2)).add (hi23.const_mul (K ^ 2 / 4))
  calc variance (fun ω => (f (A ω) + f (B ω)) / 2 - f (C ω)) μ
      ≤ ∫ ω, ((f (A ω) + f (B ω)) / 2 - f (C ω)) ^ 2 ∂μ :=
        variance_le_expectation_sq hYm.aestronglyMeasurable
    _ ≤ ∫ ω, (2 * L ^ 2 * ((A ω + B ω) / 2 - C ω) ^ 2 +
          K ^ 2 / 4 * ((A ω - C ω) ^ 4 + (B ω - C ω) ^ 4)) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) hbound
          (Eventually.of_forall hpt)
    _ = 2 * L ^ 2 * ∫ ω, ((A ω + B ω) / 2 - C ω) ^ 2 ∂μ +
          K ^ 2 / 4 * (∫ ω, (A ω - C ω) ^ 4 ∂μ + ∫ ω, (B ω - C ω) ^ 4 ∂μ) := by
        rw [integral_add (hi1.const_mul (2 * L ^ 2)) (hi23.const_mul (K ^ 2 / 4)),
          integral_const_mul, integral_const_mul, integral_add hi2 hi3]
    _ ≤ 2 * L ^ 2 * (D₁ * h ^ 2) + K ^ 2 / 4 * (D₂ * h ^ 2 + D₂ * h ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity))
    _ = (2 * L ^ 2 * D₁ + K ^ 2 * D₂ / 2) * h ^ 2 := by ring

/-! ### §5.6: the explicit step for a mean-reverting drift -/

/-- The Euler step `S + (θ − S)/τ · h` for the mean-reverting drift `(θ − S)/τ` of Giles 2015, §5.6
(the drift part of the Euler–Maruyama step). -/
noncomputable def emMeanRevert (θ τ h S : ℝ) : ℝ := S + (θ - S) / τ * h

/-- `n` explicit steps multiply the distance to the mean `θ` by `(1 − h/τ)^n`. -/
theorem emMeanRevert_iterate (θ τ h S : ℝ) (n : ℕ) :
    (emMeanRevert θ τ h)^[n] S - θ = (1 - h / τ) ^ n * (S - θ) := by
  induction n generalizing S with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, emMeanRevert, pow_succ]
    ring

/-- **The explicit step is stable for `h ≤ 2τ`** (Giles 2015, §5.6): for `0 < h ≤ 2τ` the iterates
stay within `|S − θ|` of the mean `θ`. -/
theorem emMeanRevert_bounded {θ τ h : ℝ} (hτ : 0 < τ) (hh : 0 ≤ h) (h2 : h ≤ 2 * τ) (S : ℝ)
    (n : ℕ) : |(emMeanRevert θ τ h)^[n] S - θ| ≤ |S - θ| := by
  rw [emMeanRevert_iterate, abs_mul, abs_pow]
  have hr : |1 - h / τ| ≤ 1 := by
    have h1 : h / τ ≤ 2 := by
      rw [div_le_iff₀ hτ]
      linarith
    have h0 : 0 ≤ h / τ := div_nonneg hh hτ.le
    rw [abs_le]
    constructor <;> linarith
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hr)

/-- **The explicit step is unstable for `h > 2τ`** (Giles 2015, §5.6: "the timestep `h₀` on the
coarsest level cannot be much larger than `τ` without encountering severe numerical stability
problems"): for `h > 2τ` the distance to the mean grows geometrically, `|1 − h/τ| > 1`, from any
starting point `S ≠ θ`. -/
theorem emMeanRevert_unbounded {θ τ h : ℝ} (hτ : 0 < τ) (h2 : 2 * τ < h) {S : ℝ} (hS : S ≠ θ) :
    Tendsto (fun n : ℕ => |(emMeanRevert θ τ h)^[n] S - θ|) atTop atTop := by
  have hr : 1 < |1 - h / τ| := by
    rw [abs_of_neg (by rw [sub_neg, lt_div_iff₀ hτ]; linarith), neg_sub, lt_sub_iff_add_lt,
      lt_div_iff₀ hτ]
    linarith
  have hS0 : 0 < |S - θ| := abs_pos.2 (sub_ne_zero.2 hS)
  simp only [emMeanRevert_iterate, abs_mul, abs_pow]
  exact (tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const hS0

/-! ### §5.7: the smoothed CDF -/

section cdf

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The smoothed CDF of Giles 2015, §5.7: `C_δ(x) = E[g((x − P)/δ)]`. -/
noncomputable def smoothCDF (μ : Measure Ω) (P : Ω → ℝ) (g : ℝ → ℝ) (δ x : ℝ) : ℝ :=
  ∫ ω, g ((x - P ω) / δ) ∂μ

/-- **"As `δ → 0`, `g(x/δ) → H(x)`"** (Giles 2015, §5.7): for `y ≠ 0`, `g(y/δ)` is eventually
`H(y)`, the Heaviside function, as `δ → 0⁺`. -/
theorem smooth_step_eventually {g : ℝ → ℝ} (hg0 : ∀ y < -1, g y = 0) (hg1 : ∀ y > 1, g y = 1)
    {y : ℝ} (hy : y ≠ 0) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), g (y / δ) = if 0 < y then 1 else 0 := by
  have hpos : 0 < |y| := abs_pos.2 hy
  filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
  obtain ⟨hδ0, hδy⟩ := hδ
  rcases lt_or_gt_of_ne hy with hneg | hpos'
  · rw [if_neg (not_lt.2 hneg.le)]
    apply hg0
    rw [abs_of_neg hneg] at hδy
    rw [div_lt_iff₀ hδ0]
    linarith
  · rw [if_pos hpos']
    apply hg1
    rw [abs_of_pos hpos'] at hδy
    rw [gt_iff_lt, lt_div_iff₀ hδ0]
    linarith

/-- **The smoothing error of the CDF** (Giles 2015, §5.7): if `0 ≤ g ≤ 1`, `g = 0` on `(−∞, −1)`
and `g = 1` on `(1, ∞)`, then for `δ > 0` the smoothed CDF `C_δ(x) = E[g((x − P)/δ)]` differs
from the CDF `C(x) = E[1_{P<x}]` by at most `P(|P − x| ≤ δ)`. -/
theorem abs_smoothCDF_sub_le {P : Ω → ℝ} (hP : Measurable P) {g : ℝ → ℝ} (hgm : Measurable g)
    (hg0 : ∀ y < -1, g y = 0) (hg1 : ∀ y > 1, g y = 1) (hgb : ∀ y, 0 ≤ g y ∧ g y ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |smoothCDF μ P g δ x - μ.real {ω | P ω < x}| ≤ μ.real {ω | |P ω - x| ≤ δ} := by
  have hA : MeasurableSet {ω | P ω < x} := measurableSet_lt hP measurable_const
  have hB : MeasurableSet {ω | |P ω - x| ≤ δ} :=
    measurableSet_le ((hP.sub measurable_const).abs) measurable_const
  have hgP : Measurable fun ω => g ((x - P ω) / δ) :=
    hgm.comp ((measurable_const.sub hP).div_const δ)
  have hgi : Integrable (fun ω => g ((x - P ω) / δ)) μ :=
    (integrable_const (1 : ℝ)).mono' hgP.aestronglyMeasurable (Eventually.of_forall fun ω =>
      (Real.norm_eq_abs _).trans_le ((abs_of_nonneg (hgb _).1).le.trans (hgb _).2))
  -- pointwise, the integrands differ only where `|P − x| ≤ δ`, and there by at most `1`
  have hpt : ∀ ω, |g ((x - P ω) / δ) - Set.indicator {ω | P ω < x} (fun _ => (1 : ℝ)) ω| ≤
      Set.indicator {ω | |P ω - x| ≤ δ} (fun _ => (1 : ℝ)) ω := by
    intro ω
    have hb := hgb ((x - P ω) / δ)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases hω : |P ω - x| ≤ δ
    · rw [if_pos hω]
      by_cases hlt : P ω < x
      · rw [if_pos hlt, abs_le]
        constructor <;> linarith [hb.1, hb.2]
      · rw [if_neg hlt, sub_zero, abs_of_nonneg hb.1]
        exact hb.2
    · rw [if_neg hω]
      rw [not_le] at hω
      by_cases hlt : P ω < x
      · rw [if_pos hlt]
        rw [abs_of_neg (sub_neg.2 hlt)] at hω
        rw [hg1 _ (by rw [gt_iff_lt, lt_div_iff₀ hδ]; linarith), sub_self, abs_zero]
      · rw [if_neg hlt]
        rw [not_lt] at hlt
        rw [abs_of_nonneg (sub_nonneg.2 hlt)] at hω
        rw [hg0 _ (by rw [div_lt_iff₀ hδ]; linarith), sub_self, abs_zero]
  have hIA : ∫ ω, Set.indicator {ω | P ω < x} (fun _ => (1 : ℝ)) ω ∂μ = μ.real {ω | P ω < x} := by
    rw [integral_indicator_const _ hA, smul_eq_mul, mul_one]
  have hIB : ∫ ω, Set.indicator {ω | |P ω - x| ≤ δ} (fun _ => (1 : ℝ)) ω ∂μ =
      μ.real {ω | |P ω - x| ≤ δ} := by
    rw [integral_indicator_const _ hB, smul_eq_mul, mul_one]
  rw [smoothCDF, ← hIA, ← hIB, ← integral_sub hgi ((integrable_const 1).indicator hA)]
  exact (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun ω => abs_nonneg _) ((integrable_const 1).indicator hB)
    (Eventually.of_forall hpt))

/-- **"As `δ → 0` … the accuracy improves"** (Giles 2015, §5.7): with the hypotheses of
`abs_smoothCDF_sub_le`, if `P` has no atom at `x`, then `C_δ(x) → C(x) = P(P < x)` as `δ → 0⁺`. -/
theorem tendsto_smoothCDF {P : Ω → ℝ} (hP : Measurable P) {g : ℝ → ℝ} (hgm : Measurable g)
    (hg0 : ∀ y < -1, g y = 0) (hg1 : ∀ y > 1, g y = 1) (hgb : ∀ y, 0 ≤ g y ∧ g y ≤ 1) (x : ℝ)
    (hx : μ {ω | P ω = x} = 0) :
    Tendsto (fun δ => smoothCDF μ P g δ x) (𝓝[>] 0) (𝓝 (μ.real {ω | P ω < x})) := by
  -- the probability of `|P − x| ≤ δ` tends to that of `P = x`, i.e. to `0`
  have hmeas : Tendsto (fun δ : ℝ => μ {ω | |P ω - x| ≤ δ}) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_measure_biInter_gt (μ := μ) (s := fun δ : ℝ => {ω | |P ω - x| ≤ δ})
      (a := 0) (fun r _ => (measurableSet_le ((hP.sub measurable_const).abs)
        measurable_const).nullMeasurableSet)
      (fun i j _ hij ω hω => le_trans hω hij) ⟨1, one_pos, measure_ne_top μ _⟩
    have hinter : (⋂ r > (0 : ℝ), {ω | |P ω - x| ≤ r}) = {ω | P ω = x} := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro h
        by_contra hne
        have hpos : 0 < |P ω - x| := abs_pos.2 (sub_ne_zero.2 hne)
        have := h (|P ω - x| / 2) (half_pos hpos)
        linarith
      · intro h r hr
        rw [h, sub_self, abs_zero]
        exact hr.le
    rw [hinter, hx] at h
    exact h
  have hreal : Tendsto (fun δ : ℝ => μ.real {ω | |P ω - x| ≤ δ}) (𝓝[>] 0) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeas
    simpa [Function.comp_def, measureReal_def] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun δ => norm_nonneg _) ?_ hreal
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [Real.norm_eq_abs]
  exact abs_smoothCDF_sub_le hP hgm hg0 hg1 hgb hδ x

end cdf

/-! ### Splitting (§5.2) -/

section splitting

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {μ : Measure Ω₁}
  [IsProbabilityMeasure μ] {ν : Measure Ω₂} [IsProbabilityMeasure ν]

/-- The `j`-th sub-sample, `(x, z) ↦ (x, z_j)`, pushes `μ ⊗ ν^ℕ` forward to `μ ⊗ ν`. -/
lemma measurePreserving_subsample (j : ℕ) :
    MeasurePreserving (fun q : Ω₁ × (ℕ → Ω₂) => (q.1, q.2 j))
      (μ.prod (Measure.infinitePi fun _ => ν)) (μ.prod ν) := by
  refine ⟨measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd), ?_⟩
  have h := Measure.map_prod_map μ (Measure.infinitePi fun _ : ℕ => ν) measurable_id
    (measurable_pi_apply j)
  rw [Measure.map_id, Measure.infinitePi_map_eval] at h
  exact h.symm

/-- Two distinct sub-samples, `(x, z) ↦ (x, (z_j, z_k))`, push `μ ⊗ ν^ℕ` forward to
`μ ⊗ (ν ⊗ ν)`. -/
lemma measurePreserving_subsample_pair {j k : ℕ} (hjk : j ≠ k) :
    MeasurePreserving (fun q : Ω₁ × (ℕ → Ω₂) => (q.1, (q.2 j, q.2 k)))
      (μ.prod (Measure.infinitePi fun _ => ν)) (μ.prod (ν.prod ν)) := by
  refine ⟨measurable_fst.prodMk (((measurable_pi_apply j).prodMk
    (measurable_pi_apply k)).comp measurable_snd), ?_⟩
  have h := Measure.map_prod_map μ (Measure.infinitePi fun _ : ℕ => ν) measurable_id
    ((measurable_pi_apply j).prodMk (measurable_pi_apply k))
  rw [Measure.map_id, Measure.infinitePi_map_eval_prod hjk] at h
  exact h.symm

/-- A function of one sub-sample: integrability and integral transfer from `μ ⊗ ν`. -/
lemma integrable_integral_subsample (j : ℕ) {F : Ω₁ × Ω₂ → ℝ} (hF : Integrable F (μ.prod ν)) :
    Integrable (fun q : Ω₁ × (ℕ → Ω₂) => F (q.1, q.2 j)) (μ.prod (Measure.infinitePi fun _ => ν)) ∧
      ∫ q, F (q.1, q.2 j) ∂(μ.prod (Measure.infinitePi fun _ => ν)) = ∫ w, F w ∂(μ.prod ν) := by
  have hmp := measurePreserving_subsample (μ := μ) (ν := ν) j
  have hF' : Integrable F (Measure.map (fun q : Ω₁ × (ℕ → Ω₂) => (q.1, q.2 j))
      (μ.prod (Measure.infinitePi fun _ => ν))) := by
    rw [hmp.map_eq]
    exact hF
  refine ⟨hF'.comp_measurable hmp.measurable, ?_⟩
  have h := integral_map hmp.measurable.aemeasurable hF'.aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h.symm

/-- **Splitting** (Giles 2015, §5.2, pp. 36–38: "the conditional expectation is replaced by a
numerical estimate, averaging over a number of sub-samples. i.e. for each set of Brownian
increments up to one fine timestep before the end, one uses a number of samples of the final
Brownian increment to produce an average payoff.  If the number of sub-samples is chosen
appropriately, the variance is the same, to leading order, without any increase in the
computational cost").  Let `x ∼ μ` be the outer sample, `z_0, z_1, … ∼ ν` independent sub-samples
of the final increment, independent of `x`, and `g(x, z)` a square-integrable payoff.  The average
of `M ≥ 1` sub-samples, `S = M⁻¹ ∑_{j<M} g(x, z_j)`, has the mean of the conditional expectation
`m(x) = ∫ g(x, z) dν(z)`, and `V[S] = V[m] + E[v]/M`, where `v(x) = ∫ (g(x, z) − m(x))² dν(z)` is
the conditional variance: against the exact conditional expectation, splitting adds the variance
`E[v]/M`, which the choice of `M` makes as small as required. -/
theorem splitting_mean_variance {g : Ω₁ → Ω₂ → ℝ} (hg : Measurable (Function.uncurry g))
    (hg2 : Integrable (fun q : Ω₁ × Ω₂ => g q.1 q.2 ^ 2) (μ.prod ν)) {M : ℕ} (hM : 0 < M) :
    ∫ q, (∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M ∂(μ.prod (Measure.infinitePi fun _ => ν)) =
        ∫ x, ∫ z, g x z ∂ν ∂μ ∧
      variance (fun q : Ω₁ × (ℕ → Ω₂) => (∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M)
          (μ.prod (Measure.infinitePi fun _ => ν)) =
        variance (fun x => ∫ z, g x z ∂ν) μ +
          (∫ x, ∫ z, (g x z - ∫ z', g x z' ∂ν) ^ 2 ∂ν ∂μ) / M := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hgm : Measurable fun q : Ω₁ × Ω₂ => g q.1 q.2 := hg
  -- `g` is integrable on `μ ⊗ ν`
  have hint : Integrable (fun q : Ω₁ × Ω₂ => g q.1 q.2) (μ.prod ν) := by
    refine Integrable.mono' ((hg2.add (integrable_const (1 : ℝ))).div_const 2)
      hgm.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    show ‖g q.1 q.2‖ ≤ (g q.1 q.2 ^ 2 + 1) / 2
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|g q.1 q.2| - 1), sq_abs (g q.1 q.2)]
  -- the moments of `g` along the sub-samples
  obtain ⟨A, hA⟩ : ∃ A, A = ∫ x, ∫ z, g x z ^ 2 ∂ν ∂μ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∫ x, (∫ z, g x z ∂ν) ^ 2 ∂μ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = ∫ x, ∫ z, g x z ∂ν ∂μ := ⟨_, rfl⟩
  have hgj : ∀ j, Integrable (fun q : Ω₁ × (ℕ → Ω₂) => g q.1 (q.2 j))
      (μ.prod (Measure.infinitePi fun _ => ν)) := fun j => (integrable_integral_subsample j hint).1
  have hgj2 : ∀ j, Integrable (fun q : Ω₁ × (ℕ → Ω₂) => g q.1 (q.2 j) ^ 2)
      (μ.prod (Measure.infinitePi fun _ => ν)) := fun j => (integrable_integral_subsample j hg2).1
  have hmean_j : ∀ j : ℕ, ∫ q, g q.1 (q.2 j) ∂(μ.prod (Measure.infinitePi fun _ => ν)) = C := by
    intro j
    have h := (integrable_integral_subsample j hint).2
    rw [integral_prod _ hint] at h
    rw [hC]
    exact h
  have hsq_j : ∀ j : ℕ, ∫ q, g q.1 (q.2 j) ^ 2 ∂(μ.prod (Measure.infinitePi fun _ => ν)) = A := by
    intro j
    have h := (integrable_integral_subsample j hg2).2
    rw [integral_prod _ hg2] at h
    rw [hA]
    exact h
  have hcross : ∀ {j k : ℕ}, j ≠ k →
      Integrable (fun q : Ω₁ × (ℕ → Ω₂) => g q.1 (q.2 j) * g q.1 (q.2 k))
        (μ.prod (Measure.infinitePi fun _ => ν)) ∧
      ∫ q, g q.1 (q.2 j) * g q.1 (q.2 k) ∂(μ.prod (Measure.infinitePi fun _ => ν)) = B := by
    intro j k hjk
    have hi : Integrable (fun q : Ω₁ × (ℕ → Ω₂) => g q.1 (q.2 j) * g q.1 (q.2 k))
        (μ.prod (Measure.infinitePi fun _ => ν)) := by
      refine Integrable.mono' (((hgj2 j).add (hgj2 k)).div_const 2)
        ((hgj j).aestronglyMeasurable.mul (hgj k).aestronglyMeasurable)
        (Eventually.of_forall fun q => ?_)
      show ‖g q.1 (q.2 j) * g q.1 (q.2 k)‖ ≤ (g q.1 (q.2 j) ^ 2 + g q.1 (q.2 k) ^ 2) / 2
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [sq_nonneg (|g q.1 (q.2 j)| - |g q.1 (q.2 k)|), sq_abs (g q.1 (q.2 j)),
        sq_abs (g q.1 (q.2 k))]
    refine ⟨hi, ?_⟩
    have hmp := measurePreserving_subsample_pair (μ := μ) (ν := ν) hjk
    have hFm : Measurable fun w : Ω₁ × (Ω₂ × Ω₂) => g w.1 w.2.1 * g w.1 w.2.2 :=
      (hgm.comp (measurable_fst.prodMk measurable_snd.fst)).mul
        (hgm.comp (measurable_fst.prodMk measurable_snd.snd))
    have hF : Integrable (fun w : Ω₁ × (Ω₂ × Ω₂) => g w.1 w.2.1 * g w.1 w.2.2)
        (μ.prod (ν.prod ν)) := by
      rw [← hmp.map_eq]
      exact (integrable_map_measure hFm.aestronglyMeasurable hmp.measurable.aemeasurable).2 hi
    have h1 := integral_map (μ := μ.prod (Measure.infinitePi fun _ : ℕ => ν))
      (f := fun w : Ω₁ × (Ω₂ × Ω₂) => g w.1 w.2.1 * g w.1 w.2.2)
      hmp.measurable.aemeasurable hFm.aestronglyMeasurable
    rw [hmp.map_eq, integral_prod _ hF] at h1
    have h2 : ∫ x, ∫ y, g x y.1 * g x y.2 ∂(ν.prod ν) ∂μ = B := by
      rw [hB]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show ∫ y, g x y.1 * g x y.2 ∂(ν.prod ν) = (∫ z, g x z ∂ν) ^ 2
      rw [integral_prod_mul (g x) (g x), sq]
    rw [← h2]
    exact h1.symm
  have hjk : ∀ j k, Integrable (fun q : Ω₁ × (ℕ → Ω₂) => g q.1 (q.2 j) * g q.1 (q.2 k))
        (μ.prod (Measure.infinitePi fun _ => ν)) ∧
      ∫ q, g q.1 (q.2 j) * g q.1 (q.2 k) ∂(μ.prod (Measure.infinitePi fun _ => ν)) =
        if j = k then A else B := by
    intro j k
    by_cases h : j = k
    · rw [if_pos h, ← h]
      have e : (fun q : Ω₁ × (ℕ → Ω₂) => g q.1 (q.2 j) * g q.1 (q.2 j)) =
          fun q => g q.1 (q.2 j) ^ 2 := funext fun q => (sq _).symm
      rw [e]
      exact ⟨hgj2 j, hsq_j j⟩
    · rw [if_neg h]
      exact hcross h
  -- the mean of the splitting estimator
  have hES : ∫ q, (∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M
      ∂(μ.prod (Measure.infinitePi fun _ => ν)) = C := by
    rw [integral_div, integral_finsetSum (Finset.range M) fun j _ => hgj j,
      Finset.sum_congr rfl fun j _ => hmean_j j, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_div_cancel_left₀ _ hM']
  -- its second moment
  have hpt : ∀ q : Ω₁ × (ℕ → Ω₂), ((∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M) ^ 2 =
      (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M, g q.1 (q.2 j) * g q.1 (q.2 k)) /
        (M : ℝ) ^ 2 := by
    intro q
    rw [div_pow, sq, Finset.sum_mul_sum]
  have hcount : ∀ j ∈ Finset.range M,
      ∑ k ∈ Finset.range M, (if j = k then A else B) = A + ((M : ℝ) - 1) * B := by
    intro j hj
    have e : ∀ k, (if j = k then A else B) = B + if j = k then A - B else 0 := fun k => by
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, Finset.sum_ite_eq, if_pos hj, nsmul_eq_mul]
    ring
  have hES2 : ∫ q, ((∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M) ^ 2
      ∂(μ.prod (Measure.infinitePi fun _ => ν)) =
      ((M : ℝ) * A + (M : ℝ) * ((M : ℝ) - 1) * B) / (M : ℝ) ^ 2 := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_div,
      integral_finsetSum (Finset.range M) fun j _ =>
        integrable_finsetSum (Finset.range M) fun k _ => (hjk j k).1,
      Finset.sum_congr rfl fun j _ => integral_finsetSum (Finset.range M) fun k _ => (hjk j k).1,
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => (hjk j k).2,
      Finset.sum_congr rfl hcount, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hSint : Integrable (fun q : Ω₁ × (ℕ → Ω₂) => (∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M)
      (μ.prod (Measure.infinitePi fun _ => ν)) :=
    (integrable_finsetSum (Finset.range M) fun j _ => hgj j).div_const (M : ℝ)
  have hS2int : Integrable (fun q : Ω₁ × (ℕ → Ω₂) =>
      ((∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M) ^ 2) (μ.prod (Measure.infinitePi fun _ => ν)) :=
    ((integrable_finsetSum (Finset.range M) fun j _ =>
      integrable_finsetSum (Finset.range M) fun k _ => (hjk j k).1).div_const
      ((M : ℝ) ^ 2)).congr (Eventually.of_forall fun q => (hpt q).symm)
  have hSmem : MemLp (fun q : Ω₁ × (ℕ → Ω₂) => (∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M) 2
      (μ.prod (Measure.infinitePi fun _ => ν)) :=
    (memLp_two_iff_integrable_sq hSint.aestronglyMeasurable).2 hS2int
  have hVS : variance (fun q : Ω₁ × (ℕ → Ω₂) => (∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M)
      (μ.prod (Measure.infinitePi fun _ => ν)) =
      ∫ q, ((∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M) ^ 2
        ∂(μ.prod (Measure.infinitePi fun _ => ν)) -
      (∫ q, (∑ j ∈ Finset.range M, g q.1 (q.2 j)) / M
        ∂(μ.prod (Measure.infinitePi fun _ => ν))) ^ 2 :=
    variance_eq_sub hSmem
  -- the conditional mean and the conditional variance
  have hae : ∀ᵐ x ∂μ, (∫ z, g x z ∂ν) ^ 2 ≤ ∫ z, g x z ^ 2 ∂ν ∧
      ∫ z, (g x z - ∫ z', g x z' ∂ν) ^ 2 ∂ν = ∫ z, g x z ^ 2 ∂ν - (∫ z, g x z ∂ν) ^ 2 := by
    filter_upwards [hg2.prod_right_ae] with x hx
    have hgx : Measurable fun z => g x z := hgm.comp (measurable_const.prodMk measurable_id)
    have hmx : MemLp (fun z => g x z) 2 ν :=
      (memLp_two_iff_integrable_sq hgx.aestronglyMeasurable).2 hx
    have h1 : variance (fun z => g x z) ν = ∫ z, g x z ^ 2 ∂ν - (∫ z, g x z ∂ν) ^ 2 :=
      variance_eq_sub hmx
    have h2 : variance (fun z => g x z) ν = ∫ z, (g x z - ∫ z', g x z' ∂ν) ^ 2 ∂ν :=
      variance_eq_integral (hgx.aemeasurable (μ := ν))
    have h3 := variance_nonneg (fun z => g x z) ν
    exact ⟨by linarith, h2.symm.trans h1⟩
  have hAint : Integrable (fun x => ∫ z, g x z ^ 2 ∂ν) μ := hg2.integral_prod_left
  have hmm : StronglyMeasurable fun x => ∫ z, g x z ∂ν :=
    hgm.stronglyMeasurable.integral_prod_right'
  have hm2 : Integrable (fun x => (∫ z, g x z ∂ν) ^ 2) μ := by
    refine hAint.mono' (hmm.aestronglyMeasurable.pow 2) (hae.mono fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx.1
  have hmMem : MemLp (fun x => ∫ z, g x z ∂ν) 2 μ :=
    (memLp_two_iff_integrable_sq hmm.aestronglyMeasurable).2 hm2
  have hVm : variance (fun x => ∫ z, g x z ∂ν) μ =
      ∫ x, (∫ z, g x z ∂ν) ^ 2 ∂μ - (∫ x, ∫ z, g x z ∂ν ∂μ) ^ 2 :=
    variance_eq_sub hmMem
  have hv : ∫ x, ∫ z, (g x z - ∫ z', g x z' ∂ν) ^ 2 ∂ν ∂μ =
      ∫ x, ∫ z, g x z ^ 2 ∂ν ∂μ - ∫ x, (∫ z, g x z ∂ν) ^ 2 ∂μ := by
    rw [← integral_sub hAint hm2]
    exact integral_congr_ae (hae.mono fun x hx => hx.2)
  refine ⟨hES.trans hC, ?_⟩
  rw [hVS, hES2, hES, hVm, hv, ← hA, ← hB, ← hC]
  have hMI : (M : ℝ) * (M : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hM'
  linear_combination (A * (M : ℝ)⁻¹ + B * ((M : ℝ) * (M : ℝ)⁻¹ + 1) - B * (M : ℝ)⁻¹) * hMI

end splitting

/-! ### The density as a limit (§5.7) -/

section density

open scoped NNReal ENNReal

/-- A function that vanishes outside `[−1, 1]` has compact support. -/
lemma hasCompactSupport_of_abs_gt {g : ℝ → ℝ} (hg0 : ∀ y, 1 < |y| → g y = 0) :
    HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun y hy => hg0 y (by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with hy | hy
    · exact lt_abs.2 (Or.inr (by linarith))
    · exact lt_abs.2 (Or.inl hy))

/-- `y ↦ c φ(c(x − y)) r(y)` is integrable for continuous `φ` with compact support and integrable
`r`. -/
lemma integrable_kernel_mul {φ : ℝ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {r : ℝ → ℝ} (hr : Integrable r) (c x : ℝ) :
    Integrable (fun y => c * φ (c * (x - y)) * r y) := by
  obtain ⟨B, hB⟩ := hφs.exists_bound_of_continuous hφc
  refine hr.bdd_mul (c := |c| * B) ?_ (Eventually.of_forall fun y => ?_)
  · exact (continuous_const.mul (hφc.comp (continuous_const.mul
      (continuous_const.sub continuous_id)))).aestronglyMeasurable
  · show ‖c * φ (c * (x - y))‖ ≤ |c| * B
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg c)

/-- The rescaled kernels `c φ(c(x − ·))` of a nonnegative `φ` with integral `1` vanishing outside
`[−1, 1]` are peak functions at `x`: `∫ c φ(c(x − y)) r(y) dy → r(x)` as `c → ∞` for integrable `r`
continuous at `x` (Mathlib's `tendsto_integral_comp_smul_smul_of_integrable'`). -/
lemma tendsto_kernel_integral {φ : ℝ → ℝ} (hφ0 : ∀ y, 0 ≤ φ y)
    (hφs : ∀ y, 1 < |y| → φ y = 0) (hφ1 : ∫ y, φ y = 1) {r : ℝ → ℝ} (hr : Integrable r)
    {x : ℝ} (hrx : ContinuousAt r x) :
    Tendsto (fun c : ℝ => ∫ y, c * φ (c * (x - y)) * r y) atTop (𝓝 (r x)) := by
  have hdecay : Tendsto (fun y : ℝ => ‖y‖ ^ Module.finrank ℝ ℝ * φ y) (Bornology.cobounded ℝ)
      (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 1] with y hy
    show (0 : ℝ) = ‖y‖ ^ Module.finrank ℝ ℝ * φ y
    rw [Real.norm_eq_abs] at hy
    rw [hφs y hy, mul_zero]
  have h := tendsto_integral_comp_smul_smul_of_integrable' (μ := volume) hφ0 hφ1 hdecay hr hrx
  simp only [Module.finrank_self, pow_one, smul_eq_mul] at h
  exact h

/-- The same for a kernel `g` of either sign: `g` continuous, `g = 0` outside `[−1, 1]` and
`∫ g = 1`.  With `A = ∫ |g| ≥ 1`, `g = ((2A + 1) φ₁ − (2A − 1) φ₂)/2` for the nonnegative kernels
`φ₁ = (2|g| + g)/(2A + 1)` and `φ₂ = (2|g| − g)/(2A − 1)`, each of integral `1`. -/
lemma tendsto_kernel_integral_signed {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ y, 1 < |y| → g y = 0) (hg1 : ∫ y, g y = 1) {r : ℝ → ℝ} (hr : Integrable r)
    {x : ℝ} (hrx : ContinuousAt r x) :
    Tendsto (fun c : ℝ => ∫ y, c * g (c * (x - y)) * r y) atTop (𝓝 (r x)) := by
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport (hasCompactSupport_of_abs_gt hg0)
  obtain ⟨A, hA_def⟩ : ∃ A, A = ∫ t, |g t| := ⟨_, rfl⟩
  have hA : 1 ≤ A := by
    have h := (le_abs_self (∫ t, g t)).trans (abs_integral_le_integral_abs (f := g))
    rwa [hg1, ← hA_def] at h
  have hp : (0 : ℝ) < 2 * A + 1 := by linarith
  have hm : (0 : ℝ) < 2 * A - 1 := by linarith
  have hc₁ : Continuous fun y => (2 * |g y| + g y) / (2 * A + 1) :=
    ((continuous_const.mul hg.abs).add hg).div_const _
  have hc₂ : Continuous fun y => (2 * |g y| - g y) / (2 * A - 1) :=
    ((continuous_const.mul hg.abs).sub hg).div_const _
  have hs₁ : ∀ y, 1 < |y| → (2 * |g y| + g y) / (2 * A + 1) = 0 := fun y hy => by
    rw [hg0 y hy, abs_zero, mul_zero, add_zero, zero_div]
  have hs₂ : ∀ y, 1 < |y| → (2 * |g y| - g y) / (2 * A - 1) = 0 := fun y hy => by
    rw [hg0 y hy, abs_zero, mul_zero, sub_zero, zero_div]
  have h₁ := tendsto_kernel_integral (φ := fun y => (2 * |g y| + g y) / (2 * A + 1))
    (fun y => div_nonneg (by linarith [abs_nonneg (g y), neg_abs_le (g y)]) hp.le) hs₁
    (by
      show ∫ y, (2 * |g y| + g y) / (2 * A + 1) = 1
      rw [integral_div, integral_add (hgi.abs.const_mul 2) hgi, integral_const_mul, hg1,
        ← hA_def]
      exact div_self hp.ne')
    hr hrx
  have h₂ := tendsto_kernel_integral (φ := fun y => (2 * |g y| - g y) / (2 * A - 1))
    (fun y => div_nonneg (by linarith [abs_nonneg (g y), le_abs_self (g y)]) hm.le) hs₂
    (by
      show ∫ y, (2 * |g y| - g y) / (2 * A - 1) = 1
      rw [integral_div, integral_sub (hgi.abs.const_mul 2) hgi, integral_const_mul, hg1,
        ← hA_def]
      exact div_self hm.ne')
    hr hrx
  have hlim := ((h₁.const_mul (2 * A + 1)).sub (h₂.const_mul (2 * A - 1))).div_const 2
  have e : ((2 * A + 1) * r x - (2 * A - 1) * r x) / 2 = r x := by ring
  rw [e] at hlim
  refine hlim.congr fun c => ?_
  have hi₁ := integrable_kernel_mul hc₁ (hasCompactSupport_of_abs_gt hs₁) hr c x
  have hi₂ := integrable_kernel_mul hc₂ (hasCompactSupport_of_abs_gt hs₂) hr c x
  try dsimp only
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hi₁.const_mul _) (hi₂.const_mul _), ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e₁ : (2 * A + 1) * (2 * A + 1)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  have e₂ : (2 * A - 1) * (2 * A - 1)⁻¹ = 1 := mul_inv_cancel₀ hm.ne'
  show ((2 * A + 1) * (c * ((2 * |g (c * (x - y))| + g (c * (x - y))) / (2 * A + 1)) * r y) -
      (2 * A - 1) * (c * ((2 * |g (c * (x - y))| - g (c * (x - y))) / (2 * A - 1)) * r y)) / 2 =
    c * g (c * (x - y)) * r y
  linear_combination (c * (2 * |g (c * (x - y))| + g (c * (x - y))) * r y / 2) * e₁ -
    (c * (2 * |g (c * (x - y))| - g (c * (x - y))) * r y / 2) * e₂

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The density as a limit** (Giles 2015, §5.7, p. 46: "the density `ρ(x)` of the scalar output
`P` is given by `ρ(x) = lim_{δ→0} E[δ⁻¹ g((x − P)/δ)]`, where `g(x)` is a continuous function with
`g(x) = 0` for `|x| > 1`, and `∫_{−1}^{1} g(x) dx = 1`").  If the law of `P` has a density `ρ` with
respect to Lebesgue measure that is continuous at `x`, then `E[δ⁻¹ g((x − P)/δ)] → ρ(x)` as
`δ → 0⁺`. -/
theorem tendsto_density {P : Ω → ℝ} (hP : Measurable P) {ρ : ℝ → ℝ≥0} (hρm : Measurable ρ)
    (hlaw : μ.map P = volume.withDensity fun y => (ρ y : ℝ≥0∞)) {x : ℝ}
    (hρx : ContinuousAt (fun y => (ρ y : ℝ)) x) {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ y, 1 < |y| → g y = 0) (hg1 : ∫ y, g y = 1) :
    Tendsto (fun δ => ∫ ω, δ⁻¹ * g ((x - P ω) / δ) ∂μ) (𝓝[>] 0) (𝓝 (ρ x : ℝ)) := by
  -- the density has total mass one, so it is integrable
  have hmass : ∫⁻ y, (ρ y : ℝ≥0∞) = 1 := by
    have h := congrArg (fun m : Measure ℝ => m Set.univ) hlaw
    simp only [Measure.map_apply hP MeasurableSet.univ, Set.preimage_univ, measure_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h.symm
  have hr : Integrable (fun y => (ρ y : ℝ)) :=
    (integrable_toReal_of_lintegral_ne_top hρm.coe_nnreal_ennreal.aemeasurable
      (by rw [hmass]; exact ENNReal.one_ne_top)).congr (Eventually.of_forall fun _ => rfl)
  -- the expectation is an integral against the density
  have hE : ∀ δ : ℝ, ∫ ω, δ⁻¹ * g ((x - P ω) / δ) ∂μ =
      ∫ y, δ⁻¹ * g (δ⁻¹ * (x - y)) * (ρ y : ℝ) := by
    intro δ
    have hmeas : Measurable fun y : ℝ => δ⁻¹ * g ((x - y) / δ) :=
      measurable_const.mul (hg.measurable.comp ((measurable_const.sub measurable_id).div_const δ))
    rw [← integral_map hP.aemeasurable hmeas.aestronglyMeasurable, hlaw,
      integral_withDensity_eq_integral_smul hρm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [div_eq_inv_mul]
    ring
  exact ((tendsto_kernel_integral_signed hg hg0 hg1 hr hρx).comp tendsto_inv_nhdsGT_zero).congr
    fun δ => (hE δ).symm

end density

end MLMC
