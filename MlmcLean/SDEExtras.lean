import MlmcLean.EulerMaruyama
import MlmcLean.NestedSimulation
import MlmcLean.ErrorAnalysis
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

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
  "as `δ → 0` … the accuracy improves": `C_δ(x) → C(x)` when `P` has no atom at `x`.
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
lemma sq_le_of_abs_le_add {Y a κ s t : ℝ} (h : |Y| ≤ a + κ * (s + t)) : Y ^ 2 ≤ 2 * a ^ 2 + 4 * κ ^ 2 * (s ^ 2 + t ^ 2) := by
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
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
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
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
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

end MLMC
