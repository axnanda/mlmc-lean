import MlmcLean.GBMDigitalTheorem1

/-!
# The conditional-expectation estimator of the digital option for GBM (Giles 2015, §5.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.2, paragraph
"Digital options", pp. 35–36, l. 1525–1600 of `docs/giles2015.txt`.  Geometric Brownian motion
`dS = rS dt + σS dW` (`a(S) = rS`, `b(S) = σS`), the exact solution and the schemes driven by the
same increments `Z_i ∼ N(0, 1)` (`stdNormalSeq`), the coarse path of a sample driven by the summed
increments (`pairAvg`), as in `MlmcLean.GBMDigital`, `MlmcLean.GBMStrongLp` and
`MlmcLean.GBMDigitalTheorem1`.

**The estimator.**  On level `ℓ` (`N = 2^ℓ` fine steps of size `h_ℓ = T 2^{−ℓ}`) the fine path is
the Milstein path up to `t_{N−1}`, and its Euler–Maruyama last step (`gbmMilEM`) is replaced by
the conditional expectation: `P^f_ℓ = Φ((m_f − K)/s_f)` (`gbmDigitalCondFine`) with
`m_f = Ŝ_{N−1} + rŜ_{N−1} h_ℓ` (`gbmCondMeanFine`) and `s_f = |σŜ_{N−1}| √h_ℓ` (`gbmCondStdFine`).
The coarse path of level `ℓ + 1` takes `2^ℓ − 1` Milstein steps of size `h_ℓ` with the summed
increments and re-uses the first half `ΔW_{N−2}` (`N = 2^{ℓ+1}`) of its last increment:
`P^c_ℓ = Φ((m_c − K)/s_c)` (`gbmDigitalCondCoarse`) with
`m_c = Ŝ^c_{N−2} + rŜ^c_{N−2} h_ℓ + σŜ^c_{N−2} ΔW_{N−2}` (`gbmCondMeanCoarse`) and
`s_c = |σŜ^c_{N−2}| √h_{ℓ+1}` (`gbmCondStdCoarse`).  The level-`ℓ` correction is
`P^f_ℓ − P^c_{ℓ−1}` (`fineCoarseDiff`).  `gbmDigitalCondFine_condExp`,
`gbmDigitalCondCoarse_condExp`: these payoffs are the conditional expectations of the digital
payoffs of the fine and the coarse path given the past; `gbmDigitalCond_integral_eq`: (2.4).

**What is proved.**
* `gbm_digital_cond_moments_match` (l. 1563–1566, "matching that of the fine path to within
  `O(h)`, for both the mean and the standard deviation"): for every `m ≥ 1` there is `C` with
  `E[(m_f − m_c)^{2m}] ≤ C h^{2m}` and `E[(s_f − s_c)^{2m}] ≤ C h^{2m}` on every level.
* `gbm_digital_condExp_variance_rate` (l. 1575–1577, "a variance which is approximately
  `O(h^{3/2})`"): for `K ≠ 0` and every `q < 3/2` there is `C` with
  `E[(P^f_ℓ − P^c_{ℓ−1})²] ≤ C h_ℓ^q` (so `V_ℓ ≤ C h_ℓ^q`) on every level `ℓ ≥ 1`.
* `gbm_digital_condExp_weak_rate` (l. 1578, `α`): for every `q < 1`,
  `|E[P^f_ℓ] − P(S_T > K)| ≤ C h_ℓ^q`, with `E[P^f_ℓ] = P(Ŝ^f_N > K)`.
* `gbm_digital_condExp_level_zero` (l. 1579–1583, "there is zero variance on the coarsest
  level"): `P^f_0` is the same number for every sample, `V[P^f_0] = 0`.
* `gbm_digital_condExp_theorem1` (l. 1578–1580, "Since `β > γ`, the MLMC complexity is
  `O(ε⁻²)`"): Theorem 1 end to end, mean square error `< ε²` (with a square-integrable error) at
  cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²`, no logarithmic factor (`α = 3/4`, `β = 5/4`, `γ = 1`;
  `theorem1_fineCoarse_of_rate_gt`).
* Splitting (l. 1591–1600: "the conditional expectation is replaced by a numerical estimate,
  averaging over a number of sub-samples … If the number of sub-samples is chosen appropriately,
  the variance is the same, to leading order, without any increase in the computational cost").
  With `M` sub-samples `Y_i` of the last fine increment, independent of the path
  (`stdNormalSeq.prod stdNormalSeq`; `gbmDigitalSplitFine`, `gbmDigitalSplitCoarse`, which satisfy
  (2.4), `gbmDigitalSplit_integral_eq`): `gbm_digital_split_variance_rate`,
  `E[(P^{f,M}_ℓ − P^{c,M}_{ℓ−1})²] ≤ C (h_ℓ^q + h_ℓ^{q−1/2}/M)` for every `q < 3/2`, the second term
  being the mean conditional variance of one sub-sample term, at most
  `P(H(Ŝ^f_N − K) ≠ H(Ŝ^c_N − K)) = O(h^{1−η})` (`gbm_split_mismatch_rate`), over `M`;
  `gbm_digital_split_sqrt_rate`: `M_ℓ = ⌈h_ℓ^{−1/2}⌉` sub-samples keep `V_ℓ ≤ C h_ℓ^q` at an extra
  cost `M_ℓ ≤ h_ℓ^{−1/2} + 1`, i.e. `M_ℓ h_ℓ ≤ √h_ℓ + h_ℓ → 0` against the path cost `T/h_ℓ`.
  This is the same rate as the conditional-expectation estimator, not the same variance to leading
  order (the paper's claim), which would need `M_ℓ h_ℓ^{1/2} → ∞` and lower bounds.

**The proof of the variance rate** (`condDigital_sq_rate`, in an abstract form).  Since
`Φ((m − K)/s) = P(m + sZ > K)`, the two payoffs differ by at most `2P(|Z| > t) + w/s_f` with
`w = |m_f − m_c| + t|s_f − s_c|`, and by at most `2P(|Z| > t)` if `|m_f − K| > w + t s_f`
(`abs_cdf_div_sub_cdf_div_le`).  With `t = h^{−δ}`, outside an event of probability `O(h^{2pδ})`
(Markov's inequality and the `L^{2p}` matching) `w = O(h^{1−2δ})`; near the strike,
`|Ŝ_{N−1} − K| ≤ C h^{1/2−2δ}`, an event of probability `O(h^{1/2−2δ})` (the bounded lognormal
density of `S_T` and `S_T − Ŝ_{N−1} = O(√h)` in every `L^{2p}`), `s_f ≥ |σ||K|√h/2` as `K ≠ 0`, and
the difference is `O(h^{1/2−2δ})`; away from it both payoffs lie in the same Gaussian tail
(`abs_condDigital_sub_le`, `condDigital_sq_le_main`).  So `E[(P^f − P^c)²] = O(h^{3/2−6δ})`.  The
`L^{2m}` estimates (`MomentBound`) use `gbm_mil_moment_error_le`, `gbm_em_onestep_le`, the exact
solution driven by `pairAvg` at the coarse times (`prod_gbmExpFactor_pairAvg`) and the
independence of the last increments (`MomentBound.mul_eval`).

**Deviations.**
* The exponents: `β` is every `q < 3/2` (the paper says "approximately `O(h^{3/2})`") and `α`
  every `q < 1` (the paper: `α = 1`).  The loss `η > 0` in `β` comes from the tails (the `O(h)`
  matching holds in every `L^p`, not on every path); `α` is derived from the strong error and the
  density, not from a weak-order analysis.  Neither loss changes the complexity `O(ε⁻²)`.
  `MlmcLean.GBMDigitalCondExpEndpoint` reduces the loss in `β` to a factor `(log(1/h))^{5/2}`, for
  every strike (`gbm_digital_condExp_variance_endpoint`).
* `K ≠ 0` is assumed for the variance rate and Theorem 1 (near a strike `K ≠ 0` the conditional
  standard deviation `|σŜ|√h` is of order `√h`); also `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`.  `K = 0` is the
  easy case left out to keep the proof uniform: for small `h` the Milstein path keeps the sign of
  `s₀`.  `MlmcLean.GBMDigitalCondExpExtras` treats it (the corrections are `O(h^q)` for every `q`;
  their exponential smallness is not proved) and gives the variance rate and Theorem 1 for every
  strike (`gbm_digital_condExp_variance_rate_all`, `gbm_digital_condExp_theorem1_all`).
* The factor `25 e^{−rT}` of the paper's payoffs is omitted; `b` stands for `|b|` in the
  denominators; the coarse numerator uses the re-used increment `b ΔW_{N−2}` in place of the
  paper's `b √h_ℓ` (the correction of `digital_smoothing_coarse`).

**What is not proved.**  The endpoint `β = 3/2` without a logarithmic factor
(`MlmcLean.GBMDigitalCondExpEndpoint` proves `V_ℓ = O(h^{3/2} (log(1/h))^{5/2})`, uniformly in `s₀`
and `K`: `gbm_digital_condExp_variance_endpoint`) and the endpoint `α = 1`; the kurtosis
"approximately `O(h^{−1/2})`" (l. 1577); for splitting, "the variance is the same, to leading order"
as an asymptotic equivalence of the variances (only the same rate `O(h^{3/2−η})` is proved).
Theorem 1 end to end for the splitting estimator is in `MlmcLean.GBMDigitalCondExpExtras`
(`gbm_digital_split_theorem1`).
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace MLMC

/-! ### The conditional-expectation payoffs -/

/-- **The conditional mean of the fine path at maturity** (Giles 2015, §5.2, pp. 35–36,
l. 1541–1555: "Conditional on the value `Ŝ_{N−1}` … the numerical approximation for the final value
`Ŝ_N` has a Gaussian distribution").  On level `ℓ` (`N = 2^ℓ` fine steps of size
`h_ℓ = T 2^{−ℓ}`), with the Milstein path `Ŝ^f` of GBM (`a(S) = rS`, `b(S) = σS`) driven by the
increments `Z_i` and an Euler–Maruyama last step `Ŝ^f_N = Ŝ^f_{N−1} + a(Ŝ^f_{N−1}) h_ℓ +
b(Ŝ^f_{N−1}) √h_ℓ Z_{N−1}`, the conditional mean of `Ŝ^f_N` given the past is
`m_f = Ŝ^f_{N−1} + r Ŝ^f_{N−1} h_ℓ`. -/
noncomputable def gbmCondMeanFine (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1) +
    r * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1) * (T / 2 ^ ℓ)

/-- **The conditional standard deviation of the fine path at maturity** (Giles 2015, §5.2, p. 36,
l. 1551–1555): `s_f = |b(Ŝ^f_{N−1})| √h_ℓ = |σ Ŝ^f_{N−1}| √h_ℓ`, in the setting of
`gbmCondMeanFine`. -/
noncomputable def gbmCondStdFine (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  |σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1)| *
    Real.sqrt (T / 2 ^ ℓ)

/-- **The conditional mean of the coarse path at maturity** (Giles 2015, §5.2, p. 36,
l. 1560–1574: "A similar treatment is used for the coarse path, except that in the final timestep,
we re-use the known value of the Brownian increment for the second last fine timestep, which
corresponds to the first half of the final coarse timestep").  This is the coarse path used on
level `ℓ + 1`: `2^ℓ − 1` Milstein steps of size `h_ℓ = T 2^{−ℓ}` driven by the summed increments
(`pairAvg`), reaching `Ŝ^c_{N−2}` (`N = 2^{ℓ+1}`), then the Euler–Maruyama step with the two fine
increments `ΔW_{N−2} = √h_{ℓ+1} Z_{N−2}` (known, re-used) and `ΔW_{N−1}`; given `Ŝ^c_{N−2}` and
`ΔW_{N−2}`, its mean is `m_c = Ŝ^c_{N−2} + r Ŝ^c_{N−2} h_ℓ + σ Ŝ^c_{N−2} ΔW_{N−2}`. -/
noncomputable def gbmCondMeanCoarse (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) +
    r * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) *
      (T / 2 ^ ℓ) +
    σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) *
      (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2))

/-- **The conditional standard deviation of the coarse path at maturity** (Giles 2015, §5.2, p. 36,
l. 1566–1574): only the second half `ΔW_{N−1} = √h_{ℓ+1} Z_{N−1}` of the last coarse increment is
unknown, so `s_c = |σ Ŝ^c_{N−2}| √h_{ℓ+1}`, in the setting of `gbmCondMeanCoarse`. -/
noncomputable def gbmCondStdCoarse (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  |σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1)| *
    Real.sqrt (T / 2 ^ (ℓ + 1))

/-- **The fine conditional-expectation payoff `P^f_ℓ`** (Giles 2015, §5.2, p. 36, l. 1551–1558:
"Thus the fine path payoff can be taken to be
`P^f_ℓ = 25 exp(−rT) Φ((Ŝ^f_{N−1} + a(Ŝ^f_{N−1}) h_ℓ − K)/(b(Ŝ^f_{N−1}) √h_ℓ))`, where `Φ` is the
Normal cumulative distribution function"): `Φ((m_f − K)/s_f)` with `m_f`, `s_f` of
`gbmCondMeanFine`, `gbmCondStdFine` (the factor `25 e^{−rT}` is omitted, `b` is `|b|`). -/
noncomputable def gbmDigitalCondFine (r σ T s₀ K : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  cdf (gaussianReal 0 1) ((gbmCondMeanFine r σ T s₀ ℓ z - K) / gbmCondStdFine r σ T s₀ ℓ z)

/-- **The coarse conditional-expectation payoff `P^c_ℓ`, used on level `ℓ + 1`** (Giles 2015, §5.2,
p. 36, l. 1566–1574: "the corresponding coarse path payoff function is
`P^c_{ℓ−1} = 25 exp(−rT) Φ((Ŝ^c_{N−2} + a(Ŝ^c_{N−2}) h_{ℓ−1} + b(Ŝ^c_{N−2}) √h_ℓ − K)/
(b(Ŝ^c_{N−2}) √h_ℓ))`"): `Φ((m_c − K)/s_c)` with `m_c`, `s_c` of `gbmCondMeanCoarse`,
`gbmCondStdCoarse`, with the re-used increment `b ΔW_{N−2}` in the numerator in place of the
paper's `b √h_ℓ` (the correction recorded under Deviations in the module docstring). -/
noncomputable def gbmDigitalCondCoarse (r σ T s₀ K : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  cdf (gaussianReal 0 1) ((gbmCondMeanCoarse r σ T s₀ ℓ z - K) / gbmCondStdCoarse r σ T s₀ ℓ z)

/-- **The fine path at maturity: Milstein steps and an Euler–Maruyama last step** (Giles 2015,
§5.2, p. 35, l. 1541–1544: "We start by considering the fine path simulation, and make a slight
change by using the Euler-Maruyama discretisation for the final timestep, instead of the Milstein
discretisation"): on level `ℓ`,
`Ŝ^f_N = Ŝ^f_{N−1} + r Ŝ^f_{N−1} h_ℓ + σ Ŝ^f_{N−1} √h_ℓ Z_{N−1}`, `N = 2^ℓ`. -/
noncomputable def gbmMilEM (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
    (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1))
    (Real.sqrt (T / 2 ^ ℓ) * z (2 ^ ℓ - 1))

/-! ### Uniform moment bounds -/

section MomentTools

variable {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Uniform `2m`-th moment bounds over a family** (the bookkeeping of the `L^{2m}` estimates
behind Giles 2015, §5.2, p. 36, l. 1563–1566: "matching that of the fine path to within `O(h)`, for
both the mean and the standard deviation"): every `f i` has an integrable `2m`-th power, and
`E[(f i)^{2m}] ≤ C ρ_i` with one constant `C ≥ 0` for all `i`. -/
def MomentBound (μ : Measure Ω) (f : ι → Ω → ℝ) (m : ℕ) (ρ : ι → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ i, Integrable (fun ω => f i ω ^ (2 * m)) μ ∧
    ∫ ω, f i ω ^ (2 * m) ∂μ ≤ C * ρ i

/-- `(a + b)^{2m} ≤ 2^{2m−1} (a^{2m} + b^{2m})` for all reals (convexity of `x ↦ x^{2m}`; Giles
2015, §5.2). -/
lemma pow_two_mul_add_le_two_pow (a b : ℝ) (m : ℕ) :
    (a + b) ^ (2 * m) ≤ 2 ^ (2 * m - 1) * (a ^ (2 * m) + b ^ (2 * m)) := by
  have hE : Even (2 * m) := even_two_mul m
  rw [← hE.pow_abs (a + b), ← hE.pow_abs a, ← hE.pow_abs b]
  exact (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le a b) _).trans
    (add_pow_le (abs_nonneg a) (abs_nonneg b) _)

/-- `(f + g)^{2m}` is integrable if `f^{2m}` and `g^{2m}` are, and
`E[(f + g)^{2m}] ≤ 2^{2m−1} (E[f^{2m}] + E[g^{2m}])` (Giles 2015, §5.2). -/
lemma integrable_integral_add_pow_two_mul {f g : Ω → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    {m : ℕ} (hf : Integrable (fun ω => f ω ^ (2 * m)) μ)
    (hg : Integrable (fun ω => g ω ^ (2 * m)) μ) :
    Integrable (fun ω => (f ω + g ω) ^ (2 * m)) μ ∧
      ∫ ω, (f ω + g ω) ^ (2 * m) ∂μ ≤
        2 ^ (2 * m - 1) * (∫ ω, f ω ^ (2 * m) ∂μ + ∫ ω, g ω ^ (2 * m) ∂μ) := by
  have hbd : Integrable (fun ω => 2 ^ (2 * m - 1) * (f ω ^ (2 * m) + g ω ^ (2 * m))) μ :=
    (hf.add hg).const_mul _
  have hint : Integrable (fun ω => (f ω + g ω) ^ (2 * m)) μ := by
    refine hbd.mono' ((hfm.add hgm).pow_const _).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ((even_two_mul m).pow_nonneg _)]
    exact pow_two_mul_add_le_two_pow _ _ _
  refine ⟨hint, ?_⟩
  calc ∫ ω, (f ω + g ω) ^ (2 * m) ∂μ
      ≤ ∫ ω, 2 ^ (2 * m - 1) * (f ω ^ (2 * m) + g ω ^ (2 * m)) ∂μ :=
        integral_mono hint hbd fun ω => pow_two_mul_add_le_two_pow _ _ _
    _ = 2 ^ (2 * m - 1) * (∫ ω, f ω ^ (2 * m) ∂μ + ∫ ω, g ω ^ (2 * m) ∂μ) := by
        rw [integral_const_mul, integral_add hf hg]

/-- Uniform moment bounds add up (Giles 2015, §5.2). -/
lemma MomentBound.add {f g : ι → Ω → ℝ} {m : ℕ} {ρ : ι → ℝ} (hf : MomentBound μ f m ρ)
    (hg : MomentBound μ g m ρ) (hfm : ∀ i, Measurable (f i)) (hgm : ∀ i, Measurable (g i)) :
    MomentBound μ (fun i ω => f i ω + g i ω) m ρ := by
  obtain ⟨C₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, hC₂, h₂⟩ := hg
  refine ⟨2 ^ (2 * m - 1) * (C₁ + C₂), by positivity, fun i => ?_⟩
  obtain ⟨hint, hle⟩ := integrable_integral_add_pow_two_mul (hfm i) (hgm i) (h₁ i).1 (h₂ i).1
  refine ⟨hint, hle.trans ?_⟩
  have := (h₁ i).2
  have := (h₂ i).2
  calc 2 ^ (2 * m - 1) * (∫ ω, f i ω ^ (2 * m) ∂μ + ∫ ω, g i ω ^ (2 * m) ∂μ)
      ≤ 2 ^ (2 * m - 1) * (C₁ * ρ i + C₂ * ρ i) := by gcongr
    _ = _ := by ring

/-- Uniform moment bounds are kept under negation (Giles 2015, §5.2). -/
lemma MomentBound.neg {f : ι → Ω → ℝ} {m : ℕ} {ρ : ι → ℝ} (hf : MomentBound μ f m ρ) :
    MomentBound μ (fun i ω => -f i ω) m ρ := by
  obtain ⟨C, hC, h⟩ := hf
  refine ⟨C, hC, fun i => ?_⟩
  simp only [(even_two_mul m).neg_pow]
  exact h i

/-- A uniform moment bound for a family multiplied by numbers `c_i` (Giles 2015, §5.2). -/
lemma MomentBound.const_mul {f : ι → Ω → ℝ} {m : ℕ} {ρ : ι → ℝ} (c : ι → ℝ)
    (hf : MomentBound μ f m ρ) :
    MomentBound μ (fun i ω => c i * f i ω) m (fun i => c i ^ (2 * m) * ρ i) := by
  obtain ⟨C, hC, h⟩ := hf
  refine ⟨C, hC, fun i => ?_⟩
  obtain ⟨hi, hb⟩ := h i
  simp only [mul_pow]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hc : 0 ≤ c i ^ (2 * m) := (even_two_mul m).pow_nonneg _
  calc c i ^ (2 * m) * ∫ ω, f i ω ^ (2 * m) ∂μ ≤ c i ^ (2 * m) * (C * ρ i) :=
        mul_le_mul_of_nonneg_left hb hc
    _ = C * (c i ^ (2 * m) * ρ i) := by ring

/-- A uniform moment bound with a rate `ρ ≤ K ρ'` holds with the rate `ρ'` (Giles 2015, §5.2). -/
lemma MomentBound.mono {f : ι → Ω → ℝ} {m : ℕ} {ρ ρ' : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hρ : ∀ i, ρ i ≤ K * ρ' i) (hf : MomentBound μ f m ρ) : MomentBound μ f m ρ' := by
  obtain ⟨C, hC, h⟩ := hf
  refine ⟨C * K, mul_nonneg hC hK, fun i => ⟨(h i).1, (h i).2.trans ?_⟩⟩
  calc C * ρ i ≤ C * (K * ρ' i) := mul_le_mul_of_nonneg_left (hρ i) hC
    _ = C * K * ρ' i := by ring

/-- Uniform moment bounds pass to pointwise equal families (Giles 2015, §5.2). -/
lemma MomentBound.congr {f g : ι → Ω → ℝ} {m : ℕ} {ρ : ι → ℝ} (hfg : ∀ i ω, f i ω = g i ω)
    (hf : MomentBound μ f m ρ) : MomentBound μ g m ρ := by
  have e : f = g := funext fun i => funext fun ω => hfg i ω
  rw [← e]
  exact hf

/-- A family dominated by `|c_i|` times a family with a uniform moment bound has the bound
`c_i^{2m} ρ_i` (Giles 2015, §5.2). -/
lemma MomentBound.of_abs_le {f g : ι → Ω → ℝ} {m : ℕ} {ρ : ι → ℝ} (c : ι → ℝ)
    (hgm : ∀ i, Measurable (g i)) (hle : ∀ i ω, |g i ω| ≤ |c i| * |f i ω|)
    (hf : MomentBound μ f m ρ) : MomentBound μ g m (fun i => c i ^ (2 * m) * ρ i) := by
  obtain ⟨C, hC, h⟩ := hf.const_mul c
  refine ⟨C, hC, fun i => ?_⟩
  obtain ⟨hi, hb⟩ := h i
  have hE : Even (2 * m) := even_two_mul m
  have hpt : ∀ ω, g i ω ^ (2 * m) ≤ (c i * f i ω) ^ (2 * m) := fun ω => by
    rw [← hE.pow_abs (g i ω), ← hE.pow_abs (c i * f i ω), abs_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) (hle i ω) _
  have hint : Integrable (fun ω => g i ω ^ (2 * m)) μ := by
    refine hi.mono' ((hgm i).pow_const _).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hE.pow_nonneg _)]
    exact hpt ω
  exact ⟨hint, (integral_mono hint hi hpt).trans hb⟩

end MomentTools

/-- **A product with an independent factor** (Giles 2015, §5.1–§5.2: the Brownian increments of
successive time steps are independent).  If `U_i` is a measurable function of `Z_0, …, Z_{n_i − 1}`
and `g_i` a measurable function, then `E[(U_i g_i(Z_{n_i}))^{2m}] = E[U_i^{2m}] E[g_i(Z)^{2m}]`, so
uniform bounds `O(ρ₁)` and `O(ρ₂)` give `O(ρ₁ ρ₂)` (`integral_mul_comp_eval_of_eq_lt`). -/
lemma MomentBound.mul_eval {ι : Type*} {U : ι → (ℕ → ℝ) → ℝ} {n : ι → ℕ} {g : ι → ℝ → ℝ}
    {m : ℕ} {ρ₁ ρ₂ : ι → ℝ} (hU : MomentBound stdNormalSeq U m ρ₁)
    (hg : MomentBound (gaussianReal 0 1) g m ρ₂) (hUm : ∀ i, Measurable (U i))
    (hdep : ∀ i (z z' : ℕ → ℝ), (∀ j < n i, z j = z' j) → U i z = U i z')
    (hgm : ∀ i, Measurable (g i)) :
    MomentBound stdNormalSeq (fun i z => U i z * g i (z (n i))) m (fun i => ρ₁ i * ρ₂ i) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hU
  obtain ⟨C₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, fun i => ?_⟩
  obtain ⟨hi₁, hb₁⟩ := h₁ i
  obtain ⟨hi₂, hb₂⟩ := h₂ i
  have hdep' : ∀ z z' : ℕ → ℝ, (∀ j < n i, z j = z' j) → U i z ^ (2 * m) = U i z' ^ (2 * m) :=
    fun z z' hzz => by rw [hdep i z z' hzz]
  have hA : Measurable fun z => U i z ^ (2 * m) := (hUm i).pow_const _
  have hB : Measurable fun x => g i x ^ (2 * m) := (hgm i).pow_const _
  simp only [mul_pow]
  refine ⟨integrable_mul_comp_eval_of_eq_lt hA hdep' hB hi₁ hi₂, ?_⟩
  rw [integral_mul_comp_eval_of_eq_lt hA hdep' hB]
  have h0₁ : 0 ≤ ∫ z, U i z ^ (2 * m) ∂stdNormalSeq :=
    integral_nonneg fun z => (even_two_mul m).pow_nonneg _
  have h0₂ : 0 ≤ ∫ x, g i x ^ (2 * m) ∂gaussianReal 0 1 :=
    integral_nonneg fun x => (even_two_mul m).pow_nonneg _
  calc (∫ z, U i z ^ (2 * m) ∂stdNormalSeq) * ∫ x, g i x ^ (2 * m) ∂gaussianReal 0 1
      ≤ (C₁ * ρ₁ i) * (C₂ * ρ₂ i) := mul_le_mul hb₁ hb₂ h0₂ (h0₁.trans hb₁)
    _ = C₁ * C₂ * (ρ₁ i * ρ₂ i) := by ring

/-! ### Uniform moment bounds for GBM -/

section GBMBounds

variable (r σ s₀ : ℝ) {T : ℝ} {ι : Type*}

/-- **Moments of the exact GBM solution on the grid** (Giles 2015, §5.1–§5.2): for grid times
`t_k = k h_i ≤ T`, `E[S_{t_k}^{2m}] ≤ S_0^{2m} e^{ω T}` (`ω = gbmLpRate m r σ`), uniformly; here
`S_{t_k} = S_0 ∏_{j<k} e^{(r − σ²/2)h + σ√h Z_j}`. -/
lemma momentBound_gbmExp_prod {h : ι → ℝ} {k : ι → ℕ} (hh : ∀ i, 0 ≤ h i)
    (hkT : ∀ i, (k i : ℝ) * h i ≤ T) (m : ℕ) :
    MomentBound stdNormalSeq (fun i z => s₀ * ∏ j ∈ range (k i), gbmExpFactor r σ (h i) (z j)) m
      (fun _ => 1) := by
  have hs : 0 ≤ s₀ ^ (2 * m) := (even_two_mul m).pow_nonneg s₀
  refine ⟨s₀ ^ (2 * m) * Real.exp (gbmLpRate m r σ * T), mul_nonneg hs (Real.exp_pos _).le,
    fun i => ?_⟩
  have e : (fun z : ℕ → ℝ => (s₀ * ∏ j ∈ range (k i), gbmExpFactor r σ (h i) (z j)) ^ (2 * m)) =
      fun z => s₀ ^ (2 * m) * (∏ j ∈ range (k i), gbmExpFactor r σ (h i) (z j)) ^ (2 * m) := by
    funext z
    rw [mul_pow]
  rw [e]
  refine ⟨(integrable_prod_range_pow (measurable_gbmExpFactor r σ _)
    (integrable_gbmExpFactor_pow r σ _ _) _).const_mul _, ?_⟩
  rw [integral_const_mul, integral_prod_range_pow (measurable_gbmExpFactor r σ _), mul_one]
  have hA := integral_gbmExpFactor_pow_le r σ (hh i) m
  rw [Real.sq_sqrt (hh i)] at hA
  have hA0 : 0 ≤ ∫ x, gbmExpFactor r σ (h i) x ^ (2 * m) ∂gaussianReal 0 1 :=
    integral_nonneg fun x => (even_two_mul m).pow_nonneg _
  have hω := gbmLpRate_nonneg m r σ
  have h1 : (∫ x, gbmExpFactor r σ (h i) x ^ (2 * m) ∂gaussianReal 0 1) ^ k i ≤
      Real.exp (gbmLpRate m r σ * T) := by
    calc (∫ x, gbmExpFactor r σ (h i) x ^ (2 * m) ∂gaussianReal 0 1) ^ k i
        ≤ Real.exp (gbmLpRate m r σ * h i) ^ k i := pow_le_pow_left₀ hA0 hA _
      _ = Real.exp (gbmLpRate m r σ * (k i * h i)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
      _ ≤ Real.exp (gbmLpRate m r σ * T) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hkT i) hω)
  exact mul_le_mul_of_nonneg_left h1 hs

/-- **The Milstein error of GBM in `L^{2m}`, uniformly on the grid** (Giles 2015, §5.2, p. 35,
l. 1499–1500: "first order strong convergence"): for grid times `t_k = k h_i ≤ T`,
`E[(S_{t_k} − Ŝ_k)^{2m}] ≤ C_m(T) h_i^{2m}` (`gbm_mil_moment_error_le`), in product form. -/
lemma momentBound_gbmMil_err (hT : 0 ≤ T) {h : ι → ℝ} {k : ι → ℕ} (hh : ∀ i, 0 ≤ h i)
    (hkT : ∀ i, (k i : ℝ) * h i ≤ T) {m : ℕ} (hm : 0 < m) :
    MomentBound stdNormalSeq (fun i z => s₀ * ∏ j ∈ range (k i), gbmExpFactor r σ (h i) (z j) -
      s₀ * ∏ j ∈ range (k i), gbmMilFactor r σ (h i) (z j)) m (fun i => h i ^ (2 * m)) := by
  refine ⟨gbmMilMomentConst m r σ T s₀, gbmMilMomentConst_nonneg m r σ s₀ hT,
    fun i => ⟨?_, ?_⟩⟩
  · simp_rw [mul_sub_mul_pow_two_mul]
    exact (integrable_pow_prod_sub_prod (measurable_gbmExpFactor r σ _)
      (measurable_gbmMilFactor r σ _) (even_two_mul m) (integrable_gbmExpFactor_pow r σ _ _)
      (integrable_gbmMilFactor_pow r σ (hh i) m) _).const_mul _
  · have h1 := gbm_mil_moment_error_le r σ s₀ (hh i) (k i) (hkT i) hm
    simp_rw [gbmExp_eq_prod, milsteinPath_gbm] at h1
    exact h1

/-- One exact coarse step is two exact fine steps: `e^{(r−σ²/2)2h + σ√(2h)(x+y)/√2} =
e^{(r−σ²/2)h + σ√h x} e^{(r−σ²/2)h + σ√h y}` (Giles 2015, §5.1: "summing the Brownian increments
for the fine path timesteps to obtain the Brownian increments for the coarse timesteps"). -/
lemma gbmExpFactor_two_mul_pairAvg (r σ h : ℝ) (z : ℕ → ℝ) (j : ℕ) :
    gbmExpFactor r σ (2 * h) (pairAvg z j) =
      gbmExpFactor r σ h (z (2 * j)) * gbmExpFactor r σ h (z (2 * j + 1)) := by
  unfold gbmExpFactor pairAvg
  rw [← Real.exp_add, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) h]
  congr 1
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The exact solution driven by the summed increments at the coarse time `n (2h)` is the exact
solution driven by the fine increments at the fine time `2n h` (Giles 2015, §5.1). -/
lemma prod_gbmExpFactor_pairAvg (r σ h : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    ∏ j ∈ range n, gbmExpFactor r σ (2 * h) (pairAvg z j) =
      ∏ i ∈ range (2 * n), gbmExpFactor r σ h (z i) := by
  induction n with
  | zero => simp only [range_zero, prod_empty, mul_zero]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, gbmExpFactor_two_mul_pairAvg r σ h,
      show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ]
    ring

/-- `pairAvg z j` depends only on `z (2j)`, `z (2j + 1)` (the coarse increments are the sums of
two fine ones, Giles 2015, §5.1, p. 29, and §5.2, p. 36, l. 1560–1563). -/
lemma pairAvg_eq_of_eq_lt {z z' : ℕ → ℝ} {n : ℕ} (h : ∀ j < 2 * n, z j = z' j) {j : ℕ}
    (hj : j < n) : pairAvg z j = pairAvg z' j := by
  unfold pairAvg
  rw [h (2 * j) (by omega), h (2 * j + 1) (by omega)]

/-- **The coarse Milstein error of GBM in `L^{2m}`** (Giles 2015, §5.2, p. 35, l. 1499–1500, for the
coarse path driven by the summed increments `pairAvg`): for coarse grid times `k_i (2h_i) ≤ T`,
`E[(S_{t_{2k}} − Ŝ^c_k)^{2m}] ≤ C_m(T) (2h_i)^{2m}`, where `S_{t_{2k}}` is the exact solution at
the fine time `2k h_i` driven by the fine increments (`prod_gbmExpFactor_pairAvg`) and `Ŝ^c_k` the
Milstein value after `k` coarse steps (`measurePreserving_pairAvg`). -/
lemma momentBound_gbmMil_coarse_err (hT : 0 ≤ T) {h : ι → ℝ} {k : ι → ℕ} (hh : ∀ i, 0 ≤ h i)
    (hkT : ∀ i, (k i : ℝ) * (2 * h i) ≤ T) {m : ℕ} (hm : 0 < m) :
    MomentBound stdNormalSeq
      (fun i z => s₀ * ∏ j ∈ range (2 * k i), gbmExpFactor r σ (h i) (z j) -
        s₀ * ∏ j ∈ range (k i), gbmMilFactor r σ (2 * h i) (pairAvg z j)) m
      (fun i => h i ^ (2 * m)) := by
  obtain ⟨C, hC, hb⟩ := momentBound_gbmMil_err r σ s₀ hT (h := fun i => 2 * h i) (k := k)
    (fun i => by have := hh i; positivity) hkT hm
  refine ⟨C * 2 ^ (2 * m), by positivity, fun i => ?_⟩
  obtain ⟨hi, hle⟩ := hb i
  have e : (fun z : ℕ → ℝ => (s₀ * ∏ j ∈ range (2 * k i), gbmExpFactor r σ (h i) (z j) -
      s₀ * ∏ j ∈ range (k i), gbmMilFactor r σ (2 * h i) (pairAvg z j)) ^ (2 * m)) =
      fun z => (fun w : ℕ → ℝ => (s₀ * ∏ j ∈ range (k i), gbmExpFactor r σ (2 * h i) (w j) -
        s₀ * ∏ j ∈ range (k i), gbmMilFactor r σ (2 * h i) (w j)) ^ (2 * m)) (pairAvg z) := by
    funext z
    simp only [prod_gbmExpFactor_pairAvg r σ (h i)]
  rw [e]
  refine ⟨(measurePreserving_pairAvg.integrable_comp hi.aestronglyMeasurable).2 hi, ?_⟩
  rw [integral_comp_of_measurePreserving measurePreserving_pairAvg hi.aestronglyMeasurable]
  refine hle.trans (le_of_eq ?_)
  ring

/-- **Moments of an affine function of a Gaussian, uniformly** (Giles 2015, §5.1–§5.2: the
Euler–Maruyama step `1 + rh + σ√h Z` and its variants): if `|a_i| ≤ A` with `1 ≤ A` and
`s_i² ≤ S`, then `E[(a_i + s_i Z)^{2m}] ≤ A^{2m} e^{(2m)² S/2}` (`abs_integral_affine_pow_le`). -/
lemma momentBound_affine_gaussian {a s : ι → ℝ} {A S : ℝ} (hA : 1 ≤ A) (ha : ∀ i, |a i| ≤ A)
    (hs : ∀ i, s i ^ 2 ≤ S) (m : ℕ) :
    MomentBound (gaussianReal 0 1) (fun i x => a i + s i * x) m (fun _ => 1) := by
  have hA0 : 0 ≤ A ^ (2 * m) := pow_nonneg (by linarith) _
  refine ⟨A ^ (2 * m) * Real.exp (((2 * m : ℕ) : ℝ) ^ 2 * S / 2),
    mul_nonneg hA0 (Real.exp_pos _).le, fun i => ⟨integrable_affine_pow_gaussian _ _ _, ?_⟩⟩
  rw [mul_one]
  refine (le_abs_self _).trans ((abs_integral_affine_pow_le hA (ha i) (2 * m)).trans ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hA0
  have := hs i
  have h2 : (0 : ℝ) ≤ ((2 * m : ℕ) : ℝ) ^ 2 := sq_nonneg _
  nlinarith

/-- **One exact step against one Euler–Maruyama step in `L^{2m}`** (Giles 2015, §5.1): for
`0 ≤ h_i ≤ T`, `E[(e^{(r−σ²/2)h + σ√h Z} − (1 + rh + σ√h Z))^{2m}] ≤ e^{ωT} E_{2m} h_i^{2m}`
(`gbm_em_onestep_le` with `k = 2m`). -/
lemma momentBound_gbmExp_sub_EM (hT : 0 ≤ T) {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i)
    (hhT : ∀ i, h i ≤ T) {m : ℕ} (hm : 0 < m) :
    MomentBound (gaussianReal 0 1)
      (fun i x => gbmExpFactor r σ (h i) x - gbmEMFactor r σ (h i) x) m
      (fun i => h i ^ (2 * m)) := by
  have hE : 0 ≤ gbmEMStepConst m r σ T (2 * m) := by
    unfold gbmEMStepConst
    positivity
  refine ⟨Real.exp (gbmLpRate m r σ * T) * gbmEMStepConst m r σ T (2 * m),
    mul_nonneg (Real.exp_pos _).le hE, fun i => ⟨?_, ?_⟩⟩
  · have hneg : Integrable (fun x => (-gbmEMFactor r σ (h i) x) ^ (2 * m)) (gaussianReal 0 1) := by
      simp only [(even_two_mul m).neg_pow]
      exact integrable_gbmEMFactor_pow r σ (hh i) m
    have h1 := (integrable_integral_add_pow_two_mul (μ := gaussianReal 0 1)
      (g := fun x => -gbmEMFactor r σ (h i) x)
      (measurable_gbmExpFactor r σ (h i)) (measurable_gbmEMFactor r σ (h i)).neg
      (integrable_gbmExpFactor_pow r σ _ (2 * m)) hneg).1
    simpa only [← sub_eq_add_neg] using h1
  · have h1 := gbm_em_onestep_le r σ (hh i) (hhT i) (m := m) (k := 2 * m) (by omega) le_rfl
    rw [Nat.sub_self] at h1
    simp only [pow_zero, mul_one] at h1
    have e : ∀ x, (gbmExpFactor r σ (h i) x - gbmEMFactor r σ (h i) x) ^ (2 * m) =
        (gbmEMFactor r σ (h i) x - gbmExpFactor r σ (h i) x) ^ (2 * m) := fun x => by
      rw [← (even_two_mul m).neg_pow, neg_sub]
    simp only [e]
    refine (le_abs_self _).trans (h1.trans ?_)
    have hexp : Real.exp (gbmLpRate m r σ * h i) ≤ Real.exp (gbmLpRate m r σ * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hhT i) (gbmLpRate_nonneg m r σ))
    have hp : 0 ≤ h i ^ (2 * m) := pow_nonneg (hh i) _
    calc Real.exp (gbmLpRate m r σ * h i) * gbmEMStepConst m r σ T (2 * m) * h i ^ (2 * m)
        ≤ Real.exp (gbmLpRate m r σ * T) * gbmEMStepConst m r σ T (2 * m) * h i ^ (2 * m) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hE) hp
      _ = _ := rfl

/-- **The Euler–Maruyama increment `rh + σ√h Z` in `L^{2m}`** (Giles 2015, §5.1):
`E[(1 + rh_i + σ√h_i Z − 1)^{2m}] = O(h_i^m)` uniformly for `0 ≤ h_i ≤ T`. -/
lemma momentBound_gbmEM_sub_one {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i)
    (hhT : ∀ i, h i ≤ T) (m : ℕ) :
    MomentBound (gaussianReal 0 1) (fun i x => gbmEMFactor r σ (h i) x - 1) m
      (fun i => h i ^ m) := by
  have hA : 1 ≤ 1 + |r| * Real.sqrt T := by
    have := Real.sqrt_nonneg T
    nlinarith [abs_nonneg r]
  have ha : ∀ i, |r * Real.sqrt (h i)| ≤ 1 + |r| * Real.sqrt T := fun i => by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hhT i)) (abs_nonneg r)
    linarith
  have h1 := (momentBound_affine_gaussian (a := fun i => r * Real.sqrt (h i))
    (s := fun _ => σ) hA ha (fun _ => le_rfl) m).const_mul (fun i => Real.sqrt (h i))
  refine (h1.congr fun i x => ?_).mono (K := 1) zero_le_one fun i => ?_
  · have hs := Real.mul_self_sqrt (hh i)
    unfold gbmEMFactor
    linear_combination r * hs
  · rw [mul_one, one_mul, pow_mul, Real.sq_sqrt (hh i)]

/-- `(S_{t_k})`-type products depend only on the first `2n` increments through `pairAvg`
(Giles 2015, §5.1). -/
lemma prod_pairAvg_eq_of_eq_lt (F : ℝ → ℝ) {n : ℕ} {z z' : ℕ → ℝ}
    (h : ∀ j < 2 * n, z j = z' j) :
    ∏ j ∈ range n, F (pairAvg z j) = ∏ j ∈ range n, F (pairAvg z' j) :=
  prod_congr rfl fun j hj => by rw [pairAvg_eq_of_eq_lt h (mem_range.1 hj)]

/-- **One exact step against `1` in `L^{2m}`** (Giles 2015, §5.1):
`E[(e^{(r−σ²/2)h + σ√h Z} − 1)^{2m}] = O(h_i^m)` uniformly for `0 ≤ h_i ≤ T` (the exact step
minus the Euler–Maruyama step is `O(h)`, the Euler–Maruyama increment `O(√h)`). -/
lemma momentBound_gbmExp_sub_one (hT : 0 ≤ T) {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i)
    (hhT : ∀ i, h i ≤ T) {m : ℕ} (hm : 0 < m) :
    MomentBound (gaussianReal 0 1) (fun i x => gbmExpFactor r σ (h i) x - 1) m
      (fun i => h i ^ m) := by
  have h1 := (momentBound_gbmExp_sub_EM r σ hT hh hhT hm).mono (K := T ^ m) (by positivity)
    (ρ' := fun i => h i ^ m) fun i => by
      rw [show 2 * m = m + m by ring, pow_add]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hh i) (hhT i) m) (pow_nonneg (hh i) _)
  refine (h1.add (momentBound_gbmEM_sub_one r σ hh hhT m)
    (fun i => (measurable_gbmExpFactor r σ (h i)).sub (measurable_gbmEMFactor r σ (h i)))
    (fun i => (measurable_gbmEMFactor r σ (h i)).sub_const 1)).congr fun i x => ?_
  ring

end GBMBounds

/-! ### The levels -/

/-- `2^{ℓ+1} − 1 = 2(2^ℓ − 1) + 1`: the fine path one step before maturity on level `ℓ + 1`
(Giles 2015, §5.2, p. 36, l. 1544–1546: `Ŝ_{N−1}`). -/
lemma two_pow_succ_sub_one_eq (ℓ : ℕ) : 2 ^ (ℓ + 1) - 1 = 2 * (2 ^ ℓ - 1) + 1 := by
  have := Nat.one_le_two_pow (n := ℓ)
  rw [pow_succ]
  omega

/-- `2^{ℓ+1} − 2 = 2(2^ℓ − 1)`: the second last fine step on level `ℓ + 1` (Giles 2015, §5.2,
p. 36, l. 1560–1563: "the second last fine timestep"). -/
lemma two_pow_succ_sub_two_eq (ℓ : ℕ) : 2 ^ (ℓ + 1) - 2 = 2 * (2 ^ ℓ - 1) := by
  have := Nat.one_le_two_pow (n := ℓ)
  rw [pow_succ]
  omega

/-- `2^{ℓ+1} = 2(2^ℓ − 1) + 1 + 1`: the fine steps of level `ℓ + 1` (Giles 2015, §5.2, p. 36). -/
lemma two_pow_succ_eq_add_two (ℓ : ℕ) : 2 ^ (ℓ + 1) = 2 * (2 ^ ℓ - 1) + 1 + 1 := by
  have := Nat.one_le_two_pow (n := ℓ)
  rw [pow_succ]
  omega

/-- `2^ℓ = (2^ℓ − 1) + 1`: the fine steps of level `ℓ` (Giles 2015, §5.2, p. 36). -/
lemma two_pow_eq_sub_one_add_one (ℓ : ℕ) : 2 ^ ℓ = (2 ^ ℓ - 1) + 1 := by
  have := Nat.one_le_two_pow (n := ℓ)
  omega

/-- `h_ℓ = 2 h_{ℓ+1}` for `h_ℓ = T 2^{−ℓ}` (Giles 2015, §5.2, p. 36, l. 1566–1569: `h_{ℓ−1}` and
`h_ℓ` in the coarse payoff). -/
lemma div_two_pow_eq_two_mul (T : ℝ) (ℓ : ℕ) : T / 2 ^ ℓ = 2 * (T / 2 ^ (ℓ + 1)) := by
  rw [pow_succ]
  field_simp

/-- `k h_ℓ ≤ T` for `k ≤ 2^ℓ`: the grid times of level `ℓ` lie in `[0, T]` (Giles 2015, §5.2). -/
lemma natCast_mul_div_two_pow_le {T : ℝ} (hT : 0 ≤ T) {k ℓ : ℕ} (hk : k ≤ 2 ^ ℓ) :
    (k : ℝ) * (T / 2 ^ ℓ) ≤ T := by
  have h1 : (k : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast hk
  calc (k : ℝ) * (T / 2 ^ ℓ) ≤ 2 ^ ℓ * (T / 2 ^ ℓ) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = T := by field_simp

/-- The fine Milstein path of GBM one step before maturity on level `ℓ + 1`, in product form
(Giles 2015, §5.2; `milsteinPath_gbm`). -/
lemma milsteinPath_fine_eq_prod (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z (2 ^ (ℓ + 1) - 1) =
      s₀ * ∏ j ∈ range (2 * (2 ^ ℓ - 1) + 1), gbmMilFactor r σ (T / 2 ^ (ℓ + 1)) (z j) := by
  rw [milsteinPath_gbm, two_pow_succ_sub_one_eq]

/-- The coarse Milstein path of GBM two fine steps before maturity on level `ℓ + 1`, in product
form (Giles 2015, §5.2; `milsteinPath_gbm`). -/
lemma milsteinPath_coarse_eq_prod (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) =
      s₀ * ∏ j ∈ range (2 ^ ℓ - 1), gbmMilFactor r σ (2 * (T / 2 ^ (ℓ + 1))) (pairAvg z j) := by
  rw [milsteinPath_gbm, div_two_pow_eq_two_mul T ℓ]

/-- The fine Milstein path of GBM one step before maturity on level `ℓ`, in product form (Giles
2015, §5.2, p. 36, l. 1544–1546; `milsteinPath_gbm`). -/
lemma milsteinPath_level_eq_prod (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1) =
      s₀ * ∏ j ∈ range (2 ^ ℓ - 1), gbmMilFactor r σ (T / 2 ^ ℓ) (z j) :=
  milsteinPath_gbm r σ _ s₀ z _

/-! ### The conditional means and standard deviations match to within `O(h)` -/

section Match

variable (r σ s₀ : ℝ) {T : ℝ}

/-- The summed increments `pairAvg` are a measurable map (Giles 2015, §5.1). -/
lemma measurable_pairAvg : Measurable pairAvg := measurePreserving_pairAvg.measurable

/-- `2(2^ℓ − 1) + 1 ≤ 2^{ℓ+1}`: `t_{N−1} ≤ T` on level `ℓ + 1` (Giles 2015, §5.2). -/
lemma two_mul_two_pow_sub_one_add_one_le (ℓ : ℕ) : 2 * (2 ^ ℓ - 1) + 1 ≤ 2 ^ (ℓ + 1) := by
  have := Nat.one_le_two_pow (n := ℓ)
  rw [pow_succ]
  omega

/-- `2(2^ℓ − 1) ≤ 2^{ℓ+1}`: `t_{N−2} ≤ T` on level `ℓ + 1` (Giles 2015, §5.2). -/
lemma two_mul_two_pow_sub_one_le (ℓ : ℕ) : 2 * (2 ^ ℓ - 1) ≤ 2 ^ (ℓ + 1) := by
  have := Nat.one_le_two_pow (n := ℓ)
  rw [pow_succ]
  omega

/-- `|1 + r h| ≤ 1 + |r| T` for `0 ≤ h ≤ T` (the drift factor of the last step, Giles 2015, §5.2,
p. 36, l. 1551–1555). -/
lemma abs_one_add_mul_le {h : ℝ} (hh : 0 ≤ h) (hhT : h ≤ T) : |1 + r * h| ≤ 1 + |r| * T := by
  refine (abs_add_le _ _).trans ?_
  rw [abs_one, abs_mul, abs_of_nonneg hh]
  have := mul_le_mul_of_nonneg_left hhT (abs_nonneg r)
  linarith

/-- `c^{2m} ≤ K^{2m}` for `|c| ≤ K` (bookkeeping for the `L^{2m}` bounds, Giles 2015, §5.2). -/
lemma pow_two_mul_le_of_abs_le {c K : ℝ} (hc : |c| ≤ K) (m : ℕ) : c ^ (2 * m) ≤ K ^ (2 * m) := by
  rw [← (even_two_mul m).pow_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hc _

/-- **The conditional means match to within `O(h)` in every `L^{2m}`, in product form** (Giles
2015, §5.2, p. 36, l. 1563–1566).  With `h = h_{ℓ+1}`, `n = 2^ℓ − 1`, `S_k` the exact solution at
the fine time `kh`, `X = Ŝ^f_{2n+1}` and `Y = Ŝ^c_n` (coarse, driven by `pairAvg`),
`m_f − m_c = −(1 + rh)(S_{2n+1} − X) + (S_{2n} − Y)(1 + 2rh + σ√h Z_{2n}) +
S_{2n}((1 + rh)(A − B) + rh(B − 1))(Z_{2n})`, `A`, `B` the exact and the Euler–Maruyama step. -/
lemma momentBound_condMean_diff (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m) :
    MomentBound stdNormalSeq
      (fun ℓ z => gbmCondMeanFine r σ T s₀ (ℓ + 1) z - gbmCondMeanCoarse r σ T s₀ ℓ z) m
      (fun ℓ => (T / 2 ^ (ℓ + 1)) ^ (2 * m)) := by
  have hmA : ∀ h, Measurable (gbmExpFactor r σ h) := measurable_gbmExpFactor r σ
  have hmM : ∀ h, Measurable (gbmMilFactor r σ h) := measurable_gbmMilFactor r σ
  have hmB : ∀ h, Measurable (gbmEMFactor r σ h) := measurable_gbmEMFactor r σ
  have hmP : Measurable pairAvg := measurable_pairAvg
  have hh : ∀ ℓ : ℕ, 0 ≤ T / 2 ^ (ℓ + 1) := fun ℓ => by positivity
  have hhT : ∀ ℓ : ℕ, T / 2 ^ (ℓ + 1) ≤ T := fun ℓ => div_le_self hT (one_le_pow₀ (by norm_num))
  have hk1 : ∀ ℓ : ℕ, ((2 * (2 ^ ℓ - 1) + 1 : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)) ≤ T := fun ℓ =>
    natCast_mul_div_two_pow_le hT (two_mul_two_pow_sub_one_add_one_le ℓ)
  have hk0 : ∀ ℓ : ℕ, ((2 * (2 ^ ℓ - 1) : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)) ≤ T := fun ℓ =>
    natCast_mul_div_two_pow_le hT (two_mul_two_pow_sub_one_le ℓ)
  have hkc : ∀ ℓ : ℕ, ((2 ^ ℓ - 1 : ℕ) : ℝ) * (2 * (T / 2 ^ (ℓ + 1))) ≤ T := fun ℓ => by
    rw [← div_two_pow_eq_two_mul]
    exact natCast_mul_div_two_pow_le hT (Nat.sub_le _ _)
  have hm2 : ∀ ℓ : ℕ, 0 ≤ (T / 2 ^ (ℓ + 1)) ^ (2 * m) := fun ℓ => pow_nonneg (hh ℓ) _
  -- the first piece: the fine Milstein error at `t_{2n+1}`
  have P1 := ((momentBound_gbmMil_err r σ s₀ hT hh hk1 hm).const_mul
    (fun ℓ => -(1 + r * (T / 2 ^ (ℓ + 1))))).mono (K := (1 + |r| * T) ^ (2 * m)) (by positivity)
    (ρ' := fun ℓ => (T / 2 ^ (ℓ + 1)) ^ (2 * m)) fun ℓ => mul_le_mul_of_nonneg_right
      (pow_two_mul_le_of_abs_le (by rw [abs_neg]; exact abs_one_add_mul_le r (hh ℓ) (hhT ℓ)) m)
      (hm2 ℓ)
  -- the second piece: the coarse Milstein error at `t_{2n}` times the first half of the last
  -- coarse Euler–Maruyama step
  have hA : (1 : ℝ) ≤ 1 + 2 * |r| * T := by have := abs_nonneg r; nlinarith
  have G1 := momentBound_affine_gaussian (a := fun ℓ : ℕ => 1 + 2 * r * (T / 2 ^ (ℓ + 1)))
    (s := fun ℓ : ℕ => σ * Real.sqrt (T / 2 ^ (ℓ + 1))) (S := σ ^ 2 * T) hA
    (fun ℓ => by
      refine (abs_add_le _ _).trans ?_
      rw [abs_one, abs_mul, abs_mul, abs_of_nonneg (hh ℓ), abs_two]
      have := mul_le_mul_of_nonneg_left (hhT ℓ) (abs_nonneg r)
      linarith)
    (fun ℓ => by
      rw [mul_pow, Real.sq_sqrt (hh ℓ)]
      exact mul_le_mul_of_nonneg_left (hhT ℓ) (sq_nonneg σ)) m
  have P2 := ((momentBound_gbmMil_coarse_err r σ s₀ hT hh hkc hm).mul_eval
    (n := fun ℓ => 2 * (2 ^ ℓ - 1)) G1 (fun ℓ => by fun_prop)
    (fun ℓ z z' hzz => by rw [prod_range_eq_of_eq_lt _ hzz, prod_pairAvg_eq_of_eq_lt _ hzz])
    (fun ℓ => by fun_prop)).mono (K := 1) zero_le_one
    (ρ' := fun ℓ => (T / 2 ^ (ℓ + 1)) ^ (2 * m)) fun ℓ => by rw [mul_one, one_mul]
  -- the third piece: the exact solution at `t_{2n}` times the one-step mismatch
  have G2a := ((momentBound_gbmExp_sub_EM r σ hT hh hhT hm).const_mul
    (fun ℓ => 1 + r * (T / 2 ^ (ℓ + 1)))).mono (K := (1 + |r| * T) ^ (2 * m)) (by positivity)
    (ρ' := fun ℓ => (T / 2 ^ (ℓ + 1)) ^ (2 * m)) fun ℓ => mul_le_mul_of_nonneg_right
      (pow_two_mul_le_of_abs_le (abs_one_add_mul_le r (hh ℓ) (hhT ℓ)) m) (hm2 ℓ)
  have G2b := ((momentBound_gbmEM_sub_one r σ hh hhT m).const_mul
    (fun ℓ => r * (T / 2 ^ (ℓ + 1)))).mono (K := r ^ (2 * m) * T ^ m)
    ((even_two_mul m).pow_nonneg r |>.trans_eq' rfl |> fun h => mul_nonneg h (pow_nonneg hT _))
    (ρ' := fun ℓ => (T / 2 ^ (ℓ + 1)) ^ (2 * m)) fun ℓ => by
      rw [mul_pow]
      have h1 := pow_le_pow_left₀ (hh ℓ) (hhT ℓ) m
      have h2 : 0 ≤ r ^ (2 * m) * (T / 2 ^ (ℓ + 1)) ^ (2 * m) :=
        mul_nonneg ((even_two_mul m).pow_nonneg r) (hm2 ℓ)
      calc r ^ (2 * m) * (T / 2 ^ (ℓ + 1)) ^ (2 * m) * (T / 2 ^ (ℓ + 1)) ^ m
          ≤ r ^ (2 * m) * (T / 2 ^ (ℓ + 1)) ^ (2 * m) * T ^ m := mul_le_mul_of_nonneg_left h1 h2
        _ = _ := by ring
  have G2 := G2a.add G2b
    (fun ℓ => ((measurable_gbmExpFactor r σ _).sub (measurable_gbmEMFactor r σ _)).const_mul _)
    (fun ℓ => ((measurable_gbmEMFactor r σ _).sub_const 1).const_mul _)
  have P3 := ((momentBound_gbmExp_prod r σ s₀ hh hk0 m).mul_eval
    (n := fun ℓ => 2 * (2 ^ ℓ - 1)) G2 (fun ℓ => by fun_prop)
    (fun ℓ z z' hzz => by rw [prod_range_eq_of_eq_lt _ hzz])
    (fun ℓ => by fun_prop)).mono (K := 1) zero_le_one
    (ρ' := fun ℓ => (T / 2 ^ (ℓ + 1)) ^ (2 * m)) fun ℓ => by simp only [one_mul, le_refl]
  refine ((P1.add P2 (fun ℓ => by fun_prop) (fun ℓ => by fun_prop)).add P3
    (fun ℓ => by fun_prop) (fun ℓ => by fun_prop)).congr fun ℓ z => ?_
  unfold gbmCondMeanFine gbmCondMeanCoarse
  rw [milsteinPath_fine_eq_prod, milsteinPath_coarse_eq_prod, two_pow_succ_sub_two_eq,
    div_two_pow_eq_two_mul T ℓ,
    Finset.prod_range_succ (fun j => gbmExpFactor r σ (T / 2 ^ (ℓ + 1)) (z j))]
  unfold gbmEMFactor
  ring

/-- `h^{2m} ≤ T^m h^m` for `0 ≤ h ≤ T` (an `O(h)` bound in `L^{2m}` is also `O(√h)`; Giles 2015,
§5.2). -/
lemma pow_two_mul_le_pow_mul_pow {h : ℝ} (hh : 0 ≤ h) (hhT : h ≤ T) (m : ℕ) :
    h ^ (2 * m) ≤ T ^ m * h ^ m := by
  rw [show 2 * m = m + m by ring, pow_add]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh hhT m) (pow_nonneg hh _)

/-- `∏_{j<2^{ℓ+1}} f(j) = (∏_{j<2(2^ℓ−1)+1} f(j)) f(2(2^ℓ−1)+1)`: the last fine step on level
`ℓ + 1` (Giles 2015, §5.2, p. 36). -/
lemma prod_range_two_pow_succ_eq (f : ℕ → ℝ) (ℓ : ℕ) :
    ∏ j ∈ range (2 ^ (ℓ + 1)), f j =
      (∏ j ∈ range (2 * (2 ^ ℓ - 1) + 1), f j) * f (2 * (2 ^ ℓ - 1) + 1) := by
  rw [two_pow_succ_eq_add_two, prod_range_succ]

/-- `∏_{j<2^ℓ} f(j) = (∏_{j<2^ℓ−1} f(j)) f(2^ℓ − 1)`: the last fine step on level `ℓ` (Giles 2015,
§5.2, p. 36). -/
lemma prod_range_two_pow_eq (f : ℕ → ℝ) (ℓ : ℕ) :
    ∏ j ∈ range (2 ^ ℓ), f j = (∏ j ∈ range (2 ^ ℓ - 1), f j) * f (2 ^ ℓ - 1) := by
  conv_lhs => rw [two_pow_eq_sub_one_add_one ℓ]
  exact prod_range_succ f _

/-- `| |σX| c − |σY| c | ≤ |σ c| |X − Y|` for `c ≥ 0` (the standard deviations `|b(S)| √h` of
Giles 2015, §5.2, p. 36, l. 1563–1566). -/
lemma abs_abs_mul_sub_abs_mul_le (σ X Y : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    |(|σ * X| * c - |σ * Y| * c)| ≤ |σ * c| * |X - Y| := by
  rw [← sub_mul, abs_mul, abs_of_nonneg hc, abs_mul σ c, abs_of_nonneg hc]
  calc |(|σ * X| - |σ * Y|)| * c ≤ |σ * X - σ * Y| * c :=
        mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le_abs_sub _ _) hc
    _ = |σ| * c * |X - Y| := by rw [← mul_sub, abs_mul]; ring

/-- **The fine path one fine step before maturity and the coarse path two fine steps before
maturity are `O(√h)` apart in every `L^{2m}`** (Giles 2015, §5.2), in product form:
`X − Y = −(S_{2n+1} − X) + S_{2n}(A(Z_{2n}) − 1) + (S_{2n} − Y)`. -/
lemma momentBound_fine_sub_coarse (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m) :
    MomentBound stdNormalSeq
      (fun ℓ z => s₀ * ∏ j ∈ range (2 * (2 ^ ℓ - 1) + 1),
          gbmMilFactor r σ (T / 2 ^ (ℓ + 1)) (z j) -
        s₀ * ∏ j ∈ range (2 ^ ℓ - 1), gbmMilFactor r σ (2 * (T / 2 ^ (ℓ + 1))) (pairAvg z j)) m
      (fun ℓ => (T / 2 ^ (ℓ + 1)) ^ m) := by
  have hmA : ∀ h, Measurable (gbmExpFactor r σ h) := measurable_gbmExpFactor r σ
  have hmM : ∀ h, Measurable (gbmMilFactor r σ h) := measurable_gbmMilFactor r σ
  have hmB : ∀ h, Measurable (gbmEMFactor r σ h) := measurable_gbmEMFactor r σ
  have hmP : Measurable pairAvg := measurable_pairAvg
  have hh : ∀ ℓ : ℕ, 0 ≤ T / 2 ^ (ℓ + 1) := fun ℓ => by positivity
  have hhT : ∀ ℓ : ℕ, T / 2 ^ (ℓ + 1) ≤ T := fun ℓ => div_le_self hT (one_le_pow₀ (by norm_num))
  have hk1 : ∀ ℓ : ℕ, ((2 * (2 ^ ℓ - 1) + 1 : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)) ≤ T := fun ℓ =>
    natCast_mul_div_two_pow_le hT (two_mul_two_pow_sub_one_add_one_le ℓ)
  have hk0 : ∀ ℓ : ℕ, ((2 * (2 ^ ℓ - 1) : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)) ≤ T := fun ℓ =>
    natCast_mul_div_two_pow_le hT (two_mul_two_pow_sub_one_le ℓ)
  have hkc : ∀ ℓ : ℕ, ((2 ^ ℓ - 1 : ℕ) : ℝ) * (2 * (T / 2 ^ (ℓ + 1))) ≤ T := fun ℓ => by
    rw [← div_two_pow_eq_two_mul]
    exact natCast_mul_div_two_pow_le hT (Nat.sub_le _ _)
  have hmono : ∀ ℓ : ℕ, (T / 2 ^ (ℓ + 1)) ^ (2 * m) ≤ T ^ m * (T / 2 ^ (ℓ + 1)) ^ m := fun ℓ =>
    pow_two_mul_le_pow_mul_pow (hh ℓ) (hhT ℓ) m
  have Q1 := (momentBound_gbmMil_err r σ s₀ hT hh hk1 hm).neg.mono (K := T ^ m) (by positivity)
    hmono
  have Q2 := ((momentBound_gbmExp_prod r σ s₀ hh hk0 m).mul_eval
    (n := fun ℓ => 2 * (2 ^ ℓ - 1)) (momentBound_gbmExp_sub_one r σ hT hh hhT hm)
    (fun ℓ => by fun_prop) (fun ℓ z z' hzz => by rw [prod_range_eq_of_eq_lt _ hzz])
    (fun ℓ => by fun_prop)).mono (K := 1) zero_le_one
    (ρ' := fun ℓ => (T / 2 ^ (ℓ + 1)) ^ m) fun ℓ => by simp only [one_mul, le_refl]
  have Q3 := (momentBound_gbmMil_coarse_err r σ s₀ hT hh hkc hm).mono (K := T ^ m) (by positivity)
    hmono
  refine ((Q1.add Q2 (fun ℓ => by fun_prop) (fun ℓ => by fun_prop)).add Q3
    (fun ℓ => by fun_prop) (fun ℓ => by fun_prop)).congr fun ℓ z => ?_
  rw [Finset.prod_range_succ (fun j => gbmExpFactor r σ (T / 2 ^ (ℓ + 1)) (z j))]
  ring

/-- **The conditional standard deviations match to within `O(h)` in every `L^{2m}`** (Giles 2015,
§5.2, p. 36, l. 1563–1566): `|s_f − s_c| ≤ |σ| √h |X − Y|` and `X − Y = O(√h)`
(`momentBound_fine_sub_coarse`). -/
lemma momentBound_condStd_diff (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m) :
    MomentBound stdNormalSeq
      (fun ℓ z => gbmCondStdFine r σ T s₀ (ℓ + 1) z - gbmCondStdCoarse r σ T s₀ ℓ z) m
      (fun ℓ => (T / 2 ^ (ℓ + 1)) ^ (2 * m)) := by
  have hmA : ∀ h, Measurable (gbmExpFactor r σ h) := measurable_gbmExpFactor r σ
  have hmM : ∀ h, Measurable (gbmMilFactor r σ h) := measurable_gbmMilFactor r σ
  have hmB : ∀ h, Measurable (gbmEMFactor r σ h) := measurable_gbmEMFactor r σ
  have hmP : Measurable pairAvg := measurable_pairAvg
  have hh : ∀ ℓ : ℕ, 0 ≤ T / 2 ^ (ℓ + 1) := fun ℓ => by positivity
  refine ((momentBound_fine_sub_coarse r σ s₀ hT hm).of_abs_le
    (fun ℓ => σ * Real.sqrt (T / 2 ^ (ℓ + 1)))
    (g := fun ℓ z => gbmCondStdFine r σ T s₀ (ℓ + 1) z - gbmCondStdCoarse r σ T s₀ ℓ z)
    (fun ℓ => ?_) (fun ℓ z => ?_)).mono (K := σ ^ (2 * m)) ((even_two_mul m).pow_nonneg σ)
    (fun ℓ => le_of_eq ?_)
  · unfold gbmCondStdFine gbmCondStdCoarse
    simp only [milsteinPath_fine_eq_prod, milsteinPath_coarse_eq_prod]
    fun_prop
  · unfold gbmCondStdFine gbmCondStdCoarse
    rw [milsteinPath_fine_eq_prod, milsteinPath_coarse_eq_prod]
    exact abs_abs_mul_sub_abs_mul_le σ _ _ (Real.sqrt_nonneg _)
  · rw [mul_pow, pow_mul (Real.sqrt (T / 2 ^ (ℓ + 1))) 2 m, Real.sq_sqrt (hh ℓ)]
    ring

/-- **The fine path one step before maturity is `O(√h)` from `S_T` in every `L^{2m}`** (Giles
2015, §5.2): `S_T − X = (S_{2n+1} − X) + S_{2n+1}(A(Z_{2n+1}) − 1)` on level `ℓ + 1`. -/
lemma momentBound_gbmExact_sub_fine (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m) :
    MomentBound stdNormalSeq
      (fun ℓ z => gbmExact r σ T s₀ (ℓ + 1) z -
        s₀ * ∏ j ∈ range (2 * (2 ^ ℓ - 1) + 1), gbmMilFactor r σ (T / 2 ^ (ℓ + 1)) (z j)) m
      (fun ℓ => (T / 2 ^ (ℓ + 1)) ^ m) := by
  have hmA : ∀ h, Measurable (gbmExpFactor r σ h) := measurable_gbmExpFactor r σ
  have hmM : ∀ h, Measurable (gbmMilFactor r σ h) := measurable_gbmMilFactor r σ
  have hmB : ∀ h, Measurable (gbmEMFactor r σ h) := measurable_gbmEMFactor r σ
  have hmP : Measurable pairAvg := measurable_pairAvg
  have hh : ∀ ℓ : ℕ, 0 ≤ T / 2 ^ (ℓ + 1) := fun ℓ => by positivity
  have hhT : ∀ ℓ : ℕ, T / 2 ^ (ℓ + 1) ≤ T := fun ℓ => div_le_self hT (one_le_pow₀ (by norm_num))
  have hk1 : ∀ ℓ : ℕ, ((2 * (2 ^ ℓ - 1) + 1 : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)) ≤ T := fun ℓ =>
    natCast_mul_div_two_pow_le hT (two_mul_two_pow_sub_one_add_one_le ℓ)
  have R1 := (momentBound_gbmMil_err r σ s₀ hT hh hk1 hm).mono (K := T ^ m) (by positivity)
    (ρ' := fun ℓ => (T / 2 ^ (ℓ + 1)) ^ m) fun ℓ => pow_two_mul_le_pow_mul_pow (hh ℓ) (hhT ℓ) m
  have R2 := ((momentBound_gbmExp_prod r σ s₀ hh hk1 m).mul_eval
    (n := fun ℓ => 2 * (2 ^ ℓ - 1) + 1) (momentBound_gbmExp_sub_one r σ hT hh hhT hm)
    (fun ℓ => by fun_prop) (fun ℓ z z' hzz => by rw [prod_range_eq_of_eq_lt _ hzz])
    (fun ℓ => by fun_prop)).mono (K := 1) zero_le_one
    (ρ' := fun ℓ => (T / 2 ^ (ℓ + 1)) ^ m) fun ℓ => by simp only [one_mul, le_refl]
  refine (R1.add R2 (fun ℓ => by fun_prop) (fun ℓ => by fun_prop)).congr fun ℓ z => ?_
  rw [gbmExact_eq_prod, prod_range_two_pow_succ_eq]
  ring

/-- **The strong error of the Milstein path with an Euler–Maruyama last step in every `L^{2m}`**
(Giles 2015, §5.2, p. 35, l. 1499–1500 and p. 35, l. 1541–1544): on level `ℓ`,
`E[(S_T − Ŝ^f_N)^{2m}] = O(h_ℓ^{2m})`, from `S_T − X B = (S_{N−1} − X) B + S_{N−1}(A − B)` with the
exact step `A` and the Euler–Maruyama step `B` (an Euler–Maruyama step is `O(h)` from the exact
step in `L^{2m}`). -/
lemma momentBound_gbmExact_sub_milEM (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m) :
    MomentBound stdNormalSeq (fun ℓ z => gbmExact r σ T s₀ ℓ z - gbmMilEM r σ T s₀ ℓ z) m
      (fun ℓ => (T / 2 ^ ℓ) ^ (2 * m)) := by
  have hmA : ∀ h, Measurable (gbmExpFactor r σ h) := measurable_gbmExpFactor r σ
  have hmM : ∀ h, Measurable (gbmMilFactor r σ h) := measurable_gbmMilFactor r σ
  have hmB : ∀ h, Measurable (gbmEMFactor r σ h) := measurable_gbmEMFactor r σ
  have hmP : Measurable pairAvg := measurable_pairAvg
  have hh : ∀ ℓ : ℕ, 0 ≤ T / 2 ^ ℓ := fun ℓ => by positivity
  have hhT : ∀ ℓ : ℕ, T / 2 ^ ℓ ≤ T := fun ℓ => div_le_self hT (one_le_pow₀ (by norm_num))
  have hk : ∀ ℓ : ℕ, ((2 ^ ℓ - 1 : ℕ) : ℝ) * (T / 2 ^ ℓ) ≤ T := fun ℓ =>
    natCast_mul_div_two_pow_le hT (Nat.sub_le _ _)
  have hA : (1 : ℝ) ≤ 1 + |r| * T := by have := abs_nonneg r; nlinarith
  have B := momentBound_affine_gaussian (a := fun ℓ : ℕ => 1 + r * (T / 2 ^ ℓ))
    (s := fun ℓ : ℕ => σ * Real.sqrt (T / 2 ^ ℓ)) (S := σ ^ 2 * T) hA
    (fun ℓ => abs_one_add_mul_le r (hh ℓ) (hhT ℓ))
    (fun ℓ => by
      rw [mul_pow, Real.sq_sqrt (hh ℓ)]
      exact mul_le_mul_of_nonneg_left (hhT ℓ) (sq_nonneg σ)) m
  have W1 := ((momentBound_gbmMil_err r σ s₀ hT hh hk hm).mul_eval
    (n := fun ℓ => 2 ^ ℓ - 1) B (fun ℓ => by fun_prop)
    (fun ℓ z z' hzz => by rw [prod_range_eq_of_eq_lt _ hzz, prod_range_eq_of_eq_lt _ hzz])
    (fun ℓ => by fun_prop)).mono (K := 1) zero_le_one
    (ρ' := fun ℓ => (T / 2 ^ ℓ) ^ (2 * m)) fun ℓ => by rw [mul_one, one_mul]
  have W2 := ((momentBound_gbmExp_prod r σ s₀ hh hk m).mul_eval
    (n := fun ℓ => 2 ^ ℓ - 1) (momentBound_gbmExp_sub_EM r σ hT hh hhT hm)
    (fun ℓ => by fun_prop) (fun ℓ z z' hzz => by rw [prod_range_eq_of_eq_lt _ hzz])
    (fun ℓ => by fun_prop)).mono (K := 1) zero_le_one
    (ρ' := fun ℓ => (T / 2 ^ ℓ) ^ (2 * m)) fun ℓ => by simp only [one_mul, le_refl]
  refine (W1.add W2 (fun ℓ => by fun_prop) (fun ℓ => by fun_prop)).congr fun ℓ z => ?_
  unfold gbmMilEM emStep
  rw [milsteinPath_level_eq_prod, gbmExact_eq_prod, prod_range_two_pow_eq]
  unfold gbmEMFactor
  ring

end Match

/-! ### The difference of two smoothed payoffs -/

/-- **The standard Gaussian law has density at most `1/2`** (`φ ≤ 1/√(2π) < 1/2`; used for the
"bounded density" step of Giles 2015, §5.2, p. 36, l. 1575–1577). -/
lemma gaussianReal_le_half_smul_volume :
    gaussianReal 0 1 ≤ ENNReal.ofReal (1 / 2) • volume := by
  refine Measure.le_iff.2 fun A _ => ?_
  rw [gaussianReal_apply 0 one_ne_zero, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in A, gaussianPDF 0 1 x ≤ ∫⁻ _ in A, ENNReal.ofReal (1 / 2) := by
        refine lintegral_mono fun x => ?_
        rw [gaussianPDF]
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : gaussianPDFReal 0 1 x = Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) := by
          simp only [gaussianPDFReal, NNReal.coe_one, mul_one, Nat.ofNat_nonneg, Real.sqrt_mul,
            mul_inv_rev, sub_zero, div_eq_inv_mul, mul_neg]
        rw [e1]
        have h4 : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        have hpi : 2 ≤ Real.sqrt (2 * Real.pi) := by
          rw [← h4]
          exact Real.sqrt_le_sqrt (by nlinarith [Real.two_le_pi])
        have he : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Real.exp_pos (-x ^ 2 / 2)]
    _ = ENNReal.ofReal (1 / 2) * volume A := setLIntegral_const _ _

/-- `P(|Z − c| ≤ δ) ≤ δ` for `Z ∼ N(0,1)` (`gaussianReal_le_half_smul_volume`; Giles 2015, §5.2,
p. 36, l. 1575–1577). -/
lemma gaussianReal_real_abs_sub_le (c : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (gaussianReal 0 1).real {x | |x - c| ≤ δ} ≤ δ := by
  have h := measureReal_abs_sub_le_of_map_le (μ := gaussianReal 0 1) (X := fun x : ℝ => x)
    (ρ := 1 / 2) measurable_id (by norm_num)
    (by rw [Measure.map_id']; exact gaussianReal_le_half_smul_volume) c hδ
  linarith

/-- **Markov's inequality for an even moment**: `P(a < |f|) ≤ E[f^{2p}]/a^{2p}` for `a > 0` (the
tails of the `L^{2p}` estimates, Giles 2015, §5.2, p. 36, l. 1563–1577). -/
lemma measureReal_lt_abs_le_integral_pow_div {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} {p : ℕ} (hf : Integrable (fun ω => f ω ^ (2 * p)) μ) {a : ℝ}
    (ha : 0 < a) : μ.real {ω | a < |f ω|} ≤ (∫ ω, f ω ^ (2 * p) ∂μ) / a ^ (2 * p) := by
  have hE : Even (2 * p) := even_two_mul p
  have hint : Integrable (fun ω => |f ω - (fun _ => (0 : ℝ)) ω| ^ (2 * p)) μ := by
    simp only [sub_zero, hE.pow_abs]
    exact hf
  have h := measureReal_lt_abs_sub_le_div_pow (X := f) (Y := fun _ => 0) hint ha
  simp only [sub_zero, hE.pow_abs] at h
  exact h

/-- **The Gaussian tail from the even moments**: `P(t < |Z|) ≤ (2p − 1)!!/t^{2p}` for
`Z ∼ N(0,1)`, `t > 0` (`integral_pow_two_mul_gaussian`; both smoothed payoffs in the same tail of
`Φ`, Giles 2015, §5.2, p. 36, l. 1575–1577). -/
lemma gaussianReal_real_lt_abs_le (p : ℕ) {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real {x | t < |x|} ≤
      (Nat.doubleFactorial (2 * p - 1) : ℝ) / t ^ (2 * p) := by
  have h := measureReal_lt_abs_le_integral_pow_div (μ := gaussianReal 0 1) (f := fun x => x)
    (integrable_pow_gaussian (2 * p)) ht
  rwa [integral_pow_two_mul_gaussian] at h

/-- **Two smoothed digital payoffs differ by at most the probability of a thin window** (Giles 2015,
§5.2, p. 36, l. 1575–1577: "the difference in payoff between the coarse and fine paths near the
payoff discontinuity is `O(h^{1/2})`").  For `s₁, s₂ > 0`, `t ≥ 0`, `Z ∼ N(0,1)` and
`w = |m₁ − m₂| + t |s₁ − s₂|`: `Φ((m − K)/s) = P(m + sZ > K)`, the two events differ only where
`|m₁ + s₁Z − K| ≤ w` or `|Z| > t`, and the first has probability at most `w/s₁` (the density of
`Z` is at most `1/2`); if moreover `|m₁ − K| > w + t s₁`, the first is contained in `{|Z| > t}`.
So `|Φ((m₁ − K)/s₁) − Φ((m₂ − K)/s₂)| ≤ 2P(|Z| > t) + w/s₁`, and `≤ 2P(|Z| > t)` when
`|m₁ − K| > w + t s₁`. -/
lemma abs_cdf_div_sub_cdf_div_le {m₁ m₂ s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (K : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    |cdf (gaussianReal 0 1) ((m₁ - K) / s₁) - cdf (gaussianReal 0 1) ((m₂ - K) / s₂)| ≤
        2 * (gaussianReal 0 1).real {x | t < |x|} +
          (|m₁ - m₂| + t * |s₁ - s₂|) / s₁ ∧
      (|m₁ - m₂| + t * |s₁ - s₂| + t * s₁ < |m₁ - K| →
        |cdf (gaussianReal 0 1) ((m₁ - K) / s₁) - cdf (gaussianReal 0 1) ((m₂ - K) / s₂)| ≤
          2 * (gaussianReal 0 1).real {x | t < |x|}) := by
  set w := |m₁ - m₂| + t * |s₁ - s₂| with hw
  set τ := (gaussianReal 0 1).real {x | t < |x|} with hτ
  have hτ0 : 0 ≤ τ := measureReal_nonneg
  have hX : Measurable fun x : ℝ => m₁ + s₁ * x := by fun_prop
  have hY : Measurable fun x : ℝ => m₂ + s₂ * x := by fun_prop
  have e₁ := integral_digital_gaussian (m := m₁) hs₁.ne' K
  have e₂ := integral_digital_gaussian (m := m₂) hs₂.ne' K
  rw [abs_of_pos hs₁] at e₁
  rw [abs_of_pos hs₂] at e₂
  have hmis : |cdf (gaussianReal 0 1) ((m₁ - K) / s₁) - cdf (gaussianReal 0 1) ((m₂ - K) / s₂)| ≤
      (gaussianReal 0 1).real {x | |m₁ + s₁ * x - K| ≤ w} + τ := by
    rw [← e₁, ← e₂, abs_sub_comm]
    refine (abs_integral_digital_sub_le hX hY K).trans
      ((measureReal_digital_ne_le _ _ K w).trans (add_le_add le_rfl (measureReal_mono ?_)))
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    by_contra hxt
    rw [not_lt] at hxt
    have h1 : |m₁ + s₁ * x - (m₂ + s₂ * x)| ≤ w := by
      rw [show m₁ + s₁ * x - (m₂ + s₂ * x) = (m₁ - m₂) + (s₁ - s₂) * x by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, hw]
      have := mul_le_mul_of_nonneg_left hxt (abs_nonneg (s₁ - s₂))
      linarith
    linarith
  have hw0 : 0 ≤ w := by positivity
  have hset : {x : ℝ | |m₁ + s₁ * x - K| ≤ w} = {x | |x - (K - m₁) / s₁| ≤ w / s₁} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [le_div_iff₀ hs₁]
    have : |m₁ + s₁ * x - K| = |x - (K - m₁) / s₁| * s₁ := by
      rw [← abs_of_pos hs₁, ← abs_mul, abs_of_pos hs₁]
      congr 1
      field_simp
      ring
    rw [this]
  refine ⟨hmis.trans ?_, fun hfar => hmis.trans ?_⟩
  · rw [hset]
    have := gaussianReal_real_abs_sub_le ((K - m₁) / s₁) (div_nonneg hw0 hs₁.le)
    linarith
  · have hsub : {x : ℝ | |m₁ + s₁ * x - K| ≤ w} ⊆ {x | t < |x|} := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      by_contra hxt
      rw [not_lt] at hxt
      have h1 : |m₁ - K| ≤ |m₁ + s₁ * x - K| + s₁ * |x| := by
        have := abs_sub_abs_le_abs_sub (m₁ + s₁ * x - K) (s₁ * x)
        rw [show m₁ + s₁ * x - K - s₁ * x = m₁ - K by ring, abs_mul, abs_of_pos hs₁] at this
        have := abs_sub_abs_le_abs_sub (m₁ - K) (-(s₁ * x))
        rw [abs_neg, abs_mul, abs_of_pos hs₁, sub_neg_eq_add,
          show m₁ - K + s₁ * x = m₁ + s₁ * x - K by ring] at this
        linarith
      have h2 := mul_le_mul_of_nonneg_left hxt hs₁.le
      linarith
    have := measureReal_mono (μ := gaussianReal 0 1) hsub
    linarith

/-- **The fine and coarse smoothed payoffs near and away from the strike** (Giles 2015, §5.2, p. 36,
l. 1575–1577: "the difference in payoff between the coarse and fine paths near the payoff
discontinuity is `O(h^{1/2})`").  Let `X, Y ≠ 0` be the fine and coarse values before the last
step, `m_f = X + rXh`, `s_f = |σX|√h`, `s_c = |σY|√h`, `m_c` arbitrary, `t, a ≥ 0` with
`|m_f − m_c| ≤ a`, `|s_f − s_c| ≤ a`, `η = t|σ|√h + |r|h ≤ 1/2` and
`R = 2(a(1 + t) + |K|η) ≤ |K|/2`.  Then
`|Φ((m_f − K)/s_f) − Φ((m_c − K)/s_c)| ≤ 2P(|Z| > t) + 2a(1+t)/(|σ||K|√h) · 1_{|X − K| ≤ R}`:
near the strike `|X| ≥ |K|/2`, so `s_f ≥ |σ||K|√h/2` (`abs_cdf_div_sub_cdf_div_le`); away from it
`|m_f − K| > a(1+t) + t s_f`. -/
lemma abs_condDigital_sub_le {X Y mc K r σ h a t : ℝ} (hX : X ≠ 0) (hY : Y ≠ 0) (hσ : σ ≠ 0)
    (hK : K ≠ 0) (hh : 0 < h) (ha : 0 ≤ a) (ht : 0 ≤ t) (hΔm : |X + r * X * h - mc| ≤ a)
    (hΔs : |(|σ * X| * Real.sqrt h - |σ * Y| * Real.sqrt h)| ≤ a)
    (hη : t * |σ| * Real.sqrt h + |r| * h ≤ 1 / 2)
    (hR : 2 * (a * (1 + t) + |K| * (t * |σ| * Real.sqrt h + |r| * h)) ≤ |K| / 2) :
    |cdf (gaussianReal 0 1) ((X + r * X * h - K) / (|σ * X| * Real.sqrt h)) -
        cdf (gaussianReal 0 1) ((mc - K) / (|σ * Y| * Real.sqrt h))| ≤
      2 * (gaussianReal 0 1).real {x | t < |x|} +
        2 * a * (1 + t) / (|σ| * |K| * Real.sqrt h) *
          {x : ℝ | |x - K| ≤ 2 * (a * (1 + t) + |K| * (t * |σ| * Real.sqrt h + |r| * h))}.indicator
            1 X := by
  set sh := Real.sqrt h with hshdef
  have hsh : 0 < sh := Real.sqrt_pos.2 hh
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have hK' : 0 < |K| := abs_pos.2 hK
  have hX' : 0 < |X| := abs_pos.2 hX
  have hs₁ : 0 < |σ * X| * sh := mul_pos (abs_pos.2 (mul_ne_zero hσ hX)) hsh
  have hs₂ : 0 < |σ * Y| * sh := mul_pos (abs_pos.2 (mul_ne_zero hσ hY)) hsh
  obtain ⟨hA1, hA2⟩ := abs_cdf_div_sub_cdf_div_le (m₁ := X + r * X * h) (m₂ := mc) hs₁ hs₂ K ht
  have hw : |X + r * X * h - mc| + t * |(|σ * X| * sh - |σ * Y| * sh)| ≤ a * (1 + t) := by
    have := mul_le_mul_of_nonneg_left hΔs ht
    nlinarith
  set η := t * |σ| * sh + |r| * h with hηdef
  have hη0 : 0 ≤ η := by positivity
  by_cases hXK : |X - K| ≤ 2 * (a * (1 + t) + |K| * η)
  · rw [Set.indicator_of_mem (show X ∈ {x : ℝ | |x - K| ≤ 2 * (a * (1 + t) + |K| * η)} from hXK),
      Pi.one_apply, mul_one]
    refine hA1.trans (add_le_add le_rfl ?_)
    have hXge : |K| ≤ 2 * |X| := by
      have := abs_sub_abs_le_abs_sub K X
      rw [abs_sub_comm] at this
      linarith
    rw [div_le_div_iff₀ hs₁ (by positivity)]
    have hat : 0 ≤ a * (1 + t) := by positivity
    calc (|X + r * X * h - mc| + t * |(|σ * X| * sh - |σ * Y| * sh)|) * (|σ| * |K| * sh)
        ≤ (a * (1 + t)) * (|σ| * (2 * |X|) * sh) :=
          mul_le_mul hw (by gcongr) (by positivity) hat
      _ = 2 * a * (1 + t) * (|σ * X| * sh) := by rw [abs_mul]; ring
  · rw [Set.indicator_of_notMem (show X ∉ {x : ℝ | |x - K| ≤ 2 * (a * (1 + t) + |K| * η)} from hXK),
      mul_zero, add_zero]
    apply hA2
    have hlt := not_le.1 hXK
    have h1 : |X| ≤ |X - K| + |K| := by
      have := abs_sub_abs_le_abs_sub X K
      linarith
    have h2 : |X - K| - |r| * h * |X| ≤ |X + r * X * h - K| := by
      have := abs_sub_abs_le_abs_sub (X - K) (-(r * X * h))
      rw [abs_neg, sub_neg_eq_add, show X - K + r * X * h = X + r * X * h - K by ring, abs_mul,
        abs_mul, abs_of_pos hh] at this
      linarith
    have h3 : t * (|σ * X| * sh) + |r| * h * |X| = η * |X| := by
      rw [abs_mul, hηdef]
      ring
    have h4 : η * |X| ≤ η * (|X - K| + |K|) := mul_le_mul_of_nonneg_left h1 hη0
    have h5 : η * |X - K| ≤ |X - K| / 2 := by
      have := mul_le_mul_of_nonneg_right hη (abs_nonneg (X - K))
      linarith
    nlinarith

/-- `h^{3/2 − 6δ} = (√h/(h^δ)²)³` for `h > 0` (the exponent `3/2` of the variance, less `6δ`,
Giles 2015, §5.2, p. 36, l. 1577). -/
lemma rpow_three_halves_sub_eq {h : ℝ} (hh : 0 < h) (δ : ℝ) :
    h ^ (3 / 2 - 6 * δ) = (Real.sqrt h / (h ^ δ) ^ 2) ^ 3 := by
  rw [div_pow, ← pow_mul, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hh.le, ← Real.rpow_mul hh.le, ← Real.rpow_sub hh]
  congr 1
  push_cast
  ring

/-- `(h^δ)^n ≤ h √h` for `0 < h ≤ 1` and `nδ ≥ 3/2` (a tail probability `O(h^{nδ})` is
`O(h^{3/2})`, Giles 2015, §5.2, p. 36, l. 1577). -/
lemma rpow_pow_le_mul_sqrt {h δ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {n : ℕ}
    (hn : 3 / 2 ≤ n * δ) : (h ^ δ) ^ n ≤ h * Real.sqrt h := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le, Real.sqrt_eq_rpow]
  have e : h * h ^ (1 / 2 : ℝ) = h ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hh, Real.rpow_one]
  rw [e]
  exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)

/-- **The scales of the variance estimate** (Giles 2015, §5.2, p. 36): with `v = h^δ ∈ (0, 1]`,
`0 < h ≤ 1`, `ε = √h/v²` (`= h^{1/2−2δ}`), `a = h/v` (`= h^{1−δ}`), `t = 1/v` (`= h^{−δ}`) and
`ε ≤ ε₀`, the hypotheses of `abs_condDigital_sub_le` hold, the window radius is at most `C₁ε` and
the coefficient at most `C₂ε`, with `C₁ = 2(2 + |K|(|σ| + |r|))`, `C₂ = 4/(|σ||K|)`. -/
lemma condDigital_scales {σ r K h v ε : ℝ} (hσ : σ ≠ 0) (hK : K ≠ 0) (hh : 0 < h) (hh1 : h ≤ 1)
    (hv0 : 0 < v) (hv1 : v ≤ 1) (hε : ε = Real.sqrt h / v ^ 2)
    (hεa : ε ≤ 1 / (2 * (|σ| + |r| + 1)))
    (hεb : ε ≤ |K| / (2 * (2 * (2 + |K| * (|σ| + |r|))))) :
    1 / v * |σ| * Real.sqrt h + |r| * h ≤ 1 / 2 ∧
    2 * (h / v * (1 + 1 / v) + |K| * (1 / v * |σ| * Real.sqrt h + |r| * h)) ≤ |K| / 2 ∧
    2 * (h / v * (1 + 1 / v) + |K| * (1 / v * |σ| * Real.sqrt h + |r| * h)) ≤
      2 * (2 + |K| * (|σ| + |r|)) * ε ∧
    2 * (h / v) * (1 + 1 / v) / (|σ| * |K| * Real.sqrt h) ≤ 4 / (|σ| * |K|) * ε := by
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have hK' : 0 < |K| := abs_pos.2 hK
  obtain ⟨sh, hshdef⟩ : ∃ sh, sh = Real.sqrt h := ⟨_, rfl⟩
  rw [← hshdef] at hε ⊢
  have hsh0 : 0 < sh := hshdef ▸ Real.sqrt_pos.2 hh
  have hsh1 : sh ≤ 1 := hshdef ▸ Real.sqrt_le_one.2 hh1
  have hshsq : sh * sh = h := hshdef ▸ Real.mul_self_sqrt hh.le
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hv2 : v ^ 2 ≤ v := by nlinarith
  have e1 : sh / v ≤ ε := by
    rw [hε]
    exact div_le_div_of_nonneg_left hsh0.le (by positivity) hv2
  have e2 : h / v ≤ sh * ε := by
    rw [← hshsq, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left e1 hsh0.le
  have e3 : h / v ^ 2 = sh * ε := by rw [← hshsq, hε, mul_div_assoc]
  have e4 : h ≤ ε := by
    rw [hε]
    calc h = sh * sh := hshsq.symm
      _ ≤ 1 * sh := mul_le_mul_of_nonneg_right hsh1 hsh0.le
      _ = sh / 1 := by ring
      _ ≤ sh / v ^ 2 := div_le_div_of_nonneg_left hsh0.le (by positivity) (pow_le_one₀ hv0.le hv1)
  have hat : h / v * (1 + 1 / v) ≤ 2 * ε * sh := by
    have : h / v * (1 + 1 / v) = h / v + h / v ^ 2 := by
      field_simp
    rw [this, e3]
    linarith
  have hatε : h / v * (1 + 1 / v) ≤ 2 * ε := by
    have := mul_le_mul_of_nonneg_left hsh1 (by positivity : (0 : ℝ) ≤ 2 * ε)
    linarith
  have hηε : 1 / v * |σ| * sh + |r| * h ≤ (|σ| + |r|) * ε := by
    have h1 : 1 / v * |σ| * sh = |σ| * (sh / v) := by ring
    rw [h1]
    have := mul_le_mul_of_nonneg_left e1 hσ'.le
    have := mul_le_mul_of_nonneg_left e4 (abs_nonneg r)
    linarith
  have hRε : 2 * (h / v * (1 + 1 / v) + |K| * (1 / v * |σ| * sh + |r| * h)) ≤
      2 * (2 + |K| * (|σ| + |r|)) * ε := by
    have := mul_le_mul_of_nonneg_left hηε hK'.le
    nlinarith
  refine ⟨hηε.trans ?_, hRε.trans ?_, hRε, ?_⟩
  · have h1 : (|σ| + |r|) * ε ≤ (|σ| + |r|) * (1 / (2 * (|σ| + |r| + 1))) :=
      mul_le_mul_of_nonneg_left hεa (by positivity)
    have h2 : (|σ| + |r|) * (1 / (2 * (|σ| + |r| + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  · have hC : 0 < 2 * (2 + |K| * (|σ| + |r|)) := by positivity
    calc 2 * (2 + |K| * (|σ| + |r|)) * ε ≤
          2 * (2 + |K| * (|σ| + |r|)) * (|K| / (2 * (2 * (2 + |K| * (|σ| + |r|))))) :=
          mul_le_mul_of_nonneg_left hεb hC.le
      _ = |K| / 2 := by field_simp
  · rw [div_le_iff₀ (by positivity)]
    have : 4 / (|σ| * |K|) * ε * (|σ| * |K| * sh) = 4 * ε * sh := by field_simp
    rw [this]
    linarith

/-- **The pointwise bound of the variance estimate** (Giles 2015, §5.2, p. 36, l. 1575–1580): in the
setting of `abs_condDigital_sub_le`, if moreover the window radius is at most `C₁ε` and the
coefficient at most `C₂ε`, then
`(Φ_f − Φ_c)² ≤ 1_{|m_f − m_c| > a} + 1_{|s_f − s_c| > a} + 8P(|Z| > t)² +
2(C₂ε)² 1_{|X − K| ≤ C₁ε}` (the first two indicators cover the case where the means or the
standard deviations do not match, where the bound `(Φ_f − Φ_c)² ≤ 1` is used). -/
lemma condDigital_sq_le_indicators {X Y mc K r σ h a t C₁ C₂ ε : ℝ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (hσ : σ ≠ 0) (hK : K ≠ 0) (hh : 0 < h) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hη : t * |σ| * Real.sqrt h + |r| * h ≤ 1 / 2)
    (hR : 2 * (a * (1 + t) + |K| * (t * |σ| * Real.sqrt h + |r| * h)) ≤ |K| / 2)
    (hRε : 2 * (a * (1 + t) + |K| * (t * |σ| * Real.sqrt h + |r| * h)) ≤ C₁ * ε)
    (hcoef : 2 * a * (1 + t) / (|σ| * |K| * Real.sqrt h) ≤ C₂ * ε) :
    (cdf (gaussianReal 0 1) ((X + r * X * h - K) / (|σ * X| * Real.sqrt h)) -
        cdf (gaussianReal 0 1) ((mc - K) / (|σ * Y| * Real.sqrt h))) ^ 2 ≤
      {x : ℝ | a < |x|}.indicator 1 (X + r * X * h - mc) +
        {x : ℝ | a < |x|}.indicator 1 (|σ * X| * Real.sqrt h - |σ * Y| * Real.sqrt h) +
        (8 * (gaussianReal 0 1).real {x | t < |x|} ^ 2 +
          2 * (C₂ * ε) ^ 2 * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 X) := by
  set τ := (gaussianReal 0 1).real {x | t < |x|} with hτdef
  have hτ0 : 0 ≤ τ := measureReal_nonneg
  have hI1 : 0 ≤ {x : ℝ | a < |x|}.indicator (1 : ℝ → ℝ) (X + r * X * h - mc) :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hI2 : 0 ≤ {x : ℝ | a < |x|}.indicator (1 : ℝ → ℝ)
      (|σ * X| * Real.sqrt h - |σ * Y| * Real.sqrt h) :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hI3 : 0 ≤ {x : ℝ | |x - K| ≤ C₁ * ε}.indicator (1 : ℝ → ℝ) X :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hrest : 0 ≤ 8 * τ ^ 2 + 2 * (C₂ * ε) ^ 2 *
      {x : ℝ | |x - K| ≤ C₁ * ε}.indicator (1 : ℝ → ℝ) X := by positivity
  have hle1 : (cdf (gaussianReal 0 1) ((X + r * X * h - K) / (|σ * X| * Real.sqrt h)) -
      cdf (gaussianReal 0 1) ((mc - K) / (|σ * Y| * Real.sqrt h))) ^ 2 ≤ 1 := by
    have h1 := cdf_nonneg (gaussianReal 0 1) ((X + r * X * h - K) / (|σ * X| * Real.sqrt h))
    have h2 := cdf_le_one (gaussianReal 0 1) ((X + r * X * h - K) / (|σ * X| * Real.sqrt h))
    have h3 := cdf_nonneg (gaussianReal 0 1) ((mc - K) / (|σ * Y| * Real.sqrt h))
    have h4 := cdf_le_one (gaussianReal 0 1) ((mc - K) / (|σ * Y| * Real.sqrt h))
    nlinarith
  by_cases b1 : a < |X + r * X * h - mc|
  · rw [Set.indicator_of_mem (show X + r * X * h - mc ∈ {x : ℝ | a < |x|} from b1), Pi.one_apply]
    linarith
  by_cases b2 : a < |(|σ * X| * Real.sqrt h - |σ * Y| * Real.sqrt h)|
  · rw [Set.indicator_of_mem (show |σ * X| * Real.sqrt h - |σ * Y| * Real.sqrt h ∈
      {x : ℝ | a < |x|} from b2), Pi.one_apply]
    linarith
  rw [Set.indicator_of_notMem (show X + r * X * h - mc ∉ {x : ℝ | a < |x|} from b1),
    Set.indicator_of_notMem (show |σ * X| * Real.sqrt h - |σ * Y| * Real.sqrt h ∉
      {x : ℝ | a < |x|} from b2), zero_add, zero_add]
  have key := abs_condDigital_sub_le (mc := mc) (K := K) hX hY hσ hK hh ha ht (not_lt.1 b1)
    (not_lt.1 b2) hη hR
  have hind : {x : ℝ | |x - K| ≤ 2 * (a * (1 + t) + |K| * (t * |σ| * Real.sqrt h +
      |r| * h))}.indicator (1 : ℝ → ℝ) X ≤ {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 X := by
    by_cases hw : |X - K| ≤ 2 * (a * (1 + t) + |K| * (t * |σ| * Real.sqrt h + |r| * h))
    · rw [Set.indicator_of_mem (show X ∈ {x : ℝ | |x - K| ≤ 2 * (a * (1 + t) +
          |K| * (t * |σ| * Real.sqrt h + |r| * h))} from hw),
        Set.indicator_of_mem (show X ∈ {x : ℝ | |x - K| ≤ C₁ * ε} from hw.trans hRε)]
    · rw [Set.indicator_of_notMem (show X ∉ {x : ℝ | |x - K| ≤ 2 * (a * (1 + t) +
          |K| * (t * |σ| * Real.sqrt h + |r| * h))} from hw)]
      exact hI3
  have hcoef0 : 0 ≤ 2 * a * (1 + t) / (|σ| * |K| * Real.sqrt h) := by positivity
  have hind0 : 0 ≤ {x : ℝ | |x - K| ≤ 2 * (a * (1 + t) + |K| * (t * |σ| * Real.sqrt h +
      |r| * h))}.indicator (1 : ℝ → ℝ) X := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hCε : 0 ≤ C₂ * ε := hcoef0.trans hcoef
  have hbd := key.trans (add_le_add le_rfl (mul_le_mul hcoef hind hind0 hCε))
  have hI3sq : {x : ℝ | |x - K| ≤ C₁ * ε}.indicator (1 : ℝ → ℝ) X ^ 2 =
      {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 X := by
    by_cases b3 : X ∈ {x : ℝ | |x - K| ≤ C₁ * ε}
    · rw [Set.indicator_of_mem b3, Pi.one_apply, one_pow]
    · rw [Set.indicator_of_notMem b3, zero_pow two_ne_zero]
  rw [← sq_abs]
  calc _ ≤ (2 * τ + C₂ * ε * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 X) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hbd 2
    _ ≤ 2 * (2 * τ) ^ 2 + 2 * (C₂ * ε * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 X) ^ 2 := by
        nlinarith [sq_nonneg (2 * τ - C₂ * ε * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 X)]
    _ = 8 * τ ^ 2 + 2 * (C₂ * ε) ^ 2 * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 X := by
        rw [mul_pow (C₂ * ε), hI3sq]
        ring

/-- `∫ 1_S(f) dμ = μ(f ∈ S)` and `1_S ∘ f` is integrable, for measurable `f` and `S` (the events of
the variance estimate, Giles 2015, §5.2, p. 36, l. 1575–1577). -/
lemma integrable_integral_indicator_one_comp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {S : Set ℝ} (hS : MeasurableSet S) :
    Integrable (fun ω => S.indicator (1 : ℝ → ℝ) (f ω)) μ ∧
      ∫ ω, S.indicator (1 : ℝ → ℝ) (f ω) ∂μ = μ.real {ω | f ω ∈ S} := by
  have e : (fun ω => S.indicator (1 : ℝ → ℝ) (f ω)) = (f ⁻¹' S).indicator 1 := by
    funext ω
    rfl
  rw [e]
  exact ⟨(integrable_const (1 : ℝ)).indicator (hf hS), integral_indicator_one (hf hS)⟩

/-- **The variance estimate on one level, for small steps** (Giles 2015, §5.2, p. 36,
l. 1563–1580; see `condDigital_sq_rate`): with `v = h^δ`, `ε = √h/v²` and `ε ≤ ε₀`, the second
moment of the payoff difference is at most
`(C_m + C_s + 8((2p−1)!!)² + 8C₂²ρC₁ + 2C₂²C_X/C₁^{2p}) ε³`. -/
lemma condDigital_sq_le_main {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {r σ K ρ δ h v ε C₁ C₂ Cm Cs CX : ℝ} {p : ℕ}
    (hσ : σ ≠ 0) (hK : K ≠ 0) (hpδ : 3 / 2 ≤ 2 * p * δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hδ0 : 0 ≤ δ) (hv : v = h ^ δ) (hε : ε = Real.sqrt h / v ^ 2)
    (hC₁ : C₁ = 2 * (2 + |K| * (|σ| + |r|))) (hC₂ : C₂ = 4 / (|σ| * |K|))
    (hεa : ε ≤ 1 / (2 * (|σ| + |r| + 1))) (hεb : ε ≤ |K| / (2 * C₁))
    {X Y mc ST : Ω → ℝ} (hXm : Measurable X) (hYm : Measurable Y) (hmcm : Measurable mc)
    (hX0 : ∀ᵐ ω ∂μ, X ω ≠ 0) (hY0 : ∀ᵐ ω ∂μ, Y ω ≠ 0)
    (hball : ∀ η, 0 < η → μ.real {ω | |ST ω - K| ≤ η} ≤ 2 * ρ * η)
    (hmi : Integrable (fun ω => (X ω + r * X ω * h - mc ω) ^ (2 * p)) μ)
    (hmb : ∫ ω, (X ω + r * X ω * h - mc ω) ^ (2 * p) ∂μ ≤ Cm * h ^ (2 * p))
    (hsi : Integrable (fun ω => (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) ^ (2 * p)) μ)
    (hsb : ∫ ω, (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) ^ (2 * p) ∂μ ≤
      Cs * h ^ (2 * p))
    (hxi : Integrable (fun ω => (ST ω - X ω) ^ (2 * p)) μ)
    (hxb : ∫ ω, (ST ω - X ω) ^ (2 * p) ∂μ ≤ CX * h ^ p)
    (hCm : 0 ≤ Cm) (hCs : 0 ≤ Cs) (hCX : 0 ≤ CX) :
    ∫ ω, (cdf (gaussianReal 0 1) ((X ω + r * X ω * h - K) / (|σ * X ω| * Real.sqrt h)) -
        cdf (gaussianReal 0 1) ((mc ω - K) / (|σ * Y ω| * Real.sqrt h))) ^ 2 ∂μ ≤
      (Cm + Cs + 8 * (Nat.doubleFactorial (2 * p - 1) : ℝ) ^ 2 + 8 * C₂ ^ 2 * ρ * C₁ +
        2 * C₂ ^ 2 * CX / C₁ ^ (2 * p)) * ε ^ 3 := by
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have hK' : 0 < |K| := abs_pos.2 hK
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  have hv0 : 0 < v := by rw [hv]; exact Real.rpow_pos_of_pos hh δ
  have hv1 : v ≤ 1 := by rw [hv]; exact Real.rpow_le_one hh.le hh1 hδ0
  obtain ⟨sh, hshdef⟩ : ∃ sh, sh = Real.sqrt h := ⟨_, rfl⟩
  have hsh0 : 0 < sh := hshdef ▸ Real.sqrt_pos.2 hh
  have hsh1 : sh ≤ 1 := hshdef ▸ Real.sqrt_le_one.2 hh1
  have hshsq : sh * sh = h := hshdef ▸ Real.mul_self_sqrt hh.le
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨hη, hR, hRε, hcoef⟩ := condDigital_scales (r := r) hσ hK hh hh1 hv0 hv1 hε hεa
    (by rw [← hC₁]; exact hεb)
  rw [← hC₁] at hRε
  rw [← hC₂] at hcoef
  have ha0 : 0 < h / v := by positivity
  have ht0 : 0 < 1 / v := by positivity
  -- the pointwise bound
  have hpt := fun ω (hXω : X ω ≠ 0) (hYω : Y ω ≠ 0) =>
    condDigital_sq_le_indicators (mc := mc ω) hXω hYω hσ hK hh ha0.le ht0.le hη hR hRε hcoef
  set τ := (gaussianReal 0 1).real {x | 1 / v < |x|} with hτdef
  have hτ0 : 0 ≤ τ := measureReal_nonneg
  have hS1 : MeasurableSet {x : ℝ | h / v < |x|} := measurableSet_lt measurable_const (by fun_prop)
  have hS3 : MeasurableSet {x : ℝ | |x - K| ≤ C₁ * ε} :=
    measurableSet_le (by fun_prop) measurable_const
  have hΔmm : Measurable fun ω => X ω + r * X ω * h - mc ω := by fun_prop
  have hΔsm : Measurable fun ω => |σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h := by
    fun_prop
  obtain ⟨hi1, he1⟩ := integrable_integral_indicator_one_comp (μ := μ) hΔmm hS1
  obtain ⟨hi2, he2⟩ := integrable_integral_indicator_one_comp (μ := μ) hΔsm hS1
  obtain ⟨hi3, he3⟩ := integrable_integral_indicator_one_comp (μ := μ) hXm hS3
  have hcdf : Measurable (cdf (gaussianReal 0 1)) := (monotone_cdf _).measurable
  have hFm : Measurable fun ω => (cdf (gaussianReal 0 1) ((X ω + r * X ω * h - K) /
      (|σ * X ω| * Real.sqrt h)) - cdf (gaussianReal 0 1) ((mc ω - K) /
      (|σ * Y ω| * Real.sqrt h))) ^ 2 := by fun_prop
  have hFi : Integrable (fun ω => (cdf (gaussianReal 0 1) ((X ω + r * X ω * h - K) /
      (|σ * X ω| * Real.sqrt h)) - cdf (gaussianReal 0 1) ((mc ω - K) /
      (|σ * Y ω| * Real.sqrt h))) ^ 2) μ := by
    refine Integrable.of_bound hFm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
    have h1 := cdf_nonneg (gaussianReal 0 1) ((X ω + r * X ω * h - K) / (|σ * X ω| * Real.sqrt h))
    have h2 := cdf_le_one (gaussianReal 0 1) ((X ω + r * X ω * h - K) / (|σ * X ω| * Real.sqrt h))
    have h3 := cdf_nonneg (gaussianReal 0 1) ((mc ω - K) / (|σ * Y ω| * Real.sqrt h))
    have h4 := cdf_le_one (gaussianReal 0 1) ((mc ω - K) / (|σ * Y ω| * Real.sqrt h))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hi12 : Integrable (fun ω => {x : ℝ | h / v < |x|}.indicator (1 : ℝ → ℝ)
      (X ω + r * X ω * h - mc ω) + {x : ℝ | h / v < |x|}.indicator 1
        (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h)) μ := hi1.add hi2
  have hi3' : Integrable (fun ω => 2 * (C₂ * ε) ^ 2 *
      {x : ℝ | |x - K| ≤ C₁ * ε}.indicator (1 : ℝ → ℝ) (X ω)) μ := hi3.const_mul _
  have hi3c : Integrable (fun ω => 8 * τ ^ 2 + 2 * (C₂ * ε) ^ 2 *
      {x : ℝ | |x - K| ≤ C₁ * ε}.indicator (1 : ℝ → ℝ) (X ω)) μ := (integrable_const _).add hi3'
  have hrhs : Integrable (fun ω => {x : ℝ | h / v < |x|}.indicator (1 : ℝ → ℝ)
      (X ω + r * X ω * h - mc ω) + {x : ℝ | h / v < |x|}.indicator 1
        (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) +
      (8 * τ ^ 2 + 2 * (C₂ * ε) ^ 2 * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 (X ω))) μ :=
    hi12.add hi3c
  have hint : ∫ ω, ({x : ℝ | h / v < |x|}.indicator (1 : ℝ → ℝ)
      (X ω + r * X ω * h - mc ω) + {x : ℝ | h / v < |x|}.indicator 1
        (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) +
      (8 * τ ^ 2 + 2 * (C₂ * ε) ^ 2 * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 (X ω))) ∂μ =
      μ.real {ω | X ω + r * X ω * h - mc ω ∈ {x : ℝ | h / v < |x|}} +
        μ.real {ω | |σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h ∈ {x : ℝ | h / v < |x|}} +
        (8 * τ ^ 2 + 2 * (C₂ * ε) ^ 2 * μ.real {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}}) := by
    have e1 : ∫ ω, ({x : ℝ | h / v < |x|}.indicator (1 : ℝ → ℝ)
        (X ω + r * X ω * h - mc ω) + {x : ℝ | h / v < |x|}.indicator 1
          (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) +
        (8 * τ ^ 2 + 2 * (C₂ * ε) ^ 2 * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 (X ω))) ∂μ =
        ∫ ω, ({x : ℝ | h / v < |x|}.indicator (1 : ℝ → ℝ)
          (X ω + r * X ω * h - mc ω) + {x : ℝ | h / v < |x|}.indicator 1
            (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h)) ∂μ +
        ∫ ω, (8 * τ ^ 2 + 2 * (C₂ * ε) ^ 2 *
          {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 (X ω)) ∂μ := integral_add hi12 hi3c
    have e2 : ∫ ω, ({x : ℝ | h / v < |x|}.indicator (1 : ℝ → ℝ)
          (X ω + r * X ω * h - mc ω) + {x : ℝ | h / v < |x|}.indicator 1
            (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h)) ∂μ =
        ∫ ω, {x : ℝ | h / v < |x|}.indicator (1 : ℝ → ℝ) (X ω + r * X ω * h - mc ω) ∂μ +
          ∫ ω, {x : ℝ | h / v < |x|}.indicator (1 : ℝ → ℝ)
            (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) ∂μ := integral_add hi1 hi2
    have e3 : ∫ ω, (8 * τ ^ 2 + 2 * (C₂ * ε) ^ 2 *
          {x : ℝ | |x - K| ≤ C₁ * ε}.indicator (1 : ℝ → ℝ) (X ω)) ∂μ =
        ∫ _, 8 * τ ^ 2 ∂μ + ∫ ω, 2 * (C₂ * ε) ^ 2 *
          {x : ℝ | |x - K| ≤ C₁ * ε}.indicator (1 : ℝ → ℝ) (X ω) ∂μ :=
      integral_add (integrable_const _) hi3'
    rw [e1, e2, e3, integral_const_mul (2 * (C₂ * ε) ^ 2), he1, he2, he3, integral_const,
      probReal_univ, one_smul]
  -- the probabilities
  have hP1 : μ.real {ω | X ω + r * X ω * h - mc ω ∈ {x : ℝ | h / v < |x|}} ≤
      Cm * v ^ (2 * p) := by
    refine (measureReal_lt_abs_le_integral_pow_div hmi ha0).trans ?_
    calc (∫ ω, (X ω + r * X ω * h - mc ω) ^ (2 * p) ∂μ) / (h / v) ^ (2 * p)
        ≤ Cm * h ^ (2 * p) / (h / v) ^ (2 * p) :=
          div_le_div_of_nonneg_right hmb (by positivity)
      _ = Cm * v ^ (2 * p) := by
          rw [div_pow]
          field_simp
  have hP2 : μ.real {ω | |σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h ∈
      {x : ℝ | h / v < |x|}} ≤ Cs * v ^ (2 * p) := by
    refine (measureReal_lt_abs_le_integral_pow_div hsi ha0).trans ?_
    calc (∫ ω, (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) ^ (2 * p) ∂μ) /
          (h / v) ^ (2 * p)
        ≤ Cs * h ^ (2 * p) / (h / v) ^ (2 * p) :=
          div_le_div_of_nonneg_right hsb (by positivity)
      _ = Cs * v ^ (2 * p) := by
          rw [div_pow]
          field_simp
  have hτb : τ ≤ (Nat.doubleFactorial (2 * p - 1) : ℝ) * v ^ (2 * p) := by
    refine (gaussianReal_real_lt_abs_le p ht0).trans (le_of_eq ?_)
    rw [div_pow, one_pow, div_div_eq_mul_div, div_one]
  have hP3 : μ.real {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}} ≤
      4 * ρ * C₁ * ε + CX * v ^ (4 * p) / C₁ ^ (2 * p) := by
    have hsub : {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}} ⊆
        {ω | |ST ω - K| ≤ 2 * (C₁ * ε)} ∪ {ω | C₁ * ε < |ST ω - X ω|} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      by_cases hω' : C₁ * ε < |ST ω - X ω|
      · exact Or.inr hω'
      · left
        simp only [Set.mem_ofPred_eq]
        rw [not_lt] at hω'
        calc |ST ω - K| = |(ST ω - X ω) + (X ω - K)| := by ring_nf
          _ ≤ |ST ω - X ω| + |X ω - K| := abs_add_le _ _
          _ ≤ 2 * (C₁ * ε) := by linarith
    have hC1e : 0 < C₁ * ε := by positivity
    have hεp : (C₁ * ε) ^ (2 * p) = C₁ ^ (2 * p) * (h ^ p / v ^ (4 * p)) := by
      rw [mul_pow, hε, ← hshdef, div_pow, ← pow_mul, pow_mul sh 2 p, sq, hshsq,
        show 2 * (2 * p) = 4 * p by ring]
    calc μ.real {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}}
        ≤ μ.real {ω | |ST ω - K| ≤ 2 * (C₁ * ε)} + μ.real {ω | C₁ * ε < |ST ω - X ω|} :=
          (measureReal_mono hsub).trans (measureReal_union_le _ _)
      _ ≤ 2 * ρ * (2 * (C₁ * ε)) + (∫ ω, (ST ω - X ω) ^ (2 * p) ∂μ) / (C₁ * ε) ^ (2 * p) :=
          add_le_add (hball _ (by positivity)) (measureReal_lt_abs_le_integral_pow_div hxi hC1e)
      _ ≤ 2 * ρ * (2 * (C₁ * ε)) + CX * h ^ p / (C₁ * ε) ^ (2 * p) :=
          add_le_add le_rfl (div_le_div_of_nonneg_right hxb (by positivity))
      _ = 4 * ρ * C₁ * ε + CX * v ^ (4 * p) / C₁ ^ (2 * p) := by
          rw [hεp]
          field_simp
          ring
  -- the powers of `v` against `ε³`
  have hF : v ^ (2 * p) ≤ h * sh := by
    rw [hv, hshdef]
    refine rpow_pow_le_mul_sqrt hh hh1 ?_
    push_cast
    linarith
  have hhsh : h * sh ≤ ε ^ 3 := by
    have e : ε ^ 3 = h * sh / (v ^ 2) ^ 3 := by
      rw [hε, ← hshdef, div_pow, ← hshsq]
      ring
    rw [e, le_div_iff₀ (by positivity)]
    have h1 : (v ^ 2) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) (pow_le_one₀ hv0.le hv1)
    have h2 : 0 ≤ h * sh := by positivity
    exact mul_le_of_le_one_right h2 h1
  have hv2p : v ^ (2 * p) ≤ ε ^ 3 := hF.trans hhsh
  have hv4p : v ^ (4 * p) ≤ v ^ (2 * p) := pow_le_pow_of_le_one hv0.le hv1 (by omega)
  have hv4ε : v ^ (4 * p) ≤ ε := by
    refine hv4p.trans (hF.trans ?_)
    rw [hε, ← hshdef]
    calc h * sh ≤ 1 * sh := mul_le_mul_of_nonneg_right hh1 hsh0.le
      _ = sh / 1 := by ring
      _ ≤ sh / v ^ 2 := div_le_div_of_nonneg_left hsh0.le (by positivity) (pow_le_one₀ hv0.le hv1)
  have hτ2 : τ ^ 2 ≤ (Nat.doubleFactorial (2 * p - 1) : ℝ) ^ 2 * ε ^ 3 := by
    calc τ ^ 2 ≤ ((Nat.doubleFactorial (2 * p - 1) : ℝ) * v ^ (2 * p)) ^ 2 :=
          pow_le_pow_left₀ hτ0 hτb 2
      _ = (Nat.doubleFactorial (2 * p - 1) : ℝ) ^ 2 * v ^ (4 * p) := by
          rw [mul_pow, ← pow_mul]
          ring_nf
      _ ≤ (Nat.doubleFactorial (2 * p - 1) : ℝ) ^ 2 * ε ^ 3 :=
          mul_le_mul_of_nonneg_left (hv4p.trans hv2p) (by positivity)
  have hB3 : (C₂ * ε) ^ 2 * μ.real {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}} ≤
      4 * C₂ ^ 2 * ρ * C₁ * ε ^ 3 + C₂ ^ 2 * CX / C₁ ^ (2 * p) * ε ^ 3 := by
    have h1 : (C₂ * ε) ^ 2 * μ.real {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}} ≤ (C₂ * ε) ^ 2 *
        (4 * ρ * C₁ * ε + CX * v ^ (4 * p) / C₁ ^ (2 * p)) :=
      mul_le_mul_of_nonneg_left hP3 (by positivity)
    have h2 : (C₂ * ε) ^ 2 * (CX * v ^ (4 * p) / C₁ ^ (2 * p)) ≤
        C₂ ^ 2 * CX / C₁ ^ (2 * p) * ε ^ 3 := by
      have e : (C₂ * ε) ^ 2 * (CX * v ^ (4 * p) / C₁ ^ (2 * p)) =
          C₂ ^ 2 * CX / C₁ ^ (2 * p) * (ε ^ 2 * v ^ (4 * p)) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ε ^ 2 * v ^ (4 * p) ≤ ε ^ 2 * ε := mul_le_mul_of_nonneg_left hv4ε (by positivity)
        _ = ε ^ 3 := by ring
    have e : (C₂ * ε) ^ 2 * (4 * ρ * C₁ * ε + CX * v ^ (4 * p) / C₁ ^ (2 * p)) =
        4 * C₂ ^ 2 * ρ * C₁ * ε ^ 3 + (C₂ * ε) ^ 2 * (CX * v ^ (4 * p) / C₁ ^ (2 * p)) := by ring
    linarith
  calc _ ≤ ∫ ω, ({x : ℝ | h / v < |x|}.indicator (1 : ℝ → ℝ)
        (X ω + r * X ω * h - mc ω) + {x : ℝ | h / v < |x|}.indicator 1
          (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) +
        (8 * τ ^ 2 + 2 * (C₂ * ε) ^ 2 * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 (X ω))) ∂μ := by
        refine integral_mono_ae hFi hrhs ?_
        filter_upwards [hX0, hY0] with ω hXω hYω
        exact hpt ω hXω hYω
    _ = _ := hint
    _ ≤ Cm * ε ^ 3 + Cs * ε ^ 3 + (8 * ((Nat.doubleFactorial (2 * p - 1) : ℝ) ^ 2 * ε ^ 3) +
          2 * (4 * C₂ ^ 2 * ρ * C₁ * ε ^ 3 + C₂ ^ 2 * CX / C₁ ^ (2 * p) * ε ^ 3)) := by
        have h1 := hP1.trans (mul_le_mul_of_nonneg_left hv2p hCm)
        have h2 := hP2.trans (mul_le_mul_of_nonneg_left hv2p hCs)
        linarith
    _ = _ := by ring

/-- The squared difference of two values of `Φ` is integrable and has mean at most `1` (the
smoothed payoffs of Giles 2015, §5.2, p. 36, l. 1551–1574, take values in `[0, 1]`). -/
lemma integrable_integral_sq_cdf_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Integrable (fun ω => (cdf (gaussianReal 0 1) (a ω) - cdf (gaussianReal 0 1) (b ω)) ^ 2) μ ∧
      ∫ ω, (cdf (gaussianReal 0 1) (a ω) - cdf (gaussianReal 0 1) (b ω)) ^ 2 ∂μ ≤ 1 := by
  have hcdf : Measurable (cdf (gaussianReal 0 1)) := (monotone_cdf _).measurable
  have hle : ∀ ω, (cdf (gaussianReal 0 1) (a ω) - cdf (gaussianReal 0 1) (b ω)) ^ 2 ≤ 1 :=
    fun ω => by
      have h1 := cdf_nonneg (gaussianReal 0 1) (a ω)
      have h2 := cdf_le_one (gaussianReal 0 1) (a ω)
      have h3 := cdf_nonneg (gaussianReal 0 1) (b ω)
      have h4 := cdf_le_one (gaussianReal 0 1) (b ω)
      nlinarith
  have hint : Integrable (fun ω => (cdf (gaussianReal 0 1) (a ω) -
      cdf (gaussianReal 0 1) (b ω)) ^ 2) μ :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hle ω)
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ _, (1 : ℝ) ∂μ := integral_mono hint (integrable_const 1) hle
    _ = 1 := by simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]

/-- **The variance rate of the conditional-expectation estimator, abstract form** (Giles 2015,
§5.2, p. 36, l. 1563–1580: "This results in the conditional distribution for the coarse path
underlying at maturity matching that of the fine path to within `O(h)`, for both the mean and the
standard deviation … the difference in payoff between the coarse and fine paths near the payoff
discontinuity is `O(h^{1/2})`, giving a variance which is approximately `O(h^{3/2})`").  For a
family of fine values `X_i ≠ 0` (a.s.) one step before maturity, coarse values `Y_i ≠ 0`, coarse
conditional means `m_{c,i}`, steps `h_i > 0` and a reference `S_i` (the exact solution at
maturity) with density at most `ρ` near `K ≠ 0`, if for some `p` with `2pδ ≥ 3/2`
(`0 < δ ≤ 1/4`), uniformly in `i`, `E[(m_f − m_c)^{2p}] = O(h^{2p})`,
`E[(s_f − s_c)^{2p}] = O(h^{2p})` (`m_f = X + rXh`, `s_f = |σX|√h`, `s_c = |σY|√h`) and
`E[(S − X)^{2p}] = O(h^p)`, then
`E[(Φ((m_f − K)/s_f) − Φ((m_c − K)/s_c))²] ≤ C h_i^{3/2 − 6δ}` for one `C` and all `i`.

Proof: with `v = h^δ`, `ε = √h/v² = h^{1/2 − 2δ}`, `a = h/v = h^{1−δ}`, `t = 1/v = h^{−δ}`:
outside the events `|m_f − m_c| > a`, `|s_f − s_c| > a` (probability `O(h^{2pδ})`, Markov) the
difference is at most `2P(|Z| > t) + C₂ε 1_{|X − K| ≤ C₁ε}` (`condDigital_sq_le_indicators`),
`P(|Z| > t) ≤ (2p−1)!! h^{2pδ}`, and `P(|X − K| ≤ C₁ε) ≤ 4ρC₁ε + E[(S − X)^{2p}]/(C₁ε)^{2p}`
(`condDigital_sq_le_main`); for `h > 1` or `ε > ε₀` the bound `1` is used. -/
lemma condDigital_sq_rate {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {r σ K ρ δ : ℝ} (hσ : σ ≠ 0) (hK : K ≠ 0) (hρ : 0 ≤ ρ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) {p : ℕ} (hpδ : 3 / 2 ≤ 2 * p * δ)
    {h : ι → ℝ} (hh : ∀ i, 0 < h i) {X Y mc ST : ι → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hYm : ∀ i, Measurable (Y i)) (hmcm : ∀ i, Measurable (mc i))
    (hX0 : ∀ i, ∀ᵐ ω ∂μ, X i ω ≠ 0) (hY0 : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≠ 0)
    (hball : ∀ i η, 0 < η → μ.real {ω | |ST i ω - K| ≤ η} ≤ 2 * ρ * η)
    (hΔm : MomentBound μ (fun i ω => X i ω + r * X i ω * h i - mc i ω) p
      (fun i => h i ^ (2 * p)))
    (hΔs : MomentBound μ (fun i ω => |σ * X i ω| * Real.sqrt (h i) -
      |σ * Y i ω| * Real.sqrt (h i)) p (fun i => h i ^ (2 * p)))
    (hXS : MomentBound μ (fun i ω => ST i ω - X i ω) p (fun i => h i ^ p)) :
    ∃ C, 0 ≤ C ∧ ∀ i, ∫ ω, (cdf (gaussianReal 0 1) ((X i ω + r * X i ω * h i - K) /
        (|σ * X i ω| * Real.sqrt (h i))) - cdf (gaussianReal 0 1) ((mc i ω - K) /
        (|σ * Y i ω| * Real.sqrt (h i)))) ^ 2 ∂μ ≤ C * h i ^ (3 / 2 - 6 * δ) := by
  obtain ⟨Cm, hCm, hm⟩ := hΔm
  obtain ⟨Cs, hCs, hs⟩ := hΔs
  obtain ⟨CX, hCX, hx⟩ := hXS
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have hK' : 0 < |K| := abs_pos.2 hK
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 2 * (2 + |K| * (|σ| + |r|)) := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 4 / (|σ| * |K|) := ⟨_, rfl⟩
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = min (1 / (2 * (|σ| + |r| + 1))) (|K| / (2 * C₁)) :=
    ⟨_, rfl⟩
  have hε₀0 : 0 < ε₀ := by rw [hε₀]; exact lt_min (by positivity) (by positivity)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = Cm + Cs + 8 * (Nat.doubleFactorial (2 * p - 1) : ℝ) ^ 2 +
      8 * C₂ ^ 2 * ρ * C₁ + 2 * C₂ ^ 2 * CX / C₁ ^ (2 * p) := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  have hinv : 0 ≤ 1 / ε₀ ^ 3 := by positivity
  refine ⟨1 + 1 / ε₀ ^ 3 + C₀, by positivity, fun i => ?_⟩
  have hi := hh i
  have hXi := hXm i
  have hYi := hYm i
  have hmci := hmcm i
  have hF1 := (integrable_integral_sq_cdf_sub_le (μ := μ)
    (a := fun ω => (X i ω + r * X i ω * h i - K) / (|σ * X i ω| * Real.sqrt (h i)))
    (b := fun ω => (mc i ω - K) / (|σ * Y i ω| * Real.sqrt (h i))) (by fun_prop)
    (by fun_prop)).2
  by_cases hbig : 1 < h i
  · have h1 : 1 ≤ h i ^ (3 / 2 - 6 * δ) := Real.one_le_rpow hbig.le (by linarith)
    calc _ ≤ 1 := hF1
      _ ≤ (1 + 1 / ε₀ ^ 3 + C₀) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by linarith)
  have hh1 : h i ≤ 1 := not_lt.1 hbig
  obtain ⟨v, hv⟩ : ∃ v, v = h i ^ δ := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε, ε = Real.sqrt (h i) / v ^ 2 := ⟨_, rfl⟩
  have hv0 : 0 < v := by rw [hv]; exact Real.rpow_pos_of_pos hi δ
  have hε0 : 0 < ε := by rw [hε]; have := Real.sqrt_pos.2 hi; positivity
  rw [rpow_three_halves_sub_eq hi δ, ← hv, ← hε]
  by_cases hεbig : ε₀ < ε
  · have h1 : 1 ≤ 1 / ε₀ ^ 3 * ε ^ 3 := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hε₀0.le hεbig.le 3
    have h2 : 0 ≤ (1 + C₀) * ε ^ 3 := by positivity
    calc _ ≤ 1 := hF1
      _ ≤ 1 / ε₀ ^ 3 * ε ^ 3 := h1
      _ ≤ _ := by nlinarith
  have hε' : ε ≤ ε₀ := not_lt.1 hεbig
  have hmain := condDigital_sq_le_main hσ hK hpδ hi hh1 hδ0.le hv hε hC₁ hC₂
    (hε'.trans (hε₀ ▸ min_le_left _ _)) (hε'.trans (hε₀ ▸ min_le_right _ _)) hXi hYi hmci
    (hX0 i) (hY0 i) (hball i) (hm i).1 (hm i).2 (hs i).1 (hs i).2 (hx i).1 (hx i).2
    hCm hCs hCX
  rw [← hC₀] at hmain
  have h3 : 0 ≤ (1 + 1 / ε₀ ^ 3) * ε ^ 3 := by positivity
  calc _ ≤ C₀ * ε ^ 3 := hmain
    _ ≤ _ := by nlinarith

/-! ### The variance rate for GBM -/

/-- The fine payoff `P^f_ℓ` is measurable (Giles 2015, §5.2). -/
lemma measurable_gbmDigitalCondFine (r σ T s₀ K : ℝ) (ℓ : ℕ) :
    Measurable (gbmDigitalCondFine r σ T s₀ K ℓ) := by
  have hX : Measurable fun z : ℕ → ℝ =>
      milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1) :=
    measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _
  have hcdf : Measurable (cdf (gaussianReal 0 1)) := (monotone_cdf _).measurable
  unfold gbmDigitalCondFine gbmCondMeanFine gbmCondStdFine
  fun_prop

/-- The coarse payoff `P^c_ℓ` is measurable (Giles 2015, §5.2). -/
lemma measurable_gbmDigitalCondCoarse (r σ T s₀ K : ℝ) (ℓ : ℕ) :
    Measurable (gbmDigitalCondCoarse r σ T s₀ K ℓ) := by
  have hY : Measurable fun z : ℕ → ℝ =>
      milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) :=
    (measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _).comp measurable_pairAvg
  have hcdf : Measurable (cdf (gaussianReal 0 1)) := (monotone_cdf _).measurable
  unfold gbmDigitalCondCoarse gbmCondMeanCoarse gbmCondStdCoarse
  fun_prop

/-- The payoffs `P^f_ℓ` and `P^c_ℓ` take values in `[0, 1]`, so `P^f_{ℓ+1} − P^c_ℓ` is square
integrable (Giles 2015, §5.2). -/
lemma memLp_gbmDigitalCond_sub (r σ T s₀ K : ℝ) (ℓ : ℕ) :
    MemLp (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z)
      2 stdNormalSeq := by
  refine memLp_of_bounded (a := -1) (b := 1)
    (f := fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z)
    (Eventually.of_forall fun z => ?_) ((measurable_gbmDigitalCondFine r σ T s₀ K (ℓ + 1)).sub
      (measurable_gbmDigitalCondCoarse r σ T s₀ K ℓ)).aestronglyMeasurable 2
  unfold gbmDigitalCondFine gbmDigitalCondCoarse
  have h1 := cdf_nonneg (gaussianReal 0 1) ((gbmCondMeanFine r σ T s₀ (ℓ + 1) z - K) /
    gbmCondStdFine r σ T s₀ (ℓ + 1) z)
  have h2 := cdf_le_one (gaussianReal 0 1) ((gbmCondMeanFine r σ T s₀ (ℓ + 1) z - K) /
    gbmCondStdFine r σ T s₀ (ℓ + 1) z)
  have h3 := cdf_nonneg (gaussianReal 0 1) ((gbmCondMeanCoarse r σ T s₀ ℓ z - K) /
    gbmCondStdCoarse r σ T s₀ ℓ z)
  have h4 := cdf_le_one (gaussianReal 0 1) ((gbmCondMeanCoarse r σ T s₀ ℓ z - K) /
    gbmCondStdCoarse r σ T s₀ ℓ z)
  exact ⟨by linarith, by linarith⟩

/-- **G5.2-14/15: the variance of the conditional-expectation correction for the digital option
is `O(h_ℓ^q)` for every `q < 3/2`** (Giles 2015, §5.2, p. 36, l. 1563–1580: "This results in the
conditional distribution for the coarse path underlying at maturity matching that of the fine path
to within `O(h)`, for both the mean and the standard deviation … Consequently, the difference in
payoff between the coarse and fine paths near the payoff discontinuity is `O(h^{1/2})`, giving a
variance which is approximately `O(h^{3/2})`").  For GBM `dS = rS dt + σS dW` with `s₀ ≠ 0`,
`σ ≠ 0`, `T > 0`, a strike `K ≠ 0` and every `q < 3/2` there is `C ≥ 0` such that for every level
`ℓ + 1 ≥ 1` (`h_{ℓ+1} = T 2^{−(ℓ+1)}`) the correction `P^f_{ℓ+1} − P^c_ℓ` of the
conditional-expectation payoffs (`gbmDigitalCondFine`, `gbmDigitalCondCoarse`) is square integrable
and `E[(P^f_{ℓ+1} − P^c_ℓ)²] ≤ C h_{ℓ+1}^q`, hence `V_{ℓ+1} ≤ C h_{ℓ+1}^q`.

Proof: `condDigital_sq_rate` with the `L^{2p}` matching of the conditional means and standard
deviations (`momentBound_condMean_diff`, `momentBound_condStd_diff`), the `L^{2p}` distance
`O(√h)` of the fine value one step before maturity from `S_T` (`momentBound_gbmExact_sub_fine`),
the bounded lognormal density of `S_T` (`gbmExact_smallBall`) and `Ŝ ≠ 0` a.s.
(`ae_gbm_milsteinPath_ne_zero`), with `δ = (3/2 − max(q, 1))/6` and `2pδ ≥ 3/2`.

**Deviation.**  The exponent is every `q < 3/2`, not `3/2` itself (the paper says "approximately
`O(h^{3/2})`"); the loss comes from the tails: the matching `O(h)` holds in every `L^{2p}`, not
almost surely.  `K ≠ 0` is needed for the argument (near the strike the volatility `|σ Ŝ|` is then
bounded below); the factor `25 e^{−rT}` is omitted (it multiplies `C` by `625 e^{−2rT}`).  The
endpoint `3/2` up to a factor `(ℓ + 1)^{5/2}`, for every strike, is
`gbm_digital_condExp_variance_endpoint` (`MlmcLean.GBMDigitalCondExpEndpoint`). -/
theorem gbm_digital_condExp_variance_rate (r σ : ℝ) {s₀ T K : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (hK : K ≠ 0) {q : ℝ} (hq : q < 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      MemLp (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ K ℓ z) 2 stdNormalSeq ∧
      ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2
        ∂stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ q ∧
      variance (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ K ℓ z) stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ q := by
  obtain ⟨q₁, hq₁def⟩ : ∃ q₁ : ℝ, q₁ = max q 1 := ⟨_, rfl⟩
  have hq₁ : q₁ < 3 / 2 := hq₁def ▸ max_lt hq (by norm_num)
  have hq₁1 : 1 ≤ q₁ := hq₁def ▸ le_max_right _ _
  have hqq₁ : q ≤ q₁ := hq₁def ▸ le_max_left _ _
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (3 / 2 - q₁) / 6 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 / 4 := by rw [hδdef]; linarith
  obtain ⟨p, hp⟩ := exists_nat_gt (3 / (4 * δ))
  have hpδ : 3 / 2 ≤ 2 * p * δ := by
    rw [div_lt_iff₀ (by positivity)] at hp
    linarith
  have hp0 : 0 < p := by
    have : (0 : ℝ) < p := lt_trans (by positivity) hp
    exact_mod_cast this
  have hh : ∀ ℓ : ℕ, 0 < T / 2 ^ (ℓ + 1) := fun ℓ => by positivity
  have hhT : ∀ ℓ : ℕ, T / 2 ^ (ℓ + 1) ≤ T := fun ℓ => div_le_self hT.le (one_le_pow₀ (by norm_num))
  have hXm : ∀ ℓ : ℕ, Measurable fun z : ℕ → ℝ => milsteinPath (fun S => r * S)
      (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z (2 ^ (ℓ + 1) - 1) := fun ℓ =>
    measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _
  have hYm : ∀ ℓ : ℕ, Measurable fun z : ℕ → ℝ => milsteinPath (fun S => r * S)
      (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) := fun ℓ =>
    (measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _).comp measurable_pairAvg
  have hmcm : ∀ ℓ : ℕ, Measurable (gbmCondMeanCoarse r σ T s₀ ℓ) := fun ℓ => by
    have := hYm ℓ
    unfold gbmCondMeanCoarse
    fun_prop
  have hX0 : ∀ ℓ : ℕ, ∀ᵐ z ∂stdNormalSeq, milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ (ℓ + 1)) s₀ z (2 ^ (ℓ + 1) - 1) ≠ 0 := fun ℓ =>
    (ae_gbm_milsteinPath_ne_zero r σ hs₀ hσ (hh ℓ) _).mono fun z hz => right_ne_zero_of_mul hz
  have hY0 : ∀ ℓ : ℕ, ∀ᵐ z ∂stdNormalSeq, milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) ≠ 0 := fun ℓ =>
    (measurePreserving_pairAvg.quasiMeasurePreserving.ae (ae_gbm_milsteinPath_ne_zero r σ hs₀ hσ
      (by positivity : (0 : ℝ) < T / 2 ^ ℓ) (2 ^ ℓ - 1))).mono fun z hz => right_ne_zero_of_mul hz
  obtain ⟨C, hC, hbd⟩ := condDigital_sq_rate (μ := stdNormalSeq) (r := r) (K := K)
    (ρ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T))
    (h := fun ℓ => T / 2 ^ (ℓ + 1))
    (X := fun ℓ z => milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z
      (2 ^ (ℓ + 1) - 1))
    (Y := fun ℓ z => milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z)
      (2 ^ ℓ - 1))
    (mc := fun ℓ => gbmCondMeanCoarse r σ T s₀ ℓ) (ST := fun ℓ => gbmExact r σ T s₀ (ℓ + 1))
    hσ hK (by positivity) hδ0 hδ1 hpδ hh hXm hYm hmcm hX0 hY0
    (fun ℓ η hη => gbmExact_smallBall r σ hs₀ hσ hT K (ℓ + 1) hη)
    ((momentBound_condMean_diff r σ s₀ hT.le hp0).congr fun ℓ z => rfl)
    ((momentBound_condStd_diff r σ s₀ hT.le hp0).congr fun ℓ z => rfl)
    ((momentBound_gbmExact_sub_fine r σ s₀ hT.le hp0).congr fun ℓ z => by
      rw [milsteinPath_fine_eq_prod])
  have hexp : 3 / 2 - 6 * δ = q₁ := by rw [hδdef]; ring
  have hT' : 0 ≤ T ^ (q₁ - q) := by positivity
  have key : ∀ ℓ : ℕ, ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
      gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2 ∂stdNormalSeq ≤
      C * T ^ (q₁ - q) * (T / 2 ^ (ℓ + 1)) ^ q := fun ℓ => by
    have h1 := hbd ℓ
    rw [hexp] at h1
    calc ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
          gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2 ∂stdNormalSeq
        ≤ C * (T / 2 ^ (ℓ + 1)) ^ q₁ := h1
      _ ≤ C * (T ^ (q₁ - q) * (T / 2 ^ (ℓ + 1)) ^ q) :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow_sub_mul_rpow (hh ℓ) (hhT ℓ) hqq₁) hC
      _ = C * T ^ (q₁ - q) * (T / 2 ^ (ℓ + 1)) ^ q := by ring
  refine ⟨C * T ^ (q₁ - q), mul_nonneg hC hT', fun ℓ =>
    ⟨memLp_gbmDigitalCond_sub r σ T s₀ K ℓ, key ℓ, ?_⟩⟩
  refine (variance_le_expectation_sq ((measurable_gbmDigitalCondFine r σ T s₀ K (ℓ + 1)).sub
    (measurable_gbmDigitalCondCoarse r σ T s₀ K ℓ)).aestronglyMeasurable).trans ?_
  exact key ℓ

/-! ### G5.2-13: the conditional means and standard deviations match to within `O(h)` -/

/-- **G5.2-13: the conditional distributions of the coarse and the fine path at maturity match to
within `O(h)`, for the mean and the standard deviation, in every `L^{2m}`** (Giles 2015, §5.2,
p. 36, l. 1560–1566: "A similar treatment is used for the coarse path, except that in the final
timestep, we re-use the known value of the Brownian increment for the second last fine timestep,
which corresponds to the first half of the final coarse timestep. This results in the conditional
distribution for the coarse path underlying at maturity matching that of the fine path to within
`O(h)`, for both the mean and the standard deviation").  For GBM `dS = rS dt + σS dW`, any `s₀`,
`T ≥ 0` and `m ≥ 1` there is `C ≥ 0` such that on every level `ℓ + 1` (`h = T 2^{−(ℓ+1)}`) the
conditional means `m_f` (`gbmCondMeanFine`) and `m_c` (`gbmCondMeanCoarse`) and the conditional
standard deviations `s_f` (`gbmCondStdFine`) and `s_c` (`gbmCondStdCoarse`) of the fine and the
coarse Gaussian final values given the past satisfy `E[(m_f − m_c)^{2m}] ≤ C h^{2m}` and
`E[(s_f − s_c)^{2m}] ≤ C h^{2m}` (with integrable `2m`-th powers).

Proof: both conditional means are within `O(h)` in `L^{2m}` of the exact solution and its
Euler–Maruyama continuation: `m_f − m_c = −(1 + rh)(S_{2n+1} − Ŝ^f_{2n+1}) + (S_{2n} − Ŝ^c_n)(1 +
2rh + σΔW_{2n}) + S_{2n}((1 + rh)(A − B) + rh(B − 1))(Z_{2n})` (`momentBound_condMean_diff`: the
fine and the coarse Milstein `L^{2m}` errors `gbm_mil_moment_error_le`, the exact solution driven by
`pairAvg` at coarse times being the one driven by the fine increments at even fine times, and the
one-step `L^{2m}` error of Euler–Maruyama, `gbm_em_onestep_le`); for the standard deviations,
`|s_f − s_c| ≤ |σ|√h |Ŝ^f_{2n+1} − Ŝ^c_n|` and `Ŝ^f_{2n+1} − Ŝ^c_n = O(√h)`
(`momentBound_condStd_diff`). -/
theorem gbm_digital_cond_moments_match (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      Integrable (fun z => (gbmCondMeanFine r σ T s₀ (ℓ + 1) z -
        gbmCondMeanCoarse r σ T s₀ ℓ z) ^ (2 * m)) stdNormalSeq ∧
      ∫ z, (gbmCondMeanFine r σ T s₀ (ℓ + 1) z - gbmCondMeanCoarse r σ T s₀ ℓ z) ^ (2 * m)
        ∂stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ (2 * m) ∧
      Integrable (fun z => (gbmCondStdFine r σ T s₀ (ℓ + 1) z -
        gbmCondStdCoarse r σ T s₀ ℓ z) ^ (2 * m)) stdNormalSeq ∧
      ∫ z, (gbmCondStdFine r σ T s₀ (ℓ + 1) z - gbmCondStdCoarse r σ T s₀ ℓ z) ^ (2 * m)
        ∂stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ (2 * m) := by
  obtain ⟨C₁, hC₁, h₁⟩ := momentBound_condMean_diff r σ s₀ hT hm
  obtain ⟨C₂, hC₂, h₂⟩ := momentBound_condStd_diff r σ s₀ hT hm
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun ℓ =>
    ⟨(h₁ ℓ).1, (h₁ ℓ).2.trans ?_, (h₂ ℓ).1, (h₂ ℓ).2.trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ### The weak error, the coarsest level and (2.4) -/

/-- The fine payoff `P^f_ℓ` takes values in `[0, 1]`, so it is square integrable (Giles 2015, §5.2,
p. 36, l. 1551–1558). -/
lemma memLp_gbmDigitalCondFine (r σ T s₀ K : ℝ) (ℓ : ℕ) :
    MemLp (gbmDigitalCondFine r σ T s₀ K ℓ) 2 stdNormalSeq :=
  memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun _ =>
    ⟨cdf_nonneg _ _, cdf_le_one _ _⟩)
    (measurable_gbmDigitalCondFine r σ T s₀ K ℓ).aestronglyMeasurable 2

/-- The coarse payoff `P^c_ℓ` takes values in `[0, 1]`, so it is square integrable (Giles 2015,
§5.2, p. 36, l. 1566–1574). -/
lemma memLp_gbmDigitalCondCoarse (r σ T s₀ K : ℝ) (ℓ : ℕ) :
    MemLp (gbmDigitalCondCoarse r σ T s₀ K ℓ) 2 stdNormalSeq :=
  memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun _ =>
    ⟨cdf_nonneg _ _, cdf_le_one _ _⟩)
    (measurable_gbmDigitalCondCoarse r σ T s₀ K ℓ).aestronglyMeasurable 2

/-- **(2.4) for the conditional-expectation payoffs on GBM** (Giles 2015, §5.2, p. 36,
l. 1584–1590: "It is very important in this conditional expectation formulation that
`E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` … This ensures that the identity in Equation (2.4) is respected"):
`E[P^f_ℓ] = E[P^c_ℓ]` for every `ℓ`, where `P^c_ℓ` is the coarse payoff used on level `ℓ + 1`
(`gbm_digital_smoothing_mean_eq` with the fine step `h_{ℓ+1}` and `2^ℓ − 1` coarse steps). -/
lemma gbmDigitalCond_integral_eq (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (K : ℝ) (ℓ : ℕ) :
    ∫ z, gbmDigitalCondFine r σ T s₀ K ℓ z ∂stdNormalSeq =
      ∫ z, gbmDigitalCondCoarse r σ T s₀ K ℓ z ∂stdNormalSeq := by
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have h := gbm_digital_smoothing_mean_eq r σ hs₀ hσ hh K (2 ^ ℓ - 1)
  unfold gbmDigitalCondFine gbmDigitalCondCoarse gbmCondMeanFine gbmCondStdFine
    gbmCondMeanCoarse gbmCondStdCoarse
  rw [two_pow_succ_sub_two_eq, div_two_pow_eq_two_mul T ℓ]
  exact h.symm

/-- **The fine payoff is the conditional expectation of the digital payoff of the fine path, and
has its mean** (Giles 2015, §5.2, pp. 35–36, l. 1541–1558: "Conditional on the value `Ŝ_{N−1}`
… the numerical approximation for the final value `Ŝ_N` has a Gaussian distribution, and for a
simple digital option the conditional expectation is known analytically. Thus the fine path payoff
can be taken to be `P^f_ℓ = …`").  For `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, on every level `ℓ`,
`P^f_ℓ = E[1_{Ŝ^f_N > K} | Ŝ^f_{N−1}]` a.s. (`Ŝ^f_N = gbmMilEM`, the Milstein path with an
Euler–Maruyama last step) and `E[P^f_ℓ] = P(Ŝ^f_N > K)` (`digital_smoothing`). -/
lemma gbmDigitalCondFine_condExp (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (K : ℝ) (ℓ : ℕ) :
    stdNormalSeq[fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z) |
        MeasurableSpace.comap (fun z => milsteinPath (fun S => r * S) (fun S => σ * S)
          (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1)) inferInstance] =ᵐ[stdNormalSeq]
      gbmDigitalCondFine r σ T s₀ K ℓ ∧
    ∫ z, gbmDigitalCondFine r σ T s₀ K ℓ z ∂stdNormalSeq =
      ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z) ∂stdNormalSeq := by
  have hh : 0 < T / 2 ^ ℓ := by positivity
  have hX : Measurable fun z : ℕ → ℝ => milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1) :=
    measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _
  have hind : IndepFun (fun z : ℕ → ℝ => milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1)) (fun z => z (2 ^ ℓ - 1)) stdNormalSeq :=
    indepFun_incr_of_eq_lt hX fun z z' hzz => milsteinPath_eq_of_eq_lt _ _ _ _ hzz
  have hlaw : stdNormalSeq.map (fun z : ℕ → ℝ => z (2 ^ ℓ - 1)) = gaussianReal 0 1 :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) _).map_eq
  obtain ⟨h1, h2, -⟩ := digital_smoothing hX (measurable_pi_apply _) hind hlaw
    (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop) (by fun_prop)
    (ae_gbm_milsteinPath_ne_zero r σ hs₀ hσ hh _) hh K
  have e : (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z)) =
      fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1) +
          r * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1) *
            (T / 2 ^ ℓ) +
          σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1) *
            Real.sqrt (T / 2 ^ ℓ) * z (2 ^ ℓ - 1)) := by
    funext z
    unfold gbmMilEM emStep
    rw [mul_assoc (σ * _)]
  rw [e]
  exact ⟨h1, h2⟩

/-- **The coarse payoff is the conditional expectation of the digital payoff of the coarse path**
(Giles 2015, §5.2, p. 36, l. 1560–1574: "A similar treatment is used for the coarse path, except
that in the final timestep, we re-use the known value of the Brownian increment for the second last
fine timestep, which corresponds to the first half of the final coarse timestep … the corresponding
coarse path payoff function is `P^c_{ℓ−1} = …`").  For `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, the coarse
path used on level `ℓ + 1` ends with the Euler–Maruyama step
`Ŝ^c_N = emStep(Ŝ^c_{N−2}, ΔW_{N−2} + ΔW_{N−1})` of size `h_ℓ` (`ΔW_{N−2} = √h_{ℓ+1} Z_{N−2}`
re-used, `ΔW_{N−1} = √h_{ℓ+1} Z_{N−1}`, `N = 2^{ℓ+1}`), and
`P^c_ℓ = E[1_{Ŝ^c_N > K} | Ŝ^c_{N−2}, ΔW_{N−2}]` a.s. (`digital_smoothing_milsteinEM_mean_eq`). -/
lemma gbmDigitalCondCoarse_condExp (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) (ℓ : ℕ) :
    stdNormalSeq[fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
          (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1))
          (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2) +
            Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 1))) |
        MeasurableSpace.comap (fun z => (milsteinPath (fun S => r * S) (fun S => σ * S)
          (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1), Real.sqrt (T / 2 ^ (ℓ + 1)) *
            z (2 ^ (ℓ + 1) - 2))) inferInstance] =ᵐ[stdNormalSeq]
      gbmDigitalCondCoarse r σ T s₀ K ℓ := by
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have h := (digital_smoothing_milsteinEM_mean_eq (a := fun S => r * S) (b := fun S => σ * S)
    (by fun_prop) (by fun_prop) hh s₀ K (2 ^ ℓ - 1)
    (ae_gbm_milsteinPath_ne_zero r σ hs₀ hσ (by positivity) _)).1
  unfold gbmDigitalCondCoarse gbmCondMeanCoarse gbmCondStdCoarse
  rw [two_pow_succ_sub_two_eq, two_pow_succ_sub_one_eq, div_two_pow_eq_two_mul T ℓ]
  exact h

/-- The Milstein path with an Euler–Maruyama last step is a measurable function of the increments
(Giles 2015, §5.2, p. 35, l. 1541–1544). -/
lemma measurable_gbmMilEM (r σ T s₀ : ℝ) (ℓ : ℕ) : Measurable (gbmMilEM r σ T s₀ ℓ) := by
  have hX : Measurable fun z : ℕ → ℝ => milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ ℓ) s₀ z (2 ^ ℓ - 1) :=
    measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _
  unfold gbmMilEM emStep
  fun_prop

/-- **The fraction of paths on either side of the strike for the Milstein path with an
Euler–Maruyama last step: `O(h_ℓ^q)` for every `q < 1`** (Giles 2015, §5.1, p. 33, l. 1436–1441:
"there is a bounded density of paths terminating in the neighbourhood of `K`", for the fine path
of §5.2, p. 35, l. 1541–1544).  For `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, any `K` and `q < 1` there is
`C` with `P(1_{S_T > K} ≠ 1_{Ŝ^f_N > K}) ≤ C h_ℓ^q` on every level (`digital_mismatch_le_rpow`
with the lognormal density `gbmExact_smallBall` and the strong error
`momentBound_gbmExact_sub_milEM`). -/
lemma gbm_milEM_mismatch_rate (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (K : ℝ) {q : ℝ} (hq : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ z) ≠
        (Set.Ioi K).indicator 1 (gbmMilEM r σ T s₀ ℓ z)} ≤ C * (T / 2 ^ ℓ) ^ q := by
  have hq' : q < ((2 : ℕ) : ℝ) / 2 := by rw [Nat.cast_two, div_self two_ne_zero]; exact hq
  obtain ⟨m, hm, hqm⟩ := exists_moment_exponent two_pos hq'
  obtain ⟨B, hB, hb⟩ := momentBound_gbmExact_sub_milEM r σ s₀ hT.le hm
  set ρ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)
    with hρ
  have hρ0 : 0 < ρ := by
    have := abs_pos.2 hs₀
    have := abs_pos.2 hσ
    have := Real.sqrt_pos.2 hT
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    positivity
  refine ⟨2 * (2 * ρ) ^ (2 * (m : ℝ) / (2 * m + 1)) * B ^ (1 / (2 * m + 1 : ℝ)) *
    T ^ (((2 * m : ℕ) : ℝ) / (2 * m + 1) - q), by positivity, fun ℓ => ?_⟩
  have hh : 0 < T / 2 ^ ℓ := by positivity
  have hhT : T / 2 ^ ℓ ≤ T := div_le_self hT.le (one_le_pow₀ (by norm_num))
  exact digital_mismatch_le_rpow (μ := stdNormalSeq) (K := K) hρ0
    (fun δ hδ => gbmExact_smallBall r σ hs₀ hσ hT K ℓ hδ) (hb ℓ).1 hB hh hhT (hb ℓ).2 hqm

/-- **The weak error: `|E[P^f_ℓ] − E[H(S_T − K)]| = O(h_ℓ^q)` for every `q < 1`** (Giles
2015, §5.2, p. 36, l. 1578–1580: "This leads to `α = 1`, `β = 3/2` and `γ = 1`"; condition (i) of
Theorem 1).  For `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, any strike `K` and every `q < 1` there is `C ≥ 0` with,
on every level `ℓ`: `E[P^f_ℓ] = P(Ŝ^f_N > K)` (`Ŝ^f_N` the Milstein path with an Euler–Maruyama last
step, `gbmMilEM`) and `|E[P^f_ℓ] − E[H(S_T − K)]| ≤ C h_ℓ^q`, with
`E[H(S_T − K)] = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} dN(0,1)(w)`.

Proof: `gbmDigitalCondFine_condExp`, then the weak error is at most the probability that `Ŝ^f_N`
and `S_T` end on different sides of `K` (`abs_integral_digital_sub_le`), which is `O(h^q)` by the
bounded lognormal density of `S_T` and the strong error `E[(S_T − Ŝ^f_N)^{2m}] = O(h^{2m})`
(`gbm_milEM_mismatch_rate`).

**Deviation.**  The paper's `α = 1` is not proved (only every `q < 1`); the weak rate here comes
from the strong error and the density, not from a weak-order analysis.  Theorem 1 only needs
`α ≥ ½ min(β, γ) = ½`. -/
theorem gbm_digital_condExp_weak_rate (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) {q : ℝ} (hq : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      ∫ z, gbmDigitalCondFine r σ T s₀ K ℓ z ∂stdNormalSeq =
        ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z) ∂stdNormalSeq ∧
      |∫ z, gbmDigitalCondFine r σ T s₀ K ℓ z ∂stdNormalSeq -
          ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
            (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1| ≤
        C * (T / 2 ^ ℓ) ^ q := by
  obtain ⟨C, hC, hmis⟩ := gbm_milEM_mismatch_rate r σ hs₀ hσ hT K hq
  refine ⟨C, hC, fun ℓ => ?_⟩
  obtain ⟨-, hmean'⟩ := gbmDigitalCondFine_condExp r σ hs₀ hσ hT K ℓ
  refine ⟨hmean', ?_⟩
  rw [hmean', ← integral_digital_gbmExact r σ T s₀ K ℓ]
  exact (abs_integral_digital_sub_le (measurable_gbmExact r σ T s₀ ℓ)
    (measurable_gbmMilEM r σ T s₀ ℓ) K).trans (hmis ℓ)

/-- **Zero variance on the coarsest level** (Giles 2015, §5.2, p. 36,
l. 1579–1583: "One particularly interesting feature of these results is that there is zero
variance on the coarsest level. This is because there is only one timestep on the coarsest level,
and therefore the conditional expectation is taken immediately and every sample gives the same
payoff").  On level `0` (one step of size `T`) the fine path before the last step is `S_0 = s₀`, so
`P^f_0 = Φ((s₀ + r s₀ T − K)/(|σ s₀| √T))` for every sample, `P^f_0 ∈ L²` and `V[P^f_0] = 0`. -/
theorem gbm_digital_condExp_level_zero (r σ s₀ K T : ℝ) :
    (∀ z, gbmDigitalCondFine r σ T s₀ K 0 z =
      cdf (gaussianReal 0 1) ((s₀ + r * s₀ * T - K) / (|σ * s₀| * Real.sqrt T))) ∧
    MemLp (gbmDigitalCondFine r σ T s₀ K 0) 2 stdNormalSeq ∧
    variance (gbmDigitalCondFine r σ T s₀ K 0) stdNormalSeq = 0 := by
  have hz : ∀ z, gbmDigitalCondFine r σ T s₀ K 0 z =
      cdf (gaussianReal 0 1) ((s₀ + r * s₀ * T - K) / (|σ * s₀| * Real.sqrt T)) := fun z => by
    unfold gbmDigitalCondFine gbmCondMeanFine gbmCondStdFine
    rw [pow_zero, pow_zero, div_one, Nat.sub_self]
    rfl
  refine ⟨hz, memLp_gbmDigitalCondFine r σ T s₀ K 0, ?_⟩
  have e : gbmDigitalCondFine r σ T s₀ K 0 =
      fun _ => cdf (gaussianReal 0 1) ((s₀ + r * s₀ * T - K) / (|σ * s₀| * Real.sqrt T)) :=
    funext hz
  rw [e, variance_eq_integral measurable_const.aemeasurable]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

/-! ### Theorem 1 end to end: cost `O(ε⁻²)` -/

/-- **Theorem 1 for a fine/coarse estimator with `β > γ = 1`** (Giles 2015, §2.1, Theorem 1, p. 6,
the case `β > γ`: cost `O(ε⁻²)`, with (2.4), p. 8).  Let `T > 0`, `α ≥ ½`, `β > 1`, `P^f_ℓ`,
`P^c_ℓ` (`Pf ℓ`, `Pc ℓ`) measurable square-integrable functions of the increments
`Z ∼ N(0,1)^{⊗ℕ}` with `E[P^f_ℓ] = E[P^c_ℓ]` (2.4), `P` integrable,
`|E[P^f_ℓ] − E[P]| ≤ c₁ h_ℓ^α` and `V[P^f_ℓ − P^c_{ℓ−1}] ≤ c₂ h_ℓ^β` (`P^c_{−1} = 0`,
`fineCoarseDiff`), `h_ℓ = T 2^{−ℓ}`, independent samples and cost `2^ℓ` per level-`ℓ` sample.
Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the
error of the multilevel estimator of `E[P]` is square integrable, its mean square is `< ε²`, and
`∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²` (`giles_theorem1_fineCoarse`, `complexityBound_of_lt`). -/
lemma theorem1_fineCoarse_of_rate_gt {T : ℝ} (hT : 0 < T) {α β : ℝ} (hα : 1 / 2 ≤ α)
    (hβ : 1 < β) {Pf Pc : ℕ → (ℕ → ℝ) → ℝ} {P : (ℕ → ℝ) → ℝ} (hPfm : ∀ ℓ, Measurable (Pf ℓ))
    (hPcm : ∀ ℓ, Measurable (Pc ℓ)) (hPf : ∀ ℓ, MemLp (Pf ℓ) 2 stdNormalSeq)
    (hPc : ∀ ℓ, MemLp (Pc ℓ) 2 stdNormalSeq) (hP : Integrable P stdNormalSeq)
    (h24 : ∀ ℓ, ∫ z, Pf ℓ z ∂stdNormalSeq = ∫ z, Pc ℓ z ∂stdNormalSeq) {c₁ c₂ : ℝ}
    (h_i : ∀ ℓ : ℕ, |∫ z, Pf ℓ z ∂stdNormalSeq - ∫ z, P z ∂stdNormalSeq| ≤
      c₁ * (T / 2 ^ ℓ) ^ α)
    (h_iii : ∀ ℓ : ℕ, variance (fineCoarseDiff Pf Pc ℓ) stdNormalSeq ≤ c₂ * (T / 2 ^ ℓ) ^ β) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf Pc)
            (fun p x => x p) ℓ (N ℓ) x - ∫ z, P z ∂stdNormalSeq) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf Pc)
            (fun p x => x p) ℓ (N ℓ) x - ∫ z, P z ∂stdNormalSeq) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hα0 : 0 < α := by linarith
  have hc₁ : 0 < (|c₁| + 1) * T ^ α := by positivity
  have h_i' : ∀ ℓ : ℕ, |∫ z, Pf ℓ z - P z ∂stdNormalSeq| ≤
      (|c₁| + 1) * T ^ α * (2 : ℝ) ^ (-(α * (ℓ : ℝ))) := fun ℓ => by
    rw [integral_sub ((hPf ℓ).integrable one_le_two) hP]
    have h2 : 0 ≤ T ^ α * (2 : ℝ) ^ (-(α * (ℓ : ℝ))) := by positivity
    calc _ ≤ c₁ * (T / 2 ^ ℓ) ^ α := h_i ℓ
      _ = c₁ * (T ^ α * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) := by rw [div_two_pow_rpow hT.le]
      _ ≤ (|c₁| + 1) * (T ^ α * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c₁]) h2
      _ = _ := by ring
  have hc₂ : 0 < (|c₂| + 1) * T ^ β := by positivity
  have h_iii' : ∀ ℓ, variance (fineCoarseDiff Pf Pc ℓ) stdNormalSeq ≤
      (|c₂| + 1) * T ^ β * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) := fun ℓ => by
    have h2 : 0 ≤ T ^ β * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) := by positivity
    calc _ ≤ c₂ * (T / 2 ^ ℓ) ^ β := h_iii ℓ
      _ = c₂ * (T ^ β * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) := by rw [div_two_pow_rpow hT.le]
      _ ≤ (|c₂| + 1) * (T ^ β * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c₂]) h2
      _ = _ := by ring
  have h_iv : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ 1 * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, one_mul, Real.rpow_natCast]
  have hαβγ : min β 1 / 2 ≤ α := by
    rw [min_eq_right hβ.le]
    linarith
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) P Pf Pc (fun p x => x p)
    (fun ℓ _ _ => (2 : ℝ) ^ ℓ) (fun ℓ => (2 : ℝ) ^ ℓ) (α := α) (β := β) (γ := 1) hα0
    (by linarith) one_pos hc₁ hc₂ one_pos hαβγ hω hind hP hPfm hPcm hPf hPc h24
    (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i' h_iii' h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω
    (memLp_fineCoarseDiff hPf hPc) ℓ (N ℓ)).sub (memLp_const _)).integrable_sq, hmse, ?_⟩
  unfold totalCost at hcost
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul] at hcost
  rw [complexityBound_of_lt hβ ε] at hcost
  exact hcost

/-- **Theorem 1 end to end for the conditional-expectation estimator of the digital option: mean
square error `< ε²` at cost `O(ε⁻²)`** (Giles 2015, §5.2, p. 36, l. 1578–1580: "This leads to
`α = 1`, `β = 3/2` and `γ = 1`. Since `β > γ`, the MLMC complexity is `O(ε⁻²)`", with Theorem 1,
§2.1, p. 6, and (2.4), l. 1584–1590).  For GBM `dS = rS dt + σS dW` with `s₀ ≠ 0`,
`σ ≠ 0`, `T > 0` and a strike `K ≠ 0`: level `ℓ` uses `2^ℓ` fine steps of size `T 2^{−ℓ}` (Milstein,
with the last step replaced by the conditional expectation), the fine payoff is `P^f_ℓ`
(`gbmDigitalCondFine`), the coarse payoff on level `ℓ + 1` is `P^c_ℓ` (`gbmDigitalCondCoarse`,
driven by the summed increments and re-using the first half of the last coarse increment), the
level-`ℓ` correction is `P^f_ℓ − P^c_{ℓ−1}` (`fineCoarseDiff`), the samples are independent and a
level-`ℓ` sample costs `2^ℓ`.  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are
`L` and `N_ℓ ≥ 1` for which the multilevel estimator of
`E[H(S_T − K)] = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} dN(0,1)(w)` has a square-integrable error with
mean square `< ε²`, at cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²`: no logarithmic factor.

Proof: Theorem 1 with `α = 3/4` (`gbm_digital_condExp_weak_rate`), `β = 5/4`
(`gbm_digital_condExp_variance_rate` on the levels `ℓ ≥ 1`, `gbm_digital_condExp_level_zero` on
level `0`), `γ = 1` and (2.4) (`gbmDigitalCond_integral_eq`), via
`theorem1_fineCoarse_of_rate_gt`.

**How close to the paper.**  The complexity `O(ε⁻²)` is the paper's.  The rates used are smaller
than the paper's (`α = 3/4 < 1`, `β = 5/4 < 3/2`), which only changes the constant `c₄`; any
`α ∈ [½, 1)` and `β ∈ (1, 3/2)` would do.  `K ≠ 0` is assumed (used for the variance rate;
`gbm_digital_condExp_theorem1_all` in `MlmcLean.GBMDigitalCondExpExtras` drops it); the
factor `25 e^{−rT}` of the paper's payoffs is omitted (the estimator of `25 e^{−rT} E[H(S_T − K)]`
is `25 e^{−rT}` times this one). -/
theorem gbm_digital_condExp_theorem1 (r σ : ℝ) {s₀ T K : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (hK : K ≠ 0) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (gbmDigitalCondFine r σ T s₀ K)
              (gbmDigitalCondCoarse r σ T s₀ K)) (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (gbmDigitalCondFine r σ T s₀ K)
              (gbmDigitalCondCoarse r σ T s₀ K)) (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨C₁, -, hw⟩ := gbm_digital_condExp_weak_rate r σ hs₀ hσ hT K (q := 3 / 4) (by norm_num)
  obtain ⟨C₂, hC₂, hv⟩ := gbm_digital_condExp_variance_rate r σ hs₀ hσ hT hK (q := 5 / 4)
    (by norm_num)
  obtain ⟨c₄, hc₄, h⟩ := theorem1_fineCoarse_of_rate_gt hT (α := 3 / 4) (β := 5 / 4)
    (by norm_num) (by norm_num)
    (Pf := gbmDigitalCondFine r σ T s₀ K) (Pc := gbmDigitalCondCoarse r σ T s₀ K)
    (P := fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ 0 z))
    (measurable_gbmDigitalCondFine r σ T s₀ K) (measurable_gbmDigitalCondCoarse r σ T s₀ K)
    (memLp_gbmDigitalCondFine r σ T s₀ K) (memLp_gbmDigitalCondCoarse r σ T s₀ K)
    (integrable_digital (measurable_gbmExact r σ T s₀ 0) K)
    (gbmDigitalCond_integral_eq r σ hs₀ hσ hT K) (c₁ := C₁) (c₂ := C₂)
    (fun ℓ => by rw [integral_digital_gbmExact]; exact (hw ℓ).2)
    (fun ℓ => by
      cases ℓ with
      | zero =>
        rw [fineCoarseDiff, (gbm_digital_condExp_level_zero r σ s₀ K T).2.2]
        positivity
      | succ ℓ => exact (hv ℓ).2.2)
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  rw [integral_digital_gbmExact] at hint hmse
  exact ⟨L, N, hN, hint, hmse, hcost⟩

/-! ### Splitting (Giles 2015, §5.2, l. 1591–1600) -/

/-- **The second moment of a sample mean of i.i.d. sub-samples** (the splitting estimator, Giles
2015, §5.2, p. 36, l. 1594–1598: "for each set of Brownian increments up to one fine timestep before
the end, one uses a number of samples of the final Brownian increment to produce an average
payoff").  For a measurable `F` with `|F| ≤ 1` and `M ≥ 1` i.i.d. `Y_i ∼ N(0,1)`,
`E[((1/M) ∑_{i<M} F(Y_i))²] ≤ (E[F(Y)])² + E[F(Y)²]/M` (the variance of the sum is the sum of the
variances, `IndepFun.variance_sum`). -/
lemma integral_sq_sampleMean_le {F : ℝ → ℝ} (hF : Measurable F) (hFb : ∀ w, |F w| ≤ 1) {M : ℕ}
    (hM : 0 < M) :
    ∫ y, ((∑ i ∈ range M, F (y i)) / M) ^ 2 ∂stdNormalSeq ≤
      (∫ w, F w ∂gaussianReal 0 1) ^ 2 + (∫ w, F w ^ 2 ∂gaussianReal 0 1) / M := by
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hev : ∀ i, MeasurePreserving (fun y : ℕ → ℝ => y i) stdNormalSeq (gaussianReal 0 1) :=
    fun i => measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i
  have hXm : ∀ i, Measurable fun y : ℕ → ℝ => F (y i) := fun i => hF.comp (measurable_pi_apply i)
  have hXL : ∀ i, MemLp (fun y : ℕ → ℝ => F (y i)) 2 stdNormalSeq := fun i =>
    memLp_of_bounded (a := -1) (b := 1)
      (Eventually.of_forall fun (y : ℕ → ℝ) => abs_le.1 (hFb (y i)))
      (hXm i).aestronglyMeasurable 2
  have hind : iIndepFun (fun i (y : ℕ → ℝ) => F (y i)) stdNormalSeq :=
    iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ x => F x) fun _ => hF
  have hmean : ∀ i, ∫ y, F (y i) ∂stdNormalSeq = ∫ w, F w ∂gaussianReal 0 1 := fun i =>
    integral_comp_of_measurePreserving (hev i) hF.aestronglyMeasurable
  have hsq : ∀ i, ∫ y, F (y i) ^ 2 ∂stdNormalSeq = ∫ w, F w ^ 2 ∂gaussianReal 0 1 := fun i =>
    integral_comp_of_measurePreserving (hev i) (hF.pow_const 2).aestronglyMeasurable
  have hvar : ∀ i, variance (fun y : ℕ → ℝ => F (y i)) stdNormalSeq ≤
      ∫ w, F w ^ 2 ∂gaussianReal 0 1 := fun i => by
    rw [variance_eq_sub (hXL i)]
    simp only [Pi.pow_apply]
    rw [hsq i]
    nlinarith [sq_nonneg (∫ y, F (y i) ∂stdNormalSeq)]
  have hS : (fun y : ℕ → ℝ => ∑ i ∈ range M, F (y i)) =
      ∑ i ∈ range M, (fun y : ℕ → ℝ => F (y i)) := by
    funext y
    rw [Finset.sum_apply]
  have hSL : MemLp (fun y : ℕ → ℝ => ∑ i ∈ range M, F (y i)) 2 stdNormalSeq := by
    rw [hS]
    exact memLp_finsetSum' _ fun i _ => hXL i
  have hvarS : variance (fun y : ℕ → ℝ => ∑ i ∈ range M, F (y i)) stdNormalSeq =
      ∑ i ∈ range M, variance (fun y : ℕ → ℝ => F (y i)) stdNormalSeq := by
    rw [hS]
    exact IndepFun.variance_sum (fun i _ => hXL i) (fun i _ j _ hij => hind.indepFun hij)
  have hES : ∫ y, ∑ i ∈ range M, F (y i) ∂stdNormalSeq = M * ∫ w, F w ∂gaussianReal 0 1 := by
    rw [integral_finsetSum _ (fun i _ => (hXL i).integrable one_le_two)]
    simp only [hmean, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hY : MemLp (fun y : ℕ → ℝ => (1 / M : ℝ) * ∑ i ∈ range M, F (y i)) 2 stdNormalSeq :=
    hSL.const_mul _
  have e0 : ∀ y : ℕ → ℝ, (∑ i ∈ range M, F (y i)) / M = (1 / M : ℝ) * ∑ i ∈ range M, F (y i) :=
    fun y => by ring
  simp only [e0]
  have h1 : ∫ y, ((1 / M : ℝ) * ∑ i ∈ range M, F (y i)) ^ 2 ∂stdNormalSeq =
      variance (fun y : ℕ → ℝ => (1 / M : ℝ) * ∑ i ∈ range M, F (y i)) stdNormalSeq +
        (∫ y, (1 / M : ℝ) * ∑ i ∈ range M, F (y i) ∂stdNormalSeq) ^ 2 := by
    rw [variance_eq_sub hY]
    simp only [Pi.pow_apply]
    ring
  have h2 : variance (fun y : ℕ → ℝ => (1 / M : ℝ) * ∑ i ∈ range M, F (y i)) stdNormalSeq =
      (1 / M : ℝ) ^ 2 * variance (fun y : ℕ → ℝ => ∑ i ∈ range M, F (y i)) stdNormalSeq :=
    variance_const_mul _ _ _
  have h3 : ∫ y, (1 / M : ℝ) * ∑ i ∈ range M, F (y i) ∂stdNormalSeq =
      ∫ w, F w ∂gaussianReal 0 1 := by
    rw [integral_const_mul, hES]
    field_simp
  have h4 : variance (fun y : ℕ → ℝ => ∑ i ∈ range M, F (y i)) stdNormalSeq ≤
      M * ∫ w, F w ^ 2 ∂gaussianReal 0 1 := by
    rw [hvarS]
    calc ∑ i ∈ range M, variance (fun y : ℕ → ℝ => F (y i)) stdNormalSeq
        ≤ ∑ _i ∈ range M, ∫ w, F w ^ 2 ∂gaussianReal 0 1 := Finset.sum_le_sum fun i _ => hvar i
      _ = M * ∫ w, F w ^ 2 ∂gaussianReal 0 1 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [h1, h2, h3]
  have h5 : (1 / M : ℝ) ^ 2 * variance (fun y : ℕ → ℝ => ∑ i ∈ range M, F (y i)) stdNormalSeq ≤
      (∫ w, F w ^ 2 ∂gaussianReal 0 1) / M := by
    calc (1 / M : ℝ) ^ 2 * variance (fun y : ℕ → ℝ => ∑ i ∈ range M, F (y i)) stdNormalSeq
        ≤ (1 / M : ℝ) ^ 2 * (M * ∫ w, F w ^ 2 ∂gaussianReal 0 1) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (∫ w, F w ^ 2 ∂gaussianReal 0 1) / M := by
          field_simp
  linarith

/-- **The splitting estimator against the conditional expectation, by Fubini** (Giles 2015, §5.2,
p. 36, l. 1594–1600: "If the number of sub-samples is chosen appropriately, the variance is the
same, to leading order").  Let the main increments `z` and the sub-samples `y` be independent
i.i.d. `N(0,1)` sequences and `d(z, w)` measurable with `|d| ≤ 1` (the difference of the fine and
the coarse payoff when the last fine increment is `w`).  Then the average over `M ≥ 1` sub-samples
satisfies `E[((1/M) ∑_{i<M} d(z, y_i))²] ≤ E[(∫ d(z, w) dN(0,1)(w))²] + E[d(z, y_0)²]/M`: the
conditional expectation plus the mean conditional second moment divided by `M`
(`integral_sq_sampleMean_le` for every `z`, `integral_prod`). -/
lemma integral_sq_split_le {d : (ℕ → ℝ) → ℝ → ℝ}
    (hd : Measurable fun q : (ℕ → ℝ) × ℝ => d q.1 q.2) (hdb : ∀ z w, |d z w| ≤ 1) {M : ℕ}
    (hM : 0 < M) :
    ∫ p, ((∑ i ∈ range M, d p.1 (p.2 i)) / M) ^ 2 ∂(stdNormalSeq.prod stdNormalSeq) ≤
      ∫ z, (∫ w, d z w ∂gaussianReal 0 1) ^ 2 ∂stdNormalSeq +
        (∫ p, d p.1 (p.2 0) ^ 2 ∂(stdNormalSeq.prod stdNormalSeq)) / M := by
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hdi : ∀ i, Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => d p.1 (p.2 i) := fun i =>
    hd.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hsum_b : ∀ (z : ℕ → ℝ) (y : ℕ → ℝ), |(∑ i ∈ range M, d z (y i)) / M| ≤ 1 := fun z y => by
    rw [abs_div, abs_of_pos hM', div_le_one hM']
    calc |∑ i ∈ range M, d z (y i)| ≤ ∑ i ∈ range M, |d z (y i)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ range M, (1 : ℝ) := Finset.sum_le_sum fun i _ => hdb z (y i)
      _ = M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hsq_b : ∀ x : ℝ, |x| ≤ 1 → |x ^ 2| ≤ 1 := fun x hx => by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) hx
  have hm : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      ((∑ i ∈ range M, d p.1 (p.2 i)) / M) ^ 2 :=
    ((Finset.measurable_sum _ fun i _ => hdi i).div_const _).pow_const 2
  have hint : Integrable (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      ((∑ i ∈ range M, d p.1 (p.2 i)) / M) ^ 2) (stdNormalSeq.prod stdNormalSeq) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact hsq_b _ (hsum_b p.1 p.2))
  have hm0 : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => d p.1 (p.2 0) ^ 2 := (hdi 0).pow_const 2
  have hint0 : Integrable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => d p.1 (p.2 0) ^ 2)
      (stdNormalSeq.prod stdNormalSeq) :=
    Integrable.of_bound hm0.aestronglyMeasurable 1 (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact hsq_b _ (hdb _ _))
  rw [integral_prod _ hint, integral_prod _ hint0]
  have hev : MeasurePreserving (fun y : ℕ → ℝ => y 0) stdNormalSeq (gaussianReal 0 1) :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0
  have hdz : ∀ z, Measurable fun w => d z w := fun z =>
    hd.comp (measurable_const.prodMk measurable_id)
  have hpt : ∀ z : ℕ → ℝ, ∫ y, ((∑ i ∈ range M, d z (y i)) / M) ^ 2 ∂stdNormalSeq ≤
      (∫ w, d z w ∂gaussianReal 0 1) ^ 2 + (∫ y, d z (y 0) ^ 2 ∂stdNormalSeq) / M := fun z => by
    rw [integral_comp_of_measurePreserving hev (f := fun w => d z w ^ 2)
      ((hdz z).pow_const 2).aestronglyMeasurable]
    exact integral_sq_sampleMean_le (hdz z) (hdb z) hM
  have hA : Integrable (fun z : ℕ → ℝ => (∫ w, d z w ∂gaussianReal 0 1) ^ 2) stdNormalSeq := by
    have hsm : StronglyMeasurable fun z : ℕ → ℝ => ∫ w, d z w ∂gaussianReal 0 1 :=
      hd.stronglyMeasurable.integral_prod_right'
    refine Integrable.of_bound (hsm.measurable.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    refine hsq_b _ ?_
    calc |∫ w, d z w ∂gaussianReal 0 1| ≤ ∫ w, |d z w| ∂gaussianReal 0 1 :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _w, (1 : ℝ) ∂gaussianReal 0 1 :=
          integral_mono (Integrable.of_bound (hdz z).abs.aestronglyMeasurable 1
            (Eventually.of_forall fun w => by rw [Real.norm_eq_abs, abs_abs]; exact hdb z w))
            (integrable_const 1) fun w => hdb z w
      _ = 1 := by simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  have hB : Integrable (fun z : ℕ → ℝ => (∫ y, d z (y 0) ^ 2 ∂stdNormalSeq) / M) stdNormalSeq :=
    hint0.integral_prod_left.div_const _
  calc ∫ z, ∫ y, ((∑ i ∈ range M, d z (y i)) / M) ^ 2 ∂stdNormalSeq ∂stdNormalSeq
      ≤ ∫ z, ((∫ w, d z w ∂gaussianReal 0 1) ^ 2 + (∫ y, d z (y 0) ^ 2 ∂stdNormalSeq) / M)
          ∂stdNormalSeq := integral_mono hint.integral_prod_left (hA.add hB) hpt
    _ = _ := by rw [integral_add hA hB, integral_div]

/-- **The splitting payoff of the fine path** (Giles 2015, §5.2, p. 36, l. 1591–1598: "In this
case, one can use the technique of "splitting" … Here the conditional expectation is replaced by a
numerical estimate, averaging over a number of sub-samples. i.e. for each set of Brownian
increments up to one fine timestep before the end, one uses a number of samples of the final
Brownian increment to produce an average payoff").  On level `ℓ`, with the main increments `p.1`
and the sub-samples `p.2 = (Y_0, Y_1, …)`: `(1/M) ∑_{i<M} H(Ŝ^{f,i}_N − K)`, where `Ŝ^{f,i}_N` is
the Milstein path up to `t_{N−1}` followed by the Euler–Maruyama step with the `i`-th sub-sample
`√h_ℓ Y_i` of the last increment. -/
noncomputable def gbmDigitalSplitFine (r σ T s₀ K : ℝ) (M ℓ : ℕ) (p : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ :=
  (∑ i ∈ range M, (Set.Ioi K).indicator (1 : ℝ → ℝ)
    (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
      (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ p.1 (2 ^ ℓ - 1))
      (Real.sqrt (T / 2 ^ ℓ) * p.2 i))) / M

/-- **The splitting payoff of the coarse path, used on level `ℓ + 1`** (Giles 2015, §5.2, p. 36,
l. 1591–1598, with the coarse path of l. 1560–1563): `(1/M) ∑_{i<M} H(Ŝ^{c,i}_N − K)`, where
`Ŝ^{c,i}_N` is the coarse Milstein path up to `t_{N−2}` (`N = 2^{ℓ+1}`) followed by the
Euler–Maruyama coarse step with the known increment `ΔW_{N−2} = √h_{ℓ+1} Z_{N−2}` and the `i`-th
sub-sample `√h_{ℓ+1} Y_i` of `ΔW_{N−1}` (the same sub-samples as the fine path). -/
noncomputable def gbmDigitalSplitCoarse (r σ T s₀ K : ℝ) (M ℓ : ℕ) (p : (ℕ → ℝ) × (ℕ → ℝ)) :
    ℝ :=
  (∑ i ∈ range M, (Set.Ioi K).indicator (1 : ℝ → ℝ)
    (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
      (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg p.1) (2 ^ ℓ - 1))
      (Real.sqrt (T / 2 ^ (ℓ + 1)) * p.1 (2 ^ (ℓ + 1) - 2) +
        Real.sqrt (T / 2 ^ (ℓ + 1)) * p.2 i))) / M

/-- The coarse path at maturity on level `ℓ + 1` (re-using `ΔW_{N−2}`) is the fine path with an
Euler–Maruyama last step on level `ℓ`, driven by the summed increments (Giles 2015, §5.2, p. 36,
l. 1560–1563). -/
lemma gbmMilEM_pairAvg (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmMilEM r σ T s₀ ℓ (pairAvg z) =
      emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1))
        (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2) +
          Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 1)) := by
  unfold gbmMilEM
  congr 1
  rw [pairAvg, two_pow_succ_sub_two_eq, two_pow_succ_sub_one_eq, div_two_pow_eq_two_mul T ℓ,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- **The splitting estimator on level `ℓ + 1`, against the conditional-expectation estimator**
(Giles 2015, §5.2, p. 36, l. 1594–1600: "If the number of sub-samples is chosen appropriately, the
variance is the same, to leading order").  For `s₀ ≠ 0`, `σ ≠ 0`, `T > 0` and `M ≥ 1` sub-samples
(independent of the main increments, `stdNormalSeq.prod stdNormalSeq`),
`E[(P^{f,M}_{ℓ+1} − P^{c,M}_ℓ)²] ≤ E[(P^f_{ℓ+1} − P^c_ℓ)²] + P(D ≠ 0)/M`, where `P^f`, `P^c` are the
conditional-expectation payoffs and `D = H(Ŝ^f_N − K) − H(Ŝ^c_N − K)` the digital correction of the
fine and the coarse path with the same last increment: the conditional mean of a sub-sample term
is the conditional expectation (`integral_digital_gaussian`), and its conditional second moment
has mean `P(D ≠ 0)` (`measurePreserving_update_prod`, `integral_sq_split_le`). -/
lemma gbm_split_sq_le (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T) (K : ℝ)
    (ℓ : ℕ) {M : ℕ} (hM : 0 < M) :
    ∫ p, (gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p - gbmDigitalSplitCoarse r σ T s₀ K M ℓ p) ^ 2
        ∂(stdNormalSeq.prod stdNormalSeq) ≤
      ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2
          ∂stdNormalSeq +
        stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ (ℓ + 1) z) ≠
          (Set.Ioi K).indicator 1 (gbmMilEM r σ T s₀ ℓ (pairAvg z))} / M := by
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have hsh : 0 < Real.sqrt (T / 2 ^ (ℓ + 1)) := Real.sqrt_pos.2 hh
  have hXm : Measurable fun z : ℕ → ℝ => milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ (ℓ + 1)) s₀ z (2 ^ (ℓ + 1) - 1) :=
    measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _
  have hYm : Measurable fun z : ℕ → ℝ => milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) :=
    (measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _).comp measurable_pairAvg
  have hind : Measurable ((Set.Ioi K).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Ioi
  -- the difference of the payoffs with the last fine increment `w`
  obtain ⟨d, hd⟩ : ∃ d : (ℕ → ℝ) → ℝ → ℝ, d = fun z w =>
      (Set.Ioi K).indicator (1 : ℝ → ℝ) (emStep (fun S => r * S) (fun S => σ * S)
        (T / 2 ^ (ℓ + 1)) (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z
          (2 ^ (ℓ + 1) - 1)) (Real.sqrt (T / 2 ^ (ℓ + 1)) * w)) -
      (Set.Ioi K).indicator 1 (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1))
        (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2) +
          Real.sqrt (T / 2 ^ (ℓ + 1)) * w)) := ⟨_, rfl⟩
  have hdm : Measurable fun q : (ℕ → ℝ) × ℝ => d q.1 q.2 := by
    rw [hd]
    have hf : Measurable fun q : (ℕ → ℝ) × ℝ => emStep (fun S => r * S) (fun S => σ * S)
        (T / 2 ^ (ℓ + 1)) (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀
          q.1 (2 ^ (ℓ + 1) - 1)) (Real.sqrt (T / 2 ^ (ℓ + 1)) * q.2) := by
      unfold emStep
      fun_prop
    have hc : Measurable fun q : (ℕ → ℝ) × ℝ => emStep (fun S => r * S) (fun S => σ * S)
        (T / 2 ^ ℓ) (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg q.1)
          (2 ^ ℓ - 1)) (Real.sqrt (T / 2 ^ (ℓ + 1)) * q.1 (2 ^ (ℓ + 1) - 2) +
            Real.sqrt (T / 2 ^ (ℓ + 1)) * q.2) := by
      have hz : Measurable fun q : (ℕ → ℝ) × ℝ => q.1 (2 ^ (ℓ + 1) - 2) :=
        (measurable_pi_apply _).comp measurable_fst
      have hYq : Measurable fun q : (ℕ → ℝ) × ℝ => milsteinPath (fun S => r * S)
          (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg q.1) (2 ^ ℓ - 1) := hYm.comp measurable_fst
      unfold emStep
      fun_prop
    exact (hind.comp hf).sub (hind.comp hc)
  have hdb : ∀ z w, |d z w| ≤ 1 := fun z w => by
    rw [hd]
    dsimp only
    rcases digital_eq_zero_or_one K (emStep (fun S => r * S) (fun S => σ * S)
        (T / 2 ^ (ℓ + 1)) (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z
          (2 ^ (ℓ + 1) - 1)) (Real.sqrt (T / 2 ^ (ℓ + 1)) * w)) with h1 | h1 <;>
      rcases digital_eq_zero_or_one K (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1))
        (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2) +
          Real.sqrt (T / 2 ^ (ℓ + 1)) * w)) with h2 | h2 <;>
      simp only [h1, h2, sub_zero, sub_self, zero_sub, abs_neg, abs_one, abs_zero, le_refl,
        zero_le_one]
  -- the splitting difference is the sub-sample average of `d`
  have hsplit : ∀ p : (ℕ → ℝ) × (ℕ → ℝ), gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
      gbmDigitalSplitCoarse r σ T s₀ K M ℓ p = (∑ i ∈ range M, d p.1 (p.2 i)) / M := fun p => by
    unfold gbmDigitalSplitFine gbmDigitalSplitCoarse
    rw [hd, ← sub_div, ← Finset.sum_sub_distrib]
  simp only [hsplit]
  refine (integral_sq_split_le hdm hdb hM).trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
  · -- the conditional mean of a sub-sample term is the conditional expectation
    refine integral_congr_ae ?_
    filter_upwards [ae_gbm_milsteinPath_ne_zero r σ hs₀ hσ hh (2 ^ (ℓ + 1) - 1),
      measurePreserving_pairAvg.quasiMeasurePreserving.ae (ae_gbm_milsteinPath_ne_zero r σ hs₀
        hσ (by positivity : (0 : ℝ) < T / 2 ^ ℓ) (2 ^ ℓ - 1))] with z hX hY
    have hf : ∀ w, emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1))
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z (2 ^ (ℓ + 1) - 1))
        (Real.sqrt (T / 2 ^ (ℓ + 1)) * w) = gbmCondMeanFine r σ T s₀ (ℓ + 1) z +
          σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z
            (2 ^ (ℓ + 1) - 1) * Real.sqrt (T / 2 ^ (ℓ + 1)) * w := fun w => by
      unfold emStep gbmCondMeanFine
      ring
    have hc : ∀ w, emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1))
        (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2) +
          Real.sqrt (T / 2 ^ (ℓ + 1)) * w) = gbmCondMeanCoarse r σ T s₀ ℓ z +
          σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z)
            (2 ^ ℓ - 1) * Real.sqrt (T / 2 ^ (ℓ + 1)) * w := fun w => by
      unfold emStep gbmCondMeanCoarse
      ring
    have hsf : σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z
        (2 ^ (ℓ + 1) - 1) * Real.sqrt (T / 2 ^ (ℓ + 1)) ≠ 0 := mul_ne_zero hX hsh.ne'
    have hsc : σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z)
        (2 ^ ℓ - 1) * Real.sqrt (T / 2 ^ (ℓ + 1)) ≠ 0 := mul_ne_zero hY hsh.ne'
    have hif : Integrable (fun w => (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (gbmCondMeanFine r σ T s₀ (ℓ + 1) z + σ * milsteinPath (fun S => r * S) (fun S => σ * S)
          (T / 2 ^ (ℓ + 1)) s₀ z (2 ^ (ℓ + 1) - 1) * Real.sqrt (T / 2 ^ (ℓ + 1)) * w))
        (gaussianReal 0 1) := integrable_digital (by fun_prop) K
    have hic : Integrable (fun w => (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (gbmCondMeanCoarse r σ T s₀ ℓ z + σ * milsteinPath (fun S => r * S) (fun S => σ * S)
          (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) * Real.sqrt (T / 2 ^ (ℓ + 1)) * w))
        (gaussianReal 0 1) := integrable_digital (by fun_prop) K
    rw [hd]
    dsimp only
    simp only [hf, hc]
    rw [integral_sub hif hic, integral_digital_gaussian hsf, integral_digital_gaussian hsc,
      abs_mul (σ * _) (Real.sqrt _), abs_mul (σ * _) (Real.sqrt _), abs_of_pos hsh]
    rfl
  · -- the conditional second moment has mean `P(D ≠ 0)`
    have hk : ∀ (z : ℕ → ℝ) (w : ℝ), d (Function.update z (2 ^ (ℓ + 1) - 1) w)
        (Function.update z (2 ^ (ℓ + 1) - 1) w (2 ^ (ℓ + 1) - 1)) = d z w := fun z w => by
      have h1 : milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀
          (Function.update z (2 ^ (ℓ + 1) - 1) w) (2 ^ (ℓ + 1) - 1) =
          milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z
            (2 ^ (ℓ + 1) - 1) :=
        milsteinPath_eq_of_eq_lt _ _ _ _ fun i hi => Function.update_of_ne (by omega) _ _
      have h2 : milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀
          (pairAvg (Function.update z (2 ^ (ℓ + 1) - 1) w)) (2 ^ ℓ - 1) =
          milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z)
            (2 ^ ℓ - 1) := by
        refine milsteinPath_eq_of_eq_lt _ _ _ _ fun i hi => ?_
        have := two_pow_succ_sub_one_eq ℓ
        rw [pairAvg, pairAvg, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have h3 : Function.update z (2 ^ (ℓ + 1) - 1) w (2 ^ (ℓ + 1) - 2) =
          z (2 ^ (ℓ + 1) - 2) := by
        have := Nat.one_le_two_pow (n := ℓ + 1)
        have : 2 ≤ 2 ^ (ℓ + 1) := by
          rw [pow_succ]
          have := Nat.one_le_two_pow (n := ℓ)
          omega
        exact Function.update_of_ne (by omega) _ _
      rw [hd]
      dsimp only
      rw [h1, h2, h3, Function.update_self]
    have hGm : Measurable fun z : ℕ → ℝ => d z (z (2 ^ (ℓ + 1) - 1)) ^ 2 :=
      (hdm.comp (measurable_id.prodMk (measurable_pi_apply _))).pow_const 2
    have e1 : ∫ p, d p.1 (p.2 0) ^ 2 ∂(stdNormalSeq.prod stdNormalSeq) =
        ∫ z, d z (z (2 ^ (ℓ + 1) - 1)) ^ 2 ∂stdNormalSeq := by
      rw [← integral_comp_of_measurePreserving (measurePreserving_update_prod (2 ^ (ℓ + 1) - 1) 0)
        hGm.aestronglyMeasurable]
      congr 1
      funext p
      rw [hk]
    have e2 : ∀ z : ℕ → ℝ, d z (z (2 ^ (ℓ + 1) - 1)) =
        (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ (ℓ + 1) z) -
          (Set.Ioi K).indicator 1 (gbmMilEM r σ T s₀ ℓ (pairAvg z)) := fun z => by
      rw [hd, gbmMilEM_pairAvg]
      rfl
    rw [e1]
    simp only [e2]
    rw [integral_sq_digital_sub (measurable_gbmMilEM r σ T s₀ (ℓ + 1))
      (show Measurable fun z => gbmMilEM r σ T s₀ ℓ (pairAvg z) from
        (measurable_gbmMilEM r σ T s₀ ℓ).comp measurable_pairAvg) K]

/-- **The fine and the coarse path end on different sides of the strike for an `O(h^q)` fraction of
the paths, `q < 1`** (Giles 2015, §5.2, p. 35, l. 1529–1531: "`P_ℓ − P_{ℓ−1} = O(1)` for an
`O(h_ℓ)` fraction of the paths", for the paths with an Euler–Maruyama last step).  For `s₀ ≠ 0`,
`σ ≠ 0`, `T > 0`, any `K` and `q < 1` there is `C` with
`P(H(Ŝ^f_N − K) ≠ H(Ŝ^c_N − K)) ≤ C h_{ℓ+1}^q` on every level `ℓ + 1`, where the coarse path at
maturity is the level-`ℓ` path driven by `pairAvg` (`gbmMilEM_pairAvg`): each of them is on the
side of `S_T` but for `O(h^q)` (`gbm_milEM_mismatch_rate`, `digital_ne_subset_union`). -/
lemma gbm_split_mismatch_rate (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (K : ℝ) {q : ℝ} (hq : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmMilEM r σ T s₀ ℓ (pairAvg z))} ≤
        C * (T / 2 ^ (ℓ + 1)) ^ q := by
  obtain ⟨C, hC, hmis⟩ := gbm_milEM_mismatch_rate r σ hs₀ hσ hT K hq
  refine ⟨C * (1 + (2 : ℝ) ^ q), by positivity, fun ℓ => ?_⟩
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have hS : MeasurableSet {w | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ w) ≠
      (Set.Ioi K).indicator 1 (gbmMilEM r σ T s₀ ℓ w)} :=
    (measurableSet_eq_fun (measurable_digital (measurable_gbmExact r σ T s₀ ℓ) K)
      (measurable_digital (measurable_gbmMilEM r σ T s₀ ℓ) K)).compl
  have hpre : {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ (ℓ + 1) z) ≠
      (Set.Ioi K).indicator 1 (gbmMilEM r σ T s₀ ℓ (pairAvg z))} =
      pairAvg ⁻¹' {w | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ w) ≠
        (Set.Ioi K).indicator 1 (gbmMilEM r σ T s₀ ℓ w)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, gbmExact_pairAvg]
  have h2 : stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (gbmExact r σ T s₀ (ℓ + 1) z) ≠ (Set.Ioi K).indicator 1 (gbmMilEM r σ T s₀ ℓ (pairAvg z))} ≤
      C * (2 : ℝ) ^ q * (T / 2 ^ (ℓ + 1)) ^ q := by
    rw [hpre, measurePreserving_pairAvg.measureReal_preimage hS.nullMeasurableSet]
    refine (hmis ℓ).trans (le_of_eq ?_)
    rw [div_two_pow_eq_two_mul T ℓ, Real.mul_rpow (by norm_num) hh.le]
    ring
  calc _ ≤ stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (gbmExact r σ T s₀ (ℓ + 1) z) ≠ (Set.Ioi K).indicator 1 (gbmMilEM r σ T s₀ (ℓ + 1) z)} +
        stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ)
          (gbmExact r σ T s₀ (ℓ + 1) z) ≠
            (Set.Ioi K).indicator 1 (gbmMilEM r σ T s₀ ℓ (pairAvg z))} :=
        (measureReal_mono (digital_ne_subset_union _ _ _ K)).trans (measureReal_union_le _ _)
    _ ≤ C * (T / 2 ^ (ℓ + 1)) ^ q + C * (2 : ℝ) ^ q * (T / 2 ^ (ℓ + 1)) ^ q :=
        add_le_add (hmis (ℓ + 1)) h2
    _ = _ := by ring

/-- The splitting payoffs take values in `[0, 1]`: averages of `M ≥ 1` digital payoffs (Giles 2015,
§5.2, p. 36, l. 1594–1598: "an average payoff"). -/
lemma sum_indicator_div_mem_Icc {M : ℕ} (hM : 0 < M) (K : ℝ) (f : ℕ → ℝ) :
    0 ≤ (∑ i ∈ range M, (Set.Ioi K).indicator (1 : ℝ → ℝ) (f i)) / M ∧
      (∑ i ∈ range M, (Set.Ioi K).indicator (1 : ℝ → ℝ) (f i)) / M ≤ 1 := by
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have h01 : ∀ i, 0 ≤ (Set.Ioi K).indicator (1 : ℝ → ℝ) (f i) ∧
      (Set.Ioi K).indicator (1 : ℝ → ℝ) (f i) ≤ 1 := fun i => by
    rcases digital_eq_zero_or_one K (f i) with h | h <;> rw [h] <;> norm_num
  refine ⟨div_nonneg (Finset.sum_nonneg fun i _ => (h01 i).1) hM'.le, ?_⟩
  rw [div_le_one hM']
  calc ∑ i ∈ range M, (Set.Ioi K).indicator (1 : ℝ → ℝ) (f i) ≤ ∑ _i ∈ range M, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => (h01 i).2
    _ = M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- The splitting correction `P^{f,M}_{ℓ+1} − P^{c,M}_ℓ` is measurable and takes values in
`[−1, 1]`, so it is square integrable (Giles 2015, §5.2, p. 36, l. 1591–1598). -/
lemma memLp_gbmDigitalSplit_sub (r σ T s₀ K : ℝ) (ℓ : ℕ) {M : ℕ} (hM : 0 < M) :
    MemLp (fun p => gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
      gbmDigitalSplitCoarse r σ T s₀ K M ℓ p) 2 (stdNormalSeq.prod stdNormalSeq) := by
  have hind : Measurable ((Set.Ioi K).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Ioi
  have hXm : Measurable fun z : ℕ → ℝ => milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ (ℓ + 1)) s₀ z (2 ^ (ℓ + 1) - 1) :=
    measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _
  have hYm : Measurable fun z : ℕ → ℝ => milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) :=
    (measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _).comp measurable_pairAvg
  have hXp : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => milsteinPath (fun S => r * S)
      (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ p.1 (2 ^ (ℓ + 1) - 1) := hXm.comp measurable_fst
  have hYp : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => milsteinPath (fun S => r * S)
      (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg p.1) (2 ^ ℓ - 1) := hYm.comp measurable_fst
  have hzp : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 (2 ^ (ℓ + 1) - 2) :=
    (measurable_pi_apply _).comp measurable_fst
  have hFm : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p := by
    unfold gbmDigitalSplitFine
    refine (Finset.measurable_sum _ fun i _ => hind.comp ?_).div_const _
    have hy : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    unfold emStep
    fun_prop
  have hCm : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      gbmDigitalSplitCoarse r σ T s₀ K M ℓ p := by
    unfold gbmDigitalSplitCoarse
    refine (Finset.measurable_sum _ fun i _ => hind.comp ?_).div_const _
    have hy : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    unfold emStep
    fun_prop
  refine memLp_of_bounded (a := -1) (b := 1)
    (f := fun p => gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
      gbmDigitalSplitCoarse r σ T s₀ K M ℓ p)
    (Eventually.of_forall fun p => ?_) (hFm.sub hCm).aestronglyMeasurable 2
  obtain ⟨h1, h2⟩ := sum_indicator_div_mem_Icc hM K (fun i => emStep (fun S => r * S)
    (fun S => σ * S) (T / 2 ^ (ℓ + 1)) (milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ (ℓ + 1)) s₀ p.1 (2 ^ (ℓ + 1) - 1)) (Real.sqrt (T / 2 ^ (ℓ + 1)) * p.2 i))
  obtain ⟨h3, h4⟩ := sum_indicator_div_mem_Icc hM K (fun i => emStep (fun S => r * S)
    (fun S => σ * S) (T / 2 ^ ℓ) (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀
      (pairAvg p.1) (2 ^ ℓ - 1)) (Real.sqrt (T / 2 ^ (ℓ + 1)) * p.1 (2 ^ (ℓ + 1) - 2) +
        Real.sqrt (T / 2 ^ (ℓ + 1)) * p.2 i))
  unfold gbmDigitalSplitFine gbmDigitalSplitCoarse
  exact ⟨by linarith, by linarith⟩

/-- **The variance of the splitting estimator** (Giles 2015, §5.2, p. 36, l. 1591–1600: "In this
case, one can use the technique of "splitting" … for each set of Brownian increments up to one fine
timestep before the end, one uses a number of samples of the final Brownian increment to produce an
average payoff. If the number of sub-samples is chosen appropriately, the variance is the same, to
leading order, without any increase in the computational cost, again to leading order").  For GBM
with `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, a strike `K ≠ 0` and every `q < 3/2` there is `C ≥ 0` such that
for every level `ℓ + 1` (`h = h_{ℓ+1} = T 2^{−(ℓ+1)}`) and every number `M ≥ 1` of sub-samples
(independent of the main increments, `stdNormalSeq.prod stdNormalSeq`) the splitting correction
`P^{f,M}_{ℓ+1} − P^{c,M}_ℓ` (`gbmDigitalSplitFine`, `gbmDigitalSplitCoarse`) is square integrable,
`E[(P^{f,M}_{ℓ+1} − P^{c,M}_ℓ)²] ≤ C (h^q + h^{q − 1/2}/M)`, and so is its variance.  The first term
is the conditional-expectation estimator (`gbm_digital_condExp_variance_rate`); the second is the
mean conditional variance of one sub-sample term, at most the fraction `O(h^{q−1/2})`
(`q − 1/2 < 1`) of the paths whose fine and coarse payoffs differ (`gbm_split_mismatch_rate`),
divided by `M` (`gbm_split_sq_le`).

**Deviation.**  The exponents carry the loss of `gbm_digital_condExp_variance_rate` (the paper's
"to leading order" is not an asymptotic equivalence here, but the same rate `O(h^{3/2−η})` once
`M ≥ h^{−1/2}`, `gbm_digital_split_sqrt_rate`). -/
theorem gbm_digital_split_variance_rate (r σ : ℝ) {s₀ T K : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (hK : K ≠ 0) {q : ℝ} (hq : q < 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ M : ℕ), 0 < M →
      MemLp (fun p => gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
        gbmDigitalSplitCoarse r σ T s₀ K M ℓ p) 2 (stdNormalSeq.prod stdNormalSeq) ∧
      ∫ p, (gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
          gbmDigitalSplitCoarse r σ T s₀ K M ℓ p) ^ 2 ∂(stdNormalSeq.prod stdNormalSeq) ≤
        C * ((T / 2 ^ (ℓ + 1)) ^ q + (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / M) ∧
      variance (fun p => gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
          gbmDigitalSplitCoarse r σ T s₀ K M ℓ p) (stdNormalSeq.prod stdNormalSeq) ≤
        C * ((T / 2 ^ (ℓ + 1)) ^ q + (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / M) := by
  obtain ⟨C₁, hC₁, hv⟩ := gbm_digital_condExp_variance_rate r σ hs₀ hσ hT hK hq
  obtain ⟨C₂, hC₂, hm⟩ := gbm_split_mismatch_rate r σ hs₀ hσ hT K (q := q - 1 / 2)
    (by linarith)
  refine ⟨C₁ + C₂, by positivity, fun ℓ M hM => ?_⟩
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have hL := memLp_gbmDigitalSplit_sub r σ T s₀ K ℓ hM
  have key : ∫ p, (gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
      gbmDigitalSplitCoarse r σ T s₀ K M ℓ p) ^ 2 ∂(stdNormalSeq.prod stdNormalSeq) ≤
      (C₁ + C₂) * ((T / 2 ^ (ℓ + 1)) ^ q + (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / M) := by
    refine (gbm_split_sq_le r σ hs₀ hσ hT K ℓ hM).trans ?_
    have h1 := (hv ℓ).2.1
    have h2 : stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (gbmMilEM r σ T s₀ (ℓ + 1) z) ≠ (Set.Ioi K).indicator 1
          (gbmMilEM r σ T s₀ ℓ (pairAvg z))} / M ≤
        C₂ * ((T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / M) := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (hm ℓ) hM'.le
    have h3 : 0 ≤ (T / 2 ^ (ℓ + 1)) ^ q := by positivity
    have h4 : 0 ≤ (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / M := by positivity
    nlinarith
  refine ⟨hL, key, ?_⟩
  exact (variance_le_expectation_sq hL.aestronglyMeasurable).trans key

/-- **`M_ℓ ≍ h_ℓ^{−1/2}` sub-samples keep the variance `O(h^q)`, `q < 3/2`, at an extra cost
`o(h_ℓ^{−1})`** (Giles 2015, §5.2, p. 36, l. 1597–1600: "If the number of sub-samples is chosen
appropriately, the variance is the same, to leading order, without any increase in the
computational cost, again to leading order").  For GBM with `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, `K ≠ 0` and
every `q < 3/2` there is `C ≥ 0` such that on every level `ℓ + 1` (`h = T 2^{−(ℓ+1)}`) the number
of sub-samples `M = ⌈h^{−1/2}⌉ ≥ 1` costs `M ≤ h^{−1/2} + 1`, i.e. `M h ≤ √h + h → 0` relative to
the cost `2^{ℓ+1} = T/h` of the path (an extra cost `o(h^{−1})`), and the splitting correction with
`M` sub-samples is square integrable with `E[(P^{f,M}_{ℓ+1} − P^{c,M}_ℓ)²] ≤ C h^q` and variance
`≤ C h^q`, the rate of the conditional-expectation estimator (`gbm_digital_split_variance_rate`
with `h^{q−1/2}/M ≤ h^q`).  **Deviation.**  This is the same rate, not the same variance to leading
order: with `M = ⌈h^{−1/2}⌉` the excess `P(D ≠ 0)/M` is of the same order as the
conditional-expectation variance (numerically the ratio of the two variances stays near 15 on
levels 4–7 for `r = 0.05`, `σ = 0.2`, `s₀ = K = T = 1`).  Equal variance to leading order needs
`M h^{1/2} → ∞` (e.g. `M ≍ h^{−3/4}`, still an extra cost `o(h^{−1})`), and lower bounds that are
not proved here. -/
theorem gbm_digital_split_sqrt_rate (r σ : ℝ) {s₀ T K : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (hK : K ≠ 0) {q : ℝ} (hq : q < 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      0 < ⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ ∧
      (⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ : ℝ) * (T / 2 ^ (ℓ + 1)) ≤
        Real.sqrt (T / 2 ^ (ℓ + 1)) + T / 2 ^ (ℓ + 1) ∧
      MemLp (fun p => gbmDigitalSplitFine r σ T s₀ K
          ⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ (ℓ + 1) p -
          gbmDigitalSplitCoarse r σ T s₀ K ⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ ℓ p) 2
          (stdNormalSeq.prod stdNormalSeq) ∧
      ∫ p, (gbmDigitalSplitFine r σ T s₀ K ⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ (ℓ + 1) p -
          gbmDigitalSplitCoarse r σ T s₀ K ⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ ℓ p) ^ 2
          ∂(stdNormalSeq.prod stdNormalSeq) ≤ C * (T / 2 ^ (ℓ + 1)) ^ q ∧
      variance (fun p => gbmDigitalSplitFine r σ T s₀ K
          ⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ (ℓ + 1) p -
          gbmDigitalSplitCoarse r σ T s₀ K ⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ ℓ p)
          (stdNormalSeq.prod stdNormalSeq) ≤ C * (T / 2 ^ (ℓ + 1)) ^ q := by
  obtain ⟨C, hC, hb⟩ := gbm_digital_split_variance_rate r σ hs₀ hσ hT hK hq
  refine ⟨2 * C, by positivity, fun ℓ => ?_⟩
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have hx : 0 < (T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hh _
  have hM : 0 < ⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ := Nat.ceil_pos.2 hx
  have hMx : (T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ)) ≤
      (⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ : ℝ) := Nat.le_ceil _
  have hMx' : (⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ : ℝ) <
      (T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ)) + 1 := Nat.ceil_lt_add_one hx.le
  have hxh : (T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ)) * (T / 2 ^ (ℓ + 1)) =
      Real.sqrt (T / 2 ^ (ℓ + 1)) := by
    rw [Real.sqrt_eq_rpow]
    nth_rewrite 2 [← Real.rpow_one (T / 2 ^ (ℓ + 1))]
    rw [← Real.rpow_add hh]
    norm_num
  have hcost : (⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ : ℝ) * (T / 2 ^ (ℓ + 1)) ≤
      Real.sqrt (T / 2 ^ (ℓ + 1)) + T / 2 ^ (ℓ + 1) := by
    calc (⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ : ℝ) * (T / 2 ^ (ℓ + 1))
        ≤ ((T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ)) + 1) * (T / 2 ^ (ℓ + 1)) :=
          mul_le_mul_of_nonneg_right hMx'.le hh.le
      _ = _ := by rw [add_mul, hxh, one_mul]
  obtain ⟨hL, hI, hV⟩ := hb ℓ _ hM
  have hsmall : (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) /
      (⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ : ℝ) ≤ (T / 2 ^ (ℓ + 1)) ^ q := by
    calc (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / (⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ : ℝ)
        ≤ (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / (T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) hx hMx
      _ = (T / 2 ^ (ℓ + 1)) ^ q := by
          rw [← Real.rpow_sub hh]
          norm_num
  have hfin : C * ((T / 2 ^ (ℓ + 1)) ^ q + (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) /
      (⌈(T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ))⌉₊ : ℝ)) ≤ 2 * C * (T / 2 ^ (ℓ + 1)) ^ q := by
    have := mul_le_mul_of_nonneg_left hsmall hC
    nlinarith
  exact ⟨hM, hcost, hL, hI.trans hfin, hV.trans hfin⟩

/-- **(2.4) for the splitting estimator** (Giles 2015, §5.2, p. 36, l. 1584–1600: "`E[P^c_{ℓ−1}] =
E[P^f_{ℓ−1}]` … This ensures that the identity in Equation (2.4) is respected", for the splitting
payoffs of l. 1591–1598).  For every `M ≥ 1` the fine splitting payoff of level `ℓ` and the coarse
splitting payoff used on level `ℓ + 1` both have the mean `P(Ŝ^f_N > K)` of the digital payoff of
the level-`ℓ` path with an Euler–Maruyama last step (`gbmMilEM`): a sub-sample term is the payoff of
a path whose last increment has been replaced by an independent normal
(`measurePreserving_update_prod`), and the coarse path at maturity is the level-`ℓ` path driven by
`pairAvg` (`gbmMilEM_pairAvg`, `measurePreserving_pairAvg`). -/
lemma gbmDigitalSplit_integral_eq (r σ T s₀ K : ℝ) (ℓ : ℕ) {M : ℕ} (hM : 0 < M) :
    ∫ p, gbmDigitalSplitFine r σ T s₀ K M ℓ p ∂(stdNormalSeq.prod stdNormalSeq) =
      ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z) ∂stdNormalSeq ∧
    ∫ p, gbmDigitalSplitCoarse r σ T s₀ K M ℓ p ∂(stdNormalSeq.prod stdNormalSeq) =
      ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z) ∂stdNormalSeq := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hind : Measurable ((Set.Ioi K).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Ioi
  have hG : Measurable fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z) :=
    hind.comp (measurable_gbmMilEM r σ T s₀ ℓ)
  have hGi : Integrable (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z))
      stdNormalSeq := integrable_digital (measurable_gbmMilEM r σ T s₀ ℓ) K
  have hGc : Measurable fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (gbmMilEM r σ T s₀ ℓ (pairAvg z)) := hG.comp measurable_pairAvg
  have hGci : Integrable (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (gbmMilEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq :=
    integrable_digital ((measurable_gbmMilEM r σ T s₀ ℓ).comp measurable_pairAvg) K
  have hEc : ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ (pairAvg z))
      ∂stdNormalSeq = ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z)
      ∂stdNormalSeq :=
    integral_comp_of_measurePreserving measurePreserving_pairAvg hG.aestronglyMeasurable
  -- a fine sub-sample term is the payoff of the path with the last increment replaced
  have hf : ∀ i, (fun p : (ℕ → ℝ) × (ℕ → ℝ) => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ p.1 (2 ^ ℓ - 1))
        (Real.sqrt (T / 2 ^ ℓ) * p.2 i))) = fun p => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (gbmMilEM r σ T s₀ ℓ (Function.update p.1 (2 ^ ℓ - 1) (p.2 i))) := fun i => by
    funext p
    have hpath : milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀
        (Function.update p.1 (2 ^ ℓ - 1) (p.2 i)) (2 ^ ℓ - 1) =
        milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ p.1 (2 ^ ℓ - 1) :=
      milsteinPath_eq_of_eq_lt _ _ _ _ fun j hj => Function.update_of_ne (by omega) _ _
    unfold gbmMilEM
    rw [hpath, Function.update_self]
  -- a coarse sub-sample term likewise, with the level-`ℓ` path driven by `pairAvg`
  have hc : ∀ i, (fun p : (ℕ → ℝ) × (ℕ → ℝ) => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg p.1) (2 ^ ℓ - 1))
        (Real.sqrt (T / 2 ^ (ℓ + 1)) * p.1 (2 ^ (ℓ + 1) - 2) +
          Real.sqrt (T / 2 ^ (ℓ + 1)) * p.2 i))) = fun p => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (gbmMilEM r σ T s₀ ℓ (pairAvg (Function.update p.1 (2 ^ (ℓ + 1) - 1) (p.2 i)))) :=
    fun i => by
    funext p
    have hk := two_pow_succ_sub_one_eq ℓ
    have hk2 := two_pow_succ_sub_two_eq ℓ
    have hpath : milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀
        (pairAvg (Function.update p.1 (2 ^ (ℓ + 1) - 1) (p.2 i))) (2 ^ ℓ - 1) =
        milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg p.1)
          (2 ^ ℓ - 1) := by
      refine milsteinPath_eq_of_eq_lt _ _ _ _ fun j hj => ?_
      rw [pairAvg, pairAvg, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    rw [gbmMilEM_pairAvg, hpath, Function.update_self, Function.update_of_ne (by omega)]
  have hif : ∀ i, Integrable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ p.1 (2 ^ ℓ - 1))
        (Real.sqrt (T / 2 ^ ℓ) * p.2 i))) (stdNormalSeq.prod stdNormalSeq) := fun i => by
    rw [hf i]
    exact ((measurePreserving_update_prod (2 ^ ℓ - 1) i).integrable_comp
      hGi.aestronglyMeasurable).2 hGi
  have hic : ∀ i, Integrable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg p.1) (2 ^ ℓ - 1))
        (Real.sqrt (T / 2 ^ (ℓ + 1)) * p.1 (2 ^ (ℓ + 1) - 2) +
          Real.sqrt (T / 2 ^ (ℓ + 1)) * p.2 i))) (stdNormalSeq.prod stdNormalSeq) := fun i => by
    rw [hc i]
    exact ((measurePreserving_update_prod (2 ^ (ℓ + 1) - 1) i).integrable_comp
      hGci.aestronglyMeasurable).2 hGci
  have hIf : ∀ i, ∫ p, (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ p.1 (2 ^ ℓ - 1))
        (Real.sqrt (T / 2 ^ ℓ) * p.2 i)) ∂(stdNormalSeq.prod stdNormalSeq) =
      ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z) ∂stdNormalSeq := fun i => by
    rw [hf i]
    exact integral_comp_of_measurePreserving (measurePreserving_update_prod (2 ^ ℓ - 1) i)
      hGi.aestronglyMeasurable
  have hIc : ∀ i, ∫ p, (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ)
        (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg p.1) (2 ^ ℓ - 1))
        (Real.sqrt (T / 2 ^ (ℓ + 1)) * p.1 (2 ^ (ℓ + 1) - 2) +
          Real.sqrt (T / 2 ^ (ℓ + 1)) * p.2 i)) ∂(stdNormalSeq.prod stdNormalSeq) =
      ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s₀ ℓ z) ∂stdNormalSeq := fun i => by
    rw [hc i, ← hEc]
    exact integral_comp_of_measurePreserving (measurePreserving_update_prod (2 ^ (ℓ + 1) - 1) i)
      hGci.aestronglyMeasurable
  constructor
  · unfold gbmDigitalSplitFine
    rw [integral_div, integral_finsetSum _ fun i _ => hif i, Finset.sum_congr rfl fun i _ => hIf i,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hM']
  · unfold gbmDigitalSplitCoarse
    rw [integral_div, integral_finsetSum _ fun i _ => hic i, Finset.sum_congr rfl fun i _ => hIc i,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hM']

end MLMC
