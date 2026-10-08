import MlmcLean.LevyTruncation
import MlmcLean.JumpProcesses
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Lévy processes: Brownian small jumps and Variance-Gamma Asian options (Giles 2015, §6.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §6.2 "More
general processes", pp. 47–48 (`docs/giles2015.txt`; coverage rows G6-06 and G6-07, l. 2038–2051,
and G6-09, l. 2056–2070).  This module continues `LevyTruncation.lean` (the truncated levels with
the small jumps neglected) and `JumpProcesses.lean` (Theorem 1 for the trapezoidal Asian option of
an exponential Lévy model with exactly simulated increments, `levy_asian_theorem1`).

## 1. The small jumps replaced by a Brownian term (G6-06, G6-07)

l. 2038–2041: "One approach is to simulate the large jumps and either neglect the small jumps or
approximate their effect by adding a Brownian diffusion term (Dereich 2011, Dereich and Heidenreich
2011, Marxen 2010)"; l. 2046–2048: "The ones which are smaller than `δ_ℓ` are either neglected for
both paths, or approximated by the same Brownian increment."

**Setting.**  As in `LevyTruncation.lean`: the terminal value `X_T` of a pure-jump Lévy process with
Lévy measure `ν` (`∫ min(1, z²) dν < ∞`) and the truncation `1_{|z|<1}`; `levyFine ν T δ` sums the
simulated jumps `|z| ≥ δ` of a compound Poisson input and subtracts their compensator.  The
neglected small jumps `|z| < δ` form a centred variable of variance `σ_δ² = T ∫_{|z|<δ} z² dν`
(`levySmallStd ν T δ = σ_δ`).  The corrected level-`δ` value is
`levyGaussFine ν T δ ((N, Z), W) = levyFine ν T δ (N, Z) + σ_δ W` with a standard normal `W`
independent of the jumps (input law `cpInputLaw r μ ⊗ N(0, 1)`); the fine and the coarse value of
level `ℓ` use the same `W`, scaled as `σ_{δ_ℓ} W` and `σ_{δ_{ℓ−1}} W`.
* `levyGauss_coarse_map_eq`, `levyGauss_2_4`: the coarse value has the law of the corrected
  level-`(ℓ − 1)` value simulated on its own, hence (2.4).
* `levyGauss_correction_moments`: `ΔX = X̂^{δ_ℓ} − X̂^{δ_{ℓ−1}}` is in `L²`, has mean `0` and
  `E[ΔX²] = T ∫_{δ_ℓ≤|z|<δ_{ℓ−1}} z² dν + (σ_{δ_{ℓ−1}} − σ_{δ_ℓ})² ≤ 2T ∫_{δ_ℓ≤|z|<δ_{ℓ−1}} z² dν`
  (since `(σ' − σ)² ≤ σ'² − σ²` for `0 ≤ σ ≤ σ'`).
* `levyGauss_correction_variance_le`: `V_ℓ ≤ 2 K² T ∫_{δ_ℓ≤|z|<δ_{ℓ−1}} z² dν` for a `K`-Lipschitz
  payoff.
* All levels on one space (`bandInputLaw Λ M ⊗ N(0, 1)`, `bandGaussApprox`): `bandGauss_sq_sub`
  (the same identity and bound between any two levels) and `levyGauss_limit`: the `L²` limit `X` of
  the truncated levels (as in `levy_truncation_limit`, `E[(X − X^{δ_ℓ})²] = T ∫_{|z|<δ_ℓ} z² dν`)
  satisfies `E[(X − X̂^{δ_ℓ})²] = 2T ∫_{|z|<δ_ℓ} z² dν → 0`, the same rate, and
  `|E[Φ(X̂^{δ_ℓ}) − Φ(X)]| ≤ K (2T ∫_{|z|<δ_ℓ} z² dν)^{1/2}` for `K`-Lipschitz payoffs.
* `levyGauss_expected_cost`, `levyGauss_theorem1`: Theorem 1 for the corrected levels with
  `δ_ℓ = 2^{−ℓ}` under the rates assumed in `levy_truncation_theorem1`: `α = (2 − Y)/2`,
  `β = 2 − Y`, `γ = Y`, expected cost `∑_ℓ N_ℓ (1 + T ν(|z| ≥ δ_ℓ))`.
  `levyGauss_stableLike_theorem1`: the same, end to end, for the one-sided stable-like example
  `ν(dz) = c z^{−1−Y} dz` on `(0, 1]` of `levy_stableLike_theorem1`.

## 2. Table 6.3, the Asian row, for Variance-Gamma laws (G6-09)

l. 2056–2057: "VG NIG α-stable / Asian O(h²) O(h²) O(h²)"; l. 2063–2064: "directly simulate the
increments of the Lévy process over a set of uniform timesteps (Schoutens 2003)".

**Gamma laws.**  Mathlib has the Gamma law `gammaMeasure a r` (shape `a`, rate `r`) but no
convolution identity.  `measure_eq_of_integral_exp_eq`: two probability laws on `ℝ` with the same
finite exponential moments `∫ e^{tx}` for `|t| < s` coincide (their complex moment generating
functions are analytic on the strip `|Re z| < s` and agree on the real segment, and on the imaginary
axis they are the characteristic functions).  `integral_exp_mul_gammaMeasure`:
`∫ e^{tx} dΓ(a, r) = (r/(r − t))^a` for `t < r`; hence `gammaMeasure_conv`:
`Γ(a, r) ∗ Γ(b, r) = Γ(a + b, r)`.

**Variance-Gamma.**  Two constructions of the VG increment over a step `h > 0`, with a drift `b`:
* `vgLaw b C G M h = δ_{bh} ∗ Γ(Ch, M) ∗ (−Γ(Ch, G))`, a difference of independent Gamma variables
  (Lévy density `C e^{−Mz}/z` on `z > 0` and `C e^{−G|z|}/|z|` on `z < 0`, the CGMY
  parametrisation with `Y = 0`).  `vgLaw_conv`: `vgLaw h₁ ∗ vgLaw h₂ = vgLaw (h₁ + h₂)`;
  `integral_exp_mul_vgLaw`: `∫ e^{θx} dvgLaw = e^{θbh} (M/(M − θ))^{Ch} (G/(G + θ))^{Ch}` (finite)
  for `−G < θ < M`; `vg_asian_variance_le`: `V_ℓ ≤ c h_ℓ²` for the Asian option when `M > 2`;
  `vg_asian_theorem1`: Theorem 1 for the Asian option when `M > 2`.
* `vgSubLaw b θ σ κ h`: the law of `bh + θΓ + σ√Γ Z`, `Γ ∼ Gamma(h/κ, rate 1/κ)` (mean `h`, variance
  `κh`) independent of `Z ∼ N(0, 1)`: a Brownian motion with drift `θ` and volatility `σ` run with a
  Gamma clock (Madan, Carr and Chang 1998).  `integral_exp_mul_vgSubLaw`:
  `∫ e^{ux} dvgSubLaw = e^{ubh} (1 − κ(uθ + σ²u²/2))^{−h/κ}` when `uθ + σ²u²/2 < 1/κ`;
  `vgSubLaw_conv`; `vgSubLaw_eq_vgLaw`: if `M⁻¹ − G⁻¹ = θκ` and `(MG)⁻¹ = σ²κ/2` (for `σ ≠ 0`:
  `M⁻¹, G⁻¹ = (√(θ²κ² + 2σ²κ) ± θκ)/2`) then `vgSubLaw b θ σ κ h = vgLaw b κ⁻¹ G M h`;
  `vgSub_asian_variance_le`, `vgSub_asian_theorem1`: `V_ℓ ≤ c h_ℓ²` and Theorem 1 for the Asian
  option when `2θκ + 2σ²κ < 1`.

In both Asian theorems every hypothesis of `levy_asian_theorem1` is proved (the level laws
`ν_ℓ`, the increment laws over `h_ℓ = T 2^{−ℓ}`, satisfy `ν_{ℓ+1} ∗ ν_{ℓ+1} = ν_ℓ`, and
`∫ e^{2x} dν_0 < ∞`), so `V_ℓ = O(h_ℓ²)` (the Table 6.3 entry, `β = 2`; stated on its own in
`vg_asian_variance_le` and `vgSub_asian_variance_le` through `levy_asian_payoff_sq_le`),
`|E[P_ℓ] − P| ≤ c 2^{−ℓ}`, and the MLMC estimator reaches mean square error `< ε²` at cost
`O(ε⁻²)`, with no assumption left.

## Deviations
* Part 1 models the terminal value `X_T` only (payoffs `Φ(X_T)`), as `LevyTruncation.lean` does;
  the Brownian term is `σ_δ W` with one standard normal `W` (`W = B_T/√T` for a Brownian motion
  `B`), independent of the jumps, and `σ_δ²` is the variance of the neglected compensated small
  jumps (with the truncation `1_{|z|<1}` and `δ ≤ 1` they have mean `0`, so no drift arises).
  The intermediate range is the half-open `[δ_ℓ, δ_{ℓ−1})` of `LevyTruncation.lean`.
* The strong error doubles, `E[(X − X̂^δ)²] = 2T ∫_{|z|<δ} z² dν`, because `W` is independent of
  the true small jumps.  The bias depends only on the laws, and the bound used here, through this
  independent coupling, is not sharp: Dereich (2011) bounds the Wasserstein distance between the
  small-jump part and its Gaussian replacement (same mean and variance), which gives a smaller bias
  for Lipschitz payoffs and a better complexity when the Blumenthal–Getoor index exceeds 1; this is
  not proved here, and the paper (which only names the approach) states no rate for it.  Theorem 1
  is therefore proved with the same `α, β, γ` as with the small jumps neglected (constants up to a
  factor 2).  The cost of a sample is one plus the number of simulated jumps (the normal variate is
  part of the "one").
* Part 2 uses the trapezoidal Asian average `levyAsianTrap` of `JumpProcesses.lean` on the uniform
  grid (a discrete-time analogue of `T⁻¹ ∫₀ᵀ S_t dt`; the limit `P` of the level expectations is
  not identified with the continuous-time price) and needs a horizon `T > 0` (a Gamma law needs a
  positive shape: Mathlib's `gammaMeasure 0 r` is the zero measure).  The parameter conditions
  `M > 2`, resp. `2θκ + 2σ²κ < 1`, say exactly that `E e^{2X_T} < ∞`, which the `L²` bound of the
  Asian correction uses (`S_t² = s₀² e^{2X_t}` must be integrable).

## Not proved
The improved bias of the Gaussian correction (Dereich 2011: a quantitative central limit /
Wasserstein bound for the small jumps; a large development); paths and path-dependent payoffs for
part 1; the NIG column of Table 6.3 (Mathlib has no inverse Gaussian law, nor the integral
`∫₀^∞ x^{−3/2} e^{−a/x − bx} dx` behind its Laplace transform) and the spectrally negative
α-stable column (the stable laws in Mathlib are the Gaussian laws, `α = 2`, and the symmetric
Cauchy law `cauchyMeasure`, `α = 1`; there are no spectrally negative α-stable laws); the lookback
and barrier rows.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal ENNReal

namespace MLMC

/-! ### Part 1: the small jumps replaced by a Brownian term -/

/-- The standard deviation `σ_δ = (T ∫_{|z|<δ} z² dν)^{1/2}` of the neglected small jumps (Giles
2015, §6.2, p. 47, l. 2039–2041: "approximate their effect by adding a Brownian diffusion term"):
the compensated jumps of size `|z| < δ` over `[0, T]` have variance `T ∫_{|z|<δ} z² dν`, the
variance given to the Brownian term that replaces them. -/
noncomputable def levySmallStd (ν : Measure ℝ) (T : ℝ≥0) (δ : ℝ) : ℝ :=
  Real.sqrt (T * ∫ z in {z : ℝ | |z| < δ}, z ^ 2 ∂ν)

/-- **The level-`δ` value with the small jumps replaced by a Brownian term** (Giles 2015, §6.2,
p. 47, l. 2038–2041: "simulate the large jumps and … approximate their effect by adding a Brownian
diffusion term"): on the input `((N, Z), W)`, the level-`δ` value `levyFine ν T δ (N, Z)` (the
simulated jumps `|z| ≥ δ`, compensated) plus `σ_δ W`, where `W` is a standard normal variate and
`σ_δ = levySmallStd ν T δ`. -/
noncomputable def levyGaussFine (ν : Measure ℝ) (T : ℝ≥0) (δ : ℝ)
    (ω : (ℕ × (ℕ → ℝ)) × ℝ) : ℝ :=
  levyFine ν T δ ω.1 + levySmallStd ν T δ * ω.2

/-- The law of `f(ω₁) + g(ω₂)` under a product measure is the convolution of the laws of `f` and
`g` (Giles 2015, §6.2: the jumps and the independent Brownian term). -/
lemma map_prod_add_eq_conv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [SFinite P] [SFinite Q] {f : α → ℝ} {g : β → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    (P.prod Q).map (fun ω => f ω.1 + g ω.2) = P.map f ∗ Q.map g := by
  rw [Measure.conv, Measure.map_prod_map _ _ hf hg,
    Measure.map_map measurable_add (hf.prodMap hg)]
  rfl

/-- **The coarse value of the corrected level-`ℓ` simulation has the law of the corrected
level-`(ℓ − 1)` value** (Giles 2015, §6.2, p. 47, l. 2045–2048: "The ones which are larger than
`δ_{ℓ−1}` get simulated in both the fine and coarse paths.  The ones which are smaller than `δ_ℓ`
are either neglected for both paths, or approximated by the same Brownian increment"; this gives
(2.4), §2.1, p. 8).  The jumps `|z| ≥ δ` (`δ = δ_ℓ`) are simulated once, `N ∼ P(r)`, `Z_i ∼ μ` with
`r • μ = T • ν|_{|z| ≥ δ}`, together with a standard normal `W`; the coarse value
`levyGaussFine ν T δ'` (`δ' = δ_{ℓ−1} ≥ δ`) keeps the jumps `|Z_i| ≥ δ'` and adds `σ_{δ'} W`.  Its
law is that of the corrected level-`δ'` value computed from its own simulation `N' ∼ P(r')`,
`Z'_i ∼ μ'`, `r' • μ' = T • ν|_{|z| ≥ δ'}`, and its own normal variate. -/
theorem levyGauss_coarse_map_eq {ν : Measure ℝ} {T : ℝ≥0} {δ δ' : ℝ} (hδ : δ ≤ δ') {r r' : ℝ≥0}
    {μ μ' : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (h : r • μ = T • ν.restrict (levySet δ)) (h' : r' • μ' = T • ν.restrict (levySet δ')) :
    ((cpInputLaw r μ).prod (gaussianReal 0 1)).map (levyGaussFine ν T δ') =
      ((cpInputLaw r' μ').prod (gaussianReal 0 1)).map (levyGaussFine ν T δ') := by
  have := isProbabilityMeasure_cpInputLaw r μ
  have := isProbabilityMeasure_cpInputLaw r' μ'
  have e : levyGaussFine ν T δ' =
      fun ω => levyFine ν T δ' ω.1 + (fun z => levySmallStd ν T δ' * z) ω.2 := rfl
  rw [e, map_prod_add_eq_conv _ _ (measurable_levyFine ν T δ') (measurable_const_mul _),
    map_prod_add_eq_conv _ _ (measurable_levyFine ν T δ') (measurable_const_mul _),
    levy_coarse_map_eq hδ h h']

/-- **The identity (2.4) for the corrected truncated Lévy levels** (Giles 2015, §6.2, p. 47,
l. 2045–2048: the large jumps "get simulated in both the fine and coarse paths", the small ones are
"approximated by the same Brownian increment"; §2.1, p. 8, (2.4): `E[P^f_ℓ] = E[P^c_ℓ]`).  With the
hypotheses of `levyGauss_coarse_map_eq`, for every measurable payoff `Φ`, the expectation of `Φ` of
the coarse value of the corrected level-`ℓ` simulation equals the expectation of `Φ` of the fine
value of the corrected level-`(ℓ − 1)` simulation. -/
theorem levyGauss_2_4 {ν : Measure ℝ} {T : ℝ≥0} {δ δ' : ℝ} (hδ : δ ≤ δ') {r r' : ℝ≥0}
    {μ μ' : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (h : r • μ = T • ν.restrict (levySet δ)) (h' : r' • μ' = T • ν.restrict (levySet δ'))
    {Φ : ℝ → ℝ} (hΦ : Measurable Φ) :
    ∫ ω, Φ (levyGaussFine ν T δ' ω) ∂((cpInputLaw r μ).prod (gaussianReal 0 1)) =
      ∫ ω, Φ (levyGaussFine ν T δ' ω) ∂((cpInputLaw r' μ').prod (gaussianReal 0 1)) := by
  have hm : Measurable (levyGaussFine ν T δ') :=
    ((measurable_levyFine ν T δ').comp measurable_fst).add (measurable_snd.const_mul _)
  rw [← integral_map hm.aemeasurable hΦ.aestronglyMeasurable, levyGauss_coarse_map_eq hδ h h',
    integral_map hm.aemeasurable hΦ.aestronglyMeasurable]

/-- The second moment of a standard normal variate is `1` (Giles 2015, §6.2, the Brownian term). -/
lemma integral_sq_gaussianReal_std : ∫ z, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at h
  have h0 : ∫ z, id z ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  rw [h0] at h
  simpa using h

/-- Adding an independent scaled standard normal variate (Giles 2015, §6.2, p. 47, l. 2040: "adding
a Brownian diffusion term"): if `D ∈ L²(P)`, then under `P ⊗ N(0, 1)` the variable
`D(ω₁) + c ω₂` is in `L²`, has the mean of `D` and the second moment `E[D²] + c²`. -/
lemma gaussShift_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : Ω → ℝ} (hD : MemLp D 2 P) (c : ℝ) :
    MemLp (fun ω : Ω × ℝ => D ω.1 + c * ω.2) 2 (P.prod (gaussianReal 0 1)) ∧
      ∫ ω, (D ω.1 + c * ω.2) ∂(P.prod (gaussianReal 0 1)) = ∫ x, D x ∂P ∧
      ∫ ω, (D ω.1 + c * ω.2) ^ 2 ∂(P.prod (gaussianReal 0 1)) = ∫ x, D x ^ 2 ∂P + c ^ 2 := by
  have hfst : MeasurePreserving Prod.fst (P.prod (gaussianReal 0 1)) P := measurePreserving_fst
  have hsnd : MeasurePreserving Prod.snd (P.prod (gaussianReal 0 1)) (gaussianReal 0 1) :=
    measurePreserving_snd
  have hZ : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hD1 : MemLp (fun ω : Ω × ℝ => D ω.1) 2 (P.prod (gaussianReal 0 1)) :=
    hD.comp_measurePreserving hfst
  have hZ1 : MemLp (fun ω : Ω × ℝ => ω.2) 2 (P.prod (gaussianReal 0 1)) :=
    hZ.comp_measurePreserving hsnd
  have hZmean : ∫ z, z ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  refine ⟨hD1.add (hZ1.const_mul c), ?_, ?_⟩
  · rw [integral_add (hD1.integrable one_le_two) ((hZ1.const_mul c).integrable one_le_two),
      integral_const_mul, integral_fun_fst (f := D), integral_fun_snd (f := fun z => z),
      hZmean, probReal_univ, probReal_univ, one_smul, one_smul, mul_zero, add_zero]
  · have e : (fun ω : Ω × ℝ => (D ω.1 + c * ω.2) ^ 2) = fun ω =>
        D ω.1 ^ 2 + 2 * c * (D ω.1 * ω.2) + c ^ 2 * ω.2 ^ 2 := by
      funext ω
      ring
    have i1 : Integrable (fun ω : Ω × ℝ => D ω.1 ^ 2) (P.prod (gaussianReal 0 1)) :=
      hD1.integrable_sq
    have i2 : Integrable (fun ω : Ω × ℝ => D ω.1 * ω.2) (P.prod (gaussianReal 0 1)) :=
      hD1.integrable_mul hZ1
    have i3 : Integrable (fun ω : Ω × ℝ => ω.2 ^ 2) (P.prod (gaussianReal 0 1)) :=
      hZ1.integrable_sq
    have i12 : Integrable (fun ω : Ω × ℝ => D ω.1 ^ 2 + 2 * c * (D ω.1 * ω.2))
        (P.prod (gaussianReal 0 1)) := i1.add (i2.const_mul _)
    rw [e, integral_add i12 (i3.const_mul _), integral_add i1 (i2.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_fun_fst (f := fun x => D x ^ 2), integral_prod_mul D (fun z => z),
      integral_fun_snd (f := fun z => z ^ 2), hZmean, integral_sq_gaussianReal_std,
      probReal_univ, probReal_univ, one_smul, one_smul]
    ring

/-- `∫_{|z|<δ'} z² dν = ∫_{|z|<δ} z² dν + ∫_{δ≤|z|<δ'} z² dν` for `δ ≤ δ' ≤ 1` and a Lévy measure
`ν` (Giles 2015, §6.2, p. 47, l. 2048–2050, the intermediate range). -/
lemma setIntegral_small_split {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    {δ δ' : ℝ} (hδ : δ ≤ δ') (hδ1 : δ' ≤ 1) :
    ∫ z in {z : ℝ | |z| < δ'}, z ^ 2 ∂ν =
      ∫ z in {z : ℝ | |z| < δ}, z ^ 2 ∂ν + ∫ z in levyMid δ δ', z ^ 2 ∂ν := by
  have hI := integrableOn_sq_small hν hδ1
  have e : {z : ℝ | |z| < δ'} = {z : ℝ | |z| < δ} ∪ levyMid δ δ' := by
    ext z
    rw [Set.mem_union]
    constructor
    · intro hz
      by_cases h : |z| < δ
      · exact Or.inl h
      · exact Or.inr ⟨not_lt.1 h, hz⟩
    · rintro (h | h)
      · exact (show |z| < δ from h).trans_le hδ
      · exact h.2
  have hd : Disjoint {z : ℝ | |z| < δ} (levyMid δ δ') :=
    Set.disjoint_left.2 fun z h1 h2 => absurd h2.1 (not_le.2 h1)
  rw [e] at hI ⊢
  exact setIntegral_union hd (measurableSet_levyMid δ δ') (hI.mono_set Set.subset_union_left)
    (hI.mono_set Set.subset_union_right)

/-- The small-jump variance `T ∫_{|z|<δ} z² dν` is nonnegative (Giles 2015, §6.2). -/
lemma setIntegral_small_sq_nonneg (ν : Measure ℝ) (T : ℝ≥0) (δ : ℝ) :
    0 ≤ (T : ℝ) * ∫ z in {z : ℝ | |z| < δ}, z ^ 2 ∂ν :=
  mul_nonneg T.2 (setIntegral_nonneg (measurableSet_lt continuous_abs.measurable
    measurable_const) fun z _ => sq_nonneg z)

/-- `σ_δ² = T ∫_{|z|<δ} z² dν` (Giles 2015, §6.2, p. 47, l. 2040). -/
lemma levySmallStd_sq (ν : Measure ℝ) (T : ℝ≥0) (δ : ℝ) :
    levySmallStd ν T δ ^ 2 = T * ∫ z in {z : ℝ | |z| < δ}, z ^ 2 ∂ν :=
  Real.sq_sqrt (setIntegral_small_sq_nonneg ν T δ)

/-- The Brownian terms of two cutoffs `δ ≤ δ' ≤ 1` differ by at most the intermediate range
(Giles 2015, §6.2, p. 47, l. 2048–2050): `(σ_{δ'} − σ_δ)² ≤ σ_{δ'}² − σ_δ² =
T ∫_{δ≤|z|<δ'} z² dν`, since `0 ≤ σ_δ ≤ σ_{δ'}`. -/
lemma levySmallStd_sub_sq_le {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ δ' : ℝ} (hδ : δ ≤ δ') (hδ1 : δ' ≤ 1) :
    (levySmallStd ν T δ' - levySmallStd ν T δ) ^ 2 ≤ T * ∫ z in levyMid δ δ', z ^ 2 ∂ν := by
  have hs := setIntegral_small_split hν hδ hδ1
  have hm : 0 ≤ (T : ℝ) * ∫ z in levyMid δ δ', z ^ 2 ∂ν :=
    mul_nonneg T.2 (setIntegral_nonneg (measurableSet_levyMid δ δ') fun z _ => sq_nonneg z)
  have h2 : levySmallStd ν T δ' ^ 2 = levySmallStd ν T δ ^ 2 +
      T * ∫ z in levyMid δ δ', z ^ 2 ∂ν := by
    rw [levySmallStd_sq, levySmallStd_sq, hs]
    ring
  have h0 : 0 ≤ levySmallStd ν T δ := Real.sqrt_nonneg _
  have h0' : 0 ≤ levySmallStd ν T δ' := Real.sqrt_nonneg _
  have hle : levySmallStd ν T δ ≤ levySmallStd ν T δ' := by
    refine (pow_le_pow_iff_left₀ h0 h0' two_ne_zero).1 ?_
    rw [h2]
    linarith
  nlinarith

/-- **The multilevel correction with the small jumps replaced by the same Brownian increment**
(Giles 2015, §6.2, p. 47, l. 2046–2051: "The ones which are smaller than `δ_ℓ` are either neglected
for both paths, or approximated by the same Brownian increment.  The difficulty is in the
intermediate range `[δ_ℓ, δ_{ℓ−1}]` in which the jumps are simulated for the fine path, but
neglected or approximated for the coarse path").  With the simulation of the jumps `|z| ≥ δ`
(`r • μ = T • ν|_{|z| ≥ δ}`), a standard normal `W`, a Lévy measure `ν` and `δ ≤ δ' ≤ 1`, the
difference of the corrected fine value (cutoff `δ`) and the corrected coarse value (cutoff `δ'`)
is square integrable, has mean `0` and
`E[(X̂^δ − X̂^{δ'})²] = T ∫_{δ≤|z|<δ'} z² dν + (σ_{δ'} − σ_δ)² ≤ 2 T ∫_{δ≤|z|<δ'} z² dν`.
The coupling: `σ_{δ'} W = σ_δ W + (σ_{δ'} − σ_δ) W`, so the small jumps `|z| < δ` get the same
increment `σ_δ W` on both paths, and the band `δ ≤ |z| < δ'`, simulated on the fine path, is
approximated on the coarse path by the extra term `(σ_{δ'} − σ_δ) W`. -/
theorem levyGauss_correction_moments {ν : Measure ℝ}
    (hν : Integrable (fun z => min 1 (z ^ 2)) ν) {T : ℝ≥0} {δ δ' : ℝ} (hδ : δ ≤ δ')
    (hδ1 : δ' ≤ 1) {r : ℝ≥0} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : r • μ = T • ν.restrict (levySet δ)) :
    MemLp (fun ω => levyGaussFine ν T δ ω - levyGaussFine ν T δ' ω) 2
        ((cpInputLaw r μ).prod (gaussianReal 0 1)) ∧
      ∫ ω, (levyGaussFine ν T δ ω - levyGaussFine ν T δ' ω)
        ∂((cpInputLaw r μ).prod (gaussianReal 0 1)) = 0 ∧
      ∫ ω, (levyGaussFine ν T δ ω - levyGaussFine ν T δ' ω) ^ 2
        ∂((cpInputLaw r μ).prod (gaussianReal 0 1)) =
        T * ∫ z in levyMid δ δ', z ^ 2 ∂ν + (levySmallStd ν T δ' - levySmallStd ν T δ) ^ 2 ∧
      ∫ ω, (levyGaussFine ν T δ ω - levyGaussFine ν T δ' ω) ^ 2
        ∂((cpInputLaw r μ).prod (gaussianReal 0 1)) ≤
        2 * (T * ∫ z in levyMid δ δ', z ^ 2 ∂ν) := by
  have := isProbabilityMeasure_cpInputLaw r μ
  obtain ⟨-, hL2, hmean, hsq⟩ := levy_correction_moments hδ hδ1 h
  obtain ⟨hS, hSmean, hSsq⟩ := gaussShift_moments hL2 (levySmallStd ν T δ - levySmallStd ν T δ')
  have e : (fun ω => levyGaussFine ν T δ ω - levyGaussFine ν T δ' ω) = fun ω =>
      (levyFine ν T δ ω.1 - levyFine ν T δ' ω.1) +
        (levySmallStd ν T δ - levySmallStd ν T δ') * ω.2 := by
    funext ω
    unfold levyGaussFine
    ring
  have hval : ∫ ω, (levyGaussFine ν T δ ω - levyGaussFine ν T δ' ω) ^ 2
      ∂((cpInputLaw r μ).prod (gaussianReal 0 1)) =
      T * ∫ z in levyMid δ δ', z ^ 2 ∂ν + (levySmallStd ν T δ' - levySmallStd ν T δ) ^ 2 := by
    simp_rw [fun ω => congrFun e ω]
    rw [hSsq, hsq]
    ring
  refine ⟨e ▸ hS, by simp_rw [fun ω => congrFun e ω]; rw [hSmean, hmean], hval, ?_⟩
  rw [hval]
  have := levySmallStd_sub_sq_le hν T hδ hδ1
  linarith

/-- **The variance of the corrected multilevel correction of a Lipschitz payoff** (Giles 2015,
§6.2, p. 47, l. 2046–2051: the jumps smaller than `δ_ℓ` are "approximated by the same Brownian
increment", the intermediate range "contributes to a non-zero value for `P_ℓ − P_{ℓ−1}`"; §2.1,
Theorem 1, condition iii)).  With the hypotheses of `levyGauss_correction_moments` and a
`K`-Lipschitz payoff `Φ`, the correction `Φ(X̂^δ) − Φ(X̂^{δ'})` is square integrable and
`V_ℓ ≤ 2 K² T ∫_{δ≤|z|<δ'} z² dν`. -/
theorem levyGauss_correction_variance_le {ν : Measure ℝ}
    (hν : Integrable (fun z => min 1 (z ^ 2)) ν) {T : ℝ≥0} {δ δ' : ℝ} (hδ : δ ≤ δ')
    (hδ1 : δ' ≤ 1) {r : ℝ≥0} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : r • μ = T • ν.restrict (levySet δ)) {Φ : ℝ → ℝ} {K : ℝ≥0} (hΦ : LipschitzWith K Φ) :
    MemLp (fun ω => Φ (levyGaussFine ν T δ ω) - Φ (levyGaussFine ν T δ' ω)) 2
        ((cpInputLaw r μ).prod (gaussianReal 0 1)) ∧
      variance (fun ω => Φ (levyGaussFine ν T δ ω) - Φ (levyGaussFine ν T δ' ω))
        ((cpInputLaw r μ).prod (gaussianReal 0 1)) ≤
        2 * K ^ 2 * (T * ∫ z in levyMid δ δ', z ^ 2 ∂ν) := by
  have := isProbabilityMeasure_cpInputLaw r μ
  obtain ⟨hL2, -, -, hle⟩ := levyGauss_correction_moments hν hδ hδ1 h
  have hmG : ∀ d, Measurable (levyGaussFine ν T d) := fun d =>
    ((measurable_levyFine ν T d).comp measurable_fst).add (measurable_snd.const_mul _)
  have hm : Measurable fun ω => Φ (levyGaussFine ν T δ ω) - Φ (levyGaussFine ν T δ' ω) :=
    (hΦ.continuous.measurable.comp (hmG δ)).sub (hΦ.continuous.measurable.comp (hmG δ'))
  have hL2' : MemLp (fun ω => Φ (levyGaussFine ν T δ ω) - Φ (levyGaussFine ν T δ' ω)) 2
      ((cpInputLaw r μ).prod (gaussianReal 0 1)) :=
    (hL2.const_mul (K : ℝ)).of_le hm.aestronglyMeasurable (ae_of_all _ fun ω => by
      have h1 := hΦ.dist_le_mul (levyGaussFine ν T δ ω) (levyGaussFine ν T δ' ω)
      rw [Real.dist_eq, Real.dist_eq] at h1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, NNReal.abs_eq]
      exact h1)
  refine ⟨hL2', (variance_le_expectation_sq hm.aestronglyMeasurable).trans ?_⟩
  calc ∫ ω, (Φ (levyGaussFine ν T δ ω) - Φ (levyGaussFine ν T δ' ω)) ^ 2
        ∂((cpInputLaw r μ).prod (gaussianReal 0 1))
      ≤ ∫ ω, (K : ℝ) ^ 2 * (levyGaussFine ν T δ ω - levyGaussFine ν T δ' ω) ^ 2
        ∂((cpInputLaw r μ).prod (gaussianReal 0 1)) :=
        integral_mono hL2'.integrable_sq (hL2.integrable_sq.const_mul _) fun ω =>
          sq_sub_le_of_lipschitz hΦ _ _
    _ = (K : ℝ) ^ 2 * ∫ ω, (levyGaussFine ν T δ ω - levyGaussFine ν T δ' ω) ^ 2
        ∂((cpInputLaw r μ).prod (gaussianReal 0 1)) := integral_const_mul _ _
    _ ≤ (K : ℝ) ^ 2 * (2 * (T * ∫ z in levyMid δ δ', z ^ 2 ∂ν)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 2 * K ^ 2 * (T * ∫ z in levyMid δ δ', z ^ 2 ∂ν) := by ring

/-! ### Part 1 on one space for all levels: convergence and Theorem 1 -/

/-- **The corrected level-`ℓ` approximation on the common space** (Giles 2015, §6.2, p. 47,
l. 2038–2048): the level-`ℓ` approximation `bandApprox ν T δ ℓ` built from the bands of jump sizes
(the jumps `|z| ≥ δ_ℓ`, compensated) plus `σ_{δ_ℓ} W`, with one standard normal `W` shared by all
levels. -/
noncomputable def bandGaussApprox (ν : Measure ℝ) (T : ℝ≥0) (δ : ℕ → ℝ) (ℓ : ℕ)
    (ω : (ℕ → ℕ × (ℕ → ℝ)) × ℝ) : ℝ :=
  bandApprox ν T δ ℓ ω.1 + levySmallStd ν T (δ ℓ) * ω.2

/-- The corrected level-`ℓ` approximation is measurable (Giles 2015, §6.2). -/
lemma measurable_bandGaussApprox (ν : Measure ℝ) (T : ℝ≥0) (δ : ℕ → ℝ) (ℓ : ℕ) :
    Measurable (bandGaussApprox ν T δ ℓ) :=
  ((measurable_bandApprox ν T δ ℓ).comp measurable_fst).add (measurable_snd.const_mul _)

/-- **The corrected levels on the common space** (Giles 2015, §6.2, p. 47, l. 2042–2048: "the
cutoff `δ_ℓ` for the jumps which are simulated varies with level", the small jumps
"approximated by the same Brownian increment").  For a Lévy measure `ν`, cutoffs
`0 < δ_k ≤ δ_0 ≤ 1` decreasing, the band inputs `Λ_k • M_k = T • ν|_{band k}` and a standard normal
`W`, for `ℓ ≤ ℓ'` the difference of the corrected level-`ℓ'` and level-`ℓ` approximations is
square integrable with
`E[(X̂^{δ_{ℓ'}} − X̂^{δ_ℓ})²] = T ∫_{δ_{ℓ'}≤|z|<δ_ℓ} z² dν + (σ_{δ_ℓ} − σ_{δ_{ℓ'}})²
≤ 2 T ∫_{δ_{ℓ'}≤|z|<δ_ℓ} z² dν`. -/
theorem bandGauss_sq_sub {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ) (hδ1 : δ 0 ≤ 1)
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k)) {ℓ ℓ' : ℕ} (hℓ : ℓ ≤ ℓ') :
    MemLp (fun ω => bandGaussApprox ν T δ ℓ' ω - bandGaussApprox ν T δ ℓ ω) 2
        ((bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
      ∫ ω, (bandGaussApprox ν T δ ℓ' ω - bandGaussApprox ν T δ ℓ ω) ^ 2
        ∂((bandInputLaw Λ M).prod (gaussianReal 0 1)) =
        T * ∫ z in levyMid (δ ℓ') (δ ℓ), z ^ 2 ∂ν +
          (levySmallStd ν T (δ ℓ) - levySmallStd ν T (δ ℓ')) ^ 2 ∧
      ∫ ω, (bandGaussApprox ν T δ ℓ' ω - bandGaussApprox ν T δ ℓ ω) ^ 2
        ∂((bandInputLaw Λ M).prod (gaussianReal 0 1)) ≤
        2 * (T * ∫ z in levyMid (δ ℓ') (δ ℓ), z ^ 2 ∂ν) := by
  have := isProbabilityMeasure_bandInputLaw Λ M
  obtain ⟨hL2, hsq⟩ := bandApprox_sq_sub hν T hδpos hδanti hδ1 hband hℓ
  obtain ⟨hS, -, hSsq⟩ := gaussShift_moments hL2
    (levySmallStd ν T (δ ℓ') - levySmallStd ν T (δ ℓ))
  have e : ∀ ω, bandGaussApprox ν T δ ℓ' ω - bandGaussApprox ν T δ ℓ ω =
      (bandApprox ν T δ ℓ' ω.1 - bandApprox ν T δ ℓ ω.1) +
        (levySmallStd ν T (δ ℓ') - levySmallStd ν T (δ ℓ)) * ω.2 := fun ω => by
    unfold bandGaussApprox
    ring
  have hval : ∫ ω, (bandGaussApprox ν T δ ℓ' ω - bandGaussApprox ν T δ ℓ ω) ^ 2
      ∂((bandInputLaw Λ M).prod (gaussianReal 0 1)) =
      T * ∫ z in levyMid (δ ℓ') (δ ℓ), z ^ 2 ∂ν +
        (levySmallStd ν T (δ ℓ) - levySmallStd ν T (δ ℓ')) ^ 2 := by
    simp_rw [e]
    rw [hSsq, hsq]
    ring
  refine ⟨?_, hval, ?_⟩
  · simp_rw [e]
    exact hS
  · rw [hval]
    have := levySmallStd_sub_sq_le hν T (hδanti hℓ) ((hδanti (Nat.zero_le ℓ)).trans hδ1)
    linarith

/-- **The corrected levels converge to the same limit at the same rate** (Giles 2015, §6.2, p. 47,
l. 2038–2043: "simulate the large jumps and either neglect the small jumps or approximate their
effect by adding a Brownian diffusion term …  `δ_ℓ → 0` as `ℓ → ∞` to ensure that the bias
converges to zero").  Let `ν` be a Lévy measure, `T ≥ 0`, the cutoffs `0 < δ_ℓ ≤ δ_0 ≤ 1` decrease
to `0`, and let all levels be built from independent compound Poisson inputs for the bands
(`Λ_k • M_k = T • ν|_{band k}`) and one standard normal `W`.  Then there is an `L²` limit `X` of
the truncated levels (`X − X^{δ_0} ∈ L²`, `E[(X − X^{δ_ℓ})²] = T ∫_{|z|<δ_ℓ} z² dν`), and the
corrected levels `X̂^{δ_ℓ} = X^{δ_ℓ} + σ_{δ_ℓ} W` satisfy
`E[(X − X̂^{δ_ℓ})²] = 2 T ∫_{|z|<δ_ℓ} z² dν`, which tends to `0`; for every `K`-Lipschitz payoff
`Φ`, `|E[Φ(X̂^{δ_ℓ}) − Φ(X)]| ≤ K (2 T ∫_{|z|<δ_ℓ} z² dν)^{1/2}`.  (The factor `2`: `W` is
independent of the small jumps it replaces.  The bias depends only on the laws, and this bound,
through the independent coupling, is not sharp: the smaller bias of Dereich (2011) for Lipschitz
payoffs, from a Wasserstein bound between the small-jump part and its Gaussian replacement, is not
proved here.) -/
theorem levyGauss_limit {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ) (hδ1 : δ 0 ≤ 1)
    (hδlim : Tendsto δ atTop (𝓝 0)) {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ}
    [∀ k, IsProbabilityMeasure (M k)] (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k)) :
    ∃ X : (ℕ → ℕ × (ℕ → ℝ)) → ℝ,
      MemLp (fun ω => X ω - bandApprox ν T δ 0 ω) 2 (bandInputLaw Λ M) ∧
      (∀ ℓ, Integrable (fun ω => (X ω - bandApprox ν T δ ℓ ω) ^ 2) (bandInputLaw Λ M) ∧
        ∫ ω, (X ω - bandApprox ν T δ ℓ ω) ^ 2 ∂(bandInputLaw Λ M) =
          T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν) ∧
      (∀ ℓ, Integrable (fun ω => (X ω.1 - bandGaussApprox ν T δ ℓ ω) ^ 2)
          ((bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
        ∫ ω, (X ω.1 - bandGaussApprox ν T δ ℓ ω) ^ 2
          ∂((bandInputLaw Λ M).prod (gaussianReal 0 1)) =
          2 * (T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν)) ∧
      Tendsto (fun ℓ => (T : ℝ) * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν) atTop (𝓝 0) ∧
      ∀ (Φ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K Φ → ∀ ℓ,
        Integrable (fun ω => Φ (bandGaussApprox ν T δ ℓ ω) - Φ (X ω.1))
          ((bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
        |∫ ω, Φ (bandGaussApprox ν T δ ℓ ω) - Φ (X ω.1)
            ∂((bandInputLaw Λ M).prod (gaussianReal 0 1))| ≤
          K * Real.sqrt (2 * (T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν)) := by
  obtain ⟨X, hX0, hXℓ, hτ, -⟩ := levy_truncation_limit hν T hδpos hδanti hδ1 hδlim hband
  have := isProbabilityMeasure_bandInputLaw Λ M
  set P := bandInputLaw Λ M with hP
  set Q := P.prod (gaussianReal 0 1) with hQ
  -- `X − X^{δ_ℓ} ∈ L²`
  have hD : ∀ ℓ, MemLp (fun ω => X ω - bandApprox ν T δ ℓ ω) 2 P := fun ℓ => by
    have h := hX0.sub (bandApprox_sq_sub hν T hδpos hδanti hδ1 hband (Nat.zero_le ℓ)).1
    have e : (fun ω => X ω - bandApprox ν T δ ℓ ω) = (fun ω => X ω - bandApprox ν T δ 0 ω) -
        fun ω => bandApprox ν T δ ℓ ω - bandApprox ν T δ 0 ω := by
      funext ω
      simp only [Pi.sub_apply]
      ring
    rw [e]
    exact h
  have e : ∀ ℓ ω, X ω.1 - bandGaussApprox ν T δ ℓ ω =
      (X ω.1 - bandApprox ν T δ ℓ ω.1) + (-levySmallStd ν T (δ ℓ)) * ω.2 := fun ℓ ω => by
    unfold bandGaussApprox
    ring
  have hG : ∀ ℓ, MemLp (fun ω => X ω.1 - bandGaussApprox ν T δ ℓ ω) 2 Q ∧
      ∫ ω, (X ω.1 - bandGaussApprox ν T δ ℓ ω) ^ 2 ∂Q =
        2 * (T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν) := fun ℓ => by
    obtain ⟨hS, -, hSsq⟩ := gaussShift_moments (hD ℓ) (-levySmallStd ν T (δ ℓ))
    simp_rw [e ℓ]
    refine ⟨hS, ?_⟩
    rw [hSsq, (hXℓ ℓ).2, neg_sq, levySmallStd_sq]
    ring
  refine ⟨X, hX0, hXℓ, fun ℓ => ⟨(hG ℓ).1.integrable_sq, (hG ℓ).2⟩, hτ, ?_⟩
  intro Φ K hΦ ℓ
  have hXm : AEStronglyMeasurable (fun ω : (ℕ → ℕ × (ℕ → ℝ)) × ℝ => X ω.1) Q := by
    have h := (hG ℓ).1.1.add (measurable_bandGaussApprox ν T δ ℓ).aestronglyMeasurable
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  have hm : AEStronglyMeasurable (fun ω => Φ (bandGaussApprox ν T δ ℓ ω) - Φ (X ω.1)) Q :=
    (hΦ.continuous.measurable.comp
      (measurable_bandGaussApprox ν T δ ℓ)).aestronglyMeasurable.sub
      (hΦ.continuous.comp_aestronglyMeasurable hXm)
  have hpt : ∀ ω : (ℕ → ℕ × (ℕ → ℝ)) × ℝ, |Φ (bandGaussApprox ν T δ ℓ ω) - Φ (X ω.1)| ≤
      K * |X ω.1 - bandGaussApprox ν T δ ℓ ω| := fun ω => by
    have h1 := hΦ.dist_le_mul (bandGaussApprox ν T δ ℓ ω) (X ω.1)
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (bandGaussApprox ν T δ ℓ ω)] at h1
    exact h1
  have hI1 := (((hG ℓ).1).integrable one_le_two).abs.const_mul (K : ℝ)
  have hI : Integrable (fun ω => Φ (bandGaussApprox ν T δ ℓ ω) - Φ (X ω.1)) Q :=
    hI1.mono' hm (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hpt ω)
  refine ⟨hI, ?_⟩
  calc |∫ ω, Φ (bandGaussApprox ν T δ ℓ ω) - Φ (X ω.1) ∂Q|
      ≤ ∫ ω, |Φ (bandGaussApprox ν T δ ℓ ω) - Φ (X ω.1)| ∂Q := abs_integral_le_integral_abs
    _ ≤ ∫ ω, K * |X ω.1 - bandGaussApprox ν T δ ℓ ω| ∂Q := integral_mono hI.abs hI1 hpt
    _ = K * ∫ ω, |X ω.1 - bandGaussApprox ν T δ ℓ ω| ∂Q := integral_const_mul _ _
    _ ≤ K * Real.sqrt (∫ ω, (X ω.1 - bandGaussApprox ν T δ ℓ ω) ^ 2 ∂Q) :=
        mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq (hG ℓ).1) K.2
    _ = K * Real.sqrt (2 * (T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν)) := by rw [(hG ℓ).2]

/-- **The expected cost of the corrected estimator** (Giles 2015, §2.1, Theorem 1, p. 6–7,
l. 302–304: "expected costs to allow for applications in which the simulation cost of individual
samples is itself random"; §6.2, p. 47, l. 2038–2041).  Sample `n` of level `ℓ` uses its own input
`x(ℓ, n)` (all bands and a normal variate, i.i.d. with law `bandInputLaw Λ M ⊗ N(0, 1)`) and costs
one plus the number `∑_{k≤ℓ} N_k^{(ℓ,n)}` of jumps it simulates.  For every `L` and
`N_0, …, N_L` the random total cost is integrable with expectation
`∑_{ℓ≤L} N_ℓ (1 + T ν(|z| ≥ δ_ℓ))`. -/
theorem levyGauss_expected_cost {ν : Measure ℝ} (T : ℝ≥0) {δ : ℕ → ℝ} (hδanti : Antitone δ)
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k)) (L : ℕ) (N : ℕ → ℕ) :
    Integrable (fun x : ℕ × ℕ → (ℕ → ℕ × (ℕ → ℝ)) × ℝ => ∑ ℓ ∈ range (L + 1),
        ∑ n ∈ range (N ℓ), (1 + ∑ k ∈ range (ℓ + 1), (((x (ℓ, n)).1 k).1 : ℝ)))
      (Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
    ∫ x, ∑ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ), (1 + ∑ k ∈ range (ℓ + 1), (((x (ℓ, n)).1 k).1 : ℝ))
        ∂(Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1)) =
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * (ν (levySet (δ ℓ))).toReal) := by
  have := isProbabilityMeasure_bandInputLaw Λ M
  have hmp : MeasurePreserving (fun (x : ℕ × ℕ → (ℕ → ℕ × (ℕ → ℝ)) × ℝ) p => (x p).1)
      (Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1))
      (Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_fst)]
    congr 1
    funext p
    exact (measurePreserving_fst (μ := bandInputLaw Λ M) (ν := gaussianReal 0 1)).map_eq
  obtain ⟨hI, hE⟩ := levy_expected_cost T hδanti hband L N
  refine ⟨hmp.integrable_comp_of_integrable hI, ?_⟩
  rw [← hE]
  exact integral_comp_of_measurePreserving hmp hI.1
    (f := fun x : ℕ × ℕ → ℕ → ℕ × (ℕ → ℝ) => ∑ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ),
      (1 + ∑ k ∈ range (ℓ + 1), ((x (ℓ, n) k).1 : ℝ)))

/-- **Theorem 1 for the truncated Lévy levels with the small jumps replaced by a Brownian term**
(Giles 2015, §6.2, p. 47, l. 2038–2051: "simulate the large jumps and either neglect the small
jumps or approximate their effect by adding a Brownian diffusion term"; "The ones which are smaller
than `δ_ℓ` are … approximated by the same Brownian increment"; with §2.1, Theorem 1).  Hypotheses
as in `levy_truncation_theorem1`: a Lévy measure `ν` with `∫_{|z|≥1} z² dν < ∞`, the cutoffs
`δ_ℓ = 2^{−ℓ}`, the band inputs `Λ_k • M_k = T • ν|_{band k}`, a `K`-Lipschitz payoff `Φ`, and the
rates `T ∫_{|z|<δ_ℓ} z² dν ≤ a δ_ℓ^{2−Y}`, `T ν(|z| ≥ δ_ℓ) ≤ b δ_ℓ^{−Y}` with `0 < Y < 2`.  The
corrected level `ℓ` adds `σ_{δ_ℓ} W` to the truncated value, with one standard normal `W` per sample
shared by its fine and coarse paths.  Then the corrected levels converge to the limit `X`
(`E[(X − X̂^{δ_ℓ})²] = 2 T ∫_{|z|<δ_ℓ} z² dν`), and the multilevel estimator of `E[Φ(X)]`
satisfies Theorem 1 with `α = (2 − Y)/2`, `β = 2 − Y`, `γ = Y`: for every `0 < ε < e⁻¹` there are
`L` and `N_ℓ ≥ 1` with square-integrable error, mean square error `< ε²`, and an integrable random
cost (one plus the number of simulated jumps per sample) with expectation
`∑_ℓ N_ℓ (1 + T ν(|z| ≥ δ_ℓ)) ≤ c₄ · complexityBound α β γ ε`.  These rates are those of
`levy_truncation_theorem1` and do not show Dereich's (2011) improvement (a smaller bias for
Lipschitz payoffs, from a Wasserstein bound between the small jumps and their Gaussian
replacement, and a better complexity when the Blumenthal–Getoor index, the role played by `Y`
here, exceeds 1), which is not proved here. -/
theorem levyGauss_theorem1 {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (hlarge : IntegrableOn (fun z => z ^ 2) (levySet 1) ν) (T : ℝ≥0) {Y a b : ℝ}
    (hY0 : 0 < Y) (hY2 : Y < 2)
    (hsmall : ∀ ℓ : ℕ, (T : ℝ) * ∫ z in {z : ℝ | |z| < (2 : ℝ)⁻¹ ^ ℓ}, z ^ 2 ∂ν ≤
      a * (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))))
    (hcount : ∀ ℓ : ℕ, (T : ℝ) * (ν (levySet ((2 : ℝ)⁻¹ ^ ℓ))).toReal ≤
      b * (2 : ℝ) ^ (Y * (ℓ : ℝ)))
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) k))
    {Φ : ℝ → ℝ} {K : ℝ≥0} (hΦ : LipschitzWith K Φ) :
    ∃ X : (ℕ → ℕ × (ℕ → ℝ)) → ℝ,
      (∀ ℓ, Integrable (fun ω => (X ω.1 - bandGaussApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω) ^ 2)
          ((bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
        ∫ ω, (X ω.1 - bandGaussApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω) ^ 2
            ∂((bandInputLaw Λ M).prod (gaussianReal 0 1)) =
          2 * (T * ∫ z in {z : ℝ | |z| < (2 : ℝ)⁻¹ ^ ℓ}, z ^ 2 ∂ν)) ∧
      Integrable (fun ω => Φ (X ω.1)) ((bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
      ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ ω => Φ (bandGaussApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω))
              (fun ℓ ω => Φ (bandGaussApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω)))
              (fun p x => x p) ℓ (N ℓ) x -
                ∫ ω, Φ (X ω.1) ∂((bandInputLaw Λ M).prod (gaussianReal 0 1))) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ ω => Φ (bandGaussApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω))
              (fun ℓ ω => Φ (bandGaussApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω)))
              (fun p x => x p) ℓ (N ℓ) x -
                ∫ ω, Φ (X ω.1) ∂((bandInputLaw Λ M).prod (gaussianReal 0 1))) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1)) <
            ε ^ 2 ∧
          Integrable (fun x : ℕ × ℕ → (ℕ → ℕ × (ℕ → ℝ)) × ℝ => ∑ ℓ ∈ range (L + 1),
              ∑ n ∈ range (N ℓ), (1 + ∑ k ∈ range (ℓ + 1), (((x (ℓ, n)).1 k).1 : ℝ)))
            (Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
          ∫ x, ∑ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ),
              (1 + ∑ k ∈ range (ℓ + 1), (((x (ℓ, n)).1 k).1 : ℝ))
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1)) =
            ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * (ν (levySet ((2 : ℝ)⁻¹ ^ ℓ))).toReal) ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * (ν (levySet ((2 : ℝ)⁻¹ ^ ℓ))).toReal) ≤
            c₄ * complexityBound ((2 - Y) / 2) (2 - Y) Y ε := by
  set δ : ℕ → ℝ := fun ℓ => (2 : ℝ)⁻¹ ^ ℓ with hδdef
  have hδpos : ∀ k, 0 < δ k := fun k => by positivity
  have hδanti : Antitone δ := fun m n hmn =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hδ1 : δ 0 ≤ 1 := le_of_eq (pow_zero _)
  have hδ1' : ∀ ℓ, δ ℓ ≤ 1 := fun ℓ => (hδanti (Nat.zero_le ℓ)).trans hδ1
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨X, hX0, -, hXG, -, hbias⟩ := levyGauss_limit hν T hδpos hδanti hδ1 hδlim hband
  have := isProbabilityMeasure_bandInputLaw Λ M
  set P := bandInputLaw Λ M with hP
  set Q := P.prod (gaussianReal 0 1) with hQ
  -- the level approximations are square integrable
  have hPk : ∀ k, IsProbabilityMeasure (cpInputLaw (Λ k) (M k)) := fun k =>
    isProbabilityMeasure_cpInputLaw _ _
  have hA0 : MemLp (bandApprox ν T δ 0) 2 P := by
    have hev0 : MeasurePreserving (fun ω : ℕ → ℕ × (ℕ → ℝ) => ω 0) P
        (cpInputLaw (Λ 0) (M 0)) :=
      measurePreserving_eval_infinitePi (fun k => cpInputLaw (Λ k) (M k)) 0
    have hB : levyBand δ 0 = levySet 1 := by
      change levySet ((2 : ℝ)⁻¹ ^ 0) = levySet 1
      rw [pow_zero]
    have h1 := memLp_cpSum_indicator (measurableSet_levyBand δ 0) (hband 0)
      (by rw [hB]; exact hlarge)
    have h2 := (h1.comp_measurePreserving hev0).sub (memLp_const (levyComp ν T (δ 0)))
    have e : bandApprox ν T δ 0 =
        fun ω => cpSum ((levyBand δ 0).indicator id) (ω 0) - levyComp ν T (δ 0) := by
      funext ω
      rw [bandApprox, Finset.sum_range_one]
    rw [e]
    exact h2
  have hA : ∀ ℓ, MemLp (bandApprox ν T δ ℓ) 2 P := fun ℓ => by
    have h := (bandApprox_sq_sub hν T hδpos hδanti hδ1 hband (Nat.zero_le ℓ)).1.add hA0
    have e : bandApprox ν T δ ℓ =
        (fun ω => bandApprox ν T δ ℓ ω - bandApprox ν T δ 0 ω) + bandApprox ν T δ 0 := by
      funext ω
      simp
    rw [e]
    exact h
  have hAG : ∀ ℓ, MemLp (bandGaussApprox ν T δ ℓ) 2 Q := fun ℓ =>
    (gaussShift_moments (hA ℓ) (levySmallStd ν T (δ ℓ))).1
  have hXL2 : MemLp (fun ω : (ℕ → ℕ × (ℕ → ℝ)) × ℝ => X ω.1) 2 Q := by
    have hXP : MemLp X 2 P := by
      have h := hX0.add hA0
      have e : X = (fun ω => X ω - bandApprox ν T δ 0 ω) + bandApprox ν T δ 0 := by
        funext ω
        simp
      rw [e]
      exact h
    exact hXP.comp_measurePreserving measurePreserving_fst
  have hPf : ∀ ℓ, MemLp (fun ω => Φ (bandGaussApprox ν T δ ℓ ω)) 2 Q := fun ℓ =>
    memLp_comp_lipschitz hΦ (hAG ℓ)
  have hPfm : ∀ ℓ, Measurable (fun ω => Φ (bandGaussApprox ν T δ ℓ ω)) := fun ℓ =>
    hΦ.continuous.measurable.comp (measurable_bandGaussApprox ν T δ ℓ)
  have hPX : Integrable (fun ω => Φ (X ω.1)) Q :=
    (memLp_comp_lipschitz hΦ hXL2).integrable one_le_two
  refine ⟨X, hXG, hPX, ?_⟩
  -- the constants
  have ha : 0 ≤ a := by
    have h0 := hsmall 0
    have hnn := setIntegral_small_sq_nonneg ν T ((2 : ℝ)⁻¹ ^ 0)
    rw [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one] at h0
    linarith
  -- (i): `α = (2 − Y)/2`
  have hc₁ : 0 < K * Real.sqrt (2 * a) + 1 := by positivity
  have h_i : ∀ ℓ : ℕ, |∫ ω, Φ (bandGaussApprox ν T δ ℓ ω) - Φ (X ω.1) ∂Q| ≤
      (K * Real.sqrt (2 * a) + 1) * (2 : ℝ) ^ (-((2 - Y) / 2 * (ℓ : ℝ))) := by
    intro ℓ
    have h1 := (hbias Φ K hΦ ℓ).2
    have h2 : Real.sqrt (2 * (T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν)) ≤
        Real.sqrt (2 * a) * (2 : ℝ) ^ (-((2 - Y) / 2 * (ℓ : ℝ))) := by
      rw [← sqrt_mul_two_rpow (by positivity), mul_assoc]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hsmall ℓ) (by norm_num))
    have h3 : 0 ≤ (2 : ℝ) ^ (-((2 - Y) / 2 * (ℓ : ℝ))) := by positivity
    calc _ ≤ K * Real.sqrt (2 * (T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν)) := h1
      _ ≤ K * (Real.sqrt (2 * a) * (2 : ℝ) ^ (-((2 - Y) / 2 * (ℓ : ℝ)))) :=
          mul_le_mul_of_nonneg_left h2 K.2
      _ ≤ (K * Real.sqrt (2 * a) + 1) * (2 : ℝ) ^ (-((2 - Y) / 2 * (ℓ : ℝ))) := by nlinarith
  -- (iii): `β = 2 − Y`
  set V₀ := variance (fun ω => Φ (bandGaussApprox ν T δ 0 ω)) Q with hV₀
  have hV₀0 : 0 ≤ V₀ := variance_nonneg _ _
  have hc₂ : 0 < V₀ + 2 * (K : ℝ) ^ 2 * a * (2 : ℝ) ^ (2 - Y) + 1 := by positivity
  have h_iii : ∀ ℓ, variance (fineCoarseDiff (fun ℓ ω => Φ (bandGaussApprox ν T δ ℓ ω))
      (fun ℓ ω => Φ (bandGaussApprox ν T δ ℓ ω)) ℓ) Q ≤
      (V₀ + 2 * (K : ℝ) ^ 2 * a * (2 : ℝ) ^ (2 - Y) + 1) *
        (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))) := by
    intro ℓ
    cases ℓ with
    | zero =>
      rw [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one]
      change V₀ ≤ _
      have : 0 ≤ 2 * (K : ℝ) ^ 2 * a * (2 : ℝ) ^ (2 - Y) := by positivity
      linarith
    | succ ℓ =>
      have hm := (measurable_fineCoarseDiff hPfm hPfm (ℓ + 1)).aestronglyMeasurable (μ := Q)
      refine (variance_le_expectation_sq hm).trans ?_
      have hD := bandGauss_sq_sub hν T hδpos hδanti hδ1 hband (Nat.le_succ ℓ)
      have h1 : ∫ ω, (fineCoarseDiff (fun ℓ ω => Φ (bandGaussApprox ν T δ ℓ ω))
          (fun ℓ ω => Φ (bandGaussApprox ν T δ ℓ ω)) (ℓ + 1) ^ 2) ω ∂Q ≤
          (K : ℝ) ^ 2 * ∫ ω, (bandGaussApprox ν T δ (ℓ + 1) ω - bandGaussApprox ν T δ ℓ ω) ^ 2
            ∂Q := by
        rw [← integral_const_mul]
        refine integral_mono ((hPf (ℓ + 1)).sub (hPf ℓ)).integrable_sq
          (hD.1.integrable_sq.const_mul _) fun ω => ?_
        exact sq_sub_le_of_lipschitz hΦ _ _
      have h2 : (T : ℝ) * ∫ z in levyMid (δ (ℓ + 1)) (δ ℓ), z ^ 2 ∂ν ≤
          a * (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))) := by
        refine le_trans (mul_le_mul_of_nonneg_left (setIntegral_mono_set
          (integrableOn_sq_small hν (hδ1' ℓ)) (ae_of_all _ fun z => sq_nonneg z)
          (Eventually.of_forall fun z hz => hz.2)) T.2) (hsmall ℓ)
      have e : (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))) =
          (2 : ℝ) ^ (2 - Y) * (2 : ℝ) ^ (-((2 - Y) * ((ℓ + 1 : ℕ) : ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        push_cast
        ring
      rw [e] at h2
      have hK2 : 0 ≤ (K : ℝ) ^ 2 := by positivity
      have h4 : 0 ≤ (2 : ℝ) ^ (-((2 - Y) * ((ℓ + 1 : ℕ) : ℝ))) := by positivity
      calc _ ≤ (K : ℝ) ^ 2 * ∫ ω, (bandGaussApprox ν T δ (ℓ + 1) ω -
            bandGaussApprox ν T δ ℓ ω) ^ 2 ∂Q := h1
        _ ≤ (K : ℝ) ^ 2 * (2 * ((T : ℝ) * ∫ z in levyMid (δ (ℓ + 1)) (δ ℓ), z ^ 2 ∂ν)) :=
            mul_le_mul_of_nonneg_left hD.2.2 hK2
        _ ≤ (K : ℝ) ^ 2 * (2 * (a * ((2 : ℝ) ^ (2 - Y) *
            (2 : ℝ) ^ (-((2 - Y) * ((ℓ + 1 : ℕ) : ℝ)))))) :=
            mul_le_mul_of_nonneg_left (by linarith) hK2
        _ ≤ _ := by nlinarith
  -- (iv): `γ = Y`, cost = expected number of simulated jumps plus one
  have hc₃ : 0 < 1 + |b| := by positivity
  have h_iv : ∀ ℓ : ℕ, 1 + (T : ℝ) * (ν (levySet (δ ℓ))).toReal ≤
      (1 + |b|) * (2 : ℝ) ^ (Y * (ℓ : ℝ)) := by
    intro ℓ
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Y * (ℓ : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have h2 : (T : ℝ) * (ν (levySet (δ ℓ))).toReal ≤ b * (2 : ℝ) ^ (Y * (ℓ : ℝ)) := hcount ℓ
    have h3 : b * (2 : ℝ) ^ (Y * (ℓ : ℝ)) ≤ |b| * (2 : ℝ) ^ (Y * (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_abs_self b) (by positivity)
    nlinarith
  have hαβγ : min (2 - Y) Y / 2 ≤ (2 - Y) / 2 := by
    have := min_le_left (2 - Y) Y
    linarith
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs Q
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => Q)
    (fun ω => Φ (X ω.1)) (fun ℓ ω => Φ (bandGaussApprox ν T δ ℓ ω))
    (fun ℓ ω => Φ (bandGaussApprox ν T δ ℓ ω)) (fun p x => x p)
    (fun ℓ _ _ => 1 + (T : ℝ) * (ν (levySet (δ ℓ))).toReal)
    (fun ℓ => 1 + (T : ℝ) * (ν (levySet (δ ℓ))).toReal)
    (α := (2 - Y) / 2) (β := 2 - Y) (γ := Y) (by linarith) (by linarith) hY0 hc₁ hc₂ hc₃ hαβγ
    hω hind hPX hPfm hPfm hPf hPf (fun _ => rfl) (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul])
    (fun ℓ => by
      rw [integral_sub ((hPf ℓ).integrable one_le_two) hPX]
      rw [← integral_sub ((hPf ℓ).integrable one_le_two) hPX]
      exact h_i ℓ) h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  obtain ⟨hcI, hcE⟩ := levyGauss_expected_cost T hδanti hband L N
  refine ⟨L, N, hN, ?_, hmse, hcI, hcE, ?_⟩
  · exact ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω (memLp_fineCoarseDiff hPf hPf) ℓ
      (N ℓ)).sub (memLp_const _)).integrable_sq
  · unfold totalCost at hcost
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
      probReal_univ, one_smul] at hcost
    exact hcost

/-- **Theorem 1 end to end for the stable-like example with the small jumps replaced by a Brownian
term** (Giles 2015, §6.2, p. 47, l. 2038–2048: "With infinite activity Lévy processes it is
impossible to simulate each jump.  One approach is to simulate the large jumps and either neglect
the small jumps or approximate their effect by adding a Brownian diffusion term"; "The ones which
are smaller than `δ_ℓ` are … approximated by the same Brownian increment"; with §2.1, Theorem 1).
The Lévy measure `ν(dz) = c z^{−1−Y} dz` on `0 < z ≤ 1` (`c > 0`, `0 < Y < 2`) of
`levy_stableLike_theorem1`, at time `T`, cutoffs `δ_ℓ = 2^{−ℓ}`, band inputs
`Λ_k • M_k = T • ν|_{band k}` (they exist, `exists_levy_bandLaws`), one standard normal `W` per
sample shared by its fine and coarse paths, and a `K`-Lipschitz payoff `Φ`.  The corrected levels
satisfy `E[(X − X̂^{δ_ℓ})²] = 2 T c 2^{−(2−Y)ℓ}/(2 − Y)` for an `L²` limit `X` of the truncated
levels, and the multilevel estimator of `E[Φ(X)]` satisfies Theorem 1 with `α = (2 − Y)/2`,
`β = 2 − Y`, `γ = Y`: mean square error `< ε²` with an integrable random total cost (one plus the
number of simulated jumps per sample) whose expectation is
`∑_ℓ N_ℓ (1 + T c (2^{Yℓ} − 1)/Y) ≤ c₄ · complexityBound α β γ ε`.  These are the rates of
`levy_stableLike_theorem1`; Dereich's (2011) improvement for `Y > 1` is not proved here. -/
theorem levyGauss_stableLike_theorem1 {c Y : ℝ} (hc : 0 < c) (hY0 : 0 < Y) (hY2 : Y < 2)
    (T : ℝ≥0) {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k =
      T • (stableLikeLevy c Y).restrict (levyBand (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) k))
    {Φ : ℝ → ℝ} {K : ℝ≥0} (hΦ : LipschitzWith K Φ) :
    ∃ X : (ℕ → ℕ × (ℕ → ℝ)) → ℝ,
      (∀ ℓ : ℕ, Integrable (fun ω => (X ω.1 -
          bandGaussApprox (stableLikeLevy c Y) T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω) ^ 2)
          ((bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
        ∫ ω, (X ω.1 - bandGaussApprox (stableLikeLevy c Y) T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω) ^ 2
            ∂((bandInputLaw Λ M).prod (gaussianReal 0 1)) =
          2 * T * c * (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))) / (2 - Y)) ∧
      Integrable (fun ω => Φ (X ω.1)) ((bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
      ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ ω => Φ (bandGaussApprox (stableLikeLevy c Y) T
                (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω))
              (fun ℓ ω => Φ (bandGaussApprox (stableLikeLevy c Y) T
                (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω)))
              (fun p x => x p) ℓ (N ℓ) x -
                ∫ ω, Φ (X ω.1) ∂((bandInputLaw Λ M).prod (gaussianReal 0 1))) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ ω => Φ (bandGaussApprox (stableLikeLevy c Y) T
                (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω))
              (fun ℓ ω => Φ (bandGaussApprox (stableLikeLevy c Y) T
                (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω)))
              (fun p x => x p) ℓ (N ℓ) x -
                ∫ ω, Φ (X ω.1) ∂((bandInputLaw Λ M).prod (gaussianReal 0 1))) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1)) <
            ε ^ 2 ∧
          Integrable (fun x : ℕ × ℕ → (ℕ → ℕ × (ℕ → ℝ)) × ℝ => ∑ ℓ ∈ range (L + 1),
              ∑ n ∈ range (N ℓ), (1 + ∑ k ∈ range (ℓ + 1), (((x (ℓ, n)).1 k).1 : ℝ)))
            (Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1)) ∧
          ∫ x, ∑ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ),
              (1 + ∑ k ∈ range (ℓ + 1), (((x (ℓ, n)).1 k).1 : ℝ))
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => (bandInputLaw Λ M).prod (gaussianReal 0 1)) =
            ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * c * ((2 : ℝ) ^ (Y * (ℓ : ℝ)) - 1) / Y) ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * c * ((2 : ℝ) ^ (Y * (ℓ : ℝ)) - 1) / Y) ≤
            c₄ * complexityBound ((2 - Y) / 2) (2 - Y) Y ε := by
  have hsq := integrable_sq_stableLikeLevy hc hY2
  have hν : Integrable (fun z => min 1 (z ^ 2)) (stableLikeLevy c Y) :=
    hsq.mono' (by fun_prop) (ae_of_all _ fun z => by
      rw [Real.norm_of_nonneg (le_min zero_le_one (sq_nonneg z))]
      exact min_le_right _ _)
  have hT : (0 : ℝ) ≤ T := T.2
  obtain ⟨X, hXℓ, hPX, c₄, hc₄, h⟩ := levyGauss_theorem1 hν hsq.integrableOn T hY0 hY2
    (a := T * c / (2 - Y)) (b := T * c / Y)
    (fun ℓ => by
      rw [stableLike_small_sq hc hY2 ℓ]
      exact le_of_eq (by ring))
    (fun ℓ => by
      rw [stableLike_count hc hY0 ℓ]
      have h2 : (0 : ℝ) ≤ T * c / Y := by positivity
      have e : (T : ℝ) * (c * ((2 : ℝ) ^ (Y * (ℓ : ℝ)) - 1) / Y) =
          T * c / Y * (2 : ℝ) ^ (Y * (ℓ : ℝ)) - T * c / Y := by
        field_simp
      rw [e]
      linarith) hband hΦ
  refine ⟨X, fun ℓ => ⟨(hXℓ ℓ).1, ?_⟩, hPX, c₄, hc₄, fun ε hε hε1 => ?_⟩
  · rw [(hXℓ ℓ).2, stableLike_small_sq hc hY2 ℓ]
    ring
  · obtain ⟨L, N, hN, hint, hmse, hcI, hcE, hcost⟩ := h ε hε hε1
    have e : ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) *
        (1 + T * ((stableLikeLevy c Y) (levySet ((2 : ℝ)⁻¹ ^ ℓ))).toReal) =
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * c * ((2 : ℝ) ^ (Y * (ℓ : ℝ)) - 1) / Y) := by
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [stableLike_count hc hY0 ℓ]
      ring
    exact ⟨L, N, hN, hint, hmse, hcI, hcE.trans e, e.symm.le.trans hcost⟩

/-! ### Part 2: Gamma laws -/

/-- **Exponential moments near `0` determine a law** (Giles 2015, §6.2, p. 48, l. 2063–2064:
"directly simulate the increments of the Lévy process over a set of uniform timesteps", for the
increment laws of Table 6.3; used to identify the convolutions of Gamma and Variance-Gamma laws,
the laws of sums of increments).  If two probability laws on `ℝ` have equal exponential moments
`∫ e^{tx}` for all `|t| < s`, `s > 0`, finite for the first law (hence for both), they are equal:
their complex moment generating functions are analytic on the strip `|Re z| < s` and agree on the
real segment, hence on the strip, and on the imaginary axis they are the characteristic
functions. -/
theorem measure_eq_of_integral_exp_eq {μ₁ μ₂ : Measure ℝ} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {s : ℝ} (hs : 0 < s)
    (h₁ : ∀ t ∈ Set.Ioo (-s) s, Integrable (fun x => Real.exp (t * x)) μ₁)
    (h : ∀ t ∈ Set.Ioo (-s) s, ∫ x, Real.exp (t * x) ∂μ₁ = ∫ x, Real.exp (t * x) ∂μ₂) :
    μ₁ = μ₂ := by
  have h₂ : ∀ t ∈ Set.Ioo (-s) s, Integrable (fun x => Real.exp (t * x)) μ₂ := fun t ht =>
    Integrable.of_integral_ne_zero (by rw [← h t ht]; exact (integral_exp_pos (h₁ t ht)).ne')
  set U : Set ℂ := Complex.reLm ⁻¹' Set.Ioo (-s) s with hU
  have hsub : ∀ μ : Measure ℝ, (∀ t ∈ Set.Ioo (-s) s, Integrable (fun x => Real.exp (t * x)) μ) →
      U ⊆ {z | z.re ∈ interior (integrableExpSet id μ)} := fun μ hμ z hz =>
    interior_maximal (fun t ht => hμ t ht) isOpen_Ioo hz
  have hA₁ := (analyticOnNhd_complexMGF (X := id) (μ := μ₁)).mono (hsub μ₁ h₁)
  have hA₂ := (analyticOnNhd_complexMGF (X := id) (μ := μ₂)).mono (hsub μ₂ h₂)
  have hconn : IsPreconnected U :=
    ((convex_Ioo (-s) s).linear_preimage Complex.reLm).isPreconnected
  have h0 : (0 : ℂ) ∈ U := by
    show (0 : ℂ).re ∈ Set.Ioo (-s) s
    simp [hs]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), complexMGF id μ₁ z = complexMGF id μ₂ z := by
    have hpos : ∀ n : ℕ, 0 < s / ((n + 2 : ℕ) : ℝ) := fun n => by positivity
    have hT : Tendsto (fun n : ℕ => ((s / ((n + 2 : ℕ) : ℝ) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h1 := (tendsto_const_div_atTop_nhds_zero_nat s).comp (tendsto_add_atTop_nat 2)
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
        rw [Complex.ofReal_zero] at h2
        refine h2.congr fun n => ?_
        simp
      · exact Complex.ofReal_ne_zero.2 (hpos n).ne'
    refine hT.frequently (Frequently.of_forall fun n => ?_)
    rw [complexMGF_ofReal, complexMGF_ofReal]
    have hlt : s / ((n + 2 : ℕ) : ℝ) < s := by
      rw [div_lt_iff₀ (by positivity)]
      have : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by norm_cast; omega
      nlinarith
    exact congrArg _ (h _ ⟨by linarith [hpos n], hlt⟩)
  have heq := hA₁.eqOn_of_preconnected_of_frequently_eq hA₂ hconn h0 hfreq
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  refine heq ?_
  show ((t : ℂ) * Complex.I).re ∈ Set.Ioo (-s) s
  simp [hs]

/-- The exponential moments of a Gamma law (Giles 2015, §6.2, p. 48, Table 6.3, the VG column):
`∫ e^{tx} dΓ(a, r) = (r/(r − t))^a` for shape `a > 0`, rate `r > 0` and `t < r`. -/
lemma integral_exp_mul_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    ∫ x, Real.exp (t * x) ∂(gammaMeasure a r) = (r / (r - t)) ^ a := by
  have hrt : 0 < r - t := sub_pos.2 ht
  have hm : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have e1 : ∀ x, (gammaPDF a r x).toReal • Real.exp (t * x) =
      gammaPDFReal a r x * Real.exp (t * x) := fun x => by
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), smul_eq_mul]
  simp_rw [e1]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ici 0) (fun x hx => ?_),
    integral_Ici_eq_integral_Ioi]
  · rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x => r ^ a / Real.Gamma a *
      (x ^ (a - 1) * Real.exp (-((r - t) * x)))) (fun x hx => ?_)]
    · rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hrt,
        Real.div_rpow hr.le hrt.le, Real.div_rpow zero_le_one hrt.le, Real.one_rpow]
      have := Real.Gamma_pos_of_pos ha
      have : 0 < (r - t) ^ a := Real.rpow_pos_of_pos hrt a
      field_simp
    · simp only [gammaPDFReal, if_pos (le_of_lt (show 0 < x from hx))]
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
  · simp only [gammaPDFReal, if_neg (show ¬ (0 ≤ x) from hx), zero_mul]

/-- `e^{tx}` is integrable under `Γ(a, r)` for `t < r` (Giles 2015, §6.2, Table 6.3). -/
lemma integrable_exp_mul_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {t : ℝ}
    (ht : t < r) : Integrable (fun x => Real.exp (t * x)) (gammaMeasure a r) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_mul_gammaMeasure ha hr ht]
  exact (Real.rpow_pos_of_pos (div_pos hr (sub_pos.2 ht)) a).ne'

/-- **Gamma laws add their shapes** (Giles 2015, §6.2, p. 48, l. 2078–2079: "the increments of the
driving Lévy process for the coarse path can be obtained trivially by summing the increments for the
fine path", for the Gamma subordinator of the VG process): for shapes `a, b > 0` and a rate `r > 0`,
`Γ(a, r) ∗ Γ(b, r) = Γ(a + b, r)`. -/
theorem gammaMeasure_conv {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    gammaMeasure a r ∗ gammaMeasure b r = gammaMeasure (a + b) r := by
  have := isProbabilityMeasure_gammaMeasure ha hr
  have := isProbabilityMeasure_gammaMeasure hb hr
  have := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have hval : ∀ t ∈ Set.Ioo (-r) r, ∫ x, Real.exp (t * x) ∂(gammaMeasure a r ∗ gammaMeasure b r) =
      (r / (r - t)) ^ (a + b) := fun t ht => by
    rw [integral_exp_mul_conv, integral_exp_mul_gammaMeasure ha hr ht.2,
      integral_exp_mul_gammaMeasure hb hr ht.2, ← Real.rpow_add (div_pos hr (sub_pos.2 ht.2))]
  refine (measure_eq_of_integral_exp_eq hr
    (fun t ht => integrable_exp_mul_gammaMeasure (add_pos ha hb) hr ht.2) fun t ht => ?_).symm
  rw [hval t ht, integral_exp_mul_gammaMeasure (add_pos ha hb) hr ht.2]

/-- A Gamma variable is almost surely nonnegative (Giles 2015, §6.2, Table 6.3). -/
lemma ae_nonneg_gammaMeasure (a r : ℝ) : ∀ᵐ x ∂(gammaMeasure a r), 0 ≤ x := by
  rw [ae_iff]
  have e : {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 := by
    ext x
    simp
  rw [e, gammaMeasure, withDensity_apply _ measurableSet_Iio, lintegral_gammaPDF_of_nonpos le_rfl]

/-! ### Part 2: the Variance-Gamma law as a difference of Gamma variables -/

/-- **The Variance-Gamma increment law as a difference of Gamma variables** (Giles 2015, §6.2,
p. 48, Table 6.3, l. 2056–2057, the VG column; l. 2063–2064: "directly simulate the increments of
the Lévy process over a set of uniform timesteps"): the law over a step `h` of
`bh + Γ⁺ − Γ⁻` with independent `Γ⁺ ∼ Gamma(Ch, rate M)` and `Γ⁻ ∼ Gamma(Ch, rate G)`, i.e.
`δ_{bh} ∗ Γ(Ch, M) ∗ (−Γ(Ch, G))`; the VG process with drift `b` and Lévy density
`C e^{−Mz}/z` on `z > 0`, `C e^{−G|z|}/|z|` on `z < 0`.  It is a probability law for
`C, G, M, h > 0`. -/
noncomputable def vgLaw (b C G M h : ℝ) : Measure ℝ :=
  Measure.dirac (b * h) ∗ (gammaMeasure (C * h) M ∗ (gammaMeasure (C * h) G).map (fun x => -x))

/-- The Variance-Gamma increment law is a probability law for `C, G, M, h > 0` (Giles 2015, §6.2,
Table 6.3). -/
lemma isProbabilityMeasure_vgLaw (b : ℝ) {C G M h : ℝ} (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hh : 0 < h) : IsProbabilityMeasure (vgLaw b C G M h) := by
  have := isProbabilityMeasure_gammaMeasure (mul_pos hC hh) hM
  have := isProbabilityMeasure_gammaMeasure (mul_pos hC hh) hG
  have : IsProbabilityMeasure ((gammaMeasure (C * h) G).map (fun x => -x)) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  unfold vgLaw
  infer_instance

/-- **The Variance-Gamma increments form a convolution semigroup** (Giles 2015, §6.2, p. 48,
l. 2078–2079: "the increments of the driving Lévy process for the coarse path can be obtained
trivially by summing the increments for the fine path").  For `C, G, M > 0` and steps
`h₁, h₂ > 0`, `vgLaw b C G M h₁ ∗ vgLaw b C G M h₂ = vgLaw b C G M (h₁ + h₂)`. -/
theorem vgLaw_conv (b : ℝ) {C G M : ℝ} (hC : 0 < C) (hG : 0 < G) (hM : 0 < M) {h₁ h₂ : ℝ}
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    vgLaw b C G M h₁ ∗ vgLaw b C G M h₂ = vgLaw b C G M (h₁ + h₂) := by
  have := isProbabilityMeasure_gammaMeasure (mul_pos hC hh₁) hM
  have := isProbabilityMeasure_gammaMeasure (mul_pos hC hh₁) hG
  have := isProbabilityMeasure_gammaMeasure (mul_pos hC hh₂) hM
  have := isProbabilityMeasure_gammaMeasure (mul_pos hC hh₂) hG
  have hL : ((negAddMonoidHom : ℝ →+ ℝ) : ℝ → ℝ) = fun x => -x := rfl
  have hN : (gammaMeasure (C * h₁) G).map (fun x => -x) ∗ (gammaMeasure (C * h₂) G).map
      (fun x => -x) = (gammaMeasure (C * (h₁ + h₂)) G).map (fun x => -x) := by
    rw [← hL, ← Measure.map_conv_addMonoidHom _ measurable_neg,
      gammaMeasure_conv (mul_pos hC hh₁) (mul_pos hC hh₂) hG, mul_add]
  unfold vgLaw
  rw [measure_conv_conv_comm, Measure.dirac_conv_dirac, measure_conv_conv_comm,
    gammaMeasure_conv (mul_pos hC hh₁) (mul_pos hC hh₂) hM, hN, mul_add, mul_add]

/-- **The exponential moments of the Variance-Gamma increments** (Giles 2015, §6.2, p. 48,
Table 6.3, l. 2056–2057: "VG NIG α-stable / Asian O(h²) O(h²) O(h²)", the VG column; the
exponential Lévy model `S = s₀ e^X` needs `E e^{2X} < ∞`): for `C, G, M, h > 0` and
`−G < θ < M`, `e^{θx}` is integrable under `vgLaw b C G M h` and
`∫ e^{θx} d(vgLaw b C G M h) = e^{θbh} (M/(M − θ))^{Ch} (G/(G + θ))^{Ch}`; in particular
`E e^{2X_h} < ∞` when `M > 2`. -/
theorem integral_exp_mul_vgLaw (b : ℝ) {C G M h : ℝ} (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hh : 0 < h) {θ : ℝ} (hθG : -G < θ) (hθM : θ < M) :
    Integrable (fun x => Real.exp (θ * x)) (vgLaw b C G M h) ∧
      ∫ x, Real.exp (θ * x) ∂vgLaw b C G M h =
        Real.exp (θ * (b * h)) * (M / (M - θ)) ^ (C * h) * (G / (G + θ)) ^ (C * h) := by
  have := isProbabilityMeasure_gammaMeasure (mul_pos hC hh) hM
  have := isProbabilityMeasure_gammaMeasure (mul_pos hC hh) hG
  have hval : ∫ x, Real.exp (θ * x) ∂vgLaw b C G M h =
      Real.exp (θ * (b * h)) * (M / (M - θ)) ^ (C * h) * (G / (G + θ)) ^ (C * h) := by
    unfold vgLaw
    rw [integral_exp_mul_conv, integral_exp_mul_conv, integral_dirac,
      integral_exp_mul_gammaMeasure (mul_pos hC hh) hM hθM,
      integral_map measurable_neg.aemeasurable (by fun_prop)]
    have e : ∀ x : ℝ, Real.exp (θ * -x) = Real.exp ((-θ) * x) := fun x => by ring_nf
    simp_rw [e]
    rw [integral_exp_mul_gammaMeasure (mul_pos hC hh) hG (by linarith), sub_neg_eq_add, mul_assoc]
  refine ⟨Integrable.of_integral_ne_zero ?_, hval⟩
  rw [hval]
  have h1 : 0 < (M / (M - θ)) ^ (C * h) := Real.rpow_pos_of_pos (div_pos hM (by linarith)) _
  have h2 : 0 < (G / (G + θ)) ^ (C * h) := Real.rpow_pos_of_pos (div_pos hG (by linarith)) _
  positivity

/-- **Theorem 1 for the Asian option of an exponential Variance-Gamma model** (Giles 2015, §6.2,
p. 48, Table 6.3, l. 2056–2057: "VG … Asian O(h²)"; l. 2063–2069: "directly simulate the
increments of the Lévy process over a set of uniform timesteps (Schoutens 2003), in exactly the
same way as one simulates Brownian increments …  multilevel is still very useful for path-dependent
financial options such as Asian, lookback and barrier options"; Theorem 1 and (2.4), §2.1).  For
the VG process with drift `b` and parameters `C, G > 0`, `M > 2` (so that `E e^{2X_T} < ∞`), a
horizon `T > 0`, the price `S = s₀ e^X` and a `K`-Lipschitz payoff `g` of the trapezoidal average,
level `ℓ` simulates the exact VG increments over the steps `h_ℓ = T 2^{−ℓ}`
(law `vgLaw b C G M h_ℓ`) and the coarse path sums pairs of fine increments.  Then the level
expectations converge to some `P` at the rate `|E[P_ℓ] − P| ≤ c 2^{−ℓ}`, and the MLMC estimator of
`P` has a square-integrable error with mean square `< ε²` at cost `∑_ℓ N_ℓ 2^ℓ ≤ c₄ ε⁻²`
(`β = 2` from `V_ℓ = O(h_ℓ²)`, the Table 6.3 entry, and `γ = 1`).  No hypothesis is left: the
convolution identity and the exponential moment are proved.  As for `levy_asian_theorem1`, `P` is
the limit of the level expectations (the continuous-time average is not formalised). -/
theorem vg_asian_theorem1 (b : ℝ) {C G M : ℝ} (hC : 0 < C) (hG : 0 < G) (hM : 2 < M) {T : ℝ}
    (hT : 0 < T) {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (s₀ : ℝ) :
    ∃ P : ℝ, Filter.Tendsto (fun ℓ => ∫ y, g (levyAsianTrap s₀ (2 ^ ℓ) y)
        ∂(Measure.infinitePi fun _ : ℕ => vgLaw b C G M (T / 2 ^ ℓ))) Filter.atTop
        (nhds P) ∧
      (∃ c : ℝ, ∀ ℓ : ℕ, |∫ y, g (levyAsianTrap s₀ (2 ^ ℓ) y)
        ∂(Measure.infinitePi fun _ : ℕ => vgLaw b C G M (T / 2 ^ ℓ)) - P| ≤ c / 2 ^ ℓ) ∧
      ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ)))
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))))
              (fun p x => x p) ℓ (N ℓ) x - P) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ =>
              Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ =>
                vgLaw b C G M (T / 2 ^ ℓ)) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ)))
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))))
              (fun p x => x p) ℓ (N ℓ) x - P) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ =>
              Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ =>
                vgLaw b C G M (T / 2 ^ ℓ)) < ε ^ 2 ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  have hM0 : 0 < M := by linarith
  have hP : ∀ ℓ : ℕ, IsProbabilityMeasure (vgLaw b C G M (T / 2 ^ ℓ)) := fun ℓ =>
    isProbabilityMeasure_vgLaw b hC hG hM0 (by positivity)
  have hconv : ∀ ℓ : ℕ, vgLaw b C G M (T / 2 ^ (ℓ + 1)) ∗ vgLaw b C G M (T / 2 ^ (ℓ + 1)) =
      vgLaw b C G M (T / 2 ^ ℓ) := fun ℓ => by
    rw [vgLaw_conv b hC hG hM0 (by positivity) (by positivity)]
    congr 1
    rw [pow_succ]
    field_simp
    ring
  exact levy_asian_theorem1 (fun ℓ => vgLaw b C G M (T / 2 ^ ℓ)) hconv
    (integral_exp_mul_vgLaw b hC hG hM0 (by positivity) (by linarith) hM).1 hg s₀

/-- The variance of the Asian multilevel correction for level laws with exponential moments
`e^{hκ}` (Giles 2015, §6.2, p. 48, Table 6.3, l. 2057: "Asian O(h²)"): if the increment law
`ν_ℓ` over `h_ℓ = T 2^{−ℓ}`, `T > 0`, has `∫ e^x dν_ℓ = e^{h_ℓ κ₁}` and
`∫ e^{2x} dν_ℓ = e^{h_ℓ κ₂}`, then the correction of level `ℓ + 1` (the fine average over `2^{ℓ+1}`
steps minus the coarse one over the `2^ℓ` pair sums of the same increments) is in `L²` with
variance `≤ K² s₀² C h_{ℓ+1}²`, `C = levyAsianConst κ₁ κ₂ T` (by `levy_asian_payoff_sq_le`). -/
lemma levy_asian_variance_le_of_exp (ν : ℕ → Measure ℝ) [∀ ℓ, IsProbabilityMeasure (ν ℓ)]
    {T κ₁ κ₂ : ℝ} (hT : 0 < T)
    (h1 : ∀ ℓ : ℕ, ∫ x, Real.exp x ∂ν ℓ = Real.exp (T / 2 ^ ℓ * κ₁))
    (h2 : ∀ ℓ : ℕ, ∫ x, Real.exp (2 * x) ∂ν ℓ = Real.exp (T / 2 ^ ℓ * κ₂))
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (s₀ : ℝ) (ℓ : ℕ) :
    MemLp (fun y => g (levyAsianTrap s₀ (2 ^ (ℓ + 1)) y) -
        g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y))) 2
      (Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) ∧
    variance (fun y => g (levyAsianTrap s₀ (2 ^ (ℓ + 1)) y) -
        g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y)))
      (Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) ≤
      K ^ 2 * s₀ ^ 2 * levyAsianConst κ₁ κ₂ T * (T / 2 ^ (ℓ + 1)) ^ 2 := by
  have hev : ∀ i, MeasurePreserving (fun y : ℕ → ℝ => y i)
      (Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) (ν (ℓ + 1)) := fun i =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => ν (ℓ + 1)) i
  have hYind : iIndepFun (fun i (y : ℕ → ℝ) => y i)
      (Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => ν (ℓ + 1)) (X := fun _ => id) fun _ => measurable_id
  have hm1 : ∀ i, ∫ y, Real.exp (y i) ∂(Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) =
      Real.exp (T / 2 ^ (ℓ + 1) * κ₁) := fun i =>
    (integral_comp_of_measurePreserving (hev i) (f := Real.exp)
      Real.continuous_exp.aestronglyMeasurable).trans (h1 (ℓ + 1))
  have hm2 : ∀ i, ∫ y, Real.exp (2 * y i) ∂(Measure.infinitePi fun _ : ℕ => ν (ℓ + 1)) =
      Real.exp (T / 2 ^ (ℓ + 1) * κ₂) := fun i =>
    (integral_comp_of_measurePreserving (hev i) (f := fun x => Real.exp (2 * x))
      (by fun_prop)).trans (h2 (ℓ + 1))
  have hTn : 2 * ((2 ^ ℓ : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)) = T := by
    push_cast
    field_simp
    ring
  have h := levy_asian_payoff_sq_le (fun i => measurable_pi_apply i) hYind
    (h := T / 2 ^ (ℓ + 1)) (by positivity) hm1 hm2 hg s₀ (n := 2 ^ ℓ) (by positivity) hTn
  rw [pow_succ' 2 ℓ]
  exact ⟨h.1, h.2.2⟩

/-- **`V_ℓ = O(h_ℓ²)` for the Asian option of an exponential Variance-Gamma model** (Giles 2015,
§6.2, p. 48, Table 6.3, l. 2056–2057: "VG NIG α-stable / Asian O(h²) O(h²) O(h²)"; l. 2060–2061:
"convergence rates for the multilevel variance `V_ℓ ≡ V[P_ℓ − P_{ℓ−1}]` for Variance-Gamma";
l. 2063–2064: "directly simulate the increments of the Lévy process over a set of uniform
timesteps").  In the setting of `vg_asian_theorem1` (`C, G > 0`, `M > 2`, `T > 0`, a
`K`-Lipschitz payoff `g` of the trapezoidal average of `S = s₀ e^X`), there is a constant `c` such
that for every `ℓ` the multilevel correction of level `ℓ + 1`, as a function of its `VG`
increments over `h_{ℓ+1} = T 2^{−(ℓ+1)}` (the coarse path uses their pair sums), is in `L²` and
has variance `V_{ℓ+1} ≤ c h_{ℓ+1}²`. -/
theorem vg_asian_variance_le (b : ℝ) {C G M : ℝ} (hC : 0 < C) (hG : 0 < G) (hM : 2 < M) {T : ℝ}
    (hT : 0 < T) {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (s₀ : ℝ) :
    ∃ c : ℝ, ∀ ℓ : ℕ,
      MemLp (fun y => g (levyAsianTrap s₀ (2 ^ (ℓ + 1)) y) -
          g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y))) 2
        (Measure.infinitePi fun _ : ℕ => vgLaw b C G M (T / 2 ^ (ℓ + 1))) ∧
      variance (fun y => g (levyAsianTrap s₀ (2 ^ (ℓ + 1)) y) -
          g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y)))
        (Measure.infinitePi fun _ : ℕ => vgLaw b C G M (T / 2 ^ (ℓ + 1))) ≤
        c * (T / 2 ^ (ℓ + 1)) ^ 2 := by
  have hM0 : 0 < M := by linarith
  have hP : ∀ ℓ : ℕ, IsProbabilityMeasure (vgLaw b C G M (T / 2 ^ ℓ)) := fun ℓ =>
    isProbabilityMeasure_vgLaw b hC hG hM0 (by positivity)
  -- `∫ e^{θx} d(vgLaw b C G M h) = e^{h κ(θ)}`
  have hκ : ∀ θ : ℝ, -G < θ → θ < M → ∀ h : ℝ, 0 < h →
      ∫ x, Real.exp (θ * x) ∂vgLaw b C G M h =
        Real.exp (h * (θ * b + C * Real.log (M / (M - θ)) + C * Real.log (G / (G + θ)))) := by
    intro θ hθG hθM h hh
    rw [(integral_exp_mul_vgLaw b hC hG hM0 hh hθG hθM).2,
      Real.rpow_def_of_pos (div_pos hM0 (by linarith)),
      Real.rpow_def_of_pos (div_pos hG (by linarith)), ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h1 : ∀ ℓ : ℕ, ∫ x, Real.exp x ∂vgLaw b C G M (T / 2 ^ ℓ) = Real.exp (T / 2 ^ ℓ *
      (1 * b + C * Real.log (M / (M - 1)) + C * Real.log (G / (G + 1)))) := fun ℓ => by
    rw [← hκ 1 (by linarith) (by linarith) (T / 2 ^ ℓ) (by positivity)]
    simp only [one_mul]
  have h2 : ∀ ℓ : ℕ, ∫ x, Real.exp (2 * x) ∂vgLaw b C G M (T / 2 ^ ℓ) = Real.exp (T / 2 ^ ℓ *
      (2 * b + C * Real.log (M / (M - 2)) + C * Real.log (G / (G + 2)))) := fun ℓ =>
    hκ 2 (by linarith) hM (T / 2 ^ ℓ) (by positivity)
  exact ⟨_, levy_asian_variance_le_of_exp (fun ℓ => vgLaw b C G M (T / 2 ^ ℓ)) hT h1 h2 hg s₀⟩

/-! ### Part 2: the Variance-Gamma law as a Gamma-time-changed Brownian motion -/

/-- **The Variance-Gamma increment law as a time-changed Brownian motion** (Giles 2015, §6.2,
p. 48, Table 6.3, l. 2056–2057, the VG column; l. 2063–2064): the law over a step `h` of
`bh + θΓ + σ√Γ Z` with `Γ ∼ Gamma(h/κ, rate 1/κ)` (mean `h`, variance `κh`) and an independent
`Z ∼ N(0, 1)`: a Brownian motion with drift `θ` and volatility `σ`, evaluated at a Gamma time,
plus the drift `bh`.  It is a probability law for `κ, h > 0`. -/
noncomputable def vgSubLaw (b θ σ κ h : ℝ) : Measure ℝ :=
  Measure.dirac (b * h) ∗ ((gammaMeasure (h / κ) κ⁻¹).prod (gaussianReal 0 1)).map
    (fun p => θ * p.1 + σ * Real.sqrt p.1 * p.2)

/-- The time-changed Variance-Gamma increment law is a probability law for `κ, h > 0` (Giles 2015,
§6.2, Table 6.3). -/
lemma isProbabilityMeasure_vgSubLaw (b θ σ : ℝ) {κ h : ℝ} (hκ : 0 < κ) (hh : 0 < h) :
    IsProbabilityMeasure (vgSubLaw b θ σ κ h) := by
  have := isProbabilityMeasure_gammaMeasure (div_pos hh hκ) (inv_pos.2 hκ)
  have : IsProbabilityMeasure (((gammaMeasure (h / κ) κ⁻¹).prod (gaussianReal 0 1)).map
      (fun p => θ * p.1 + σ * Real.sqrt p.1 * p.2)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold vgSubLaw
  infer_instance

/-- The exponential moments of `θΓ + σ√Γ Z` (Giles 2015, §6.2, Table 6.3): conditioning on `Γ`,
`E[e^{u(θΓ + σ√Γ Z)} | Γ] = e^{(uθ + σ²u²/2)Γ}`, so for `uθ + σ²u²/2 < 1/κ` the moment is finite
and equals `(κ⁻¹/(κ⁻¹ − (uθ + σ²u²/2)))^{h/κ}`. -/
lemma integral_exp_mul_vgSubCore {θ σ κ h : ℝ} (hκ : 0 < κ) (hh : 0 < h) {u : ℝ}
    (hu : u * θ + σ ^ 2 * u ^ 2 / 2 < κ⁻¹) :
    Integrable (fun x => Real.exp (u * x)) (((gammaMeasure (h / κ) κ⁻¹).prod
        (gaussianReal 0 1)).map (fun p => θ * p.1 + σ * Real.sqrt p.1 * p.2)) ∧
      ∫ x, Real.exp (u * x) ∂(((gammaMeasure (h / κ) κ⁻¹).prod (gaussianReal 0 1)).map
        (fun p => θ * p.1 + σ * Real.sqrt p.1 * p.2)) =
        (κ⁻¹ / (κ⁻¹ - (u * θ + σ ^ 2 * u ^ 2 / 2))) ^ (h / κ) := by
  have ha : 0 < h / κ := div_pos hh hκ
  have hr : 0 < κ⁻¹ := inv_pos.2 hκ
  have := isProbabilityMeasure_gammaMeasure ha hr
  set c := u * θ + σ ^ 2 * u ^ 2 / 2 with hc
  have hf : Measurable fun p : ℝ × ℝ => θ * p.1 + σ * Real.sqrt p.1 * p.2 := by fun_prop
  have hF : Measurable fun p : ℝ × ℝ => Real.exp (u * (θ * p.1 + σ * Real.sqrt p.1 * p.2)) := by
    fun_prop
  have e1 : ∀ g z : ℝ, Real.exp (u * (θ * g + σ * Real.sqrt g * z)) =
      Real.exp (u * θ * g) * Real.exp (u * σ * Real.sqrt g * z) := fun g z => by
    rw [← Real.exp_add]
    ring_nf
  have hinner : ∀ g : ℝ, ∫ z, Real.exp (u * (θ * g + σ * Real.sqrt g * z)) ∂(gaussianReal 0 1) =
      Real.exp (u * θ * g) * Real.exp ((u * σ * Real.sqrt g) ^ 2 / 2) := fun g => by
    simp_rw [e1 g]
    rw [integral_const_mul, integral_exp_mul_gaussianReal]
    congr 2
    push_cast
    ring
  have hinner' : ∀ᵐ g ∂(gammaMeasure (h / κ) κ⁻¹),
      ∫ z, Real.exp (u * (θ * g + σ * Real.sqrt g * z)) ∂(gaussianReal 0 1) =
        Real.exp (c * g) := by
    filter_upwards [ae_nonneg_gammaMeasure (h / κ) κ⁻¹] with g hg
    rw [hinner g, ← Real.exp_add, mul_pow, Real.sq_sqrt hg]
    congr 1
    rw [hc]
    ring
  have hI : Integrable (fun p : ℝ × ℝ => Real.exp (u * (θ * p.1 + σ * Real.sqrt p.1 * p.2)))
      ((gammaMeasure (h / κ) κ⁻¹).prod (gaussianReal 0 1)) := by
    refine (integrable_prod_iff hF.aestronglyMeasurable).2 ⟨ae_of_all _ fun g => ?_, ?_⟩
    · simp_rw [e1 g]
      exact (integrable_exp_mul_gaussianReal _).const_mul _
    · refine (integrable_exp_mul_gammaMeasure ha hr hu).congr ?_
      filter_upwards [hinner'] with g hg
      rw [← hg]
      congr 1
      funext z
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine ⟨?_, ?_⟩
  · rw [integrable_map_measure (by fun_prop) hf.aemeasurable]
    exact hI
  · rw [integral_map hf.aemeasurable (by fun_prop), integral_prod _ hI,
      integral_congr_ae hinner', integral_exp_mul_gammaMeasure ha hr hu]

/-- **The exponential moments of the time-changed Variance-Gamma increments** (Giles 2015, §6.2,
p. 48, Table 6.3, l. 2056–2057: "VG NIG α-stable / Asian O(h²) O(h²) O(h²)", the VG column;
l. 2063–2064: "directly simulate the increments of the Lévy process over a set of uniform
timesteps"; `E e^{2X} < ∞` is needed for the exponential model): for
`κ, h > 0` and `c = uθ + σ²u²/2 < 1/κ`, `e^{ux}` is integrable under `vgSubLaw b θ σ κ h` and
`∫ e^{ux} d(vgSubLaw b θ σ κ h) = e^{ubh} (κ⁻¹/(κ⁻¹ − c))^{h/κ} = e^{ubh} (1 − κc)^{−h/κ}`. -/
theorem integral_exp_mul_vgSubLaw (b : ℝ) {θ σ κ h : ℝ} (hκ : 0 < κ) (hh : 0 < h) {u : ℝ}
    (hu : u * θ + σ ^ 2 * u ^ 2 / 2 < κ⁻¹) :
    Integrable (fun x => Real.exp (u * x)) (vgSubLaw b θ σ κ h) ∧
      ∫ x, Real.exp (u * x) ∂(vgSubLaw b θ σ κ h) =
        Real.exp (u * (b * h)) * (κ⁻¹ / (κ⁻¹ - (u * θ + σ ^ 2 * u ^ 2 / 2))) ^ (h / κ) := by
  have := isProbabilityMeasure_gammaMeasure (div_pos hh hκ) (inv_pos.2 hκ)
  have hval : ∫ x, Real.exp (u * x) ∂(vgSubLaw b θ σ κ h) =
      Real.exp (u * (b * h)) * (κ⁻¹ / (κ⁻¹ - (u * θ + σ ^ 2 * u ^ 2 / 2))) ^ (h / κ) := by
    rw [vgSubLaw, integral_exp_mul_conv, integral_dirac, (integral_exp_mul_vgSubCore hκ hh hu).2]
  refine ⟨Integrable.of_integral_ne_zero ?_, hval⟩
  rw [hval]
  have hq : 0 < κ⁻¹ / (κ⁻¹ - (u * θ + σ ^ 2 * u ^ 2 / 2)) :=
    div_pos (inv_pos.2 hκ) (sub_pos.2 hu)
  have := Real.rpow_pos_of_pos hq (h / κ)
  positivity

/-- An explicit neighbourhood of `0` on which the time-changed VG moments are finite (Giles 2015,
§6.2, Table 6.3): if `|u| < min(1, κ⁻¹/(|θ| + σ² + 1))` then `uθ + σ²u²/2 < κ⁻¹`. -/
lemma vgSub_exponent_lt {θ σ κ : ℝ} {u : ℝ}
    (hu : |u| < min 1 (κ⁻¹ / (|θ| + σ ^ 2 + 1))) : u * θ + σ ^ 2 * u ^ 2 / 2 < κ⁻¹ := by
  have h1 : |u| < 1 := hu.trans_le (min_le_left _ _)
  have h2 : |u| < κ⁻¹ / (|θ| + σ ^ 2 + 1) := hu.trans_le (min_le_right _ _)
  have hd : 0 < |θ| + σ ^ 2 + 1 := by positivity
  rw [lt_div_iff₀ hd] at h2
  have h3 : u * θ ≤ |u| * |θ| := by
    rw [← abs_mul]
    exact le_abs_self _
  have h4 : u ^ 2 ≤ |u| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg u]
  have h5 : σ ^ 2 * u ^ 2 / 2 ≤ σ ^ 2 * |u| := by nlinarith [sq_nonneg σ, sq_nonneg u]
  nlinarith [abs_nonneg u, sq_nonneg σ, abs_nonneg θ]

/-- **The time-changed Variance-Gamma increments form a convolution semigroup** (Giles 2015, §6.2,
p. 48, l. 2078–2079: "the increments of the driving Lévy process for the coarse path can be obtained
trivially by summing the increments for the fine path").  For `κ > 0` and steps `h₁, h₂ > 0`,
`vgSubLaw b θ σ κ h₁ ∗ vgSubLaw b θ σ κ h₂ = vgSubLaw b θ σ κ (h₁ + h₂)`. -/
theorem vgSubLaw_conv (b θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) {h₁ h₂ : ℝ} (hh₁ : 0 < h₁)
    (hh₂ : 0 < h₂) :
    vgSubLaw b θ σ κ h₁ ∗ vgSubLaw b θ σ κ h₂ = vgSubLaw b θ σ κ (h₁ + h₂) := by
  have := isProbabilityMeasure_vgSubLaw b θ σ hκ hh₁
  have := isProbabilityMeasure_vgSubLaw b θ σ hκ hh₂
  have := isProbabilityMeasure_vgSubLaw b θ σ hκ (add_pos hh₁ hh₂)
  set s := min 1 (κ⁻¹ / (|θ| + σ ^ 2 + 1)) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos (inv_pos.2 hκ) (by positivity))
  have hc : ∀ u ∈ Set.Ioo (-s) s, u * θ + σ ^ 2 * u ^ 2 / 2 < κ⁻¹ := fun u hu =>
    vgSub_exponent_lt (abs_lt.2 hu)
  have hval : ∀ u ∈ Set.Ioo (-s) s, ∫ x, Real.exp (u * x)
      ∂(vgSubLaw b θ σ κ h₁ ∗ vgSubLaw b θ σ κ h₂) =
      Real.exp (u * (b * (h₁ + h₂))) *
        (κ⁻¹ / (κ⁻¹ - (u * θ + σ ^ 2 * u ^ 2 / 2))) ^ ((h₁ + h₂) / κ) := fun u hu => by
    have hq : 0 < κ⁻¹ / (κ⁻¹ - (u * θ + σ ^ 2 * u ^ 2 / 2)) :=
      div_pos (inv_pos.2 hκ) (sub_pos.2 (hc u hu))
    rw [integral_exp_mul_conv, (integral_exp_mul_vgSubLaw b hκ hh₁ (hc u hu)).2,
      (integral_exp_mul_vgSubLaw b hκ hh₂ (hc u hu)).2, add_div, Real.rpow_add hq, mul_add,
      mul_add, Real.exp_add]
    ring
  refine (measure_eq_of_integral_exp_eq hs0
    (fun u hu => (integral_exp_mul_vgSubLaw b hκ (add_pos hh₁ hh₂) (hc u hu)).1)
    fun u hu => ?_).symm
  rw [hval u hu, (integral_exp_mul_vgSubLaw b hκ (add_pos hh₁ hh₂) (hc u hu)).2]

/-- **The two descriptions of the Variance-Gamma law agree** (Giles 2015, §6.2, p. 48, Table 6.3,
l. 2056–2057: "VG NIG α-stable / Asian O(h²) O(h²) O(h²)", the VG column; l. 2060–2061:
"convergence rates for the multilevel variance `V_ℓ ≡ V[P_ℓ − P_{ℓ−1}]` for Variance-Gamma, NIG,
and spectrally-negative α-stable processes").  If `κ, G, M, h > 0`, `M⁻¹ − G⁻¹ = θκ` and
`(MG)⁻¹ = σ²κ/2` (for
`σ ≠ 0` these are solved by `M⁻¹, G⁻¹ = (√(θ²κ² + 2σ²κ) ± θκ)/2`), then the time-changed Brownian
increment is the difference of Gamma variables: `vgSubLaw b θ σ κ h = vgLaw b κ⁻¹ G M h`, since
`1 − κ(uθ + σ²u²/2) = (1 − u/M)(1 + u/G)`. -/
theorem vgSubLaw_eq_vgLaw (b : ℝ) {θ σ κ G M h : ℝ} (hκ : 0 < κ) (hG : 0 < G) (hM : 0 < M)
    (hh : 0 < h) (h1 : M⁻¹ - G⁻¹ = θ * κ) (h2 : (M * G)⁻¹ = σ ^ 2 * κ / 2) :
    vgSubLaw b θ σ κ h = vgLaw b κ⁻¹ G M h := by
  have hr : 0 < κ⁻¹ := inv_pos.2 hκ
  have := isProbabilityMeasure_vgSubLaw b θ σ hκ hh
  have := isProbabilityMeasure_vgLaw b hr hG hM hh
  have hs : 0 < min G M := lt_min hG hM
  -- the key identity `1 − κ (uθ + σ²u²/2) = (M − u)(G + u)/(MG)`
  have key : ∀ u : ℝ, 1 - κ * (u * θ + σ ^ 2 * u ^ 2 / 2) = (M - u) * (G + u) / (M * G) :=
    fun u => by
      have e : κ * (u * θ + σ ^ 2 * u ^ 2 / 2) = u * (M⁻¹ - G⁻¹) + u ^ 2 * (M * G)⁻¹ := by
        rw [h1, h2]
        ring
      rw [e]
      field_simp
      ring
  have hc : ∀ u ∈ Set.Ioo (-min G M) (min G M), u * θ + σ ^ 2 * u ^ 2 / 2 < κ⁻¹ ∧
      κ⁻¹ / (κ⁻¹ - (u * θ + σ ^ 2 * u ^ 2 / 2)) = M / (M - u) * (G / (G + u)) := by
    intro u hu
    have huG : -G < u := lt_of_le_of_lt (neg_le_neg (min_le_left G M)) hu.1
    have huM : u < M := lt_of_lt_of_le hu.2 (min_le_right G M)
    have hpos : 0 < (M - u) * (G + u) / (M * G) :=
      div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hM hG)
    have hk := key u
    have hκc : κ * (u * θ + σ ^ 2 * u ^ 2 / 2) < 1 := by linarith
    have hκi : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
    have hlt : u * θ + σ ^ 2 * u ^ 2 / 2 < κ⁻¹ := by nlinarith
    refine ⟨hlt, ?_⟩
    have hk2 : κ⁻¹ - (u * θ + σ ^ 2 * u ^ 2 / 2) = κ⁻¹ * ((M - u) * (G + u) / (M * G)) := by
      rw [← hk]
      field_simp
    have hMu : M - u ≠ 0 := by linarith
    have hGu : G + u ≠ 0 := by linarith
    rw [hk2]
    field_simp
  refine measure_eq_of_integral_exp_eq hs
    (fun u hu => (integral_exp_mul_vgSubLaw b hκ hh (hc u hu).1).1) fun u hu => ?_
  have huG : -G < u := lt_of_le_of_lt (neg_le_neg (min_le_left G M)) hu.1
  have huM : u < M := lt_of_lt_of_le hu.2 (min_le_right G M)
  rw [(integral_exp_mul_vgSubLaw b hκ hh (hc u hu).1).2,
    (integral_exp_mul_vgLaw b hr hG hM hh huG huM).2, (hc u hu).2,
    Real.mul_rpow (div_pos hM (by linarith)).le (div_pos hG (by linarith)).le,
    div_eq_inv_mul h κ]
  ring

/-- **Theorem 1 for the Asian option of an exponential Variance-Gamma model, `(θ, σ, κ)`
parameters** (Giles 2015, §6.2, p. 48, Table 6.3, l. 2056–2057: "VG … Asian O(h²)"; l. 2063–2068:
"directly simulate the increments of the Lévy process over a set of uniform timesteps (Schoutens
2003) … multilevel is still very useful for path-dependent financial options such as Asian";
Theorem 1 and (2.4), §2.1).  For the VG process `X_t = bt + θΓ_t + σ B_{Γ_t}` (`Γ` a Gamma process
with `E Γ_t = t`, `Var Γ_t = κt`, `B` a Brownian motion), with `κ > 0` and
`2θκ + 2σ²κ < 1` (exactly `E e^{2X_T} < ∞`), a horizon `T > 0`, `S = s₀ e^X` and a `K`-Lipschitz
payoff `g` of the trapezoidal average, level `ℓ` simulates the exact increments over the steps
`h_ℓ = T 2^{−ℓ}` (law `vgSubLaw b θ σ κ h_ℓ`).  Then the level expectations converge to some `P`
at the rate `|E[P_ℓ] − P| ≤ c 2^{−ℓ}`, and the MLMC estimator of `P` has a square-integrable error
with mean square `< ε²` at cost `∑_ℓ N_ℓ 2^ℓ ≤ c₄ ε⁻²`, with no assumption left (the convolution
identity and the exponential moment are proved).  As for `levy_asian_theorem1`, `P` is the limit
of the level expectations (the continuous-time average is not formalised). -/
theorem vgSub_asian_theorem1 (b θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hexp : 2 * θ * κ + 2 * σ ^ 2 * κ < 1) {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (s₀ : ℝ) :
    ∃ P : ℝ, Filter.Tendsto (fun ℓ => ∫ y, g (levyAsianTrap s₀ (2 ^ ℓ) y)
        ∂(Measure.infinitePi fun _ : ℕ => vgSubLaw b θ σ κ (T / 2 ^ ℓ))) Filter.atTop
        (nhds P) ∧
      (∃ c : ℝ, ∀ ℓ : ℕ, |∫ y, g (levyAsianTrap s₀ (2 ^ ℓ) y)
        ∂(Measure.infinitePi fun _ : ℕ => vgSubLaw b θ σ κ (T / 2 ^ ℓ)) - P| ≤ c / 2 ^ ℓ) ∧
      ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ)))
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))))
              (fun p x => x p) ℓ (N ℓ) x - P) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ =>
              Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ =>
                vgSubLaw b θ σ κ (T / 2 ^ ℓ)) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (w ℓ)))
              (fun ℓ w => g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum (w (ℓ + 1))))))
              (fun p x => x p) ℓ (N ℓ) x - P) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ =>
              Measure.infinitePi fun ℓ => Measure.infinitePi fun _ : ℕ =>
                vgSubLaw b θ σ κ (T / 2 ^ ℓ)) < ε ^ 2 ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  have hP : ∀ ℓ : ℕ, IsProbabilityMeasure (vgSubLaw b θ σ κ (T / 2 ^ ℓ)) := fun ℓ =>
    isProbabilityMeasure_vgSubLaw b θ σ hκ (by positivity)
  have hconv : ∀ ℓ : ℕ, vgSubLaw b θ σ κ (T / 2 ^ (ℓ + 1)) ∗ vgSubLaw b θ σ κ (T / 2 ^ (ℓ + 1)) =
      vgSubLaw b θ σ κ (T / 2 ^ ℓ) := fun ℓ => by
    rw [vgSubLaw_conv b θ σ hκ (by positivity) (by positivity)]
    congr 1
    rw [pow_succ]
    field_simp
    ring
  have hu : 2 * θ + σ ^ 2 * 2 ^ 2 / 2 < κ⁻¹ := by
    have hκi : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
    nlinarith
  exact levy_asian_theorem1 (fun ℓ => vgSubLaw b θ σ κ (T / 2 ^ ℓ)) hconv
    (integral_exp_mul_vgSubLaw b hκ (by positivity) hu).1 hg s₀

/-- **`V_ℓ = O(h_ℓ²)` for the Asian option of an exponential Variance-Gamma model, `(θ, σ, κ)`
parameters** (Giles 2015, §6.2, p. 48, Table 6.3, l. 2056–2057: "VG NIG α-stable / Asian O(h²)
O(h²) O(h²)"; l. 2060–2061: "convergence rates for the multilevel variance
`V_ℓ ≡ V[P_ℓ − P_{ℓ−1}]` for Variance-Gamma"; l. 2063–2064: "directly simulate the increments of
the Lévy process over a set of uniform timesteps").  In the setting of `vgSub_asian_theorem1`
(`κ > 0`, `2θκ + 2σ²κ < 1`, `T > 0`, a `K`-Lipschitz payoff `g` of the trapezoidal average of
`S = s₀ e^X`), there is a constant `c` such that for every `ℓ` the multilevel correction of level
`ℓ + 1`, as a function of its increments over `h_{ℓ+1} = T 2^{−(ℓ+1)}` (the coarse path uses their
pair sums), is in `L²` and has variance `V_{ℓ+1} ≤ c h_{ℓ+1}²`. -/
theorem vgSub_asian_variance_le (b θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hexp : 2 * θ * κ + 2 * σ ^ 2 * κ < 1) {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (s₀ : ℝ) :
    ∃ c : ℝ, ∀ ℓ : ℕ,
      MemLp (fun y => g (levyAsianTrap s₀ (2 ^ (ℓ + 1)) y) -
          g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y))) 2
        (Measure.infinitePi fun _ : ℕ => vgSubLaw b θ σ κ (T / 2 ^ (ℓ + 1))) ∧
      variance (fun y => g (levyAsianTrap s₀ (2 ^ (ℓ + 1)) y) -
          g (levyAsianTrap s₀ (2 ^ ℓ) (levyPairSum y)))
        (Measure.infinitePi fun _ : ℕ => vgSubLaw b θ σ κ (T / 2 ^ (ℓ + 1))) ≤
        c * (T / 2 ^ (ℓ + 1)) ^ 2 := by
  have hP : ∀ ℓ : ℕ, IsProbabilityMeasure (vgSubLaw b θ σ κ (T / 2 ^ ℓ)) := fun ℓ =>
    isProbabilityMeasure_vgSubLaw b θ σ hκ (by positivity)
  have hκi : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
  -- `∫ e^{ux} d(vgSubLaw b θ σ κ h) = e^{h κ(u)}`
  have hκu : ∀ u : ℝ, u * θ + σ ^ 2 * u ^ 2 / 2 < κ⁻¹ → ∀ h : ℝ, 0 < h →
      ∫ x, Real.exp (u * x) ∂vgSubLaw b θ σ κ h = Real.exp (h *
        (u * b + Real.log (κ⁻¹ / (κ⁻¹ - (u * θ + σ ^ 2 * u ^ 2 / 2))) / κ)) := by
    intro u hu h hh
    rw [(integral_exp_mul_vgSubLaw b hκ hh hu).2,
      Real.rpow_def_of_pos (div_pos (inv_pos.2 hκ) (sub_pos.2 hu)), ← Real.exp_add]
    congr 1
    field_simp
  have hu1 : 1 * θ + σ ^ 2 * 1 ^ 2 / 2 < κ⁻¹ := by
    nlinarith [mul_nonneg (sq_nonneg σ) hκ.le]
  have hu2 : 2 * θ + σ ^ 2 * 2 ^ 2 / 2 < κ⁻¹ := by
    nlinarith
  have h1 : ∀ ℓ : ℕ, ∫ x, Real.exp x ∂vgSubLaw b θ σ κ (T / 2 ^ ℓ) = Real.exp (T / 2 ^ ℓ *
      (1 * b + Real.log (κ⁻¹ / (κ⁻¹ - (1 * θ + σ ^ 2 * 1 ^ 2 / 2))) / κ)) := fun ℓ => by
    rw [← hκu 1 hu1 (T / 2 ^ ℓ) (by positivity)]
    simp only [one_mul]
  have h2 : ∀ ℓ : ℕ, ∫ x, Real.exp (2 * x) ∂vgSubLaw b θ σ κ (T / 2 ^ ℓ) = Real.exp (T / 2 ^ ℓ *
      (2 * b + Real.log (κ⁻¹ / (κ⁻¹ - (2 * θ + σ ^ 2 * 2 ^ 2 / 2))) / κ)) := fun ℓ =>
    hκu 2 hu2 (T / 2 ^ ℓ) (by positivity)
  exact ⟨_, levy_asian_variance_le_of_exp (fun ℓ => vgSubLaw b θ σ κ (T / 2 ^ ℓ)) hT h1 h2 hg s₀⟩

end MLMC
