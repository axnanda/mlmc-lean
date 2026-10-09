import MlmcLean.GBMMilstein

/-!
# Mean-square stability of the parabolic SPDE scheme (Giles 2015, §7.3)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §7.3
"Parabolic SPDE" (pp. 53–54), citing Giles and Reisinger (2012).  The SPDE
`dp = −μ ∂p/∂x dt + ½ ∂²p/∂x² dt − √ρ ∂p/∂x dM_t`, `x > 0`, "subject to boundary condition
`p(0, t) = 0`" (p. 53), is discretised (p. 54) by
`p^{n+1}_j = p^n_j − (μk + √(ρk) Z_n)/(2h) (p^n_{j+1} − p^n_{j−1})
  + ((1 − ρ)k + ρk Z_n²)/(2h²) (p^n_{j+1} − 2p^n_j + p^n_{j−1})`
"where `p^n_j ≈ p(jh, nk)`, and the `Z_n` are standard Normal random variables so that `√h Z_n`
corresponds to an increment of the driving scalar Brownian motion.  The multilevel
implementation is very straightforward.  As with the model parabolic example discussed
previously, `k_ℓ = k_{ℓ−1}/4` and `h_ℓ = h_{ℓ−1}/2` due to numerical stability considerations
which are analysed in the paper. … The computational cost increases by factor 8 on each level".

This file gives a von Neumann stability analysis of this scheme in mean square, with the same
`Z_n` for every grid point `j` (see *Deviations from the paper* below for how it relates to the
paper).  Write `λ = k/h²` and `s = sin(θ/2)`.

* `spdeStep`, `spdePath`: the scheme on sequences `ℤ → ℂ`, iterated with `Z_0, Z_1, …`;
  `spdeStep_eq_milstein`: it is the Milstein step with Brownian increment `ΔM_n = √k Z_n`.  The
  increment over a timestep `k` is `√k Z_n`, so the paper's "`√h Z_n`" is a slip for `√k Z_n`
  (`h` is the mesh width; in the SDE sections `h` is the timestep).
* `spdeStep_fourierMode`, `spdePath_fourierMode`: a Fourier mode `e^{ijθ}` is multiplied by the
  amplification factor `G(θ, Z) = 1 − 2λs²((1 − ρ) + ρZ²) − i(μk + √(ρk) Z) sin θ / h` per step,
  so after `n` steps by `∏_{m<n} G(θ, Z_m)`.
* `integral_normSq_spdeAmp`: for `Z ~ N(0,1)`,
  `E|G|² = 1 − 4λs²[(1 − ρ) + ρs² − λs²(1 + 2ρ²)] + 4λμ²k s²(1 − s²)`;
  `integral_normSq_spdePath`: with independent `Z_m`, `E|p^n_j|² = (E|G|²)ⁿ` for the mode.
* `integral_normSq_spdeAmp_le`, `spde_meanSquare_stable`: if `0 ≤ ρ ≤ 1` and `λ(1 + 2ρ²) ≤ 1`
  then `E|G|² ≤ 1 + μ²λk` for every `θ`, and the mean square of a mode after `n ≤ T/k` steps is
  at most `(1 + μ²λk)ⁿ ≤ exp(μ²λT)`, uniformly in `k` at fixed `λ`.
* `spde_meanSquare_stable_periodic`: the same bound for the discrete `ℓ²` norm of every
  `N`-periodic initial datum, `E ∑_{j<N} |p^n_j|² ≤ exp(μ²λT) ∑_{j<N} |p⁰_j|²` (discrete Fourier
  inversion `periodic_eq_sum_fourierMode` and Parseval identity `sum_normSq_sum_fourierMode`;
  the modes `θ_m = 2πm/N` share the noise `Z_n` but are orthogonal in `j`).
* `integral_normSq_spdeAmp_pi`, `spde_meanSquare_unstable`: `E|G(π, Z)|² = 1 + 4λ(λ(1 + 2ρ²) − 1)`,
  so if `λ(1 + 2ρ²) > 1` the mean square of the mode `(−1)^j` after `⌊T/k⌋` steps tends to `∞` as
  `k → 0` at fixed `λ`.
* `spde_level_refinement`, `spde_level_refinement_stable`, `spde_level_cost`,
  `spde_levels_stable`: with `h_ℓ = h_{ℓ−1}/2`, the ratio `λ` of level `ℓ − 1` is kept (or not
  exceeded) on level `ℓ` iff `k_ℓ = k_{ℓ−1}/4` (`k_ℓ ≤ k_{ℓ−1}/4`); if level `ℓ − 1` runs at the
  largest stable ratio `λ = 1/(1 + 2ρ²)`, level `ℓ` satisfies the stability condition iff
  `k_ℓ ≤ k_{ℓ−1}/4`; the cost `(X/h)(T/k)` grows by the factor 8; the levels
  `h_ℓ = h_0/2^ℓ`, `k_ℓ = k_0/4^ℓ` all satisfy the same bound `exp(μ²λT)`.
* `spdeStep_heat`, `norm_spdeStep_heat_le`: for `ρ = μ = 0` the scheme is the explicit heat step
  `heatStep` of §7.1 with ratio `k/(2h²)` (the SPDE has `½ ∂²p/∂x²`), and the condition
  `λ(1 + 2ρ²) ≤ 1` becomes `λ ≤ 1`, i.e. `k/(2h²) ≤ ½`, the condition of `abs_heatStep_le`.
  Conversely, for `ρ = μ = 0` the factor `G(π, Z) = 1 − 2λ = 1 − 4 · k/(2h²)` is the factor
  `1 − 4λ'` of the alternating mode in `heatStep_alternating` (`λ' = k/(2h²)`), so the
  instability `λ > 1` of `spde_meanSquare_unstable` is the instability `λ' > ½` of §7.1.  For
  `ρ > 0` the maximum-principle argument of §7.1 is not available (the coefficient
  `1 − ((1 − ρ)k + ρkZ²)/h²` of `p^n_j` is negative for large `|Z|`), hence the mean-square
  analysis.

**Deviations from the paper.**
* *Whole-line (or periodic) modes instead of the half-line problem.*  The paper's SPDE lives on
  `x > 0` with `p(0, t) = 0`.  The mode results (`spdeStep_fourierMode` to `spde_levels_stable`)
  are on the whole grid `ℤ`, and `spde_meanSquare_stable_periodic` and
  `integral_sum_normSq_spdePath_periodic` are on `N`-periodic data.  This is the standard von
  Neumann analysis: it ignores the boundary, and for the half-line Dirichlet problem it gives a
  necessary-type condition (modes localised away from `x = 0` behave as on `ℤ`); that
  localisation argument is not formalised here.
* *The stability condition is derived here.*  Giles (2015) states no stability condition; it only
  says that the refinement is due to "numerical stability considerations which are analysed in
  the paper", i.e. Giles and Reisinger (2012), which is not available here.  The formula for
  `E|G|²` and the condition `λ(1 + 2ρ²) ≤ 1` are derived in this file from the scheme as printed
  on p. 54; they have not been checked against the cited paper.
* *Paper slip.*  "`√h Z_n`" should read "`√k Z_n`" (`spdeStep_eq_milstein`).
* *Degenerate mesh `h = 0`.*  Lean's convention `x/0 = 0` gives `λ = k/h² = 0` and
  `sin θ/h = 0`, so the scheme is the identity and `G = 1`, and the statements hold trivially.
  The meaningful case is `h ≠ 0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace MLMC

/-! ### The scheme -/

/-- One step of the scheme of Giles 2015, §7.3, p. 54, on a sequence `p : ℤ → ℂ` (grid index `j`),
with mesh width `h`, timestep `k`, drift `μ`, correlation `ρ` and the normal sample `z = Z_n`
(the same for every `j`):
`p_j − (μk + √(ρk) z)/(2h) (p_{j+1} − p_{j−1})
  + ((1 − ρ)k + ρkz²)/(2h²) (p_{j+1} − 2p_j + p_{j−1})`. -/
noncomputable def spdeStep (mu rho k h z : ℝ) (p : ℤ → ℂ) (j : ℤ) : ℂ :=
  p j - (((mu * k + Real.sqrt (rho * k) * z) / (2 * h) : ℝ) : ℂ) * (p (j + 1) - p (j - 1))
    + ((((1 - rho) * k + rho * k * z ^ 2) / (2 * h ^ 2) : ℝ) : ℂ) *
      (p (j + 1) - 2 * p j + p (j - 1))

/-- The scheme of Giles 2015, §7.3, p. 54, iterated: `p^0 = p₀` and `p^{n+1} = spdeStep(Z_n, p^n)`,
driven by the sequence `Z = (Z_0, Z_1, …)` of normal samples. -/
noncomputable def spdePath (mu rho k h : ℝ) (p₀ : ℤ → ℂ) (Z : ℕ → ℝ) : ℕ → ℤ → ℂ
  | 0 => p₀
  | n + 1 => spdeStep mu rho k h (Z n) (spdePath mu rho k h p₀ Z n)

/-- The Fourier mode `j ↦ e^{ijθ}` of the von Neumann analysis behind Giles 2015, §7.3, p. 54
("numerical stability considerations which are analysed in the paper"). -/
noncomputable def fourierMode (θ : ℝ) (j : ℤ) : ℂ :=
  Complex.exp ((((j : ℝ) * θ : ℝ) : ℂ) * Complex.I)

/-- The amplification factor of the scheme of Giles 2015, §7.3, p. 54, for the mode `θ` and the
sample `z`: `G(θ, z) = 1 − 2λ sin²(θ/2) ((1 − ρ) + ρz²) − i (μk + √(ρk) z) sin θ / h`, with
`λ = k/h²`. -/
noncomputable def spdeAmp (mu rho k h θ z : ℝ) : ℂ :=
  ((1 - 2 * (k / h ^ 2) * Real.sin (θ / 2) ^ 2 * ((1 - rho) + rho * z ^ 2) : ℝ) : ℂ)
    - (((mu * k + Real.sqrt (rho * k) * z) * Real.sin θ / h : ℝ) : ℂ) * Complex.I

/-- **The scheme is the Milstein step with Brownian increment `√k Z_n`** (Giles 2015, §7.3, p. 54:
"A Milstein time discretisation with timestep `k` … the `Z_n` are standard Normal random variables
so that `√h Z_n` corresponds to an increment of the driving scalar Brownian motion").  For
`ρ, k ≥ 0`, with `ΔM = √k z`, the step equals
`p_j − (μk + √ρ ΔM) (p_{j+1} − p_{j−1})/(2h) + (k + ρ(ΔM² − k)) (p_{j+1} − 2p_j + p_{j−1})/(2h²)`,
i.e. the Euler terms `−μk D₁p + ½k D₂p − √ρ ΔM D₁p` of
`dp = −μ ∂p/∂x dt + ½ ∂²p/∂x² dt − √ρ ∂p/∂x dM` plus the Milstein correction
`½ρ (ΔM² − k) D₂p`.  So the increment of `M` over one timestep `k` is `√k Z_n` (variance `k`): the
paper's "`√h Z_n`" is a slip for `√k Z_n` (`h` is the mesh width here). -/
theorem spdeStep_eq_milstein {rho k : ℝ} (hρ : 0 ≤ rho) (hk : 0 ≤ k) (mu h z : ℝ) (p : ℤ → ℂ)
    (j : ℤ) :
    spdeStep mu rho k h z p j =
      p j - (((mu * k + Real.sqrt rho * (Real.sqrt k * z)) / (2 * h) : ℝ) : ℂ) *
          (p (j + 1) - p (j - 1))
        + (((k + rho * ((Real.sqrt k * z) ^ 2 - k)) / (2 * h ^ 2) : ℝ) : ℂ) *
          (p (j + 1) - 2 * p j + p (j - 1)) := by
  have e1 : (mu * k + Real.sqrt (rho * k) * z) / (2 * h) =
      (mu * k + Real.sqrt rho * (Real.sqrt k * z)) / (2 * h) := by
    rw [Real.sqrt_mul hρ]
    ring
  have e2 : ((1 - rho) * k + rho * k * z ^ 2) / (2 * h ^ 2) =
      (k + rho * ((Real.sqrt k * z) ^ 2 - k)) / (2 * h ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hk]
    ring
  rw [spdeStep, e1, e2]

/-! ### Fourier modes -/

/-- Shifting a Fourier mode by one grid point multiplies it by `e^{iθ} = cos θ + i sin θ`. -/
lemma fourierMode_add_one (θ : ℝ) (j : ℤ) :
    fourierMode θ (j + 1) =
      fourierMode θ j * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
  rw [fourierMode, fourierMode, Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Shifting a Fourier mode back by one grid point multiplies it by `e^{−iθ} = cos θ − i sin θ`. -/
lemma fourierMode_sub_one (θ : ℝ) (j : ℤ) :
    fourierMode θ (j - 1) =
      fourierMode θ j * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I) := by
  have e : (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I =
      Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast
    ring
  rw [e, fourierMode, fourierMode, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A Fourier mode has modulus one: `|e^{ijθ}|² = 1`. -/
lemma normSq_fourierMode (θ : ℝ) (j : ℤ) : Complex.normSq (fourierMode θ j) = 1 := by
  rw [Complex.normSq_eq_norm_sq, fourierMode, Complex.norm_exp_ofReal_mul_I, one_pow]

/-- The scheme is linear: it commutes with multiplication by a constant. -/
lemma spdeStep_const_mul (mu rho k h z : ℝ) (c : ℂ) (p : ℤ → ℂ) (j : ℤ) :
    spdeStep mu rho k h z (fun i => c * p i) j = c * spdeStep mu rho k h z p j := by
  rw [spdeStep, spdeStep]
  ring

/-- **The Fourier-mode identity** (von Neumann analysis behind Giles 2015, §7.3, p. 54: "numerical
stability considerations which are analysed in the paper").  The scheme maps the mode `e^{ijθ}`
to `G(θ, z) e^{ijθ}`, with
`G(θ, z) = 1 − 2λ sin²(θ/2) ((1 − ρ) + ρz²) − i (μk + √(ρk) z) sin θ / h` and `λ = k/h²`
(`spdeAmp`).  Here `p_{j+1} − p_{j−1} = 2i sin θ p_j` and
`p_{j+1} − 2p_j + p_{j−1} = −4 sin²(θ/2) p_j`.  The identity holds for all real parameters. -/
theorem spdeStep_fourierMode (mu rho k h z θ : ℝ) (j : ℤ) :
    spdeStep mu rho k h z (fourierMode θ) j = spdeAmp mu rho k h θ z * fourierMode θ j := by
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    rw [← Real.cos_two_mul_eq_one_sub]
    ring_nf
  rw [spdeStep, spdeAmp, fourierMode_add_one, fourierMode_sub_one, hc]
  push_cast
  ring

/-- **The `n`-step Fourier-mode identity** (von Neumann analysis behind Giles 2015, §7.3, p. 54:
"numerical stability considerations which are analysed in the paper").  Driven by
`Z_0, Z_1, …`, the scheme started from the mode `e^{ijθ}` gives
`p^n_j = (∏_{m<n} G(θ, Z_m)) e^{ijθ}`.  The identity holds for all real parameters. -/
theorem spdePath_fourierMode (mu rho k h θ : ℝ) (Z : ℕ → ℝ) (n : ℕ) (j : ℤ) :
    spdePath mu rho k h (fourierMode θ) Z n j =
      (∏ m ∈ range n, spdeAmp mu rho k h θ (Z m)) * fourierMode θ j := by
  induction n generalizing j with
  | zero => rw [spdePath, prod_range_zero, one_mul]
  | succ n ih =>
    have ih' : spdePath mu rho k h (fourierMode θ) Z n =
        fun i => (∏ m ∈ range n, spdeAmp mu rho k h θ (Z m)) * fourierMode θ i := funext ih
    rw [spdePath, ih', spdeStep_const_mul, spdeStep_fourierMode, prod_range_succ]
    ring

/-! ### The mean square of the amplification factor -/

/-- `|G(θ, z)|² = (Re G)² + (Im G)²` written out. -/
lemma normSq_spdeAmp (mu rho k h θ z : ℝ) :
    Complex.normSq (spdeAmp mu rho k h θ z) =
      (1 - 2 * (k / h ^ 2) * Real.sin (θ / 2) ^ 2 * ((1 - rho) + rho * z ^ 2)) ^ 2 +
        ((mu * k + Real.sqrt (rho * k) * z) * Real.sin θ / h) ^ 2 := by
  rw [spdeAmp, sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg, Complex.normSq_add_mul_I, neg_sq]

/-- `z ↦ |G(θ, z)|²` is measurable. -/
lemma measurable_normSq_spdeAmp (mu rho k h θ : ℝ) :
    Measurable fun z => Complex.normSq (spdeAmp mu rho k h θ z) := by
  have e : (fun z => Complex.normSq (spdeAmp mu rho k h θ z)) = fun z =>
      (1 - 2 * (k / h ^ 2) * Real.sin (θ / 2) ^ 2 * ((1 - rho) + rho * z ^ 2)) ^ 2 +
        ((mu * k + Real.sqrt (rho * k) * z) * Real.sin θ / h) ^ 2 :=
    funext (normSq_spdeAmp mu rho k h θ)
  rw [e]
  fun_prop

/-- `E[(a + bZ²)² + (c + dZ)²] = a² + 2ab + 3b² + c² + d²` for `Z ~ N(0,1)` (from `E Z = E Z³ = 0`,
`E Z² = 1`, `E Z⁴ = 3`). -/
lemma integral_sq_add_sq_gaussian (a b c d : ℝ) :
    ∫ z, ((a + b * z ^ 2) ^ 2 + (c + d * z) ^ 2) ∂gaussianReal 0 1 =
      a ^ 2 + 2 * a * b + 3 * b ^ 2 + c ^ 2 + d ^ 2 := by
  have e : (fun z : ℝ => (a + b * z ^ 2) ^ 2 + (c + d * z) ^ 2) = fun z =>
      (a ^ 2 + c ^ 2) + 2 * c * d * z + (2 * a * b + d ^ 2) * z ^ 2 + 0 * z ^ 3 +
        b ^ 2 * z ^ 4 := by
    funext z
    ring
  rw [e, integral_quartic_gaussian]
  ring

/-- `sin² θ = 4 sin²(θ/2) (1 − sin²(θ/2))`. -/
lemma sin_sq_eq_four_mul (θ : ℝ) :
    Real.sin θ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 * (1 - Real.sin (θ / 2) ^ 2) := by
  have h2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]
    ring_nf
  rw [h2, mul_pow, mul_pow, Real.cos_sq']
  ring

/-- **The mean square of the amplification factor** (von Neumann analysis behind Giles 2015, §7.3,
p. 54: "numerical stability considerations which are analysed in the paper").  For `Z ~ N(0,1)`,
`ρ ≥ 0`, `k ≥ 0`, `λ = k/h²` and `s = sin(θ/2)`:
`E|G(θ, Z)|² = 1 − 4λs²[(1 − ρ) + ρs² − λs²(1 + 2ρ²)] + 4λμ²k s²(1 − s²)`.
(Uses `E Z = E Z³ = 0`, `E Z² = 1`, `E Z⁴ = 3`; `ρ, k ≥ 0` make `√(ρk)² = ρk`.)  The paper does
not state this formula: it is derived here, since the analysis of Giles and Reisinger (2012) is
not available. -/
theorem integral_normSq_spdeAmp {rho k : ℝ} (hρ : 0 ≤ rho) (hk : 0 ≤ k) (mu h θ : ℝ) :
    ∫ z, Complex.normSq (spdeAmp mu rho k h θ z) ∂gaussianReal 0 1 =
      1 - 4 * (k / h ^ 2) * Real.sin (θ / 2) ^ 2 * ((1 - rho) + rho * Real.sin (θ / 2) ^ 2
          - k / h ^ 2 * Real.sin (θ / 2) ^ 2 * (1 + 2 * rho ^ 2))
        + 4 * (k / h ^ 2) * mu ^ 2 * k * Real.sin (θ / 2) ^ 2 * (1 - Real.sin (θ / 2) ^ 2) := by
  have hsin := sin_sq_eq_four_mul θ
  have hsq : Real.sqrt (rho * k) ^ 2 = rho * k := Real.sq_sqrt (mul_nonneg hρ hk)
  have e : (fun z => Complex.normSq (spdeAmp mu rho k h θ z)) = fun z =>
      ((1 - 2 * (k / h ^ 2) * Real.sin (θ / 2) ^ 2 * (1 - rho)) +
          (-(2 * (k / h ^ 2) * Real.sin (θ / 2) ^ 2 * rho)) * z ^ 2) ^ 2 +
        (mu * k * Real.sin θ / h + Real.sqrt (rho * k) * Real.sin θ / h * z) ^ 2 := by
    funext z
    rw [normSq_spdeAmp]
    ring
  rw [e, integral_sq_add_sq_gaussian]
  linear_combination ((mu * k) ^ 2 + Real.sqrt (rho * k) ^ 2) / h ^ 2 * hsin +
    4 * Real.sin (θ / 2) ^ 2 * (1 - Real.sin (θ / 2) ^ 2) / h ^ 2 * hsq

/-- **Mean-square stability, one step** (Giles 2015, §7.3, p. 54: "`k_ℓ = k_{ℓ−1}/4` and
`h_ℓ = h_{ℓ−1}/2` due to numerical stability considerations which are analysed in the paper").
If `0 ≤ ρ ≤ 1`, `k ≥ 0` and `λ(1 + 2ρ²) ≤ 1` with `λ = k/h²`, then `E|G(θ, Z)|² ≤ 1 + μ²λk` for
every `θ`.  Indeed the bracket in `integral_normSq_spdeAmp` is
`(1 − ρ)(1 − s²) + s²(1 − λ(1 + 2ρ²)) ≥ 0`, and `4s²(1 − s²) ≤ 1`.  The condition
`λ(1 + 2ρ²) ≤ 1` is derived here (Giles 2015 states none; Giles and Reisinger (2012) is not
available); `spde_meanSquare_unstable` shows that it is sharp at `θ = π`. -/
theorem integral_normSq_spdeAmp_le {mu rho k h : ℝ} (hρ0 : 0 ≤ rho) (hρ1 : rho ≤ 1)
    (hk : 0 ≤ k) (hlam : k / h ^ 2 * (1 + 2 * rho ^ 2) ≤ 1) (θ : ℝ) :
    ∫ z, Complex.normSq (spdeAmp mu rho k h θ z) ∂gaussianReal 0 1 ≤
      1 + mu ^ 2 * (k / h ^ 2) * k := by
  rw [integral_normSq_spdeAmp hρ0 hk]
  have hS0 : 0 ≤ Real.sin (θ / 2) ^ 2 := sq_nonneg _
  have hS1 : Real.sin (θ / 2) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  have hl : 0 ≤ k / h ^ 2 := div_nonneg hk (sq_nonneg h)
  have hb : 0 ≤ (1 - rho) * (1 - Real.sin (θ / 2) ^ 2) +
      Real.sin (θ / 2) ^ 2 * (1 - k / h ^ 2 * (1 + 2 * rho ^ 2)) :=
    add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hS0 (by linarith))
  have h1 := mul_nonneg (mul_nonneg hl hS0) hb
  have hq : 4 * Real.sin (θ / 2) ^ 2 * (1 - Real.sin (θ / 2) ^ 2) ≤ 1 := by
    nlinarith [sq_nonneg (2 * Real.sin (θ / 2) ^ 2 - 1)]
  have h2 := mul_le_mul_of_nonneg_left hq (mul_nonneg (mul_nonneg (sq_nonneg mu) hl) hk)
  nlinarith

/-- **The mean square of a Fourier mode after `n` steps** (von Neumann analysis behind Giles
2015, §7.3, p. 54: "numerical stability considerations which are analysed in the paper").  With
independent standard normal `Z_0, Z_1, …` (`stdNormalSeq`), the scheme started from `e^{ijθ}`
satisfies `E|p^n_j|² = E|∏_{m<n} G(θ, Z_m)|² = (E|G(θ, Z)|²)ⁿ`.  The mode lives on the whole
grid `ℤ`, not on the half line `x > 0` with `p(0, t) = 0` of the paper (von Neumann analysis). -/
theorem integral_normSq_spdePath (mu rho k h θ : ℝ) (n : ℕ) (j : ℤ) :
    ∫ Z, Complex.normSq (spdePath mu rho k h (fourierMode θ) Z n j) ∂stdNormalSeq =
      (∫ z, Complex.normSq (spdeAmp mu rho k h θ z) ∂gaussianReal 0 1) ^ n := by
  have e : (fun Z : ℕ → ℝ => Complex.normSq (spdePath mu rho k h (fourierMode θ) Z n j)) =
      fun Z => ∏ m ∈ range n, Complex.normSq (spdeAmp mu rho k h θ (Z m)) := by
    funext Z
    rw [spdePath_fourierMode, map_mul, normSq_fourierMode, mul_one, map_prod]
  rw [e]
  exact integral_prod_stdNormalSeq (measurable_normSq_spdeAmp mu rho k h θ) n

/-- **Mean-square stability over `n` steps, uniformly in `k` at fixed `λ`** (Giles 2015, §7.3,
p. 54: "`k_ℓ = k_{ℓ−1}/4` and `h_ℓ = h_{ℓ−1}/2` due to numerical stability considerations which
are analysed in the paper").  If `0 ≤ ρ ≤ 1`, `k ≥ 0` and `λ(1 + 2ρ²) ≤ 1` with `λ = k/h²`, then
for independent standard normal `Z_m` the scheme started from the mode `e^{ijθ}` satisfies, for
`nk ≤ T`, `E|p^n_j|² ≤ (1 + μ²λk)ⁿ ≤ exp(μ²λT)`: the bound depends on `λ`, `μ`, `T` only.
Deviations: the mode lives on the whole grid `ℤ`, not on the half line `x > 0` with
`p(0, t) = 0` of the paper (von Neumann analysis, a necessary-type condition for the half-line
problem); and the condition `λ(1 + 2ρ²) ≤ 1` is derived here, since Giles 2015 states none and
Giles and Reisinger (2012) is not available.  There is no hypothesis `h ≠ 0`: at `h = 0` the
coefficients `k/h²`, `·/(2h)` and `·/(2h²)` are `0` by Lean's division convention, the scheme is
the identity and both bounds read `1 ≤ 1`, so the statement is trivial there. -/
theorem spde_meanSquare_stable {mu rho k h T : ℝ} (hρ0 : 0 ≤ rho) (hρ1 : rho ≤ 1) (hk : 0 ≤ k)
    (hlam : k / h ^ 2 * (1 + 2 * rho ^ 2) ≤ 1) (θ : ℝ) {n : ℕ} (hT : n * k ≤ T) (j : ℤ) :
    ∫ Z, Complex.normSq (spdePath mu rho k h (fourierMode θ) Z n j) ∂stdNormalSeq ≤
        (1 + mu ^ 2 * (k / h ^ 2) * k) ^ n ∧
      (1 + mu ^ 2 * (k / h ^ 2) * k) ^ n ≤ Real.exp (mu ^ 2 * (k / h ^ 2) * T) := by
  have hl : 0 ≤ mu ^ 2 * (k / h ^ 2) := mul_nonneg (sq_nonneg mu) (div_nonneg hk (sq_nonneg h))
  have hx : 0 ≤ mu ^ 2 * (k / h ^ 2) * k := mul_nonneg hl hk
  refine ⟨?_, ?_⟩
  · rw [integral_normSq_spdePath]
    exact pow_le_pow_left₀ (integral_nonneg fun _ => Complex.normSq_nonneg _)
      (integral_normSq_spdeAmp_le hρ0 hρ1 hk hlam θ) n
  · have hexp := Real.add_one_le_exp (mu ^ 2 * (k / h ^ 2) * k)
    calc (1 + mu ^ 2 * (k / h ^ 2) * k) ^ n ≤ Real.exp (mu ^ 2 * (k / h ^ 2) * k) ^ n :=
          pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = Real.exp (mu ^ 2 * (k / h ^ 2) * (n * k)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
      _ ≤ Real.exp (mu ^ 2 * (k / h ^ 2) * T) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT hl)

/-! ### Instability -/

/-- **The mean square of the amplification factor of the mode `θ = π`** (von Neumann analysis
behind Giles 2015, §7.3, p. 54: "numerical stability considerations which are analysed in the
paper"): `E|G(π, Z)|² = 1 + 4λ(λ(1 + 2ρ²) − 1)` with `λ = k/h²`, for all real parameters (at
`θ = π`, `sin θ = 0` and `sin(θ/2) = 1`, so `G(π, Z) = 1 − 2λ((1 − ρ) + ρZ²)` is real). -/
theorem integral_normSq_spdeAmp_pi (mu rho k h : ℝ) :
    ∫ z, Complex.normSq (spdeAmp mu rho k h Real.pi z) ∂gaussianReal 0 1 =
      1 + 4 * (k / h ^ 2) * (k / h ^ 2 * (1 + 2 * rho ^ 2) - 1) := by
  have e : (fun z => Complex.normSq (spdeAmp mu rho k h Real.pi z)) = fun z =>
      ((1 - 2 * (k / h ^ 2) * (1 - rho)) + (-(2 * (k / h ^ 2) * rho)) * z ^ 2) ^ 2 +
        (0 + 0 * z) ^ 2 := by
    funext z
    rw [normSq_spdeAmp, Real.sin_pi, Real.sin_pi_div_two]
    ring
  rw [e, integral_sq_add_sq_gaussian]
  ring

/-- **Instability for `λ(1 + 2ρ²) > 1`** (Giles 2015, §7.3, p. 54: the refinement
`k_ℓ = k_{ℓ−1}/4`, `h_ℓ = h_{ℓ−1}/2` is "due to numerical stability considerations").  Fix
`λ` with `λ(1 + 2ρ²) > 1`, a time `T > 0`, and meshes `h(k)` with `k/h(k)² = λ`.  Then
`E|G(π, Z)|² = 1 + c` with `c = 4λ(λ(1 + 2ρ²) − 1) > 0` independent of `k`, and the mean square
of the mode `e^{ijπ} = (−1)^j` after `⌊T/k⌋` steps, `(1 + c)^{⌊T/k⌋}`, tends to `∞` as
`k → 0⁺`.  (No sign condition on `ρ` is needed here.)  Deviation: the mode `(−1)^j` lives on
the whole grid `ℤ`, not on the half line `x > 0` with `p(0, t) = 0` of the paper (von Neumann
analysis); the threshold `λ(1 + 2ρ²) = 1` is derived here, Giles and Reisinger (2012) not being
available. -/
theorem spde_meanSquare_unstable {mu rho lam T : ℝ} (hlam : 1 < lam * (1 + 2 * rho ^ 2))
    (hT : 0 < T) {mesh : ℝ → ℝ} (hmesh : ∀ k, 0 < k → k / mesh k ^ 2 = lam) (j : ℤ) :
    Tendsto (fun k => ∫ Z, Complex.normSq
        (spdePath mu rho k (mesh k) (fourierMode Real.pi) Z ⌊T / k⌋₊ j) ∂stdNormalSeq)
      (𝓝[>] 0) atTop := by
  have hl : 0 < lam := by
    by_contra hneg
    nlinarith [sq_nonneg rho]
  have hc : 1 < 1 + 4 * lam * (lam * (1 + 2 * rho ^ 2) - 1) := by
    have := mul_pos hl (sub_pos.mpr hlam)
    linarith
  have hdiv : Tendsto (fun k : ℝ => T / k) (𝓝[>] 0) atTop := by
    have h := Filter.Tendsto.const_mul_atTop hT (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
    refine h.congr fun k => ?_
    rw [div_eq_mul_inv]
  have hlim := (tendsto_pow_atTop_atTop_of_one_lt hc).comp
    ((tendsto_nat_floor_atTop (α := ℝ)).comp hdiv)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  rw [Function.comp_apply, Function.comp_apply, integral_normSq_spdePath,
    integral_normSq_spdeAmp_pi, hmesh k hk]

/-! ### The level hierarchy -/

/-- **Keeping `λ` forces `k_ℓ = k_{ℓ−1}/4`** (Giles 2015, §7.3, p. 54: "`k_ℓ = k_{ℓ−1}/4` and
`h_ℓ = h_{ℓ−1}/2` due to numerical stability considerations").  Let level `ℓ − 1` use the ratio
`λ = k_{ℓ−1}/h_{ℓ−1}²` and let `h_ℓ = h_{ℓ−1}/2`.  Then level `ℓ` does not exceed that ratio iff
`k_ℓ ≤ k_{ℓ−1}/4`, and keeps it iff `k_ℓ = k_{ℓ−1}/4`.  This is algebra about the ratio `k/h²`;
the link with stability, for the largest stable ratio, is `spde_level_refinement_stable`. -/
theorem spde_level_refinement {lam h₀ h₁ k₀ k₁ : ℝ} (hh : h₀ ≠ 0) (hh₁ : h₁ = h₀ / 2)
    (hk₀ : k₀ / h₀ ^ 2 = lam) :
    (k₁ / h₁ ^ 2 ≤ lam ↔ k₁ ≤ k₀ / 4) ∧ (k₁ / h₁ ^ 2 = lam ↔ k₁ = k₀ / 4) := by
  have hpos : 0 < h₀ ^ 2 := by positivity
  have e : k₁ / h₁ ^ 2 = 4 * k₁ / h₀ ^ 2 := by
    rw [hh₁]
    field_simp
    ring
  rw [e, ← hk₀]
  refine ⟨?_, ?_⟩
  · rw [div_le_div_iff_of_pos_right hpos]
    constructor <;> intro h <;> linarith
  · rw [div_left_inj' hpos.ne']
    constructor <;> intro h <;> linarith

/-- **At the largest stable ratio, stability on the next level forces `k_ℓ ≤ k_{ℓ−1}/4`** (Giles
2015, §7.3, p. 54: "`k_ℓ = k_{ℓ−1}/4` and `h_ℓ = h_{ℓ−1}/2` due to numerical stability
considerations which are analysed in the paper").  If level `ℓ − 1` runs at the largest
mean-square stable ratio, `λ(1 + 2ρ²) = 1` with `λ = k_{ℓ−1}/h_{ℓ−1}²`, and
`h_ℓ = h_{ℓ−1}/2`, then level `ℓ` satisfies the stability condition
`(k_ℓ/h_ℓ²)(1 + 2ρ²) ≤ 1` of `spde_meanSquare_stable` iff `k_ℓ ≤ k_{ℓ−1}/4`; for
`k_ℓ > k_{ℓ−1}/4` the ratio exceeds the threshold of `spde_meanSquare_unstable`.  The largest
admissible timestep is `k_ℓ = k_{ℓ−1}/4`.  (The hypothesis forces `h_{ℓ−1} ≠ 0`.) -/
theorem spde_level_refinement_stable {rho h₀ h₁ k₀ k₁ : ℝ} (hh₁ : h₁ = h₀ / 2)
    (hmax : k₀ / h₀ ^ 2 * (1 + 2 * rho ^ 2) = 1) :
    k₁ / h₁ ^ 2 * (1 + 2 * rho ^ 2) ≤ 1 ↔ k₁ ≤ k₀ / 4 := by
  have hh : h₀ ≠ 0 := by
    rintro rfl
    norm_num at hmax
  have ha : 0 < 1 + 2 * rho ^ 2 := by positivity
  have hpos : 0 < h₀ ^ 2 := by positivity
  have e : k₁ / h₁ ^ 2 * (1 + 2 * rho ^ 2) = 4 * k₁ * (1 + 2 * rho ^ 2) / h₀ ^ 2 := by
    rw [hh₁]
    field_simp
    ring
  have hk₀ : k₀ * (1 + 2 * rho ^ 2) = h₀ ^ 2 := by
    rw [div_mul_eq_mul_div, div_eq_one_iff_eq hpos.ne'] at hmax
    exact hmax
  rw [e, div_le_one₀ hpos, ← hk₀]
  constructor
  · intro h
    have h' : 4 * k₁ ≤ k₀ := le_of_mul_le_mul_right h ha
    linarith
  · intro h
    have h' : 4 * k₁ ≤ k₀ := by linarith
    nlinarith

/-- **The cost grows by the factor 8 per level** (Giles 2015, §7.3, p. 54: "The computational
cost increases by factor 8 on each level").  On `[0, X] × [0, T]` the cost per sample is the
number `X/h` of grid intervals times the number `T/k` of timesteps; halving `h` and quartering
`k` multiplies it by `8`. -/
theorem spde_level_cost (X T h k : ℝ) :
    X / (h / 2) * (T / (k / 4)) = 8 * (X / h * (T / k)) := by
  rw [div_div_eq_mul_div, div_div_eq_mul_div]
  ring

/-- **All levels are stable with one bound** (Giles 2015, §7.3, p. 54: "`k_ℓ = k_{ℓ−1}/4` and
`h_ℓ = h_{ℓ−1}/2`").  With `h_ℓ = h_0/2^ℓ`, `k_ℓ = k_0/4^ℓ`, `0 ≤ ρ ≤ 1`, `k_0 ≥ 0` and
`λ(1 + 2ρ²) ≤ 1` for `λ = k_0/h_0²`, every level has the ratio `λ`, so the mean square of a mode
after `n ≤ T/k_ℓ` steps on level `ℓ` is at most `exp(μ²λT)`, independently of `ℓ`. -/
theorem spde_levels_stable {mu rho k₀ h₀ T : ℝ} (hρ0 : 0 ≤ rho) (hρ1 : rho ≤ 1) (hk : 0 ≤ k₀)
    (hlam : k₀ / h₀ ^ 2 * (1 + 2 * rho ^ 2) ≤ 1) (θ : ℝ) (ℓ n : ℕ)
    (hT : n * (k₀ / 4 ^ ℓ) ≤ T) (j : ℤ) :
    ∫ Z, Complex.normSq (spdePath mu rho (k₀ / 4 ^ ℓ) (h₀ / 2 ^ ℓ) (fourierMode θ) Z n j)
        ∂stdNormalSeq ≤ Real.exp (mu ^ 2 * (k₀ / h₀ ^ 2) * T) := by
  have h4 : ((2 : ℝ) ^ ℓ) ^ 2 = 4 ^ ℓ := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have e : k₀ / 4 ^ ℓ / (h₀ / 2 ^ ℓ) ^ 2 = k₀ / h₀ ^ 2 := by
    rw [div_pow, h4, div_div_div_cancel_right₀ (pow_ne_zero ℓ four_ne_zero)]
  have hk' : 0 ≤ k₀ / 4 ^ ℓ := div_nonneg hk (by positivity)
  have h := spde_meanSquare_stable (mu := mu) hρ0 hρ1 hk' (by rw [e]; exact hlam) θ hT j
  rw [e] at h
  exact h.1.trans h.2

/-! ### Periodic data: mean-square stability in the discrete `ℓ²` norm -/

/-- On the naturals a Fourier mode is a power: `e^{ijθ} = (e^{iθ})^j`. -/
lemma fourierMode_natCast (θ : ℝ) (j : ℕ) :
    fourierMode θ j = Complex.exp ((θ : ℂ) * Complex.I) ^ j := by
  rw [fourierMode, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e^{ijθ} · conj(e^{ijθ'}) = e^{ij(θ − θ')}`. -/
lemma fourierMode_mul_conj (θ θ' : ℝ) (j : ℤ) :
    fourierMode θ j * (starRingEnd ℂ) (fourierMode θ' j) = fourierMode (θ - θ') j := by
  rw [fourierMode, fourierMode, fourierMode, ← Complex.exp_conj, ← Complex.exp_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- The discrete frequencies `θ_m = 2πm/N` are `N`-periodic modes:
`e^{i(j + N)θ_m} = e^{ijθ_m}`. -/
lemma fourierMode_add_period {N : ℕ} (hN : 0 < N) (m : ℕ) (j : ℤ) :
    fourierMode (2 * Real.pi * m / N) (j + N) = fourierMode (2 * Real.pi * m / N) j := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have e : ((((j + N : ℤ) : ℝ) * (2 * Real.pi * m / N) : ℝ) : ℂ) * Complex.I =
      ((((j : ℝ) * (2 * Real.pi * m / N) : ℝ) : ℂ) * Complex.I) +
        (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [fourierMode, fourierMode, e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- `e^{ijθ_m}` is symmetric in `j` and `m` for `θ_m = 2πm/N`. -/
lemma fourierMode_symm (N m j : ℕ) :
    fourierMode (2 * Real.pi * m / N) j = fourierMode (2 * Real.pi * j / N) m := by
  rw [fourierMode, fourierMode]
  congr 2
  push_cast
  ring

/-- **Discrete orthogonality**: for `m, m' < N`,
`∑_{j<N} e^{ijθ_m} conj(e^{ijθ_{m'}}) = N` if `m = m'` and `0` otherwise (`θ_m = 2πm/N`). -/
lemma sum_fourierMode_mul_conj {N : ℕ} (hN : 0 < N) {m m' : ℕ} (hm : m < N) (hm' : m' < N) :
    ∑ j ∈ range N, fourierMode (2 * Real.pi * m / N) j *
        (starRingEnd ℂ) (fourierMode (2 * Real.pi * m' / N) j) =
      if m = m' then (N : ℂ) else 0 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have e : ∀ j : ℕ, fourierMode (2 * Real.pi * m / N) j *
      (starRingEnd ℂ) (fourierMode (2 * Real.pi * m' / N) j) =
        Complex.exp (((2 * Real.pi * m / N - 2 * Real.pi * m' / N : ℝ) : ℂ) * Complex.I) ^ j :=
    fun j => by rw [fourierMode_mul_conj, fourierMode_natCast]
  rw [sum_congr rfl fun j _ => e j]
  split_ifs with hmm
  · subst hmm
    rw [sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    simp
  · have hw1 : Complex.exp (((2 * Real.pi * m / N - 2 * Real.pi * m' / N : ℝ) : ℂ) *
        Complex.I) ≠ 1 := by
      rw [Ne, Complex.exp_eq_one_iff]
      rintro ⟨n, hn⟩
      have him := congrArg Complex.im hn
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat,
        Complex.mul_re] at him
      have h1 : ((m : ℝ) - m') = n * N := by
        field_simp at him
        nlinarith [Real.pi_pos]
      have h2 : ((m : ℤ) - m') = n * N := by exact_mod_cast h1
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have : n * (N : ℤ) ≤ -N := by nlinarith
        omega
      · subst hn0
        omega
      · have : (N : ℤ) ≤ n * N := by nlinarith
        omega
    have hwN : Complex.exp (((2 * Real.pi * m / N - 2 * Real.pi * m' / N : ℝ) : ℂ) *
        Complex.I) ^ N = 1 := by
      have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      refine ⟨(m : ℤ) - m', ?_⟩
      push_cast
      field_simp
    rw [geom_sum_eq hw1, hwN, sub_self, zero_div]

/-- **Discrete Parseval identity**: for `θ_m = 2πm/N`,
`∑_{j<N} |∑_{m<N} c_m e^{ijθ_m}|² = N ∑_{m<N} |c_m|²`. -/
lemma sum_normSq_sum_fourierMode {N : ℕ} (hN : 0 < N) (c : ℕ → ℂ) :
    ∑ j ∈ range N, Complex.normSq (∑ m ∈ range N, c m * fourierMode (2 * Real.pi * m / N) j) =
      N * ∑ m ∈ range N, Complex.normSq (c m) := by
  apply Complex.ofReal_injective
  have key : ∀ j : ℕ, ((Complex.normSq (∑ m ∈ range N,
      c m * fourierMode (2 * Real.pi * m / N) j) : ℝ) : ℂ) =
        ∑ m ∈ range N, ∑ m' ∈ range N, c m * (starRingEnd ℂ) (c m') *
          (fourierMode (2 * Real.pi * m / N) j *
            (starRingEnd ℂ) (fourierMode (2 * Real.pi * m' / N) j)) := by
    intro j
    rw [← Complex.mul_conj, map_sum, sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun m' _ => ?_
    rw [map_mul]
    ring
  rw [Complex.ofReal_sum, sum_congr rfl fun j _ => key j, sum_comm]
  have inner : ∀ m ∈ range N, ∑ j ∈ range N, ∑ m' ∈ range N, c m * (starRingEnd ℂ) (c m') *
      (fourierMode (2 * Real.pi * m / N) j *
        (starRingEnd ℂ) (fourierMode (2 * Real.pi * m' / N) j)) =
      N * ((Complex.normSq (c m) : ℝ) : ℂ) := by
    intro m hm
    rw [sum_comm]
    have h2 : ∀ m' ∈ range N, ∑ j ∈ range N, c m * (starRingEnd ℂ) (c m') *
        (fourierMode (2 * Real.pi * m / N) j *
          (starRingEnd ℂ) (fourierMode (2 * Real.pi * m' / N) j)) =
        if m = m' then c m * (starRingEnd ℂ) (c m') * N else 0 := by
      intro m' hm'
      rw [← mul_sum, sum_fourierMode_mul_conj hN (mem_range.mp hm) (mem_range.mp hm')]
      split_ifs <;> ring
    rw [sum_congr rfl h2, sum_ite_eq, if_pos hm, Complex.mul_conj]
    ring
  rw [sum_congr rfl inner, ← mul_sum]
  push_cast
  ring

/-- An `N`-periodic function on `ℤ` is determined by its values on `0, …, N − 1`. -/
lemma periodic_eq_toNat_emod {N : ℕ} (hN : 0 < N) {f : ℤ → ℂ} (hf : ∀ j, f (j + N) = f j)
    (i : ℤ) : f i = f ((i % N).toNat : ℕ) := by
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Int.toNat_of_nonneg (Int.emod_nonneg i hN')]
  have h := (Function.Periodic.int_mul (f := f) (c := (N : ℤ)) hf (i / N)) (i % N)
  rw [← h]
  congr 1
  rw [mul_comm]
  exact (Int.emod_add_mul_ediv i N).symm

/-- **Discrete Fourier inversion**: an `N`-periodic `p : ℤ → ℂ` is the sum of its modes,
`p_j = ∑_{m<N} c_m e^{ijθ_m}` for every `j ∈ ℤ`, with `θ_m = 2πm/N` and
`c_m = N⁻¹ ∑_{l<N} p_l conj(e^{ilθ_m})`. -/
lemma periodic_eq_sum_fourierMode {N : ℕ} (hN : 0 < N) {p : ℤ → ℂ}
    (hp : ∀ j, p (j + N) = p j) (i : ℤ) :
    p i = ∑ m ∈ range N, ((N : ℂ)⁻¹ * ∑ j ∈ range N, p j *
      (starRingEnd ℂ) (fourierMode (2 * Real.pi * m / N) j)) *
        fourierMode (2 * Real.pi * m / N) i := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set f : ℤ → ℂ := fun i => ∑ m ∈ range N, ((N : ℂ)⁻¹ * ∑ j ∈ range N, p j *
      (starRingEnd ℂ) (fourierMode (2 * Real.pi * m / N) j)) *
        fourierMode (2 * Real.pi * m / N) i with hf
  have hfper : ∀ j, f (j + N) = f j := by
    intro j
    simp only [hf, fourierMode_add_period hN]
  show p i = f i
  rw [periodic_eq_toNat_emod hN hp i, periodic_eq_toNat_emod hN hfper i]
  have hlt : (i % N).toNat < N := by
    have h1 := Int.emod_lt_of_pos i (by exact_mod_cast hN : (0 : ℤ) < N)
    omega
  set i₀ := (i % N).toNat
  rw [hf]
  dsimp only
  have e : ∀ m ∈ range N, ((N : ℂ)⁻¹ * ∑ j ∈ range N, p j *
      (starRingEnd ℂ) (fourierMode (2 * Real.pi * m / N) j)) *
        fourierMode (2 * Real.pi * m / N) i₀ =
      (N : ℂ)⁻¹ * ∑ j ∈ range N, p j * (fourierMode (2 * Real.pi * i₀ / N) m *
        (starRingEnd ℂ) (fourierMode (2 * Real.pi * j / N) m)) := by
    intro m _
    rw [mul_assoc, sum_mul]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [fourierMode_symm N m i₀, fourierMode_symm N m j]
    ring
  rw [sum_congr rfl e, ← mul_sum, sum_comm]
  have e2 : ∀ j ∈ range N, ∑ m ∈ range N, p j * (fourierMode (2 * Real.pi * i₀ / N) m *
      (starRingEnd ℂ) (fourierMode (2 * Real.pi * j / N) m)) =
      if i₀ = j then p j * N else 0 := by
    intro j hj
    rw [← mul_sum, sum_fourierMode_mul_conj hN hlt (mem_range.mp hj)]
    split_ifs <;> ring
  rw [sum_congr rfl e2, sum_ite_eq, if_pos (mem_range.mpr hlt)]
  field_simp

/-- The scheme is linear: it commutes with finite sums. -/
lemma spdeStep_sum (mu rho k h z : ℝ) (s : Finset ℕ) (f : ℕ → ℤ → ℂ) (j : ℤ) :
    spdeStep mu rho k h z (fun i => ∑ m ∈ s, f m i) j = ∑ m ∈ s, spdeStep mu rho k h z (f m) j := by
  unfold spdeStep
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib, sum_add_distrib,
    sum_sub_distrib, ← mul_sum]

/-- The scheme started from a finite sum of Fourier modes `∑_m c_m e^{ijθ_m}` gives
`p^n_j = ∑_m c_m (∏_{i<n} G(θ_m, Z_i)) e^{ijθ_m}`. -/
lemma spdePath_sum_fourierMode (mu rho k h : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (θ : ℕ → ℝ)
    (Z : ℕ → ℝ) (n : ℕ) (j : ℤ) :
    spdePath mu rho k h (fun i => ∑ m ∈ s, c m * fourierMode (θ m) i) Z n j =
      ∑ m ∈ s, c m * (∏ i ∈ range n, spdeAmp mu rho k h (θ m) (Z i)) * fourierMode (θ m) j := by
  induction n generalizing j with
  | zero =>
    rw [spdePath]
    refine sum_congr rfl fun m _ => ?_
    rw [prod_range_zero, mul_one]
  | succ n ih =>
    have ih' : spdePath mu rho k h (fun i => ∑ m ∈ s, c m * fourierMode (θ m) i) Z n =
        fun i => ∑ m ∈ s, c m * (∏ i ∈ range n, spdeAmp mu rho k h (θ m) (Z i)) *
          fourierMode (θ m) i := funext ih
    rw [spdePath, ih', spdeStep_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [spdeStep_const_mul, spdeStep_fourierMode, prod_range_succ]
    ring

/-- `z ↦ |G(θ, z)|²` is integrable for `z ~ N(0,1)` (a quartic polynomial). -/
lemma integrable_normSq_spdeAmp (mu rho k h θ : ℝ) :
    Integrable (fun z => Complex.normSq (spdeAmp mu rho k h θ z)) (gaussianReal 0 1) := by
  have e : (fun z => Complex.normSq (spdeAmp mu rho k h θ z)) = fun z =>
      (1 - 2 * (k / h ^ 2) * Real.sin (θ / 2) ^ 2 * (1 - rho)) ^ 2 +
        (mu * k * Real.sin θ / h) ^ 2 +
        (2 * (mu * k * Real.sin θ / h) * (Real.sqrt (rho * k) * Real.sin θ / h)) * z +
        (2 * (1 - 2 * (k / h ^ 2) * Real.sin (θ / 2) ^ 2 * (1 - rho)) *
            (-(2 * (k / h ^ 2) * Real.sin (θ / 2) ^ 2 * rho)) +
          (Real.sqrt (rho * k) * Real.sin θ / h) ^ 2) * z ^ 2 + 0 * z ^ 3 +
        (-(2 * (k / h ^ 2) * Real.sin (θ / 2) ^ 2 * rho)) ^ 2 * z ^ 4 := by
    funext z
    rw [normSq_spdeAmp]
    ring
  rw [e]
  exact integrable_quartic_gaussian _ _ _ _ _

/-- **The mean square of the `ℓ²` norm for periodic data** (von Neumann analysis behind Giles
2015, §7.3, p. 54: "numerical stability considerations which are analysed in the paper").  For an
`N`-periodic initial datum `p⁰` with discrete Fourier coefficients
`c_m = N⁻¹ ∑_{l<N} p⁰_l conj(e^{ilθ_m})`, `θ_m = 2πm/N`, independent standard normal `Z_i` give
`E ∑_{j<N} |p^n_j|² = N ∑_{m<N} |c_m|² (E|G(θ_m, Z)|²)ⁿ`: although all modes share the noise
`Z_n`, their cross terms vanish after summing over `j` (orthogonality), so each mode contributes
its own mean-square growth.  No condition on the parameters is needed. -/
theorem integral_sum_normSq_spdePath_periodic (mu rho k h : ℝ) {N : ℕ} (hN : 0 < N)
    {p : ℤ → ℂ} (hp : ∀ j, p (j + N) = p j) (n : ℕ) :
    ∫ Z, ∑ j ∈ range N, Complex.normSq (spdePath mu rho k h p Z n j) ∂stdNormalSeq =
      N * ∑ m ∈ range N, Complex.normSq ((N : ℂ)⁻¹ * ∑ j ∈ range N, p j *
          (starRingEnd ℂ) (fourierMode (2 * Real.pi * m / N) j)) *
        (∫ z, Complex.normSq (spdeAmp mu rho k h (2 * Real.pi * m / N) z)
          ∂gaussianReal 0 1) ^ n := by
  set c : ℕ → ℂ := fun m => (N : ℂ)⁻¹ * ∑ j ∈ range N, p j *
      (starRingEnd ℂ) (fourierMode (2 * Real.pi * m / N) j)
  have hp' : p = fun i => ∑ m ∈ range N, c m * fourierMode (2 * Real.pi * m / N) i :=
    funext (periodic_eq_sum_fourierMode hN hp)
  have e : ∀ Z : ℕ → ℝ, ∑ j ∈ range N, Complex.normSq (spdePath mu rho k h p Z n j) =
      N * ∑ m ∈ range N, Complex.normSq (c m) *
        ∏ i ∈ range n, Complex.normSq (spdeAmp mu rho k h (2 * Real.pi * m / N) (Z i)) := by
    intro Z
    have e1 : ∀ j : ℕ, spdePath mu rho k h p Z n j = ∑ m ∈ range N,
        (c m * ∏ i ∈ range n, spdeAmp mu rho k h (2 * Real.pi * m / N) (Z i)) *
          fourierMode (2 * Real.pi * m / N) j := by
      intro j
      rw [hp', spdePath_sum_fourierMode]
    rw [sum_congr rfl fun j _ => congrArg Complex.normSq (e1 j),
      sum_normSq_sum_fourierMode hN]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [map_mul, map_prod]
  rw [funext e, integral_const_mul, integral_finsetSum]
  · congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, integral_prod_stdNormalSeq (measurable_normSq_spdeAmp _ _ _ _ _)]
  · intro m _
    exact (integrable_prod_stdNormalSeq (measurable_normSq_spdeAmp _ _ _ _ _)
      (integrable_normSq_spdeAmp _ _ _ _ _) n).const_mul _

/-- **Mean-square stability in the discrete `ℓ²` norm for all periodic data** (Giles 2015, §7.3,
p. 54: "`k_ℓ = k_{ℓ−1}/4` and `h_ℓ = h_{ℓ−1}/2` due to numerical stability considerations which
are analysed in the paper").  If `0 ≤ ρ ≤ 1`, `k ≥ 0` and `λ(1 + 2ρ²) ≤ 1` with `λ = k/h²`, then
for every `N`-periodic initial datum `p⁰` and independent standard normal `Z_i`, for `nk ≤ T`,
`E ∑_{j<N} |p^n_j|² ≤ (1 + μ²λk)ⁿ ∑_{j<N} |p⁰_j|² ≤ exp(μ²λT) ∑_{j<N} |p⁰_j|²`.
(Periodic boundary conditions replace the boundary condition `p(0, t) = 0` of the paper: the von
Neumann analysis is the analysis of the periodic problem; the discrete Fourier inversion and
Parseval identity reduce it to `integral_normSq_spdeAmp_le`.) -/
theorem spde_meanSquare_stable_periodic {mu rho k h T : ℝ} (hρ0 : 0 ≤ rho) (hρ1 : rho ≤ 1)
    (hk : 0 ≤ k) (hlam : k / h ^ 2 * (1 + 2 * rho ^ 2) ≤ 1) {N : ℕ} (hN : 0 < N) {p : ℤ → ℂ}
    (hp : ∀ j, p (j + N) = p j) {n : ℕ} (hT : n * k ≤ T) :
    ∫ Z, ∑ j ∈ range N, Complex.normSq (spdePath mu rho k h p Z n j) ∂stdNormalSeq ≤
        (1 + mu ^ 2 * (k / h ^ 2) * k) ^ n * ∑ j ∈ range N, Complex.normSq (p j) ∧
      (1 + mu ^ 2 * (k / h ^ 2) * k) ^ n * ∑ j ∈ range N, Complex.normSq (p j) ≤
        Real.exp (mu ^ 2 * (k / h ^ 2) * T) * ∑ j ∈ range N, Complex.normSq (p j) := by
  have hsum : 0 ≤ ∑ j ∈ range N, Complex.normSq (p j) :=
    sum_nonneg fun j _ => Complex.normSq_nonneg _
  refine ⟨?_, ?_⟩
  · set c : ℕ → ℂ := fun m => (N : ℂ)⁻¹ * ∑ j ∈ range N, p j *
        (starRingEnd ℂ) (fourierMode (2 * Real.pi * m / N) j)
    have hpar : ∑ j ∈ range N, Complex.normSq (p j) =
        N * ∑ m ∈ range N, Complex.normSq (c m) := by
      rw [← sum_normSq_sum_fourierMode hN c]
      refine sum_congr rfl fun j _ => ?_
      rw [← periodic_eq_sum_fourierMode hN hp]
    rw [integral_sum_normSq_spdePath_periodic mu rho k h hN hp n, hpar]
    calc (N : ℝ) * ∑ m ∈ range N, Complex.normSq (c m) *
          (∫ z, Complex.normSq (spdeAmp mu rho k h (2 * Real.pi * m / N) z)
            ∂gaussianReal 0 1) ^ n
        ≤ N * ∑ m ∈ range N, Complex.normSq (c m) * (1 + mu ^ 2 * (k / h ^ 2) * k) ^ n := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun m _ => ?_)
            (Nat.cast_nonneg (α := ℝ) N)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
            (integral_nonneg fun _ => Complex.normSq_nonneg _)
            (integral_normSq_spdeAmp_le hρ0 hρ1 hk hlam _) n) (Complex.normSq_nonneg _)
      _ = (1 + mu ^ 2 * (k / h ^ 2) * k) ^ n * (N * ∑ m ∈ range N, Complex.normSq (c m)) := by
          rw [← sum_mul]
          ring
  · exact mul_le_mul_of_nonneg_right
      (spde_meanSquare_stable (mu := mu) hρ0 hρ1 hk hlam 0 hT 0).2 hsum

/-! ### Comparison with the deterministic model problem of §7.1 -/

/-- **For `ρ = μ = 0` the scheme is the explicit heat step of §7.1** (Giles 2015, §7.3, p. 54: "As
with the model parabolic example discussed previously"): on real data,
`spdeStep 0 0 k h z u = heatStep (k/(2h²)) u` (the SPDE has the diffusion `½ ∂²p/∂x²`, the model
problem of §7.1 has `∂²u/∂x²`, hence the ratio `k/(2h²)`). -/
theorem spdeStep_heat (k h z : ℝ) (u : ℤ → ℝ) (j : ℤ) :
    spdeStep 0 0 k h z (fun i => (u i : ℂ)) j = (heatStep (k / (2 * h ^ 2)) u j : ℂ) := by
  rw [spdeStep, heatStep, zero_mul, Real.sqrt_zero]
  push_cast
  ring

/-- **The stability conditions agree for `ρ = μ = 0`** (Giles 2015, §7.1 and §7.3, p. 54): the
mean-square condition `λ(1 + 2ρ²) ≤ 1` becomes `k/h² ≤ 1`, i.e. `k/(2h²) ≤ ½`, which is the
condition of the discrete maximum principle `abs_heatStep_le` (Giles 2015, §7.1, p. 51:
"Keeping `k_ℓ/h_ℓ² = ¼` ensures the explicit numerical discretisation is stable on all levels";
§7.3, p. 54: "As with the model parabolic example discussed previously, `k_ℓ = k_{ℓ−1}/4` and
`h_ℓ = h_{ℓ−1}/2` due to numerical stability considerations").  Under it the step does not
increase the maximum norm of real data.  Conversely, for `ρ = μ = 0` the factor
`G(π, Z) = 1 − 2k/h² = 1 − 4λ'` with `λ' = k/(2h²)` is the factor of the alternating mode in
`heatStep_alternating`, and the instability `k/h² > 1` of `spde_meanSquare_unstable` is the
instability `λ' > ½` of §7.1. -/
theorem norm_spdeStep_heat_le {k h M : ℝ} (hk : 0 ≤ k) (hlam : k / h ^ 2 ≤ 1)
    (z : ℝ) {u : ℤ → ℝ} (hu : ∀ j, |u j| ≤ M) (j : ℤ) :
    ‖spdeStep 0 0 k h z (fun i => (u i : ℂ)) j‖ ≤ M := by
  have e : k / (2 * h ^ 2) = k / h ^ 2 / 2 := by
    rw [div_div, mul_comm]
  rw [spdeStep_heat, Complex.norm_real, Real.norm_eq_abs]
  refine abs_heatStep_le ?_ ?_ hu j
  · rw [e]
    exact div_nonneg (div_nonneg hk (sq_nonneg h)) two_pos.le
  · rw [e]
    linarith

end MLMC
