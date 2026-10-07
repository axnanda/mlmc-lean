import MlmcLean.ApplicationExtras
import MlmcLean.GBMMilstein
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The elliptic example of Giles 2015, §7.1: second-order accuracy of the finite differences

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §7.1 "Two
simple examples" (p. 49): "The equation is `d/dx (c(x) du/dx) = −50 Z²` on `0 < x < 1`, with
boundary data `u(0) = u(1) = 0`.  `Z` is a Normal random variable with zero mean and unit variance,
and `c(x) = 1 + a x` with `a` being a uniform random variable on the unit interval `(0, 1)`.  The
output quantity of interest is chosen to be `P = ∫₀¹ u(x) dx`. … Level `ℓ` uses a uniform grid with
spacing `h_ℓ = 2^{−(ℓ+1)}` … A simple second order central difference approximation is used
(equivalent to a finite element approximation with a 1-point quadrature).  The uniform second order
accuracy means that there is a constant `K` such that `|P − P_ℓ| < K h_ℓ²` and therefore we have
`α = 2`, `β = 4` …" (the sentence continues on p. 51 with `γ = 1` and the `O(ε^{−2})` complexity,
which are `pde_complexity` of `MlmcLean.PDEExamples`).

**The scheme.**  With `f = 50 Z²`, `h = 1/N` and the nodes `x_j = j h`, the scheme is
`U_0 = U_N = 0` and `(c(x_{j+½})(U_{j+1} − U_j) − c(x_{j−½})(U_j − U_{j−1}))/h² = −f` for
`0 < j < N` (`IsEllipticFD`); this is the conservative central difference that the one-point
(midpoint) finite elements produce (`isEllipticFD_iff_fe`, from `fe_eq_centralDiff` of
`MlmcLean.ApplicationExtras`).  The paper does not say how `P_ℓ` is computed from the grid values;
we take the trapezoidal rule `P_ℓ = h ((U_0 + U_N)/2 + ∑_{0<j<N} U_j)` (`ellipticFDOutput`),
which is also the exact integral of the piecewise-linear finite-element solution.  Level `ℓ` uses
`N = 2^{ℓ+1}` (`ellipticPl`).

**The proof.**  In one dimension the fluxes telescope exactly.  The exact flux is `c u′ = q − f x`
and the discrete flux `c(x_{i+½})(U_{i+1} − U_i)/h` is `D − f x_{i+½}` at the midpoints, so
`u′ = (q − f t)/c(t)` and the increments of `U` are the midpoint rule for it
(`integral_of_isEllipticSol`, `output_of_isEllipticFD`).  With the moments
`A_k = ∫₀¹ tᵏ/c(t) dt` and their midpoint rules `B_k = h ∑_i x_{i+½}ᵏ/c(x_{i+½})`, the boundary
conditions give `q = f A₁/A₀`, `D = f B₁/B₀`, and integration (summation) by parts gives
`P = f (A₂ − A₁²/A₀)` and `P_ℓ = f (B₂ − B₁²/B₀)` (`integral_sub_ellipticFDOutput`).  Now
`A₂ − A₁²/A₀ = min_ν ∫₀¹ (t − ν)²/c(t) dt` and likewise for `B`, so the difference is squeezed
between the midpoint-rule errors of `(t − ν)²/c(t)` at the two minimisers `ν ∈ [0, 1]`
(`abs_quadratic_gap_le`, `le_quadratic_gap`).  The second derivative `2(1 + aν)²/(1 + at)³` of
this weight lies in `[1/4, 8]`, so each midpoint-rule error lies between `h²/96` and `h²/3`
(`abs_midpoint_error_le`, `le_midpoint_error`, `integral_sub_midpoint_mem`, `ellipticGap_mem`).

**Main results.**

* `isEllipticSol_ellipticSol`, `eq_ellipticSol_of_isEllipticSol`: the exact solution
  `u(x) = ∫₀ˣ (q − f t)/(1 + a t) dt`, `q = f A₁/A₀`, is the only classical solution on `[0, 1]`.
* `isEllipticFD_ellipticFDSol`, `isEllipticFD_iff`: the exact finite-difference solution
  `U_j = h ∑_{i<j} (D − f x_{i+½})/(1 + a x_{i+½})`, `D = f B₁/B₀`, is the only one;
  `isEllipticFD_iff_fe`: the scheme is the finite-element method with one-point quadrature.
* `ellipticFD_error`: **uniform second-order accuracy**, `|P − P_h| ≤ (|f|/3) h²` for every
  `a ∈ [0, 1]`, every forcing `f`, every classical solution `u` and every solution `U` of the
  scheme; `ellipticFD_error_ge`: the order is exact, `(|f|/96) h² ≤ |P − P_h|`.
* `ellipticFD_nodal_error`: the max-norm reading of "uniform second order accuracy",
  `|u(x_j) − U_j| ≤ (|f|/3) h²` at every node.
* `ellipticPl_error`: for the paper's forcing `f = 50 Z²`, `|P − P_ℓ| ≤ K h_ℓ²` with the random
  constant `K = (50/3) Z²`.
* `not_ae_abs_ellipticP_sub_le`: no deterministic `K` satisfies `|P − P_ℓ| ≤ K h_ℓ²` almost
  surely, whatever the law of `a ∈ [0, 1]`.
* `ellipticK_moments`: for `Z ~ N(0, 1)`, `E[K] = 50/3` and `E[K²] = 2500/3 < ∞`.
* `elliptic_fd_rates`: **`α = 2`, `β = 4` end to end**, from `rates_of_pathwise_random`: `P` and
  `P_ℓ` are square integrable, `|E[P_ℓ − P]| ≤ (50/3) h_ℓ²` and
  `V[P_{ℓ+1} − P_ℓ] ≤ E[(P_{ℓ+1} − P_ℓ)²] ≤ (62500/3) h_{ℓ+1}⁴`.

**Deviations from the paper.**  The paper's constant `K` is deterministic, but here it cannot be:
the error is at least `(50/96) Z² h_ℓ²` and `Z²` is unbounded (`not_ae_abs_ellipticP_sub_le`).
We use the random constant `K = (50/3) Z²`, which has `E[K²] < ∞`, and that is all the rates need.
We state `≤` rather than the paper's `<`: this is a modelling choice tied to our explicit `K`,
which vanishes at `Z = 0` (any larger constant gives `<`).  We read "uniform" as uniform in the
coefficient `a ∈ [0, 1]`; the paper's conclusion is about the output error `P − P_ℓ`, which we
bound directly (`ellipticFD_error`), and we also prove the nodal max-norm bound
(`ellipticFD_nodal_error`).  Only `a ∈ [0, 1]` almost surely and the measurability of `a` are
used (not its uniform law, nor the independence of `a` and `Z`).  The constants `1/3` and `1/96`
are not sharp: numerically `|P − P_ℓ|/(|f| h²)` ranges over `[0.057, 1/12]`, with `1/12` at
`a = 0`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### The problem, the scheme and their solutions -/

/-- The moments `A_k = ∫₀¹ tᵏ/(1 + a t) dt` of the weight `1/c(t)`, `c(t) = 1 + a t`, of the
elliptic example of Giles 2015, §7.1 (p. 49).  The exact flux, solution and output are expressed
through `A₀`, `A₁`, `A₂`. -/
noncomputable def ellipticMoment (a : ℝ) (k : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ k / (1 + a * t)

/-- The midpoint rules `B_k = h ∑_{i<N} x_{i+½}ᵏ/(1 + a x_{i+½})` for the moments `A_k`, with
`h = 1/N` and the cell midpoints `x_{i+½} = (i + ½) h` (Giles 2015, §7.1). -/
noncomputable def ellipticFDMoment (a : ℝ) (N k : ℕ) : ℝ :=
  ∑ i ∈ range N, 1 / (N : ℝ) * (((i : ℝ) + 1 / 2) / N) ^ k / (1 + a * (((i : ℝ) + 1 / 2) / N))

/-- **The elliptic problem** of Giles 2015, §7.1 (p. 49): `d/dx (c(x) du/dx) = −f` on `0 < x < 1`,
`c(x) = 1 + a x`, `u(0) = u(1) = 0` (the paper has `f = 50 Z²`).  A classical solution is
continuous on `[0, 1]` and differentiable on `(0, 1)`, and its flux `c u′` is differentiable on
`(0, 1)` with derivative `−f`. -/
def IsEllipticSol (a f : ℝ) (u : ℝ → ℝ) : Prop :=
  ContinuousOn u (Set.Icc 0 1) ∧ DifferentiableOn ℝ u (Set.Ioo 0 1) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun y => (1 + a * y) * deriv u y) (-f) x) ∧
    u 0 = 0 ∧ u 1 = 0

/-- The exact solution of the elliptic problem of Giles 2015, §7.1:
`u(x) = ∫₀ˣ (q − f t)/(1 + a t) dt`, with the flux `c u′ = q − f x` and `q = f A₁/A₀` chosen so
that `u(1) = 0`. -/
noncomputable def ellipticSol (a f x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, (f * ellipticMoment a 1 / ellipticMoment a 0 - f * t) / (1 + a * t)

/-- **The finite-difference scheme** of Giles 2015, §7.1 (p. 49: "a simple second order central
difference approximation … (equivalent to a finite element approximation with a 1-point
quadrature)"), on the uniform grid `x_j = j h`, `h = 1/N`: `U_0 = U_N = 0` and, at every interior
node `0 < j < N`, `(c(x_{j+½}) (U_{j+1} − U_j) − c(x_{j−½}) (U_j − U_{j−1}))/h² = −f` with
`c(x) = 1 + a x`.  The paper does not print the scheme; this conservative form, with `c` at the
cell midpoints, is our reading, and it is the one that the finite elements with the midpoint
quadrature give (`isEllipticFD_iff_fe`).  For `N = 2` (level `0`) there is one interior node. -/
def IsEllipticFD (a f : ℝ) (N : ℕ) (U : ℕ → ℝ) : Prop :=
  U 0 = 0 ∧ U N = 0 ∧ ∀ j : ℕ, 0 < j → j < N →
    ((1 + a * (((j : ℝ) + 1 / 2) / N)) * (U (j + 1) - U j) -
        (1 + a * (((j : ℝ) - 1 / 2) / N)) * (U j - U (j - 1))) / (1 / (N : ℝ)) ^ 2 = -f

/-- The exact solution of the finite-difference scheme of Giles 2015, §7.1:
`U_j = h ∑_{i<j} (D − f x_{i+½})/(1 + a x_{i+½})`, with the discrete flux
`c(x_{i+½})(U_{i+1} − U_i)/h = D − f x_{i+½}` and `D = f B₁/B₀` chosen so that `U_N = 0`. -/
noncomputable def ellipticFDSol (a f : ℝ) (N j : ℕ) : ℝ :=
  ∑ i ∈ range j, 1 / (N : ℝ) *
    (f * ellipticFDMoment a N 1 / ellipticFDMoment a N 0 - f * (((i : ℝ) + 1 / 2) / N)) /
      (1 + a * (((i : ℝ) + 1 / 2) / N))

/-- The approximation `P_ℓ` of the output `P = ∫₀¹ u(x) dx` of Giles 2015, §7.1, from the grid
values `U_0, …, U_N`: the trapezoidal rule `h ((U_0 + U_N)/2 + ∑_{0<j<N} U_j)`, `h = 1/N` (the
paper does not specify `P_ℓ`; this is also the integral of the piecewise-linear interpolant). -/
noncomputable def ellipticFDOutput (N : ℕ) (U : ℕ → ℝ) : ℝ :=
  1 / (N : ℝ) * ((U 0 + U N) / 2 + ∑ j ∈ range (N - 1), U (j + 1))

/-- The output `P = ∫₀¹ u(x) dx` of the elliptic example of Giles 2015, §7.1, for the coefficient
`c(x) = 1 + a x` and the forcing `f` (`f = 50 Z²` in the paper). -/
noncomputable def ellipticP (a f : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, ellipticSol a f x

/-- The level-`ℓ` approximation `P_ℓ` of Giles 2015, §7.1: the scheme on the grid of spacing
`h_ℓ = 2^{−(ℓ+1)}` (`N = 2^{ℓ+1}` cells), and the trapezoidal rule for `∫₀¹ u`. -/
noncomputable def ellipticPl (a f : ℝ) (ℓ : ℕ) : ℝ :=
  ellipticFDOutput (2 ^ (ℓ + 1)) (ellipticFDSol a f (2 ^ (ℓ + 1)))

/-! ### The midpoint rule -/

/-- **The midpoint rule on one cell.**  If `Φ′ = φ`, `φ′ = φ₁`, `φ₁′ = φ₂` and `|φ₂| ≤ M` on
`[x − r, x + r]`, then `|Φ(x + r) − Φ(x − r) − 2r φ(x)| ≤ M r³/3`: the midpoint rule for
`∫_{x−r}^{x+r} φ` has error at most `M h³/24`, `h = 2r` (used for Giles 2015, §7.1). -/
lemma abs_midpoint_error_le {Φ φ φ₁ φ₂ : ℝ → ℝ} {x r M : ℝ} (hr : 0 ≤ r)
    (hΦ : ∀ t ∈ Set.Icc (x - r) (x + r), HasDerivAt Φ (φ t) t)
    (hφ : ∀ t ∈ Set.Icc (x - r) (x + r), HasDerivAt φ (φ₁ t) t)
    (hφ₁ : ∀ t ∈ Set.Icc (x - r) (x + r), HasDerivAt φ₁ (φ₂ t) t)
    (hM : ∀ t ∈ Set.Icc (x - r) (x + r), |φ₂ t| ≤ M) :
    |Φ (x + r) - Φ (x - r) - 2 * r * φ x| ≤ M / 3 * r ^ 3 := by
  have hp : ∀ s ∈ Set.Icc (0 : ℝ) r, x + s ∈ Set.Icc (x - r) (x + r) := fun s hs =>
    ⟨by linarith [hs.1, hs.2], by linarith [hs.2]⟩
  have hm : ∀ s ∈ Set.Icc (0 : ℝ) r, x - s ∈ Set.Icc (x - r) (x + r) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  -- the odd part of `φ₁` around `x`
  have d1 : ∀ s ∈ Set.Icc (0 : ℝ) r, HasDerivAt (fun s => φ₁ (x + s) - φ₁ (x - s))
      (φ₂ (x + s) + φ₂ (x - s)) s := fun s hs =>
    (((hφ₁ _ (hp s hs)).comp_const_add x s).sub
      ((hφ₁ _ (hm s hs)).comp_const_sub x s)).congr_deriv (by ring)
  have bd1 : ∀ s ∈ Set.Ico (0 : ℝ) r, ‖φ₂ (x + s) + φ₂ (x - s)‖ ≤ 2 * M := by
    intro s hs
    have hs' := Set.Ico_subset_Icc_self hs
    rw [Real.norm_eq_abs]
    calc |φ₂ (x + s) + φ₂ (x - s)| ≤ |φ₂ (x + s)| + |φ₂ (x - s)| := abs_add_le _ _
      _ ≤ M + M := add_le_add (hM _ (hp s hs')) (hM _ (hm s hs'))
      _ = 2 * M := by ring
  have b1 : ∀ s ∈ Set.Icc (0 : ℝ) r, ‖φ₁ (x + s) - φ₁ (x - s)‖ ≤ 2 * M * s :=
    image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s => φ₁ (x + s) - φ₁ (x - s)) (B := fun s => 2 * M * s) (B' := fun _ => 2 * M)
      (fun s hs => (d1 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (d1 s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp) (fun s => ((hasDerivAt_id' s).const_mul (2 * M)).congr_deriv (mul_one _)) bd1
  -- the even part of `φ` around `x`
  have d2 : ∀ s ∈ Set.Icc (0 : ℝ) r, HasDerivAt (fun s => φ (x + s) + φ (x - s) - 2 * φ x)
      (φ₁ (x + s) - φ₁ (x - s)) s := fun s hs =>
    ((((hφ _ (hp s hs)).comp_const_add x s).add
      ((hφ _ (hm s hs)).comp_const_sub x s)).sub_const (2 * φ x)).congr_deriv (by ring)
  have b2 : ∀ s ∈ Set.Icc (0 : ℝ) r, ‖φ (x + s) + φ (x - s) - 2 * φ x‖ ≤ M * s ^ 2 :=
    image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s => φ (x + s) + φ (x - s) - 2 * φ x) (B := fun s => M * s ^ 2)
      (B' := fun s => 2 * M * s)
      (fun s hs => (d2 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (d2 s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp [two_mul]) (fun s => ((hasDerivAt_pow 2 s).const_mul M).congr_deriv (by ring))
      (fun s hs => b1 s (Set.Ico_subset_Icc_self hs))
  -- the error itself
  have d3 : ∀ s ∈ Set.Icc (0 : ℝ) r, HasDerivAt (fun s => Φ (x + s) - Φ (x - s) - 2 * s * φ x)
      (φ (x + s) + φ (x - s) - 2 * φ x) s := fun s hs =>
    ((((hΦ _ (hp s hs)).comp_const_add x s).sub ((hΦ _ (hm s hs)).comp_const_sub x s)).sub
      (((hasDerivAt_id' s).const_mul 2).mul_const (φ x))).congr_deriv (by ring)
  have b3 := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s => Φ (x + s) - Φ (x - s) - 2 * s * φ x) (B := fun s => M / 3 * s ^ 3)
      (B' := fun s => M * s ^ 2)
      (fun s hs => (d3 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (d3 s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp) (fun s => ((hasDerivAt_pow 3 s).const_mul (M / 3)).congr_deriv (by ring))
      (fun s hs => b2 s (Set.Ico_subset_Icc_self hs)) (Set.right_mem_Icc.2 hr)
  rwa [Real.norm_eq_abs] at b3

/-- **The midpoint rule on one cell, lower bound.**  If `Φ′ = φ`, `φ′ = φ₁`, `φ₁′ = φ₂` and
`m ≤ φ₂` on `[x − r, x + r]`, then `m r³/3 ≤ Φ(x + r) − Φ(x − r) − 2r φ(x)`: the error of the
midpoint rule for `∫_{x−r}^{x+r} φ` is at least `m h³/24`, `h = 2r` (used for Giles 2015, §7.1). -/
lemma le_midpoint_error {Φ φ φ₁ φ₂ : ℝ → ℝ} {x r m : ℝ} (hr : 0 ≤ r)
    (hΦ : ∀ t ∈ Set.Icc (x - r) (x + r), HasDerivAt Φ (φ t) t)
    (hφ : ∀ t ∈ Set.Icc (x - r) (x + r), HasDerivAt φ (φ₁ t) t)
    (hφ₁ : ∀ t ∈ Set.Icc (x - r) (x + r), HasDerivAt φ₁ (φ₂ t) t)
    (hlow : ∀ t ∈ Set.Icc (x - r) (x + r), m ≤ φ₂ t) :
    m / 3 * r ^ 3 ≤ Φ (x + r) - Φ (x - r) - 2 * r * φ x := by
  have hp : ∀ s ∈ Set.Icc (0 : ℝ) r, x + s ∈ Set.Icc (x - r) (x + r) := fun s hs =>
    ⟨by linarith [hs.1, hs.2], by linarith [hs.2]⟩
  have hm : ∀ s ∈ Set.Icc (0 : ℝ) r, x - s ∈ Set.Icc (x - r) (x + r) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  -- the odd part of `φ₁` around `x`
  have d1 : ∀ s ∈ Set.Icc (0 : ℝ) r, HasDerivAt (fun s => φ₁ (x + s) - φ₁ (x - s))
      (φ₂ (x + s) + φ₂ (x - s)) s := fun s hs =>
    (((hφ₁ _ (hp s hs)).comp_const_add x s).sub
      ((hφ₁ _ (hm s hs)).comp_const_sub x s)).congr_deriv (by ring)
  have b1 : ∀ s ∈ Set.Icc (0 : ℝ) r, 2 * m * s ≤ φ₁ (x + s) - φ₁ (x - s) :=
    image_le_of_deriv_right_le_deriv_boundary (f := fun s => 2 * m * s) (f' := fun _ => 2 * m)
      (B := fun s => φ₁ (x + s) - φ₁ (x - s)) (B' := fun s => φ₂ (x + s) + φ₂ (x - s))
      (by fun_prop)
      (fun s _ => (((hasDerivAt_id' s).const_mul (2 * m)).congr_deriv (mul_one _)).hasDerivWithinAt)
      (by simp) (fun s hs => (d1 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (d1 s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun s hs => by
        have hs' := Set.Ico_subset_Icc_self hs
        linarith [hlow _ (hp s hs'), hlow _ (hm s hs')])
  -- the even part of `φ` around `x`
  have d2 : ∀ s ∈ Set.Icc (0 : ℝ) r, HasDerivAt (fun s => φ (x + s) + φ (x - s) - 2 * φ x)
      (φ₁ (x + s) - φ₁ (x - s)) s := fun s hs =>
    ((((hφ _ (hp s hs)).comp_const_add x s).add
      ((hφ _ (hm s hs)).comp_const_sub x s)).sub_const (2 * φ x)).congr_deriv (by ring)
  have b2 : ∀ s ∈ Set.Icc (0 : ℝ) r, m * s ^ 2 ≤ φ (x + s) + φ (x - s) - 2 * φ x :=
    image_le_of_deriv_right_le_deriv_boundary (f := fun s => m * s ^ 2)
      (f' := fun s => 2 * m * s) (B := fun s => φ (x + s) + φ (x - s) - 2 * φ x)
      (B' := fun s => φ₁ (x + s) - φ₁ (x - s)) (by fun_prop)
      (fun s _ => (((hasDerivAt_pow 2 s).const_mul m).congr_deriv (by ring)).hasDerivWithinAt)
      (by simp [two_mul]) (fun s hs => (d2 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (d2 s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun s hs => b1 s (Set.Ico_subset_Icc_self hs))
  -- the error itself
  have d3 : ∀ s ∈ Set.Icc (0 : ℝ) r, HasDerivAt (fun s => Φ (x + s) - Φ (x - s) - 2 * s * φ x)
      (φ (x + s) + φ (x - s) - 2 * φ x) s := fun s hs =>
    ((((hΦ _ (hp s hs)).comp_const_add x s).sub ((hΦ _ (hm s hs)).comp_const_sub x s)).sub
      (((hasDerivAt_id' s).const_mul 2).mul_const (φ x))).congr_deriv (by ring)
  exact image_le_of_deriv_right_le_deriv_boundary (f := fun s => m / 3 * s ^ 3)
      (f' := fun s => m * s ^ 2) (B := fun s => Φ (x + s) - Φ (x - s) - 2 * s * φ x)
      (B' := fun s => φ (x + s) + φ (x - s) - 2 * φ x) (by fun_prop)
      (fun s _ => (((hasDerivAt_pow 3 s).const_mul (m / 3)).congr_deriv (by ring)).hasDerivWithinAt)
      (by simp) (fun s hs => (d3 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (d3 s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun s hs => b2 s (Set.Ico_subset_Icc_self hs)) (Set.right_mem_Icc.2 hr)

/-- The weight `φ_ν(t) = (t − ν)²/(1 + a t)` has the derivative
`(t − ν)(2 + a t + a ν)/(1 + a t)²` where `1 + a t ≠ 0`. -/
lemma hasDerivAt_ellipticWeight (a ν : ℝ) {t : ℝ} (ht : 1 + a * t ≠ 0) :
    HasDerivAt (fun t => (t - ν) ^ 2 / (1 + a * t))
      ((t - ν) * (2 + a * t + a * ν) / (1 + a * t) ^ 2) t := by
  have h1 : HasDerivAt (fun t => (t - ν) ^ 2) (2 * (t - ν)) t :=
    (((hasDerivAt_id' t).sub_const ν).pow 2).congr_deriv (by ring)
  have h2 : HasDerivAt (fun t => 1 + a * t) a t :=
    (((hasDerivAt_id' t).const_mul a).const_add 1).congr_deriv (mul_one a)
  refine (h1.div h2 ht).congr_deriv ?_
  field_simp
  ring

/-- The second derivative of the weight `(t − ν)²/(1 + a t)` is `2(1 + a ν)²/(1 + a t)³` where
`1 + a t ≠ 0`. -/
lemma hasDerivAt_ellipticWeight_deriv (a ν : ℝ) {t : ℝ} (ht : 1 + a * t ≠ 0) :
    HasDerivAt (fun t => (t - ν) * (2 + a * t + a * ν) / (1 + a * t) ^ 2)
      (2 * (1 + a * ν) ^ 2 / (1 + a * t) ^ 3) t := by
  have h1 : HasDerivAt (fun t => (t - ν) * (2 + a * t + a * ν)) (2 + 2 * a * t) t :=
    (((hasDerivAt_id' t).sub_const ν).mul
      ((((hasDerivAt_id' t).const_mul a).const_add 2).add_const (a * ν))).congr_deriv (by ring)
  have h2 : HasDerivAt (fun t => (1 + a * t) ^ 2) (2 * (1 + a * t) * a) t :=
    ((((hasDerivAt_id' t).const_mul a).const_add 1).pow 2).congr_deriv (by ring)
  refine (h1.div h2 (pow_ne_zero 2 ht)).congr_deriv ?_
  field_simp
  ring

/-- The second derivative `2(1 + a ν)²/(1 + a t)³` of the weight is at most `8` for
`a, ν ∈ [0, 1]` and `t ≥ 0`. -/
lemma abs_ellipticWeight_deriv2_le {a ν t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hν0 : 0 ≤ ν)
    (hν1 : ν ≤ 1) (ht : 0 ≤ t) : |2 * (1 + a * ν) ^ 2 / (1 + a * t) ^ 3| ≤ 8 := by
  have h1 : 1 ≤ 1 + a * t := by nlinarith [mul_nonneg ha0 ht]
  have h2 : 1 + a * ν ≤ 2 := by nlinarith [mul_le_mul ha1 hν1 hν0 zero_le_one]
  have h3 : 0 ≤ 1 + a * ν := by nlinarith [mul_nonneg ha0 hν0]
  have h4 : 1 ≤ (1 + a * t) ^ 3 := one_le_pow₀ h1
  have h5 : (1 + a * ν) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ h3 h2 2
  rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity)),
    div_le_iff₀ (by positivity)]
  nlinarith

/-- The second derivative `2(1 + a ν)²/(1 + a t)³` of the weight is at least `1/4` for
`a ∈ [0, 1]`, `ν ≥ 0` and `t ∈ [0, 1]`. -/
lemma ellipticWeight_deriv2_ge {a ν t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hν0 : 0 ≤ ν)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 1 / 4 ≤ 2 * (1 + a * ν) ^ 2 / (1 + a * t) ^ 3 := by
  have h1 : 1 ≤ 1 + a * t := by nlinarith [mul_nonneg ha0 ht0]
  have h2 : 1 + a * t ≤ 2 := by nlinarith [mul_le_mul ha1 ht1 ht0 zero_le_one]
  have h3 : 1 ≤ 1 + a * ν := by nlinarith [mul_nonneg ha0 hν0]
  have h4 : (1 + a * t) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) h2 3
  have h5 : 1 ≤ (1 + a * ν) ^ 2 := one_le_pow₀ h3
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The flux quotient `g(t) = (p − r t)/(1 + a t)` has the derivative `−(r + a p)/(1 + a t)²`
where `1 + a t ≠ 0`. -/
lemma hasDerivAt_affine_div (a p r : ℝ) {t : ℝ} (ht : 1 + a * t ≠ 0) :
    HasDerivAt (fun t => (p - r * t) / (1 + a * t)) (-(r + a * p) / (1 + a * t) ^ 2) t := by
  have h1 : HasDerivAt (fun t => p - r * t) (-r) t :=
    (((hasDerivAt_id' t).const_mul r).const_sub p).congr_deriv (by ring)
  have h2 : HasDerivAt (fun t => 1 + a * t) a t :=
    (((hasDerivAt_id' t).const_mul a).const_add 1).congr_deriv (mul_one a)
  refine (h1.div h2 ht).congr_deriv ?_
  field_simp
  ring

/-- The second derivative of `(p − r t)/(1 + a t)` is `2a(r + a p)/(1 + a t)³` where
`1 + a t ≠ 0`. -/
lemma hasDerivAt_affine_div_deriv (a p r : ℝ) {t : ℝ} (ht : 1 + a * t ≠ 0) :
    HasDerivAt (fun t => -(r + a * p) / (1 + a * t) ^ 2)
      (2 * a * (r + a * p) / (1 + a * t) ^ 3) t := by
  have h2 : HasDerivAt (fun t => (1 + a * t) ^ 2) (2 * (1 + a * t) * a) t :=
    ((((hasDerivAt_id' t).const_mul a).const_add 1).pow 2).congr_deriv (by ring)
  refine ((hasDerivAt_const t (-(r + a * p))).div h2 (pow_ne_zero 2 ht)).congr_deriv ?_
  field_simp
  ring

/-- The second derivative `2a(r + a p)/(1 + a t)³` is at most `2(|r| + |p|)` in absolute value
for `a ∈ [0, 1]` and `t ≥ 0`. -/
lemma abs_affine_div_deriv2_le {a p r t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t) :
    |2 * a * (r + a * p) / (1 + a * t) ^ 3| ≤ 2 * (|r| + |p|) := by
  have h1 : 1 ≤ 1 + a * t := by nlinarith [mul_nonneg ha0 ht]
  have h3 : 1 ≤ (1 + a * t) ^ 3 := one_le_pow₀ h1
  have h4 : |r + a * p| ≤ |r| + |p| := by
    calc |r + a * p| ≤ |r| + |a * p| := abs_add_le _ _
      _ = |r| + a * |p| := by rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ |r| + |p| := by nlinarith [abs_nonneg p]
  have h5 : |2 * a * (r + a * p)| ≤ 2 * (|r| + |p|) := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg ha0]
    nlinarith [mul_nonneg (sub_nonneg.2 ha1) (abs_nonneg (r + a * p))]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + a * t) ^ 3), div_le_iff₀ (by positivity)]
  calc |2 * a * (r + a * p)| ≤ 2 * (|r| + |p|) := h5
    _ ≤ 2 * (|r| + |p|) * (1 + a * t) ^ 3 := le_mul_of_one_le_right (by positivity) h3

/-- A continuous numerator over `1 + a t`, `a ≥ 0`, is interval integrable on `[0, x]`, `x ≥ 0`. -/
lemma intervalIntegrable_div_affine {a : ℝ} (ha : 0 ≤ a) {p : ℝ → ℝ} (hp : Continuous p) {x : ℝ}
    (hx : 0 ≤ x) : IntervalIntegrable (fun t => p t / (1 + a * t)) volume 0 x := by
  refine ContinuousOn.intervalIntegrable_of_Icc hx fun t ht => ?_
  have h : 1 + a * t ≠ 0 := by nlinarith [mul_nonneg ha ht.1]
  have hc : ContinuousAt (fun t : ℝ => 1 + a * t) t := by fun_prop
  exact (hp.continuousAt.div₀ hc h).continuousWithinAt

/-- **The composite midpoint rule for `(t − ν)²/(1 + a t)`** (used for Giles 2015, §7.1): for
`a, ν ∈ [0, 1]` and `N ≥ 1` cells, the error
`E = ∫₀¹ (t − ν)²/(1 + a t) dt − h ∑_{i<N} (x_{i+½} − ν)²/(1 + a x_{i+½})`, `h = 1/N`, satisfies
`h²/96 ≤ E` and `|E| ≤ h²/3`, because the second derivative of the weight lies in `[1/4, 8]`. -/
lemma integral_sub_midpoint_mem {a ν : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hν0 : 0 ≤ ν)
    (hν1 : ν ≤ 1) {N : ℕ} (hN : 0 < N) :
    1 / 96 * (1 / (N : ℝ)) ^ 2 ≤ (∫ t in (0 : ℝ)..1, (t - ν) ^ 2 / (1 + a * t)) -
        ∑ i ∈ range N, 1 / (N : ℝ) * ((((i : ℝ) + 1 / 2) / N - ν) ^ 2 /
          (1 + a * (((i : ℝ) + 1 / 2) / N))) ∧
      |(∫ t in (0 : ℝ)..1, (t - ν) ^ 2 / (1 + a * t)) -
        ∑ i ∈ range N, 1 / (N : ℝ) * ((((i : ℝ) + 1 / 2) / N - ν) ^ 2 /
          (1 + a * (((i : ℝ) + 1 / 2) / N)))| ≤ 1 / 3 * (1 / (N : ℝ)) ^ 2 := by
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < 1 + a * t := fun t ht => by nlinarith [mul_nonneg ha0 ht]
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hmeas : Measurable fun t : ℝ => (t - ν) ^ 2 / (1 + a * t) := by fun_prop
  -- the antiderivative
  have hΦ : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun y => ∫ s in (0 : ℝ)..y, (s - ν) ^ 2 / (1 + a * s))
      ((t - ν) ^ 2 / (1 + a * t)) t := fun t ht =>
    intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_div_affine ha0 (by fun_prop) ht)
      hmeas.stronglyMeasurable.stronglyMeasurableAtFilter
      (hasDerivAt_ellipticWeight a ν (hpos t ht).ne').continuousAt
  -- telescoping over the cells
  have htel : ∑ i ∈ range N, ((∫ s in (0 : ℝ)..((i : ℝ) + 1) / N, (s - ν) ^ 2 / (1 + a * s)) -
      ∫ s in (0 : ℝ)..(i : ℝ) / N, (s - ν) ^ 2 / (1 + a * s)) =
      ∫ t in (0 : ℝ)..1, (t - ν) ^ 2 / (1 + a * t) := by
    have h := Finset.sum_range_sub
      (fun i : ℕ => ∫ s in (0 : ℝ)..(i : ℝ) / N, (s - ν) ^ 2 / (1 + a * s)) N
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div,
      intervalIntegral.integral_same, sub_zero] at h
    rw [h, div_self hNr.ne']
  -- one cell
  have hcell : ∀ i ∈ range N,
      1 / 4 / 3 * (1 / (2 * (N : ℝ))) ^ 3 ≤
        (∫ s in (0 : ℝ)..((i : ℝ) + 1) / N, (s - ν) ^ 2 / (1 + a * s)) -
          (∫ s in (0 : ℝ)..(i : ℝ) / N, (s - ν) ^ 2 / (1 + a * s)) -
          1 / (N : ℝ) * ((((i : ℝ) + 1 / 2) / N - ν) ^ 2 / (1 + a * (((i : ℝ) + 1 / 2) / N))) ∧
      |(∫ s in (0 : ℝ)..((i : ℝ) + 1) / N, (s - ν) ^ 2 / (1 + a * s)) -
        (∫ s in (0 : ℝ)..(i : ℝ) / N, (s - ν) ^ 2 / (1 + a * s)) -
        1 / (N : ℝ) * ((((i : ℝ) + 1 / 2) / N - ν) ^ 2 / (1 + a * (((i : ℝ) + 1 / 2) / N)))| ≤
        8 / 3 * (1 / (2 * (N : ℝ))) ^ 3 := by
    intro i hi
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast mem_range.1 hi
    have e1 : ((i : ℝ) + 1 / 2) / N + 1 / (2 * N) = ((i : ℝ) + 1) / N := by
      field_simp
      ring
    have e0 : ((i : ℝ) + 1 / 2) / N - 1 / (2 * N) = (i : ℝ) / N := by
      field_simp
      ring
    have e2 : 2 * (1 / (2 * (N : ℝ))) = 1 / N := by
      field_simp
    have hsub : ∀ t ∈ Set.Icc (((i : ℝ) + 1 / 2) / N - 1 / (2 * N))
        (((i : ℝ) + 1 / 2) / N + 1 / (2 * N)), 0 ≤ t ∧ t ≤ 1 := by
      intro t ht
      rw [e0, e1] at ht
      exact ⟨le_trans (by positivity) ht.1, ht.2.trans ((div_le_one hNr).2 hiN)⟩
    have hl := le_midpoint_error (m := 1 / 4) (by positivity)
      (fun t ht => hΦ t (hsub t ht).1)
      (fun t ht => hasDerivAt_ellipticWeight a ν (hpos t (hsub t ht).1).ne')
      (fun t ht => hasDerivAt_ellipticWeight_deriv a ν (hpos t (hsub t ht).1).ne')
      (fun t ht => ellipticWeight_deriv2_ge ha0 ha1 hν0 (hsub t ht).1 (hsub t ht).2)
    have hu := abs_midpoint_error_le (M := 8) (by positivity)
      (fun t ht => hΦ t (hsub t ht).1)
      (fun t ht => hasDerivAt_ellipticWeight a ν (hpos t (hsub t ht).1).ne')
      (fun t ht => hasDerivAt_ellipticWeight_deriv a ν (hpos t (hsub t ht).1).ne')
      (fun t ht => abs_ellipticWeight_deriv2_le ha0 ha1 hν0 hν1 (hsub t ht).1)
    rw [e1, e0, e2] at hl hu
    exact ⟨hl, hu⟩
  rw [← htel, ← sum_sub_distrib]
  constructor
  · calc 1 / 96 * (1 / (N : ℝ)) ^ 2 = ∑ _i ∈ range N, 1 / 4 / 3 * (1 / (2 * (N : ℝ))) ^ 3 := by
          rw [sum_const, card_range, nsmul_eq_mul]
          field_simp
          ring
      _ ≤ _ := sum_le_sum fun i hi => (hcell i hi).1
  · calc |∑ i ∈ range N, ((∫ s in (0 : ℝ)..((i : ℝ) + 1) / N, (s - ν) ^ 2 / (1 + a * s)) -
          (∫ s in (0 : ℝ)..(i : ℝ) / N, (s - ν) ^ 2 / (1 + a * s)) -
          1 / (N : ℝ) * ((((i : ℝ) + 1 / 2) / N - ν) ^ 2 / (1 + a * (((i : ℝ) + 1 / 2) / N))))|
        ≤ ∑ i ∈ range N, |(∫ s in (0 : ℝ)..((i : ℝ) + 1) / N, (s - ν) ^ 2 / (1 + a * s)) -
          (∫ s in (0 : ℝ)..(i : ℝ) / N, (s - ν) ^ 2 / (1 + a * s)) -
          1 / (N : ℝ) * ((((i : ℝ) + 1 / 2) / N - ν) ^ 2 / (1 + a * (((i : ℝ) + 1 / 2) / N)))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ range N, 8 / 3 * (1 / (2 * (N : ℝ))) ^ 3 := sum_le_sum fun i hi => (hcell i hi).2
      _ = 1 / 3 * (1 / (N : ℝ)) ^ 2 := by
          rw [sum_const, card_range, nsmul_eq_mul]
          field_simp
          ring

/-- **The composite midpoint rule on `[0, j h]`** (used for Giles 2015, §7.1).  If `φ` is
measurable and twice differentiable on `[0, 1]` with `|φ″| ≤ M`, then for `N ≥ 1` cells of width
`h = 1/N` and `j ≤ N`, `|∫₀^{j h} φ − h ∑_{i<j} φ(x_{i+½})| ≤ (M/24) h²`. -/
lemma abs_integral_sub_midpoint_sum_le {φ φ₁ φ₂ : ℝ → ℝ} {M : ℝ} (hmeas : Measurable φ)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (φ₁ t) t)
    (hφ₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ₁ (φ₂ t) t)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |φ₂ t| ≤ M) {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    |(∫ t in (0 : ℝ)..(j : ℝ) / N, φ t) - ∑ i ∈ range j, 1 / (N : ℝ) * φ (((i : ℝ) + 1 / 2) / N)|
      ≤ M / 24 * (1 / (N : ℝ)) ^ 2 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  -- the antiderivative
  have hΦ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun y => ∫ s in (0 : ℝ)..y, φ s) (φ t) t :=
    fun t ht => intervalIntegral.integral_hasDerivAt_right
      (ContinuousOn.intervalIntegrable_of_Icc ht.1 fun s hs =>
        (hφ s ⟨hs.1, hs.2.trans ht.2⟩).continuousAt.continuousWithinAt)
      hmeas.stronglyMeasurable.stronglyMeasurableAtFilter (hφ t ht).continuousAt
  -- telescoping over the cells
  have htel : ∑ i ∈ range j, ((∫ s in (0 : ℝ)..((i : ℝ) + 1) / N, φ s) -
      ∫ s in (0 : ℝ)..(i : ℝ) / N, φ s) = ∫ t in (0 : ℝ)..(j : ℝ) / N, φ t := by
    have h := Finset.sum_range_sub (fun i : ℕ => ∫ s in (0 : ℝ)..(i : ℝ) / N, φ s) j
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div,
      intervalIntegral.integral_same, sub_zero] at h
    exact h
  -- one cell
  have hcell : ∀ i ∈ range j, |(∫ s in (0 : ℝ)..((i : ℝ) + 1) / N, φ s) -
      (∫ s in (0 : ℝ)..(i : ℝ) / N, φ s) - 1 / (N : ℝ) * φ (((i : ℝ) + 1 / 2) / N)| ≤
      M / 3 * (1 / (2 * (N : ℝ))) ^ 3 := by
    intro i hi
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast (mem_range.1 hi).trans_le hj
    have e1 : ((i : ℝ) + 1 / 2) / N + 1 / (2 * N) = ((i : ℝ) + 1) / N := by
      field_simp
      ring
    have e0 : ((i : ℝ) + 1 / 2) / N - 1 / (2 * N) = (i : ℝ) / N := by
      field_simp
      ring
    have e2 : 2 * (1 / (2 * (N : ℝ))) = 1 / N := by
      field_simp
    have hsub : ∀ t ∈ Set.Icc (((i : ℝ) + 1 / 2) / N - 1 / (2 * N))
        (((i : ℝ) + 1 / 2) / N + 1 / (2 * N)), t ∈ Set.Icc (0 : ℝ) 1 := by
      intro t ht
      rw [e0, e1] at ht
      exact ⟨le_trans (by positivity) ht.1, ht.2.trans ((div_le_one hNr).2 hiN)⟩
    have h := abs_midpoint_error_le (by positivity) (fun t ht => hΦ t (hsub t ht))
      (fun t ht => hφ t (hsub t ht)) (fun t ht => hφ₁ t (hsub t ht))
      (fun t ht => hM t (hsub t ht))
    rw [e1, e0, e2] at h
    exact h
  rw [← htel, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hcell).trans ?_)
  rw [sum_const, card_range, nsmul_eq_mul]
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
  calc (j : ℝ) * (M / 3 * (1 / (2 * (N : ℝ))) ^ 3)
      ≤ (N : ℝ) * (M / 3 * (1 / (2 * (N : ℝ))) ^ 3) :=
        mul_le_mul_of_nonneg_right hjN (mul_nonneg (div_nonneg hM0 (by norm_num)) (by positivity))
    _ = M / 24 * (1 / (N : ℝ)) ^ 2 := by
        field_simp
        ring

/-! ### Moments -/

/-- `∫₀¹ (α + β t + γ t²)/(1 + a t) dt = α A₀ + β A₁ + γ A₂` for `a ≥ 0`. -/
lemma integral_quadratic_div {a : ℝ} (ha : 0 ≤ a) (α β γ : ℝ) :
    ∫ t in (0 : ℝ)..1, (α + β * t + γ * t ^ 2) / (1 + a * t) =
      α * ellipticMoment a 0 + β * ellipticMoment a 1 + γ * ellipticMoment a 2 := by
  have hi : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ => t ^ k / (1 + a * t)) volume 0 1 :=
    fun k => intervalIntegrable_div_affine ha (continuous_pow k) zero_le_one
  have e : (fun t : ℝ => (α + β * t + γ * t ^ 2) / (1 + a * t)) = fun t =>
      α * (t ^ 0 / (1 + a * t)) + β * (t ^ 1 / (1 + a * t)) + γ * (t ^ 2 / (1 + a * t)) := by
    funext t
    ring
  rw [e, intervalIntegral.integral_add (((hi 0).const_mul α).add ((hi 1).const_mul β))
      ((hi 2).const_mul γ), intervalIntegral.integral_add ((hi 0).const_mul α)
      ((hi 1).const_mul β), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rfl

/-- `h ∑_{i<N} (α + β x_{i+½} + γ x_{i+½}²)/(1 + a x_{i+½}) = α B₀ + β B₁ + γ B₂`. -/
lemma sum_quadratic_div (a : ℝ) (N : ℕ) (α β γ : ℝ) :
    ∑ i ∈ range N, 1 / (N : ℝ) * (α + β * (((i : ℝ) + 1 / 2) / N) +
        γ * (((i : ℝ) + 1 / 2) / N) ^ 2) / (1 + a * (((i : ℝ) + 1 / 2) / N)) =
      α * ellipticFDMoment a N 0 + β * ellipticFDMoment a N 1 + γ * ellipticFDMoment a N 2 := by
  simp only [ellipticFDMoment, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- `A₀ = ∫₀¹ dt/(1 + a t) > 0` for `a ≥ 0`. -/
lemma ellipticMoment_zero_pos {a : ℝ} (ha : 0 ≤ a) : 0 < ellipticMoment a 0 :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_div_affine ha (continuous_pow 0) zero_le_one)
    (fun x hx => div_pos (by rw [pow_zero]; exact one_pos) (by nlinarith [mul_nonneg ha hx.1.le]))
    zero_lt_one

/-- `0 ≤ A₁ ≤ A₀` for `a ≥ 0`. -/
lemma ellipticMoment_one_mem {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ ellipticMoment a 1 ∧ ellipticMoment a 1 ≤ ellipticMoment a 0 := by
  refine ⟨intervalIntegral.integral_nonneg zero_le_one fun t ht =>
    div_nonneg (by rw [pow_one]; exact ht.1) (by nlinarith [mul_nonneg ha ht.1]), ?_⟩
  have h := integral_quadratic_div ha 1 (-1) 0
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (1 + -1 * t + 0 * t ^ 2) / (1 + a * t) :=
    intervalIntegral.integral_nonneg zero_le_one fun t ht =>
      div_nonneg (by nlinarith [ht.2]) (by nlinarith [mul_nonneg ha ht.1])
  linarith

/-- The cell midpoints `x_{i+½} = (i + ½)/N`, `i < N`, lie in `[0, 1]`, and `1 + a x_{i+½} > 0`. -/
lemma ellipticMidpoint_mem {a : ℝ} (ha : 0 ≤ a) {N i : ℕ} (hi : i < N) :
    0 ≤ ((i : ℝ) + 1 / 2) / N ∧ ((i : ℝ) + 1 / 2) / N ≤ 1 ∧
      0 < 1 + a * (((i : ℝ) + 1 / 2) / N) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  have h0 : 0 ≤ ((i : ℝ) + 1 / 2) / N := by positivity
  refine ⟨h0, (div_le_one hNr).2 (by linarith), by nlinarith [mul_nonneg ha h0]⟩

/-- `B₀ > 0` for `a ≥ 0` and `N ≥ 1`. -/
lemma ellipticFDMoment_zero_pos {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N) :
    0 < ellipticFDMoment a N 0 := by
  refine sum_pos (fun i hi => ?_) (nonempty_range_iff.2 hN.ne')
  rw [pow_zero, mul_one]
  exact div_pos (div_pos one_pos (Nat.cast_pos.2 hN)) (ellipticMidpoint_mem ha (mem_range.1 hi)).2.2

/-- `0 ≤ B₁ ≤ B₀` for `a ≥ 0`. -/
lemma ellipticFDMoment_one_mem {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    0 ≤ ellipticFDMoment a N 1 ∧ ellipticFDMoment a N 1 ≤ ellipticFDMoment a N 0 := by
  refine ⟨sum_nonneg fun i _ => ?_, ?_⟩
  · rw [pow_one]
    positivity
  · have h := sum_quadratic_div a N 1 (-1) 0
    have h0 : 0 ≤ ∑ i ∈ range N, 1 / (N : ℝ) * (1 + -1 * (((i : ℝ) + 1 / 2) / N) +
        0 * (((i : ℝ) + 1 / 2) / N) ^ 2) / (1 + a * (((i : ℝ) + 1 / 2) / N)) := by
      refine sum_nonneg fun i hi => ?_
      obtain ⟨-, h1, hc⟩ := ellipticMidpoint_mem ha (mem_range.1 hi)
      exact div_nonneg (mul_nonneg (by positivity) (by nlinarith)) hc.le
    linarith

/-- **The gap between the two minima** (Giles 2015, §7.1).  `A₂ − A₁²/A₀` is the minimum over `ν`
of `A₂ − 2νA₁ + ν²A₀`, attained at `μ = A₁/A₀`, and likewise for `B` with `λ = B₁/B₀`.  So the
difference of the minima lies between the differences of the two quadratics at `μ` and at `λ`,
and `|(A₂ − A₁²/A₀) − (B₂ − B₁²/B₀)| ≤ ε` as soon as both of those are at most `ε`. -/
lemma abs_quadratic_gap_le {A₀ A₁ A₂ B₀ B₁ B₂ ε : ℝ} (hA : 0 < A₀) (hB : 0 < B₀)
    (hl : |(A₂ - 2 * (B₁ / B₀) * A₁ + (B₁ / B₀) ^ 2 * A₀) -
      (B₂ - 2 * (B₁ / B₀) * B₁ + (B₁ / B₀) ^ 2 * B₀)| ≤ ε)
    (hm : |(A₂ - 2 * (A₁ / A₀) * A₁ + (A₁ / A₀) ^ 2 * A₀) -
      (B₂ - 2 * (A₁ / A₀) * B₁ + (A₁ / A₀) ^ 2 * B₀)| ≤ ε) :
    |(A₂ - A₁ ^ 2 / A₀) - (B₂ - B₁ ^ 2 / B₀)| ≤ ε := by
  have e1 : (A₂ - A₁ ^ 2 / A₀) - (B₂ - B₁ ^ 2 / B₀) =
      ((A₂ - 2 * (B₁ / B₀) * A₁ + (B₁ / B₀) ^ 2 * A₀) -
        (B₂ - 2 * (B₁ / B₀) * B₁ + (B₁ / B₀) ^ 2 * B₀)) - A₀ * (B₁ / B₀ - A₁ / A₀) ^ 2 := by
    field_simp
    ring
  have e2 : (A₂ - A₁ ^ 2 / A₀) - (B₂ - B₁ ^ 2 / B₀) =
      ((A₂ - 2 * (A₁ / A₀) * A₁ + (A₁ / A₀) ^ 2 * A₀) -
        (B₂ - 2 * (A₁ / A₀) * B₁ + (A₁ / A₀) ^ 2 * B₀)) + B₀ * (B₁ / B₀ - A₁ / A₀) ^ 2 := by
    field_simp
    ring
  have p1 : 0 ≤ A₀ * (B₁ / B₀ - A₁ / A₀) ^ 2 := mul_nonneg hA.le (sq_nonneg _)
  have p2 : 0 ≤ B₀ * (B₁ / B₀ - A₁ / A₀) ^ 2 := mul_nonneg hB.le (sq_nonneg _)
  rw [abs_le] at hl hm ⊢
  constructor <;> linarith [hl.1, hl.2, hm.1, hm.2]

/-- The lower half of `abs_quadratic_gap_le`: since `B₂ − B₁²/B₀` is the minimum of
`B₂ − 2νB₁ + ν²B₀`, the difference of the minima is at least the difference of the two
quadratics at `μ = A₁/A₀` (Giles 2015, §7.1). -/
lemma le_quadratic_gap {A₀ A₁ A₂ B₀ B₁ B₂ ε : ℝ} (hA : 0 < A₀) (hB : 0 < B₀)
    (hm : ε ≤ (A₂ - 2 * (A₁ / A₀) * A₁ + (A₁ / A₀) ^ 2 * A₀) -
      (B₂ - 2 * (A₁ / A₀) * B₁ + (A₁ / A₀) ^ 2 * B₀)) :
    ε ≤ (A₂ - A₁ ^ 2 / A₀) - (B₂ - B₁ ^ 2 / B₀) := by
  have e2 : (A₂ - A₁ ^ 2 / A₀) - (B₂ - B₁ ^ 2 / B₀) =
      ((A₂ - 2 * (A₁ / A₀) * A₁ + (A₁ / A₀) ^ 2 * A₀) -
        (B₂ - 2 * (A₁ / A₀) * B₁ + (A₁ / A₀) ^ 2 * B₀)) + B₀ * (B₁ / B₀ - A₁ / A₀) ^ 2 := by
    field_simp
    ring
  rw [e2]
  linarith [mul_nonneg hB.le (sq_nonneg (B₁ / B₀ - A₁ / A₀))]

/-- The quadratics `A₂ − 2νA₁ + ν²A₀` and `B₂ − 2νB₁ + ν²B₀` are `∫₀¹ (t − ν)²/c(t) dt` and its
midpoint rule, so for `a, ν ∈ [0, 1]` their difference lies between `h²/96` and `h²/3`. -/
lemma moment_gap_mem {a ν : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    {N : ℕ} (hN : 0 < N) :
    1 / 96 * (1 / (N : ℝ)) ^ 2 ≤
        (ellipticMoment a 2 - 2 * ν * ellipticMoment a 1 + ν ^ 2 * ellipticMoment a 0) -
          (ellipticFDMoment a N 2 - 2 * ν * ellipticFDMoment a N 1 +
            ν ^ 2 * ellipticFDMoment a N 0) ∧
      |(ellipticMoment a 2 - 2 * ν * ellipticMoment a 1 + ν ^ 2 * ellipticMoment a 0) -
        (ellipticFDMoment a N 2 - 2 * ν * ellipticFDMoment a N 1 +
          ν ^ 2 * ellipticFDMoment a N 0)| ≤ 1 / 3 * (1 / (N : ℝ)) ^ 2 := by
  obtain ⟨hl, hu⟩ := integral_sub_midpoint_mem ha0 ha1 hν0 hν1 hN
  have eJ : ∫ t in (0 : ℝ)..1, (t - ν) ^ 2 / (1 + a * t) =
      ∫ t in (0 : ℝ)..1, (ν ^ 2 + -2 * ν * t + 1 * t ^ 2) / (1 + a * t) := by
    congr 1
    funext t
    ring
  have eS : ∑ i ∈ range N, 1 / (N : ℝ) * ((((i : ℝ) + 1 / 2) / N - ν) ^ 2 /
        (1 + a * (((i : ℝ) + 1 / 2) / N))) =
      ∑ i ∈ range N, 1 / (N : ℝ) * (ν ^ 2 + -2 * ν * (((i : ℝ) + 1 / 2) / N) +
        1 * (((i : ℝ) + 1 / 2) / N) ^ 2) / (1 + a * (((i : ℝ) + 1 / 2) / N)) :=
    sum_congr rfl fun i _ => by ring
  rw [eJ, eS, integral_quadratic_div ha0, sum_quadratic_div] at hl hu
  have e : (ellipticMoment a 2 - 2 * ν * ellipticMoment a 1 + ν ^ 2 * ellipticMoment a 0) -
        (ellipticFDMoment a N 2 - 2 * ν * ellipticFDMoment a N 1 +
          ν ^ 2 * ellipticFDMoment a N 0) =
      (ν ^ 2 * ellipticMoment a 0 + -2 * ν * ellipticMoment a 1 + 1 * ellipticMoment a 2) -
        (ν ^ 2 * ellipticFDMoment a N 0 + -2 * ν * ellipticFDMoment a N 1 +
          1 * ellipticFDMoment a N 2) := by
    ring
  rw [e]
  exact ⟨hl, hu⟩

/-- **The gap between the exact and the discrete minima** (Giles 2015, §7.1): for `a ∈ [0, 1]`
and `N ≥ 1` cells, `G = (A₂ − A₁²/A₀) − (B₂ − B₁²/B₀)` satisfies `h²/96 ≤ G` and `|G| ≤ h²/3`,
`h = 1/N` (`P − P_h = f G`, `integral_sub_ellipticFDOutput`). -/
lemma ellipticGap_mem {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {N : ℕ} (hN : 0 < N) :
    1 / 96 * (1 / (N : ℝ)) ^ 2 ≤
        (ellipticMoment a 2 - ellipticMoment a 1 ^ 2 / ellipticMoment a 0) -
          (ellipticFDMoment a N 2 - ellipticFDMoment a N 1 ^ 2 / ellipticFDMoment a N 0) ∧
      |(ellipticMoment a 2 - ellipticMoment a 1 ^ 2 / ellipticMoment a 0) -
        (ellipticFDMoment a N 2 - ellipticFDMoment a N 1 ^ 2 / ellipticFDMoment a N 0)| ≤
        1 / 3 * (1 / (N : ℝ)) ^ 2 := by
  have hA0 := ellipticMoment_zero_pos ha0
  have hB0 := ellipticFDMoment_zero_pos ha0 hN
  obtain ⟨hA1, hA10⟩ := ellipticMoment_one_mem ha0
  obtain ⟨hB1, hB10⟩ := ellipticFDMoment_one_mem ha0 N
  have hmu := moment_gap_mem ha0 ha1 (div_nonneg hA1 hA0.le) ((div_le_one hA0).2 hA10) hN
  have hlam := moment_gap_mem ha0 ha1 (div_nonneg hB1 hB0.le) ((div_le_one hB0).2 hB10) hN
  exact ⟨le_quadratic_gap hA0 hB0 hmu.1, abs_quadratic_gap_le hA0 hB0 hlam.2 hmu.2⟩

/-! ### The exact output and its finite-difference approximation -/

/-- **The exact flux** (Giles 2015, §7.1).  For every classical solution `u` of `(c u′)′ = −f`,
`u(0) = u(1) = 0`, the flux `c u′` is affine, `c u′ = q − f x` on `(0, 1)`, and the boundary
condition `u(1) = u(0)` forces `q A₀ = f A₁`. -/
lemma hasDerivAt_of_isEllipticSol {a f : ℝ} (ha : 0 ≤ a) {u : ℝ → ℝ}
    (hu : IsEllipticSol a f u) :
    ∃ q : ℝ, q * ellipticMoment a 0 = f * ellipticMoment a 1 ∧
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u ((q - f * x) / (1 + a * x)) x := by
  obtain ⟨hcont, hdiff, hflux, hu0, hu1⟩ := hu
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < 1 + a * t := fun t ht => by nlinarith [mul_nonneg ha ht]
  -- the flux is affine
  have hF : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun y => (1 + a * y) * deriv u y + f * y) 0 x := fun x hx =>
    ((hflux x hx).add ((hasDerivAt_id' x).const_mul f)).congr_deriv (by ring)
  obtain ⟨q, hq⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx => (hF x hx).differentiableAt.differentiableWithinAt) (fun x hx => (hF x hx).deriv)
  -- so `u′ = (q − f x)/(1 + a x)`
  have hd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u ((q - f * x) / (1 + a * x)) x := by
    intro x hx
    have h1 := (hdiff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
    have h3 : (1 + a * x) * deriv u x + f * x = q := hq x hx
    have h2 : deriv u x = (q - f * x) / (1 + a * x) := by
      rw [eq_div_iff (hpos x hx.1.le).ne']
      linarith
    rwa [h2] at h1
  have hgi : IntervalIntegrable (fun t => (q - f * t) / (1 + a * t)) volume 0 1 :=
    intervalIntegrable_div_affine ha (by fun_prop) zero_le_one
  have hg : ∫ t in (0 : ℝ)..1, (q - f * t) / (1 + a * t) =
      q * ellipticMoment a 0 - f * ellipticMoment a 1 := by
    calc ∫ t in (0 : ℝ)..1, (q - f * t) / (1 + a * t) =
          ∫ t in (0 : ℝ)..1, (q + -f * t + 0 * t ^ 2) / (1 + a * t) := by
          congr 1
          funext t
          ring
      _ = _ := integral_quadratic_div ha q (-f) 0
      _ = _ := by ring
  -- the boundary condition `u(1) = 0`
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hd hgi
  rw [hu1, hu0, sub_zero, hg] at hftc
  exact ⟨q, by linarith, hd⟩

/-- **The exact output** (Giles 2015, §7.1).  For every classical solution `u` of
`(c u′)′ = −f`, `u(0) = u(1) = 0`, with the flux `c u′ = q − f x`, `q A₀ = f A₁`,
`∫₀¹ u = f A₂ − q A₁` (integration by parts: `∫₀¹ u = ∫₀¹ (1 − x) u′(x) dx`). -/
lemma integral_of_isEllipticSol {a f : ℝ} (ha : 0 ≤ a) {u : ℝ → ℝ} (hu : IsEllipticSol a f u) :
    ∃ q : ℝ, q * ellipticMoment a 0 = f * ellipticMoment a 1 ∧
      ∫ x in (0 : ℝ)..1, u x = f * ellipticMoment a 2 - q * ellipticMoment a 1 := by
  obtain ⟨q, hq, hd⟩ := hasDerivAt_of_isEllipticSol ha hu
  obtain ⟨hcont, -, -, hu0, hu1⟩ := hu
  -- integration by parts
  have hv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun y => (y - 1) * u y)
      (u x + (x - 1) * ((q - f * x) / (1 + a * x))) x := fun x hx =>
    (((hasDerivAt_id' x).sub_const 1).mul (hd x hx)).congr_deriv (by ring)
  have hvc : ContinuousOn (fun y => (y - 1) * u y) (Set.Icc 0 1) :=
    (continuousOn_id.sub continuousOn_const).mul hcont
  have hui : IntervalIntegrable u volume 0 1 := hcont.intervalIntegrable_of_Icc zero_le_one
  have ew : (fun x => (x - 1) * ((q - f * x) / (1 + a * x))) =
      fun x => (-q + (q + f) * x + -f * x ^ 2) / (1 + a * x) := by
    funext x
    ring
  have hwi : IntervalIntegrable (fun x => (x - 1) * ((q - f * x) / (1 + a * x))) volume 0 1 := by
    rw [ew]
    exact intervalIntegrable_div_affine ha (by fun_prop) zero_le_one
  have hparts := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hvc hv
    (hui.add hwi)
  rw [intervalIntegral.integral_add hui hwi, ew, integral_quadratic_div ha, hu1, hu0] at hparts
  exact ⟨q, hq, by linarith⟩

/-- **The finite-difference output** (Giles 2015, §7.1).  For every solution `U` of the scheme
on `N ≥ 1` cells, the discrete flux is `c(x_{i+½})(U_{i+1} − U_i)/h = D − f x_{i+½}` with
`D B₀ = f B₁`, and the trapezoidal rule gives `P_ℓ = f B₂ − D B₁` (summation by parts). -/
lemma output_of_isEllipticFD {a f : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N) {U : ℕ → ℝ}
    (hU : IsEllipticFD a f N U) :
    ∃ D : ℝ, D * ellipticFDMoment a N 0 = f * ellipticFDMoment a N 1 ∧
      (∀ i < N, U (i + 1) - U i = 1 / (N : ℝ) * (D - f * (((i : ℝ) + 1 / 2) / N)) /
        (1 + a * (((i : ℝ) + 1 / 2) / N))) ∧
      ellipticFDOutput N U = f * ellipticFDMoment a N 2 - D * ellipticFDMoment a N 1 := by
  obtain ⟨h0, hNU, hj⟩ := hU
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  -- the discrete flux decreases by `f h²` from one cell to the next
  have hR : ∀ i < N, (1 + a * (((i : ℝ) + 1 / 2) / N)) * (U (i + 1) - U i) =
      (1 + a * ((((0 : ℕ) : ℝ) + 1 / 2) / N)) * (U (0 + 1) - U 0) -
        f * (1 / (N : ℝ)) ^ 2 * i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h := hj (i + 1) (Nat.succ_pos i) hi
      rw [div_eq_iff (by positivity), Nat.add_sub_cancel] at h
      have h' := ih (by omega)
      push_cast at h h' ⊢
      linear_combination h + h'
  set R₀ : ℝ := (1 + a * ((((0 : ℕ) : ℝ) + 1 / 2) / N)) * (U (0 + 1) - U 0)
  set D : ℝ := (N : ℝ) * (R₀ + f * (1 / (N : ℝ)) ^ 2 / 2) with hD
  have hinc : ∀ i < N, U (i + 1) - U i = 1 / (N : ℝ) * (D - f * (((i : ℝ) + 1 / 2) / N)) /
      (1 + a * (((i : ℝ) + 1 / 2) / N)) := by
    intro i hi
    rw [eq_div_iff (ellipticMidpoint_mem ha hi).2.2.ne', mul_comm, hR i hi, hD]
    field_simp
    ring
  -- the boundary condition `U_N = 0`
  have hsum : ∑ i ∈ range N, (U (i + 1) - U i) =
      D * ellipticFDMoment a N 0 - f * ellipticFDMoment a N 1 := by
    calc ∑ i ∈ range N, (U (i + 1) - U i) = ∑ i ∈ range N, 1 / (N : ℝ) *
          (D + -f * (((i : ℝ) + 1 / 2) / N) + 0 * (((i : ℝ) + 1 / 2) / N) ^ 2) /
            (1 + a * (((i : ℝ) + 1 / 2) / N)) :=
          sum_congr rfl fun i hi => by rw [hinc i (mem_range.1 hi)]; ring
      _ = _ := sum_quadratic_div a N D (-f) 0
      _ = _ := by ring
  rw [Finset.sum_range_sub, hNU, h0, sub_zero] at hsum
  -- summation by parts
  have hout : ellipticFDOutput N U = 1 / (N : ℝ) * ∑ j ∈ range N, U (j + 1) := by
    unfold ellipticFDOutput
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel, sum_range_succ, h0, hNU]
    ring
  have hv : ∑ j ∈ range N, ((((j + 1 : ℕ) : ℝ) / N - 1) * U (j + 1) - ((j : ℝ) / N - 1) * U j) =
      (((N : ℕ) : ℝ) / N - 1) * U N - (((0 : ℕ) : ℝ) / N - 1) * U 0 :=
    Finset.sum_range_sub (fun j : ℕ => ((j : ℝ) / N - 1) * U j) N
  rw [hNU, h0, mul_zero, mul_zero, sub_zero] at hv
  have e : ∀ j ∈ range N, ((((j + 1 : ℕ) : ℝ) / N - 1) * U (j + 1) - ((j : ℝ) / N - 1) * U j) =
      1 / (N : ℝ) * U (j + 1) - (1 - (j : ℝ) / N) * (U (j + 1) - U j) := fun j _ => by
    push_cast
    ring
  rw [sum_congr rfl e, sum_sub_distrib, ← mul_sum] at hv
  have h2 : ∑ j ∈ range N, (1 - (j : ℝ) / N) * (U (j + 1) - U j) =
      (1 + 1 / (2 * N)) * D * ellipticFDMoment a N 0 +
        (-((1 + 1 / (2 * N)) * f) - D) * ellipticFDMoment a N 1 + f * ellipticFDMoment a N 2 := by
    rw [← sum_quadratic_div]
    refine sum_congr rfl fun j hj => ?_
    rw [hinc j (mem_range.1 hj)]
    ring
  refine ⟨D, by linarith, hinc, ?_⟩
  rw [hout]
  linear_combination hv + h2 - (1 + 1 / (2 * (N : ℝ))) * hsum

/-- **The error is the forcing times the gap of the minima** (Giles 2015, §7.1).  For every
classical solution `u` and every solution `U` of the scheme on `N ≥ 1` cells,
`∫₀¹ u − P_h = f ((A₂ − A₁²/A₀) − (B₂ − B₁²/B₀))`: the error is linear in the forcing. -/
lemma integral_sub_ellipticFDOutput {a f : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N) {u : ℝ → ℝ}
    (hu : IsEllipticSol a f u) {U : ℕ → ℝ} (hU : IsEllipticFD a f N U) :
    (∫ x in (0 : ℝ)..1, u x) - ellipticFDOutput N U =
      f * ((ellipticMoment a 2 - ellipticMoment a 1 ^ 2 / ellipticMoment a 0) -
        (ellipticFDMoment a N 2 - ellipticFDMoment a N 1 ^ 2 / ellipticFDMoment a N 0)) := by
  obtain ⟨q, hq, hP⟩ := integral_of_isEllipticSol ha hu
  obtain ⟨D, hD, -, hPl⟩ := output_of_isEllipticFD ha hN hU
  have hq' : q = f * ellipticMoment a 1 / ellipticMoment a 0 := by
    rw [eq_div_iff (ellipticMoment_zero_pos ha).ne']
    exact hq
  have hD' : D = f * ellipticFDMoment a N 1 / ellipticFDMoment a N 0 := by
    rw [eq_div_iff (ellipticFDMoment_zero_pos ha hN).ne']
    exact hD
  rw [hP, hPl, hq', hD']
  ring

/-! ### Existence and uniqueness -/

/-- **The exact solution** of the elliptic example (Giles 2015, §7.1, p. 49: "`d/dx(c(x) du/dx) =
−50 Z²` on `0 < x < 1`, with boundary data `u(0) = u(1) = 0` … `c(x) = 1 + a x`").  For `a ≥ 0`
and every forcing `f`, `u(x) = ∫₀ˣ (q − f t)/(1 + a t) dt` with `q = f A₁/A₀` is a classical
solution. -/
theorem isEllipticSol_ellipticSol {a : ℝ} (ha : 0 ≤ a) (f : ℝ) :
    IsEllipticSol a f (ellipticSol a f) := by
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < 1 + a * t := fun t ht => by nlinarith [mul_nonneg ha ht]
  have hA0 := ellipticMoment_zero_pos ha
  set q := f * ellipticMoment a 1 / ellipticMoment a 0 with hq
  have hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt (ellipticSol a f) ((q - f * x) / (1 + a * x)) x := by
    intro x hx
    have hi : IntervalIntegrable (fun t => (q - f * t) / (1 + a * t)) volume 0 x :=
      intervalIntegrable_div_affine ha (by fun_prop) hx
    have hm : Measurable fun t : ℝ => (q - f * t) / (1 + a * t) := by fun_prop
    have hc : ContinuousAt (fun t : ℝ => (q - f * t) / (1 + a * t)) x :=
      ContinuousAt.div₀ (by fun_prop) (by fun_prop) (hpos x hx).ne'
    exact intervalIntegral.integral_hasDerivAt_right hi
      hm.stronglyMeasurable.stronglyMeasurableAtFilter hc
  refine ⟨fun x hx => (hd x hx.1).continuousAt.continuousWithinAt,
    fun x hx => (hd x hx.1.le).differentiableAt.differentiableWithinAt, fun x hx => ?_,
    intervalIntegral.integral_same, ?_⟩
  · have hev : (fun y => (1 + a * y) * deriv (ellipticSol a f) y) =ᶠ[nhds x]
        fun y => q - f * y := by
      filter_upwards [Ioi_mem_nhds hx.1] with y hy
      rw [(hd y (le_of_lt hy)).deriv]
      field_simp [(hpos y (le_of_lt hy)).ne']
    exact ((((hasDerivAt_id' x).const_mul f).const_sub q).congr_deriv
      (by ring)).congr_of_eventuallyEq hev
  · show ∫ t in (0 : ℝ)..1, (q - f * t) / (1 + a * t) = 0
    calc ∫ t in (0 : ℝ)..1, (q - f * t) / (1 + a * t) =
          ∫ t in (0 : ℝ)..1, (q + -f * t + 0 * t ^ 2) / (1 + a * t) := by
          congr 1
          funext t
          ring
      _ = _ := integral_quadratic_div ha q (-f) 0
      _ = 0 := by rw [hq]; field_simp; ring

/-- **Uniqueness of the exact solution** (Giles 2015, §7.1, p. 49: "The equation is
`d/dx(c(x) du/dx) = −50 Z²` on `0 < x < 1`, with boundary data `u(0) = u(1) = 0` … The output
quantity of interest is chosen to be `P = ∫₀¹ u(x) dx`").  For `a ≥ 0`, every classical solution
of `(c u′)′ = −f`, `u(0) = u(1) = 0`, agrees with `ellipticSol` on `[0, 1]`, so its output
`∫₀¹ u` is `ellipticP a f`: `P` is well defined. -/
theorem eq_ellipticSol_of_isEllipticSol {a f : ℝ} (ha : 0 ≤ a) {u : ℝ → ℝ}
    (hu : IsEllipticSol a f u) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, u x = ellipticSol a f x) ∧
      ∫ x in (0 : ℝ)..1, u x = ellipticP a f := by
  obtain ⟨q, hq, hd⟩ := hasDerivAt_of_isEllipticSol ha hu
  have hq' : q = f * ellipticMoment a 1 / ellipticMoment a 0 := by
    rw [eq_div_iff (ellipticMoment_zero_pos ha).ne']
    exact hq
  have heq : ∀ x ∈ Set.Icc (0 : ℝ) 1, u x = ellipticSol a f x := by
    intro x hx
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (hu.1.mono (Set.Icc_subset_Icc_right hx.2)) (fun y hy => hd y ⟨hy.1, hy.2.trans_le hx.2⟩)
      (intervalIntegrable_div_affine ha (by fun_prop) hx.1)
    rw [hu.2.2.2.1, sub_zero, hq'] at h
    exact h.symm
  refine ⟨heq, intervalIntegral.integral_congr fun x hx => ?_⟩
  rw [Set.uIcc_of_le zero_le_one] at hx
  exact heq x hx

/-- The increments of the exact finite-difference solution:
`U_{i+1} − U_i = h (D − f x_{i+½})/(1 + a x_{i+½})` with `D = f B₁/B₀`. -/
lemma ellipticFDSol_succ_sub (a f : ℝ) (N i : ℕ) :
    ellipticFDSol a f N (i + 1) - ellipticFDSol a f N i = 1 / (N : ℝ) *
      (f * ellipticFDMoment a N 1 / ellipticFDMoment a N 0 - f * (((i : ℝ) + 1 / 2) / N)) /
        (1 + a * (((i : ℝ) + 1 / 2) / N)) := by
  unfold ellipticFDSol
  rw [sum_range_succ]
  ring

/-- **The exact finite-difference solution** (Giles 2015, §7.1, p. 49: "Level `ℓ` uses a uniform
grid … A simple second order central difference approximation is used").  For `a ≥ 0`, every
forcing `f` and `N ≥ 1` cells, `U_j = h ∑_{i<j} (D − f x_{i+½})/(1 + a x_{i+½})` with
`D = f B₁/B₀` solves the scheme. -/
theorem isEllipticFD_ellipticFDSol {a : ℝ} (ha : 0 ≤ a) (f : ℝ) {N : ℕ} (hN : 0 < N) :
    IsEllipticFD a f N (ellipticFDSol a f N) := by
  have hB0 := ellipticFDMoment_zero_pos ha hN
  refine ⟨sum_range_zero _, ?_, fun j hj hjN => ?_⟩
  · unfold ellipticFDSol
    calc _ = ∑ i ∈ range N, 1 / (N : ℝ) *
          (f * ellipticFDMoment a N 1 / ellipticFDMoment a N 0 + -f * (((i : ℝ) + 1 / 2) / N) +
            0 * (((i : ℝ) + 1 / 2) / N) ^ 2) / (1 + a * (((i : ℝ) + 1 / 2) / N)) :=
          sum_congr rfl fun i _ => by ring
      _ = _ := sum_quadratic_div a N _ (-f) 0
      _ = 0 := by field_simp; ring
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, ellipticFDSol_succ_sub, ellipticFDSol_succ_sub]
    have e : ((k + 1 : ℕ) : ℝ) - 1 / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
    rw [e]
    field_simp
    push_cast
    ring

/-- **Uniqueness of the finite-difference solution** (Giles 2015, §7.1, p. 49: "Level `ℓ` uses a
uniform grid with spacing `h_ℓ = 2^{−(ℓ+1)}` … A simple second order central difference
approximation is used").  For `a ≥ 0` and `N ≥ 1` cells, `U` solves the scheme if and only if it
agrees with `ellipticFDSol` at the nodes `0, …, N`, so `P_ℓ` is well defined. -/
theorem isEllipticFD_iff {a : ℝ} (ha : 0 ≤ a) (f : ℝ) {N : ℕ} (hN : 0 < N) (U : ℕ → ℝ) :
    IsEllipticFD a f N U ↔ ∀ j ≤ N, U j = ellipticFDSol a f N j := by
  constructor
  · intro hU
    have hB0 := ellipticFDMoment_zero_pos ha hN
    obtain ⟨D, hD, hinc, -⟩ := output_of_isEllipticFD ha hN hU
    have hD' : D = f * ellipticFDMoment a N 1 / ellipticFDMoment a N 0 := by
      rw [eq_div_iff hB0.ne']
      exact hD
    intro j
    induction j with
    | zero => intro _; exact hU.1.trans (sum_range_zero _).symm
    | succ j ih =>
      intro hj
      have h1 := hinc j (by omega)
      have h2 := ellipticFDSol_succ_sub a f N j
      rw [← hD', ← ih (by omega)] at h2
      linarith
  · intro h
    obtain ⟨h0, hN', hj⟩ := isEllipticFD_ellipticFDSol ha f hN
    refine ⟨(h 0 (Nat.zero_le _)).trans h0, (h N le_rfl).trans hN', fun j hj0 hjN => ?_⟩
    rw [h (j + 1) hjN, h j hjN.le, h (j - 1) (by omega)]
    exact hj j hj0 hjN

/-- **The scheme is the finite-element method with one-point quadrature** (Giles 2015, §7.1,
p. 49: "A simple second order central difference approximation is used (equivalent to a finite
element approximation with a 1-point quadrature)").  `U` solves the scheme on `N` cells if and
only if `U_0 = U_N = 0` and, at every interior node `0 < j < N`, the stiffness row of the
piecewise-linear finite elements with the midpoint quadrature for `−(c u′)′ = f`,
`c(x) = 1 + a x`, on the mesh of size `h = 1/N` equals the load row (`feStiffness`, `feLoad` of
`MlmcLean.ApplicationExtras`; this is `fe_eq_centralDiff`).  (As `c` is affine, `c(x_{j±½})` is
also the average of the nodal values of `c`.) -/
theorem isEllipticFD_iff_fe (a f : ℝ) (N : ℕ) (U : ℕ → ℝ) :
    IsEllipticFD a f N U ↔ U 0 = 0 ∧ U N = 0 ∧ ∀ j : ℕ, 0 < j → j < N →
      feStiffness N (1 / N) (fun x => 1 + a * x) U j = feLoad N (1 / N) (fun _ => f) j := by
  refine and_congr_right' (and_congr_right' (forall_congr' fun j => imp_congr_right fun hj0 =>
    imp_congr_right fun hjN => ?_))
  have hh : (1 / (N : ℝ)) ≠ 0 := one_div_ne_zero (Nat.cast_pos.2 (by omega)).ne'
  obtain ⟨hs, hl⟩ := fe_eq_centralDiff (c := fun x => 1 + a * x) (f := fun _ => f) (u := U) hj0
    hjN hh
  rw [hs, hl, mul_right_inj' hh, neg_div, mul_one_div, mul_one_div,
    show (f + f) / 2 = f by ring, neg_eq_iff_eq_neg]

/-! ### Second-order accuracy -/

/-- **Uniform second-order accuracy of the elliptic example** (Giles 2015, §7.1, p. 49: "A
simple second order central difference approximation is used … The uniform second order accuracy
means that there is a constant `K` such that `|P − P_ℓ| < K h_ℓ²` …").  For every coefficient
`c(x) = 1 + a x` with `a ∈ [0, 1]`, every forcing `f`, every classical solution `u` of
`(c u′)′ = −f`, `u(0) = u(1) = 0`, and every solution `U` of the scheme on `N ≥ 1` cells,
`|∫₀¹ u − P_h| ≤ (|f|/3) h²`, `h = 1/N`, where `P_h` is the trapezoidal rule for the grid values.
We read "uniform" as uniform in the random coefficient: the constant does not depend on
`a ∈ [0, 1]` (it is proportional to `|f|`, and for `f = 50 Z²` it is the random constant
`(50/3) Z²` of `ellipticPl_error`).  As the paper's conclusion is about the output `P`, we bound
`P − P_h` directly; the nodal errors `max_j |u(x_j) − U_j|` (the max-norm reading of "uniform")
obey the same bound (`ellipticFD_nodal_error`).  We state `≤` for our explicit constant, which
vanishes with `f`; every larger constant gives the paper's `<`.  The constant `1/3` is not sharp
(numerically the best one is `1/12`, attained at `a = 0`), but the order `h²` is
(`ellipticFD_error_ge`). -/
theorem ellipticFD_error {a f : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {N : ℕ} (hN : 0 < N)
    {u : ℝ → ℝ} (hu : IsEllipticSol a f u) {U : ℕ → ℝ} (hU : IsEllipticFD a f N U) :
    |(∫ x in (0 : ℝ)..1, u x) - ellipticFDOutput N U| ≤ |f| / 3 * (1 / (N : ℝ)) ^ 2 := by
  rw [integral_sub_ellipticFDOutput ha0 hN hu hU, abs_mul]
  calc _ ≤ |f| * (1 / 3 * (1 / (N : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left (ellipticGap_mem ha0 ha1 hN).2 (abs_nonneg f)
    _ = |f| / 3 * (1 / (N : ℝ)) ^ 2 := by ring

/-- **The error is exactly of second order** (Giles 2015, §7.1, p. 49: "A simple second order
central difference approximation is used … The uniform second order accuracy means that there is
a constant `K` such that `|P − P_ℓ| < K h_ℓ²` …").  Under the hypotheses of `ellipticFD_error`,
also `(|f|/96) h² ≤ |∫₀¹ u − P_h|`, `h = 1/N`: the midpoint rule underestimates
`∫₀¹ (t − ν)²/c(t) dt` by at least `h²/96`, because the second derivative of the weight is at
least `1/4`.  So the order `2` cannot be improved, and for `f ≠ 0` the error never vanishes
(numerically `|∫₀¹ u − P_h|/(|f| h²)` lies between `0.057` and `1/12`). -/
theorem ellipticFD_error_ge {a f : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {N : ℕ} (hN : 0 < N)
    {u : ℝ → ℝ} (hu : IsEllipticSol a f u) {U : ℕ → ℝ} (hU : IsEllipticFD a f N U) :
    |f| / 96 * (1 / (N : ℝ)) ^ 2 ≤ |(∫ x in (0 : ℝ)..1, u x) - ellipticFDOutput N U| := by
  rw [integral_sub_ellipticFDOutput ha0 hN hu hU, abs_mul]
  calc |f| / 96 * (1 / (N : ℝ)) ^ 2 = |f| * (1 / 96 * (1 / (N : ℝ)) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
        ((ellipticGap_mem ha0 ha1 hN).1.trans (le_abs_self _)) (abs_nonneg f)

/-- If `|I − (U + c S)| ≤ ε`, `|c| T ≤ ε` and `0 ≤ S ≤ T`, then `|I − U| ≤ 2ε` (the splitting of
the nodal error in `ellipticFD_nodal_error`). -/
lemma abs_sub_le_two_mul_of_split {I U c S T ε : ℝ} (h1 : |I - (U + c * S)| ≤ ε)
    (h2 : |c| * T ≤ ε) (hS : 0 ≤ S) (hST : S ≤ T) : |I - U| ≤ 2 * ε := by
  have e : I - U = (I - (U + c * S)) + c * S := by ring
  rw [e]
  calc |(I - (U + c * S)) + c * S| ≤ |I - (U + c * S)| + |c * S| := abs_add_le _ _
    _ = |I - (U + c * S)| + |c| * S := by rw [abs_mul, abs_of_nonneg hS]
    _ ≤ ε + |c| * T := add_le_add h1 (mul_le_mul_of_nonneg_left hST (abs_nonneg c))
    _ ≤ 2 * ε := by linarith

/-- **Uniform second-order accuracy at the nodes** (Giles 2015, §7.1, p. 49: "A simple second
order central difference approximation is used … The uniform second order accuracy means that
there is a constant `K` such that `|P − P_ℓ| < K h_ℓ²` …").  In the max-norm reading of
"uniform": for `a ∈ [0, 1]`, every forcing `f`, every classical solution `u`, every solution `U`
of the scheme on `N ≥ 1` cells and every node `x_j = j h`, `j ≤ N`, `h = 1/N`,
`|u(x_j) − U_j| ≤ (|f|/3) h²`.  Both `u(x_j)` and `U_j` integrate the flux quotient
`g(t) = (q − f t)/c(t)`, exactly and by the midpoint rule with the discrete flux constant `D`
instead of `q`; the midpoint rule for `g` (`|g″| ≤ 4|f|`) and the two boundary conditions
`u(1) = U_N = 0` bound both parts by `(|f|/6) h²`.  (Numerically the best constant is below
`0.008`; at `a = 0` the scheme is exact at the nodes.) -/
theorem ellipticFD_nodal_error {a f : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {N : ℕ} (hN : 0 < N)
    {u : ℝ → ℝ} (hu : IsEllipticSol a f u) {U : ℕ → ℝ} (hU : IsEllipticFD a f N U) {j : ℕ}
    (hj : j ≤ N) : |u ((j : ℝ) / N) - U j| ≤ |f| / 3 * (1 / (N : ℝ)) ^ 2 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < 1 + a * t := fun t ht => by nlinarith [mul_nonneg ha0 ht]
  have hA0 := ellipticMoment_zero_pos ha0
  obtain ⟨hA1, hA10⟩ := ellipticMoment_one_mem ha0
  set q := f * ellipticMoment a 1 / ellipticMoment a 0 with hq
  set D := f * ellipticFDMoment a N 1 / ellipticFDMoment a N 0
  -- `|q| ≤ |f|`, so `|g″| ≤ 4|f|`
  have hqf : |q| ≤ |f| := by
    have hμ : |ellipticMoment a 1 / ellipticMoment a 0| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hA1 hA0.le)]
      exact (div_le_one hA0).2 hA10
    rw [hq, mul_div_assoc, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg f) hμ
  have hmid : ∀ k ≤ N, |(∫ t in (0 : ℝ)..(k : ℝ) / N, (q - f * t) / (1 + a * t)) -
      ∑ i ∈ range k, 1 / (N : ℝ) * ((q - f * (((i : ℝ) + 1 / 2) / N)) /
        (1 + a * (((i : ℝ) + 1 / 2) / N)))| ≤ 4 * |f| / 24 * (1 / (N : ℝ)) ^ 2 := fun k hk =>
    abs_integral_sub_midpoint_sum_le (φ := fun t => (q - f * t) / (1 + a * t)) (by fun_prop)
      (fun t ht => hasDerivAt_affine_div a q f (hpos t ht.1).ne')
      (fun t ht => hasDerivAt_affine_div_deriv a q f (hpos t ht.1).ne')
      (fun t ht => (abs_affine_div_deriv2_le ha0 ha1 ht.1).trans (by linarith)) hN hk
  -- the exact and the discrete solution at the nodes, and the boundary conditions at `x = 1`
  have hu' : u ((j : ℝ) / N) = ∫ t in (0 : ℝ)..(j : ℝ) / N, (q - f * t) / (1 + a * t) :=
    (eq_ellipticSol_of_isEllipticSol ha0 hu).1 _
      ⟨by positivity, (div_le_one hNr).2 (by exact_mod_cast hj)⟩
  have hU' : U j = ∑ i ∈ range j, 1 / (N : ℝ) * (D - f * (((i : ℝ) + 1 / 2) / N)) /
      (1 + a * (((i : ℝ) + 1 / 2) / N)) := (isEllipticFD_iff ha0 f hN U).1 hU j hj
  have h1 : ∫ t in (0 : ℝ)..(N : ℝ) / N, (q - f * t) / (1 + a * t) = 0 := by
    rw [div_self hNr.ne']
    exact (isEllipticSol_ellipticSol ha0 f).2.2.2.2
  have hN0 : ∑ i ∈ range N, 1 / (N : ℝ) * (D - f * (((i : ℝ) + 1 / 2) / N)) /
      (1 + a * (((i : ℝ) + 1 / 2) / N)) = 0 := (isEllipticFD_ellipticFDSol ha0 f hN).2.1
  -- the midpoint rule for `g` is the discrete solution plus `(q − D)` times a positive sum
  have key : ∀ k : ℕ, ∑ i ∈ range k, 1 / (N : ℝ) * ((q - f * (((i : ℝ) + 1 / 2) / N)) /
        (1 + a * (((i : ℝ) + 1 / 2) / N))) =
      ∑ i ∈ range k, 1 / (N : ℝ) * (D - f * (((i : ℝ) + 1 / 2) / N)) /
          (1 + a * (((i : ℝ) + 1 / 2) / N)) +
        (q - D) * ∑ i ∈ range k, 1 / (N : ℝ) / (1 + a * (((i : ℝ) + 1 / 2) / N)) := by
    intro k
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hS0 : 0 ≤ ∑ i ∈ range j, 1 / (N : ℝ) / (1 + a * (((i : ℝ) + 1 / 2) / N)) :=
    sum_nonneg fun i _ => by positivity
  have hSN : ∑ i ∈ range j, 1 / (N : ℝ) / (1 + a * (((i : ℝ) + 1 / 2) / N)) ≤
      ∑ i ∈ range N, 1 / (N : ℝ) / (1 + a * (((i : ℝ) + 1 / 2) / N)) :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hj) fun i _ _ => by positivity
  -- at `j = N` the boundary conditions give `|q − D| S_N ≤ (|f|/6) h²`
  have hEN := hmid N le_rfl
  rw [key, h1, hN0, zero_add, zero_sub, abs_neg, abs_mul, abs_of_nonneg (hS0.trans hSN)] at hEN
  have hEj := hmid j hj
  rw [key] at hEj
  rw [hu', hU']
  calc _ ≤ 2 * (4 * |f| / 24 * (1 / (N : ℝ)) ^ 2) :=
        abs_sub_le_two_mul_of_split hEj hEN hS0 hSN
    _ = |f| / 3 * (1 / (N : ℝ)) ^ 2 := by ring

/-- **The level-`ℓ` error of the elliptic example with a random constant** (Giles 2015, §7.1,
p. 49: "Level `ℓ` uses a uniform grid with spacing `h_ℓ = 2^{−(ℓ+1)}` … there is a constant `K`
such that `|P − P_ℓ| < K h_ℓ²` …").  For the forcing `50 Z²` and every `a ∈ [0, 1]`,
`|P − P_ℓ| ≤ K h_ℓ²` with `K = (50/3) Z²`.  The constant must depend on `Z`: no deterministic
`K` bounds the error almost surely (`not_ae_abs_ellipticP_sub_le`). -/
theorem ellipticPl_error {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (Z : ℝ) (ℓ : ℕ) :
    |ellipticP a (50 * Z ^ 2) - ellipticPl a (50 * Z ^ 2) ℓ| ≤
      50 / 3 * Z ^ 2 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 := by
  have hN : 0 < 2 ^ (ℓ + 1) := by positivity
  have h := ellipticFD_error ha0 ha1 hN (isEllipticSol_ellipticSol ha0 (50 * Z ^ 2))
    (isEllipticFD_ellipticFDSol ha0 (50 * Z ^ 2) hN)
  have e : 1 / ((2 ^ (ℓ + 1) : ℕ) : ℝ) = (1 / 2 : ℝ) ^ (ℓ + 1) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, one_div_pow]
  rw [e, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 50 * Z ^ 2)] at h
  calc |ellipticP a (50 * Z ^ 2) - ellipticPl a (50 * Z ^ 2) ℓ|
      ≤ 50 * Z ^ 2 / 3 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 := h
    _ = 50 / 3 * Z ^ 2 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 := by ring

/-- The lower bound `(50/96) Z² h_ℓ² ≤ |P − P_ℓ|` for the forcing `50 Z²` and `a ∈ [0, 1]`
(`ellipticFD_error_ge` on level `ℓ`; Giles 2015, §7.1). -/
lemma ellipticPl_error_ge {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (Z : ℝ) (ℓ : ℕ) :
    50 / 96 * Z ^ 2 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 ≤
      |ellipticP a (50 * Z ^ 2) - ellipticPl a (50 * Z ^ 2) ℓ| := by
  have hN : 0 < 2 ^ (ℓ + 1) := by positivity
  have h := ellipticFD_error_ge ha0 ha1 hN (isEllipticSol_ellipticSol ha0 (50 * Z ^ 2))
    (isEllipticFD_ellipticFDSol ha0 (50 * Z ^ 2) hN)
  have e : 1 / ((2 ^ (ℓ + 1) : ℕ) : ℝ) = (1 / 2 : ℝ) ^ (ℓ + 1) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, one_div_pow]
  rw [e, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 50 * Z ^ 2)] at h
  calc 50 / 96 * Z ^ 2 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2
      = 50 * Z ^ 2 / 96 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 := by ring
    _ ≤ |ellipticP a (50 * Z ^ 2) - ellipticPl a (50 * Z ^ 2) ℓ| := h

/-! ### The random constant and the rates -/

/-- **The random constant has finite moments** (Giles 2015, §7.1, p. 49, with the paper's
"`Z` is a Normal random variable with zero mean and unit variance").  For `Z ~ N(0, 1)` the
constant `K = (50/3) Z²` of `ellipticPl_error` is square integrable, with `E[K] = 50/3` and
`E[K²] = 2500/3` (from `E[Z²] = 1`, `E[Z⁴] = 3`). -/
theorem ellipticK_moments {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    MemLp (fun ω => 50 / 3 * Z ω ^ 2) 2 μ ∧ ∫ ω, 50 / 3 * Z ω ^ 2 ∂μ = 50 / 3 ∧
      ∫ ω, (50 / 3 * Z ω ^ 2) ^ 2 ∂μ = 2500 / 3 := by
  have h4 : Integrable (fun x : ℝ => x ^ 4) (Measure.map Z μ) := by
    rw [hZ.map_eq]
    exact integrable_pow_gaussian 4
  have h4Z : Integrable (fun ω => Z ω ^ 4) μ := h4.comp_aemeasurable hZ.aemeasurable
  have hm : AEStronglyMeasurable (fun ω => 50 / 3 * Z ω ^ 2) μ :=
    ((hZ.aemeasurable.pow_const 2).const_mul _).aestronglyMeasurable
  have i2 : ∫ ω, Z ω ^ 2 ∂μ = 1 := by
    rw [← integral_sq_gaussian]
    exact hZ.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  have i4 : ∫ ω, Z ω ^ 4 ∂μ = 3 := by
    rw [← integral_pow_four_gaussian]
    exact hZ.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  have e : (fun ω => (50 / 3 * Z ω ^ 2) ^ 2) = fun ω => 2500 / 9 * Z ω ^ 4 := by
    funext ω
    ring
  refine ⟨(memLp_two_iff_integrable_sq hm).2 ?_, ?_, ?_⟩
  · rw [e]
    exact h4Z.const_mul _
  · rw [integral_const_mul, i2]
    norm_num
  · rw [e, integral_const_mul, i4]
    norm_num

/-- **No deterministic constant** (Giles 2015, §7.1, p. 49: "there is a constant `K` such that
`|P − P_ℓ| < K h_ℓ²`", for the forcing `−50 Z²` where "`Z` is a Normal random variable with zero
mean and unit variance").  Let `a` take values in `[0, 1]` almost surely (with any law, dependent
on `Z` or not) and let `Z ~ N(0, 1)`.  Then on no level `ℓ` does a deterministic `K` satisfy
`|P − P_ℓ| ≤ K h_ℓ²` almost surely, since the error is at least `(50/96) Z² h_ℓ²`
(`ellipticFD_error_ge`) and `Z²` is unbounded (`not_ae_abs_gaussian_sq_mul_le`).  So the paper's
`K` has to be read as a random constant, as in `ellipticPl_error` and `elliptic_fd_rates`. -/
theorem not_ae_abs_ellipticP_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a Z : Ω → ℝ} (ha01 : ∀ᵐ ω ∂μ, a ω ∈ Set.Icc (0 : ℝ) 1)
    (hZ : HasLaw Z (gaussianReal 0 1) μ) (ℓ : ℕ) (K : ℝ) :
    ¬ ∀ᵐ ω ∂μ, |ellipticP (a ω) (50 * Z ω ^ 2) - ellipticPl (a ω) (50 * Z ω ^ 2) ℓ| ≤
      K * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 := by
  intro h
  refine not_ae_abs_gaussian_sq_mul_le hZ (e := 50 / 96 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2)
    (by positivity) (K * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2) ?_
  filter_upwards [h, ha01] with ω h1 h2
  rw [abs_of_nonneg (by positivity)]
  calc Z ω ^ 2 * (50 / 96 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2) =
        50 / 96 * Z ω ^ 2 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 := by ring
    _ ≤ _ := ellipticPl_error_ge h2.1 h2.2 (Z ω) ℓ
    _ ≤ _ := h1

/-- The closed form of the exact output: `P = f (A₂ − A₁²/A₀)` for `a ≥ 0`. -/
lemma ellipticP_eq {a : ℝ} (ha : 0 ≤ a) (f : ℝ) :
    ellipticP a f = f * (ellipticMoment a 2 - ellipticMoment a 1 ^ 2 / ellipticMoment a 0) := by
  obtain ⟨q, hq, hP⟩ := integral_of_isEllipticSol ha (isEllipticSol_ellipticSol ha f)
  have hq' : q = f * ellipticMoment a 1 / ellipticMoment a 0 := by
    rw [eq_div_iff (ellipticMoment_zero_pos ha).ne']
    exact hq
  show ∫ x in (0 : ℝ)..1, ellipticSol a f x = _
  rw [hP, hq']
  ring

/-- `a ↦ A_k(a) = ∫₀¹ tᵏ/(1 + a t) dt` is measurable. -/
lemma measurable_ellipticMoment (k : ℕ) : Measurable fun a => ellipticMoment a k := by
  have e : (fun a => ellipticMoment a k) =
      fun a => ∫ t, t ^ k / (1 + a * t) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    funext fun a => intervalIntegral.integral_of_le zero_le_one
  rw [e]
  exact (StronglyMeasurable.integral_prod_right (f := fun a t : ℝ => t ^ k / (1 + a * t))
    (by fun_prop : Measurable fun p : ℝ × ℝ => p.2 ^ k / (1 + p.1 * p.2)).stronglyMeasurable
    ).measurable

/-- `(a, f) ↦ P_ℓ` is measurable (a finite sum of rational functions). -/
lemma measurable_ellipticPl (ℓ : ℕ) : Measurable fun p : ℝ × ℝ => ellipticPl p.1 p.2 ℓ := by
  unfold ellipticPl ellipticFDOutput ellipticFDSol ellipticFDMoment
  fun_prop

/-- `|P| ≤ |f|` for `a ≥ 0`: `P = f (A₂ − A₁²/A₀)` with `0 ≤ A₂ ≤ A₁ ≤ A₀ ≤ 1`. -/
lemma abs_ellipticP_le {a : ℝ} (ha : 0 ≤ a) (f : ℝ) : |ellipticP a f| ≤ |f| := by
  have hA0 := ellipticMoment_zero_pos ha
  obtain ⟨hA1, -⟩ := ellipticMoment_one_mem ha
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < 1 + a * t := fun t ht => by nlinarith [mul_nonneg ha ht]
  have h01 : ellipticMoment a 0 ≤ 1 := by
    calc ellipticMoment a 0 ≤ ∫ _ in (0 : ℝ)..1, (1 : ℝ) :=
          intervalIntegral.integral_mono_on zero_le_one
            (intervalIntegrable_div_affine ha (continuous_pow 0) zero_le_one)
            intervalIntegrable_const fun t ht => by
              rw [pow_zero, div_le_one (hpos t ht.1)]
              nlinarith [mul_nonneg ha ht.1]
      _ = 1 := by simp
  have h10 := (ellipticMoment_one_mem ha).2
  have h2 : 0 ≤ ellipticMoment a 2 := intervalIntegral.integral_nonneg zero_le_one fun t ht =>
    div_nonneg (pow_nonneg ht.1 2) (hpos t ht.1).le
  have h21 : ellipticMoment a 2 ≤ ellipticMoment a 1 := by
    have h := integral_quadratic_div ha 0 1 (-1)
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (0 + 1 * t + -1 * t ^ 2) / (1 + a * t) :=
      intervalIntegral.integral_nonneg zero_le_one fun t ht =>
        div_nonneg (by nlinarith [ht.1, ht.2]) (hpos t ht.1).le
    linarith
  have hq : ellipticMoment a 1 ^ 2 / ellipticMoment a 0 ≤ ellipticMoment a 1 := by
    rw [div_le_iff₀ hA0]
    nlinarith
  have hq0 : 0 ≤ ellipticMoment a 1 ^ 2 / ellipticMoment a 0 := by positivity
  rw [ellipticP_eq ha, abs_mul]
  calc |f| * |ellipticMoment a 2 - ellipticMoment a 1 ^ 2 / ellipticMoment a 0| ≤ |f| * 1 :=
        mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg f)
    _ = |f| := mul_one _

/-- A function bounded by a multiple of `Z²`, `Z ~ N(0, 1)`, is square integrable
(`E[Z⁴] = 3 < ∞`, `ellipticK_moments`). -/
lemma memLp_two_of_abs_le_mul_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z g : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) (hg : AEStronglyMeasurable g μ) {C : ℝ}
    (h : ∀ᵐ ω ∂μ, |g ω| ≤ C * Z ω ^ 2) : MemLp g 2 μ := by
  refine ((ellipticK_moments hZ).1.const_mul (3 * C / 50)).of_le hg ?_
  filter_upwards [h] with ω hω
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  calc |g ω| ≤ C * Z ω ^ 2 := hω
    _ = 3 * C / 50 * (50 / 3 * Z ω ^ 2) := by ring
    _ ≤ |3 * C / 50 * (50 / 3 * Z ω ^ 2)| := le_abs_self _

/-- **The elliptic example has `α = 2` and `β = 4`, end to end** (Giles 2015, §7.1, p. 49: "The
uniform second order accuracy means that there is a constant `K` such that `|P − P_ℓ| < K h_ℓ²`
and therefore we have `α = 2`, `β = 4` …"; the `γ = 1` and the `O(ε^{−2})` complexity that the
sentence goes on to state are `pde_complexity` of `MlmcLean.PDEExamples`).  Let `a` be a random
variable with values in `[0, 1]` almost surely (the paper takes it uniform on `(0, 1)`) and
`Z ~ N(0, 1)`, let `P` be the output `∫₀¹ u` of the exact solution of `(c u′)′ = −50 Z²`,
`c(x) = 1 + a x`, `u(0) = u(1) = 0`, and `P_ℓ` the trapezoidal rule for the finite-difference
solution on the grid of spacing `h_ℓ = 2^{−(ℓ+1)}`.  Then `P` and `P_ℓ` are square integrable
(so `V₀ = V[P₀] < ∞`), `P_ℓ − P` is integrable with `|E[P_ℓ − P]| ≤ (50/3) h_ℓ²` (`α = 2`),
and `P_{ℓ+1} − P_ℓ` is square integrable with
`V[P_{ℓ+1} − P_ℓ] ≤ E[(P_{ℓ+1} − P_ℓ)²] ≤ (62500/3) h_{ℓ+1}⁴` (`β = 4`).  This applies
`rates_of_pathwise_random` with the random constant `K = (50/3) Z²` (`ellipticPl_error`), which has
`E[K] = 50/3` and `E[K²] = 2500/3` (`ellipticK_moments`); no deterministic `K` exists
(`not_ae_abs_ellipticP_sub_le`).  `μ` is a probability measure because `Z` has a Gaussian law. -/
theorem elliptic_fd_rates {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {a Z : Ω → ℝ}
    (ha : AEMeasurable a μ) (ha01 : ∀ᵐ ω ∂μ, a ω ∈ Set.Icc (0 : ℝ) 1)
    (hZ : HasLaw Z (gaussianReal 0 1) μ) (ℓ : ℕ) :
    MemLp (fun ω => ellipticP (a ω) (50 * Z ω ^ 2)) 2 μ ∧
      MemLp (fun ω => ellipticPl (a ω) (50 * Z ω ^ 2) ℓ) 2 μ ∧
      Integrable (fun ω => ellipticPl (a ω) (50 * Z ω ^ 2) ℓ - ellipticP (a ω) (50 * Z ω ^ 2))
        μ ∧
      |∫ ω, (ellipticPl (a ω) (50 * Z ω ^ 2) ℓ - ellipticP (a ω) (50 * Z ω ^ 2)) ∂μ| ≤
        50 / 3 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 ∧
      MemLp (fun ω => ellipticPl (a ω) (50 * Z ω ^ 2) (ℓ + 1) -
        ellipticPl (a ω) (50 * Z ω ^ 2) ℓ) 2 μ ∧
      variance (fun ω => ellipticPl (a ω) (50 * Z ω ^ 2) (ℓ + 1) -
        ellipticPl (a ω) (50 * Z ω ^ 2) ℓ) μ ≤
        ∫ ω, (ellipticPl (a ω) (50 * Z ω ^ 2) (ℓ + 1) - ellipticPl (a ω) (50 * Z ω ^ 2) ℓ) ^ 2 ∂μ ∧
      ∫ ω, (ellipticPl (a ω) (50 * Z ω ^ 2) (ℓ + 1) - ellipticPl (a ω) (50 * Z ω ^ 2) ℓ) ^ 2 ∂μ ≤
        62500 / 3 * ((1 / 2 : ℝ) ^ (ℓ + 2)) ^ 4 := by
  have : IsProbabilityMeasure μ := hZ.isProbabilityMeasure_iff.2 inferInstance
  obtain ⟨hK, hK1, hK2⟩ := ellipticK_moments hZ
  have hf : AEMeasurable (fun ω => 50 * Z ω ^ 2) μ := (hZ.aemeasurable.pow_const 2).const_mul 50
  have hPl : ∀ ℓ : ℕ, AEStronglyMeasurable (fun ω => ellipticPl (a ω) (50 * Z ω ^ 2) ℓ) μ :=
    fun ℓ => ((measurable_ellipticPl ℓ).comp_aemeasurable (ha.prodMk hf)).aestronglyMeasurable
  have hP : AEStronglyMeasurable (fun ω => ellipticP (a ω) (50 * Z ω ^ 2)) μ := by
    have hm : AEStronglyMeasurable (fun ω => 50 * Z ω ^ 2 * (ellipticMoment (a ω) 2 -
        ellipticMoment (a ω) 1 ^ 2 / ellipticMoment (a ω) 0)) μ :=
      (hf.mul (((measurable_ellipticMoment 2).sub (((measurable_ellipticMoment 1).pow_const 2).div
        (measurable_ellipticMoment 0))).comp_aemeasurable ha)).aestronglyMeasurable
    refine hm.congr ?_
    filter_upwards [ha01] with ω hω
    exact (ellipticP_eq hω.1 _).symm
  have herr : ∀ ℓ : ℕ, ∀ᵐ ω ∂μ, |ellipticP (a ω) (50 * Z ω ^ 2) -
      ellipticPl (a ω) (50 * Z ω ^ 2) ℓ| ≤ 50 / 3 * Z ω ^ 2 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 :=
    fun ℓ => by
      filter_upwards [ha01] with ω hω
      exact ellipticPl_error hω.1 hω.2 (Z ω) ℓ
  obtain ⟨i1, h1, m2, h2, h3⟩ := rates_of_pathwise_random (K := fun ω => 50 / 3 * Z ω ^ 2)
    (e := fun ℓ => ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2) hP hPl hK herr ℓ
  -- `P` and `P_ℓ` are bounded by multiples of `Z²`
  have hP2 : MemLp (fun ω => ellipticP (a ω) (50 * Z ω ^ 2)) 2 μ := by
    refine memLp_two_of_abs_le_mul_sq hZ hP (C := 50) ?_
    filter_upwards [ha01] with ω hω
    exact (abs_ellipticP_le hω.1 _).trans_eq (abs_of_nonneg (by positivity))
  have hPl2 : MemLp (fun ω => ellipticPl (a ω) (50 * Z ω ^ 2) ℓ) 2 μ := by
    refine memLp_two_of_abs_le_mul_sq hZ (hPl ℓ) (C := 100) ?_
    filter_upwards [ha01, herr ℓ] with ω hω he
    have hh : ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    have hb : |ellipticP (a ω) (50 * Z ω ^ 2)| ≤ 50 * Z ω ^ 2 :=
      (abs_ellipticP_le hω.1 _).trans_eq (abs_of_nonneg (by positivity))
    have hk : 50 / 3 * Z ω ^ 2 * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ 2 ≤ 50 / 3 * Z ω ^ 2 :=
      mul_le_of_le_one_right (by positivity) hh
    calc |ellipticPl (a ω) (50 * Z ω ^ 2) ℓ|
        = |ellipticP (a ω) (50 * Z ω ^ 2) -
            (ellipticP (a ω) (50 * Z ω ^ 2) - ellipticPl (a ω) (50 * Z ω ^ 2) ℓ)| := by
          rw [sub_sub_cancel]
      _ ≤ |ellipticP (a ω) (50 * Z ω ^ 2)| +
            |ellipticP (a ω) (50 * Z ω ^ 2) - ellipticPl (a ω) (50 * Z ω ^ 2) ℓ| := abs_sub _ _
      _ ≤ 100 * Z ω ^ 2 := by linarith [sq_nonneg (Z ω)]
  rw [hK1] at h1
  rw [hK2] at h3
  exact ⟨hP2, hPl2, i1, h1, m2, h2, h3.trans_eq (by ring)⟩

end MLMC
