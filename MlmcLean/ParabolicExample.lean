import MlmcLean.GBMMilstein
import MlmcLean.AsymptoticNormal
import MlmcLean.LUTAsymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The parabolic SPDE example of Giles 2015, §7.1, end to end

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015) 259–328, §7.1
"Two simple examples", pp. 50–51 (`docs/giles2015.txt`, l. 2175–2212).

"The second example is a 1D parabolic SPDE, in which `u(x, t)` satisfies the SPDE
`du = ∂²u/∂x² dt + 10 dW`, on the domain `0 < x < 1` with boundary data `u(0, t) = u(1, t) = 0`
and initial data `u(x, 0) = 0`.  The output functional is chosen to be `P = ∫₀¹ u²(x, 0.25)`. …
An Euler-Maruyama time discretisation with timestep `k`, combined with a second order space
discretisation with uniform grid spacing `h`, gives the discrete approximation
`u^{n+1}_j = u^n_j + k/h² (u^n_{j+1} − 2u^n_j + u^n_{j−1}) + 10 ΔW^n`.  The level `ℓ`
approximation uses `h_ℓ = 2^{−(ℓ+1)}`, `k_ℓ = ¼ h_ℓ²`. … the cost per sample increases by factor
8, giving `γ = 3`. … the solution error is `O(2^{−2ℓ})` and hence `α = 2` and `β = 4`.  This leads
to the optimal complexity of `O(ε^{−2})`."

The noise is one scalar Brownian motion `W`, added at every grid point (`10 ΔW^n`), and the scheme
is linear.  So each level is a linear Gaussian recursion, which the discrete sine vectors
diagonalise; everything below is proved without Itô calculus or PDE theory.

**The model.**  Level `ℓ` has `J = 2^{ℓ+1}` grid intervals (`h = 1/J`), the ratio `k/h² = ¼` and
`N = T/k = 4^{ℓ+1}` time steps up to `T = ¼`.  The Brownian increments are
`ΔW^n = √k z_n = z_n/2^{ℓ+2}` with independent standard normal `z_0, z_1, …` (`stdNormalSeq`).
`parabolicStep` is the explicit step on the nodes `j = 0, …, J` (the boundary nodes keep their
values), `parabolicPath` the scheme started from `u⁰ = 0`, and `parabolicP ℓ z = h ∑_{j=0}^{J}
(u^N_j)²` the grid quadrature of `∫₀¹ u²(x, ¼) dx` (the trapezoidal rule, since
`u_0 = u_J = 0`).  The coarse sample of the level-`(ℓ+1)` correction is `parabolicP ℓ` at
`pairAvg (pairAvg z)`, whose `p`-th entry is `(z_{4p} + z_{4p+1} + z_{4p+2} + z_{4p+3})/2`: its
Brownian increments are the sums of four fine ones (`parabolic_coupling`).  §7.1 does not spell
out the coupling ("The multilevel implementation is again very easy"); this is the standard one
of §5.1 ("summing the Brownian increments for the fine path timesteps to obtain the Brownian
increments for the coarse timesteps"), with four fine steps per coarse step as `k_ℓ = 4k_{ℓ+1}`.
`parabolicStep λ J w` is the special case `dirichletHeatStep λ J (fun _ => w)` (spatially constant
noise) of the scheme of `MlmcLean.SpotCheckRemarks`, which is not imported here.

**Results.**
* Diagonalisation (`parabolicPath_eq_sum`): `u^n_j = ∑_{m=1}^{J−1} A^n_m sin(πmj/J)`, where each
  mode amplitude is the scalar AR(1) recursion `A^{n+1}_m = μ_m A^n_m + 10 c_m ΔW^n` (`modeAmp`)
  with `μ_m = 1 − 4λ sin²(πm/(2J))` (`sineEig`) and `c_m = (2/J) ∑_{0<i<J} sin(πmi/J)`, the
  projection of the constant vector (`sineCoef`; `sineCoef_eq`:
  `c_m = (1 − cos πm)/J · cot(πm/(2J))`); `sum_sq_parabolicPath`:
  `∑_j (u^n_j)² = (J/2) ∑_m (A^n_m)²`; `integral_parabolicP`: the exact mean of `P_ℓ`.
* The variance rate `β = 4` (`parabolic_variance_rate`):
  `E[(P_{ℓ+1} − P^c_ℓ)²] ≤ 1.5·10⁶ · 16^{−(ℓ+1)}`, with the correction square integrable.
* The limit (`parabolic_mean_tendsto`): `E[P_ℓ] → ∑_{m odd} 400(1 − e^{−π²m²/2})/(π⁴m⁴)`, the
  explicit series `parabolicLimit` (which equals `E ∫₀¹ u²(x, ¼) dx` for the SPDE by the Itô
  isometry; that identification is not formalised, see the deviations below).
* The weak rate `α = 2` (`parabolic_weak_rate`): `|E[P_{ℓ+1}] − E[P_ℓ]| ≤ 1225 · 4^{−(ℓ+1)}` and
  `|E[P_ℓ] − parabolicLimit| ≤ 409 · 4^{−ℓ}`.
* Theorem 1 end to end (`parabolic_mlmc_theorem1`): mean square error `< ε²` at cost `O(ε⁻²)`,
  with a level-`ℓ` sample costing `2^{ℓ+1} · 4^{ℓ+1} = 8^{ℓ+1}` (`γ = 3`).

**The proof of `β = 4`.**  The coarse sine vectors are the restrictions of the fine ones to the
even nodes, so `P_{ℓ+1} − P^c_ℓ = ½ ∑_{m<J/2} ((A^f_m)² − (A^c_m)²) + ½ ∑_{m≥J/2} (A^f_m)²` with
`J` the fine number of intervals.  Every amplitude is a finite linear combination `∑ α_i z_i`, a
centred Gaussian with `E X⁴ = 3 (E X²)²`.  The coefficient vectors satisfy
`∑ α_i² ≤ 100/m⁴` (`parabolic_sum_sq_coef_le`) and, over one coarse step (four fine steps),
a recursion which gives `∑ (α^f_i − α^c_i)² ≤ 9600/J⁴` for `m < J/2`
(`parabolic_diff_rec_bound`, `parabolic_sum_sq_diff_coef_le`).  A weighted Cauchy–Schwarz
inequality over the modes (weights `m⁻²`) assembles the bound (`parabolic_variance_of_coef`).
Then `|E[P_{ℓ+1}] − E[P_ℓ]| ≤ (E[(P_{ℓ+1} − P^c_ℓ)²])^{1/2}` by (2.4), and Tannery's theorem
(`tendsto_sum_range_of_dominated` of `MlmcLean.LUTAsymptotics`) identifies the limit.

**Deviations from the paper.**
* The paper's `P = ∫₀¹ u²(x, 0.25)` is the output of the SPDE, which is not constructed here (no
  stochastic integration in Mathlib).  The target of Theorem 1 is `parabolicLimit = lim E[P_ℓ]`
  (`parabolic_mean_tendsto`), the closed-form series above; that it equals `E ∫₀¹ u²(x, ¼) dx`
  for the mild solution `u = ∑_m a_m(t) sin(mπx)`, `a_m(t) = 10 (4/(mπ)) ∫₀ᵗ e^{−m²π²(t−s)} dW_s`
  (`m` odd), is the Itô isometry and is not formalised.
* "the solution error is `O(2^{−2ℓ})`" (the strong error against the SPDE) is not proved; the
  rates `α = 2` and `β = 4` are proved directly for the level differences, which is what
  Theorem 1 needs.
* The constants are explicit and not optimised: numerically (exact Gaussian computations),
  `E[(P_ℓ − P^c_{ℓ−1})²] · 16^ℓ` increases to about `43` and `|E[P_ℓ] − E[P_{ℓ−1}]| · 4^ℓ` to
  about `1.6`.
* The cost of a sample counts the node updates `J N` of the fine path; the coarse path adds `1/8`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real
open scoped NNReal

namespace MLMC

/-! ### Discrete sine vectors -/

/-- The discrete sine vector `sin(πmj/J)` of mode `m` on the grid `j = 0, …, J` with `J`
intervals (Giles 2015, §7.1, p. 51: the eigenvectors of the Dirichlet difference operator of the
scheme `u^{n+1}_j = u^n_j + k/h² (u^n_{j+1} − 2u^n_j + u^n_{j−1}) + 10ΔW^n`). -/
noncomputable def sineMode (J m j : ℕ) : ℝ := Real.sin (π * m * j / J)

/-- Telescoping (Giles 2015, §7.1, for the discrete sine transform):
`2 sin(d/2) ∑_{j<n} cos(jd) = sin((n − ½)d) + sin(d/2)`. -/
lemma two_sin_mul_sum_range_cos (d : ℝ) (n : ℕ) :
    2 * Real.sin (d / 2) * ∑ j ∈ range n, Real.cos (j * d) =
      Real.sin ((n - 1 / 2) * d) + Real.sin (d / 2) := by
  have h : ∀ j : ℕ, 2 * Real.sin (d / 2) * Real.cos (j * d) =
      Real.sin ((((j + 1 : ℕ) : ℝ) - 1 / 2) * d) - Real.sin (((j : ℝ) - 1 / 2) * d) := by
    intro j
    rw [Real.sin_sub_sin]
    push_cast
    ring_nf
  rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ => h j,
    Finset.sum_range_sub (fun j : ℕ => Real.sin (((j : ℝ) - 1 / 2) * d))]
  push_cast
  rw [show ((0 : ℝ) - 1 / 2) * d = -(d / 2) by ring, Real.sin_neg, sub_neg_eq_add]

/-- The cosine sum over one half period (Giles 2015, §7.1, for the discrete sine transform): if
`sin(πk) = 0` and `sin(πk/(2J)) ≠ 0`, then `∑_{j<J} cos(πkj/J) = (1 − cos πk)/2`. -/
lemma sum_range_cos_pi_mul_div {J : ℕ} (hJ : 0 < J) {k : ℝ} (hk : Real.sin (π * k) = 0)
    (hk2 : Real.sin (π * k / (2 * J)) ≠ 0) :
    ∑ j ∈ range J, Real.cos (π * k * j / J) = (1 - Real.cos (π * k)) / 2 := by
  have hJ' : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  set d : ℝ := π * k / J with hd
  have hd2 : d / 2 = π * k / (2 * J) := by rw [hd]; field_simp
  have h := two_sin_mul_sum_range_cos d J
  have e1 : ∀ j : ℕ, Real.cos (π * k * j / J) = Real.cos (j * d) := fun j => by
    rw [hd]; ring_nf
  have e2 : ((J : ℝ) - 1 / 2) * d = π * k - d / 2 := by rw [hd]; field_simp
  rw [e2, Real.sin_sub, hk, zero_mul, zero_sub] at h
  rw [Finset.sum_congr rfl fun j _ => e1 j]
  rw [hd2] at h
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hk2)
  linear_combination h

/-- `sin x ≠ 0` for `x ≠ 0` in `(−π, π)`. -/
lemma sin_ne_zero_of_ne_zero_of_mem_Ioo {x : ℝ} (hx : x ≠ 0) (h1 : -π < x) (h2 : x < π) :
    Real.sin x ≠ 0 := fun h => hx ((Real.sin_eq_zero_iff_of_lt_of_lt h1 h2).1 h)

/-- **Orthogonality of the discrete sine vectors** (Giles 2015, §7.1): for modes
`0 < m, m' < J`, `∑_{j<J} sin(πmj/J) sin(πm'j/J) = J/2` if `m = m'` and `0` otherwise. -/
lemma sum_range_sineMode_mul {J m m' : ℕ} (hm : m ∈ Ico 1 J) (hm' : m' ∈ Ico 1 J) :
    ∑ j ∈ range J, sineMode J m j * sineMode J m' j = if m = m' then (J : ℝ) / 2 else 0 := by
  rw [Finset.mem_Ico] at hm hm'
  have hJ : 0 < J := by omega
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hpi := Real.pi_pos
  have hmJ : (m : ℝ) < J := by exact_mod_cast hm.2
  have hm'J : (m' : ℝ) < J := by exact_mod_cast hm'.2
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  have hm'1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm'.1
  have hprod : ∀ j : ℕ, sineMode J m j * sineMode J m' j =
      (Real.cos (π * ((m : ℝ) - m') * j / J) - Real.cos (π * ((m : ℝ) + m') * j / J)) / 2 := by
    intro j
    rw [sineMode, sineMode,
      show π * ((m : ℝ) - m') * j / J = π * m * j / J - π * m' * j / J by ring,
      show π * ((m : ℝ) + m') * j / J = π * m * j / J + π * m' * j / J by ring,
      Real.cos_sub, Real.cos_add]
    ring
  rw [Finset.sum_congr rfl fun j _ => hprod j, ← Finset.sum_div, Finset.sum_sub_distrib]
  have hsm : Real.sin (π * m) = 0 := by rw [mul_comm]; exact Real.sin_nat_mul_pi m
  have hsm' : Real.sin (π * m') = 0 := by rw [mul_comm]; exact Real.sin_nat_mul_pi m'
  -- the sum with `m + m'`
  have hplus : ∑ j ∈ range J, Real.cos (π * ((m : ℝ) + m') * j / J) =
      (1 - Real.cos (π * ((m : ℝ) + m'))) / 2 := by
    refine sum_range_cos_pi_mul_div hJ ?_ ?_
    · rw [mul_add, Real.sin_add, hsm, hsm']; ring
    · refine sin_ne_zero_of_ne_zero_of_mem_Ioo ?_ ?_ ?_
      · positivity
      · have : 0 < π * ((m : ℝ) + m') / (2 * J) := by positivity
        linarith
      · rw [div_lt_iff₀ (by positivity)]
        nlinarith
  split_ifs with hmm
  · subst hmm
    have h0 : ∀ j : ℕ, Real.cos (π * ((m : ℝ) - m) * j / J) = 1 := fun j => by
      rw [sub_self, mul_zero, zero_mul, zero_div, Real.cos_zero]
    rw [Finset.sum_congr rfl fun j _ => h0 j, hplus, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, show π * ((m : ℝ) + m) = ((2 * m : ℕ) : ℝ) * π by push_cast; ring,
      Real.cos_nat_mul_pi, pow_mul]
    norm_num
  · have hminus : ∑ j ∈ range J, Real.cos (π * ((m : ℝ) - m') * j / J) =
        (1 - Real.cos (π * ((m : ℝ) - m'))) / 2 := by
      refine sum_range_cos_pi_mul_div hJ ?_ ?_
      · rw [mul_sub, Real.sin_sub, hsm, hsm']; ring
      · have hne : (m : ℝ) - m' ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hmm)
        refine sin_ne_zero_of_ne_zero_of_mem_Ioo ?_ ?_ ?_
        · exact div_ne_zero (mul_ne_zero hpi.ne' hne) (by positivity)
        · rw [lt_div_iff₀ (by positivity)]
          nlinarith
        · rw [div_lt_iff₀ (by positivity)]
          nlinarith
    rw [hminus, hplus, mul_sub, mul_add, Real.cos_sub, Real.cos_add, hsm, hsm']
    ring

/-- The sine vectors vanish at the boundary node `j = 0` (Giles 2015, §7.1: `u(0, t) = 0`). -/
lemma sineMode_zero_right (J m : ℕ) : sineMode J m 0 = 0 := by
  simp [sineMode]

/-- The sine vectors vanish at the boundary node `j = J` (Giles 2015, §7.1: `u(1, t) = 0`). -/
lemma sineMode_self (J m : ℕ) : sineMode J m J = 0 := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp [sineMode]
  · have hJ' : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
    rw [sineMode, mul_div_assoc, div_self hJ', mul_one, mul_comm]
    exact Real.sin_nat_mul_pi m

/-- The discrete sine matrix `sin(πmj/J)` is symmetric in the mode `m` and the node `j`. -/
lemma sineMode_comm (J m j : ℕ) : sineMode J m j = sineMode J j m := by
  rw [sineMode, sineMode, mul_right_comm]

/-- Orthogonality of the sine vectors over all nodes `j = 0, …, J` (Giles 2015, §7.1). -/
lemma sum_range_succ_sineMode_mul {J m m' : ℕ} (hm : m ∈ Ico 1 J) (hm' : m' ∈ Ico 1 J) :
    ∑ j ∈ range (J + 1), sineMode J m j * sineMode J m' j =
      if m = m' then (J : ℝ) / 2 else 0 := by
  rw [Finset.sum_range_succ, sineMode_self, zero_mul, add_zero, sum_range_sineMode_mul hm hm']

/-- Orthogonality of the sine vectors over the interior nodes `0 < j < J` (Giles 2015, §7.1). -/
lemma sum_Ico_sineMode_mul {J m m' : ℕ} (hm : m ∈ Ico 1 J) (hm' : m' ∈ Ico 1 J) :
    ∑ j ∈ Ico 1 J, sineMode J m j * sineMode J m' j = if m = m' then (J : ℝ) / 2 else 0 := by
  have hJ : 0 < J := by rw [Finset.mem_Ico] at hm; omega
  rw [← sum_range_sineMode_mul hm hm', Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot hJ, sineMode_zero_right, zero_mul, zero_add]

/-- The projection `c_m = (2/J) ∑_{0<i<J} sin(πmi/J)` of the constant vector `1` on the sine
vector of mode `m` (Giles 2015, §7.1, p. 51: the noise `10ΔW^n` is the same at every grid point, so
mode `m` receives `10 c_m ΔW^n`). -/
noncomputable def sineCoef (J m : ℕ) : ℝ := 2 / J * ∑ i ∈ Ico 1 J, sineMode J m i

/-- **The constant vector is the sum of its sine modes** (Giles 2015, §7.1): for every interior
node `0 < j < J`, `∑_{m=1}^{J−1} c_m sin(πmj/J) = 1`. -/
lemma sum_sineCoef_mul_sineMode {J j : ℕ} (hj : j ∈ Ico 1 J) :
    ∑ m ∈ Ico 1 J, sineCoef J m * sineMode J m j = 1 := by
  have hJ : (J : ℝ) ≠ 0 := by
    rw [Finset.mem_Ico] at hj
    exact_mod_cast (show J ≠ 0 by omega)
  have e : ∀ m ∈ Ico 1 J, sineCoef J m * sineMode J m j =
      2 / J * ∑ i ∈ Ico 1 J, sineMode J i m * sineMode J j m := fun m _ => by
    rw [sineCoef, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sineMode_comm J m i, sineMode_comm J m j]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun i hi => sum_Ico_sineMode_mul hi hj]
  rw [Finset.sum_ite_eq' (Ico 1 J) j (fun _ => (J : ℝ) / 2), if_pos hj]
  field_simp

/-- **The projection of the constant vector in closed form** (Giles 2015, §7.1, p. 51, the noise
term of the scheme "`u^{n+1}_j = u^n_j + k/h² (u^n_{j+1} − 2u^n_j + u^n_{j−1}) + 10ΔW^n`", which is
the same at every grid point): for `0 < m < 2J`,
`c_m = (2/J) ∑_{0<i<J} sin(πmi/J) = (1 − cos πm)/J · cot(πm/(2J))`, that is
`(2/J) cot(πm/(2J))` for odd `m` and `0` for even `m`.  So only the odd modes are forced, and for
fixed odd `m`, `c_m → 4/(πm) = 2∫₀¹ sin(πmx) dx` (the sine coefficient of `1`) as `J → ∞`. -/
theorem sineCoef_eq {J m : ℕ} (hm : 0 < m) (hm2 : m < 2 * J) :
    sineCoef J m = (1 - Real.cos (π * m)) / J *
      (Real.cos (π * m / (2 * J)) / Real.sin (π * m / (2 * J))) := by
  have hJ : 0 < J := by omega
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hm2r : (m : ℝ) < 2 * J := by exact_mod_cast hm2
  set θ : ℝ := π * m / J with hθ
  have hθ2 : θ / 2 = π * m / (2 * J) := by rw [hθ]; field_simp
  have hs : Real.sin (θ / 2) ≠ 0 := by
    rw [hθ2]
    refine (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have htel : ∀ i : ℕ, 2 * Real.sin (θ / 2) * sineMode J m i =
      Real.cos (((i : ℝ) - 1 / 2) * θ) - Real.cos ((((i + 1 : ℕ) : ℝ) - 1 / 2) * θ) := by
    intro i
    rw [Real.cos_sub_cos, sineMode]
    push_cast
    have e1 : (((i : ℝ) - 1 / 2) * θ + ((i : ℝ) + 1 - 1 / 2) * θ) / 2 = π * m * i / J := by
      rw [hθ]; ring
    have e2 : (((i : ℝ) - 1 / 2) * θ - ((i : ℝ) + 1 - 1 / 2) * θ) / 2 = -(θ / 2) := by ring
    rw [e1, e2, Real.sin_neg]
    ring
  have hsum : 2 * Real.sin (θ / 2) * ∑ i ∈ Ico 1 J, sineMode J m i =
      (1 - Real.cos (π * m)) * Real.cos (θ / 2) := by
    have h0 : ∑ i ∈ Ico 1 J, sineMode J m i = ∑ i ∈ range J, sineMode J m i := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hJ, sineMode_zero_right,
        zero_add]
    rw [h0, Finset.mul_sum, Finset.sum_congr rfl fun i _ => htel i,
      Finset.sum_range_sub' (fun i : ℕ => Real.cos (((i : ℝ) - 1 / 2) * θ))]
    have e3 : ((J : ℝ) - 1 / 2) * θ = π * m - θ / 2 := by rw [hθ]; field_simp
    have hsm : Real.sin (π * m) = 0 := by rw [mul_comm]; exact Real.sin_nat_mul_pi m
    simp only [Nat.cast_zero]
    rw [e3, Real.cos_sub, hsm, show ((0 : ℝ) - 1 / 2) * θ = -(θ / 2) by ring, Real.cos_neg]
    ring
  rw [sineCoef, ← hθ2]
  field_simp
  linear_combination hsum

/-- The eigenvalue `μ_m = 1 − 4λ sin²(πm/(2J))` of the explicit step `u_j + λ(u_{j+1} − 2u_j +
u_{j−1})` (`λ = k/h²`) on the sine vector of mode `m` (Giles 2015, §7.1, p. 51). -/
noncomputable def sineEig (lam : ℝ) (J m : ℕ) : ℝ :=
  1 - 4 * lam * Real.sin (π * m / (2 * J)) ^ 2

/-- With the paper's ratio `k_ℓ/h_ℓ² = ¼` (Giles 2015, §7.1, p. 51) the eigenvalues are
`μ_m = cos²(πm/(2J)) ∈ [0, 1]`. -/
lemma sineEig_quarter (J m : ℕ) : sineEig (1 / 4) J m = Real.cos (π * m / (2 * J)) ^ 2 := by
  rw [sineEig, Real.cos_sq']
  ring

/-- The sine vectors are eigenvectors of the explicit step (Giles 2015, §7.1, p. 51): at every
node `j > 0`, `v_j + λ(v_{j+1} − 2v_j + v_{j−1}) = μ_m v_j` for `v_j = sin(πmj/J)`.  (The same
identity, for `dirichletHeatStep` with zero noise, is `dirichletHeatStep_sin` in
`MlmcLean.SpotCheckRemarks`, which is not imported here.) -/
lemma sineMode_step (lam : ℝ) {J j : ℕ} (hj : 0 < j) (m : ℕ) :
    sineMode J m j + lam * (sineMode J m (j + 1) - 2 * sineMode J m j + sineMode J m (j - 1)) =
      sineEig lam J m * sineMode J m j := by
  set θ : ℝ := π * m / J with hθ
  have e0 : ∀ i : ℕ, sineMode J m i = Real.sin (θ * i) := fun i => by
    rw [sineMode, hθ]; ring_nf
  have hc : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have e1 : Real.sin (θ * ((j + 1 : ℕ) : ℝ)) =
      Real.sin (θ * j) * Real.cos θ + Real.cos (θ * j) * Real.sin θ := by
    rw [Nat.cast_succ, mul_add, mul_one, Real.sin_add]
  have e2 : Real.sin (θ * ((j - 1 : ℕ) : ℝ)) =
      Real.sin (θ * j) * Real.cos θ - Real.cos (θ * j) * Real.sin θ := by
    rw [hc, mul_sub, mul_one, Real.sin_sub]
  have e3 : Real.cos θ = 1 - 2 * Real.sin (π * m / (2 * J)) ^ 2 := by
    have h3 : θ = 2 * (π * m / (2 * J)) := by
      rw [hθ]
      rcases Nat.eq_zero_or_pos J with h | h
      · simp [h]
      · field_simp
    rw [h3, Real.cos_two_mul, Real.cos_sq']
    ring
  rw [e0, e0, e0, e1, e2, sineEig, e3]
  ring

/-! ### The scheme and its diagonalisation -/

/-- One step of the explicit scheme of Giles 2015, §7.1 (p. 51, l. 2179–2194:
"`u^{n+1}_j = u^n_j + k/h² (u^n_{j+1} − 2u^n_j + u^n_{j−1}) + 10ΔW^n`", "boundary data
`u(0, t) = u(1, t) = 0`") on the grid `j = 0, …, J`: the interior nodes `0 < j < J` get
`u_j + λ(u_{j+1} − 2u_j + u_{j−1}) + w` with `λ = k/h²` and the noise `w` (the same at every node,
`10ΔW^n` in the paper); the boundary nodes keep their values.  Values at `j > J` are carried
along and never used.  This is the special case of spatially constant noise of
`dirichletHeatStep` in `MlmcLean.SpotCheckRemarks` (not imported here):
`parabolicStep λ J w = dirichletHeatStep λ J (fun _ => w)`, by the same defining expression. -/
def parabolicStep (lam : ℝ) (J : ℕ) (w : ℝ) (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  if 0 < j ∧ j < J then u j + lam * (u (j + 1) - 2 * u j + u (j - 1)) + w else u j

/-- The scheme of Giles 2015, §7.1 (p. 51) started from the initial data `u(x, 0) = 0` and driven
by the Brownian increments `dW`: `u⁰ = 0`, `u^{n+1} = parabolicStep λ J (10 ΔW^n) uⁿ`. -/
def parabolicPath (lam : ℝ) (J : ℕ) (dW : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | n + 1 => parabolicStep lam J (10 * dW n) (parabolicPath lam J dW n)

/-- The amplitude of one sine mode (Giles 2015, §7.1): the scalar AR(1) recursion `A⁰ = 0`,
`A^{n+1} = μ Aⁿ + 10 c ΔW^n` driven by the Brownian increments `dW`. -/
def modeAmp (μ c : ℝ) (dW : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => μ * modeAmp μ c dW n + 10 * c * dW n

/-- The AR(1) recursion in closed form (Giles 2015, §7.1): `A^n = ∑_{i<n} 10 c μ^{n−1−i} ΔW^i`,
a linear combination of the Brownian increments. -/
lemma modeAmp_eq_sum (μ c : ℝ) (dW : ℕ → ℝ) (n : ℕ) :
    modeAmp μ c dW n = ∑ i ∈ range n, 10 * c * μ ^ (n - 1 - i) * dW i := by
  induction n with
  | zero => simp [modeAmp]
  | succ n ih =>
    rw [modeAmp, ih, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [show n + 1 - 1 - i = n - 1 - i + 1 by omega, pow_succ]
      ring
    · rw [show n + 1 - 1 - n = 0 by omega, pow_zero]
      ring

/-- **The scheme is diagonalised by the discrete sine vectors** (Giles 2015, §7.1, p. 51:
"`u^{n+1}_j = u^n_j + k/h² (u^n_{j+1} − 2u^n_j + u^n_{j−1}) + 10ΔW^n`" with "boundary data
`u(0, t) = u(1, t) = 0` and initial data `u(x, 0) = 0`").  For every ratio `λ = k/h²`, number of
intervals `J`, Brownian increments `ΔW` and step `n`, at every node `j ≤ J`,
`u^n_j = ∑_{m=1}^{J−1} A^n_m sin(πmj/J)`, where the amplitude `A^n_m` of mode `m` is the scalar
AR(1) recursion `A^{n+1}_m = μ_m A^n_m + 10 c_m ΔW^n`, `A^0_m = 0` (`modeAmp`), with the
eigenvalue `μ_m = 1 − 4λ sin²(πm/(2J))` (`sineEig`) and the projection `c_m` of the constant
vector on mode `m` (`sineCoef`).  All modes are driven by the same scalar increments `ΔW^n`. -/
theorem parabolicPath_eq_sum (lam : ℝ) (J : ℕ) (dW : ℕ → ℝ) (n : ℕ) {j : ℕ} (hj : j ≤ J) :
    parabolicPath lam J dW n j =
      ∑ m ∈ Ico 1 J, modeAmp (sineEig lam J m) (sineCoef J m) dW n * sineMode J m j := by
  induction n generalizing j with
  | zero => simp [parabolicPath, modeAmp]
  | succ n ih =>
    rw [parabolicPath, parabolicStep]
    split_ifs with hint
    · rw [ih hj, ih (show j + 1 ≤ J by omega), ih (show j - 1 ≤ J by omega)]
      have hc := sum_sineCoef_mul_sineMode (J := J) (j := j) (Finset.mem_Ico.2 ⟨hint.1, hint.2⟩)
      have e : ∀ m ∈ Ico 1 J, modeAmp (sineEig lam J m) (sineCoef J m) dW (n + 1) * sineMode J m j =
          modeAmp (sineEig lam J m) (sineCoef J m) dW n * sineMode J m j +
            lam * (modeAmp (sineEig lam J m) (sineCoef J m) dW n * sineMode J m (j + 1) -
              2 * (modeAmp (sineEig lam J m) (sineCoef J m) dW n * sineMode J m j) +
              modeAmp (sineEig lam J m) (sineCoef J m) dW n * sineMode J m (j - 1)) +
            10 * dW n * (sineCoef J m * sineMode J m j) := fun m _ => by
        rw [modeAmp]
        linear_combination (-modeAmp (sineEig lam J m) (sineCoef J m) dW n) *
          sineMode_step lam (J := J) hint.1 m
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, hc,
        Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      ring
    · have hb : j = 0 ∨ j = J := by omega
      have h0 : ∀ m, sineMode J m j = 0 := fun m =>
        hb.elim (fun h => by rw [h]; exact sineMode_zero_right J m)
          (fun h => by rw [h]; exact sineMode_self J m)
      rw [ih hj]
      simp only [h0, mul_zero]

/-- **The grid quadrature of `u²` in the sine modes** (Giles 2015, §7.1, p. 51: "The output
functional is chosen to be `P = ∫₀¹ u²(x, 0.25)`"): `∑_{j=0}^{J} (u^n_j)² = (J/2) ∑_{m=1}^{J−1}
(A^n_m)²` (discrete Parseval identity), so `h ∑_j (u^n_j)² = ½ ∑_m (A^n_m)²` with `h = 1/J`. -/
theorem sum_sq_parabolicPath (lam : ℝ) (J : ℕ) (dW : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range (J + 1), parabolicPath lam J dW n j ^ 2 =
      (J : ℝ) / 2 * ∑ m ∈ Ico 1 J, modeAmp (sineEig lam J m) (sineCoef J m) dW n ^ 2 := by
  set a : ℕ → ℝ := fun m => modeAmp (sineEig lam J m) (sineCoef J m) dW n with ha
  calc ∑ j ∈ range (J + 1), parabolicPath lam J dW n j ^ 2
      = ∑ j ∈ range (J + 1), ∑ m ∈ Ico 1 J, ∑ m' ∈ Ico 1 J,
          a m * a m' * (sineMode J m j * sineMode J m' j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [parabolicPath_eq_sum lam J dW n (by rw [Finset.mem_range] at hj; omega), sq,
          Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
        rw [ha]
        ring
    _ = ∑ m ∈ Ico 1 J, ∑ m' ∈ Ico 1 J,
          a m * a m' * ∑ j ∈ range (J + 1), sineMode J m j * sineMode J m' j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ m ∈ Ico 1 J, ∑ m' ∈ Ico 1 J, a m * a m' * (if m = m' then (J : ℝ) / 2 else 0) := by
        refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun m' hm' => ?_
        rw [sum_range_succ_sineMode_mul hm hm']
    _ = (J : ℝ) / 2 * ∑ m ∈ Ico 1 J, a m ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq (Ico 1 J) m, if_pos hm]
        ring

/-! ### Linear combinations of independent standard normal variables -/

/-- A finite linear combination `∑_{i<n} α_i z_i` of independent standard normal variables is
`N(0, ∑ α_i²)` (used for the mode amplitudes of Giles 2015, §7.1, which are such combinations of
the Brownian increments). -/
lemma hasLaw_linComb_stdNormalSeq (α : ℕ → ℝ) (n : ℕ) :
    HasLaw (fun z : ℕ → ℝ => ∑ i ∈ range n, α i * z i)
      (gaussianReal 0 (∑ i ∈ range n, (α i ^ 2).toNNReal)) stdNormalSeq := by
  have hX : ∀ i, HasLaw (fun z : ℕ → ℝ => α i * z i)
      (gaussianReal 0 (α i ^ 2).toNNReal) stdNormalSeq := by
    intro i
    have h0 : HasLaw (fun z : ℕ → ℝ => z i) (gaussianReal 0 1) stdNormalSeq :=
      ⟨(measurable_pi_apply i).aemeasurable,
        (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i).map_eq⟩
    have h1 := gaussianReal_const_mul h0 (α i)
    have e : (.mk (α i ^ 2) (sq_nonneg _) * 1 : ℝ≥0) = (α i ^ 2).toNNReal := by
      ext
      simp [Real.coe_toNNReal _ (sq_nonneg (α i))]
    rw [mul_zero, e] at h1
    exact h1
  have hind : iIndepFun (fun i (z : ℕ → ℝ) => α i * z i) stdNormalSeq :=
    iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun i x => α i * x)
      (fun i => measurable_id.const_mul (α i))
  have h := hasLaw_finsetSum_gaussianReal (m := fun _ => 0) hX hind (range n)
  simpa using h

/-- `N(0, v)` is the image of `N(0, 1)` under `x ↦ √v x` (for the Gaussian moments used in Giles
2015, §7.1).  This is `gaussianReal_map_sqrt_mul` of `MlmcLean.AdaptiveGrids` read backwards;
that module is not imported here, so the one-line proof is repeated. -/
lemma gaussianReal_zero_eq_map_sqrt_mul (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  ext
  simp

section moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The second moment of `X ∼ N(0, v)` is `v`. -/
lemma integral_sq_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ^ 2 ∂P = v := by
  have h := hX.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  simp only [Function.comp_def] at h
  rw [h, gaussianReal_zero_eq_map_sqrt_mul, integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow]
  rw [integral_const_mul, integral_sq_gaussian, mul_one, Real.sq_sqrt (NNReal.coe_nonneg v)]

/-- The fourth moment of `X ∼ N(0, v)` is `3v²`. -/
lemma integral_pow_four_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ^ 4 ∂P = 3 * (v : ℝ) ^ 2 := by
  have h := hX.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  simp only [Function.comp_def] at h
  rw [h, gaussianReal_zero_eq_map_sqrt_mul, integral_map (by fun_prop) (by fun_prop)]
  have e : ∀ x : ℝ, (Real.sqrt v * x) ^ 4 = (v : ℝ) ^ 2 * x ^ 4 := fun x => by
    rw [mul_pow, show Real.sqrt v ^ 4 = (Real.sqrt v ^ 2) ^ 2 by ring,
      Real.sq_sqrt (NNReal.coe_nonneg v)]
  simp only [e]
  rw [integral_const_mul, integral_pow_four_gaussian]
  ring

/-- A measurable `X ∼ N(0, v)` has finite moments of every order (for Giles 2015, §7.1).  This
generalises `memLp_of_map_eq_gaussianReal` of `MlmcLean.EulerSuperlinear` (the case `v = 1`, not
imported here) to every variance. -/
lemma memLp_of_hasLaw_gaussianReal {X : Ω → ℝ} (hXm : Measurable X) {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) (p : ℝ≥0) : MemLp X p P :=
  (memLp_id_gaussianReal p).comp_measurePreserving ⟨hXm, hX.map_eq⟩

/-- `X⁴` is integrable for a measurable `X ∼ N(0, v)`. -/
lemma integrable_pow_four_of_hasLaw_gaussianReal {X : Ω → ℝ} (hXm : Measurable X) {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) : Integrable (fun ω => X ω ^ 4) P := by
  have h := (memLp_of_hasLaw_gaussianReal hXm hX 4).integrable_norm_pow (p := 4) (by norm_num)
  refine h.congr (Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]

/-- **The second moment of a product of centred Gaussians** (for Giles 2015, §7.1): if
`X ∼ N(0, v_X)` and `Y ∼ N(0, v_Y)` (not necessarily independent) with `v_X ≤ A` and `v_Y ≤ B`,
`A, B > 0`, then `(XY)²` is integrable and `E[(XY)²] ≤ 3AB` (from `X²Y² ≤ (tX⁴ + Y⁴/t)/2` with
`t = B/A` and `E X⁴ = 3v_X²`). -/
lemma integral_sq_mul_le_of_hasLaw_gaussianReal {X Y : Ω → ℝ} (hXm : Measurable X)
    (hYm : Measurable Y)
    {vX vY : ℝ≥0} (hX : HasLaw X (gaussianReal 0 vX) P) (hY : HasLaw Y (gaussianReal 0 vY) P)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hvX : (vX : ℝ) ≤ A) (hvY : (vY : ℝ) ≤ B) :
    Integrable (fun ω => (X ω * Y ω) ^ 2) P ∧ ∫ ω, (X ω * Y ω) ^ 2 ∂P ≤ 3 * A * B := by
  set t : ℝ := B / A with ht
  have ht0 : 0 < t := div_pos hB hA
  have hpt : ∀ ω, (X ω * Y ω) ^ 2 ≤ (t * X ω ^ 4 + Y ω ^ 4 / t) / 2 := fun ω => by
    have e : (t * X ω ^ 4 + Y ω ^ 4 / t) / 2 - (X ω * Y ω) ^ 2 =
        (t * X ω ^ 2 - Y ω ^ 2) ^ 2 / (2 * t) := by
      field_simp
      ring
    have : 0 ≤ (t * X ω ^ 2 - Y ω ^ 2) ^ 2 / (2 * t) := by positivity
    linarith
  have hI : Integrable (fun ω => (t * X ω ^ 4 + Y ω ^ 4 / t) / 2) P :=
    (((integrable_pow_four_of_hasLaw_gaussianReal hXm hX).const_mul t).add
      ((integrable_pow_four_of_hasLaw_gaussianReal hYm hY).div_const t)).div_const 2
  have hint : Integrable (fun ω => (X ω * Y ω) ^ 2) P :=
    hI.mono' ((hXm.mul hYm).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hpt ω)
  refine ⟨hint, ?_⟩
  have hvX0 : (0 : ℝ) ≤ vX := vX.2
  have hvY0 : (0 : ℝ) ≤ vY := vY.2
  calc ∫ ω, (X ω * Y ω) ^ 2 ∂P ≤ ∫ ω, (t * X ω ^ 4 + Y ω ^ 4 / t) / 2 ∂P :=
        integral_mono hint hI hpt
    _ = (t * (3 * (vX : ℝ) ^ 2) + 3 * (vY : ℝ) ^ 2 / t) / 2 := by
        rw [integral_div,
          integral_add ((integrable_pow_four_of_hasLaw_gaussianReal hXm hX).const_mul t)
          ((integrable_pow_four_of_hasLaw_gaussianReal hYm hY).div_const t), integral_const_mul,
          integral_div, integral_pow_four_of_hasLaw_gaussianReal hX,
          integral_pow_four_of_hasLaw_gaussianReal hY]
    _ ≤ (t * (3 * A ^ 2) + 3 * B ^ 2 / t) / 2 := by
        gcongr
    _ = 3 * A * B := by
        rw [ht]
        field_simp
        ring

end moments

/-- A finite linear combination of the coordinates is measurable. -/
lemma measurable_linComb (α : ℕ → ℝ) (n : ℕ) :
    Measurable (fun z : ℕ → ℝ => ∑ i ∈ range n, α i * z i) :=
  Finset.measurable_sum _ fun i _ => by fun_prop

/-- The variance `∑ (α_i²)⁺` of a linear combination, as a real number, is `∑ α_i²`. -/
lemma coe_sum_toNNReal_sq (α : ℕ → ℝ) (n : ℕ) :
    ((∑ i ∈ range n, (α i ^ 2).toNNReal : ℝ≥0) : ℝ) = ∑ i ∈ range n, α i ^ 2 := by
  rw [NNReal.coe_sum]
  exact Finset.sum_congr rfl fun i _ => Real.coe_toNNReal _ (sq_nonneg _)

/-- The difference of two linear combinations is the combination of the differences. -/
lemma linComb_sub_linComb (α β : ℕ → ℝ) (n : ℕ) (z : ℕ → ℝ) :
    ∑ i ∈ range n, α i * z i - ∑ i ∈ range n, β i * z i = ∑ i ∈ range n, (α i - β i) * z i := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The sum of two linear combinations is the combination of the sums. -/
lemma linComb_add_linComb (α β : ℕ → ℝ) (n : ℕ) (z : ℕ → ℝ) :
    ∑ i ∈ range n, α i * z i + ∑ i ∈ range n, β i * z i = ∑ i ∈ range n, (α i + β i) * z i := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- For linear combinations `X = ∑ α_i z_i`, `Y = ∑ β_i z_i` of independent standard normals with
`∑ (α_i − β_i)² ≤ A`, `∑ α_i² ≤ B/4`, `∑ β_i² ≤ B/4`: `E[((X − Y)(X + Y))²] ≤ 3AB` (Giles 2015,
§7.1: the fine and the coarse amplitude of one mode). -/
lemma integral_sq_mul_linComb_le (α β : ℕ → ℝ) (n : ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hαβ : ∑ i ∈ range n, (α i - β i) ^ 2 ≤ A) (hα : ∑ i ∈ range n, α i ^ 2 ≤ B / 4)
    (hβ : ∑ i ∈ range n, β i ^ 2 ≤ B / 4) :
    Integrable (fun z : ℕ → ℝ => ((∑ i ∈ range n, α i * z i - ∑ i ∈ range n, β i * z i) *
      (∑ i ∈ range n, α i * z i + ∑ i ∈ range n, β i * z i)) ^ 2) stdNormalSeq ∧
    ∫ z, ((∑ i ∈ range n, α i * z i - ∑ i ∈ range n, β i * z i) *
      (∑ i ∈ range n, α i * z i + ∑ i ∈ range n, β i * z i)) ^ 2 ∂stdNormalSeq ≤ 3 * A * B := by
  simp only [linComb_sub_linComb, linComb_add_linComb]
  have hB' : ∑ i ∈ range n, (α i + β i) ^ 2 ≤ B := by
    calc ∑ i ∈ range n, (α i + β i) ^ 2 ≤ ∑ i ∈ range n, (2 * α i ^ 2 + 2 * β i ^ 2) :=
          Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (α i - β i)]
      _ = 2 * ∑ i ∈ range n, α i ^ 2 + 2 * ∑ i ∈ range n, β i ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ B := by linarith
  exact integral_sq_mul_le_of_hasLaw_gaussianReal (measurable_linComb _ n) (measurable_linComb _ n)
    (hasLaw_linComb_stdNormalSeq _ n) (hasLaw_linComb_stdNormalSeq _ n) hA hB
    ((coe_sum_toNNReal_sq _ n).trans_le hαβ) ((coe_sum_toNNReal_sq _ n).trans_le hB')

/-- For a linear combination `X = ∑ α_i z_i` of independent standard normals with
`∑ α_i² ≤ B`: `E[(X²)²] ≤ 3B²`. -/
lemma integral_pow_four_linComb_le (α : ℕ → ℝ) (n : ℕ) {B : ℝ}
    (hα : ∑ i ∈ range n, α i ^ 2 ≤ B) :
    Integrable (fun z : ℕ → ℝ => ((∑ i ∈ range n, α i * z i) ^ 2) ^ 2) stdNormalSeq ∧
    ∫ z, ((∑ i ∈ range n, α i * z i) ^ 2) ^ 2 ∂stdNormalSeq ≤ 3 * B ^ 2 := by
  have h4 : ∀ x : ℝ, (x ^ 2) ^ 2 = x ^ 4 := fun x => by ring
  simp only [h4]
  have hlaw := hasLaw_linComb_stdNormalSeq α n
  refine ⟨integrable_pow_four_of_hasLaw_gaussianReal (measurable_linComb α n) hlaw, ?_⟩
  rw [integral_pow_four_of_hasLaw_gaussianReal hlaw, coe_sum_toNNReal_sq]
  have h0 : 0 ≤ ∑ i ∈ range n, α i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

/-- The square of a linear combination of independent standard normals is square integrable. -/
lemma memLp_sq_linComb (α : ℕ → ℝ) (n : ℕ) :
    MemLp (fun z : ℕ → ℝ => (∑ i ∈ range n, α i * z i) ^ 2) 2 stdNormalSeq := by
  rw [memLp_two_iff_integrable_sq ((measurable_linComb α n).pow_const 2).aestronglyMeasurable]
  exact (integral_pow_four_linComb_le α n le_rfl).1

/-! ### The second moment of a difference of two sums of squares -/

/-- `∑_{a ≤ m < b} m⁻² ≤ 2` for `a ≥ 1`. -/
lemma sum_Ico_one_div_sq_le_two {a b : ℕ} (ha : 1 ≤ a) :
    ∑ m ∈ Ico a b, (1 / (m : ℝ)) ^ 2 ≤ 2 := by
  have hsub : Ico a b ⊆ Ioo 0 b := fun m hm => by
    rw [Finset.mem_Ico] at hm
    rw [Finset.mem_Ioo]
    omega
  calc ∑ m ∈ Ico a b, (1 / (m : ℝ)) ^ 2 = ∑ m ∈ Ico a b, ((m : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [one_div, inv_pow]
    _ ≤ ∑ m ∈ Ioo 0 b, ((m : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity
    _ ≤ 2 / ((0 : ℕ) + 1) := sum_Ioo_inv_sq_le 0 b
    _ = 2 := by norm_num

/-- Weighted Cauchy–Schwarz with the weights `m⁻²`: `(∑_{a≤m<b} f_m)² ≤ 2 ∑_{a≤m<b} m² f_m²`
for `a ≥ 1`. -/
lemma sq_sum_Ico_le_two_mul_sum {a b : ℕ} (ha : 1 ≤ a) (f : ℕ → ℝ) :
    (∑ m ∈ Ico a b, f m) ^ 2 ≤ 2 * ∑ m ∈ Ico a b, (m : ℝ) ^ 2 * f m ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Ico a b) (fun m => 1 / (m : ℝ)) (fun m => m * f m)
  have e : ∑ m ∈ Ico a b, 1 / (m : ℝ) * (m * f m) = ∑ m ∈ Ico a b, f m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have : (m : ℝ) ≠ 0 := by
      rw [Finset.mem_Ico] at hm
      exact_mod_cast (show m ≠ 0 by omega)
    field_simp
  rw [e] at h
  refine h.trans ?_
  have e2 : ∑ m ∈ Ico a b, ((m : ℝ) * f m) ^ 2 = ∑ m ∈ Ico a b, (m : ℝ) ^ 2 * f m ^ 2 := by
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [e2]
  exact mul_le_mul_of_nonneg_right (sum_Ico_one_div_sq_le_two ha)
    (Finset.sum_nonneg fun m _ => by positivity)

/-- The pointwise bound behind the variance rate of Giles 2015, §7.1: with `J = 2J_c`,
`(½ ∑_{m<J} X_m² − ½ ∑_{m<J_c} Y_m²)² ≤ ∑_{m<J_c} m² ((X_m − Y_m)(X_m + Y_m))² +
∑_{J_c≤m<J} m² (X_m²)²` (sums over `m ≥ 1`). -/
lemma parabolic_sq_half_sub_le {Jc : ℕ} (hJc : 1 ≤ Jc) (X Y : ℕ → ℝ) :
    (1 / 2 * ∑ m ∈ Ico 1 (2 * Jc), X m ^ 2 - 1 / 2 * ∑ m ∈ Ico 1 Jc, Y m ^ 2) ^ 2 ≤
      ∑ m ∈ Ico 1 Jc, (m : ℝ) ^ 2 * ((X m - Y m) * (X m + Y m)) ^ 2 +
        ∑ m ∈ Ico Jc (2 * Jc), (m : ℝ) ^ 2 * (X m ^ 2) ^ 2 := by
  have hsplit : ∑ m ∈ Ico 1 (2 * Jc), X m ^ 2 =
      ∑ m ∈ Ico 1 Jc, X m ^ 2 + ∑ m ∈ Ico Jc (2 * Jc), X m ^ 2 :=
    (Finset.sum_Ico_consecutive _ hJc (by omega)).symm
  have e : 1 / 2 * ∑ m ∈ Ico 1 (2 * Jc), X m ^ 2 - 1 / 2 * ∑ m ∈ Ico 1 Jc, Y m ^ 2 =
      1 / 2 * (∑ m ∈ Ico 1 Jc, (X m - Y m) * (X m + Y m) + ∑ m ∈ Ico Jc (2 * Jc), X m ^ 2) := by
    rw [hsplit]
    have : ∑ m ∈ Ico 1 Jc, (X m - Y m) * (X m + Y m) =
        ∑ m ∈ Ico 1 Jc, X m ^ 2 - ∑ m ∈ Ico 1 Jc, Y m ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [this]
    ring
  rw [e]
  have h1 := sq_sum_Ico_le_two_mul_sum (b := Jc) (le_refl 1) (fun m => (X m - Y m) * (X m + Y m))
  have h2 := sq_sum_Ico_le_two_mul_sum (b := 2 * Jc) hJc (fun m => X m ^ 2)
  set T1 := ∑ m ∈ Ico 1 Jc, (X m - Y m) * (X m + Y m)
  set T2 := ∑ m ∈ Ico Jc (2 * Jc), X m ^ 2
  have h3 : (1 / 2 * (T1 + T2)) ^ 2 ≤ (T1 ^ 2 + T2 ^ 2) / 2 := by
    nlinarith [sq_nonneg (T1 - T2)]
  linarith

/-- **The second moment of the correction from the coefficient bounds** (Giles 2015, §7.1, the
variance rate `β = 4`).  Let `J = 2J_c`, and let the fine and coarse amplitudes of mode `m` be
`X_m = ∑_{i<N} F_{m,i} z_i` and `Y_m = ∑_{i<N} G_{m,i} z_i` with independent standard normal `z_i`.
If `∑_i F_{m,i}² ≤ 100/m⁴` for `0 < m < J`, `∑_i G_{m,i}² ≤ 100/m⁴` and
`∑_i (F_{m,i} − G_{m,i})² ≤ K/J⁴` for `0 < m < J_c`, then `D = ½ ∑_{m<J} X_m² − ½ ∑_{m<J_c} Y_m²`
is square integrable and `E[D²] ≤ (2400K + 960000)/J⁴`. -/
lemma parabolic_variance_of_coef {Jc N : ℕ} (hJc : 1 ≤ Jc) (F G : ℕ → ℕ → ℝ) {K : ℝ}
    (hK : 0 < K)
    (hF : ∀ m ∈ Ico 1 (2 * Jc), ∑ i ∈ range N, F m i ^ 2 ≤ 100 / (m : ℝ) ^ 4)
    (hG : ∀ m ∈ Ico 1 Jc, ∑ i ∈ range N, G m i ^ 2 ≤ 100 / (m : ℝ) ^ 4)
    (hD : ∀ m ∈ Ico 1 Jc, ∑ i ∈ range N, (F m i - G m i) ^ 2 ≤ K / ((2 * Jc : ℕ) : ℝ) ^ 4) :
    MemLp (fun z : ℕ → ℝ => 1 / 2 * ∑ m ∈ Ico 1 (2 * Jc), (∑ i ∈ range N, F m i * z i) ^ 2 -
      1 / 2 * ∑ m ∈ Ico 1 Jc, (∑ i ∈ range N, G m i * z i) ^ 2) 2 stdNormalSeq ∧
    ∫ z, (1 / 2 * ∑ m ∈ Ico 1 (2 * Jc), (∑ i ∈ range N, F m i * z i) ^ 2 -
      1 / 2 * ∑ m ∈ Ico 1 Jc, (∑ i ∈ range N, G m i * z i) ^ 2) ^ 2 ∂stdNormalSeq ≤
      (2400 * K + 960000) / ((2 * Jc : ℕ) : ℝ) ^ 4 := by
  set J : ℝ := ((2 * Jc : ℕ) : ℝ) with hJ_def
  have hJ : 0 < J := by rw [hJ_def]; exact_mod_cast (show 0 < 2 * Jc by omega)
  refine ⟨((memLp_finsetSum _ fun m _ => memLp_sq_linComb (F m) N).const_mul _).sub
    ((memLp_finsetSum _ fun m _ => memLp_sq_linComb (G m) N).const_mul _), ?_⟩
  -- the two families of terms
  have hT1 : ∀ m ∈ Ico 1 Jc, Integrable (fun z : ℕ → ℝ => (m : ℝ) ^ 2 *
      ((∑ i ∈ range N, F m i * z i - ∑ i ∈ range N, G m i * z i) *
        (∑ i ∈ range N, F m i * z i + ∑ i ∈ range N, G m i * z i)) ^ 2) stdNormalSeq ∧
      ∫ z, (m : ℝ) ^ 2 * ((∑ i ∈ range N, F m i * z i - ∑ i ∈ range N, G m i * z i) *
        (∑ i ∈ range N, F m i * z i + ∑ i ∈ range N, G m i * z i)) ^ 2 ∂stdNormalSeq ≤
        1200 * K / J ^ 4 * (1 / (m : ℝ)) ^ 2 := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by
      rw [Finset.mem_Ico] at hm; exact_mod_cast (show 0 < m by omega)
    have hmf : m ∈ Ico 1 (2 * Jc) := by
      rw [Finset.mem_Ico] at hm ⊢; omega
    have h := integral_sq_mul_linComb_le (F m) (G m) N (A := K / J ^ 4) (B := 400 / (m : ℝ) ^ 4)
      (by positivity) (by positivity) (hD m hm) ((hF m hmf).trans_eq (by ring))
      ((hG m hm).trans_eq (by ring))
    refine ⟨h.1.const_mul _, ?_⟩
    rw [integral_const_mul]
    calc (m : ℝ) ^ 2 * ∫ z, ((∑ i ∈ range N, F m i * z i - ∑ i ∈ range N, G m i * z i) *
          (∑ i ∈ range N, F m i * z i + ∑ i ∈ range N, G m i * z i)) ^ 2 ∂stdNormalSeq
        ≤ (m : ℝ) ^ 2 * (3 * (K / J ^ 4) * (400 / (m : ℝ) ^ 4)) :=
          mul_le_mul_of_nonneg_left h.2 (by positivity)
      _ = 1200 * K / J ^ 4 * (1 / (m : ℝ)) ^ 2 := by
          field_simp
          ring
  have hT2 : ∀ m ∈ Ico Jc (2 * Jc), Integrable (fun z : ℕ → ℝ => (m : ℝ) ^ 2 *
      ((∑ i ∈ range N, F m i * z i) ^ 2) ^ 2) stdNormalSeq ∧
      ∫ z, (m : ℝ) ^ 2 * ((∑ i ∈ range N, F m i * z i) ^ 2) ^ 2 ∂stdNormalSeq ≤
        480000 / J ^ 4 * (1 / (m : ℝ)) ^ 2 := by
    intro m hm
    have hm' := Finset.mem_Ico.1 hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmJ : J ≤ 2 * m := by
      rw [hJ_def]; push_cast; exact_mod_cast (show 2 * Jc ≤ 2 * m by omega)
    have hmf : m ∈ Ico 1 (2 * Jc) := by rw [Finset.mem_Ico]; omega
    have h := integral_pow_four_linComb_le (F m) N (hF m hmf)
    refine ⟨h.1.const_mul _, ?_⟩
    rw [integral_const_mul]
    have hJm : J ^ 4 ≤ 16 * (m : ℝ) ^ 4 := by
      have := pow_le_pow_left₀ hJ.le hmJ 4
      linarith [show (2 * (m : ℝ)) ^ 4 = 16 * (m : ℝ) ^ 4 by ring]
    calc (m : ℝ) ^ 2 * ∫ z, ((∑ i ∈ range N, F m i * z i) ^ 2) ^ 2 ∂stdNormalSeq
        ≤ (m : ℝ) ^ 2 * (3 * (100 / (m : ℝ) ^ 4) ^ 2) :=
          mul_le_mul_of_nonneg_left h.2 (by positivity)
      _ = 30000 / (m : ℝ) ^ 4 * (1 / (m : ℝ)) ^ 2 := by
          field_simp
          ring
      _ ≤ 480000 / J ^ 4 * (1 / (m : ℝ)) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  -- the pointwise bound and integration
  have hRint : Integrable (fun z : ℕ → ℝ =>
      ∑ m ∈ Ico 1 Jc, (m : ℝ) ^ 2 *
        ((∑ i ∈ range N, F m i * z i - ∑ i ∈ range N, G m i * z i) *
          (∑ i ∈ range N, F m i * z i + ∑ i ∈ range N, G m i * z i)) ^ 2 +
      ∑ m ∈ Ico Jc (2 * Jc), (m : ℝ) ^ 2 * ((∑ i ∈ range N, F m i * z i) ^ 2) ^ 2)
      stdNormalSeq :=
    (integrable_finsetSum _ fun m hm => (hT1 m hm).1).add
      (integrable_finsetSum _ fun m hm => (hT2 m hm).1)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hRint
    (Eventually.of_forall fun z => parabolic_sq_half_sub_le hJc
      (fun m => ∑ i ∈ range N, F m i * z i)
      (fun m => ∑ i ∈ range N, G m i * z i))).trans ?_
  rw [integral_add (integrable_finsetSum _ fun m hm => (hT1 m hm).1)
    (integrable_finsetSum _ fun m hm => (hT2 m hm).1),
    integral_finsetSum _ fun m hm => (hT1 m hm).1,
    integral_finsetSum _ fun m hm => (hT2 m hm).1]
  have hs1 := Finset.sum_le_sum fun m hm => (hT1 m hm).2
  have hs2 := Finset.sum_le_sum fun m hm => (hT2 m hm).2
  rw [← Finset.mul_sum] at hs1 hs2
  have hw1 := sum_Ico_one_div_sq_le_two (a := 1) (b := Jc) le_rfl
  have hw2 := sum_Ico_one_div_sq_le_two (a := Jc) (b := 2 * Jc) hJc
  have hK' : 0 ≤ 1200 * K / J ^ 4 := by positivity
  have hc' : 0 ≤ 480000 / J ^ 4 := by positivity
  calc _ ≤ 1200 * K / J ^ 4 * ∑ m ∈ Ico 1 Jc, (1 / (m : ℝ)) ^ 2 +
        480000 / J ^ 4 * ∑ m ∈ Ico Jc (2 * Jc), (1 / (m : ℝ)) ^ 2 := add_le_add hs1 hs2
    _ ≤ 1200 * K / J ^ 4 * 2 + 480000 / J ^ 4 * 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hw1 hK') (mul_le_mul_of_nonneg_left hw2 hc')
    _ = (2400 * K + 960000) / J ^ 4 := by ring

/-! ### The coefficients of the fine and the coarse mode amplitudes -/

/-- `(ax + y)² ≤ a x² + y²/t` for `a ≥ 0`, `t > 0`, `a + t ≤ 1`. -/
lemma sq_mul_add_le_div {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) (hat : a + t ≤ 1) (x y : ℝ) :
    (a * x + y) ^ 2 ≤ a * x ^ 2 + y ^ 2 / t := by
  have h : 0 ≤ 1 - a - t := by linarith
  have key : t * (a * x + y) ^ 2 ≤ t * (a * x ^ 2) + y ^ 2 := by
    nlinarith [mul_nonneg ha (sq_nonneg (t * x - y)),
      mul_nonneg (mul_nonneg ht.le ha) (mul_nonneg h (sq_nonneg x)), mul_nonneg h (sq_nonneg y)]
  have e : a * x ^ 2 + y ^ 2 / t = (t * (a * x ^ 2) + y ^ 2) / t := by
    field_simp
  rw [e, le_div_iff₀ ht]
  linarith

/-- Splitting a sum over `4(r + 1)` fine steps into the first `4r` and the last coarse step. -/
lemma sum_range_four_mul_succ (h : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ range (4 * (r + 1)), h i =
      ∑ i ∈ range (4 * r), h i + ∑ q ∈ range 4, h (4 * r + q) := by
  rw [show 4 * (r + 1) = 4 * r + 4 by ring, Finset.sum_range_add]

/-- A function of the coarse step `⌊i/4⌋` summed over `4r` fine steps:
`∑_{i<4r} g(⌊i/4⌋) = 4 ∑_{p<r} g(p)`. -/
lemma sum_range_four_mul_comp_div (g : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ range (4 * r), g (i / 4) = 4 * ∑ p ∈ range r, g p := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : ∀ q ∈ range 4, g ((4 * r + q) / 4) = g r := fun q hq => by
      rw [Finset.mem_range] at hq
      congr 1
      omega
    rw [sum_range_four_mul_succ, ih, Finset.sum_congr rfl h, Finset.sum_range_succ g r,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring

/-- The geometric bound `∑_{i<n} (κ μ^{n−1−i})² ≤ κ²/(1 − μ)` for `0 ≤ μ < 1`. -/
lemma sum_sq_mul_pow_le (κ μ : ℝ) (h0 : 0 ≤ μ) (h1 : μ < 1) (n : ℕ) :
    ∑ i ∈ range n, (κ * μ ^ (n - 1 - i)) ^ 2 ≤ κ ^ 2 / (1 - μ) := by
  have hr := Finset.sum_range_reflect (fun k => κ ^ 2 * (μ ^ 2) ^ k) n
  have e : ∑ i ∈ range n, (κ * μ ^ (n - 1 - i)) ^ 2 = κ ^ 2 * ∑ k ∈ range n, (μ ^ 2) ^ k := by
    rw [Finset.mul_sum, ← hr]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (n - 1 - i) 2]
  rw [e]
  have hg : ∑ k ∈ range n, (μ ^ 2) ^ k ≤ 1 / (1 - μ ^ 2) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) (sq_nonneg μ) (by nlinarith)
    rwa [pow_zero, ← Finset.range_eq_Ico] at this
  have h2 : 1 / (1 - μ ^ 2) ≤ 1 / (1 - μ) :=
    one_div_le_one_div_of_le (by linarith) (by nlinarith)
  calc κ ^ 2 * ∑ k ∈ range n, (μ ^ 2) ^ k ≤ κ ^ 2 * (1 / (1 - μ)) :=
        mul_le_mul_of_nonneg_left (hg.trans h2) (sq_nonneg κ)
    _ = κ ^ 2 / (1 - μ) := by ring

/-- **The coefficient recursion over one coarse step** (Giles 2015, §7.1 with §5.1: the coarse path
is driven by the sums of four fine Brownian increments, since `k_ℓ = 4k_{ℓ+1}`; see
`parabolic_coupling`).  Let the fine coefficients after `4r` fine steps be
`s c_f μ_f^{4r−1−i}` and the coarse ones after `r` coarse steps `s c_c μ_c^{r−1−⌊i/4⌋}`, with
`a = μ_f⁴`, `a + t ≤ 1`, `t > 0`, and the coarse coefficients bounded by `G` in `ℓ²`.  Then their
difference satisfies `∑_{i<4r} (…)² ≤ ((a − μ_c)² G/t + ∑_{q<4} (s c_f μ_f^{3−q} − s c_c)²)/t`. -/
lemma parabolic_diff_rec_bound {s cf cc μf μc t Gmax : ℝ} (ht : 0 < t)
    (hat : μf ^ 4 + t ≤ 1)
    (hG : ∀ r : ℕ, ∑ i ∈ range (4 * r), (s * cc * μc ^ (r - 1 - i / 4)) ^ 2 ≤ Gmax) (r : ℕ) :
    ∑ i ∈ range (4 * r), (s * cf * μf ^ (4 * r - 1 - i) - s * cc * μc ^ (r - 1 - i / 4)) ^ 2 ≤
      ((μf ^ 4 - μc) ^ 2 * Gmax / t +
        ∑ q ∈ range 4, (s * cf * μf ^ (3 - q) - s * cc) ^ 2) / t := by
  set a : ℝ := μf ^ 4 with ha_def
  set B : ℝ := (a - μc) ^ 2 * Gmax / t +
    ∑ q ∈ range 4, (s * cf * μf ^ (3 - q) - s * cc) ^ 2 with hB_def
  have hGmax : 0 ≤ Gmax := by simpa using hG 0
  have hB : 0 ≤ B := by positivity
  have ha : 0 ≤ a := by positivity
  induction r with
  | zero => simp only [mul_zero, Finset.range_zero, Finset.sum_empty]; positivity
  | succ r ih =>
    rw [sum_range_four_mul_succ]
    have h1 : ∀ i ∈ range (4 * r),
        (s * cf * μf ^ (4 * (r + 1) - 1 - i) - s * cc * μc ^ (r + 1 - 1 - i / 4)) ^ 2 ≤
          a * (s * cf * μf ^ (4 * r - 1 - i) - s * cc * μc ^ (r - 1 - i / 4)) ^ 2 +
            (a - μc) ^ 2 * (s * cc * μc ^ (r - 1 - i / 4)) ^ 2 / t := by
      intro i hi
      rw [Finset.mem_range] at hi
      have e1 : μf ^ (4 * (r + 1) - 1 - i) = a * μf ^ (4 * r - 1 - i) := by
        rw [show 4 * (r + 1) - 1 - i = (4 * r - 1 - i) + 4 by omega, pow_add, mul_comm]
      have e2 : μc ^ (r + 1 - 1 - i / 4) = μc * μc ^ (r - 1 - i / 4) := by
        rw [show r + 1 - 1 - i / 4 = (r - 1 - i / 4) + 1 by omega, pow_succ, mul_comm]
      rw [e1, e2]
      have h := sq_mul_add_le_div ha ht hat
        (s * cf * μf ^ (4 * r - 1 - i) - s * cc * μc ^ (r - 1 - i / 4))
        ((a - μc) * (s * cc * μc ^ (r - 1 - i / 4)))
      convert h using 1 <;> ring
    have h2 : ∀ q ∈ range 4, (s * cf * μf ^ (4 * (r + 1) - 1 - (4 * r + q)) -
        s * cc * μc ^ (r + 1 - 1 - (4 * r + q) / 4)) ^ 2 =
        (s * cf * μf ^ (3 - q) - s * cc) ^ 2 := by
      intro q hq
      rw [Finset.mem_range] at hq
      rw [show 4 * (r + 1) - 1 - (4 * r + q) = 3 - q by omega,
        show r + 1 - 1 - (4 * r + q) / 4 = 0 by omega, pow_zero, mul_one]
    rw [Finset.sum_congr rfl h2]
    calc _ ≤ ∑ i ∈ range (4 * r),
            (a * (s * cf * μf ^ (4 * r - 1 - i) - s * cc * μc ^ (r - 1 - i / 4)) ^ 2 +
              (a - μc) ^ 2 * (s * cc * μc ^ (r - 1 - i / 4)) ^ 2 / t) +
            ∑ q ∈ range 4, (s * cf * μf ^ (3 - q) - s * cc) ^ 2 :=
          add_le_add_left (Finset.sum_le_sum h1) _
      _ = a * ∑ i ∈ range (4 * r),
              (s * cf * μf ^ (4 * r - 1 - i) - s * cc * μc ^ (r - 1 - i / 4)) ^ 2 +
            (a - μc) ^ 2 * (∑ i ∈ range (4 * r), (s * cc * μc ^ (r - 1 - i / 4)) ^ 2) / t +
            ∑ q ∈ range 4, (s * cf * μf ^ (3 - q) - s * cc) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum]
      _ ≤ a * (B / t) + (a - μc) ^ 2 * Gmax / t +
            ∑ q ∈ range 4, (s * cf * μf ^ (3 - q) - s * cc) ^ 2 := by
          gcongr
          exact hG r
      _ = (a + t) * B / t := by
          rw [hB_def]
          field_simp
          ring
      _ ≤ B / t := by
          gcongr
          nlinarith

/-- For a mode `0 < m < J` the half angle `x = πm/(2J) ∈ (0, π/2)` has `sin x > 0`, `cos x > 0`
and `m/J ≤ sin x ≤ 2m/J` (Jordan's inequality and `sin x ≤ x`). -/
lemma sineMode_angle_bounds {J m : ℕ} (hm : m ∈ Ico 1 J) :
    0 < Real.sin (π * m / (2 * J)) ∧ 0 < Real.cos (π * m / (2 * J)) ∧
      (m : ℝ) / J ≤ Real.sin (π * m / (2 * J)) ∧ Real.sin (π * m / (2 * J)) ≤ 2 * m / J := by
  rw [Finset.mem_Ico] at hm
  have hJ : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  have hmJ : (m : ℝ) < J := by exact_mod_cast hm.2
  have hpi := Real.pi_pos
  have hx0 : 0 < π * m / (2 * J) := by positivity
  have hx1 : π * m / (2 * J) < π / 2 := by
    rw [div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith
  refine ⟨Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith),
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩, ?_, ?_⟩
  · have h := Real.mul_le_sin hx0.le hx1.le
    have e : 2 / π * (π * m / (2 * J)) = m / J := by field_simp
    linarith
  · have h := Real.sin_le hx0.le
    have : π * m / (2 * J) ≤ 2 * m / J := by
      rw [div_le_div_iff₀ (by positivity) hJ]
      nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity : (0 : ℝ) ≤ m * J)]
    linarith

/-- `(1 − cos y)² ≤ 4`. -/
lemma one_sub_cos_sq_le_four (y : ℝ) : (1 - Real.cos y) ^ 2 ≤ 4 := by
  have h1 := Real.neg_one_le_cos y
  have h2 := Real.cos_le_one y
  nlinarith

/-- **The mode amplitudes are `O(m⁻²)`** (Giles 2015, §7.1): for a mode `0 < m < J` with the
paper's `k/h² = ¼` and `ΔW = z/(2J)`, the coefficients of the amplitude after `n` steps satisfy
`∑_{i<n} (10/(2J) · c_m μ_m^{n−1−i})² ≤ 100/m⁴`, uniformly in `J` and `n`. -/
lemma parabolic_sum_sq_coef_le {J m : ℕ} (hm : m ∈ Ico 1 J) (n : ℕ) :
    ∑ i ∈ range n, (10 / (2 * (J : ℝ)) * sineCoef J m * sineEig (1 / 4) J m ^ (n - 1 - i)) ^ 2 ≤
      100 / (m : ℝ) ^ 4 := by
  obtain ⟨hS, hC, hSl, -⟩ := sineMode_angle_bounds hm
  have hm' := Finset.mem_Ico.1 hm
  have hJ : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set S := Real.sin (π * m / (2 * J)) with hS_def
  set C := Real.cos (π * m / (2 * J)) with hC_def
  have hSC : S ^ 2 + C ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  rw [sineEig_quarter, sineCoef_eq (by omega) (by omega)]
  refine (sum_sq_mul_pow_le _ _ (sq_nonneg C) (by nlinarith) n).trans ?_
  have e1 : 1 - C ^ 2 = S ^ 2 := by linarith
  have e2 : 10 / (2 * (J : ℝ)) * ((1 - Real.cos (π * m)) / J * (C / S)) =
      5 * (1 - Real.cos (π * m)) * C / (J ^ 2 * S) := by
    field_simp
    ring
  rw [e1, e2, div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (5 * (1 - Real.cos (π * m)) * C) ^ 2 ≤ 100 := by
    have := one_sub_cos_sq_le_four (π * m)
    have hC1 : C ^ 2 ≤ 1 := by nlinarith
    calc (5 * (1 - Real.cos (π * m)) * C) ^ 2 = 25 * (1 - Real.cos (π * m)) ^ 2 * C ^ 2 := by
          ring
      _ ≤ 25 * 4 * 1 := by gcongr
      _ = 100 := by norm_num
  have h2 : (m : ℝ) ^ 4 ≤ (J * S) ^ 4 := by
    have : (m : ℝ) ≤ J * S := by
      rw [div_le_iff₀ hJ] at hSl
      linarith
    exact pow_le_pow_left₀ hm0.le this 4
  calc (5 * (1 - Real.cos (π * m)) * C) ^ 2 * (m : ℝ) ^ 4 ≤ 100 * (J * S) ^ 4 :=
        mul_le_mul h1 h2 (by positivity) (by norm_num)
    _ = 100 * ((J ^ 2 * S) ^ 2 * S ^ 2) := by ring

/-- `((1 − t)^{k+1} − (1 − t) + t)² ≤ 4t²` for `0 ≤ t ≤ ½` and `k ≤ 3`. -/
lemma parabolic_poly_sq_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) {k : ℕ} (hk : k ≤ 3) :
    ((1 - t) * (1 - t) ^ k - (1 - t) + t) ^ 2 ≤ 4 * t ^ 2 := by
  have key : ∀ q : ℝ, -2 ≤ q → q ≤ 2 → (t * q) ^ 2 ≤ 4 * t ^ 2 := fun q hq1 hq2 => by
    rw [mul_pow]
    nlinarith [mul_nonneg (by linarith : 0 ≤ q + 2) (by linarith : 0 ≤ 2 - q), sq_nonneg t]
  interval_cases k
  · rw [show (1 - t) * (1 - t) ^ 0 - (1 - t) + t = t * 1 by ring]
    exact key 1 (by norm_num) (by norm_num)
  · rw [show (1 - t) * (1 - t) ^ 1 - (1 - t) + t = t * t by ring]
    exact key t (by linarith) (by linarith)
  · rw [show (1 - t) * (1 - t) ^ 2 - (1 - t) + t = t * (-1 + 3 * t - t ^ 2) by ring]
    exact key _ (by nlinarith) (by nlinarith)
  · rw [show (1 - t) * (1 - t) ^ 3 - (1 - t) + t = t * (-2 + 6 * t - 4 * t ^ 2 + t ^ 3) by ring]
    exact key _ (by nlinarith [mul_nonneg h0 (sq_nonneg t), sq_nonneg (t - 2)])
      (by nlinarith [mul_nonneg h0 (sq_nonneg t)])

/-- `((1 − t)⁴ − (1 − 2t)²)² ≤ 4t⁴` for `0 < t < ½`: four fine steps against one coarse step
of the mode recursion agree to `O(t²)`. -/
lemma parabolic_quartic_sq_le {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) :
    ((1 - t) ^ 4 - (1 - 2 * t) ^ 2) ^ 2 ≤ 4 * t ^ 4 := by
  have hp : (1 - t) ^ 4 - (1 - 2 * t) ^ 2 = t ^ 2 * (2 - 4 * t + t ^ 2) := by ring
  rw [hp, mul_pow, show 4 * t ^ 4 = (t ^ 2) ^ 2 * 4 by ring]
  have h3 : (2 - 4 * t + t ^ 2) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ 2 - 4 * t + t ^ 2)
      (by nlinarith : (0 : ℝ) ≤ 4 * t - t ^ 2)]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The new coefficients of one coarse step (Giles 2015, §7.1): with `S = sin x`, `C = cos x`,
`S² < ½`, `c_f = σ/J · C/S`, `c_c = σ/(J/2) · cos 2x/sin 2x` and `σ² ≤ 4`, for `k ≤ 3`,
`(10/(2J) · c_f (C²)^k − 10/(2J) · c_c)² ≤ 800 S²/J⁴`. -/
lemma parabolic_noise_coef_le {S C σ J : ℝ} (hS : 0 < S) (hC : 0 < C) (hSC : S ^ 2 + C ^ 2 = 1)
    (ht1 : S ^ 2 < 1 / 2) (hJ : 0 < J) (hσ : σ ^ 2 ≤ 4) {k : ℕ} (hk : k ≤ 3) :
    (10 / (2 * J) * (σ / J * (C / S)) * (C ^ 2) ^ k -
      10 / (2 * J) * (σ / (J / 2) * ((C ^ 2 - S ^ 2) / (2 * S * C)))) ^ 2 ≤
      800 * S ^ 2 / J ^ 4 := by
  have hwid : (10 / (2 * J) * (σ / J * (C / S)) * (C ^ 2) ^ k -
      10 / (2 * J) * (σ / (J / 2) * ((C ^ 2 - S ^ 2) / (2 * S * C)))) * (J ^ 2 * S * C) =
      5 * σ * (C ^ 2 * (C ^ 2) ^ k - C ^ 2 + S ^ 2) := by
    field_simp
    ring
  generalize (10 / (2 * J) * (σ / J * (C / S)) * (C ^ 2) ^ k -
      10 / (2 * J) * (σ / (J / 2) * ((C ^ 2 - S ^ 2) / (2 * S * C)))) = w at hwid ⊢
  have hC2t : C ^ 2 = 1 - S ^ 2 := by linarith
  have hp := parabolic_poly_sq_le (t := S ^ 2) (by positivity) ht1.le hk
  rw [← hC2t] at hp
  have h1 : (w * (J ^ 2 * S * C)) ^ 2 ≤ 400 * (S ^ 2) ^ 2 := by
    rw [hwid, mul_pow, mul_pow]
    calc 5 ^ 2 * σ ^ 2 * (C ^ 2 * (C ^ 2) ^ k - C ^ 2 + S ^ 2) ^ 2 ≤
          5 ^ 2 * 4 * (4 * (S ^ 2) ^ 2) := by gcongr
      _ = 400 * (S ^ 2) ^ 2 := by ring
  have h2 : (w * (J ^ 2 * S * C)) ^ 2 = w ^ 2 * J ^ 4 * S ^ 2 * C ^ 2 := by ring
  rw [h2, hC2t] at h1
  have h3 : w ^ 2 * J ^ 4 * S ^ 2 * (1 / 2) ≤ w ^ 2 * J ^ 4 * S ^ 2 * (1 - S ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : w ^ 2 * J ^ 4 * S ^ 2 ≤ 800 * S ^ 2 * S ^ 2 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  exact le_of_mul_le_mul_right h4 (by positivity)

/-- The final arithmetic of the difference bound: if `t² ≤ 16m⁴/J⁴`, then
`(4t⁴ (100/m⁴)/t + 4 (800t/J⁴))/t ≤ 9600/J⁴`. -/
lemma parabolic_diff_final_le {t m J : ℝ} (ht : 0 < t) (hm : 0 < m) (hJ : 0 < J)
    (htm : t ^ 2 ≤ 16 * m ^ 4 / J ^ 4) :
    (4 * t ^ 4 * (100 / m ^ 4) / t + 4 * (800 * t / J ^ 4)) / t ≤ 9600 / J ^ 4 := by
  have e : (4 * t ^ 4 * (100 / m ^ 4) / t + 4 * (800 * t / J ^ 4)) / t =
      400 * (t ^ 2 / m ^ 4) + 3200 / J ^ 4 := by
    field_simp
    ring
  rw [e]
  have h4 : t ^ 2 / m ^ 4 ≤ 16 / J ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [le_div_iff₀ (by positivity)] at htm
    nlinarith
  calc 400 * (t ^ 2 / m ^ 4) + 3200 / J ^ 4 ≤ 400 * (16 / J ^ 4) + 3200 / J ^ 4 := by gcongr
    _ = 9600 / J ^ 4 := by ring

/-- The difference bound of Giles 2015, §7.1, for abstract trigonometric data: the fine and coarse
coefficients of one mode differ by at most `9600/J⁴` in `ℓ²`. -/
lemma parabolic_sum_sq_diff_coef_le_aux {s cf cc μc S C σ J m : ℝ} (hS : 0 < S) (hC : 0 < C)
    (hSC : S ^ 2 + C ^ 2 = 1) (ht1 : S ^ 2 < 1 / 2) (hJ : 0 < J) (hm : 0 < m)
    (hSm : S ≤ 2 * m / J) (hσ : σ ^ 2 ≤ 4) (hs : s = 10 / (2 * J))
    (hcf : cf = σ / J * (C / S)) (hcc : cc = σ / (J / 2) * ((C ^ 2 - S ^ 2) / (2 * S * C)))
    (hμc : μc = (C ^ 2 - S ^ 2) ^ 2)
    (hG : ∀ r : ℕ, ∑ i ∈ range (4 * r), (s * cc * μc ^ (r - 1 - i / 4)) ^ 2 ≤ 100 / m ^ 4)
    (r : ℕ) :
    ∑ i ∈ range (4 * r), (s * cf * (C ^ 2) ^ (4 * r - 1 - i) - s * cc * μc ^ (r - 1 - i / 4)) ^ 2
      ≤ 9600 / J ^ 4 := by
  have ht0 : 0 < S ^ 2 := by positivity
  have hC2t : C ^ 2 = 1 - S ^ 2 := by linarith
  have hat : (C ^ 2) ^ 4 + S ^ 2 ≤ 1 := by
    rw [hC2t]
    have h1t : 0 ≤ 1 - S ^ 2 := by linarith
    nlinarith [pow_le_one₀ h1t (by linarith : 1 - S ^ 2 ≤ 1) (n := 3)]
  refine (parabolic_diff_rec_bound ht0 hat hG r).trans ?_
  have hab : ((C ^ 2) ^ 4 - μc) ^ 2 ≤ 4 * (S ^ 2) ^ 4 := by
    rw [hμc, hC2t, show 1 - S ^ 2 - S ^ 2 = 1 - 2 * S ^ 2 by ring]
    exact parabolic_quartic_sq_le ht0 ht1
  have hterm : ∀ q ∈ range 4, (s * cf * (C ^ 2) ^ (3 - q) - s * cc) ^ 2 ≤
      800 * S ^ 2 / J ^ 4 := by
    intro q hq
    rw [Finset.mem_range] at hq
    rw [hs, hcf, hcc]
    exact parabolic_noise_coef_le hS hC hSC ht1 hJ hσ (by omega)
  have hnoise : ∑ q ∈ range 4, (s * cf * (C ^ 2) ^ (3 - q) - s * cc) ^ 2 ≤
      4 * (800 * S ^ 2 / J ^ 4) := by
    refine (Finset.sum_le_sum hterm).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  have htm : (S ^ 2) ^ 2 ≤ 16 * m ^ 4 / J ^ 4 := by
    have h1 : S ^ 2 ≤ (2 * m / J) ^ 2 := pow_le_pow_left₀ hS.le hSm 2
    calc (S ^ 2) ^ 2 ≤ ((2 * m / J) ^ 2) ^ 2 := pow_le_pow_left₀ ht0.le h1 2
      _ = 16 * m ^ 4 / J ^ 4 := by ring
  calc ((((C ^ 2) ^ 4 - μc) ^ 2 * (100 / m ^ 4) / S ^ 2 +
        ∑ q ∈ range 4, (s * cf * (C ^ 2) ^ (3 - q) - s * cc) ^ 2) / S ^ 2)
      ≤ (4 * (S ^ 2) ^ 4 * (100 / m ^ 4) / S ^ 2 + 4 * (800 * S ^ 2 / J ^ 4)) / S ^ 2 := by
        gcongr
    _ ≤ 9600 / J ^ 4 := parabolic_diff_final_le ht0 hm hJ htm

/-- **The fine and the coarse amplitude of a mode differ by `O(J⁻²)`** (Giles 2015, §7.1: "the
solution error is `O(2^{−2ℓ})`", for one mode of the coupled pair).  For `J = 2J_c` fine
intervals, a mode `0 < m < J_c` and `r` coarse steps, the coefficients of the fine amplitude after
`4r` fine steps and of the coarse amplitude after `r` coarse steps (with the summed increments)
differ by at most `9600/J⁴` in `ℓ²`. -/
lemma parabolic_sum_sq_diff_coef_le {Jc m : ℕ} (hm : m ∈ Ico 1 Jc) (r : ℕ) :
    ∑ i ∈ range (4 * r), (10 / (2 * ((2 * Jc : ℕ) : ℝ)) * sineCoef (2 * Jc) m *
        sineEig (1 / 4) (2 * Jc) m ^ (4 * r - 1 - i) -
      10 / (2 * ((2 * Jc : ℕ) : ℝ)) * sineCoef Jc m * sineEig (1 / 4) Jc m ^ (r - 1 - i / 4)) ^ 2
      ≤ 9600 / ((2 * Jc : ℕ) : ℝ) ^ 4 := by
  have hm' := Finset.mem_Ico.1 hm
  have hmf : m ∈ Ico 1 (2 * Jc) := Finset.mem_Ico.2 ⟨hm'.1, by omega⟩
  obtain ⟨hS, hC, -, hSu⟩ := sineMode_angle_bounds hmf
  obtain ⟨-, hC2, -, -⟩ := sineMode_angle_bounds hm
  have hJ : (0 : ℝ) < ((2 * Jc : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * Jc by omega)
  have hJc : (Jc : ℝ) = ((2 * Jc : ℕ) : ℝ) / 2 := by push_cast; ring
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h2x : π * m / (2 * Jc) = 2 * (π * m / (2 * ((2 * Jc : ℕ) : ℝ))) := by
    rw [hJc]; field_simp
  have hSC := Real.sin_sq_add_cos_sq (π * m / (2 * ((2 * Jc : ℕ) : ℝ)))
  have hcos2 : Real.cos (2 * (π * m / (2 * ((2 * Jc : ℕ) : ℝ)))) =
      Real.cos (π * m / (2 * ((2 * Jc : ℕ) : ℝ))) ^ 2 -
        Real.sin (π * m / (2 * ((2 * Jc : ℕ) : ℝ))) ^ 2 := by
    rw [Real.cos_two_mul]; linarith
  rw [h2x, hcos2] at hC2
  have hG : ∀ r : ℕ, ∑ i ∈ range (4 * r), (10 / (2 * ((2 * Jc : ℕ) : ℝ)) * sineCoef Jc m *
      sineEig (1 / 4) Jc m ^ (r - 1 - i / 4)) ^ 2 ≤ 100 / (m : ℝ) ^ 4 := by
    intro r
    rw [sum_range_four_mul_comp_div (fun p => (10 / (2 * ((2 * Jc : ℕ) : ℝ)) * sineCoef Jc m *
      sineEig (1 / 4) Jc m ^ (r - 1 - p)) ^ 2) r, Finset.mul_sum]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) (parabolic_sum_sq_coef_le hm r)
    rw [hJc]
    field_simp
    ring
  rw [sineEig_quarter (2 * Jc) m]
  refine parabolic_sum_sq_diff_coef_le_aux hS hC hSC (by nlinarith) hJ hm0 hSu
    (one_sub_cos_sq_le_four _) rfl
    (sineCoef_eq (by omega) (by omega)) ?_ ?_ hG r
  · rw [sineCoef_eq (by omega) (by omega), h2x, hcos2, Real.sin_two_mul, hJc]
  · rw [sineEig_quarter, h2x, hcos2]

/-! ### The levels, the coupling and the variance rate -/

/-- **The level-`ℓ` output of the parabolic example** (Giles 2015, §7.1, p. 51: "The output
functional is chosen to be `P = ∫₀¹ u²(x, 0.25)`. … The level `ℓ` approximation uses
`h_ℓ = 2^{−(ℓ+1)}`, `k_ℓ = ¼ h_ℓ²`"): `h ∑_{j=0}^{J} (u^N_j)²` with `J = 2^{ℓ+1}`, `h = 1/J`,
`N = 4^{ℓ+1}` steps (`N k_ℓ = ¼`), `λ = ¼` and the Brownian increments `ΔW^n = √k_ℓ z_n =
z_n/2^{ℓ+2}` from the standard normal inputs `z`.  As `u_0 = u_J = 0`, the sum is the trapezoidal
rule. -/
noncomputable def parabolicP (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  ((2 : ℝ) ^ (ℓ + 1))⁻¹ * ∑ j ∈ range (2 ^ (ℓ + 1) + 1),
    parabolicPath (1 / 4) (2 ^ (ℓ + 1)) (fun n => z n / 2 ^ (ℓ + 2)) (4 ^ (ℓ + 1)) j ^ 2

/-- The grid quadrature in the sine modes, with explicit coefficients (Giles 2015, §7.1):
`J⁻¹ ∑_j (u^N_j)² = ½ ∑_m (∑_{i<N} 10/(2J) · c_m μ_m^{N−1−i} z_i)²` for `ΔW = z/(2J)`. -/
lemma parabolic_quadrature_eq_sum_modes {J : ℕ} (hJ : 0 < J) (N : ℕ) (z : ℕ → ℝ) :
    (J : ℝ)⁻¹ * ∑ j ∈ range (J + 1),
        parabolicPath (1 / 4) J (fun n => z n / (2 * J)) N j ^ 2 =
      1 / 2 * ∑ m ∈ Ico 1 J, (∑ i ∈ range N,
        10 / (2 * (J : ℝ)) * sineCoef J m * sineEig (1 / 4) J m ^ (N - 1 - i) * z i) ^ 2 := by
  have hJ' : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  rw [sum_sq_parabolicPath, ← mul_assoc, show (J : ℝ)⁻¹ * (J / 2) = 1 / 2 by field_simp]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [modeAmp_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `P_ℓ` as half a sum of squares of linear combinations of the inputs (Giles 2015, §7.1). -/
lemma parabolicP_eq (ℓ : ℕ) (z : ℕ → ℝ) :
    parabolicP ℓ z = 1 / 2 * ∑ m ∈ Ico 1 (2 ^ (ℓ + 1)), (∑ i ∈ range (4 ^ (ℓ + 1)),
      10 / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)) * sineCoef (2 ^ (ℓ + 1)) m *
        sineEig (1 / 4) (2 ^ (ℓ + 1)) m ^ (4 ^ (ℓ + 1) - 1 - i) * z i) ^ 2 := by
  have e : (fun n => z n / (2 : ℝ) ^ (ℓ + 2)) =
      fun n => z n / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)) := by
    funext n
    push_cast
    ring
  rw [parabolicP, e, ← parabolic_quadrature_eq_sum_modes (by positivity)]
  congr 1
  push_cast
  ring

/-- `pairAvg (pairAvg z) p = (z_{4p} + z_{4p+1} + z_{4p+2} + z_{4p+3})/2`. -/
lemma pairAvg_pairAvg_apply (z : ℕ → ℝ) (p : ℕ) :
    pairAvg (pairAvg z) p = (z (4 * p) + z (4 * p + 1) + z (4 * p + 2) + z (4 * p + 3)) / 2 := by
  rw [pairAvg, pairAvg, pairAvg]
  rw [show 2 * (2 * p + 1) + 1 = 4 * p + 3 by ring, show 2 * (2 * p + 1) = 4 * p + 2 by ring,
    show 2 * (2 * p) + 1 = 4 * p + 1 by ring, show 2 * (2 * p) = 4 * p by ring,
    ← add_div, div_div, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Regrouping a linear combination of the quadruple averages by the fine inputs. -/
lemma sum_range_mul_quadAvg (β : ℕ → ℝ) (M : ℕ) (z : ℕ → ℝ) :
    ∑ p ∈ range M, β p * ((z (4 * p) + z (4 * p + 1) + z (4 * p + 2) + z (4 * p + 3)) / 2) =
      ∑ i ∈ range (4 * M), β (i / 4) / 2 * z i := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, sum_range_four_mul_succ]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [show (4 * M + 0) / 4 = M by omega, show (4 * M + 1) / 4 = M by omega,
      show (4 * M + 2) / 4 = M by omega, show (4 * M + 3) / 4 = M by omega, add_zero]
    ring

/-- The coarse sample `P_ℓ(pairAvg (pairAvg z))` as half a sum of squares of linear
combinations of the fine inputs (Giles 2015, §7.1). -/
lemma parabolicP_pairAvg_eq (ℓ : ℕ) (z : ℕ → ℝ) :
    parabolicP ℓ (pairAvg (pairAvg z)) = 1 / 2 * ∑ m ∈ Ico 1 (2 ^ (ℓ + 1)),
      (∑ i ∈ range (4 * 4 ^ (ℓ + 1)), 10 / (2 * ((2 * 2 ^ (ℓ + 1) : ℕ) : ℝ)) *
        sineCoef (2 ^ (ℓ + 1)) m * sineEig (1 / 4) (2 ^ (ℓ + 1)) m ^ (4 ^ (ℓ + 1) - 1 - i / 4) *
          z i) ^ 2 := by
  rw [parabolicP_eq]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  simp only [pairAvg_pairAvg_apply]
  rw [sum_range_mul_quadAvg (fun p => 10 / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)) *
    sineCoef (2 ^ (ℓ + 1)) m *
    sineEig (1 / 4) (2 ^ (ℓ + 1)) m ^ (4 ^ (ℓ + 1) - 1 - p))]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- The fine sample `P_{ℓ+1}` with `J = 2 · 2^{ℓ+1}` and `N = 4 · 4^{ℓ+1}` (Giles 2015,
§7.1). -/
lemma parabolicP_succ_eq (ℓ : ℕ) (z : ℕ → ℝ) :
    parabolicP (ℓ + 1) z = 1 / 2 * ∑ m ∈ Ico 1 (2 * 2 ^ (ℓ + 1)),
      (∑ i ∈ range (4 * 4 ^ (ℓ + 1)), 10 / (2 * ((2 * 2 ^ (ℓ + 1) : ℕ) : ℝ)) *
        sineCoef (2 * 2 ^ (ℓ + 1)) m *
          sineEig (1 / 4) (2 * 2 ^ (ℓ + 1)) m ^ (4 * 4 ^ (ℓ + 1) - 1 - i) * z i) ^ 2 := by
  rw [parabolicP_eq, ← pow_succ', ← pow_succ']

/-- The coarse coefficients on the fine inputs are bounded as the level-`ℓ` ones (Giles 2015,
§7.1). -/
lemma parabolic_sum_sq_coarse_coef_le {Jc m : ℕ} (hm : m ∈ Ico 1 Jc) (M : ℕ) :
    ∑ i ∈ range (4 * M), (10 / (2 * ((2 * Jc : ℕ) : ℝ)) * sineCoef Jc m *
      sineEig (1 / 4) Jc m ^ (M - 1 - i / 4)) ^ 2 ≤ 100 / (m : ℝ) ^ 4 := by
  rw [sum_range_four_mul_comp_div (fun p => (10 / (2 * ((2 * Jc : ℕ) : ℝ)) * sineCoef Jc m *
    sineEig (1 / 4) Jc m ^ (M - 1 - p)) ^ 2) M, Finset.mul_sum]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) (parabolic_sum_sq_coef_le hm M)
  have hJc : (Jc : ℝ) ≠ 0 := by
    rw [Finset.mem_Ico] at hm
    exact_mod_cast (show Jc ≠ 0 by omega)
  push_cast
  field_simp
  ring

/-- The variance bound of Giles 2015, §7.1, in the mode coordinates. -/
lemma parabolic_level_variance_aux {Jc : ℕ} (hJc : 1 ≤ Jc) (M : ℕ) :
    MemLp (fun z : ℕ → ℝ => 1 / 2 * ∑ m ∈ Ico 1 (2 * Jc), (∑ i ∈ range (4 * M),
        10 / (2 * ((2 * Jc : ℕ) : ℝ)) * sineCoef (2 * Jc) m *
          sineEig (1 / 4) (2 * Jc) m ^ (4 * M - 1 - i) * z i) ^ 2 -
      1 / 2 * ∑ m ∈ Ico 1 Jc, (∑ i ∈ range (4 * M), 10 / (2 * ((2 * Jc : ℕ) : ℝ)) *
        sineCoef Jc m * sineEig (1 / 4) Jc m ^ (M - 1 - i / 4) * z i) ^ 2) 2 stdNormalSeq ∧
    ∫ z, (1 / 2 * ∑ m ∈ Ico 1 (2 * Jc), (∑ i ∈ range (4 * M),
        10 / (2 * ((2 * Jc : ℕ) : ℝ)) * sineCoef (2 * Jc) m *
          sineEig (1 / 4) (2 * Jc) m ^ (4 * M - 1 - i) * z i) ^ 2 -
      1 / 2 * ∑ m ∈ Ico 1 Jc, (∑ i ∈ range (4 * M), 10 / (2 * ((2 * Jc : ℕ) : ℝ)) *
        sineCoef Jc m * sineEig (1 / 4) Jc m ^ (M - 1 - i / 4) * z i) ^ 2) ^ 2 ∂stdNormalSeq ≤
      24000000 / ((2 * Jc : ℕ) : ℝ) ^ 4 := by
  have h := parabolic_variance_of_coef (N := 4 * M) hJc
    (fun m i => 10 / (2 * ((2 * Jc : ℕ) : ℝ)) * sineCoef (2 * Jc) m *
      sineEig (1 / 4) (2 * Jc) m ^ (4 * M - 1 - i))
    (fun m i => 10 / (2 * ((2 * Jc : ℕ) : ℝ)) * sineCoef Jc m *
      sineEig (1 / 4) Jc m ^ (M - 1 - i / 4)) (K := 9600) (by norm_num)
    (fun m hm => parabolic_sum_sq_coef_le hm (4 * M))
    (fun m hm => parabolic_sum_sq_coarse_coef_le hm M)
    (fun m hm => parabolic_sum_sq_diff_coef_le hm M)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  norm_num

/-- `P_ℓ` as a function (Giles 2015, §7.1). -/
lemma parabolicP_fun_eq (ℓ : ℕ) : parabolicP ℓ = fun z => 1 / 2 * ∑ m ∈ Ico 1 (2 ^ (ℓ + 1)),
    (∑ i ∈ range (4 ^ (ℓ + 1)), 10 / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)) * sineCoef (2 ^ (ℓ + 1)) m *
      sineEig (1 / 4) (2 ^ (ℓ + 1)) m ^ (4 ^ (ℓ + 1) - 1 - i) * z i) ^ 2 :=
  funext (parabolicP_eq ℓ)

/-- `P_ℓ` is measurable. -/
lemma measurable_parabolicP (ℓ : ℕ) : Measurable (parabolicP ℓ) := by
  rw [parabolicP_fun_eq]
  exact (Finset.measurable_sum _ fun m _ => (measurable_linComb _ _).pow_const 2).const_mul _

/-- `P_ℓ` is square integrable (Giles 2015, §7.1). -/
lemma memLp_parabolicP (ℓ : ℕ) : MemLp (parabolicP ℓ) 2 stdNormalSeq := by
  rw [parabolicP_fun_eq]
  exact (memLp_finsetSum _ fun m _ => memLp_sq_linComb _ _).const_mul _

/-- **The exact mean of the level-`ℓ` output** (Giles 2015, §7.1, p. 51: "The output functional
is chosen to be `P = ∫₀¹ u²(x, 0.25)`. … The level `ℓ` approximation uses `h_ℓ = 2^{−(ℓ+1)}`,
`k_ℓ = ¼ h_ℓ²`"): with `J = 2^{ℓ+1}` and `N = 4^{ℓ+1}`,
`E[P_ℓ] = ½ ∑_{m=1}^{J−1} ∑_{i<N} (10/(2J) · c_m μ_m^{N−1−i})²`, the sum of the variances of the
mode amplitudes (each mode amplitude is a centred Gaussian). -/
theorem integral_parabolicP (ℓ : ℕ) :
    ∫ z, parabolicP ℓ z ∂stdNormalSeq = 1 / 2 * ∑ m ∈ Ico 1 (2 ^ (ℓ + 1)),
      ∑ i ∈ range (4 ^ (ℓ + 1)), (10 / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)) * sineCoef (2 ^ (ℓ + 1)) m *
        sineEig (1 / 4) (2 ^ (ℓ + 1)) m ^ (4 ^ (ℓ + 1) - 1 - i)) ^ 2 := by
  rw [parabolicP_fun_eq, integral_const_mul,
    integral_finsetSum _ fun m _ => (memLp_sq_linComb _ _).integrable one_le_two]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_sq_of_hasLaw_gaussianReal (hasLaw_linComb_stdNormalSeq _ _), coe_sum_toNNReal_sq]

/-- **The coupling of the paper** (Giles 2015, §5.1, p. 29: "The multilevel coupling is achieved by
using the same underlying driving Brownian path for the coarse and fine paths; this is
accomplished by summing the Brownian increments for the fine path timesteps to obtain the
Brownian increments for the coarse timesteps"; §7.1, p. 51, only says "The multilevel
implementation is again very easy", so the coupling of the SPDE example is implicit and taken
from §5.1 and (2.4)).  The coarse inputs `pairAvg (pairAvg z)` are again independent standard
normals, and for every level `ℓ` the coarse Brownian increment `z'_p/2^{ℓ+2}` of level `ℓ` is the
sum of the four fine increments `z_{4p+q}/2^{ℓ+3}` of level `ℓ + 1` (four fine steps per coarse
step, since `k_ℓ = 4 k_{ℓ+1}`). -/
theorem parabolic_coupling :
    MeasurePreserving (fun z => pairAvg (pairAvg z)) stdNormalSeq stdNormalSeq ∧
      ∀ (ℓ : ℕ) (z : ℕ → ℝ) (p : ℕ), pairAvg (pairAvg z) p / 2 ^ (ℓ + 2) =
        ∑ q ∈ range 4, z (4 * p + q) / 2 ^ (ℓ + 3) := by
  refine ⟨measurePreserving_pairAvg.comp measurePreserving_pairAvg, fun ℓ z p => ?_⟩
  rw [pairAvg_pairAvg_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
  rw [pow_succ]
  ring

/-- **The variance rate `β = 4`** (Giles 2015, §7.1, p. 51: "Because the stochastic forcing is
additive … the solution error is `O(2^{−2ℓ})` and hence `α = 2` and `β = 4`").  The correction
`P_{ℓ+1}(z) − P_ℓ(pairAvg (pairAvg z))` of the coupled fine and coarse paths is square integrable
and `E[(P_{ℓ+1} − P^c_ℓ)²] ≤ 1500000 · 16^{−(ℓ+1)}`.  Deviation: the paper derives `β = 4` from
the strong error against the SPDE, which is not proved here; the bound is proved directly by the
mode analysis (the constant is not optimised; numerically the left side times `16^{ℓ+1}` is about
`43`). -/
theorem parabolic_variance_rate (ℓ : ℕ) :
    MemLp (fun z => parabolicP (ℓ + 1) z - parabolicP ℓ (pairAvg (pairAvg z))) 2 stdNormalSeq ∧
      ∫ z, (parabolicP (ℓ + 1) z - parabolicP ℓ (pairAvg (pairAvg z))) ^ 2 ∂stdNormalSeq ≤
        1500000 / 16 ^ (ℓ + 1) := by
  simp only [parabolicP_succ_eq, parabolicP_pairAvg_eq]
  obtain ⟨h1, h2⟩ :=
    parabolic_level_variance_aux (Jc := 2 ^ (ℓ + 1)) Nat.one_le_two_pow (4 ^ (ℓ + 1))
  refine ⟨h1, h2.trans_eq ?_⟩
  have h16 : ((2 * 2 ^ (ℓ + 1) : ℕ) : ℝ) ^ 4 = 16 * 16 ^ (ℓ + 1) := by
    push_cast
    rw [mul_pow, ← pow_mul, mul_comm (ℓ + 1) 4, pow_mul]
    norm_num
  rw [h16]
  field_simp
  norm_num

/-! ### The limit of the level means -/

/-- `x sin(a/x) → a` as `x → ∞` (for `a > 0`). -/
lemma tendsto_mul_sin_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => x * Real.sin (a / x)) atTop (𝓝 a) := by
  have hlow : Tendsto (fun x : ℝ => a - a ^ 3 / 6 / x ^ 2) atTop (𝓝 a) := by
    have h := (tendsto_const_nhds (x := a ^ 3 / 6)).div_atTop
      (tendsto_pow_atTop (α := ℝ) two_ne_zero)
    simpa using (tendsto_const_nhds (x := a)).sub h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have h := Real.sin_gt_sub_cube (x := a / x) (by positivity)
    have e : x * (a / x - (a / x) ^ 3 / 6) = a - a ^ 3 / 6 / x ^ 2 := by
      field_simp
    rw [← e]
    exact (mul_lt_mul_of_pos_left h hx).le
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have h := Real.sin_le (x := a / x) (by positivity)
    calc x * Real.sin (a / x) ≤ x * (a / x) := mul_le_mul_of_nonneg_left h hx.le
      _ = a := by field_simp

/-- `cos(a/x) → 1` as `x → ∞`. -/
lemma tendsto_cos_div_atTop (a : ℝ) : Tendsto (fun x : ℝ => Real.cos (a / x)) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => a / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 := (Real.continuous_cos.tendsto 0).comp h
  rw [Real.cos_zero] at h2
  exact h2

/-- `cos(a/√n)^n → e^{−a²/2}` as `n → ∞`. -/
lemma tendsto_cos_div_sqrt_pow (a : ℝ) :
    Tendsto (fun n : ℕ => Real.cos (a / Real.sqrt n) ^ n) atTop (𝓝 (Real.exp (-(a ^ 2 / 2)))) := by
  have hg : Tendsto (fun n : ℕ => (n : ℝ) * (Real.cos (a / Real.sqrt n) - 1)) atTop
      (𝓝 (-(a ^ 2 / 2))) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (5 * a ^ 4 / 96))
    filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (⌈a ^ 2⌉₊)] with n hn hna
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hna' : a ^ 2 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hna)
    have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
    have hz : |a / Real.sqrt n| ≤ 1 := by
      rw [abs_div, abs_of_pos hs0, div_le_one hs0]
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hna'
    have hb := Real.cos_bound hz
    have hz2 : (a / Real.sqrt n) ^ 2 = a ^ 2 / n := by rw [div_pow, hs]
    have hz4 : |a / Real.sqrt n| ^ 4 = (a ^ 2 / n) ^ 2 := by
      rw [show |a / Real.sqrt n| ^ 4 = (|a / Real.sqrt n| ^ 2) ^ 2 by ring, sq_abs, hz2]
    have e : (n : ℝ) * (Real.cos (a / Real.sqrt n) - 1) - -(a ^ 2 / 2) =
        n * (Real.cos (a / Real.sqrt n) - (1 - (a / Real.sqrt n) ^ 2 / 2)) := by
      rw [hz2]
      field_simp
      ring
    rw [Real.norm_eq_abs, e, abs_mul, abs_of_pos hn']
    rw [hz4] at hb
    calc (n : ℝ) * |Real.cos (a / Real.sqrt n) - (1 - (a / Real.sqrt n) ^ 2 / 2)|
        ≤ n * ((a ^ 2 / n) ^ 2 * (5 / 96)) := mul_le_mul_of_nonneg_left hb hn'.le
      _ = 5 * a ^ 4 / 96 / n := by
          field_simp
  have h := Real.tendsto_one_add_pow_exp_of_tendsto hg
  refine h.congr fun n => ?_
  ring_nf

/-- The geometric sum `∑_{i<n} (κ μ^{n−1−i})² = κ² (1 − μ^{2n})/(1 − μ²)` for `μ² ≠ 1`. -/
lemma sum_sq_mul_pow_eq (κ μ : ℝ) (hμ : μ ^ 2 ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, (κ * μ ^ (n - 1 - i)) ^ 2 = κ ^ 2 * (1 - μ ^ (2 * n)) / (1 - μ ^ 2) := by
  have hr := Finset.sum_range_reflect (fun k => κ ^ 2 * (μ ^ 2) ^ k) n
  have e : ∑ i ∈ range n, (κ * μ ^ (n - 1 - i)) ^ 2 = κ ^ 2 * ∑ k ∈ range n, (μ ^ 2) ^ k := by
    rw [Finset.mul_sum, ← hr]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (n - 1 - i) 2]
  rw [e, geom_sum_eq hμ, ← pow_mul]
  have h1 : μ ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hμ
  have h2 : 1 - μ ^ 2 ≠ 0 := fun h => h1 (by linarith)
  field_simp
  ring

/-- The mean square of one mode in closed form (Giles 2015, §7.1): with `S = sin(πm/(2J))`,
`C = cos(πm/(2J))`, `½ ∑_{i<n} (10/(2J) · c_m μ_m^{n−1−i})² =
25 (1 − cos πm)² C² (1 − C^{4n}) / (2 (JS)⁴ (1 + C²))`. -/
lemma parabolic_mode_mean_eq {J m : ℕ} (hm : m ∈ Ico 1 J) (n : ℕ) :
    1 / 2 * ∑ i ∈ range n,
        (10 / (2 * (J : ℝ)) * sineCoef J m * sineEig (1 / 4) J m ^ (n - 1 - i)) ^ 2 =
      25 * (1 - Real.cos (π * m)) ^ 2 * Real.cos (π * m / (2 * J)) ^ 2 *
        (1 - Real.cos (π * m / (2 * J)) ^ (4 * n)) /
        (2 * ((J : ℝ) * Real.sin (π * m / (2 * J))) ^ 4 *
          (1 + Real.cos (π * m / (2 * J)) ^ 2)) := by
  obtain ⟨hS, hC, -, -⟩ := sineMode_angle_bounds hm
  have hm' := Finset.mem_Ico.1 hm
  have hJ : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hSC := Real.sin_sq_add_cos_sq (π * m / (2 * J))
  rw [sineEig_quarter, sineCoef_eq (by omega) (by omega)]
  generalize Real.sin (π * m / (2 * J)) = S at hS hSC ⊢
  generalize Real.cos (π * m / (2 * J)) = C at hC hSC ⊢
  have hC1 : (C ^ 2) ^ 2 ≠ 1 := by
    have : C ^ 2 < 1 := by nlinarith
    nlinarith
  rw [sum_sq_mul_pow_eq _ _ hC1, ← pow_mul, show 2 * (2 * n) = 4 * n by ring,
    show 1 - (C ^ 2) ^ 2 = S ^ 2 * (1 + C ^ 2) by nlinarith]
  field_simp
  ring

/-- The mean square of mode `m ≥ 1` converges as `ℓ → ∞` (Giles 2015, §7.1), with
`J = 2^{ℓ+1}`, `n = 4^{ℓ+1}`: to `100 (1 − cos πm)² (1 − e^{−π²m²/2})/(π⁴m⁴)`. -/
lemma parabolic_mode_mean_tendsto {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ℓ : ℕ => 25 * (1 - Real.cos (π * m)) ^ 2 *
        Real.cos (π * m / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ))) ^ 2 *
        (1 - Real.cos (π * m / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ))) ^ (4 * 4 ^ (ℓ + 1))) /
        (2 * (((2 ^ (ℓ + 1) : ℕ) : ℝ) * Real.sin (π * m / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)))) ^ 4 *
          (1 + Real.cos (π * m / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ))) ^ 2))) atTop
      (𝓝 (100 * (1 - Real.cos (π * m)) ^ 2 * (1 - Real.exp (-(π ^ 2 * m ^ 2 / 2))) /
        (π ^ 4 * m ^ 4))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set a : ℝ := π * m / 2 with ha
  have ha0 : 0 < a := by positivity
  have hx : ∀ ℓ : ℕ, π * m / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)) = a / ((2 ^ (ℓ + 1) : ℕ) : ℝ) :=
    fun ℓ => by rw [ha]; field_simp
  simp only [hx]
  have hJ : Tendsto (fun ℓ : ℕ => ((2 ^ (ℓ + 1) : ℕ) : ℝ)) atTop atTop := by
    push_cast
    exact (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (tendsto_add_atTop_nat 1)
  have hJS := (tendsto_mul_sin_div ha0).comp hJ
  have hC := (tendsto_cos_div_atTop a).comp hJ
  have hk : Tendsto (fun ℓ : ℕ => 4 * 4 ^ (ℓ + 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun ℓ => ?_) tendsto_id
    have := Nat.lt_pow_self (show 1 < 4 by norm_num) (n := ℓ + 1)
    simp only [id]
    omega
  have hCN := (tendsto_cos_div_sqrt_pow (2 * a)).comp hk
  have hsq : ∀ ℓ : ℕ, Real.sqrt ((4 * 4 ^ (ℓ + 1) : ℕ) : ℝ) = 2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ) := by
    intro ℓ
    rw [show ((4 * 4 ^ (ℓ + 1) : ℕ) : ℝ) = (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)) ^ 2 by
      push_cast
      rw [mul_pow, ← pow_mul, pow_mul']
      norm_num]
    exact Real.sqrt_sq (by positivity)
  have hCN' : Tendsto (fun ℓ : ℕ => Real.cos (a / ((2 ^ (ℓ + 1) : ℕ) : ℝ)) ^ (4 * 4 ^ (ℓ + 1)))
      atTop (𝓝 (Real.exp (-((2 * a) ^ 2 / 2)))) := by
    refine hCN.congr fun ℓ => ?_
    simp only [Function.comp_apply, hsq]
    congr 2
    field_simp
  have hnum := ((tendsto_const_nhds (x := 25 * (1 - Real.cos (π * m)) ^ 2)).mul (hC.pow 2)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hCN')
  have hden := ((tendsto_const_nhds (x := (2 : ℝ))).mul (hJS.pow 4)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add (hC.pow 2))
  have hlim := hnum.div hden (by positivity)
  have hval : 25 * (1 - Real.cos (π * m)) ^ 2 * 1 ^ 2 * (1 - Real.exp (-((2 * a) ^ 2 / 2))) /
      (2 * a ^ 4 * (1 + 1 ^ 2)) = 100 * (1 - Real.cos (π * m)) ^ 2 *
        (1 - Real.exp (-(π ^ 2 * m ^ 2 / 2))) / (π ^ 4 * m ^ 4) := by
    rw [ha, show (2 * (π * m / 2)) ^ 2 = π ^ 2 * m ^ 2 by ring]
    field_simp
    ring
  rw [← hval]
  exact hlim

/-- The terms of the limit series are nonnegative and at most `(400/π⁴) m⁻⁴`. -/
lemma parabolic_series_term_le (m : ℕ) :
    0 ≤ 100 * (1 - Real.cos (π * m)) ^ 2 * (1 - Real.exp (-(π ^ 2 * m ^ 2 / 2))) /
      (π ^ 4 * m ^ 4) ∧
    100 * (1 - Real.cos (π * m)) ^ 2 * (1 - Real.exp (-(π ^ 2 * m ^ 2 / 2))) /
      (π ^ 4 * m ^ 4) ≤ 400 / π ^ 4 * (1 / (m : ℝ) ^ 4) := by
  have he0 : 0 ≤ 1 - Real.exp (-(π ^ 2 * m ^ 2 / 2)) := by
    have : Real.exp (-(π ^ 2 * m ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ π ^ 2 * (m : ℝ) ^ 2 / 2 := by positivity
      linarith)
    linarith
  have he1 : 1 - Real.exp (-(π ^ 2 * m ^ 2 / 2)) ≤ 1 := by
    have := Real.exp_pos (-(π ^ 2 * m ^ 2 / 2))
    linarith
  have hc := one_sub_cos_sq_le_four (π * m)
  refine ⟨by positivity, ?_⟩
  calc 100 * (1 - Real.cos (π * m)) ^ 2 * (1 - Real.exp (-(π ^ 2 * m ^ 2 / 2))) /
        (π ^ 4 * m ^ 4) ≤ 100 * 4 * 1 / (π ^ 4 * m ^ 4) := by
        gcongr
    _ = 400 / π ^ 4 * (1 / (m : ℝ) ^ 4) := by
        rw [div_mul_div_comm]
        ring

/-- **The target value `P = lim E[P_ℓ]` of the parabolic example** (Giles 2015, §7.1, p. 51:
"`P = ∫₀¹ u²(x, 0.25)`"): the explicit series
`∑_{k≥0} 400 (1 − e^{−π²(2k+1)²/2}) / (π⁴ (2k+1)⁴)`, the limit of `E[P_ℓ]`
(`parabolic_mean_tendsto`).  For the SPDE `du = u_xx dt + 10 dW` with zero boundary and initial
data, the mild solution is `u = ∑_m a_m(t) sin(mπx)` with `a_m(t) = 10 ĉ_m ∫₀ᵗ e^{−m²π²(t−s)} dW_s`,
`ĉ_m = 2∫₀¹ sin(mπx) dx = 4/(mπ)` for odd `m` and `0` otherwise, and by the Itô isometry
`E ∫₀¹ u²(x, ¼) dx = ½ ∑_m E a_m(¼)² = ∑_{m odd} 400 (1 − e^{−π²m²/2})/(π⁴m⁴)`; this
identification needs stochastic integration and is not formalised. -/
noncomputable def parabolicLimit : ℝ :=
  ∑' k : ℕ, 400 * (1 - Real.exp (-(π ^ 2 * (2 * k + 1) ^ 2 / 2))) / (π ^ 4 * (2 * k + 1) ^ 4)

/-- **The level means converge to the explicit series `parabolicLimit`** (Giles 2015, §7.1, p. 51:
"`P = ∫₀¹ u²(x, 0.25)`"; the weak convergence of the scheme): `E[P_ℓ] → parabolicLimit =
∑_{m odd} 400 (1 − e^{−π²m²/2})/(π⁴m⁴)` as `ℓ → ∞`.  This series equals `E ∫₀¹ u²(x, ¼) dx` for
the SPDE by the Itô isometry (see `parabolicLimit`); that identification is not formalised, so
the statement is the convergence to the series only.  The proof takes the limit of each mode
(`parabolic_mode_mean_tendsto`: `J sin(πm/(2J)) → πm/2` and
`cos(πm/(2J))^{4J²} → e^{−π²m²/2}`) and dominates the modes by `50/m⁴` (Tannery's theorem). -/
theorem parabolic_mean_tendsto :
    Tendsto (fun ℓ => ∫ z, parabolicP ℓ z ∂stdNormalSeq) atTop (𝓝 parabolicLimit) := by
  set t : ℕ → ℝ := fun m => 100 * (1 - Real.cos (π * m)) ^ 2 *
    (1 - Real.exp (-(π ^ 2 * m ^ 2 / 2))) / (π ^ 4 * m ^ 4) with ht
  set f : ℕ → ℕ → ℝ := fun ℓ m => if m ∈ Ico 1 (2 ^ (ℓ + 1)) then 1 / 2 *
    ∑ i ∈ range (4 ^ (ℓ + 1)), (10 / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)) * sineCoef (2 ^ (ℓ + 1)) m *
      sineEig (1 / 4) (2 ^ (ℓ + 1)) m ^ (4 ^ (ℓ + 1) - 1 - i)) ^ 2 else 0 with hf
  have hint : ∀ ℓ, ∫ z, parabolicP ℓ z ∂stdNormalSeq = ∑ m ∈ range (2 ^ (ℓ + 1)), f ℓ m := by
    intro ℓ
    rw [integral_parabolicP, Finset.mul_sum, hf]
    simp only
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (fun m hm => by
      rw [Finset.mem_Ico] at hm
      exact Finset.mem_range.2 hm.2)]
  have hK : Tendsto (fun ℓ : ℕ => 2 ^ (ℓ + 1)) atTop atTop :=
    tendsto_atTop_mono (fun ℓ => (Nat.lt_two_pow_self (n := ℓ)).le.trans
      (Nat.pow_le_pow_right two_pos (Nat.le_succ ℓ))) tendsto_id
  have hb : Summable fun m : ℕ => 50 / (m : ℝ) ^ 4 := by
    have := (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 4)).mul_left 50
    exact this.congr fun m => mul_one_div _ _
  have hf0 : ∀ ℓ m, m < 2 ^ (ℓ + 1) → 0 ≤ f ℓ m := by
    intro ℓ m _
    rw [hf]
    simp only
    split_ifs
    · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    · exact le_rfl
  have hfb : ∀ ℓ m, m < 2 ^ (ℓ + 1) → f ℓ m ≤ 50 / (m : ℝ) ^ 4 := by
    intro ℓ m _
    rw [hf]
    simp only
    split_ifs with hm
    · have h1 := parabolic_sum_sq_coef_le hm (4 ^ (ℓ + 1))
      have e : (100 : ℝ) / (m : ℝ) ^ 4 = 2 * (50 / (m : ℝ) ^ 4) := by ring
      linarith
    · positivity
  have hfg : ∀ m, Tendsto (fun ℓ => f ℓ m) atTop (𝓝 (t m)) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h0 : t 0 = 0 := by simp [ht]
      rw [h0]
      refine tendsto_const_nhds.congr fun ℓ => ?_
      rw [hf]
      simp
    · refine (parabolic_mode_mean_tendsto hm).congr' ?_
      filter_upwards [eventually_ge_atTop m] with ℓ hℓ
      have hmJ : m ∈ Ico 1 (2 ^ (ℓ + 1)) := by
        rw [Finset.mem_Ico]
        refine ⟨hm, ?_⟩
        calc m < 2 ^ m := Nat.lt_two_pow_self
          _ ≤ 2 ^ (ℓ + 1) := Nat.pow_le_pow_right two_pos (by omega)
      rw [hf]
      simp only
      rw [if_pos hmJ, parabolic_mode_mean_eq hmJ]
  have hlim := tendsto_sum_range_of_dominated hK hb hf0 hfb hfg
  -- the even terms vanish
  have htsum : ∑' m, t m = ∑' k : ℕ, 400 * (1 - Real.exp (-(π ^ 2 * (2 * k + 1) ^ 2 / 2))) /
      (π ^ 4 * (2 * k + 1) ^ 4) := by
    have hts : Summable t := by
      have := (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 4)).mul_left (400 / π ^ 4)
      exact this.of_nonneg_of_le (fun m => (parabolic_series_term_le m).1)
        (fun m => (parabolic_series_term_le m).2)
    have he : Summable fun k => t (2 * k) :=
      hts.comp_injective (mul_right_injective₀ two_ne_zero)
    have ho : Summable fun k => t (2 * k + 1) :=
      hts.comp_injective fun a b h => by simpa using h
    rw [← tsum_even_add_odd he ho]
    have hev : ∀ k : ℕ, t (2 * k) = 0 := fun k => by
      rw [ht]
      simp only
      rw [show π * ((2 * k : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) * π by ring, Real.cos_nat_mul_pi,
        pow_mul]
      simp
    have hodd : ∀ k : ℕ, t (2 * k + 1) = 400 * (1 - Real.exp (-(π ^ 2 * (2 * k + 1) ^ 2 / 2))) /
        (π ^ 4 * (2 * k + 1) ^ 4) := fun k => by
      rw [ht]
      simp only
      rw [show π * ((2 * k + 1 : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) * π by ring,
        Real.cos_nat_mul_pi, pow_succ (-1 : ℝ) (2 * k), pow_mul (-1 : ℝ) 2 k]
      push_cast
      ring
    simp only [hev, hodd, tsum_zero, zero_add]
  rw [parabolicLimit, ← htsum]
  exact hlim.congr fun ℓ => (hint ℓ).symm

/-! ### The weak rate and Theorem 1 -/

/-- **The weak rate `α = 2`** (Giles 2015, §7.1, p. 51: "the solution error is `O(2^{−2ℓ})` and
hence `α = 2`").  Every `P_ℓ` is square integrable, consecutive level means satisfy
`|E[P_{ℓ+1}] − E[P_ℓ]| ≤ 1225 · 4^{−(ℓ+1)}`, and `|E[P_ℓ] − P| ≤ 409 · 4^{−ℓ}` for the limit
`P = parabolicLimit` of the level means.  Proof: by (2.4) (`parabolic_coupling`),
`E[P_{ℓ+1}] − E[P_ℓ]` is the mean of the coupled correction, which is at most the square root of
its second moment (`parabolic_variance_rate`, `√1500000 < 1225`); summing the geometric tail gives
the bias bound.  Deviation: the paper argues through the strong error against the SPDE. -/
theorem parabolic_weak_rate :
    (∀ ℓ, MemLp (parabolicP ℓ) 2 stdNormalSeq) ∧
    (∀ ℓ, |∫ z, parabolicP (ℓ + 1) z ∂stdNormalSeq - ∫ z, parabolicP ℓ z ∂stdNormalSeq| ≤
      1225 / 4 ^ (ℓ + 1)) ∧
    ∀ ℓ, |∫ z, parabolicP ℓ z ∂stdNormalSeq - parabolicLimit| ≤ 409 / 4 ^ ℓ := by
  have hpp := parabolic_coupling.1
  have hstep : ∀ ℓ, |∫ z, parabolicP (ℓ + 1) z ∂stdNormalSeq -
      ∫ z, parabolicP ℓ z ∂stdNormalSeq| ≤ 1225 / 4 ^ (ℓ + 1) := by
    intro ℓ
    obtain ⟨hD, hV⟩ := parabolic_variance_rate ℓ
    have h24 : ∫ z, parabolicP ℓ (pairAvg (pairAvg z)) ∂stdNormalSeq =
        ∫ z, parabolicP ℓ z ∂stdNormalSeq :=
      integral_comp_of_measurePreserving hpp (measurable_parabolicP ℓ).aestronglyMeasurable
    have hmean : ∫ z, (parabolicP (ℓ + 1) z - parabolicP ℓ (pairAvg (pairAvg z))) ∂stdNormalSeq =
        ∫ z, parabolicP (ℓ + 1) z ∂stdNormalSeq - ∫ z, parabolicP ℓ z ∂stdNormalSeq := by
      have hc : Integrable (fun z => parabolicP ℓ (pairAvg (pairAvg z))) stdNormalSeq :=
        ((memLp_parabolicP ℓ).comp_measurePreserving hpp).integrable one_le_two
      rw [integral_sub ((memLp_parabolicP (ℓ + 1)).integrable one_le_two) hc, h24]
    rw [← hmean]
    refine abs_le_of_sq_le_sq ((sq_integral_le_integral_sq_of_memLp hD).trans
      (hV.trans ?_)) (by positivity)
    rw [div_pow, ← pow_mul, show (4 : ℝ) ^ ((ℓ + 1) * 2) = 16 ^ (ℓ + 1) by
      rw [pow_mul']; norm_num]
    gcongr
    norm_num
  have hu : ∀ n : ℕ, dist (∫ z, parabolicP n z ∂stdNormalSeq)
      (∫ z, parabolicP (n + 1) z ∂stdNormalSeq) ≤ 1225 / 4 * (1 / 4) ^ n := fun n => by
    rw [Real.dist_eq, abs_sub_comm]
    refine (hstep n).trans_eq ?_
    rw [one_div_pow, pow_succ]
    field_simp
  refine ⟨memLp_parabolicP, hstep, fun ℓ => ?_⟩
  have h := dist_le_of_le_geometric_of_tendsto (1 / 4 : ℝ) (1225 / 4) (by norm_num) hu
    parabolic_mean_tendsto ℓ
  rw [Real.dist_eq] at h
  refine h.trans ?_
  rw [one_div_pow, div_le_div_iff₀ (by norm_num) (by positivity)]
  have h4 : (0 : ℝ) < 4 ^ ℓ := by positivity
  field_simp
  nlinarith

/-- **Theorem 1 for the parabolic SPDE example, end to end: MSE `< ε²` at cost `O(ε⁻²)`**
(Giles 2015, §7.1, p. 51: "Since the number of grid points doubles on each level, and the number of
timesteps increases by factor 4, the cost per sample increases by factor 8, giving `γ = 3`. … the
solution error is `O(2^{−2ℓ})` and hence `α = 2` and `β = 4`.  This leads to the optimal
complexity of `O(ε^{−2})`").  The level means converge to `P = parabolicLimit`, and there is
`c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the multilevel
estimator `∑_{ℓ≤L} N_ℓ⁻¹ ∑_{n<N_ℓ} (P_ℓ − P^c_{ℓ−1})(z^{(ℓ,n)})` (fine minus coupled coarse
sample, `fineCoarseDiff`, with independent inputs `z^{(ℓ,n)}`, the coordinates of
`stdNormalSeq^{⊗(ℕ×ℕ)}`) has a square-integrable error with mean square `< ε²`, at cost
`∑_{ℓ≤L} N_ℓ 2^{ℓ+1} 4^{ℓ+1} ≤ c₄ ε⁻²` (grid intervals times time steps of the fine path).  No
rate is assumed: `α = 2` (`parabolic_weak_rate`), `β = 4` (`parabolic_variance_rate`), (2.4)
(`parabolic_coupling`) and `γ = 3` are proved, and Theorem 1 is `giles_theorem1_fineCoarse`.
Deviations: `P` is the limit of the level means rather than the SPDE output itself (see
`parabolicLimit`); the cost counts the fine path only (the coarse path adds `1/8`). -/
theorem parabolic_mlmc_theorem1 :
    Tendsto (fun ℓ => ∫ z, parabolicP ℓ z ∂stdNormalSeq) atTop (𝓝 parabolicLimit) ∧
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff parabolicP (fun ℓ z => parabolicP ℓ (pairAvg (pairAvg z))))
              (fun p x => x p) ℓ (N ℓ) x - parabolicLimit) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff parabolicP (fun ℓ z => parabolicP ℓ (pairAvg (pairAvg z))))
              (fun p x => x p) ℓ (N ℓ) x - parabolicLimit) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (2 ^ (ℓ + 1) * 4 ^ (ℓ + 1)) ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨hPf, -, hbias⟩ := parabolic_weak_rate
  have hpp := parabolic_coupling.1
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hPcm : ∀ ℓ, Measurable (fun z => parabolicP ℓ (pairAvg (pairAvg z))) := fun ℓ =>
    (measurable_parabolicP ℓ).comp hpp.measurable
  have hPc : ∀ ℓ, MemLp (fun z => parabolicP ℓ (pairAvg (pairAvg z))) 2 stdNormalSeq :=
    fun ℓ => (hPf ℓ).comp_measurePreserving hpp
  have h24 : ∀ ℓ, ∫ z, parabolicP ℓ z ∂stdNormalSeq =
      ∫ z, parabolicP ℓ (pairAvg (pairAvg z)) ∂stdNormalSeq := fun ℓ =>
    (integral_comp_of_measurePreserving hpp (measurable_parabolicP ℓ).aestronglyMeasurable).symm
  -- (i): the weak rate `α = 2`
  have h_i : ∀ ℓ : ℕ, |∫ y, parabolicP ℓ y - parabolicLimit ∂stdNormalSeq| ≤
      409 * (2 : ℝ) ^ (-(2 * (ℓ : ℝ))) := by
    intro ℓ
    rw [integral_sub ((hPf ℓ).integrable one_le_two) (integrable_const _), integral_const,
      probReal_univ, one_smul, two_rpow_neg_two_mul, ← div_eq_mul_inv]
    exact hbias ℓ
  -- (iii): the variance rate `β = 4`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (parabolicP 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := hV₀ ▸ variance_nonneg _ _
  have h_iii : ∀ ℓ, variance (fineCoarseDiff parabolicP
      (fun ℓ z => parabolicP ℓ (pairAvg (pairAvg z))) ℓ) stdNormalSeq ≤
      (V₀ + 1500000) * (2 : ℝ) ^ (-(4 * (ℓ : ℝ))) := by
    intro ℓ
    have e4 : (2 : ℝ) ^ (-(4 * (ℓ : ℝ))) = ((16 : ℝ) ^ ℓ)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_natCast,
        Real.rpow_ofNat]
      norm_num
    rw [e4]
    cases ℓ with
    | zero =>
      rw [fineCoarseDiff, ← hV₀, pow_zero, inv_one, mul_one]
      linarith
    | succ ℓ =>
      obtain ⟨hD, hV⟩ := parabolic_variance_rate ℓ
      have hp : 0 ≤ ((16 : ℝ) ^ (ℓ + 1))⁻¹ := by positivity
      calc variance (fineCoarseDiff parabolicP
            (fun ℓ z => parabolicP ℓ (pairAvg (pairAvg z))) (ℓ + 1)) stdNormalSeq
          = variance (fun z => parabolicP (ℓ + 1) z - parabolicP ℓ (pairAvg (pairAvg z)))
              stdNormalSeq := by rw [fineCoarseDiff]
        _ ≤ ∫ z, (parabolicP (ℓ + 1) z - parabolicP ℓ (pairAvg (pairAvg z))) ^ 2
              ∂stdNormalSeq := variance_le_expectation_sq hD.aestronglyMeasurable
        _ ≤ 1500000 / 16 ^ (ℓ + 1) := hV
        _ ≤ (V₀ + 1500000) * ((16 : ℝ) ^ (ℓ + 1))⁻¹ := by
          rw [div_eq_mul_inv]
          nlinarith
  -- (iv): a level-`ℓ` sample costs `2^{ℓ+1} 4^{ℓ+1} = 8^{ℓ+1}` (`γ = 3`)
  have h_iv : ∀ ℓ : ℕ, (2 : ℝ) ^ (ℓ + 1) * 4 ^ (ℓ + 1) ≤ 8 * (2 : ℝ) ^ ((3 : ℝ) * (ℓ : ℝ)) := by
    intro ℓ
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast, Real.rpow_ofNat, ← mul_pow]
    norm_num
    rw [pow_succ]
    linarith
  have hαβγ : min (4 : ℝ) 3 / 2 ≤ 2 := by
    rw [min_eq_right (by norm_num : (3 : ℝ) ≤ 4)]
    norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) (fun _ => parabolicLimit) parabolicP
    (fun ℓ z => parabolicP ℓ (pairAvg (pairAvg z))) (fun p x => x p)
    (fun ℓ _ _ => (2 : ℝ) ^ (ℓ + 1) * 4 ^ (ℓ + 1)) (fun ℓ => (2 : ℝ) ^ (ℓ + 1) * 4 ^ (ℓ + 1))
    (α := 2) (β := 4) (γ := 3) two_pos (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 409)
    (by positivity : 0 < V₀ + 1500000) (by norm_num : (0 : ℝ) < 8) hαβγ hω hind
    (integrable_const _) measurable_parabolicP hPcm hPf hPc h24 (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i h_iii h_iv
  refine ⟨parabolic_mean_tendsto, c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  have hP : ∫ _y, parabolicLimit ∂stdNormalSeq = parabolicLimit := by
    rw [integral_const, probReal_univ, one_smul]
  rw [hP] at hmse
  have hY : MemLp (fun x => ∑ ℓ ∈ range (L + 1),
      blockMean (fineCoarseDiff parabolicP (fun ℓ z => parabolicP ℓ (pairAvg (pairAvg z))))
        (fun p x => x p) ℓ (N ℓ) x) 2 (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) :=
    memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω (memLp_fineCoarseDiff hPf hPc) ℓ (N ℓ)
  refine ⟨L, N, hN, (hY.sub (memLp_const parabolicLimit)).integrable_sq, hmse, ?_⟩
  simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul] at hcost
  rw [complexityBound_of_lt (by norm_num : (3 : ℝ) < 4) ε] at hcost
  exact hcost

end MLMC
