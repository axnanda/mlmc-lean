import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith

/-!
# The multilevel Monte Carlo estimator: mean, variance and mean-square error

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §1.3 and §2.1,
eq. (2.1)–(2.3).

Giles writes the telescoping identity `E[P_L] = E[P_0] + ∑_{ℓ=1}^{L} E[P_ℓ − P_{ℓ−1}]` (§1.3, p. 4),
estimates each term by an independent estimator `Y_ℓ`, and states for `Y = ∑_{ℓ=0}^{L} Y_ℓ`

  `MSE ≡ E[(Y − E[P])²] = V[Y] + (E[Y] − E[P])²`   (2.1)
  `E[Y] = E[P_L]`,  `V[Y] = ∑_{ℓ} N_ℓ⁻¹ V_ℓ`         (2.3)

(the second equality of (2.3) combines `V[Y] = ∑_ℓ V[Y_ℓ]` with `V[Y_ℓ] = N_ℓ⁻¹ V_ℓ`, see
`variance_sample_mean` in `MlmcLean/Theorem1.lean`).  These are the probabilistic facts used in the
proof of his Theorem 1; everything else in that proof is real analysis
(see `MlmcLean/Complexity.lean`).

We formalise them on an arbitrary probability space `(Ω, μ)` with Mathlib's
`ProbabilityTheory.variance` and `ProbabilityTheory.IndepFun` (pairwise independence, weaker than
the paper's independence).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Mean-square-error decomposition** (Giles 2015, eq. (2.1)):
`E[(Y − m)²] = Var[Y] + (E[Y] − m)²` for any square-integrable `Y` and any real target `m`
(Giles: `m = E[P]`). -/
theorem mse_eq_variance_add_sq_bias {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (m : ℝ) :
    μ[fun ω => (Y ω - m) ^ 2] = variance Y μ + (μ[Y] - m) ^ 2 := by
  have h1 : MemLp (fun ω => Y ω - m) 2 μ := hY.sub (memLp_const m)
  have h2 := variance_eq_sub h1
  have h3 : variance (fun ω => Y ω - m) μ = variance Y μ :=
    variance_sub_const hY.aestronglyMeasurable m
  have h4 : μ[fun ω => Y ω - m] = μ[Y] - m := by
    rw [integral_sub (hY.integrable one_le_two) (integrable_const m), integral_const]
    simp
  rw [h3, h4] at h2
  have h5 : μ[(fun ω => Y ω - m) ^ 2] = μ[fun ω => (Y ω - m) ^ 2] := rfl
  rw [h5] at h2
  linarith

/-- Giles (2.3), the **mean** of the multilevel estimator.  Condition (ii) of Theorem 1 is
`E[Y_0] = E[P_0]` and `E[Y_ℓ] = E[P_ℓ − P_{ℓ−1}]` for `ℓ > 0`; the telescoping sum
`E[P_L] = E[P_0] + ∑_{ℓ=1}^{L} E[P_ℓ − P_{ℓ−1}]` (§1.3, p. 4) then gives
`E[∑_{ℓ=0}^{L} Y_ℓ] = E[P_L]`.  Here `Pℓ ℓ` are the level approximations. -/
theorem mlmc_mean (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ) (L : ℕ)
    (hY : ∀ ℓ, Integrable (Y ℓ) μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (h_ii₀ : μ[Y 0] = μ[Pℓ 0])
    (h_ii : ∀ ℓ, μ[Y (ℓ + 1)] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω]) :
    μ[∑ ℓ ∈ range (L + 1), Y ℓ] = μ[Pℓ L] := by
  have hsum : μ[∑ ℓ ∈ range (L + 1), Y ℓ] = ∑ ℓ ∈ range (L + 1), μ[Y ℓ] := by
    rw [← integral_finsetSum _ (fun ℓ _ => hY ℓ)]
    congr 1
    ext ω
    simp [Finset.sum_apply]
  rw [hsum, Finset.sum_range_succ', h_ii₀]
  have htel : ∀ ℓ ∈ range L, μ[Y (ℓ + 1)] = μ[Pℓ (ℓ + 1)] - μ[Pℓ ℓ] := fun ℓ _ => by
    rw [h_ii ℓ, integral_sub (hPℓ _) (hPℓ _)]
  have htele : ∀ n : ℕ, ∑ ℓ ∈ range n, (μ[Pℓ (ℓ + 1)] - μ[Pℓ ℓ]) = μ[Pℓ n] - μ[Pℓ 0] := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [Finset.sum_congr rfl htel, htele L]
  ring

/-- The first step of Giles (2.3), the **variance** of the multilevel estimator: for pairwise
independent square-integrable level estimators, `V[∑ Y_ℓ] = ∑ V[Y_ℓ]` (with `V[Y_ℓ] = N_ℓ⁻¹V_ℓ`
this is (2.3), see `variance_sample_mean`). -/
theorem mlmc_variance (Y : ℕ → Ω → ℝ) (L : ℕ) (hY : ∀ ℓ, MemLp (Y ℓ) 2 μ)
    (hind : Set.Pairwise ↑(range (L + 1)) fun i j => IndepFun (Y i) (Y j) μ) :
    variance (∑ ℓ ∈ range (L + 1), Y ℓ) μ = ∑ ℓ ∈ range (L + 1), variance (Y ℓ) μ :=
  IndepFun.variance_sum (fun ℓ _ => hY ℓ) hind

/-- **MSE of the multilevel estimator** (Giles 2015, (2.1) combined with (2.3)):
`E[(∑ Y_ℓ − m)²] = ∑ V[Y_ℓ] + (E[P_L] − m)²`, for any target `m` (Giles: `m = E[P]`), where
`Pℓ ℓ` are the level approximations. -/
theorem mlmc_mse (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ) (L : ℕ) (m : ℝ)
    (hY : ∀ ℓ, MemLp (Y ℓ) 2 μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hind : Set.Pairwise ↑(range (L + 1)) fun i j => IndepFun (Y i) (Y j) μ)
    (h_ii₀ : μ[Y 0] = μ[Pℓ 0])
    (h_ii : ∀ ℓ, μ[Y (ℓ + 1)] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω]) :
    μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ ω - m) ^ 2] =
      ∑ ℓ ∈ range (L + 1), variance (Y ℓ) μ + (μ[Pℓ L] - m) ^ 2 := by
  have hsum : MemLp (∑ ℓ ∈ range (L + 1), Y ℓ) 2 μ :=
    memLp_finsetSum' _ (fun ℓ _ => hY ℓ)
  have h := mse_eq_variance_add_sq_bias hsum m
  rw [mlmc_variance Y L hY hind,
    mlmc_mean Pℓ Y L (fun ℓ => (hY ℓ).integrable one_le_two) hPℓ h_ii₀ h_ii] at h
  have hfun : (fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ ω - m) ^ 2) =
      fun ω => ((∑ ℓ ∈ range (L + 1), Y ℓ) ω - m) ^ 2 := by
    ext ω
    simp [Finset.sum_apply]
  rw [hfun]
  exact h

end MLMC
