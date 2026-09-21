import Mathlib
import MlmcLean.Estimator
import MlmcLean.Complexity

/-!
# Giles' Theorem 1 on a probability space

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), Theorem 1.

This file states Theorem 1 as Giles states it — for random variables on a probability space
`(Ω, μ)` — and proves it from

* `MlmcLean.Estimator`: `MSE = ∑ V[Y_ℓ] + (E[P_L] − E[P])²` (Giles (2.3)),
* `MlmcLean.Complexity`: the deterministic choice of `L`, `N_ℓ` and the three cost regimes.

**Data.**
* `P : Ω → ℝ` — the quantity of interest, `Pℓ ℓ` — its level-`ℓ` approximation;
* `Y ℓ n : Ω → ℝ` — the level-`ℓ` estimator "based on `n` Monte Carlo samples";
* `V ℓ` — the per-sample variance at level `ℓ` (`V[Y_ℓ] = V_ℓ / N_ℓ`, Giles (2.3));
* `C ℓ` — the expected cost per sample at level `ℓ` (total cost `∑ N_ℓ C_ℓ`).

**Hypotheses (i)–(iv)** are stated verbatim from the paper.  Independence of the estimators
across levels is assumed for every choice of sample sizes, since the theorem *chooses* `N_ℓ`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Giles (2.2)/(2.3): the variance of a Monte Carlo average of `N` pairwise independent samples
of common variance `v` is `v / N`.  This is how `V[Y_ℓ] = V_ℓ / N_ℓ` arises. -/
theorem variance_sample_mean (X : ℕ → Ω → ℝ) (N : ℕ) (hN : 0 < N) (v : ℝ)
    (hX : ∀ n, MemLp (X n) 2 μ) (hvar : ∀ n, variance (X n) μ = v)
    (hind : Set.Pairwise ↑(range N) fun i j => IndepFun (X i) (X j) μ) :
    variance (fun ω => (N : ℝ)⁻¹ * ∑ n ∈ range N, X n ω) μ = v / N := by
  have h1 : (fun ω => (N : ℝ)⁻¹ * ∑ n ∈ range N, X n ω) =
      fun ω => (N : ℝ)⁻¹ * (∑ n ∈ range N, X n) ω := by
    ext ω
    simp [Finset.sum_apply]
  rw [h1, variance_const_mul, IndepFun.variance_sum (fun n _ => hX n) hind]
  simp only [hvar, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  field_simp

/-- **Giles' Theorem 1.**
Let `P` be a random variable and `Pℓ ℓ` its level-`ℓ` approximation.  If there exist independent
estimators `Y ℓ N` based on `N` Monte Carlo samples, each with expected cost `C ℓ` and variance
`V ℓ` (per sample), and positive constants `α, β, γ, c₁, c₂, c₃` with `α ≥ ½ min(β,γ)` and

  (i)   `|E[Pℓ ℓ − P]| ≤ c₁ 2^{−αℓ}`,
  (ii)  `E[Y 0 N] = E[Pℓ 0]`, `E[Y (ℓ+1) N] = E[Pℓ (ℓ+1) − Pℓ ℓ]`,
  (iii) `V ℓ ≤ c₂ 2^{−βℓ}`,
  (iv)  `C ℓ ≤ c₃ 2^{γℓ}`,

then there is `c₄ > 0` such that for every `ε < e⁻¹` there are `L` and `N ℓ ≥ 1` for which the
multilevel estimator `∑_{ℓ=0}^{L} Y ℓ (N ℓ)` has `MSE = E[(Y − E[P])²] < ε²` and total cost
`∑ N ℓ · C ℓ ≤ c₄ ε⁻²` if `β > γ`, `c₄ ε⁻² (log ε)²` if `β = γ`, `c₄ ε^{−2−(γ−β)/α}` if `β < γ`. -/
theorem giles_theorem1
    (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (V C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (h_i : ∀ ℓ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ c₄ * complexityBound α β γ ε := by
  obtain ⟨c₄, hc₄, hcore⟩ :=
    mlmc_complexity_core (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) hα hβ hγ hc₁ hc₂ hc₃ hαβγ
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := hcore ε hε hε1
  refine ⟨L, N, hN, ?_, ?_⟩
  · -- mean-square error
    have hind' : Set.Pairwise ↑(range (L + 1)) fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ :=
      fun i _ j _ hij => hind N hij
    rw [mlmc_mse Pℓ (fun ℓ => Y ℓ (N ℓ)) L (μ[P]) (fun ℓ => hY ℓ (N ℓ)) hPℓ hind'
      (h_ii₀ (N 0)) (fun ℓ => h_ii ℓ (N (ℓ + 1)))]
    have hb : (μ[Pℓ L] - μ[P]) ^ 2 ≤ (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 := by
      have h := h_i L
      rw [integral_sub (hPℓ L) hP] at h
      exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
    have hv : ∑ ℓ ∈ range (L + 1), variance (Y ℓ (N ℓ)) μ ≤
        ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) := by
      apply Finset.sum_le_sum
      intro ℓ _
      rw [h_var ℓ (N ℓ) (hN ℓ)]
      exact div_le_div_of_nonneg_right (h_iii ℓ) (by positivity)
    linarith
  · -- cost
    calc ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ
        ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ := by
          apply Finset.sum_le_sum
          intro ℓ _
          exact mul_le_mul_of_nonneg_left (h_iv ℓ) (by positivity)
      _ ≤ c₄ * complexityBound α β γ ε := hcost

end MLMC
