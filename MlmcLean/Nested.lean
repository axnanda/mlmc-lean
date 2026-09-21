import Mathlib
import MlmcLean.Allocation
import MlmcLean.Estimator

/-!
# Nested multilevel Monte Carlo (Haas–Giles 2025)

Reference: I.-B. Haas, M.B. Giles, *A nested MLMC framework for efficient simulations on FPGAs*,
arXiv:2502.07123 (2025), §2.2, eq. (9)–(12).

Each level-`ℓ` term `E[ΔP_ℓ]` is split into a low-precision estimate and a correction,

  `E[P_L] = ∑_{ℓ=0}^{L} E[Δ̃P_ℓ] + E[ΔP_ℓ − Δ̃P_ℓ]`      (9)

estimated with `Ñ_ℓ` resp. `N^Δ_ℓ` samples of per-sample variance `Ṽ_ℓ`, `V^Δ_ℓ` and cost
`C̃_ℓ`, `C^Δ_ℓ`.  Then

  `Cost = ∑ Ñ_ℓ C̃_ℓ + N^Δ_ℓ C^Δ_ℓ`   (10),   `Variance = ∑ Ṽ_ℓ/Ñ_ℓ + V^Δ_ℓ/N^Δ_ℓ`   (11),

and, optimising with a Lagrange multiplier under `Variance = ε²`,

  `Cost_nested = ε⁻² (∑_{ℓ=0}^{L} √(Ṽ_ℓ C̃_ℓ) + √(V^Δ_ℓ C^Δ_ℓ))²`.      (12)

We prove (12) rigorously as a two-sided statement, by applying the optimal-allocation theorem of
`MlmcLean/Allocation.lean` to the index set `levels × {low precision, correction}`:

* `nested_cost_lower_bound`: every allocation meeting (11) `≤ ε²` costs at least (12);
* `nested_optimal_allocation`: integer sample numbers exist meeting (11) `≤ ε²` with cost at most
  (12) plus the rounding overhead `∑ (C̃_ℓ + C^Δ_ℓ)`;

and the probabilistic content of (9)–(11), `nested_mlmc_mse`: for independent unbiased component
estimators the MSE of the nested estimator is `∑ (V[Ỹ_ℓ] + V[Y^Δ_ℓ]) + (E[P_L] − E[P])²`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### The index set `levels × {low precision, correction}` -/

/-- `nIdx L = {0,…,L} × Bool`; `true` = low-precision term `Δ̃P_ℓ`, `false` = correction
`ΔP_ℓ − Δ̃P_ℓ`. -/
def nIdx (L : ℕ) : Finset (ℕ × Bool) := range (L + 1) ×ˢ Finset.univ

/-- Combine two level-indexed families into one family on `ℕ × Bool`. -/
def pairFam {X : Type*} (f g : ℕ → X) : ℕ × Bool → X := fun p => if p.2 then f p.1 else g p.1

@[simp] lemma pairFam_true {X : Type*} (f g : ℕ → X) (ℓ : ℕ) : pairFam f g (ℓ, true) = f ℓ := rfl
@[simp] lemma pairFam_false {X : Type*} (f g : ℕ → X) (ℓ : ℕ) : pairFam f g (ℓ, false) = g ℓ := rfl

lemma sum_nIdx {M : Type*} [AddCommMonoid M] (L : ℕ) (h : ℕ × Bool → M) :
    ∑ p ∈ nIdx L, h p = ∑ ℓ ∈ range (L + 1), (h (ℓ, true) + h (ℓ, false)) := by
  unfold nIdx
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Fintype.sum_bool]

lemma nIdx_nonempty (L : ℕ) : (nIdx L).Nonempty :=
  ⟨(0, true), by simp [nIdx]⟩

lemma pairFam_pos {f g : ℕ → ℝ} (hf : ∀ ℓ, 0 < f ℓ) (hg : ∀ ℓ, 0 < g ℓ) (p : ℕ × Bool) :
    0 < pairFam f g p := by
  rcases p with ⟨ℓ, b⟩
  cases b <;> simp [hf, hg]

/-! ### Haas–Giles (12) as a lower bound and as an achievable cost -/

section deterministic

variable (L : ℕ) (Vt Ct VΔ CΔ : ℕ → ℝ)

/-- Haas–Giles (12), **lower bound**: any real allocation `ñ_ℓ, n^Δ_ℓ > 0` with nested variance
(11) at most `ε²` has nested cost (10) at least `ε⁻² (∑ √(Ṽ_ℓ C̃_ℓ) + √(V^Δ_ℓ C^Δ_ℓ))²`. -/
theorem nested_cost_lower_bound (nt nΔ : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hVt : ∀ ℓ, 0 ≤ Vt ℓ) (hVΔ : ∀ ℓ, 0 ≤ VΔ ℓ) (hCt : ∀ ℓ, 0 ≤ Ct ℓ) (hCΔ : ∀ ℓ, 0 ≤ CΔ ℓ)
    (hnt : ∀ ℓ, 0 < nt ℓ) (hnΔ : ∀ ℓ, 0 < nΔ ℓ)
    (hvar : ∑ ℓ ∈ range (L + 1), (Vt ℓ / nt ℓ + VΔ ℓ / nΔ ℓ) ≤ ε ^ 2) :
    (ε ^ 2)⁻¹ *
        (∑ ℓ ∈ range (L + 1), (Real.sqrt (Vt ℓ * Ct ℓ) + Real.sqrt (VΔ ℓ * CΔ ℓ))) ^ 2 ≤
      ∑ ℓ ∈ range (L + 1), (nt ℓ * Ct ℓ + nΔ ℓ * CΔ ℓ) := by
  have h := cost_lower_bound (nIdx L) (pairFam Vt VΔ) (pairFam Ct CΔ) (pairFam nt nΔ)
    (by positivity : 0 < ε ^ 2)
    (fun p _ => by rcases p with ⟨ℓ, b⟩; cases b <;> simp [hVt, hVΔ])
    (fun p _ => by rcases p with ⟨ℓ, b⟩; cases b <;> simp [hCt, hCΔ])
    (fun p _ => pairFam_pos hnt hnΔ p)
    (by rw [sum_nIdx]; simpa using hvar)
  rw [sum_nIdx, sum_nIdx] at h
  simpa using h

/-- Haas–Giles (12), **achievability**: there are integer sample numbers `Ñ_ℓ, N^Δ_ℓ ≥ 1` with
nested variance (11) at most `ε²` and nested cost (10) at most
`ε⁻² (∑ √(Ṽ_ℓ C̃_ℓ) + √(V^Δ_ℓ C^Δ_ℓ))² + ∑ (C̃_ℓ + C^Δ_ℓ)`
(the second term being the cost of rounding the optimal real sample numbers up to integers). -/
theorem nested_optimal_allocation {ε : ℝ} (hε : 0 < ε)
    (hVt : ∀ ℓ, 0 < Vt ℓ) (hVΔ : ∀ ℓ, 0 < VΔ ℓ) (hCt : ∀ ℓ, 0 < Ct ℓ) (hCΔ : ∀ ℓ, 0 < CΔ ℓ) :
    ∃ Nt NΔ : ℕ → ℕ, (∀ ℓ, 0 < Nt ℓ) ∧ (∀ ℓ, 0 < NΔ ℓ) ∧
      ∑ ℓ ∈ range (L + 1), (Vt ℓ / (Nt ℓ : ℝ) + VΔ ℓ / (NΔ ℓ : ℝ)) ≤ ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), ((Nt ℓ : ℝ) * Ct ℓ + (NΔ ℓ : ℝ) * CΔ ℓ) ≤
        (ε ^ 2)⁻¹ *
            (∑ ℓ ∈ range (L + 1), (Real.sqrt (Vt ℓ * Ct ℓ) + Real.sqrt (VΔ ℓ * CΔ ℓ))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), (Ct ℓ + CΔ ℓ) := by
  have hs := nIdx_nonempty L
  have hV := pairFam_pos hVt hVΔ
  have hC := pairFam_pos hCt hCΔ
  have hτ : 0 < ε ^ 2 := by positivity
  refine ⟨fun ℓ => optimalN (nIdx L) (pairFam Vt VΔ) (pairFam Ct CΔ) (ε ^ 2) (ℓ, true),
    fun ℓ => optimalN (nIdx L) (pairFam Vt VΔ) (pairFam Ct CΔ) (ε ^ 2) (ℓ, false),
    fun ℓ => optimalN_pos hs hV hC hτ _, fun ℓ => optimalN_pos hs hV hC hτ _, ?_, ?_⟩
  · have h := optimalN_variance hs hV hC hτ
    rw [sum_nIdx] at h
    simpa using h
  · have h := optimalN_cost hs hV hC hτ
    unfold S at h
    rw [sum_nIdx, sum_nIdx, sum_nIdx] at h
    simpa using h

end deterministic

/-! ### The nested estimator on a probability space: (9)–(11) -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Haas–Giles (9)–(11).  Let `P ℓ` be the level-`ℓ` approximation and `Dt ℓ` the low-precision
level difference `Δ̃P_ℓ`.  Let `Yt ℓ` estimate `E[Δ̃P_ℓ]` and `YΔ ℓ` estimate
`E[ΔP_ℓ − Δ̃P_ℓ]` (with `ΔP_0 = P_0`, `ΔP_ℓ = P_ℓ − P_{ℓ−1}`), all `2(L+1)` estimators pairwise
independent.  Then the nested estimator `∑_ℓ (Yt ℓ + YΔ ℓ)` has mean `E[P_L]` (9), variance
`∑_ℓ (V[Yt ℓ] + V[YΔ ℓ])` (11), and hence
`MSE = ∑_ℓ (V[Yt ℓ] + V[YΔ ℓ]) + (E[P_L] − m)²`. -/
theorem nested_mlmc_mse (P Dt : ℕ → Ω → ℝ) (Yt YΔ : ℕ → Ω → ℝ) (L : ℕ) (m : ℝ)
    (hYt : ∀ ℓ, MemLp (Yt ℓ) 2 μ) (hYΔ : ∀ ℓ, MemLp (YΔ ℓ) 2 μ)
    (hP : ∀ ℓ, Integrable (P ℓ) μ) (hDt : ∀ ℓ, Integrable (Dt ℓ) μ)
    (hind : Set.Pairwise ↑(nIdx L) fun i j => IndepFun (pairFam Yt YΔ i) (pairFam Yt YΔ j) μ)
    (ht : ∀ ℓ, μ[Yt ℓ] = μ[Dt ℓ])
    (hΔ₀ : μ[YΔ 0] = μ[fun ω => P 0 ω - Dt 0 ω])
    (hΔ : ∀ ℓ, μ[YΔ (ℓ + 1)] = μ[fun ω => (P (ℓ + 1) ω - P ℓ ω) - Dt (ℓ + 1) ω]) :
    μ[fun ω => (∑ ℓ ∈ range (L + 1), (Yt ℓ ω + YΔ ℓ ω) - m) ^ 2] =
      ∑ ℓ ∈ range (L + 1), (variance (Yt ℓ) μ + variance (YΔ ℓ) μ) + (μ[P L] - m) ^ 2 := by
  -- the level estimators `Y ℓ = Yt ℓ + YΔ ℓ`
  set Y : ℕ → Ω → ℝ := fun ℓ => Yt ℓ + YΔ ℓ with hY_def
  have hY : ∀ ℓ, MemLp (Y ℓ) 2 μ := fun ℓ => (hYt ℓ).add (hYΔ ℓ)
  have hYsum : ∑ ℓ ∈ range (L + 1), Y ℓ = ∑ p ∈ nIdx L, pairFam Yt YΔ p := by
    rw [sum_nIdx]
    rfl
  -- variance via the `2(L+1)` independent components
  have hvar : variance (∑ ℓ ∈ range (L + 1), Y ℓ) μ =
      ∑ ℓ ∈ range (L + 1), (variance (Yt ℓ) μ + variance (YΔ ℓ) μ) := by
    rw [hYsum, IndepFun.variance_sum (fun p _ => ?_) hind, sum_nIdx]
    · simp
    · rcases p with ⟨ℓ, b⟩
      cases b
      · exact hYΔ ℓ
      · exact hYt ℓ
  -- mean via the telescoping sum (9)
  have hmean : μ[∑ ℓ ∈ range (L + 1), Y ℓ] = μ[P L] := by
    apply mlmc_mean P Y L (fun ℓ => (hY ℓ).integrable one_le_two) hP
    · show μ[fun ω => Yt 0 ω + YΔ 0 ω] = μ[P 0]
      rw [integral_add ((hYt 0).integrable one_le_two) ((hYΔ 0).integrable one_le_two), ht, hΔ₀,
        integral_sub (hP 0) (hDt 0)]
      ring
    · intro ℓ
      show μ[fun ω => Yt (ℓ + 1) ω + YΔ (ℓ + 1) ω] = μ[fun ω => P (ℓ + 1) ω - P ℓ ω]
      rw [integral_add ((hYt _).integrable one_le_two) ((hYΔ _).integrable one_le_two), ht, hΔ,
        integral_sub ((hP _).sub (hP _)) (hDt _), integral_sub (hP _) (hP _),
        integral_sub (hP _) (hP _)]
      ring
  have hsum : MemLp (∑ ℓ ∈ range (L + 1), Y ℓ) 2 μ := memLp_finset_sum' _ (fun ℓ _ => hY ℓ)
  have h := mse_eq_variance_add_sq_bias hsum m
  rw [hvar, hmean] at h
  have hfun : (fun ω => (∑ ℓ ∈ range (L + 1), (Yt ℓ ω + YΔ ℓ ω) - m) ^ 2) =
      fun ω => ((∑ ℓ ∈ range (L + 1), Y ℓ) ω - m) ^ 2 := by
    ext ω
    simp [Finset.sum_apply, hY_def]
  rw [hfun]
  exact h

end MLMC
