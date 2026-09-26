import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import MlmcLean.Allocation
import MlmcLean.Estimator
import MlmcLean.SampleMean

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

We prove (12) rigorously by applying the optimal-allocation theorem of `MlmcLean/Allocation.lean`
to the index set `levels × {low precision, correction}`:

* `nested_cost_isLeast`: (12) is the least cost (10) over all real allocations with variance
  (11) at most `ε²`, attained by the paper's Lagrange-multiplier allocation (`λ_M`);
* `nested_cost_lower_bound`: every allocation meeting (11) `≤ ε²` costs at least (12);
* `nested_optimal_allocation`: integer sample numbers exist meeting (11) `≤ ε²` with cost at most
  (12) plus `∑ (C̃_ℓ + C^Δ_ℓ)`, a bound for the rounding-up overhead that the paper ignores;
* `nested_saving`: the paper's "saving of a factor approximately `max_ℓ C̃_ℓ/C^Δ_ℓ`" (p. 4) as an
  inequality between the optimal costs (12) and (8).

On a probability space:

* `nestedEstimator_mean_variance`: the nested estimator built from independent samples has mean
  `E[P_L]` (9) and variance `∑ Ṽ_ℓ/Ñ_ℓ + V^Δ_ℓ/N^Δ_ℓ` (11); `nestedCost_mean`: its expected cost is
  `∑ Ñ_ℓ C̃_ℓ + N^Δ_ℓ C^Δ_ℓ` (10);
* `nested_mlmc_mse`: for abstract independent component estimators with the right means, the
  mean, the variance and the MSE `∑ (V[Ỹ_ℓ] + V[Y^Δ_ℓ]) + (E[P_L] − m)²` (Giles 2015, (2.1)).
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
  · have h := optimalN_variance hs (fun p _ => hV p) (fun p _ => hC p) hτ
    rw [sum_nIdx] at h
    simpa using h
  · have h := optimalN_cost hs (fun p _ => hV p) (fun p _ => hC p) hτ
    rw [sum_nIdx, sum_nIdx, sum_nIdx] at h
    simpa using h

/-- **Haas–Giles (12), exactly.**  Among all real allocations `ñ_ℓ, n^Δ_ℓ > 0` whose nested
variance (11) is at most `ε²`, the least nested cost (10) is
`ε⁻² (∑_ℓ √(Ṽ_ℓ C̃_ℓ) + √(V^Δ_ℓ C^Δ_ℓ))²`; it is attained by the Lagrange-multiplier allocation
`Ñ_ℓ = λ_M √(Ṽ_ℓ/C̃_ℓ)`, `N^Δ_ℓ = λ_M √(V^Δ_ℓ/C^Δ_ℓ)` of the paper (`lagrangeN` on the index set
`levels × {low precision, correction}`). -/
theorem nested_cost_isLeast {ε : ℝ} (hε : 0 < ε)
    (hVt : ∀ ℓ, 0 < Vt ℓ) (hVΔ : ∀ ℓ, 0 < VΔ ℓ) (hCt : ∀ ℓ, 0 < Ct ℓ) (hCΔ : ∀ ℓ, 0 < CΔ ℓ) :
    IsLeast {c | ∃ nt nΔ : ℕ → ℝ, (∀ ℓ, 0 < nt ℓ) ∧ (∀ ℓ, 0 < nΔ ℓ) ∧
        ∑ ℓ ∈ range (L + 1), (Vt ℓ / nt ℓ + VΔ ℓ / nΔ ℓ) ≤ ε ^ 2 ∧
        c = ∑ ℓ ∈ range (L + 1), (nt ℓ * Ct ℓ + nΔ ℓ * CΔ ℓ)}
      ((ε ^ 2)⁻¹ *
        (∑ ℓ ∈ range (L + 1), (Real.sqrt (Vt ℓ * Ct ℓ) + Real.sqrt (VΔ ℓ * CΔ ℓ))) ^ 2) := by
  have hs := nIdx_nonempty L
  have hV := pairFam_pos hVt hVΔ
  have hC := pairFam_pos hCt hCΔ
  have hτ : 0 < ε ^ 2 := by positivity
  obtain ⟨hvarL, hcostL⟩ := lagrangeN_variance_cost hs (fun p _ => hV p) (fun p _ => hC p) hτ
  rw [sum_nIdx] at hvarL
  rw [sum_nIdx, sum_nIdx] at hcostL
  simp only [pairFam_true, pairFam_false] at hvarL hcostL
  refine ⟨⟨fun ℓ => lagrangeN (nIdx L) (pairFam Vt VΔ) (pairFam Ct CΔ) (ε ^ 2) (ℓ, true),
    fun ℓ => lagrangeN (nIdx L) (pairFam Vt VΔ) (pairFam Ct CΔ) (ε ^ 2) (ℓ, false),
    fun ℓ => lagrangeN_pos hs (fun p _ => hV p) (fun p _ => hC p) hτ (hV _) (hC _),
    fun ℓ => lagrangeN_pos hs (fun p _ => hV p) (fun p _ => hC p) hτ (hV _) (hC _),
    hvarL.le, hcostL.symm⟩, ?_⟩
  rintro c ⟨nt, nΔ, hnt, hnΔ, hvar, rfl⟩
  exact nested_cost_lower_bound L Vt Ct VΔ CΔ nt nΔ hε (fun ℓ => (hVt ℓ).le)
    (fun ℓ => (hVΔ ℓ).le) (fun ℓ => (hCt ℓ).le) (fun ℓ => (hCΔ ℓ).le) hnt hnΔ hvar

/-- **The saving of nested MLMC, made precise** (Haas–Giles 2025, §2.2, p. 4: "if
`V^Δ_ℓ/Ṽ_ℓ ≪ C̃_ℓ/C^Δ_ℓ ≪ 1` then the nested estimation leads to a computational saving of a factor
approximately `max_ℓ C̃_ℓ/C^Δ_ℓ` compared to the standard MLMC framework").  Suppose that on every
level `ℓ ≤ L` the cost ratio is `C̃_ℓ/C^Δ_ℓ ≤ r`, the correction is small,
`V^Δ_ℓ ≤ δ² (C̃_ℓ/C^Δ_ℓ) Ṽ_ℓ`, and the low-precision variance and the correction cost compare with
the full-precision `V_ℓ, C_ℓ` as `Ṽ_ℓ ≤ θ V_ℓ`, `C^Δ_ℓ ≤ (1 + κ) C_ℓ`.  Then the optimal nested
cost (12) is at most `(1 + δ)² θ (1 + κ) r` times the optimal MLMC cost (8)
`ε⁻² (∑ √(V_ℓ C_ℓ))²`; with `δ, κ` small and `θ ≈ 1` the factor is `≈ r = max_ℓ C̃_ℓ/C^Δ_ℓ`. -/
theorem nested_saving (V C : ℕ → ℝ) {ε δ θ κ r : ℝ}
    (hCt : ∀ ℓ, 0 ≤ Ct ℓ) (hCΔ : ∀ ℓ, 0 < CΔ ℓ)
    (hV : ∀ ℓ, 0 ≤ V ℓ) (hC : ∀ ℓ, 0 ≤ C ℓ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (hκ : 0 ≤ 1 + κ)
    (hr : ∀ ℓ ∈ range (L + 1), Ct ℓ / CΔ ℓ ≤ r)
    (hsmall : ∀ ℓ ∈ range (L + 1), VΔ ℓ ≤ δ ^ 2 * (Ct ℓ / CΔ ℓ) * Vt ℓ)
    (hVV : ∀ ℓ ∈ range (L + 1), Vt ℓ ≤ θ * V ℓ)
    (hCC : ∀ ℓ ∈ range (L + 1), CΔ ℓ ≤ (1 + κ) * C ℓ) :
    (ε ^ 2)⁻¹ *
        (∑ ℓ ∈ range (L + 1), (Real.sqrt (Vt ℓ * Ct ℓ) + Real.sqrt (VΔ ℓ * CΔ ℓ))) ^ 2 ≤
      (1 + δ) ^ 2 * θ * (1 + κ) * r *
        ((ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) := by
  have hL : 0 ∈ range (L + 1) := Finset.mem_range.2 (Nat.succ_pos L)
  have hr0 : 0 ≤ r := le_trans (div_nonneg (hCt 0) (hCΔ 0).le) (hr 0 hL)
  have hA : 0 ≤ θ * (1 + κ) * r := mul_nonneg (mul_nonneg hθ hκ) hr0
  have hterm : ∀ ℓ ∈ range (L + 1), Real.sqrt (Vt ℓ * Ct ℓ) + Real.sqrt (VΔ ℓ * CΔ ℓ) ≤
      (1 + δ) * Real.sqrt (θ * (1 + κ) * r) * Real.sqrt (V ℓ * C ℓ) := by
    intro ℓ hℓ
    have hCΔ0 := hCΔ ℓ
    have hdiv : Ct ℓ / CΔ ℓ * CΔ ℓ = Ct ℓ := div_mul_cancel₀ _ hCΔ0.ne'
    -- the correction term is at most `δ √(Ṽ C̃)`
    have h1 : Real.sqrt (VΔ ℓ * CΔ ℓ) ≤ δ * Real.sqrt (Vt ℓ * Ct ℓ) := by
      have hle : VΔ ℓ * CΔ ℓ ≤ δ ^ 2 * (Vt ℓ * Ct ℓ) := by
        calc VΔ ℓ * CΔ ℓ ≤ δ ^ 2 * (Ct ℓ / CΔ ℓ) * Vt ℓ * CΔ ℓ :=
              mul_le_mul_of_nonneg_right (hsmall ℓ hℓ) hCΔ0.le
          _ = δ ^ 2 * (Vt ℓ * Ct ℓ) := by linear_combination (δ ^ 2 * Vt ℓ) * hdiv
      calc Real.sqrt (VΔ ℓ * CΔ ℓ) ≤ Real.sqrt (δ ^ 2 * (Vt ℓ * Ct ℓ)) := Real.sqrt_le_sqrt hle
        _ = δ * Real.sqrt (Vt ℓ * Ct ℓ) := by
            rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ]
    -- the low-precision term is at most `√(θ (1+κ) r) √(V C)`
    have h2 : Real.sqrt (Vt ℓ * Ct ℓ) ≤ Real.sqrt (θ * (1 + κ) * r) * Real.sqrt (V ℓ * C ℓ) := by
      rw [← Real.sqrt_mul hA]
      apply Real.sqrt_le_sqrt
      have e : Vt ℓ * Ct ℓ = Vt ℓ * CΔ ℓ * (Ct ℓ / CΔ ℓ) := by
        linear_combination (-Vt ℓ) * hdiv
      rw [e]
      calc Vt ℓ * CΔ ℓ * (Ct ℓ / CΔ ℓ) ≤ θ * V ℓ * ((1 + κ) * C ℓ) * r :=
            mul_le_mul (mul_le_mul (hVV ℓ hℓ) (hCC ℓ hℓ) hCΔ0.le (mul_nonneg hθ (hV ℓ)))
              (hr ℓ hℓ) (div_nonneg (hCt ℓ) hCΔ0.le)
              (mul_nonneg (mul_nonneg hθ (hV ℓ)) (mul_nonneg hκ (hC ℓ)))
        _ = θ * (1 + κ) * r * (V ℓ * C ℓ) := by ring
    calc Real.sqrt (Vt ℓ * Ct ℓ) + Real.sqrt (VΔ ℓ * CΔ ℓ)
        ≤ (1 + δ) * Real.sqrt (Vt ℓ * Ct ℓ) := by linarith
      _ ≤ (1 + δ) * (Real.sqrt (θ * (1 + κ) * r) * Real.sqrt (V ℓ * C ℓ)) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = (1 + δ) * Real.sqrt (θ * (1 + κ) * r) * Real.sqrt (V ℓ * C ℓ) := by ring
  have hsum : ∑ ℓ ∈ range (L + 1), (Real.sqrt (Vt ℓ * Ct ℓ) + Real.sqrt (VΔ ℓ * CΔ ℓ)) ≤
      (1 + δ) * Real.sqrt (θ * (1 + κ) * r) * ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hsum0 : 0 ≤ ∑ ℓ ∈ range (L + 1), (Real.sqrt (Vt ℓ * Ct ℓ) + Real.sqrt (VΔ ℓ * CΔ ℓ)) :=
    Finset.sum_nonneg fun ℓ _ => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hK2 : ((1 + δ) * Real.sqrt (θ * (1 + κ) * r)) ^ 2 = (1 + δ) ^ 2 * (θ * (1 + κ) * r) := by
    rw [mul_pow, Real.sq_sqrt hA]
  calc (ε ^ 2)⁻¹ *
        (∑ ℓ ∈ range (L + 1), (Real.sqrt (Vt ℓ * Ct ℓ) + Real.sqrt (VΔ ℓ * CΔ ℓ))) ^ 2
      ≤ (ε ^ 2)⁻¹ * ((1 + δ) * Real.sqrt (θ * (1 + κ) * r) *
          ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum0 hsum 2) (by positivity)
    _ = (1 + δ) ^ 2 * θ * (1 + κ) * r *
          ((ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) := by
        rw [mul_pow, hK2]
        ring

end deterministic

/-! ### The nested estimator built from independent samples: (9)–(11) -/

section estimator

variable {Ω₀ Ω : Type*}

/-- The two kinds of samples of the nested estimator (Haas–Giles 2025, §2.2): on level `ℓ`, index
`(ℓ, true)` is the low-precision difference `Δ̃P_ℓ` and `(ℓ, false)` the correction
`ΔP_ℓ − Δ̃P_ℓ`, with `ΔP_ℓ = P_ℓ − P_{ℓ−1}` (`levelDiff`). -/
noncomputable def nestedTerm (Pl Dt : ℕ → Ω₀ → ℝ) : ℕ × Bool → Ω₀ → ℝ :=
  pairFam Dt fun ℓ y => levelDiff Pl ℓ y - Dt ℓ y

@[simp] lemma nestedTerm_true (Pl Dt : ℕ → Ω₀ → ℝ) (ℓ : ℕ) (y : Ω₀) :
    nestedTerm Pl Dt (ℓ, true) y = Dt ℓ y := rfl

@[simp] lemma nestedTerm_false (Pl Dt : ℕ → Ω₀ → ℝ) (ℓ : ℕ) (y : Ω₀) :
    nestedTerm Pl Dt (ℓ, false) y = levelDiff Pl ℓ y - Dt ℓ y := rfl

/-- The nested MLMC estimator (Haas–Giles 2025, §2.2, from (9)): the sum over the levels
`ℓ = 0, …, L` of the Monte Carlo average of `Nt ℓ` samples of `Δ̃P_ℓ` and of the Monte Carlo
average of `NΔ ℓ` samples of `ΔP_ℓ − Δ̃P_ℓ`, each sample computed from its own input
`ω ((ℓ, b), n)`. -/
noncomputable def nestedEstimator (Pl Dt : ℕ → Ω₀ → ℝ) (ω : (ℕ × Bool) × ℕ → Ω → Ω₀) (L : ℕ)
    (Nt NΔ : ℕ → ℕ) (x : Ω) : ℝ :=
  ∑ ℓ ∈ range (L + 1),
    (blockMean (nestedTerm Pl Dt) ω (ℓ, true) (Nt ℓ) x +
      blockMean (nestedTerm Pl Dt) ω (ℓ, false) (NΔ ℓ) x)

/-- The total cost of the nested estimator: `costT ℓ n` is the cost of the `n`-th low-precision
sample on level `ℓ` and `costΔ ℓ n` that of the `n`-th correction sample. -/
noncomputable def nestedCost (costT costΔ : ℕ → ℕ → Ω → ℝ) (L : ℕ) (Nt NΔ : ℕ → ℕ) (x : Ω) : ℝ :=
  ∑ ℓ ∈ range (L + 1), (∑ n ∈ range (Nt ℓ), costT ℓ n x + ∑ n ∈ range (NΔ ℓ), costΔ ℓ n x)

variable [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀} {μ : Measure Ω}
  {Pl Dt : ℕ → Ω₀ → ℝ} {ω : (ℕ × Bool) × ℕ → Ω → Ω₀}

omit [MeasurableSpace Ω₀] [MeasurableSpace Ω] in
lemma nestedEstimator_eq_sum (L : ℕ) (Nt NΔ : ℕ → ℕ) :
    nestedEstimator (Ω := Ω) Pl Dt ω L Nt NΔ =
      ∑ q ∈ nIdx L, blockMean (nestedTerm Pl Dt) ω q (pairFam Nt NΔ q) := by
  funext x
  rw [Finset.sum_apply, sum_nIdx]
  rfl

/-- **Haas–Giles (9) and (11) for the nested estimator built from samples.**  Let the inputs
`ω ((ℓ, b), n)` be mutually independent with law `ν`, the level approximations `Pl ℓ` and the
low-precision differences `Dt ℓ = Δ̃P_ℓ` be measurable and square-integrable, and all sample numbers
`Ñ_ℓ = Nt ℓ` and `N^Δ_ℓ = NΔ ℓ` be at least `1`.  Then the nested estimator has mean `E[P_L]`
(the identity (9)) and variance `∑_{ℓ=0}^{L} Ṽ_ℓ/Ñ_ℓ + V^Δ_ℓ/N^Δ_ℓ` (11), where
`Ṽ_ℓ = V[Δ̃P_ℓ]` and `V^Δ_ℓ = V[ΔP_ℓ − Δ̃P_ℓ]`. -/
theorem nestedEstimator_mean_variance [IsProbabilityMeasure μ]
    (hω : ∀ q, MeasurePreserving (ω q) μ ν) (hind : iIndepFun ω μ)
    (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hDtm : ∀ ℓ, Measurable (Dt ℓ))
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν) (hDt : ∀ ℓ, MemLp (Dt ℓ) 2 ν) (L : ℕ) {Nt NΔ : ℕ → ℕ}
    (hNt : ∀ ℓ, 0 < Nt ℓ) (hNΔ : ∀ ℓ, 0 < NΔ ℓ) :
    μ[nestedEstimator Pl Dt ω L Nt NΔ] = ∫ y, Pl L y ∂ν ∧
      variance (nestedEstimator Pl Dt ω L Nt NΔ) μ =
        ∑ ℓ ∈ range (L + 1), (variance (Dt ℓ) ν / Nt ℓ +
          variance (fun y => levelDiff Pl ℓ y - Dt ℓ y) ν / NΔ ℓ) := by
  -- the law `ν` of the inputs is a probability measure, as the image of `μ`
  have : IsProbabilityMeasure ν := by
    rw [← (hω ((0, true), 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω ((0, true), 0)).measurable.aemeasurable
  have hTm : ∀ q, Measurable (nestedTerm Pl Dt q) := by
    rintro ⟨ℓ, b⟩
    cases b
    · exact (measurable_levelDiff hPlm ℓ).sub (hDtm ℓ)
    · exact hDtm ℓ
  have hT : ∀ q, MemLp (nestedTerm Pl Dt q) 2 ν := by
    rintro ⟨ℓ, b⟩
    cases b
    · exact (memLp_levelDiff hPl ℓ).sub (hDt ℓ)
    · exact hDt ℓ
  have hT1 : ∀ q, Integrable (nestedTerm Pl Dt q) ν := fun q => (hT q).integrable one_le_two
  have hPl1 : ∀ ℓ, Integrable (Pl ℓ) ν := fun ℓ => (hPl ℓ).integrable one_le_two
  have hB : ∀ q N, Integrable (blockMean (nestedTerm Pl Dt) ω q N) μ := fun q N =>
    (memLp_blockMean hω hT q N).integrable one_le_two
  constructor
  · -- (9): the expectations telescope
    have hint : ∀ ℓ, Integrable (fun x => blockMean (nestedTerm Pl Dt) ω (ℓ, true) (Nt ℓ) x +
        blockMean (nestedTerm Pl Dt) ω (ℓ, false) (NΔ ℓ) x) μ := fun ℓ =>
      (hB (ℓ, true) (Nt ℓ)).add (hB (ℓ, false) (NΔ ℓ))
    simp only [nestedEstimator]
    rw [integral_finsetSum _ fun ℓ _ => hint ℓ]
    have hterm : ∀ ℓ, ∫ x, (blockMean (nestedTerm Pl Dt) ω (ℓ, true) (Nt ℓ) x +
        blockMean (nestedTerm Pl Dt) ω (ℓ, false) (NΔ ℓ) x) ∂μ = ∫ y, levelDiff Pl ℓ y ∂ν := by
      intro ℓ
      rw [integral_add (hB (ℓ, true) (Nt ℓ)) (hB (ℓ, false) (NΔ ℓ)),
        integral_blockMean hω hT1 (ℓ, true) (hNt ℓ), integral_blockMean hω hT1 (ℓ, false) (hNΔ ℓ)]
      simp only [nestedTerm_true, nestedTerm_false]
      rw [integral_sub (integrable_levelDiff hPl1 ℓ) ((hDt ℓ).integrable one_le_two)]
      ring
    rw [Finset.sum_congr rfl fun ℓ _ => hterm ℓ]
    exact sum_integral_levelDiff hPl1 L
  · -- (11): the `2(L+1)` Monte Carlo averages are independent
    have hN : ∀ q, 0 < pairFam Nt NΔ q := by
      rintro ⟨ℓ, b⟩
      cases b
      · exact hNΔ ℓ
      · exact hNt ℓ
    rw [nestedEstimator_eq_sum, IndepFun.variance_sum
      (fun q _ => memLp_blockMean hω hT q (pairFam Nt NΔ q))
      (fun q _ r _ hqr => indepFun_blockMean (fun q => (hω q).measurable) hind hTm hqr _ _),
      sum_nIdx]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [variance_blockMean hω hind hTm hT (ℓ, true) (hN _),
      variance_blockMean hω hind hTm hT (ℓ, false) (hN _)]
    rfl

/-- **Haas–Giles (10), the expected cost of the nested estimator.**  If every low-precision
sample on level `ℓ` has integrable cost with mean `C̃_ℓ` and every correction sample has integrable
cost with mean `C^Δ_ℓ`, the expected total cost is `∑_{ℓ=0}^{L} Ñ_ℓ C̃_ℓ + N^Δ_ℓ C^Δ_ℓ`. -/
theorem nestedCost_mean (costT costΔ : ℕ → ℕ → Ω → ℝ) (Ct CΔ : ℕ → ℝ)
    (hT : ∀ ℓ n, Integrable (costT ℓ n) μ) (hΔ : ∀ ℓ n, Integrable (costΔ ℓ n) μ)
    (hTm : ∀ ℓ n, μ[costT ℓ n] = Ct ℓ) (hΔm : ∀ ℓ n, μ[costΔ ℓ n] = CΔ ℓ)
    (L : ℕ) (Nt NΔ : ℕ → ℕ) :
    μ[nestedCost costT costΔ L Nt NΔ] =
      ∑ ℓ ∈ range (L + 1), ((Nt ℓ : ℝ) * Ct ℓ + (NΔ ℓ : ℝ) * CΔ ℓ) := by
  have hTs : ∀ ℓ, Integrable (fun x => ∑ n ∈ range (Nt ℓ), costT ℓ n x) μ := fun ℓ =>
    integrable_finsetSum _ fun n _ => hT ℓ n
  have hΔs : ∀ ℓ, Integrable (fun x => ∑ n ∈ range (NΔ ℓ), costΔ ℓ n x) μ := fun ℓ =>
    integrable_finsetSum _ fun n _ => hΔ ℓ n
  have hint : ∀ ℓ, Integrable (fun x => ∑ n ∈ range (Nt ℓ), costT ℓ n x +
      ∑ n ∈ range (NΔ ℓ), costΔ ℓ n x) μ := fun ℓ => (hTs ℓ).add (hΔs ℓ)
  simp only [nestedCost]
  rw [integral_finsetSum _ fun ℓ _ => hint ℓ]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [integral_add (hTs ℓ) (hΔs ℓ), integral_finsetSum _ fun n _ => hT ℓ n,
    integral_finsetSum _ fun n _ => hΔ ℓ n]
  simp only [hTm, hΔm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end estimator

/-! ### Abstract component estimators: mean, variance and MSE -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Haas–Giles (9) and (11) in component-estimator form, with Giles (2015), (2.1).**  Let `Pℓ ℓ`
be the level-`ℓ` approximation and `Dt ℓ` the low-precision level difference `Δ̃P_ℓ`.  Let `Yt ℓ`
estimate `E[Δ̃P_ℓ]` and `YΔ ℓ` estimate `E[ΔP_ℓ − Δ̃P_ℓ]` (`ΔP_ℓ = levelDiff Pℓ ℓ`), all `2(L+1)`
square-integrable estimators pairwise independent.  Then the nested estimator `∑_ℓ (Yt ℓ + YΔ ℓ)`
has mean `E[P_L]` (the identity (9)), variance `∑_ℓ (V[Yt ℓ] + V[YΔ ℓ])` (the form of (11) before
the per-sample variances are inserted), and mean-square error
`∑_ℓ (V[Yt ℓ] + V[YΔ ℓ]) + (E[P_L] − m)²` for any target `m` (the MSE when `m = E[P]`). -/
theorem nested_mlmc_mse (Pℓ Dt : ℕ → Ω → ℝ) (Yt YΔ : ℕ → Ω → ℝ) (L : ℕ) (m : ℝ)
    (hYt : ∀ ℓ, MemLp (Yt ℓ) 2 μ) (hYΔ : ∀ ℓ, MemLp (YΔ ℓ) 2 μ)
    (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ) (hDt : ∀ ℓ, Integrable (Dt ℓ) μ)
    (hind : Set.Pairwise ↑(nIdx L) fun i j => IndepFun (pairFam Yt YΔ i) (pairFam Yt YΔ j) μ)
    (ht : ∀ ℓ, μ[Yt ℓ] = μ[Dt ℓ])
    (hΔ : ∀ ℓ, μ[YΔ ℓ] = μ[fun ω => levelDiff Pℓ ℓ ω - Dt ℓ ω]) :
    μ[fun ω => ∑ ℓ ∈ range (L + 1), (Yt ℓ ω + YΔ ℓ ω)] = μ[Pℓ L] ∧
      variance (fun ω => ∑ ℓ ∈ range (L + 1), (Yt ℓ ω + YΔ ℓ ω)) μ =
        ∑ ℓ ∈ range (L + 1), (variance (Yt ℓ) μ + variance (YΔ ℓ) μ) ∧
      μ[fun ω => (∑ ℓ ∈ range (L + 1), (Yt ℓ ω + YΔ ℓ ω) - m) ^ 2] =
        ∑ ℓ ∈ range (L + 1), (variance (Yt ℓ) μ + variance (YΔ ℓ) μ) + (μ[Pℓ L] - m) ^ 2 := by
  -- mean via the telescoping sum (9)
  have hmean : μ[fun ω => ∑ ℓ ∈ range (L + 1), (Yt ℓ ω + YΔ ℓ ω)] = μ[Pℓ L] := by
    have hint : ∀ ℓ, Integrable (fun ω => Yt ℓ ω + YΔ ℓ ω) μ := fun ℓ =>
      ((hYt ℓ).add (hYΔ ℓ)).integrable one_le_two
    rw [integral_finsetSum _ fun ℓ _ => hint ℓ]
    have hterm : ∀ ℓ, ∫ ω, (Yt ℓ ω + YΔ ℓ ω) ∂μ = ∫ ω, levelDiff Pℓ ℓ ω ∂μ := fun ℓ => by
      rw [integral_add ((hYt ℓ).integrable one_le_two) ((hYΔ ℓ).integrable one_le_two), ht, hΔ,
        integral_sub (integrable_levelDiff hPℓ ℓ) (hDt ℓ)]
      ring
    rw [Finset.sum_congr rfl fun ℓ _ => hterm ℓ]
    exact sum_integral_levelDiff hPℓ L
  -- variance via the `2(L+1)` independent components
  have hfun : (fun ω => ∑ ℓ ∈ range (L + 1), (Yt ℓ ω + YΔ ℓ ω)) =
      ∑ p ∈ nIdx L, pairFam Yt YΔ p := by
    funext ω
    rw [Finset.sum_apply, sum_nIdx]
    rfl
  have hvar : variance (fun ω => ∑ ℓ ∈ range (L + 1), (Yt ℓ ω + YΔ ℓ ω)) μ =
      ∑ ℓ ∈ range (L + 1), (variance (Yt ℓ) μ + variance (YΔ ℓ) μ) := by
    rw [hfun, IndepFun.variance_sum (fun p _ => ?_) hind, sum_nIdx]
    · simp
    · rcases p with ⟨ℓ, b⟩
      cases b
      · exact hYΔ ℓ
      · exact hYt ℓ
  have hsum : MemLp (fun ω => ∑ ℓ ∈ range (L + 1), (Yt ℓ ω + YΔ ℓ ω)) 2 μ :=
    memLp_finsetSum _ fun ℓ _ => (hYt ℓ).add (hYΔ ℓ)
  refine ⟨hmean, hvar, (mse_eq_variance_add_sq_bias hsum m).trans ?_⟩
  rw [hvar, hmean]

end MLMC
