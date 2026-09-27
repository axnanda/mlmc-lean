import MlmcLean.Estimator
import MlmcLean.Complexity
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Giles' Theorem 1 on a probability space

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1,
Theorem 1 (pp. 6–7 of the author's version).

This file states Theorem 1 as Giles states it — for random variables on a probability space
`(Ω, μ)` — and proves it from

* `MlmcLean.Estimator`: `MSE = ∑ V[Y_ℓ] + (E[P_L] − E[P])²` (Giles (2.1), (2.3)),
* `MlmcLean.Complexity`: the deterministic choice of `L`, `N_ℓ` and the three cost regimes.

**Data.**
* `P : Ω → ℝ` — the quantity of interest, `Pℓ ℓ` — its level-`ℓ` approximation;
* `Y ℓ n : Ω → ℝ` — the level-`ℓ` estimator "based on `n` Monte Carlo samples";
* `V ℓ` — the variance of one sample at level `ℓ`, so `V[Y_ℓ] = V_ℓ / N_ℓ` (Giles (2.3));
* `C ℓ` — the expected cost of one sample at level `ℓ`;
* `Cost ℓ n : Ω → ℝ` — the (random) cost of computing `Y ℓ n`, with `E[Cost ℓ n] = n C_ℓ`.

**Hypotheses.** (i), (iii) and (iv) are the paper's.  The theorem *chooses* the sample sizes, so
the estimators are given for every sample size `n ≥ 1`; condition (ii), the variance identity
`V[Y ℓ n] = V ℓ / n`, square-integrability and the cost identity are required for every `n ≥ 1`,
and (pairwise) independence across levels for every choice of sample sizes `N ≥ 1`.  `P` and the
`Pℓ ℓ` are integrable (implicit in the paper).

* `giles_theorem1` — the theorem, with the paper's conclusion `E[C] ≤ c₄ · (…)` for the random
  total cost `C = ∑_ℓ Cost ℓ (N ℓ)`;
* `giles_theorem1_cost_sum` — the same with the cost written as `∑ N_ℓ C_ℓ` (`= E[C]`);
* `giles_theorem1_uniform` — the theorem with one constant `c₄` for all probability spaces and
  data, depending only on `α, β, γ, c₁, c₂, c₃` (as in the paper's proof);
* `giles_theorem1_isBigO` — the three regimes as `Asymptotics.IsBigO` statements as `ε → 0⁺`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Asymptotics Topology

namespace MLMC

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The variance of a Monte Carlo average of `N` pairwise independent samples of common variance
`v` is `v / N` (Giles 2015, §1.1, p. 2: "The variance of this estimate is `N⁻¹V[P]`"; this is how
`V[Y_ℓ] = N_ℓ⁻¹ V_ℓ` in (2.2)–(2.3) arises).  It holds for any measure `μ`, in particular on a
probability space. -/
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

/-- **Giles' Theorem 1 from the deterministic core** (a step of this formalisation's proof of
Giles 2015, §2.1, Theorem 1).  Hypotheses (i)–(iv) as in `giles_theorem1_cost_sum`, and any
constant `c₄` with the property that `mlmc_complexity_core` provides: for every `0 < ε < e⁻¹`
there are `L` and `N_ℓ ≥ 1` with `(c₁ 2^{−αL})² + ∑_{ℓ=0}^{L} c₂ 2^{−βℓ}/N_ℓ < ε²` and
`∑_{ℓ=0}^{L} N_ℓ c₃ 2^{γℓ} ≤ c₄ · complexityBound α β γ ε`.  Then for every `0 < ε < e⁻¹` there are
`L` and `N_ℓ ≥ 1` for which the multilevel estimator has `MSE < ε²` and
`∑_{ℓ=0}^{L} N_ℓ C_ℓ ≤ c₄ · complexityBound α β γ ε`.  The constant `c₄` is not changed, so it
depends only on what the core's constant depends on (`giles_theorem1_uniform`). -/
theorem giles_theorem1_of_core
    (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (V C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ c₄ : ℝ}
    (hcore : ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ ≤ c₄ * complexityBound α β γ ε)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (h_i : ∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ c₄ * complexityBound α β γ ε := by
  intro ε hε hε1
  obtain ⟨L, N, hN, hmse, hcost⟩ := hcore ε hε hε1
  refine ⟨L, N, hN, ?_, ?_⟩
  · -- mean-square error
    have hind' : Set.Pairwise ↑(range (L + 1)) fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ :=
      fun i _ j _ hij => hind N hN hij
    rw [mlmc_mse Pℓ (fun ℓ => Y ℓ (N ℓ)) L (μ[P]) (fun ℓ => hY ℓ (N ℓ) (hN ℓ)) hPℓ hind'
      (h_ii₀ (N 0) (hN 0)) (fun ℓ => h_ii ℓ (N (ℓ + 1)) (hN (ℓ + 1)))]
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

/-- **Giles' Theorem 1, with the cost written as `∑_ℓ N_ℓ C_ℓ`** (Giles 2015, §2.1, Theorem 1).
Hypotheses as in `giles_theorem1` without the random costs; the conclusion bounds
`∑_{ℓ=0}^{L} N_ℓ C_ℓ`, which is the expected total cost `E[C]` when each level-`ℓ` sample has
expected cost `C_ℓ`. -/
theorem giles_theorem1_cost_sum
    (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (V C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (h_i : ∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ c₄ * complexityBound α β γ ε := by
  obtain ⟨c₄, hc₄, hcore⟩ :=
    mlmc_complexity_core (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) hα hβ hγ hc₁ hc₂ hc₃ hαβγ
  exact ⟨c₄, hc₄, giles_theorem1_of_core P Pℓ Y V C hcore hP hPℓ hY hind h_i h_ii₀ h_ii h_var
    h_iii h_iv⟩

/-- **Giles' Theorem 1** (Giles 2015, §2.1, Theorem 1).
Let `P` be an integrable random variable and `Pℓ ℓ` its integrable level-`ℓ` approximation.
Suppose there are square-integrable estimators `Y ℓ n` based on `n ≥ 1` Monte Carlo samples,
pairwise independent across levels for every choice of sample sizes `N ≥ 1`, whose samples at
level `ℓ` have variance `V ℓ` (so `V[Y ℓ n] = V ℓ / n` for `n ≥ 1`) and expected cost `C ℓ` (so
the integrable random cost `Cost ℓ n` of computing `Y ℓ n` has `E[Cost ℓ n] = n C ℓ` for
`n ≥ 1`), and positive constants `α, β, γ, c₁, c₂, c₃` with `α ≥ ½ min(β,γ)` and

  (i)   `|E[Pℓ ℓ − P]| ≤ c₁ 2^{−αℓ}`,
  (ii)  `E[Y 0 n] = E[Pℓ 0]`, `E[Y (ℓ+1) n] = E[Pℓ (ℓ+1) − Pℓ ℓ]` for `n ≥ 1`,
  (iii) `V ℓ ≤ c₂ 2^{−βℓ}`,
  (iv)  `C ℓ ≤ c₃ 2^{γℓ}`.

Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N ℓ ≥ 1` for which
the multilevel estimator `Y = ∑_{ℓ=0}^{L} Y ℓ (N ℓ)` has `MSE = E[(Y − E[P])²] < ε²` and its
computational cost `C = ∑_{ℓ=0}^{L} Cost ℓ (N ℓ)` has expectation
`E[C] ≤ c₄ ε⁻²` if `β > γ`, `c₄ ε⁻² (log ε)²` if `β = γ`, `c₄ ε^{−2−(γ−β)/α}` if `β < γ`. -/
theorem giles_theorem1
    (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (Cost : ℕ → ℕ → Ω → ℝ) (V C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost_int : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (hCost_mean : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_i : ∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        μ[fun ω => ∑ ℓ ∈ range (L + 1), Cost ℓ (N ℓ) ω] ≤ c₄ * complexityBound α β γ ε := by
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_cost_sum P Pℓ Y V C hα hβ hγ hc₁ hc₂ hc₃ hαβγ hP hPℓ hY
    hind h_i h_ii₀ h_ii h_var h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, hmse, ?_⟩
  have hE : μ[fun ω => ∑ ℓ ∈ range (L + 1), Cost ℓ (N ℓ) ω] =
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := by
    rw [integral_finsetSum _ fun ℓ _ => hCost_int ℓ (N ℓ) (hN ℓ)]
    exact Finset.sum_congr rfl fun ℓ _ => hCost_mean ℓ (N ℓ) (hN ℓ)
  rw [hE]
  exact hcost

universe u

/-- **Giles' Theorem 1 with a constant that depends only on `α, β, γ, c₁, c₂, c₃`** (Giles 2015,
§2.1, Theorem 1; the proof in the paper computes `c₄` from these six constants alone).  Let
`α, β, γ, c₁, c₂, c₃` be positive with `α ≥ ½ min(β,γ)`.  Then one `c₄ > 0` serves every
probability space and every `P`, `Pℓ`, `Y`, `Cost`, `V`, `C` that satisfy the hypotheses of
`giles_theorem1` with these constants: for every `0 < ε < e⁻¹` there are `L` and `N ℓ ≥ 1` for
which `Y = ∑_{ℓ=0}^{L} Y ℓ (N ℓ)` has `E[(Y − E[P])²] < ε²` and the cost
`C = ∑_{ℓ=0}^{L} Cost ℓ (N ℓ)` has `E[C] ≤ c₄ · complexityBound α β γ ε`. -/
theorem giles_theorem1_uniform {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α) :
    ∃ c₄ : ℝ, 0 < c₄ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (Cost : ℕ → ℕ → Ω → ℝ)
        (V C : ℕ → ℝ),
        Integrable P μ → (∀ ℓ, Integrable (Pℓ ℓ) μ) →
        (∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ) →
        (∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
          Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ) →
        (∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ) →
        (∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ) →
        (∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) →
        (∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0]) →
        (∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω]) →
        (∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n) →
        (∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) →
        (∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) →
        ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
          ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
            μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
            μ[fun ω => ∑ ℓ ∈ range (L + 1), Cost ℓ (N ℓ) ω] ≤
              c₄ * complexityBound α β γ ε := by
  obtain ⟨c₄, hc₄, hcore⟩ :=
    mlmc_complexity_core (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) hα hβ hγ hc₁ hc₂ hc₃ hαβγ
  refine ⟨c₄, hc₄, ?_⟩
  intro Ω _ μ _ P Pℓ Y Cost V C hP hPℓ hY hind hCost_int hCost_mean h_i h_ii₀ h_ii h_var h_iii
    h_iv ε hε hε1
  obtain ⟨L, N, hN, hmse, hcost⟩ := giles_theorem1_of_core P Pℓ Y V C hcore hP hPℓ hY hind h_i
    h_ii₀ h_ii h_var h_iii h_iv ε hε hε1
  refine ⟨L, N, hN, hmse, ?_⟩
  have hE : μ[fun ω => ∑ ℓ ∈ range (L + 1), Cost ℓ (N ℓ) ω] =
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := by
    rw [integral_finsetSum _ fun ℓ _ => hCost_int ℓ (N ℓ) (hN ℓ)]
    exact Finset.sum_congr rfl fun ℓ _ => hCost_mean ℓ (N ℓ) (hN ℓ)
  rw [hE]
  exact hcost

/-- **Corollary of Giles' Theorem 1: a weaker big-O form as `ε → 0⁺`** (Giles 2015, §2.1,
Theorem 1).  Under the hypotheses of `giles_theorem1_cost_sum` and nonnegative costs `C ℓ ≥ 0`
(`IsBigO` compares absolute values), one can choose
`L(ε)` and `N_ℓ(ε) ≥ 1` for all `0 < ε < e⁻¹` so that `MSE < ε²`, and the cost
`ε ↦ ∑_{ℓ ≤ L(ε)} N_ℓ(ε) C_ℓ` is, as `ε → 0⁺`,
`O(ε⁻²)` if `β > γ`, `O(ε⁻² (log ε)²)` if `β = γ`, and `O(ε^{−2−(γ−β)/α})` if `β < γ`. -/
theorem giles_theorem1_isBigO
    (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (V C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (h_i : ∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ)))
    (hC : ∀ ℓ, 0 ≤ C ℓ) :
    ∃ (L : ℝ → ℕ) (N : ℝ → ℕ → ℕ),
      (∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) → (∀ ℓ, 0 < N ε ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ range (L ε + 1), Y ℓ (N ε ℓ) ω - μ[P]) ^ 2] < ε ^ 2) ∧
      (γ < β → (fun ε => ∑ ℓ ∈ range (L ε + 1), (N ε ℓ : ℝ) * C ℓ) =O[𝓝[>] 0]
        fun ε => ε ^ (-2 : ℝ)) ∧
      (β = γ → (fun ε => ∑ ℓ ∈ range (L ε + 1), (N ε ℓ : ℝ) * C ℓ) =O[𝓝[>] 0]
        fun ε => ε ^ (-2 : ℝ) * (Real.log ε) ^ 2) ∧
      (β < γ → (fun ε => ∑ ℓ ∈ range (L ε + 1), (N ε ℓ : ℝ) * C ℓ) =O[𝓝[>] 0]
        fun ε => ε ^ (-2 - (γ - β) / α)) := by
  obtain ⟨c₄, -, h⟩ := giles_theorem1_cost_sum P Pℓ Y V C hα hβ hγ hc₁ hc₂ hc₃ hαβγ hP hPℓ hY
    hind h_i h_ii₀ h_ii h_var h_iii h_iv
  -- choose `L ε` and `N ε` for every `ε`, with the guarantees for `0 < ε < e⁻¹`
  have h' : ∀ ε : ℝ, ∃ (L : ℕ) (N : ℕ → ℕ), 0 < ε → ε < Real.exp (-1) →
      (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ c₄ * complexityBound α β γ ε := by
    intro ε
    by_cases hε : 0 < ε ∧ ε < Real.exp (-1)
    · obtain ⟨L, N, hLN⟩ := h ε hε.1 hε.2
      exact ⟨L, N, fun _ _ => hLN⟩
    · exact ⟨0, fun _ => 1, fun h1 h2 => absurd ⟨h1, h2⟩ hε⟩
  choose L N hLN using h'
  have hO : (fun ε => ∑ ℓ ∈ range (L ε + 1), (N ε ℓ : ℝ) * C ℓ) =O[𝓝[>] 0]
      fun ε => complexityBound α β γ ε := by
    refine IsBigO.of_bound c₄ ?_
    filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-1))] with ε hε
    obtain ⟨-, -, hcost⟩ := hLN ε hε.1 hε.2
    have h0 : 0 ≤ ∑ ℓ ∈ range (L ε + 1), (N ε ℓ : ℝ) * C ℓ :=
      Finset.sum_nonneg fun ℓ _ => mul_nonneg (Nat.cast_nonneg _) (hC ℓ)
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (complexityBound_nonneg hε.1)]
    exact hcost
  refine ⟨L, N, fun ε h1 h2 => ⟨(hLN ε h1 h2).1, (hLN ε h1 h2).2.1⟩, fun hlt => ?_,
    fun heq => ?_, fun hgt => ?_⟩
  · exact hO.congr_right fun ε => complexityBound_of_lt hlt ε
  · exact hO.congr_right fun ε => complexityBound_of_eq heq ε
  · exact hO.congr_right fun ε => complexityBound_of_gt hgt ε

end MLMC
