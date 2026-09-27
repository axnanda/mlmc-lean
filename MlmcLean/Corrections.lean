import MlmcLean.SampleMean

/-!
# Other multilevel corrections: the identity (2.4) and antithetic estimators

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1, pp. 8–9 of
the author's version.

"Equation (2.2) gives the natural choice for the multilevel correction estimator `Y_ℓ`.  However,
the multilevel theorem allows for the use of other estimators, provided they satisfy the restriction
of condition ii) which ensures that `E[Y] = E[P_L]`."  `giles_theorem1_corrections` is Theorem 1 for
the Monte Carlo averages `Y_ℓ = N_ℓ⁻¹ ∑_{n<N_ℓ} Δ_ℓ(ω^{(ℓ,n)})` of any family of level corrections
`Δ_ℓ` computed from independent inputs, under condition ii) `E[Δ_ℓ] = E[P_ℓ − P_{ℓ−1}]`.  Giles'
two examples:

* different fine and coarse approximations, `Y_ℓ = N_ℓ⁻¹ ∑ (P^f_ℓ(ω⁽ⁿ⁾) − P^c_{ℓ−1}(ω⁽ⁿ⁾))`:
  "Provided we maintain the identity `E[P^f_ℓ] = E[P^c_ℓ]` (2.4) … then condition ii) is
  satisfied" (`integral_fineCoarseDiff`, `giles_theorem1_fineCoarse`);
* antithetic samples, `Y_ℓ = N_ℓ⁻¹ ∑ ½(P_ℓ(ω⁽ⁿ⁾) + P_ℓ(ω_a⁽ⁿ⁾)) − P_{ℓ−1}(ω⁽ⁿ⁾)` with `ω_a⁽ⁿ⁾` of
  the same distribution as `ω⁽ⁿ⁾`: "Since `E[P_ℓ(ω_a⁽ⁿ⁾)] = E[P_ℓ(ω⁽ⁿ⁾)]`, then again condition ii)
  is satisfied" (`integral_antitheticDiff`, `giles_theorem1_antithetic`).  The antithetic input
  is `ω_a = a(ω)` for a measure-preserving map `a` of the input space (for Brownian paths, for
  instance, the path with swapped or reflected increments).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

section defs

variable {Ω₀ : Type*}

/-- The level correction with different fine and coarse approximations (Giles 2015, §2.1, p. 8):
`P^f_ℓ − P^c_{ℓ−1}`, with `P^c_{−1} ≡ 0`. -/
noncomputable def fineCoarseDiff (Pf Pc : ℕ → Ω₀ → ℝ) : ℕ → Ω₀ → ℝ
  | 0 => Pf 0
  | ℓ + 1 => fun y => Pf (ℓ + 1) y - Pc ℓ y

/-- The antithetic level correction (Giles 2015, §2.1, p. 9): `½(P_ℓ(ω) + P_ℓ(ω_a)) − P_{ℓ−1}(ω)`
with `P_{−1} ≡ 0`, where the antithetic input is `ω_a = a(ω)`. -/
noncomputable def antitheticDiff (Pl : ℕ → Ω₀ → ℝ) (a : Ω₀ → Ω₀) : ℕ → Ω₀ → ℝ
  | 0 => fun y => 2⁻¹ * (Pl 0 y + Pl 0 (a y))
  | ℓ + 1 => fun y => 2⁻¹ * (Pl (ℓ + 1) y + Pl (ℓ + 1) (a y)) - Pl ℓ y

end defs

section prob

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀}

lemma measurable_fineCoarseDiff {Pf Pc : ℕ → Ω₀ → ℝ} (hf : ∀ ℓ, Measurable (Pf ℓ))
    (hc : ∀ ℓ, Measurable (Pc ℓ)) : ∀ ℓ, Measurable (fineCoarseDiff Pf Pc ℓ)
  | 0 => hf 0
  | ℓ + 1 => (hf (ℓ + 1)).sub (hc ℓ)

lemma memLp_fineCoarseDiff {Pf Pc : ℕ → Ω₀ → ℝ} (hf : ∀ ℓ, MemLp (Pf ℓ) 2 ν)
    (hc : ∀ ℓ, MemLp (Pc ℓ) 2 ν) : ∀ ℓ, MemLp (fineCoarseDiff Pf Pc ℓ) 2 ν
  | 0 => hf 0
  | ℓ + 1 => (hf (ℓ + 1)).sub (hc ℓ)

lemma measurable_antitheticDiff {Pl : ℕ → Ω₀ → ℝ} {a : Ω₀ → Ω₀} (ha : Measurable a)
    (hPl : ∀ ℓ, Measurable (Pl ℓ)) : ∀ ℓ, Measurable (antitheticDiff Pl a ℓ)
  | 0 => ((hPl 0).add ((hPl 0).comp ha)).const_mul 2⁻¹
  | ℓ + 1 => (((hPl (ℓ + 1)).add ((hPl (ℓ + 1)).comp ha)).const_mul 2⁻¹).sub (hPl ℓ)

lemma memLp_antitheticDiff {Pl : ℕ → Ω₀ → ℝ} {a : Ω₀ → Ω₀} (ha : MeasurePreserving a ν ν)
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν) : ∀ ℓ, MemLp (antitheticDiff Pl a ℓ) 2 ν
  | 0 => ((hPl 0).add ((hPl 0).comp_measurePreserving ha)).const_mul 2⁻¹
  | ℓ + 1 =>
    (((hPl (ℓ + 1)).add ((hPl (ℓ + 1)).comp_measurePreserving ha)).const_mul 2⁻¹).sub (hPl ℓ)

/-- **Condition ii) for different fine and coarse approximations** (Giles 2015, §2.1, p. 8):
"Provided we maintain the identity `E[P^f_ℓ] = E[P^c_ℓ]` (2.4) so that the expectation on level `ℓ`
is the same for the two approximations, then condition ii) is satisfied": under (2.4),
`E[P^f_ℓ − P^c_{ℓ−1}] = E[P^f_ℓ − P^f_{ℓ−1}]` for every `ℓ` (with `P_{−1} ≡ 0`). -/
theorem integral_fineCoarseDiff {Pf Pc : ℕ → Ω₀ → ℝ} (hf : ∀ ℓ, Integrable (Pf ℓ) ν)
    (hc : ∀ ℓ, Integrable (Pc ℓ) ν) (h24 : ∀ ℓ, ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν) (ℓ : ℕ) :
    ∫ y, fineCoarseDiff Pf Pc ℓ y ∂ν = ∫ y, levelDiff Pf ℓ y ∂ν := by
  cases ℓ with
  | zero => rfl
  | succ ℓ =>
    have e1 : ∫ y, fineCoarseDiff Pf Pc (ℓ + 1) y ∂ν = ∫ y, Pf (ℓ + 1) y ∂ν - ∫ y, Pc ℓ y ∂ν :=
      integral_sub (hf (ℓ + 1)) (hc ℓ)
    have e2 : ∫ y, levelDiff Pf (ℓ + 1) y ∂ν = ∫ y, Pf (ℓ + 1) y ∂ν - ∫ y, Pf ℓ y ∂ν :=
      integral_sub (hf (ℓ + 1)) (hf ℓ)
    rw [e1, e2, h24 ℓ]

/-- **Condition ii) for antithetic estimators** (Giles 2015, §2.1, p. 9): "Some others define an
antithetic `ω_a⁽ⁿ⁾` with the same distribution as `ω⁽ⁿ⁾` … Since `E[P_ℓ(ω_a⁽ⁿ⁾)] = E[P_ℓ(ω⁽ⁿ⁾)]`,
then again condition ii) is satisfied": for a measure-preserving `a` (so that `ω_a = a(ω)` has the
law of `ω`), `E[½(P_ℓ + P_ℓ ∘ a) − P_{ℓ−1}] = E[P_ℓ − P_{ℓ−1}]` for every `ℓ` (with
`P_{−1} ≡ 0`). -/
theorem integral_antitheticDiff {Pl : ℕ → Ω₀ → ℝ} {a : Ω₀ → Ω₀} (ha : MeasurePreserving a ν ν)
    (hPl : ∀ ℓ, Integrable (Pl ℓ) ν) (ℓ : ℕ) :
    ∫ y, antitheticDiff Pl a ℓ y ∂ν = ∫ y, levelDiff Pl ℓ y ∂ν := by
  have hcomp : ∀ k, Integrable (fun y => Pl k (a y)) ν := fun k =>
    (ha.integrable_comp (hPl k).aestronglyMeasurable).2 (hPl k)
  have hsame : ∀ k, ∫ y, Pl k (a y) ∂ν = ∫ y, Pl k y ∂ν := fun k =>
    integral_comp_of_measurePreserving ha (hPl k).aestronglyMeasurable
  -- the mean of the antithetic average `½(P_k + P_k ∘ a)` is `E[P_k]`
  have havg : ∀ k, ∫ y, 2⁻¹ * (Pl k y + Pl k (a y)) ∂ν = ∫ y, Pl k y ∂ν := fun k => by
    rw [integral_const_mul, integral_add (hPl k) (hcomp k), hsame k]
    ring
  cases ℓ with
  | zero => exact havg 0
  | succ ℓ =>
    have hint : Integrable (fun y => 2⁻¹ * (Pl (ℓ + 1) y + Pl (ℓ + 1) (a y))) ν :=
      ((hPl (ℓ + 1)).add (hcomp (ℓ + 1))).const_mul 2⁻¹
    have e1 : ∫ y, antitheticDiff Pl a (ℓ + 1) y ∂ν =
        ∫ y, 2⁻¹ * (Pl (ℓ + 1) y + Pl (ℓ + 1) (a y)) ∂ν - ∫ y, Pl ℓ y ∂ν :=
      integral_sub hint (hPl ℓ)
    have e2 : ∫ y, levelDiff Pl (ℓ + 1) y ∂ν = ∫ y, Pl (ℓ + 1) y ∂ν - ∫ y, Pl ℓ y ∂ν :=
      integral_sub (hPl (ℓ + 1)) (hPl ℓ)
    rw [e1, e2, havg]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Giles' Theorem 1 for any level corrections satisfying condition ii)** (Giles 2015, §2.1,
Theorem 1 and p. 8: "the multilevel theorem allows for the use of other estimators, provided they
satisfy the restriction of condition ii) which ensures that `E[Y] = E[P_L]`").  Let the inputs
`ω (ℓ, n)` be mutually independent with law `ν`, and let `Δ_ℓ` be measurable, square-integrable
level corrections with `E[Δ_ℓ] = E[P_ℓ − P_{ℓ−1}]` (`P_{−1} ≡ 0`).  Let `cost ℓ n` be the cost of
the `n`-th level-`ℓ` sample, with mean `C ℓ`.  Under (i) `|E[P_ℓ − P]| ≤ c₁ 2^{−αℓ}`,
(iii) `V[Δ_ℓ] ≤ c₂ 2^{−βℓ}`, (iv) `C_ℓ ≤ c₃ 2^{γℓ}` with positive constants and
`α ≥ ½ min(β, γ)`, there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1`
for which `Y = ∑_{ℓ=0}^{L} N_ℓ⁻¹ ∑_{n<N_ℓ} Δ_ℓ(ω^{(ℓ,n)})` has `MSE < ε²` and
`E[C] ≤ c₄ ε⁻²`, `c₄ ε⁻² (log ε)²` or `c₄ ε^{−2−(γ−β)/α}` according as `β > γ`, `β = γ`, `β < γ`. -/
theorem giles_theorem1_corrections [IsProbabilityMeasure μ] (P : Ω₀ → ℝ) (Pl : ℕ → Ω₀ → ℝ)
    (Δ : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    (hP : Integrable P ν) (hPl : ∀ ℓ, Integrable (Pl ℓ) ν)
    (hΔm : ∀ ℓ, Measurable (Δ ℓ)) (hΔ : ∀ ℓ, MemLp (Δ ℓ) 2 ν)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (h_i : ∀ ℓ : ℕ, |∫ y, Pl ℓ y - P y ∂ν| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii : ∀ ℓ, ∫ y, Δ ℓ y ∂ν = ∫ y, levelDiff Pl ℓ y ∂ν)
    (h_iii : ∀ ℓ, variance (Δ ℓ) ν ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean Δ ω ℓ (N ℓ) x - ∫ y, P y ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * complexityBound α β γ ε := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  -- transport `P` and `P_ℓ` to `Ω` along the input `ω (0, 0)`
  have hφ := hω (0, 0)
  have tr : ∀ f : Ω₀ → ℝ, Integrable f ν → ∫ x, f (ω (0, 0) x) ∂μ = ∫ y, f y ∂ν :=
    fun f hf => integral_comp_of_measurePreserving hφ hf.aestronglyMeasurable
  have hPμ : Integrable (fun x => P (ω (0, 0) x)) μ :=
    (hφ.integrable_comp hP.aestronglyMeasurable).2 hP
  have hPlμ : ∀ ℓ, Integrable (fun x => Pl ℓ (ω (0, 0) x)) μ :=
    fun ℓ => (hφ.integrable_comp (hPl ℓ).aestronglyMeasurable).2 (hPl ℓ)
  have hΔ1 : ∀ ℓ, Integrable (Δ ℓ) ν := fun ℓ => (hΔ ℓ).integrable one_le_two
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1 (μ := μ) (fun x => P (ω (0, 0) x))
    (fun ℓ x => Pl ℓ (ω (0, 0) x)) (fun ℓ n => blockMean Δ ω ℓ n)
    (fun ℓ n x => ∑ k ∈ range n, cost ℓ k x) (fun ℓ => variance (Δ ℓ) ν) C
    hα hβ hγ hc₁ hc₂ hc₃ hαβγ hPμ hPlμ (fun ℓ n _ => memLp_blockMean hω hΔ ℓ n)
    (fun N _ i j hij => indepFun_blockMean (fun p => (hω p).measurable) hind hΔm hij _ _)
    (fun ℓ n _ => integrable_finsetSum _ fun k _ => hcost ℓ k)
    (fun ℓ n _ => by
      rw [integral_finsetSum _ fun k _ => hcost ℓ k]
      simp [hcostC])
    (fun ℓ => by
      dsimp only
      rw [tr (fun y => Pl ℓ y - P y) ((hPl ℓ).sub hP)]
      exact h_i ℓ)
    (fun n hn => by
      rw [integral_blockMean hω hΔ1 0 hn, h_ii 0, tr (Pl 0) (hPl 0), levelDiff_zero])
    (fun ℓ n hn => by
      dsimp only
      rw [integral_blockMean hω hΔ1 (ℓ + 1) hn, h_ii (ℓ + 1),
        tr (fun y => Pl (ℓ + 1) y - Pl ℓ y) ((hPl (ℓ + 1)).sub (hPl ℓ)), levelDiff_succ])
    (fun ℓ n hn => variance_blockMean hω hind hΔm hΔ ℓ hn) h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost'⟩ := h ε hε hε1
  refine ⟨L, N, hN, ?_, hcost'⟩
  rw [tr P hP] at hmse
  exact hmse

/-- **Theorem 1 for different fine and coarse approximations** (Giles 2015, §2.1, p. 8, (2.4) and
Theorem 1).  The multilevel estimator is
`Y = ∑_{ℓ=0}^{L} N_ℓ⁻¹ ∑_{n<N_ℓ} (P^f_ℓ − P^c_{ℓ−1})(ω^{(ℓ,n)})` with `P^c_{−1} ≡ 0`.  If the two
approximations satisfy (2.4), `E[P^f_ℓ] = E[P^c_ℓ]`, then under conditions (i) for `P^f_ℓ`, (iii)
for `V_ℓ = V[P^f_ℓ − P^c_{ℓ−1}]` and (iv), the conclusion of Theorem 1 holds (inputs, costs and
constants as in `giles_theorem1_corrections`). -/
theorem giles_theorem1_fineCoarse [IsProbabilityMeasure μ] (P : Ω₀ → ℝ) (Pf Pc : ℕ → Ω₀ → ℝ)
    (ω : ℕ × ℕ → Ω → Ω₀) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) (hP : Integrable P ν)
    (hPfm : ∀ ℓ, Measurable (Pf ℓ)) (hPcm : ∀ ℓ, Measurable (Pc ℓ))
    (hPf : ∀ ℓ, MemLp (Pf ℓ) 2 ν) (hPc : ∀ ℓ, MemLp (Pc ℓ) 2 ν)
    (h24 : ∀ ℓ, ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (h_i : ∀ ℓ : ℕ, |∫ y, Pf ℓ y - P y ∂ν| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, variance (fineCoarseDiff Pf Pc ℓ) ν ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf Pc) ω ℓ (N ℓ) x -
          ∫ y, P y ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * complexityBound α β γ ε := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  have hPf1 : ∀ ℓ, Integrable (Pf ℓ) ν := fun ℓ => (hPf ℓ).integrable one_le_two
  have hPc1 : ∀ ℓ, Integrable (Pc ℓ) ν := fun ℓ => (hPc ℓ).integrable one_le_two
  exact giles_theorem1_corrections P Pf (fineCoarseDiff Pf Pc) ω cost C hα hβ hγ hc₁ hc₂ hc₃
    hαβγ hω hind hP hPf1 (measurable_fineCoarseDiff hPfm hPcm) (memLp_fineCoarseDiff hPf hPc)
    hcost hcostC h_i (integral_fineCoarseDiff hPf1 hPc1 h24) h_iii h_iv

/-- **Theorem 1 for antithetic estimators** (Giles 2015, §2.1, p. 9, and Theorem 1).  The
multilevel estimator is
`Y = ∑_{ℓ=0}^{L} N_ℓ⁻¹ ∑_{n<N_ℓ} (½(P_ℓ(ω⁽ⁿ⁾) + P_ℓ(ω_a⁽ⁿ⁾)) − P_{ℓ−1}(ω⁽ⁿ⁾))` with
`ω⁽ⁿ⁾ = ω^{(ℓ,n)}`, `ω_a⁽ⁿ⁾ = a(ω^{(ℓ,n)})` for a measure-preserving `a` ("an antithetic `ω_a⁽ⁿ⁾`
with the same distribution as `ω⁽ⁿ⁾`") and `P_{−1} ≡ 0`.  Under conditions (i), (iii) for
`V_ℓ = V[½(P_ℓ + P_ℓ ∘ a) − P_{ℓ−1}]` and (iv), the conclusion of Theorem 1 holds (inputs, costs
and constants as in `giles_theorem1_corrections`). -/
theorem giles_theorem1_antithetic [IsProbabilityMeasure μ] (P : Ω₀ → ℝ) (Pl : ℕ → Ω₀ → ℝ)
    (a : Ω₀ → Ω₀) (ω : ℕ × ℕ → Ω → Ω₀) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    (ha : MeasurePreserving a ν ν) (hP : Integrable P ν)
    (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (h_i : ∀ ℓ : ℕ, |∫ y, Pl ℓ y - P y ∂ν| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, variance (antitheticDiff Pl a ℓ) ν ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (antitheticDiff Pl a) ω ℓ (N ℓ) x -
          ∫ y, P y ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * complexityBound α β γ ε := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  have hPl1 : ∀ ℓ, Integrable (Pl ℓ) ν := fun ℓ => (hPl ℓ).integrable one_le_two
  exact giles_theorem1_corrections P Pl (antitheticDiff Pl a) ω cost C hα hβ hγ hc₁ hc₂ hc₃
    hαβγ hω hind hP hPl1 (measurable_antitheticDiff ha.measurable hPlm)
    (memLp_antitheticDiff ha hPl) hcost hcostC h_i (integral_antitheticDiff ha hPl1) h_iii h_iv

end prob

end MLMC
