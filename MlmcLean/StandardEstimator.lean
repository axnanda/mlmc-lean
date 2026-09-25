import MlmcLean.Theorem1
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure

/-!
# The standard multilevel Monte Carlo estimator, built from independent samples

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §1.3 (p. 4)
and §2.1, eq. (2.2)–(2.3) and Theorem 1.

`MlmcLean/Theorem1.lean` proves Theorem 1 for *any* family of estimators satisfying its
hypotheses.  This file constructs the estimator Giles actually uses,

  `Y = ∑_{ℓ=0}^{L} Y_ℓ`,  `Y_ℓ = N_ℓ⁻¹ ∑_{n=1}^{N_ℓ} (P_ℓ^{(ℓ,n)} − P_{ℓ−1}^{(ℓ,n)})`,  `P_{−1} ≡ 0`,  (2.2)

where the `n`-th sample on level `ℓ` evaluates the fine and the coarse approximation on the same
random input `ω^{(ℓ,n)}`, and "independent samples are used at each level of correction" (p. 4).
From the independence and the common law of the inputs we *derive* the hypotheses of Theorem 1 —
unbiasedness (ii), `V[Y_ℓ] = N_ℓ⁻¹ V_ℓ` with `V_ℓ = V[P_ℓ − P_{ℓ−1}]` (2.3), and independence
across levels — and obtain Theorem 1 for this estimator (`giles_theorem1_standard`).
`giles_theorem1_iid` removes the last assumption: on the infinite product space `Ω₀^{ℕ×ℕ}` the
coordinate maps are independent inputs, so the statement there assumes nothing about independence.

**Setting.**  `(Ω₀, ν)` is the probability space of one random input (for an SDE, a Brownian
path); `Pl ℓ : Ω₀ → ℝ` is the level-`ℓ` approximation and `P : Ω₀ → ℝ` the quantity of
interest.  The simulation runs on a probability space `(Ω, μ)` carrying the inputs
`ω (ℓ, n) : Ω → Ω₀`, which are mutually independent and each distributed as `ν`.  The cost of the
`n`-th sample on level `ℓ` is a random variable `cost ℓ n` with mean `C ℓ`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

section defs

variable {Ω₀ Ω : Type*}

/-- The level-`ℓ` correction `ΔP_ℓ = P_ℓ − P_{ℓ−1}`, with `P_{−1} ≡ 0` (Giles 2015, (2.2)). -/
noncomputable def levelDiff (Pl : ℕ → Ω₀ → ℝ) : ℕ → Ω₀ → ℝ
  | 0 => Pl 0
  | ℓ + 1 => fun y => Pl (ℓ + 1) y - Pl ℓ y

@[simp] lemma levelDiff_zero (Pl : ℕ → Ω₀ → ℝ) : levelDiff Pl 0 = Pl 0 := rfl

@[simp] lemma levelDiff_succ (Pl : ℕ → Ω₀ → ℝ) (ℓ : ℕ) :
    levelDiff Pl (ℓ + 1) = fun y => Pl (ℓ + 1) y - Pl ℓ y := rfl

/-- Giles (2.2): the level-`ℓ` estimator with `N` samples,
`Y_ℓ = N⁻¹ ∑_{n<N} (P_ℓ − P_{ℓ−1})(ω^{(ℓ,n)})`. -/
noncomputable def levelEstimator (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (ℓ N : ℕ) (x : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ range N, levelDiff Pl ℓ (ω (ℓ, n) x)

/-- Giles (2.2): the multilevel estimator `Y = ∑_{ℓ=0}^{L} Y_ℓ` with `N ℓ` samples on level `ℓ`. -/
noncomputable def mlmcEstimator (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (L : ℕ) (N : ℕ → ℕ)
    (x : Ω) : ℝ :=
  ∑ ℓ ∈ range (L + 1), levelEstimator Pl ω ℓ (N ℓ) x

/-- The total computational cost `C = ∑_{ℓ=0}^{L} ∑_{n<N_ℓ} cost ℓ n` of the multilevel
estimator, where `cost ℓ n` is the cost of the `n`-th sample on level `ℓ`. -/
noncomputable def totalCost (cost : ℕ → ℕ → Ω → ℝ) (L : ℕ) (N : ℕ → ℕ) (x : Ω) : ℝ :=
  ∑ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ), cost ℓ n x

end defs

section prob

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω} {Pl : ℕ → Ω₀ → ℝ} {ω : ℕ × ℕ → Ω → Ω₀}

lemma measurable_levelDiff (hPl : ∀ ℓ, Measurable (Pl ℓ)) : ∀ ℓ, Measurable (levelDiff Pl ℓ)
  | 0 => hPl 0
  | ℓ + 1 => (hPl (ℓ + 1)).sub (hPl ℓ)

lemma memLp_levelDiff (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν) : ∀ ℓ, MemLp (levelDiff Pl ℓ) 2 ν
  | 0 => hPl 0
  | ℓ + 1 => (hPl (ℓ + 1)).sub (hPl ℓ)

/-- Integrals transport along a measure-preserving map. -/
lemma integral_comp_of_measurePreserving {φ : Ω → Ω₀} (hφ : MeasurePreserving φ μ ν)
    {f : Ω₀ → ℝ} (hf : AEStronglyMeasurable f ν) : ∫ x, f (φ x) ∂μ = ∫ y, f y ∂ν := by
  rw [← hφ.map_eq] at hf ⊢
  exact (integral_map hφ.measurable.aemeasurable hf).symm

lemma memLp_sample (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    (ℓ n : ℕ) : MemLp (fun x => levelDiff Pl ℓ (ω (ℓ, n) x)) 2 μ :=
  (memLp_levelDiff hPl ℓ).comp_measurePreserving (hω (ℓ, n))

lemma memLp_levelEstimator (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν) (ℓ N : ℕ) : MemLp (levelEstimator Pl ω ℓ N) 2 μ :=
  (memLp_finsetSum _ fun n _ => memLp_sample hω hPl ℓ n).const_mul _

/-- Condition (ii) of Theorem 1 holds for the estimator (2.2): `E[Y_ℓ] = E[P_ℓ − P_{ℓ−1}]`. -/
lemma integral_levelEstimator [IsProbabilityMeasure μ] (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν) (ℓ : ℕ) {N : ℕ} (hN : 0 < N) :
    μ[levelEstimator Pl ω ℓ N] = ∫ y, levelDiff Pl ℓ y ∂ν := by
  have hterm : ∀ n, ∫ x, levelDiff Pl ℓ (ω (ℓ, n) x) ∂μ = ∫ y, levelDiff Pl ℓ y ∂ν := fun n =>
    integral_comp_of_measurePreserving (hω (ℓ, n)) (measurable_levelDiff hPlm ℓ).aestronglyMeasurable
  simp only [levelEstimator]
  rw [integral_const_mul, integral_finsetSum _ fun n _ =>
    (memLp_sample hω hPl ℓ n).integrable one_le_two]
  simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [← mul_assoc, inv_mul_cancel₀ hN', one_mul]

/-- Giles (2.3): `V[Y_ℓ] = N_ℓ⁻¹ V_ℓ` with `V_ℓ = V[P_ℓ − P_{ℓ−1}]`, for independent inputs. -/
lemma variance_levelEstimator [IsProbabilityMeasure μ] (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    (ℓ : ℕ) {N : ℕ} (hN : 0 < N) :
    variance (levelEstimator Pl ω ℓ N) μ = variance (levelDiff Pl ℓ) ν / N := by
  have hX : iIndepFun (fun p : ℕ × ℕ => levelDiff Pl p.1 ∘ ω p) μ :=
    hind.comp (fun p => levelDiff Pl p.1) (fun p => measurable_levelDiff hPlm p.1)
  exact variance_sample_mean (fun n x => levelDiff Pl ℓ (ω (ℓ, n) x)) N hN _
    (fun n => memLp_sample hω hPl ℓ n)
    (fun n => (hω (ℓ, n)).variance_fun_comp (measurable_levelDiff hPlm ℓ).aemeasurable)
    (fun a _ b _ hab => hX.indepFun (i := (ℓ, a)) (j := (ℓ, b)) (by simpa using hab))

/-- The level-`i` block of samples `ω^{(i,0)}, …, ω^{(i,M-1)}` as one random variable. -/
lemma levelEstimator_eq_comp (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (k M : ℕ) :
    levelEstimator Pl ω k M =
      (fun t : ({k} ×ˢ range M : Finset (ℕ × ℕ)) → Ω₀ =>
        (M : ℝ)⁻¹ * ∑ p : ({k} ×ˢ range M : Finset (ℕ × ℕ)), levelDiff Pl k (t p)) ∘
      (fun x (p : ({k} ×ˢ range M : Finset (ℕ × ℕ))) => ω p x) := by
  funext x
  simp only [levelEstimator, Function.comp_apply]
  congr 1
  rw [Finset.sum_coe_sort (s := {k} ×ˢ range M) (f := fun p => levelDiff Pl k (ω p x)),
    Finset.sum_product, Finset.sum_singleton]

/-- "Independent samples are used at each level of correction" (Giles 2015, p. 4): estimators on
different levels use disjoint blocks of the independent inputs, hence are independent. -/
lemma indepFun_levelEstimator (hωm : ∀ p, Measurable (ω p)) (hind : iIndepFun ω μ)
    (hPlm : ∀ ℓ, Measurable (Pl ℓ)) {i j : ℕ} (hij : i ≠ j) (Ni Nj : ℕ) :
    IndepFun (levelEstimator Pl ω i Ni) (levelEstimator Pl ω j Nj) μ := by
  have hST : Disjoint ({i} ×ˢ range Ni) ({j} ×ˢ range Nj) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton] at h1 h2
    exact hij (h1.1.symm.trans h2.1)
  have hmeas : ∀ k M : ℕ, Measurable fun t : ({k} ×ˢ range M : Finset (ℕ × ℕ)) → Ω₀ =>
      (M : ℝ)⁻¹ * ∑ p : ({k} ×ˢ range M : Finset (ℕ × ℕ)), levelDiff Pl k (t p) :=
    fun k M => Measurable.const_mul (Finset.measurable_sum _ fun p _ =>
      (measurable_levelDiff hPlm k).comp (measurable_pi_apply p)) _
  rw [levelEstimator_eq_comp Pl ω i Ni, levelEstimator_eq_comp Pl ω j Nj]
  exact (hind.indepFun_finset _ _ hST hωm).comp (hmeas i Ni) (hmeas j Nj)

/-- **Giles' Theorem 1 for the standard estimator (2.2)** (Giles 2015, §2.1, Theorem 1).
Let the inputs `ω (ℓ, n)` be mutually independent with law `ν`, and let `cost ℓ n` be the cost of
the `n`-th level-`ℓ` sample, with mean `C ℓ`.  Assume the level approximations `Pl ℓ` are
measurable and square-integrable and, with `V_ℓ = V[P_ℓ − P_{ℓ−1}]`,

  (i)   `|E[P_ℓ − P]| ≤ c₁ 2^{−αℓ}`,   (iii) `V_ℓ ≤ c₂ 2^{−βℓ}`,   (iv) `C_ℓ ≤ c₃ 2^{γℓ}`,

for positive `α, β, γ, c₁, c₂, c₃` with `α ≥ ½ min(β,γ)`; condition (ii) holds automatically.
Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which
the estimator (2.2) satisfies `E[(Y − E[P])²] < ε²` and `E[C] ≤ c₄ ε⁻²`, `c₄ ε⁻² (log ε)²` or
`c₄ ε^{−2−(γ−β)/α}` according as `β > γ`, `β = γ` or `β < γ`. -/
theorem giles_theorem1_standard [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : Ω₀ → ℝ) (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    (hP : Integrable P ν) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (h_i : ∀ ℓ : ℕ, |∫ y, Pl ℓ y - P y ∂ν| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, variance (levelDiff Pl ℓ) ν ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (mlmcEstimator Pl ω L N x - ∫ y, P y ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * complexityBound α β γ ε := by
  -- transport `P` and `P_ℓ` to `Ω` along the input `ω (0, 0)`
  have hφ := hω (0, 0)
  have hPl1 : ∀ ℓ, Integrable (Pl ℓ) ν := fun ℓ => (hPl ℓ).integrable one_le_two
  have tr : ∀ f : Ω₀ → ℝ, Integrable f ν → ∫ x, f (ω (0, 0) x) ∂μ = ∫ y, f y ∂ν :=
    fun f hf => integral_comp_of_measurePreserving hφ hf.aestronglyMeasurable
  have hPμ : Integrable (fun x => P (ω (0, 0) x)) μ :=
    (hφ.integrable_comp hP.aestronglyMeasurable).2 hP
  have hPlμ : ∀ ℓ, Integrable (fun x => Pl ℓ (ω (0, 0) x)) μ :=
    fun ℓ => (hφ.integrable_comp (hPl1 ℓ).aestronglyMeasurable).2 (hPl1 ℓ)
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1 (μ := μ) (fun x => P (ω (0, 0) x))
    (fun ℓ x => Pl ℓ (ω (0, 0) x)) (fun ℓ n => levelEstimator Pl ω ℓ n)
    (fun ℓ n x => ∑ k ∈ range n, cost ℓ k x) (fun ℓ => variance (levelDiff Pl ℓ) ν) C
    hα hβ hγ hc₁ hc₂ hc₃ hαβγ hPμ hPlμ (fun ℓ n => memLp_levelEstimator hω hPl ℓ n)
    (fun N _ i j hij => indepFun_levelEstimator (fun p => (hω p).measurable) hind hPlm hij _ _)
    (fun ℓ n _ => integrable_finsetSum _ fun k _ => hcost ℓ k)
    (fun ℓ n _ => by
      dsimp only
      rw [integral_finsetSum _ fun k _ => hcost ℓ k]
      simp [hcostC])
    (fun ℓ => by
      dsimp only
      rw [tr (fun y => Pl ℓ y - P y) ((hPl1 ℓ).sub hP)]
      exact h_i ℓ)
    (fun n hn => by
      dsimp only
      rw [integral_levelEstimator hω hPlm hPl 0 hn, tr (Pl 0) (hPl1 0), levelDiff_zero])
    (fun ℓ n hn => by
      dsimp only
      rw [integral_levelEstimator hω hPlm hPl (ℓ + 1) hn,
        tr (fun y => Pl (ℓ + 1) y - Pl ℓ y) ((hPl1 (ℓ + 1)).sub (hPl1 ℓ)), levelDiff_succ])
    (fun ℓ n hn => variance_levelEstimator hω hind hPlm hPl ℓ hn) h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost'⟩ := h ε hε hε1
  refine ⟨L, N, hN, ?_, hcost'⟩
  rw [tr P hP] at hmse
  exact hmse

/-- Independent inputs exist for every input distribution: on the infinite product space
`Ω₀^{ℕ×ℕ}` with the product measure `ν^{⊗(ℕ×ℕ)}`, the coordinate maps are mutually independent,
each with law `ν`.  So the hypotheses of `giles_theorem1_standard` are never vacuous. -/
theorem exists_iid_inputs (ν : Measure Ω₀) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ × ℕ => ν) ∧
      iIndepFun (fun (p : ℕ × ℕ) (x : ℕ × ℕ → Ω₀) => x p) (Measure.infinitePi fun _ => ν) ∧
      ∀ p, MeasurePreserving (fun x : ℕ × ℕ → Ω₀ => x p) (Measure.infinitePi fun _ => ν) ν :=
  ⟨inferInstance,
    iIndepFun_infinitePi (P := fun _ : ℕ × ℕ => ν) (X := fun _ => id) (fun _ => measurable_id),
    fun p => measurePreserving_eval_infinitePi (fun _ : ℕ × ℕ => ν) p⟩

/-- **Giles' Theorem 1 for the standard estimator with independent samples** (Giles 2015, §2.1,
Theorem 1 and (2.2)).  Only the input distribution `ν`, the level approximations `P_ℓ` and the
per-sample cost functions `κ_ℓ` are given; the independent samples are the coordinates of the
infinite product space `(Ω₀^{ℕ×ℕ}, ν^{⊗(ℕ×ℕ)})`, the `n`-th level-`ℓ` sample costs `κ_ℓ(ω^{(ℓ,n)})`,
and `C_ℓ = E[κ_ℓ]`.  Under (i), (iii), (iv) with `α ≥ ½ min(β,γ)` there is `c₄ > 0` such that for
every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with `MSE < ε²` and `E[C] ≤ c₄ · bound(ε)`. -/
theorem giles_theorem1_iid (ν : Measure Ω₀) [IsProbabilityMeasure ν]
    (P : Ω₀ → ℝ) (Pl : ℕ → Ω₀ → ℝ) (κ : ℕ → Ω₀ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hP : Integrable P ν) (hPlm : ∀ ℓ, Measurable (Pl ℓ)) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    (hκ : ∀ ℓ, Integrable (κ ℓ) ν)
    (h_i : ∀ ℓ : ℕ, |∫ y, Pl ℓ y - P y ∂ν| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, variance (levelDiff Pl ℓ) ν ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, ∫ y, κ ℓ y ∂ν ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        ∫ x, (mlmcEstimator Pl (fun p x => x p) L N x - ∫ y, P y ∂ν) ^ 2
          ∂(Measure.infinitePi fun _ => ν) < ε ^ 2 ∧
        ∫ x, totalCost (fun ℓ n x => κ ℓ (x (ℓ, n))) L N x ∂(Measure.infinitePi fun _ => ν)
          ≤ c₄ * complexityBound α β γ ε := by
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs ν
  exact giles_theorem1_standard (μ := Measure.infinitePi fun _ => ν) P Pl (fun p x => x p)
    (fun ℓ n x => κ ℓ (x (ℓ, n))) (fun ℓ => ∫ y, κ ℓ y ∂ν) hα hβ hγ hc₁ hc₂ hc₃ hαβγ hω hind hP
    hPlm hPl (fun ℓ n => ((hω (ℓ, n)).integrable_comp (hκ ℓ).aestronglyMeasurable).2 (hκ ℓ))
    (fun ℓ n => integral_comp_of_measurePreserving (hω (ℓ, n)) (hκ ℓ).aestronglyMeasurable)
    h_i h_iii h_iv

end prob

end MLMC
