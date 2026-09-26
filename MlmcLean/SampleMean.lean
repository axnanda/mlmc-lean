import MlmcLean.StandardEstimator

/-!
# Monte Carlo averages over blocks of independent inputs

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §1.1 (p. 2 of the
author's version): "a simple Monte Carlo estimate is just an average of values `P(ω)` for `N`
independent samples … The variance of this estimate is `N⁻¹V[P]`"; §1.3 (p. 4): "independent
samples are used at each level of correction".

Every estimator in these papers is a sum of Monte Carlo averages, each over its own block of
independent random inputs.  `blockMean f ω i N` is the average of `f i` over the `N` inputs
`ω (i, 0), …, ω (i, N − 1)`.  For inputs that are mutually independent with law `ν`:

* `integral_blockMean` — the average is unbiased, `E = ∫ f i dν`;
* `variance_blockMean` — its variance is `V_ν[f i] / N`;
* `indepFun_blockMean` — averages over different blocks are independent.

The standard MLMC estimator (`MlmcLean/StandardEstimator.lean`) is the case `f = levelDiff Pl`;
the nested estimator of Haas and Giles (`MlmcLean/Nested.lean`) uses the index set
`levels × {low precision, correction}`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

section defs

variable {ι Ω₀ Ω : Type*}

/-- The Monte Carlo average `N⁻¹ ∑_{n<N} f_i(ω^{(i,n)})` of `f i` over the block of inputs
`ω (i, 0), …, ω (i, N−1)` (Giles 2015, §1.1, p. 2).  For `N = 0` it is `0`. -/
noncomputable def blockMean (f : ι → Ω₀ → ℝ) (ω : ι × ℕ → Ω → Ω₀) (i : ι) (N : ℕ) (x : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ range N, f i (ω (i, n) x)

end defs

section prob

variable {ι Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω} {f : ι → Ω₀ → ℝ} {ω : ι × ℕ → Ω → Ω₀}

lemma memLp_blockMean (hω : ∀ q, MeasurePreserving (ω q) μ ν) (hf : ∀ i, MemLp (f i) 2 ν)
    (i : ι) (N : ℕ) : MemLp (blockMean f ω i N) 2 μ :=
  (memLp_finsetSum _ fun n _ => (hf i).comp_measurePreserving (hω (i, n))).const_mul _

/-- A Monte Carlo average of `N ≥ 1` samples with law `ν` is unbiased (Giles 2015, §1.1). -/
lemma integral_blockMean [IsProbabilityMeasure μ] (hω : ∀ q, MeasurePreserving (ω q) μ ν)
    (hf : ∀ i, Integrable (f i) ν) (i : ι) {N : ℕ} (hN : 0 < N) :
    μ[blockMean f ω i N] = ∫ y, f i y ∂ν := by
  have hint : ∀ n, Integrable (fun x => f i (ω (i, n) x)) μ := fun n =>
    ((hω (i, n)).integrable_comp (hf i).aestronglyMeasurable).2 (hf i)
  have hterm : ∀ n, ∫ x, f i (ω (i, n) x) ∂μ = ∫ y, f i y ∂ν := fun n =>
    integral_comp_of_measurePreserving (hω (i, n)) (hf i).aestronglyMeasurable
  simp only [blockMean]
  rw [integral_const_mul, integral_finsetSum _ fun n _ => hint n]
  simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [← mul_assoc, inv_mul_cancel₀ hN', one_mul]

/-- The variance of a Monte Carlo average of `N ≥ 1` independent samples with law `ν` is
`V_ν[f i] / N` (Giles 2015, §1.1, p. 2). -/
lemma variance_blockMean [IsProbabilityMeasure μ] (hω : ∀ q, MeasurePreserving (ω q) μ ν)
    (hind : iIndepFun ω μ) (hfm : ∀ i, Measurable (f i)) (hf : ∀ i, MemLp (f i) 2 ν)
    (i : ι) {N : ℕ} (hN : 0 < N) :
    variance (blockMean f ω i N) μ = variance (f i) ν / N := by
  have hX : iIndepFun (fun q : ι × ℕ => f q.1 ∘ ω q) μ :=
    hind.comp (fun q => f q.1) (fun q => hfm q.1)
  exact variance_sample_mean (fun n x => f i (ω (i, n) x)) N hN _
    (fun n => (hf i).comp_measurePreserving (hω (i, n)))
    (fun n => (hω (i, n)).variance_fun_comp (hfm i).aemeasurable)
    (fun a _ b _ hab => hX.indepFun (i := (i, a)) (j := (i, b)) (by simpa using hab))

omit [MeasurableSpace Ω₀] [MeasurableSpace Ω] in
/-- The block average over block `k` is a function of the inputs `ω (k, 0), …, ω (k, M − 1)`. -/
lemma blockMean_eq_comp (f : ι → Ω₀ → ℝ) (ω : ι × ℕ → Ω → Ω₀) (k : ι) (M : ℕ) :
    blockMean f ω k M =
      (fun t : ({k} ×ˢ range M : Finset (ι × ℕ)) → Ω₀ =>
        (M : ℝ)⁻¹ * ∑ p : ({k} ×ˢ range M : Finset (ι × ℕ)), f k (t p)) ∘
      (fun x (p : ({k} ×ˢ range M : Finset (ι × ℕ))) => ω p x) := by
  funext x
  simp only [blockMean, Function.comp_apply]
  congr 1
  rw [Finset.sum_coe_sort (s := {k} ×ˢ range M) (f := fun p => f k (ω p x)),
    Finset.sum_product, Finset.sum_singleton]

/-- Averages over different blocks of mutually independent inputs are independent (Giles 2015,
§1.3, p. 4: "independent samples are used at each level of correction"). -/
lemma indepFun_blockMean (hωm : ∀ q, Measurable (ω q)) (hind : iIndepFun ω μ)
    (hfm : ∀ i, Measurable (f i)) {i j : ι} (hij : i ≠ j) (Ni Nj : ℕ) :
    IndepFun (blockMean f ω i Ni) (blockMean f ω j Nj) μ := by
  have hST : Disjoint ({i} ×ˢ range Ni) ({j} ×ˢ range Nj) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton] at h1 h2
    exact hij (h1.1.symm.trans h2.1)
  have hmeas : ∀ (k : ι) (M : ℕ), Measurable fun t : ({k} ×ˢ range M : Finset (ι × ℕ)) → Ω₀ =>
      (M : ℝ)⁻¹ * ∑ p : ({k} ×ˢ range M : Finset (ι × ℕ)), f k (t p) :=
    fun k M => Measurable.const_mul (Finset.measurable_sum _ fun p _ =>
      (hfm k).comp (measurable_pi_apply p)) _
  rw [blockMean_eq_comp f ω i Ni, blockMean_eq_comp f ω j Nj]
  exact (hind.indepFun_finset _ _ hST hωm).comp (hmeas i Ni) (hmeas j Nj)

end prob

end MLMC
