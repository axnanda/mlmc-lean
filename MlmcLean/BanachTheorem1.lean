import MlmcLean.MultiOutput
import MlmcLean.StandardEstimator
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Theorem 1 for outputs in a Banach space of type 2 (Giles 2015, §2.5)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.5,
pp. 17–18 (l. 776–787 of `docs/giles2015.txt`).  For norms other than the 2-norm "the variance
for the combined multilevel estimator can not necessarily be expressed in the usual form as
`∑_ℓ N_ℓ⁻¹ V_ℓ` … Nevertheless, the theory can be extended to the use of other norms by using
results from Banach space theory for the sums of independent random variables (Ledoux and
Talagrand 1991, Heinrich 1998)".

**The Banach-space input is an assumption.**  The result of Banach space theory that is needed
is the *type-2 inequality* for sums of independent random variables.  Type and cotype theory
(Rademacher averages, the Kahane–Khintchine inequalities, symmetrisation) is not in Mathlib, so
the inequality is taken as a hypothesis on the space: `HasType2.{u} E τ` says that for all
mutually independent, square-integrable, mean-zero `E`-valued random variables `X_0, …, X_{n−1}`
on any probability space `Ω : Type u`,

  `E‖∑_i X_i‖² ≤ τ² ∑_i E‖X_i‖²`.

(A Banach space has Rademacher type 2 with constant `T` iff this holds with some `τ`; by
symmetrisation `τ ≤ 2T`.  The predicate depends on a universe level because it quantifies over
probability spaces; mathematically it does not depend on the level, and the results below assume
it at the universe of the simulation space.)

**Setting.**  `E` is a real Banach space with its Borel σ-algebra; `(Ω₀, ν)` is the space of one
random input, `Pl ℓ : Ω₀ → E` the level-`ℓ` approximation, `P : Ω₀ → E` the quantity of
interest; the inputs `ω^{(ℓ,n)} : Ω → Ω₀` are mutually independent with law `ν`.  The estimator
is Giles' (2.2), `Y = ∑_{ℓ=0}^{L} N_ℓ⁻¹ ∑_{n<N_ℓ} ΔP_ℓ(ω^{(ℓ,n)})`, `ΔP_ℓ = P_ℓ − P_{ℓ−1}`,
`P_{−1} ≡ 0` (`vecMlmcEstimator`, `vecLevelDiff`), and `V_ℓ = E‖ΔP_ℓ − E[ΔP_ℓ]‖²` is the
substitute for the variance given in the paper.

**Results.**
* `mlmc_mse_le_of_hasType2`: under type 2 with constant `τ`,
  `E‖Y − m‖² ≤ 2 (τ² ∑_{ℓ=0}^{L} V_ℓ/N_ℓ + ‖E[P_L] − m‖²)` for every `m ∈ E`.  The factor `τ²`
  comes from the type-2 inequality applied to all `∑_ℓ N_ℓ` centred samples at once; the
  factor `2` from `‖z + b‖² ≤ 2‖z‖² + 2‖b‖²`, since in a Banach space the cross term between
  the random error and the bias does not vanish.
* `giles_theorem1_banach`: Theorem 1 in a type-2 Banach space: under (i)
  `‖E[P_ℓ − P]‖ ≤ c₁ 2^{−αℓ}`, (iii) `V_ℓ ≤ c₂ 2^{−βℓ}`, (iv) `C_ℓ ≤ c₃ 2^{γℓ}` and
  `α ≥ ½ min(β, γ)`, there is `c₄` such that for `0 < ε < e⁻¹` some `L`, `N_ℓ ≥ 1` give
  `E‖Y − E[P]‖² < ε²` at expected cost `≤ c₄ · complexityBound α β γ ε`.  It reuses the
  deterministic core `mlmc_complexity_core` of Theorem 1 with the constants `2c₁` and
  `2(τ² + 1)c₂`.
* `hasType2_of_innerProductSpace`: every real Hilbert space has type 2 with `τ = 1` (from the
  Pythagoras identity `integral_norm_sum_sq_of_indepFun`), so the hypothesis is satisfiable and
  the results apply to every Hilbert space (for the standard estimator (2.2);
  `giles_theorem1_hilbert` treats abstract level estimators, with the exact MSE identity).
* `hasType2_of_isomorphic_embedding`: a space with a linear embedding `a‖x‖ ≤ ‖Tx‖ ≤ b‖x‖` into a
  Hilbert space has type 2 with `τ = b/a`; hence every finite-dimensional normed space has type 2
  (`exists_hasType2_of_finiteDimensional`), for instance `ℝ × ℝ` with the maximum norm
  (`exists_hasType2_prod`; with `τ = √2`, `hasType2_prod_sqrt_two`, which is the best constant, not
  formalised), where the 2-norm identity fails (`sq_norm_add_of_indepFun_fails_sup`).  So Theorem 1
  holds for finitely many outputs measured in any norm, e.g. the maximum error over the outputs.

**Deviations from the paper.**  The paper gives no statement for other norms, only the pointer
to Banach space theory; the statements here are one way to make it precise.  Type 2 is a
hypothesis of the main results; it is proved here only for spaces isomorphic to a subspace of a
Hilbert space (all finite-dimensional spaces among them).  Independence is mutual
(`iIndepFun`), as the type-2 inequality requires, not pairwise as in the Hilbert-space case.  The
MSE bound carries the factor `2` above, even in a Hilbert space (where `mlmc_mse_hilbert` gives
the exact identity).  The `P_ℓ` are only assumed square-integrable (`MemLp`, which includes a.e.
strong measurability); Borel measurability of the `P_ℓ` is not needed.

**Not proved.**  No infinite-dimensional space that is not isomorphic to a Hilbert space is shown
to have type 2 (e.g. `L^p`, `2 < p < ∞`: this needs the Khintchine–Kahane inequalities, absent
from Mathlib; the sup norm of `C([0,1])` has no type 2), and neither the type-`p`
versions (`1 < p < 2`, where the `p`-th moment of the error of `N` samples decays like `N^{1−p}`)
nor the Daun–Heinrich parametric-integration results cited on p. 18 are formalised.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

universe u v

/-! ### Type 2 -/

/-- **Type 2 for sums of independent random variables**, the assumption standing for the
"results from Banach space theory for the sums of independent random variables" of Giles 2015,
§2.5, pp. 17–18, l. 782–787.  `HasType2.{u} E τ` holds if on every probability space `(Ω, μ)`
with `Ω : Type u`, for every `n` and all mutually independent, square-integrable, mean-zero
random variables `X_0, …, X_{n−1}` with values in the real Banach space `E`,
`E‖∑_i X_i‖² ≤ τ² ∑_i E‖X_i‖²`.  In a Hilbert space this holds with `τ = 1` and equality;
in general it is an assumption on `E` (type and cotype theory is not in Mathlib).  Assume it at
the universe `u` of the simulation space; mathematically the property does not depend on `u`. -/
def HasType2 (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] (τ : ℝ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin n → Ω → E), iIndepFun X μ → (∀ i, MemLp (X i) 2 μ) →
    (∀ i, ∫ ω, X i ω ∂μ = 0) →
    ∫ ω, ‖∑ i, X i ω‖ ^ 2 ∂μ ≤ τ ^ 2 * ∑ i, ∫ ω, ‖X i ω‖ ^ 2 ∂μ

/-- The type-2 inequality for a finite subfamily `(X_i)_{i ∈ s}` of an independent family with
any index type (the form in which Giles 2015, §2.5, p. 18 uses it):
`E‖∑_{i∈s} X_i‖² ≤ τ² ∑_{i∈s} E‖X_i‖²`. -/
lemma HasType2.integral_norm_sum_sq_le {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {τ : ℝ} (hE : HasType2.{u} E τ) {Ω : Type u}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι)
    {X : ι → Ω → E} (hind : iIndepFun X μ) (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hX0 : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    ∫ ω, ‖∑ i ∈ s, X i ω‖ ^ 2 ∂μ ≤ τ ^ 2 * ∑ i ∈ s, ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
  classical
  let g : Fin s.card → ι := fun k => (s.equivFin.symm k : ι)
  have hg : Function.Injective g := Subtype.val_injective.comp s.equivFin.symm.injective
  have hmem : ∀ k, g k ∈ s := fun k => (s.equivFin.symm k).2
  have h := hE Ω μ s.card (fun k => X (g k)) (hind.precomp hg) (fun k => hX _ (hmem k))
    (fun k => hX0 _ (hmem k))
  have hreE : ∀ ω, ∑ k, X (g k) ω = ∑ i ∈ s, X i ω := fun ω => by
    rw [← Finset.sum_coe_sort s]
    exact Equiv.sum_comp s.equivFin.symm (fun i : s => X i ω)
  have hreR : ∑ k, ∫ ω, ‖X (g k) ω‖ ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
    rw [← Finset.sum_coe_sort s]
    exact Equiv.sum_comp s.equivFin.symm (fun i : s => ∫ ω, ‖X i ω‖ ^ 2 ∂μ)
  rw [hreR] at h
  simpa only [hreE] using h

/-- **Every real Hilbert space has type 2 with constant `1`** (Giles 2015, §2.5, p. 17: "when
using the 2-norm, this extends to independent random vectors `a` and `b`, each with zero mean,
since `E[‖a+b‖²] = E[‖a‖²] + E[‖b‖²]`, and similarly to random functions with a 2-norm based on
an inner product"; l. 772–775).  So `HasType2` is satisfiable, and the type-2 results below
contain the Hilbert-space case. -/
theorem hasType2_of_innerProductSpace {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] :
    HasType2.{u} F 1 := by
  intro Ω _ μ _ n X hind hX hX0
  rw [one_pow, one_mul]
  exact (integral_norm_sum_sq_of_indepFun univ (fun i _ => hX i) (fun i _ => hX0 i)
    (fun i _ j _ hij => hind.indepFun hij)).le

/-- **Spaces isomorphic to a subspace of a Hilbert space have type 2** (Giles 2015, §2.5,
pp. 17–18, l. 776–787: the 2-norm identity "does not necessarily apply for other norms.
Nevertheless, the theory can be extended to the use of other norms by using results from Banach
space theory").  If a continuous linear map `T : E → F` into a real Hilbert space satisfies
`a‖x‖ ≤ ‖T x‖ ≤ b‖x‖` with `a > 0`, then `E` has type 2 with constant `b / a`. -/
theorem hasType2_of_isomorphic_embedding {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    (T : E →L[ℝ] F) {a b : ℝ} (ha : 0 < a) (hlow : ∀ x, a * ‖x‖ ≤ ‖T x‖)
    (hup : ∀ x, ‖T x‖ ≤ b * ‖x‖) : HasType2.{u} E (b / a) := by
  intro Ω _ μ _ n X hind hX hX0
  have hY : ∀ i, MemLp (fun ω => T (X i ω)) 2 μ := fun i => T.comp_memLp' (hX i)
  have hYind : iIndepFun (fun i ω => T (X i ω)) μ :=
    hind.comp (fun _ => T) (fun _ => T.continuous.measurable)
  have hY0 : ∀ i, ∫ ω, T (X i ω) ∂μ = 0 := fun i => by
    rw [T.integral_comp_comm ((hX i).integrable one_le_two), hX0 i, map_zero]
  have hpyth := integral_norm_sum_sq_of_indepFun (μ := μ) univ (X := fun i ω => T (X i ω))
    (fun i _ => hY i) (fun i _ => hY0 i) (fun i _ j _ hij => hYind.indepFun hij)
  have hS : MemLp (fun ω => ∑ i, X i ω) 2 μ := memLp_finsetSum univ fun i _ => hX i
  have hTS : MemLp (fun ω => ∑ i, T (X i ω)) 2 μ := memLp_finsetSum univ fun i _ => hY i
  have h1 : a ^ 2 * ∫ ω, ‖∑ i, X i ω‖ ^ 2 ∂μ ≤ ∫ ω, ‖∑ i, T (X i ω)‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono (hS.norm.integrable_sq.const_mul _) hTS.norm.integrable_sq fun ω => ?_
    dsimp only
    rw [← map_sum T (fun i => X i ω) univ, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (hlow _) 2
  have h2 : ∀ i, ∫ ω, ‖T (X i ω)‖ ^ 2 ∂μ ≤ b ^ 2 * ∫ ω, ‖X i ω‖ ^ 2 ∂μ := fun i => by
    rw [← integral_const_mul]
    refine integral_mono (hY i).norm.integrable_sq ((hX i).norm.integrable_sq.const_mul _)
      fun ω => ?_
    dsimp only
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hup _) 2
  rw [hpyth] at h1
  have h3 := Finset.sum_le_sum fun i (_ : i ∈ univ) => h2 i
  rw [← Finset.mul_sum] at h3
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- **Every finite-dimensional real normed space has type 2** (Giles 2015, §2.5, pp. 17–18,
l. 776–787: for "other norms" the theory "can be extended … by using results from Banach space
theory for the sums of independent random variables").  This covers finitely many outputs with
any norm, e.g. the maximum norm, for which the 2-norm identity of l. 772–775 fails
(`sq_norm_add_of_indepFun_fails_sup`).  (Completeness is automatic in finite dimension.) -/
theorem exists_hasType2_of_finiteDimensional {E : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] : ∃ τ, HasType2.{u} E τ := by
  let T : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let Tl : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := T
  let Ts : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E := T.symm
  have ha : 0 < (‖Ts‖ + 1)⁻¹ := inv_pos.2 (by positivity)
  refine ⟨‖Tl‖ / (‖Ts‖ + 1)⁻¹, hasType2_of_isomorphic_embedding Tl ha (fun x => ?_)
    (fun x => Tl.le_opNorm x)⟩
  have h := Ts.le_opNorm (Tl x)
  have hx : Ts (Tl x) = x := T.symm_apply_apply x
  rw [hx] at h
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (Tl x)]

/-- **A non-Hilbert norm of type 2: `ℝ × ℝ` with the maximum norm** (Giles 2015, §2.5, pp. 17–18,
l. 776–787: "However this does not necessarily apply for other norms … Nevertheless, the theory
can be extended to the use of other norms").  Mathlib's norm on `ℝ × ℝ` is
`‖(x, y)‖ = max |x| |y|`; the 2-norm identity fails for it
(`sq_norm_add_of_indepFun_fails_sup`), but it has type 2, so `giles_theorem1_banach` applies to
it. -/
theorem exists_hasType2_prod : ∃ τ, HasType2.{u} (ℝ × ℝ) τ :=
  exists_hasType2_of_finiteDimensional

/-- **The sharp type-2 constant of `ℝ × ℝ` with the maximum norm is at most `√2`** (Giles 2015,
§2.5, pp. 17–18, l. 776–787).  From `‖x‖_∞ ≤ ‖x‖₂ ≤ √2 ‖x‖_∞` and
`hasType2_of_isomorphic_embedding`.  The constant cannot be lowered (not formalised): the
random signs `±(1, 1)` and `±(1, −1)` give `E‖X₁ + X₂‖² = 4 = 2 (E‖X₁‖² + E‖X₂‖²)`. -/
theorem hasType2_prod_sqrt_two : HasType2.{u} (ℝ × ℝ) (Real.sqrt 2) := by
  let T : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap).comp
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearMap
  have hT : ∀ p : ℝ × ℝ, ‖T p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := fun p => by
    simp [T, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  have hlow : ∀ p : ℝ × ℝ, 1 * ‖p‖ ≤ ‖T p‖ := fun p => by
    rw [one_mul, ← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, hT,
      Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total |p.1| |p.2| with h | h
    · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg p.1]
    · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg p.2]
  have hup : ∀ p : ℝ × ℝ, ‖T p‖ ≤ Real.sqrt 2 * ‖p‖ := fun p => by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, hT, mul_pow,
      Real.sq_sqrt (by norm_num), Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : p.1 ^ 2 ≤ (max |p.1| |p.2|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) 2
    have h2 : p.2 ^ 2 ≤ (max |p.1| |p.2|) ^ 2 := by
      rw [← sq_abs p.2]; exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) 2
    linarith
  simpa using hasType2_of_isomorphic_embedding T one_pos hlow hup

/-! ### The multilevel estimator with outputs in a normed space -/

/-- The level corrections of Giles 2015, §1.3 and (2.2), for outputs in a vector space `E`:
`ΔP_0 = P_0` and `ΔP_ℓ = P_ℓ − P_{ℓ−1}` for `ℓ ≥ 1`. -/
def vecLevelDiff {Ω₀ E : Type*} [Sub E] (Pl : ℕ → Ω₀ → E) : ℕ → Ω₀ → E
  | 0 => Pl 0
  | ℓ + 1 => fun y => Pl (ℓ + 1) y - Pl ℓ y

/-- Giles' multilevel estimator (2.2) for outputs in a real vector space `E` (Giles 2015, §2.5):
`Y = ∑_{ℓ=0}^{L} N_ℓ⁻¹ ∑_{n<N_ℓ} ΔP_ℓ(ω^{(ℓ,n)})`, where `ω^{(ℓ,n)}` is the input of the `n`-th
sample on level `ℓ`.  For `N_ℓ = 0` the level term is `0`; every theorem assumes `N_ℓ ≥ 1`. -/
noncomputable def vecMlmcEstimator {Ω₀ Ω E : Type*} [AddCommGroup E] [Module ℝ E]
    (Pl : ℕ → Ω₀ → E) (ω : ℕ × ℕ → Ω → Ω₀) (L : ℕ) (N : ℕ → ℕ) (x : Ω) : E :=
  ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ)⁻¹ • ∑ n ∈ range (N ℓ), vecLevelDiff Pl ℓ (ω (ℓ, n) x)

section estimator

variable {Ω₀ E : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀} [NormedAddCommGroup E]

/-- Square-integrable approximations have square-integrable level corrections. -/
lemma memLp_vecLevelDiff {Pl : ℕ → Ω₀ → E} (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν) :
    ∀ ℓ, MemLp (vecLevelDiff Pl ℓ) 2 ν
  | 0 => hPl 0
  | ℓ + 1 => (hPl (ℓ + 1)).sub (hPl ℓ)

variable [NormedSpace ℝ E]

/-- Telescoping of the level means (Giles 2015, §1.3, p. 4, for vector outputs):
`∑_{ℓ=0}^{L} E[ΔP_ℓ] = E[P_L]`. -/
lemma sum_integral_vecLevelDiff {Pl : ℕ → Ω₀ → E} (hPl : ∀ ℓ, Integrable (Pl ℓ) ν) :
    ∀ L : ℕ, ∑ ℓ ∈ range (L + 1), ∫ y, vecLevelDiff Pl ℓ y ∂ν = ∫ y, Pl L y ∂ν
  | 0 => by
    rw [sum_range_one]
    rfl
  | L + 1 => by
    rw [sum_range_succ, sum_integral_vecLevelDiff hPl L]
    show _ + ∫ y, (Pl (L + 1) y - Pl L y) ∂ν = _
    rw [integral_sub (hPl _) (hPl _)]
    abel

/-- Bochner integrals of vector-valued functions transport along a measure-preserving map. -/
lemma integral_comp_measurePreserving_vec {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {φ : Ω → Ω₀} (hφ : MeasurePreserving φ μ ν) {f : Ω₀ → E} (hf : AEStronglyMeasurable f ν) :
    ∫ x, f (φ x) ∂μ = ∫ y, f y ∂ν := by
  rw [← hφ.map_eq] at hf ⊢
  exact (integral_map hφ.measurable.aemeasurable hf).symm

end estimator

/-! ### The mean-square error under type 2 -/

/-- **The MSE of the multilevel estimator in a type-2 Banach space** (Giles 2015, §2.5,
pp. 17–18, l. 776–787: "the variance for the combined multilevel estimator can not necessarily be
expressed in the usual form as `∑_ℓ N_ℓ⁻¹ V_ℓ`, `V_ℓ ≡ E[‖P_ℓ − P_{ℓ−1} − E[P_ℓ − P_{ℓ−1}]‖²]`.
Nevertheless, the theory can be extended to the use of other norms by using results from Banach
space theory for the sums of independent random variables").  If `E` has type 2 with constant
`τ` (`HasType2`), the inputs `ω^{(ℓ,n)}` are independent with law `ν`, the `P_ℓ` are
square-integrable and `N_ℓ ≥ 1` for `ℓ ≤ L`, then for every `m ∈ E` the squared error of the
estimator (2.2) is integrable and
`E‖Y − m‖² ≤ 2 (τ² ∑_{ℓ=0}^{L} V_ℓ/N_ℓ + ‖E[P_L] − m‖²)`. -/
theorem mlmc_mse_le_of_hasType2 {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {τ : ℝ} (hE : HasType2.{u} E τ)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Pl : ℕ → Ω₀ → E) (ω : ℕ × ℕ → Ω → Ω₀)
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν) (L : ℕ) {N : ℕ → ℕ} (hN : ∀ ℓ ∈ range (L + 1), 0 < N ℓ)
    (m : E) :
    Integrable (fun x => ‖vecMlmcEstimator Pl ω L N x - m‖ ^ 2) μ ∧
      ∫ x, ‖vecMlmcEstimator Pl ω L N x - m‖ ^ 2 ∂μ ≤
        2 * (τ ^ 2 * ∑ ℓ ∈ range (L + 1),
            (∫ y, ‖vecLevelDiff Pl ℓ y - ∫ z, vecLevelDiff Pl ℓ z ∂ν‖ ^ 2 ∂ν) / N ℓ +
          ‖(∫ y, Pl L y ∂ν) - m‖ ^ 2) := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  set D := vecLevelDiff Pl with hDdef
  have hD : ∀ ℓ, MemLp (D ℓ) 2 ν := memLp_vecLevelDiff hPl
  set d : ℕ → E := fun ℓ => ∫ z, D ℓ z ∂ν with hd
  set V : ℕ → ℝ := fun ℓ => ∫ y, ‖D ℓ y - d ℓ‖ ^ 2 ∂ν with hV
  -- the centred, scaled samples, indexed by `Σ ℓ, n`
  set X : (Σ _ : ℕ, ℕ) → Ω → E :=
    fun q x => (N q.1 : ℝ)⁻¹ • (D q.1 (ω (q.1, q.2) x) - d q.1) with hX
  set S : Finset (Σ _ : ℕ, ℕ) := (range (L + 1)).sigma fun ℓ => range (N ℓ) with hS
  have hg : Function.Injective (fun q : (Σ _ : ℕ, ℕ) => ((q.1, q.2) : ℕ × ℕ)) :=
    (Equiv.sigmaEquivProd ℕ ℕ).injective
  have hXind : iIndepFun X μ := by
    refine (hind.precomp hg).comp₀ (fun q z => (N q.1 : ℝ)⁻¹ • (D q.1 z - d q.1))
      (fun q => (hω _).measurable.aemeasurable) (fun q => ?_)
    rw [(hω _).map_eq]
    exact (((hD q.1).1.sub aestronglyMeasurable_const).const_smul _).aemeasurable
  have hDω : ∀ ℓ n, MemLp (fun x => D ℓ (ω (ℓ, n) x)) 2 μ := fun ℓ n =>
    (hD ℓ).comp_measurePreserving (hω _)
  have hXL2 : ∀ q, MemLp (X q) 2 μ := fun q =>
    ((hDω q.1 q.2).sub (memLp_const _)).const_smul _
  have hX0 : ∀ q, ∫ x, X q x ∂μ = 0 := fun q => by
    rw [hX, integral_smul, integral_sub ((hDω q.1 q.2).integrable one_le_two) (integrable_const _),
      integral_comp_measurePreserving_vec (hω _) (hD q.1).1, integral_const]
    simp [hd]
  have hXsq : ∀ q, ∫ x, ‖X q x‖ ^ 2 ∂μ = ((N q.1 : ℝ)⁻¹) ^ 2 * V q.1 := fun q => by
    have hpt : ∀ x, ‖X q x‖ ^ 2 = ((N q.1 : ℝ)⁻¹) ^ 2 * ‖D q.1 (ω (q.1, q.2) x) - d q.1‖ ^ 2 :=
      fun x => by rw [hX, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [hpt]
    rw [integral_const_mul, integral_comp_measurePreserving_vec (hω _)
      (f := fun y => ‖D q.1 y - d q.1‖ ^ 2)
      ((hD q.1).sub (memLp_const _)).norm.integrable_sq.aestronglyMeasurable]
  -- the error splits into a centred random part and the bias
  have hid : ∀ x, vecMlmcEstimator Pl ω L N x - m =
      ∑ q ∈ S, X q x + ((∫ y, Pl L y ∂ν) - m) := by
    intro x
    rw [hS, Finset.sum_sigma,
      ← sum_integral_vecLevelDiff (fun ℓ => (hPl ℓ).integrable one_le_two) L]
    have hlev : ∀ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ), X ⟨ℓ, n⟩ x =
        (N ℓ : ℝ)⁻¹ • ∑ n ∈ range (N ℓ), D ℓ (ω (ℓ, n) x) - d ℓ := fun ℓ hℓ => by
      rw [hX]
      dsimp only
      rw [← smul_sum, sum_sub_distrib, sum_const, card_range, smul_sub,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 (hN ℓ hℓ).ne'), one_smul]
    rw [sum_congr rfl hlev, sum_sub_distrib]
    unfold vecMlmcEstimator
    abel
  set Z : Ω → E := fun x => ∑ q ∈ S, X q x with hZdef
  set b : E := (∫ y, Pl L y ∂ν) - m with hb
  have hZ : MemLp Z 2 μ := memLp_finsetSum S fun q _ => hXL2 q
  have hT := hE.integral_norm_sum_sq_le S hXind (fun q _ => hXL2 q) (fun q _ => hX0 q)
  have hsumV : ∑ q ∈ S, ∫ x, ‖X q x‖ ^ 2 ∂μ = ∑ ℓ ∈ range (L + 1), V ℓ / N ℓ := by
    rw [hS, Finset.sum_sigma]
    refine sum_congr rfl fun ℓ hℓ => ?_
    simp only [hXsq, sum_const, card_range, nsmul_eq_mul]
    have hN' : (N ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hN ℓ hℓ).ne'
    field_simp
  have hfun : (fun x => ‖vecMlmcEstimator Pl ω L N x - m‖ ^ 2) = fun x => ‖Z x + b‖ ^ 2 :=
    funext fun x => by rw [hid x]
  have hint : Integrable (fun x => ‖Z x + b‖ ^ 2) μ := (hZ.add (memLp_const b)).norm.integrable_sq
  have hZ2 : Integrable (fun x => ‖Z x‖ ^ 2) μ := hZ.norm.integrable_sq
  refine ⟨hfun ▸ hint, ?_⟩
  rw [hfun]
  have hpt : ∀ x, ‖Z x + b‖ ^ 2 ≤ 2 * ‖Z x‖ ^ 2 + 2 * ‖b‖ ^ 2 := fun x => by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (Z x) b) 2
    nlinarith [sq_nonneg (‖Z x‖ - ‖b‖)]
  calc ∫ x, ‖Z x + b‖ ^ 2 ∂μ ≤ ∫ x, (2 * ‖Z x‖ ^ 2 + 2 * ‖b‖ ^ 2) ∂μ :=
        integral_mono hint ((hZ2.const_mul 2).add (integrable_const _)) hpt
    _ = 2 * ∫ x, ‖Z x‖ ^ 2 ∂μ + 2 * ‖b‖ ^ 2 := by
        rw [integral_add (hZ2.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const]
        simp
    _ ≤ 2 * (τ ^ 2 * ∑ ℓ ∈ range (L + 1), V ℓ / N ℓ) + 2 * ‖b‖ ^ 2 := by
        rw [← hsumV]
        linarith [hT]
    _ = _ := by ring

/-! ### Theorem 1 in a type-2 Banach space -/

/-- **Giles' Theorem 1 for outputs in a Banach space of type 2** (Giles 2015, §2.5, pp. 17–18,
l. 782–787: "the theory can be extended to the use of other norms by using results from Banach
space theory for the sums of independent random variables", with the substitutions
"`|E[P_ℓ] − E[P]| → ‖E[P_ℓ] − E[P]‖`, `V[P_ℓ − P_{ℓ−1}] → E[‖P_ℓ − P_{ℓ−1} − E[P_ℓ − P_{ℓ−1}]‖²]`"
of l. 764–768 in Theorem 1 of §2.1).  Let `E` have type 2 with constant `τ` (`HasType2`), let the
inputs `ω^{(ℓ,n)}` be independent with law `ν`, the `P_ℓ` square-integrable, `P` integrable, and
let the `n`-th level-`ℓ` sample cost `cost ℓ n` with mean `C_ℓ`.  If
(i) `‖E[P_ℓ − P]‖ ≤ c₁ 2^{−αℓ}`, (iii) `E‖ΔP_ℓ − E[ΔP_ℓ]‖² ≤ c₂ 2^{−βℓ}`,
(iv) `C_ℓ ≤ c₃ 2^{γℓ}` and `α ≥ ½ min(β, γ)`, then there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the estimator (2.2) has integrable squared
error, `E‖Y − E[P]‖² < ε²`, and expected total cost `≤ c₄ ε⁻²` if `β > γ`, `c₄ ε⁻² (log ε)²` if
`β = γ`, `c₄ ε^{−2−(γ−β)/α}` if `β < γ`.  (`c₄` depends on `τ`.) -/
theorem giles_theorem1_banach {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {τ : ℝ} (hE : HasType2.{u} E τ)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀} {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (P : Ω₀ → E) (Pl : ℕ → Ω₀ → E) (ω : ℕ × ℕ → Ω → Ω₀) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    (hP : Integrable P ν) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (h_i : ∀ ℓ : ℕ, ‖∫ y, (Pl ℓ y - P y) ∂ν‖ ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, ∫ y, ‖vecLevelDiff Pl ℓ y - ∫ z, vecLevelDiff Pl ℓ z ∂ν‖ ^ 2 ∂ν ≤
      c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => ‖vecMlmcEstimator Pl ω L N x - ∫ y, P y ∂ν‖ ^ 2) μ ∧
        ∫ x, ‖vecMlmcEstimator Pl ω L N x - ∫ y, P y ∂ν‖ ^ 2 ∂μ < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * complexityBound α β γ ε := by
  obtain ⟨c₄, hc₄, hcore⟩ := mlmc_complexity_core (c₁ := 2 * c₁)
    (c₂ := 2 * (τ ^ 2 + 1) * c₂) (c₃ := c₃) hα hβ hγ (by positivity) (by positivity) hc₃ hαβγ
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost'⟩ := hcore ε hε hε1
  obtain ⟨hint, hle⟩ :=
    mlmc_mse_le_of_hasType2 hE Pl ω hω hind hPl L (fun ℓ _ => hN ℓ) (∫ y, P y ∂ν)
  refine ⟨L, N, hN, hint, ?_, ?_⟩
  · -- mean-square error
    have : IsProbabilityMeasure ν := by
      rw [← (hω (0, 0)).map_eq]
      exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
    set V : ℕ → ℝ := fun ℓ => ∫ y, ‖vecLevelDiff Pl ℓ y - ∫ z, vecLevelDiff Pl ℓ z ∂ν‖ ^ 2 ∂ν
      with hV
    have hb : ‖(∫ y, Pl L y ∂ν) - ∫ y, P y ∂ν‖ ^ 2 ≤ (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 := by
      have h := h_i L
      rw [integral_sub ((hPl L).integrable one_le_two) hP] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    have hv : 2 * (τ ^ 2 * ∑ ℓ ∈ range (L + 1), V ℓ / N ℓ) ≤
        ∑ ℓ ∈ range (L + 1), Vb β (2 * (τ ^ 2 + 1) * c₂) ℓ / (N ℓ : ℝ) := by
      rw [mul_sum, mul_sum]
      refine sum_le_sum fun ℓ _ => ?_
      have hV0 : 0 ≤ V ℓ := integral_nonneg fun _ => sq_nonneg _
      have hNpos : (0 : ℝ) < N ℓ := Nat.cast_pos.2 (hN ℓ)
      have h3 := h_iii ℓ
      have hτ : 0 ≤ τ ^ 2 := sq_nonneg τ
      have hnum : 2 * τ ^ 2 * V ℓ ≤ 2 * (τ ^ 2 + 1) * c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) := by
        nlinarith
      calc 2 * (τ ^ 2 * (V ℓ / N ℓ)) = 2 * τ ^ 2 * V ℓ / N ℓ := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hnum hNpos.le
    have hb2 : 2 * ‖(∫ y, Pl L y ∂ν) - ∫ y, P y ∂ν‖ ^ 2 ≤
        (2 * c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 := by
      have h0 : 0 ≤ (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 := sq_nonneg _
      nlinarith
    calc ∫ x, ‖vecMlmcEstimator Pl ω L N x - ∫ y, P y ∂ν‖ ^ 2 ∂μ
        ≤ 2 * (τ ^ 2 * ∑ ℓ ∈ range (L + 1), V ℓ / N ℓ +
            ‖(∫ y, Pl L y ∂ν) - ∫ y, P y ∂ν‖ ^ 2) := hle
      _ < ε ^ 2 := by linarith
  · -- cost
    have hEc : μ[totalCost cost L N] = ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := by
      show ∫ x, ∑ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ), cost ℓ n x ∂μ = _
      rw [integral_finsetSum _ fun ℓ _ => integrable_finsetSum _ fun n _ => hcost ℓ n]
      refine sum_congr rfl fun ℓ _ => ?_
      rw [integral_finsetSum _ fun n _ => hcost ℓ n]
      simp only [hcostC, sum_const, card_range, nsmul_eq_mul]
    rw [hEc]
    calc ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ
        ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ :=
          sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (h_iv ℓ) (by positivity)
      _ ≤ c₄ * complexityBound α β γ ε := hcost'

end MLMC
