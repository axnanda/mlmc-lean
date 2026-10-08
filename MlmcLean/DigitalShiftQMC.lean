import MlmcLean.RandomShiftQMC
import Mathlib.Probability.UniformOn
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Randomised QMC by a random digital shift (Giles 2015, §3.5)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §3.5 "MLQMC
algorithm", pp. 26–27 (l. 1183–1199 of `docs/giles2015.txt`): QMC points are constructed "using
well-established QMC techniques such as rank-1 lattices … or Sobol sequences … to provide a
relatively uniform coverage of a unit hypercube integration region … Using just one set of `N_ℓ`
points gives good accuracy, but no confidence interval.  To regain a confidence interval one uses
randomised QMC in which the set of points is gives [sic] a random shift (for rank-1 lattice
rules) or a digital scrambling (for Sobol sequences).  Using 32 sets of points, each collectively
randomised, yields 32 set averages for the quantity of interest, `Y_ℓ`, and from these 32 random
independent values the variance of their average, `V_ℓ`, can be estimated in the usual way."

The random shift of lattice points is `MlmcLean/RandomShiftQMC.lean`.  This file formalises the
simplest *digital* randomisation of a point set such as a Sobol net, the **random digital shift
in base 2**: every point `x` is replaced by `x ⊕ U`, the digit-wise exclusive or of the binary
digits of `x` with those of one random `U` with independent fair digits, the same `U` for all
points of the set.

**Representation.**  A point is the sequence of its binary digits, an element of `ι → Bool`; for
points of the unit cube `[0,1]^δ` (`δ` a finite set of coordinates, `δ = Fin d` for `d`
dimensions) take `ι = δ × ℕ`, the `(j, k)` entry being the `(k+1)`-th binary digit of the `j`-th
coordinate, and `binaryPoint` maps digits to the point `(∑_k u_{j,k} 2^{−(k+1)})_j`.  The law of
independent fair digits is `uniformDigits ι`, the product of fair coins on `Bool` (Mathlib's
`Measure.infinitePi`).  Working on the digit space makes the digital shift an everywhere-defined
measurable map and sidesteps the two binary expansions of dyadic rationals (a null set); the
link to Lebesgue measure on the cube is proved separately (`uniformDigits_map_binaryPoint`).

**Results.**
* `digitalShift_measurePreserving`: for every fixed `x`, `u ↦ x ⊕ u` preserves the fair product
  measure, i.e. `x ⊕ U` has independent fair digits whenever `U` has.
* `digitalShiftQMC_unbiased`: hence for any points `x_0, …, x_{N−1}` and any integrable `f` the
  digitally shifted QMC average `N⁻¹ ∑_k f(x_k ⊕ U)` is integrable with mean `∫ f`.
* `digitalShift_replicates`: with `R` independent shifts (the paper's `R = 32`) the `R` set
  averages are independent and identically distributed with mean `∫ f`, their average is
  unbiased with variance `V₁/R` (`V₁` the variance of one set average), and the usual estimate
  of this variance is unbiased.
* `uniformDigits_map_binaryValue`, `uniformDigits_map_binaryPoint`: the binary expansion of
  independent fair digits is uniformly distributed on `[0,1]` and on `[0,1]^δ`: the push-forward
  of `uniformDigits` is Lebesgue measure restricted to the unit cube.  (Proof: the distribution
  function `G(t) = P(∑_k u_k 2^{−(k+1)} ≤ t)` satisfies `G(t) = ½ G(2t) + ½ G(2t − 1)` by
  splitting off the first digit, which forces `G(t) = min(max(t, 0), 1)`.)
* `digitalShiftQMC_unbiased_cube`: so for any points of the cube, given by their binary digits,
  each digitally shifted point is uniform on `[0,1]^δ`, and for every integrand `g` integrable on
  the cube, `N⁻¹ ∑_k g(x_k ⊕ U)` is an unbiased estimator of `∫_{[0,1]^δ} g`.

**Deviations and what is not proved.**  This is the random digital shift, not Owen's nested
scrambling, with which Sobol points are usually randomised; both make each randomised point
uniform, which is all that the unbiasedness and the confidence interval of the paper use.  No QMC
error rate (no discrepancy or Walsh-coefficient bound, no `O(N⁻¹)` behaviour) is claimed, and the
construction of Sobol points is not formalised (the points are arbitrary).  The cube is closed,
`[0,1]^δ`; its boundary is Lebesgue-null, so this is the same as `[0,1)^δ`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### Fair digits and the digital shift -/

/-- The law of independent fair binary digits indexed by `ι`: the product of the uniform
probability measures on `Bool` (for `ι = ℕ` the fair coin-tossing measure on Cantor space, for
`ι = δ × ℕ` the law of the binary digits of a uniform point of `[0,1]^δ`). -/
noncomputable def uniformDigits (ι : Type*) : Measure (ι → Bool) :=
  Measure.infinitePi fun _ : ι => uniformOn (Set.univ : Set Bool)

/-- The fair-digit measure is a probability measure. -/
lemma isProbabilityMeasure_uniformDigits (ι : Type*) :
    IsProbabilityMeasure (uniformDigits ι) := by
  unfold uniformDigits
  infer_instance

/-- **The digital shift in base 2** (Giles 2015, §3.5, p. 26): the digit-wise exclusive or
`x ⊕ u` of two digit sequences. -/
def digitalShift {ι : Type*} (x u : ι → Bool) : ι → Bool :=
  fun i => xor (x i) (u i)

/-- The digital shift by a fixed `x` is measurable. -/
lemma measurable_digitalShift {ι : Type*} (x : ι → Bool) : Measurable (digitalShift x) :=
  measurable_pi_lambda _ fun i => Measurable.of_discrete.comp (measurable_pi_apply i)

/-- A fair coin is invariant under `c ↦ b ⊕ c`. -/
lemma uniformOn_bool_map_xor (b : Bool) :
    (uniformOn (Set.univ : Set Bool)).map (xor b) = uniformOn Set.univ := by
  refine Measure.ext_of_singleton fun c => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton c)]
  have h : xor b ⁻¹' {c} = {xor b c} := by
    ext a
    cases a <;> cases b <;> cases c <;> simp
  rw [h, uniformOn_univ, uniformOn_univ, Measure.count_singleton, Measure.count_singleton]

/-- **A digital shift preserves the uniform distribution** (Giles 2015, §3.5, p. 26, l. 1190–1193:
"To regain a confidence interval one uses randomised QMC in which the set of points is gives [sic]
a random shift (for rank-1 lattice rules) or a digital scrambling (for Sobol sequences)").  For
every fixed digit sequence `x`, the map `u ↦ x ⊕ u` preserves the fair product measure
`uniformDigits ι`: if `U` has independent fair digits, so has `x ⊕ U`. -/
theorem digitalShift_measurePreserving {ι : Type*} (x : ι → Bool) :
    MeasurePreserving (digitalShift x) (uniformDigits ι) (uniformDigits ι) := by
  refine ⟨measurable_digitalShift x, ?_⟩
  have h := Measure.infinitePi_map_pi (μ := fun _ : ι => uniformOn (Set.univ : Set Bool))
    (f := fun i => xor (x i)) fun _ => Measurable.of_discrete
  simp only [uniformOn_bool_map_xor] at h
  exact h

/-! ### The digitally shifted QMC average -/

/-- **The digitally shifted QMC average** (Giles 2015, §3.5, p. 26): `N⁻¹ ∑_{k<N} f(x_k ⊕ u)`,
the average of `f` over the points `x_0, …, x_{N−1}` (given by their binary digits), all shifted
digitally by the same `u`. -/
noncomputable def digitalShiftQMC {ι : Type*} (f : (ι → Bool) → ℝ) (x : ℕ → ι → Bool) (N : ℕ)
    (u : ι → Bool) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ range N, f (digitalShift (x k) u)

section average

variable {ι : Type*}

/-- A digitally shifted QMC average of a measurable `f` is a measurable function of the shift. -/
lemma measurable_digitalShiftQMC {f : (ι → Bool) → ℝ} (hf : Measurable f) (x : ℕ → ι → Bool)
    (N : ℕ) : Measurable (digitalShiftQMC f x N) :=
  (Finset.measurable_sum _ fun k _ => hf.comp (measurable_digitalShift (x k))).const_mul _

/-- A digitally shifted QMC average of a square-integrable `f` is square-integrable. -/
lemma memLp_digitalShiftQMC {f : (ι → Bool) → ℝ} (hf : MemLp f 2 (uniformDigits ι))
    (x : ℕ → ι → Bool) (N : ℕ) : MemLp (digitalShiftQMC f x N) 2 (uniformDigits ι) :=
  (memLp_finsetSum _ fun k _ =>
    hf.comp_measurePreserving (digitalShift_measurePreserving (x k))).const_mul _

/-- **A random digital shift makes a QMC rule unbiased** (Giles 2015, §3.5, p. 26, l. 1190–1193:
"To regain a confidence interval one uses randomised QMC in which the set of points is gives [sic]
a random shift (for rank-1 lattice rules) or a digital scrambling (for Sobol sequences)").  Let
`x_0, …, x_{N−1}` be any `N ≥ 1` points, given by their binary digits (for instance a Sobol net),
and let the shift `U` have independent fair digits (law `uniformDigits ι`).  Then every shifted
point `x_k ⊕ U` again has independent fair digits, and for every integrable `f` the digitally
shifted average `N⁻¹ ∑_k f(x_k ⊕ U)` is integrable with mean `∫ f`. -/
theorem digitalShiftQMC_unbiased {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Ω → ι → Bool} (hU : MeasurePreserving U μ (uniformDigits ι)) (x : ℕ → ι → Bool)
    {f : (ι → Bool) → ℝ} (hf : Integrable f (uniformDigits ι)) {N : ℕ} (hN : 0 < N) :
    (∀ k, MeasurePreserving (fun ω => digitalShift (x k) (U ω)) μ (uniformDigits ι)) ∧
      Integrable (fun ω => digitalShiftQMC f x N (U ω)) μ ∧
      ∫ ω, digitalShiftQMC f x N (U ω) ∂μ = ∫ y, f y ∂(uniformDigits ι) := by
  have hsh := fun k => digitalShift_measurePreserving (ι := ι) (x k)
  have hint : ∀ k, Integrable (fun u => f (digitalShift (x k) u)) (uniformDigits ι) := fun k =>
    ((hsh k).integrable_comp hf.aestronglyMeasurable).2 hf
  have hQ : Integrable (digitalShiftQMC f x N) (uniformDigits ι) :=
    (integrable_finsetSum _ fun k _ => hint k).const_mul _
  refine ⟨fun k => (hsh k).comp hU, (hU.integrable_comp hQ.aestronglyMeasurable).2 hQ, ?_⟩
  rw [integral_comp_of_measurePreserving hU hQ.aestronglyMeasurable]
  unfold digitalShiftQMC
  rw [integral_const_mul, integral_finsetSum _ fun k _ => hint k]
  have hterm : ∀ k, ∫ u, f (digitalShift (x k) u) ∂(uniformDigits ι) =
      ∫ y, f y ∂(uniformDigits ι) := fun k =>
    integral_comp_of_measurePreserving (hsh k) hf.aestronglyMeasurable
  simp only [hterm, sum_const, card_range, nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  field_simp

/-- **Independent digital shifts: `32` independent unbiased values and the variance of their
average** (Giles 2015, §3.5, pp. 26–27, l. 1193–1199: "Using 32 sets of points, each collectively
randomised, yields 32 set averages for the quantity of interest, `Y_ℓ`, and from these 32 random
independent values the variance of their average, `V_ℓ`, can be estimated in the usual way"), for
the digital shift of Sobol-type points.  Let `U_0, U_1, …` be independent digital shifts, each
with independent fair digits, let `f` be measurable and square-integrable, and let
`x_0, …, x_{N−1}` be any `N ≥ 1` points.  With `R ≥ 1` replicates (the paper's `R = 32`), the set
averages `Y_r = N⁻¹ ∑_k f(x_k ⊕ U_r)`
* are independent, square-integrable and identically distributed, each with mean `∫ f`;
* have an unbiased average `Ȳ = R⁻¹ ∑_{r<R} Y_r`, `E[Ȳ] = ∫ f`, with variance `V[Ȳ] = V₁/R`,
  where `V₁` is the variance of one set average;
* and, for `R ≥ 2`, the usual estimate `(R(R − 1))⁻¹ ∑_{r<R} (Y_r − Ȳ)²` of `V[Ȳ]` is unbiased.
-/
theorem digitalShift_replicates {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {U : ℕ → Ω → ι → Bool}
    (hU : ∀ r, MeasurePreserving (U r) μ (uniformDigits ι)) (hUind : iIndepFun U μ)
    (x : ℕ → ι → Bool) {f : (ι → Bool) → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (uniformDigits ι)) {N R : ℕ} (hN : 0 < N) (hR : 0 < R) :
    iIndepFun (fun r ω => digitalShiftQMC f x N (U r ω)) μ ∧
      (∀ r, MemLp (fun ω => digitalShiftQMC f x N (U r ω)) 2 μ) ∧
      (∀ r, μ.map (fun ω => digitalShiftQMC f x N (U r ω)) =
        (uniformDigits ι).map (digitalShiftQMC f x N)) ∧
      (∀ r, ∫ ω, digitalShiftQMC f x N (U r ω) ∂μ = ∫ y, f y ∂(uniformDigits ι)) ∧
      ∫ ω, (R : ℝ)⁻¹ * ∑ r ∈ range R, digitalShiftQMC f x N (U r ω) ∂μ =
        ∫ y, f y ∂(uniformDigits ι) ∧
      variance (fun ω => (R : ℝ)⁻¹ * ∑ r ∈ range R, digitalShiftQMC f x N (U r ω)) μ =
        variance (digitalShiftQMC f x N) (uniformDigits ι) / R ∧
      (2 ≤ R → ∫ ω, ((R : ℝ) * (R - 1))⁻¹ * ∑ r ∈ range R, (digitalShiftQMC f x N (U r ω) -
          (R : ℝ)⁻¹ * ∑ s ∈ range R, digitalShiftQMC f x N (U s ω)) ^ 2 ∂μ =
        variance (digitalShiftQMC f x N) (uniformDigits ι) / R) := by
  have := isProbabilityMeasure_uniformDigits ι
  have hQm := measurable_digitalShiftQMC hfm x N
  have hQ2 := memLp_digitalShiftQMC hf x N
  have hYind : iIndepFun (fun r ω => digitalShiftQMC f x N (U r ω)) μ :=
    hUind.comp (fun _ => digitalShiftQMC f x N) (fun _ => hQm)
  have hY2 : ∀ r, MemLp (fun ω => digitalShiftQMC f x N (U r ω)) 2 μ := fun r =>
    hQ2.comp_measurePreserving (hU r)
  have hmean : ∀ r, ∫ ω, digitalShiftQMC f x N (U r ω) ∂μ = ∫ y, f y ∂(uniformDigits ι) :=
    fun r => (digitalShiftQMC_unbiased (hU r) x (hf.integrable one_le_two) hN).2.2
  have hvar : ∀ r, variance (fun ω => digitalShiftQMC f x N (U r ω)) μ =
      variance (digitalShiftQMC f x N) (uniformDigits ι) := fun r =>
    (hU r).variance_fun_comp hQm.aemeasurable
  have hpair : Set.Pairwise ↑(range R) fun i j =>
      IndepFun (fun ω => digitalShiftQMC f x N (U i ω))
        (fun ω => digitalShiftQMC f x N (U j ω)) μ :=
    fun i _ j _ hij => hYind.indepFun hij
  have hR' : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hR.ne'
  refine ⟨hYind, hY2, fun r => ?_, hmean, ?_, variance_sample_mean _ R hR _ hY2 hvar hpair,
    fun hR2 => ?_⟩
  · rw [← (hU r).map_eq, Measure.map_map hQm (hU r).measurable]
    rfl
  · rw [integral_const_mul, integral_finsetSum _ fun r _ => (hY2 r).integrable one_le_two]
    simp only [hmean, sum_const, card_range, nsmul_eq_mul]
    field_simp
  · have hR1 : (R : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ R := by exact_mod_cast hR2
      linarith
    rw [integral_const_mul, integral_sum_sq_sub_mean _ hR hY2 hmean hvar hpair]
    field_simp

end average

/-! ### From binary digits to points of the unit cube -/

/-- The number `∑_{k≥0} u_k 2^{−(k+1)} ∈ [0, 1]` with binary digits `u_0, u_1, …` (the series
converges absolutely, its terms being at most `2^{−(k+1)}`). -/
noncomputable def binaryValue (u : ℕ → Bool) : ℝ :=
  ∑' k, ((u k).toNat : ℝ) / 2 ^ (k + 1)

/-- The `k`-th term of a binary expansion is at most `2^{−(k+1)} = ½ · 2^{−k}`. -/
lemma binaryTerm_le (b : Bool) (k : ℕ) : (b.toNat : ℝ) / 2 ^ (k + 1) ≤ 1 / 2 / 2 ^ k := by
  have hb : (b.toNat : ℝ) ≤ 1 := by cases b <;> simp
  rw [div_div, ← pow_succ']
  exact div_le_div_of_nonneg_right hb (by positivity)

/-- A binary expansion converges. -/
lemma summable_binaryTerm (u : ℕ → Bool) :
    Summable fun k => ((u k).toNat : ℝ) / 2 ^ (k + 1) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (fun k => binaryTerm_le (u k) k)
    (summable_geometric_two' 1)

/-- The value of a digit sequence is a measurable function of the digits. -/
lemma measurable_binaryValue : Measurable binaryValue := by
  refine measurable_of_tendsto_metrizable
    (f := fun n u => ∑ k ∈ range n, ((u k).toNat : ℝ) / 2 ^ (k + 1)) (fun n => ?_) ?_
  · exact Finset.measurable_sum _ fun k _ =>
      (Measurable.of_discrete (f := fun b : Bool => (b.toNat : ℝ) / 2 ^ (k + 1))).comp
        (measurable_pi_apply k)
  · exact tendsto_pi_nhds.2 fun u => (summable_binaryTerm u).hasSum.tendsto_sum_nat

/-- `0 ≤ ∑_k u_k 2^{−(k+1)}`. -/
lemma binaryValue_nonneg (u : ℕ → Bool) : 0 ≤ binaryValue u :=
  tsum_nonneg fun _ => by positivity

/-- `∑_k u_k 2^{−(k+1)} ≤ ∑_k 2^{−(k+1)} = 1`. -/
lemma binaryValue_le_one (u : ℕ → Bool) : binaryValue u ≤ 1 :=
  ((summable_binaryTerm u).tsum_le_tsum (fun k => binaryTerm_le (u k) k)
    (summable_geometric_two' 1)).trans_eq (tsum_geometric_two' 1)

/-- Prepending a digit: `consDigit b v = (b, v_0, v_1, …)`. -/
def consDigit (b : Bool) (v : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | k + 1 => v k

/-- Prepending a digit is measurable. -/
lemma measurable_consDigit : Measurable fun p : Bool × (ℕ → Bool) => consDigit p.1 p.2 :=
  measurable_pi_lambda _ fun k => by
    cases k with
    | zero => exact measurable_fst
    | succ k => exact (measurable_pi_apply k).comp measurable_snd

/-- Splitting off the first binary digit: `0.b v_0 v_1 … = (b + 0.v_0 v_1 …)/2`. -/
lemma binaryValue_consDigit (b : Bool) (v : ℕ → Bool) :
    binaryValue (consDigit b v) = ((b.toNat : ℝ) + binaryValue v) / 2 := by
  unfold binaryValue
  rw [(summable_binaryTerm (consDigit b v)).tsum_eq_zero_add]
  have h : ∀ k, ((consDigit b v (k + 1)).toNat : ℝ) / 2 ^ (k + 1 + 1) =
      ((v k).toNat : ℝ) / 2 ^ (k + 1) / 2 := fun k => by
    show ((v k).toNat : ℝ) / 2 ^ (k + 1 + 1) = _
    rw [pow_succ, div_div]
  simp only [h]
  rw [tsum_div_const]
  show (b.toNat : ℝ) / 2 ^ (0 + 1) + _ = _
  ring

/-- A finite product over `s ⊆ ℕ` split into the factor at `0` and the shifted rest. -/
lemma prod_eq_ite_mul_prod_succ {M : Type*} [CommMonoid M] (s : Finset ℕ) (g : ℕ → M) :
    ∏ i ∈ s, g i = (if 0 ∈ s then g 0 else 1) *
      ∏ k ∈ s.preimage Nat.succ Nat.succ_injective.injOn, g (k + 1) := by
  classical
  have h1 : ∏ k ∈ s.preimage Nat.succ Nat.succ_injective.injOn, g (k + 1) =
      ∏ i ∈ s, (if i = 0 then 1 else g i) := by
    rw [← Finset.prod_preimage Nat.succ s Nat.succ_injective.injOn
      (fun i => if i = 0 then 1 else g i)]
    · exact Finset.prod_congr rfl fun k _ => by simp
    · intro x _ hx
      have : x = 0 := by
        by_contra h
        exact hx ⟨x - 1, by omega⟩
      simp [this]
  rw [h1, ← Finset.prod_ite_eq' s 0 (fun _ => g 0), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [h, mul_one]
  · rw [one_mul]

/-- Independent fair digits are a fair first digit followed by an independent sequence of fair
digits: the law of `(b, v) ↦ (b, v_0, v_1, …)` under `fair coin ⊗ uniformDigits ℕ` is
`uniformDigits ℕ`. -/
lemma map_consDigit :
    ((uniformOn (Set.univ : Set Bool)).prod (uniformDigits ℕ)).map
      (fun p => consDigit p.1 p.2) = uniformDigits ℕ := by
  have := isProbabilityMeasure_uniformDigits ℕ
  refine Measure.eq_infinitePi _ fun s t _ => ?_
  rw [Measure.map_apply measurable_consDigit
    (MeasurableSet.pi s.countable_toSet fun _ _ => .of_discrete)]
  have hpre : (fun p : Bool × (ℕ → Bool) => consDigit p.1 p.2) ⁻¹' Set.pi ↑s t =
      (if 0 ∈ s then t 0 else Set.univ) ×ˢ
        Set.pi ↑(s.preimage Nat.succ Nat.succ_injective.injOn) (fun k => t (k + 1)) := by
    ext ⟨b, v⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨?_, fun k hk => h (k + 1) hk⟩
      split_ifs with h0
      · exact h 0 h0
      · trivial
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero =>
        rw [if_pos hi] at h0
        exact h0
      | succ k => exact h k hi
  rw [hpre, Measure.prod_prod]
  unfold uniformDigits
  rw [Measure.infinitePi_pi _ (fun _ _ => .of_discrete), prod_eq_ite_mul_prod_succ s]
  congr 1
  split_ifs
  · rfl
  · exact measure_univ

/-- A fair coin gives mass `½` to each side. -/
lemma uniformOn_bool_singleton (b : Bool) : uniformOn (Set.univ : Set Bool) {b} = 2⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton]
  simp

/-- The self-similarity of the distribution function of `∑_k u_k 2^{−(k+1)}`:
`P(X ≤ t) = ½ P(X ≤ 2t) + ½ P(X ≤ 2t − 1)` (condition on the first digit). -/
lemma uniformDigits_binaryValue_le (t : ℝ) :
    uniformDigits ℕ {u | binaryValue u ≤ t} =
      2⁻¹ * uniformDigits ℕ {u | binaryValue u ≤ 2 * t} +
        2⁻¹ * uniformDigits ℕ {u | binaryValue u ≤ 2 * t - 1} := by
  have := isProbabilityMeasure_uniformDigits ℕ
  have hA : ∀ s, MeasurableSet {u : ℕ → Bool | binaryValue u ≤ s} := fun s =>
    measurableSet_le measurable_binaryValue measurable_const
  conv_lhs => rw [← map_consDigit]
  rw [Measure.map_apply measurable_consDigit (hA t)]
  have hpre : (fun p : Bool × (ℕ → Bool) => consDigit p.1 p.2) ⁻¹' {u | binaryValue u ≤ t} =
      ({false} ×ˢ {u | binaryValue u ≤ 2 * t}) ∪
        ({true} ×ˢ {u | binaryValue u ≤ 2 * t - 1}) := by
    ext ⟨b, v⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, binaryValue_consDigit, Set.mem_union,
      Set.mem_prod, Set.mem_singleton_iff]
    cases b
    · simp only [Bool.toNat_false, Nat.cast_zero, zero_add, true_and, Bool.false_eq_true,
        false_and, or_false]
      constructor <;> intro h <;> linarith
    · simp only [Bool.toNat_true, Nat.cast_one, Bool.true_eq_false, false_and, true_and,
        false_or]
      constructor <;> intro h <;> linarith
  have hdisj : Disjoint ({false} ×ˢ {u : ℕ → Bool | binaryValue u ≤ 2 * t})
      ({true} ×ˢ {u : ℕ → Bool | binaryValue u ≤ 2 * t - 1}) := by
    rw [Set.disjoint_left]
    rintro ⟨b, v⟩ h1 h2
    simp only [Set.mem_prod, Set.mem_singleton_iff] at h1 h2
    rw [h1.1] at h2
    exact Bool.false_ne_true h2.1
  rw [hpre, measure_union hdisj ((measurableSet_singleton true).prod (hA _)), Measure.prod_prod,
    Measure.prod_prod, uniformOn_bool_singleton, uniformOn_bool_singleton]

/-- The uniform distribution function is the only one with values in `[0, 1]`, `G = 0` on
`(−∞, 0)`, `G = 1` on `[1, ∞)` and `G(t) = ½ G(2t) + ½ G(2t − 1)`: on `[0, 1)` one of the two
terms is fixed, so the difference to `min(max(t, 0), 1)` halves at each step. -/
lemma eq_clamp_of_selfSimilar {G : ℝ → ℝ} (h0 : ∀ t, 0 ≤ G t) (h1 : ∀ t, G t ≤ 1)
    (hneg : ∀ t < 0, G t = 0) (hone : ∀ t, 1 ≤ t → G t = 1)
    (hG : ∀ t, G t = (G (2 * t) + G (2 * t - 1)) / 2) (t : ℝ) : G t = max 0 (min t 1) := by
  set c : ℝ → ℝ := fun s => max 0 (min s 1) with hcdef
  have hc : ∀ s, c s = (c (2 * s) + c (2 * s - 1)) / 2 := fun s => by
    simp only [hcdef, max_def, min_def]
    split_ifs <;> linarith
  have hc0 : ∀ s, 0 ≤ c s := fun s => le_max_left _ _
  have hc1 : ∀ s, c s ≤ 1 := fun s => max_le zero_le_one (min_le_right _ _)
  have hcneg : ∀ s < 0, c s = 0 := fun s hs => by
    simp only [hcdef]
    exact max_eq_left (min_le_of_left_le hs.le)
  have hcone : ∀ s, 1 ≤ s → c s = 1 := fun s hs => by
    simp only [hcdef]
    rw [min_eq_right hs, max_eq_right zero_le_one]
  have key : ∀ n : ℕ, ∀ s, |G s - c s| ≤ (1 / 2) ^ n := by
    intro n
    induction n with
    | zero =>
      intro s
      rw [pow_zero, abs_le]
      constructor <;> linarith [h0 s, h1 s, hc0 s, hc1 s]
    | succ n ih =>
      intro s
      have e : G s - c s = ((G (2 * s) - c (2 * s)) + (G (2 * s - 1) - c (2 * s - 1))) / 2 := by
        rw [hG s, hc s]
        ring
      rw [e, abs_div, abs_two, pow_succ]
      rcases lt_or_ge (2 * s) 1 with h | h
      · have h' : 2 * s - 1 < 0 := by linarith
        rw [hneg _ h', hcneg _ h', sub_self, add_zero]
        linarith [ih (2 * s)]
      · rw [hone _ h, hcone _ h, sub_self, zero_add]
        linarith [ih (2 * s - 1)]
  have hlim : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := ge_of_tendsto' hlim fun n => key n t
  have h' : G t - c t = 0 := abs_eq_zero.1 (le_antisymm h (abs_nonneg _))
  linarith

/-- **Fair binary digits give a uniform point of `[0, 1]`** (the identification behind the
"unit hypercube integration region" of Giles 2015, §3.5, p. 26, l. 1183–1185, for the
digit representation of QMC points used in this file).  If `u_0, u_1, …` are independent fair
digits, then `∑_k u_k 2^{−(k+1)}` is uniformly distributed on `[0, 1]`: the push-forward of
`uniformDigits ℕ` under `binaryValue` is Lebesgue measure restricted to `[0, 1]`. -/
theorem uniformDigits_map_binaryValue :
    (uniformDigits ℕ).map binaryValue = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have := isProbabilityMeasure_uniformDigits ℕ
  set G : ℝ → ℝ := fun s => (uniformDigits ℕ {u | binaryValue u ≤ s}).toReal with hGdef
  have hG : ∀ s, G s = (G (2 * s) + G (2 * s - 1)) / 2 := fun s => by
    simp only [hGdef]
    rw [uniformDigits_binaryValue_le s,
      ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))
        (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)), ENNReal.toReal_mul,
      ENNReal.toReal_mul]
    simp
    ring
  have hG0 : ∀ s, 0 ≤ G s := fun s => ENNReal.toReal_nonneg
  have hGneg : ∀ s < 0, G s = 0 := fun s hs => by
    have he : {u : ℕ → Bool | binaryValue u ≤ s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun u hu => by
        have := binaryValue_nonneg u
        simp only [Set.mem_ofPred_eq] at hu
        linarith
    simp only [hGdef, he, measure_empty, ENNReal.toReal_zero]
  have hGone : ∀ s, 1 ≤ s → G s = 1 := fun s hs => by
    have he : {u : ℕ → Bool | binaryValue u ≤ s} = Set.univ :=
      Set.eq_univ_of_forall fun u => (binaryValue_le_one u).trans hs
    simp only [hGdef, he, measure_univ, ENNReal.toReal_one]
  have hG1 : ∀ s, G s ≤ 1 := fun s => by
    simp only [hGdef]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.map_apply measurable_binaryValue measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  have hinter : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 (min t 1) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
    tauto
  rw [hinter, Real.volume_Icc, sub_zero]
  have hL : uniformDigits ℕ (binaryValue ⁻¹' Set.Iic t) = ENNReal.ofReal (G t) :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [hL, eq_clamp_of_selfSimilar hG0 hG1 hGneg hGone hG t]
  rcases le_total (min t 1) 0 with h | h
  · rw [max_eq_left h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_right h]

/-- The point `(∑_k u_{j,k} 2^{−(k+1)})_{j ∈ δ}` of the unit cube `[0,1]^δ` with binary digits
`u_{j,0}, u_{j,1}, …` in coordinate `j`. -/
noncomputable def binaryPoint {δ : Type*} (u : δ × ℕ → Bool) : δ → ℝ :=
  fun j => binaryValue fun k => u (j, k)

/-- The point with given binary digits is a measurable function of the digits. -/
lemma measurable_binaryPoint {δ : Type*} : Measurable (binaryPoint (δ := δ)) :=
  measurable_pi_lambda _ fun j =>
    measurable_binaryValue.comp (measurable_pi_lambda _ fun k => measurable_pi_apply (j, k))

/-- **Fair binary digits give a uniform point of the unit cube** (Giles 2015, §3.5, p. 26,
l. 1183–1185: QMC points "provide a relatively uniform coverage of a unit hypercube integration
region"; this identifies the digit space of this file with that region).  For a finite set `δ`
of coordinates, the push-forward of `uniformDigits (δ × ℕ)` under `binaryPoint` is Lebesgue
measure restricted to `[0,1]^δ`. -/
theorem uniformDigits_map_binaryPoint {δ : Type*} [Fintype δ] :
    (uniformDigits (δ × ℕ)).map binaryPoint =
      volume.restrict (Set.univ.pi fun _ : δ => Set.Icc (0 : ℝ) 1) := by
  have hcurry : (binaryPoint : (δ × ℕ → Bool) → δ → ℝ) =
      (fun w : δ → ℕ → Bool => fun j => binaryValue (w j)) ∘
        (MeasurableEquiv.curry δ ℕ Bool) := rfl
  have hmv : Measurable fun w : δ → ℕ → Bool => fun j => binaryValue (w j) :=
    measurable_pi_lambda _ fun j => measurable_binaryValue.comp (measurable_pi_apply j)
  rw [hcurry, ← Measure.map_map hmv (MeasurableEquiv.curry δ ℕ Bool).measurable]
  have hc := Measure.infinitePi_map_curry (fun (_ : δ) (_ : ℕ) => uniformOn (Set.univ : Set Bool))
  have h1 := uniformDigits_map_binaryValue
  unfold uniformDigits at h1 ⊢
  have hpm : IsProbabilityMeasure
      ((Measure.infinitePi fun _ : ℕ => uniformOn (Set.univ : Set Bool)).map binaryValue) :=
    Measure.isProbabilityMeasure_map measurable_binaryValue.aemeasurable
  rw [hc, Measure.infinitePi_map_pi _ (fun _ => measurable_binaryValue), Measure.infinitePi_eq_pi,
    h1, volume_pi, Measure.restrict_pi_pi]

/-- **A random digital shift gives an unbiased QMC estimate of an integral over the unit cube**
(Giles 2015, §3.5, p. 26, l. 1183–1193: QMC points such as "Sobol sequences … provide a relatively
uniform coverage of a unit hypercube integration region … To regain a confidence interval one
uses randomised QMC in which the set of points is gives [sic] … a digital scrambling (for Sobol
sequences)").  Let `x_0, …, x_{N−1}` (`N ≥ 1`) be any points of `[0,1]^δ`, given by their binary
digits, and let the shift `U` have independent fair digits.  Then every digitally shifted point
`x_k ⊕ U` is uniformly distributed on `[0,1]^δ`, and for every `g` integrable on `[0,1]^δ` the
randomised QMC average `N⁻¹ ∑_k g(x_k ⊕ U)` is integrable with mean `∫_{[0,1]^δ} g`. -/
theorem digitalShiftQMC_unbiased_cube {δ : Type*} [Fintype δ] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : Ω → δ × ℕ → Bool} (hU : MeasurePreserving U μ (uniformDigits (δ × ℕ)))
    (x : ℕ → δ × ℕ → Bool) {g : (δ → ℝ) → ℝ}
    (hg : IntegrableOn g (Set.univ.pi fun _ : δ => Set.Icc (0 : ℝ) 1)) {N : ℕ} (hN : 0 < N) :
    (∀ k, MeasurePreserving (fun ω => binaryPoint (digitalShift (x k) (U ω))) μ
      (volume.restrict (Set.univ.pi fun _ : δ => Set.Icc (0 : ℝ) 1))) ∧
    Integrable (fun ω => (N : ℝ)⁻¹ * ∑ k ∈ range N, g (binaryPoint (digitalShift (x k) (U ω))))
      μ ∧
    ∫ ω, (N : ℝ)⁻¹ * ∑ k ∈ range N, g (binaryPoint (digitalShift (x k) (U ω))) ∂μ =
      ∫ y in Set.univ.pi (fun _ : δ => Set.Icc (0 : ℝ) 1), g y := by
  have hmp : MeasurePreserving binaryPoint (uniformDigits (δ × ℕ))
      (volume.restrict (Set.univ.pi fun _ : δ => Set.Icc (0 : ℝ) 1)) :=
    ⟨measurable_binaryPoint, uniformDigits_map_binaryPoint⟩
  have hf : Integrable (fun u => g (binaryPoint u)) (uniformDigits (δ × ℕ)) :=
    (hmp.integrable_comp hg.aestronglyMeasurable).2 hg
  obtain ⟨-, hint, hmean⟩ := digitalShiftQMC_unbiased hU x hf hN
  refine ⟨fun k => hmp.comp ((digitalShift_measurePreserving (x k)).comp hU), hint, ?_⟩
  rw [show (fun ω => (N : ℝ)⁻¹ * ∑ k ∈ range N, g (binaryPoint (digitalShift (x k) (U ω)))) =
    fun ω => digitalShiftQMC (fun u => g (binaryPoint u)) x N (U ω) from rfl, hmean]
  exact integral_comp_of_measurePreserving hmp hg.aestronglyMeasurable

end MLMC
