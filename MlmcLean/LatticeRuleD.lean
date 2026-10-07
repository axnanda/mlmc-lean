import MlmcLean.QMC1D
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Randomly shifted rank-1 lattice rules in `d` dimensions (Giles 2015, §1, §2.7, §3.5)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015).
* §1, p. 2 (l. 70–74 of `docs/giles2015.txt`): in quasi-Monte Carlo "the samples are not chosen
  randomly and independently, but are instead selected very carefully to reduce the error.  In the
  best cases, the error may be `O(N⁻¹)`, up to logarithmic terms".
* §2.7, p. 20 (l. 921–938): MLQMC "was based on extensible rank-1 lattices developed at UNSW (Dick,
  Pillichshammer and Waterhouse 2007)", and "These theoretical developments are very encouraging,
  showing that under certain conditions they lead to multilevel methods with a complexity which is
  `O(ε^{−p})` with `p < 2`."
* §3.5, pp. 26–27 (l. 1179–1199): the `N_ℓ` points are constructed "using well-established QMC
  techniques such as rank-1 lattices (Dick et al. 2007) … to provide a relatively uniform coverage
  of a unit hypercube integration region.  In the best cases, this results in the approximate
  numerical integration error being `O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})` error which
  comes from Monte Carlo sampling. … To regain a confidence interval one uses randomised QMC in
  which the set of points is gives [sic] a random shift (for rank-1 lattice rules) … Using 32 sets
  of points, each collectively randomised, yields 32 set averages for the quantity of interest,
  `Y_ℓ`, and from these 32 random independent values the variance of their average, `V_ℓ`, can be
  estimated in the usual way."

`MlmcLean.QMC1D` treats one dimension.  This file treats randomly shifted rank-1 lattice rules in
any dimension, on the unit torus `𝕋^d = (ℝ/ℤ)^d` (`UnitAddTorus d` for a finite index type `d`,
with its uniform probability measure `volume`, as in `MlmcLean.RandomShiftQMC`): a function on the
unit cube `[0, 1)^d` is a function on `𝕋^d`, and the sum `x + u` on `𝕋^d` is `frac(x + u)`
coordinatewise (`rank1Lattice_add_coe`).

**Setting.**  For a generating vector `z ∈ ℤ^d` and `N ≥ 1` the rank-1 lattice is
`x_i = frac(i z/N)`, `i < N` (`rank1Lattice z N`), and a shift `u ∈ 𝕋^d` gives the randomly
shifted lattice average `Q(u) = N⁻¹ ∑_{i<N} f(x_i + u)` (`shiftedQMC f (rank1Lattice z N) N u`).
The dual lattice is `L^⊥ = {k ∈ ℤ^d : k·z ≡ 0 mod N}` (`dualLattice z N`), and
`f̂(k) = ∫_{𝕋^d} e^{−2πi k·x} f(x) dx` is the `k`-th Fourier coefficient (`torusCoeff`, built from
the characters `torusChar k x = e^{2πi k·x}`).

**Fourier analysis on `𝕋^d`.**  Mathlib proves Parseval's identity on `𝕋^d` in
`Mathlib.Analysis.Fourier.AddCircleMulti`, whose compiled file is not part of this project's
Mathlib build; the part needed here is re-proved along the same lines (orthonormality by Fubini,
completeness by the Stone–Weierstrass theorem and the density of continuous functions in `L²`),
for the measure `volume` of `UnitAddTorus d` (`hasSum_sq_torusCoeff`,
`hasSum_torusCoeff_mul_torusChar`).

**Main results.**
* `hasSum_variance_rank1Lattice`: for `f ∈ L²(𝕋^d)`, the variance of `Q(u)` over a uniform shift
  is `∑_{k ∈ L^⊥ \ {0}} |f̂(k)|²`.  The Fourier coefficients of `Q` are
  `f̂(k) N⁻¹ ∑_{i<N} e^{2πi i k·z/N} = f̂(k) 1_{L^⊥}(k)` (`sum_torusChar_rank1Lattice`, the
  character sum), and Parseval's identity gives the formula.
* `rank1Lattice_randomShift`: with a uniform random shift `U`, every point `x_i + U` is uniform and
  `Q(U)` is an unbiased, square-integrable estimate of `∫ f` with that variance;
  `rank1Lattice_replicates`: `R` independent shifts (the paper's `R = 32`) give an unbiased
  average with variance `∑_{L^⊥ \ {0}} |f̂(k)|²/R`, and an unbiased estimate of it.
* `variance_rank1Lattice_le_variance`: the variance is at most `Var f = ∑_{k ≠ 0} |f̂(k)|²`, the
  variance of one Monte Carlo sample; `variance_rank1Lattice_re_torusChar`: for every lattice this
  is attained by `f(x) = cos(2π k·x)` with `k ∈ L^⊥ \ {0}` (then `Q = f`, of variance `1/2`, while
  the average of `N` independent samples has variance `1/(2N)`).
* `variance_rank1Lattice_le_of_coeff_le`, `variance_rank1Lattice_le_sq_tsum`,
  `variance_rank1Lattice_le_of_weighted`: bounds by the coefficients on `L^⊥ \ {0}` only: by
  `∑_{L^⊥ \ {0}} w(k)²` when `|f̂(k)| ≤ w(k)` there, by `(∑_{L^⊥ \ {0}} |f̂(k)|)²` for absolutely
  summable coefficients, and by `S/c` when `∑_k ρ(k)|f̂(k)|² = S` and `ρ ≥ c > 0` on `L^⊥ \ {0}`.
* `abs_rank1Lattice_sub_integral_le`: for continuous `f` with absolutely summable Fourier
  coefficients, `|Q(u) − ∫ f| ≤ ∑_{k ∈ L^⊥ \ {0}} |f̂(k)|` for **every** shift `u`.
* `mlqmcLattice_complexity`, `mlqmcLattice_complexity_lt_two`: the analogues of
  `mlqmc_complexity` and `mlqmc_complexity_lt_two` of `MlmcLean.QMC1D` for MLQMC with one randomly
  shifted rank-1 lattice per level in `d` dimensions, when the dual-lattice sums of the level
  corrections are at most `(c₂ 2^{−bℓ}/N)²` (the paper's best case `O(N_ℓ⁻¹)`);
  `mlqmcLattice_complexity_rate`: the same for sums at most `(c₂ 2^{−bℓ} N^{−r})²`, `r > 0`: cost
  `O(ε^{−max(1/r, g/a)})` when `rg < b` (`mlqmc_complexity_core_rate`, the real-analysis core,
  extends `mlqmc_complexity_core` from `r = 1` to every rate `r > 0`).

**Not formalised.**  The existence of good generating vectors (Korobov's construction, the
component-by-component construction, extensible lattices), i.e. the decay of the dual-lattice sums
for smooth periodic `f`, is out of scope: the MLQMC theorems assume it.  Sobol points and digital
scrambling are not treated.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ComplexConjugate

namespace MLMC

variable {d : Type*} [Fintype d]

/-! ### Fourier analysis on the torus `𝕋^d` -/

/-- **The characters of the torus** `𝕋^d` (Mathlib's `UnitAddTorus.mFourier`), the Fourier modes
behind the rank-1 lattice rules of Giles 2015, §3.5, p. 26: for `k ∈ ℤ^d`,
`e_k(x) = e^{2πi k·x} = ∏_j e^{2πi k_j x_j}`, as a continuous function `𝕋^d → ℂ`. -/
noncomputable def torusChar (k : d → ℤ) : C(UnitAddTorus d, ℂ) where
  toFun x := ∏ j, fourier (k j) (x j)
  continuous_toFun := by fun_prop

/-- `e_k(x) = ∏_j e^{2πi k_j x_j}`. -/
lemma torusChar_apply (k : d → ℤ) (x : UnitAddTorus d) :
    torusChar k x = ∏ j, fourier (k j) (x j) := rfl

/-- `e^{2πi n(s + t)} = e^{2πi ns} e^{2πi nt}` on the circle `ℝ/ℤ`. -/
lemma fourier_add_unit (n : ℤ) (s t : UnitAddCircle) :
    fourier n (s + t) = fourier n s * fourier n t := by
  rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- `e_k` is a character: `e_k(x + y) = e_k(x) e_k(y)`. -/
lemma torusChar_add (k : d → ℤ) (x y : UnitAddTorus d) :
    torusChar k (x + y) = torusChar k x * torusChar k y := by
  rw [torusChar_apply, torusChar_apply, torusChar_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => fourier_add_unit (k j) (x j) (y j)

/-- `e_{m+n} = e_m e_n`. -/
lemma torusChar_add_index (m n : d → ℤ) (x : UnitAddTorus d) :
    torusChar (m + n) x = torusChar m x * torusChar n x := by
  rw [torusChar_apply, torusChar_apply, torusChar_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => fourier_add

/-- `e_{−k} = conj e_k`. -/
lemma torusChar_neg_index (k : d → ℤ) (x : UnitAddTorus d) :
    torusChar (-k) x = conj (torusChar k x) := by
  rw [torusChar_apply, torusChar_apply, map_prod]
  exact Finset.prod_congr rfl fun j _ => fourier_neg

/-- `e_0 = 1`. -/
lemma torusChar_zero_index (x : UnitAddTorus d) : torusChar 0 x = 1 := by
  rw [torusChar_apply]
  exact Finset.prod_eq_one fun j _ => fourier_zero

/-- `|e_k(x)| = 1`. -/
lemma norm_torusChar (k : d → ℤ) (x : UnitAddTorus d) : ‖torusChar k x‖ = 1 := by
  rw [torusChar_apply, norm_prod]
  exact Finset.prod_eq_one fun j _ => Circle.norm_coe _

/-- `e_k(x) e_{−k}(x) = 1`. -/
lemma torusChar_mul_neg (k : d → ℤ) (x : UnitAddTorus d) :
    torusChar k x * torusChar (-k) x = 1 := by
  rw [← torusChar_add_index, add_neg_cancel, torusChar_zero_index]

/-- The sup norm of `e_k` is `1`. -/
lemma norm_torusChar_eq_one (k : d → ℤ) : ‖torusChar k‖ = 1 := by
  apply le_antisymm
  · exact (ContinuousMap.norm_le _ zero_le_one).2 fun x => (norm_torusChar k x).le
  · refine (le_of_eq ?_).trans ((torusChar k).norm_coe_le_norm 0)
    rw [norm_torusChar]

/-- `∫_{ℝ/ℤ} e^{2πi nt} dt = 1_{n = 0}`. -/
lemma integral_fourier_unitAddCircle (n : ℤ) :
    ∫ t : UnitAddCircle, fourier n t = if n = 0 then 1 else 0 := by
  have h := congr_fun (fourierCoeff_fourier (T := 1) n) 0
  rw [fourierCoeff, AddCircle.integral_haarAddCircle] at h
  simp only [neg_zero, fourier_zero, one_smul, inv_one] at h
  rw [h]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Pi.single_eq_of_ne (Ne.symm hn)]
    simp [hn]

/-- `∫_{𝕋^d} e_k = 1_{k = 0}` (Fubini). -/
lemma integral_torusChar (k : d → ℤ) :
    ∫ x : UnitAddTorus d, torusChar k x = if k = 0 then 1 else 0 := by
  have h := integral_fintype_prod_volume_eq_prod (𝕜 := ℂ) (E := fun _ : d => UnitAddCircle)
    (fun j t => fourier (k j) t)
  simp only [integral_fourier_unitAddCircle] at h
  rw [show (fun x : UnitAddTorus d => torusChar k x) =
    fun x : UnitAddTorus d => ∏ j, fourier (k j) (x j) from rfl, h, Finset.prod_boole]
  congr 1
  simp only [Finset.mem_univ, true_implies, funext_iff, Pi.zero_apply]

/-- The characters `e_k` are orthonormal in `L²(𝕋^d)`. -/
lemma orthonormal_torusChar :
    Orthonormal ℂ (fun k : d → ℤ => ContinuousMap.toLp (E := ℂ) 2 volume ℂ (torusChar k)) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [ContinuousMap.inner_toLp]
  have h : ∀ x, torusChar n x * conj (torusChar m x) = torusChar (n - m) x := fun x => by
    rw [← torusChar_neg_index, ← torusChar_add_index, sub_eq_add_neg]
  simp only [h, integral_torusChar, sub_eq_zero, eq_comm]

/-- `e_{δ_i}(x) = e^{2πi x_i}`. -/
lemma torusChar_single [DecidableEq d] (i : d) (x : UnitAddTorus d) :
    torusChar (Pi.single i 1) x = fourier 1 (x i) := by
  rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by
    rw [Pi.single_eq_of_ne hj, fourier_zero]) (fun h => absurd (Finset.mem_univ i) h),
    Pi.single_eq_same]

/-- The linear span of the characters is dense in `C(𝕋^d, ℂ)` (Stone–Weierstrass). -/
lemma span_torusChar_closure_eq_top :
    (Submodule.span ℂ (Set.range (torusChar (d := d)))).topologicalClosure = ⊤ := by
  classical
  let A : StarSubalgebra ℂ C(UnitAddTorus d, ℂ) :=
    { toSubalgebra := Algebra.adjoin ℂ (Set.range torusChar)
      star_mem' := by
        change Algebra.adjoin ℂ (Set.range torusChar) ≤
          star (Algebra.adjoin ℂ (Set.range (torusChar (d := d))))
        refine Algebra.adjoin_le ?_
        rintro _ ⟨n, rfl⟩
        refine Algebra.subset_adjoin ⟨-n, ?_⟩
        ext1 x
        rw [ContinuousMap.star_apply, torusChar_neg_index, starRingEnd_apply] }
  have hspan : Subalgebra.toSubmodule A.toSubalgebra =
      Submodule.span ℂ (Set.range torusChar) := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Set.Subset.trans (fun x => Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_)
      Submodule.subset_span
    · ext z
      rw [torusChar_zero_index, ContinuousMap.one_apply]
    · rintro _ _ _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
      refine ⟨m + n, ?_⟩
      ext z
      rw [torusChar_add_index, ContinuousMap.mul_apply]
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    rw [Ne, funext_iff, not_forall] at hxy
    obtain ⟨i, hi⟩ := hxy
    refine ⟨_, ⟨torusChar (Pi.single i 1), Algebra.subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
    dsimp only
    rw [torusChar_single, torusChar_single, fourier_one, fourier_one, Ne, Circle.coe_inj]
    contrapose hi
    exact AddCircle.injective_toCircle one_ne_zero hi
  rw [← hspan]
  exact congr_arg (fun B : StarSubalgebra ℂ C(UnitAddTorus d, ℂ) =>
    Subalgebra.toSubmodule B.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep)

/-- The linear span of the characters is dense in `L²(𝕋^d)`. -/
lemma span_torusCharLp_closure_eq_top :
    (Submodule.span ℂ (Set.range fun k : d → ℤ =>
      ContinuousMap.toLp (E := ℂ) 2 volume ℂ (torusChar k))).topologicalClosure = ⊤ := by
  have h := (ContinuousMap.toLp_denseRange ℂ (volume : Measure (UnitAddTorus d)) ℂ
    (p := 2) (by simp)).topologicalClosure_map_submodule (span_torusChar_closure_eq_top (d := d))
  rwa [Submodule.map_span, ← Set.range_comp] at h

/-- **The Fourier coefficients on the torus** `𝕋^d` (Mathlib's `UnitAddTorus.mFourierCoeff`, for
the uniform measure `volume`; they govern the error of the rank-1 lattice rules of Giles 2015, §3.5,
p. 26): for `g : 𝕋^d → ℂ` and `k ∈ ℤ^d`,
`ĝ(k) = ∫_{𝕋^d} e^{−2πi k·x} g(x) dx`.  (For a non-integrable `g` the Bochner integral is `0`; the
theorems assume `g ∈ L²`.) -/
noncomputable def torusCoeff (g : UnitAddTorus d → ℂ) (k : d → ℤ) : ℂ :=
  ∫ x, torusChar (-k) x * g x

/-- The characters form a Hilbert basis of `L²(𝕋^d)` whose coordinates are the Fourier
coefficients `torusCoeff`. -/
lemma exists_torusFourierBasis :
    ∃ b : HilbertBasis (d → ℤ) ℂ (Lp ℂ 2 (volume : Measure (UnitAddTorus d))),
      (∀ k, b k = ContinuousMap.toLp (E := ℂ) 2 volume ℂ (torusChar k)) ∧
      ∀ (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) k, b.repr f k = torusCoeff f k := by
  refine ⟨HilbertBasis.mk orthonormal_torusChar span_torusCharLp_closure_eq_top.ge,
    fun k => by rw [HilbertBasis.coe_mk], fun f k => ?_⟩
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.coe_mk, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure (UnitAddTorus d))
    (torusChar k)] with t ht
  rw [ht, torusChar_neg_index, RCLike.inner_apply, mul_comm]

/-- Parseval's identity on `𝕋^d` for elements of `L²`. -/
lemma hasSum_sq_torusCoeff_Lp (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    HasSum (fun k => ‖torusCoeff f k‖ ^ 2) (∫ t, ‖f t‖ ^ 2) := by
  obtain ⟨b, -, hrepr⟩ := exists_torusFourierBasis (d := d)
  have H₁ : HasSum (fun i => ‖b.repr f i‖ ^ 2) (‖b.repr f‖ ^ 2) := by
    apply_mod_cast lp.hasSum_norm ?_ (b.repr f)
    simp
  have H₂ : ‖b.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp
  have H₃ := congr_arg RCLike.re (@L2.inner_def (UnitAddTorus d) ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re (L2.integrable_inner f f)] at H₃
  simp only [← norm_sq_eq_re_inner] at H₃
  rw [H₂, H₃] at H₁
  simpa only [hrepr] using H₁

/-- **Parseval's identity on `𝕋^d`**: for `g ∈ L²(𝕋^d)`, `∑_k |ĝ(k)|² = ∫ |g|²`. -/
lemma hasSum_sq_torusCoeff {g : UnitAddTorus d → ℂ} (hg : MemLp g 2 volume) :
    HasSum (fun k => ‖torusCoeff g k‖ ^ 2) (∫ t, ‖g t‖ ^ 2) := by
  have h := hasSum_sq_torusCoeff_Lp (hg.toLp g)
  have hc : ∀ k, torusCoeff (hg.toLp g) k = torusCoeff g k := fun k =>
    integral_congr_ae (hg.coeFn_toLp.mono fun t ht => by dsimp only; rw [ht])
  have hi : ∫ t, ‖(hg.toLp g) t‖ ^ 2 = ∫ t, ‖g t‖ ^ 2 :=
    integral_congr_ae (hg.coeFn_toLp.mono fun t ht => by dsimp only; rw [ht])
  rw [hi] at h
  simpa only [hc] using h

/-- **Pointwise Fourier inversion on `𝕋^d`**: a continuous `g` with absolutely summable Fourier
coefficients is the sum of its Fourier series at every point (the proof shows that the series
converges uniformly). -/
lemma hasSum_torusCoeff_mul_torusChar {g : C(UnitAddTorus d, ℂ)}
    (hs : Summable fun k => ‖torusCoeff g k‖) (x : UnitAddTorus d) :
    HasSum (fun k => torusCoeff g k * torusChar k x) (g x) := by
  obtain ⟨b, hb, hrepr⟩ := exists_torusFourierBasis (d := d)
  have hL2 := b.hasSum_repr (ContinuousMap.toLp (E := ℂ) 2 volume ℂ g)
  have hc : ∀ k, b.repr (ContinuousMap.toLp (E := ℂ) 2 volume ℂ g) k = torusCoeff g k :=
    fun k => by
      rw [hrepr]
      exact integral_congr_ae ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
        (volume : Measure (UnitAddTorus d)) g).mono fun t ht => by dsimp only; rw [ht])
  simp only [hc, hb] at hL2
  have hsum : HasSum (fun k => torusCoeff g k • torusChar k) g := by
    refine ContinuousMap.hasSum_of_hasSum_Lp (p := 2) (μ := volume) (𝕜 := ℂ)
      (.of_norm ?_) ?_
    · simpa only [norm_smul, norm_torusChar_eq_one, mul_one] using hs
    · simpa only [Function.comp_def, map_smul] using hL2
  have h := (ContinuousMap.evalCLM ℂ x).hasSum hsum
  simpa only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul] using h

/-- The uniform measure `volume` on `𝕋^d` is a probability measure. -/
lemma isProbabilityMeasure_volume_torus :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus d)) := by
  have : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨by simp⟩
  infer_instance

/-- A measure that is carried to the uniform measure on `𝕋^d` is a probability measure. -/
lemma isProbabilityMeasure_of_measurePreserving_torus {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : Ω → UnitAddTorus d} (hU : MeasurePreserving U μ volume) :
    IsProbabilityMeasure μ := by
  have := isProbabilityMeasure_volume_torus (d := d)
  constructor
  rw [← Set.preimage_univ (f := U), hU.measure_preimage MeasurableSet.univ.nullMeasurableSet,
    measure_univ]

/-- `e_k g` is integrable when `g` is. -/
lemma integrable_torusChar_mul {g : UnitAddTorus d → ℂ} (hg : Integrable g volume) (k : d → ℤ) :
    Integrable (fun x => torusChar k x * g x) volume :=
  hg.bdd_mul (torusChar k).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_torusChar k x).le)

/-- Translation multiplies the Fourier coefficients by a character:
`(g(a + ·))^(k) = e_k(a) ĝ(k)`. -/
lemma torusCoeff_add_left (g : UnitAddTorus d → ℂ) (a : UnitAddTorus d) (k : d → ℤ) :
    torusCoeff (fun u => g (a + u)) k = torusChar k a * torusCoeff g k := by
  unfold torusCoeff
  rw [← integral_const_mul,
    ← integral_add_left_eq_self (μ := volume) (fun v => torusChar k a * (torusChar (-k) v * g v)) a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [torusChar_add, ← mul_assoc, ← mul_assoc, torusChar_mul_neg, one_mul]

/-- The `0`-th Fourier coefficient of a real function is its integral. -/
lemma torusCoeff_zero_ofReal (f : UnitAddTorus d → ℝ) :
    torusCoeff (fun u => (f u : ℂ)) 0 = ((∫ u, f u : ℝ) : ℂ) := by
  unfold torusCoeff
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [neg_zero, torusChar_zero_index, one_mul]

/-! ### The rank-1 lattice and its dual lattice -/

/-- **The rank-1 lattice** (Giles 2015, §3.5, p. 26: "rank-1 lattices (Dick et al. 2007)"; §2.7,
p. 20): for a generating vector `z ∈ ℤ^d`, `N ∈ ℕ` and `i ∈ ℕ`, the point
`x_i = i z/N mod 1 ∈ 𝕋^d`, i.e. `frac(i z/N)` coordinatewise.  (For `N = 0`, Lean's `i/0 = 0`
gives `x_i = 0`; the theorems assume `N ≥ 1`.) -/
noncomputable def rank1Lattice (z : d → ℤ) (N i : ℕ) : UnitAddTorus d :=
  fun j => (((i : ℝ) * z j / N : ℝ) : UnitAddCircle)

omit [Fintype d] in
/-- The shifted lattice points are `frac(i z/N + u)` coordinatewise. -/
lemma rank1Lattice_add_coe (z : d → ℤ) (N i : ℕ) (u : d → ℝ) :
    rank1Lattice z N i + (fun j => (u j : UnitAddCircle)) =
      fun j => ((Int.fract ((i : ℝ) * z j / N + u j) : ℝ) : UnitAddCircle) := by
  funext j
  rw [Pi.add_apply, AddCircle.coe_fract, rank1Lattice, AddCircle.coe_add]

/-- **The dual lattice** of the rank-1 lattice (Giles 2015, §3.5, p. 26: "rank-1 lattices") with
generating vector `z ∈ ℤ^d` and `N` points:
`L^⊥ = {k ∈ ℤ^d : k·z ≡ 0 mod N}`, the frequencies `k` for which `e^{2πi k·x}` is constant on
the lattice.  (For `N = 0` it is `{k : k·z = 0}`; the theorems assume `N ≥ 1`.) -/
def dualLattice (z : d → ℤ) (N : ℕ) : Set (d → ℤ) := {k | (N : ℤ) ∣ ∑ j, k j * z j}

/-- `0 ∈ L^⊥`. -/
lemma zero_mem_dualLattice (z : d → ℤ) (N : ℕ) : (0 : d → ℤ) ∈ dualLattice z N := by
  simp [dualLattice]

/-- For `N = 1`, `L^⊥ = ℤ^d`. -/
lemma dualLattice_one (z : d → ℤ) : dualLattice z 1 = Set.univ :=
  Set.eq_univ_of_forall fun k => by
    change ((1 : ℕ) : ℤ) ∣ ∑ j, k j * z j
    rw [Nat.cast_one]
    exact one_dvd _

/-- `e_k(x_i) = ω^i` with `ω = e^{2πi k·z/N}`. -/
lemma torusChar_rank1Lattice (k z : d → ℤ) (N i : ℕ) :
    torusChar k (rank1Lattice z N i) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ j, k j * z j : ℤ) : ℂ) / N) ^ i := by
  rw [torusChar_apply, ← Complex.exp_nat_mul]
  have h : ∀ j, fourier (k j) (rank1Lattice z N i j) =
      Complex.exp (2 * Real.pi * Complex.I * (k j) * (((i : ℝ) * z j / N : ℝ) : ℂ) / 1) :=
    fun j => fourier_coe_apply
  rw [Finset.prod_congr rfl fun j _ => h j, ← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `e_k = 1` on the lattice when `k ∈ L^⊥`. -/
lemma torusChar_rank1Lattice_of_mem {k z : d → ℤ} {N : ℕ} (hk : k ∈ dualLattice z N) (i : ℕ) :
    torusChar k (rank1Lattice z N i) = 1 := by
  obtain ⟨q, hq⟩ := hk
  rw [torusChar_rank1Lattice]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [Nat.cast_zero, div_zero, Complex.exp_zero, one_pow]
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((∑ j, k j * z j : ℤ) : ℂ) / N) = 1 := by
    rw [hq, ← Complex.exp_int_mul_two_pi_mul_I q]
    congr 1
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    push_cast
    field_simp
  rw [h1, one_pow]

/-- **The character sum**: `∑_{i<N} e^{2πi i k·z/N} = N 1_{k ∈ L^⊥}` for `N ≥ 1` (a geometric sum
of `N`-th roots of unity). -/
lemma sum_torusChar_rank1Lattice (k z : d → ℤ) {N : ℕ} (hN : 0 < N) :
    ∑ i ∈ range N, torusChar k (rank1Lattice z N i) =
      if (N : ℤ) ∣ ∑ j, k j * z j then (N : ℂ) else 0 := by
  simp_rw [torusChar_rank1Lattice]
  set m : ℤ := ∑ j, k j * z j with hm
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  split_ifs with hdvd
  · obtain ⟨q, hq⟩ := hdvd
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / N) = 1 := by
      rw [hq, ← Complex.exp_int_mul_two_pi_mul_I q]
      congr 1
      push_cast
      field_simp
    simp [h1]
  · have h1 : Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / N) ≠ 1 := by
      intro h
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
      apply hdvd
      refine ⟨n, ?_⟩
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : (m : ℂ) = (N : ℂ) * n :=
        calc (m : ℂ) = 2 * Real.pi * Complex.I * (m : ℂ) / N * N / (2 * Real.pi * Complex.I) := by
              field_simp
          _ = n * (2 * Real.pi * Complex.I) * N / (2 * Real.pi * Complex.I) := by rw [hn]
          _ = N * n := by field_simp
      exact_mod_cast h2
    have h2 : Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / N) ^ N = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I m]
      congr 1
      field_simp
    rw [geom_sum_eq h1, h2, sub_self, zero_div]

/-- The Fourier coefficients of a shifted QMC average:
`Q̂(k) = N⁻¹ (∑_{i<N} e_k(x_i)) f̂(k)`. -/
lemma torusCoeff_shiftedQMC {f : UnitAddTorus d → ℝ} (hf : Integrable f volume)
    (x : ℕ → UnitAddTorus d) (N : ℕ) (k : d → ℤ) :
    torusCoeff (fun u => (shiftedQMC f x N u : ℂ)) k =
      (N : ℂ)⁻¹ * (∑ i ∈ range N, torusChar k (x i)) * torusCoeff (fun u => (f u : ℂ)) k := by
  have hint : ∀ i, Integrable (fun u => torusChar (-k) u * (f (x i + u) : ℂ)) volume := fun i =>
    integrable_torusChar_mul
      (((measurePreserving_add_left volume (x i)).integrable_comp_of_integrable hf).ofReal) _
  have e : ∀ u, torusChar (-k) u * (shiftedQMC f x N u : ℂ) =
      (N : ℂ)⁻¹ * ∑ i ∈ range N, torusChar (-k) u * (f (x i + u) : ℂ) := fun u => by
    unfold shiftedQMC
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hc : ∀ i, ∫ u, torusChar (-k) u * (f (x i + u) : ℂ) =
      torusChar k (x i) * torusCoeff (fun u => (f u : ℂ)) k := fun i =>
    torusCoeff_add_left (fun u => (f u : ℂ)) (x i) k
  unfold torusCoeff at hc ⊢
  simp only [e]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i, Finset.sum_congr rfl
    fun i _ => hc i, ← Finset.sum_mul, mul_assoc]

/-- The randomly shifted rank-1 lattice rule keeps exactly the Fourier coefficients on the dual
lattice: `Q̂(k) = 1_{L^⊥}(k) f̂(k)`. -/
lemma torusCoeff_rank1Lattice {f : UnitAddTorus d → ℝ} (hf : Integrable f volume) (z : d → ℤ)
    {N : ℕ} (hN : 0 < N) (k : d → ℤ) :
    torusCoeff (fun u => (shiftedQMC f (rank1Lattice z N) N u : ℂ)) k =
      (dualLattice z N).indicator (torusCoeff fun u => (f u : ℂ)) k := by
  rw [torusCoeff_shiftedQMC hf, sum_torusChar_rank1Lattice k z hN]
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  by_cases hk : (N : ℤ) ∣ ∑ j, k j * z j
  · have hk' : k ∈ dualLattice z N := hk
    rw [if_pos hk, Set.indicator_of_mem hk', inv_mul_cancel₀ hN', one_mul]
  · have hk' : k ∉ dualLattice z N := hk
    rw [if_neg hk, Set.indicator_of_notMem hk', mul_zero, zero_mul]

/-! ### The variance of the randomly shifted lattice rule -/

/-- **The variance of a randomly shifted rank-1 lattice rule is the sum of `|f̂(k)|²` over the
nonzero dual lattice** (Giles 2015, §3.5, p. 26: QMC points constructed with "rank-1 lattices
(Dick et al. 2007)", randomised by "a random shift (for rank-1 lattice rules)"; p. 27: "the variance
of their average, `V_ℓ`").  Let `f ∈ L²(𝕋^d)` be real, `z ∈ ℤ^d` and `N ≥ 1`.  Then the variance
of the shifted lattice average `Q(u) = N⁻¹ ∑_{i<N} f(frac(i z/N + u))` over a uniformly distributed
shift `u ∈ 𝕋^d` is
`Var_u[Q(u)] = ∑_{k ∈ L^⊥ \ {0}} |f̂(k)|²`, `L^⊥ = {k ∈ ℤ^d : k·z ≡ 0 mod N}`,
the series converging (`HasSum`).  Proof: `Q̂(k) = f̂(k) N⁻¹ ∑_{i<N} e^{2πi i k·z/N} =
1_{L^⊥}(k) f̂(k)` (`torusCoeff_rank1Lattice`, the character sum `sum_torusChar_rank1Lattice`),
Parseval's identity `∫ Q² = ∑_k |Q̂(k)|²` (`hasSum_sq_torusCoeff`), and `∫ Q = f̂(0) = ∫ f`. -/
theorem hasSum_variance_rank1Lattice {f : UnitAddTorus d → ℝ} (hf : MemLp f 2 volume)
    (z : d → ℤ) {N : ℕ} (hN : 0 < N) :
    HasSum ((dualLattice z N \ {0}).indicator fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖ ^ 2)
      (variance (shiftedQMC f (rank1Lattice z N) N) volume) := by
  have := isProbabilityMeasure_volume_torus (d := d)
  have hf1 : Integrable f volume := hf.integrable one_le_two
  have hQ2 := memLp_shiftedQMC hf (rank1Lattice z N) N
  have hpar : HasSum (fun k => ‖torusCoeff
      (fun u => ((shiftedQMC f (rank1Lattice z N) N u : ℝ) : ℂ)) k‖ ^ 2)
      (∫ t, ‖((shiftedQMC f (rank1Lattice z N) N t : ℝ) : ℂ)‖ ^ 2) :=
    hasSum_sq_torusCoeff (hQ2.ofReal (K := ℂ))
  have hint : ∫ t, ‖((shiftedQMC f (rank1Lattice z N) N t : ℝ) : ℂ)‖ ^ 2 =
      ∫ t, shiftedQMC f (rank1Lattice z N) N t ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h1 : HasSum ((dualLattice z N).indicator fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖ ^ 2)
      (∫ t, shiftedQMC f (rank1Lattice z N) N t ^ 2) := by
    rw [← hint]
    refine hpar.congr_fun fun k => ?_
    rw [torusCoeff_rank1Lattice hf1 z hN]
    by_cases hk : k ∈ dualLattice z N
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, norm_zero,
        zero_pow two_ne_zero]
  have h2 := hasSum_ite_eq (0 : d → ℤ) (‖torusCoeff (fun x => (f x : ℂ)) 0‖ ^ 2)
  have hmean : ∫ t, shiftedQMC f (rank1Lattice z N) N t = ∫ t, f t :=
    (shiftedQMC_unbiased (MeasurePreserving.id volume) _ hf1 hN).2.2
  have key : ((dualLattice z N \ {0}).indicator fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖ ^ 2)
      = fun k => (dualLattice z N).indicator (fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖ ^ 2) k
        - if k = 0 then ‖torusCoeff (fun x => (f x : ℂ)) 0‖ ^ 2 else 0 := by
    funext k
    by_cases hk0 : k = 0
    · subst hk0
      rw [Set.indicator_of_notMem (fun h => h.2 rfl),
        Set.indicator_of_mem (zero_mem_dualLattice z N), if_pos rfl, sub_self]
    · rw [if_neg hk0, sub_zero]
      by_cases hk : k ∈ dualLattice z N
      · rw [Set.indicator_of_mem (show k ∈ dualLattice z N \ {0} from ⟨hk, hk0⟩),
          Set.indicator_of_mem hk]
      · rw [Set.indicator_of_notMem (fun h => hk h.1), Set.indicator_of_notMem hk]
  have hv : variance (shiftedQMC f (rank1Lattice z N) N) volume =
      (∫ t, shiftedQMC f (rank1Lattice z N) N t ^ 2) -
        ‖torusCoeff (fun x => (f x : ℂ)) 0‖ ^ 2 := by
    rw [variance_eq_sub hQ2, torusCoeff_zero_ofReal, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, ← hmean]
    simp only [Pi.pow_apply]
  rw [key, hv]
  exact h1.sub h2

omit [Fintype d] in
/-- With one point (`N = 1`) the rank-1 lattice rule is `f` itself. -/
lemma shiftedQMC_rank1Lattice_one (f : UnitAddTorus d → ℝ) (z : d → ℤ) :
    shiftedQMC f (rank1Lattice z 1) 1 = f := by
  funext u
  have h0 : rank1Lattice z 1 0 = 0 := by
    funext j
    rw [rank1Lattice, Nat.cast_zero, zero_mul, zero_div, QuotientAddGroup.mk_zero]
    rfl
  rw [shiftedQMC, Finset.sum_range_one, h0, zero_add, Nat.cast_one, inv_one, one_mul]

/-- The variance of one Monte Carlo sample in Fourier terms: `Var f = ∑_{k ≠ 0} |f̂(k)|²` (the
case `N = 1` of `hasSum_variance_rank1Lattice`). -/
lemma hasSum_variance_torus {f : UnitAddTorus d → ℝ} (hf : MemLp f 2 volume) :
    HasSum (({0}ᶜ : Set (d → ℤ)).indicator fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖ ^ 2)
      (variance f volume) := by
  have h := hasSum_variance_rank1Lattice hf (0 : d → ℤ) one_pos
  rwa [shiftedQMC_rank1Lattice_one, dualLattice_one, ← Set.compl_eq_univ_sdiff] at h

/-- **A random shift makes the rank-1 lattice rule an unbiased estimator, with variance
`∑_{L^⊥ \ {0}} |f̂(k)|²`** (Giles 2015, §3.5, p. 26: "To regain a confidence interval one uses
randomised QMC in which the set of points is gives [sic] a random shift (for rank-1 lattice
rules)").  Let `U` be uniformly distributed on `𝕋^d` (its law is `volume`), `z ∈ ℤ^d`, `N ≥ 1` and
`f ∈ L²(𝕋^d)` real.  Then
* every shifted point `x_i + U = frac(i z/N + U)` is uniformly distributed on `𝕋^d`;
* `Q(U) = N⁻¹ ∑_{i<N} f(x_i + U)` is square-integrable, with `E[Q(U)] = ∫_{𝕋^d} f`;
* `Var[Q(U)] = ∑_{k ∈ L^⊥ \ {0}} |f̂(k)|²` (`hasSum_variance_rank1Lattice`). -/
theorem rank1Lattice_randomShift {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Ω → UnitAddTorus d} (hU : MeasurePreserving U μ volume) (z : d → ℤ)
    {f : UnitAddTorus d → ℝ} (hf : MemLp f 2 volume) {N : ℕ} (hN : 0 < N) :
    (∀ i, MeasurePreserving (fun ω => rank1Lattice z N i + U ω) μ volume) ∧
      MemLp (fun ω => shiftedQMC f (rank1Lattice z N) N (U ω)) 2 μ ∧
      ∫ ω, shiftedQMC f (rank1Lattice z N) N (U ω) ∂μ = ∫ y, f y ∧
      HasSum ((dualLattice z N \ {0}).indicator fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖ ^ 2)
        (variance (fun ω => shiftedQMC f (rank1Lattice z N) N (U ω)) μ) := by
  have hQ2 := memLp_shiftedQMC hf (rank1Lattice z N) N
  obtain ⟨hpts, -, hmean⟩ :=
    shiftedQMC_unbiased hU (rank1Lattice z N) (hf.integrable one_le_two) hN
  refine ⟨hpts, hQ2.comp_measurePreserving hU, hmean, ?_⟩
  rw [hU.variance_fun_comp hQ2.aestronglyMeasurable.aemeasurable]
  exact hasSum_variance_rank1Lattice hf z hN

/-- **`R` independent random shifts: an unbiased average with variance
`∑_{L^⊥ \ {0}} |f̂(k)|²/R`, and an unbiased variance estimate** (Giles 2015, §3.5, pp. 26–27:
"Using 32 sets of points, each collectively randomised, yields 32 set averages for the quantity of
interest, `Y_ℓ`, and from these 32 random independent values the variance of their average, `V_ℓ`,
can be estimated in the usual way").  Let `U_0, U_1, …` be mutually independent shifts, each
uniform on `𝕋^d` (as in `randomShift_replicates`), `f` measurable and square-integrable,
`z ∈ ℤ^d`, `N ≥ 1` and `R ≥ 1` (the paper's `R = 32`).  For the set averages
`Y_r = N⁻¹ ∑_{i<N} f(frac(i z/N + U_r))` and their average `Ȳ = R⁻¹ ∑_{r<R} Y_r`:
* `E[Ȳ] = ∫_{𝕋^d} f`;
* `V[Ȳ] = ∑_{k ∈ L^⊥ \ {0}} |f̂(k)|²/R`;
* for `R ≥ 2`, `E[(R(R − 1))⁻¹ ∑_{r<R} (Y_r − Ȳ)²] = ∑_{k ∈ L^⊥ \ {0}} |f̂(k)|²/R`. -/
theorem rank1Lattice_replicates {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : ℕ → Ω → UnitAddTorus d} (hU : ∀ r, MeasurePreserving (U r) μ volume)
    (hUind : iIndepFun U μ) (z : d → ℤ) {f : UnitAddTorus d → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) {N R : ℕ} (hN : 0 < N) (hR : 0 < R) :
    ∫ ω, (R : ℝ)⁻¹ * ∑ r ∈ range R, shiftedQMC f (rank1Lattice z N) N (U r ω) ∂μ =
        ∫ y, f y ∧
      HasSum (fun k => (dualLattice z N \ {0}).indicator
          (fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖ ^ 2) k / R)
        (variance (fun ω => (R : ℝ)⁻¹ * ∑ r ∈ range R,
          shiftedQMC f (rank1Lattice z N) N (U r ω)) μ) ∧
      (2 ≤ R → HasSum (fun k => (dualLattice z N \ {0}).indicator
          (fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖ ^ 2) k / R)
        (∫ ω, ((R : ℝ) * (R - 1))⁻¹ * ∑ r ∈ range R,
          (shiftedQMC f (rank1Lattice z N) N (U r ω) -
            (R : ℝ)⁻¹ * ∑ s ∈ range R, shiftedQMC f (rank1Lattice z N) N (U s ω)) ^ 2 ∂μ)) := by
  have := isProbabilityMeasure_of_measurePreserving_torus (hU 0)
  obtain ⟨-, -, -, hmean, hvar, hest⟩ :=
    randomShift_replicates hU hUind (rank1Lattice z N) hfm hf hN hR
  have h := (hasSum_variance_rank1Lattice hf z hN).div_const (R : ℝ)
  refine ⟨hmean, ?_, fun hR2 => ?_⟩
  · rw [hvar]
    exact h
  · rw [hest hR2]
    exact h

/-! ### Consequences -/

/-- **A randomly shifted rank-1 lattice rule is never worse than one Monte Carlo sample**
(Giles 2015, §1, p. 2: in QMC "the samples are not chosen randomly and independently, but are
instead selected very carefully to reduce the error").  For every `f ∈ L²(𝕋^d)`, `z ∈ ℤ^d` and
`N ≥ 1`, the variance over a uniform shift of the lattice average is at most `Var f`, the variance
of `f(U)` for one uniform sample `U`: `∑_{L^⊥ \ {0}} |f̂(k)|² ≤ ∑_{k ≠ 0} |f̂(k)|² = Var f`
(`hasSum_variance_torus`).  It can be equal, and so worse than the `Var f/N` of `N` independent
samples, for every lattice (`variance_rank1Lattice_re_torusChar`). -/
theorem variance_rank1Lattice_le_variance {f : UnitAddTorus d → ℝ} (hf : MemLp f 2 volume)
    (z : d → ℤ) {N : ℕ} (hN : 0 < N) :
    variance (shiftedQMC f (rank1Lattice z N) N) volume ≤ variance f volume :=
  hasSum_le (fun k => Set.indicator_le_indicator_of_subset (fun _ hk => hk.2)
    (fun _ => sq_nonneg _) k) (hasSum_variance_rank1Lattice hf z hN) (hasSum_variance_torus hf)

/-- **Without conditions on the integrand a lattice rule need not beat Monte Carlo** (Giles 2015,
§1, p. 2: "In the best cases, the error may be `O(N⁻¹)`"; §3.5, p. 26: "In the best cases …
`O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})`").  For every generating vector `z ∈ ℤ^d`, every
`N ≥ 1` and every nonzero `k ∈ L^⊥`, the integrand `f(x) = Re e^{2πi k·x} = cos(2π k·x)` is
reproduced by the shifted lattice rule, `Q = f`, and `Var f = 1/2`.  So the randomly shifted
lattice rule has variance `1/2` (equality in `variance_rank1Lattice_le_variance`), while the average
of `N` independent uniform samples has variance `1/(2N)` (`variance_sample_mean`): the best case
needs integrands whose Fourier coefficients on `L^⊥ \ {0}` are small. -/
theorem variance_rank1Lattice_re_torusChar (z : d → ℤ) {N : ℕ} (hN : 0 < N) {k : d → ℤ}
    (hk : k ∈ dualLattice z N) (hk0 : k ≠ 0) :
    shiftedQMC (fun x => (torusChar k x).re) (rank1Lattice z N) N =
        (fun x => (torusChar k x).re) ∧
      variance (fun x => (torusChar k x).re) volume = 1 / 2 := by
  have := isProbabilityMeasure_volume_torus (d := d)
  refine ⟨funext fun u => ?_, ?_⟩
  · have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    unfold shiftedQMC
    simp only [torusChar_add, torusChar_rank1Lattice_of_mem hk, one_mul, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    field_simp
  · have hint : ∀ m : d → ℤ, Integrable (fun x => torusChar m x) volume := fun m => by
      simpa only [mul_one] using integrable_torusChar_mul (integrable_const (1 : ℂ)) m
    have hm : ∀ m : d → ℤ, m ≠ 0 → ∫ x, (torusChar m x).re = 0 := fun m hm => by
      have h := Complex.reCLM.integral_comp_comm (hint m)
      simp only [Complex.reCLM_apply] at h
      rw [h, integral_torusChar, if_neg hm, Complex.zero_re]
    have hsq : ∀ x, (torusChar k x).re ^ 2 = 1 / 2 + (torusChar (k + k) x).re / 2 := fun x => by
      have h1 := norm_torusChar k x
      rw [Complex.norm_def, Real.sqrt_eq_one, Complex.normSq_apply] at h1
      rw [torusChar_add_index, Complex.mul_re]
      nlinarith [h1]
    have hkk : k + k ≠ 0 := by
      intro h
      apply hk0
      funext j
      have := congr_fun h j
      simp only [Pi.add_apply, Pi.zero_apply] at this
      simp only [Pi.zero_apply]
      omega
    have hmem : MemLp (fun x => (torusChar k x).re) 2 volume :=
      MemLp.of_bound (torusChar k).continuous.aestronglyMeasurable.re 1
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          exact (Complex.abs_re_le_norm _).trans (norm_torusChar k x).le)
    rw [variance_eq_sub hmem]
    simp only [Pi.pow_apply, hsq]
    have hre : Integrable (fun x => (torusChar (k + k) x).re) volume := (hint (k + k)).re
    rw [hm k hk0, integral_add (integrable_const _) (hre.div_const 2), integral_const,
      integral_div, hm (k + k) hkk]
    simp

/-- **The variance is bounded by majorants of the Fourier coefficients on `L^⊥ \ {0}`**
(Giles 2015, §1, p. 2: "In the best cases, the error may be `O(N⁻¹)`, up to logarithmic terms").
If `|f̂(k)| ≤ w(k)` for every `k ∈ L^⊥ \ {0}` and `∑_{k ∈ L^⊥ \ {0}} w(k)² = W`, then the
variance of the randomly shifted rank-1 lattice rule is at most `W`.  For example, for the
Korobov majorants `w(k) = C ∏_j max(1, |k_j|)^{−α}`, `α > 1/2`, the bound is `C²` times the
classical figure of merit `∑_{L^⊥ \ {0}} ∏_j max(1, |k_j|)^{−2α}` of the generating vector
(whose decay in `N` for good generating vectors is not proved here). -/
theorem variance_rank1Lattice_le_of_coeff_le {f : UnitAddTorus d → ℝ} (hf : MemLp f 2 volume)
    (z : d → ℤ) {N : ℕ} (hN : 0 < N) {w : (d → ℤ) → ℝ} {W : ℝ}
    (hw : ∀ k ∈ dualLattice z N \ {0}, ‖torusCoeff (fun x => (f x : ℂ)) k‖ ≤ w k)
    (hW : HasSum ((dualLattice z N \ {0}).indicator fun k => w k ^ 2) W) :
    variance (shiftedQMC f (rank1Lattice z N) N) volume ≤ W := by
  refine hasSum_le (fun k => ?_) (hasSum_variance_rank1Lattice hf z hN) hW
  by_cases hk : k ∈ dualLattice z N \ {0}
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
    exact pow_le_pow_left₀ (norm_nonneg _) (hw k hk) 2
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk]

/-- **For absolutely summable Fourier coefficients the variance is at most the square of their
tail on `L^⊥ \ {0}`** (Giles 2015, §1, p. 2: "In the best cases, the error may be `O(N⁻¹)`").
If `∑_{k ∈ L^⊥ \ {0}} |f̂(k)|` converges, the variance of the randomly shifted rank-1 lattice rule
is at most `(∑_{k ∈ L^⊥ \ {0}} |f̂(k)|)²` (a sum of squares of nonnegative terms is at most the
square of their sum).  For continuous `f` the same tail bounds the error for every shift
(`abs_rank1Lattice_sub_integral_le`). -/
theorem variance_rank1Lattice_le_sq_tsum {f : UnitAddTorus d → ℝ} (hf : MemLp f 2 volume)
    (z : d → ℤ) {N : ℕ} (hN : 0 < N)
    (hs : Summable ((dualLattice z N \ {0}).indicator fun k =>
      ‖torusCoeff (fun x => (f x : ℂ)) k‖)) :
    variance (shiftedQMC f (rank1Lattice z N) N) volume ≤
      (∑' k, (dualLattice z N \ {0}).indicator
        (fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖) k) ^ 2 := by
  set a := (dualLattice z N \ {0}).indicator fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖
  have ha : ∀ k, 0 ≤ a k := fun k => Set.indicator_nonneg (fun _ _ => norm_nonneg _) k
  have hle : ∀ k, a k ≤ ∑' j, a j := fun k => hs.le_tsum k fun j _ => ha j
  rw [sq]
  refine hasSum_le (fun k => ?_) (hasSum_variance_rank1Lattice hf z hN)
    (hs.hasSum.mul_right (∑' j, a j))
  have e : (dualLattice z N \ {0}).indicator
      (fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖ ^ 2) k = a k ^ 2 := by
    by_cases hk : k ∈ dualLattice z N \ {0}
    · simp only [a, Set.indicator_of_mem hk]
    · simp only [a, Set.indicator_of_notMem hk]
      ring
  rw [e, sq]
  exact mul_le_mul_of_nonneg_left (hle k) (ha k)

/-- **In a weighted space the variance is the weighted norm divided by the smallest weight on
`L^⊥ \ {0}`** (Giles 2015, §1, p. 2: "In the best cases, the error may be `O(N⁻¹)`, up to
logarithmic terms").  Let `ρ ≥ 0` be weights with `∑_k ρ(k) |f̂(k)|² = S` (the squared norm of `f`
in the weighted space) and `ρ(k) ≥ c > 0` for every `k ∈ L^⊥ \ {0}`.  Then the variance of the
randomly shifted rank-1 lattice rule is at most `S/c`.  For the Korobov weights
`ρ(k) = ∏_j max(1, |k_j|)^{2α}` the best `c` is `ϱ^{2α}`, where
`ϱ = min_{k ∈ L^⊥ \ {0}} ∏_j max(1, |k_j|)` is the Zaremba index of the generating vector (whose
growth with `N` is not proved here). -/
theorem variance_rank1Lattice_le_of_weighted {f : UnitAddTorus d → ℝ} (hf : MemLp f 2 volume)
    (z : d → ℤ) {N : ℕ} (hN : 0 < N) {ρ : (d → ℤ) → ℝ} {c S : ℝ} (hc : 0 < c)
    (hρ : ∀ k, 0 ≤ ρ k) (hρc : ∀ k ∈ dualLattice z N \ {0}, c ≤ ρ k)
    (hS : HasSum (fun k => ρ k * ‖torusCoeff (fun x => (f x : ℂ)) k‖ ^ 2) S) :
    variance (shiftedQMC f (rank1Lattice z N) N) volume ≤ S / c := by
  refine hasSum_le (fun k => ?_) (hasSum_variance_rank1Lattice hf z hN) (hS.div_const c)
  by_cases hk : k ∈ dualLattice z N \ {0}
  · rw [Set.indicator_of_mem hk, le_div_iff₀ hc, mul_comm]
    exact mul_le_mul_of_nonneg_right (hρc k hk) (sq_nonneg _)
  · rw [Set.indicator_of_notMem hk]
    exact div_nonneg (mul_nonneg (hρ k) (sq_nonneg _)) hc.le

/-- **The error bound for every shift: `|Q(u) − ∫ f| ≤ ∑_{k ∈ L^⊥ \ {0}} |f̂(k)|`** (Giles 2015,
§1, p. 2: "In the best cases, the error may be `O(N⁻¹)`, up to logarithmic terms"; §3.5, p. 26:
"In the best cases, this results in the approximate numerical integration error being `O(N_ℓ⁻¹)`
rather than the usual `O(N_ℓ^{−1/2})` error which comes from Monte Carlo sampling").  Let
`f : 𝕋^d → ℝ` be continuous with absolutely summable Fourier coefficients, `z ∈ ℤ^d` and
`N ≥ 1`.  Then for every shift `u ∈ 𝕋^d` (deterministic, not only on average)
`|N⁻¹ ∑_{i<N} f(frac(i z/N + u)) − ∫_{𝕋^d} f| ≤ ∑_{k ∈ L^⊥ \ {0}} |f̂(k)|`.
So the error is `O(N⁻¹)` whenever the coefficient tail on `L^⊥ \ {0}` is (the existence of
generating vectors with this property for smooth `f` is not proved here).  Proof: the Fourier
series of `f` converges at every point (`hasSum_torusCoeff_mul_torusChar`), the lattice average
keeps the terms with `k ∈ L^⊥` (`sum_torusChar_rank1Lattice`), and the `k = 0` term is `∫ f`. -/
theorem abs_rank1Lattice_sub_integral_le {f : UnitAddTorus d → ℝ} (hf : Continuous f)
    (hs : Summable fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖) (z : d → ℤ) {N : ℕ}
    (hN : 0 < N) (u : UnitAddTorus d) :
    |shiftedQMC f (rank1Lattice z N) N u - ∫ x, f x| ≤
      ∑' k, (dualLattice z N \ {0}).indicator (fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖) k := by
  set g : C(UnitAddTorus d, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp hf⟩
  have hser : ∀ x, HasSum (fun k => torusCoeff (fun x => (f x : ℂ)) k * torusChar k x)
      (f x : ℂ) := fun x => hasSum_torusCoeff_mul_torusChar (g := g) hs x
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  -- the shifted rule keeps the terms on the dual lattice
  have hQ : HasSum (fun k => (dualLattice z N).indicator
      (fun k => torusCoeff (fun x => (f x : ℂ)) k * torusChar k u) k)
      ((shiftedQMC f (rank1Lattice z N) N u : ℝ) : ℂ) := by
    have h := (hasSum_sum fun i (_ : i ∈ range N) => hser (rank1Lattice z N i + u)).mul_left
      ((N : ℂ)⁻¹)
    have e1 : ((shiftedQMC f (rank1Lattice z N) N u : ℝ) : ℂ) =
        (N : ℂ)⁻¹ * ∑ i ∈ range N, (f (rank1Lattice z N i + u) : ℂ) := by
      unfold shiftedQMC
      push_cast
      rfl
    rw [e1]
    refine h.congr_fun fun k => ?_
    simp only [torusChar_add]
    rw [← Finset.mul_sum]
    simp only [mul_comm (torusChar k (rank1Lattice z N _)) (torusChar k u), ← mul_assoc]
    rw [← Finset.mul_sum, sum_torusChar_rank1Lattice k z hN]
    by_cases hk : k ∈ dualLattice z N
    · have hk' : (N : ℤ) ∣ ∑ j, k j * z j := hk
      rw [Set.indicator_of_mem hk, if_pos hk']
      field_simp
    · have hk' : ¬ (N : ℤ) ∣ ∑ j, k j * z j := hk
      rw [Set.indicator_of_notMem hk, if_neg hk', mul_zero, mul_zero]
  -- the `k = 0` term is the integral
  have h0 : torusCoeff (fun x => (f x : ℂ)) 0 * torusChar 0 u = ((∫ x, f x : ℝ) : ℂ) := by
    rw [torusChar_zero_index, mul_one, torusCoeff_zero_ofReal]
  have hE : HasSum (fun k => (dualLattice z N \ {0}).indicator
      (fun k => torusCoeff (fun x => (f x : ℂ)) k * torusChar k u) k)
      (((shiftedQMC f (rank1Lattice z N) N u - ∫ x, f x : ℝ)) : ℂ) := by
    have h2 := hasSum_ite_eq (0 : d → ℤ) (((∫ x, f x : ℝ)) : ℂ)
    have h3 := hQ.sub h2
    rw [Complex.ofReal_sub]
    refine h3.congr_fun fun k => ?_
    by_cases hk0 : k = 0
    · subst hk0
      rw [Set.indicator_of_notMem (fun h => h.2 rfl),
        Set.indicator_of_mem (zero_mem_dualLattice z N), if_pos rfl, h0, sub_self]
    · rw [if_neg hk0, sub_zero]
      by_cases hk : k ∈ dualLattice z N
      · rw [Set.indicator_of_mem (show k ∈ dualLattice z N \ {0} from ⟨hk, hk0⟩),
          Set.indicator_of_mem hk]
      · rw [Set.indicator_of_notMem (fun h => hk h.1), Set.indicator_of_notMem hk]
  have hb : HasSum (fun k => (dualLattice z N \ {0}).indicator
      (fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖) k)
      (∑' k, (dualLattice z N \ {0}).indicator
        (fun k => ‖torusCoeff (fun x => (f x : ℂ)) k‖) k) :=
    (hs.indicator _).hasSum
  have hle := hE.norm_le_of_bounded hb fun k => by
    by_cases hk : k ∈ dualLattice z N \ {0}
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, norm_mul, norm_torusChar, mul_one]
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, norm_zero]
  rwa [Complex.norm_real, Real.norm_eq_abs] at hle

/-! ### MLQMC with rank-1 lattices in `d` dimensions -/

/-- **The mean square error of the `d`-dimensional MLQMC estimator.**  With pairwise independent
shifts `U_ℓ` uniform on `𝕋^d`, measurable square-integrable level corrections `f_ℓ`, generating
vectors `z_ℓ`, `N_ℓ ≥ 1`, bias `|∑_{ℓ≤L} ∫ f_ℓ − I| ≤ B` and dual-lattice sums
`∑_{k ∈ L_ℓ^⊥ \ {0}} |f̂_ℓ(k)|² ≤ v_ℓ`, the estimator
`Y = ∑_{ℓ≤L} N_ℓ⁻¹ ∑_{i<N_ℓ} f_ℓ(frac(i z_ℓ/N_ℓ + U_ℓ))` has `E[(Y − I)²] ≤ B² + ∑_{ℓ≤L} v_ℓ`
(`mse_eq_variance_add_sq_bias`, `IndepFun.variance_sum`, `rank1Lattice_randomShift`). -/
lemma mlqmcLattice_mse_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : ℕ → Ω → UnitAddTorus d} (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ volume)
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → UnitAddTorus d → ℝ}
    (hfm : ∀ ℓ, Measurable (f ℓ)) (hf : ∀ ℓ, MemLp (f ℓ) 2 volume) (z : ℕ → d → ℤ) {L : ℕ}
    {N : ℕ → ℕ} (hN : ∀ ℓ, 0 < N ℓ) {I B : ℝ} {v : ℕ → ℝ}
    (hbias : |∑ ℓ ∈ range (L + 1), (∫ y, f ℓ y) - I| ≤ B)
    (hv : ∀ ℓ, ∑' k, (dualLattice (z ℓ) (N ℓ) \ {0}).indicator
      (fun k => ‖torusCoeff (fun x => (f ℓ x : ℂ)) k‖ ^ 2) k ≤ v ℓ) :
    ∫ ω, (∑ ℓ ∈ range (L + 1),
        shiftedQMC (f ℓ) (rank1Lattice (z ℓ) (N ℓ)) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ ≤
      B ^ 2 + ∑ ℓ ∈ range (L + 1), v ℓ := by
  have := isProbabilityMeasure_of_measurePreserving_torus (hU 0)
  have hone := fun ℓ => rank1Lattice_randomShift (hU ℓ) (z ℓ) (hf ℓ) (hN ℓ)
  have hL2 : ∀ ℓ, MemLp (fun ω => shiftedQMC (f ℓ) (rank1Lattice (z ℓ) (N ℓ)) (N ℓ) (U ℓ ω)) 2 μ :=
    fun ℓ => (hone ℓ).2.1
  have hpair : Set.Pairwise ↑(range (L + 1)) fun i j =>
      IndepFun (fun ω => shiftedQMC (f i) (rank1Lattice (z i) (N i)) (N i) (U i ω))
        (fun ω => shiftedQMC (f j) (rank1Lattice (z j) (N j)) (N j) (U j ω)) μ :=
    fun i _ j _ hij => (hUind hij).comp (measurable_shiftedQMC (hfm i) _ _)
      (measurable_shiftedQMC (hfm j) _ _)
  have hsumfun : (fun ω => ∑ ℓ ∈ range (L + 1),
      shiftedQMC (f ℓ) (rank1Lattice (z ℓ) (N ℓ)) (N ℓ) (U ℓ ω)) =
      ∑ ℓ ∈ range (L + 1), fun ω => shiftedQMC (f ℓ) (rank1Lattice (z ℓ) (N ℓ)) (N ℓ) (U ℓ ω) := by
    ext ω
    rw [Finset.sum_apply]
  have hY : MemLp (fun ω => ∑ ℓ ∈ range (L + 1),
      shiftedQMC (f ℓ) (rank1Lattice (z ℓ) (N ℓ)) (N ℓ) (U ℓ ω)) 2 μ :=
    memLp_finsetSum _ fun ℓ _ => hL2 ℓ
  have hvar : variance (fun ω => ∑ ℓ ∈ range (L + 1),
      shiftedQMC (f ℓ) (rank1Lattice (z ℓ) (N ℓ)) (N ℓ) (U ℓ ω)) μ ≤
      ∑ ℓ ∈ range (L + 1), v ℓ := by
    rw [hsumfun, IndepFun.variance_sum (fun ℓ _ => hL2 ℓ) hpair]
    exact sum_le_sum fun ℓ _ => ((hone ℓ).2.2.2.tsum_eq).symm.le.trans (hv ℓ)
  have hmean : ∫ ω, ∑ ℓ ∈ range (L + 1),
      shiftedQMC (f ℓ) (rank1Lattice (z ℓ) (N ℓ)) (N ℓ) (U ℓ ω) ∂μ =
      ∑ ℓ ∈ range (L + 1), ∫ y, f ℓ y := by
    rw [integral_finsetSum _ fun ℓ _ => (hL2 ℓ).integrable one_le_two]
    exact sum_congr rfl fun ℓ _ => (hone ℓ).2.2.1
  have hb : (∑ ℓ ∈ range (L + 1), (∫ y, f ℓ y) - I) ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hbias 2
  have hdec := mse_eq_variance_add_sq_bias hY I
  rw [hmean] at hdec
  rw [hdec]
  linarith

/-- From a real-analysis complexity bound to the `d`-dimensional MLQMC estimator: if the
allocation `(L, N_ℓ)` of `hcore` makes `(c₁ 2^{−aL})² + ∑_{ℓ≤L} vb(ℓ, N_ℓ) < ε²` at cost
`≤ K ε^{−p}`, and the dual-lattice sums of the generating vectors `Z(ℓ, N)` are at most
`vb(ℓ, N)`, the MLQMC estimator with this allocation has mean square error `< ε²` at the same cost
bound (`mlqmcLattice_mse_le`). -/
lemma mlqmcLattice_of_core {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : ℕ → Ω → UnitAddTorus d} (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ volume)
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → UnitAddTorus d → ℝ}
    (hfm : ∀ ℓ, Measurable (f ℓ)) (hf : ∀ ℓ, MemLp (f ℓ) 2 volume) (Z : ℕ → ℕ → d → ℤ)
    {C : ℕ → ℝ} {vb : ℕ → ℕ → ℝ} {I a g c₁ c₃ p : ℝ}
    (hbias : ∀ L : ℕ, |∑ ℓ ∈ range (L + 1), (∫ y, f ℓ y) - I| ≤
      c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))))
    (hV : ∀ ℓ N : ℕ, 0 < N → ∑' k, (dualLattice (Z ℓ N) N \ {0}).indicator
      (fun k => ‖torusCoeff (fun x => (f ℓ x : ℂ)) k‖ ^ 2) k ≤ vb ℓ N)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ)))
    (hcore : ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 + ∑ ℓ ∈ range (L + 1), vb ℓ (N ℓ) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤ K * ε ^ (-p)) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      ∫ ω, (∑ ℓ ∈ range (L + 1),
          shiftedQMC (f ℓ) (rank1Lattice (Z ℓ (N ℓ)) (N ℓ)) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ < ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ K * ε ^ (-p) := by
  obtain ⟨K, hK, hcore⟩ := hcore
  refine ⟨K, hK, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := hcore ε hε hε1
  refine ⟨L, N, hN, (mlqmcLattice_mse_le hU hUind hfm hf (fun ℓ => Z ℓ (N ℓ)) hN (hbias L)
    (fun ℓ => hV ℓ (N ℓ) (hN ℓ))).trans_lt hmse, ?_⟩
  calc ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ
      ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :=
        sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (hC ℓ) (Nat.cast_nonneg _)
    _ ≤ _ := hcost

/-- `(c 2^{−bℓ}/M)² ≤ (max(|c|, 1) 2^{−b'ℓ}/M)²` for `b' ≤ b` and `M ≥ 0`: the constants of the
MLQMC theorems need not be assumed positive. -/
lemma sq_mul_two_rpow_div_le {c b b' M : ℝ} (hb : b' ≤ b) (hM : 0 ≤ M) (ℓ : ℕ) :
    (c * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / M) ^ 2 ≤
      (max |c| 1 * (2 : ℝ) ^ (-(b' * (ℓ : ℝ))) / M) ^ 2 := by
  have h0 : 0 ≤ (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / M := by positivity
  have h1 : (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / M ≤ (2 : ℝ) ^ (-(b' * (ℓ : ℝ))) / M :=
    div_le_div_of_nonneg_right (two_rpow_neg_mul_le hb ℓ) hM
  have h2 : |c| ≤ max |c| 1 := le_max_left _ _
  rw [mul_div_assoc, mul_div_assoc, ← sq_abs (c * _), abs_mul, abs_of_nonneg h0]
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul h2 h1 h0 ((abs_nonneg c).trans h2)) 2

/-- **MLQMC complexity for a QMC variance rate `N^{−2r}`, the real-analysis core** (Giles 2015,
§2.7, p. 20: "under certain conditions they lead to multilevel methods with a complexity which is
`O(ε^{−p})` with `p < 2`"; §3.5, p. 26: QMC error "In the best cases … `O(N_ℓ⁻¹)` rather than the
usual `O(N_ℓ^{−1/2})`").  The generalisation of `mlqmc_complexity_core` (the case `r = 1`) to a
level-`ℓ` variance `(c₂ 2^{−bℓ} N_ℓ^{−r})²` with `N_ℓ` points.  Let `a, r > 0`, `rg < b` (no sign
conditions on `b`, `g`) and `c₁, c₂, c₃ > 0`, with a bias `c₁ 2^{−aL}` at finest level `L` and a
cost `c₃ 2^{gℓ}` per point.  There is `K > 0` such that for every `0 < ε < 1` there are `L` and
`N_ℓ ≥ 1` with `(c₁ 2^{−aL})² + ∑_{ℓ≤L} (c₂ 2^{−bℓ} N_ℓ^{−r})² < ε²` and
`∑_{ℓ≤L} N_ℓ c₃ 2^{gℓ} ≤ K ε^{−p}`, `p = max(1/r, g/a)`.  Proof: `L = levelL a c₁ (ε/2)` and
`N_ℓ = ⌈A ε^{−1/r} 2^{−(2b+g)ℓ/(2r+1)}⌉`, `A = (2c₂/(1 − τ))^{1/r}`, `τ = 2^{(rg−b)/(2r+1)} < 1`
(the allocation `N_ℓ ∝ (V_ℓ/C_ℓ)^{1/(2r+1)}`, `V_ℓ = c₂² 2^{−2bℓ}`, `C_ℓ = c₃ 2^{gℓ}`): the
variance terms are `≤ (ε(1 − τ)/2)² τ^{2ℓ}`, the main cost is `O(ε^{−1/r})`, and rounding up costs
`O(ε^{−max(1/r, g/a)})` (`exists_sum_two_rpow_le` at `ε^{1/r}`). -/
theorem mlqmc_complexity_core_rate {a b g r c₁ c₂ c₃ : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hgb : r * g < b) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(a * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / (N ℓ : ℝ) ^ r) ^ 2 < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          K * ε ^ (-max (1 / r) (g / a)) := by
  have h2r : 0 < 2 * r + 1 := by linarith
  set e : ℝ := (r * g - b) / (2 * r + 1) with he
  set s : ℝ := (2 * b + g) / (2 * r + 1) with hs
  have he0 : e < 0 := div_neg_of_neg_of_pos (by linarith) h2r
  have hE1 : ∀ ℓ : ℕ, e * ℓ + r * (-(s * ℓ)) = -(b * ℓ) := fun ℓ => by
    rw [he, hs]
    field_simp
    ring
  have hE2 : ∀ ℓ : ℕ, -(s * ℓ) + g * ℓ = 2 * e * ℓ := fun ℓ => by
    rw [he, hs]
    field_simp
    ring
  set τ : ℝ := (2 : ℝ) ^ e with hτ
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos two_pos _
  have hτ1 : τ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two he0
  have h1τ : 0 < 1 - τ := by linarith
  have hτ2 : τ ^ 2 < 1 := by nlinarith
  have h1τ2 : 0 < 1 - τ ^ 2 := by linarith
  have hτℓ : ∀ ℓ : ℕ, τ ^ ℓ = (2 : ℝ) ^ (e * ℓ) := fun ℓ => (two_rpow_mul_nat e ℓ).symm
  have hτ2ℓ : ∀ ℓ : ℕ, (τ ^ 2) ^ ℓ = (2 : ℝ) ^ (2 * e * ℓ) := fun ℓ => by
    rw [← pow_mul, hτℓ]
    congr 1
    push_cast
    ring
  have hc : 0 < 2 * c₂ / (1 - τ) := div_pos (by positivity) h1τ
  set A : ℝ := (2 * c₂ / (1 - τ)) ^ (1 / r) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos hc _
  have hAr : A ^ r = 2 * c₂ / (1 - τ) := by
    rw [hA, ← Real.rpow_mul hc.le, one_div_mul_cancel hr.ne', Real.rpow_one]
  have hK1 := K1_pos (α := a) hc₁
  obtain ⟨K₀, hK₀, hround⟩ := exists_sum_two_rpow_le g (div_pos ha hr)
    (Real.rpow_pos_of_pos hK1 (1 / r))
  refine ⟨A * c₃ / (1 - τ ^ 2) + c₃ * K₀, by positivity, fun ε hε hε1 => ?_⟩
  set M : ℕ → ℝ := fun ℓ => A * ε ^ (-(1 / r)) * (2 : ℝ) ^ (-(s * ℓ)) with hM
  have hM0 : ∀ ℓ, 0 < M ℓ := fun ℓ => by positivity
  refine ⟨levelL a c₁ (ε / 2), fun ℓ => ⌈M ℓ⌉₊, fun ℓ => Nat.ceil_pos.2 (hM0 ℓ), ?_, ?_⟩
  · -- the mean square error
    have hbias : (c₁ * (2 : ℝ) ^ (-(a * (levelL a c₁ (ε / 2) : ℝ)))) ^ 2 ≤ ε ^ 2 / 4 := by
      have hb := levelL_bias ha hc₁ (half_pos hε)
      calc _ ≤ (ε / 2) ^ 2 := by gcongr
        _ = ε ^ 2 / 4 := by ring
    have hterm : ∀ ℓ ∈ range (levelL a c₁ (ε / 2) + 1),
        (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈M ℓ⌉₊ : ℕ) : ℝ) ^ r) ^ 2 ≤
          (ε * (1 - τ) / 2) ^ 2 * (τ ^ 2) ^ ℓ := by
      intro ℓ _
      have hN : M ℓ ≤ ((⌈M ℓ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have hNr : M ℓ ^ r ≤ ((⌈M ℓ⌉₊ : ℕ) : ℝ) ^ r := Real.rpow_le_rpow (hM0 ℓ).le hN hr.le
      have hMr : M ℓ ^ r = A ^ r * ε⁻¹ * (2 : ℝ) ^ (r * (-(s * ℓ))) := by
        simp only [hM]
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hA0.le (by positivity),
          ← Real.rpow_mul hε.le, ← Real.rpow_mul two_pos.le, neg_mul, one_div_mul_cancel hr.ne',
          Real.rpow_neg_one, mul_comm (-(s * ℓ)) r]
      have hMr0 : 0 < M ℓ ^ r := Real.rpow_pos_of_pos (hM0 ℓ) r
      have h1 : c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈M ℓ⌉₊ : ℕ) : ℝ) ^ r ≤
          ε * (1 - τ) / 2 * τ ^ ℓ := by
        rw [div_le_iff₀ (hMr0.trans_le hNr)]
        calc c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) = ε * (1 - τ) / 2 * τ ^ ℓ * M ℓ ^ r := by
              rw [hMr, hAr, hτℓ, ← hE1 ℓ, Real.rpow_add two_pos]
              field_simp
          _ ≤ ε * (1 - τ) / 2 * τ ^ ℓ * ((⌈M ℓ⌉₊ : ℕ) : ℝ) ^ r := by gcongr
      have h0 : 0 ≤ c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈M ℓ⌉₊ : ℕ) : ℝ) ^ r := by positivity
      calc _ ≤ (ε * (1 - τ) / 2 * τ ^ ℓ) ^ 2 := by gcongr
        _ = _ := by ring
    have hgeo := geom_sum_le_of_lt_one (sq_nonneg τ) hτ2 (levelL a c₁ (ε / 2) + 1)
    have hvar : ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1),
        (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / ((⌈M ℓ⌉₊ : ℕ) : ℝ) ^ r) ^ 2 ≤ ε ^ 2 / 4 := by
      calc _ ≤ ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1), (ε * (1 - τ) / 2) ^ 2 * (τ ^ 2) ^ ℓ :=
            sum_le_sum hterm
        _ = (ε * (1 - τ) / 2) ^ 2 * ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1), (τ ^ 2) ^ ℓ := by
            rw [mul_sum]
        _ ≤ (ε * (1 - τ) / 2) ^ 2 * (1 - τ ^ 2)⁻¹ := by gcongr
        _ = ε ^ 2 / 4 * ((1 - τ) / (1 + τ)) := by
            have h1t' : 1 - τ ^ 2 = (1 - τ) * (1 + τ) := by ring
            rw [h1t']
            field_simp
            norm_num
        _ ≤ ε ^ 2 / 4 * 1 := by
            gcongr
            rw [div_le_one (by linarith)]
            linarith
        _ = ε ^ 2 / 4 := mul_one _
    nlinarith [sq_pos_of_pos hε]
  · -- the cost
    have hL2 := two_rpow_levelL_half_le ha hc₁ hε hε1
    have hεr0 : 0 < ε ^ (1 / r) := Real.rpow_pos_of_pos hε _
    have hεr1 : ε ^ (1 / r) < 1 := Real.rpow_lt_one hε.le hε1 (by positivity)
    have hLr : (2 : ℝ) ^ (a / r * (levelL a c₁ (ε / 2) : ℝ)) ≤ K1 a c₁ ^ (1 / r) / ε ^ (1 / r) := by
      rw [← Real.div_rpow hK1.le hε.le, div_mul_eq_mul_div, div_eq_mul_one_div,
        Real.rpow_mul two_pos.le]
      exact Real.rpow_le_rpow (by positivity) hL2 (by positivity)
    have hround' := hround (ε ^ (1 / r)) hεr0 hεr1 _ hLr
    have hpow : (ε ^ (1 / r)) ^ (-max 1 (g / (a / r))) = ε ^ (-max (1 / r) (g / a)) := by
      rw [← Real.rpow_mul hε.le]
      congr 1
      rw [mul_neg, mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / r), mul_one]
      congr 2
      field_simp
    rw [hpow] at hround'
    have hterm : ∀ ℓ ∈ range (levelL a c₁ (ε / 2) + 1),
        ((⌈M ℓ⌉₊ : ℕ) : ℝ) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) ≤
          A * c₃ * ε ^ (-(1 / r)) * (τ ^ 2) ^ ℓ + c₃ * ((2 : ℝ) ^ g) ^ ℓ := by
      intro ℓ _
      have hN : ((⌈M ℓ⌉₊ : ℕ) : ℝ) ≤ M ℓ + 1 := (Nat.ceil_lt_add_one (hM0 ℓ).le).le
      calc _ ≤ (M ℓ + 1) * (c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) := by gcongr
        _ = A * c₃ * ε ^ (-(1 / r)) * ((2 : ℝ) ^ (-(s * ℓ)) * (2 : ℝ) ^ (g * (ℓ : ℝ))) +
            c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ)) := by
            simp only [hM]
            ring
        _ = _ := by rw [← Real.rpow_add two_pos, hE2, ← hτ2ℓ, two_rpow_mul_nat g ℓ]
    have hgeo := geom_sum_le_of_lt_one (sq_nonneg τ) hτ2 (levelL a c₁ (ε / 2) + 1)
    have hp1 : ε ^ (-(1 / r)) ≤ ε ^ (-max (1 / r) (g / a)) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1.le (neg_le_neg (le_max_left _ _))
    calc _ ≤ ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1),
          (A * c₃ * ε ^ (-(1 / r)) * (τ ^ 2) ^ ℓ + c₃ * ((2 : ℝ) ^ g) ^ ℓ) := sum_le_sum hterm
      _ = A * c₃ * ε ^ (-(1 / r)) * ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1), (τ ^ 2) ^ ℓ +
          c₃ * ∑ ℓ ∈ range (levelL a c₁ (ε / 2) + 1), ((2 : ℝ) ^ g) ^ ℓ := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ A * c₃ * ε ^ (-(1 / r)) * (1 - τ ^ 2)⁻¹ +
          c₃ * (K₀ * ε ^ (-max (1 / r) (g / a))) := by gcongr
      _ = A * c₃ / (1 - τ ^ 2) * ε ^ (-(1 / r)) + c₃ * K₀ * ε ^ (-max (1 / r) (g / a)) := by
          ring
      _ ≤ A * c₃ / (1 - τ ^ 2) * ε ^ (-max (1 / r) (g / a)) +
          c₃ * K₀ * ε ^ (-max (1 / r) (g / a)) := by gcongr
      _ = _ := by ring

/-- **MLQMC with randomly shifted rank-1 lattice rules in `d` dimensions: mean square error `< ε²`
at cost `O(ε^{−max(1, g/a)})`** (Giles 2015, §2.7, p. 20: "under certain conditions they lead to
multilevel methods with a complexity which is `O(ε^{−p})` with `p < 2`"; §3.5, p. 26: "rank-1
lattices (Dick et al. 2007)", "In the best cases, this results in the approximate numerical
integration error being `O(N_ℓ⁻¹)` rather than the usual `O(N_ℓ^{−1/2})` error", randomised by "a
random shift (for rank-1 lattice rules)").  The `d`-dimensional analogue of `mlqmc_complexity`:
the level-`ℓ` correction is a function `f_ℓ` of `d` uniform inputs, i.e. on `𝕋^d`.  Assume
* each `f_ℓ` is measurable and square-integrable on `𝕋^d`;
* for every level `ℓ` and every `N ≥ 1` the generating vector `Z(ℓ, N) ∈ ℤ^d` makes the dual-lattice
  sum `∑_{k ∈ L^⊥ \ {0}} |f̂_ℓ(k)|² ≤ (c₂ 2^{−bℓ}/N)²`, i.e. (by `hasSum_variance_rank1Lattice`)
  the randomly shifted lattice rule with `N` points has root-mean-square error `≤ c₂ 2^{−bℓ}/N`
  (the paper's best case `O(N_ℓ⁻¹)`, with level-dependent constants); this is an assumption,
  since the existence of such generating vectors is not proved here;
* the bias at finest level `L` is `|∑_{ℓ≤L} ∫_{𝕋^d} f_ℓ − I| ≤ c₁ 2^{−aL}`;
* a point on level `ℓ` costs `C_ℓ ≤ c₃ 2^{gℓ}`, with `a > 0` and either `b > g`, or `a ≤ b` and
  `a < g` (no sign conditions on `g` or on the constants);
* the shifts `U_0, U_1, …` (one per level) are pairwise independent and uniform on `𝕋^d`.
Then there is `K > 0` such that for every `0 < ε < 1` there are `L` and `N_ℓ ≥ 1` for which the
MLQMC estimator `Y = ∑_{ℓ≤L} N_ℓ⁻¹ ∑_{i<N_ℓ} f_ℓ(frac(i Z(ℓ, N_ℓ)/N_ℓ + U_ℓ))` has
`E[(Y − I)²] < ε²` and cost `∑_{ℓ≤L} N_ℓ C_ℓ ≤ K ε^{−max(1, g/a)}` (`mlqmc_complexity_core`), so
`p = max(1, g/a) < 2` whenever `g < 2a`.  Each level uses one randomly shifted lattice; the `32`
replicates of Algorithm 2 (`rank1Lattice_replicates`) change only the constant. -/
theorem mlqmcLattice_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : ℕ → Ω → UnitAddTorus d} (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ volume)
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → UnitAddTorus d → ℝ}
    (hfm : ∀ ℓ, Measurable (f ℓ)) (hf : ∀ ℓ, MemLp (f ℓ) 2 volume) (Z : ℕ → ℕ → d → ℤ)
    {C : ℕ → ℝ} {I a b g c₁ c₂ c₃ : ℝ} (ha : 0 < a) (hgb : g < b ∨ (a ≤ b ∧ a < g))
    (hbias : ∀ L : ℕ, |∑ ℓ ∈ range (L + 1), (∫ y, f ℓ y) - I| ≤
      c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))))
    (hV : ∀ ℓ N : ℕ, 0 < N → ∑' k, (dualLattice (Z ℓ N) N \ {0}).indicator
      (fun k => ‖torusCoeff (fun x => (f ℓ x : ℂ)) k‖ ^ 2) k ≤
        (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N) ^ 2)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      ∫ ω, (∑ ℓ ∈ range (L + 1),
          shiftedQMC (f ℓ) (rank1Lattice (Z ℓ (N ℓ)) (N ℓ)) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ < ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ K * ε ^ (-max 1 (g / a)) := by
  have hcore := mlqmc_complexity_core ha hgb (lt_max_of_lt_right one_pos : 0 < max c₁ 1)
    (lt_max_of_lt_right one_pos : 0 < max |c₂| 1) (lt_max_of_lt_right one_pos : 0 < max c₃ 1)
  exact mlqmcLattice_of_core (vb := fun ℓ N =>
      (max |c₂| 1 * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / (N : ℝ)) ^ 2)
    hU hUind hfm hf Z (fun L => le_max_one_mul (by positivity) (hbias L))
    (fun ℓ N hN => (hV ℓ N hN).trans (sq_mul_two_rpow_div_le le_rfl (Nat.cast_nonneg N) ℓ))
    (fun ℓ => le_max_one_mul (by positivity) (hC ℓ)) hcore

/-- **MLQMC with randomly shifted rank-1 lattice rules in `d` dimensions has complexity `O(ε^{−p})`
with `p < 2` whenever `g < 2a` and `g < a + b`** (Giles 2015, §2.7, p. 20: "These theoretical
developments are very encouraging, showing that under certain conditions they lead to multilevel
methods with a complexity which is `O(ε^{−p})` with `p < 2`").  The `d`-dimensional analogue of
`mlqmc_complexity_lt_two`: in the setting of `mlqmcLattice_complexity` (level corrections `f_ℓ` on
`𝕋^d`, generating vectors `Z(ℓ, N)` with dual-lattice sums `≤ (c₂ 2^{−bℓ}/N)²` (assumed), bias
`≤ c₁ 2^{−aL}`, cost per point `C_ℓ ≤ c₃ 2^{gℓ}`, pairwise independent uniform shifts), assume only
`a > 0`, `g < 2a` and `g < a + b`.  Then there are `p < 2` and `K > 0` such that for every
`0 < ε < 1` there are `L` and `N_ℓ ≥ 1` for which the MLQMC estimator
`Y = ∑_{ℓ≤L} N_ℓ⁻¹ ∑_{i<N_ℓ} f_ℓ(frac(i Z(ℓ, N_ℓ)/N_ℓ + U_ℓ))` has `E[(Y − I)²] < ε²` at cost
`∑_{ℓ≤L} N_ℓ C_ℓ ≤ K ε^{−p}`.  Proof: with `b' = min(b, g − a/2) < g` the sums are
`≤ (max(|c₂|, 1) 2^{−b'ℓ}/N)²`, and `mlqmc_complexity_core_of_lt` gives
`p = max(1 + (g − b')/a, g/a) < 2`. -/
theorem mlqmcLattice_complexity_lt_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : ℕ → Ω → UnitAddTorus d} (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ volume)
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → UnitAddTorus d → ℝ}
    (hfm : ∀ ℓ, Measurable (f ℓ)) (hf : ∀ ℓ, MemLp (f ℓ) 2 volume) (Z : ℕ → ℕ → d → ℤ)
    {C : ℕ → ℝ} {I a b g c₁ c₂ c₃ : ℝ} (ha : 0 < a) (h2a : g < 2 * a) (hgab : g < a + b)
    (hbias : ∀ L : ℕ, |∑ ℓ ∈ range (L + 1), (∫ y, f ℓ y) - I| ≤
      c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))))
    (hV : ∀ ℓ N : ℕ, 0 < N → ∑' k, (dualLattice (Z ℓ N) N \ {0}).indicator
      (fun k => ‖torusCoeff (fun x => (f ℓ x : ℂ)) k‖ ^ 2) k ≤
        (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / N) ^ 2)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :
    ∃ p : ℝ, p < 2 ∧ ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ),
      (∀ ℓ, 0 < N ℓ) ∧
      ∫ ω, (∑ ℓ ∈ range (L + 1),
          shiftedQMC (f ℓ) (rank1Lattice (Z ℓ (N ℓ)) (N ℓ)) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ < ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ K * ε ^ (-p) := by
  have hga : g / a < 2 := by
    rw [div_lt_iff₀ ha]
    linarith
  have hb'g : min b (g - a / 2) < g := (min_le_right _ _).trans_lt (by linarith)
  have hgb' : (g - min b (g - a / 2)) / a < 1 := by
    rw [div_lt_one ha]
    have : g - a < min b (g - a / 2) := lt_min (by linarith) (by linarith)
    linarith
  have hcore := mlqmc_complexity_core_of_lt ha hb'g (lt_max_of_lt_right one_pos : 0 < max c₁ 1)
    (lt_max_of_lt_right one_pos : 0 < max |c₂| 1) (lt_max_of_lt_right one_pos : 0 < max c₃ 1)
  exact ⟨max (1 + (g - min b (g - a / 2)) / a) (g / a), max_lt (by linarith) hga,
    mlqmcLattice_of_core (vb := fun ℓ N =>
      (max |c₂| 1 * (2 : ℝ) ^ (-(min b (g - a / 2) * (ℓ : ℝ))) / (N : ℝ)) ^ 2)
    hU hUind hfm hf Z (fun L => le_max_one_mul (by positivity) (hbias L))
    (fun ℓ N hN => (hV ℓ N hN).trans
      (sq_mul_two_rpow_div_le (min_le_left _ _) (Nat.cast_nonneg N) ℓ))
    (fun ℓ => le_max_one_mul (by positivity) (hC ℓ)) hcore⟩

/-- **MLQMC with randomly shifted rank-1 lattice rules for a QMC variance rate `N^{−2r}`: cost
`O(ε^{−max(1/r, g/a)})`** (Giles 2015, §2.7, p. 20: "under certain conditions they lead to
multilevel methods with a complexity which is `O(ε^{−p})` with `p < 2`"; §3.5, p. 26: "In the best
cases, this results in the approximate numerical integration error being `O(N_ℓ⁻¹)` rather than
the usual `O(N_ℓ^{−1/2})` error which comes from Monte Carlo sampling").  In the setting of
`mlqmcLattice_complexity` (level corrections `f_ℓ` on `𝕋^d`, pairwise independent uniform shifts,
bias `≤ c₁ 2^{−aL}`, cost per point `C_ℓ ≤ c₃ 2^{gℓ}`), assume that for every level `ℓ` and every
`N ≥ 1` the generating vector `Z(ℓ, N)` makes the dual-lattice sum
`∑_{k ∈ L^⊥ \ {0}} |f̂_ℓ(k)|² ≤ (c₂ 2^{−bℓ} N^{−r})²` (root-mean-square error `O(2^{−bℓ}N^{−r})`;
`r = 1/2` is the Monte Carlo rate and `r = 1` the paper's best case), with `a, r > 0` and
`rg < b` (no sign conditions on `b`, `g` or the constants).  Then there is `K > 0` such that for
every `0 < ε < 1` there are `L` and `N_ℓ ≥ 1` for which the MLQMC estimator
`Y = ∑_{ℓ≤L} N_ℓ⁻¹ ∑_{i<N_ℓ} f_ℓ(frac(i Z(ℓ, N_ℓ)/N_ℓ + U_ℓ))` has `E[(Y − I)²] < ε²` and cost
`∑_{ℓ≤L} N_ℓ C_ℓ ≤ K ε^{−max(1/r, g/a)}` (`mlqmc_complexity_core_rate`).  So
`p = max(1/r, g/a) < 2` exactly when `r > 1/2` and `g < 2a`; for `r = 1/2` it is
`max(2, g/a)`, as for Giles' Theorem 1 with `β = 2b > γ = g`.  (Giles 2015, §5.2, p. 35, reports
that MLQMC with the Milstein scheme for geometric Brownian motion, where `a = b = g = 1`
(`V_ℓ = O(h_ℓ²)`), reduced the complexity "from `O(ε^{−2})` to approximately `O(ε^{−1.5})`"; here
that corresponds to `r = 2/3`.) -/
theorem mlqmcLattice_complexity_rate {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : ℕ → Ω → UnitAddTorus d} (hU : ∀ ℓ, MeasurePreserving (U ℓ) μ volume)
    (hUind : Pairwise fun i j => IndepFun (U i) (U j) μ) {f : ℕ → UnitAddTorus d → ℝ}
    (hfm : ∀ ℓ, Measurable (f ℓ)) (hf : ∀ ℓ, MemLp (f ℓ) 2 volume) (Z : ℕ → ℕ → d → ℤ)
    {C : ℕ → ℝ} {I a b g r c₁ c₂ c₃ : ℝ} (ha : 0 < a) (hr : 0 < r) (hrgb : r * g < b)
    (hbias : ∀ L : ℕ, |∑ ℓ ∈ range (L + 1), (∫ y, f ℓ y) - I| ≤
      c₁ * (2 : ℝ) ^ (-(a * (L : ℝ))))
    (hV : ∀ ℓ N : ℕ, 0 < N → ∑' k, (dualLattice (Z ℓ N) N \ {0}).indicator
      (fun k => ‖torusCoeff (fun x => (f ℓ x : ℂ)) k‖ ^ 2) k ≤
        (c₂ * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / (N : ℝ) ^ r) ^ 2)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ (g * (ℓ : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
      ∫ ω, (∑ ℓ ∈ range (L + 1),
          shiftedQMC (f ℓ) (rank1Lattice (Z ℓ (N ℓ)) (N ℓ)) (N ℓ) (U ℓ ω) - I) ^ 2 ∂μ < ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ K * ε ^ (-max (1 / r) (g / a)) := by
  have hcore := mlqmc_complexity_core_rate ha hr hrgb (lt_max_of_lt_right one_pos : 0 < max c₁ 1)
    (lt_max_of_lt_right one_pos : 0 < max |c₂| 1) (lt_max_of_lt_right one_pos : 0 < max c₃ 1)
  exact mlqmcLattice_of_core (vb := fun ℓ N =>
      (max |c₂| 1 * (2 : ℝ) ^ (-(b * (ℓ : ℝ))) / (N : ℝ) ^ r) ^ 2)
    hU hUind hfm hf Z (fun L => le_max_one_mul (by positivity) (hbias L))
    (fun ℓ N hN => (hV ℓ N hN).trans
      (sq_mul_two_rpow_div_le le_rfl (Real.rpow_nonneg (Nat.cast_nonneg N) r) ℓ))
    (fun ℓ => le_max_one_mul (by positivity) (hC ℓ)) hcore

end MLMC
