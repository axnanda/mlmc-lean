import MlmcLean.LagrangeBitWidth
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.Compact

/-!
# Haas–Giles §6.1: the optimal bit-widths exist, their first-order conditions, convexity

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), §6.1 (pp. 11–12, (34)–(36), Figures 3 and 5).
`MlmcLean.BitWidth` proves the derivative identity (36) and `MlmcLean.LagrangeBitWidth` that the
solutions of (35) minimise the Lagrangian; this file studies the level cost (34) itself,
`√(V_ℓ C̃_ℓ(d)) + √(V^Δ_ℓ(d) C_ℓ)` (`bitLevelCost`), as a function of real (relaxed) bit-widths
`d`, with the cost (31) and the variance bound (26).

* **An optimum exists** (p. 12: "Although we do not prove it formally we can see that the
  resulting function is convex which ensures the existence of an optimum"; there "the resulting
  function" is the function of `λ` plotted in Figure 3).  If `V_ℓ > 0`, (34) attains its minimum
  over the bit-widths on every nonempty closed set `S ⊆ {d ≥ 0}` when `M_i, M'_i ≥ 0` and
  `M_i + M'_i > 0` (`exists_isMinOn_bitLevelCost_of_nonneg`), and on every nonempty closed set
  when every `M_i > 0` (`exists_isMinOn_bitLevelCost`), by continuity and coercivity, without
  convexity.
* **First-order conditions.**  At a local minimiser with `C̃_ℓ(d) > 0`, (36) and (35) hold with
  `λ = √(V_ℓ V^Δ_ℓ(d)/(C_ℓ C̃_ℓ(d)))` (`eq36_eq35_of_isLocalMin`); on a box `d ≥ b`, (35) holds
  for the variables above their bound and `∂V^Δ/∂d_i + λ ∂C̃/∂d_i ≥ 0` for those on it
  (`kkt_of_isMinOn_box`).
* **The search over `λ` reaches the optimum** (p. 12: "update the value of `λ` until we reach
  the optimal solution of the overall problem").  An interior minimiser `d*` is the unique
  solution of the uncoupled equations (35) for `λ* = √(V_ℓ V^Δ_ℓ(d*)/(C_ℓ C̃_ℓ(d*)))`, and it
  minimises the Lagrangian `V^Δ_ℓ + λ* C̃_ℓ` (`lagrange_of_isMinOn_bitLevelCost`).  Moreover `λ*`
  minimises the function of `λ` of Figure 3, `λ ↦ (34)` at the solution `d(λ)` of (35)
  (`lambdaBitWidth`), over all `λ > 0` with `d(λ) ∈ S`, and its minimum value is the minimum of
  (34) over `S` (`isMinOn_lambda_bitLevelCost`).
* **Optimised beats uniform** (p. 12: "the optimisation method we suggest improves the level cost
  compared to the best uniform bit-width choice").  The best uniform bit-width exists and the
  optimum costs at most as much (`exists_best_uniform_bitLevelCost`), strictly less when the
  variance factors `E[x̄_i²] 4^{e_i}` are not proportional to the marginal costs `M_i w + M'_i`
  (`bitLevelCost_lt_uniform`).
* **Convexity in the bit-widths.**  The paper's convexity remark is about the function of `λ` of
  Figure 3 (plotted against `log λ`), not about (34) as a function of the bit-widths; convexity
  in the relaxed bit-widths is a related question that the paper does not discuss.  The variance
  part `√(V^Δ_ℓ(d))` is always convex (`convexOn_sqrt_vIndepR`).  Without additions
  (`M'_i = 0`), (34) is convex (`convexOn_bitLevelCost`), strictly so when all `E[x̄_i²] > 0`
  (`strictConvexOn_bitLevelCost`), and its minimiser on a closed convex set is unique
  (`existsUnique_isMinOn_bitLevelCost`).  With additions (34) need not be convex
  (`not_convexOn_bitLevelCost`).  Numerically (not proved here), the function of `λ` of Figure 3
  need not be convex for other parameters than the paper's, so convexity cannot be taken for
  granted, and with additions the minimiser need not be unique (see the docstrings of
  `not_convexOn_bitLevelCost` and `existsUnique_isMinOn_bitLevelCost`).
-/

open Finset Filter Topology

namespace MLMC

section existence

variable {ι : Type*}

/-- **The level cost (34)** of Haas–Giles (2025, §6.1, p. 11) as a function of real bit-widths
`d`: "at each level the aim is to minimise the level cost (33) which, using the fact that
`C_ℓ ≫ C̃_ℓ`, is approximated as `√(V_ℓ C̃_ℓ) + √(V^Δ_ℓ C_ℓ)` (34)".  Here `C̃_ℓ(d)` is the cost
(31) (`sepCost`, with the operation counts `M i = M_i` and `M' i = M'_i`), `V^Δ_ℓ(d)` is the
variance bound (26) (`vIndepR`, with `E i = E[x̄_i²]` and the exponents `e`), `V = V_ℓ` and
`C = C_ℓ`. -/
noncomputable def bitLevelCost (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ)
    (V C : ℝ) (d : ι → ℝ) : ℝ :=
  Real.sqrt (V * sepCost s M M' d) + Real.sqrt (vIndepR s E e d * C)

/-- The variance bound `vIndepR` is continuous in the bit-widths. -/
lemma continuous_vIndepR (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) :
    Continuous (vIndepR s E e) := by
  have h : vIndepR s E e = fun d => (1 / 12) * ∑ i ∈ s, E i * (4 : ℝ) ^ ((e i : ℝ) - d i) := rfl
  rw [h]
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
  exact continuous_const.mul (continuous_const.rpow (continuous_const.sub (continuous_apply i))
    fun _ => Or.inl (by norm_num))

/-- The cost `sepCost` is continuous in the bit-widths. -/
lemma continuous_sepCost (s : Finset ι) (M M' : ι → ℝ) : Continuous (sepCost s M M') := by
  have h : sepCost s M M' = fun d =>
      (1 / 2) * ∑ i ∈ s, M i * d i ^ 2 + ∑ i ∈ s, M' i * d i := rfl
  rw [h]
  exact (continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_apply i).pow 2))).add
    (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))

/-- The level cost `bitLevelCost` is continuous in the bit-widths. -/
lemma continuous_bitLevelCost (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ)
    (V C : ℝ) : Continuous (bitLevelCost s E e M M' V C) :=
  ((continuous_const.mul (continuous_sepCost s M M')).sqrt).add
    (((continuous_vIndepR s E e).mul continuous_const).sqrt)

/-- A continuous function on `ι → ℝ` attains its minimum on a closed set `S` if the points of `S`
where it is at most its value at some `x₀ ∈ S` lie in a box `∏_i [lo_i, up_i]`. -/
lemma exists_isMinOn_of_sublevel_subset_box [Fintype ι] {F : (ι → ℝ) → ℝ} (hF : Continuous F)
    {S : Set (ι → ℝ)} (hS : IsClosed S) {x₀ : ι → ℝ} (hx₀ : x₀ ∈ S) (lo up : ι → ℝ)
    (hbox : ∀ d ∈ S, F d ≤ F x₀ → ∀ i, d i ∈ Set.Icc (lo i) (up i)) :
    ∃ dstar ∈ S, IsMinOn F S dstar := by
  set K := S ∩ {d | F d ≤ F x₀}
  have hKsub : K ⊆ Set.univ.pi fun i => Set.Icc (lo i) (up i) :=
    fun d hd i _ => hbox d hd.1 hd.2 i
  have hKc : IsCompact K := (isCompact_univ_pi fun i => isCompact_Icc).of_isClosed_subset
    (hS.inter (isClosed_le hF continuous_const)) hKsub
  obtain ⟨dstar, hdK, hmin⟩ := hKc.exists_isMinOn ⟨x₀, hx₀, show F x₀ ≤ F x₀ from le_rfl⟩
    hF.continuousOn
  refine ⟨dstar, hdK.1, isMinOn_iff.2 fun y hy => ?_⟩
  by_cases hyB : F y ≤ F x₀
  · exact isMinOn_iff.1 hmin y ⟨hy, hyB⟩
  · exact le_trans (isMinOn_iff.1 hmin x₀ ⟨hx₀, show F x₀ ≤ F x₀ from le_rfl⟩)
      (le_of_not_ge hyB)

/-- On a sublevel set of the level cost (34) the cost (31) is bounded: if `V > 0` and
`F(d) ≤ B`, then `C̃(d) ≤ B²/V`, since `√(V C̃(d)) ≤ F(d)`. -/
lemma sepCost_le_of_bitLevelCost_le (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ)
    {V : ℝ} (C : ℝ) (hV : 0 < V) {d : ι → ℝ} {B : ℝ}
    (hdB : bitLevelCost s E e M M' V C d ≤ B) : sepCost s M M' d ≤ B ^ 2 / V := by
  rcases le_or_gt 0 (sepCost s M M' d) with h | h
  · have h1 : Real.sqrt (V * sepCost s M M' d) ≤ B :=
      le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hdB
    have h2 : V * sepCost s M M' d ≤ B ^ 2 :=
      calc V * sepCost s M M' d = Real.sqrt (V * sepCost s M M' d) ^ 2 :=
            (Real.sq_sqrt (mul_nonneg hV.le h)).symm
        _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [le_div_iff₀ hV]
    linarith
  · exact le_trans h.le (by positivity)

/-- The quadratic part of the cost (31) controls each bit-width: for `M_j > 0`,
`M_i d_i² / 4 ≤ C̃(d) + ∑_j M'_j² / M_j`. -/
lemma mul_sq_div_four_le_sepCost (s : Finset ι) {M M' : ι → ℝ} (hM : ∀ j ∈ s, 0 < M j)
    (d : ι → ℝ) {i : ι} (hi : i ∈ s) :
    M i * d i ^ 2 / 4 ≤ sepCost s M M' d + ∑ j ∈ s, M' j ^ 2 / M j := by
  have hterm : ∀ j ∈ s, M j * d j ^ 2 / 4 ≤
      (1 / 2) * (M j * d j ^ 2) + M' j * d j + M' j ^ 2 / M j := fun j hj => by
    have hMj := hM j hj
    have key : (1 / 2) * (M j * d j ^ 2) + M' j * d j + M' j ^ 2 / M j - M j * d j ^ 2 / 4 =
        M j * (d j / 2 + M' j / M j) ^ 2 := by
      field_simp
      ring
    have : 0 ≤ M j * (d j / 2 + M' j / M j) ^ 2 := by positivity
    linarith
  have hsum : sepCost s M M' d + ∑ j ∈ s, M' j ^ 2 / M j =
      ∑ j ∈ s, ((1 / 2) * (M j * d j ^ 2) + M' j * d j + M' j ^ 2 / M j) := by
    simp only [sepCost, Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum]
  calc M i * d i ^ 2 / 4 ≤ ∑ j ∈ s, M j * d j ^ 2 / 4 :=
        Finset.single_le_sum (f := fun j => M j * d j ^ 2 / 4)
          (fun j hj => by have := hM j hj; positivity) hi
    _ ≤ _ := Finset.sum_le_sum hterm

/-- On nonnegative bit-widths the cost (31) controls each bit-width linearly: for
`M_j, M'_j, d_j ≥ 0`, `(M_i/2 + M'_i) d_i ≤ M_i/2 + C̃(d)`. -/
lemma mul_le_sepCost_of_nonneg (s : Finset ι) {M M' : ι → ℝ} (hM : ∀ j ∈ s, 0 ≤ M j)
    (hM' : ∀ j ∈ s, 0 ≤ M' j) {d : ι → ℝ} (hd : ∀ j ∈ s, 0 ≤ d j) {i : ι} (hi : i ∈ s) :
    (M i / 2 + M' i) * d i ≤ M i / 2 + sepCost s M M' d := by
  have hsum : sepCost s M M' d = ∑ j ∈ s, ((1 / 2) * (M j * d j ^ 2) + M' j * d j) := by
    simp only [sepCost, Finset.mul_sum, Finset.sum_add_distrib]
  have hterm : (1 / 2) * (M i * d i ^ 2) + M' i * d i ≤ sepCost s M M' d := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun j => (1 / 2) * (M j * d j ^ 2) + M' j * d j)
      (fun j hj => by
        have := hM j hj
        have := hM' j hj
        have := hd j hj
        positivity) hi
  nlinarith [mul_nonneg (hM i hi) (sq_nonneg (d i - 1)), mul_nonneg (hM i hi) (hd i hi)]

/-- **An optimal bit-width configuration exists** (Haas–Giles 2025, §6.1, p. 12: "Although we do
not prove it formally we can see that the resulting function is convex which ensures the
existence of an optimum").  Let `V_ℓ > 0` and let every variable be involved in some operation
of the cost (31): `M_i, M'_i ≥ 0` and `M_i + M'_i > 0` (a variable used only in additions,
`M_i = 0 < M'_i`, is allowed).  Then the level cost (34) attains its minimum on every nonempty
closed set `S` of nonnegative real bit-widths, e.g. on all relaxed bit-widths `d ≥ 0`.  No
convexity is needed: (34) is continuous and at least `√(V_ℓ C̃_ℓ(d))`, and on `d ≥ 0`
`(M_i/2 + M'_i) d_i ≤ M_i/2 + C̃_ℓ(d)` (`mul_le_sepCost_of_nonneg`), so every sublevel set is
bounded.  Deviation: in the paper "the resulting function" is the function of `λ` of Figure 3,
whose minimum the golden section search computes; this is the existence of a minimiser of (34)
over the bit-widths themselves, "the optimal solution of the overall problem" (for the link with
the minimum over `λ` see `isMinOn_lambda_bitLevelCost`).  On `S` the cost `C̃_ℓ(d)` is `≥ 0`, so
for `C_ℓ ≥ 0` and `E[x̄_i²] ≥ 0` (the paper's setting) no square root of a negative number
occurs; the statement holds for all `E`, `e` and `C_ℓ`. -/
theorem exists_isMinOn_bitLevelCost_of_nonneg [Fintype ι] (E : ι → ℝ) (e : ι → ℤ)
    {M M' : ι → ℝ} {V : ℝ} (C : ℝ) (hV : 0 < V) (hM : ∀ i, 0 ≤ M i) (hM' : ∀ i, 0 ≤ M' i)
    (hMM : ∀ i, 0 < M i + M' i) {S : Set (ι → ℝ)} (hS : IsClosed S)
    (hS0 : S ⊆ {d | ∀ i, 0 ≤ d i}) (hne : S.Nonempty) :
    ∃ dstar ∈ S, IsMinOn (bitLevelCost univ E e M M' V C) S dstar := by
  obtain ⟨x₀, hx₀⟩ := hne
  set B := bitLevelCost univ E e M M' V C x₀
  refine exists_isMinOn_of_sublevel_subset_box (continuous_bitLevelCost _ _ _ _ _ _ _) hS hx₀
    (fun _ => 0) (fun i => (M i / 2 + B ^ 2 / V) / (M i / 2 + M' i)) fun d hd hdB i => ?_
  have hc : 0 < M i / 2 + M' i := by linarith [hM i, hM' i, hMM i]
  have h1 := mul_le_sepCost_of_nonneg univ (fun j _ => hM j) (fun j _ => hM' j)
    (fun j _ => hS0 hd j) (mem_univ i)
  have h2 := sepCost_le_of_bitLevelCost_le univ E e M M' C hV hdB
  refine ⟨hS0 hd i, ?_⟩
  rw [le_div_iff₀ hc]
  linarith

/-- **An optimal bit-width configuration exists, on any closed set** (Haas–Giles 2025, §6.1,
p. 12: "Although we do not prove it formally we can see that the resulting function is convex
which ensures the existence of an optimum").  If `V_ℓ > 0` and every multiplication count
`M_i > 0` (`M'_i`, `E`, `e`, `C_ℓ` arbitrary), the level cost (34) attains its minimum on every
nonempty closed set `S` of real bit-widths, not necessarily nonnegative ones: (34) is continuous
and at least `√(V_ℓ C̃_ℓ(d))`, which tends to `∞` with `d` (`mul_sq_div_four_le_sepCost`).
Deviation: as in `exists_isMinOn_bitLevelCost_of_nonneg`, this is the existence of a minimiser
over the bit-widths, not over `λ`.  At points with `C̃_ℓ(d) < 0` (for `M'_i ≥ 0` only at negative
bit-widths) the term `√(V_ℓ C̃_ℓ(d))` is Lean's `√x = 0`, i.e. (34) is read with `√(max x 0)`, a
continuous function; the existence does not rely on these values, and on the physical domain
`S ⊆ {d ≥ 0}` with `M'_i ≥ 0` they do not occur (`exists_isMinOn_bitLevelCost_of_nonneg`, which
also allows `M_i = 0`). -/
theorem exists_isMinOn_bitLevelCost [Fintype ι] (E : ι → ℝ) (e : ι → ℤ) {M : ι → ℝ}
    (M' : ι → ℝ) {V : ℝ} (C : ℝ) (hV : 0 < V) (hM : ∀ i, 0 < M i) {S : Set (ι → ℝ)}
    (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ dstar ∈ S, IsMinOn (bitLevelCost univ E e M M' V C) S dstar := by
  obtain ⟨x₀, hx₀⟩ := hne
  set R := bitLevelCost univ E e M M' V C x₀ ^ 2 / V + ∑ j, M' j ^ 2 / M j
  refine exists_isMinOn_of_sublevel_subset_box (continuous_bitLevelCost _ _ _ _ _ _ _) hS hx₀
    (fun i => -Real.sqrt (4 * R / M i)) (fun i => Real.sqrt (4 * R / M i))
    fun d _ hdB i => ?_
  have h2 := sepCost_le_of_bitLevelCost_le univ E e M M' C hV hdB
  have h3 := mul_sq_div_four_le_sepCost univ (M' := M') (fun j _ => hM j) d (mem_univ i)
  have h4 : d i ^ 2 ≤ 4 * R / M i := by
    rw [le_div_iff₀ (hM i)]
    linarith
  exact abs_le.1 (Real.abs_le_sqrt h4)

/-- **The best uniform bit-width, and the optimum is at least as good** (Haas–Giles 2025, §6.1,
p. 12, Figures 3 and 5: "Figure 5 also confirms that the optimisation method we suggest improves
the level cost compared to the best uniform bit-width choice").  Under the hypotheses of
`exists_isMinOn_bitLevelCost_of_nonneg` (`V_ℓ > 0`, `M_i, M'_i ≥ 0`, `M_i + M'_i > 0`, `S` a
closed set of nonnegative bit-widths), if `S` contains a uniform configuration (all `d_i`
equal), then a best uniform bit-width `w₀` exists (it minimises (34) among the uniform
configurations in `S`), and there is a minimiser `d*` of (34) over `S`, whose level cost is at
most that of `w₀`.  Unlike the paper's comparison, this uses no convexity; for the strict
inequality see `bitLevelCost_lt_uniform`.  The proof only uses the existence of minimisers on
closed subsets of `S`, so the same holds on any closed `S` when every `M_i > 0`
(`exists_isMinOn_bitLevelCost`). -/
theorem exists_best_uniform_bitLevelCost [Fintype ι] (E : ι → ℝ) (e : ι → ℤ) {M M' : ι → ℝ}
    {V : ℝ} (C : ℝ) (hV : 0 < V) (hM : ∀ i, 0 ≤ M i) (hM' : ∀ i, 0 ≤ M' i)
    (hMM : ∀ i, 0 < M i + M' i) {S : Set (ι → ℝ)} (hS : IsClosed S)
    (hS0 : S ⊆ {d | ∀ i, 0 ≤ d i}) {w₁ : ℝ} (hw₁ : (fun _ : ι => w₁) ∈ S) :
    ∃ w₀ : ℝ, (fun _ : ι => w₀) ∈ S ∧
      (∀ w : ℝ, (fun _ : ι => w) ∈ S → bitLevelCost univ E e M M' V C (fun _ => w₀) ≤
        bitLevelCost univ E e M M' V C (fun _ => w)) ∧
      ∃ dstar ∈ S, IsMinOn (bitLevelCost univ E e M M' V C) S dstar ∧
        bitLevelCost univ E e M M' V C dstar ≤ bitLevelCost univ E e M M' V C (fun _ => w₀) := by
  have hD : IsClosed {d : ι → ℝ | ∀ i j, d i = d j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_apply i) (continuous_apply j)
  obtain ⟨d₀, hd₀, hmin₀⟩ := exists_isMinOn_bitLevelCost_of_nonneg E e C hV hM hM' hMM
    (hS.inter hD) (Set.inter_subset_left.trans hS0) ⟨_, hw₁, fun _ _ => rfl⟩
  obtain ⟨w₀, rfl⟩ : ∃ w₀ : ℝ, d₀ = fun _ => w₀ := by
    rcases isEmpty_or_nonempty ι with h | ⟨⟨i₀⟩⟩
    · exact ⟨0, funext fun i => (IsEmpty.false i).elim⟩
    · exact ⟨d₀ i₀, funext fun i => hd₀.2 i i₀⟩
  obtain ⟨dstar, hdstar, hmin⟩ :=
    exists_isMinOn_bitLevelCost_of_nonneg E e C hV hM hM' hMM hS hS0 ⟨_, hw₁⟩
  exact ⟨w₀, hd₀.1, fun w hw => isMinOn_iff.1 hmin₀ _ ⟨hw, fun _ _ => rfl⟩, dstar, hdstar, hmin,
    isMinOn_iff.1 hmin _ hd₀.1⟩

end existence

section firstOrder

variable {ι : Type*}

/-- The partial derivative of the level cost (34) in the bit-width `d_i` (Haas–Giles 2025, §6.1,
p. 12, (36)): `½ (√(C/V^Δ) ∂V^Δ/∂d_i + √(V/C̃) ∂C̃/∂d_i)`, from `hasDerivAt_levelCost`,
`hasDerivAt_vIndepR_update` and `hasDerivAt_sepCost_update`. -/
lemma hasDerivAt_bitLevelCost_update [DecidableEq ι] (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ)
    (M M' : ι → ℝ) {V C : ℝ} (hV : 0 < V) (hC : 0 < C) {d : ι → ℝ}
    (hCt : 0 < sepCost s M M' d) (hVd : 0 < vIndepR s E e d) {i : ι} (hi : i ∈ s) :
    HasDerivAt (fun t => bitLevelCost s E e M M' V C (Function.update d i t))
      ((Real.sqrt (C / vIndepR s E e d) * -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - d i) / 12)
        + Real.sqrt (V / sepCost s M M' d) * (M i * d i + M' i)) / 2) (d i) := by
  have h := hasDerivAt_levelCost (Ct := fun t => sepCost s M M' (Function.update d i t))
    (Vd := fun t => vIndepR s E e (Function.update d i t)) hV hC
    (by simpa only [Function.update_eq_self] using hCt)
    (by simpa only [Function.update_eq_self] using hVd)
    (hasDerivAt_sepCost_update s M M' d hi (d i)) (hasDerivAt_vIndepR_update s E e d hi (d i))
  simp only [Function.update_eq_self] at h
  exact h

/-- **Haas–Giles (2025), §6.1, p. 12, (36) and (35) at an optimum.**  "Similarly, minimising (34)
by equating its derivative to zero gives
`√(C_ℓ/V^Δ_ℓ(d)) ∂V^Δ_ℓ/∂d_{i,ℓ} + √(V_ℓ/C̃_ℓ(d)) ∂C̃_ℓ/∂d_{i,ℓ} = 0` (36) so it is again of the
form (35), where `λ = √(V_ℓ V^Δ_ℓ(d)/C_ℓ C̃_ℓ(d))` gives the optimal trade-off between cost and
variance."  At every local minimiser `d*` of (34) over real bit-widths with `C̃_ℓ(d*) > 0` and
`V^Δ_ℓ(d*) > 0` (and `V_ℓ, C_ℓ > 0`), (36) holds for every variable `i`, with the partial
derivatives `−(log 4) E[x̄_i²] 4^{e_i − d_i}/12` of (26) and `M_i d_i + M'_i` of (31), and so does
(35) with this `λ`.  The paper equates the derivative to zero; here (36) is proved to hold at a
minimiser (Fermat's theorem in each coordinate). -/
theorem eq36_eq35_of_isLocalMin (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ)
    (M M' : ι → ℝ) {V C : ℝ} (hV : 0 < V) (hC : 0 < C) {dstar : ι → ℝ}
    (hmin : IsLocalMin (bitLevelCost s E e M M' V C) dstar) (hCt : 0 < sepCost s M M' dstar)
    (hVd : 0 < vIndepR s E e dstar) :
    ∀ i ∈ s,
      Real.sqrt (C / vIndepR s E e dstar) *
          -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
        Real.sqrt (V / sepCost s M M' dstar) * (M i * dstar i + M' i) = 0 ∧
      -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
        Real.sqrt (V * vIndepR s E e dstar / (C * sepCost s M M' dstar)) *
          (M i * dstar i + M' i) = 0 := by
  classical
  intro i hi
  have hloc : IsLocalMin (fun t => bitLevelCost s E e M M' V C (Function.update dstar i t))
      (dstar i) := by
    have h1 : IsLocalMin (bitLevelCost s E e M M' V C) (Function.update dstar i (dstar i)) := by
      rwa [Function.update_eq_self]
    exact h1.comp_continuous (continuous_const.update i continuous_id).continuousAt
  have h0 := hloc.hasDerivAt_eq_zero
    (hasDerivAt_bitLevelCost_update s E e M M' hV hC hCt hVd hi)
  exact ⟨by linarith, (levelCost_stationary_iff hC hCt hVd).1 h0⟩

/-- The variance bound (26) is positive when every `E[x̄_k²] ≥ 0` and some variable has
`E[x̄_i²] > 0` (Haas–Giles 2025, §4.2, p. 9). -/
lemma vIndepR_pos {s : Finset ι} {E : ι → ℝ} (hE : ∀ k ∈ s, 0 ≤ E k) {i : ι} (hi : i ∈ s)
    (hEi : 0 < E i) (e : ι → ℤ) (d : ι → ℝ) : 0 < vIndepR s E e d :=
  mul_pos (by norm_num) (Finset.sum_pos'
    (fun k hk => mul_nonneg (hE k hk) (Real.rpow_pos_of_pos (by norm_num) _).le)
    ⟨i, hi, mul_pos hEi (Real.rpow_pos_of_pos (by norm_num) _)⟩)

/-- Each scalar equation (35), `−(log 4) E 4^{e − t}/12 + λ (M t + M') = 0`, has at most one
solution `t` when `λ, E > 0` and `M ≥ 0` (Haas–Giles 2025, §6.1, p. 12; existence is
`exists_unique_bitWidth`). -/
lemma eq35_unique {lam E M M' : ℝ} (e : ℝ) (hlam : 0 < lam) (hE : 0 < E) (hM : 0 ≤ M)
    {t₁ t₂ : ℝ} (h₁ : -(Real.log 4 * E * (4 : ℝ) ^ (e - t₁) / 12) + lam * (M * t₁ + M') = 0)
    (h₂ : -(Real.log 4 * E * (4 : ℝ) ^ (e - t₂) / 12) + lam * (M * t₂ + M') = 0) :
    t₁ = t₂ := by
  have hc : 0 < Real.log 4 * E := mul_pos (Real.log_pos (by norm_num)) hE
  have key : ∀ {a b : ℝ}, a < b →
      -(Real.log 4 * E * (4 : ℝ) ^ (e - a) / 12) + lam * (M * a + M') = 0 →
      -(Real.log 4 * E * (4 : ℝ) ^ (e - b) / 12) + lam * (M * b + M') = 0 → False := by
    intro a b hab ha hb
    have h4 : (4 : ℝ) ^ (e - b) < (4 : ℝ) ^ (e - a) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    have h5 := mul_lt_mul_of_pos_left h4 hc
    have h6 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab.le hM) hlam.le
    linarith
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · exact (key h h₁ h₂).elim
  · exact h
  · exact (key h h₂ h₁).elim

/-- **The Lagrange approach reaches the optimum** (Haas–Giles 2025, §6.1, p. 12: "The idea is
therefore that given a guess of `λ` we solve iteratively a system for the bit-widths `d_{i,ℓ}`,
then update the value of `λ` until we reach the optimal solution of the overall problem").  Let
`d*` minimise (34) over a set `S` that is a neighbourhood of `d*` (e.g. `S = {d ≥ 0}` and all
`d*_i > 0`), with `C̃_ℓ(d*) > 0`, `V_ℓ, C_ℓ > 0`, `E[x̄_i²] > 0` and `M_i ≥ 0`.  Then
`λ* = √(V_ℓ V^Δ_ℓ(d*)/(C_ℓ C̃_ℓ(d*)))` is positive, `d*` solves the uncoupled equations (35) for
`λ*`, it minimises the Lagrangian `V^Δ_ℓ + λ* C̃_ℓ` over all real bit-widths, and every solution
of (35) for `λ*` agrees with `d*` on the variables: there is a single `λ`, namely `λ*`, whose
solution of (35) is the optimum.  That `λ*` also minimises the function of `λ` that the paper's
search minimises is `isMinOn_lambda_bitLevelCost`; the uniqueness of the minimiser over `λ` and
the convergence of the paper's iteration (golden section search over `λ`) are not addressed. -/
theorem lagrange_of_isMinOn_bitLevelCost (s : Finset ι) {E : ι → ℝ}
    (e : ι → ℤ) {M : ι → ℝ} (M' : ι → ℝ) {V C : ℝ} (hV : 0 < V) (hC : 0 < C)
    (hE : ∀ i ∈ s, 0 < E i) (hM : ∀ i ∈ s, 0 ≤ M i) {S : Set (ι → ℝ)} {dstar : ι → ℝ}
    (hmin : IsMinOn (bitLevelCost s E e M M' V C) S dstar) (hS : S ∈ 𝓝 dstar)
    (hCt : 0 < sepCost s M M' dstar) :
    0 < Real.sqrt (V * vIndepR s E e dstar / (C * sepCost s M M' dstar)) ∧
    (∀ i ∈ s, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
        Real.sqrt (V * vIndepR s E e dstar / (C * sepCost s M M' dstar)) *
          (M i * dstar i + M' i) = 0) ∧
    (∀ d : ι → ℝ, vIndepR s E e dstar +
        Real.sqrt (V * vIndepR s E e dstar / (C * sepCost s M M' dstar)) *
          sepCost s M M' dstar ≤
      vIndepR s E e d + Real.sqrt (V * vIndepR s E e dstar / (C * sepCost s M M' dstar)) *
          sepCost s M M' d) ∧
    (∀ d : ι → ℝ, (∀ i ∈ s, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - d i) / 12) +
        Real.sqrt (V * vIndepR s E e dstar / (C * sepCost s M M' dstar)) *
          (M i * d i + M' i) = 0) → ∀ i ∈ s, d i = dstar i) := by
  obtain ⟨i₀, hi₀⟩ : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · rw [h] at hCt
      simp [sepCost] at hCt
    · exact h
  have hVd := vIndepR_pos (fun k hk => (hE k hk).le) hi₀ (hE i₀ hi₀) e dstar
  have hlam : 0 < Real.sqrt (V * vIndepR s E e dstar / (C * sepCost s M M' dstar)) :=
    Real.sqrt_pos.2 (div_pos (mul_pos hV hVd) (mul_pos hC hCt))
  have h35 := fun i hi => (eq36_eq35_of_isLocalMin s E e M M' hV hC (hmin.isLocalMin hS) hCt
    hVd i hi).2
  refine ⟨hlam, h35, lagrangian_le_of_eq35 s E e M M' (fun i hi => (hE i hi).le) hM hlam.le h35,
    fun d hd i hi => eq35_unique (e i : ℝ) hlam (hE i hi) (hM i hi) (hd i hi) (h35 i hi)⟩

/-- **The bit-widths of the `λ`-search** (Haas–Giles 2025, §6.1, p. 12: "given a guess of `λ` we
solve iteratively a system for the bit-widths `d_{i,ℓ}`"; (35) "gives a set of uncoupled
nonlinear scalar equations for each pair `i, ℓ`, which are easily solved to obtain `d_{i,ℓ}`",
p. 11).  For each variable `i`, `lambdaBitWidth E e M M' λ i` is a solution `t` of the scalar
equation (35), `−(log 4) E[x̄_i²] 4^{e_i − t}/12 + λ (M_i t + M'_i) = 0`, chosen with
`Classical.epsilon`.  For `λ > 0`, `E[x̄_i²] > 0` and `M_i, M'_i ≥ 0` not both zero it is the
unique solution (`eq35_lambdaBitWidth`, `exists_unique_bitWidth`); when the equation has no
solution its value is unspecified.  The function of `λ` plotted in Figure 3 is
`λ ↦ bitLevelCost univ E e M M' V C (lambdaBitWidth E e M M' λ)`. -/
noncomputable def lambdaBitWidth (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ) (lam : ℝ) : ι → ℝ :=
  fun i => Classical.epsilon fun t : ℝ =>
    -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - t) / 12) + lam * (M i * t + M' i) = 0

/-- `lambdaBitWidth` solves the equation (35) of a variable whenever that equation has a
solution. -/
lemma eq35_lambdaBitWidth_of_exists (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ) (lam : ℝ) {i : ι}
    (h : ∃ t : ℝ, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - t) / 12) +
      lam * (M i * t + M' i) = 0) :
    -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - lambdaBitWidth E e M M' lam i) / 12) +
      lam * (M i * lambdaBitWidth E e M M' lam i + M' i) = 0 :=
  Classical.epsilon_spec h

/-- For `λ > 0`, `E[x̄_i²] > 0` and `M_i, M'_i ≥ 0` not both zero, `lambdaBitWidth` solves the
uncoupled equations (35) (Haas–Giles 2025, §6.1, p. 12; `exists_unique_bitWidth`). -/
lemma eq35_lambdaBitWidth (s : Finset ι) {E : ι → ℝ} (e : ι → ℤ) {M M' : ι → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hE : ∀ i ∈ s, 0 < E i) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hM' : ∀ i ∈ s, 0 ≤ M' i) (hMM : ∀ i ∈ s, 0 < M i + M' i) :
    ∀ i ∈ s,
      -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - lambdaBitWidth E e M M' lam i) / 12) +
        lam * (M i * lambdaBitWidth E e M M' lam i + M' i) = 0 := fun i hi =>
  eq35_lambdaBitWidth_of_exists E e M M' lam
    (exists_unique_bitWidth (e i) hlam (hE i hi) (hM i hi) (hM' i hi) (hMM i hi)).exists

/-- **The optimum over `λ` is the optimum over the bit-widths** (Haas–Giles 2025, §6.1, p. 12:
"update the value of `λ` until we reach the optimal solution of the overall problem"; "The
optimal value for `λ` is then determined by golden section search optimisation").  The search
minimises the function of `λ` of Figure 3, `G(λ) = (34)` at the solution `d(λ)` of (35)
(`lambdaBitWidth`).  Let `d*` minimise (34) over a set `S` of real bit-widths that is a
neighbourhood of `d*` (an interior optimum, e.g. `S = {d ≥ 0}` and all `d*_i > 0`), with
`C̃_ℓ(d*) > 0`, `V_ℓ, C_ℓ > 0`, `E[x̄_i²] > 0` and `M_i ≥ 0`, and let
`λ* = √(V_ℓ V^Δ_ℓ(d*)/(C_ℓ C̃_ℓ(d*)))`.  Then `λ* > 0` and `d(λ*) = d*`, so
`G(λ*) = (34)(d*)` is the minimum of (34) over `S`, and `λ*` minimises `G` over all `λ > 0` whose
`d(λ)` lies in `S`: the minimum over `λ` equals the minimum over the bit-widths.  Deviation: the
optimum `d*` is assumed to be interior (for a minimiser on the bound `d_i = 0` (35) can fail,
`kkt_of_isMinOn_box`); for `M'_i ≥ 0` and `M_i + M'_i > 0`, `d(λ)` solves (35) for every `λ > 0`
(`eq35_lambdaBitWidth`).  The uniqueness of the minimiser over `λ` and the convergence of the
golden section search are not addressed. -/
theorem isMinOn_lambda_bitLevelCost [Fintype ι] {E : ι → ℝ} (e : ι → ℤ) {M : ι → ℝ}
    (M' : ι → ℝ) {V C : ℝ} (hV : 0 < V) (hC : 0 < C) (hE : ∀ i, 0 < E i) (hM : ∀ i, 0 ≤ M i)
    {S : Set (ι → ℝ)} {dstar : ι → ℝ} (hmin : IsMinOn (bitLevelCost univ E e M M' V C) S dstar)
    (hS : S ∈ 𝓝 dstar) (hCt : 0 < sepCost univ M M' dstar) :
    0 < Real.sqrt (V * vIndepR univ E e dstar / (C * sepCost univ M M' dstar)) ∧
    lambdaBitWidth E e M M'
      (Real.sqrt (V * vIndepR univ E e dstar / (C * sepCost univ M M' dstar))) = dstar ∧
    IsMinOn (fun lam => bitLevelCost univ E e M M' V C (lambdaBitWidth E e M M' lam))
      {lam | 0 < lam ∧ lambdaBitWidth E e M M' lam ∈ S}
      (Real.sqrt (V * vIndepR univ E e dstar / (C * sepCost univ M M' dstar))) := by
  obtain ⟨hlam, h35, -, -⟩ := lagrange_of_isMinOn_bitLevelCost univ e M' hV hC
    (fun i _ => hE i) (fun i _ => hM i) hmin hS hCt
  have hfix : lambdaBitWidth E e M M'
      (Real.sqrt (V * vIndepR univ E e dstar / (C * sepCost univ M M' dstar))) = dstar :=
    funext fun i => eq35_unique (e i : ℝ) hlam (hE i) (hM i)
      (eq35_lambdaBitWidth_of_exists E e M M' _ ⟨dstar i, h35 i (mem_univ i)⟩)
      (h35 i (mem_univ i))
  refine ⟨hlam, hfix, isMinOn_iff.2 fun lam hlam' => ?_⟩
  rw [hfix]
  exact isMinOn_iff.1 hmin _ hlam'.2

/-- **Optimised bit-widths are strictly better than uniform ones** (Haas–Giles 2025, §6.1, p. 12:
"Figure 5 also confirms that the optimisation method we suggest improves the level cost compared
to the best uniform bit-width choice").  Let `d*` minimise (34) over `S`, and let the uniform
configuration `d_i = w` be an interior point of `S` with `C̃_ℓ > 0` (and `V_ℓ, C_ℓ > 0`,
`E[x̄_k²] ≥ 0`).  If for two variables `i, j` the variance factors `E[x̄²] 4^e` are not
proportional to the marginal costs `M w + M'`, i.e.
`E[x̄_i²] 4^{e_i} (M_j w + M'_j) ≠ E[x̄_j²] 4^{e_j} (M_i w + M'_i)`, then the level cost (34) at
`d*` is strictly smaller than at the uniform configuration: a uniform optimum would satisfy (35)
(`eq36_eq35_of_isLocalMin`), which forces the proportionality.  (The non-proportionality forces
`E[x̄_i²] > 0` or `E[x̄_j²] > 0`, hence `V^Δ_ℓ > 0`.) -/
theorem bitLevelCost_lt_uniform (s : Finset ι) {E : ι → ℝ} (e : ι → ℤ)
    (M M' : ι → ℝ) {V C : ℝ} (hV : 0 < V) (hC : 0 < C) (hE : ∀ k ∈ s, 0 ≤ E k)
    {S : Set (ι → ℝ)} {dstar : ι → ℝ} (hmin : IsMinOn (bitLevelCost s E e M M' V C) S dstar)
    {w : ℝ} (hS : S ∈ 𝓝 (fun _ : ι => w)) (hCt : 0 < sepCost s M M' (fun _ => w)) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s)
    (hij : E i * (4 : ℝ) ^ (e i : ℝ) * (M j * w + M' j) ≠
      E j * (4 : ℝ) ^ (e j : ℝ) * (M i * w + M' i)) :
    bitLevelCost s E e M M' V C dstar < bitLevelCost s E e M M' V C (fun _ => w) := by
  by_contra hlt
  rw [not_lt] at hlt
  have hminw : IsMinOn (bitLevelCost s E e M M' V C) S (fun _ => w) :=
    isMinOn_iff.2 fun y hy => hlt.trans (isMinOn_iff.1 hmin y hy)
  have hVd : 0 < vIndepR s E e (fun _ => w) := by
    rcases (hE i hi).eq_or_lt with h0 | h0
    · have hj0 : E j ≠ 0 := by
        intro hj0
        apply hij
        rw [← h0, hj0]
        ring
      exact vIndepR_pos hE hj (lt_of_le_of_ne (hE j hj) (Ne.symm hj0)) e _
    · exact vIndepR_pos hE hi h0 e _
  have h := eq36_eq35_of_isLocalMin s E e M M' hV hC (hminw.isLocalMin hS) hCt hVd
  have hi35 := (h i hi).2
  have hj35 := (h j hj).2
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 4)] at hi35 hj35
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hprod : Real.log 4 / (12 * (4 : ℝ) ^ w) *
      (E i * (4 : ℝ) ^ (e i : ℝ) * (M j * w + M' j) -
        E j * (4 : ℝ) ^ (e j : ℝ) * (M i * w + M' i)) = 0 := by
    linear_combination (-(M j * w + M' j)) * hi35 + (M i * w + M' i) * hj35
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact absurd h0 (div_pos hlog (by positivity)).ne'
  · exact hij (sub_eq_zero.1 h0)

/-- One-sided Fermat: if `f` has a minimum on `[a, ∞)` at `a` and a derivative `f'` at `a`, then
`f' ≥ 0`. -/
lemma hasDerivAt_nonneg_of_isMinOn_Ici {f : ℝ → ℝ} {a f' : ℝ} (hmin : IsMinOn f (Set.Ici a) a)
    (hf : HasDerivAt f f' a) : 0 ≤ f' := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi a) (lt_irrefl a)).1
    hf.hasDerivWithinAt
  refine ge_of_tendsto h (eventually_nhdsWithin_of_forall fun t (ht : a < t) => ?_)
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.2 (isMinOn_iff.1 hmin t ht.le)) (sub_nonneg.2 ht.le)

/-- The factorisation behind "(36) is of the form (35)" (Haas–Giles 2025, §6.1, p. 12):
`√(C/V^Δ) λ = √(V/C̃)` for `λ = √(V V^Δ/(C C̃))`. -/
lemma sqrt_div_mul_sqrt_lambda {V C Ct Vd : ℝ} (hC : 0 < C) (hCt : 0 < Ct) (hVd : 0 < Vd) :
    Real.sqrt (C / Vd) * Real.sqrt (V * Vd / (C * Ct)) = Real.sqrt (V / Ct) := by
  rw [← Real.sqrt_mul (div_pos hC hVd).le]
  congr 1
  rw [div_mul_div_comm, div_eq_div_iff (mul_pos hVd (mul_pos hC hCt)).ne' hCt.ne']
  ring

/-- **First-order conditions at an optimum with bounded bit-widths** (Haas–Giles 2025, §6.1,
p. 12, (35)–(36); the paper's bit-widths are eventually "positive integers", §6.2, p. 13, while
the relaxed problem of §6.1 leaves the bound implicit).  Let `d*` minimise (34) over the box
`d_i ≥ b_i` (e.g. `b = 0`), with `d*` in the box, `C̃_ℓ(d*) > 0`, `V^Δ_ℓ(d*) > 0` and
`V_ℓ, C_ℓ > 0`, and let `λ = √(V_ℓ V^Δ_ℓ(d*)/(C_ℓ C̃_ℓ(d*)))`.  Then for every variable
`∂V^Δ_ℓ/∂d_i + λ ∂C̃_ℓ/∂d_i ≥ 0`, with equality, i.e. (35), when `d*_i > b_i`.  A variable can sit
on its bound with strict inequality; (35) then fails for it. -/
theorem kkt_of_isMinOn_box (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ)
    (M M' : ι → ℝ) {V C : ℝ} (hV : 0 < V) (hC : 0 < C) {b dstar : ι → ℝ}
    (hmin : IsMinOn (bitLevelCost s E e M M' V C) {d | ∀ i ∈ s, b i ≤ d i} dstar)
    (hd : ∀ i ∈ s, b i ≤ dstar i) (hCt : 0 < sepCost s M M' dstar)
    (hVd : 0 < vIndepR s E e dstar) :
    ∀ i ∈ s,
      0 ≤ -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
        Real.sqrt (V * vIndepR s E e dstar / (C * sepCost s M M' dstar)) *
          (M i * dstar i + M' i) ∧
      (b i < dstar i →
        -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
          Real.sqrt (V * vIndepR s E e dstar / (C * sepCost s M M' dstar)) *
            (M i * dstar i + M' i) = 0) := by
  classical
  intro i hi
  set F := bitLevelCost s E e M M' V C
  have hφ : ∀ t, b i ≤ t → F dstar ≤ F (Function.update dstar i t) := fun t ht =>
    isMinOn_iff.1 hmin _ fun j hj => by
      rcases eq_or_ne j i with rfl | hji
      · rw [Function.update_self]
        exact ht
      · rw [Function.update_of_ne hji]
        exact hd j hj
  have hderiv := hasDerivAt_bitLevelCost_update s E e M M' hV hC hCt hVd hi
  have hfac := sqrt_div_mul_sqrt_lambda (V := V) hC hCt hVd
  have ha : 0 < Real.sqrt (C / vIndepR s E e dstar) :=
    Real.sqrt_pos.2 (div_pos hC hVd)
  have hmin' : IsMinOn (fun t => F (Function.update dstar i t)) (Set.Ici (dstar i)) (dstar i) :=
    isMinOn_iff.2 fun t ht => by
      rw [Function.update_eq_self]
      exact hφ t ((hd i hi).trans ht)
  have h0 := hasDerivAt_nonneg_of_isMinOn_Ici hmin' hderiv
  refine ⟨?_, fun hlt => ?_⟩
  · set lam := Real.sqrt (V * vIndepR s E e dstar / (C * sepCost s M M' dstar))
    set x := -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
      lam * (M i * dstar i + M' i)
    have hx : 0 ≤ Real.sqrt (C / vIndepR s E e dstar) * x := by
      have : Real.sqrt (C / vIndepR s E e dstar) * x =
          Real.sqrt (C / vIndepR s E e dstar) *
            -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
          Real.sqrt (V / sepCost s M M' dstar) * (M i * dstar i + M' i) := by
        rw [← hfac]
        ring
      rw [this]
      linarith
    exact nonneg_of_mul_nonneg_right (by linarith) ha
  · have hmin'' : IsMinOn (fun t => F (Function.update dstar i t)) (Set.Ici (b i)) (dstar i) :=
      isMinOn_iff.2 fun t ht => by
        rw [Function.update_eq_self]
        exact hφ t ht
    exact (levelCost_stationary_iff hC hCt hVd).1
      ((hmin''.isLocalMin (Ici_mem_nhds hlt)).hasDerivAt_eq_zero hderiv)

end firstOrder

section convexity

variable {ι : Type*}

/-- Minkowski's inequality for convex combinations in the Euclidean norm:
`√(∑ (a X_i + b Y_i)²) ≤ a √(∑ X_i²) + b √(∑ Y_i²)` for `a, b ≥ 0`. -/
lemma sqrt_sum_sq_convex_comb_le (s : Finset ι) (X Y : ι → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (∑ i ∈ s, (a * X i + b * Y i) ^ 2) ≤
      a * Real.sqrt (∑ i ∈ s, X i ^ 2) + b * Real.sqrt (∑ i ∈ s, Y i ^ 2) := by
  have hP := Real.sq_sqrt (Finset.sum_nonneg fun i (_ : i ∈ s) => sq_nonneg (X i))
  have hQ := Real.sq_sqrt (Finset.sum_nonneg fun i (_ : i ∈ s) => sq_nonneg (Y i))
  have hCS := mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt s X Y) (mul_nonneg ha hb)
  have hexp : ∑ i ∈ s, (a * X i + b * Y i) ^ 2 = a ^ 2 * ∑ i ∈ s, X i ^ 2 +
      2 * (a * b * ∑ i ∈ s, X i * Y i) + b ^ 2 * ∑ i ∈ s, Y i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Real.sqrt_le_left (by positivity), hexp]
  set P := Real.sqrt (∑ i ∈ s, X i ^ 2)
  set Q := Real.sqrt (∑ i ∈ s, Y i ^ 2)
  have hsq : (a * P + b * Q) ^ 2 = a ^ 2 * P ^ 2 + 2 * (a * b * (P * Q)) + b ^ 2 * Q ^ 2 := by
    ring
  rw [hsq, hP, hQ]
  linarith

/-- The variance bound (26) as a squared Euclidean norm (Haas–Giles 2025, §4.2):
`V_indep(d) = ∑_i (√(E[x̄_i²]/12) e^{(log 4)(e_i − d_i)/2})²` for `E[x̄_i²] ≥ 0`. -/
lemma vIndepR_eq_sum_sq (s : Finset ι) {E : ι → ℝ} (hE : ∀ i ∈ s, 0 ≤ E i) (e : ι → ℤ)
    (d : ι → ℝ) :
    vIndepR s E e d = ∑ i ∈ s,
      (Real.sqrt (E i / 12) * Real.exp (Real.log 4 * ((e i : ℝ) - d i) / 2)) ^ 2 := by
  unfold vIndepR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_pow, Real.sq_sqrt (div_nonneg (hE i hi) (by norm_num)), sq (Real.exp _),
    ← Real.exp_add, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [show Real.log 4 * ((e i : ℝ) - d i) / 2 + Real.log 4 * ((e i : ℝ) - d i) / 2 =
    Real.log 4 * ((e i : ℝ) - d i) by ring]
  ring

/-- Each entry `√(E/12) e^{(log 4)(c − t)/2}` of the vector in `vIndepR_eq_sum_sq` is convex in
`t`. -/
lemma sqrt_mul_exp_le (E c x y : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    Real.sqrt (E / 12) * Real.exp (Real.log 4 * (c - (a * x + b * y)) / 2) ≤
      a * (Real.sqrt (E / 12) * Real.exp (Real.log 4 * (c - x) / 2)) +
        b * (Real.sqrt (E / 12) * Real.exp (Real.log 4 * (c - y) / 2)) := by
  have h := convexOn_exp.2 (Set.mem_univ (Real.log 4 * (c - x) / 2))
    (Set.mem_univ (Real.log 4 * (c - y) / 2)) ha hb hab
  simp only [smul_eq_mul] at h
  have hexp : Real.log 4 * (c - (a * x + b * y)) / 2 =
      a * (Real.log 4 * (c - x) / 2) + b * (Real.log 4 * (c - y) / 2) := by
    linear_combination (-(Real.log 4 * c / 2)) * hab
  rw [hexp]
  have h12 : 0 ≤ Real.sqrt (E / 12) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h h12]

/-- Each entry `√(E/12) e^{(log 4)(c − t)/2}` of the vector in `vIndepR_eq_sum_sq` is strictly
convex in `t` when `E > 0`. -/
lemma sqrt_mul_exp_lt {E : ℝ} (hE : 0 < E) (c : ℝ) {x y : ℝ} (hxy : x ≠ y) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Real.sqrt (E / 12) * Real.exp (Real.log 4 * (c - (a * x + b * y)) / 2) <
      a * (Real.sqrt (E / 12) * Real.exp (Real.log 4 * (c - x) / 2)) +
        b * (Real.sqrt (E / 12) * Real.exp (Real.log 4 * (c - y) / 2)) := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hne : Real.log 4 * (c - x) / 2 ≠ Real.log 4 * (c - y) / 2 := by
    intro h
    apply hxy
    have := mul_left_cancel₀ hlog.ne' (by linarith : Real.log 4 * (c - x) = Real.log 4 * (c - y))
    linarith
  have h := strictConvexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) hne ha hb hab
  simp only [smul_eq_mul] at h
  have hexp : Real.log 4 * (c - (a * x + b * y)) / 2 =
      a * (Real.log 4 * (c - x) / 2) + b * (Real.log 4 * (c - y) / 2) := by
    linear_combination (-(Real.log 4 * c / 2)) * hab
  rw [hexp]
  have h12 : 0 < Real.sqrt (E / 12) := Real.sqrt_pos.2 (div_pos hE (by norm_num))
  nlinarith [mul_lt_mul_of_pos_left h h12]

/-- **The variance part of (34) is convex in the bit-widths** (Haas–Giles 2025, §4.2, p. 9, the
bound (26), and §6.1, p. 11, the level cost (34), "approximated as
`√(V_ℓ C̃_ℓ) + √(V^Δ_ℓ C_ℓ)`").  For `E[x̄_i²] ≥ 0`, the function `d ↦ √(V_indep(d))` of the
bound (26) is convex on all real bit-widths: it is the Euclidean norm of the vector
`(√(E[x̄_i²]/12) 2^{e_i − d_i})_i` with convex nonnegative entries (`vIndepR_eq_sum_sq`,
Minkowski's inequality).  So the term `√(V^Δ_ℓ C_ℓ)` of (34) is convex, and any non-convexity of
(34) in the bit-widths comes from the cost term (`not_convexOn_bitLevelCost`).  The paper makes
no convexity claim in the bit-widths: its remark "Although we do not prove it formally we can
see that the resulting function is convex" (p. 12) concerns the function of `λ` of Figure 3;
convexity in the relaxed bit-widths is a related question that the paper does not discuss. -/
theorem convexOn_sqrt_vIndepR (s : Finset ι) {E : ι → ℝ} (hE : ∀ i ∈ s, 0 ≤ E i)
    (e : ι → ℤ) : ConvexOn ℝ Set.univ (fun d => Real.sqrt (vIndepR s E e d)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [vIndepR_eq_sum_sq s hE, vIndepR_eq_sum_sq s hE, vIndepR_eq_sum_sq s hE]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine le_trans (Real.sqrt_le_sqrt (Finset.sum_le_sum fun i hi => pow_le_pow_left₀
    (by positivity) (sqrt_mul_exp_le (E i) (e i : ℝ) (x i) (y i) ha hb hab) 2))
    (sqrt_sum_sq_convex_comb_le s _ _ ha hb)

/-- `d ↦ √(V_indep(d))` is strictly convex when every `E[x̄_i²] > 0` (Haas–Giles 2025, §4.2, (26)):
two configurations differ in some variable, whose entry in `vIndepR_eq_sum_sq` is strictly
convex. -/
lemma strictConvexOn_sqrt_vIndepR [Fintype ι] {E : ι → ℝ} (hE : ∀ i, 0 < E i)
    (e : ι → ℤ) : StrictConvexOn ℝ Set.univ (fun d => Real.sqrt (vIndepR univ E e d)) := by
  have hE' : ∀ i ∈ (univ : Finset ι), 0 ≤ E i := fun i _ => (hE i).le
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hxy
  simp only [smul_eq_mul]
  rw [vIndepR_eq_sum_sq _ hE', vIndepR_eq_sum_sq _ hE', vIndepR_eq_sum_sq _ hE']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine lt_of_lt_of_le (Real.sqrt_lt_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Finset.sum_lt_sum (fun i _ => pow_le_pow_left₀ (by positivity)
      (sqrt_mul_exp_le (E i) (e i : ℝ) (x i) (y i) ha.le hb.le hab) 2)
      ⟨i₀, mem_univ _, pow_lt_pow_left₀ (sqrt_mul_exp_lt (hE i₀) (e i₀ : ℝ) hi₀ ha hb hab)
        (by positivity) two_ne_zero⟩))
    (sqrt_sum_sq_convex_comb_le _ _ _ ha.le hb.le)

/-- Without additions (`M'_i = 0`) the cost (31) is a squared weighted Euclidean norm,
`C̃(d) = ∑_i (√(M_i/2) d_i)²` (Haas–Giles 2025, §5, p. 11). -/
lemma sepCost_eq_sum_sq (s : Finset ι) {M M' : ι → ℝ} (hM : ∀ i ∈ s, 0 ≤ M i)
    (hM' : ∀ i ∈ s, M' i = 0) (d : ι → ℝ) :
    sepCost s M M' d = ∑ i ∈ s, (Real.sqrt (M i / 2) * d i) ^ 2 := by
  have h0 : ∑ i ∈ s, M' i * d i = 0 := Finset.sum_eq_zero fun i hi => by rw [hM' i hi, zero_mul]
  unfold sepCost
  rw [h0, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_pow, Real.sq_sqrt (div_nonneg (hM i hi) (by norm_num))]
  ring

/-- Without additions (`M'_i = 0`, `M_i ≥ 0`) the square root of the cost (31) is convex: it is a
weighted Euclidean norm (Haas–Giles 2025, §5, p. 11). -/
lemma convexOn_sqrt_sepCost (s : Finset ι) {M M' : ι → ℝ} (hM : ∀ i ∈ s, 0 ≤ M i)
    (hM' : ∀ i ∈ s, M' i = 0) : ConvexOn ℝ Set.univ (fun d => Real.sqrt (sepCost s M M' d)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [sepCost_eq_sum_sq s hM hM', sepCost_eq_sum_sq s hM hM', sepCost_eq_sum_sq s hM hM']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h : ∀ i, Real.sqrt (M i / 2) * (a * x i + b * y i) =
      a * (Real.sqrt (M i / 2) * x i) + b * (Real.sqrt (M i / 2) * y i) := fun i => by ring
  simp only [h]
  exact sqrt_sum_sq_convex_comb_le s _ _ ha hb

/-- `V C̃(d)` is the cost (31) with the counts multiplied by `V`. -/
lemma mul_sepCost (s : Finset ι) (M M' : ι → ℝ) (V : ℝ) (d : ι → ℝ) :
    V * sepCost s M M' d = sepCost s (fun i => V * M i) (fun i => V * M' i) d := by
  simp only [sepCost, mul_add, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

/-- `V_indep(d) C` is the bound (26) with the second moments multiplied by `C`. -/
lemma vIndepR_mul (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (C : ℝ) (d : ι → ℝ) :
    vIndepR s E e d * C = vIndepR s (fun i => E i * C) e d := by
  simp only [vIndepR, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The level cost (34) as `√(C̃'(d)) + √(V'(d))` with rescaled cost (31) and bound (26). -/
lemma bitLevelCost_eq (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ) (V C : ℝ) :
    bitLevelCost s E e M M' V C = fun d =>
      Real.sqrt (sepCost s (fun i => V * M i) (fun i => V * M' i) d) +
        Real.sqrt (vIndepR s (fun i => E i * C) e d) := by
  funext d
  rw [bitLevelCost, mul_sepCost, vIndepR_mul]

/-- **Without additions the level cost (34) is convex in the bit-widths** (Haas–Giles 2025, §6.1,
p. 11, (34): "approximated as `√(V_ℓ C̃_ℓ) + √(V^Δ_ℓ C_ℓ)`", with the cost (31) of §5, p. 11).
If no variable is involved in an addition (`M'_i = 0`), then
`√(V_ℓ C̃_ℓ(d)) = √(V_ℓ/2 ∑_i M_i d_i²)` is a weighted Euclidean norm, and (34) is convex on all
real bit-widths, for `E[x̄_i²], M_i, V_ℓ, C_ℓ ≥ 0`.  With additions this fails
(`not_convexOn_bitLevelCost`).  The paper does not state convexity in the bit-widths: its remark
"Although we do not prove it formally we can see that the resulting function is convex" (p. 12)
concerns the function of `λ` of Figure 3; convexity in the relaxed bit-widths is a related
question. -/
theorem convexOn_bitLevelCost (s : Finset ι) {E : ι → ℝ} (hE : ∀ i ∈ s, 0 ≤ E i) (e : ι → ℤ)
    {M M' : ι → ℝ} (hM : ∀ i ∈ s, 0 ≤ M i) (hM' : ∀ i ∈ s, M' i = 0) {V C : ℝ} (hV : 0 ≤ V)
    (hC : 0 ≤ C) : ConvexOn ℝ Set.univ (bitLevelCost s E e M M' V C) := by
  rw [bitLevelCost_eq]
  exact (convexOn_sqrt_sepCost s (fun i hi => mul_nonneg hV (hM i hi))
    (fun i hi => by rw [hM' i hi, mul_zero])).add
    (convexOn_sqrt_vIndepR s (fun i hi => mul_nonneg (hE i hi) hC) e)

/-- **Without additions the level cost (34) is strictly convex in the bit-widths** (Haas–Giles
2025, §6.1, p. 11, (34): "approximated as `√(V_ℓ C̃_ℓ) + √(V^Δ_ℓ C_ℓ)`") when, moreover, every
`E[x̄_i²] > 0` and `C_ℓ > 0`: its variance part `√(V^Δ_ℓ C_ℓ)` is then strictly convex
(`strictConvexOn_sqrt_vIndepR`).  As for `convexOn_bitLevelCost`, the paper's convexity remark
(p. 12) is about the function of `λ` of Figure 3, not about (34) in the bit-widths. -/
theorem strictConvexOn_bitLevelCost [Fintype ι] {E : ι → ℝ} (hE : ∀ i, 0 < E i) (e : ι → ℤ)
    {M M' : ι → ℝ} (hM : ∀ i, 0 ≤ M i) (hM' : ∀ i, M' i = 0) {V C : ℝ} (hV : 0 ≤ V)
    (hC : 0 < C) : StrictConvexOn ℝ Set.univ (bitLevelCost univ E e M M' V C) := by
  rw [bitLevelCost_eq]
  exact (convexOn_sqrt_sepCost univ (fun i _ => mul_nonneg hV (hM i))
    (fun i _ => by rw [hM' i, mul_zero])).add_strictConvexOn
    (strictConvexOn_sqrt_vIndepR (fun i => mul_pos (hE i) hC) e)

/-- **Without additions the optimal bit-widths are unique** (Haas–Giles 2025, §6.1, p. 12: "the
optimal solution of the overall problem"; the minimisation of (34), p. 11).  If `M'_i = 0`,
`M_i > 0` and `E[x̄_i²] > 0` for every variable and `V_ℓ, C_ℓ > 0`, then on every nonempty closed
convex set of real bit-widths (e.g. `d ≥ 0`) the level cost (34) has exactly one minimiser
(`exists_isMinOn_bitLevelCost`, `strictConvexOn_bitLevelCost`).  The paper's convexity remark
(p. 12) is about the function of `λ` of Figure 3; this is the related uniqueness question in the
relaxed bit-widths, which the paper does not discuss.  With additions uniqueness can fail:
numerically, for one variable with `E[x̄²] = 12`, `e = 0`, `M = M' = V_ℓ = 1` and
`C_ℓ = 5.98905644…`, (34) on `d ≥ 0` has the two minimisers `d = 0` and `d = 1.07087811…`, both
with value `√C_ℓ` (not proved here). -/
theorem existsUnique_isMinOn_bitLevelCost [Fintype ι] {E : ι → ℝ} (hE : ∀ i, 0 < E i)
    (e : ι → ℤ) {M M' : ι → ℝ} (hM : ∀ i, 0 < M i) (hM' : ∀ i, M' i = 0) {V C : ℝ}
    (hV : 0 < V) (hC : 0 < C) {S : Set (ι → ℝ)} (hS : IsClosed S) (hSc : Convex ℝ S)
    (hne : S.Nonempty) :
    ∃! dstar : ι → ℝ, dstar ∈ S ∧ IsMinOn (bitLevelCost univ E e M M' V C) S dstar := by
  obtain ⟨dstar, hd, hmin⟩ := exists_isMinOn_bitLevelCost E e M' C hV hM hS hne
  have hstrict := (strictConvexOn_bitLevelCost hE e (fun i => (hM i).le) hM' hV.le hC).subset
    (Set.subset_univ S) hSc
  exact ⟨dstar, ⟨hd, hmin⟩, fun y hy => hstrict.eq_of_isMinOn hy.2 hmin hy.1 hd⟩

/-- **With additions the level cost (34) need not be convex in the bit-widths** (Haas–Giles 2025,
§6.1, p. 11, (34): "approximated as `√(V_ℓ C̃_ℓ) + √(V^Δ_ℓ C_ℓ)`", with the cost (31) of §5).
For one variable with `E[x̄²] = 12`, `e = 0`, `M = M' = 1` and `V_ℓ = C_ℓ = 1`, (34) is
`√(d²/2 + d) + 2^{−d}`, and on `d ≥ 0` its value `√(3/2) + 1/2` at `d = 1` exceeds the mean
`13/8` of its values `1` at `d = 0` and `9/4` at `d = 2`.  The cause is the cost:
`√(M d²/2 + M' d)` is strictly concave for `M' > 0`.  This does not contradict the paper, which
does not claim convexity in the bit-widths: its remark "Although we do not prove it formally we
can see that the resulting function is convex which ensures the existence of an optimum" (p. 12)
concerns the function of `λ` plotted in Figure 3, (34) at the solution of (35), on a logarithmic
`λ` axis.  That function need not be convex either for other parameters than the paper's (the
remark concerns the plotted example), as numerical examples show (not proved here): on the
`log λ` axis of Figure 3, for two variables with variance factors
`E[x̄_i²] 4^{e_i}/12 = 0.0250113` and `173.236`, `M = (2, 1)`, `M' = (20, 10)`, `V_ℓ = 1`,
`C_ℓ = 252.344`, it is concave for `2.2·10⁻⁹ ≤ λ ≤ 2.6·10⁻⁷`, where the bit-widths
lie between 6 and 16; on a linear `λ` axis it fails to be convex even without additions (one
variable, `E[x̄²] 4^e/12 = 1895.1`, `M = 2`, `M' = 0`, `V_ℓ = 1`, `C_ℓ = 4.87055`: concave near
`λ = 0.29`, `d = 4.9`).  The existence of an optimum does not need convexity
(`exists_isMinOn_bitLevelCost_of_nonneg`, `isMinOn_lambda_bitLevelCost`). -/
theorem not_convexOn_bitLevelCost :
    ¬ ConvexOn ℝ {d : Unit → ℝ | ∀ i, 0 ≤ d i}
      (bitLevelCost univ (fun _ => 12) (fun _ => 0) (fun _ => 1) (fun _ => 1) 1 1) := by
  intro h
  have hx : (fun _ : Unit => (0 : ℝ)) ∈ {d : Unit → ℝ | ∀ i, 0 ≤ d i} := fun _ => le_rfl
  have hy : (fun _ : Unit => (2 : ℝ)) ∈ {d : Unit → ℝ | ∀ i, 0 ≤ d i} := fun _ => by norm_num
  have h1 := h.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmid : (1 / 2 : ℝ) • (fun _ : Unit => (0 : ℝ)) + (1 / 2 : ℝ) • (fun _ : Unit => (2 : ℝ)) =
      fun _ => 1 := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num
  rw [hmid] at h1
  simp only [bitLevelCost, sepCost, vIndepR, univ_unique, sum_singleton, smul_eq_mul] at h1
  norm_num at h1
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4, h16] at h1
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h32 : 9 / 8 * Real.sqrt 2 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by positivity), mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h33 : 9 / 8 < Real.sqrt 3 / Real.sqrt 2 := by
    rw [lt_div_iff₀ h2]
    exact h32
  linarith

end convexity

end MLMC
