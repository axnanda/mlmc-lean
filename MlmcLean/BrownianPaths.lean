import MlmcLean.SDEExtras
import MlmcLean.AsymptoticNormal
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# Brownian paths for multilevel SDE simulation: union grids, bridge midpoint, time reversal

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.2
"Milstein discretisation" (pp. 38–39), §5.3 "Multi-dimensional SDEs" (pp. 39 and 42) and §5.6
"Stiff and highly nonlinear SDEs" (pp. 44–45, Figure 5.9 and Algorithm 3).  Line numbers refer
to the text `docs/giles2015.txt`.  The paper uses the following constructions of the driving
Brownian path without proof; this file proves them.

**§5.6, Algorithm 3: the union of two grids** (lines 1926–1929, p. 44: "The underlying Brownian
path needs to be sampled at a set of times which are the union of the simulation times used by
the coarse and fine path. The independent Brownian increments can be simulated for each time
interval, and summed to give `W(t)` at the required times.").
* `iIndepFun_blockSum`: sums of independent `N(m_i, v_i)` variables over pairwise disjoint finite
  blocks are independent, the sum over a block `S` being `N(∑_{i ∈ S} m_i, ∑_{i ∈ S} v_i)` (the
  Gaussian analogue of `iIndepFun_stepCounts` in `PoissonGrids.lean`).
* `unionGridBM`: on the sorted union grid `u_0 ≤ u_1 ≤ ⋯`,
  `W(u_k) = ∑_{i<k} √(u_{i+1} − u_i) Z_i` with `Z_0, Z_1, …` independent standard normal
  variables on any probability space (e.g. the coordinates of `stdNormalSeq`), as Algorithm 3
  accumulates `∆W := √h Z` (lines 1938–1966, p. 45).  A finite union grid
  `0 = u_0 < ⋯ < u_K = T` is extended by `u_k = T` for `k > K`, so that `u` is monotone on `ℕ`.
* `unionGridBM_increments`, `unionGridBM_hasLaw`, `unionGridBM_map_eq`,
  `unionGrid_brownian_map_eq`: for a path whose times `t_j = u_{τ(j)}` are among the union-grid
  times (`τ` monotone), the increments `W(t_{j+1}) − W(t_j)` are independent
  `N(0, t_{j+1} − t_j)`; so the fine and the coarse path each have exactly the law of the
  single-level scheme on their own grid, driven by `√(t_{j+1} − t_j) Z_j`.

**§5.2: the Brownian-bridge midpoint** (lines 1699–1701, p. 39: the coarse interpolant at the fine
time uses "the Brownian increments `W_{n+1} − W_n` and `W_{n+2} − W_{n+1}` already generated for
the fine path. The standard Brownian path results can then be used to obtain the coarse path
payoff approximations").
* `bridge_midpoint_law`: if `∆W₁`, `∆W₂` are independent `N(0, h/2)`, then
  `W(t + h/2) = ½(W(t) + W(t + h)) + ½(∆W₁ − ∆W₂)`, where `½(∆W₁ − ∆W₂) ~ N(0, h/4)` is
  independent of `∆W₁ + ∆W₂ ~ N(0, h)` (the paper's volatility factor `b^c_n` only rescales the
  deviation and is omitted).
* `brownian_bridge_midpoint`: for a pre-Brownian motion `B`,
  `B(s + h/2) − ½(B(s) + B(s + h)) ~ N(0, h/4)`, independent of `B(s + h)` and of the past
  `(B(r))_{r ≤ s}`.

**§5.3: weighted averages of assets** (lines 1718–1722, p. 39: "if the financial option depends on
the weighted average of a set of underlying assets, then the Brownian interpolation for each
individual asset leads naturally to a Brownian interpolation for the average").
* `bridgeInterp_weighted_sum`: the interpolant `bridgeInterp` of `SDEExtras.lean` is linear in
  `(S, b W)`: the weighted average of the per-asset interpolants is the interpolant (with unit
  volatility) of the averaged values, driven by the averaged path `∑_a w_a b_a W_a`.

**§5.3: the antithetic path by time reversal** (lines 1805–1809, p. 42: "`ω^a_i` is an antithetic
counterpart defined by a time-reversal of the Brownian path within each coarse timestep. This
results in the Brownian increments for the antithetic fine path being swapped relative to the
original path").
* `antitheticBM`: on each coarse step `[kH, (k+1)H)`, `B^a(t) = B(kH) + B((k+1)H) − B((2k+1)H − t)`;
  `isPreBrownianReal_antitheticBM`: `B^a` is again a pre-Brownian motion (Mathlib's
  `IsPreBrownianReal`: it has the finite-dimensional laws of Brownian motion), so every payoff
  depending on finitely many path values has the same law for the antithetic and the original
  path.
* `iIndepFun_antitheticBM`: the multi-dimensional case.  The paper uses the reversal for
  multi-dimensional SDEs (lines 1728–1735, p. 39), driven by a `d`-dimensional Brownian motion
  with independent components; reversing each component gives independent pre-Brownian
  components again.
* `antitheticBM_natCast_mul`: `B^a = B` at the coarse times, so the coarse path is unchanged;
  `fineIncrements_antitheticBM`: with `H = 2h`, the fine increments of `B^a` are those of `B`
  swapped within each coarse step (`swapIncrements`), whose law invariance is the discrete
  statement `measurePreserving_swapIncrements` of `SDEExtras.lean`.
* `reverseFirstStep`, `isPreBrownianReal_reverseFirstStep`, `reverseFirstStep_fineIncrements`:
  the reversal within the first coarse step only, `B^a(t) = B(H) − B(H − t)` for `t ≤ H` and
  `B^a(t) = B(t)` for `t > H`.
* `isPreBrownianReal_reflect` is the common engine: reflecting a pre-Brownian motion in time
  inside each interval of a family of intervals that are equal or disjoint (for `s ≤ t` the
  interval of `s` is that of `t` or lies to its left) gives a pre-Brownian motion.  (For nested
  intervals this fails.)

**Scope.**  The grids are deterministic.  In the adaptive scheme of §5.6 the timesteps
`h_ℓ = 2^{−ℓ} H(Ŝ_n)` depend on the path, and identifying the law of each path then needs
Brownian motion at stopping times, which is not formalised (as in `PoissonGrids.lean`).
Pre-Brownian motion fixes the finite-dimensional laws only; the continuity of the paths of `B^a`
is not proved, so payoffs of a continuum of path values (the lookback and barrier payoffs) are
not covered.  The time-reversal results are stated for one scalar Brownian component `B`; the
`d`-dimensional Brownian motion of §5.3 is handled componentwise: the pathwise statements apply
to each component, and `iIndepFun_antitheticBM` gives the law of the reversed `d`-dimensional
path (independent components; correlated Brownian motions are not treated).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MLMC

/-! ### Sums of independent Gaussian increments over disjoint blocks -/

section Blocks

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ι → Ω → ℝ} {v : ι → ℝ≥0}

/-- Independent real Gaussian variables form a Gaussian process (Giles 2015, §5.6: the
independent Brownian increments on the sub-intervals of the union grid): every finite family of
them is jointly Gaussian. -/
lemma isGaussianProcess_of_iIndepFun (hind : iIndepFun X μ)
    (hX : ∀ i, HasGaussianLaw (X i) μ) : IsGaussianProcess X μ where
  hasGaussianLaw _ := (hind.precomp Subtype.val_injective).hasGaussianLaw fun i => hX i

/-- The block sums `k ↦ ∑_{i ∈ S k} X_i` of a Gaussian process form a Gaussian process (Giles
2015, §5.6: the Brownian increments "summed to give `W(t)` at the required times"). -/
lemma isGaussianProcess_blockSum {κ : Type*} (hX : IsGaussianProcess X μ) (S : κ → Finset ι) :
    IsGaussianProcess (fun k ω => ∑ i ∈ S k, X i ω) μ :=
  hX.of_isGaussianProcess fun k => ⟨S k,
    { toFun x := ∑ i, x i
      map_add' x y := by simp [Finset.sum_add_distrib]
      map_smul' c x := by simp [Finset.mul_sum] },
    fun ω => by simp [Finset.sum_attach (S k) (fun i => X i ω)]⟩

/-- **Sums of independent Gaussian increments over disjoint blocks are independent Gaussian
increments** (Giles 2015, §5.6, p. 44, lines 1927–1929: "The independent Brownian increments can
be simulated for each time interval, and summed to give `W(t)` at the required times"; the
Brownian counterpart of `iIndepFun_stepCounts`, §8, p. 56).  If the `X_i` are independent with
laws `N(m_i, v_i)` and the finite blocks `S k` are pairwise disjoint, then the block sums
`Y_k = ∑_{i ∈ S k} X_i` are independent and `Y_k` has law `N(∑_{i ∈ S k} m_i, ∑_{i ∈ S k} v_i)`.
The blocks need not cover the index set, and both the index set `ι` and the set `κ` of blocks
may be infinite.  (The Brownian increments of the paper are the centred case `m_i = 0`.) -/
theorem iIndepFun_blockSum {κ : Type*} {m : ι → ℝ} (hind : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) μ) (S : κ → Finset ι)
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndepFun (fun k ω => ∑ i ∈ S k, X i ω) μ ∧
      ∀ k, HasLaw (fun ω => ∑ i ∈ S k, X i ω)
        (gaussianReal (∑ i ∈ S k, m i) (∑ i ∈ S k, v i)) μ := by
  have := hind.isProbabilityMeasure
  have hG := isGaussianProcess_blockSum
    (isGaussianProcess_of_iIndepFun hind fun i => (hX i).hasGaussianLaw)
    (fun p : (_ : κ) × Unit => S p.1)
  have hL2 : ∀ i, MemLp (X i) 2 μ := fun i => (hX i).hasGaussianLaw.memLp_two
  refine ⟨?_, fun k => hasLaw_finsetSum_gaussianReal hX hind (S k)⟩
  have h := IsGaussianProcess.iIndepFun_of_covariance_eq_zero
    (X := fun k (_ : Unit) ω => ∑ i ∈ S k, X i ω) hG
    (fun k _ => (hG.hasGaussianLaw_eval ⟨k, ()⟩).aemeasurable) fun k l hkl _ _ => by
      rw [covariance_fun_sum_fun_sum' (fun i _ => hL2 i) (fun i _ => hL2 i)]
      refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
      have hij : i ≠ j := fun h => Finset.disjoint_left.1 (hS hkl) hi (h ▸ hj)
      exact (hind.indepFun hij).covariance_eq_zero (hL2 i) (hL2 j)
  exact h.comp (fun _ f => f ()) fun _ => measurable_pi_apply ()

end Blocks

/-! ### §5.6, Algorithm 3: the Brownian path on the union of two grids -/

/-- **The Brownian path on the union grid** (Giles 2015, §5.6, pp. 44–45, lines 1926–1929 and
Algorithm 3, lines 1938–1966: "`h := t − t_old`, `∆W := √h Z`, `∆W^c := ∆W^c + ∆W`,
`∆W^f := ∆W^f + ∆W`").  The union of the simulation times of the coarse and the fine path is
`u_0 ≤ u_1 ≤ ⋯`, and `W(u_k) = ∑_{i<k} √(u_{i+1} − u_i) z_i`, driven by the normal variates
`z = (Z_0, Z_1, …)`. -/
noncomputable def unionGridBM (u : ℕ → ℝ) (z : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range k, Real.sqrt (u (i + 1) - u i) * z i

/-- The increment of the union-grid path between two union-grid indices is the sum of the
sub-interval increments in between (Giles 2015, §5.6, Algorithm 3: the accumulators `∆W^c` and
`∆W^f` sum the increments `∆W` since the last update of the path). -/
lemma unionGridBM_sub_eq_sum (u z : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    unionGridBM u z n - unionGridBM u z m =
      ∑ i ∈ Ico m n, Real.sqrt (u (i + 1) - u i) * z i :=
  (Finset.sum_Ico_eq_sub _ hmn).symm

/-- The variances of the sub-intervals of a step add up to the length of the step (Giles 2015,
§5.6): `∑_{m ≤ i < n} (u_{i+1} − u_i) = u_n − u_m` for a monotone grid. -/
lemma sum_toNNReal_Ico {u : ℕ → ℝ} (hu : Monotone u) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Ico m n, (u (i + 1) - u i).toNNReal = (u n - u m).toNNReal := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sum, Real.coe_toNNReal _ (sub_nonneg.2 (hu hmn))]
  rw [Finset.sum_congr rfl fun i _ => Real.coe_toNNReal _ (sub_nonneg.2 (hu (Nat.le_succ i)))]
  exact Finset.sum_Ico_sub u hmn

section UnionGrid

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℕ → Ω → ℝ}

/-- A scaled standard normal variable: `√c Y` has law `N(0, c)` for `c ≥ 0` (Giles 2015, §5.6,
Algorithm 3: "`∆W := √h Z`"). -/
lemma hasLaw_sqrt_mul {c : ℝ} (hc : 0 ≤ c) {Y : Ω → ℝ} (hY : HasLaw Y (gaussianReal 0 1) μ) :
    HasLaw (fun ω => Real.sqrt c * Y ω) (gaussianReal 0 c.toNNReal) μ := by
  convert gaussianReal_const_mul hY (Real.sqrt c) using 2
  · simp
  · ext
    simp [Real.sq_sqrt hc, hc]

/-- **The increments of the union-grid path over either grid are independent `N(0, ∆t)`**
(Giles 2015, §5.6, p. 44, lines 1926–1929: "The underlying Brownian path needs to be sampled at
a set of times which are the union of the simulation times used by the coarse and fine path. The
independent Brownian increments can be simulated for each time interval, and summed to give
`W(t)` at the required times").  Let `Z_0, Z_1, …` be independent standard normal variables on
any probability space (e.g. the coordinates `z ↦ z_i` of `stdNormalSeq`), let `u` be the sorted
union grid (`u` monotone on `ℕ`: a finite grid `u_0 < ⋯ < u_K = T` is extended by `u_k = T` for
`k > K`), and let the times of one of the two paths be `t_j = u_{τ(j)}`, `j = 0, …, n`, with `τ`
monotone.  Then the path's increments `W(t_{j+1}) − W(t_j)` (`unionGridBM`) are independent,
and the `j`-th has law `N(0, t_{j+1} − t_j)`.  The grids are deterministic here; the adaptive
grids of §5.6, which depend on the path, are not covered. -/
theorem unionGridBM_increments (hZ : iIndepFun Z μ)
    (hZ1 : ∀ i, HasLaw (Z i) (gaussianReal 0 1) μ) {u : ℕ → ℝ} (hu : Monotone u) {n : ℕ}
    {τ : Fin (n + 1) → ℕ} (hτ : Monotone τ) :
    iIndepFun (fun (j : Fin n) ω =>
        unionGridBM u (Z · ω) (τ j.succ) - unionGridBM u (Z · ω) (τ j.castSucc)) μ ∧
      ∀ j : Fin n, HasLaw
        (fun ω => unionGridBM u (Z · ω) (τ j.succ) - unionGridBM u (Z · ω) (τ j.castSucc))
        (gaussianReal 0 (u (τ j.succ) - u (τ j.castSucc)).toNNReal) μ := by
  have hind : iIndepFun (fun i ω => Real.sqrt (u (i + 1) - u i) * Z i ω) μ :=
    hZ.comp (fun i x => Real.sqrt (u (i + 1) - u i) * x) fun _ => by fun_prop
  have hX : ∀ i, HasLaw (fun ω => Real.sqrt (u (i + 1) - u i) * Z i ω)
      (gaussianReal 0 (u (i + 1) - u i).toNNReal) μ := fun i =>
    hasLaw_sqrt_mul (sub_nonneg.2 (hu (Nat.le_succ i))) (hZ1 i)
  have hle : ∀ j : Fin n, τ j.castSucc ≤ τ j.succ := fun j => hτ (Fin.castSucc_le_succ j)
  have hdisj :
      Pairwise (Function.onFun Disjoint fun j : Fin n => Ico (τ j.castSucc) (τ j.succ)) := by
    intro j l hjl
    rcases lt_or_gt_of_ne hjl with h | h
    · exact Finset.disjoint_left.2 fun i hi hi' => by
        have := hτ (Fin.succ_le_castSucc_iff.2 h)
        simp only [Finset.mem_Ico] at hi hi'
        omega
    · exact Finset.disjoint_left.2 fun i hi hi' => by
        have := hτ (Fin.succ_le_castSucc_iff.2 h)
        simp only [Finset.mem_Ico] at hi hi'
        omega
  obtain ⟨h1, h2⟩ := iIndepFun_blockSum hind hX _ hdisj
  have e : ∀ (j : Fin n) (ω : Ω),
      unionGridBM u (Z · ω) (τ j.succ) - unionGridBM u (Z · ω) (τ j.castSucc) =
        ∑ i ∈ Ico (τ j.castSucc) (τ j.succ), Real.sqrt (u (i + 1) - u i) * Z i ω := fun j ω =>
    unionGridBM_sub_eq_sum u (Z · ω) (hle j)
  simp_rw [e]
  refine ⟨h1, fun j => ?_⟩
  have h2j := h2 j
  rw [Finset.sum_const_zero, sum_toNNReal_Ico hu (hle j)] at h2j
  exact h2j

/-- **The joint law of the increments of the union-grid path over one grid** (Giles 2015, §5.6,
p. 44, lines 1926–1929): with `Z_0, Z_1, …` independent standard normal, `u` the sorted union
grid and `t_j = u_{τ(j)}` the times of one of the two paths, the vector of increments
`(W(t_{j+1}) − W(t_j))_j` has the product law `⊗_j N(0, t_{j+1} − t_j)`. -/
theorem unionGridBM_hasLaw (hZ : iIndepFun Z μ) (hZ1 : ∀ i, HasLaw (Z i) (gaussianReal 0 1) μ)
    {u : ℕ → ℝ} (hu : Monotone u) {n : ℕ} {τ : Fin (n + 1) → ℕ} (hτ : Monotone τ) :
    HasLaw (fun ω (j : Fin n) =>
        unionGridBM u (Z · ω) (τ j.succ) - unionGridBM u (Z · ω) (τ j.castSucc))
      (Measure.pi fun j : Fin n => gaussianReal 0 (u (τ j.succ) - u (τ j.castSucc)).toNNReal)
      μ :=
  (unionGridBM_increments hZ hZ1 hu hτ).1.hasLaw_pi (unionGridBM_increments hZ hZ1 hu hτ).2

/-- The increments `√(c_j) Z_j` of the single-level scheme on its own grid (Giles 2015, §5.1,
p. 29, lines 1279–1281: "Brownian increments `∆W_n`") have the law `⊗_j N(0, c_j)` when the
`Z_j` are independent standard normal. -/
lemma ownGrid_hasLaw (hZ : iIndepFun Z μ) (hZ1 : ∀ i, HasLaw (Z i) (gaussianReal 0 1) μ)
    {n : ℕ} {c : Fin n → ℝ} (hc : ∀ j, 0 ≤ c j) :
    HasLaw (fun ω (j : Fin n) => Real.sqrt (c j) * Z j ω)
      (Measure.pi fun j : Fin n => gaussianReal 0 (c j).toNNReal) μ := by
  have h1 := (hZ.precomp Fin.val_injective (g := fun j : Fin n => (j : ℕ))).comp
    (fun j (x : ℝ) => Real.sqrt (c j) * x) fun _ => by fun_prop
  exact h1.hasLaw_pi fun j => hasLaw_sqrt_mul (hc j) (hZ1 j)

/-- **Each path driven by the union grid has the law of the path simulated on its own grid**
(Giles 2015, §5.6, p. 44, lines 1926–1929, and Algorithm 3, p. 45).  With `Z_0, Z_1, …`
independent standard normal, `u` the sorted union grid and `t_j = u_{τ(j)}` the times of one of
the two paths, the increments `W(t_{j+1}) − W(t_j)` of the union-grid path have the same joint
law as the increments `√(t_{j+1} − t_j) Z_j` that the single-level scheme simulates on the grid
`(t_j)` alone.  Hence every function of the path's increments (the path of any scheme driven by
them, and its payoff) has the same law in both simulations. -/
theorem unionGridBM_map_eq (hZ : iIndepFun Z μ) (hZ1 : ∀ i, HasLaw (Z i) (gaussianReal 0 1) μ)
    {u : ℕ → ℝ} (hu : Monotone u) {n : ℕ} {τ : Fin (n + 1) → ℕ} (hτ : Monotone τ) :
    μ.map (fun ω (j : Fin n) =>
        unionGridBM u (Z · ω) (τ j.succ) - unionGridBM u (Z · ω) (τ j.castSucc)) =
      μ.map (fun ω (j : Fin n) => Real.sqrt (u (τ j.succ) - u (τ j.castSucc)) * Z j ω) := by
  rw [(unionGridBM_hasLaw hZ hZ1 hu hτ).map_eq,
    (ownGrid_hasLaw hZ hZ1 fun j => sub_nonneg.2 (hu (hτ (Fin.castSucc_le_succ j)))).map_eq]

/-- **Both the fine and the coarse path have their single-level law** (Giles 2015, §5.6, p. 44,
lines 1917–1930, Figure 5.9 and Algorithm 3: the timesteps of the two levels "are not naturally
nested. It may appear that this would cause difficulties in the MLMC implementation, but
Figure 5.9 tries to illustrate that it does not").  The `Z_i` are independent standard normal,
the union grid `u` is sorted, the fine path uses the times `u_{τf(j)}` and the coarse path the
times `u_{τc(j)}`.  Both paths are driven by the same union-grid path `W` (this is the
coupling), and each one's increments have the law of the increments simulated on its own grid
alone.  This is `unionGridBM_map_eq` applied to each of the two grids, recorded separately as
the paper's claim about both paths.  The statement gives each path's own law, not their joint
law; the grids are deterministic. -/
theorem unionGrid_brownian_map_eq (hZ : iIndepFun Z μ)
    (hZ1 : ∀ i, HasLaw (Z i) (gaussianReal 0 1) μ) {u : ℕ → ℝ} (hu : Monotone u) {nf nc : ℕ}
    {τf : Fin (nf + 1) → ℕ} {τc : Fin (nc + 1) → ℕ} (hτf : Monotone τf) (hτc : Monotone τc) :
    μ.map (fun ω (j : Fin nf) =>
        unionGridBM u (Z · ω) (τf j.succ) - unionGridBM u (Z · ω) (τf j.castSucc)) =
      μ.map (fun ω (j : Fin nf) => Real.sqrt (u (τf j.succ) - u (τf j.castSucc)) * Z j ω) ∧
    μ.map (fun ω (j : Fin nc) =>
        unionGridBM u (Z · ω) (τc j.succ) - unionGridBM u (Z · ω) (τc j.castSucc)) =
      μ.map (fun ω (j : Fin nc) => Real.sqrt (u (τc j.succ) - u (τc j.castSucc)) * Z j ω) :=
  ⟨unionGridBM_map_eq hZ hZ1 hu hτf, unionGridBM_map_eq hZ hZ1 hu hτc⟩

end UnionGrid

/-! ### §5.2: the Brownian-bridge midpoint -/

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The discrete Brownian-bridge midpoint law** (Giles 2015, §5.2, p. 39, lines 1693–1701:
"`Ŝ^c(t_{n+1}) = ½(Ŝ^c_n + Ŝ^c_{n+2}) + ½ b^c_n((W_{n+1} − W_n) − (W_{n+2} − W_{n+1}))` using the
Brownian increments `W_{n+1} − W_n` and `W_{n+2} − W_{n+1}` already generated for the fine path.
The standard Brownian path results can then be used").  Let the two fine increments `∆W₁, ∆W₂` of
a coarse step of length `h` be independent `N(0, h/2)`.  Then the coarse increment
`∆W₁ + ∆W₂` is `N(0, h)`, the bridge deviation `½(∆W₁ − ∆W₂)` is `N(0, h/4)`, the two are
independent (the rotation invariance of the standard Gaussian in `ℝ²`), and the midpoint value is
`W(t + h/2) = W(t) + ∆W₁ = ½(W(t) + W(t + h)) + ½(∆W₁ − ∆W₂)` with `W(t + h) = W(t) + ∆W₁ + ∆W₂`:
the midpoint is the average of the endpoints plus an independent `N(0, h/4)` deviation.  The
paper's volatility factor `b^c_n` only rescales the deviation (to `N(0, (b^c_n)² h/4)`) and is
omitted. -/
theorem bridge_midpoint_law {h : ℝ≥0} {dW₁ dW₂ : Ω → ℝ} (hind : IndepFun dW₁ dW₂ μ)
    (h₁ : HasLaw dW₁ (gaussianReal 0 (h / 2)) μ) (h₂ : HasLaw dW₂ (gaussianReal 0 (h / 2)) μ) :
    HasLaw (fun ω => dW₁ ω + dW₂ ω) (gaussianReal 0 h) μ ∧
      HasLaw (fun ω => (dW₁ ω - dW₂ ω) / 2) (gaussianReal 0 (h / 4)) μ ∧
      IndepFun (fun ω => dW₁ ω + dW₂ ω) (fun ω => (dW₁ ω - dW₂ ω) / 2) μ ∧
      ∀ ω (W₀ : ℝ), W₀ + dW₁ ω = (W₀ + (W₀ + dW₁ ω + dW₂ ω)) / 2 + (dW₁ ω - dW₂ ω) / 2 := by
  have := h₁.isProbabilityMeasure
  have hL1 : MemLp dW₁ 2 μ := h₁.hasGaussianLaw.memLp_two
  have hL2 : MemLp dW₂ 2 μ := h₂.hasGaussianLaw.memLp_two
  have hsum : HasLaw (fun ω => dW₁ ω + dW₂ ω) (gaussianReal 0 h) μ := by
    refine ⟨h₁.aemeasurable.add h₂.aemeasurable, ?_⟩
    change μ.map (dW₁ + dW₂) = _
    rw [gaussianReal_add_gaussianReal_of_indepFun hind h₁.map_eq h₂.map_eq, add_zero,
      add_halves]
  have hneg : HasLaw (-dW₂) (gaussianReal 0 (h / 2)) μ := by
    simpa using gaussianReal_neg h₂
  have hind' : IndepFun dW₁ (-dW₂) μ := hind.comp measurable_id measurable_neg
  have hdiff : HasLaw (fun ω => dW₁ ω - dW₂ ω) (gaussianReal 0 h) μ := by
    refine ⟨h₁.aemeasurable.sub h₂.aemeasurable, ?_⟩
    change μ.map (dW₁ + -dW₂) = _
    rw [gaussianReal_add_gaussianReal_of_indepFun hind' h₁.map_eq hneg.map_eq, add_zero,
      add_halves]
  refine ⟨hsum, ?_, ?_, fun ω W₀ => by ring⟩
  · convert gaussianReal_div_const hdiff 2 using 2
    · simp
    · ext
      norm_num
  · let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
      { toFun x := (x.1 + x.2, (x.1 - x.2) / 2)
        map_add' x y := by ext <;> simp <;> ring
        map_smul' c x := by ext <;> simp <;> ring }
    have hG : HasGaussianLaw (fun ω => (dW₁ ω + dW₂ ω, (dW₁ ω - dW₂ ω) / 2)) μ :=
      (IndepFun.hasGaussianLaw h₁.hasGaussianLaw h₂.hasGaussianLaw hind).map_fun L
    refine hG.indepFun_of_covariance_eq_zero ?_
    rw [covariance_fun_div_right]
    change cov[dW₁ + dW₂, dW₁ - dW₂; μ] / 2 = 0
    rw [covariance_add_left hL1 hL2 (hL1.sub hL2), covariance_sub_right hL1 hL1 hL2,
      covariance_sub_right hL2 hL1 hL2, covariance_self h₁.aemeasurable,
      covariance_self h₂.aemeasurable, h₁.variance_eq, h₂.variance_eq, covariance_comm dW₂ dW₁]
    ring

/-- **The Brownian-bridge midpoint for a Brownian motion** (Giles 2015, §5.2, p. 39,
lines 1693–1701: the coarse interpolant at the fine time is
"`½(Ŝ^c_n + Ŝ^c_{n+2}) + ½ b^c_n((W_{n+1} − W_n) − (W_{n+2} − W_{n+1}))` … The standard Brownian
path results can then be used").  For a pre-Brownian motion `B` and `s, h ≥ 0`, the deviation
`B(s + h/2) − ½(B(s) + B(s + h))` of the midpoint from the average of the endpoints has law
`N(0, h/4)` and is independent of the endpoint `B(s + h)` together with the whole past
`(B(r))_{r ≤ s}`: given the values at the ends of a coarse step, the value at its midpoint is
their average plus an independent `N(0, h/4)` variable. -/
theorem brownian_bridge_midpoint {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (s h : ℝ≥0) :
    HasLaw (fun ω => B (s + h / 2) ω - (B s ω + B (s + h) ω) / 2) (gaussianReal 0 (h / 4)) μ ∧
      IndepFun (fun ω => B (s + h / 2) ω - (B s ω + B (s + h) ω) / 2)
        (fun ω => (B (s + h) ω, fun r : Set.Iic s => B r ω)) μ := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hL : ∀ r, MemLp (B r) 2 μ := fun r =>
    (hB.isGaussianProcess.hasGaussianLaw_eval r).memLp_two
  constructor
  · have hmono : Monotone ![s, s + h / 2, s + h] := by
      refine Fin.monotone_iff_le_succ.2 fun i => ?_
      fin_cases i
      · simp
      · simp
    have hind := (hB.hasIndepIncrements 2 _ hmono).indepFun (show (0 : Fin 2) ≠ 1 by decide)
    have hd : ∀ a b : ℝ≥0, a ≤ b → nndist b.1 a.1 = b - a := fun a b hab => by
      change nndist (b : ℝ) (a : ℝ) = b - a
      apply NNReal.eq
      rw [coe_nndist, Real.dist_eq, NNReal.coe_sub hab, abs_of_nonneg (by
        have := NNReal.coe_le_coe.2 hab
        linarith)]
    have h1 : HasLaw (fun ω => B (s + h / 2) ω - B s ω) (gaussianReal 0 (h / 2)) μ := by
      have := hB.hasLaw_sub (s + h / 2) s
      rwa [hd _ _ le_self_add, add_tsub_cancel_left] at this
    have h2 : HasLaw (fun ω => B (s + h) ω - B (s + h / 2) ω) (gaussianReal 0 (h / 2)) μ := by
      have := hB.hasLaw_sub (s + h) (s + h / 2)
      rwa [hd _ _ (by gcongr; exact half_le_self (by positivity)), add_tsub_add_eq_tsub_left,
        tsub_eq_of_eq_add (add_halves h).symm] at this
    obtain ⟨-, h3, -, -⟩ := bridge_midpoint_law (by simpa using hind) h1 h2
    convert h3 using 2 with ω
    ring
  · classical
    let D : Unit → Ω → ℝ := fun _ ω => B (s + h / 2) ω - (B s ω + B (s + h) ω) / 2
    let Y : Unit ⊕ Set.Iic s → Ω → ℝ := Sum.elim (fun _ => B (s + h)) fun r => B r
    have hG : IsGaussianProcess (Sum.elim D Y) μ := by
      refine hB.isGaussianProcess.of_isGaussianProcess ?_
      rintro (_ | _ | r)
      · exact ⟨{s, s + h / 2, s + h},
          { toFun x := x ⟨s + h / 2, by simp⟩ - (x ⟨s, by simp⟩ + x ⟨s + h, by simp⟩) / 2
            map_add' x y := by simp; ring
            map_smul' c x := by simp; ring }, fun ω => rfl⟩
      · exact ⟨{s + h},
          { toFun x := x ⟨s + h, by simp⟩
            map_add' x y := rfl
            map_smul' c x := rfl }, fun ω => rfl⟩
      · exact ⟨{r.1},
          { toFun x := x ⟨r.1, by simp⟩
            map_add' x y := rfl
            map_smul' c x := rfl }, fun ω => rfl⟩
    have hM : MemLp (fun ω => (B s ω + B (s + h) ω) / 2) 2 μ := by
      simpa [div_eq_mul_inv] using ((hL s).add (hL (s + h))).mul_const 2⁻¹
    have hcov : ∀ d : ℝ≥0, d ≤ s ∨ d = s + h → cov[D (), B d; μ] = 0 := by
      intro d hd
      change cov[fun ω => B (s + h / 2) ω - (B s ω + B (s + h) ω) / 2, B d; μ] = 0
      rw [covariance_fun_sub_left (hL _) hM (hL _), covariance_fun_div_left]
      change cov[B (s + h / 2), B d; μ] - cov[B s + B (s + h), B d; μ] / 2 = 0
      rw [covariance_add_left (hL _) (hL _) (hL _), hB.covariance_eval, hB.covariance_eval,
        hB.covariance_eval]
      rcases hd with hd | rfl
      · rw [min_eq_right hd, min_eq_right (hd.trans le_self_add),
          min_eq_right (hd.trans le_self_add)]
        ring
      · rw [min_eq_left (by gcongr; exact half_le_self (by positivity)), min_eq_left le_self_add,
          min_self]
        push_cast
        ring
    have hind := IsGaussianProcess.indepFun_of_covariance_eq_zero hG
      (fun _ => ((hL _).sub hM).aemeasurable)
      (fun j => by rcases j with _ | r <;> exact (hL _).aemeasurable)
      (fun i j => by
        rcases j with _ | r
        · exact hcov _ (Or.inr rfl)
        · exact hcov _ (Or.inl r.2))
    have hψ : Measurable fun g : Unit ⊕ Set.Iic s → ℝ =>
        (g (Sum.inl ()), fun r : Set.Iic s => g (Sum.inr r)) := by fun_prop
    have hφ : Measurable fun f : Unit → ℝ => f () := measurable_pi_apply ()
    exact hind.comp hφ hψ

end Bridge

/-! ### §5.3: the interpolant of a weighted average of assets -/

/-- **The Brownian interpolant of a weighted average of assets** (Giles 2015, §5.3, p. 39,
lines 1718–1722: "if the financial option depends on the weighted average of a set of underlying
assets, then the Brownian interpolation for each individual asset leads naturally to a Brownian
interpolation for the average, and then the standard one-dimensional results can be used as
usual").  For assets `a ∈ s` with weights `w_a`, values `S₀_a, S₁_a` at the ends of the step,
frozen volatilities `b_a` and Brownian values `W₀_a, W₁_a, Wt_a`, the weighted average of the
interpolants `bridgeInterp` (`SDEExtras.lean`) is the interpolant of the averaged values
`∑ w_a S₀_a`, `∑ w_a S₁_a`, with unit volatility, driven by the averaged path
`V = ∑ w_a b_a W_a` at the same `λ`.  The statement is the linearity of the interpolant in
`(S, b W)`; that `V` is a scaled Brownian motion (for correlated Brownian motions `W_a`), to which
the one-dimensional results apply, is not formalised here. -/
theorem bridgeInterp_weighted_sum {α : Type*} (s : Finset α) (w S₀ S₁ b W₀ W₁ Wt : α → ℝ)
    (lam : ℝ) :
    ∑ a ∈ s, w a * bridgeInterp (S₀ a) (S₁ a) (b a) (W₀ a) (W₁ a) (Wt a) lam =
      bridgeInterp (∑ a ∈ s, w a * S₀ a) (∑ a ∈ s, w a * S₁ a) 1
        (∑ a ∈ s, w a * b a * W₀ a) (∑ a ∈ s, w a * b a * W₁ a) (∑ a ∈ s, w a * b a * Wt a)
        lam := by
  unfold bridgeInterp
  simp only [one_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ### §5.3: the antithetic path by time reversal within each coarse step -/

/-- The covariance algebra of a time reflection inside one interval `[a, b] ∋ s ≤ t`
(Giles 2015, §5.3): with `Cov(B(x), B(y)) = min(x, y)` the reflected values
`B(a) + B(b) − B(a + b − ·)` have covariance `s`. -/
lemma cov_reflect_same {a b s t : ℝ} (h1 : a ≤ s) (h2 : s ≤ t) (h3 : t ≤ b) :
    min a a + min a b - min a (a + b - t) + (min b a + min b b - min b (a + b - t)) -
      (min (a + b - s) a + min (a + b - s) b - min (a + b - s) (a + b - t)) = s := by
  rw [min_self, min_self, min_eq_left (by linarith : a ≤ b), min_eq_right (by linarith : a ≤ b),
    min_eq_left (by linarith : a ≤ a + b - t), min_eq_right (by linarith : a + b - t ≤ b),
    min_eq_right (by linarith : a ≤ a + b - s), min_eq_left (by linarith : a + b - s ≤ b),
    min_eq_right (by linarith : a + b - t ≤ a + b - s)]
  ring

/-- The covariance algebra of time reflections inside two consecutive disjoint intervals
`s ∈ [a, b]`, `t ∈ [c, d]`, `b ≤ c` (Giles 2015, §5.3): the reflected values have covariance
`s`. -/
lemma cov_reflect_disjoint {a b c d s t : ℝ} (h1 : a ≤ s) (h2 : s ≤ b) (h3 : b ≤ c)
    (h4 : c ≤ t) (h5 : t ≤ d) :
    min a c + min a d - min a (c + d - t) + (min b c + min b d - min b (c + d - t)) -
      (min (a + b - s) c + min (a + b - s) d - min (a + b - s) (c + d - t)) = s := by
  rw [min_eq_left (by linarith : a ≤ c), min_eq_left (by linarith : a ≤ d),
    min_eq_left (by linarith : a ≤ c + d - t), min_eq_left (by linarith : b ≤ c),
    min_eq_left (by linarith : b ≤ d), min_eq_left (by linarith : b ≤ c + d - t),
    min_eq_left (by linarith : a + b - s ≤ c), min_eq_left (by linarith : a + b - s ≤ d),
    min_eq_left (by linarith : a + b - s ≤ c + d - t)]
  ring

section Reversal

variable {Ω : Type*}

/-- **Time reflection inside equal-or-disjoint intervals preserves pre-Brownian motion** (the
engine of Giles 2015, §5.3, p. 42, lines 1805–1809: "a time-reversal of the Brownian path within
each coarse timestep").  Each time `t` lies in an interval `[a(t), b(t)]`, and for `s ≤ t` the
intervals of `s` and `t` are either equal or `b(s) ≤ a(t)`.  If `B` is pre-Brownian, so is
`t ↦ B(a(t)) + B(b(t)) − B(a(t) + b(t) − t)`: it is a centred Gaussian process with covariance
`min(s, t)`.  The intervals may not be nested: for `[0, 1] ∋ s = 0.8` and `[0, 2] ∋ t = 0.9`
the reflected values `B(0) + B(1) − B(0.2)` and `B(0) + B(2) − B(1.1)` are uncorrelated, not of
covariance `0.8`. -/
lemma isPreBrownianReal_reflect [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a b : ℝ≥0 → ℝ≥0) (ha : ∀ t, a t ≤ t) (hb : ∀ t, t ≤ b t)
    (hab : ∀ s t, s ≤ t → (a s = a t ∧ b s = b t) ∨ b s ≤ a t) :
    IsPreBrownianReal (fun t ω => B (a t) ω + B (b t) ω - B (a t + b t - t) ω) P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hL : ∀ r, MemLp (B r) 2 P := fun r =>
    (hB.isGaussianProcess.hasGaussianLaw_eval r).memLp_two
  have hG : IsGaussianProcess (fun t ω => B (a t) ω + B (b t) ω - B (a t + b t - t) ω) P := by
    classical
    exact hB.isGaussianProcess.of_isGaussianProcess fun t => ⟨{a t, b t, a t + b t - t},
      { toFun x := x ⟨a t, by simp⟩ + x ⟨b t, by simp⟩ - x ⟨a t + b t - t, by simp⟩
        map_add' x y := by simp; abel
        map_smul' c x := by simp; ring },
      by simp⟩
  refine hG.isPreBrownianReal_of_covariance (fun t => ?_) (fun s t hst => ?_)
  · have hi : ∀ r, Integrable (B r) P := hB.integrable_eval
    rw [integral_sub (f := fun ω => B (a t) ω + B (b t) ω) ((hi _).add (hi _)) (hi _),
      integral_add (hi _) (hi _), hB.integral_eval, hB.integral_eval, hB.integral_eval]
    simp
  · change cov[B (a s) + B (b s) - B (a s + b s - s), B (a t) + B (b t) - B (a t + b t - t); P] = s
    rw [covariance_sub_left ((hL _).add (hL _)) (hL _) (((hL _).add (hL _)).sub (hL _)),
      covariance_add_left (hL _) (hL _) (((hL _).add (hL _)).sub (hL _)),
      covariance_sub_right (hL _) ((hL _).add (hL _)) (hL _),
      covariance_sub_right (hL _) ((hL _).add (hL _)) (hL _),
      covariance_sub_right (hL _) ((hL _).add (hL _)) (hL _),
      covariance_add_right (hL _) (hL _) (hL _), covariance_add_right (hL _) (hL _) (hL _),
      covariance_add_right (hL _) (hL _) (hL _)]
    simp only [hB.covariance_eval, NNReal.coe_min]
    rw [NNReal.coe_sub ((hb s).trans le_add_self), NNReal.coe_sub ((hb t).trans le_add_self),
      NNReal.coe_add, NNReal.coe_add]
    have ha' : ∀ r, (a r : ℝ) ≤ r := fun r => NNReal.coe_le_coe.2 (ha r)
    have hb' : ∀ r : ℝ≥0, (r : ℝ) ≤ b r := fun r => NNReal.coe_le_coe.2 (hb r)
    rcases hab s t hst with ⟨h1, h2⟩ | h
    · rw [h1, h2]
      exact cov_reflect_same (h1 ▸ ha' s) (NNReal.coe_le_coe.2 hst) (hb' t)
    · exact cov_reflect_disjoint (ha' s) (hb' s) (NNReal.coe_le_coe.2 h) (ha' t) (hb' t)

/-- **The antithetic Brownian path** (Giles 2015, §5.3, p. 42, lines 1805–1809: "`ω^a_i` is an
antithetic counterpart defined by a time-reversal of the Brownian path within each coarse
timestep").  With coarse timestep `H`, on the coarse step `[kH, (k+1)H)` containing `t`
(`k = ⌊t/H⌋`), `B^a(t) = B(kH) + B((k+1)H) − B(kH + (k+1)H − t)`: the path of `B` inside the step
run backwards, re-attached to the same endpoints.  `B` is one scalar Brownian component; a
`d`-dimensional path is reversed componentwise (`iIndepFun_antitheticBM`).  For `H = 0` the
definition degenerates (Lean's `t / 0 = 0` gives the constant `B(0)`); the theorems about laws
assume `H ≠ 0`. -/
noncomputable def antitheticBM (H : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  B (⌊t / H⌋₊ * H) ω + B ((⌊t / H⌋₊ + 1) * H) ω -
    B (⌊t / H⌋₊ * H + (⌊t / H⌋₊ + 1) * H - t) ω

/-- **The antithetic path is again a Brownian motion** (Giles 2015, §5.3, p. 42, lines 1799–1809:
the antithetic estimator `Y_ℓ = N_ℓ⁻¹ ∑ (½(P_ℓ(ω_i) + P_ℓ(ω^a_i)) − P_{ℓ−1}(ω_i))`, where "`ω^a_i`
is an antithetic counterpart defined by a time-reversal of the Brownian path within each coarse
timestep").  If `B` is a pre-Brownian motion (Mathlib's `IsPreBrownianReal`: the
finite-dimensional laws of Brownian motion) and the coarse timestep is `H > 0`, then the
time-reversed path `antitheticBM H B` is again pre-Brownian; hence `P_ℓ(ω^a)` has the law of
`P_ℓ(ω)` for every payoff of finitely many path values, which is what makes the antithetic
estimator respect (2.4).  Path continuity is not part of the statement.  The statement is for
one scalar Brownian component; the paper's setting is a multi-dimensional SDE, whose
`d`-dimensional driving Brownian motion is reversed componentwise (`iIndepFun_antitheticBM`). -/
theorem isPreBrownianReal_antitheticBM [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {H : ℝ≥0} (hH : H ≠ 0) :
    IsPreBrownianReal (antitheticBM H B) P := by
  refine isPreBrownianReal_reflect hB (fun t => ⌊t / H⌋₊ * H) (fun t => (⌊t / H⌋₊ + 1) * H)
    (fun t => ?_) (fun t => ?_) (fun s t hst => ?_)
  · calc (⌊t / H⌋₊ : ℝ≥0) * H ≤ t / H * H := mul_le_mul_left (Nat.floor_le (by positivity)) H
      _ = t := div_mul_cancel₀ t hH
  · calc t = t / H * H := (div_mul_cancel₀ t hH).symm
      _ ≤ (⌊t / H⌋₊ + 1) * H := mul_le_mul_left (Nat.lt_floor_add_one _).le H
  · have hk : ⌊s / H⌋₊ ≤ ⌊t / H⌋₊ := Nat.floor_le_floor (by gcongr)
    rcases hk.eq_or_lt with hk | hk
    · exact Or.inl ⟨by rw [hk], by rw [hk]⟩
    · refine Or.inr (mul_le_mul_left ?_ H)
      exact_mod_cast hk

/-- **The antithetic path of a multi-dimensional Brownian motion** (Giles 2015, §5.3, pp. 39 and
42, lines 1728–1735 and 1799–1809: for "multi-dimensional SDEs which do not satisfy the
commutativity condition", Giles and Szpruch's antithetic treatment uses "`ω^a_i` … an antithetic
counterpart defined by a time-reversal of the Brownian path within each coarse timestep").  The
driving Brownian motion is `d`-dimensional with independent components `B_i` (`i ∈ ι`, any index
type), and the reversal acts on each component.  If the `B_i` are pre-Brownian and independent
as processes (path-valued random variables, with the product σ-algebra on paths), then for
`H > 0` the reversed components `antitheticBM H B_i` are again pre-Brownian and independent: the
reversed path is again a `d`-dimensional pre-Brownian motion.  Correlated Brownian components
are not treated. -/
theorem iIndepFun_antitheticBM [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) {H : ℝ≥0} (hH : H ≠ 0) :
    (∀ i, IsPreBrownianReal (antitheticBM H (B i)) P) ∧
      iIndepFun (fun i ω t => antitheticBM H (B i) t ω) P := by
  refine ⟨fun i => isPreBrownianReal_antitheticBM (hB i) hH, ?_⟩
  have hg : Measurable fun (f : ℝ≥0 → ℝ) (t : ℝ≥0) =>
      f (⌊t / H⌋₊ * H) + f ((⌊t / H⌋₊ + 1) * H) - f (⌊t / H⌋₊ * H + (⌊t / H⌋₊ + 1) * H - t) :=
    measurable_pi_lambda _ fun t => by fun_prop
  exact hind.comp (fun _ => _) fun _ => hg

/-- **The antithetic path agrees with the original path at the coarse times** (Giles 2015, §5.3,
p. 42, lines 1805–1809): `B^a(kH) = B(kH)` for every `k`, so the coarse path `P_{ℓ−1}(ω)`, which
only sees the Brownian values at the coarse times, is the same for `ω` and `ω^a`. -/
theorem antitheticBM_natCast_mul (H : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (k : ℕ) :
    antitheticBM H B (k * H) ω = B (k * H) ω := by
  rcases eq_or_ne H 0 with rfl | hH
  · simp [antitheticBM]
  unfold antitheticBM
  rw [mul_div_cancel_right₀ _ hH, Nat.floor_natCast, add_tsub_cancel_left, add_sub_cancel_right]

/-- The fine Brownian increments `∆W_i = W((i+1)h) − W(ih)` of a path `W` with fine timestep `h`
(Giles 2015, §5.3, p. 42, lines 1807–1809: "the Brownian increments for the antithetic fine
path"). -/
def fineIncrements (h : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) (i : ℕ) : ℝ :=
  W ((i + 1 : ℕ) * h) ω - W (i * h) ω

/-- `⌊m h / (2h)⌋ = ⌊m / 2⌋` for `h > 0`: the fine time `m h` lies in the coarse step `⌊m / 2⌋`
(Giles 2015, §5.3, coarse timestep `2h`). -/
lemma floor_natCast_mul_div_two_mul {h : ℝ≥0} (hh : h ≠ 0) (m : ℕ) :
    ⌊(m : ℝ≥0) * h / (2 * h)⌋₊ = m / 2 := by
  have hpos : 0 < h := pos_iff_ne_zero.2 hh
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    calc ((m / 2 : ℕ) : ℝ≥0) * (2 * h) = ((2 * (m / 2) : ℕ) : ℝ≥0) * h := by push_cast; ring
      _ ≤ m * h := by gcongr; omega
  · rw [div_lt_iff₀ (by positivity)]
    calc (m : ℝ≥0) * h < ((2 * (m / 2) + 2 : ℕ) : ℝ≥0) * h := by gcongr; omega
      _ = ((m / 2 : ℕ) + 1) * (2 * h) := by push_cast; ring

/-- The antithetic path at the even fine times `2k h` (the coarse times, coarse timestep `2h`) is
the original path (Giles 2015, §5.3). -/
lemma antitheticBM_two_mul (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (h : ℝ≥0) (k : ℕ) :
    antitheticBM (2 * h) B ((2 * k : ℕ) * h) ω = B ((2 * k : ℕ) * h) ω := by
  have e : ((2 * k : ℕ) : ℝ≥0) * h = k * (2 * h) := by push_cast; ring
  rw [e]
  exact antitheticBM_natCast_mul (2 * h) B ω k

/-- The antithetic path at the odd fine time `(2k+1) h`, the midpoint of the coarse step
`[2kh, (2k+2)h]`: `B^a((2k+1)h) = B(2kh) + B((2k+2)h) − B((2k+1)h)` (Giles 2015, §5.3). -/
lemma antitheticBM_two_mul_add_one (B : ℝ≥0 → Ω → ℝ) (ω : Ω) {h : ℝ≥0} (hh : h ≠ 0) (k : ℕ) :
    antitheticBM (2 * h) B ((2 * k + 1 : ℕ) * h) ω =
      B ((2 * k : ℕ) * h) ω + B ((2 * (k + 1) : ℕ) * h) ω - B ((2 * k + 1 : ℕ) * h) ω := by
  unfold antitheticBM
  rw [floor_natCast_mul_div_two_mul hh, show (2 * k + 1) / 2 = k by omega]
  have e1 : (k : ℝ≥0) * (2 * h) = (2 * k : ℕ) * h := by push_cast; ring
  have e2 : ((k : ℝ≥0) + 1) * (2 * h) = (2 * (k + 1) : ℕ) * h := by push_cast; ring
  have e3 : ((2 * k : ℕ) : ℝ≥0) * h + ((2 * (k + 1) : ℕ) : ℝ≥0) * h - (2 * k + 1 : ℕ) * h =
      (2 * k + 1 : ℕ) * h := tsub_eq_of_eq_add (by push_cast; ring)
  rw [e1, e2, e3]

/-- **Time reversal swaps the fine increments within each coarse step** (Giles 2015, §5.3, p. 42,
lines 1805–1809: "an antithetic counterpart defined by a time-reversal of the Brownian path within
each coarse timestep. This results in the Brownian increments for the antithetic fine path being
swapped relative to the original path").  With fine timestep `h` and coarse timestep `2h`, the
fine increments of the antithetic path `antitheticBM (2h) B` are, for every `ω`, the fine
increments of `B` with the two increments of each coarse step exchanged:
`∆W^a_{2k} = ∆W_{2k+1}` and `∆W^a_{2k+1} = ∆W_{2k}` (`swapIncrements` of `SDEExtras.lean`, whose
law invariance is `measurePreserving_swapIncrements`).  The statement is pathwise for one scalar
component; for the `d`-dimensional Brownian path of a multi-dimensional SDE it applies to each
component. -/
theorem fineIncrements_antitheticBM (h : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    fineIncrements h (antitheticBM (2 * h) B) ω = swapIncrements (fineIncrements h B ω) := by
  funext i
  rcases eq_or_ne h 0 with rfl | hh
  · simp [fineIncrements, swapIncrements]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
  · have hs : pairSwap (2 * k) = 2 * k + 1 := by unfold pairSwap; split_ifs <;> omega
    simp only [fineIncrements, swapIncrements, hs]
    rw [antitheticBM_two_mul_add_one B ω hh k, antitheticBM_two_mul B ω h k,
      show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    ring
  · have hs : pairSwap (2 * k + 1) = 2 * k := by unfold pairSwap; split_ifs <;> omega
    simp only [fineIncrements, swapIncrements, hs]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, antitheticBM_two_mul_add_one B ω hh k,
      antitheticBM_two_mul B ω h (k + 1)]
    ring

/-- The time reversal within the first coarse step `[0, H]` only (Giles 2015, §5.3, p. 42,
lines 1805–1809): `B^a(t) = B(H) − B(H − t)` for `t ≤ H` and `B^a(t) = B(t)` for `t > H`. -/
noncomputable def reverseFirstStep (H : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t ≤ H then B H ω - B (H - t) ω else B t ω

/-- **Reversing a Brownian motion within the first coarse step gives a Brownian motion** (Giles
2015, §5.3, p. 42, lines 1805–1809: "a time-reversal of the Brownian path within each coarse
timestep").  If `B` is pre-Brownian, so is `B^a(t) = B(H) − B(H − t)` (`t ≤ H`),
`B^a(t) = B(t)` (`t > H`), for every `H ≥ 0`.  (At `t = H` this gives `B(H) − B(0)`, which is
`B(H)` almost surely.)  The statement is for one scalar Brownian component; the multi-dimensional
version (componentwise reversal of independent components) is stated for the reversal within
every coarse step, `iIndepFun_antitheticBM`. -/
theorem isPreBrownianReal_reverseFirstStep [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (H : ℝ≥0) :
    IsPreBrownianReal (reverseFirstStep H B) P := by
  have h := isPreBrownianReal_reflect hB (fun t => if t ≤ H then 0 else t)
    (fun t => if t ≤ H then H else t) (fun t => by split_ifs <;> simp)
    (fun t => by split_ifs with ht <;> simp [ht]) (fun s t hst => by
      by_cases ht : t ≤ H
      · simp [ht, hst.trans ht]
      · by_cases hs : s ≤ H
        · simp [hs, ht, (not_le.1 ht).le]
        · simp [hs, ht, hst])
  refine h.congr fun t => ?_
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
  by_cases ht : t ≤ H
  · simp [reverseFirstStep, ht, hω]
  · simp [reverseFirstStep, ht]

/-- **The reversal within the first coarse step swaps its two fine increments** (Giles 2015,
§5.3, p. 42, lines 1807–1809: "the Brownian increments for the antithetic fine path being swapped
relative to the original path").  With coarse timestep `2h`, for every `ω`:
`B^a(h) − B^a(0) = B(2h) − B(h)` and `B^a(2h) − B^a(h) = B(h) − B(0)`.  The statement is pathwise
for one scalar component; for a `d`-dimensional path it applies to each component. -/
theorem reverseFirstStep_fineIncrements (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (h : ℝ≥0) :
    reverseFirstStep (2 * h) B h ω - reverseFirstStep (2 * h) B 0 ω = B (2 * h) ω - B h ω ∧
      reverseFirstStep (2 * h) B (2 * h) ω - reverseFirstStep (2 * h) B h ω =
        B h ω - B 0 ω := by
  have h1 : h ≤ 2 * h := by rw [two_mul]; exact le_add_self
  have h2 : 2 * h - h = h := by rw [two_mul, add_tsub_cancel_right]
  simp [reverseFirstStep, h1, h2]

end Reversal

end MLMC
