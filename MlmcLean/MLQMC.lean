import MlmcLean.Algorithm

/-!
# The MLQMC algorithm (Giles 2015, §3.5, Algorithm 2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §3.5 (p. 27 of
the author's version).

```
Algorithm 2 MLQMC algorithm
  start with L = 2, and an initial set size N_ℓ = 1 on levels ℓ = 0, 1, 2
  while not converged do
    evaluate 32 set averages on any level with new/changed values of N_ℓ
    compute corresponding new/changed estimates for V_ℓ
    test whether total variance condition (3.2) is satisfied
    if total variance still too big then
      determine ℓ* defined by (3.3) and double N_ℓ*
    else
      test for weak convergence
      if not converged then
        set L := L + 1, and initialise N_L = 1
      end if
    end if
  end while
```

Here `V_ℓ` is the variance of the average of the 32 randomised set averages on level `ℓ`, the
variance target is `∑_{ℓ ≤ L} V_ℓ ≤ ½ε²` (3.2), and (3.3) doubles `N_ℓ` on the level
`ℓ* = argmax_ℓ V_ℓ/(N_ℓ C_ℓ)`.

As for Algorithm 1 (`MlmcLean.Algorithm`), the algorithm is analysed with exact values.  After
`k` doublings `N_ℓ = 2^k`, and `v ℓ k` is the variance on level `ℓ` after `k` doublings.  How fast
`v ℓ k` decays is a question of QMC theory; the loop only needs `v ℓ k > 0` and `v ℓ k → 0` as
`k → ∞` on each level.  In one dimension, with randomly shifted rank-1 lattices, `MlmcLean.QMC1D`
proves `v ℓ k ≤ V(f_ℓ)²/N²` and the MLQMC complexity; QMC error theory in `d` dimensions is not
formalised.

* `mlqmcLevel` is a level `ℓ* ≤ L` of (3.3); `mlqmcStep` doubles `N_{ℓ*}`; `mlqmcIter` iterates.
* **The inner loop terminates** (`mlqmc_inner_terminates`): for every `θ > 0` some iterate has
  `∑_{ℓ ≤ L} v ℓ k_ℓ ≤ θ`.  A level with so many points that its ratio `V_ℓ/(N_ℓ C_ℓ)` is below
  the ratio of every level still short of its share of the target is never doubled again, so the
  levels short of their share are doubled until none is left.
* **The outer loop** (`mlqmcState`) adds levels until the weak-convergence test of Algorithm 1
  passes, so it stops at `alg1Level m α ε` (`alg1_terminates`), with the variance target (3.2) met
  (`mlqmc_algorithm`); then the MSE is at most `ε²` (`mlqmc_mse`).
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace MLMC

/-! ### The doubling rule (3.3) -/

section inner

variable (v : ℕ → ℕ → ℝ) (C : ℕ → ℝ) (L : ℕ)

/-- The ratio `V_ℓ/(N_ℓ C_ℓ)` of (3.3) on level `ℓ` after `k` doublings (`N_ℓ = 2^k`). -/
noncomputable def mlqmcRatio (ℓ k : ℕ) : ℝ :=
  v ℓ k / ((2 : ℝ) ^ k * C ℓ)

/-- **The level `ℓ*` of (3.3)** (Giles 2015, §3.5, p. 27: "the greatest reduction in total
variance relative to the additional computational effort is achieved by doubling `N_ℓ` on the
level `ℓ* = argmax_ℓ V_ℓ/(N_ℓ C_ℓ)`"): a level `ℓ ≤ L` with the largest ratio `mlqmcRatio`, where
`k ℓ` is the number of doublings on level `ℓ`. -/
noncomputable def mlqmcLevel (k : ℕ → ℕ) : ℕ :=
  Classical.choose ((range (L + 1)).exists_max_image (fun ℓ => mlqmcRatio v C ℓ (k ℓ))
    ⟨0, mem_range.2 (Nat.succ_pos L)⟩)

lemma mlqmcLevel_mem (k : ℕ → ℕ) : mlqmcLevel v C L k ∈ range (L + 1) :=
  (Classical.choose_spec ((range (L + 1)).exists_max_image (fun ℓ => mlqmcRatio v C ℓ (k ℓ))
    ⟨0, mem_range.2 (Nat.succ_pos L)⟩)).1

lemma le_mlqmcLevel (k : ℕ → ℕ) {ℓ : ℕ} (hℓ : ℓ ∈ range (L + 1)) :
    mlqmcRatio v C ℓ (k ℓ) ≤ mlqmcRatio v C (mlqmcLevel v C L k) (k (mlqmcLevel v C L k)) :=
  (Classical.choose_spec ((range (L + 1)).exists_max_image (fun ℓ => mlqmcRatio v C ℓ (k ℓ))
    ⟨0, mem_range.2 (Nat.succ_pos L)⟩)).2 ℓ hℓ

/-- One pass of the inner loop of Algorithm 2 (Giles 2015, §3.5): "determine `ℓ*` defined by
(3.3) and double `N_ℓ*`", i.e. add one to the number of doublings on the level `ℓ*`. -/
noncomputable def mlqmcStep (k : ℕ → ℕ) : ℕ → ℕ :=
  Function.update k (mlqmcLevel v C L k) (k (mlqmcLevel v C L k) + 1)

/-- The numbers of doublings after `n` passes of the inner loop at finest level `L`, from `k`. -/
noncomputable def mlqmcIter (k : ℕ → ℕ) (n : ℕ) : ℕ → ℕ :=
  (mlqmcStep v C L)^[n] k

lemma mlqmcIter_succ (k : ℕ → ℕ) (n : ℕ) :
    mlqmcIter v C L k (n + 1) = mlqmcStep v C L (mlqmcIter v C L k n) :=
  Function.iterate_succ_apply' _ _ _

lemma le_mlqmcStep (k : ℕ → ℕ) (ℓ : ℕ) : k ℓ ≤ mlqmcStep v C L k ℓ := by
  unfold mlqmcStep
  rcases eq_or_ne ℓ (mlqmcLevel v C L k) with h | h
  · rw [h, Function.update_self]
    exact Nat.le_succ _
  · exact (Function.update_of_ne h _ _).ge

/-- Each pass doubles exactly one set size. -/
lemma sum_mlqmcStep (k : ℕ → ℕ) :
    ∑ ℓ ∈ range (L + 1), mlqmcStep v C L k ℓ = ∑ ℓ ∈ range (L + 1), k ℓ + 1 := by
  unfold mlqmcStep
  rw [Finset.sum_update_of_mem (mlqmcLevel_mem v C L k),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (mlqmcLevel_mem v C L k) k]
  ring

lemma sum_mlqmcIter (k : ℕ → ℕ) (n : ℕ) :
    ∑ ℓ ∈ range (L + 1), mlqmcIter v C L k n ℓ = ∑ ℓ ∈ range (L + 1), k ℓ + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [mlqmcIter_succ, sum_mlqmcStep, ih, add_assoc]

variable {v C}

/-- **The inner loop of Algorithm 2 terminates** (Giles 2015, §3.5, Algorithm 2: "if total
variance still too big then determine `ℓ*` defined by (3.3) and double `N_ℓ*`").  Suppose the
variance `v ℓ k` of the level-`ℓ` average after `k` doublings is positive and tends to `0` as
`k → ∞`, and the costs `C_ℓ` are positive.  Then from any numbers of doublings `k₀` the greedy
doubling reaches `∑_{ℓ ≤ L} v ℓ k_ℓ ≤ θ`, for every `θ > 0`. -/
theorem mlqmc_inner_terminates (hv : ∀ ℓ k, 0 < v ℓ k) (hC : ∀ ℓ, 0 < C ℓ)
    (hlim : ∀ ℓ, Tendsto (v ℓ) atTop (𝓝 0)) (L : ℕ) (k₀ : ℕ → ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ n, ∑ ℓ ∈ range (L + 1), v ℓ (mlqmcIter v C L k₀ n ℓ) ≤ θ := by
  -- beyond `K` doublings every level meets its share `θ/(L + 1)` of the target
  have hθ' : 0 < θ / ((L : ℝ) + 1) := div_pos hθ (Nat.cast_add_one_pos L)
  obtain ⟨K, hK⟩ : ∃ K, ∀ k ≥ K, ∀ ℓ ∈ range (L + 1), v ℓ k ≤ θ / ((L : ℝ) + 1) := by
    have h : ∀ᶠ k in atTop, ∀ ℓ ∈ range (L + 1), v ℓ k ≤ θ / ((L : ℝ) + 1) :=
      (Filter.eventually_all_finset (range (L + 1))).2 fun ℓ _ =>
        (hlim ℓ).eventually (ge_mem_nhds hθ')
    exact Filter.eventually_atTop.1 h
  -- the ratios of the levels with fewer than `K` doublings are at least `η > 0`
  obtain ⟨η, hη, hηle⟩ : ∃ η > 0, ∀ ℓ ∈ range (L + 1), ∀ k < K, η ≤ mlqmcRatio v C ℓ k := by
    rcases (range (L + 1) ×ˢ range K).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun ℓ hℓ k hk => absurd
        (Finset.mk_mem_product hℓ (Finset.mem_range.2 hk)) ?_⟩
      rw [he]
      exact Finset.notMem_empty _
    · obtain ⟨p, -, hmin⟩ :=
        (range (L + 1) ×ˢ range K).exists_min_image (fun p => mlqmcRatio v C p.1 p.2) hne
      exact ⟨mlqmcRatio v C p.1 p.2, div_pos (hv _ _) (mul_pos (pow_pos two_pos _) (hC _)),
        fun ℓ hℓ k hk => hmin (ℓ, k) (Finset.mk_mem_product hℓ (Finset.mem_range.2 hk))⟩
  -- beyond `K'` doublings the ratio of every level is below `η`
  obtain ⟨K', hK'⟩ : ∃ K', ∀ k ≥ K', ∀ ℓ ∈ range (L + 1), mlqmcRatio v C ℓ k < η := by
    have hr : ∀ ℓ, Tendsto (fun k => mlqmcRatio v C ℓ k) atTop (𝓝 0) := fun ℓ => by
      have h1 := (hlim ℓ).div_const (C ℓ)
      rw [zero_div] at h1
      refine squeeze_zero (fun k => (div_pos (hv ℓ k) (mul_pos (pow_pos two_pos k) (hC ℓ))).le)
        (fun k => ?_) h1
      exact div_le_div_of_nonneg_left (hv ℓ k).le (hC ℓ)
        (le_mul_of_one_le_left (hC ℓ).le (one_le_pow₀ one_le_two))
    have h : ∀ᶠ k in atTop, ∀ ℓ ∈ range (L + 1), mlqmcRatio v C ℓ k < η :=
      (Filter.eventually_all_finset (range (L + 1))).2 fun ℓ _ =>
        (hr ℓ).eventually (gt_mem_nhds hη)
    exact Filter.eventually_atTop.1 h
  -- while some level has fewer than `K` doublings, every level has at most `B`
  obtain ⟨B, hB⟩ : ∃ B, B = K' + ∑ ℓ ∈ range (L + 1), k₀ ℓ := ⟨_, rfl⟩
  have hinv : ∀ n, (∃ ℓ ∈ range (L + 1), mlqmcIter v C L k₀ n ℓ < K) →
      ∀ ℓ ∈ range (L + 1), mlqmcIter v C L k₀ n ℓ ≤ B := by
    intro n
    induction n with
    | zero =>
      intro _ ℓ hℓ
      have h := Finset.single_le_sum (fun i _ => Nat.zero_le (k₀ i)) hℓ
      exact h.trans (by rw [hB]; exact Nat.le_add_left _ _)
    | succ n ih =>
      rintro ⟨ℓ₁, hℓ₁, hlt⟩
      have hmono : mlqmcIter v C L k₀ n ℓ₁ ≤ mlqmcIter v C L k₀ (n + 1) ℓ₁ := by
        rw [mlqmcIter_succ]
        exact le_mlqmcStep _ _ _ _ _
      have hB' := ih ⟨ℓ₁, hℓ₁, lt_of_le_of_lt hmono hlt⟩
      have hlt₁ : mlqmcIter v C L k₀ n ℓ₁ < K := lt_of_le_of_lt hmono hlt
      -- the level doubled still has fewer than `K'` doublings
      have hstar : mlqmcIter v C L k₀ n (mlqmcLevel v C L (mlqmcIter v C L k₀ n)) < K' := by
        by_contra hge
        have h1 := hK' _ (not_lt.1 hge) _ (mlqmcLevel_mem v C L (mlqmcIter v C L k₀ n))
        have h2 := hηle ℓ₁ hℓ₁ _ hlt₁
        have h3 := le_mlqmcLevel v C L (mlqmcIter v C L k₀ n) hℓ₁
        linarith
      intro ℓ hℓ
      rw [mlqmcIter_succ]
      unfold mlqmcStep
      rcases eq_or_ne ℓ (mlqmcLevel v C L (mlqmcIter v C L k₀ n)) with h | h
      · rw [h, Function.update_self]
        omega
      · rw [Function.update_of_ne h]
        exact hB' ℓ hℓ
  -- after `(L + 1) B + 1` passes no level has fewer than `K` doublings
  refine ⟨(L + 1) * B + 1, ?_⟩
  have hall : ∀ ℓ ∈ range (L + 1), K ≤ mlqmcIter v C L k₀ ((L + 1) * B + 1) ℓ := by
    by_contra hcon
    push Not at hcon
    have hle := hinv _ hcon
    have hsum := sum_mlqmcIter v C L k₀ ((L + 1) * B + 1)
    have hbound : ∑ ℓ ∈ range (L + 1), mlqmcIter v C L k₀ ((L + 1) * B + 1) ℓ ≤ (L + 1) * B :=
      calc ∑ ℓ ∈ range (L + 1), mlqmcIter v C L k₀ ((L + 1) * B + 1) ℓ
          ≤ ∑ _ℓ ∈ range (L + 1), B := Finset.sum_le_sum hle
        _ = (L + 1) * B := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  have hL1 : (L : ℝ) + 1 ≠ 0 := (Nat.cast_add_one_pos L).ne'
  calc ∑ ℓ ∈ range (L + 1), v ℓ (mlqmcIter v C L k₀ ((L + 1) * B + 1) ℓ)
      ≤ ∑ _ℓ ∈ range (L + 1), θ / ((L : ℝ) + 1) :=
        Finset.sum_le_sum fun ℓ hℓ => hK _ (hall ℓ hℓ) ℓ hℓ
    _ = θ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add_one]
        exact mul_div_cancel₀ θ hL1

end inner

/-! ### The whole algorithm -/

open Classical in
/-- **The inner loop of Algorithm 2** at finest level `L` (Giles 2015, §3.5): from the numbers of
doublings `k`, double `N_{ℓ*}` until the total variance `∑_{ℓ ≤ L} v ℓ k_ℓ` is at most `θ` (in
Algorithm 2, `θ = ε²/2`, (3.2)); `k` itself if that never happens (it does, under the hypotheses of
`mlqmc_inner_terminates`). -/
noncomputable def mlqmcInner (v : ℕ → ℕ → ℝ) (C : ℕ → ℝ) (L : ℕ) (θ : ℝ) (k : ℕ → ℕ) :
    ℕ → ℕ :=
  if h : ∃ n, ∑ ℓ ∈ range (L + 1), v ℓ (mlqmcIter v C L k n ℓ) ≤ θ then
    mlqmcIter v C L k (Nat.find h) else k

/-- **The numbers of doublings when Algorithm 2 leaves its inner loop with finest level `L ≥ 2`**
(Giles 2015, §3.5): "start with `L = 2`, and an initial set size `N_ℓ = 1` on levels
`ℓ = 0, 1, 2`", run the inner loop, and after "set `L := L + 1`, and initialise `N_L = 1`" run it
again.  (No level above the current `L` has been doubled, so `N_L = 1` holds when `L` is added;
the values for `L < 2` are the initial state.) -/
noncomputable def mlqmcState (v : ℕ → ℕ → ℝ) (C : ℕ → ℝ) (θ : ℝ) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | 1 => fun _ => 0
  | 2 => mlqmcInner v C 2 θ fun _ => 0
  | L + 3 => mlqmcInner v C (L + 3) θ (mlqmcState v C θ (L + 2))

section outer

variable {v : ℕ → ℕ → ℝ} {C : ℕ → ℝ}

lemma mlqmcInner_variance (hv : ∀ ℓ k, 0 < v ℓ k) (hC : ∀ ℓ, 0 < C ℓ)
    (hlim : ∀ ℓ, Tendsto (v ℓ) atTop (𝓝 0)) (L : ℕ) (k : ℕ → ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∑ ℓ ∈ range (L + 1), v ℓ (mlqmcInner v C L θ k ℓ) ≤ θ := by
  have h := mlqmc_inner_terminates hv hC hlim L k hθ
  unfold mlqmcInner
  rw [dif_pos h]
  exact Nat.find_spec h

/-- When Algorithm 2 leaves its inner loop with finest level `L ≥ 2`, the variance target
`∑_{ℓ ≤ L} V_ℓ ≤ θ` holds (Giles 2015, §3.5, (3.2) with `θ = ε²/2`). -/
lemma mlqmcState_variance (hv : ∀ ℓ k, 0 < v ℓ k) (hC : ∀ ℓ, 0 < C ℓ)
    (hlim : ∀ ℓ, Tendsto (v ℓ) atTop (𝓝 0)) {θ : ℝ} (hθ : 0 < θ) :
    ∀ L, 2 ≤ L → ∑ ℓ ∈ range (L + 1), v ℓ (mlqmcState v C θ L ℓ) ≤ θ
  | 0, h => absurd h (by norm_num)
  | 1, h => absurd h (by norm_num)
  | 2, _ => mlqmcInner_variance hv hC hlim 2 _ hθ
  | L + 3, _ => mlqmcInner_variance hv hC hlim (L + 3) _ hθ

/-- **Algorithm 2 terminates, and meets the variance target (3.2)** (Giles 2015, §3.5, with
exact values).  Let the exact corrections `m_ℓ = E[P_ℓ − P_{ℓ−1}]` tend to `0`, `α, ε > 0`, and let
the level variances `v ℓ k` (after `k` doublings) be positive and tend to `0`, with positive costs.
The weak-convergence test is that of Algorithm 1, so the outer loop stops at the level
`L = alg1Level m α ε ≥ 2`, where the test `alg1Rem m α L ≤ ε/√2` passes; every inner loop stops;
and at exit `∑_{ℓ ≤ L} V_ℓ ≤ ε²/2`. -/
theorem mlqmc_algorithm {m : ℕ → ℝ} (hm : Tendsto m atTop (𝓝 0)) {α ε : ℝ} (hα : 0 < α)
    (hε : 0 < ε) (hv : ∀ ℓ k, 0 < v ℓ k) (hC : ∀ ℓ, 0 < C ℓ)
    (hlim : ∀ ℓ, Tendsto (v ℓ) atTop (𝓝 0)) :
    2 ≤ alg1Level m α ε ∧ alg1Rem m α (alg1Level m α ε) ≤ ε / Real.sqrt 2 ∧
      ∑ ℓ ∈ range (alg1Level m α ε + 1),
        v ℓ (mlqmcState v C (ε ^ 2 / 2) (alg1Level m α ε) ℓ) ≤ ε ^ 2 / 2 := by
  obtain ⟨h2, hrem⟩ := alg1Level_spec (alg1_terminates hm hα hε)
  exact ⟨h2, hrem, mlqmcState_variance hv hC hlim (by positivity) _ h2⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The MSE at exit of Algorithm 2** (Giles 2015, §3.5: (3.2) "ensures" the variance part of the
MSE bound, and the weak-convergence test is that of Algorithm 1).  Let `P_ℓ` be integrable with
`E[P_ℓ] → E[P]`, so that the exact corrections `m_ℓ = E[P_ℓ − P_{ℓ−1}]` tend to `0` and Algorithm 2
stops, at `L = alg1Level m α ε` (`mlqmc_algorithm`).  If the corrections beyond `L` decay at least
geometrically from one of the anchors `L, L − 1, L − 2`, and the MLQMC estimator `Y` has
`E[Y] = E[P_L]` and variance `V[Y] ≤ ∑_{ℓ ≤ L} V_ℓ` at exit, then `E[(Y − E[P])²] ≤ ε²`. -/
theorem mlqmc_mse {Y P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} {α ε : ℝ} {k : ℕ} (hα : 0 < α) (hε : 0 < ε)
    (hv : ∀ ℓ k, 0 < v ℓ k) (hC : ∀ ℓ, 0 < C ℓ) (hlim : ∀ ℓ, Tendsto (v ℓ) atTop (𝓝 0))
    (hk : k ≤ 2) (hY : MemLp Y 2 μ) (hPl : ∀ ℓ, Integrable (Pl ℓ) μ)
    (hPlim : Tendsto (fun ℓ => μ[Pl ℓ]) atTop (𝓝 (μ[P])))
    (hdecay : ∀ ℓ : ℕ, alg1Level (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) α ε < ℓ →
      |∫ ω, levelDiff Pl ℓ ω ∂μ| ≤
        |∫ ω, levelDiff Pl (alg1Level (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) α ε - k) ω ∂μ| *
          (2 : ℝ) ^ (-(α * ((ℓ : ℝ) -
            (alg1Level (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) α ε - k : ℕ)))))
    (hmean : μ[Y] = μ[Pl (alg1Level (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) α ε)])
    (hvar : variance Y μ ≤ ∑ ℓ ∈ range (alg1Level (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) α ε + 1),
      v ℓ (mlqmcState v C (ε ^ 2 / 2) (alg1Level (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) α ε) ℓ)) :
    μ[fun ω => (Y ω - μ[P]) ^ 2] ≤ ε ^ 2 := by
  -- the exact corrections tend to `0`, since `E[P_ℓ]` converges
  have hm : Tendsto (fun ℓ => ∫ ω, levelDiff Pl ℓ ω ∂μ) atTop (𝓝 0) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    have h := (hPlim.comp (tendsto_add_atTop_nat 1)).sub hPlim
    rw [sub_self] at h
    refine h.congr fun ℓ => ?_
    rw [Function.comp_apply, levelDiff_succ, integral_sub (hPl _) (hPl _)]
  obtain ⟨h2, hrem, hV⟩ := mlqmc_algorithm hm hα hε hv hC hlim
  exact alg1_mse hα hk (hk.trans h2) hY hPl hPlim hdecay hmean (hvar.trans hV) hrem

end outer

end MLMC
