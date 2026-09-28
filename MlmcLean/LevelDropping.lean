import MlmcLean.ControlVariate

/-!
# Non-geometric MLMC: when to drop a level (Giles 2015, §2.6)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.6
(pp. 18–20 of the author's version).

"MLMC does not require the use of a geometric sequence of grids."  Giles first asks which subset
`ℓ₀ < ℓ₁ < ⋯ < ℓ_M = L` of a large collection of potential levels to use:

* by (1.1), the least cost of MLMC on the levels of `s` is
  `C(ℓ₀, …, ℓ_M) = ε⁻² (√(V_{ℓ₀} C_{ℓ₀}) + ∑_{m=1}^{M} √(V_{ℓ_{m−1},ℓ_m} C_{ℓ_{m−1},ℓ_m}))²`
  (`subsetCost`, `subsetCost_eq`, `subset_optimal_cost`), and the corrections telescope to
  `P_{ℓ_M}` (`sum_subsetCorr`);
* an exhaustive search over the `2^L` subsets of `{0, …, L}` containing `L` finds an optimal one
  (`card_levelSubsets`, `exists_optimal_subset`).

Then, given levels `0, …, L`, Giles asks whether it is better to keep a level `ℓ` or to drop it and
jump from `ℓ − 1` to `ℓ + 1`.  With
`V_ℓ = V[P_ℓ − P_{ℓ−1}]`, `C_ℓ` its cost, `Ṽ_{ℓ+1} = V[P_{ℓ+1} − P_{ℓ−1}]` and `C̃_{ℓ+1}` its cost:

* keeping level `ℓ`, the product of the combined variance and the combined cost of the two
  estimators that involve level `ℓ` is at best `V_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`
  (`levelKeep_product`), while dropping it gives `Ṽ_{ℓ+1} C̃_{ℓ+1}`;
* the test (2.5), `Ṽ_{ℓ+1} C̃_{ℓ+1} < V_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`, holds
  exactly when dropping level `ℓ` lowers the optimal cost (1.1) of the whole hierarchy for a given
  variance, equivalently the optimal variance for a given cost (`levelDrop_test`);
* `Ṽ_{ℓ+1} = V_{ℓ+1} + 2ρ √(V_ℓ V_{ℓ+1}) + V_ℓ` with `ρ` the correlation of the two increments
  (`levelDrop_variance`); for `ρ = 1` and `C_ℓ ≤ C_{ℓ+1} = C̃_{ℓ+1}` the test fails, so level `ℓ` is
  kept (`levelDrop_perfect_correlation`); for `ρ = 0` it reads
  `1 + V_ℓ/V_{ℓ+1} < (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²` (`levelDrop_uncorrelated`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### Choosing a subset of the levels -/

section subsets

/-- The variance or the cost of the correction at level `ℓ` of MLMC on an ordered subset `s` of the
levels (Giles 2015, §2.6, p. 18).  If `ℓ` is the smallest level of `s`, the correction is `P_ℓ`
itself and the value is `f ℓ` (`V_ℓ = V[P_ℓ]`, or the cost `C_ℓ` of one sample of `P_ℓ`);
otherwise the correction is `P_ℓ − P_{ℓ'}`, where `ℓ'` is the next smaller level of `s`, and the
value is `f₂ ℓ' ℓ` (`V_{ℓ',ℓ} = V[P_ℓ − P_{ℓ'}]`, or the cost `C_{ℓ',ℓ}` of one sample of it). -/
noncomputable def subsetCorr (f : ℕ → ℝ) (f₂ : ℕ → ℕ → ℝ) (s : Finset ℕ) (ℓ : ℕ) : ℝ :=
  if h : (s.filter (· < ℓ)).Nonempty then f₂ ((s.filter (· < ℓ)).max' h) ℓ else f ℓ

/-- **The cost of MLMC on a subset of the levels** (Giles 2015, §2.6, p. 18): for the levels
`ℓ₀ < ℓ₁ < ⋯ < ℓ_M` of `s`,
`C(ℓ₀, …, ℓ_M) = ε⁻² (√(V_{ℓ₀} C_{ℓ₀}) + ∑_{m=1}^{M} √(V_{ℓ_{m−1},ℓ_m} C_{ℓ_{m−1},ℓ_m}))²`
(`subsetCost_eq`), where `V_ℓ = V[P_ℓ]`, `V_{ℓ₁,ℓ₂} = V[P_{ℓ₂} − P_{ℓ₁}]` for `ℓ₁ < ℓ₂`, and `C_ℓ`,
`C_{ℓ₁,ℓ₂}` are the costs of one sample.  (The paper writes the pair as `V_{ℓ_m,ℓ_{m−1}}`; by its
definition of `V_{ℓ₁,ℓ₂}` this is `V[P_{ℓ_m} − P_{ℓ_{m−1}}]`.) -/
noncomputable def subsetCost (V C : ℕ → ℝ) (V₂ C₂ : ℕ → ℕ → ℝ) (ε : ℝ) (s : Finset ℕ) : ℝ :=
  (ε ^ 2)⁻¹ * (∑ ℓ ∈ s, Real.sqrt (subsetCorr V V₂ s ℓ * subsetCorr C C₂ s ℓ)) ^ 2

lemma subsetCorr_pos {f : ℕ → ℝ} {f₂ : ℕ → ℕ → ℝ} (hf : ∀ ℓ, 0 < f ℓ) (hf₂ : ∀ a b, 0 < f₂ a b)
    (s : Finset ℕ) (ℓ : ℕ) : 0 < subsetCorr f f₂ s ℓ := by
  unfold subsetCorr
  split_ifs
  · exact hf₂ _ _
  · exact hf _

lemma subsetCorr_congr {f : ℕ → ℝ} {f₂ : ℕ → ℕ → ℝ} {s t : Finset ℕ} {ℓ : ℕ}
    (h : s.filter (· < ℓ) = t.filter (· < ℓ)) : subsetCorr f f₂ s ℓ = subsetCorr f f₂ t ℓ := by
  unfold subsetCorr
  rw [h]

/-- At a new top level `ℓ` the correction is taken from the previous top level. -/
lemma subsetCorr_insert_top {f : ℕ → ℝ} {f₂ : ℕ → ℕ → ℝ} {s : Finset ℕ} {ℓ : ℕ}
    (h : ∀ x ∈ s, x < ℓ) :
    subsetCorr f f₂ (insert ℓ s) ℓ = if hs : s.Nonempty then f₂ (s.max' hs) ℓ else f ℓ := by
  have hf : (insert ℓ s).filter (· < ℓ) = s := by
    rw [Finset.filter_insert, if_neg (lt_irrefl ℓ), Finset.filter_true_of_mem h]
  unfold subsetCorr
  rw [hf]

/-- The smallest level `ℓ₀` of the subset `{ℓ₀ < ⋯ < ℓ_M}` carries `f ℓ₀`. -/
lemma subsetCorr_image_zero {M : ℕ} {ℓ : Fin (M + 1) → ℕ} (hℓ : StrictMono ℓ) (f : ℕ → ℝ)
    (f₂ : ℕ → ℕ → ℝ) : subsetCorr f f₂ (Finset.univ.image ℓ) (ℓ 0) = f (ℓ 0) := by
  have h : ¬((Finset.univ.image ℓ).filter (· < ℓ 0)).Nonempty := by
    rintro ⟨x, hx⟩
    rw [Finset.mem_filter, Finset.mem_image] at hx
    obtain ⟨⟨k, -, rfl⟩, hk⟩ := hx
    exact Fin.not_lt_zero k (hℓ.lt_iff_lt.1 hk)
  unfold subsetCorr
  rw [dif_neg h]

/-- The level `ℓ_{m+1}` of the subset `{ℓ₀ < ⋯ < ℓ_M}` carries `f₂ ℓ_m ℓ_{m+1}`. -/
lemma subsetCorr_image_succ {M : ℕ} {ℓ : Fin (M + 1) → ℕ} (hℓ : StrictMono ℓ) (f : ℕ → ℝ)
    (f₂ : ℕ → ℕ → ℝ) (m : Fin M) :
    subsetCorr f f₂ (Finset.univ.image ℓ) (ℓ m.succ) = f₂ (ℓ m.castSucc) (ℓ m.succ) := by
  have hmem : ℓ m.castSucc ∈ (Finset.univ.image ℓ).filter (· < ℓ m.succ) :=
    Finset.mem_filter.2 ⟨Finset.mem_image_of_mem ℓ (Finset.mem_univ _), hℓ Fin.castSucc_lt_succ⟩
  have hne : ((Finset.univ.image ℓ).filter (· < ℓ m.succ)).Nonempty := ⟨_, hmem⟩
  have hmax : ((Finset.univ.image ℓ).filter (· < ℓ m.succ)).max' hne = ℓ m.castSucc := by
    refine le_antisymm (Finset.max'_le _ _ _ fun y hy => ?_) (Finset.le_max' _ _ hmem)
    rw [Finset.mem_filter, Finset.mem_image] at hy
    obtain ⟨⟨k, -, rfl⟩, hk⟩ := hy
    exact hℓ.monotone (Fin.le_castSucc_iff.2 (hℓ.lt_iff_lt.1 hk))
  unfold subsetCorr
  rw [dif_pos hne, hmax]

/-- **Giles 2015, §2.6, p. 18: the cost of MLMC on the levels `ℓ₀ < ℓ₁ < ⋯ < ℓ_M`** is
`ε⁻² (√(V_{ℓ₀} C_{ℓ₀}) + ∑_{m=1}^{M} √(V_{ℓ_{m−1},ℓ_m} C_{ℓ_{m−1},ℓ_m}))²`. -/
theorem subsetCost_eq {M : ℕ} {ℓ : Fin (M + 1) → ℕ} (hℓ : StrictMono ℓ) (V C : ℕ → ℝ)
    (V₂ C₂ : ℕ → ℕ → ℝ) (ε : ℝ) :
    subsetCost V C V₂ C₂ ε (Finset.univ.image ℓ) =
      (ε ^ 2)⁻¹ * (Real.sqrt (V (ℓ 0) * C (ℓ 0)) + ∑ m : Fin M,
        Real.sqrt (V₂ (ℓ m.castSucc) (ℓ m.succ) * C₂ (ℓ m.castSucc) (ℓ m.succ))) ^ 2 := by
  unfold subsetCost
  rw [Finset.sum_image fun a _ b _ h => hℓ.injective h, Fin.sum_univ_succ,
    subsetCorr_image_zero hℓ, subsetCorr_image_zero hℓ]
  simp only [subsetCorr_image_succ hℓ]

/-- **The subset estimator estimates `E[P_L]`** (Giles 2015, §2.6, p. 18, "with fixed `ℓ_M = L`"):
the corrections `P_{ℓ₀}` and `P_{ℓ_m} − P_{ℓ_{m−1}}` of an ordered subset of the levels telescope to
`P` at the largest level of the subset.  With `p ℓ = E[P_ℓ]` this says that MLMC on the subset has
expectation `E[P_{ℓ_M}]`, the same bias as MLMC on all the levels up to `ℓ_M`. -/
theorem sum_subsetCorr (p : ℕ → ℝ) {s : Finset ℕ} (hs : s.Nonempty) :
    ∑ ℓ ∈ s, subsetCorr p (fun i j => p j - p i) s ℓ = p (s.max' hs) := by
  revert hs
  induction s using Finset.induction_on_max with
  | empty => exact fun hs => absurd hs Finset.not_nonempty_empty
  | insert a t hlt ih =>
    intro hs
    have ha : a ∉ t := fun h => lt_irrefl a (hlt a h)
    have hmax : (insert a t).max' hs = a :=
      le_antisymm
        (Finset.max'_le _ _ _ fun y hy =>
          (Finset.mem_insert.1 hy).elim le_of_eq fun hy => (hlt y hy).le)
        (Finset.le_max' _ _ (Finset.mem_insert_self a t))
    have hrest : ∀ ℓ ∈ t, subsetCorr p (fun i j => p j - p i) (insert a t) ℓ =
        subsetCorr p (fun i j => p j - p i) t ℓ := fun ℓ hℓ =>
      subsetCorr_congr (by rw [Finset.filter_insert, if_neg (not_lt.2 (hlt ℓ hℓ).le)])
    rw [hmax, Finset.sum_insert ha, Finset.sum_congr rfl hrest, subsetCorr_insert_top hlt]
    rcases t.eq_empty_or_nonempty with rfl | ht
    · rw [dif_neg Finset.not_nonempty_empty, Finset.sum_empty, add_zero]
    · rw [dif_pos ht, ih ht, sub_add_cancel]

/-- **Giles 2015, §2.6, p. 18: the optimal allocation on a subset of the levels.**  "For a
particular ordered subset of levels … following the analysis in Section 1.3 which led to (1.1), we
obtain the cost `C(ℓ₀, …, ℓ_M)`."  For a nonempty set `s` of levels with positive variances and
costs, the least cost `∑_{ℓ∈s} N_ℓ C_ℓ` of MLMC on the levels of `s` (the correction on `ℓ ∈ s`
having variance and cost `subsetCorr`) among the real sample numbers `N_ℓ > 0` that give variance
`∑_{ℓ∈s} V_ℓ/N_ℓ ≤ ε²` is `subsetCost`. -/
theorem subset_optimal_cost (V C : ℕ → ℝ) (V₂ C₂ : ℕ → ℕ → ℝ) {ε : ℝ} (hε : 0 < ε)
    {s : Finset ℕ} (hs : s.Nonempty) (hV : ∀ ℓ, 0 < V ℓ) (hC : ∀ ℓ, 0 < C ℓ)
    (hV₂ : ∀ a b, 0 < V₂ a b) (hC₂ : ∀ a b, 0 < C₂ a b) :
    IsLeast {c | ∃ N : ℕ → ℝ, (∀ ℓ ∈ s, 0 < N ℓ) ∧
        ∑ ℓ ∈ s, subsetCorr V V₂ s ℓ / N ℓ ≤ ε ^ 2 ∧ c = ∑ ℓ ∈ s, N ℓ * subsetCorr C C₂ s ℓ}
      (subsetCost V C V₂ C₂ ε s) :=
  (optimal_cost_isLeast s (subsetCorr V V₂ s) (subsetCorr C C₂ s) (pow_pos hε 2) hs
    (fun ℓ _ => subsetCorr_pos hV hV₂ s ℓ) (fun ℓ _ => subsetCorr_pos hC hC₂ s ℓ)).1

/-- The candidate subsets of `{0, …, L}` that keep the finest level `L` are `2^L` in number (Giles
2015, §2.6, p. 18: "If the maximum number of levels is not too large, it is possible to perform an
exhaustive search"). -/
theorem card_levelSubsets (L : ℕ) : ((range (L + 1)).powerset.filter (L ∈ ·)).card = 2 ^ L := by
  have hL : L ∉ range L := Finset.notMem_range_self
  have heq : (range (L + 1)).powerset.filter (L ∈ ·) = (range L).powerset.image (insert L) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hsub, hLt⟩
      refine ⟨t.erase L, fun x hx => ?_, Finset.insert_erase hLt⟩
      have hxL := Finset.ne_of_mem_erase hx
      have hx' := hsub (Finset.mem_of_mem_erase hx)
      rw [Finset.mem_range] at hx' ⊢
      omega
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun x hx => ?_, Finset.mem_insert_self L u⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Finset.self_mem_range_succ _
      · exact Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hu hx)))
  rw [heq, Finset.card_image_of_injOn, Finset.card_powerset, Finset.card_range]
  intro t ht u hu htu
  have htL : L ∉ t := fun h => hL (Finset.mem_powerset.1 (Finset.mem_coe.1 ht) h)
  have huL : L ∉ u := fun h => hL (Finset.mem_powerset.1 (Finset.mem_coe.1 hu) h)
  calc t = (insert L t).erase L := (Finset.erase_insert htL).symm
    _ = (insert L u).erase L := by rw [htu]
    _ = u := Finset.erase_insert huL

/-- **The exhaustive search** (Giles 2015, §2.6, p. 18: "it is possible to perform an exhaustive
search to find the optimal subset `{ℓ₁, ℓ₂, …, ℓ_M}` which minimises this cost"): among the subsets
of the levels `{0, …, L}` that keep the finest level `L`, one has the least cost `subsetCost`. -/
theorem exists_optimal_subset (V C : ℕ → ℝ) (V₂ C₂ : ℕ → ℕ → ℝ) (ε : ℝ) (L : ℕ) :
    ∃ s ∈ (range (L + 1)).powerset.filter (L ∈ ·),
      ∀ t ∈ (range (L + 1)).powerset.filter (L ∈ ·),
        subsetCost V C V₂ C₂ ε s ≤ subsetCost V C V₂ C₂ ε t :=
  Finset.exists_min_image _ _ ⟨{L}, Finset.mem_filter.2
    ⟨Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 (Finset.self_mem_range_succ L)),
      Finset.mem_singleton_self L⟩⟩

end subsets

-- `x (1 + √(y/x))² = (√y + √x)²` for `x > 0`
lemma mul_one_add_sqrt_div_sq {x y : ℝ} (hx : 0 < x) :
    x * (1 + Real.sqrt (y / x)) ^ 2 = (Real.sqrt y + Real.sqrt x) ^ 2 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 : (1 + Real.sqrt y / Real.sqrt x) * Real.sqrt x = Real.sqrt y + Real.sqrt x := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ hs.ne', add_comm]
  rw [Real.sqrt_div' y hx.le, ← h1, mul_pow, Real.sq_sqrt hx.le, mul_comm]

/-- **Keeping level `ℓ`** (Giles 2015, §2.6, pp. 18–19): "If we keep level `ℓ` then the contribution
to the overall multilevel estimator due to samples involving level `ℓ` is
`N_ℓ⁻¹ ∑ (P_ℓ − P_{ℓ−1}) + N_{ℓ+1}⁻¹ ∑ (P_{ℓ+1} − P_ℓ)` … and so the product of the combined
variance and combined cost is `V_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`" for the optimal
ratio of `N_ℓ` to `N_{ℓ+1}`.  For positive `V_ℓ, V_{ℓ+1}, C_ℓ, C_{ℓ+1}` this value is the least
product `(V_ℓ/N_ℓ + V_{ℓ+1}/N_{ℓ+1})(N_ℓ C_ℓ + N_{ℓ+1} C_{ℓ+1})` over all real
`N_ℓ, N_{ℓ+1} > 0`. -/
theorem levelKeep_product {Vℓ Vℓ₁ Cℓ Cℓ₁ : ℝ} (hV : 0 < Vℓ) (hV₁ : 0 < Vℓ₁) (hC : 0 < Cℓ)
    (hC₁ : 0 < Cℓ₁) :
    IsLeast {x | ∃ n n₁ : ℝ, 0 < n ∧ 0 < n₁ ∧ x = (Vℓ / n + Vℓ₁ / n₁) * (n * Cℓ + n₁ * Cℓ₁)}
      (Vℓ₁ * Cℓ₁ * (1 + Real.sqrt (Vℓ * Cℓ / (Vℓ₁ * Cℓ₁))) ^ 2) := by
  rw [mul_one_add_sqrt_div_sq (mul_pos hV₁ hC₁)]
  have two : ∀ a b : ℝ, 0 < a → 0 < b → ∀ i, 0 < (![a, b] : Fin 2 → ℝ) i := fun a b ha hb =>
    (Fin.forall_fin_two (p := fun j => 0 < (![a, b] : Fin 2 → ℝ) j)).2 ⟨ha, hb⟩
  refine ⟨⟨Real.sqrt (Vℓ / Cℓ), Real.sqrt (Vℓ₁ / Cℓ₁), Real.sqrt_pos.2 (div_pos hV hC),
    Real.sqrt_pos.2 (div_pos hV₁ hC₁), ?_⟩, ?_⟩
  · -- the optimal allocation `N ∝ √(V/C)`: variance and cost both equal `∑ √(V C)`
    have hr₀ : 0 < Real.sqrt (Vℓ / Cℓ) := Real.sqrt_pos.2 (div_pos hV hC)
    have hr₁ : 0 < Real.sqrt (Vℓ₁ / Cℓ₁) := Real.sqrt_pos.2 (div_pos hV₁ hC₁)
    have e0 : Vℓ / Real.sqrt (Vℓ / Cℓ) = Real.sqrt (Vℓ * Cℓ) := by
      rw [div_eq_iff hr₀.ne']
      linear_combination -(sqrt_div_mul_sqrt_mul hV.le hC)
    have e1 : Vℓ₁ / Real.sqrt (Vℓ₁ / Cℓ₁) = Real.sqrt (Vℓ₁ * Cℓ₁) := by
      rw [div_eq_iff hr₁.ne']
      linear_combination -(sqrt_div_mul_sqrt_mul hV₁.le hC₁)
    rw [e0, e1, sqrt_div_mul hV.le hC, sqrt_div_mul hV₁.le hC₁]
    ring
  · -- every allocation: Cauchy–Schwarz, `(∑ √(V C))² ≤ (∑ V/N)(∑ N C)`
    rintro x ⟨n, n₁, hn, hn₁, rfl⟩
    have hτ : 0 < Vℓ / n + Vℓ₁ / n₁ := add_pos (div_pos hV hn) (div_pos hV₁ hn₁)
    have h := cost_lower_bound (Finset.univ : Finset (Fin 2)) ![Vℓ, Vℓ₁] ![Cℓ, Cℓ₁] ![n, n₁] hτ
      (fun i _ => (two Vℓ Vℓ₁ hV hV₁ i).le) (fun i _ => (two Cℓ Cℓ₁ hC hC₁ i).le)
      (fun i _ => two n n₁ hn hn₁ i) (by rw [Fin.sum_univ_two]; exact le_rfl)
    rw [Fin.sum_univ_two, Fin.sum_univ_two, inv_mul_le_iff₀ hτ] at h
    exact h

/-- **The level-dropping test (2.5)** (Giles 2015, §2.6, p. 19): "The question now is whether
`Ṽ_{ℓ+1} C̃_{ℓ+1} < V_{ℓ+1} C_{ℓ+1} (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`  (2.5).  If this test is
true, then it is best to drop level `ℓ`, because for a fixed computational cost this will deliver
the lower variance, or for a fixed variance it can be achieved at a lower computational cost."
Let the levels other than `ℓ` and `ℓ + 1` be indexed by a finite set `s`, with per-sample variances
`V_i` and costs `C_i`.  By (1.1) the least cost for a variance target `τ > 0` is `τ⁻¹ (∑ √(V C))²`
over the levels used, and the least variance for a cost budget `τ` has the same form
(`optimal_cost_isLeast`, `optimal_variance_isLeast`).  Replacing the corrections on levels `ℓ` and
`ℓ + 1` by the single correction `P_{ℓ+1} − P_{ℓ−1}` (variance `Ṽ`, cost `C̃`) makes this value
strictly smaller if and only if (2.5) holds. -/
theorem levelDrop_test {ι : Type*} (s : Finset ι) (V C : ι → ℝ) {Vℓ Vℓ₁ Cℓ Cℓ₁ Vd Cd τ : ℝ}
    (hV₁ : 0 < Vℓ₁) (hC₁ : 0 < Cℓ₁) (hτ : 0 < τ) :
    τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i) + Real.sqrt (Vd * Cd)) ^ 2 <
        τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i) + Real.sqrt (Vℓ * Cℓ) +
          Real.sqrt (Vℓ₁ * Cℓ₁)) ^ 2 ↔
      Vd * Cd < Vℓ₁ * Cℓ₁ * (1 + Real.sqrt (Vℓ * Cℓ / (Vℓ₁ * Cℓ₁))) ^ 2 := by
  have hS0 : 0 ≤ ∑ i ∈ s, Real.sqrt (V i * C i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have ha := Real.sqrt_nonneg (Vℓ * Cℓ)
  have hb : 0 < Real.sqrt (Vℓ₁ * Cℓ₁) := Real.sqrt_pos.2 (mul_pos hV₁ hC₁)
  have hd := Real.sqrt_nonneg (Vd * Cd)
  rw [mul_one_add_sqrt_div_sq (mul_pos hV₁ hC₁), mul_lt_mul_iff_of_pos_left (inv_pos.2 hτ),
    pow_lt_pow_iff_left₀ (add_nonneg hS0 hd) (add_nonneg (add_nonneg hS0 ha) hb.le) two_ne_zero,
    add_assoc, add_lt_add_iff_left, Real.sqrt_lt' (add_pos_of_nonneg_of_pos ha hb)]

section prob

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Giles 2015, §2.6, p. 20: "Using the standard result for the variance of a sum of two random
variables, we have `Ṽ_{ℓ+1} = V_{ℓ+1} + 2ρ √(V_ℓ V_{ℓ+1}) + V_ℓ`, where `ρ` is the correlation
between `P_{ℓ+1} − P_ℓ` and `P_ℓ − P_{ℓ−1}`."  Here `X = P_{ℓ+1} − P_ℓ` and `Y = P_ℓ − P_{ℓ−1}`
are square-integrable with positive variances, so `X + Y = P_{ℓ+1} − P_{ℓ−1}`. -/
theorem levelDrop_variance {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hVX : 0 < variance X μ) (hVY : 0 < variance Y μ) :
    variance (fun ω => X ω + Y ω) μ = variance X μ +
      2 * correlation X Y μ * Real.sqrt (variance Y μ * variance X μ) + variance Y μ := by
  rw [variance_fun_add hX hY, correlation, mul_comm (variance Y μ) (variance X μ), mul_assoc 2,
    div_mul_cancel₀ _ (Real.sqrt_pos.2 (mul_pos hVX hVY)).ne']

/-- **Perfectly correlated increments: keep the level** (Giles 2015, §2.6, p. 20): "If `ρ = 1`, and
so we have perfect correlation between the increments at different levels, then
`Ṽ_{ℓ+1} = V_{ℓ+1} (1 + √(V_ℓ/V_{ℓ+1}))²`.  Since `C_ℓ < C_{ℓ+1}`, it follows that the test (2.5)
is never satisfied, and so it is best to retain level `ℓ`."  With `X = P_{ℓ+1} − P_ℓ`,
`Y = P_ℓ − P_{ℓ−1}`, correlation `1`, `0 < C_ℓ ≤ C_{ℓ+1}` and the paper's approximation
`C̃_{ℓ+1} = C_{ℓ+1}`, the test (2.5) fails. -/
theorem levelDrop_perfect_correlation {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hVX : 0 < variance X μ) (hVY : 0 < variance Y μ) (hρ : correlation X Y μ = 1)
    {Cℓ Cℓ₁ : ℝ} (hC : 0 < Cℓ) (hCC : Cℓ ≤ Cℓ₁) :
    variance (fun ω => X ω + Y ω) μ =
        variance X μ * (1 + Real.sqrt (variance Y μ / variance X μ)) ^ 2 ∧
      ¬ variance (fun ω => X ω + Y ω) μ * Cℓ₁ <
        variance X μ * Cℓ₁ * (1 + Real.sqrt (variance Y μ * Cℓ / (variance X μ * Cℓ₁))) ^ 2 := by
  have hC₁ : 0 < Cℓ₁ := hC.trans_le hCC
  have hsum : variance (fun ω => X ω + Y ω) μ =
      variance X μ * (1 + Real.sqrt (variance Y μ / variance X μ)) ^ 2 := by
    rw [levelDrop_variance hX hY hVX hVY, hρ, mul_one, mul_one_add_sqrt_div_sq hVX, add_sq,
      Real.sq_sqrt hVY.le, Real.sq_sqrt hVX.le, Real.sqrt_mul hVY.le]
    ring
  refine ⟨hsum, fun h => ?_⟩
  -- `√(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})) ≤ √(V_ℓ/V_{ℓ+1})` because `C_ℓ ≤ C_{ℓ+1}`
  have hq : Real.sqrt (variance Y μ * Cℓ / (variance X μ * Cℓ₁)) ≤
      Real.sqrt (variance Y μ / variance X μ) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (mul_pos hVX hC₁) hVX]
    nlinarith [mul_le_mul_of_nonneg_left hCC (mul_nonneg hVY.le hVX.le)]
  have hq0 := Real.sqrt_nonneg (variance Y μ * Cℓ / (variance X μ * Cℓ₁))
  have hsq : (1 + Real.sqrt (variance Y μ * Cℓ / (variance X μ * Cℓ₁))) ^ 2 ≤
      (1 + Real.sqrt (variance Y μ / variance X μ)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hle := mul_le_mul_of_nonneg_left hsq (mul_pos hVX hC₁).le
  rw [hsum] at h
  linarith

/-- **Uncorrelated increments** (Giles 2015, §2.6, p. 20): "if `ρ = 0`, and so the increments at
different levels are independent, then `Ṽ_{ℓ+1} = V_{ℓ+1} + V_ℓ` and so we drop level `ℓ` if
`1 + V_ℓ/V_{ℓ+1} < (1 + √(V_ℓ C_ℓ/(V_{ℓ+1} C_{ℓ+1})))²`."  With `X = P_{ℓ+1} − P_ℓ`,
`Y = P_ℓ − P_{ℓ−1}`, correlation `0` and `C̃_{ℓ+1} = C_{ℓ+1}`, the test (2.5) is equivalent to this
inequality. -/
theorem levelDrop_uncorrelated {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hVX : 0 < variance X μ) (hVY : 0 < variance Y μ) (hρ : correlation X Y μ = 0)
    {Cℓ Cℓ₁ : ℝ} (hC₁ : 0 < Cℓ₁) :
    variance (fun ω => X ω + Y ω) μ = variance X μ + variance Y μ ∧
      (variance (fun ω => X ω + Y ω) μ * Cℓ₁ <
          variance X μ * Cℓ₁ * (1 + Real.sqrt (variance Y μ * Cℓ / (variance X μ * Cℓ₁))) ^ 2 ↔
        1 + variance Y μ / variance X μ <
          (1 + Real.sqrt (variance Y μ * Cℓ / (variance X μ * Cℓ₁))) ^ 2) := by
  have hsum : variance (fun ω => X ω + Y ω) μ = variance X μ + variance Y μ := by
    rw [levelDrop_variance hX hY hVX hVY, hρ]
    ring
  refine ⟨hsum, ?_⟩
  have hdiv : variance Y μ / variance X μ * variance X μ = variance Y μ :=
    div_mul_cancel₀ _ hVX.ne'
  have e : (variance X μ + variance Y μ) * Cℓ₁ =
      variance X μ * Cℓ₁ * (1 + variance Y μ / variance X μ) := by
    linear_combination (-Cℓ₁) * hdiv
  rw [hsum, e, mul_lt_mul_iff_of_pos_left (mul_pos hVX hC₁)]

end prob

end MLMC
