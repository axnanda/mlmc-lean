import MlmcLean.ContractingLevels

/-!
# Giles' Theorem 1 with a polylogarithmic factor in the cost (Giles 2015, §2.1 and §10.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1,
Theorem 1 (pp. 6–7 of the author's version), whose condition "iv) `C_ℓ ≤ c₃ 2^{γℓ}`" bounds the
expected cost of a level-`ℓ` sample; §1.3 (p. 4), the Lagrange-multiplier allocation
`N_ℓ = μ √(V_ℓ/C_ℓ)`; §10.1 "Markov chains and limiting distributions" (p. 61): "Because the decay
is exponential in `N_ℓ − N_{ℓ−1}`, it is appropriate to choose `N_ℓ` to increase linearly with
level.  A very similar approach can also be used for contracting SDEs which converge to a limiting
distribution.  For these, the level `ℓ` path will perform a simulation for the time interval
`[−T_ℓ, 0]`, using timestep `h_ℓ`."

**Why a logarithmic factor.**  For the contracting SDEs of §10.1 with `h_ℓ = h₀ 2^{−ℓ}` and `T_ℓ`
growing linearly in `ℓ`, a level-`ℓ` sample takes `N_ℓ = T_ℓ/h_ℓ ≍ (ℓ + 1) 2^ℓ` steps, which is
not `O(2^{γℓ})` for `γ = 1`.  `contracting_levels_mlmc` (`MlmcLean/ContractingLevels.lean`)
therefore applies Theorem 1 with `γ = 1 + η` and obtains the cost `O(ε^{−2−2η})` for every
`η > 0`.  Here condition iv) is replaced by

  iv') `C_ℓ ≤ c₃ (ℓ + 1)^κ 2^{γℓ}` for a real `κ ≥ 0`,

and the cost bounds become (`complexityBoundLog`)

  `E[C] ≤ c₄ ε⁻² |log ε|^κ` (`β > γ`), `c₄ ε⁻² |log ε|^{2+κ}` (`β = γ`),
  `c₄ ε^{−2−(γ−β)/α} |log ε|^κ` (`β < γ`),

Giles' bounds for `κ = 0`.  This extension is not stated in the paper.

**Proof.**  The finest level and the sample sizes are those of the proof of Theorem 1
(`exists_L_N`): `L = ⌈log₂(2c₁/ε)/α⌉₊`, so that the bias bound is `≤ ε/2` and
`L + 1 ≤ K₂ |log ε|`, and `N_ℓ` is the rounded-up Lagrange allocation for `V_ℓ = c₂ 2^{−βℓ}`,
`C_ℓ = c₃ 2^{γℓ}` and the variance `ε²/2`.  It is also the Lagrange allocation for the costs
`c₃ (L + 1)^κ 2^{γℓ}` (a factor common to all levels cancels from
`N_ℓ ∝ √(V_ℓ/C_ℓ) ∑_k √(V_k C_k)`), and on the levels `ℓ ≤ L`,
`(ℓ + 1)^κ ≤ (L + 1)^κ ≤ K₂^κ |log ε|^κ`: the cost is at most `K₂^κ |log ε|^κ` times the bound of
Theorem 1 (`cost_le_of_level`).

**The exponents.**  With the allocation `N_ℓ ∝ √(V_ℓ/C_ℓ)` rounded up the cost is at most
`2ε⁻² (∑_{ℓ ≤ L} √(V_ℓ C_ℓ))² + ∑_{ℓ ≤ L} C_ℓ`, with
`√(V_ℓ C_ℓ) ≤ √(c₂c₃) (ℓ + 1)^{κ/2} 2^{(γ−β)ℓ/2}` and `L ≍ |log ε|`: the first term is
`O(ε⁻²)` for `β > γ`, `O(ε⁻² L^{2+κ})` for `β = γ` and
`O(ε⁻² L^κ 2^{(γ−β)L})` for `β < γ`, and the rounding-up overhead is
`∑_{ℓ ≤ L} C_ℓ = O(L^κ 2^{γL}) = O(|log ε|^κ ε^{−γ/α})`.  So the three exponents above are right.
They cannot be lowered (`mlmc_cost_lower_log`), except in the case `β > γ`, where `|log ε|^κ` comes
only from the overhead, i.e. from `O(1)` samples on the finest level: it is needed when `γ = 2α`,
and for `γ < 2α` the cost is `O(ε⁻²)` (`giles_theorem1_log_of_lt`).

**Results.**
* `complexityBoundLog`, `complexityBoundLog_eq` (`= |log ε|^κ · complexityBound`);
* `mlmc_complexity_core_log` — the deterministic core;
* `giles_theorem1_log_cost_sum`, `giles_theorem1_log` — Theorem 1 with condition iv'), on a
  probability space (cost written as `∑ N_ℓ C_ℓ`, and random costs);
* `giles_theorem1_log_of_lt` — for `β > γ` and `γ < 2α`, the cost `O(ε⁻²)`;
* `mlmc_cost_lower_log` — matching lower bounds when conditions i), iii), iv') hold with equality;
* `giles_theorem1_fineCoarse_log` — Theorem 1 with condition iv') for different fine and coarse
  approximations satisfying (2.4), with independent inputs;
* `contracting_levels_mlmc_log` — §10.1: the contracting SDE of `contracting_levels_mlmc` at cost
  `O(ε⁻² |log ε|³)` (`α = 1/2`, `β = γ = 1`, logarithmic exponent `1`), instead of `O(ε^{−2−2η})`.

**Deviations.**  The extension is not in the paper.  Giles' hypothesis `β > 0` is not used and is
dropped.  `κ ≥ 0` is needed: for `κ < 0`, `β > γ`, `V_ℓ = c₂ 2^{−βℓ}` and
`C_ℓ = c₃ (ℓ + 1)^κ 2^{γℓ}`, every allocation with variance `≤ ε²` has `N₀ ≥ V₀ ε⁻²` and so costs
at least `c₂ c₃ ε⁻²` (as in the first bound of `mlmc_cost_lower_log`), which is not
`O(ε⁻² |log ε|^κ)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace MLMC

/-! ### The bound and the deterministic core -/

/-- **The three regimes of Theorem 1 with a polylogarithmic factor in the cost** (Giles 2015,
§2.1, Theorem 1, with condition iv) relaxed to `C_ℓ ≤ c₃ (ℓ + 1)^κ 2^{γℓ}`; an extension needed
for §10.1): `ε⁻² |log ε|^κ` if `β > γ`, `ε⁻² |log ε|^{2+κ}` if `β = γ` and
`ε^{−2−(γ−β)/α} |log ε|^κ` if `β < γ`.  For `κ = 0` it is `complexityBound`. -/
noncomputable def complexityBoundLog (α β γ κ ε : ℝ) : ℝ :=
  if γ < β then ε ^ (-2 : ℝ) * |Real.log ε| ^ κ
  else if β = γ then ε ^ (-2 : ℝ) * |Real.log ε| ^ (2 + κ)
  else ε ^ (-2 - (γ - β) / α) * |Real.log ε| ^ κ

/-- `complexityBoundLog` in the case `β > γ`: `ε⁻² |log ε|^κ` (Giles 2015, §2.1, Theorem 1, with
the cost factor `(ℓ + 1)^κ`). -/
lemma complexityBoundLog_of_lt {α β γ κ : ℝ} (h : γ < β) (ε : ℝ) :
    complexityBoundLog α β γ κ ε = ε ^ (-2 : ℝ) * |Real.log ε| ^ κ := by
  simp [complexityBoundLog, h]

/-- `complexityBoundLog` in the case `β = γ`: `ε⁻² |log ε|^{2+κ}` (Giles 2015, §2.1, Theorem 1,
with the cost factor `(ℓ + 1)^κ`). -/
lemma complexityBoundLog_of_eq {α β γ κ : ℝ} (h : β = γ) (ε : ℝ) :
    complexityBoundLog α β γ κ ε = ε ^ (-2 : ℝ) * |Real.log ε| ^ (2 + κ) := by
  simp [complexityBoundLog, h]

/-- `complexityBoundLog` in the case `β < γ`: `ε^{−2−(γ−β)/α} |log ε|^κ` (Giles 2015, §2.1,
Theorem 1, with the cost factor `(ℓ + 1)^κ`). -/
lemma complexityBoundLog_of_gt {α β γ κ : ℝ} (h : β < γ) (ε : ℝ) :
    complexityBoundLog α β γ κ ε = ε ^ (-2 - (γ - β) / α) * |Real.log ε| ^ κ := by
  simp [complexityBoundLog, h.ne, not_lt.2 h.le]

/-- For `κ ≥ 0` the bound `complexityBoundLog` is the bound of Giles' Theorem 1 (Giles 2015,
§2.1, `complexityBound`) times `|log ε|^κ`; in the case `β = γ`,
`(log ε)² |log ε|^κ = |log ε|^{2+κ}`. -/
lemma complexityBoundLog_eq {α β γ κ : ℝ} (hκ : 0 ≤ κ) (ε : ℝ) :
    complexityBoundLog α β γ κ ε = |Real.log ε| ^ κ * complexityBound α β γ ε := by
  rcases lt_trichotomy γ β with h | h | h
  · rw [complexityBoundLog_of_lt h, complexityBound_of_lt h]
    ring
  · rw [complexityBoundLog_of_eq h.symm, complexityBound_of_eq h.symm,
      Real.rpow_add' (abs_nonneg _) (by linarith : (2 : ℝ) + κ ≠ 0), Real.rpow_two, sq_abs]
    ring
  · rw [complexityBoundLog_of_gt h, complexityBound_of_gt h]
    ring

/-- **Theorem 1 with a polylogarithmic factor in the cost — deterministic core** (a step of this
formalisation's proof of the extension of Giles 2015, §2.1, Theorem 1, to the costs
`C_ℓ ≤ c₃ (ℓ + 1)^κ 2^{γℓ}`; not stated in the paper).  Let `α, γ, c₁, c₂, c₃ > 0`, `κ ≥ 0` and
`α ≥ ½ min(β, γ)`.  There is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and
`N_ℓ ≥ 1` with `(c₁ 2^{−αL})² + ∑_{ℓ ≤ L} c₂ 2^{−βℓ}/N_ℓ < ε²` and
`∑_{ℓ ≤ L} N_ℓ c₃ (ℓ + 1)^κ 2^{γℓ} ≤ c₄ · complexityBoundLog α β γ κ ε`.  They are the `L` and
`N_ℓ` of the proof of Theorem 1 (`exists_L_N`, Giles p. 7: "L is chosen so that
`(E[Y]−E[P])² < ½ε²`, and the constant of proportionality for `N_ℓ` is chosen so that
`V[Y] < ½ε²` … the optimal value is rounded up"): the bias bound is `≤ ε/2`, `L + 1 ≤ K₂ |log ε|`,
and `N_ℓ` is the rounded-up Lagrange allocation (§1.3, p. 4) for `V_ℓ = c₂ 2^{−βℓ}`,
`C_ℓ = c₃ 2^{γℓ}` and the variance `ε²/2`, which is also the Lagrange allocation for
`c₃ (L + 1)^κ 2^{γℓ}`.  On the levels `ℓ ≤ L`, `(ℓ + 1)^κ ≤ (L + 1)^κ ≤ K₂^κ |log ε|^κ`, which
multiplies the bound of Theorem 1 (`cost_le_of_level`).  The constant `c₄` depends only on
`α, β, γ, κ, c₁, c₂, c₃`. -/
theorem mlmc_complexity_core_log {α β γ κ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (hκ : 0 ≤ κ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) ≤
          c₄ * complexityBoundLog α β γ κ ε := by
  obtain ⟨c₄, hc₄, hcost⟩ := cost_le_of_level (β := β) hα hγ hc₂ hc₃ (K1_pos (α := α) hc₁) hαβγ
  have hK2 : 0 < K2 α c₁ := K2_pos hα
  refine ⟨c₄ * K2 α c₁ ^ κ, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hbias, hvar, hcost', hL, hL1⟩ :=
    exists_L_N (β := β) (γ := γ) hα hc₁ hc₂ hc₃ hε hε1
  refine ⟨L, N, hN, by have := pow_pos hε 2; linarith, ?_⟩
  have hlog : |Real.log ε| = -Real.log ε := abs_of_neg (Real.log_neg hε (eps_lt_one hε1))
  have hB : ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ ≤ c₄ * complexityBound α β γ ε :=
    hcost'.trans (hcost ε hε hε1 L hL)
  -- the factor `(ℓ + 1)^κ` is at most `(L + 1)^κ` on the levels `ℓ ≤ L`
  have hterm : ∀ ℓ ∈ range (L + 1),
      (N ℓ : ℝ) * (c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) ≤
        ((L : ℝ) + 1) ^ κ * ((N ℓ : ℝ) * Cb γ c₃ ℓ) := by
    intro ℓ hℓ
    have hℓL : (ℓ : ℝ) ≤ L := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    have h1 : ((ℓ : ℝ) + 1) ^ κ ≤ ((L : ℝ) + 1) ^ κ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hκ
    have h2 : 0 ≤ (N ℓ : ℝ) * Cb γ c₃ ℓ := mul_nonneg (Nat.cast_nonneg _) (Cb_pos hc₃ ℓ).le
    calc (N ℓ : ℝ) * (c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ)))
        = ((ℓ : ℝ) + 1) ^ κ * ((N ℓ : ℝ) * Cb γ c₃ ℓ) := by unfold Cb; ring
      _ ≤ ((L : ℝ) + 1) ^ κ * ((N ℓ : ℝ) * Cb γ c₃ ℓ) := mul_le_mul_of_nonneg_right h1 h2
  -- `(L + 1)^κ ≤ K₂^κ |log ε|^κ`
  have hLκ : ((L : ℝ) + 1) ^ κ ≤ K2 α c₁ ^ κ * |Real.log ε| ^ κ := by
    rw [← Real.mul_rpow hK2.le (abs_nonneg _), hlog]
    exact Real.rpow_le_rpow (by positivity) hL1 hκ
  have hS : 0 ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ :=
    Finset.sum_nonneg fun ℓ _ => mul_nonneg (Nat.cast_nonneg _) (Cb_pos hc₃ ℓ).le
  have hBnn : 0 ≤ complexityBound α β γ ε := complexityBound_nonneg hε
  calc ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ)))
      ≤ ∑ ℓ ∈ range (L + 1), ((L : ℝ) + 1) ^ κ * ((N ℓ : ℝ) * Cb γ c₃ ℓ) :=
        Finset.sum_le_sum hterm
    _ = ((L : ℝ) + 1) ^ κ * ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (K2 α c₁ ^ κ * |Real.log ε| ^ κ) * (c₄ * complexityBound α β γ ε) :=
        mul_le_mul hLκ hB hS (by positivity)
    _ = c₄ * K2 α c₁ ^ κ * complexityBoundLog α β γ κ ε := by
        rw [complexityBoundLog_eq hκ]
        ring

/-! ### Theorem 1 with the cost factor `(ℓ + 1)^κ` on a probability space -/

section prob

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The mean-square error from the core inequality** (Giles 2015, §2.1, (2.1) and (2.3), as in
the proof of Theorem 1, p. 7).  Under conditions i), ii) and iii) of Theorem 1 with the
hypotheses of `giles_theorem1` on the estimators, if `N_ℓ ≥ 1` for all `ℓ` and
`(c₁ 2^{−αL})² + ∑_{ℓ ≤ L} c₂ 2^{−βℓ}/N_ℓ < ε²`, then the multilevel estimator
`Y = ∑_{ℓ ≤ L} Y ℓ (N ℓ)` has `E[(Y − E[P])²] < ε²`. -/
lemma mse_lt_of_core_bound (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (V : ℕ → ℝ)
    {α β c₁ c₂ ε : ℝ} {L : ℕ} {N : ℕ → ℕ} (hN : ∀ ℓ, 0 < N ℓ)
    (hcore : (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 +
      ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) < ε ^ 2)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (h_i : ∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) :
    μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 := by
  have hind' : Set.Pairwise ↑(range (L + 1)) fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ :=
    fun i _ j _ hij => hind N hN hij
  rw [mlmc_mse Pℓ (fun ℓ => Y ℓ (N ℓ)) L (μ[P]) (fun ℓ => hY ℓ (N ℓ) (hN ℓ)) hPℓ hind'
    (h_ii₀ (N 0) (hN 0)) (fun ℓ => h_ii ℓ (N (ℓ + 1)) (hN (ℓ + 1)))]
  have hb : (μ[Pℓ L] - μ[P]) ^ 2 ≤ (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 := by
    have h := h_i L
    rw [integral_sub (hPℓ L) hP] at h
    exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
  have hv : ∑ ℓ ∈ range (L + 1), variance (Y ℓ (N ℓ)) μ ≤
      ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) := by
    apply Finset.sum_le_sum
    intro ℓ _
    rw [h_var ℓ (N ℓ) (hN ℓ)]
    exact div_le_div_of_nonneg_right (h_iii ℓ) (by positivity)
  linarith

/-- **Giles' Theorem 1 with a polylogarithmic factor, with the cost written as `∑_ℓ N_ℓ C_ℓ`**
(Giles 2015, §2.1, Theorem 1, with condition iv) relaxed to `C_ℓ ≤ c₃ (ℓ + 1)^κ 2^{γℓ}`).
Hypotheses as in `giles_theorem1_log` without the random costs; the conclusion bounds
`∑_{ℓ=0}^{L} N_ℓ C_ℓ`, which is the expected total cost `E[C]` when each level-`ℓ` sample has
expected cost `C_ℓ`, by `c₄ · complexityBoundLog α β γ κ ε`. -/
theorem giles_theorem1_log_cost_sum
    (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (V C : ℕ → ℝ)
    {α β γ κ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (h_i : ∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ c₄ * complexityBoundLog α β γ κ ε := by
  obtain ⟨c₄, hc₄, hcore⟩ := mlmc_complexity_core_log (β := β) hα hγ hκ hc₁ hc₂ hc₃ hαβγ
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := hcore ε hε hε1
  refine ⟨L, N, hN,
    mse_lt_of_core_bound P Pℓ Y V hN hmse hP hPℓ hY hind h_i h_ii₀ h_ii h_var h_iii, ?_⟩
  calc ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ
      ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :=
        Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (h_iv ℓ) (Nat.cast_nonneg _)
    _ ≤ c₄ * complexityBoundLog α β γ κ ε := hcost

/-- **Giles' Theorem 1 with a polylogarithmic factor in the cost** (Giles 2015, §2.1, Theorem 1,
with its condition "iv) `C_ℓ ≤ c₃ 2^{γℓ}`" relaxed to `C_ℓ ≤ c₃ (ℓ + 1)^κ 2^{γℓ}`: the extension
needed for §10.1, p. 61, where "it is appropriate to choose `N_ℓ` to increase linearly with level"
and a level-`ℓ` sample of a contracting SDE costs of order `ℓ 2^ℓ`).
Let `P` be an integrable random variable and `Pℓ ℓ` its integrable level-`ℓ` approximation.
Suppose there are square-integrable estimators `Y ℓ n` based on `n ≥ 1` Monte Carlo samples,
pairwise independent across levels for every choice of sample sizes `N ≥ 1`, whose samples at
level `ℓ` have variance `V ℓ` (so `V[Y ℓ n] = V ℓ / n` for `n ≥ 1`) and expected cost `C ℓ` (so the
integrable random cost `Cost ℓ n` of computing `Y ℓ n` has `E[Cost ℓ n] = n C ℓ` for `n ≥ 1`), and
constants `α, γ, c₁, c₂, c₃ > 0`, `κ ≥ 0` and `β` with `α ≥ ½ min(β,γ)` and

  (i)   `|E[Pℓ ℓ − P]| ≤ c₁ 2^{−αℓ}`,
  (ii)  `E[Y 0 n] = E[Pℓ 0]`, `E[Y (ℓ+1) n] = E[Pℓ (ℓ+1) − Pℓ ℓ]` for `n ≥ 1`,
  (iii) `V ℓ ≤ c₂ 2^{−βℓ}`,
  (iv') `C ℓ ≤ c₃ (ℓ + 1)^κ 2^{γℓ}`.

Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N ℓ ≥ 1` for which
`Y = ∑_{ℓ=0}^{L} Y ℓ (N ℓ)` has `MSE = E[(Y − E[P])²] < ε²` and the cost
`C = ∑_{ℓ=0}^{L} Cost ℓ (N ℓ)` has `E[C] ≤ c₄ ε⁻² |log ε|^κ` if `β > γ`,
`c₄ ε⁻² |log ε|^{2+κ}` if `β = γ`, and `c₄ ε^{−2−(γ−β)/α} |log ε|^κ` if `β < γ`
(`complexityBoundLog`).  For `κ = 0` this is Giles' Theorem 1 (`giles_theorem1`).  The extension
is not stated in the paper.  Its exponents cannot be lowered (`mlmc_cost_lower_log`), except that
for `β > γ` and `γ < 2α` the cost is `O(ε⁻²)` (`giles_theorem1_log_of_lt`).  Giles' hypothesis
`β > 0` is not needed and is dropped.  `κ ≥ 0` is needed: for `κ < 0` and `β > γ` the bound fails
when `V_ℓ = c₂ 2^{−βℓ}` and `C_ℓ = c₃ (ℓ + 1)^κ 2^{γℓ}`, since a variance `≤ ε²` needs
`N₀ ≥ V₀ ε⁻²` and so costs at least `c₂ c₃ ε⁻²` (as in `mlmc_cost_lower_log`).  The constant `c₄`
depends only on `α, β, γ, κ, c₁, c₂, c₃` (`mlmc_complexity_core_log`). -/
theorem giles_theorem1_log
    (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (Cost : ℕ → ℕ → Ω → ℝ) (V C : ℕ → ℝ)
    {α β γ κ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost_int : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (hCost_mean : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_i : ∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        μ[fun ω => ∑ ℓ ∈ range (L + 1), Cost ℓ (N ℓ) ω] ≤
          c₄ * complexityBoundLog α β γ κ ε := by
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_log_cost_sum P Pℓ Y V C hα hγ hκ hc₁ hc₂ hc₃ hαβγ hP
    hPℓ hY hind h_i h_ii₀ h_ii h_var h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, hmse, ?_⟩
  have hE : μ[fun ω => ∑ ℓ ∈ range (L + 1), Cost ℓ (N ℓ) ω] =
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := by
    rw [integral_finsetSum _ fun ℓ _ => hCost_int ℓ (N ℓ) (hN ℓ)]
    exact Finset.sum_congr rfl fun ℓ _ => hCost_mean ℓ (N ℓ) (hN ℓ)
  rw [hE]
  exact hcost

/-- A power of `ℓ + 1` grows more slowly than any exponential (for the case `β > γ`, `γ < 2α` of
Giles 2015, §2.1, Theorem 1, with the cost factor `(ℓ + 1)^κ`): for `κ ≥ 0` and `η > 0` there is
`A > 0` with `(ℓ + 1)^κ ≤ A 2^{ηℓ}` for all `ℓ`, namely `A = (1 + (2^δ − 1)⁻¹)^κ`,
`δ = η/(κ + 1)` (`succ_le_two_rpow`). -/
lemma succ_rpow_le_two_rpow {κ η : ℝ} (hκ : 0 ≤ κ) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧ ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ κ ≤ A * (2 : ℝ) ^ (η * (ℓ : ℝ)) := by
  have hδ : 0 < η / (κ + 1) := div_pos hη (by linarith)
  have hq : 1 < (2 : ℝ) ^ (η / (κ + 1)) := Real.one_lt_rpow (by norm_num) hδ
  have hA0 : 0 < 1 + ((2 : ℝ) ^ (η / (κ + 1)) - 1)⁻¹ := by
    have : 0 < (2 : ℝ) ^ (η / (κ + 1)) - 1 := by linarith
    positivity
  refine ⟨(1 + ((2 : ℝ) ^ (η / (κ + 1)) - 1)⁻¹) ^ κ, Real.rpow_pos_of_pos hA0 κ, fun ℓ => ?_⟩
  have h1 := succ_le_two_rpow hδ ℓ
  have hexp : η / (κ + 1) * (ℓ : ℝ) * κ ≤ η * (ℓ : ℝ) := by
    have e : η / (κ + 1) * (ℓ : ℝ) * κ = η * (ℓ : ℝ) * (κ / (κ + 1)) := by ring
    rw [e]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by linarith)).2 (by linarith))
  calc ((ℓ : ℝ) + 1) ^ κ
      ≤ ((1 + ((2 : ℝ) ^ (η / (κ + 1)) - 1)⁻¹) * (2 : ℝ) ^ (η / (κ + 1) * (ℓ : ℝ))) ^ κ :=
        Real.rpow_le_rpow (by positivity) h1 hκ
    _ = (1 + ((2 : ℝ) ^ (η / (κ + 1)) - 1)⁻¹) ^ κ * (2 : ℝ) ^ (η / (κ + 1) * (ℓ : ℝ) * κ) := by
        rw [Real.mul_rpow hA0.le (by positivity), ← Real.rpow_mul (by norm_num)]
    _ ≤ (1 + ((2 : ℝ) ^ (η / (κ + 1)) - 1)⁻¹) ^ κ * (2 : ℝ) ^ (η * (ℓ : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
          (Real.rpow_nonneg hA0.le κ)

/-- **No logarithmic factor when `β > γ` and `γ < 2α`** (Giles 2015, §2.1, Theorem 1, case
`β > γ`: "the dominant computational cost is on the coarsest levels where `C_ℓ = O(1)` and
`O(ε⁻²)` samples are required to achieve the desired accuracy", with condition iv) relaxed to
`C_ℓ ≤ c₃ (ℓ + 1)^κ 2^{γℓ}`).  Under the hypotheses of `giles_theorem1_log_cost_sum`, if `γ < β`
and `γ < 2α` there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with
`MSE < ε²` and `∑_{ℓ ≤ L} N_ℓ C_ℓ ≤ c₄ ε⁻²`: the factor `|log ε|^κ` of `giles_theorem1_log` in the
case `β > γ` is needed only at the boundary `γ = 2α` (`mlmc_cost_lower_log`).  Proof:
`(ℓ + 1)^κ ≤ A 2^{ηℓ}` with `η = ½ min(β − γ, 2α − γ)` (`succ_rpow_le_two_rpow`), and Theorem 1
(`giles_theorem1_cost_sum`) with the rate `γ + η`, which satisfies `γ + η < β` and
`γ + η < 2α`.  Not stated in the paper; the hypotheses `α ≥ ½ min(β, γ)` and `β > 0` of Theorem 1
follow from `γ < 2α` and `0 < γ < β`. -/
theorem giles_theorem1_log_of_lt
    (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (V C : ℕ → ℝ)
    {α β γ κ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hγβ : γ < β) (hγα : γ < 2 * α)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (h_i : ∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  -- a rate `γ' = γ + η` strictly between `γ` and `min(β, 2α)`
  have hη : 0 < min (β - γ) (2 * α - γ) / 2 := by
    have := lt_min (sub_pos.2 hγβ) (sub_pos.2 hγα)
    linarith
  have hη1 : min (β - γ) (2 * α - γ) / 2 < β - γ := by
    have := min_le_left (β - γ) (2 * α - γ)
    linarith
  have hη2 : min (β - γ) (2 * α - γ) / 2 < 2 * α - γ := by
    have := min_le_right (β - γ) (2 * α - γ)
    linarith
  obtain ⟨A, hA, hpoly⟩ := succ_rpow_le_two_rpow hκ hη
  have hmin : min β (γ + min (β - γ) (2 * α - γ) / 2) / 2 ≤ α := by
    have := min_le_right β (γ + min (β - γ) (2 * α - γ) / 2)
    linarith
  -- condition (iv) of Theorem 1 with the rate `γ'`: `C_ℓ ≤ c₃ A 2^{γ'ℓ}`
  have h_iv' : ∀ ℓ : ℕ, C ℓ ≤ c₃ * A *
      (2 : ℝ) ^ ((γ + min (β - γ) (2 * α - γ) / 2) * (ℓ : ℝ)) := fun ℓ => by
    have e : (2 : ℝ) ^ ((γ + min (β - γ) (2 * α - γ) / 2) * (ℓ : ℝ)) =
        (2 : ℝ) ^ (min (β - γ) (2 * α - γ) / 2 * (ℓ : ℝ)) * (2 : ℝ) ^ (γ * (ℓ : ℝ)) := by
      rw [← Real.rpow_add two_pos]
      congr 1
      ring
    rw [e]
    calc C ℓ ≤ c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ)) := h_iv ℓ
      _ ≤ c₃ * (A * (2 : ℝ) ^ (min (β - γ) (2 * α - γ) / 2 * (ℓ : ℝ))) *
          (2 : ℝ) ^ (γ * (ℓ : ℝ)) := by
        gcongr
        exact hpoly ℓ
      _ = c₃ * A * ((2 : ℝ) ^ (min (β - γ) (2 * α - γ) / 2 * (ℓ : ℝ)) *
          (2 : ℝ) ^ (γ * (ℓ : ℝ))) := by ring
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_cost_sum P Pℓ Y V C hα (by linarith) (by linarith)
    hc₁ hc₂ (mul_pos hc₃ hA) hmin hP hPℓ hY hind h_i h_ii₀ h_ii h_var h_iii h_iv'
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  rw [complexityBound_of_lt (by linarith)] at hcost
  exact ⟨L, N, hN, hmse, hcost⟩

end prob

/-! ### The exponents cannot be lowered -/

/-- A Bernoulli-type lower bound for a sum of powers (for the lower bounds of the extension of
Giles 2015, §2.1, Theorem 1): `n^{p+1}/(p + 1) ≤ ∑_{j<n} (j + 1)^p` for `p ≥ 0`.  Induction on `n`
with Bernoulli's inequality `(n/(n + 1))^{p+1} ≥ 1 − (p + 1)/(n + 1)`
(`one_add_mul_self_le_rpow_one_add`). -/
lemma rpow_div_le_sum_succ_rpow {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    (n : ℝ) ^ (p + 1) / (p + 1) ≤ ∑ j ∈ range n, ((j : ℝ) + 1) ^ p := by
  have hp1 : 0 < p + 1 := by linarith
  induction n with
  | zero =>
    rw [Finset.sum_range_zero, Nat.cast_zero, Real.zero_rpow hp1.ne', zero_div]
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    -- Bernoulli: `1 − (p + 1)/(n + 1) ≤ (n/(n + 1))^{p+1}`
    have hs : (-1 : ℝ) ≤ -1 / ((n : ℝ) + 1) := by
      rw [neg_div, neg_le_neg_iff, div_le_one hn1]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hb := one_add_mul_self_le_rpow_one_add hs (by linarith : (1 : ℝ) ≤ p + 1)
    have e1 : 1 + -1 / ((n : ℝ) + 1) = (n : ℝ) / ((n : ℝ) + 1) := by
      field_simp
      ring
    rw [e1, Real.div_rpow (Nat.cast_nonneg n) hn1.le] at hb
    have hq : 0 < ((n : ℝ) + 1) ^ (p + 1) := Real.rpow_pos_of_pos hn1 _
    rw [le_div_iff₀ hq] at hb
    -- `(n + 1)^{p+1} ≤ n^{p+1} + (p + 1)(n + 1)^p`
    have key : ((n : ℝ) + 1) ^ (p + 1) ≤ (n : ℝ) ^ (p + 1) + (p + 1) * ((n : ℝ) + 1) ^ p := by
      have e3 : (1 + (p + 1) * (-1 / ((n : ℝ) + 1))) * ((n : ℝ) + 1) ^ (p + 1) =
          ((n : ℝ) + 1) ^ (p + 1) - (p + 1) * ((n : ℝ) + 1) ^ p := by
        rw [Real.rpow_add_one hn1.ne' p]
        field_simp
        ring
      linarith
    calc ((n : ℝ) + 1) ^ (p + 1) / (p + 1)
        ≤ ((n : ℝ) ^ (p + 1) + (p + 1) * ((n : ℝ) + 1) ^ p) / (p + 1) :=
          div_le_div_of_nonneg_right key hp1.le
      _ = (n : ℝ) ^ (p + 1) / (p + 1) + ((n : ℝ) + 1) ^ p := by
          field_simp
      _ ≤ ∑ j ∈ range n, ((j : ℝ) + 1) ^ p + ((n : ℝ) + 1) ^ p := by linarith

/-- **Lower bounds for the cost: the exponents of `giles_theorem1_log` are sharp** (for the
extension of Giles 2015, §2.1, Theorem 1, to the costs `C_ℓ ≤ c₃ (ℓ + 1)^κ 2^{γℓ}`; not stated in
the paper).
Consider the model in which conditions i), iii) and iv') hold with equality: the bias `c₁ 2^{−αℓ}`,
the variances `V_ℓ = c₂ 2^{−βℓ}` and the costs `C_ℓ = c₃ (ℓ + 1)^κ 2^{γℓ}`, with
`α, c₁, c₂, c₃ > 0` and `κ ≥ 0`; by Giles (2.1) and (2.3) the multilevel estimator with finest
level `L` and `N_ℓ ≥ 1` samples on level `ℓ` has `MSE = (c₁ 2^{−αL})² + ∑_{ℓ ≤ L} V_ℓ/N_ℓ`.  If
this is `≤ ε²` with `0 < ε < c₁`, then its cost `∑_{ℓ ≤ L} N_ℓ C_ℓ` is at least
* `c₂ c₃ ε⁻²` (the coarsest level needs `N₀ ≥ V₀ ε⁻²`);
* `c₂ c₃ (1 + κ/2)⁻² ε⁻² (log₂(c₁/ε)/α)^{2+κ}` if `β = γ` (Cauchy–Schwarz, `cost_lower_bound`,
  `∑_{ℓ ≤ L} (ℓ + 1)^{κ/2} ≥ (L + 1)^{1+κ/2}/(1 + κ/2)` and `L ≥ log₂(c₁/ε)/α`);
* `c₂ c₃ ε⁻² (c₁/ε)^{(γ−β)/α} (log₂(c₁/ε)/α)^κ` if `β ≤ γ` (the finest level needs
  `N_L ≥ V_L ε⁻²`);
* `c₃ (c₁/ε)^{γ/α} (log₂(c₁/ε)/α)^κ` if `γ ≥ 0` (one sample on the finest level).
As `log₂(c₁/ε) ~ |log ε|/log 2` for `ε → 0`, these are the bounds `complexityBoundLog` of
`giles_theorem1_log` up to constants for `β = γ` and for `β < γ`, and for `β > γ` with `γ = 2α`
(the last bound, `(c₁/ε)^{γ/α} = (c₁/ε)²`); for `β > γ` and `γ < 2α` the first bound matches
`giles_theorem1_log_of_lt`.  The case `κ = 0` gives the sharpness of Giles' bounds. -/
theorem mlmc_cost_lower_log {α β γ κ c₁ c₂ c₃ ε : ℝ} (hα : 0 < α) (hκ : 0 ≤ κ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hε : 0 < ε) (hεc : ε < c₁) (L : ℕ)
    (N : ℕ → ℕ) (hN : ∀ ℓ, 0 < N ℓ)
    (hmse : (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 +
      ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) ≤ ε ^ 2) :
    c₂ * c₃ * ε ^ (-2 : ℝ) ≤
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) ∧
    (β = γ → c₂ * c₃ / (1 + κ / 2) ^ 2 * ε ^ (-2 : ℝ) * (Real.logb 2 (c₁ / ε) / α) ^ (2 + κ) ≤
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ)))) ∧
    (β ≤ γ → c₂ * c₃ * ε ^ (-2 : ℝ) * (c₁ / ε) ^ ((γ - β) / α) *
        (Real.logb 2 (c₁ / ε) / α) ^ κ ≤
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ)))) ∧
    (0 ≤ γ → c₃ * (c₁ / ε) ^ (γ / α) * (Real.logb 2 (c₁ / ε) / α) ^ κ ≤
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ)))) := by
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ → ℝ,
      C = fun ℓ : ℕ => c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ)) := ⟨_, rfl⟩
  have hsum : ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * ((ℓ : ℝ) + 1) ^ κ *
      (2 : ℝ) ^ (γ * (ℓ : ℝ))) = ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := by
    rw [hCdef]
  rw [hsum]
  have hC : ∀ ℓ, 0 < C ℓ := fun ℓ => by rw [hCdef]; positivity
  have hcost0 : ∀ ℓ ∈ range (L + 1), 0 ≤ (N ℓ : ℝ) * C ℓ :=
    fun ℓ _ => mul_nonneg (Nat.cast_nonneg _) (hC ℓ).le
  -- the squared bias and the variance are both at most `ε²`
  have hV0 : ∀ ℓ ∈ range (L + 1), 0 ≤ Vb β c₂ ℓ / (N ℓ : ℝ) :=
    fun ℓ _ => div_nonneg (Vb_pos hc₂ ℓ).le (Nat.cast_nonneg _)
  have hvar0 : 0 ≤ ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) := Finset.sum_nonneg hV0
  have hb0 : 0 ≤ (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 := sq_nonneg _
  have hbias : c₁ * (2 : ℝ) ^ (-(α * (L : ℝ))) ≤ ε :=
    (pow_le_pow_iff_left₀ (by positivity) hε.le two_ne_zero).1 (by linarith)
  have hvar : ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) ≤ ε ^ 2 := by linarith
  -- the number of levels: `log₂(c₁/ε)/α ≤ L`
  have h2pos : 0 < (2 : ℝ) ^ (α * (L : ℝ)) := Real.rpow_pos_of_pos two_pos _
  have h2L : c₁ / ε ≤ (2 : ℝ) ^ (α * (L : ℝ)) := by
    rw [Real.rpow_neg zero_le_two, ← div_eq_mul_inv, div_le_iff₀ h2pos] at hbias
    rw [div_le_iff₀ hε]
    linarith
  have hlog : 0 < Real.logb 2 (c₁ / ε) / α :=
    div_pos (Real.logb_pos one_lt_two ((one_lt_div hε).2 hεc)) hα
  have hlogL : Real.logb 2 (c₁ / ε) / α ≤ (L : ℝ) + 1 := by
    have h := (Real.logb_le_iff_le_rpow one_lt_two (div_pos hc₁ hε)).2 h2L
    rw [div_le_iff₀ hα]
    nlinarith
  -- `(c₁/ε)^{q/α} ≤ 2^{qL}` for `q ≥ 0`
  have hpowL : ∀ q : ℝ, 0 ≤ q → (c₁ / ε) ^ (q / α) ≤ (2 : ℝ) ^ (q * (L : ℝ)) := fun q hq => by
    have e : (2 : ℝ) ^ (q * (L : ℝ)) = ((2 : ℝ) ^ (α * (L : ℝ))) ^ (q / α) := by
      rw [← Real.rpow_mul zero_le_two]
      congr 1
      field_simp
    rw [e]
    exact Real.rpow_le_rpow (div_pos hc₁ hε).le h2L (div_nonneg hq hα.le)
  have hεinv : ε ^ (-2 : ℝ) = (ε ^ 2)⁻¹ := by
    rw [Real.rpow_neg hε.le, Real.rpow_two]
  -- every level needs `N_ℓ ≥ V_ℓ ε⁻²`, and the cost is at least that of any one level
  have hNℓ : ∀ ℓ ∈ range (L + 1), Vb β c₂ ℓ * ε ^ (-2 : ℝ) ≤ N ℓ := fun ℓ hℓ => by
    have h1 : Vb β c₂ ℓ / (N ℓ : ℝ) ≤ ε ^ 2 := (Finset.single_le_sum hV0 hℓ).trans hvar
    have hNpos : (0 : ℝ) < N ℓ := by exact_mod_cast hN ℓ
    rw [div_le_iff₀ hNpos] at h1
    rw [hεinv, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hε 2)]
    linarith
  have hlev : ∀ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ :=
    fun ℓ hℓ => Finset.single_le_sum hcost0 hℓ
  have h0 : (0 : ℕ) ∈ range (L + 1) := Finset.mem_range.2 (Nat.succ_pos L)
  have hL : L ∈ range (L + 1) := Finset.self_mem_range_succ L
  refine ⟨?_, fun hβγ => ?_, fun hβγ => ?_, fun hγ => ?_⟩
  · -- the coarsest level: `N₀ C₀ ≥ ε⁻² V₀ C₀ = c₂ c₃ ε⁻²`
    have hV00 : Vb β c₂ 0 = c₂ := by
      unfold Vb
      rw [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one]
    have hC00 : C 0 = c₃ := by
      rw [hCdef]
      simp
    calc c₂ * c₃ * ε ^ (-2 : ℝ) = Vb β c₂ 0 * ε ^ (-2 : ℝ) * C 0 := by rw [hV00, hC00]; ring
      _ ≤ (N 0 : ℝ) * C 0 := mul_le_mul_of_nonneg_right (hNℓ 0 h0) (hC 0).le
      _ ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := hlev 0 h0
  · -- `β = γ`: Cauchy–Schwarz, `cost ≥ ε⁻² (∑ √(V_ℓ C_ℓ))²`, `√(V_ℓ C_ℓ) = √(c₂c₃) (ℓ+1)^{κ/2}`
    have hcs := cost_lower_bound (range (L + 1)) (Vb β c₂) C (fun ℓ => (N ℓ : ℝ)) (pow_pos hε 2)
      (fun ℓ _ => (Vb_pos hc₂ ℓ).le) (fun ℓ _ => (hC ℓ).le)
      (fun ℓ _ => by exact_mod_cast hN ℓ) hvar
    have hVC : ∀ ℓ : ℕ, Real.sqrt (Vb β c₂ ℓ * C ℓ) =
        Real.sqrt (c₂ * c₃) * ((ℓ : ℝ) + 1) ^ (κ / 2) := fun ℓ => by
      have h1 : (2 : ℝ) ^ (-(β * (ℓ : ℝ))) * (2 : ℝ) ^ (γ * (ℓ : ℝ)) = 1 := by
        rw [← Real.rpow_add two_pos, hβγ, neg_add_cancel, Real.rpow_zero]
      have e : Vb β c₂ ℓ * C ℓ = (c₂ * c₃) * ((ℓ : ℝ) + 1) ^ κ := by
        rw [hCdef]
        unfold Vb
        calc c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) * (c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ)))
            = c₂ * c₃ * ((ℓ : ℝ) + 1) ^ κ *
              ((2 : ℝ) ^ (-(β * (ℓ : ℝ))) * (2 : ℝ) ^ (γ * (ℓ : ℝ))) := by ring
          _ = c₂ * c₃ * ((ℓ : ℝ) + 1) ^ κ := by rw [h1, mul_one]
      rw [e, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (((ℓ : ℝ) + 1) ^ κ),
        ← Real.rpow_mul (by positivity)]
      congr 2
      ring
    have hS : Real.sqrt (c₂ * c₃) * (((L : ℝ) + 1) ^ (κ / 2 + 1) / (κ / 2 + 1)) ≤
        ∑ ℓ ∈ range (L + 1), Real.sqrt (Vb β c₂ ℓ * C ℓ) := by
      rw [Finset.sum_congr rfl fun ℓ _ => hVC ℓ, ← Finset.mul_sum]
      have h := rpow_div_le_sum_succ_rpow (p := κ / 2) (by positivity) (L + 1)
      push_cast at h
      exact mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    have hS0 : 0 ≤ Real.sqrt (c₂ * c₃) * (((L : ℝ) + 1) ^ (κ / 2 + 1) / (κ / 2 + 1)) := by
      positivity
    have hsq : (Real.sqrt (c₂ * c₃) * (((L : ℝ) + 1) ^ (κ / 2 + 1) / (κ / 2 + 1))) ^ 2 =
        c₂ * c₃ / (1 + κ / 2) ^ 2 * ((L : ℝ) + 1) ^ (2 + κ) := by
      have h2 : (((L : ℝ) + 1) ^ (κ / 2 + 1)) ^ 2 = ((L : ℝ) + 1) ^ (2 + κ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring
      rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), h2, add_comm (κ / 2) 1]
      ring
    have hL2κ : (Real.logb 2 (c₁ / ε) / α) ^ (2 + κ) ≤ ((L : ℝ) + 1) ^ (2 + κ) :=
      Real.rpow_le_rpow hlog.le hlogL (by linarith)
    calc c₂ * c₃ / (1 + κ / 2) ^ 2 * ε ^ (-2 : ℝ) * (Real.logb 2 (c₁ / ε) / α) ^ (2 + κ)
        ≤ c₂ * c₃ / (1 + κ / 2) ^ 2 * ε ^ (-2 : ℝ) * ((L : ℝ) + 1) ^ (2 + κ) := by
          gcongr
      _ = (ε ^ 2)⁻¹ * (Real.sqrt (c₂ * c₃) *
            (((L : ℝ) + 1) ^ (κ / 2 + 1) / (κ / 2 + 1))) ^ 2 := by
          rw [hsq, hεinv]
          ring
      _ ≤ (ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (Vb β c₂ ℓ * C ℓ)) ^ 2 := by
          gcongr
      _ ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := hcs
  · -- `β ≤ γ`: the finest level alone, `N_L C_L ≥ ε⁻² V_L C_L`
    have e : Vb β c₂ L * C L =
        c₂ * c₃ * ((L : ℝ) + 1) ^ κ * (2 : ℝ) ^ ((γ - β) * (L : ℝ)) := by
      rw [hCdef]
      unfold Vb
      have h1 : (2 : ℝ) ^ (-(β * (L : ℝ))) * (2 : ℝ) ^ (γ * (L : ℝ)) =
          (2 : ℝ) ^ ((γ - β) * (L : ℝ)) := by
        rw [← Real.rpow_add two_pos]
        congr 1
        ring
      calc c₂ * (2 : ℝ) ^ (-(β * (L : ℝ))) * (c₃ * ((L : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (L : ℝ)))
          = c₂ * c₃ * ((L : ℝ) + 1) ^ κ *
            ((2 : ℝ) ^ (-(β * (L : ℝ))) * (2 : ℝ) ^ (γ * (L : ℝ))) := by ring
        _ = _ := by rw [h1]
    have h1 := hpowL (γ - β) (by linarith)
    have hκL : (Real.logb 2 (c₁ / ε) / α) ^ κ ≤ ((L : ℝ) + 1) ^ κ :=
      Real.rpow_le_rpow hlog.le hlogL hκ
    calc c₂ * c₃ * ε ^ (-2 : ℝ) * (c₁ / ε) ^ ((γ - β) / α) * (Real.logb 2 (c₁ / ε) / α) ^ κ
        ≤ c₂ * c₃ * ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * (L : ℝ)) * ((L : ℝ) + 1) ^ κ := by
          gcongr
      _ = Vb β c₂ L * ε ^ (-2 : ℝ) * C L := by rw [mul_right_comm _ _ (C L), e]; ring
      _ ≤ (N L : ℝ) * C L := mul_le_mul_of_nonneg_right (hNℓ L hL) (hC L).le
      _ ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := hlev L hL
  · -- `γ ≥ 0`: one sample on the finest level, `N_L C_L ≥ C_L`
    have h1 := hpowL γ hγ
    have hκL : (Real.logb 2 (c₁ / ε) / α) ^ κ ≤ ((L : ℝ) + 1) ^ κ :=
      Real.rpow_le_rpow hlog.le hlogL hκ
    have hNL1 : (1 : ℝ) ≤ N L := by exact_mod_cast hN L
    calc c₃ * (c₁ / ε) ^ (γ / α) * (Real.logb 2 (c₁ / ε) / α) ^ κ
        ≤ c₃ * (2 : ℝ) ^ (γ * (L : ℝ)) * ((L : ℝ) + 1) ^ κ := by
          gcongr
      _ = C L := by rw [hCdef]; ring
      _ ≤ (N L : ℝ) * C L := le_mul_of_one_le_left (hC L).le hNL1
      _ ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := hlev L hL

/-! ### Different fine and coarse approximations (Giles 2015, §2.1, (2.4)) -/

section corrections

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Theorem 1 with a polylogarithmic factor for different fine and coarse approximations**
(Giles 2015, §2.1, p. 8, (2.4) and Theorem 1, with condition iv) relaxed to
`C_ℓ ≤ c₃ (ℓ + 1)^κ 2^{γℓ}`).  The multilevel estimator is
`Y = ∑_{ℓ=0}^{L} N_ℓ⁻¹ ∑_{n<N_ℓ} (P^f_ℓ − P^c_{ℓ−1})(ω^{(ℓ,n)})` with `P^c_{−1} ≡ 0`, where the
inputs `ω (ℓ, n)` are mutually independent with law `ν`.  Let the approximations be measurable and
square integrable and satisfy (2.4), `E[P^f_ℓ] = E[P^c_ℓ]` ("Provided we maintain the identity
`E[P^f_ℓ] = E[P^c_ℓ]` … then condition ii) is satisfied"), let the `n`-th level-`ℓ` sample have
an integrable cost of mean `C ℓ`, and let (i) `|E[P^f_ℓ − P]| ≤ c₁ 2^{−αℓ}`,
(iii) `V[P^f_ℓ − P^c_{ℓ−1}] ≤ c₂ 2^{−βℓ}` and (iv') `C_ℓ ≤ c₃ (ℓ + 1)^κ 2^{γℓ}` with
`α, γ, c₁, c₂, c₃ > 0`, `κ ≥ 0` and `α ≥ ½ min(β, γ)`.  Then there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with `MSE < ε²` and expected cost
`E[C] ≤ c₄ · complexityBoundLog α β γ κ ε`.  As `giles_theorem1_fineCoarse` (via
`giles_theorem1_corrections`), with `giles_theorem1_log` in place of `giles_theorem1`; Giles'
hypothesis `β > 0` is dropped. -/
theorem giles_theorem1_fineCoarse_log [IsProbabilityMeasure μ] (P : Ω₀ → ℝ)
    (Pf Pc : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
    {α β γ κ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) (hP : Integrable P ν)
    (hPfm : ∀ ℓ, Measurable (Pf ℓ)) (hPcm : ∀ ℓ, Measurable (Pc ℓ))
    (hPf : ∀ ℓ, MemLp (Pf ℓ) 2 ν) (hPc : ∀ ℓ, MemLp (Pc ℓ) 2 ν)
    (h24 : ∀ ℓ, ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (h_i : ∀ ℓ : ℕ, |∫ y, Pf ℓ y - P y ∂ν| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, variance (fineCoarseDiff Pf Pc ℓ) ν ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * ((ℓ : ℝ) + 1) ^ κ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf Pc) ω ℓ (N ℓ) x -
          ∫ y, P y ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * complexityBoundLog α β γ κ ε := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  have hPf1 : ∀ ℓ, Integrable (Pf ℓ) ν := fun ℓ => (hPf ℓ).integrable one_le_two
  have hPc1 : ∀ ℓ, Integrable (Pc ℓ) ν := fun ℓ => (hPc ℓ).integrable one_le_two
  have hΔm := measurable_fineCoarseDiff hPfm hPcm
  have hΔ := memLp_fineCoarseDiff hPf hPc
  have hΔ1 : ∀ ℓ, Integrable (fineCoarseDiff Pf Pc ℓ) ν := fun ℓ => (hΔ ℓ).integrable one_le_two
  have h_ii := integral_fineCoarseDiff hPf1 hPc1 h24
  -- transport `P` and `P^f_ℓ` to `Ω` along the input `ω (0, 0)`
  have hφ := hω (0, 0)
  have tr : ∀ f : Ω₀ → ℝ, Integrable f ν → ∫ x, f (ω (0, 0) x) ∂μ = ∫ y, f y ∂ν :=
    fun f hf => integral_comp_of_measurePreserving hφ hf.aestronglyMeasurable
  have hPμ : Integrable (fun x => P (ω (0, 0) x)) μ :=
    (hφ.integrable_comp hP.aestronglyMeasurable).2 hP
  have hPfμ : ∀ ℓ, Integrable (fun x => Pf ℓ (ω (0, 0) x)) μ :=
    fun ℓ => (hφ.integrable_comp (hPf1 ℓ).aestronglyMeasurable).2 (hPf1 ℓ)
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_log (μ := μ) (fun x => P (ω (0, 0) x))
    (fun ℓ x => Pf ℓ (ω (0, 0) x)) (fun ℓ n => blockMean (fineCoarseDiff Pf Pc) ω ℓ n)
    (fun ℓ n x => ∑ k ∈ range n, cost ℓ k x) (fun ℓ => variance (fineCoarseDiff Pf Pc ℓ) ν) C
    hα hγ hκ hc₁ hc₂ hc₃ hαβγ hPμ hPfμ (fun ℓ n _ => memLp_blockMean hω hΔ ℓ n)
    (fun N _ i j hij => indepFun_blockMean (fun p => (hω p).measurable) hind hΔm hij _ _)
    (fun ℓ n _ => integrable_finsetSum _ fun k _ => hcost ℓ k)
    (fun ℓ n _ => by
      rw [integral_finsetSum _ fun k _ => hcost ℓ k]
      simp [hcostC])
    (fun ℓ => by
      dsimp only
      rw [tr (fun y => Pf ℓ y - P y) ((hPf1 ℓ).sub hP)]
      exact h_i ℓ)
    (fun n hn => by
      rw [integral_blockMean hω hΔ1 0 hn, h_ii 0, tr (Pf 0) (hPf1 0), levelDiff_zero])
    (fun ℓ n hn => by
      dsimp only
      rw [integral_blockMean hω hΔ1 (ℓ + 1) hn, h_ii (ℓ + 1),
        tr (fun y => Pf (ℓ + 1) y - Pf ℓ y) ((hPf1 (ℓ + 1)).sub (hPf1 ℓ)), levelDiff_succ])
    (fun ℓ n hn => variance_blockMean hω hind hΔm hΔ ℓ hn) h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost'⟩ := h ε hε hε1
  refine ⟨L, N, hN, ?_, hcost'⟩
  rw [tr P hP] at hmse
  exact hmse

end corrections

/-! ### Contracting SDEs with level-dependent time steps (Giles 2015, §10.1) -/

section levels

variable {a b : ℝ → ℝ} {Ka Kb : ℝ≥0} {κ δ : ℝ}

/-- **Theorem 1 end to end for a contracting SDE with level-dependent time steps, at cost
`O(ε⁻² |log ε|³)`** (Giles 2015, §10.1, p. 61: "A very similar approach can also be used for
contracting SDEs which converge to a limiting distribution.  For these, the level `ℓ` path will
perform a simulation for the time interval `[−T_ℓ, 0]`, using timestep `h_ℓ`", with "it is
appropriate to choose `N_ℓ` to increase linearly with level" and §2.1, Theorem 1).  A
strengthening of `contracting_levels_mlmc`, with its hypotheses and without `η`: let `a` be
`K_a`-Lipschitz and dissipative, `(x − y)(a(x) − a(y)) ≤ −κ (x − y)²`, let `b` be `K_b`-Lipschitz,
let `h_ℓ = h₀ 2^{−ℓ}` with the margin `K_b² + K_a² h₀ + δ ≤ 2κ`, `δ > 0`, let level `ℓ` take `N_ℓ`
steps with `2N_ℓ ≤ N_{ℓ+1}`, `T_ℓ = N_ℓ h_ℓ ≥ c ℓ`, `c δ ≥ 8 log 2` and `N_ℓ ≤ m (ℓ + 1) 2^ℓ`, with
the coupling of `variance_contractLevels_le`, and let `f` be a `K_f`-Lipschitz payoff.  Then:
(1) for every `ℓ`, `f(X^{(ℓ)})` is integrable, the chain with step `h_ℓ` started at `x₀` `n` steps
in the past converges almost surely as `n → ∞` to the stationary chain `contractLimit ℓ`, and
`f(X^{h_ℓ}_∞)` is integrable;
(2) the level means converge, `E[f(X^{(ℓ)})] → P`, and also `E[f(X^{h_ℓ}_∞)] → P`;
(3) there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and sample sizes `M_ℓ ≥ 1`
for which the multilevel estimator
`∑_{ℓ ≤ L} M_ℓ⁻¹ ∑_{n < M_ℓ} (f(X^f_ℓ) − f(X^c_{ℓ−1}))(z^{(ℓ,n)})` (with `f(X^c_{−1}) ≡ 0` and
independent copies `z^{(ℓ,n)}` of the normal sequence) has a square-integrable error with mean
square `< ε²` about `P`, at cost `∑_{ℓ ≤ L} M_ℓ N_ℓ ≤ c₄ ε⁻² |log ε|³` (instead of
`c₄ ε^{−2−2η}`, `η > 0`, in `contracting_levels_mlmc`).
(1) and (2) are those of `contracting_levels_mlmc`.  For (3), `giles_theorem1_fineCoarse_log` is
applied with `α = 1/2` and `β = 1` (as in `contracting_levels_mlmc`), `γ = 1` and the logarithmic
exponent `1`, since `N_ℓ ≤ m (ℓ + 1) 2^ℓ`: the case `β = γ` gives `ε⁻² |log ε|^{2+1}`.  For an
estimator whose bias, variances and costs attain these rates, the exponent `3` cannot be lowered
(`mlmc_cost_lower_log`).  Deviations as in `contracting_levels_mlmc` (one dimension, Lipschitz
payoff, the cost of a sample counted as the `N_ℓ` steps of its fine path, `β = 1` not sharp for
additive noise, `P` not identified with the mean under the invariant law of the SDE). -/
theorem contracting_levels_mlmc_log (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hδ : 0 < δ) {h₀ : ℝ}
    (hh₀ : 0 < h₀) (hmargin : (Kb : ℝ) ^ 2 + (Ka : ℝ) ^ 2 * h₀ + δ ≤ 2 * κ) (x₀ : ℝ)
    {N : ℕ → ℕ} (hN : ∀ ℓ, 2 * N ℓ ≤ N (ℓ + 1)) {c : ℝ} (hc : 8 * Real.log 2 ≤ c * δ)
    (hT : ∀ ℓ : ℕ, c * ℓ ≤ N ℓ * (h₀ / 2 ^ ℓ)) {m : ℕ}
    (hNm : ∀ ℓ, N ℓ ≤ m * (ℓ + 1) * 2 ^ ℓ) {f : ℝ → ℝ} {Kf : ℝ≥0} (hf : LipschitzWith Kf f) :
    (∀ ℓ, Integrable (fun z => f (contractPath a b h₀ x₀ N ℓ z)) stdNormalSeq ∧
      (∀ᵐ z ∂stdNormalSeq, Tendsto (fun n => backIter (emStep a b (h₀ / 2 ^ ℓ)) n
        (fun k => Real.sqrt (h₀ / 2 ^ ℓ) * z k) x₀) atTop (𝓝 (contractLimit a b h₀ x₀ ℓ z))) ∧
      Integrable (fun z => f (contractLimit a b h₀ x₀ ℓ z)) stdNormalSeq) ∧
    ∃ P : ℝ, Tendsto (fun ℓ => ∫ z, f (contractPath a b h₀ x₀ N ℓ z) ∂stdNormalSeq) atTop
        (𝓝 P) ∧
      Tendsto (fun ℓ => ∫ z, f (contractLimit a b h₀ x₀ ℓ z) ∂stdNormalSeq) atTop (𝓝 P) ∧
      ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (M : ℕ → ℕ), (∀ ℓ, 0 < M ℓ) ∧
          Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ z => f (contractPath a b h₀ x₀ N ℓ z))
              (fun ℓ z => f (contractPath a b h₀ x₀ N ℓ (pairAvg z)))) (fun p x => x p) ℓ
                (M ℓ) x - P) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ z => f (contractPath a b h₀ x₀ N ℓ z))
              (fun ℓ z => f (contractPath a b h₀ x₀ N ℓ (pairAvg z)))) (fun p x => x p) ℓ
                (M ℓ) x - P) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
          ∫ x, totalCost (fun ℓ _ _ => (N ℓ : ℝ)) L M x
              ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ≤
            c₄ * (ε ^ (-2 : ℝ) * |Real.log ε| ^ 3) := by
  -- (1) and (2), with the limit `P`, from `contracting_levels_mlmc` (with `η = 1`)
  obtain ⟨hlev, P, hP, hlimP, -⟩ :=
    contracting_levels_mlmc ha hb hdiss hδ hh₀ hmargin x₀ hN hc hT hNm hf one_pos
  refine ⟨hlev, P, hP, hlimP, ?_⟩
  -- the level approximations
  obtain ⟨Pf, hPfdef⟩ : ∃ Pf : ℕ → (ℕ → ℝ) → ℝ,
      Pf = fun ℓ z => f (contractPath a b h₀ x₀ N ℓ z) := ⟨_, rfl⟩
  obtain ⟨Pc, hPcdef⟩ : ∃ Pc : ℕ → (ℕ → ℝ) → ℝ,
      Pc = fun ℓ z => f (contractPath a b h₀ x₀ N ℓ (pairAvg z)) := ⟨_, rfl⟩
  have hfm : Measurable f := hf.continuous.measurable
  have hPfm : ∀ ℓ, Measurable (Pf ℓ) := fun ℓ => by
    rw [hPfdef]
    exact hfm.comp (measurable_contractPath ha hb h₀ x₀ N ℓ)
  have hPcPf : ∀ ℓ, Pc ℓ = Pf ℓ ∘ pairAvg := fun ℓ => by
    rw [hPcdef, hPfdef]
    rfl
  have hPcm : ∀ ℓ, Measurable (Pc ℓ) := fun ℓ => by
    rw [hPcPf]
    exact (hPfm ℓ).comp measurePreserving_pairAvg.measurable
  have hPf : ∀ ℓ, MemLp (Pf ℓ) 2 stdNormalSeq := fun ℓ => by
    rw [hPfdef]
    exact (memLp_contractPath ha hb hdiss hδ hh₀ hmargin x₀ N hf ℓ).1
  have hPc : ∀ ℓ, MemLp (Pc ℓ) 2 stdNormalSeq := fun ℓ => by
    rw [hPcPf]
    exact (hPf ℓ).comp_measurePreserving measurePreserving_pairAvg
  have h24 : ∀ ℓ, ∫ z, Pf ℓ z ∂stdNormalSeq = ∫ z, Pc ℓ z ∂stdNormalSeq := fun ℓ => by
    rw [hPcPf]
    exact (integral_comp_of_measurePreserving measurePreserving_pairAvg
      (hPfm ℓ).aestronglyMeasurable).symm
  -- the constants (the coupling constants at `H = h₀/2`, the largest fine step)
  have hh₀2 : 0 ≤ h₀ / 2 := by positivity
  have hC₁ := contractC1_nonneg a b Ka Kb hδ hh₀2 x₀
  have hC₂ := contractC2_nonneg a b Ka Kb hδ hh₀2 x₀
  have hM₀ := contractM_nonneg a b Ka Kb hδ hh₀.le x₀
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (Kf : ℝ) ^ 2 *
      (contractC1 a b Ka Kb δ (h₀ / 2) x₀ * h₀ + 2 * contractC2 a b Ka Kb δ (h₀ / 2) x₀) :=
    ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  -- the second moments of the corrections decay like `2^{−ℓ}`
  have hsq : ∀ ℓ : ℕ, ∫ z, (Pf (ℓ + 1) z - Pc ℓ z) ^ 2 ∂stdNormalSeq ≤
      B * (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) := fun ℓ => by
    rw [hPfdef, hPcdef, hB, mul_assoc]
    exact (integral_sq_contractDiff_le ha hb hdiss hδ hh₀ hmargin x₀ hf ℓ (hN ℓ)).trans
      (mul_le_mul_of_nonneg_left (contract_bound_le_two_pow hC₂ hδ hc ℓ (hT ℓ)) (sq_nonneg _))
  -- consecutive level means differ by at most `√B r^ℓ`, `r = 2^{−1/2}`
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  have hr2 : ∀ ℓ : ℕ, (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) ≤ (r ^ ℓ) ^ 2 := fun ℓ => by
    have hr2' : r ^ 2 = 2⁻¹ := by
      rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
      norm_num
    have e1 : (r ^ ℓ) ^ 2 = (2 ^ ℓ)⁻¹ := by
      rw [← pow_mul, mul_comm, pow_mul, hr2', inv_pow]
    rw [e1, Real.rpow_neg zero_le_two, Real.rpow_natCast, pow_succ]
    apply inv_anti₀ (by positivity)
    have : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    linarith
  have hmean : ∀ ℓ : ℕ, dist (∫ z, Pf ℓ z ∂stdNormalSeq) (∫ z, Pf (ℓ + 1) z ∂stdNormalSeq) ≤
      Real.sqrt B * r ^ ℓ := fun ℓ => by
    have hY : MemLp (fun z => Pf (ℓ + 1) z - Pc ℓ z) 2 stdNormalSeq := (hPf (ℓ + 1)).sub (hPc ℓ)
    have hvar := variance_nonneg (fun z => Pf (ℓ + 1) z - Pc ℓ z) stdNormalSeq
    rw [variance_eq_sub hY] at hvar
    simp only [Pi.pow_apply] at hvar
    have hsub : ∫ z, (Pf (ℓ + 1) z - Pc ℓ z) ∂stdNormalSeq =
        ∫ z, Pf (ℓ + 1) z ∂stdNormalSeq - ∫ z, Pc ℓ z ∂stdNormalSeq :=
      integral_sub ((hPf _).integrable one_le_two) ((hPc _).integrable one_le_two)
    rw [Real.dist_eq, abs_sub_comm, h24 ℓ, ← hsub]
    apply abs_le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, Real.sq_sqrt hB0]
    have := mul_le_mul_of_nonneg_left (hr2 ℓ) hB0
    linarith [hsq ℓ]
  have hP' : Tendsto (fun ℓ => ∫ z, Pf ℓ z ∂stdNormalSeq) atTop (𝓝 P) := by
    rw [hPfdef]
    exact hP
  have hrpow : ∀ ℓ : ℕ, r ^ ℓ = (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) := fun ℓ => by
    rw [hrdef, show -(1 / 2 * (ℓ : ℝ)) = -(1 / 2) * (ℓ : ℝ) by ring,
      Real.rpow_mul_natCast zero_le_two]
  -- Theorem 1 with the logarithmic factor: `α = 1/2`, `β = γ = 1`, logarithmic exponent `1`
  obtain ⟨hprob, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  obtain ⟨c₄, hc₄, H⟩ := giles_theorem1_fineCoarse_log (μ := Measure.infinitePi fun _ : ℕ × ℕ =>
      stdNormalSeq) (ν := stdNormalSeq) (fun _ => P) Pf Pc (fun p x => x p)
    (fun ℓ _ _ => (N ℓ : ℝ)) (fun ℓ => (N ℓ : ℝ)) (α := 1 / 2) (β := 1) (γ := 1) (κ := 1)
    (c₁ := Real.sqrt B / (1 - r) + 1) (c₂ := (Kf : ℝ) ^ 2 * contractM a b Ka Kb δ h₀ x₀ + B + 1)
    (c₃ := (m : ℝ) + 1) (by norm_num) one_pos zero_le_one
    (by have : 0 < 1 - r := by linarith
        positivity)
    (by positivity) (by positivity)
    (by norm_num) hω hind (integrable_const P) hPfm hPcm hPf hPc h24
    (fun _ _ => integrable_const _)
    (fun ℓ _ => by rw [integral_const, probReal_univ, one_smul])
    (fun ℓ => by
      have hd := dist_le_of_le_geometric_of_tendsto r _ hr1 hmean hP' ℓ
      rw [Real.dist_eq] at hd
      rw [integral_sub ((hPf ℓ).integrable one_le_two) (integrable_const P), integral_const,
        probReal_univ, one_smul, ← hrpow ℓ]
      have h1r : 0 < 1 - r := by linarith
      calc |∫ z, Pf ℓ z ∂stdNormalSeq - P| ≤ Real.sqrt B * r ^ ℓ / (1 - r) := hd
        _ = Real.sqrt B / (1 - r) * r ^ ℓ := by ring
        _ ≤ (Real.sqrt B / (1 - r) + 1) * r ^ ℓ :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0 ℓ))
    (fun ℓ => by
      cases ℓ with
      | zero =>
        have hv0 := variance_le_expectation_sq (μ := stdNormalSeq)
          ((hPfm 0).sub_const (f x₀)).aestronglyMeasurable
        rw [variance_sub_const (hPfm 0).aestronglyMeasurable] at hv0
        simp only [Pi.pow_apply] at hv0
        have h0 : ∫ z, (Pf 0 z - f x₀) ^ 2 ∂stdNormalSeq ≤
            (Kf : ℝ) ^ 2 * contractM a b Ka Kb δ h₀ x₀ := by
          rw [hPfdef]
          exact (memLp_contractPath ha hb hdiss hδ hh₀ hmargin x₀ N hf 0).2
        show variance (Pf 0) stdNormalSeq ≤ _
        rw [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one]
        linarith
      | succ ℓ =>
        have hm : Measurable fun z => Pf (ℓ + 1) z - Pc ℓ z := (hPfm _).sub (hPcm _)
        have hv := variance_le_expectation_sq (μ := stdNormalSeq) hm.aestronglyMeasurable
        simp only [Pi.pow_apply] at hv
        show variance (fun z => Pf (ℓ + 1) z - Pc ℓ z) stdNormalSeq ≤ _
        have hp : 0 ≤ (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) := by positivity
        rw [one_mul]
        have : (Kf : ℝ) ^ 2 * contractM a b Ka Kb δ h₀ x₀ * (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) +
            (2 : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) ≥ 0 := by positivity
        nlinarith [hsq ℓ])
    (fun ℓ => by
      have h1 : (N ℓ : ℝ) ≤ m * ((ℓ : ℝ) + 1) * 2 ^ ℓ := by exact_mod_cast hNm ℓ
      rw [Real.rpow_one, one_mul, Real.rpow_natCast]
      have h2 : (0 : ℝ) ≤ ((ℓ : ℝ) + 1) * 2 ^ ℓ := by positivity
      nlinarith)
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, M, hM, hmse, hcost⟩ := H ε hε hε1
  subst hPfdef hPcdef
  refine ⟨L, M, hM, ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω
    (memLp_fineCoarseDiff hPf hPc) ℓ (M ℓ)).sub (memLp_const P)).integrable_sq, ?_, ?_⟩
  · rw [integral_const, probReal_univ, one_smul] at hmse
    exact hmse
  · rw [complexityBoundLog_of_eq rfl, show (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at hcost
    exact hcost

end levels

end MLMC
