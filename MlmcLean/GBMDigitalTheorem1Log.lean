import MlmcLean.Theorem1Log
import MlmcLean.GBMDigitalTheorem1
import MlmcLean.GBMDigitalEndpoint

/-!
# Theorem 1 with logarithmic factors in the rates; the digital option at cost `O(ε^{−3} |log ε|)`
(Giles 2015, §2.1 and §5.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1, Theorem 1
(pp. 6–7, l. 271–299 of `docs/giles2015.txt`): "If there exist independent estimators `Y_ℓ` based
on `N_ℓ` Monte Carlo samples, each with expected cost `C_ℓ` and variance `V_ℓ`, and positive
constants `α, β, γ, c₁, c₂, c₃` such that `α ≥ ½ min(β, γ)` and i) `|E[P_ℓ − P]| ≤ c₁ 2^{−αℓ}`
… iii) `V_ℓ ≤ c₂ 2^{−βℓ}` iv) `C_ℓ ≤ c₃ 2^{γℓ}`, then there exists a positive constant `c₄` such
that for any `ε < e⁻¹` there are values `L` and `N_ℓ` for which the multilevel estimator … has a
mean-square-error with bound `MSE ≡ E[(Y − E[P])²] < ε²` with a computational complexity `C`
with bound `E[C] ≤ … c₄ ε^{−2−(γ−β)/α}, β < γ`" (l. 273–299); and §5.1, p. 33, l. 1435–1449, the
digital option `P(S) ≡ 10 exp(−rT) H(S_T − K)` (p. 30, l. 1356–1358) for geometric Brownian
motion with the Euler–Maruyama scheme: "noting that the strong error is `O(h_ℓ^{1/2})`, and there
is a bounded density of paths terminating in the neighbourhood of `K`, there is therefore an
`O(h_ℓ^{1/2})` fraction of the samples with the coarse and fine paths on either side of the
strike, with `P_ℓ−P_{ℓ−1} = ±1`. This gives `V_ℓ = O(h^{1/2})` … Consequently, this application
has `α = 1`, `β = ½`, `γ = 1`, leading to the MLMC complexity being `O(ε^{−2.5})`."

**Theorem 1 with logarithmic factors in conditions i) and iii)** (not stated in the paper).  In the
case `β < γ`, with `α, γ, c₁, c₂, c₃ > 0`, `a, b ≥ 0`, `α ≥ ½ min(β, γ)` and

  i'')   `|E[P_ℓ − P]| ≤ c₁ (ℓ + 1)^a 2^{−αℓ}`,
  iii'') `V_ℓ ≤ c₂ (ℓ + 1)^b 2^{−βℓ}`,
  iv)    `C_ℓ ≤ c₃ 2^{γℓ}`,

there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with `MSE < ε²`
and `E[C] ≤ c₄ ε^{−2−(γ−β)/α} |log ε|^k`, where

  `k = max(b + a(γ − β)/α, aγ/α)`.

For `h_ℓ = h₀ 2^{−ℓ}`, `(ℓ + 1) log 2 = log(2h₀/h_ℓ)`, so the factors `(ℓ + 1)^a`, `(ℓ + 1)^b` are
powers of `log(1/h_ℓ)` up to constants, as in the "`O(h^{1/2} log h)`" of Table 5.2 (l. 1431).
`MlmcLean.Theorem1Log` puts the factor `(ℓ + 1)^κ` into condition iv) instead.

**The exponent `k`.**  The finest level is the least `L` with `c₁ (L + 1)^a 2^{−αL} ≤ ε/2`
(`exists_level_logRate`); then `L + 1 ≤ K₂ |log ε|`, and the paper's "`2^{−αL} = O(ε)`"
(p. 7, l. 326, used as `2^{αL} = O(ε⁻¹)`) becomes `2^{αL} ≤ K₁ |log ε|^a / ε`.  The sample sizes
are the rounded-up Lagrange allocation (§1.3, p. 4, l. 174: "`N_ℓ = μ √(V_ℓ/C_ℓ)`") for the
variance target `ε²/2` (p. 7, l. 313–318), which costs at most
`2ε⁻² (∑_{ℓ ≤ L} √(V_ℓ C_ℓ))² + ∑_{ℓ ≤ L} C_ℓ`.  On the levels `ℓ ≤ L`,
`√(V_ℓ C_ℓ) ≤ √(c₂ c₃) (L + 1)^{b/2} 2^{(γ−β)ℓ/2}`, so the first term is
`O(ε⁻² (L + 1)^b 2^{(γ−β)L}) = O(ε^{−2−(γ−β)/α} |log ε|^{b + a(γ−β)/α})`; the rounding-up overhead
is `O(2^{γL}) = O(ε^{−γ/α} |log ε|^{aγ/α})`, and `ε^{−γ/α} ≤ ε^{−2−(γ−β)/α}` as `β ≤ 2α`.

**The digital option.**  `gbm_em_exact_mismatch_le` (`MlmcLean.GBMDigitalEndpoint`) bounds the
probability that the level-`ℓ` Euler–Maruyama path and the exact solution `S_T` (driven by the
same increments) end on different sides of `K` by `C (h_ℓ (ℓ + 1))^{1/2}`, `h_ℓ = T 2^{−ℓ}`,
uniformly in `S_0` and `K`; since `|E[1_{Ŝ_ℓ > K}] − P(S_T > K)|` is at most
that probability, this is the weak error (`gbm_em_digital_weak_endpoint`), i.e. condition i'')
with `α = a = ½`.  `gbm_em_digital_endpoint` is condition iii'') with `β = b = ½`, and a level-`ℓ`
sample costs `2^ℓ` (`γ = 1`).  So `−2 − (γ − β)/α = −3` and `k = max(½ + ½, 1) = 1`:
`gbm_em_digital_theorem1_log` gives `MSE < ε²` at cost `∑_{ℓ ≤ L} N_ℓ 2^ℓ ≤ c₄ ε⁻³ |log ε|` for
`0 < ε < e⁻¹`, for the estimator, the probability space and the target
`P(S_T > K) = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} dN(0,1)(w)` of `gbm_em_digital_theorem1`; this
removes the loss `η > 0` of its cost `O(ε^{−3−η})`.

**Sharpness of `ε⁻³ |log ε|` for these rates (heuristic, not formalised).**  If the bias and
the variances are of exact order `(ℓ + 1)^{1/2} 2^{−ℓ/2}`, then `MSE ≤ ε²` forces
`(L + 1)^{1/2} 2^{−L/2} ≲ ε`, hence `2^L ≳ ε⁻² |log ε|`, and the finest level alone needs
`N_L ≥ V_L ε⁻²` samples of cost `2^L`, so it costs `≳ ε⁻² (L + 1)^{1/2} 2^{L/2} ≳ ε⁻³ |log ε|`.
So `k = 1` is the best exponent that these rates allow; a lower cost needs better rates (such as
the paper's `α = 1`).

**What is not proved.**  The paper's weak order `α = 1` of Euler–Maruyama for the digital option
(a result of Bally–Talay type for non-smooth payoffs, not cited in the paper; out of scope here),
and hence its `O(ε^{−2.5})` (Theorem 1 with `α = 1`, `β = ½`, `γ = 1`: `ε^{−2−(1−½)/1}`).  Here the
weak error is bounded by the mismatch probability, i.e. by `E[|1_{Ŝ_ℓ > K} − 1_{S_T > K}|]`, which
does not see the cancellation behind `α = 1` and for which only `O((h log(1/h))^{1/2})` is proved:
`α = ½` up to the logarithm.  `ε⁻³ |log ε|` is the best cost this estimator gives when the weak
error is bounded by the mismatch probability.
Also not proved: the observed `V_ℓ = O(h_ℓ^{1/2})` without the logarithm (Table 5.2, l. 1431),
and the cases `β ≥ γ` of the variant of Theorem 1.

**Deviations.**  The variant of Theorem 1 is stated only for `β < γ` (the case of the digital
option); Giles' hypothesis `β > 0` is not needed and is dropped.  The exponent `k` is the one the
proof gives; for `β < 2α` the overhead is of lower order and `k = b + a(γ − β)/α` would also do
(with another constant); for the digital option both terms of the maximum equal `1`.  For GBM the
deviations are those of `gbm_em_digital_theorem1`: `σ ≠ 0` and `T > 0`, the factor `10 e^{−rT}` of
the payoff is omitted, the coarse path of a sample is driven by the summed increments (`pairAvg`)
and a level-`ℓ` sample costs `2^ℓ` (its number of fine steps).  The constant `c₄` depends on
`r, σ, T, s₀, K` (on `s₀` and `K` only through `V[1_{Ŝ_0 > K}]`).

**Results.**
* `exists_level_logRate`, `mlmc_complexity_core_logRates` — the choice of `L` and the
  deterministic core;
* `giles_theorem1_logRates`, `giles_theorem1_fineCoarse_logRates` — the variant of Theorem 1 on a
  probability space, and for fine and coarse approximations satisfying (2.4) with independent
  inputs;
* `gbm_em_digital_weak_endpoint` — the mismatch with the exact solution and the weak error of the
  digital option, `O((h_ℓ (ℓ + 1))^{1/2})`;
* `theorem1_pairAvg_of_sqrtLog_rate`, `gbm_em_digital_theorem1_log` — Theorem 1 end to end for the
  digital option with Euler–Maruyama at cost `O(ε⁻³ |log ε|)`.
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace MLMC

/-! ### The finest level and the deterministic core -/

/-- **The finest level when the bias bound carries a factor `(ℓ + 1)^a`** (a step of this
formalisation's proof of the variant of Giles 2015, §2.1, Theorem 1, pp. 6–7, with condition i)
relaxed to `|E[P_ℓ − P]| ≤ c₁ (ℓ + 1)^a 2^{−αℓ}`; p. 7, l. 313–314: "`L` is chosen so that
`(E[Y]−E[P])² < ½ε²`", and l. 326: "Because of condition i), we have `2^{−αL} = O(ε)`").  For
`α, c₁ > 0` and `a ≥ 0` there are `K₁, K₂ > 0` such that for every `0 < ε < e⁻¹` some `L` has
`c₁ (L + 1)^a 2^{−αL} ≤ ε/2`, `2^{αL} ≤ K₁ |log ε|^a / ε` and `L + 1 ≤ K₂ |log ε|`.  `L` is the
least level with the first property.  One exists: with `(ℓ + 1)^a ≤ A 2^{αℓ/2}`
(`succ_rpow_le_two_rpow`), the level of `exists_L_N` for the rate `α/2` and the constant `c₁ A`
has the property and `L + 1 ≤ K₂ |log ε|`, `K₂ = K2 (α/2) (c₁ A) ≥ 1`.  By minimality, if `L ≥ 1`
then `c₁ L^a 2^{−α(L−1)} > ε/2`, which gives the second bound with
`K₁ = 2^α (1 + 2c₁) K₂^a ≥ 1` (for `L = 0`, `1 ≤ K₁ |log ε|^a / ε` as `ε < 1 ≤ |log ε|`). -/
lemma exists_level_logRate {α a c₁ : ℝ} (hα : 0 < α) (ha : 0 ≤ a) (hc₁ : 0 < c₁) :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ L : ℕ, c₁ * ((L : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (L : ℝ))) ≤ ε / 2 ∧
        (2 : ℝ) ^ (α * (L : ℝ)) ≤ K₁ * |Real.log ε| ^ a / ε ∧
        (L : ℝ) + 1 ≤ K₂ * |Real.log ε| := by
  obtain ⟨A, hA, hpoly⟩ := succ_rpow_le_two_rpow a (half_pos hα)
  have hK₂1 : 1 ≤ K2 (α / 2) (c₁ * A) := by
    unfold K2
    have : 0 ≤ (|Real.log (2 * (c₁ * A))| + 1) / (α / 2 * Real.log 2) := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      positivity
    linarith
  have hK₂ : 0 < K2 (α / 2) (c₁ * A) := by linarith
  have hK₂a : 1 ≤ K2 (α / 2) (c₁ * A) ^ a := Real.one_le_rpow hK₂1 ha
  have hK₁ : 1 ≤ (2 : ℝ) ^ α * (1 + 2 * c₁) * K2 (α / 2) (c₁ * A) ^ a := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ α := Real.one_le_rpow one_le_two hα.le
    have h2 : (1 : ℝ) ≤ 1 + 2 * c₁ := by linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hK₂a
  refine ⟨(2 : ℝ) ^ α * (1 + 2 * c₁) * K2 (α / 2) (c₁ * A) ^ a, K2 (α / 2) (c₁ * A),
    by linarith, hK₂, fun ε hε hε1 => ?_⟩
  have hlog : |Real.log ε| = -Real.log ε := abs_of_neg (Real.log_neg hε (eps_lt_one hε1))
  have hΛ1 : 1 ≤ |Real.log ε| := by rw [hlog]; exact one_le_neg_log hε hε1
  have hε1' : ε < 1 := eps_lt_one hε1
  -- a level that is admissible for the rate `α/2`
  obtain ⟨L', -, -, hb', -, -, -, hL'⟩ := exists_L_N (β := 0) (γ := 0) (c₂ := 1) (c₃ := 1)
    (half_pos hα) (mul_pos hc₁ hA) one_pos one_pos hε hε1
  have hb'' : c₁ * A * (2 : ℝ) ^ (-(α / 2 * (L' : ℝ))) ≤ ε / 2 := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    calc _ ≤ ε ^ 2 / 4 := hb'
      _ = (ε / 2) ^ 2 := by ring
  have hadm : c₁ * ((L' : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (L' : ℝ))) ≤ ε / 2 := by
    refine le_trans ?_ hb''
    have e : (2 : ℝ) ^ (α / 2 * (L' : ℝ)) * (2 : ℝ) ^ (-(α * (L' : ℝ))) =
        (2 : ℝ) ^ (-(α / 2 * (L' : ℝ))) := by
      rw [← Real.rpow_add two_pos]
      congr 1
      ring
    calc c₁ * ((L' : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (L' : ℝ)))
        ≤ c₁ * (A * (2 : ℝ) ^ (α / 2 * (L' : ℝ))) * (2 : ℝ) ^ (-(α * (L' : ℝ))) := by
          gcongr
          exact hpoly L'
      _ = c₁ * A * ((2 : ℝ) ^ (α / 2 * (L' : ℝ)) * (2 : ℝ) ^ (-(α * (L' : ℝ)))) := by ring
      _ = c₁ * A * (2 : ℝ) ^ (-(α / 2 * (L' : ℝ))) := by rw [e]
  have hex : ∃ L : ℕ, c₁ * ((L : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (L : ℝ))) ≤ ε / 2 :=
    ⟨L', hadm⟩
  classical
  have hLL' : Nat.find hex ≤ L' := Nat.find_min' hex hadm
  have hLle : ((Nat.find hex : ℕ) : ℝ) + 1 ≤ K2 (α / 2) (c₁ * A) * |Real.log ε| := by
    rw [hlog]
    have : ((Nat.find hex : ℕ) : ℝ) ≤ L' := by exact_mod_cast hLL'
    linarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, hLle⟩
  -- the minimality of the level bounds `2^{αL}`
  rw [le_div_iff₀ hε]
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h0 | hs
  · rw [h0, Nat.cast_zero, mul_zero, Real.rpow_zero]
    calc 1 * ε ≤ 1 := by linarith
      _ ≤ (2 : ℝ) ^ α * (1 + 2 * c₁) * K2 (α / 2) (c₁ * A) ^ a * |Real.log ε| ^ a :=
          one_le_mul_of_one_le_of_one_le hK₁ (Real.one_le_rpow hΛ1 ha)
  · set n := Nat.pred (Nat.find hex) with hn
    have hnot := Nat.find_min hex (show n < Nat.find hex by omega)
    rw [not_le] at hnot
    have hxy : (2 : ℝ) ^ (α * (n : ℝ)) * (2 : ℝ) ^ (-(α * (n : ℝ))) = 1 := by
      rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
    have h1 : ε / 2 * (2 : ℝ) ^ (α * (n : ℝ)) ≤ c₁ * ((n : ℝ) + 1) ^ a := by
      have := mul_lt_mul_of_pos_right hnot (Real.rpow_pos_of_pos two_pos (α * (n : ℝ)))
      calc ε / 2 * (2 : ℝ) ^ (α * (n : ℝ))
          ≤ c₁ * ((n : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (n : ℝ))) * (2 : ℝ) ^ (α * (n : ℝ)) :=
            this.le
        _ = c₁ * ((n : ℝ) + 1) ^ a *
            ((2 : ℝ) ^ (α * (n : ℝ)) * (2 : ℝ) ^ (-(α * (n : ℝ)))) := by ring
        _ = c₁ * ((n : ℝ) + 1) ^ a := by rw [hxy, mul_one]
    have hcast : ((Nat.find hex : ℕ) : ℝ) = (n : ℝ) + 1 := by
      rw [hs]
      push_cast
      ring
    have hn1 : (n : ℝ) + 1 ≤ K2 (α / 2) (c₁ * A) * |Real.log ε| := by
      rw [← hcast]
      linarith
    have hpow : ((n : ℝ) + 1) ^ a ≤ K2 (α / 2) (c₁ * A) ^ a * |Real.log ε| ^ a := by
      rw [← Real.mul_rpow hK₂.le (abs_nonneg _)]
      exact Real.rpow_le_rpow (by positivity) hn1 ha
    have e2 : (2 : ℝ) ^ (α * ((Nat.find hex : ℕ) : ℝ)) =
        (2 : ℝ) ^ α * (2 : ℝ) ^ (α * (n : ℝ)) := by
      rw [hcast, ← Real.rpow_add two_pos]
      congr 1
      ring
    rw [e2]
    have hP : 0 ≤ K2 (α / 2) (c₁ * A) ^ a * |Real.log ε| ^ a := by positivity
    have h2a : (0 : ℝ) < 2 ^ α := Real.rpow_pos_of_pos two_pos α
    calc (2 : ℝ) ^ α * (2 : ℝ) ^ (α * (n : ℝ)) * ε
        = (2 : ℝ) ^ α * (2 * (ε / 2 * (2 : ℝ) ^ (α * (n : ℝ)))) := by ring
      _ ≤ (2 : ℝ) ^ α * (2 * (c₁ * (K2 (α / 2) (c₁ * A) ^ a * |Real.log ε| ^ a))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (h1.trans (mul_le_mul_of_nonneg_left hpow hc₁.le)) two_pos.le) h2a.le
      _ ≤ (2 : ℝ) ^ α * ((1 + 2 * c₁) * (K2 (α / 2) (c₁ * A) ^ a * |Real.log ε| ^ a)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) h2a.le
      _ = _ := by ring

/-- **Theorem 1 with logarithmic factors in the bias and the variance, case `β < γ` —
deterministic core** (a step of this formalisation's proof of a variant of Giles 2015, §2.1,
Theorem 1, pp. 6–7, l. 271–299, case "`E[C] ≤ c₄ ε^{−2−(γ−β)/α}`, `β < γ`", l. 299; not stated in
the paper).  Let `α, γ, c₁, c₂, c₃ > 0`, `a, b ≥ 0`, `β < γ` and `α ≥ ½ min(β, γ)`.  There is
`c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with
`(c₁ (L + 1)^a 2^{−αL})² + ∑_{ℓ ≤ L} c₂ (ℓ + 1)^b 2^{−βℓ} / N_ℓ < ε²` and
`∑_{ℓ ≤ L} N_ℓ c₃ 2^{γℓ} ≤ c₄ ε^{−2−(γ−β)/α} |log ε|^k`, `k = max(b + a(γ − β)/α, aγ/α)`.
The proof follows Giles' sketch (p. 7, l. 309–318: "the cost on level `ℓ` is proportional to
`2^{(γ−β)ℓ/2}`. The result then follows from the requirement that `L` is chosen so that
`(E[Y]−E[P])² < ½ε²`, and the constant of proportionality for `N_ℓ` is chosen so that
`V[Y] < ½ε²` … the optimal value is rounded up to the nearest integer"): `L` from
`exists_level_logRate` (bias `≤ ε/2`, `2^{αL} ≤ K₁ |log ε|^a / ε`, `L + 1 ≤ K₂ |log ε|`), `N_ℓ`
the rounded-up Lagrange allocation (§1.3, p. 4, l. 174) for `V_ℓ = c₂ (ℓ + 1)^b 2^{−βℓ}`,
`C_ℓ = c₃ 2^{γℓ}` and the variance `ε²/2` (`optimalN_variance`, `optimalN_cost`).  The cost is
`≤ 2ε⁻² (∑_{ℓ ≤ L} √(V_ℓ C_ℓ))² + ∑_{ℓ ≤ L} C_ℓ`; with `(ℓ + 1)^b ≤ (L + 1)^b ≤ K₂^b |log ε|^b`
and `2^{(γ−β)L} ≤ (K₁ |log ε|^a / ε)^{(γ−β)/α}` the first term is
`O(ε^{−2−(γ−β)/α} |log ε|^{b + a(γ−β)/α})`, and the overhead is
`O(2^{γL}) = O(ε^{−γ/α} |log ε|^{aγ/α})` (`tail_cost_bound`), with `ε^{−γ/α} ≤ ε^{−2−(γ−β)/α}`
since `β ≤ 2α`.  The constant `c₄` depends only on `α, β, γ, a, b, c₁, c₂, c₃`.  Giles' hypothesis
`β > 0` is not used. -/
theorem mlmc_complexity_core_logRates {α β γ a b c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (hβγ : β < γ) (hαβγ : min β γ / 2 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (c₁ * ((L : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1), c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) / (N ℓ : ℝ) <
            ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) ≤
          c₄ * (ε ^ (-2 - (γ - β) / α) *
            |Real.log ε| ^ max (b + a * (γ - β) / α) (a * γ / α)) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hlev⟩ := exists_level_logRate hα ha hc₁
  have hβα : β / α ≤ 2 := by
    rw [min_eq_left hβγ.le] at hαβγ
    rw [div_le_iff₀ hα]
    linarith
  set r : ℝ := (2 : ℝ) ^ ((γ - β) / 2) with hr_def
  set g : ℝ := (2 : ℝ) ^ γ with hg_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos two_pos _
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by linarith)
  have hr1' : 0 < r - 1 := by linarith
  have hg : 1 < g := Real.one_lt_rpow (by norm_num) hγ
  have hg1 : 0 < g - 1 := by linarith
  have hp : 0 ≤ γ - β := by linarith
  refine ⟨2 * (c₂ * c₃) * K₂ ^ b * (r / (r - 1)) ^ 2 * K₁ ^ ((γ - β) / α) +
    c₃ * (g / (g - 1)) * K₁ ^ (γ / α), by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨L, hbias, hL, hL1⟩ := hlev ε hε hε1
  set Λ := |Real.log ε| with hΛ
  have hlog : Λ = -Real.log ε := abs_of_neg (Real.log_neg hε (eps_lt_one hε1))
  have hΛ1 : 1 ≤ Λ := by rw [hlog]; exact one_le_neg_log hε hε1
  have hΛ0 : 0 < Λ := by linarith
  have hε1' : ε < 1 := eps_lt_one hε1
  have hVpos : ∀ ℓ : ℕ, 0 < c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) :=
    fun ℓ => by positivity
  have hCpos : ∀ ℓ, 0 < Cb γ c₃ ℓ := Cb_pos hc₃
  have hs : (range (L + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
  have hτ : 0 < ε ^ 2 / 2 := by positivity
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ → ℕ, N = optimalN (range (L + 1))
      (fun ℓ : ℕ => c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) (Cb γ c₃)
      (ε ^ 2 / 2) := ⟨_, rfl⟩
  have hvar : ∑ ℓ ∈ range (L + 1),
      c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) / (N ℓ : ℝ) ≤ ε ^ 2 / 2 := by
    rw [hNdef]
    exact optimalN_variance hs (fun ℓ _ => hVpos ℓ) (fun ℓ _ => hCpos ℓ) hτ
  have hcost := optimalN_cost hs (fun ℓ _ => hVpos ℓ) (fun ℓ _ => hCpos ℓ) hτ
  rw [← hNdef] at hcost
  refine ⟨L, N, fun ℓ => by rw [hNdef]; exact optimalN_pos hs hVpos hCpos hτ ℓ, ?_, ?_⟩
  · -- the mean square error: bias² `≤ ε²/4`, variance `≤ ε²/2`
    have h0 : 0 ≤ c₁ * ((L : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (L : ℝ))) := by positivity
    have hb2 : (c₁ * ((L : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 ≤ (ε / 2) ^ 2 :=
      pow_le_pow_left₀ h0 hbias 2
    nlinarith [pow_pos hε 2]
  -- the cost
  show ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ ≤ _
  set S := ∑ ℓ ∈ range (L + 1), r ^ ℓ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => pow_nonneg hr0.le _
  -- `√(V_ℓ C_ℓ) ≤ (L + 1)^{b/2} √(c₂ c₃) r^ℓ` on the levels `ℓ ≤ L`
  have hterm : ∀ ℓ ∈ range (L + 1),
      Real.sqrt (c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) * Cb γ c₃ ℓ) ≤
        Real.sqrt (((L : ℝ) + 1) ^ b) * (Real.sqrt (c₂ * c₃) * r ^ ℓ) := by
    intro ℓ hℓ
    have hℓL : (ℓ : ℝ) ≤ L := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    have h1 : ((ℓ : ℝ) + 1) ^ b ≤ ((L : ℝ) + 1) ^ b :=
      Real.rpow_le_rpow (by positivity) (by linarith) hb
    have e : c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) * Cb γ c₃ ℓ =
        ((ℓ : ℝ) + 1) ^ b * (Vb β c₂ ℓ * Cb γ c₃ ℓ) := by
      unfold Vb
      ring
    have hVC : 0 ≤ Vb β c₂ ℓ * Cb γ c₃ ℓ := (mul_pos (Vb_pos hc₂ ℓ) (hCpos ℓ)).le
    rw [e, ← sqrt_Vb_mul_Cb hc₂ hc₃ ℓ, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h1 hVC)
  have hQ : (∑ ℓ ∈ range (L + 1),
      Real.sqrt (c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) * Cb γ c₃ ℓ)) ^ 2 ≤
        ((L : ℝ) + 1) ^ b * (c₂ * c₃) * S ^ 2 := by
    have h1 := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← hS] at h1
    have h0 : 0 ≤ ∑ ℓ ∈ range (L + 1),
        Real.sqrt (c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) * Cb γ c₃ ℓ) :=
      Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
    calc _ ≤ (Real.sqrt (((L : ℝ) + 1) ^ b) * (Real.sqrt (c₂ * c₃) * S)) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = ((L : ℝ) + 1) ^ b * (c₂ * c₃) * S ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
          ring
  -- `S² ≤ (r/(r − 1))² 2^{(γ−β)L}` and `2^{(γ−β)L} ≤ K₁^{(γ−β)/α} Λ^{a(γ−β)/α} ε^{−(γ−β)/α}`
  have hr2L : r ^ (2 * L) = (2 : ℝ) ^ ((γ - β) * (L : ℝ)) := by
    rw [hr_def, ← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    push_cast
    ring
  have hKΛ : 0 < K₁ * Λ ^ a := by positivity
  have hpowK : ∀ q : ℝ, 0 ≤ q → (K₁ * Λ ^ a) ^ (q / α) = K₁ ^ (q / α) * Λ ^ (a * (q / α)) :=
    fun q hq => by rw [Real.mul_rpow hK₁.le (by positivity), ← Real.rpow_mul hΛ0.le]
  have hS2 : S ^ 2 ≤ (r / (r - 1)) ^ 2 *
      (K₁ ^ ((γ - β) / α) * Λ ^ (a * ((γ - β) / α)) * ε ^ (-((γ - β) / α))) := by
    have h1 := two_rpow_L_le hα hp hKΛ hε hL
    rw [hpowK _ hp] at h1
    calc S ^ 2 ≤ (r ^ L * (r / (r - 1))) ^ 2 :=
          pow_le_pow_left₀ hS0 (geom_sum_le_of_one_lt hr1 L) 2
      _ = (r / (r - 1)) ^ 2 * r ^ (2 * L) := by ring
      _ = (r / (r - 1)) ^ 2 * (2 : ℝ) ^ ((γ - β) * (L : ℝ)) := by rw [hr2L]
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  -- `(L + 1)^b ≤ K₂^b Λ^b`
  have hLb : ((L : ℝ) + 1) ^ b ≤ K₂ ^ b * Λ ^ b := by
    rw [← Real.mul_rpow hK₂.le hΛ0.le]
    exact Real.rpow_le_rpow (by positivity) hL1 hb
  -- the rounding-up overhead
  have hCsum : ∑ ℓ ∈ range (L + 1), Cb γ c₃ ℓ = c₃ * ∑ ℓ ∈ range (L + 1), g ^ ℓ := by
    unfold Cb
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by rw [two_rpow_mul_nat]
  have htail := tail_cost_bound hα hγ hc₃ hKΛ hε L hL
  rw [hpowK _ hγ.le] at htail
  -- the exponents
  have hτinv : (ε ^ 2 / 2)⁻¹ = 2 * ε ^ (-2 : ℝ) := by
    rw [inv_div, ← eps_inv_sq_eq hε, inv_pow]
    ring
  have hexp : ε ^ (-2 : ℝ) * ε ^ (-((γ - β) / α)) = ε ^ (-2 - (γ - β) / α) := by
    rw [show (-2 : ℝ) - (γ - β) / α = -2 + -((γ - β) / α) by ring, Real.rpow_add hε]
  have hεγ : ε ^ (-(γ / α)) ≤ ε ^ (-2 - (γ - β) / α) := by
    apply Real.rpow_le_rpow_of_exponent_ge hε hε1'.le
    have : (γ - β) / α = γ / α - β / α := by ring
    rw [this]
    linarith
  set k := max (b + a * (γ - β) / α) (a * γ / α) with hk
  have hΛk1 : Λ ^ b * Λ ^ (a * ((γ - β) / α)) ≤ Λ ^ k := by
    rw [← Real.rpow_add hΛ0, ← mul_div_assoc]
    exact Real.rpow_le_rpow_of_exponent_le hΛ1 (le_max_left _ _)
  have hΛk2 : Λ ^ (a * (γ / α)) ≤ Λ ^ k := by
    rw [← mul_div_assoc]
    exact Real.rpow_le_rpow_of_exponent_le hΛ1 (le_max_right _ _)
  set E := ε ^ (-2 - (γ - β) / α) with hE
  have hE0 : 0 ≤ E := by positivity
  have hε2 : 0 ≤ ε ^ (-2 : ℝ) := by positivity
  calc ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ
      ≤ (ε ^ 2 / 2)⁻¹ * (∑ ℓ ∈ range (L + 1),
          Real.sqrt (c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) * Cb γ c₃ ℓ)) ^ 2 +
          ∑ ℓ ∈ range (L + 1), Cb γ c₃ ℓ := hcost
    _ ≤ 2 * ε ^ (-2 : ℝ) * ((K₂ ^ b * Λ ^ b) * (c₂ * c₃) * ((r / (r - 1)) ^ 2 *
          (K₁ ^ ((γ - β) / α) * Λ ^ (a * ((γ - β) / α)) * ε ^ (-((γ - β) / α))))) +
          c₃ * (g / (g - 1)) * (K₁ ^ (γ / α) * Λ ^ (a * (γ / α)) * ε ^ (-(γ / α))) := by
        rw [hτinv, hCsum]
        refine add_le_add (mul_le_mul_of_nonneg_left (hQ.trans ?_) (by positivity)) htail
        exact mul_le_mul (mul_le_mul_of_nonneg_right hLb (by positivity)) hS2
          (by positivity) (by positivity)
    _ = 2 * (c₂ * c₃) * K₂ ^ b * (r / (r - 1)) ^ 2 * K₁ ^ ((γ - β) / α) *
          (ε ^ (-2 : ℝ) * ε ^ (-((γ - β) / α))) * (Λ ^ b * Λ ^ (a * ((γ - β) / α))) +
          c₃ * (g / (g - 1)) * K₁ ^ (γ / α) * ε ^ (-(γ / α)) * Λ ^ (a * (γ / α)) := by ring
    _ ≤ 2 * (c₂ * c₃) * K₂ ^ b * (r / (r - 1)) ^ 2 * K₁ ^ ((γ - β) / α) * E * Λ ^ k +
          c₃ * (g / (g - 1)) * K₁ ^ (γ / α) * E * Λ ^ k := by
        rw [hexp]
        gcongr
    _ = _ := by ring

/-! ### The variant of Theorem 1 on a probability space -/

section prob

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The mean-square error from the core inequality, with logarithmic factors** (Giles 2015,
§2.1, (2.1) and (2.3), as in the proof of Theorem 1, p. 7, l. 313–316: "`L` is chosen so that
`(E[Y]−E[P])² < ½ε²`, and the constant of proportionality for `N_ℓ` is chosen so that
`V[Y] < ½ε²`").  Under conditions i''), ii) and iii'') with square-integrable estimators
`Y ℓ n` (`n ≥ 1`), pairwise independent across levels, if `N_ℓ ≥ 1` and
`(c₁ (L + 1)^a 2^{−αL})² + ∑_{ℓ ≤ L} c₂ (ℓ + 1)^b 2^{−βℓ} / N_ℓ < ε²`, then the error of
`Y = ∑_{ℓ ≤ L} Y ℓ (N ℓ)` is square integrable and `E[(Y − E[P])²] < ε²` (`mlmc_mse`). -/
lemma mse_lt_of_core_bound_logRates (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ)
    (V : ℕ → ℝ) {α β a b c₁ c₂ ε : ℝ} {L : ℕ} {N : ℕ → ℕ} (hN : ∀ ℓ, 0 < N ℓ)
    (hcore : (c₁ * ((L : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 +
      ∑ ℓ ∈ range (L + 1), c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) / (N ℓ : ℝ) <
        ε ^ 2)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (h_i : ∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤
      c₁ * ((ℓ : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) :
    Integrable (fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2) μ ∧
      μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 := by
  refine ⟨((memLp_finsetSum _ fun ℓ _ => hY ℓ (N ℓ) (hN ℓ)).sub
    (memLp_const _)).integrable_sq, ?_⟩
  have hind' : Set.Pairwise ↑(range (L + 1)) fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ :=
    fun i _ j _ hij => hind N hN hij
  rw [mlmc_mse Pℓ (fun ℓ => Y ℓ (N ℓ)) L (μ[P]) (fun ℓ => hY ℓ (N ℓ) (hN ℓ)) hPℓ hind'
    (h_ii₀ (N 0) (hN 0)) (fun ℓ => h_ii ℓ (N (ℓ + 1)) (hN (ℓ + 1)))]
  have hb : (μ[Pℓ L] - μ[P]) ^ 2 ≤ (c₁ * ((L : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 := by
    have h := h_i L
    rw [integral_sub (hPℓ L) hP] at h
    exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
  have hv : ∑ ℓ ∈ range (L + 1), variance (Y ℓ (N ℓ)) μ ≤
      ∑ ℓ ∈ range (L + 1), c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) / (N ℓ : ℝ) := by
    apply Finset.sum_le_sum
    intro ℓ _
    rw [h_var ℓ (N ℓ) (hN ℓ)]
    exact div_le_div_of_nonneg_right (h_iii ℓ) (by positivity)
  linarith

/-- **Theorem 1 with logarithmic factors in conditions i) and iii), case `β < γ`** (a variant of
Giles 2015, §2.1, Theorem 1, pp. 6–7, l. 271–299, not stated in the paper: "then there exists a
positive constant `c₄` such that for any `ε < e⁻¹` there are values `L` and `N_ℓ` for which the
multilevel estimator … has a mean-square-error with bound `MSE ≡ E[(Y − E[P])²] < ε²` with a
computational complexity `C` with bound `E[C] ≤ … c₄ ε^{−2−(γ−β)/α}, β < γ`", here with an extra
factor `|log ε|^k`).  Let `P` be integrable, `Pℓ ℓ` integrable level approximations, `Y ℓ n`
square-integrable estimators from `n ≥ 1` samples, pairwise independent across levels for every
choice of sample sizes, with `V[Y ℓ n] = V ℓ / n` and integrable random costs `Cost ℓ n` with
`E[Cost ℓ n] = n C ℓ`, and constants `α, γ, c₁, c₂, c₃ > 0`, `a, b ≥ 0`, `β < γ`,
`α ≥ ½ min(β, γ)` with

  (i'')   `|E[Pℓ ℓ − P]| ≤ c₁ (ℓ + 1)^a 2^{−αℓ}`,
  (ii)    `E[Y 0 n] = E[Pℓ 0]`, `E[Y (ℓ+1) n] = E[Pℓ (ℓ+1) − Pℓ ℓ]` for `n ≥ 1`,
  (iii'') `V ℓ ≤ c₂ (ℓ + 1)^b 2^{−βℓ}`,
  (iv)    `C ℓ ≤ c₃ 2^{γℓ}`.

Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N ℓ ≥ 1` for which
`Y = ∑_{ℓ=0}^{L} Y ℓ (N ℓ)` has a square-integrable error, `MSE = E[(Y − E[P])²] < ε²`, and the
cost `C = ∑_{ℓ=0}^{L} Cost ℓ (N ℓ)` has `E[C] ≤ c₄ ε^{−2−(γ−β)/α} |log ε|^k` with
`k = max(b + a(γ − β)/α, aγ/α)`; for `a = b = 0` this is Giles' bound in the case `β < γ`.
In the proof `c₄` is that of `mlmc_complexity_core_logRates`, which depends only on
`α, β, γ, a, b, c₁, c₂, c₃`; the statement does not record this uniformity.
Giles' hypothesis `β > 0` is dropped; the cases `β ≥ γ` are not treated. -/
theorem giles_theorem1_logRates
    (P : Ω → ℝ) (Pℓ : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (Cost : ℕ → ℕ → Ω → ℝ) (V C : ℕ → ℝ)
    {α β γ a b c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hβγ : β < γ)
    (hαβγ : min β γ / 2 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost_int : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (hCost_mean : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_i : ∀ ℓ : ℕ, |μ[fun ω => Pℓ ℓ ω - P ω]| ≤
      c₁ * ((ℓ : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → μ[Y 0 n] = μ[Pℓ 0])
    (h_ii : ∀ ℓ n, 0 < n → μ[Y (ℓ + 1) n] = μ[fun ω => Pℓ (ℓ + 1) ω - Pℓ ℓ ω])
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2) μ ∧
        μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        μ[fun ω => ∑ ℓ ∈ range (L + 1), Cost ℓ (N ℓ) ω] ≤
          c₄ * (ε ^ (-2 - (γ - β) / α) *
            |Real.log ε| ^ max (b + a * (γ - β) / α) (a * γ / α)) := by
  obtain ⟨c₄, hc₄, hcore⟩ :=
    mlmc_complexity_core_logRates hα hγ hβγ hαβγ ha hb hc₁ hc₂ hc₃
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := hcore ε hε hε1
  obtain ⟨hint, hmse'⟩ :=
    mse_lt_of_core_bound_logRates P Pℓ Y V hN hmse hP hPℓ hY hind h_i h_ii₀ h_ii h_var h_iii
  refine ⟨L, N, hN, hint, hmse', ?_⟩
  -- `E[C] = ∑ N_ℓ C_ℓ`, then condition iv) termwise
  rw [integral_finsetSum _ fun ℓ _ => hCost_int ℓ (N ℓ) (hN ℓ)]
  calc ∑ ℓ ∈ range (L + 1), μ[Cost ℓ (N ℓ)] = ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ :=
        Finset.sum_congr rfl fun ℓ _ => hCost_mean ℓ (N ℓ) (hN ℓ)
    _ ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :=
        Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (h_iv ℓ) (Nat.cast_nonneg _)
    _ ≤ _ := hcost

end prob

/-! ### Different fine and coarse approximations with independent inputs -/

section fineCoarse

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Theorem 1 with logarithmic factors for different fine and coarse approximations, case
`β < γ`** (Giles 2015, §2.1, p. 8, (2.4): "Provided we maintain the identity
`E[P^f_ℓ] = E[P^c_ℓ]` … then condition ii) is satisfied", and Theorem 1, pp. 6–7, l. 271–299,
with conditions i) and iii) relaxed to i'') and iii''); not stated in the paper).  The multilevel
estimator is `Y = ∑_{ℓ=0}^{L} N_ℓ⁻¹ ∑_{n<N_ℓ} (P^f_ℓ − P^c_{ℓ−1})(ω^{(ℓ,n)})`, `P^c_{−1} ≡ 0`,
with mutually independent inputs `ω (ℓ, n)` of law `ν`.  Let the approximations be measurable and
square integrable with (2.4), `P` integrable, the `n`-th level-`ℓ` sample have an integrable cost
of mean `C ℓ`, and (i'') `|E[P^f_ℓ − P]| ≤ c₁ (ℓ + 1)^a 2^{−αℓ}`,
(iii'') `V[P^f_ℓ − P^c_{ℓ−1}] ≤ c₂ (ℓ + 1)^b 2^{−βℓ}`, (iv) `C_ℓ ≤ c₃ 2^{γℓ}` with
`α, γ, c₁, c₂, c₃ > 0`, `a, b ≥ 0`, `β < γ` and `α ≥ ½ min(β, γ)`.  Then there is `c₄ > 0` such
that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with a square-integrable error,
`MSE < ε²` and expected cost `E[C] ≤ c₄ ε^{−2−(γ−β)/α} |log ε|^k`,
`k = max(b + a(γ − β)/α, aγ/α)`.  Proof: `giles_theorem1_logRates` for the block means of the
corrections, transported along `ω (0, 0)`, with condition ii) from (2.4)
(`integral_fineCoarseDiff`), as `giles_theorem1_fineCoarse_log`. -/
theorem giles_theorem1_fineCoarse_logRates [IsProbabilityMeasure μ] (P : Ω₀ → ℝ)
    (Pf Pc : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
    {α β γ a b c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hβγ : β < γ)
    (hαβγ : min β γ / 2 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) (hP : Integrable P ν)
    (hPfm : ∀ ℓ, Measurable (Pf ℓ)) (hPcm : ∀ ℓ, Measurable (Pc ℓ))
    (hPf : ∀ ℓ, MemLp (Pf ℓ) 2 ν) (hPc : ∀ ℓ, MemLp (Pc ℓ) 2 ν)
    (h24 : ∀ ℓ, ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (h_i : ∀ ℓ : ℕ, |∫ y, Pf ℓ y - P y ∂ν| ≤
      c₁ * ((ℓ : ℝ) + 1) ^ a * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, variance (fineCoarseDiff Pf Pc ℓ) ν ≤
      c₂ * ((ℓ : ℝ) + 1) ^ b * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
          blockMean (fineCoarseDiff Pf Pc) ω ℓ (N ℓ) x - ∫ y, P y ∂ν) ^ 2) μ ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf Pc) ω ℓ (N ℓ) x -
          ∫ y, P y ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * (ε ^ (-2 - (γ - β) / α) *
          |Real.log ε| ^ max (b + a * (γ - β) / α) (a * γ / α)) := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  have hPf1 : ∀ ℓ, Integrable (Pf ℓ) ν := fun ℓ => (hPf ℓ).integrable one_le_two
  have hPc1 : ∀ ℓ, Integrable (Pc ℓ) ν := fun ℓ => (hPc ℓ).integrable one_le_two
  have hΔm := measurable_fineCoarseDiff hPfm hPcm
  have hΔ := memLp_fineCoarseDiff hPf hPc
  have hΔ1 : ∀ ℓ, Integrable (fineCoarseDiff Pf Pc ℓ) ν := fun ℓ => (hΔ ℓ).integrable one_le_two
  have h_ii := integral_fineCoarseDiff hPf1 hPc1 h24
  -- transport `P` and `P_ℓ` to `Ω` along the input `ω (0, 0)`
  have hφ := hω (0, 0)
  have tr : ∀ f : Ω₀ → ℝ, Integrable f ν → ∫ x, f (ω (0, 0) x) ∂μ = ∫ y, f y ∂ν :=
    fun f hf => integral_comp_of_measurePreserving hφ hf.aestronglyMeasurable
  have hPμ : Integrable (fun x => P (ω (0, 0) x)) μ :=
    (hφ.integrable_comp hP.aestronglyMeasurable).2 hP
  have hPlμ : ∀ ℓ, Integrable (fun x => Pf ℓ (ω (0, 0) x)) μ :=
    fun ℓ => (hφ.integrable_comp (hPf1 ℓ).aestronglyMeasurable).2 (hPf1 ℓ)
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_logRates (μ := μ) (fun x => P (ω (0, 0) x))
    (fun ℓ x => Pf ℓ (ω (0, 0) x)) (fun ℓ n => blockMean (fineCoarseDiff Pf Pc) ω ℓ n)
    (fun ℓ n x => ∑ k ∈ range n, cost ℓ k x) (fun ℓ => variance (fineCoarseDiff Pf Pc ℓ) ν) C
    hα hγ hβγ hαβγ ha hb hc₁ hc₂ hc₃ hPμ hPlμ (fun ℓ n _ => memLp_blockMean hω hΔ ℓ n)
    (fun N _ i j hij => indepFun_blockMean (fun p => (hω p).measurable) hind hΔm hij _ _)
    (fun ℓ n _ => integrable_finsetSum _ fun k _ => hcost ℓ k)
    (fun ℓ n _ => by
      rw [integral_finsetSum _ fun k _ => hcost ℓ k,
        Finset.sum_congr rfl fun k _ => hcostC ℓ k, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul])
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
  obtain ⟨L, N, hN, hint, hmse, hcost'⟩ := h ε hε hε1
  rw [tr P hP] at hint hmse
  exact ⟨L, N, hN, hint, hmse, hcost'⟩

end fineCoarse

/-! ### The digital option with Euler–Maruyama -/

/-- `√(T 2^{−ℓ} x) = √T x^{1/2} 2^{−ℓ/2}` for `T ≥ 0` (the rate `(h_ℓ (ℓ + 1))^{1/2}`,
`h_ℓ = T 2^{−ℓ}`, of Giles 2015, §5.1, p. 33, l. 1436–1441, "an `O(h_ℓ^{1/2})` fraction of the
samples", up to the logarithm, written in the form `c (ℓ + 1)^{1/2} 2^{−ℓ/2}` of conditions i'')
and iii'')); for `x < 0` both sides are the junk value `0`, and it is used only with `x = ℓ + 1`. -/
lemma sqrt_div_two_pow_mul_eq {T : ℝ} (hT : 0 ≤ T) (ℓ : ℕ) (x : ℝ) :
    Real.sqrt (T / 2 ^ ℓ * x) =
      Real.sqrt T * x ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    div_two_pow_rpow hT]
  ring

/-- **The digital option with Euler–Maruyama: the mismatch with the exact solution and the weak
error are `O((h_ℓ (ℓ + 1))^{1/2})`, uniformly in `S_0` and `K`** (Giles 2015, §5.1, p. 33, l.
1436–1441: "noting that the strong error is `O(h_ℓ^{1/2})`, and there is a bounded density of paths
terminating in the neighbourhood of `K`, there is therefore an `O(h_ℓ^{1/2})` fraction of the
samples with the coarse and fine paths on either side of the strike"; condition i) of Theorem 1,
§2.1, p. 6, l. 277; Table 5.2, l. 1431, analysis "`O(h^{1/2} log h)`", a rate for `V_ℓ`, not for the
weak error).  For GBM with `σ ≠ 0` and `T > 0` there is `C ≥ 0`, depending only on `r`, `σ` and `T`,
such that for every `s₀`, every strike `K` and every level `ℓ` (`2^ℓ` steps of size
`h_ℓ = T 2^{−ℓ}`): `P(1_{S_T > K} ≠ 1_{Ŝ_ℓ > K}) ≤ C (h_ℓ (ℓ + 1))^{1/2}` (`S_T` the exact solution
driven by the same increments) and `|E[1_{Ŝ_ℓ > K}] − E[1_{S_T > K}]| ≤ C (h_ℓ (ℓ + 1))^{1/2}`, with
`E[1_{S_T > K}] = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} dN(0,1)(w)`.  Since
`(ℓ + 1) log 2 = log(2T/h_ℓ)`, this is the weak rate `½` up to `(log(1/h_ℓ))^{1/2}`: condition i'')
with `α = a = ½`; the endpoint `q = ½` of `gbm_em_digital_weak_rate` (every `q < ½`) up to the
logarithm.  Proof: `gbm_em_exact_mismatch_le` with `endpoint_bound_le_sqrt` (bound
`√h_ℓ (A + B (ℓ log 2)^{1/2}) ≤ (A + B) (h_ℓ (ℓ + 1))^{1/2}`, `C = A + B` with `A`, `B` as in
`endpoint_bound_le_sqrt`), the empty mismatch for `s₀ = 0`, and `abs_integral_digital_sub_le`.  The
paper's weak order `α = 1` (l. 1447–1449) is not proved. -/
theorem gbm_em_digital_weak_endpoint (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ K : ℝ) (ℓ : ℕ),
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ z) ≠
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z)} ≤
        C * Real.sqrt (T / 2 ^ ℓ * ((ℓ : ℝ) + 1)) ∧
      |∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ z) ∂stdNormalSeq -
          ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
            (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1| ≤
        C * Real.sqrt (T / 2 ^ ℓ * ((ℓ : ℝ) + 1)) := by
  set D := σ ^ 2 + r ^ 2 * T with hD
  set A := 48 * T * Real.sqrt T * D ^ 2 +
    (T * r ^ 2 + 12 * Real.sqrt T * D * Real.sqrt D) / (|σ| * Real.sqrt (2 * Real.pi)) +
    2 / Real.sqrt T with hA
  set B := 320 * D / (|σ| * Real.sqrt (2 * Real.pi)) with hB
  have hD0 : 0 ≤ D := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  -- the mismatch with the exact solution at one level
  have hmis : ∀ (s₀ K : ℝ) (ℓ : ℕ),
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ z) ≠
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z)} ≤
        (A + B) * Real.sqrt (T / 2 ^ ℓ * ((ℓ : ℝ) + 1)) := by
    intro s₀ K ℓ
    have hh0 : 0 < T / 2 ^ ℓ := by positivity
    have hk1 : (1 : ℝ) ≤ (ℓ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) ℓ]
    have hsk : 1 ≤ Real.sqrt ((ℓ : ℝ) + 1) := Real.one_le_sqrt.2 hk1
    rcases eq_or_ne s₀ 0 with rfl | hs₀
    · have hz : ∀ z, gbmExact r σ T 0 ℓ z = gbmEM r σ T 0 ℓ z := fun z => by
        rw [gbmEM_eq_prod, zero_mul]
        unfold gbmExact
        rw [zero_mul]
      have hset : {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T 0 ℓ z) ≠
          (Set.Ioi K).indicator 1 (gbmEM r σ T 0 ℓ z)} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, hz z, ne_eq, not_true_eq_false, Set.mem_empty_iff_false]
      rw [hset, measureReal_empty]
      positivity
    have hm := (gbm_em_exact_mismatch_le r σ hs₀ hσ hT K ℓ rfl hD).trans
      (endpoint_bound_le_sqrt (r := r) (D := D) (L := (ℓ : ℝ) * Real.log 2) hσ hT hh0
        (div_le_self hT.le (one_le_pow₀ (by norm_num))))
    rw [← hA, ← hB] at hm
    have hlog21 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      norm_num at this
      linarith
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hL : Real.sqrt ((ℓ : ℝ) * Real.log 2) ≤ Real.sqrt ((ℓ : ℝ) + 1) := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith [Nat.cast_nonneg (α := ℝ) ℓ]
    have hAB : A + B * Real.sqrt ((ℓ : ℝ) * Real.log 2) ≤ (A + B) * Real.sqrt ((ℓ : ℝ) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hL hB0]
    calc _ ≤ _ := hm
      _ ≤ Real.sqrt (T / 2 ^ ℓ) * ((A + B) * Real.sqrt ((ℓ : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hAB (Real.sqrt_nonneg _)
      _ = (A + B) * Real.sqrt (T / 2 ^ ℓ * ((ℓ : ℝ) + 1)) := by
          rw [Real.sqrt_mul hh0.le]
          ring
  refine ⟨A + B, by positivity, fun s₀ K ℓ => ⟨hmis s₀ K ℓ, ?_⟩⟩
  rw [← integral_digital_gbmExact r σ T s₀ K ℓ]
  exact (abs_integral_digital_sub_le (measurable_gbmExact r σ T s₀ ℓ)
    (measurable_gbmEM r σ T s₀ ℓ) K).trans (hmis s₀ K ℓ)

/-- **Theorem 1 for a fine/coarse estimator coupled by the summed increments, with
`α = β = ½` up to the factor `(ℓ + 1)^{1/2}` and `γ = 1`** (Giles 2015, §2.1, Theorem 1, pp. 6–7,
l. 271–299, the case `β < γ`, "`c₄ ε^{−2−(γ−β)/α}`", here with the factor `|log ε|`, and (2.4),
p. 8).  Let `T > 0`, `P_ℓ` (`Pf ℓ`) measurable and square integrable functions of the increments
`Z ∼ N(0,1)^{⊗ℕ}`, the coarse payoff `P_ℓ ∘ pairAvg` (so (2.4) holds), `P` integrable,
`|E[P_ℓ] − E[P]| ≤ c₁ (h_ℓ (ℓ + 1))^{1/2}` and
`V[P_{ℓ+1} − P_ℓ ∘ pairAvg] ≤ c₂ (h_{ℓ+1} (ℓ + 1))^{1/2}` with `h_ℓ = T 2^{−ℓ}`, independent
samples and cost `2^ℓ` per level-`ℓ` sample.  Then there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the error of the multilevel estimator of
`E[P]` is square integrable, its mean square is `< ε²`, and the cost is
`∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻³ |log ε|`.  Proof: `giles_theorem1_fineCoarse_logRates` with
`α = β = a = b = ½`, `γ = 1` (`−2 − (γ − β)/α = −3`, `k = max(½ + ½, 1) = 1`), via
`sqrt_div_two_pow_mul_eq`; `V[P_0]` enters the variance constant of Theorem 1. -/
lemma theorem1_pairAvg_of_sqrtLog_rate {T : ℝ} (hT : 0 < T)
    {Pf : ℕ → (ℕ → ℝ) → ℝ} {P : (ℕ → ℝ) → ℝ} (hPfm : ∀ ℓ, Measurable (Pf ℓ))
    (hPf : ∀ ℓ, MemLp (Pf ℓ) 2 stdNormalSeq) (hP : Integrable P stdNormalSeq) {c₁ c₂ : ℝ}
    (h_i : ∀ ℓ : ℕ, |∫ z, Pf ℓ z ∂stdNormalSeq - ∫ z, P z ∂stdNormalSeq| ≤
      c₁ * Real.sqrt (T / 2 ^ ℓ * ((ℓ : ℝ) + 1)))
    (h_iii : ∀ ℓ : ℕ, variance (fun z => Pf (ℓ + 1) z - Pf ℓ (pairAvg z)) stdNormalSeq ≤
      c₂ * Real.sqrt (T / 2 ^ (ℓ + 1) * ((ℓ : ℝ) + 1))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf
            (fun ℓ z => Pf ℓ (pairAvg z))) (fun p x => x p) ℓ (N ℓ) x -
            ∫ z, P z ∂stdNormalSeq) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf
            (fun ℓ z => Pf ℓ (pairAvg z))) (fun p x => x p) ℓ (N ℓ) x -
            ∫ z, P z ∂stdNormalSeq) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) <
          ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-3 : ℝ) * |Real.log ε|) := by
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hPcm : ∀ ℓ, Measurable (fun z => Pf ℓ (pairAvg z)) := fun ℓ =>
    (hPfm ℓ).comp measurePreserving_pairAvg.measurable
  have hPc : ∀ ℓ, MemLp (fun z => Pf ℓ (pairAvg z)) 2 stdNormalSeq := fun ℓ =>
    (hPf ℓ).comp_measurePreserving measurePreserving_pairAvg
  have h24 : ∀ ℓ, ∫ z, Pf ℓ z ∂stdNormalSeq = ∫ z, Pf ℓ (pairAvg z) ∂stdNormalSeq := fun ℓ =>
    (integral_comp_of_measurePreserving measurePreserving_pairAvg
      (hPfm ℓ).aestronglyMeasurable).symm
  -- (i) with `α = a = 1/2`
  have hc₁ : 0 < (|c₁| + 1) * Real.sqrt T := by positivity
  have h_i' : ∀ ℓ : ℕ, |∫ z, Pf ℓ z - P z ∂stdNormalSeq| ≤
      (|c₁| + 1) * Real.sqrt T * ((ℓ : ℝ) + 1) ^ (1 / 2 : ℝ) *
        (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) := fun ℓ => by
    rw [integral_sub ((hPf ℓ).integrable one_le_two) hP]
    have h2 : 0 ≤ Real.sqrt T * ((ℓ : ℝ) + 1) ^ (1 / 2 : ℝ) *
        (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) := by positivity
    calc _ ≤ c₁ * Real.sqrt (T / 2 ^ ℓ * ((ℓ : ℝ) + 1)) := h_i ℓ
      _ = c₁ * (Real.sqrt T * ((ℓ : ℝ) + 1) ^ (1 / 2 : ℝ) *
          (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ)))) := by
          rw [sqrt_div_two_pow_mul_eq hT.le ℓ]
      _ ≤ (|c₁| + 1) * (Real.sqrt T * ((ℓ : ℝ) + 1) ^ (1 / 2 : ℝ) *
          (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ)))) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c₁]) h2
      _ = _ := by ring
  -- (iii) with `β = b = 1/2`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (Pf 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by
    rw [hV₀]
    exact variance_nonneg _ _
  have hc₂ : 0 < V₀ + (|c₂| + 1) * Real.sqrt T := by positivity
  have h_iii' : ∀ ℓ, variance (fineCoarseDiff Pf (fun ℓ z => Pf ℓ (pairAvg z)) ℓ)
      stdNormalSeq ≤ (V₀ + (|c₂| + 1) * Real.sqrt T) * ((ℓ : ℝ) + 1) ^ (1 / 2 : ℝ) *
        (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) := by
    intro ℓ
    cases ℓ with
    | zero =>
      show variance (Pf 0) stdNormalSeq ≤ _
      rw [← hV₀, Nat.cast_zero, zero_add, Real.one_rpow, mul_zero, neg_zero, Real.rpow_zero,
        mul_one, mul_one]
      have : 0 ≤ (|c₂| + 1) * Real.sqrt T := by positivity
      linarith
    | succ ℓ =>
      have hx : ((ℓ : ℝ) + 1) ^ (1 / 2 : ℝ) ≤ (((ℓ + 1 : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by push_cast; linarith) (by norm_num)
      have hX : 0 ≤ Real.sqrt T * ((ℓ : ℝ) + 1) ^ (1 / 2 : ℝ) *
          (2 : ℝ) ^ (-(1 / 2 * ((ℓ + 1 : ℕ) : ℝ))) := by positivity
      have hY : 0 ≤ (((ℓ + 1 : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ) *
          (2 : ℝ) ^ (-(1 / 2 * ((ℓ + 1 : ℕ) : ℝ))) := by positivity
      calc variance (fineCoarseDiff Pf (fun ℓ z => Pf ℓ (pairAvg z)) (ℓ + 1)) stdNormalSeq
          = variance (fun z => Pf (ℓ + 1) z - Pf ℓ (pairAvg z)) stdNormalSeq := rfl
        _ ≤ c₂ * Real.sqrt (T / 2 ^ (ℓ + 1) * ((ℓ : ℝ) + 1)) := h_iii ℓ
        _ = c₂ * (Real.sqrt T * ((ℓ : ℝ) + 1) ^ (1 / 2 : ℝ) *
            (2 : ℝ) ^ (-(1 / 2 * ((ℓ + 1 : ℕ) : ℝ)))) := by
            rw [sqrt_div_two_pow_mul_eq hT.le (ℓ + 1)]
        _ ≤ (|c₂| + 1) * (Real.sqrt T * ((ℓ : ℝ) + 1) ^ (1 / 2 : ℝ) *
            (2 : ℝ) ^ (-(1 / 2 * ((ℓ + 1 : ℕ) : ℝ)))) :=
            mul_le_mul_of_nonneg_right (by linarith [le_abs_self c₂]) hX
        _ ≤ (|c₂| + 1) * (Real.sqrt T * (((ℓ + 1 : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ) *
            (2 : ℝ) ^ (-(1 / 2 * ((ℓ + 1 : ℕ) : ℝ)))) := by
            gcongr
        _ ≤ _ := by nlinarith [mul_nonneg hV₀0 hY]
  -- (iv) with `γ = 1`: a level-`ℓ` sample costs `2^ℓ`
  have h_iv : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ 1 * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, one_mul, Real.rpow_natCast]
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse_logRates
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) P Pf (fun ℓ z => Pf ℓ (pairAvg z))
    (fun p x => x p) (fun ℓ _ _ => (2 : ℝ) ^ ℓ) (fun ℓ => (2 : ℝ) ^ ℓ) (α := 1 / 2)
    (β := 1 / 2) (γ := 1) (a := 1 / 2) (b := 1 / 2) (by norm_num) one_pos (by norm_num)
    (by rw [min_eq_left (by norm_num : (1 / 2 : ℝ) ≤ 1)]; norm_num) (by norm_num) (by norm_num)
    hc₁ hc₂ one_pos hω hind hP hPfm hPcm hPf hPc h24 (fun _ _ => integrable_const _)
    (fun _ _ => by rw [integral_const, probReal_univ, one_smul]) h_i' h_iii' h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, hint, hmse, ?_⟩
  have e : ∀ x : ℕ × ℕ → ℕ → ℝ, totalCost (fun ℓ _ _ => (2 : ℝ) ^ ℓ) L N x =
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ := fun x => by
    unfold totalCost
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e1 : (-2 - (1 - 1 / 2) / (1 / 2) : ℝ) = -3 := by norm_num
  have e2 : max (1 / 2 + 1 / 2 * (1 - 1 / 2) / (1 / 2)) (1 / 2 * 1 / (1 / 2) : ℝ) = 1 := by
    norm_num
  rw [funext e, integral_const, probReal_univ, one_smul, e1, e2, Real.rpow_one] at hcost
  exact hcost

/-- **Theorem 1 end to end for the digital option with Euler–Maruyama: MSE `< ε²` at cost
`O(ε⁻³ |log ε|)`** (Giles 2015, §5.1, p. 30, l. 1356–1358: "Figure 5.4 illustrates the problem with
discontinuous payoff functions. The underlying SDE is exactly the same, but the payoff is a
digital option with payoff `P(S) ≡ 10 exp(−rT) H(S_T − K)`"; p. 33, l. 1436–1449: "This gives
`V_ℓ = O(h^{1/2})` … Consequently, this application has `α = 1`, `β = ½`, `γ = 1`, leading to the
MLMC complexity being `O(ε^{−2.5})`", with Theorem 1, §2.1, pp. 6–7, l. 271–299, and (2.4), p. 8).
For `dS = rS dt + σS dW`, `S_0 = s₀`, `σ ≠ 0`, `T > 0` and any strike `K`: level `ℓ` uses `2^ℓ`
Euler–Maruyama steps of size `T 2^{−ℓ}`, the payoff is `H(Ŝ_ℓ − K) = 1_{Ŝ_ℓ > K}`, the coarse path
of a sample is driven by the summed increments, the samples are independent and a level-`ℓ`
sample costs `2^ℓ`.  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and
`N_ℓ ≥ 1` for which the multilevel estimator of
`E[H(S_T − K)] = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} dN(0,1)(w)` (the estimator, probability space
and target of `gbm_em_digital_theorem1`) has a square-integrable error with mean square `< ε²`, at
cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻³ |log ε|`.  This removes the loss `η > 0` of
`gbm_em_digital_theorem1` (cost `O(ε^{−3−η})`).  No rate is assumed: the weak error
`gbm_em_digital_weak_endpoint` (`α = a = ½`), the variance `gbm_em_digital_endpoint`
(`β = b = ½`) and `theorem1_pairAvg_of_sqrtLog_rate` (`γ = 1`, `k = 1`).

**How close to the paper.**  The paper's `O(ε^{−2.5})` uses the weak order `α = 1` of
Euler–Maruyama for the digital option (a result of Bally–Talay type for non-smooth payoffs, not
cited in the paper), which is not proved here: the weak error is bounded by the mismatch
probability, `O((h log(1/h))^{1/2})`, i.e. `α = ½` up to the logarithm, and with these rates
`ε⁻³ |log ε|` is what Theorem 1 gives (and, heuristically, the best it can give; see the module
documentation).  The constant `c₄` depends on `r, σ, T, s₀, K` (on `s₀`, `K` only through
`V[1_{Ŝ_0 > K}]`).  `σ ≠ 0` is needed, as in `gbm_em_digital_theorem1`: for `σ = 0`, `s₀ = −1`,
`r = T = 1` and `K = −e` the mean square error is `1` for every `L` and `N`. -/
theorem gbm_em_digital_theorem1_log (r σ s₀ K : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ z))
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ (pairAvg z))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ z))
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ (pairAvg z))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-3 : ℝ) * |Real.log ε|) := by
  obtain ⟨C₁, -, hC₁⟩ := gbm_em_digital_weak_endpoint r σ hσ hT
  obtain ⟨C₂, -, hC₂⟩ := gbm_em_digital_endpoint r σ hσ hT
  obtain ⟨c₄, hc₄, h⟩ := theorem1_pairAvg_of_sqrtLog_rate hT
    (Pf := fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ z))
    (P := fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ 0 z))
    (fun ℓ => measurable_digital (measurable_gbmEM r σ T s₀ ℓ) K)
    (fun ℓ => memLp_digital (measurable_gbmEM r σ T s₀ ℓ) K)
    (integrable_digital (measurable_gbmExact r σ T s₀ 0) K) (c₁ := C₁) (c₂ := C₂)
    (fun ℓ => by rw [integral_digital_gbmExact]; exact (hC₁ s₀ K ℓ).2)
    (fun ℓ => (hC₂ s₀ K ℓ).1)
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  rw [integral_digital_gbmExact] at hint hmse
  exact ⟨L, N, hN, hint, hmse, hcost⟩

end MLMC
