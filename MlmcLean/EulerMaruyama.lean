import MlmcLean.Corrections
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic.LinearCombination

/-!
# The Euler–Maruyama fine/coarse coupling (Haas–Giles 2025, (2), (4)–(5); Giles 2015, §5.1)

References: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1 (2.4) and
§5.1 "Euler–Maruyama discretisation" (pp. 29–30); I.-B. Haas and M.B. Giles, *A nested MLMC
framework for efficient simulations on FPGAs*, arXiv:2502.07123 (2025), §2, equations (2), (4)
and (5).

**The scheme.**  The SDE `dS_t = a(S_t, t) dt + b(S_t, t) dW_t` is approximated by the
Euler–Maruyama scheme `S_{i+1} = S_i + a(S_i, t_i) h + b(S_i, t_i) √h Z_i`, `t_i = i h`, driven by
independent standard normal increments `Z_0, Z_1, …` (`emPath`), whose joint law is `N(0,1)^{⊗ℕ}`
(`stdNormalSeq`).  On level `ℓ` the fine path (4) takes `2^ℓ` steps of size `h_ℓ = T 2^{−ℓ}`.  The
coarse path (5) uses the same increments and the same step `h`, but freezes the drift and the
volatility over pairs of steps (`emCoarsePath`):

  `S^c_{i+1} = S^c_i + a(S^c_{2⌊i/2⌋}, t_{2⌊i/2⌋}) h + b(S^c_{2⌊i/2⌋}, t_{2⌊i/2⌋}) √h Z_i`.

* `emCoarsePath_succ`, `eq_emCoarsePath`: `emCoarsePath` satisfies (5), and it is its only solution;
* `emCoarsePath_two_mul`: at the even indices the coarse path is the Euler–Maruyama path with step
  `2h` driven by `(Z_{2k} + Z_{2k+1})/√2` — Giles' "summing the Brownian increments for the fine
  path timesteps to obtain the Brownian increments for the coarse timesteps";
* `map_pairSum_gaussian`, `measurePreserving_pairAvg`: these coarse increments are again
  independent standard normal variables;
* `integral_emCoarse`: hence (2.4) holds, a payoff of the coarse path on level `ℓ + 1` has the
  expectation of the same payoff of the fine path on level `ℓ`; `em_mlmc_theorem1` is Giles'
  Theorem 1 for the Euler–Maruyama estimator, with (2.4) derived rather than assumed.

**The variance rate (Giles 2015, §5.1).**  `variance_levelDiff_le`:
"`V_ℓ ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`"; `variance_sub_le_of_lipschitz`:
"`V[P − P_ℓ] ≤ E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`" for Lipschitz payoffs;
`variance_levelDiff_of_strong`: a mean-square rate `E[(P − P_ℓ)²] = O(2^{−βℓ})` gives
`V_ℓ = O(2^{−βℓ})`; `em_complexity`: the exponents `α = β = γ = 1` (`h_ℓ = 2^{−ℓ} h_0`) and
`α = β = γ = 2` (`h_ℓ = 4^{−ℓ} h_0`) both give `O(ε⁻²(log ε)²)`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### The fine and the coarse path -/

/-- The Euler–Maruyama scheme (Haas–Giles 2025, (2) and (4); Giles 2015, §5.1): `S_0 = S₀` and
`S_{i+1} = S_i + a(S_i, t_i) h + b(S_i, t_i) √h Z_i` with `t_i = i h`, driven by the normal
increments `z = (Z_0, Z_1, …)`. -/
noncomputable def emPath (a b : ℝ → ℝ → ℝ) (h S₀ : ℝ) (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => S₀
  | i + 1 => emPath a b h S₀ z i + a (emPath a b h S₀ z i) (i * h) * h +
      b (emPath a b h S₀ z i) (i * h) * Real.sqrt h * z i

/-- The normal increments of the coarse path, `(Z_{2k} + Z_{2k+1})/√2` (Giles 2015, §5.1: the
coarse Brownian increments are the sums of the fine ones; Haas–Giles 2025, (5)). -/
noncomputable def pairAvg (z : ℕ → ℝ) (k : ℕ) : ℝ := (z (2 * k) + z (2 * k + 1)) / Real.sqrt 2

/-- The coarse path of Haas–Giles 2025, (5), in which the drift and the volatility are frozen over
pairs of fine steps.  At the even indices it is the Euler–Maruyama path with step `2h` driven by
`pairAvg z`; at the odd index `2k + 1` it is one step of size `h` from there (`emCoarsePath_succ`
shows that it satisfies (5), and `eq_emCoarsePath` that it is the only solution). -/
noncomputable def emCoarsePath (a b : ℝ → ℝ → ℝ) (h S₀ : ℝ) (z : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i % 2 = 0 then emPath a b (2 * h) S₀ (pairAvg z) (i / 2)
  else emPath a b (2 * h) S₀ (pairAvg z) (i / 2) +
    a (emPath a b (2 * h) S₀ (pairAvg z) (i / 2)) ((2 * (i / 2) : ℕ) * h) * h +
    b (emPath a b (2 * h) S₀ (pairAvg z) (i / 2)) ((2 * (i / 2) : ℕ) * h) * Real.sqrt h *
      z (i - 1)

lemma emPath_succ (a b : ℝ → ℝ → ℝ) (h S₀ : ℝ) (z : ℕ → ℝ) (i : ℕ) :
    emPath a b h S₀ z (i + 1) = emPath a b h S₀ z i + a (emPath a b h S₀ z i) (i * h) * h +
      b (emPath a b h S₀ z i) (i * h) * Real.sqrt h * z i := rfl

/-- **At the even indices the coarse path is the Euler–Maruyama path with step `2h`** (Giles 2015,
§5.1; Haas–Giles 2025, (5)), driven by the coarse increments `(Z_{2k} + Z_{2k+1})/√2`. -/
theorem emCoarsePath_two_mul (a b : ℝ → ℝ → ℝ) (h S₀ : ℝ) (z : ℕ → ℝ) (k : ℕ) :
    emCoarsePath a b h S₀ z (2 * k) = emPath a b (2 * h) S₀ (pairAvg z) k := by
  have e1 : 2 * k % 2 = 0 := by omega
  have e2 : 2 * k / 2 = k := by omega
  unfold emCoarsePath
  rw [if_pos e1, e2]

lemma emCoarsePath_two_mul_add_one (a b : ℝ → ℝ → ℝ) (h S₀ : ℝ) (z : ℕ → ℝ) (k : ℕ) :
    emCoarsePath a b h S₀ z (2 * k + 1) = emPath a b (2 * h) S₀ (pairAvg z) k +
      a (emPath a b (2 * h) S₀ (pairAvg z) k) ((2 * k : ℕ) * h) * h +
      b (emPath a b (2 * h) S₀ (pairAvg z) k) ((2 * k : ℕ) * h) * Real.sqrt h * z (2 * k) := by
  have e1 : ¬(2 * k + 1) % 2 = 0 := by omega
  have e2 : (2 * k + 1) / 2 = k := by omega
  have e3 : 2 * k + 1 - 1 = 2 * k := by omega
  unfold emCoarsePath
  rw [if_neg e1, e2, e3]

/-- **The coarse path satisfies Haas–Giles (5)** (Haas–Giles 2025, (5): "when `i` is even,
`S^c_{i+1}` and `S^c_{i+2}` are both computed using the drift and volatility evaluated based on
`S^c_i, t_i`"):
`S^c_{i+1} = S^c_i + a(S^c_{2⌊i/2⌋}, t_{2⌊i/2⌋}) h + b(S^c_{2⌊i/2⌋}, t_{2⌊i/2⌋}) √h Z_i`.
Two coarse sub-steps of size `h` with frozen coefficients make one Euler–Maruyama step of size
`2h` with the increment `(Z_{2k} + Z_{2k+1})/√2`. -/
theorem emCoarsePath_succ (a b : ℝ → ℝ → ℝ) (h S₀ : ℝ) (z : ℕ → ℝ) (i : ℕ) :
    emCoarsePath a b h S₀ z (i + 1) = emCoarsePath a b h S₀ z i +
      a (emCoarsePath a b h S₀ z (2 * (i / 2))) ((2 * (i / 2) : ℕ) * h) * h +
      b (emCoarsePath a b h S₀ z (2 * (i / 2))) ((2 * (i / 2) : ℕ) * h) * Real.sqrt h * z i := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
  · have e : 2 * k / 2 = k := by omega
    rw [e, emCoarsePath_two_mul_add_one, emCoarsePath_two_mul]
  · have e : (2 * k + 1) / 2 = k := by omega
    have e' : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
    have et : (k : ℝ) * (2 * h) = ((2 * k : ℕ) : ℝ) * h := by push_cast; ring
    have hs : Real.sqrt (2 * h) = Real.sqrt 2 * Real.sqrt h := Real.sqrt_mul (by norm_num) h
    have key : Real.sqrt 2 * pairAvg z k = z (2 * k) + z (2 * k + 1) :=
      mul_div_cancel₀ _ (by positivity)
    rw [e, e', emCoarsePath_two_mul, emCoarsePath_two_mul_add_one, emCoarsePath_two_mul,
      emPath_succ, et, hs]
    linear_combination
      (b (emPath a b (2 * h) S₀ (pairAvg z) k) (((2 * k : ℕ) : ℝ) * h) * Real.sqrt h) * key

/-- **The coarse path is the only solution of (5)** (Haas–Giles 2025, (5)): a sequence with
`S^c_0 = S₀` that satisfies the recursion (5) is `emCoarsePath`. -/
theorem eq_emCoarsePath (a b : ℝ → ℝ → ℝ) (h S₀ : ℝ) (z : ℕ → ℝ) {Sc : ℕ → ℝ} (h0 : Sc 0 = S₀)
    (h5 : ∀ i, Sc (i + 1) = Sc i + a (Sc (2 * (i / 2))) ((2 * (i / 2) : ℕ) * h) * h +
      b (Sc (2 * (i / 2))) ((2 * (i / 2) : ℕ) * h) * Real.sqrt h * z i) :
    Sc = emCoarsePath a b h S₀ z := by
  funext i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero =>
      rw [h0]
      exact (emCoarsePath_two_mul a b h S₀ z 0).symm
    | succ i =>
      rw [h5, emCoarsePath_succ, ih i (Nat.lt_succ_self i), ih (2 * (i / 2)) (by omega)]

/-! ### The coarse increments are standard normal -/

/-- The law `N(0,1)^{⊗ℕ}` of independent standard normal increments `Z_0, Z_1, …` (Haas–Giles
2025, (2): "`Z_i` is a random increment that follows the normal distribution `N(0,1)`"). -/
noncomputable abbrev stdNormalSeq : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

/-- **The coarse increment is a standard normal** (Giles 2015, §5.1; Haas–Giles 2025, (5)): if
`Z₀, Z₁` are independent standard normal variables, then `(Z₀ + Z₁)/√2` is standard normal. -/
theorem map_pairSum_gaussian :
    (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1).map
      (fun y : Fin 2 → ℝ => (y 0 + y 1) / Real.sqrt 2) = gaussianReal 0 1 := by
  have hind : IndepFun (fun y : Fin 2 → ℝ => y 0) (fun y => y 1)
      (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) :=
    (iIndepFun_infinitePi (P := fun _ : Fin 2 => gaussianReal 0 1) (X := fun _ x => x)
      fun _ => measurable_id).indepFun (by decide)
  have h0 : (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1).map (fun y => y 0) =
      gaussianReal 0 1 := Measure.infinitePi_map_eval _ 0
  have h1 : (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1).map (fun y => y 1) =
      gaussianReal 0 1 := Measure.infinitePi_map_eval _ 1
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hind h0 h1
  have hcomp : (fun y : Fin 2 → ℝ => (y 0 + y 1) / Real.sqrt 2) =
      (fun x => x / Real.sqrt 2) ∘ ((fun y : Fin 2 → ℝ => y 0) + fun y => y 1) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), hsum, gaussianReal_map_div_const]
  congr 1
  · simp
  · rw [← NNReal.coe_inj]
    norm_num [Real.sq_sqrt]

/-- **The coarse increments are again independent standard normal variables** (Giles 2015, §5.1;
Haas–Giles 2025, (5)): `z ↦ ((z_{2k} + z_{2k+1})/√2)_k` preserves `N(0,1)^{⊗ℕ}`.  The pairs
`(z_{2k}, z_{2k+1})` are independent (the product measure, reindexed and curried), and each pair is
mapped to a standard normal (`map_pairSum_gaussian`). -/
theorem measurePreserving_pairAvg : MeasurePreserving pairAvg stdNormalSeq stdNormalSeq := by
  have hf : Function.Injective (fun p : ℕ × Fin 2 => 2 * p.1 + (p.2 : ℕ)) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    change 2 * a + (i : ℕ) = 2 * b + (j : ℕ) at h
    have hi := i.isLt
    have hj := j.isLt
    obtain rfl : a = b := by omega
    obtain rfl : i = j := Fin.ext (by omega)
    rfl
  -- reindex the coordinates by the pairs `(k, i) ↦ 2k + i`
  have m1 : MeasurePreserving (fun (z : ℕ → ℝ) (p : ℕ × Fin 2) => z (2 * p.1 + (p.2 : ℕ)))
      stdNormalSeq (Measure.infinitePi fun _ : ℕ × Fin 2 => gaussianReal 0 1) :=
    ⟨measurable_pi_lambda _ fun p => measurable_pi_apply _,
      Measure.map_infinitePi_infinitePi_of_inj hf⟩
  -- curry: a sequence of independent pairs
  have m2 : MeasurePreserving (MeasurableEquiv.curry ℕ (Fin 2) ℝ)
      (Measure.infinitePi fun _ : ℕ × Fin 2 => gaussianReal 0 1)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) :=
    ⟨(MeasurableEquiv.curry ℕ (Fin 2) ℝ).measurable,
      Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1)⟩
  -- map each pair to its normalised sum
  have m3 : MeasurePreserving
      (fun (x : ℕ → Fin 2 → ℝ) (k : ℕ) => (x k 0 + x k 1) / Real.sqrt 2)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1)
      stdNormalSeq := by
    refine ⟨measurable_pi_lambda _ fun k => ?_, ?_⟩
    · exact (((measurable_pi_apply 0).comp (measurable_pi_apply k)).add
        ((measurable_pi_apply 1).comp (measurable_pi_apply k))).div_const _
    · refine (Measure.infinitePi_map_pi _
        (f := fun _ (y : Fin 2 → ℝ) => (y 0 + y 1) / Real.sqrt 2)
        (fun _ => ((measurable_pi_apply 0).add (measurable_pi_apply 1)).div_const _)).trans ?_
      simp only [map_pairSum_gaussian, stdNormalSeq]
  have h := (m3.comp m2).comp m1
  have e : ((fun (x : ℕ → Fin 2 → ℝ) (k : ℕ) => (x k 0 + x k 1) / Real.sqrt 2) ∘
      (MeasurableEquiv.curry ℕ (Fin 2) ℝ)) ∘
      (fun (z : ℕ → ℝ) (p : ℕ × Fin 2) => z (2 * p.1 + (p.2 : ℕ))) = pairAvg := by
    funext z k
    simp [pairAvg, MeasurableEquiv.coe_curry, Function.curry]
  rwa [e] at h

/-! ### The level approximations and (2.4) -/

/-- The fine level-`ℓ` approximation (Haas–Giles 2025, (4)): a payoff `Φ ℓ` of the Euler–Maruyama
path with `2^ℓ` steps of size `h_ℓ = T 2^{−ℓ}`, driven by the normal increments `z`. -/
noncomputable def emFine (a b : ℝ → ℝ → ℝ) (T S₀ : ℝ) (Φ : ℕ → (ℕ → ℝ) → ℝ) (ℓ : ℕ)
    (z : ℕ → ℝ) : ℝ :=
  Φ ℓ (emPath a b (T / 2 ^ ℓ) S₀ z)

/-- The coarse level-`ℓ` approximation within a level-`(ℓ + 1)` sample (Haas–Giles 2025, (5)): the
same payoff `Φ ℓ` of the coarse path with step `h_{ℓ+1}` at the coarse times `t_{2k}`. -/
noncomputable def emCoarse (a b : ℝ → ℝ → ℝ) (T S₀ : ℝ) (Φ : ℕ → (ℕ → ℝ) → ℝ) (ℓ : ℕ)
    (z : ℕ → ℝ) : ℝ :=
  Φ ℓ (fun k => emCoarsePath a b (T / 2 ^ (ℓ + 1)) S₀ z (2 * k))

/-- **The coarse approximation is the fine approximation of the level below, driven by the coarse
increments** (Giles 2015, §5.1; Haas–Giles 2025, (4)–(5)):
`P^c_ℓ(z) = P^f_ℓ((Z_{2k} + Z_{2k+1})/√2)`, since `2 h_{ℓ+1} = h_ℓ`. -/
theorem emCoarse_eq (a b : ℝ → ℝ → ℝ) (T S₀ : ℝ) (Φ : ℕ → (ℕ → ℝ) → ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    emCoarse a b T S₀ Φ ℓ z = emFine a b T S₀ Φ ℓ (pairAvg z) := by
  have e : 2 * (T / 2 ^ (ℓ + 1)) = T / 2 ^ ℓ := by
    rw [pow_succ (2 : ℝ) ℓ, ← div_div, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  unfold emCoarse emFine
  exact congrArg (Φ ℓ) (funext fun k => by rw [emCoarsePath_two_mul, e])

/-- **The Euler–Maruyama coupling satisfies (2.4)** (Giles 2015, §2.1, (2.4)
"`E[P^f_ℓ] = E[P^c_ℓ]`", and §5.1; Haas–Giles 2025, (4)–(5)).  With independent standard normal
increments, the payoff of the coarse path in a level-`(ℓ + 1)` sample has the same expectation as
the payoff of the fine path on level `ℓ`. -/
theorem integral_emCoarse (a b : ℝ → ℝ → ℝ) (T S₀ : ℝ) (Φ : ℕ → (ℕ → ℝ) → ℝ) (ℓ : ℕ)
    (hm : AEStronglyMeasurable (emFine a b T S₀ Φ ℓ) stdNormalSeq) :
    ∫ z, emCoarse a b T S₀ Φ ℓ z ∂stdNormalSeq = ∫ z, emFine a b T S₀ Φ ℓ z ∂stdNormalSeq := by
  simp_rw [emCoarse_eq]
  exact integral_comp_of_measurePreserving measurePreserving_pairAvg hm

/-- **Theorem 1 for the Euler–Maruyama estimator** (Giles 2015, §2.1, Theorem 1 with (2.4), and
§5.1; Haas–Giles 2025, (3)–(5)).  The level-`ℓ` correction is the fine payoff (4) minus the coarse
payoff (5) on the same normal increments, `Y_ℓ = N_ℓ⁻¹ ∑_n (P^f_ℓ − P^c_{ℓ−1})(ω^{(ℓ,n)})`, with
the samples `ω^{(ℓ,n)}` independent with law `N(0,1)^{⊗ℕ}`.  Condition (2.4) holds
(`integral_emCoarse`), so under (i) for `P^f_ℓ`, (iii) for `V_ℓ = V[P^f_ℓ − P^c_{ℓ−1}]` and (iv)
with `α ≥ ½ min(β, γ)`, there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and
`N_ℓ ≥ 1` with `MSE < ε²` and `E[C] ≤ c₄ · bound(ε)`. -/
theorem em_mlmc_theorem1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (a b : ℝ → ℝ → ℝ) (T S₀ : ℝ) (Φ : ℕ → (ℕ → ℝ) → ℝ) (P : (ℕ → ℝ) → ℝ)
    (ω : ℕ × ℕ → Ω → ℕ → ℝ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hω : ∀ p, MeasurePreserving (ω p) μ stdNormalSeq) (hind : iIndepFun ω μ)
    (hP : Integrable P stdNormalSeq) (hPfm : ∀ ℓ, Measurable (emFine a b T S₀ Φ ℓ))
    (hPf : ∀ ℓ, MemLp (emFine a b T S₀ Φ ℓ) 2 stdNormalSeq)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (h_i : ∀ ℓ : ℕ, |∫ z, emFine a b T S₀ Φ ℓ z - P z ∂stdNormalSeq| ≤
      c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, variance (fineCoarseDiff (emFine a b T S₀ Φ) (emCoarse a b T S₀ Φ) ℓ)
      stdNormalSeq ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1),
          blockMean (fineCoarseDiff (emFine a b T S₀ Φ) (emCoarse a b T S₀ Φ)) ω ℓ (N ℓ) x -
            ∫ z, P z ∂stdNormalSeq) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * complexityBound α β γ ε := by
  have hc : ∀ ℓ, emCoarse a b T S₀ Φ ℓ = emFine a b T S₀ Φ ℓ ∘ pairAvg := fun ℓ =>
    funext (emCoarse_eq a b T S₀ Φ ℓ)
  have hPcm : ∀ ℓ, Measurable (emCoarse a b T S₀ Φ ℓ) := fun ℓ => by
    rw [hc]
    exact (hPfm ℓ).comp measurePreserving_pairAvg.measurable
  have hPc : ∀ ℓ, MemLp (emCoarse a b T S₀ Φ ℓ) 2 stdNormalSeq := fun ℓ => by
    rw [hc]
    exact (hPf ℓ).comp_measurePreserving measurePreserving_pairAvg
  exact giles_theorem1_fineCoarse P (emFine a b T S₀ Φ) (emCoarse a b T S₀ Φ) ω cost C hα hβ hγ
    hc₁ hc₂ hc₃ hαβγ hω hind hP hPfm hPcm hPf hPc
    (fun ℓ => (integral_emCoarse a b T S₀ Φ ℓ (hPfm ℓ).aestronglyMeasurable).symm)
    hcost hcostC h_i h_iii h_iv

/-! ### The variance rate (Giles 2015, §5.1) -/

section Variance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `V[X − Y] ≤ 2 (V[X] + V[Y])` for square-integrable `X, Y` (Giles 2015, §5.1: the bound on the
variance of a level correction). -/
theorem variance_sub_le_two_mul {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance (fun ω => X ω - Y ω) μ ≤ 2 * (variance X μ + variance Y μ) := by
  have hXm := hX.aestronglyMeasurable.aemeasurable
  have hYm := hY.aestronglyMeasurable.aemeasurable
  have hdm : AEMeasurable (fun ω => X ω - Y ω) μ := hXm.sub hYm
  rw [variance_eq_integral hdm, variance_eq_integral hXm, variance_eq_integral hYm,
    integral_sub (hX.integrable one_le_two) (hY.integrable one_le_two)]
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ ω, X ω ∂μ := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = ∫ ω, Y ω ∂μ := ⟨_, rfl⟩
  rw [← hm, ← hn]
  have hXa : Integrable (fun ω => (X ω - m) ^ 2) μ := (hX.sub (memLp_const m)).integrable_sq
  have hYb : Integrable (fun ω => (Y ω - n) ^ 2) μ := (hY.sub (memLp_const n)).integrable_sq
  calc ∫ ω, (X ω - Y ω - (m - n)) ^ 2 ∂μ
      ≤ ∫ ω, (2 * (X ω - m) ^ 2 + 2 * (Y ω - n) ^ 2) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
          ((hXa.const_mul 2).add (hYb.const_mul 2)) (Filter.Eventually.of_forall fun ω => by
            nlinarith [sq_nonneg (X ω - m + (Y ω - n))])
    _ = 2 * (∫ ω, (X ω - m) ^ 2 ∂μ + ∫ ω, (Y ω - n) ^ 2 ∂μ) := by
        rw [integral_add (hXa.const_mul 2) (hYb.const_mul 2), integral_const_mul,
          integral_const_mul]
        ring

/-- **The variance of a level correction** (Giles 2015, §5.1: "`V_ℓ ≡ V[P_ℓ − P_{ℓ−1}] ≤
2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`"). -/
theorem variance_levelDiff_le {P P₁ P₂ : Ω → ℝ} (hP : MemLp P 2 μ) (h₁ : MemLp P₁ 2 μ)
    (h₂ : MemLp P₂ 2 μ) :
    variance (fun ω => P₁ ω - P₂ ω) μ ≤
      2 * (variance (fun ω => P ω - P₁ ω) μ + variance (fun ω => P ω - P₂ ω) μ) := by
  have hA : MemLp (fun ω => P ω - P₂ ω) 2 μ := hP.sub h₂
  have hB : MemLp (fun ω => P ω - P₁ ω) 2 μ := hP.sub h₁
  have h := variance_sub_le_two_mul hA hB
  have e : variance (fun ω => P₁ ω - P₂ ω) μ =
      variance (fun ω => (P ω - P₂ ω) - (P ω - P₁ ω)) μ :=
    congrArg (fun F : Ω → ℝ => variance F μ) (funext fun ω => by ring)
  rw [e]
  linarith

/-- **Lipschitz payoffs** (Giles 2015, §5.1: "For Lipschitz payoff functions `P` … for which
`|P(S₁) − P(S₂)| ≤ K‖S₁ − S₂‖`, we have `V[P − P_ℓ] ≤ E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`").  If
`|P − P_ℓ| ≤ K D` pointwise with `D²` integrable (`D = ‖S − Ŝ_ℓ‖`), then
`V[P − P_ℓ] ≤ E[(P − P_ℓ)²] ≤ K² E[D²]`. -/
theorem variance_sub_le_of_lipschitz {P Pl D : Ω → ℝ} {K : ℝ}
    (hm : AEStronglyMeasurable (fun ω => P ω - Pl ω) μ) (hD : Integrable (fun ω => D ω ^ 2) μ)
    (hK : ∀ ω, |P ω - Pl ω| ≤ K * D ω) :
    variance (fun ω => P ω - Pl ω) μ ≤ ∫ ω, (P ω - Pl ω) ^ 2 ∂μ ∧
      ∫ ω, (P ω - Pl ω) ^ 2 ∂μ ≤ K ^ 2 * ∫ ω, D ω ^ 2 ∂μ := by
  have hsq : ∀ ω, (P ω - Pl ω) ^ 2 ≤ K ^ 2 * D ω ^ 2 := fun ω => by
    calc (P ω - Pl ω) ^ 2 = |P ω - Pl ω| ^ 2 := (sq_abs _).symm
      _ ≤ (K * D ω) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hK ω) 2
      _ = K ^ 2 * D ω ^ 2 := by ring
  have hint : Integrable (fun ω => (P ω - Pl ω) ^ 2) μ :=
    (hD.const_mul (K ^ 2)).mono' (hm.pow 2) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hsq ω)
  refine ⟨?_, ?_⟩
  · simpa only [Pi.pow_apply] using variance_le_expectation_sq hm
  · rw [← integral_const_mul]
    exact integral_mono hint (hD.const_mul _) hsq

/-- **From the strong rate to the variance rate** (Giles 2015, §5.1: "`E[‖S − Ŝ‖²] = O(h)` … and
hence `V_ℓ = O(h_ℓ)`"; the variance rate `β` of Theorem 1 is the mean-square rate of the
approximations).  If `E[(P − P_ℓ)²] ≤ c 2^{−βℓ}` for every `ℓ`, then
`V[P_{ℓ+1} − P_ℓ] ≤ 2c(1 + 2^β) 2^{−β(ℓ+1)}`. -/
theorem variance_levelDiff_of_strong {P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} (hP : MemLp P 2 μ)
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ) {c β : ℝ}
    (hs : ∀ ℓ : ℕ, ∫ ω, (P ω - Pl ℓ ω) ^ 2 ∂μ ≤ c * (2 : ℝ) ^ (-(β * ℓ))) (ℓ : ℕ) :
    variance (fun ω => Pl (ℓ + 1) ω - Pl ℓ ω) μ ≤
      2 * c * (1 + (2 : ℝ) ^ β) * (2 : ℝ) ^ (-(β * ((ℓ + 1 : ℕ) : ℝ))) := by
  have hv : ∀ k : ℕ, variance (fun ω => P ω - Pl k ω) μ ≤ c * (2 : ℝ) ^ (-(β * k)) := fun k => by
    have hm : AEStronglyMeasurable (fun ω => P ω - Pl k ω) μ :=
      hP.aestronglyMeasurable.sub (hPl k).aestronglyMeasurable
    have h := variance_le_expectation_sq hm
    simp only [Pi.pow_apply] at h
    exact h.trans (hs k)
  have h1 := variance_levelDiff_le hP (hPl (ℓ + 1)) (hPl ℓ)
  have h2 := hv (ℓ + 1)
  have h3 := hv ℓ
  have e : (2 : ℝ) ^ (-(β * (ℓ : ℝ))) =
      (2 : ℝ) ^ β * (2 : ℝ) ^ (-(β * ((ℓ + 1 : ℕ) : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  rw [e] at h3
  linarith

end Variance

/-- **The complexity of the Euler–Maruyama MLMC estimator** (Giles 2015, §5.1:
"If `h_ℓ = 4^{−ℓ} h_0` … this gives `α = 2, β = 2` and `γ = 2`.  Alternatively, if
`h_ℓ = 2^{−ℓ} h_0` … then `α = 1, β = 1` and `γ = 1`.  In either case, Theorem 1 gives the
complexity to achieve a root-mean-square error of `ε` to be `O(ε⁻²(log ε)²)`"). -/
theorem em_complexity (ε : ℝ) :
    complexityBound 1 1 1 ε = ε ^ (-2 : ℝ) * Real.log ε ^ 2 ∧
      complexityBound 2 2 2 ε = ε ^ (-2 : ℝ) * Real.log ε ^ 2 :=
  ⟨complexityBound_of_eq rfl ε, complexityBound_of_eq rfl ε⟩

end MLMC
