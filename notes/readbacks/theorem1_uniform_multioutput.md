# Read-back audit: packet 15 (round 4)

- **Date:** 2026-09-27
- **Packet:** `readback/round4/packet15.lean` (12 declarations: 6 definitions `complexityBound`, `Vb`, `Cb`, `sumSqrtVC`, `lagrangeN`, `kurtosis`; 6 theorems `giles_theorem1_of_core`, `giles_theorem1_uniform`, `multiOutput_optimal`, `integral_norm_add_sq_of_indepFun`, `integral_add_sq_of_indepFun`, `tendsto_kurtosis_atTop`)
- **Auditor:** an independent, blind sub-agent
- **Rules followed:**
  - Read only three things: the packet, `prove2me_workspace/references/mission_auditor.md`, and Mathlib sources under `.lake/packages/mathlib/Mathlib/`. I used Mathlib only to confirm definitions and conventions: `variance`/`evariance`, `IndepFun`/`Indep`/`IndepSets`, `MemLp`, `Measure.real`, `IsLeast`, `Finset.sup'`, `Pairwise`, the Bochner integral's junk values, the `Real.rpow`/`Real.sqrt`/`Real.log` conventions, the precedence of `∑`, and `Measure.infinitePi` for a witness.
  - Did not open any project source, `docs/`, `notes/`, README, PLAN, metadata, scripts, git history, paper or web page. Did not infer meaning from declaration names.
  - Translated what the code says, not what it may intend. Accounted for every binder and hypothesis, surfaced degenerate and junk cases, and kept the exact strength of every connective (< vs ≤, ∃ vs ∀, quantifier order).
  - Checked truth and non-vacuity by hand proof sketches plus pure-Python numeric checks (script `readback/round4/work15/checks.py`; no third-party libraries). No Lean was run.
  - Section 1 of each entry is a literal rendering without judgement. Assessment is confined to sections 2–5. Following this request, I used Unicode math (no LaTeX) instead of the KaTeX that the mission file suggests.

## Conventions used in all renderings

- ℕ = {0, 1, 2, …}. `range (L+1)` = {0, 1, …, L}. A sum Σ_{ℓ=0}^{L} is over that set.
- **Precedence of `∑`.** Mathlib parses the body of `∑` at level 67, which is between `+`/`-` (65) and `*`/`/` (70); Mathlib's library note "operator precedence of big operators" confirms this. So `∑ ℓ ∈ s, Y ℓ (N ℓ) ω - μ[P]` means (Σ_ℓ Y_ℓ,N_ℓ(ω)) − E[P], with E[P] subtracted once, while `∑ ℓ ∈ s, a ℓ / b ℓ` and `∑ ℓ ∈ s, a ℓ * b ℓ` are sums of quotients and products.
- **Real powers.** x^y with a real exponent is `Real.rpow`. For x > 0 it equals exp(y·log x). Also 0^y = 0 for y ≠ 0, and a negative base gives a junk value. Every power in this packet has base 2 or base ε > 0, except inside the definition of `complexityBound` itself.
- **Total-function conventions.** x/0 = 0 and 0⁻¹ = 0. √x = 0 for x ≤ 0. log 0 = 0 and log x = log|x|.
- **Expectation.** E[f] or ∫ f dμ (Lean `μ[f]`) is the Bochner integral. It is 0 if f is not μ-integrable, or if the target space is not complete.
- **Variance.** Var(X) (Lean `variance X μ`) is the real part (`toReal`) of the extended-valued integral ∫⁻ |X − E[X]|² dμ. For X ∈ L² on a finite measure it is the usual variance. It is 0 when that integral is +∞, for example when X ∉ L² on a probability space.
- **Independence.** `IndepFun f g μ` means that the σ-algebras σ(f) = f⁻¹(Borel) and σ(g) are independent: μ(A ∩ B) = μ(A)·μ(B) for all A ∈ σ(f) and B ∈ σ(g).
- **Lᵖ membership.** `MemLp f 2 μ` means f is a.e.-strongly measurable and ∫|f|² dμ < ∞; it is written f ∈ L²(μ) below.
- **Other notation.** `Pairwise R` means R(i, j) for all i ≠ j. `μ.real S` = μ(S) converted to a real, with ∞ ↦ 0. `Tendsto f atTop atTop` means f(ℓ) → +∞. `Tendsto g atTop (𝓝 0)` means g(ℓ) → 0.
- **Abbreviation.** CB(ε) is short for `complexityBound α β γ ε` (declaration 1).

---

## 1. `complexityBound` (definition)

**1. Rendering.** For real numbers α, β, γ, ε:

  CB(α, β, γ, ε) =
  - ε^(−2), if γ < β;
  - ε^(−2) · (log ε)², if β = γ (and not γ < β);
  - ε^(−2 − (γ − β)/α), otherwise (that is, γ > β).

Here log is the natural logarithm and the powers are real powers. The branches are tested in the order shown.

**2. Truth check.** This is a definition, so there is nothing to prove.

**3. Non-vacuity.** For 0 < ε < e⁻¹ every branch is strictly positive. In the middle branch, (log ε)² > 1 because |log ε| > 1.

**4. Junk values.**
- For ε ≤ 0 the value is a convention. For example, at ε = 0 the first branch gives 0^(−2) = 0 and the middle branch gives 0.
- For α = 0 the exponent (γ − β)/0 is 0, so the last branch silently becomes ε^(−2).
- Neither case arises in this packet: every use has ε > 0. `giles_theorem1_uniform` also assumes α > 0. In `giles_theorem1_of_core`, α is unconstrained, but CB appears in the same form in the hypothesis and in the conclusion.

**5. Concerns.** None beyond these conventions.

## 2. `Vb` (definition)

**1. Rendering.** For real β, c₂ and ℓ ∈ ℕ: Vb(β, c₂, ℓ) = c₂ · 2^(−β·ℓ).

**2–4. Checks.** Nothing to prove, no junk (the base 2 is positive), total for all inputs.

**5. Concerns.** None.

## 3. `Cb` (definition)

**1. Rendering.** For real γ, c₃ and ℓ ∈ ℕ: Cb(γ, c₃, ℓ) = c₃ · 2^(γ·ℓ).

**2–4. Checks.** Nothing to prove, no junk.

**5. Concerns.** None.

---

## 4. `giles_theorem1_of_core` (theorem)

**1. Rendering.**

*Setting and binders.*
- (Ω, 𝓕) is a measurable space (Ω is any type) and μ is a probability measure on it.
- P : Ω → ℝ, P_ℓ : Ω → ℝ for ℓ ∈ ℕ, and Y(ℓ, n) : Ω → ℝ for ℓ, n ∈ ℕ are arbitrary functions.
- V, C : ℕ → ℝ are arbitrary sequences.
- α, β, γ, c₁, c₂, c₃, c₄ are arbitrary reals. No sign or order constraints are assumed.

*Hypotheses.*
- **(hcore)** For every real ε with 0 < ε < e⁻¹ there exist L ∈ ℕ and N : ℕ → ℕ with N_ℓ ≥ 1 for **all** ℓ ∈ ℕ such that both of these hold:

      (c₁ · 2^(−αL))² + Σ_{ℓ=0}^{L} c₂·2^(−βℓ) / N_ℓ  <  ε²
      Σ_{ℓ=0}^{L} N_ℓ · c₃·2^(γℓ)  ≤  c₄ · CB(α, β, γ, ε)

- **(hP)** P is μ-integrable. **(hPℓ)** Every P_ℓ is μ-integrable.
- **(hY)** Y(ℓ, n) ∈ L²(μ) for all ℓ and all n ≥ 1.
- **(hind)** For every N : ℕ → ℕ with all N_ℓ ≥ 1, and all i ≠ j in ℕ, the variables Y(i, N_i) and Y(j, N_j) are independent under μ. This is equivalent to: Y(i, n) and Y(j, m) are independent for all i ≠ j and all n, m ≥ 1. Only pairwise independence is assumed.
- **(h_i)** |E[P_ℓ − P]| ≤ c₁ · 2^(−αℓ) for every ℓ.
- **(h_ii₀)** E[Y(0, n)] = E[P_0] for every n ≥ 1.
- **(h_ii)** E[Y(ℓ+1, n)] = E[P_{ℓ+1} − P_ℓ] for every ℓ and every n ≥ 1.
- **(h_var)** Var(Y(ℓ, n)) = V_ℓ / n for every ℓ and every n ≥ 1.
- **(h_iii)** V_ℓ ≤ c₂ · 2^(−βℓ) for every ℓ.
- **(h_iv)** C_ℓ ≤ c₃ · 2^(γℓ) for every ℓ.

*Conclusion.* For every real ε with 0 < ε < e⁻¹ there exist L ∈ ℕ and N : ℕ → ℕ with N_ℓ ≥ 1 for all ℓ such that:

      E[ ( Σ_{ℓ=0}^{L} Y(ℓ, N_ℓ) − E[P] )² ]  <  ε²
      Σ_{ℓ=0}^{L} N_ℓ · C_ℓ  ≤  c₄ · CB(α, β, γ, ε)

Here C_ℓ is the deterministic sequence, and E[P] is subtracted once from the whole sum.

**What `hcore` asserts.** It is a purely deterministic statement about the seven numbers (α, β, γ, c₁, c₂, c₃, c₄). It mentions none of Ω, μ, P, P_ℓ, Y, V or C. It says that for each ε ∈ (0, e⁻¹) one can choose a level L and positive integer sample sizes N_ℓ such that two conditions hold:
- the squared bias bound (c₁·2^(−αL))² plus the variance bound Σ Vb(β, c₂, ℓ)/N_ℓ is below ε²;
- the cost bound Σ N_ℓ · Cb(γ, c₃, ℓ) is at most c₄ · CB(ε).

In other words, hcore is the whole numerical core of an MLMC complexity theorem, taken as an assumption. The theorem assumes none of the usual side conditions (α, β, γ > 0, α ≥ ½·min(β, γ), constants positive); whether hcore holds for given constants is left to the user of the lemma.

**2. Truth check: true.** The conclusion follows from the hypotheses, using the same L and N that hcore provides.
- *Cost.* Each N_ℓ ≥ 0 and C_ℓ ≤ c₃·2^(γℓ), so Σ N_ℓ C_ℓ ≤ Σ N_ℓ c₃ 2^(γℓ) ≤ c₄·CB(ε).
- *Mean-square error, setup.* Let Z_ℓ = Y(ℓ, N_ℓ), which is in L² because N_ℓ ≥ 1, and let S = Σ_{ℓ≤L} Z_ℓ ∈ L². Then E[(S − E P)²] = Var(S) + (E S − E P)².
- *Variance part.* Pairwise independence together with L² gives Var(S) = Σ Var(Z_ℓ); this is Mathlib's `IndepFun.variance_sum`. That sum is Σ V_ℓ/N_ℓ ≤ Σ c₂ 2^(−βℓ)/N_ℓ.
- *Bias part.* Linearity applies because P and every P_ℓ are integrable. So E S = E P_0 + Σ_{ℓ<L}(E P_{ℓ+1} − E P_ℓ) = E P_L, which telescopes. Hence (E S − E P)² = (E[P_L − P])² ≤ (c₁ 2^(−αL))².
- *Combining.* The MSE is at most the left side of hcore, which is < ε².

**3. Non-vacuity.** All hypotheses can hold together.
- *(a) Trivial witness.* Take Ω a one-point space with the Dirac measure, all functions and sequences 0, and c₁ = c₂ = c₃ = c₄ = 0 (hcore then reads 0 < ε² and 0 ≤ 0).
- *(b) Non-degenerate witness: constants.* Take α = 1, β = 2, γ = 1, c₁ = c₂ = c₃ = 1, c₄ = 30, so CB(ε) = ε^(−2).
- *(b) hcore by hand.* Let L be the least integer ≥ 0 with 4^(−L) ≤ ε²/2; then 2^L < 2√2/ε. Let N_ℓ = ⌈7 ε^(−2) 2^(−3ℓ/2)⌉.
  - Variance term: Σ 4^(−ℓ)/N_ℓ ≤ (ε²/7)·Σ 2^(−ℓ/2) < 0.488 ε², so bias² + variance < ε².
  - Cost term: Σ N_ℓ 2^ℓ ≤ 7ε^(−2)·3.414 + 2^(L+1) < 23.9 ε^(−2) + 5.66 ε^(−1) < 30 ε^(−2).
  - Numerically, over 1200 values of ε in [e⁻¹·10⁻¹², e⁻¹): the largest ratio MSE-bound/ε² is 0.987 and the largest ratio cost/ε^(−2) is 23.9.
- *(b) Probability space and data.* Take Ω = [0, 1] with Lebesgue measure and i.i.d. fair signs ξ₀, ξ₁, … (binary digits). Alternatively take Ω = {±1}^ℕ with Mathlib's `Measure.infinitePi`. Then set:
  - P ≡ 0 and P_ℓ ≡ 2^(−ℓ);
  - Y(0, n) = 1 + ξ₀/√n, and Y(ℓ+1, n) = −2^(−(ℓ+1)) + 2^(−(ℓ+1))·ξ_{ℓ+1}/√n;
  - V_ℓ = 4^(−ℓ) and C_ℓ = 2^ℓ.

  Every hypothesis holds, most of them with equality.
- *Extremal data for general constants.* For c₁, c₂ ≥ 0 and any α, β, γ, c₃, take:
  - P ≡ 0 and P_ℓ ≡ c₁2^(−αℓ);
  - Y(0, n) = c₁ + √(c₂/n)·ξ₀, and Y(ℓ+1, n) = c₁(2^(−α(ℓ+1)) − 2^(−αℓ)) + √(c₂2^(−β(ℓ+1))/n)·ξ_{ℓ+1};
  - V_ℓ = c₂2^(−βℓ) and C_ℓ = c₃2^(γℓ).

  On this data the conclusion's MSE is exactly the left side of hcore, and its cost is exactly hcore's cost. So hcore is also **necessary** for the conclusion to hold on all admissible data. It has exactly the right strength; it is not a hidden over-strong assumption.

**4. Junk values.** None. The MSE integrand is integrable because S ∈ L². Each Var(Y(ℓ, n)) with n ≥ 1 is a genuine variance because Y(ℓ, n) ∈ L². E[P] and E[P_ℓ] are genuine because these functions are integrable. The cost in the conclusion is a finite deterministic sum. There is one degenerate edge: if c₁ < 0 then (h_i) cannot hold, and if c₂ < 0 then (h_var) together with (h_iii) cannot hold, since Var ≥ 0 forces V_ℓ ≥ 0. For those parameter values the theorem is vacuously true, which is harmless.

**5. Concerns.**
- This is a **reduction lemma**. All the quantitative content (the choice of L and N, the existence of c₄, the role of α ≥ ½min(β, γ), of ε < e⁻¹ and of the log factor) sits in the hypothesis hcore. The lemma itself only adds the bias–variance decomposition and the cost comparison. It should not be read as the complexity theorem on its own; `giles_theorem1_uniform` is the self-contained form.
- *Modelling of Y.* Y(ℓ, n) is an abstract random variable with prescribed mean and variance exactly V_ℓ/n. Nothing says it is an average of n samples.
- *Modelling of C.* C_ℓ is a deterministic number bounded only from above, so it may be negative.
- *Independence.* Only pairwise independence across levels is assumed, and it is required for every positive allocation N.
- N_ℓ ≥ 1 is also required for ℓ > L. This is harmless.

**Verdict:** OK (note).

---

## 5. `giles_theorem1_uniform` (theorem)

**1. Rendering.**

*Outer binders and assumptions.* Let α, β, γ, c₁, c₂, c₃ be real numbers with α > 0, β > 0, γ > 0, c₁ > 0, c₂ > 0, c₃ > 0 and min(β, γ)/2 ≤ α. Then **there exists a real c₄ > 0** such that the statement below holds.

*Inner binders.* The statement ranges over:
- every type Ω in the fixed universe u, every σ-algebra on Ω, and every probability measure μ on Ω;
- all functions P : Ω → ℝ, P_ℓ : Ω → ℝ, Y(ℓ, n) : Ω → ℝ and Cost(ℓ, n) : Ω → ℝ (ℓ, n ∈ ℕ);
- all sequences V, C : ℕ → ℝ.

*Inner hypotheses.*
1. P is integrable.
2. Every P_ℓ is integrable.
3. Y(ℓ, n) ∈ L² for n ≥ 1.
4. For every N : ℕ → ℕ with all N_ℓ ≥ 1, Y(i, N_i) and Y(j, N_j) are independent for all i ≠ j.
5. Cost(ℓ, n) is integrable for n ≥ 1.
6. E[Cost(ℓ, n)] = n · C_ℓ for n ≥ 1.
7. |E[P_ℓ − P]| ≤ c₁2^(−αℓ).
8. E[Y(0, n)] = E[P_0] for n ≥ 1.
9. E[Y(ℓ+1, n)] = E[P_{ℓ+1} − P_ℓ] for n ≥ 1.
10. Var(Y(ℓ, n)) = V_ℓ/n for n ≥ 1.
11. V_ℓ ≤ c₂2^(−βℓ).
12. C_ℓ ≤ c₃2^(γℓ).

Each of these holds for all ℓ.

*Inner conclusion.* If hypotheses 1–12 hold, then for every ε with 0 < ε < e⁻¹ there exist L ∈ ℕ and N : ℕ → ℕ with all N_ℓ ≥ 1 such that:

      E[ ( Σ_{ℓ=0}^{L} Y(ℓ, N_ℓ) − E[P] )² ]  <  ε²
      E[ Σ_{ℓ=0}^{L} Cost(ℓ, N_ℓ) ]  ≤  c₄ · CB(α, β, γ, ε)

**Quantifier order: what c₄ may depend on.**
- ∃ c₄ comes after α, β, γ, c₁, c₂, c₃ and their hypotheses. It comes before Ω, μ, P, P_ℓ, Y, Cost, V, C and ε.
- So c₄ may depend only on (α, β, γ, c₁, c₂, c₃), and formally on the universe level u. The u-dependence is harmless: pushing a space up a universe (via `ULift`) preserves every hypothesis and the conclusion, so the c₄ for level u also serves every lower level.
- c₄ is uniform over all probability spaces and data, and over all ε ∈ (0, e⁻¹).
- L and N are chosen last, so they may depend on the data and on ε. In fact they need only ε and the constants.

**Satisfiability of the inner hypothesis set: satisfiable.**
- *(a) Degenerate witness.* Take Ω = a one-point type in universe u (for example `PUnit`) with the Dirac measure, P = P_ℓ = Y = Cost ≡ 0 and V = C ≡ 0. All 12 hypotheses hold for any positive constants. The conclusion becomes 0 < ε² and 0 ≤ c₄·CB(ε), which is true because CB(ε) > 0.
- *(b) Non-degenerate "extremal" witness, for any admissible constants.*
  - Probability space: Ω = {±1}^ℕ with the fair-coin product measure (`Measure.infinitePi`, lifted to universe u). ξ_ℓ are the coordinates, which are independent.
  - Data: P ≡ 0 and P_ℓ ≡ c₁2^(−αℓ); Y(0, n) = c₁ + √(c₂/n)ξ₀, and Y(ℓ+1, n) = c₁(2^(−α(ℓ+1)) − 2^(−αℓ)) + √(c₂2^(−β(ℓ+1))/n)·ξ_{ℓ+1}; V_ℓ = c₂2^(−βℓ), C_ℓ = c₃2^(γℓ) and Cost(ℓ, n) ≡ n·C_ℓ.
  - Every hypothesis holds; 7, 10, 11 and 12 hold with equality.
  - On this data the conclusion says exactly: ∃ L, N with (c₁2^(−αL))² + Σ c₂2^(−βℓ)/N_ℓ < ε² and Σ N_ℓ c₃2^(γℓ) ≤ c₄·CB(ε). That is the `hcore` of declaration 4. So, given declaration 4, this theorem is equivalent to "some c₄ > 0 satisfies hcore for these constants".

**2. Truth check: true.** This is the standard multilevel argument, with the core proved as follows. Write v_ℓ = c₂2^(−βℓ) and k_ℓ = c₃2^(γℓ).
- *Choice of L.* Let L be the least integer with (c₁2^(−αL))² ≤ ε²/2. Then 2^(αL) ≤ A/ε with A = max(1, 2^α√2·c₁).
- *Choice of N.* Let S = Σ_{k≤L} √(v_k k_k) and N_ℓ = ⌈3ε^(−2)·√(v_ℓ/k_ℓ)·S⌉. The variance term is then ≤ ε²/3, so the MSE is < ε².
- *Cost split.* The cost is at most 3ε^(−2)S² + Σ_{ℓ≤L} k_ℓ.
- *First term, by regime.*
  - β > γ: S is bounded, so the term is ≤ const·ε^(−2).
  - β = γ: S = √(c₂c₃)(L+1) and L + 1 ≤ const·|log ε|, which uses |log ε| > 1. So the term is ≤ const·ε^(−2)(log ε)².
  - β < γ: S² ≤ const·2^((γ−β)L) ≤ const·ε^(−(γ−β)/α).
- *Second term.* It is ≤ const·ε^(−γ/α). This is dominated by CB(ε) exactly because α ≥ ½min(β, γ):
  - if β ≥ γ, then γ/α ≤ 2;
  - if β < γ, then γ/α ≤ 2 + (γ−β)/α, which is equivalent to β ≤ 2α.
- *Uniformity.* All constants depend only on (α, β, γ, c₁, c₂, c₃).
- *Transfer to the data.* By hypotheses 5, 6 and 12, E[Σ Cost] = Σ N_ℓ C_ℓ ≤ Σ N_ℓ k_ℓ. The MSE is handled as in declaration 4.
- *Numeric check.* With this construction, the ratio cost/CB(ε) stays bounded for ε from 0.3 down to 10⁻¹⁰ in all regimes. Sample parameter sets gave about 20–35 (β > γ), 8–54 (β = γ), 80–130 (β < γ) and about 10³ at the edge α = β/2.
- *Hypotheses that cannot be dropped.* When α < ½min(β, γ) the ratio blows up, like 10²⁰ at ε = 10⁻¹⁰. On the extremal data this blow-up is forced: every level ℓ ≤ L needs N_ℓ ≥ 1, so the cost is at least c₃2^(γL), while the bias forces 2^L ≳ ε^(−1/α). Hence the assumption α ≥ ½min(β, γ) cannot be dropped. The assumption α > 0 is redundant: β, γ > 0 give min(β, γ)/2 > 0, and α ≥ min(β, γ)/2.

**3. Non-vacuity.** The outer hypotheses are satisfiable, for example (α, β, γ, c₁, c₂, c₃) = (1, 2, 1, 1, 1, 1). The inner hypotheses are satisfiable by witnesses (a) and (b) above.

**4. Junk values.** None. The MSE integrand is the square of an L² function minus a constant, so it is integrable. The cost integrand is a finite sum of integrable functions, so E[Σ Cost] = Σ N_ℓ C_ℓ is genuine. The variances are genuine (L²). CB(ε) is evaluated at ε > 0 with α > 0.

**5. Concerns (notes only).**
- *Cost.* Only the **expected** total cost is bounded. Cost is tied to the rest of the data only through E[Cost(ℓ, n)] = n·C_ℓ, with no link to Y. C_ℓ may be negative.
- *Modelling.* Same abstractions as declaration 4: Y(ℓ, n) is an abstract variable with variance exactly V_ℓ/n for every n, and only pairwise independence across levels is assumed.
- *Universe.* Ω ranges over a single universe u per instance, which is harmless.
- *Redundant hypothesis.* The assumption α > 0 follows from the others, as explained in the truth check.

**Verdict:** OK (note).

---

## 6. `sumSqrtVC` (definition)

**1. Rendering.** For any index type ι, a finite set s ⊆ ι and V, C : ι → ℝ: sumSqrtVC(s, V, C) = Σ_{i∈s} √(V_i · C_i).

**2–3. Checks.** It is a definition; the empty s gives 0.

**4. Junk values.** Any term with V_i·C_i < 0 silently contributes 0.

**5. Concerns.** None for the use in this packet, where all inputs are positive.

**Verdict:** OK (note: junk √ for negative products).

## 7. `lagrangeN` (definition)

**1. Rendering.** For s, V, C as in declaration 6, a real τ and an index i ∈ ι (i need not lie in s):

  lagrangeN(s, V, C, τ, i) = τ⁻¹ · √(V_i / C_i) · Σ_{k∈s} √(V_k C_k).

For positive V, C and τ this is the classical Lagrange-multiplier minimiser of Σ n_i C_i subject to Σ V_i/n_i = τ.

**4. Junk values.**
- τ = 0 gives τ⁻¹ = 0, so the value is 0.
- C_i = 0 gives V_i/C_i = 0.
- A negative ratio gives √ = 0.

**5. Concerns.** None for the use in this packet (τ = ½, positive V and C).

**Verdict:** OK (note).

---

## 8. `multiOutput_optimal` (theorem)

**1. Rendering.**

*Binders.*
- κ is any type and M ⊆ κ is a nonempty finite set.
- V : ℕ × κ → ℝ is written V_{ℓ,m}, C : ℕ → ℝ and ε : κ → ℝ.
- Positivity: ε_m > 0 for m ∈ M, V_{ℓ,m} > 0 for all ℓ ∈ ℕ and m ∈ M, and C_ℓ > 0 for all ℓ ∈ ℕ.
- L ∈ ℕ.

*Derived quantities.*
- W_ℓ := max_{m∈M} V_{ℓ,m}/ε_m². This is `Finset.sup'`, a genuine maximum over the nonempty M, and it is > 0.
- S := Σ_{ℓ=0}^{L} √(W_ℓ C_ℓ).
- n*_ℓ := lagrangeN({0..L}, W, C, ½, ℓ) = 2·√(W_ℓ/C_ℓ)·S.

*Conclusion.* All four of the following hold:
- **(a) Minimum.** 2S² is the least element (`IsLeast`: it belongs to the set and is ≤ every element) of the set

      { Σ_{ℓ=0}^{L} n_ℓ C_ℓ  :  n : ℕ → ℝ,  n_ℓ > 0 for ℓ ≤ L,  Σ_{ℓ=0}^{L} W_ℓ / n_ℓ ≤ ½ }.

  The sample sizes n are real-valued, and values of n beyond L are irrelevant.
- **(b) Positivity.** n*_ℓ > 0 for every ℓ ∈ {0, …, L}.
- **(c) Cost of n\*.** Σ_{ℓ=0}^{L} n*_ℓ · C_ℓ = 2S².
- **(d) Per-output bound.** For every m ∈ M: Σ_{ℓ=0}^{L} V_{ℓ,m} / n*_ℓ ≤ ε_m²/2.

**2. Truth check: true.**
- *(a) Lower bound.* By Cauchy–Schwarz, S² = (Σ √(W_ℓ/n_ℓ)·√(n_ℓC_ℓ))² ≤ (Σ W_ℓ/n_ℓ)(Σ n_ℓC_ℓ) ≤ ½·Σ n_ℓC_ℓ.
- *(a) Attainment.* The bound is attained at n*: Σ W_ℓ/n*_ℓ = ½ exactly, and the cost is 2S².
- *(b)* S > 0 because it is a nonempty sum of positive terms.
- *(c)* √(W/C)·C = √(WC).
- *(d)* V_{ℓ,m} ≤ ε_m²·W_ℓ, so the sum is ≤ ε_m²·Σ W_ℓ/n*_ℓ = ε_m²/2.
- *Numeric check.* 300 random instances with up to 4 outputs and L ≤ 5 all passed (a)–(d). Against 60,000 random feasible n, the smallest ratio cost/(2S²) was 1.000000.

**3. Non-vacuity.** Take κ a one-point type, M = {∗}, V ≡ C ≡ ε ≡ 1 and L = 0. Then W₀ = 1, the set is {n₀ : n₀ ≥ 2}, and its minimum 2 equals 2·1².

**4. Junk values.** None. Every quantity is positive, the maximum is genuine, and τ = ½ ≠ 0.

**5. Concerns.**
- **Aggregated constraint.** Optimality in (a) is only for the single aggregated constraint Σ_ℓ max_m(V_{ℓ,m}/ε_m²)/n_ℓ ≤ ½. That constraint implies the per-output constraints Σ_ℓ V_{ℓ,m}/n_ℓ ≤ ε_m²/2 (m ∈ M) but is strictly stronger than them. The theorem shows n* is *feasible* for the per-output constraints (d). It does **not** show n* is optimal for the per-output problem, and in general it is not.
- **Counterexample to per-output optimality.** Take M = {1, 2}, L = 1, C = (1, 1), ε ≡ 1, V_{0,1} = V_{1,2} = 1 and V_{1,1} = V_{0,2} = 10⁻³. The `IsLeast` value is 8, while the per-output optimum is about 4.004.
- Sample sizes are real numbers (a continuous relaxation), not integers.
- The positivity assumptions on V and C are imposed for all ℓ ∈ ℕ, although only ℓ ≤ L matters. This is harmless.

**Verdict:** OK (note).

---

## 9. `integral_norm_add_sq_of_indepFun` (theorem)

**1. Rendering.**
- **Setting.** (Ω, μ) is a probability space. E is a real inner-product space that is complete (a real Hilbert space), with a σ-algebra equal to its Borel σ-algebra.
- **Hypotheses.** a, b : Ω → E are independent under μ, a ∈ L²(μ; E), b ∈ L²(μ; E), and the Bochner integral ∫ a dμ = 0 (only a is centred).
- **Conclusion.**

      ∫ ‖a + b‖² dμ = ∫ ‖a‖² dμ + ∫ ‖b‖² dμ.

**2. Truth check: true.**
- *Expansion.* Pointwise, ‖a+b‖² = ‖a‖² + 2⟨a, b⟩ + ‖b‖². All three terms are integrable, since |⟨a, b⟩| ≤ ½(‖a‖² + ‖b‖²).
- *Cross term.* E⟨a, b⟩ = ⟨E a, E b⟩ = 0. This holds even when E is not separable. Both a and b are a.e. separably valued, so expand ⟨a, b⟩ = Σ_k ⟨a, e_k⟩⟨b, e_k⟩ in an orthonormal basis of a separable closed subspace containing their values. Each term is a product of independent real L² variables, with expectation ⟨E a, e_k⟩⟨E b, e_k⟩ = 0. Pass to the limit by dominated convergence, since the partial sums are bounded by ‖a‖·‖b‖.
- *Numeric check.* Exact rational checks on 200 random finite product spaces in ℚ² all passed. Without centring, the identity fails by 2⟨E a, E b⟩; one example gives a difference of 8, so hypothesis ha0 is genuinely needed.

**3. Non-vacuity.** Take E = ℝ, Ω = {±1}² with the uniform measure, a = the first coordinate and b = the second coordinate + 5.

**4. Junk values.** None. Because E is complete and a ∈ L² ⊆ L¹, the condition ∫ a = 0 is a genuine centring condition, not the Bochner junk value. The norm-squared integrands are integrable.

**5. Concerns.** None. The σ-algebra on E and the Borel assumption are there only to define independence.

**Verdict:** OK.

## 10. `integral_add_sq_of_indepFun` (theorem)

**1. Rendering.** Let (Ω, μ) be a probability space, and let a, b : Ω → ℝ be independent under μ with a, b ∈ L²(μ) and E[a] = 0. Then

      E[(a + b)²] = E[a²] + E[b²].

The inner-product-space variable E from the enclosing section is not mentioned in the statement, so it is not a binder of this theorem.

**2. Truth check: true.** Expand the square; the cross term E[ab] = E[a]E[b] = 0 by independence and L² integrability.

**3. Non-vacuity.** Use the same witness as in declaration 9 with values in ℝ.

**4. Junk values.** None.

**5. Concerns.** None.

**Verdict:** OK.

---

## 11. `kurtosis` (definition)

**1. Rendering.** For a measurable space Ω₀, any measure ν on it (not necessarily a probability measure) and X : Ω₀ → ℝ:

      kurtosis(X, ν) = ( ∫ X⁴ dν ) / ( ∫ X² dν )².

**4. Junk values.**
- If ∫ X² dν = 0 (for example X = 0 a.e.), or if X² is not integrable, the denominator is 0 and the value is 0.
- If X⁴ is not integrable while X² is, the value is also 0.

**5. Concerns.**
- This is the **non-central** fourth-moment ratio E[X⁴]/(E[X²])², moments about 0.
- It is not the usual kurtosis E[(X − E X)⁴]/Var(X)²; the two agree when E X = 0.
- The measure need not be normalised.

**Verdict:** OK (note).

## 12. `tendsto_kurtosis_atTop` (theorem)

**1. Rendering.**
- **Setting.** (Ω, 𝓕) is a measurable space and μ is any measure on it. There is no probability or finiteness assumption.
- **Binders.** X_ℓ : Ω → ℝ for ℓ ∈ ℕ.
- **Hypotheses.**
  - Each X_ℓ is measurable.
  - X_ℓ(ω) ∈ {−1, 0, 1} for all ℓ and ω.
  - For each ℓ the real number μ.real{X_ℓ ≠ 0} is > 0. This forces 0 < μ{X_ℓ ≠ 0} < ∞, because infinite measure converts to 0.
  - ∫ X_ℓ² dμ → 0 as ℓ → ∞.
- **Conclusion.** kurtosis(X_ℓ, μ) = (∫ X_ℓ⁴ dμ)/(∫ X_ℓ² dμ)² → +∞ as ℓ → ∞. That is, for every M there is ℓ₀ with kurtosis(X_ℓ, μ) ≥ M for all ℓ ≥ ℓ₀.

**2. Truth check: true.** Since X_ℓ ∈ {−1, 0, 1}, we have X_ℓ² = X_ℓ⁴ = the indicator of {X_ℓ ≠ 0}. Let p_ℓ = μ{X_ℓ ≠ 0}, which lies in (0, ∞). Then ∫X_ℓ² = ∫X_ℓ⁴ = p_ℓ and the kurtosis equals 1/p_ℓ. The last hypothesis says p_ℓ → 0 with p_ℓ > 0, so 1/p_ℓ → +∞. An exact check confirms kurtosis = 1/μ(X ≠ 0).

**3. Non-vacuity.** Take Ω = [0, 1] with Lebesgue measure and X_ℓ = the indicator of [0, 2^(−ℓ)], so p_ℓ = 2^(−ℓ).

**4. Junk values.** None. The integrals are genuine because the support has finite measure, and the denominator p_ℓ² is > 0. The hypothesis hp is exactly what excludes the junk case p_ℓ = 0, where the kurtosis would be 0/0 = 0.

**5. Concerns.**
- The result is elementary once the values are ternary: the kurtosis is just 1/p_ℓ.
- "Kurtosis" here is the non-central ratio of declaration 11.
- The statement holds for arbitrary measures.

**Verdict:** OK (note).

---

## Summary table

| Declaration | Verdict | One-line reason |
|---|---|---|
| `complexityBound` | OK (note) | Three-regime piecewise bound; junk only for ε ≤ 0 or α = 0, neither of which arises in this packet's uses. |
| `Vb` | OK | c₂·2^(−βℓ). |
| `Cb` | OK | c₃·2^(γℓ). |
| `giles_theorem1_of_core` | OK (note) | True and non-vacuous, but a reduction lemma: the deterministic hypothesis `hcore` holds the whole numerical content. It is also exactly the right strength (it is what the conclusion says on extremal data). |
| `giles_theorem1_uniform` | OK (note) | True (standard MLMC argument). c₄ depends only on (α, β, γ, c₁, c₂, c₃). Inner hypotheses are satisfiable, including a non-degenerate witness where every bound is attained. Only expected cost is bounded; Y(ℓ, n) is abstract; the assumption α > 0 is redundant. |
| `sumSqrtVC` | OK (note) | Σ √(V_i C_i); negative products silently give 0. |
| `lagrangeN` | OK (note) | τ⁻¹√(V_i/C_i)·Σ√(V_k C_k); junk for τ = 0, C_i = 0 or negative ratios. |
| `multiOutput_optimal` | OK (note) | True, but optimality is for the max-aggregated constraint with real n. For the per-output constraints n* is only shown feasible (the per-output optimum can be about half: 8 vs 4.004). |
| `integral_norm_add_sq_of_indepFun` | OK | E‖a+b‖² = E‖a‖² + E‖b‖² for independent L² Hilbert-valued a, b with E a = 0; no junk. |
| `integral_add_sq_of_indepFun` | OK | Real-valued special case; no junk. |
| `kurtosis` | OK (note) | Non-central ratio E[X⁴]/(E[X²])²; junk 0 for a zero or undefined second moment. |
| `tendsto_kurtosis_atTop` | OK (note) | For {−1, 0, 1}-valued X the kurtosis is 1/μ(X ≠ 0), which tends to +∞; arbitrary measure; no junk. |

## Overall

All 12 declarations are well formed. All six theorems are true and non-vacuous, and none of their conclusions holds only because of a junk value: every integral, variance and quotient in the conclusions is evaluated where it is genuine.

The two MLMC statements need the most care from a reader:
- **`giles_theorem1_of_core`** assumes, as hypothesis `hcore`, a purely deterministic statement about (α, β, γ, c₁, c₂, c₃, c₄): for every ε ∈ (0, e⁻¹) there are L and N ≥ 1 with bias bound² + Σ variance bound/N_ℓ < ε² and cost bound ≤ c₄·CB(ε). The lemma then transfers this to the actual estimator's MSE and cost. The transfer is correct, and hcore is exactly what the conclusion asserts on extremal data. But the lemma is not a complexity theorem by itself.
- **`giles_theorem1_uniform`** is self-contained. c₄ is chosen after the six constants and before the probability space, the data and ε, so it depends only on (α, β, γ, c₁, c₂, c₃). The inner hypotheses can all be met, both trivially and by a non-degenerate independent-coin model. The assumption α ≥ ½min(β, γ) is necessary, while α > 0 is implied by it together with β, γ > 0.

Modelling points a reviewer should be aware of:
- The per-level estimator Y(ℓ, n) is abstract; nothing says it is a sample mean.
- Independence across levels is only pairwise.
- Only the expected cost is bounded, and C_ℓ may be negative.
- `multiOutput_optimal` optimises a conservative aggregated constraint with real-valued sample sizes, not the per-output problem.
- `kurtosis` is the non-central moment ratio.
