# Blind read-back: packet 13

- **Date:** 2026-09-26
- **Packet:** `packet13.lean` (a scratch file, not in the repository): 12 declarations (3 definitions, 9 theorems). They cover:
  - multi-output sample allocation, with real-valued sample sizes;
  - Pythagoras/orthogonality identities for independent centred Hilbert-space-valued random variables;
  - the bias–variance split;
  - an MLMC MSE identity and a Hilbert-space version of the "Giles Theorem 1" complexity statement;
  - a counterexample for the sup norm on ℝ × ℝ.
- **Rules followed:**
  - I read only `packet12.lean`, `packet13.lean` and `mission_auditor.md`.
  - I used Mathlib sources under `.lake/packages/mathlib/Mathlib/` only to confirm definitions and conventions: `IndepFun`, `MemLp`, `IsLeast`, `Finset.sup'`, `Pairwise`/`Set.Pairwise`, the Bochner `integral` and its junk cases (non-integrable or non-complete codomain gives 0), the `μ[X]` macro, `Real.sqrt`, `Real.rpow`, the norm on `ℝ × ℝ` (`Prod.norm_def`: ‖(x, y)‖ = max ‖x‖ ‖y‖), the product σ-algebra, and `∑` parsing precedence (body at precedence 67).
  - I did **not** open the project's Lean files, `docs/`, `notes/`, README, PLAN, metadata, git history, papers or the web.
  - I translate the code literally. The math is plain Unicode, as the caller asked; this overrides the KaTeX style in `mission_auditor.md`.
  - Proofs are `sorry` in the packet. I sanity-checked by hand that each statement is plausibly true.

## Context and conventions (verified in Mathlib)

- **Opens:** `open MeasureTheory ProbabilityTheory Finset`, `open scoped RealInnerProductSpace`, inside `namespace MLMC`.
- **Variable context:**
  - `multiOutput_variance` and `multiOutput_optimal` are stated over an arbitrary type κ, with no instances.
  - The remaining theorems use: Ω a measurable space with a measure μ (implicit); E a real inner-product space (`NormedAddCommGroup E`, `InnerProductSpace ℝ E`). Each theorem adds its own instances (probability measure, completeness, Borel σ-algebra on E).
- **Integrals:**
  - `∫ ω, f ω ∂μ` is the Bochner integral, written E[f] below. It equals **0** when f is not integrable, and **0 for every f** when the codomain is not complete.
  - `μ[f]` is the same integral.
- **`Finset.sup'`:** `M.sup' hM g` over a nonempty finite set M of reals is max_{m∈M} g(m).
- **Pairwise conditions:**
  - `Set.Pairwise s r`: r(i, j) for all distinct i, j ∈ s.
  - `Pairwise r`: r(i, j) for all i ≠ j.
- **`IndepFun a b μ`:** μ(a⁻¹A ∩ b⁻¹B) = μ(a⁻¹A)·μ(b⁻¹B) for all measurable A, B in the codomains. For E, the codomain σ-algebra is the Borel one (`BorelSpace E`).
- **Real arithmetic:** √t = 0 for t ≤ 0; x/0 = 0; 0⁻¹ = 0.
- **Parsing:** `∑ ℓ, A ℓ - m` means (∑_ℓ A_ℓ) − m, and `∑ ℓ, ∫… ∂μ + ‖…‖²` means (∑_ℓ ∫…) + ‖…‖². I checked all statements with this rule; each parses in the sensible way.
- **Notation:** S_ℓ := max_{m∈M} V_{ℓ,m} / ε_m² (the `sup'` expression used in #4 and #5).

---

## 1. `sumSqrtVC` (definition)

**Reads as.** For a finite set s and V, C : ι → ℝ: sumSqrtVC(s, V, C) = ∑_{i∈s} √(V_i · C_i).

**Junk values.** √ of a negative product is 0, so negative V_i·C_i terms contribute 0.

**Satisfiable (witness).** n/a (definition).

**Trivial/redundant?** n/a.

**Notes.** None.

## 2. `lagrangeN` (definition)

**Reads as.** lagrangeN(s, V, C, τ)(i) = τ⁻¹ · √(V_i / C_i) · ∑_{j∈s} √(V_j C_j).

**Junk values.** Each of these gives 0 instead of an error:
- τ = 0 (τ⁻¹ = 0);
- C_i = 0 (V_i/0 = 0, so √0 = 0);
- V_i / C_i < 0.

The index i is not required to lie in s.

**Satisfiable (witness).** n/a.

**Trivial/redundant?** n/a.

**Notes.** In #5 it is used with τ = 1/2, V = S and C > 0. There it equals 2·√(S_ℓ/C_ℓ)·∑_{j≤L} √(S_j C_j) > 0, so no junk arises.

## 3. `complexityBound` (definition)

**Reads as.** The same as in packet 12. complexityBound(α, β, γ, ε) =
- ε^(−2), if γ < β;
- ε^(−2)·(ln ε)², if β = γ;
- ε^(−2−(γ−β)/α), if γ > β.

The powers are real powers.

**Junk values.** Junk arises only for ε ≤ 0 (rpow conventions), for α = 0 ((γ−β)/0 = 0), or at ε = 1 (ln 1 = 0). All are excluded where it is used (α > 0, 0 < ε < e⁻¹). There every branch is ≥ ε^(−2) > 0.

**Satisfiable (witness).** n/a.

**Trivial/redundant?** n/a.

**Notes.** None.

## 4. `multiOutput_variance`

**Reads as.** Inputs:
- κ is any type, and M ⊆ κ is a **nonempty** finite set of "outputs";
- V : ℕ → κ → ℝ is arbitrary (any sign);
- ε : κ → ℝ with ε_m > 0 for every m ∈ M;
- L ∈ ℕ;
- N : ℕ → ℝ (**real-valued**) with N_ℓ > 0 for ℓ = 0, …, L.

Hypothesis: ∑_{ℓ=0}^{L} S_ℓ / N_ℓ ≤ 1/2, where S_ℓ = max_{m∈M} V_{ℓ,m}/ε_m².

Conclusion: for every m ∈ M, ∑_{ℓ=0}^{L} V_{ℓ,m} / N_ℓ ≤ ε_m² / 2.

**Junk values.** None on the relevant indices. ε_m > 0 on M and N_ℓ > 0 on {0..L}, so no division by 0 occurs. Values of ε and N off M and off {0..L} are irrelevant. `sup'` is a genuine maximum because M is nonempty.

**Satisfiable (witness).** V ≡ 0, any positive N. Non-trivial: V ≡ 1, ε ≡ 1, N_ℓ = 2(L+1).

**Trivial/redundant?** Not trivial, but elementary. For m ∈ M, V_{ℓ,m} ≤ ε_m² S_ℓ; divide by N_ℓ and sum. Both positivity hypotheses are needed.

**Notes.** The N_ℓ are real numbers, not sample counts, and no integrality is involved. V may be negative.

## 5. `multiOutput_optimal`

**Reads as.** Inputs: M ⊆ κ nonempty and finite; V : ℕ → κ → ℝ with V_{ℓ,m} > 0 for **all** ℓ ∈ ℕ and m ∈ M; C : ℕ → ℝ with C_ℓ > 0 for all ℓ ∈ ℕ; ε_m > 0 for m ∈ M; L ∈ ℕ. S_ℓ is as in #4, so S_ℓ > 0. The conclusion is the conjunction of two parts.

- **(1) Least relaxed cost.** Let K be the set of reals ∑_{ℓ=0}^{L} n_ℓ·C_ℓ, where n : ℕ → ℝ ranges over sequences with n_ℓ > 0 for ℓ ≤ L and ∑_{ℓ=0}^{L} S_ℓ/n_ℓ ≤ 1/2. Then 2·(∑_{ℓ=0}^{L} √(S_ℓ·C_ℓ))² is the **least element** of K. That is, some feasible real n attains this cost, and no feasible real n gives a smaller cost.
- **(2) Feasibility per output.** Let n*_ℓ := lagrangeN({0..L}, S, C, 1/2)(ℓ) = 2·√(S_ℓ/C_ℓ)·∑_{j=0}^{L} √(S_j C_j). Then for every m ∈ M, ∑_{ℓ=0}^{L} V_{ℓ,m} / n*_ℓ ≤ ε_m²/2.

**Junk values.** None. S_ℓ > 0 and C_ℓ > 0, so the square roots are of positive numbers. τ = 1/2 gives τ⁻¹ = 2, and n*_ℓ > 0, so every division is genuine.

**Satisfiable (witness).** V ≡ 1, C ≡ 1 and ε ≡ 1. Then S_ℓ = 1, the minimum is 2(L+1)², attained at n_ℓ = 2(L+1) = n*_ℓ. The set K is nonempty (and IsLeast asserts membership), so the statement is not vacuous.

**Trivial/redundant?** Not trivial.
- (1) is the Cauchy–Schwarz optimum: (∑√(S_ℓC_ℓ))² ≤ (∑S_ℓ/n_ℓ)(∑n_ℓC_ℓ), with equality at n ∝ √(S/C).
- (2) follows from #4 because ∑S_ℓ/n*_ℓ = 1/2.
- Positivity of V_{ℓ,m} and C_ℓ is demanded for every ℓ ∈ ℕ, although only ℓ ≤ L matter. Harmless.

**Notes.**
- **Relaxed problem.** Sample sizes are real (a continuous relaxation), not natural numbers.
- **Parts (1) and (2) are not linked.** Part (1) does not name the minimiser. Part (2) does *not* assert that n* is feasible for the aggregated constraint of (1), nor that ∑ n*_ℓ C_ℓ equals the minimum. It asserts only the per-output variance bounds. Both of those facts are true (∑S_ℓ/n*_ℓ = 1/2, and the cost of n* is 2(∑√(S_ℓC_ℓ))²), but the statement does not claim them.

## 6. `integral_norm_add_sq_of_indepFun`

**Reads as.** Setting:
- μ is a probability measure on Ω;
- E is a **complete** real inner-product space (a real Hilbert space), carrying its Borel σ-algebra;
- a, b : Ω → E are independent under μ;
- a, b ∈ L²(μ; E) (a.e.-strongly measurable with E‖a‖² < ∞, and likewise for b);
- E[a] = 0 and E[b] = 0 (Bochner means).

Conclusion: E‖a + b‖² = E‖a‖² + E‖b‖².

**Junk values.** None.
- E is complete, so the means are genuine Bochner integrals. Without completeness they would be 0 by convention and the mean-zero hypotheses would be empty, but completeness is assumed.
- a, b ∈ L² makes ‖a‖², ‖b‖² and ‖a+b‖² integrable.

**Satisfiable (witness).**
- a = b = 0.
- Non-trivial: E = ℝ, a = X, b = Y with X, Y independent ±1 fair signs. Then 2 = 1 + 1.
- Or E = Euclidean ℝ² with a = (X, 0) and b = (0, Y). Then again 2 = 1 + 1. Compare #12.

**Trivial/redundant?** Not trivial. It needs E⟨a, b⟩ = ⟨E a, E b⟩ = 0, which uses independence. All hypotheses are used.

**Notes.** E is not assumed separable. The statement remains true: a, b are a.e. equal to strongly measurable, separably valued versions, and independence passes to a.e.-equal versions (`IndepFun.congr`).

## 7. `integral_add_sq_of_indepFun`

**Reads as.** μ is a probability measure on Ω. a, b : Ω → ℝ are independent (for the Borel σ-algebra on ℝ), both in L²(μ), with E[a] = E[b] = 0. Then E[(a + b)²] = E[a²] + E[b²].

**Junk values.** None, since L² gives integrable squares.

**Satisfiable (witness).** a = b = 0, or independent fair ±1 signs.

**Trivial/redundant?** Not trivial. It is E[ab] = E[a]E[b] = 0.

**Notes.** This is the real-valued special case of #6.

## 8. `integral_norm_sum_sq_of_indepFun`

**Reads as.** Setting: μ is a probability measure; E is a complete real inner-product space with the Borel σ-algebra; ι is any type, s ⊆ ι a finite set, and X_i : Ω → E. Hypotheses, for i ∈ s:
- X_i ∈ L²(μ; E);
- E[X_i] = 0;
- X_i and X_j are independent for all **distinct** i, j ∈ s (pairwise, not mutual, independence).

Conclusion: E‖∑_{i∈s} X_i‖² = ∑_{i∈s} E‖X_i‖².

**Junk values.** None, for the same reasons as #6.

**Satisfiable (witness).** X ≡ 0. Non-trivial: independent fair signs, with E = ℝ.

**Trivial/redundant?** Not trivial. For s = ∅ both sides are 0, and for a singleton s it is immediate. The hypotheses are only required on s.

**Notes.** Pairwise independence suffices and is all that is assumed.

## 9. `integral_norm_sub_sq_eq`

**Reads as.** μ is a probability measure on Ω, and E is a complete real inner-product space; no σ-algebra on E is needed. Let Z ∈ L²(μ; E) and m ∈ E. Then

  E‖Z − m‖² = E‖Z − E Z‖² + ‖E Z − m‖².

This is the bias–variance decomposition.

**Junk values.** None. Z ∈ L² ⊂ L¹ (probability space) and E is complete, so E Z is genuine. ‖Z − c‖² is integrable for every constant c.

**Satisfiable (witness).** Any L² random vector, for example Z = X·e with X a fair ±1 sign and e a unit vector.

**Trivial/redundant?** Not trivial, but standard. The cross term vanishes because E⟨Z − EZ, v⟩ = 0.

**Notes.** The probability-measure assumption is used: ∫‖EZ − m‖² dμ = ‖EZ − m‖² needs μ(Ω) = 1.

## 10. `mlmc_mse_hilbert`

**Reads as.** Setting: μ is a probability measure; E is a complete real inner-product space with the Borel σ-algebra. Data: Pℓ_ℓ : Ω → E and Y_ℓ : Ω → E for ℓ ∈ ℕ, L ∈ ℕ, and m ∈ E. Hypotheses:
- every Y_ℓ (all ℓ ∈ ℕ) is in L²(μ; E);
- every Pℓ_ℓ is integrable;
- Y_i and Y_j are independent for distinct i, j ∈ {0, …, L};
- E[Y_0] = E[Pℓ_0];
- E[Y_{ℓ+1}] = E[Pℓ_{ℓ+1} − Pℓ_ℓ] for **every** ℓ ∈ ℕ.

Conclusion:

  E‖(∑_{ℓ=0}^{L} Y_ℓ) − m‖² = ∑_{ℓ=0}^{L} E‖Y_ℓ − E Y_ℓ‖² + ‖E[Pℓ_L] − m‖².

The last term lies outside the sum; I checked the parsing.

**Junk values.** None. The Y_ℓ are in L², the Pℓ_ℓ are integrable, and E is complete, so every integral is genuine. The telescoping E[∑Y_ℓ] = E[Pℓ_L] uses the integrability of Pℓ.

**Satisfiable (witness).** Everything 0. Non-trivial: E = ℝ, Pℓ_ℓ = 2^(−ℓ) (constants), Y_0 = 1 + X_0 and Y_{ℓ+1} = −2^(−ℓ−1) + X_{ℓ+1}, with X_ℓ independent fair signs.

**Trivial/redundant?** Not trivial. It combines #9 and #8, applied to Y_ℓ − E Y_ℓ, with telescoping. The hypotheses on Y_ℓ and h_ii for ℓ ≥ L are more than needed (harmless).

**Notes.**
- All objects, including the "levels" Pℓ, live on the same space Ω.
- The Y_ℓ are tied to Pℓ only through their means.

## 11. `giles_theorem1_hilbert`

**Reads as.**

*Setting.* μ is a probability measure on Ω, and E is a real Hilbert space (complete inner-product space) with the Borel σ-algebra. All data are universally quantified:
- P : Ω → E and levels Pℓ_ℓ : Ω → E;
- estimators Y_{ℓ,n} : Ω → E, one for each level ℓ and sample size n;
- costs Cost_{ℓ,n} : Ω → ℝ;
- V, C : ℕ → ℝ;
- reals α, β, γ, c₁, c₂, c₃, all > 0, with min(β, γ)/2 ≤ α.

*Hypotheses.*
- P and every Pℓ_ℓ are integrable.
- Y_{ℓ,n} ∈ L²(μ; E) for n ≥ 1.
- (hind) For every N : ℕ → ℕ with all N_ℓ ≥ 1, the family (Y_{ℓ,N_ℓ})_{ℓ∈ℕ} is pairwise independent. Equivalently: Y_{i,n} and Y_{j,n′} are independent whenever i ≠ j and n, n′ ≥ 1.
- For n ≥ 1, Cost_{ℓ,n} is integrable with E[Cost_{ℓ,n}] = n·C_ℓ.
- (i) ‖E[Pℓ_ℓ − P]‖ ≤ c₁·2^(−αℓ).
- (ii₀) E[Y_{0,n}] = E[Pℓ_0] for n ≥ 1.
- (ii) E[Y_{ℓ+1,n}] = E[Pℓ_{ℓ+1} − Pℓ_ℓ] for n ≥ 1.
- (var) E‖Y_{ℓ,n} − E Y_{ℓ,n}‖² = V_ℓ / n exactly, for n ≥ 1. This forces V_ℓ ≥ 0.
- (iii) V_ℓ ≤ c₂·2^(−βℓ).
- (iv) C_ℓ ≤ c₃·2^(γℓ).

*Conclusion.* There is c₄ > 0 such that for every ε with 0 < ε < e⁻¹ there exist L ∈ ℕ and N : ℕ → ℕ, with N_ℓ ≥ 1 for all ℓ, satisfying:
- E‖∑_{ℓ=0}^{L} Y_{ℓ,N_ℓ} − E[P]‖² < ε²;
- E[∑_{ℓ=0}^{L} Cost_{ℓ,N_ℓ}] ≤ c₄·complexityBound(α, β, γ, ε).

*Quantifier order.* c₄ is chosen before ε, so it does not depend on ε. It is chosen after all the data, so it may depend on P, Pℓ, Y, Cost, V, C and μ as well as on the constants.

**Junk values.** None.
- E is complete, so E[P] and E[Y] are genuine.
- Y_{ℓ,N_ℓ} ∈ L² because N_ℓ ≥ 1, so the MSE integrand is integrable.
- V_ℓ/n has n ≥ 1.
- The costs are integrable, so the expected total cost is exactly ∑_{ℓ≤L} N_ℓ C_ℓ.
- The "n ≥ 1" guards match the conclusion's N_ℓ ≥ 1.

**Satisfiable (witness).**
- *Degenerate.* Everything 0: then (var) holds with V ≡ 0, and constants are independent.
- *Non-degenerate.* E = ℝ, and Ω = [0,1]^(ℕ×ℕ) with i.i.d. uniform coordinates U_{ℓ,k}. Take:
  - P = U_{0,0} and Pℓ_ℓ = U_{0,0} + 2^(−ℓ), so α = 1;
  - Y_{0,n} = (1/n)∑_{k<n}(U_{0,k} + 1);
  - Y_{ℓ+1,n} = −2^(−ℓ−1) + (1/n)∑_{k<n} 2^(−ℓ−1)(U_{ℓ+1,k} − ½);
  - V_0 = 1/12 and V_{ℓ+1} = 4^(−ℓ−1)/12, so β = 2;
  - Cost_{ℓ,n} = n·2^ℓ, so C_ℓ = 2^ℓ and γ = 1.

  Different levels use disjoint coordinates, so hind holds.

**Trivial/redundant?** Not trivial. It is the MLMC complexity bound, uniform in ε, and genuinely uses min(β, γ)/2 ≤ α.

**Notes.**
- **(minor concern) Constant dependence.** As in packet 12, ∃c₄ follows all the data. The statement does not give a c₄ depending only on (α, β, γ, c₁, c₂, c₃).
- **Abstract estimators.** The Y_{ℓ,n} are not required to be sample means. They are arbitrary random vectors with the right means, variance **exactly** V_ℓ/n (an equality, not ≤), and cross-level independence for every choice of sample sizes. There is no relation between Y_{ℓ,n} for different n at the same level.
- **Cost model.** Cost enters only through E[Cost_{ℓ,n}] = n·C_ℓ. C_ℓ may be negative, since (iv) is only an upper bound.
- **Other details.**
  - Independence is only pairwise.
  - Sample sizes are natural numbers.
  - The MSE bound is strict.
  - ε is restricted to (0, e⁻¹).

## 12. `sq_norm_add_of_indepFun_fails_sup`

**Reads as.** There exist a type Ω (in universe 0), a σ-algebra on Ω, a measure μ on Ω, and maps a, b : Ω → ℝ × ℝ such that all of the following hold:
- μ is a probability measure;
- a and b are independent under μ (for the product = Borel σ-algebra on ℝ × ℝ);
- a, b ∈ L²(μ);
- E[a] = E[b] = (0, 0);
- E‖a + b‖² = 1;
- E‖a‖² + E‖b‖² = 2.

Here ‖(x, y)‖ = max(|x|, |y|): Mathlib's norm on ℝ × ℝ is the **sup norm**, not the Euclidean norm.

**Junk values.** None. ℝ × ℝ is complete, so the means are genuine. L² makes ‖a‖², ‖b‖² and ‖a+b‖² integrable, so the values 1 and 2 cannot come from the "non-integrable gives 0" convention.

**Satisfiable (witness).** Ω = Bool × Bool with all subsets measurable and μ uniform (mass 1/4 each). Let s(true) = 1 and s(false) = −1, a(ω) = (s(ω₁), 0) and b(ω) = (0, s(ω₂)). Then:
- a and b are independent, bounded and centred;
- ‖a‖ = ‖b‖ = 1;
- ‖a + b‖ = max(1, 1) = 1.

So E‖a+b‖² = 1 and E‖a‖² + E‖b‖² = 2.

**What the conjuncts force.** No degenerate witness exists:
- μ must be a probability measure, so the zero measure is excluded.
- If a = 0 almost surely, then E‖a+b‖² = E‖b‖² = E‖a‖² + E‖b‖², which contradicts 1 ≠ 2. The same holds for b. So both must be genuinely random and centred.
- The conjuncts are exactly a failure of the Pythagorean identity of #6 for independent centred L² vectors.

**Trivial/redundant?** Not trivial; it is a simple explicit counterexample. It does not contradict #6, because ℝ × ℝ with the max norm is not an inner-product space.

**Notes.** The statement's truth depends essentially on Mathlib's convention that ℝ × ℝ carries the max norm. With the Euclidean norm, the same a and b give E‖a+b‖² = 2, and the conjuncts would be unsatisfiable. A reader who takes "ℝ × ℝ" to mean Euclidean ℝ² would misread it. The name ("fails_sup") and this read-back make the convention explicit.

---

## Summary table

| # | Declaration | Verdict | One-line reason |
|---|---|---|---|
| 1 | `sumSqrtVC` | OK | ∑_{i∈s} √(V_iC_i); √(negative) = 0 junk, irrelevant where used. |
| 2 | `lagrangeN` | OK | τ⁻¹√(V_i/C_i)∑√(V_jC_j); junk 0 for τ = 0 or C_i = 0, excluded where used (τ = ½, C > 0). |
| 3 | `complexityBound` | OK | Three-case rate; positive on 0 < ε < e⁻¹; junk only outside the theorems' range. |
| 4 | `multiOutput_variance` | OK | The aggregated normalised constraint implies each per-output bound; N is real-valued. |
| 5 | `multiOutput_optimal` | OK | Relaxed (real n) minimum cost 2(∑√(S_ℓC_ℓ))² is attained (IsLeast, non-empty set); (2) only asserts per-output feasibility of n*, not its optimality. |
| 6 | `integral_norm_add_sq_of_indepFun` | OK | Pythagoras for independent centred L² vectors in a real Hilbert space; completeness present (no junk). |
| 7 | `integral_add_sq_of_indepFun` | OK | Real special case of #6. |
| 8 | `integral_norm_sum_sq_of_indepFun` | OK | Finite-sum version under pairwise independence on s. |
| 9 | `integral_norm_sub_sq_eq` | OK | Bias–variance decomposition for Z ∈ L²(μ; E). |
| 10 | `mlmc_mse_hilbert` | OK | MSE = ∑ level variances + ‖E[Pℓ_L] − m‖²; bias term outside the sum (checked parsing). |
| 11 | `giles_theorem1_hilbert` | concern (minor) | Genuine, non-vacuous, no junk. c₄ comes after all data (may depend on P, Pℓ, Y, Cost, V, C, μ). Estimators are abstract, with variance exactly V_ℓ/n. |
| 12 | `sq_norm_add_of_indepFun_fails_sup` | OK | Non-degenerate counterexample (witness above); true only because ℝ × ℝ has the max norm in Mathlib. |
