# Blind read-back: packet 12

- **Date:** 2026-09-26
- **Packet:** `packet12.lean` (a scratch file, not in the repository): 20 declarations (8 definitions, 12 theorems). They cover level differences, sample means, total cost, the complexity bound, three variants of the "Giles Theorem 1" MLMC complexity statement (general corrections, fine/coarse, antithetic), Richardson extrapolation and the ML2R weights/estimator.
- **Rules followed:**
  - I read only `packet12.lean`, `packet13.lean` and `mission_auditor.md`.
  - I used Mathlib sources under `.lake/packages/mathlib/Mathlib/` only to confirm the definitions and conventions of constants the statements use: `variance`/`evariance`, `IndepFun`/`iIndepFun` (and the kernel versions), `MemLp`, `MeasurePreserving`, `IsLeast`, `IsBigO`, `𝓝[>]`, the Bochner `integral` and its junk cases, the `μ[X]` expectation macro, `Real.rpow`, `Real.sqrt`, `Finset.sup'`, `Pairwise`, the norm on `ℝ × ℝ`, and the parsing precedence of `∑`/`∏`.
  - I did **not** open the project's Lean files, `docs/`, `notes/`, README, PLAN, metadata, git history, any paper, or the web.
  - I translate what the code literally says, not an intended meaning.
  - The caller asked for plain-Unicode math, which overrides the KaTeX style in `mission_auditor.md`.
  - Proofs are `sorry` in the packet, so I did not check proofs. I did sanity-check by hand that each statement is plausibly true, and I say so where relevant.

## Conventions used below (verified in Mathlib)

- **Context:** `open MeasureTheory ProbabilityTheory Finset Filter Topology Asymptotics`, inside `namespace MLMC`.
- **Index sets:**
  - `range (L+1)` = {0, 1, …, L}.
  - `Ico ℓ (L+1)` = {ℓ, …, L}, empty if ℓ > L.
  - `Icc 1 L` = {1, …, L}, empty if L = 0.
- **Expectation macro:** `μ[X]` expands to `∫ x, X x ∂μ`, the Bochner integral, written E_μ[X] below. The Bochner integral is **0** when the integrand is not integrable (and always 0 in a non-complete codomain). All codomains here are ℝ.
- **Variance:** `variance X μ` = toReal(∫⁻ ‖X − E_μ X‖ₑ² dμ). For a finite μ and X ∈ L²(μ) this is the usual variance. It is **0 by convention** when the lintegral is +∞, for example when X is a.e.-strongly measurable but not in L².
- **L² membership:** `MemLp f 2 μ` means f is a.e.-strongly measurable and ∫|f|² dμ < ∞.
- **Measure preservation:** `MeasurePreserving f μ ν` means f is measurable and the push-forward f₊μ equals ν. If μ is a probability measure, this forces ν to be a probability measure.
- **Independence:**
  - `iIndepFun f μ` (mutual independence): for every finite index set S and measurable sets B_i, μ(⋂_{i∈S} f_i⁻¹(B_i)) = ∏_{i∈S} μ(f_i⁻¹(B_i)).
  - `IndepFun f g μ` is the same condition for two functions.
- **Parsing:** the body of `∑ x ∈ s, …` is parsed at precedence 67. So `∑ ℓ, A ℓ - B` means (∑_ℓ A_ℓ) − B, and `∑ n, a n * x ^ n + R ℓ` means (∑_n a_n xⁿ) + R_ℓ. I checked every statement below with this rule; each parses in the mathematically sensible way.
- **Real arithmetic:**
  - x/0 = 0 and 0⁻¹ = 0 in ℝ.
  - `(2:ℝ) ^ (t:ℝ)` is `Real.rpow`, which is > 0 for every real t.
  - `x ^ (n:ℕ)` is the ordinary power.
  - `2⁻¹` is the real number 1/2.
- **Notation used below:**
  - P_ℓ stands for `Pl ℓ`.
  - ΔP_ℓ := `levelDiff Pl ℓ`.
  - n_ℓ := `ml2rNode α ℓ`.
  - w_ℓ := `ml2rWeight α L ℓ`.

---

## 1. `levelDiff` (definition)

**Reads as.** Given a sequence P_0, P_1, … of functions Ω₀ → ℝ:
- ΔP_0 = P_0;
- ΔP_{ℓ+1}(y) = P_{ℓ+1}(y) − P_ℓ(y).

Consequently ∑_{ℓ=0}^{L} ΔP_ℓ = P_L pointwise, for every L.

**Junk values.** None (only subtraction).

**Satisfiable (witness).** n/a (definition).

**Trivial/redundant?** n/a.

**Notes.** No measurability or integrability is built in. Ω₀ is an arbitrary type.

## 2. `blockMean` (definition)

**Reads as.** Inputs: f : ι → Ω₀ → ℝ, a "sample map" ω : ι × ℕ → Ω → Ω₀, an index i, N ∈ ℕ and x ∈ Ω. Then

  blockMean f ω i N x = (1/N) · ∑_{n=0}^{N−1} f_i(ω_{(i,n)}(x)).

This is the sample mean of f_i over the samples ω_{(i,0)}(x), …, ω_{(i,N−1)}(x).

**Junk values.** For N = 0 the value is 0⁻¹ · (empty sum) = 0, not "undefined". Every theorem below that uses `blockMean` requires N_ℓ ≥ 1, so this never matters there.

**Satisfiable (witness).** n/a.

**Trivial/redundant?** n/a.

**Notes.** Index i uses exactly the sample indices (i, 0), …, (i, N−1). Different i therefore use disjoint sample indices.

## 3. `totalCost` (definition)

**Reads as.** totalCost cost L N x = ∑_{ℓ=0}^{L} ∑_{n=0}^{N_ℓ−1} cost_{ℓ,n}(x).

**Junk values.** None. A level with N_ℓ = 0 contributes 0.

**Satisfiable (witness).** n/a.

**Trivial/redundant?** n/a.

**Notes.** No sign restriction on cost.

## 4. `complexityBound` (definition)

**Reads as.** complexityBound(α, β, γ, ε) =
- ε^(−2), if γ < β;
- ε^(−2) · (ln ε)², if β = γ;
- ε^(−2 − (γ−β)/α), otherwise (that is, γ > β).

The exponents are real (rpow).

**Junk values.** These cases are all outside the range used by the theorems (α > 0, 0 < ε < e⁻¹):
- For ε ≤ 0, rpow conventions apply: 0^t = 0 for t ≠ 0, and a negative base gives exp(t·ln|ε|)·cos(πt).
- For α = 0 the third branch collapses to ε^(−2), because (γ−β)/0 = 0.
- At ε = 1 the middle branch is 0.

For 0 < ε < e⁻¹ every branch is ≥ ε^(−2) > 0, because (ln ε)² > 1 and ε < 1.

**Satisfiable (witness).** n/a.

**Trivial/redundant?** n/a.

**Notes.** The case order is: first γ < β, then β = γ, otherwise γ > β. The three cases are exhaustive and disjoint.

## 5. `fineCoarseDiff` (definition)

**Reads as.** For Pf, Pc : ℕ → Ω₀ → ℝ:
- D_0 = Pf_0;
- D_{ℓ+1}(y) = Pf_{ℓ+1}(y) − Pc_ℓ(y).

**Junk values.** None.

**Satisfiable (witness).** n/a.

**Trivial/redundant?** n/a.

**Notes.** At level ℓ+1 the subtracted "coarse" term is Pc_ℓ, not Pf_ℓ. Both terms are evaluated at the same point y.

## 6. `antitheticDiff` (definition)

**Reads as.** For P_ℓ = Pl ℓ and a map a : Ω₀ → Ω₀:
- A_0(y) = ½ (P_0(y) + P_0(a(y)));
- A_{ℓ+1}(y) = ½ (P_{ℓ+1}(y) + P_{ℓ+1}(a(y))) − P_ℓ(y).

**Junk values.** None (`2⁻¹` = 1/2 in ℝ).

**Satisfiable (witness).** n/a.

**Trivial/redundant?** n/a.

**Notes.** Level 0 is also antithetically averaged. The subtracted coarse term P_ℓ is evaluated at y only, not averaged over y and a(y).

## 7. `integral_fineCoarseDiff`

**Reads as.** Let Ω₀ be a measurable space and ν **any** measure on it (not assumed finite or a probability measure). Suppose:
- every Pf_ℓ and every Pc_ℓ is ν-integrable;
- ∫ Pf_ℓ dν = ∫ Pc_ℓ dν for every ℓ.

Then for every ℓ ∈ ℕ, ∫ D_ℓ dν = ∫ ΔPf_ℓ dν, where ΔPf = levelDiff Pf. Concretely:
- for ℓ = 0 both sides are ∫ Pf_0 dν;
- ∫ (Pf_{ℓ+1} − Pc_ℓ) dν = ∫ (Pf_{ℓ+1} − Pf_ℓ) dν.

**Junk values.** Every integrand is a difference of integrable functions, hence integrable. No integral is 0 merely by convention.

**Satisfiable (witness).**
- Pc = Pf, any integrable Pf.
- Non-trivial: ν = uniform on [0,1], Pf_ℓ(y) = y and Pc_ℓ(y) = 1 − y.

**Trivial/redundant?**
- The ℓ = 0 case holds by definition.
- For ℓ+1 the proof needs only Pf_ℓ, Pf_{ℓ+1} and Pc_ℓ integrable and the mean equality at ℓ. The "for all ℓ" hypotheses are stronger than needed for a fixed ℓ (harmless).
- The integrability hypotheses are genuinely needed for linearity.

**Notes.** A short consequence of linearity of the integral.

## 8. `integral_antitheticDiff`

**Reads as.** Let ν be any measure on Ω₀ and a : Ω₀ → Ω₀ measurable with a₊ν = ν. Suppose every P_ℓ is ν-integrable. Then for every ℓ, ∫ A_ℓ dν = ∫ ΔP_ℓ dν. Concretely:
- ∫ ½(P_0 + P_0∘a) dν = ∫ P_0 dν;
- ∫ [½(P_{ℓ+1} + P_{ℓ+1}∘a) − P_ℓ] dν = ∫ (P_{ℓ+1} − P_ℓ) dν.

**Junk values.** P_ℓ∘a is integrable with the same integral because a is measure-preserving. No junk.

**Satisfiable (witness).**
- a = id.
- Non-trivial: ν = standard Gaussian on ℝ, a(y) = −y, P_ℓ(y) = y + 2^(−ℓ).

**Trivial/redundant?** Not trivial. It uses the change of variables ∫ f∘a dν = ∫ f d(a₊ν).

**Notes.** ν is an arbitrary measure (possibly infinite).

## 9. `giles_theorem1_corrections`

**Reads as.**

*Setting.*
- Ω₀ is a measurable space with a measure ν (implicit).
- Ω is a measurable space with a measure μ (implicit), assumed to be a **probability** measure.
- Data, all universally quantified:
  - P : Ω₀ → ℝ;
  - P_ℓ (Pl) and Δ_ℓ (Δ), each ℕ → (Ω₀ → ℝ);
  - a sample family ω_p : Ω → Ω₀ for p ∈ ℕ×ℕ;
  - cost_{ℓ,n} : Ω → ℝ;
  - C : ℕ → ℝ;
  - reals α, β, γ, c₁, c₂, c₃, all > 0, with min(β, γ)/2 ≤ α.

*Hypotheses.*
- (hω) Each ω_p is measurable and has law ν under μ. This forces ν to be a probability measure.
- (hind) The whole family (ω_p)_{p∈ℕ×ℕ} is mutually independent under μ.
- P and every P_ℓ are ν-integrable. Every Δ_ℓ is measurable and in L²(ν).
- Every cost_{ℓ,n} is μ-integrable, with E_μ[cost_{ℓ,n}] = C_ℓ (the same for all n).
- (i) |∫ (P_ℓ − P) dν| ≤ c₁ · 2^(−αℓ) for all ℓ.
- (ii) ∫ Δ_ℓ dν = ∫ ΔP_ℓ dν for all ℓ.
- (iii) Var_ν(Δ_ℓ) ≤ c₂ · 2^(−βℓ) for all ℓ.
- (iv) C_ℓ ≤ c₃ · 2^(γℓ) for all ℓ.

*Conclusion.* There is c₄ > 0 such that for every ε with 0 < ε < e⁻¹ there exist L ∈ ℕ and N : ℕ → ℕ with N_ℓ ≥ 1 for **all** ℓ ∈ ℕ, satisfying:
- (a) E_μ[(Ŷ − ∫ P dν)²] < ε², where Ŷ(x) = ∑_{ℓ=0}^{L} (1/N_ℓ) ∑_{n=0}^{N_ℓ−1} Δ_ℓ(ω_{(ℓ,n)}(x));
- (b) E_μ[∑_{ℓ=0}^{L} ∑_{n<N_ℓ} cost_{ℓ,n}] ≤ c₄ · complexityBound(α, β, γ, ε). The left side equals ∑_{ℓ≤L} N_ℓ C_ℓ.

*Quantifier order.* c₄ is chosen before ε, so it does not depend on ε. It is chosen after all the data, so it **may** depend on P, Pl, Δ, ω, cost, C, μ, ν, not just on α, β, γ, c₁, c₂, c₃. L and N may depend on ε and on everything else.

**Junk values.** None can make (a) or (b) true by convention:
- **MSE.** Δ_ℓ ∈ L²(ν) and ω_{(ℓ,n)} has law ν, so Δ_ℓ∘ω_{(ℓ,n)} ∈ L²(μ). Hence Ŷ − const ∈ L²(μ) (μ is a probability measure), so the square is integrable and the MSE is a genuine value, not 0.
- **Variance.** Var_ν(Δ_ℓ) is the true variance, because Δ_ℓ ∈ L²(ν) and ν is a probability measure. The "0 if not L²" convention cannot trigger.
- **Other integrals.** ∫Δ_ℓ, ∫ΔP_ℓ, ∫(P_ℓ − P) and ∫P all have integrable integrands (L² ⊂ L¹ because ν is forced to be a probability measure).
- **hP matters.** Without hP, ∫(P_ℓ − P) and ∫P would be 0 by convention, and (i) would become vacuous. hP is present.
- **Cost.** The costs are integrable, so E[totalCost] = ∑_{ℓ≤L} N_ℓ C_ℓ exactly.
- **Other.** N_ℓ ≥ 1, so 1/N_ℓ is never 0⁻¹. The rpow bases (2 and ε) are > 0.

**Satisfiable (witness).**
- *Degenerate.* Ω₀ = ℝ and ν = δ₀. (Ω, μ) is any probability space and ω_p ≡ 0; constant maps are measurable, have law δ₀, and are mutually independent. Take P = P_ℓ = Δ_ℓ = 0, cost = 0, C = 0, and α = β = γ = c_i = 1.
- *Non-degenerate.* ν = uniform on [0,1]. Ω = [0,1]^(ℕ×ℕ) with the product measure, and ω_p = coordinate projections (i.i.d. uniform). Take:
  - P(y) = y and P_ℓ(y) = y + 2^(−ℓ)y², so |bias| = 2^(−ℓ)/3 and α = 1;
  - Δ_ℓ = ΔP_ℓ, with Var(ΔP_{ℓ+1}) = 4^(−ℓ−1)·(4/45), so β = 2;
  - cost_{ℓ,n} ≡ 2^ℓ = C_ℓ, so γ = 1.

  Then min(2, 1)/2 = ½ ≤ 1.

**Trivial/redundant?**
- Not trivial. The content is a cost bound with a constant uniform in ε, and it genuinely uses min(β, γ)/2 ≤ α. Without that condition the bias-driven cost ≈ ε^(−γ/α) could exceed the bound.
- hΔm (Δ_ℓ measurable) appears logically redundant. MemLp already gives a.e.-strong measurability, and replacing Δ_ℓ by a measurable ν-a.e.-equal version changes no hypothesis value and no integral in the conclusion, since ω_{(ℓ,n)}⁻¹ maps ν-null sets to μ-null sets. It is harmless.

**Notes.**
- **(minor concern) Constant dependence.** Because ∃c₄ follows all the data, the statement does not say that one c₄ works for all problem data sharing the same (α, β, γ, c₁, c₂, c₃). It is weaker than a version with c₄ = c₄(α, β, γ, c₁, c₂, c₃), although still non-trivial and uniform in ε.
- **Cost model.** Cost is *expected* cost. cost_{ℓ,n} and C_ℓ may be negative, since (iv) is only an upper bound; this only makes (b) easier. Nothing links `cost` to the samples ω.
- **Sample coupling.** The only link between Δ and Pl is equality of means (ii). Each Δ_ℓ is evaluated at one sample ω_{(ℓ,n)}, so any fine/coarse coupling lives inside Δ_ℓ.
- **Other details.**
  - Sample sizes are natural numbers.
  - The MSE bound is strict (< ε²).
  - ε ranges only over (0, e⁻¹).
  - N_ℓ ≥ 1 is demanded for every ℓ ∈ ℕ even though only ℓ ≤ L enter (harmless).
  - All hypotheses are required for every level ℓ ∈ ℕ, as appropriate since L is chosen after ε.

## 10. `giles_theorem1_fineCoarse`

**Reads as.** Same setting, quantifiers and conclusion as #9, with the correction Δ_ℓ replaced by D_ℓ = fineCoarseDiff Pf Pc ℓ. So the estimator is Ŷ(x) = ∑_{ℓ=0}^{L} (1/N_ℓ) ∑_{n<N_ℓ} D_ℓ(ω_{(ℓ,n)}(x)): level 0 uses Pf_0, and level ℓ+1 uses Pf_{ℓ+1} − Pc_ℓ at the same sample.

Hypotheses:
- P is ν-integrable.
- Every Pf_ℓ and Pc_ℓ is measurable and in L²(ν).
- ∫ Pf_ℓ dν = ∫ Pc_ℓ dν for all ℓ.
- (i) |∫ (Pf_ℓ − P) dν| ≤ c₁ 2^(−αℓ).
- (iii) Var_ν(D_ℓ) ≤ c₂ 2^(−βℓ).
- (iv) C_ℓ ≤ c₃ 2^(γℓ).
- hω, hind, and the cost hypotheses, exactly as in #9.

The conclusion is the same ∃c₄ > 0 ∀ε ∈ (0, e⁻¹) ∃L, N (N_ℓ ≥ 1) statement.

**Junk values.** D_ℓ is measurable and in L²(ν) (a difference of L² functions), so the variance is genuine. Otherwise the same as #9: no junk.

**Satisfiable (witness).**
- Degenerate: as in #9, with Pf = Pc = 0.
- Non-degenerate: ν = uniform on [0,1], i.i.d. coordinates as in #9. Take:
  - P = 0, Pf_ℓ(y) = 2^(−ℓ)y and Pc_ℓ(y) = 2^(−ℓ)(1−y), so both means are 2^(−ℓ−1);
  - D_{ℓ+1}(y) = 3·2^(−ℓ−1)y − 2^(−ℓ), with Var = (3/4)·4^(−ℓ−1), so β = 2;
  - bias 2^(−ℓ−1), so α = 1;
  - cost ≡ 2^ℓ, so γ = 1.

**Trivial/redundant?** Not trivial. hPfm and hPcm look redundant for the same reason as hΔm in #9 (harmless).

**Notes.**
- Same minor concern as #9: c₄ may depend on all data.
- The mean equality ∫Pf_ℓ = ∫Pc_ℓ at every ℓ makes the estimator's mean telescope to ∫Pf_L.
- (i) is stated for Pf.

## 11. `giles_theorem1_antithetic`

**Reads as.** Same setting, quantifiers and conclusion as #9, with Δ_ℓ replaced by A_ℓ = antitheticDiff Pl a ℓ. Extra data: a : Ω₀ → Ω₀, measurable with a₊ν = ν.

Hypotheses:
- P is ν-integrable.
- Every P_ℓ is measurable and in L²(ν).
- (i) |∫ (P_ℓ − P) dν| ≤ c₁ 2^(−αℓ).
- (iii) Var_ν(A_ℓ) ≤ c₂ 2^(−βℓ).
- (iv) C_ℓ ≤ c₃ 2^(γℓ).
- hω, hind, and the cost hypotheses, exactly as in #9.

The estimator is Ŷ(x) = ∑_{ℓ=0}^{L} (1/N_ℓ) ∑_{n<N_ℓ} A_ℓ(ω_{(ℓ,n)}(x)).

**Junk values.** P_ℓ∘a is in L²(ν) and measurable, so A_ℓ ∈ L²(ν) and its variance is genuine. Otherwise as in #9: no junk.

**Satisfiable (witness).**
- a = id, which gives A_ℓ = ΔP_ℓ for ℓ ≥ 1, with the #9 witnesses.
- Non-degenerate: ν = uniform on [0,1] and a(y) = 1 − y. Take:
  - P = 0 and P_ℓ(y) = 2^(−ℓ)y;
  - A_0 ≡ ½;
  - A_{ℓ+1}(y) = 2^(−ℓ−2) − 2^(−ℓ)y, with Var = 4^(−ℓ)/12, so β = 2;
  - α = 1 and γ = 1.

**Trivial/redundant?** Not trivial. hPlm looks redundant (a measurable modification of P_ℓ changes P_ℓ∘a only on a ν-null set). Harmless.

**Notes.**
- Same minor concern as #9 (c₄ may depend on all data).
- Level 0 of the estimator is ½(P_0 + P_0∘a), not P_0; its mean is still ∫P_0 by measure preservation.

## 12. `ml2rNode` (definition)

**Reads as.** n_ℓ(α) = 2^(−αℓ) (real power, with ℓ cast to ℝ).

**Junk values.** None. n_ℓ > 0 always, and n_0 = 1.

**Satisfiable (witness).** n/a.

**Trivial/redundant?** n/a.

**Notes.** The nodes are strictly decreasing in ℓ for α > 0, strictly increasing for α < 0, and all equal to 1 for α = 0.

## 13. `ml2rWeight` (definition)

**Reads as.** w_ℓ(α, L) = ∏_{k ∈ {0,…,L}, k ≠ ℓ} n_k / (n_k − n_ℓ).

For ℓ ≤ L and pairwise distinct nodes (α ≠ 0), this is the Lagrange basis polynomial for the nodes n_0, …, n_L evaluated at 0: ∏_{k≠ℓ} (0 − n_k)/(n_ℓ − n_k).

Examples for α = 1:
- L = 1: w = (−1, 2).
- L = 2: w = (1/3, −2, 8/3).

**Junk values.**
- If α = 0 and L ≥ 1, every factor is 1/0 = 0, so w_ℓ = 0 for all ℓ ≤ L. These are junk "weights".
- For ℓ > L nothing is erased; the product runs over all k ≤ L.
- For L = 0, w_0 = 1 (empty product).

**Satisfiable (witness).** n/a.

**Trivial/redundant?** n/a.

**Notes.** The weights are only meaningful for α ≠ 0. Every theorem below assumes α > 0.

## 14. `richardson_extrapolation`

**Reads as.** Let F : ℝ → ℝ be any function (no regularity assumed), and let P, a, α be reals with α > 0.

*Hypothesis.* There are c and δ > 0 such that |F(h) − P − a·h^α| ≤ c·h^(2α) for all 0 < h < δ. This is the literal meaning of `=O[𝓝[>] 0]` on ℝ.

*Conclusion.* There are c′ and δ′ > 0 such that |(2^α F(h) − F(2h)) / (2^α − 1) − P| ≤ c′·h^(2α) for all 0 < h < δ′.

**Junk values.**
- 𝓝[>]0 is a non-trivial filter on ℝ, so the O-statements are not vacuous.
- Only h ∈ (0, δ) matter, so h^α is the ordinary positive power.
- 2^α − 1 > 0, so there is no division by zero.
- Values of F at h ≤ 0 or far from 0 are irrelevant.

**Satisfiable (witness).** F(h) = P + a h^α (the hypothesis holds with c = 0). Also F(h) = P + a h^α + b h^(2α).

**Trivial/redundant?**
- Not vacuous; it is elementary: one can take c′ = c(2^α + 4^α)/(2^α − 1).
- **hα is redundant.** The literal statement also holds for α < 0, by the same algebra, since 2^α − 1 ≠ 0 and (2h)^α = 2^α h^α for h > 0.
- It also holds for α = 0. There the expression is (F(h) − F(2h))/0 − P = −P, by x/0 = 0, which is O(h⁰) = O(1). Harmless.

**Notes.**
- The error model is exactly one term a·h^α plus an O(h^(2α)) remainder.
- The conclusion is big-O (not little-o) of h^(2α), one-sided (h → 0⁺).

## 15. `ml2r_weights`

**Reads as.** For α > 0 and L ∈ ℕ:
- (i) For every integer n with 0 ≤ n ≤ L: ∑_{ℓ=0}^{L} w_ℓ · n_ℓⁿ = 1 if n = 0, and 0 otherwise.
- (ii) Uniqueness. For every w′ : ℕ → ℝ satisfying the same L+1 equations (∑_{ℓ=0}^{L} w′_ℓ n_ℓⁿ = [n = 0] for 0 ≤ n ≤ L), w′_ℓ = w_ℓ for every ℓ ∈ {0, …, L}.

**Junk values.** None. For α > 0 the nodes are pairwise distinct, so no factor of w_ℓ divides by 0.

**Satisfiable (witness).** The only hypothesis is α > 0. The premise of (ii) is satisfiable, by w itself via (i).

**Trivial/redundant?** Not trivial. It is exactness of Lagrange interpolation at 0 plus invertibility of the Vandermonde matrix. Check with α = 1, L = 2: ∑w = 1, ∑w·n = 0, ∑w·n² = 0.

**Notes.**
- α > 0 is used only to make the nodes distinct. The identities also hold for α < 0, and fail for α = 0 when L ≥ 1 (then w = 0).
- Uniqueness is asserted only on {0, …, L}.
- The exponent n is a natural number.

## 16. `ml2r_moment_succ`

**Reads as.** For α > 0 and L ∈ ℕ: ∑_{ℓ=0}^{L} w_ℓ · n_ℓ^(L+1) = (−1)^L · ∏_{k=0}^{L} n_k. The product equals 2^(−α·L(L+1)/2).

**Junk values.** None (distinct nodes).

**Satisfiable (witness).** Only α > 0 is assumed.

**Trivial/redundant?** Not trivial. Check with α = 1, L = 1: (−1)·1 + 2·(1/2)² = −1/2 = (−1)¹·(1·½).

**Notes.** The same remark about α < 0 as in #15 applies.

## 17. `ml2r_bias_eq`

**Reads as.** Let α > 0, L ∈ ℕ, reals EPl_ℓ (ℓ ∈ ℕ), EP, and real sequences a, R. Suppose that for every ℓ ∈ {0, …, L}:

  EPl_ℓ − EP = ∑_{n=1}^{L} a_n · n_ℓⁿ + R_ℓ.

Then (∑_{ℓ=0}^{L} w_ℓ · EPl_ℓ) − EP = ∑_{ℓ=0}^{L} w_ℓ · R_ℓ.

**Junk values.** None.
- For L = 0 the inner sum is empty. The hypothesis becomes EPl_0 − EP = R_0 and the conclusion is the same identity (w_0 = 1).

**Satisfiable (witness).** Always, for any EPl, EP and a: define R_ℓ := EPl_ℓ − EP − ∑_{n=1}^{L} a_n n_ℓⁿ.

**Trivial/redundant?**
- R is unconstrained, so the hypothesis constrains nothing. The theorem is a pure algebraic identity: for all EPl, EP and a, ∑ w_ℓ (EPl_ℓ − EP − ∑_{n=1}^{L} a_n n_ℓⁿ) = ∑ w_ℓ EPl_ℓ − EP.
- It is not trivial: it packages ∑w_ℓ = 1 and ∑w_ℓ n_ℓⁿ = 0 for 1 ≤ n ≤ L.

**Notes.**
- Nothing is assumed or concluded about the size of R_ℓ. Any "bias bound" reading needs separate estimates on R.
- EPl and EP are plain reals, not integrals.

## 18. `ml2r_bias`

**Reads as.** Let α > 0, L ∈ ℕ, reals EPl_ℓ and EP, and a real sequence a. Suppose that for every ℓ ∈ {0, …, L} the **exact** finite expansion

  EPl_ℓ − EP = ∑_{n=1}^{L+1} a_n · n_ℓⁿ

holds, with no remainder. Then

  (∑_{ℓ=0}^{L} w_ℓ EPl_ℓ) − EP = (−1)^L · a_{L+1} · 2^(−α·L(L+1)/2).

The exponent L(L+1)/2 is computed in ℝ, so there is no natural-number division.

**Junk values.** None.

**Satisfiable (witness).** Arbitrary a and EP, with EPl_ℓ := EP + ∑_{n=1}^{L+1} a_n n_ℓⁿ. Check with α = 1, L = 1: the result is −a_2/2.

**Trivial/redundant?** Not trivial. It follows from #15(i), #16 and ∏_{k≤L} 2^(−αk) = 2^(−αL(L+1)/2).

**Notes.** The hypothesis is an exact expansion of order L+1 at the L+1 nodes, and the conclusion is an exact equality. There is no asymptotic or remainder content.

## 19. `ml2r_rearrange`

**Reads as.** Let ν be any measure on a measurable space Ω₀ and suppose every P_ℓ is ν-integrable. Then for every real sequence w and every L ∈ ℕ:

  ∑_{ℓ=0}^{L} w_ℓ ∫P_ℓ dν = ∑_{ℓ=0}^{L} W_ℓ ∫ΔP_ℓ dν, where W_ℓ = ∑_{k=ℓ}^{L} w_k.

This is Abel summation.

**Junk values.** Integrability ensures ∫ΔP_{ℓ+1} = ∫P_{ℓ+1} − ∫P_ℓ, so there is no junk.

**Satisfiable (witness).** Any integrable family, for example P_ℓ ≡ const with ν a probability measure.

**Trivial/redundant?** Not trivial, but elementary.

**Notes.** w is arbitrary (not only the ML2R weights). ν need not be finite.

## 20. `ml2r_estimator_mean_variance`

**Reads as.**

*Setting.*
- μ is a probability measure on Ω.
- Each ω_p : Ω → Ω₀ (p ∈ ℕ×ℕ) is measurable with law ν, and the family (ω_p) is mutually independent under μ. This forces ν to be a probability measure.
- Every P_ℓ is measurable and in L²(ν).
- w : ℕ → ℝ is arbitrary, L ∈ ℕ, and N : ℕ → ℕ with N_ℓ ≥ 1 for all ℓ.

*Estimator.* With W_ℓ = ∑_{k=ℓ}^{L} w_k:

  Ŷ(x) = ∑_{ℓ=0}^{L} (1/N_ℓ) ∑_{n<N_ℓ} W_ℓ · ΔP_ℓ(ω_{(ℓ,n)}(x)).

*Conclusion.*
- (a) E_μ[Ŷ] = ∑_{ℓ=0}^{L} w_ℓ ∫P_ℓ dν.
- (b) Var_μ(Ŷ) = ∑_{ℓ=0}^{L} W_ℓ² · Var_ν(ΔP_ℓ) / N_ℓ.

**Junk values.** None.
- ΔP_ℓ ∈ L²(ν) and Ŷ ∈ L²(μ), so both variances are genuine (the "0 if not L²" convention cannot trigger).
- E_μ[Ŷ] is a genuine integral.
- N_ℓ ≥ 1, so there is no division by 0.

**Satisfiable (witness).**
- Degenerate: ν = δ₀ with constant ω_p, as in #9.
- Non-degenerate: i.i.d. uniform coordinates on [0,1]^(ℕ×ℕ), with P_ℓ(y) = 2^(−ℓ)y.

**Trivial/redundant?** Not trivial.
- hPlm looks redundant (a.e.-modification argument as in #9).
- hN is required for all ℓ, although only ℓ ≤ L matter (harmless).

**Notes.**
- The estimator is written in level-difference form with weights W_ℓ.
- (a) equates its mean with the "weighted levels" form ∑w_ℓ E[P_ℓ], combining with #19.
- The sample sizes are natural numbers.

---

## Summary table

| # | Declaration | Verdict | One-line reason |
|---|---|---|---|
| 1 | `levelDiff` | OK | ΔP_0 = P_0, ΔP_{ℓ+1} = P_{ℓ+1} − P_ℓ; telescopes to P_L. |
| 2 | `blockMean` | OK | Sample mean over samples (i, 0..N−1); N = 0 gives 0 (junk), never used with N = 0. |
| 3 | `totalCost` | OK | ∑_{ℓ≤L} ∑_{n<N_ℓ} cost_{ℓ,n}; no sign restriction. |
| 4 | `complexityBound` | OK | ε^(−2) / ε^(−2)(ln ε)² / ε^(−2−(γ−β)/α) by case; positive on 0<ε<e⁻¹; junk only for α=0 or ε∉(0,1). |
| 5 | `fineCoarseDiff` | OK | D_0 = Pf_0, D_{ℓ+1} = Pf_{ℓ+1} − Pc_ℓ. |
| 6 | `antitheticDiff` | OK | A_0 = ½(P_0 + P_0∘a), A_{ℓ+1} = ½(P_{ℓ+1} + P_{ℓ+1}∘a) − P_ℓ (level 0 also averaged). |
| 7 | `integral_fineCoarseDiff` | OK | Linearity; integrability genuinely needed; ℓ = 0 is definitional; ν arbitrary. |
| 8 | `integral_antitheticDiff` | OK | Measure preservation of a gives ∫P∘a = ∫P. |
| 9 | `giles_theorem1_corrections` | concern (minor) | Genuine, non-vacuous, no junk. c₄ comes after all data, so it may depend on P, Pl, Δ, ω, cost, μ, ν (not only on the constants). hΔm is redundant. |
| 10 | `giles_theorem1_fineCoarse` | concern (minor) | Same as #9 (c₄ data-dependent); otherwise faithful to its literal content; no junk. |
| 11 | `giles_theorem1_antithetic` | concern (minor) | Same as #9 (c₄ data-dependent); level 0 is antithetic; no junk. |
| 12 | `ml2rNode` | OK | 2^(−αℓ) > 0. |
| 13 | `ml2rWeight` | OK | Lagrange basis at 0; junk (all 0) when α = 0 and L ≥ 1, excluded by α > 0 in every theorem. |
| 14 | `richardson_extrapolation` | OK | Correct O(h^(2α)) statement on the non-trivial filter 𝓝[>]0; hα is redundant (it also holds for α ≤ 0). |
| 15 | `ml2r_weights` | OK | Moment conditions n = 0..L plus uniqueness on {0..L}; α > 0 only needed for distinct nodes. |
| 16 | `ml2r_moment_succ` | OK | (L+1)-th moment = (−1)^L ∏n_k; checked on L = 1. |
| 17 | `ml2r_bias_eq` | OK | Pure identity since R is free; says nothing about the size of R. |
| 18 | `ml2r_bias` | OK | Exact expansion to order L+1 gives bias (−1)^L a_{L+1} 2^(−αL(L+1)/2) (real exponent). |
| 19 | `ml2r_rearrange` | OK | Abel summation with W_ℓ = ∑_{k=ℓ}^{L} w_k; integrability needed and present. |
| 20 | `ml2r_estimator_mean_variance` | OK | Mean = ∑w_ℓE[P_ℓ], variance = ∑W_ℓ²Var(ΔP_ℓ)/N_ℓ; all genuine (L²); hPlm redundant. |
