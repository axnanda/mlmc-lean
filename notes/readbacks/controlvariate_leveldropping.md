# Blind read-back: packet 10 (round 3)

- **Date:** 2026-09-26
- **Packet:** `packet10.lean` (a scratch file, not in the repository). It has 15 declarations: two definitions (`blockMean`, `correlation`) and 13 theorems.
- **Auditor:** an independent, blind sub-agent.
- **Rules followed:**
  - **What I read.** Only `packet10.lean`, `packet11.lean` and `references/mission_auditor.md`. I did not open:
    - the project's Lean sources;
    - `docs/`, `notes/`, README, PLAN or metadata;
    - git history, any paper, or the web.
  - **Mathlib.** I consulted Mathlib sources only for exact definitions and conventions:
    - `Probability/Moments/Variance.lean` (`evariance`, `variance`);
    - `Probability/Moments/Covariance.lean`;
    - `MeasureTheory/Function/LpSeminorm/Defs.lean` (`MemLp`);
    - `Dynamics/Ergodic/MeasurePreserving.lean`;
    - `Probability/Independence/Basic.lean`, `.../Kernel/IndepFun.lean` and `.../Kernel/Indep.lean` (`iIndepFun`);
    - `Order/Bounds/Defs.lean` (`IsLeast`);
    - `Analysis/Real/Sqrt.lean`;
    - `MeasureTheory/Integral/Bochner/Basic.lean` (`integral_undef`);
    - `Probability/Notation.lean` (the `μ[X]` macro);
    - `Algebra/BigOperators/Group/Finset/Defs.lean` (parsing precedence of `∑`).
  - **Method.** I translate the code, not a presumed intent (mission_auditor.md, principles 1–5). Verdicts cover literal meaning, junk values, vacuity and triviality.
  - **What "true" means here.** The packet's proofs are `sorry`. When I say a statement "holds" or "is true", that is my own check of the mathematics: a hand proof, plus numeric spot checks on random finite examples run as inline Python (no files written). It is not a check of the project's Lean proofs.
  - **Files written.** Only the two output files.

## Conventions used below (checked in Mathlib)

- **E_μ[h].** This is `μ[h]` = ∫ h dμ, the Bochner integral. It is **0 whenever h is not μ-integrable**.
- **Var_μ(X).** This is `variance X μ` = toReal(∫⁻ |X − E_μ X|² dμ).
  - For X ∈ L²(μ) it is the usual variance.
  - If the lower integral is ∞ (e.g. X is a.e.-measurable but not in L², on a finite measure), then **Var = 0**.
  - It is always ≥ 0.
- **Cov_μ(X, Y).** This is `covariance X Y μ` = ∫ (X − E X)(Y − E Y) dμ, a Bochner integral, so it is 0 if the integrand is not integrable.
- **X ∈ L²(μ).** This is `MemLp X 2 μ`: X is a.e.-strongly measurable and ∫ |X|² dμ < ∞.
- **"ω_n has law ν".** This is `MeasurePreserving ω_n μ ν`: ω_n is measurable and (ω_n)_*μ = ν exactly.
- **`iIndepFun ω μ`.** The ω_n are mutually independent. For every finite index set S and all measurable B_n: μ(⋂_{n∈S} ω_n⁻¹B_n) = ∏_{n∈S} μ(ω_n⁻¹B_n).
- **`IsLeast S m`.** m ∈ S and m ≤ s for all s ∈ S, so m is an attained minimum.
- **Total-function conventions.** √x (`Real.sqrt`) = 0 for x ≤ 0, x/0 = 0, and 0⁻¹ = 0.
- **`range N`.** This is {0, …, N−1}; the empty sum is 0.
- **Parsing of ∑.** The body of `∑ i ∈ s, …` is parsed at precedence 67, so it absorbs `*` and `/` but stops at `+` and `-`.
  - `∑ i ∈ s, a i + b` means (∑_{i∈s} a_i) + b.
  - `c * ∑ n, a n - d` means (c·∑_n a_n) − d.

## Standing context

- **`mc_estimate`, `controlVariate_estimator`.** Ω and Ω₀ are measurable spaces. μ is a probability measure on Ω (an explicit instance argument). ν is a measure on Ω₀ with **no stated assumption**. However, hω at n = 0 gives ν = (ω₀)_*μ, so ν is automatically a probability measure.
- **`controlVariate_mean`, `controlVariate_variance`, `controlVariate_optimal`.** μ is a probability measure on Ω, and f, g : Ω → ℝ are implicit.
- **`levelDrop_variance`, `levelDrop_perfect_correlation`, `levelDrop_uncorrelated`.** μ is a probability measure on Ω.
- **`optimal_cost_*`, `levelKeep_product`, `levelDrop_test`.** These are statements about real numbers only. No measure-theoretic variable is mentioned, so none is included.
- **`blockMean`.** The packet gives no context. ι, Ω and Ω₀ are arbitrary types, and no measurable structure is needed.

---

## 1. `blockMean` (definition)

### Reads as
The inputs are:
- arbitrary types ι, Ω, Ω₀;
- a family of functions f_i : Ω₀ → ℝ (i ∈ ι);
- a family of maps ω_{(i,n)} : Ω → Ω₀, indexed by (i, n) ∈ ι × ℕ;
- an index i, a natural number N and a point x ∈ Ω.

The definition is

  blockMean(f, ω, i, N)(x) = (1/N) · ∑_{n=0}^{N−1} f_i( ω_{(i,n)}(x) ).

This is the empirical mean of f_i over the N points ω_{(i,0)}(x), …, ω_{(i,N−1)}(x).

### Junk values
When N = 0, (0:ℝ)⁻¹ = 0 and the sum is empty, so blockMean = 0 rather than undefined. There is no other junk.

### Satisfiable (witness)
Not applicable to a definition. Example: take ι = Unit, Ω = Ω₀ = ℝ, f = id, ω_{(i,n)}(x) = x + n and N = 2. Then blockMean = x + ½.

### Trivial/redundant?
Not applicable.

### Notes
- **No theorem in packet 10 or 11 mentions `blockMean`**, so these packets neither constrain nor exercise it.
- Block i uses its own sample indices {i} × {0, …, N−1} and its own integrand f_i.
- N is a natural number.

## 2. `mc_estimate`

### Reads as
Let (Ω, μ) be a probability space and (Ω₀, ν) a measure space. Let ω_0, ω_1, … : Ω → Ω₀ satisfy:
- (hω) every ω_n is measurable and (ω_n)_*μ = ν;
- (hind) the whole infinite sequence (ω_n)_{n∈ℕ} is mutually independent under μ.

Let P : Ω₀ → ℝ be measurable (hPm) with P ∈ L²(ν) (hP), and let N ∈ ℕ with N ≥ 1 (hN). Put

  P̂_N(x) = (1/N) ∑_{n=0}^{N−1} P(ω_n(x)),  m = ∫ P dν,  V = Var_ν(P).

Then all four of the following hold:
1. E_μ[P̂_N] = m.
2. Var_μ(P̂_N) = V/N.
3. E_μ[(P̂_N − m)²] = V/N.
4. For every real ε > 0: √(E_μ[(P̂_N − m)²]) ≤ ε ⟺ V/ε² ≤ N, with N cast to ℝ.

By the precedence rule, the "− m" in (3)–(4) sits outside the sum, as written above. The value would be the same either way, because N ≥ 1.

### Junk values
None is active:
- ν is a probability measure (by hω), so P ∈ L²(ν) ⊂ L¹(ν). Hence m and V are genuine, and V < ∞.
- Each P∘ω_n has the same law as P under ν, so P̂_N ∈ L²(μ). The integrals in (1) and (3) and the variance in (2) are therefore genuine.
- N ≥ 1 makes (N:ℝ)⁻¹ genuine.
- In (4), ε² > 0 and the argument of √ is V/N ≥ 0, so √ is never clipped.

### Satisfiable (witness)
- **Degenerate.** Ω = Ω₀ = one point, μ = ν = Dirac, ω_n = id (trivially independent), P constant. Then V = 0.
- **Non-degenerate.** Ω = [0,1) with Lebesgue measure and Ω₀ = ℝ. Let ω_n(x) be the (n+1)-th binary digit of x, which gives i.i.d. Bernoulli(½) variables, so ν = ½δ₀ + ½δ₁. Take P = id. Then m = ½, V = ¼ and Var(P̂_N) = 1/(4N).

### Trivial/redundant?
The statement is not trivial:
- (1) is linearity.
- (2) is the variance of an i.i.d. mean; it uses both independence and the equal laws.
- (3) follows from (1) and (2), since for an unbiased estimator the MSE equals the variance.
- (4) is an algebraic rearrangement of (3): √(V/N) ≤ ε ⟺ V ≤ ε²N.

**Redundancy.** hP is what makes the conclusions genuine, but it is logically redundant:
- If P ∈ L¹∖L², then P̂_N ∉ L²(μ). So Var(P̂_N) = 0 and V = 0 by the "Var = 0 off L²" convention, E[(P̂_N − m)²] = 0 by the "∫ = 0 when not integrable" convention, and (4) becomes "true ⟺ true".
- If P ∉ L¹, every quantity is a junk 0.

So hP is exactly the hypothesis that rules out the degenerate reading, and it is present. Mutual independence of the whole infinite sequence is more than needed (pairwise independence of ω_0, …, ω_{N−1} would do), but this is harmless.

### Notes
- (4) is an exact characterisation for the given N, not merely a sufficient condition.
- ν is not declared a probability measure, but hω forces it to be one.
- The sample size N is a natural number.

## 3. `correlation` (definition)

### Reads as
For a measurable space Ω, functions f, g : Ω → ℝ and **any** measure μ on Ω:

  ρ_μ(f, g) = Cov_μ(f, g) / √( Var_μ(f) · Var_μ(g) ).

### Junk values
- **Zero variance.** If Var_μ f = 0 or Var_μ g = 0, the denominator is √0 = 0, so **ρ = 0**. This includes the Mathlib convention that Var = 0 for a measurable function outside L² on a finite measure.
- **Non-integrable covariance.** If the covariance integrand is not integrable, Cov = 0 and ρ = 0.
- **Non-probability measures.** μ need not be a probability measure. For other measures Var and Cov are unnormalised integrals, and ρ is not the usual coefficient.
- **The genuine case.** For a probability measure μ, f, g ∈ L²(μ) and both variances > 0, ρ is the usual Pearson correlation, with values in [−1, 1].

So "ρ = 0" alone does not mean "uncorrelated". A nonzero value (for example ρ = 1) can arise only when the denominator is nonzero.

### Satisfiable (witness)
Take Ω = {a, b} with μ uniform and f = g = 1_{a}. Then Cov = ¼, Var f = Var g = ¼, and ρ = 1. With g = 1_{b} instead, ρ = −1.

### Trivial/redundant?
Not applicable.

### Notes
Every theorem in this packet that uses ρ also assumes a probability measure and L² functions. Where it matters, it also assumes positive variances. So the junk branch is inactive in every use; I checked each theorem below.

## 4. `controlVariate_mean`

### Reads as
Let (Ω, μ) be a probability space, let f, g : Ω → ℝ be μ-integrable (hf, hg), and let λ ∈ ℝ. Then

  E_μ[ f − λ·(g − E_μ g) ] = E_μ f.

### Junk values
None is active: the integrand is integrable.

### Satisfiable (witness)
Any integrable f and g work, for example f = g = 1_{a} on the two-point uniform space.

### Trivial/redundant?
The statement is elementary: linearity plus μ(Ω) = 1.
- **hf is logically redundant.** If f were not integrable, then (since g is integrable) f − λ(g − E g) would not be integrable either. Both sides would then be 0 by convention.
- **hg is needed.** With g non-integrable and λ ≠ 0, the left side is 0 while E f can be nonzero.

### Notes
None.

## 5. `controlVariate_variance`

### Reads as
Let (Ω, μ) be a probability space, f, g ∈ L²(μ) and λ ∈ ℝ. Then

  Var_μ( f − λ(g − E_μ g) ) = Var_μ f − 2λ·Cov_μ(f, g) + λ²·Var_μ g.

### Junk values
None is active: every term is genuine for L² functions.

### Satisfiable (witness)
Any f, g ∈ L² work, for example on the two-point space.

### Trivial/redundant?
This is the standard bilinear expansion. **Both hypotheses are needed.** Counterexample without them: take f = 1_A with 0 < μ(A) < 1, g ∈ L¹∖L² independent of A, and λ = 1.
- The left side is 0, because the function is not in L² and so its Var is 0 by convention.
- The right side is μ(A)(1 − μ(A)) > 0.

### Notes
None.

## 6. `controlVariate_optimal`

### Reads as
Let (Ω, μ) be a probability space with f, g ∈ L²(μ), Var_μ f > 0 and Var_μ g > 0. Write ρ = ρ_μ(f, g), and for λ ∈ ℝ let v(λ) = Var_μ( f − λ(g − E_μ g) ). Then:
- **(a)** (1 − ρ²)·Var f is the **least element** of {v(λ) : λ ∈ ℝ}. Some λ attains it, and v(λ) ≥ (1 − ρ²)·Var f for every λ.
- **(b)** For every λ ∈ ℝ: v(λ) = (1 − ρ²)·Var f ⟺ λ = ρ·√(Var f / Var g).

So the minimiser is unique and equals ρ√(Var f / Var g) = Cov(f, g)/Var g.

### Junk values
None is active. Positive variances plus L² make ρ genuine, and Var f / Var g > 0.

### Satisfiable (witness)
Take the two-point uniform space with f = g = 1_{a}. Then Var = ¼ and ρ = 1, and v(λ) = (1 − λ)²/4, so the minimum 0 is attained exactly at λ = 1. I also checked the formulas numerically on 5000 random finite examples with |ρ| < 1.

### Trivial/redundant?
The statement is not trivial: it minimises the quadratic Var f − 2λ·Cov + λ²·Var g.
- **hVg is needed for (b).** If Var g = 0, every λ attains the minimum, but (b) would single out λ = 0.
- **hVf is logically redundant.** If Var f = 0, then Cov = 0 and ρ = 0, and v(λ) = λ²·Var g. Its unique minimiser λ = 0 equals ρ·√0, so (a) and (b) still hold.

### Notes
The IsLeast set is a range over ℝ, so it is nonempty.

## 7. `controlVariate_estimator`

### Reads as
The setup is that of `mc_estimate`:
- (Ω, μ) is a probability space;
- the ω_n : Ω → Ω₀ are measurable, have law ν and are mutually independent;
- f, g : Ω₀ → ℝ are measurable and in L²(ν);
- N ≥ 1 and λ ∈ ℝ.

Let m_g = ∫ g dν, and define

  Ŷ(x) = (1/N) ∑_{n=0}^{N−1} [ f(ω_n(x)) − λ( g(ω_n(x)) − m_g ) ],  F̂(x) = (1/N) ∑_{n=0}^{N−1} f(ω_n(x)).

Then:
1. E_μ[Ŷ] = ∫ f dν.
2. Var_μ(Ŷ) = Var_ν( f − λ(g − m_g) ) / N.
3. If Var_ν f > 0, Var_ν g > 0 and λ = ρ_ν(f, g)·√(Var_ν f / Var_ν g), then Var_μ(Ŷ) = (1 − ρ_ν(f, g)²)·Var_μ(F̂).

### Junk values
None is active:
- ν is a probability measure (by hω).
- Everything is in L², and N ≥ 1.
- In (3) the variances are positive, so ρ_ν is genuine.

### Satisfiable (witness)
Use the Bernoulli witness of `mc_estimate` with f = g = id. Then Var_ν = ¼, ρ = 1 and λ = 1. So Ŷ ≡ ½, and (3) reads 0 = 0 · Var(F̂).

### Trivial/redundant?
The statement is not trivial: (3) combines (2), the optimal-λ identity and Var(F̂) = Var_ν f / N.

**Both positivity premises in (3) are logically redundant.** If either variance is 0, then ρ_ν = 0, and the premise forces λ = 0 (via ρ = 0 or √(x/0) = 0). Then Ŷ = F̂ and (3) becomes an identity.

(1) and (2) hold for every λ.

### Notes
The means, variances and correlation of the integrands are taken under the sample law ν, while the estimator variances are taken under μ. N is a natural number.

## 8. `optimal_cost_const_product`

### Reads as
Let V, C : ℕ → ℝ be arbitrary sequences, L ∈ ℕ, and τ ∈ ℝ arbitrary. Suppose V_0 ≥ 0, C_0 ≥ 0, and V_ℓ·C_ℓ = V_0·C_0 for every ℓ ∈ {0, …, L}. Then

  τ⁻¹·( ∑_{ℓ=0}^{L} √(V_ℓ C_ℓ) )² = τ⁻¹·(L+1)²·V_0 C_0.

### Junk values
- **τ is unrestricted.** For τ = 0 both sides are 0 (since τ⁻¹ = 0), so the identity still holds, trivially.
- **Signs.** For ℓ ≥ 1, V_ℓ and C_ℓ may individually be negative. Only their product is constrained, and it equals V_0 C_0 ≥ 0, so √ is never clipped.

### Satisfiable (witness)
Take V ≡ C ≡ 1, L = 3, τ = 2. Both sides equal 8.

### Trivial/redundant?
The identity is elementary, because every summand equals √(V_0 C_0).
- The factor τ⁻¹ is common to both sides and plays no role.
- hV0 ∧ hC0 is used only to get V_0 C_0 ≥ 0, which is all that is needed. If V_0 C_0 < 0, the identity fails for τ ≠ 0.

### Notes
None.

## 9. `optimal_cost_increasing`

### Reads as
Let V, C : ℕ → ℝ, r > 1 and τ > 0. Suppose V_ℓ ≥ 0 and C_ℓ ≥ 0 for all ℓ, and r·√(V_ℓ C_ℓ) ≤ √(V_{ℓ+1} C_{ℓ+1}) for all ℓ ∈ ℕ. Then for every L ∈ ℕ:

  τ⁻¹·V_L C_L ≤ τ⁻¹·( ∑_{ℓ=0}^{L} √(V_ℓ C_ℓ) )² ≤ (r/(r−1))²·τ⁻¹·V_L C_L.

### Junk values
None: r − 1 > 0, τ > 0, and all products are ≥ 0.

### Satisfiable (witness)
Take V_ℓ = 4^ℓ, C_ℓ = 1, r = 2, τ = 1 and L = 2. The chain reads 16 ≤ 49 ≤ 64. The all-zero sequence is also allowed (0 ≤ 0 ≤ 0).

### Trivial/redundant?
The statement is not trivial: it is a geometric-series bound. I spot-checked it numerically.
- **hr is needed.** With r = 1, r/(r−1) = 1/0 = 0, and the upper bound fails (e.g. V ≡ C ≡ 1, L = 0).
- **Over-assumptions (harmless).** The growth condition is assumed for all ℓ, though only ℓ < L is used. The sign conditions are assumed for all ℓ, though only V_L C_L ≥ 0 is essential.

### Notes
Both inequalities are non-strict. The constant (r/(r−1))² does not depend on L.

## 10. `optimal_cost_decreasing`

### Reads as
Let V, C : ℕ → ℝ, 0 ≤ r < 1 and τ > 0. Suppose V_ℓ, C_ℓ ≥ 0 for all ℓ, and √(V_{ℓ+1} C_{ℓ+1}) ≤ r·√(V_ℓ C_ℓ) for all ℓ. Then for every L ∈ ℕ:

  τ⁻¹·V_0 C_0 ≤ τ⁻¹·( ∑_{ℓ=0}^{L} √(V_ℓ C_ℓ) )² ≤ (1 − r)⁻²·τ⁻¹·V_0 C_0.

### Junk values
None, since 1 − r > 0.

### Satisfiable (witness)
Take V_ℓ = 4^{−ℓ}, C_ℓ = 1, r = ½, τ = 1 and L = 2. The chain reads 1 ≤ 3.0625 ≤ 4.

### Trivial/redundant?
The statement is not trivial; I spot-checked it numerically.

**hr0 (r ≥ 0) is logically redundant.** If r < 0, the decay hypothesis forces every √(V_ℓ C_ℓ) to be 0, and the conclusion becomes 0 ≤ 0 ≤ 0.

### Notes
Both inequalities are non-strict.

## 11. `levelKeep_product`

### Reads as
Let V_ℓ, V_{ℓ+1}, C_ℓ, C_{ℓ+1} be four positive reals. (The Lean names are Vℓ, Vℓ₁, Cℓ, Cℓ₁; nothing ties them to any sequence.) Let

  S = { (V_ℓ/n + V_{ℓ+1}/n₁)·(n·C_ℓ + n₁·C_{ℓ+1}) : n, n₁ ∈ ℝ, n > 0, n₁ > 0 }.

Then S has the least element

  m = V_{ℓ+1} C_{ℓ+1}·(1 + √(V_ℓ C_ℓ / (V_{ℓ+1} C_{ℓ+1})))²,  which equals (√(V_ℓ C_ℓ) + √(V_{ℓ+1} C_{ℓ+1}))².

That is:
- m is attained for some real n, n₁ > 0, for example n = √(V_ℓ/C_ℓ) and n₁ = √(V_{ℓ+1}/C_{ℓ+1}), or any common positive multiple of these;
- every element of S is ≥ m.

### Junk values
None: all quantities are positive.

### Satisfiable (witness)
Set all four values to 1. Then S = {(1/n + 1/n₁)(n + n₁)} and m = 4, attained at n = n₁.

### Trivial/redundant?
The statement is not trivial (it is Cauchy–Schwarz / AM–GM). All four positivity hypotheses are used. I checked it numerically on random inputs.

### Notes
- **The sample sizes n and n₁ are real numbers, not natural numbers.** This is a continuous relaxation.
  - The expression depends only on the ratio n/n₁, and it has a unique optimal ratio √((V_ℓ/C_ℓ)/(V_{ℓ+1}/C_{ℓ+1})).
  - Over natural numbers the minimum is attained only if that ratio is rational. So the ℕ-valued version of this IsLeast statement would be false in general.
- The same expression m is the right-hand side of `levelDrop_test`. It also appears, with V_{ℓ+1} := Var X and V_ℓ := Var Y, in `levelDrop_perfect_correlation` and `levelDrop_uncorrelated`.

## 12. `levelDrop_test`

### Reads as
Take:
- any type ι, a finite set s ⊆ ι, and functions V, C : ι → ℝ;
- reals V_ℓ, V_{ℓ+1}, C_ℓ, C_{ℓ+1}, V_d, C_d, τ with V_{ℓ+1} > 0, C_{ℓ+1} > 0 and τ > 0.

Let S = ∑_{i∈s} √(V_i C_i). Then

  τ⁻¹·(S + √(V_d C_d))² < τ⁻¹·(S + √(V_ℓ C_ℓ) + √(V_{ℓ+1} C_{ℓ+1}))²
  ⟺ V_d C_d < V_{ℓ+1} C_{ℓ+1}·(1 + √(V_ℓ C_ℓ / (V_{ℓ+1} C_{ℓ+1})))².

By the ∑ precedence rule, √(V_d C_d), √(V_ℓ C_ℓ) and √(V_{ℓ+1} C_{ℓ+1}) are each added once, outside the sum over s.

### Junk values
V, C, V_ℓ, C_ℓ, V_d and C_d have no sign constraints, so their products may be negative, in which case √ clips to 0.

I checked every sign case, by hand and on 2·10⁵ random samples that included negative values. **The equivalence still holds.** For example, V_d C_d < 0 makes both sides true. With the same clipping, the right-hand side equals (√(V_ℓ C_ℓ) + √(V_{ℓ+1} C_{ℓ+1}))².

### Satisfiable (witness)
Take s = ∅, V_ℓ = C_ℓ = V_{ℓ+1} = C_{ℓ+1} = τ = 1 and C_d = 1.
- With V_d = 3, both sides are true (3 < 4).
- With V_d = 5, both sides are false.

### Trivial/redundant?
The statement is elementary. Because S ≥ 0 and τ > 0, the left side is equivalent to √(V_d C_d) < √(V_ℓ C_ℓ) + √(V_{ℓ+1} C_{ℓ+1}), so the common terms S and τ⁻¹ drop out.
- τ > 0 is needed for the direction of the inequality.
- Of V_{ℓ+1} > 0 and C_{ℓ+1} > 0, only the positivity of their product is really needed.

### Notes
The inequality is strict on both sides.

## 13. `levelDrop_variance`

### Reads as
Let (Ω, μ) be a probability space, X, Y ∈ L²(μ), Var X > 0 and Var Y > 0. Then

  Var(X + Y) = Var X + 2·ρ_μ(X, Y)·√(Var Y · Var X) + Var Y.

### Junk values
None is active: ρ is genuine, and ρ·√(Var X · Var Y) = Cov(X, Y).

### Satisfiable (witness)
Take the two-point uniform space with X = 1_{a} and Y = 1_{b}. Then ρ = −1 and both sides are 0.

### Trivial/redundant?
This is Var(X + Y) = Var X + 2 Cov + Var Y, with Cov rewritten as ρ√(Var X · Var Y). I checked it numerically.

**hVX and hVY are logically redundant.** If a variance is 0, then Cov = 0 by Cauchy–Schwarz, and ρ·√0 = 0. So the identity holds for all X, Y ∈ L².

### Notes
None.

## 14. `levelDrop_perfect_correlation`

### Reads as
Let (Ω, μ) be a probability space, X, Y ∈ L²(μ), Var X > 0, Var Y > 0 and **ρ_μ(X, Y) = 1**. Let C_ℓ and C_{ℓ+1} be reals with 0 < C_ℓ ≤ C_{ℓ+1}. Then:
- **(a)** Var(X + Y) = Var X·(1 + √(Var Y / Var X))², which equals (√Var X + √Var Y)².
- **(b)** It is **not** the case that Var(X + Y)·C_{ℓ+1} < Var X·C_{ℓ+1}·(1 + √(Var Y·C_ℓ / (Var X·C_{ℓ+1})))².

Equivalently, (b) says Var(X + Y)·C_{ℓ+1} ≥ (√(Var X·C_{ℓ+1}) + √(Var Y·C_ℓ))².

### Junk values
None is active. With positive variances, ρ = 1 is a genuine perfect positive correlation: Y − E Y = c(X − E X) almost surely, for some c > 0.

### Satisfiable (witness)
Take X = Y = 1_{a} on the two-point uniform space, with C_ℓ = 1 and C_{ℓ+1} = 2.
- (a) reads 1 = ¼·4.
- (b) reads 2 ≥ ½(1 + √½)² ≈ 1.457.

### Trivial/redundant?
(a) is the variance identity with ρ = 1. (b) follows from (a) because C_ℓ/C_{ℓ+1} ≤ 1.
- **hVX and hVY are implied by hρ.** ρ = 1 ≠ 0 forces the denominator √(Var X · Var Y) to be nonzero.
- **hC (C_ℓ > 0) is logically redundant.** I checked the cases C_{ℓ+1} > 0, = 0 and < 0: (b) holds for every C_ℓ ≤ C_{ℓ+1}, whatever its sign.
- **hCC is essential.**

### Notes
(b) is a negated strict inequality, i.e. a non-strict ≥. Equality holds when C_ℓ = C_{ℓ+1}. The costs C_ℓ and C_{ℓ+1} are free reals, not linked to X or Y.

## 15. `levelDrop_uncorrelated`

### Reads as
Let (Ω, μ) be a probability space, X, Y ∈ L²(μ), Var X > 0, Var Y > 0 and **ρ_μ(X, Y) = 0**. Let C_ℓ be any real (no sign condition) and C_{ℓ+1} > 0. Then:
- **(a)** Var(X + Y) = Var X + Var Y.
- **(b)** Var(X + Y)·C_{ℓ+1} < Var X·C_{ℓ+1}·(1 + √(Var Y·C_ℓ / (Var X·C_{ℓ+1})))² ⟺ 1 + Var Y / Var X < (1 + √(Var Y·C_ℓ / (Var X·C_{ℓ+1})))².

### Junk values
- With positive variances, ρ = 0 ⟺ Cov = 0, so this is genuine uncorrelatedness.
- If C_ℓ ≤ 0, √ clips to 0 and both sides of (b) are false, so the equivalence still holds.

### Satisfiable (witness)
Take two independent fair coins on {0,1}² with the uniform measure. Then Var X = Var Y = ¼, Cov = 0 and Var(X + Y) = ½.
- With C_ℓ = 1 and C_{ℓ+1} = 4, both sides of (b) are true (2 < 2.25).
- With C_ℓ = 1 and C_{ℓ+1} = 100, both sides are false (2 vs 1.21).

### Trivial/redundant?
- (a) is the variance identity with Cov = 0.
- (b) is (a) substituted in, then both sides divided by Var X·C_{ℓ+1} > 0. **It is a purely algebraic reformulation and does not settle which side holds.**
- **hVX and hVY are logically redundant.** If a variance is 0, (a) still holds, and both sides of (b) are false under the x/0 = 0 and √0 = 0 conventions.

### Notes
C_ℓ has no positivity hypothesis here, unlike in `levelDrop_perfect_correlation`. Both inequalities in (b) are strict.

---

## Summary

| Declaration | Verdict | One-line reason |
|---|---|---|
| `blockMean` | OK | (1/N)∑_{n<N} f_i(ω_{(i,n)}(x)); junk value 0 at N = 0; not used by any theorem in packets 10–11 |
| `mc_estimate` | OK | All four conjuncts genuine (ν forced to be a probability measure, P ∈ L², N ≥ 1); (3)–(4) follow algebraically from (1)–(2); hP is the hypothesis that prevents a degenerate all-junk reading |
| `correlation` | OK (note) | Pearson ρ when both variances > 0 and L²; junk 0 otherwise, and for non-probability μ unnormalised; every use in the packet excludes the junk case |
| `controlVariate_mean` | OK | Elementary; hf redundant via junk convention |
| `controlVariate_variance` | OK | Standard expansion; both L² hypotheses needed |
| `controlVariate_optimal` | OK | Exact attained minimum and unique minimiser; hVf redundant, hVg needed |
| `controlVariate_estimator` | OK | Genuine; the two positivity premises of (3) are redundant |
| `optimal_cost_const_product` | OK | Elementary identity; τ⁻¹ decorative, τ unrestricted (τ = 0 gives 0 = 0) |
| `optimal_cost_increasing` | OK | Genuine geometric bound; non-strict |
| `optimal_cost_decreasing` | OK | Genuine geometric bound; r ≥ 0 redundant |
| `levelKeep_product` | OK (note) | Sample sizes n, n₁ are **real** (continuous relaxation); the ℕ-valued version would be false in general |
| `levelDrop_test` | OK | Iff valid even for negative (√-clipped) inputs; elementary |
| `levelDrop_variance` | OK | Restates Var(X+Y) = VX + 2Cov + VY; positivity hypotheses redundant |
| `levelDrop_perfect_correlation` | OK | (b) is a non-strict ≥; hVX, hVY implied by ρ = 1; hC redundant |
| `levelDrop_uncorrelated` | OK | (b) is only a rescaling of (a); hVX, hVY redundant; C_ℓ sign-free |

Overall:
- No statement in packet 10 is vacuous. Every hypothesis set has a witness, and none of the conclusions holds only because of a junk convention under the stated hypotheses.
- The remaining points are informational:
  - several redundant hypotheses;
  - the real-valued relaxation in `levelKeep_product`;
  - `blockMean` is never exercised.
