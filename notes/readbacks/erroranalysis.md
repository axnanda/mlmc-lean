# Blind read-back: packet 11 (round 3)

- **Date:** 2026-09-26
- **Packet:** `packet11.lean` (a scratch file, not in the repository). It has 14 declarations: one definition (`kurtosis`) and 13 theorems.
- **Auditor:** an independent, blind sub-agent.
- **Rules followed:**
  - **Files opened:** only `packet10.lean`, `packet11.lean` and `references/mission_auditor.md`.
  - **Files not opened:** the project's Lean sources, `docs/`, `notes/`, README, PLAN, metadata, git history, any paper, and the web.
  - **Mathlib:** consulted only for exact definitions and conventions. These are the same files as for packet 10, plus:
    - `Topology/Algebra/InfiniteSum/Defs.lean` (`HasSum`);
    - `MeasureTheory/Measure/MeasureSpaceDef.lean` (`Measure.real`);
    - `Algebra/Order/Floor/Semiring.lean` (`Nat.ceil`).
  - **Method:** I translate the code, not a presumed intent (mission_auditor.md principles 1–5).
  - **Scope of "true":** the packet's proofs are `sorry`. "Holds" or "true" below means my own mathematical check: hand proofs, plus numeric spot checks run as inline Python with no files written.
  - **Output:** only the two output files were written.

## Conventions (checked in Mathlib)

As in `out10.md`:

- **Expectation.** E_μ[h] = μ[h] is the Bochner integral, and it is 0 when h is not integrable.
- **Variance.** Var_μ(X) is toReal(∫⁻ |X − E X|²). It is the usual variance on L², and it is 0 when the lintegral is infinite.
- **Covariance.** Cov_μ is the Bochner integral of (X − E X)(Y − E Y).
- **L².** X ∈ L² means `MemLp X 2`.
- **Measure-preserving, independence.** These have the same meaning as in packet 10.
- **Real-valued conventions.** √x = 0 for x ≤ 0, x/0 = 0, and 0⁻¹ = 0.
- **Parsing.** The body of `∑` stops at `+` and `-`.

Additional conventions:

- **`HasSum f s`** means unconditional convergence: the limit over finite subsets of ℕ. For real series this is absolute convergence, with sum s.
- **`μ.real A`** is toReal(μ(A)). For a probability measure this is just μ(A).
- **`⌈x⌉₊`** is `Nat.ceil`: the least natural number ≥ x. It equals 0 exactly when x ≤ 0.
- **Limits.** `Tendsto u atTop (𝓝 c)` means u_ℓ → c. `Tendsto u atTop atTop` means u_ℓ → +∞.
- **Real powers.** 2^x with real x is the usual exp(x ln 2); the base is positive, so there is no junk.

## Standing context

- **File-level.** Unless stated otherwise, (Ω, μ) is a probability space.
- **`kurtosis`.** Ω₀ is a measurable space, and ν is an explicit, arbitrary measure.
- **`sampleVariance_sd`.** (Ω₀, ν) is a measure space with no assumption on ν, together with the probability space (Ω, μ). Hypothesis hω forces ν to be a probability measure.

## Important: `levelDiff` is used but not defined

Three statements use `levelDiff`: `weak_rate_of_second_moment`, `remaining_error` and `convergence_test_mse`. It is defined in neither packet 11 nor packet 10.

From how it is used, its type is levelDiff : (ℕ → Ω → ℝ) → ℕ → Ω → ℝ. I was not allowed to look it up. Below, I write P_ℓ := `Pl ℓ` and Δ_ℓ := `levelDiff Pl ℓ`, and treat Δ_ℓ as an opaque function Ω → ℝ determined by the family (P_ℓ) and by ℓ.

**The truth of all three statements depends on what Δ_ℓ is.** I checked two candidate readings:

- **(B) Backward difference:** Δ_ℓ = P_ℓ − P_{ℓ−1} for ℓ ≥ 1, with Δ_0 arbitrary. Under (B), all three statements are true.
- **(F) Forward difference:** Δ_ℓ = P_{ℓ+1} − P_ℓ. Under (F), all three are false; explicit counterexamples are given below.

So these three read-backs are incomplete until someone supplies the definition of `levelDiff` and checks it against (B).

---

## 1. `mse_lt_of_half`

### Reads as
Assumptions:
- (Ω, μ) is a probability space.
- Y, P, P_L : Ω → ℝ, with Y ∈ L²(μ) and P, P_L μ-integrable.
- E Y = E P_L (hmean).
- ε ∈ ℝ, with no sign assumption.
- Var Y < ε²/2 (hV).
- (∫ (P_L − P) dμ)² < ε²/2 (hbias).

Conclusion:

  E_μ[(Y − E_μ P)²] < ε².

### Junk values
None is active:
- Y ∈ L², so Var Y is genuine and (Y − E P)² is integrable.
- P and P_L are integrable, so ∫ (P_L − P) = E P_L − E P is genuine.

### Satisfiable (witness)
- **Trivial:** Y = P = P_L = 0 and ε = 1.
- **Non-degenerate:** Y = P_L = 1_A with μ(A) = ½, P = 0, ε = 2. Then Var Y = ¼ < 2, the bias² is ¼ < 2, and the MSE is ½ < 4.

### Trivial/redundant?
This is the bias–variance decomposition:

  MSE = Var Y + (E P_L − E P)² < ε²/2 + ε²/2.

All hypotheses are needed. For example, drop hPL: take P ≡ 10, P_L not integrable, Y ≡ 0 and ε = 1. Then the junk values make hmean and hbias true, but the conclusion reads 100 < 1.

### Notes
- ε ≠ 0 is forced, because 0 ≤ Var Y < ε²/2. The sign of ε is irrelevant.
- Both hypotheses and the conclusion are strict inequalities.
- Y is related to P_L only through their equal means.

## 2. `weak_rate_of_second_moment`

### Reads as
Assumptions:
- (Ω, μ) is a probability space.
- P : Ω → ℝ is integrable.
- P_ℓ ∈ L²(μ) for every ℓ ∈ ℕ.
- β > 0 and c₂ ≥ 0 are reals.
- E P_ℓ → E P as ℓ → ∞ (hlim).
- **For every ℓ ≥ 1:** ∫ Δ_ℓ² dμ ≤ c₂·2^{−βℓ} (h_iii).

Conclusion: **for every ℓ ∈ ℕ, including ℓ = 0,**

  |∫ (P_ℓ − P) dμ| ≤ ( √c₂ / (2^{β/2} − 1) )·2^{−(β/2)ℓ}.

### Junk values
- 2^{β/2} − 1 > 0 because β > 0, √c₂ is genuine, and ∫ (P_ℓ − P) = E P_ℓ − E P is genuine.
- ∫ Δ_ℓ² is genuine only if Δ_ℓ ∈ L². If the real Δ_ℓ were not square-integrable, h_iii would hold vacuously through the junk value 0.
- Under (B), Δ_ℓ ∈ L² because every P_ℓ is in L².

### Satisfiable (witness)
Under (B):
- Take Z ∈ L², P_ℓ = P + 2^{−ℓ}Z, β = 2 and c₂ = E Z².
- Then Δ_ℓ = −2^{−ℓ}Z and ∫ Δ_ℓ² = c₂·2^{−2ℓ}.
- The conclusion reads |2^{−ℓ}·E Z| ≤ √(E Z²)·2^{−ℓ}, which holds by Jensen.
- Trivial alternative: P_ℓ = P = 0.

### Trivial/redundant?
Not trivial.

**Under (B)** the stated constant is exactly what the argument gives:
- E P − E P_ℓ = ∑_{k>ℓ} E Δ_k, by telescoping and hlim.
- |E Δ_k| ≤ (E Δ_k²)^{1/2} ≤ √c₂·2^{−βk/2}.
- ∑_{k≥ℓ+1} 2^{−βk/2} = 2^{−βℓ/2}/(2^{β/2} − 1).

**Under (F) the statement is false.** Take P ≡ 0, P_0 ≡ 100, P_ℓ ≡ 0 for ℓ ≥ 1, c₂ = 0 and β = 1. Then Δ_ℓ = 0 for all ℓ ≥ 1, so every hypothesis holds, but the ℓ = 0 conclusion reads 100 ≤ 0.

The L² hypothesis on P_ℓ is what blocks the junk escape in h_iii.

### Notes
- **Concern:** the statement depends on the undefined `levelDiff`; see the top of this file.
- h_iii is assumed only for ℓ ≥ 1, while the conclusion covers every ℓ ≥ 0. This is consistent under (B).
- The conclusion bounds the weak error |E P_ℓ − E P| using a second-moment decay of Δ_ℓ.

## 3. `allocation_eq_3_1`

### Reads as
Assumptions:
- L ∈ ℕ.
- V, C : ℕ → ℝ with V_ℓ > 0 and C_ℓ > 0 for all ℓ.
- ε > 0.

Let S = ∑_{k=0}^{L} √(V_k C_k), and for each ℓ ≤ L let

  N_ℓ = ⌈ 2ε⁻²·√(V_ℓ/C_ℓ)·S ⌉₊,

the least natural number ≥ that real, used as a real number. Then:

1. ∑_{ℓ=0}^{L} V_ℓ / N_ℓ ≤ ε²/2;
2. ∑_{ℓ=0}^{L} N_ℓ·C_ℓ ≤ 2ε⁻²·S² + ∑_{ℓ=0}^{L} C_ℓ.

### Junk values
- The argument of the ceiling is > 0, so N_ℓ ≥ 1. There is no division by 0 in (1), and the ⌈x⌉₊ = 0 case never occurs.
- ε⁻² is genuine.

### Satisfiable (witness)
L = 0, V_0 = C_0 = 1, ε = 1. Then N_0 = 2, and the two claims read ½ ≤ ½ and 2 ≤ 3. I also checked 2·10⁴ random instances.

### Trivial/redundant?
Elementary:
- N_ℓ ≥ x_ℓ gives V_ℓ/N_ℓ ≤ ε²·√(V_ℓC_ℓ)/(2S), and these sum to ε²/2.
- N_ℓ < x_ℓ + 1 gives (2).

Positivity is assumed for every ℓ but used only for ℓ ≤ L. This is harmless.

### Notes
- Sample sizes here are **natural numbers**, obtained from the ceiling. Contrast `levelKeep_product` in packet 10.
- (1) is non-strict, and equality can occur, as in the witness.

## 4. `remaining_error`

### Reads as
Assumptions:
- (Ω, μ) is a probability space.
- α > 0, a ∈ ℝ, L ∈ ℕ.
- P is integrable, and every P_ℓ is integrable.
- E P_ℓ → E P.
- For every ℓ ≥ L: **∫ Δ_ℓ dμ = a·2^{−αℓ}**. This is an exact equality.

Conclusions:
1. The series ∑_{k=0}^{∞} ∫ Δ_{L+1+k} dμ converges unconditionally (for real series, absolutely), and its sum is ∫ (P − P_L) dμ.
2. ∫ (P − P_L) dμ = (∫ Δ_L dμ) / (2^α − 1).

### Junk values
- 2^α − 1 > 0, and ∫ (P − P_L) = E P − E P_L is genuine.
- ∫ Δ_ℓ would be a junk 0 if Δ_ℓ were not integrable. Under (B), Δ_ℓ is integrable.

### Satisfiable (witness)
Under (B):
- Take constants P ≡ c and P_ℓ ≡ c − a·2^{−αℓ}/(2^α − 1), with L ≥ 1. Then E Δ_ℓ = a·2^{−αℓ} for every ℓ ≥ 1.
- Trivial alternative: a = 0 and P_ℓ = P = 0.

### Trivial/redundant?
Not trivial.

**Under (B)** both conclusions hold:
- The partial sums telescope to E P_{L+K} − E P_L, which tends to E P − E P_L.
- The terms are a·2^{−α(L+1+k)}, which are absolutely summable.
- Their sum is a·2^{−αL}/(2^α − 1) = E Δ_L/(2^α − 1), using the ℓ = L case of the hypothesis. This works for L = 0 as well, whatever Δ_0 is.

**Under (F) it is false unless a = 0.** The telescoping sum becomes E P − E P_{L+1}, and in fact E P − E P_L = 2^α·E Δ_L/(2^α − 1).

Numeric check with α = 1.3, a = 0.8, L = 3:
- the (B) series sums to 0.036647, which equals E P − E P_L and equals E Δ_L/(2^α − 1);
- the (F) series sums to 0.014883, which does not.

### Notes
- **Concern:** the statement depends on the undefined `levelDiff`.
- **The decay hypothesis is an exact geometric law for the level means from L onward**: E Δ_ℓ = a·2^{−αℓ} for every ℓ ≥ L. It is not a bound and not an asymptotic "≈". Conclusion (2) is exact under that model. It says nothing when the means are only approximately geometric.

## 5. `convergence_test_mse`

### Reads as
Assumptions:
- (Ω, μ) is a probability space.
- α > 0; a, ε ∈ ℝ; L ∈ ℕ.
- Y ∈ L², P is integrable, and every P_ℓ is integrable.
- E P_ℓ → E P.
- **Exact geometric level means:** E Δ_ℓ = a·2^{−αℓ} for every ℓ ≥ L.
- E Y = E P_L.
- Var Y ≤ ε²/2.
- |∫ Δ_L dμ| / (2^α − 1) < ε/√2.

Conclusion:

  E_μ[(Y − E P)²] < ε².

### Junk values
None is active:
- ε > 0 is forced by the last hypothesis.
- √2 is genuine, and Y ∈ L².

### Satisfiable (witness)
Under (B):
- a = 0, P = P_ℓ = Y = 0 and ε = 1. The test reads 0 < 1/√2 and the conclusion reads 0 < 1.
- Non-degenerate: take the constant witness from `remaining_error`, with Y ≡ E P_L and ε large enough.

### Trivial/redundant?
**Under (B)** the conclusion holds:
- By the (B)-argument of `remaining_error`, E P_L − E P = −E Δ_L/(2^α − 1).
- So MSE = Var Y + (E Δ_L)²/(2^α − 1)² < ε²/2 + ε²/2.

**Under (F) it is false in general**, because the true bias is 2^α times larger. Take α = 1, Y ≡ E P_L (so Var Y = 0), and |E Δ_L|/(2^α − 1) = 0.9ε/√2. Then MSE = (1.8ε/√2)² = 1.62ε², which exceeds ε².

### Notes
- **Concern:** this has the same undefined `levelDiff` and the same exact-geometric-model assumption as `remaining_error`.
- Y is any L² random variable with E Y = E P_L and Var Y ≤ ε²/2. No estimator structure is involved.
- The variance bound is non-strict, the bias test is strict, and the conclusion is strict.

## 6. `consistency_mean`

### Reads as
Assumptions:
- (Ω, μ) is a probability space, and ℓ ∈ ℕ.
- a, b, c : Ω → ℝ are integrable.
- Pf_k and Pc_k : Ω → ℝ are integrable for every k.
- E Pf_ℓ = E Pc_ℓ (h24).
- E a = E Pf_ℓ.
- E b = E Pf_{ℓ+1}.
- E c = ∫ (Pf_{ℓ+1} − Pc_ℓ) dμ.

Conclusion:

  ∫ (a − b + c) dμ = 0.

### Junk values
None is active.

### Satisfiable (witness)
- All functions equal to 0.
- Or: a = Pf_ℓ, b = Pf_{ℓ+1}, c = Pf_{ℓ+1} − Pc_ℓ, with E Pc_ℓ = E Pf_ℓ.

### Trivial/redundant?
**It is near-tautological.** Expanding,

  E(a − b + c) = E Pf_ℓ − E Pf_{ℓ+1} + (E Pf_{ℓ+1} − E Pc_ℓ) = E Pf_ℓ − E Pc_ℓ,

which is 0 by h24.
- The random variables enter only through their means.
- The substantive identity E Pf_ℓ = E Pc_ℓ is **assumed** (h24), not derived.
- Integrability of Pf_k for k ≠ ℓ+1 and of Pc_k for k ≠ ℓ is unused.

### Notes
The statement is about expectations only.

## 7. `covariance_sq_le`

### Reads as
Assumptions: (Ω, μ) is a probability space and X, Y ∈ L²(μ).

Conclusion:

  Cov(X, Y)² ≤ Var X·Var Y.

### Junk values
None is active.

### Satisfiable (witness)
Any X, Y ∈ L². For example X = Y = 1_A gives equality.

### Trivial/redundant?
This is standard Cauchy–Schwarz. The hypotheses are needed. Take X ∈ L¹∖L² with E X = 0 and Y = 1_{X>0}. Then Var X = 0 by convention, but Cov(X, Y) = E[X; X > 0] > 0.

### Notes
None.

## 8. `sqrt_variance_add_le`

### Reads as
Assumptions: (Ω, μ) is a probability space and X, Y ∈ L²(μ).

Conclusion:

  √Var(X + Y) ≤ √Var X + √Var Y.

### Junk values
None is active. The variances are genuine and ≥ 0, so √ is never clipped.

### Satisfiable (witness)
Any X, Y ∈ L².

### Trivial/redundant?
This is standard: Minkowski's inequality for standard deviations. The hypotheses are needed. Take X = Z + W and Y = −Z, with Z ∈ L¹∖L² and W ∈ L², Var W > 0. The left side is √Var W > 0, while the right side is 0 by convention.

### Notes
None.

## 9. `sqrt_variance_sub_le`

### Reads as
Assumptions: (Ω, μ) is a probability space and X, Y ∈ L²(μ).

Conclusion:

  √Var(X − Y) ≤ √Var X + √Var Y.

### Junk values
None is active.

### Satisfiable (witness)
Any X, Y ∈ L².

### Trivial/redundant?
Standard. The hypotheses are needed; the counterexample is as in item 8, with Y = Z.

### Notes
None.

## 10. `consistency_sd`

### Reads as
Assumptions: (Ω, μ) is a probability space and a, b, c ∈ L²(μ).

Conclusion:

  √Var(a − b + c) ≤ √Var a + √Var b + √Var c.

### Junk values
None is active.

### Satisfiable (witness)
Any a, b, c ∈ L².

### Trivial/redundant?
Standard: apply Minkowski twice. The L² hypotheses make every term genuine.

### Notes
None.

## 11. `kurtosis` (definition)

### Reads as
For a measurable space Ω₀, a function X : Ω₀ → ℝ and **any** measure ν:

  κ_ν(X) = ( ∫ X⁴ dν ) / ( ∫ X² dν )².

- This uses **raw (non-central) moments**: it is E X⁴ / (E X²)².
- It equals the usual (Pearson) kurtosis E(X − E X)⁴ / Var(X)² only when E X = 0 and ν is a probability measure.
- It is not the excess kurtosis; there is no "− 3".

### Junk values
- If X² is not integrable, the denominator is a junk 0, so κ = 0.
- If X⁴ is not integrable, the numerator is a junk 0, so κ = 0.
- If X = 0 almost everywhere, κ = 0/0 = 0.

### Satisfiable (witness)
- ν = fair coin on {±1} and X = id: κ = 1.
- ν uniform on {−1, 0, 1}: κ = (2/3)/(4/9) = 3/2.

### Trivial/redundant?
Not applicable.

### Notes
- `sampleVariance_sd` assumes E X = 0, so there κ is the standard kurtosis.
- `kurtosis_of_ternary` and `tendsto_kurtosis_atTop` make **no** mean-zero assumption, so there κ is the raw ratio E X⁴/(E X²)².

## 12. `sampleVariance_sd`

### Reads as
Assumptions:
- (Ω, μ) is a probability space and (Ω₀, ν) is a measure space.
- The maps ω_n : Ω → Ω₀ are measurable, each has law ν, and they are mutually independent (n ∈ ℕ).
- X : Ω₀ → ℝ is measurable.
- X⁴ is ν-integrable.
- ∫ X dν = 0.
- ∫ X² dν > 0.
- N ≥ 1.

Define Ŝ_N(x) = (1/N) ∑_{n=0}^{N−1} X(ω_n(x))². Then:

1. E_μ[Ŝ_N] = Var_ν X.
2. √(Var_μ Ŝ_N) = √( (κ_ν(X) − 1)/N )·∫ X² dν.

### Junk values
None is active under the stated hypotheses:
- ν is a probability measure (by hω).
- X ∈ L⁴ ⊂ L² ⊂ L¹, so Var_ν X = ∫ X² is genuine.
- κ is genuine, since its denominator is > 0.
- κ − 1 ≥ 0 by Jensen (E X⁴ ≥ (E X²)²), so √ is not clipped.
- Ŝ_N ∈ L²(μ).

### Satisfiable (witness)
- **Degenerate:** Ω = [0,1) with Lebesgue measure; Rademacher maps ω_n into Ω₀ = ℝ; ν = ½δ₋₁ + ½δ₁; X = id. Then E X² = 1, κ = 1 and Ŝ_N ≡ 1, so (1) reads 1 = 1 and (2) reads 0 = 0.
- **Non-degenerate:** ν uniform on {−1, 0, 1}, using i.i.d. ternary digits. Then E X² = 2/3 and κ = 3/2, and both sides of (2) equal √(2/(9N)).

I checked this exactly by enumerating the product space for N = 1, 2, 3 on 300 random mean-zero finite distributions.

### Trivial/redundant?
Not trivial.
- hX0 is needed for (1), because Var X = E X² only when the mean is 0. (2) would hold without hX0.
- **hpos and hX4 give the statement its meaning, but each is logically redundant, and so are both together.** The conclusions still hold without them, through junk conventions:
  - If X = 0 almost everywhere, everything is 0.
  - If X ∈ L²∖L⁴, then Ŝ_N ∉ L², so the left side of (2) is 0. Also κ = 0, so √(−1/N) = 0 and the right side is 0.
  - If X ∉ L², every term is a junk 0.

So a proof does not need these two hypotheses. Their presence is what makes (2) non-degenerate.

### Notes
- The estimator Ŝ_N is the **mean of squares**, i.e. the variance estimator for a known mean of zero. It is **not** the usual sample variance (1/(N−1))∑(X_n − X̄)².
- (2) is a statement about the standard deviation of this particular estimator.
- N is a natural number.
- ν is not declared a probability measure, but hω forces it to be one.

## 13. `kurtosis_of_ternary`

### Reads as
Assumptions:
- (Ω, μ) is a probability space.
- X : Ω → ℝ is measurable.
- X(ω) ∈ {−1, 0, 1} **for every** ω (pointwise, not almost surely).
- p := μ({X ≠ 0}) > 0.

Conclusion:

  κ_μ(X) = 1/p.

### Junk values
None is active. X⁴ = X² = 1_{X≠0}, so both integrals equal p > 0.

### Satisfiable (witness)
- X ≡ 1: κ = 1 = 1/1.
- Ω = {1, 2, 3} uniform with X = (−1, 0, 1): p = 2/3 and κ = 3/2.

### Trivial/redundant?
Elementary.
- **hp is logically redundant.** If p = 0, then κ = 0/0 = 0 and 1/p = 0⁻¹ = 0, so both sides are 0.
- The measurability hypothesis hXm is needed.

### Notes
- There is no assumption that E X = 0, and no symmetry assumption.
- "Kurtosis" here is the raw ratio E X⁴/(E X²)². For a ternary X with E X ≠ 0, this differs from the central kurtosis.

## 14. `tendsto_kurtosis_atTop`

### Reads as
Assumptions:
- (Ω, μ) is a probability space.
- X_ℓ : Ω → ℝ is measurable for each ℓ ∈ ℕ.
- Each X_ℓ takes values in {−1, 0, 1} everywhere.
- p_ℓ := μ(X_ℓ ≠ 0) > 0 for every ℓ.
- E X_ℓ² → 0.

Conclusion:

  κ_μ(X_ℓ) → +∞ as ℓ → ∞.

### Junk values
- hp rules out the 0/0 = 0 junk value.
- Without hp, κ would be 0 at every level with p_ℓ = 0, and the conclusion could fail. So hp is **needed** here.

### Satisfiable (witness)
Take Ω = [0, 1] with Lebesgue measure and X_ℓ = 1_{[0, 2^{−ℓ}]}. Then p_ℓ = 2^{−ℓ} and κ = 2^ℓ → ∞.

Any witness needs events of arbitrarily small positive probability, so no finite Ω works. That is fine.

### Trivial/redundant?
It follows directly from item 13: κ(X_ℓ) = 1/p_ℓ, and E X_ℓ² = p_ℓ → 0⁺.

### Notes
Kurtosis here is the raw ratio, as in item 13.

---

## Summary

| Declaration | Verdict | One-line reason |
|---|---|---|
| `mse_lt_of_half` | OK | Genuine bias–variance bound; all hypotheses needed; ε ≠ 0 forced |
| `weak_rate_of_second_moment` | **concern** | Uses `levelDiff`, which is **not defined in the packet**. True if Δ_ℓ = P_ℓ − P_{ℓ−1} (ℓ ≥ 1); false under the forward-difference reading (counterexample) |
| `allocation_eq_3_1` | OK | Genuine; natural-number sample sizes N_ℓ ≥ 1 via ceiling, no junk division |
| `remaining_error` | **concern** | `levelDiff` undefined (same dependence); hypothesis is an **exact** geometric law E Δ_ℓ = a·2^{−αℓ} for all ℓ ≥ L, not a bound |
| `convergence_test_mse` | **concern** | Same `levelDiff` dependence and exact-geometric assumption; Y is any L² r.v. with the right mean and variance |
| `consistency_mean` | OK (note) | Only linear bookkeeping of hypothesised means; the key identity E Pf_ℓ = E Pc_ℓ is a hypothesis |
| `covariance_sq_le` | OK | Cauchy–Schwarz; L² needed |
| `sqrt_variance_add_le` | OK | Minkowski for standard deviations; L² needed |
| `sqrt_variance_sub_le` | OK | Same, for X − Y |
| `consistency_sd` | OK | Minkowski twice |
| `kurtosis` | OK (note) | **Raw** moments E X⁴/(E X²)², central only when E X = 0; junk 0 when moments are missing or zero |
| `sampleVariance_sd` | OK (note) | Estimator is the mean of squares (known mean 0), not the usual sample variance; hX4/hpos give meaning but are logically redundant via junk |
| `kurtosis_of_ternary` | OK (note) | Raw kurtosis (no mean-zero assumption); hp redundant (0/0 = 0 = 0⁻¹) |
| `tendsto_kurtosis_atTop` | OK | Genuine; hp needed |

- No statement in packet 11 is vacuous: every hypothesis set has a witness, conditionally on (B) for the three `levelDiff` statements.
- Under the stated hypotheses, no conclusion holds only because of a junk convention.
- The main open item is the missing definition of `levelDiff`. It decides whether `weak_rate_of_second_moment`, `remaining_error` and `convergence_test_mse` are true at all.
