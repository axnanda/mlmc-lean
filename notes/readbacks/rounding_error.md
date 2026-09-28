# Read-back audit: packet 14 (round 4)

- **Date:** 2026-09-27
- **Packet:** `/tmp/claude-0/-home-user-mlmc-lean/8f263d87-ec2c-550e-ae99-ab3862cfe2e3/scratchpad/readback/round4/packet14.lean`. It has 18 declarations: 3 definitions and 15 theorems, with proofs replaced by `sorry`.
- **Auditor:** an independent, blind sub-agent.
- **Rules followed:**
  - **Files read.** I read only the packet, `references/mission_auditor.md`, and Mathlib sources. I used Mathlib only to confirm the definitions and conventions of the constants the statements use. I did not open the project's Lean sources, `docs/`, `notes/`, README, PLAN, metadata, scripts, git history, any paper, or the web.
  - **Translation.** I translated the code, not any presumed intent, and inferred no meaning from declaration or file names. Every binder, hypothesis and typeclass assumption is listed. Non-standard definitions are expanded inline. Degenerate cases and junk values are surfaced. The exact strength of every relation is kept (≤ vs <, ∃, direction).
  - **Read-back kept neutral.** Section 1 of each entry is a neutral read-back. The judgements asked for by the caller are in sections 2 to 5: truth, non-vacuity, junk values and concerns.
  - **Sanity checks.** Numeric checks used Python: exact rational arithmetic on finite probability spaces, and Monte Carlo for the continuous uniform laws. Parse and elaboration checks used the bare Lean core toolchain on a scratch file, with no Mathlib and no project import. All scripts are in `scratchpad/readback/round4/checks14/`.

---

## Conventions (confirmed in Mathlib sources or with the Lean core toolchain)

- **Integer exponents.** In e ∈ ℤ, d ∈ ℕ, the expressions "e − d" and "e − d − 1" are integer subtractions. d is cast to ℤ and there is no truncation at 0 (core Lean: e = 0, d = 5 gives −6). For k ∈ ℤ, 2^k and 4^k are real integer powers (zpow), so 2^k = 1/2^(−k) for k < 0, and they are always > 0. In `roundFixed_mantissa`, 2^d with d ∈ ℕ is an ordinary power in ℤ.
- **Negation vs power.** `-(2 : ℝ) ^ k` parses as −(2^k), not (−2)^k. In core Lean, `-(2 : Int) ^ 2` evaluates to −4. Mathlib's `Odd.neg_pow : (-a) ^ n = -a ^ n` relies on the same parse. So every interval [−2^k, 2^k] below is symmetric with half-width 2^k > 0.
- **round** (`Mathlib/Algebra/Order/Round.lean`): round(y) = ⌊y⌋ if 2·fract(y) < 1, and ⌈y⌉ otherwise. Equivalently round(y) = ⌊y + 1/2⌋ (`round_eq`). It is the nearest integer, with ties broken toward +∞: round(1/2) = 1, round(−1/2) = 0, and |y − round(y)| ≤ 1/2 (`abs_sub_round`).
- **Bochner integral** (`MeasureTheory/Integral/Bochner/Basic.lean`): ∫ f dμ := 0 whenever f is not μ-integrable, including when f is not μ-a.e.-strongly measurable. Below, E[f] := ∫ f dμ.
- **L².** "f ∈ L²(μ)" renders `MemLp f 2 μ`: f is μ-a.e.-strongly measurable and ∫ |f|² dμ < ∞.
- **Variance** (`Probability/Moments/Variance.lean`): Var(Y) := toReal(∫⁻ |Y − E[Y]|² dμ). This is a lower Lebesgue integral in [0, ∞] converted to ℝ, with ∞ ↦ 0.
  - For Y ∈ L²(μ) and μ finite, it is the usual variance.
  - For μ finite and Y a.e.-strongly measurable but Y ∉ L²(μ), Var(Y) = 0 (`evariance_eq_top`).
  - It is always ≥ 0.
- **Covariance** (`Probability/Moments/Covariance.lean`): Cov(X, Y) := ∫ (X − E[X])·(Y − E[Y]) dμ, a Bochner integral.
- **Independence** (`Probability/Independence/Basic.lean`): "f ⫫ g" renders `IndepFun f g μ`. It means μ(f⁻¹A ∩ g⁻¹B) = μ(f⁻¹A)·μ(g⁻¹B) for all Borel A, B ⊆ ℝ.
- **Pairwise** (`Logic/Pairwise.lean`): `Set.Pairwise S r` means r(a, b) for all a, b ∈ S with a ≠ b.
- **Uniform law** (`Probability/Distributions/Uniform.lean`, `ConditionalProbability.lean`, `MeasureTheory/Measure/Map.lean`): `pdf.IsUniform X S μ` means X₊μ = (λ(S))⁻¹ · λ|_S.
  - λ is Lebesgue measure on ℝ, and the arithmetic is in [0, ∞].
  - The pushforward X₊μ is *defined to be the zero measure* when X is not μ-a.e. measurable.
  - For S = [−c, c] with c > 0, the right-hand side is a probability measure. The hypothesis then says exactly that X is μ-a.e. measurable and μ(X ∈ B) = λ(B ∩ [−c, c]) / (2c) for all Borel B.
  - In particular it forces μ(Ω) = 1 and |X| ≤ c μ-a.e.
- **Disjoint sum** (`Data/Finset/Sum.lean`): s ⊔ t := {inl i : i ∈ s} ∪ {inr j : j ∈ t}, a finite subset of the disjoint union ι ⊕ κ. `Sum.elim f g` means f on inl-points and g on inr-points.
- **Square root.** √ is `Real.sqrt`, and √y = 0 for y < 0.
- **Finite sums.** Σ[i ∈ s] aᵢ is the finite sum over the finite set s, and it is 0 if s = ∅.
- **Standing setting.** For declarations 9–15, 17 and 18, (Ω, 𝓕) is a measurable space and μ is a **probability** measure on it. Declaration 4 declares the probability instance itself. For declarations 5 and 6, μ is an arbitrary measure.

---

## 1. `roundFixed` (definition)

1. **Rendering.** For e ∈ ℤ, d ∈ ℕ and x ∈ ℝ, put h := 2^(e−d) > 0. Then

   roundFixed(e, d, x) := h · round(x / h) = h · ⌊x/h + 1/2⌋.

   This is the point of the grid hℤ = {h·k : k ∈ ℤ} nearest to x. When x is exactly halfway between two grid points, it is the larger one.
2. **Truth.** Not applicable (definition). It is well defined for all inputs, since h > 0 and there is no division by zero.
3. **Non-vacuity.** Not applicable.
4. **Junk values.** None.
5. **Concerns (note).**
   - Ties go toward +∞, so the map is not odd-symmetric: roundFixed(e, d, h/2) = h but roundFixed(e, d, −h/2) = 0. It is not ties-to-even.
   - The grid spacing depends only on (e, d), never on x. There is no exponent chosen from |x|, no bound on the integer multiplier (so no overflow or saturation), and no subnormal handling.
   - d enters only through the integer e − d.

## 2. `abs_sub_roundFixed_le`

1. **Rendering.** For all e ∈ ℤ, d ∈ ℕ and x ∈ ℝ:

   |x − roundFixed(e, d, x)| ≤ 2^(e−d−1).
2. **Truth: true.** With h = 2^(e−d), |x − h·round(x/h)| = h·|x/h − round(x/h)| ≤ h/2 = 2^(e−d−1). Python checked 20,000 random rational cases, including exact ties. The largest ratio of error to bound was 1, attained at ties.
3. **Non-vacuity.** There are no hypotheses.
4. **Junk values.** None.
5. **Concerns.** None. The bound is sharp: equality holds at x = (m + 1/2)·h.

## 3. `roundFixed_mantissa`

1. **Rendering.** For all e ∈ ℤ, d ∈ ℕ and x ∈ ℝ: if |x| < 2^e − 2^(e−d−1), then there is an integer k such that |k| < 2^d (compared in ℤ) and roundFixed(e, d, x) = 2^(e−d) · k.
2. **Truth: true.** k is forced to be round(x/h) with h = 2^(e−d). The hypothesis is equivalent to |x/h| < 2^d − 1/2. That gives −2^d + 1 < x/h + 1/2 < 2^d, hence −(2^d − 1) ≤ ⌊x/h + 1/2⌋ ≤ 2^d − 1. Python checked 20,000 cases, including points within 10⁻⁹ of both ends.
3. **Non-vacuity.** 2^e − 2^(e−d−1) ≥ 2^(e−1) > 0 for every e and d. So x = 0 with k = 0 is a witness.
4. **Junk values.** None.
5. **Concerns.**
   - Because 2^(e−d) ≠ 0, k is unique. The real content is |round(x/h)| ≤ 2^d − 1.
   - The strict hypothesis is sharp. At x = +(2^e − 2^(e−d−1)) exactly, ties-up rounding gives k = 2^d. At the negative end, k = −(2^d − 1), so there is slack on that side.
   - The statement says nothing about larger |x|.

## 4. `integral_sq_roundError_le`

1. **Rendering.** Let μ be a probability measure on (Ω, 𝓕). For all e ∈ ℤ, d ∈ ℕ and every function X : Ω → ℝ (no measurability is assumed):

   ∫ (X(ω) − roundFixed(e, d, X(ω)))² dμ(ω) ≤ 4^(e−d−1).
2. **Truth: true.** By #2 the integrand g satisfies 0 ≤ g ≤ (2^(e−d−1))² = 4^(e−d−1) pointwise. If g is integrable, then ∫ g ≤ 4^(e−d−1)·μ(Ω) = 4^(e−d−1). Otherwise ∫ g = 0 < 4^(e−d−1). Python checked 2,000 random discrete laws.
3. **Non-vacuity.** Take Ω a single point with the Dirac measure and X ≡ 0: the left side is 0. With X ≡ 2^(e−d−1), a tie point, the left side is 4^(e−d−1), so equality is attained and the bound is sharp.
4. **Junk values.**
   - For a.e.-measurable X, g is bounded and measurable (roundFixed is Borel), hence integrable, and the bound is genuine.
   - For X such that g is not a.e.-strongly measurable, the left side is the junk value 0 and the inequality holds trivially. The statement quantifies over such X too.
5. **Concerns (note).**
   - The constant is the worst-case h²/4 with h = 2^(e−d), not a uniform-model h²/12.
   - The probability assumption matters: the bound can fail if μ(Ω) > 1.
   - (e, d) are the same for every ω.

## 5. `integral_sq_of_isUniform`

1. **Rendering.** Let μ be **any** measure on (Ω, 𝓕); no finiteness is assumed. Let X : Ω → ℝ and a ∈ ℝ, and suppose:
   - (i) a > 0;
   - (ii) the law of X under μ is the normalised Lebesgue measure on [−a, a], i.e. X₊μ = (2a)⁻¹ · λ|_[−a,a].

   Then ∫ X(ω)² dμ(ω) = a²/3.
2. **Truth: true.** Hypothesis (ii) makes X₊μ a probability measure. So X is μ-a.e. measurable (otherwise X₊μ = 0), and μ(Ω) = X₊μ(ℝ) = 1. By change of variables, ∫ X² dμ = (2a)⁻¹ ∫_[−a,a] x² dx = (2a)⁻¹ · 2a³/3 = a²/3. An exact rational check agrees.
3. **Non-vacuity.** Witness: Ω = ℝ, μ = (2a)⁻¹·λ|_[−a,a], X = identity, a = 1.
4. **Junk values.** None. |X| ≤ a μ-a.e., so X² is integrable and a²/3 is the genuine value.
5. **Concerns.**
   - μ is not declared a probability measure, but (ii) forces μ(Ω) = 1.
   - Hypothesis (i) is not redundant:
     - For a < 0 the interval is empty and the normalised measure is the zero measure. Then μ = 0 satisfies (ii), and the conclusion 0 = a²/3 fails.
     - For a = 0 the normalised measure is also 0, so (ii) degenerates to "μ = 0 or X is not a.e. measurable". It can then fail. Example: Ω = [0, 1], X = 1_A − 1_(Aᶜ) with A non-measurable of inner measure 0 and outer measure 1. Then ∫ X² = 1 ≠ 0.

## 6. `integral_sq_uniform_roundError`

1. **Rendering.** Let μ be **any** measure on (Ω, 𝓕), δ : Ω → ℝ, e ∈ ℤ and d ∈ ℕ. If the law of δ under μ is the normalised Lebesgue measure on [−2^(e−d−1), 2^(e−d−1)], then

   ∫ δ(ω)² dμ(ω) = 4^(e−d) / 12.
2. **Truth: true.** This is #5 with a = 2^(e−d−1) > 0: a²/3 = 4^(e−d−1)/3 = 4^(e−d)/12. Exact checks for e ∈ [−4, 4] and d ∈ [0, 5] agree.
3. **Non-vacuity.** Witness: Ω = ℝ, μ uniform on that interval, δ = identity.
4. **Junk values.** None.
5. **Concerns.**
   - As in #5, μ(Ω) = 1 is forced, and no positivity hypothesis is needed because the half-width 2^(e−d−1) is automatically > 0.
   - With h = 2^(e−d) the value is h²/12.
   - δ is any random variable with this law; nothing links δ to `roundFixed`.

## 7. `vIndep` (definition)

1. **Rendering.** For a type ι, a finite set s ⊆ ι, M : ι → ℝ, e : ι → ℤ and d : ι → ℕ:

   vIndep(s, M, e, d) := (1/12) · Σ[i ∈ s] Mᵢ · 4^(eᵢ−dᵢ).
2. **Truth.** Not applicable.
3. **Non-vacuity.** Not applicable.
4. **Junk values.** None. 1/12 is the real number 1/12, not natural-number division, because the definition's type is ℝ. An empty s gives 0.
5. **Concerns.** None. There is no sign constraint on M, and negative Mᵢ contribute negatively. With hᵢ = 2^(eᵢ−dᵢ), vIndep = Σ Mᵢ·hᵢ²/12.

## 8. `vCorr` (definition)

1. **Rendering.** With the same data,

   vCorr(s, M, e, d) := (Σ[i ∈ s] √Mᵢ · 2^(eᵢ−dᵢ−1))²,

   where √Mᵢ := 0 when Mᵢ < 0.
2. **Truth.** Not applicable.
3. **Non-vacuity.** Not applicable.
4. **Junk values.** Negative Mᵢ silently contribute 0 through the √ convention. An empty s gives 0, and vCorr is always ≥ 0.
5. **Concerns (note).** None beyond the √ convention. With hᵢ = 2^(eᵢ−dᵢ), vCorr = (Σ √Mᵢ·hᵢ/2)².

## 9. `variance_sum_eq`

1. **Rendering.** Let μ be a probability measure. Let ι be a type with decidable equality (a technical instance used to remove an element from a finite set), s a finite subset of ι, and Xᵢ : Ω → ℝ for each i ∈ ι. If Xᵢ ∈ L²(μ) for every i ∈ s, then

   Var(Σ[i ∈ s] Xᵢ) = Σ[i ∈ s] Var(Xᵢ) + Σ[i ∈ s] Σ[j ∈ s, j ≠ i] Cov(Xᵢ, Xⱼ).
2. **Truth: true.** For L² variables Var(ΣXᵢ) = Σᵢ Σⱼ Cov(Xᵢ, Xⱼ) (Mathlib `variance_fun_sum'`), and Cov(Xᵢ, Xᵢ) = Var(Xᵢ) (`covariance_self`). An exact identity check on 300 random finite probability spaces with arbitrary dependence agrees.
3. **Non-vacuity.** Any finite L² family is a witness, e.g. Xᵢ ≡ 0.
4. **Junk values.** None. Every term is genuine under the L² hypothesis.
5. **Concerns.** None. The off-diagonal double sum counts each unordered pair twice, as it should. Values of Xᵢ for i ∉ s are irrelevant.

## 10. `variance_le_integral_sq`

1. **Rendering.** Let μ be a probability measure, and x̄, δ : Ω → ℝ both μ-a.e.-strongly measurable. Then

   Var(x̄·δ) ≤ ∫ x̄(ω)² · δ(ω)² dμ(ω).
2. **Truth: true.**
   - If Y := x̄δ ∈ L², then Var(Y) = E[Y²] − E[Y]² ≤ E[Y²].
   - If Y ∉ L², then Var(Y) = 0 by convention and Y² is not integrable, so the right side is 0 and the inequality reads 0 ≤ 0.

   This is Mathlib's `variance_le_expectation_sq` applied to Y.
3. **Non-vacuity.** x̄ ≡ δ ≡ 1 (0 ≤ 1) is a witness, as is any product in L².
4. **Junk values: partly.** When x̄δ ∉ L², *both* sides are 0 by convention: the variance of a non-L² variable is 0, and the integral of a non-integrable function is 0. So the statement is trivially true there. It has content only when x̄δ ∈ L².
5. **Concerns (note).** There is no L² hypothesis and no independence. The right side is E[(x̄δ)²], not E[x̄²]·E[δ²].

## 11. `variance_sum_mul_le_of_indep`

1. **Rendering.** Let μ be a probability measure, ι a type, s ⊆ ι finite, and sensᵢ, errᵢ : Ω → ℝ for i ∈ ι. Hypotheses:
   - (a) sensᵢ·errᵢ ∈ L²(μ) for every i ∈ s;
   - (b) sensᵢ is μ-a.e.-strongly measurable for every i ∈ s;
   - (c) errᵢ is μ-a.e.-strongly measurable for every i ∈ s;
   - (d) sensᵢ ⫫ errᵢ for every i ∈ s;
   - (e) sensᵢ·errᵢ ⫫ sensⱼ·errⱼ for all distinct i, j ∈ s.

   Conclusion:

   Var(Σ[i ∈ s] sensᵢ·errᵢ) ≤ Σ[i ∈ s] (∫ sensᵢ² dμ) · (∫ errᵢ² dμ).
2. **Truth: true.**
   - Yᵢ := sensᵢ·errᵢ is in L² and the Yᵢ are pairwise independent, so Cov(Yᵢ, Yⱼ) = 0 for i ≠ j. Hence Var(ΣYᵢ) = Σ Var(Yᵢ) ≤ Σ E[Yᵢ²].
   - By (b)–(d), sensᵢ² ⫫ errᵢ², so ∫⁻ Yᵢ² = ∫⁻ sensᵢ² · ∫⁻ errᵢ² in [0, ∞].
   - The left side is finite. So either both factors are finite, and then E[Yᵢ²] equals the i-th right-hand term; or one factor is 0 (that function vanishes a.e.), and then both E[Yᵢ²] and the right-hand term are 0.
   - Exact checks on 200 random product spaces agree.
3. **Non-vacuity.** Witness: Ω = [0, 1]^(2n) with Lebesgue measure, and sensᵢ, errᵢ bounded functions of distinct coordinates. Simpler still, sensᵢ ≡ 1 with errᵢ on separate coordinates.
4. **Junk values.** The right-hand factors are Bochner integrals, which are 0 when sensᵢ or errᵢ ∉ L². Under the hypotheses that only happens when the partner factor vanishes a.e. Then Yᵢ = 0 a.e. and the true contribution is also 0, so the junk value never decides the inequality.
5. **Concerns.** None. Only pairwise independence of the products is assumed, which suffices. The bound drops the terms (E[sensᵢ]·E[errᵢ])².

## 12. `variance_linearised_indep`

1. **Rendering.** Let μ be a probability measure, ι a type, s ⊆ ι finite, x̄ᵢ, δᵢ : Ω → ℝ, and eᵢ ∈ ℤ, dᵢ ∈ ℕ. Hypotheses:
   - (a) x̄ᵢ ∈ L²(μ) for every i ∈ s;
   - (b) for every i ∈ s, the law of δᵢ is uniform on [−2^(eᵢ−dᵢ−1), 2^(eᵢ−dᵢ−1)], as expanded in the conventions. This implies δᵢ is a.e. measurable and |δᵢ| ≤ 2^(eᵢ−dᵢ−1) a.e.
   - (c) x̄ᵢ ⫫ δᵢ for every i ∈ s;
   - (d) x̄ᵢδᵢ ⫫ x̄ⱼδⱼ for all distinct i, j ∈ s.

   Conclusion:

   Var(Σ[i ∈ s] x̄ᵢ·δᵢ) ≤ vIndep(s, i ↦ ∫ x̄ᵢ² dμ, e, d) = (1/12) · Σ[i ∈ s] (∫ x̄ᵢ² dμ) · 4^(eᵢ−dᵢ).
2. **Truth: true.** x̄ᵢδᵢ ∈ L² because δᵢ is bounded. Then #11 and #6 give Var ≤ Σ E[x̄ᵢ²]·4^(eᵢ−dᵢ)/12. In fact **equality** holds: E[δᵢ] = 0 gives E[x̄ᵢδᵢ] = 0, so Var(x̄ᵢδᵢ) = E[x̄ᵢ²]·E[δᵢ²]. A Monte Carlo run (3 terms, 400,000 samples) gave Var / vIndep = 0.9997.
3. **Non-vacuity.**
   - Single index: s = {1}, Ω = ℝ with μ uniform on [−c, c] where c = 2^(e₁−d₁−1), δ₁ = identity, x̄₁ ≡ 1 (a constant is independent of everything). Then Var = c²/3 = vIndep.
   - Several indices: a product space with each x̄ᵢ and δᵢ on its own coordinate.
   - Dithered rounding also works. δᵢ := (x̄ᵢ + Uᵢ) − roundFixed(eᵢ, dᵢ, x̄ᵢ + Uᵢ), with Uᵢ uniform on [−hᵢ/2, hᵢ/2] and independent of x̄ᵢ, satisfies (b) and (c). A simulation confirmed this.
4. **Junk values.** None.
5. **Concerns (note).**
   - The conclusion is stated as ≤, although the hypotheses give equality.
   - δᵢ is an abstract random variable, not defined from `roundFixed`. Hypotheses (b) and (c) **cannot both hold if δᵢ is a measurable function of x̄ᵢ**, for example δᵢ = x̄ᵢ − roundFixed(eᵢ, dᵢ, x̄ᵢ). In that case δᵢ ⫫ δᵢ, so δᵢ is a.s. constant, which contradicts a uniform law on an interval of positive length. The theorem therefore applies to noise that is exogenous to x̄ᵢ, not to deterministic rounding of x̄ᵢ itself.
   - The pairwise independence (d) of the products is assumed, not derived.

## 13. `variance_sum_le_sq_sum_sqrt`

1. **Rendering.** Let μ be a probability measure, s ⊆ ι finite, and Yᵢ : Ω → ℝ. If Yᵢ ∈ L²(μ) for every i ∈ s, then

   Var(Σ[i ∈ s] Yᵢ) ≤ (Σ[i ∈ s] √Var(Yᵢ))².
2. **Truth: true.** By Minkowski (the triangle inequality in L² for the centred variables), sd(ΣYᵢ) ≤ Σ sd(Yᵢ). Squaring the two nonnegative sides gives the claim. Checked on 300 random finite spaces with correlated Yᵢ.
3. **Non-vacuity.** Any L² family is a witness. Equality holds for Yᵢ = cᵢ·Z with cᵢ ≥ 0.
4. **Junk values.** None. Var ≥ 0, so each √ is genuine.
5. **Concerns.** None.

## 14. `sqrt_variance_mul_le`

1. **Rendering.** Let μ be a probability measure, x̄, δ : Ω → ℝ and B ∈ ℝ. Suppose:
   - (a) B ≥ 0;
   - (b) x̄ ∈ L²(μ);
   - (c) δ is μ-a.e.-strongly measurable;
   - (d) |δ(ω)| ≤ B for μ-a.e. ω.

   Then √Var(x̄·δ) ≤ √(∫ x̄² dμ) · B.
2. **Truth: true.** Var(x̄δ) ≤ E[(x̄δ)²] ≤ B²·E[x̄²]; take square roots. Checked on random finite spaces.
3. **Non-vacuity.** x̄ ≡ 1, δ ≡ 0, B = 0 is a witness. Equality holds for x̄ ≡ c and δ = ±B with a fair sign.
4. **Junk values.** None. x̄δ ∈ L² because |x̄δ| ≤ B·|x̄| a.e.
5. **Concerns (note).** Hypothesis (a) is redundant. If B < 0, the full-measure set {|δ| ≤ B} would be empty, which is impossible under a probability measure.

## 15. `variance_linearised_corr`

1. **Rendering.** Let μ be a probability measure, s ⊆ ι finite, x̄ᵢ, δᵢ : Ω → ℝ, and eᵢ ∈ ℤ, dᵢ ∈ ℕ. Hypotheses, for every i ∈ s:
   - (a) x̄ᵢ ∈ L²(μ);
   - (b) δᵢ is μ-a.e.-strongly measurable;
   - (c) |δᵢ| ≤ 2^(eᵢ−dᵢ−1) μ-a.e.

   There is **no independence assumption of any kind**. Conclusion:

   Var(Σ[i ∈ s] x̄ᵢ·δᵢ) ≤ vCorr(s, i ↦ ∫ x̄ᵢ² dμ, e, d) = (Σ[i ∈ s] √(∫ x̄ᵢ² dμ) · 2^(eᵢ−dᵢ−1))².
2. **Truth: true.** It follows from #13 and #14. Checked on 300 random finite spaces with arbitrary dependence.
3. **Non-vacuity.** x̄ᵢ ≡ 0 is a trivial witness. The bound is **attained**: take x̄ᵢ ≡ cᵢ ≥ 0 and δᵢ = 2^(eᵢ−dᵢ−1)·ε with one common fair sign ε. The exact check gives 441/64 = 441/64.
4. **Junk values.** None. ∫ x̄ᵢ² is genuine and ≥ 0.
5. **Concerns.** None. The hypotheses admit δᵢ := x̄ᵢ − roundFixed(eᵢ, dᵢ, x̄ᵢ): it satisfies (c) by #2 and is measurable when x̄ᵢ is. The statement itself does not mention `roundFixed`.

## 16. `vIndep_le_vCorr`

1. **Rendering.** Let ι be a type, s ⊆ ι finite, M : ι → ℝ with Mᵢ ≥ 0 for all i ∈ s, e : ι → ℤ and d : ι → ℕ. Then

   (1/12) · Σ[i ∈ s] Mᵢ·4^(eᵢ−dᵢ) ≤ (Σ[i ∈ s] √Mᵢ · 2^(eᵢ−dᵢ−1))².
2. **Truth: true.** The square of a sum of nonnegative terms is at least the sum of their squares. That sum is Σ Mᵢ·4^(eᵢ−dᵢ−1) = (1/4)·Σ Mᵢ·4^(eᵢ−dᵢ), which is ≥ (1/12)·Σ Mᵢ·4^(eᵢ−dᵢ). In 20,000 random cases the smallest ratio of right side to left side was 3, reached with a single nonzero term.
3. **Non-vacuity.** Mᵢ ≡ 0 is a witness, as is any nonnegative M.
4. **Junk values.** None under the hypothesis, since √ is applied only to nonnegative numbers.
5. **Concerns (note).** The hypothesis Mᵢ ≥ 0 is **redundant**. Negative Mᵢ only lower the left side and contribute 0 to the right side through the √ convention. Python found 0 violations with negative Mᵢ allowed. Whenever the left side is positive, the inequality has slack of a factor ≥ 3.

## 17. `variance_extended_indep`

1. **Rendering.** Let μ be a probability measure, ι and κ types, s ⊆ ι and t ⊆ κ finite, x̄ᵢ, δᵢ : Ω → ℝ (i ∈ ι), z̄ⱼ, δZⱼ : Ω → ℝ (j ∈ κ), eᵢ ∈ ℤ, dᵢ ∈ ℕ and mse ∈ ℝ. Hypotheses:
   - (a) x̄ᵢ ∈ L²(μ) for every i ∈ s;
   - (b) for every i ∈ s, the law of δᵢ is uniform on [−2^(eᵢ−dᵢ−1), 2^(eᵢ−dᵢ−1)];
   - (c) z̄ⱼ is μ-a.e.-strongly measurable for every j ∈ t;
   - (d) δZⱼ is μ-a.e.-strongly measurable for every j ∈ t;
   - (e) z̄ⱼ·δZⱼ ∈ L²(μ) for every j ∈ t;
   - (f) ∫ δZⱼ² dμ = mse for every j ∈ t. This is one common number and a Bochner integral.
   - (g) x̄ᵢ ⫫ δᵢ for every i ∈ s;
   - (h) z̄ⱼ ⫫ δZⱼ for every j ∈ t;
   - (i) for a ∈ s ⊔ t, let W_a := x̄ᵢ·δᵢ if a = inl i and W_a := z̄ⱼ·δZⱼ if a = inr j. Then W_a ⫫ W_b for all distinct a, b ∈ s ⊔ t. This covers x–x, z–z and x–z pairs.

   Conclusion:

   Var(Σ[i ∈ s] x̄ᵢ·δᵢ + Σ[j ∈ t] z̄ⱼ·δZⱼ) ≤ (1/12)·Σ[i ∈ s] (∫ x̄ᵢ² dμ)·4^(eᵢ−dᵢ) + (Σ[j ∈ t] ∫ z̄ⱼ² dμ) · mse.

   The first term on the right is vIndep(s, i ↦ ∫ x̄ᵢ², e, d).
2. **Truth: true.**
   - All W_a are in L² and pairwise independent, so Var = Σ_a Var(W_a).
   - x-terms: Var(x̄ᵢδᵢ) = E[x̄ᵢ²]·4^(eᵢ−dᵢ)/12 exactly, as in #12.
   - z-terms: Var(z̄ⱼδZⱼ) ≤ E[(z̄ⱼδZⱼ)²] = (∫ z̄ⱼ²)·(∫ δZⱼ²) = (∫ z̄ⱼ²)·mse, as in #11.
   - A Monte Carlo run gave Var 3.72 ≤ bound 4.13.
3. **Non-vacuity.** Witness: a product space with each x̄ᵢ, δᵢ, z̄ⱼ and δZⱼ on its own coordinate, with all δZⱼ sharing one law (e.g. ±√mse). Also s = t = ∅, giving 0 ≤ 0.
4. **Junk values.**
   - ∫ z̄ⱼ² and ∫ δZⱼ² are Bochner integrals and are 0 outside L². Hypothesis (f) does not itself assert δZⱼ ∈ L².
   - Under (c), (d), (e) and (h), a non-L² factor forces its partner to vanish a.e. The junk zeros then coincide with true zero contributions, so they never decide the inequality.
   - If t = ∅, mse is unconstrained but is multiplied by the empty sum 0.
5. **Concerns (note).**
   - The x-part carries the same caveat as #12: the hypotheses are unsatisfiable if some δᵢ is a measurable function of x̄ᵢ.
   - mse is a raw second moment E[δZⱼ²], not a variance, and it must be the same for all j ∈ t.
   - The x-part of the bound is attained with equality. The z-part drops (E[z̄ⱼ]·E[δZⱼ])².

## 18. `variance_extended_corr`

1. **Rendering.** μ is a probability measure, and ι, κ, s, t, x̄, δ, z̄, δZ, e, d and mse are as in #17. Hypotheses:
   - (a) x̄ᵢ ∈ L²(μ) for every i ∈ s;
   - (b) δᵢ is μ-a.e.-strongly measurable for every i ∈ s;
   - (c) |δᵢ| ≤ 2^(eᵢ−dᵢ−1) μ-a.e. for every i ∈ s;
   - (d) z̄ⱼ is μ-a.e.-strongly measurable for every j ∈ t;
   - (e) δZⱼ is μ-a.e.-strongly measurable for every j ∈ t;
   - (f) z̄ⱼ·δZⱼ ∈ L²(μ) for every j ∈ t;
   - (g) ∫ δZⱼ² dμ = mse for every j ∈ t;
   - (h) z̄ⱼ ⫫ δZⱼ for every j ∈ t.

   There is **no independence between different terms**. Conclusion:

   Var(Σ[i ∈ s] x̄ᵢ·δᵢ + Σ[j ∈ t] z̄ⱼ·δZⱼ) ≤ (Σ[i ∈ s] √(∫ x̄ᵢ² dμ)·2^(eᵢ−dᵢ−1) + Σ[j ∈ t] √((∫ z̄ⱼ² dμ)·mse))².
2. **Truth: true.**
   - Minkowski over all terms, as in #13.
   - sd(x̄ᵢδᵢ) ≤ √E[x̄ᵢ²]·2^(eᵢ−dᵢ−1), by #14.
   - sd(z̄ⱼδZⱼ) ≤ √E[(z̄ⱼδZⱼ)²] = √((∫ z̄ⱼ²)·mse), by independence as in #11.
   - A Monte Carlo run gave 3.72 ≤ 34.2.
3. **Non-vacuity.** Trivial witnesses exist. A nondegenerate one takes any bounded δᵢ, for instance the actual rounding errors x̄ᵢ − roundFixed(eᵢ, dᵢ, x̄ᵢ), plus independent z-pairs.
4. **Junk values.** As in #17, the junk zeros coincide with true zero contributions. When t ≠ ∅, mse = ∫ δZⱼ² ≥ 0, so √ is never applied to a negative number.
5. **Concerns.** None. The x-part is the vCorr expression written out in full. The z-part needs only within-pair independence (h).

---

## Summary

| Declaration | Verdict | One-line reason |
|---|---|---|
| `roundFixed` (def) | OK (note) | h·⌊x/h + 1/2⌋ with h = 2^(e−d); ties go toward +∞; fixed grid with no range or overflow modelling |
| `abs_sub_roundFixed_le` | OK | \|x − roundFixed\| ≤ h/2, sharp at ties |
| `roundFixed_mantissa` | OK | \|round(x/h)\| ≤ 2^d − 1 under a strict, sharp magnitude bound; witness x = 0 |
| `integral_sq_roundError_le` | OK (note) | pointwise bound integrated, sharp; for non-measurable X only the junk value 0 is compared |
| `integral_sq_of_isUniform` | OK | uniform law forces μ(Ω) = 1 and measurability; a > 0 is necessary |
| `integral_sq_uniform_roundError` | OK | second moment h²/12 of U[−h/2, h/2]; δ is not linked to roundFixed |
| `vIndep` (def) | OK | (1/12)·Σ Mᵢ·4^(eᵢ−dᵢ), with a real 1/12 |
| `vCorr` (def) | OK (note) | (Σ √Mᵢ·2^(eᵢ−dᵢ−1))²; √ silently maps negative Mᵢ to 0 |
| `variance_sum_eq` | OK | standard bilinearity identity under L² |
| `variance_le_integral_sq` | OK (note) | Var ≤ E[Y²]; if x̄δ ∉ L² both sides are 0 by convention |
| `variance_sum_mul_le_of_indep` | OK | pairwise independence plus E[Y²] = E[sens²]E[err²]; junk zeros never decide it |
| `variance_linearised_indep` | OK (note) | true, in fact an equality; unsatisfiable if δᵢ is a measurable function of x̄ᵢ |
| `variance_sum_le_sq_sum_sqrt` | OK | Minkowski for standard deviations |
| `sqrt_variance_mul_le` | OK (note) | true and sharp; hB is redundant |
| `variance_linearised_corr` | OK | worst-case bound with no independence; attained |
| `vIndep_le_vCorr` | OK (note) | true with slack factor ≥ 3; hM is redundant |
| `variance_extended_indep` | OK (note) | true; same exogenous-noise caveat as `variance_linearised_indep`; common raw second moment mse |
| `variance_extended_corr` | OK | Minkowski plus per-term bounds; only within-pair independence |

**Overall.**

No declaration is false and none is vacuous: every theorem has an explicit witness, and in several cases the bound is attained. None depends on a junk value for its meaningful content. Junk conventions enter only in corner cases, and there they agree with the true value:
- non-measurable X in `integral_sq_roundError_le`;
- a non-L² product in `variance_le_integral_sq`;
- non-L² factors with an a.e.-zero partner in the independence lemmas.

The points a reviewer should weigh are these:

1. **Rounding model.** `roundFixed` is rounding on a fixed grid with spacing 2^(e−d) and ties broken toward +∞. The exponent is not chosen from x, and there is no overflow or saturation. The mantissa bound holds only under the separate magnitude hypothesis of `roundFixed_mantissa`.
2. **Uniform-noise theorems.** In `variance_linearised_indep` and `variance_extended_indep`, the noise δᵢ is an abstract random variable, uniform and independent of x̄ᵢ. These hypotheses are jointly **unsatisfiable when δᵢ is any measurable function of x̄ᵢ**, including the deterministic rounding error x̄ᵢ − roundFixed(eᵢ, dᵢ, x̄ᵢ). They can be satisfied by exogenous noise, for example rounding a dithered input.
3. **Links to `roundFixed`.** None of the variance theorems mentions `roundFixed`. The only link is the numeric half-width 2^(e−d−1). The worst-case ("corr") theorems can be instantiated with actual rounding errors.
4. **Redundant hypotheses and slack.**
   - hB in `sqrt_variance_mul_le` and hM in `vIndep_le_vCorr` are redundant.
   - The ≤ in `variance_linearised_indep` is actually an equality.
   - vIndep ≤ vCorr always holds with slack of a factor ≥ 3.
5. **Measures not declared probability.** In `integral_sq_of_isUniform` and `integral_sq_uniform_roundError`, μ is not declared a probability measure, but the uniform-law hypothesis forces μ(Ω) = 1.
