# Blind read-back audit: packet A (`hg_path_bitwidth`)

- **Date:** 2026-09-27
- **Packet:** `packet_A_hg_path_bitwidth.lean`
- **Declarations audited:** 50. That is 8 definitions and 42 theorems:
  - 14 in module `FixedPointPath` (2 definitions, 12 theorems);
  - 14 in `BitWidth` (4 definitions, 10 theorems);
  - 20 in `LagrangeBitWidth` (20 theorems);
  - 2 supporting definitions from "other modules" (`roundFixed`, `vIndep`).
- **Auditor:** an independent session, working blind.
- **Rules followed:**
  - I read only three things: the packet, the auditor rules (`mission_auditor.md`), and the Mathlib and Lean-core sources, and those sources only to confirm conventions.
  - I did not open the project sources, docs, notes, README, PLAN, scripts, git history, any paper, or the web.
  - I inferred no meaning from declaration or file names.
  - Each rendering translates the code literally. It lists every binder, hypothesis and typeclass assumption, expands project definitions inline, and keeps the exact strength of every relation.
  - Truth claims were sanity-checked numerically with pure-Python scripts (exact rationals where possible) in `work_A_hg_path_bitwidth/`:
    - `check_path.py`
    - `check_bitwidth.py`
    - `check_lagrange.py`
    - `check_variance.py`
  - Every check passed. Each entry quotes the relevant output.

---

## Summary table

| # | Declaration | Kind | Truth | Hypotheses satisfiable | Junk dependence | Flag |
|---|---|---|---|---|---|---|
| 1 | `gbmStep` | def | — | — | $\sqrt h=0$ for $h<0$ | minor |
| 2 | `gbmStep_eq` | thm | true | yes (none) | none | — |
| 3 | `gbmPath` | def | — | — | inherits 1 | — |
| 4 | `gbmPath_succ` | thm | true | yes | none | — |
| 5 | `gbmPath_eq_prod` | thm | true | yes | none | — |
| 6 | `abs_con1_con2` | thm | true | yes | none | — |
| 7 | `integral_sq_mul1_le` | thm | true | yes | hypothesis can hold via $\int=0$ junk | minor |
| 8 | `integral_sq_sum1_le` | thm | true | yes | none | — |
| 9 | `integral_sq_gbmPath_le` | thm | true | yes | none | — |
| 10 | `integral_sq_mul2_le` | thm | true | yes | none | — |
| 11 | `perturbed_sub_eq` | thm | true | yes | none | — |
| 12 | `abs_perturbed_sub_le` | thm | true | yes | none | — |
| 13 | `integral_abs_perturbed_sub_le` | thm | true | yes | LHS is junk $0$ if the integrand is not integrable (possible: no measurability on $\rho$) | **concern** |
| 14 | `integral_abs_roundFixed_path_sub_le` | thm | true | yes | none (integrand genuinely integrable) | minor |
| 15 | `opCost` | def | — | — | none | — |
| 16 | `opCount` | def | — | — | none | — |
| 17 | `sepCost` | def | — | — | none | — |
| 18 | `opCost_le_sepCost` | thm | true | yes | none | — |
| 19 | `levelwise_optimisation` | thm | true | yes | none | — |
| 20 | `vIndepR` | def | — | — | none | — |
| 21 | `vIndepR_natCast` | thm | true | yes | none | — |
| 22 | `hasDerivAt_vIndepR_update` | thm | true | yes | none | — |
| 23 | `hasDerivAt_sepCost_update` | thm | true | yes | none | — |
| 24 | `exists_unique_bitWidth` | thm | true | yes | none | — |
| 25 | `hasDerivAt_levelCost` | thm | true | yes | none | — |
| 26 | `levelCost_stationary_iff` | thm | true | yes | $V$ unconstrained; $V\le0$ handled by $\sqrt{\text{neg}}=0$ on both sides | minor |
| 27 | `vIndepR_antitone` | thm | true | yes | none | — |
| 28 | `greedy_rounding_feasible` | thm | true | yes | none | **concern** (trivial witness $k=n$) |
| 29 | `levelCost34_le_levelCost33` | thm | true | yes | $\sqrt{\text{neg}}=0$ possible | — |
| 30 | `levelCost33_le_sqrt_mul` | thm | true | yes | $\sqrt{\text{neg}}=0$ possible | — |
| 31 | `levelCost33_le_add_mul` | thm | true | yes | $\sqrt{\text{neg}}=0$ possible | — |
| 32 | `totalCost32_bounds` | thm | true | yes | $\varepsilon=0\Rightarrow(\varepsilon^2)^{-1}=0$ | minor |
| 33 | `lagrangian_le_of_eq35` | thm | true | yes | none | — |
| 34 | `vIndepR_le_of_eq35` | thm | true | yes | none | — |
| 35 | `sepCost_le_of_eq35` | thm | true | yes | none | — |
| 36 | `exists_eq35_isMin` | thm | true | yes | none | — |
| 37 | `eq35_of_isLocalMinOn` | thm | true | yes | none | — |
| 38 | `marginalRatio_eq_of_isLocalMinOn` | thm | true | yes | none (division guarded) | — |
| 39 | `eq37_iff` | thm | true | yes | none (division guarded) | — |
| 40 | `lambda37_pos` | thm | true | yes | none | — |
| 41 | `eq37_of_eq35` | thm | true | yes | none | — |
| 42 | `rpow_four_sub_add_one` | thm | true | yes | none | — |
| 43 | `vIndepR_sub_update_add_one` | thm | true | yes | none | — |
| 44 | `sepCost_update_add_one_sub` | thm | true | yes | none | — |
| 45 | `errorBound_succ` | thm | true | yes | none | — |
| 46 | `errorBound_eq_div_pow` | thm | true | yes | none | — |
| 47 | `errorShare_succ` | thm | true | yes | zero denominators: $x/0=0$ on both sides | minor |
| 48 | `variance_extended_le_two_mul` | thm | true | yes | hypotheses may hold via junk $\int=0$, conclusion unaffected | minor |
| 49 | `roundFixed` | def | — | — | none (divisor $2^{e-d}>0$) | minor (only $e-d$ matters, no range limit) |
| 50 | `vIndep` | def | — | — | none ($\mathbb Z$-subtraction, no truncation) | — |

In summary:

- No statement is false.
- No statement has contradictory (vacuous) hypotheses.
- Two statements are flagged as concerning: #13 and #28.
- Several entries have minor junk or degenerate-case remarks.

---

## Conventions (confirmed in the sources)

Paths are relative to `.lake/packages/mathlib/Mathlib/` unless marked "core". Core means `/root/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`.

1. **Operator precedence (core `Init/Notation.lean` l. 284–295, 305–311).**
   - `+` and binary `-` are `infixl:65`.
   - `*` and `/` are `infixl:70`.
   - `^` is `infixr:80`.
   - Unary `-` is `prefix:75`. Hence $-(2{:}\mathbb R)^{k}$ parses as $-(2^{k})$, not $(-2)^k$.
   - `⁻¹` is `postfix:max`. Hence `ε⁻¹ ^ 2` is $(\varepsilon^{-1})^2$.
   - `x ^ y` elaborates via `rightact%`, so the exponent's type comes from the exponent term itself. In `(4:ℝ) ^ (e i - d i)` with `e i : ℤ` and `d i : ℕ`, the exponent is computed in $\mathbb Z$: $d_i$ is cast into $\mathbb Z$, so there is no truncated $\mathbb N$ subtraction, and the power is the integer power (zpow). The same holds for `(2:ℝ) ^ (e - d)` and `(2:ℝ) ^ (e - d - 1)`.
   - `(4:ℝ) ^ ((e i : ℝ) - t)` is the real power (rpow).
2. **Big operators (`Algebra/BigOperators/Group/Finset/Defs.lean` l. 181, 196).** In `∑ x ∈ s, body` and `∏ x ∈ s, body`, the body is parsed at precedence 67.
   - `+`, binary `-`, `=` and `≤` end the body.
   - `*`, `/` and `^` stay inside it.
   - Example: `∑ i ∈ s, -(a i) + lam * ∑ i ∈ s, (b i) = 0` means $\big(\sum_{i\in s}-a_i\big)+\lambda\sum_{i\in s}b_i=0$.
3. **Division and inverse by zero.** `div_zero : a / 0 = 0` (`Algebra/GroupWithZero/Basic.lean` l. 407) and `inv_zero : 0⁻¹ = 0` (`Algebra/GroupWithZero/Defs.lean` l. 236).
4. **Real square root (`Analysis/Real/Sqrt.lean`).**
   - Definition (l. 112): `Real.sqrt x = NNReal.sqrt (Real.toNNReal x)`, so $\sqrt x=0$ for $x\le 0$ (`sqrt_eq_zero_of_nonpos`, l. 142).
   - $\sqrt{\cdot}$ is monotone on all of $\mathbb R$ (`sqrt_le_sqrt`, l. 209).
   - $\sqrt{xy}=\sqrt x\sqrt y$ when $x\ge0$ (`sqrt_mul`, l. 366).
5. **Real power (`Analysis/SpecialFunctions/Pow/Real.lean`).**
   - Definition (l. 35): `rpow x y = ((x:ℂ)^(y:ℂ)).re`.
   - For $x>0$, $x^y=\exp(\log x\cdot y)$ (`rpow_def_of_pos`, l. 51). All real powers in this packet have base $4>0$, so no rpow junk (negative base, $0^0$) arises.
   - `rpow_intCast` (l. 57): $x^{(n:\mathbb R)}=x^n$ for $n\in\mathbb Z$.
   - `rpow_sub` (l. 262): for $x>0$, $x^{y-z}=x^y/x^z$.
6. **Bochner integral (`MeasureTheory/Integral/Bochner/Basic.lean`).**
   - `integral_undef` (l. 202): if $f$ is not integrable, $\int f\,d\mu=0$.
   - `integral_const_mul` (l. 288): $\int c f=c\int f$, with **no** integrability hypothesis.
   - `integral_mono_of_nonneg` (l. 639): needs only the upper function to be integrable.
7. **Variance (`Probability/Moments/Variance.lean`).**
   - Definitions (l. 58, 64): $\operatorname{evariance}(X)=\int^{-}\lVert X-\mathbb E_\mu X\rVert_e^2\,d\mu\in[0,\infty]$ and $\operatorname{variance}=(\operatorname{evariance}).\mathrm{toReal}$. So an $\infty$ evariance becomes $0$.
   - `variance_of_not_memLp` (l. 132): an AE-strongly-measurable non-$L^2$ $X$ has variance $0$.
   - `IndepFun.variance_sum` (l. 422): pairwise independence plus $L^2$ gives additivity of variance.
8. **Uniform law (`Probability/Distributions/Uniform.lean` l. 64).**
   - `pdf.IsUniform X s ℙ μ := map X ℙ = cond μ s`, where the reference measure $\mu$ defaults to `volume`.
   - `ProbabilityTheory.cond μ s = (μ s)⁻¹ • μ.restrict s` (`Probability/ConditionalProbability.lean` l. 76).
   - `Measure.map f μ = 0` when $f$ is not AE-measurable (`MeasureTheory/Measure/Map.lean` l. 91–93, `map_of_not_aemeasurable` l. 112).
   - For an interval of positive finite length, `cond` is a probability measure. So `IsUniform` forces $X$ to be AE-measurable with the uniform law, and no junk arises.
9. **Rounding (`Algebra/Order/Round.lean`).**
   - `round x = if 2 * fract x < 1 then ⌊x⌋ else ⌈x⌉` (l. 48). This is the nearest integer, with ties broken toward $+\infty$.
   - `abs_sub_round` (l. 193): $|x-\operatorname{round}x|\le 1/2$.
   - `round_eq`: $\operatorname{round}x=\lfloor x+1/2\rfloor$. Floor is measurable (`MeasureTheory/Function/Floor.lean`), so round is measurable.
10. **Independence (`Probability/Independence/Basic.lean` l. 136, 144).**
    - `iIndepFun f μ` (mutual independence of the family) and `IndepFun f g μ` mean independence of the generated σ-algebras. They are defined via `Kernel.const Unit μ` and `dirac ()`.
    - Measurability is not built into these definitions.
11. **Local minimum on a set.** `IsLocalMinOn f s a := IsMinFilter f (𝓝[s] a) a`, i.e. $\forall^{\!f} x\in\mathcal N_{s}(a),\ f(a)\le f(x)$ (`Topology/Order/LocalExtr.lean` l. 49, `Order/Filter/Extr.lean` l. 98).
12. **$L^p$ membership.** `MemLp f p μ := AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞` (`MeasureTheory/Function/LpSeminorm/Defs.lean` l. 118).
13. **Order and combinatorics conventions.**
    - `Antitone f := ∀ a b, a ≤ b → f b ≤ f a` (`Order/Monotone/Defs.lean` l. 68).
    - On function types the order is pointwise (`Order/Defs/Prop.lean` l. 18).
    - `Set.Pairwise s r` requires $r(x,y)$ only for **distinct** $x,y\in s$ (`Logic/Pairwise.lean` l. 83).
    - `Finset.Ico a b = ∅` when $b\le a$ (`Order/Interval/Finset/Basic.lean` l. 118).
    - Empty sums are $0$ and empty products are $1$.
    - `Finset.disjSum` is the disjoint union in $\iota\oplus\kappa$ (`Data/Finset/Sum.lean` l. 34).
14. **Lagrange multipliers (used in truth arguments, not a convention).** `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d` (`Analysis/Calculus/LagrangeMultipliers.lean` l. 87) says: at a local extremum of $\varphi$ on $\{f=f(x_0)\}$, there are $(a,b)\ne0$ with $a f'+b\varphi'=0$.

### Notation used below

- $\sqrt{x}$ is Mathlib's real square root ($=0$ for $x\le0$).
- $4^{y}$ with real $y$ is $e^{y\ln 4}$. $2^{k}$ and $4^{k}$ with $k\in\mathbb Z$ are integer powers.
- $\operatorname{rnd}(x)$ is Mathlib's `round`.
- $\mathbb E_\mu[f]:=\int f\,d\mu$ is the Bochner integral (it is $0$ if $f$ is not integrable).
- $d[i\mapsto t]$ is $d$ with coordinate $i$ replaced by $t$.
- $[P]\in\{0,1\}$ is the indicator of a proposition.
- $\{a,\dots,b\}$ is empty when $a>b$.

---

## Module `FixedPointPath`

### 1. `gbmStep` (definition)

**Rendering.** For real numbers $r,\sigma,h,S,Z$:
$$\mathrm{gbmStep}(r,\sigma,h,S,Z)=S+S\cdot\big(rh+(\sqrt h\,\sigma)\,Z\big).$$
This is written with the intermediate names:
- $\mathrm{con1}=rh$;
- $\mathrm{con2}=\sqrt h\,\sigma$;
- $\mathrm{mul1}=\mathrm{con2}\cdot Z$;
- $\mathrm{sum1}=\mathrm{con1}+\mathrm{mul1}$;
- $\mathrm{mul2}=S\cdot\mathrm{sum1}$;
- result $S+\mathrm{mul2}$.

**Truth.** Definition. It is total, with no side conditions.

**Non-vacuity.** Not applicable.

**Junk values.** For $h<0$, $\sqrt h=0$, so the $Z$-term vanishes while $rh$ is kept. The theorems below that carry probabilistic content assume $h\ge0$ (or $h>0$). The purely algebraic ones hold for all $h$.

**Concerns.** None beyond the $h<0$ convention.

### 2. `gbmStep_eq`

**Rendering.** For all real $r,\sigma,h,S,Z$ (no hypotheses):
$$\mathrm{gbmStep}(r,\sigma,h,S,Z)=S+rSh+\sigma S\sqrt h\,Z.$$

**Truth.** True. This is a ring identity, with $\sqrt h$ treated as an arbitrary real. Checked on 20 000 random tuples, including $h<0$.

**Non-vacuity.** There are no hypotheses.

**Junk values.** None. For $h<0$ both sides use $\sqrt h=0$ consistently.

**Concerns.** None.

### 3. `gbmPath` (definition)

**Rendering.** Take reals $r,\sigma,h,s_0$ and a real sequence $Z=(Z_i)_{i\in\mathbb N}$. Then $\mathrm{gbmPath}(r,\sigma,h,s_0,Z):\mathbb N\to\mathbb R$, written $P_n$, is defined recursively by
$$P_0=s_0,\qquad P_{i+1}=\mathrm{gbmStep}(r,\sigma,h,P_i,Z_i)=P_i+P_i\big(rh+\sqrt h\,\sigma Z_i\big).$$
So $P_n$ depends only on $Z_0,\dots,Z_{n-1}$.

**Truth.** Definition.

**Non-vacuity.** Not applicable.

**Junk values.** Inherits the $h<0$ remark of #1.

**Concerns.** None.

### 4. `gbmPath_succ`

**Rendering.** For all $r,\sigma,h,s_0\in\mathbb R$, every sequence $Z:\mathbb N\to\mathbb R$ and every $i\in\mathbb N$, with $P$ as in #3:
$$P_{i+1}=P_i\cdot\big(1+rh+\sqrt h\,\sigma Z_i\big).$$

**Truth.** True, by unfolding one step and factoring. Checked numerically.

**Non-vacuity.** There are no hypotheses.

**Junk values.** None.

**Concerns.** None.

### 5. `gbmPath_eq_prod`

**Rendering.** For all $r,\sigma,h,s_0\in\mathbb R$, $Z:\mathbb N\to\mathbb R$ and $n\in\mathbb N$:
$$P_n=s_0\prod_{i=0}^{n-1}\big(1+rh+\sqrt h\,\sigma Z_i\big).$$
For $n=0$ the product is empty and equals $1$.

**Truth.** True, by induction using #4. Checked numerically.

**Non-vacuity.** There are no hypotheses.

**Junk values.** None.

**Concerns.** None.

### 6. `abs_con1_con2`

**Rendering.** For real $r,\sigma,h$ with $0\le h$, both of the following hold:
$$|rh|=|r|\,h \qquad\text{and}\qquad |\sqrt h\,\sigma|=|\sigma|\sqrt h.$$

**Truth.** True.
- The first conjunct uses $h\ge0$. Without it the conjunct fails: $h=-1$, $r=1$ gives $1\ne-1$.
- The second conjunct holds for every $h$, since $\sqrt h\ge0$.

**Non-vacuity.** Take $h=0$.

**Junk values.** None.

**Concerns.** None.

### 7. `integral_sq_mul1_le`

**Rendering.** The binders are:
- a measurable space $\Omega$;
- an arbitrary measure $\mu$ on $\Omega$. The section's probability-measure assumption is explicitly omitted, so $\mu$ need not even be finite;
- an arbitrary function $Y:\Omega\to\mathbb R$, with no measurability or integrability assumed;
- reals $\sigma,h$.

The hypotheses are $\int Y^2\,d\mu\le 1$ and $0\le h$. The claim is:
$$\int_\Omega\big(\sqrt h\,\sigma\,Y(\omega)\big)^2\,d\mu(\omega)\ \le\ \sigma^2 h.$$

**Truth.** True.
- The integrand equals $h\sigma^2Y^2$ pointwise.
- Mathlib's $\int c f=c\int f$ holds unconditionally, so the left side is $h\sigma^2\int Y^2\le h\sigma^2$.

**Non-vacuity.** Take $Y\equiv0$ and any $\mu$.

**Junk values.** If $Y^2$ is not $\mu$-integrable, then $\int Y^2=0$ by convention, so the hypothesis holds automatically. In that case the left side is also $h\sigma^2\cdot 0=0$ by convention, and the statement reads $0\le\sigma^2h$. The claim is still correct, but in that case it says nothing about $Y$.

**Concerns.** Minor. The hypothesis does not force $Y\in L^2$, and $\mu$ is an arbitrary measure.

### 8. `integral_sq_sum1_le`

**Rendering.** The binders are:
- a measurable space $\Omega$ with a **probability** measure $\mu$;
- $Y:\Omega\to\mathbb R$ with $Y\in L^2(\mu)$, $\int Y\,d\mu=0$ and $\int Y^2\,d\mu\le1$;
- reals $r,\sigma,h$ with $0\le h\le 1$.

The claim is:
$$\int_\Omega\big(rh+\sqrt h\,\sigma\,Y\big)^2\,d\mu\ \le\ (r^2+\sigma^2)\,h.$$

**Truth.** True.
- Expanding gives $r^2h^2+2rh\sqrt h\sigma\cdot0+h\sigma^2\int Y^2\le r^2h^2+\sigma^2h$.
- Then $h^2\le h$ gives $\le(r^2+\sigma^2)h$.
- The hypothesis $h\le1$ is needed: $r=1$, $\sigma=0$, $h=4$ gives $16>4$.
- No violations in exact enumeration over four mean-zero discrete laws. Equality is reached for $r=0$, $\mathbb E Y^2=1$.

**Non-vacuity.** Take $Y$ Rademacher on $[0,1]$ with Lebesgue measure.

**Junk values.** None: $Y\in L^2$ makes every integral genuine.

**Concerns.** None.

### 9. `integral_sq_gbmPath_le`

**Rendering.** The binders are:
- a measurable space $\Omega$ with a **probability** measure $\mu$;
- a family $Z=(Z_i)_{i\in\mathbb N}$ of functions $\Omega\to\mathbb R$ satisfying:
  - the $Z_i$ are mutually independent under $\mu$;
  - each $Z_i$ is measurable;
  - each $Z_i\in L^2(\mu)$;
  - $\int Z_i\,d\mu=0$;
  - $\int Z_i^2\,d\mu\le1$;
- reals $r,\sigma,h$ with $0\le h\le1$;
- $s_0\in\mathbb R$ and $n\in\mathbb N$.

Let $P_n(\omega)=s_0\prod_{i<n}(1+rh+\sqrt h\,\sigma Z_i(\omega))$ be the path of #3 driven by $(Z_i(\omega))_i$. The claim is:
$$\int_\Omega P_n(\omega)^2\,d\mu(\omega)\ \le\ s_0^2\exp\!\big((2|r|+r^2+\sigma^2)\,n\,h\big).$$

**Truth.** True.
- By independence, $\mathbb E\prod_i m_i^2=\prod_i\mathbb E m_i^2$ with $m_i=1+rh+\sqrt h\sigma Z_i$.
- $\mathbb E m_i^2=(1+rh)^2+h\sigma^2\mathbb EZ_i^2\le1+(2|r|+r^2+\sigma^2)h\le e^{(2|r|+r^2+\sigma^2)h}$.
- Exact enumeration (400 random configurations): no violation. Equality holds at $n=0$ or $h=0$.

**Non-vacuity.** Take $\Omega=[0,1]$ with Lebesgue measure and $Z_i$ the Rademacher functions. The degenerate choice $Z\equiv0$ also works.

**Junk values.** None. The integrand is integrable (a product of independent $L^2$ factors squared).

**Concerns.** None. As a side remark, $h\le1$ is not needed for this particular bound, because $(1+rh)^2+h\sigma^2\le e^{(2|r|+\sigma^2)h}$ for all $h\ge0$. The separate measurability hypothesis also looks mathematically unnecessary, since $L^2$ already gives AE-strong measurability. Both are harmless.

### 10. `integral_sq_mul2_le`

**Rendering.** The setting is the same as #9:
- probability measure $\mu$;
- $(Z_i)$ mutually independent, measurable, in $L^2$, mean $0$, $\int Z_i^2\le1$;
- $0\le h\le1$;
- $s_0\in\mathbb R$.

Now take an index $i\in\mathbb N$. The claim is:
$$\int_\Omega\Big(P_i(\omega)\cdot\big(rh+\sqrt h\,\sigma Z_i(\omega)\big)\Big)^2 d\mu\ \le\ s_0^2\Big(\exp\!\big((2|r|+r^2+\sigma^2)\,i\,h\big)\cdot\big((r^2+\sigma^2)h\big)\Big).$$

**Truth.** True.
- $P_i$ is a function of $Z_0,\dots,Z_{i-1}$, which is independent of $Z_i$, so the expectation factors.
- The two factors are bounded by #9 and #8.
- Exact enumeration: no violation.

**Non-vacuity.** As in #9.

**Junk values.** None.

**Concerns.** None.

### 11. `perturbed_sub_eq`

**Rendering.** Take real sequences $m,\rho,S,\tilde S:\mathbb N\to\mathbb R$ with, for every $k\in\mathbb N$:
- $S_{k+1}=S_km_k$;
- $\tilde S_{k+1}=\tilde S_km_k+\rho_k$;

and with $\tilde S_0=S_0$. For every $n\in\mathbb N$:
$$\tilde S_n-S_n=\sum_{k=0}^{n-1}\rho_k\prod_{j=k+1}^{n-1}m_j.$$
Here the inner product runs over $\mathrm{Ico}(k+1,n)=\{k+1,\dots,n-1\}$ and is $1$ when $k=n-1$.

**Truth.** True. The difference $D_k=\tilde S_k-S_k$ satisfies $D_0=0$ and $D_{k+1}=D_km_k+\rho_k$. Checked on 5 000 random instances.

**Non-vacuity.** Define $S$ and $\tilde S$ by the recursions.

**Junk values.** None.

**Concerns.** None.

### 12. `abs_perturbed_sub_le`

**Rendering.** The hypotheses of #11 hold, and in addition there is $u\in\mathbb R$ with $|\rho_k|\le u$ for **every** $k\in\mathbb N$. Then for every $n$:
$$|\tilde S_n-S_n|\ \le\ u\sum_{k=0}^{n-1}\Big|\prod_{j=k+1}^{n-1}m_j\Big|.$$

**Truth.** True, by #11 and the triangle inequality. The hypothesis on $\rho$ implies $u\ge0$. Checked numerically.

**Non-vacuity.** Take $\rho\equiv0$ and $u=0$.

**Junk values.** None.

**Concerns.** None. The bound on $\rho$ is required for all $k$, although only $k<n$ matter.

### 13. `integral_abs_perturbed_sub_le`

**Rendering.** The binders are:
- a probability measure $\mu$ on $\Omega$;
- $(Z_i)_{i\in\mathbb N}$ mutually independent, each measurable, in $L^2(\mu)$, with $\int Z_i=0$ and $\int Z_i^2\le1$;
- reals $r,\sigma,h,u$ with $0\le h\le1$ and $0\le u$;
- $s_0\in\mathbb R$;
- **arbitrary** functions $\tilde S,\rho:\mathbb N\to(\Omega\to\mathbb R)$. No measurability is assumed, and nothing says $\rho_k$ depends only on $Z_0,\dots,Z_k$.

These satisfy, for all $\omega$ and $k$:
- $\tilde S_0(\omega)=s_0$;
- $\tilde S_{k+1}(\omega)=\tilde S_k(\omega)\,(1+rh+\sqrt h\,\sigma Z_k(\omega))+\rho_k(\omega)$;
- $|\rho_k(\omega)|\le u$.

Let $n\in\mathbb N$, and let $P_n$ be the path of #3 driven by $(Z_i(\omega))$ from $s_0$. The claim is:
$$\int_\Omega\big|\tilde S_n(\omega)-P_n(\omega)\big|\,d\mu\ \le\ u\,n\,\exp\!\big((2|r|+r^2+\sigma^2)\,n\,h\big).$$

**Truth.** True.
- Pointwise, #12 gives $|\tilde S_n-P_n|\le u\sum_{k<n}|\prod_{j=k+1}^{n-1}m_j|$.
- The right-hand side is integrable, with $\mathbb E|\prod m_j|\le(\prod\mathbb E m_j^2)^{1/2}\le e^{ch(n-k-1)/2}\le e^{cnh}$, where $c=2|r|+r^2+\sigma^2$.
- `integral_mono_of_nonneg` needs only the upper function to be integrable, so the bound also holds when the left integrand is not integrable (then the left side is $0$).
- Exact enumeration with the worst-case choice $\rho_k=u\,\mathrm{sign}(\prod_{j>k}m_j)$ (allowed, since $\rho$ may depend on all of $\omega$): no violation. The ratio reaches $1$ at $r=\sigma=0$, where $\rho\equiv u$ gives $|\tilde S_n-P_n|=nu$, so the bound is attained.

**Non-vacuity.** Take $\rho\equiv0$ (then $\tilde S=P$), with $Z$ as in #9.

**Junk values.** Yes, in a degenerate case. Because nothing forces $\rho$ (hence $\tilde S_n$) to be measurable, $|\tilde S_n-P_n|$ may fail to be integrable. Then the Bochner integral is $0$ and the inequality holds trivially. For measurable $\rho$ the integral is genuine.

**Concerns.**
- The conclusion does not assert integrability of the error, and for non-measurable perturbations it carries no information.
- The perturbations may be non-adapted, i.e. may depend on future $Z$'s. This makes the statement stronger, not weaker.
- The hypothesis $0\le u$ is redundant, since it is implied by the bound on $\rho$.

### 14. `integral_abs_roundFixed_path_sub_le`

**Rendering.** The binders are:
- a probability measure $\mu$;
- $(Z_i)$ mutually independent, measurable, in $L^2$, with mean $0$ and $\int Z_i^2\le1$;
- reals $r,\sigma,h,T$ with $0<h\le1$;
- $s_0\in\mathbb R$, $e\in\mathbb Z$, $d\in\mathbb N$;
- $\tilde S:\mathbb N\to(\Omega\to\mathbb R)$.

$\tilde S$ satisfies, for all $\omega$ and $k$:
- $\tilde S_0(\omega)=s_0$, which is **not** rounded;
- $\tilde S_{k+1}(\omega)=\mathrm{roundFixed}_{e,d}\Big(\tilde S_k(\omega)+\tilde S_k(\omega)\big(rh+\sqrt h\,\sigma Z_k(\omega)\big)\Big)$.

Here $\mathrm{roundFixed}_{e,d}(x)=2^{e-d}\operatorname{rnd}(x/2^{e-d})$ rounds to the nearest integer multiple of $2^{e-d}$, with ties upward and no clipping. Let $n\in\mathbb N$ with $n\,h=T$. The claim is:
$$\int_\Omega|\tilde S_n-P_n|\,d\mu\ \le\ \frac{T}{h}\cdot2^{\,e-d-1}\cdot\exp\!\big((2|r|+r^2+\sigma^2)\,T\big).$$
The exponent $e-d-1$ is computed in $\mathbb Z$.

**Truth.** True.
- Set $\rho_k=\mathrm{roundFixed}(y_k)-y_k$. Then $|\rho_k|\le2^{e-d}\cdot\tfrac12=2^{e-d-1}$ by `abs_sub_round`.
- Apply #13 with $u=2^{e-d-1}$, and use $T/h=n$ (since $h>0$) and $nh=T$.
- Exact enumeration (300 configurations): no violation; worst ratio 0.65. The half-ulp bound was checked on 20 000 samples.

**Non-vacuity.** Define $\tilde S$ by the recursion; for example $n=0$, $T=0$, $h=1/2$.

**Junk values.** None.
- $T/h$ is genuine because $h>0$.
- $\tilde S_n$ is a Borel function of $Z_0,\dots,Z_{n-1}$ (round is measurable), and it is dominated by an integrable function, so the integral is genuine.

**Concerns.** Minor.
- $T$ is not a free parameter: $T/h$ is exactly $n$.
- $e$ and $d$ enter only through $e-d$, and the rounding has unbounded range.
- The initial value $s_0$ is not rounded.

---

## Module `BitWidth`

### 15. `opCost` (definition)

**Rendering.** The inputs are:
- types $\iota,\kappa,\kappa'$;
- a finite set $\mathrm{mul}\subseteq\kappa$ with maps $a,b:\kappa\to\iota$;
- a finite set $\mathrm{add}\subseteq\kappa'$ with maps $a',b':\kappa'\to\iota$;
- $d:\iota\to\mathbb R$.

Then
$$\mathrm{opCost}=\sum_{k\in\mathrm{mul}}d(a_k)\,d(b_k)+\sum_{k\in\mathrm{add}}\max\big(d(a'_k),d(b'_k)\big).$$

**Truth / Non-vacuity.** Definition; not applicable.

**Junk values.** None.

**Concerns.** None.

### 16. `opCount` (definition)

**Rendering.** With decidable equality on $\iota$, a finite set $\mathrm{ops}\subseteq\kappa$, maps $a,b:\kappa\to\iota$ and $i\in\iota$:
$$\mathrm{opCount}(\mathrm{ops},a,b,i)=\#\{k\in\mathrm{ops}:a_k=i\}+\#\{k\in\mathrm{ops}:b_k=i\}\in\mathbb N.$$
An index $k$ with $a_k=b_k=i$ is counted twice.

**Truth / Non-vacuity.** Definition.

**Junk values.** None.

**Concerns.** None.

### 17. `sepCost` (definition)

**Rendering.** For a finite set $\mathrm{vars}\subseteq\iota$ and $M,M',d:\iota\to\mathbb R$:
$$\mathrm{sepCost}(\mathrm{vars},M,M',d)=\tfrac12\sum_{i\in\mathrm{vars}}M_i\,d_i^2+\sum_{i\in\mathrm{vars}}M'_i\,d_i.$$

**Truth / Non-vacuity.** Definition.

**Junk values.** None.

**Concerns.** None.

### 18. `opCost_le_sepCost`

**Rendering.** The binders are:
- types $\iota,\kappa,\kappa'$ with decidable equality on $\iota$;
- a finite $\mathrm{vars}\subseteq\iota$;
- finite $\mathrm{mul}\subseteq\kappa$ with $a,b:\kappa\to\iota$, such that $a_k,b_k\in\mathrm{vars}$ for all $k\in\mathrm{mul}$;
- finite $\mathrm{add}\subseteq\kappa'$ with $a',b':\kappa'\to\iota$, such that $a'_k,b'_k\in\mathrm{vars}$ for all $k\in\mathrm{add}$;
- $d:\iota\to\mathbb R$ with $d_i\ge0$ for all $i\in\mathrm{vars}$.

Write $c^{\times}_i=\#\{k\in\mathrm{mul}:a_k=i\}+\#\{k\in\mathrm{mul}:b_k=i\}$ and $c^{+}_i=\#\{k\in\mathrm{add}:a'_k=i\}+\#\{k\in\mathrm{add}:b'_k=i\}$, cast to reals. The claim is:
$$\sum_{k\in\mathrm{mul}}d(a_k)d(b_k)+\sum_{k\in\mathrm{add}}\max(d(a'_k),d(b'_k))\ \le\ \tfrac12\sum_{i\in\mathrm{vars}}c^{\times}_i d_i^2+\sum_{i\in\mathrm{vars}}c^{+}_i d_i.$$

**Truth.** True.
- Summing fiberwise, the right side equals $\tfrac12\sum_{k\in\mathrm{mul}}(d(a_k)^2+d(b_k)^2)+\sum_{k\in\mathrm{add}}(d(a'_k)+d(b'_k))$.
- The first part dominates by AM–GM, which holds for all reals.
- The second part dominates because $x+y\ge\max(x,y)$ when $x,y\ge0$. The nonnegativity hypothesis is needed here: $d\equiv-1$ with one add-operation gives $-1>-2$.
- 5 000 random exact-rational instances: no violation.

**Non-vacuity.** Take all sets empty, or any instance with $d\ge0$.

**Junk values.** None.

**Concerns.** None.

### 19. `levelwise_optimisation`

**Rendering.** The binders are:
- a type $X$ and $L\in\mathbb N$;
- sets $S_\ell\subseteq X$ for $\ell\in\mathbb N$;
- $g:\mathbb N\times X\to\mathbb R$ with $g_\ell(x)\ge0$ for **all** $\ell,x$;
- $\varepsilon>0$;
- $d:\mathbb N\to X$ with $d_\ell\in S_\ell$ for **every** $\ell\in\mathbb N$.

The claim is that
$$\Big[\forall d':\mathbb N\to X\ \text{with}\ d'_\ell\in S_\ell\ \forall\ell:\ (\varepsilon^{-1})^2\Big(\sum_{\ell=0}^{L}g_\ell(d_\ell)\Big)^2\le(\varepsilon^{-1})^2\Big(\sum_{\ell=0}^{L}g_\ell(d'_\ell)\Big)^2\Big]$$
holds if and only if
$$\forall\ell\in\{0,\dots,L\},\ \forall x\in S_\ell:\ g_\ell(d_\ell)\le g_\ell(x).$$

**Truth.** True.
- Since $\varepsilon^{-2}>0$ and both sums are $\ge0$, the left side is equivalent to "$\sum g_\ell(d_\ell)\le\sum g_\ell(d'_\ell)$ for all feasible $d'$".
- For "⇐", sum the levelwise inequalities.
- For "⇒", test with $d'=d[\ell\mapsto x]$.
- Brute force on 3 000 random finite instances: no mismatch.

**Non-vacuity.** Take $S_\ell=X$ with $X$ nonempty.

**Junk values.** None ($\varepsilon>0$).

**Concerns.** None.
- The hypothesis on $d$ forces **every** $S_\ell$, $\ell\in\mathbb N$, to be nonempty, not only those with $\ell\le L$.
- $g\ge0$ is required everywhere.
- $\varepsilon$ plays no role.

### 20. `vIndepR` (definition)

**Rendering.** For a finite $s\subseteq\iota$, $E:\iota\to\mathbb R$, $e:\iota\to\mathbb Z$ and $d:\iota\to\mathbb R$:
$$\mathrm{vIndepR}(s,E,e,d)=\frac1{12}\sum_{i\in s}E_i\,4^{\,e_i-d_i},$$
where $4^{e_i-d_i}=\exp((e_i-d_i)\ln4)$ is the real power.

**Truth / Non-vacuity.** Definition.

**Junk values.** None (the base is positive).

**Concerns.** $e_i$ and $d_i$ enter only through $e_i-d_i$.

### 21. `vIndepR_natCast`

**Rendering.** For a finite $s\subseteq\iota$, $E:\iota\to\mathbb R$, $e:\iota\to\mathbb Z$ and $d:\iota\to\mathbb N$, with $d$ cast coordinatewise into $\mathbb R$:
$$\mathrm{vIndepR}(s,E,e,d)=\mathrm{vIndep}(s,E,e,d)=\frac1{12}\sum_{i\in s}E_i\,4^{\,e_i-d_i}.$$
On the right the exponent $e_i-d_i\in\mathbb Z$ is an integer power, possibly negative.

**Truth.** True, by `rpow_intCast`. Checked numerically on 2 000 instances.

**Non-vacuity.** There are no hypotheses.

**Junk values.** None. The subtraction is in $\mathbb Z$, not truncated.

**Concerns.** None.

### 22. `hasDerivAt_vIndepR_update`

**Rendering.** The binders are:
- decidable equality on $\iota$;
- a finite $s\subseteq\iota$;
- $E:\iota\to\mathbb R$, $e:\iota\to\mathbb Z$, $d:\iota\to\mathbb R$;
- $i\in s$ and $t\in\mathbb R$.

The claim: the real function $\tau\mapsto\frac1{12}\sum_{j\in s}E_j4^{e_j-d[i\mapsto\tau]_j}$ has derivative
$$-\frac{\ln4\cdot E_i\cdot4^{\,e_i-t}}{12}$$
at $\tau=t$.

**Truth.** True, since only the $i$-th term depends on $\tau$. Checked by finite differences on 2 000 instances.

**Non-vacuity.** Take $s=\{i\}$.

**Junk values.** None.

**Concerns.** None.

### 23. `hasDerivAt_sepCost_update`

**Rendering.** With decidable equality on $\iota$, a finite $\mathrm{vars}$, $M,M',d:\iota\to\mathbb R$, $i\in\mathrm{vars}$ and $t\in\mathbb R$: the function
$$\tau\mapsto\tfrac12\sum_{j\in\mathrm{vars}}M_j\,d[i\mapsto\tau]_j^2+\sum_{j\in\mathrm{vars}}M'_j\,d[i\mapsto\tau]_j$$
has derivative $M_i\,t+M'_i$ at $t$.

**Truth.** True. Checked by finite differences.

**Non-vacuity.** Take $\mathrm{vars}=\{i\}$.

**Junk values.** None.

**Concerns.** None.

### 24. `exists_unique_bitWidth`

**Rendering.** Take reals $\lambda,E,M,M'$ and $e\in\mathbb Z$, with:
- $\lambda>0$;
- $E>0$;
- $M\ge0$;
- $M'\ge0$;
- $M+M'>0$.

Then there is **exactly one** $t\in\mathbb R$ with
$$-\frac{\ln4\cdot E\cdot4^{\,e-t}}{12}+\lambda\,(Mt+M')=0.$$

**Truth.** True.
- The left side $f$ has derivative $\frac{(\ln4)^2E}{12}4^{e-t}+\lambda M>0$.
- $f(t)\to-\infty$ as $t\to-\infty$.
- As $t\to+\infty$, $f(t)\to+\infty$ (if $M>0$) or $\to\lambda M'>0$ (if $M=0$).
- Numerically: positive derivative, one sign change, bisection root found in 3 000 instances.
- The hypothesis $M+M'>0$ is needed: with $M=M'=0$, $f<0$ everywhere.

**Non-vacuity.** Take $\lambda=E=M'=1$, $M=0$, $e=0$.

**Junk values.** None.

**Concerns.** None.

### 25. `hasDerivAt_levelCost`

**Rendering.** The binders are:
- functions $C_t,V_d:\mathbb R\to\mathbb R$;
- reals $C_t',V_d',V,C,t$ with $V>0$, $C>0$, $C_t(t)>0$ and $V_d(t)>0$;
- $C_t$ has derivative $C_t'$ at $t$, and $V_d$ has derivative $V_d'$ at $t$.

The claim: $\tau\mapsto\sqrt{V\,C_t(\tau)}+\sqrt{V_d(\tau)\,C}$ has derivative
$$\frac{\sqrt{C/V_d(t)}\;V_d'+\sqrt{V/C_t(t)}\;C_t'}{2}$$
at $t$.

**Truth.** True, by the chain rule: $\frac{d}{d\tau}\sqrt{V C_t}=\frac{V C_t'}{2\sqrt{VC_t}}=\frac12\sqrt{V/C_t}\,C_t'$, and similarly for the second term. Finite differences on 2 000 instances agree.

**Non-vacuity.** Take $C_t\equiv V_d\equiv1$ and $V=C=1$.

**Junk values.** None under the hypotheses.

**Concerns.** None. The hypotheses $V>0$ and $C>0$ appear not to be needed: for $V\le0$ the first term is locally $0$ and the formula also gives $0$. This is harmless.

### 26. `levelCost_stationary_iff`

**Rendering.** For reals $V,C,C_t,V_d,C_t',V_d'$ with $C>0$, $C_t>0$ and $V_d>0$ (and **no** hypothesis on $V$):
$$\frac{\sqrt{C/V_d}\,V_d'+\sqrt{V/C_t}\,C_t'}{2}=0\iff V_d'+\sqrt{\frac{V\,V_d}{C\,C_t}}\;C_t'=0.$$

**Truth.** True.
- For $V\ge0$, multiply the left side by $2\sqrt{V_d/C}>0$ and use $\sqrt{V/C_t}\sqrt{V_d/C}=\sqrt{VV_d/(CC_t)}$.
- For $V<0$, both $\sqrt{V/C_t}$ and $\sqrt{VV_d/(CC_t)}$ are $0$, and both sides reduce to $V_d'=0$.
- 20 000 random instances, including $V\le0$: no mismatch.

**Non-vacuity.** Take $C=C_t=V_d=1$.

**Junk values.** For $V<0$ the statement holds only because $\sqrt{\text{negative}}=0$ appears consistently on both sides. The meaning for $V\ge0$ is intact.

**Concerns.** Minor: $V$ is unconstrained.

### 27. `vIndepR_antitone`

**Rendering.** For a finite $s\subseteq\iota$, $E:\iota\to\mathbb R$ with $E_i\ge0$ for $i\in s$, and $e:\iota\to\mathbb Z$: the map $d\mapsto\frac1{12}\sum_{i\in s}E_i4^{e_i-d_i}$ on $\mathbb R^\iota$ is antitone for the coordinatewise order. That is, if $d_i\le d'_i$ for all $i\in\iota$, then $\mathrm{vIndepR}(d')\le\mathrm{vIndepR}(d)$.

**Truth.** True. Each $4^{e_i-d_i}$ is decreasing in $d_i$, and $E_i\ge0$. Checked numerically.

**Non-vacuity.** Take $E\equiv0$.

**Junk values.** None.

**Concerns.** None.

### 28. `greedy_rounding_feasible`

**Rendering.** The binders are:
- a type $\iota$ and $n\in\mathbb N$;
- a bijection $\sigma:\iota\to\{0,\dots,n-1\}$ (so $|\iota|=n$);
- $V:\mathbb R^\iota\to\mathbb R$ antitone for the coordinatewise order;
- $d\in\mathbb R^\iota$ and $\tau\in\mathbb R$ with $V(d)\le\tau$.

Then there exists $k\in\mathbb N$ with $k\le n$ and
$$V\Big(i\mapsto\lfloor d_i\rfloor+[\sigma(i)<k]\Big)\le\tau.$$

**Truth.** True, and trivially so: $k=n$ always works. Then every coordinate becomes $\lfloor d_i\rfloor+1>d_i$, and antitonicity gives $V(\lfloor d\rfloor+1)\le V(d)\le\tau$. Checked numerically with $k=n$.

**Non-vacuity.** Take $\iota=\mathrm{Fin}\,n$, $\sigma=\mathrm{id}$, $V\equiv0$, $\tau=0$.

**Junk values.** None.

**Concerns.** **Yes.** The existential is always witnessed by the maximal $k=n$. So:
- the order $\sigma$ plays no role;
- nothing is asserted about which prefix, or how small a $k$, suffices;
- the conclusion is much weaker than its form suggests.

---

## Module `LagrangeBitWidth`

Throughout this module:
- $\mathrm{vIndepR}(d)=\frac1{12}\sum_{i\in s}E_i4^{e_i-d_i}$;
- $\mathrm{sepCost}(d)=\frac12\sum_{i\in s}M_id_i^2+\sum_{i\in s}M'_id_i$;
- "(35) at $i$" abbreviates
$$-\frac{\ln4\cdot E_i\cdot4^{\,e_i-d^\star_i}}{12}+\lambda\big(M_id^\star_i+M'_i\big)=0.$$

### 29. `levelCost34_le_levelCost33`

**Rendering.** For reals $V,V_d,C,C_t$ with $V_d\ge0$ and $C_t\ge0$ ($V$ and $C$ arbitrary):
$$\sqrt{VC_t}+\sqrt{V_dC}\ \le\ \sqrt{VC_t}+\sqrt{V_d(C+C_t)}.$$

**Truth.** True. $V_dC\le V_d(C+C_t)$, and $\sqrt{\cdot}$ is monotone on $\mathbb R$. The hypothesis $V_d\ge0$ is needed when $C<0$: $V_d=-1$, $C=-2$, $C_t=3$ gives $\sqrt2>0$. 50 000 random checks passed.

**Non-vacuity.** Take all variables $0$.

**Junk values.** $\sqrt{\cdot}$ of negative arguments ($V<0$ or $C<0$) is $0$. The statement stays true and meaningful.

**Concerns.** None.

### 30. `levelCost33_le_sqrt_mul`

**Rendering.** For reals $V,V_d,C,C_t$ with $C>0$ and $C_t\ge0$ ($V$ and $V_d$ arbitrary):
$$\sqrt{VC_t}+\sqrt{V_d(C+C_t)}\ \le\ \sqrt{1+C_t/C}\;\big(\sqrt{VC_t}+\sqrt{V_dC}\big).$$

**Truth.** True.
- $\sqrt{1+C_t/C}\ge1$ handles the first term.
- For $V_d\ge0$, $\sqrt{V_d(C+C_t)}=\sqrt{1+C_t/C}\sqrt{V_dC}$.
- For $V_d<0$, both square roots are $0$.
- 50 000 random checks passed.

**Non-vacuity.** Take $C=1$ and everything else $0$.

**Junk values.** $\sqrt{\text{neg}}=0$ for $V<0$ or $V_d<0$. Still meaningful.

**Concerns.** None.

### 31. `levelCost33_le_add_mul`

**Rendering.** The binders are as in #30 ($C>0$, $C_t\ge0$). The claim is:
$$\sqrt{VC_t}+\sqrt{V_d(C+C_t)}\ \le\ \Big(1+\frac{C_t}{2C}\Big)\big(\sqrt{VC_t}+\sqrt{V_dC}\big).$$

**Truth.** True, from #30 and $\sqrt{1+x}\le1+x/2$ for $x\ge0$. Checked numerically.

**Non-vacuity.** As in #30.

**Junk values.** As in #30.

**Concerns.** None.

### 32. `totalCost32_bounds`

**Rendering.** The binders are:
- $L\in\mathbb N$;
- sequences $V,V_d,C,C_t:\mathbb N\to\mathbb R$;
- reals $\varepsilon,r$, with $\varepsilon$ unconstrained;
- for all $\ell\in\mathbb N$: $V_{d,\ell}\ge0$, $C_\ell>0$ and $C_{t,\ell}\ge0$;
- $C_{t,\ell}/C_\ell\le r$ for $\ell\in\{0,\dots,L\}$.

Put $A=\sum_{\ell=0}^{L}\big(\sqrt{V_\ell C_{t,\ell}}+\sqrt{V_{d,\ell}C_\ell}\big)$ and $B=\sum_{\ell=0}^{L}\big(\sqrt{V_\ell C_{t,\ell}}+\sqrt{V_{d,\ell}(C_\ell+C_{t,\ell})}\big)$. The claim is that both of the following hold:
$$(\varepsilon^2)^{-1}A^2\le(\varepsilon^2)^{-1}B^2 \qquad\text{and}\qquad (\varepsilon^2)^{-1}B^2\le(1+r)\big((\varepsilon^2)^{-1}A^2\big).$$

**Truth.** True.
- $0\le A\le B$ termwise by #29, and $(\varepsilon^2)^{-1}\ge0$.
- $B\le\sqrt{1+r}\,A$ termwise by #30, using $C_{t,\ell}/C_\ell\le r$.
- $1+r\ge1$, since $r\ge C_{t,0}/C_0\ge0$.
- 20 000 random checks, including $\varepsilon=0$, passed.

**Non-vacuity.** Take $V\equiv V_d\equiv C_t\equiv0$, $C\equiv1$, $r=0$.

**Junk values.**
- $\varepsilon=0$ is allowed. Then $(\varepsilon^2)^{-1}=0^{-1}=0$ and both conjuncts collapse to $0\le0$.
- $V_\ell<0$ is allowed and gives $\sqrt{\cdot}=0$.
- The meaning for $\varepsilon\ne0$ is intact.

**Concerns.** Minor.
- $\varepsilon$ is unconstrained.
- $V_{d,\ell}\ge0$ is in fact redundant here given $C_\ell>0$.
- The positivity hypotheses are imposed for all $\ell\in\mathbb N$, although only $\ell\le L$ matter.

### 33. `lagrangian_le_of_eq35`

**Rendering.** The binders are:
- a type $\iota$ and a finite $s\subseteq\iota$;
- $E,M,M':\iota\to\mathbb R$ and $e:\iota\to\mathbb Z$, with $E_i\ge0$ and $M_i\ge0$ for $i\in s$ ($M'$ unconstrained);
- $\lambda\ge0$;
- $d^\star:\iota\to\mathbb R$ satisfying (35) at every $i\in s$;
- any $d:\iota\to\mathbb R$.

The claim is:
$$\mathrm{vIndepR}(d^\star)+\lambda\,\mathrm{sepCost}(d^\star)\ \le\ \mathrm{vIndepR}(d)+\lambda\,\mathrm{sepCost}(d).$$

**Truth.** True.
- The left and right sides are $\sum_{i\in s}\phi_i$ with $\phi_i(x)=\frac{E_i}{12}4^{e_i-x}+\lambda(\frac12M_ix^2+M'_ix)$.
- Each $\phi_i$ is convex, since $\phi_i''=\frac{(\ln4)^2E_i}{12}4^{e_i-x}+\lambda M_i\ge0$.
- (35) says $\phi_i'(d^\star_i)=0$.
- 80 000 random comparisons passed, including $M'<0$.

**Non-vacuity.** Choose $d^\star_i$ by #24; for example $s=\{0\}$, $E=M'=\lambda=1$, $M=0$. Alternatively take $s=\varnothing$.

**Junk values.** None.

**Concerns.** None. If $\lambda=0$, (35) forces $E_i=0$ on $s$, and the statement becomes $0\le0$.

### 34. `vIndepR_le_of_eq35`

**Rendering.** The hypotheses are exactly those of #33 ($E_i\ge0$ and $M_i\ge0$ on $s$, $\lambda\ge0$, (35) at every $i\in s$), for some $d$ with $\mathrm{sepCost}(d)\le\mathrm{sepCost}(d^\star)$. The claim is:
$$\mathrm{vIndepR}(d^\star)\le\mathrm{vIndepR}(d).$$

**Truth.** True, by #33 and $\lambda(\mathrm{sepCost}(d)-\mathrm{sepCost}(d^\star))\le0$. Checked numerically.

**Non-vacuity.** As in #33, with $d=d^\star$.

**Junk values.** None.

**Concerns.** None.

### 35. `sepCost_le_of_eq35`

**Rendering.** The hypotheses are as in #33, but with $\lambda>0$ strictly, for some $d$ with $\mathrm{vIndepR}(d)\le\mathrm{vIndepR}(d^\star)$. The claim is:
$$\mathrm{sepCost}(d^\star)\le\mathrm{sepCost}(d).$$

**Truth.** True, by #33 and division by $\lambda>0$. Checked numerically.

**Non-vacuity.** As in #33.

**Junk values.** None.

**Concerns.** None.

### 36. `exists_eq35_isMin`

**Rendering.** The binders are:
- a finite $s\subseteq\iota$;
- $E,M,M':\iota\to\mathbb R$ and $e:\iota\to\mathbb Z$, with $E_i>0$, $M_i\ge0$, $M'_i\ge0$ and $M_i+M'_i>0$ for all $i\in s$;
- $\lambda>0$.

Then there exists $d^\star:\iota\to\mathbb R$ such that:
- (35) holds at every $i\in s$;
- for every $d$ with $\mathrm{sepCost}(d)\le\mathrm{sepCost}(d^\star)$, we have $\mathrm{vIndepR}(d^\star)\le\mathrm{vIndepR}(d)$.

**Truth.** True. Take $d^\star_i$ from #24 for $i\in s$ (anything outside $s$), then apply #34.

**Non-vacuity.** The hypotheses are satisfiable, for example with $s=\varnothing$ or the data of #33.

**Junk values.** None.

**Concerns.** None.

### 37. `eq35_of_isLocalMinOn`

**Rendering.** The binders are:
- a finite type $\iota$ with decidable equality;
- $E,M,M':\iota\to\mathbb R$, $e:\iota\to\mathbb Z$ and $d^\star\in\mathbb R^\iota$. There is no sign condition on anything.

Write $F(d)=\frac1{12}\sum_{i\in\iota}E_i4^{e_i-d_i}$ and $G(d)=\frac12\sum_{i\in\iota}M_id_i^2+\sum_{i\in\iota}M'_id_i$, both summed over all of $\iota$. The hypotheses are:
- $d^\star$ is a local minimiser of $F$ on the level set $\{d:G(d)=G(d^\star)\}$. That is, there is a neighbourhood $U$ of $d^\star$ in $\mathbb R^\iota$ with $F(d^\star)\le F(d)$ for all $d\in U$ with $G(d)=G(d^\star)$;
- there is some $i$ with $M_id^\star_i+M'_i\ne0$.

Then there exists $\lambda\in\mathbb R$ (of any sign) such that (35) holds at **every** $i\in\iota$.

**Truth.** True. This is the Lagrange multiplier theorem.
- Mathlib's 1d version gives $(a,b)\ne0$ with $a\nabla G+b\nabla F=0$.
- $\nabla G(d^\star)\ne0$ forces $b\ne0$, and then $\lambda=a/b$.
- The gradients are $\partial_iF=-\ln4\,E_i4^{e_i-d_i}/12$ and $\partial_iG=M_id_i+M'_i$.
- Numerically, at constrained minimisers on 200 random ellipses, $\nabla F\parallel\nabla G$ to $4\cdot10^{-8}$.

**Non-vacuity.** Take $\iota=\{0,1\}$, $E=(1,1)$, $e=(0,0)$, $M=(0,0)$, $M'=(1,1)$, $d^\star=(c/2,c/2)$. On the line $d_0+d_1=c$ this is the global minimiser of the convex $F$, and $M_id^\star_i+M'_i=1\ne0$.

**Junk values.** None.

**Concerns.** None. As a consequence of the statement, any coordinate with $M_id^\star_i+M'_i=0$ must have $E_i=0$.

### 38. `marginalRatio_eq_of_isLocalMinOn`

**Rendering.** The hypotheses are identical to #37. The conclusion: there exists $\lambda\in\mathbb R$ such that for every $i\in\iota$ with $M_id^\star_i+M'_i\ne0$,
$$\frac{\ln4\cdot E_i\cdot4^{\,e_i-d^\star_i}/12}{M_id^\star_i+M'_i}=\lambda.$$

**Truth.** True, from #37 by dividing by the nonzero denominator.

**Non-vacuity.** As in #37.

**Junk values.** None: the division is only asserted where the denominator is nonzero.

**Concerns.** None. Nothing is asserted for coordinates with zero denominator.

### 39. `eq37_iff`

**Rendering.** The binders are:
- a finite $s\subseteq\iota$;
- $E,M,M':\iota\to\mathbb R$ and $e:\iota\to\mathbb Z$;
- a **single** real $w$, the same for every $i$;
- a hypothesis $c:=\sum_{i\in s}(M_iw+M'_i)\ne0$;
- $\lambda\in\mathbb R$.

The claim is:
$$\Big(\sum_{i\in s}-\frac{\ln4\,E_i\,4^{e_i-w}}{12}\Big)+\lambda\,c=0\iff\lambda=\frac{\sum_{i\in s}\ln4\,E_i\,4^{e_i-w}/12}{c}.$$

**Truth.** True: $-A+\lambda c=0\iff\lambda=A/c$ for $c\ne0$. 20 000 random checks passed.

**Non-vacuity.** Take $s=\{0\}$, $M'_0=1$, $M_0=0$.

**Junk values.** None ($c\ne0$).

**Concerns.** None.

### 40. `lambda37_pos`

**Rendering.** For a finite $s$, $E,M,M'$, $e$ and a real $w$, with:
- $E_i\ge0$ for all $i\in s$;
- some $i\in s$ with $E_i>0$;
- $\sum_{i\in s}(M_iw+M'_i)>0$.

The claim is:
$$0<\frac{\sum_{i\in s}\ln4\,E_i\,4^{e_i-w}/12}{\sum_{i\in s}(M_iw+M'_i)}.$$

**Truth.** True. The numerator is $>0$, since $\ln4>0$, $4^{x}>0$ and $E\ge0$ with one $E_i>0$. The denominator is $>0$.

**Non-vacuity.** Take $s=\{0\}$, $E_0=1$, $M_0=0$, $M'_0=1$.

**Junk values.** None.

**Concerns.** None.

### 41. `eq37_of_eq35`

**Rendering.** For a finite $s$, $E,M,M'$, $e$, $\lambda\in\mathbb R$ and $d:\iota\to\mathbb R$ such that (35) holds at $d$ for every $i\in s$, with no sign conditions:
$$\Big(\sum_{i\in s}-\frac{\ln4\,E_i4^{e_i-d_i}}{12}\Big)+\lambda\sum_{i\in s}(M_id_i+M'_i)=0.$$

**Truth.** True, by summing (35) over $s$.

**Non-vacuity.** Take $s=\varnothing$ or the data of #33.

**Junk values.** None.

**Concerns.** None.

### 42. `rpow_four_sub_add_one`

**Rendering.** For all real $e,d$:
$$4^{\,e-(d+1)}=4^{\,e-d}/4,$$
with real powers.

**Truth.** True, by `rpow_sub` with base $4>0$. Checked numerically.

**Non-vacuity.** There are no hypotheses.

**Junk values.** None.

**Concerns.** None.

### 43. `vIndepR_sub_update_add_one`

**Rendering.** With decidable equality on $\iota$, a finite $s$, $E:\iota\to\mathbb R$, $e:\iota\to\mathbb Z$, $d:\iota\to\mathbb R$ and $i\in s$:
$$\mathrm{vIndepR}(d)-\mathrm{vIndepR}\big(d[i\mapsto d_i+1]\big)=\frac{E_i\,4^{\,e_i-d_i}}{16},$$
where $\mathrm{vIndepR}(x)=\frac1{12}\sum_{j\in s}E_j4^{e_j-x_j}$.

**Truth.** True: $\frac{E_i}{12}(4^{x}-4^{x-1})=\frac{E_i}{12}\cdot\frac34\cdot4^{x}=\frac{E_i4^{x}}{16}$. Checked numerically.

**Non-vacuity.** Take $s=\{i\}$.

**Junk values.** None.

**Concerns.** None.

### 44. `sepCost_update_add_one_sub`

**Rendering.** With decidable equality on $\iota$, a finite $s$, $M,M',d:\iota\to\mathbb R$ and $i\in s$:
$$\mathrm{sepCost}\big(d[i\mapsto d_i+1]\big)-\mathrm{sepCost}(d)=M_i\big(d_i+\tfrac12\big)+M'_i.$$

**Truth.** True: $\frac12M_i((d_i+1)^2-d_i^2)+M'_i=M_i(d_i+\frac12)+M'_i$. Checked numerically.

**Non-vacuity.** Take $s=\{i\}$.

**Junk values.** None.

**Concerns.** None.

### 45. `errorBound_succ`

**Rendering.** For sequences $F,d:\mathbb N\to\mathbb R$ with $F_{\ell+1}=2F_\ell$ and $d_{\ell+1}=d_\ell+1$ for all $\ell$, and any $\ell\in\mathbb N$:
$$F_{\ell+1}\,4^{-d_{\ell+1}}=\frac{F_\ell\,4^{-d_\ell}}{2},$$
with real powers.

**Truth.** True: $2F_\ell\cdot4^{-d_\ell-1}=F_\ell4^{-d_\ell}/2$. Checked numerically.

**Non-vacuity.** Take $F_\ell=2^\ell$ and $d_\ell=\ell$.

**Junk values.** None.

**Concerns.** None.

### 46. `errorBound_eq_div_pow`

**Rendering.** The hypotheses are as in #45. For every $\ell\in\mathbb N$:
$$F_\ell\,4^{-d_\ell}=\frac{F_0\,4^{-d_0}}{2^{\ell}}.$$

**Truth.** True, by induction with #45. Checked numerically.

**Non-vacuity.** As in #45.

**Junk values.** None.

**Concerns.** None.

### 47. `errorShare_succ`

**Rendering.** For a finite $s\subseteq\iota$ and $B:\mathbb N\to(\iota\to\mathbb R)$ with $B_{\ell+1}(i)=B_\ell(i)/2$ for all $\ell\in\mathbb N$ and $i\in s$, and for any $\ell\in\mathbb N$ and $i\in s$:
$$\frac{B_{\ell+1}(i)}{\sum_{j\in s}B_{\ell+1}(j)}=\frac{B_\ell(i)}{\sum_{j\in s}B_\ell(j)}.$$

**Truth.** True.
- If $\sum_jB_\ell(j)\ne0$, numerator and denominator are both halved.
- If $\sum_jB_\ell(j)=0$, both denominators are $0$ and both sides equal $0$ by $x/0=0$.
- Checked numerically, including forced zero sums.

**Non-vacuity.** Take $B_\ell(i)=2^{-\ell}$.

**Junk values.** The zero-denominator case holds only through $x/0=0$ on both sides. This is consistent, but not a genuine ratio identity there.

**Concerns.** Minor. The theorem does not assume a nonzero denominator.

### 48. `variance_extended_le_two_mul`

**Rendering.** The binders are:
- a measurable space $\Omega$ with a **probability** measure $\mu$;
- types $\iota,\kappa$ with finite sets $s\subseteq\iota$ and $t\subseteq\kappa$;
- functions $\bar x_i,\delta_i:\Omega\to\mathbb R$ for $i\in\iota$, and $\bar z_j,\delta^Z_j:\Omega\to\mathbb R$ for $j\in\kappa$;
- $e:\iota\to\mathbb Z$, $d:\iota\to\mathbb N$ and a real $\mathrm{mse}$.

The hypotheses are:
1. $\bar x_i\in L^2(\mu)$ for $i\in s$.
2. For $i\in s$, $\delta_i$ is uniformly distributed on $[-2^{e_i-d_i-1},\,2^{e_i-d_i-1}]$ w.r.t. Lebesgue measure. That is, the law of $\delta_i$ equals normalised Lebesgue measure on that interval. The exponent is computed in $\mathbb Z$, and the lower endpoint is $-(2^{k})$.
3. $\bar z_j$ and $\delta^Z_j$ are AE-strongly measurable for $j\in t$.
4. $\bar z_j\delta^Z_j\in L^2(\mu)$ for $j\in t$.
5. $\int(\delta^Z_j)^2d\mu=\mathrm{mse}$ for every $j\in t$.
6. $\bar x_i$ is independent of $\delta_i$ ($i\in s$), and $\bar z_j$ is independent of $\delta^Z_j$ ($j\in t$).
7. The products $Y_a$ are **pairwise** independent for distinct $a,b$ in the disjoint union $s\sqcup t$. Here $Y_{\mathrm{inl}\,i}=\bar x_i\delta_i$ and $Y_{\mathrm{inr}\,j}=\bar z_j\delta^Z_j$.
8. $\big(\sum_{j\in t}\int\bar z_j^2d\mu\big)\cdot\mathrm{mse}\le\mathrm{vIndep}$, where $\mathrm{vIndep}:=\frac1{12}\sum_{i\in s}\big(\int\bar x_i^2d\mu\big)4^{\,e_i-d_i}$ (integer powers).

The conclusion is:
$$\operatorname{Var}_\mu\Big[\sum_{i\in s}\bar x_i\delta_i+\sum_{j\in t}\bar z_j\delta^Z_j\Big]\ \le\ 2\cdot\frac1{12}\sum_{i\in s}\Big(\int\bar x_i^2\,d\mu\Big)4^{\,e_i-d_i}.$$
Here $\operatorname{Var}$ is Mathlib's variance, the real part of $\int^{-}|X-\mathbb EX|^2$, which is $0$ if that is infinite.

**Truth.** True.
- Every $Y_a$ is in $L^2$: $\delta_i$ is a.e. bounded and AE-measurable because its law is a genuine uniform law, and for $j\in t$ this is hypothesis 4.
- Pairwise independence gives $\operatorname{Var}\sum Y_a=\sum\operatorname{Var}Y_a\le\sum\mathbb E Y_a^2$.
- $\mathbb E(\bar x_i\delta_i)^2=\mathbb E\bar x_i^2\cdot a_i^2/3$ with $a_i=2^{e_i-d_i-1}$. Since $a_i^2/3=4^{e_i-d_i}/12$, the $x$-part is $\le\mathrm{vIndep}$. This was verified exactly with fractions.
- $\mathbb E(\bar z_j\delta^Z_j)^2=\mathbb E\bar z_j^2\,\mathbb E(\delta^Z_j)^2=\mathbb E\bar z_j^2\cdot\mathrm{mse}$, so the $z$-part is $\le\mathrm{vIndep}$ by hypothesis 8.
- The factor $2$ is attained: 3 000 exact independent models reached a maximum Var/vIndep of exactly 2. A Monte Carlo run with $4\cdot10^5$ samples gave $0.06769$ against $2\,\mathrm{vIndep}=0.06771$.

**Non-vacuity.**
- The trivial instance $s=t=\varnothing$ gives $0\le0$.
- A substantive instance: $\Omega=[0,1]^3$ with Lebesgue measure, $\bar x_1\equiv1$, $\delta_1$ uniform on $[-a,a]$ from the first coordinate, and $\bar z_1$ and $\delta^Z_1$ independent symmetric $\pm$ variables built from the other coordinates, with $\mathrm{mse}\le\mathrm{vIndep}/\mathbb E\bar z_1^2$.

**Junk values.**
- The integrals in hypotheses 5 and 8 are Bochner integrals. They are $0$ when $\bar z_j$ or $\delta^Z_j$ is not in $L^2$, so these hypotheses can hold "by junk". However, independence together with hypothesis 4 then forces the other factor to vanish a.e., since $\mathbb E\bar z^2\cdot\mathbb E(\delta^Z)^2=\mathbb E(\bar z\delta^Z)^2<\infty$ in $[0,\infty]$. So the corresponding product is $0$ a.e. and the conclusion is unaffected.
- If $t=\varnothing$, $\mathrm{mse}$ is unconstrained and irrelevant.
- The variance on the left is genuine, because the sum is in $L^2$.

**Concerns.** Minor.
- Only pairwise independence of the products is assumed. That is exactly what the variance identity needs.
- $e_i$ and $d_i$ enter only through $e_i-d_i$.

---

## Supporting definitions ("from other modules")

### 49. `roundFixed` (definition)

**Rendering.** For $e\in\mathbb Z$, $d\in\mathbb N$ and $x\in\mathbb R$:
$$\mathrm{roundFixed}_{e,d}(x)=2^{\,e-d}\cdot\operatorname{rnd}\!\big(x/2^{\,e-d}\big).$$
- $e-d\in\mathbb Z$, so the power is an integer power, possibly negative.
- $\operatorname{rnd}$ is the nearest integer, with ties toward $+\infty$.

So the result is the nearest element of the grid $2^{e-d}\mathbb Z$ to $x$, with ties rounded up. Examples: $\mathrm{roundFixed}_{0,1}(0.25)=0.5$ and $\mathrm{roundFixed}_{0,1}(-0.25)=0$.

**Truth / Non-vacuity.** Definition.

**Junk values.** None. The divisor $2^{e-d}>0$, and the subtraction is in $\mathbb Z$.

**Concerns.** Minor (literal observations):
- $e$ and $d$ enter only through $e-d$.
- There is no range limit, clipping or overflow: any real $x$ is rounded to the grid.
- Ties are resolved upward, not to even.

### 50. `vIndep` (definition)

**Rendering.** For a type $\iota$, a finite $s\subseteq\iota$, $M:\iota\to\mathbb R$, $e:\iota\to\mathbb Z$ and $d:\iota\to\mathbb N$:
$$\mathrm{vIndep}(s,M,e,d)=\frac1{12}\sum_{i\in s}M_i\,4^{\,e_i-d_i}.$$
The exponent $e_i-d_i$ is computed in $\mathbb Z$ (no truncation), and the power is an integer power.

**Truth / Non-vacuity.** Definition.

**Junk values.** None.

**Concerns.** $e_i$ and $d_i$ enter only through $e_i-d_i$.

---

## Numerical-check log (scripts in `work_A_hg_path_bitwidth/`)

- `check_path.py`
  - identity failures: 0;
  - perturbed identity and bound failures: 0;
  - moment-bound violations: 0 (worst ratios 1.0, attained only in degenerate cases);
  - adversarial perturbation violations: 0 (worst ratio 1.0 at $r=\sigma=0$);
  - roundFixed path violations: 0 (worst ratio 0.652);
  - half-ulp violations: 0.
- `check_bitwidth.py`: all counters 0, covering:
  - opCost (exact rationals);
  - levelwise iff (brute force);
  - natCast;
  - derivatives;
  - unique root;
  - levelCost derivative;
  - stationary iff, including $V\le0$;
  - antitone and greedy with $k=n$.
- `check_lagrange.py`: all counters 0, covering:
  - levelCost inequalities;
  - totalCost32 bounds, including $\varepsilon=0$;
  - Lagrangian sufficiency, including $M'<0$;
  - eq37;
  - rpow and update identities;
  - errorBound and errorShare, including zero denominators.

  The Lagrange-necessity alignment was $3.9\cdot10^{-8}$.
- `check_variance.py`:
  - $\mathbb E\delta^2=4^{e-d}/12$ exactly;
  - 0 failures in 3 000 exact independent models, with maximum Var/vIndep $=2$;
  - Monte Carlo Var $=0.067694$ against $2\,\mathrm{vIndep}=0.067708$.
