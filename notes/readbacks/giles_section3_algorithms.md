# Blind read-back audit: packet `D_g_section3`

- **Date:** 2026-09-27
- **Packet:** `packet_D_g_section3.lean`
- **Number of declarations audited:** 53
  - 45 in the packet body: 13 definitions and 32 theorems/lemmas;
  - 8 supporting definitions from the trailing section "definitions used above, from other modules".
- **Work directory (numerical checks):** `work_D_g_section3/`
  - `check_algorithm.py`
  - `check_complexity.py`, `check_complexity_tail.py`, `check_complexity_tail2.py`
  - `check_mlqmc_impl.py`

## Rules followed

1. **Blind reading.** I opened only these sources:
   - the packet;
   - `prove2me_workspace/references/mission_auditor.md`;
   - Mathlib sources under `/home/user/mlmc-lean/.lake/packages/mathlib/Mathlib` and core Lean sources (toolchain v4.33.1), only to confirm the definitions and conventions of constants the statements use.

   I did not open project Lean sources, `docs/`, `notes/`, README, PLAN, `prove2me/`, `scripts/`, git history, papers or the web. I inferred no meaning from declaration or file names; names are used only as labels.
2. **Read-back principles of `mission_auditor.md`.**
   - Translate the code, not the intent.
   - Account for every binder, hypothesis and typeclass assumption.
   - Expand non-standard (project) definitions inline.
   - Surface degenerate cases and junk values.
   - Keep the exact strength of every relation and quantifier.
   - Use plain mathematical notation.

   The **Rendering** part of each entry is neutral and contains no judgment. The task asks for assessments, so they appear only under **Truth**, **Non-vacuity**, **Junk values** and **Concerns**.
3. **Numerical checks.** Python standard library only (no numpy or mpmath was available). I used exact `Fraction`s where possible and floats with tolerances otherwise.
4. **Formatting.** LaTeX is written with single backslashes, because this is a Markdown file and not a JSON payload.

### Packet artefacts (noted, not audited as content)

- **`le_floorEst` and `floorEst_le`.** Each displays an equation-compiler proof (`| 0 => … | 1 => … | _ + 2 => …`) followed by `:= sorry`. This is not valid Lean as displayed. Only the statement, up to the first `|`, is audited.
- **`omit [IsProbabilityMeasure μ] in`.** A blank line (a removed docstring) separates this line from `abs_integral_sub_le_alg1Rem`. `omit … in` applies to the next command, so that theorem does **not** assume that $\mu$ is a probability measure. It does not even assume that $\mu$ is finite.

---

## Verdict overview

| # | Declaration | Kind | Truth | Main flags |
|---|---|---|---|---|
| 1 | `alg1Rem` | def | — | degenerate for $\alpha\le 0$ (value $\le 0$; $=0$ at $\alpha=0$ by $x/0=0$); truncated indices for $L<2$ |
| 2 | `abs_div_le_alg1Rem` | lemma | true | — |
| 3 | `abs_tail_le` | thm | true | hypotheses unsatisfiable if $A<0$ (harmless) |
| 4 | `abs_tail_le_alg1Rem` | thm | true | — |
| 5 | `alg1Init` | def | — | — |
| 6 | `alg1Samples` | def | — | junk if $\varepsilon=0$, $C_\ell=0$ or negative $V,C$ |
| 7 | `alg1Level` | def | — | default value $0$; equals $2$ for every $m$ when $\alpha\le0\le\varepsilon$ |
| 8 | `alg1_terminates` | thm | true | — |
| 9 | `alg1Level_le` | thm | true | — |
| 10 | `alg1_variance` | thm | true | $N_0$ plays no role |
| 11 | `abs_integral_sub_le_alg1Rem` | thm | true | $\mu$ arbitrary measure (omit); $P$ need not be integrable (junk $\int P=0$) |
| 12 | `robust_test_mse` | thm | true | $P$ need not be integrable; $Y$ arbitrary $L^2$ variable |
| 13 | `alg1_mse` | thm | true | same as 12 |
| 14 | `alg1_not_guaranteed` | thm | true | $\alpha$ unconstrained, so the level clause is automatic for $\alpha\le0$; trivial constant witness |
| 15 | `alg1_complexity` | thm | true | no sign condition on $\beta$ (still true) |
| 16 | `mlqmcRatio` | def | — | $x/0=0$ if $C_\ell=0$ |
| 17 | `mlqmcLevel` | def | — | tie-breaking unspecified (`Classical.choose`) |
| 18 | `mlqmcStep` | def | — | — |
| 19 | `mlqmcIter` | def | — | — |
| 20 | `mlqmc_inner_terminates` | thm | true | purely existential, no bound on $n$ |
| 21 | `mlqmcInner` | def | — | default: returns input unchanged |
| 22 | `mlqmcState` | def | — | zero function at $L=0,1$ |
| 23 | `mlqmc_algorithm` | thm | true | $m$ and $(v,C)$ unrelated |
| 24 | `mlqmc_mse` | thm | true | hypothesis `hm` redundant; `hvar` is an equality; $P$ need not be integrable |
| 25 | `powerSum_variance_eq` | thm | true | — |
| 26 | `powerSum_variance_nonneg` | thm | true | — |
| 27 | `powerSum_variance_mean` | thm | true | $\nu$ not assumed probability, but forced |
| 28 | `floorEst` | def | — | — |
| 29 | `le_floorEst` | thm | true | packet artefact |
| 30 | `floorEst_ge_extrapolation` | thm | true | — |
| 31 | `floorEst_le` | thm | true | packet artefact |
| 32 | `lsSlope` | def | — | $=0$ when $s=\emptyset$ or $t$ constant on $s$ |
| 33 | `lsIntercept` | def | — | inherits 32 |
| 34 | `lsFit_le` | thm | true | — |
| 35 | `lsSlope_affine` | thm | true | — |
| 36 | `lsSlope_log_geometric` | thm | true | — |
| 37 | `gaussian_tail_three` | thm | true | numeric margin: $0.0026998<0.003$ |
| 38 | `consistency_check_gaussian` | thm | true | `hv` superfluous; threshold uses the sum of the three standard deviations |
| 39 | `consistency_check_chebyshev` | thm | true | bound $1/9$ is attained |
| 40 | `sampleVariance_relative_sd_le_iff` | thm | true | for $\kappa<1$ relies on $\sqrt{\text{neg}}=0$ (both sides true) |
| 41 | `integral_ternary` | thm | true | — |
| 42 | `measureReal_ternary_zero` | thm | true | — |
| 43 | `prob_all_zero` | thm | true | no explicit probability assumption, but forced by independence |
| 44 | `powerSum_variance_of_zero` | thm | true | $N=0$ gives $0/0=0$ |
| 45 | `mlqmc_doubling_level` | thm | true | near-tautological |
| 46 | `optimalN` | def | — | $\lceil\cdot\rceil_{\mathbb N}$ truncates negatives |
| 47 | `levelDiff` | def | — | index 0 is not a difference |
| 48 | `complexityBound` | def | — | junk only for $\varepsilon\le0$ or $\alpha=0$ |
| 49 | `Vb` | def | — | — |
| 50 | `Cb` | def | — | — |
| 51 | `levelL` | def | — | several junk cases ($\delta=0$, $\alpha=0$, non-positive $\log$ argument) |
| 52 | `lagrangeN` | def | — | $0^{-1}=0$, $\sqrt{\text{neg}}=0$, $x/0=0$ |
| 53 | `sumSqrtVC` | def | — | $\sqrt{\text{neg}}=0$ |

**No statement was judged false. No statement has contradictory (jointly unsatisfiable) hypotheses.**

---

## Conventions (confirmed in the Mathlib / core Lean sources)

Paths are relative to `/home/user/mlmc-lean/.lake/packages/mathlib/Mathlib` unless stated otherwise.

1. **Division and inverse by zero.**
   - $x/0=0$: `div_zero`, `Algebra/GroupWithZero/Basic.lean:407`.
   - $0^{-1}=0$: `inv_zero`, `Algebra/GroupWithZero/Defs.lean:236`.
2. **Square root.**
   - $\sqrt{x}=0 \iff x\le0$, so $\sqrt{\text{negative}}=0$: `Real.sqrt_eq_zero'`, `Analysis/Real/Sqrt.lean:268`.
   - For $y\ge0$: $\sqrt x\le y\iff x\le y^2$: `Real.sqrt_le_left`, line 224.
3. **Logarithms.**
   - `Real.log` sets $\log 0=0$ and $\log x=\log|x|$: `Analysis/SpecialFunctions/Log/Basic.lean:44, 103, 115`.
   - `Real.logb b x = log x / log b`: `Analysis/SpecialFunctions/Log/Base.lean:43`.
4. **Real powers.**
   - For $x>0$, `x ^ (y:ℝ) = exp (log x * y)`: `Analysis/SpecialFunctions/Pow/Real.lean:51`.
   - The negative-base formula is at line 95, and $0^y$ at lines 120 and 128.

   Every real power in the packet has base $2$ or base $\varepsilon$, and base $\varepsilon$ occurs only in `complexityBound`, which is used only with $\varepsilon>0$. A natural-number exponent, as in `(2:ℝ)^k` with `k : ℕ` or `ε ^ 2`, is the ordinary monoid power.
5. **Natural-number ceiling** $\lceil a\rceil_{\mathbb N}$ (`Nat.ceil`, written `⌈a⌉₊`).
   - $\lceil a\rceil_{\mathbb N}=0\iff a\le0$: `Algebra/Order/Floor/Semiring.lean:187`.
   - $a\le\lceil a\rceil_{\mathbb N}$: line 178.
   - $\lceil a\rceil_{\mathbb N}<a+1$ for $a\ge0$: line 357.
6. **Natural-number subtraction truncates:** $a-b=0$ when $a\le b$ (core). Below this is written $a\ominus b:=\max(a-b,0)$.
7. **`Nat.find h`** is the least $n$ satisfying the predicate, with lemmas `Nat.find_spec` and `Nat.find_min'`: `Data/Nat/Find.lean:60–83`. The packet uses it under `open Classical`, with classical decidability.
8. **`Finset.exists_max_image s f h : ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x`**: `Data/Finset/Max.lean:528`. `Classical.choose` of this returns *some* such $x$; which maximiser it returns is unspecified.
9. **Function updates and iteration.**
   - `Function.update f a v` changes $f$ only at $a$: `Logic/Function/Basic.lean:638`.
   - `f^[n]` is the $n$-fold iterate, with `f^[0] = id`: `Nat.iterate`, `Logic/Function/Iterate.lean:41`.
10. **Expectation notation.** `μ[X]` is notation for `∫ x, X x ∂μ`: `Probability/Notation.lean:53`, a scoped macro in `ProbabilityTheory`, which the packet opens.
11. **Bochner integral of a non-integrable function is $0$:** `integral_undef`, `MeasureTheory/Integral/Bochner/Basic.lean:202`.
12. **Variance.**
    - `evariance X μ = ∫⁻ ‖X − μ[X]‖ₑ²` and `variance X μ = (evariance X μ).toReal`: `Probability/Moments/Variance.lean:58, 64`.
    - For a finite measure and an a.e.-strongly-measurable $X\notin L^2$, the evariance is $\infty$ (line 110), so the variance is $0$, because `ENNReal.toReal ∞ = 0` (`Data/ENNReal/Basic.lean:283`).
    - For $X\in L^2$ the variance is $\int(X-\mathbb E X)^2$ (line 155).
13. **`MemLp f p μ`** means `AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞`: `MeasureTheory/Function/LpSeminorm/Defs.lean:118`. `Integrable` is defined at `MeasureTheory/Function/L1Space/Integrable.lean:59`.
14. **`μ.real s = (μ s).toReal`** for every set $s$, measurable or not, via the outer measure: `MeasureTheory/Measure/MeasureSpaceDef.lean:101`.
15. **`HasLaw X μ P`** means $X$ is $P$-a.e. measurable and $P\circ X^{-1}=\mu$: `Probability/HasLaw.lean:39`.
16. **`gaussianReal m v`**, with $v\in\mathbb R_{\ge0}$, is the Gaussian with mean $m$ and **variance** $v$, or the Dirac mass at $m$ when $v=0$. It is a probability measure: `Probability/Distributions/Gaussian/Real.lean:222`.
17. **Measure preservation and image measures.**
    - `MeasurePreserving f μa μb` means $f$ is measurable and `map f μa = μb`: `Dynamics/Ergodic/MeasurePreserving.lean:45`.
    - `Measure.map` of a non-a.e.-measurable map is $0$: `MeasureTheory/Measure/Map.lean:112`. This is never triggered here, because measurability is part of the `MeasurePreserving` and `HasLaw` structures.
18. **Independence.** `iIndepFun f μ` unfolds to the following: for **every** finite index set $S$, including $S=\emptyset$, and sets $A_i$ in the σ-algebra generated by $f_i$, we have $\mu(\bigcap_{i\in S}A_i)=\prod_{i\in S}\mu(A_i)$.
    - Sources: `Probability/Independence/Basic.lean:136`; `Kernel/Indep.lean:68`; `Basic.lean:160` (`iIndepSets_iff`).
    - The case $S=\emptyset$ forces $\mu(\Omega)=1$. Mathlib records this as `iIndepFun.isProbabilityMeasure`, `Basic.lean:790`.
19. **The literal `0.003 : ℝ`** is `OfScientific` via `NNRatCast.toOfScientific` and equals exactly $3/1000$: `Algebra/Order/Ring/Unbundled/Rat.lean:45`, `Algebra/Field/Rat.lean:108`.
20. **`|a|` is `macro:max` for `abs a`**: `Algebra/Order/Group/Unbundled/Abs.lean:45`. Hence `max (max A B) |m L| / D` parses as $\max(A,B,|m_L|)/D$, because application binds tighter than `/`.
21. **`omit [inst] in cmd`** keeps the instance out of the next declaration only: core `src/lean/Lean/Parser/Command.lean:972–977`. Without it, an instance-implicit section variable such as `[IsProbabilityMeasure μ]` is included whenever the variables it depends on (here $\mu$) are.
22. **Standard notions.**
    - `Finset.range n` is $\{0,\dots,n-1\}$.
    - `Tendsto f atTop (𝓝 a)` means $f(n)\to a$ as $n\to\infty$.
    - `Real.exp (-1)` is $e^{-1}\approx0.3679$.

---

## Notation used in the renderings

Every entry below re-expands the project definitions it uses. The following symbols are used throughout:

- $a\ominus b:=\max(a-b,0)$ for natural numbers.
- $2^{x}$: for real $x$, the real power $e^{x\ln2}$; for natural $x$, the ordinary power.
- $\lceil x\rceil_{\mathbb N}$: the least natural number $n$ with $x\le n$, which is $0$ whenever $x\le0$.
- $\mathbb E_\mu[f]:=\int_\Omega f\,d\mu$ (Bochner), taken to be $0$ when $f$ is not $\mu$-integrable.
- $\operatorname{Var}_\mu(Y):=\bigl(\int^{-}|Y-\mathbb E_\mu Y|^2\,d\mu\bigr)$ converted to a real number, with $\infty\mapsto0$.
- For $P_\ell:\Omega\to\mathbb R$: $\Delta P_0:=P_0$ and $\Delta P_j:=P_j-P_{j-1}$ pointwise for $j\ge1$. This is `levelDiff`.

---

## Part A — declarations from `MlmcLean.Algorithm`

### 1. `alg1Rem` (definition)

**Rendering.** The inputs are a real sequence $m=(m_j)_{j\in\mathbb N}$, a real number $\alpha$ and a natural number $L$. The output is the real number
$$\operatorname{alg1Rem}(m,\alpha,L)=\frac{\max\bigl\{\,|m_{L\ominus2}|\cdot2^{-2\alpha},\ \ |m_{L\ominus1}|\cdot2^{-\alpha},\ \ |m_L|\,\bigr\}}{2^{\alpha}-1}.$$
- $L\ominus j=\max(L-j,0)$. For $L=0$ all three indices are $0$; for $L=1$ the first two indices are $0$.
- $2^{-2\alpha}$, $2^{-\alpha}$ and $2^\alpha$ are real powers.
- The quotient is $0$ when the denominator is $0$, that is, when $\alpha=0$.

**Truth.** Not applicable (definition). The `max` parse is confirmed (Convention 20).

**Non-vacuity.** Not applicable; the function is total.

**Junk values.**
- $\alpha=0$: the denominator is $0$, so the value is $0$ for every $m$ and $L$.
- $\alpha<0$: the denominator is negative, so the value is $\le0$.
- $L\in\{0,1\}$: indices truncated by natural-number subtraction.

None of these is triggered when $\alpha>0$ and $L\ge2$; the value is then $\ge0$.

**Concerns.** For $\alpha\le0$, every inequality $\operatorname{alg1Rem}(m,\alpha,L)\le\delta$ with $\delta\ge0$ holds automatically. This propagates to `alg1Level` (entry 7) and `alg1_not_guaranteed` (entry 14).

### 2. `abs_div_le_alg1Rem` (lemma)

**Rendering.** For every real sequence $m$, every real $\alpha$ with $\alpha>0$, and every $L\in\mathbb N$:
$$\frac{|m_L|}{2^{\alpha}-1}\ \le\ \frac{\max\{|m_{L\ominus2}|\,2^{-2\alpha},\ |m_{L\ominus1}|\,2^{-\alpha},\ |m_L|\}}{2^{\alpha}-1}.$$
The right-hand side is $\operatorname{alg1Rem}(m,\alpha,L)$, with $L\ominus j=\max(L-j,0)$.

**Truth.** True. For $\alpha>0$ we have $2^\alpha-1>0$, and $|m_L|$ is one of the terms of the maximum. Checked on 2000 random cases (`check_algorithm.py`).

**Non-vacuity.** The only hypothesis is $\alpha>0$, for example $\alpha=1$.

**Junk values.** None that affects the statement: the denominator is positive, and for $L<2$ the truncated indices appear only in the other terms of the maximum.

**Concerns.** None.

### 3. `abs_tail_le` (theorem)

**Rendering.**
- Data: $q:\mathbb N\to\mathbb R$, $q'\in\mathbb R$, $\alpha,A\in\mathbb R$, $L\in\mathbb N$.
- Hypotheses:
  - $q_\ell\to q'$ as $\ell\to\infty$;
  - $\alpha>0$ (there is no sign condition on $A$);
  - for every natural $\ell>L$,
  $$|q_\ell-q_{\ell-1}|\le A\cdot2^{-\alpha(\ell-L)}.$$
- Conclusion:
$$|q'-q_L|\le\frac{A}{2^{\alpha}-1}.$$

**Truth.** True. Telescoping gives $q'-q_L=\lim_{M\to\infty}\sum_{\ell=L+1}^{M}(q_\ell-q_{\ell-1})$. Hence $|q'-q_L|\le A\sum_{j\ge1}2^{-\alpha j}=A/(2^\alpha-1)$. Equality is attained when all increments have the same sign and maximal size.

**Non-vacuity.** Take $q$ constant, $A\ge0$ and $\alpha=1$. If $A<0$, the hypothesis already fails at $\ell=L+1$, since the left side is $\ge0$ and the right side is $<0$. So the hypotheses can hold only when $A\ge0$.

**Junk values.** None. Since $\ell>L\ge0$ we have $\ell\ge1$, so $\ell-1$ is not truncated, and the denominator is positive.

**Concerns.** None. $A\ge0$ is not stated, but it is forced.

### 4. `abs_tail_le_alg1Rem` (theorem)

**Rendering.**
- Data: $q,m:\mathbb N\to\mathbb R$, $q'\in\mathbb R$, $\alpha\in\mathbb R$, $L,k\in\mathbb N$.
- Hypotheses:
  - $q_\ell\to q'$;
  - $\alpha>0$;
  - $k\le2$ and $k\le L$;
  - for every natural $\ell>L$,
  $$|q_\ell-q_{\ell-1}|\le|m_{L-k}|\cdot2^{-\alpha\,(\ell-(L-k))}.$$
  Here $L-k$ is computed in $\mathbb N$ and then cast to $\mathbb R$; since $k\le L$ it is the true difference.
- Conclusion:
$$|q'-q_L|\le\operatorname{alg1Rem}(m,\alpha,L)=\frac{\max\{|m_{L\ominus2}|\,2^{-2\alpha},\ |m_{L\ominus1}|\,2^{-\alpha},\ |m_L|\}}{2^\alpha-1}.$$

**Truth.** True. The tail sum is $|m_{L-k}|\,2^{-\alpha k}\sum_{j\ge1}2^{-\alpha j}=|m_{L-k}|\,2^{-\alpha k}/(2^\alpha-1)$. For $k=0,1,2$ this numerator is the third, second and first term of the maximum respectively. A 3000-case stress test with extremal increments (`check_algorithm.py`) gave $\max(\text{lhs}-\text{rhs})=2.2\times10^{-16}$, which is rounding; equality is attainable.

**Non-vacuity.** Take $q$ constant, any $m$, and $L=k=0$.

**Junk values.** For $L<2$, the numerator of `alg1Rem` contains truncated indices. For example, at $L=1$ the "$L-2$" term is $|m_0|2^{-2\alpha}$. Because $k\le L$, the term the bound actually needs is genuine, and the extra terms only enlarge the right side.

**Concerns.** $m$ and $q$ are linked only through the hypothesis.

### 5. `alg1Init` (definition)

**Rendering.** For natural numbers $N_0$ and $\ell$: $\operatorname{alg1Init}(N_0,\ell)=N_0$ if $\ell\le2$, and $0$ otherwise.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** None.

**Concerns.** None.

### 6. `alg1Samples` (definition)

**Rendering.** The inputs are $N_0\in\mathbb N$, real sequences $V,C:\mathbb N\to\mathbb R$ and a real $\varepsilon$. The output is a family of natural numbers $N^{(L)}_\ell$ for $L,\ell\in\mathbb N$, defined by recursion on $L$:
$$N^{(0)}_\ell=\begin{cases}N_0,&\ell\le2,\\0,&\ell>2,\end{cases}$$
$$N^{(L+1)}_\ell=\max\Bigl(N^{(L)}_\ell,\ \ c^{(L+1)}_\ell\Bigr),\qquad c^{(L+1)}_\ell=\begin{cases}\Bigl\lceil\ \tau^{-1}\cdot\sqrt{V_\ell/C_\ell}\cdot\sum_{j=0}^{L+1}\sqrt{V_j\,C_j}\ \Bigr\rceil_{\mathbb N}&\text{if }2\le L+1\text{ and }\ell\le L+1,\\[2pt]0&\text{otherwise,}\end{cases}$$
where $\tau=\varepsilon^2/2$.
- $c^{(L+1)}_\ell$ is `optimalN (range (L+2)) V C (ε²/2) ℓ`, expanded through `lagrangeN` and `sumSqrtVC`, whose index set is $\{0,\dots,L+1\}$.
- $\lceil x\rceil_{\mathbb N}$ is the least natural number $\ge x$.
- $\sqrt{x}=0$ for $x<0$, $x/0=0$ and $0^{-1}=0$.

In particular $N^{(1)}=N^{(0)}$. For $L'\ge2$ and $\varepsilon\neq0$:
$$N^{(L')}_\ell=\max\Bigl(N^{(L'-1)}_\ell,\ \mathbf 1[\ell\le L']\cdot\bigl\lceil(2/\varepsilon^2)\sqrt{V_\ell/C_\ell}\,\textstyle\sum_{j=0}^{L'}\sqrt{V_jC_j}\bigr\rceil_{\mathbb N}\Bigr).$$

**Truth / Non-vacuity.** Not applicable. The recursion is structural in $L$.

**Junk values.**
- $\varepsilon=0$: $\tau^{-1}=0^{-1}=0$, so every new term is $0$ and $N^{(L)}=N^{(0)}$ for all $L$.
- $C_\ell=0$: $V_\ell/C_\ell=0$.
- Negative $V_\ell/C_\ell$ or $V_jC_j$: the square root is $0$.
- Non-positive argument of the ceiling: the result is $0$.

None of these occurs when all $V_j,C_j>0$ and $\varepsilon\ne0$.

**Concerns.**
- Derived fact, not part of the rendering: if $V,C>0$ and $\varepsilon\ne0$, then $S_{L'}=\sum_{j\le L'}\sqrt{V_jC_j}$ increases with $L'$. So for $L\ge2$ and $\ell\le L$:
$$N^{(L)}_\ell=\max\bigl(N_0\mathbf 1[\ell\le2],\ \lceil(2/\varepsilon^2)\sqrt{V_\ell/C_\ell}\,S_L\rceil_{\mathbb N}\bigr).$$
- Index 2 already receives $N_0$ at stages $L=0$ and $L=1$.

### 7. `alg1Level` (definition)

**Rendering.** The inputs are $m:\mathbb N\to\mathbb R$ and real $\alpha,\varepsilon$.
- If some natural $L$ satisfies $L\ge2$ and $\operatorname{alg1Rem}(m,\alpha,L)\le\varepsilon/\sqrt2$, the output is the **least** such $L$.
- Otherwise the output is $0$.

Here, for $L\ge2$ (so no index truncation):
$$\operatorname{alg1Rem}(m,\alpha,L)=\frac{\max\{|m_{L-2}|\,2^{-2\alpha},|m_{L-1}|\,2^{-\alpha},|m_L|\}}{2^\alpha-1},$$
with quotient $0$ if $\alpha=0$. The existence test uses classical logic.

**Truth / Non-vacuity.** Not applicable.

**Junk values.**
- The default value $0$ is returned when no admissible $L$ exists. For example, $\varepsilon<0$ with $\alpha>0$, or a sequence $m$ with $\liminf_L\operatorname{alg1Rem}>\varepsilon/\sqrt2$.
- For $\alpha\le0$ we have $\operatorname{alg1Rem}\le0$, so for every $\varepsilon\ge0$ the output is $2$, whatever $m$ is.

**Concerns.**
- The output is never $1$, and it is $0$ only in the "no admissible $L$" case.
- The test at $L=2$ involves $m_0$. In the probabilistic statements below, $m_0=\mathbb E[P_0]$ itself, not a difference.

### 8. `alg1_terminates` (theorem)

**Rendering.** For every $m:\mathbb N\to\mathbb R$ with $m_\ell\to0$, every real $\alpha>0$ and every real $\varepsilon>0$, there exists $L\in\mathbb N$ with $L\ge2$ and
$$\frac{\max\{|m_{L-2}|\,2^{-2\alpha},\ |m_{L-1}|\,2^{-\alpha},\ |m_L|\}}{2^\alpha-1}\le\frac{\varepsilon}{\sqrt2}.$$

**Truth.** True. The numerator tends to $0$, while the denominator is a fixed positive number and $\varepsilon/\sqrt2>0$.

**Non-vacuity.** Take $m=0$.

**Junk values.** None.

**Concerns.** None. Under these hypotheses, `alg1Level` is the genuine least $L$ and never the default $0$.

### 9. `alg1Level_le` (theorem)

**Rendering.**
- Data: $m:\mathbb N\to\mathbb R$ and real $\alpha,c,\varepsilon$.
- Hypotheses:
  - $\alpha>0$, $c>0$, $\varepsilon>0$;
  - $|m_\ell|\le c\cdot2^{-\alpha\ell}$ for every $\ell\in\mathbb N$.

Let $\hat L=\operatorname{alg1Level}(m,\alpha,\varepsilon)$: the least $L\ge2$ with $\max\{|m_{L-2}|2^{-2\alpha},|m_{L-1}|2^{-\alpha},|m_L|\}/(2^\alpha-1)\le\varepsilon/\sqrt2$, or $0$ if there is none. Then all three of the following hold:
1. $2\le\hat L$;
2. $\max\{|m_{\hat L-2}|\,2^{-2\alpha},|m_{\hat L-1}|\,2^{-\alpha},|m_{\hat L}|\}/(2^\alpha-1)\le\varepsilon/\sqrt2$;
3. the level bound
$$\hat L\le\max\Bigl(2,\ \Bigl\lceil\frac1\alpha\log_2\frac{c/(2^\alpha-1)}{\varepsilon/\sqrt2}\Bigr\rceil_{\mathbb N}\Bigr).$$
   The inner term is `levelL α (c/(2^α−1)) (ε/√2)`, where $\operatorname{levelL}(\alpha,c_1,\delta)=\lceil\log_2(c_1/\delta)/\alpha\rceil_{\mathbb N}$ and $\lceil x\rceil_{\mathbb N}=0$ for $x\le0$.

**Truth.** True.
- Parts 1 and 2: $m\to0$, so an admissible $L$ exists (entry 8), and `Nat.find` returns an admissible value.
- Part 3: for $L\ge2$ every numerator term is $\le c\,2^{-\alpha L}$, so $\operatorname{alg1Rem}(m,\alpha,L)\le c\,2^{-\alpha L}/(2^\alpha-1)$. This is $\le\varepsilon/\sqrt2$ as soon as $L\ge\log_2\bigl(c\sqrt2/((2^\alpha-1)\varepsilon)\bigr)/\alpha$. The candidate $\max(2,\lceil\cdot\rceil_{\mathbb N})$ therefore qualifies, so the least admissible $L$ is at most it.
- Numerically: 0 violations in 3000 random cases (`check_algorithm.py`).

**Non-vacuity.** Take $m=0$ and $c=1$.

**Junk values.** None that matters. The argument of $\log_2$ is positive. When that logarithm is negative, the ceiling truncates to $0$, which the $\max$ with $2$ absorbs.

**Concerns.** None.

### 10. `alg1_variance` (theorem)

**Rendering.**
- Data: $N_0\in\mathbb N$; $V,C:\mathbb N\to\mathbb R$; real $\varepsilon$; $L\in\mathbb N$.
- Hypotheses: $V_\ell>0$ and $C_\ell>0$ for every $\ell$; $\varepsilon>0$; $L\ge2$.
- Conclusion:
$$\sum_{\ell=0}^{L}\frac{V_\ell}{N^{(L)}_\ell}\le\frac{\varepsilon^2}{2}.$$

Here $N^{(L)}_\ell=\operatorname{alg1Samples}(N_0,V,C,\varepsilon,L,\ell)$, cast to $\mathbb R$, is defined by:
- $N^{(0)}_\ell=N_0\mathbf 1[\ell\le2]$;
- $N^{(L'+1)}_\ell=\max\bigl(N^{(L')}_\ell,\ \mathbf 1[2\le L'+1\wedge\ell\le L'+1]\cdot\lceil(\varepsilon^2/2)^{-1}\sqrt{V_\ell/C_\ell}\sum_{j=0}^{L'+1}\sqrt{V_jC_j}\rceil_{\mathbb N}\bigr)$.

**Truth.** True.
- For $L\ge2$ and $\ell\le L$, the last recursion step gives $N^{(L)}_\ell\ge(2/\varepsilon^2)\sqrt{V_\ell/C_\ell}\,S_L>0$, where $S_L=\sum_{j\le L}\sqrt{V_jC_j}$.
- Hence $V_\ell/N^{(L)}_\ell\le(\varepsilon^2/2)\sqrt{V_\ell C_\ell}/S_L$. Summing over $\ell\le L$ gives $\le\varepsilon^2/2$.
- Numerically: the maximum of $\text{sum}/(\varepsilon^2/2)$ over 400 random cases is $0.99999999976$.

**Non-vacuity.** Take $V=C=1$, $\varepsilon=1$, $L=2$.

**Junk values.** None. Under the hypotheses every denominator $N^{(L)}_\ell$ with $\ell\le L$ is $\ge1$.

**Concerns.**
- $N_0$ plays no role in the bound; a larger $N_0$ only enlarges the $N^{(L)}_\ell$.
- The statement is deterministic: $V$ is just a positive sequence.

### 11. `abs_integral_sub_le_alg1Rem` (theorem)

**Rendering.**
- Data:
  - a type $\Omega$ with a σ-algebra and a measure $\mu$ on it. $\mu$ is **arbitrary**: it is not assumed finite or a probability measure, because the section's probability assumption is explicitly omitted;
  - functions $P:\Omega\to\mathbb R$ and $P_\ell:\Omega\to\mathbb R$ for $\ell\in\mathbb N$;
  - $\alpha\in\mathbb R$ and $L,k\in\mathbb N$.
- Notation: $\Delta P_0=P_0$, $\Delta P_j=P_j-P_{j-1}$ for $j\ge1$, and $m_j=\int_\Omega\Delta P_j\,d\mu$.
- Hypotheses:
  - $\alpha>0$, $k\le2$, $k\le L$;
  - every $P_\ell$ is $\mu$-integrable;
  - $\int P_\ell\,d\mu\to\int P\,d\mu$ as $\ell\to\infty$. $P$ is not assumed integrable or measurable; if it is not integrable, $\int P\,d\mu$ is $0$;
  - for every natural $\ell>L$: $\ |m_\ell|\le|m_{L-k}|\cdot2^{-\alpha(\ell-(L-k))}$.
- Conclusion:
$$\Bigl|\int P\,d\mu-\int P_L\,d\mu\Bigr|\le\operatorname{alg1Rem}(m,\alpha,L)=\frac{\max\{|m_{L\ominus2}|\,2^{-2\alpha},\ |m_{L\ominus1}|\,2^{-\alpha},\ |m_L|\}}{2^\alpha-1}.$$

**Truth.** True. For $\ell\ge1$, integrability gives $m_\ell=\int P_\ell-\int P_{\ell-1}$. Entry 4 with $q_\ell=\int P_\ell\,d\mu$ and $q'=\int P\,d\mu$ then applies. No finiteness of $\mu$ is needed.

**Non-vacuity.** Take $P=P_\ell=0$ for any measure.

**Junk values.**
- If $P$ is not integrable, $\int P\,d\mu=0$ by convention. The hypothesis then says $\int P_\ell\to0$, and the conclusion bounds $|\int P_L|$.
- $m_0=\int P_0$ is not a difference.
- For $L<2$ the indices in `alg1Rem` are truncated, which is harmless.

**Concerns.**
- $\mu$ is completely general here, unlike in entries 12–14.
- When $L=k$, the anchor is $m_{L-k}=m_0=\int P_0\,d\mu$, the integral of $P_0$ itself.

### 12. `robust_test_mse` (theorem)

**Rendering.**
- Data:
  - a type $\Omega$ with a σ-algebra and a **probability** measure $\mu$;
  - $Y,P:\Omega\to\mathbb R$ and $P_\ell:\Omega\to\mathbb R$ for $\ell\in\mathbb N$;
  - real $\alpha,\varepsilon$ and natural $L,k$.
- Notation: $\mathbb E[f]=\int f\,d\mu$ (and $0$ if $f$ is not integrable), $\Delta P_0=P_0$, $\Delta P_j=P_j-P_{j-1}$, $m_j=\mathbb E[\Delta P_j]$.
- Hypotheses:
  - $\alpha>0$, $k\le2$, $k\le L$;
  - $Y\in L^2(\mu)$;
  - every $P_\ell$ is integrable;
  - $\mathbb E[P_\ell]\to\mathbb E[P]$, where $P$ is not assumed integrable;
  - for every $\ell>L$: $|m_\ell|\le|m_{L-k}|\,2^{-\alpha(\ell-(L-k))}$;
  - $\mathbb E[Y]=\mathbb E[P_L]$;
  - $\operatorname{Var}_\mu(Y)\le\varepsilon^2/2$;
  - the **strict** test
  $$\frac{\max\{|m_{L\ominus2}|\,2^{-2\alpha},|m_{L\ominus1}|\,2^{-\alpha},|m_L|\}}{2^\alpha-1}<\frac{\varepsilon}{\sqrt2}.$$
- Conclusion (strict):
$$\mathbb E\bigl[(Y-\mathbb E[P])^2\bigr]<\varepsilon^2.$$

**Truth.** True.
- For $Y\in L^2$ and a probability measure, $\mathbb E[(Y-c)^2]=\operatorname{Var}(Y)+(\mathbb E Y-c)^2$.
- By entry 11, $|\mathbb E Y-\mathbb E P|=|\mathbb E P_L-\mathbb E P|\le\operatorname{alg1Rem}$.
- $0\le\operatorname{alg1Rem}<\varepsilon/\sqrt2$ gives a squared bias $<\varepsilon^2/2$. Adding the variance, which is $\le\varepsilon^2/2$, gives $<\varepsilon^2$.

**Non-vacuity.** Take a one-point $\Omega$, $Y=P=P_\ell=0$ and $\varepsilon=1$.

**Junk values.**
- $\mathbb E[P]$ is the junk value $0$ if $P$ is not integrable.
- The variance is genuine because $Y\in L^2$.
- The integrand $(Y-c)^2$ is integrable, so there is no integral junk in the conclusion.

**Concerns.**
- $Y$ is an arbitrary $L^2$ function. The statement links it to the rest only through $\mathbb E[Y]=\mathbb E[P_L]$ and the variance bound; no construction of $Y$ appears.
- $\varepsilon>0$ is not assumed, but it follows from the strict test, since $\operatorname{alg1Rem}\ge0$ when $\alpha>0$.
- The target $\mathbb E[P]$ may be a junk value (see above).

### 13. `alg1_mse` (theorem)

**Rendering.** The data are the same as in entry 12: a probability measure $\mu$ on $\Omega$; $Y,P,(P_\ell)$; real $\alpha,\varepsilon$; natural $L,k$; and $m_j=\mathbb E[\Delta P_j]$. The hypotheses are the same, except the test is **non-strict**:
- $\alpha>0$, $k\le2$, $k\le L$;
- $Y\in L^2(\mu)$;
- every $P_\ell$ is integrable;
- $\mathbb E[P_\ell]\to\mathbb E[P]$;
- for every $\ell>L$: $|m_\ell|\le|m_{L-k}|\,2^{-\alpha(\ell-(L-k))}$;
- $\mathbb E[Y]=\mathbb E[P_L]$;
- $\operatorname{Var}_\mu(Y)\le\varepsilon^2/2$;
- $\max\{|m_{L\ominus2}|\,2^{-2\alpha},|m_{L\ominus1}|\,2^{-\alpha},|m_L|\}/(2^\alpha-1)\le\varepsilon/\sqrt2$.

Conclusion (non-strict):
$$\mathbb E\bigl[(Y-\mathbb E[P])^2\bigr]\le\varepsilon^2.$$

**Truth.** True, by the same decomposition: the variance is at most $\varepsilon^2/2$ and the squared bias is at most $\operatorname{alg1Rem}^2\le\varepsilon^2/2$. This uses $0\le\operatorname{alg1Rem}\le\varepsilon/\sqrt2$, which also forces $\varepsilon\ge0$.

**Non-vacuity.** The witness of entry 12 works.

**Junk values.** As in entry 12: $\mathbb E[P]$ is the junk $0$ if $P$ is not integrable.

**Concerns.** As in entry 12.

### 14. `alg1_not_guaranteed` (theorem)

**Rendering.** Fix a type $\Omega$ with a σ-algebra and a **probability** measure $\mu$. For every real $\alpha$ (no sign condition), every real $\varepsilon>0$ and every real $B$, there exist $P:\Omega\to\mathbb R$ and $P_\ell:\Omega\to\mathbb R$ for $\ell\in\mathbb N$ such that all of the following hold:
- $P$ is $\mu$-integrable, and every $P_\ell$ is $\mu$-integrable;
- $\mathbb E[P_\ell]\to\mathbb E[P]$;
- $\operatorname{alg1Level}(m,\alpha,\varepsilon)=2$, where $m_j=\mathbb E[\Delta P_j]$, $\Delta P_0=P_0$ and $\Delta P_j=P_j-P_{j-1}$.
  - Since $2$ is the smallest candidate, this is equivalent to $\max\{|m_0|\,2^{-2\alpha},|m_1|\,2^{-\alpha},|m_2|\}/(2^\alpha-1)\le\varepsilon/\sqrt2$, with quotient $0$ when $\alpha=0$.
- For every $Y\in L^2(\mu)$ with $\mathbb E[Y]=\mathbb E[P_2]$: $\ B\le\mathbb E\bigl[(Y-\mathbb E[P])^2\bigr]$.

**Truth.** True. A witness:
- $P_0=P_1=P_2=0$, $P_\ell=K$ for $\ell\ge3$, and $P=K$, with $K\ge\sqrt{\max(B,0)}$;
- then $m=(0,0,0,K,0,0,\dots)$, the level-2 test value is $0\le\varepsilon/\sqrt2$, and $\mathbb E[(Y-K)^2]\ge(\mathbb E Y-K)^2=K^2\ge B$.
- Checked for $\alpha\in\{-1,0,0.5,2\}$ (`check_algorithm.py`).

**Non-vacuity.** The only hypothesis is $\varepsilon>0$. The existential holds on every probability space, as shown above.

**Junk values.** For $\alpha\le0$ the level clause is automatic, whatever $m$ is: at $\alpha=0$ by $x/0=0$, and for $\alpha<0$ because the denominator is negative. For $\alpha>0$ the clause is genuine.

**Concerns.**
- $\alpha$ is unconstrained, so part of the quantifier range is degenerate.
- The statement imposes no decay or regularity on the witness. A trivial constant witness with a jump at index 3 suffices.
- The error bound holds for every $Y$ with the prescribed mean.

### 15. `alg1_complexity` (theorem)

**Rendering.** For all reals $\alpha,\beta,\gamma,c_1,c_2,c_3$ and every $N_0\in\mathbb N$, assume:
- $\alpha>0$ and $\gamma>0$;
- $c_1,c_2,c_3>0$;
- $\min(\beta,\gamma)/2\le\alpha$. There is no sign condition on $\beta$.

Then there exists $c_4>0$, depending only on $(\alpha,\beta,\gamma,c_1,c_2,c_3,N_0)$, with the following property. For every real $\varepsilon$ with $0<\varepsilon<e^{-1}$ and all sequences $m,V,C:\mathbb N\to\mathbb R$ such that, for every $\ell$,
- $|m_\ell|\le c_1\,2^{-\alpha\ell}$,
- $0<V_\ell\le c_2\,2^{-\beta\ell}$ (this upper bound is `Vb β c₂ ℓ`),
- $0<C_\ell\le c_3\,2^{\gamma\ell}$ (this upper bound is `Cb γ c₃ ℓ`),

we have
$$\sum_{\ell=0}^{\hat L}N^{(\hat L)}_\ell\,C_\ell\ \le\ c_4\cdot\mathcal B(\alpha,\beta,\gamma,\varepsilon).$$
The symbols are:
- $\hat L=\operatorname{alg1Level}(m,\alpha,\varepsilon)$: the least $L\ge2$ with $\max\{|m_{L-2}|2^{-2\alpha},|m_{L-1}|2^{-\alpha},|m_L|\}/(2^\alpha-1)\le\varepsilon/\sqrt2$, or $0$ if none.
- $N^{(\hat L)}_\ell=\operatorname{alg1Samples}(N_0,V,C,\varepsilon,\hat L,\ell)$: the recursion $N^{(0)}_\ell=N_0\mathbf 1[\ell\le2]$ and $N^{(L+1)}_\ell=\max\bigl(N^{(L)}_\ell,\mathbf 1[2\le L+1\wedge\ell\le L+1]\lceil(2/\varepsilon^2)\sqrt{V_\ell/C_\ell}\sum_{j=0}^{L+1}\sqrt{V_jC_j}\rceil_{\mathbb N}\bigr)$.
- $\mathcal B$ is `complexityBound`:
$$\mathcal B(\alpha,\beta,\gamma,\varepsilon)=\begin{cases}\varepsilon^{-2},&\gamma<\beta,\\ \varepsilon^{-2}(\ln\varepsilon)^2,&\beta=\gamma,\\ \varepsilon^{-2-(\gamma-\beta)/\alpha},&\gamma>\beta.\end{cases}$$

**Truth.** True.
- **Level bound.** By entry 9, $2\le\hat L$ and $2^{\alpha\hat L}\le A_0/\varepsilon$ for a constant $A_0$.
- **Allocation.** By the derived form of entry 6, $N^{(\hat L)}_\ell\le N_0\mathbf 1[\ell\le2]+1+(2/\varepsilon^2)\sqrt{V_\ell/C_\ell}\,S_{\hat L}$. So
$$\text{sum}\le N_0(C_0+C_1+C_2)+\sum_{\ell\le\hat L}C_\ell+(2/\varepsilon^2)S_{\hat L}^2.$$
- **Growth of the terms.**
  - $\sum_{\ell\le\hat L}C_\ell\lesssim2^{\gamma\hat L}\lesssim\varepsilon^{-\gamma/\alpha}$.
  - $S_{\hat L}\lesssim1$ if $\gamma<\beta$; $S_{\hat L}\lesssim\hat L+1\lesssim|\ln\varepsilon|$ if $\beta=\gamma$; $S_{\hat L}\lesssim2^{(\gamma-\beta)\hat L/2}$ if $\gamma>\beta$.
- **Role of the hypothesis.** $\min(\beta,\gamma)\le2\alpha$ is exactly what makes $\varepsilon^{-\gamma/\alpha}\lesssim\mathcal B$ in each case. $\varepsilon<e^{-1}$ gives $(\ln\varepsilon)^2>1$, so $\mathcal B\ge\varepsilon^{-2}\ge e^2$ absorbs the constants. Negative $\beta$ is covered by the case $\gamma>\beta$.
- **Numerics** (`check_complexity*.py`).
  - Tested 8 parameter sets, including $\beta<0$ and the boundary cases $\alpha=\min(\beta,\gamma)/2$, with extremal and random admissible $(m,V,C)$.
  - In every set, $\text{sum}/\mathcal B$ stays bounded as $\varepsilon\to0$.
  - In the $(\alpha,\beta,\gamma)=(1,-1,1)$ case the ratio is exactly $16\cdot4^{\text{frac}}<64$, where frac is the ceiling offset. So its slow drift is periodic, not growth.

**Non-vacuity.** Take, for example, $\alpha=\beta=\gamma=c_i=1$, $m=0$, $V_\ell=2^{-\ell}$ and $C_\ell=2^{\ell}$.

**Junk values.** None triggered. $\varepsilon>0$, so the real powers are genuine; $\alpha>0$, so there is no division by $0$; $\hat L$ is the genuine least level; all ceilings have positive arguments.

**Concerns.**
- $\beta$ has no sign condition; the statement remains true for $\beta\le0$.
- The bounded quantity is $\sum_{\ell\le\hat L}N^{(\hat L)}_\ell C_\ell$, formed from the final allocation. Since the recursion takes a max at each stage, this final allocation dominates all earlier stages.
- $m$ is an arbitrary sequence, unrelated to $V$ and $C$.
- Only upper bounds are imposed on $V$ and $C$.

---

## Part B — declarations from `MlmcLean.MLQMC`

Notation: $v:\mathbb N\to\mathbb N\to\mathbb R$ is written $v_{\ell,j}$, and $C:\mathbb N\to\mathbb R$ is written $C_\ell$.

### 16. `mlqmcRatio` (definition)

**Rendering.** For $v$, $C$ and $\ell,k\in\mathbb N$:
$$\operatorname{mlqmcRatio}(v,C,\ell,k)=\frac{v_{\ell,k}}{2^{k}\,C_\ell},$$
where $2^k$ is the natural power, and the value is $0$ if $C_\ell=0$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** $x/0=0$ when $C_\ell=0$.

**Concerns.** None.

### 17. `mlqmcLevel` (definition)

**Rendering.** For $v$, $C$, $L\in\mathbb N$ and a counter $k:\mathbb N\to\mathbb N$, the output is an index $\ell^\ast\in\{0,\dots,L\}$ such that
$$\frac{v_{\ell',k_{\ell'}}}{2^{k_{\ell'}}C_{\ell'}}\le\frac{v_{\ell^\ast,k_{\ell^\ast}}}{2^{k_{\ell^\ast}}C_{\ell^\ast}}\quad\text{for all }\ell'\in\{0,\dots,L\}.$$
It is obtained by the global choice function from the existence of a maximiser over the non-empty set $\{0,\dots,L\}$. When several indices attain the maximum, which one is returned is unspecified, though it is a fixed function of $(v,C,L,k)$.

**Truth / Non-vacuity.** Not applicable; the choice is always possible.

**Junk values.** Ratios use $x/0=0$ if some $C_\ell=0$.

**Concerns.** Tie-breaking is unspecified.

### 18. `mlqmcStep` (definition)

**Rendering.** $\operatorname{mlqmcStep}(v,C,L,k)$ is the counter $k'$ given by
- $k'_{\ell^\ast}=k_{\ell^\ast}+1$, where $\ell^\ast=\operatorname{mlqmcLevel}(v,C,L,k)$ (entry 17);
- $k'_\ell=k_\ell$ for $\ell\ne\ell^\ast$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** Inherited from entry 17.

**Concerns.** None.

### 19. `mlqmcIter` (definition)

**Rendering.** $\operatorname{mlqmcIter}(v,C,L,k,n)$ is the result of applying $k\mapsto\operatorname{mlqmcStep}(v,C,L,k)$ to $k$ exactly $n$ times. For $n=0$ it is $k$. Each step adds $1$ to $k$ at an index in $\{0,\dots,L\}$ that maximises $v_{\ell,k_\ell}/(2^{k_\ell}C_\ell)$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** None beyond entry 17.

**Concerns.** None.

### 20. `mlqmc_inner_terminates` (theorem)

**Rendering.**
- Data: $v:\mathbb N\to\mathbb N\to\mathbb R$ and $C:\mathbb N\to\mathbb R$.
- Hypotheses:
  - $v_{\ell,j}>0$ for all $\ell,j$;
  - $C_\ell>0$ for all $\ell$;
  - for each $\ell$, $v_{\ell,j}\to0$ as $j\to\infty$.

Then for every $L\in\mathbb N$, every initial counter $k^0:\mathbb N\to\mathbb N$ and every real $\theta>0$, there exists $n\in\mathbb N$ with
$$\sum_{\ell=0}^{L}v_{\ell,\,k^{(n)}_\ell}\le\theta,\qquad k^{(n)}=\operatorname{mlqmcIter}(v,C,L,k^0,n).$$
Here $k^{(n)}$ is the result of $n$ greedy steps, each adding $1$ to $k$ at an index $\ell\in\{0,\dots,L\}$ that maximises $v_{\ell,k_\ell}/(2^{k_\ell}C_\ell)$, with unspecified tie-breaking.

**Truth.** True. Suppose some index $\ell_0\le L$ were incremented only finitely often.
- Its ratio would eventually be a constant $r_0>0$.
- The indices incremented infinitely often have counters tending to $\infty$, so their ratios tend to $0$ and eventually drop below $r_0$. They could then no longer be selected, which is a contradiction.
- Hence every index $\le L$ is incremented infinitely often, every $v_{\ell,k^{(n)}_\ell}\to0$, and the finite sum tends to $0<\theta$.

The argument is independent of tie-breaking. Simulated with 4 families, min and max tie-breaking, and random $k^0$ (`check_mlqmc_impl.py`).

**Non-vacuity.** Take $v_{\ell,j}=2^{-j}$ and $C=1$.

**Junk values.** None, because $C>0$.

**Concerns.** The statement is purely existential, with no bound on $n$. For slowly decaying $v$, for example $v_{\ell,j}\sim1/\log j$, the required $n$ is astronomically large.

### 21. `mlqmcInner` (definition)

**Rendering.** For $v$, $C$, $L$, real $\theta$ and a counter $k$, write $k^{(n)}=\operatorname{mlqmcIter}(v,C,L,k,n)$.
- If there is an $n$ with $\sum_{\ell=0}^{L}v_{\ell,k^{(n)}_\ell}\le\theta$, then $\operatorname{mlqmcInner}(v,C,L,\theta,k)=k^{(n^\ast)}$, where $n^\ast$ is the **least** such $n$.
- Otherwise the value is $k$ itself.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** The fallback "return $k$ unchanged" applies when no $n$ works.

**Concerns.** None.

### 22. `mlqmcState` (definition)

**Rendering.** For $v$, $C$ and real $\theta$, the counters $s^{(L)}=\operatorname{mlqmcState}(v,C,\theta,L):\mathbb N\to\mathbb N$ are defined by recursion on $L$:
- $s^{(0)}=s^{(1)}=0$, the zero counter;
- $s^{(2)}=\operatorname{mlqmcInner}(v,C,2,\theta,0)$;
- $s^{(L)}=\operatorname{mlqmcInner}(v,C,L,\theta,s^{(L-1)})$ for $L\ge3$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** None. $L=0,1$ give the zero counter by definition.

**Concerns.** None.

### 23. `mlqmc_algorithm` (theorem)

**Rendering.**
- Data: $m:\mathbb N\to\mathbb R$; real $\alpha,\varepsilon$; $v$ and $C$, which are implicit arguments.
- Hypotheses:
  - $m_\ell\to0$;
  - $\alpha>0$ and $\varepsilon>0$;
  - $v_{\ell,j}>0$ for all $\ell,j$;
  - $C_\ell>0$ for all $\ell$;
  - $v_{\ell,j}\to0$ as $j\to\infty$ for each $\ell$.

Let $\hat L=\operatorname{alg1Level}(m,\alpha,\varepsilon)$: the least $L\ge2$ with $\max\{|m_{L-2}|2^{-2\alpha},|m_{L-1}|2^{-\alpha},|m_L|\}/(2^\alpha-1)\le\varepsilon/\sqrt2$, or $0$ if none. Then all three hold:
1. $2\le\hat L$;
2. $\max\{|m_{\hat L-2}|2^{-2\alpha},|m_{\hat L-1}|2^{-\alpha},|m_{\hat L}|\}/(2^\alpha-1)\le\varepsilon/\sqrt2$;
3. $\sum_{\ell=0}^{\hat L}v_{\ell,\,s_\ell}\le\varepsilon^2/2$, where $s=\operatorname{mlqmcState}(v,C,\varepsilon^2/2,\hat L)$ (entry 22, with $\theta=\varepsilon^2/2$).

**Truth.** True.
- Parts 1 and 2 follow from entry 8 and `Nat.find`.
- Part 3: $\hat L\ge2$, so $s=\operatorname{mlqmcInner}(v,C,\hat L,\varepsilon^2/2,\cdot)$. By entry 20, an admissible $n$ exists, so the least one is used and satisfies the bound.
- Simulated in `check_mlqmc_impl.py`.

**Non-vacuity.** Take $m=0$, $v_{\ell,j}=2^{-j}$ and $C=1$.

**Junk values.** None; the level exists.

**Concerns.** The sequence $m$ and the data $(v,C)$ are unrelated. The conclusion is a conjunction of facts about two independent deterministic procedures.

### 24. `mlqmc_mse` (theorem)

**Rendering.**
- Data:
  - a type $\Omega$ with a σ-algebra and a **probability** measure $\mu$;
  - implicit $v:\mathbb N\to\mathbb N\to\mathbb R$ and $C:\mathbb N\to\mathbb R$;
  - $Y,P:\Omega\to\mathbb R$ and $P_\ell:\Omega\to\mathbb R$ for $\ell\in\mathbb N$;
  - real $\alpha,\varepsilon$ and natural $k$.
- Notation: $\mathbb E[f]=\int f\,d\mu$ (and $0$ if $f$ is not integrable), $\Delta P_0=P_0$, $\Delta P_j=P_j-P_{j-1}$, $m_j=\mathbb E[\Delta P_j]$, and $\hat L=\operatorname{alg1Level}(m,\alpha,\varepsilon)$.
  - $\hat L$ is the least $L\ge2$ with $\max\{|m_{L-2}|2^{-2\alpha},|m_{L-1}|2^{-\alpha},|m_L|\}/(2^\alpha-1)\le\varepsilon/\sqrt2$, or $0$ if none.
- Hypotheses:
  - $\alpha>0$ and $\varepsilon>0$;
  - $v_{\ell,j}>0$ for all $\ell,j$;
  - $C_\ell>0$ for all $\ell$;
  - $v_{\ell,j}\to0$ as $j\to\infty$ for each $\ell$;
  - $m_\ell\to0$;
  - $k\le2$;
  - $Y\in L^2(\mu)$;
  - every $P_\ell$ is integrable;
  - $\mathbb E[P_\ell]\to\mathbb E[P]$, where $P$ is not assumed integrable;
  - for every natural $\ell>\hat L$: $\ |m_\ell|\le|m_{\hat L\ominus k}|\cdot2^{-\alpha(\ell-(\hat L\ominus k))}$;
  - $\mathbb E[Y]=\mathbb E[P_{\hat L}]$;
  - the variance equality
  $$\operatorname{Var}_\mu(Y)=\sum_{\ell=0}^{\hat L}v_{\ell,\,s_\ell},\qquad s=\operatorname{mlqmcState}(v,C,\varepsilon^2/2,\hat L).$$
    Here $s^{(0)}=s^{(1)}=0$, $s^{(2)}=\operatorname{mlqmcInner}(v,C,2,\theta,0)$ and $s^{(L)}=\operatorname{mlqmcInner}(v,C,L,\theta,s^{(L-1)})$ with $\theta=\varepsilon^2/2$, as in entries 17–22.
- Conclusion:
$$\mathbb E\bigl[(Y-\mathbb E[P])^2\bigr]\le\varepsilon^2.$$

**Truth.** True.
- By entry 23, $\hat L\ge2\ge k$, which makes the $\ominus$ an honest subtraction. Also $\operatorname{alg1Rem}(m,\alpha,\hat L)\le\varepsilon/\sqrt2$ and $\sum v_{\ell,s_\ell}\le\varepsilon^2/2$, so $\operatorname{Var}(Y)\le\varepsilon^2/2$.
- Entry 13 then applies with $L=\hat L$.

**Non-vacuity.** Jointly satisfiable.
- Take $\Omega=\{0,1\}$ with the uniform measure, $P=P_\ell=0$, so $m=0$ and $\hat L=2$, with the decay hypothesis reading $0\le0$.
- Take $v_{\ell,j}=2^{-j}$, $C=1$, and $Y=\pm b$ with $b^2=\sum_{\ell\le2}v_{\ell,s_\ell}$.
- On a one-point $\Omega$ the hypotheses are unsatisfiable, since the variance is $0$ while the sum is $>0$. That is fine for a universally quantified $\Omega$.

**Junk values.**
- $\mathbb E[P]$ is the junk $0$ if $P$ is not integrable.
- $\hat L\ominus k$ never truncates under the hypotheses.
- The variance is genuine.

**Concerns.**
- The hypothesis $m_\ell\to0$ is redundant: it follows from integrability of the $P_\ell$ and convergence of $\mathbb E[P_\ell]$.
- `hvar` is an **equality** between $\operatorname{Var}(Y)$ and the $v$-sum; the proof only needs $\le$.
- Apart from `hvar`, nothing links $v$ and $C$ to $Y$ or to the $P_\ell$.
- The decay hypothesis is anchored at the index $\hat L$ produced by `alg1Level` itself.
- There is no hypothesis $k\le\hat L$, but it is implied.

---

## Part C — declarations from `MlmcLean.Implementation`

### 25. `powerSum_variance_eq` (theorem)

**Rendering.** For every $x:\mathbb N\to\mathbb R$ and every $N\in\mathbb N$ with $N>0$:
$$\frac1N\sum_{n=0}^{N-1}x_n^2-\Bigl(\frac1N\sum_{n=0}^{N-1}x_n\Bigr)^2=\frac1N\sum_{n=0}^{N-1}\Bigl(x_n-\frac1N\sum_{k=0}^{N-1}x_k\Bigr)^2.$$

**Truth.** True. This is the standard identity. Checked exactly with `Fraction`s on 500 random cases.

**Non-vacuity.** Take $N=1$.

**Junk values.** None, since $N>0$.

**Concerns.** None.

### 26. `powerSum_variance_nonneg` (theorem)

**Rendering.** For every $x:\mathbb N\to\mathbb R$ and every $N>0$:
$$0\le\frac1N\sum_{n=0}^{N-1}x_n^2-\Bigl(\frac1N\sum_{n=0}^{N-1}x_n\Bigr)^2.$$

**Truth.** True, by entry 25.

**Non-vacuity.** Take $N=1$.

**Junk values.** None.

**Concerns.** None.

### 27. `powerSum_variance_mean` (theorem)

**Rendering.**
- Data:
  - types $\Omega,\Omega_0$ with σ-algebras;
  - a **probability** measure $\mu$ on $\Omega$ (an explicit assumption);
  - a measure $\nu$ on $\Omega_0$, with no stated assumption;
  - maps $\omega_n:\Omega\to\Omega_0$ for $n\in\mathbb N$;
  - $X:\Omega_0\to\mathbb R$ and $N\in\mathbb N$.
- Hypotheses:
  - each $\omega_n$ is measurable with image measure $\mu\circ\omega_n^{-1}=\nu$;
  - the family $(\omega_n)_{n\in\mathbb N}$ is mutually independent under $\mu$;
  - $X$ is measurable and $X\in L^2(\nu)$;
  - $N>0$.
- Conclusion:
$$\int_\Omega\Bigl[\frac1N\sum_{n=0}^{N-1}X(\omega_n(x))^2-\Bigl(\frac1N\sum_{n=0}^{N-1}X(\omega_n(x))\Bigr)^2\Bigr]d\mu(x)=\Bigl(1-\frac1N\Bigr)\operatorname{Var}_\nu(X).$$

**Truth.** True. $\mathbb E[\text{mean of squares}]=\mathbb E_\nu X^2$, and $\mathbb E[(\text{mean})^2]=\operatorname{Var}_\nu(X)/N+(\mathbb E_\nu X)^2$ by pairwise independence and identical laws. Checked exactly by enumeration for a 4-point law and $N=1,\dots,4$.

**Non-vacuity.** Take $\Omega_0=\{0,1\}$ with a Bernoulli $\nu$, $\Omega=\Omega_0^{\mathbb N}$ with the product measure, and $\omega_n$ the coordinate maps. A trivial alternative is a one-point $\Omega_0$.

**Junk values.** None. The integrand is integrable because $X\circ\omega_n\in L^2(\mu)$, and the variance is genuine because $X\in L^2(\nu)$. $\nu$ is automatically a probability measure, since $\nu=\mu\circ\omega_0^{-1}$.

**Concerns.** None.

### 28. `floorEst` (definition)

**Rendering.** For $x:\mathbb N\to\mathbb R$ and $r\in\mathbb R$, the sequence $F=\operatorname{floorEst}(x,r)$ is
$$F_0=x_0,\qquad F_1=x_1,\qquad F_{\ell+2}=\max\bigl(x_{\ell+2},\ r\,F_{\ell+1}\bigr).$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.** None.

**Concerns.** None.

### 29. `le_floorEst` (theorem)

**Rendering.** For every $x:\mathbb N\to\mathbb R$, every $r\in\mathbb R$ and every $\ell\in\mathbb N$: $\ x_\ell\le F_\ell$, where $F$ is as in entry 28.

**Truth.** True: equality holds for $\ell\le1$, and for larger $\ell$ it is the left argument of the $\max$.

**Non-vacuity.** There are no hypotheses.

**Junk values.** None.

**Concerns.** Packet artefact: proof text appears before `:= sorry`. The statement itself is unaffected.

### 30. `floorEst_ge_extrapolation` (theorem)

**Rendering.** For every $x:\mathbb N\to\mathbb R$, every $r\in\mathbb R$ and every $\ell\in\mathbb N$: $\ r\,F_{\ell+1}\le F_{\ell+2}$, with $F=\operatorname{floorEst}(x,r)$ as in entry 28.

**Truth.** True: this is the right argument of the $\max$.

**Non-vacuity.** There are no hypotheses.

**Junk values.** None.

**Concerns.** None.

### 31. `floorEst_le` (theorem)

**Rendering.**
- Data: $x,y:\mathbb N\to\mathbb R$ and $r\in\mathbb R$.
- Hypotheses:
  - $r\ge0$;
  - $x_\ell\le y_\ell$ for every $\ell$;
  - $r\,y_{\ell+1}\le y_{\ell+2}$ for every $\ell$.
- Conclusion: $F_\ell\le y_\ell$ for every $\ell$, where $F=\operatorname{floorEst}(x,r)$, i.e. $F_0=x_0$, $F_1=x_1$ and $F_{\ell+2}=\max(x_{\ell+2},rF_{\ell+1})$.

**Truth.** True, by induction: $rF_{\ell+1}\le ry_{\ell+1}\le y_{\ell+2}$, using $r\ge0$.

**Non-vacuity.** Take $x=y=0$ and $r=1$.

**Junk values.** None.

**Concerns.** Packet artefact, as in entry 29. Together, entries 29–31 say that $F$ is the least sequence that is $\ge x$ and satisfies $rF_{\ell+1}\le F_{\ell+2}$ (for $r\ge0$).

### 32. `lsSlope` (definition)

**Rendering.** For an arbitrary index type $\iota$, a finite set $s\subseteq\iota$ and $t,y:\iota\to\mathbb R$, let $|s|$ be the cardinality, $\bar t=\frac1{|s|}\sum_{j\in s}t_j$ and $\bar y=\frac1{|s|}\sum_{j\in s}y_j$. Both means are $0$ when $s=\emptyset$. Then
$$\operatorname{lsSlope}(s,t,y)=\frac{\sum_{i\in s}(t_i-\bar t)(y_i-\bar y)}{\sum_{i\in s}(t_i-\bar t)^2},$$
and the value is $0$ when the denominator is $0$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** When $s=\emptyset$, or when $t$ is constant on $s$, the value is $0$ (confirmed numerically).

**Concerns.** None.

### 33. `lsIntercept` (definition)

**Rendering.** With the notation of entry 32:
$$\operatorname{lsIntercept}(s,t,y)=\bar y-\operatorname{lsSlope}(s,t,y)\cdot\bar t.$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.** Inherited from entry 32.

**Concerns.** None.

### 34. `lsFit_le` (theorem)

**Rendering.**
- Data: a type $\iota$, a finite $s\subseteq\iota$, and $t,y:\iota\to\mathbb R$.
- Hypothesis: $\sum_{i\in s}(t_i-\bar t)^2\ne0$, where $\bar t=\frac{1}{|s|}\sum_{j\in s}t_j$. This is equivalent to $t$ not being constant on $s$, and it forces $|s|\ge2$.
- Conclusion: for all $a,b\in\mathbb R$,
$$\sum_{i\in s}\bigl(y_i-(\hat\beta\,t_i+\hat a)\bigr)^2\le\sum_{i\in s}\bigl(y_i-(a\,t_i+b)\bigr)^2,$$
where $\hat\beta=\operatorname{lsSlope}(s,t,y)$ and $\hat a=\operatorname{lsIntercept}(s,t,y)$ (entries 32–33).

**Truth.** True: these are the ordinary least-squares minimisers. Checked exactly on several thousand random comparisons: up to 500 random instances with 10 competing pairs $(a,b)$ each, skipping instances where $t$ is constant.

**Non-vacuity.** Take $s=\{0,1\}$ and $t=\mathrm{id}$.

**Junk values.** The hypothesis excludes the zero-denominator case.

**Concerns.** None.

### 35. `lsSlope_affine` (theorem)

**Rendering.** For a type $\iota$, a finite $s\subseteq\iota$, $t:\iota\to\mathbb R$ and $c,a\in\mathbb R$ with $\sum_{i\in s}(t_i-\bar t)^2\ne0$:
$$\operatorname{lsSlope}\bigl(s,t,(c+a\,t_i)_{i}\bigr)=a.$$

**Truth.** True: $y_i-\bar y=a(t_i-\bar t)$. Checked exactly.

**Non-vacuity.** Take $s=\{0,1\}$ and $t=\mathrm{id}$.

**Junk values.** Excluded by the hypothesis.

**Concerns.** None.

### 36. `lsSlope_log_geometric` (theorem)

**Rendering.**
- Data: a finite $s\subseteq\mathbb N$, natural numbers $i,j$, and real $c,\alpha$.
- Hypotheses: $i\in s$, $j\in s$, $i\ne j$, and $c>0$. There is no condition on $\alpha$.
- Conclusion:
$$\operatorname{lsSlope}\Bigl(s,\ (\ell)_{\ell},\ \bigl(\log_2(c\cdot2^{-\alpha\ell})\bigr)_{\ell}\Bigr)=-\alpha,$$
with $\operatorname{lsSlope}$ as in entry 32. The regressor is $t_\ell=\ell$, viewed as a real number.

**Truth.** True: $\log_2(c\,2^{-\alpha\ell})=\log_2c-\alpha\ell$ is affine in $\ell$, and two distinct points make $t$ non-constant. Checked numerically.

**Non-vacuity.** Take $s=\{0,1\}$ and $c=1$.

**Junk values.** None, since $c>0$ makes the argument of $\log_2$ positive.

**Concerns.** None. $i$ and $j$ only witness $|s|\ge2$.

### 37. `gaussian_tail_three` (theorem)

**Rendering.** For the standard normal distribution $\mathcal N(0,1)$ on $\mathbb R$ (mean $0$, variance $1$):
$$\mathcal N(0,1)\bigl(\{x\in\mathbb R:\ |x|>3\}\bigr)<0.003=\tfrac{3}{1000}.$$

**Truth.** True: the probability is $\operatorname{erfc}(3/\sqrt2)=0.0026997961\ldots<0.003$.

**Non-vacuity.** Not applicable; the statement is closed.

**Junk values.** None. The literal $0.003$ is exactly $3/1000$ (Convention 19).

**Concerns.** None. The margin is about 10%.

### 38. `consistency_check_gaussian` (theorem)

**Rendering.**
- Data:
  - a type $\Omega$ with a σ-algebra and a **probability** measure $\mu$;
  - $a,b,c:\Omega\to\mathbb R$;
  - $v\in\mathbb R_{\ge0}$.
- Hypotheses:
  - $a,b,c\in L^2(\mu)$;
  - $v\ne0$;
  - $a-b+c$ is $\mu$-a.e. measurable and has law $\mathcal N(0,v)$ under $\mu$, where $v$ is the **variance**.
- Notation: $\sigma_a=\sqrt{\operatorname{Var}_\mu(a)}$, and similarly $\sigma_b$, $\sigma_c$.
- Conclusion:
$$\mu\bigl(\{\omega:\ 3(\sigma_a+\sigma_b+\sigma_c)<|a(\omega)-b(\omega)+c(\omega)|\}\bigr)<0.003.$$
  The measure is taken as a real number. If the set is not measurable, the outer measure is used.

**Truth.** True.
- By the triangle inequality in $L^2$ applied to the centred variables, $\sqrt v=\sigma_{a-b+c}\le\sigma_a+\sigma_b+\sigma_c$.
- Hence the event is contained, up to a null set, in $\{|a-b+c|>3\sqrt v\}$, whose probability is $\mathcal N(0,1)(|x|>3)\approx0.0027<0.003$.

**Non-vacuity.** Take $\Omega=\mathbb R$, $\mu=\mathcal N(0,1)$, $a=\mathrm{id}$, $b=c=0$ and $v=1$.

**Junk values.** None that changes the meaning. The variances are genuine because $a,b,c\in L^2$. If one of them were not in $L^2$, its variance would be the junk value $0$; the $L^2$ hypotheses prevent this.

**Concerns.**
- The hypothesis $v\ne0$ is superfluous. With $v=0$ we get $a-b+c=0$ a.s., and the event is null.
- The threshold uses $\sigma_a+\sigma_b+\sigma_c$, which is at least the standard deviation of $a-b+c$. The event is therefore no larger than the "$3\sigma$" event for $a-b+c$.

### 39. `consistency_check_chebyshev` (theorem)

**Rendering.**
- Data: a type $\Omega$ with a σ-algebra and a **probability** measure $\mu$, and $a,b,c:\Omega\to\mathbb R$.
- Hypotheses:
  - $a,b,c\in L^2(\mu)$;
  - $\int(a-b+c)\,d\mu=0$;
  - $S:=\sigma_a+\sigma_b+\sigma_c>0$, where $\sigma_\bullet=\sqrt{\operatorname{Var}_\mu(\bullet)}$.
- Conclusion:
$$\mu\bigl(\{\omega:\ 3S\le|a(\omega)-b(\omega)+c(\omega)|\}\bigr)\le\frac19.$$
  The measure is taken as a real number, using the outer measure if the set is not measurable.

**Truth.** True, by Chebyshev: $\mathbb E[(a-b+c)^2]=\operatorname{Var}(a-b+c)\le S^2$, so the probability is $\le S^2/(9S^2)$.

The bound is attained. Take $a$ with law $\{-3,0,3\}$ and weights $\{1/18,8/9,1/18\}$, and $b=c=0$. Then $S=1$ and the probability is exactly $1/9$ (checked exactly).

**Non-vacuity.** Take $\Omega=\mathbb R$, $\mu=\mathcal N(0,1)$, $a=\mathrm{id}$ and $b=c=0$.

**Junk values.** None. The $L^2$ hypotheses make the variances genuine.

**Concerns.** None. The condition $S>0$ is necessary: with $S=0$ the event is all of $\Omega$.

### 40. `sampleVariance_relative_sd_le_iff` (theorem)

**Rendering.** For all real $\kappa$ and $r$ with $r>0$, and every $N\in\mathbb N$ with $N>0$:
$$\sqrt{\frac{\kappa-1}{N}}\le r\iff\frac{\kappa-1}{r^2}\le N,$$
where $\sqrt{x}=0$ for $x<0$.

**Truth.** True for **all** real $\kappa$.
- If $\kappa\ge1$, both sides are equivalent to $\kappa-1\le r^2N$.
- If $\kappa<1$, the left side is $0\le r$ by the square-root convention, and the right side is a negative number $\le N$. Both are true.
- 200,000 random checks, including $\kappa<1$, gave 0 mismatches.

**Non-vacuity.** Take $r=1$ and $N=1$.

**Junk values.** For $\kappa<1$ the left side uses $\sqrt{\text{negative}}=0$. The equivalence still holds, because both sides are true.

**Concerns.** This is a pure real-number statement; no random variables appear.

### 41. `integral_ternary` (theorem)

**Rendering.** Let $\Omega$ have a σ-algebra and a **probability** measure $\mu$, and let $X:\Omega\to\mathbb R$ be measurable with $X(\omega)\in\{-1,0,1\}$ for every $\omega$. Then
$$\int X\,d\mu=\mu(\{X=1\})-\mu(\{X=-1\}).$$

**Truth.** True.

**Non-vacuity.** Take $X=0$.

**Junk values.** None: $X$ is bounded and measurable on a probability space.

**Concerns.** None.

### 42. `measureReal_ternary_zero` (theorem)

**Rendering.** Under the same data and hypotheses as entry 41 ($\mu$ a probability measure; $X$ measurable with values in $\{-1,0,1\}$ everywhere):
$$\mu(\{X=0\})=1-\mu(\{X=1\})-\mu(\{X=-1\}).$$

**Truth.** True: the three sets form a measurable partition.

**Non-vacuity.** Take $X=0$.

**Junk values.** None.

**Concerns.** None.

### 43. `prob_all_zero` (theorem)

**Rendering.**
- Data:
  - types $\Omega,\Omega_0$ with σ-algebras;
  - measures $\mu$ on $\Omega$ and $\nu$ on $\Omega_0$, with **no** stated finiteness or probability assumption;
  - maps $\omega_n:\Omega\to\Omega_0$ for $n\in\mathbb N$;
  - $X:\Omega_0\to\mathbb R$ and $N\in\mathbb N$.
- Hypotheses:
  - each $\omega_n$ is measurable with $\mu\circ\omega_n^{-1}=\nu$;
  - $(\omega_n)_{n\in\mathbb N}$ is mutually independent under $\mu$;
  - $X$ is measurable.
- Conclusion:
$$\mu\bigl(\{x:\ X(\omega_n(x))=0\text{ for all }n\in\{0,\dots,N-1\}\}\bigr)=\nu(\{X=0\})^{N},$$
  with both measures taken as real numbers.

**Truth.** True.
- Mutual independence, taken over the empty index set, forces $\mu(\Omega)=1$ (Mathlib: `iIndepFun.isProbabilityMeasure`). Then $\nu=\mu\circ\omega_0^{-1}$ is also a probability measure.
- The identity is independence together with identical laws. For $N=0$ both sides equal $1$.
- Checked exactly by enumeration.

**Non-vacuity.** Take a product space with coordinate maps, as in entry 27.

**Junk values.** None.

**Concerns.** The probability assumptions are implicit, being forced by the independence hypothesis, rather than stated. This is harmless.

### 44. `powerSum_variance_of_zero` (theorem)

**Rendering.** For every $x:\mathbb N\to\mathbb R$ and every $N\in\mathbb N$ (including $N=0$), if $x_n=0$ for all $n\in\{0,\dots,N-1\}$, then
$$\frac1N\sum_{n=0}^{N-1}x_n^2-\Bigl(\frac1N\sum_{n=0}^{N-1}x_n\Bigr)^2=0.$$

**Truth.** True: both sums are $0$.

**Non-vacuity.** Take $x=0$.

**Junk values.** For $N=0$ the expression is $0/0-(0/0)^2=0$ by $x/0=0$. The result is still consistent.

**Concerns.** None.

### 45. `mlqmc_doubling_level` (theorem)

**Rendering.**
- Data: a type $\iota$, a finite non-empty $s\subseteq\iota$, real-valued $V,N,C:\iota\to\mathbb R$ (here $N$ is real-valued), and a real $f$.
- Hypothesis: $f>0$.
- Conclusion: both of the following hold.
  1. There is $\ell\in s$ with $\dfrac{V_k}{N_kC_k}\le\dfrac{V_\ell}{N_\ell C_\ell}$ for all $k\in s$.
  2. For every $\ell\in s$:
  $$\Bigl(\forall k\in s:\ \frac{fV_k}{N_kC_k}\le\frac{fV_\ell}{N_\ell C_\ell}\Bigr)\iff\Bigl(\forall k\in s:\ \frac{V_k}{N_kC_k}\le\frac{V_\ell}{N_\ell C_\ell}\Bigr).$$

  All quotients are $0$ when the denominator is $0$.

**Truth.** True. Part 1: a finite non-empty set has a maximiser. Part 2: $fV_k/(N_kC_k)=f\cdot\bigl(V_k/(N_kC_k)\bigr)$, and multiplying by $f>0$ preserves $\le$.

**Non-vacuity.** Take $s=\{0\}$ and $f=1$.

**Junk values.** Quotients with a zero denominator are $0$; the statement still holds.

**Concerns.**
- The statement is near-tautological. Part 1 does not involve $f$.
- $f$ is an arbitrary positive number, not a specific constant.

---

## Part D — supporting definitions (trailing section of the packet)

### 46. `optimalN` (definition)

**Rendering.** For an index type $\iota$, a finite $s\subseteq\iota$, $V,C:\iota\to\mathbb R$, $\tau\in\mathbb R$ and $i\in\iota$:
$$\operatorname{optimalN}(s,V,C,\tau,i)=\bigl\lceil\operatorname{lagrangeN}(s,V,C,\tau,i)\bigr\rceil_{\mathbb N}=\Bigl\lceil\tau^{-1}\sqrt{V_i/C_i}\ \sum_{j\in s}\sqrt{V_jC_j}\Bigr\rceil_{\mathbb N}.$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.**
- Non-positive argument: the value is $0$.
- $\tau=0$: $\tau^{-1}=0$.
- Negative radicands: the square root is $0$.
- $C_i=0$: $V_i/C_i=0$.

**Concerns.** None.

### 47. `levelDiff` (definition)

**Rendering.** For $P_\ell:\Omega_0\to\mathbb R$ ($\ell\in\mathbb N$):
$$\operatorname{levelDiff}(P)_0=P_0,\qquad\operatorname{levelDiff}(P)_{\ell+1}=P_{\ell+1}-P_\ell\ \ \text{(pointwise)}.$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.** None.

**Concerns.** Index $0$ is $P_0$ itself, not a difference. This matters wherever $m_0$ enters `alg1Rem` (entries 11–14 and 24).

### 48. `complexityBound` (definition)

**Rendering.** For real $\alpha,\beta,\gamma,\varepsilon$:
$$\operatorname{complexityBound}(\alpha,\beta,\gamma,\varepsilon)=\begin{cases}\varepsilon^{-2},&\gamma<\beta,\\ \varepsilon^{-2}\,(\ln\varepsilon)^2,&\beta=\gamma,\\ \varepsilon^{-2-(\gamma-\beta)/\alpha},&\text{otherwise }(\gamma>\beta),\end{cases}$$
using real powers.

**Truth / Non-vacuity.** Not applicable.

**Junk values.**
- $\varepsilon\le0$: real power of a non-positive base, and $\ln 0=0$.
- $\alpha=0$: $(\gamma-\beta)/0=0$.

None of these occurs where it is used (entry 15: $0<\varepsilon<e^{-1}$, $\alpha>0$).

**Concerns.** None.

### 49. `Vb` (definition)

**Rendering.** $\operatorname{Vb}(\beta,c_2,\ell)=c_2\cdot2^{-\beta\ell}$ for real $\beta,c_2$ and $\ell\in\mathbb N$, using the real power.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** None.

**Concerns.** None.

### 50. `Cb` (definition)

**Rendering.** $\operatorname{Cb}(\gamma,c_3,\ell)=c_3\cdot2^{\gamma\ell}$ for real $\gamma,c_3$ and $\ell\in\mathbb N$, using the real power.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** None.

**Concerns.** None.

### 51. `levelL` (definition)

**Rendering.** For real $\alpha,c_1,\delta$:
$$\operatorname{levelL}(\alpha,c_1,\delta)=\Bigl\lceil\frac{\log_2(c_1/\delta)}{\alpha}\Bigr\rceil_{\mathbb N},$$
where $\log_2x=\ln x/\ln2$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.**
- $\delta=0$: $c_1/0=0$, then $\log_2 0=0$, so the value is $0$.
- $c_1/\delta<0$: $\log_2|c_1/\delta|$ is used.
- $\alpha=0$: division by $0$ gives $0$.
- A negative quotient is truncated to $0$ by $\lceil\cdot\rceil_{\mathbb N}$.

In entry 9 the argument is positive and $\alpha>0$.

**Concerns.** None.

### 52. `lagrangeN` (definition)

**Rendering.** For $s$, $V$, $C$, $\tau$ and $i$ as in entry 46:
$$\operatorname{lagrangeN}(s,V,C,\tau,i)=\tau^{-1}\cdot\sqrt{V_i/C_i}\cdot\sum_{j\in s}\sqrt{V_j\,C_j}.$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.** $0^{-1}=0$, $\sqrt{\text{negative}}=0$, $x/0=0$.

**Concerns.** None.

### 53. `sumSqrtVC` (definition)

**Rendering.** $\operatorname{sumSqrtVC}(s,V,C)=\sum_{i\in s}\sqrt{V_i\,C_i}$, with $\sqrt{\text{negative}}=0$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** $\sqrt{\text{negative}}=0$.

**Concerns.** None.

---

## Numerical checks performed (all in `work_D_g_section3/`)

| Script | What it checks | Result |
|---|---|---|
| `check_algorithm.py` | entries 2, 4, 9, 10 and the witness of 14 | all pass. Entry 4: max excess $2.2\times10^{-16}$ (rounding). Entry 10: max ratio $0.99999999976$. Entry 14: `alg1Level` $=2$ for $\alpha\in\{-1,0,0.5,2\}$ |
| `check_complexity.py` | entry 15, 8 parameter sets incl. $\beta<0$ and boundary cases $\alpha=\min(\beta,\gamma)/2$ | bounded ratios in every set |
| `check_complexity_tail.py`, `check_complexity_tail2.py` | entry 15, case $(1,-1,1)$, $\varepsilon$ down to $10^{-40}$ | ratio $=16\cdot4^{\text{frac}}$, max $63.5<64$ |
| `check_mlqmc_impl.py` | entries 20, 23, 25–27, 34–37, 39, 40, 43 | all pass. Exact `Fraction` checks for 25–27 and 43. $\operatorname{erfc}(3/\sqrt2)=0.002699796$. Chebyshev bound attained |
