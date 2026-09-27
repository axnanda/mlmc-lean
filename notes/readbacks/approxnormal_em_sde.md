# Blind read-back audit: packet B

- **Date:** 2026-09-27
- **Packet:** `packet_B_hg_normals_sde.lean`
- **Declarations audited:** 80 in total:
  - 75 in the three module sections (`ApproxNormal`, `EulerMaruyama`, `SDEExtras`): 16 definitions (one is an `abbrev`) and 59 theorems or lemmas;
  - 5 supporting definitions from the trailing section "definitions used above, from other modules".
- **Work directory (scripts):** `work_B_hg_normals_sde/`

## Rules followed

1. **Sources.** I read only:
   - the packet;
   - the auditor rules (`prove2me_workspace/references/mission_auditor.md`);
   - Mathlib sources under `/home/user/mlmc-lean/.lake/packages/mathlib/Mathlib`;
   - Lean core sources under `/root/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`, to check how instances are resolved.

   I opened nothing else: no project Lean sources, docs, notes, README, PLAN, prove2me, scripts, git history, papers, or web pages.
2. **Names.** No meaning is inferred from declaration or file names. Where the code says less than a reader might expect, the Concerns part says so from the code's side only.
3. **Renderings** follow the read-back principles in `mission_auditor.md`:
   - translate the code, not the intent;
   - list every binder, hypothesis and typeclass;
   - expand project definitions inline;
   - keep the exact strength of every relation and the quantifier order;
   - surface degenerate cases;
   - no judgment inside the rendering.

   The *Truth / Non-vacuity / Junk values / Concerns* parts are the extra assessment this audit asked for.
4. **Section variables.** A section `variable` enters a declaration only if the declaration mentions it. An instance-implicit variable enters once everything it mentions has entered. I applied this rule to decide which section hypotheses (for example `[IsProbabilityMeasure μ]`) each declaration carries.
5. **Numerical checks.** These use pure Python with the standard library only (`fractions`, `random`, `math`), because numpy is not installed. All checks passed; the relevant results are quoted in the entries below.
   - `check_exact.py`: exact rational and integer checks for the coupling identities, counting results, rearrangement, alternating minimisation, dyadic index, bridge identity and the mean-reverting iteration.
   - `check_numeric.py`: quadrature identities, lookup-table mirror, the Euler–Maruyama recursion, the antithetic bounds, an exact finite-distribution check of the splitting formula, the smoothed-CDF bound, and kernel convergence.
   - `check_mlmc.py`: the conclusion of `em_mlmc_theorem1` under worst-case hypotheses.
   - `check_em.py`: the Euler–Maruyama coupling identity and a Brownian witness.
6. **Format.** Markdown with KaTeX, single backslashes (this is a file, not a JSON payload).

---

## Summary

**Overall verdict.**
- **False:** none. Every theorem is judged true.
- **Vacuous:** none. Every theorem has jointly satisfiable hypotheses; witnesses are given in each entry.
- **Junk-dependent in a way that changes meaning:** none. Under its own hypotheses, no theorem's meaning depends on a junk value.
- **Worth a human look:** these are listed in the "Flags" column and discussed under each entry's Concerns. The main ones are `em_mlmc_theorem1` (abstract: all rates are assumed), the three `…_complexity` evaluations, and the non-central `kurtosis` definition.

Abbreviation: `hyp` = hypothesis.

| # | Declaration | Kind | Truth | Flags |
|---|---|---|---|---|
| 1 | `intervalMean` | def | – | junk: $a=b\Rightarrow0$; non-integrable $\Rightarrow0$ |
| 2 | `integral_sq_sub_const` | lemma | true | – |
| 3 | `integral_sq_sub_eq` | thm | true | hyp $a<b$ superfluous |
| 4 | `integral_sq_sub_intervalMean_le` | thm | true | – |
| 5 | `eq_intervalMean_of_integral_sq_sub_le` | thm | true | – |
| 6 | `intervalMean_isLeast` | thm | true | – |
| 7 | `gridPt` | def | – | – |
| 8 | `lutValue` | def | – | junk: non-integrable $\Rightarrow0$ |
| 9 | `lutValue_isLeast` | thm | true | – |
| 10 | `integral_sq_sub_lutValue` | thm | true | – |
| 11 | `sum_integral_sq_sub_lutValue` | thm | true | – |
| 12 | `sum_integral_sq_le_iff` | thm | true | – |
| 13 | `method1_le` | thm | true | – |
| 14 | `method1_le_perm` | thm | true | – |
| 15 | `lutValue_mirror` | thm | true | no integrability hyp (junk-consistent) |
| 16 | `lutValue_upper_half` | thm | true | hyp $1\le d$ redundant |
| 17 | `coupledUniform` | def | – | junk for $D<d$ |
| 18 | `coupledUniform_eq` | thm | true | – |
| 19 | `coupledUniform_mem` | thm | true | – |
| 20 | `midpoint_mem_cell` | thm | true | – |
| 21 | `coupledIndex` | def | – | junk for $D<d$ |
| 22 | `coupledUniform_eq_index` | lemma | true | – |
| 23 | `sum_coupledIndex` | thm | true | – |
| 24 | `card_signed_sums` | thm | true | – |
| 25 | `card_image_add_le` | thm | true | `DecidableEq ι` unused by statement |
| 26 | `choose_two_pow_add_one` | thm | true | – |
| 27 | `sorting_minimises` | thm | true | – |
| 28 | `alternating_min_antitone` | thm | true | – |
| 29 | `alternating_min_eventually_const` | thm | true | only the objective values stabilise |
| 30 | `alternating_eventually_periodic` | thm | true | – |
| 31 | `alternating_stationary` | thm | true | – |
| 32 | `dyadic_index` | thm | true | hyps force $d\ge2$ |
| 33 | `affine_fit_exact` | thm | true | – |
| 34 | `emPath` | def | – | $\sqrt h=0$ for $h\le0$ |
| 35 | `pairAvg` | def | – | – |
| 36 | `emCoarsePath` | def | – | – |
| 37 | `emCoarsePath_two_mul` | thm | true | – |
| 38 | `emCoarsePath_succ` | thm | true | – |
| 39 | `eq_emCoarsePath` | thm | true | – |
| 40 | `stdNormalSeq` | abbrev | – | – |
| 41 | `map_pairSum_gaussian` | thm | true | – |
| 42 | `measurePreserving_pairAvg` | thm | true | – |
| 43 | `emFine` | def | – | – |
| 44 | `emCoarse` | def | – | – |
| 45 | `emCoarse_eq` | thm | true | – |
| 46 | `integral_emCoarse` | thm | true | no integrability hyp ($0=0$ case) |
| 47 | `em_mlmc_theorem1` | thm | true | **abstract**: all three rate conditions are hyps; $a,b,T,S_0,\Phi,P$ otherwise unconstrained; $c_4$ may depend on all data |
| 48 | `variance_sub_le_two_mul` | thm | true | – |
| 49 | `variance_levelDiff_le` | thm | true | – |
| 50 | `variance_sub_le_of_lipschitz` | thm | true | hyp is only a pointwise domination bound |
| 51 | `variance_levelDiff_of_strong` | thm | true | – |
| 52 | `em_complexity` | thm | true | only evaluates the case split of `complexityBound`, for every real $\varepsilon$ |
| 53 | `timestep_rate` | thm | true | – |
| 54 | `kurtosis_const_mul` | thm | true | `kurtosis` is non-central; $x/0=0$ (consistent) |
| 55 | `digital_em_complexity` | thm | true | evaluation only |
| 56 | `milstein_complexity` | thm | true | evaluation only |
| 57 | `integral_condExp_eq_of_map_eq` | thm | true | $0=0$ when $g\circ S$ non-integrable; ambient σ-algebra is $m_0$ |
| 58 | `bridgeInterp` | def | – | – |
| 59 | `bridgeInterp_midpoint` | thm | true | argument order ($W_1:=W_{n2}$, $W_t:=W_{n1}$) |
| 60 | `pairSwap` | def | – | – |
| 61 | `swapIncrements` | def | – | – |
| 62 | `measurePreserving_swapIncrements` | thm | true | – |
| 63 | `abs_antithetic_le` | thm | true | – |
| 64 | `variance_antithetic_le` | thm | true | 4th moments bounded by $D_2h^2$ (not $h^4$) |
| 65 | `emMeanRevert` | def | – | junk for $\tau=0$ |
| 66 | `emMeanRevert_iterate` | thm | true | holds also for $\tau=0$ (junk-consistent) |
| 67 | `emMeanRevert_bounded` | thm | true | – |
| 68 | `emMeanRevert_unbounded` | thm | true | – |
| 69 | `smoothCDF` | def | – | junk for $\delta=0$ |
| 70 | `smooth_step_eventually` | thm | true | – |
| 71 | `abs_smoothCDF_sub_le` | thm | true | – |
| 72 | `tendsto_smoothCDF` | thm | true | – |
| 73 | `splitting_mean_variance` | thm | true | – |
| 74 | `tendsto_kernel_integral_signed` | lemma | true | – |
| 75 | `tendsto_density` | thm | true | – |
| 76 | `complexityBound` | def (supporting) | – | junk for $\varepsilon\le0$ or $\alpha=0$ |
| 77 | `totalCost` | def (supporting) | – | – |
| 78 | `blockMean` | def (supporting) | – | $N=0\Rightarrow0$ |
| 79 | `kurtosis` | def (supporting) | – | non-central moment ratio; $x/0=0$ |
| 80 | `fineCoarseDiff` | def (supporting) | – | – |

---

## Conventions (confirmed in the sources)

Paths are relative to `Mathlib/` unless marked "core".

- **C1. Interval integral.** `MeasureTheory/Integral/IntervalIntegral/Basic.lean:657`:
  `∫ x in a..b, f x ∂μ := ∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
  The notation `∫ u in a..b, f u` uses Lebesgue measure. The integral is **oriented**: for $a>b$ it equals $-\int_{(b,a]}f$, and for $a=b$ it is $0$. Below, $\int_a^b$ always means this oriented integral.
- **C2. Interval integrability.** `IntervalIntegrable f μ a b := IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ` (same file, line 72). Equivalently, $f$ is integrable on $(\min(a,b),\max(a,b)]$.
- **C3. Bochner integral.** The integral of a non-integrable function is $0$ (`integral_undef`, `MeasureTheory/Integral/Bochner/Basic.lean:202`). The notation `∫ x, body ∂μ` parses `body` at precedence 60 (line 166), so `∫ z, F z - P z ∂μ` integrates the difference.
- **C4. Expectation notation.** `P[X]` in `ProbabilityTheory` expands to `∫ x, X x ∂P` (`Probability/Notation.lean:53`).
- **C5. Variance.** In `Probability/Moments/Variance.lean`:
  - lines 58 and 64: `evariance X μ := ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ` and `variance X μ := (evariance X μ).toReal`;
  - `evariance_eq_top`: for a finite measure and an a.e.-strongly-measurable $X\notin L^2$, the evariance is $\infty$, so the variance is **0**;
  - `variance_le_expectation_sq` (line 339): $\mathrm{Var}\,X\le\mu[X^2]$ for a probability measure and a.e.-strongly-measurable $X$, with no other condition.
- **C6. Conditional expectation.** `MeasureTheory/Function/ConditionalExpectation/Basic.lean:102`: `μ[f|m]` is the zero function if $m\not\le m_0$, or if `μ.trim` is not σ-finite, or if $f$ is not integrable.
  - `integral_condExp` (line 236): if $m\le m_0$ and `μ.trim` is σ-finite, then $\int\mu[f|m]\,d\mu=\int f\,d\mu$ for **every** $f$ (both sides are $0$ if $f$ is not integrable).
  - `isFiniteMeasure_trim` (`MeasureTheory/Measure/Trim.lean:124`).
- **C7. Pushforward.**
  - `Measure.map f μ` is the zero measure unless $f$ is a.e.-measurable (`MeasureTheory/Measure/Map.lean:91`).
  - `MeasurePreserving f μa μb := Measurable f ∧ map f μa = μb` (`Dynamics/Ergodic/MeasurePreserving.lean:45`).
- **C8. Gaussian.** `gaussianReal m v` (with $v\in\mathbb R_{\ge0}$) is `dirac m` if $v=0$ and otherwise Lebesgue measure with the Gaussian density. It is a probability measure. So `gaussianReal 0 1` $=\mathcal N(0,1)$ (`Probability/Distributions/Gaussian/Real.lean:222`).
- **C9. Infinite product measure.** `Measure.infinitePi μ` is the product measure (extended from cylinder sets) when every factor is a probability measure, and the zero measure otherwise (`Probability/ProductMeasure.lean:358`).
  - It is then a probability measure (line 381).
  - Its coordinates are measure-preserving (`measurePreserving_eval_infinitePi`, line 470).
  - Its coordinates are independent (`iIndepFun_infinitePi`, `Probability/Independence/InfinitePi.lean:127`).
- **C10. Independence.** `iIndepFun f μ` means the σ-algebras generated by the $f_i$ are mutually independent (`Probability/Independence/Basic.lean:136`). The codomain $\mathbb R^{\mathbb N}$ carries the product σ-algebra.
- **C11. Real-valued measure.** `μ.real s := (μ s).toReal`, so an infinite measure maps to $0$ (`MeasureTheory/Measure/MeasureSpaceDef.lean:101`).
- **C12. Square root.** `Real.sqrt x = 0` for $x\le0$ (`Analysis/Real/Sqrt.lean:142`). `Real.sqrt_mul (hx : 0 ≤ x) (y)` gives $\sqrt{xy}=\sqrt x\sqrt y$ for **every** real $y$ (line 366).
- **C13. Real powers** (`Analysis/SpecialFunctions/Pow/Real.lean`):
  - $x^y=e^{y\log x}$ for $x>0$;
  - $x^0=1$;
  - $0^y=0$ for $y\ne0$;
  - for $x<0$, $x^y=e^{y\log x}\cos(y\pi)$.
- **C14. Logarithm.** `Real.log 0 = 0` and `log (-x) = log x` (`Analysis/SpecialFunctions/Log/Basic.lean:103,121`).
- **C15. Natural logarithm.** `Nat.log b n` is the largest $k$ with $b^k\le n$ (for $b>1$, $n\ne0$), and `Nat.log b 0 = 0` (`Data/Nat/Log.lean:62,145`).
- **C16. Arithmetic.** Natural-number subtraction $\dot-$ truncates at $0$; natural-number `/` is floor division and `%` is the remainder. In fields, $x/0=0$ and $0^{-1}=0$.
- **C17. Least element.** `IsLeast s a := a ∈ s ∧ a ∈ lowerBounds s` (`Order/Bounds/Defs.lean:45`).
- **C18. Big-operator precedence.** `∑ x ∈ s, body` parses `body` at precedence 67 (`Algebra/BigOperators/Group/Finset/Defs.lean:181`). Hence:
  - `∑ ℓ ∈ s, F ℓ - c` means $(\sum F_\ell)-c$;
  - `r * ∑ j ∈ s, A j + ∑ …` means $r\cdot(\sum A_j)+\sum\ldots$.
- **C19. Iteration.** `f^[n]` is `Nat.iterate f n` (`Logic/Function/Iterate.lean:46`), so $f^{[0]}=\mathrm{id}$.
- **C20. One-sided neighbourhood.** `𝓝[>] x := nhdsWithin x (Set.Ioi x)` (`Topology/Defs/Filter.lean:155`).
- **C21. Local instance order** (core `Lean/Meta/SynthInstance.lean`, `getInstances`). Local instances are pushed after the global ones, in local-context order, and the generator tries instances from the end of the array. So, among several local instances of one class, the **last-declared** one wins. Consequence for `integral_condExp_eq_of_map_eq`, which has `{m m' m₀ : MeasurableSpace Ω}`: the measure `μ : Measure Ω`, `Measurable S` and `μ.map S` all use $m_0$.
- **C22. Unconditional integral identities.**
  - `intervalIntegral.integral_comp_sub_left` (`IntervalIntegral/Basic.lean:1054`): $\int_a^b f(d-x)\,dx=\int_{d-b}^{d-a}f$, with no integrability hypothesis.
  - `integral_const_mul` (`Bochner/Basic.lean:288`): $\int r f=r\int f$, with no hypothesis.
- **C23. Measure with density.** `Measure.withDensity μ f` assigns $s\mapsto\int^-_s f\,d\mu$ (`MeasureTheory/Measure/WithDensity.lean:39`).

## Notation used below

- $\lambda$ is Lebesgue measure on $\mathbb R$, and $\int_a^b$ is the oriented integral of C1.
- "Interval-integrable on $a..b$" is as in C2.
- $x_{d,j}:=j/2^d$ (this is `gridPt d j`).
- $\ell_{d,j}:=\operatorname{lutValue}(f,d,j)$ when $f$ is clear from context.
- $\mathbb G:=\bigotimes_{n\in\mathbb N}\mathcal N(0,1)$ on $\mathbb R^{\mathbb N}$ (this is `stdNormalSeq`).
- $\mathrm{Fin}\,n=\{0,\dots,n-1\}$.

---

## A. Module `MlmcLean.ApproxNormal`

The section `Projection` has section variables $f:\mathbb R\to\mathbb R$ and $a,b\in\mathbb R$ (implicit). The section `Grid` has $f:\mathbb R\to\mathbb R$ (implicit).

### 1. `intervalMean` (definition)

**Rendering.** For $f:\mathbb R\to\mathbb R$ and $a,b\in\mathbb R$:
$$\operatorname{intervalMean}(f,a,b)=(b-a)^{-1}\int_a^b f(u)\,du .$$
- For $a<b$ this is the Lebesgue average of $f$ over $(a,b]$.
- For $a>b$ both factors change sign, so it is the average of $f$ over $(b,a]$.
- For $a=b$ it is $0$.

**Truth / Non-vacuity.** Not applicable (definition).

**Junk values.**
- When $a=b$, $0^{-1}=0$ gives the value $0$.
- If $f$ is not integrable on the interval, the integral is $0$ (C3), so the value is $0$.

**Concerns.** None. Every theorem that uses it assumes $a<b$ and that $f$ and $f^2$ are integrable.

### 2. `integral_sq_sub_const` (lemma)

**Rendering.** Let $f:\mathbb R\to\mathbb R$ and let $a,b$ be real numbers, in either order. Assume:
- $f$ is interval-integrable on $a..b$;
- $u\mapsto f(u)^2$ is interval-integrable on $a..b$.

Then for every $z\in\mathbb R$:
$$\int_a^b (z-f(u))^2\,du=(b-a)\,z^2-2z\int_a^b f(u)\,du+\int_a^b f(u)^2\,du .$$

**Truth.** True. Expand the square and use linearity of the oriented integral: the constant, $f$ and $f^2$ are all interval-integrable, and $\int_a^b z^2\,du=(b-a)z^2$.

**Non-vacuity.** $f\equiv0$, any $a,b$.

**Junk values.** None. The hypotheses make every integral genuine.

**Concerns.** None.

### 3. `integral_sq_sub_eq` (theorem)

**Rendering.** Let $f$ and $a<b$ be given, with $f$ and $f^2$ interval-integrable on $a..b$. Write $m=\operatorname{intervalMean}(f,a,b)=\frac1{b-a}\int_a^b f$. Then for every $z\in\mathbb R$:
$$\int_a^b (z-f(u))^2\,du=(b-a)\,(z-m)^2+\int_a^b (m-f(u))^2\,du .$$

**Truth.** True. This is the bias–variance decomposition: expand both sides and use $(b-a)m=\int_a^b f$. Checked numerically in `check_numeric.py`.

**Non-vacuity.** $a=0$, $b=1$, $f\equiv0$.

**Junk values.** None.

**Concerns.** The hypothesis $a<b$ is superfluous (harmless). The identity also holds for $a>b$, because $(b-a)m=\int_a^b f$ still holds. It holds for $a=b$ too, since both sides are $0$. The numerical check confirmed both cases.

### 4. `integral_sq_sub_intervalMean_le` (theorem)

**Rendering.** Let $f$ and $a<b$ be given, with $f$ and $f^2$ interval-integrable on $a..b$, and let $m=\operatorname{intervalMean}(f,a,b)$. Then for every $z\in\mathbb R$:
$$\int_a^b (m-f(u))^2\,du\ \le\ \int_a^b (z-f(u))^2\,du .$$

**Truth.** True, by theorem 3, since $(b-a)(z-m)^2\ge0$.

**Non-vacuity.** As in theorem 3.

**Junk values.** None.

**Concerns.** None. Here $a<b$ is genuinely needed: for $a>b$ the oriented integrals of squares are $\le0$ and the inequality reverses (observed numerically).

### 5. `eq_intervalMean_of_integral_sq_sub_le` (theorem)

**Rendering.** Let $f$ and $a<b$ be given, with $f$ and $f^2$ interval-integrable on $a..b$. Let $z\in\mathbb R$ satisfy
$$\int_a^b(z-f)^2\le\int_a^b(m-f)^2,\qquad m=\operatorname{intervalMean}(f,a,b).$$
Then $z=m$.

**Truth.** True. Theorem 3 gives $(b-a)(z-m)^2\le0$, and $b-a>0$.

**Non-vacuity.** $z=m$ satisfies the hypothesis.

**Junk values.** None.

**Concerns.** None.

### 6. `intervalMean_isLeast` (theorem)

**Rendering.** Let $f$ and $a<b$ be given, with $f$ and $f^2$ interval-integrable on $a..b$. Then the number $\int_a^b(m-f)^2$, where $m=\operatorname{intervalMean}(f,a,b)$, is the least element of
$$\Big\{\textstyle\int_a^b (z-f(u))^2\,du\ :\ z\in\mathbb R\Big\}.$$
That is, it belongs to the set (at $z=m$) and is $\le$ every element.

**Truth.** True, by theorem 4.

**Non-vacuity.** As in theorem 3.

**Junk values.** None.

**Concerns.** None.

### 7. `gridPt` (definition)

**Rendering.** For $d,j\in\mathbb N$: $\operatorname{gridPt}(d,j)=j/2^d\in\mathbb R$, written $x_{d,j}$ below.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** None, since $2^d\ge1$.

**Concerns.** None.

### 8. `lutValue` (definition)

**Rendering.** For $f:\mathbb R\to\mathbb R$ and $d,j\in\mathbb N$:
$$\operatorname{lutValue}(f,d,j)=2^d\int_{x_{d,j}}^{x_{d,j+1}}f(u)\,du .$$
This is $2^d$ times the Lebesgue integral of $f$ over the cell $(j2^{-d},(j+1)2^{-d}]$. The cell has length $2^{-d}$, so the value is the average of $f$ on that cell; it equals $\operatorname{intervalMean}(f,x_{d,j},x_{d,j+1})$. There is no restriction $j<2^d$, so cells beyond $[0,1]$ are allowed.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** If $f$ is not integrable on the cell, the value is $0$.

**Concerns.** None.

### 9. `lutValue_isLeast` (theorem)

**Rendering.** Let $f$ and $d,j\in\mathbb N$ be such that $f$ and $f^2$ are interval-integrable on $x_{d,j}..x_{d,j+1}$. Then both of the following hold.
1. $\int_{x_{d,j}}^{x_{d,j+1}}(\ell_{d,j}-f)^2$ is the least element of the set $\big\{\int_{x_{d,j}}^{x_{d,j+1}}(z-f)^2 : z\in\mathbb R\big\}$.
2. For every $z\in\mathbb R$: if $\int_{x_{d,j}}^{x_{d,j+1}}(z-f)^2\le\int_{x_{d,j}}^{x_{d,j+1}}(\ell_{d,j}-f)^2$, then $z=\ell_{d,j}$.

**Truth.** True. The cell has positive length $2^{-d}$, and $\ell_{d,j}$ is the interval mean on it, because $(x_{d,j+1}-x_{d,j})^{-1}=2^d$. Theorems 5 and 6 then apply.

**Non-vacuity.** $f\equiv0$.

**Junk values.** None.

**Concerns.** None.

### 10. `integral_sq_sub_lutValue` (theorem)

**Rendering.** Under the hypotheses of theorem 9, for every $z\in\mathbb R$:
$$\int_{x_{d,j}}^{x_{d,j+1}}(z-f)^2=(2^d)^{-1}(z-\ell_{d,j})^2+\int_{x_{d,j}}^{x_{d,j+1}}(\ell_{d,j}-f)^2 .$$

**Truth.** True: theorem 3 on the cell, whose length is $(2^d)^{-1}$.

**Non-vacuity.** $f\equiv0$.

**Junk values.** None.

**Concerns.** None.

### 11. `sum_integral_sq_sub_lutValue` (theorem)

**Rendering.** Let $f$ and $d,n\in\mathbb N$ satisfy $n\le2^d$, and let $f$ and $f^2$ be interval-integrable on $0..1$. Then for any $w:\mathbb N\to\mathbb R$:
$$\sum_{j=0}^{n-1}\int_{x_{d,j}}^{x_{d,j+1}}(w_j-f)^2=(2^d)^{-1}\sum_{j=0}^{n-1}(w_j-\ell_{d,j})^2+\sum_{j=0}^{n-1}\int_{x_{d,j}}^{x_{d,j+1}}(\ell_{d,j}-f)^2 .$$
The factor $(2^d)^{-1}$ multiplies only the first sum on the right (C18).

**Truth.** True. For $j<n\le2^d$ each cell lies inside $[0,1]$, so it inherits integrability; apply theorem 10 cell by cell and add.

**Non-vacuity.** $f\equiv0$, $n=0$ or $n=2^d$.

**Junk values.** None.

**Concerns.** None.

### 12. `sum_integral_sq_le_iff` (theorem)

**Rendering.** Under the hypotheses of theorem 11, for any $w,w':\mathbb N\to\mathbb R$:
$$\sum_{j<n}\int_{x_{d,j}}^{x_{d,j+1}}(w_j-f)^2\le\sum_{j<n}\int_{x_{d,j}}^{x_{d,j+1}}(w'_j-f)^2\iff\sum_{j<n}(w_j-\ell_{d,j})^2\le\sum_{j<n}(w'_j-\ell_{d,j})^2 .$$

**Truth.** True, by theorem 11 and $(2^d)^{-1}>0$.

**Non-vacuity.** As in theorem 11.

**Junk values.** None.

**Concerns.** None.

### 13. `method1_le` (theorem)

**Rendering.** Under the hypotheses of theorem 11, for any $w:\mathbb N\to\mathbb R$:
1. $\sum_{j<n}\int_{x_{d,j}}^{x_{d,j+1}}(\ell_{d,j}-f)^2\le\sum_{j<n}\int_{x_{d,j}}^{x_{d,j+1}}(w_j-f)^2$; and
2. if these two sums are equal, then $w_j=\ell_{d,j}$ for every $j<n$.

**Truth.** True. By theorem 11, the difference of the two sums is $(2^d)^{-1}\sum_{j<n}(w_j-\ell_{d,j})^2$.

**Non-vacuity.** As in theorem 11.

**Junk values.** None.

**Concerns.** None.

### 14. `method1_le_perm` (theorem)

**Rendering.** Let $f$ and $d\in\mathbb N$ be given, with $f$ and $f^2$ interval-integrable on $0..1$. Let $\pi$ be any permutation of $\mathrm{Fin}\,2^d$ and $\tilde Z:\mathrm{Fin}\,2^d\to\mathbb R$ any function. Then:
$$\sum_{j=0}^{2^d-1}\int_{x_{d,j}}^{x_{d,j+1}}(\ell_{d,j}-f)^2\ \le\ \sum_{j\in\mathrm{Fin}\,2^d}\int_{x_{d,\pi(j)}}^{x_{d,\pi(j)+1}}(\tilde Z_j-f)^2 .$$
In words: assigning value $\tilde Z_j$ to cell $\pi(j)$ never gives a smaller total squared error than assigning every cell its own mean.

**Truth.** True. Re-index with $k=\pi(j)$ and apply theorem 13 with $n=2^d$ and $w_k=\tilde Z_{\pi^{-1}(k)}$.

**Non-vacuity.** $f\equiv0$, $\pi=\mathrm{id}$.

**Junk values.** None.

**Concerns.** None.

### 15. `lutValue_mirror` (theorem)

**Rendering.** Let $f$ satisfy $f(1-u)=-f(u)$ for **every** $u\in\mathbb R$, and let $d,j\in\mathbb N$ with $j<2^d$. Then
$$\ell_{d,\,2^d-1-j}=-\ell_{d,j}.$$
Here $2^d-1-j$ is natural-number subtraction, which does not truncate because $j<2^d$. There is no integrability hypothesis.

**Truth.** True. The substitution $u\mapsto1-u$ maps the cell of $2^d-1-j$ onto the cell of $j$. The lemmas `integral_comp_sub_left` and `integral_neg` need no integrability (C22). Checked numerically for $d<5$.

**Non-vacuity.** $f(u)=u-\tfrac12$.

**Junk values.** If $f$ is not integrable on cell $j$, it is not integrable on the mirrored cell either (because $f(1-u)=-f(u)$). Then both lookup values are $0$ and the statement reads $0=-0$. It is genuinely meaningful for locally integrable $f$.

**Concerns.** The symmetry is required on all of $\mathbb R$, not only on $[0,1]$; this forces $f(\tfrac12)=0$. It is still satisfiable.

### 16. `lutValue_upper_half` (theorem)

**Rendering.** Let $f$ satisfy $f(1-u)=-f(u)$ for all $u\in\mathbb R$, and let $d,j\in\mathbb N$ with $1\le d$, $2^{d-1}\le j$ and $j<2^d$. Then both of the following hold:
- $2^d-1-j<2^{d-1}$;
- $\ell_{d,j}=-\ell_{d,\,2^d-1-j}$.

All subtractions are natural-number subtractions, and none truncates here.

**Truth.** True. The first part holds because $2^d-1-j\le2^{d-1}-1$. The second part is theorem 15.

**Non-vacuity.** $d=1$, $j=1$, $f(u)=u-\tfrac12$.

**Junk values.** Same remark as theorem 15.

**Concerns.** The hypothesis $1\le d$ is redundant: for $d=0$, $2^{0\dot-1}=2^0=1$, and $1\le j<1$ is impossible.

### 17. `coupledUniform` (definition)

**Rendering.** For $\pi:\mathbb N\to\mathbb N$ and $d,D,J\in\mathbb N$, set $s=D\dot-d$ (truncated) and $q=\lfloor J/2^s\rfloor$. Then
$$\operatorname{coupledUniform}(\pi,d,D,J)=\frac{\pi(q)}{2^d}+\frac{J-2^s q+\frac12}{2^D}\in\mathbb R ,$$
where $J-2^sq=J\bmod2^s$.

When $d\le D$, this is the midpoint of sub-cell number $J\bmod2^{D-d}$ (width $2^{-D}$) inside level-$d$ cell number $\pi(q)$. Nothing requires $\pi(q)<2^d$ or $J<2^D$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** For $D<d$: $s=0$ and $q=J$, so the value is $\pi(J)/2^d+1/2^{D+1}$; for example with $\pi=\mathrm{id}$, $d=3$, $D=1$ the values are $1/4, 3/8, 1/2, 5/8$. Every theorem that uses it assumes $d\le D$.

**Concerns.** None beyond the $D<d$ case.

### 18. `coupledUniform_eq` (theorem)

**Rendering.** For $d\le D$, any $\pi:\mathbb N\to\mathbb N$ and any $J$, with $q=\lfloor J/2^{D-d}\rfloor$:
$$\operatorname{coupledUniform}(\pi,d,D,J)=\frac{\pi(q)-q}{2^d}+\frac{J+\frac12}{2^D}.$$

**Truth.** True, using $2^{D-d}/2^D=2^{-d}$. Checked exactly with rationals over random $\pi,d,D,J$.

**Non-vacuity.** Any $d\le D$.

**Junk values.** None under $d\le D$.

**Concerns.** None.

### 19. `coupledUniform_mem` (theorem)

**Rendering.** For $d\le D$ and any $\pi$, $J$, with $q=\lfloor J/2^{D-d}\rfloor$:
$$x_{d,\pi(q)}<\operatorname{coupledUniform}(\pi,d,D,J)<x_{d,\pi(q)+1}.$$
Both inequalities are strict.

**Truth.** True, since $0<(r+\tfrac12)/2^D<2^{-d}$ for $0\le r<2^{D-d}$. Checked exactly.

**Non-vacuity.** Any $d\le D$.

**Junk values.** None.

**Concerns.** None.

### 20. `midpoint_mem_cell` (theorem)

**Rendering.** For $d\le D$ and any $J$, with $q=\lfloor J/2^{D-d}\rfloor$:
$$x_{d,q}<\frac{J+\frac12}{2^D}<x_{d,q+1}.$$

**Truth.** True, since $q2^{D-d}\le J<(q+1)2^{D-d}$. Checked exactly.

**Non-vacuity.** Trivial.

**Junk values.** None.

**Concerns.** None.

### 21. `coupledIndex` (definition)

**Rendering.** With $s=D\dot-d$:
$$\operatorname{coupledIndex}(\pi,d,D,J)=2^{s}\,\pi(\lfloor J/2^{s}\rfloor)+(J\bmod2^{s})\in\mathbb N .$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.** For $D<d$ the value is $\pi(J)$.

**Concerns.** None.

### 22. `coupledUniform_eq_index` (lemma)

**Rendering.** For $d\le D$ and any $\pi$, $J$:
$$\operatorname{coupledUniform}(\pi,d,D,J)=\frac{\operatorname{coupledIndex}(\pi,d,D,J)+\frac12}{2^D}.$$

**Truth.** True. Checked exactly.

**Non-vacuity.** Trivial.

**Junk values.** None.

**Concerns.** None.

### 23. `sum_coupledIndex` (theorem)

**Rendering.** Let $d\le D$, and let $\pi,\rho:\mathbb N\to\mathbb N$ satisfy, for every $j<2^d$:
- $\pi(j)<2^d$ and $\rho(j)<2^d$;
- $\rho(\pi(j))=j$ and $\pi(\rho(j))=j$.

So $\pi$ restricted to $\{0,\dots,2^d-1\}$ is a bijection with inverse $\rho$; outside this range both are unconstrained. Then for every additive commutative monoid $M$ and every $g:\mathbb N\to M$:
$$\sum_{J=0}^{2^D-1}g\big(\operatorname{coupledIndex}(\pi,d,D,J)\big)=\sum_{J=0}^{2^D-1}g(J).$$

**Truth.** True. Writing $J=2^{D-d}q+r$, the map $J\mapsto2^{D-d}\pi(q)+r$ permutes $\{0,\dots,2^D-1\}$. Checked by brute force: 300 random cases, no failures.

**Non-vacuity.** $\pi=\rho=\mathrm{id}$.

**Junk values.** None.

**Concerns.** None.

### 24. `card_signed_sums` (theorem)

**Rendering.** For $e\ge1$ and $n\in\mathbb N$: the number of functions
$$\mathrm{Fin}\,n\to\{\mathrm{true},\mathrm{false}\}\times\mathrm{Fin}\,2^{e-1}$$
equals $2^{ne}$.

**Truth.** True: the count is $(2\cdot2^{e-1})^n=2^{ne}$.

**Non-vacuity.** $e=1$.

**Junk values.** None under $e\ge1$.

**Concerns.** This is pure counting. The hypothesis $e\ge1$ is needed: for $e=0$, $2^{0\dot-1}=1$ and the count is $2^n\ne1$.

### 25. `card_image_add_le` (theorem)

**Rendering.** For any type $\iota$ with decidable equality, any finite set $s\subseteq\iota$ and any $x:\iota\to\mathbb R$:
$$\#\{x_i+x_j:(i,j)\in s\times s\}\le\binom{|s|+1}{2}.$$

**Truth.** True. The sums are symmetric in $(i,j)$, so there is at most one value per unordered pair with repetition. The bound is sharp: $x_i=2^i$ attains it. Checked on 3000 random cases.

**Non-vacuity.** Trivial.

**Junk values.** None.

**Concerns.** The `DecidableEq ι` assumption is not used by the statement (harmless).

### 26. `choose_two_pow_add_one` (theorem)

**Rendering.** For every $k\in\mathbb N$:
$$\binom{2^{k+1}+1}{2}=2^{2k+1}+2^k.$$

**Truth.** True. Checked for $k<40$.

**Non-vacuity.** Not applicable (no hypotheses).

**Junk values.** None.

**Concerns.** None.

### 27. `sorting_minimises` (theorem)

**Rendering.** Let $n\in\mathbb N$. Let $Z:\mathrm{Fin}\,n\to\mathbb R$ be non-decreasing and $\tilde Z:\mathrm{Fin}\,n\to\mathbb R$ arbitrary. Let $\pi$ be a permutation of $\mathrm{Fin}\,n$ such that $\tilde Z_i<\tilde Z_j\Rightarrow\pi(i)<\pi(j)$ for all $i,j$, and let $\sigma$ be any permutation. Then:
$$\sum_{j}\big(Z_{\pi(j)}-\tilde Z_j\big)^2\le\sum_j\big(Z_{\sigma(j)}-\tilde Z_j\big)^2 .$$

**Truth.** True, by the rearrangement inequality: $Z\circ\pi$ and $\tilde Z$ are similarly ordered. Brute force over all permutations for $n\le5$, including ties: 2047 hypothesis instances, no failures.

**Non-vacuity.** Take $\pi$ to be a sorting permutation of $\tilde Z$.

**Junk values.** None.

**Concerns.** None.

### 28. `alternating_min_antitone` (theorem)

**Rendering.** Let $P,X$ be any types, $F:P\times X\to\mathbb R$, and $\pi:\mathbb N\to P$, $x:\mathbb N\to X$ sequences such that:
- (i) for all $k$ and all $y\in X$: $F(\pi_k,x_k)\le F(\pi_k,y)$;
- (ii) for all $k$ and all $p\in P$: $F(\pi_{k+1},x_k)\le F(p,x_k)$.

Then $k\mapsto F(\pi_k,x_k)$ is non-increasing: $k\le k'\Rightarrow F(\pi_{k'},x_{k'})\le F(\pi_k,x_k)$.

**Truth.** True, from the chain $F(\pi_{k+1},x_{k+1})\le F(\pi_{k+1},x_k)\le F(\pi_k,x_k)$. Checked on random finite examples.

**Non-vacuity.** $F$ constant.

**Junk values.** None.

**Concerns.** None.

### 29. `alternating_min_eventually_const` (theorem)

**Rendering.** Under the hypotheses of theorem 28, with $P$ additionally finite:
$$\exists K\ \forall k\ge K:\ F(\pi_k,x_k)=F(\pi_K,x_K).$$

**Truth.** True. By (i), $F(\pi_k,x_k)=\min_yF(\pi_k,y)$ depends only on $\pi_k$, so the sequence takes finitely many values. A non-increasing sequence with finitely many values is eventually constant. Checked numerically.

**Non-vacuity.** $F$ constant.

**Junk values.** None.

**Concerns.** Only the objective values are asserted to stabilise; the statement says nothing about $\pi_k$ or $x_k$ stabilising.

### 30. `alternating_eventually_periodic` (theorem)

**Rendering.** Let $P$ be a finite type and $X$ any type, with maps $S:X\to P$ and $T:P\to X$. Let $\pi:\mathbb N\to P$ satisfy $\pi_{k+1}=S(T(\pi_k))$ for all $k$. Then:
$$\exists K\ \exists p>0\ \forall k\ge K:\ \pi_{k+p}=\pi_k .$$

**Truth.** True, by the pigeonhole principle applied to the iterates of $S\circ T$. Checked numerically.

**Non-vacuity.** Trivial.

**Junk values.** None.

**Concerns.** There is no minimisation hypothesis: this is a statement about iterating any self-map of a finite set.

### 31. `alternating_stationary` (theorem)

**Rendering.** Let $P,X$ be any types, $S:X\to P$, $T:P\to X$, and $\pi$ with $\pi_{k+1}=S(T(\pi_k))$ for all $k$. Let $K$ satisfy $\pi_{K+1}=\pi_K$. Then $\pi_k=\pi_K$ for all $k\ge K$.

**Truth.** True: a fixed point of $S\circ T$ stays fixed.

**Non-vacuity.** $S\circ T=\mathrm{id}$.

**Junk values.** None.

**Concerns.** None.

### 32. `dyadic_index` (theorem)

**Rendering.** Let $d,j\in\mathbb N$ with $j\ne0$ and $j<2^{d\dot-1}$, and let $L=\lfloor\log_2 j\rfloor$ (`Nat.log 2 j`). Then all four of the following hold:
- $2^L\le j$;
- $j<2^{L+1}$;
- $1\le L+1$;
- $L+1\le d\dot-1$.

**Truth.** True. Checked exhaustively for $d<14$.

**Non-vacuity.** $d=2$, $j=1$.

**Junk values.** None: $j\ne0$ avoids `Nat.log 2 0 = 0`.

**Concerns.** The hypotheses force $d\ge2$: for $d\in\{0,1\}$ they would require $j<1$ together with $j\ne0$.

### 33. `affine_fit_exact` (theorem)

**Rendering.** Let $j_1\ne j_2$, $Z_1$, $Z_2$ be real numbers. Let $a,b$ be real numbers such that, for all $a',b'\in\mathbb R$,
$$(a+bj_1-Z_1)^2+(a+bj_2-Z_2)^2\le(a'+b'j_1-Z_1)^2+(a'+b'j_2-Z_2)^2 .$$
Then $a+bj_1=Z_1$ and $a+bj_2=Z_2$.

**Truth.** True. Some pair $(a',b')$ interpolates both points exactly, so the minimum value is $0$.

**Non-vacuity.** $j_1=0$, $j_2=1$, $a=Z_1$, $b=Z_2-Z_1$.

**Junk values.** None.

**Concerns.** None.

---

## B. Module `MlmcLean.EulerMaruyama`

### 34. `emPath` (definition)

**Rendering.** For $a,b:\mathbb R\times\mathbb R\to\mathbb R$ (first argument the state, second the time), reals $h$ and $S_0$, and $z:\mathbb N\to\mathbb R$, $\operatorname{emPath}(a,b,h,S_0,z)$ is the sequence $(S_i)_{i\in\mathbb N}$ with
$$S_0=S_0,\qquad S_{i+1}=S_i+a(S_i,\,ih)\,h+b(S_i,\,ih)\,\sqrt h\,z_i .$$
Here $\sqrt h$ is `Real.sqrt` and $ih$ is $i$ cast to $\mathbb R$ times $h$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** For $h<0$, $\sqrt h=0$, so there is no noise term.

**Concerns.** None.

### 35. `pairAvg` (definition)

**Rendering.** $(\operatorname{pairAvg}z)_k=(z_{2k}+z_{2k+1})/\sqrt2$.

**Truth / Non-vacuity / Junk values.** Not applicable; no junk.

**Concerns.** None.

### 36. `emCoarsePath` (definition)

**Rendering.** Let $S^c=\operatorname{emPath}(a,b,2h,S_0,\operatorname{pairAvg}z)$. Then $\operatorname{emCoarsePath}(a,b,h,S_0,z)$ at index $i$ is:
- for even $i$: $S^c_{i/2}$;
- for odd $i=2k+1$: $S^c_k+a(S^c_k,\,2k\,h)\,h+b(S^c_k,\,2k\,h)\,\sqrt h\,z_{2k}$.

The code writes $z_{i-1}$ with $i-1=2k$ (no truncation), and the time argument as $(2\lfloor i/2\rfloor)\cdot h$ with the natural number cast to $\mathbb R$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** As for `emPath`.

**Concerns.** None.

### 37. `emCoarsePath_two_mul` (theorem)

**Rendering.** For all $a,b,h,S_0,z,k$:
$$\operatorname{emCoarsePath}(a,b,h,S_0,z)_{2k}=\operatorname{emPath}(a,b,2h,S_0,\operatorname{pairAvg}z)_k .$$

**Truth.** True, by definition.

**Non-vacuity.** Not applicable (no hypotheses).

**Junk values.** None.

**Concerns.** None.

### 38. `emCoarsePath_succ` (theorem)

**Rendering.** For all $a,b,h,S_0,z,i$, write $E=\operatorname{emCoarsePath}(a,b,h,S_0,z)$ and $i'=2\lfloor i/2\rfloor$. Then
$$E_{i+1}=E_i+a(E_{i'},\,i'h)\,h+b(E_{i'},\,i'h)\,\sqrt h\,z_i .$$

**Truth.** True for **every** real $h$. The step from odd to even index uses $\sqrt{2h}/\sqrt2=\sqrt h$, which holds for all $h$ by C12. Checked numerically with $h>0$, $h<0$ and $h=0$: maximum relative error $5\cdot10^{-16}$.

**Non-vacuity.** Not applicable.

**Junk values.** None that matter.

**Concerns.** None.

### 39. `eq_emCoarsePath` (theorem)

**Rendering.** Let $a,b,h,S_0,z$ be given, and let $Sc:\mathbb N\to\mathbb R$ satisfy:
- $Sc_0=S_0$;
- for all $i$: $Sc_{i+1}=Sc_i+a(Sc_{i'},i'h)\,h+b(Sc_{i'},i'h)\sqrt h\,z_i$, where $i'=2\lfloor i/2\rfloor$.

Then $Sc=\operatorname{emCoarsePath}(a,b,h,S_0,z)$ as functions on $\mathbb N$.

**Truth.** True, by strong induction, using $i'\le i$ and theorem 38.

**Non-vacuity.** $Sc=\operatorname{emCoarsePath}(a,b,h,S_0,z)$ itself.

**Junk values.** None.

**Concerns.** None.

### 40. `stdNormalSeq` (abbrev)

**Rendering.** $\mathbb G=\bigotimes_{n\in\mathbb N}\mathcal N(0,1)$ on $\mathbb R^{\mathbb N}$ with the product σ-algebra: the law of an i.i.d. standard normal sequence. It is a genuine product measure, since every factor is a probability measure (C9).

**Truth / Non-vacuity / Junk values.** Not applicable; no junk.

**Concerns.** None.

### 41. `map_pairSum_gaussian` (theorem)

**Rendering.** The image of $\mathcal N(0,1)\otimes\mathcal N(0,1)$ on $\mathbb R^{\{0,1\}}$ under $y\mapsto(y_0+y_1)/\sqrt2$ is $\mathcal N(0,1)$.

**Truth.** True: the sum of two independent $\mathcal N(0,1)$ variables is $\mathcal N(0,2)$, and scaling by $1/\sqrt2$ gives $\mathcal N(0,1)$.

**Non-vacuity.** Not applicable.

**Junk values.** None: the map is measurable, so the pushforward is genuine.

**Concerns.** None.

### 42. `measurePreserving_pairAvg` (theorem)

**Rendering.** $\operatorname{pairAvg}:\mathbb R^{\mathbb N}\to\mathbb R^{\mathbb N}$ is measurable, and its image of $\mathbb G$ is $\mathbb G$.

**Truth.** True. The coordinates $(z_{2k}+z_{2k+1})/\sqrt2$ use disjoint pairs, so they are independent, and each is $\mathcal N(0,1)$.

**Non-vacuity.** Not applicable.

**Junk values.** None.

**Concerns.** None.

### 43. `emFine` (definition)

**Rendering.** For $a,b$, reals $T,S_0$, $\Phi:\mathbb N\to(\mathbb R^{\mathbb N}\to\mathbb R)$ (an arbitrary level-indexed functional), $\ell\in\mathbb N$ and $z\in\mathbb R^{\mathbb N}$:
$$\operatorname{emFine}(a,b,T,S_0,\Phi,\ell)(z)=\Phi_\ell\big(\operatorname{emPath}(a,b,T/2^\ell,S_0,z)\big).$$
$\Phi_\ell$ sees the whole infinite Euler–Maruyama sequence with step $T/2^\ell$.

**Truth / Non-vacuity.** Not applicable.

**Junk values.** $T\le0$ gives step $\le0$ and no noise.

**Concerns.** None.

### 44. `emCoarse` (definition)

**Rendering.**
$$\operatorname{emCoarse}(a,b,T,S_0,\Phi,\ell)(z)=\Phi_\ell\big(k\mapsto\operatorname{emCoarsePath}(a,b,T/2^{\ell+1},S_0,z)_{2k}\big).$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.** As for `emFine`.

**Concerns.** None.

### 45. `emCoarse_eq` (theorem)

**Rendering.** For all $a,b,T,S_0,\Phi,\ell,z$:
$$\operatorname{emCoarse}(a,b,T,S_0,\Phi,\ell)(z)=\operatorname{emFine}(a,b,T,S_0,\Phi,\ell)(\operatorname{pairAvg}z).$$

**Truth.** True, by theorem 37 and $2\cdot T/2^{\ell+1}=T/2^\ell$. Checked numerically (exact agreement).

**Non-vacuity.** Not applicable.

**Junk values.** None.

**Concerns.** None.

### 46. `integral_emCoarse` (theorem)

**Rendering.** For all $a,b,T,S_0,\Phi,\ell$: if $\operatorname{emFine}(a,b,T,S_0,\Phi,\ell)$ is $\mathbb G$-a.e. strongly measurable, then
$$\int\operatorname{emCoarse}(\dots,\ell)\,d\mathbb G=\int\operatorname{emFine}(\dots,\ell)\,d\mathbb G .$$

**Truth.** True, by theorem 45, theorem 42 and change of variables.

**Non-vacuity.** $\Phi\equiv0$.

**Junk values.** No integrability is assumed. If `emFine` is not integrable, neither is `emCoarse` (by measure preservation), and both sides are $0$. The statement stays consistent.

**Concerns.** None.

### 47. `em_mlmc_theorem1` (theorem)

**Rendering.**

*Data.*
- A measurable space $\Omega$ with a probability measure $\mu$.
- $a,b:\mathbb R\times\mathbb R\to\mathbb R$ and $T,S_0\in\mathbb R$. No condition is placed on these ($T$ may be $\le0$).
- $\Phi:\mathbb N\to(\mathbb R^{\mathbb N}\to\mathbb R)$ and $P:\mathbb R^{\mathbb N}\to\mathbb R$.
- $\omega=(\omega_{\ell,n})_{(\ell,n)\in\mathbb N\times\mathbb N}$ with each $\omega_{\ell,n}:\Omega\to\mathbb R^{\mathbb N}$.
- $\mathrm{cost}=(\mathrm{cost}_{\ell,n})$ with each $\mathrm{cost}_{\ell,n}:\Omega\to\mathbb R$, and $C:\mathbb N\to\mathbb R$.
- Reals $\alpha,\beta,\gamma,c_1,c_2,c_3$.

Write:
- $P^f_\ell=\operatorname{emFine}(a,b,T,S_0,\Phi,\ell)$ and $P^c_\ell=\operatorname{emCoarse}(a,b,T,S_0,\Phi,\ell)$ (both maps $\mathbb R^{\mathbb N}\to\mathbb R$);
- $Y=\operatorname{fineCoarseDiff}(P^f,P^c)$, that is, $Y_0=P^f_0$ and $Y_{\ell+1}=P^f_{\ell+1}-P^c_\ell$.

*Hypotheses.*
1. $\alpha,\beta,\gamma,c_1,c_2,c_3>0$, and $\min(\beta,\gamma)/2\le\alpha$.
2. For every $(\ell,n)$, $\omega_{\ell,n}$ is measurable and its law under $\mu$ is $\mathbb G$.
3. The family $(\omega_{\ell,n})_{(\ell,n)}$ is mutually independent under $\mu$.
4. $P$ is $\mathbb G$-integrable.
5. For every $\ell$, $P^f_\ell$ is measurable and lies in $L^2(\mathbb G)$.
6. For every $\ell,n$, $\mathrm{cost}_{\ell,n}$ is $\mu$-integrable and $\mathbb E_\mu[\mathrm{cost}_{\ell,n}]=C_\ell$.
7. For every $\ell$: $\big|\int(P^f_\ell-P)\,d\mathbb G\big|\le c_1\,2^{-\alpha\ell}$.
8. For every $\ell$: $\mathrm{Var}_{\mathbb G}(Y_\ell)\le c_2\,2^{-\beta\ell}$.
9. For every $\ell$: $C_\ell\le c_3\,2^{\gamma\ell}$.

*Conclusion.* There is $c_4>0$ such that for every $\varepsilon$ with $0<\varepsilon<e^{-1}$ there are $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with $N_\ell\ge1$ for **all** $\ell$, satisfying both
$$\mathbb E_\mu\Big[\Big(\sum_{\ell=0}^{L}\frac1{N_\ell}\sum_{n=0}^{N_\ell-1}Y_\ell(\omega_{\ell,n})-\int P\,d\mathbb G\Big)^2\Big]<\varepsilon^2$$
and
$$\mathbb E_\mu\Big[\sum_{\ell=0}^{L}\sum_{n=0}^{N_\ell-1}\mathrm{cost}_{\ell,n}\Big]\le c_4\cdot K(\alpha,\beta,\gamma,\varepsilon),$$
where $K(\alpha,\beta,\gamma,\varepsilon)$ is `complexityBound` (entry 76):
$$K=\begin{cases}\varepsilon^{-2} & \gamma<\beta,\\ \varepsilon^{-2}(\ln\varepsilon)^2 & \beta=\gamma,\\ \varepsilon^{-2-(\gamma-\beta)/\alpha} & \gamma>\beta.\end{cases}$$

*Quantifier order.* $c_4$ is chosen after all the data (it may depend on $a,b,T,S_0,\Phi,P,\omega,\mathrm{cost},C,\alpha,\dots,c_3$) and before $\varepsilon$. $L$ and $N$ depend on $\varepsilon$ and on everything else. The subtraction of $\int P$ lies outside the sum over $\ell$ (C18).

**Truth.** True. This is the standard multilevel Monte Carlo complexity theorem, with the weak-error, variance and cost conditions assumed per sample.
- **Telescoping.** $\mathbb E[P^c_\ell]=\mathbb E[P^f_\ell]$ by theorem 46, so the estimator has mean $\mathbb E_{\mathbb G}[P^f_L]$.
- **Mean squared error.** By hypotheses 2 and 3, the MSE equals $(\mathbb E P^f_L-\mathbb E P)^2+\sum_{\ell\le L}V_\ell/N_\ell$, where $V_\ell=\mathrm{Var}_{\mathbb G}(Y_\ell)$.
- **Choice of parameters.** Take
  - $L=\max(0,\lceil\log_2(\sqrt2c_1/\varepsilon)/\alpha\rceil)$;
  - $S_L=\sum_{\ell\le L}2^{(\gamma-\beta)\ell/2}$;
  - $N_\ell=\lceil4\varepsilon^{-2}c_2S_L2^{-(\beta+\gamma)\ell/2}\rceil$ for $\ell\le L$, and $N_\ell=1$ beyond $L$.
- **Bounds.** Then the MSE is at most $\varepsilon^2/2+\varepsilon^2/4<\varepsilon^2$. The expected cost is $\sum_\ell N_\ell C_\ell\le\sum_\ell N_\ell c_3 2^{\gamma\ell}$; this remains valid if some $C_\ell<0$. It is bounded by a constant times $K$, using $\alpha\ge\min(\beta,\gamma)/2$ and $(\ln\varepsilon)^2>1$ for $\varepsilon<e^{-1}$.
- **Numerical check** (`check_mlmc.py`). With worst-case data ($|{\rm bias}|=c_1 2^{-\alpha L}$, $V_\ell=c_2 2^{-\beta\ell}$, $C_\ell=c_3 2^{\gamma\ell}$), the MSE stays below $\varepsilon^2$ and the ratio cost$/K$ stays bounded as $\varepsilon\to0$ (down to $3.7\cdot10^{-11}$). This held for 8 triples $(\alpha,\beta,\gamma)$, including the edge case $\alpha=\min(\beta,\gamma)/2$, and 3 sets of constants each.
- **Hypothesis 1 matters.** When $\alpha<\min(\beta,\gamma)/2$, the unavoidable cost $C_L$ outgrows $K$.

**Non-vacuity.** The following witness satisfies every hypothesis:
- $\Omega=(\mathbb R^{\mathbb N})^{\mathbb N\times\mathbb N}$ with $\mu=\bigotimes_{\mathbb N\times\mathbb N}\mathbb G$ and $\omega_p$ the $p$-th coordinate. Hypotheses 2 and 3 then follow from `measurePreserving_eval_infinitePi` and `iIndepFun_infinitePi` (C9).
- $a\equiv0$, $b\equiv1$, $T=1$, $S_0=0$, $\Phi_\ell(S)=S_{2^\ell}$, and $P(z)=z_0$.
- Then $P^f_\ell\sim\mathcal N(0,1)$ and the bias is $0$. Also $Y_{\ell+1}\equiv0$ identically (checked in `check_em.py`) and $\mathrm{Var}\,Y_0=1$.
- $\mathrm{cost}_{\ell,n}\equiv2^\ell=C_\ell$, with $\alpha=\beta=\gamma=c_1=c_2=c_3=1$.

The trivial choice $\Phi\equiv0$, $P\equiv0$ also works.

**Junk values.** Under the hypotheses, nothing here depends on a junk value:
- $\int(P^f_\ell-P)$ is a genuine integral, since both functions are integrable.
- $\mathrm{Var}(Y_\ell)$ is a genuine variance, since $P^c_\ell=P^f_\ell\circ\operatorname{pairAvg}\in L^2$ (theorems 42 and 45).
- $\mathbb E_\mu[\mathrm{cost}]$ is genuine.
- For **every** choice of $L$ and $N$, the squared error in the conclusion is $\mu$-integrable, so the strict bound $<\varepsilon^2$ cannot be met by an integral defaulting to $0$.
- $N_\ell^{-1}$ is genuine because $N_\ell\ge1$.
- $\varepsilon\in(0,e^{-1})$ and $\alpha>0$ make the powers and the logarithm in $K$ genuine.

**Concerns.**
1. The statement is **abstract**. It places no condition on $a$, $b$, $T$, $S_0$ or $\Phi$ (no regularity, no link between the $\Phi_\ell$ across levels). $P$ is tied to the rest only through hypothesis 7. All three rate conditions (hypotheses 7, 8, 9) are assumed rather than derived. The only Euler–Maruyama-specific input is the coupling $P^c_\ell=P^f_\ell\circ\operatorname{pairAvg}$, which gives the telescoping property.
2. $c_4$ may depend on all the data, not only on $(\alpha,\beta,\gamma,c_1,c_2,c_3)$.
3. `cost` and $C$ are unconstrained in sign, and `cost` is an arbitrary integrable random variable per $(\ell,n)$, not tied to the computation. The cost conclusion therefore amounts to $\sum_{\ell\le L}N_\ell C_\ell\le c_4K$.

### 48. `variance_sub_le_two_mul` (theorem)

**Rendering.** Let $(\Omega,\mu)$ be a probability space and $X,Y\in L^2(\mu)$. Then
$$\mathrm{Var}(X-Y)\le2(\mathrm{Var}\,X+\mathrm{Var}\,Y).$$

**Truth.** True, since $|2\,\mathrm{Cov}(X,Y)|\le\mathrm{Var}\,X+\mathrm{Var}\,Y$.

**Non-vacuity.** $X=Y=0$.

**Junk values.** None: all variables are in $L^2$.

**Concerns.** None.

### 49. `variance_levelDiff_le` (theorem)

**Rendering.** On a probability space, let $P,P_1,P_2\in L^2(\mu)$. Then
$$\mathrm{Var}(P_1-P_2)\le2\big(\mathrm{Var}(P-P_1)+\mathrm{Var}(P-P_2)\big).$$

**Truth.** True: theorem 48 applied to $(P-P_2)-(P-P_1)$.

**Non-vacuity.** All zero.

**Junk values.** None.

**Concerns.** None.

### 50. `variance_sub_le_of_lipschitz` (theorem)

**Rendering.** On a probability space, let $P,P_l,D:\Omega\to\mathbb R$ and $K\in\mathbb R$ satisfy:
- $P-P_l$ is a.e. strongly measurable;
- $D^2$ is integrable;
- $|P(\omega)-P_l(\omega)|\le K\,D(\omega)$ for **every** $\omega$.

Then
$$\mathrm{Var}(P-P_l)\le\int(P-P_l)^2\,d\mu\le K^2\int D^2\,d\mu .$$

**Truth.** True. Pointwise $(P-P_l)^2\le K^2D^2$, which is integrable, and $\mathrm{Var}\le\mathbb E[X^2]$ (C5).

**Non-vacuity.** Everything zero.

**Junk values.** None: $P-P_l\in L^2$ follows from the domination.

**Concerns.** The hypothesis is only a pointwise domination bound; no Lipschitz property of anything appears in the code. The first inequality does not use the bound at all. $K$ and $D$ may be negative, but the hypothesis forces $KD\ge0$ everywhere.

### 51. `variance_levelDiff_of_strong` (theorem)

**Rendering.** On a probability space, let $P\in L^2$ and $P_\ell\in L^2$ for all $\ell\in\mathbb N$, and let $c,\beta\in\mathbb R$ satisfy
$$\int(P-P_\ell)^2\,d\mu\le c\,2^{-\beta\ell}\quad\text{for every }\ell\in\mathbb N .$$
Then for every $\ell$:
$$\mathrm{Var}(P_{\ell+1}-P_\ell)\le2c\,(1+2^\beta)\,2^{-\beta(\ell+1)} .$$

**Truth.** True. Theorem 49 gives $\mathrm{Var}(P_{\ell+1}-P_\ell)\le2(c2^{-\beta(\ell+1)}+c2^{-\beta\ell})$, which equals the right-hand side.

**Non-vacuity.** $P_\ell=P$, $c=0$. Any $c<0$ makes the hypothesis impossible, but $c\ge0$ is fine.

**Junk values.** None.

**Concerns.** None.

### 52. `em_complexity` (theorem)

**Rendering.** For every real $\varepsilon$:
$$K(1,1,1,\varepsilon)=\varepsilon^{-2}(\ln\varepsilon)^2\quad\text{and}\quad K(2,2,2,\varepsilon)=\varepsilon^{-2}(\ln\varepsilon)^2,$$
where $K$ is `complexityBound` (entry 76).

**Truth.** True: both parameter triples fall in the $\beta=\gamma$ branch.

**Non-vacuity.** Not applicable (no hypotheses).

**Junk values.** The identity also holds for $\varepsilon\le0$, where both sides are the same junk expression (C13, C14). It is harmless.

**Concerns.** This only evaluates the case split of `complexityBound` at fixed parameters. It says nothing about any scheme's rates.

---

## C. Module `MlmcLean.SDEExtras`

### 53. `timestep_rate` (theorem)

**Rendering.** For $h_0>0$, $k,q\in\mathbb R$ and $\ell\in\mathbb N$:
$$\big(h_02^{-k\ell}\big)^q=h_0^q\,2^{-kq\ell}\quad\text{and}\quad\big(h_02^{-k\ell}\big)^{-1}=h_0^{-1}\,2^{k\ell}.$$
All powers are real powers.

**Truth.** True, by the real-power rules for positive bases.

**Non-vacuity.** $h_0=1$.

**Junk values.** None, since the bases are positive.

**Concerns.** None.

### 54. `kurtosis_const_mul` (theorem)

**Rendering.** For any measurable space $\Omega_0$, any $X:\Omega_0\to\mathbb R$, **any** measure $\nu$ on $\Omega_0$ (not assumed finite or probability), and any real $c\ne0$:
$$\kappa(cX,\nu)=\kappa(X,\nu),\qquad\text{where }\ \kappa(X,\nu)=\frac{\int X^4\,d\nu}{\big(\int X^2\,d\nu\big)^2}.$$

**Truth.** True in all cases. The numerator scales by $c^4$ and the denominator by $c^4$, unconditionally (C22). If the denominator is $0$, both sides are $0$ ($x/0=0$).

**Non-vacuity.** $c=1$.

**Junk values.** $x/0=0$ and non-integrable moments give $0$, but they do so consistently on both sides.

**Concerns.** $\kappa$ is the ratio of the **raw** (non-central) fourth moment to the squared raw second moment, not the usual centred kurtosis. It is also not normalised by $\nu(\Omega_0)$.

### 55. `digital_em_complexity` (theorem)

**Rendering.** For every real $\varepsilon$: $K(1,\tfrac12,1,\varepsilon)=\varepsilon^{-5/2}$.

**Truth.** True: this is the third branch, with exponent $-2-(1-\tfrac12)/1=-\tfrac52$.

**Non-vacuity.** Not applicable.

**Junk values.** Holds for every real $\varepsilon$, including the junk region $\varepsilon\le0$.

**Concerns.** This is an evaluation of the case split only.

### 56. `milstein_complexity` (theorem)

**Rendering.** For every real $\varepsilon$: $K(1,2,1,\varepsilon)=\varepsilon^{-2}$ and $K(1,\tfrac32,1,\varepsilon)=\varepsilon^{-2}$.

**Truth.** True: both are in the first branch, since $\gamma=1<\beta$.

**Non-vacuity.** Not applicable.

**Junk values.** Holds for every real $\varepsilon$.

**Concerns.** This is an evaluation of the case split only.

### 57. `integral_condExp_eq_of_map_eq` (theorem)

**Rendering.**
- Let $\Omega$ carry three σ-algebras $m,m',m_0$. The ambient one is $m_0$ (C21): it is used for $\mu$, for measurability of $S$ and $S'$, and for the image measures.
- Let $\alpha$ carry a σ-algebra, and let $\mu$ be a finite measure on $(\Omega,m_0)$.
- Assume $m\le m_0$ and $m'\le m_0$.
- Let $S,S':\Omega\to\alpha$ be $m_0$-measurable with equal image measures, $\mu\circ S^{-1}=\mu\circ S'^{-1}$.
- Let $g:\alpha\to\mathbb R$ be strongly measurable.

Then
$$\int\mathbb E_\mu[g\circ S\mid m]\,d\mu=\int\mathbb E_\mu[g\circ S'\mid m']\,d\mu .$$

**Truth.** True. Since $\mu$ is finite, $\mu$ trimmed to $m$ is finite, so C6 applies. The left side equals $\int g\circ S\,d\mu=\int g\,d(\mu\circ S^{-1})$. By the same argument, the right side equals $\int g\,d(\mu\circ S'^{-1})$, which is the same number.

**Non-vacuity.** $S=S'$ and $m=m'=m_0$.

**Junk values.** No integrability of $g\circ S$ is assumed. If $g\circ S$ is not integrable, then neither is $g\circ S'$ (same law), both conditional expectations are the zero function, and the statement reads $0=0$. It is meaningful in the integrable case.

**Concerns.** The content is only in the integrable case (harmless). Three σ-algebras are in scope, and the ambient one is fixed by instance order.

### 58. `bridgeInterp` (definition)

**Rendering.** For reals $S_0,S_1,b,W_0,W_1,W_t,\lambda$:
$$\operatorname{bridgeInterp}(S_0,S_1,b,W_0,W_1,W_t,\lambda)=S_0+\lambda(S_1-S_0)+b\big(W_t-W_0-\lambda(W_1-W_0)\big).$$

**Truth / Non-vacuity / Junk values.** Not applicable; no junk.

**Concerns.** None.

### 59. `bridgeInterp_midpoint` (theorem)

**Rendering.** For all reals $S_n,S_{n2},b,W_n,W_{n1},W_{n2}$:
$$\operatorname{bridgeInterp}(S_n,S_{n2},b,W_n,W_{n2},W_{n1},\tfrac12)=\tfrac12(S_n+S_{n2})+\tfrac12\,b\big((W_{n1}-W_n)-(W_{n2}-W_{n1})\big).$$
Note the argument order: the endpoint value $W_1$ is $W_{n2}$, and the interior value $W_t$ is $W_{n1}$.

**Truth.** True. Checked exactly with rationals.

**Non-vacuity.** Not applicable.

**Junk values.** None.

**Concerns.** None.

### 60. `pairSwap` (definition)

**Rendering.** For $i\in\mathbb N$: $\operatorname{pairSwap}(i)=i+1$ if $i$ is even, and $i-1$ if $i$ is odd. It swaps $2k\leftrightarrow2k+1$; there is no truncation because odd $i\ge1$.

**Truth / Non-vacuity / Junk values.** Not applicable; no junk.

**Concerns.** None.

### 61. `swapIncrements` (definition)

**Rendering.** $(\operatorname{swapIncrements}z)_i=z_{\operatorname{pairSwap}(i)}$.

**Truth / Non-vacuity / Junk values.** Not applicable; no junk.

**Concerns.** None.

### 62. `measurePreserving_swapIncrements` (theorem)

**Rendering.** For every probability measure $P$ on $\mathbb R$: `swapIncrements` is measurable on $\mathbb R^{\mathbb N}$ and maps the i.i.d. product $P^{\otimes\mathbb N}$ to itself.

**Truth.** True: permuting the coordinates of an i.i.d. product preserves it.

**Non-vacuity.** Any $P$, for example $\mathcal N(0,1)$.

**Junk values.** None.

**Concerns.** None.

### 63. `abs_antithetic_le` (theorem)

**Rendering.** Let $f,f':\mathbb R\to\mathbb R$ and $K\in\mathbb R$ satisfy:
- $f$ is differentiable at every $x$ with derivative $f'(x)$;
- for all $x\le y$: $|f'(y)-f'(x)|\le K(y-x)$. So $f'$ is $K$-Lipschitz, which forces $K\ge0$.

Then for all reals $a,b,c$:
$$\Big|\frac{f(a)+f(b)}2-f(c)\Big|\le|f'(c)|\,\Big|\frac{a+b}2-c\Big|+\frac K4\big((a-c)^2+(b-c)^2\big).$$

**Truth.** True. By Taylor's theorem with a Lipschitz derivative, $|f(a)-f(c)-f'(c)(a-c)|\le\frac K2(a-c)^2$, and similarly for $b$. The bound is tight for $f=Kx^2/2$. Checked numerically: 20000 random cases, maximum excess $3.6\cdot10^{-15}$, which is rounding error.

**Non-vacuity.** $f=\sin$, $f'=\cos$, $K=1$.

**Junk values.** None.

**Concerns.** None.

### 64. `variance_antithetic_le` (theorem)

**Rendering.** Let $(\Omega,\mu)$ be a probability space. Let $f,f'$, $K$ be as in theorem 63, and assume also $|f'(x)|\le L$ for all $x$. Let $D_1,D_2,h$ be reals and $A,B,C:\Omega\to\mathbb R$ measurable. Assume:
- $((A+B)/2-C)^2$, $(A-C)^4$ and $(B-C)^4$ are integrable;
- $\mathbb E[((A+B)/2-C)^2]\le D_1h^2$;
- $\mathbb E[(A-C)^4]\le D_2h^2$ and $\mathbb E[(B-C)^4]\le D_2h^2$.

Then
$$\mathrm{Var}\Big(\frac{f(A)+f(B)}2-f(C)\Big)\le\Big(2L^2D_1+\frac{K^2D_2}2\Big)h^2 .$$

**Truth.** True. Theorem 63 pointwise, together with $(u+v)^2\le2u^2+2v^2$ and $(p+q)^2\le2(p^2+q^2)$, gives an $L^2$ bound on the variable, and $\mathrm{Var}\le\mathbb E[X^2]$. A Monte Carlo sanity check agrees.

**Non-vacuity.** $A=B=C=0$, $h=0$, $f=\sin$, $K=L=1$.

**Junk values.** None: the variable is in $L^2$ by domination.

**Concerns.** The fourth moments are bounded by $D_2h^2$, not $h^4$. This is only a parametrisation, but a reader may not expect it.

### 65. `emMeanRevert` (definition)

**Rendering.** For reals $\theta,\tau,h,S$:
$$\operatorname{emMeanRevert}(\theta,\tau,h,S)=S+\frac{\theta-S}{\tau}\,h .$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.** For $\tau=0$, $(\theta-S)/0=0$, so the value is $S$.

**Concerns.** None.

### 66. `emMeanRevert_iterate` (theorem)

**Rendering.** For all reals $\theta,\tau,h,S$ and all $n\in\mathbb N$, with $E=\operatorname{emMeanRevert}(\theta,\tau,h,\cdot)$ and $E^{[n]}$ its $n$-fold iterate ($E^{[0]}=\mathrm{id}$):
$$E^{[n]}(S)-\theta=(1-h/\tau)^n\,(S-\theta).$$

**Truth.** True for every $\tau$, including $\tau=0$: both sides use $x/0=0$, so $E=\mathrm{id}$ and $1-h/0=1$. Checked exactly with rationals, including $\tau=0$.

**Non-vacuity.** Not applicable (no hypotheses).

**Junk values.** The case $\tau=0$ is junk but consistent on both sides.

**Concerns.** None.

### 67. `emMeanRevert_bounded` (theorem)

**Rendering.** For $\tau>0$ and $0\le h\le2\tau$, and every $S$ and $n$:
$$|E^{[n]}(S)-\theta|\le|S-\theta| .$$

**Truth.** True, since $|1-h/\tau|\le1$.

**Non-vacuity.** $\tau=h=1$.

**Junk values.** None.

**Concerns.** None.

### 68. `emMeanRevert_unbounded` (theorem)

**Rendering.** For $\tau>0$, $h>2\tau$ and $S\ne\theta$:
$$|E^{[n]}(S)-\theta|\to+\infty\quad\text{as }n\to\infty .$$

**Truth.** True, since $|1-h/\tau|>1$.

**Non-vacuity.** $\tau=1$, $h=3$, $S=1$, $\theta=0$.

**Junk values.** None.

**Concerns.** None.

### 69. `smoothCDF` (definition)

**Rendering.** For any measurable space $\Omega$, **any** measure $\mu$ on it (the definition's own binder), $P:\Omega\to\mathbb R$, $g:\mathbb R\to\mathbb R$ and reals $\delta,x$:
$$\operatorname{smoothCDF}(\mu,P,g,\delta,x)=\int g\Big(\frac{x-P(\omega)}{\delta}\Big)\,d\mu(\omega).$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.**
- For $\delta=0$ the value is $g(0)\,\mu(\Omega)$ when integrable.
- If the integrand is not integrable, the value is $0$.

The theorems below use only $\delta>0$ (or $\delta\to0^+$).

**Concerns.** None.

### 70. `smooth_step_eventually` (theorem)

**Rendering.** Let $g:\mathbb R\to\mathbb R$ satisfy $g(y)=0$ for all $y<-1$ and $g(y)=1$ for all $y>1$, and let $y\ne0$. Then for all sufficiently small $\delta>0$:
$$g(y/\delta)=\begin{cases}1 & y>0,\\ 0 & y<0.\end{cases}$$

**Truth.** True, for $0<\delta<|y|$.

**Non-vacuity.** $g(y)=\min(1,\max(0,(y+1)/2))$.

**Junk values.** None.

**Concerns.** None.

### 71. `abs_smoothCDF_sub_le` (theorem)

**Rendering.** Let $(\Omega,\mu)$ be a probability space and $P$ measurable. Let $g$ be measurable with $g=0$ on $(-\infty,-1)$, $g=1$ on $(1,\infty)$ and $0\le g\le1$ everywhere. Let $\delta>0$ and $x\in\mathbb R$. Then
$$\big|\operatorname{smoothCDF}(\mu,P,g,\delta,x)-\mu(P<x)\big|\le\mu(|P-x|\le\delta).$$

**Truth.** True. The integrand differs from $\mathbf 1_{P<x}$ only where $|P-x|\le\delta$, and there by at most $1$. At the boundary points $P=x\pm\delta$ the difference is at most $1$ and the closed inequality $\le\delta$ includes them. Checked exactly on 5000 discrete laws with atoms at $x$ and $x\pm\delta$.

**Non-vacuity.** Any $P$ with $g$ as in theorem 70.

**Junk values.** None: $\mu.\mathrm{real}$ is finite on a probability space.

**Concerns.** None.

### 72. `tendsto_smoothCDF` (theorem)

**Rendering.** Under the hypotheses of theorem 71 (without $\delta$), assume also $\mu(P=x)=0$. Then
$$\operatorname{smoothCDF}(\mu,P,g,\delta,x)\to\mu(P<x)\quad\text{as }\delta\to0^+ .$$

**Truth.** True, by theorem 71 and $\mu(|P-x|\le\delta)\downarrow\mu(P=x)=0$. The hypothesis $\mu(P=x)=0$ is needed: if $P\equiv x$, the value is $g(0)$ (for example $\tfrac12$), not $0$.

**Non-vacuity.** $P\sim\mathcal N(0,1)$.

**Junk values.** None.

**Concerns.** None.

### 73. `splitting_mean_variance` (theorem)

**Rendering.** Let $(\Omega_1,\mu)$ and $(\Omega_2,\nu)$ be probability spaces. Let $g:\Omega_1\times\Omega_2\to\mathbb R$ be jointly measurable with $g^2\in L^1(\mu\otimes\nu)$, and let $M\ge1$. Under $Q=\mu\otimes\nu^{\otimes\mathbb N}$ on $\Omega_1\times\Omega_2^{\mathbb N}$, define
$$\hat Y(x,(z_j)_j)=\frac1M\sum_{j<M}g(x,z_j).$$
Then:
$$\mathbb E_Q[\hat Y]=\int\!\!\int g(x,z)\,d\nu(z)\,d\mu(x),$$
$$\mathrm{Var}_Q(\hat Y)=\mathrm{Var}_\mu\Big(x\mapsto\int g(x,z)\,d\nu(z)\Big)+\frac1M\int\!\!\int\Big(g(x,z)-\int g(x,z')\,d\nu(z')\Big)^2d\nu(z)\,d\mu(x).$$

**Truth.** True, by the law of total variance. Checked exactly with finite discrete $\mu$ and $\nu$ for $M=1,2,3$.

**Non-vacuity.** $g\equiv0$, or any bounded measurable $g$.

**Junk values.** For the $\mu$-null set of $x$ where $g(x,\cdot)\notin L^2(\nu)$, the inner integrals take junk values, but this does not affect the outer integrals.

**Concerns.** None.

### 74. `tendsto_kernel_integral_signed` (lemma)

**Rendering.** Let $g:\mathbb R\to\mathbb R$ be continuous with $g(y)=0$ for $|y|>1$ and $\int g\,d\lambda=1$; $g$ may take negative values. Let $r:\mathbb R\to\mathbb R$ be Lebesgue-integrable and continuous at $x$. Then
$$\int c\,g(c(x-y))\,r(y)\,dy\to r(x)\quad\text{as }c\to+\infty .$$

**Truth.** True. Substitute $u=c(x-y)$ and use continuity of $r$ at $x$ together with boundedness of $g$. Checked numerically with a signed kernel (minimum value about $-1.02$): the integrals $1.09, 1.66, 1.99, 2.026$ approach $r(x)=2.030$.

**Non-vacuity.** Normalised bump $g$ and a Gaussian $r$.

**Junk values.** None: $g$ bounded and $r$ integrable make the integrand integrable.

**Concerns.** None.

### 75. `tendsto_density` (theorem)

**Rendering.** Let $(\Omega,\mu)$ be a probability space and $P$ measurable. Let $\rho:\mathbb R\to\mathbb R_{\ge0}$ be measurable with $\mu\circ P^{-1}=\rho\,d\lambda$, that is, $P$ has density $\rho$. Assume $\rho$ (as a real function) is continuous at $x$, and let $g$ be as in lemma 74. Then
$$\int\delta^{-1}g\Big(\frac{x-P(\omega)}{\delta}\Big)d\mu(\omega)\to\rho(x)\quad\text{as }\delta\to0^+ .$$

**Truth.** True. Change variables to $\int\delta^{-1}g((x-y)/\delta)\rho(y)\,dy$ and apply lemma 74 with $c=\delta^{-1}$; $\rho$ is integrable with $\int\rho=1$.

**Non-vacuity.** $P\sim\mathcal N(0,1)$ with its density.

**Junk values.** None: $\delta>0$ along the filter.

**Concerns.** None.

---

## D. Supporting definitions (trailing section of the packet)

The packet shows these without binders for the type variables $\Omega$, $\Omega_0$ and $\iota$. I read them as arbitrary types; `kurtosis` needs a measurable space on $\Omega_0$ in order to form `Measure Ω₀`.

### 76. `complexityBound` (definition)

**Rendering.** For reals $\alpha,\beta,\gamma,\varepsilon$:
$$K(\alpha,\beta,\gamma,\varepsilon)=\begin{cases}\varepsilon^{-2} & \text{if }\gamma<\beta,\\ \varepsilon^{-2}(\ln\varepsilon)^2 & \text{else if }\beta=\gamma,\\ \varepsilon^{-2-(\gamma-\beta)/\alpha} & \text{otherwise }(\gamma>\beta).\end{cases}$$
All powers are real powers.

**Truth / Non-vacuity.** Not applicable.

**Junk values.**
- For $\varepsilon\le0$, the powers and the logarithm follow C13 and C14 (for example $0^{-2}=0$ and $\ln0=0$).
- For $\alpha=0$ in the third branch, $(\gamma-\beta)/0=0$.

It is used genuinely only in theorem 47, where $\varepsilon\in(0,e^{-1})$ and $\alpha>0$.

**Concerns.** None.

### 77. `totalCost` (definition)

**Rendering.**
$$\operatorname{totalCost}(\mathrm{cost},L,N)(x)=\sum_{\ell=0}^{L}\sum_{n=0}^{N_\ell-1}\mathrm{cost}_{\ell,n}(x).$$

**Truth / Non-vacuity / Junk values.** Not applicable; no junk.

**Concerns.** None.

### 78. `blockMean` (definition)

**Rendering.**
$$\operatorname{blockMean}(f,\omega,i,N)(x)=N^{-1}\sum_{n=0}^{N-1}f_i\big(\omega_{(i,n)}(x)\big).$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.** For $N=0$ the value is $0$ (since $0^{-1}=0$).

**Concerns.** None.

### 79. `kurtosis` (definition)

**Rendering.**
$$\kappa(X,\nu)=\frac{\int X^4\,d\nu}{\big(\int X^2\,d\nu\big)^2}.$$

**Truth / Non-vacuity.** Not applicable.

**Junk values.** The value is $0$ if $\int X^2=0$ or if $X^4$ is not integrable. It is not normalised by $\nu(\Omega_0)$.

**Concerns.** This is a non-central moment ratio, not the usual centred kurtosis.

### 80. `fineCoarseDiff` (definition)

**Rendering.** For $P^f,P^c:\mathbb N\to(\Omega_0\to\mathbb R)$:
- $\operatorname{fineCoarseDiff}(P^f,P^c)_0=P^f_0$;
- $\operatorname{fineCoarseDiff}(P^f,P^c)_{\ell+1}=P^f_{\ell+1}-P^c_\ell$, pointwise.

**Truth / Non-vacuity / Junk values.** Not applicable; no junk.

**Concerns.** None.
