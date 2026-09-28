# Blind read-back audit: packet G (`packet_G_lut_limits.lean`)

| | |
|---|---|
| **Date** | 2026-09-28 |
| **Packet** | `readback/round7/packet_G_lut_limits.lean` (section header `MlmcLean.LUTLimits`, plus two appended definitions from `MlmcLean.ApproxNormal`) |
| **Declarations audited** | **7**: 3 definitions (`gridPt`, `lutValue`, `method1MSE`) and 4 theorems (`tendsto_method1MSE`, `dyadic_mse_ge`, `method3_mse_ge`, `method3_mse_not_tendsto_zero`) |
| **Auditor** | independent blind auditor (sub-agent) |

## Rules followed

1. **Files read:** only the packet, the mission file `prove2me_workspace/references/mission_auditor.md`, and Mathlib sources under `.lake/packages/mathlib/Mathlib`. I used Mathlib only to confirm the definitions and conventions listed below. I opened no project sources, `docs/`, `notes/`, README, PLAN, papers, other packets or outputs, and I did not look at git history or the web. (The harness put the repository's `CLAUDE.md` into my context automatically. I did not use it.)
2. **Translation:** I translated the code, not the intent. Declaration and file names are treated as labels and are not interpreted.
3. **Renderings** name every binder and hypothesis, unfold every packet definition inline, and keep the exact strength of each relation. They contain no judgement. Truth, vacuity and junk-value analysis appear only in the separate **Assessment** blocks.
4. **Lean was not run** (compiled Mathlib is absent). I read elaboration, casts and parsing from the source. I checked the numerics in pure-Python scripts (standard library only) in `readback/round7/work_G/`.

## Summary

- **7 declarations.** All **4 theorems are true** (proof sketches below). **None is vacuous**: every hypothesis set holds with non-trivial data, for example $f(u)=-u^2$ with $\mu=2$, or $f=\Phi^{-1}$ (inverse standard normal CDF) with $k\ge 2$. **None holds only because of a junk value.** Under the stated hypotheses every integral involved is a genuine Lebesgue integral. The three Dyadic conclusions are lower bounds or a non-convergence claim, and a junk value of $0$ could only work *against* them.
- **Numerical checks** agree with every statement. There are exact rational computations for polynomial $f$ and closed-form cell integrals for $\Phi^{-1}$. Details are in the last section.
- **Main points for a human auditor:**
  1. **`tendsto_method1MSE` is qualitative only.** It gives no rate, and no uniform rate exists: for the monotone, square-integrable $f(u)=-u^{-1/2}/(2-\ln u)$, $\mathrm{method1MSE}(f,d)\gtrsim 1/(d\ln 2)$.
     - Monotonicity is not needed for truth.
     - `hf` follows from `hmono` plus `hf2`.
     - `hf2` is load-bearing. For $f(u)=-u^{-1/2}$, which satisfies `hmono` and `hf` but not `hf2`, the junk convention makes the Lean value of `method1MSE` increase to about $0.00938>0$.
  2. **The Dyadic theorems restrict the approximant only on one block of cells.** The approximant is piecewise constant: one real number per cell. The theorems constrain only the cells covering $(2^{-(k+1)},2^{-k}]$, where the values must be an affine function $a+bj$ of the natural cell index $j$.
     - The hypothesis `hconc` is uniform strong midpoint concavity of $f$ on the closed block $[2^{-(k+1)},2^{-k}]$ only. No monotonicity is assumed.
     - For $f=\Phi^{-1}$, `hconc` holds exactly when $k\ge 2$; it fails for $k=0,1$.
     - The constant $c$ depends only on $(f,k,\mu)$ and is uniform in $d$, $a$, $b$ and $w$. An explicit admissible value is $c=\mu^2\,2^{-5k-18}$.
  3. **Natural-number subtraction** makes the hypothesis `hw` of `method3_mse_not_tendsto_zero` vacuous for $d\le k+2$: the index sets are $\varnothing,\{1\},\{2,3\}$. This is harmless for a limit statement.
  4. **In the Dyadic theorems `hf` and `hf2` overlap.** Given `hconc`, either one suffices, by the classical regularity theorem for midpoint-concave functions. Dropping both makes all three statements false: take $f(u)=-u^2+A(u)$ with $A$ a discontinuous additive (Hamel-basis) function; every integral is then the junk value $0$.

## Mathlib conventions confirmed

Paths are relative to `.lake/packages/mathlib/Mathlib/`.

| Convention | Where (file:line) | Consequence for this packet |
|---|---|---|
| `intervalIntegral f a b μ := ∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ` | `MeasureTheory/Integral/IntervalIntegral/Basic.lean:657-658` | The integral runs over the half-open interval $(a,b]$ |
| Notation `∫ x in a..b, f x` means `intervalIntegral f a b volume` (Lebesgue measure) | same file `:666` | All packet integrals are with respect to Lebesgue measure |
| `integral_of_le`: if $a\le b$, the integral equals `∫ x in Ioc a b` | same file `:677` | Always applies here, since $j/2^d<(j+1)/2^d$ |
| `integral_symm`: reversing the bounds negates the integral (the $a>b$ case) | same file `:684` | Never triggered in this packet |
| **Junk:** `integral_undef`: not `IntervalIntegrable` implies the integral is $0$ | same file `:709` | A non-integrable integrand on a cell contributes $0$ |
| **Junk:** `integral_non_aestronglyMeasurable`: not a.e.-strongly-measurable implies the integral is $0$ | same file `:717` | Non-measurable integrands contribute $0$ |
| **Junk (Bochner):** `integral_undef`, `integral_non_aestronglyMeasurable` | `MeasureTheory/Integral/Bochner/Basic.lean:202, 209` | Underlies both lines above |
| `IntervalIntegrable f μ a b := IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ` | `IntervalIntegral/Basic.lean:72-73` | `IntervalIntegrable g volume 0 1` means $g$ is integrable on $(0,1]$; the second conjunct concerns $(1,0]=\varnothing$ and holds automatically |
| `IntegrableOn f s μ := Integrable f (μ.restrict s)` | `MeasureTheory/Integral/IntegrableOn.lean:92-93` | |
| `Integrable f μ := AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ` | `MeasureTheory/Function/L1Space/Integrable.lean:59-61` | Integrability includes measurability |
| `intervalIntegral.integral_nonneg`: if $a\le b$ and $f\ge0$ on $[a,b]$, the integral is $\ge 0$ | `IntervalIntegral/Basic.lean:1390` | Every term of every packet sum is $\ge0$, genuine or junk |
| `integral_comp_add_right` (translation invariance) | `IntervalIntegral/Basic.lean:954` | Used in the proof sketch of `dyadic_mse_ge` |
| `MonotoneOn f s := ∀ a ∈ s, ∀ b ∈ s, a ≤ b → f a ≤ f b` | `Order/Monotone/Defs.lean:74-75` | Weakly increasing (non-decreasing), only on $s$ |
| `Set.Ioo a b = {x ∣ a < x ∧ x < b}`, `Ioc`, `Icc` | `Order/Interval/Set/Defs.lean:51, 63, 76` | `hmono` concerns the open interval $(0,1)$ |
| `Tendsto f l₁ l₂ := l₁.map f ≤ l₂`; `atTop` on ℕ | `Order/Filter/Defs.lean:321-322`; `Order/Filter/AtTopBot/Defs.lean:39` | Ordinary sequence limit as $d\to\infty$ |
| `Finset.mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b`; empty when $b\le a$ (`Ico_eq_empty_of_le`) | `Order/Interval/Finset/Defs.lean:305`; `Order/Interval/Finset/Basic.lean:118` | Index sets are half-open |
| `Nat.card_Ico : #(Ico a b) = b - a` | `Order/Interval/Finset/Nat.lean:84` | The block has $2^{d-k}-2^{d-k-1}=2^{d-k-1}$ indices |
| `Finset.range n`, `mem_range : m ∈ range n ↔ m < n` | `Data/Finset/Range.lean:53, 64` | `range (2^d)` is $\{0,\dots,2^d-1\}$ |
| `∑ x ∈ s, f x` is `Finset.sum s f` | `Algebra/BigOperators/Group/Finset/Defs.lean:27` | |
| **Junk:** truncated subtraction on ℕ, `tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b` | `Algebra/Order/Sub/Basic.lean:35` | `d - k - 1` and `d - k` truncate to 0 when $d\le k$ |
| **Junk:** `div_zero : a / 0 = 0`, `inv_zero : 0⁻¹ = 0` | `Algebra/GroupWithZero/Basic.lean:407`; `Algebra/GroupWithZero/Defs.lean:236` | Never triggered: only $2^d$, $2^k$, $2^{k+1}$ are inverted or divided by, and none is $0$ |
| `Real.volume_Ioc : volume (Ioc a b) = ofReal (b - a)` | `MeasureTheory/Measure/Lebesgue/Basic.lean:110` | `volume` is Lebesgue measure |
| `aemeasurable_restrict_of_monotoneOn` | `MeasureTheory/Constructions/BorelSpace/Order.lean:794` | Used in the redundancy remark for `hf` |
| `Nat.cast_succ` | `Data/Nat/Cast/Defs.lean:86` | `gridPt d (j+1)` equals $(j+1)/2^d$ |

**Elaboration notes** (read from source):
- In `a + b * j` and `w j = a + b * j`, the natural number $j$ is cast to ℝ.
- In `range (2 ^ d)` and `Ico (2 ^ (d-k-1)) (2 ^ (d-k))`, the powers are natural numbers.
- In `gridPt` and `lutValue`, `2 ^ d` is the real power. Even if it were computed in ℕ and cast, the value would be the same.
- `f u ^ 2` means $(f(u))^2$.
- `2 * f (u + s) - f u - f (u + 2 * s)` means $(2f(u+s)-f(u))-f(u+2s)$.
- `d - k - 1` means $(d-k)-1$, both truncated.
- The packet has no typeclass assumptions; all types are concrete ($\mathbb R$, $\mathbb N$).

---

## Declarations

**Standing convention**, restated inside each rendering where it matters: for real $a<b$, $\int_a^b g(u)\,du$ denotes the Lebesgue integral of $g$ over the half-open interval $(a,b]$ if $g$ is Lebesgue-integrable there (that is, a.e.-strongly measurable with finite integral of $|g|$), and the number $0$ otherwise.

### 1. `gridPt` (definition)

**Rendering.** For natural numbers $d$ and $j$, $\mathrm{gridPt}(d,j)$ is the real number
$$x^{(d)}_j \;:=\; \frac{j}{2^d},$$
where $j$ is converted to a real number and $2^d$ is a real power. Since $2^d\ge 1$, no division by zero can occur. Nothing ties $j$ to $d$: for $j>2^d$ the point lies to the right of $1$.

### 2. `lutValue` (definition)

**Rendering.** For a function $f:\mathbb R\to\mathbb R$ and natural numbers $d,j$,
$$\mathrm{lutValue}(f,d,j) \;:=\; 2^d\int_{j/2^d}^{(j+1)/2^d} f(u)\,du .$$
Because $j/2^d<(j+1)/2^d$, the integral is the Lebesgue integral of $f$ over the half-open cell $I^{(d)}_j:=\bigl(j/2^d,\,(j+1)/2^d\bigr]$, which has length $2^{-d}$, **provided $f$ is Lebesgue-integrable on that cell; otherwise the integral, and hence $\mathrm{lutValue}(f,d,j)$, is $0$.** Equivalently, when $f$ is integrable on $I^{(d)}_j$, $\mathrm{lutValue}(f,d,j)$ is the mean value of $f$ over $I^{(d)}_j$. There is no restriction on $j$.

### 3. `method1MSE` (definition)

**Rendering.** For $f:\mathbb R\to\mathbb R$ and $d\in\mathbb N$, write $\bar f^{(d)}_j:=\mathrm{lutValue}(f,d,j)=2^d\int_{j/2^d}^{(j+1)/2^d}f(v)\,dv$. Then
$$\mathrm{method1MSE}(f,d)\;:=\;\sum_{j=0}^{2^d-1}\;\int_{j/2^d}^{(j+1)/2^d}\bigl(\bar f^{(d)}_j-f(u)\bigr)^2\,du .$$

- The sum runs over the $2^d$ indices $j=0,1,\dots,2^d-1$. Their cells $I^{(d)}_j=(j/2^d,(j+1)/2^d]$ partition $(0,1]$. For $d=0$ there is a single term, the cell $(0,1]$.
- Each outer integral is the Lebesgue integral over $I^{(d)}_j$ of $u\mapsto(\bar f^{(d)}_j-f(u))^2$, with value $0$ if that function is not integrable on the cell.
- Likewise $\bar f^{(d)}_j=0$ whenever $f$ is not integrable on $I^{(d)}_j$.

### 4. `tendsto_method1MSE` (theorem)

**Rendering.** Let $f:\mathbb R\to\mathbb R$ be any function (implicit argument) such that:

1. **(hmono)** $f$ is non-decreasing on the open interval $(0,1)$: $f(x)\le f(y)$ for all real $x,y$ with $0<x\le y<1$.
2. **(hf)** $f$ is Lebesgue-integrable on $(0,1]$. The Mathlib predicate "interval-integrable on $0..1$" also requires integrability on $(1,0]=\varnothing$, which holds automatically.
3. **(hf2)** $u\mapsto f(u)^2$ is Lebesgue-integrable on $(0,1]$.

Then, as $d\to\infty$ through the natural numbers,
$$\mathrm{method1MSE}(f,d)\;=\;\sum_{j=0}^{2^d-1}\int_{j/2^d}^{(j+1)/2^d}\Bigl(2^d\!\int_{j/2^d}^{(j+1)/2^d}f(v)\,dv\;-\;f(u)\Bigr)^2du\;\longrightarrow\;0 .$$

- All integrals are Lebesgue integrals over the half-open cells $(j/2^d,(j+1)/2^d]$, with the convention that a non-integrable integrand gives $0$.
- No rate of convergence is asserted, and there are no typeclass assumptions.
- `hmono` does not constrain $f(0)$, $f(1)$, or $f$ outside $(0,1)$. Of these values only $f(1)$ enters the integrals at all, and only at the single point $u=1$.

**Assessment.**

- **Truth: true.**
  - Under hf and hf2, $f$ and $f^2$ are integrable on every cell $I^{(d)}_j\subseteq(0,1]$. So $\bar f^{(d)}_j$ is the genuine cell mean, and every integrand $(\bar f^{(d)}_j-f)^2=(\bar f^{(d)}_j)^2-2\bar f^{(d)}_jf+f^2$ is integrable. Hence $\mathrm{method1MSE}(f,d)=\lVert f-P_df\rVert^2_{L^2(0,1]}$, where $P_df$ is the step function equal to $\bar f^{(d)}_j$ on $I^{(d)}_j$.
  - $P_d$ is an orthogonal projection on $L^2(0,1]$, so it has norm at most $1$. For continuous $g$ on $[0,1]$, $\lVert g-P_dg\rVert_\infty\le\omega_g(2^{-d})\to0$, where $\omega_g$ is the modulus of continuity.
  - Given $\varepsilon>0$, choose a continuous $g$ with $\lVert f-g\rVert_2<\varepsilon$. Then $\lVert f-P_df\rVert_2\le\lVert f-g\rVert_2+\lVert g-P_dg\rVert_2+\lVert P_d(g-f)\rVert_2<2\varepsilon+\omega_g(2^{-d})<3\varepsilon$ for large $d$.
  - Alternatively, use $L^2$ martingale convergence for the dyadic filtration. The argument never uses hmono.
- **Non-vacuity: satisfiable with non-trivial data.**
  - $f(u)=u$ satisfies all three hypotheses. The exact value is $\mathrm{method1MSE}=1/(12\cdot4^d)$, verified with rational arithmetic for $d\le 8$.
  - The unbounded $f=\Phi^{-1}$ on $(0,1)$, extended arbitrarily (say by $0$) elsewhere, also works: it is non-decreasing, $\int_0^1\lvert\Phi^{-1}\rvert=2\varphi(0)\approx0.798$ and $\int_0^1(\Phi^{-1})^2=1$.
- **Junk values: no loophole.**
  - Under hf and hf2 every `lutValue` and every outer integral is a genuine Lebesgue integral, so the conclusion is not a junk artefact.
  - The junk convention would matter without hf2. $f(u)=-u^{-1/2}$ satisfies hmono and hf but not hf2.
    - For every $d$ the $j=0$ outer integrand $(\bar f_0+u^{-1/2})^2$ is not integrable on $(0,2^{-d}]$, so that term is the junk value $0$.
    - The other terms equal $\ln(1+1/j)-4(\sqrt{j+1}-\sqrt j)^2$, independent of $d$.
    - So the Lean value of $\mathrm{method1MSE}(f,d)$ increases to about $0.009379>0$, while the true $L^2$ error is $+\infty$.
    - Hence hf2 is essential: without it the conclusion is false.
- **Concerns.**
  - *Qualitative only.* No uniform rate is possible: for $f(u)=-u^{-1/2}/(2-\ln u)$ (monotone on $(0,1)$, with $\int_0^h f^2=1/(2+d\ln2)$ for $h=2^{-d}$), the $j=0$ term alone behaves like $1/(d\ln 2)$. Numerically, $d\cdot V_0\to1/\ln2\approx1.44$.
  - *Redundant hypotheses.*
    - hmono is not needed for truth. hf and hf2 suffice; an antitone indicator function was checked numerically.
    - hf follows from hmono and hf2: a monotone function on $(0,1)$ is a.e.-measurable there (`aemeasurable_restrict_of_monotoneOn`), and $L^2\subset L^1$ on $(0,1]$.
    - So $\{\text{hmono},\text{hf2}\}$ and $\{\text{hf},\text{hf2}\}$ each suffice. $\{\text{hmono},\text{hf}\}$ does not (the example above). $\{\text{hf2}\}$ alone does not either: $f=\pm1$ according to a Bernstein set has $f^2=1$, all cell means are the junk value $0$, and $\mathrm{method1MSE}=1$ for every $d$.
  - `MonotoneOn` is weak monotonicity and holds only on the open interval. The sum always covers all $2^d$ cells of $(0,1]$.

### 5. `dyadic_mse_ge` (theorem)

**Rendering.** Let $f:\mathbb R\to\mathbb R$, $k\in\mathbb N$ and $\mu\in\mathbb R$ (all implicit arguments) satisfy:

1. **(hf)** $f$ is Lebesgue-integrable on $(0,1]$.
2. **(hf2)** $u\mapsto f(u)^2$ is Lebesgue-integrable on $(0,1]$.
3. **(hμ)** $\mu>0$.
4. **(hconc)** For all real numbers $u$ and $s$ with $2^{-(k+1)}\le u$, $0\le s$ and $u+2s\le 2^{-k}$:
$$\mu\,s^2\;\le\;2f(u+s)-f(u)-f(u+2s).$$

Then there exists a real number $c>0$ such that for every natural number $d\ge k+3$ and all real numbers $a,b$:
$$c\;\le\;\sum_{j=2^{d-k-1}}^{2^{d-k}-1}\;\int_{j/2^d}^{(j+1)/2^d}\bigl(a+b\,j-f(u)\bigr)^2\,du .$$

- **Order of quantifiers.** $c$ is chosen after $f,k,\mu$, so it may depend on them. It is chosen before $d,a,b$, so it is the same for all of them.
- **Index range.** $j$ runs over the natural numbers with $2^{d-k-1}\le j<2^{d-k}$, which is $2^{d-k-1}\ge4$ indices. Because $d\ge k+3$, the natural-number differences $d-k-1\ge2$ and $d-k\ge3$ are not truncated.
- **Cells.** The corresponding cells $(j/2^d,(j+1)/2^d]$ partition $(2^{-(k+1)},2^{-k}]$.
- **The affine term.** $a+b\,j$ uses the index $j$ itself, converted to a real number, not the grid point $j/2^d$.
- **Integrals.** Each integral is the Lebesgue integral over its cell, with value $0$ if the integrand is not integrable there. There are no typeclass assumptions.

**Assessment.**

- **Truth: true, with the explicit constant $c=\mu^2\,2^{-5k-18}$.** Sketch:
  - *Setup.* Let $N=2^{d-k-1}\ge4$, $h=2^{-d}$, $m=\lfloor N/3\rfloor\ge1$ and $s=mh$. Let $e(v)=a+b\,j(v)-f(v)$, where $j(v)$ is the index of the cell containing $v$.
  - *Pointwise bound.* For $u$ in cell $j\in[N,N+m)$, the points $u+s$ and $u+2s$ lie in cells $j+m$ and $j+2m$. We have $u>2^{-(k+1)}$ and $u+2s\le(N+3m)h\le2^{-k}$, so hconc applies. The affine values cancel in the second difference: $2f(u+s)-f(u)-f(u+2s)=e(u)-2e(u+s)+e(u+2s)$. Hence $\mu s^2\le|e(u)|+2|e(u+s)|+|e(u+2s)|$. By weighted Cauchy–Schwarz, $\mu^2s^4\le4\bigl(e(u)^2+2e(u+s)^2+e(u+2s)^2\bigr)$.
  - *Summing.* Integrate over cell $j$ and use translation invariance. Then sum over the $m$ indices $j\in[N,N+m)$. The three shifted index ranges are disjoint subsets of $[N,2N)$. This gives $m h\,\mu^2 s^4\le 8\sum_{j=N}^{2N-1}\int_{\text{cell }j}e^2$, that is, $\text{sum}\ge\mu^2(mh)^5/8$.
  - *Uniform constant.* $mh=(\lfloor N/3\rfloor/N)\,2^{-(k+1)}\ge2^{-(k+3)}$ for $N\ge4$. So $\text{sum}\ge\mu^2 2^{-5k-18}$, uniformly in $d,a,b$.
  - *Integrability* of $e^2$ on each block cell comes from hf and hf2.
  - *Numerical confirmation.*
    - For $f=-u^2$ (exact rationals, $k=0..3$) and for $\Phi^{-1}$ ($k=2,3,4$), the minimum over $(a,b)$ of the sum stays above $c$ for every $d$ tested. For $f=-u^2$ that is $d=k+3..k+12$; for $\Phi^{-1}$ it is $d=k+3..k+18$.
    - The minimum decreases to a positive limit. For $-u^2$ the limit is $L^5/180$ with $L=2^{-(k+1)}$, matched to a relative error of $3\times10^{-5}$.
- **Non-vacuity: satisfiable with non-trivial data.**
  - $f(u)=-u^2$ with $\mu=2$ and any $k$: $2f(u+s)-f(u)-f(u+2s)=2s^2$ identically, and $f$ is bounded, so hf and hf2 hold.
  - A monotone example is $f=\Phi^{-1}$ on $(0,1)$ (arbitrary elsewhere) with $k\ge2$ and $\mu=-(\Phi^{-1})''(2^{-k})=\lvert x\rvert/\varphi(x)^2$ at $x=\Phi^{-1}(2^{-k})$. This gives $\mu\approx6.679$ for $k=2$, $27.15$ for $k=3$ and $101.4$ for $k=4$, and was checked on a grid of $(u,s)$.
- **Junk values: no loophole.**
  - The conclusion is a lower bound, so junk values $0$ could only decrease the right-hand side.
  - Under the hypotheses all block-cell integrands are integrable.
  - There is no natural-number truncation, since $d\ge k+3$, and no inverse of $0$.
- **Concerns.**
  - *The approximant is piecewise constant.* It has one value per cell, and it is constrained only on the cells covering $(2^{-(k+1)},2^{-k}]$. Since $a$ and $b$ range over all reals, "affine in the index $j$" is the same class as "affine in the grid point $j/2^d$", with the slope rescaled by $2^d$.
  - *hconc is a condition on the closed block $[2^{-(k+1)},2^{-k}]$ only.* For $C^2$ functions it is equivalent to $f''\le-\mu$ on the block. Nothing is assumed about $f$ elsewhere except integrability, and no monotonicity is assumed.
    - For $f=\Phi^{-1}$, hconc holds for some $\mu>0$ exactly when $k\ge2$.
    - For $k=1$ the second-difference ratio tends to $0$ near $u=1/2$, because $(\Phi^{-1})''(1/2)=0$.
    - For $k=0$ the ratio is negative, because $\Phi^{-1}$ is convex on $[1/2,1)$. That block also contains $u=1$, where Lean's $f(1)$ is an arbitrary real.
  - *Small $d$.* The theorem says nothing about $d\le k+2$. With at most 2 block cells, $a+bj$ can match the cell means exactly.
  - *Partial redundancy of hf and hf2.* Given hconc, $f$ is midpoint-concave on the block. If $f$ is also bounded below on a set of positive measure, which follows from either hf or hf2, then $f$ is continuous in the interior of the block and bounded on the closed block (Bernstein–Doetsch/Ostrowski). So either hypothesis alone suffices.
  - *Neither can be dropped together.* $f(u)=-u^2+A(u)$, with $A$ additive and discontinuous (a Hamel-basis construction, available in Lean's classical logic), satisfies hconc with $\mu=2$. But every block-cell integrand is then non-measurable, so every integral is the junk value $0$ and the sum is $0<c$.

### 6. `method3_mse_ge` (theorem)

**Rendering.** Let $f:\mathbb R\to\mathbb R$, $k\in\mathbb N$, $\mu\in\mathbb R$ (implicit) satisfy the same four hypotheses as in `dyadic_mse_ge`:

1. **(hf)** $f$ is Lebesgue-integrable on $(0,1]$.
2. **(hf2)** $f^2$ is Lebesgue-integrable on $(0,1]$.
3. **(hμ)** $\mu>0$.
4. **(hconc)** $\mu s^2\le2f(u+s)-f(u)-f(u+2s)$ for all real $u,s$ with $2^{-(k+1)}\le u$, $0\le s$ and $u+2s\le2^{-k}$.

Then there exists a real number $c>0$ with the following property. For every natural number $d\ge k+3$ and every function $w:\mathbb N\to\mathbb R$: **if** there exist real numbers $a,b$ with $w(j)=a+b\,j$ for every natural $j$ with $2^{d-k-1}\le j<2^{d-k}$, **then**
$$c\;\le\;\sum_{j=0}^{2^d-1}\int_{j/2^d}^{(j+1)/2^d}\bigl(w(j)-f(u)\bigr)^2\,du .$$

- **Order of quantifiers.** $c$ is chosen after $f,k,\mu$ and before $d,w,a,b$. The pair $(a,b)$ is existentially quantified inside the hypothesis on $w$, separately for each $d$ and $w$.
- **What is unconstrained.** The values $w(j)$ for $j$ outside $[2^{d-k-1},2^{d-k})$ are arbitrary. Values for $j\ge2^d$ do not enter.
- **The sum** covers all $2^d$ cells of $(0,1]$. Integrals follow the same convention as before: Lebesgue integral over $(j/2^d,(j+1)/2^d]$, and $0$ if the integrand is not integrable.

**Assessment.**

- **Truth: true, with the same $c$ as `dyadic_mse_ge`.**
  - Because $2^{d-k}\le 2^d$, the block indices form a subset of $\{0,\dots,2^d-1\}$.
  - Every term of the full sum is $\ge0$ (`intervalIntegral.integral_nonneg`). This holds for a genuine value or a junk $0$ alike.
  - On the block $w(j)=a+bj$, so the block part is at least $c$ by `dyadic_mse_ge`.
  - Numerically: 100 random admissible $w$ (exact, $f=-u^2$, $k=1$, $d=7$) all give $\text{sum}\ge\inf_w\ge c$.
- **Non-vacuity.** $f=-u^2$, $\mu=2$, any $k$, and $w\equiv0$ (so $a=b=0$). Or take $w$ equal to the cell means off the block and to the least-squares affine fit on the block.
- **Junk values.** None. As before, junk values could only lower the right-hand side. Off-block cells contribute $\ge0$ in either case, and under hf and hf2 they are genuine anyway.
- **Concerns.**
  - Only one block, fixed by $k$, is constrained; $w$ is free elsewhere.
  - The infimum over admissible $w$ equals $\mathrm{method1MSE}(f,d)$ plus the affine-fit residual on the block. It converges to the same positive limit as in `dyadic_mse_ge` (numerically $5.425\times10^{-6}$ for $-u^2$ with $k=1$, and $7.077\times10^{-6}$ for $\Phi^{-1}$ with $k=2$).
  - Redundancy of hf and hf2: as in `dyadic_mse_ge`.

### 7. `method3_mse_not_tendsto_zero` (theorem)

**Rendering.** Let $f:\mathbb R\to\mathbb R$, $k\in\mathbb N$, $\mu\in\mathbb R$ (implicit) satisfy the four hypotheses of `dyadic_mse_ge`:

1. **(hf)** $f$ is integrable on $(0,1]$.
2. **(hf2)** $f^2$ is integrable on $(0,1]$.
3. **(hμ)** $\mu>0$.
4. **(hconc)** $\mu s^2\le2f(u+s)-f(u)-f(u+2s)$ whenever $2^{-(k+1)}\le u$, $0\le s$ and $u+2s\le2^{-k}$.

Also let $w:\mathbb N\times\mathbb N\to\mathbb R$, written $(d,j)\mapsto w_d(j)$, be an explicit argument satisfying:

5. **(hw)** For every natural number $d$ there exist real numbers $a_d,b_d$ with $w_d(j)=a_d+b_d\,j$ for every natural $j$ with $2^{(d\mathbin{\dot{-}}k)\mathbin{\dot{-}}1}\le j<2^{d\mathbin{\dot{-}}k}$. Here $x\mathbin{\dot{-}}y=\max(x-y,0)$ is truncated subtraction on $\mathbb N$. The index set is:
   - $\varnothing$ for $d\le k$;
   - $\{1\}$ for $d=k+1$;
   - $\{2,3\}$ for $d=k+2$;
   - the $2^{d-k-1}$ indices $2^{d-k-1},\dots,2^{d-k}-1$ for $d\ge k+3$.

Then it is **not** the case that
$$E_d\;:=\;\sum_{j=0}^{2^d-1}\int_{j/2^d}^{(j+1)/2^d}\bigl(w_d(j)-f(u)\bigr)^2\,du\;\longrightarrow\;0\qquad(d\to\infty).$$
The integrals follow the usual convention: Lebesgue integral over the half-open cell, and $0$ if the integrand is not integrable.

**Assessment.**

- **Truth: true.**
  - For each $d\ge k+3$, hw supplies $(a_d,b_d)$. `method3_mse_ge`, applied with $w=w_d$, then gives $E_d\ge c>0$ for all $d\ge k+3$.
  - So the tail of $(E_d)$ never enters $(-c,c)$, and $E_d\not\to0$.
- **Non-vacuity.** $f=-u^2$, $\mu=2$, $k=1$ and $w\equiv0$ satisfy everything, and so do the optimal admissible families.
  - Numerically, $\inf_{w}E_d\to5.425\times10^{-6}>0$ for $-u^2$ with $k=1$, where the limit is $L^5/180$ with $L=1/4$.
  - For $\Phi^{-1}$ with $k=2$ the limit is $7.077\times10^{-6}$.
- **Junk values.** A junk $0$ would push $E_d$ *towards* $0$, that is, against the conclusion; under the hypotheses all integrals are genuine anyway. The truncation in hw only makes hw vacuous for $d\le k+2$, which cannot affect a statement about the limit.
- **Concerns.**
  - hw imposes nothing for $d\le k+2$. For $d\le k$ the index set is empty, and one or two points can always be fitted by an affine function.
  - The conclusion is weaker than what is available: it says only that $E_d$ does not tend to $0$, while `method3_mse_ge` gives $E_d\ge c$ for all $d\ge k+3$. The theorem does not claim that $E_d$ converges.
  - Removing both hf and hf2 makes it false: the Hamel-type $f$ from §5 gives $E_d=0$ for all $d$.

---

## Numerical sanity checks

Scripts are in `readback/round7/work_G/`: pure Python 3.11, standard library only (`fractions`, `math`, `statistics.NormalDist`). Each script's output is saved next to it as `*.out`. **No check failed.**

**Method.** For a constant $c$ on a cell of length $h$, with $F=\int f$ and $G=\int f^2$ over the cell,
$$\int(c-f)^2=\bigl[G-F^2/h\bigr]+h\,(c-F/h)^2 .$$
So the minimum over $(a,b)$ is the sum of within-cell variances plus a $2\times2$ least-squares residual of the cell means. Cell integrals of $\Phi^{-1}$ use closed forms: $\int\Phi^{-1}=-\varphi(\Phi^{-1})$ and $\int(\Phi^{-1})^2=u-\Phi^{-1}\varphi(\Phi^{-1})$. One cell was cross-checked by Gauss–Legendre quadrature (agreement to $10^{-7}$ relative, which is the float cancellation level).

| Script | Instance | Result |
|---|---|---|
| `check_method1.py` (a) | $f(u)=u$, exact | $\mathrm{method1MSE}(d)=1/(12\cdot4^d)$ exactly, $d=0..8$ |
| (b) | $f=\Phi^{-1}$ | $1.000,\;0.363,\;0.139,\dots,\;1.48\times10^{-6}$ at $d=16$; ratio per step $\to\approx0.47$, heading towards $1/2$ |
| (c) | $f=-u^{-1/4}$ (monotone, unbounded, $L^2$) | $\to0$ like $2^{-d/2}$ (ratio per 2 steps $=0.500$) |
| (d) | indicator of $(0,1/3]$ (antitone), exact | $\to0$, always $\le 2^{-d}/4$: monotonicity is not needed |
| (e) | $f=-u^{-1/2}$ (hmono and hf hold, **hf2 fails**) | Lean value (junk $0$ on cell 0) is $0,\;0.00873,\;0.00934,\dots\to0.0093793>0$: **the conclusion fails without hf2** |
| (f) | $f=-u^{-1/2}/(2-\ln u)$ (hmono, hf, hf2 hold) | $j=0$ term $V_0$: $d\,V_0=0.14,\,0.44,\,0.93,\,1.27,\,1.40$ at $d=1,4,16,64,256$, tending to $1/\ln2$: the rate can be as slow as about $1/d$ |
| `check_dyadic.py` (a) | $f=-u^2$, $\mu=2$, $k=0..3$, exact | hconc is an identity ($=2s^2$). $\min_{a,b}$ of the sum $\ge c=\mu^2 2^{-5k-18}$ for all $d=k+3..k+12$; min/limit $=9.44,3.11,1.53,1.13,\dots,1.00003$, with limit $L^5/180$ |
| (b) | $f=\Phi^{-1}$, $k=2,3,4$ | $\mu_k=6.679,\,27.146,\,101.43$; hconc verified on a $200\times200$ $(u,s)$ grid; $\min_{a,b}$ of the sum decreases to $7.0767\times10^{-6}$, $3.2479\times10^{-6}$, $1.3991\times10^{-6}$ respectively, always $\ge c$ ($1.7\times10^{-7}$, $8.6\times10^{-8}$, $3.7\times10^{-8}$) |
| (c) | $\Phi^{-1}$, $k=1$ and $k=0$ | $k=1$: ratio $0.197\to0.0197\to0.00197$ as $u+s\to1/2$ (no $\mu>0$ works). $k=0$: ratio about $-6.68<0$ |
| (d) | 200 random $(a,b)$, $f=-u^2$, exact | the sum is always $\ge$ the computed minimum, and the direct evaluation at the optimum equals it exactly |
| `check_method3.py` (a) | index sets, $k=2$ | $d=0,1,2$: $\varnothing$; $d=3$: $\{1\}$; $d=4$: $\{2,3\}$; $d=5$: $\{4,\dots,7\}$ (truncated subtraction confirmed) |
| (b) | $f=-u^2$, $k=1$, exact | $\inf_w E_d$: $0.0889,\dots,1.73\times10^{-3}$ for $d\le3$ (constraint vacuous), then $4.4\times10^{-4},\dots,5.4258\times10^{-6}$ at $d=14$, tending to $L^5/180=5.4253\times10^{-6}>0$; always $\ge c$ for $d\ge4$ |
| (c) | $f=\Phi^{-1}$, $k=2$ | $\inf_w E_d\to7.0767\times10^{-6}>0$; the method1 part $\to0$ while the block residual stays near $7.08\times10^{-6}$ |
| (d) | 100 random admissible $w$, exact | the full sum $\ge\inf_w E_d\ge c$ in every case |

**Numerical conclusion.**
- All four theorems behave as stated on every instance tested.
- The only failures observed are the intended negative controls: (e), where hf2 is dropped, and (c), where hconc fails for $\Phi^{-1}$ with $k\le1$. In both cases a hypothesis is violated, not a theorem.
