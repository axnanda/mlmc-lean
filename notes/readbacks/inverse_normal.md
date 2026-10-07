# Blind read-back report: R20 (inverse normal CDF and lookup tables)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round18/packet_R20_invnormal.lean` |
| declarations audited | 48 (33 theorems + 15 definitions: `normCDF`, `normCDFInv` and the 13 appended definitions) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round18/work_R20/` (`check_basic.py`, `check_block.py`, `check_method1.py`, `check_method1_asym.py`, `check_method3.py`, helper `common.py`, each with its `.out`; Lean scratch files `Scratch.lean`/`.out` (elaboration of the packet) and `Junk.lean`/`.out` (junk values, compiled with no errors)) |

Notation: $\Phi$ is the standard normal CDF, $\varphi(x)=(2\pi)^{-1/2}e^{-x^2/2}$ its density, $F=\Phi^{-1}$,
$h=2^{-d}$, cell $j$ of level $d$ is $C_{d,j}=[j2^{-d},(j+1)2^{-d}]$, and block $k$ is $B_k=[2^{-(k+1)},2^{-k}]$.

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| D1 | `normCDF` | def | n/a ($=\Phi$) | n/a | no |
| D2 | `normCDFInv` | def | n/a ($=\Phi^{-1}$ on $(0,1)$, $0$ elsewhere) | n/a | the junk value $0$ is part of the definition |
| D3 | `gridPt` | def | n/a | n/a | no |
| D4 | `lutValue` | def | n/a (cell average) | n/a | no |
| D5 | `method1MSE` | def | n/a | n/a | no |
| D6 | `method3MSE` | def | n/a | n/a | no |
| D7 | `method3Limit` | def | n/a | n/a | no (the series is summable) |
| D8 | `method3Value` | def | n/a | n/a | no |
| D9 | `dyadicAffineErr` | def | n/a | n/a | no |
| D10 | `method3Half` | def | n/a | n/a | no |
| D11 | `dyadicMomentLim` | def | n/a | n/a | no |
| D12 | `lsqFit` | def | n/a | n/a | no |
| D13 | `dyadicGroup` | def | n/a | n/a | no |
| D14 | `finMean` | def | n/a | n/a | no |
| D15 | `lsqSlope` | def | n/a | n/a | no |
| 1 | `hasDerivAt_normCDF` | theorem | true | no | no |
| 2 | `continuous_normCDF` | theorem | true | no | no |
| 3 | `strictMono_normCDF` | theorem | true | no | no |
| 4 | `tendsto_normCDF_atBot` | theorem | true | no | no |
| 5 | `tendsto_normCDF_atTop` | theorem | true | no | no |
| 6 | `normCDF_neg` | theorem | true | no | no |
| 7 | `normCDF_normCDFInv` | theorem | true | no | no |
| 8 | `normCDFInv_normCDF` | theorem | true | no | no |
| 9 | `strictMonoOn_normCDFInv` | theorem | true | no | no |
| 10 | `normCDFInv_one_sub` | theorem | true | no | no (hypothesis `hu` is superfluous: outside $(0,1)$ the identity also holds, via $0=-0$) |
| 11 | `map_normCDFInv` | theorem | true | no | no |
| 12 | `hasLaw_normCDFInv` | theorem | true | no | no |
| 13 | `hasLaw_normCDFInv_comp` | theorem | true | no | no |
| 14 | `intervalIntegrable_normCDFInv` | theorem | true | no | no |
| 15 | `hasDerivAt_normCDFInv` | theorem | true | no | no |
| 16 | `deriv_normCDFInv` | theorem | true | no | no |
| 17 | `deriv_deriv_normCDFInv_le` | theorem | true | no | no |
| 18 | `concaveOn_normCDFInv_add_sq` | theorem | true | no | no |
| 19 | `normCDFInv_second_diff` | theorem | true | no | no |
| 20 | `normCDFInv_dyadic_concave` | theorem | true | no | no |
| 21 | `lutValue_mirror_normCDFInv` | theorem | true | no | no |
| 22 | `lutValue_upper_half_normCDFInv` | theorem | true | no | no |
| 23 | `tendsto_method1MSE_normCDFInv` | theorem | true | no | no |
| 24 | `lutStream_normCDFInv_tendstoInDistribution` | theorem | true | no | no |
| 25 | `lutStreams_sum_normCDFInv_tendstoInDistribution` | theorem | true | no | no |
| 26 | `dyadic_mse_ge_normCDFInv` | theorem | true | no | no |
| 27 | `method3_mse_ge_normCDFInv` | theorem | true | no | no |
| 28 | `tendsto_method3MSE_normCDFInv` | theorem | true | no | no |
| 29 | `exp_mul_gaussianPDFReal_le` | theorem | true | no | no |
| 30 | `neg_mul_normCDF_le` | theorem | true | no | no |
| 31 | `normCDFInv_block_bounds` | theorem | true | no | no |
| 32 | `method1MSE_order_normCDFInv` | theorem | true | no | no |
| 33 | `tendsto_log_method1MSE_normCDFInv` | theorem | true | no | no |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.** All 33 theorems are true as stated. Every
   hypothesis set has a concrete instance, and every numerical constant was checked with mpmath.
2. **Junk value of the inverse.** `normCDFInv u = 0` for every $u\notin(0,1)$, so $\Phi^{-1}(0)=\Phi^{-1}(1)=0$
   instead of $\mp\infty$ (checked in Lean: `Junk.lean`). No theorem relies on this. The pointwise statements
   are restricted to $(0,1)$, $(0,\tfrac14]$ or blocks inside $(0,\tfrac12]$. The integrals see
   $\{0,1\}$ only as a null set, and $\lfloor 2^dU\rfloor_+<2^d$ almost surely. Three hypotheses really are
   needed to keep out the junk: `0 < u` in #17–#19 (#17 would be false at $u=0$, where
   `deriv (deriv normCDFInv) 0 = 0`; #18 would be false if $0$ were in the interval) and `j < 2^d` in #21
   (for $j\ge 2^d$ the left side is `lutValue … 0` $<0$ while the right side is $-0$). The hypothesis of #10
   is unnecessary, because the identity also holds outside $(0,1)$ through $0=-0$ (proved in `Junk.lean`).
   This is harmless.
3. **Constants (all correct, with slack).** $(\Phi^{-1})''\le-\pi$ on $(0,\tfrac14]$: the true supremum is
   $-6.6793$, reached at $u=\tfrac14$. Second difference $\ge\pi s^2$: the observed minimum ratio is $2.13$.
   Mills lower bound $e^{-3/2}=0.2231$: the true infimum of $-x\Phi(x)/\varphi(x)$ over $x\le-1$ is $0.6557$,
   at $x=-1$. Mills upper bound: the standard $\Phi(x)\le\varphi(x)/|x|$. Block bounds: the ratio
   $m(F(v)-F(u))^2/(2^m(v-u))^2$ lies in $[0.7213,\,3.179]$, against the claimed $[(4e^4)^{-1},\,8(4+2\pi e)]=[0.00458,\,168.6]$.
4. **The MSEs are genuine.** $F\in L^2(0,1)$ with $\int_0^1F=0$ and $\int_0^1F^2=1$ (#14), so every cell
   integral of $(c-F)^2$ is a true integral and not the junk value of a non-integrable function. Closed forms
   and direct quadrature of the definitions agree to 12–15 digits.
5. **What the asymptotics mean.**
   - #32 is a two-sided $\Theta(2^{-d}/d)$ bound with fixed $c,K>0$ for all $d\ge2$. It is not an asymptotic
     equivalence. Numerically $d\,2^d\,\mathrm{MSE}_1(d)\in[1.116,\,1.575]$ for $2\le d\le400$, and it seems to
     settle near $1.56$. Starting at $d\ge2$ is needed in Lean only to avoid $d=0$, where $1/0=0$ would make
     the upper bound read $\mathrm{MSE}\le0$.
   - #33 gives only the exponential rate, $\log\mathrm{MSE}_1(d)/d\to-\log2$. It cannot see the $1/d$ factor
     and is strictly weaker than #32. Convergence is slow: $-0.82$ at $d=20$, $-0.707$ at $d=400$.
   - #28 says the method-3 limit exists, equals the explicit series
     $2\sum_{k\ge1}\operatorname{dist}^2_{L^2(B_k)}(F,\text{affine})\approx4.133\times10^{-5}$, and is positive.
     Positivity also rules out the junk `tsum = 0`. Numerically
     $\mathrm{MSE}_3(16)-\lim=1.48\times10^{-6}$, and the gap halves with each level.
   - #26/#27: the lower bound $c$ holds uniformly over all $d\ge k+3$ and over all affine-in-$j$ tables. The
     minimum over $(a,b)$ decreases in $d$ towards `dyadicAffineErr k` (for example $7.077\times10^{-6}$ for
     $k=2$), so the best $c$ is about that value.
6. **Minor remarks (not defects).**
   - The bound $-\pi$ in #17 is far from sharp.
   - #20 is #19 restricted to a dyadic block. Its hypotheses `2 ≤ k` and $2^{-(k+1)}\le u$ are stronger than
     needed.
   - Part (a) of #25 does not use independence; part (b) does.
   - In #13, $P$ is not assumed to be a probability measure, but `HasLaw` forces $P(\Omega)=1$.

---

## Definitions

### D1 `normCDF`
**Rendering.** `normCDF x = cdf (gaussianReal 0 1) x`. Mathlib's `cdf μ` is a `StieltjesFunction`, and for a
probability measure `cdf μ x = μ.real (Iic x)`. Since `gaussianReal 0 1` is $\mathcal N(0,1)$ (variance $1\ne0$,
so not the Dirac branch), this is $\Phi(x)=\mathcal N(0,1)((-\infty,x])$.

### D2 `normCDFInv`
**Rendering.** `(Ioo 0 1).indicator (Function.invFun normCDF) u`: this is $\Phi^{-1}(u)$ for $u\in(0,1)$ and $0$
otherwise. `Function.invFun` returns a chosen preimage when one exists. $\Phi$ is a bijection
$\mathbb R\to(0,1)$, so on $(0,1)$ this is the true inverse. **Junk:** $\Phi^{-1}(u)=0$ for $u\le0$ or $u\ge1$, in
particular $\Phi^{-1}(0)=\Phi^{-1}(1)=0$ (Lean-checked in `Junk.lean`, together with `lutValue normCDFInv d j = 0`
for $j\ge2^d$, which describes cells outside $[0,1]$).

### D3 `gridPt`
**Rendering.** $\mathrm{gridPt}(d,j)=j/2^d\in\mathbb R$.

### D4 `lutValue`
**Rendering.** $\mathrm{lutValue}(f,d,j)=2^d\int_{j2^{-d}}^{(j+1)2^{-d}}f(u)\,du$, the average of $f$ over cell $C_{d,j}$
(the $L^2$-optimal constant on the cell). If $f$ were not integrable on the cell, the interval integral would
be the junk value $0$. For $F$ it is integrable (#14).

### D5 `method1MSE`
**Rendering.** $\mathrm{MSE}_1(f,d)=\sum_{j=0}^{2^d-1}\int_{C_{d,j}}(\mathrm{lutValue}(f,d,j)-f(u))^2\,du$. This is
the squared $L^2(0,1)$ error of the piecewise-constant table of cell averages ("method 1"). For $f=F$ it
equals $1-2^d\sum_j(\varphi(x_j)-\varphi(x_{j+1}))^2$ with $x_j=F(j2^{-d})$, a closed form I checked against
direct quadrature.

### D6 `method3MSE`
**Rendering.** $\mathrm{MSE}_3(f,d)=\sum_{j<2^d}\int_{C_{d,j}}(\mathrm{method3Value}(f,d,j)-f)^2$.

### D7 `method3Limit`
**Rendering.** $2\sum'_{k\ge0}\mathrm{dyadicAffineErr}(f,k+1)=2\sum_{k\ge1}\mathrm{dyadicAffineErr}(f,k)$, over the
blocks $[\tfrac14,\tfrac12],[\tfrac18,\tfrac14],\dots$. `∑'` is $0$ when the series is not summable. For $F$ the
terms lie between $0$ and $\int_{B_k}F^2$, so the series is summable. Its value is $4.13297\times10^{-5}$.

### D8 `method3Value`
**Rendering.** For $j<2^{d-1}$ (ℕ-subtraction, so $2^{0}=1$ when $d=0$) the value is $\mathrm{method3Half}(f,d,j)$.
Otherwise it is $-\mathrm{method3Half}(f,d,2^d-1-j)$, an antisymmetric mirror of the lower half. That is
exact for $F$, since $F(1-u)=-F(u)$.

### D9 `dyadicAffineErr`
**Rendering.** $\int_{B_k}f^2-2^{k+1}\big(\int_{B_k}f\big)^2-12\cdot8^{k+1}M_k^2$, where
$M_k=\int_{B_k}(u-\tfrac{3}{2^{k+2}})f(u)\,du$. Here $|B_k|=L=2^{-(k+1)}$, the midpoint is $3/2^{k+2}$ and
$\int_{B_k}(u-\text{mid})^2=L^3/12$, so this is exactly $\min_{\alpha,\beta}\int_{B_k}(f-\alpha-\beta u)^2$, the squared
$L^2$ distance from $f$ to affine functions on $B_k$. Numerically checked: for $k=1,2,3$ the closed form,
direct quadrature and an independent normal-equation fit all agree.

### D10 `method3Half`
**Rendering.** The least-squares affine-in-$j$ fit of the table values $\mathrm{lutValue}(f,d,\cdot)$ over the
dyadic index group of $j$, evaluated at $j$.

### D11 `dyadicMomentLim`
**Rendering.** $M_k=\int_{2^{-(k+1)}}^{2^{-k}}(u-3/2^{k+2})f(u)\,du$, the first moment about the block midpoint.

### D12 `lsqFit`
**Rendering.** $\bar y_S+\mathrm{slope}_S(y)\,(j-\bar\imath_S)$, the ordinary least-squares line through
$\{(i,y_i):i\in S\}$, evaluated at $j$.

### D13 `dyadicGroup`
**Rendering.** $\{0,1\}$ if $j<2$, otherwise $[2^{\lfloor\log_2 j\rfloor},2^{\lfloor\log_2j\rfloor+1})$. Within the lower
half at level $d$, the index group $[2^m,2^{m+1})$ is the $u$-block $B_{d-1-m}$, and $\{0,1\}$ is $[0,2^{1-d}]$.

### D14 `finMean`
**Rendering.** $(\sum_{j\in S}y_j)/|S|$ (equal to $0$ if $S=\emptyset$ by $x/0=0$; this never happens for the groups used).

### D15 `lsqSlope`
**Rendering.** $\sum_S(j-\bar\imath)y_j/\sum_S(j-\bar\imath)^2$, the OLS slope (the denominator is positive since $|S|\ge2$).

---

## Theorems

### 1 `hasDerivAt_normCDF`
**Rendering.** For every $x\in\mathbb R$, $\Phi'(x)=\varphi(x)$ (`gaussianPDFReal 0 1 x` $=(\sqrt{2\pi})^{-1}e^{-x^2/2}$).
**Assessment.** True by the fundamental theorem of calculus, since the density is continuous. There are no
hypotheses, so it is not vacuous, and no junk value is involved. This is the standard fact $\Phi'=\varphi$.

### 2 `continuous_normCDF`
**Rendering.** $\Phi$ is continuous. **Assessment.** True (it follows from #1). Standard.

### 3 `strictMono_normCDF`
**Rendering.** $x<y\Rightarrow\Phi(x)<\Phi(y)$. **Assessment.** True, because $\varphi>0$ everywhere. Standard.

### 4 `tendsto_normCDF_atBot`
**Rendering.** $\Phi(x)\to0$ as $x\to-\infty$. **Assessment.** True (Mathlib `tendsto_cdf_atBot`). Standard.

### 5 `tendsto_normCDF_atTop`
**Rendering.** $\Phi(x)\to1$ as $x\to+\infty$. **Assessment.** True. Standard.

### 6 `normCDF_neg`
**Rendering.** For every $x$, $\Phi(-x)=1-\Phi(x)$. **Assessment.** True by symmetry of $\mathcal N(0,1)$, which has
no atoms. The numerical maximum deviation is $10^{-41}$ (`check_basic.out`). Standard.

### 7 `normCDF_normCDFInv`
**Rendering.** For $u\in(0,1)$, $\Phi(\Phi^{-1}(u))=u$.
**Assessment.** True: $\Phi$ maps onto $(0,1)$ by the intermediate value theorem and #4/#5, so `invFun`
returns a genuine preimage. The hypothesis is necessary, because for $u\notin(0,1)$ the left side is
$\Phi(0)=\tfrac12\neq u$. Instance: $u=\tfrac12$. Not junk-dependent.

### 8 `normCDFInv_normCDF`
**Rendering.** For every $x$, $\Phi^{-1}(\Phi(x))=x$. **Assessment.** True, because $\Phi(x)\in(0,1)$ and $\Phi$ is
injective. There are no hypotheses. Not junk-dependent (numerical deviation $4\times10^{-31}$).

### 9 `strictMonoOn_normCDFInv`
**Rendering.** $\Phi^{-1}$ is strictly increasing on $(0,1)$. **Assessment.** True (the inverse of a strictly
increasing bijection). The restriction to $(0,1)$ is essential, since outside it the function is the constant $0$. Standard.

### 10 `normCDFInv_one_sub`
**Rendering.** For $u\in(0,1)$, $\Phi^{-1}(1-u)=-\Phi^{-1}(u)$.
**Assessment.** True by #6 and injectivity (numerical deviation $10^{-40}$). Instance: $u=0.3$. Not
junk-dependent. **The hypothesis is superfluous:** for $u\notin(0,1)$ we also have $1-u\notin(0,1)$, so both
sides equal $0$ (proved in `Junk.lean`). This only makes the stated result weaker than what holds. Standard
symmetry of normal quantiles.

### 11 `map_normCDFInv`
**Rendering.** The pushforward of Lebesgue measure restricted to $(0,1)$ (the uniform law) under $\Phi^{-1}$ is
$\mathcal N(0,1)$.
**Assessment.** True: this is inverse-transform sampling. For $x\in\mathbb R$,
$\lambda\{u\in(0,1):\Phi^{-1}(u)\le x\}=\lambda((0,\Phi(x)])=\Phi(x)$. `Measure.map` of a non-AEMeasurable map
would be $0\ne\mathcal N(0,1)$, so the statement also certifies measurability. The values at $0$ and $1$ live on
a null set. Not junk-dependent.

### 12 `hasLaw_normCDFInv`
**Rendering.** `HasLaw normCDFInv (gaussianReal 0 1) (volume.restrict (Ioo 0 1))`: $\Phi^{-1}$ is AEMeasurable and
its law under $U(0,1)$ is $\mathcal N(0,1)$. **Assessment.** True (#11). Standard.

### 13 `hasLaw_normCDFInv_comp`
**Rendering.** For any measurable space $(\Omega,P)$ and $U:\Omega\to\mathbb R$ with law $U(0,1)$ under $P$, the
variable $\Phi^{-1}(U)$ has law $\mathcal N(0,1)$ under $P$.
**Assessment.** True (#12 composed with `HasLaw.comp`). $P$ is not assumed to be a probability measure, but
`HasLaw` forces $P(\Omega)=1$. Instance: $\Omega=\mathbb R$, $P=\lambda|_{(0,1)}$, $U=\mathrm{id}$. Not junk-dependent,
since $U\in\{0,1\}$ has probability $0$. Inverse-transform sampling.

### 14 `intervalIntegrable_normCDFInv`
**Rendering.** $\Phi^{-1}$ and $(\Phi^{-1})^2$ are Lebesgue integrable on $[0,1]$.
**Assessment.** True: $\int_0^1(\Phi^{-1})^2=\int x^2\varphi(x)\,dx=1$ (numerically $1.0$ both in $x$-space and via
$u$-space quadrature with explicit tails), and $L^2\subset L^1$ on a finite measure space. This is what makes
all the MSE quantities genuine. Standard ($\mathbb E Z^2=1$).

### 15 `hasDerivAt_normCDFInv`
**Rendering.** For $u\in(0,1)$, $(\Phi^{-1})'(u)=1/\varphi(\Phi^{-1}(u))$.
**Assessment.** True by the inverse function theorem ($\Phi'=\varphi>0$). $(0,1)$ is open, so the junk values
outside do not matter. Numerically confirmed at $u=0.001,0.1,0.25,0.6$ to 12 digits. Instance: $u=\tfrac12$.

### 16 `deriv_normCDFInv`
**Rendering.** For $u\in(0,1)$: (i) `deriv normCDFInv u` $=1/\varphi(x)$ with $x=\Phi^{-1}(u)$; (ii) the function
`deriv normCDFInv` has derivative $x/\varphi(x)^2$ at $u$; (iii) `deriv (deriv normCDFInv) u` $=x/\varphi(x)^2$.
**Assessment.** True. `deriv normCDFInv` agrees with $1/\varphi(\Phi^{-1})$ on the open set $(0,1)$, and
$\frac{d}{du}\varphi(x(u))^{-1}=-\varphi'(x)x'(u)/\varphi(x)^2=x\varphi(x)\cdot\varphi(x)^{-1}/\varphi(x)^2$ because
$\varphi'(x)=-x\varphi(x)$. Numerically, `mp.diff` matches $x/\varphi(x)^2$ to 12 digits. Not junk-dependent.

### 17 `deriv_deriv_normCDFInv_le`
**Rendering.** For $0<u\le\tfrac14$, $(\Phi^{-1})''(u)\le-\pi$.
**Assessment.** True: $(\Phi^{-1})''(u)=2\pi\,x\,e^{x^2}$ with $x=\Phi^{-1}(u)\le\Phi^{-1}(\tfrac14)=-0.67449$. This is
increasing in $x$ for $x<0$, so the supremum over $(0,\tfrac14]$ is $-6.6793$, attained at $u=\tfrac14$, which is
$\le-\pi$. A grid of 2000 points confirms it. The constant is not sharp but is correct. The hypothesis $0<u$
is necessary: at $u=0$ the function `deriv normCDFInv` is $0$ to the left and unbounded to the right, so
`deriv (deriv normCDFInv) 0 = 0 > -π`. The statement therefore avoids the junk value rather than relying on it.

### 18 `concaveOn_normCDFInv_add_sq`
**Rendering.** $u\mapsto\Phi^{-1}(u)+\frac\pi2u^2$ is concave on $(0,\tfrac14]$.
**Assessment.** True: $(0,\tfrac14]$ is a convex subset of $(0,1)$, where $F$ is $C^2$, and there the second
derivative is $\le-\pi+\pi=0$ (#17). The left endpoint $0$ is excluded, and must be: with the junk value
$f(0)=0$ concavity would fail near $0$, where $f\to-\infty$.

### 19 `normCDFInv_second_diff`
**Rendering.** If $u>0$, $s\ge0$ and $u+2s\le\tfrac14$, then $\pi s^2\le2\Phi^{-1}(u+s)-\Phi^{-1}(u)-\Phi^{-1}(u+2s)$.
**Assessment.** True: applying concavity (#18) to $g=\Phi^{-1}+\frac\pi2u^2$ gives $2g(u+s)-g(u)-g(u+2s)\ge0$, and
the quadratic part contributes exactly $-\frac\pi2\cdot(-2s^2)$. Over 3000 random $(u,s)$ the minimum ratio is
$2.13\ge1$. Instance: $u=0.1$, $s=0.05$. Not junk-dependent.

### 20 `normCDFInv_dyadic_concave`
**Rendering.** For $k\ge2$, $2^{-(k+1)}\le u$, $s\ge0$ and $u+2s\le2^{-k}$, the same inequality $\pi s^2\le2F(u+s)-F(u)-F(u+2s)$ holds.
**Assessment.** True: a special case of #19, since $u>0$ and $2^{-k}\le\tfrac14$. The hypotheses are stronger
than needed (only $u>0$ and $u+2s\le\tfrac14$ matter). Instance: $k=2$, $u=\tfrac18$, $s=\tfrac1{16}$.

### 21 `lutValue_mirror_normCDFInv`
**Rendering.** For $j<2^d$, $\mathrm{lutValue}(F,d,2^d-1-j)=-\mathrm{lutValue}(F,d,j)$. The ℕ-subtraction is
genuine, since $j\le2^d-1$.
**Assessment.** True: cell $2^d-1-j$ is the image of cell $j$ under $u\mapsto1-u$, and $F(1-u)=-F(u)$ holds for
every $u$. Instance: $d=1$, $j=0$. The hypothesis is necessary and excludes junk: for $j\ge2^d$ the right side
is $-0$, because the cell lies outside $[0,1]$ where $F=0$, while the left side is
$\mathrm{lutValue}(F,d,0)<0$.

### 22 `lutValue_upper_half_normCDFInv`
**Rendering.** If $d\ge1$ and $2^{d-1}\le j<2^d$, then $2^d-1-j<2^{d-1}$ and $\mathrm{lutValue}(F,d,j)=-\mathrm{lutValue}(F,d,2^d-1-j)$.
**Assessment.** True: $2^d-1-j\le2^{d-1}-1$, and #21 applied to $j'=2^d-1-j$ gives the identity. Instance:
$d=1$, $j=1$.

### 23 `tendsto_method1MSE_normCDFInv`
**Rendering.** $\mathrm{MSE}_1(F,d)\to0$ as $d\to\infty$.
**Assessment.** True: the cell-average table is the conditional expectation of $F(U)$ given the dyadic
$\sigma$-field $\mathcal F_d$, which converges in $L^2$ for $F\in L^2$ (martingale convergence, or density of step
functions). Numerically $0.3634$ ($d=1$), $1.50\times10^{-4}$ ($d=10$), $7.44\times10^{-8}$ ($d=20$); closed form and
direct quadrature agree for $d\le5$. It also follows from #32.

### 24 `lutStream_normCDFInv_tendstoInDistribution`
**Rendering.** $(\Omega,P)$ and $(\Omega',P')$ are probability spaces, $U\sim U(0,1)$ under $P$, and $G\sim\mathcal N(0,1)$
under $P'$. Then $X_d=\mathrm{lutValue}(F,d,\lfloor2^dU\rfloor_+)$ converges in distribution to $G$, meaning weak
convergence of the laws $P\circ X_d^{-1}\to P'\circ G^{-1}$ in `ProbabilityMeasure ℝ`, together with
AEMeasurability of each $X_d$ and of $G$.
**Assessment.** True: $X_d=\mathbb E[F(U)\mid\mathcal F_d]\to F(U)$ in $L^2$, and $F(U)\sim\mathcal N(0,1)$ (#13). On
$U\in(0,1)$ the index $\lfloor2^dU\rfloor_+$ lies in $[0,2^d-1]$, so the junk table entries are never used.
Instance: $\Omega=\Omega'=\mathbb R$, $P=\lambda|_{(0,1)}$, $U=\mathrm{id}$, $P'=\mathcal N(0,1)$, $G=\mathrm{id}$.

### 25 `lutStreams_sum_normCDFInv_tendstoInDistribution`
**Rendering.** Let $n\ge1$, let $U_1,\dots,U_n$ be mutually independent (`iIndepFun`) and $U(0,1)$, and let
$G\sim\mathcal N(0,1)$. Then (a) for each $i$, $n^{-1/2}X_d^{(i)}$ converges in distribution to $\mathcal N(0,1/n)$
(the limit is `id` under `gaussianReal 0 (n:ℝ≥0)⁻¹`, whose variance is $1/n$); and (b)
$\sum_in^{-1/2}X_d^{(i)}$ converges in distribution to $G$.
**Assessment.** True. (a) follows from #24 and scaling, without needing independence. (b) holds because the
$L^2$ error of the sum is at most $\sum_i$ of the individual errors, which tends to $0$, and
$\sum_in^{-1/2}F(U_i)\sim\mathcal N(0,1)$ by independence. The variance $(n)^{-1}$ is correct, and $n\ge1$ is
needed (for $n=0$ the empty sum is $0$). Instance: $n=1$, $U_0=\mathrm{id}$ on $(\mathbb R,\lambda|_{(0,1)})$.

### 26 `dyadic_mse_ge_normCDFInv`
**Rendering.** For each $k\ge2$ there is a $c>0$ (depending only on $k$) such that for all $d\ge k+3$ and all
$a,b\in\mathbb R$:
$c\le\sum_{j=2^{d-k-1}}^{2^{d-k}-1}\int_{C_{d,j}}(a+bj-F(u))^2du$. The index block corresponds to the $u$-block
$B_k\subset(0,\tfrac18]$, and the ℕ-subtractions are genuine since $d\ge k+3$.
**Assessment.** True. For a fixed $d$ the minimum over $(a,b)$ equals
$\sum_j\int_{C_{d,j}}(F-y_j)^2+h\cdot\mathrm{RSS}$, which is $>0$. As $d\to\infty$ it tends to
$\mathrm{dyadicAffineErr}(F,k)>0$, because $F$ is strictly concave and hence not affine on $B_k$. Numerically
(`check_method3.out`) the minimum decreases monotonically in $d$ to the limit: for $k=2$ it is
$1.54\times10^{-4}$ at $d=5$ and $7.0768\times10^{-6}$ at $d=16$, against the limit $7.0767\times10^{-6}$. The same
pattern holds for $k=3,\dots,6$. A uniform $c$ (about `dyadicAffineErr F k`) therefore exists. Not vacuous
($k=2$), not junk-dependent.

### 27 `method3_mse_ge_normCDFInv`
**Rendering.** For $k\ge2$: (i) there is a $c>0$ such that for all $d\ge k+3$ and every table $w:\mathbb N\to\mathbb R$
that is affine in $j$ on the index block $[2^{d-k-1},2^{d-k})$, the full MSE
$\sum_{j<2^d}\int_{C_{d,j}}(w_j-F)^2\ge c$; (ii) for any family $w_d$ that, for every $d$, is affine on that
block, the full MSE does not tend to $0$.
**Assessment.** True. (i) follows from #26, since all other cell integrals are $\ge0$. (ii) follows from (i).
Requiring affinity "for every $d$" in (ii) adds nothing, because for $d<k+3$ the block has at most 2 indices
and any $w$ is affine there. This covers method 3, whose table is affine on each dyadic index group. Not vacuous.

### 28 `tendsto_method3MSE_normCDFInv`
**Rendering.** $0<\mathrm{method3Limit}(F)$ and $\mathrm{MSE}_3(F,d)\to\mathrm{method3Limit}(F)=2\sum_{k\ge1}\operatorname{dist}^2_{L^2(B_k)}(F,\text{affine})$.
**Assessment.** True. The lower half at level $d$ splits into the group $\{0,1\}$, with error
$\le\int_0^{2^{1-d}}F^2\to0$, and the blocks $B_k$ for $k=1..d-2$. Each block error is the minimum over
affine-in-$j$ tables, so it is bounded by $\int_{B_k}F^2$ (a summable bound) and tends to
$\mathrm{dyadicAffineErr}(F,k)$. By dominated convergence the sum converges, and mirror symmetry doubles it.
Numerically the limit is $4.13297\times10^{-5}$, and $\mathrm{MSE}_3(d)-\lim$ is $1.45\times10^{-5}$, $6.73\times10^{-6}$,
$3.15\times10^{-6}$, $1.48\times10^{-6}$ for $d=13..16$ (halving each level). Closed form and direct quadrature
agree for $d\le5$, and $\mathrm{MSE}_3=\mathrm{MSE}_1$ for $d\le3$, as expected since the groups have $\le2$ points.
Positivity also excludes the junk `tsum = 0` of a non-summable series. Not junk-dependent.

### 29 `exp_mul_gaussianPDFReal_le`
**Rendering.** For $x\le-1$, $e^{-3/2}\varphi(x)\le-x\,\Phi(x)$.
**Assessment.** True: the Mills-ratio lower bound $\Phi(x)\ge\frac{|x|}{1+x^2}\varphi(x)$ gives
$-x\Phi(x)\ge\tfrac12\varphi(x)$ for $|x|\ge1$. Numerically $\inf_{x\le-1}(-x\Phi(x)/\varphi(x))=0.6557$, attained
at $x=-1$, which exceeds $e^{-3/2}=0.2231$. The ratio tends to $1$ as $x\to-\infty$. Instance: $x=-1$.

### 30 `neg_mul_normCDF_le`
**Rendering.** For every $x$, $-x\Phi(x)\le\varphi(x)$.
**Assessment.** True: trivial for $x\ge0$; for $x<0$ it is the Mills upper bound $\Phi(x)\le\varphi(x)/|x|$. The
numerical maximum of $-x\Phi(x)-\varphi(x)$ on $[-40,40]$ is negative. Standard.

### 31 `normCDFInv_block_bounds`
**Rendering.** For $m\ge1$ and $2^{-(m+1)}\le u\le v\le2^{-m}$:
$(4e^4)^{-1}(2^m(v-u))^2\le m\,(F(v)-F(u))^2\le8(4+\varphi(1)^{-2})(2^m(v-u))^2$, where $\varphi(1)^{-2}=2\pi e$.
**Assessment.** True. By the mean value theorem $F(v)-F(u)=g(\xi)(v-u)$ with $g=1/\varphi(F)$ decreasing on
$(0,\tfrac12)$. So it suffices that $m\,g(w)^2/4^m$ lies in $[0.00458,168.6]$ on the block. Numerically, over
$m=1..59$ and selected $m$ up to $800$ (with a tail-accurate inverse), it lies in $[0.7213,3.179]$ and tends to
$[1/(2\ln2),\,2/\ln2]$. Random $(m,u,v)$ give ratios in $[0.78,3.00]$. An analytic argument via #29/#30 and
$x^2\le2(m+1)\ln2$ gives the stated constants. Instance: $m=1$, $u=\tfrac14$, $v=\tfrac12$. Not
junk-dependent, since $u,v\in(0,\tfrac12]$.

### 32 `method1MSE_order_normCDFInv`
**Rendering.** There are constants $c,K>0$ such that for all $d\ge2$:
$c\,\frac{2^{-d}}{d}\le\mathrm{MSE}_1(F,d)\le K\,\frac{2^{-d}}{d}$ (the cast to $\mathbb R$ is as expected).
**Assessment.** True. The interior cells give $\approx\frac{h^2}{12}\int_h^{1-h}(F')^2\sim\frac{h}{12\ln(1/h)}$, and the
end cells give $\approx\frac{h}{\ln(1/h)}\cdot\mathrm{Var}(\ln\text{Unif})=\frac{h}{d\ln2}$. Together this is
$\Theta(2^{-d}/d)$. Numerically $d2^d\mathrm{MSE}_1(d)$ is $1.116$ ($d=2$), $1.533$ ($d=10$), $1.560$ ($d=20$),
$1.5746$ ($d=60$, the maximum) and $1.566$ ($d=400$). The large-$d$ values use exact end cells plus a midpoint
expansion, validated against the exact values to a relative error of $10^{-10}$. So
$c\approx1.1$ and $K\approx1.6$ appear to work, and the analytic estimate shows the ratio stays bounded for all $d$. This is a $\Theta$ statement, not an asymptotic equivalence. The
condition $d\ge2$ only avoids $d=0$, where Lean's $1/0=0$ would make the upper bound $\mathrm{MSE}\le0$ false.

### 33 `tendsto_log_method1MSE_normCDFInv`
**Rendering.** $\log(\mathrm{MSE}_1(F,d))/d\to-\log2$.
**Assessment.** True: by #32, $\log\mathrm{MSE}_1=-d\log2-\log d+O(1)$. Since $\mathrm{MSE}_1>0$ for every $d$, the
logarithm is genuine and not `log 0 = 0`. Convergence is slow: $-0.821$ ($d=20$), $-0.735$ ($d=100$),
$-0.707$ ($d=400$). This only states the exponential rate, which is strictly weaker than #32.
