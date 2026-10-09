# Blind read-back report: R50_lut

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round26/packet_R50_lut.lean` |
| declarations audited | 19 (11 theorems; 3 definitions in the packet body: `lutScaled`, `method1CellErr`, `logCellVar`; 5 appended definitions: `gridPt`, `lutValue`, `method1MSE`, `normCDF`, `normCDFInv`) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round26/work_R50_lut/` (`common.py` and `cells.py` are shared helper modules; `check1_mills.py` … `check6_mse.py` each have a matching `.out`; `Check1.lean`/`Check1.out` is the elaboration check) |

Elaboration was confirmed by compiling `Check1.lean` (`import MlmcLean`, `#check`/`#print` only). `range` in
`method1MSE` is `Finset.range`. `log` is `Real.log`. `1/2` in theorem 10 is the real number $1/2$. All 11 theorems use only
`[propext, Classical.choice, Quot.sound]`.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `neg_mul_gaussianPDFReal_le_one_add_sq_mul` | theorem | true | no (no hypotheses) | no |
| 2 | `normCDFInv_sub_mul_le` | theorem | true | no (e.g. $u=0.1,v=0.4$) | no |
| 3 | `log_sub_le_normCDFInv_sub_mul` | theorem | true | no (e.g. $u=0.1,v=0.4$) | no (`v < 1/2` avoids $(-0)^{-1}=0$) |
| 4 | `tendsto_lutScaled` | theorem | true | no (e.g. $t=1/2$) | no |
| 5 | `tendsto_natCast_div_sq_normCDFInv` | theorem | true | no | no (junk only at $d=0,1$, which a limit ignores) |
| 6 | `tendsto_method1CellErr_normCDFInv` | theorem | true | no | no |
| 7 | `summable_logCellVar` | theorem | true | no | no |
| 8 | `tendsto_mul_method1MSE_normCDFInv` | theorem | true | no | no (the `tsum` is a real sum; the constant is about 1.5586) |
| 9 | `method1MSE_normCDFInv_const_pos` | theorem | true | no | no (it would be false if the `tsum` fell back to 0) |
| 10 | `tendsto_method1MSE_succ_div_normCDFInv` | theorem | true | no | no (the MSE is $>0$, so no division by 0) |
| 11 | `isEquivalent_method1MSE_normCDFInv` | theorem | true | no | no (junk only at $d=0$; the constant is $>0$) |
| – | `gridPt`, `lutValue`, `method1MSE`, `normCDF`, `normCDFInv`, `lutScaled`, `method1CellErr`, `logCellVar` | def | n/a | n/a | `normCDFInv` is 0 off $(0,1)$ (see below); harmless here |

## Main points for a human auditor

- All 11 statements are true, none is vacuous, and none depends on a junk value. High-precision numerical checks with mpmath
  confirm every inequality and every limit, including the constant $C=\sum_j \mathrm{logCellVar}(j)/\log 2\approx 1.558582$.
- `normCDFInv` is $\Phi^{-1}$ on $(0,1)$ and **0 outside** (so $\Phi^{-1}(1)=0$ in Lean). This junk value appears only at finitely
  many $d$ in the limit statements: at $d=0$ $\Phi^{-1}(1/2^0)=\Phi^{-1}(1)=0$, and in `lutScaled` $t/2^d\ge 1$ for small $d$.
  A `Tendsto` or `IsEquivalent` statement ignores finitely many $d$, so this does not matter.
- Theorem 3 needs `v < 1/2`. At $v=1/2$ Lean gives $(-\Phi^{-1}(1/2))^{-1}=(-0)^{-1}=0$, and the inequality then fails
  (e.g. $u=0.45$: $0.105>0.0158$). The hypothesis is the right one.
- `tsum`: `logCellVar j` $\ge 0$ and $\sim 1/(12j^2)$, so the series really converges. Theorem 9 ($0<\sum'/\log 2$) would be
  false if the `tsum` fell back to 0, so theorems 8, 9 and 11 do not rely on that fallback. The $j=0$ term uses
  $\int_0^1\log^2 t\,dt = 2$ and $\int_0^1 \log t\,dt=-1$, both real (integrable) integrals; Lean's $\log 0=0$ sits on a null
  set.
- `method1CellErr` and `method1MSE` integrate $(\text{cell mean}-\Phi^{-1})^2$, which is integrable because
  $\Phi^{-1}\in L^2(0,1)$. The closed forms agree with direct quadrature of the Lean definitions (`check5_cellerr.out`), so no
  "non-integrable means 0" junk is involved.
- Convergence in theorems 5, 6 and 8 is slow, with a relative error of order $\log d/d$. For example
  $d\,2^d\,\mathrm{MSE}(d)=1.5471$ at $d=14$, $1.5743$ at $d=50$, $1.5626$ at $d=1000$ and $1.5592$ at $d=10^4$, against
  $C=1.5586$. The approach is non-monotone (it overshoots $C$ and then comes back down), which is consistent with the claimed limit.

## Per-declaration sections

Notation: $\varphi(x)=(2\pi)^{-1/2}e^{-x^2/2}$, $\Phi$ the standard normal CDF, $h=2^{-d}$, $c_d=\Phi^{-1}(2^{-d})$.

### Definitions

**Rendering.**
- `gridPt d j` $=j/2^d\in\mathbb R$ ($j,d\in\mathbb N$ cast to $\mathbb R$).
- `lutValue f d j` $=2^d\int_{j/2^d}^{(j+1)/2^d} f(u)\,du$ (interval integral, i.e. over $(a,b]$), the mean of $f$ on cell $j$.
- `method1MSE f d` $=\sum_{j=0}^{2^d-1}\int_{j/2^d}^{(j+1)/2^d}(\mathrm{lutValue}\,f\,d\,j-f(u))^2du$, the $L^2(0,1)$ error of
  the piecewise-constant cell-average approximation of $f$ on $2^d$ uniform cells.
- `normCDF x` $=$ `cdf (gaussianReal 0 1) x` $=\Phi(x)$. Mathlib's `cdf μ x = μ.real (Iic x)` for a probability measure, and
  `gaussianReal 0 1` is $N(0,1)$ (variance $1:\mathbb R_{\ge0}$).
- `normCDFInv u` $=\mathbf 1_{(0,1)}(u)\cdot$ `invFun normCDF u`. $\Phi:\mathbb R\to(0,1)$ is a continuous strictly increasing
  bijection, so this is $\Phi^{-1}(u)$ for $u\in(0,1)$ and $0$ for $u\notin(0,1)$ (junk).
- `lutScaled d t` $=(\Phi^{-1}(t/2^d)-c_d)\cdot(-c_d)$, with the junk-zero convention when $t/2^d\notin(0,1)$ or $d=0$.
- `method1CellErr d j` $=\int_{j/2^d}^{(j+1)/2^d}(\mathrm{lutValue}\,\Phi^{-1}\,d\,j-\Phi^{-1}(u))^2du$, the error on cell $j$.
- `logCellVar j` $=\int_j^{j+1}\log^2t\,dt-\big(\int_j^{j+1}\log t\,dt\big)^2=\mathrm{Var}(\log T)$ with $T\sim U[j,j+1]$.

**Assessment.** The definitions are faithful. $\Phi^{-1}\in L^2(0,1)$ ($\int(\Phi^{-1})^2=\int x^2\varphi=1$), so every cell
integral is a real integral, including the singular end cells. `logCellVar 0` $=2-1=1$, and `logCellVar 1` $=1-2\log^22$
(checked numerically).

### 1. `neg_mul_gaussianPDFReal_le_one_add_sq_mul`

**Rendering.** For all real $z$: $-z\,\varphi(z)\le(1+z^2)\,\Phi(z)$. Here `gaussianPDFReal 0 1 z` $=(\sqrt{2\pi})^{-1}e^{-z^2/2}$.

**Assessment.** True. For $z\ge0$ the left side is $\le0\le$ the right side. For $z=-x<0$ the inequality is
$x\varphi(x)\le(1+x^2)(1-\Phi(x))$, the classical lower bound $\frac{1-\Phi(x)}{\varphi(x)}\ge\frac{x}{1+x^2}$. Proof: let
$g(x)=(1+x^2)(1-\Phi(x))-x\varphi(x)$. Then $g'(x)=2x(1-\Phi(x))-2\varphi(x)\le0$ by the upper Mills bound, and $g\to0$ as
$x\to\infty$, so $g\ge0$. It is not vacuous (no hypotheses) and uses no junk values. Numerically (`check1_mills.out`) there is
no violation on $[-40,40]$ or at $z=-50,\dots,-10^4$, and the ratio LHS/RHS tends to 1, so the bound is sharp. Standard result:
the Mills-ratio lower bound (Gordon/Birnbaum inequality).

### 2. `normCDFInv_sub_mul_le`

**Rendering.** For real $u,v$ with $0<u\le v<1$: $(\Phi^{-1}(v)-\Phi^{-1}(u))\cdot(-\Phi^{-1}(v))\le\log v-\log u$.

**Assessment.** True. Let $a=\Phi^{-1}(u)\le b=\Phi^{-1}(v)$. Then $\log v-\log u=\int_a^b\varphi/\Phi\,dx$, and
$\varphi(x)/\Phi(x)\ge -x\ge -b$ on $[a,b]$ by the Mills upper bound $\Phi(x)\le\varphi(x)/|x|$ for $x<0$ (and trivially for
$x\ge0$). Integrating gives the claim. All of $u,v$ lie in $(0,1)$, so no junk value is used. If $b\ge0$ the statement is
trivially true ($\text{LHS}\le0\le\text{RHS}$), but that is genuine mathematics. Not vacuous: $u=0.1,v=0.4$ gives
$0.2605\le1.386$. No violation in 5000 random pairs, including log-uniform pairs down to $10^{-300}$, and the bound is nearly
sharp in the tail ($u=10^{-100}$, $v=2u$: $0.6911\le0.6931$) (`check2_twopoint.out`). The hypothesis $v<1$ is natural. With
$v=1$ the junk value $\Phi^{-1}(1)=0$ would still make the inequality hold, but that case is excluded anyway. Standard result:
the hazard-rate/Mills-ratio lower bound on $\frac{d}{dx}\log\Phi$, integrated between two quantiles.

### 3. `log_sub_le_normCDFInv_sub_mul`

**Rendering.** For real $u,v$ with $0<u\le v<1/2$: $\log v-\log u\le(\Phi^{-1}(v)-\Phi^{-1}(u))\big(-\Phi^{-1}(u)+(-\Phi^{-1}(v))^{-1}\big)$.

**Assessment.** True. Here $a\le b<0$. Theorem 1 gives $\varphi(x)/\Phi(x)\le(1+x^2)/(-x)=-x+1/(-x)\le -a+1/(-b)$ on $[a,b]$.
Integrate. Since $v<1/2$, $b<0$ and the inverse is a real inverse. The hypothesis is necessary: at $v=1/2$ Lean gives
$(-0)^{-1}=0$ and the inequality is false (e.g. $u=0.45$: $0.1054>0.0158$; `check2_twopoint.out`). Not vacuous ($u=0.1$,
$v=0.4$: $1.386\le5.376$). No violation in 3507 random pairs. Standard result: the integrated Mills-ratio upper bound on
$\varphi/\Phi$ (from Gordon's lower bound).

### 4. `tendsto_lutScaled`

**Rendering.** For real $t>0$: $\big(\Phi^{-1}(t2^{-d})-\Phi^{-1}(2^{-d})\big)\cdot(-\Phi^{-1}(2^{-d}))\to\log t$ as
$d\to\infty$ ($d\in\mathbb N$).

**Assessment.** True. For large $d$ both arguments lie in $(0,1/2)$. Theorems 2 and 3 (applied with $u,v=\min,\max$ of
$t2^{-d}$ and $2^{-d}$) sandwich the expression between $\log t$ and $\log t\cdot(1+O(1/c_d^2))$, and $c_d\to-\infty$. The
junk values (at $d=0$, and wherever $t/2^d\ge1$) affect only finitely many $d$. The hypothesis $t>0$ is necessary: for
$t\le0$ Lean gives $\Phi^{-1}(t/2^d)=0$, so the expression is $c_d^2\to\infty$. Numerically, at $t=0.001,0.5,3,100$ the values
converge to $\log t$ (e.g. $t=100$: $5.58,4.71,4.63,4.610,4.606$ against $4.6052$; `check3_lutscaled.out`). Standard result:
quantile spacing in the normal tail, $\Phi^{-1}(t\varepsilon)-\Phi^{-1}(\varepsilon)\sim\log t/|\Phi^{-1}(\varepsilon)|$ (the
Gumbel normalisation for Gaussian extremes).

### 5. `tendsto_natCast_div_sq_normCDFInv`

**Rendering.** $d/\Phi^{-1}(2^{-d})^2\to 1/(2\log2)$ as $d\to\infty$ in $\mathbb N$ (real division; `^` binds before `/`).

**Assessment.** True, because $\Phi^{-1}(\varepsilon)^2\sim2\log(1/\varepsilon)=2d\log2$. Junk values occur only at $d=0$
($\Phi^{-1}(1)=0$) and $d=1$ ($\Phi^{-1}(1/2)=0$, so $1/0=0$), which a limit ignores. Numerically the values are
$0.7900$ ($d=50$), $0.72610$ ($10^3$), $0.721419$ ($10^5$), against $0.721348$. Standard result: the leading-order asymptotics of
the normal quantile.

### 6. `tendsto_method1CellErr_normCDFInv`

**Rendering.** For each fixed $j\in\mathbb N$: $d\,2^d\int_{jh}^{(j+1)h}(\bar g_j-\Phi^{-1}(u))^2du\to\mathrm{logCellVar}(j)/(2\log2)$,
where $\bar g_j$ is the cell mean.

**Assessment.** True. Substitute $u=t/2^d$: the cell error is $2^{-d}\,\mathrm{Var}_{t\sim U[j,j+1]}(\Phi^{-1}(t2^{-d}))
=2^{-d}c_d^{-2}\,\mathrm{Var}_t(\mathrm{lutScaled}\,d\,t)$. Theorem 4 with domination from theorems 2 and 3 gives
$\mathrm{Var}(\mathrm{lutScaled})\to\mathrm{Var}(\log T)$, and theorem 5 gives $d/c_d^2\to1/(2\log2)$. For small $d$ with
$j\ge2^d$ the cell lies outside $(0,1)$ and the error is junk 0, but this affects only finitely many $d$. Numerically
(closed form $\int g^2-(\int g)^2/h$, checked against direct quadrature of the Lean definition): for $j=0$, the values at
$d=50,10^3,5\cdot10^4$ are $0.7235,0.7230,0.72142$ against $0.72135$. The cases $j=1,2,5,20$ converge in the same way
(`check5_cellerr.out`). Standard result: the local error of the end cells of a piecewise-constant approximation of the normal
quantile function.

### 7. `summable_logCellVar`

**Rendering.** $\sum_{j\ge0}\mathrm{Var}(\log U[j,j+1])$ is summable in $\mathbb R$.

**Assessment.** True. The terms are $\ge0$, and $\mathrm{logCellVar}(j)=\frac1{12j^2}(1+O(1/j))$; numerically $12j^2\cdot$ term
is $0.99009$ at $j=100$ and $0.9999$ at $j=10^4$. The sum is $\approx1.080327$. There is no junk value: the $j=0$ term is the
real integral $\int_0^1\log^2=2$. Standard result: the delta-method variance $\approx(1/j)^2/12$, which forms a $p$-series with
$p=2$.

### 8. `tendsto_mul_method1MSE_normCDFInv`

**Rendering.** $d\,2^d\,\mathrm{MSE}_d\to C:=\big(\sum_{j\ge0}\mathrm{logCellVar}(j)\big)/\log2$, where $\mathrm{MSE}_d$ is the
$L^2(0,1)$ error of the $2^d$-cell cell-average lookup table for $\Phi^{-1}$.

**Assessment.** True. By symmetry $\Phi^{-1}(1-u)=-\Phi^{-1}(u)$, both tails contribute equally, which gives
$2\cdot\sum_j\mathrm{logCellVar}(j)/(2\log2)$. The interior cells contribute $\approx h^2/12\int(\Phi^{-1})'^2$ over the
interior, which is $o(h/d)$ once the end cells are split off. Uniform control of the tail of the $j$-sum comes from the
$1/(12j^2)$ bound. The `tsum` is a real sum (theorem 7). Numerically, the exact sum is computed for $d\le14$ and a
semi-analytic sum (exact for 1500 end cells, midpoint rule for the rest, validated against the exact sum to a relative
difference of $4\cdot10^{-10}$) for larger $d$. $d2^d\mathrm{MSE}$ is $1.5471$ ($d=14$), $1.5603$ ($20$), $1.5743$ ($50$),
$1.5674$ ($300$), $1.5626$ ($10^3$), $1.5592$ ($10^4$), against $C=1.558582$ (`check6_mse.out`). Standard result:
$\|\Phi^{-1}-Q_N\|_{L^2}^2\asymp1/(N\log N)$ for the piecewise-constant uniform-grid approximation $Q_N$, $N=2^d$ (known from
work on approximate random variables). Here it is made sharp with an explicit constant.

### 9. `method1MSE_normCDFInv_const_pos`

**Rendering.** $0<\big(\sum'_j\mathrm{logCellVar}(j)\big)/\log2$.

**Assessment.** True. The terms are $\ge0$, the series is summable, the $j=0$ term is 1, and $\log2>0$; the value is
$\approx1.5586$. This does not depend on a junk value. Indeed the statement implies summability, because a non-summable `tsum`
would be 0 and $0<0$ fails. Standard fact: a convergent series of non-negative terms with one positive term has a positive sum.

### 10. `tendsto_method1MSE_succ_div_normCDFInv`

**Rendering.** $\mathrm{MSE}_{d+1}/\mathrm{MSE}_d\to1/2$ as $d\to\infty$ (real division).

**Assessment.** True, from theorems 8 and 9: the ratio is $\frac{C+o(1)}{C+o(1)}\cdot\frac{d}{2(d+1)}\to\frac12$.
$\mathrm{MSE}_d>0$ for every $d$ ($\Phi^{-1}$ is non-constant on every cell inside $[0,1]$), so the division is real. Numerically
the ratio is $0.4652$ ($d=13$), $0.4766$ ($20$), $0.4950$ ($100$), $0.49995$ ($10^4$). The statement is weaker than theorem 11:
any $\mathrm{MSE}\asymp 2^{-d}d^{-k}$ gives the same limit.

### 11. `isEquivalent_method1MSE_normCDFInv`

**Rendering.** $\mathrm{MSE}_d\sim C\cdot(2^d)^{-1}/d$ as $d\to\infty$. Here `IsEquivalent u v` means $u-v=o(v)$; since $v_d\ne0$
for $d\ge1$, this is the same as $u_d/v_d\to1$.

**Assessment.** True; it is equivalent to theorem 8 given $C>0$ (theorem 9). The junk value $v_0=C\cdot1/0=0$ at $d=0$ does not
matter, because the little-o condition is eventual. Since $C>0$, the statement does not collapse to "$\mathrm{MSE}_d$ is
eventually 0". Numerically $\mathrm{MSE}_d/(C2^{-d}/d)=1.0011$ ($d=20$), $1.0101$ ($50$), $1.0026$ ($10^3$), $1.0004$ ($10^4$).
Standard result: the sharp asymptotics of the piecewise-constant inverse-normal lookup-table MSE,
$\sim\frac{\sum_j\mathrm{Var}(\log U[j,j+1])}{\log 2}\cdot\frac{2^{-d}}{d}$.
