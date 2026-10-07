# Blind read-back report: R7 `MlmcLean.LUTAsymptotics`

| Field | Value |
|---|---|
| Date | 2026-10-07 |
| Packet | `readback/round14/packet_R7_lut_asymptotics.lean` |
| Declarations audited | 29 (14 theorems, 12 module definitions, 3 appended definitions) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round14/work_R7/` (`*.py` with matching `*.out`; `scratch.lean`/`scratch.out` = sorry-compiled copy of the packet with targeted Mathlib imports, `#check`ed with `pp.numericTypes`/`pp.coercions`) |

Notation used below: $h=2^{-d}$ is the cell width, cell $j$ is $C_j=[jh,(j+1)h]$, $y_j=\texttt{lutValue } f\,d\,j = h^{-1}\int_{C_j} f$ is the cell mean, $I_k=[2^{-(k+1)},2^{-k}]$ is the $k$-th dyadic interval, $m_k = 3/2^{k+2}$ its midpoint, $G_{d,k}=[2^{d-k-1},2^{d-k})\cap\mathbb N$ (the cells covering $I_k$ when $d\ge k+1$) and $n=|G_{d,k}|=2^{d-k-1}$. "$f\in L^1\cap L^2$" abbreviates the two hypotheses `hf`, `hf2` (interval integrability of $f$ and $f^2$ on $[0,1]$).

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `sum_sq_lsqFit_le` | theorem | true | no | no |
| 2 | `dyadic_groupMSE_eq` | theorem | true (sympy-verified, $d\le7$) | no | no (under `hd`; also true at $d=k+1$ via $x/0=0$, but that case is excluded) |
| 3 | `tendsto_dyadic_groupMSE` | theorem | true | no | no |
| 4 | `dyadicAffineErr_isLeast` | theorem | true | no | no |
| 5 | `tendsto_method3MSE` | theorem | true | no | no (the `tsum` is summable) |
| 6 | `method3Limit_pos` | theorem | true | no ($\Phi^{-1}$ with $k=2$, or $-u^2$) | no |
| 7 | `exists_tendsto_method3MSE` | theorem | true | no | no |
| 8 | `groupMSE_sub_half` | theorem | true (sympy-verified) | no | no |
| 9 | `groupMSE_quadratic` | theorem | true (sympy-verified, symbolic $\alpha,\beta,\gamma$) | no | no |
| 10 | `groupMSE_odd_quadratic` | theorem | true (exact rational check) | no (no hypotheses) | no |
| 11 | `method1MSE_le_order` | theorem | true | no ($\Phi^{-1}$, $K\approx3.18$) | no |
| 12 | `method1MSE_ge_order` | theorem | true | no ($\Phi^{-1}$, $c\approx0.72$) | no |
| 13 | `method1MSE_order` | theorem | true | no | no |
| 14 | `tendsto_log_method1MSE_div` | theorem | true | no | no |
| D1–D15 | definitions | def | n/a | n/a | junk only at $d\in\{0,1\}$ in `method3Value` (irrelevant to every theorem) |

## Main points for a human auditor

- No false, vacuous or junk-dependent statement was found. I re-derived and checked all four exact formulas (2, 8, 9, 10) with exact arithmetic for small $d,k$.
- **Oddness is used consistently.** `hodd` appears exactly where the upper half $[1/2,1]$ matters: `tendsto_method3MSE`, `exists_tendsto_method3MSE` and the method-1 upper bounds (11, 13, 14). It is absent where only $(0,1/2]$ matters (`method3Limit_pos`, `method1MSE_ge_order`, the per-group results). Without it, the method-3 statement fails: for the even function $g=-(u-\tfrac12)^2$ the MSE tends to $0.02499$, while `method3Limit g` $=1/89280$ (`check_method3.out`). `hodd` is stated for all $u\in\mathbb R$, which is stronger than needed but harmless because any $f$ on $[0,1]$ extends. It forces $f(1/2)=0$.
- **The method-1 block hypotheses are satisfiable, but only by functions with a $\sqrt{\log(1/u)}$-type singularity at 0.** For $f=\Phi^{-1}$ the ratio $R_m(u,v)=m(f v-f u)^2/(2^m(v-u))^2$ lies between $\inf_m\inf R_m = 1/(2\ln2)\approx0.7213$ (approached as $m\to\infty$) and $\sup R_m\approx3.179$ (peak near $m=5$; the limit is $2/\ln 2$). So `hlo` holds with $c=0.72$ and `hup` with $K=3.18$. A simpler example satisfies both with $c=K=1$: the function that is piecewise linear with slope $2^m/\sqrt m$ on block $m$, with $f(1/2)=0$, extended oddly. Smooth $f$ (for example affine) satisfy `hup` but never `hlo` with $c>0$, as expected for an order-$2^{-d}/d$ (not $4^{-d}$) result. If $K<0$, `hup` is unsatisfiable, so $K\ge 0$ holds implicitly.
- **`hconc` in theorems 6 and 7 holds for $\Phi^{-1}$ with $k=2$ but not with $k=1$.** On $I_2$ it holds with $\mu\approx6.68=-(\Phi^{-1})''(1/4)$. It fails on $I_1=[1/4,1/2]$ because $(\Phi^{-1})''(1/2)=0$: the ratio $D/s^2\to0$ at the corner. So the statements are non-vacuous for $\Phi^{-1}$, but one must pick $k\ge2$.
- **Modelling choices worth knowing.** (a) Method 3 groups cells $\{0,1\}$, i.e. $[0,2^{1-d}]$, together. This is not a dyadic interval: the $k=d-1$ interval is a single cell merged with cell 0. Its contribution tends to 0. (b) For $d\in\{0,1\}$, `method3Value` uses ℕ-subtraction ($2^{0-1}=1$) and a group $\{0,1\}$ that reaches into the upper half, or outside $[0,1]$ when $d=0$. This is junk but only affects finitely many terms of a limit. (c) The constant $c/64$ in the lower bound is weaker than the $c/(48(d-1))$ a one-cell argument gives. The $6K$ in the upper bound has ample slack: my proof sketch gives about $3.3K$.
- **`hf` is not redundant given `hf2`.** It supplies measurability, since $f^2$ can be integrable while $f$ is not measurable. In `groupMSE_quadratic` both `hf` and `hf2` are superfluous, because $f$ is quadratic on $I_k$; this is harmless.
- **`log(MSE)/d` converges slowly**, like $-\ln2-\ln d/d$: it is $-0.839$ at $d=16$ for $\Phi^{-1}$. This does not affect the truth of the limit statement.

---

## Definitions

### D1 `finMean`
**Rendering.** $\mathrm{finMean}(S,y)=\frac1{|S|}\sum_{j\in S}y_j$, a real number, with $0/0=0$ for $S=\emptyset$.

### D2 `lsqSlope`
**Rendering.** With $\bar\jmath=\mathrm{finMean}(S,\mathrm{id})$, $\mathrm{lsqSlope}(S,y)=\dfrac{\sum_{j\in S}(j-\bar\jmath)y_j}{\sum_{j\in S}(j-\bar\jmath)^2}$, the OLS slope. It is $0$ when the denominator is $0$, i.e. $|S|\le1$.

### D3 `lsqFit`
**Rendering.** $\mathrm{lsqFit}(S,y,j)=\bar y+\mathrm{lsqSlope}(S,y)\,(j-\bar\jmath)$, the OLS line in the index $j$, evaluated at any $j\in\mathbb N$.

### D4 `dyadicGroup`
**Rendering.** $\{0,1\}$ if $j<2$, otherwise $[2^{\lfloor\log_2 j\rfloor},2^{\lfloor\log_2 j\rfloor+1})$, the dyadic block of indices containing $j$ (`Nat.log 2 j` $=\lfloor\log_2 j\rfloor$ for $j\ge1$). Index $1$ is merged with $0$.

### D5 `method3Half`
**Rendering.** $\mathrm{lsqFit}(\mathrm{dyadicGroup}(j),\,y,\,j)$, where $y_j$ are the cell means at level $d$.

### D6 `method3Value`
**Rendering.** For $j<2^{d-1}$ (ℕ-subtraction, so $2^{0-1}=1$) this is `method3Half f d j`. Otherwise it is $-\,$`method3Half f d (2^d-1-j)`, i.e. minus the fit at the mirrored index; no truncation occurs, because $j<2^d$ in every use. For $d\ge2$ this is the stated "method 3": the lower half uses the LSQ affine fit per dyadic block, and the upper half is the odd mirror. For $d=1$ the group $\{0,1\}$ includes the upper-half cell; for $d=0$ it includes the cell $[1,2]$ outside $[0,1]$. These are junk cases, irrelevant to the limit theorems.

### D7 `method3MSE`
**Rendering.** $\sum_{j<2^d}\int_{C_j}(\mathrm{method3Value}(f,d,j)-f(u))^2\,du$.

### D8 `groupMSE`
**Rendering.** $\sum_{j\in S}\int_{C_j}(\mathrm{lsqFit}(S,y,j)-f(u))^2\,du$, the $L^2$ error of the method-3 rule restricted to the cells of $S$.

### D9 `dyadicMoment`
**Rendering.** $M_{d,k}=\sum_{j\in G_{d,k}}\big((j+\tfrac12)h-m_k\big)\int_{C_j}f$, where $(j+\frac12)h-m_k=(j-\bar\jmath)h$ is the cell midpoint centred at the midpoint of $I_k$. Index bounds use ℕ-subtraction, which is harmless when $d\ge k+1$.

### D10 `dyadicMomentLim`
**Rendering.** $\int_{I_k}(u-m_k)f(u)\,du$.

### D11 `dyadicAffineErr`
**Rendering.** $E_k(f)=\int_{I_k}f^2-2^{k+1}\big(\int_{I_k}f\big)^2-12\cdot8^{k+1}\big(\int_{I_k}(u-m_k)f\big)^2$. Since $|I_k|=2^{-(k+1)}$ and $\|u-m_k\|^2_{L^2(I_k)}=|I_k|^3/12$, this is $\|f\|^2-\|P f\|^2$, where $P$ is the orthogonal projection onto affine functions on $I_k$: the squared $L^2(I_k)$ distance from $f$ to the affine functions.

### D12 `method3Limit`
**Rendering.** $2\sum_{k\ge1}E_k(f)$, written as a `tsum` (which is $0$ if not summable). Under `hf2` it is summable, since $0\le E_k\le\int_{I_k}f^2$ and $\sum_k\int_{I_k}f^2\le\int_0^1f^2$. So the junk value never arises under the theorems' hypotheses.

### D13–D15 `gridPt`, `lutValue`, `method1MSE` (appended)
**Rendering.** $\mathrm{gridPt}(d,j)=j/2^d$; $\mathrm{lutValue}(f,d,j)=2^d\int_{C_j}f=y_j$; $\mathrm{method1MSE}(f,d)=\sum_{j<2^d}\int_{C_j}(y_j-f)^2=\sum_j\int_{C_j}(f-y_j)^2$, the $L^2$ error of the piecewise-constant cell-mean rule.

---

## Theorems

### 1. `sum_sq_lsqFit_le`
**Rendering.** For every finite $S\subset\mathbb N$, every $y:\mathbb N\to\mathbb R$ and all $a,b\in\mathbb R$: $\sum_{j\in S}(\mathrm{lsqFit}(S,y,j)-y_j)^2\le\sum_{j\in S}(a+bj-y_j)^2$.

**Assessment.** True; this is the least-squares optimality of the OLS line (normal equations / Pythagoras). Degenerate cases: for $S=\emptyset$ both sides are $0$. For $|S|=1$ the slope is the junk $0/0=0$, but it is multiplied by $j-\bar\jmath=0$, so the fit equals $y_j$ and the left side is $0$. The statement therefore does not depend on the junk value. `check_lsq.py`: 30,680 exact random comparisons, including non-contiguous $S$ and perturbations of the optimum, with 0 violations. Non-vacuous (no hypotheses).

### 2. `dyadic_groupMSE_eq`
**Rendering.** If $f\in L^1\cap L^2$ on $[0,1]$ and $k+2\le d$ (so $n\ge2$), then
$\mathrm{groupMSE}(f,d,G_{d,k})=\int_{I_k}f^2-2^{k+1}(\int_{I_k}f)^2-12\cdot8^{k+1}\frac{n^2}{n^2-1}M_{d,k}^2$, with $n=2^{d-k-1}$ (real).

**Assessment.** True.
- *Derivation.* $\int_{C_j}(c-f)^2=h(c-y_j)^2+\int_{C_j}(f-y_j)^2$ gives $\mathrm{groupMSE}=\int_{I_k}f^2-h\sum y_j^2+h\sum(\hat y_j-y_j)^2$. The OLS identity $\sum(\hat y-y)^2=\sum y^2-n\bar y^2-S_{xy}^2/S_{xx}$ holds with $S_{xx}=n(n^2-1)/12$, and $S_{xy}=M/h^2$.
- *Constants.* $h n\bar y^2=2^{k+1}(\int f)^2$ and $hS_{xy}^2/S_{xx}=12(nh)^{-3}\frac{n^2}{n^2-1}M^2$, with $(nh)^{-3}=8^{k+1}$.
- *Check.* `check_group_formulas.py` verifies the identity symbolically, with generic cell integrals $\int_{C_j}f$ and $\int_{C_j}f^2$ as free symbols, for all $k+2\le d\le7$.
- *Junk values.* None. The identity also holds at $d=k+1$ through $1/0=0$, but the hypothesis excludes that case. Under `hf`/`hf2` all integrals are genuine.
- *Non-vacuous.* Example: $f=\Phi^{-1}$ extended by $0$, $d=4$, $k=1$.

### 3. `tendsto_dyadic_groupMSE`
**Rendering.** If $f\in L^1\cap L^2$, then for each fixed $k\in\mathbb N$, $\mathrm{groupMSE}(f,d,G_{d,k})\to E_k(f)$ as $d\to\infty$.

**Assessment.** True. By (2), $n^2/(n^2-1)\to1$, and $|M_{d,k}-\int_{I_k}(u-m_k)f|\le\sum_j\int_{C_j}|(j+\tfrac12)h-u||f|\le\frac h2\int_{I_k}|f|\to0$. For small $d$ the index set is junk ($\emptyset$ when $d\le k$), which is irrelevant to the limit. Numerically, for $\Phi^{-1}$ and $k=0,1,2,3$ the ratio groupMSE$/E_k$ goes to $1.0000$ by $d\approx k+12$ (`check_group_limit.out`). This is the convergence of the discrete (cell-mean) LSQ fit to the continuous $L^2$ affine projection.

### 4. `dyadicAffineErr_isLeast`
**Rendering.** If $f\in L^1\cap L^2$, then for every $k$, $E_k(f)$ is the least element of $\{\int_{I_k}(a+bu-f(u))^2du:(a,b)\in\mathbb R^2\}$: it is attained, and it is a lower bound.

**Assessment.** True. The set $\{1,u-m_k\}$ is an orthogonal basis of the affine functions in $L^2(I_k)$; the minimiser is $b=12\cdot8^{k+1}\int(u-m_k)f$ and $a=2^{k+1}\int f-b\,m_k$, and the minimum is $\|f\|^2-\|Pf\|^2=E_k$. Under the hypotheses every integrand is integrable, so no junk $0$ integrals arise. Sympy confirms $E_k=\min_{a,b}$ for symbolic quadratics (`check_group_formulas.out`). This is the standard best-$L^2$-approximation result.

### 5. `tendsto_method3MSE`
**Rendering.** If $f\in L^1\cap L^2$ and $f(1-u)=-f(u)$ for all real $u$, then $\mathrm{method3MSE}(f,d)\to2\sum_{k\ge1}E_k(f)$.

**Assessment.** True.
- *Upper half.* Substituting $u\mapsto1-u$ and using oddness, the upper half equals the lower half.
- *Lower half.* For $d\ge2$ it equals $\mathrm{groupMSE}(\{0,1\})+\sum_{k=1}^{d-2}\mathrm{groupMSE}(G_{d,k})$.
- *Group $\{0,1\}$.* The 2-point fit reproduces the cell means, so this term is $\le\int_0^{2h}f^2\to0$.
- *Remaining groups.* Each term converges by (3) and is dominated by $\int_{I_k}f^2$ (by (2), since every subtracted term is $\ge0$), with $\sum_k\int_{I_k}f^2<\infty$. Tannery's theorem gives the limit.
- *Summability.* The `tsum` is summable, so no junk value is involved.
- *Exact check.* For $f=(u-\frac12)|u-\frac12|$, `method3MSE` computed literally from the definitions equals that decomposition exactly ($d=2..11$) and tends to $1/89280$ (ratio $1.00057$ at $d=11$).
- *$\Phi^{-1}$.* The MSE decreases towards the computed limit $\approx4.133\times10^{-5}$ (ratio $1.76$ at $d=12$; slow because the $\{0,1\}$ group contributes about $2^{-d}/d$).
- *Oddness needed.* For the even function $g=-(u-\frac12)^2$ the MSE tends to $0.025\ne$ method3Limit($g$).

The hypotheses are appropriate.

### 6. `method3Limit_pos`
**Rendering.** If $f\in L^1\cap L^2$, and for some $k\ge1$ and some $\mu>0$ we have $\mu s^2\le2f(u+s)-f(u)-f(u+2s)$ whenever $2^{-(k+1)}\le u$, $s\ge0$ and $u+2s\le2^{-k}$ (uniform strong midpoint concavity on $I_k$), then $\mathrm{method3Limit}(f)>0$.

**Assessment.** True. If $E_k=0$ then $f=a+bu$ a.e. on $I_k$ (by (4)). Fix a small $s>0$; for a.e. $u$ in the positive-measure set $[2^{-(k+1)},2^{-k}-2s]$ the three values $f(u),f(u+s),f(u+2s)$ are affine, which forces $0\ge\mu s^2$, a contradiction. All $E_j\ge0$ and the series is summable, so the `tsum` is at least $E_k>0$. No oddness is needed, correctly.
- *Satisfiable.* By $f=-u^2$ ($\mu=2$).
- *For $f=\Phi^{-1}$.* It holds with $k=2$ ($\inf D/s^2\approx6.68$, matching $-(\Phi^{-1})''(1/4)=6.679$) and $k=3$ ($\approx27.1$). It is **not** satisfied with $k=1$, since $D/s^2\to0$ as $u+2s=1/2$ and $s\to0$, because $(\Phi^{-1})''(1/2)=0$ (`check_phiinv_hyps.out`).

The hypothesis is pointwise and strong (it excludes, for example, functions that are affine on every $I_k$), but it is sufficient and reasonable.

### 7. `exists_tendsto_method3MSE`
**Rendering.** Under the hypotheses of (5) together with those of (6): there is $C>0$ with $\mathrm{method3MSE}(f,d)\to C$.

**Assessment.** True; it follows from (5) and (6) with $C=\mathrm{method3Limit}(f)$. It is non-vacuous: $f=\Phi^{-1}$ (extended by $0$ outside $(0,1)$, which keeps oddness) with $k=2$ and $\mu=6$; or $f=(u-\frac12)|u-\frac12|$ with $k=1$ and $\mu=2$.

### 8. `groupMSE_sub_half`
**Rendering.** For $f(u)=u-\frac12$ and $k+1\le d$: $\mathrm{groupMSE}(f,d,G_{d,k})=2^{-(k+1)}\,4^{-d}/12$.

**Assessment.** True. Cell means of an affine function are affine in $j$, so the fit reproduces them, and each cell contributes $h^3/12$; summing gives $n h^3/12=2^{-(k+1)}h^2/12$. For $n=1$ ($d=k+1$) the slope is $0/0=0$ but is multiplied by $0$, so there is no junk dependence. Sympy-verified for all $0\le k<d\le6$. This is the classical $h^2/12$ variance of a linear function on a cell.

### 9. `groupMSE_quadratic`
**Rendering.** If $f\in L^1\cap L^2$, $f(u)=\alpha+\beta u+\gamma u^2$ on the closed $I_k$, and $k+2\le d$, then $\mathrm{groupMSE}(f,d,G_{d,k})=E_k(f)+(\beta+2\gamma m_k)^2\,2^{-(k+1)}4^{-d}/12$.

**Assessment.** True. Write $f=A+Bt+\Gamma t^2$ with $t=u-m_k$ and $B=\beta+2\gamma m_k$. By symmetry $M_{d,k}=Bh^3n(n^2-1)/12$ and the continuous moment is $Bh^3n^3/12$. The difference of the two subtracted terms is then $12\cdot8^{k+1}\cdot B^2h^6n^4/144=B^2(nh)h^2/12$. Sympy-verified with symbolic $\alpha,\beta,\gamma$ for all $k+2\le d\le6$; additionally $E_k=\gamma^2|I_k|^5/180$ equals the true affine minimum. `hf`/`hf2` are superfluous but harmless. Non-vacuous (any quadratic).

### 10. `groupMSE_odd_quadratic`
**Rendering.** For $f(u)=(u-\frac12)|u-\frac12|$, all three of the following hold:
- (i) $\mathrm{method3Limit}(f)>0$;
- (ii) $\mathrm{method3MSE}(f,d)\to\mathrm{method3Limit}(f)$;
- (iii) for all $k\ge1$ and $d\ge k+2$: $E_k(f)>0$ and $\mathrm{groupMSE}(f,d,G_{d,k})=E_k(f)+(1-3/2^{k+1})^2\,2^{-(k+1)}4^{-d}/12$.

**Assessment.** True. $f$ is odd about $\frac12$ and continuous, and on $I_k\subset[0,\frac12]$ ($k\ge1$) it equals $-(u-\frac12)^2$, i.e. $\beta=1$, $\gamma=-1$, so $\beta+2\gamma m_k=1-3/2^{k+1}$. (iii) is therefore an instance of (9), with $E_k=2^{-5(k+1)}/180>0$. (ii) is an instance of (5). (i) holds because $\mathrm{method3Limit}=2\sum_{k\ge1}2^{-5(k+1)}/180=1/89280$. All three were verified exactly (sympy and exact rational evaluation of the definitions). The restriction $k\ge1$ is essential, since $I_0$ lies in the other branch of $|\cdot|$, and the statement respects it.

### 11. `method1MSE_le_order`
**Rendering.** Let $f\in L^1\cap L^2$ with $f(1-u)=-f(u)$, and let $K\in\mathbb R$ be such that for every $m\ge1$ and all $2^{-(m+1)}\le u\le v\le2^{-m}$: $m(f v-f u)^2\le K(2^m(v-u))^2$ (a Lipschitz constant $\sqrt{K/m}\,2^m$ on block $m$). Then for every $d\ge1$: $\mathrm{method1MSE}(f,d)\le6K\,2^{-d}/d$.

**Assessment.** True.
- *Cells $j\ge1$.* In the lower half they lie inside single blocks $m\in[1,d-1]$; Lipschitz functions satisfy cell variance $\le L^2h^3/12$, so block $m$ contributes $\le K2^{-d}2^{m-d}/(24m)$.
- *Cell 0.* $[0,h]=\bigcup_{m\ge d}$ block $m$. Chaining block endpoints gives $|f(u)-f(h)|\le(m-d+1)\sqrt{K/(4d)}$ on block $m$, so its contribution is $\le\frac{K}{4d}2^{-d}\sum_{i\ge1}i^22^{-i}=1.5K2^{-d}/d$.
- *Total.* Oddness doubles everything: $\le K\frac{2^{-d}}{d}\big(3+\frac{d}{12}\sum_{m<d}2^{m-d}/m\big)\le3.14K\frac{2^{-d}}d$ (since $\max_d d\sum_{m<d}2^{m-d}/m=5/3$).
- *Numerics.* $\Phi^{-1}$ gives $2^dd\,\mathrm{MSE}\approx1.55$ against $6K\approx19.1$; the piecewise-linear $c=K=1$ example gives $\le1.07$ against $6$.
- *Remarks.* $K<0$ makes `hup` unsatisfiable (vacuous case only). `hodd` is genuinely needed, since nothing else controls $f$ on $[1/2,1]$. `hlo` is correctly not assumed.

### 12. `method1MSE_ge_order`
**Rendering.** Let $f\in L^1\cap L^2$, $c\ge0$, and suppose that for every $m\ge1$ and all $2^{-(m+1)}\le u\le v\le2^{-m}$: $c(2^m(v-u))^2\le m(f v-f u)^2$. Then for every $d\ge2$: $\frac{c}{64}\,2^{-d}/d\le\mathrm{method1MSE}(f,d)$.

**Assessment.** True. The single cell $[h,2h]$ equals block $m=d-1\ge1$. Its variance is $\frac1{2h}\iint(f(x)-f(y))^2\ge\frac{c\,4^{d-1}}{(d-1)}\frac{h^3}{12}=\frac{c\,2^{-d}}{48(d-1)}\ge\frac c{64}\frac{2^{-d}}d$, and this holds even for non-monotone $f$. No oddness is needed, correctly. $c=0$ is trivial since the MSE is $\ge 0$. Satisfiable with $c>0$ by $\Phi^{-1}$ ($c=1/(2\ln2)$, the infimum over all blocks, approached from above as $m\to\infty$) and by the piecewise-linear example ($c=1$). The constant $1/64$ is not sharp.

### 13. `method1MSE_order`
**Rendering.** If $f\in L^1\cap L^2$ is odd about $\frac12$, $c>0$, and both block inequalities (`hlo` with $c$, `hup` with $K$) hold, then $K>0$, and for all $d\ge2$: $\frac c{64}2^{-d}/d\le\mathrm{method1MSE}(f,d)\le6K\,2^{-d}/d$.

**Assessment.** True. $K>0$: taking $u=1/4$, $v=1/2$ in block 1 gives $0<c/4\le(f(1/2)-f(1/4))^2\le K/4$. The two bounds follow from (11) and (12). Non-vacuous: $\Phi^{-1}$ with $c=0.72$ and $K=3.18$ (checked for $m\le4000$ with the asymptotes $1/(2\ln 2)$ and $2/\ln2$, and with 7,200 random pairs for $m\le24$, all inside $[c,K]$), or the piecewise-linear example with $c=K=1$.

### 14. `tendsto_log_method1MSE_div`
**Rendering.** Under the hypotheses of (13): $\log(\mathrm{method1MSE}(f,d))/d\to-\log2$ as $d\to\infty$ ($d$ cast to $\mathbb R$).

**Assessment.** True. For $d\ge2$, $\log(c/64)-d\log2-\log d\le\log\mathrm{MSE}\le\log(6K)-d\log2-\log d$. The MSE is strictly positive for $d\ge2$, so `Real.log` is not evaluated at a junk point, and the $x/0$ at $d=0$ is irrelevant to the limit. Numerically, for $\Phi^{-1}$ the value is $-0.839$ at $d=16$, approaching $-0.693$ like $-\ln2-\ln d/d$. This is the exponential rate $2^{-d}$ of the cell-mean lookup-table error for $\Phi^{-1}$, up to the $1/d$ factor.
