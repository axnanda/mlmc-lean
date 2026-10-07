# Blind read-back report: R12 (1-D elliptic finite differences)

| Field | Value |
|---|---|
| Date | 2026-10-07 |
| Packet | `readback/round16/packet_R12_elliptic.lean` |
| Declarations audited | 24 (12 theorems, 9 module definitions, 3 appended definitions) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round16/work_R12/` (`sym_check.py/.out`, `num_check.py/.out`, `num_check2.py/.out`, `scratch.lean/.out`) |

Tooling: `scratch.lean` is a copy of the packet (proofs still `sorry`) compiled with
`lake env lean -DautoImplicit=false` under `import MlmcLean`, inside a fresh namespace `Audit`.
It also runs `#check`/`#print` on the repository constants with `pp.numericTypes` and `pp.coercions` turned on.
Every packet statement elaborates identically to the repository constant. All casts are real:
`1 / N` in `isEllipticFD_iff_fe` is `(1:ℝ)/↑N`, and every `1 / 2` is `(1/2 : ℝ)`, never ℕ-division.
`2 ^ (ℓ+1)` in `ellipticPl` is a natural number.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| D1 | `ellipticMoment` | def | faithful ($M_k=\int_0^1 t^k/(1+at)\,dt$) | – | – |
| D2 | `ellipticFDMoment` | def | faithful (midpoint rule for $M_k$) | – | – |
| D3 | `IsEllipticSol` | def | faithful classical formulation | – | no |
| D4 | `ellipticSol` | def | faithful: the exact solution (sympy) | – | no (for $a>-1$) |
| D5 | `IsEllipticFD` | def | faithful flux FD scheme | – | no |
| D6 | `ellipticFDSol` | def | faithful: the exact discrete solution (sympy, $N\le 6$) | – | no (for $N\ge1$, $a\ge0$) |
| D7 | `ellipticFDOutput` | def | faithful composite trapezoid | – | $N=0$ gives 0, never used |
| D8 | `ellipticP` | def | faithful $P=\int_0^1u$ | – | no |
| D9 | `ellipticPl` | def | faithful, $N=2^{\ell+1}$, $h_\ell=2^{-(\ell+1)}$ | – | no |
| D10 | `feStiffness` | def | P1 stiffness row (midpoint coefficient quadrature) | – | – |
| D11 | `feLoad` | def | P1 load row (midpoint quadrature) | – | – |
| D12 | `hatNodal` | def | nodal values of the hat function $\varphi_j$ | – | – |
| 1 | `isEllipticSol_ellipticSol` | theorem | TRUE | no | no |
| 2 | `eq_ellipticSol_of_isEllipticSol` | theorem | TRUE | no | no |
| 3 | `isEllipticFD_ellipticFDSol` | theorem | TRUE | no | no |
| 4 | `isEllipticFD_iff` | theorem | TRUE | no | no |
| 5 | `isEllipticFD_iff_fe` | theorem | TRUE | no | no ($N\le1$: both sides reduce to the boundary conditions) |
| 6 | `ellipticFD_error` | theorem | TRUE (constant 1/3 loose: true max is 1/12) | no | no |
| 7 | `ellipticFD_error_ge` | theorem | TRUE (constant 1/96 loose: true min ≈ 0.0573) | no | no |
| 8 | `ellipticFD_nodal_error` | theorem | TRUE (very loose: true max ≈ 0.00761) | no | no |
| 9 | `ellipticPl_error` | theorem | TRUE | no | no |
| 10 | `ellipticK_moments` | theorem | TRUE | no | no |
| 11 | `not_ae_abs_ellipticP_sub_le` | theorem | TRUE | no | no |
| 12 | `elliptic_fd_rates` | theorem | TRUE | no | no (integrability and $L^2$ asserted; the variance is genuine) |

## Main points for a human auditor

- **No false, vacuous or junk-dependent statement found.** sympy confirms the definitions are the exact
  continuous solution (symbolic $a>0$, $f$) and the exact discrete solution (symbolic $a, f$, $N=1..6$).
  Solving the linear system symbolically for $N\le5$ gives a unique solution, equal to
  `ellipticFDSol`. The FE identity `feStiffness − feLoad = −(1/N)·(FD residual + f)` holds for $N=2..6$.
- **Closed forms behind the bounds.** For $f=1$: $P=M_2-M_1^2/M_0$ and $P_h=\tilde M_2-\tilde M_1^2/\tilde M_0$,
  where $\tilde M_k$ is the midpoint-rule value of $M_k$ (checked symbolically for $N\le5$). Both are
  minima over $C$ of $\int (t-C)^2 w$, resp. $Q_h[(t-C)^2w]$, with $w=1/(1+at)$. The function $g_C=(t-C)^2w$ is convex,
  with $g_C''=2(1+aC)^2/(1+at)^3$. The midpoint-rule error therefore gives
  $\frac{h^2}{96}\le \frac{h^2(1+aC^*)^2}{12(1+a)^3}\le P-P_h\le \frac{h^2(1+aC_h)^2}{12}\le \frac{h^2}{3}$
  for $0\le a\le1$. This proves 6 and 7 for every $N\ge1$, and shows the error has a fixed sign.
- **The constants are loose but correct.** Numerically, $(P-P_h)/(f h^2)\in[0.0573,\,1/12]$: max at $a=0$, min at
  $a=1,N=1$. The nodal error ratio is $\le 0.00762$, against a stated $1/3$. A short rigorous argument gives $\le h^2/4$
  (see 8).
- **Probability hypotheses are adequate.** `HasLaw Z (gaussianReal 0 1) μ` forces $\mu$ to be a probability measure,
  because `μ.map Z` is a probability measure and $Z$ is a.e.-measurable. Theorem 12 assumes `AEMeasurable a`, which
  is needed for the measurability of $\omega\mapsto P(a(\omega),\cdot)$. Theorem 11 does not need it, which is
  legitimate. In 12, `Integrable` and `MemLp … 2` are part of the conclusion, so $\mathbb E[P_\ell-P]$ and the
  variance are genuine.
- **The "random forcing" is spatially constant.** $f=50Z^2$ does not depend on $x$, and the randomness in $a$ is
  only a coefficient slope in $[0,1]$. This is a deliberately simple, one-parameter-per-sample model problem, not a
  general random PDE.
- **Exact arithmetic of the constants.** $62500/3=(250/3)^2\cdot3$ comes from
  $|P_{\ell+1}-P_\ell|\le\frac{50}{3}Z^2(h_{\ell+1}^2+h_\ell^2)=\frac{250}{3}Z^2h_{\ell+1}^2$ and $\mathbb E Z^4=3$.
  The variance bound is indexed by $h_{\ell+1}=2^{-(\ell+2)}$, the fine level of the correction $P_{\ell+1}-P_\ell$.
  This gives rates $\alpha=2$ and $\beta=4$ in $h$.
- **Assumptions stronger than needed.** Theorems 1–4 assume $a\ge0$ where $a>-1$ (for 3 and 4: all
  $1+a x_{i+1/2}\ne0$ and $\tilde M_0\ne0$) would suffice. This only restricts generality.

---

## Definitions

### D1 `ellipticMoment a k`
**Rendering.** $M_k(a)=\int_0^1 \frac{t^k}{1+at}\,dt$ (interval integral; for $a\le -1$ the integrand is
singular or non-integrable and the value is a junk value, but every theorem assumes $a\ge0$).

### D2 `ellipticFDMoment a N k`
**Rendering.** $\tilde M_k(a,N)=\sum_{i=0}^{N-1}\frac1N\,\frac{x_{i+1/2}^k}{1+a x_{i+1/2}}$ with
$x_{i+1/2}=(i+\tfrac12)/N$, which is the composite midpoint rule for $M_k$. It equals $0$ for $N=0$.

### D3 `IsEllipticSol a f u`
**Rendering.** $u$ is continuous on $[0,1]$ and differentiable on $(0,1)$. For every $x\in(0,1)$ the function
$y\mapsto(1+ay)\,u'(y)$ has derivative $-f$ at $x$, where $u'$ is `deriv u`, a genuine derivative on the open set
$(0,1)$. Finally $u(0)=u(1)=0$. This is the classical form of $((1+ax)u')'=-f$ with homogeneous Dirichlet conditions,
for constant $f\in\mathbb R$. Only values of `deriv u` inside $(0,1)$ are used, so no junk value is involved.

### D4 `ellipticSol a f x`
**Rendering.** $u(x)=\int_0^x \frac{fC-ft}{1+at}\,dt$ with $C=M_1/M_0$. Check: the flux is $(1+at)u'=f(C-t)$, so its
derivative is $-f$. $u(0)=0$, and $u(1)=f(CM_0-M_1)=0$. sympy (`sym_check.out`) gives
$u=\frac{f\,\log\frac{1+ax}{(1+a)^x}}{a\log(1+a)}$, flux derivative $-f$, $u(0)=u(1)=0$, and
$\int_0^1u=f(M_2-M_1^2/M_0)$. At $a=0$: $u=fx(1-x)/2$ and $P=f/12$.

### D5 `IsEllipticFD a f N U`
**Rendering.** $U:\mathbb N\to\mathbb R$ with $U_0=0$, $U_N=0$, and for $0<j<N$:
$\big[c_{j+1/2}(U_{j+1}-U_j)-c_{j-1/2}(U_j-U_{j-1})\big]/h^2=-f$, where $h=1/N$ and $c_{j\pm1/2}=1+a(j\pm\frac12)/N$.
Both are real casts. `j - 1` is ℕ-subtraction, harmless since $j\ge1$. This is the standard conservative
second-order scheme with fluxes at the half-points. Values $U_j$ for $j>N$ are unconstrained.

### D6 `ellipticFDSol a f N j`
**Rendering.** $U_j=\sum_{i<j}\frac1N\,\frac{fC_h-fx_{i+1/2}}{1+ax_{i+1/2}}$ with $C_h=\tilde M_1/\tilde M_0$, the
discrete analogue of D4: the discrete flux is $f(C_h-x_{i+1/2})$, and $U_N=f(C_h\tilde M_0-\tilde M_1)=0$.
sympy confirms all scheme residuals vanish for $N=1..6$, symbolic $a, f$.

### D7 `ellipticFDOutput N U`
**Rendering.** $\frac1N\big(\frac{U_0+U_N}2+\sum_{j=1}^{N-1}U_j\big)$, the composite trapezoidal rule on the grid values.
The `N - 1` is ℕ-subtraction; for $N=0$ the value is 0, which never occurs in the theorems ($N>0$ or $N=2^{\ell+1}$).

### D8 `ellipticP a f`
**Rendering.** $P(a,f)=\int_0^1 u_{a,f}(x)\,dx$ with $u$ from D4. It is exactly linear in $f$.

### D9 `ellipticPl a f ℓ`
**Rendering.** $P_\ell(a,f)=$ the trapezoid output of the discrete solution with $N=2^{\ell+1}$ (ℕ), so
$h_\ell=2^{-(\ell+1)}$.

### D10 `feStiffness N h c u j`
**Rendering.** $\sum_{e<N} h\,c((e+\frac12)h)\,\frac{u_{e+1}-u_e}{h}\,\frac{\varphi_j(e+1)-\varphi_j(e)}{h}$, the $j$-th
row of the P1 finite-element stiffness form with the coefficient sampled at element midpoints.

### D11 `feLoad N h f j`
**Rendering.** $\sum_{e<N} h\,f((e+\frac12)h)\,\frac{\varphi_j(e+1)+\varphi_j(e)}2$, the P1 load vector with midpoint
quadrature.

### D12 `hatNodal j i`
**Rendering.** $\varphi_j(x_i)=\delta_{ij}$.

---

## Theorems

### 1. `isEllipticSol_ellipticSol`
**Rendering.** For $a\ge0$ and every $f\in\mathbb R$, `ellipticSol a f` satisfies D3.

**Assessment.** True. The integrand is continuous on $(-1/a,\infty)\supset[0,1]$, so by the FTC $u'=f(C-x)/(1+ax)$ and the
flux is $f(C-x)$, with derivative $-f$. $u(0)=0$ is an empty integral, and $u(1)=0$ because $C=M_1/M_0$ and $M_0>0$. Verified
symbolically in `sym_check.out`. Not vacuous: there are no hypotheses beyond $a\ge0$. No junk dependence: $M_0>0$, so
the division is genuine. The hypothesis $a\ge0$ is stronger than the natural $a>-1$. Standard fact: explicit solution of a 1-D
divergence-form two-point BVP.

### 2. `eq_ellipticSol_of_isEllipticSol`
**Rendering.** For $a\ge0$, if $u$ satisfies D3, then $u(x)=$ `ellipticSol a f x` for all $x\in[0,1]$, and
$\int_0^1u=P(a,f)$.

**Assessment.** True (uniqueness). On $(0,1)$ the flux has derivative $-f$, so $(1+ay)u'(y)=K-fy$. Since $u$ is
continuous on $[0,1]$ with a bounded continuous derivative on $(0,1)$, the FTC gives $u(x)=\int_0^x\frac{K-ft}{1+at}dt$.
Then $u(1)=0$ forces $K=fM_1/M_0$. The integral identity follows because the two functions agree on $[0,1]$. Not vacuous:
theorem 1 provides $u$. No junk values. Standard fact: uniqueness for the Dirichlet problem.

### 3. `isEllipticFD_ellipticFDSol`
**Rendering.** For $a\ge0$, $f\in\mathbb R$ and $N\ge1$, `ellipticFDSol a f N` satisfies D5.

**Assessment.** True. $U_{j+1}-U_j=h f(C_h-x_{j+1/2})/c_{j+1/2}$, so the flux difference is $-fh\cdot h$, and dividing by
$h^2$ gives $-f$. $U_N=0$ because $C_h\tilde M_0=\tilde M_1$ and $\tilde M_0>0$. sympy confirms this for
$N=1..6$ with symbolic $a$ and $f$. Not vacuous, no junk values.

### 4. `isEllipticFD_iff`
**Rendering.** For $a\ge0$, $N\ge1$ and any $U:\mathbb N\to\mathbb R$: $U$ satisfies the scheme
$\iff U_j=$ `ellipticFDSol a f N j` for all $j\le N$.

**Assessment.** True. The scheme only involves $U_0..U_N$, which gives ⇐ via theorem 3. For ⇒, the discrete flux
satisfies $F_{j+1/2}=F_{1/2}-fjh$, so $U$ is determined up to $F_{1/2}$, and $U_N=0$ then fixes $F_{1/2}$ because
$\tilde M_0>0$. sympy `solve` gives a unique solution, equal to D6, for $N=1..5$. The interior determinants
(e.g. $-4(a+2)$, $\frac94(23a^2+108a+108)$) do not vanish for $a\ge0$. Not vacuous. Restricting the conclusion to
$j\le N$ is appropriate. Standard fact: unique solvability of the tridiagonal M-matrix system.

### 5. `isEllipticFD_iff_fe`
**Rendering.** For all $a,f\in\mathbb R$, $N\in\mathbb N$ and $U$: D5 holds $\iff U_0=0$, $U_N=0$, and for $0<j<N$
`feStiffness N (1/N) (x ↦ 1+a x) U j = feLoad N (1/N) (x ↦ f) j`, with $1/N$ real.

**Assessment.** True. For $0<j<N$ only the elements $e=j-1,j$ contribute. The stiffness row is
$[c_{j-1/2}(U_j-U_{j-1})-c_{j+1/2}(U_{j+1}-U_j)]/h$ and the load row is $hf$. So stiffness − load $=-h\,(\text{FD
expression}+f)$, a polynomial identity in $a$ (sympy, $N=2..6$), and $h=1/N\neq0$ whenever an interior $j$ exists.
For $N\le1$ both sides reduce to the boundary conditions. No junk dependence: the cast was checked, and $1/N$ is not ℕ-division
(which would have made the FE side trivially $0=0$). Standard fact: P1 FEM with midpoint quadrature on a uniform
mesh coincides with the flux FD scheme scaled by $h$.

### 6. `ellipticFD_error`
**Rendering.** For $0\le a\le1$, $N\ge1$, any exact solution $u$ (D3) and any discrete solution $U$ (D5):
$\big|\int_0^1u-\text{trap}_N(U)\big|\le\frac{|f|}{3}h^2$ with $h=1/N$.

**Assessment.** True. By theorems 2 and 4 the error is $f\cdot e(a,N)$, with
$e=(M_2-M_1^2/M_0)-(\tilde M_2-\tilde M_1^2/\tilde M_0)$, verified symbolically. With $g_C=(t-C)^2/(1+at)$ we have
$P=\min_C\int g_C$ and $P_h=\min_C Q_h[g_C]$, so $e\le(I-Q_h)[g_{C_h}]=\sum\frac{h^3}{24}g''(\xi_i)$.
Since $g_C''=2(1+aC)^2/(1+at)^3\le2(1+a)^2\le8$, this gives $e\le h^2/3$.
Numerically (`num_check.out`: $a\in\{0,0.01,\dots,1\}$, $N\le80$ and up to 512; `num_check2.out`: random $a$, $N\le3000$)
$\max e N^2=1/12$, attained at $a=0$. The bound therefore holds with a factor-4 margin, and no counterexample exists.
Not vacuous: theorems 1 and 3 provide $u$ and $U$. No junk values: $N>0$, and the integral is of a continuous function.
Standard fact: second-order convergence of the flux scheme combined with the trapezoidal output.

### 7. `ellipticFD_error_ge`
**Rendering.** Same hypotheses as 6. Then $\frac{|f|}{96}h^2\le\big|\int_0^1u-\text{trap}_N(U)\big|$.

**Assessment.** True. With $C^*=M_1/M_0\in(0,1)$:
$e\ge(I-Q_h)[g_{C^*}]\ge\frac{h^2}{24}\min g''=\frac{h^2(1+aC^*)^2}{12(1+a)^3}\ge\frac{h^2}{96}$.
Numerically $\min eN^2\approx0.05730$ (at $a=1,N=1$), and the limit coefficient lies in $[0.0650,0.0833]$. The error
never changes sign. Not vacuous, and nontrivial for $f\ne0$. Meaning: the $h^2$ rate is sharp, with no superconvergence of
the output.

### 8. `ellipticFD_nodal_error`
**Rendering.** Same hypotheses, and $j\le N$. Then $|u(j/N)-U_j|\le\frac{|f|}3h^2$.

**Assessment.** True. Numerically $\max_j|u(x_j)-U_j|N^2\le0.007613$ ($a=1$, large $N$). For $a=0$ the scheme is
nodally exact. Rigorous sketch for $f=1$:
$u(x_j)-U_j=(C-C_h)Q_j[w]+(I_j-Q_j)[(C-t)w]$. Here $((C-t)w)''=2a(1+aC)/(1+at)^3\in[0,3]$, so the second term lies in
$[0,h^2/8]$. In $C-C_h=(\delta_1M_0-M_1\delta_0)/(M_0\tilde M_0)$ we have $\delta_0\in[0,a^2h^2/12]$,
$\delta_1\in[-ah^2/12,0]$, $C\le\frac12$ and $\tilde M_0\ge\frac12$, so the first term lies in $[-h^2/4,0]$. Hence
$|u(x_j)-U_j|\le h^2/4<h^2/3$. Not vacuous, no junk values. Standard fact: $O(h^2)$ nodal accuracy.

### 9. `ellipticPl_error`
**Rendering.** For $0\le a\le1$, $Z\in\mathbb R$ and $\ell\in\mathbb N$:
$|P(a,50Z^2)-P_\ell(a,50Z^2)|\le\frac{50}{3}Z^2\,(2^{-(\ell+1)})^2$.

**Assessment.** True. This is theorem 6 with $u=$ D4, $U=$ D6, $N=2^{\ell+1}$ and $|f|=50Z^2$. It gives the random constant
$K=\frac{50}3Z^2$. Not vacuous, no junk values.

### 10. `ellipticK_moments`
**Rendering.** If $Z\sim\mathcal N(0,1)$ under $\mu$ (`HasLaw`, which forces $\mu$ to be a probability measure), then
$K=\frac{50}3Z^2\in L^2(\mu)$, $\mathbb E K=\frac{50}3$ and $\mathbb E K^2=\frac{2500}{3}$.

**Assessment.** True: $\mathbb EZ^2=1$ and $\mathbb EZ^4=3$, so $\mathbb EK^2=\frac{2500}{9}\cdot3$. Not vacuous
($\Omega=\mathbb R$, $\mu=\mathcal N(0,1)$, $Z=\mathrm{id}$). No junk values: MemLp is asserted, so the integrals are genuine.

### 11. `not_ae_abs_ellipticP_sub_le`
**Rendering.** Let $a:\Omega\to\mathbb R$ with $a\in[0,1]$ a.s. (no measurability assumed) and $Z\sim\mathcal N(0,1)$. Then
for every $\ell$ and every deterministic $K\in\mathbb R$, it is not true that
$|P(a,50Z^2)-P_\ell(a,50Z^2)|\le K h_\ell^2$ almost surely.

**Assessment.** True. By theorem 7, the error is a.s. at least $\frac{50Z^2}{96}h_\ell^2$, so the a.s. bound would force
$Z^2\le\frac{96K}{50}$ a.s. But $\mu\{Z^2>c\}=\mathcal N(0,1)\{x^2>c\}>0$ (via `map_apply_of_aemeasurable`). The
missing measurability of $a$ is harmless for a negated a.e. statement. Not vacuous: same instance as 10, with $a\equiv\frac12$.
Meaning: no deterministic constant works, which justifies the random $K$.

### 12. `elliptic_fd_rates`
**Rendering.** Let $a$ be a.e.-measurable with $a\in[0,1]$ a.s., and $Z\sim\mathcal N(0,1)$. Write $P=P(a,50Z^2)$,
$P_\ell=P_\ell(a,50Z^2)$ and $h_\ell=2^{-(\ell+1)}$. Then for every $\ell$:
$P\in L^2$; $P_\ell\in L^2$; $P_\ell-P$ is integrable; $|\mathbb E[P_\ell-P]|\le\frac{50}3h_\ell^2$;
$P_{\ell+1}-P_\ell\in L^2$; $\mathrm{Var}(P_{\ell+1}-P_\ell)\le\mathbb E[(P_{\ell+1}-P_\ell)^2]\le\frac{62500}3h_{\ell+1}^4$.

**Assessment.** True.
- *Measurability.* $P=50Z^2p(a)$ with $p$ continuous on $(-1,\infty)$. Since $p\circ a$ equals $p\circ\mathrm{clamp}\circ a$
  a.e., it is AE-strongly measurable. $P_\ell=50Z^2\,T_\ell(a)$ with $T_\ell$ a measurable rational expression.
- *Bounds.* $|P|,|P_\ell|\le CZ^2\in L^2$ because $\mathbb EZ^4=3$. From theorem 9 and $\mathbb EZ^2=1$:
  $|\mathbb E[P_\ell-P]|\le\frac{50}3h_\ell^2$. By the triangle inequality,
  $|P_{\ell+1}-P_\ell|\le\frac{50}3Z^2(h_{\ell+1}^2+4h_{\ell+1}^2)$, so its second moment is at most
  $\frac{62500}{9}\cdot3\,h_{\ell+1}^4$. $\mathrm{Var}\le\mathbb E X^2$ holds for a probability measure, and $X\in L^2$ makes
  the variance genuine.
- *Numerics* (`num_check2.out`, deterministic $a$): the weak-error ratio to the bound is $\approx0.19$–$0.25$, and the
  second-moment ratio is $\approx0.012$–$0.023$.

Not vacuous: as in 10, with $a\equiv\frac12$. No junk values: integrability and $L^2$ membership are part of the
conclusion. `AEMeasurable a` is a needed and natural hypothesis. Standard result: MLMC rate assumptions with $\alpha=2$
(weak error in $h_\ell$) and $\beta=4$ (variance of the level correction in $h_{\ell+1}$).
