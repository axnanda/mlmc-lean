# Blind read-back report: R16 (drift-implicit Euler, integrating factor, explicit Euler)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round17/packet_R16_driftimplicit.lean` |
| declarations audited | 20 (14 theorems, 6 definitions) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round17/work_R16/` (`threshold.py`, `moments.py`, `linear.py`, `em_cubic.py`, each with a `.out` file; `Scratch.lean`/`Scratch.out` is the elaboration check) |

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `implicitStep` | def | n/a | n/a | uses `Function.invFun`. The value is unspecified only when there is no preimage, and the theorems never reach that case (see 7–10, 13) |
| 2 | `implicitPath` | def | n/a | n/a | no |
| 3 | `linRecPath` | def | n/a | n/a | no (not used by any theorem in the packet) |
| 4 | `intFactorPath` | def | n/a | n/a | no |
| 5 | `emPath` (appended) | def | n/a | n/a | no ($\sqrt h$ is junk for $h<0$, but every theorem assumes $h\ge0$) |
| 6 | `eulerDriftStep` (appended) | def | n/a | n/a | no |
| 7 | `existsUnique_implicitStep` | theorem | true | no | no |
| 8 | `abs_implicitStep_sub_le` | theorem | true | no | no (the denominator $1-hK>0$) |
| 9 | `continuous_implicitStep_add` | theorem | true | no | no |
| 10 | `abs_implicitStep_le` | theorem | true | no | no (any preimage satisfies the bound, and one always exists) |
| 11 | `implicitCubic_abs_antitone` | theorem | true | no | no |
| 12 | `implicitCubic_tendsto_zero` | theorem | true | no | no |
| 13 | `implicitCubic_stable_explicitCubic_threshold` | theorem | true (threshold $h x_0^2\le 2$ is exact, boundary included) | no | no |
| 14 | `implicitPath_moments_le` | theorem | true | no | no ($\mu$ is forced to be a probability measure, even for $N=0$) |
| 15 | `implicitCubic_moments_le` | theorem | true | no | $T/0=0$ at $N=0$ is harmless (the bound still holds) |
| 16 | `implicit_vs_explicit_cubic_moments` | theorem | true | no | no (the explicit-Euler moments are finite and really diverge) |
| 17 | `intFactorPath_second_moment_eq` | theorem | true | no | no |
| 18 | `intFactorPath_second_moment_le` | theorem | true | no | no |
| 19 | `emLinear_second_moment_eq` | theorem | true | no | no |
| 20 | `emLinear_second_moment_tendsto_atTop` | theorem | true | no | no |

## Main points for a human auditor

1. **The implicit step uses `Function.invFun`.** By definition, `invFun f r` is `Classical.choose` of a preimage when one exists, and `Classical.arbitrary ℝ` otherwise (checked with `#print`). No theorem depends on the arbitrary value:
   - In theorems 7–9 and 14, the one-sided Lipschitz bound with $hK<1$ plus continuity makes $y\mapsto y-ha(y)$ a bijection.
   - In theorem 10 there is no `hK`, so uniqueness can fail. Continuity plus $y\,a(y)\le0$ still gives surjectivity by the IVT, and *every* preimage satisfies $|y|\le|r|$.
   - For the cubic drift, $y\mapsto y+hy^3$ is a bijection for $h\ge0$.

   Continuity of $a$ is genuinely needed: with a jump, no preimage may exist.
2. **Thresholds checked numerically.**
   - Explicit cubic Euler: $\sup_n|E^n x_0|<\infty \iff hx_0^2\le 2$ is exact. At $u=hx_0^2=2$ the orbit is the exact 2-cycle $x_0,-x_0$. For $u\in[0,2]$, $u\mapsto u(1-u)^2$ maps $[0,2]$ into itself. For $u>2$ it blows up doubly exponentially (`threshold.out`).
   - Euler–Maruyama (EM) for the linear drift: $Lh>2$ gives $|1-Lh|>1$. The strict inequality is slightly weaker than possible: at $Lh=2$ with $\sigma\ne0$ the second moment also diverges, linearly. This is not an error.
3. **The implicit-scheme moment bounds are true and uniform in the step size.** They are exactly the moments of the driftless process $x_0+\sigma W_{Nh}$; with $h=T/N$ they depend only on $T$. The proof route: $|Y(r)|\le|r|$, so $E X_{n+1}^p\le E(X_n+\sigma\sqrt h Z_n)^p$ for $p=2,4$. Quadrature and Monte Carlo agree, and the bounds are loose (`moments.out`).
4. **Explicit-Euler divergence for $-x^3$** (the Hutzenthaler–Jentzen–Kloeden 2011 phenomenon) is true for every $x_0$ and every $T>0$. A rigorous lower bound (`em_cubic.out`) gives $E X_N^2\ge P(A_N)\cdot 2\cdot4^{3^{N-1}}N/T$ with $P(A_N)\gtrsim e^{-cN^2}$, which tends to $\infty$; for $T=1$ and $N=8$ it already exceeds $10^{1205}$. The convergence is not monotone: the exact values for $T=1,x_0=0$ are $1,0.719,0.549$ at $N=1,2,3$. The fourth-moment claim follows by Jensen's inequality.
5. **Noise model.** $\Delta W_n=\sqrt h Z_n$, with $\mu.\mathrm{map}(Z_n)=\mathcal N(0,1)$ for $n<N$ and `iIndepFun` over `Fin N`. `iIndepFun.isProbabilityMeasure` (Mathlib, applied to the empty index set) forces $\mu(\Omega)=1$, even for `Fin 0`. Without this, the $N=0$ cases with $x_0\ne0$ (the `MemLp` claim and $\int x_0^2\,d\mu\le x_0^2$) could fail.
6. **Integrability.** Every integrand is genuinely integrable, so no Bochner junk value of 0 occurs:
   - implicit path: $|X_N|\le|x_0|+|\sigma|\sqrt h\sum|Z_k|$;
   - linear schemes: affine in Gaussians;
   - explicit cubic EM: a polynomial in Gaussians.
7. **Narrower than the standard result (not wrong).** `implicitPath_moments_le` assumes *global* dissipativity $y\,a(y)\le0$ in addition to one-sided Lipschitz. This excludes, for example, the double-well drift $y-y^3$, for which the usual bound has the form $C(1+x_0^2)e^{CT}$.
8. **Unused definition.** `linRecPath` is defined but used by none of the 14 theorems.

## Per-declaration sections

### 1. `implicitStep`
**Rendering.** $Y_{a,h}(r):=\mathrm{invFun}(g)(r)$ with $g(y)=y-h\,a(y)$. That is, $Y(r)$ is a chosen (`Classical.choose`) $y$ with $y-ha(y)=r$ if such a $y$ exists, and a fixed arbitrary real otherwise. It is one step of backward Euler: $Y(r)$ solves $Y=r+ha(Y)$.

**Assessment.** It is a definition. Whether the theorems depend on the junk branch is examined in each theorem below; none does.

### 2. `implicitPath`
**Rendering.** $X_0=x_0$ and $X_{n+1}=Y_{a,h}(X_n+\sigma\sqrt h\,z_n)$, so $X_{n+1}=X_n+h\,a(X_{n+1})+\sigma\sqrt h z_n$. This is the drift-implicit Euler scheme with additive noise, with $\Delta W_n=\sqrt h z_n$. (`√h` is `Real.sqrt`.)

### 3. `linRecPath`
**Rendering.** $X_0=x_0$ and $X_{n+1}=\rho X_n+s z_n$, a scalar AR(1) recursion. No theorem in the packet uses it.

### 4. `intFactorPath`
**Rendering.** $X_0=x_0$ and $X_{n+1}=e^{-Lh}(X_n+\sigma\sqrt h z_n)$. This is the integrating-factor (Lawson-type exponential Euler) scheme for $dX=-LX\,dt+\sigma\,dW$.

### 5. `emPath` (appended)
**Rendering.** $S_0$ given, and $S_{i+1}=S_i+a(S_i,ih)h+b(S_i,ih)\sqrt h z_i$: Euler–Maruyama with $i$ cast to ℝ.

### 6. `eulerDriftStep` (appended)
**Rendering.** $E_{b,h}(S)=S+h\,b(S)$, one explicit Euler step of the ODE $\dot S=b(S)$.

### 7. `existsUnique_implicitStep`
**Rendering.** Assume $a$ continuous, $(a(x)-a(y))(x-y)\le K(x-y)^2$ for all $x,y$ (one-sided Lipschitz, $K\in\mathbb R$ arbitrary), $h\ge0$ and $hK<1$. Then for all $x,c$: (i) there is a unique $y$ with $y=x+ha(y)+c$; and (ii) $Y(x+c)=x+h\,a(Y(x+c))+c$.

**Assessment.** True. Let $g(y)=y-ha(y)$. Then $(g(x)-g(y))(x-y)\ge(1-hK)(x-y)^2>0$, so $g$ is strictly increasing with slope at least $1-hK$. Hence $g$ is coercive and continuous, so bijective. (i) is $g(y)=x+c$; (ii) follows from `invFun_eq` because a preimage exists. Not vacuous: for example $a(y)=-y^3$, $K=0$, any $h\ge0$. No junk value is involved. Continuity is necessary: $a=-\mathrm{sign}$ is one-sided Lipschitz with $K=0$, but $g$ skips $(-h,h)$. This is the standard solvability of the implicit Euler equation under a monotonicity (one-sided Lipschitz) condition.

### 8. `abs_implicitStep_sub_le`
**Rendering.** Under the same hypotheses, for all $r,r'$: $|Y(r)-Y(r')|\le |r-r'|/(1-hK)$.

**Assessment.** True. With $y=Y(r)$ and $y'=Y(r')$, we have $(r-r')(y-y')=(y-y')^2-h(a(y)-a(y'))(y-y')\ge(1-hK)(y-y')^2$. Divide by $|y-y'|$. The denominator $1-hK$ is positive, so no $x/0$ issue arises. Not vacuous (same example). This is the standard Lipschitz bound for the resolvent $(I-ha)^{-1}$.

### 9. `continuous_implicitStep_add`
**Rendering.** Under the same hypotheses, $(p_1,p_2)\mapsto Y(p_1+p_2)$ is continuous and measurable on $\mathbb R^2$.

**Assessment.** True, as a corollary of 8 (Lipschitz implies continuous implies Borel measurable). Not vacuous, and no junk value.

### 10. `abs_implicitStep_le`
**Rendering.** Assume $a$ continuous, $y\,a(y)\le0$ for all $y$, and $h\ge0$. Then $|Y(r)|\le|r|$ for every $r$. There is **no** one-sided Lipschitz hypothesis.

**Assessment.** True.
- *Existence:* continuity plus $ya(y)\le0$ gives $g(y)\ge y$ for $y>0$ and $g(y)\le y$ for $y<0$, so $g$ is surjective by the IVT. Hence `invFun` returns a genuine preimage.
- *Bound:* for any preimage, $ry=y^2-h\,y\,a(y)\ge y^2$, so $|y|\le|r|$.

The theorem therefore holds whichever preimage `Classical.choose` picks, and the arbitrary branch is never reached. Not vacuous ($a=-y^3$). This is the standard contractivity of backward Euler for a dissipative drift.

### 11. `implicitCubic_abs_antitone`
**Rendering.** For $h\ge0$ and every $x_0$, $n\mapsto|Y^{n}(x_0)|$ is non-increasing on ℕ, where $Y$ is the implicit step for $a(y)=-y^3$. (The elaboration check shows `-y ^ 3` is `-(y ^ 3)`; for an odd power the reading does not matter anyway.)

**Assessment.** True by 10, since $y\cdot(-y^3)=-y^4\le0$. At $h=0$ the sequence is constant. Numerically confirmed (`threshold.out`). This is the unconditional stability of backward Euler for $\dot x=-x^3$.

### 12. `implicitCubic_tendsto_zero`
**Rendering.** For $h>0$ and every $x_0$, $Y^n(x_0)\to0$.

**Assessment.** True. $|x_n|$ decreases to some $\ell\ge0$, and $|x_n|-|x_{n+1}|=h|x_{n+1}|^3\ge h\ell^3$ (the iterates keep their sign), which forces $\ell=0$. $h>0$ is needed; at $h=0$ the sequence is constant. Numerically, $x_n\approx 1/\sqrt{2hn}$ (`threshold.out`). This is the global asymptotic stability of backward Euler for $\dot x=-x^3$.

### 13. `implicitCubic_stable_explicitCubic_threshold`
**Rendering.** For $h\ge0$ and every $x_0$:
- (i) $|Y^n(x_0)|\le|x_0|$ for all $n$;
- (ii) the explicit orbit $E^n(x_0)$, with $E(S)=S-hS^3$, is bounded if and only if $hx_0^2\le2$;
- (iii) if $hx_0^2>2$ then $|E^n(x_0)|\to+\infty$.

**Assessment.** True. Put $u=hS^2$; then $u\mapsto u(1-u)^2$, which maps $[0,2]$ into $[0,2]$ (its maximum on $[0,2]$ is 2, at $u=2$). For $u>2$, $u_{n+1}/u_n=(u_n-1)^2\ge(u_0-1)^2>1$.

Numerically: the boundary $u=2$ gives the exact rational 2-cycle $1,-1,1,\dots$; $u_0=1.999$ stays bounded; $u_0=2.001$ exceeds $10^{30}$ at $n=9$ (`threshold.out`). At $h=0$ both sides of (ii) hold and (iii) is vacuous. This is the standard conditional stability threshold of explicit Euler for $\dot x=-x^3$.

### 14. `implicitPath_moments_le`
**Rendering.** Let $\mu$ be any measure on $\Omega$. Assume $a$ continuous, one-sided Lipschitz with constant $K$, dissipative ($ya(y)\le0$), $h\ge0$ and $hK<1$. Take $\sigma,x_0\in\mathbb R$, $N\in\mathbb N$, and $Z:\mathbb N\to\Omega\to\mathbb R$ with $\mathrm{law}(Z_n)=\mathcal N(0,1)$ for $n<N$ and $(Z_n)_{n<N}$ mutually independent (`iIndepFun` on `Fin N`). Let $X_N$ be the implicit path at step $N$. Then:
- $X_N\in L^4(\mu)$;
- $\int X_N^2\,d\mu\le x_0^2+\sigma^2Nh$;
- $\int X_N^4\,d\mu\le x_0^4+6x_0^2\sigma^2Nh+3\sigma^4(Nh)^2$, with $N$ cast to ℝ.

**Assessment.** True.
- **Probability measure.** `iIndepFun` forces $\mu(\Omega)=1$ (Mathlib `iIndepFun.isProbabilityMeasure`, applied to the empty index set; checked in `Scratch.lean` for `Fin 0`). So the $N=0$ case $\int x_0^2\,d\mu=x_0^2$ is fine and not a junk case.
- **Measurability.** $X_N$ is a continuous function (by 9) of the a.e.-measurable vector $(Z_0,\dots,Z_{N-1})$.
- **Integrability.** By 10, $|X_N|\le|x_0|+|\sigma|\sqrt h\sum_{k<N}|Z_k|$, so $X_N\in L^4$.
- **Moment recursion.** $X_n$ is independent of $Z_n$, and $EZ=EZ^3=0$, $EZ^2=1$, $EZ^4=3$. Hence $m_2'\le m_2+\sigma^2h$ and $m_4'\le m_4+6\sigma^2h\,m_2+3\sigma^4h^2$. Iterating gives exactly the right-hand sides (checked with sympy for $N\le7$); they are the moments of $x_0+\sigma W_{Nh}$.

Quadrature at $N=2$ (cubic drift, and $a=-y(y-1)^2$ with $K=1/3$) confirms the bounds (`moments.out`).

Not vacuous: take $\Omega=\mathbb R^{\mathbb N}$ with `Measure.infinitePi (fun _ => gaussianReal 0 1)`, coordinate maps as $Z_n$, and $a=-y^3$, $K=0$. The bound is uniform in $h$ through $Nh$. The hypothesis set is narrower than the standard result: global dissipativity excludes, for example, $a=y-y^3$. `hK` serves only uniqueness and measurability.

### 15. `implicitCubic_moments_le`
**Rendering.** For $x_0$, $T\ge0$, $N\in\mathbb N$, and $Z$ as above ($N(0,1)$ for $n<N$, independent on `Fin N`), take the implicit path with $a=-y^3$, $h=T/N$ ($T/0=0$) and $\sigma=1$. Then $X_N\in L^4$, $E X_N^2\le x_0^2+T$ and $E X_N^4\le x_0^4+6x_0^2T+3T^2$.

**Assessment.** True, as 14 with $K=0$ and $Nh=T$ (or $Nh=0\le T$ when $N=0$). The bound is uniform in $N$. Monte Carlo with $T=1$, $x_0=2$ and $N$ up to 256 gives $E X^2\approx0.55\le5$ (`moments.out`). The junk value $T/0=0$ at $N=0$ only gives the trivially true $x_0^2\le x_0^2+T$. Not vacuous. This is the uniform-in-step-size moment bound for drift-implicit Euler with cubic drift (Higham–Mao–Stuart / Mao–Szpruch type).

### 16. `implicit_vs_explicit_cubic_moments`
**Rendering.** Take $x_0$ and $T>0$, and a triangular array $Z_{N,n}$ such that for each $N$ the row $(Z_{N,n})_{n<N}$ is i.i.d. $\mathcal N(0,1)$; the dependence across rows is unrestricted. Then:
- (a) for all $N$, the bounds of 15 hold for the implicit path driven by row $N$;
- (b) $E[(X^{EM}_N)^2]\to+\infty$ as $N\to\infty$, where $X^{EM}$ is EM for $dX=-X^3dt+dW$ with $h=T/N$ driven by row $N$;
- (c) the same for $E[(X^{EM}_N)^4]$.

**Assessment.** True. (a) is 15. For (b), this is Hutzenthaler–Jentzen–Kloeden (2011), "Strong and weak divergence in finite time of Euler's method for SDEs with non-globally Lipschitz coefficients", which shows $E|X^{EM}_N|^p\to\infty$ for every $p\ge1$.

Own lower bound (`em_cubic.py`):
- Let $A_N=\{Z_0\ge z^*\}\cap\bigcap_{1\le k<N}\{|Z_k|\le h^{-1/2}\}$, with $z^*$ chosen so that $hX_1^2\ge8$.
- On $A_N$, $u_{k+1}\ge u_k^3/4$, so $X_N^2\ge 2\cdot4^{3^{N-1}}/h$. There were zero violations in 8000 random checks of this step.
- $P(A_N)\ge e^{-O(N^2)}$, so the bound tends to $\infty$; for $T=1$ it exceeds $10^{11676}$ at $N=10$.

$X^{EM}_N$ is a polynomial in Gaussians, so its integrals are finite: there is no non-integrable junk value of 0. The convergence is not monotone: for $T=1,x_0=0$ the exact values are $E X_N^2=1,0.719,0.549$ at $N=1,2,3$. (c) follows from (b) by Jensen ($\mu$ is a probability measure; it is also forced by `hZ` at $N=1$).

Not vacuous: set $Z_{N,n}=\xi_n$ for an i.i.d. sequence $\xi$. Modelling each $N$ by its own row is adequate, because only the law of each row enters.

### 17. `intFactorPath_second_moment_eq`
**Rendering.** For any $L,\sigma,x_0$, $h\ge0$, $N$, and $(Z_n)_{n<N}$ i.i.d. $\mathcal N(0,1)$:
$$E X_N^2=e^{-2LhN}x_0^2+e^{-2Lh}\sigma^2h\sum_{k<N}e^{-2Lhk}$$
for the integrating-factor scheme (written with `Real.exp (-2*L*h) ^ N`).

**Assessment.** True. The recursion is $m'=e^{-2Lh}(m+\sigma^2h)$, using independence and $EZ=0$. The closed form matches symbolically for $N\le6$, and Monte Carlo gives 0.19145 against 0.19131 (`linear.out`). $X_N$ is affine-Gaussian, so it is integrable. It holds for any sign of $L$. Not vacuous.

### 18. `intFactorPath_second_moment_le`
**Rendering.** For $L>0$ and $h\ge0$, under the same noise hypotheses: $X_N\in L^2$ and $E X_N^2\le\max(x_0^2,\sigma^2/(2L))$.

**Assessment.** True. $m_N=\rho^N x_0^2+(1-\rho^N)m^*$ with $\rho=e^{-2Lh}$ and $m^*=\sigma^2h\rho/(1-\rho)=\sigma^2h/(e^{2Lh}-1)\le\sigma^2/(2L)$, because $e^x-1\ge x$. A grid search found a maximum excess of exactly 0 (equality at $N=0$ or $h=0$; `linear.out`). The bound is uniform in $h$ with no step-size restriction. It is the discrete analogue of the stationary OU variance $\sigma^2/(2L)$. Not vacuous.

### 19. `emLinear_second_moment_eq`
**Rendering.** For any $L,\sigma,x_0$, $h\ge0$, and the same noise: EM for $dX=-LX\,dt+\sigma dW$ has
$$E X_N^2=((1-Lh)^2)^Nx_0^2+\sigma^2h\sum_{k<N}((1-Lh)^2)^k.$$

**Assessment.** True: $X'=(1-Lh)X+\sigma\sqrt hZ$ gives $m'=(1-Lh)^2m+\sigma^2h$. Checked symbolically (`linear.out`). Not vacuous, and no junk value. This is the standard mean-square recursion for EM on the OU process.

### 20. `emLinear_second_moment_tendsto_atTop`
**Rendering.** Assume $h>0$, $Lh>2$, $x_0\ne0$ or $\sigma\ne0$, and an infinite i.i.d. $\mathcal N(0,1)$ sequence $Z$ (`iIndepFun Z μ` on all of ℕ). Then $E X_N^2\to\infty$ for the EM path.

**Assessment.** True by 19. Here $q=(1-Lh)^2>1$, so $q^Nx_0^2\to\infty$ if $x_0\ne0$, and $\sigma^2h\sum_{k<N}q^k\ge\sigma^2hN\to\infty$ if $\sigma\ne0$. The `hne` hypothesis is necessary, since the zero path is the counterexample without it. The threshold is right; the strict "$>2$" is slightly weaker than possible, because at $Lh=2$ with $\sigma\ne0$ the second moment also diverges, linearly (`linear.out`: 5, 50, 200). This is the classical mean-square instability of EM for $Lh>2$. Not vacuous.
