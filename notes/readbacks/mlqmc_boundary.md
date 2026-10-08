# Blind read-back report — R9 (MLQMC boundary case)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round15/packet_R9_mlqmc_boundary.lean` |
| declarations audited | 7 (6 theorems + 1 appended definition `latticeRule`) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round15/work_R9/` (`upper.py`, `lower.py`, `lattice.py`, `exponents.py`, `exponents_slow.py`, each with `.out`; `Scratch.lean` / `Scratch.out` = elaboration check of a `sorry` copy) |

Elaboration was confirmed by compiling a scratch copy with `import MlmcLean` (`Scratch.out`):
every `x ^ 2` is a natural-number power, `(2:ℝ) ^ (…)`, `(-Real.log ε) ^ ((3:ℝ)/2)`, `ε ^ (-p)`,
`(-Real.log ε) ^ q`, `(|c₁|/ε) ^ (g/a)` are `Real.rpow`; `N ℓ : ℕ` is cast to `ℝ` in theorems 1, 2, 4, 6;
`example : latticeRule = myLatticeRule := rfl` (a verbatim copy of the appended definition) succeeds.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 0 | `latticeRule` | def | — | — | no (only $N=0$ gives $0^{-1}\cdot 0=0$; never used with $N=0$) |
| 1 | `mlqmc_boundary_complexity_core` | theorem | true | no | no |
| 2 | `mlqmc_boundary_complexity` | theorem | true | no (product-space instance exists) | no |
| 3 | `mlqmc_boundary_cost_lower` | theorem | true | no (for $a>0$); for $a\le 0$ partly vacuous (infeasible for $\varepsilon\le\|c_1\|$) | no |
| 4 | `mlqmc_boundary_exponents_optimal` | theorem | true | no (for $a>0$); trivially true for $a\le 0$ | no |
| 5 | `mlqmc_finest_level_cost_lower` | theorem | true | no | no |
| 6 | `mlqmc_finest_level_exponent_optimal` | theorem | true | no | no |

## Main points for a human auditor

- All six theorems are true as stated. None depends on a junk value: every division is by a
  positive quantity, and every `rpow` base is positive on the ranges that matter ($2$, $-\log\varepsilon>1$ for
  $\varepsilon<e^{-1}$, $-\log\varepsilon>0$ for $\varepsilon<1$, $|c_1|/\varepsilon\ge 0$ with exponent $g/a\ge0$). In theorem 2 the
  integrand is a.e. bounded and a.e.-measurable, so the Bochner integral is genuine (not the junk $0$).
- Quantifier order is right everywhere: $K$ (resp. $k$) comes before $\varepsilon$ and does not depend on $\varepsilon$, $L$ or $N$.
  Theorem 3 bounds **all** $L\in\mathbb N$ and **all real** allocations with $N_\ell>0$ for $\ell\le L$ (so it covers integer ones too).
  Theorems 4 and 6 refute every integer allocation (and arbitrary $L$) with $K$ of any sign and any $\varepsilon_0>0$.
- The upper bounds (1, 2) assume $g\le b$ (not $b=g$) and $g\le a$, $a>0$; the lower bounds (3, 4) assume $b\le g$. The
  two meet exactly in the boundary case $b=g\le a$, $a>0$, where the order $\varepsilon^{-1}|\log\varepsilon|^{3/2}$ is exact.
  For $b>g$ the upper bound is true but not sharp; for $b<g$ the lower bound is true but not sharp. Both are harmless generalisations.
- Theorems 3 and 4 put no hypothesis on $a$. For $a\le0$ the bias term $c_1^2 2^{-2aL}\ge c_1^2$, so the constraint MSE $\le\varepsilon^2$
  cannot be met once $\varepsilon\le|c_1|$. Theorem 3 is then vacuous for small $\varepsilon$ (it still holds for $\varepsilon\in(|c_1|,1)$ with a
  positive $k$). Theorem 4 is then trivially true. The content is real for $a>0$, which is the case of interest.
- Theorem 5 assumes $1\le N_L$ for a **real** allocation (not only $N_L>0$). This is a modelling assumption ("at least one sample on
  the finest level"). It is automatic for integer allocations, which are all that theorem 6 uses.
- Theorem 2: $c_1,c_2\ge0$ follow from `hbias`/`hV`; $c_3$ and the costs $C_\ell$ may be negative. That only makes the cost
  bound easier and is harmless. `hf` (bounded variation) rules out the `ENNReal.toReal ⊤ = 0` junk in `hV`. Only pairwise
  independence of the shifts is assumed, which is all the MSE decomposition needs.
- The ranges of $\varepsilon$ are needed: in theorems 1 and 2, $(-\log\varepsilon)^{3/2}\to0$ as $\varepsilon\to1$ while every admissible cost is
  $\gtrsim 1/\varepsilon$. So the upper bound could not hold up to $1$, and $\varepsilon<e^{-1}$ is a sensible cut-off (it makes $-\log\varepsilon>1$).
- Numerics (mpmath, $\varepsilon$ down to $10^{-30}$, and further in closed form):
  - Upper bound: the explicit Lagrange/Hölder integer allocation always gives MSE $<\varepsilon^2$, with cost$/(\varepsilon^{-1}|\log\varepsilon|^{3/2})$ bounded in
    11 parameter sets. For $a=b=g=c_i=1$ the ratio lies in $[2.51,13.4]$ and tends to $\sqrt2(\ln2)^{-3/2}\approx2.45$.
  - Lower bound: the exact real-allocation minimum over $N$ (Hölder closed form, checked against 11 800 random allocations with
    0 violations) and over $L$ gives a ratio bounded away from $0$ for $\varepsilon\in(0,1)$, including $\varepsilon\to1$. For $a=b=g=c_i=1$ the
    ratio tends to $(\ln 2)^{-3/2}\approx1.733$ (1.7384 at $\varepsilon=10^{-1000}$).
  - The divergence claimed by theorems 4 and 6 is confirmed, but it is very slow for $p=1$, $q$ close to $3/2$, and for $q<0$ close to $0$.

---

## 0. `latticeRule` (definition, from MlmcLean.QMC1D)

**Rendering.** For $f:\mathbb R\to\mathbb R$, $N\in\mathbb N$ and $u\in\mathbb R$,
$$\mathrm{latticeRule}(f,N,u)=\frac1N\sum_{i=0}^{N-1} f\!\left(\frac{i+u}{N}\right).$$
This is the one-dimensional rank-1 lattice (equal-weight rectangle) rule with the shift $u/N$. For $u\sim\mathrm{Unif}[0,1]$ it has the
same distribution as the usual randomly shifted lattice $\{i/N+\Delta\}\bmod 1$ with $\Delta\sim\mathrm{Unif}[0,1)$. For $N=0$ it is $0^{-1}\cdot0=0$
(junk), but every use below has $N_\ell>0$.

**Assessment.** The definition is standard. I checked numerically (`lattice.py`) that $\mathbb E_u[Q]=\int_0^1 f$ and
$\sup_u|Q(u)-\int_0^1 f|\le \mathrm{Var}(f;[0,1])/N$ for five BV functions (linear, a jump, $\sqrt y$, $\sin 6\pi y$, jump plus quadratic)
and $N\in\{1,\dots,21\}$. The worst ratio is $0.90\le1$.

## 1. `mlqmc_boundary_complexity_core`

**Rendering.** Let $a,b,g,c_1,c_2,c_3\in\mathbb R$ with $a>0$, $g\le a$, $g\le b$ and $c_1,c_2,c_3>0$. Then there is a $K>0$
(depending only on the parameters) such that for every $\varepsilon$ with $0<\varepsilon<e^{-1}$ there are $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with
$N_\ell\ge1$ for all $\ell$ such that
$$\big(c_1 2^{-aL}\big)^2+\sum_{\ell=0}^{L}\Big(\frac{c_2 2^{-b\ell}}{N_\ell}\Big)^2<\varepsilon^2
\quad\text{and}\quad \sum_{\ell=0}^{L} N_\ell\, c_3 2^{g\ell}\le K\,\varepsilon^{-1}(-\log\varepsilon)^{3/2}.$$
All powers of $2$ are real powers of the positive base $2$. $-\log\varepsilon>1$ on this range, so the `rpow` is of a positive number.

**Assessment.** *True.* Take $L$ minimal with $c_1 2^{-aL}<\varepsilon/\sqrt2$, so $L+1\lesssim 1+\log_2(c_1/\varepsilon)/a\lesssim|\log\varepsilon|$.
Put $V_\ell=c_2^2 2^{-2b\ell}$, $C_\ell=c_3 2^{g\ell}$ and $S=\sum_{\ell\le L}V_\ell^{1/3}C_\ell^{2/3}=(c_2c_3)^{2/3}\sum_{\ell\le L}2^{2(g-b)\ell/3}\le (c_2c_3)^{2/3}(L+1)$
(using $g\le b$). Take $N_\ell=\lceil \sqrt{2S}\,\varepsilon^{-1}(V_\ell/C_\ell)^{1/3}\rceil$. Then $\sum V_\ell/N_\ell^2\le\varepsilon^2/2$, so the MSE is $<\varepsilon^2$, and the
cost is at most $\sqrt2\,S^{3/2}/\varepsilon+\sum_{\ell\le L}C_\ell$. The first term is $O(\varepsilon^{-1}|\log\varepsilon|^{3/2})$. The rounding term is at most
$c_3(L+1)\max(1,2^{gL})=O(|\log\varepsilon|\,\varepsilon^{-g/a})=O(\varepsilon^{-1}|\log\varepsilon|)$, using $g\le a$ and $\varepsilon<1$. Near $\varepsilon=e^{-1}$ we have
$(-\log\varepsilon)^{3/2}\ge1$, so one $K$ works for the whole range.
Numerics (`upper.py`): over 11 parameter sets (including $b>g$, $b=g=0$, negative $b=g$, negative $g$, and extreme $c_i$), 404 values of
$\varepsilon\in(10^{-30},e^{-1})$ always give MSE $<\varepsilon^2$ and a bounded ratio. Example: for $a=b=g=c_i=1$ the ratio lies in $[2.51,13.39]$ and tends to $\sqrt2(\ln2)^{-3/2}\approx2.45$.
*Non-vacuous:* $a=b=g=c_1=c_2=c_3=1$. *Junk:* none ($N_\ell\ge1$, so there is no division by $0$; the rpow bases are positive).
*Hypotheses:* $c_i>0$ is more than needed ($c_i\ge0$ would do); $g\le b$ generalises the boundary case $b=g$; $g\le a$ and
$g\le b$ are necessary for the rate. *Standard result:* the MLQMC/MLMC complexity theorem in the boundary case $\beta=\gamma$ (with
QMC variance decay $N^{-2}$, Lagrange allocation $N_\ell\propto (V_\ell/C_\ell)^{1/3}$) giving cost $\varepsilon^{-1}|\log\varepsilon|^{3/2}$.

## 2. `mlqmc_boundary_complexity`

**Rendering.** Let $(\Omega,\mu)$ be a measurable space with a measure, and let $U_\ell:\Omega\to\mathbb R$ ($\ell\in\mathbb N$) be measure-preserving from $\mu$
to Lebesgue measure restricted to $[0,1]$. So each $U_\ell$ is measurable and $\sim\mathrm{Unif}[0,1]$, and $\mu$ is necessarily a probability
measure. Assume the $U_\ell$ are pairwise independent. Let $f_\ell:\mathbb R\to\mathbb R$ have bounded variation on $[0,1]$, $C:\mathbb N\to\mathbb R$, and
$I,a,b,g,c_1,c_2,c_3\in\mathbb R$ with $a>0$, $g\le a$, $g\le b$. Assume:
(bias) $\big|\sum_{\ell=0}^{L}\int_0^1 f_\ell-I\big|\le c_1 2^{-aL}$ for all $L$;
(variation) $\mathrm{Var}(f_\ell;[0,1])\le c_2 2^{-b\ell}$ for all $\ell$ (as `toReal` of `eVariationOn`, which is finite by `hf`);
(cost) $C_\ell\le c_3 2^{g\ell}$.
Then there is a $K>0$ such that for every $0<\varepsilon<e^{-1}$ there are $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$, all $N_\ell\ge1$, with
$$\int_\Omega\Big(\sum_{\ell=0}^{L}\mathrm{latticeRule}(f_\ell,N_\ell,U_\ell(\omega))-I\Big)^2\,d\mu(\omega)<\varepsilon^2,\qquad
\sum_{\ell=0}^{L}N_\ell C_\ell\le K\varepsilon^{-1}(-\log\varepsilon)^{3/2}.$$

**Assessment.** *True.* With $Q_\ell=\mathrm{latticeRule}(f_\ell,N_\ell,U_\ell)$, I check unbiasedness, the variance bound, the MSE
decomposition, and then reuse theorem 1:
- Unbiasedness: $\mathbb E Q_\ell=\int_0^1 f_\ell$, because the shifted points tile $[0,1]$.
- Variance: $|Q_\ell-\int f_\ell|\le N_\ell^{-1}\sum_i\mathrm{Var}(f_\ell;[i/N_\ell,(i+1)/N_\ell])=\mathrm{Var}(f_\ell;[0,1])/N_\ell$ surely (on
  $U_\ell\in[0,1]$), so $\mathrm{Var}(Q_\ell)\le(c_2 2^{-b\ell}/N_\ell)^2$.
- MSE decomposition: pairwise independence kills the cross terms, so MSE $=(\sum\int f_\ell-I)^2+\sum\mathrm{Var}(Q_\ell)$, which is at most
  the deterministic expression of theorem 1.
- Then apply theorem 1's construction with $\max(c_i,1)$ in place of $c_i$. Here $c_1,c_2\ge0$ are forced by the hypotheses, and
  $C_\ell\le c_3 2^{g\ell}\le \max(c_3,1)2^{g\ell}$.

*Junk check:* BV on $[0,1]$ implies bounded on $[0,1]$ and a.e.-measurable there (difference of monotone functions). Each $f_\ell\circ((i+\cdot)/N)$
composed with the measure-preserving $U_\ell$ is therefore a.e.-strongly measurable and a.e. bounded, so the integrand is integrable on the
probability space and the integral is not the junk $0$. `hf` excludes the `toReal ⊤ = 0` loophole in `hV`, and $\int_0^1 f_\ell$ is a genuine
integral. Values of $f_\ell$ outside $[0,1]$ only matter on a null set.

*Non-vacuous:* $\Omega=\mathbb R^{\mathbb N}$ with `Measure.infinitePi` of $\mathrm{Leb}|_{[0,1]}$ and $U_\ell$ the coordinates, $f_\ell(y)=2^{-\ell}y$, $I=1$,
$a=b=g=1$, $c_1=\tfrac12$, $c_2=1$, $C_\ell=2^\ell$, $c_3=1$. The bias is exactly $2^{-L-1}$ and the variation is $2^{-\ell}$; both were checked in `lattice.py`, which also checks
$\mathrm{Var}(Q_3)=2^{-6}/(12\cdot 49)\le(2^{-3}/7)^2$. This is genuinely the boundary case $b=g=a$. (Pairwise independence rules out a
single shared $U$, so a product space is needed, and Mathlib provides one.)

*Hypotheses:* no positivity is assumed on $c_3$ or $C_\ell$; negative costs only make the conclusion easier (harmless). Only
pairwise, not mutual, independence is assumed, which is the weaker and sufficient condition. *Standard result:* the randomised MLQMC
complexity theorem (randomly shifted lattice rules, Koksma–Hlawka-type bound $|Q-I|\le V(f)/N$ in 1D) in the boundary case.

## 3. `mlqmc_boundary_cost_lower`

**Rendering.** Let $a,b,g,c_1,c_2,c_3\in\mathbb R$ with $b\le g$, $c_1\ne0$, $c_2\ne0$, $c_3>0$ ($a$ is unrestricted). Then there is a $k>0$ such
that for every $0<\varepsilon<1$, every $L\in\mathbb N$ and every $N:\mathbb N\to\mathbb R$ with $N_\ell>0$ for $\ell\le L$:
if $(c_12^{-aL})^2+\sum_{\ell=0}^{L}(c_22^{-b\ell}/N_\ell)^2\le\varepsilon^2$, then
$$k\,\varepsilon^{-1}(-\log\varepsilon)^{3/2}\le\sum_{\ell=0}^{L}N_\ell\,c_32^{g\ell}.$$

**Assessment.** *True.* By Hölder with exponents $(3,\tfrac32)$:
$\sum_\ell V_\ell^{1/3}C_\ell^{2/3}=\sum_\ell (V_\ell/N_\ell^2)^{1/3}(N_\ell C_\ell)^{2/3}\le(\sum V_\ell/N_\ell^2)^{1/3}(\sum N_\ell C_\ell)^{2/3}$. Hence the cost is at least
$S_L^{3/2}/\varepsilon$, and $S_L=(c_2^2c_3^2)^{1/3}\sum_{\ell\le L}2^{2(g-b)\ell/3}\ge(c_2^2c_3^2)^{1/3}(L+1)$ because $b\le g$. So the cost is at least $|c_2|c_3(L+1)^{3/2}/\varepsilon$.
- If $a>0$: the bias constraint gives $L\ge\log_2(|c_1|/\varepsilon)/a$. For $\varepsilon\le\min(1,|c_1|)^2$ this gives $L+1\gtrsim-\log\varepsilon$. For larger $\varepsilon$,
  $-\log\varepsilon\le 2\log^+(1/|c_1|)$ is bounded and $L+1\ge1$ suffices. So a uniform $k$ exists.
- If $a\le0$: the constraint forces $\varepsilon\ge|c_1|$ (so $|c_1|<1$), $-\log\varepsilon\le-\log|c_1|$ is bounded, and $L+1\ge1$ suffices.
- As $\varepsilon\to1$ the left side tends to $0$, so there is no difficulty there.

Numerics (`lower.py`): the exact minimum over real $N$ ($S_L^{3/2}/\sqrt{\varepsilon^2-c_1^22^{-2aL}}$, validated by 11 800 random allocations with 0
violations), minimised over $L$, divided by $\varepsilon^{-1}|\log\varepsilon|^{3/2}$, has a positive infimum in all 13 parameter sets. These include $b<g$,
negative $c_1,c_2$, negative $b=g$, $g>a$, $a=0$ and $a<0$ (where the grid points with $\varepsilon\le|c_1|$ are infeasible). For $a=b=g=c_i=1$ the ratio tends to
$(\ln2)^{-3/2}\approx1.733$: 1.856 at $10^{-30}$, 1.7384 at $10^{-1000}$.
*Non-vacuous:* $a=b=g=c_i=1$; feasible $(L,N)$ exist for every $\varepsilon$ (theorem 1). *Junk:* none ($N_\ell>0$ on the summation range; the
rpow base is $-\log\varepsilon>0$). *Hypotheses:* there is no condition on $a$, which makes the theorem partly vacuous for $a\le0$, as explained above. This is harmless.
$c_1\ne0$ and $c_2\ne0$ are needed: with $c_1=0$, $L=0$ gives cost $\sim1/\varepsilon$ without the log factor. *Standard result:* the lower half of the
$\Theta(\varepsilon^{-1}|\log\varepsilon|^{3/2})$ complexity in the boundary case. The optimal allocation for fixed $L$ is the Lagrange/Hölder one.

## 4. `mlqmc_boundary_exponents_optimal`

**Rendering.** Let $b\le g$, $c_1\ne0$, $c_2\ne0$, $c_3>0$ ($a$ arbitrary), and let $p,q\in\mathbb R$ with $p<1$, or with $p=1$ and $q<3/2$.
Then there are **no** $K\in\mathbb R$ and $\varepsilon_0>0$ such that for every $0<\varepsilon<\varepsilon_0$ some $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N_{\ge1}$ satisfy
MSE $\le\varepsilon^2$ (same expression as in theorem 1, but with $\le$) and $\sum_{\ell\le L}N_\ell c_32^{g\ell}\le K\varepsilon^{-p}(-\log\varepsilon)^q$.

**Assessment.** *True.*
- For $a>0$: theorem 3 gives the cost bound $\ge k\varepsilon^{-1}(-\log\varepsilon)^{3/2}$ for every feasible $(L,N)$, and
  $K\varepsilon^{-p}(-\log\varepsilon)^q/(k\varepsilon^{-1}(-\log\varepsilon)^{3/2})=(K/k)\,\varepsilon^{1-p}(-\log\varepsilon)^{q-3/2}\to0$, which is a contradiction for small $\varepsilon$. This holds for any sign of $K$ and any
  $\varepsilon_0$. Values of $\varepsilon\ge1$, where $(-\log\varepsilon)^q$ would be a negative-base rpow, are never needed.
- For $a\le0$: no feasible $(L,N)$ exists once $\varepsilon\le|c_1|$, so the statement is trivially true.
- The threshold is sharp: for $(p,q)=(1,3/2)$, $b=g\le a$ and $a>0$, the existential does hold by theorem 1 (with $\varepsilon_0=e^{-1}$).

Numerics (`exponents.py`, `exponents_slow.py`): with $(p,q)=(-1,5)$ and $(0.99,10)$ the ratio blows up (the latter only for $\varepsilon\lesssim10^{-10^4}$), and with $(1,1.49)$
it grows like $|\log\varepsilon|^{0.01}$. With $(1,1.5)$ it stays bounded (about 1.75).
*Non-vacuous:* $a=b=g=c_i=1$, $p=1$, $q=1.4$. *Junk:* none. *Hypotheses:* no $a>0$ (trivial for $a\le0$). *Standard result:* optimality
of the exponents $(1,3/2)$ in the boundary-case complexity.

## 5. `mlqmc_finest_level_cost_lower`

**Rendering.** Let $a>0$, $g\ge0$, $c_3\ge0$ and $c_1\in\mathbb R$. For every $\varepsilon>0$ (no upper bound), every $L\in\mathbb N$ and every $N:\mathbb N\to\mathbb R$ with
$N_\ell\ge0$ for $\ell\le L$ and $N_L\ge1$: if $|c_1|2^{-aL}\le\varepsilon$, then
$c_3\,(|c_1|/\varepsilon)^{g/a}\le\sum_{\ell=0}^{L}N_\ell\,c_32^{g\ell}$.

**Assessment.** *True and elementary.* The sum is at least $N_Lc_32^{gL}\ge c_32^{gL}$ (the other terms are $\ge0$). Also $0\le|c_1|/\varepsilon\le2^{aL}$, and
$x\mapsto x^{g/a}$ is monotone on $[0,\infty)$ because $g/a\ge0$, so $(|c_1|/\varepsilon)^{g/a}\le2^{gL}$. Edge cases: if $c_1=0$ and $g=0$, the left side is
$c_3\cdot0^0=c_3$ (Lean's $0^0=1$). This makes the left side larger, not smaller, and the inequality still holds because the sum is at least $c_3N_L\ge c_3$. So the theorem does not depend on
that convention. A random check (`exponents.py`, 20 000 trials including $c_1=0$ and $g=0$) found 0 violations.
*Non-vacuous:* $a=g=c_1=c_3=\varepsilon=1$, $L=0$, $N\equiv1$. *Junk:* none ($\varepsilon>0$, the base is $\ge0$, the exponent is $\ge0$).
*Hypotheses:* $N_L\ge1$ (rather than $N_L>0$) for real allocations is an explicit modelling assumption. Without it a real allocation could
make $N_L$ tiny, and the bound would fail. It is automatic for integer allocations. *Standard result:* the finest-level lower bound
cost $\ge C_L\gtrsim\varepsilon^{-g/a}$ (one sample on level $L$, and the bias forces $L\ge\log_2(|c_1|/\varepsilon)/a$).

## 6. `mlqmc_finest_level_exponent_optimal`

**Rendering.** Let $a>0$, $c_1\ne0$, $c_3>0$ ($b,g,c_2$ arbitrary), and let $p,q$ satisfy $p<g/a$, or $p=g/a$ and $q<0$. Then there are no $K\in\mathbb R$
and $\varepsilon_0>0$ such that for every $0<\varepsilon<\varepsilon_0$ some $L$ and $N:\mathbb N\to\mathbb N_{\ge1}$ satisfy MSE $\le\varepsilon^2$ and
$\sum_{\ell\le L}N_\ell c_32^{g\ell}\le K\varepsilon^{-p}(-\log\varepsilon)^q$.

**Assessment.** *True.*
- If $g\ge0$: theorem 5 (with $N_L\ge1$, and the bias part of the MSE giving $|c_1|2^{-aL}\le\varepsilon$) gives cost $\ge c_3|c_1|^{g/a}\varepsilon^{-g/a}$, while
  $K\varepsilon^{-p}(-\log\varepsilon)^q=o(\varepsilon^{-g/a})$ under `hpq`.
- If $g<0$ (allowed, since there is no hypothesis on $g$): the cost is $\ge c_3N_0\ge c_3>0$, while $-p>-g/a>0$ (or $p=g/a<0$ with $q<0$) makes
  $K\varepsilon^{-p}(-\log\varepsilon)^q\to0$.
- Either way the existential fails for small $\varepsilon$, for any $K$ and $\varepsilon_0$.

Numerics (`exponents.py`, `exponents_slow.py`) confirm divergence for $g=2,-1,0$. For $(p,q)=(g/a,-0.1)$ the growth is $|\log\varepsilon|^{0.1}$ (10.9 at $\varepsilon=10^{-10^{10}}$).
*Non-vacuous:* $a=1$, $g=2$, $c_1=c_3=1$, $p=1.9$, $q=0$. For any $a>0$ feasible allocations exist for every $\varepsilon$ (take $L$ large and $N$ large), so the
negation is not trivial. *Junk:* none (the rpow of $-\log\varepsilon\le0$ for $\varepsilon\ge1$ is never needed). *Remark:* in the boundary case $b=g\le a$ this is
weaker than theorem 4 (since $g/a\le1$). Its role is to show that $g\le a$ cannot be dropped from theorems 1 and 2. It is sharp when $g>a$ and
$b\ge g$ (cost $\asymp\varepsilon^{-g/a}$). *Standard result:* the finest-level (bias-driven) cost lower bound $\varepsilon^{-\gamma/\alpha}$ in MLMC/MLQMC complexity theorems.
