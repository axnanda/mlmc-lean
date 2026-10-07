# Blind read-back report: R22 (jumps, exponential Lévy Asian payoffs, jump-adapted grids, thinning)

| Field | Value |
|---|---|
| Date | 2026-10-07 |
| Packet | `readback/round19/packet_R22_jumps.lean` |
| Declarations audited | 36: 14 theorems, 16 definitions in the packet body and 6 appended definitions (the empty `section Moments` contains no declaration) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round19/work_R22/`: `asian_exact.py/.out`, `asian_bound_sweep.py/.out`, `defs_check.py/.out`, `jumpdiff_check.py/.out`, `grid_law_check.py/.out`, `thinning_check.py/.out`, Lean scratch files `packet_copy.lean/.out` (whole packet re-elaborated with `sorry` proofs in a private namespace), `t0.lean/.out`, `t1.lean/.out` |

Sources consulted: the packet and Mathlib sources only (`Measure.infinitePi`, `poissonMeasure`, `gaussianReal`,
`Measure.conv`, `variance`/`evariance`, `HasLaw`, `IndepFun`/`iIndepFun`, `iIndepFun.isProbabilityMeasure`,
`Finset.sort`/`orderEmbOfFin`, `Tuple.sort`, `Measure.map_of_not_aemeasurable`).

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `levyAsianTrap` | def | n/a | n/a | no ($N=0$ gives $0/0=0$, but no theorem uses $N=0$) |
| 2 | `levyTrapPair` | def | n/a | n/a | no |
| 3 | `levyPairDiffSum` | def | n/a | n/a | no |
| 4 | `levyAsianConst` | def | n/a | n/a | no ($T=0$ gives $K/0=0$; every use has $T=2nh>0$) |
| 5 | `levy_asian_avg_sq_le` | theorem | **true** (exact check: worst ratio of exact value to bound is $1/2$) | no | no |
| 6 | `levy_asian_payoff_sq_le` | theorem | **true** | no | no |
| 7 | `levy_asian_theorem1` | theorem | **true** | no | no (the MSE integrand is $L^2$, so the integral is not the junk 0) |
| 8 | `jumpDiffLaw` | def | n/a | n/a | no (always a probability measure; `toNNReal` clips only when $h<0$ or $\lambda<0$) |
| 9 | `jumpDiffLaw_conv` | theorem | **true** (`hlam` is not needed) | no | no |
| 10 | `jumpDiffusion_asian_theorem1` | theorem | **true** (`hlam` is not needed) | no | no |
| 11 | `unionGridBM_map_eq_nat` | theorem | **true** | no | no |
| 12 | `jumpGrid` | def | n/a | n/a | no |
| 13 | `gridSeq` | def | n/a | n/a | no (it clamps at the last point by design) |
| 14 | `gridIdx` | def | n/a | n/a | no (`idxOf` returns the length if the point is missing; that cannot happen in the theorem because $C\subseteq F$) |
| 15 | `jumpAdapted_coarse_map_eq` | theorem | **true** | no | no |
| 16 | `jumpAdapted_map_eq` | theorem | **true** | no | no (both maps are of AE-measurable functions) |
| 17 | `jumpAdapted_2_4` | theorem | **true** | no | no (the integrability ↔ is stated) |
| 18 | `jaTimes` | def | n/a | n/a | no (the ℕ subtraction is exact on its branch) |
| 19 | `jaGrid` | def | n/a | n/a | no |
| 20 | `jaCoarseIdx` | def | n/a | n/a | no |
| 21 | `jaPos` | def | n/a | n/a | no |
| 22 | `jaCoarseInc` | def | n/a | n/a | no |
| 23 | `jaOwnInc` | def | n/a | n/a | no (the √ argument is ≥ 0 because the grid is sorted) |
| 24 | `jumpAdapted_random_map_eq` | theorem | **true** | no | no |
| 25 | `jumpAdapted_random_2_4` | theorem | **true** | no | no |
| 26 | `thinLaw` | def | n/a | n/a | no |
| 27 | `thinLR` | def | n/a | n/a | no division by 0 under `hq` |
| 28 | `thinning_lr_unbiased` | theorem | **true** (purely algebraic) | no | no |
| 29 | `thinLaw_isProb` | theorem | **true** | no | no |
| 30 | `thinning_mlmc_correction` | theorem | **true** | no | no |
| 31 | `blockMean` (appended) | def | n/a | n/a | no ($N=0$ gives 0, but every theorem forces $N_\ell>0$) |
| 32 | `fineCoarseDiff` (appended) | def | n/a | n/a | no |
| 33 | `stdNormalSeq` (appended) | def | n/a | n/a | no |
| 34 | `levyPairSum` (appended) | def | n/a | n/a | no |
| 35 | `levyPath` (appended) | def | n/a | n/a | no |
| 36 | `unionGridBM` (appended) | def | n/a | n/a | no (with a monotone grid every √ argument is ≥ 0) |

No statement is false, vacuous or dependent on a junk value. The points below are about scope and hypotheses.

## Main points for a human auditor

1. **The $h^2$ bound and its constant are correct (#5, #6).** I derived and checked an exact closed form for
   $\mathbb E[(A^f-A^c)^2]$. It depends on the increment law only through $m_1=\mathbb E e^{Y}=e^{h\kappa_1}$ and
   $m_2=\mathbb E e^{2Y}=e^{h\kappa_2}$. Checks:
   - symbolic expansion from the definitions (sympy, $n\le4$);
   - direct enumeration for finite-support laws ($n\le5$);
   - Gauss–Hermite quadrature and 2-D quadrature for Gaussian increments;
   - direct lattice sums for compound Poisson with random jump sizes;
   - Poisson sums × quadrature for `jumpDiffLaw`.

   Over the feasible parameter region ($\kappa_2\ge2\kappa_1$), the supremum of exact/bound is $1/2$. It is approached as
   $T(|\kappa_1|+|\kappa_2|)\to0$ with $\kappa_2=0$ and $\kappa_1<0$; 15 792 grid points and 20 000 random points never
   exceed it. The $h^2$ rate is sharp: exact$/h^2\to \frac{s_0^2}{T^2}\frac{(\kappa_2-2\kappa_1)(e^{\kappa_2T}-1)}{4\kappa_2}$.
   An analytic bound $s_0^2h^2e^{3TK}\big(\frac{K}{2T}+\frac{K^2}{4}+\frac{T^2K^4}{64}\big)$, with $K=|\kappa_1|+|\kappa_2|$,
   also proves the stated constant.
2. **What the "Theorem 1" statements target (#7, #10).** $P$ is existential but pinned down as the (unique) limit of
   $\mathbb E\,g(\text{trapezoidal average with }2^\ell\text{ steps})$. Nothing in the statements identifies $P$ with
   the continuous-time Asian price $\mathbb E\,g\big(\tfrac{s_0}{T}\int_0^Te^{X_t}dt\big)$, and no continuous-time
   process appears in them. This is enough for MLMC to be meaningful, and the identification holds mathematically, but
   the Lean statement does not assert it. Clause (i) follows from clause (ii).
3. **The MSE clause has no integrability conjunct (#7, #10).** If the integrand were not integrable, the clause would
   hold trivially (the integral would be 0). Here it is a real statement: the integrand is in $L^2$ because `hexp` (and
   the Gaussian/Poisson exponential moments in #10) together with the Lipschitz property of $g$ give it.
4. **`jumpDiffLaw` uses a fixed jump size $a$.** It is the law of $bh+\sigma W_h+aN_h$ with $N_h\sim$ Poisson: fixed-size
   Poisson jumps, not Merton/Kou random jump sizes. General Lévy laws are covered only through the abstract #7 (via
   `hconv` and `hexp`). `hlam : 0 ≤ lam` is superfluous in #9 and #10: for $\lambda<0$, `toNNReal` turns the jumps off
   and the statements remain true. `hh₁`/`hh₂` in #9 are needed (counterexample $h_1=-1,h_2=2$).
5. **Random jump-time statements (#16, #17, #24, #25).**
   - Measurability assumptions: $R$ is measurable; $\mathrm{law}(Z)=$`stdNormalSeq`, which forces $Z$ to be
     AE-measurable and $\mu$ to be a probability measure; $u,\tau$ (or $M,S$) are measurable. Together these make every
     `Measure.map` here a map of an AE-measurable function, so the equalities are not junk $0=0$.
   - Independence assumption: $R$ is independent of the whole Gaussian sequence $Z$, which is the natural one.
   - No assumption on the jump times is needed: they need not be in $[0,T]$, distinct, sorted or off the grid, and the
     step $h$ may be any real number.
   - The conclusions are joint laws with $R$, which is exactly what MLMC telescoping needs.
   - Exact rational covariance checks of the underlying Gaussian identities passed in 11 000 random configurations,
     including ties, duplicates, $h\le0$ and $n=0$.
6. **Thinning (#28–#30).** `thinning_lr_unbiased` is a purely algebraic identity. It needs no positivity, no
   $p\in[0,1]$ and no adaptedness of $p$ or $q$; only `hq` ($q\notin\{0,1\}$ everywhere) is used, and that is sufficient
   rather than necessary. Without some such condition it fails (example: $q\equiv0$). Reading it as
   $\mathbb E_Q[F\cdot dP/dQ]=\mathbb E_P[F]$ also needs `thinLaw_isProb`, for which adaptedness `had` is necessary
   (counterexample: total mass $3/5$) and `hp` is needed only for nonnegativity.
7. **#5 and #6 are slightly more general than "i.i.d. increments".** They need only independence plus equal
   $\mathbb E e^{Y_i}$ and $\mathbb E e^{2Y_i}$. `iIndepFun` already forces $\mu$ to be a probability measure (Mathlib
   `iIndepFun.isProbabilityMeasure`). The positive right-hand sides of `h1`/`h2` force $e^{Y_i}$ and $e^{2Y_i}$ to be
   integrable, so they are not junk.

---

## Per-declaration sections

Notation: $X_k=\sum_{i<k}y_i$ (`levyPath`); $\mathrm{Trap}_N(s_0,y)=\frac1N\sum_{k<N}\frac{s_0e^{X_k}+s_0e^{X_{k+1}}}{2}$;
$y^{(2)}_k=y_{2k}+y_{2k+1}$ (`levyPairSum`). For a random sequence $Y$ I write $A^f=\mathrm{Trap}_{2n}(s_0,Y)$ and
$A^c=\mathrm{Trap}_{n}(s_0,Y^{(2)})$. Note that $A^c$ uses the coarse path $X^c_j=X_{2j}$.

### 1. `levyAsianTrap` (def)
**Rendering.** For $s_0\in\mathbb R$, $N\in\mathbb N$ and $y:\mathbb N\to\mathbb R$:
$\mathrm{levyAsianTrap}(s_0,N,y)=\big(\sum_{k=0}^{N-1}(s_0e^{X_k}+s_0e^{X_{k+1}})/2\big)/N$, with $N$ cast to ℝ.
This is the trapezoidal rule with $N$ equal steps for the time average $\frac1T\int_0^Ts_0e^{X_t}\,dt$ (an arithmetic
Asian average; $T$ cancels). For $N=0$ the value is $0$ (empty sum, then $/0$), but no theorem uses $N=0$.

### 2. `levyTrapPair` (def)
**Rendering.** $\mathrm{levyTrapPair}(a,b)=e^a-\frac{1+e^{a+b}}2$. This is the fine-minus-coarse trapezoid error over one
coarse step, in units of $e^{X_{2j}}$.

### 3. `levyPairDiffSum` (def)
**Rendering.** $\mathrm{levyPairDiffSum}(y,n)=\sum_{j<n}e^{X_{2j}}\,\mathrm{levyTrapPair}(y_{2j},y_{2j+1})$.
I checked symbolically, for $n\le6$, that
$\mathrm{Trap}_{2n}(s_0,y)-\mathrm{Trap}_n(s_0,y^{(2)})=\frac{s_0}{2n}\,\mathrm{levyPairDiffSum}(y,n)$
(`defs_check.out`). Neither this definition nor #2 appears in a theorem statement.

### 4. `levyAsianConst` (def)
**Rendering.** With $K=|\kappa_1|+|\kappa_2|$:
$\mathrm{levyAsianConst}(\kappa_1,\kappa_2,T)=e^{6TK}\big(K/T+K^2+T^2K^4\big)$. At $T=0$, $K/T=0$ by the Lean convention;
this is never used because $T=2nh>0$ wherever the constant appears.

### 5. `levy_asian_avg_sq_le` (theorem)
**Rendering.** Let $(\Omega,\mu)$ be a measure space (no instance assumed) and $Y_i:\Omega\to\mathbb R$ measurable and
mutually independent (`iIndepFun`, which implies that $\mu$ is a probability measure). Let $h>0$ and
$\kappa_1,\kappa_2,T\in\mathbb R$, and suppose $\int e^{Y_i}d\mu=e^{h\kappa_1}$ and $\int e^{2Y_i}d\mu=e^{h\kappa_2}$ for
all $i$. Let $s_0\in\mathbb R$ and $n\in\mathbb N$ with $n>0$ and $2nh=T$ (computed in ℝ as `2 * ↑n * h`). Then
$(A^f-A^c)^2$ is integrable and
$$\int (A^f-A^c)^2\,d\mu\;\le\; s_0^2\,\mathrm{levyAsianConst}(\kappa_1,\kappa_2,T)\,h^2 .$$
The constant depends only on $\kappa_1,\kappa_2,T$, so the bound is uniform in $n$ for fixed $T$.

**Assessment.** *True.*

*Exact formula.* Write $A^f-A^c=\frac{s_0}{2n}\sum_{j<n}e^{X_{2j}}D_j$ with
$D_j=e^{Y_{2j}}-\frac{1+e^{Y_{2j}+Y_{2j+1}}}2$. Independence gives
$$\mathbb E(A^f-A^c)^2=\frac{s_0^2}{4n^2}\Big(\mathbb E D^2\sum_{j<n}m_2^{2j}+2c_0c_1\!\!\sum_{0\le j<k<n}\!\! m_2^{2j}m_1^{2(k-j-1)}\Big),$$
where $\mathbb ED^2=m_2+\frac14+\frac{m_2^2}4-m_1-m_1m_2+\frac{m_1^2}2$, $c_0=\mathbb ED=-\frac{(m_1-1)^2}2$ and
$c_1=\mathbb E[De^{Y+Y'}]=-\frac{(m_1-m_2)^2}2$. Every monomial has exponent at most 2 in each $e^{Y_i}$, so only $m_1$
and $m_2$ enter. Hence identically distributed increments are not needed.

*Verification.*
- Symbolic expansion from the definitions agrees for $n=1..4$ (`asian_exact.out` §2).
- Direct enumeration over 2- and 3-point laws agrees for $n\le5$, to $10^{-30}$ (or to float-input rounding $10^{-17}$).
- Gauss–Hermite quadrature for Gaussian increments ($n=1,2$) and a 2-D tanh-sinh quadrature agree.
- Compound Poisson with random ±jump sizes, by direct lattice sums ($n=1,2$), agrees.
- `jumpDiffLaw` increments (Poisson double sum × Gauss–Hermite, $n=1$) agree to about $10^{-11}$, which is the
  truncation error.

*Constant.* Put $x_i=T\kappa_i$; the ratio of exact to bound then depends only on $(x_1,x_2,n)$. The sweep
(`asian_bound_sweep.out`) covers 15 792 feasible grid points with $|x_i|\in[10^{-6},100]$ and $n$ up to $2^{20}$, plus
20 000 random points. The maximum ratio is $0.4999965$, with supremum $1/2$ attained as $X=|x_1|+|x_2|\to0$ with
$x_2=0$ and $x_1<0$. Analytically, using $|e^x-1|\le|x|e^{|x|}$, $\mathbb ED^2\le w+w^2$ with $w=\frac{|v|}2+|u|\le hKe^{hK}$,
$0\le c_0c_1\le h^4K^4e^{4hK}/4$, $\sum_j m_2^{2j}\le ne^{TK}$, the double sum $\le\frac{n^2}{2}e^{TK}$, and $h\le T/2$:
$$\mathbb E(A^f-A^c)^2\le s_0^2h^2e^{3TK}\Big(\frac K{2T}+\frac{K^2}4+\frac{T^2K^4}{64}\Big)\le s_0^2\,\mathrm{levyAsianConst}\,h^2 .$$
*Rate.* For fixed $T$, exact$/h^2$ converges to $\frac{s_0^2}{T^2}\frac{(\kappa_2-2\kappa_1)(e^{\kappa_2T}-1)}{4\kappa_2}>0$
(confirmed in the sweep, e.g. $0.0104109$ for $b=0,\sigma=0.2,T=1$), so $h^2$ is the exact order. The cross terms are
$O(h^4)$.

*Vacuity.* Not vacuous. Example: $\Omega=\mathbb R^{\mathbb N}$ with $\mu$ the infinite product of $\mathcal N(0,h)$,
$Y_i$ the coordinates, $\kappa_1=\frac12$, $\kappa_2=2$, $h=\frac12$, $n=1$, $T=1$. The hypotheses are satisfiable
exactly when $\kappa_2\ge2\kappa_1$ (Jensen; Gaussians realise every such pair).

*Junk values.* None. `h1`/`h2` have positive right-hand sides, which forces integrability. The probability measure
comes from `iIndepFun`. $T>0$. The integrability conjunct makes the integral genuine.

*Hypotheses.* Weaker than i.i.d. (see above), which is fine.

*Standard fact.* This is the strong $L^2$ order-1 convergence (level variance $O(h^2)$, $\beta=2$) of the trapezoidal
Asian average under exponential Lévy models with the pairwise-summed coarse path. I recall this from the MLMC literature
for exponential Lévy models (Giles–Xia); this is from memory, not from the repository's papers.

### 6. `levy_asian_payoff_sq_le` (theorem)
**Rendering.** Same hypotheses as #5, plus $g:\mathbb R\to\mathbb R$ with $|g(x)-g(y)|\le K|x-y|$ for all $x,y$. Then
$g(A^f)-g(A^c)\in L^2(\mu)$, $\int (g(A^f)-g(A^c))^2d\mu\le K^2s_0^2\,\mathrm{levyAsianConst}\,h^2$, and
$\mathrm{Var}_\mu(g(A^f)-g(A^c))\le K^2s_0^2\,\mathrm{levyAsianConst}\,h^2$.

**Assessment.** *True.* $g$ is continuous, hence measurable. $(g(A^f)-g(A^c))^2\le K^2(A^f-A^c)^2$ when $K\ge0$; if
$K<0$ the hypothesis `hg` is contradictory. Then use #5. Mathlib's `variance` is
$(\int^-\|X-\mathbb EX\|^2)^{\rm toReal}$, which for an $L^2$ variable on a probability space is
$\mathbb EX^2-(\mathbb EX)^2\le\mathbb EX^2$.
*Vacuity:* no (#5's instance with $g=\mathrm{id}$, $K=1$). *Junk:* none; MemLp is stated, so the variance and the
integral are genuine. *Standard fact:* the Lipschitz-payoff level-variance bound $V_\ell=O(h_\ell^2)$.

### 7. `levy_asian_theorem1` (theorem)
**Rendering.** Hypotheses:
- $\nu:\mathbb N\to$ probability measures on ℝ, with $\nu_{\ell+1}*\nu_{\ell+1}=\nu_\ell$ for every $\ell$, so
  $\nu_0=\nu_\ell^{*2^\ell}$ and $\nu_\ell$ is the increment law over $2^{-\ell}$ of the horizon;
- $e^{2x}\in L^1(\nu_0)$;
- $g$ is $K$-Lipschitz, and $s_0\in\mathbb R$.

Let $E_\ell=\int g(\mathrm{Trap}_{2^\ell}(s_0,y))\,d\nu_\ell^{\otimes\mathbb N}(y)$. Then there exists $P\in\mathbb R$ with:
1. $E_\ell\to P$;
2. $\exists c\ \forall\ell:\ |E_\ell-P|\le c/2^\ell$;
3. $\exists c_4>0\ \forall\varepsilon\in(0,e^{-1})\ \exists L\in\mathbb N,\ N:\mathbb N\to\mathbb N_{>0}$ such that the
   MLMC estimator $\hat Y=\sum_{\ell=0}^L\frac1{N_\ell}\sum_{k<N_\ell}\Delta_\ell(x_{\ell,k})$ satisfies
   $\mathbb E(\hat Y-P)^2<\varepsilon^2$ and $\sum_{\ell\le L}N_\ell2^\ell\le c_4\varepsilon^{-2}$.

Here the samples $x_{\ell,k}$ are i.i.d. over $(\ell,k)\in\mathbb N^2$. Each is a multilevel path $w$ with
$w_\ell\sim\nu_\ell^{\otimes\mathbb N}$, independent across $\ell$. The level terms are
$\Delta_0(w)=g(\mathrm{Trap}_1(s_0,w_0))$ and
$\Delta_{\ell+1}(w)=g(\mathrm{Trap}_{2^{\ell+1}}(s_0,w_{\ell+1}))-g(\mathrm{Trap}_{2^\ell}(s_0,w^{(2)}_{\ell+1}))$, so
fine and coarse are coupled through the same increments. $c_4$ may depend on $\nu,g,K,s_0$ but not on $\varepsilon$; $L$
and $N$ depend on $\varepsilon$.

**Assessment.** *True.* Set $\kappa_1=\log\int e^xd\nu_0$ and $\kappa_2=\log\int e^{2x}d\nu_0$; both are finite by
`hexp`. Tonelli on $\nu_0=\nu_\ell^{*2^\ell}$ gives $\int e^{tx}d\nu_\ell=e^{2^{-\ell}\kappa_t}$ for $t=1,2$. Put
$C=K^2s_0^2\,\mathrm{levyAsianConst}(\kappa_1,\kappa_2,1)$. Then #6 with $T=1$ and $h=2^{-\ell-1}$ gives
$\mathbb E\Delta_{\ell+1}^2\le C\,4^{-\ell-1}$, uniformly in $\ell$. The coarse term has law $\nu_\ell$ by `hconv`, so
$|E_{\ell+1}-E_\ell|\le\sqrt C\,2^{-\ell-1}$. The sequence is therefore Cauchy, and (i) and (ii) follow with
$c=\sqrt C$. Clause (iii) is Giles' MLMC complexity theorem with $\alpha=1$, $\beta=2>\gamma=1$, which gives
$O(\varepsilon^{-2})$. Rounding $N_\ell$ up adds $O(2^L)=O(\varepsilon^{-1})$ to the cost, and the strict "<" is reached
by aiming slightly lower.

*What is targeted.* $P$ is the unique limit of the expected discretised payoffs. The statement says nothing about a
continuous-time process or $\mathbb E\,g(\frac{s_0}{T}\int e^{X_t}dt)$. The identification does hold mathematically:
`hconv` and the exponential moments yield a Lévy process with these dyadic marginals, and the trapezoidal sums converge
a.s. and in $L^2$. It is just not part of the statement. Clause (i) is implied by (ii).

*Junk.* The MSE integral carries no integrability conjunct, but the integrand is in $L^2$ because
$|g(A)|\le|g(0)|+K|A|$ and $\mathbb Ee^{2X_k}<\infty$, so the clause is a real statement. `infinitePi` is not the junk 0
because every $\nu_\ell$ is a probability measure (assumed). `blockMean` never divides by 0 because $N_\ell>0$.
$\varepsilon^{(-2:\mathbb R)}=\varepsilon^{-2}$ because $\varepsilon>0$.

*Vacuity:* no (e.g. $\nu_\ell=\mathcal N(0,2^{-\ell})$, $g=\mathrm{id}$).

*Hypotheses:* natural. The family need not come with an explicit Lévy process.

*Standard result:* the MLMC complexity theorem (Giles 2008, Thm 3.1) instantiated for Asian options under exponential
Lévy models.

### 8. `jumpDiffLaw` (def)
**Rendering.** $\mathrm{jumpDiffLaw}(b,\sigma,a,\lambda,h)=\mathcal N\big(bh,(\sigma^2h)^+\big)*\mathrm{Law}(a\,N)$ with
$N\sim\mathrm{Poisson}((\lambda h)^+)$, where $(\cdot)^+$ is `toNNReal`. This is the increment law of
$X_t=bt+\sigma W_t+aN_t$ with **fixed** jump size $a$. Variance $0$ gives the Dirac mass, and rate $0$ gives
$\delta_0$ (since $0^0=1$).

It is always a probability measure; Lean found the instance once the map lemma was supplied (`t1.out`). For
$h,\lambda\ge0$, $\int e^{ty}=\exp\big(tbh+\tfrac{t^2\sigma^2h}2+\lambda h(e^{ta}-1)\big)$, so
$\kappa_1=b+\frac{\sigma^2}2+\lambda(e^a-1)$ and $\kappa_2=2b+2\sigma^2+\lambda(e^{2a}-1)$ (checked numerically in
`jumpdiff_check.out`).

### 9. `jumpDiffLaw_conv` (theorem)
**Rendering.** For all $b,\sigma,a$, $\lambda\ge0$ and $h_1,h_2\ge0$:
$\mathrm{jumpDiffLaw}(h_1)*\mathrm{jumpDiffLaw}(h_2)=\mathrm{jumpDiffLaw}(h_1+h_2)$.

**Assessment.** *True.* Gaussian convolution (Mathlib `gaussianReal_conv_gaussianReal`), Poisson convolution
(`poissonMeasure_conv_poissonMeasure`), $n\mapsto an$ being additive, and commutativity and associativity of $*$. The
characteristic-function identity holds to $10^{-30}$ in 300 random cases.

*Hypotheses:* `hlam` is **not needed**: for $\lambda<0$ the rates clip to 0 and the identity still holds (checked). `hh₁`
and `hh₂` are needed: for $h_1=-1,h_2=2$ the identity fails (cf-difference 0.33).
*Vacuity:* no. *Junk:* none.
*Standard fact:* $(\mu_h)_{h\ge0}$ is a convolution semigroup (Lévy process marginals).

### 10. `jumpDiffusion_asian_theorem1` (theorem)
**Rendering.** For all $b,\sigma,a$, $\lambda\ge0$, $T\ge0$, $K$-Lipschitz $g$ and $s_0$: the same three conclusions as
#7, with $\nu_\ell=\mathrm{jumpDiffLaw}(b,\sigma,a,\lambda,T/2^\ell)$.

**Assessment.** *True.* It is a corollary of #7. `hconv` comes from #9 with $h_1=h_2=T/2^{\ell+1}\ge0$, `hexp` from the
Gaussian and Poisson exponential moments, and each $\nu_\ell$ is a probability measure. When $T=0$ every law is
$\delta_0$, so $P=g(s_0)$ and the MSE is 0.

*Target:* the same as #7. $P$ is the limit of the discretised expectations; mathematically it equals the Asian price
under $bt+\sigma W_t+aN_t$, but the statement does not say so.
*Hypotheses:* `hlam` is superfluous (for $\lambda<0$ the model is purely Gaussian and the result still holds). The model
has deterministic jump sizes.
*Vacuity:* no. *Junk:* none (as in #7).

### 11. `unionGridBM_map_eq_nat` (theorem)
**Rendering.** For monotone $u:\mathbb N\to\mathbb R$ and monotone $\tau:\mathbb N\to\mathbb N$, let
$B_u(z,k)=\sum_{i<k}\sqrt{u_{i+1}-u_i}\,z_i$. Under `stdNormalSeq` (i.i.d. $\mathcal N(0,1)$), the law of
$\big(B_u(z,\tau_{j+1})-B_u(z,\tau_j)\big)_{j\in\mathbb N}$ equals the law of
$\big(\sqrt{u_{\tau_{j+1}}-u_{\tau_j}}\,z_j\big)_j$.

**Assessment.** *True.* The blocks $[\tau_j,\tau_{j+1})$ are disjoint, and the variances telescope to
$u_{\tau_{j+1}}-u_{\tau_j}$. Both sides are centred Gaussian product laws with the same covariance. Exact covariance
check: 3000 random cases with 0 mismatches.
*Hypotheses:* both monotonicity assumptions are needed. Without monotone $\tau$ the blocks overlap or reverse and
$\sqrt{\text{neg}}=0$ appears.
*Vacuity:* no. *Junk:* none; all √ arguments are ≥ 0.
*Standard fact:* Brownian increments over a sub-grid are independent $\mathcal N(0,\Delta t)$.

### 12. `jumpGrid` (def)
**Rendering.** $\{kh:0\le k\le N\}\cup J$ as a `Finset ℝ`, so duplicates are merged.

### 13. `gridSeq` (def)
**Rendering.** The $\min(i,K)$-th smallest element (0-based) of $F$, where $|F|=K+1$. Indices past the end are clamped to
$\max F$, so later increments are 0.

### 14. `gridIdx` (def)
**Rendering.** The position in `F.sort (· ≤ ·)` of the $c$-th smallest element of $C$. `List.idxOf` returns the length if
the element is absent; that never happens in #15.

### 15. `jumpAdapted_coarse_map_eq` (theorem)
**Rendering.** Let $Z_i$ be i.i.d. $\mathcal N(0,1)$ (`iIndepFun` plus `HasLaw`), $h\in\mathbb R$, $n\in\mathbb N$,
$J$ a finite set of reals, $C=\mathrm{jumpGrid}(2h,n,J)$ with $|C|=K_c+1$, and $F=\mathrm{jumpGrid}(h,2n,J)$ with
$|F|=K_f+1$. Then the law of the vector $\big(B_F(\mathrm{idx}(c_{j+1}))-B_F(\mathrm{idx}(c_j))\big)_{j<K_c}$ equals the
law of $\big(\sqrt{c_{j+1}-c_j}\,Z_j\big)_{j<K_c}$. Here $B_F$ is the Brownian path on the sorted fine grid built from $Z$,
and $c_j$ are the sorted coarse points.

**Assessment.** *True.* $C\subseteq F$ because $k(2h)=(2k)h$ exactly in ℝ, for any sign of $h$. The equality
`gridSeq` ∘ `gridIdx` $=c_j$ then gives disjoint blocks whose variances telescope. Exact check: 4000 random cases with
$h\in\{1/3,-1/2,0,2/5\}$, $n\le4$ and colliding or out-of-range $J$; 0 mismatches.
*Vacuity:* no ($h=1,n=1,J=\{1/2\}$). *Junk:* none.
*Hypotheses:* none extra are needed; there is no sign condition on $h$ and none on the location of $J$.
*Standard fact:* coarse jump-adapted Brownian increments obtained by summing fine ones have the correct law.

### 16. `jumpAdapted_map_eq` (theorem)
**Rendering.** Setting:
- $R:\Omega\to E$ is measurable (the random jump data);
- $Z:\Omega\to\mathbb R^{\mathbb N}$ has $\mu$-law `stdNormalSeq`, which forces AE-measurability and makes $\mu$ a
  probability measure;
- $R\perp Z$ (`IndepFun`, with the product σ-algebra on $\mathbb R^{\mathbb N}$);
- $u:E\to\mathbb R^{\mathbb N}$ and $\tau:E\to\mathbb N^{\mathbb N}$ are measurable, with $u(r)$ and $\tau(r)$ monotone
  for every $r$.

Claim: the joint law of $\big(R,\ (B_{u(R)}(Z,\tau(R)_{j+1})-B_{u(R)}(Z,\tau(R)_j))_j\big)$ equals the joint law of
$\big(R,\ (\sqrt{u(R)_{\tau(R)_{j+1}}-u(R)_{\tau(R)_j}}\,Z_j)_j\big)$.

**Assessment.** *True.* By independence, $\mathrm{law}(R,Z)=\mathrm{law}(R)\otimes\gamma^{\mathbb N}$. Both functions
are jointly measurable in $(r,z)$ ($k\in\mathbb N$ is countable). For each fixed $r$, the sections have equal laws by #11.
Since both maps are of AE-measurable functions, the equality is not the junk $0=0$.
*Measurability and independence:* adequate and natural. Independence of $R$ from the whole sequence $Z$ is what is
required.
*Vacuity:* no ($E=$`Unit`, $\Omega=\mathbb R^{\mathbb N}$, $Z=\mathrm{id}$).
*Standard fact:* conditionally on the jump data, Brownian increments on a jump-adapted grid are independent Gaussians.

### 17. `jumpAdapted_2_4` (theorem)
**Rendering.** Same hypotheses as #16, plus $F:E\times\mathbb R^{\mathbb N}\to\mathbb R$ jointly measurable. Then
$F(R,\text{BM-increments})$ is integrable iff $F(R,\sqrt{\Delta u}\,Z)$ is, and the two integrals are equal.

**Assessment.** *True.* Immediate from #16 by a change of variables. The integrability ↔ is stated, so the integral
equality is not a disguised $0=0$.
*Vacuity:* no. *Junk:* none.

### 18. `jaTimes` (def)
**Rendering.** For $i<N+1+m$: $t_i=ih$ if $i\le N$, and $t_i=s_{i-N-1}$ otherwise. These are the uniform times followed
by the $m$ jump times. The ℕ subtraction is exact on its branch.

### 19. `jaGrid` (def)
**Rendering.** The $\min(i,N+m)$-th order statistic of $(t_0,\dots,t_{N+m})$, with multiplicities kept. `Tuple.sort`
breaks ties by index (lexicographic order on $(t_i,i)$, checked in Mathlib).

### 20. `jaCoarseIdx` (def)
**Rendering.** $i\mapsto 2i$ for $i\le n$ and $i\mapsto i+n$ otherwise. This maps coarse labels into fine labels with
$t^{f}_{\iota(i)}=t^{c}_i$, and it is strictly increasing.

### 21. `jaPos` (def)
**Rendering.** The fine sorted position of the coarse point at sorted position $\min(j,n+m)$. Because `jaCoarseIdx` is
strictly increasing and ties are broken by index, the order is preserved: `jaPos` is strictly increasing on
$j\le n+m$ and constant afterwards (checked).

### 22. `jaCoarseInc` (def)
**Rendering.** $B_{\mathrm{jaGrid}(h,2n)}(z,\mathrm{jaPos}(j+1))-B_{\mathrm{jaGrid}(h,2n)}(z,\mathrm{jaPos}(j))$: the
coarse increments read off the fine Brownian path.

### 23. `jaOwnInc` (def)
**Rendering.** $\sqrt{g_{j+1}-g_j}\,z_j$ with $g=\mathrm{jaGrid}(h,N,m,s)$: directly simulated increments. The √
argument is ≥ 0 because the grid is sorted.

### 24. `jumpAdapted_random_map_eq` (theorem)
**Rendering.** $R,Z$ are as in #16; $M:E\to\mathbb N$ (number of jumps) and $S:E\to\mathbb R^{\mathbb N}$ (jump times)
are measurable; $h\in\mathbb R$ and $n\in\mathbb N$ are arbitrary. Then
$\mathrm{law}\big(R,\mathrm{jaCoarseInc}(h,n,M(R),S(R),Z)\big)=\mathrm{law}\big(R,\mathrm{jaOwnInc}(2h,n,M(R),S(R),Z)\big)$.

**Assessment.** *True.* For fixed $r$, $\mathrm{jaGrid}(h,2n)$ evaluated at `jaPos`$(j)$ equals $\mathrm{jaGrid}(2h,n)(j)$,
`jaPos` is monotone, and the variances telescope, so the conditional laws agree. Then apply independence as in #16.

Exact covariance check: 4000 random configurations with $h\in\{1/3,-1/2,0,2/5,1\}$, $n\in\{0..4\}$, $m\le5$, jump times
colliding with grid points or with each other or outside $[0,T]$. Results: 0 non-monotone `jaPos`, 0 grid mismatches,
0 covariance mismatches.

*Assumptions:* no ordering, range, distinctness or sign-of-$h$ condition is needed. The measurability of $R,M,S$, the
law of $Z$ and $R\perp Z$ are exactly what is needed.
*Vacuity:* no. *Junk:* none; the maps are of AE-measurable functions.
*Standard fact:* MLMC consistency of jump-adapted Brownian coupling, as in Xia–Giles-type jump-adapted MLMC.

### 25. `jumpAdapted_random_2_4` (theorem)
**Rendering and assessment.** This is the integral and integrability form of #24 for jointly measurable
$F:E\times\mathbb R^{\mathbb N}\to\mathbb R$. *True.* Not vacuous, no junk.

### 26. `thinLaw` (def)
**Rendering.** $\prod_{i<m}\big(p_i(a)\text{ if }a_i\text{ else }1-p_i(a)\big)$ for $a\in\{0,1\}^m$: the law of
sequential Bernoulli thinning of $m$ candidate jumps, where $p_i$ may depend on the whole vector $a$.

### 27. `thinLR` (def)
**Rendering.** $\prod_i\big(p_i/q_i\text{ if }a_i\text{ else }(1-p_i)/(1-q_i)\big)$, the likelihood ratio $dP/dQ$. There
is no division by 0 under `hq`.

### 28. `thinning_lr_unbiased` (theorem)
**Rendering.** For any real $p$ and any real $q$ with $q_i(a)\notin\{0,1\}$ for all $i,a$, and any
$F:\{0,1\}^m\to\mathbb R$: $\sum_a\mathrm{thinLaw}_q(a)\,F(a)\,\mathrm{thinLR}_{p,q}(a)=\sum_a\mathrm{thinLaw}_p(a)F(a)$.

**Assessment.** *True.* Pointwise, $\mathrm{thinLaw}_q\cdot\mathrm{thinLR}_{p,q}=\mathrm{thinLaw}_p$ factor by factor.
Exact rational check: 400 random cases with $p$ negative or greater than 1 and non-adapted; 0 failures.

*Positivity question:* **no $p,q>0$ (or $[0,1]$ or adaptedness) condition is needed**. Only $q\ne0$ where $a_i$ is true
and $q\ne1$ where $a_i$ is false are used, and `hq` is a sufficient strengthening of that. Without such a condition the
identity fails ($q\equiv0$, $p=\tfrac12$: LHS $=\tfrac12$, RHS $=1$). The probabilistic reading
$\mathbb E_Q[F\,dP/dQ]=\mathbb E_P[F]$ additionally needs $q\in(0,1)$ adapted and $p\in[0,1]$ adapted (#29); the Lean
statement is more general than that.
*Vacuity:* no. *Junk:* none.
*Standard fact:* change of measure / importance sampling for Bernoulli thinning.

### 29. `thinLaw_isProb` (theorem)
**Rendering.** If $0\le p_i(a)\le1$, and $p_i(a)$ depends only on $a_0,\dots,a_{i-1}$ (`had`), then
$\mathrm{thinLaw}_p\ge0$ and $\sum_a\mathrm{thinLaw}_p(a)=1$.

**Assessment.** *True.* Induct on the last coordinate. 300 random adapted cases: 0 failures. `had` is necessary:
$p_0(a)=\tfrac12$ if $a_0$ and $\tfrac9{10}$ otherwise gives total mass $3/5$. `hp` is used only for nonnegativity; with
adaptedness alone the sum is still 1.
*Vacuity:* no. *Standard fact:* a sequential (predictable) Bernoulli scheme defines a probability law.

### 30. `thinning_mlmc_correction` (theorem)
**Rendering.** Under `hq`:
$\sum_a\mathrm{thinLaw}_q(a)\big(F_f\,\mathrm{LR}_{p_f,q}-F_c\,\mathrm{LR}_{p_c,q}\big)=\mathbb E_{p_f}F_f-\mathbb E_{p_c}F_c$
(written as finite sums).

**Assessment.** *True.* Linear combination of two instances of #28. 300 random cases: 0 failures.
*Vacuity:* no. *Junk:* none.
*Standard fact:* unbiased MLMC correction with a common proposal $q$ for fine and coarse thinning.

### 31. `blockMean` (appended def)
**Rendering.** $\frac1N\sum_{k<N}f_i(\omega_{(i,k)}(x))$: the sample mean of $N$ samples at level $i$. For $N=0$ the value
is 0, which every theorem excludes.

### 32. `fineCoarseDiff` (appended def)
**Rendering.** Level $0$ is $P^f_0$; level $\ell+1$ is $P^f_{\ell+1}-P^c_\ell$.

### 33. `stdNormalSeq` (appended def)
**Rendering.** $\mathcal N(0,1)^{\otimes\mathbb N}$ via `Measure.infinitePi`. That construction takes no instance
argument and gives 0 when some factor is not a probability measure; here every factor is one.

### 34. `levyPairSum` (appended def)
**Rendering.** $z^{(2)}_k=z_{2k}+z_{2k+1}$.

### 35. `levyPath` (appended def)
**Rendering.** $\sum_{i<n}z_i$, with value 0 at $n=0$.

### 36. `unionGridBM` (appended def)
**Rendering.** $\sum_{i<k}\sqrt{u_{i+1}-u_i}\,z_i$: a Brownian path on grid $u$ built from normals $z$.
$\sqrt{\text{negative}}=0$ would be junk, but every theorem uses a monotone grid.
