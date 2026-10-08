# Blind read-back report: R27 (rank-1 lattice rules and MLQMC complexity)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round20/packet_R27_lattice.lean` |
| declarations audited | 15 theorems (plus 5 definitions read: `torusChar`, `torusCoeff`, `rank1Lattice`, `dualLattice`, `shiftedQMC`) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round20/work_R27/` (`lattice_variance_check.py/.out`, `complexity_check.py/.out`, `complexity_check_deep.py/.out`, Lean scratch files `scratch{1,2,3}.lean/.out`) |

Lean checks I ran: the packet compiles with only the 15 expected `sorry` warnings. I copied it into a
scratch file that imports only Mathlib, with `shiftedQMC` copied verbatim from the packet and no
`import MlmcLean`. `rfl` tests confirmed these points:
- `∑ ℓ ∈ range (L+1), (∫ y, f ℓ y) - I` and `(∑ ℓ ∈ range (L+1), shiftedQMC … - I)^2` parse as (sum) − I. A negative `rfl` test for the other reading fails, as it should.
- `((R:ℝ) * (R - 1))⁻¹` uses real subtraction.
- `((2:ℝ)^m)^r` is `Real.rpow`.
- `volume` on `UnitAddTorus d` is `Measure.pi (fun _ => volume)`, where each factor is `ofReal 1 • addHaarMeasure ⊤`. Its total mass is 1 (proved in scratch).
- `volume (Icc (0:d→ℝ) 1) = 1`.
- `dualLattice z 1 = univ`.

## Conventions used throughout

- $\mathbb T^d=(\mathbb R/\mathbb Z)^d$, with Haar probability measure. $e_k(x)=\prod_j e^{2\pi i k_j x_j}=e^{2\pi i k\cdot x}$ (`torusChar k`), and $\hat f(k)=\int e_{-k}f$ (`torusCoeff`).
- The rank-1 lattice is $x_i=(i z/N) \bmod 1$ for $i=0,\dots,N-1$, and $L^\perp=\{k\in\mathbb Z^d: N\mid k\cdot z\}$ (`dualLattice`).
- $Q_N(f)(u)=\frac1N\sum_{i<N}f(x_i+u)$ (`shiftedQMC`).
- $\sigma^2_{z,N}(f):=\sum_{k\in L^\perp\setminus\{0\}}|\hat f(k)|^2$.
- `variance X μ` $=(\int^-|X-\mathbb E X|^2)$`.toReal`.

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `hasSum_variance_rank1Lattice` | theorem | true | no | no |
| 2 | `rank1Lattice_randomShift` | theorem | true | no | no |
| 3 | `rank1Lattice_replicates` | theorem | true | no | no |
| 4 | `rank1Lattice_cube_randomShift` | theorem | true | no | no |
| 5 | `variance_rank1Lattice_le_variance` | theorem | true | no | no |
| 6 | `variance_rank1Lattice_re_torusChar` | theorem | true | no | no |
| 7 | `variance_rank1Lattice_le_of_coeff_le` | theorem | true | no | no |
| 8 | `variance_rank1Lattice_le_sq_tsum` | theorem | true | no | no (summability is assumed) |
| 9 | `variance_rank1Lattice_le_of_weighted` | theorem | true | no | no |
| 10 | `abs_rank1Lattice_sub_integral_le` | theorem | true | no | no (summability is assumed) |
| 11 | `mlqmc_complexity_core_rate` | theorem | true | no | no |
| 12 | `mlqmcLattice_complexity` | theorem | true | no | no (see note on `hV` tsum) |
| 13 | `mlqmcLattice_complexity_of_lt` | theorem | true | no | no |
| 14 | `mlqmcLattice_complexity_lt_two` | theorem | true | no | no |
| 15 | `mlqmcLattice_complexity_rate` | theorem | true | no | no |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement was found.** Numerical checks confirmed several identities exactly:
   - the variance identity (#1/#2/#4);
   - unbiasedness of the replicate sample variance (#3);
   - the invariance under the lattice rule and the value $1/2$ in #6;
   - the pointwise bound in #10.

   For the complexity theorems I ran the explicit allocations, and cost$\cdot\varepsilon^{p}$ stays bounded down to $\varepsilon=10^{-40}$.
2. **The `hV` hypotheses in #12–#15 are `tsum`s.** A non-summable series would make the tsum 0. For $f_\ell\in L^2$ the series is always summable (Parseval), and by #1 the tsum equals the variance of the shifted lattice rule. So `hV` is a genuine variance hypothesis: $\mathrm{Var}\le (c_2 2^{-b\ell}N^{-1})^2$ for $N=2^m$, or $N^{-r}$ in #15. It is required for **every** $m\ge0$, including $N=1$ (i.e. $\mathrm{Var}f_\ell\le c_2^2 4^{-b\ell}$), and every level $\ell$. Here $b$ is the decay rate of the standard deviation; Giles' $\beta$ equals $2b$.
3. **#12–#15 do not assume $c_1,c_2,c_3>0$ or $C_\ell\ge0$.**
   - If $c_1<0$, `hbias` cannot be satisfied.
   - If $c_3<0$, or $C_\ell<0$, the cost conclusion holds trivially.

   Both only make particular instances degenerate. The theorems stay true and non-vacuous.
4. **The case split in #12, $g<b \lor (a\le b\land a<g)$, is exactly right.**
   - When $g>b$ and $a\le b$, $1+(g-b)/a\le g/a$.
   - When $g=b>a$, the $\varepsilon^{-1}\log^{3/2}$ term is absorbed by $\varepsilon^{-g/a}$.
   - The boundary cases are rightly excluded: $g=b<a$ and $a=b=g$ have a log factor. Numerically, cost$\cdot\varepsilon$ grows without bound in those cases (`complexity_check*.out`).
5. **Shift independence.** Only **pairwise** independence is assumed, which is enough for the variance of a sum. Every $U_\ell$/$U_r$ for all $\ell\in\mathbb N$ must be measure-preserving onto the uniform law, which makes $\mu$ a probability measure automatically.
6. **#5 and #6 together.** #5 bounds the variance by $\mathrm{Var}(f)$, not by $\mathrm{Var}(f)/N$. That is the correct sharp general bound: #6 exhibits $f=\cos(2\pi k\cdot x)$ with $k\in L^\perp\setminus\{0\}$, for which $Q_N f=f$.
7. **#14 is qualitative** ($\exists p<2$). Its case $g=b$ is handled by lowering $b$ slightly: `hV` is monotone in $b$ for $\ell\ge0$.
8. **Minor Lean point.** With the Mathlib modules used, `IsProbabilityMeasure (volume : Measure (UnitAddTorus d))` is not found by instance search. Mathlib registers it only locally, in `AddCircleMulti`. The measure still has mass 1, which I proved in scratch. This affects proofs only, not the meaning of any statement.

---

## 1. `hasSum_variance_rank1Lattice`

**Rendering.** Let $d$ be a finite index set and $f:\mathbb T^d\to\mathbb R$ with $f\in L^2$. Let $z\in\mathbb Z^d$ and $N\in\mathbb N$ with $N>0$. Then the family $k\mapsto \mathbf 1_{L^\perp\setminus\{0\}}(k)\,|\hat f(k)|^2$, indexed by $k\in\mathbb Z^d$, is (unconditionally) summable with sum $\mathrm{Var}_{u\sim\mathrm{Unif}(\mathbb T^d)}\big[Q_N(f)(u)\big]$.

**Assessment.**
- **Truth.** True. Write $Q_N f(u)=\sum_k \hat f(k)e_k(u)\cdot\frac1N\sum_i e_k(x_i)$ in $L^2$. The character sum $\frac1N\sum_{i<N}e^{2\pi i\, i(k\cdot z)/N}$ equals $\mathbf 1[N\mid k\cdot z]$. So $Q_Nf=\sum_{k\in L^\perp}\hat f(k)e_k$, its mean is $\hat f(0)=\int f$, and Parseval gives the variance.
- **Numerical check.** $d=2$, $z=(1,2)$, $N=5$, a trigonometric polynomial with $\mathrm{Var}f=1.29$. The predicted value $0.5$ matched exact grid integration to $4\times10^{-16}$ (`lattice_variance_check.out`).
- **Vacuity.** Not vacuous: any $f\in L^2$ works.
- **Junk.** None. `variance` is finite because $Q_Nf\in L^2$, and `torusCoeff` is a genuine integral because $L^2\subset L^1$ on a probability space.
- **Hypotheses.** Natural.
- **Standard result.** The variance formula for a randomly shifted rank-1 lattice rule, $\mathrm{Var}=\sum_{k\in L^\perp\setminus 0}|\hat f(k)|^2$ (e.g. L'Ecuyer–Lemieux; Dick–Kuo–Sloan, Acta Numerica 2013).

## 2. `rank1Lattice_randomShift`

**Rendering.** Let $(\Omega,\mu)$ be a measurable space and $U:\Omega\to\mathbb T^d$ measure-preserving from $\mu$ to the uniform law (so $U$ is measurable, $U_\#\mu=$ Haar, and $\mu(\Omega)=1$). Let $z$ be given, $f\in L^2(\mathbb T^d)$ and $N>0$. Then:
- (a) for every $i\in\mathbb N$, $\omega\mapsto x_i+U(\omega)$ is measure-preserving;
- (b) $Q_Nf(U)\in L^2(\mu)$;
- (c) $\mathbb E_\mu[Q_Nf(U)]=\int_{\mathbb T^d}f$;
- (d) $\sum_{k\in L^\perp\setminus0}|\hat f(k)|^2=\mathrm{Var}_\mu[Q_Nf(U)]$, as a `HasSum`.

**Assessment.**
- **Truth.** True. (a) Haar measure is translation invariant. (b)–(d) Transport #1 through the measure-preserving map $U$. This was checked numerically together with #1 ($\mathbb E Q=0.7=\int f$).
- **Vacuity.** Not vacuous: take $\Omega=\mathbb T^d$, $\mu=$ volume and $U=\mathrm{id}$.
- **Junk.** None.
- **Hypotheses.** Standard.
- **Standard result.** A randomly shifted lattice rule is unbiased, with the variance formula above.

## 3. `rank1Lattice_replicates`

**Rendering.** Let $U_r:\Omega\to\mathbb T^d$ for $r\in\mathbb N$, each uniformly distributed (measure-preserving) and pairwise independent. Let $f\in L^2$, $N>0$ and $R>0$, and set $\bar Q=\frac1R\sum_{r<R}Q_Nf(U_r)$. Then:
- (a) $\mathbb E\bar Q=\int f$;
- (b) $\sum_k \mathbf 1_{L^\perp\setminus0}(k)|\hat f(k)|^2/R$ has sum $\mathrm{Var}(\bar Q)$, i.e. $\mathrm{Var}\bar Q=\sigma^2_{z,N}(f)/R$;
- (c) if $R\ge2$, the same series has sum $\mathbb E\Big[\frac{1}{R(R-1)}\sum_{r<R}\big(Q_Nf(U_r)-\bar Q\big)^2\Big]$. That is, the usual sample-variance estimator of $\mathrm{Var}\bar Q$ is unbiased.

The subtraction $R-1$ is real (checked), and $(R:\mathbb R)^{-1}$ is well defined since $R>0$.

**Assessment.**
- **Truth.** True. The $Q_r$ are pairwise independent, hence uncorrelated, square-integrable and identically distributed with variance $\sigma^2$. So $\mathrm{Var}\bar Q=\sigma^2/R$ and $\mathbb E\frac{1}{R-1}\sum(Q_r-\bar Q)^2=\sigma^2$.
- **Numerical check.** Exact enumeration for $R=2,3$ gave $0.25$ and $0.1667$ for both the estimator mean and $\mathrm{Var}\bar Q$, against predictions of $0.5/2$ and $0.5/3$.
- **Vacuity.** Not vacuous: e.g. $\Omega=(\mathbb T^d)^{\mathbb N}$ with `Measure.infinitePi` and coordinate projections.
- **Junk.** None: $R\ge2$ is required for the $(R(R-1))^{-1}$ part.
- **Hypotheses.** Pairwise independence of all $U_r$, $r\in\mathbb N$, is more than needed, since only $r<R$ matter. It is weaker than mutual independence. Fine.
- **Standard result.** The standard practical error estimate for randomly shifted QMC with $R$ independent shifts.

## 4. `rank1Lattice_cube_randomShift`

**Rendering.** Let $U:\Omega\to\mathbb R^d$ be measure-preserving from $\mu$ onto Lebesgue measure restricted to $[0,1]^d$ (mass 1). Let $F:\mathbb R^d\to\mathbb R$ with $F\in L^2([0,1]^d)$, and $N>0$. Then:
- $\mathbb E_\mu\big[\frac1N\sum_{i<N}F(\{iz/N+U\})\big]=\int_{[0,1]^d}F$, where $\{\cdot\}$ is the componentwise `Int.fract`;
- $\sum_{k\in L^\perp\setminus0}\Big|\int_{[0,1]^d}e^{-2\pi i k\cdot t}F(t)\,dt\Big|^2$ has sum equal to the variance of that estimator.

**Assessment.**
- **Truth.** True. $u\mapsto\{c+u\}$ maps Lebesgue measure on $[0,1]^d$ to Lebesgue measure on $[0,1)^d$, which equals it as a measure since the boundary is null. Identifying $[0,1)^d$ with $\mathbb T^d$, the statement reduces to #1/#2, and the cube Fourier coefficient is exactly $\hat F(k)$.
- **Values of $F$.** Only values of $F$ on $[0,1)^d$ are ever used, so being only a.e.-defined on $[0,1]^d$ is harmless.
- **Parsing.** `∫ t in Icc 0 1, F t ∧ …` parses as an equality conjoined with the `HasSum`. The integral body has precedence 60, so it does not absorb `∧`.
- **Vacuity.** Not vacuous: $\Omega=\mathbb R^d$, $\mu=\mathrm{vol}|_{[0,1]^d}$, $U=\mathrm{id}$.
- **Junk.** None.
- **Standard result.** The cube formulation of the randomly shifted lattice rule (shift modulo 1).

## 5. `variance_rank1Lattice_le_variance`

**Rendering.** For $f\in L^2(\mathbb T^d)$, any $z$ and $N>0$: $\mathrm{Var}_u[Q_Nf(u)]\le\mathrm{Var}(f)$.

**Assessment.**
- **Truth.** True: $\sum_{L^\perp\setminus0}|\hat f|^2\le\sum_{k\ne0}|\hat f|^2=\mathrm{Var}f$ by Parseval.
- **Vacuity.** Not vacuous.
- **Junk.** None.
- **Strength.** The bound is $\mathrm{Var}f$, not the Monte Carlo $\mathrm{Var}f/N$. This is the correct sharp general statement (see #6); it is not a weakened one.
- **Standard result.** A corollary of Parseval: a shifted lattice rule never does worse than a single random sample.

## 6. `variance_rank1Lattice_re_torusChar`

**Rendering.** Let $z$ be given, $N>0$, and $k\in L^\perp$ with $k\ne0$. Put $g(x)=\mathrm{Re}\,e_k(x)=\cos(2\pi k\cdot x)$. Then $Q_N g=g$ as functions on $\mathbb T^d$ (pointwise, for every shift), and $\mathrm{Var}(g)=1/2$.

**Assessment.**
- **Truth.** True.
  - $e_k(x_i+u)=e^{2\pi i\, i(k\cdot z)/N}e_k(u)=e_k(u)$ because $N\mid k\cdot z$, so the average of $N$ equal terms is $g(u)$.
  - $\int\cos(2\pi k\cdot x)\,dx=0$ and $\int\cos^2=1/2$ for $k\ne0$.
  - Numerical check: $\max_u|Q_Ng-g|=1.4\times10^{-15}$ and $\mathrm{Var}=0.5$.
- **Vacuity.** Not vacuous: $d=1$, $z=1$, $N=2$, $k=2$; or $N=1$ with any $k\neq0$.
- **Junk.** None.
- **Standard result.** The sharpness example showing that no rate is possible without decay of the Fourier coefficients: dual-lattice frequencies are aliased to the mean.

## 7. `variance_rank1Lattice_le_of_coeff_le`

**Rendering.** Let $f\in L^2$ and $N>0$, and let $w:\mathbb Z^d\to\mathbb R$ satisfy $|\hat f(k)|\le w(k)$ for all $k\in L^\perp\setminus0$. If $\sum_{k\in L^\perp\setminus0}w(k)^2=W$ (as a `HasSum`), then $\mathrm{Var}[Q_Nf]\le W$.

**Assessment.**
- **Truth.** True: termwise $|\hat f|^2\le w^2$ on the support, since $0\le|\hat f|\le w$ there. Comparing the two `HasSum`s with #1 gives the result.
- **Vacuity.** Not vacuous: take $w=|\hat f|$ and $W=\sigma^2$.
- **Junk.** None: summability is given by `HasSum`.
- **Standard result.** A comparison bound on the dual-lattice sum.

## 8. `variance_rank1Lattice_le_sq_tsum`

**Rendering.** Let $f\in L^2$ and $N>0$, and assume $\sum_{k\in L^\perp\setminus0}|\hat f(k)|$ is summable. Then $\mathrm{Var}[Q_Nf]\le\big(\sum_{k\in L^\perp\setminus0}|\hat f(k)|\big)^2$.

**Assessment.**
- **Truth.** True: $\sum a_k^2\le(\sum a_k)^2$ for $a_k\ge0$.
- **Junk.** Without `hs` the tsum would be 0 and the claim would become $\mathrm{Var}\le0$, which is false. With `hs` there is no junk.
- **Vacuity.** Not vacuous: any trigonometric polynomial.
- **Standard result.** $\ell^2\le\ell^1$; this is the variance version of the worst-case bound.

## 9. `variance_rank1Lattice_le_of_weighted`

**Rendering.** Let $f\in L^2$, $N>0$ and $c>0$. Let $\rho:\mathbb Z^d\to\mathbb R$ satisfy $\rho\ge0$ everywhere and $\rho\ge c$ on $L^\perp\setminus0$. Assume $\sum_{k\in\mathbb Z^d}\rho(k)|\hat f(k)|^2=S$ (`HasSum`, over **all** $k$). Then $\mathrm{Var}[Q_Nf]\le S/c$.

**Assessment.**
- **Truth.** True: $\sum_{L^\perp\setminus0}|\hat f|^2\le c^{-1}\sum_{L^\perp\setminus0}\rho|\hat f|^2\le c^{-1}S$, using $\rho\ge0$ off the dual lattice.
- **Vacuity.** Not vacuous: $\rho\equiv1$, $c=1$, $S=\|f\|_2^2$.
- **Junk.** None: $c>0$.
- **Standard result.** The weighted Korobov-norm bound $\mathrm{Var}\le\|f\|_\rho^2/\min_{L^\perp\setminus0}\rho$.

## 10. `abs_rank1Lattice_sub_integral_le`

**Rendering.** Let $f:\mathbb T^d\to\mathbb R$ be continuous with $\sum_{k\in\mathbb Z^d}|\hat f(k)|<\infty$. Then for every $z$, every $N>0$ and **every** shift $u$: $\big|Q_Nf(u)-\int f\big|\le\sum_{k\in L^\perp\setminus0}|\hat f(k)|$.

**Assessment.**
- **Truth.** True.
  - With absolutely summable coefficients, the Fourier series converges uniformly to a continuous function with the same coefficients. That function equals $f$ a.e., hence everywhere by continuity, since Haar measure has full support.
  - Then $Q_Nf(u)-\hat f(0)=\sum_{L^\perp\setminus0}\hat f(k)e_k(u)$.
  - Numerical check: max error $1.0$ against a bound of $1.0$; the bound is attained.
- **Vacuity.** Not vacuous: trigonometric polynomials.
- **Junk.** None: `hs` makes the tsum genuine, and the indicator of a summable family is summable.
- **Standard result.** The classical lattice-rule error expression for absolutely convergent Fourier series (Sloan–Joe, Korobov).

## 11. `mlqmc_complexity_core_rate`

**Rendering.** Fix reals $a>0$, $r>0$, $c_1,c_2,c_3>0$ and $g,b$ with $rg<b$. Then there is $K>0$ (depending only on these constants) such that for every $\varepsilon\in(0,1)$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with all $N_\ell\ge1$, satisfying:

$$(c_12^{-aL})^2+\sum_{\ell=0}^{L}\big(c_22^{-b\ell}N_\ell^{-r}\big)^2<\varepsilon^2,\qquad \sum_{\ell=0}^{L}N_\ell\,c_32^{g\ell}\le K\varepsilon^{-\max(1/r,\,g/a)}.$$

All powers are real `rpow` with positive bases.

**Assessment.**
- **Truth.** True. Choose $L$ minimal with $c_1^22^{-2aL}<\varepsilon^2/2$, so $2^{aL}\lesssim\varepsilon^{-1}$. Pick $\beta\in(g,b/r)$, which is possible because $rg<b$ and $r>0$, and set $N_\ell=\lceil A\varepsilon^{-1/r}2^{-\beta\ell}\rceil$.
  - Variance part: $\le c_2^2A^{-2r}\varepsilon^2\sum2^{-2(b-r\beta)\ell}<\varepsilon^2/2$ for large $A$.
  - Cost: $\le Ac_3\varepsilon^{-1/r}\sum2^{(g-\beta)\ell}+c_3\sum_{\ell\le L}2^{g\ell}$. The second term is $O(\varepsilon^{-g/a})$ if $g>0$, $O(\log\varepsilon^{-1})$ if $g=0$, and $O(1)$ if $g<0$. All of these are $\le K\varepsilon^{-\max(1/r,g/a)}$.
- **Numerical check** (`complexity_check.out`, `complexity_check_deep.out`). Cases $r=0.5$, $r=2$, $r=1.5$ with $g,b<0$, and $g=0$ all gave bounded cost$\cdot\varepsilon^p$ down to $\varepsilon=10^{-12}$, and down to $10^{-40}$ for the drifting case.
- **Vacuity.** Not vacuous.
- **Junk.** None.
- **Standard result.** The MLQMC complexity optimisation lemma (Giles-type complexity theorem with QMC rate $N^{-r}$).

## 12. `mlqmcLattice_complexity`

**Rendering.**

Setup:
- $(\Omega,\mu)$ is a measurable space.
- For each level $\ell\in\mathbb N$: a finite index type $d_\ell$, a uniform shift $U_\ell:\Omega\to\mathbb T^{d_\ell}$ (measure-preserving), the $U_\ell$ pairwise independent, and $f_\ell\in L^2(\mathbb T^{d_\ell})$.
- Generating vectors $Z_\ell(N)\in\mathbb Z^{d_\ell}$, and costs $C:\mathbb N\to\mathbb R$.
- Reals $I,a,b,g,c_1,c_2,c_3$ with $a>0$ and ($g<b$ or ($a\le b$ and $a<g$)).

Hypotheses:
- (bias) for all $L$: $\big|\sum_{\ell=0}^L\int f_\ell-I\big|\le c_12^{-aL}$. The parse is (sum) $-I$, checked.
- (hV) for all $\ell,m$: $\sum_{k\in L^\perp(Z_\ell(2^m),2^m)\setminus0}|\hat f_\ell(k)|^2\le(c_22^{-b\ell}/2^m)^2$.
- (hC) $C_\ell\le c_32^{g\ell}$.

Conclusion: there is $K>0$ such that for all $\varepsilon\in(0,1)$ there exist $L$ and $N:\mathbb N\to\mathbb N$, each $N_\ell$ a power of 2, with

$$\mathbb E_\mu\Big[\Big(\sum_{\ell=0}^LQ_{N_\ell}^{Z_\ell(N_\ell)}f_\ell(U_\ell)-I\Big)^2\Big]<\varepsilon^2,\qquad \sum_{\ell=0}^LN_\ell C_\ell\le K\varepsilon^{-\max(1,g/a)}.$$

**Assessment.**
- **Truth.** True.
  - MSE: by #2 and pairwise independence, MSE $=\text{bias}_L^2+\sum_\ell\mathrm{Var}_\ell\le c_1^22^{-2aL}+\sum_\ell c_2^22^{-2b\ell}N_\ell^{-2}$. Here `hV` applies because $N_\ell=2^m$ and the lattice used is $Z_\ell(N_\ell)$, consistent with `hV`.
  - Case $g<b$: apply #11 with $r=1$; rounding up to powers of 2 costs a factor of at most 2. Constants are replaced by $\max(c_i,1)$ if needed.
  - Case $a\le b$, $a<g$: the Lagrange allocation $N_\ell\propto(s_\ell^2/C_\ell)^{1/3}$ gives cost $\asymp\varepsilon^{-1}S^{3/2}+\sum_{\ell\le L}C_\ell$ with $S=\sum(s_\ell C_\ell)^{2/3}$. If $g>b$ this is $\varepsilon^{-1-(g-b)/a}+\varepsilon^{-g/a}\lesssim\varepsilon^{-g/a}$, because $a\le b$. If $g=b$ it is $\varepsilon^{-1}\log^{3/2}+\varepsilon^{-g/a}\lesssim\varepsilon^{-g/a}$, because $g/a>1$.
  - Numerical check: bounded ratios for $(a,b,g)=(1,2,1),(0.5,2,1.5),(1,1.5,2),(1,2,2)$. The excluded boundaries $(2,1,1)$ and $(1,1,1)$ show growth, so the strict inequalities matter.
- **Integrability.** The integrand is in $L^1$ because every $Q(U_\ell)\in L^2(\mu)$ and $\mu(\Omega)=1$. The MSE is therefore not a junk 0.
- **`hV` and the tsum.** `hV` is a tsum, but it is always summable (#1), so it equals the true variance and there is no junk.
- **Constants.** No positivity of $c_i$ or $C_\ell$ is assumed. This is harmless: $c_1<0$ makes `hbias` unsatisfiable, and negative costs make the cost bound trivial.
- **Vacuity.** Not vacuous: $d_\ell=\mathrm{Fin}\,1$, $Z\equiv1$, $f_\ell=2^{-b\ell}\cos2\pi x$, $I=0$, $c_2^2\ge1/2$, $C_\ell=c_32^{g\ell}$ and product-measure shifts. For $N\ge2$ the dual lattice $N\mathbb Z$ misses $\pm1$.
- **Strength.** `hV` assumes the full rate $N^{-1}$ for every power of 2, including $N=1$. That is strong but standard; #15 covers rates $N^{-r}$.
- **Standard result.** The MLQMC complexity theorem for randomly shifted lattice rules (cf. Kuo–Schwab–Sloan 2015; Giles–Waterhouse).

## 13. `mlqmcLattice_complexity_of_lt`

**Rendering.** The same setup and hypotheses as #12, except that the case condition is replaced by $b<g$. Conclusion: the same, with cost $\le K\varepsilon^{-\max(1+(g-b)/a,\;g/a)}$.

**Assessment.**
- **Truth.** True. The Lagrange allocation gives $\varepsilon^{-1}S^{3/2}\asymp\varepsilon^{-1}2^{(g-b)L}\asymp\varepsilon^{-1-(g-b)/a}$, and rounding to $N_\ell\ge1$ adds $\sum_{\ell\le L}C_\ell\lesssim\max(1,\varepsilon^{-g/a})$. Since $1+(g-b)/a>1$, the $O(1)$ and log terms are absorbed.
- **Numerical check.** Bounded ratios for $(1,1,2)$, $(2,1,2)$ and $(1,-2,-1)$ (the last with $g,b<0$).
- **Vacuity.** Not vacuous: the same example as #12.
- **Junk.** None.
- **Standard result.** The $\beta<\gamma$ branch of the MLMC/MLQMC complexity theorem: with $r=1$, $\varepsilon^{-1/r-(g-b/r)/a}$.

## 14. `mlqmcLattice_complexity_lt_two`

**Rendering.** The same setup and hypotheses as #12, with $g<2a$ and $g<a+b$ instead of the case condition. Conclusion: there exists a real $p<2$ and $K>0$ such that the conclusion of #12 holds with cost $\le K\varepsilon^{-p}$.

**Assessment.**
- **Truth.** True.
  - If $g<b$: $p=\max(1,g/a)<2$.
  - If $g>b$: $p=\max(1+(g-b)/a,g/a)<2$, using $g<a+b$ and $g<2a$.
  - If $g=b$: lower $b$ to some $b'<b$ with $g<a+b'$; `hV` still holds because $2^{-b\ell}\le2^{-b'\ell}$ for $\ell\ge0$. Then apply #13.
  - Numerical check: $(1,1.5,1.5)$ with $p=1.5$ and $(2,1,1)$ with $p=1.1$ gave bounded ratios.
- **Vacuity.** Not vacuous.
- **Junk.** None.
- **Strength.** Qualitative only: a statement that MLQMC beats the Monte Carlo $\varepsilon^{-2}$.
- **Standard result.** A corollary of the MLQMC complexity theorem.

## 15. `mlqmcLattice_complexity_rate`

**Rendering.** As #12, with an additional $r>0$ and the case condition replaced by $rg<b$. `hV` becomes $\sum_{L^\perp\setminus0}|\hat f_\ell|^2\le\big(c_22^{-b\ell}/(2^m)^r\big)^2$, where $(2^m)^r$ is `rpow`. Conclusion: cost $\le K\varepsilon^{-\max(1/r,\,g/a)}$, with $N_\ell$ powers of 2 and MSE $<\varepsilon^2$.

**Assessment.**
- **Truth.** True: the MSE decomposition as in #12, followed by #11, with power-of-2 rounding costing a factor of at most $2^r$ in the variance or 2 in the cost.
- **Numerical check.** $r=0.5$ and $r=2$ with power-of-2 rounding gave bounded ratios.
- **Vacuity.** Not vacuous.
- **Junk.** None.
- **Standard result.** The MLQMC complexity theorem with a general QMC convergence rate $N^{-r}$; this is the $rg<b$ regime.
