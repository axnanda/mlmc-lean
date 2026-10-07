# Blind read-back: `packet_R13_corollaries.lean`

| Field | Value |
|---|---|
| Date | 2026-10-07 |
| Packet | `readback/round16/packet_R13_corollaries.lean` |
| Declarations audited | 18 (15 theorems and 3 module definitions: `blockAvg`, `emFineM`, `emCoarseM`); the 13 appended definitions are rendered for reference |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round16/work_R13/` (`contraction.py`, `contracting_mlmc.py`, `lut.py`, `mc_exit.py`, `rates.py`, `blockavg.py`, each with a `.out`; Lean elaboration checks are in `scratch*.lean` and `scratch3.out`) |

Elaboration check: a scratch copy of all 15 statements with `import MlmcLean` compiles with only
`sorry` warnings (`scratch.lean`). `#print` of the module and appended definitions matches the
packet text (`scratch2.lean`). `#check` with `pp.coercions.types` confirms the casts described
below (`scratch3.out`).

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| D1 | `blockAvg` | def | n/a | n/a | no ($M=0$ gives $0/0=0$, but every theorem assumes $M>0$) |
| D2 | `emFineM` | def | n/a | n/a | no |
| D3 | `emCoarseM` | def | n/a | n/a | no |
| 1 | `emStep_meanSquare_contraction` | theorem | true | no | no |
| 2 | `contracting_sde_mlmc` | theorem | true | no | no |
| 3 | `lutStream_tendstoInDistribution` | theorem | true | no | no |
| 4 | `lutStreams_sum_tendstoInDistribution` | theorem | true | no | no |
| 5 | `mc_exit_time_complexity` | theorem | true (elementary arithmetic) | no | no |
| 6 | `mc_complexity_lower` | theorem | true | no | no |
| 7 | `beta_le_two_alpha` | theorem | true | no | no |
| 8 | `beta_le_two_alpha_of_bias` | theorem | true | no | no |
| 9 | `mlmc_optimal_complexity_necessary` | theorem | true | no | no |
| 10 | `sqrt_mul_blockAvg` | theorem | true | no | no (true even without its two hypotheses) |
| 11 | `emCoarseM_eq` | theorem | true | no | no |
| 12 | `map_blockSum_gaussian` | theorem | true | no | no |
| 13 | `measurePreserving_blockAvg` | theorem | true | no | no |
| 14 | `integral_emCoarseM` | theorem | true | no | no (when $P^f_\ell$ is not integrable, both sides are $0$, so the identity still holds; the intended case is the $L^2$ one) |
| 15 | `em_mlmc_theorem1_M` | theorem | true | no | no |

No statement is false, vacuous or dependent on a junk value.

## Main points for a human auditor

1. **The limit in (a) is assumed, not proved.** `contracting_sde_mlmc` takes as a hypothesis a
   function $X$ with $\mathrm{backIter}_n(\xi(\omega),x_0)\to X(\omega)$ almost surely. Under the
   other hypotheses such an $X$ always exists. The increments of the backward iteration satisfy
   $\|Y_{n+1}-Y_n\|_{L^2}\le C\rho^{n/2}$, so they are summable almost surely; `contraction.out`
   shows this decay numerically. The hypothesis is therefore satisfiable and harmless, but the
   theorem does not itself establish that the chain has a limit. The target is the invariant law
   of the Euler-Maruyama chain with the fixed step $h$, not the invariant law of the SDE.
2. **Naming in (a).** In `contracting_sde_mlmc`, `N ℓ` is the number of backward Euler-Maruyama
   steps at level $\ell$ (it grows linearly, $m_1\ell\le N_\ell\le m_2(\ell+1)$). `M ℓ` is the
   number of samples. The cost model charges $N_\ell$ per level-$\ell$ sample rather than
   $N_\ell+N_{\ell-1}$, which changes the cost by at most a factor of 2.
3. **The step-size condition is exactly right.** `hstep` $K_b^2+K_a^2h<2\kappa$ is equivalent to
   $\rho<1$ when $h>0$. `contraction.out` confirms this:
   - $\rho$ crosses 1 exactly at $h=(2\kappa-K_b^2)/K_a^2$;
   - the bound $\mathbb E[\Delta^2]\le\rho(x-y)^2$ holds in every sampled case;
   - $\rho$ is attained (equality) for linear $a,b$.

   $\rho\ge0$ holds because dissipativity plus the Lipschitz bound force $\kappa\le K_a$, so
   $\rho\ge(1-\kappa h)^2+K_b^2h$.
4. **(b) has a superfluous hypothesis.** In both LUT theorems, `MonotoneOn f (Ioo 0 1)` is not
   needed. The LUT output is $\mathbb E[f(U)\mid\mathcal F_d]$ for the dyadic $\sigma$-algebra
   $\mathcal F_d$, so it converges to $f(U)$ almost surely by martingale convergence, for any
   $f\in L^1(0,1)$. The floor index $\lfloor 2^dU\rfloor_+$ always picks the dyadic cell that
   contains $U\in(0,1)$ (checked on $10^5$ samples). The cell integrals are genuine, because
   $\int_0^1|f|=\mathbb E|Z|<\infty$, so no non-integrable cell can silently become $0$.
   Kolmogorov-Smirnov distances to $N(0,1)$ fall like $2^{-d}$ (`lut.out`).
5. **(c) is only arithmetic.** `mc_exit_time_complexity` is pure parameter arithmetic: the MSE is
   modelled as $\text{bias}^2+\bar V/N$, and no estimator or random variable appears. Parts (iii)
   and (iv) are the elementary facts $\varepsilon\sqrt{|\log\varepsilon|}\to0$ and
   $\sqrt{|\log\varepsilon|}\ge1$ for $\varepsilon\le e^{-1}$. They do not prove an MLMC
   exit-time complexity.
6. **The quantifiers in (d) and (e) work.** In (d), "frequently" combined with "eventually" gives
   infinitely many $\ell$ at which all the inequalities hold, and that is enough. In (e) there is
   no "frequently": the lower bounds on bias, $V_\ell$ and $C_\ell$ are assumed for every $\ell$.
   The two conclusions follow:
   - $\gamma<\beta$ from Cauchy-Schwarz plus $L(\varepsilon)\to\infty$;
   - $\gamma/\alpha\le2$ from $N_L\ge1$.

   `rates.out` gives a non-vacuous instance with $\alpha=1,\beta=2,\gamma=1$, where
   $\text{cost}\cdot\varepsilon^2\approx23$ stays bounded. It also shows the growth of
   $\text{cost}\cdot\varepsilon^2$ when either condition fails.
7. **$M=1$ is allowed in (f).** All refinement-factor statements assume only $0<M$, so the
   degenerate case $M=1$ (no refinement, `blockAvg 1 = id`) is included. This is harmless:
   division by $\sqrt M$ never hits $\sqrt0$. `em_mlmc_theorem1_M` is the abstract Giles
   Theorem 1 and stays true for $M=1$. Two hypotheses are slightly loose but harmless:
   - $C_\ell$ is not required to be $\ge0$;
   - $h_0$ may be negative, in which case $\sqrt{h}=0$ removes the noise. The theorem stays true
     because it is abstract in $(i)$-$(iv)$.
8. **Unneeded hypotheses in the block-average lemmas.** `sqrt_mul_blockAvg` holds without `hM`
   and without `hh`: both sides are $0$ when $M=0$ or $h<0$. `map_blockSum_gaussian`,
   `measurePreserving_blockAvg` and `emCoarseM_eq` (at $\ell=0$, $h_0\neq0$) do need $M>0$.

---

## Module definitions

### D1 `blockAvg`
**Rendering.** For $M\in\mathbb N$, $z:\mathbb N\to\mathbb R$ and $k\in\mathbb N$:
$\mathrm{blockAvg}_M(z)_k=\big(\sum_{i<M}z_{Mk+i}\big)/\sqrt{M}$, with $M$ cast to $\mathbb R$.
For $M=0$ the value is $0/0=0$.

**Assessment.** It is the normalised sum over the $k$-th block of length $M$. For $M\ge1$ it is
the standard way to build coarse Gaussian increments from fine ones.

### D2 `emFineM`
**Rendering.** $P^f_\ell(z)=\Phi_\ell\big(\mathrm{emPath}(a,b,h_0/M^\ell,S_0,z)\big)$. This is the
Euler-Maruyama path with step $h_\ell=h_0/M^\ell$ (as a real number) driven by the standard
normals $z$, followed by the level-$\ell$ path functional $\Phi_\ell$.

### D3 `emCoarseM`
**Rendering.**
$P^c_\ell(z)=\Phi_\ell\big(\mathrm{emPath}(a,b,M\cdot h_0/M^{\ell+1},S_0,\mathrm{blockAvg}_M z)\big)$.
This is the level-$\ell$ path, with step $M h_{\ell+1}=h_\ell$, driven by the block-normalised
level-$(\ell+1)$ normals. Its Brownian increments are
$\sqrt{h_\ell}\,\mathrm{blockAvg}_M(z)_k=\sum_{i<M}\sqrt{h_{\ell+1}}z_{Mk+i}$, which is the
correct coupling. `blockavg.py` checks that the Brownian endpoints agree to $10^{-16}$. In
`fineCoarseDiff`, $P^c_{\ell}$ is paired with $P^f_{\ell+1}$.

### Appended definitions (reference)
- `levelDiff Pl 0 = Pl 0` and `levelDiff Pl (ℓ+1) = Pl(ℓ+1) − Pl ℓ`, pointwise.
- `fineCoarseDiff Pf Pc 0 = Pf 0` and `fineCoarseDiff Pf Pc (ℓ+1) = Pf(ℓ+1) − Pc ℓ`.
- `levelEstimator Pl ω ℓ N x` $=N^{-1}\sum_{n<N}\mathrm{levelDiff}\,Pl\,\ell\,(\omega(\ell,n)x)$.
- `mlmcEstimator` $=\sum_{\ell\le L}$ of the level estimators with $N_\ell$ samples.
- `blockMean f ω i N x` $=N^{-1}\sum_{n<N}f_i(\omega(i,n)x)$.
- `totalCost cost L N x` $=\sum_{\ell\le L}\sum_{n<N_\ell}\mathrm{cost}_{\ell,n}(x)$.
- `complexityBound` $=\varepsilon^{-2}$ if $\gamma<\beta$, $\varepsilon^{-2}(\log\varepsilon)^2$ if
  $\beta=\gamma$, and $\varepsilon^{-2-(\gamma-\beta)/\alpha}$ otherwise.
- `emPath`: $S_0$, then
  $S_{i+1}=S_i+a(S_i,ih)h+b(S_i,ih)\sqrt h\,z_i$, where $\sqrt{\cdot}$ is `Real.sqrt`
  ($=0$ for $h<0$).
- `stdNormalSeq` $=N(0,1)^{\otimes\mathbb N}$.
- `emStep a b h S dW` $=S+a(S)h+b(S)\,dW$.
- `backIter φ 0 e x = x` and `backIter φ (n+1) e x = φ(backIter φ n (e∘succ) x, e 0)`. Hence
  $\mathrm{backIter}_n(e,x)=F_{e_0}\circ\cdots\circ F_{e_{n-1}}(x)$: the chain started at $x$ at
  time $-n$, with $e_0$ the most recent innovation, and
  $\mathrm{backIter}_{n+1}(e,x)=\mathrm{backIter}_n(e,F_{e_n}(x))$.
- `gridPt d j` $=j/2^d$.
- `lutValue f d j` $=2^d\int_{j/2^d}^{(j+1)/2^d}f$, the average of $f$ over a dyadic cell.

---

## 1. `emStep_meanSquare_contraction`
**Rendering.** The setting is:
- $a,b:\mathbb R\to\mathbb R$ with Lipschitz constants $K_a,K_b\ge0$;
- $\kappa\in\mathbb R$ with $(x-y)(a(x)-a(y))\le-\kappa(x-y)^2$ for all $x,y$;
- $h\in\mathbb R_{\ge0}$ with $h>0$ and $K_b^2+K_a^2h<2\kappa$.

Let $\rho:=1-2\kappa h+K_a^2h^2+K_b^2h$. The theorem says that (i) $0\le\rho$, (ii) $\rho<1$, and
(iii) for all $x,y$:
$$\textstyle\int^-\mathrm{ofReal}\big((x+a(x)h+b(x)w-y-a(y)h-b(y)w)^2\big)\,dN(0,h)(w)\le\mathrm{ofReal}(\rho)\cdot\mathrm{ofReal}((x-y)^2).$$
`gaussianReal 0 h` has variance $h$.

**Assessment.** True. Write $\Delta=A+Bw$ with $A=(x-y)+(a(x)-a(y))h$ and $B=b(x)-b(y)$. Then
$\mathbb E\Delta^2=A^2+B^2h$, and
$A^2\le(x-y)^2(1-2\kappa h+K_a^2h^2)$ by dissipativity and the Lipschitz bound, while
$B^2h\le K_b^2h(x-y)^2$.
- (ii) holds because $\rho-1=h(K_b^2+K_a^2h-2\kappa)<0$.
- (i) holds because `hstep` forces $\kappa>0$, and dissipativity plus the Lipschitz bound give
  $\kappa\le K_a$, so $\rho\ge(1-\kappa h)^2\ge0$.

With $\rho\ge0$ the product of `ofReal`s equals $\mathrm{ofReal}(\rho(x-y)^2)$, and the lintegral
is the genuine second moment.

Numerical check (`contraction.out`): three examples (linear; $a=-2x+\sin x$, $b=\tfrac12\cos x$;
$a=-1.5x+\tfrac12\tanh x$, $b=0.3\sin x$). The bound holds for 2000 random pairs at each step
size, $\rho$ crosses 1 exactly at $h=(2\kappa-K_b^2)/K_a^2$, and equality holds in the linear
case.

Non-vacuity: $a(x)=-x$, $b=0$, $K_a=\kappa=1$, $K_b=0$, $h=1/2$ gives $\rho=1/4$. There is no
junk value. This is the standard mean-square contractivity of the Euler-Maruyama step under a
one-sided Lipschitz (dissipativity) condition, with step restriction
$h<(2\kappa-K_b^2)/K_a^2$.

## 2. `contracting_sde_mlmc`
**Rendering.** The hypotheses on $a,b,\kappa,h$ are as in 1. In addition:
- $\gamma\in(0,1]$ and $f$ satisfies $|f(x)-f(y)|\le K_f|x-y|^\gamma$ (real power);
- $\xi_k$ are i.i.d. $N(0,h)$ (measurable, `iIndepFun`, with marginal laws $N(0,h)$) on a
  probability space $(\Omega,\mu)$;
- $x_0\in\mathbb R$, and $X:\Omega\to\mathbb R$ with
  $\mathrm{backIter}_n(\mathrm{emStep}_{a,b,h},\xi(\omega),x_0)\to X(\omega)$ for $\mu$-a.e. $\omega$;
- $N:\mathbb N\to\mathbb N$ is monotone with $m_1\ge1$, $m_1\ell\le N_\ell\le m_2(\ell+1)$.

Conclusion: there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there are $L$ and a
sample-count function $M$ with every $M_\ell>0$ and the following, where the probability space
is $\Pi=\big(N(0,h)^{\otimes\mathbb N}\big)^{\otimes(\mathbb N\times\mathbb N)}$:
- the estimator is
  $\hat Y=\sum_{\ell\le L}M_\ell^{-1}\sum_{n<M_\ell}\big(P_\ell-P_{\ell-1}\big)(x_{(\ell,n)})$,
  with $P_\ell(e)=f(\mathrm{backIter}_{N_\ell}(e,x_0))$ and $P_{-1}:=0$;
- $(\hat Y-\int f(X)\,d\mu)^2$ is integrable and its integral is $<\varepsilon^2$;
- the expected cost $\sum_{\ell\le L}M_\ell N_\ell$ is at most $c_4\varepsilon^{-2}$.

**Assessment.** True. Write $Y_n=\mathrm{backIter}_n$. By 1, applied conditionally from the
outermost step inwards (each $F_{e_k}$ acts on arguments independent of $e_k$):
$$\mathbb E|Y_{n+1}-Y_n|^2=\mathbb E|G_n(F_{e_n}x_0)-G_n(x_0)|^2\le\rho^n\,\mathbb E|F_{e_n}x_0-x_0|^2.$$
So $\|Y_{n+1}-Y_n\|_2=O(\rho^{n/2})$. Hence $Y_n$ converges almost surely and in $L^2$, the
hypothesis `hX` is satisfiable, and $\|X-Y_n\|_2=O(\rho^{n/2})$ by Fatou.

Since $\gamma\le1$, Jensen gives $V_\ell\le K_f^2(\mathbb E|Y_{N_\ell}-Y_{N_{\ell-1}}|^2)^\gamma=O(\rho^{\gamma(\ell-1)})$
and $|\text{bias}_L|=O(\rho^{\gamma N_L/2})=O(\rho^{\gamma L/2})$. The cost per sample is
$N_\ell=O(\ell)$, so $\sum\sqrt{V_\ell N_\ell}<\infty$. With $L=O(\log1/\varepsilon)$ and the
usual allocation $M_\ell=\max(1,\lceil2\varepsilon^{-2}\sqrt{V_\ell/N_\ell}\,S\rceil)$, the cost
is at most $2\varepsilon^{-2}S^2+m_2(L+1)^2=O(\varepsilon^{-2})$. Under $\mu$ the laws of
$Y_{N_\ell}$ equal those under $\Pi$, so the target $\int f(X)\,d\mu$ is the limit of the level
means. $f\circ X$ is integrable, since $|f(x)|\le|f(x_0)|+K_f|x-x_0|^\gamma$ and
$X\in L^2$, so the target is not the junk value $0$.

`contracting_mlmc.out` simulates the level variances for $f=\sqrt{|x|}$ ($\gamma=1/2$) with
$N_\ell=3\ell$. They decay geometrically and $\sum\sqrt{V_\ell N_\ell}$ levels off.

Non-vacuity: $a=-x$, $b=0$, $h=1/2$, $f=\mathrm{id}$, $\xi$ the coordinates of
$N(0,1/2)^{\otimes\mathbb N}$, $X=0$, $N_\ell=\ell$. A non-degenerate example is
$a=-2x+\sin x$, $b=\tfrac12\cos x$, $h=0.1$. There is no junk value.

Notes: the existence of the limit is assumed, not proved (Main point 1). Monotonicity of $N$ is
not needed. This is the standard result that, for a geometrically contracting chain, MLMC over
the "start time in the past" achieves $O(\varepsilon^{-2})$ for Hölder functionals of the
invariant law of the Euler-Maruyama chain (coupling from the past).

## 3. `lutStream_tendstoInDistribution`
**Rendering.** The hypotheses are:
- $f:\mathbb R\to\mathbb R$ is nondecreasing on $(0,1)$;
- $f$ is a.e.-measurable for Lebesgue measure on $(0,1)$ and pushes it forward to $N(0,1)$;
- $U$ has law $\mathrm{Unif}(0,1)$ under the probability measure $P$;
- $G$ has law $N(0,1)$ under $P'$.

Conclusion: $X_d(\omega)=2^d\int_{j/2^d}^{(j+1)/2^d}f$, with $j=\lfloor2^dU(\omega)\rfloor_+$
(`Nat.floor`), converges in distribution to $G$ as $d\to\infty$. Mathlib's
`TendstoInDistribution` means each $X_d$ is a.e.-measurable, $G$ is a.e.-measurable, and the laws
converge weakly as `ProbabilityMeasure`s.

**Assessment.** True. For $U\in(0,1)$, $j\in\{0,\dots,2^d-1\}$ and $U\in[j2^{-d},(j+1)2^{-d})$
(checked on $10^5$ samples). Then $X_d=\mathbb E[f(U)\mid\mathcal F_d]$, where $\mathcal F_d$ is
the dyadic $\sigma$-algebra, and $f\in L^1(0,1)$ because $\int|f|=\mathbb E|Z|$. Lévy's upward
theorem gives $X_d\to f(U)$ almost surely, and $f(U)\sim N(0,1)$. Measurability holds because
$X_d$ factors through the $\mathbb N$-valued $\lfloor2^dU\rfloor_+$.

There is no junk value: each cell integral is a genuine integral, and $U\notin(0,1)$ has
probability $0$. `lut.out` (with $f=\Phi^{-1}$, using the closed-form cell integrals
$\varphi(\Phi^{-1}(a))-\varphi(\Phi^{-1}(b))$) shows the KS distance to $N(0,1)$ falling from
0.29 at $d=1$ to $1.5\cdot10^{-4}$ at $d=12$, and the second moment tending to 1.

Non-vacuity: $f=\Phi^{-1}$ on $(0,1)$, $0$ elsewhere; $U=\mathrm{id}$ on
$(\mathbb R,\lambda|_{(0,1)})$; $G=\mathrm{id}$ on $(\mathbb R,N(0,1))$. The monotonicity
hypothesis is superfluous. This is convergence of the piecewise-constant (cell-mean) lookup-table
inverse CDF, a martingale-convergence argument.

## 4. `lutStreams_sum_tendstoInDistribution`
**Rendering.** $f$ and $G$ are as in 3. $n>0$ and $U_1,\dots,U_n$ are independent
$\mathrm{Unif}(0,1)$ under $P$. Conclusion:
- (i) for each $i$, $n^{-1/2}X_d^{(i)}\Rightarrow N(0,1/n)$, written as the variable `id` under
  `gaussianReal 0 (n:ℝ≥0)⁻¹`;
- (ii) $\sum_i n^{-1/2}X_d^{(i)}\Rightarrow G\sim N(0,1)$.

**Assessment.** True. (i) is scaling of 3. For (ii), each summand converges almost surely on the
common space to $n^{-1/2}f(U_i)$. The limit $n^{-1/2}\sum f(U_i)$ is $N(0,1)$ because the
$f(U_i)$ are i.i.d. $N(0,1)$. Almost-sure convergence implies convergence in distribution.

$n>0$ prevents $(0)^{-1}=0$ (which would give the Dirac limit). `lut.out` computes the exact law
for $n=2$: the KS distance is $2^{-d-1}$, tending to 0.

Non-vacuity: product of $n$ uniforms with $f=\Phi^{-1}$. There is no junk value, and
monotonicity is again superfluous.

## 5. `mc_exit_time_complexity`
**Rendering.** For $c_1,c_3>0$ and $\bar V\ge0$:
- (i) there is $c_4>0$ such that for all $\varepsilon\in(0,1)$ there are $L,N\in\mathbb N$, $N>0$,
  with $(c_12^{-L/2})^2+\bar V/N\le\varepsilon^2$ and $N\,c_32^L\le c_4\varepsilon^{-4}$;
- (ii) the same with bias $c_12^{-L}$ and cost bound $c_4\varepsilon^{-3}$;
- (iii) $\varepsilon^{-3}\sqrt{|\log\varepsilon|}/\varepsilon^{-4}\to0$ as $\varepsilon\to0^+$;
- (iv) $\varepsilon^{-3}\le\varepsilon^{-3}\sqrt{|\log\varepsilon|}$ for
  $0<\varepsilon\le e^{-1}$.

**Assessment.** True.
- (i): take the least $L$ with $c_1^22^{-L}\le\varepsilon^2/2$ and
  $N=\max(1,\lceil2\bar V\varepsilon^{-2}\rceil)$. Then the cost is at most
  $(2\bar V+1)\max(1,4c_1^2)c_3\varepsilon^{-4}$.
- (ii): the same with $2^{-2L}$, giving cost $O(\varepsilon^{-3})$.
- (iii) is $\varepsilon\sqrt{|\log\varepsilon|}\to0$.
- (iv) uses $|\log\varepsilon|\ge1$.

`mc_exit.out` confirms that the witnesses satisfy the MSE bound on 400 values of $\varepsilon$
down to $10^{-10}$, with bounded $\text{cost}\cdot\varepsilon^4$ (resp. $\varepsilon^3$).

Non-vacuity is trivial ($c_1=c_3=1$, $\bar V=0$), and there is no junk value since rpow is only
applied to $\varepsilon>0$. The statement is only arithmetic about bias, variance and cost
models; no estimator appears (Main point 5). It is the standard plain-MC complexity
$\varepsilon^{-2-1/\alpha}$ for weak orders $1/2$ and $1$.

## 6. `mc_complexity_lower`
**Rendering.** The setting is:
- $\omega_n:\Omega\to\Omega_0$ are measure-preserving from $\mu$ (a probability measure) to
  $\nu$, and mutually independent;
- $P\in L^1(\nu)$, and $P_L$ is measurable and in $L^2(\nu)$;
- $\alpha>0$, $\gamma\ge0$, $a_1>0$, $a_3\ge0$, $L\in\mathbb N$, $N\in\mathbb N_{>0}$,
  $\varepsilon>0$, and $v,C$ real.

The hypotheses are:
- $a_12^{-\alpha L}\le|\int(P_L-P)\,d\nu|$;
- $v\le\mathrm{Var}_\nu(P_L)$;
- $a_32^{\gamma L}\le C$;
- $\mathbb E_\mu\big[(N^{-1}\sum_{n<N}P_L(\omega_n)-\int P\,d\nu)^2\big]\le\varepsilon^2$.

Conclusion: $v\,a_3\,a_1^{\gamma/\alpha}\varepsilon^{-2-\gamma/\alpha}\le N\,C$.

**Assessment.** True. The MSE equals $\mathrm{Var}(P_L)/N+\text{bias}^2$ (i.i.d. samples, $L^2$),
so the MSE integral is genuine and not junk. This gives:
- $N\ge v/\varepsilon^2$;
- $a_12^{-\alpha L}\le\varepsilon$, hence $2^{\gamma L}\ge(a_1/\varepsilon)^{\gamma/\alpha}$.

Multiply when $v\ge0$. When $v<0$ the left side is $\le0\le NC$. `rates.out` finds 0 violations
in $2\cdot10^5$ random admissible instances and a family that is tight up to a factor 4.

Non-vacuity: $\nu=N(0,1)$, $\omega_n$ the coordinates of $N(0,1)^{\otimes\mathbb N}$, $P=0$,
$P_L=\mathrm{id}+1$, $\alpha=\gamma=a_1=a_3=v=C=1$, $L=0$, $\varepsilon=2$, $N\ge1$. This is the
standard lower bound $\varepsilon^{-2-\gamma/\alpha}$ for plain MC.

## 7. `beta_le_two_alpha`
**Rendering.** $\mu$ is a probability measure and $P_\ell\in L^2(\mu)$. Let
$Y_\ell=\mathrm{levelDiff}$, with $\kappa>0$ and $c>0$. Hypotheses:
- eventually $\kappa\,\mathbb E[Y_\ell^2]\le\mathrm{Var}(Y_\ell)$;
- eventually $\mathrm{Var}(Y_\ell)\le c_22^{-\beta\ell}$;
- frequently (infinitely often) $c2^{-\alpha\ell}\le|\mathbb E Y_\ell|$.

Conclusion: $\beta\le2\alpha$. The constants $\alpha,\beta,c_2$ are unconstrained reals.

**Assessment.** True. For infinitely many $\ell$:
$$c^24^{-\alpha\ell}\le(\mathbb EY_\ell)^2\le\mathbb EY_\ell^2\le c_22^{-\beta\ell}/\kappa.$$
- If $c_2\le0$ this is a contradiction.
- Otherwise $c^2\kappa/c_2\le2^{(2\alpha-\beta)\ell}$ for infinitely many $\ell$, which forces
  $\beta\le2\alpha$.

The "frequently" quantifier is enough, and the variance is genuine because $Y_\ell\in L^2$.

Non-vacuity (`rates.out`): $Y_\ell=2^{-\ell}(1+Z)$, i.e. $P_\ell=(2-2^{-\ell})(1+Z)$, with
$\kappa=1/2$, $c=c_2=1$, $\alpha=1$, $\beta=2$ (sharp). The hypotheses force $\kappa\le1$, which
is harmless. This is Giles' remark that $\beta\le2\alpha$ when $V_\ell$ is comparable to
$\mathbb E[Y_\ell^2]$.

## 8. `beta_le_two_alpha_of_bias`
**Rendering.** $P\in L^1$, $P_\ell\in L^2$, $\mathbb EP_\ell\to\mathbb EP$, $\kappa>0$, $a_1>0$.
The eventual $\kappa$-domination and variance bounds are as in 7, and frequently
$a_12^{-\alpha\ell}\le|\mathbb E(P_\ell-P)|$. Conclusion: $\beta\le2\alpha$.

**Assessment.** True. Telescoping with the limit hypothesis gives
$\mathbb EP-\mathbb EP_\ell=\sum_{k>\ell}\mathbb EY_k$. Suppose $\beta>2\alpha$.
- If $\beta>0$: $|\mathbb EY_k|\le\sqrt{c_2/\kappa}\,2^{-\beta k/2}$ eventually, so
  $|\text{bias}_\ell|=O(2^{-\beta\ell/2})=o(2^{-\alpha\ell})$, which contradicts "frequently".
- If $\beta\le0$: then $\alpha<0$, so $a_12^{-\alpha\ell}\to\infty$, which contradicts
  $\text{bias}\to0$.
- If $c_2\le0$: the variance is eventually $0$, so eventually $\mathbb EY_k=0$ and the bias is $0$,
  a contradiction.

Non-vacuity: $P=2(1+Z)$, $P_\ell=(2-2^{-\ell})(1+Z)$, $a_1=1$, $\alpha=1$, $\beta=2$,
$\kappa=1/2$. There is no junk value. This is the bias version of the same remark.

## 9. `mlmc_optimal_complexity_necessary`
**Rendering.** $\mu$ is a probability measure, $P\in L^1$ and $P_\ell\in L^1$. $Y_{\ell,n}$ is
the level-$\ell$ estimator with $n$ samples, in $L^2$ for $n>0$. For every positive $N(\cdot)$
the variables $\{Y_{\ell,N_\ell}\}_\ell$ are pairwise independent. Also, for $n>0$:
- $\mathbb E\,\mathrm{Cost}_{\ell,n}=nC_\ell$, with $\mathrm{Cost}_{\ell,n}$ integrable;
- $\mathrm{Var}(Y_{\ell,n})=V_\ell/n$;
- $\mathbb EY_{\ell,n}=\mathbb E\,\mathrm{levelDiff}\,P_\ell$.

For **every** $\ell$: $a_12^{-\alpha\ell}\le|\mathbb E(P_\ell-P)|$, $a_22^{-\beta\ell}\le V_\ell$
and $a_32^{\gamma\ell}\le C_\ell$, with $\alpha,a_1,a_2,a_3>0$ and $\gamma\ge0$.

Hypothesis `hopt`: there are $c_4$ and $\varepsilon_0>0$ such that for every
$\varepsilon\in(0,\varepsilon_0)$ there are $L$ and $N>0$ with
$\mathbb E[(\sum_{\ell\le L}Y_{\ell,N_\ell}-\mathbb EP)^2]<\varepsilon^2$ and
$\mathbb E\sum_{\ell\le L}\mathrm{Cost}_{\ell,N_\ell}\le c_4\varepsilon^{-2}$.

Conclusion: $\gamma<\beta$ and $\gamma/\alpha\le2$.

**Assessment.** True. The MSE equals $\sum_{\ell\le L}V_\ell/N_\ell+\text{bias}_L^2$ (pairwise
independence and telescoping of the means). Then:
- $a_12^{-\alpha L}<\varepsilon$, so $L(\varepsilon)\to\infty$.
- Cauchy-Schwarz gives
  $\big(\sum_{\ell\le L}\sqrt{V_\ell C_\ell}\big)^2\le\big(\sum V_\ell/N_\ell\big)\big(\sum N_\ell C_\ell\big)<c_4$.
  So $\sum_\ell2^{(\gamma-\beta)\ell/2}<\infty$, i.e. $\gamma<\beta$.
- $\text{cost}\ge N_LC_L\ge a_32^{\gamma L}>a_3(a_1/\varepsilon)^{\gamma/\alpha}$, so
  $\varepsilon^{-\gamma/\alpha}=O(\varepsilon^{-2})$, i.e. $\gamma/\alpha\le2$.

This uses the integrality $N_\ell\ge1$. There is no "frequently" quantifier; the lower bounds for
every $\ell$ are stronger hypotheses than "eventually" but standard for a necessity statement.

Non-vacuity (`rates.out`):
- $P\equiv1$, $P_\ell\equiv1-2^{-\ell}$;
- $Y_{\ell,n}=\mathbb E\,\mathrm{levelDiff}\,P_\ell+2^{-\ell}n^{-1/2}Z_\ell$ with $Z_\ell$
  i.i.d. $N(0,1)$;
- $\mathrm{Cost}_{\ell,n}\equiv n2^\ell$;
- $\alpha=1$, $\beta=2$, $\gamma=1$, all $a_i=1$.

`hopt` holds with $\text{cost}\cdot\varepsilon^2\approx23$. The same script shows
$\text{cost}\cdot\varepsilon^2$ growing when $\gamma=\beta$ or $\gamma>2\alpha$. Every variance
and integral involved is genuine. This is the standard necessary condition for $O(\varepsilon^{-2})$
MLMC: $\beta>\gamma$, and the finest level alone costs $\varepsilon^{-\gamma/\alpha}$.

## 10. `sqrt_mul_blockAvg`
**Rendering.** For $M>0$, $h\ge0$, $z$ and $k$:
$\sqrt{Mh}\,\mathrm{blockAvg}_M(z)_k=\sum_{i<M}\sqrt h\,z_{Mk+i}$.

**Assessment.** True, since $\sqrt{Mh}=\sqrt M\sqrt h$ and $\sqrt M\neq0$. The numerical error is
$7\cdot10^{-15}$ (`blockavg.out`). It also holds without either hypothesis: both sides are $0$
when $M=0$ or $h<0$. It is not vacuous. This identity says the coarse Brownian increment is the
sum of $M$ fine ones.

## 11. `emCoarseM_eq`
**Rendering.** For $M>0$: $P^c_\ell(z)=P^f_\ell(\mathrm{blockAvg}_Mz)$.

**Assessment.** True, since $M\cdot(h_0/M^{\ell+1})=h_0/M^\ell$ in $\mathbb R$ when $M\neq0$.
It fails for $M=0$, $\ell=0$, $h_0\ne0$, so `hM` is needed. Not vacuous.

## 12. `map_blockSum_gaussian`
**Rendering.** For $M>0$, the pushforward of $N(0,1)^{\otimes M}$ (written as `infinitePi` over
`Fin M`) under $y\mapsto(\sum_iy_i)/\sqrt M$ is $N(0,1)$.

**Assessment.** True: the sum of $M$ i.i.d. $N(0,1)$ variables is $N(0,M)$, and scaling gives
$N(0,1)$. It is false for $M=0$ (Dirac at 0), so `hM` is needed. This is the standard Gaussian
convolution fact.

## 13. `measurePreserving_blockAvg`
**Rendering.** For $M>0$, $\mathrm{blockAvg}_M:(\mathbb R^{\mathbb N},N(0,1)^{\otimes\mathbb N})\to(\mathbb R^{\mathbb N},N(0,1)^{\otimes\mathbb N})$
is measure-preserving, including measurability.

**Assessment.** True. Coordinate $k$ depends only on the disjoint block
$\{Mk,\dots,Mk+M-1\}$, so the coordinates are independent and each is $N(0,1)$ by 12.
Measurability holds because each coordinate is a finite sum of coordinates. Monte Carlo
(`blockavg.out`) gives mean $\approx0$, variance $\approx1$, fourth moment $\approx3$ and
correlation between coordinates $\approx0$ for $M=1,2,3,5$. It is not vacuous.

## 14. `integral_emCoarseM`
**Rendering.** Suppose $M>0$ and $P^f_\ell$ is a.e.-strongly measurable for
$N(0,1)^{\otimes\mathbb N}$. Then $\int P^c_\ell\,d\gamma^{\otimes\mathbb N}=\int P^f_\ell\,d\gamma^{\otimes\mathbb N}$,
where $\gamma^{\otimes\mathbb N}$ denotes $N(0,1)^{\otimes\mathbb N}$.

**Assessment.** True by 11 and 13: $\int g\circ T\,d\mu=\int g\,d(T_\#\mu)=\int g\,d\mu$, with
`integral_map` and the measurability hypothesis. If $g$ is not integrable, both sides are $0$, so
the identity holds in that case too. In the intended application $g\in L^2$. This is the
condition behind the telescoping identity (Giles 2008, (2.4)): the coarse estimator at level
$\ell+1$ has the same mean as the fine estimator at level $\ell$.

## 15. `em_mlmc_theorem1_M`
**Rendering.** The data are:
- $\mu$ a probability measure, $a,b:\mathbb R^2\to\mathbb R$, $h_0,S_0\in\mathbb R$, $M>0$,
  functionals $\Phi_\ell$, and $P\in L^1(N(0,1)^{\otimes\mathbb N})$;
- samples $\omega_{(\ell,n)}:\Omega\to\mathbb R^{\mathbb N}$, measure-preserving onto
  $N(0,1)^{\otimes\mathbb N}$ and mutually independent;
- $P^f_\ell$ measurable and in $L^2$;
- costs $\mathrm{cost}_{\ell,n}$ integrable with $\mathbb E\,\mathrm{cost}_{\ell,n}=C_\ell$;
- $\alpha,\beta,\gamma,c_1,c_2,c_3>0$ with $\min(\beta,\gamma)/2\le\alpha$.

For **every** $\ell$:
- (i) $|\int(P^f_\ell-P)|\le c_12^{-\alpha\ell}$;
- (iii) $\mathrm{Var}(\mathrm{fineCoarseDiff}_\ell)\le c_22^{-\beta\ell}$, where
  $\mathrm{fineCoarseDiff}_\ell=P^f_\ell-P^c_{\ell-1}$ and $P^c_{-1}:=0$;
- (iv) $C_\ell\le c_32^{\gamma\ell}$.

Conclusion: there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there are $L$ and
$N>0$ for which:
- the squared error of
  $\hat Y=\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}\mathrm{fineCoarseDiff}_\ell(\omega_{(\ell,n)})$
  about $\int P$ is integrable, with MSE $<\varepsilon^2$;
- $\mathbb E[\text{totalCost}]=\sum_{\ell\le L}N_\ell C_\ell\le c_4\,\mathrm{complexityBound}(\alpha,\beta,\gamma,\varepsilon)$.

**Assessment.** True. Every ingredient is genuine:
- $P^c_{\ell}=P^f_\ell\circ\mathrm{blockAvg}_M$ is measurable and in $L^2$ (11, 13);
- $\mathbb E\hat Y=\mathbb EP^f_L$ by 14 (telescoping);
- the variance is $\sum V_\ell/N_\ell$ by independence;
- the expected cost is $\sum N_\ell C_\ell$.

With these, the standard proof of Giles' Theorem 1 applies verbatim. A $C_\ell$ that may be
negative only lowers the cost. Allowing $M=1$ (no refinement) or $h_0<0$ does not break the
abstract statement.

Non-vacuity:
- geometric Brownian motion $a=rS$, $b=\sigma S$, $h_0=T=1$, $M=2$;
- $\Phi_\ell(\text{path})=\text{path}(2^\ell)$, $P\equiv S_0e^{r}$;
- $\omega_p$ the coordinates of the product space, $\mathrm{cost}_{\ell,n}\equiv2^\ell$;
- $\alpha=1$, $\beta=\gamma=1$.

There is no junk value: $\varepsilon<e^{-1}$, so $\log\varepsilon\ne0$, and $\alpha>0$. This is
Giles (2008), Theorem 1, for the Euler-Maruyama coupling with refinement factor $M$.
