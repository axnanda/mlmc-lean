# Blind read-back report: R45_digital

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round25/packet_R45_digital.lean` |
| declarations audited | 12 theorems (and the 9 definitions they use) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round25/work_R45_digital/` (`condexp_rate.py`, `zero_strike.py`, `weak_rate.py`, `split_rate.py`, `digital_shift.py`, each with a `.out` file; `Check1.lean`/`Check2.lean` with `.out`) |

I compiled `Check1.lean`, which uses `import MlmcLean` and `#check`/`#print`. It showed that every statement elaborates as the packet shows. In particular:
- `cdf (gaussianReal 0 1)` is the standard normal CDF $\Phi$.
- `deriv (fun S => σ*S) S = σ` (checked with `by simp`), so `milsteinStep` is the usual GBM Milstein step.
- In theorem 9(g), `((R:ℝ)*(R-1))⁻¹` is real subtraction, $(R(R-1))^{-1}$.

`#print axioms` on all 12 theorems lists only `propext`, `Classical.choice` and `Quot.sound`.

## Notation used below

These are GBM Milstein paths with $h_\ell = T/2^\ell$. One Milstein step is
$$S \mapsto S\bigl(1 + rh + \sigma\sqrt h\,z + \tfrac{\sigma^2 h}{2}(z^2-1)\bigr).$$

**Fine estimator.** $F_\ell(z) = \Phi\bigl((S^f(1+rh_\ell) - K)/(|\sigma S^f|\sqrt{h_\ell})\bigr)$. Here $S^f$ is the Milstein path after $2^\ell - 1$ steps driven by $z_0,\dots,z_{2^\ell-2}$. This is $P(\text{one Euler last step} > K \mid S^f)$.

**Coarse estimator.** $C_\ell(z) = \Phi\bigl((S^c(1+rh_\ell) + \sigma S^c\sqrt{h_{\ell+1}}\,z_{2^{\ell+1}-2} - K)/(|\sigma S^c|\sqrt{h_{\ell+1}})\bigr)$. Here $S^c$ is the coarse path after $2^\ell - 1$ steps of size $h_\ell$, driven by the pair averages $(z_{2k}+z_{2k+1})/\sqrt2$. The coarse last step uses the fine increment over its first half and integrates out its second half. This is the Giles (2008) Milstein / conditional-expectation coupling.

**Splitting estimators.** The "split" versions replace $\Phi(\cdot)$ by the average of $M$ indicators that use independent last-step normals $p_2(i)$. Fine and coarse share the same $p_2(i)$.

**Exact price.** $P_K = \int \mathbf 1\{s_0 e^{(r-\sigma^2/2)T+\sigma\sqrt T w} > K\}\,dN(0,1)(w)$, which is the undiscounted digital price $P(S_T>K)$.

**Junk value.** When $\sigma S = 0$ the CDF argument divides by 0, which Lean sets to 0, so the value is $\Phi(0) = 1/2$. This happens only on a null set: $s_0 \ne 0$, and each Milstein factor is a non-degenerate quadratic in a Gaussian (its leading coefficient is $\sigma^2h/2 \ne 0$). So no statement depends on it.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `gbm_digital_condExp_variance_rate_zero_strike` | theorem | true | no | no (the case itself is degenerate, see below) |
| 2 | `gbm_digital_condExp_variance_rate_all` | theorem | true | no | no |
| 3 | `gbm_digital_condExp_theorem1_all` | theorem | true | no | no |
| 4 | `gbm_digital_split_variance_rate_all` | theorem | true | no | no |
| 5 | `gbm_digital_split_weak_rate` | theorem | true | no | no |
| 6 | `gbm_digital_split_theorem1` | theorem | true | no | no |
| 7 | `digitalShift_measurePreserving` | theorem | true | no | no |
| 8 | `digitalShiftQMC_unbiased` | theorem | true | no | no |
| 9 | `digitalShift_replicates` | theorem | true | no | no |
| 10 | `uniformDigits_map_binaryValue` | theorem | true | no | no |
| 11 | `uniformDigits_map_binaryPoint` | theorem | true | no | no |
| 12 | `digitalShiftQMC_unbiased_cube` | theorem | true | no | no |

## Main points for a human auditor

- **No false, vacuous or junk-dependent statement found.** The only junk value is $\Phi(0)=1/2$ when $\sigma S=0$. It sits on a null set, and the hypotheses $s_0\ne0$, $\sigma\ne0$, $T>0$ are exactly what make it null. These hypotheses are needed: with $\sigma=0$, theorem 3 would fail.
- **Theorem 1 (zero strike, every real $q$) is true, but only because the case is degenerate.**
  - With $K=0$ the exact payoff is a.s. constant ($1$ if $s_0>0$, $0$ if $s_0<0$).
  - Once $h(\sigma^2-2r)<1$, every Milstein factor is positive, so the paths keep the sign of $s_0$. Then $E[d^2]\le 2e^{-a/h}$ for some $a>0$, which is smaller than any power of $h$.
  - `zero_strike.out` confirms this: for example $E[d^2]\approx 10^{-300}$ at $h = 2^{-11}$ when $r=0$, $\sigma=1$.
  - Read the "any $q$" rate as a feature of the trivial payoff, not of MLMC.
- **Rates are $\delta$-weakened versions of the sharp ones.**
  - Theorems 2 and 4 take $q<3/2$, the Giles–Debrabant–Rößler $O(h^{3/2-\delta})$ form. Numerically $E[d^2]/h^{3/2}$ is roughly constant (`condexp_rate.out`).
  - Theorem 5 takes $q<1$, against a weak error that is numerically $O(h)$ (`weak_rate.out`).
  - Theorem 4's term $h^{q-1/2}/M$ is at most $h^{1-\delta}/M$. The quantity behind it, $E[e]$, is numerically about $0.066\,h$ (`split_rate.out`).
  - None of this is a defect; the statements are slightly weaker than the sharp rates.
- **Theorems 3 and 6 are the Giles (2008, Thm 3.1) complexity bound** in the regime $\beta>\gamma=1$, $\alpha\ge1/2$, giving cost $O(\varepsilon^{-2})$.
  - The constant $c_4$ depends on $(r,\sigma,s_0,T,K)$ but not on $\varepsilon$.
  - The target is the undiscounted price $P(S_T>K)$.
  - The model allows $s_0<0$ and $\sigma<0$, which is more general than usual.
  - In theorem 6, $M_\ell=\lceil h_\ell^{-1/2}\rceil$ is correctly shared between the fine part at level $\ell$ and the coarse part of the level-$\ell$ difference.
  - I checked the telescoping identity $E[C_\ell]=E[F_\ell]$ analytically and numerically (`weak_rate.out`: $E[C_0]=F_0$ to 15 digits).
- **Digital-shift results 7–12 are standard and stated without unusual hypotheses.**
  - $\iota$ is arbitrary in 7–9.
  - Theorem 9 assumes `Measurable f` on top of `MemLp f 2`. This is slightly more than needed, and natural for the independence and pushforward-law clauses.
  - Theorem 12 holds for any digit arrays $x_k$, not only digital nets, which is correct for unbiasedness.

## Per-declaration sections

### 1. `gbm_digital_condExp_variance_rate_zero_strike`

**Rendering.** Let $r,\sigma,s_0,T,q\in\mathbb R$ with $s_0\ne0$, $\sigma\ne0$ and $T>0$, and let $q$ be arbitrary (it may be negative or very large). Write $d_\ell = F_{\ell+1}-C_\ell$ with $K=0$, as a function of $z\sim\bigotimes_{\mathbb N}N(0,1)$ (`stdNormalSeq`).

The claim: there is $C\ge0$, depending on $r,\sigma,s_0,T,q$, such that for every $\ell\in\mathbb N$:
- $d_\ell\in L^2$;
- $E[d_\ell^2]\le C\,(T/2^{\ell+1})^q$;
- $\operatorname{Var}(d_\ell)\le C\,(T/2^{\ell+1})^q$.

Here `Var` is Mathlib `variance`, which is $(\text{evariance}).\text{toReal}$, the usual variance for $L^2$ functions.

**Assessment.**
- **Truth: true.**
  - The functions are bounded in $[-1,1]$ and measurable, which gives $L^2$, and $\operatorname{Var}\le E[d^2]$.
  - The Milstein factor $\frac{\sigma^2h}{2}z^2+\sigma\sqrt h z+(1+rh-\frac{\sigma^2h}{2})$ has discriminant $\sigma^2h(\sigma^2h-2rh-1)$, which is negative once $h(\sigma^2-2r)<1$. From that level on the paths keep the sign of $s_0$.
  - Take $s_0>0$. Then $F=\Phi((1+rh)/(|\sigma|\sqrt h))$ and $C=\Phi((1+2rh)/(|\sigma|\sqrt h)\pm z')$. Both are within $O(e^{-c/h})$ of 1 in mean square: $E[(1-\Phi(b+Z))^2]\le\Phi(-b/\sqrt2)$. The case $s_0<0$ is symmetric.
  - The remaining finitely many levels have $|d|\le1$ and are absorbed into $C$, since $(T/2^{\ell+1})^q>0$.
  - `zero_strike.py` computes $E[d^2]$ exactly for the sign-preserving levels and shows superpolynomial decay.
- **Vacuity:** not vacuous; e.g. $r=0.05$, $\sigma=0.2$, $s_0=T=1$, $q=10$.
- **Junk values:** none beyond the null set where $\sigma S=0$.
- **Remark:** a strike-zero digital is a trivial payoff for GBM, so the unbounded rate reflects that triviality.
- **Standard fact:** the cond-exp MLMC level variance for a payoff that is exponentially smooth on the support. It is a degenerate special case of Giles (2008, Milstein, §4).

### 2. `gbm_digital_condExp_variance_rate_all`

**Rendering.** Same setting as theorem 1, but with an arbitrary strike $K$ and any real $q<3/2$. The claim: there is $C\ge0$ such that for all $\ell$:
- $F_{\ell+1}-C_\ell\in L^2(\text{stdNormalSeq})$;
- $E[(F_{\ell+1}-C_\ell)^2]\le C\,h_{\ell+1}^q$;
- $\operatorname{Var}(F_{\ell+1}-C_\ell)\le C\,h_{\ell+1}^q$.

**Assessment.**
- **Truth: true.** Write $h = h_{\ell+1}$.
  - The conditional means differ by $O(h)$: one Milstein step plus the strong order 1 of Milstein. The conditional standard deviations are $\asymp\sqrt h$.
  - So the CDF arguments differ by $O(\sqrt h)$. That difference matters only when $S$ is within $O(\sqrt h)$ of $K$, which has probability $O(\sqrt h)$.
  - Hence $E[d^2]=O(h^{3/2})$ up to logarithms, and every $q<3/2$ is covered.
  - Numerically (`condexp_rate.out`, two parameter sets including $s_0<0$, $K<0$), $E[d^2]/h^{1.5}$ stays around $0.004$ for one set and $0.02$ for the other over $\ell=0..7$, with log-slopes near 1.5.
- **Vacuity:** not vacuous.
- **Junk values:** none.
- **Hypotheses:** none unusual. $q<3/2$ is the $\delta$-weakened sharp rate.
- **Standard result:** Giles (2008) Milstein paper, digital option with conditional expectation, $\beta\approx3/2$. Proved as $O(h^{3/2-\delta})$ in Giles–Debrabant–Rößler.

### 3. `gbm_digital_condExp_theorem1_all`

**Rendering.** Let $r,\sigma$ be arbitrary, $s_0\ne0$, $\sigma\ne0$, $T>0$, and $K$ arbitrary. The claim: there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with all $N_\ell>0$ satisfying the following.

Take samples $x(\ell,n)$ i.i.d. from `stdNormalSeq`, via `infinitePi` over $\mathbb N\times\mathbb N$. Define
$$Y=\sum_{\ell=0}^{L}\frac1{N_\ell}\sum_{n<N_\ell}D_\ell(x(\ell,n)),\qquad D_0=F_0,\quad D_{\ell+1}=F_{\ell+1}-C_\ell.$$
Then:
- $(Y-P_K)^2$ is integrable;
- $E[(Y-P_K)^2]<\varepsilon^2$;
- $\sum_{\ell\le L}N_\ell 2^\ell\le c_4\varepsilon^{-2}$.

**Assessment.**
- **Truth: true.**
  - $E[C_\ell]=E[F_\ell]$: integrate out $z'$ to get $E\Phi(\alpha\pm Z)=\Phi(\alpha/\sqrt2)$, and pair averages are i.i.d. $N(0,1)$, independent of $z'$. So $E[Y]=E[F_L]$.
  - Independence across $(\ell,n)$ gives $\text{MSE}=(E F_L-P_K)^2+\sum V_\ell/N_\ell$.
  - The ingredients are $\beta=3/2-\delta>\gamma=1$ (theorem 2), $\alpha=1-\delta\ge1/2$ (theorem 5; numerically bias $\approx0.004\text{–}0.04\,h$), and cost $2^\ell$.
  - Giles' Theorem 3.1 with $\beta>\gamma$ then gives MSE $<\varepsilon^2$ at cost $O(\varepsilon^{-2})$. Strictness is achievable with slack.
  - $Y$ is bounded, so it is integrable.
- **Vacuity:** not vacuous.
- **Junk values:** none.
- **Notes:**
  - The target is the undiscounted digital.
  - $c_4$ depends on all model parameters but is uniform in $\varepsilon$.
  - The cost counts only $2^\ell$ per sample; the coarse cost is absorbed in $c_4$.
- **Standard result:** Giles (2008, Operations Research, Thm 3.1) applied to the Milstein / conditional-expectation digital estimator.

### 4. `gbm_digital_split_variance_rate_all`

**Rendering.** Same model as theorem 2, $K$ arbitrary, $q<3/2$. The claim: there is $C\ge0$ such that for all $\ell$ and all $M\ge1$:
- the difference $\mathrm{SF}_{M,\ell+1}-\mathrm{SC}_{M,\ell}$ is in $L^2$ under `stdNormalSeq ⊗ stdNormalSeq`;
- its second moment and its variance are at most $C\bigl(h^q+h^{q-1/2}/M\bigr)$, where $h=T/2^{\ell+1}$.

Here SF and SC are the $M$-sample split estimators. The fine one is $\frac1M\sum_{i<M}\mathbf 1\{S^f(1+rh)+\sigma S^f\sqrt h\,p_2(i)>K\}$. The coarse one uses the coarse path and the increment $\sqrt h\,p_1(2^{\ell+1}-2)+\sqrt h\,p_2(i)$ over the coarse step $2h$.

**Assessment.**
- **Truth: true.**
  - Conditional on $p_1$, the $M$ indicator differences are i.i.d. with mean $d$ (the cond-exp difference) and second moment $e$ (the probability that the fine and coarse finals straddle $K$).
  - Hence $E[\cdot^2]=E[d^2]+(E[e]-E[d^2])/M\le E[d^2]+E[e]/M$.
  - $E[d^2]=O(h^{q})$ by theorem 2's analysis. $E[e]=O(h^{1-\delta})$ because the final values differ by $O(h)$ and the law near $K$ has bounded density. Since $q-\tfrac12<1$, $E[e]/M\le Ch^{q-1/2}/M$.
  - Numerically (`split_rate.out`), $E[e]/h\approx0.06$. A direct MC at $\ell=3$ matches the formula for $M=1$ and $M=4$.
- **Vacuity:** not vacuous.
- **Junk values:** none. $M>0$ avoids $0/0$.
- **Hypotheses:** none unusual.
- **Standard result:** path splitting for digital options (Asmussen–Glynn; Giles, Acta Numerica 2015, digital options). Its variance is $O(h^{3/2}+h/M)$, here $\delta$-weakened.

### 5. `gbm_digital_split_weak_rate`

**Rendering.** For $s_0\ne0$, $\sigma\ne0$, $T>0$, any $K$ and any $q<1$: there is $C\ge0$ such that for all $\ell$ and all $M\ge1$:
- $E[\mathrm{SF}_{M,\ell}]=E[F_\ell]$;
- $|E[\mathrm{SF}_{M,\ell}]-P_K|\le C\,(T/2^\ell)^q$.

**Assessment.**
- **Truth: true.**
  - The first part is the tower property: $E[\mathbf 1\{m+sW>K\}]=\Phi((m-K)/|s|)$ for $W\sim N(0,1)$, off a null set.
  - The second part is the weak error of Milstein with a Gaussian last step for a digital payoff. It is $O(h)$ for this non-degenerate log-normal model, so every $q<1$ is covered, with $\ell=0$ and small $\ell$ absorbed into $C$.
  - `weak_rate.out` uses the exact conditional probability as a control variate and finds bias$/h$ of $0.039, 0.021, 0.012, 0.008, 0.006, 0.006, 0.005, 0.004$ for $\ell=0..7$.
- **Vacuity:** not vacuous.
- **Junk values:** none.
- **Hypotheses:** none unusual. $q<1$ is a $\delta$-weakened $O(h)$.
- **Standard result:** Milstein weak order 1 for a digital payoff (Bally–Talay type), plus unbiasedness of splitting.

### 6. `gbm_digital_split_theorem1`

**Rendering.** Same as theorem 3, with these changes:
- level $\ell$ uses split estimators with $M_\ell=\lceil (T/2^\ell)^{-1/2}\rceil$ for the fine part;
- the coarse part of the level-$(\ell+1)$ difference uses $M_{\ell+1}$, so both parts share it;
- samples are pairs $(p_1,p_2)$ from `stdNormalSeq ⊗ stdNormalSeq`, i.i.d. over $\mathbb N\times\mathbb N$;
- the cost bound is $\sum_{\ell\le L}N_\ell(2^\ell+M_\ell)\le c_4\varepsilon^{-2}$, with MSE $<\varepsilon^2$.

**Assessment.**
- **Truth: true.**
  - $M_\ell\ge1$.
  - $E[\mathrm{SC}_{M,\ell}]=E[\mathrm{SF}_{M',\ell}]=E[F_\ell]$ for any $M,M'$, so the sum telescopes to $E[F_L]$.
  - With $M_{\ell}\ge h_\ell^{-1/2}$, theorem 4 gives $V_\ell\le 2Ch_\ell^{q}$ with $q\in(1,3/2)$.
  - The cost per sample is $2^\ell+M_\ell\le 2^\ell(1+T^{-1/2})+1=O(2^\ell)$.
  - The weak rate is $\alpha\ge1/2$ by theorem 5. Giles' theorem with $\beta>\gamma$ then gives $O(\varepsilon^{-2})$.
- **Vacuity:** not vacuous.
- **Junk values:** none.
- **Standard result:** the MLMC complexity theorem (Giles 2008) for the splitting estimator.

### 7. `digitalShift_measurePreserving`

**Rendering.** Let $\iota$ be any type and $x\in\{0,1\}^\iota$. The map $u\mapsto x\oplus u$ (coordinatewise XOR) is measurable and preserves the uniform product measure $\bigotimes_\iota\mathrm{Unif}\{0,1\}$ (`infinitePi`).

**Assessment.**
- **Truth: true.** XOR with a fixed bit is a bijection of $\{0,1\}$, so it preserves the uniform measure in each coordinate. Product maps preserve `infinitePi`: the image is a probability measure that agrees on finite boxes, and `eq_infinitePi` gives uniqueness. This holds for every $\iota$, including uncountable ones.
- **Vacuity:** not vacuous.
- **Junk values:** none.
- **Standard fact:** invariance of Haar measure on $\mathbb Z_2^\iota$ under translation.

### 8. `digitalShiftQMC_unbiased`

**Rendering.** Let $U:\Omega\to\{0,1\}^\iota$ push $\mu$ to the uniform product measure. Let $x:\mathbb N\to\{0,1\}^\iota$ be arbitrary, $f$ integrable with respect to the uniform measure, and $N>0$. Then:
- (a) $\omega\mapsto x_k\oplus U(\omega)$ is measure-preserving for every $k$;
- (b) $\omega\mapsto \frac1N\sum_{k<N}f(x_k\oplus U(\omega))$ is $\mu$-integrable;
- (c) its integral equals $\int f$.

**Assessment.**
- **Truth: true.** Compose theorem 7 with $U$. Integrability and the change of variables need only a.e.-strong measurability of $f$, which comes with integrability.
- **Vacuity:** not vacuous.
- **Junk values:** $N>0$ is needed, since $N=0$ gives $0$.
- **Standard result:** unbiasedness of a randomly digitally shifted QMC rule (Dick–Pillichshammer).

### 9. `digitalShift_replicates`

**Rendering.** Let $\mu$ be a probability measure, $U_r$ ($r\in\mathbb N$) mutually independent maps each pushing $\mu$ to the uniform measure, $f$ measurable with $f\in L^2$, $N>0$ and $R>0$. Write $Q=$ `digitalShiftQMC f x N`. Then:
- (a) the $Q\circ U_r$ are mutually independent;
- (b) each $Q\circ U_r\in L^2(\mu)$;
- (c) each has law $Q_\#(\text{uniform})$;
- (d) each has mean $\int f$;
- (e) $E[\frac1R\sum_{r<R}Q\circ U_r]=\int f$;
- (f) $\operatorname{Var}(\frac1R\sum_r Q\circ U_r)=\operatorname{Var}_{\text{unif}}(Q)/R$;
- (g) if $R\ge2$: $E\bigl[\frac1{R(R-1)}\sum_r(Q_r-\bar Q)^2\bigr]=\operatorname{Var}(Q)/R$, with real $R-1$.

**Assessment.**
- **Truth: true.**
  - (a): measurable functions of independent variables are independent.
  - (b) and (c): measure preservation, and $Q$ is a finite sum of $L^2$ functions composed with measure-preserving maps.
  - (f) and (g): the i.i.d. variance of the mean and the unbiased sample variance.
  - `digital_shift.out` checks (e)–(g) exactly by enumeration over $\iota=\mathrm{Fin}\,3$ with $N\le3$ and $R\le3$.
- **Vacuity:** not vacuous.
- **Junk values:** none ($R\ge2$ guards (g)).
- **Hypotheses:** `Measurable f` is slightly stronger than a.e.-measurability, but natural for (a) and (c).
- **Standard result:** estimating the error of randomized QMC by independent replicates (Owen; L'Ecuyer–Lemieux).

### 10. `uniformDigits_map_binaryValue`

**Rendering.** The pushforward of i.i.d. fair bits $(u_k)$ under $u\mapsto\sum_k u_k 2^{-(k+1)}$ (a `tsum`, always summable) equals Lebesgue measure restricted to $[0,1]$.

**Assessment.**
- **Truth: true.** The truncated sums are uniform on the dyadic grid (checked exactly in `digital_shift.out`). The map is measurable as a pointwise limit of measurable partial sums. The two measures agree on dyadic intervals, which form a π-system generating the Borel sets of $[0,1]$. Dyadic rationals with two expansions form a null set.
- **Vacuity:** not applicable (no hypotheses).
- **Junk values:** none; the series converges.
- **Standard fact:** Steinhaus / Borel: random binary digits give the uniform distribution.

### 11. `uniformDigits_map_binaryPoint`

**Rendering.** For a finite type $\delta$, the pushforward of i.i.d. fair bits indexed by $\delta\times\mathbb N$ under $u\mapsto(j\mapsto\sum_k u(j,k)2^{-(k+1)})$ equals Lebesgue measure on $\mathbb R^\delta$ restricted to $[0,1]^\delta$.

**Assessment.**
- **Truth: true.** Currying turns the product over $\delta\times\mathbb N$ into a product over $\delta$ of products over $\mathbb N$. Apply theorem 10 in each coordinate, then use `Measure.pi` of the restrictions. The empty case $\delta=\emptyset$ is also fine: both sides are a Dirac mass on the one point.
- **Vacuity:** not applicable.
- **Junk values:** none.
- **Standard fact:** independent uniform coordinates give the uniform distribution on the cube.

### 12. `digitalShiftQMC_unbiased_cube`

**Rendering.** Let $\delta$ be a finite type and $U$ a uniformly distributed digit array on $\delta\times\mathbb N$. Let $x_k$ be arbitrary digit arrays, $g$ integrable on $[0,1]^\delta$, and $N>0$. Then:
- (a) each randomly shifted point $\omega\mapsto\text{binaryPoint}(x_k\oplus U(\omega))$ pushes $\mu$ to Lebesgue measure on $[0,1]^\delta$;
- (b) the QMC average $\frac1N\sum_{k<N}g(\cdot)$ is integrable;
- (c) its mean equals $\int_{[0,1]^\delta}g$.

**Assessment.**
- **Truth: true.** Compose theorems 7 and 11 with $U$, then change variables. This needs only a.e.-strong measurability of $g$ on the cube.
- **Vacuity:** not vacuous.
- **Junk values:** none. $N>0$ is needed.
- **Standard result:** a random digital shift in base 2 makes every point uniform, so the shifted QMC rule is unbiased (Dick–Pillichshammer, *Digital Nets and Sequences*).
