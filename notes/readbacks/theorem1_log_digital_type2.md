# Blind read-back report: R51 (Theorem 1 with log rates, GBM digital, type-2 for ℝ × ℝ)

| field | value |
|---|---|
| date | 2026-10-09 |
| packet | `readback/round27/packet_R51_t1l_extras.lean` |
| declarations audited | 10 theorems (no helper lemmas appear in the packet; 19 appended definitions read) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round27/work_R51_t1l_extras/` (`core_logrates.py/.out`, `gbm_digital_mc.py/.out`, `type2_maxnorm.py/.out`, `level0_delta.py/.out`; Lean scratch files `Packet.lean/.out`, `Print.lean/.out`, `Level0.lean/.out`) |

Method note: the packet uses `HasType2` but does not include its definition. I got it with `#print MLMC.HasType2` in a scratch file that imports `MlmcLean` (`Print.out`); I opened no repository source. The scratch copy of all 10 statements (`Packet.lean`) elaborates with `-DautoImplicit=false`. `Level0.lean` proves the identity and the variance claim of #10 by `simp` unfolding, and it compiles without errors.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `mlmc_complexity_core_logRates` | theorem | true | no | no |
| 2 | `giles_theorem1_logRates` | theorem | true | no | no |
| 3 | `giles_theorem1_fineCoarse_logRates` | theorem | true | no | no |
| 4 | `gbm_em_digital_weak_endpoint` | theorem | true | no | no |
| 5 | `gbm_em_digital_theorem1_log` | theorem | true | no | no |
| 6 | `two_le_sq_of_hasType2_prod` | theorem | true | no | no |
| 7 | `not_hasType2_prod_of_lt_sqrt_two` | theorem | true | no | no |
| 8 | `hasType2_prod_iff` | theorem | true | no | no |
| 9 | `isLeast_hasType2_prod` | theorem | true | no | no |
| 10 | `gbm_digital_condExp_delta_level_zero` | theorem | true (by unfolding definitions) | no | no (it is a definitional identity; for degenerate parameters both sides contain the same `x/0` or `√(T<0)` junk) |

## Main points for a human auditor

- **Quantifier order is correct everywhere.** In #1–#3 and #5, $c_4$ is chosen before $\varepsilon$, and only $L$ and $N$ depend on $\varepsilon$. In #4, $C$ depends only on $(r,\sigma,T)$ and is uniform in $s_0$, $K$ and $\ell$. This uniformity is a strong claim, but it is true (scaling plus the bounded density of $\log X_T$; see #4).
- **No log or rpow junk.** Every `Real.log` is $|\log\varepsilon|$ with $\varepsilon\in(0,e^{-1})$, so $|\log\varepsilon|>1$. Every rpow has a positive base: $\varepsilon$, $L+1\ge1$, $\ell+1\ge1$ or $2$. Every log exponent is $\ge0$. The square roots in #4 have positive arguments because $T>0$.
- **No junk integrals or variances.** Each mean-square-error integral comes with an explicit `Integrable` conjunct. The costs are finite sums of integrable functions. The variances in the hypotheses are taken of $L^2$ functions. The integrals in #4(b) are of bounded measurable indicators.
- **`min β γ / 2 ≤ α` together with `β < γ` is just $\beta\le2\alpha$.** $\beta$ may be negative; the claim stays true (checked numerically for $\beta=-1$ and $\beta=-3$). The condition is necessary: if $\beta>2\alpha$, the cost of a single sample on the finest level already exceeds the bound.
- **The log exponent $\max(b+a(\gamma-\beta)/\alpha,\ a\gamma/\alpha)$ is valid but not always sharp.** The second entry is only needed when $\beta=2\alpha$.
- **#4 and #5 are weaker than the standard results, though true.** #4 bounds the weak error at the strong-type scale $\sqrt{h(\ell+1)}$, while the true weak order for this digital option under EM is $h$. As a result, #5 proves $\varepsilon^{-3}|\log\varepsilon|$ (from $\alpha=\beta=a=b=\tfrac12$, $\gamma=1$), not Giles' $\varepsilon^{-5/2}$ (which uses $\alpha=1$, $\beta=\tfrac12$). The cost model in #5 is $\sum N_\ell 2^\ell$, with the coarse-path steps absorbed into the constant.
- **The type-2 constant is the definition-specific one.** `HasType2.{u} E τ` is defined with independent, mean-zero $L^2$ families and $\tau^2$, so its sign does not matter. That is why #8 has $|\tau|$ and #9 restricts to $\tau\ge0$. The optimal constant $\sqrt2$ for $(\mathbb R^2,\|\cdot\|_\infty)$ is correct.
- **#10 has no hypotheses at all.** It is a definitional computation, and the level-0 term is a constant, so its variance is 0. For $s_0\ne0$, $\sigma\ne0$, $T>0$ the constant equals $\partial_{s_0}P(S_1>K)$ for one Gaussian step (checked numerically). For $\sigma s_0=0$ or $T\le0$ it is a junk number, but the statement does not claim anything about its meaning.

---

## 1. `mlmc_complexity_core_logRates`

**Rendering.** Let $\alpha,\beta,\gamma,a,b,c_1,c_2,c_3\in\mathbb R$ with $\alpha>0$, $\gamma>0$, $\beta<\gamma$, $\min(\beta,\gamma)/2\le\alpha$ (that is, $\beta\le2\alpha$), $a,b\ge0$ and $c_1,c_2,c_3>0$. Then there is a $c_4>0$ such that for every real $\varepsilon$ with $0<\varepsilon<e^{-1}$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with all $N_\ell\ge1$ such that

$$\big(c_1(L+1)^a2^{-\alpha L}\big)^2+\sum_{\ell=0}^{L}\frac{c_2(\ell+1)^b2^{-\beta\ell}}{N_\ell}<\varepsilon^2,$$

$$\sum_{\ell=0}^{L}N_\ell\,c_3 2^{\gamma\ell}\le c_4\,\varepsilon^{-2-(\gamma-\beta)/\alpha}\,|\log\varepsilon|^{\max(b+a(\gamma-\beta)/\alpha,\ a\gamma/\alpha)}.$$

All powers with real exponents are `Real.rpow`; $\varepsilon^2$ is a natural-number power. $c_4$ depends only on the eight parameters.

**Assessment.**
- **Truth: true.** Choose the least $L$ with $c_1(L+1)^a2^{-\alpha L}\le\varepsilon/2$. Then $L\le C(1+|\log\varepsilon|)\le C'|\log\varepsilon|$ and $2^L\le C\varepsilon^{-1/\alpha}|\log\varepsilon|^{a/\alpha}$. Take $N_\ell=\lceil 4\varepsilon^{-2}\sqrt{V_\ell/C_\ell}\,S\rceil$ with $S=\sum_k\sqrt{V_kC_k}$, so the variance sum is at most $\varepsilon^2/4$. The cost is at most $4\varepsilon^{-2}S^2+\sum C_\ell$. Since $\gamma>\beta$, $S^2\le C(L+1)^b2^{(\gamma-\beta)L}$, which gives $\varepsilon^{-2-(\gamma-\beta)/\alpha}|\log\varepsilon|^{b+a(\gamma-\beta)/\alpha}$. The ceiling term satisfies $\sum C_\ell\le C2^{\gamma L}\le C\varepsilon^{-\gamma/\alpha}|\log\varepsilon|^{a\gamma/\alpha}$, and $\varepsilon^{-\gamma/\alpha}\le\varepsilon^{-2-(\gamma-\beta)/\alpha}$ exactly when $\beta\le2\alpha$. The max in the log exponent covers both terms because $|\log\varepsilon|>1$.
- **Numerical check** (`core_logrates.py`). I tried 7 parameter sets, including $\beta<0$ and $\beta=2\alpha$, with $\varepsilon$ from $0.36$ down to $10^{-40}$. MSE$/\varepsilon^2\le0.5$ throughout, and cost/bound stays bounded (it decreases or plateaus as $\varepsilon\to0$).
- **Vacuity: not vacuous.** For example $\alpha=1$, $\beta=1$, $\gamma=2$, $a=b=0$, $c_i=1$.
- **Junk values: none.** All rpow bases are positive, and $|\log\varepsilon|>1$.
- **Hypotheses.** `min β γ` is redundant given $\beta<\gamma$, but harmless. $\beta$ may be negative. Only the case $\beta<\gamma$ of Giles' theorem is covered. The log exponent is valid but not sharp when $\beta<2\alpha$.

**Standard result.** The deterministic core of Giles (2008), Theorem 3.1, case $\beta<\gamma$ ($\varepsilon^{-2-(\gamma-\beta)/\alpha}$), with polylogarithmic factors in the bias and variance rates.

## 2. `giles_theorem1_logRates`

**Rendering.** Let $(\Omega,\mu)$ be a probability space. Take real functions $P$, $P_\ell$, $Y_{\ell,n}$, $\mathrm{Cost}_{\ell,n}$ and real sequences $V,C$, with the same parameter conditions as #1. Assume:
- $P$ and every $P_\ell$ are integrable;
- $Y_{\ell,n}\in L^2$ for $n>0$;
- for every $N$ with all $N_\ell>0$, the family $(Y_{i,N_i})_i$ is pairwise independent;
- $\mathrm{Cost}_{\ell,n}$ is integrable with $E[\mathrm{Cost}_{\ell,n}]=nC_\ell$ for $n>0$;
- $|E[P_\ell-P]|\le c_1(\ell+1)^a2^{-\alpha\ell}$;
- $E[Y_{0,n}]=E[P_0]$ and $E[Y_{\ell+1,n}]=E[P_{\ell+1}-P_\ell]$ for $n>0$;
- $\operatorname{Var}(Y_{\ell,n})=V_\ell/n$ for $n>0$;
- $V_\ell\le c_2(\ell+1)^b2^{-\beta\ell}$ and $C_\ell\le c_3 2^{\gamma\ell}$.

Then there is a $c_4>0$ such that for all $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N>0$ with:
- $(\sum_{\ell\le L}Y_{\ell,N_\ell}-E[P])^2$ integrable;
- its mean $<\varepsilon^2$;
- $E[\sum_{\ell\le L}\mathrm{Cost}_{\ell,N_\ell}]\le c_4\varepsilon^{-2-(\gamma-\beta)/\alpha}|\log\varepsilon|^{\max(\cdots)}$.

**Assessment.**
- **Truth: true.** The bias telescopes to $E[P_L]-E[P]$. Pairwise independence of $L^2$ variables gives $\operatorname{Var}(\sum Y)=\sum V_\ell/N_\ell$, so MSE $\le$ (bias bound)$^2+\sum c_2(\ell+1)^b2^{-\beta\ell}/N_\ell$. The cost is $\sum N_\ell C_\ell\le\sum N_\ell c_32^{\gamma\ell}$. Then apply #1.
- **Vacuity: not vacuous.** All functions $0$ and $V=C=0$ satisfy every hypothesis. So does the genuine sample-mean model on a product space.
- **Junk values: none.** The variance is taken of $L^2$ functions, the conclusion asserts integrability of the squared error, and the cost integral is of a finite sum of integrable functions.
- **Hypotheses.** Independence is required for every admissible $N$; this is natural, since $N$ is chosen after the hypotheses. Pairwise independence is weaker than mutual, so that is good. $V_\ell\ge0$ follows automatically from the variance identity. Nothing suspicious.

**Standard result.** Giles (2008), Theorem 3.1 (probabilistic MLMC complexity), case $\beta<\gamma$, with log-factor rates.

## 3. `giles_theorem1_fineCoarse_logRates`

**Rendering.** Let $\mu$ be a probability measure on $\Omega$ and $\nu$ a measure on $\Omega_0$. The samples $\omega_{(\ell,n)}:\Omega\to\Omega_0$ each push $\mu$ to $\nu$ (so $\nu$ is a probability measure) and are mutually independent (`iIndepFun`). Assume:
- $P$ is $\nu$-integrable;
- $P^f_\ell$ and $P^c_\ell$ are measurable and in $L^2(\nu)$;
- $\int P^f_\ell\,d\nu=\int P^c_\ell\,d\nu$;
- $\mathrm{cost}_{\ell,n}$ is integrable with mean $C_\ell$;
- $|\int(P^f_\ell-P)\,d\nu|\le c_1(\ell+1)^a2^{-\alpha\ell}$;
- $\operatorname{Var}_\nu(D_\ell)\le c_2(\ell+1)^b2^{-\beta\ell}$, where $D_0=P^f_0$ and $D_{\ell+1}=P^f_{\ell+1}-P^c_\ell$;
- $C_\ell\le c_32^{\gamma\ell}$.

The parameter conditions are as in #1. Then there is a $c_4>0$ such that for all $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N>0$ such that the estimator $\widehat Y=\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}D_\ell(\omega_{(\ell,n)})$ satisfies:
- $(\widehat Y-\int P\,d\nu)^2$ is integrable;
- $E(\widehat Y-\int P\,d\nu)^2<\varepsilon^2$;
- $E[\sum_{\ell\le L}\sum_{n<N_\ell}\mathrm{cost}_{\ell,n}]\le c_4\varepsilon^{-2-(\gamma-\beta)/\alpha}|\log\varepsilon|^{\max(\cdots)}$.

**Assessment.**
- **Truth: true.** By $\int P^c_\ell=\int P^f_\ell$ the means telescope to $\int P^f_L\,d\nu$. Mutual independence and measure preservation give $\operatorname{Var}(\text{block}_\ell)=\operatorname{Var}_\nu(D_\ell)/N_\ell$ and independence across levels (disjoint index sets). The cost has mean $\sum N_\ell C_\ell$. Then apply #1.
- **Vacuity: not vacuous.** Take $\Omega_0=\mathbb R$ with $\nu=N(0,1)$, $\Omega=(\mathbb N^2\to\mathbb R)$ with the product measure, coordinate projections as samples, and all functions $0$.
- **Junk values: none.** The variance is of an $L^2$ function, the bias integrals are of integrable functions, and integrability of the squared error is asserted.
- **Hypotheses.** $\nu$ is not assumed to be a probability measure, but this follows from `MeasurePreserving`. The standard hypotheses (eq. (2.4)-type consistency $E P^c_\ell=E P^f_\ell$) are present. Nothing suspicious.

**Standard result.** Giles (2008), Theorem 3.1, for the standard fine/coarse MLMC estimator with i.i.d. samples, with log-factor rates.

## 4. `gbm_em_digital_weak_endpoint`

**Rendering.** Let $r,\sigma\in\mathbb R$ with $\sigma\ne0$ and $T>0$. Under `stdNormalSeq` the $z_i$ are i.i.d. $N(0,1)$. Write $h=T/2^\ell$ and define:
- $X=s_0\exp((r-\sigma^2/2)T+\sigma\sqrt h\sum_{i<2^\ell}z_i)$, the exact GBM at time $T$ driven by the same increments;
- $Y=s_0\prod_{i<2^\ell}(1+rh+\sigma\sqrt h z_i)$, the Euler–Maruyama endpoint (`emPath` with drift $rS$ and volatility $\sigma S$).

Then there is a $C\ge0$, depending only on $(r,\sigma,T)$, such that for all $s_0,K\in\mathbb R$ and all $\ell\in\mathbb N$:
- (a) $P\big(\mathbf 1\{X>K\}\ne\mathbf 1\{Y>K\}\big)\le C\sqrt{h(\ell+1)}$;
- (b) $\big|E\,\mathbf 1\{Y>K\}-\int\mathbf 1\{s_0e^{(r-\sigma^2/2)T+\sigma\sqrt T w}>K\}\,dN(0,1)(w)\big|\le C\sqrt{h(\ell+1)}$.

**Assessment.**
- **Truth: true.**
  - *Scaling.* $X=s_0X_1$ and $Y=s_0Y_1$. For $s_0>0$ the event in (a) is $\{K/s_0\text{ lies between }X_1\text{ and }Y_1\}$. For $s_0<0$ it is the same event up to null boundary events. For $s_0=0$ it is empty.
  - *Splitting the event.* $\log X_1\sim N((r-\sigma^2/2)T,\sigma^2T)$ has density at most $(|\sigma|\sqrt{2\pi T})^{-1}$; this is where $\sigma\ne0$ and $T>0$ are needed. So
  $$P(\text{differ})\le P(|\log X_1-\log k|\le\delta)+P(|\log Y_1-\log X_1|>\delta)+P(Y_1\le0)\le C\delta+\cdots,$$
  uniformly in $k$.
  - *The log-error term.* $\log Y_1-\log X_1=-\tfrac{\sigma^2h}{2}\sum(z_i^2-1)+O_p(h)$ concentrates at scale $\sqrt h$ with sub-exponential tails. Taking $\delta\asymp\sqrt{h\log(1/h)}\lesssim\sqrt{h(\ell+1)}$ (with a $T$-dependent constant) makes the tail at most $C\sqrt h$.
  - *Remaining terms.* $P(Y_1\le0)\le 2^\ell\Phi(-(1+rh)/(|\sigma|\sqrt h))$ is negligible. The finitely many small $\ell$ are absorbed into $C$, because the probability is at most $1$.
  - *Part (b).* Under the product measure, $\sqrt h\sum z_i\sim N(0,T)$, so the second integral is $E\,\mathbf 1\{X>K\}$. Then (b) follows from $|E f-E g|\le P(f\ne g)$ for indicators.
  - *Necessity of $\sigma\ne0$.* For $\sigma=0$ the claim is false: with $K$ between $s_0e^{rT}$ and $s_0(1+rh)^{2^\ell}$ the probability is $1$.
- **Numerical check** (`gbm_digital_mc.py`, exact sup over $K$ of the empirical coverage). For $(r,\sigma,T)=(0.05,0.2,1)$, $\ell\le8$, the ratio $\sup_K P/\sqrt{h(\ell+1)}$ stays between $0.022$ and $0.041$. For $(-0.5,1,2)$ it decreases from $0.35$ to $0.10$. For $s_0=-1$ it behaves the same way.
- **Vacuity: not vacuous.** For example $\sigma=0.2$, $T=1$.
- **Junk values: none.** The measure is a probability measure. The integrands are bounded measurable indicators: `emPath` is a finite measurable composition of coordinates. If the EM integral were junk $0$, (b) would fail, so the claim depends on the genuine value.
- **Hypotheses.** The constant is uniform in $s_0$ and $K$, which is strong but valid. The rate $\sqrt{h(\ell+1)}$ (that is, $\sqrt{h\log(1/h)}$ up to $T$) is weaker than the true orders: about $\sqrt h$ for (a) and $h$ for the weak error (b).

**Standard result.** The digital-option coupling and weak-error estimate for Euler–Maruyama on GBM, in the spirit of Giles (2008) §5 and Avikainen-type bounds. (b) is a deliberately weak form of the Bally–Talay weak error.

## 5. `gbm_em_digital_theorem1_log`

**Rendering.** Let $r,\sigma,s_0,K\in\mathbb R$ with $\sigma\ne0$ and $T>0$. Then there is a $c_4>0$ such that for all $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N>0$ with the following property. Draw independent $N(0,1)$ sequences $x_{(\ell,n)}$ (`infinitePi` over $\mathbb N\times\mathbb N$ of `stdNormalSeq`) and set:
- $D_0(z)=\mathbf 1\{Y^{(0)}(z)>K\}$;
- $D_{\ell+1}(z)=\mathbf 1\{Y^{(\ell+1)}(z)>K\}-\mathbf 1\{Y^{(\ell)}(\mathrm{pairAvg}\,z)>K\}$, where $\mathrm{pairAvg}\,z_k=(z_{2k}+z_{2k+1})/\sqrt2$ is the correct Brownian coupling for the coarse path.

The estimator $\widehat Y=\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}D_\ell(x_{(\ell,n)})$ then satisfies:
- $(\widehat Y-P(S_T>K))^2$ is integrable, where $P(S_T>K)$ is written as the Gaussian integral in the statement;
- $E(\widehat Y-P(S_T>K))^2<\varepsilon^2$;
- $\sum_{\ell\le L}N_\ell2^\ell\le c_4\varepsilon^{-3}|\log\varepsilon|$.

**Assessment.**
- **Truth: true.** Apply #3/#1 with $\alpha=\beta=a=b=\tfrac12$, $\gamma=1$, $c_3=1$.
  - Bias: by #4(b), $\le C\sqrt T(\ell+1)^{1/2}2^{-\ell/2}$.
  - Variance: $\operatorname{Var}D_{\ell+1}\le P(\text{fine}\ne\text{exact})+P(\text{coarse}\ne\text{exact})$, because $\text{gbmExact}_\ell(\mathrm{pairAvg}\,z)=\text{gbmExact}_{\ell+1}(z)$ and pairAvg preserves the measure. This is $\lesssim(\ell+1)^{1/2}2^{-\ell/2}$ by #4(a).
  - The consistency condition $E P^c_\ell=E P^f_\ell$ holds because pairAvg preserves the measure.
  - Exponents: $-2-(1-\tfrac12)/\tfrac12=-3$ and $\max(\tfrac12+\tfrac12,\ 1)=1$.
- **Vacuity: not vacuous** (any $\sigma\ne0$, $T>0$).
- **Junk values: none.** Integrability is asserted, and the target is the genuine $P(S_T>K)$. Degenerate $s_0=0$ makes everything constant (MSE $0$), which is still a correct instance.
- **Hypotheses.** No restriction on $s_0$ or $K$ is needed, because #4 is uniform. The cost $\sum N_\ell2^\ell$ counts only fine steps (the coarse steps are a constant factor). The result $\varepsilon^{-3}|\log\varepsilon|$ is weaker than Giles' standard $\varepsilon^{-5/2}$ for EM digital options, which uses weak order 1.

**Standard result.** The MLMC complexity for a digital option on GBM with Euler–Maruyama (Giles 2008 §5), in the weak-rate form $\alpha=\beta=\tfrac12$ with log factors.

## 6. `two_le_sq_of_hasType2_prod`

**Rendering.** `HasType2.{u} E τ` (from `#print`) means the following. For every probability space $(\Omega,\mu)$ with $\Omega$ in universe $u$, every $n$, and every independent family $X_1,\dots,X_n:\Omega\to E$ with each $X_i\in L^2$ and $\int X_i=0$:
$$\int\Big\|\sum X_i\Big\|^2d\mu\le\tau^2\sum\int\|X_i\|^2d\mu.$$
The theorem says: if $\mathbb R\times\mathbb R$ with the sup norm $\max(|x|,|y|)$ has this property with $\tau$, then $2\le\tau^2$.

**Assessment.**
- **Truth: true.** Take two independent Rademacher signs $\epsilon_1,\epsilon_2$ on $\mathrm{ULift}(\mathrm{Bool}^2)$, which works in any universe. Set $X_1=\epsilon_1(1,1)$ and $X_2=\epsilon_2(1,-1)$. Then $\|X_1+X_2\|_\infty=2$ surely, so $4\le2\tau^2$. `type2_maxnorm.py` gives the exact ratio $2$.
- **Vacuity: not vacuous**, since $\tau=\sqrt2$ satisfies the hypothesis by #8.
- **Junk values: none.** The $L^2$ hypotheses make all integrals genuine.

**Standard result.** The lower bound for the type-2 constant of $\ell^\infty_2$.

## 7. `not_hasType2_prod_of_lt_sqrt_two`

**Rendering.** If $|\tau|<\sqrt2$, then $\mathbb R\times\mathbb R$ (sup norm) does not have type 2 with constant $\tau$ in the sense above.

**Assessment.**
- **Truth: true.** $|\tau|<\sqrt2$ gives $\tau^2<2$, which contradicts #6.
- **Vacuity: not vacuous** (e.g. $\tau=1$).
- **Junk values: none.**

**Standard result.** Contrapositive of #6.

## 8. `hasType2_prod_iff`

**Rendering.** $\mathbb R\times\mathbb R$ (sup norm) has type 2 with constant $\tau$ if and only if $\sqrt2\le|\tau|$.

**Assessment.**
- **Truth: true.** The forward direction is #6. For the converse:
  - $\|v\|_\infty^2\le v_1^2+v_2^2$.
  - Components of independent mean-zero $L^2$ vectors are independent mean-zero, so the cross terms vanish and $E\|\sum X_i\|_2^2=\sum E\|X_i\|_2^2$.
  - $\sum E\|X_i\|_2^2\le2\sum E\|X_i\|_\infty^2\le\tau^2\sum E\|X_i\|_\infty^2$.

  The random discrete test in `type2_maxnorm.py` (3000 families) found a maximum ratio of $1.74$, which is at most $2$.
- **Vacuity: not vacuous.**
- **Junk values: none.** The absolute value $|\tau|$ is needed because the definition uses $\tau^2$.

**Standard result.** The type-2 constant of $\ell^\infty_2$ (for this definition, via independent mean-zero sums) equals $\sqrt2$.

## 9. `isLeast_hasType2_prod`

**Rendering.** $\sqrt2$ is the least element of $\{\tau\ge0:\ \mathbb R\times\mathbb R\text{ has type 2 with constant }\tau\}$.

**Assessment.**
- **Truth: true.** $\sqrt2$ is in the set by #8. Any $\tau\ge0$ in the set has $\tau=|\tau|\ge\sqrt2$ by #8.
- **Vacuity: not vacuous** (the set is nonempty).
- **Junk values: none.**

**Standard result.** The optimal type-2 constant of $(\mathbb R^2,\|\cdot\|_\infty)$ is $\sqrt2$.

## 10. `gbm_digital_condExp_delta_level_zero`

**Rendering.** For all real $r,\sigma,s_0,K,T$, with no hypotheses, the level-0 term $D_0=\texttt{gbmDigitalCondFineDelta}(\cdot)_0$ of the conditional-expectation digital-delta estimator satisfies three things:
- (i) For every $z$,
$$D_0(z)=\varphi\!\Big(\frac{s_0+rs_0T-K}{|\sigma s_0|\sqrt T}\Big)\cdot\frac{K}{s_0\,|\sigma s_0|\sqrt T},$$
where $\varphi$ is the standard normal pdf.
- (ii) $D_0\in L^2(\texttt{stdNormalSeq})$.
- (iii) $\operatorname{Var}(D_0)=0$.

**Assessment.**
- **Truth: true.** At $\ell=0$ we have $2^0-1=0$ and $T/2^0=T$. So `milsteinPath … 0 = s₀`, the conditional mean is $s_0+rs_0T$ and the conditional standard deviation is $|\sigma s_0|\sqrt T$, independent of $z$. Then (i) is a definitional unfolding. I confirmed in Lean that `simp [fineCoarseDiff, gbmDigitalCondFineDelta, gbmCondMeanFine, gbmCondStdFine, milsteinPath]` closes it. (ii) and (iii) hold because $D_0$ is a constant function; (iii) is also confirmed in `Level0.lean`.
- **Meaning check** (`level0_delta.py`). For $s_0\ne0$, $\sigma\ne0$, $T>0$ the constant equals $\partial_{s_0}P(S_1>K)$ with $S_1\sim N(s_0(1+rT),\sigma^2s_0^2T)$, for both signs of $s_0$ and $\sigma$ (agreement to 12 digits).
- **Vacuity: not vacuous** (there are no hypotheses).
- **Junk values.** For $\sigma s_0=0$ or $T\le0$ both sides contain the same $x/0=0$ or $\sqrt{T}=0$ junk. The identity still holds by definition, and (ii) and (iii) hold for any constant. So the theorem is not true *because of* junk, but in those cases its right-hand side is not a delta.
- **Hypotheses.** None. The statement is a book-keeping lemma, not a deep fact.

**Standard result.** In Giles' conditional-expectation (Milstein with a Gaussian last step) smoothing for digital Greeks, the level-0 estimator is deterministic, so its variance is zero.
