# Blind read-back report: packet R28 (Theorem 1, log-cost variants)

| Field | Value |
|---|---|
| Date | 2026-10-08 |
| Packet | `readback/round20/packet_R28_thm1log.lean` |
| Declarations audited | 10 (9 theorems + 1 definition `complexityBoundLog`); the 11 appended helper definitions are rendered briefly in §0 |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round20/work_R28/` (`core_check.py/.out`, `lower_check.py/.out`, `contract_sim.py/.out`, `scratch.lean/.out`) |

Lean check: I compiled a scratch copy of the packet (namespace renamed to `MLMC.AuditR28`, proofs left as `sorry`,
`import MlmcLean`). It elaborates with no errors (`scratch.out`). The `#print` output of the appended helper definitions
matches the packet. `#check` confirms the binder structure. Parse checks with `rfl`/`simp` confirm that
`∑ ℓ ∈ range (L+1), Y ℓ (N ℓ) ω - μ[P]` reads as $(\sum_\ell Y_\ell) - \mathbb E P$, not as $\sum_\ell (Y_\ell - \mathbb E P)$:
the big-operator body has precedence 67 and `-` has 65. A body `Vb … / N ℓ` keeps the division inside the sum.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `complexityBoundLog` | def | n/a (well-defined, positive on $0<\varepsilon<e^{-1}$) | n/a | No |
| 2 | `mlmc_complexity_core_log` | theorem | True | No | No |
| 3 | `giles_theorem1_log_cost_sum` | theorem | True | No | No |
| 4 | `giles_theorem1_log_uniform` | theorem | True | No | No |
| 5 | `giles_theorem1_log` | theorem | True | No | No |
| 6 | `giles_theorem1_log_of_lt` | theorem | True | No | No |
| 7 | `mlmc_cost_lower_log` | theorem | True | No | No |
| 8 | `giles_theorem1_corrections_log` | theorem | True | No | No |
| 9 | `giles_theorem1_fineCoarse_log` | theorem | True | No | No |
| 10 | `contracting_levels_mlmc_log` | theorem | True (proof sketch; Monte Carlo agrees; I did not check every constant) | No | No |

## Main points for a human auditor

- I found no false or vacuous statement, and none that holds only because of a junk value. Every MSE integrand and every
  cost integrand is integrable under the stated hypotheses, so no "$<\varepsilon^2$" claim holds only because a
  non-integrable integral is 0. Every `variance` is taken of an $L^2$ variable, so the hypotheses are not weakened by
  `variance = (evariance).toReal = 0` for non-$L^2$ variables. Every `rpow` has a positive base.
- **The constant $c_4$ is uniform only in #4.** In #3, #5, #6, #8, #9 and #10, $c_4$ is chosen after all the data
  ($\mu$, $Y$, $V$, $C$, cost, $a$, $b$, $f$, …), so it may depend on them. Giles's theorem has $c_4$ depending only
  on $\alpha,\beta,\gamma,c_1,c_2,c_3$. The `_uniform` theorem (#4) restores this for the general bound. No uniform
  version of the sharp $\gamma<\beta$ bound (#6) is in the packet.
- **The $\gamma<\beta$ branch of `complexityBoundLog` is loose.** That branch is $\varepsilon^{-2}|\log\varepsilon|^\kappa$,
  which is sharp only when $\gamma=2\alpha$; there, the rounding cost $\sum_{\ell\le L} C_\ell$ really is of order
  $\varepsilon^{-2}|\log\varepsilon|^{\kappa}$ (`core_check.out`, case 3). For $\gamma<2\alpha$ the sharp
  $\varepsilon^{-2}$ is the separate theorem #6. #6 assumes strict $\gamma<2\alpha$ and puts **no sign condition on
  $\kappa$** (any real $\kappa$). For $\kappa\le 0$ the boundary $\gamma=2\alpha$ is excluded unnecessarily, but #2–#5
  with $\kappa=0$ cover it.
- **The lower bound #7 is a model lower bound.** It assumes exact bias $c_1 2^{-\alpha L}$ and exact variances
  $V_\ell=c_2 2^{-\beta\ell}$, and bounds the cost of any $(L,N)$ satisfying the model MSE constraint. It is not an
  information-based lower bound over all estimators. It matches the upper bounds for $\beta=\gamma$, for $\beta<\gamma$,
  and for $\gamma<\beta$ with $\gamma=2\alpha$ (via part (d)). For $\gamma<\beta$ with $\gamma<2\alpha$ it gives only
  $\varepsilon^{-2}$, which matches #6.
- **#10 (contracting levels):**
  - The name `κ` here is the **dissipativity constant**, not the log-cost exponent; the latter is fixed at 1, giving
    $|\log\varepsilon|^3=|\log\varepsilon|^{2+1}$.
  - The target $P$ is defined only as the common limit $\lim_\ell \mathbb E f(\text{contractPath}_\ell)=\lim_\ell \mathbb E f(\text{contractLimit}_\ell)$
    of the Euler–Maruyama quantities. The theorem does **not** say that $P=\int f\,d\pi$ for the invariant measure
    $\pi$ of the SDE. $P$ is still uniquely determined by the statement.
  - The cost of a level-$\ell$ sample is modelled as $N_\ell$ fine steps; the coarse path's $N_{\ell-1}\le N_\ell/2$
    steps are not counted. This changes cost only by a constant factor.
  - Only 1-D SDEs are covered.
  - `backIter` applies the noise in backward order (coupling from the past).
  - The hypotheses are mutually consistent: they imply $\kappa\le K_a$ and $\delta h_0\le 1$, and an explicit instance
    is given below.
- **#8 and #9:** $\nu$ is not assumed to be a probability measure, but `hω` (measure preservation from the probability
  measure $\mu$) forces it. In #8, `h_ii` constrains only the **means** of the corrections $\Delta_\ell$, as in
  Giles's general correction framework.
- **Minor modelling choices in #3–#6:**
  - Independence is only pairwise across levels; this is enough for adding variances.
  - `h_var` is an equality $\operatorname{Var}(Y_{\ell,n})=V_\ell/n$ (sample-mean structure) rather than $\le$.
  - Costs $C_\ell$ are only bounded above and may be negative, which is harmless for an upper bound.

---

## §0. Helper definitions (appended from other modules; `#print` matches the packet)

- `Vb β c₂ ℓ` $=c_2\,2^{-\beta\ell}$ (real power, $\ell$ cast to $\mathbb R$).
- `levelDiff Pl 0 = Pl 0`; `levelDiff Pl (ℓ+1) = Pl(ℓ+1) − Pl ℓ` (pointwise).
- `totalCost cost L N x` $=\sum_{\ell=0}^{L}\sum_{n<N_\ell}\mathrm{cost}(\ell,n,x)$.
- `blockMean f ω i N x` $=N^{-1}\sum_{n<N} f_i(\omega_{(i,n)}(x))$. For $N=0$ it is $0$ by $0^{-1}=0$; this never
  arises, because every theorem forces $N_\ell>0$.
- `fineCoarseDiff Pf Pc 0 = Pf 0`; `fineCoarseDiff Pf Pc (ℓ+1) = Pf(ℓ+1) − Pc ℓ`. So `Pc ℓ` is the level-$\ell$
  approximation computed inside the level-$(\ell{+}1)$ correction.
- `pairAvg z k` $=(z_{2k}+z_{2k+1})/\sqrt2$. If $z$ is i.i.d. $N(0,1)$, so is `pairAvg z`. Then
  $\sqrt{h_\ell}\,\text{pairAvg}(z)_k=\sqrt{h_{\ell+1}}(z_{2k}+z_{2k+1})$, which is the Brownian-increment coupling.
- `stdNormalSeq` = the infinite product $\bigotimes_{k\in\mathbb N}N(0,1)$ on $\mathbb R^{\mathbb N}$.
- `backIter φ n e x`: $\mathrm{backIter}_0=x$ and $\mathrm{backIter}_{n+1}(e,x)=\varphi(\mathrm{backIter}_n(e_{\cdot+1},x),e_0)$.
  So $\mathrm{backIter}_n(e,x)=\varphi(\cdots\varphi(\varphi(x,e_{n-1}),e_{n-2})\cdots,e_0)$: the noise $e_{n-1}$ is
  applied first and $e_0$ last (backward, coupling-from-the-past iteration).
- `emStep a b h S dW` $=S+a(S)h+b(S)\,dW$ (one Euler–Maruyama step).
- `contractPath a b h₀ x₀ N ℓ z` $=\mathrm{backIter}(\mathrm{emStep}_{h_\ell}, N_\ell, (\sqrt{h_\ell}z_k)_k, x_0)$ with
  $h_\ell=h_0/2^\ell$. This is EM with $N_\ell$ steps of size $h_\ell$ started at $x_0$, over the horizon
  $T_\ell=N_\ell h_\ell$.
- `contractLimit … ℓ z` = `limUnder atTop` of the same sequence as $n\to\infty$. Where the sequence diverges this is a
  junk value chosen by `Classical.choice`; #10 proves almost-sure convergence, so the junk value is irrelevant.

## 1. `complexityBoundLog` (definition)

**Rendering.** For real $\alpha,\beta,\gamma,\kappa,\varepsilon$:
$$\mathrm{CB}(\varepsilon)=\begin{cases}\varepsilon^{-2}\,|\log\varepsilon|^{\kappa}, & \gamma<\beta,\\ \varepsilon^{-2}\,|\log\varepsilon|^{2+\kappa}, & \beta=\gamma,\\ \varepsilon^{-2-(\gamma-\beta)/\alpha}\,|\log\varepsilon|^{\kappa}, & \gamma>\beta,\end{cases}$$
with real (`rpow`) powers. On $0<\varepsilon<e^{-1}$ (the only range used) we have $|\log\varepsilon|>1$ and
$\varepsilon>0$, so all bases are positive and $\mathrm{CB}>0$. When $\kappa=0$, $|\log\varepsilon|^0=1$.

**Assessment.** This is the cost bound of Giles's MLMC complexity theorem (Giles 2008, Thm 3.1; Giles 2015,
Acta Numerica Thm 2.1), extended to a per-sample cost $c_3(\ell+1)^\kappa2^{\gamma\ell}$ with a polylogarithmic factor.
With $L\asymp|\log\varepsilon|$, that factor contributes $|\log\varepsilon|^\kappa$. In the case $\gamma<\beta$ the
factor $|\log\varepsilon|^\kappa$ is not sharp unless $\gamma=2\alpha$ (see #6 and #7). It is still a valid upper
bound. There are no junk values on the domain used.

## 2. `mlmc_complexity_core_log`

**Rendering.** Hypotheses: $\alpha>0$, $\gamma>0$, $\kappa\ge0$, $c_1,c_2,c_3>0$ and $\tfrac12\min(\beta,\gamma)\le\alpha$;
$\beta$ is an arbitrary real. Claim: there is a $c_4>0$, depending only on $(\alpha,\beta,\gamma,\kappa,c_1,c_2,c_3)$,
such that for every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with all
$N_\ell\ge1$ satisfying
$$\big(c_1 2^{-\alpha L}\big)^2+\sum_{\ell=0}^{L}\frac{c_22^{-\beta\ell}}{N_\ell}<\varepsilon^2,\qquad
\sum_{\ell=0}^{L}N_\ell\,c_3(\ell+1)^\kappa2^{\gamma\ell}\le c_4\,\mathrm{CB}(\varepsilon).$$

**Assessment.**
- **True.** Take $L=\lfloor\log_2(\sqrt2c_1/\varepsilon)/\alpha\rfloor+1$, so that the squared bias is below
  $\varepsilon^2/2$ strictly. Take $N_\ell=\lceil2\varepsilon^{-2}\sqrt{V_\ell/C_\ell}\,S\rceil$ with
  $S=\sum_{\ell\le L}\sqrt{V_\ell C_\ell}$. Then the variance term is at most $\varepsilon^2/2$, and
  $\text{cost}\le2\varepsilon^{-2}S^2+\sum_{\ell\le L}C_\ell$.
  - The bound $S^2\lesssim1$, $L^{2+\kappa}$ or $L^\kappa2^{(\gamma-\beta)L}$ in the three cases.
  - The rounding term satisfies $\sum_{\ell\le L} C_\ell\lesssim L^\kappa 2^{\gamma L}\lesssim|\log\varepsilon|^\kappa\varepsilon^{-\gamma/\alpha}$
    (this uses $\gamma>0$). It is dominated by $\mathrm{CB}$ because $\gamma\le2\alpha$ when $\gamma\le\beta$, and
    $\beta\le2\alpha$ when $\beta<\gamma$. The second case allows $\beta\le0$.
  - $L+1\le K|\log\varepsilon|$ because $|\log\varepsilon|>1$.
  - `core_check.out`: the ratio cost$/\mathrm{CB}$ stays bounded for $\varepsilon$ from $0.999e^{-1}$ down to $10^{-64}$
    in 9 parameter regimes, including $\beta<0$, the boundaries $\gamma=2\alpha$ and $\beta=2\alpha$, and large $c_1$.
- **Vacuity:** none. The only hypotheses are parameter constraints, e.g. $\alpha=\beta=\gamma=1$, $\kappa=0$,
  $c_i=1$.
- **Junk:** none. $N_\ell>0$ is enforced, so there is no division by zero.
- **Hypotheses:** standard. $\gamma>0$ is needed for the geometric rounding sum.
  $\tfrac12\min(\beta,\gamma)\le\alpha$ is Giles's condition.
- **Standard result:** the deterministic core of Giles's Theorem 1 (log-cost variant).

## 3. `giles_theorem1_log_cost_sum`

**Rendering.** The setting is a probability space $(\Omega,\mu)$ with real random variables $P$, $P_\ell$ and
$Y_{\ell,n}$ ($\ell,n\in\mathbb N$), and real sequences $V$, $C$. The constants are as in #2: $\alpha,\gamma>0$,
$\kappa\ge0$, $c_i>0$, $\tfrac12\min(\beta,\gamma)\le\alpha$. Hypotheses:
- $P$ and every $P_\ell$ are integrable.
- $Y_{\ell,n}\in L^2$ for $n>0$.
- For $i\ne j$ and $n,m>0$, $Y_{i,n}$ and $Y_{j,m}$ are independent. This is the content of the "$\forall N>0$,
  Pairwise" form.
- $|\mathbb E[P_\ell-P]|\le c_12^{-\alpha\ell}$.
- $\mathbb E Y_{0,n}=\mathbb E P_0$ and $\mathbb E Y_{\ell+1,n}=\mathbb E[P_{\ell+1}-P_\ell]$ for $n>0$.
- $\operatorname{Var}Y_{\ell,n}=V_\ell/n$ for $n>0$.
- $V_\ell\le c_22^{-\beta\ell}$.
- $C_\ell\le c_3(\ell+1)^\kappa2^{\gamma\ell}$.

Claim: there is a $c_4>0$ (it may depend on all the data) such that for every $\varepsilon\in(0,e^{-1})$ there exist
$L$ and $N$ with all $N_\ell\ge1$ satisfying
$\mathbb E\big[(\sum_{\ell\le L}Y_{\ell,N_\ell}-\mathbb EP)^2\big]<\varepsilon^2$ and
$\sum_{\ell\le L}N_\ell C_\ell\le c_4\,\mathrm{CB}(\varepsilon)$.

**Assessment.**
- **True.** By telescoping, $\mathbb E\sum Y=\mathbb EP_L$. MSE $=\operatorname{Var}+\text{bias}^2$, where
  $\operatorname{Var}=\sum V_\ell/N_\ell$ by pairwise independence. So
  $\text{MSE}\le(c_12^{-\alpha L})^2+\sum Vb/N_\ell$. Then apply #2, and use $N_\ell C_\ell\le N_\ell\,c_3(\ell+1)^\kappa2^{\gamma\ell}$.
- **Vacuity:** none. Trivial instance: everything $0$ (variance of $0$ is $0=0/n$; constants are independent).
  Non-trivial instance: on $\bigotimes_{\mathbb N\times\mathbb N}N(0,1)$ take $Y_{\ell,n}=\sqrt{c_2}2^{-\beta\ell/2}\frac1n\sum_{k<n}x_{(\ell,k)}$,
  $P=P_\ell=0$, $V_\ell=c_22^{-\beta\ell}$ and $C_\ell=c_3(\ell+1)^\kappa2^{\gamma\ell}$.
- **Junk:** none. The MSE integrand is the square of an $L^2$ function minus a constant, so it is integrable, and the
  integral is not a junk $0$. `variance` is genuine because $Y\in L^2$. $V_\ell\ge0$ follows from `h_var` at $n=1$.
- **Hypotheses:**
  - $c_4$ is not uniform in the data, which is weaker than Giles; #4 fixes this.
  - The `h_var` equality is a strong structural assumption, but natural.
  - $C_\ell$ may be negative, which is harmless.
- **Standard result:** Giles's MLMC complexity theorem (log-cost variant), with cost expressed as $\sum N_\ell C_\ell$.

## 4. `giles_theorem1_log_uniform`

**Rendering.** For constants as in #2, there is a $c_4>0$ (depending only on
$\alpha,\beta,\gamma,\kappa,c_1,c_2,c_3$) with the following property. For every probability space $(\Omega,\mu)$
with $\Omega$ in universe `u`, all $P,P_\ell,Y_{\ell,n},\mathrm{Cost}_{\ell,n},V,C$ satisfying the hypotheses of #3,
together with $\mathrm{Cost}_{\ell,n}$ integrable and $\mathbb E\,\mathrm{Cost}_{\ell,n}=n\,C_\ell$ for $n>0$, and every
$\varepsilon\in(0,e^{-1})$, there exist $L$ and $N\ge1$ with MSE $<\varepsilon^2$ and
$\mathbb E\big[\sum_{\ell\le L}\mathrm{Cost}_{\ell,N_\ell}\big]\le c_4\,\mathrm{CB}(\varepsilon)$.

**Assessment.**
- **True.** $\mathbb E\sum_\ell\mathrm{Cost}_{\ell,N_\ell}=\sum N_\ell C_\ell$ by linearity (finite sum of integrable
  functions). The $c_4$ from #2 depends only on the constants, so it works uniformly.
- **Vacuity:** none. Use the instance from #3 with $\mathrm{Cost}_{\ell,n}\equiv nC_\ell$.
- **Junk:** none.
- **Quantifier order** is the strong one ($\exists c_4$ before the data), matching Giles.
- **Standard result:** Giles's Theorem 1, in its proper uniform form (log-cost variant).

## 5. `giles_theorem1_log`

**Rendering.** The same hypotheses as #3, plus random costs with $\mathrm{Cost}_{\ell,n}$ integrable and
$\mathbb E\,\mathrm{Cost}_{\ell,n}=nC_\ell$ for $n>0$. Conclusion: there is a $c_4>0$ (it may depend on the data) such
that for every $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N\ge1$ with MSE $<\varepsilon^2$ and
$\mathbb E\sum_{\ell\le L}\mathrm{Cost}_{\ell,N_\ell}\le c_4\,\mathrm{CB}(\varepsilon)$.

**Assessment.**
- **True.** It is a direct consequence of #4, or of #3 plus linearity.
- **Vacuity:** none (same instance).
- **Junk:** none. The cost integrand is a finite sum of integrable functions.
- **Hypotheses:** $c_4$ is non-uniform; otherwise standard.
- **Standard result:** Giles's Theorem 1 with expected random cost.

## 6. `giles_theorem1_log_of_lt`

**Rendering.** The hypotheses of #3, except:
- there is no $\kappa\ge0$ hypothesis, so $\kappa$ is any real;
- there is no `hαβγ` hypothesis;
- instead it assumes $\gamma<\beta$ and $\gamma<2\alpha$, both strict.

Conclusion: there is a $c_4>0$ (it may depend on the data) such that for every $\varepsilon\in(0,e^{-1})$ there exist
$L$ and $N\ge1$ with MSE $<\varepsilon^2$ and $\sum_{\ell\le L}N_\ell C_\ell\le c_4\varepsilon^{-2}$, with no log
factor.

**Assessment.**
- **True.** $S=\sum_\ell\sqrt{V_\ell C_\ell}\le\sqrt{c_2c_3}\sum(\ell+1)^{\kappa/2}2^{-(\beta-\gamma)\ell/2}<\infty$ for
  any real $\kappa$. The rounding term is $\lesssim L^{\max(\kappa,0)}2^{\gamma L}\lesssim|\log\varepsilon|^{\max(\kappa,0)}\varepsilon^{-\gamma/\alpha}=o(\varepsilon^{-2})$
  because $\gamma<2\alpha$ strictly.
- **The strictness is needed when $\kappa>0$.** With $\gamma=2\alpha$, $\kappa=1$, and bias and cost bounds attained,
  cost$\cdot\varepsilon^2$ grows like $|\log\varepsilon|$ (`core_check.out`, case 3).
- **Vacuity:** none, e.g. $\alpha=1$, $\beta=2$, $\gamma=1$, with any $\kappa$, including $\kappa=-3$ or $\kappa=5$.
- **Junk:** none. $(\ell+1)^\kappa$ has base $\ge1$.
- **Hypotheses:**
  - $c_4$ is non-uniform.
  - For $\kappa\le0$, excluding $\gamma=2\alpha$ is unnecessary, but that case is covered by #2–#5 with $\kappa=0$.
- **Standard result:** the $\beta>\gamma$ case of Giles's theorem ($O(\varepsilon^{-2})$), which stays robust under
  polylogarithmic cost growth.

## 7. `mlmc_cost_lower_log`

**Rendering.** Hypotheses: $\alpha>0$, $\kappa\ge0$, $c_1,c_2,c_3>0$ and $0<\varepsilon<c_1$; $\beta,\gamma$ are
arbitrary reals. For any $L\in\mathbb N$ and $N\ge1$ with
$(c_12^{-\alpha L})^2+\sum_{\ell\le L}c_22^{-\beta\ell}/N_\ell\le\varepsilon^2$, set
$W=\sum_{\ell\le L}N_\ell c_3(\ell+1)^\kappa2^{\gamma\ell}$ and $\lambda=\log_2(c_1/\varepsilon)/\alpha>0$. Then:
- (a) $W\ge c_2c_3\varepsilon^{-2}$;
- (b) if $\beta=\gamma$: $W\ge\frac{c_2c_3}{(1+\kappa/2)^2}\varepsilon^{-2}\lambda^{2+\kappa}$;
- (c) if $\beta\le\gamma$: $W\ge c_2c_3\varepsilon^{-2}(c_1/\varepsilon)^{(\gamma-\beta)/\alpha}\lambda^{\kappa}$;
- (d) if $\gamma\ge0$: $W\ge c_3(c_1/\varepsilon)^{\gamma/\alpha}\lambda^\kappa$.

**Assessment.** **True.**
- The variance sum is strictly positive, so $c_12^{-\alpha L}<\varepsilon$. Hence $L>\lambda>0$ and $L+1>\lambda$.
- By Cauchy–Schwarz, $\big(\sum\sqrt{V_\ell C_\ell}\big)^2\le\big(\sum V_\ell/N_\ell\big)W\le\varepsilon^2W$, where
  $V_\ell C_\ell=c_2c_3(\ell+1)^\kappa2^{(\gamma-\beta)\ell}$.
- (a): use the $\ell=0$ term, or $N_0\ge c_2/\varepsilon^2$ directly.
- (b): $\sum_{m=1}^{L+1}m^{\kappa/2}\ge\int_0^{L+1}x^{\kappa/2}dx=(L+1)^{1+\kappa/2}/(1+\kappa/2)$, using $\kappa\ge0$.
- (c): use the $\ell=L$ term, with $2^{(\gamma-\beta)L}\ge(c_1/\varepsilon)^{(\gamma-\beta)/\alpha}$.
- (d): use $W\ge N_Lc_3(L+1)^\kappa2^{\gamma L}$ with $N_L\ge1$.
- `lower_check.out`: across 4000 random admissible instances (with near-optimal and perturbed $N$), all applicable
  inequalities hold. The minimum ratios $W/\text{lower}$ are 1.51, 1.30, 4.70 and 1.21.

Further points:
- **Vacuity:** none. Example: $\alpha=\beta=c_1=c_2=1$, $\varepsilon=1/2$, $L=2$, $N\equiv10$ gives
  $1/16+0.175\le1/4$.
- **Junk:** none. `hεc` makes $c_1/\varepsilon>1$, so $\log_2>0$ and all `rpow` bases are positive.
- **Hypotheses:** this is a lower bound for the **model** problem (exact bias and variance profiles). It is not a
  minimax or information-based complexity lower bound. Using "$\le\varepsilon^2$" in the hypothesis makes it slightly
  stronger than needed.
- **Standard result:** the optimal-allocation (Lagrange / Cauchy–Schwarz) lower bound of MLMC cost. It shows that
  Giles's bounds are sharp for $\beta=\gamma$ (with $|\log\varepsilon|^{2+\kappa}$) and for $\beta<\gamma$.

## 8. `giles_theorem1_corrections_log`

**Rendering.** The setting:
- a sample space $(\Omega_0,\nu)$ and a probability space $(\Omega,\mu)$;
- sample maps $\omega_{(\ell,n)}:\Omega\to\Omega_0$, each measure-preserving $\mu\to\nu$, forming a mutually
  independent family (`iIndepFun`). This forces $\nu$ to be a probability measure.

Hypotheses:
- $P$ and every $P_\ell$ are $\nu$-integrable.
- Each correction $\Delta_\ell$ is measurable and in $L^2(\nu)$.
- Each random cost $\mathrm{cost}_{\ell,n}$ is $\mu$-integrable with mean $C_\ell$, for all $n$.
- $|\mathbb E_\nu[P_\ell-P]|\le c_12^{-\alpha\ell}$.
- $\mathbb E_\nu\Delta_\ell=\mathbb E_\nu[\mathrm{levelDiff}(P)_\ell]$, i.e. $\mathbb EP_0$ for $\ell=0$ and
  $\mathbb E[P_{\ell}-P_{\ell-1}]$ for $\ell\ge1$.
- $\operatorname{Var}_\nu\Delta_\ell\le c_22^{-\beta\ell}$.
- $C_\ell\le c_3(\ell+1)^\kappa2^{\gamma\ell}$.
- The constants are as in #2.

Conclusion: there is a $c_4>0$ (it may depend on the data) such that for every $\varepsilon\in(0,e^{-1})$ there exist
$L$ and $N\ge1$ with
$\mathbb E_\mu\big[(\sum_{\ell\le L}\frac1{N_\ell}\sum_{n<N_\ell}\Delta_\ell(\omega_{(\ell,n)})-\mathbb E_\nu P)^2\big]<\varepsilon^2$
and $\mathbb E_\mu\big[\sum_{\ell\le L}\sum_{n<N_\ell}\mathrm{cost}_{\ell,n}\big]\le c_4\,\mathrm{CB}(\varepsilon)$.

**Assessment.**
- **True.** The block means have mean $\mathbb E\Delta_\ell$ and variance $\operatorname{Var}\Delta_\ell/N_\ell$; by
  independence the variances add; the means telescope to $\mathbb EP_L$. Expected cost $=\sum N_\ell C_\ell$. Then
  apply #2.
- **Vacuity:** none. Take $\Omega_0=\mathbb R$, $\nu=N(0,1)$, $\Omega=\mathbb R^{\mathbb N\times\mathbb N}$ with the
  product measure, $\omega_p$ the coordinate projections, $\Delta_\ell(y)=\sqrt{c_2}2^{-\beta\ell/2}y$, $P=P_\ell=0$,
  and cost $\equiv C_\ell$.
- **Junk:** none.
  - $\Delta_\ell\circ\omega_p\in L^2(\mu)$ by `MemLp.comp_measurePreserving`, so the MSE integrand is integrable.
  - The variance is genuine.
  - The integral `∫ y, Pl ℓ y - P y ∂ν` parses as the integral of the difference.
- **Hypotheses:** standard. `h_ii` constrains only means, which is the general "corrections" form. $c_4$ is
  non-uniform.
- **Standard result:** Giles's Theorem 1 for a general MLMC estimator with i.i.d. samples per level (Giles 2015, §2).

## 9. `giles_theorem1_fineCoarse_log`

**Rendering.** The same sampling setting as #8. Fine and coarse approximations $P^f_\ell,P^c_\ell$ are measurable and
in $L^2(\nu)$, with $\mathbb E_\nu P^f_\ell=\mathbb E_\nu P^c_\ell$ for all $\ell$ (the telescoping condition), and
$P$ is integrable. Hypotheses:
- $|\mathbb E_\nu[P^f_\ell-P]|\le c_12^{-\alpha\ell}$;
- $\operatorname{Var}_\nu(\mathrm{fineCoarseDiff}_\ell)\le c_22^{-\beta\ell}$, where the correction is $P^f_0$ at
  level 0 and $P^f_{\ell+1}-P^c_\ell$ at level $\ell+1$;
- the same cost hypotheses as #8.

The conclusion is as in #8, with $\Delta=\mathrm{fineCoarseDiff}$.

**Assessment.**
- **True.** $\mathbb E\,\mathrm{fineCoarseDiff}_{\ell+1}=\mathbb EP^f_{\ell+1}-\mathbb EP^c_\ell=\mathbb EP^f_{\ell+1}-\mathbb EP^f_\ell$,
  so the sum telescopes to $\mathbb EP^f_L$. Then argue as in #8.
- **Vacuity:** none. All-zero instance; or $P^f_\ell=P^c_\ell=2^{-\beta\ell/2}y$ with $\beta\ge0$ (correction
  variance $\le2^{-\beta\ell}$).
- **Junk:** none (all variables are $L^2$).
- **Hypotheses:** standard. `Pc ℓ` is indexed by the coarse level ($P^c_\ell$ is used in correction $\ell+1$); this is
  consistent with `h24`.
- **Standard result:** Giles 2015 Thm 2.1 for fine/coarse estimators $Y_\ell=P^f_\ell-P^c_{\ell-1}$ under the condition
  $\mathbb E P^f_\ell=\mathbb E P^c_\ell$.

## 10. `contracting_levels_mlmc_log`

**Rendering.**
- **Data:** $a,b:\mathbb R\to\mathbb R$ that are $K_a$- and $K_b$-Lipschitz, and dissipative:
  $(x-y)(a(x)-a(y))\le-\kappa(x-y)^2$ for all $x,y$, where $\kappa$ is the **dissipativity constant**.
- **Constants:** $\delta>0$, $h_0>0$, with the margin $K_b^2+K_a^2h_0+\delta\le2\kappa$. Start point $x_0\in\mathbb R$.
- **Step counts** $N:\mathbb N\to\mathbb N$ (inequalities in $\mathbb N$ except `hT`):
  - $2N_\ell\le N_{\ell+1}$;
  - for a real $c$ with $8\ln2\le c\delta$: $c\,\ell\le N_\ell h_0/2^\ell$ (horizon $T_\ell\ge c\ell$);
  - for some $m\in\mathbb N$: $N_\ell\le m(\ell+1)2^\ell$.
- **Test function:** $f$ is $K_f$-Lipschitz.
- **Part A**, for every $\ell$:
  - $f(\text{contractPath}_\ell)$ is integrable under $\bigotimes N(0,1)$;
  - almost surely the backward EM iterates $\mathrm{backIter}_n$ (step $h_\ell=h_0/2^\ell$, noise $\sqrt{h_\ell}z_k$)
    converge as $n\to\infty$ to $\text{contractLimit}_\ell(z)$;
  - $f(\text{contractLimit}_\ell)$ is integrable.
- **Part B:** there is a $P\in\mathbb R$ with $\mathbb Ef(\text{contractPath}_\ell)\to P$ and
  $\mathbb Ef(\text{contractLimit}_\ell)\to P$ as $\ell\to\infty$. Moreover there is a $c_4>0$ such that for every
  $\varepsilon\in(0,e^{-1})$ there exist $L$ and $M\ge1$ with the following properties, under
  $\bigotimes_{(\ell,n)\in\mathbb N^2}\bigotimes_k N(0,1)$:
  - the squared error of the MLMC estimator
    $\sum_{\ell\le L}\frac1{M_\ell}\sum_{n<M_\ell}\mathrm{fineCoarseDiff}_\ell(x_{(\ell,n)})$ is integrable;
  - its mean square error about $P$ is $<\varepsilon^2$;
  - the expected cost $\sum_{\ell\le L}M_\ell N_\ell$ is $\le c_4\varepsilon^{-2}|\log\varepsilon|^3$.

  Here $\mathrm{fineCoarseDiff}_{\ell+1}(z)=f(\text{contractPath}_{\ell+1}(z))-f(\text{contractPath}_\ell(\text{pairAvg }z))$.

**Assessment.** **True**, on the following sketch.
- **One-step contraction.** With $e=x-y$ and the same noise, one EM step gives
  $\mathbb E|e'|^2\le e^2\big(1-h(2\kappa-K_b^2-K_a^2h)\big)\le(1-\delta h)e^2$ for $h\le h_0$. Each level's chain
  contracts in mean square. (The hypotheses force $\kappa\le K_a$ and hence $\delta h_0\le1$, so they are consistent.)
- **(A) Backward iterates.** Consecutive backward iterates differ by
  $\mathbb E|X_{n+1}-X_n|^2\le(1-\delta h)^n\,\text{const}$. This is summable, so the iterates converge a.s. `limUnder`
  equals that limit a.s. Gaussian moments and Lipschitz maps give integrability; Fatou with uniform second moments
  covers the limit.
- **(B) Coupled pair.** For the fine (two half-steps) and coarse (one step, `pairAvg` noise) pair, the leading part
  contracts at rate $\delta$. The remainder terms are $O(h^{3/2}|e|(1+|x|))$ and $O(h^2(1+x^2))$, with uniformly bounded
  moments. This gives $\mathbb E e_{n+1}^2\le(1-\tfrac\delta2h)\mathbb E e_n^2+Ch^2$.
- **Variance and bias rates.**
  - The burn-in mismatch decays like $e^{-\delta T_\ell/2}\le2^{-4\ell}$, using $c\delta\ge8\ln2$.
  - So $\operatorname{Var}(\mathrm{fineCoarseDiff}_\ell)\lesssim2^{-\ell}$, i.e. $\beta=1$.
  - The bias is $\lesssim\sum_{k\ge\ell}2^{-k/2}$, i.e. $\alpha=\tfrac12$.
  - The cost satisfies $N_\ell\le m(\ell+1)2^\ell$, i.e. $\gamma=1$, $\kappa_{\rm cost}=1$.
  - Since $\tfrac12\min(\beta,\gamma)=\tfrac12\le\alpha$, #9 with $\beta=\gamma$ gives $\varepsilon^{-2}|\log\varepsilon|^{3}$.
- **Existence of $P$.** The level means are Cauchy (via the coupled differences), and
  $|\mathbb Ef(\text{path}_\ell)-\mathbb Ef(\text{limit}_\ell)|\lesssim e^{-\delta T_\ell/2}\to0$.
- **Monte Carlo check** (`contract_sim.out`). Instance: $a(x)=-x$, $b(x)=0.5+0.3\sin x$, $h_0=1$, $\delta=0.91$,
  $c=6.1$, $N_\ell=7(\ell+1)2^\ell$, $m=7$, $f=|\cdot|$, $x_0=5$. All hypotheses are checked in the script.
  - $\operatorname{Var}(\mathrm{fineCoarseDiff}_\ell)\cdot2^\ell$ decreases from 0.083 to 0.005 over levels 1–7.
  - The mean corrections decay geometrically.
  - The telescoped means converge to about 0.284.

Further points:
- **Vacuity:** none. The instance above satisfies every hypothesis. A simpler one is $b\equiv\sigma$, $K_b=0$,
  $a(x)=-x$, $\kappa=1$, $h_0=\delta=1$, $c=6$, $N_\ell=6(\ell+1)2^\ell$, $m=6$, $f=\mathrm{id}$.
- **Junk:** none.
  - `contractLimit`'s junk value off the convergence set is null-set irrelevant, because Part A proves a.s.
    convergence.
  - The MSE integrability is asserted explicitly.
  - $\sqrt{h_\ell}$ has a positive argument.
  - $N_0=0$ is allowed; then level 0 is the constant $f(x_0)$, which is harmless.
- **Hypotheses and modelling:**
  - The name `κ` is the dissipativity constant, not the log exponent.
  - $P$ is not identified with $\int f\,d\pi_{\rm SDE}$.
  - Cost counts only the $N_\ell$ fine steps per sample, a constant-factor undercount.
  - 1-D only.
  - $c_4$ depends on all the data.
  - The constant $8\ln2$ leaves ample slack in my sketch: any rate $\ge\delta/8$ for the coupled pair would suffice.
- **Standard result:** MLMC for invariant-measure expectations of contractive ergodic SDEs via Euler–Maruyama with
  spin-up time $T_\ell\propto\ell$ (in the spirit of Fang & Giles; Glynn & Rhee). It has the
  $O(\varepsilon^{-2}|\log\varepsilon|^3)$ complexity of the $\beta=\gamma=1$ case with one extra log factor in the
  cost.
