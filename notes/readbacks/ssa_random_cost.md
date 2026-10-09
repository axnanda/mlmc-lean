# Blind read-back R54: SSA tick-counter cost (`MlmcLean.TauLeapingSSACost`)

| Field | Value |
|---|---|
| Date | 2026-10-09 |
| Packet | `readback/round28/packet_R54_ssacost.lean` |
| Declarations audited | 11 (5 definitions and 6 theorems). The 22 context definitions appended to the packet are also rendered briefly. |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round28/work_R54_ssacost/`: `check_ssa_laws.py` / `.out` (numerics), `scratch1.lean` / `.out` (the packet compiled with `sorry` plus `#check`s using `pp.coercions` and `pp.numericTypes`), `scratch2.lean` (parse and division-convention checks), `scratch3.lean` (measurability checks). All Lean files compile. |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `ssaStepCount` | def | n/a (well defined: the kernels have discrete domains, so they are measurable) | n/a | no |
| 2 | `ssaChainCount` | def | n/a | n/a | no |
| 3 | `ssaChainCount_map_fst` | theorem | **true** (needs no hypotheses at all) | no | no |
| 4 | `ssaChainCount_map_exact` | theorem | **true** (`hΛ` is needed) | no | no |
| 5 | `ssaChainCount_marginals` | theorem | **true** (`hΛ` and `hN` are needed) | no | no |
| 6 | `ssaLevelCountLaw` | def | n/a | n/a | no |
| 7 | `ssaCountInputLaw` | def | n/a (it is Mathlib's junk `0` if some factor is not a probability measure, which can only happen without `hΛ`) | n/a | guarded: every theorem that uses it assumes `hΛ` |
| 8 | `ssaSampleCost` | def | n/a | n/a | no |
| 9 | `ssa_exact_sample_cost` | theorem | **true** | no | no |
| 10 | `ssaTotalCost_moments` | theorem | **true** | no | no |
| 11 | `ssa_mlmc_complexity_random_cost` | theorem | **true** | no | no |

## Main points for a human auditor

1. **All six theorems are true and non-vacuous, and none of them depends on a junk value.** I checked them numerically with exact finite-support computations (Poisson tails truncated below $10^{-30}$). The maximum discrepancy is about $2\times10^{-16}$ in every identity.
2. **The cost comes from the same sample as the estimator.** In the complexity theorem, the cost of sample $(L{+}1,n)$ is $2^L + (x_{(L+1,n)}(L{+}1)).2$. The estimator uses the state pair $(x_{(L+1,n)}(L{+}1)).1$: the same outer index $p=(L{+}1,n)$, the same coordinate $L{+}1$ and the same `N`. The counter is generated in `ssaStepCount` by the same Poisson draw $m$ that drives the $m$ ticks of the state. Theorem 2 confirms the coupling: given $K=k$, the exact state has law `jumpPow k x₀`.
3. **The `infinitePi` junk branch.** In Mathlib (`ProductMeasure.lean:358`), `Measure.infinitePi μ` is defined as `if ∀ i, IsProbabilityMeasure (μ i) then … else 0`. The definitions `ssaCountInputLaw` and `ssaInputLaw` carry no bound $\lambda\le\Lambda$. Without that bound, `ssaTick` has total mass $\max(1,a,b)>1$ (checked: mass $1.6$ for $b=1.6$), so these products would be the zero measure. Every theorem that uses them assumes `hΛ`. Theorems 9(i) and 11(i) also assert `IsProbabilityMeasure`, which excludes the junk branch explicitly.
4. **The hypotheses are needed and natural.**
   - `hΛ : ∀ x, lam x ≤ Λ` is necessary for theorem 4. With $\Lambda=1$, $\lambda(0)=0.3$, $\lambda(1)=3$ and $n=2$, the two sides differ by $0.081$.
   - `0 < N` is necessary for theorem 5. With $N=0$ we get $T/0=0$ and zero steps, so the counter is identically $0$, not $\mathrm{Poi}(\Lambda T)$.
   - Theorem 3 needs no hypothesis. It is true even when the measures have mass greater than 1 (checked with mass $1.43$).
5. **Theorem 11 is a statement for a fixed $L$.** The constant $c$ is chosen after $L$ (and after $\lambda,\Lambda,T,x_0,\Phi,M$), so it may depend on $L$. The $\varepsilon^{-2}$ rate comes purely from unbiasedness: the last level is exact. The theorem says nothing about how the cost depends on $L$, chooses no $L(\varepsilon)$, and does not show an advantage over plain exact simulation. The tail bound follows from Chebyshev's inequality because $\operatorname{Var} C = N_{L+1}\Lambda T \le \mathbb E C \le c/\varepsilon^2$.
6. **Modelling choices worth knowing.**
   - The propensity must be bounded. This excludes mass-action rates such as $\lambda(x)=kx$.
   - There is a single reaction channel with jumps of $+1$, and $\Phi$ must be bounded.
   - The exact-level cost $K\sim\mathrm{Poi}(\Lambda T)$ counts all uniformisation ticks, including the fictitious ones, so $\mathbb E C$ grows with the chosen $\Lambda$.
   - A coupled $\tau$-leap sample at level $\ell$ costs $2^\ell$, which counts only the fine steps.
   - `exactLaw` is identified with the time-$T$ law of the continuous-time chain only through the uniformisation formula. That formula is correct for bounded rates, but the identification is not part of the packet.
7. **Parsing and casts were checked in Lean.**
   - In theorem 10, the right-hand side `∑ ℓ ∈ range (L + 1), N ℓ * 2 ^ ℓ + N (L+1) * (2^L + Λ*T)` parses as $(\sum_{\ell\le L} N_\ell 2^\ell) + N_{L+1}(2^L+\Lambda T)$. The big-sum body is `term:67`; checked with `Eq.refl`. This is the intended reading. The `∑ … - ∫ Φ` in theorem 11 parses the same way.
   - `T / ↑N` is a division in $\mathbb R_{\ge0}$ by a cast natural number. `T / (2:ℝ≥0)^L` has divisor at least 1.
   - The integrals elaborate to `↑Λ * ↑T` in $\mathbb R$.

## Context definitions (appended from other modules; brief rendering)

Notation: everything below is in $\mathbb R_{\ge0}$, so $x/0=0$ and $u-v$ means $(u-v)_+$. Write $\mathrm{Poi}(r)$ for `poissonMeasure r` $=\sum_n e^{-r}r^n/n!\,\delta_n$, a probability measure for every $r\ge0$.

- `jumpKernel lam Λ x` $=a_x\,\delta_{x+1}+(1-a_x)_+\,\delta_x$, where $a_x=\lambda(x)/\Lambda$. `jumpPow k x` is the $k$-step iterate.
- `exactLaw lam Λ t x` $=\sum_k \mathrm{Poi}(\Lambda t)\{k\}\,$`jumpPow k x`. This is the uniformisation (Jensen) formula for the pure-birth chain with rate $\lambda$ at time $t$, valid when $\lambda\le\Lambda$.
- `ssaTick lam Λ z (s₁,s₂)`: let $a=\lambda(s_1)/\Lambda$ and $b=\lambda(z)/\Lambda$. The kernel is
  $\min(a,b)\,\delta_{(s_1+1,s_2+1)}+(a-b)_+\,\delta_{(s_1+1,s_2)}+(b-a)_+\,\delta_{(s_1,s_2+1)}+(1-\max(a,b))_+\,\delta_{(s_1,s_2)}$.
  Its total mass is $\max(1,a,b)$. Under $a,b\le1$:
  - its first marginal is `jumpKernel s₁`;
  - its second coordinate moves up by 1 with probability $b$ (a $\tau$-leap move with the rate frozen at $z$);
  - the two moves are maximally coupled.
- `ssaTickPow lam Λ z n s` is $n$ ticks with $z$ held fixed. `ssaStep lam Λ h s` $=\sum_n \mathrm{Poi}(\Lambda h)\{n\}\,$`ssaTickPow lam Λ s.2 n s`, so $z$ is the coarse state at the start of the step. `ssaChain lam Λ h x₀ n` is $n$ such steps from $(x_0,x_0)$. Coordinate 1 is the exact (uniformised) path; coordinate 2 is the $\tau$-leap path with step $h$.
- `tauStep lam h x` is $x+\mathrm{Poi}(h\lambda(x))$; `tauChain` is $n$ such steps.
- `couplePair a b (p₁,p₂)` $=(p_1+p_2[b<a],\ p_1+p_2[a<b])$. `coupledIncr a b` is the image of $\mathrm{Poi}(\min)\otimes\mathrm{Poi}(\max-\min)$ under `couplePair a b`, a split coupling of $\mathrm{Poi}(a)$ and $\mathrm{Poi}(b)$.
- `coupledTwoStep lam h s` couples two fine $\tau$ steps of size $h$ with one coarse step of size $2h$, whose rate is frozen at $\lambda(s_2)$. `coupledChain lam h x₀ k` is $k$ such double steps.
- `tauLevelLaw lam T x₀`:
  - level 0 is $(X,X)$ with $X\sim$ `tauChain T x₀ 1`;
  - level $\ell+1$ is `coupledChain (T/2^{ℓ+1}) x₀ 2^ℓ`, i.e. fine step $T/2^{\ell+1}$ coupled with coarse step $T/2^\ell$ over $[0,T]$.
- `ssaLevelLaw lam Λ T x₀ L ℓ` is `tauLevelLaw ℓ` if $\ell\le L$, and otherwise `ssaChain (T/2^L) x₀ 2^L`. `ssaInputLaw` $=$ `infinitePi (ssaLevelLaw …)`.
- `tauFine Φ ℓ y` $=\Phi((y\,\ell).1)$ and `tauCoarse Φ ℓ y` $=\Phi((y(\ell+1)).2)$. `fineCoarseDiff Pf Pc 0 = Pf 0` and `fineCoarseDiff Pf Pc (ℓ+1) = Pf(ℓ+1) − Pc ℓ`. For `ssaCorrection Φ L ℓ y`:
  - if $\ell=0$: $\Phi((y\,0).1)$;
  - if $1\le\ell\le L$: $\Phi((y\,\ell).1)-\Phi((y\,\ell).2)$;
  - if $\ell>L$: $\Phi((y\,\ell).1)-\Phi((y\,\ell).2)$.

  So every level-$\ell$ correction reads only coordinate $\ell$ of its sample vector.
- `blockMean f ω i N x` $=N^{-1}\sum_{n<N} f\,i\,(\omega(i,n)\,x)$, with $0^{-1}=0$. `totalCost cost L N x` $=\sum_{\ell\le L}\sum_{n<N_\ell}\mathrm{cost}\,\ell\,n\,x$.

---

## 1. `ssaStepCount` (def)

**Rendering.** For $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $\Lambda,h\in\mathbb R_{\ge0}$ and a state $s=((a,b),c)\in(\mathbb N\times\mathbb N)\times\mathbb N$, define the measure
$$\mathrm{ssaStepCount}(s)=\sum_{m\ge0}\mathrm{Poi}(\Lambda h)\{m\}\cdot\big(\mathrm{ssaTickPow}_{z=b}^{\,m}(a,b)\big)\circ\big(t\mapsto(t,\,c+m)\big)^{-1}.$$
Draw the number of clock ticks $m\sim\mathrm{Poi}(\Lambda h)$, apply $m$ coupled ticks with the coarse rate frozen at $z=b$, and add $m$ to the counter.

**Assessment.** The definition is sound. The Poisson draw $m$ both drives the ticks and increments the counter, so the counter is the number of ticks actually used. The bind kernel $n\mapsto(\dots).\mathrm{map}(\dots)$ has domain $\mathbb N$, so it is measurable (`Measurable.of_discrete`, checked in `scratch3.lean`). The `bind` is therefore not the junk `0`.

## 2. `ssaChainCount` (def)

**Rendering.** This is the $n$-step Markov chain on $(\mathbb N\times\mathbb N)\times\mathbb N$ started at $((x_0,x_0),0)$ with kernel `ssaStepCount lam Λ h`. Formally, `ssaChainCount 0` $=\delta_{((x_0,x_0),0)}$ and `ssaChainCount (n+1)` $=$ `(ssaChainCount n).bind ssaStepCount`.

**Assessment.** The definition is sound. `ssaStepCount` is measurable because its domain is countable with measurable singletons (checked in Lean).

## 3. `ssaChainCount_map_fst` (theorem)

**Rendering.** For all $\lambda,\Lambda,h,x_0$ and all $n\in\mathbb N$, with **no hypotheses**,
$$(\mathrm{ssaChainCount}\,n)\circ\mathrm{fst}^{-1}=\mathrm{ssaChain}\,n.$$
Forgetting the counter gives back the existing coupled chain.

**Assessment.**
- **True.** By induction, using $(\mu\gg\!=\kappa)\circ f^{-1}=\mu\gg\!=(\kappa(\cdot)\circ f^{-1})$, $(\mu\circ g^{-1})\gg\!=\kappa=\mu\gg\!=(\kappa\circ g)$, and $\mathrm{ssaStepCount}(s)\circ\mathrm{fst}^{-1}=\mathrm{ssaStep}(s.1)$, because the counter never feeds back into the state. These identities need only measurability (automatic here). They hold for arbitrary measures, including measures of mass greater than 1 or infinite mass when $\lambda>\Lambda$.
- **Numerics.** The difference is at most $1.1\times10^{-16}$ for $N=1,2,4$ (section B). It is $5.6\times10^{-17}$ for $\lambda(1)=3>\Lambda=1$, where the mass is $1.43$ (section B′).
- **Vacuity.** Not vacuous: there are no hypotheses. For example $\lambda\equiv1$, $\Lambda=2$, $h=1$, $x_0=0$.
- **Junk.** None.
- **Standard fact.** An augmented Markov chain whose extra component does not influence the original one has the original chain as its marginal.

## 4. `ssaChainCount_map_exact` (theorem)

**Rendering.** Assume $\lambda(x)\le\Lambda$ for all $x$. Then for all $h\in\mathbb R_{\ge0}$, $x_0\in\mathbb N$ and $n\in\mathbb N$, the joint law of (exact state $u.1.1$, counter $u.2$) under `ssaChainCount n` is
$$\sum_k \mathrm{Poi}\big(n\,\Lambda h\big)\{k\}\;\mathrm{jumpPow}_k(x_0)\otimes\delta_k .$$
Here $n$ is cast from $\mathbb N$ to $\mathbb R_{\ge0}$. Equivalently, $K\sim\mathrm{Poi}(n\Lambda h)$, and given $K=k$ the exact state is the $k$-step uniformised jump chain.

**Assessment.**
- **True.** Under $a,b\le1$, the first marginal of `ssaTick z s` is `jumpKernel s.1`, whatever $s.2$ and $z$ are: the mass at $x+1$ is $\min(a,b)+(a-b)_+=a$, and the mass at $x$ is $(b-a)_++(1-\max(a,b))=1-a$. So the first marginal of `ssaTickPow` is `jumpPow m`. The pair (exact state, counter) is then itself a Markov chain with step $(x,c)\mapsto(\mathrm{jumpPow}_m x,\,c+m)$, $m\sim\mathrm{Poi}(\Lambda h)$. The result follows from Chapman–Kolmogorov and $\mathrm{Poi}(r)*\mathrm{Poi}(r')=\mathrm{Poi}(r+r')$.
- **Numerics.** The maximum error is at most $1.1\times10^{-16}$ for $h=0.3$, $n=0,\dots,3$ and for $h=T/N$, $N=1,2,4$.
- **`hΛ` is genuinely needed.** With $\Lambda=1$, $\lambda(0)=0.3$, $\lambda(1)=3$ and $n=2$, the two sides differ by $0.081$ (section B′). The coarse rate $b$ exceeds 1 and puts extra mass on "exact stays".
- **Vacuity.** Not vacuous. Example: $\lambda(x)=1+0.9\sin(1.7x+0.3)$, $\Lambda=2$, $h=0.3$, $x_0=0$.
- **Junk.** None. If $\Lambda=0$ then $\lambda\equiv0$; the $0/0=0$ inside `ssaTick` is never used because $\mathrm{Poi}(0)=\delta_0$, and both sides equal $\delta_{(x_0,0)}$ (section F).
- **Standard fact.** Uniformisation (Jensen's method): the number of Poisson ticks is $\mathrm{Poi}(\Lambda t)$, and the state given $k$ ticks has law $P^k$.

## 5. `ssaChainCount_marginals` (theorem)

**Rendering.** Assume $\lambda\le\Lambda$ pointwise, $T\in\mathbb R_{\ge0}$, $x_0\in\mathbb N$ and $N\in\mathbb N$ with $0<N$. Let $\mu=$ `ssaChainCount lam Λ (T/↑N) x₀ N`, i.e. $N$ steps of length $T/N$ in $\mathbb R_{\ge0}$. Then:
- (i) $\mu$ is a probability measure;
- (ii) $\mu\circ\mathrm{fst}^{-1}=$ `ssaChain (T/N) x₀ N`;
- (iii) the counter has law $\mathrm{Poi}(\Lambda T)$;
- (iv) (exact state, counter) has law $\sum_k\mathrm{Poi}(\Lambda T)\{k\}\,\mathrm{jumpPow}_k(x_0)\otimes\delta_k$;
- (v) the counter, as a real function, is in $L^2(\mu)$;
- (vi) $\int u.2\,d\mu=\Lambda T$ (in $\mathbb R$, as `↑Λ * ↑T`);
- (vii) $\operatorname{Var}_\mu(u.2)=\Lambda T$.

**Assessment.**
- **True.**
  - (i): under the bound, `ssaTick` has mass $\max(a,b)+(1-\max(a,b))=1$, and Poisson binds and maps keep probability measures.
  - (ii) is theorem 3.
  - (iii) and (iv) are theorem 4 with $n=N$, using $N\cdot(\Lambda\cdot T/N)=\Lambda T$ for $N>0$.
  - (v)–(vii) are the Poisson moments.
- **Numerics.** Mass $1.000000000000$, $\mathbb E K=1.6$ and $\operatorname{Var}K=1.6$ for $\Lambda T=1.6$, $N=1,2,4$.
- **Junk.** None. `variance` is the real part of `evariance`, which would be the junk $0$ only if $u.2\notin L^2$; (v) rules that out. $T/N$ never divides by zero because of `hN`. `hN` is needed: for $N=0$ the counter is $\equiv0$ (section B″).
- **Edge cases.** For $\Lambda T=0$ all claims hold genuinely ($\delta_0$, mean 0, variance 0).
- **Vacuity.** Not vacuous. Example: $\lambda(x)=1+0.9\sin(1.7x+0.3)$, $\Lambda=2$, $T=0.8$, $N=4$.
- **Standard fact.** Mean and variance of a Poisson variable, plus uniformisation.

## 6. `ssaLevelCountLaw` (def)

**Rendering.** The level-$\ell$ law with a counter:
- if $\ell\le L$: the image of `tauLevelLaw T x₀ ℓ` under $q\mapsto(q,0)$, so the $\tau$-leap levels carry counter $0$;
- if $\ell\ge L+1$: `ssaChainCount lam Λ (T/2^L) x₀ 2^L`, i.e. $2^L$ steps of length $T/2^L$ (in $\mathbb R_{\ge0}$, with $(2:\mathbb R_{\ge0})^L\ge1$).

**Assessment.** The definition is sound and has no division by zero. It is a probability measure exactly when `ssaChainCount` is, which holds under `hΛ` but is not guaranteed without it.

## 7. `ssaCountInputLaw` (def)

**Rendering.** `Measure.infinitePi (ssaLevelCountLaw lam Λ T x₀ L)`: the law on $\mathbb N\to(\mathbb N\times\mathbb N)\times\mathbb N$ of independent coordinates, coordinate $\ell$ having law `ssaLevelCountLaw … ℓ`. This is Mathlib's convention: the measure is the genuine product if every factor is a probability measure, and the zero measure otherwise.

**Assessment.** The junk branch is reachable only without `hΛ`. Every theorem that uses this definition assumes `hΛ`, and theorems 9 and 11 assert `IsProbabilityMeasure`.

## 8. `ssaSampleCost` (def)

**Rendering.** $\mathrm{cost}_{L,\ell}(y)=2^\ell$ if $\ell\le L$, and $2^L+(y\,\ell).2$ otherwise (the counter read from coordinate $\ell$ of the same sample vector $y$, cast to $\mathbb R$).

**Assessment.** Sound. It is a cost model: the $\tau$-leap levels cost $2^\ell$ deterministically (only fine steps are counted), and the exact level costs $2^L$ $\tau$ steps plus all uniformisation ticks.

## 9. `ssa_exact_sample_cost` (theorem)

**Rendering.** Assume $\lambda\le\Lambda$. For all $T$, $x_0$ and $L$, let $\nu=$ `ssaCountInputLaw lam Λ T x₀ L`. Then:
- (i) $\nu$ is a probability measure;
- (ii) coordinate $L+1$ under $\nu$ has law `ssaChainCount (T/2^L) x₀ 2^L`;
- (iii) the counter of that law is $\mathrm{Poi}(\Lambda T)$;
- (iv) $y\mapsto 2^L+(y(L{+}1)).2$ is in $L^2(\nu)$;
- (v) its mean is $2^L+\Lambda T$;
- (vi) its variance is $\Lambda T$.

**Assessment.**
- **True.**
  - (i): every factor is a probability measure (the $\tau$ levels are Poisson binds and maps; the SSA level is theorem 5(i) with $N=2^L$). So `infinitePi` takes its genuine branch and is a probability measure.
  - (ii) follows from `infinitePi_map_eval`, using $L+1>L$.
  - (iii) is theorem 5(iii) with $N=2^L$, using $T/(2{:}\mathbb R_{\ge0})^L=T/\uparrow(2^L)$.
  - (iv)–(vi) are Poisson moments shifted by a constant.
- **Numerics.** $\mathbb E=2^L+1.6$ and $\operatorname{Var}=1.6$ for $L=0,1,2$ (section D).
- **Junk.** None. Integrability is asserted, and the variance is genuine.
- **Vacuity.** Not vacuous. Example: $L=2$ with the $\lambda,\Lambda,T$ above.
- **Standard fact.** Expected cost of a uniformised exact (SSA-type) path: $\Lambda T$ ticks on average.

## 10. `ssaTotalCost_moments` (theorem)

**Rendering.** Assume $\lambda\le\Lambda$. For all $T,x_0,L$ and an arbitrary $N:\mathbb N\to\mathbb N$ (zeros allowed), let $P=\bigotimes_{p\in\mathbb N\times\mathbb N}\nu$, an i.i.d. sample vector $x_p$ for each index $p=(\ell,n)$. Define
$$C(x)=\sum_{\ell=0}^{L+1}\sum_{n<N_\ell}\mathrm{cost}_{L,\ell}(x_{(\ell,n)}),$$
where the cost for $\ell=L+1$ is $2^L+(x_{(L+1,n)}(L{+}1)).2$. Then $C\in L^2(P)$,
$$\mathbb E C=\Big(\sum_{\ell=0}^{L}N_\ell 2^\ell\Big)+N_{L+1}(2^L+\Lambda T),\qquad \operatorname{Var}C=N_{L+1}\Lambda T.$$
The bracketing is the actual parse, checked by `Eq.refl` in `scratch2.lean`.

**Assessment.**
- **True.** $C=\text{const}+\sum_{n<N_{L+1}}K_n$, where the $K_n$ are counters taken from distinct coordinates $(L{+}1,n)$ of the product, hence i.i.d. $\mathrm{Poi}(\Lambda T)$. Their sum is $\mathrm{Poi}(N_{L+1}\Lambda T)$.
- **Junk.** None. If $P$ were the junk $0$, the mean identity would fail for nonzero $N$, so the statement is not trivialised. For $N\equiv0$ both sides are genuinely 0.
- **Vacuity.** Not vacuous. Example: $N\equiv3$, $L=2$.
- **Standard fact.** Mean and variance of a sum of independent Poisson variables plus constants.

## 11. `ssa_mlmc_complexity_random_cost` (theorem)

**Rendering.** Assume $\lambda\le\Lambda$ and $\Phi:\mathbb N\to\mathbb R$ with $|\Phi|\le M$. For every $L\in\mathbb N$, with $P=\bigotimes_{p\in\mathbb N\times\mathbb N}$ `ssaCountInputLaw L`:
- (i) $P$ is a probability measure.
- (ii) The image of $P$ under $x\mapsto(p,\ell)\mapsto(x\,p\,\ell).1$, which forgets every counter, is $\bigotimes_p$ `ssaInputLaw L`.
- (iii) $\exists c>0$, which may depend on $\lambda,\Lambda,T,x_0,\Phi,M,L$ but not on $\varepsilon$, such that $\forall\varepsilon\in(0,1]$ $\exists N:\mathbb N\to\mathbb N$ with $N_\ell\ge1$ for all $\ell$ satisfying the following. Let
  $$\hat Y(x)=\sum_{\ell=0}^{L+1}\frac1{N_\ell}\sum_{n<N_\ell}Y_\ell\big(x_{(\ell,n)}\big),$$
  where $Y_\ell$ is `ssaCorrection Φ L ℓ` applied to the state part of the sample vector:
  - $Y_0=\Phi(X^{(0)})$;
  - $Y_\ell=\Phi(\text{fine})-\Phi(\text{coarse})$ of the coupled $\tau$-leap pair, for $1\le\ell\le L$;
  - $Y_{L+1}=\Phi(\text{exact})-\Phi(\tau\text{-leap with step }T/2^L)$ of the SSA-coupled pair.

  Let $\mu^*=\int\Phi\,d\,\mathrm{exactLaw}(T)$. Then:
  - (a) $(\hat Y-\mu^*)^2$ is integrable and $\mathbb E(\hat Y-\mu^*)^2<\varepsilon^2$;
  - (b) $C$ (as in theorem 10, with the same $N$) is integrable and $\mathbb E C\le c/\varepsilon^2$;
  - (c) $P\{C\ge 2c/\varepsilon^2\}\le\varepsilon^2/c$.

**Assessment.**
- **True.**
  - *Unbiasedness.* The sum telescopes: the fine marginal of level $\ell$ equals the coarse marginal of level $\ell+1$; the coarse marginal of the SSA pair equals the fine marginal of level $L$; and the exact marginal is `exactLaw T` by theorem 5(iv). Numerically, the bias is at most $1.1\times10^{-16}$ for $L=0,1,2$ (section C).
  - *MSE.* $\mathbb E(\hat Y-\mu^*)^2=\sum_\ell V_\ell/N_\ell\le4M^2\sum_\ell 1/N_\ell$. Take $N_\ell=\lceil4(L{+}2)M^2/\varepsilon^2\rceil+1\le A/\varepsilon^2$ with $A=4(L{+}2)M^2+2$ (using $\varepsilon\le1$). Then the MSE is below $\varepsilon^2$.
  - *Mean cost.* $\mathbb E C\le A\,(2^{L+1}-1+2^L+\Lambda T)/\varepsilon^2=:c/\varepsilon^2$.
  - *Tail.* $\operatorname{Var}C=N_{L+1}\Lambda T\le\mathbb E C\le c/\varepsilon^2$, and $\{C\ge2c/\varepsilon^2\}\subseteq\{C-\mathbb EC\ge c/\varepsilon^2\}$. Chebyshev gives the bound $(c/\varepsilon^2)/(c/\varepsilon^2)^2=\varepsilon^2/c$.
  - Section E checks MSE, $\mathbb E C$ and the exact Poisson tail for $\varepsilon\in\{1,0.5,0.1,0.03\}$.
  - (ii) holds coordinatewise: $(\tau\text{-law}\otimes\delta_0)\circ\mathrm{fst}^{-1}=\tau$-law, and theorem 3 handles the SSA level. Then use `infinitePi` of maps.
- **The cost is attached to the estimator's own sample** (main point 2).
- **Junk.** None.
  - $N_\ell\ge1$ is asserted, so blockMean's $0^{-1}=0$ never appears.
  - $P$ is a probability measure by (i).
  - Both integrability statements are asserted.
  - `exactLaw` is a probability measure under `hΛ` and $\Phi$ is bounded, so $\mu^*$ is a genuine expectation.
  - $c>0$, so `ENNReal.ofReal (ε²/c)` is a genuine positive bound.
- **Vacuity.** Not vacuous. Example: $\lambda(x)=1+0.9\sin(1.7x+0.3)$, $\Lambda=2$, $T=0.8$, $x_0=0$, $L=2$, $\Phi(x)=\cos(0.9x)+0.3\,(x\bmod3)$, $M=1.6$.
- **Remarks.**
  - The constant $c$ depends on $L$. This is the "unbiased estimator gives $O(\varepsilon^{-2})$" statement for each fixed $L$. It is weaker than an optimised complexity statement: no $L(\varepsilon)$, no dependence on $L$, no comparison with plain SSA Monte Carlo.
  - Bounded $\Phi$ is a stronger assumption than needed; finite second moments would do.
  - Bounded propensity is assumed (main point 6).
- **Standard result.** The unbiased multilevel Monte Carlo estimator of Anderson and Higham (2012), with an exact SSA final level coupled to $\tau$-leaping, written here in uniformised form. The cost tail bound is Chebyshev's inequality.
