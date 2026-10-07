# Blind read-back report: R19 `tauexact`

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round18/packet_R19_tauexact.lean` (relative to the scratchpad) |
| declarations audited | 28: 13 theorems, 3 definitions from the module, 12 appended definitions |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round18/work_R19/` (`*.py` with `*.out`; scratch Lean files `check*.lean` with `check*.out`) |

Work files:
- Python: `common.py` (a literal re-implementation of the packet definitions on a truncated state space), `s1_uniformisation_vs_expm`, `s2_equations`, `s3_weak_error`, `s4_mlmc_levels`, `s5_weak_error_adversarial`, `s6_semigroup` and `s7_mlmc_cost`.
- Lean:
  - `check1`: `#check` of all 13 statements and `#print axioms`.
  - `check2`/`check3`: conventions and instance search. In `check3`, lines 4–10 compile and the errors after them are the expected instance-search failures.
  - `check4`/`check5`: the auditor's own proofs that every level law is a probability measure and that the MSE integrand is measurable. `check5` contains `check4` and adds three lemmas. It compiles, and its axioms are only `propext`, `Classical.choice` and `Quot.sound`.

All 13 statements elaborate exactly as printed in the packet (`check1.out`). `κ ∘ₘ μ` is `μ.bind κ`.

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| D1 | `jumpKernel` | def | faithful (uniformised kernel $I+Q/\Lambda$, under $\lambda\le\Lambda$) | – | – (if $\Lambda=0$, then $\lambda/0=0$ gives $\delta_x$, which is correct because then $\lambda\equiv0$) |
| D2 | `jumpPow` | def | faithful ($P^n$) | – | – |
| D3 | `exactLaw` | def | faithful ($e^{tQ}$ by uniformisation, checked numerically to $10^{-30}$) | – | – |
| D4 | `blockMean` | def | faithful | – | $0^{-1}=0$ only when $N=0$, which the theorem excludes |
| D5 | `fineCoarseDiff` | def | faithful | – | – |
| D6 | `tauStep` | def | faithful | – | – |
| D7 | `tauChain` | def | faithful | – | – |
| D8 | `tauInputLaw` | def | faithful, but `infinitePi` is $0$ unless every factor is a probability measure (they all are, checked in Lean) | – | no |
| D9 | `tauFine` | def | faithful | – | – |
| D10 | `tauCoarse` | def | faithful | – | – |
| D11 | `tauLevelLaw` | def | faithful (the marginals were checked numerically) | – | – |
| D12 | `coupledChain` | def | faithful | – | – |
| D13 | `coupledTwoStep` | def | faithful (fine: two $h$-steps; coarse: one $2h$-step) | – | – |
| D14 | `coupledIncr` | def | faithful (common-part Poisson coupling) | – | – |
| D15 | `couplePair` | def | faithful | – | – |
| 1 | `isProbabilityMeasure_exactLaw` | theorem | TRUE | no | no |
| 2 | `exactLaw_add` | theorem | TRUE | no | no (`hΛ` is not needed) |
| 3 | `exactLaw_tauStep_le` | theorem | TRUE (the sharp constant is about 1; the theorem states 2) | no | no |
| 4 | `tauLeaping_weak_error_exact` | theorem | TRUE | no | no |
| 5 | `tauLeaping_mlmc_exact` | theorem | TRUE | no | no (checked: the product measure is a probability measure and the integrand is measurable and bounded) |
| 6 | `exactLaw_eq_of_bound` | theorem | TRUE | no | no |
| 7 | `exactLaw_const` | theorem | TRUE | no | no |
| 8 | `exactLaw_generator` | theorem | TRUE (the sharp constant is about 2; the theorem states 5) | no | no |
| 9 | `exactLaw_hasDerivWithinAt_zero` | theorem | TRUE | no | no |
| 10 | `exactLaw_backward_equation` | theorem | TRUE | no | no |
| 11 | `exactLaw_forward_equation` | theorem | TRUE | no | no |
| 12 | `exactLaw_master_equation` | theorem | TRUE | no | no |
| 13 | `exactLaw_unique` | theorem | TRUE | no (example: $Q=$ `exactLaw`, $C=5\Lambda^2$) | no |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement was found.** The uniformised law `exactLaw` agrees with $e^{tQ}$ to about $10^{-30}$. Here $Q(x,x+1)=\lambda(x)$ and $Q(x,x)=-\lambda(x)$, and $e^{tQ}$ was computed with the mpmath `expm` on a truncated $\mathbb N$ (`s1`). The checks covered 4 rate functions, $t\in\{0.01,0.3,1,2.5\}$ and starting points $x\in\{0,1,3\}$.
   - The law does not depend on $\Lambda$: rates $\Lambda\in\{\sup\lambda,\ 2\sup\lambda,\ \sup\lambda+0.37,\ 10\}$ give the same law.
   - The master, forward and backward equations hold, with residuals of about $10^{-40}$ (`s2`). The semigroup identity holds (`s6`).
2. **A junk-value hazard in #5 is real but does not materialise.** Mathlib's `Measure.infinitePi μ` is defined as `if ∀ i, IsProbabilityMeasure (μ i) then … else 0`, and the repository has no global `IsProbabilityMeasure` instance for `tauLevelLaw`, `coupledChain`, `tauChain` or `tauInputLaw` (`check3`).
   - If any level law failed to be a probability measure, the MSE would be $\int\cdot\,d0=0<\varepsilon^2$ and #5 would be trivially true.
   - I proved in scratch Lean, independently, that every `tauLevelLaw` is a probability measure, so the outer `infinitePi` is one too. I also proved the MSE integrand measurable (`check5`). It is bounded, so the integral is the genuine mean-square error.
3. **The hypothesis `hΛ` ($\lambda\le\Lambda$) is essential for #1 and everything that depends on it.** Without it, `jumpKernel` has mass $\lambda(x)/\Lambda>1$, because the truncated subtraction makes $1-\lambda/\Lambda=0$. For constant $\lambda=3$ and $\Lambda=1$ the law has mass $e^{(\lambda-\Lambda)t}$: $e^2$ at $t=1$ (`s1`).
   - In #2 the hypothesis is superfluous: the semigroup identity also holds when it is violated (`s6`). This is harmless.
4. **The constants are true with margin.**
   - One-step tau error (#3): $\sup\|\cdot\|_1/(\Lambda h)^2\approx0.99$, against the stated 2. My analytic bound is $1.5$.
   - Generator remainder (#8): about $1.99$, against the stated 5.
   - Global weak error (#4), as error divided by the bound: at most $0.035$ for $\min(x,3)$ and at most $0.48$ for adversarial rate patterns (`s3`, `s5`). The error is exactly 0 for constant rates.
   - Weak order 1 is sharp: $N\cdot\mathrm{err}\to0.63$.
5. **The payoffs are any functions $\mathbb N\to\mathbb R$ bounded by $M$.** Measurability is automatic, because the σ-algebra on $\mathbb N$ is $\top$ (checked by `rfl`). $M\ge0$ follows from the hypotheses.
   - Boundedness is genuinely assumed. #3–#5 therefore do not cover the usual quantity of interest, $\Phi(x)=x$ (the mean copy number).
   - The model is also narrow: one birth channel, jumps of $+1$, and globally bounded rates.
6. **The quantifier order in #5 is the standard one.** $c_4>0$ is chosen after $(\lambda,\Lambda,T,x_0,\Phi,M)$ and before $\varepsilon$; $L$ and $N$ depend on $\varepsilon$.
   - The bias is measured against the exact chain, not against the finest tau-leaping level.
   - Cost is $\sum N_\ell2^\ell$.
   - Rates measured for $\min(x,3)$: $\beta=\gamma=1$, with $V_\ell2^\ell\to1.79$ for $\Phi=(-1)^x$ (`s4`). With rigorous a-priori bounds, $\text{cost}/(\varepsilon^{-2}\log^2\varepsilon)$ stays at most $832$ and decreases over $\varepsilon\in[6.5\cdot10^{-13},0.18]$ (`s7`).
7. **The uniqueness theorem (#13) assumes a uniform quantitative expansion.** It assumes $|Q_tf(x)-f(x)-t\lambda(x)\Delta f(x)|\le Ct^2M$ for all bounded $f$, all $x$ and all $t\le1$, with one constant $C$.
   - That is stronger than "solves the Kolmogorov equations". It is a legitimate characterisation for bounded rates, but it should be described that way.
8. **The derivative statements correctly use $s\mapsto$ `exactLaw` $(s.\mathrm{toNNReal})$.** At $0$ only a right derivative is claimed (`Set.Ici 0`), and for $t>0$ a two-sided `HasDerivAt`. The function is constant for $s<0$, so a two-sided derivative at 0 would generally be false; the packet does not claim one.

---

## Definitions

### D1 `jumpKernel lam Λ x`
**Rendering.**
$$K(x,\cdot)=p_x\,\delta_{x+1}+(1\dot-p_x)\,\delta_x,\qquad p_x=\lambda(x)/\Lambda\in\mathbb R_{\ge0}.$$
Here $\lambda(x)/0=0$ and $1\dot-p=\max(1-p,0)$ (`ℝ≥0`). The scalars act on measures through the coercion to `ℝ≥0∞`; `(c • μ) s = ↑c * μ s` is checked by `rfl`.
- If $0<\Lambda$ and $\lambda(x)\le\Lambda$, this is the uniformised kernel $P=I+Q/\Lambda$ of the pure-birth chain.
- If $\Lambda=0$ it is $\delta_x$.
- If $\lambda(x)>\Lambda$ it is $(\lambda(x)/\Lambda)\delta_{x+1}$, whose mass exceeds 1.

**Assessment.** The definition is faithful under `hΛ`. I proved its probability property in Lean myself (`aud_jumpKernel` in `check5`).

### D2 `jumpPow lam Λ n x`
**Rendering.** $P^0(x,\cdot)=\delta_x$ and $P^{n+1}(x,\cdot)=\sum_yP^n(x,y)K(y,\cdot)$, which is `bind`. It is the $n$-step kernel of the uniformised jump chain.

### D3 `exactLaw lam Λ t x`
**Rendering.**
$$P_t(x,\cdot)=\sum_{n\ge0}e^{-\Lambda t}\frac{(\Lambda t)^n}{n!}P^n(x,\cdot)$$
This is Mathlib's `poissonMeasure (Λ*t)` bound with $n\mapsto P^n(x,\cdot)$, the uniformisation (Jensen) formula $e^{tQ}=e^{-\Lambda t}e^{\Lambda tP}$.

**Assessment.** It is faithful: it agrees with `mpmath.expm(t Q)` to $\le1.7\cdot10^{-30}$ in all tested cases (`s1`). `poissonMeasure 0`$=\delta_0$, since Mathlib uses $0^0=1$, so $P_0(x,\cdot)=\delta_x$.

### D4 `blockMean f ω i N x`
**Rendering.** $N^{-1}\sum_{n<N}f_i(\omega_{(i,n)}(x))$ (with $0^{-1}=0$ in ℝ). It is the sample mean of $N$ samples at level $i$.

### D5 `fineCoarseDiff Pf Pc ℓ`
**Rendering.** For $\ell=0$ it is $Pf_0$; for $\ell+1$ it is $y\mapsto Pf_{\ell+1}(y)-Pc_\ell(y)$. These are the MLMC correction terms.

### D6 `tauStep lam h x`
**Rendering.** The law of $x+\mathrm{Poi}(h\lambda(x))$: one tau-leaping step.

### D7 `tauChain lam h x₀ n`
**Rendering.** The law after $n$ tau-leaping steps of size $h$ started at $x_0$ (iterated `bind`).

### D8 `tauInputLaw lam T x₀`
**Rendering.** `Measure.infinitePi` over levels $\ell\in\mathbb N$ of `tauLevelLaw ℓ`: a measure on $\mathbb N\to\mathbb N\times\mathbb N$ with independent levels.

**Assessment.** Mathlib defines `infinitePi` as `0` unless every factor is a probability measure. Every factor is one (own Lean proof `aud_tauLevelLaw` and `aud_outer`, `check5`), so this is the genuine product.

### D9, D10 `tauFine`, `tauCoarse`
**Rendering.** `tauFine Φ ℓ y` $=\Phi((y_\ell)_1)$ and `tauCoarse Φ ℓ y` $=\Phi((y_{\ell+1})_2)$. So `fineCoarseDiff` gives $D_0(y)=\Phi((y_0)_1)$ and $D_{\ell+1}(y)=\Phi((y_{\ell+1})_1)-\Phi((y_{\ell+1})_2)$. A correction uses the fine and coarse paths of the same coupled pair.

### D11 `tauLevelLaw lam T x₀ ℓ`
**Rendering.**
- Level 0 is the law of $(X,X)$ with $X\sim$ one tau step of size $T$.
- Level $\ell+1$ is `coupledChain` with $h=T/2^{\ell+1}$ (in `ℝ≥0`) and $2^\ell$ coupled double steps. The fine path makes $2^{\ell+1}$ steps of size $h$ and the coarse path $2^\ell$ steps of size $2h$.

**Assessment.** The level-$\ell$ coarse marginal has the law of the level-$(\ell-1)$ fine path, so the sum telescopes. Numerically, the fine and coarse marginals match `tauChain` to $\le4\cdot10^{-15}$ for $\ell=1..7$ (`s4`).

### D12 `coupledChain`
**Rendering.** `coupledTwoStep` iterated $k$ times from $(x_0,x_0)$.

### D13 `coupledTwoStep lam h (s₁,s₂)`
**Rendering.** Draw $(i,j)\sim$ `coupledIncr`$(h\lambda(s_1),h\lambda(s_2))$, then $(i',j')\sim$ `coupledIncr`$(h\lambda(s_1+i),h\lambda(s_2))$, and output $(s_1+i+i',\,s_2+j+j')$.
- The fine path makes two $h$-steps with the rate updated in between.
- On the coarse side, $j'\sim\mathrm{Poi}(h\lambda(s_2))$ is conditionally independent of $(i,j)$, so $j+j'\sim\mathrm{Poi}(2h\lambda(s_2))$: one coarse step.

**Assessment.** Faithful.

### D14 `coupledIncr a b`
**Rendering.** The law of `couplePair a b (P₁,P₂)` with $P_1\sim\mathrm{Poi}(\min(a,b))$ and $P_2\sim\mathrm{Poi}(\max-\min)$ independent. The truncated subtraction is harmless here. The marginals are $\mathrm{Poi}(a)$ and $\mathrm{Poi}(b)$: the standard common-part coupling, as in the Anderson–Higham split-Poisson coupling.

### D15 `couplePair a b (p₁,p₂)`
**Rendering.** $(p_1+[b<a]p_2,\;p_1+[a<b]p_2)$.

---

## Theorems

### 1. `isProbabilityMeasure_exactLaw`
**Rendering.** For $\lambda:\mathbb N\to\mathbb R_{\ge0}$ and $\Lambda\in\mathbb R_{\ge0}$ with $\lambda(x)\le\Lambda$ for all $x$, and for all $t\ge0$ and $x\in\mathbb N$, $P_t(x,\cdot)$ is a probability measure.

**Assessment.**
- **Truth.** True. Under `hΛ`, $p_x\le1$ (or $p_x=0$ when $\Lambda=0$), so $K$ is stochastic, $P^n$ is stochastic, and a Poisson mixture of probability measures is a probability measure. Numerically the mass is 1 to $10^{-20}$.
- **The hypothesis is necessary.** For $\lambda\equiv3$, $\Lambda=1$ and $t=1$ the mass is $e^2=7.389$ (`s1`).
- **Vacuity.** Not vacuous: $\lambda=\min(x,3)$, $\Lambda=3$.
- **Junk values.** None.
- **Standard fact.** Uniformisation produces a Markov kernel.

### 2. `exactLaw_add`
**Rendering.** Under `hΛ`, for all $s,t\ge0$ and $x$: $P_{s+t}(x,\cdot)=\sum_yP_s(x,y)P_t(y,\cdot)$.

**Assessment.**
- **Truth.** True: $\mathrm{Poi}(\Lambda s)*\mathrm{Poi}(\Lambda t)=\mathrm{Poi}(\Lambda(s+t))$ and $P^{m+n}=P^mP^n$. It is verified numerically to $10^{-30}$ (`s6`).
- **Hypothesis stronger than needed.** `hΛ` is not needed: the identity is the semigroup law of $e^{\Lambda t(P-I)}$ for any nonnegative kernel. `s6` confirms it with $\lambda>\Lambda$ (masses $7.39$, $148.4$). This is harmless.
- **Vacuity.** Not vacuous.
- **Junk values.** None.
- **Standard fact.** The Chapman–Kolmogorov (semigroup) property.

### 3. `exactLaw_tauStep_le`
**Rendering.** Under `hΛ`, for every $f:\mathbb N\to\mathbb R$ with $|f|\le M$, every $h\ge0$ and every $x$:
$$\big|\mathbb E_xf(X_h)-\mathbb Ef(x+\mathrm{Poi}(h\lambda(x)))\big|\le2(\Lambda h)^2M.$$

**Assessment.**
- **Truth.** True. Both laws give mass $e^{-h\lambda(x)}$ to $x$. Each gives mass $\le(\Lambda h)^2/2$ to $[x+2,\infty)$, since the exact chain needs at least two uniformised events to get there. So $\|\mu-\nu\|_1\le1.5(\Lambda h)^2$. For $\Lambda h\ge1$ the left side is at most $2M$ anyway.
- **Numerics.** The sharp constant is $\sup\|\mu-\nu\|_1/(\Lambda h)^2\approx0.9934$ at $h=0.01$ and tends to 1 as $h\to0$, attained for $\lambda(x)=\Lambda$, $\lambda(x+1)=0$ (`s3`).
- **Vacuity.** Not vacuous.
- **Junk values.** None. $f$ is bounded and the measures are probability measures, so the integrals are genuine.
- **Standard fact.** The $O(h^2)$ local weak error of tau-leaping.

### 4. `tauLeaping_weak_error_exact`
**Rendering.** Under `hΛ`, for every $\Phi$ with $|\Phi|\le M$, every $T\ge0$, $x_0$ and $N\ge1$:
$$\big|\mathbb E\,\Phi(Y_N^{(T/N)})-\mathbb E_{x_0}\Phi(X_T)\big|\le\frac{2\Lambda^2T^2M}{N}.$$
Here $Y^{(h)}$ is tau-leaping with step $h=T/N$, computed in `ℝ≥0`.

**Assessment.**
- **Truth.** True by telescoping, $\tau_h^N-P_h^N=\sum_k\tau_h^k(\tau_h-P_h)P_h^{N-1-k}$. Each term is $\le2(\Lambda T/N)^2M$ by #3, since $|P_h^j\Phi|\le M$. It also uses $N\cdot(T/N)=T$ in `ℝ≥0` (with $N>0$) and #2.
- **Numerics** (`s3`, `s5`).
  - Constant rate: error 0 to $10^{-20}$. Tau-leaping is exact here.
  - $\lambda=\min(x,3)$, $x_0\in\{1,2\}$: error/bound $\le0.035$ and $N\cdot\mathrm{err}\to0.63$, so order 1 is sharp.
  - Adversarial periodic rates: error/bound $\le0.48$.
- **Vacuity.** Not vacuous.
- **Junk values.** None.
- **Scope.** Bounded payoffs only.
- **Standard fact.** First-order weak convergence of tau-leaping (Rathinam et al.; Li 2007; Anderson–Ganguly–Kurtz 2011), here for a single birth channel with bounded rates.

### 5. `tauLeaping_mlmc_exact`
**Rendering.** For every $\lambda\le\Lambda$, $T\ge0$, $x_0$ and $\Phi$ with $|\Phi|\le M$ there is $c_4>0$, depending only on these data, with the following property. For every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with all $N_\ell\ge1$ such that two conditions hold:
1. The mean-square error is small:
$$\mathbb E\Big[\Big(\sum_{\ell=0}^L\frac1{N_\ell}\sum_{n<N_\ell}D_\ell(Y^{(\ell,n)})-\mathbb E_{x_0}\Phi(X_T)\Big)^2\Big]<\varepsilon^2,$$
where the $Y^{(\ell,n)}$, $(\ell,n)\in\mathbb N^2$, are i.i.d. with law `tauInputLaw`, and $D_\ell$ are the corrections from D9 and D10.
2. The cost is bounded: $\sum_{\ell\le L}N_\ell2^\ell\le c_4\,\varepsilon^{-2}(\log\varepsilon)^2$. `Real.log ε ^ 2` parses as $(\log\varepsilon)^2$ (checked by `rfl`), and $\varepsilon^{-2}$ is `rpow` with $\varepsilon>0$.

**Assessment.**
- **Truth.** True. This is Giles' MLMC complexity theorem with $\alpha=1$ (#4 with $N=2^L$: bias $\le2\Lambda^2T^2M2^{-L}$), $\beta=1$ and $\gamma=1$, which gives $\varepsilon^{-2}(\log\varepsilon)^2$. The $\beta=1$ comes from the coupling: $P(\text{fine}\ne\text{coarse})\le\Lambda^2T^2/2^{\ell+1}$, because a discrepancy needs a fine jump in the first substep and a mismatch in the second, each with probability $\le h\Lambda$, over $2^{\ell-1}$ coarse steps. So $V_\ell\le4M^2\Lambda^2T^22^{-\ell-1}$.
- **Numerics.**
  - $2^\ell P(\text{fine}\ne\text{coarse})\to0.51$ and $2^\ell V_\ell\to1.79$ for $\Phi=(-1)^x$ (`s4`).
  - With the rigorous bounds and the standard choice of $L$ and $N_\ell$, MSE$/\varepsilon^2\approx0.65$. $\text{cost}/(\varepsilon^{-2}\log^2\varepsilon)\le832$ over $\varepsilon\in[6.5\cdot10^{-13},0.18]$ and decreases, so a single $c_4$ works (`s7`).
- **Quantifier order.** $\exists c_4$ comes before $\forall\varepsilon$, which is correct and uniform. The condition $N_\ell>0$ for all $\ell$, including $\ell>L$, is harmless.
- **Junk values.** None.
  - (a) If some level law were not a probability measure, `infinitePi` would be the zero measure and the MSE would be $0$. Ruled out by my own Lean proof (`aud_outer`).
  - (b) A non-integrable integrand would make the Bochner integral $0$. Ruled out: the integrand is measurable (own Lean proof `aud_est_meas`) and bounded by $((L+1)2M+|\mathbb E\Phi|)^2$.
  - (c) $(\log\varepsilon)^2\ge1$ on the allowed range.
- **Vacuity.** Not vacuous.
- **Scope.** The target is the exact chain, which is stronger than targeting the finest discretisation. Payoffs must be bounded, so $\Phi(x)=x$ is not covered.
- **Standard fact.** Giles (2008); Anderson–Higham (2012), tau-leaping MLMC.

### 6. `exactLaw_eq_of_bound`
**Rendering.** If $\lambda\le\Lambda$ and $\lambda\le\Lambda'$, then $P^{(\Lambda)}_t(x,\cdot)=P^{(\Lambda')}_t(x,\cdot)$ for all $t$ and $x$.

**Assessment.**
- **Truth.** True: both equal $e^{tQ}$. Confirmed for $\Lambda\in\{\sup,2\sup,\sup+0.37,10\}$, and for $\Lambda=0$ against $\Lambda'=4$ with $\lambda\equiv0$, where both are $\delta_x$ (`s1`).
- **Vacuity.** Not vacuous.
- **Junk values.** None.
- **Standard fact.** The uniformisation result does not depend on the uniformisation rate.

### 7. `exactLaw_const`
**Rendering.** For all $\Lambda,t,x$ with no hypothesis: `exactLaw (fun _ => Λ) Λ t x` is the law of $x+\mathrm{Poi}(\Lambda t)$.

**Assessment.**
- **Truth.** True. For $\Lambda>0$, $K=\delta_{x+1}$ (the coefficient $1-1=0$) and $P^n=\delta_{x+n}$. For $\Lambda=0$, $\mathrm{Poi}(0)=\delta_0$ and both sides are $\delta_x$; the kernel value $0/0=0$ is never used. Checked numerically for $\Lambda\in\{0,0.5,2,7\}$.
- **Vacuity and junk values.** Not vacuous; no junk.
- **Standard fact.** The Poisson process.

### 8. `exactLaw_generator`
**Rendering.** Under `hΛ`, for $|f|\le M$, all $t\ge0$ and all $x$:
$$\big|\mathbb E_xf(X_t)-[f(x)+t\lambda(x)(f(x+1)-f(x))]\big|\le5(\Lambda t)^2M.$$

**Assessment.**
- **Truth.** True. Let $a=t\lambda(x)\le u=\Lambda t$ and $\mu=P_t(x,\cdot)$. For $u<1$ the left side is $\le M\big(|e^{-a}-1+a|+|\mu(\{x+1\})-a|+\mu([x+2,\infty))\big)\le M(a^2/2+a^2/2+u^2/2+u^2/2)\le2u^2M$. For $u\ge1$ it is $\le(2+2u)M\le5u^2M$.
- **Numerics.** The sharp constant is about $1.99$ as $t\to0$, for $\lambda(x)=\lambda(x+1)=\Lambda$ (`s3`).
- **Vacuity and junk values.** Not vacuous; no junk.
- **Standard fact.** $P_t=I+tQ+O(t^2)$ for a bounded generator.

### 9. `exactLaw_hasDerivWithinAt_zero`
**Rendering.** Under `hΛ`, for $|f|\le M$: $s\mapsto\mathbb E_xf(X_{s^+})$, with $s^+=$`s.toNNReal`, has right derivative $\lambda(x)(f(x+1)-f(x))=(Qf)(x)$ at $s=0$, within $[0,\infty)$.

**Assessment.**
- **Truth.** True. It follows from #8, since the value at 0 is $f(x)$. Numerically the residual is $10^{-14}$ at $s=10^{-15}$ (`s2`).
- **Use of `toNNReal`.** It is harmless: only $s\ge0$ matters.
- **Vacuity and junk values.** Not vacuous; no junk.
- **Standard fact.** The definition of the generator.

### 10. `exactLaw_backward_equation`
**Rendering.** Under `hΛ`, for $|f|\le M$, all $x$ and $t>0$:
$$\frac{d}{dt}\mathbb E_xf(X_t)=\lambda(x)\big(\mathbb E_{x+1}f(X_t)-\mathbb E_xf(X_t)\big)=(QP_tf)(x).$$
The derivative is two-sided, and `toNNReal` equals the identity near $t$.

**Assessment.**
- **Truth.** True; the residual is $\le10^{-40}$ (`s2`).
- **Vacuity and junk values.** Not vacuous; no junk.
- **Standard fact.** The Kolmogorov backward equation.

### 11. `exactLaw_forward_equation`
**Rendering.** Under `hΛ`, for $|f|\le M$ and $t>0$:
$$\frac{d}{dt}\mathbb E_xf(X_t)=\mathbb E_x\big[\lambda(X_t)(f(X_t+1)-f(X_t))\big]=(P_tQf)(x).$$

**Assessment.**
- **Truth.** True. The integrand is bounded by $2\Lambda M$, so the integral is genuine. The residual is $\le10^{-40}$ (`s2`).
- **Vacuity and junk values.** Not vacuous; no junk.
- **Standard fact.** The Kolmogorov forward equation in weak form.

### 12. `exactLaw_master_equation`
**Rendering.** Under `hΛ`, for $x$ and $t>0$, with $p_t(y)=P_t(x,\{y\})$ given by `.real`, that is `toReal`, which is finite here:
$$\dot p_t(0)=-\lambda(0)p_t(0),\qquad \dot p_t(y+1)=\lambda(y)p_t(y)-\lambda(y+1)p_t(y+1)\quad(\forall y).$$

**Assessment.**
- **Truth.** True; the residual is $\le2.3\cdot10^{-41}$ for $y\le9$ (`s2`). It is the forward equation applied to indicators.
- **Vacuity and junk values.** Not vacuous; no junk.
- **Standard fact.** The pure-birth master equation.

### 13. `exactLaw_unique`
**Rendering.** Under `hΛ`, let $Q:\mathbb R_{\ge0}\to\mathbb N\to\mathrm{Measure}\,\mathbb N$ satisfy three conditions:
1. Every $Q_t(x,\cdot)$ is a probability measure.
2. $Q_{s+t}(x,\cdot)=\sum_yQ_s(x,y)Q_t(y,\cdot)$.
3. For some real $C$, fixed before everything else: for all $f$ and $M$ with $|f|\le M$, all $t$ with $t\le1$ and all $x$, $|Q_tf(x)-f(x)-t\lambda(x)(f(x+1)-f(x))|\le Ct^2M$.

Then $Q_t(x,\cdot)=P_t(x,\cdot)$ for all $t$ and $x$.

**Assessment.**
- **Truth.** True. Take $h=t/n\le1$; then $Q_t-P_t=\sum_kQ_h^k(Q_h-P_h)P_h^{n-1-k}$. Each term is $\le(C+5\Lambda^2)h^2M$ by the hypothesis and #8, so the total is $\le(C+5\Lambda^2)t^2M/n\to0$. Equality on all bounded $f$, including indicators, gives equality of the measures on $\mathbb N$.
- **Vacuity.** Not vacuous: $Q=P$ with $C=5\Lambda^2$, using #1, #2 and #8. Hypotheses with $C<0$ can never be satisfied (take $f\equiv1$, $M=1$, $t=\tfrac12$), which is harmless.
- **Junk values.** None.
- **Unusual hypothesis.** The generator condition is a uniform $O(t^2)$ remainder in sup norm. That is stronger than requiring $Q$ to solve the forward or backward equations. It is a valid uniqueness theorem within this class, but not the textbook "unique solution of the Kolmogorov equations" statement.
- **Standard fact.** A bounded generator determines its semigroup ($e^{tQ}$).
