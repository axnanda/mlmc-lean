# Blind read-back report: packet R39 (SSA / tau-leaping coupling and the unbiased MLMC estimator)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round23/packet_R39_ssa.lean` |
| declarations audited | 10 theorems, plus the 19 definitions they use (8 in the packet's own module, 11 appended from other modules) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round23/work_R39_ssa/` (`check_thinning.py`, `check_ssa.py`, `check_unbiased.py`, `check_complexity.py`, each with its `.out`; `Check.lean` and `Check.out` hold the elaborated statements and `#print axioms`) |

Lean check: `Check.lean` imports `MlmcLean` and `#check`s every theorem with `pp.coercions` and `pp.numericTypes` on. All ten statements elaborate exactly as the packet shows them. `#print axioms` lists only `propext, Classical.choice, Quot.sound` for all ten.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `poisson_thinning` | theorem | true | no | no (`hp` is needed: for $p>1$ the NNReal $1-p=0$ makes it false) |
| 2 | `ssaStep_map_fst` | theorem | true | no | no |
| 3 | `ssaStep_map_snd` | theorem | true | no | no |
| 4 | `ssaChain_marginals` | theorem | true | no | no |
| 5 | `ssaChain_ne_le` | theorem | true (the constant could be 1/2) | no | no |
| 6 | `ssaChain_sq_le` | theorem | true | no | no |
| 7 | `ssaChain_abs_le` | theorem | true (the constants could be 1/2 and 1/4) | no | no |
| 8 | `ssa_mlmc_unbiased` | theorem | true | no | no (it states `IsProbabilityMeasure`, so the measure is not the junk value 0 of `infinitePi`) |
| 9 | `variance_ssaCorrection_exact_le` | theorem | true | no | no. It does not state `IsProbabilityMeasure` itself; if `ssaInputLaw` were 0 it would be trivially true, but under `hΛ` it is a probability measure (this follows from #8) |
| 10 | `ssa_mlmc_complexity` | theorem | true, but **weak**: the constant $c$ may depend on $L$ (and on all other data), so it is the generic $O(\varepsilon^{-2})$ bound for any unbiased, finite-variance estimator | no | no |

## Main points for a human auditor

1. **`ssa_mlmc_complexity` is much weaker than it looks.** $L$ is fixed before $\exists c$, so $c=c(\lambda,\Lambda,T,x_0,\Phi,M,L)$. Since the estimator is exactly unbiased for every $L$, the claim follows from "MSE $=\sum_\ell V_\ell/N_\ell$" with $N_\ell=\lceil K/\varepsilon^2\rceil$. It never uses the decay of the level variances, and it holds equally for $L=0$ (one tau-leap level plus the SSA correction). It says nothing about how $c$ grows with $L$, $\Lambda$ or $T$, and nothing about the MLMC saving. If the docstring or paper claims more (an $L$-uniform constant, an explicit $c$, or an optimal $L$), the Lean statement does not capture it. The real MLMC content of the packet is #9 (top-level variance $O(\Lambda^2T^2 2^{-L})$) together with the cost weight $2^L+\Lambda T$, and #10 does not link them.
2. **Modelling scope (statements true, but narrower than the general SSA/tau-leaping MLMC of Anderson–Higham).**
   - Only a single-species *pure-birth* process: one channel, $x\to x+1$ at rate $\lambda(x)$.
   - The rates must be *uniformly bounded*, $\lambda\le\Lambda$ (`hΛ`). This excludes, for example, linear birth $\lambda(x)=cx$.
   - The test function must be *bounded*, $|\Phi|\le M$. This excludes $\Phi(x)=x$.
   - The "exact" law `exactLaw` is *defined* by uniformisation: a Poisson$(\Lambda t)$ number of ticks, each a jump with probability $\lambda(x)/\Lambda$. That this equals the CTMC transition law is standard (Jensen's uniformisation), but it is not proved in the packet.
   - On the other hand, no Lipschitz condition on $\lambda$ is needed. The $O(h)$ coupling error comes from boundedness alone.
3. **Constants have slack.**
   - #5: the proof gives $P(X\ne Y)\le \Lambda^2T^2/(2N)$. Numerically the ratio to the stated bound is at most $0.39$, tending to $1/2$.
   - #7: the proof gives $\mathbb E|X-Y|\le(\Lambda^2T^2/2+\Lambda^3T^3/4)/N$. Numerically the ratio is at most $0.32$.
   - The constants are not tight, but they are not wrong.
4. **NNReal arithmetic in `ssaTick` is used deliberately, not as a junk value.**
   - `a - b` and `b - a` are the positive parts $(a-b)^+$ and $(b-a)^+$ of a maximal coupling.
   - Under `hΛ`, $\max(a,b)\le1$, so the truncation in `1 - max a b` never triggers.
   - $\Lambda=0$ gives `lam x / 0 = 0`, which is consistent because `hΛ` then forces $\lambda\equiv0$.
5. **Minor points.**
   - In #8 and #10, `hN : ∀ ℓ, 0 < N ℓ` (in #10 it is a conclusion) covers *all* $\ell\in\mathbb N$, although only $\ell\le L+1$ is used. This is harmless.
   - `Measure.infinitePi` is defined in Mathlib as `if (∀ i, IsProbabilityMeasure (μ i)) then … else 0`, so the `IsProbabilityMeasure` conjunct of #8 and #10 has real content: it rules out the zero measure.

---

## Definitions (rendering only)

Throughout, $\lambda=$ `lam` $:\mathbb N\to\mathbb R_{\ge0}$, $\Lambda,h,T\in\mathbb R_{\ge0}$, and divisions and subtractions in $\mathbb R_{\ge0}$ follow NNReal conventions ($x/0=0$, $a-b=\max(a-b,0)$). `μ.bind κ` is $\int\kappa(x)\,\mu(dx)$ (Giry monad). All functions on $\mathbb N$ and $\mathbb N\times\mathbb N$ are measurable (countable, discrete σ-algebras), so every `bind` and `map` here is the honest mixture or push-forward. `poissonMeasure r` $=\sum_n e^{-r}r^n/n!\,\delta_n$ (Mathlib; $0^0=1$, so `Po(0)` $=\delta_0$).

- **`binomialLaw n p`** $=\sum_{k=0}^n\binom nk p^k(1-p)^{n-k}\delta_k$, with $1-p$ truncated at 0 and $0^0=1$. This is Bin$(n,p)$ when $p\le1$.
- **`ssaTick lam Λ z s`**: put $a=\lambda(s_1)/\Lambda$ and $b=\lambda(z)/\Lambda$. One uniformisation tick of the pair $s=(s_1,s_2)$ under the maximal coupling of Bernoulli$(a)$ (the SSA component, at its current state) and Bernoulli$(b)$ (the tau component, with its rate frozen at state $z$). The masses are: $\min(a,b)$ at $(s_1+1,s_2+1)$, $(a-b)^+$ at $(s_1+1,s_2)$, $(b-a)^+$ at $(s_1,s_2+1)$, and $(1-\max(a,b))^+$ at $s$.
- **`ssaTickPow lam Λ z n s`**: the $n$-fold composition of `ssaTick … z`, starting at $\delta_s$.
- **`ssaStep lam Λ h s`** $=\sum_n \mathrm{Po}(\Lambda h)(n)\,$`ssaTickPow lam Λ s.2 n s`: one coupled step of length $h$, with the frozen tau state $z=s_2$ at the start of the step.
- **`ssaChain lam Λ h x₀ N`**: $N$ steps of `ssaStep`, starting at $\delta_{(x_0,x_0)}$.
- **`ssaLevelLaw lam Λ T x₀ L ℓ`**: `tauLevelLaw lam T x₀ ℓ` if $\ell\le L$, else `ssaChain lam Λ (T/2^L) x₀ (2^L)`.
- **`ssaInputLaw`** $=\bigotimes_{\ell\in\mathbb N}$ `ssaLevelLaw … ℓ`, a measure on $(\mathbb N\times\mathbb N)^{\mathbb N}$. It is Mathlib's `infinitePi`, which is $0$ unless every factor is a probability measure.
- **`ssaCorrection Φ L ℓ y`**:
  - $\ell=0$: $\Phi(y_0.1)$.
  - $1\le\ell\le L$: $\Phi(y_\ell.1)-\Phi(y_\ell.2)$, through `fineCoarseDiff (tauFine Φ) (tauCoarse Φ)`, where `tauCoarse Φ (ℓ-1) y` $=\Phi(y_\ell.2)$.
  - $\ell>L$: $\Phi(y_\ell.1)-\Phi(y_\ell.2)$.
- **`blockMean f ω i N x`** $=N^{-1}\sum_{n<N} f_i(\omega(i,n)(x))$, with $0^{-1}=0$. With `ω = fun p x => x p` it is the sample mean of $f_\ell$ over the independent draws $x(\ell,n)$.
- **`fineCoarseDiff Pf Pc`**: $0\mapsto Pf_0$, $\ell+1\mapsto Pf_{\ell+1}-Pc_\ell$.
- **`tauStep lam h x`** $=x+\mathrm{Po}(h\lambda(x))$: one tau-leaping step.
- **`tauChain lam h x₀ N`**: $N$ tau-leaping steps from $x_0$.
- **`tauLevelLaw lam T x₀ ℓ`**:
  - $\ell=0$: the law of $(Y,Y)$ with $Y\sim$ `tauChain lam T x₀ 1`.
  - $\ell+1$: `coupledChain lam (T/2^{ℓ+1}) x₀ (2^ℓ)`. Its first coordinate is $2^{\ell+1}$ fine steps of $h=T/2^{\ell+1}$, and its second is $2^\ell$ coarse steps of $2h=T/2^\ell$.
- **`tauFine Φ ℓ y`** $=\Phi(y_\ell.1)$ and **`tauCoarse Φ ℓ y`** $=\Phi(y_{\ell+1}.2)$.
- **`exactLaw lam Λ t x`** $=\sum_n\mathrm{Po}(\Lambda t)(n)\,$`jumpPow lam Λ n x`. This is the uniformised pure-birth chain at time $t$ (the CTMC transition law when $\lambda\le\Lambda$).
- **`jumpPow`**: the $n$-fold composition of `jumpKernel`.
- **`jumpKernel lam Λ x`** $=\frac{\lambda(x)}\Lambda\delta_{x+1}+(1-\frac{\lambda(x)}\Lambda)^+\delta_x$.
- **`coupledChain lam h x₀ k`**: $k$ steps of `coupledTwoStep`, starting at $\delta_{(x_0,x_0)}$.
- **`coupledTwoStep lam h s`**: two fine tau steps for $s_1$ (the second uses the updated $s_1$). The coarse component $s_2$ receives two increments, both at the frozen rate $h\lambda(s_2)$, so in total $s_2+\mathrm{Po}(2h\lambda(s_2))$. Each pair of increments comes from `coupledIncr`.
- **`coupledIncr a b`**: the law of `couplePair a b (P, Q)` with $P\sim\mathrm{Po}(\min)$ and $Q\sim\mathrm{Po}(\max-\min)$ independent. This is the standard split-Poisson coupling with marginals Po$(a)$ and Po$(b)$.
- **`couplePair a b (p,q)`** $=(p+[b<a]q,\;p+[a<b]q)$.

Numerical confirmation (`check_unbiased.out`): the coarse marginal of level $\ell+1$ equals the fine marginal of level $\ell$, and the tau marginal of the SSA level equals the fine marginal of level $L$ (errors below $10^{-12}$, from Poisson truncation). So the level structure telescopes as intended.

---

## 1. `poisson_thinning`

**Rendering.** For every $\mu\in\mathbb R_{\ge0}$ and every $p\in\mathbb R_{\ge0}$ with $p\le1$:
$$\sum_{k\ge0}\mathrm{Po}(\mu)(k)\,\mathrm{Bin}(k,p)=\mathrm{Po}(p\mu)$$
as measures on $\mathbb N$. In Lean the left side is `(fun k => binomialLaw k p) ∘ₘ Po(μ)`.

**Assessment.**
- *Truth: true.* For each $j$:
$$\sum_{k\ge j}e^{-\mu}\frac{\mu^k}{k!}\binom kj p^j(1-p)^{k-j}=e^{-\mu}\frac{(p\mu)^j}{j!}\sum_{m\ge0}\frac{((1-p)\mu)^m}{m!}=e^{-p\mu}\frac{(p\mu)^j}{j!}.$$
  The edge cases $p=0$, $p=1$ and $\mu=0$ work because $0^0=1$. `check_thinning.out` shows a maximum error of $2\cdot10^{-41}$ over a grid of $\mu$, $p$ and $j$.
- *Vacuity: not vacuous.* Take $\mu=1$, $p=1/2$.
- *Junk values: none.*
- *Hypotheses:* `hp` is necessary. For $p>1$, NNReal gives $1-p=0$, so `binomialLaw k p` $=p^k\delta_k$ and the bind has total mass $e^{\mu(p-1)}\ne1$ (the script shows $e$ for $\mu=1$, $p=2$).
- *Standard result:* Poisson thinning, i.e. binomial thinning of a Poisson variable (the colouring theorem).

## 2. `ssaStep_map_fst`

**Rendering.** Suppose $\lambda(x)\le\Lambda$ for all $x$. Then for all $h\in\mathbb R_{\ge0}$ and all $s\in\mathbb N^2$, the first marginal of `ssaStep lam Λ h s` equals `exactLaw lam Λ h s.1`.

**Assessment.**
- *Truth: true.* The first marginal of one tick is $(\min(a,b)+(a-b)^+)\delta_{s_1+1}+((b-a)^++(1-\max)^+)\delta_{s_1}=a\,\delta_{s_1+1}+(1-a)\delta_{s_1}$, which is `jumpKernel` at $s_1$. This uses $\max(a,b)\le1$, which follows from `hΛ`. Since this depends only on $s_1$, induction gives `(ssaTickPow n s).map fst = jumpPow n s.1`. Mixing over Po$(\Lambda h)$ gives `exactLaw`. If $\Lambda=0$, then $\lambda\equiv0$ and both sides are $\delta_{s_1}$.
- *Numerical check:* `check_ssa.out` shows errors of at most $2\cdot10^{-16}$ for 6 rate functions, 2 values of $h$ and 3 states.
- *Vacuity: not vacuous.* Take $\lambda\equiv1$, $\Lambda=1$.
- *Junk values: none.*
- *Standard result:* the SSA marginal of the uniformisation coupling is the exact (uniformised) transition kernel.

## 3. `ssaStep_map_snd`

**Rendering.** Under the same hypothesis, the second marginal of `ssaStep lam Λ h s` is $s_2+\mathrm{Po}(h\lambda(s_2))$, i.e. `tauStep lam h s.2`.

**Assessment.**
- *Truth: true.* The second marginal of one tick is $b\,\delta_{s_2+1}+(1-b)\delta_{s_2}$ with $b=\lambda(s_2)/\Lambda$ fixed through the step. So after $n$ ticks the second coordinate is $s_2+\mathrm{Bin}(n,b)$. Thinning (#1) gives $s_2+\mathrm{Po}(b\Lambda h)=s_2+\mathrm{Po}(h\lambda(s_2))$. The case $\Lambda=0$ is consistent.
- *Numerical check:* `check_ssa.out` shows errors of at most $1.1\cdot10^{-16}$.
- *Vacuity: not vacuous.*
- *Junk values: none.* Note that `tauStep` uses `h * lam x`, while the thinning gives `(lam z/Λ) * (Λ*h)`. These agree because $\Lambda>0$ or $\lambda\equiv0$.
- *Standard result:* thinning of the uniformising Poisson clock gives the tau-leap increment.

## 4. `ssaChain_marginals`

**Rendering.** Suppose $\lambda\le\Lambda$, $T\in\mathbb R_{\ge0}$, $x_0\in\mathbb N$ and $N\ge1$. Put $h=T/N$, computed in $\mathbb R_{\ge0}$. Then the $N$-step coupled chain is a probability measure, its first marginal is `exactLaw lam Λ T x₀` (the exact law at time $T$), and its second marginal is `tauChain lam (T/N) x₀ N` ($N$ tau-leap steps of size $T/N$).

**Assessment.**
- *Truth: true.* Induction on the number of steps, using #2, #3 and `map`/`bind` commutation. For the first coordinate, Chapman–Kolmogorov for the uniformised chain holds because $\mathrm{Po}(\Lambda h)^{*N}=\mathrm{Po}(\Lambda T)$ and `jumpPow` is a semigroup in $n$. The kernel masses are 1 under `hΛ`, so the chain is a probability measure. $N(T/N)=T$ requires $N>0$.
- *Hypotheses:* `hN` is necessary. With $N=0$, $T/0=0$ and the chain is $\delta_{(x_0,x_0)}$, whose first marginal is not `exactLaw … T x₀` in general.
- *Numerical check:* `check_ssa.out` shows mass $1$ and marginal errors below $10^{-15}$ for 6 rate functions, $T\in\{0.25,0.5,1,2\}$ and $N\in\{1,2,4,8\}$.
- *Vacuity: not vacuous.*
- *Junk values: none.*
- *Standard result:* marginal consistency of the SSA/tau-leaping coupling (an exact process coupled to its tau-leap approximation).

## 5. `ssaChain_ne_le`

**Rendering.** Under `hΛ` and $N\ge1$:
$$P_{\text{ssaChain}(T/N,N)}\big(X\ne Y\big)\le\frac{\Lambda^2T^2}{N},$$
where $X$ and $Y$ are the two coordinates (real-valued, through `.real` = `toReal`).

**Assessment.**
- *Truth: true.*
  - Within one step started from $X=Y=z$, the first tick has $a=b$, so the pair moves together. A discrepancy can arise only after a joint jump, so it needs at least 2 ticks: $P\le P(\mathrm{Po}(m)\ge2)\le m^2/2$ with $m=\Lambda T/N$.
  - The event $\{X_N\ne Y_N\}$ is contained in the union over steps of the events "equal at the start, unequal at the end".
  - Hence $P\le N m^2/2=\Lambda^2T^2/(2N)$, which is half the stated bound.
- *Numerical check:* `check_ssa.out` has no violations, and the maximum ratio to the stated bound is $0.389$. The extremal example is $\lambda(z)=\Lambda$, $\lambda(z+1)=0$, where the ratio tends to $1/2$ as $m\to0$.
- *Vacuity: not vacuous.*
- *Junk values: none.* The measure is a probability measure, so `.real` is the true probability.
- *Standard result:* the $O(h)$ decoupling probability of the SSA/tau-leap coupling, giving strong error $O(h)$ in the "probability of disagreement" metric.

## 6. `ssaChain_sq_le`

**Rendering.** Suppose $\lambda\le\Lambda$, $|\Phi(x)|\le M$ for all $x$, and $N\ge1$. Then $\Phi(X)-\Phi(Y)\in L^2$ and
$$\mathbb E[(\Phi(X)-\Phi(Y))^2]\le 4M^2\cdot\frac{\Lambda^2T^2}{N}.$$

**Assessment.**
- *Truth: true.* $(\Phi(X)-\Phi(Y))^2\le4M^2\,\mathbf 1\{X\ne Y\}$, then apply #5. The `MemLp` part holds because the function is bounded and measurable and the measure is a probability measure.
- *Vacuity: not vacuous.* Take $\Phi=\min(x,3)$, $M=3$. Note that `hΦ` forces $M\ge0$.
- *Junk values: none.*
- *Hypotheses:* bounded $\Phi$ is a restriction; see main point 2.
- *Standard result:* the $L^2$ coupling error for bounded test functions, the basis of the variance bound in the SSA level of MLMC.

## 7. `ssaChain_abs_le`

**Rendering.** Under `hΛ` and $N\ge1$:
- $|X-Y|$ (as a real number) is integrable;
- $P(X\ne Y)\le\mathbb E|X-Y|$;
- $\mathbb E|X-Y|\le(\Lambda^2T^2+\Lambda^3T^3)/N$.

**Assessment.**
- *Truth: true.*
  - *Integrability:* $|X-Y|$ is at most the total number of uniformisation ticks, which is Po$(\Lambda T)$-distributed.
  - *Second claim:* integer-valued differences satisfy $\mathbf 1\{X\ne Y\}\le|X-Y|$.
  - *Third claim:* let $D_k=|X_k-Y_k|$, and note $|X-Y|$ changes by at most 1 per tick.
    - If $D_k>0$, the expected increase over the step is at most $\mathbb E[\#\text{ticks}]=m$.
    - If $D_k=0$, it is at most $\mathbb E[(\#\text{ticks}-1)^+]\le m^2/2$.
    - With $P(D_k>0)\le k m^2/2$ (from #5):
$$\mathbb E D_N\le\sum_{k<N}\Big(\tfrac{k m^3}{2}+\tfrac{m^2}{2}\Big)\le\frac{\Lambda^3T^3/4+\Lambda^2T^2/2}{N}.$$
- *Numerical check:* `check_ssa.out` has no violations, and the maximum ratio to the stated bound is $0.319$.
- *Vacuity: not vacuous.*
- *Junk values: none.* This is a real integral of an integrable function.
- *Standard result:* the $L^1$ strong error $O(h)$ of tau-leaping against the exact path (cf. Anderson–Ganguly–Kurtz and Anderson–Higham). Here it is proved under bounded rates rather than Lipschitz rates.

## 8. `ssa_mlmc_unbiased`

**Rendering.** Suppose $\lambda\le\Lambda$, $|\Phi|\le M$, $L\in\mathbb N$, and $N:\mathbb N\to\mathbb N$ with $N_\ell>0$ for all $\ell$. Let $P$ be the iid product over indices $(\ell,n)\in\mathbb N^2$ of `ssaInputLaw` (each draw $x(\ell,n)$ is an independent vector of level pairs). Define
$$\hat Y(x)=\sum_{\ell=0}^{L+1}\frac1{N_\ell}\sum_{n<N_\ell}C_\ell\big(x(\ell,n)\big),\qquad C_\ell=\texttt{ssaCorrection }\Phi\ L\ \ell.$$
Then:
- $P$ is a probability measure;
- $\hat Y$ is $P$-integrable;
- $\mathbb E_P\hat Y=\mathbb E_{\texttt{exactLaw}(T,x_0)}[\Phi]$.

**Assessment.**
- *Truth: true.*
  - Integrability: each $C_\ell$ is bounded by $2M$.
  - $\mathbb E\hat Y=\sum_{\ell\le L+1}\mathbb E\,C_\ell(y)$ with $y_\ell\sim$ `ssaLevelLaw ℓ`.
  - The levels telescope: $\mathbb E\Phi(\tau_0)+\sum_{\ell=1}^L(\mathbb E\Phi(\tau_\ell)-\mathbb E\Phi(\tau_{\ell-1}))+\mathbb E\Phi(X_T)-\mathbb E\Phi(\tau_L)$, where $\tau_\ell$ is tau-leaping with $2^\ell$ steps of $T/2^\ell$. This uses the coupledChain marginals and #4 with $N=2^L$.
  - The case $L=0$ works too, since $T/2^0=T$.
  - `check_unbiased.out` shows a telescoped sum equal to $\mathbb E\Phi(X_T)$ within $2\cdot10^{-12}$ for 3 rate functions, 3 choices of $\Phi$ and $L=0,1,2$.
- *Vacuity: not vacuous.* For example $\lambda\equiv1$, $\Lambda=1$, $T=1$, $x_0=0$, $\Phi=\min(\cdot,3)$, $M=3$, $L=1$, $N\equiv1$.
- *Junk values: none.* `infinitePi` would be $0$ for a non-probability family, but the first conjunct excludes that. `blockMean` with $N_\ell=0$ would be $0$, but `hN` excludes that.
- *Hypotheses:* `hN` for all $\ell$, rather than only $\ell\le L+1$, is harmless over-assumption.
- *Standard result:* unbiasedness of the multilevel estimator with an exact (SSA) finest level (Anderson–Higham 2012, unbiased MLMC for CTMCs) via telescoping.

## 9. `variance_ssaCorrection_exact_le`

**Rendering.** Suppose $\lambda\le\Lambda$ and $|\Phi|\le M$, and fix $L$. The top correction $C_{L+1}(y)=\Phi(y_{L+1}.1)-\Phi(y_{L+1}.2)$ is in $L^2$ of `ssaInputLaw`, and
$$\mathrm{Var}(C_{L+1})\le 4M^2\Lambda^2T^2/2^L,$$
with $2^L$ computed in $\mathbb R$.

**Assessment.**
- *Truth: true.* $y_{L+1}\sim$ `ssaChain (T/2^L) x₀ 2^L`, and $\mathrm{Var}\le\mathbb E[C^2]\le4M^2\Lambda^2T^2/2^L$ by #6 with $N=2^L$. The casts agree: $T/\uparrow(2^L)=T/2^L$ in $\mathbb R_{\ge0}$.
- *Numerical check:* `check_unbiased.out` shows variances far below the bound.
- *Vacuity: not vacuous.*
- *Junk values: none in fact.* If `ssaInputLaw` were the zero measure (Mathlib's `infinitePi` fallback), the statement would be trivially true. It is not zero, because under `hΛ` every `ssaLevelLaw ℓ` is a probability measure (this is implied by the first conjunct of #8). The theorem does not restate this, so a reader should rely on #8 for non-triviality.
- *Standard result:* the variance decay $V_{L}=O(h_L)$ of the SSA-vs-tau correction level, the $\beta=1$ rate in Giles's MLMC theorem.

## 10. `ssa_mlmc_complexity`

**Rendering.** Suppose $\lambda\le\Lambda$, $|\Phi|\le M$, and fix $L$. Then the product measure $P$ is a probability measure, and there is $c>0$, which may depend on $\lambda,\Lambda,T,x_0,\Phi,M,L$, such that for every $\varepsilon\in(0,1]$ there exists $N:\mathbb N\to\mathbb N_{>0}$ with:
- $(\hat Y-\mathbb E\Phi(X_T))^2$ integrable;
- $\mathrm{MSE}=\mathbb E_P(\hat Y-\mathbb E\Phi(X_T))^2<\varepsilon^2$;
- cost $\sum_{\ell=0}^{L}N_\ell2^\ell+N_{L+1}(2^L+\Lambda T)\le c/\varepsilon^2$, computed in $\mathbb R$.

**Assessment.**
- *Truth: true.* By #8 the MSE equals the variance, which is $\sum_{\ell\le L+1}V_\ell/N_\ell$ by independence of the draws $x(\ell,n)$. Take $K=\sum V_\ell+1$ and $N_\ell=\lceil K/\varepsilon^2\rceil$. Then MSE $<\varepsilon^2$, and the cost is at most $(K/\varepsilon^2+1)W\le 2KW/\varepsilon^2$ with $W=\sum_\ell w_\ell$, using $\varepsilon\le1$.
- *Numerical check:* `check_complexity.out` confirms this for $L=0,\dots,3$ with $\lambda(x)=2/(1+x)$, $\Lambda=2$, $T=1$, $\Phi=\min(\cdot,3)$. That naive allocation gives a $c$ that grows with $L$ ($19.6, 34.9, 65.1, 125.4$), which illustrates that the statement lets $c$ depend on $L$.
- *Vacuity: not vacuous.* The instance from #8 works.
- *Junk values: none.* `IsProbabilityMeasure` is asserted, so the MSE is not the integral against the zero measure.
- *Weakness (main finding):* because $c$ is chosen after $L$, the statement is the generic fact that an unbiased, finite-variance estimator with fixed per-sample cost reaches MSE $\varepsilon^2$ at cost $O(\varepsilon^{-2})$. It uses neither #9 nor any level-variance decay. It holds verbatim for $L=0$, and for any positive cost weights. It gives no information about the size of $c$ or about the MLMC gain over plain SSA Monte Carlo (whose cost is also $O(\Lambda T\varepsilon^{-2})$). It is therefore much weaker than the MLMC complexity theorem it echoes (Giles 2008, Thm 3.1; Anderson–Higham 2012), where the constant is explicit or uniform and the level structure matters.
- *Standard result:* the $O(\varepsilon^{-2})$ cost of unbiased MLMC / unbiased Monte Carlo.
