# Blind read-back report: R46 (tau-leaping, linear growth / linear birth; Banach-valued MLMC)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round25/packet_R46_taubanach.lean` |
| declarations audited | 19 (16 theorems + 3 definitions in the packet body: `HasType2`, `vecLevelDiff`, `vecMlmcEstimator`); the 13 appended definitions are read in §0 |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round25/work_R46_taubanach/` (`common.py`, `s1_moments.py/.out`, `s2_coupled.py/.out`, `s3_weak.py/.out`, `s4_type2.py/.out`, `s5_alloc.py/.out`, `Scratch1.lean/.out`) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `tauChain_moments_linear` | theorem | true | no | no |
| 2 | `coupledChain_sq_le_lipschitz` | theorem | true | no | no |
| 3 | `variance_coupledChain_le_lipschitz` | theorem | true | no | no |
| 4 | `variance_tauCorrection_le_lipschitz` | theorem | true | no | no (the measures are genuine probability measures; checked in Lean) |
| 5 | `tauLeaping_mlmc_theorem1_lipschitz` | theorem | true | no | no (same check) |
| 6 | `tauLeaping_mlmc_linearBirth` | theorem | true | no | no |
| 7 | `integral_tauChain_linearBirth` | theorem | true | no | no |
| 8 | `tauLeaping_linearBirth_weak_error` | theorem | true | no | no |
| 9 | `tauLeaping_mlmc_linearBirth_mean` | theorem | true | no | no |
| D1 | `HasType2` | def | n/a | n/a (non-degenerate: `HasType2 (ℝ×ℝ) 1` is false) | n/a |
| 10 | `hasType2_of_innerProductSpace` | theorem | true | no | no |
| 11 | `hasType2_of_isomorphic_embedding` | theorem | true | no | no |
| 12 | `exists_hasType2_of_finiteDimensional` | theorem | true | no | no |
| 13 | `exists_hasType2_prod` | theorem | true | no | no |
| 14 | `hasType2_prod_sqrt_two` | theorem | true (and $\sqrt2$ is sharp) | no | no |
| D2 | `vecLevelDiff` | def | n/a | n/a | n/a |
| D3 | `vecMlmcEstimator` | def | n/a | n/a | n/a |
| 15 | `mlmc_mse_le_of_hasType2` | theorem | true | no | no |
| 16 | `giles_theorem1_banach` | theorem | true | no | no |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.** All 16 theorems are true as stated.
2. **The main junk-value risk is ruled out.** Mathlib's `Measure.infinitePi μ` is defined as `if ∀ i, IsProbabilityMeasure (μ i) then … else 0`. If any `tauLevelLaw` failed to be a probability measure, `tauInputLaw` would be the zero measure, and #4, #5, #6 and #9 would hold trivially (variance 0, MSE 0). I proved in Lean, with my own short proofs (`Scratch1.lean`, compiles with no errors), that `tauChain`, `coupledIncr`, `coupledTwoStep`, `coupledChain`, `tauLevelLaw` and `tauInputLaw` are all probability measures. So the product measures are genuine.
3. **#5 and #6 take the weak-error rate as a hypothesis** (`hweak`, with $\alpha\ge\tfrac12$ and $P$ otherwise free; `hweak` forces $P=\lim_\ell \mathbb E\,\Phi(X^{(\ell)}_T)$, the limit of the tau-leap means, not the exact SSA mean). The variance rate $\beta=1$ is proved, not assumed. The weak-error hypothesis is discharged only in #9 (linear birth with $\Phi=\mathrm{id}$, $P=x_0e^{cT}$), via #8.
4. **Cost model in #5, #6 and #9.** Cost is the deterministic count $\sum_\ell N_\ell 2^\ell$ of fine steps. The real cost per sample is $1.5\cdot2^\ell$ (fine plus coarse steps), so this differs only by a constant. This is the $\beta=\gamma=1$ case of Giles' theorem, giving $\varepsilon^{-2}(\log\varepsilon)^2$.
5. **#2 and #3 are stronger than a per-propensity bound.** The constant $c$ is chosen before the propensity $\lambda$ and is uniform over all $K$-Lipschitz $\lambda$ on $\mathbb N$ with $\lambda(0)\le a$. In #3 it is also uniform over all $L_\Phi$-Lipschitz $\Phi$. I believe both are true (sketch below), and exact numerics show $\mathbb E[(X^f-X^c)^2]/h$ staying bounded.
6. **`HasType2` uses independent mean-zero summands rather than Rademacher sums.** This is equivalent to Rademacher type 2 up to a factor 2 in $\tau$ (by symmetrisation). $\tau$ enters only as $\tau^2$, so its sign does not matter.
   - **σ-algebra on $E$.** The definition allows any `MeasurableSpace E`, and with a coarse σ-algebra `iIndepFun` would be too weak. Every theorem that uses it adds `[BorelSpace E]`, so this causes no issue in the packet.
   - **Universes.** The universe of $\Omega$ is a parameter (`HasType2.{u}`). In #15 and #16, $\Omega$ has the same universe, which I confirmed with `pp.universes`.
7. **#14's constant $\sqrt2$ is sharp** for Mathlib's sup norm on $\mathbb R\times\mathbb R$. With $X_1=r_1(1,1)$ and $X_2=r_2(1,-1)$ ($r_i$ Rademacher), $\mathbb E\|X_1+X_2\|_\infty^2=4=2\sum\mathbb E\|X_i\|_\infty^2$ (`s4_type2.out`). In particular `HasType2 (ℝ×ℝ) 1` is false, so the definition is not degenerate.
8. **Minor slack and unneeded hypotheses (harmless):**
   - #1's bounds are loose: $\mathbb E X\le(1+x_0)e^{(a+b)T}-1$ holds, and $\max(a,b)$ would suffice in place of $a+b$.
   - #8 has slack of a factor 2: the sharp constant is $\tfrac12$.
   - `hc₁ : 0 < c₁` in #5 and #6, and `hγ`/`hc₃` positivity in #16, are not needed for truth.
   - In #16, costs are not required to be nonnegative; only the upper bound $C_\ell\le c_32^{\gamma\ell}$ is used, which only makes the conclusion easier.
   - In #15 and #16, $\nu$ is not declared a probability measure, but `MeasurePreserving (ω p) μ ν` with $\mu$ a probability measure forces it to be one.
9. **A proof subtlety, not a truth issue (#15 and #16).** `Pl ℓ` is only `MemLp`, so it is a.e.-strongly measurable but not necessarily measurable. Independence of $\mathrm{Pl}_\ell\circ\omega_p$ then needs an a.e.-modification argument (replace $\mathrm{Pl}_\ell$ by a strongly measurable version, which is Borel measurable since `BorelSpace E` holds, and transport the a.e. equality along the measure-preserving maps $\omega_p$). The statement is still true.

---

## §0 Appended definitions (read once, used throughout)

- `tauStep λ h x` $=$ law of $x+\mathrm{Poi}(h\lambda(x))$ on $\mathbb N$. Mathlib's `poissonMeasure r` $=\sum_n e^{-r}r^n/n!\,\delta_n$ is a probability measure.
- `tauChain λ h x₀ n` $=$ law of $X_n$ for the tau-leap chain $X_0=x_0$, $X_{k+1}=X_k+\mathrm{Poi}(h\lambda(X_k))$: a single birth reaction with step $h$ and $n$ steps, built by `Measure.bind`. On $\mathbb N$ and $\mathbb N\times\mathbb N$ every function is measurable (countable, measurable singletons), so `bind` is the genuine Markov composition.
- `couplePair a b (p,q)` and `coupledIncr a b`: with $P_1\sim\mathrm{Poi}(\min(a,b))$ and $P_2\sim\mathrm{Poi}(|a-b|)$ independent, the pair is $(P_1+[b<a]P_2,\;P_1+[a<b]P_2)$. Its marginals are $\mathrm{Poi}(a)$ and $\mathrm{Poi}(b)$ (the standard "common part plus difference" Poisson coupling, Anderson–Higham).
- `coupledTwoStep λ h (f,c)`: draw $(i_1,j_1)\sim$ `coupledIncr`$(h\lambda(f),h\lambda(c))$, then $(i_2,j_2)\sim$ `coupledIncr`$(h\lambda(f+i_1),h\lambda(c))$, and return $(f+i_1+i_2,\;c+j_1+j_2)$. Fine: two steps of size $h$. Coarse: one step of size $2h$, since $j_1+j_2\sim\mathrm{Poi}(2h\lambda(c))$ given $c$.
- `coupledChain λ h x₀ k`: $k$ coupled two-steps from $(x_0,x_0)$. The fine marginal is `tauChain λ h x₀ (2k)` and the coarse marginal is `tauChain λ (2h) x₀ k`. I checked both numerically (TV distance $\le 10^{-7}$, truncation level, in `s2_coupled.out`).
- `tauLevelLaw λ T x₀ 0` $=$ law of $(X,X)$ with $X\sim$ `tauChain λ T x₀ 1`. `tauLevelLaw λ T x₀ (ℓ+1)` $=$ `coupledChain λ (T/2^{ℓ+1}) x₀ (2^ℓ)` (fine: $2^{\ell+1}$ steps of $T/2^{\ell+1}$; coarse: $2^\ell$ steps of $T/2^\ell$). All divisions are in `ℝ≥0` with $2^\ell>0$, so there is no division-by-zero junk.
- `tauInputLaw λ T x₀` $=$ the product (`infinitePi`) over $\ell\in\mathbb N$ of `tauLevelLaw`, a law on $\mathbb N\to\mathbb N\times\mathbb N$. It is genuine because all factors are probability measures (Lean-checked, point 2).
- `tauFine Φ ℓ y = Φ((y ℓ).1)`, `tauCoarse Φ ℓ y = Φ((y (ℓ+1)).2)`. `fineCoarseDiff Pf Pc 0 = Pf 0` and `fineCoarseDiff Pf Pc (ℓ+1) y = Pf (ℓ+1) y − Pc ℓ y`. So level $0$ is $\Phi(X^{(0)})$ and level $\ell+1$ is $\Phi(X^f)-\Phi(X^c)$ for the coupled pair $y(\ell+1)$.
- `blockMean f ω i N x` $=N^{-1}\sum_{n<N}f\,i\,(\omega(i,n)\,x)$, with $\mathbb N$-cast inverse (for $N=0$ this would be $0$, but every use has $N_\ell>0$). With `ω = fun p x => x p` and the product measure over $\mathbb N\times\mathbb N$, the samples $x(\ell,n)$ are i.i.d. `tauInputLaw`.
- `totalCost cost L N x` $=\sum_{\ell\le L}\sum_{n<N_\ell}\mathrm{cost}_{\ell,n}(x)$.
- `complexityBound α β γ ε` $=\varepsilon^{-2}$ if $\gamma<\beta$; $\varepsilon^{-2}(\log\varepsilon)^2$ if $\beta=\gamma$; $\varepsilon^{-2-(\gamma-\beta)/\alpha}$ otherwise (`rpow`, with $\varepsilon>0$ in every use).

---

## 1. `tauChain_moments_linear`

**Rendering.** Fix $\lambda:\mathbb N\to\mathbb R_{\ge0}$ and $a,b\ge0$ with $\lambda(x)\le a+bx$ for all $x\in\mathbb N$. Fix $x_0\in\mathbb N$, $T\in\mathbb R$, $h\in\mathbb R_{\ge0}$, $n\in\mathbb N$ with $nh\le T$ (so $T\ge0$). Let $X_n\sim$ `tauChain λ h x₀ n`. Then:
- $X_n\in L^2$;
- $\mathbb E X_n\le(1+x_0)e^{(a+b)T}$;
- $\mathbb E X_n^2\le(1+x_0)^2\exp\big((3(a+b)+(a+b)^2T)\,T\big)$.

All quantities are real, with $a,b,h,x$ cast. Elaboration confirmed.

**Assessment.** True. Put $s=a+b$; then $\lambda(x)\le s(1+x)$. Given $X_k$:
- $\mathbb E[1+X_{k+1}\mid X_k]=1+X_k+h\lambda\le(1+X_k)(1+hs)$.
- $\mathbb E[(1+X_{k+1})^2\mid X_k]=(1+X_k)^2+2(1+X_k)h\lambda+h\lambda+h^2\lambda^2\le(1+X_k)^2(1+3hs+h^2s^2)$, using $1+X\le(1+X)^2$.

Iterating gives $\le(1+x_0)e^{snh}$ and $(1+x_0)^2e^{nh(3s+hs^2)}$, and $nh\le T$, $h\le T$ (when $n\ge1$) give the claims. The case $n=0$ is immediate because the exponent is $\ge0$. $L^2$ follows inductively since Poisson has all moments.

Numerics (`s1_moments.out`): over 150 cases the worst ratios are 0.79 (mean) and 0.38 (second moment).

Not vacuous: e.g. $\lambda\equiv1$, $a=1$, $b=0$. No junk: the integrals are of $L^2$ functions under a probability measure. The bound is loose (point 8). This is the standard Gronwall-type moment bound for tau-leaping with linear-growth propensity.

## 2. `coupledChain_sq_le_lipschitz`

**Rendering.** For $K,a\ge0$, $T\ge0$, $x_0\in\mathbb N$ there is $c\ge0$ (depending only on $K,a,T,x_0$) such that the following holds. For every $\lambda:\mathbb N\to\mathbb R_{\ge0}$ with $|\lambda(x)-\lambda(y)|\le K|x-y|$ on $\mathbb N$ and $\lambda(0)\le a$, every $h\ge0$, and every $k\in\mathbb N$ with $2kh\le T$: under $(X^f,X^c)\sim$ `coupledChain λ h x₀ k` (fine: $2k$ steps of $h$; coarse: $k$ steps of $2h$; Poisson coupling), $X^f-X^c\in L^2$ and $\mathbb E(X^f-X^c)^2\le c\,h$.

**Assessment.** True. Let $D=X^f-X^c$. Then $\lambda\le a+Kx$, so #1 bounds the moments of $X^f$ uniformly in $\lambda$.

In one coupled two-step, $i_1-j_1=\pm\mathrm{Poi}(h|\lambda(f)-\lambda(c)|)$ and $i_2-j_2=\pm\mathrm{Poi}(h|\lambda(f+i_1)-\lambda(c)|)$, with $|\lambda(f+i_1)-\lambda(c)|\le K(|D|+i_1)$ and $\mathbb E[i_1\mid\cdot]=h\lambda(f)$.

- **$L^1$ estimate:** $\mathbb E|D_{k+1}|\le(1+2hK)\mathbb E|D_k|+Kh^2\mathbb E\lambda(X^f)$. Over $\le T/(2h)$ steps this gives $\mathbb E|D|=O(h)$.
- **$L^2$ estimate:** $\mathbb E D_{k+1}^2\le(1+Ch)\mathbb E D_k^2+Ch\,\mathbb E|D_k|+Ch^2(1+\mathbb E\lambda(X^f)^2)$, which gives $\mathbb ED^2=O(h)$.

All constants depend only on $K,a,T,x_0$. If $k\ge1$ then $h\le T/2$; if $k=0$ then $D=0$.

Exact numerics (`s2_coupled.out`, $T=1$, $h=1/2,\dots,1/16$), giving $\mathbb ED^2/h$:
- $\lambda=1+x$: $2.0\to3.5\to4.8\to5.7$, consistent with a heuristic limit $\approx6.2$;
- $\lambda=1+|x-3|$ (non-monotone): $3.3\to2.3$;
- $\lambda=3+2\sin x$: $\approx2.0$–$2.3$;
- $\lambda=2x$, $x_0=2$: $16\to46\to88\to123$, increments shrinking, heuristic limit $O(10^2)$.

Not vacuous: e.g. $\lambda=1+x$, $K=a=1$. No junk. This is Anderson–Higham's (2012) strong-error estimate $\mathbb E|X^f-X^c|^2=O(h)$ for Poisson-coupled tau-leaping. It is stated uniformly over the Lipschitz class, which is stronger than the usual per-$\lambda$ statement.

## 3. `variance_coupledChain_le_lipschitz`

**Rendering.** Same as #2, plus a real $L_\Phi$ fixed before $c$. There is $c\ge0$ such that for every admissible $\lambda$, every $\Phi:\mathbb N\to\mathbb R$ with $|\Phi(x)-\Phi(y)|\le L_\Phi|x-y|$, and every $h,k$ with $2kh\le T$:
- $\Phi(X^f)-\Phi(X^c)\in L^2$;
- $\mathbb E(\Phi(X^f)-\Phi(X^c))^2\le ch$;
- `variance` of $\Phi(X^f)-\Phi(X^c)$ is $\le ch$.

**Assessment.** True: $(\Phi(x)-\Phi(y))^2\le L_\Phi^2(x-y)^2$, so take $L_\Phi^2c$ from #2. Variance $\le$ second moment under a probability measure. `variance` (= `(evariance).toReal`) would be junk $0$ off $L^2$, but $L^2$ is asserted, so no junk.

If $L_\Phi<0$, no $\Phi$ satisfies the hypothesis (for $x\ne y$), so that case is vacuously true. Any $L_\Phi\ge0$ gives non-vacuous instances. Numerics with $\Phi=\sqrt{1+x}$ give $\mathrm{Var}/h$ bounded (`s2_coupled.out`). This is the standard MLMC level-variance bound for tau-leaping.

## 4. `variance_tauCorrection_le_lipschitz`

**Rendering.** Fix a $K$-Lipschitz $\lambda$ on $\mathbb N$ (no bound on $\lambda(0)$ is needed, since the constant may depend on $\lambda$), $T\in\mathbb R_{\ge0}$, $x_0$, and an $L_\Phi$-Lipschitz $\Phi$. There is $c_2>0$ such that for every $\ell$, the level-$\ell$ correction $Y_\ell$ = `fineCoarseDiff (tauFine Φ) (tauCoarse Φ) ℓ` is in $L^2$(`tauInputLaw λ T x₀`) and $\mathrm{Var}(Y_\ell)\le c_2\,2^{-\ell}$ (the exponent is `rpow` $-(1\cdot\ell)$).

**Assessment.** True.
- $Y_0=\Phi(X)$ with $X=x_0+\mathrm{Poi}(T\lambda(x_0))$, which has finite variance.
- For $\ell+1$, the coordinate law is `coupledChain λ (T/2^{ℓ+1}) x₀ 2^ℓ` with $2kh=T$, so #3 gives $\le c\,T/2^{\ell+1}$.
- The coordinate marginal of `infinitePi` is the factor; this is a genuine product (Lean-checked).

Non-vacuous. No junk. For $T=0$ everything is deterministic, which is fine. This is the $\beta=1$ variance hypothesis (iii) of Giles' theorem for tau-leaping.

## 5. `tauLeaping_mlmc_theorem1_lipschitz`

**Rendering.** Fix a $K$-Lipschitz $\lambda$, $T\ge0$, $x_0$, an $L_\Phi$-Lipschitz $\Phi$, $P\in\mathbb R$, $\alpha\ge\tfrac12$, and $c_1>0$, with
$|\mathbb E\,\Phi(X^{(\ell)})-P|\le c_1 2^{-\alpha\ell}$ for all $\ell$, where $X^{(\ell)}\sim$ `tauChain λ (T/2^ℓ) x₀ 2^ℓ`.

Then there is $c_4>0$ such that for all $\varepsilon\in(0,e^{-1})$ there are $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N_{>0}$ for which the MLMC estimator
$\hat Y=\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}Y_\ell(x(\ell,n))$ (with $x(\ell,n)$ i.i.d. `tauInputLaw`, via the product over $\mathbb N\times\mathbb N$) satisfies:
- $(\hat Y-P)^2$ is integrable;
- $\mathbb E(\hat Y-P)^2<\varepsilon^2$;
- $\sum_{\ell\le L}N_\ell2^\ell\le c_4\,\varepsilon^{-2}(\log\varepsilon)^2$.

**Assessment.** True.
- **Telescoping.** The coarse marginal at level $\ell+1$ equals `tauChain λ (T/2^ℓ) x₀ 2^ℓ`, the fine law at level $\ell$ (and level 0 is one step of $T$). So $\mathbb E\hat Y=\mathbb E\Phi(X^{(L)})$.
- **MSE.** $\mathrm{MSE}=\sum V_\ell/N_\ell+\text{bias}^2$, with $V_\ell\le c_22^{-\ell}$ by #4.
- **Allocation.** Choose $L$ with $c_1^22^{-2\alpha L}\le\varepsilon^2/4$ and $N_\ell=\lceil2\varepsilon^{-2}c_2(L+1)2^{-\ell}\rceil$.
- **Cost.** $\le2c_2\varepsilon^{-2}(L+1)^2+2^{L+1}$. Here $2^L\lesssim\varepsilon^{-1/\alpha}\le\varepsilon^{-2}$ (since $\alpha\ge\tfrac12$) and $(L+1)^2\lesssim(\log\varepsilon)^2$ (since $\varepsilon<e^{-1}$ gives $|\log\varepsilon|>1$).

`s5_alloc.out` confirms that cost$/(\varepsilon^{-2}\log^2\varepsilon)$ stays bounded, tending to $2c_2/(\alpha\ln2)^2$, including at the boundary $\alpha=\tfrac12$.

Non-vacuous (e.g. #9's instance, or $\Phi\equiv P$). No junk: the product measure is genuine, `Real.log ε` has $\varepsilon>0$, and `rpow` has a positive base. The weak rate is a hypothesis (point 3). This is Giles (2008) Theorem 1, case $\beta=\gamma$, applied to tau-leaping (Anderson–Higham 2012).

## 6. `tauLeaping_mlmc_linearBirth`

**Rendering.** This is #5 specialised to $\lambda(x)=cx$ ($c\in\mathbb R_{\ge0}$), with the same hypotheses on $\Phi,P,\alpha,c_1$ and `hweak`, and the same conclusion.

**Assessment.** True: $\lambda(x)=cx$ is $c$-Lipschitz, so #5 applies. Non-vacuous: #9's data satisfies `hweak` (via #8). No junk. This is the MLMC complexity for tau-leaping of the linear birth process.

## 7. `integral_tauChain_linearBirth`

**Rendering.** For $c,h\in\mathbb R_{\ge0}$ and $x_0,n\in\mathbb N$, with $X_n\sim$ `tauChain (x ↦ c x) h x₀ n`: $X_n$ is integrable and $\mathbb EX_n=x_0(1+hc)^n$ (real casts, confirmed).

**Assessment.** True: $\mathbb E[X_{k+1}\mid X_k]=(1+hc)X_k$. Exact DP agrees to $10^{-12}$, the truncation level (`s1_moments.out`). Not vacuous. No junk (integrability is asserted). This is the mean of the explicit Euler/tau-leap scheme for $\dot m=cm$.

## 8. `tauLeaping_linearBirth_weak_error`

**Rendering.** For $c,T\in\mathbb R_{\ge0}$, $x_0$, and $N\ge1$:
$\big|\mathbb E X_N^{(T/N)}-x_0e^{cT}\big|\le x_0(cT)^2e^{cT}/N$, where $X^{(T/N)}$ is the linear-birth tau-leap with step $T/N$ (`ℝ≥0` division, $N>0$) and $N$ steps.

**Assessment.** True. By #7 the left side is $x_0\big(e^{x}-(1+x/N)^N\big)$ with $x=cT$, and
$(1+x/N)^N\ge e^{x-x^2/(2N)}\ge e^x(1-x^2/(2N))$.
So the bound holds with constant $\tfrac12$; the stated constant 1 has slack. `s3_weak.out` gives a maximum ratio of $0.49999997$.

Edge cases $x_0=0$ and $c=0$ or $T=0$ give $0\le0$ (genuine, not junk). This is the first-order weak error of Euler/tau-leaping for linear birth.

## 9. `tauLeaping_mlmc_linearBirth_mean`

**Rendering.** For $c,T\ge0$ and $x_0$, there is $c_4>0$ such that for all $\varepsilon\in(0,e^{-1})$ there are $L$ and $N>0$ for which the MLMC estimator with $\Phi=\mathrm{id}$ for the linear birth tau-leap satisfies:
- $\mathbb E(\hat Y-x_0e^{cT})^2<\varepsilon^2$ (with integrability);
- cost $\sum N_\ell2^\ell\le c_4\varepsilon^{-2}(\log\varepsilon)^2$.

**Assessment.** True. Apply #6 with $\Phi=\mathrm{id}$ ($L_\Phi=1$), $P=x_0e^{cT}$, $\alpha=1$, $c_1=x_0(cT)^2e^{cT}+1>0$. The hypothesis `hweak` follows from #8 with $N=2^\ell$ (`Nat.cast_pow`). $x_0e^{cT}$ is the exact mean of the Yule/linear birth process. Non-vacuous (no hypotheses). No junk.

## D1. `HasType2` (definition)

**Rendering.** For a real Banach space $E$ with some σ-algebra and $\tau\in\mathbb R$, `HasType2.{u} E τ` means the following. For every probability space $(\Omega,\mu)$ with $\Omega$ in universe $u$, every $n$, and every independent family $X_1,\dots,X_n:\Omega\to E$ (independence w.r.t. the given σ-algebra on $E$) with $X_i\in L^2$ and Bochner mean $0$:
$$\mathbb E\Big\|\sum_iX_i\Big\|^2\le\tau^2\sum_i\mathbb E\|X_i\|^2.$$

**Assessment.** This is the type-2 inequality in "independent mean-zero" form. It is equivalent to Rademacher type 2 up to $\tau\mapsto2\tau$. Only $\tau^2$ matters. It is non-degenerate: the sup-norm example (point 7) shows `HasType2 (ℝ×ℝ) 1` fails. The σ-algebra on $E$ is arbitrary in the definition, but all theorems assume `BorelSpace`.

## 10. `hasType2_of_innerProductSpace`

**Rendering.** Every real Hilbert space $F$ (complete, Borel σ-algebra) satisfies `HasType2.{u} F 1` for every universe $u$.

**Assessment.** True:
$$\mathbb E\|\textstyle\sum X_i\|^2=\sum\mathbb E\|X_i\|^2+\sum_{i\ne j}\mathbb E\langle X_i,X_j\rangle,$$
and $\mathbb E\langle X_i,X_j\rangle=\langle\mathbb EX_i,\mathbb EX_j\rangle=0$ by pairwise independence. This uses integrability by Cauchy–Schwarz, and approximation of the a.e.-separably-valued $X_i$ by countably-valued Borel functions $\varphi_m(X_i)$, which handles non-separable $F$. Equality holds in Euclidean random tests (`s4_type2.out`). Non-vacuous (e.g. $\mathbb R$). This is the Pythagoras/Bienaymé identity: Hilbert spaces have type 2 with constant 1.

## 11. `hasType2_of_isomorphic_embedding`

**Rendering.** Let $E$ be a Banach space (Borel) and $F$ a Hilbert space (Borel), and let $T:E\to F$ be continuous linear with $a\|x\|\le\|Tx\|\le b\|x\|$, $a>0$. Then `HasType2.{u} E (b/a)`.

**Assessment.** True: $T\circ X_i$ are independent (since $T$ is Borel measurable), mean zero (since $T$ commutes with the Bochner integral), and in $L^2$. Then
$$\mathbb E\|\textstyle\sum X_i\|^2\le a^{-2}\mathbb E\|\sum TX_i\|^2=a^{-2}\sum\mathbb E\|TX_i\|^2\le(b/a)^2\sum\mathbb E\|X_i\|^2.$$
If $E=0$ then $b$ may be negative, but only $\tau^2$ enters. Non-vacuous ($T=\mathrm{id}$). This is the statement that type 2 is invariant under isomorphism, with Banach–Mazur-type constant $b/a$.

## 12. `exists_hasType2_of_finiteDimensional`

**Rendering.** Every finite-dimensional real normed space (Borel) has `HasType2.{u} E τ` for some $\tau$.

**Assessment.** True: all norms are equivalent, so take a linear isomorphism to Euclidean $\mathbb R^d$ and apply #11. Standard.

## 13. `exists_hasType2_prod`

**Rendering.** There is $\tau$ with `HasType2.{u} (ℝ×ℝ) τ` (Mathlib's sup norm, product = Borel σ-algebra).

**Assessment.** True (e.g. by #14 or #12).

## 14. `hasType2_prod_sqrt_two`

**Rendering.** `HasType2.{u} (ℝ×ℝ) √2`, with $\|(x,y)\|=\max(|x|,|y|)$.

**Assessment.** True:
$$\mathbb E\max(S_1^2,S_2^2)\le\mathbb ES_1^2+\mathbb ES_2^2=\sum_i\mathbb E\big[(X_i^1)^2+(X_i^2)^2\big]\le2\sum\mathbb E\|X_i\|_\infty^2.$$
The constant is sharp: the example in point 7 gives ratio exactly 2. Random exact tests give a maximum ratio of 1.65 (`s4_type2.out`). This is the type-2 constant of $\ell^\infty_2$.

## D2. `vecLevelDiff` and D3. `vecMlmcEstimator` (definitions)

**Rendering.**
- `vecLevelDiff Pl 0 = Pl 0`, and `vecLevelDiff Pl (ℓ+1) = Pl (ℓ+1) − Pl ℓ`. These are the $E$-valued MLMC corrections, where fine and coarse use the same input $y$.
- `vecMlmcEstimator Pl ω L N x` $=\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}\Delta P_\ell(\omega(\ell,n)\,x)$. With $N_\ell=0$ the inverse is $0$ and that level drops out, but every theorem assumes $N_\ell>0$.

**Assessment.** These are standard Giles estimator definitions. Giles' condition (ii) on the mean is built in by construction.

## 15. `mlmc_mse_le_of_hasType2`

**Rendering.** Let $E$ be a Borel Banach space with `HasType2.{u} E τ`, $(\Omega_0,\nu)$ a measurable space with measure, and $(\Omega,\mu)$ a probability space in universe $u$. Let $P_\ell:\Omega_0\to E$ be in $L^2(\nu)$, and let $\omega_{(\ell,n)}:\Omega\to\Omega_0$ be measure-preserving from $\mu$ to $\nu$ and mutually independent. Let $L\in\mathbb N$, $N_\ell>0$ for $\ell\le L$, and $m\in E$. Then $\|\hat Y-m\|^2\in L^1(\mu)$ and
$$\mathbb E\|\hat Y-m\|^2\le2\Big(\tau^2\sum_{\ell\le L}\frac{\mathbb E_\nu\|\Delta P_\ell-\mathbb E_\nu\Delta P_\ell\|^2}{N_\ell}+\big\|\mathbb E_\nu P_L-m\big\|^2\Big).$$

**Assessment.** True. By telescoping $\mathbb E\hat Y=\mathbb E_\nu P_L$. Then $\|\hat Y-m\|^2\le2\|\hat Y-\mathbb E\hat Y\|^2+2\|\mathbb E\hat Y-m\|^2$. Finally, $\hat Y-\mathbb E\hat Y$ is a finite sum of independent, mean-zero, $L^2$ terms $N_\ell^{-1}(\Delta P_\ell\circ\omega_{(\ell,n)}-\text{mean})$, reindexed by `Fin`, and type 2 gives $\le\tau^2\sum_\ell N_\ell\cdot N_\ell^{-2}V_\ell$.

Two remarks:
- $\nu$ is forced to be a probability measure.
- Measurability of $P_\ell$ is only a.e.; see point 9 (a proof issue, not a truth issue).

Non-vacuous (e.g. $E=\mathbb R$, $\tau=1$, $\Omega=\Omega_0^{\mathbb N\times\mathbb N}$ with the product measure). The factor 2 is a harmless weakening of the exact bias–variance split (exact in Hilbert space). This is the Banach-space MLMC MSE bound (type-2 Bienaymé).

## 16. `giles_theorem1_banach`

**Rendering.** Same setting as #15, plus:
- $P\in L^1(\nu)$;
- costs $\mathrm{cost}_{\ell,n}\in L^1(\mu)$ with $\mathbb E\,\mathrm{cost}_{\ell,n}=C_\ell$;
- $\alpha,\beta,\gamma,c_1,c_2,c_3>0$ and $\alpha\ge\tfrac12\min(\beta,\gamma)$;
- (i) $\|\mathbb E_\nu(P_\ell-P)\|\le c_12^{-\alpha\ell}$;
- (iii) $\mathbb E_\nu\|\Delta P_\ell-\mathbb E\Delta P_\ell\|^2\le c_22^{-\beta\ell}$;
- (iv) $C_\ell\le c_32^{\gamma\ell}$.

Then there is $c_4>0$ such that for all $\varepsilon\in(0,e^{-1})$ there are $L$ and $N>0$ with $\|\hat Y-\mathbb E_\nu P\|^2$ integrable, $\mathbb E\|\hat Y-\mathbb E_\nu P\|^2<\varepsilon^2$, and $\mathbb E[\text{totalCost}]\le c_4\cdot$`complexityBound α β γ ε`.

**Assessment.** True. By #15 with $m=\mathbb E_\nu P$, MSE $\le2\tau^2\sum V_\ell/N_\ell+2c_1^22^{-2\alpha L}$, and $\mathbb E[\text{cost}]=\sum N_\ell C_\ell$. Giles' allocation $N_\ell\propto\varepsilon^{-2}\sqrt{V_\ell/C_\ell}\cdot\sum\sqrt{V_kC_k}$ (with bounds in place of $V_\ell,C_\ell$) gives the three regimes. The rounding term $\sum_{\ell\le L}C_\ell\lesssim\varepsilon^{-\gamma/\alpha}$ is dominated in each case exactly when $\alpha\ge\tfrac12\min(\beta,\gamma)$. $\tau^2$ only enters $c_4$.

Non-vacuous (e.g. $E=\mathbb R$, $P_\ell=P$ constant, $\Omega_0$ a point). No junk: `complexityBound` with $\varepsilon>0$ is genuine `rpow`/`log`. Costs need not be nonnegative, which is harmless. This is Giles (2008, Oper. Res.) Theorem 1, Banach-space version under type 2 (cf. Heinrich's multilevel work in Banach spaces).
