# Blind read-back report: packet R37 (tau-leaping extensions)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round22/packet_R37_tau.lean` |
| declarations audited | 10 theorems (fully assessed) + 11 local definitions (rendered); the 15 appended external definitions are rendered for context |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round22/work_R37/` (`weak_error.py/.out`, `level_variance.py/.out`, `adaptive.py/.out`, `Check1.lean/.out`, `Check2.lean/.out`) |

Lean checks (scratch files only, `import MlmcLean`, one process at a time, no `lake build`):
- `Check1.lean`: every packet definition, including the appended ones, agrees with the library definition by `rfl`. All of them compiled.
- `Check2.lean`: restates theorems 1, 2 and 4 and prints them with `pp.numericTypes` and `pp.coercions.types`. It also gives an **independent proof** (it does not use any repo instance) that every `tauLevelLaw lam T x₀ ℓ` is a probability measure, so `Measure.infinitePi (fun _ : ℕ × ℕ => tauInputLaw lam T x₀) ≠ 0`. It compiled with no errors.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `exactLaw_tauStep_le_linear` | theorem | true | no | no |
| 2 | `tauLeaping_weak_error_exact_linear` | theorem | true | no | no |
| 3 | `tauLeaping_weak_error_exact_lipschitz` | theorem | true | no | no |
| 4 | `tauLeaping_mlmc_exact_lipschitz` | theorem | true | no | no (the `infinitePi` measure is not 0; checked in Lean) |
| 5 | `adaptRun_law` | theorem | true | no | no |
| 6 | `coupledIncr_bind_map_add` | theorem | true | no | no |
| 7 | `adaptUnion_baseGrid` | theorem | true | no | no |
| 8 | `adaptUnion_fine` | theorem | true | no | no |
| 9 | `adaptUnion_coarse` | theorem | true | no | no |
| 10 | `adaptUnion_2_4` | theorem | true | no | no |

## Main points for a human auditor

1. **All 10 statements are true, none is vacuous, and none relies on a junk value.** Numerical checks (exact pmf computation with truncation) agree. Worst observed ratio of error to bound: 0.75 for theorem 1, 0.66 for theorem 2 and 0.23 for theorem 3. All law identities in the Adaptive section match to within $10^{-12}$ in total variation.
2. **Junk trap avoided in theorem 4.** Mathlib's `Measure.infinitePi` is *defined* to be `0` unless every factor is a probability measure. If that happened, theorem 4 would hold trivially (MSE $=0$; take $L=0$, $N\equiv1$, $c_4=1$). I proved in a scratch file, from the packet definitions alone, that every `tauLevelLaw ℓ` is a probability measure, so the sampling measure is a genuine probability measure.
3. **Scope is narrower than the standard tau-leaping results.** The model is a single-species *pure-birth* chain on $\mathbb N$ (jumps of $+1$) with a *bounded* propensity $\lambda(x)\le\Lambda$. The "exact law" is *defined* by uniformization at rate $\Lambda$. This excludes unbounded propensities (e.g. a linear birth process $\lambda(x)=cx$) and multi-reaction networks. Within this scope no Lipschitz hypothesis on $\lambda$ is needed: on $\mathbb N$, bounded rates are automatically $\Lambda$-Lipschitz.
4. **Theorem 2 needs `hN : 0 < N`.** With $N=0$ the right-hand side is $(\dots)/0=0$ while the left-hand side is $|\Phi(x_0)-\mathbb E\Phi(X_T)|$, so the hypothesis is necessary and is not a junk shortcut.
5. **Theorem 4.** The constant $c_4$ is chosen after (so may depend on) $\lambda,\Lambda,T,x_0,\Phi,K$, which is standard. The cost model is $\sum_\ell N_\ell 2^\ell$. The restriction $\varepsilon<e^{-1}$ is Giles' standard one. The MSE bound is strict ($<\varepsilon^2$). Numerically the level variance is $V_\ell=O(2^{-\ell})$ even for a discontinuous alternating $\lambda$, which confirms $\beta=1=\gamma$.
6. **Adaptive section.** Time is the lattice $\delta\mathbb N$ and step sizes $\nu(t,x)\in\mathbb N$ are counted in units of $\delta$. The hypotheses "$\nu\ge1$ before $M$" and "(at least one) selector lands exactly on $M$" are **necessary**:
   - dropping `hT` in theorem 7 gives total-variation distance 2;
   - a coarse selector with $\nu=0$ in theorem 8 gives total-variation distance 0.71.

   These results are pure identities between laws (consistency of the union-grid coupling and telescoping). The packet contains no error or complexity bound for the adaptive scheme.
7. Theorem 1's bound is not sharp. A coupling argument gives $(A+Bx+2B)(\Lambda h)^2\le 2(\Lambda h)^2(A+B(x+1))$. This slack is harmless.

---

## Definitions (rendering only)

Appended external definitions (all confirmed equal to the library ones by `rfl`):
- `poissonMeasure r` (Mathlib) is $\mathrm{Poi}(r)$ on $\mathbb N$, a probability measure.
- `tauStep lam h x` is the law of $x+\mathrm{Poi}(h\lambda(x))$: one tau-leap of size $h$.
- `tauChain lam h x₀ n` is the law of $Y_n$ for the tau-leaping chain $Y_0=x_0$, $Y_{k+1}\sim$ `tauStep h Y_k`.
- `jumpKernel lam Λ x` $=\frac{\lambda(x)}{\Lambda}\delta_{x+1}+(1-\frac{\lambda(x)}{\Lambda})\delta_x$, computed in $\mathbb R_{\ge0}$ (so $\lambda/0=0$ and truncated subtraction). `jumpPow n x` is its $n$-step law.
- `exactLaw lam Λ t x` $=\sum_n \mathrm{Poi}(\Lambda t)(n)\,$`jumpPow n x`. This is the uniformization representation of the law at time $t$ of the pure-birth CTMC with rates $\lambda$ started at $x$, valid when $\lambda\le\Lambda$.
- `couplePair a b (p₁,p₂)` $=(p_1+[b<a]p_2,\;p_1+[a<b]p_2)$. `coupledIncr a b` is the law of `couplePair a b` under $\mathrm{Poi}(\min(a,b))\otimes\mathrm{Poi}(\max-\min)$. This is the "split" coupling: its marginals are $\mathrm{Poi}(a)$ and $\mathrm{Poi}(b)$, and the two components differ by a $\mathrm{Poi}(|a-b|)$ amount.
- `coupledTwoStep lam h (f,c)` performs two fine tau-leaps of size $h$ (rates $\lambda(f)$, then $\lambda(f+i_1)$) coupled with two half-increments of one coarse leap of size $2h$ (rate $\lambda(c)$ both times). `coupledChain lam h x₀ k` is $k$ such steps from $(x_0,x_0)$.
- `tauLevelLaw lam T x₀ 0` is the law of $(Y,Y)$ with $Y\sim$ `tauChain T x₀ 1`. `tauLevelLaw lam T x₀ (ℓ+1)` is `coupledChain` with $h=T/2^{\ell+1}$ for $2^\ell$ steps: a fine path with $2^{\ell+1}$ steps of size $T/2^{\ell+1}$ coupled to a coarse path with $2^\ell$ steps of size $T/2^\ell$.
- `tauInputLaw` is the independent product over $\ell\in\mathbb N$ of the `tauLevelLaw ℓ`, on $\mathbb N\to\mathbb N\times\mathbb N$.
- `tauFine Φ ℓ y` $=\Phi((y_\ell)_1)$ and `tauCoarse Φ ℓ y` $=\Phi((y_{\ell+1})_2)$.
- `fineCoarseDiff Pf Pc 0` $=$ `Pf 0`, and `fineCoarseDiff Pf Pc (ℓ+1)` $=$ `Pf (ℓ+1)` $-$ `Pc ℓ`.
- `blockMean f ω i N x` $=N^{-1}\sum_{n<N} f_i(\omega_{(i,n)}(x))$.

Local definitions (section `Adaptive`, with parameters $\lambda:\mathbb N\to\mathbb R_{\ge0}$ and base step $\delta\in\mathbb R_{\ge0}$; a state is a triple $p=(x,\ \bar x,\ \tau)$ meaning current value, value frozen at the last step start, and lattice index of the next step end):
- `tauAdvance ν u p i`: add $i$ to $x$. If $u=\tau$ (the step ends now), reset to $(x+i,\ x+i,\ u+\nu(u,x+i))$; otherwise return $(x+i,\bar x,\tau)$.
- `adaptStart ν t x` $=(x,x,t+\nu(t,x))$.
- `adaptSubStep ν j p`: one base substep $j\to j+1$. The increment is $\mathrm{Poi}(\delta\lambda(\bar x))$, followed by `tauAdvance ν (j+1)`.
- `adaptRun ν j r p`: $r$ consecutive base substeps starting at lattice time $j$.
- `adaptCoupledStep νf νc j (pf,pc)`: one base substep for a fine/coarse pair. The increments come from `coupledIncr`$(\delta\lambda(\bar x_f),\delta\lambda(\bar x_c))$ and each component is advanced by its own selector. `adaptCoupledRun` is $r$ such substeps.
- `adaptUnionStep νf νc M (t,pf,pc)`: if $t\ge M$, stay put. Otherwise jump to $m=\min(\tau_f,\tau_c)$, the next point of the union grid, with coupled increments `coupledIncr`$((m-t)\delta\lambda(\bar x_f),(m-t)\delta\lambda(\bar x_c))$, where $m-t$ is ℕ-subtraction (never truncated under the theorems' hypotheses). Then apply `tauAdvance` at $m$ to both components. `adaptUnionRun νf νc M K` is $K$ such steps.
- `adaptTauStep ν M (t,x)`: if $t\ge M$, stay put. Otherwise go to $(t+\nu(t,x),\ x+\mathrm{Poi}(\nu(t,x)\,\delta\,\lambda(x)))$: one adaptive tau-leap. `adaptTauRun ν M k` is $k$ such steps.
- `adaptUnionInit νf νc x₀` $=(0,\ $`adaptStart νf 0 x₀`$,\ $`adaptStart νc 0 x₀`$)$.

---

## 1. `exactLaw_tauStep_le_linear`

**Rendering.** Fix $\lambda:\mathbb N\to\mathbb R_{\ge0}$ and $\Lambda\in\mathbb R_{\ge0}$ with $\lambda(x)\le\Lambda$ for all $x$. Let $f:\mathbb N\to\mathbb R$ and $A,B\in\mathbb R$ satisfy $|f(y)|\le A+B\,y$ for all $y\in\mathbb N$ (with $y$ cast to $\mathbb R$). Then for every $h\in\mathbb R_{\ge0}$ and $x\in\mathbb N$:
- $f$ is integrable under `exactLaw` $(h,x)$ and under `tauStep` $(h,x)$, and
- $\bigl|\mathbb E_x f(X_h)-\mathbb E f(x+\mathrm{Poi}(h\lambda(x)))\bigr|\le 2(\Lambda h)^2\,(A+B(x+1))$, computed in $\mathbb R$ (Lean elaborates this as `2 * (↑Λ * ↑h)^2 * (A + B * (↑x + 1))`).

**Assessment.** *True.* The hypothesis forces $A\ge0$ and $B\ge0$. Represent both laws with the same $N\sim\mathrm{Poi}(\Lambda h)$ potential jumps. The tau-step is the thinning of these jumps with constant acceptance probability $\lambda(x)/\Lambda$. When $N\le1$ the two constructions coincide, and both values always lie in $[x,x+N]$. Hence the error is at most
$$\mathbb E\bigl[2(A+B(x+N))\mathbf 1_{N\ge2}\bigr]\le (A+Bx)a^2+2Ba^2\le 2a^2(A+B(x+1)),\qquad a=\Lambda h,$$
using $P(N\ge2)\le a^2/2$ and $\mathbb E[N\mathbf 1_{N\ge2}]=a(1-e^{-a})\le a^2$. Integrability follows from the linear growth of $f$ and the finite Poisson moments.

When $\Lambda=0$, both laws are $\delta_x$, and $0\le0$ holds genuinely. Numerically, the worst case of $\sum_y|\mu-\nu|(y)(A+By)$ divided by the bound is $0.748$ (`weak_error.out`).

*Vacuity:* none. Example: $\lambda\equiv\Lambda=1$, $f=\mathrm{id}$, $A=0$, $B=1$, $h=1$, $x=0$.

*Junk values:* none. $\lambda/\Lambda$ is only junk when $\Lambda=0$, and then no jump is ever proposed. *Hypotheses:* bounded rates are a modelling restriction (point 3).

*Standard fact:* the local (one-step) weak error of tau-leaping is $O(h^2)$ (cf. Rathinam–Petzold–Cao–Gillespie 2005; Li 2007), here proved via uniformization.

## 2. `tauLeaping_weak_error_exact_linear`

**Rendering.** Assume $\lambda\le\Lambda$ and $|\Phi(y)|\le A+By$ on $\mathbb N$. For $T\in\mathbb R_{\ge0}$, $x_0\in\mathbb N$ and $N\in\mathbb N$ with $N>0$:
- $\Phi$ is integrable under `tauChain lam (T/N) x₀ N` (that is, $N$ tau-leaps of size $T/N$, with $T/N$ computed in $\mathbb R_{\ge0}$) and under `exactLaw lam Λ T x₀`, and
- $\bigl|\mathbb E\Phi(Y_N)-\mathbb E\Phi(X_T)\bigr|\le \dfrac{2\Lambda^2T^2\,(A+B(1+x_0+\Lambda T))}{N}$ in $\mathbb R$.

**Assessment.** *True.* Let $u_s(y)=\mathbb E_y\Phi(X_s)$ and $h=T/N$. Use the semigroup property of `exactLaw` (it is uniformization) to telescope:
$$\mathbb E\Phi(Y_N)-\mathbb E\Phi(X_T)=\sum_{n<N}\mathbb E[(P^\tau_h-P^{ex}_h)u_{T-(n+1)h}(Y_n)].$$
Since $|u_s(y)|\le (A+B\Lambda s)+By$, theorem 1 bounds each term by $2\Lambda^2h^2(A+B\Lambda s_n+B(\mathbb EY_n+1))$. With $\mathbb EY_n\le x_0+\Lambda nh$ and $s_n+nh\le T$, each term is at most $2\Lambda^2h^2(A+B(1+x_0+\Lambda T))$. Summing $N$ terms gives the claim. Numerically the worst ratio of error to bound is $0.658$.

*Vacuity:* none. Example: $\lambda\equiv1=\Lambda$, $\Phi=\mathrm{id}$, $T=1$, $N=1$.

*Junk:* none. `hN` is genuinely needed: for $N=0$ the right-hand side would be $(\dots)/0=0$ and the claim false.

*Standard result:* tau-leaping has weak order 1 (Li 2007; Anderson–Ganguly–Kurtz 2011), here for a pure-birth process with bounded rates.

## 3. `tauLeaping_weak_error_exact_lipschitz`

**Rendering.** This is theorem 2 for $\Phi$ that is $K$-Lipschitz on $\mathbb N$ ($|\Phi(x)-\Phi(y)|\le K|x-y|$ for all $x,y\in\mathbb N$), with no growth constant. Both integrabilities hold, and the error is at most $2\Lambda^2T^2K(1+x_0+\Lambda T)/N$.

**Assessment.** *True.* Taking $x=0$, $y=1$ shows $K\ge0$. Both measures are probability measures, so the error is unchanged when $\Phi$ is replaced by $\Phi-\Phi(0)$. That function satisfies $|\cdot|\le 0+Ky$, so theorem 2 applies with $A=0$, $B=K$. Numerically the worst ratio (using the Wasserstein-1 formula $K\sum_y|F_\mu-F_\nu|$) is $0.226$.

*Vacuity:* none. Example: $\Phi=\mathrm{id}$, $K=1$.

*Junk:* none, and `hN` is needed as in theorem 2.

*Standard result:* weak order 1 of tau-leaping for Lipschitz observables.

## 4. `tauLeaping_mlmc_exact_lipschitz`

**Rendering.** Assume $\lambda\le\Lambda$, and fix $T$, $x_0$ and a $K$-Lipschitz $\Phi$ on $\mathbb N$. **There exists** $c_4>0$, which may depend on all of these data, such that for **every** $\varepsilon\in(0,e^{-1})$ **there exist** $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with $N_\ell>0$ for all $\ell$, satisfying the following.

Sample $\omega=(\omega_{(\ell,n)})_{(\ell,n)\in\mathbb N^2}$ i.i.d. from `tauInputLaw`, so each $\omega_{(\ell,n)}$ is an independent family $(\omega_{(\ell,n)}(k))_k$ with $\omega_{(\ell,n)}(k)\sim$ `tauLevelLaw k`. Define the estimator
$$\hat Y=\sum_{\ell=0}^{L}\frac1{N_\ell}\sum_{n<N_\ell}\Delta_\ell(\omega_{(\ell,n)}),$$
with $\Delta_0(y)=\Phi(y_0^{(1)})$ and $\Delta_{\ell+1}(y)=\Phi(y_{\ell+1}^{(1)})-\Phi(y_{\ell+1}^{(2)})$ (the fine minus the coarse component). Then:
- $(\hat Y-\mathbb E\Phi(X_T))^2$ is integrable,
- $\mathbb E(\hat Y-\mathbb E\Phi(X_T))^2<\varepsilon^2$, where $\mathbb E\Phi(X_T)$ is the integral under `exactLaw lam Λ T x₀`, and
- $\sum_{\ell\le L}N_\ell 2^\ell\le c_4\,\varepsilon^{-2}(\log\varepsilon)^2$ (with `rpow` $\varepsilon^{(-2:\mathbb R)}$ and $\varepsilon>0$).

**Assessment.** *True.*
- **Telescoping.** The level-$(\ell+1)$ coarse marginal is `tauChain`$(T/2^\ell,2^\ell)$, the law of the level-$\ell$ fine path. This is confirmed numerically, with total variation below $10^{-12}$ (`level_variance.out`). So $\mathbb E\hat Y=\mathbb E\Phi(Y^{(L)})$ with $2^L$ steps of size $T/2^L$, and theorem 3 gives bias $\le C2^{-L}$.
- **Variance.** The split coupling gives $\mathbb E(Y^f-Y^c)^2=O(2^{-\ell})$. A Gronwall argument works because bounded rates on $\mathbb N$ are $\Lambda$-Lipschitz. Numerically, $2^{\ell+1}\,\mathbb E(Y^f-Y^c)^2$ stays bounded (about 2.7, 0.26 and 0.60 for three choices of $\lambda$), so $V_\ell\le K^2C2^{-\ell}$.
- **Complexity.** Giles' complexity theorem with $\alpha=\beta=\gamma=1$ gives cost $O(\varepsilon^{-2}\log^2\varepsilon)$. The strict inequality is obtained by aiming for $\varepsilon^2/2$ for both bias² and variance. Setting $N_\ell=1$ for $\ell>L$ satisfies the positivity condition at no cost.

*Vacuity:* none. $\varepsilon=0.1$ is admissible, and all data can be non-degenerate.

*Junk check (important):* `Measure.infinitePi` is `0` unless every factor is a probability measure, and in that case the statement would hold trivially. `Check2.lean` proves from the packet definitions that every `tauLevelLaw ℓ` is a probability measure, so the product measure is non-zero; it is a genuine probability measure. The factor $(N_\ell)^{-1}$ is never $0^{-1}$ because $N_\ell>0$. $\log\varepsilon$ is evaluated only at $\varepsilon\in(0,e^{-1})$.

*Hypotheses:* standard. $c_4$ depending on the problem data is the usual form.

*Standard result:* the Giles (2008) MLMC complexity theorem in the case $\beta=\gamma$, applied to Anderson–Higham (2012) MLMC for tau-leaping. Here the target is the *exact* CTMC law, with bias controlled by the weak order 1.

## 5. `adaptRun_law`

**Rendering.** Let $\nu:\mathbb N\to\mathbb N\to\mathbb N$ and $M\in\mathbb N$ satisfy $\nu(t,x)\ge1$ and $t+\nu(t,x)\le M$ for all $t<M$ and all $x$. Then for every $x_0$, the law of the current value $p.1$ after $M$ base substeps from `adaptStart ν 0 x₀` (base-grid simulation with frozen rates) equals the law of the state after $M$ steps of the adaptive tau-leap chain `adaptTauRun ν M M (0,x₀)`.

**Assessment.** *True.* Inside a step $[t,t+\nu)$ the rate is frozen at $\lambda(\bar x)$, and $\nu$ independent $\mathrm{Poi}(\delta\lambda(\bar x))$ increments sum to $\mathrm{Poi}(\nu\delta\lambda(\bar x))$. Because steps start below $M$, end at most at $M$ and advance by at least 1, the step ends hit $M$ exactly within at most $M$ steps, after which `adaptTauRun` stays put. Numerically the total variation is at most $1.1\times10^{-14}$ over 30 random instances.

*Vacuity:* none ($\nu\equiv1$). *Junk:* none; all spaces are discrete, so maps are measurable and the measures are probability measures.

*Hypotheses:* both are needed. Without landing, the substep run stops mid-step; with $\nu=0$, it stalls.

*Standard fact:* additivity of Poisson increments; this is the base-grid representation of adaptive tau-leaping.

## 6. `coupledIncr_bind_map_add`

**Rendering.** For $\alpha,\beta,s,t\in\mathbb R_{\ge0}$, any measurable space $\gamma$ and any $F:\mathbb N^2\to\gamma$: if $I\sim$ `coupledIncr(sα,sβ)` and an independent $I'\sim$ `coupledIncr(tα,tβ)`, then $F(I+I')$ has the law of $F$ applied to `coupledIncr((s+t)α,(s+t)β)`.

**Assessment.** *True.* If $s=0$ or $t=0$, one factor is $\delta_{(0,0)}$. Otherwise the indicators $[s\beta<s\alpha]=[\beta<\alpha]$ are the same for $s$, $t$ and $s+t$, and $\mathrm{Poi}$ is additive in both independent coordinates. Any $F$ on $\mathbb N^2$ is measurable. Numerically the total variation is at most $1.3\times10^{-14}$ (with $F=\mathrm{id}$).

*Vacuity:* none. *Junk:* none.

*Standard fact:* Poisson additivity, i.e. the split coupling is a Lévy coupling.

## 7. `adaptUnion_baseGrid`

**Rendering.** Assume $\nu_f\ge1$ and $\nu_c\ge1$ for $t<M$, and that **at least one** of them lands exactly on $M$ ($t+\nu(t,x)\le M$ for all $t<M$ and all $x$). Then the law of the pair of triples $(p_f,p_c)$ after $M$ union-grid steps from `adaptUnionInit` equals the law after $M$ coupled base substeps `adaptCoupledRun … 0 M` from $(\,$`adaptStart νf 0 x₀`$,\ $`adaptStart νc 0 x₀`$)$.

**Assessment.** *True.* Between consecutive points of the union grid, both frozen rates are constant. Theorem 6 merges $m-t$ coupled base increments into one. `tauAdvance` updates only at step ends, which are exactly the union-grid points. The landing selector keeps $m\le M$, so the union run never overshoots, and it reaches $M$ within $M$ steps. Numerically the total variation is at most $3.5\times10^{-13}$.

*Necessity of the hypotheses* (checked numerically): if both selectors overshoot $M$, the total variation is 2.

*Vacuity:* none. *Junk:* the ℕ-subtraction $m-t$ is never truncated, because $m>t$ is an invariant under $\nu\ge1$.

*Standard idea:* the union-of-grids coupling for adaptive MLMC (e.g. Lester–Yates–Giles–Baker 2015 for adaptive tau-leaping; Giles et al. for adaptive SDE MLMC).

## 8. `adaptUnion_fine`

**Rendering.** If $\nu_f\ge1$, $\nu_f$ lands on $M$, and $\nu_c\ge1$ (for $t<M$), then the law of the fine current value after $M$ union steps equals the law of `adaptTauRun νf M M (0,x₀)` (second coordinate).

**Assessment.** *True.* Theorem 7 (first disjunct) reduces this to the coupled base run. The fine component of that run evolves autonomously as `adaptSubStep νf`, because the first marginal of `coupledIncr(a,b)` is $\mathrm{Poi}(a)$. Theorem 5 then finishes. Numerically the total variation is at most $4.8\times10^{-13}$.

*Necessity of `hc1`:* with $\nu_c=0$ the union run stalls, and the total variation is 0.71. The coarse selector may overshoot $M$.

*Vacuity/junk:* none.

## 9. `adaptUnion_coarse`

**Rendering.** This is the mirror image of theorem 8. If $\nu_f\ge1$, $\nu_c\ge1$ and $\nu_c$ lands on $M$, then the coarse current value after $M$ union steps has the law of `adaptTauRun νc M M (0,x₀)`.

**Assessment.** *True*, by the symmetric argument (the second marginal of `coupledIncr` is $\mathrm{Poi}(b)$). Numerically the total variation is at most $4.6\times10^{-13}$.

*Vacuity/junk:* none.

## 10. `adaptUnion_2_4`

**Rendering.** Let $\nu,\nu',\nu''$ all be $\ge1$ before $M$, and let $\nu$ land on $M$. Consider level A, the union run with fine selector $\nu'$ and coarse selector $\nu$, and level B, the union run with fine selector $\nu$ and coarse selector $\nu''$. Then:
- the coarse value of A and the fine value of B have the same law on $\mathbb N$;
- for every $\Phi:\mathbb N\to\mathbb R$, $\Phi(\text{coarse}_A)$ is integrable iff $\Phi(\text{fine}_B)$ is; and
- the two integrals are equal.

**Assessment.** *True.* Both laws equal `adaptTauRun ν M M (0,x₀)`, by theorem 9 (for A) and theorem 8 (for B). The integrability and integral statements follow by `integrable_map_measure` and `integral_map`, since all maps on discrete spaces are measurable. Numerically the total variation is at most $3.3\times10^{-13}$. $\nu'$ and $\nu''$ may overshoot $M$; only the shared selector $\nu$ must land.

*Vacuity/junk:* none. The "iff" and the equality are not trivialised by non-integrability, because the laws are literally equal.

*Standard fact:* the MLMC telescoping-consistency condition that the coarse approximation on level $\ell$ has the same law as the fine approximation on level $\ell-1$. Presumably this is equation (2.4) of the cited paper; I cannot verify that reference blind.
