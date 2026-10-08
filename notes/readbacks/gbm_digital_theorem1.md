# Blind read-back report: packet R33 (digital / barrier / Milstein coupling)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round22/packet_R33_digital.lean` (relative to the scratchpad) |
| declarations audited | 12: 11 theorems plus 1 definition (`barrierPayoff`). The 13 appended definitions are rendered in §0. |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round22/work_R33/` (`digital_rates.py/.out`, `strong_and_exponents.py/.out`, `barrier_rates.py/.out`, `scratch.lean/.out`) |

I compiled a scratch copy (`work_R33/scratch.lean`, using `import MlmcLean`, with every theorem renamed `audit_*` and proved by `sorry`). All 11 statements elaborate. All the appended definitions, and `barrierPayoff`, match the library versions by `rfl` (17 `rfl` examples, all accepted). `stdNormalSeq[f | m]` elaborates to `condExp m stdNormalSeq f`. Output: `work_R33/scratch.out`.

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 0 | `barrierPayoff` | def | n/a (discretely monitored knock-out payoff, monitored at $t_1,\dots,t_m$) | n/a | n/a |
| 1 | `gbm_em_digital_weak_rate` | theorem | true | no | no |
| 2 | `gbm_mil_digital_weak_rate` | theorem | true | no | no |
| 3 | `gbm_em_digital_theorem1` | theorem | true (weaker than the standard $\varepsilon^{-5/2}$) | no | no (an `Integrable` conjunct blocks the junk value) |
| 4 | `gbm_mil_digital_theorem1` | theorem | true | no | no |
| 5 | `gbm_em_barrier_rate` | theorem | true (weak rate weaker than standard) | no (only the sub-case $K_g<0$ is empty) | no (`MemLp 2` is asserted) |
| 6 | `gbm_mil_barrier_rate` | theorem | true | no (same remark) | no |
| 7 | `gbm_em_barrier_theorem1` | theorem | true (weaker than the standard $\varepsilon^{-5/2}$) | no (same remark) | no |
| 8 | `gbm_mil_barrier_theorem1` | theorem | true | no (same remark) | no |
| 9 | `map_milstein_coarse_eq_fine` | theorem | true | no | no (the case $h\le 0$ is trivial via $\sqrt{\text{neg}}=0$) |
| 10 | `integral_condExp_milstein_coarse_eq_fine` | theorem | true | no | partly: the conditional expectations play no role, and for non-integrable $g\circ(\cdot)$ both sides are $0$ by convention |
| 11 | `splitting_milstein_mean_eq` | theorem | true | no | no (the case $h\le0$ is trivial) |

## Main points for a human auditor

1. **No false statements.** All 11 theorems are true in my assessment, and none is vacuous. Paths, couplings and targets are modelled correctly: the coarse path driven by `pairAvg z` reuses the fine Brownian increments, and $\pi_*\mu=\mu$.
2. **EM results are weaker than the standard ones.**
   - Theorems 1 and 5 bound the EM *weak* error only at rate $h^{q}$ with $q<1/2$. The true weak order is 1 (Bally–Talay; my MC run shows successive ratios of about $2$, see `digital_rates.out`).
   - So theorems 3 and 7 give cost $\varepsilon^{-3-\eta}$. Giles' Theorem 1 with $\alpha=1,\beta=1/2,\gamma=1$ gives $\varepsilon^{-5/2}$ for the EM digital option (and the same for the discrete barrier).
   - The statements are correct but not sharp. Their exponent is exactly what Giles' formula $2+(\gamma-\beta)/\alpha$ gives with $\alpha=\beta=q\uparrow 1/2$.
3. **Uniformity in the digital rates.** In theorems 1 and 2 the constant $C$ is uniform in $s_0$, $K$ and $\ell$, which is stronger than the usual statement. It is still true, because the lognormal density is bounded and both schemes converge strongly. The hypothesis $\sigma\neq0$ is genuinely needed: with $\sigma=0$ and $K$ strictly between $s_0(1+rh)^{n}$ and $s_0e^{rT}$, the indicators disagree with probability 1.
4. **Theorem 10's conditioning is decorative.**
   - Mathlib's `integral_condExp` gives $\int\mu[f\mid m]\,d\mu=\int f\,d\mu$ for every sub-σ-algebra $m\le m_0$ with no integrability assumption; for non-integrable $f$ both sides are $0$.
   - So theorem 10 says only $E[g(\text{coarse step})]=E[g(\text{fine step})]=E[g(\text{path}_{n+1})]$, which is theorem 9 plus unfolding a definition.
   - The specific σ-algebras (coarse path together with the first half-increment, and coarse path alone) do not matter. There is no integrability hypothesis on $g$, so for non-integrable $g$ the theorem holds as $0=0$.
5. **Degenerate step sizes.** Theorems 9–11 allow any real $h$. For $h\le0$, `Real.sqrt` returns $0$, every path is deterministic, and the identities hold trivially. This is harmless.
6. **Theorem 11 assumes no measurability of $a,b$.** It is still true: the integrability hypothesis `hint` forces the relevant function of $n+1$ Gaussians to be a.e.-measurable (a Fubini section argument, see §11).
7. **Barrier modelling choices.**
   - $g$ is only Lipschitz, so unbounded payoffs are allowed.
   - $K_g<0$ makes `hg` unsatisfiable, which is a harmless empty sub-case.
   - $A$ is restricted to the half-lines $(-\infty,B]$ (up-and-out) or $(B,\infty)$ (down-and-out).
   - Monitoring is at $t_1,\dots,t_m$, not at $t_0$.
   - The digital target is the undiscounted $P(S_T>K)$ (no $e^{-rT}$).
8. **Redundant conjuncts.** In theorems 1 and 2 the weak-error conjunct follows from the disagreement conjunct, because $|E[\mathbf 1_A-\mathbf 1_B]|\le P(\mathbf 1_A\ne\mathbf 1_B)$ and the exact path has the target law. It adds no independent content.

---

## §0 Notation and the appended definitions

- $\mu=$ `stdNormalSeq` $=\bigotimes_{i\in\mathbb N}N(0,1)$ on $\mathbb R^{\mathbb N}$ (i.i.d. standard normals $z_0,z_1,\dots$).
- `pairAvg`: $(\pi z)_k=(z_{2k}+z_{2k+1})/\sqrt2$. Under $\mu$, $\pi z$ is again i.i.d. $N(0,1)$, so $\pi_*\mu=\mu$.
- `emPath a b h S₀ z`: $S_0=S_0$, $S_{i+1}=S_i+a(S_i,ih)h+b(S_i,ih)\sqrt h\,z_i$. With `gbmDrift r` $=(S,t)\mapsto rS$ and `gbmVol σ` $=(S,t)\mapsto\sigma S$ this is $S_n=S_0\prod_{i<n}(1+rh+\sigma\sqrt h z_i)$.
- `milsteinStep a b h S dW` $=S+a(S)h+b(S)\,dW+\tfrac12 b(S)\,b'(S)\,(dW^2-h)$. Here $b'$ is Mathlib's `deriv`, which is genuine for $b(S)=\sigma S$, so $b'=\sigma$. `milsteinPath`: $S_{i+1}=$ `milsteinStep` $(S_i,\sqrt h z_i)$.
- Write $h_\ell=T/2^\ell$. Then:
  - `gbmExact` $X_\ell(z)=s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt{h_\ell}\sum_{i<2^\ell}z_i\big)$, the exact GBM at $T$ driven by the same increments;
  - `gbmEM` $Y^{E}_\ell(z)=s_0\prod_{i<2^\ell}(1+rh_\ell+\sigma\sqrt{h_\ell}z_i)$;
  - `gbmMil` $Y^{M}_\ell(z)=s_0\prod_{i<2^\ell}\big(1+rh_\ell+\sigma\sqrt{h_\ell}z_i+\tfrac12\sigma^2h_\ell(z_i^2-1)\big)$.
- Write $h^{(m)}_j=T/(m2^j)$, with monitoring index $k$ at time $t_k=kT/m$. Then:
  - `gbmMonExact` $=s_0\exp((r-\sigma^2/2)t_k+\sigma\sqrt{h^{(m)}_j}\sum_{i<k2^j}z_i)$;
  - `gbmMonEM` and `gbmMonMil` are the EM and Milstein paths with step $h^{(m)}_j$, evaluated at step $k2^j$, i.e. at time $t_k$.
- `fineCoarseDiff Pf Pc`: $D_0=P^f_0$ and $D_{\ell+1}(y)=P^f_{\ell+1}(y)-P^c_\ell(y)$.
- `blockMean f ω i N x` $=N^{-1}\sum_{n<N}f_i(\omega(i,n)x)$. With $\omega(p,x)=x_p$ this is the sample mean of $f_i$ over the i.i.d. draws $x_{(i,0)},\dots,x_{(i,N-1)}$ under $\mathbb P=$ `infinitePi` $\bigotimes_{(\ell,n)\in\mathbb N^2}\mu$. For $N=0$ it gives $0^{-1}\cdot 0=0$, but every theorem requires $N_\ell>0$.
- Coupling check: $\sqrt{2h}\,(\pi z)_k=\sqrt h(z_{2k}+z_{2k+1})$ for $h>0$ (sympy check in `strong_and_exponents.out`). Also $X_\ell(\pi z)=X_{\ell+1}(z)$. So the coarse level driven by $\pi z$ is the level-$\ell$ scheme driven by the same Brownian path as the fine level, and $E_\mu[P_\ell\circ\pi]=E_\mu[P_\ell]$.

## §0′ `barrierPayoff` (definition)

**Rendering.** For $g:\mathbb R\to\mathbb R$, a set $A\subseteq\mathbb R$, $m\in\mathbb N$ and a path $S:\mathbb N\to\mathbb R$:
$$\text{barrierPayoff}(g,A,m,S)=g(S_m)\prod_{k=0}^{m-1}\mathbf 1_A(S_{k+1})=g(S_m)\,\mathbf 1\{S_1,\dots,S_m\in A\}.$$
This is a discretely monitored knock-out option paying $g(S_m)$ if the path stays in $A$ at the monitoring dates $1,\dots,m$. Date $0$ is not monitored. For $m=0$ it is just $g(S_0)$.

**Assessment.** It is a definition, so there is nothing to assess. It is the standard discretely monitored barrier payoff.

---

## 1. `gbm_em_digital_weak_rate`

**Rendering.** Let $r,\sigma\in\mathbb R$, $\sigma\ne0$, $T>0$ and $q<1/2$ (any real, possibly negative). Then there is $C\ge0$, depending on $r,\sigma,T,q$ only, such that for **all** $s_0,K\in\mathbb R$ and all $\ell\in\mathbb N$:
1. $\mu\{z:\mathbf 1\{X_\ell(z)>K\}\ne\mathbf 1\{Y^E_\ell(z)>K\}\}\le C\,(T/2^\ell)^q$;
2. $\big|E_\mu\mathbf 1\{Y^E_\ell>K\}-\int\mathbf 1\{s_0e^{(r-\sigma^2/2)T+\sigma\sqrt T w}>K\}\,N(0,1)(dw)\big|\le C(T/2^\ell)^q$.

The base of the power is positive, so `rpow` is genuine. The probability is `Measure.real` of a measurable set.

**Assessment.**
- **Truth: true.**
  - Factor out $s_0$. For $s_0=0$ there is never a disagreement. For $s_0\neq0$ set $c=K/s_0$, so the event is $\{\mathbf 1\{X>c\}\ne\mathbf 1\{Y>c\}\}$, or with $<$ when $s_0<0$. Here $X=e^{(\dots)}$ is lognormal and $Y=\prod(1+rh+\sigma\sqrt h z_i)$.
  - The event is contained in $\{|X-c|\le|X-Y|\}$, so its probability is at most $P(|X-Y|>\delta)+P(|X-c|\le\delta)\le C_p h^{p/2}\delta^{-p}+2\delta\|f_X\|_\infty$.
  - The density bound uses $\sup f_X=e^{-\mu_L+s^2/2}/(s\sqrt{2\pi})<\infty$ because $\sigma\ne0$. Numerically this is $1.97$ for $r=.05$, $\sigma=.2$ ($\mu_L=(r-\sigma^2/2)T$, $s=\sigma\sqrt T$).
  - The moment bound $E|X-Y|^p\le C_ph^{p/2}$ is EM strong order $1/2$.
  - Taking $\delta=h^{1/2-\epsilon}$ and $p$ large gives $O(h^{q})$ for any $q<1/2$, uniformly in $c$ and in the sign of $s_0$. Finitely many coarse levels and $q\le0$ are absorbed into $C$, since the probability is at most 1 and $h^q>0$.
  - Part 2 follows: the difference of the two means is at most the disagreement probability, because $\sqrt{h_\ell}\sum_{i<2^\ell}z_i\sim N(0,T)=\sqrt T\,N(0,1)$.
  - MC check (`digital_rates.out`): successive ratios of the disagreement probability are $\approx1.41=2^{1/2}$.
- **Vacuity:** no. Instance: $r=0.05$, $\sigma=0.2$, $T=1$, $q=0.4$.
- **Junk values:** none.
- **Remarks.**
  - Uniformity in $s_0$ and $K$ is stronger than usual, but valid.
  - The weak-error conjunct is far from sharp: the true EM weak order for the digital is 1 (Bally–Talay 1996, nondegenerate GBM). The MC weak-error ratios are $\approx2$. The conjunct is also redundant given part 1.
  - $\sigma\ne0$ is necessary.
- **Standard fact:** EM strong order $1/2$ plus a bounded density implies an $O(h^{1/2-})$ digital disagreement rate (Giles 2008; Avikainen 2009).

## 2. `gbm_mil_digital_weak_rate`

**Rendering.** This is the same as theorem 1 with Milstein ($Y^M_\ell$) in place of EM, and $q<1$. There is $C\ge0$ (depending on $r,\sigma,T,q$) such that for all $s_0,K,\ell$: $\mu\{\mathbf 1\{X_\ell>K\}\ne\mathbf 1\{Y^M_\ell>K\}\}\le C(T/2^\ell)^q$, and the digital weak error is at most $C(T/2^\ell)^q$.

**Assessment.**
- **Truth: true.** The argument is the same as in theorem 1, with Milstein strong order 1 for GBM ($E|X-Y^M|^p\le C_ph^p$; MC strong-error ratios $\approx2.0$ in `strong_and_exponents.out`). With $\delta=h^{1-\epsilon}$ this gives $O(h^{1-})$ uniformly in $c$. The weak part follows as before.
- **Vacuity:** no.
- **Junk values:** none. `deriv` of $S\mapsto\sigma S$ is the genuine $\sigma$.
- **Remarks.** The rate is sharp up to logarithms. The uniformity remark from theorem 1 applies.
- **Standard fact:** Milstein strong order 1 implies a digital disagreement probability of $O(h^{1-})$ (Giles, "Improved MLMC convergence using the Milstein scheme", 2008).

## 3. `gbm_em_digital_theorem1`

**Rendering.**
- Fix $r,\sigma,s_0,K$, $\sigma\ne0$, $T>0$, $\eta>0$. Then $\exists c_4>0$ such that $\forall\varepsilon\in(0,e^{-1})$ $\exists L\in\mathbb N$ and $\exists N:\mathbb N\to\mathbb N$ with $N_\ell\ge1$ for all $\ell$.
- Define the estimator $\hat Y(x)=\sum_{\ell=0}^{L}N_\ell^{-1}\sum_{n<N_\ell}D_\ell(x_{\ell,n})$, where $D_0(z)=\mathbf 1\{Y^E_0(z)>K\}$ and $D_{\ell+1}(z)=\mathbf 1\{Y^E_{\ell+1}(z)>K\}-\mathbf 1\{Y^E_\ell(\pi z)>K\}$. The $x_{\ell,n}$ are i.i.d. $\mu$ under $\mathbb P=\bigotimes_{\mathbb N^2}\mu$.
- Define the target $P^*=P(s_0e^{(r-\sigma^2/2)T+\sigma\sqrt TW}>K)$ with $W\sim N(0,1)$.
- Then three things hold:
  - (i) $(\hat Y-P^*)^2\in L^1(\mathbb P)$;
  - (ii) $E_{\mathbb P}(\hat Y-P^*)^2<\varepsilon^2$;
  - (iii) $\sum_{\ell\le L}N_\ell 2^\ell\le c_4\varepsilon^{-3-\eta}$.
- $c_4$ may depend on all problem data and on $\eta$, but not on $\varepsilon$.

**Assessment.**
- **Truth: true.**
  - $E D_{\ell+1}=E P_{\ell+1}-E P_\ell$ because $\pi_*\mu=\mu$, so the sum telescopes to $E\hat Y=EP_L$.
  - Bias: $|EP_L-P^*|\le C h_L^q$ by theorem 1.
  - Variance: $V_\ell\le E D_\ell^2=P(\text{fine}\ne\text{coarse})\le P(\text{fine}\ne X_{\ell+1})+P(\text{coarse}\ne X_\ell\circ\pi)\le 2Ch_\ell^q$, using $X_\ell\circ\pi=X_{\ell+1}$.
  - Giles' Theorem 1 with $\alpha=\beta=q$, $\gamma=1$ (and $\alpha\ge\frac12\min(\beta,\gamma)$) gives cost $O(\varepsilon^{-2-(1-q)/q})$. Choosing $q\ge1/(2+\eta)<1/2$ gives exponent at most $3+\eta$ (sympy in `strong_and_exponents.out`).
  - Integrability holds because the integrand is bounded and measurable.
- **Vacuity:** no. Instance: $r=.05$, $\sigma=.2$, $s_0=K=T=1$, $\eta=.1$.
- **Junk values:** the `Integrable` conjunct prevents the "non-integrable integral $=0$" junk value from making (ii) trivial. There are no divisions by $0$, since $N_\ell\ge1$.
- **Remarks.**
  - This is **weaker than the standard result**. The true weak order of EM for this digital is $\alpha=1$, so Giles (2008) gets $O(\varepsilon^{-5/2})$ for the EM digital ($\beta=1/2$). The packet only uses $\alpha\approx1/2$, giving $\varepsilon^{-3-\eta}$.
  - The cost model $\sum N_\ell2^\ell$ ignores the extra coarse cost (factor $\le3/2$), which is standard.
  - The target is undiscounted.
- **Standard fact:** the MLMC complexity theorem (Giles 2008, Theorem 1) applied to the EM digital option.

## 4. `gbm_mil_digital_theorem1`

**Rendering.** This is the same as theorem 3 with Milstein ($Y^M$) in both the fine and coarse levels, and cost bound $\sum_{\ell\le L}N_\ell2^\ell\le c_4\varepsilon^{-2-\eta}$.

**Assessment.**
- **Truth: true.** Theorem 2 gives $\alpha=\beta=q$ for any $q<1$, so the exponent $2+(1-q)/q\to2$. Pick $q\ge1/(1+\eta)$.
- **Vacuity:** no.
- **Junk values:** none (`Integrable` is asserted).
- **Remarks.** The standard result is $O(\varepsilon^{-2}(\log\varepsilon)^2)$ when $\beta=\gamma$, so $\varepsilon^{-2-\eta}$ is equivalent up to $\varepsilon^{-\eta}$. Giles' conditional-expectation smoothing would give $\beta=3/2$ and $O(\varepsilon^{-2})$; that is not claimed here.
- **Standard fact:** Giles MLMC Theorem 1 with the Milstein scheme.

## 5. `gbm_em_barrier_rate`

**Rendering.**
- Hypotheses: $\sigma\ne0$, $T>0$, $m\ge1$. $g$ satisfies $|g(x)-g(y)|\le K_g|x-y|$ for all $x,y$, with $K_g\in\mathbb R$. $A=(-\infty,B]$ or $A=(B,\infty)$. $q<1/2$.
- Define $\Pi_j(z)=\text{barrierPayoff}(g,A,m,S^{E,j}(z))$, where $S^{E,j}_k$ is EM with step $h^{(m)}_j=T/(m2^j)$ at time $t_k$. Set $Y_j(z)=\Pi_{j+1}(z)-\Pi_j(\pi z)$.
- Claim: there is $C\ge0$ (depending on all data and $q$) such that for every $j\in\mathbb N$:
  - (a) $Y_j\in L^2(\mu)$;
  - (b) $\operatorname{Var}_\mu(Y_j)\le C\,(T/(m2^{j+1}))^q$;
  - (c) $|E_\mu\Pi_j-E_\mu\Pi^{ex}|\le C\,(T/(m2^j))^q$, where $\Pi^{ex}$ is the payoff of the exact GBM sampled at $t_1,\dots,t_m$ (via `gbmMonExact … m 0`, i.e. increments $\sqrt{T/m}\,z_i$).

**Assessment.**
- **Truth: true.**
  - (a) $|g(x)|\le|g(0)|+K_g|x|$ and the EM path is a polynomial in Gaussians, so all moments are finite. $g$ is continuous, hence measurable.
  - (b) Bound $E Y_j^2\le K_g^2E|S^f_m-S^c_m|^2+E[(|g(S^f_m)|+|g(S^c_m)|)^2\mathbf 1\{\exists k:\mathbf 1_A(S^f_k)\ne\mathbf 1_A(S^c_k)\}]$. This is at most $Ch+C_p\,P(\text{disagree})^{1-1/p}$. Each monitoring-date disagreement probability is $O(h^{1/2-})$ as in theorem 1: the exact $S_{t_k}$, $k\ge1$, has a bounded density because $\sigma\ne0$ and $t_k>0$, which is why it matters that $t_0$ is not monitored. Hence $O(h^{q})$ for every $q<1/2$.
  - (c) The exact path at resolution $j$ has the same joint law at $t_1,\dots,t_m$ as at resolution $0$, so $|E\Pi_j-E\Pi^{ex}|\le E|\Pi_j-\Pi^{ex,j}|=O(h^{1/2-})$ by the same split.
  - MC (`barrier_rates.out`, $g=(x-1)^+$, $A=(-\infty,1.3]$, $m=4$): $EY_j^2$ falls about $5.9\times$ over 6 levels, i.e. about $2^{0.43}$ per level, consistent with $\beta=1/2$ up to MC noise.
- **Vacuity:** no. Instance: $g=\mathrm{id}$, $K_g=1$, $A=(-\infty,1]$, $m=1$. Only the sub-case $K_g<0$ is empty, since `hg` then fails for $x\ne y$.
- **Junk values:** none. `MemLp 2` is asserted, so `variance` (which is `evariance.toReal`) is the true variance and not a junk $0$ from $\infty$.
- **Remarks.** The weak conjunct (c) at $q<1/2$ is weaker than the true EM weak order 1 for discretely monitored options under nondegeneracy. Only half-line barriers are allowed.
- **Standard fact:** strong and weak convergence of EM for discretely monitored barrier options, which supplies the variance and bias hypotheses of MLMC.

## 6. `gbm_mil_barrier_rate`

**Rendering.** This is the same as theorem 5 with Milstein paths $S^{M,j}$ and $q<1$: (a) $Y_j\in L^2$; (b) $\operatorname{Var}Y_j\le C(T/(m2^{j+1}))^q$; (c) $|E\Pi_j-E\Pi^{ex}|\le C(T/(m2^j))^q$.

**Assessment.**
- **Truth: true.** The same decomposition gives $EY_j^2\le Ch^2+C_pP(\text{disagree})^{1-1/p}$, with $P(\text{disagree})=O(h^{1-})$ by Milstein strong order 1. MC: $EY^2$ falls about $25.7\times$ over 6 levels, i.e. about $2^{0.78}$ per level, which is noisy but consistent with $\beta=1$.
- **Vacuity:** no (same remark as theorem 5 about $K_g<0$).
- **Junk values:** none.
- **Standard fact:** the Milstein analogue of theorem 5.

## 7. `gbm_em_barrier_theorem1`

**Rendering.**
- Data as in theorem 5, plus $\eta>0$. Then $\exists c_4>0$ $\forall\varepsilon\in(0,e^{-1})$ $\exists L$ and $\exists N$ with $N_j\ge1$, such that the estimator $\hat Y=\sum_{j\le L}N_j^{-1}\sum_{n<N_j}D_j(x_{j,n})$ satisfies:
  - $(\hat Y-E\Pi^{ex})^2\in L^1(\mathbb P)$;
  - $E(\hat Y-E\Pi^{ex})^2<\varepsilon^2$;
  - $\sum_{j\le L}N_j\,m2^j\le c_4\varepsilon^{-3-\eta}$.
- Here $D_0=\Pi_0$ and $D_{j+1}(z)=\Pi_{j+1}(z)-\Pi_j(\pi z)$ (EM).

**Assessment.**
- **Truth: true.** The sum telescopes because $\pi_*\mu=\mu$. Theorem 5 gives $\alpha=\beta=q\uparrow1/2$, the cost per sample is $m2^j\propto h_j^{-1}$, and Giles' Theorem 1 gives the exponent $\le3+\eta$. The squared error is integrable because each $D_j\in L^2$ and the sum is finite.
- **Vacuity:** no.
- **Junk values:** none (`Integrable` is asserted).
- **Remarks.** This is weaker than the standard $O(\varepsilon^{-5/2})$ (EM weak order 1, $\beta=1/2$), for the same reason as theorem 3.
- **Standard fact:** Giles MLMC Theorem 1 for a discretely monitored barrier option with EM.

## 8. `gbm_mil_barrier_theorem1`

**Rendering.** This is the same as theorem 7 with Milstein, and cost $\sum_{j\le L}N_jm2^j\le c_4\varepsilon^{-2-\eta}$.

**Assessment.**
- **Truth: true.** Theorem 6 gives $\alpha=\beta=q\uparrow1$, so the exponent tends to $2$.
- **Vacuity:** no.
- **Junk values:** none.
- **Standard fact:** Giles' Theorem 1 with $\beta\approx\gamma$: $\varepsilon^{-2}$ up to logarithms, here $\varepsilon^{-2-\eta}$.

## 9. `map_milstein_coarse_eq_fine`

**Rendering.** Let $a,b:\mathbb R\to\mathbb R$ be measurable, $h,S_0\in\mathbb R$ arbitrary, and $n\in\mathbb N$. Write $M^{2h}_n(w)$ for `milsteinPath a b (2h) S₀ w n`. Then the law under $\mu$ of
$$z\mapsto \text{milsteinStep}_{2h}\big(M^{2h}_n(\pi z),\ \sqrt h z_{2n}+\sqrt h z_{2n+1}\big)$$
equals the law under $\mu$ of $w\mapsto\text{milsteinStep}_{2h}(M^{2h}_n(w),\sqrt{2h}\,w_n)$, which is $M^{2h}_{n+1}(w)$ by definition.

**Assessment.**
- **Truth: true.**
  - For $h>0$, $\sqrt h z_{2n}+\sqrt hz_{2n+1}=\sqrt{2h}(\pi z)_n$, so the left function is (right function)$\circ\pi$ and $\pi_*\mu=\mu$.
  - Both functions are measurable: Mathlib's `measurable_deriv` makes `deriv b` measurable for any $b$, and $a,b$ are measurable. So `map_map` applies.
  - For $h\le0$, $\sqrt h=\sqrt{2h}=0$, both paths are deterministic, and the two measures are the same Dirac mass.
- **Vacuity:** no ($a=b=0$).
- **Junk values:** the case $h\le0$ holds only via $\sqrt{\text{neg}}=0$, but that is a degenerate sub-case; for $h>0$ the content is genuine.
- **Standard fact:** the pairwise-averaging coupling of fine and coarse Brownian increments preserves the law (the MLMC telescoping identity for Milstein).

## 10. `integral_condExp_milstein_coarse_eq_fine`

**Rendering.** Let $a,b$ be measurable, $h,S_0$ arbitrary, $n\in\mathbb N$ and $g$ strongly measurable. Write $F_c(z)=g(\text{milsteinStep}_{2h}(M^{2h}_n(\pi z),\sqrt hz_{2n}+\sqrt hz_{2n+1}))$ and $F_f(w)=g(\text{milsteinStep}_{2h}(M^{2h}_n(w),\sqrt{2h}w_n))$. The statement is:
1. $\int E_\mu[F_c\mid\sigma(M^{2h}_n\circ\pi,\ \sqrt h z_{2n})]\,d\mu=\int E_\mu[F_f\mid\sigma(M^{2h}_n)]\,d\mu$;
2. that common value $=\int g(M^{2h}_{n+1})\,d\mu$.

Here $\mu[f\mid m]$ is Mathlib's `condExp`, and the σ-algebras are comaps of measurable maps into $\mathbb R^2$ and $\mathbb R$.

**Assessment.**
- **Truth: true.**
  - Mathlib's `integral_condExp` (`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:236`) states $\int\mu[f\mid m]=\int f$ for $m\le m_0$ and $\mu.\mathrm{trim}$ σ-finite (automatic for a probability measure), with no integrability assumption: if $f$ is not integrable, both sides are $0$.
  - So (1) reduces to $\int F_c=\int F_f$, which follows from theorem 9 and `integral_map` ($g$ strongly measurable).
  - (2) reduces to $\int F_f=\int g(M_{n+1})$, which holds because $F_f=g\circ M^{2h}_{n+1}$ definitionally (checked by `rfl` in `scratch.lean`).
- **Vacuity:** no.
- **Junk values:**
  - The conditional expectations are inert: any sub-σ-algebra would give the same statement.
  - With no integrability hypothesis on $g\circ M_{n+1}$, the non-integrable case holds as $0=0$ (both the `condExp` junk value and the Bochner junk value are $0$).
  - The intended use (smoothing the last step by conditioning, Giles' "conditional expectation" technique) is only reflected as mean-consistency, which is a weak statement but a correct one.
  - The case $h\le0$ is degenerate.
- **Standard fact:** the tower property plus equality of laws; this is the unbiasedness / telescoping requirement for conditional-expectation-smoothed MLMC levels.

## 11. `splitting_milstein_mean_eq`

**Rendering.**
- Let $a,b:\mathbb R\to\mathbb R$ be **arbitrary**, with no measurability assumed. Let $h,S_0\in\mathbb R$, $n\in\mathbb N$, $M\ge1$, and $g:\mathbb R\to\mathbb R$ with $w\mapsto g(M^{2h}_{n+1}(w))\in L^1(\mu)$.
- Under $\mu\otimes\mu$, with $p=(p_1,p_2)$:
  1. $E\big[\frac1M\sum_{i<M}g(\text{milsteinStep}_{2h}(M^{2h}_n(\pi p_1),\sqrt h p_1(2n)+\sqrt hp_2(i)))\big]=E\big[\frac1M\sum_{i<M}g(\text{milsteinStep}_{2h}(M^{2h}_n(p_1),\sqrt{2h}p_2(i)))\big]$;
  2. that common value $=E_\mu[g(M^{2h}_{n+1})]$.
- The division is by $(M:\mathbb R)>0$.

**Assessment.**
- **Truth: true.**
  - Let $G(y_0,\dots,y_n)=g(\text{milsteinStep}_{2h}(M^{2h}_n(y_{0..n-1}),\sqrt{2h}y_n))$, so $g\circ M^{2h}_{n+1}=G\circ(w_0,\dots,w_n)$.
  - In (1), for $h>0$, the $i$-th left summand is $G\big((\pi p_1)_0,\dots,(\pi p_1)_{n-1},(p_1(2n)+p_2(i))/\sqrt2\big)$, and the $i$-th right summand is $G(p_1(0),\dots,p_1(n-1),p_2(i))$. Both arguments are $N(0,1)^{\otimes(n+1)}$, since the coordinates used are disjoint and independent.
  - **Measurability without hypotheses on $a,b$:** `hint` makes $G\circ\mathrm{proj}$ a.e.-equal to a measurable $\Psi$ on $\mu\cong\nu\otimes\rho$. Fubini on the null set gives $G=\Psi(\cdot,r_0)$ $\nu$-a.e. for a suitable $r_0$, so $G$ is $\nu$-a.e.-measurable and integrable.
  - Every summand therefore has integral $E_\nu G=E_\mu g(M_{n+1})$, and averaging $M$ equal terms gives the same value.
  - For $h\le0$ everything is constant.
- **Vacuity:** no ($g=0$, or $a=b=0$ with $g$ bounded).
- **Junk values:** none. $M>0$ prevents $/0$, and `hint` excludes the Bochner junk value.
- **Remarks.** Omitting measurability of $a,b$ is unusual but harmless, since `hint` supplies what is needed.
- **Standard fact:** unbiasedness of path splitting (resampling the final half-increment $M$ times) for the Milstein coarse level, as in Giles' "splitting" technique for discontinuous payoffs.
