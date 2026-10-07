# Blind read-back report: R10 (nested MIMC, smooth payoff)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round16/packet_R10_mimc_smooth.lean` |
| declarations audited | 3 (theorems `nested_mimc_smooth_variance_rate`, `nested_mimc_smooth_mean_rate`, `nested_mimc_smooth_complexity`) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round16/work_R10/` (`brute_defs.py/.out`, `rates_fast.py/.out`, `random_search.py/.out`, Lean scratch files `Scratch.lean/.out`, `Vac.lean/.out`) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `nested_mimc_smooth_variance_rate` | theorem | true (proof sketch; explicit constant confirmed numerically with large margin) | no (explicit instance) | no |
| 2 | `nested_mimc_smooth_mean_rate` | theorem | true (Cauchy–Schwarz + AM–GM from #1) | no | no |
| 3 | `nested_mimc_smooth_complexity` | theorem | true (standard MIMC complexity, $\beta=(2,2)>\gamma=(1,1)$) | no (explicit instance; sampling hypotheses checked in Lean) | no (see the remark on $\int g(z,\cdot)\,d\rho$) |

## Main points for a human auditor

1. All three statements look true and are not vacuous. Example: $Z\in\{-1,0,2\}$ or Rademacher, $W$ Rademacher, $gh_\ell(z,w)=z+w+2^{-\ell}(1+w)$, $f=\sin$ ($K=L=1$). Exact computation for $\ell_1\le 10$, $\ell_2\le 12$ shows that $4^{\ell_1+\ell_2}E[Y^2]$ and $2^{\ell_1+\ell_2}|E Y|$ converge to non-zero constants. The rates are therefore attained, and sharp, on the boundary rows $\ell_1=0$ and $\ell_2=0$ too. A random search over 6000 instances found no violation of the explicit constants. The largest ratio LHS/RHS was 0.51, at the corner $(0,0)$, and at most 0.04 everywhere else.
2. The weak-error hypothesis `hw` (in both forms) is uniform in $z$: it is a $\nu$-essential-supremum bound on the conditional bias $E_W[gh_{\ell+1}-gh_\ell](z)$, or on $E_W[gh_\ell]-E_W[g]$. This is stronger than needed. It rules out natural examples where the conditional bias grows with $z$ and $Z$ is unbounded, for example $gh_\ell=z+w+2^{-\ell}z^2$ with Gaussian $Z$. There `hs` and `hm₄` hold and the conclusion still holds, but `hw` fails. The example in the task context ($+2^{-\ell}c$) satisfies it.
3. `hs` asks for strong order 1 in $L^4$ ($E|gh_{\ell+1}-gh_\ell|^4\le c_s 2^{-4\ell}$), so $\beta_2=2$. This excludes Euler–Maruyama with multiplicative noise (strong order 1/2), but it matches the claimed rate $V=O(2^{-2\ell_1-2\ell_2})$. All moment hypotheses are raw, not centred. A raw bound implies the centred one (factor $\le 16$), so no natural example is excluded. `hm₄` is redundant: Minkowski's inequality gives it from `hgh4` at $\ell=0$ together with `hs`.
4. Theorem 2 adds nothing beyond #1: it is $|EY|\le\sqrt{E Y^2}\le 2^{-(\ell_1+\ell_2)}\sqrt{C_*}\le 2^{-(\ell_1+\ell_2)}(C_*+1)/2$. It still gives the correct mean rate $\alpha=1$, which is sharp in the example.
5. In theorem 3, `g` has no measurability or integrability assumption. If $g(z,\cdot)$ is not $\rho$-integrable, $\int g(z,v)\,d\rho$ is the junk value $0$. But `hw` forces that value to equal $\lim_\ell\int gh_\ell(z,\cdot)\,d\rho$ for $\nu$-a.e. $z$, so in effect the target is $E_Z f(\lim_\ell E_W gh_\ell)$. Truth does not depend on a junk value. The name "$g$" only carries its intended meaning when its sections are integrable.
6. The other integrals in theorem 3 are genuine:
   - the MSE integrand is square-integrable, since each $Y_\ell\circ\omega$ is in $L^2$ by #1 and the samples are measure-preserving;
   - the target $\int f(G)\,d\nu$ is integrable;
   - the cost integrals are integrable by hypothesis.

   Further points, all checked in Lean:
   - `∑ ℓ ∈ I, a - b` parses as `(∑ ℓ ∈ I, a) - b`;
   - `indexSet (fun _ => 1/2) Λ` is the total-degree simplex $\{\ell_1+\ell_2\le 2\Lambda\}$ and is empty when $\Lambda<0$;
   - $c_4$ is chosen before $\varepsilon$, and $\Lambda$ and $N$ depend on $\varepsilon$.

   The cost model only constrains the means $C_\ell\le c_3 2^{\ell_1+\ell_2}$. Costs are not tied to the samples and may even be negative, which is harmless for an upper bound. `hc₃ : 0 < c₃` is superfluous.
7. Theorem 1 bounds the raw second moment $E[Y^2]$, which is stronger than a variance bound. Its constant mixes $f(0)^2$, $f'(0)^4$, $m_4$ and $c_s$ inhomogeneously (from AM–GM steps). That is valid, and the numerical margin is large.

---

## 1. `nested_mimc_smooth_variance_rate`

**Rendering.**

*Setting and hypotheses.*
- $(\mathcal Z,\nu)$ and $(\mathcal W,\rho)$ are probability spaces.
- $f,f',f'':\mathbb R\to\mathbb R$ with $f'=Df$ and $f''=Df'$ everywhere.
- $|f'(y)-f'(x)|\le K(y-x)$ for $x\le y$, so $f'$ is $K$-Lipschitz. This forces $K\ge0$ and $|f''|\le K$.
- $|f''(y)-f''(x)|\le L(y-x)$, so $f''$ is $L$-Lipschitz and $L\ge 0$.
- For every $\ell\in\mathbb N$, $gh_\ell:\mathcal Z\times\mathcal W\to\mathbb R$ is jointly measurable and satisfies:
  - $gh_\ell^4\in L^1(\nu\otimes\rho)$;
  - $E_{\nu\otimes\rho}[gh_\ell^4]\le m_4$;
  - $(2^\ell)^4\,E_{\nu\otimes\rho}[(gh_{\ell+1}-gh_\ell)^4]\le c_s$;
  - for $\nu$-a.e. $z$: $2^\ell\,\bigl|\int(gh_{\ell+1}(z,v)-gh_\ell(z,v))\,\rho(dv)\bigr|\le c_w$.

*Sampling and estimator.* Sample $(Z,W)\sim\nu\otimes\rho^{\otimes\mathbb N}$ (`nestedLaw` $=\nu\otimes$ `Measure.infinitePi`). For a function $g$ write $\bar g_M(Z,W)=M^{-1}\sum_{m<M}g(Z,W_m)$. The antithetic difference is:
- $\Delta_0[g]=f(g(Z,W_0))$;
- for $\ell_1\ge1$ and $M=2^{\ell_1-1}$: $\Delta_{\ell_1}[g]=f(\bar g_{2M})-\tfrac12 f(\bar g_M(W_{0..M-1}))-\tfrac12 f(\bar g_M(W_{M..2M-1}))$.

The second half uses `shiftSeq`. The mixed difference is $Y_{\ell_1,0}=\Delta_{\ell_1}[gh_0]$ and $Y_{\ell_1,\ell_2}=\Delta_{\ell_1}[gh_{\ell_2}]-\Delta_{\ell_1}[gh_{\ell_2-1}]$, both on the same sample.

*Conclusion.* For all $\ell_1,\ell_2\in\mathbb N$:
- $Y_{\ell_1,\ell_2}\in L^2$;
- $4^{\ell_1+\ell_2}\,E[Y_{\ell_1,\ell_2}^2]\le C_*:=2f(0)^2+48|f'(0)|^4+(2+3375K^2+32K^4+336L^2c_w^2)m_4+(4+434K^2)c_s$.

The constant does not depend on $\ell_1,\ell_2$. Powers of 2 are real powers with natural-number exponents.

**Assessment.**

*Truth: true.* Proof sketch:
- **Corner $(0,0)$.** $f(x)^2\le 2f(0)^2+2f'(0)^4+(2+K^2)x^4$, so $E[Y^2]\le 2f(0)^2+2f'(0)^4+(2+K^2)m_4$.
- **Row $\ell_1=0$, $\ell_2\ge1$.** Use $|f(a)-f(b)|\le(|f'(0)|+K(|a|+|b|))|a-b|$, Cauchy–Schwarz and $E d^4\le 16c_s2^{-4\ell_2}$. This gives $4^{\ell_2}E[Y^2]\le 4(f'(0)^4+c_s)+16K^2(m_4+c_s)$.
- **Row $\ell_2=0$, $\ell_1\ge1$.** $|\Delta|\le K(A-B)^2/8$, where $A,B$ are the half means, and $E(A-B)^4\le 48m_4/M^2$. This gives $\le 3K^2m_4$.
- **Interior.** Interpolate $x_t=gh_{\ell_2-1}+t\,d$, where $d=gh_{\ell_2}-gh_{\ell_2-1}$. Then $\frac{d}{dt}\Delta=\tfrac{\bar D}{2}\,[2f'(\mathrm{mid})-f'(A_t)-f'(B_t)]+\tfrac{\delta}{2}[f'(B_t)-f'(A_t)]$, where $\bar D$ is the full mean of $d$ and $\delta$ is the half-mean difference of $d$.
  - The second-difference factor is $\le\min(L(A_t-B_t)^2/4,\,K|A_t-B_t|)$.
  - Split $\bar D=E_W d(z)+(\bar D-E_W d)$. The ess-sup bound $|E_Wd|\le 2c_w2^{-\ell_2}$ pairs with $L$; the centred fluctuation $O(M^{-1/2}2^{-\ell_2})$ in $L^4$ pairs with $K$ through Cauchy–Schwarz with $\|A_t-B_t\|_4=O(M^{-1/2})$.
  - All terms are $O(4^{-\ell_1-\ell_2})$, using only fourth moments. My crude constants were about $36L^2c_w^2m_4+216K^2(m_4+c_s)$, well inside $C_*$.
- **$L^2$ membership.** Follows from measurability and the quadratic growth of $f$ with $gh_\ell\in L^4$.

*Numerics.*
- `brute_defs.py` enumerates every inner sample tuple and mirrors `innerMean`, `shiftSeq`, `nestedDelta` and `nestedMimcDelta` exactly. Five examples (sin, cos, $x^2/2$, $\sin 3x$, $\sin 10x$ with scaled $g$; nonlinear and $z$-dependent level corrections) gave a maximum ratio LHS/$C_*$ of $7\times10^{-5}$.
- `rates_fast.py` (exact binomial sums, $\ell_1\le10$, $\ell_2\le12$) shows that $4^{\ell_1+\ell_2}E[Y^2]$ converges to non-zero limits (about 1.17 in the interior, 1.63 on row $\ell_1=0$, 2.26 on row $\ell_2=0$; maximum 5.90 against a bound of $5.97\times10^5$). So the rate is attained and sharp, including on the boundaries.
- `random_search.py` (6000 random discrete laws, $f=a\sin(bx+c)+dx+ex^2/2+h$ and affine/quadratic $gh$) found a maximum ratio of 0.508, at $(0,0)$. The maximum away from the corner was 0.039.

*Vacuity: not vacuous.* Take $\mathcal Z=\mathcal W=\mathbb R$, $\nu=\rho=$ Rademacher, $f=\sin$, $K=L=1$ (checked in Lean, `Vac.lean`), and $gh_\ell=z+w+2^{-\ell}(1+w)$. Then $m_4=72$, $c_s=1/2$, $c_w=1/2$. The task-context example $z+w+2^{-\ell}c$ also works, with $c_s=c^4/16$ and $c_w=|c|/2$.

*Junk values: none.*
- `hgh4` makes every integral in `hm₄` and `hs` a genuine integral of an integrable function. Without it, `hs` could hold through a junk $0$.
- For a.e. $z$ the sections in `hw` are integrable (Fubini).
- The conclusion asserts `MemLp … 2`, so $\int Y^2$ is genuine.

*Unusual or strong hypotheses.*
- `hw` is a uniform-in-$z$ (ess-sup) bound on the conditional bias. It is stronger than needed and excludes, for example, $gh_\ell=z+w+2^{-\ell}z^2$ with $Z\sim N(0,1)$.
- `hs` is strong order 1 in $L^4$, which excludes multiplicative-noise Euler–Maruyama.
- `hm₄` is redundant.
- The moments are raw rather than centred, which is harmless.
- The conclusion is a raw second-moment bound, stronger than a variance bound.

*Standard result.* This is the variance rate $\beta=(2,2)$ for the antithetic nested estimator with a $C^{2,1}$ payoff (Giles 2018; Bujok–Hambly–Reisinger antithetic nested MLMC), combined with an $L^4$ strong-order-1 approximation $g_\ell$ in the second MIMC direction (Haji-Ali–Nobile–Tempone mixed differences).

## 2. `nested_mimc_smooth_mean_rate`

**Rendering.** The hypotheses are identical to #1. Conclusion: for all $\ell_1,\ell_2$, $Y_{\ell_1,\ell_2}\in L^1(\nu\otimes\rho^{\otimes\mathbb N})$ and $2^{\ell_1+\ell_2}\,|E[Y_{\ell_1,\ell_2}]|\le (C_*+1)/2$, with $C_*$ as in #1.

**Assessment.**

*Truth: true.* $L^2\subset L^1$ on a probability space. Then $|EY|\le\sqrt{EY^2}\le 2^{-(\ell_1+\ell_2)}\sqrt{C_*}$ and $\sqrt{C_*}\le (C_*+1)/2$ by AM–GM.

*Numerics.* $2^{\ell_1+\ell_2}|EY|$ converges to about 0.33 in the example, so $\alpha=1$ is sharp there. All tests passed. The random-search maximum of LHS/RHS was 0.71, at $(0,0)$ with $f\approx$ constant $1/\sqrt2$.

*Vacuity: not vacuous* (same instance as #1).

*Junk values: none.*

*Remark.* This adds nothing beyond #1. The bound is the Cauchy–Schwarz consequence and does not exploit cancellation in the mean. That is enough for $\alpha=(1,1)$, which is the true order for this estimator.

*Standard result.* The weak rate $\alpha=(1,1)$ for antithetic nested MIMC with a smooth payoff.

## 3. `nested_mimc_smooth_complexity`

**Rendering.**

*Hypotheses.*
- The hypotheses on $f$ and on `hgh`, `hgh4`, `hm₄` and `hs` are as in #1.
- `hw` is replaced by a bound against a limit $g:\mathcal Z\to\mathcal W\to\mathbb R$, which has no measurability or integrability assumption: for every $\ell$ and $\nu$-a.e. $z$, $2^\ell\,\bigl|\int gh_\ell(z,v)\rho(dv)-\int g(z,v)\rho(dv)\bigr|\le c_w$.
- $(\Omega,\mu)$ is a probability space. For $\ell\in\mathbb N^2$ (`Fin 2 → ℕ`, with $\ell_1$=`ℓ 0` the inner-sample level and $\ell_2$=`ℓ 1` the discretisation level) and $n\in\mathbb N$, the samples $\omega_{(\ell,n)}:\Omega\to\mathcal Z\times\mathcal W^{\mathbb N}$ each push $\mu$ forward to $\nu\otimes\rho^{\otimes\mathbb N}$ and are mutually independent (`iIndepFun`).
- $\mathrm{cost}(\ell,n)\in L^1(\mu)$ with $E[\mathrm{cost}(\ell,n)]=C(\ell)\le c_3 2^{\ell_1+\ell_2}$, where $c_3>0$.

*Conclusion.* There exists $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $\Lambda\in\mathbb R$ and $N:\mathbb N^2\to\mathbb N$, with $N_\ell>0$ for every $\ell$, satisfying:
- $E_\mu\Bigl[\Bigl(\sum_{\ell\in I_\Lambda}N_\ell^{-1}\sum_{n<N_\ell}Y_\ell(\omega_{(\ell,n)})-\int_{\mathcal Z} f\bigl(\textstyle\int g(z,v)\rho(dv)\bigr)\nu(dz)\Bigr)^2\Bigr]<\varepsilon^2$;
- $E_\mu\bigl[\sum_{\ell\in I_\Lambda}\sum_{n<N_\ell}\mathrm{cost}(\ell,n)\bigr]\le c_4\varepsilon^{-2}$ (real power).

Here $I_\Lambda=$ `indexSet (fun _ => 1/2) Λ` $=\{\ell:\ell_d\le\lfloor 2\Lambda\rfloor_+ \text{ for each } d,\ (\ell_1+\ell_2)/2\le\Lambda\}$. That is the total-degree simplex $\{\ell_1+\ell_2\le 2\Lambda\}$ for $\Lambda\ge0$ and $\emptyset$ for $\Lambda<0$; both facts were proved in `Scratch.lean`.

The subtraction of the target sits outside the sum. `∑` parses its body at precedence 67; checked by `rfl` in `Scratch.lean`, and the pretty-printer shows `(⋯ - ⋯) ^ 2`.

$c_4$ comes before $\varepsilon$ and may depend only on the problem data. $\Lambda$ and $N$ depend on $\varepsilon$.

**Assessment.**

*Truth: true.* This is the standard MIMC complexity theorem in the case $\beta_i>\gamma_i$. Proof sketch:
1. **Consecutive weak bound.** The new `hw` gives the consecutive bound with $c_w'=\tfrac32c_w$, so #1 and #2 give $V_\ell\le C_*4^{-|\ell|}$ and $|EY_\ell|\le C'2^{-|\ell|}$.
2. **Telescoping and the limit.**
   - Telescoping gives $\sum_{a\le A,b\le B}EY_{a,b}=E f(\overline{gh_B}_{2^A})$. Shifted blocks have the same law under `infinitePi`; `brute_defs.py` and `rates_fast.py` verified this identity to $10^{-30}$ and $10^{-12}$.
   - As $A\to\infty$ this tends to $E f(E_W gh_B(Z))$, by the SLLN and uniform integrability from fourth moments.
   - As $B\to\infty$ it tends to $E f(G(Z))$ with $G(z)=\int g(z,\cdot)d\rho$, by `hw` and the linear growth of $f'$.
   - Absolute summability ($\sum 2^{-|\ell|}<\infty$) identifies the full sum with the target.
3. **Bias.** The bias of $I_\Lambda$ is $\le C'\sum_{n>\lfloor2\Lambda\rfloor}(n+1)2^{-n}$. Take $2\Lambda\approx\log_2\varepsilon^{-1}+\log_2\log_2\varepsilon^{-1}+O(1)$.
4. **Variance and cost.** Take $N_\ell=\lceil 2\varepsilon^{-2}\sqrt{V_\ell/\bar C_\ell}\,S\rceil$ with $\bar C_\ell=c_3 2^{|\ell|}$ and $S=\sum_{\ell}\sqrt{V_\ell\bar C_\ell}\lesssim\sum_n(n+1)2^{-n/2}<\infty$. Independence gives variance $\le\varepsilon^2/2$. The expected cost is $\sum N_\ell C(\ell)\le 2S^2\varepsilon^{-2}+c_3\sum_{I_\Lambda}2^{|\ell|}$, and the last sum is $O(\varepsilon^{-1}\log^2\varepsilon^{-1})$. So the cost is $O(\varepsilon^{-2})$.

*Numerics* (`rates_fast.py`, $f=\sin$, $Z\in\{-1,0,2\}$, $W$ Rademacher, $gh_\ell=z+w+2^{-\ell}(1+w)$, $g=z+w$).
- The exact simplex bias satisfies $\mathrm{bias}(L)\,2^L/(L+1)\to 0.31$.
- With the allocation above, $\mathrm{MSE}/\varepsilon^2\in[0.56,0.83]$.
- $\mathrm{cost}\cdot\varepsilon^2$ rises from 279 to 367 as $\varepsilon$ goes from $10^{-2}$ to $10^{-4}$. It stays below its limit bound $2S_\infty^2=384$, consistent with $O(\varepsilon^{-2})$.

*Vacuity: not vacuous.* Take the instance of #1 with $g(z,w)=z+w$ ($c_w=1$), $\Omega=(\mathbb N^2\times\mathbb N\to\mathcal Z\times\mathcal W^{\mathbb N})$ with $\mu=$ `infinitePi` of copies of `nestedLaw`, and $\omega=$ the coordinate projections. `Vac.lean` proves `MeasurePreserving` and `iIndepFun` for this choice. Set $\mathrm{cost}\equiv 2^{\ell_1+\ell_2}$ and $c_3=1$.

*Junk values: none that the truth depends on.*
- The MSE integrand is a genuine square-integrable function, so $\mu[\cdot]=0$ cannot happen through non-integrability.
- The cost integral is a finite sum of integrable functions.
- $z\mapsto f(G(z))$ is integrable and a.e.-strongly measurable, since $G$ is a.e. a limit of measurable functions and $|G-E_Wgh_0|\le c_w$.
- The one junk possibility: $\int g(z,v)\rho(dv)=0$ when $g(z,\cdot)$ is not integrable. `hw` then forces $\int gh_\ell(z,\cdot)d\rho\to0$, so the target is still the true limit of what the estimator estimates. The statement stays true, and its meaning is "target $=E_Zf(\lim_\ell E_W gh_\ell)$".

*Unusual or strong hypotheses.*
- `hw` is ess-sup in $z$ (see #1).
- `hc₃` is superfluous.
- The cost random variables are unrelated to the samples and constrained only through their means. Negative costs are allowed but only make the bound easier.
- $N_\ell>0$ is required for every $\ell$, including outside $I_\Lambda$, which is harmless.
- $\varepsilon<e^{-1}$ is harmless.

*Standard result.* The MIMC complexity theorem (Haji-Ali, Nobile & Tempone 2016; Giles, Acta Numerica 2015, §9) with total-degree index set: if $\beta_i>\gamma_i$ in every direction, then MSE $<\varepsilon^2$ at cost $O(\varepsilon^{-2})$. Here $\alpha=(1,1)$, $\beta=(2,2)$, $\gamma=(1,1)$.
