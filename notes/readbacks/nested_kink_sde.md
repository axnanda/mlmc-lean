# Blind read-back report: `packet_R4_kink_sde.lean`

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round13/packet_R4_kink_sde.lean` |
| declarations audited | 9 theorems (in full). The 8 module definitions and instances and the 11 appended definitions are rendered in §0. |
| auditor | independent blind auditor (sub-agent) |
| scripts | `readback/round13/work_R4/` (`mimc_kink.py/.out`, `mlmc_kink.py/.out`, `mimc_table.py/.out`, `lower_bound_check.py/.out`, the helper libraries `kink_common.py` and `mimc_kink_lib.py`, and the Lean elaboration check `Check.lean/.out`) |

I elaborated the statements with `import MlmcLean` and `#check`/`#print` (`Check.lean`, output in `Check.out`). They match the packet verbatim: the same casts, `npow` versus `rpow`, and definitions. `Bool` carries the `⊤` σ-algebra. `#print axioms` on four of the theorems lists only `propext`, `Classical.choice` and `Quot.sound`.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `nested_kink_bias_rate_one` | theorem | true | no | no |
| 2 | `nested_kink_sde_bias_rate` | theorem | true | no | no |
| 3 | `nested_kink_sde_variance_rate` | theorem | true | no | no |
| 4 | `nested_kink_sde_mlmc_complexity` | theorem | true | no | no |
| 5 | `kinkInnerApprox_hypotheses` | theorem | true | n/a (no hypotheses) | no |
| 6 | `kinkInnerApprox_mlmc_rates` | theorem | true | n/a (no hypotheses) | no |
| 7 | `kinkMimc_variance_ge` | theorem | true (exact enumeration: variance is at least 14 times the bound) | no | no |
| 8 | `nested_mimc_kink_rates_false` | theorem | true | no | no |
| 9 | `nested_mimc_kink_three_halves_false` | theorem | true | n/a | no |

## Main points for a human auditor

1. **All 9 statements are true, none is vacuous and none depends on a junk value.** The rate theorems have explicit constants that are uniform in $\ell$. The complexity theorem has the correct quantifier order: $\exists c_4>0\ \forall\varepsilon\in(0,e^{-1})\ \exists L,N$. The MSE and cost integrands are genuinely integrable under the hypotheses, so `μ[…] < ε²` cannot hold through a junk zero. The variances in theorems 7–9 are of bounded measurable functions, so they are genuine. In the "¬∃C" direction a junk zero would only make the refuted bound easier to satisfy.
2. **The example instantiates every hypothesis.** `kinkInnerApprox_hypotheses` gives `hgh`, `hfib` (with equality, $m_4=1/4096$), `hg0`, `hw` (with equality, $c_w=1/8$) and `hball` ($k=1/2$, $c_d=2$). Its last conjunct, $gh_{\ell+1}-gh_\ell\equiv-2^{-\ell}/16$, gives `hs` with $c_s=1/256$, and $f=(x-\tfrac12)^+$ is $a_0=a_1=0$, $c=1$, $k=1/2$. The constants 10 and 14 in `kinkInnerApprox_mlmc_rates` are what theorems 2 and 3 give for these parameters (9.30 and 13.61). The exact values are far smaller: $2^\ell|\text{bias}|\to 9/128\approx0.0703$, and $2^{3\ell/2}E[\Delta_{\ell+1}^2]$ falls from $2.6\cdot10^{-3}$ towards $1/(3072\sqrt\pi)\approx1.84\cdot10^{-4}$.
   - *Caveat:* in this example the inner-discretisation error is deterministic ($gh_\ell-g\equiv2^{-\ell}/8$). It therefore satisfies `hs` with rate $2^{-3\ell/2}$, much better than the assumed $2^{-\ell/2}$. That is enough for non-vacuity, but it does not exercise the strong-error hypothesis at its own rate. A variant with random strong error at exactly rate 1/2, such as $z+s(b)(1/8+2^{-\ell/4}/8)$, also meets all the hypotheses.
3. **Strong but standard hypotheses in theorems 2–4.**
   - The weak error must hold *a.e.-uniformly in $z$*: $2^\ell|E_\rho gh_\ell(z,\cdot)-E_\rho g(z,\cdot)|\le c_w$ for a.e. $z$.
   - The centred conditional 4th moments must be bounded *a.e.-uniformly*.
   - `hball` is a small-ball (bounded density) condition on the exact conditional mean.
   - The strong-error hypothesis `hs` only asks for $E(gh_{\ell+1}-gh_\ell)^2\le c_s2^{-\ell/2}$, which is weaker than Euler–Maruyama's $2^{-\ell}$.
   - $g$ has no measurability or integrability hypothesis: it enters only through $X(z)=\int g(z,v)\,d\rho(v)$. The hypotheses and the conclusions speak about the same $X$, so this does not create a junk loophole.
4. **The MIMC counterexample checks out exactly.** I enumerated the inner coins exactly and integrated over $z$ exactly (piecewise quadratic, Fractions).
   - **Mean:** $E[\text{MIMC correction}]=0$ in every case.
   - **Lower bound:** in `kinkMimc_variance_ge` the ratio Var / $2^{-(2\ell_2+j+17)}$ is exactly 14 at $(j,\ell_2)=(0,1)$ and lies in $[14.0,\,18.04]$ on the whole tested range ($j\le6$). Its limit is about $2^{4.17}$.
   - **Analytic argument:** a short proof gives $\text{Var}\ge2^{-(2\ell_2+j+15.66)}$ for all admissible $(j,\ell_2)$.
   - **Shape:** the variance behaves like $V(\ell_1,\ell_2)\asymp2^{-\ell_1/2}\min(2^{-\ell_1},2^{-2\ell_2})$.
   - **Consequence:** along the ray $(\ell_1,\ell_2)=(2j,j+1)$ the variance is $\ge2^{-(3j+19)}$, so every bound $C2^{-\beta_1\ell_1-\beta_2\ell_2}$ with $2\beta_1+\beta_2>3$ fails.
   - **Sharpness:** the threshold is sharp. Numerically $(1,1)$, $(1/2,2)$ and $(3/2,0)$ (all with $2\beta_1+\beta_2=3$) stay bounded.
   - **MLMC comparison:** the MLMC correction of the same example does decay like $2^{-3\ell/2}$. Its local log2 slopes go $-2.03\to-1.57$ and approach $-1.5$, because the second moment is $A2^{-3\ell/2}+B2^{-2\ell}$.
5. **Small remarks.**
   - `hingeAntithetic` is defined but not used in any packet statement.
   - The refutations deny a *global* bound (for all $\ell_1,\ell_2$), which is the usual form of the MIMC rate assumption. The violating sequence tends to infinity in both indices, so an "eventually" bound is refuted too, although the statement does not say so.

---

## §0 Definitions (rendering only)

- `kinkSign b` $=1$ if $b$ is `true`, else $-1$. `kinkCoin` $=\tfrac12(\delta_{\text{true}}+\delta_{\text{false}})$ is a fair coin on `Bool` (σ-algebra $\top$). `kinkOuter` is Lebesgue measure restricted to $[0,1]\subset\mathbb R$, i.e. $Z\sim U[0,1]$. Both instances state that these are probability measures, which is true.
- `kinkInner z b` $=z+s(b)/8$, the exact inner function; its $\rho$-mean is $z$. `kinkInnerApprox ℓ z b` $=z+s(b)/8+2^{-\ell}/8$, the level-$\ell$ inner approximation with deterministic bias $2^{-\ell}/8$.
- `hingeAntithetic e₁ e₂ x` $=(x+\tfrac{e_1+e_2}2)^+-\tfrac12(x+e_1)^+-\tfrac12(x+e_2)^+$.
- Appended definitions:
  - `nestedLaw ν ρ` $=\nu\otimes\rho^{\otimes\mathbb N}$ (`Measure.infinitePi`).
  - `innerMean g M z w` $=M^{-1}\sum_{m<M}g(z,w_m)$.
  - `shiftSeq M w` $=(w_{M+m})_m$.
  - `nestedP f g ℓ` $=f(\text{mean of }2^\ell\text{ samples})$.
  - `nestedTarget f g ρ (z,w)` $=f(\int g(z,v)\,d\rho)$.
  - `nestedSdeP f gh ℓ` $=f(\text{mean of }gh_\ell\text{ over }2^\ell\text{ samples})$.
  - `nestedSdeDelta f gh 0` $=$ `nestedSdeP f gh 0`, and `nestedSdeDelta f gh (ℓ+1)` $=f(\bar Y^{gh_{\ell+1}}_{2^{\ell+1}})-\tfrac12f(\bar Y^{gh_\ell}_{\text{first }2^\ell})-\tfrac12f(\bar Y^{gh_\ell}_{\text{next }2^\ell})$. This is the antithetic MLMC correction; it refines the sample count and the inner level together.
  - `nestedDelta f g` is the same with $g$ fixed: the antithetic correction in the sample-count direction only.
  - `nestedMimcDelta f gh ℓ₁ 0` $=$ `nestedDelta f (gh 0) ℓ₁`, and `nestedMimcDelta f gh ℓ₁ (ℓ₂+1)` $=$ `nestedDelta f (gh (ℓ₂+1)) ℓ₁` $-$ `nestedDelta f (gh ℓ₂) ℓ₁`. This is the mixed MIMC difference with common inner samples $w$.
  - `blockMean F ω ℓ N x` $=N^{-1}\sum_{n<N}F_\ell(\omega_{(\ell,n)}(x))$.
  - `totalCost cost L N x` $=\sum_{\ell\le L}\sum_{n<N_\ell}\mathrm{cost}_{\ell,n}(x)$.

Notation below: $M=2^\ell$, $X(z)=\int g(z,v)\,d\rho(v)$, $X_\ell(z)=\int gh_\ell(z,v)\,d\rho(v)$, $\bar X$ is a sample mean, $D=\bar X-X$ given $z$, $d(z)=|X(z)-k|$, and $L_f=|a_1|+|c|$ is the Lipschitz constant of $f$.

---

## 1. `nested_kink_bias_rate_one`

**Rendering.**
- **Setting:** $\nu$ and $\rho$ are probability measures; $f(x)=a_0+a_1x+c(x-k)^+$ for all $x$; $g:\mathcal Z\times\mathcal W\to\mathbb R$ is jointly measurable.
- **Moment hypothesis:** for $\nu$-a.e. $z$, $g(z,\cdot)^4\in L^1(\rho)$ and $\int(g(z,v)-X(z))^4\,d\rho\le m_4$.
- **Small ball:** $\nu\{z:|X(z)-k|\le t\}\le\mathrm{ofReal}(c_dt)$ for all real $t>0$.
- **Conclusion:** for every $\ell\in\mathbb N$, $(z,w)\mapsto f(\bar X^{(2^\ell)}(z,w))-f(X(z))$ is integrable for $\nu\otimes\rho^{\mathbb N}$, and $2^\ell\,|E[f(\bar X_{2^\ell})-f(X)]|\le3c_d|c|(1+80m_4)$.
- **Types:** $2^\ell$ is a real `npow`; $m_4,c_d\in\mathbb R$ are universally quantified, not existential.

**Assessment.**
- **Truth: true.** Write $f(\bar X)-f(X)=a_1D+c[(\bar X-k)^+-(X-k)^+]$. Given $z$, $E[D]=0$. If $X>k$, then $(\bar X-k)^+-(X-k)^+-D=(-d-D)^+\le(|D|-d)^+$, and the case $X\le k$ is symmetric. So $0\le\text{bias}(z)\le E[(|D|-d)^+]\le\min\!\big(E|D|,\tfrac{27}{256}E D^4/d^3\big)$.
- **Moment inputs:** $E D^4\le3m_4/M^2$ and $E|D|\le m_4^{1/4}M^{-1/2}$, using $\sigma^4\le\mu_4$.
- **Layer cake:** with $\nu(d<s)\le c_ds$, $\int\min(A,B/d^3)\,d\nu\le\tfrac32c_dB^{1/3}A^{2/3}$. This gives $|\text{bias}|\le\approx1.02\,c_d|c|\sqrt{m_4}/M\le3c_d|c|(1+80m_4)/M$.
- **Integrability:** $|f(\bar X)-f(X)|\le L_f|D|$ and $E[D^2\mid z]\le\sqrt{m_4}/M$ uniformly. Measurability of $X$ follows from joint measurability of $g$.
- **Implicit constraints:** $m_4\ge0$ and $c_d>0$ are forced, because $\nu$ is a probability measure and $\nu\{|X-k|\le t\}\to1$.
- **Vacuity:** not vacuous. Take $\nu=U[0,1]$, $\rho$ a fair coin, $g(z,b)=z\pm1/8$, $k=1/2$, $c_d=2$, $m_4=1/4096$ (this is `kinkInner`).
- **Junk values:** none. Integrability is part of the conclusion, $X$ is a genuine integral for a.e. $z$, and $\nu$-integrability of $X$ is not needed because only differences are integrated.
- **Hypotheses:** standard (uniform conditional moments, bounded density of $X$ near the kink).

**Standard result:** the $O(1/M)$ bias of nested simulation with a piecewise-linear (one-kink) outer function under a bounded-density condition (Gordy–Juneja; Giles–Haji-Ali). Here the inner function $g$ is exact.

## 2. `nested_kink_sde_bias_rate`

**Rendering.**
- **Setting:** as in §1, but with a family $gh_\ell$ of jointly measurable functions. The moment bound holds for each $\ell$, a.e. $z$, with the same $m_4$.
- **New ingredient:** an arbitrary $g$ (no measurability or integrability hypothesis) with a.e.-uniform weak error, $\forall\ell$, for $\nu$-a.e. $z$: $2^\ell|X_\ell(z)-X(z)|\le c_w$.
- **Small ball:** for the exact mean $X$, as in §1.
- **Conclusion:** for every $\ell$, $f(\bar X^{gh_\ell}_{2^\ell})-f(X)$ is integrable, and $2^\ell|E[\cdot]|\le4c_d|c|(1+80m_4)(1+c_w)+(|a_1|+|c|)c_w$.

**Assessment.**
- **Truth: true.** Split into $[f(\bar X_\ell)-f(X_\ell)]+[f(X_\ell)-f(X)]$. The second bracket is at most $L_fc_w2^{-\ell}$.
- **First bracket:** run the argument of §1 with $d_\ell=|X_\ell-k|$. Now $\nu(d_\ell<s)\le c_d(s+c_w2^{-\ell})$, so the layer cake adds $c_d\,c_w2^{-\ell}E|D|$, which is still $O(2^{-\ell})$. The constant has a wide margin.
- **Measurability:** $X$ is an a.e. limit of the measurable $X_\ell$, so the target is a.e.-measurable. The small-ball set may be non-measurable; the hypothesis then bounds its outer measure, which is consistent. $c_w\ge0$ is forced.
- **Vacuity:** not vacuous; the example satisfies every hypothesis (§5).
- **Junk values:** none. If $g(z,\cdot)$ were not integrable, $X(z)=0$ would be a junk value, but the hypotheses and the target both refer to the same $X$, so nothing becomes trivial. Integrability is asserted.
- **Hypotheses:** the a.e.-uniform weak error and uniform 4th moments are strong but reasonable (bounded-coefficient SDE inner paths).

**Standard result:** the nested-MLMC bias bound with an approximate inner sampler, $O(2^{-\ell})$ from the samples plus $O(2^{-\ell})$ from the weak error. Compare Giles–Haji-Ali, *Multilevel nested simulation for efficient risk estimation* (2019).

## 3. `nested_kink_sde_variance_rate`

**Rendering.**
- **Hypotheses:** those of §2, plus strong error: $\forall\ell$, $2^{\ell/2}\int(gh_{\ell+1}-gh_\ell)^2\,d(\nu\otimes\rho)\le c_s$. Here $2^{\ell/2}$ is `rpow`.
- **Conclusion:** for every $\ell$, the antithetic correction $\Delta_{\ell+1}=$`nestedSdeDelta f gh (ℓ+1)` is in $L^2(\nu\otimes\rho^{\mathbb N})$, and $2^{3\ell/2}E[\Delta_{\ell+1}^2]\le6c_dc^2(1+16m_4)(1+c_w)+\tfrac32(|a_1|+|c|)^2(\tfrac94c_w^2+c_s)$.
- **Note:** the bound is on the second moment, which is at least the variance.

**Assessment.**
- **Decomposition:** $\Delta=T_1+cH$ with $T_1=f(\bar Y^{gh_{\ell+1}}_{2M})-f(\bar Y^{gh_\ell}_{2M})$ and $H=(\bar Y'-k)^+-\tfrac12(\bar Y_a-k)^+-\tfrac12(\bar Y_b-k)^+$. The linear part of $f$ cancels in $H$.
- **First term:** $E[T_1^2]\le L_f^2\big(E(\delta g)^2/(2M)+\tfrac94c_w^2M^{-2}\big)$.
- **Second term:** $|H|\le\tfrac12\max_i(|D_i|-d_\ell)^+$, so $E[H^2\mid z]\le\tfrac12\min(\sqrt{m_4}/M,\;3m_4/(16M^2d_\ell^2))$. The layer cake with the shifted small ball gives $E H^2\le\tfrac12c_d(\tfrac{\sqrt3}{2}m_4^{3/4}M^{-3/2}+c_w\sqrt{m_4}M^{-2})$.
- **Combination:** with $(x+y)^2\le3y^2+\tfrac32x^2$ the stated bound follows, with room to spare. The form $\tfrac32(\ldots)^2(\tfrac94c_w^2+c_s)$ matches this split exactly. **True.**
- **No junk-zero loophole in `hs`:** `hs` integrates over $\nu\otimes\rho$ and would be trivially true if $(gh_{\ell+1}-gh_\ell)^2$ were not integrable. But integrability follows from `hfib` and `hw`: the conditional mean is at most $\tfrac32c_w2^{-\ell}$ and the centred 4th moment is at most $16m_4$. So `hs` is a genuine constraint.
- **Vacuity and junk values:** not vacuous, as the example shows. No junk: MemLp is asserted.
- **Hypotheses:** `hs` asks only for strong rate 1/2 in mean square, which is weak and makes the theorem stronger.

**Standard result:** the antithetic nested-MLMC variance $O(M^{-3/2})$ for a kink payoff (Giles–Haji-Ali, β = 3/2), combined with the inner discretisation.

## 4. `nested_kink_sde_mlmc_complexity`

**Rendering.**
- **Problem hypotheses:** those of §3, plus `hg0`: $gh_0^2\in L^1(\nu\otimes\rho)$.
- **Sampling hypotheses:** a probability space $(\Omega,\mu)$ and $\omega:\mathbb N\times\mathbb N\to\Omega\to\mathcal Z\times\mathcal W^{\mathbb N}$, each $\omega_p$ measure-preserving onto $\nu\otimes\rho^{\mathbb N}$, with the family `iIndepFun`.
- **Cost hypotheses:** costs $\mathrm{cost}_{\ell,n}\in L^1(\mu)$ with $E[\mathrm{cost}_{\ell,n}]=C_\ell\le c_3\,4^\ell$, where $c_3>0$.
- **Conclusion (order):** there is $c_4>0$, depending on all of the data but not on $\varepsilon$, such that for every real $\varepsilon\in(0,e^{-1})$ there are $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with all $N_\ell>0$, satisfying the two bounds below.
- **MSE bound:** $E_\mu\big[(\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}\Delta_\ell(\omega_{\ell,n})-\int f(X)\,d\nu)^2\big]<\varepsilon^2$.
- **Cost bound:** $E_\mu[\text{total cost}]\le c_4\varepsilon^{-5/2}$, with `rpow`.

**Assessment.**
- **Truth: true.** Apply the MLMC complexity theorem with $\alpha=1$ (§2), $\beta=3/2$ (§3) and $\gamma=2$. Since $\beta<\gamma$, this gives cost $\varepsilon^{-2-(\gamma-\beta)/\alpha}=\varepsilon^{-5/2}$.
- **Ingredients:** $E\sum_{\ell\le L}\Delta_\ell=E f(\bar X^{gh_L}_{2^L})$ by telescoping, because the antithetic halves have the law of $P_\ell$. $\Delta_0=f(gh_0(z,w_0))\in L^2$ by `hg0` and linear growth of $f$. $\Delta_{\ell\ge1}\in L^2$ by §3. Levels and samples are independent.
- **Choice of $N$:** $N_\ell\propto\varepsilon^{-2}2^{-7\ell/4}\sum_{k\le L}2^{k/4}$ gives cost $O(\varepsilon^{-2}(\sum2^{k/4})^2+4^L)=O(\varepsilon^{-5/2})$.
- **Quantifier order:** correct; the constant comes before $\varepsilon$. The restriction $\varepsilon<e^{-1}$ is harmless.
- **No junk zero, MSE:** non-integrability would give $0<\varepsilon^2$ trivially, but the integrand is a square of an $L^2$ function, hence integrable.
- **No junk zero, target:** $\int f(X)\,d\nu$ is genuine because $X\in L^2(\nu)$, from `hg0`, Jensen and $|X-X_0|\le c_w$ a.e.
- **Cost model:** costs may be negative, which only weakens the hypothesis on the data and does not trivialise the conclusion.
- **Vacuity:** not vacuous. Take the example of §5 with i.i.d. $\omega$ on an infinite product space and, say, $\mathrm{cost}_{\ell,n}\equiv4^\ell$.

**Standard result:** the MLMC complexity theorem (Giles 2008/2015; Cliffe–Giles–Scheichl–Teckentrup 2011) in the case $\beta<\gamma$, applied to nested simulation with an SDE inner sampler.

## 5. `kinkInnerApprox_hypotheses`

**Rendering.** A conjunction of six facts.
1. Each $(z,b)\mapsto gh_\ell(z,b)=z+s(b)/8+2^{-\ell}/8$ is measurable.
2. For all $\ell$ and all real $z$: $gh_\ell(z,\cdot)^4\in L^1(\text{coin})$, and the centred 4th moment equals $1/4096$.
3. $gh_0^2\in L^1(\text{kinkOuter}\otimes\text{coin})$.
4. For all $\ell,z$: $2^\ell|E\,gh_\ell(z,\cdot)-E\,g(z,\cdot)|=1/8$.
5. For all $t>0$: $\text{Leb}([0,1]\cap\{|z-1/2|\le t\})\le\mathrm{ofReal}(2t)$.
6. For all $\ell,z,b$: $gh_{\ell+1}(z,b)-gh_\ell(z,b)=-2^{-\ell}/16$.

**Assessment.** Each conjunct is checked directly.
- **Facts 1–3:** true. The mean is $z+2^{-\ell}/8$ and the deviations are $\pm1/8$, so the centred 4th moment is $8^{-4}$. Integrability holds because the functions are bounded on $[0,1]\times$`Bool`.
- **Facts 4–6:** true. Fact 4 is $2^\ell\cdot2^{-\ell}/8$; fact 5 is $\min(2t,1)\le2t$; fact 6 is elementary.

**Instantiation:** these give every hypothesis of §§2–4 with $m_4=1/4096$, $c_w=1/8$, $c_d=2$, $k=1/2$, and $c_s=1/256$ (from fact 6: $2^{\ell/2}2^{-2\ell}/256\le1/256$).

**Junk values:** none, everything is a concrete computation. Fact 4 has $2^\ell\cdot\text{bias}$ *equal* to $1/8$, so the weak rate is exact. **Caveat:** fact 6 makes the strong error deterministic (see main point 2).

## 6. `kinkInnerApprox_mlmc_rates`

**Rendering.** For every $\ell$, with $f=(x-\tfrac12)^+$, outer $U[0,1]$, a fair inner coin, `kinkInnerApprox` and `kinkInner`, two bounds hold:
- $2^\ell\,|E[f(\bar X^{gh_\ell}_{2^\ell})-f(X)]|\le10$;
- $2^{3\ell/2}E[\Delta_{\ell+1}^2]\le14$.

**Assessment.**
- **Truth: true.** Instantiating §2 gives $8\cdot(1+80/4096)\cdot\tfrac98+\tfrac18\approx9.30\le10$. Instantiating §3 gives $12(1+16/4096)\tfrac98+\tfrac32(\tfrac9{256}+\tfrac1{256})\approx13.61\le14$.
- **Exact computation (`mlmc_kink.out`):** for $\ell=0..14$, $2^\ell|\text{bias}|=5/64\approx0.0781,\ 19/256\approx0.0742,\ \dots\to9/128\approx0.0703$.
- **Exact second moment:** $2^{3\ell/2}E[\Delta^2_{\ell+1}]=2.58\cdot10^{-3}$ at $\ell=0$, decreasing to $2.08\cdot10^{-4}$ at $\ell=13$. The predicted limit is $1/(3072\sqrt\pi)=1.837\cdot10^{-4}$, from the antithetic tent term $E r^3/6$.
- **Decay:** the local log2 slopes are $-2.03,-1.97,\dots,-1.57$, tending to $-1.5$. **The MLMC correction decays like $2^{-3\ell/2}$.**
- **Junk values:** none; the integrands are bounded and measurable.

## 7. `kinkMimc_variance_ge`

**Rendering.** For natural numbers $j,\ell_2$ with $j+1\le\ell_2$, let $Y=$`nestedMimcDelta f kinkInnerApprox (2j+1) (ℓ₂+1)` under $U[0,1]\otimes\text{coin}^{\mathbb N}$. This is the mixed difference: 
$$Y=\big[\text{antithetic }2^{2j+1}\text{-sample correction with }gh_{\ell_2+1}\big]-\big[\text{the same with }gh_{\ell_2}\big],$$
with common inner coins. The claims are:
- $\int Y=0$;
- $2^{-(2\ell_2+j+17)}\le\mathrm{Var}(Y)$, where `Var` is Mathlib's `variance` $=(\text{evariance}).\text{toReal}$.

**Assessment.**
- **Reduction:** with $x=z-\tfrac12$, half-sample means $a=S_a/(8n)$ and $b=S_b/(8n)$ ($n=4^j$), and $e_\ell=2^{-\ell}/8$, one has $Y=H(x+e_{\ell_2+1})-H(x+e_{\ell_2})$ with $H=$`hingeAntithetic a b`. $H$ is a negative tent of half-width $r=|a-b|/2$ and depth $r/2$, supported inside $[-1/8,1/8]$.
- **Mean zero:** the shifts are at most $1/8$, so both translates lie inside $x\in[-1/2,1/2]$ and $\int Y\,dz=0$ for every coin outcome.
- **Variance closed form:** $\mathrm{Var}=E\,F(r,\delta)$ with $\delta=2^{-\ell_2}/16$. Here $F=(2r\delta^2-\delta^3)/4$ for $\delta\le r$, $(\tfrac43r^3-\tfrac13(2r-\delta)^3)/4$ for $r\le\delta\le2r$, and $r^3/3$ for $\delta\ge2r$.
- **Analytic lower bound:** $\mathrm{Var}\ge\frac{\delta^2}{32n}(E|D|-2^{j-2})$ with $D=K_a-K_b$. Using $E|D|\ge(ED^2)^{3/2}/(ED^4)^{1/2}\ge\sqrt{n/6}$, this gives $\mathrm{Var}\ge(1/\sqrt6-1/4)2^{-(2\ell_2+j+13)}=2^{-(2\ell_2+j+15.66)}$, valid for all $\ell_2\ge j+1$ (`lower_bound_check.out`).
- **Truth: true.**
- **Exact check, three ways (`mimc_kink.out`):**
  - (A) brute force over all coin sequences using a faithful transcription of `innerMean`, `shiftSeq`, `nestedDelta` and `nestedMimcDelta`, for $\ell_1\le3$ and for $(\ell_1,\ell_2')=(4,2)$ with $2^{16}$ sequences;
  - (B) binomial enumeration over $(K_a,K_b)$;
  - (C) the closed form.
  
  All three agree exactly; for example $\mathrm{Var}=7/262144$ at $(j,\ell_2)=(0,1)$, which is exactly 14 times $2^{-19}$. $E[Y]=0$ exactly in every case.
- **Ratio Var/bound:** between 14.0 and 18.04 for $j\le6$ and a range of $\ell_2\ge j+1$; $\log_2\mathrm{Var}+2\ell_2+j\to-12.83$.
- **Junk values:** none; $Y$ is bounded and measurable, so the variance is genuine.
- **Hypothesis $j+1\le\ell_2$:** necessary. For $\ell_2\ll j$, $\mathrm{Var}\approx2^{-3\ell_1/2}$, which is below the stated bound.

## 8. `nested_mimc_kink_rates_false`

**Rendering.** For real $\beta_1,\beta_2$ with $2\beta_1+\beta_2>3$, there is no real $C$ such that for all $\ell_1,\ell_2\in\mathbb N$, $\mathrm{Var}[\text{nestedMimcDelta}(\ell_1+1,\ell_2+1)]\le C\,2^{-(\beta_1\ell_1+\beta_2\ell_2)}$ (`rpow`, with $\ell_i$ cast to $\mathbb R$).

**Assessment.**
- **Truth: true.** Put $(\ell_1,\ell_2)=(2j,j+1)$ and apply §7 with its $\ell_2:=j+1$. Then $2^{-(3j+19)}\le C\,2^{-((2\beta_1+\beta_2)j+\beta_2)}$ for all $j$, which forces $C\ge2^{(2\beta_1+\beta_2-3)j+\beta_2-19}\to\infty$. A negative $C$ is excluded because $\mathrm{Var}>0$.
- **Numerical confirmation (`mimc_table.out`):**
  - On the grid $\ell_1\le14$, $\ell_2\le12$, $V(\ell_1,\ell_2)\asymp2^{-\ell_1/2}\min(2^{-\ell_1},2^{-2\ell_2})$; the normalised log2 values lie in $[-13.5,-11.4]$.
  - $V\cdot2^{1.5\ell_1+1.5\ell_2}$ along the ray grows by a factor of about $2^{1.5}$ per step, from $7.6\cdot10^{-5}$ to $4.0\cdot10^{-2}$.
  - For $(\beta_1,\beta_2)=(1,1)$, $(1/2,2)$ and $(3/2,0)$ (all with $2\beta_1+\beta_2=3$) the scaled values stay bounded, so the threshold is sharp: under this shape the admissible rates are exactly $\{2\beta_1+\beta_2\le3,\ \beta_1\le3/2,\ \beta_2\le2\}$.
- **Vacuity:** the hypothesis is satisfiable, e.g. $\beta=(1.5,1.5)$.
- **Junk values:** none. A junk-zero variance would only make the refuted bound easier.
- **Form of the statement:** it negates the *global* bound. That is the natural MIMC "rate assumption" form, and it is refuted along a sequence that tends to infinity in both indices.

**Standard fact:** the MIMC mixed-difference variance rate fails for nested simulation with a kink. The variance is $2^{-\ell_1/2-2\ell_2}$ on the ridge $\ell_2\approx\ell_1/2$, not a product of the one-dimensional rates.

## 9. `nested_mimc_kink_three_halves_false`

**Rendering.** There is no $C$ with $\mathrm{Var}[\text{nestedMimcDelta}(\ell_1+1,\ell_2+1)]\le C\,2^{-(\frac32\ell_1+\frac32\ell_2)}$ for all $\ell_1,\ell_2$.

**Assessment.**
- **Truth: true.** It is the special case $\beta_1=\beta_2=3/2$ of §8, since $2\cdot\tfrac32+\tfrac32=4.5>3$.
- **Numerical confirmation:** the ratio along $(2j,j+1)$ grows like $2^{1.5j}$ (`mimc_table.out`).
- **Junk values:** none.
