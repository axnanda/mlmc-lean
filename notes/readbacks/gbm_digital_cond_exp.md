# Blind read-back report: packet R38 (GBM digital option, conditional expectation and splitting)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round23/packet_R38_condexp.lean` |
| declarations audited | 24 (7 theorems, 17 definitions: 10 in the packet body, 7 appended from other modules) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round23/work_R38_condexp/` (`Check.lean`/`.out`, `mc_condexp.py`/`.out`, `weak_quad.py`/`.out`) |

**Elaboration check.** `work_R38_condexp/Check.lean` (with `import MlmcLean`) showed:
- every definition in the packet agrees with the library one by `rfl`;
- each packet theorem statement, written out as an `example`, is closed by the library theorem of the same name;
- `^ (2 * m)` is the natural-number power, `^ q` and `ε ^ (-2 : ℝ)` are `Real.rpow`, and `⌈…⌉₊ : ℕ`;
- `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for all seven theorems.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `gbmCondMeanFine` | def | n/a | n/a | n/a |
| 2 | `gbmCondStdFine` | def | n/a | n/a | n/a |
| 3 | `gbmCondMeanCoarse` | def | n/a | n/a | n/a |
| 4 | `gbmCondStdCoarse` | def | n/a | n/a | n/a |
| 5 | `gbmDigitalCondFine` | def | n/a | n/a | n/a (value $\Phi(0)=1/2$ when the std is 0) |
| 6 | `gbmDigitalCondCoarse` | def | n/a | n/a | n/a (same) |
| 7 | `gbmMilEM` | def | n/a | n/a | n/a |
| 8 | `MomentBound` | def | n/a | n/a | n/a (not used by any theorem in the packet) |
| 9 | `gbmDigitalSplitFine` | def | n/a | n/a | n/a ($/0$ when $M=0$) |
| 10 | `gbmDigitalSplitCoarse` | def | n/a | n/a | n/a ($/0$ when $M=0$) |
| 11 | `blockMean` | def | n/a | n/a | n/a |
| 12 | `fineCoarseDiff` | def | n/a | n/a | n/a |
| 13 | `pairAvg` | def | n/a | n/a | n/a |
| 14 | `stdNormalSeq` | def (abbrev) | n/a | n/a | n/a |
| 15 | `emStep` | def | n/a | n/a | n/a |
| 16 | `milsteinPath` | def | n/a | n/a | n/a |
| 17 | `milsteinStep` | def | n/a | n/a | n/a |
| 18 | `gbm_digital_condExp_variance_rate` | theorem | true | no | no |
| 19 | `gbm_digital_cond_moments_match` | theorem | true | no | no (the case $T=0$ is trivially $0\le0$) |
| 20 | `gbm_digital_condExp_weak_rate` | theorem | true | no | no |
| 21 | `gbm_digital_condExp_level_zero` | theorem | true | no | no (an identity; for degenerate parameters both sides are the same junk value) |
| 22 | `gbm_digital_condExp_theorem1` | theorem | true | no | no |
| 23 | `gbm_digital_split_variance_rate` | theorem | true | no | no |
| 24 | `gbm_digital_split_sqrt_rate` | theorem | true | no | no |

## Main points for a human auditor

1. **All seven theorems look true and faithful.** They formalise these results:
   - Giles's (2008, Milstein paper) conditional-expectation treatment of the digital option under GBM;
   - the splitting variant;
   - the MLMC complexity theorem (Giles 2008, *Op. Res.*, Thm 3.1, case $\beta>\gamma$, cost $c_4\varepsilon^{-2}$) applied to the conditional-expectation estimator.
2. **Rates carry a $\delta$-loss.** The statements use $q<3/2$ for the variance and $q<1$ for the weak error. These are the provable $O(h^{3/2-\delta})$ and $O(h^{1-\delta})$ forms (in the style of Giles–Debrabant–Rößler), slightly weaker than the headline $O(h^{3/2})$ and $O(h)$. My Monte Carlo and quadrature runs are consistent with the sharp rates:
   - $E[D^2]/h^{3/2}$ levels off;
   - the weak error falls by a factor of 3.4 to 4.1 per level at $\ell\le2$.
3. **The hypothesis $K\neq0$ in #18, #22, #23, #24 is not needed.** For $K=0$ and $s_0\ne0$, the Milstein factor is $\tfrac12(\sigma\sqrt h z+1)^2+\tfrac12+rh-\tfrac12\sigma^2h>0$ for small $h$, so the paths keep their sign. The level differences are then exponentially small. The hypothesis is a harmless restriction, not an error.
4. **$s_0\neq0$ and $\sigma\neq0$ are the right hypotheses.**
   - Without them the conditional std is identically 0 and both payoffs equal the junk value $\Phi(x/0)=\Phi(0)=1/2$. The variance statements #18 and #23/#24 would then hold trivially ($D\equiv0$).
   - In #20 the hypotheses are necessary: without them the statement is false, because $1/2\ne P(S_T>K)\in\{0,1\}$.
   - With the hypotheses, the junk value $\Phi(0)$ occurs only on the null set $\{\hat S_{n-1}=0\}$, where a Milstein factor (a quadratic in $z$ with leading coefficient $\tfrac12\sigma^2h\neq0$) vanishes.
5. **#21 has no hypotheses.** It is a definitional identity: the level-0 conditional payoff is the constant $\Phi\big((s_0+rs_0T-K)/(|\sigma s_0|\sqrt T)\big)$, plus the facts that a constant is in $L^2$ and has variance 0. For $T\le0$ or $\sigma s_0=0$ the right-hand side is a junk value, but the identity holds literally on both sides. As a consequence, level 0 of the MLMC estimator is deterministic.
6. **#19 has extra or loose hypotheses.**
   - $0<m$ is unnecessary: with $m=0$ both sides are 1 and $C$.
   - $T=0$ is allowed and makes both differences identically 0 (all paths equal $s_0$), so the bound is $0\le C\cdot0$.
   - It has no hypotheses on $r,\sigma,s_0$, which is correct: strong order 1 of Milstein for linear coefficients holds for all parameters.
7. **#22 details.**
   - The cost model is $\sum_\ell N_\ell 2^\ell$: fine steps only, with the coarse path absorbed in the constant.
   - $\varepsilon<e^{-1}$ comes from Giles's theorem.
   - The MSE bound is strict ($<\varepsilon^2$).
   - The samples $x_{(\ell,n)}$ are i.i.d. under `infinitePi` over $\mathbb N\times\mathbb N$.
   - Unbiasedness of the telescoping sum needs $E[P^c_\ell]=E[P^f_\ell]$. This is not stated, but it is true: `pairAvg` gives i.i.d. $N(0,1)$, and the coarse last increment $\sqrt{h_{\ell+1}}(z_{2n-2}+z_{2n-1})\sim N(0,h_\ell)$. I checked it at $\ell=0$ by quadrature to $10^{-10}$.
8. **`MomentBound` is defined but unused.** None of the seven statements uses it.

---

## Notation used below

- $\gamma=N(0,1)$ (`gaussianReal 0 1`), $\Phi=$ `cdf γ` (the standard normal CDF, continuous).
- $h_\ell=T/2^\ell$ (real division, $2^\ell$ a natural-number power) and $n_\ell=2^\ell$.
- For a step $h$ and noise $z=(z_k)$, $\hat S^{(h)}_k(z)$ is `milsteinPath (r·) (σ·) h s₀ z k`.
- $\tilde z=$ `pairAvg z`.
- $D^{\rm cond}_\ell=P^f_{\ell+1}-P^c_\ell$, the conditional-expectation difference.
- Lean conventions that matter here:
  - $x/0=0$;
  - $\sqrt x=0$ for $x<0$;
  - `deriv` of a non-differentiable function is 0 (not triggered here, since $b$ is linear);
  - ℕ-subtraction ($2^\ell-1$ and $2^{\ell+1}-2$ never truncate, because $2^\ell\ge1$ and $2^{\ell+1}\ge2$).

---

## Definitions

### 17. `milsteinStep a b h S dW`
**Rendering.** $S+a(S)h+b(S)\,dW+\tfrac12\,b(S)\,b'(S)\,(dW^2-h)$, where $b'(S)$ is Mathlib's `deriv b S`. This is one Milstein step for $dS=a(S)dt+b(S)dW$.

### 16. `milsteinPath a b h S₀ z k`
**Rendering.**
- $\hat S_0=S_0$ and $\hat S_{i+1}=\text{milsteinStep}(a,b,h,\hat S_i,\sqrt h\,z_i)$, with $\sqrt h=0$ if $h<0$.
- For GBM ($a=rS$, $b=\sigma S$, `deriv b = σ`): $\hat S_{i+1}=\hat S_i\,F_h(z_i)$ with $F_h(z)=1+rh+\sigma\sqrt h z+\tfrac12\sigma^2h(z^2-1)$.
- Step $k$ uses $z_0,\dots,z_{k-1}$.

### 15. `emStep a b h S dW`
**Rendering.** $S+a(S)h+b(S)\,dW$, one Euler–Maruyama step.

### 13. `pairAvg z k`
**Rendering.** $\tilde z_k=(z_{2k}+z_{2k+1})/\sqrt2$. This is the coarse normal built from two fine normals, so the coarse increment is $\sqrt{h_\ell}\tilde z_k=\sqrt{h_{\ell+1}}(z_{2k}+z_{2k+1})$. It is the standard MLMC coupling.

### 14. `stdNormalSeq`
**Rendering.** The product measure $\gamma^{\otimes\mathbb N}$ on $\mathbb R^{\mathbb N}$ (`Measure.infinitePi`), the law of an i.i.d. $N(0,1)$ sequence. It is a probability measure.

### 11. `blockMean f ω i N x`
**Rendering.** $N^{-1}\sum_{n<N}f_i(\omega_{(i,n)}(x))$. When $N=0$ this is $0$ by $0^{-1}=0$; this never matters here because #22 requires $N_\ell>0$.

### 12. `fineCoarseDiff Pf Pc`
**Rendering.** $Y_0=P^f_0$ and $Y_{\ell+1}=P^f_{\ell+1}-P^c_\ell$, the MLMC level corrections.

### 1–4. `gbmCondMeanFine`, `gbmCondStdFine`, `gbmCondMeanCoarse`, `gbmCondStdCoarse` (level $\ell$, noise $z$)
**Rendering.** Let $n=n_\ell$ and $h=h_\ell$.
- Fine mean: $\mu^f_\ell=\hat S^{(h)}_{n-1}(z)\,(1+rh)$.
- Fine std: $s^f_\ell=|\sigma\,\hat S^{(h)}_{n-1}(z)|\sqrt h$.
- These are the conditional mean and std of the EM last step $\hat S_{n-1}+r\hat S_{n-1}h+\sigma\hat S_{n-1}\sqrt h z_{n-1}$, given $z_0,\dots,z_{n-2}$.
- Coarse mean: $\mu^c_\ell=\hat S^{(h)}_{n-1}(\tilde z)(1+rh)+\sigma\hat S^{(h)}_{n-1}(\tilde z)\sqrt{h_{\ell+1}}\,z_{2n-2}$.
- Coarse std: $s^c_\ell=|\sigma\hat S^{(h)}_{n-1}(\tilde z)|\sqrt{h_{\ell+1}}$.
- These are the conditional mean and std of the coarse EM last step with increment $\sqrt{h_{\ell+1}}(z_{2n-2}+z_{2n-1})$, given the fine noise $z_0..z_{2n-2}$.
- The coarse path $\hat S_{n-1}(\tilde z)$ uses $z_0..z_{2n-3}$, and the fine path at level $\ell+1$, $\hat S^{(h_{\ell+1})}_{2n-1}(z)$, uses $z_0..z_{2n-2}$. Both are measurable with respect to the same $\sigma$-algebra, as in Giles's construction.

### 5–6. `gbmDigitalCondFine`, `gbmDigitalCondCoarse`
**Rendering.**
- Fine: $P^f_\ell(z)=\Phi\big((\mu^f_\ell-K)/s^f_\ell\big)$. Coarse: $P^c_\ell(z)=\Phi\big((\mu^c_\ell-K)/s^c_\ell\big)$.
- When the std is positive this equals $P(\mu+s\,Z>K\mid\cdot)$, the conditional probability that the EM final value exceeds $K$.
- When the std is 0 (that is, $\hat S_{n-1}=0$, $\sigma=0$, or $T\le0$), Lean gives $\Phi(0)=1/2$.

### 7. `gbmMilEM`
**Rendering.** $\hat S^{\rm MilEM}_\ell(z)=\hat S_{n-1}(1+rh)+\sigma\hat S_{n-1}\sqrt h\,z_{n-1}$ with $n=n_\ell$, $h=h_\ell$: Milstein for $n-1$ steps followed by one EM step.

### 8. `MomentBound μ f m ρ`
**Rendering.** $\exists C\ge0\ \forall i$: $f_i^{2m}\in L^1(\mu)$ and $\int f_i^{2m}\,d\mu\le C\rho_i$. It is not used by any theorem in the packet.

### 9–10. `gbmDigitalSplitFine`, `gbmDigitalSplitCoarse` (sample count $M$, level $\ell$, $p=(z,w)$)
**Rendering.**
- Fine: $\frac1M\sum_{i<M}\mathbf 1\{\hat S_{n-1}(z)(1+rh_\ell)+\sigma\hat S_{n-1}(z)\sqrt{h_\ell}\,w_i>K\}$.
- Coarse: $\frac1M\sum_{i<M}\mathbf 1\{\hat S_{n-1}(\tilde z)(1+rh_\ell)+\sigma\hat S_{n-1}(\tilde z)(\sqrt{h_{\ell+1}}z_{2n-2}+\sqrt{h_{\ell+1}}w_i)>K\}$.
- When $M=0$, both are $0$ by division by zero.
- These are Monte Carlo approximations of $P^f$ and $P^c$ using $M$ independent last-step normals $w_i$. In the theorems, the fine at level $\ell+1$ and the coarse at level $\ell$ share the same $w_i$.

---

## Theorems

### 18. `gbm_digital_condExp_variance_rate`
**Rendering.** For all real $r,\sigma,s_0,T,K,q$ with $s_0\ne0$, $\sigma\ne0$, $T>0$, $K\ne0$ and $q<3/2$, there is a $C\ge0$ (depending on all of these) such that for every $\ell\in\mathbb N$, with $h=T/2^{\ell+1}$ and $D=P^f_{\ell+1}-P^c_\ell$ under `stdNormalSeq`:
- $D\in L^2$;
- $E[D^2]\le C\,h^{q}$;
- $\operatorname{Var}(D)\le C\,h^q$, where $h^q$ is `rpow` with a positive base.

**Assessment.**
- **Truth: true.**
  - $|D|\le1$ and $D$ is measurable, so $D\in L^2$, and $\operatorname{Var}\le E[D^2]$.
  - Main estimate: by #19, $\mu^f-\mu^c=O(h)$ and $s^f-s^c=O(h)$ in every $L^p$, while $s\asymp\sqrt h$ near the strike. So the arguments of $\Phi$ differ by $O(\sqrt h)(1+|a|)$, and $\Phi'$ is non-negligible only when $\mu$ is within $O(\sqrt h)$ of $K$, which has probability $O(\sqrt h)$ (bounded density near $K\ne0$). This gives $E[D^2]=O(h^{3/2})$, and $O(h^{3/2-\delta})$ once Hölder is used.
  - Levels with large $h$ are finitely many and are absorbed into $C$ because $D^2\le1$. For $q\le0$ the statement is trivial.
  - Monte Carlo (`mc_condexp.out`):
    - $r=.05$, $\sigma=.2$, $T=s_0=K=1$: $E[D^2]/h^{1.5}$ goes 0.0023, 0.0021, 0.0033, 0.0039, 0.0041, 0.0045, 0.0046, 0.0047, levelling off. Successive ratios approach $2^{1.5}=2.83$ (2.69, 2.63, 2.75, 2.75).
    - $\sigma=.5$, $K=1.2$: similar, with the ratio levelling at about 0.025.
- **Vacuity: no.** Example: $r=0.05$, $\sigma=0.2$, $s_0=T=K=1$, $q=1.4$.
- **Junk values: no.**
  - The value $\Phi(0)$ appears only on the null set $\{\hat S=0\}$ (roots of quadratics with leading coefficient $\tfrac12\sigma^2h\ne0$).
  - The hypotheses $s_0,\sigma\ne0$ correctly exclude the degenerate cases where $D\equiv0$ through junk.
  - $K\ne0$ is not needed (see main point 3) but is harmless.
  - The rate is $\delta$-weaker than the $O(h^{3/2})$ headline.
- **Standard result.** Giles (2008), "Improved MLMC convergence using the Milstein scheme": for the digital option with conditional expectation over the last step, $V_\ell=O(h^{3/2})$. The proven form $O(h^{3/2-\delta})$ is in Giles–Debrabant–Rößler.

### 19. `gbm_digital_cond_moments_match`
**Rendering.** For all real $r,\sigma,s_0$, all $T\ge0$ and every natural $m>0$, there is a $C\ge0$ such that for every $\ell$, with $h=T/2^{\ell+1}$ (natural-number power $h^{2m}$):
- $(\mu^f_{\ell+1}-\mu^c_\ell)^{2m}$ is integrable and $E[(\mu^f_{\ell+1}-\mu^c_\ell)^{2m}]\le C h^{2m}$;
- $(s^f_{\ell+1}-s^c_\ell)^{2m}$ is integrable and $E[(s^f_{\ell+1}-s^c_\ell)^{2m}]\le C h^{2m}$.

**Assessment.**
- **Truth: true.** Write $n=n_\ell$ and $h_f=h$, $z=z_{2n-2}$.
  - Means: $\mu^f-\mu^c=(\hat S^f_{2n-2}-\hat S^c_{n-1})(1+2rh_f+\sigma\sqrt{h_f}z)+\hat S^f_{2n-2}\big[r^2h_f^2+r\sigma h_f^{3/2}z+(1+rh_f)\tfrac12\sigma^2h_f(z^2-1)\big]$.
  - The first term is $O(h)$ by strong order 1 of Milstein for scalar GBM (fine/coarse coupling, all moments). The bracket is $O(h)$.
  - Stds: $|s^f-s^c|\le|\sigma|\sqrt{h_f}\,|\hat S^f_{2n-1}-\hat S^c_{n-1}|=\sqrt h\cdot(O(\sqrt h)+O(h))$.
  - Integrability holds because all quantities are bounded by polynomials in Gaussians.
  - For $T=0$: all paths equal $s_0$, both differences are $\equiv0$, and the bound is $0\le C\cdot0$, using $m>0$.
  - Monte Carlo: $E[\Delta\mu^2]/h^2$ is about 0.001 and 0.055, and $E[\Delta s^2]/h^2$ about 0.0018 and 0.088, flat across $\ell=0..7$. $E[\Delta\mu^4]/h^4$ stays bounded, with noise.
- **Vacuity: no.** Example: $T=1$, $m=1$, any $r,\sigma,s_0$.
- **Junk values: no.**
  - $T=0$ is a trivial but genuine case.
  - $hm:0<m$ is unnecessary (with $m=0$ the claim is $1\le C$).
  - There are correctly no hypotheses on $r,\sigma,s_0$.
- **Standard result.** The strong-convergence ingredient (fine/coarse $L^{2m}$ distance of $O(h)$, Milstein strong order 1) behind Giles's conditional-expectation analysis.

### 20. `gbm_digital_condExp_weak_rate`
**Rendering.** For all $r,\sigma,s_0,T$ with $s_0\ne0$, $\sigma\ne0$, $T>0$, any real $K$ and any $q<1$, there is a $C\ge0$ such that for every $\ell$ (including $\ell=0$, with $h=T/2^\ell$):
- (a) $\int P^f_\ell\,d\,\text{stdNormalSeq}=P(\hat S^{\rm MilEM}_\ell>K)$, written as the integral of the indicator of $(K,\infty)$;
- (b) $\big|E[P^f_\ell]-P^\ast\big|\le C h^q$, where $P^\ast=\int\mathbf 1\{s_0e^{(r-\sigma^2/2)T+\sigma\sqrt T w}>K\}\,\gamma(dw)=P(S_T>K)$ for exact GBM.

**Assessment.**
- **Truth: true.**
  - (a) is the tower property. Given $z_0..z_{n-2}$ with $\hat S_{n-1}\ne0$, $\hat S^{\rm MilEM}=\mu+\sigma\hat S_{n-1}\sqrt h z_{n-1}$, which has the conditional law $N(\mu,s^2)$ with $s>0$. Hence $P(\cdot>K\mid\cdot)=1-\Phi((K-\mu)/s)=\Phi((\mu-K)/s)$. The set $\{\hat S_{n-1}=0\}$ is null when $\sigma\ne0$, $T>0$; for $\ell=0$, $\hat S_0=s_0\ne0$.
  - (b) is weak order 1 for a digital payoff of Milstein with a final EM step (the conditional expectation smooths it); bounded differences absorb the finitely many large-$h$ levels.
  - Quadrature (`weak_quad.out`, exact up to Gauss–Hermite error), for $r=.05$, $\sigma=.2$, $s_0=K=T=1$: errors $3.909\times10^{-2}$, $1.067\times10^{-2}$, $3.129\times10^{-3}$ at $\ell=0,1,2$, ratios 3.66 and 3.41.
  - For $\sigma=.5$, $K=1.2$: ratios 4.11 and 3.75.
  - For $s_0<0$ the case mirrors this. For $K$ of the opposite sign the error is 0 to $10^{-14}$.
  - Monte Carlo telescoping is consistent with the quadrature.
- **Vacuity: no.** Example: $r=.05$, $\sigma=.2$, $s_0=T=K=1$, $q=0.9$.
- **Junk values: no.**
  - $s_0\ne0$ and $\sigma\ne0$ are necessary here: otherwise $P^f\equiv1/2$ by junk while $P^\ast\in\{0,1\}$, and the claim fails.
  - $K$ is unrestricted, which is correct.
  - The rate $q<1$ is $\delta$-weaker than $O(h)$.
- **Standard result.** The weak convergence (order 1) of the Milstein/EM discretisation for a digital option: Talay–Tubaro / Bally–Talay type, as used in Giles's MLMC digital example. (a) is the conditional-expectation identity of Giles (2008).

### 21. `gbm_digital_condExp_level_zero`
**Rendering.** For all real $r,\sigma,s_0,K,T$ (no hypotheses):
- (i) for every $z$, $P^f_0(z)=\Phi\big((s_0+rs_0T-K)/(|\sigma s_0|\sqrt T)\big)$;
- (ii) $P^f_0\in L^2(\text{stdNormalSeq})$;
- (iii) $\operatorname{Var}(P^f_0)=0$.

**Assessment.**
- **Truth: true.**
  - At $\ell=0$: $h=T/1=T$ and the path index is $2^0-1=0$, so $\hat S_0=s_0$, $\mu=s_0+rs_0T$ and $s=|\sigma s_0|\sqrt T$. The function is constant.
  - A constant is in $L^2$ of a probability measure and has evariance 0.
- **Vacuity: no.** It holds for every parameter value.
- **Junk values.**
  - For $T\le0$ or $\sigma s_0=0$ the closed form is $\Phi(0)=1/2$ (via $x/0=0$, or $\sqrt T=0$ for $T<0$) and is meaningless as a probability.
  - The statement is an identity between the same expressions, so it does not hold "only because of" junk.
  - It is a bookkeeping lemma: level 0 of the MLMC estimator is deterministic.
- **Standard result.** A trivial observation: with one time step, the conditional expectation over the only step is exact, so the level-0 estimator has zero variance.

### 22. `gbm_digital_condExp_theorem1`
**Rendering.** Assume $s_0\ne0$, $\sigma\ne0$, $T>0$, $K\ne0$. Then there exists $c_4>0$ (depending only on $r,\sigma,s_0,T,K$) such that for every $\varepsilon$ with $0<\varepsilon<e^{-1}$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with $N_\ell>0$ for all $\ell$, such that:
- the squared error $(Y-P^\ast)^2$ is integrable;
- the mean-square error satisfies $E[(Y-P^\ast)^2]<\varepsilon^2$;
- the cost satisfies $\sum_{\ell=0}^{L}N_\ell\,2^\ell\le c_4\,\varepsilon^{-2}$ (`rpow` with exponent $-2$).

Here:
- $Y(x)=\sum_{\ell=0}^{L}\frac1{N_\ell}\sum_{n<N_\ell}Y_\ell(x_{(\ell,n)})$ is the MLMC estimator;
- $Y_0=P^f_0$ and $Y_{\ell+1}=P^f_{\ell+1}-P^c_\ell$;
- $x=(x_{(\ell,n)})_{(\ell,n)\in\mathbb N^2}$ are i.i.d. samples of `stdNormalSeq` (`infinitePi` over $\mathbb N\times\mathbb N$);
- $P^\ast=P(S_T>K)$ as in #20.

**Assessment.**
- **Truth: true.** It is Giles's complexity theorem with:
  - $\alpha$ close to 1, from #20;
  - $\beta\in(1,3/2)$, from #18;
  - $\gamma=1$ (cost $2^\ell$ per sample).
- Unbiasedness of the telescoping sum: $E[Y]=E[P^f_L]$, because $E[P^c_\ell]=E[P^f_\ell]$ (`pairAvg` gives i.i.d. normals, and the coarse last increment is $N(0,h_\ell)$). This was checked numerically at $\ell=0$ to $10^{-10}$.
- Since $\beta>\gamma$, choose $L$ with bias at most $\varepsilon/2$ and $N_\ell\propto\varepsilon^{-2}\sqrt{V_\ell/2^\ell}\sum_k\sqrt{V_k2^k}$, a convergent geometric sum. Then the variance is below $\varepsilon^2/2$ and the cost is $O(\varepsilon^{-2})$. The ceiling overhead $\sum_{\ell\le L}2^\ell=O(\varepsilon^{-1/\alpha})\le O(\varepsilon^{-2})$ because $\alpha\ge1/2$.
- $V_0=0$ by #21.
- Integrability is immediate because $|Y_\ell|\le1$.
- **Vacuity: no.** The same parameter example as above works, and $\varepsilon\in(0,e^{-1})$ is a non-empty range.
- **Junk values: no.** The integral is of an integrable bounded function (integrability is asserted), and $N_\ell>0$ excludes $0^{-1}$.
- **Comments.**
  - $K\ne0$ is not needed.
  - The cost counts only fine steps; the constant absorbs the coarse-path factor $3/2$.
  - $\varepsilon<e^{-1}$ is inherited from the source theorem.
  - The strict MSE bound is fine.
- **Standard result.** Giles, *Multilevel Monte Carlo path simulation* (Oper. Res. 2008), Theorem 3.1, case $\beta>\gamma$ (cost $c_4\varepsilon^{-2}$), applied to the digital option with conditional expectation (Giles 2008, Milstein paper).

### 23. `gbm_digital_split_variance_rate`
**Rendering.** Assume $s_0\ne0$, $\sigma\ne0$, $T>0$, $K\ne0$ and $q<3/2$. There is a $C\ge0$ such that for all $\ell\in\mathbb N$ and all $M\in\mathbb N$ with $M>0$, with $h=T/2^{\ell+1}$ and $D^{\rm split}=\text{SplitFine}(M,\ell+1)-\text{SplitCoarse}(M,\ell)$ under $\gamma^{\otimes\mathbb N}\otimes\gamma^{\otimes\mathbb N}$:
- $D^{\rm split}\in L^2$;
- $E[(D^{\rm split})^2]\le C\big(h^q+h^{q-1/2}/M\big)$;
- $\operatorname{Var}(D^{\rm split})$ satisfies the same bound.

$C$ is uniform in both $\ell$ and $M$.

**Assessment.**
- **Truth: true.**
  - Conditional on $z$, $D^{\rm split}=\frac1M\sum_i\xi_i$ with $\xi_i=\mathbf 1(A_i)-\mathbf 1(B_i)$ i.i.d. and $E[\xi_i\mid z]=D^{\rm cond}(z)$, since fine and coarse share the same $w_i$ and the conditional probabilities are exactly $P^f_{\ell+1}$ and $P^c_\ell$.
  - Hence $E[(D^{\rm split})^2]=E[(D^{\rm cond})^2]+E[\operatorname{Var}(\xi\mid z)]/M\le Ch^{3/2-\delta}+E[\xi^2]/M$.
  - The fine and coarse final values differ by $O(h)$ in $L^p$, and the density near $K$ is bounded, so $E[\xi^2]=P(K\text{ lies between them})=O(h^{1-\delta})=O(h^{q-1/2})$.
  - Monte Carlo: the $M=1$ split $E[D^2]$ roughly halves per level (2.8e-2, 1.26e-2, 7.5e-3, 4.0e-3, 1.8e-3, …).
  - $D\in L^2$ because $|D|\le1$.
- **Vacuity: no.** The same parameter example with $q=1.4$ and $M=1$ works.
- **Junk values: no.** $M>0$ excludes the $/0$ case. $h^{q-1/2}$ with a possibly negative exponent is a legitimate `rpow` with a positive base.
- **Comments.** $K\ne0$ is not needed.
- **Standard result.** The "splitting" variant of the conditional-expectation technique (Giles; Giles–Debrabant–Rößler; Burgos–Giles): replace the analytic conditional expectation by $M$ sub-samples of the last increment, with variance $O(h^{3/2-\delta}+h^{1-\delta}/M)$.

### 24. `gbm_digital_split_sqrt_rate`
**Rendering.** Same hypotheses as #23. There is a $C\ge0$ such that for every $\ell$, with $h=T/2^{\ell+1}$ and $M_\ell=\lceil h^{-1/2}\rceil_{\mathbb N}$:
- (a) $M_\ell>0$;
- (b) $M_\ell\,h\le\sqrt h+h$;
- (c) $D^{\rm split}$ with $M=M_\ell$ is in $L^2$;
- (d) $E[(D^{\rm split})^2]\le Ch^q$;
- (e) $\operatorname{Var}(D^{\rm split})\le Ch^q$.

**Assessment.**
- **Truth: true.**
  - (a): $h^{-1/2}>0$, so its ceiling is at least 1.
  - (b): $\lceil x\rceil<x+1$ and $h^{-1/2}h=h^{1/2}=\sqrt h$ for $h>0$.
  - (d) and (e) follow from #23 with $1/M_\ell\le h^{1/2}$: $h^{q-1/2}/M_\ell\le h^q$, giving $2C$.
  - Monte Carlo with $M=\lceil h^{-1/2}\rceil$: $E[D^2]/h^{1.5}$ is about 0.04–0.07 and 0.09–0.18, bounded.
- **Vacuity: no.**
- **Junk values: no.** Part (b) is the cost statement: the $M_\ell$ extra samples cost at most $h^{-1/2}+1$, which the $O(h^{-1})$ path cost dominates.
- **Comments.** $K\ne0$ is not needed.
- **Standard result.** Splitting with $M_\ell\sim h_\ell^{-1/2}$ recovers the $O(h^{3/2-\delta})$ variance of the analytic conditional expectation at the same order of cost per sample.
