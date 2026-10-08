# Blind read-back report: R47 levyextras

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round25/packet_R47_levyextras.lean` |
| declarations audited | 25 (20 theorems + 5 definitions: `levySmallStd`, `levyGaussFine`, `bandGaussApprox`, `vgLaw`, `vgSubLaw`) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round25/work_R47_levyextras/` (`check_cp_moments.py`, `check_bands.py`, `check_stable.py`, `check_vg.py`, `check_asian.py`, each with a `.out` file; `Scratch.lean`/`Scratch.out` is a sorry'd copy of the packet that compiles cleanly against `import MlmcLean`; `Inst.lean`/`Inst.out` is an instance probe) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `levyGauss_coarse_map_eq` | theorem | true | no | no |
| 2 | `levyGauss_2_4` | theorem | true | no | no |
| 3 | `levyGauss_correction_moments` | theorem | true | no | no |
| 4 | `levyGauss_correction_variance_le` | theorem | true | no | no |
| 5 | `bandGauss_sq_sub` | theorem | true | no | no |
| 6 | `levyGauss_limit` | theorem | true | no | no |
| 7 | `levyGauss_expected_cost` | theorem | true | no | no |
| 8 | `levyGauss_theorem1` | theorem | true | no | no |
| 9 | `levyGauss_stableLike_theorem1` | theorem | true | no | no |
| 10 | `measure_eq_of_integral_exp_eq` | theorem | true | no | no (a hypothesis leans on the convention, see below) |
| 11 | `gammaMeasure_conv` | theorem | true | no | no |
| 12 | `vgLaw_conv` | theorem | true | no | no |
| 13 | `integral_exp_mul_vgLaw` | theorem | true | no | no |
| 14 | `vg_asian_theorem1` | theorem | true | no | no |
| 15 | `vg_asian_variance_le` | theorem | true | no | no |
| 16 | `integral_exp_mul_vgSubLaw` | theorem | true | no | no |
| 17 | `vgSubLaw_conv` | theorem | true | no | no |
| 18 | `vgSubLaw_eq_vgLaw` | theorem | true | no | no |
| 19 | `vgSub_asian_theorem1` | theorem | true | no | no |
| 20 | `vgSub_asian_variance_le` | theorem | true | no | no |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement was found.** Exact computations and Monte Carlo runs agree with every closed-form constant (scripts listed above).
2. **The Gaussian correction does not improve the rates (#6, #8, #9).** The Gaussian variable $G$ is independent of the jumps, and the same $G$ is shared by the fine and coarse levels. As a result:
   - $E(X-\text{bandGauss}_\ell)^2 = 2T\int_{|z|<\delta_\ell}z^2\,d\nu$, which is twice the error without the correction.
   - The rates $\alpha=(2-Y)/2$, $\beta=2-Y$, $\gamma=Y$ are those of the plain truncation scheme.
   - The cost is therefore $\varepsilon^{-\max(2,\,2Y/(2-Y))}$, with an extra $\log^2\varepsilon$ factor at $Y=1$.

   The statements are true, but they do not show the extra benefit of a Gaussian-corrected scheme that is coupled to the jumps (Dereich 2011). They also treat only the terminal value $\Phi(X_T)$ of a pure-jump Lévy variable, not an SDE driven by a Lévy process.
3. **`Measure.infinitePi` in this Mathlib (`if h : ∀ i, IsProbabilityMeasure (μ i) then … else 0`) is the zero measure when some factor is not a probability measure.** No `IsProbabilityMeasure` instance exists for `vgLaw`/`vgSubLaw` (checked in `Inst.out`), so #14, #15, #19 and #20 elaborate without one. If any factor were not a probability measure, the MSE, variance and integrability claims would be trivially true (all integrals would be 0). Under the stated hypotheses every factor is a probability measure: $C,G,M,T>0$ in #14/#15 and $\kappa,T>0$ in #19/#20 make all Gamma shapes and rates positive. So these statements are not junk, but $T>0$, $C>0$ and $\kappa>0$ are what keep them meaningful.
4. **#10 assumes integrability of $e^{tx}$ only under $\mu_1$.** Integrability under $\mu_2$ follows from the convention that a non-integrable function has integral 0: $\int e^{tx}\,d\mu_1>0$, so $\int e^{tx}\,d\mu_2$ cannot be the junk 0. The statement is therefore equivalent to the standard moment-generating-function uniqueness theorem. This is not a defect.
5. **In #8, the hypothesis `hlarge` ($\int_{|z|\ge1}z^2\,d\nu<\infty$) is genuinely needed** for level 0 to have finite variance and for $\Phi(X)$ to be integrable. The real constants $a$ and $b$ are forced to be $\ge0$ by `hsmall`/`hcount`. $X$ is not stated to be measurable, but the `Integrable`/`MemLp` conclusions force a.e. measurability. Clause (i) pins $X$ down a.e. as the $L^2$ limit of `bandApprox ℓ`, so the target $E\Phi(X)$ is meaningful. Likewise, in #14/#19, $P$ is pinned down as the limit of the level means.
6. **#1–#3 and #7 have no positivity hypothesis on $\delta$.** If $\delta\le0$, then `levySet δ` $=\mathbb R$ and the hypothesis `h` forces $T=0$ or $\nu$ finite, and the claims stay correct. In #3, `hδ1 : δ' ≤ 1` is genuinely needed for the compensators to telescope.
7. **The Variance-Gamma Asian MLMC rates were checked by exact second-moment formulas** for the trapezoidal average of $e^{X}$, using $E e^{uX_t}=e^{t\psi(u)}$:
   - $E D_\ell^2/h^2$ converges, so $\beta=2$.
   - $n\sqrt{E(A_n-I)^2}$ converges, so the strong $L^2$ error, and hence the Lipschitz weak error, is $O(2^{-\ell})$, i.e. $\alpha=1$.
   - The cost is $2^\ell$, so $\gamma=1$.

   This gives a cost of order $\varepsilon^{-2}$. The conditions $M>2$ and $2\theta\kappa+2\sigma^2\kappa<1$ are exactly the conditions for $E e^{2X_t}<\infty$.

---

## Definitions

**`levySmallStd ν T δ`** $=\sqrt{T\int_{\{|z|<\delta\}}z^2\,\nu(dz)}$. This is the standard deviation at time $T$ of the small jumps (those with $|z|<\delta$). Both conventions apply here: `Real.sqrt` of a negative number is 0, and the Bochner integral of a non-integrable function is 0.

**`levyGaussFine ν T δ ω`**, with $\omega=((N,(Z_i)_i),g)$, is
$$\sum_{i<N}Z_i\,1_{|Z_i|\ge\delta}-T\int_{\delta\le|z|<1}z\,d\nu+s(\delta)\,g,$$
where $s(\delta)$ is `levySmallStd ν T δ`. This is the compound-Poisson part with jumps of size at least $\delta$, compensated with the truncation function $1_{|z|<1}$, plus a Gaussian term for the small jumps.

**`bandGaussApprox ν T δ ℓ ω`**, with $\omega=((\omega_k)_k,g)$, is
$$\sum_{k\le\ell}\sum_{i<N_k}Z^k_i\,1_{\text{band}_k}(Z^k_i)-T\int_{\delta_\ell\le|z|<1}z\,d\nu+s(\delta_\ell)\,g,$$
where $\text{band}_0=\{|z|\ge\delta_0\}$ and $\text{band}_{k+1}=\{\delta_{k+1}\le|z|<\delta_k\}$.

**`vgLaw b C G M h`** $=\delta_{bh}*\Gamma(Ch,\text{rate }M)*(-\Gamma(Ch,\text{rate }G))$. This is the law of $bh+\Gamma_1-\Gamma_2$, the Variance-Gamma increment in CGM form (CGMY with $Y=0$). The `∗` operator is `infixr`, so the expression elaborates exactly as parenthesised. Mathlib's `gammaMeasure a r` has shape $a$ and rate $r$.

**`vgSubLaw b θ σ κ h`** $=\delta_{bh}*\mathcal L(\theta V+\sigma\sqrt V Z)$, where $V\sim\Gamma(h/\kappa,\text{rate }1/\kappa)$ (mean $h$, variance $\kappa h$) and $Z\sim N(0,1)$ are independent. This is the Madan–Carr–Chang Brownian motion subordinated by a Gamma process. On the null set $V<0$, $\sqrt V$ takes the junk value 0, which does not matter.

---

## 1. `levyGauss_coarse_map_eq`

**Rendering.** Let $\nu$ be any measure on $\mathbb R$, $T\in\mathbb R_{\ge0}$, $\delta\le\delta'$, and $r,r'\in\mathbb R_{\ge0}$. Let $\mu,\mu'$ be probability measures with $r\mu=T\,\nu|_{\{|z|\ge\delta\}}$ and $r'\mu'=T\,\nu|_{\{|z|\ge\delta'\}}$. Then the push-forward of $(\mathrm{Poi}(r)\otimes\mu^{\otimes\mathbb N})\otimes N(0,1)$ under `levyGaussFine ν T δ'` equals the push-forward of $(\mathrm{Poi}(r')\otimes\mu'^{\otimes\mathbb N})\otimes N(0,1)$ under the same map.

**Assessment.**
- **Truth: true.** $\sum_{i<N}f(Z_i)$, with $N\sim\mathrm{Poi}(r)$ and $Z_i\sim\mu$ i.i.d., is compound Poisson with Lévy measure $(r\mu)\circ f^{-1}$ off $0$. Take $f=1_{\{|z|\ge\delta'\}}\,\mathrm{id}$. Since $\{|z|\ge\delta'\}\subseteq\{|z|\ge\delta\}$, both inputs give Lévy measure $T\nu|_{\{|z|\ge\delta'\}}$ off $0$. Mass at $0$ is irrelevant, and the case $r'=0$ works too. The compensator and the Gaussian term are the same on both sides.
- **Numerics.** The characteristic functions agree exactly for a discrete $\nu$ (`check_cp_moments.out`).
- **Junk.** The map is measurable, so no junk `map = 0` arises.
- **Vacuity: not vacuous.** For example, $\nu=$ Lebesgue measure on $(0,1)$, $\delta=0.1$, $\delta'=0.5$, $r=0.9$, $\mu=U[0.1,1)$, $r'=0.5$, $\mu'=U[0.5,1)$.
- **Hypotheses.** $\delta\le\delta'$ is necessary.
- **Standard result.** Thinning/restriction of a Poisson random measure. This is the consistency (coupling) condition in Gaussian-corrected Lévy MLMC (Dereich 2011).

## 2. `levyGauss_2_4`

**Rendering.** Same hypotheses as #1, and $\Phi$ measurable. Then
$$\int\Phi(\text{levyGaussFine}_{\delta'})\,d(P_{r,\mu}\otimes N)=\int\Phi(\text{levyGaussFine}_{\delta'})\,d(P_{r',\mu'}\otimes N).$$

**Assessment.**
- **Truth: true.** It follows from #1 by change of variables. Equal laws make the two sides simultaneously integrable or simultaneously non-integrable, and in the second case both are 0 consistently.
- **Junk.** Not junk-dependent.
- **Vacuity: not vacuous.** Use the instance from #1 with $\Phi=\mathrm{id}$.
- **Standard result.** The integral form of the coupling identity (presumably eq. (2.4) of the source paper).

## 3. `levyGauss_correction_moments`

**Rendering.** Assume:
- $\int\min(1,z^2)\,d\nu<\infty$;
- $\delta\le\delta'\le1$;
- $r\mu=T\nu|_{\{|z|\ge\delta\}}$, with $\mu$ a probability measure.

Write $P=\mathrm{Poi}(r)\otimes\mu^{\otimes\mathbb N}\otimes N(0,1)$ and $D=\text{levyGaussFine}_\delta-\text{levyGaussFine}_{\delta'}$. Then:
- (a) $D\in L^2(P)$;
- (b) $E D=0$;
- (c) $E D^2=T\int_{\delta\le|z|<\delta'}z^2\,d\nu+(s(\delta')-s(\delta))^2$;
- (d) $E D^2\le 2T\int_{\delta\le|z|<\delta'}z^2\,d\nu$.

**Assessment.**
- **Truth: true.**
  - We have $D=\sum_{i<N}g(Z_i)-T\int g\,d\nu+(s(\delta)-s(\delta'))G$, where $g=z1_{\{\delta\le|z|<\delta'\}}$. The compensators telescope because $\delta\le\delta'\le1$.
  - Campbell's formula gives mean $0$ and variance $r\int g^2\,d\mu=T\int_{\text{mid}}z^2\,d\nu$. The Gaussian term is independent, which gives (c).
  - For (d), use $(a-b)^2\le a^2-b^2$ for $a\ge b\ge0$, together with $s(\delta')^2-s(\delta)^2=T\int_{\text{mid}}z^2\,d\nu$. All integrals are genuine, since $z^2$ is integrable on $\{|z|<1\}$.
- **Edge cases.** When $\delta\le0$, the hypothesis forces $T=0$ or $\nu$ finite, and the claims still hold.
- **Numerics.** Monte Carlo gives $E D^2=0.46405$ against the formula $0.46376$ (`check_cp_moments.out`).
- **Vacuity: not vacuous.** For example, $\nu=$ Lebesgue measure on $(0,1)$, $\delta=0.1$, $\delta'=0.5$.
- **Hypotheses.** $\delta'\le1$ is needed; without it the compensators would not telescope.
- **Standard result.** The Lévy–Itô isometry for a compensated compound Poisson process, with an added Gaussian.

## 4. `levyGauss_correction_variance_le`

**Rendering.** Same hypotheses as #3, and $\Phi$ $K$-Lipschitz ($K\in\mathbb R_{\ge0}$). Then $\Phi(F_\delta)-\Phi(F_{\delta'})\in L^2(P)$, and its variance is at most $2K^2\,T\int_{\delta\le|z|<\delta'}z^2\,d\nu$.

**Assessment.**
- **Truth: true.** $\mathrm{Var}\le E(\cdot)^2\le K^2E D^2$, and #3(d) bounds $E D^2$. Mathlib's `variance` is a genuine value here because the $L^2$ membership is asserted.
- **Vacuity: not vacuous.**
- **Standard result.** The standard MLMC level-variance bound for Lipschitz payoffs.

## 5. `bandGauss_sq_sub`

**Rendering.** Assume:
- $\int\min(1,z^2)\,d\nu<\infty$;
- $\delta_k>0$, $\delta$ antitone, $\delta_0\le1$;
- $\Lambda_kM_k=T\nu|_{\text{band}_k}$ for all $k$;
- $\ell\le\ell'$.

Write $D=\text{bandGauss}_{\ell'}-\text{bandGauss}_\ell$ under $\bigotimes_k(\mathrm{Poi}(\Lambda_k)\otimes M_k^{\otimes\mathbb N})\otimes N(0,1)$. Then $D\in L^2$, and
$$E D^2=T\int_{\delta_{\ell'}\le|z|<\delta_\ell}z^2\,d\nu+(s(\delta_\ell)-s(\delta_{\ell'}))^2\le2T\int_{\delta_{\ell'}\le|z|<\delta_\ell}z^2\,d\nu.$$

**Assessment.**
- **Truth: true.** This is the same computation as #3, applied to the independent bands $\ell+1,\dots,\ell'$.
- **Numerics.** Monte Carlo gives $0.39704$ against the formula $0.39763$ (`check_bands.out`).
- **Vacuity: not vacuous.** Take $\delta_k=2^{-k}$ and the stable-like $\nu$ from #9.
- **Standard result.** The level-difference moment for the band (dyadic truncation) coupling.

## 6. `levyGauss_limit`

**Rendering.** Same hypotheses as #5, plus $\delta_k\to0$. There exists $X:(\mathbb N\to\mathbb N\times(\mathbb N\to\mathbb R))\to\mathbb R$ such that:
- (i) $X-\text{bandApprox}_0\in L^2$;
- (ii) for every $\ell$, $E(X-\text{bandApprox}_\ell)^2=T\int_{|z|<\delta_\ell}z^2\,d\nu$, and the integrand is integrable;
- (iii) for every $\ell$, $E(X\circ\mathrm{fst}-\text{bandGauss}_\ell)^2=2T\int_{|z|<\delta_\ell}z^2\,d\nu$, and the integrand is integrable;
- (iv) $T\int_{|z|<\delta_\ell}z^2\,d\nu\to0$;
- (v) for every $K$-Lipschitz $\Phi$ and every $\ell$, $\Phi(\text{bandGauss}_\ell)-\Phi(X)$ is integrable and $|E[\cdot]|\le K\sqrt{2T\int_{|z|<\delta_\ell}z^2\,d\nu}$.

**Assessment.**
- **Truth: true.**
  - $X$ is the $L^2$ limit of the independent, mean-zero band sums. Their variances are summable: $T\int_{|z|<\delta_0}z^2\,d\nu<\infty$.
  - (ii) is the tail variance. The atom at $0$ does not matter because $z^2=0$ there.
  - (iii) adds $s(\delta_\ell)^2$, using that $G$ is independent with mean 0.
  - (iv) follows by dominated convergence.
  - (v) follows from Lipschitz continuity and Cauchy–Schwarz.
- **Numerics.** Monte Carlo gives $1.519$ against the claimed $1.515$, and $0.7527$ against $0.7497$ (`check_bands.out`).
- **Measurability of $X$.** $X$ is not required to be measurable, but (i) and (ii) force it to be a.e. measurable, and (ii) determines $X$ a.e.
- **Vacuity: not vacuous.**
- **Hypotheses.** None is unusual. Note that (iii) and (v) make the Gaussian-corrected approximation worse in $L^2$ than the uncorrected one, by a factor 2.
- **Standard result.** The Lévy–Itô construction of the small-jump $L^2$ limit, and the weak error for Lipschitz functionals.

## 7. `levyGauss_expected_cost`

**Rendering.** Assume $\delta$ antitone (no sign condition), $\Lambda_kM_k=T\nu|_{\text{band}_k}$, and any $L$ and $N:\mathbb N\to\mathbb N$. Under the i.i.d. product over $(\ell,n)\in\mathbb N^2$ of the band input law $\otimes\,N(0,1)$, the cost
$$\sum_{\ell\le L}\sum_{n<N_\ell}\Bigl(1+\sum_{k\le\ell}N_k^{(\ell,n)}\Bigr)$$
is integrable, and its expectation is $\sum_{\ell\le L}N_\ell\bigl(1+T\,\nu(\{|z|\ge\delta_\ell\}).\mathrm{toReal}\bigr)$.

**Assessment.**
- **Truth: true.** $E N_k=\Lambda_k$. Evaluating the measure identity at $\mathbb R$ gives $\Lambda_k=T\nu(\text{band}_k)$. The bands $0..\ell$ partition $\{|z|\ge\delta_\ell\}$ when $\delta$ is antitone.
- **Junk.** If $T>0$, all masses are finite. If $T=0$, both sides vanish, since $0\cdot\infty=0$ in `ENNReal` and `toReal ∞ = 0` gives $0\cdot0$. So the formula is genuine in every case.
- **Numerics.** Monte Carlo gives $10.619$ against the formula $10.62$.
- **Vacuity: not vacuous.**
- **Standard result.** The expected number of simulated jumps (Wald identity).

## 8. `levyGauss_theorem1`

**Rendering.** Assume:
- $\int\min(1,z^2)\,d\nu<\infty$ and $\int_{|z|\ge1}z^2\,d\nu<\infty$;
- $T\in\mathbb R_{\ge0}$, $0<Y<2$, and real $a,b$;
- for all $\ell$, $T\int_{|z|<2^{-\ell}}z^2\,d\nu\le a\,2^{-(2-Y)\ell}$;
- for all $\ell$, $T\,\nu(|z|\ge2^{-\ell})\le b\,2^{Y\ell}$;
- the bands are built from $\delta_k=2^{-k}$, with $\Lambda_kM_k=T\nu|_{\text{band}_k}$;
- $\Phi$ is $K$-Lipschitz.

Then there exists $X$ such that:
- (i) for every $\ell$, $E(X-\text{bandGauss}_\ell)^2=2T\int_{|z|<2^{-\ell}}z^2\,d\nu$;
- (ii) $\Phi(X)$ is integrable;
- (iii) there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N_\ell>0$ (for all $\ell$) with the following properties. The MLMC estimator $\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}\bigl[\Phi(\text{bandGauss}_\ell)-\Phi(\text{bandGauss}_{\ell-1})\bigr](x_{\ell,n})$ uses i.i.d. samples, and the same sample (including the same $G$) serves both levels. Its error relative to $E\Phi(X)$ is in $L^2$ with MSE $<\varepsilon^2$. The expected cost equals $\sum_{\ell\le L}N_\ell\bigl(1+T\nu(|z|\ge2^{-\ell})\bigr)$, and this is $\le c_4\cdot\text{complexityBound}\bigl(\tfrac{2-Y}2,\,2-Y,\,Y,\,\varepsilon\bigr)$.

**Assessment.**
- **Truth: true.** Apply Giles' MLMC complexity theorem with:
  - bias at most $K\sqrt{2a}\,2^{-(2-Y)L/2}$ (by #6(v)), so $\alpha=(2-Y)/2$;
  - $V_\ell\le2K^2a\,2^{2-Y}2^{-(2-Y)\ell}$ for $\ell\ge1$ (by #5); $V_0<\infty$ because of `hlarge`; so $\beta=2-Y$;
  - $C_\ell\le(1+b)2^{Y\ell}$, so $\gamma=Y$.

  The condition $\alpha\ge\tfrac12\min(\beta,\gamma)$ holds. The resulting cost is $\varepsilon^{-2}$ for $Y<1$, $\varepsilon^{-2}\log^2\varepsilon$ for $Y=1$, and $\varepsilon^{-2Y/(2-Y)}$ for $Y>1$ (`check_stable.out`).
- **Clause (i) determines $X$ a.e.** By independence of $G$, (i) implies $E(X-\text{bandApprox}_\ell)^2=T\int\to0$, so the target is genuine.
- **Hypotheses.** `hsmall` and `hcount` force $a,b\ge0$. `hlarge` is necessary.
- **Weaker than the paper.** The rates are those of the uncorrected scheme, because the Gaussian is independent of the jumps (Main point 2). The setting is the terminal value of the process only.
- **Vacuity: not vacuous.** Take the stable-like $\nu$ from #9 with $a=Tc/(2-Y)$ and $b=Tc/Y$, or $\nu=0$.
- **Standard result.** Giles (2008), Theorem 1, applied to Lévy truncation MLMC (Dereich–Heidenreich 2011 / Dereich 2011 setting).

## 9. `levyGauss_stableLike_theorem1`

**Rendering.** Take $c>0$, $0<Y<2$, and $\nu(dz)=c\,z^{-1-Y}1_{(0,1]}(z)\,dz$, with dyadic bands and Lipschitz $\Phi$. The conclusion is that of #8 with explicit constants:
- $E(X-\text{bandGauss}_\ell)^2=2Tc\,2^{-(2-Y)\ell}/(2-Y)$;
- the cost is $\sum_\ell N_\ell\bigl(1+Tc(2^{Y\ell}-1)/Y\bigr)$.

**Assessment.**
- **Truth: true.** We have:
  - $T\int_0^{2^{-\ell}}cz^{1-Y}\,dz=Tc\,2^{-(2-Y)\ell}/(2-Y)$;
  - $T\int_{2^{-\ell}}^1cz^{-1-Y}\,dz=Tc(2^{Y\ell}-1)/Y$, which is $0$ for $\ell=0$ since $\{|z|\ge1\}\cap(0,1]=\{1\}$ is null;
  - `hν` holds with value $c/(2-Y)$, and `hlarge` holds trivially.

  So #8 applies. All values were checked with mpmath (`check_stable.out`).
- **Vacuity: not vacuous.** For example, $c=1$, $Y=1$, $T=1$.
- **Standard result.** A one-sided, truncated stable-like Lévy measure with Blumenthal–Getoor index $Y$.

## 10. `measure_eq_of_integral_exp_eq`

**Rendering.** Let $\mu_1,\mu_2$ be probability measures on $\mathbb R$ and $s>0$. Assume that for all $t\in(-s,s)$, $e^{tx}\in L^1(\mu_1)$ and $\int e^{tx}\,d\mu_1=\int e^{tx}\,d\mu_2$. Then $\mu_1=\mu_2$.

**Assessment.**
- **Truth: true.** Integrability under $\mu_2$ is not assumed but is forced: $\int e^{tx}\,d\mu_1>0$, while a non-integrable function has Bochner integral $0$. So the two moment generating functions are finite and equal on $(-s,s)$. They extend analytically to the strip $|\mathrm{Re}|<s$, so the characteristic functions agree and $\mu_1=\mu_2$.
- **Junk.** The junk convention only removes a redundant hypothesis; it does not weaken the result.
- **Vacuity: not vacuous.** For example, $\mu_1=\mu_2=N(0,1)$, $s=1$.
- **Standard result.** Uniqueness via the moment generating function (Curtiss 1942; Billingsley §30).

## 11. `gammaMeasure_conv`

**Rendering.** For $a,b,r>0$: $\Gamma(a,\text{rate }r)*\Gamma(b,\text{rate }r)=\Gamma(a+b,\text{rate }r)$ (Mathlib: shape $a$, rate $r$).

**Assessment.**
- **Truth: true.** This is the standard Gamma additivity. The density convolution was checked numerically (`check_vg.out`).
- **Vacuity: not vacuous.** For example, $a=b=r=1$.
- **Standard result.** Additivity of Gamma distributions with a common rate.

## 12. `vgLaw_conv`

**Rendering.** For $C,G,M,h_1,h_2>0$ and any real $b$: `vgLaw b C G M h₁ ∗ vgLaw b C G M h₂ = vgLaw b C G M (h₁+h₂)`.

**Assessment.**
- **Truth: true.** Use commutativity and associativity of convolution, $\delta_x*\delta_y=\delta_{x+y}$, #11 for both Gamma parts, and the fact that negation is additive (so map commutes with convolution).
- **Vacuity: not vacuous.**
- **Standard result.** Variance-Gamma increments form a convolution semigroup (Lévy process).

## 13. `integral_exp_mul_vgLaw`

**Rendering.** For $C,G,M,h>0$ and $-G<\theta<M$: $e^{\theta x}$ is integrable under `vgLaw`, and its integral is
$$e^{\theta bh}\Bigl(\tfrac{M}{M-\theta}\Bigr)^{Ch}\Bigl(\tfrac{G}{G+\theta}\Bigr)^{Ch}.$$
All bases are positive.

**Assessment.**
- **Truth: true.** This is the product of the Gamma moment generating functions. Numerically, quadrature matches the formula to 15 digits at $\theta\in\{-2.5,-0.4,1.2,4.5\}$.
- **Vacuity: not vacuous.**
- **Standard result.** The moment generating function of the CGM-form Variance-Gamma law.

## 14. `vg_asian_theorem1`

**Rendering.** Assume $C,G>0$, $M>2$, $T>0$, $|g(x)-g(y)|\le K|x-y|$ ($K$ real), and $s_0\in\mathbb R$. Let $A_{2^\ell}(y)=2^{-\ell}\sum_{k<2^\ell}\tfrac{s_0e^{S_k}+s_0e^{S_{k+1}}}2$, where $S_k=\sum_{i<k}y_i$. Then there exists $P$ such that:
- (a) $E\,g(A_{2^\ell})\to P$, where $y$ has i.i.d. `vgLaw(T/2^ℓ)` coordinates;
- (b) there is $c$ with $|E\,g(A_{2^\ell})-P|\le c/2^\ell$ for all $\ell$;
- (c) there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N_\ell>0$ with the following properties. The MLMC estimator has level-0 term $g(A_1(w_0))$ and level-$(\ell+1)$ term $g(A_{2^{\ell+1}}(w_{\ell+1}))-g(A_{2^\ell}(\text{pairSum}\,w_{\ell+1}))$. The samples are i.i.d. over $(\ell,n)$, and $w_{\ell'}$ has i.i.d. `vgLaw(T/2^{ℓ'})` coordinates. The error relative to $P$ is in $L^2$ with MSE $<\varepsilon^2$, and $\sum_{\ell\le L}N_\ell2^\ell\le c_4\varepsilon^{-2}$.

**Assessment.**
- **Truth: true.**
  - `pairSum` of i.i.d. `vgLaw(h/2)` increments is i.i.d. `vgLaw(h)` (by #12), so the sum telescopes.
  - The strong $L^2$ error of the trapezoidal average relative to $\frac1T\int_0^Ts_0e^{X_t}\,dt$ is $O(2^{-\ell})$, which gives (a) and (b) with $P=E\,g(\text{continuous average})$.
  - $E D_\ell^2=O(h^2)$ gives $\beta=2$, and $\gamma=1$. Giles' theorem then gives an $\varepsilon^{-2}$ cost.
  - $M>2$ is exactly the condition $Ee^{2X_t}<\infty$.
- **Numerics.** Exact second-moment computations give $E D_\ell^2/h^2\to0.7078$ (for $b=0.1$, $C=1.5$, $G=3$, $M=2.5$) and $n\sqrt{E(A_n-I)^2}\to0.4857$ (`check_asian.out`).
- **Junk.** `infinitePi` would be $0$ if a factor were not a probability measure (Main point 3). Here $C,G,M,T>0$ make every factor a probability measure, so the result is not junk.
- **Vacuity: not vacuous.** For example, $C=G=1$, $M=3$, $T=1$, $g=\mathrm{id}$, $K=1$.
- **Standard result.** MLMC for an Asian option under an exponential Variance-Gamma model (Giles 2008, Theorem 1; cf. Xia–Giles).

## 15. `vg_asian_variance_le`

**Rendering.** Same hypotheses as #14. There exists $c$ such that for every $\ell$, the difference $g(A_{2^{\ell+1}}(y))-g(A_{2^\ell}(\text{pairSum}\,y))$ is in $L^2$ and has variance at most $c\,(T/2^{\ell+1})^2$, where $y$ has i.i.d. `vgLaw(T/2^{ℓ+1})` coordinates.

**Assessment.**
- **Truth: true.** The difference of the averages is $D=\frac1{2n}\sum_j\bigl[S_{2j+1}-\tfrac{S_{2j}+S_{2j+2}}2\bigr]$. It is a sum of martingale-difference terms of size $O(\sqrt h)$ plus a mean of order $O(h)$, so $ED^2=O(h^2)$. The Lipschitz bound then transfers this to the variance.
- **Numerics.** Checked exactly (`check_asian.out`).
- **Vacuity: not vacuous.**
- **Standard result.** The $\beta=2$ level-variance bound for trapezoidal Asian MLMC.

## 16. `integral_exp_mul_vgSubLaw`

**Rendering.** For $\kappa,h>0$ and $u\theta+\sigma^2u^2/2<\kappa^{-1}$: $e^{ux}$ is integrable under `vgSubLaw`, and its integral is
$$e^{ubh}\Bigl(\frac{\kappa^{-1}}{\kappa^{-1}-(u\theta+\sigma^2u^2/2)}\Bigr)^{h/\kappa}.$$
The base is positive.

**Assessment.**
- **Truth: true.** Conditioning on $V$ gives $Ee^{(u\theta+\sigma^2u^2/2)V}$, which is the Gamma moment generating function. Quadrature matches the formula at $u\in\{-3,0.5,2\}$.
- **Hypotheses.** No sign condition on $\sigma$ or $\theta$ is needed.
- **Vacuity: not vacuous.**
- **Standard result.** The Madan–Carr–Chang (1998) moment generating function $(1-\kappa\theta u-\kappa\sigma^2u^2/2)^{-h/\kappa}$.

## 17. `vgSubLaw_conv`

**Rendering.** For $\kappa,h_1,h_2>0$ and any $b,\theta,\sigma$: `vgSubLaw … h₁ ∗ vgSubLaw … h₂ = vgSubLaw … (h₁+h₂)`.

**Assessment.**
- **Truth: true.** Conditionally on $V_i$, the laws are $N(\theta V_i,\sigma^2V_i)$, and these add. Combine this with #11 for the Gamma subordinator; alternatively use #10 together with #16.
- **Vacuity: not vacuous.**
- **Standard result.** Subordinated Brownian motion is a Lévy process.

## 18. `vgSubLaw_eq_vgLaw`

**Rendering.** Assume $\kappa,G,M,h>0$, $M^{-1}-G^{-1}=\theta\kappa$, and $(MG)^{-1}=\sigma^2\kappa/2$. Then `vgSubLaw b θ σ κ h = vgLaw b κ⁻¹ G M h`.

**Assessment.**
- **Truth: true.** We have $(1-u/M)(1+u/G)=1-\kappa(u\theta+\sigma^2u^2/2)$; sympy reduces the difference to $0$. So the moment generating functions agree near $0$, and #10 gives equality of the laws.
- **Vacuity: not vacuous.** For example, $G=M=2$, $\theta=0$, $\kappa=1$, $\sigma=1/\sqrt2$.
- **Standard result.** The Madan–Carr–Chang correspondence between the $(\theta,\sigma,\kappa)$ and $(C,G,M)$ parametrisations, with $C=1/\kappa$.

## 19. `vgSub_asian_theorem1`

**Rendering.** This is #14 with `vgSubLaw b θ σ κ (T/2^ℓ)` in place of `vgLaw`, under $\kappa>0$, $2\theta\kappa+2\sigma^2\kappa<1$, $T>0$, and $g$ $K$-Lipschitz.

**Assessment.**
- **Truth: true.** The condition `hexp` is $Ee^{2X_t}<\infty$, i.e. #16 at $u=2$. By convexity, every $u\in[0,2]$ is then admissible.
- **Numerics.** The same exact computations as for #14 give $E D^2/h^2\to0.1069$ and $n\sqrt{E(A_n-I)^2}\to0.1888$ for $\theta=0.1$, $\sigma=0.4$, $\kappa=0.8$.
- **Junk.** Every factor of `infinitePi` is a probability measure, since $h/\kappa>0$ and $\kappa^{-1}>0$.
- **Vacuity: not vacuous.** For example, $\theta=0$, $\sigma=0.5$, $\kappa=1$.
- **Standard result.** Same as #14.

## 20. `vgSub_asian_variance_le`

**Rendering.** This is #15 with `vgSubLaw` in place of `vgLaw`, under the hypotheses of #19.

**Assessment.**
- **Truth: true.** Same argument as #15.
- **Vacuity: not vacuous.**
- **Standard result.** The $\beta=2$ level-variance bound.
