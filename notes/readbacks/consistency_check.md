# Blind read-back report: packet R3 (MLMC consistency check)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round13/packet_R3_consistency.lean` |
| declarations audited | 11 (2 definitions, 9 theorems) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round13/work_R3/` (`scratch_packet.lean/.out`, `instance_sharp.lean/.out`, `mc_consistency.py/.out`, `twosample_clt.py/.out`) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `empMean` | def | n/a (biased sample mean, $0$ at $N=0$) | n/a | n/a |
| 2 | `empVar` | def | n/a (biased $1/N$ sample variance, $0$ at $N=0$) | n/a | n/a |
| 3 | `tendsto_empVar_ae` | theorem | true | no | no |
| 4 | `tendstoInMeasure_empVar` | theorem | true | no | no |
| 5 | `tendstoInDistribution_twoSample` | theorem | true | no | no |
| 6 | `tendstoInDistribution_consistencyStat` | theorem | true | no | no |
| 7 | `consistency_check_of_variance_estimates` | theorem | true | no | no |
| 8 | `consistency_check_of_empVar_le` | theorem | true | no | no |
| 9 | `consistency_check_empirical` | theorem | true | no | no |
| 10 | `consistency_check_empirical_lt` | theorem | true | no | no |
| 11 | `consistency_check_empirical_sharp` | theorem | true | no (instance checked in Lean) | no |

The scratch copy of the packet compiles; it is in `work_R3/scratch_packet.lean`, with the namespace renamed and all proofs left as `sorry`. In that file, `rfl` confirms that the packet's
`empMean`/`empVar` are definitionally equal to the library's `MLMC.empMean`/`MLMC.empVar`. It also checks
`empMean x 0 = 0`, `empVar x 0 = 0`, the cancellation identity
$-\bar B_N + \overline{(B-D)}_N = -\bar D_N$, and that `(0.003 : ℝ) = 3/1000`.

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.** All nine theorems are asymptotic: they take
   `Tendsto … atTop` or `∀ᶠ k in atTop` with $N_a,N_b\to\infty$. So the $N=0$ conventions
   (`empMean x 0 = 0/0 = 0`, `empVar x 0 = 0`, `V/0 = 0`) never matter.
2. **$P^f_{\ell+1}$ cancels exactly from the statistic.** Because `empMean` is linear,
   $a-b+c = \bar A_{N_a} - \overline{P^c_\ell}_{N_b}$ holds pointwise and exactly. So
   `tendstoInDistribution_consistencyStat` is `twoSample` with $f=P^f_\ell$, $g=P^c_\ell$, $i=\ell$, $j=\ell+1$.
   Its normaliser $\sqrt{\sigma_f^2/N_a+\sigma_c^2/N_b}$ is exactly $\mathrm{sd}(a-b+c)$. It needs
   no hypothesis on $P^f_{\ell+1}$, and has none.
3. **The two-sample CLT is correct with only second moments and arbitrary relative growth of $N_a,N_b$.**
   This follows from a characteristic-function argument in which the mixing weights lie in $[0,1]$. Monte Carlo
   (`twosample_clt.out`) gives $E[S^2]\approx 1.00$ for $(N_a,N_b)$ as unbalanced as $(10^6,10^3)$
   and $(10,10^3)$.
4. **`_of_empVar_le`, `_empirical` and `_lt` make no assumption about $P^f_{\ell+1}$**: neither $L^2$ nor
   measurability. They are still true, because empirical standard deviation is a seminorm on the sample vector, so
   $\sqrt{\widehat V_B}+\sqrt{\widehat V_C}\ge\sqrt{\widehat V_{P^c}}$ holds deterministically. The event
   may be non-measurable, but `μ.real` is then outer measure and monotonicity suffices.
5. **The `0.003` in `_lt` holds only eventually, and "eventually" can be late.** In the Gaussian sharp example
   with $N_a=N_b=N$, the exact false-alarm probability is $0.2804$ at $N=2$, $0.0192$ at $N=10$ and
   $0.00357$ at $N=100$. It first drops below $0.003$ at $N=275$, then approaches
   $P(|Z|\ge3)=0.0026998$ from above ($0.002708$ at $N=10^4$). Monte Carlo agrees. The packet makes no
   finite-$N$ claim.
6. **`_sharp` is satisfiable, and its limit is right.** A concrete instance is checked in Lean
   (`instance_sharp.lean`): $\Omega=\mathbb R^{\mathbb N\times\mathbb N}$ with an i.i.d. $N(0,1)$ product,
   $\omega(p)$ the coordinate maps, $\nu=N(0,1)$, $P^f\equiv0$, $P^c_\ell=\mathrm{id}$, $N_a=N_b=\mathrm{id}$.
   There the statistic is a biased-variance $t$-statistic, and $P(|t|>3)\to P(|Z|\ge3)$.
   The hypotheses `hPf₀` and `hPf₁` matter: Mathlib's `variance` of a non-$L^2$ function is the junk value $0$
   (`variance_of_not_memLp`), so without them `hf0`/`hf1` could hold vacuously. Both are present.
7. **The `Va, Vb, Vc` hypotheses in `consistency_check_of_variance_estimates` are natural.** Each is a one-sided
   condition: $N\cdot V$ is asymptotically $\ge$ the true variance in probability. Both the biased and the unbiased
   empirical variance divided by $N$ satisfy it (via `tendstoInMeasure_empVar` along $N_a(k)\to\infty$), as does
   any conservative over-estimate.
8. **The strong law uses pairwise independence plus identical distribution.** This is exactly Etemadi's
   hypothesis set, and the same as Mathlib's `strong_law_ae`. It is the weakest standard form, not a defect.
9. **Scope.** The results bound only the false-alarm rate when the identity $E[P^f_\ell]=E[P^c_\ell]$ holds.
   No statement covers the check's power, i.e. that it fails with probability $\to1$ when the identity is
   violated. `iIndepFun ω μ`, joint independence of the whole $\mathbb N\times\mathbb N$ sample array,
   is stronger than needed but natural.

### Notation used below

For sample $(i,n)$ write $Y_{i,n}=\omega(i,n)$, with law $\nu$; all of them are jointly independent. Set
$A_n=P^f_\ell(Y_{\ell,n})$, $B_n=P^f_{\ell+1}(Y_{\ell+1,n})$, $C_n=B_n-P^c_\ell(Y_{\ell+1,n})$ and $D_n=P^c_\ell(Y_{\ell+1,n})$.
Write $\bar X_N$ for `empMean X N` and $\widehat V_X(N)$ for `empVar X N`. The statistic is
$T_k=\bar A_{N_a(k)}-\bar B_{N_b(k)}+\bar C_{N_b(k)}$. The variances are
$\sigma_f^2=\mathrm{Var}_\nu P^f_\ell$, $\sigma_1^2=\mathrm{Var}_\nu P^f_{\ell+1}$,
$\sigma_Y^2=\mathrm{Var}_\nu(P^f_{\ell+1}-P^c_\ell)$ and $\sigma_c^2=\mathrm{Var}_\nu P^c_\ell$, and
$s_k^2=\sigma_f^2/N_a(k)+\sigma_c^2/N_b(k)$. Finally $p_3=P(|Z|\ge 3)=\operatorname{erfc}(3/\sqrt2)=0.00269979606$.
Mathlib's `variance X μ` is `(∫⁻ ‖X − μ[X]‖ₑ²).toReal`; it is the usual variance for $L^2$ functions and $0$ for non-$L^2$ ones.
Because $\mu$ is a probability measure and `MeasurePreserving (ω p) μ ν`, $\nu=\omega(p)_*\mu$ is a probability measure.

---

## 1. `empMean` (def)

**Rendering.** For $x:\mathbb N\to\mathbb R$ and $N\in\mathbb N$, $\mathrm{empMean}(x,N)=\frac1N\sum_{n<N}x_n$, with $N$ cast to $\mathbb R$.
At $N=0$ this is $0/0=0$ in Lean.

**Assessment.** It is the ordinary sample mean of the first $N$ terms. The junk value at $N=0$ is irrelevant to every
theorem below (see each theorem). It is linear in $x$ for every $N$, including $N=0$. This linearity makes $P^f_{\ell+1}$
cancel from $a-b+c$, as checked in Lean in `scratch_packet.lean`.

## 2. `empVar` (def)

**Rendering.** $\mathrm{empVar}(x,N)=\frac1N\sum_{n<N}(x_n-\mathrm{empMean}(x,N))^2$. This is the **biased** sample variance,
with denominator $N$ rather than $N-1$. At $N=0$ it is $0$.

**Assessment.** It is the standard biased (maximum-likelihood) variance estimator, equal to $\frac1N\sum x_n^2-\bar x_N^2$ for $N\ge1$.
The $N=0$ value plays no role in the asymptotic theorems. Its square root is a seminorm on $(x_0,\dots,x_{N-1})$; theorem 8 uses this.

## 3. `tendsto_empVar_ae`

**Rendering.** Let $(\Omega,\mu)$ be a probability space and $X_n:\Omega\to\mathbb R$. Assume $X_0\in L^2(\mu)$, that the $X_n$ are
**pairwise** independent, and that each $X_i$ has the same law as $X_0$ (`IdentDistrib` includes a.e.-measurability). Then for
$\mu$-a.e. $x$, $\mathrm{empVar}((X_n(x))_n,N)\to\mathrm{Var}_\mu(X_0)$ as $N\to\infty$.

**Assessment.** **True.** For $N\ge1$, $\mathrm{empVar}=\frac1N\sum_{n<N}X_n^2-(\frac1N\sum_{n<N}X_n)^2$. The
$X_n^2$ are pairwise independent (as compositions with a measurable map), identically distributed and integrable
(because $X_0\in L^2$). Etemadi's strong law (Mathlib `strong_law_ae`, whose hypothesis is
`Pairwise ((· ⟂ᵢ[μ] ·) on X)`) therefore gives a.s. convergence of both averages. The limit is
$E X_0^2-(EX_0)^2=\mathrm{Var}(X_0)$.

- **Hypotheses.** Pairwise independence plus identical distribution is exactly what Etemadi's SLLN needs, so the hypothesis is not weak in a harmful way.
- **Non-vacuous.** Take i.i.d. $N(0,1)$ coordinates on an infinite product.
- **Junk values.** None. $L^2$ is assumed, so `variance` is not the junk $0$, and the value at $N=0$ is irrelevant to a limit.

This is the strong consistency of the sample variance.

## 4. `tendstoInMeasure_empVar`

**Rendering.** Same hypotheses as theorem 3. For every $\varepsilon>0$, $\mu\{x:\varepsilon\le|\mathrm{empVar}((X_n(x)),N)-\mathrm{Var}(X_0)|\}\to0$
as $N\to\infty$. The measure used is the outer measure, so no measurability is needed in the definition.

**Assessment.** **True.** It follows from theorem 3, because a.s. convergence implies convergence in measure on a finite
measure space. Each `empVar` here is a.e.-measurable. Non-vacuous by the same instance as theorem 3, and no junk dependence.
This is the weak consistency of the sample variance.

## 5. `tendstoInDistribution_twoSample`

**Rendering.** Hypotheses:

- $\mu$ and $P'$ are probability measures.
- Each $\omega(p):\Omega\to\Omega_0$, $p\in\mathbb N\times\mathbb N$, is measure-preserving $\mu\to\nu$.
- The family $(\omega(p))_p$ is mutually independent (`iIndepFun`).
- $i\ne j$.
- $f,g\in L^2(\nu)$ with $\int f\,d\nu=\int g\,d\nu$ and $\mathrm{Var}_\nu f+\mathrm{Var}_\nu g>0$.
- $N_a,N_b:\mathbb N\to\mathbb N$ both tend to $\infty$; their relative rates are arbitrary.
- $Z\sim N(0,1)$ under $P'$.

Conclusion: the random variables
$$S_k=\frac{\overline{f(Y_{i,\cdot})}_{N_a(k)}-\overline{g(Y_{j,\cdot})}_{N_b(k)}}{\sqrt{\mathrm{Var} f/N_a(k)+\mathrm{Var} g/N_b(k)}}$$
converge in distribution to $Z$. Mathlib's `TendstoInDistribution` means that every $S_k$ is a.e.-measurable, $Z$ is
a.e.-measurable, and the laws converge weakly as `ProbabilityMeasure`s.

**Assessment.** **True.** The two groups of samples are independent because $i\ne j$. The numerator therefore has mean $0$
(because $\int f=\int g$) and variance exactly $\sigma_f^2/N_a+\sigma_g^2/N_b$, so the normalisation is right.

To see the limit, write $S_k=\alpha_k U_k-\beta_k V_k$, where $U_k,V_k$ are the standardised single-sample means
(independent of each other), $\alpha_k^2=(\sigma_f^2/N_a)/s_k^2$ and $\beta_k^2=1-\alpha_k^2$. If $\sigma_f=0$ the
$f$-term is a.s. $0$ and $\alpha_k=0$; likewise for $g$. By the i.i.d. CLT, $\varphi_{U_k}\to e^{-t^2/2}$ uniformly on
compacts (Lévy). Since $\alpha_k,\beta_k\in[0,1]$,
$\varphi_{S_k}(t)=\varphi_{U_k}(\alpha_kt)\varphi_{V_k}(-\beta_kt)\to e^{-(\alpha_k^2+\beta_k^2)t^2/2}=e^{-t^2/2}$.
Equivalently, Lindeberg's condition holds for the triangular array. This needs only second moments and no relation between
the growth rates of $N_a$ and $N_b$.

Measurability holds: $f\circ\omega(p)$ is a.e.-measurable because $\omega(p)$ is measure-preserving. For finitely many
$k$, $N_a(k)=0$ gives junk numerators and denominators, which is irrelevant to the limit.

- **Necessary hypotheses.** All of `hij`, `hfg` and `hpos` are needed:
  - without `hij` the two means are correlated;
  - without `hfg` the numerator diverges;
  - without `hpos` the denominator is $0$ and $S_k\equiv 0/0=0$ in Lean, which does not converge to $N(0,1)$.
- **Numerical check.** In `twosample_clt.out`, with $f\sim\mathrm{Exp}(1)$ and $g\sim\Gamma(4,1/4)$ (equal means, variances $1$ and $1/4$), $E[S^2]=1.00$ for
  $(N_a,N_b)\in\{(10,10^3),(10^3,10),(10^3,10^6),(10^6,10^3),(10^4,10^4)\}$. Tail frequencies approach $0.05$ and $0.0027$ as
  $\min(N_a,N_b)$ grows.
- **Non-vacuous.** The product-Gaussian instance of theorem 11 works, with $f=g=\mathrm{id}$, $\nu=N(0,1)$, $i=0$, $j=1$ and $Z=\mathrm{id}$ under $N(0,1)$.

This is the CLT for a difference of two independent sample means (Welch-type z-statistic with known variances).

## 6. `tendstoInDistribution_consistencyStat`

**Rendering.** Same probabilistic setup as theorem 5. $P^f,P^c:\mathbb N\to\Omega_0\to\mathbb R$, with $P^f_\ell,P^c_\ell\in L^2(\nu)$
and $\int P^f_\ell\,d\nu=\int P^c_\ell\,d\nu$. There is **no** assumption on $P^f_{\ell+1}$. Also
$\mathrm{Var}P^f_\ell+\mathrm{Var}P^c_\ell>0$, $N_a,N_b\to\infty$ and $Z\sim N(0,1)$. Then
$(\bar A_{N_a(k)}-\bar B_{N_b(k)}+\bar C_{N_b(k)})/\sqrt{\sigma_f^2/N_a(k)+\sigma_c^2/N_b(k)}\to Z$ in distribution.

**Assessment.** **True.** Since `empMean` is linear, $-\bar B_N+\bar C_N=-\bar D_N$ holds exactly for every $N$, including $0$.
This was checked in Lean. The statistic is therefore literally the theorem-5 statistic with $f=P^f_\ell$, $g=P^c_\ell$, $i=\ell$,
$j=\ell+1\ne\ell$. The denominator is exactly $\mathrm{sd}(a-b+c)$:
$\mathrm{Var}(a)=\sigma_f^2/N_a$, and $\mathrm{Var}(c-b)=\mathrm{Var}(\bar D)=\sigma_c^2/N_b$.

Leaving out any hypothesis on $P^f_{\ell+1}$ is legitimate. The function $x\mapsto T_k(x)$ equals a measurable function
pointwise, so a.e.-measurability holds whatever $P^f_{\ell+1}$ is. Non-vacuous by the theorem-11 instance, and no junk dependence.

This is the CLT for Giles' MLMC consistency statistic $a-b+c$, which uses identity $E[P^f_\ell]=E[P^c_\ell]$.

## 7. `consistency_check_of_variance_estimates`

**Rendering.** Setup as above, with $P^f_\ell,P^f_{\ell+1},P^c_\ell\in L^2(\nu)$, $\int P^f_\ell=\int P^c_\ell$, $N_a,N_b\to\infty$,
and $V_a,V_b,V_c:\mathbb N\to\Omega\to\mathbb R$ arbitrary; they need not be measurable. Assume:

- for every $c<\sigma_f^2$, $\mu\{N_a(k)V_a(k)<c\}\to0$;
- for every $c<\sigma_1^2$, $\mu\{N_b(k)V_b(k)<c\}\to0$;
- for every $c<\sigma_Y^2$, $\mu\{N_b(k)V_c(k)<c\}\to0$.

Here $N$ is cast to $\mathbb R$ and the measure is the outer measure. Then for every $\eta>0$, eventually in $k$,
$$\mu\{3(\sqrt{V_a(k)}+\sqrt{V_b(k)}+\sqrt{V_c(k)})<|T_k|\}<p_3+\eta.$$
The square root of a negative number is $0$ in Lean. Taken over all $\eta$, the conclusion is equivalent to $\limsup_k(\cdot)\le p_3$.

**Assessment.** **True.**

*Degenerate case: $\sigma_f^2+\sigma_c^2=0$.* Then $P^f_\ell=P^c_\ell=m$ $\nu$-a.e., because the means are equal. So $T_k=0$
a.s. once $N_a,N_b\ge1$, and the event $\{3(\ge0)<0\}$ is null.

*Otherwise:* fix $\delta\in(0,1)$. With probability $\to1$, $\sqrt{V_a}\ge(1-\delta)\sigma_f/\sqrt{N_a}$, and similarly for $V_b$
and $V_c$. When a $\sigma$ is $0$ the bound $\sqrt{\cdot}\ge0$ is trivial. By Minkowski in $L^2(\nu)$, $\sigma_c\le\sigma_1+\sigma_Y$,
because $P^c_\ell=P^f_{\ell+1}-(P^f_{\ell+1}-P^c_\ell)$. This step uses `hPf₁`. Hence the threshold is at least
$3(1-\delta)(\sigma_f/\sqrt{N_a}+\sigma_c/\sqrt{N_b})\ge3(1-\delta)s_k$. The event is contained in
$\{|T_k|/s_k>3(1-\delta)\}\cup\{\text{bad sets}\}$. By outer-measure subadditivity and theorem 6 (portmanteau; $N(0,1)$
has no atoms), $\limsup\le P(|Z|\ge3(1-\delta))$. This tends to $p_3$ as $\delta\downarrow0$. There is no `hpos`, and none is needed.

- **The $V$ hypotheses are satisfiable by natural estimators.** $V_a(k)=\mathrm{empVar}(A,N_a(k))/N_a(k)$ works, as does the unbiased
  $s^2/N$. Indeed $N_aV_a=\mathrm{empVar}$ for $N_a\ge1$, and it tends to $\sigma_f^2$ in probability (theorem 4 composed with $N_a\to\infty$).
  Any conservative over-estimate also works. The one-sided form is the right one, since over-estimating the variance only makes the check more conservative.
- **`hPf₁` is genuinely used.** Without it, $\sigma_1^2$ could be the junk $0$ and the Minkowski step would fail.
- **Non-vacuous.** Use the theorem-11 instance with $V$ given by the empirical variances.

This is the asymptotic false-alarm bound of Giles' MLMC consistency check, $|a-b+c|>3(\sqrt{V_a}+\sqrt{V_b}+\sqrt{V_c})$.

## 8. `consistency_check_of_empVar_le`

**Rendering.** As theorem 7, but with only $P^f_\ell,P^c_\ell\in L^2$ assumed. There is no assumption on $P^f_{\ell+1}$, not even
measurability. Instead of the in-probability hypotheses: eventually in $k$, $\mu$-a.e.,

- $V_a(k)\ge\mathrm{empVar}(A,N_a(k))/N_a(k)$,
- $V_b(k)\ge\mathrm{empVar}(B,N_b(k))/N_b(k)$,
- $V_c(k)\ge\mathrm{empVar}(C,N_b(k))/N_b(k)$.

The conclusion is the same: for every $\eta>0$, eventually $\mu\{3(\sqrt{V_a}+\sqrt{V_b}+\sqrt{V_c})<|T_k|\}<p_3+\eta$.

**Assessment.** **True.** $\sqrt{\mathrm{empVar}}$ is a seminorm on the sample vector, and $D=B-C$ samplewise. Hence, deterministically,
$\sqrt{\widehat V_B}+\sqrt{\widehat V_C}\ge\sqrt{\widehat V_D}$. Up to a null set, the event is therefore contained in the
measurable event $\{3(\sqrt{\widehat V_A/N_a}+\sqrt{\widehat V_D/N_b})<|T_k|\}$, using monotonicity of outer measure.

That event involves only $P^f_\ell$ and $P^c_\ell$, which are $L^2$. Theorem 3/4 gives $\widehat V_A\to\sigma_f^2$ and
$\widehat V_D\to\sigma_c^2$, and theorem 6 gives the CLT. The same $\delta$-argument as in theorem 7, or the degenerate case
$T_k=0$ a.s., bounds the limsup by $p_3$.

The missing $L^2$/measurability hypothesis on $P^f_{\ell+1}$ is harmless, and strictly more general. The hypotheses are
satisfiable (equality, with the theorem-11 instance) and no junk value is used. This is the same result as theorem 7, for the
estimators actually used in practice, or any larger ones.

## 9. `consistency_check_empirical`

**Rendering.** Theorem 8 with $V_a=\mathrm{empVar}(A,N_a)/N_a$, $V_b=\mathrm{empVar}(B,N_b)/N_b$ and $V_c=\mathrm{empVar}(C,N_b)/N_b$
substituted. Hypotheses: $P^f_\ell,P^c_\ell\in L^2$, equal means, $N_a,N_b\to\infty$ and $\eta>0$. Conclusion: eventually the
false-alarm probability is $<p_3+\eta$.

**Assessment.** **True.** This is the special case of theorem 8 with equality in its hypotheses. Non-vacuous (theorem-11 instance)
and no junk dependence. These are exactly Giles' $V_\ell/N_\ell$ estimators with the biased variance.

## 10. `consistency_check_empirical_lt`

**Rendering.** The same hypotheses as theorem 9, without $\eta$. Conclusion: eventually in $k$, the false-alarm probability is
$<0.003$ (the real number $3/1000$).

**Assessment.** **True.** Take $\eta=0.003-p_3=0.0003002>0$ in theorem 9; $p_3=0.00269979606$, computed in `mc_consistency.out`.

It is not trivially true, and the word "eventually" matters. In the Gaussian sharp example with $N_a=N_b=N$, the exact
probability is $P(|t_{N-1}|>3\sqrt{(N-1)/N})$:

| $N$ | exact probability |
|---|---|
| 2 | $0.2804$ ($=1-\frac2\pi\arctan(3/\sqrt2)$) |
| 5 | $0.0550$ |
| 10 | $0.0192$ |
| 50 | $0.00460$ |
| 100 | $0.00357$ |
| 200 | $0.00312$ |
| 275 | first $N$ below $0.003$ |
| 1000 | $0.00278$ |
| $10^4$ | $0.002708$ |

Direct and sufficient-statistic Monte Carlo agree within one or two standard errors. The convergence is from above, so no
finite-$N$ bound of $p_3$ holds in general. The statement does not claim one. With a skewed centred $\mathrm{Exp}(1)$ in place of
$N(0,1)$ the approach is slower still: MC gives $0.0051\pm0.0007$ at $N=300$.

## 11. `consistency_check_empirical_sharp`

**Rendering.** The hypotheses are:

- $P^f_\ell,P^f_{\ell+1},P^c_\ell\in L^2(\nu)$;
- $\int P^f_\ell=\int P^c_\ell$;
- $\mathrm{Var}P^f_\ell=0$, $\mathrm{Var}P^f_{\ell+1}=0$ and $\mathrm{Var}P^c_\ell>0$;
- $N_a,N_b\to\infty$.

Conclusion: the false-alarm probability (empirical thresholds, as in theorem 9) converges to $p_3=P(|Z|\ge3)$.

**Assessment.** **True, and the limit is correct.** Since $P^f_\ell=m$ and $P^f_{\ell+1}=m'$ $\nu$-a.e. ($L^2$ and variance $0$), a.s.
$\bar A=m$, $\widehat V_A=\widehat V_B=0$ and $\widehat V_C=\widehat V_D$. Also $T_k=m-\bar D_{N_b}$ with $E D=m$. The event is
$\{\sqrt{N_b}\,|\bar D-m|/\sqrt{\widehat V_D}>3\}$, the biased-variance $t$-statistic exceeding $3$. By the CLT and Slutsky
($\widehat V_D\to\sigma_c^2>0$), its probability tends to $P(|Z|>3)=P(|Z|\ge3)$, since $N(0,1)$ has no atoms.

- **Satisfiable instance, checked in Lean** (`instance_sharp.lean`, all hypotheses proved). Take
  - $\Omega=\mathbb R^{\mathbb N\times\mathbb N}$ with `Measure.infinitePi (fun _ => gaussianReal 0 1)`;
  - $\omega(p)$ the evaluation at $p$ (`measurePreserving_eval_infinitePi`, `iIndepFun_infinitePi`);
  - $\nu=N(0,1)$, $P^f\equiv0$, $P^c_\ell=\mathrm{id}$, $\ell=0$, $N_a=N_b=\mathrm{id}$.

  Then $\mathrm{Var}P^c_0=1$.
- **Numerical check.** For this instance the exact finite-$N$ probabilities in the table under theorem 10 tend to $0.0027$,
  confirmed by Monte Carlo. At $N=2$ the probability is $0.280$, far above $0.003$.
- **Junk-value guard.** `hPf₀` and `hPf₁` prevent `hf0`/`hf1` from being satisfied by the junk value
  $\mathrm{Var}=0$ for non-$L^2$ functions (`variance_of_not_memLp`).
- **Modelling note.** The instance is unnatural as MLMC, since the fine level-$(\ell+1)$ output is constant while the coarse
  one is random. It serves only to show that the constant $p_3$ in theorems 7–9 cannot be improved. Sharpness also arises
  more naturally, in the limit $N_a/N_b\to\infty$ with $P^f_{\ell+1}=P^c_\ell$.

This is the sharpness of the 3-sigma consistency check: an asymptotic $t$-test false-alarm rate.
