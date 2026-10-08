# Blind read-back report: packet R40 (truncated Karhunen–Loève field)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round23/packet_R40_kl.lean` |
| declarations audited | 9 (2 definitions, 7 theorems) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round23/work_R40_kl/` (`check_kl.py` / `check_kl.out`; elaboration check `scratch_R40.lean` / `scratch_R40.out`) |

The elaboration check compiled a copy of the packet (proofs still `sorry`) against Mathlib alone
(`Mathlib.Probability.Distributions.Gaussian.Real`, `Mathlib.Probability.ProductMeasure`), with
`stdNormalSeq` redefined locally exactly as in the packet appendix. All 7 statements elaborate. I
checked the casts and operator precedence with `pp.numericTypes`/`pp.coercions`: `klDiffusivity … ^ p` is `Real.rpow`
because `p : ℝ`. `p ^ 2 * S / 2` parses as $(p^2 S)/2$. Every sum is in ℝ.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `klField` | def | n/a | n/a | n/a (but see the note on $\sqrt{\theta_n}$ for $\theta_n<0$) |
| 2 | `klDiffusivity` | def | n/a | n/a | n/a |
| 3 | `klField_levelCorrection` | theorem | true | no | no |
| 4 | `exists_klField_limit` | theorem | true | no | no |
| 5 | `map_klField_eq_gaussianReal` | theorem | true | no | no (the degenerate case uses `gaussianReal 0 0 = dirac 0`, the standard convention) |
| 6 | `klDiffusivity_moment` | theorem | true | no | no |
| 7 | `integral_klField_mul` | theorem | true | no | no |
| 8 | `tendsto_integral_klField_mul` | theorem | true | no | no |
| 9 | `kl_hypotheses_satisfiable` | theorem | true | n/a (existence statement) | no |

## Main points for a human auditor

- All 7 theorems are true and non-vacuous. None depends on a junk value. `klField` would silently
  set $\sqrt{\theta_n}=0$ when $\theta_n<0$, but every theorem assumes `hθ : ∀ n, 0 ≤ θ n`, so this
  never comes up.
- The theorems are more general than KL theory needs. They never assume that $f_n$ are
  eigenfunctions of a covariance operator: #3 and #4 need only an $L^2(\nu)$-orthonormal family, and
  #5–#8 are pointwise in $x$ and need no orthonormality at all. $R$ in #6 and #8 is just "the value
  of the series $\sum_n\theta_n f_n(x)f_n(y)$" (a `HasSum` hypothesis), not a given covariance kernel. The
  eigen-equation appears only in the witness #9 and is never used as a hypothesis. So the link
  to "the KL expansion of a given kernel $R$" comes only from the names. This makes the theorems more
  general, not weaker.
- #3 and #4 measure the error in $L^2(\mathbb P\otimes\nu)$ of the **log-field**
  $a_K=\sum_{n<K}\sqrt{\theta_n}z_nf_n$, not of the diffusivity $e^{a_K}$. #6 bounds
  $\mathbb E[e^{p\,a_K(x)}]$ pointwise in $x$ only. There is no uniform-in-$x$ bound, which would
  need $\sup_x R(x,x)<\infty$.
- #9 shows the hypotheses can be met with the discrete witness $D=\mathbb N$, counting measure,
  $f_n=\mathbf 1_{\{n\}}$, diagonal kernel $R(x,y)=\theta_x\mathbf 1_{x=y}$. That is enough for
  non-vacuity, but it is not a continuous-domain KL example. Its last two conjuncts hold for every
  $\theta$, including negative ones.

---

## 1. `klField` (definition)

**Rendering.** For $\theta:\mathbb N\to\mathbb R$, $f:\mathbb N\to D\to\mathbb R$, $K\in\mathbb N$,
$z\in\mathbb R^{\mathbb N}$, $x\in D$:
$$\mathrm{klField}(\theta,f,K,z,x)=\sum_{n=0}^{K-1}\sqrt{\theta_n}\,z_n\,f_n(x).$$
Here `Real.sqrt`, so $\sqrt{\theta_n}=0$ when $\theta_n<0$ (junk). This is the $K$-term truncated KL
expansion of a centred Gaussian field.

## 2. `klDiffusivity` (definition)

**Rendering.** $\mathrm{klDiffusivity}(\theta,f,K,z,x)=\exp(\mathrm{klField}(\theta,f,K,z,x))$, the
truncated log-normal diffusion coefficient $a_K(x)=e^{g_K(x)}$. It is always $>0$.

`stdNormalSeq` (appendix) is `Measure.infinitePi (fun _ => gaussianReal 0 1)`, the law of an i.i.d.
$N(0,1)$ sequence on $\mathbb R^{\mathbb N}$. Every factor is a probability measure, so Mathlib's
`infinitePi` is the genuine product (its `else 0` branch is not taken).

## 3. `klField_levelCorrection`

**Rendering.** Let $(D,\mathcal D)$ be a measurable space and $\nu$ an s-finite measure on it. Assume
$\theta_n\ge0$ for all $n$, each $f_n\in L^2(\nu)$, and $\int f_nf_m\,d\nu=\delta_{nm}$ for all $n,m$
(Bochner integral). Then for all $K\le M$ (both in ℕ), the function
$(z,x)\mapsto(\mathrm{klField}_M(z,x)-\mathrm{klField}_K(z,x))^2$ is integrable with respect to
$\mathrm{stdNormalSeq}\otimes\nu$, and
$$\int\!\!\int\Big(\sum_{n=K}^{M-1}\sqrt{\theta_n}z_nf_n(x)\Big)^2\,d\nu(x)\,d\mathbb P(z)=\sum_{n\in[K,M)}\theta_n .$$

**Assessment.**
- *Truth:* true. The difference is $\sum_{n=K}^{M-1}\sqrt{\theta_n}z_nf_n(x)$. Its square is a finite
  sum of terms $\sqrt{\theta_n\theta_m}\,z_nz_m\,f_n(x)f_m(x)$. Each term is integrable on the
  product: $z_nz_m\in L^1(\mathbb P)$, $f_nf_m\in L^1(\nu)$ by Cauchy–Schwarz, and the product of
  integrable functions of separate variables is integrable. Fubini then gives
  $\mathbb E[z_nz_m]\int f_nf_m=\delta_{nm}\cdot\delta_{nm}$. So the integral is
  $\sum_{K\le n<M}\theta_n$. I checked this exactly (sympy) for $D=[0,1]$,
  $f_n=\sqrt2\sin((n+1)\pi x)$, $\theta_n=(n+1)^{-2}$ and several $(K,M)$, including $K=M$
  (`check_kl.out`).
- *Vacuity:* not vacuous. Take $D=\mathbb N$, $\nu$ = counting measure, $f_n=\mathbf 1_{\{n\}}$,
  $\theta_n=2^{-n}$ (see #9), or Lebesgue measure on $[0,1]$ with the sine basis.
- *Junk:* none. `hf` makes every $f_nf_m$ integrable, so the Bochner integrals in `hfo` are genuine,
  and the conclusion asserts integrability. `hθ` rules out the $\sqrt{\text{negative}}$ junk.
- *Hypotheses:* standard. Orthonormality is all that is used. They do not need to be
  eigenfunctions, so the statement is more general than the KL version. `SFinite ν` is what
  Mathlib's `Measure.prod` needs.
- *Standard result:* Parseval/Itô-isometry identity for the truncated KL expansion,
  $\mathbb E\|g_M-g_K\|_{L^2(D)}^2=\sum_{K\le n<M}\theta_n$. This is the variance of the
  level-correction of the log-field.

## 4. `exists_klField_limit`

**Rendering.** Same setting as #3 ($\nu$ s-finite, $\theta_n\ge0$, $f_n\in L^2(\nu)$ orthonormal),
plus $\theta$ summable. Then **there exists** $Y:\mathbb R^{\mathbb N}\times D\to\mathbb R$ (it may depend on
$\theta,f,\nu$) with $Y\in L^2(\mathrm{stdNormalSeq}\otimes\nu)$ such that:
- for **every** $K\in\mathbb N$, $(Y-\mathrm{klField}_K)^2$ is integrable and
  $\int (Y-\mathrm{klField}_K)^2\,d(\mathbb P\otimes\nu)=\sum_{n\ge0}\theta_{n+K}$ (a `tsum`);
- $\int (Y-\mathrm{klField}_K)^2\to0$ as $K\to\infty$.

**Assessment.**
- *Truth:* true. By #3 the partial sums $S_K$ form a Cauchy sequence in
  $L^2(\mathbb P\otimes\nu)$, because $\|S_M-S_K\|^2=\sum_{K\le n<M}\theta_n$ and $\theta$ is
  summable. By completeness they converge to some $Y\in L^2$. Then
  $\|Y-S_K\|^2=\lim_M\|S_M-S_K\|^2=\sum_{n\ge K}\theta_n=\sum_n\theta_{n+K}$, and this tail tends to
  $0$. The tail values for $\theta_n=2^{-n}$ were checked to be $2^{1-K}$.
- *Vacuity:* not vacuous. Use the same instance as #3 with $\theta_n=2^{-n}$.
- *Junk:* none. Integrability is asserted, and the `tsum` is of a summable series
  (a shift of a summable series), so it is a real sum.
- *Hypotheses:* standard. $Y$ is existential, but the identities force $Y=\lim S_K$
  $(\mathbb P\otimes\nu)$-a.e., so $Y$ is pinned down a.e. and the statement is not weakened. The
  third conjunct follows from the second.
- *Standard result:* $L^2$ convergence of the KL series (Itô–Nisio/Parseval type) with the exact
  truncation error $\mathbb E\|g-g_K\|^2_{L^2(D)}=\sum_{n\ge K}\theta_n$.

## 5. `map_klField_eq_gaussianReal`

**Rendering.** For $\theta_n\ge0$, any $f$, any $K\in\mathbb N$ and any point $x\in D$ ($D$ needs no
measurable structure), the pushforward of $\mathrm{stdNormalSeq}$ under
$z\mapsto\mathrm{klField}(\theta,f,K,z,x)$ is $N\big(0,\ \sum_{n<K}\theta_nf_n(x)^2\big)$ (the
variance is passed as `.toNNReal`).

**Assessment.**
- *Truth:* true. The map is $\sum_{n<K}c_nz_n$ with $c_n=\sqrt{\theta_n}f_n(x)$. It is measurable,
  so `Measure.map` is genuine. A sum of independent $N(0,c_n^2)$ variables is
  $N(0,\sum c_n^2)$, and $c_n^2=\theta_nf_n(x)^2$ because $\theta_n\ge0$. I checked the CDF
  numerically for $K=2$ (`check_kl.out`).
- *Vacuity:* not vacuous (any $\theta\ge0$, e.g. $\theta_n=1$, $f_n(x)=1$, $K=2$ gives $N(0,2)$).
- *Junk:* `.toNNReal` is applied to a non-negative number, so it has no effect. When $K=0$ or all
  $f_n(x)=0$, both sides are $\delta_0$, by Mathlib's `gaussianReal μ 0 = dirac μ`. This is the
  standard degenerate-Gaussian convention, not a junk artefact. `hθ` is needed: for $\theta_n<0$
  the left side drops the term while the right side subtracts it.
- *Standard result:* the truncated KL field at a fixed point is centred Gaussian with variance
  $\sum_{n<K}\theta_nf_n(x)^2$ (stability of Gaussians under independent sums).

## 6. `klDiffusivity_moment`

**Rendering.** Assume $\theta_n\ge0$, and let $f$, $R:D\to D\to\mathbb R$ and $x\in D$ be such that
$\sum_n\theta_nf_n(x)f_n(x)$ converges unconditionally (`HasSum`) to $R(x,x)$. Then for **all**
$p\in\mathbb R$ and $K\in\mathbb N$:
1. $z\mapsto \mathrm{klDiffusivity}_K(z,x)^p$ (`Real.rpow` of a positive base) is
   integrable with respect to $\mathrm{stdNormalSeq}$;
2. $\int \exp(g_K(x))^p\,d\mathbb P=\exp\!\big(p^2\sigma_K^2(x)/2\big)$, where
   $\sigma_K^2(x)=\sum_{n<K}\theta_nf_n(x)^2$;
3. $\exp(p^2\sigma_K^2(x)/2)\le\exp(p^2R(x,x)/2)$.

**Assessment.**
- *Truth:* true. The base $e^{g_K(x)}>0$, so $(e^{g_K})^p=e^{p\,g_K}$. By #5,
  $g_K(x)\sim N(0,\sigma_K^2)$, so $\mathbb E e^{pG}=e^{p^2\sigma_K^2/2}$ and the integrand is
  integrable. For (3), the terms $\theta_nf_n(x)^2\ge0$, so partial sums are at most the sum
  $R(x,x)$, and $p^2\ge0$. I checked the moment numerically for $K=2$ and $p\in\{1,-2.5,0.5,3\}$.
- *Vacuity:* not vacuous ($\theta_n=2^{-n}$, $f_n\equiv1$, $R(x,x)=2$).
- *Junk:* none. The rpow has a strictly positive base, and integrability is asserted.
- *Hypotheses:* `hR` is used only for (3). The bound is pointwise in $x$; it is not uniform over $D$.
- *Standard result:* moments of the log-normal diffusivity,
  $\mathbb E[a_K(x)^p]=\exp(p^2\sigma_K^2(x)/2)\le\exp(p^2R(x,x)/2)$, uniformly in $K$.

## 7. `integral_klField_mul`

**Rendering.** For $\theta_n\ge0$, any $f$, $K$, $x,y\in D$: $z\mapsto g_K(z,x)\,g_K(z,y)$ is
integrable with respect to $\mathrm{stdNormalSeq}$, and
$\mathbb E[g_K(x)g_K(y)]=\sum_{n<K}\theta_nf_n(x)f_n(y)$.

**Assessment.**
- *Truth:* true. Expand the product. Each $z_nz_m$ is integrable, and $\mathbb E[z_nz_m]=\delta_{nm}$
  and $\sqrt{\theta_n}^2=\theta_n$. I checked symbolically for $K=3$ (sympy).
- *Vacuity:* not vacuous. *Junk:* none, since integrability is asserted and `hθ` avoids the
  $\sqrt{\cdot}$ junk.
- *Standard result:* the covariance of the truncated KL field is the truncated Mercer sum.

## 8. `tendsto_integral_klField_mul`

**Rendering.** For $\theta_n\ge0$, any $f$, and $x,y$ with
$\sum_n\theta_nf_n(x)f_n(y)=R(x,y)$ (unconditional `HasSum`):
$\mathbb E[g_K(x)g_K(y)]\to R(x,y)$ as $K\to\infty$.

**Assessment.**
- *Truth:* true. By #7 the integral equals the partial sum $\sum_{n<K}$, and `HasSum` implies that
  the partial sums over `range K` converge to the sum.
- *Vacuity:* not vacuous (as in #6). *Junk:* none.
- *Hypotheses:* `HasSum` (unconditional convergence) is the natural hypothesis. It follows, for
  example, from Mercer's theorem, or from Cauchy–Schwarz given summability on the two diagonals.
- *Standard result:* the covariance of the truncated KL field converges to the kernel $R$
  (Mercer expansion $R(x,y)=\sum_n\theta_nf_n(x)f_n(y)$).

## 9. `kl_hypotheses_satisfiable`

**Rendering.** The counting measure on ℕ is s-finite, **and there exists** $f:\mathbb N\to\mathbb N\to\mathbb R$
such that:
- each $f_n\in L^2(\text{count})$;
- $\sum_xf_n(x)f_m(x)=\delta_{nm}$ (as a Bochner integral);
- for **every** $\theta:\mathbb N\to\mathbb R$ and all $n,x$,
  $\int(\mathbf 1_{x=y}\theta_x)f_n(y)\,d\text{count}(y)=\theta_nf_n(x)$. This is the eigen-equation
  for the diagonal kernel $R(x,y)=\theta_x\mathbf 1_{x=y}$;
- for every $\theta$ and all $x,y$, $\sum_n\theta_nf_n(x)f_n(y)=\theta_x\mathbf 1_{x=y}$ (`HasSum`).

**Assessment.**
- *Truth:* true, with witness $f_n=\mathbf 1_{\{n\}}$. Counting measure on a countable type is
  σ-finite. Each $f_n$ has finite support, so every integral and sum is a finite sum. Then
  $\int R(x,\cdot)f_n=\theta_x\mathbf 1_{x=n}=\theta_n\mathbf 1_{n=x}$, and the Mercer series has at
  most one nonzero term. I checked this on a truncation with random signed $\theta$.
- *Vacuity:* n/a (an existence statement). It shows that the hypotheses `SFinite ν`, `hf`, `hfo`
  of #3/#4, together with an eigen-structure and the `HasSum` hypotheses of #6/#8, can be met
  jointly.
- *Junk:* none. The integrands are finitely supported, so the Bochner integrals are genuine.
- *Remark:* the example is the trivial diagonal (discrete white-noise) kernel. It establishes
  consistency, not a continuous-domain KL example.
- *Standard fact:* the standard basis of $\ell^2(\mathbb N)$ diagonalises a diagonal kernel.
