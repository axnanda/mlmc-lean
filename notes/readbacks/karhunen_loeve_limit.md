# Blind read-back report: packet R43 (Karhunen–Loève limit)

| Field | Value |
|---|---|
| Date | 2026-10-08 |
| Packet | `readback/round24/packet_R43_kllimit.lean` |
| Declarations audited | 11 in the module (9 theorems + 2 definitions); the 3 appended definitions are also rendered |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round24/work_R43_kllimit/` (`r43_checks.py` / `.out`; elaboration check `scratch_R43.lean`) |

Elaboration check: a copy of the packet compiled with `import MlmcLean` (only the `sorry` warnings).
The packet's copies of `klLimit`, `klLimitDiffusivity`, `klField`, `klDiffusivity` and
`stdNormalSeq` are equal by `rfl` to the library constants. `f n x ^ 2` elaborates with exponent
`(2 : ℕ)` (monoid power). `klLimitDiffusivity θ f z x ^ p` with `p : ℝ` is `Real.rpow`.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| D1 | `klLimit` | def | n/a | n/a | junk off the convergence set (`limUnder`), never used non-a.e. |
| D2 | `klLimitDiffusivity` | def | n/a | n/a | inherits D1 |
| 1 | `klLimit_tendsto` | theorem | true | no | no |
| 2 | `map_klLimit_eq_gaussianReal` | theorem | true | no | no (the `toNNReal` argument is ≥ 0) |
| 3 | `integral_klLimit_mul` | theorem | true | no | no |
| 4 | `klLimitDiffusivity_moment` | theorem | true | no | no (rpow of a positive base) |
| 5 | `tendsto_integral_abs_klDiffusivity_rpow_sub` | theorem | true | no | no |
| 6 | `map_sum_klLimit_eq_gaussianReal` | theorem | true | no | no (the `toNNReal` argument is ≥ 0) |
| 7 | `isGaussian_map_klLimit` | theorem | true | no | no |
| 8 | `klLimitDiffusivity_unbounded` | theorem | true | no | no |
| 9 | `klLimit_ae_eq_L2_limit` | theorem | true | no | no |

## Main points for a human auditor

- **All 9 theorems are true, none is vacuous, and none depends on a junk value.** They state the
  standard pointwise and $L^2(\Omega\times D)$ facts about a Gaussian Karhunen–Loève series and its
  lognormal exponential.
- `klLimit` is `limUnder atTop` of the partial sums. Where the series diverges its value is an
  arbitrary `Classical.epsilon` value. Every theorem talks about `klLimit` only almost surely or
  through its law, so this junk value never matters. Theorems 1 and 9 also prove that the partial
  sums converge almost surely to `klLimit`.
- Hypotheses. `hθ : ∀ n, 0 ≤ θ n` is needed, because `Real.sqrt` sends negative numbers to 0.
  Without it the variance formulas would contain negative $\theta_n$. Summability of
  $\sum_n\theta_n f_n(x)^2$ is exactly the condition (necessary and sufficient) for a series of
  independent centred Gaussians to converge almost surely. The `HasSum … (R x y)` hypotheses only
  give the name $R(x,y)$ to the covariance sum. In theorem 3 the summability part of `hxy` already
  follows from `hx` and `hy` (since $|ab|\le(a^2+b^2)/2$), so it is redundant but harmless.
- `toNNReal` (theorems 2 and 6) never clamps, because $R(x,x)=\sum\theta_n f_n(x)^2\ge0$ and
  $\sum_{ij}a_ia_jR(x_i,x_j)=\sum_n\theta_n(\sum_ia_if_n(x_i))^2\ge0$.
- In theorem 7, `IsGaussian` also asserts implicitly that the vector map is a.e.-measurable. If it
  were not, the image measure would be $0$, which is not Gaussian.
- In theorem 9, $\nu$ only has to be s-finite (it need not be finite), and $f_n$ only has to be
  a.e.-strongly measurable through `MemLp`. The statement is still true: replace each $f_n$ by a
  measurable version and use Tonelli. The last conjunct identifies `klLimit` with the
  $L^2(\mathbb P\otimes\nu)$-limit of the partial sums (uniqueness of $L^2$ limits).

## Per-declaration sections

Notation: $\mathbb P$ = `stdNormalSeq` = $\bigotimes_{n\in\mathbb N}N(0,1)$ on $\mathbb R^{\mathbb N}$,
i.e. $z=(z_n)$ are i.i.d. standard normals. For $K\in\mathbb N$,
$Y_K(z,x)$ = `klField θ f K z x` $=\sum_{n<K}\sqrt{\theta_n}\,z_n\,f_n(x)$ (where
$\sqrt{\cdot}$ is `Real.sqrt`, so $\sqrt{t}=0$ for $t<0$). `klDiffusivity θ f K z x` $=e^{Y_K(z,x)}$.

### D1. `klLimit`

**Rendering.** $Y(z,x)$ = `limUnder atTop (K ↦ Y_K(z,x))`. This is the limit of the partial sums
when it exists (unique, since $\mathbb R$ is Hausdorff). Otherwise it is an unspecified real
(`Classical.epsilon`).

**Assessment.** This is a definition. It is the random field of the full KL expansion
$\sum_{n}\sqrt{\theta_n}z_nf_n(x)$.

### D2. `klLimitDiffusivity`

**Rendering.** $a(z,x)=\exp(Y(z,x))$. This is the lognormal diffusion coefficient.

**Assessment.** This is a definition.

### 1. `klLimit_tendsto`

**Rendering.** Let $D$ be a type, $\theta:\mathbb N\to\mathbb R$ with $\theta_n\ge0$ for all $n$,
$f:\mathbb N\to D\to\mathbb R$, $x\in D$, and suppose $\sum_n\theta_nf_n(x)^2$ is summable. Then:
(i) for $\mathbb P$-a.e. $z$, $Y_K(z,x)\to Y(z,x)$ as $K\to\infty$;
(ii) $z\mapsto Y(z,x)\in L^2(\mathbb P)$;
(iii) for every $K$, $(Y(\cdot,x)-Y_K(\cdot,x))^2$ is integrable and
$\mathbb E[(Y-Y_K)^2]=\sum_{n\ge0}\theta_{n+K}f_{n+K}(x)^2$;
(iv) $\mathbb E[(Y-Y_K)^2]\to0$.

**Assessment.** True. The terms $\sqrt{\theta_n}f_n(x)z_n$ are independent and centred, with
summable variances $\theta_nf_n(x)^2$. By Kolmogorov's one-series theorem (or $L^2$-bounded
martingale convergence) the series converges a.s. and in $L^2$. The a.s. limit is the `limUnder`
value. The tail $\sum_{n\ge K}$ has variance $\sum_{n\ge K}\theta_nf_n(x)^2$, which is the shifted
`tsum` and tends to 0. A Monte Carlo check of (iii) ($\theta_n=2^{-n}$, $f_n=\cos(nx)$, $x=0.7$)
agrees with the formula (`r43_checks.out`). Not vacuous: e.g. $D=\mathrm{Unit}$, $\theta_n=2^{-n}$,
$f_n\equiv1$. There is no junk dependence: the integrals are of integrable functions and the
`tsum` is summable. `hθ` is needed (see main points). This is the a.s./mean-square convergence of
a Gaussian series, i.e. pointwise convergence of the KL expansion.

### 2. `map_klLimit_eq_gaussianReal`

**Rendering.** Assume $\theta_n\ge0$ and $\sum_n\theta_nf_n(x)f_n(x)=R(x,x)$ (as a `HasSum`). Then
the law of $z\mapsto Y(z,x)$ under $\mathbb P$ is $N(0,\max(R(x,x),0))$. If $R(x,x)=0$ this law is
the Dirac mass at 0.

**Assessment.** True. Each $Y_K$ is $N(0,\sum_{n<K}\theta_nf_n(x)^2)$, and $Y_K\to Y$ a.s., so the
characteristic functions converge to $\exp(-R t^2/2)$. Here $R(x,x)\ge0$, so `toNNReal` does not
clamp. In the degenerate case every term vanishes, so $Y\equiv0$ and the law is $\delta_0$, as
stated. Not vacuous: $\theta_0=1$, $f_0\equiv1$, all other terms 0, $R=1$. There is no junk
dependence. This is the fact that the limit of a Gaussian series is Gaussian with the limiting
variance.

### 3. `integral_klLimit_mul`

**Rendering.** Assume $\theta\ge0$, that $\sum_n\theta_nf_n(x)^2$ and $\sum_n\theta_nf_n(y)^2$ are
summable, and that $\sum_n\theta_nf_n(x)f_n(y)=R(x,y)$. Then $Y(\cdot,x)$ and $Y(\cdot,y)$ are in
$L^2(\mathbb P)$, their product is integrable, and $\mathbb E[Y(\cdot,x)Y(\cdot,y)]=R(x,y)$.

**Assessment.** True. Theorem 1 gives $L^2$ convergence at $x$ and at $y$, and the $L^2$ inner
product is continuous, so
$\mathbb E[Y_K(x)Y_K(y)]=\sum_{n<K}\theta_nf_n(x)f_n(y)\to R(x,y)$. The summability in `hxy` is
implied by `hx` and `hy`, so `hxy` only names the value. Not vacuous: as in theorem 2 with $y=x$.
There is no junk dependence. This is the covariance identity $\mathrm{Cov}(Y(x),Y(y))=R(x,y)$ for
the KL field (Mercer kernel).

### 4. `klLimitDiffusivity_moment`

**Rendering.** Assume $\theta\ge0$ and $\sum_n\theta_nf_n(x)^2=R(x,x)$. Then for every real $p$,
$z\mapsto a(z,x)^p$ (`Real.rpow`) is $\mathbb P$-integrable and
$\mathbb E[a(\cdot,x)^p]=\exp(p^2R(x,x)/2)$.

**Assessment.** True. Since $a=e^{Y}>0$, we have $a^p=e^{pY}$, and $Y\sim N(0,R)$ by theorem 2. The
Gaussian moment generating function gives $e^{p^2R/2}$. Quadrature agrees for
$R\in\{0.3,1,2.5\}$, $p\in\{-2,-0.5,0,0.7,3\}$ (`r43_checks.out`). Not vacuous. There is no junk
dependence: the base is positive, so rpow is genuine. This is the moment formula of the lognormal
distribution.

### 5. `tendsto_integral_abs_klDiffusivity_rpow_sub`

**Rendering.** Assume $\theta\ge0$ and that $\sum_n\theta_nf_n(x)^2$ is summable. Fix $p\in\mathbb R$.
Then:
(i) for every $K$, $e^{pY_K(\cdot,x)}$ is integrable;
(ii) $e^{pY(\cdot,x)}$ is integrable;
(iii) for every $K$, $|e^{pY_K}-e^{pY}|$ is integrable;
(iv) $\mathbb E|e^{pY_K}-e^{pY}|\to0$ as $K\to\infty$;
(v) $\mathbb E[e^{pY_K}]\to\mathbb E[e^{pY}]$.
(Here $(e^{Y})^p$ is written with rpow; it equals $e^{pY}$.)

**Assessment.** True. $Y=Y_K+T_K$ with $T_K$ independent of $Y_K$, so
$\mathbb E|e^{pY_K}-e^{pY}|=\mathbb E e^{pY_K}\cdot\mathbb E|1-e^{pT_K}|$. The first factor is at
most $e^{p^2R/2}$ and the second tends to 0 because $\mathrm{Var}\,T_K\to0$ (alternatively, use
Vitali with uniform integrability). The numerical $L^1$ distances decrease to 0
(`r43_checks.out`). (v) follows from (iv). Not vacuous. There is no junk dependence. This is $L^1$
convergence of the truncated lognormal coefficient: the truncation error of KL in the coefficient
$a$.

### 6. `map_sum_klLimit_eq_gaussianReal`

**Rendering.** Let $\iota$ be a finite type, $x:\iota\to D$, $a:\iota\to\mathbb R$, $\theta\ge0$,
and suppose $\sum_n\theta_nf_n(x_i)f_n(x_j)=R(x_i,x_j)$ for all $i,j$. Then the law of
$z\mapsto\sum_ia_iY(z,x_i)$ is $N\bigl(0,\max(\sum_{i,j}a_ia_jR(x_i,x_j),0)\bigr)$.

**Assessment.** True. The linear combination is the a.s. limit of
$\sum_{n<K}\sqrt{\theta_n}z_n\sum_ia_if_n(x_i)$, a Gaussian series with variances
$\theta_n(\sum_ia_if_n(x_i))^2$ summing to $\sum_{ij}a_ia_jR(x_i,x_j)\ge0$, so `toNNReal` does not
clamp. The diagonal case $i=j$ of `hR` gives summability at every $x_i$. If $\iota$ is empty, both
sides are $\delta_0$. Not vacuous. There is no junk dependence. These are the finite-dimensional
Gaussian marginals of the KL field (Cramér–Wold form).

### 7. `isGaussian_map_klLimit`

**Rendering.** Under the same hypotheses as theorem 6 (without $a$), let
$\mu$ = law of $z\mapsto(Y(z,x_k))_{k\in\iota}$ on $\mathbb R^\iota$. Then:
(i) $\mu$ is a Gaussian measure (Mathlib `IsGaussian`: every continuous linear functional pushes
$\mu$ forward to `gaussianReal` with its mean and variance; this includes being a probability
measure);
(ii) each coordinate $v\mapsto v_i$ is in $L^2(\mu)$;
(iii) $\int v_i\,d\mu=0$;
(iv) $\int v_iv_j\,d\mu=R(x_i,x_j)$.

**Assessment.** True. A continuous linear functional on $\mathbb R^\iota$ is
$v\mapsto\sum a_iv_i$, so (i) follows from theorem 6 together with identifying the mean (0) and the
variance. (ii)–(iv) follow from theorem 3 and the zero mean. The map is a.e.-measurable (it is the
a.e. limit of measurable maps), so $\mu$ is a probability measure. Not vacuous. There is no junk
dependence. This says the KL field is a centred Gaussian process with covariance $R$.

### 8. `klLimitDiffusivity_unbounded`

**Rendering.** Assume $\theta\ge0$, $\sum_n\theta_nf_n(x)^2=R(x,x)$ and $R(x,x)>0$. Then for every
real $M$, $\mathbb P(a(\cdot,x)>M)>0$ and $\mathbb P(a(\cdot,x)^{-1}>M)>0$.

**Assessment.** True. $Y\sim N(0,R)$ with $R>0$ has full support, so
$\mathbb P(Y>\log M)>0$ (the event is the whole space a.s. if $M\le0$), and similarly for $-Y$.
Example: the probability is about $6\times10^{-4148}>0$ for $R=0.01$, $M=10^6$. `hpos` is needed:
for $R=0$, $a\equiv1$. Not vacuous: $\theta_0=1$, $f_0\equiv1$. There is no junk dependence. This
says the lognormal coefficient is neither uniformly bounded nor uniformly bounded away from 0, so
the PDE is not uniformly elliptic.

### 9. `klLimit_ae_eq_L2_limit`

**Rendering.** Let $(D,\nu)$ be a measurable space with an s-finite measure. Assume
$\theta_n\ge0$, $\sum_n\theta_n<\infty$, each $f_n\in L^2(\nu)$, and
$\int f_nf_m\,d\nu=\delta_{nm}$ (orthonormal). Then, with $\mathbb P\otimes\nu$ on
$\mathbb R^{\mathbb N}\times D$:
(i) for $\nu$-a.e. $x$, $\sum_n\theta_nf_n(x)^2$ is summable;
(ii) for $(\mathbb P\otimes\nu)$-a.e. $(z,x)$, $Y_K(z,x)\to Y(z,x)$;
(iii) $Y\in L^2(\mathbb P\otimes\nu)$;
(iv) for every $K$, $(Y-Y_K)^2$ is $(\mathbb P\otimes\nu)$-integrable and its integral is
$\sum_{n\ge0}\theta_{n+K}$;
(v) for every $Y'\in L^2(\mathbb P\otimes\nu)$ with $\int(Y'-Y_K)^2\,d(\mathbb P\otimes\nu)\to0$,
$Y'=Y$ $(\mathbb P\otimes\nu)$-a.e.

**Assessment.** True.
(i) By Tonelli, $\int\sum_n\theta_nf_n^2\,d\nu=\sum_n\theta_n<\infty$.
(ii) Take measurable versions $\tilde f_n$. The exceptional $x$-set is $\nu$-null, and its product
with $\mathbb R^{\mathbb N}$ is null. For the measurable bad set, Tonelli (which needs s-finiteness)
and theorem 1 at $\nu$-a.e. $x$ give measure 0.
(iii), (iv) $\iint(Y-Y_K)^2=\int\sum_{n\ge K}\theta_nf_n(x)^2\,d\nu=\sum_{n\ge K}\theta_n$ by
orthonormality.
(v) Uniqueness of $L^2$ limits, using (iv) $\to0$. The integrals in the hypothesis of (v) are of
integrable functions ($Y'$ and $Y_K$ are in $L^2$), so they are not junk.
The example $D=[0,1]$, $f_n=\sqrt2\sin((n+1)\pi x)$, $\theta_n=(n+1)^{-2}$ confirms orthonormality
and $\int\sum_{n\ge K}\theta_nf_n^2=\sum_{n\ge K}\theta_n$ numerically (`r43_checks.out`). Not
vacuous: e.g. $D=\mathbb N$ with counting measure and $f_n=\mathbf 1_{\{n\}}$, $\theta_n=2^{-n}$.
The hypotheses are standard (trace class covariance, orthonormal eigenfunctions). Only
s-finiteness is assumed, not a finite measure, which makes the statement more general. This is the
mean-square convergence of the KL expansion in $L^2(\Omega\times D)$, with error equal to the
eigenvalue tail $\sum_{n\ge K}\theta_n$, and the identification of the pointwise limit with the
$L^2$ limit.

### Appended definitions (rendered for completeness)

- `stdNormalSeq` $=\bigotimes_{n\in\mathbb N}N(0,1)$ (`Measure.infinitePi`).
- `klField θ f K z x` $=\sum_{n<K}\sqrt{\theta_n}\,z_n\,f_n(x)$ (`Real.sqrt`).
- `klDiffusivity θ f K z x` $=\exp(\texttt{klField}\ \theta\ f\ K\ z\ x)$.
