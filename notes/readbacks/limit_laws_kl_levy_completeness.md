# Blind read-back report: R52_limits

| field | value |
|---|---|
| date | 2026-10-09 |
| packet | `readback/round27/packet_R52_limits.lean` |
| declarations audited | 20 (19 theorems + 1 definition `posHalfStep`) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round27/work_R52_limits/` (`levy_checks.py/.out`, `l2_symbolic.py/.out`, `kl_checks.py/.out`, `halfstep_checks.py/.out`, `scratch1.lean/.out`, `scratch2.lean/.out`, `complete_instance.lean/.out`) |

The scratch copy of the packet (proofs still `sorry`, plus `import MlmcLean`) compiles. I used `#print` to see how
`MLMC.stdNormalSeq` is defined, because the packet uses it but does not list it among the appended definitions. It is
`@[reducible] def stdNormalSeq : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1`. I read no
repository source.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `posSemidef_klCov` | theorem | true | no | no |
| 2 | `map_klLimit_eq_multivariateGaussian` | theorem | true | no | no (the `limUnder` junk sits on a null set; the matrix is PSD, so the `multivariateGaussian` fallback to a Dirac is not used) |
| 3 | `map_klLimit_pi_eq_multivariateGaussian` | theorem | true | no | no |
| 4 | `klLimit_multivariateGaussian_satisfiable` | theorem | true | no (it is itself a witness) | no |
| 5 | `posHalfStep` | def | n/a ($x\mapsto x/2$ on $(0,\infty)$, ignores the noise) | n/a | n/a |
| 6 | `posHalfStep_contracting` | theorem | true (with equality) | no | no |
| 7 | `lintegral_posHalfStep_ne_top` | theorem | true (trivial; holds for every real $p$) | no | no |
| 8 | `coe_fwdIter_posHalfStep` | theorem | true | no | no |
| 9 | `map_fwdIter_posHalfStep` | theorem | true | no | no |
| 10 | `posHalfStep_no_weak_limit` | theorem | true | no (the hypothesis `hP` cannot hold when $\mu(\Omega)\ne1$, but every probability $\mu$ is covered) | no |
| 11 | `not_tendstoInDistribution_fwdIter_posHalfStep` | theorem | true | no | no (the claim is for every $X$, measurable ones included) |
| 12 | `not_completeSpace_Ioi_zero` | theorem | true | no | no |
| 13 | `completeSpace_cannot_be_dropped` | theorem | true; the negation is not cheap | no | no |
| 14 | `integrable_levyKhintchine` | theorem | true | no | no |
| 15 | `charFun_bandApprox` | theorem | true | no | no |
| 16 | `levy_limit_charFun` | theorem | true | no | no (`hX0` makes every L² integral genuine) |
| 17 | `levy_truncation_limit_charFun` | theorem | true | no | no |
| 18 | `levy_limit_map_eq` | theorem | true | no | no |
| 19 | `exists_unique_levyKhintchine_law` | theorem | true | no | no |
| 20 | `stableLike_limit_charFun` | theorem | true | no | no |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.**
2. **`stdNormalSeq` is not in the packet's appendix of definitions.** `#print` shows it is
   $\bigotimes_{n\in\mathbb N}N(0,1)$ (`Measure.infinitePi fun _ => gaussianReal 0 1`). With that definition the
   Karhunen–Loève (KL) statements are the standard ones.
3. **`klLimit` uses `limUnder`.** Where the partial sums $\sum_{n<K}\sqrt{\theta_n}z_nf_n(x)$ do not converge,
   `limUnder` returns a fixed `Classical.choice` constant. The set where that happens is null: Kolmogorov's
   theorem applies because $\sum_n\theta_nf_n(x)^2=R(x,x)<\infty$ comes from `hR i i`. So the law is not affected.
   The covariance matrix is PSD (theorem 1), so the fallback `multivariateGaussian μ S = dirac μ` for a non-PSD $S$
   never applies.
4. **`completeSpace_cannot_be_dropped` is a genuine negation.**
   - With `[CompleteSpace α]` added, the universal statement is true. It is the Diaconis–Freedman / Wu–Shao
     iterated-random-functions theorem: the backward iterates converge a.s. on the same $\Omega$, and their limit
     serves as $X$.
   - The witness for the negation is the deterministic halving chain on $(0,\infty)$: its mass escapes to the
     missing point $0$.
   - I checked in Lean (`complete_instance.lean`, compiles without `sorry`) that the same chain on the complete space
     $\mathbb R$ satisfies every hypothesis and the conclusion, with $X\equiv0$.
   - No hypothesis is unsatisfiable or mis-typed. $\nu$ is forced to be the law of $\xi_i$, `TendstoInDistribution`'s
     AE-measurability fields are met because $\varphi$ is jointly measurable, and $X$ is required on the same
     $\Omega$, which is fine because of the backward-iteration limit.
5. **`hδ1 : δ 0 ≤ 1`.**
   - It is superfluous in `levy_limit_charFun` and `levy_limit_map_eq`. It is harmless there, and only makes those
     statements slightly weaker.
   - It is necessary in `levy_truncation_limit_charFun` for the exact L² identity. Counterexample without it:
     $\nu=\delta_{3/2}$ and $\delta=(2,\tfrac12,\tfrac14,\dots)$. At $\ell=0$ the left side is
     $\tfrac94(T+T^2)$ and the right side is $\tfrac94T$ (`l2_symbolic.out`).
6. **Junk values in the L² hypotheses are ruled out.** The Bochner integrals in `hXlim` and `hX0` are genuine:
   `hX0` and the bounded bands $k\ge1$ make $X-\texttt{bandApprox}\,\ell\in L^2$ for every $\ell$. In
   `stableLike_limit_charFun` the conclusion has no `MemLp`, but nothing is lost. For $T>0$ the stated integral is
   positive, which forces integrability. In every case the `charFun` conclusion forces $X$ to be AE-measurable,
   because `Measure.map` of a non-AE-measurable map is $0$, whose characteristic function is $0\neq e^{(\cdot)}$.
7. **Minor generality notes.**
   - $\nu$ may carry an atom at $0$, even an infinite one. This is harmless, because every integrand vanishes at
     $z=0$ and the bands exclude $0$.
   - `stableLike_limit_charFun` allows every $Y<2$, including $Y\le0$, where $\nu$ is finite rather than
     "stable-like". The statement is still true.
   - `lintegral_posHalfStep_ne_top` holds for every real $p$.

---

## Per-declaration sections

Shared notation for the Lévy part:
- $\Omega_\star=(\mathbb N\times\mathbb R^{\mathbb N})^{\mathbb N}$ and
  $\mathbb P=\texttt{bandInputLaw}\,\Lambda\,M=\bigotimes_k\big(\mathrm{Po}(\Lambda_k)\otimes M_k^{\otimes\mathbb N}\big)$.
- $\omega_k=(N_k,(Y_{k,i})_i)$.
- Bands: $B_0=\{|z|\ge\delta_0\}$ and $B_{k+1}=\{\delta_{k+1}\le|z|<\delta_k\}$.
- $\texttt{cpSum}\,g\,(N,Y)=\sum_{i<N}g(Y_i)$.
- $\texttt{levyComp}(\delta)=T\int_{\delta\le|z|<1}z\,d\nu$.
- $S_\ell=\texttt{bandApprox}\,\nu\,T\,\delta\,\ell=\sum_{k\le\ell}\sum_{i<N_k}\mathbf 1_{B_k}(Y_{k,i})Y_{k,i}-\texttt{levyComp}(\delta_\ell)$.
- $g_t(z)=e^{itz}-1-itz\mathbf 1_{|z|<1}$.
- In `T * ∫ …` the factor $T:\mathbb R_{\ge0}$ is cast as $\mathbb R_{\ge0}\to\mathbb R\to\mathbb C$ (`↑↑T`, confirmed by
  elaboration).
- `charFun μ t` $=\int e^{itx}\,d\mu$ (Mathlib `charFun_apply_real`).

### 1. `posSemidef_klCov`

**Rendering.** Hypotheses:
- $\iota$ is finite, $\theta_n\ge0$, $f_n:D\to\mathbb R$ and $R:D\times D\to\mathbb R$.
- $x:\iota\to D$ is a family of points.
- For all $i,j$: $\sum_n\theta_nf_n(x_i)f_n(x_j)=R(x_i,x_j)$, as an unconditional `HasSum` in $\mathbb R$.

Then the matrix $(R(x_i,x_j))_{i,j}$ is positive semidefinite: Hermitian (symmetric), and
$\sum_{i,j}v_iv_jR_{ij}\ge0$ for every finitely supported $v$ (Mathlib's `Finsupp` form).

**Assessment.**
- **Truth:** true. Symmetry follows from uniqueness of `HasSum` limits and commutativity of the product.
  Positivity: $\sum_{ij}v_iv_jR_{ij}=\sum_n\theta_n(\sum_iv_if_n(x_i))^2\ge0$, a finite linear combination of
  `HasSum`s.
- **Vacuity:** not vacuous; take theorem 4's instance. Numerically (`kl_checks.out`), a Brownian-bridge KL with a
  repeated point gives eigenvalues $\approx(0,0.67,1.29,4.99)\ge0$.
- **Junk:** none.
- **Standard fact:** a covariance kernel given by a Mercer/KL series is positive semidefinite (Gram matrices of
  $\ell^2$ feature maps).

### 2. `map_klLimit_eq_multivariateGaussian`

**Rendering.** Same hypotheses as theorem 1, plus `DecidableEq ι`. Let $z\sim\bigotimes_nN(0,1)$ (`stdNormalSeq`).
Define $\texttt{klLimit}(z,x)=\lim_{K\to\infty}\sum_{n<K}\sqrt{\theta_n}z_nf_n(x)$; `limUnder` gives a fixed
arbitrary constant when there is no limit. Then the law of the vector
$(\texttt{klLimit}(z,x_k))_{k\in\iota}\in$ `EuclideanSpace ℝ ι` is the centred multivariate Gaussian with covariance
matrix $(R(x_i,x_j))_{ij}$.

**Assessment.**
- **Truth:** true.
  - The diagonal hypothesis gives $\sum_n\theta_nf_n(x)^2<\infty$, so each coordinate series of independent centred
    Gaussians converges a.s. (Kolmogorov two-series / $L^2$ martingale). Off the null set, `klLimit` equals the true
    limit.
  - The characteristic functions of the partial-sum vectors are $\exp(-\tfrac12v^\top S_Kv)$, which converge to
    $\exp(-\tfrac12v^\top Rv)$.
  - $R$ is PSD (theorem 1), so Mathlib's `multivariateGaussian 0 R` really has covariance $R$, and its non-PSD
    Dirac fallback does not apply.
  - `klLimit` is measurable: it is the limit on the measurable convergence set and constant elsewhere. So
    `Measure.map` is not the junk $0$.
- **Vacuity:** not vacuous; see theorem 4.
- **Junk:** the `limUnder` junk lives on a null set, so the conclusion does not depend on it.
- **Standard fact:** finite-dimensional distributions of a Karhunen–Loève (Gaussian series) field are Gaussian with
  the series covariance (Itô–Nisio / Kolmogorov).

### 3. `map_klLimit_pi_eq_multivariateGaussian`

**Rendering.** Same as theorem 2, but the vector is taken in $\iota\to\mathbb R$ (product space). Its law equals the
push-forward of `multivariateGaussian 0 R` under `WithLp.ofLp`.

**Assessment.**
- **Truth:** true. It is theorem 2 composed with the measurable equivalence `ofLp` (functoriality of
  `Measure.map`).
- **Vacuity:** not vacuous.
- **Junk:** none.
- **Standard fact:** the same fact as theorem 2, stated on the plain product space.

### 4. `klLimit_multivariateGaussian_satisfiable`

**Rendering.** There is $f:\mathbb N\to\mathbb N\to\mathbb R$ (so $D=\mathbb N$), chosen before $\theta$, such that for
every $\theta\ge0$ and every finite family $x:\iota\to\mathbb N$:
- (a) $\sum_n\theta_nf_n(x_i)f_n(x_j)=\theta_{x_i}\mathbf 1[x_i=x_j]$, as a `HasSum`;
- (b) the law of $(\texttt{klLimit}(z,x_k))_k$ is $N\big(0,(\mathbf 1[x_i=x_j]\theta_{x_i})_{ij}\big)$.

**Assessment.**
- **Truth:** true with $f_n(m)=\mathbf 1[n=m]$. The partial sums are eventually constant and equal to
  $\sqrt{\theta_m}z_m$, so the vector is $(\sqrt{\theta_{x_k}}z_{x_k})_k$, which is Gaussian with exactly that
  covariance.
- **Vacuity:** not vacuous. This is the non-vacuity witness for theorems 1–3, and `kl_checks.out` checks the
  identity in (a).
- **Junk:** none.
- **Standard fact:** independent Gaussian coordinates (white noise on $\mathbb N$) as a degenerate KL expansion.

### 5. `posHalfStep` (definition)

**Rendering.** For any noise type $E$: $\texttt{posHalfStep}(x,e)=x/2\in(0,\infty)$ for $x\in(0,\infty)$. The noise
$e$ is ignored, and the proof term certifies $x/2>0$.

**Assessment.** A faithful definition. Its iterates are $x_0/2^n$ (theorem 8).

### 6. `posHalfStep_contracting`

**Rendering.** Let $\nu$ be a probability measure on $E$ and $p>0$ real. Then:
- $0\le2^{-p}<1$ (real `rpow`);
- for all $x,y\in(0,\infty)$: $\int^-\mathrm{ofReal}(|x/2-y/2|^p)\,d\nu\le\mathrm{ofReal}(2^{-p})\cdot\mathrm{ofReal}(|x-y|^p)$.

**Assessment.**
- **Truth:** true, with equality: $|x/2-y/2|^p=2^{-p}|x-y|^p$, $\nu(E)=1$, and `ofReal` is multiplicative on
  nonnegative numbers. See `halfstep_checks.out`.
- **Vacuity:** not vacuous (for example $\nu=\delta_e$).
- **Junk:** none; every base is positive or $0$ with $p>0$.
- **Standard fact:** the average-contraction ("geometric moment contraction") condition for the chain.

### 7. `lintegral_posHalfStep_ne_top`

**Rendering.** For a probability $\nu$, $x_0>0$ and any real $p$:
$\int^-\mathrm{ofReal}(|x_0-x_0/2|^p)\,d\nu<\infty$.

**Assessment.**
- **Truth:** true and trivial. The integrand is the constant $\mathrm{ofReal}((x_0/2)^p)$, which is finite because
  the base is positive. No condition on $p$ is needed.
- **Vacuity:** not vacuous.
- **Junk:** none.
- **Standard fact:** the finite first-step moment hypothesis of the iterated-random-function theorem.

### 8. `coe_fwdIter_posHalfStep`

**Rendering.** $\texttt{fwdIter}$ is defined by $x_0\mapsto x_0$ and $x_{n+1}=\varphi(x_n,e_n)$. For every $n$, noise
sequence $e$ and $x_0$: the real value of the $n$-th forward iterate of `posHalfStep` is $x_0/2^n$, with a natural
number power.

**Assessment.**
- **Truth:** true, by induction on $n$.
- **Vacuity:** not vacuous.
- **Junk:** none.
- **Standard fact:** the closed form of the halving recursion.

### 9. `map_fwdIter_posHalfStep`

**Rendering.** Let $\mu$ be a probability measure, $\xi_k:\Omega\to E$ arbitrary (not even assumed measurable),
$x_0>0$, $n\in\mathbb N$ and $e$ any sequence. Then the law of $\omega\mapsto x_n(\xi(\omega))$ is
$\delta_{x_n(e)}$.

**Assessment.**
- **Truth:** true. The map is constant (it is $x_0/2^n$ whatever the noise), and
  `Measure.map_const` gives $\mu(\Omega)\,\delta=\delta$.
- **Vacuity:** not vacuous.
- **Junk:** none; a constant map is measurable, so `map` is not the junk $0$.
- **Standard fact:** the push-forward of a probability measure under a constant map.

### 10. `posHalfStep_no_weak_limit`

**Rendering.** This declaration omits `[IsProbabilityMeasure μ]`, so $\mu$ is any measure. Take any $\xi$, any $x_0>0$,
any probability measure $\pi$ on $(0,\infty)$, and probability measures $P_n$ on $(0,\infty)$ with
$P_n=\mu\circ(\omega\mapsto x_n)^{-1}$. Then $P_n\not\to\pi$ in the weak topology of `ProbabilityMeasure (Ioi 0)`.

**Assessment.**
- **Truth:** true.
  - `hP` forces $\mu(\Omega)\,\delta_{x_0/2^n}=P_n$, hence $\mu(\Omega)=1$ and $P_n=\delta_{x_0/2^n}$. For other
    $\mu$ the hypothesis is unsatisfiable, so the statement is vacuous for them.
  - Suppose $P_n\to\pi$. For the bounded continuous function $g_\varepsilon(x)=\min(1,x/\varepsilon)$ on
    $(0,\infty)$ we have $g_\varepsilon(x_0/2^n)\to0$, so $\int g_\varepsilon\,d\pi=0$ for every $\varepsilon>0$.
  - Letting $\varepsilon\downarrow0$, monotone convergence gives $\pi((0,\infty))=0$, which is a contradiction. See
    `halfstep_checks.out`.
- **Vacuity:** not vacuous; any probability $\mu$ with $P_n:=\delta_{x_0/2^n}$ works.
- **Junk:** none.
- **Standard fact:** mass escaping to a missing boundary point destroys tightness, so there is no weak limit in a
  non-complete space.

### 11. `not_tendstoInDistribution_fwdIter_posHalfStep`

**Rendering.** Let $\mu$ be a probability measure. For every probability space $(\Omega',\mu')$ and every
$X:\Omega'\to(0,\infty)$, the forward iterates $x_n(\xi(\cdot))$ do **not** converge in distribution to $X$, in
Mathlib's `TendstoInDistribution` sense: AE-measurability of each $X_n$ and of $X$, plus weak convergence of the laws.

**Assessment.**
- **Truth:** true. Each $X_n$ is constant, hence measurable. If $X$ were AE-measurable with laws converging, then
  $\mu'\circ X^{-1}$ would be a weak limit, which theorem 10 rules out. If $X$ is not AE-measurable the structure
  fails trivially. The universal quantifier over $X$ includes measurable $X$, so the content is not cheap.
- **Vacuity:** not vacuous.
- **Junk:** no reliance on junk.
- **Standard fact:** the same fact as theorem 10, in random-variable language.

### 12. `not_completeSpace_Ioi_zero`

**Rendering.** $(0,\infty)$ with the subspace metric is not complete.

**Assessment.**
- **Truth:** true. $1/n$ is Cauchy and has no limit in the set; equivalently, $(0,\infty)$ is not closed in
  $\mathbb R$.
- **Vacuity:** not applicable (no hypotheses).
- **Junk:** none.
- **Standard fact:** a subspace of a complete space is complete iff it is closed.

### 13. `completeSpace_cannot_be_dropped`

**Rendering.** The theorem asserts the negation of the following universal statement.

For every $\alpha:\texttt{Type}$ that is a metric space with Borel $\sigma$-algebra and second countable (no
completeness), every probability space $(\Omega,\mu)$ with $\Omega:\texttt{Type}$, every measure $\nu$ on
$\mathbb R$, every jointly measurable $\varphi:\alpha\times\mathbb R\to\alpha$ and every $\xi:\mathbb N\to\Omega\to\mathbb R$,
**if** all of the following hold:
- reals $p>0$ and $0\le\rho<1$;
- $\int^-d(\varphi(x,e),\varphi(y,e))^p\,\nu(de)\le\rho\,d(x,y)^p$ for all $x,y$;
- the $\xi_i$ are mutually independent, measurable, and each has law $\nu$;
- $x_0\in\alpha$ satisfies $\int^-d(x_0,\varphi(x_0,e))^p\,\nu(de)<\infty$;

**then** there is $X:\Omega\to\alpha$ such that the forward iterates $x_n=\varphi(\cdot,\xi_{n-1})\circ\dots\circ\varphi(\cdot,\xi_0)(x_0)$
converge in distribution to $X$.

The negation says that some instance satisfies all the hypotheses and admits no such $X$.

**Assessment.**
- **Truth:** true. Witness: $\alpha=(0,\infty)$, $\varphi=$ `posHalfStep`, $p=1$, $\rho=\tfrac12$, any probability
  space carrying i.i.d. $\xi$ with law $\nu$ (for example $\Omega=$ `Unit` or $\mathbb R^{\mathbb N}$), and
  $x_0=1$. The hypotheses hold by theorems 6 and 7 and joint continuity. The conclusion fails by theorem 11.
- **The negation is not cheap.**
  - With `[CompleteSpace α]` added, the universal statement is a true theorem.
  - The backward iterates $B_n=\varphi_{\xi_0}\circ\dots\circ\varphi_{\xi_{n-1}}(x_0)$ satisfy
    $\mathbb E\,d(B_{n+1},B_n)^p\le\rho^nC$. This uses independence, Fubini and the average contraction.
  - Hence $\sum_n d(B_{n+1},B_n)<\infty$ a.s. For $p\ge1$ this follows from Minkowski. For $p<1$, use that
    $\sum a_n^p<\infty$ implies $\sum a_n<\infty$.
  - So $B_n\to B_\infty$ a.s. on the same $\Omega$, by completeness. $B_\infty$ is AE-measurable and serves as
    $X$.
  - Finally $\mathrm{Law}(x_n)=\mathrm{Law}(B_n)$, because $(\xi_0,\dots,\xi_{n-1})$ is exchangeable.
  - Nothing in the hypotheses is unsatisfiable or junk. $\nu$ is forced to be a probability measure by
    `μ.map (ξ i) = ν`. The AE-measurability fields of `TendstoInDistribution` hold because $\varphi$ is jointly
    measurable. The same-$\Omega$ requirement on $X$ is met by $B_\infty$.
  - Lean check, `complete_instance.lean` (compiles, no `sorry`): the same halving chain on the complete $\alpha=\mathbb R$
    satisfies every hypothesis and the conclusion, with $\Omega=\mathbb R^{\mathbb N}$,
    $\mu=\delta_0^{\otimes\mathbb N}$, $\xi_i=$ coordinate $i$, $\nu=\delta_0$, $p=1$, $\rho=\tfrac12$, $x_0=1$ and
    $X\equiv0$. So the failure on $(0,\infty)$ is caused precisely by the missing limit point.
- **Vacuity:** not vacuous.
- **Junk:** none.
- **Standard fact:** completeness is needed in the Diaconis–Freedman (1999) / Wu–Shao (2004) convergence theorem for
  iterated random functions.

### 14. `integrable_levyKhintchine`

**Rendering.** Let $\nu$ be any measure on $\mathbb R$ with $\int\min(1,z^2)\,d\nu<\infty$ (stated as `Integrable`;
`z^2` is a natural number power). Then for every real $t$, $g_t(z)=e^{itz}-1-itz\mathbf 1_{|z|<1}$ is
$\nu$-integrable as a $\mathbb C$-valued function.

**Assessment.**
- **Truth:** true. $|g_t(z)|\le\max(2,t^2/2)\min(1,z^2)$, because $|e^{iu}-1-iu|\le u^2/2$ and $|e^{iu}-1|\le2$
  (checked numerically in `levy_checks.out` §5). $g_t$ is measurable.
- **Vacuity:** not vacuous (any Lévy measure, for example `stableLikeLevy`).
- **Junk:** none.
- **Standard fact:** the Lévy–Khintchine integrand is integrable against a Lévy measure.

### 15. `charFun_bandApprox`

**Rendering.** Hypotheses:
- $\nu$ as in theorem 14, $T\in\mathbb R_{\ge0}$;
- $\delta_k>0$ antitone (no $\delta_0\le1$, no limit assumption);
- $\Lambda_k\in\mathbb R_{\ge0}$, and probability measures $M_k$ with $\Lambda_kM_k=T\,\nu|_{B_k}$.

Then for every $\ell$ and $t$: $\mathbb E_{\mathbb P}e^{itS_\ell}=\exp\big(T\int_{|z|\ge\delta_\ell}g_t\,d\nu\big)$.

**Assessment.**
- **Truth:** true.
  - The coordinates $\omega_k$ are independent.
  - Each $\sum_{i<N_k}\mathbf 1_{B_k}(Y_{k,i})Y_{k,i}$ is compound Poisson with characteristic function
    $\exp(\Lambda_k(\int e^{itz\mathbf 1_{B_k}}dM_k-1))=\exp(T\int_{B_k}(e^{itz}-1)d\nu)$. Here $M_k$ is carried by
    $B_k$ when $\Lambda_k>0$; when $\Lambda_k=0$ we have $N_k=0$ a.s.
  - The bands are disjoint, and since $\delta$ is antitone, $\bigcup_{k\le\ell}B_k=\{|z|\ge\delta_\ell\}$.
  - Multiplying by $e^{-it\,\texttt{levyComp}(\delta_\ell)}$ gives the formula. This holds even when
    $\delta_\ell>1$, where both the compensator and the indicator term vanish.
  - $\nu(B_k)<\infty$ by `hν` and $\delta_k>0$, so `hband` is satisfiable.
  - Numerically (`levy_checks.out` §2–3), the Poisson series agrees with the closed form, and the product of band
    characteristic functions times the compensator agrees with the right-hand side to 15 digits.
- **Vacuity:** not vacuous. Example: $\nu=\delta_{1/2}$, $\delta_k=2^{-k}$, $\Lambda_1=T$, $M_1=\delta_{1/2}$, and
  $\Lambda_k=0$, $M_k=\delta_0$ otherwise.
- **Junk:** none. If $S_\ell$ were not measurable, `map` would be $0$ and its characteristic function $0\ne e^{(\cdot)}$.
  The integral over $\{|z|\ge\delta_\ell\}$ is of a bounded function on a finite-measure set.
- **Standard fact:** the characteristic function of a (compensated) compound Poisson variable, i.e. the large-jump
  part of the Lévy–Itô decomposition.

### 16. `levy_limit_charFun`

**Rendering.** Hypotheses:
- those of theorem 15, plus $\delta_0\le1$ and $\delta_k\to0$;
- $X:\Omega_\star\to\mathbb R$ with $X-S_0\in L^2(\mathbb P)$;
- $\mathbb E_{\mathbb P}(X-S_\ell)^2\to0$ as $\ell\to\infty$ (Bochner integrals).

Then for every $t$: $\mathbb E\,e^{itX}=\exp\big(T\int g_t\,d\nu\big)$, the Lévy–Khintchine form with triplet
$(0,0,T\nu)$ and truncation $\mathbf 1_{|z|<1}$.

**Assessment.**
- **Truth:** true.
  - $L^2$ convergence implies convergence in distribution, so the characteristic functions converge.
  - By theorem 15 and dominated convergence (dominating function from theorem 14), together with
    $\{|z|\ge\delta_\ell\}\uparrow\{z\ne0\}$ and $g_t(0)=0$, the limit is $\exp(T\int g_t\,d\nu)$.
  - `levy_checks.out` §4 shows the convergence numerically for the stable-like case.
- **Junk:** the integrals in `hXlim` are genuine.
  - $X-S_\ell=(X-S_0)-\sum_{1\le k\le\ell}(\text{band-}k\text{ sum})+\text{const}$.
  - The band sums for $k\ge1$ have jumps bounded by $\delta_0$, so they are in $L^2$. Hence every
    $(X-S_\ell)^2$ is integrable, and `hX0` prevents the "non-integrable ⇒ integral 0" junk.
  - `hX0` also gives AE-measurability of $X$.
- **Hypotheses:** `hδ1` is not needed here, since $\delta_\ell\le1$ eventually. It is harmless and makes the
  statement slightly weaker than possible.
- **Vacuity:** not vacuous; the $X$ from theorem 17 satisfies every hypothesis.
- **Standard fact:** the Lévy–Khintchine formula for the $L^2$ limit of compensated small-jump truncations (the
  Lévy–Itô construction).

### 17. `levy_truncation_limit_charFun`

**Rendering.** Under the hypotheses of theorem 16 on $\nu,T,\delta,\Lambda,M$, there exists $X:\Omega_\star\to\mathbb R$
with:
- (a) $X-S_0\in L^2(\mathbb P)$;
- (b) for every $\ell$: $\mathbb E(X-S_\ell)^2=T\int_{|z|<\delta_\ell}z^2\,d\nu$;
- (c) $\mathbb E\,e^{itX}=\exp(T\int g_t\,d\nu)$ for every $t$.

**Assessment.**
- **Truth:** true.
  - For $\ell<L$ and $\delta_\ell\le1$: $S_L-S_\ell=\sum_{\ell<k\le L}(\text{band sum}_k-T\int_{B_k}z\,d\nu)$. This is
    a sum of independent centred terms with variance $T\int_{\delta_L\le|z|<\delta_\ell}z^2\,d\nu$.
  - So $(S_L)$ is Cauchy in $L^2$, and its limit $X$ satisfies (b). The point $z=0$ contributes $0$.
  - (c) then follows from theorem 16.
- **Hypotheses:** `hδ1` is genuinely needed for (b). Counterexample without it: $\nu=\delta_{3/2}$,
  $\delta=(2,\tfrac12,\tfrac14,\dots)$. At $\ell=0$, $X-S_0=\tfrac32N_1$ with $N_1\sim\mathrm{Po}(T)$, so
  $\mathbb E(X-S_0)^2=\tfrac94(T+T^2)\ne\tfrac94T$ (`l2_symbolic.out`).
- **Junk:** none. The integral in (b) is finite because $\delta_\ell\le1$ makes $z^2=\min(1,z^2)$ there, and the
  left side is a genuine integral by (a).
- **Vacuity:** not vacuous; `hband` is always satisfiable, with $\Lambda_k=T\nu(B_k)<\infty$.
- **Standard fact:** existence of the Lévy process marginal as the $L^2$ limit, with the exact $L^2$ truncation
  error $T\int_{|z|<\delta}z^2\,d\nu$ (Asmussen–Rosiński small-jump variance).

### 18. `levy_limit_map_eq`

**Rendering.** Fix $\nu$ and $T$. Take two truncation schemes $(\delta,\Lambda,M)$ and $(\delta',\Lambda',M')$, each
satisfying the hypotheses of theorem 16, with respective $L^2$ limits $X$ and $X'$. Then
$\mathrm{Law}_{\mathbb P}(X)=\mathrm{Law}_{\mathbb P'}(X')$ as measures on $\mathbb R$.

**Assessment.**
- **Truth:** true. Theorem 16 gives both laws the same characteristic function. Both are probability measures, since
  $X$ and $X'$ are AE-measurable, and characteristic functions determine finite measures
  (`Measure.ext_of_charFun`).
- **Hypotheses:** `hδ1` and `hδ1'` are superfluous (harmless).
- **Vacuity:** not vacuous.
- **Junk:** none.
- **Standard fact:** the limit law does not depend on the truncation scheme (uniqueness of the infinitely divisible
  law).

### 19. `exists_unique_levyKhintchine_law`

**Rendering.** For $\nu$ with $\int\min(1,z^2)d\nu<\infty$ and $T\ge0$, there is a probability measure $\rho$ on
$\mathbb R$ with $\hat\rho(t)=\exp(T\int g_t\,d\nu)$ for all $t$. Moreover, every finite measure $\rho'$ with the same
characteristic function equals $\rho$.

**Assessment.**
- **Truth:** true. Existence follows from theorem 17, for example with $\delta_k=2^{-k}$. Uniqueness follows from
  injectivity of the characteristic function on finite measures. At $t=0$, $\hat\rho'(0)=\rho'(\mathbb R)=1$, so
  $\rho'$ is automatically a probability measure.
- **Vacuity:** not vacuous ($T=0$ gives $\rho=\delta_0$; nontrivial $\nu$ works too).
- **Junk:** none; the integral is genuine by theorem 14.
- **Standard fact:** the Lévy–Khintchine theorem (existence direction for triplet $(0,0,T\nu)$) plus Lévy's
  uniqueness theorem.

### 20. `stableLike_limit_charFun`

**Rendering.** Hypotheses:
- $c>0$, $Y<2$ (no lower bound), $T\ge0$;
- $\nu_{c,Y}(dz)=(cz^{-1-Y})^+\mathbf 1_{(0,1]}(z)\,dz$ (`stableLikeLevy`; real `rpow` with positive base on the
  support);
- $\delta_\ell=2^{-\ell}$, and $\Lambda,M$ satisfying `hband` for $\nu_{c,Y}$.

Then there is $X$ with:
- (a) $\mathbb E(X-S_\ell)^2=Tc\,2^{-(2-Y)\ell}/(2-Y)$ for every $\ell$ (real `rpow`);
- (b) $\mathbb E\,e^{itX}=\exp\big(T\int_0^1cz^{-1-Y}(e^{itz}-1-itz)\,dz\big)$ for all $t$, with the integral over
  `Ioo 0 1` against Lebesgue measure.

**Assessment.**
- **Truth:** true.
  - The Lévy condition holds: $\int\min(1,z^2)d\nu=c/(2-Y)<\infty$ (`levy_checks.out` §6).
  - (a) is theorem 17(b): $T\int_0^{2^{-\ell}}cz^{1-Y}dz=Tc\,2^{-(2-Y)\ell}/(2-Y)$. This was checked symbolically
    (`l2_symbolic.out`), and numerically for $(c,Y)=(1.3,0.7),(0.4,1.9),(2,-1.5)$, both directly and as band sums
    (`levy_checks.out` §1; small "direct" deviations at $Y=1.9$ are quadrature error near the singularity).
  - (b) is theorem 17(c) with $\int g_t\,d\nu=\int_{(0,1]}cz^{-1-Y}g_t(z)\,dz$ (withDensity). The endpoint $z=1$,
    where the indicator switches, is Lebesgue-null, so this equals the stated `Ioo` integral. That integral is
    genuinely integrable: the integrand is $O(z^{1-Y})$ near $0$.
  - $B_0=\{|z|\ge1\}$ has $\nu$-measure $0$, so $\Lambda_0=0$.
- **Junk:** none. For $T>0$ the right side of (a) is positive, which forces integrability. When $T=0$, $X=0$ is a
  genuine witness. The characteristic-function conclusion forces $X$ to be AE-measurable.
- **Hypotheses:** $Y\le0$ is allowed (then $\nu$ is finite, so not really "stable-like"). The statement is still
  true. $c>0$ is needed: for $c\le0$ the density is $0$ while the formula in (a) is nonzero.
- **Vacuity:** not vacuous ($c=Y=1$, $T=1$, $\Lambda_k=\nu(B_k)=2^{k-1}$ for $k\ge1$, $\Lambda_0=0$).
- **Standard fact:** the Lévy–Itô construction for a one-sided tempered (truncated) stable-like Lévy measure, with
  small-jump $L^2$ error $\propto\delta^{2-Y}$ (Asmussen–Rosiński; the rate used in multilevel Monte Carlo for Lévy
  processes).
