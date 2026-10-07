# Blind read-back report: packet R23 (estimators)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round19/packet_R23_estimators.lean` |
| declarations audited | 13 theorems; the 4 packet definitions and the 6 appended definitions are also rendered |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round19/work_R23/` (`*.py` with matching `*.out`; Lean scratch files `scratch_R23*.lean` / `.out`, `negctrl.lean` / `.out`) |
| toolchain | Lean v4.33.1, Mathlib 0df444a: the packet compiles as a scratch copy with targeted Mathlib imports, with only the 13 expected `sorry` warnings |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `cltCex_moments` | theorem | true | no (no hypotheses) | no |
| 2 | `mlmc_clt_counterexample` | theorem | true | no | no |
| 3 | `mlmc_clt_counterexample_conditions` | theorem | true | no | no |
| 4 | `exists_mlmc_clt_counterexample` | theorem | true | no (existential, witnessed by an infinite product space) | no |
| 5 | `consistency_check_one_sample_iff` | theorem | true | no (no hypotheses) | no (a 1-sample empirical variance really is 0; every divisor is 1) |
| 6 | `consistency_check_one_sample` | theorem | true | no | no |
| 7 | `consistency_check_two_samples` | theorem | true | no | no |
| 8 | `sampleVar_mean_variance` | theorem | true | no | no |
| 9 | `sampleVar_sd` | theorem | true | no | no |
| 10 | `tendsto_sampleVar_sd_div` | theorem | true | no | no |
| 11 | `empVar_mean_variance` | theorem | true | no | no |
| 12 | `empVar_sd` | theorem | true | no | no |
| 13 | `tendsto_empVar_sd_div` | theorem | true | no | no |

## Main points for a human auditor

1. All 13 statements are true as stated. None is vacuous, and none depends on a junk value. I found no false
   statement; the remarks below concern meaning and hypothesis strength only.
2. **Meaning of "not asymptotically normal" (#2, #4).** The MLMC error is standardised by its *exact*
   standard deviation $s_k$, and the claim is that it does **not** converge in distribution to
   $N(0,1)$ (conjunct (d)). The theorem also proves the stronger conjunct (c): the standardised error tends
   to $0$ in probability, so its limit law is $\delta_0$. Conjunct (d) follows from (c) by uniqueness of
   weak limits. I confirmed $\delta_0$ with exact characteristic functions. At $t=2$, $\varphi_{T_k}(t)$ is
   $0.858, 0.961, 0.9965$ for $k=10, 40, 320$, against $e^{-2}=0.135$ for $N(0,1)$. A simulation with exact
   binomial sampling agrees: $P(|T_k|\le 0.5) = 0.92, 0.98, 0.99$ for $k = 10, 18, 24$, against $0.38$ for
   $N(0,1)$. Convergence is slow: the levels below $k$ carry a share $k/(k+(k+1)^2)\approx 1/k$ of the
   variance.
3. "Each level estimator is asymptotically normal" is proved only for a **fixed** level $\ell$ as
   $k\to\infty$ (conjunct (a)). The moving top level $\ell=k$, which has only $k+1$ samples, tends to $0$ in
   probability (conjunct (b)). That is the usual meaning.
4. **Violated conditions (#3).** The Lindeberg sum tends to $1$, the maximum possible, instead of $0$. The
   Lyapunov ratio does not tend to $0$ for any $\delta\ge 0$. The case $\delta=0$ is trivial (the ratio is
   identically $1$); for $\delta>0$ the ratio tends to $\infty$. The uniform bound on standardised
   $(2+\delta)$-moments fails because the ratio is $2^{\ell\delta/2}$ (the kurtosis is $2^\ell$).
5. **Consistency check (#5–#7).** These statements are about the event that the 3-sigma check *fires*
   (reports an inconsistency).
   - With $N=1$, all three empirical variances are $0$, so the check fires exactly when
     $Pf_\ell \ne Pc_\ell$ at the two samples. That happens almost surely when $Pc_\ell$ is atomless, whether
     or not $E Pf_\ell = E Pc_\ell$.
   - With $N=2$, in a Gaussian example where $E Pf_\ell = E Pc_\ell$ does hold, the false-alarm
     probabilities are exactly $\tfrac{2}{\pi}\arctan(\sqrt2/3)\approx 0.2804$ (biased `empVar`) and
     $\tfrac{2}{\pi}\arctan(1/3)\approx 0.2048$ (unbiased `sampleVar`). Both follow from a ratio of
     independent normals being standard Cauchy. I confirmed both by exact angular integration (agreement to
     $10^{-41}$), by quadrature, and by a $4\cdot10^5$-sample Monte Carlo run.
6. **Sample-variance moments (#8–#13).** The formulas are the textbook ones. I verified them with sympy for
   $N=2,\dots,7$ using general raw moments, and by exact enumeration for a Rademacher law ($\kappa=1$),
   Bernoulli(1/3), a 3-point law and a constant. Hypothesis strength:
   - `hN : 2 ≤ N` is essential for `sampleVar`: Lean's `sampleVar x 1 = 0` (division by $0$), so
     $E[s_1^2]=0\ne\sigma^2$.
   - `hN` is unnecessary in #11, which also holds for $N=1$.
   - `hv` (in #9) and `hκ` (in #10) are essential. The packet's `kurtosis` of a zero-variance variable is
     the junk value $0$, which `hv` excludes.
   - With $\kappa=1$, the standard deviation of $s^2$ decays like $\sigma^2\sqrt{2}/N$, not like
     $\sigma^2\sqrt{(\kappa-1)/N}$, which is why `hκ` is needed in the limit statements.
7. The packet's `kurtosis` is the raw ratio $\int X^4/(\int X^2)^2$. It is applied to $X-EX$ in #9–#13,
   which gives Pearson's (not excess) kurtosis. In #1 it is applied to the uncentred $Y_\ell$, which is
   legitimate because $EY_\ell=0$.
8. Minor remarks on hypothesis strength (none affects truth):
   - #6 assumes mutual independence of the whole family, but only $\omega_{(\ell,0)}\perp\omega_{(\ell+1,0)}$
     is used.
   - #8 assumes $L^4$ for the mean claim, which needs only $L^2$.
   - The upper bound in #12 reuses the `sampleVar` bound, so it drops a factor $(N-1)/N$ and is looser than
     necessary.

## Lean and Mathlib conventions checked

- `ProbabilityTheory.variance X μ = (evariance X μ).toReal` with `evariance = ∫⁻ ‖X − μ[X]‖ₑ²`. It equals
  $0$ for $X\notin L^2$, but that case never arises here: every function is bounded or polynomial in
  $L^4$ variables.
- `TendstoInDistribution X l Z μ μ'` is a *structure*. It requires every `X i` to be AE-measurable and `Z`
  to be AE-measurable, plus `Tendsto` of the laws in `ProbabilityMeasure E` (weak convergence). A negated
  `TendstoInDistribution` could therefore hold for a junk reason. It does not here: all $T_k$ are
  measurable (measurable step functions of the measurable $\omega_p$), and `HasLaw` gives AE-measurability
  of $Z$.
- `TendstoInMeasure μ f l g` means $\forall\varepsilon>0$ (in `ℝ≥0∞`),
  $\mu\{\varepsilon\le \mathrm{edist}(f_i x, g x)\}\to 0$. It imposes no measurability requirement.
- Other definitions confirmed in Mathlib:
  - `HasLaw Z ν P`: AE-measurable, and `P.map Z = ν`.
  - `MeasurePreserving f μa μb`: measurable, and `map f μa = μb`.
  - `iIndepFun`: mutual independence.
  - `gaussianReal 0 1` is $N(0,1)$.
- Notation precedences:
  - `√` is `prefix:max` for `Real.sqrt`, so `√s ^ (2+δ)` is $(\sqrt s)^{2+\delta}$.
  - In `∫ x, f ∂μ` the measure is parsed at precedence 70, so `∫ … ∂ν - c` is $(\int\ldots)-c$.
- Parse checks: `with_reducible rfl` confirmed the parenthesisation of the right-hand sides of #8, #9 and
  #11, of the closed form in #1(iv), and of `√s ^ (2+δ)`. A negative control with a different
  parenthesisation is rejected (`negctrl.out`).
- Facts confirmed in Lean on the scratch copy:
  - `levelDiff cltCexP ℓ = cltCexDiff ℓ`.
  - `empMean x 1 = x 0` and `empVar x 1 = 0`.
  - `sampleVar x 1 = 0` and `sampleVar x 0 = 0` (junk values).
  - `empVar x 2 = (x 0 − x 1)²/4` and `sampleVar x 2 = (x 0 − x 1)²/2`.
  - The `kurtosis` of the zero function under a Dirac mass is $0$ (junk value).
  - `cltCexN 3 3 = 4`, `cltCexN 3 1 = 256`, `cltCexN 3 5 = 64` (truncated subtraction for $\ell>k$).

## Definitions (rendering)

Notation used throughout:

- $\lambda$ is `volume.restrict (Set.Icc 0 1)`, the uniform law on $[0,1]$.
- $V_\ell := \operatorname{Var}_\lambda(Y_\ell)$.
- $s_k^2 := \sum_{\ell=0}^k V_\ell/N_{k,\ell}$.

The definitions:

- `cltCexDiff ℓ u` $=D_\ell(u)$, which is $1$ if $u<2^{-\ell}/2$, $-1$ if $2^{-\ell-1}\le u<2^{-\ell}$, and
  $0$ if $u\ge 2^{-\ell}$. It also equals $1$ for $u<0$, which is a $\lambda$-null set.
- `cltCexP ℓ u` $=P_\ell(u)=\sum_{j=0}^{\ell}D_j(u)$. Explicitly, $P_\ell = j-1$ on $[2^{-j-1},2^{-j})$ for
  $j\le\ell$, $P_\ell = \ell+1$ on $[0,2^{-\ell-1})$, and $P_\ell(1)=0$.
- `cltCexN k ℓ` $=N_{k,\ell}$, which is $k+1$ if $\ell=k$ and $(k+1)^3\,2^{k\,\dot-\,\ell}$ otherwise. The
  subtraction is truncated in ℕ, so the value is $(k+1)^3$ when $\ell>k$.
- `sampleVar x N` $=\frac{1}{N-1}\sum_{n<N}(x_n-\bar x_N)^2$ with real $N-1$. Lean convention: the value
  is $0$ at $N=1$ (division by $0$) and at $N=0$ (the sum is $0$).
- `levelDiff Pl ℓ` $= Pl_0$ for $\ell=0$, and $Pl_\ell - Pl_{\ell-1}$ otherwise. Write
  $Y_\ell :=$ `levelDiff cltCexP ℓ` $=D_\ell$.
- `levelEstimator Pl ω ℓ N x` $=\hat Y_{\ell,N}(x) = N^{-1}\sum_{n<N}\mathrm{levelDiff}\,Pl\,\ell\,(\omega_{(\ell,n)}(x))$.
  At $N=0$ it is $0$.
- `mlmcEstimator Pl ω L N x` $=\sum_{\ell=0}^{L}\hat Y_{\ell,N(\ell)}(x)$. Write
  $\hat P_k :=$ `mlmcEstimator cltCexP ω k (cltCexN k)`.
- `kurtosis X ν` $=\int X^4\,d\nu\,/\,(\int X^2\,d\nu)^2$ (raw moments, not centred). Lean convention: the
  value is $0$ if the denominator is $0$.
- `empMean x N` $=\bar x_N=(\sum_{n<N}x_n)/N$. `empVar x N` $=\sum_{n<N}(x_n-\bar x_N)^2/N$ (biased).

---

## 1. `cltCex_moments`

**Rendering.** There are no hypotheses. The statement is the conjunction of four parts.

1. For every $\ell\in\mathbb N$:
   - $\int Y_\ell\,d\lambda=0$;
   - $\operatorname{Var}_\lambda(Y_\ell)=2^{-\ell}$;
   - $\lambda\{Y_\ell\neq 0\}=2^{-\ell}$ (as a real number, via `.real`);
   - `kurtosis` $(Y_\ell,\lambda)=\int Y_\ell^4\,d\lambda/(\int Y_\ell^2\,d\lambda)^2=2^\ell$;
   - $\int P_\ell\,d\lambda=0$.
2. For all $\ell\le m$: $\int(P_m-P_\ell)^2\,d\lambda=2^{-\ell}-2^{-m}$.
3. For every $n_0\in\mathbb N$ there is $K$ such that $N_{k,\ell}\ge n_0$ for all $k\ge K$ and all
   $\ell\le k$.
4. For every $k$: $\sum_{\ell=0}^{k}\operatorname{Var}_\lambda(Y_\ell)/N_{k,\ell} = \big(k/(k+1)^3+1/(k+1)\big)/2^k$,
   computed in ℝ with casts from ℕ.

**Assessment.** True.

- $Y_\ell=D_\ell$ by telescoping (also confirmed in Lean).
- Under $\lambda$, $D_\ell$ takes the value $\pm1$ with probability $2^{-\ell-1}$ each and $0$ otherwise.
  So its mean is $0$, and $E D_\ell^2=E D_\ell^4=P(D_\ell\ne0)=2^{-\ell}$, which gives kurtosis
  $2^{-\ell}/2^{-2\ell}=2^\ell$.
- For $i<j$, $D_j\neq0$ only on $[0,2^{-j})\subseteq[0,2^{-i-1})$, where $D_i=1$. Hence
  $E D_iD_j=E D_j=0$, and $E(P_m-P_\ell)^2=\sum_{j=\ell+1}^{m}2^{-j}$.
- $\min_{\ell\le k}N_{k,\ell}=k+1$, which gives part 3.
- Each $\ell<k$ contributes $2^{-\ell}/((k+1)^32^{k-\ell})=2^{-k}/(k+1)^3$, and the top level contributes
  $2^{-k}/(k+1)$. That gives part 4.

`cltcex_exact.py` verified everything exactly with rationals: part 1 for $\ell\le12$, part 2 for
$\ell\le m\le10$, part 4 for $k\le40$.

- **Vacuity:** none, since there are no hypotheses.
- **Junk values:** none. The functions are bounded, so `variance` is the genuine variance, and the kurtosis
  denominator $2^{-2\ell}$ is nonzero. The raw-moment `kurtosis` equals Pearson's because $EY_\ell=0$.
  Truncated ℕ-subtraction only affects $\ell>k$, which never enters parts 3 and 4.
- **Standard fact:** a toy MLMC hierarchy with $V_\ell=2^{-\ell}$ ($\beta=1$), no weak error, and kurtosis
  $2^\ell$ (rare $\pm1$ jumps).

## 2. `mlmc_clt_counterexample`

**Rendering.** Hypotheses:

- $(\Omega,\mu)$ is a probability space;
- $(\omega_p)_{p\in\mathbb N\times\mathbb N}$ are real random variables, each with law $U[0,1]$ (`hω`),
  mutually independent (`hind`);
- $Z$ is a random variable on another probability space $(\Omega',P')$ with law $N(0,1)$ (`hZ`, which also
  gives AE-measurability).

Conclusions, as $k\to\infty$:

- **(a)** For every fixed $\ell$: $\big(\hat Y_{\ell,N_{k,\ell}}-EY_\ell\big)/\sqrt{V_\ell/N_{k,\ell}}$
  converges in distribution to $Z$ (that is, to $N(0,1)$).
- **(b)** For the top level: $\big(\hat Y_{k,N_{k,k}}-EY_k\big)/\sqrt{V_k/N_{k,k}}\to0$ in $\mu$-probability,
  where $N_{k,k}=k+1$.
- **(c)** $T_k:=\big(\hat P_k-\int P_k\,d\lambda\big)/s_k\to0$ in $\mu$-probability.
- **(d)** $T_k$ does **not** converge in distribution to $Z$.

Because the levels are independent, $s_k^2$ is exactly $\operatorname{Var}(\hat P_k)$, and
$E\hat P_k=\int P_k\,d\lambda=0$. So $T_k$ is the exactly standardised MLMC error.

**Assessment.** True.

- **(a)** For fixed $\ell$, $N_{k,\ell}=(k+1)^32^{k-\ell}\to\infty$, and the summands are iid with variance
  $2^{-\ell}>0$, so the Lindeberg–Lévy CLT applies. The exact characteristic functions approach
  $e^{-t^2/2}$ for $\ell=0,3,8$ (`cltcex_charfun.out`).
- **(b)** $P\big(\sum_{n\le k}Y_k(\omega_{(k,n)})\ne0\big)\le(k+1)2^{-k}\to0$.
- **(c)** Write $T_k=A_k+B_k$, where $A_k$ collects the levels below $k$ and $B_k$ is level $k$.
  - $EA_k^2=k/(k+(k+1)^2)\to0$, so $A_k\to0$ in $L^2$.
  - $P(B_k\ne0)\le(k+1)2^{-k}\to0$, even though $EB_k^2=(k+1)^2/(k+(k+1)^2)\to1$.
- **(d)** By (c) and Mathlib's `TendstoInMeasure.tendstoInDistribution`, $T_k$ converges in distribution
  to $\delta_0$. Limits in distribution are unique (`tendstoInDistribution_unique`), and
  $\delta_0\neq N(0,1)$. The negation is not trivially true through the structure's AE-measurability
  fields, because all $T_k$ are measurable.

So "not asymptotically normal" means precisely that the exactly standardised error fails to converge in
distribution to $N(0,1)$. Its actual limit is $\delta_0$: asymptotically all the variance sits in the top
level, which is zero with probability tending to $1$.

Numerics:

- Exact characteristic functions: $\varphi_{T_k}(t)\to1$ for each $t$ tested. At $t=2$ they are
  $0.858$, $0.961$ and $0.9965$ for $k=10$, $40$ and $320$; at $t=3$, $k=320$ the value is $0.992$.
- Simulation (`cltcex_sim.out`): $P(|T_k|\le0.25)=0.63$, $0.75$ and $0.81$ for $k=10$, $18$ and $24$,
  against $0.197$ for $N(0,1)$.

The other checks:

- **Vacuity:** none. Take $\Omega=\mathbb R^{\mathbb N\times\mathbb N}$ with `Measure.infinitePi` of
  $\lambda$ and coordinate maps for $\omega$; take $\Omega'=\mathbb R$, $P'=N(0,1)$ and $Z=\mathrm{id}$
  (as in #4).
- **Junk values:** none. Every $N_{k,\ell}\ge1$ and every $V_\ell>0$, so there is no division by $0$ and
  no square root of a negative number.
- **Remarks:** (d) is a corollary of (c). Asymptotic normality is claimed only for fixed $\ell$ in (a),
  which is the standard notion.
- **Standard fact:** this is a counterexample showing that $N_\ell\to\infty$ at every level, together with
  per-level asymptotic normality, does not imply a CLT for MLMC with a growing number of levels.

## 3. `mlmc_clt_counterexample_conditions`

**Rendering.** The hypotheses on $\omega$ are those of #2, without $Z$. Put
$\xi_{k,\ell,n}:=(N_{k,\ell}s_k)^{-1}\big(Y_\ell(\omega_{(\ell,n)})-EY_\ell\big)$, so that
$T_k=\sum_{\ell\le k}\sum_{n<N_{k,\ell}}\xi_{k,\ell,n}$ and $\sum E\xi^2=1$. The conclusions:

- **(i)** For every real $\varepsilon>0$, the Lindeberg sum
  $L_k(\varepsilon):=\sum_{\ell\le k,\ n<N_{k,\ell}}\int_{\{|\xi_{k,\ell,n}|>\varepsilon\}}\xi_{k,\ell,n}^2\,d\mu$
  tends to $1$. The sum runs over the Finset `sigma`, and the integrals are set integrals.
- **(ii)** For every real $\delta\ge0$, the Lyapunov ratio
  $R_k(\delta):=\big(\sum_{\ell\le k}E_\lambda|Y_\ell-EY_\ell|^{2+\delta}\,N_{k,\ell}^{-1-\delta}\big)/s_k^{2+\delta}$
  does **not** tend to $0$. Powers are `rpow`, and $R_k(\delta)=\sum E|\xi|^{2+\delta}$.
- **(iii)** For every $\delta>0$ there is **no** real $K$ with
  $E_\lambda|Y_\ell-EY_\ell|^{2+\delta}\le K\,V_\ell^{1+\delta/2}$ for all $\ell$.

**Assessment.** True.

- **(i)** Since $|Y_\ell|\in\{0,1\}$,
  $L_k(\varepsilon)=s_k^{-2}\sum_{\ell\le k}(V_\ell/N_{k,\ell})\,\mathbf 1[N_{k,\ell}s_k<1/\varepsilon]$.
  The top level has $N_{k,k}s_k=\sqrt{(k/(k+1)+k+1)\,2^{-k}}\to0$, so its term is eventually included. That
  term equals $(k+1)^2/(k+(k+1)^2)\to1$, and the whole sum is at most $1$.
- **(ii)** $E|Y_\ell|^{2+\delta}=2^{-\ell}$, using `0 ^ (2+δ) = 0` (valid because $2+\delta\ne0$).
  - For $\delta=0$, $R_k\equiv1$, which is trivial.
  - For $\delta>0$, the top-level term behaves like $(2^k/(k+1))^{\delta/2}\to\infty$.
- **(iii)** The ratio is $2^{-\ell}/2^{-\ell(1+\delta/2)}=2^{\ell\delta/2}$, which is unbounded.

Exact numerics (`cltcex_exact.out`):

- $L_k(0.1)$ is $0.924$, $0.982$ and $0.998$ for $k=10$, $40$ and $320$.
- $R_k(0.5)$ is $2.8$, $393$ and $3.4\cdot10^5$ for $k=10$, $40$ and $80$.
- $R_k(0.01)$ is $8.9$ at $k=640$.

The other checks:

- **Vacuity:** none (the same instance as #2).
- **Junk values:** none. The `rpow` bases are nonnegative ($|\cdot|$, $\sqrt{\cdot}$) or at least $1$
  ($N_{k,\ell}$), and the sets are measurable.
- **Remark:** the $\delta=0$ case of (ii) is included but trivial.
- **Standard fact:** the Lindeberg condition, the Lyapunov condition, and uniformly bounded standardised
  $(2+\delta)$-moments are the usual sufficient conditions for an MLMC CLT. The example violates all three;
  the last one fails because the kurtosis $2^\ell$ is unbounded.

## 4. `exists_mlmc_clt_counterexample`

**Rendering.** There exist:

- a probability space $(\Omega,\mu)$ with $\Omega$ in `Type`;
- a mutually independent family $(\omega_p)_{p\in\mathbb N\times\mathbb N}$ of $U[0,1]$ real random
  variables

such that (a)–(d) of #2 hold with $Z=\mathrm{id}$ on $(\mathbb R,N(0,1))$. The elaborated statement binds
the anonymous `MeasurableSpace` and `IsProbabilityMeasure` witnesses as instances, which the scratch compile
confirms.

**Assessment.** True. Take $\Omega=\mathbb N\times\mathbb N\to\mathbb R$ with `Measure.infinitePi`
$(\lambda)$ and the coordinate projections, then apply #2 with
`HasLaw id (gaussianReal 0 1) (gaussianReal 0 1)`. The theorem also shows that the hypotheses of #2 and #3
are satisfiable.

- **Junk values:** none.
- **Standard fact:** this is the existence form of the counterexample.

## 5. `consistency_check_one_sample_iff`

**Rendering.** The setting is arbitrary types $\Omega_0,\Omega$ (no measurability), arbitrary
$Pf,Pc:\mathbb N\to\Omega_0\to\mathbb R$, $\omega:\mathbb N\times\mathbb N\to\Omega\to\Omega_0$, a level
$\ell$ and an outcome $x$. Put:

- $a_n=Pf_\ell(\omega_{(\ell,n)}x)$;
- $b_n=Pf_{\ell+1}(\omega_{(\ell+1,n)}x)$;
- $c_n=b_n-Pc_\ell(\omega_{(\ell+1,n)}x)$.

The statement has two parts:

- `empVar` of $a$, $b$ and $c$ at $N=1$ is $0$.
- $3\big(\sqrt{v_a/1}+\sqrt{v_b/1}+\sqrt{v_c/1}\big)<|\bar a_1-\bar b_1+\bar c_1|$ holds iff
  $Pf_\ell(\omega_{(\ell,0)}x)\ne Pc_\ell(\omega_{(\ell+1,0)}x)$.

**Assessment.** True by direct algebra. One sample has empirical variance $(x_0-x_0)^2/1=0$ and empirical
mean $x_0$ (both Lean-checked). So the left-hand side is $0$, and
$\bar a-\bar b+\bar c=Pf_\ell(\omega_{(\ell,0)}x)-Pc_\ell(\omega_{(\ell+1,0)}x)$. In 100,000 random trials,
ties included, there were 0 violations (`consistency_check.out`).

- **Vacuity:** none.
- **Junk values:** none; every divisor is $1$.
- **Standard fact:** the degenerate $N=1$ case of the MLMC consistency check, which tests
  $E P^f_\ell=E P^c_\ell$ via $|\hat a-\hat b+\hat c|$ against three standard errors.

## 6. `consistency_check_one_sample`

**Rendering.** Hypotheses:

- $(\Omega,\mu)$ is a probability space;
- the $\omega_p:\Omega\to\Omega_0$ have law $\nu$ and are mutually independent;
- $Pf_\ell$ and $Pc_\ell$ are measurable;
- the law of $Pc_\ell$ under $\nu$ has no atoms: $\nu\{Pc_\ell=t\}=0$ for every $t$.

Conclusion: the check with $N=1$ fires with $\mu$-probability exactly $1$.

**Assessment.** True. By #5 the event is $\{Pf_\ell(\omega_{(\ell,0)})\ne Pc_\ell(\omega_{(\ell+1,0)})\}$. The
indices $(\ell,0)$ and $(\ell+1,0)$ differ, so by independence and Fubini the complementary event has
probability $\int\nu\{Pc_\ell=Pf_\ell(y)\}\,\nu(dy)=0$.

The theorem does not assume $E Pf_\ell=E Pc_\ell$, so the one-sample check always signals an inconsistency.
In a simulation with $Pf=Pc=\mathrm{id}$ and uniform inputs, where the identity holds, it fired in 100% of
$10^5$ runs.

- **Vacuity:** none. Take $\Omega_0=\mathbb R$, $\nu=\lambda$, $Pc_\ell=\mathrm{id}$, on a product space.
- **Junk values:** none.
- **Hypothesis strength:** `hind` (independence of the whole family) is stronger than needed; only two
  coordinates are used. `hatom` could equally be placed on $Pf_\ell$. Both are harmless.

## 7. `consistency_check_two_samples`

**Rendering.** Hypotheses:

- the $\omega_p$ are iid $N(0,1)$ and mutually independent;
- $Pf_\ell\equiv0$, $Pf_{\ell+1}\equiv0$ and $Pc_\ell(y)=-y$.

So $E Pf_\ell=0=E Pc_\ell(G)$, and the identity being tested holds. With $N=2$ the conclusions are:

- $\mu(\text{check with biased `empVar` fires})=\tfrac{2}{\pi}\arctan(\sqrt2/3)$, and $1/4$ is below that
  value.
- $\mu(\text{check with unbiased `sampleVar` fires})=\tfrac{2}{\pi}\arctan(1/3)$, and $1/8$ is below that
  value.

**Assessment.** True.

- Here $a=b=0$ and $c_n=G_n:=\omega_{(\ell+1,n)}$.
- `empVar` $(c,2)=(G_0-G_1)^2/4$ and `sampleVar` $(c,2)=(G_0-G_1)^2/2$ (both Lean-checked), and the
  empirical mean is $(G_0+G_1)/2$.
- With $U=(G_0+G_1)/\sqrt2$ and $V=(G_0-G_1)/\sqrt2$ (iid $N(0,1)$):
  - the biased check fires iff $3|V|/2<|U|/\sqrt2$, i.e. $|V/U|<\sqrt2/3$;
  - the unbiased check fires iff $|V/U|<1/3$.
- $V/U$ is standard Cauchy, and $P(|C|<c)=\tfrac{2}{\pi}\arctan c$.

Numerics (`consistency_check.out`):

- The values are $0.280437798007543>0.25$ and $0.204832764699133>0.125$.
- An independent angular computation, using the homogeneity of the event and the rotation invariance of
  the 2-D Gaussian, matches to $10^{-41}$, and so does quadrature.
- Monte Carlo with $4\cdot10^5$ runs gives $0.28065\pm0.0007$ and $0.20484$.

The other checks:

- **Vacuity:** none (a Gaussian product space).
- **Junk values:** none; `sampleVar` at $N=2$ divides by $1$.
- **Standard fact:** the false-alarm rate of the 3σ consistency check with tiny samples, via a Cauchy
  ratio.

## 8. `sampleVar_mean_variance`

**Rendering.** Hypotheses:

- $\mu$ is a probability measure;
- the $\omega_n:\Omega\to\Omega_0$ have law $\nu$ (so $\nu$ is a probability measure) and are mutually
  independent;
- $X$ is measurable with $\int X^4\,d\nu<\infty$;
- $N\ge2$.

Let $s_N^2(x)=$ `sampleVar` $(X(\omega_0x),\dots,X(\omega_{N-1}x))$, $\sigma^2=\operatorname{Var}_\nu X$ and
$\mu_4=\int(X-EX)^4\,d\nu$. Conclusion:
$E_\mu s_N^2=\sigma^2$ and $\operatorname{Var}_\mu(s_N^2)=\big(\mu_4-\tfrac{N-3}{N-1}\sigma^4\big)/N$.
The parse was confirmed by reducible `rfl`.

**Assessment.** True; these are the textbook formulas. sympy confirms them for $N=2,\dots,7$ with general
raw moments $m_1,\dots,m_4$ (`samplevar_sympy.out`), and exact enumeration confirms them for four laws.

- **Vacuity:** none (iid $N(0,1)$, $X=\mathrm{id}$).
- **Junk values:** none. $X\in L^4$ gives $s^2\in L^2$, so `variance` is genuine. A zero-variance $X$
  gives $0=0$ genuinely.
- **`hN` is essential:** at $N=1$ Lean's `sampleVar` is $0$, so $E=0\ne\sigma^2$ (enumeration).
- **Hypothesis strength:** the mean claim alone needs only $L^2$.

## 9. `sampleVar_sd`

**Rendering.** The hypotheses of #8 plus $\sigma^2>0$ and $N\ge2$. Let
$\kappa=$ `kurtosis` $(X-EX,\nu)=\mu_4/\sigma^4$ (Pearson's kurtosis). The statement has four parts:

1. $1\le\kappa$.
2. $\operatorname{sd}(s_N^2)=\sqrt{(\kappa-1)/N+2/(N(N-1))}\;\sigma^2$.
3. $\sqrt{(\kappa-1)/N}\,\sigma^2\le\operatorname{sd}(s_N^2)$.
4. If $\kappa>1$, then $\operatorname{sd}(s_N^2)\le\sqrt{(\kappa-1)/N}\,\sigma^2\big(1+1/((\kappa-1)(N-1))\big)$.

**Assessment.** True.

1. $(EZ^2)^2\le EZ^4$ by Cauchy–Schwarz on a probability space.
2. This is #8 rewritten; sympy gives difference $0$.
3. Drop the nonnegative term $2/(N(N-1))$.
4. Use $\sqrt{a+b}\le\sqrt a\,(1+b/(2a))$. sympy gives
   $a(1+t)^2-(a+b)=1/(N(N-1)^2(\kappa-1))\ge0$.

The bounds were also checked numerically for the Bernoulli(1/3) and 3-point laws.

- **`hv` is necessary for part 1:** with $\sigma^2=0$ the Lean `kurtosis` is $0/0=0$. Part 1 is therefore
  not junk-dependent; junk would *break* it, and `hv` rules that out.
- **$\kappa=1$ (Rademacher):** part 3 reads $0\le\ldots$, part 4 is vacuous, and part 2 gives
  $\sigma^2\sqrt{2/(N(N-1))}$, matching enumeration.
- The square-root arguments are $\ge0$ because $\kappa\ge1$.
- **Vacuity:** none ($N(0,1)$ with $\kappa=3$).

## 10. `tendsto_sampleVar_sd_div`

**Rendering.** The hypotheses of #8, without `hv` or `hN`, plus $\kappa>1$. Conclusion:
$\operatorname{sd}(s_N^2)\,/\,\big(\sqrt{(\kappa-1)/N}\,\sigma^2\big)\to1$ as $N\to\infty$.

**Assessment.** True. For $N\ge2$ the ratio is $\sqrt{1+2/((\kappa-1)(N-1))}$, which tends to $1$ (sympy
limit). The junk values at $N=0,1$ do not affect the limit.

- `hκ` implies $\sigma^2>0$, since otherwise the Lean `kurtosis` is $0$.
- `hκ` is necessary. If $\kappa=1$, the denominator is $0$, so the Lean ratio is $0$. Mathematically the
  rate is then different: $\operatorname{sd}\sim\sqrt2\,\sigma^2/N$.
- **Vacuity:** none.
- **Standard fact:** $\operatorname{sd}(s^2)\approx\sigma^2\sqrt{(\kappa-1)/N}$.

## 11. `empVar_mean_variance`

**Rendering.** The hypotheses of #8, with $N\ge2$. Conclusion:
$E[\mathrm{empVar}_N]=\tfrac{N-1}{N}\sigma^2$ and
$\operatorname{Var}(\mathrm{empVar}_N)=(N-1)\big((N-1)\mu_4-(N-3)\sigma^4\big)/N^3$. The parse was confirmed
by reducible `rfl`.

**Assessment.** True. Since $\mathrm{empVar}_N=\frac{N-1}{N}s_N^2$, the variance is
$((N-1)/N)^2\operatorname{Var}(s^2_N)$. sympy confirms this for $N=2,\dots,7$, and enumeration confirms it.

- **Junk values:** none.
- **Hypothesis strength:** `hN` is stronger than needed. The statement also holds at $N=1$, genuinely, with
  both sides $0$; at $N=0$ it holds only by junk.

## 12. `empVar_sd`

**Rendering.** The hypotheses of #8 plus $\sigma^2>0$ and $N\ge2$. The statement has three parts:

1. $\operatorname{sd}(\mathrm{empVar}_N)=\tfrac{N-1}{N}\sqrt{(\kappa-1)/N+2/(N(N-1))}\,\sigma^2$.
2. $(1-1/N)\sqrt{(\kappa-1)/N}\,\sigma^2\le\operatorname{sd}(\mathrm{empVar}_N)$.
3. If $\kappa>1$, then $\operatorname{sd}(\mathrm{empVar}_N)\le\sqrt{(\kappa-1)/N}\,\sigma^2\big(1+1/((\kappa-1)(N-1))\big)$.

**Assessment.** True.

1. Follows from #11; sympy gives difference $0$, and enumeration matches.
2. Equals $\frac{N-1}{N}$ times part 3 of #9.
3. $\operatorname{sd}(\mathrm{empVar})=\frac{N-1}{N}\operatorname{sd}(s^2)\le\operatorname{sd}(s^2)$, then
   apply part 4 of #9.

- **Junk values:** none.
- **Hypothesis strength:** part 3 is looser than necessary because it misses the factor $(N-1)/N$. That is
  harmless.
- **Vacuity:** none.

## 13. `tendsto_empVar_sd_div`

**Rendering.** The hypotheses of #10. Conclusion:
$\operatorname{sd}(\mathrm{empVar}_N)\,/\,\big(\sqrt{(\kappa-1)/N}\,\sigma^2\big)\to1$.

**Assessment.** True. The ratio is $\frac{N-1}{N}\sqrt{1+2/((\kappa-1)(N-1))}$, which tends to $1$ (sympy
limit). The remarks on `hκ` from #10 apply here too.

- **Junk values:** none.
- **Vacuity:** none.
