# Blind read-back report: central limit theorems (packet R1)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round12/packet_R1_central_limit.lean` |
| declarations audited | 11 theorems |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round12/work_R1/` (`lyapunov_instances.py/.out`, `exact_clt_dyadic.py/.out`, `Scratch1.lean/.out`, `Probe2.lean/.out`) |

Lean checks: `Scratch1.lean` is the packet with `sorry` proofs in a renamed namespace on top of
`import MlmcLean`. It elaborates with only "declaration uses `sorry`" warnings. It also confirms by
`rfl` that `√V ^ (2+δ)` parses as `(Real.sqrt V) ^ (2+δ)` (`√` is `prefix:max`) and that
`(n:ℝ) ^ (-1-δ)` is `Real.rpow`. `Probe2.lean` compiles with no errors. It proves formally:
(a) at δ = 0 the hypotheses of `tendstoInDistribution_lyapunov` contradict each other;
(b) at δ = 0 the MLMC Lyapunov hypothesis `hlyap`, together with `hσ` and `hPl`, is
contradictory (the ratio is eventually exactly 1);
(c) `levelEstimator … ℓ 0 x = 0`;
(d) `((0:ℕ):ℝ) ^ (-1-δ) = 0` for δ ≥ 0.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `tendstoInDistribution_lindeberg` | theorem | true (Lindeberg–Feller CLT) | no | no |
| 2 | `tendsto_lindeberg_of_lyapunov` | theorem | true (Lyapunov ⇒ Lindeberg) | no | no |
| 3 | `tendstoInDistribution_lyapunov` | theorem | true (Lyapunov CLT) | no (δ > 0); **δ = 0 case vacuous** (formally checked) | no |
| 4 | `tendsto_measureReal_abs_le_of_tendstoInDistribution` | theorem | true (portmanteau) | no | no |
| 5 | `tendstoInDistribution_mlmcEstimator_lyapunov` | theorem | true | no (δ > 0); **δ = 0 case vacuous** (formally checked) | no |
| 6 | `tendstoInDistribution_mlmcEstimator_of_moment_le` | theorem | true | no | no |
| 7 | `tendsto_measureReal_abs_mlmcEstimator_sub_le` | theorem | true | no (δ > 0); δ = 0 vacuous | no |
| 8 | `tendsto_measureReal_abs_mlmcEstimator_sub_le_of_moment_le` | theorem | true | no | no |
| 9 | `tendstoInDistribution_mlmcEstimator_of_bias` | theorem | true | no (δ > 0); δ = 0 vacuous | no (`∫ P` may be a junk 0, but the theorem holds for any constant) |
| 10 | `tendsto_measureReal_abs_mlmcEstimator_sub_le_of_bias` | theorem | true | no (δ > 0); δ = 0 vacuous | no (same remark) |
| 11 | `eventually_lt_measureReal_abs_mlmcEstimator_sub_le_tol` | theorem | true | no (δ > 0, θ ∈ (0,1], z > 0); δ = 0 vacuous; θ ∉ [0,1] or z = 0 trivial | no |

## Main points for a human auditor

1. **No false, wholly vacuous or junk-dependent statement found.** All 11 theorems are standard
   facts, stated faithfully. `TendstoInDistribution` with rows on different spaces `Ω k` means weak
   convergence of the push-forward laws `(P k).map (S k)` in `ProbabilityMeasure ℝ`. Mathlib's
   topology there is the bounded-continuous-test-function topology
   (`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`). So this is the usual
   convergence in distribution.
2. **δ = 0 is allowed but vacuous** in #3, #5, #7, #9, #10 and #11. With δ = 0 the Lyapunov
   quantity equals the normalised variance, which is identically 1 (eventually 1 in the MLMC
   versions). It therefore cannot tend to 0. This is proved formally in `Probe2.lean`, (a) and
   (b). It is harmless, because instances with δ > 0 exist (below), but stating `0 < δ` would be
   cleaner. In #2 (no normalisation) δ = 0 is non-vacuous, and there the conclusion follows
   directly from the hypothesis.
3. **Division by zero is correctly guarded.** `hσ` (eventually $V_k>0$) is essential: with
   $P_\ell\equiv 0$ every other hypothesis of #5 holds ($0/0=0\to0$), but the conclusion
   "$0\to N(0,1)$" is false. `hN`/`hNtop` (eventually every $N_{k\ell}\ge1$) is essential: a level
   with $N=0$ would silently drop out (`levelEstimator … 0 = 0`) and shift the mean.
   `(N:ℝ)^(-1-δ)` is the genuine $N^{-1-δ}$ whenever $N\ge1$. At $N=0$ it is 0, consistent with
   `Var/0 = 0`. Only finitely many $k$ are affected, and `atTop` limits ignore them.
4. **`variance` and set integrals are genuine.** `hPl` (L² for every level ℓ ≤ L k) and `hM`
   (integrable centred (2+δ)-th moment) make every `variance`, `∫ Pl (L k)` and moment in the
   statements a true value. They are never a `toReal ⊤ = 0` or non-integrable junk 0.
   `cdf (gaussianReal 0 1) z` is $\Phi(z)$ (`cdf_eq_real`), and $2\Phi(z)-1=P(|Z|\le z)$ (checked
   numerically).
5. **`P` (the target quantity) is not assumed integrable** in #9, #10 and #11. If it is not, `∫ P`
   is the junk value 0. The statements stay true, because they hold with any real constant in
   place of `∫ P`. Only the reading "centred at $E[P]$" needs `Integrable P ν` (minor).
6. **#11 (`_tol`).** Adding the two hypotheses gives $|{\rm bias}_k|+z\sqrt{V_k}\le TOL_k$
   eventually, so negative `TOL` is impossible (contradictory hypotheses). For θ ∉ [0,1] the
   hypotheses force $TOL_k=0$ and (since $V_k>0$) $z=0$. The same happens for θ = 0. Then the
   conclusion $-\eta<\mu(\cdot)$ is trivially true, but correct ($P(|Z|\le 0)=0$). The statement
   has real content for θ ∈ (0,1] and z > 0, for example θ = 1/2, z = 1.96 in Instance A.
7. **Modelling choices (not defects).** One fixed sample array `ω (ℓ,n)` is reused for every `k`,
   which is harmless because only marginal laws matter. The CLT in #5–#8 is centred at
   $E[P_{L_k}]$, not $E[P]$. The bias hypothesis of #9 and #10, bias $=o(\sqrt{V_k})$, is
   stronger than the usual MLMC tuning in which bias $\asymp\sqrt{V_k}$. #11 covers that
   tuning instead.

**Concrete non-degenerate instances** (used for all MLMC theorems; checked in
`lyapunov_instances.out` and `exact_clt_dyadic.out`):

* **Instance A (bounded, dyadic, growing levels).** Setup:
  * $\Omega_0=\mathbb R$, $\nu=\mathrm{Unif}[0,1]$, $P(y)=y$, $P_\ell(y)=\lfloor 2^\ell y\rfloor/2^\ell$.
  * $\Omega=\mathbb R^{\mathbb N\times\mathbb N}$ with $\mu=\bigotimes\nu$ (`Measure.infinitePi`), and $\omega(p)$ the coordinate maps. These are measure-preserving and `iIndepFun`.
  * $L_k=k$, $N_{k\ell}=2^k$.

  Consequences:
  * $D_0=0$ a.s. For $\ell\ge1$, $D_\ell=b_\ell(y)2^{-\ell}$ with $b_\ell$ the ℓ-th binary digit. So $\operatorname{Var}D_\ell=2^{-2\ell-2}$ and $E|D_\ell-ED_\ell|^{2+\delta}=2^{-(\ell+1)(2+\delta)}=\operatorname{Var}^{1+\delta/2}$, giving $K=1$.
  * $V_k>0$ for $k\ge1$.
  * The Lyapunov ratio (δ = 1) is about $2^{-k/2}\to0$.
  * bias $=-2^{-k-1}$ and bias$/\sqrt{V_k}\approx-\sqrt{12}\,2^{-k/2-1}\to0$.
  * For `_tol`: θ = 1/2, z = 1.96, $TOL_k=2\max(2^{-k-1},z\sqrt{V_k})$.

  The exact law of the estimator for k ≤ 7 gives $P(|Y_k-EP_{L_k}|\le 1.96\sqrt{V_k})$ = 0.948, 0.953, 0.951, 0.950, 0.950 (k = 3–7). The Kolmogorov distance to Φ is 0.0006 at k = 7.
* **Instance B (Gaussian).** $\nu=N(0,1)$, $P_\ell(y)=(1-2^{-\ell-1})y$, so $D_\ell$ is Gaussian with
  variance $4^{-\ell-1}$, and $K=E|\xi|^{2+\delta}$. Take $L_k=k$, $N_{k\ell}=k+1$. The Lyapunov
  ratio is bounded by $K(k+1)^{-\delta/2}\to0$. The normalised estimator is exactly N(0,1) for
  every k, which is a consistency check.

---

## Per-declaration analysis

Notation: a "row" $k$ has finite index set $s_k$. In the MLMC part:
* $D_\ell=$ `levelDiff Pl ℓ`, so $D_0=P_0$ and $D_\ell=P_\ell-P_{\ell-1}$.
* $\mathrm{Var}_\ell=\mathrm{Var}_\nu(D_\ell)$ and $M_\ell(\delta)=\int|D_\ell-\int D_\ell\,d\nu|^{2+\delta}d\nu$.
* $V_k=\sum_{\ell=0}^{L_k}\mathrm{Var}_\ell/N_{k\ell}$ (real division, $x/0=0$).
* $Y_k=$ `mlmcEstimator Pl ω (L k) (N k)` $=\sum_{\ell=0}^{L_k}N_{k\ell}^{-1}\sum_{n<N_{k\ell}}D_\ell(\omega_{(\ell,n)})$ (with $0^{-1}=0$).

### 1. `tendstoInDistribution_lindeberg`

**Rendering.** Setup:
* For each $k\in\mathbb N$: a probability space $(\Omega_k,P_k)$, which may differ with $k$; a finset $s_k\subseteq\iota$; and real functions $X_{k,j}$ on $\Omega_k$.
* $Z$ on a probability space $(\Omega',P')$ with law $N(0,1)$ (`HasLaw`: AE-measurable and $P'\circ Z^{-1}=N(0,1)$).

Hypotheses, for every $k$:
* $(X_{k,j})_{j\in s_k}$ are mutually independent under $P_k$ (`iIndepFun` of the restricted family).
* Each $X_{k,j}\in L^2(P_k)$ and $E X_{k,j}=0$.
* $\sum_{j\in s_k}\mathrm{Var}(X_{k,j})=1$.
* Lindeberg: for every $\varepsilon>0$, $\sum_{j\in s_k}\int_{\{|X_{k,j}|>\varepsilon\}}X_{k,j}^2\,dP_k\to0$ as $k\to\infty$.

Conclusion: $S_k=\sum_{j\in s_k}X_{k,j}$ converges in distribution to $Z$. That is, each $S_k$ is AE-measurable, $Z$ is AE-measurable, and the laws $P_k\circ S_k^{-1}\to N(0,1)$ weakly.

**Assessment.**
* **True.** This is the Lindeberg–Feller CLT for triangular arrays (Billingsley, *Probability and Measure*, Thm 27.2; Durrett Thm 3.4.10).
* **Measurability.** `forall_aemeasurable` is needed for every k, not only eventually. It follows from `MemLp`.
* **Rows on different spaces.** These are fine: the definition only uses push-forward laws.
* **Independence.** `iIndepFun` for merely AE-measurable functions transfers to measurable modifications, since sets differing by null sets have the same outer measure.
* **No junk values.** `Var` is the true variance (L²). The set integrals are genuine: the integrand is integrable and the set is null-measurable.
* **Non-vacuous.** Take $s_k=\{0,\dots,k\}$ and $X_{k,j}=r_j/\sqrt{k+1}$ with iid Rademacher (or $N(0,1)$) $r_j$. The Lindeberg sum is $\mathbf 1\{1/\sqrt{k+1}>\varepsilon\}$, which is eventually 0 (`lyapunov_instances.out`).
* **Hypotheses.** All are standard. `h1` (exact normalisation for every k) is the usual form. Strict `ε < |X|` vs `≥` is immaterial.

### 2. `tendsto_lindeberg_of_lyapunov`

**Rendering.** For arbitrary measures $P_k$ (the `omit` removes the probability assumption), a
finset $s_k$ and $X_{k,j}$, and real $\delta\ge0$, assume:
* each $X_{k,j}$ ($j\in s_k$) is AE-measurable;
* $|X_{k,j}|^{2+\delta}$ (real power) is integrable;
* $\sum_{j\in s_k}\int|X_{k,j}|^{2+\delta}dP_k\to0$.

Then for every $\varepsilon>0$, $\sum_{j\in s_k}\int_{\{\varepsilon<|X_{k,j}|\}}X_{k,j}^2\,dP_k\to0$.

**Assessment.**
* **True.** On $\{|x|>\varepsilon\}$, $x^2\le\varepsilon^{-\delta}|x|^{2+\delta}$. So each set integral lies in $[0,\varepsilon^{-\delta}\int|X|^{2+\delta}]$, and the squeeze gives the limit.
* **Junk values do not help.** The integrand is genuinely integrable on the set, being dominated by an integrable function. Even a junk 0 would lie in the same interval.
* **Hypotheses.** Valid for non-probability measures, so dropping the instance is correct and more general. δ = 0 is allowed and non-vacuous, but then the conclusion is immediate from the hypothesis.
* **Non-vacuous.** The Rademacher array above with δ = 1 has Lyapunov sum $(k+1)^{-1/2}\to0$.
* **Standard fact.** The Lyapunov condition implies the Lindeberg condition (Billingsley, (27.16)).

### 3. `tendstoInDistribution_lyapunov`

**Rendering.** The setting and hypotheses `hind`, `hX`, `h0`, `h1` are those of #1. In addition,
for real $\delta\ge0$:
* $|X_{k,j}|^{2+\delta}$ is integrable;
* $\sum_{j\in s_k}E|X_{k,j}|^{2+\delta}\to0$.

Conclusion: $S_k\to Z\sim N(0,1)$ in distribution.

**Assessment.**
* **True.** Combine #2 with #1. This is the Lyapunov CLT (Billingsley Thm 27.3).
* **δ = 0 is vacuous.** Then $E|X|^{2}=\mathrm{Var}X$ (mean 0), so the Lyapunov sum is identically 1 by `h1` and cannot tend to 0. This is proved in Lean in `Probe2.lean` (a).
* **δ > 0 instances exist.** The Rademacher array with δ = 1 has sum $(k+1)^{-1/2}$.
* **No junk values.** The moments are integrable by `hint`.
* **Assessment of the δ convention.** Permitting δ = 0 adds only a vacuous case, so the theorem is no weaker than the standard one; `0 < δ` would be cleaner.

### 4. `tendsto_measureReal_abs_le_of_tendstoInDistribution`

**Rendering.** For any index type ι, any filter $l$, probability spaces $(\Omega_i,P_i)$ and real
$S_i$: if $S_i\to Z$ in distribution along $l$, with $Z\sim N(0,1)$ under the probability $P'$,
then for every $z\ge0$, $P_i(|S_i|\le z)\to 2\Phi(z)-1$ along $l$. Here $\Phi=$
`cdf (gaussianReal 0 1)`, which equals $N(0,1)((-\infty,z])$ by `cdf_eq_real`.

**Assessment.**
* **True.** By the portmanteau theorem: $[-z,z]$ has frontier $\{\pm z\}$, which is $N(0,1)$-null. Its mass is $\Phi(z)-\Phi(-z)=2\Phi(z)-1$, checked numerically including $z=0\mapsto0$.
* **Measurability.** $\{|S_i|\le z\}$ is null-measurable because $S_i$ is AE-measurable, so `measureReal` is genuine.
* **`hz` is needed.** For $z<0$ the left side is 0 but $2\Phi(z)-1<0$.
* **Non-vacuous.** Take $S_i=Z$ for all $i$ (`tendstoInDistribution_const`).
* **No junk values.**

### 5. `tendstoInDistribution_mlmcEstimator_lyapunov`

**Rendering.** Data:
* a probability space $(\Omega,\mu)$ and a measure space $(\Omega_0,\nu)$;
* samples $\omega_p:\Omega\to\Omega_0$, $p\in\mathbb N^2$, each measure-preserving $\mu\to\nu$ (hence ν is a probability measure) and jointly mutually independent;
* $L:\mathbb N\to\mathbb N$ with $P_\ell\in L^2(\nu)$ for all $\ell\le L_k$ and all $k$;
* real $\delta\ge0$, with $M_\ell(\delta)<\infty$ (integrable) for $\ell\le L_k$;
* $N:\mathbb N\to\mathbb N\to\mathbb N$;
* $Z\sim N(0,1)$ on a probability space $P'$.

Hypotheses:
* eventually in $k$, $N_{k\ell}\ge1$ for all $\ell\le L_k$;
* eventually $V_k>0$;
* the Lyapunov ratio tends to 0: $\Big(\sum_{\ell\le L_k}M_\ell(\delta)N_{k\ell}^{-1-\delta}\Big)\big/(\sqrt{V_k})^{2+\delta}\to0$ (real `rpow`; $(\sqrt V)^{2+\delta}=V^{1+\delta/2}$).

Conclusion: $(Y_k-E_\nu[P_{L_k}])/\sqrt{V_k}\to Z$ in distribution, with every row on $(\Omega,\mu)$.

**Assessment.**
* **True.** Eventually, view the summands $\big(D_\ell(\omega_{(\ell,n)})-ED_\ell\big)/(N_{k\ell}\sqrt{V_k})$, $\ell\le L_k$, $n<N_{k\ell}$, as one row of independent, centred L² variables.
  * Independence comes from `hind` and composition; AE-measurable $D_\ell$ is handled by taking measurable modifications.
  * The variances sum to 1.
  * The sum is $(Y_k-EP_{L_k})/\sqrt{V_k}$, because $EY_k=\sum_\ell ED_\ell=EP_{L_k}$ by telescoping (this needs every $N_{k\ell}\ge1$).
  * The Lyapunov sum equals exactly the displayed ratio.
  * So #3 applies.
* **Rows for small k.** For all $k$ the row function is AE-measurable, because `hPl` holds for every k. So `forall_aemeasurable` causes no trouble.
* **Junk values.** Every quantity is genuine eventually. $V_k\ge0$ always, so `√` never sees a negative argument. $N=0$ gives $0^{-1-\delta}=0$ (`Probe2` (d)) and $\mathrm{Var}/0=0$, but only finitely often.
* **`hσ` is necessary.** Without it, $P_\ell\equiv0$ would satisfy everything else via $0/0=0$ while the conclusion is false.
* **δ = 0 is vacuous.** The ratio is eventually exactly 1 (`Probe2.lean` (b), proved in Lean).
* **Non-vacuous for δ > 0.** Instance A (δ = 1; ratio 0.186, 0.046, 2.9e-3, 1.1e-5 at k = 4, 8, 16, 32) and Instance B (ratio ≤ $K(k+1)^{-\delta/2}$).
* **Standard result.** The Lyapunov-condition CLT for MLMC with a growing number of levels, from my own knowledge. This is the type of result in Collier–Haji-Ali–Nobile–von Schwerin–Tempone, "A continuation multilevel Monte Carlo algorithm" (BIT 2015), appendix lemma on normality of the MLMC estimator; that reference is not verified here.
* **Modelling.** One sample array is shared across $k$, which is harmless. The centring is at $E[P_{L_k}]$, so this is a CLT for the statistical error only.

### 6. `tendstoInDistribution_mlmcEstimator_of_moment_le`

**Rendering.** The setting is that of #5 with **δ > 0**, plus:
* `hM` integrability;
* a constant $K$ with $M_\ell(\delta)\le K\,\mathrm{Var}_\ell^{1+\delta/2}$ for all $k$ and $\ell\le L_k$;
* `hNtop`: for every $n_0$, eventually $\min_{\ell\le L_k}N_{k\ell}\ge n_0$ (that is, $\min_\ell N_{k\ell}\to\infty$);
* eventually $V_k>0$.

There is no Lyapunov hypothesis. Conclusion: $(Y_k-EP_{L_k})/\sqrt{V_k}\to Z\sim N(0,1)$ in distribution.

**Assessment.**
* **True.** The Lyapunov ratio is bounded as follows:
  $$\sum_\ell M_\ell N_\ell^{-1-\delta}\le K\sum_\ell(\mathrm{Var}_\ell/N_\ell)^{1+\delta/2}N_\ell^{-\delta/2}\le K(\min N)^{-\delta/2}V_k^{\delta/2}\sum_\ell \mathrm{Var}_\ell/N_\ell=K(\min N)^{-\delta/2}V_k^{1+\delta/2}.$$
  Hence the ratio is at most $K(\min N)^{-\delta/2}\to0$ (checked numerically for both instances), and #5 applies.
* **Implied hypothesis.** `hNtop` with $n_0=1$ gives `hN`.
* **Sign of K.** $K\le0$ would force all $M_\ell=0$, so all $\mathrm{Var}_\ell=0$, contradicting `hσ`. Non-vacuous instances therefore need $K>0$.
* **Non-vacuous.** Instance A with $K=1$, δ = 1; Instance B with $K=E|\xi|^{2+\delta}$.
* **No junk values.** `Var^(1+δ/2)` is an rpow of a non-negative number.
* **Strength of hypotheses.** They are sufficient conditions: a bounded normalised (2+δ)-moment ("kurtosis-type") bound and every $N_{k\ell}\to\infty$. They are standard in the MLMC CLT literature, but stronger than Lyapunov (#5), which is also provided.

### 7. `tendsto_measureReal_abs_mlmcEstimator_sub_le`

**Rendering.** The hypotheses are those of #5, without $P'$ and $Z$. For $z\ge0$:
$$\mu\big(|Y_k-EP_{L_k}|\le z\sqrt{V_k}\big)\to2\Phi(z)-1.$$

**Assessment.**
* **True.** Eventually $V_k>0$, and then the event equals $\{|(Y_k-EP_{L_k})/\sqrt{V_k}|\le z\}$. Apply #5 (with a Gaussian $Z$, which exists) and #4.
* **The case z = 0.** The limit is 0, which is correct.
* **δ = 0** is vacuous, as in #5.
* **Non-vacuous.** Instance A. The exact law at z = 1.96 gives 0.9477, 0.9529, 0.9506, 0.9500, 0.9501 for k = 3–7; at z = 1 it gives 0.678–0.683 against 0.6827.
* **No junk values.** For small $k$ with $V_k=0$ the event is a junk event, but only finitely often.
* **Standard result.** Asymptotic coverage of the MLMC normal confidence interval.

### 8. `tendsto_measureReal_abs_mlmcEstimator_sub_le_of_moment_le`

**Rendering.** The hypotheses are those of #6 (δ > 0, the K-moment bound, $\min N\to\infty$, $V_k>0$
eventually). For $z\ge0$, $\mu(|Y_k-EP_{L_k}|\le z\sqrt{V_k})\to2\Phi(z)-1$.

**Assessment.**
* **True.** By #6 and #4, as in #7.
* **Non-vacuous.** Instance A.
* **No junk values.**
* **Standard result.** As in #7.

### 9. `tendstoInDistribution_mlmcEstimator_of_bias`

**Rendering.** The hypotheses are those of #5, plus a function $P:\Omega_0\to\mathbb R$ (no
integrability assumed) with
$$\big(E_\nu P_{L_k}-\textstyle\int P\,d\nu\big)/\sqrt{V_k}\to0.$$
Conclusion: $(Y_k-\int P\,d\nu)/\sqrt{V_k}\to Z\sim N(0,1)$ in distribution.

**Assessment.**
* **True.** The row equals the CLT row of #5 plus a deterministic sequence tending to 0, so Slutsky's theorem applies.
* **`∫ P` need not be meaningful.** If $P$ is not integrable, `∫ P = 0` (junk). The statement is still true, since the proof works for any constant $c$ in place of $\int P$. Adding `Integrable P ν` would only be cosmetic.
* **δ = 0** is vacuous.
* **Non-vacuous.** Instance A with $P(y)=y$: bias$/\sqrt{V_k}\approx -\sqrt{12}\,2^{-k/2-1}\to0$, numerically −0.108 at k = 8 and −2.6e-5 at k = 32.
* **Strength of hypothesis.** Requiring bias $=o(\sqrt{V_k})$ is stronger than the usual MLMC tuning, which #11 covers.
* **Standard result.** CLT for the total error when the bias is negligible.

### 10. `tendsto_measureReal_abs_mlmcEstimator_sub_le_of_bias`

**Rendering.** The hypotheses are those of #9 (without $P'$ and $Z$). For $z\ge0$:
$$\mu\big(|Y_k-\textstyle\int P\,d\nu|\le z\sqrt{V_k}\big)\to2\Phi(z)-1.$$

**Assessment.**
* **True.** By #9 and #4, using $V_k>0$ eventually.
* **Non-vacuous.** Instance A.
* **No junk dependence.** The same `∫ P` remark as #9 applies.
* **δ = 0** is vacuous.
* **Standard result.** Asymptotic confidence interval for $E[P]$.

### 11. `eventually_lt_measureReal_abs_mlmcEstimator_sub_le_tol`

**Rendering.** The hypotheses are those of #5 (without $P'$ and $Z$). In addition there are
$P:\Omega_0\to\mathbb R$, reals θ, $z\ge0$, a sequence $TOL_k\in\mathbb R$, and $\eta>0$, with:
* eventually $|E_\nu P_{L_k}-\int P\,d\nu|\le(1-\theta)TOL_k$;
* eventually $z\sqrt{V_k}\le\theta\,TOL_k$.

Conclusion: eventually $2\Phi(z)-1-\eta<\mu(|Y_k-\int P\,d\nu|\le TOL_k)$. Equivalently,
$\liminf_k\mu(|Y_k-\int P|\le TOL_k)\ge2\Phi(z)-1$.

**Assessment.**
* **True.** By the triangle inequality,
  $$\{|Y_k-EP_{L_k}|\le z\sqrt{V_k}\}\subseteq\{|Y_k-\textstyle\int P|\le z\sqrt{V_k}+(1-\theta)TOL_k\}\subseteq\{|Y_k-\int P|\le TOL_k\}.$$
  The first set's probability tends to $2\Phi(z)-1$ by #7. The proof never uses $\theta\in[0,1]$.
* **θ and TOL.** Summing the two hypotheses gives $|{\rm bias}|+z\sqrt{V_k}\le TOL_k$ eventually, so $TOL_k\ge0$ eventually: negative `TOL` makes the hypotheses contradictory. For $\theta>1$ or $\theta<0$ the hypotheses force $TOL_k=0$ and then $z=0$ (because $V_k>0$). The same happens for θ = 0. In those cases the conclusion $-\eta<\mu(\cdot)$ is trivially true, but $2\Phi(0)-1=0$ is the correct value, so this is not a junk effect.
* **Non-vacuous.** Real content needs θ ∈ (0,1] and z > 0. Instance A with θ = 1/2, z = 1.96, $TOL_k=2\max(2^{-k-1},1.96\sqrt{V_k})$ satisfies everything; the exact probability is about 0.9999 > 0.95 − η.
* **δ = 0** is vacuous, as in #5.
* **Junk values.** The `∫ P` remark from #9 applies.
* **Standard result.** The MLMC accuracy split: bias ≤ (1−θ)TOL and $C_\alpha\sqrt{\mathrm{Var}}\le\theta TOL$ give $P(|Y-E P|\le TOL)\gtrsim1-\alpha$ with $z=C_\alpha=\Phi^{-1}(1-\alpha/2)$. This is as in continuation-MLMC (Collier et al. 2015), from my own knowledge. The conclusion is a lower bound, not a limit, which is the appropriate form.
