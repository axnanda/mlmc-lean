# Blind audit of `packet_L1_estimator_theorem1.lean`

| field | value |
|---|---|
| date | 2026-09-29 |
| packet | `readback/round10/packet_L1_estimator_theorem1.lean` |
| declarations audited | 23 (14 theorems/lemmas, 9 definitions; `universe u` is inert) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round10/work_L1/` (each `*.py` has its output next to it as `*.out`) |
| sources consulted | the packet, plus Mathlib sources in `.lake/packages/mathlib` (commit 0df444a), used only for definitions and conventions |

Scripts:

- `check_allocation.py`: checks `cost_lower_bound`, `optimalN_variance` and `optimalN_cost` on 20 000 random instances each, using 60-digit mpmath and reproducing the Lean conventions for `√`, `/0` and `⌈·⌉₊`.
- `check_estimator_finite.py`: exact rational checks on finite spaces of `mse_eq_variance_add_sq_bias`, `mlmc_mean`, `mlmc_variance`, `mlmc_mse` and `variance_sample_mean`. It also includes a dependent-variables counterexample and a non-probability-measure counterexample.
- `check_level_estimator.py`: exact checks of `integral_levelEstimator`, `variance_levelEstimator` and `indepFun_levelEstimator` on a finite product space. It also covers the edge cases $i=j$ and $N=0$.
- `check_instance.py`: builds an explicit, non-degenerate instance of all hypotheses of Theorem 1 and computes its MSE directly.
- `check_giles_theorem1.py`: runs the textbook choice of $(L,N_\ell)$ in 8 parameter regimes for $\varepsilon$ from $e^{-1}$ down to $3.7\cdot10^{-16}$. It also shows that `hαβγ` and `hC` are needed.
- `check_multiindex.py`: checks `sum_piFinset_succ`, and checks `crossDiff` against the inclusion–exclusion formula, the telescoping identity and `levelDiff`.

## Conventions used in the renderings (checked in the Mathlib sources)

- `μ[f]` is the macro `∫ x, ↑(f x) ∂μ`, i.e. the Bochner integral $\int f\,d\mu$. It equals $0$ when $f$ is not integrable.
- `variance X μ` is `(evariance X μ).toReal`, where `evariance X μ` is $\int^-\|X-\mu[X]\|_e^2\,d\mu$. For $X\in L^2$ and finite $\mu$ this is the usual variance. When the evariance is $\infty$ the value is $0$.
- `IndepFun f g μ` means $\mu(A\cap B)=\mu(A)\mu(B)$ for all $A\in\sigma(f)$ and $B\in\sigma(g)$, for any measure $\mu$. Taking $A=B=\Omega$ forces $\mu(\Omega)\in\{0,1,\infty\}$.
- `iIndepFun f μ` means $\mu(\bigcap_{i\in s}A_i)=\prod_{i\in s}\mu(A_i)$ for every finite $s$, including $s=\emptyset$. The empty case forces $\mu(\Omega)=1$ (Mathlib `iIndepFun.isProbabilityMeasure`).
- `MeasurePreserving f μ ν` means $f$ is measurable and $f_\#\mu=\nu$. `MemLp X 2 μ` means $X$ is a.e.-strongly measurable with $\|X\|_{L^2}<\infty$.
- In `∑ x ∈ s, body` the body is parsed at precedence 67 (Mathlib `bigsum` syntax). So `∑ ℓ ∈ r, Y ℓ ω - m` means $(\sum_\ell Y_\ell(\omega))-m$, and `∑ …, a + b` means $(\sum a)+b$. On the other hand `*` and `/` stay inside the sum.
- Lean's junk values: $x/0=0$, $0^{-1}=0$, $\sqrt{x}=0$ for $x<0$, and $\lceil x\rceil_+=0$ for $x\le0$. `(2:ℝ)^(t:ℝ)` and `ε^(r:ℝ)` with a positive base are the usual real powers.
- `f =O[𝓝[>] 0] g` means there is a $K$ such that $|f(\varepsilon)|\le K|g(\varepsilon)|$ for all sufficiently small $\varepsilon>0$.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `mse_eq_variance_add_sq_bias` | theorem | true | no | no |
| 2 | `mlmc_mean` | theorem (any measure) | true | no | no |
| 3 | `mlmc_variance` | theorem (any measure) | true | no | no |
| 4 | `mlmc_mse` | theorem | true | no | no |
| 5 | `levelEstimator` | def | n/a | n/a | n/a (value $0$ at $N=0$) |
| 6 | `mlmcEstimator` | def | n/a | n/a | n/a |
| 7 | `totalCost` | def | n/a | n/a | n/a |
| 8 | `integral_levelEstimator` | lemma | true | no | no |
| 9 | `variance_levelEstimator` | lemma | true | no | no (the junk case $N=0$ is excluded by `hN`) |
| 10 | `indepFun_levelEstimator` | lemma (no probability instance) | true | no | no |
| 11 | `cost_lower_bound` | theorem | true (sharp) | no | no |
| 12 | `sumSqrtVC` | def | n/a | n/a | n/a |
| 13 | `lagrangeN` | def | n/a | n/a | n/a (junk $0$ if $C_i=0$ or $\tau=0$; no theorem reaches it) |
| 14 | `optimalN` | def | n/a | n/a | n/a (`⌈·⌉₊` sends values $\le0$ to $0$; no theorem reaches it) |
| 15 | `optimalN_variance` | theorem | true | no | no |
| 16 | `optimalN_cost` | theorem | true | no | no |
| 17 | `variance_sample_mean` | theorem (any measure) | true | no | no (the junk case $N=0$ is excluded by `hN`) |
| 18 | `giles_theorem1_cost_sum` | theorem | true | no | no |
| 19 | `giles_theorem1_isBigO` | theorem | true | no | no |
| 20 | `sum_piFinset_succ` | lemma | true | no | no |
| 21 | `crossDiff` | def | n/a | n/a | n/a |
| 22 | `levelDiff` | def | n/a | n/a | n/a |
| 23 | `complexityBound` | def | n/a | n/a | n/a |

## Main points for a human auditor

1. **No statement is false, vacuous or dependent on a junk value.** All 14 theorems and lemmas are true, and each has a non-degenerate instance. The identities were checked exactly on finite spaces. The allocation inequalities were checked on 20 000 random instances each.
2. **`giles_theorem1_cost_sum` is Giles's MLMC complexity theorem** in its $(\alpha,\beta,\gamma)$ form, with $\alpha\ge\frac12\min(\beta,\gamma)$ and $\varepsilon<e^{-1}$. It makes these modelling choices:
   - The estimators $Y_{\ell,n}$ are abstract.
   - `h_var` requires the variance to be *exactly* $V_\ell/n$ for every $n\ge1$. The proof only needs $\le$, but equality is what the standard i.i.d. estimator satisfies.
   - The cost is the deterministic number $\sum_{\ell\le L}N_\ell C_\ell$. It is not linked to $Y$, and $C_\ell$ has only an upper bound, so it may be negative.
   - `mlmcEstimator` and `totalCost` are not used by any statement in this packet.
   - $c_4$ is chosen after all the data, so it may depend on $\mu,P,Y,V,C$. This matches Giles's wording, but uniformity in $(\alpha,\beta,\gamma,c_1,c_2,c_3)$ is not asserted.
3. **Hypothesis hygiene.**
   - `hαβγ` is genuinely needed. With $\alpha<\frac12\min(\beta,\gamma)$ an instance satisfying all other hypotheses breaks the bound (`check_giles_theorem1`, Part 2).
   - `hC : 0 ≤ C ℓ` is needed for the Big-O version (Part 3).
   - `hα` is redundant, because it follows from `hβ`, `hγ` and `hαβγ`.
   - `hs : s.Nonempty` is redundant in `optimalN_variance` and `optimalN_cost`.
4. **Four statements omit `[IsProbabilityMeasure μ]`: `mlmc_mean`, `mlmc_variance`, `variance_sample_mean` and `indepFun_levelEstimator`.** All four remain true for every measure:
   - `mlmc_mean` needs only linearity of the integral.
   - In `mlmc_variance` and `variance_sample_mean`, independence either forces $\mu(\Omega)=1$ (Mathlib `MemLp.isProbabilityMeasure_of_indepFun`) or makes every variable a.e. $0$. `mlmc_variance` is literally Mathlib's `IndepFun.variance_sum`.
   - In `indepFun_levelEstimator`, `iIndepFun` forces $\mu(\Omega)=1$.
5. **Every junk boundary is excluded by a hypothesis.**
   - At $N=0$, `variance_sample_mean` and `variance_levelEstimator` would hold only because $0^{-1}=0$ and $x/0=0$. Both assume `0 < N`.
   - The MSE integral in Theorem 1 cannot be the junk $0$, because every $Y_{\ell,N_\ell}$ with $N_\ell\ge1$ is in $L^2$.
   - `optimalN` is $\ge1$ on $s$ under its hypotheses, so the junk $V/0$ never occurs.

## Per-declaration sections

### 1. `mse_eq_variance_add_sq_bias` (theorem)

**Rendering.** Let $\mu$ be a probability measure on $\Omega$, let $Y:\Omega\to\mathbb R$ with $Y\in L^2(\mu)$, and let $m\in\mathbb R$. Then
$$\int(Y-m)^2\,d\mu=\operatorname{Var}_\mu(Y)+\Big(\int Y\,d\mu-m\Big)^2 .$$

**Assessment.**
- **Truth.** True. Write $Y-m=(Y-\mathbb EY)+(\mathbb EY-m)$. The cross term integrates to $2(\mathbb EY-m)\int(Y-\mathbb EY)\,d\mu=0$ because $\mu(\Omega)=1$. For $Y\in L^2$, Mathlib's `variance` equals $\int(Y-\mathbb EY)^2$ (`variance_eq_integral`). Exact equality holds on 200 random finite spaces.
- **Vacuity.** Not vacuous. Example: $\Omega=\{0,1\}$ uniform, $Y(\omega)=\omega$, $m=0$ gives $\tfrac12=\tfrac14+\tfrac14$.
- **Junk.** None. Because $Y\in L^2$, the function $(Y-m)^2$ is integrable and the evariance is finite.
- **Hypotheses.** The probability instance is really used. For a measure of mass 2 the two sides are $4$ and $8$.
- **Standard result.** The bias–variance decomposition of mean-square error.

### 2. `mlmc_mean` (theorem; `μ` is an arbitrary measure)

**Rendering.** Let $\mu$ be any measure, and let $P_\ell,Y_\ell:\Omega\to\mathbb R$ ($\ell\in\mathbb N$) all be integrable. Assume $\int Y_0=\int P_0$, and $\int Y_{\ell+1}=\int(P_{\ell+1}-P_\ell)$ for all $\ell$. Then for every $L$: $\int\sum_{\ell=0}^{L}Y_\ell\,d\mu=\int P_L\,d\mu$.

**Assessment.**
- **Truth.** True for every measure. By linearity, the left side is $\int P_0+\sum_{\ell<L}\big(\int P_{\ell+1}-\int P_\ell\big)$, which telescopes to $\int P_L$. Exact checks pass, including on a measure of mass $11/2$.
- **Vacuity.** Not vacuous. Example: constants $P_\ell=2^{-\ell}$, $Y_0=1$, $Y_{\ell+1}=-2^{-\ell-1}$.
- **Junk.** None. `hPℓ` is what rules out the junk value $0$ for the integral of a non-integrable difference.
- **Standard result.** The MLMC telescoping identity $\mathbb EP_L=\mathbb EP_0+\sum_{\ell=1}^L\mathbb E[P_\ell-P_{\ell-1}]$, i.e. unbiasedness of the MLMC estimator for $\mathbb EP_L$.

### 3. `mlmc_variance` (theorem; `μ` is an arbitrary measure)

**Rendering.** Let $\mu$ be any measure, let $Y_\ell\in L^2(\mu)$ for all $\ell$, and let $Y_i$ and $Y_j$ be independent (`IndepFun`) for all distinct $i,j\in\{0,\dots,L\}$. Then $\operatorname{Var}_\mu\big(\sum_{\ell=0}^LY_\ell\big)=\sum_{\ell=0}^L\operatorname{Var}_\mu(Y_\ell)$.

**Assessment.**
- **Truth.** True for every measure.
  - If $L=0$, both sides are $\operatorname{Var}(Y_0)$.
  - If $L\ge1$ and some $Y_j$ is not a.e. $0$, pick $A=\{|Y_j|\ge c\}$ with $0<\mu(A)<\infty$. Independence with $B=\Omega$ then forces $\mu(\Omega)=1$ (Mathlib `MemLp.isProbabilityMeasure_of_indepFun`). Bienaymé's identity then applies, since all covariances vanish.
  - Otherwise every $Y_\ell$ is a.e. $0$, and both sides are genuinely $0$.
  - The statement is exactly Mathlib's `IndepFun.variance_sum` with $s=\{0,\dots,L\}$, which also has no probability assumption.
- **Vacuity.** Not vacuous: independent Rademacher variables work.
- **Junk.** None.
- **Hypotheses.** Independence does real work: with $Y_0=Y_1$ Rademacher the two sides are $4$ and $2$.
- **Standard result.** Bienaymé's identity.

### 4. `mlmc_mse` (theorem)

**Rendering.** Let $\mu$ be a probability measure. Assume $Y_\ell\in L^2$ and $P_\ell\in L^1$ for all $\ell$; $Y_0,\dots,Y_L$ are pairwise independent; $\int Y_0=\int P_0$; and $\int Y_{\ell+1}=\int(P_{\ell+1}-P_\ell)$. Then for any $m\in\mathbb R$:
$$\int\Big(\sum_{\ell=0}^LY_\ell-m\Big)^2d\mu=\sum_{\ell=0}^L\operatorname{Var}(Y_\ell)+\Big(\int P_L\,d\mu-m\Big)^2 .$$

**Assessment.**
- **Truth.** True: apply #1 to $\sum_\ell Y_\ell\in L^2$, then use #3 and #2. Exact checks pass.
- **Vacuity.** Not vacuous.
- **Junk.** None.
- **Standard result.** The MSE of the MLMC estimator equals the sum of the level variances plus the squared bias.

### 5. `levelEstimator` (def)

**Rendering.** $\widehat Y_{\ell,N}(x)=N^{-1}\sum_{n=0}^{N-1}\Delta P_\ell\big(\omega_{(\ell,n)}(x)\big)$.
- $\Delta P_\ell$ is `levelDiff`.
- $\omega_{(\ell,n)}:\Omega\to\Omega_0$ is the random input of sample $n$ on level $\ell$, so each $(\ell,n)$ has its own input.
- For $N=0$ the value is $0^{-1}\cdot0=0$.

This is the standard level-$\ell$ sample mean.

### 6. `mlmcEstimator` (def)

**Rendering.** $\widehat Y(x)=\sum_{\ell=0}^{L}\widehat Y_{\ell,N_\ell}(x)$, the standard MLMC estimator. No statement in this packet uses it.

### 7. `totalCost` (def)

**Rendering.** $\sum_{\ell=0}^{L}\sum_{n<N_\ell}\mathrm{cost}(\ell,n,x)$, a possibly random total cost. No statement in this packet uses it. Theorem 1 uses the deterministic stand-in $\sum_\ell N_\ell C_\ell$ instead.

### 8. `integral_levelEstimator` (lemma)

**Rendering.** Let $\mu$ be a probability measure on $\Omega$ and $\nu$ a measure on $\Omega_0$. Assume every $\omega_p$ is measurable with $(\omega_p)_\#\mu=\nu$, every $P_\ell\in L^1(\nu)$, and $N\ge1$. Then $\int\widehat Y_{\ell,N}\,d\mu=\int\Delta P_\ell\,d\nu$.

**Assessment.**
- **Truth.** True. $\Delta P_\ell\in L^1(\nu)$, so by change of variables each $\Delta P_\ell\circ\omega_{(\ell,n)}$ is $\mu$-integrable with integral $\int\Delta P_\ell\,d\nu$. The estimator averages $N$ equal numbers. Note that $\nu$ is automatically a probability measure. The exact check passes.
- **Hypotheses.** `hN` is essential: at $N=0$ the left side is $0$, while the script's right side is $-33/10$.
- **Vacuity.** Not vacuous. Take $\Omega=\Omega_0^{\mathbb N\times\mathbb N}$, $\mu=$ `Measure.infinitePi (fun _ => ν)` and $\omega_p=$ evaluation at $p$ (Mathlib `measurePreserving_eval_infinitePi`).
- **Junk.** None.
- **Standard result.** Unbiasedness of the sample mean.

### 9. `variance_levelEstimator` (lemma)

**Rendering.** Take the setting of #8 and assume in addition:
- the family $(\omega_p)_{p\in\mathbb N\times\mathbb N}$ is mutually independent (`iIndepFun`);
- every $P_\ell$ is measurable and in $L^2(\nu)$;
- $N\ge1$.

Then $\operatorname{Var}_\mu(\widehat Y_{\ell,N})=\operatorname{Var}_\nu(\Delta P_\ell)/N$.

**Assessment.**
- **Truth.** True. The functions $\Delta P_\ell\circ\omega_{(\ell,n)}$, $n<N$, are independent, because they are measurable maps of independent inputs. They share the variance $\operatorname{Var}_\nu(\Delta P_\ell)$, since variance is preserved under measure-preserving maps. So the variance of their mean is that variance divided by $N$. The exact check passes.
- **Vacuity.** Not vacuous: the `infinitePi` instance works, with Mathlib `iIndepFun_infinitePi`.
- **Junk.** At $N=0$ both sides would be $0$, purely because $0^{-1}=0$ and $x/0=0$. `hN` excludes this case.
- **Hypotheses.** `hPlm` (measurability) is a mild technical assumption used to carry independence through composition.
- **Standard result.** $\operatorname{Var}(\bar X_N)=\sigma^2/N$ for i.i.d. samples.

### 10. `indepFun_levelEstimator` (lemma; no probability instance)

**Rendering.** Let $\mu$ be any measure. Assume every $\omega_p$ is measurable, $(\omega_p)_p$ is mutually independent under $\mu$, and every $P_\ell$ is measurable. Then for $i\ne j$ and any $N_i,N_j\in\mathbb N$, the estimators $\widehat Y_{i,N_i}$ and $\widehat Y_{j,N_j}$ are independent.

**Assessment.**
- **Truth.** True.
  - `iIndepFun` forces $\mu(\Omega)=1$, so the missing instance does no harm.
  - The two estimators are measurable functions of the disjoint sub-families $\{\omega_{(i,n)}\}_{n<N_i}$ and $\{\omega_{(j,n)}\}_{n<N_j}$, so they are independent.
  - When $N_i=0$ the estimator is the constant $0$ (an empty sum), which is independent of everything.
- **Checks.** Exact factorisation checks pass. For $i=j$ with shared samples the joint law does not factorise, so `hij` is needed.
- **Vacuity.** Not vacuous (`infinitePi` instance).
- **Junk.** None.
- **Standard result.** Functions of disjoint blocks of an independent family are independent.

### 11. `cost_lower_bound` (theorem)

**Rendering.** Let $s$ be finite and $V,C,n:\iota\to\mathbb R$ with $V_i\ge0$, $C_i\ge0$ and $n_i>0$ for $i\in s$. Let $\tau>0$ with $\sum_{i\in s}V_i/n_i\le\tau$. Then
$$\tau^{-1}\Big(\sum_{i\in s}\sqrt{V_iC_i}\Big)^2\le\sum_{i\in s}n_iC_i .$$
Here the $n_i$ are real numbers (the continuous relaxation).

**Assessment.**
- **Truth.** True by Cauchy–Schwarz:
$$\Big(\sum_i\sqrt{V_i/n_i}\,\sqrt{n_iC_i}\Big)^2\le\Big(\sum_i V_i/n_i\Big)\Big(\sum_i n_iC_i\Big)\le\tau\sum_i n_iC_i .$$
- **Sharpness.** Equality holds at $n_i=$ `lagrangeN` (numerical deviation $<10^{-60}$). There were no violations in 20 000 random instances, including zeros in $V$ and $C$.
- **Vacuity.** Not vacuous. Example: $s=\{1,2\}$, $V=(1,4)$, $C=(1,1)$, $n=(2,4)$, $\tau=3/2$ gives $6\le6$.
- **Junk.** None.
- **Standard result.** The optimal-allocation (Lagrange-multiplier) lower bound for MLMC: with total variance budget $\tau$, the minimal cost is $\tau^{-1}\big(\sum\sqrt{V_\ell C_\ell}\big)^2$.

### 12. `sumSqrtVC` (def)

**Rendering.** $S(s,V,C)=\sum_{i\in s}\sqrt{V_iC_i}$, with $\sqrt{x}=0$ for $x<0$.

### 13. `lagrangeN` (def)

**Rendering.** $N^*_i=\tau^{-1}\sqrt{V_i/C_i}\;S(s,V,C)$, the real sample size that is optimal under a Lagrange multiplier for variance target $\tau$. Junk conventions: $C_i=0$ gives $V_i/C_i=0$, and $\tau=0$ gives $\tau^{-1}=0$.

### 14. `optimalN` (def)

**Rendering.** $\lceil N^*_i\rceil_+\in\mathbb N$, which is $0$ when $N^*_i\le0$.

### 15. `optimalN_variance` (theorem)

**Rendering.** Let $s\ne\emptyset$, $V_i,C_i>0$ on $s$, and $\tau>0$. Then $\sum_{i\in s}V_i/\lceil N^*_i\rceil_+\le\tau$.

**Assessment.**
- **Truth.** True. Since $S>0$, we have $\lceil N^*_i\rceil_+\ge N^*_i>0$. Also $V_i/N^*_i=\tau\sqrt{V_iC_i}/S$, and these terms sum to $\tau$. There were no violations in 20 000 instances.
- **Junk.** None. No `optimalN` value was $0$ in the random instances, so the junk path $V/0=0$ is never taken.
- **Vacuity.** Not vacuous. Example: $s=\{0\}$, $V=C=\tau=1$ gives $1\le1$.
- **Hypotheses.** `hs` is redundant, because for empty $s$ the claim is $0\le\tau$.
- **Standard result.** The rounded-up Lagrange allocation meets the variance target, as in Giles's proof of the complexity theorem.

### 16. `optimalN_cost` (theorem)

**Rendering.** Under the same hypotheses as #15:
$$\sum_{i\in s}\lceil N^*_i\rceil_+C_i\le\tau^{-1}\Big(\sum_{i\in s}\sqrt{V_iC_i}\Big)^2+\sum_{i\in s}C_i .$$

**Assessment.**
- **Truth.** True, because $\lceil x\rceil_+<x+1$ for $x\ge0$ and $N^*_iC_i=\tau^{-1}\sqrt{V_iC_i}\,S$. There were no violations in 20 000 instances.
- **Hypotheses.** `hs` is redundant.
- **Junk.** None.
- **Standard result.** The "$+\sum_\ell C_\ell$" rounding overhead in Giles's proof.

### 17. `variance_sample_mean` (theorem; `μ` is an arbitrary measure)

**Rendering.** Let $\mu$ be any measure. Assume $X_n\in L^2(\mu)$ and $\operatorname{Var}(X_n)=v$ for all $n\in\mathbb N$, that $X_0,\dots,X_{N-1}$ are pairwise independent, and that $N\ge1$. Then $\operatorname{Var}\big(N^{-1}\sum_{n<N}X_n\big)=v/N$.

**Assessment.**
- **Truth.** True for every measure.
  - `variance_const_mul` holds for arbitrary measures.
  - The sum is handled as in #3. If $N\ge2$ and some $X_n$ with $n<N$ is not a.e. $0$, independence forces a probability measure. If every $X_n$ with $n<N$ is a.e. $0$, then $v=\operatorname{Var}(X_0)=0$ and both sides are genuinely $0$.
  - $N=1$ is immediate.
- **Hypotheses.** Only equal variances are required, not identical laws. The script uses two different laws, both with variance $2$. `hX` and `hvar` quantify over all $n$ although only $n<N$ is needed; this is harmless.
- **Junk.** At $N=0$ the statement would hold only because $0^{-1}=0$ and $v/0=0$. `hN` excludes this.
- **Vacuity.** Not vacuous.
- **Standard result.** The variance of the mean of pairwise-independent variables with equal variance (Bienaymé).

### 18. `giles_theorem1_cost_sum` (theorem)

**Rendering.** Let $\mu$ be a probability measure. The data are:
- $P:\Omega\to\mathbb R$ and $P_\ell:\Omega\to\mathbb R$ for $\ell\in\mathbb N$;
- $Y_{\ell,n}:\Omega\to\mathbb R$, the level-$\ell$ estimator with $n$ samples;
- real numbers $V_\ell$ and $C_\ell$;
- real constants $\alpha,\beta,\gamma,c_1,c_2,c_3>0$ with $\alpha\ge\tfrac12\min(\beta,\gamma)$.

The hypotheses are:
- $P\in L^1$ and every $P_\ell\in L^1$.
- $Y_{\ell,n}\in L^2$ for $n\ge1$.
- `hind`: for every $N:\mathbb N\to\mathbb N_{\ge1}$, the family $(Y_{\ell,N_\ell})_{\ell\in\mathbb N}$ is pairwise independent. Equivalently, $Y_{i,n}\perp Y_{j,n'}$ for all $i\ne j$ and all $n,n'\ge1$.
- (i) $|\mathbb E[P_\ell-P]|\le c_12^{-\alpha\ell}$.
- (ii) $\mathbb EY_{0,n}=\mathbb EP_0$ and $\mathbb EY_{\ell+1,n}=\mathbb E[P_{\ell+1}-P_\ell]$ for $n\ge1$.
- `h_var`: $\operatorname{Var}Y_{\ell,n}=V_\ell/n$ for $n\ge1$.
- (iii) $V_\ell\le c_22^{-\beta\ell}$.
- (iv) $C_\ell\le c_32^{\gamma\ell}$, with no sign condition on $C_\ell$.

Conclusion: there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N_{\ge1}$ with
$$\mathbb E\Big[\Big(\sum_{\ell=0}^{L}Y_{\ell,N_\ell}-\mathbb EP\Big)^2\Big]<\varepsilon^2\quad\text{and}\quad\sum_{\ell=0}^{L}N_\ell C_\ell\le c_4\cdot\mathrm{cB}(\alpha,\beta,\gamma,\varepsilon),$$
where $\mathrm{cB}$ is `complexityBound` (#23).

On quantifier order: $c_4$ comes after all the data but before $\varepsilon$, and $L$ and $N$ depend on $\varepsilon$.

**Assessment.**
- **Truth.** True, by the standard proof:
  - By #4 with $m=\mathbb EP$, $\text{MSE}=\sum_{\ell\le L}V_\ell/N_\ell+(\mathbb E[P_L-P])^2$.
  - Take $L=\max(0,\lceil\alpha^{-1}\log_2(2c_1/\varepsilon)\rceil)$, so the squared bias is at most $\varepsilon^2/4$.
  - Take $N_\ell=$ `optimalN` on $\{0,\dots,L\}$ with $\bar V_\ell=c_22^{-\beta\ell}$, $\bar C_\ell=c_32^{\gamma\ell}$ and $\tau=\varepsilon^2/2$. Then the variance is at most $\varepsilon^2/2$, so $\text{MSE}\le\tfrac34\varepsilon^2<\varepsilon^2$.
  - The cost satisfies $\sum_\ell N_\ell C_\ell\le\sum_\ell N_\ell\bar C_\ell\le2\varepsilon^{-2}\big(\sum_\ell\sqrt{\bar V_\ell\bar C_\ell}\big)^2+\sum_\ell\bar C_\ell$ (#16). The first inequality uses $N_\ell\ge0$, which is why negative $C_\ell$ are harmless.
  - The sum $\sum_\ell\sqrt{\bar V_\ell\bar C_\ell}$ is $O(1)$, $O(L+1)$ or $O(2^{(\gamma-\beta)L/2})$ in the three regimes. Moreover $2^L\lesssim\varepsilon^{-1/\alpha}$, and $L+1\lesssim|\log\varepsilon|$ because $\varepsilon<e^{-1}$.
  - Finally $\sum_\ell\bar C_\ell=O(\varepsilon^{-\gamma/\alpha})$, which is dominated by $\mathrm{cB}$ exactly because $\alpha\ge\tfrac12\min(\beta,\gamma)$.
- **Numerical evidence** (`check_giles_theorem1`). In 8 configurations, including the boundary $\alpha=\tfrac12\min(\beta,\gamma)$ in each regime and unequal constants, $\text{MSE}<\varepsilon^2$ always held. The ratio $\text{cost}/\mathrm{cB}$ stayed bounded for $\varepsilon\in[3.7\cdot10^{-16},e^{-1}]$, with suprema between 20 and 1200 and stable tails.
- **Vacuity.** Not vacuous (`check_instance`). The instance is:
  - $\Omega=[0,1)$ with Lebesgue measure, and $r_\ell$ the Rademacher functions;
  - $P=0$ and $P_\ell=2^{-\ell}$;
  - $Y_{\ell,n}=m_\ell+2^{-\ell}n^{-1/2}r_\ell$, with $m_0=1$ and $m_{\ell+1}=-2^{-\ell-1}$;
  - $V_\ell=4^{-\ell}$ and $C_\ell=2^\ell$;
  - $(\alpha,\beta,\gamma)=(1,2,1)$ and $c_i=1$.

  All hypotheses were verified exactly. For $\varepsilon=0.3,0.2,0.1$, the directly computed MSE matched the formula and was below $\varepsilon^2$. A second, standard instance comes from #8–#10 (`infinitePi`), with $Y_{\ell,n}=\widehat Y_{\ell,n}$ and $V_\ell=\operatorname{Var}_\nu(\Delta P_\ell)$.
- **Junk.** None. Each $Y_{\ell,N_\ell}\in L^2$, so the MSE integrand is integrable and the integral is not the junk $0$. All variances are genuine because of $L^2$. Since $\varepsilon>0$, the real powers are ordinary, and $\log\varepsilon<-1$.
- **Hypotheses.**
  - `h_var` is an equality. The proof only needs $\le$, as in Giles (2008), condition (iii).
  - $C_\ell$ may be negative. This makes the statement more general, not weaker.
  - `hα` is redundant, and `hc₁`–`hc₃ > 0` are harmless.
  - `hαβγ` is necessary. With $(\alpha,\beta,\gamma)=(0.25,4,1)$ and the bias exactly $2^{-\alpha\ell}$, every admissible choice has $\text{cost}\ge\sum_{\ell\le L_{\min}}2^\ell$. Relative to $\varepsilon^{-2}$ this grows like $\varepsilon^{-2}$ (Part 2).
  - $c_4$ may depend on all the data.
  - The cost is an abstract number and is not tied to $Y$ or to `totalCost`.
- **Standard result.** The MLMC complexity theorem: Giles (2008), Operations Research, Thm 3.1; in $(\alpha,\beta,\gamma)$ form, Cliffe–Giles–Scheichl–Teckentrup (2011), Thm 1, and Giles (2015), Acta Numerica, Thm 1.

### 19. `giles_theorem1_isBigO` (theorem)

**Rendering.** The data and hypotheses are those of #18, plus $C_\ell\ge0$. Conclusion: there exist functions $L:\mathbb R\to\mathbb N$ and $N:\mathbb R\to(\mathbb N\to\mathbb N)$ such that:
- (a) for every $\varepsilon\in(0,e^{-1})$, all $N(\varepsilon)_\ell\ge1$ and the MSE is below $\varepsilon^2$;
- with $\mathrm{cost}(\varepsilon)=\sum_{\ell\le L(\varepsilon)}N(\varepsilon)_\ell C_\ell$, as $\varepsilon\to0^+$:
  - (b) if $\gamma<\beta$, $\mathrm{cost}=O(\varepsilon^{-2})$;
  - (c) if $\beta=\gamma$, $\mathrm{cost}=O(\varepsilon^{-2}(\log\varepsilon)^2)$;
  - (d) if $\beta<\gamma$, $\mathrm{cost}=O(\varepsilon^{-2-(\gamma-\beta)/\alpha})$.

**Assessment.**
- **Truth.** True. For $\varepsilon\in(0,e^{-1})$, choose $L$ and $N$ as in #18 (arbitrary elsewhere). With $C_\ell\ge0$ we get $|\text{cost}|=\text{cost}\le c_4\,\mathrm{cB}$, and $\mathrm{cB}$ equals the relevant rate in each regime.
- **Hypotheses.** `hC` is needed for this form. With $C_\ell=-2^{2^\ell}$ (allowed by (iv)) and exact bias, $|\text{cost}|\ge2^{2^{L_{\min}}}$, which is super-polynomial (Part 3).
- **Vacuity.** Not vacuous. Each regime is realised by the Rademacher instance with a suitable choice of $(\beta,\gamma)$.
- **Junk.** None. The rates are positive near $0^+$, so the Big-O is not trivial.
- **Standard result.** The same theorem, in asymptotic form.

### 20. `sum_piFinset_succ` (lemma)

**Rendering.** For $t:\{0,\dots,D\}\to\mathrm{Finset}\,\mathbb N$ and $f:\mathbb N^{D+1}\to\mathbb R$:
$$\sum_{\ell\in t_0\times\cdots\times t_D}f(\ell)=\sum_{j\in t_0}\;\sum_{m\in t_1\times\cdots\times t_D}f(j,m).$$
Here `Fin.tail t` $=(t_1,\dots,t_D)$ and `Fin.cons j m` $=(j,m_1,\dots,m_D)$.

**Assessment.**
- **Truth.** True: $\ell\mapsto(\ell_0,\operatorname{tail}\ell)$ is a bijection with inverse `Fin.cons`. It held in 300 random cases, including empty factors.
- **Vacuity and junk.** Not vacuous; no junk.
- **Standard result.** Iterated summation over a product index set (Fubini for finite sums).

### 21. `crossDiff` (def)

**Rendering.** For $D=0$, the value is $p(\ell)$. For $D+1$ dimensions:
$$\mathrm{crossDiff}\big(p(\ell_0,\cdot)\big)(\ell_{1..D})-[\ell_0>0]\cdot\mathrm{crossDiff}\big(p(\ell_0-1,\cdot)\big)(\ell_{1..D}).$$
Unfolding the recursion,
$$\mathrm{crossDiff}\,p\,\ell=\Big(\prod_i\Delta_i\Big)p(\ell)=\sum_{S\subseteq\{i:\ell_i>0\}}(-1)^{|S|}\,p(\ell-e_S),$$
where $\Delta_ip(\ell)=p(\ell)-p(\ell-e_i)$ if $\ell_i>0$ and $\Delta_ip(\ell)=p(\ell)$ otherwise.
- The natural-number subtraction $\ell_0-1$ is guarded by the test $\ell_0=0$, so it never truncates.
- The script confirms the inclusion–exclusion form and the telescoping identity $\sum_{k\le\ell}\mathrm{crossDiff}\,p\,k=p(\ell)$.
- For $D=1$ it reduces to `levelDiff`.

This is the mixed difference of multi-index Monte Carlo (Haji-Ali, Nobile and Tempone).

### 22. `levelDiff` (def)

**Rendering.** $\Delta P_0=P_0$ and $\Delta P_{\ell+1}=P_{\ell+1}-P_\ell$, pointwise. This is the standard MLMC level correction.

### 23. `complexityBound` (def)

**Rendering.**
$$\mathrm{cB}(\alpha,\beta,\gamma,\varepsilon)=\begin{cases}\varepsilon^{-2}&\text{if }\gamma<\beta,\\ \varepsilon^{-2}(\log\varepsilon)^2&\text{if }\beta=\gamma,\\ \varepsilon^{-2-(\gamma-\beta)/\alpha}&\text{otherwise, i.e. }\beta<\gamma.\end{cases}$$
The exponents are real powers. For $\varepsilon\in(0,e^{-1})$ all three values are genuine positive numbers, and $(\log\varepsilon)^2>1$. For $\varepsilon\le0$ the values would be junk, but no statement uses them there. These are the three cost regimes of Giles's theorem.
