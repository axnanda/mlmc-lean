# Blind read-back report: packet R42 (Lévy truncation)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round24/packet_R42_levy.lean` |
| declarations audited | 16 theorems + 15 definitions (12 in the packet, 3 appended) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round24/work_R42_levy/` (`cp_checks.py`, `levy_discrete_checks.py`, `stable_like.py`, `complexity.py`, each with its `.out`; `scratch.lean`/`print.lean` with `print.out` = elaboration check) |

I compiled the packet in a separate namespace with `import MlmcLean`. All 16 statements elaborate, and each gives only the expected `sorry` warning. I printed the key statements with `pp.parens`/`pp.coercions` (`print.out`) to confirm the parse:
- `∑ x ∈ s, body` takes its body at precedence 67, so `∑ …, a - c` means $(\sum a) - c$.
- `∫ x, body ∂μ` takes its body at precedence 60, so `∫ ω, Φ A - Φ X ∂μ` means $\int(\Phi A-\Phi X)$.
- Every `T`, `r`, `K : ℝ≥0` is cast to ℝ (or to ℂ) where it is used.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `charFun_cpSum` | theorem | true | no | no |
| 2 | `cp_thinning` | theorem | true | no | no |
| 3 | `cp_thinning_indep` | theorem | true | no | no |
| 4 | `cpSum_moments` | theorem | true | no | no |
| 5 | `levy_coarse_map_eq` | theorem | true | no | no |
| 6 | `levy_truncation_2_4` | theorem | true | no | no (when $\Phi\circ X$ is not integrable both sides are $0$, consistently) |
| 7 | `levy_correction_moments` | theorem | true | no | no |
| 8 | `levy_correction_variance_le` | theorem | true | no | no |
| 9 | `bandApprox_sq_sub` | theorem | true | no | no |
| 10 | `levy_truncation_limit` | theorem | true | no | no |
| 11 | `bandApprox_map_eq` | theorem | true | no | no |
| 12 | `integral_band_count` | theorem | true | no | no |
| 13 | `levy_expected_cost` | theorem | true | no | no |
| 14 | `levy_truncation_theorem1` | theorem | true | no | no |
| 15 | `exists_levy_bandLaws` | theorem | true | no | no |
| 16 | `levy_stableLike_theorem1` | theorem | true | no | no |
| D | `cpInputLaw`, `cpSum`, `levySet`, `levyComp`, `levyFine`, `levyMid`, `levyBand`, `bandInputLaw`, `bandApprox`, `bandTerm`, `stableLikeDensity`, `stableLikeLevy`, `complexityBound`, `blockMean`, `fineCoarseDiff` | defs | n/a | n/a | `stableLikeDensity` uses `rpow` of a non-positive base only off its support (irrelevant); `blockMean` with $N=0$ gives $0$, but every use has $N_\ell>0$ |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.** I checked every theorem by hand. I also checked the compound-Poisson facts and the Lévy identities with exact enumeration, for discrete marks or a discrete $\nu$, and found agreement to about $10^{-40}$. I checked the stable-like closed forms by quadrature. All are non-vacuous; the stable-like measure $c z^{-1-Y}\mathbf 1_{(0,1]}$ is an instance for 9–16.
2. **`levy_truncation_theorem1` / `levy_stableLike_theorem1`.** These are Giles' MLMC complexity theorem with rates $\alpha=(2-Y)/2$, $\beta=2-Y$, $\gamma=Y$. Since $\alpha=\beta/2$, the condition $\alpha\ge\frac12\min(\beta,\gamma)$ holds, and $2+(\gamma-\beta)/\alpha=\gamma/\alpha$. That means the rounding term $\sum_\ell C_\ell\sim\varepsilon^{-\gamma/\alpha}$ never dominates. A numerical allocation (`complexity.py`) gives a bounded cost/complexityBound ratio for $Y=0.5,1,1.5,1.9$. In closed form the bounds are $\varepsilon^{-2}$ for $Y<1$, $\varepsilon^{-2}\log^2\varepsilon$ for $Y=1$, and $\varepsilon^{-2Y/(2-Y)}$ for $Y>1$.
3. **How $X$ is defined.** The limit $X$ is existential. It is pinned down a.e. only as the $L^2$ limit of the band approximations, because $\mathbb E(X-\text{bandApprox}_\ell)^2=T\int_{|z|<\delta_\ell}z^2\,d\nu\to0$. So the target $\mathbb E\Phi(X)$ is the right one. However, no statement says that $X$ has the Lévy–Khintchine law $\exp\big(T\int(e^{itz}-1-itz\mathbf 1_{|z|<1})\,\nu(dz)\big)$. The model is a pure-jump Lévy variable at the fixed time $T$, with no Gaussian part and no drift.
4. **Possibly redundant hypotheses (harmless).**
   - In `bandApprox_sq_sub`, the hypotheses `hν` and `hδpos` are implied for this purpose by `hband` (which forces $T\nu(\text{band}_k)<\infty$).
   - `levy_truncation_limit` does not need `hlarge`.
   - `levy_truncation_theorem1` really does need `hlarge`: it is used for the level-0 variance and for $\Phi(X)\in L^1$.
   - `hc : 0 < c` in theorem 16 is necessary: with $c\le0$ the density clips to $0$.
5. **Junk-value checks.**
   - `.toReal` of $\nu(\{|z|\ge 2^{-\ell}\})$ in `hcount` and in the cost formulas would trivialise if that measure were $\infty$. It is excluded by `hν` (and by `hband` when $T>0$).
   - Every set integral that appears is of a function that is genuinely integrable whenever $T>0$. When $T=0$ both sides are $0$ for real reasons, since then $r=\Lambda_k=0$.
   - `blockMean` is used only with $N_\ell>0$.
6. **Unused definition.** `bandTerm` is defined but used in none of the 16 statements.

---

## Definitions

**`cpInputLaw r μ`** ($\mu$ a probability measure). The measure $\mathrm{Poi}(r)\otimes\mu^{\otimes\mathbb N}$ on $\mathbb N\times\mathbb R^{\mathbb N}$. A sample is $(n,(x_i)_{i\in\mathbb N})$: $n$ is a Poisson count and the $x_i$ are i.i.d. marks. Note that `poissonMeasure 0` $=\delta_0$, because $0^0=1$.

**`cpSum f (n,x)`** $=\sum_{i<n} f(x_i)$, the compound-Poisson sum.

**`levySet δ`** $=\{z:\delta\le|z|\}$. **`levyMid δ δ'`** $=\{z:\delta\le|z|<\delta'\}$.

**`levyComp ν T δ`** $=T\int_{\{\delta\le|z|<1\}} z\,\nu(dz)$, the compensator of the jumps of size in $[\delta,1)$.

**`levyFine ν T δ (n,x)`** $=\sum_{i<n}\mathbf 1_{\{|x_i|\ge\delta\}}x_i-\text{levyComp}(\nu,T,\delta)$. This is the $\delta$-truncated compensated jump sum.

**`levyBand δ`**: $\text{band}_0=\{|z|\ge\delta_0\}$ and $\text{band}_{k+1}=\{\delta_{k+1}\le|z|<\delta_k\}$.

**`bandInputLaw Λ M`** $=\bigotimes_{k\in\mathbb N}\big(\mathrm{Poi}(\Lambda_k)\otimes M_k^{\otimes\mathbb N}\big)$. This is an independent compound-Poisson input for each band.

**`bandApprox ν T δ ℓ ω`** $=\sum_{k\le\ell}\text{cpSum}(\mathbf 1_{\text{band}_k}\mathrm{id})(\omega_k)-\text{levyComp}(\nu,T,\delta_\ell)$.

**`bandTerm ν T δ k (n,x)`** $=\text{cpSum}(\mathbf 1_{\text{band}_k}\mathrm{id})(n,x)-T\int_{\text{band}_k}z\,d\nu$, the centred band contribution. It is unused.

**`stableLikeDensity c Y z`** $=\max(c\,z^{-1-Y},0)\in\mathbb R_{\ge0}$, where `rpow` is used. For $z\le0$ the value is junk, but it is never used.

**`stableLikeLevy c Y`** $=\max(c z^{-1-Y},0)\,\mathbf 1_{(0,1]}(z)\,dz$. For $c>0$ this is the one-sided stable-like Lévy measure on $(0,1]$.

**`complexityBound α β γ ε`** is
- $\varepsilon^{-2}$ if $\gamma<\beta$;
- $\varepsilon^{-2}(\log\varepsilon)^2$ if $\beta=\gamma$;
- $\varepsilon^{-2-(\gamma-\beta)/\alpha}$ otherwise.

**`blockMean f ω i N x`** $=N^{-1}\sum_{n<N}f_i(\omega(i,n)(x))$. With $\omega=(p,x)\mapsto x\,p$ it is the sample mean at level $i$ over the samples $x(i,0),\dots,x(i,N-1)$.

**`fineCoarseDiff Pf Pc`**: level $0\mapsto P^f_0$ and level $\ell+1\mapsto P^f_{\ell+1}-P^c_\ell$, evaluated on the same input.

---

## 1. `charFun_cpSum`

**Rendering.** Let $r\ge0$, let $\mu$ be a probability measure on $\mathbb R$, let $f$ be measurable, and let $t\in\mathbb R$. Let $S=\sum_{i<N}f(x_i)$ with $N\sim\mathrm{Poi}(r)$ independent of $x_i\overset{iid}\sim\mu$. Then
$$\varphi_S(t)=\mathbb E e^{itS}=\exp\Big(r\int(e^{itf(x)}-1)\,\mu(dx)\Big).$$

**Assessment.**
- **Truth:** true. Conditioning on $N=n$ gives $\sum_n e^{-r}\frac{r^n}{n!}\varphi_{f}(t)^n=e^{r(\varphi_f(t)-1)}$. The integrand is bounded and measurable, so it is integrable. `cp_checks.py` gives agreement to $10^{-41}$.
- **Vacuity:** none; take $\mu=\delta_1$ and $f=\mathrm{id}$.
- **Junk:** none. Measurability of $f$ is needed so that the pushforward is non-zero.
- **Standard result:** the Lévy–Khintchine/characteristic function of a compound Poisson law.

## 2. `cp_thinning`

**Rendering.** Let $\mu,\mu'$ be probability measures, $A$ measurable, and $r'\mu'=r\,\mu|_A$. Then the law of $\sum_{i<N}\mathbf 1_A(x_i)x_i$ under $\mathrm{CP}(r,\mu)$ equals the law of $\sum_{i<N'}x'_i$ under $\mathrm{CP}(r',\mu')$.

**Assessment.**
- **Truth:** true. Comparing total masses gives $r'=r\mu(A)$, so $\mu'=\mu(\cdot\mid A)$ when $r'>0$. Both characteristic functions equal $\exp\big(r\int_A(e^{itx}-1)d\mu\big)$, because outside $A$ the integrand $e^{0}-1$ vanishes. When $r'=0$ both laws are $\delta_0$, and $\mu'$ is irrelevant.
- **Numerics:** checked exactly in `cp_checks.py`, including the case $\mu(A)=0$.
- **Vacuity:** none; take $\mu=\frac12(\delta_1+\delta_{-1})$, $A=(0,\infty)$, $r=2$, $r'=1$, $\mu'=\delta_1$.
- **Junk:** none.
- **Standard result:** thinning of a marked Poisson process (restriction theorem).

## 3. `cp_thinning_indep`

**Rendering.** Let $A$ be measurable. Under $\mathrm{CP}(r,\mu)$, the random variables $\sum_{i<N}\mathbf 1_A(x_i)x_i$ and $\sum_{i<N}\mathbf 1_{A^c}(x_i)x_i$ are independent (`IndepFun` for real-valued maps, Borel σ-algebras).

**Assessment.**
- **Truth:** true. The joint characteristic function is $\exp\big(r\int_A(e^{isx}-1)\,d\mu+r\int_{A^c}(e^{itx}-1)\,d\mu\big)$, which factorises. Exact check in `cp_checks.py`: max $|\text{joint}-\text{product}|\approx10^{-41}$.
- **Vacuity:** none.
- **Junk:** none.
- **Standard result:** the Poisson colouring theorem.

## 4. `cpSum_moments`

**Rendering.** Let $g$ be measurable with $g\in L^2(\mu)$, and let $S=\text{cpSum}\,g$ under $\mathrm{CP}(r,\mu)$. Then:
- $S\in L^2$;
- $\mathbb E S=r\int g\,d\mu$;
- $\mathbb E(S-r\int g\,d\mu)^2=r\int g^2\,d\mu$.

**Assessment.**
- **Truth:** true. We have $\mathbb E S^2=r\,\mathbb Eg^2+r^2(\mathbb Eg)^2$, by Wald's identities. Exact check: $3.06=3.06$ and $10.2=10.2$.
- **Vacuity:** none.
- **Junk:** none, because $L^2$ membership is the first conjunct.
- **Standard result:** the mean and variance of a compound Poisson sum.

## 5. `levy_coarse_map_eq`

**Rendering.** Suppose $\delta\le\delta'$, $r\mu=T\nu|_{\{|z|\ge\delta\}}$ and $r'\mu'=T\nu|_{\{|z|\ge\delta'\}}$, with $\mu,\mu'$ probability measures. Then the law of $\text{levyFine}_{\delta'}$ under $\mathrm{CP}(r,\mu)$ equals its law under $\mathrm{CP}(r',\mu')$.

**Assessment.**
- **Truth:** true. Apply #2 with $A=\{|z|\ge\delta'\}$: $r\mu|_A=T\nu|_{\{|z|\ge\delta\}\cap A}=T\nu|_A=r'\mu'$, using $\delta\le\delta'$. Then subtract the same constant on both sides. The hypotheses force $T\nu(\{|z|\ge\delta\})<\infty$ (or $T=0$, hence $r=0$). Exact check in `levy_discrete_checks.py`.
- **Vacuity:** none; take $\nu=\delta_{1/2}+\delta_2$, $T=1$, $\delta=\tfrac14$, $\delta'=1$.
- **Junk:** none.
- **Standard result:** the coarse truncation is a thinning of the fine one, giving consistency of truncation levels.

## 6. `levy_truncation_2_4`

**Rendering.** Same hypotheses as #5, and $\Phi$ measurable. Then $\mathbb E_{\mathrm{CP}(r,\mu)}\Phi(\text{levyFine}_{\delta'})=\mathbb E_{\mathrm{CP}(r',\mu')}\Phi(\text{levyFine}_{\delta'})$, as Bochner integrals.

**Assessment.**
- **Truth:** true, from #5 and `integral_map`.
- **Integrability:** this is not asserted. If $\Phi(\text{levyFine})$ is not integrable, both sides are $0$. Integrability is a property of the law, so it holds on both sides or neither, and the statement is a genuine equality in law.
- **Vacuity:** none.
- **Standard result:** the coarse level can be simulated either from its own input or by thinning the fine input. This is what makes the MLMC coupling unbiased (telescoping).

## 7. `levy_correction_moments`

**Rendering.** Suppose $\delta\le\delta'\le1$ and $r\mu=T\nu|_{\{|z|\ge\delta\}}$. Let $D=\text{levyFine}_\delta-\text{levyFine}_{\delta'}$. Then:
- (a) for every $\omega$, $D(\omega)=\sum_{i<n}\mathbf 1_{\{\delta\le|x_i|<\delta'\}}x_i-T\int_{\delta\le|z|<\delta'}z\,d\nu$;
- (b) $D\in L^2(\mathrm{CP}(r,\mu))$;
- (c) $\mathbb ED=0$;
- (d) $\mathbb ED^2=T\int_{\delta\le|z|<\delta'}z^2\,d\nu$.

**Assessment.**
- **Truth:** true.
- **(a)** follows from additivity of cpSum and from $\{\delta\le|z|<1\}=\{\delta\le|z|<\delta'\}\sqcup\{\delta'\le|z|<1\}$, which uses $\delta'\le1$. The needed integrability holds: when $T>0$, the measure $\nu(\{|z|\ge\delta\})=r/T$ is finite and $|z|<1$ on these sets. When $T=0$ both compensators are $0$.
- **(b)–(d)** follow from #4 with $g=\mathbf 1_{\text{mid}}\mathrm{id}$, which is bounded by $\delta'$, together with $r\int\mathbf 1_{\text{mid}}z\,d\mu=T\int_{\text{mid}}z\,d\nu$.
- **Numerics:** exact check gives $\mathbb ED^2=0.4875$, matching the formula.
- **Hypotheses:** $\delta'\le1$ is necessary for (a).
- **Vacuity:** none; take $\nu=\delta_{1/2}$, $T=1$, $\delta=\tfrac14$, $\delta'=1$.
- **Junk:** none.
- **Standard result:** the level correction is a centred compound Poisson sum of the jumps in $[\delta,\delta')$.

## 8. `levy_correction_variance_le`

**Rendering.** Same hypotheses as #7, and $\Phi$ is $K$-Lipschitz. Then $\Phi(\text{levyFine}_\delta)-\Phi(\text{levyFine}_{\delta'})\in L^2$, and its variance is at most $K^2\,T\int_{\delta\le|z|<\delta'}z^2\,d\nu$.

**Assessment.**
- **Truth:** true: $\mathrm{Var}\le\mathbb E(\cdot)^2\le K^2\mathbb ED^2$, then apply #7(d). `variance` is the genuine variance, because the $L^2$ conjunct is proved.
- **Vacuity:** none.
- **Junk:** none.
- **Standard result:** the MLMC variance bound $V_\ell\lesssim\int_{\text{band}}z^2\,d\nu$.

## 9. `bandApprox_sq_sub`

**Rendering.** Assume:
- $\int\min(1,z^2)\,d\nu<\infty$;
- $\delta_k>0$, $\delta$ antitone, $\delta_0\le1$;
- $M_k$ are probability measures with $\Lambda_kM_k=T\nu|_{\text{band}_k}$;
- $\ell\le\ell'$.

Then $\text{bandApprox}_{\ell'}-\text{bandApprox}_\ell\in L^2(\text{bandInputLaw})$, and its second moment is $T\int_{\delta_{\ell'}\le|z|<\delta_\ell}z^2\,d\nu$.

**Assessment.**
- **Truth:** true. The difference is $\sum_{k=\ell+1}^{\ell'}\big(\text{cpSum}_k-T\int_{\text{band}_k}z\,d\nu\big)$. This uses $\text{levyComp}(\delta_{\ell'})-\text{levyComp}(\delta_\ell)=T\int_{[\delta_{\ell'},\delta_\ell)}z\,d\nu$, valid since $\delta_\ell\le1$. The summands are independent and centred, and their variances add up over the disjoint bands.
- **Numerics:** exact check gives $0.7575=0.7575$.
- **Hypotheses:** `hν` and `hδpos` are stronger than this conclusion needs (`hband` already gives finiteness), but they are natural.
- **Vacuity:** none (stable-like $\nu$, $\delta_k=2^{-k}$, laws from #15).
- **Junk:** none.

## 10. `levy_truncation_limit`

**Rendering.** Assume the hypotheses of #9 and $\delta_k\to0$. Then there is $X:\Omega\to\mathbb R$ such that:
- $X-\text{bandApprox}_0\in L^2$;
- for every $\ell$, $(X-\text{bandApprox}_\ell)^2$ is integrable and $\mathbb E(X-\text{bandApprox}_\ell)^2=T\int_{|z|<\delta_\ell}z^2\,d\nu$;
- $T\int_{|z|<\delta_\ell}z^2\,d\nu\to0$;
- for every $K$-Lipschitz $\Phi$ and every $\ell$, $\Phi(\text{bandApprox}_\ell)-\Phi(X)$ is integrable and $|\mathbb E[\Phi(\text{bandApprox}_\ell)-\Phi(X)]|\le K\sqrt{T\int_{|z|<\delta_\ell}z^2\,d\nu}$.

**Assessment.**
- **Truth:** true. Take $X=\text{bandApprox}_0+\sum_{k\ge1}\text{bandTerm}_k(\omega_k)$, which is an $L^2$-convergent series of independent centred terms with total variance $T\int_{0<|z|<\delta_0}z^2\le T\int\min(1,z^2)<\infty$. The tail over $k>\ell$ has variance $T\int_{0<|z|<\delta_\ell}z^2$. This equals the stated integral, since $z^2=0$ at $z=0$ and the bands $k>\ell$ cover $\{0<|z|<\delta_\ell\}$ because $\delta_k\downarrow0$.
- **Limit:** follows by dominated convergence with dominating function $\min(1,z^2)$.
- **Weak error:** Jensen/Cauchy–Schwarz plus the Lipschitz bound.
- **Vacuity:** none.
- **Junk:** none; the integrals are finite by `hν`.
- **Note:** $X$ is determined a.e. as the $L^2$ limit. Its Lévy–Khintchine law is not stated.
- **Standard result:** the Lévy–Itô small-jump $L^2$ limit, with the strong/weak truncation error $\sigma^2(\delta)=\int_{|z|<\delta}z^2\,d\nu$ (as in Asmussen–Rosiński and Dereich–Heidenreich).

## 11. `bandApprox_map_eq`

**Rendering.** Assume $\delta$ antitone, $\Lambda_kM_k=T\nu|_{\text{band}_k}$ and $r\mu=T\nu|_{\{|z|\ge\delta_\ell\}}$. Then the law of $\text{bandApprox}_\ell$ under bandInputLaw equals the law of $\text{levyFine}_{\delta_\ell}$ under $\mathrm{CP}(r,\mu)$.

**Assessment.**
- **Truth:** true. By antitonicity, the bands $0..\ell$ are disjoint with union $\{|z|\ge\delta_\ell\}$. A sum of independent $\mathrm{CP}(\Lambda_k,M_k)$ is $\mathrm{CP}$ with intensity $\sum_k\Lambda_kM_k=T\nu|_{\{|z|\ge\delta_\ell\}}=r\mu$, which can be seen by comparing characteristic functions. The indicators are a.s. irrelevant because $M_k$ (resp. $\mu$) is carried by the band (resp. the set) when the rate is positive. Both sides subtract the same constant.
- **Numerics:** exact check for $\ell=0..3$ gives differences of about $10^{-42}$.
- **Hypotheses:** positivity of $\delta$ is not needed, and not assumed.
- **Vacuity:** none.
- **Junk:** none.

## 12. `integral_band_count`

**Rendering.** Assume $\delta$ antitone and `hband`. Then $\mathbb E\sum_{k\le\ell}n_k=T\,\nu(\{|z|\ge\delta_\ell\})$, with `toReal` taken and $n_k=(\omega_k).1\in\mathbb N$ cast to ℝ.

**Assessment.**
- **Truth:** true: $\mathbb En_k=\Lambda_k=T\nu(\text{band}_k)$, and the bands are disjoint with union $\{|z|\ge\delta_\ell\}$. The Poisson counts are integrable.
- **toReal:** the measure is finite when $T>0$, by `hband`. When $T=0$ both sides are $0$. Exact check: $0.975, 2.175, 4.125, 7.125$ match.
- **Vacuity:** none.
- **Junk:** none.
- **Standard result:** the expected number of simulated jumps.

## 13. `levy_expected_cost`

**Rendering.** Same hypotheses as #12, for any $L$ and $N:\mathbb N\to\mathbb N$. Under i.i.d. samples $x(\ell,n)\sim$ bandInputLaw indexed by $\mathbb N\times\mathbb N$ (`infinitePi`), the cost $\sum_{\ell\le L}\sum_{n<N_\ell}\big(1+\sum_{k\le\ell}n_k(x(\ell,n))\big)$ is integrable, and its mean is $\sum_{\ell\le L}N_\ell\,(1+T\nu(\{|z|\ge\delta_\ell\}))$.

**Assessment.**
- **Truth:** true, by linearity, the coordinate marginals of `infinitePi`, and #12.
- **Vacuity:** none.
- **Junk:** none.
- **Standard result:** the expected cost of the MLMC estimator under the "one unit plus one per jump" cost model.

## 14. `levy_truncation_theorem1`

**Rendering.** Fix $\delta_\ell=2^{-\ell}$. Assume:
- $\int\min(1,z^2)\,d\nu<\infty$ and $\int_{|z|\ge1}z^2\,d\nu<\infty$;
- $0<Y<2$;
- for every $\ell\in\mathbb N$: $T\int_{|z|<2^{-\ell}}z^2\,d\nu\le a\,2^{-(2-Y)\ell}$ and $T\,\nu(\{|z|\ge2^{-\ell}\})\le b\,2^{Y\ell}$ (toReal);
- `hband` holds;
- $\Phi$ is $K$-Lipschitz.

Then there exists $X$ such that:
- (i) for every $\ell$, $\mathbb E(X-\text{bandApprox}_\ell)^2=T\int_{|z|<2^{-\ell}}z^2\,d\nu$, with integrability;
- (ii) $\Phi(X)\in L^1$;
- (iii) there is $c_4>0$ (independent of $\varepsilon$) such that for every $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N$ with $N_\ell>0$ for all $\ell$, satisfying the conditions below.

The conditions in (iii) are:
- The MLMC estimator $\hat Y=\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}\big[P_\ell-P_{\ell-1}\big](x(\ell,n))$ satisfies $\mathbb E(\hat Y-\mathbb E\Phi(X))^2<\varepsilon^2$, with the square integrable. Here $P_\ell=\Phi(\text{bandApprox}_\ell)$, $P_{-1}:=0$, and fine and coarse are evaluated on the same sample.
- The expected cost is integrable and equals $\sum_{\ell\le L}N_\ell(1+T\nu(\{|z|\ge2^{-\ell}\}))$.
- That cost is at most $c_4\cdot\text{complexityBound}\big(\tfrac{2-Y}2,2-Y,Y,\varepsilon\big)$.

**Assessment.**
- **Truth:** true. (i) is #10 (with $\delta_\ell=2^{-\ell}\to0$). (ii) follows from `hlarge`, since $\mathbb E|\text{bandApprox}_0|\le T\int_{|z|\ge1}|z|\,d\nu<\infty$.
- **(iii) is Giles' theorem with rates:**
  - weak error: $|\mathbb E P_\ell-\mathbb E\Phi(X)|\le K\sqrt a\,2^{-(2-Y)\ell/2}$, so $\alpha=(2-Y)/2$;
  - variance: $V_\ell\le K^2a\,2^{-(2-Y)(\ell-1)}$ for $\ell\ge1$, and $V_0\le K^2T\int_{|z|\ge1}z^2\,d\nu$ (this is where `hlarge` is needed), so $\beta=2-Y$;
  - cost: $C_\ell=1+T\nu(\{|z|\ge2^{-\ell}\})\le(1+b)2^{Y\ell}$, so $\gamma=Y$.
- Giles' condition $\alpha\ge\frac12\min(\beta,\gamma)$ holds because $\alpha=\beta/2$. The strict $<\varepsilon^2$ is achievable, for example by splitting $\varepsilon^2/3$ each way.
- The three cases give $\varepsilon^{-2}$ ($Y<1$), $\varepsilon^{-2}\log^2\varepsilon$ ($Y=1$) and $\varepsilon^{-2Y/(2-Y)}$ ($Y>1$). `complexity.py` checks the allocation numerically; the ratios stay bounded for $Y\in\{0.5,1,1.5,1.9\}$.
- **The target is the right one:** $X$ is pinned down a.e. by (i), since the right-hand side tends to $0$, so $\mathbb E\Phi(X)$ is not a free choice.
- **Hypotheses:** $a,b$ are arbitrary reals, but are forced to be $\ge0$. `hcount` with toReal is not trivialised, because `hν` makes the measure finite.
- **Vacuity:** none; see #16 with $a=Tc/(2-Y)$ and $b=Tc/Y$.
- **Junk:** $N_\ell>0$, so `blockMean` never divides by zero; $\varepsilon>0$ in the rpow; $\varepsilon<e^{-1}$ makes $\log^2\varepsilon>1$.
- **Standard result:** MLMC for Lévy-driven quantities with jump truncation (Dereich–Heidenreich type), combined with Giles' MLMC complexity theorem.

## 15. `exists_levy_bandLaws`

**Rendering.** If $\int\min(1,z^2)\,d\nu<\infty$ and $\delta_k>0$ for all $k$ (no monotonicity assumed), then there exist rates $\Lambda_k\in\mathbb R_{\ge0}$ and probability measures $M_k$ with $\Lambda_kM_k=T\nu|_{\text{band}_k}$ for every $k$.

**Assessment.**
- **Truth:** true. Each band lies inside $\{|z|\ge\delta_j\}$ for some $j$ with $\delta_j>0$, and $\nu(\{|z|\ge\delta\})\le\int\min(1,z^2)/\min(1,\delta^2)<\infty$. So take $\Lambda_k=T\nu(\text{band}_k)$, and let $M_k$ be the normalised restriction (or any probability measure if the mass is $0$).
- **Vacuity:** none.
- **Junk:** none.
- **Standard result:** a Lévy measure is finite away from the origin.

## 16. `levy_stableLike_theorem1`

**Rendering.** Let $\nu=c\,z^{-1-Y}\mathbf 1_{(0,1]}(z)\,dz$ with $c>0$ and $0<Y<2$. Assume `hband` with $\delta_\ell=2^{-\ell}$ and $\Phi$ $K$-Lipschitz. Then the conclusion of #14 holds with explicit formulas:
- $\mathbb E(X-\text{bandApprox}_\ell)^2=Tc\,2^{-(2-Y)\ell}/(2-Y)$;
- the expected cost is $\sum_{\ell\le L}N_\ell\big(1+Tc(2^{Y\ell}-1)/Y\big)$;
- the cost is at most $c_4\,\text{complexityBound}(\tfrac{2-Y}2,2-Y,Y,\varepsilon)$.

**Assessment.**
- **Truth:** true. The closed forms are $\int_0^{h}z^2\,c z^{-1-Y}\,dz=c\,h^{2-Y}/(2-Y)$ and $\int_h^1 c z^{-1-Y}\,dz=c(h^{-Y}-1)/Y$, with $h=2^{-\ell}$. The point $\{1\}$ is Lebesgue-null, so the bound at $\ell=0$ is $0$. `stable_like.py` confirms these to about $10^{-27}$ for several $(c,Y)$, and confirms $\int\min(1,z^2)\,d\nu=c/(2-Y)<\infty$.
- **How it follows from #14:** take $a=Tc/(2-Y)$ and $b=Tc/Y$. `hlarge` holds trivially, since $\nu(\{|z|\ge1\})=0$.
- **Hypotheses:** `hc` is needed, since for $c\le0$ the density clips to $0$ and the formula would be negative. The negative-base `rpow` junk of the density lies outside the support $(0,1]$.
- **Vacuity:** none; for example $c=Y=T=1$, with $\Lambda,M$ from #15.
- **Junk:** none.
- **Standard result:** the MLMC complexity for a stable-like (Blumenthal–Getoor index $Y$) jump measure: $\varepsilon^{-2}$, $\varepsilon^{-2}\log^2\varepsilon$, or $\varepsilon^{-2Y/(2-Y)}$.
