# Blind read-back audit: packet M2 (remarks, random-shift QMC, CLTs)

| Field | Value |
|---|---|
| Date | 2026-09-29 |
| Packet | `readback/round11/packet_M2_remarks_qmc_clt.lean` (relative to the scratchpad) |
| Declarations audited | 14 (13 theorems and 1 definition, `shiftedQMC`), plus 6 supporting definitions rendered for context (2 of them recovered with `#print`, see point 1) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round11/work_M2/` (Python `check_*.py` with `.out`; Lean `scratch_packet.lean`, `defs_probe*.lean`, `eqn_probe.lean` with `.out`) |
| Toolchain | Lean v4.33.1, Mathlib 0df444a (local `.lake`) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `singleTerm_variance_le_of_sq_le` | theorem | true | no | no |
| 2 | `singleTermN_samples_of_sq_le` | theorem | true | no | no |
| 3 | `levelKeep_combined` | theorem | true (algebraic identity) | no | no |
| 4 | `splitting_variance_le` | theorem | true | no | no |
| 5 | `splitting_leading_order` | theorem | true | no | no |
| 6 | `markov_linear_levels` | theorem | true | no | no |
| 7 | `shiftedQMC` | def | n/a (definition is as intended) | n/a | n/a (`N = 0` gives 0, never used) |
| 8 | `shiftedQMC_unbiased` | theorem | true | no | no |
| 9 | `randomShift_replicates` | theorem | true | no | no |
| 10 | `tendstoInDistribution_levelEstimator` | theorem | true | no | no |
| 11 | `tendstoInDistribution_mlmcEstimator` | theorem | true | no | no |
| 12 | `sum_gaussian_hasLaw` | theorem | true | no | no |
| 13 | `tendstoInDistribution_sum_of_approxNormal` | theorem | true | no | no |
| 14 | `tendstoInDistribution_sum_inv_sqrt_mul` | theorem | true | no | no |

## Main points for a human auditor

1. **Packet defect: two definitions are missing.** Under "definitions used above", the entries for
   `MlmcLean.Randomised` are two dangling `omit [...] in` lines with no declaration after them. So
   `singleTerm` and `singleTermN`, which theorems 1 and 2 depend on, are not in the packet. I
   recovered their elaborated bodies with `#print` after `import MlmcLean` (`work_M2/defs_probe.out`).
   I did not read any source file. The bodies are
   `singleTerm Pl K p ω = (p (K ω))⁻¹ * levelDiff Pl (K ω) ω` and
   `singleTermN Pl K p ξ N x = (↑N)⁻¹ * ∑ n ∈ range N, singleTerm Pl K p (ξ n x)`.
   Theorems 1 and 2 were audited against these. The packet extractor should be fixed.
2. **Possible build-coverage issue (unverified; needs someone with repo access).** In this
   environment, `import MlmcLean` does not provide `MLMC.shiftedQMC`. `import MlmcLean.GilesRemarks`
   also fails because its `.olean` does not exist, and the same holds for `RandomShiftQMC` and
   `AsymptoticNormal` (`work_M2/defs_probe2.out`). The local build may just be stale. Still, someone
   should confirm that the root module or the CI target builds these three modules, and that
   `scripts/AxiomCheck.lean` covers them. Because of this, I compiled a scratch copy of the packet
   (`work_M2/scratch_packet.lean`) against `import MlmcLean` plus targeted Mathlib imports, with
   `shiftedQMC` re-declared verbatim. All 13 statements elaborate as printed.
3. **All 13 theorems are true, none is vacuous, and none relies on a junk value.** Every hypothesis
   that blocks a junk escape is present:
   - `hc` (finite $c$) in theorem 6: without it $c$`.toReal` $=0$ and the bound would claim $\mathrm{Var}\le 0$.
   - `hVm > 0` in theorems 4 and 5: without it $W/0=0$ would make `hMθ` trivial and the upper bound false.
   - `hsum2` in theorems 1 and 2: it makes the estimator $L^2$, so its `variance` is not the junk 0.
   - `hN`, `hR` and `2 ≤ R` in the QMC theorems.
   - `Var[Z 0; P] = 1` in theorem 14: it forces $Z_0\in L^2$, so `P[Z 0] = 0` is the genuine mean.
4. **Theorem 1's upper bound needs the relative-bias condition at every level, including
   $\ell=0$.** The condition is $(\mathbb E P_0)^2\le\delta\,\mathrm{Var}P_0$. Some condition of this
   kind is needed: the exact variance is
   $\sum V_\ell/p_\ell+\big(\sum m_\ell^2/p_\ell-(\sum m_\ell)^2\big)$, and the bracket is not small
   when the level-0 mean is large. In the example in `check_singleTerm.out`,
   $\mathrm{Var}Z=3.02$ and $\sum V/p=2.02$, while `hE` forces $\delta\ge 100$. So the upper bound
   only says something useful when $\delta$ is small. The lower bound needs no bias assumption.
   This is a modelling point, not a defect.
5. **`levelKeep_combined` is only an identity at the stated ratio**
   $n=n_1\sqrt{VC_1/(V_1C)}$. It does not claim the ratio is optimal. The ratio is in fact optimal
   (checked with sympy), but that is not part of the statement.
6. **`markov_linear_levels`: only part (ii) has real content.** Part (i) is just $\beta>0$ and part
   (iii) is plain arithmetic (linear $\le$ exponential). I proved (ii) independently with constant
   $4c/(1-\rho)^2\ge c/(1-\rho^{1/(2\gamma)})^{2\gamma}$. The theorem gives no weak-error (bias)
   rate.
7. **The CLTs are the "easy" fixed-$L$ versions.** Theorem 11 has $L$ fixed and $N_\ell=m_\ell n$,
   which is weaker than MLMC CLTs where $L\to\infty$ as $\varepsilon\to0$ (those need Lindeberg
   conditions). Theorems 12 and 13 are the special case where every component has variance $1/n$.
8. **Minor.** `section sampleVariance` in `RandomShiftQMC` is empty in the packet; if it holds
   declarations, they were not given to me. Three measures carry no `IsProbabilityMeasure`
   instance: $\mu'$ in theorem 2, $\mu$ in theorem 8 and $P$ in theorem 12. Each is forced to be a
   probability measure by the `MeasurePreserving` or `HasLaw` hypotheses, so this is harmless.

Conventions checked in Mathlib sources:
- `variance X μ = (evariance X μ).toReal`. It equals $\infty$.toReal $=0$ when $X\notin L^2$ and $X$ is a.e.-measurable (`evariance_eq_top`).
- `HasLaw` requires AEMeasurability and `P.map X = μ`.
- `TendstoInDistribution` requires AEMeasurability of each term and of the limit, plus weak convergence of the laws as `ProbabilityMeasure`s.
- `gaussianReal μ v` has variance `v` and is `dirac μ` when `v = 0`.
- `Measure.infinitePi` is `0` unless every factor is a probability measure. It is always a genuine product here.
- `UnitAddTorus d = d → UnitAddCircle`. Its `volume` is `Measure.pi` of the mass-1 Haar measure, which is translation invariant.
- `IdentDistrib` includes AEMeasurability of both sides.

---

## Supporting definitions (rendered for context)

Notation: $P_\ell$ is `Pl ℓ`, and $Y_\ell$ is `levelDiff Pl ℓ`.

- `levelDiff`: $Y_0=P_0$ and $Y_{\ell+1}=P_{\ell+1}-P_\ell$ (pointwise). Checked by `rfl` in `eqn_probe.lean`.
- `levelEstimator Pl ω ℓ N x` $=N^{-1}\sum_{n<N}Y_\ell(\omega(\ell,n)(x))$. For $N=0$ it is $0$.
- `mlmcEstimator Pl ω L N x` $=\sum_{\ell\le L}$ `levelEstimator Pl ω ℓ (N ℓ) x`.
- `backIter φ n e x`: $0\mapsto x$ and $n+1\mapsto \varphi(\texttt{backIter}\,\varphi\,n\,(e\circ(\cdot+1))\,x,\ e_0)$.
  So $\texttt{backIter}\,\varphi\,n\,e\,x=F_{e_0}\circ F_{e_1}\circ\cdots\circ F_{e_{n-1}}(x)$ with
  $F_e=\varphi(\cdot,e)$. The noise $e_{n-1}$ is applied first and $e_0$ last, so the chain is
  "started $n$ steps in the past". Checked by `rfl`, including the unrolled case $n=3$.
- `singleTerm Pl K p ω` $=p_{K(\omega)}^{-1}\,Y_{K(\omega)}(\omega)$. Recovered with `#print`; missing from the packet.
- `singleTermN Pl K p ξ N x` $=N^{-1}\sum_{n<N}$ `singleTerm Pl K p` $(\xi_n(x))$. Recovered with `#print`; missing from the packet.

---

## 1. `singleTerm_variance_le_of_sq_le` (theorem)

**Rendering.** The setting:
- $(\Omega,\mu)$ is a probability space.
- $K:\Omega\to\mathbb N$ is measurable.
- Every $P_\ell:\Omega\to\mathbb R$ is measurable and in $L^2(\mu)$.
- $p:\mathbb N\to\mathbb R$ satisfies $\mu(K=\ell)=p_\ell>0$ for every $\ell$. Hence $\sum_\ell p_\ell=1$ and $K$ has full support on $\mathbb N$.

The hypotheses:
- For each $\ell$ separately, $K$ is independent of $Y_\ell$.
- $\sum_\ell \mathbb E[Y_\ell^2]/p_\ell$ is summable.
- For one real $\delta$ (any sign) and every $\ell\ge0$: $(\mathbb E Y_\ell)^2\le\delta\,\mathrm{Var}(Y_\ell)$.

The conclusion, with $Z=Y_K/p_K$ (`singleTerm`) and $V_\ell=\mathrm{Var}(Y_\ell)$:
$$\textstyle\sum'_\ell V_\ell/p_\ell\ \le\ \mathrm{Var}_\mu(Z)\ \le\ (1+\delta)\sum'_\ell V_\ell/p_\ell .$$

**Assessment.**
- **Truth: true.** Write $m_\ell=\mathbb E Y_\ell$.
  - By independence, $\mathbb E[Y_\ell^2\mathbf 1_{K=\ell}]=p_\ell\mathbb E Y_\ell^2$. So $\mathbb E Z^2=\sum\mathbb E Y_\ell^2/p_\ell<\infty$, and $Z\in L^2$ (so `variance` is the genuine variance).
  - $\mathbb E Z=\sum_\ell m_\ell$. The series converges absolutely because $\sum|m_\ell|\le(\sum m_\ell^2/p_\ell)^{1/2}(\sum p_\ell)^{1/2}$.
  - Hence $\mathrm{Var}Z=\sum V_\ell/p_\ell+\big[\sum m_\ell^2/p_\ell-(\sum m_\ell)^2\big]$.
  - The bracket is $\ge0$ by Cauchy–Schwarz with $\sum p_\ell=1$. This gives the lower bound.
  - The bracket is $\le\sum m_\ell^2/p_\ell\le\delta\sum V_\ell/p_\ell$ by `hE`. This gives the upper bound.
  - If $\delta<0$, `hE` forces $m_\ell=0$ and $V_\ell=0$, so everything is $0$.
  - `check_singleTerm.py`: 4000 random instances with the exact law of $Z$. The closed form matches to $6\cdot10^{-37}$, both bounds hold, and the zero-mean case gives equality in the lower bound.
- **Vacuity: no.** Take $\Omega=\mathbb N\times\{\pm1\}^{\mathbb N}$, $K$ geometric with $p_\ell=2^{-\ell-1}$, $Y_\ell=2^{-\ell}S_\ell$ with Rademacher $S_\ell$ independent of $K$, $P_\ell=\sum_{j\le\ell}Y_j$ and $\delta=0$. Then both sides equal $4$.
- **Junk: none.** `∑'` is taken over a summable nonnegative series ($V_\ell/p_\ell\le\mathbb E Y_\ell^2/p_\ell$), $p_\ell>0$, and $Z\in L^2$.
- **Hypotheses.**
  - Independence is only pairwise ($K$ with each $Y_\ell$), which is weaker than the usual assumption. Good.
  - `hPl` for all $\ell$ is equivalent to $Y_\ell\in L^2$ for all $\ell$.
  - `hE` at $\ell=0$ is a real restriction (see main point 4).
- **Standard result.** The variance of the Rhee–Glynn single-term randomised MLMC estimator, $\mathrm{Var}Z=\sum\mathbb E[\Delta P_\ell^2]/p_\ell-(\mathbb E P)^2\approx\sum V_\ell/p_\ell$ (Giles' review, randomised MLMC).

## 2. `singleTermN_samples_of_sq_le` (theorem)

**Rendering.** Take all the hypotheses of theorem 1, and add:
- a measurable space $(\Omega',\mu')$ with maps $\xi_n:\Omega'\to\Omega$ that are measure preserving ($\mu'\circ\xi_n^{-1}=\mu$, which forces $\mu'$ to be a probability measure) and mutually independent;
- $N\in\mathbb N$ with $N\ge1$, and $\varepsilon>0$.

Let $\bar Z_N=N^{-1}\sum_{n<N}Z\circ\xi_n$ (`singleTermN`) and $S=\sum'_\ell V_\ell/p_\ell$. Then:
- (a) $\mathrm{Var}_{\mu'}(\bar Z_N)=\mathrm{Var}_\mu(Z)/N$;
- (b) $\mathrm{Var}(\bar Z_N)\le\varepsilon^2\Rightarrow \varepsilon^{-2}S\le N$;
- (c) $(1+\delta)\varepsilon^{-2}S\le N\Rightarrow\mathrm{Var}(\bar Z_N)\le\varepsilon^2$.

**Assessment.**
- **Truth: true.**
  - (a) is the variance of the mean of $N$ i.i.d. $L^2$ copies of $Z$: the $Z\circ\xi_n$ are independent and each has the law of $Z$.
  - (b) and (c) follow from (a) and theorem 1 after multiplying by $\varepsilon^2/N>0$.
  - `check_singleTerm.py` checks (a) exactly by convolution for $N=1,2,3$.
- **Vacuity: no.** Take $\Omega'=\Omega^{\mathbb N}$ with the product measure and $\xi_n$ the coordinates.
- **Junk: none.**
- **Hypotheses.** The missing probability instance on $\mu'$ is harmless (forced).
- **Standard result.** The sample-size requirement $N\approx\varepsilon^{-2}\sum V_\ell/p_\ell$ for randomised MLMC: (b) is the necessary part, (c) the sufficient part.

## 3. `levelKeep_combined` (theorem)

**Rendering.** For reals $V,V_1,C,C_1,n_1>0$ and $n=n_1\sqrt{(V/V_1)(C_1/C)}$, let $s=\sqrt{VC/(V_1C_1)}$. Then:
- (a) $V/n+V_1/n_1=(V_1/n_1)(1+s)$;
- (b) $nC+n_1C_1=n_1C_1(1+s)$;
- (c) $(V/n+V_1/n_1)(nC+n_1C_1)=V_1C_1(1+s)^2$.

All quantities are real; nothing is a natural number.

**Assessment.**
- **Truth: true.** Direct algebra. `check_levelKeep.py`: the sympy residuals are $0$, and 20000 random inputs spanning $10^{\pm8}$ give relative residual $\le10^{-50}$.
- **Vacuity: no.**
- **Junk: none.** Every square-root argument is positive and $n>0$.
- **Scope.** The statement does not claim that this $n$ minimises the product. It does: the critical point is $n/n_1=\sqrt{VC_1/(V_1C)}$ with minimum $(\sqrt{VC}+\sqrt{V_1C_1})^2$ (checked, not part of the theorem).
- **Standard result.** Optimal allocation $N_\ell\propto\sqrt{V_\ell/C_\ell}$ restricted to two levels, giving variance times cost $(\sqrt{V_\ell C_\ell}+\sqrt{V_{\ell_1}C_{\ell_1}})^2$ (Giles' remark on whether to keep a level).

## 4. `splitting_variance_le` (theorem)

**Rendering.** The setting:
- $(\Omega_1,\mu)$ and $(\Omega_2,\nu)$ are probability spaces.
- $g:\Omega_1\times\Omega_2\to\mathbb R$ is jointly measurable with $g^2\in L^1(\mu\otimes\nu)$.
- $M\in\mathbb N$ with $M\ge1$, and $\theta>0$.
- $m(x)=\int g(x,z)\,\nu(dz)$ and $V_m=\mathrm{Var}_\mu(m)>0$.
- $W=\iint(g(x,z)-m(x))^2\,\nu(dz)\,\mu(dx)$.
- Hypothesis: $W/(\theta V_m)\le M$.

The estimator is $\hat Y_M(x,(z_j)_{j\in\mathbb N})=M^{-1}\sum_{j<M}g(x,z_j)$ on $\Omega_1\times\Omega_2^{\mathbb N}$ under $\mu\otimes\nu^{\otimes\mathbb N}$. Conclusion: $V_m\le\mathrm{Var}(\hat Y_M)\le(1+\theta)V_m$.

**Assessment.**
- **Truth: true.**
  - By the law of total variance, $\mathrm{Var}\hat Y_M=V_m+W/M$.
  - $W\ge0$ gives the lower bound.
  - $W/M\le\theta V_m$ is exactly the hypothesis, which gives the upper bound.
  - `check_splitting.py` checks the identity by exact rational enumeration (error $0$) and the sandwich in all cases.
- **Vacuity: no.** Take $g(x,z)=x+z$ on $[0,1]^2$ with Lebesgue measure: $V_m=W=1/12$, $\theta=1$, $M=1$.
- **Junk: none.**
  - For $\mu$-a.e. $x$, $g(x,\cdot)\in L^2(\nu)$, so $m$ is the genuine inner integral.
  - The integrand of $W$ is $\le\int g^2\,d\nu$, which is integrable, so $W$ is the genuine integral.
  - $\hat Y_M\in L^2$.
  - `infinitePi` is the genuine product because $\nu$ is a probability measure.
  - `hVm` is necessary: with $V_m=0$, `hMθ` would read $W/0=0\le M$ and the upper bound would fail.
- **Standard result.** The variance of a splitting (conditional sub-sampling) estimator, $\mathrm{Var}(\mathbb E[g\mid x])+\mathbb E[\mathrm{Var}(g\mid x)]/M$.

## 5. `splitting_leading_order` (theorem)

**Rendering.** The setting:
- $l$ is an arbitrary filter on $\iota$.
- $h_i>0$ and $h_i\to0$ along $l$.
- Each $g_i$ satisfies the integrability hypotheses of theorem 4, with $V_{m,i}>0$.

Write $W_i$ for the $W$ of $g_i$. The statement is the equivalence of the following two conditions:
- There exists $M:\iota\to\mathbb N$ with every $M_i\ge1$, such that along $l$ both $\mathrm{Var}(\hat Y_{i,M_i})/V_{m,i}\to1$ and $(h_i^{-1}-1+M_i)/h_i^{-1}\to1$.
- $h_iW_i/V_{m,i}\to0$ along $l$.

**Assessment.**
- **Truth: true.** Put $r_i=W_i/V_{m,i}$. The variance ratio is $1+r_i/M_i$ and the cost ratio is $1+h_i(M_i-1)$.
  - ($\Rightarrow$): $h_ir_i=(r_i/M_i)(h_i(M_i-1)+h_i)\to0$.
  - ($\Leftarrow$): take $M_i=\lceil\sqrt{r_i/h_i}\rceil+1$. Then $r_i/M_i\le\sqrt{h_ir_i}$ and $h_i(M_i-1)\le\sqrt{h_ir_i}+h_i$.
  - `check_splitting.py` illustrates both a good family and a bad family.
- **Vacuity: no.** Take a constant $g_i=g$ with $V_m>0$ and $h_i=1/(i+1)$ along `atTop`.
- **Junk: none.** $h_i>0$ and $V_{m,i}>0$.
- **Modelling.** The cost model is abstract: $h^{-1}-1$ path steps plus $M$ unit-cost final-step samples.
- **Standard result.** Giles' splitting remark: with $M\to\infty$ and $hM\to0$, the variance is $\mathrm{Var}(\mathbb E[g\mid x])$ and the cost is $h^{-1}$, both to leading order.

## 6. `markov_linear_levels` (theorem)

**Rendering.** The setting:
- $\alpha$ is a second-countable pseudo-metric space with a Borel-type σ-algebra; $E$ is a measurable space carrying a measure $\nu$.
- $\varphi:\alpha\times E\to\alpha$ is jointly measurable.
- $\gamma\in(0,1]$ and $\rho\in(0,1)$.
- Contraction in mean: for all $x,y$, $\int d(\varphi(x,e),\varphi(y,e))^{2\gamma}\nu(de)\le\rho\,d(x,y)^{2\gamma}$.
- On a probability space $(\Omega,\mu)$, the $\xi_i$ are measurable, mutually independent, and each has law $\nu$ (so $\nu$ is a probability measure).
- $x_0\in\alpha$ with $c:=\int d(x_0,\varphi(x_0,e))^{2\gamma}\nu(de)<\infty$.
- $f$ is measurable with $|f(x)-f(y)|\le d(x,y)^\gamma$.
- $a,b\in\mathbb N$ with $a\ge1$.

Let $X_n=F_{\xi_0}\circ\cdots\circ F_{\xi_{n-1}}(x_0)$ (`backIter`) and $P_\ell=f(X_{a\ell+b})$. Then:
- (i) $\beta:=a\log_2(1/\rho)>0$;
- (ii) for every $\ell\in\mathbb N$, $\mathrm{Var}(Y_\ell)\le\frac{4c}{(1-\rho)^2\rho^a}2^{-\beta\ell}=\frac{4c\,\rho^{a(\ell-1)}}{(1-\rho)^2}$;
- (iii) for every $\gamma'>0$ there is $c_3>0$ (depending on $\gamma',a,b$) with $a\ell+b\le c_3 2^{\gamma'\ell}$ for all $\ell$. Here $a\ell+b$ is computed in $\mathbb N$ and then cast.

**Assessment.**
- **Truth: true.** Let $s=2\gamma\in(0,2]$.
  - Iterating the contraction through independence gives $\mathbb E\,d(G(Y),G(x_0))^s\le\rho^m\,\mathbb E\,d(Y,x_0)^s$, where $G=F_{\xi_0}\circ\cdots\circ F_{\xi_{m-1}}$ and $Y$ is independent of $\xi_0,\dots,\xi_{m-1}$.
  - For a $k$-step iterate $Y$ started at $x_0$, the successive increments have $s$-th moments $\le\rho^jc$.
  - Hence $\mathbb E\,d(Y,x_0)^s\le c/(1-\rho)$ when $s\le1$ (subadditivity of $t^s$), and $\le c/(1-\rho^{1/s})^s$ when $1<s\le2$ (Minkowski).
  - Both are $\le4c/(1-\rho)^2$, because $(1-\rho^{1/s})^s\ge(1-\sqrt\rho)^2\ge(1-\rho)^2/4$.
  - For $\ell\ge1$ and $m=a(\ell-1)+b$: $\mathrm{Var}Y_\ell\le\mathbb E(f(X_{m+a})-f(X_m))^2\le\rho^m\cdot4c/(1-\rho)^2\le\frac{4c}{(1-\rho)^2\rho^a}\rho^{a\ell}$.
  - For $\ell=0$: $\mathrm{Var}f(X_b)\le\mathbb E(f(X_b)-f(x_0))^2\le4c/(1-\rho)^2$.
  - (i) and (iii) are elementary.
  - `check_markov.py` uses exact enumeration over $2^{12}$ Rademacher noise sequences, 4 chains (linear, nonlinear $\kappa\sin x$, multiplicative, asymmetric) × $\gamma\in\{1,\tfrac12,\tfrac14\}$ × 3 values of $\rho$ × 3 pairs $(a,b)$. The maximum of $\mathrm{Var}(Y_\ell)/$bound is $0.209$, and (iii) is confirmed.
- **Vacuity: no.** Take $\alpha=E=\mathbb R$, $\nu=N(0,1)$, $\varphi(x,e)=x/2+e$, $\gamma=1$, $\rho=1/4$, $f=\mathrm{id}$, $x_0=0$ (so $c=1$), $\xi_i$ the coordinates on $\mathbb R^{\mathbb N}$.
- **Junk: none.**
  - `hc` is essential: with $c=\infty$ we would have $c$`.toReal` $=0$ and a false bound.
  - $f(X_n)\in L^2$, so the variances are genuine.
  - When $c=0$ the bound $0$ is correct, since $X_n=x_0$ a.s.
- **Notes.**
  - The Hölder constant is normalised to 1.
  - The constant is not sharp.
  - No bias rate is given.
  - (iii) says nothing about the chain.
- **Standard result.** MLMC for equilibrium expectations of contracting Markov chains (Glynn–Rhee style coupling from the past), with level $\ell$ run for $a\ell+b$ steps: $V_\ell=O(2^{-\beta\ell})$ with $\beta=a\log_2\rho^{-1}$ and cost $O(\ell)=O(2^{\gamma'\ell})$, hence $O(\varepsilon^{-2})$ complexity.

## 7. `shiftedQMC` (definition)

**Rendering.** For $f:\mathbb T^d\to\mathbb R$ (with $\mathbb T^d$ = `UnitAddTorus d` $=(\mathbb R/\mathbb Z)^d$), points $x:\mathbb N\to\mathbb T^d$, $N\in\mathbb N$ and shift $u\in\mathbb T^d$:
$$Q_N(u)=N^{-1}\sum_{i<N}f(x_i+u),$$
with addition mod 1 in each coordinate. For $N=0$ the value is $0$ (since $0^{-1}=0$ and the sum is empty). This is the Cranley–Patterson randomly shifted QMC rule, for an arbitrary point sequence.

## 8. `shiftedQMC_unbiased` (theorem)

**Rendering.** The setting:
- $d$ is finite; $(\Omega,\mu)$ is any measure space.
- $U:\Omega\to\mathbb T^d$ is measure preserving onto `volume`. So $U$ is uniform and $\mu$ is a probability measure.
- $x$ is any point sequence, $f\in L^1(\mathbb T^d)$, and $N\ge1$.

Then:
- (a) for every $i$, $\omega\mapsto x_i+U(\omega)$ is measure preserving;
- (b) $Q_N\circ U\in L^1(\mu)$;
- (c) $\mathbb E_\mu[Q_N(U)]=\int_{\mathbb T^d}f$.

**Assessment.**
- **Truth: true.** Haar measure (a product of mass-1 circle measures) is translation invariant; the rest follows by linearity. `check_qmc.py` confirms (c) by quadrature for $d=1$ and $N=1,2,4$.
- **Vacuity: no.** Take $\Omega=\mathbb T^d$ and $U=\mathrm{id}$.
- **Junk: none.** $f$ is integrable, and `hN` rules out $N=0$, where the left side is $0$.
- **Standard result.** Unbiasedness of randomly shifted QMC.

## 9. `randomShift_replicates` (theorem)

**Rendering.** The setting:
- $(\Omega,\mu)$ is a probability space.
- The $U_r$ ($r\in\mathbb N$) are i.i.d. uniform on $\mathbb T^d$ (each measure preserving; `iIndepFun`).
- $f$ is measurable and in $L^2(\mathbb T^d)$; $N,R\ge1$.
- $Q_r:=Q_N(U_r)$ and $\bar Q=R^{-1}\sum_{r<R}Q_r$.

Then:
- (a) the $Q_r$ are mutually independent;
- (b) each $Q_r$ has law $\mathrm{volume}\circ Q_N^{-1}$;
- (c) $\mathbb E Q_r=\int f$;
- (d) $\mathbb E\bar Q=\int f$;
- (e) $\mathrm{Var}\bar Q=\mathrm{Var}_{\rm vol}(Q_N)/R$;
- (f) if $R\ge2$, then $\mathbb E\big[(R(R-1))^{-1}\sum_{r<R}(Q_r-\bar Q)^2\big]=\mathrm{Var}_{\rm vol}(Q_N)/R$. Elaboration confirms that $R-1$ is real subtraction, $(\uparrow R\cdot(\uparrow R-1))^{-1}$.

**Assessment.**
- **Truth: true.** These are standard facts about i.i.d. $L^2$ replicates, plus the unbiased sample variance. `check_qmc.py` checks every identity exactly on a finite-grid analogue for $R=2,3,4$.
- **Vacuity: no.** Take $\Omega=(\mathbb T^d)^{\mathbb N}$ with coordinates $U_r$.
- **Junk: none.** $f\in L^2$ gives $Q_N\in L^2$, and $R\ge1$ or $R\ge2$ as appropriate.
- **Standard result.** Independent random shifts give an unbiased estimate and an unbiased error estimate (L'Ecuyer–Lemieux; Dick–Kuo–Sloan).

## 10. `tendstoInDistribution_levelEstimator` (theorem)

**Rendering.** The setting:
- $(\Omega,\mu)$ and $(\Omega',P')$ are probability spaces.
- $\omega(\ell,n):\Omega\to\Omega_0$ is measure preserving onto $\nu$ for every $(\ell,n)$, and the whole family indexed by $\mathbb N\times\mathbb N$ is independent. So the samples are i.i.d. with law $\nu$.
- $\ell$ is fixed and $Y_\ell\in L^2(\nu)$.
- $Z$ on $\Omega'$ has law $N(0,\mathrm{Var}_\nu Y_\ell)$.

Conclusion: $\sqrt N\big(N^{-1}\sum_{n<N}Y_\ell(\omega(\ell,n))-\mathbb E_\nu Y_\ell\big)\Rightarrow Z$ in distribution as $N\to\infty$.

**Assessment.**
- **Truth: true.** Lindeberg–Lévy CLT. The degenerate case with variance $0$ gives the limit $\delta_0$ and is also correct.
- **Vacuity: no.** Take the product space $\Omega_0^{\mathbb N\times\mathbb N}$.
- **Junk: none.** $\mathbb E_\nu Y_\ell$ is genuine because $Y_\ell\in L^1$.
- **Hypotheses.** Independence of the whole $\mathbb N\times\mathbb N$ family is more than needed, but harmless.

## 11. `tendstoInDistribution_mlmcEstimator` (theorem)

**Rendering.** The setting:
- The sampling setup is the same as in theorem 10.
- $L$ is fixed, $P_\ell\in L^2(\nu)$ for $\ell\le L$, and $m_\ell\ge1$ are integers for $\ell\le L$.
- $Z\sim N\big(0,\sum_{\ell\le L}V_\ell/m_\ell\big)$.

With $N_\ell=m_\ell n$ and $\hat Y_n=\sum_{\ell\le L}N_\ell^{-1}\sum_{k<N_\ell}Y_\ell(\omega(\ell,k))$, the conclusion is $\sqrt n(\hat Y_n-\mathbb E_\nu P_L)\Rightarrow Z$ as $n\to\infty$.

**Assessment.**
- **Truth: true.**
  - The expectations telescope: $\sum_{\ell\le L}\mathbb E Y_\ell=\mathbb E P_L$.
  - The levels use disjoint sample sets, so they are independent.
  - $\sqrt n(\bar Y_\ell-\mathbb E Y_\ell)=m_\ell^{-1/2}\sqrt{N_\ell}(\cdots)\Rightarrow N(0,V_\ell/m_\ell)$, and the sum of independent limits gives the claimed variance.
  - `check_clt.py` checks the exact variance identity and a Monte Carlo sample of 20000 (variance 0.2647 against 0.2635; CDF within about 0.004 of $\Phi$).
- **Vacuity: no.**
- **Junk: none.**
- **Scope.** This is the fixed-$L$ CLT, not the $L\to\infty$ (as $\varepsilon\to0$) MLMC CLT.

## 12. `sum_gaussian_hasLaw` (theorem)

**Rendering.** For $n\ge1$, let $X_0,\dots,X_{n-1}$ on $(\Omega,P)$ be independent, each with law $N(0,1/n)$. Then $\sum_iX_i\sim N(0,1)$. $P$ carries no instance but is forced to be a probability measure.

**Assessment.**
- **Truth: true.** The characteristic functions multiply: $(e^{-t^2/2n})^n=e^{-t^2/2}$. Checked with sympy and by numerical convolution for $n=2$.
- **Vacuity: no.** Take coordinates on $\mathbb R^n$ with the product law.
- **Junk: none.** Since $n\ge1$, $(n:\mathbb R_{\ge0})^{-1}=1/n$.
- **Scope.** Special case of closure of Gaussians under independent sums, with equal variances.

## 13. `tendstoInDistribution_sum_of_approxNormal` (theorem)

**Rendering.** The setting:
- $(\Omega,P)$ and $(\Omega',P')$ are probability spaces, and $n\ge1$.
- For each $d$, the variables $X_{d,0},\dots,X_{d,n-1}$ are independent. No independence across different $d$ is assumed.
- For each $i$, $X_{d,i}\Rightarrow N(0,1/n)$ as $d\to\infty$.
- $G\sim N(0,1)$.

Conclusion: $\sum_iX_{d,i}\Rightarrow G$.

**Assessment.**
- **Truth: true.** The characteristic function of the sum is the product of the component characteristic functions, which tends to $e^{-t^2/2}$; then apply Lévy continuity. `check_clt.py` gives an exact binomial example whose Kolmogorov distance falls from 0.22 to 0.007.
- **Vacuity: no.**
- **Junk: none.**

## 14. `tendstoInDistribution_sum_inv_sqrt_mul` (theorem)

**Rendering.** On a probability space $(\Omega,P)$, let $(Z_i)_{i\in\mathbb N}$ be mutually independent and each identically distributed with $Z_0$, with $\mathbb E Z_0=0$ and $\mathrm{Var}Z_0=1$. Let $G\sim N(0,1)$ on $(\Omega',P')$. Then $\sum_{i<n}n^{-1/2}Z_i\Rightarrow G$.

**Assessment.**
- **Truth: true.** Classical Lindeberg–Lévy CLT.
- **Junk: none.** `IdentDistrib` makes $Z_0$ a.e.-measurable. If $Z_0\notin L^2$, Mathlib's `variance` would be $0\ne1$. So $Z_0\in L^2$, and the hypothesis $\mathbb E Z_0=0$ is about the genuine mean, not the junk integral.
- **Numerical check.** `check_clt.py`: for Rademacher variables the exact Kolmogorov distance is 0.123, 0.040, 0.013 and 0.006 for $n=10,100,1000,4000$.
- **Vacuity: no.**
