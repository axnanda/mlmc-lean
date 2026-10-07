# Blind read-back report: R21 (end-to-end instances)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round18/packet_R21_endtoend.lean` |
| declarations audited | 18 (16 theorems, 2 definitions: `gbmExactM`, `truncGrid`) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round18/work_R21/` (each `*.py` has its `*.out`; `scratch_packet.lean`/`.out` is the elaboration check) |

Elaboration check: I compiled a scratch copy of the packet (namespace renamed to `MLMC.Audit`, proofs `sorry`, `import MlmcLean`). It elaborates without errors. `#check` with `pp.numericTypes` confirms the casts: `T ≤ (54:ℝ) * ↑N`, real costs `↑(N ℓ) * (2:ℝ)^(ℓ+1)` and `↑(N ℓ) * (↑m * ↑M ^ ℓ)`, and `Real.log ε ^ 2 = (log ε)^2` (see `scratch_packet.out`).

Mathlib conventions I checked in the sources: `round x = if 2 * fract x < 1 then ⌊x⌋ else ⌈x⌉`, and `round_eq : round x = ⌊x + 1/2⌋`, so ties go towards $+\infty$. `HasLaw` packages `AEMeasurable` together with `map = law`. `iIndepFun.isProbabilityMeasure` holds even for an empty index type, because the empty `Finset` forces $\mu(\Omega)=1$. `variance = (evariance).toReal`. `gaussianReal μ v` has variance `v`. `Measure.infinitePi` is the product of probability measures.

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `elliptic_mlmc_theorem1` | theorem | true | no | no |
| 2 | `elliptic_mlmc_theorem1_uniform` | theorem | true | no | no |
| 3 | `gbm_call_mlmc_theorem1` | theorem | true | no | no |
| 4 | `gbm_mil_call_mlmc_theorem1` | theorem | true | no | no |
| 5 | `tamedCubic_fourth_moment_le` | theorem | true | no | no |
| 6 | `gbmExactM` | def | n/a | n/a | n/a |
| 7 | `gbmExactM_blockAvg` | theorem | true | no | no (hypothesis `0 < M` is superfluous) |
| 8 | `gbm_weak_error_le_M` | theorem | true | no | no |
| 9 | `gbm_correction_variance_le_M` | theorem | true | no | no |
| 10 | `gbm_mlmc_theorem1_M` | theorem | true | no | no |
| 11 | `exists_lsq_minimiser` | theorem | true | no | no |
| 12 | `method2_iteration_exists` | theorem | true | no | no |
| 13 | `method2_sorting_iteration_exists` | theorem | true | no | no |
| 14 | `roundFixed_coarse_increment_mean` | theorem | true | no | no, but it depends on a convention: Mathlib's `round` sends ties up |
| 15 | `nearestRound_coarse_increment_pos_prob` | theorem | true | no | no |
| 16 | `roundFixed_coarse_increment_pos_prob` | theorem | true | no | no, but it depends on a convention: Mathlib's `round` sends ties up |
| 17 | `truncGrid` | def | n/a | n/a | n/a |
| 18 | `truncGrid_coarse_increment_mean_lt` | theorem | true | no | no |

## Main points for a human auditor

1. **All 16 theorems are true. None is vacuous and none depends on a junk value.** I found no false statement.
2. **The five complexity statements (#1–#4, #10) have the correct quantifier order.** The order is $\exists c_4>0\ \forall \varepsilon\in(0,e^{-1})\ \exists L, (N_\ell)_\ell$. So $c_4$ is fixed before $\varepsilon$ and depends only on the model data: $(\nu,a,Z)$ for the elliptic case, and $(r,\sigma,s_0,K,T)$ or $(r,\sigma,s_0,T,m,M,g,K)$ for the GBM cases.
   - **The MSE is a genuine expectation.** It is the expected squared error of the standard MLMC estimator under the product measure `infinitePi` over i.i.d. samples $x_{\ell,n}$, indexed by (level, sample). Fine and coarse paths share the same sample.
   - **The junk values are blocked.** Integrability of the squared error is asserted, so the junk value "integral of a non-integrable function $=0$" cannot be used. $N_\ell\ge 1$ is required, so the junk value $0^{-1}=0$ cannot be used either.
   - **Cost model.** The cost is $\sum_{\ell\le L} N_\ell \times$ (fine-grid size): $2^{\ell+1}$ cells (elliptic), $2^\ell$ steps (GBM), $mM^\ell$ steps (factor $M$). Coarse-path evaluations and random-number generation are not counted. That changes only constants.
   - **Rates.** $\varepsilon^{-2}$ for the elliptic FD case and for Milstein ($\beta>\gamma$); $\varepsilon^{-2}(\log\varepsilon)^2$ for Euler–Maruyama ($\beta=\gamma=1$). Both match Giles' MLMC complexity theorem.
3. **#14 and #16 hold only because Mathlib's `round` sends ties towards $+\infty$.** This is a convention, not a junk value.
   - Under IEEE round-to-nearest-even, or round-half-away-from-zero, both means in #14 are exactly $0$.
   - Under round-to-nearest-even, the inequality in #16 reverses: at $Q/s=2$ the probabilities are $0.2398$ vs $0.1494$, instead of $0.2398$ vs $0.3645$ (`rounding_ties.out`).
   - #15 is the convention-free version: it splits on whether the coarse rounding sends the tie at $q$ up or down.
   - If these results are meant to model IEEE floating-point rounding, the intended tie rule should be checked.
4. **Exact values behind the rounding inequalities** ($s=\sqrt v$, $Q=2^{e-B}$ coarse spacing, $K_i=\operatorname{round}(2X_i/Q)$, $p=P(K_i\text{ odd})$):
   - $E[\mathrm{rc}(X_1+X_2)]=0$.
   - $E[\mathrm{rc}(\mathrm{rf}X_1+\mathrm{rf}X_2)]=Q\,p(1-p)$.
   - $E[\mathrm{rc}(\mathrm{rf}X_1)+\mathrm{rc}(\mathrm{rf}X_2)]=Q\,p$.
   - Since $p\approx\tfrac12$ for $Q\lesssim s$, these two means are $\approx Q/4$ and $Q/2$.
   - For the truncation version (#18), the three means are exactly $-2q<-\tfrac32q<-q$ for every $v>0$.
   - All of these were computed exactly with mpmath and confirmed by Monte Carlo.
5. **#5 (tamed Euler): the hypothesis $T\le 54N$ is exactly the step-size condition $h\le54$, and it is sharp.** The tamed drift map $x\mapsto x-hx^3/(1+h|x|^3)$ is non-expansive iff $h\le 54$, because $\max_{u\ge0}(u^2-2u^3)=1/27$. At $h=54$, $x_0=1/3$, $N=1$ both bounds hold with equality. At $h=58$, $x_0=0.3$, $N=1$ the second-moment bound fails.
6. **#8 and #9 rest on an explicit strong-error constant `gbmStrongConst`.** I computed the EM strong error $E|\hat S_N-S_T|^2$ in closed form. Over about 57,000 parameter points its ratio to $C\,h$ never exceeded $0.0989$; asymptotically the ratio is at most $1/10$.
7. **The minimiser statements (#11–#13) are genuine but elementary.**
   - #11 is the existence of least-squares solutions; $X$ may be infinite-dimensional.
   - #12 and #13 are existential and claim only that the objective value stabilises. They say nothing about $\pi_k$ or $x_k$ converging, and they do not claim global optimality. Global optimality would be false: in 279 of 400 random instances the stabilised value exceeds the global minimum (`lsq_perm_global.out`).
8. **Minor points.**
   - In #7 the hypothesis `0 < M` is superfluous.
   - #1 needs neither independence of $a$ and $Z$ nor a uniform law for $a$, so it is more general than the paper's example.
   - In #15, `rc` and `rf` are not assumed measurable. This is harmless: the events differ from measurable ones only by null sets, and $\mu$ of a set is its outer measure.

---

## Per-declaration analysis

Notation: $\Phi$ is the standard normal CDF; "EM" means Euler–Maruyama; for GBM, $dS=rS\,dt+\sigma S\,dW$ and $S_T=s_0e^{(r-\sigma^2/2)T+\sigma W_T}$.

### 1. `elliptic_mlmc_theorem1` (theorem)

**Rendering.** Let $(\Omega_0,\nu)$ be a probability space. Let $a,Z:\Omega_0\to\mathbb R$ be measurable, with $a\in[0,1]$ $\nu$-a.s. and $Z\sim N(0,1)$ under $\nu$. No independence of $a$ and $Z$ is assumed.

The exact solution:
- For $a,f\in\mathbb R$, let $m_k(a)=\int_0^1 t^k/(1+at)\,dt$.
- $u(x)=\int_0^x (f m_1/m_0 - f t)/(1+at)\,dt$. This is the solution of $-((1+ax)u')'=f$ on $(0,1)$ with $u(0)=u(1)=0$.
- $P(a,f)=\int_0^1u$. Evaluating gives $P=f\,(m_2-m_1^2/m_0)$.

The discrete solution:
- $P_\ell(a,f)$ uses $n=2^{\ell+1}$ cells, $h=1/n$ and midpoints $x_{i+1/2}=(i+\tfrac12)h$.
- $U_j=\sum_{i<j}h\,(C_h-fx_{i+1/2})/(1+ax_{i+1/2})$, with $C_h=f\,m^h_1/m^h_0$, where $m^h_k$ are the midpoint sums.
- This is exactly the solution of the conservative three-point finite-difference scheme with the coefficient evaluated at cell midpoints, and $U_n=0$.
- The output is the trapezoidal rule $h[(U_0+U_n)/2+\sum_{j=1}^{n-1}U_j]$.

The random input is $f=50Z^2$.

**Claim.** There is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with every $N_\ell\ge1$ satisfying the following.
- Let $x=(x_{\ell,n})_{(\ell,n)\in\mathbb N^2}$ be i.i.d. $\sim\nu$, distributed as $\nu^{\otimes\mathbb N^2}$.
- Let $\hat Y(x)=\sum_{\ell=0}^{L}N_\ell^{-1}\sum_{n<N_\ell}(P_\ell-P_{\ell-1})(a,f)(x_{\ell,n})$, with $P_{-1}:=0$. Fine and coarse levels are evaluated at the same sample.
- Then $(\hat Y-E_\nu[P(a,50Z^2)])^2$ is integrable.
- $E[(\hat Y-E_\nu P)^2]<\varepsilon^2$.
- $\sum_{\ell\le L}N_\ell\,2^{\ell+1}\le c_4\varepsilon^{-2}$.

$c_4$ may depend on $\nu,a,Z$, but not on $\varepsilon$.

**Assessment.** True.
- *Rates.* `elliptic_fd.out` confirms the closed form $P=f(m_2-m_1^2/m_0)$ by quadrature. It shows $(P_\ell-P)/(fh^2)\to -c(a)$ with $c(a)\in[0.065,0.0834]$ for $a\in[0,1]$, and that $|P_\ell-P_{\ell-1}|\cdot4^\ell$ is constant. Hence the weak error is $\le c\,E[f]\,4^{-\ell}$ ($\alpha=2$), $V_\ell\le c\,E[f^2]\,16^{-\ell}$ with $E f^2=7500<\infty$ ($\beta=4$), and the cost is $2^{\ell+1}$ ($\gamma=1$). Giles' theorem in the case $\beta>\gamma$ gives the $c_4\varepsilon^{-2}$ bound.
- *Quantifiers.* Correct.
- *MSE.* Genuine, over independent samples.
- *Junk values.* None are exploitable: integrability is asserted and $N_\ell\ge1$. On the null set where $a\notin[0,1]$, $1+at$ can vanish and Lean's $x/0=0$ applies; this is irrelevant.
- *Hypotheses.* The separate `Measurable a` and `Measurable Z` are harmless. Allowing any law of $a$ on $[0,1]$ and any dependence between $a$ and $Z$ is a generalisation of the paper's example.
- *Vacuity.* Not vacuous: take $\Omega_0=\mathbb R^2$, $\nu=U[0,1]\otimes N(0,1)$, $a=$ first coordinate, $Z=$ second coordinate.

Standard result: the MLMC complexity theorem (Giles, Acta Numerica 2015, Thm 1; Cliffe–Giles–Scheichl–Teckentrup 2011) applied to the 1-D elliptic example $-((1+ax)u')'=50Z^2$ with output $\int_0^1u$.

### 2. `elliptic_mlmc_theorem1_uniform` (theorem)

**Rendering.** Identical to #1, except that the hypothesis $a\in[0,1]$ a.s. is replaced by $a\sim U[0,1]$ (law `volume.restrict (Icc 0 1)`, which is a probability measure).

**Assessment.** True. It is a corollary of #1, since `HasLaw` implies $a\in[0,1]$ a.s. Not vacuous: same instance as #1. No junk values. This is the paper's setting: $a\sim U(0,1)$, $Z\sim N(0,1)$. Independence is again not required.

### 3. `gbm_call_mlmc_theorem1` (theorem)

**Rendering.** For all real $r,\sigma,s_0,K$ and $T\ge0$: there is $c_4>0$ such that for all $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N_\ell\ge1$ with the following properties.

The sampling and the payoff:
- Each $x_{\ell,n}\in\mathbb R^{\mathbb N}$ is an i.i.d. $N(0,1)$ sequence, independent across $(\ell,n)$ (`infinitePi` of `stdNormalSeq`).
- $\hat Y=\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}D_\ell(x_{\ell,n})$.
- The payoff is $g(S)=e^{-rT}(S-K)^+$.

The levels:
- $D_0=g(\text{EM with 1 step of size }T)$.
- $D_{\ell+1}(z)=g(\hat S^f)-g(\hat S^c)$.
- $\hat S^f$ is EM with $2^{\ell+1}$ steps of size $h=T/2^{\ell+1}$ and $\Delta W_i=\sqrt h z_i$.
- $\hat S^c$ is EM with $2^\ell$ steps of size $2h$ and increments $\sqrt{2h}(z_{2k}+z_{2k+1})/\sqrt2=\Delta W_{2k}+\Delta W_{2k+1}$. This is the correct Brownian coupling, and $\hat S^c$ has the same law as the level-$\ell$ fine path.

The claim:
- The squared error is integrable.
- $E[(\hat Y-V)^2]<\varepsilon^2$, where $V=E\,[e^{-rT}(s_0e^{(r-\sigma^2/2)T+\sigma\sqrt Tw}-K)^+]$ with $w\sim N(0,1)$. This is the exact Black–Scholes price.
- $\sum_{\ell\le L}N_\ell2^\ell\le c_4\,\varepsilon^{-2}(\log\varepsilon)^2$.

**Assessment.** True.
- *Rates.* EM for GBM satisfies $E|\hat S_N-S_T|^2\le C h$ (see #8). The payoff is $e^{-rT}$-Lipschitz. Hence $V_\ell=O(2^{-\ell})$ ($\beta=1$), the bias is $O(2^{-\ell/2})$ ($\alpha\ge\tfrac12=\tfrac12\min(\beta,\gamma)$), and $\gamma=1$. This is the $\beta=\gamma$ case, giving $\varepsilon^{-2}(\log\varepsilon)^2$.
- *Constant.* $c_4$ depends on $(r,\sigma,s_0,K,T)$.
- *Degenerate parameters.* $T=0$: everything is exact, the MSE is $0$, and the cost is $1\le c_4\varepsilon^{-2}\log^2\varepsilon$, since the right-hand side exceeds $e^2c_4$. $\sigma=0$, $s_0\le0$, and any $K$ are all fine.
- *Junk values.* None.
- *Vacuity.* Not vacuous: $r=0.05$, $\sigma=0.2$, $s_0=K=100$, $T=1$.

Standard result: Giles (2008, Oper. Res.), the European call with EM, complexity $O(\varepsilon^{-2}(\log\varepsilon)^2)$.

### 4. `gbm_mil_call_mlmc_theorem1` (theorem)

**Rendering.** As #3, but the paths use the Milstein scheme $S_{i+1}=S_i\,(1+rh+\sigma\Delta W_i+\tfrac12\sigma^2(\Delta W_i^2-h))$.
- `deriv (fun S => σ*S) = σ`, so there is no junk value.
- The fine path has $2^{\ell+1}$ steps; the coarse path uses `pairAvg`, so each coarse increment is the sum of two fine increments.
- The cost bound is $\sum N_\ell2^\ell\le c_4\varepsilon^{-2}$.

**Assessment.** True. Milstein has strong order 1 for GBM: `gbm_strong.out` computes the exact $E|\hat S_N-S_T|^2/h^2$ in closed form and finds it bounded. Hence $V_\ell=O(4^{-\ell})$ ($\beta=2>\gamma=1$) and $\alpha\ge1$, which gives $\varepsilon^{-2}$. Quantifiers, MSE and cost model are as in #3. Not vacuous; no junk values.

Standard result: Giles (2008, "Improved MLMC convergence using the Milstein scheme").

### 5. `tamedCubic_fourth_moment_le` (theorem)

**Rendering.**
- $\mu$ is not assumed to be a probability measure, but `iIndepFun` forces $\mu(\Omega)=1$, even when $N=0$.
- $x_0\in\mathbb R$, $T\ge0$, $N\in\mathbb N$ with $T\le54N$. Equivalently $h:=T/N\le54$; $N=0$ forces $T=0$.
- $Z_0,\dots,Z_{N-1}$ each have law $N(0,1)$ and are mutually independent (family indexed by `Fin N`).
- The tamed Euler scheme for $dX=-X^3dt+dW$: $X_0=x_0$, $X_{n+1}=X_n-hX_n^3/(1+h|X_n|^3)+\sqrt hZ_n$.

Claims:
- $X_N\in L^4(\mu)$.
- $E X_N^2\le x_0^2+T$.
- $E X_N^4\le x_0^4+6x_0^2T+3T^2$. These right-hand sides are exactly the moments of $x_0+W_T$.

**Assessment.** True.
- *Proof.* Let $D(x)=x\,(1+h|x|^3-hx^2)/(1+h|x|^3)$. Then $|D(x)|\le|x|$ for all $x$ iff $h(u^2-2u^3)\le2$ for all $u\ge0$. That holds iff $h\le54$, because $\max_{u\ge0}(u^2-2u^3)=1/27$, attained at $u=1/3$. $X_n$ is a function of $Z_0,\dots,Z_{n-1}$, so it is independent of $Z_n$. Therefore $EX_{n+1}^2=ED(X_n)^2+h$ and $EX_{n+1}^4=ED^4+6hED^2+3h^2$. Induction gives both bounds.
- *Sharpness* (`tamed_cubic.out`). At $h=54$, $x_0=1/3$, $N=1$ both bounds hold with equality, since $D(1/3)=-1/3$. With $N=1$, $T=58$, $x_0=0.3$ the second-moment bound fails ($58.0963>58.09$). So $T\le54N$ is exactly the right hypothesis, not an overly strong one.
- *Further checks.* Checks at $N=2$ by quadrature also pass.
- *Junk values.* None: $\mu$ is a probability measure and $X_N\in L^4$, so the integrals are genuine. For $N=0$, $T/0=0$ is irrelevant because the path is $x_0$.
- *Vacuity.* Not vacuous: $\Omega=\mathbb R^{\mathbb N}$ with `stdNormalSeq`, $Z_n$ the coordinates, $N=1$, $T=1$.

Standard result: moment bounds for the tamed Euler scheme (Hutzenthaler–Jentzen–Kloeden 2012). Here it is a sharp explicit version for the drift $-x^3$ with additive noise.

### 6. `gbmExactM` (definition)

**Rendering.** $\mathrm{gbmExactM}(r,\sigma,T,s_0,m,M,\ell,z)=s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt{T/(mM^\ell)}\sum_{i<mM^\ell}z_i\big)$. This is the exact GBM value at time $T$, driven by $mM^\ell$ Brownian increments of size $T/(mM^\ell)$. Lean conventions: if $T<0$, $\sqrt{\cdot}=0$; if $m=0$, $T/0=0$ and the sum is empty.

### 7. `gbmExactM_blockAvg` (theorem)

**Rendering.** For $M>0$: $\mathrm{gbmExactM}(\dots,m,M,\ell,\mathrm{blockAvg}_Mz)=\mathrm{gbmExactM}(\dots,m,M,\ell+1,z)$, where $\mathrm{blockAvg}_Mz(k)=M^{-1/2}\sum_{i<M}z_{Mk+i}$.

**Assessment.** True for all real parameters. Regroup the sum: $\sum_{k<mM^\ell}\sum_{i<M}z_{Mk+i}=\sum_{j<mM^{\ell+1}}z_j$. Then use $\sqrt x/\sqrt M=\sqrt{x/M}$ (`Real.sqrt_div'`, valid for every $x$ when $M\ge0$).

The identity holds for every $T$; when $T<0$ both sides degenerate in the same way, so it is not junk-dependent. The hypothesis `0 < M` is **superfluous**: for $M=0$, `blockAvg 0 = 0/0 = 0` and both sides equal $s_0e^{(r-\sigma^2/2)T}$. This is harmless.

Meaning: the exact solution is invariant under the fine-to-coarse increment map, which is the coupling identity used in #9. Not vacuous.

### 8. `gbm_weak_error_le_M` (theorem)

**Rendering.** Assumptions:
- $T\ge0$, $m\ge1$, $M\ge1$, $\ell\in\mathbb N$.
- $|g(x)-g(y)|\le K|x-y|$. This forces $K\ge0$.
- $\hat S$ is EM for GBM with $h=T/(mM^\ell)$ and $mM^\ell$ steps (terminal time $T$), driven by an i.i.d. $N(0,1)$ sequence.

Claim: $\big|E\,g(\hat S_{mM^\ell})-E\,g(S_T)\big|\le K\sqrt{C\,T/(mM^\ell)}$, where $C=\texttt{gbmStrongConst}=s_0^2e^{(2|r|+\sigma^2)T}(|r|+\sigma^2)(5(|r|+\sigma^2)T+4)$.

**Assessment.** True. The weak error is at most $K\,E|\hat S-S_T|\le K\sqrt{E|\hat S-S_T|^2}$, comparing on the same Brownian path. So the claim follows from the strong bound $E|\hat S_N-S_T|^2\le C\,h$.

Checking the strong bound:
- *Closed form.* $E|\hat S_N-S_T|^2/s_0^2=u^N-2w^N+z^N$, with $u=(1+rh)^2+\sigma^2h$, $w=e^{rh}(1+rh+\sigma^2h)$, $z=e^{(2r+\sigma^2)h}$. It agrees with quadrature.
- *Grid and random search* (`gbm_strong.out`, `gbm_strong_extreme.out`). About 57,000 points (a 6,984-point grid plus 20,000 and 29,806 random draws) with $|r|$ up to 100, $\sigma$ up to 10, $T$ from $10^{-4}$ to 100, $N$ up to $10^6$ (cases with $|r|T+\sigma^2T>3000$ were skipped). The maximum of $\text{error}^2/(Ch)$ is $0.0989$.
- *Asymptotics.* The leading term is $s_0^2e^{(2r+\sigma^2)T}\sigma^4Th/2\le Ch/10$.
- *Rigorous case $r=0$.* $\text{error}^2=s_0^2\big(e^x-(1+x/N)^N\big)\le s_0^2e^x x^2/(2N)$, where $x=\sigma^2T$.

Degenerate case $T=0$: both sides are 0. No junk values: $g$ is Lipschitz and the paths have all moments.

The stated weak order is only $\tfrac12$, which is weaker than the classical weak order 1 for smooth payoffs, but sufficient for MLMC. Not vacuous: $g=\mathrm{id}$, $K=1$.

Standard result: strong order $\tfrac12$ of EM for GBM (Kloeden–Platen), used as in Giles 2008.

### 9. `gbm_correction_variance_le_M` (theorem)

**Rendering.** Same hypotheses as #8.
- The fine path is EM with $mM^{\ell+1}$ steps of size $h_f=T/(mM^{\ell+1})$.
- The coarse path is EM with $mM^\ell$ steps of size $Mh_f$ and increments $\sqrt{Mh_f}\,\mathrm{blockAvg}_Mz_k=\sqrt{h_f}\sum_{i<M}z_{Mk+i}$, which is the correct coupling.
- Claim: $\operatorname{Var}[g(\hat S^f)-g(\hat S^c)]\le 2K^2\,C\,(T/m)(M+1)/M^{\ell+1}$.

**Assessment.** True.
- *Proof.* $\operatorname{Var}\le E(\cdot)^2\le K^2E(\hat S^f-\hat S^c)^2\le2K^2\big(E(\hat S^f-S_T)^2+E(\hat S^c-S_T)^2\big)$. Both paths have the same exact $S_T$, by #7. Applying the strong bound from #8 to each term gives $\le2K^2C(h_f+Mh_f)$, which is exactly the right-hand side.
- *Junk values.* None: the random variable is in $L^2$, so `variance = evariance.toReal` is not the $\infty\mapsto0$ junk value.
- *Vacuity.* Not vacuous.

Standard result: the $\beta=1$ variance bound for EM-based MLMC with a Lipschitz payoff.

### 10. `gbm_mlmc_theorem1_M` (theorem)

**Rendering.** As #3, with these changes:
- Refinement factor $M\ge2$.
- The coarsest level has $m\ge1$ steps ($h_0=T/m$); level $\ell$ uses $mM^\ell$ fine steps, coupled to $mM^{\ell-1}$ coarse steps through `blockAvg`.
- General $K$-Lipschitz payoff $g$.
- Reference value $E\,g(S_T)$.

Claim: $\exists c_4>0\ \forall\varepsilon\in(0,e^{-1})\ \exists L,N_\ell\ge1$ with an integrable squared error, $\mathrm{MSE}<\varepsilon^2$, and $\sum_{\ell\le L}N_\ell\,mM^\ell\le c_4\varepsilon^{-2}(\log\varepsilon)^2$.

**Assessment.** True. It follows from #8 ($\alpha=\tfrac12$ in base $M$) and #9 ($\beta=1$), with $\gamma=1$. Since $L\approx2\log_M\varepsilon^{-1}$, $(L+1)^2\le c\log^2\varepsilon$ for $\varepsilon<e^{-1}$, and the level-sum overhead $\sum_\ell mM^\ell=O(\varepsilon^{-2})$. $c_4$ depends on $(r,\sigma,s_0,T,m,M,g,K)$. The hypothesis $M\ge2$ is appropriate. No junk values; not vacuous.

Standard result: Giles 2008 Theorem 3.1 with a general refinement factor $M$.

### 11. `exists_lsq_minimiser` (theorem)

**Rendering.** $X$ is any real vector space (possibly infinite-dimensional), $\iota$ is finite, $A:X\to\mathbb R^\iota$ is linear, and $b\in\mathbb R^\iota$. Then there is $x$ with $\|b-Ax\|_2^2\le\|b-Ay\|_2^2$ for all $y$.

**Assessment.** True. The range of $A$ is a finite-dimensional, hence closed, subspace of $\mathbb R^\iota$. The orthogonal projection of $b$ onto it is attained, at some $Ax$. This is a genuine existence statement: it would fail for a non-closed range in infinite dimensions. Not vacuous: $X=\mathbb R$, $Ax=(x,x)$, $b=(0,1)$, minimiser $x=\tfrac12$.

Standard result: existence of least-squares solutions (normal equations).

### 12. `method2_iteration_exists` (theorem)

**Rendering.** Given $A$, $Z\in\mathbb R^\iota$ and $\pi^0\in S_\iota$, there exist sequences $\pi_k\in S_\iota$ and $x_k\in X$ with:
- (i) $\pi_0=\pi^0$;
- (ii) $x_k\in\arg\min_y\|Z\circ\pi_k-Ay\|^2$;
- (iii) $\pi_{k+1}\in\arg\min_{p\in S_\iota}\|Z\circ p-Ax_k\|^2$;
- (iv) $F_k:=\|Z\circ\pi_k-Ax_k\|^2$ is eventually constant.

**Assessment.** True.
- *Construction.* Use #11 for each $x_k$; $S_\iota$ is finite, so each $\pi_{k+1}$ exists.
- *Monotonicity.* $F_{k+1}\le\|Z\circ\pi_{k+1}-Ax_k\|^2\le F_k$.
- *Stabilisation.* $F_k=G(\pi_k)$, where $G(\pi)=\min_y\|Z\circ\pi-Ay\|^2$ takes finitely many values. So $F_k$ is eventually constant.

The existential quantifier is not exploited, since every such alternating sequence stabilises. The statement is weak in two ways:
- Only the objective value stabilises; nothing is claimed about $\pi_k$ or $x_k$.
- Global optimality is not claimed, and it would be false: in 279 of 400 random instances the stabilised value exceeds the global minimum (`lsq_perm_global.out`).

`lsq_perm.out` confirms the monotone decrease and the stabilisation. Not vacuous.

Standard result: monotone convergence of alternating minimisation over a finite set.

### 13. `method2_sorting_iteration_exists` (theorem)

**Rendering.** As #12 with $\iota=\mathrm{Fin}\,n$ and $Z$ monotone. The permutation step is replaced by a ranking condition: $(Ax_k)_i<(Ax_k)_j\Rightarrow\pi_{k+1}(i)<\pi_{k+1}(j)$. Conditions (i), (ii) and (iv) are unchanged.

**Assessment.** True. A ranking permutation exists: sort by $Ax_k$, breaking ties by index. Because $Z$ is monotone, $Z\circ\pi_{k+1}$ is similarly ordered to $Ax_k$. By the rearrangement inequality, $\pi_{k+1}$ minimises $\|Z\circ p-Ax_k\|^2$ over all $p$. The argument of #12 then applies.

`lsq_perm.out` checked exhaustively on random 5-element instances that the sorting permutation is optimal. Same caveats as #12. Not vacuous; for $n=0$ it is trivial.

### 14. `roundFixed_coarse_increment_mean` (theorem)

**Rendering.**
- $\mathrm{roundFixed}(e,d,x)=2^{e-d}\operatorname{round}(x/2^{e-d})$, with Mathlib's `round` ($\lfloor x+\tfrac12\rfloor$, ties up).
- $Q=2^{e-B}$ is the coarse spacing, $\mathrm{rc}=\mathrm{roundFixed}(e,B,\cdot)$, and $\mathrm{rf}=\mathrm{roundFixed}(e,B+1,\cdot)$ has spacing $Q/2$.
- $X_1,X_2$ are i.i.d. $N(0,v)$ with $v>0$; `HasLaw` makes $\mu$ a probability measure.

Claims:
- (i) $\mathrm{rc}(X_1+X_2)$ is integrable with mean $0$.
- (ii) $\mathrm{rc}(\mathrm{rf}X_1+\mathrm{rf}X_2)$ is integrable with mean $>0$.
- (iii) $\mathrm{rc}(\mathrm{rf}X_1)+\mathrm{rc}(\mathrm{rf}X_2)$ is integrable with mean $>0$.

**Assessment.** True.
- *(i).* By symmetry, since ties have probability 0.
- *(ii) and (iii).* With $K_i=\operatorname{round}(2X_i/Q)$, which is symmetric, only odd values produce coarse ties, and those round up. This gives exactly $E(\text{ii})=Q\,p(1-p)$ and $E(\text{iii})=Q\,p$, where $p=P(K_i\text{ odd})>0$.

Exact values (`rounding.out`), as multiples of $Q$, at $Q/s=0.5$, $2$, $4$, $8$ (here $p\approx\tfrac12$ whenever $Q/s\le1$):

| $Q/s$ | $E(\text{ii})/Q$ | $E(\text{iii})/Q$ |
|---|---|---|
| 0.5 | 0.25 | 0.5 |
| 2 | 0.24998 | 0.49542 |
| 4 | 0.21563 | 0.31461 |
| 8 | 0.04343 | 0.04550 |

Monte Carlo with $4\cdot10^5$ samples agrees, e.g. $0.2513$ and $0.4975$ at $Q/s=2$.

**The positivity depends on the convention.** It comes entirely from Mathlib's ties-up `round`. With IEEE ties-to-even, or ties-away-from-zero, both means are exactly $0$ (`rounding_ties.out`). $v\ne0$ is necessary: for $v=0$ all means are $0$. Not vacuous: $\Omega=\mathbb R^2$, $\mu=N(0,1)^{\otimes2}$, $e=B=0$.

Standard fact: double-rounding bias.

### 15. `nearestRound_coarse_increment_pos_prob` (theorem)

**Rendering.** Assumptions:
- $q>0$.
- $\mathrm{rc}:\mathbb R\to2q\mathbb Z$ with $|x-\mathrm{rc}\,x|\le q$. This is any nearest rounding to the coarse grid, with arbitrary per-point tie-breaking, and it is not assumed measurable.
- $\mathrm{rf}:\mathbb R\to q\mathbb Z$ with $|x-\mathrm{rf}\,x|\le q/2$.
- $X_1,X_2$ are i.i.d. $N(0,v)$ with $v>0$.

The hypotheses force $\mathrm{rc}(q)\in\{0,2q\}$. Claims, where $\mu$ of a set is its outer measure:
- (a) If $\mathrm{rc}(q)>0$: $\mu\{\mathrm{rc}(X_1+X_2)>0\}<\mu\{\mathrm{rc}(\mathrm{rf}X_1+\mathrm{rf}X_2)>0\}$.
- (b) If $\mathrm{rc}(q)\le0$: the reverse strict inequality.

**Assessment.** True. Let $K_i=\mathrm{rf}(X_i)/q$, a nearest integer to $X_i/q$, a.s. unique, and $Y=X_1+X_2$. Up to null sets:
- $\{\mathrm{rc}(Y)>0\}=\{Y>q\}$.
- $\{\mathrm{rc}(qK_1+qK_2)>0\}=\{K_1+K_2\ge2\}$, together with $\{K_1+K_2=1\}$ when $\mathrm{rc}(q)>0$.

Since $|X_i/q-K_i|\le\tfrac12$, we have $Y>q\Rightarrow K_1+K_2\ge1$ and $K_1+K_2\ge2\Rightarrow Y\ge q$. Both differences have positive probability: for example, $X_1/q\in(0.5,0.6)$ with $X_2/q\in(-0.1,0.1)$ for (a), and $X_1/q\in(1.0,1.1)$ with $X_2/q\in(0.2,0.3)$ for (b).

Numerics (`rounding.out`), with $t=q/s\in[10^{-3},100]$, $A=P(Y>q)=\Phi(-t/\sqrt2)$, $B_{\rm up}=P(K_1+K_2\ge1)$ and $B_{\rm down}=P(K_1+K_2\ge2)$:
- $\min B_{\rm up}/A=1.00028$ and $\max B_{\rm down}/A=0.99972$; both ratios tend to 1 as $t\to0$.
- At $t=1$: $A=0.23975$, $B_{\rm up}=0.36454$, $B_{\rm down}=0.14939$.

Non-measurability of `rc` and `rf` is harmless, because each event differs from a measurable one by a null set. Not vacuous: both cases are realised, by ties-up and ties-down nearest rounding.

### 16. `roundFixed_coarse_increment_pos_prob` (theorem)

**Rendering.** With $Q=2^{e-B}$ and $X_1,X_2$ i.i.d. $N(0,v)$, $v>0$: $P(\mathrm{rc}(X_1+X_2)>0)<P(\mathrm{rc}(\mathrm{rf}X_1+\mathrm{rf}X_2)>0)$, with `rc` and `rf` as in #14.

**Assessment.** True. It is the instance of #15(a) with $q=Q/2$: Mathlib gives $\operatorname{round}(1/2)=1$, so $\mathrm{rc}(q)=Q>0$.

Exact values: $1-\Phi(Q/(2\sqrt2s))$ vs $P(K_1+K_2\ge1)$. At $Q/s=2$ these are $0.23975$ vs $0.36454$; Monte Carlo gives $0.2405$ vs $0.3658$.

**The direction depends on the convention.** Under IEEE ties-to-even, $\mathrm{rc}(q)=0$ and the inequality reverses: $0.23975$ vs $0.14939$. Ties-away-from-zero gives the same as ties-up. Not vacuous; no junk values.

### 17. `truncGrid` (definition)

**Rendering.** $T_c(x)=c\lfloor x/c\rfloor$, truncation towards $-\infty$ onto the grid $c\mathbb Z$. For $c=0$ it is the junk value $0$; it is not used with $c=0$, since $q>0$.

### 18. `truncGrid_coarse_increment_mean_lt` (theorem)

**Rendering.** Let $q>0$ and $X_1,X_2$ be i.i.d. $N(0,v)$ with $v>0$. Claims:
- (i) For every $\omega$: $T_{2q}(T_qX_1)+T_{2q}(T_qX_2)\le T_{2q}(T_qX_1+T_qX_2)\le T_{2q}(X_1+X_2)$.
- (ii) The three quantities are integrable.
- (iii) Their means satisfy the same two inequalities strictly.

**Assessment.** True.
- *Pointwise inequalities.* The first holds because $\lfloor\cdot\rfloor$ is superadditive. The second holds because $T_qx\le x$ and $T_{2q}$ is monotone.
- *Exact means.* They are $-2q<-\tfrac32q<-q$ for every $v>0$, and indeed for any symmetric continuous law. With $k=\lfloor X/q\rfloor$, the law of $k$ is symmetric under $k\mapsto-1-k$. So $E\lfloor X/c\rfloor=-\tfrac12$, $P(k\text{ odd})=\tfrac12$, $E\lfloor k/2\rfloor=-\tfrac12$ and $E\lfloor(k_1+k_2)/2\rfloor=-\tfrac34$. This is confirmed exactly for $t$ from 0.01 to 30 and by Monte Carlo (`rounding.out`).
- *Necessity of $v>0$.* For $v=0$ all quantities are $0$ and the strict inequalities fail.
- *Junk values.* None.
- *Vacuity.* Not vacuous.

Standard fact: truncation (round towards $-\infty$) bias.
