# Blind read-back report: packet R34 (remarks)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round22/packet_R34_remarks.lean` |
| declarations audited | 15 (14 theorems + 1 definition, `dirichletHeatStep`) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round22/work_R34/` (`*.py` with matching `*.out`; Lean scratch files `scratch_R34.lean`, `combined_R34.lean` with `.lean.out`) |

Lean elaboration: the statements were compiled with `sorry` proofs (`scratch_R34.lean`, `combined_R34.lean`, using `import MlmcLean`), and both files compile. `combined_R34.lean` also contains these checks, all of which pass:

- **Definitions match.** Every definition appended to the packet (`ml2rNode`, `ml2rWeight`, `pairAvg`, `stdNormalSeq`, `gbmEM`, `gbmStrongConst`, `normCDFInv`, `normCDF`, `emPath`, `gbmDrift`, `gbmVol`) and the packet's own `dirichletHeatStep` agree with the imported ones by `rfl`.
- **Statements match.** Each of the 14 packet statements is closed by the imported theorem of the same name, so the packet matches the repo statements up to defeq.
- **Parsing.** Probes confirm that `(N:ℝ)⁻¹ * ∑ n ∈ range N, f n - EP` parses as $\bigl(N^{-1}\sum_n f_n\bigr) - EP$, and likewise that `∑ ℓ ∈ range (L+1), w ℓ * e ℓ - EP` parses as $(\sum_\ell w_\ell e_\ell) - EP$.
- **Literals and casts.** `2 ^ (ℓ+1)` in the cost theorem is real, `ε ^ (-3 : ℝ)` is `Real.rpow`, and `(L:ℝ) * (L+1) / 2` casts $L$ before adding 1.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `ml2r_bias_not_attainable` | theorem | true | no | no |
| 2 | `variance_smoothCDF_correction_le` | theorem | true | no | no |
| 3 | `tendsto_variance_smoothCDF_correction` | theorem | true | no | no |
| 4 | `dirichletHeatStep` | def | n/a (faithful explicit FTCS step with Dirichlet boundary) | n/a | ℕ-subtraction `j - 1` only used when `0 < j`: harmless |
| 5 | `dirichletHeat_stable` | theorem | true | no | no |
| 6 | `dirichletHeat_unstable` | theorem | true | no | no |
| 7 | `nested_inputs_mlmc` | theorem | true | no | no |
| 8 | `nested_vector_inputs_mlmc` | theorem | true | no | no |
| 9 | `nested_mc_cost_upper` | theorem | true | no | no |
| 10 | `nested_mc_cost_lower` | theorem | true | no | no |
| 11 | `ouEM_invariant` | theorem | true | no | no |
| 12 | `tendsto_ouEM_invariant` | theorem | true | no | no |
| 13 | `tendstoInDistribution_normCDFInv_midpoint` | theorem | true | no | no; conjunct (a) shows the junk branch of `normCDFInv` is never hit |
| 14 | `gbm_em_identity_variance_two_sided` | theorem | true | no | no |
| 15 | `gbm_em_identity_variance_cost` | theorem | true | no | no |

## Main points for a human auditor

1. **Every statement is true, none is vacuous, and none depends on a junk value.** The audit found no false statement.
2. **`ml2r_bias_not_attainable`, conjunct 1, uses remainder exponent $L$ instead of the usual $L+1$.** The conjunct verifies the weak-error expansion for the toy model, with all coefficients zero, truncation order $L$ and remainder $\le |d|\,n_\ell^{L}$. The usual remainder is $O(n_\ell^{L+1})$. Both forms hold here, because the bias is supported on $\ell=0$, where $n_0=1$. Check the paper's exact assumption.
   - The model's bias is exactly $w_0 d \asymp 2^{-\alpha L(L+1)/2}$. This rate matches the known ML2R rate $M^{-\alpha R(R-1)/2}$ with $R=L+1$ and $M=2$, and conjunct 5 shows it is not $O(2^{-\alpha L^2})$.
3. **`gbm_em_identity_variance_two_sided`: the step-size condition looks sufficient rather than necessary, and the lower bound is sharp.**
   - The hypothesis $|r|T\le 2^\ell$ applies to both bounds. Numerically, neither bound fails outside it (`gbm_outside_hyp.out`, `gbm_a_minus1.out`).
   - The lower bound is attained exactly at $r=0,\ \ell=0$, and the ratio tends to 1 as $\sigma^2T, |r|T\to0$.
   - The upper bound has a lot of slack: Var/upper $\le 0.017$ over 40k random cases.
   - I derived the exact variance in closed form, verified the per-pair moments symbolically, and checked the formula against the literal `emPath` recursion. Both bounds hold over every sampled case, including the edge $|r|T=2^\ell$.
4. **`nested_mc_cost_upper` needs $\varepsilon\le1$ and fixes $N$ and $M$.**
   - The hypothesis $\varepsilon\le1$ is genuinely used. Without it, $v=c=0,\ \varepsilon=10$ gives $NM=1 > 10^{-3}$.
   - $c\ge0$ and $v\ge0$ are not assumed, but they follow from the hypotheses at $M=1$.
   - $N$ and $M$ are pinned to explicit formulas, so the existential is not doing any work.
   - The cost model is abstract ($N\cdot M$), and the inner sampling is hidden inside $\Omega_0$ and `PM M`.
5. **`nested_mc_cost_lower` concerns one estimator, and $c\ge0$ is needed.** The statement is about a single estimator $P$ with bias $\ge c/M$ and variance $\ge v$. The hypothesis $c\ge0$ is necessary: with $c<0$ and $v<0$ the conclusion can fail.
6. **`dirichletHeat_unstable`: the $\exists J_0$ is essential.** For $\lambda=0.51$ every $J\le 11$ is stable, and for $\tfrac12<\lambda\le1$ the grid $J=2$ is stable (`heat_check.out`).
7. **`tendsto_variance_smoothCDF_correction`: the no-atom hypotheses are needed.** The hypotheses $\mu\{P_f=x\}=\mu\{P_c=x\}=0$ cannot be dropped. With an atom at $x$ and $g(0)\neq0$, the limit is wrong.
8. **`nested_inputs_mlmc` does not require $\nu_\ell$ to be finite.** This is fine: $(\nu\otimes\rho).\mathrm{map}\ \mathrm{fst}=\nu$ needs only that $\rho$ is a probability measure (Mathlib `measurePreserving_fst`). The `Measure.map` terms are genuine pushforwards, because integrability gives AE-measurability.

---

## 1. `ml2r_bias_not_attainable`

**Rendering.**
Hypotheses: $\alpha\in\mathbb R$ with $\alpha>0$; $EP, d\in\mathbb R$ with $d\ne0$; $EP_\ell = EP + d\,[\ell=0]$ for all $\ell\in\mathbb N$.

Notation:
- Nodes: $n_\ell = 2^{-\alpha\ell}$ (real power).
- Weights: $w^L_\ell=\prod_{k\in\{0..L\}\setminus\{\ell\}} \frac{n_k}{n_k-n_\ell}$. This is the Lagrange basis polynomial at nodes $n_0,\dots,n_L$, evaluated at 0.

Conclusion (five conjuncts):
1. For all $L$ and all $\ell\le L$: $\bigl|EP_\ell-EP-\sum_{n=1}^{L}0\cdot n_\ell^{n}\bigr|\le |d|\,n_\ell^{L}$, with natural-number powers.
2. For all $L$: $\sum_{\ell=0}^{L} w^L_\ell EP_\ell - EP = w^L_0 d$.
3. For all $L$: $|w^L_0| = 2^{-\alpha L(L+1)/2}\big/\prod_{k=1}^{L}(1-n_k)$.
4. For all $L$: $|d|\,2^{-\alpha L(L+1)/2}\le\bigl|\sum_\ell w^L_\ell EP_\ell-EP\bigr|$.
5. $\bigl|\sum_\ell w^L_\ell EP_\ell-EP\bigr|\big/2^{-\alpha L^2}\to+\infty$ as $L\to\infty$.

**Assessment.** True.
1. Conjunct 1. The left side is $|d|$ at $\ell=0$, where $n_0^L=1$, and $0$ otherwise.
2. Conjunct 2. The nodes are distinct because $\alpha>0$, so $\sum_\ell w_\ell=1$ (Lagrange interpolation of the constant 1, evaluated at 0). Then $\sum w_\ell(EP+d[\ell=0])-EP=w_0d$.
3. Conjunct 3. $w_0=\prod_{k=1}^L \frac{n_k}{n_k-1}$. Since $0<n_k<1$ for $k\ge1$, its absolute value is $\prod n_k/\prod(1-n_k)$, and $\prod_{k=1}^L 2^{-\alpha k}=2^{-\alpha L(L+1)/2}$.
4. Conjunct 4. $0<\prod(1-n_k)\le1$.
5. Conjunct 5. The ratio is at least $|d|\,2^{\alpha(L^2-L)/2}\to\infty$.

Checks: `ml2r_check.out` confirms conjuncts 2–5 and the moment identities $\sum_\ell w_\ell n_\ell^j=0$ for $1\le j\le L$, at 60 digits, for $\alpha\in\{0.1,0.5,1,2\}$ and $L\le12$.

- **Vacuity:** not vacuous, e.g. $\alpha=1,\ d=1,\ EP=0$.
- **Junk values:** none. Every power has base $2>0$, and every denominator is nonzero.
- **Hypotheses and form:** conjunct 1 is a conclusion stated with remainder order $L$ rather than $L+1$ (see Main point 2). The $L+1$ form would also hold.

**Standard fact.** In multilevel Richardson–Romberg (ML2R, Lemaire–Pagès), the weights are Lagrange/Vandermonde weights. The residual bias is $\propto\prod_k n_k = 2^{-\alpha L(L+1)/2}$ (the $M^{-\alpha R(R-1)/2}$ factor), and it is not $O(2^{-\alpha L^2})$.

## 2. `variance_smoothCDF_correction_le`

**Rendering.**
Setting: $(\Omega,\mu)$ is a probability space. $P_f$ and $P_c$ are a.e.-strongly measurable, and $P_f-P_c\in L^2(\mu)$. The function $g:\mathbb R\to\mathbb R$ is $K$-Lipschitz with $K\in\mathbb R_{\ge0}$, $\delta>0$ and $x\in\mathbb R$. Write $D=g((x-P_f)/\delta)-g((x-P_c)/\delta)$.

Conclusion:
- $D\in L^2(\mu)$, and
- $\operatorname{Var}_\mu(D)\le (K/\delta)^2\,\mathbb E[(P_f-P_c)^2]$.

**Assessment.** True. We have $|D|\le (K/\delta)|P_f-P_c|$ pointwise, and $D$ is AE-strongly measurable as a continuous function of AE-strongly-measurable maps. Hence $D\in L^2$, and $\operatorname{Var}D\le\mathbb E D^2\le (K/\delta)^2\mathbb E(P_f-P_c)^2$.

Numerical check: $U\sim\mathrm{Unif}(0,1)$, $P_f=U$, $P_c=U^2$ and a clamp $g$ (`smoothcdf_check.out`); the bound holds for every $\delta$ tested.

- **Vacuity:** not vacuous: $P_f=P_c=0$ and $g=\mathrm{id}$.
- **Junk values:** none. Mathlib `variance` is `evariance.toReal`, which is finite because $D\in L^2$, and the integral is of an integrable function.
- **Hypotheses:** none unusual. $P_f$ and $P_c$ need not be individually square-integrable.

**Standard fact.** This is the variance bound for the smoothed-indicator MLMC correction in CDF estimation (Giles–Nagapetyan–Ritter): $V_\ell\lesssim \delta^{-2}\,\mathbb E|P_f-P_c|^2$.

## 3. `tendsto_variance_smoothCDF_correction`

**Rendering.**
Setting: $(\Omega,\mu)$ is a probability space and $P_f,P_c$ are AE-measurable. The function $g$ is continuous, with $g(y)=0$ for $y<-1$ and $g(y)=1$ for $y>1$. The point $x$ satisfies $\mu\{P_f=x\}=\mu\{P_c=x\}=0$.

Conclusion:
- (a) $D_\delta := g((x-P_f)/\delta)-g((x-P_c)/\delta)\in L^2$ for every $\delta>0$.
- (b) $\mathbf 1\{P_f<x\}-\mathbf 1\{P_c<x\}\in L^2$.
- (c) $\operatorname{Var}(D_\delta)\to \operatorname{Var}(\mathbf 1\{P_f<x\}-\mathbf 1\{P_c<x\})$ as $\delta\to0^+$, with $\delta$ real and the filter $\mathcal N_{>}(0)$.

**Assessment.** True.
- $g$ is bounded, because it is continuous on $[-1,1]$ and constant outside. That gives (a) and (b).
- Where $P_f\ne x$, $(x-P_f)/\delta\to\pm\infty$, so $g(\cdot)\to\mathbf 1\{P_f<x\}$. This holds a.e. by the no-atom hypothesis, and the same is true for $P_c$.
- Dominated convergence along the countably generated filter gives convergence of $\mathbb E D_\delta$ and $\mathbb E D_\delta^2$, hence of the variance. That gives (c).

Numerical check: the variance converges to $p(1-p)$ with $p=\sqrt{.5}-.5$ (`smoothcdf_check.out`).

- **Vacuity:** not vacuous: $P_f=P_c=0$, $x=1$, $g=\mathrm{clamp}((y+1)/2)$.
- **Junk values:** none.
- **Hypotheses:**
  - The no-atom hypotheses are necessary. If $P_f=x$ with probability $\tfrac12$, $P_c\equiv x+1$ and $g(0)\neq0$, the limit is $g(0)^2/4\ne0$.
  - Continuity of $g$ is slightly more than needed (bounded measurable would do), but it is natural.

**Standard fact.** In the Giles–Nagapetyan–Ritter smoothing, as the smoothing width $\delta\to0$ the smoothed correction's variance tends to the variance of the indicator correction (dominated convergence).

## 4. `dirichletHeatStep` (definition)

**Rendering.**
For $\lambda\in\mathbb R$, $J\in\mathbb N$, forcing $w$ and grid function $u:\mathbb N\to\mathbb R$, the new value at $j$ is:
- $u_j+\lambda(u_{j+1}-2u_j+u_{j-1})+w_j$ if $0<j<J$;
- $u_j$ otherwise, i.e. the boundary nodes $j=0,J$ and the out-of-domain nodes $j>J$ are frozen.

**Assessment.** This is the explicit forward-time centred-space (FTCS) Euler step for $u_t=u_{xx}$ (plus forcing) with Dirichlet boundary conditions and $\lambda=\Delta t/\Delta x^2$. The natural-number subtraction in $u(j-1)$ is used only when $j\ge1$, so it is harmless. It agrees with the imported definition (`rfl`).

## 5. `dirichletHeat_stable`

**Rendering.**
Hypotheses:
- $0\le\lambda\le\tfrac12$ and $J\in\mathbb N$.
- $U$ and $V$ are sequences of grid functions with $U_{n+1}=S_{w_n}(U_n)$ and $V_{n+1}=S_{w_n}(V_n)$: the same step and the same forcing $w_n$.
- $|U_0(j)-V_0(j)|\le M$ for all $j\le J$.

Conclusion: for every $n$, $U_n(0)=U_0(0)$, $U_n(J)=U_0(J)$, and $|U_n(j)-V_n(j)|\le M$ for all $j\le J$.

**Assessment.** True.
- The boundary values are frozen by the definition, including when $J=0$.
- For the error $E_n=U_n-V_n$ (the forcing cancels), at interior nodes $E_{n+1}(j)=(1-2\lambda)E_n(j)+\lambda E_n(j+1)+\lambda E_n(j-1)$.
- This is a convex combination when $0\le\lambda\le\tfrac12$, and its indices stay within $\{0..J\}$. Induction then gives the discrete maximum principle.
- Random tests: `heat_check.out`, 300 random trials, no growth.

- **Vacuity:** not vacuous: $\lambda=\tfrac14$, $J=4$, $w=0$, any $U_0,V_0$ with $M=\max_{j\le J}|U_0(j)-V_0(j)|$.
- **Junk values:** none.
- **Hypotheses:** none unusual.

**Standard fact.** This is $\ell^\infty$ stability (maximum principle) of explicit Euler for the heat equation under the CFL condition $\lambda\le\tfrac12$.

## 6. `dirichletHeat_unstable`

**Rendering.**
For $\lambda>\tfrac12$ there exists $J_0\in\mathbb N$ such that for every $J\ge J_0$ there exists $v:\mathbb N\to\mathbb R$ with $v(0)=v(J)=0$ and $|v(j)|\le1$ for all $j$, such that $|(S_0^{\,n}v)(1)|\to\infty$ as $n\to\infty$. Here $S_0$ is the unforced step and $S_0^{\,n}$ is its $n$-fold iterate.

**Assessment.** True.
1. Take the mode $v_j=\sin(j(J-1)\pi/J)$. It is an eigenvector of the interior update with eigenvalue $\mu=1-4\lambda\cos^2(\pi/(2J))$.
2. $\mu<-1$ as soon as $\cos^2(\pi/(2J))>1/(2\lambda)$, which holds for all large $J$ because the left side increases to 1.
3. $v_1=\sin(\pi/J)\ne0$ for $J\ge2$, so $|\mu|^n|v_1|\to\infty$.

The $\exists J_0$ is essential.
- For $\lambda=0.51$ the first unstable grid is $J=12$, and for $\lambda\in(\tfrac12,1]$ the grid $J=2$ is stable.
- $J_0\le1$ would be false, because $J=0$ or $J=1$ has no interior.

Simulated growth is shown in `heat_check.out`.

- **Vacuity:** not vacuous: e.g. $\lambda=1$, with $J_0=3$.
- **Junk values:** none.

**Standard fact.** This is the instability of explicit FTCS for $\lambda>\tfrac12$ (von Neumann/eigenvalue analysis: the highest mode is amplified by a factor $|1-4\lambda\cos^2(\pi/2J)|>1$).

## 7. `nested_inputs_mlmc`

**Rendering.**
Setting:
- Measurable spaces $X_\ell$ and $Z_\ell$.
- Measures $\nu_\ell$ on $X_\ell$, which may be arbitrary.
- Probability measures $\rho_\ell$ on $Z_\ell$.
- Maps $\mathrm{split}_\ell:X_{\ell+1}\to X_\ell\times Z_\ell$, each measure-preserving from $\nu_{\ell+1}$ to $\nu_\ell\otimes\rho_\ell$.
- Functions $P_\ell\in L^1(\nu_\ell)$.

Conclusion:
- (a) $\mathrm{law}_{\nu_{\ell+1}}\bigl(P_\ell(\mathrm{split}_\ell(\xi)_1)\bigr)=\mathrm{law}_{\nu_\ell}(P_\ell)$ for every $\ell$, as equality of pushforward measures.
- (b) $\int P_\ell(\mathrm{split}_\ell(\xi)_1)\,d\nu_{\ell+1}=\int P_\ell\,d\nu_\ell$.
- (c) For all $L$: $\int P_0\,d\nu_0+\sum_{\ell<L}\int\bigl(P_{\ell+1}-P_\ell\circ\mathrm{fst}\circ\mathrm{split}_\ell\bigr)\,d\nu_{\ell+1}=\int P_L\,d\nu_L$.

**Assessment.** True.
- $\mathrm{fst}\circ\mathrm{split}_\ell$ is measure-preserving from $\nu_{\ell+1}$ to $\nu_\ell$, since $(\nu\otimes\rho)\circ\mathrm{fst}^{-1}=\rho(\text{univ})\,\nu=\nu$. In Mathlib, `map_fst_prod` and `measurePreserving_fst` need only `SFinite`/`IsProbabilityMeasure` on the second factor.
- $P_\ell$ is AE-measurable, so (a) follows from `map_map`. Then (b) follows, and (c) is linearity plus telescoping; both integrands are integrable.

- **Vacuity:** not vacuous.
  - Trivial instance: Unit spaces with Dirac measures.
  - Meaningful instance: $X_\ell=\mathrm{Fin}\,\ell\to\mathbb R$ with Gaussian product measures, $Z_\ell=\mathbb R$, $\mathrm{split}=(\text{init},\text{last})$.
- **Junk values:** none. The maps are genuine pushforwards of AE-measurable functions, not the junk value 0.
- **Hypotheses:** none unusual. $\nu_\ell$ need not be finite.

**Standard fact.** This is the MLMC telescoping identity with nested (shared) inputs: the coarse functional evaluated on the coarse part of the fine input has the same law as at level $\ell$.

## 8. `nested_vector_inputs_mlmc`

**Rendering.**
Setting: $E$ is a measurable space and $\eta_i$ ($i\in\mathbb N$) are probability measures on it. $K:\mathbb N\to\mathbb N$ satisfies $K_\ell\le K_{\ell+1}$. Write $\Pi_\ell=\bigotimes_{i<K_\ell}\eta_i$ on $E^{K_\ell}$, where coordinate $i$ has law $\eta_i$. The functions satisfy $P_\ell\in L^1(\Pi_\ell)$, and "restrict" means keeping the first $K_\ell$ coordinates via `Fin.castLE`.

Conclusion: (a), (b) and (c) as in §7, with $\Pi_{\ell+1}$ and coordinate restriction in place of $\nu_{\ell+1}$ and $\mathrm{fst}\circ\mathrm{split}$.

**Assessment.** True. The restriction $E^{K_{\ell+1}}\to E^{K_\ell}$ pushes $\Pi_{\ell+1}$ to $\Pi_\ell$: it is the marginal of a product of probability measures, and coordinate $\mathrm{castLE}\,i$ has law $\eta_{i}$. The rest is as in §7.

- **Vacuity:** not vacuous: $E=\mathbb R$, $\eta_i=N(0,1)$, $K_\ell=2^\ell$, $P_\ell$ bounded and measurable.
- **Junk values:** none.
- **Hypotheses:** none unusual.

**Standard fact.** This is the same telescoping identity as §7 for i.i.d.-type vector inputs (e.g. a growing number of random-field coefficients or quasi-MC dimensions).

## 9. `nested_mc_cost_upper`

**Rendering.**
Setting:
- $(\Omega,\mu)$ is a probability space.
- $\omega_n:\Omega\to\Omega_0$ are mutually independent, each with law $\nu$.
- For every $M\in\mathbb N$ with $M>0$: $P_M$ is measurable, $P_M\in L^2(\nu)$, $|\mathbb E_\nu P_M-EP|\le c/M$, and $\operatorname{Var}_\nu P_M\le v$.

Conclusion: for every real $\varepsilon\in(0,1]$ there exist $N,M\in\mathbb N$ with:
- $N=\max(1,\lceil 2v/\varepsilon^2\rceil)$ and $M=\max(1,\lceil 2c/\varepsilon\rceil)$, so both are fully determined;
- $N,M>0$;
- $\bigl(N^{-1}\sum_{n<N}P_M(\omega_n)-EP\bigr)^2$ is integrable, and its integral (the mean-squared error, MSE) is $\le\varepsilon^2$;
- $N\cdot M\le(2v+1)(2c+1)\,\varepsilon^{-3}$, with a real power.

**Assessment.** True.
- At $M=1$ the hypotheses force $c\ge0$ and $v\ge0$.
- $\mathrm{MSE}=\operatorname{Var}P_M/N+\mathrm{bias}^2\le v/N+c^2/M^2\le\varepsilon^2/2+\varepsilon^2/4$. Independence comes from `iIndepFun` composed with the measurable $P_M$.
- Cost: $N\le 2v/\varepsilon^2+1\le(2v+1)/\varepsilon^2$ and $M\le(2c+1)/\varepsilon$, both using $\varepsilon\le1$.
- Random test of the arithmetic: 200k cases, no violation, maximum $\mathrm{MSE}/\varepsilon^2=0.75$ (`nested_ou_check.out`).

- **Vacuity:** not vacuous: $\Omega=\mathbb R^{\mathbb N}$ with i.i.d. $N(0,1)$, $\omega_n$ the coordinates, $P_M(y)=y+1/M$, $EP=0$, $c=v=1$.
- **Junk values:** none. $\varepsilon>0$ for the real power, and the ceilings are of nonnegative reals.
- **Hypotheses:** $\varepsilon\le1$ is genuinely needed. With $v=c=0$ and $\varepsilon=10$, $NM=1>10^{-3}$.
- **Modelling:** the cost model is $N\cdot M$, the "inner samples" are abstract, and $N,M$ are fixed by explicit formulas.

**Standard fact.** This is the classical $O(\varepsilon^{-3})$ cost of nested Monte Carlo when the inner bias is $O(1/M)$.

## 10. `nested_mc_cost_lower`

**Rendering.**
Setting: the same i.i.d. setting as §9 with a single measurable $P\in L^2(\nu)$, and reals $c\ge0$, $v$, $\varepsilon>0$, $N,M\in\mathbb N_{>0}$.

Hypotheses:
- $c/M\le|\mathbb E_\nu P-EP|$;
- $v\le\operatorname{Var}_\nu P$;
- $\mathbb E\bigl(N^{-1}\sum_{n<N}P(\omega_n)-EP\bigr)^2\le\varepsilon^2$.

Conclusion: $c\,v\,\varepsilon^{-3}\le N\cdot M$.

**Assessment.** True.
- The MSE equals $\operatorname{Var}P/N+\mathrm{bias}^2$.
- From this, $\mathrm{bias}\le\varepsilon$, so $M\ge c/\varepsilon$; and $\operatorname{Var}P/N\le\varepsilon^2$, so $N\ge v/\varepsilon^2$ when $v>0$. Multiplying gives the bound.
- If $v\le0$, the left side is $\le0$ because $c\ge0$.
- Random test: 200k cases, no violation.

- **Vacuity:** not vacuous: $P(y)=y+1$ with $y\sim N(0,1)$, $EP=0$, $c=M=N=v=1$, $\varepsilon=2$ (MSE $2\le4$).
- **Junk values:** none. The MSE integrand is integrable, so the hypothesis is not junk-satisfied.
- **Hypotheses:**
  - $c\ge0$ is needed.
  - The bias hypothesis is a lower bound on the bias for the given $M$. This is the usual "bias is at least $c/M$" assumption for a lower bound.

**Standard fact.** This is the matching $\Omega(\varepsilon^{-3})$ lower bound for nested Monte Carlo.

## 11. `ouEM_invariant`

**Rendering.**
Hypotheses: $\kappa>0$, $h>0$, $\kappa h<2$, and $\sigma\in\mathbb R$ arbitrary. Let $s^2=\sigma^2/(\kappa(2-\kappa h))$; it is $\ge0$, so `toNNReal` is the identity here.

Conclusion:
- (a) If $X\sim N(0,s^2)$ and $Z\sim N(0,1)$ are independent, then $(1-\kappa h)X+\sigma\sqrt h\,Z\sim N(0,s^2)$.
- (b) Every probability measure $\pi$ on $\mathbb R$ with the same invariance property equals $N(0,s^2)$.

**Assessment.** True.
- (a): with $a=1-\kappa h$, $a^2s^2+\sigma^2h=s^2$ (verified with sympy). The case $\sigma=0$ gives the Dirac measure, which Mathlib treats as `gaussianReal 0 0`.
- (b): $|a|<1$. The characteristic function satisfies $\varphi(t)=\varphi(a t)e^{-\sigma^2ht^2/2}$. Iterating and using continuity of $\varphi$ at 0 gives $\varphi(t)=e^{-s^2t^2/2}$. This also covers $a=0$.

- **Vacuity:** not vacuous: $\kappa=1$, $h=\tfrac12$, $\sigma=1$.
- **Junk values:** none.
- **Hypotheses:** none unusual. $\kappa h<2$ is exactly the condition for $|1-\kappa h|<1$ given $\kappa,h>0$.

**Standard fact.** The Euler–Maruyama discretisation of the Ornstein–Uhlenbeck process $dX=-\kappa X\,dt+\sigma\,dW$ has the unique invariant law $N\bigl(0,\sigma^2/(\kappa(2-\kappa h))\bigr)$.

## 12. `tendsto_ouEM_invariant`

**Rendering.**
Hypothesis: $\kappa>0$. Conclusion: as $h\to0^+$, $N\bigl(0,(\sigma^2/(\kappa(2-\kappa h)))^+\bigr)\to N(0,\sigma^2/(2\kappa))$ in the weak topology of `ProbabilityMeasure ℝ`.

**Assessment.** True.
- For $h<2/\kappa$ the variance is continuous and tends to $\sigma^2/(2\kappa)$ (sympy limit).
- Centred Gaussians with converging variances converge weakly (characteristic functions, or an explicit coupling $\sqrt{v}Z$).
- For $h\ge2/\kappa$, division by zero and `toNNReal` clipping occur, but they are irrelevant to the one-sided limit at $0$.

- **Vacuity:** not vacuous.
- **Junk values:** none affect the statement.

**Standard fact.** As the step size $h\to0$, the EM invariant law converges to the true Ornstein–Uhlenbeck stationary law $N(0,\sigma^2/2\kappa)$.

## 13. `tendstoInDistribution_normCDFInv_midpoint`

**Rendering.**
Setting: probability spaces $(\Omega,P)$ and $(\Omega',P')$. Each $I_n$ is uniform on $\{0,\dots,n\}$ under $P$ (as `HasLaw`, so AE-measurable). $G\sim N(0,1)$ under $P'$.

Conclusion:
- (a) $(k+\tfrac12)/(n+1)\in(0,1)$ for all $k\le n$.
- (b) $(n+\tfrac12)/n>1$ for all $n>0$.
- (c) $\Phi^{-1}\bigl((I_n+\tfrac12)/(n+1)\bigr)\to G$ in distribution, where `normCDFInv` is $\Phi^{-1}$ (via `invFun`) on $(0,1)$ and $0$ elsewhere.

**Assessment.** True.
- (a) and (b) are elementary.
- For (c), the midpoints are in $(0,1)$, so the junk branch is never used.
- $P\bigl(\Phi^{-1}(u_{I_n})\le t\bigr)=\#\{k:(k+\tfrac12)/(n+1)\le\Phi(t)\}/(n+1)\to\Phi(t)$. Numerically the Kolmogorov distance is exactly $1/(2(n+1))$ (`midpoint_check.out`).
- AE-measurability of the composites holds because $\mathbb N$ is discrete.

- **Vacuity:** not vacuous: $\Omega=[0,1]$ with Lebesgue measure, $I_n=\min(n,\lfloor(n+1)u\rfloor)$, and $G=\mathrm{id}$ on $(\mathbb R,N(0,1))$.
- **Junk values:** none. Conjunct (a) explicitly shows that the junk value of `normCDFInv` is avoided.
- **Remark:** conjunct (b) is a remark that the alternative normalisation $(k+\tfrac12)/n$ would leave $(0,1)$ at $k=n$, where `normCDFInv` would return the junk value 0.

**Standard fact.** Midpoint-rule quantile sampling converges in law to $N(0,1)$ by the continuous mapping theorem / quantile transform.

## 14. `gbm_em_identity_variance_two_sided`

**Rendering.**
Setting: $r,\sigma,s_0\in\mathbb R$, $T\ge0$, $\ell\in\mathbb N$ with $|r|T\le 2^\ell$.

The scheme: `gbmEM` at level $\ell$ is the Euler–Maruyama approximation of geometric Brownian motion (GBM) at time $T$. It uses $m=2^\ell$ steps of size $h=T/m$, with $S_{i+1}=S_i(1+rh+\sigma\sqrt h\,z_i)$ and $S_0=s_0$. The coarse path uses `pairAvg z`, where $z'_k=(z_{2k}+z_{2k+1})/\sqrt2$; this is the Brownian-increment coupling. The $z_i$ are i.i.d. $N(0,1)$ (`stdNormalSeq`). Write $D_\ell=S^{(\ell+1)}_T(z)-S^{(\ell)}_T(\mathrm{pairAvg}\,z)$.

Conclusion:
- (i) $D_\ell\in L^2$.
- (ii) $s_0^2\sigma^4T^2e^{-4|r|T}/4\cdot2^{-\ell}\le\operatorname{Var}D_\ell$.
- (iii) $\operatorname{Var}D_\ell\le 6\,C\,T\,2^{-(\ell+1)}$, where $C=s_0^2e^{(2|r|+\sigma^2)T}(|r|+\sigma^2)(5(|r|+\sigma^2)T+4)$.

**Assessment.** True.

Exact formula. Write $a=rT/(2m)$ and $b^2=\sigma^2T/(2m)$. Per coarse step, $F=(1+a+bx)(1+a+by)$ and $C_k=1+2a+b(x+y)$, which gives

$\operatorname{Var}D/s_0^2=((1+a)^2+b^2)^{2m}-2((1+a)^2(1+2a)+2(1+a)b^2)^m+((1+2a)^2+2b^2)^m-((1+a)^{2m}-(1+2a)^m)^2.$

I verified the moments symbolically and checked $D$ against the literal `emPath` recursion (`gbm_check.out`).

Lower bound (proof sketch). Project onto the orthonormal family $\psi_k=z_{2k}z_{2k+1}$. We have $\mathbb E[D\psi_k]=s_0b^2(1+a)^{2(m-1)}$ and $\mathbb E[C\psi_k]=0$. Hence $\operatorname{Var}D\ge s_0^2\sigma^4T^2(1+a)^{4m-4}/(4m)$. With $|a|\le\tfrac12$, $(1-|a|)^{4m}\ge e^{-2.78|r|T}\ge e^{-4|r|T}$.

Upper bound. It follows from a strong-error bound $\mathbb E|S^{EM}_h-S_T|^2\le C h$ and $(x+y)^2\le2x^2+2y^2$: $2CT/2^{\ell+1}+2CT/2^{\ell}=6CT/2^{\ell+1}$.

Numerics, over a 4464-point grid and 40k random cases including $|r|T=2^\ell$ exactly (`gbm_check.out`, `gbm_random_scan.out`):
- $\min \mathrm{Var}/\mathrm{lower}=1.0$, attained at $r=0,\ell=0$, where $\operatorname{Var}=\sigma^4T^2/4$ exactly.
- $\max \mathrm{Var}/\mathrm{upper}\approx0.016$.

- **Vacuity:** not vacuous: $r=0$, $\sigma=s_0=T=1$, $\ell=0$ gives $\operatorname{Var}=\tfrac14$ = the lower bound, and upper bound $=27e\approx73$.
- **Junk values:** none. $T\ge0$ keeps $\sqrt{T/2^\ell}$ genuine, and the variance is of an $L^2$ variable.
- **Hypotheses:** $|r|T\le2^\ell$ (coarse step $|r|h_c\le1$) applies to both bounds. It appears not to be necessary for either: numerically both still hold beyond it (`gbm_outside_hyp.out`, `gbm_a_minus1.out`). The theorem is therefore slightly weaker than possible, but not defective.

**Standard fact.** For Euler–Maruyama on GBM with payoff $S_T$, the MLMC level variance satisfies $V_\ell\asymp h_\ell$ ($\beta=1$, strong order ½; Giles 2008).

## 15. `gbm_em_identity_variance_cost`

**Rendering.**
Hypotheses: $T>0$, $s_0\ne0$, $\sigma\ne0$, $r$ arbitrary.

Conclusion:
- (i) $D_\ell\in L^2$ for all $\ell$.
- (ii) There exist reals $c>0$ and $C$ with $c\le2^{\ell+1}\operatorname{Var}D_\ell\le C$ for all $\ell$.
- (iii) $2^{\ell+1}\operatorname{Var}D_\ell\not\to0$.

**Assessment.** True.
- For the finitely many $\ell$ with $|r|T>2^\ell$:
  - $\operatorname{Var}D_\ell>0$, because $D_\ell$ is a nonconstant polynomial in Gaussians: its multilinear monomial $\prod_{i<2m}z_i$ has coefficient $s_0b^{2m}\ne0$.
  - $\operatorname{Var}D_\ell$ is finite.
- For the remaining $\ell$, §14 gives $\tfrac12 s_0^2\sigma^4T^2e^{-4|r|T}\le2^{\ell+1}\operatorname{Var}D_\ell\le 6CT$.
- Taking the minimum and maximum gives (ii), and (iii) follows from (ii).
- Numerical sequences in `gbm_check.out` converge to positive limits, e.g. $\approx\sigma^4T^2e^{(2r+\sigma^2)T}/2$.

- **Vacuity:** not vacuous: $r=0$, $\sigma=s_0=T=1$.
- **Junk values:** none.
- **Hypotheses:** $s_0\ne0$, $\sigma\ne0$ and $T>0$ are all needed; otherwise $\operatorname{Var}D_\ell\equiv0$.

**Standard fact.** For Euler–Maruyama on GBM, the level variance has exact rate $\beta=1$: $V_\ell=\Theta(2^{-\ell})$, and it is not $o(h_\ell)$.
