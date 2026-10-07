# Blind read-back report: R5 (confidence intervals with estimated variance)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round14/packet_R5_ci_estimated.lean` |
| declarations audited | 15 theorems (+ 1 definition `mlmcVarEst`, + the appended `levelDiff`, `mlmcEstimator`, `levelEstimator`, `empVar`, `empMean`) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round14/work_R5/` (`empvar_L1_exact.py/.out`, `coverage_sim.py/.out`, `scratch_packet.lean/.out`, `nonvacuity.lean/.out`) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `tendsto_measureReal_abs_le_mul_of_rel` | theorem (abstract Slutsky) | true | no | no |
| 2 | `integral_abs_empVar_sub_le` | theorem | true (constant is sharp) | no | no |
| 3 | `integral_abs_empVar_sub_le_sqrt` | theorem | true | no | no |
| 4 | `integral_abs_mlmcVarEst_sub_le` | theorem | true | no | no |
| 5 | `tendsto_measureReal_mlmcVarEst_rel` | theorem | true | no | no |
| 6 | `tendstoInMeasure_mlmcVarEst_div` | theorem | true | no | no |
| 7 | `tendsto_measureReal_mlmcVarEst_rel_fixed` | theorem | true | no | no |
| 8 | `tendstoInMeasure_sqrt_mlmcVarEst_div_fixed` | theorem | true | no | no |
| 9 | `tendstoInDistribution_mlmcEstimator_fixed` | theorem | true | no | no |
| 10 | `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd_fixed` | theorem | true | no | no |
| 11 | `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd` | theorem | true | no | no |
| 12 | `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd_of_bias` | theorem | true | no | no (see note on $\int P$) |
| 13 | `eventually_lt_measureReal_abs_mlmcEstimator_sub_le_estSd_add` | theorem | true | no | no (trivial for $z<0$, by design) |
| 14 | `eventually_measureReal_test_and_tol_lt_abs_lt` | theorem | true | no | no (trivial for $z<0$) |
| 15 | `eventually_lt_measureReal_test_and_abs_sub_le_tol` | theorem | true | no | no (trivial for $z\le 0$) |

## Main points for a human auditor

1. **All 15 statements are true, none is vacuous, and none depends on a junk value.** The scratch copy
   (proofs `sorry`) elaborates with `-DautoImplicit=false`; the sampling hypotheses `hω`, `hind` are
   satisfiable (checked in Lean with `Measure.infinitePi` and coordinate maps, `nonvacuity.lean`).
2. **The L1 constant in #2 is exactly right and sharp.** $\mathbb E|s^2_N-\sigma^2|\le(\sqrt{(K-1)/N}+1/N)\sigma^2$
   follows from $s^2-\sigma^2=\frac1N\sum(Y_n^2-\sigma^2)-\bar Y^2$ ($Y=X-m$), giving
   $\le\sqrt{(\mu_4-\sigma^4)/N}+\sigma^2/N$. Exact rational enumeration (two- and three-point laws,
   $N\le 12$, 3457 random (law, $N$) cases) never exceeds it, and **equality holds for every
   symmetric two-point law at every $N$** (with $K=\kappa=1$). The `+1/N` (bias of the
   divide-by-$N$ variance) cannot be dropped. #3's $\sqrt{2K/N}$ follows because $K\ge1$ whenever
   $\sigma^2>0$; worst ratio found $1/\sqrt2$.
3. **`empVar` is the biased (divide-by-$N$) sample variance**; at $N=0$ it is $0/0=0$ and the RHS of
   #2/#3 is also $0$ (because $x/0=0$, $\sqrt0=0$), so `hN : 0 < N` (and `0 < n₀` in #4) is necessary,
   not decorative; with $N=0$ the claim would be false ($\sigma^2\le0$).
4. **`h4` (integrability of the 4th central moment) guards against a junk value.** Without it, the
   Bochner integral in `hK` would be $0$ for $g\in L^2\setminus L^4$, `hK` would hold for every
   $K\ge0$, and #2 (e.g. with $K=1$: $\mathbb E|s^2-\sigma^2|\le\sigma^2/N$) would be false. It is present
   in every statement that uses `hK`.
5. **No division by a random quantity in any event.** The CI events are
   $|Y-c|\le z\sqrt{\hat\sigma^2}$; the only divisions are by the deterministic $\sigma_k^2$ / $\sigma_k$ (#6, #8,
   #9, #12's `hbias`), which are protected by `hσ` (eventually $\sigma_k^2>0$) or by `hV` + $N\to\infty$.
   Without them #6/#8/#9/#10 would be false (ratio $=x/0=0$, not $1$).
6. **`hz : 0 ≤ z` is necessary in #1, #10, #11, #12** (for $z<0$ the probability tends to $0$ but the
   claimed limit $2\Phi(z)-1<0$). It is correctly absent from #13–#15, which are trivially true for
   $z<0$ (and for $z=0$ in #15) because the bound is then negative, resp. $>1$.
7. **#15 needs both `0 ≤ θ'` and `θ' < θ`.** Counterexample without `0 ≤ θ'`: $\theta=1$, $\theta'<0$, zero
   bias, $TOL_k=z\sigma_k/\theta'<0$; then $\{|Y-\mathbb EP|\le TOL_k\}=\varnothing$ and the probability is
   $0<2\Phi(z)-1-\eta$. With $\theta'=\theta$ the first event becomes $\{\hat\sigma\le\sigma\}$; simulation
   (`coverage_sim.out`, Example C) gives probability $0.80\to0.64\to0.57$, far below $0.95-\eta$; with
   $\theta'=0.4<\theta=0.5$ it gives $0.91\to0.94\to0.98$.
8. **$\int P\,d\nu$ in #12–#15 has no integrability hypothesis on $P$.** Not junk-dependent: each
   statement holds for an arbitrary real constant $c$ in place of $\int P$ (the proofs only use the
   bias hypothesis). But if $P\notin L^1$ the "target" is silently $0$, so the CI-for-$\mathbb E[P]$ reading
   presupposes integrability.
9. **Growing number of levels (#5, #6, #11–#15)**: the hypotheses (one kurtosis constant $K$ for all
   levels, $\min_{\ell\le L_k}N_{k,\ell}\to\infty$ via `hNtop`, which has the correct quantifier order
   $\forall n_0\,\forall^\infty k\,\forall\ell\le L_k$) suffice: Lyapunov ratio
   $\sum\mathbb E\xi^4/\sigma^4\le K/\min_\ell N_{k,\ell}\to0$. Fixed-$L$ versions (#7–#10) need only $L^2$.
10. **#1 has no measurability hypotheses**; still true since `μ` on arbitrary sets is the outer measure
    (monotone, subadditive), which is all the Slutsky sandwich needs.
11. **Coverage check** (`coverage_sim.out`): fixed $L=2$ (Taylor partial sums of $e^w$), coverage of
    $Y\pm1.96\hat\sigma$ is $0.741, 0.881, 0.923, 0.946, 0.947, 0.953$ as $N$ grows (oracle-$\sigma$
    coverage $\approx0.95$ throughout); growing $L_k=k$ (dyadic truncation, $K=1$): $\approx0.95$ for
    $\mathbb E P_{L_k}$ and $0.18\to0.72\to0.90\to0.94\to0.948\to0.951$ for $\mathbb EP$ as bias$/\sigma\to0$.

## Notation used below

$D_\ell=$ `levelDiff Pl ℓ` ($D_0=P_0$, $D_\ell=P_\ell-P_{\ell-1}$); $m_\ell=\int D_\ell\,d\nu$,
$V_\ell=\mathrm{Var}_\nu D_\ell$ (Mathlib `variance`, population variance), $\mu_{4,\ell}=\int(D_\ell-m_\ell)^4d\nu$.
Samples $X_{\ell,n}=D_\ell(\omega(\ell,n)(x))$. $\mathrm{empVar}(x,N)=\frac1N\sum_{n<N}(x_n-\bar x_N)^2$ ($=0$ if
$N=0$). For level counts $N_\ell$ (ℕ, cast to ℝ, $1/0=0$):
$Y=\sum_{\ell\le L}\frac1{N_\ell}\sum_{n<N_\ell}X_{\ell,n}$ (`mlmcEstimator`),
$\hat\sigma^2=\sum_{\ell\le L}\mathrm{empVar}_\ell(N_\ell)/N_\ell$ (`mlmcVarEst`), $\sigma^2=\sum_{\ell\le L}V_\ell/N_\ell$.
"$\mathbb P$" is `μ.real` (the real-valued outer measure). $\Phi=$ `cdf (gaussianReal 0 1)`.
Standing hypotheses of #2–#15: `hω`: every $\omega(p):\Omega\to\Omega_0$ is measurable with law $\nu$ under $\mu$
($\mu$ a probability measure, hence so is $\nu$); `hind`: the family $(\omega(p))_{p\in\mathbb N\times\mathbb N}$ is
mutually independent. So all samples are i.i.d. $\sim\nu$ across levels and indices.

---

## 1. `tendsto_measureReal_abs_le_mul_of_rel`

**Rendering.** $\mu$ probability measure on $\Omega$; $S_k,\hat\sigma_k:\Omega\to\mathbb R$, $\sigma_k\in\mathbb R$
(no measurability assumed). If (hS) for every $z'\ge0$, $\mathbb P(|S_k|\le z'\sigma_k)\to2\Phi(z')-1$, and
(hσh) for every $\varepsilon>0$, $\mathbb P(\varepsilon\sigma_k<|\hat\sigma_k-\sigma_k|)\to0$, then for every $z\ge0$,
$\mathbb P(|S_k|\le z\hat\sigma_k)\to2\Phi(z)-1$.

**Assessment.** True (Slutsky-type sandwich). Let $C_\varepsilon=\{\varepsilon\sigma_k<|\hat\sigma_k-\sigma_k|\}$. Off
$C_\varepsilon$, $\varepsilon\sigma_k\ge0$ and $(1-\varepsilon)\sigma_k\le\hat\sigma_k\le(1+\varepsilon)\sigma_k$, so (with $z\ge0$)
$\{|S|\le z\hat\sigma\}\subseteq\{|S|\le z(1+\varepsilon)\sigma\}\cup C_\varepsilon$ and
$\{|S|\le z(1-\varepsilon)\sigma\}\subseteq\{|S|\le z\hat\sigma\}\cup C_\varepsilon$ ($0<\varepsilon<1$). Monotonicity and
subadditivity of the outer measure give $\limsup\le2\Phi(z(1+\varepsilon))-1$,
$\liminf\ge2\Phi(z(1-\varepsilon))-1$; continuity of $\Phi$ finishes. Negative or zero $\sigma_k$ cause no
problem (if $\sigma_k<0$, $C_\varepsilon=\Omega$, which hσh forbids eventually). Non-vacuous: $\Omega=\mathbb R$,
$\mu=N(0,1)$, $S_k=\mathrm{id}$, $\sigma_k=\hat\sigma_k=1$. No junk. `hz` is needed: for $z<0$ and
$\hat\sigma\approx\sigma>0$ the probability $\to0\ne2\Phi(z)-1<0$. Hypothesis hS "for all $z'\ge0$" is what
a CLT plus continuity of the Gaussian cdf delivers. Standard: Slutsky's lemma for studentisation.

## 2. `integral_abs_empVar_sub_le`

**Rendering.** Under `hω`, `hind`; $g:\Omega_0\to\mathbb R$ with $g\in L^2(\nu)$, $(g-\mathbb Eg)^4\in L^1(\nu)$, and
$\mu_4(g)\le K\,\mathrm{Var}(g)^2$ ($K\in\mathbb R$). For every $i\in\mathbb N$ and $N\ge1$:
$$\int\Big|\mathrm{empVar}\big((g(\omega(i,n)))_n,N\big)-\mathrm{Var}(g)\Big|\,d\mu\le\Big(\sqrt{\tfrac{K-1}{N}}+\tfrac1N\Big)\mathrm{Var}(g).$$
(`√` is `Real.sqrt`, $=0$ on negatives; $N$ cast to ℝ.)

**Assessment.** True. With $Y_n=g(\omega(i,n))-\mathbb Eg$ i.i.d., $s^2-\sigma^2=A-B$ where
$A=\frac1N\sum(Y_n^2-\sigma^2)$, $B=\bar Y^2\ge0$; $\mathbb E|A|\le\sqrt{\mathrm{Var}A}=\sqrt{(\mu_4-\sigma^4)/N}\le\sqrt{(K-1)/N}\,\sigma^2$
and $\mathbb EB=\sigma^2/N$. If $\sigma^2=0$, $g$ is a.e. constant, LHS $=0=$ RHS (any $K$). Exact
enumeration (`empvar_L1_exact.out`): also verified $\mathbb Es^2=\frac{N-1}N\sigma^2$ and
$\mathrm{Var}(s^2)=[(N-1)^2\mu_4-(N-1)(N-3)\sigma^4]/N^3$ exactly; the bound is never exceeded (max
ratio $1.0$) and is **attained with equality** for symmetric two-point laws ($\kappa=1$) at every
$N=1..12$, so the constant is sharp; dropping $+1/N$ would be false. Non-vacuous: infinite product
model (`nonvacuity.lean`), $g=\pm1$, $K=1$. Junk: `hN` is necessary (at $N=0$: LHS $=\sigma^2$, RHS
$=(\sqrt{(K-1)/0}+1/0)\sigma^2=0$); `h4` is necessary (else the Bochner integral in `hK` is $0$
and `hK` holds for every $K\ge0$, making the bound false for $g\in L^2\setminus L^4$); both are present.
`hg` (L²) is needed for `variance` to be meaningful. Standard: $L^1$ (via $L^2$) error bound for the
sample variance in terms of kurtosis.

## 3. `integral_abs_empVar_sub_le_sqrt`

**Rendering.** Same hypotheses as #2; conclusion
$\int|\mathrm{empVar}-\mathrm{Var}(g)|\,d\mu\le\sqrt{2K/N}\,\mathrm{Var}(g)$.

**Assessment.** True: if $\sigma^2>0$ then $K\ge\mu_4/\sigma^4\ge1$, and
$(\sqrt{(K-1)/N}+1/N)^2\le2K/N\iff2\sqrt{K-1}/\sqrt N+1/N\le K+1$, true since
$2\sqrt{K-1}\le K$ and $N\ge1$. If $\sigma^2=0$ both sides are $0$. Enumeration: max ratio
LHS/RHS $=0.7071$. Non-vacuous as #2; `hN`, `h4` necessary as in #2. Weaker but simpler form of #2.

## Definition `mlmcVarEst`

$\hat\sigma^2(x)=\sum_{\ell\le L}\mathrm{empVar}\big((D_\ell(\omega(\ell,n)x))_n,N_\ell\big)/N_\ell$ — the plug-in
estimate of $\mathrm{Var}(Y)=\sum V_\ell/N_\ell$ with the **biased** (divide-by-$N$) level variances; a level
with $N_\ell\le1$ contributes $0$. Always $\ge0$, so `√` is never applied to a negative number.
Uses the same samples as `mlmcEstimator` (level $\ell$ uses $\omega(\ell,n)$, $n<N_\ell$).

## 4. `integral_abs_mlmcVarEst_sub_le`

**Rendering.** Under `hω`, `hind`, fixed $L$; for all $\ell\le L$: $D_\ell\in L^2$, $(D_\ell-m_\ell)^4\in L^1$,
$\mu_{4,\ell}\le KV_\ell^2$; $N:\mathbb N\to\mathbb N$ with $N_\ell\ge n_0\ge1$ for $\ell\le L$. Then
$\int|\hat\sigma^2-\sigma^2|\,d\mu\le\sqrt{2K/n_0}\,\sigma^2$.

**Assessment.** True: triangle inequality and #3 per level,
$\sum_\ell\frac{1}{N_\ell}\sqrt{2K/N_\ell}V_\ell\le\sqrt{2K/n_0}\sum V_\ell/N_\ell$ (all terms integrable as
$D_\ell\in L^2$). Non-vacuous (Example B of `coverage_sim.py`: $K=1$). Junk: `0 < n₀` needed
(else RHS $=0$); `h4` as in #2. Standard.

## 5. `tendsto_measureReal_mlmcVarEst_rel`

**Rendering.** Growing levels $L:\mathbb N\to\mathbb N$, $N_{k,\ell}$; for all $k$ and $\ell\le L_k$: $D_\ell\in L^2$,
4th central moment integrable, $\mu_{4,\ell}\le KV_\ell^2$ (one $K$); `hNtop`: $\forall n_0\,\forall^\infty k\,
\forall\ell\le L_k:\ n_0\le N_{k,\ell}$ (i.e. $\min_{\ell\le L_k}N_{k,\ell}\to\infty$). For every $\varepsilon>0$:
$\mathbb P(\varepsilon\sigma_k^2<|\hat\sigma_k^2-\sigma_k^2|)\to0$.

**Assessment.** True: Markov plus #4 gives $\le\sqrt{2K/n_0}/\varepsilon$ eventually when $\sigma_k^2>0$; if
$\sigma_k^2=0$ (with $N\ge1$) all $V_\ell=0$, $\hat\sigma^2=0$ a.s., the event is null; so no positivity
hypothesis is needed. Event has no division. Non-vacuous (Example B). No junk. Standard
(relative consistency of the variance estimator under a uniform kurtosis bound).

## 6. `tendstoInMeasure_mlmcVarEst_div`

**Rendering.** Hypotheses of #5 plus `hσ`: eventually $\sigma_k^2>0$. Then $\hat\sigma_k^2/\sigma_k^2\to1$ in
$\mu$-measure (Mathlib `TendstoInMeasure`: $\forall\varepsilon>0$, $\mu\{\varepsilon\le\mathrm{edist}\}\to0$).

**Assessment.** True: for $\sigma_k^2>0$, $\{\varepsilon\le|\hat\sigma^2/\sigma^2-1|\}=\{\varepsilon\sigma^2\le|\hat\sigma^2-\sigma^2|\}$,
Markov + #4. `hσ` is necessary (if $\sigma_k^2=0$ the quotient is $x/0=0$, distance $1$). Division
only by the deterministic $\sigma_k^2$. Non-vacuous; no junk. Standard.

## 7. `tendsto_measureReal_mlmcVarEst_rel_fixed`

**Rendering.** Fixed $L$; $D_\ell\in L^2$ for $\ell\le L$ (no 4th moments); $N_{k,\ell}\to\infty$ for each
$\ell\le L$. For $\varepsilon>0$: $\mathbb P(\varepsilon\sigma_k^2<|\hat\sigma_k^2-\sigma_k^2|)\to0$.

**Assessment.** True: by the WLLN (only $L^1$ of $D_\ell^2$ needed) $s_\ell^2(N)\to V_\ell$ in probability as
$N\to\infty$; levels with $V_\ell=0$ are a.s. exact; $\{\varepsilon\sigma^2<|\hat\sigma^2-\sigma^2|\}\subseteq
\bigcup_{\ell:V_\ell>0}\{\varepsilon V_\ell<|s_\ell^2-V_\ell|\}$ up to null sets, finitely many levels. Non-vacuous
(Example A). No junk. Standard.

## 8. `tendstoInMeasure_sqrt_mlmcVarEst_div_fixed`

**Rendering.** Fixed $L$, $D_\ell\in L^2$, `hV`: some $\ell\le L$ has $V_\ell>0$, $N_{k,\ell}\to\infty$ for each
$\ell\le L$. Then $\sqrt{\hat\sigma_k^2}/\sqrt{\sigma_k^2}\to1$ in measure.

**Assessment.** True: `hV` and $N_{k,\ell}\ge1$ eventually give $\sigma_k^2>0$ eventually; then the ratio is
$\sqrt{\hat\sigma^2/\sigma^2}$ and $|\sqrt r-1|\le|r-1|$, plus #7. `hV` is necessary (else ratio $=0$).
Non-vacuous; no junk. Standard (continuous mapping).

## 9. `tendstoInDistribution_mlmcEstimator_fixed`

**Rendering.** Fixed $L$, $P_\ell\in L^2(\nu)$ for $\ell\le L$, `hV`, $N_{k,\ell}\to\infty$ for $\ell\le L$; $Z$ with law
$N(0,1)$ on $(\Omega',P')$. Then $(Y_k-\int P_L\,d\nu)/\sqrt{\sigma_k^2}\Rightarrow Z$ (Mathlib
`TendstoInDistribution`, which also asserts a.e.-measurability of each $Y_k$).

**Assessment.** True: $\mathbb EY_k=\sum m_\ell=\mathbb EP_L$ (telescoping, all integrable). The standardized sum is
$\sum_\ell w_{k,\ell}Z_{k,\ell}$ with independent $Z_{k,\ell}\Rightarrow N(0,1)$ (classical CLT per level with
$V_\ell>0$), weights $w_{k,\ell}^2=(V_\ell/N_{k,\ell})/\sigma_k^2$ summing to $1$; characteristic functions give
$N(0,1)$ even if the weights oscillate. Measurability follows from $P_\ell\in L^2$ and `hω`. `hV`
necessary (else quotient $=0$). Non-vacuous (Example A). Standard MLMC CLT for fixed $L$.

## 10. `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd_fixed`

**Rendering.** Hypotheses of #9 (without $Z$) and $z\ge0$:
$\mathbb P(|Y_k-\mathbb EP_L|\le z\sqrt{\hat\sigma_k^2})\to2\Phi(z)-1$.

**Assessment.** True: #1 with $S_k=Y_k-\mathbb EP_L$, $\sigma_k$ the true sd, $\hat\sigma_k=\sqrt{\hat\sigma_k^2}$; hS from #9
and continuity of $\Phi$; hσh from #8. No random division. `hz` needed (for $z<0$ the probability
$\to0$); `hV` needed (else $Y=\mathbb EP_L$ a.s. and the probability is $1$). Simulation: coverage
$0.741\to0.953$ for $z=1.96$. Standard asymptotic CI with estimated variance.

## 11. `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd`

**Rendering.** Growing levels: for all $k,\ell\le L_k$: $P_\ell\in L^2$, 4th central moment of $D_\ell$
integrable and $\le KV_\ell^2$; `hNtop`; `hσ` (eventually $\sigma_k^2>0$); $z\ge0$. Then
$\mathbb P(|Y_k-\mathbb EP_{L_k}|\le z\sqrt{\hat\sigma_k^2})\to2\Phi(z)-1$.

**Assessment.** True: Lyapunov CLT for the triangular array $\xi=(X_{\ell,n}-m_\ell)/N_{k,\ell}$:
$\sum\mathbb E\xi^4/\sigma_k^4\le K\sum_\ell V_\ell^2/N_{k,\ell}^3/\sigma_k^4\le K/\min_\ell N_{k,\ell}\to0$; then #1 with
#6 (and $\sqrt{\cdot}$). The uniform $K$ and `hNtop` are exactly what is needed. `hz`, `hσ` necessary.
Simulation (Example B, $L_k=k$): coverage $\approx0.95$ at all $k$. Standard (CLT for MLMC with growing
$L$ under a kurtosis bound, plus Slutsky).

## 12. `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd_of_bias`

**Rendering.** Hypotheses of #11, $P:\Omega_0\to\mathbb R$ (no integrability), `hbias`:
$(\mathbb EP_{L_k}-\int P)/\sqrt{\sigma_k^2}\to0$, $z\ge0$. Then $\mathbb P(|Y_k-\int P|\le z\sqrt{\hat\sigma_k^2})\to2\Phi(z)-1$.

**Assessment.** True by Slutsky (deterministic shift $\to0$ in standardized units) and #1. The proof
works for any constant $c$ in place of $\int P$, so not junk-dependent; but if $P\notin L^1$ then
$\int P=0$ and the statement is a CI for $0$ — interpretive caveat only. Division by the deterministic
$\sigma_k$ is protected by `hσ`. Simulation (Example B, target $1/2$): $0.18,0.72,0.90,0.94,0.948,0.951$
as bias$/\sigma=2.83\to0.086$. `hz` needed. Standard.

## 13. `eventually_lt_measureReal_abs_mlmcEstimator_sub_le_estSd_add`

**Rendering.** Hypotheses of #11, `hb`: eventually $|\mathbb EP_{L_k}-\int P|\le b_k$; any $z\in\mathbb R$, $\eta>0$.
Then eventually $2\Phi(z)-1-\eta<\mathbb P(|Y_k-\int P|\le z\sqrt{\hat\sigma_k^2}+b_k)$. Quantifiers: $\forall z\,\forall\eta>0\,
\forall^\infty k$.

**Assessment.** True: $\{|Y-\mathbb EP_L|\le z\hat\sigma\}\subseteq\{|Y-\int P|\le z\hat\sigma+b_k\}$ when the bias bound
holds; for $z\ge0$ apply #11; for $z<0$ the LHS is negative. No hypothesis on $b_k$ needed (a
negative $b_k$ makes `hb` false). Non-vacuous (Example B with $b_k=2^{-L_k-1}$). Standard
(bias-inflated CI, non-asymptotic in the bias).

## 14. `eventually_measureReal_test_and_tol_lt_abs_lt`

**Rendering.** Hypotheses of #11, $\theta\in\mathbb R$, $TOL:\mathbb N\to\mathbb R$, `hbias`: eventually
$|\mathbb EP_{L_k}-\int P|\le(1-\theta)TOL_k$; any $z$, $\eta>0$. Then eventually
$\mathbb P(z\sqrt{\hat\sigma^2}\le\theta TOL_k\ \wedge\ TOL_k<|Y_k-\int P|)<2(1-\Phi(z))+\eta$.

**Assessment.** True for all $\theta$, $TOL$, $z$: on the event, $|Y-\mathbb EP_L|\ge|Y-\int P|-|{\rm bias}|>
TOL-(1-\theta)TOL=\theta TOL\ge z\hat\sigma$ (sign-free), so the event lies in $\{|Y-\mathbb EP_L|>z\hat\sigma\}$,
whose probability $\to2-2\Phi(z)$ for $z\ge0$ (#11 and complement; the sets are null-measurable). For
$z<0$ the bound exceeds $1$. Non-vacuous. Standard: "test passes but error exceeds TOL" has
asymptotic probability at most $\alpha$.

## 15. `eventually_lt_measureReal_test_and_abs_sub_le_tol`

**Rendering.** Hypotheses of #11, $0\le\theta'<\theta$, `hbias` as in #14, `hstat`: eventually
$z\sqrt{\sigma_k^2}\le\theta'TOL_k$ (true sd), $\eta>0$. Then eventually
$2\Phi(z)-1-\eta<\mathbb P(z\sqrt{\hat\sigma^2}\le\theta TOL_k\ \wedge\ |Y_k-\int P|\le TOL_k)$.

**Assessment.** True. For $z\le0$ trivial. For $z>0$: `hstat`, `hσ`, $\theta'\ge0$ force $\theta'>0$, $TOL_k>0$,
so $\theta TOL_k\ge(\theta/\theta')z\sigma_k$ with $\theta/\theta'>1$: $\mathbb P(z\hat\sigma>\theta TOL)\le
\mathbb P(\hat\sigma>(\theta/\theta')\sigma)\to0$ (#6); and $\{|Y-\mathbb EP_L|\le z\sigma\}\subseteq\{|Y-\int P|\le TOL\}$ since
$z\sigma\le\theta TOL$ and $|{\rm bias}|\le(1-\theta)TOL$; CLT gives $\to2\Phi(z)-1$. Both `0 ≤ θ'` and
`θ' < θ` are necessary: without the former, take $\theta=1$, $\theta'<0$, zero bias,
$TOL_k=z\sigma_k/\theta'<0$ — all other hypotheses hold and the probability is $0$; with $\theta'=\theta$ the
probability tends to about $P(\hat\sigma\le\sigma)$ (simulated $0.80\to0.64\to0.57$ vs. $0.91\to0.98$ for
$\theta'=0.4$, `coverage_sim.out` Example C). Non-vacuous (Example B with $\theta=0.5,\theta'=0.4$,
$TOL_k=z\sigma_k/\theta'$). Standard: asymptotic probability that the stopping test passes and the
tolerance is met.
