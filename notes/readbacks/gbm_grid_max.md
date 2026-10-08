# Blind read-back report: R31 (GBM grid maximum / lookback)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round21/packet_R31_gridmax.lean` |
| declarations audited | 14 in the module (12 theorems + 2 definitions: `gbmGridExact`, `lookbackMinPayoff`); the empty `section Levels` declares nothing; the 18 appended supporting definitions are also rendered |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round21/work_R31/` (`Scratch.lean`/`.out`, `check_moment_const{,2,3}.py`/`.out`, `mc_rates.py`/`.out`) |

I compiled a self-contained copy of the packet (`work_R31/Scratch.lean`) against Mathlib's targeted imports, with the
appended definitions copied verbatim, without `import MlmcLean`, and with `-DautoImplicit=false`. All 12 statements
elaborate, and the only warnings are the expected `sorry` ones. Elaboration facts I confirmed:
- In `gbm_em_grid_max_error`, `h ^ m` is a natural-number power and `(·) ^ ((m:ℝ)⁻¹)` is `Real.rpow`.
- `N * h`, `2 * N * h` and `(N + 1) * …` are real (`↑N`).
- In the payoffs, `2 ^ ℓ` is a natural number, and in the step sizes `T / 2 ^ ℓ` is real.
- `h ^ (1 - δ)`, `(T/2^ℓ)^((1-δ)/2)` and `ε ^ (-2 - η)` are `rpow`.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `gbmGridExact` | def | n/a (exact GBM on a grid; correct) | n/a | n/a |
| 2 | `gbm_em_grid_max_error` | theorem | true (constant checked numerically, with large margin) | no | no |
| 3 | `gbm_em_grid_max_error_sharp` | theorem | true | no | no |
| 4 | `gbm_grid_monitoring_gap_rate` | theorem | true (weaker than the sharp $O(h)$) | no | no (when $h=0$ and $\delta>1$ the convention $0^{-x}=0$ gives a right side of $0$, but the left side is also $0$) |
| 5 | `lookbackMinPayoff` | def | n/a | n/a | n/a |
| 6 | `gbm_em_gridLookback_variance_rate` | theorem | true | no | no |
| 7 | `gbm_em_gridLookbackMin_variance_rate` | theorem | true | no | no |
| 8 | `gbm_em_gridFloatLookback_variance_rate` | theorem | true | no | no |
| 9 | `gbm_em_gridLookback_mean_converges` | theorem | true | no | no |
| 10 | `gbm_em_gridLookbackMin_mean_converges` | theorem | true | no | no |
| 11 | `gbm_em_gridFloatLookback_mean_converges` | theorem | true | no | no |
| 12 | `gbm_em_gridLookback_theorem1` | theorem | true | no | no |
| 13 | `gbm_em_gridLookbackMin_theorem1` | theorem | true | no | no |
| 14 | `gbm_em_gridFloatLookback_theorem1` | theorem | true | no | no |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.** Every hypothesis set has a concrete instance, for example
   $r=0.05$, $\sigma=0.2$, $s_0=1$, $T=1$, $g=\mathrm{id}$ ($K=1$), $\delta=\tfrac12$, $h=0.1$, $N=10$, $m=1$. All
   payoffs are $L^2$, so the integrals and `variance` take their genuine values: the "non-integrable gives 0" and
   "$\mathrm{evariance}=\infty$ gives 0" conventions are never triggered.
2. **`gbm_em_grid_max_error` depends on an explicit, complicated constant** $C_m=$ `gbmEMMomentConst m r σ T s₀`. The
   statement follows from $\mathbb E|X_{nh}-Y_n|^{2m}\le C_m h^m$ for $nh\le T$, together with
   $\mathbb E\max e^2\le(\sum_n\mathbb E e_n^{2m})^{1/m}$.
   - **Numerical check.** I computed $\mathbb E|X_{nh}-Y_n|^{2m}$ exactly in closed form at 120–200 digits, over
     several hundred cases. These covered $m\in\{1,2,3,4,5\}$, $\sigma=0$, $|r|h$ up to 10, $\sigma^2T$ up to 8, and
     $h$ not dividing $T$. The largest ratio $\mathbb E|e_n|^{2m}/(C_mh^m)$ was $5.5\times10^{-3}$, so the constant
     is valid and very loose.
   - **$C_m\ge 0$.** All weights are non-negative once $T\ge0$, and $T\ge0$ follows from $Nh\le T$ and $h\ge0$. So
     the `rpow` base is non-negative.
   - **Weakness at $m=1$.** For $m=1$ and $N\approx T/h$ the right side is about $C_1(T+h)$, which does not tend to
     $0$. That instance carries little information. The rate $h^{1-1/m}$ only appears for $m\ge2$, and the sharp
     $O(h)$ is the separate theorem `…_sharp`.
3. **The rates are deliberately weaker than the sharp ones, but true.**
   - **Monitoring gap and level variances:** stated as $h^{1-\delta}$, where the truth is $O(h)$. A Monte Carlo run,
     `mc_rates.out`, shows $\mathbb E[\text{gap}^2]/h$ levelling off near $0.06$.
   - **Weak error:** stated as $h^{(1-\delta)/2}$, where the truth is $O(\sqrt h)$.
   - **MLMC cost:** stated as $\varepsilon^{-2-\eta}$ for every $\eta>0$, where Giles' theorem with $\beta=\gamma=1$
     would give $\varepsilon^{-2}(\log\varepsilon)^2$.
   - These look like artefacts of the proof route ($L^p$ union bounds over $\sim1/h$ grid points), not errors.
4. **Variance theorems allow any $\delta>0$, including $\delta\ge1$.** For $\delta\ge 1$ they only assert uniform
   boundedness, or less. The `mean_converges` theorems restrict to $0<\delta<1$. Both are harmless.
5. **Coupling checks.**
   - The coarse level uses `pairAvg`, i.e. increments $\sqrt{2h}\,(z_{2k}+z_{2k+1})/\sqrt2=\sqrt h(z_{2k}+z_{2k+1})$.
     This is the correct Brownian coupling, and `pairAvg z` is again i.i.d. $N(0,1)$, so the telescoping sum has the
     right expectation.
   - `emCoarse` at index $2k$ reduces to `emPath (2h) (pairAvg z) k`.
   - The MLMC target $Y$ is pinned down as the limit of the **exact-GBM** grid lookback means. This is
     $\mathbb E\,g(\sup_{[0,T]}S)$ (or $\inf$, or $S_T-\inf$), i.e. the continuously monitored price, not the
     EM-approximate one.
6. **Lipschitz hypothesis.** `hg : ∀ x y, |g x - g y| ≤ K*|x-y|` places no sign constraint on $K$. It is satisfiable
   only for $K\ge0$, which is standard.

---

## Supporting definitions (rendering)

- `emPath a b h S₀ z`: the Euler–Maruyama recursion $Y_0=S_0$,
  $Y_{i+1}=Y_i+a(Y_i,ih)\,h+b(Y_i,ih)\sqrt h\,z_i$.
- `gbmDrift r = (S,t)↦rS` and `gbmVol σ = (S,t)↦σS`. So for GBM, $Y_{i+1}=Y_i(1+rh+\sigma\sqrt h z_i)$.
- `pairAvg z k` $=(z_{2k}+z_{2k+1})/\sqrt2$.
- `stdNormalSeq`: the law of an i.i.d. $N(0,1)$ sequence on $\mathbb R^{\mathbb N}$ (`Measure.infinitePi`).
- `emCoarsePath a b h S₀ z i`:
  - for even $i$, the coarse EM path with step $2h$ driven by `pairAvg z`, evaluated at $i/2$;
  - for odd $i$, one extra half-step with $z_{i-1}$.

  Only even indices are used here.
- `emFine … ℓ z` $=\Phi_\ell(\text{EM path with step }T/2^\ell\text{ driven by }z)$.
- `emCoarse … ℓ z` $=\Phi_\ell(k\mapsto\text{emCoarsePath}(T/2^{\ell+1})(z)(2k))$, which equals
  $\Phi_\ell(\text{EM path with step }T/2^\ell\text{ driven by pairAvg }z)$.
- `fineCoarseDiff Pf Pc`: level $0$ is $Pf_0$; level $\ell+1$ is $Pf_{\ell+1}-Pc_\ell$.
- `blockMean f ω i N x` $=\frac1N\sum_{n<N} f_i(\omega(i,n)\,x)$. With `ω = fun p x => x p`, level $\ell$ uses the
  i.i.d. sequences $x(\ell,0),\dots,x(\ell,N_\ell-1)$.
- `lookbackPayoff g m S` $=g(\max_{0\le n\le m}S_n)$.
- `floatLookbackPayoff g m S` $=g(S_m-\min_{0\le n\le m}S_n)$.
- `gbmEMMomentConst m r σ t s₀` $=s_0^{2m}\,t\,I_m\,e^{(\rho_m+1)t}$, where:
  - $\rho_m=2m|r-\sigma^2/2|+2m^2\sigma^2+|r|+2m\sigma^2$;
  - $I_m=\sum_{k<2m}w_k\,s_k^{2m-k-1}$;
  - $s_k=(1+2mw_k)^{1/(k+1)}$;
  - $w_0=2m\beta_1\sqrt t$ (from $\tau^{3-a}$ with $a=2$), where $\beta_1=(|r|+2m\sigma^2)^2$;
  - $w_k=\binom{2m}{k+1}E_{k+1}\,t^{(k-1)/2}$ for $k\ge1$;
  - $E_j=2\cdot3^{j-1}\big[(\sigma^2+2(|r-\sigma^2/2|+2m\sigma^2)^2t)^j+(2\sigma^2)^j(2j-1)!!\big]$.

  The natural-number subtractions $3-a$, $k-1$, $2m-(k+1)$ and $2j-1$ are all non-truncating where they are used.
  Every term is $\ge0$ when $t\ge0$.

---

## 1. `gbmGridExact` (def)

**Rendering.** $\texttt{gbmGridExact}(r,\sigma,h,s_0,z,n)=s_0\exp\!\big((r-\tfrac{\sigma^2}2)\,nh+\sigma\sqrt h\sum_{i<n}z_i\big)$.
With $z$ i.i.d. $N(0,1)$, this is the exact GBM solution $S_{t}=s_0e^{(r-\sigma^2/2)t+\sigma W_t}$ at $t=nh$, where
$W_{nh}=\sqrt h\sum_{i<n}z_i$. It uses the same Gaussian increments as `emPath`, so it is the strong-error coupling.
The definition is correct. For $h<0$, $\sqrt h=0$ is a junk value, but every theorem assumes $h\ge0$ or uses
$h=T/2^\ell$ with $T\ge0$.

## 2. `gbm_em_grid_max_error`

**Rendering.** Let $r,\sigma,s_0\in\mathbb R$, $h\ge0$, $T\in\mathbb R$, $N\in\mathbb N$ with $Nh\le T$ (so $T\ge0$),
and $m\in\mathbb N$ with $m\ge1$. Write $X_n=$ `gbmGridExact` and $Y_n=$ the GBM Euler–Maruyama path, both with step
$h$ and driven by the same $z\sim$ `stdNormalSeq`. Then:
- $z\mapsto\max_{0\le n\le N}(X_n-Y_n)^2$ is integrable, and
- $\mathbb E\big[\max_{0\le n\le N}(X_n-Y_n)^2\big]\le\big((N+1)\,C_m(r,\sigma,T,s_0)\,h^m\big)^{1/m}$, where
  $h^m$ is a natural-number power and the outer power is `rpow`.

**Assessment.**
- **Truth:** true. $\mathbb E\max_n e_n^2\le(\mathbb E\max_n e_n^{2m})^{1/m}$ by Jensen/Lyapunov, and
  $\mathbb E\max_n e_n^{2m}\le\sum_{n\le N}\mathbb E e_n^{2m}\le(N+1)C_mh^m$. The last step needs the per-time
  strong $L^{2m}$ bound $\mathbb E|X_n-Y_n|^{2m}\le C_mh^m$ for $nh\le T$.
  - I checked this bound against the exact closed form, which expands
    $\mathbb E[X_n^jY_n^{2m-j}]=s_0^{2m}\big(e^{ja+j^2b^2/2}\,\mathbb E(1+c+jb^2+bz)^{2m-j}\big)^n$ binomially, at
    high precision (`check_moment_const*.py`).
  - Over about 750 cases ($m\le5$, $\sigma\in[0,3]$, $|r|\le10$, $T\le20$, including $h\nmid T$ and $1+rh<0$) the
    maximum ratio was $5.5\times10^{-3}$.
  - $C_m\ge0$, so the `rpow` base is non-negative.
  - Edge case $h=0$: both paths are constantly $s_0$, so the left side is $0$ and the right side is
    $((N+1)C_m\cdot0)^{1/m}=0$.
- **Vacuity:** not vacuous ($h=0.1$, $N=10$, $T=1$, $m=2$).
- **Junk values:** none relied on.
- **Hypotheses:** $m>0$ is needed. For $m=0$ the right side would be $1^{0}$-type junk equal to $1$, which is false in
  general. The bound grows with $N$: for $N\approx T/h$ it is about $T^{1/m}C_m^{1/m}h^{1-1/m}$, and for $m=1$ it is
  only about $C_1(T+h)$, so it does not vanish. This is a weak, crude max-over-grid bound; the sharp bound is the next
  theorem.
- **Standard fact:** strong $L^p$ convergence of order $\tfrac12$ for Euler–Maruyama applied to GBM, combined with a
  union bound for the maximum over the grid.

## 3. `gbm_em_grid_max_error_sharp`

**Rendering.** For $r,\sigma,s_0$ and $T\ge0$ there is $C\ge0$, depending only on $(r,\sigma,s_0,T)$, such that for
every real $h\ge0$ and every $N\in\mathbb N$ with $Nh\le T$:
- $\max_{0\le n\le N}(X_n-Y_n)^2$ is integrable, and
- $\mathbb E\max_{0\le n\le N}(X_n-Y_n)^2\le C\,h$.

**Assessment.**
- **Truth:** true. It is the classical strong error bound $\mathbb E\sup_{n\le N}|X(t_n)-Y_n|^2\le Ch$ for
  Euler–Maruyama with globally Lipschitz coefficients, via a discrete Gronwall argument plus Doob or BDG on the
  martingale part. For larger $h$ (up to $T$), uniform moment bounds give a constant times $h$. When $h>T$ only $N=0$
  is allowed and the left side is $0$. A Monte Carlo check (`mc_rates.out`, $r=0.05$, $\sigma=0.4$) shows
  $\mathbb E\max e^2/h\approx0.016$–$0.030$ for $h$ from $1/2$ to $1/512$.
- **Vacuity:** no.
- **Junk values:** none.
- **Quantifiers:** $C$ is chosen before $h$ and $N$. This is the standard uniform form.
- **Standard fact:** Kloeden–Platen / Higham–Mao–Stuart strong order $\tfrac12$ in sup-norm on the grid.

## 4. `gbm_grid_monitoring_gap_rate`

**Rendering.** For $r,\sigma,s_0$, $T\ge0$ and $\delta>0$ there is $C\ge0$ (depending on $r,\sigma,s_0,T,\delta$) such
that for all $h\ge0$ and $N\in\mathbb N$ with $2Nh\le T$, writing $X_n=$ `gbmGridExact r σ h s₀ z n`:
- $\big(\max_{0\le n\le 2N}X_n-\max_{0\le k\le N}X_{2k}\big)^2$ is integrable, with
  $\mathbb E[\cdot]\le C\,h^{1-\delta}$ (`rpow`);
- the same holds with $\min$ in place of $\max$.

**Assessment.**
- **Truth:** true. $0\le\max_{\text{fine}}-\max_{\text{coarse}}\le\max_k|X_{2k+1}-X_{2k}|$, and
  $\mathbb E\max_k|\Delta X|^2\le(\sum_k\mathbb E|\Delta X_k|^{2p})^{1/p}\lesssim(N h^p)^{1/p}\lesssim h^{1-1/p}$.
  Choosing $p\ge1/\delta$ gives the claim; for $h\le T/2$ all moments are uniformly bounded. The minimum is
  symmetric.
- **Sharpness:** the true rate is $O(h)$, since $(\text{gap})/\sqrt h$ has a limit law (Asmussen–Glynn–Pitman type).
  Monte Carlo in `mc_rates.out` gives $\mathbb E\text{gap}_{\max}^2/h\to\approx0.058$ and
  $\mathbb E\text{gap}_{\min}^2/h\approx0.017$. So the statement is weaker than optimal, but true.
- **Edge cases:**
  - $h=0$: $X_n\equiv s_0$, so the left side is $0$. The right side is $C\cdot0^{1-\delta}$, which is $0$, or $C$ when
    $\delta=1$. Mathlib's $0^{x}=0$ for $x<0$ is used when $\delta>1$, but the inequality $0\le0$ holds anyway.
  - $T=0$ with $h>0$ forces $N=0$, and both sides of the gap are $s_0$.
- **Vacuity:** no.
- **Junk values:** none relied on.
- **Hypotheses:** $\delta\ge1$ is allowed, and then the claim is only boundedness, or weaker.
- **Standard fact:** discrete-monitoring error of the running maximum or minimum of Brownian motion / GBM between
  nested grids.

## 5. `lookbackMinPayoff` (def)

**Rendering.** $\texttt{lookbackMinPayoff}(g,m,S)=g(\min_{0\le n\le m}S_n)$. This is the discretely monitored
lookback-on-minimum payoff, the counterpart of `lookbackPayoff` $=g(\max_{0\le n\le m}S_n)$.

## 6. `gbm_em_gridLookback_variance_rate`

**Rendering.** For $r,\sigma,s_0$, $T\ge0$, $g:\mathbb R\to\mathbb R$ with $|g(x)-g(y)|\le K|x-y|$, and $\delta>0$,
there is $C\ge0$ such that for every $\ell\in\mathbb N$, with $h_{\ell}=T/2^{\ell}$,
$$\operatorname{Var}\Big[g\big(\max_{n\le 2^{\ell+1}}Y^{(h_{\ell+1})}_n(z)\big)-g\big(\max_{k\le 2^{\ell}}Y^{(h_\ell)}_k(\mathrm{pairAvg}\,z)\big)\Big]\le C\,h_{\ell+1}^{\,1-\delta}.$$
Here $Y^{(h)}(w)$ is the GBM EM path with step $h$ driven by $w$, and Var is Mathlib `variance`, i.e.
`(evariance).toReal`.

**Assessment.**
- **Truth:** true. $\operatorname{Var}D\le\mathbb E D^2\le K^2\,\mathbb E(\Delta\max)^2$. Then split
  $\max\text{EM}_f-\max\text{EM}_c$ into three terms:
  - $(\max\text{EM}_f-\max X_{\text{fine}})$, which is $O(h)$ in $L^2$ by #3;
  - $(\max X_{\text{fine}}-\max X_{\text{even}})$, which is $O(h^{1-\delta})$ by #4;
  - $(\max X_{\text{even}}-\max\text{EM}_c)$, which is $O(h)$ by #3, because the exact GBM driven by `pairAvg z`
    with step $2h$ equals $X_{2k}$ with step $h$.
- **Edge case $T=0$:** everything equals $s_0$, so the variance is $0$.
- The random variable is in $L^2$ (Lipschitz $g$, all EM moments finite), so `variance` is the genuine variance
  rather than the `toReal ⊤ = 0` junk.
- **Vacuity:** no.
- **Junk values:** none.
- **Hypotheses:** $\delta\ge1$ is allowed (then the claim is just boundedness). The rate is weaker than the
  numerically expected $O(h)$.
- **Standard fact:** MLMC level-variance bound $V_\ell=O(h_\ell^{\beta})$ (Giles 2008), here with
  $\beta=1-\delta$, for the EM discretely monitored lookback.

## 7. `gbm_em_gridLookbackMin_variance_rate`

**Rendering.** As #6 with $\min$ in place of $\max$, via `lookbackMinPayoff`.

**Assessment.** True by the same argument, using the $\min$ half of #4. It is not vacuous and does not rely on junk
values. Standard fact: same as #6.

## 8. `gbm_em_gridFloatLookback_variance_rate`

**Rendering.** As #6 with payoff $g(S_m-\min_{n\le m}S_n)$ for $m=2^{\ell+1}$ (fine) and $m=2^\ell$ (coarse). The
terminal values are $S_{2^{\ell+1}}$ on the fine path and $S_{2^\ell}$ on the coarse path, both at time $T$.

**Assessment.** True. $|D|\le K(|S^f_T-S^c_T|+|\min_f-\min_c|)$. The terminal-value difference is $O(h)$ in $L^2$
by #3, and the minimum difference is handled as in #7. It is not vacuous and does not rely on junk values. Standard
fact: as in #6, for a floating-strike lookback.

## 9. `gbm_em_gridLookback_mean_converges`

**Rendering.** For $r,\sigma,s_0$, $T\ge0$ and $K$-Lipschitz $g$ there is $Y\in\mathbb R$ such that:
1. $\mathbb E\,g(\max_{n\le2^\ell}Y^{(T/2^\ell)}_n)\to Y$ as $\ell\to\infty$ (EM, step $T/2^\ell$);
2. $\mathbb E\,g(\max_{n\le 2^\ell}X^{(T/2^\ell)}_n)\to Y$ (exact GBM on the grid);
3. for every $\delta\in(0,1)$ there is $C\ge0$ such that for all $\ell$,
   $|\mathbb E\,g(\max\text{EM}_\ell)-Y|\le C(T/2^\ell)^{(1-\delta)/2}$.

**Assessment.**
- **Truth:** true, with $Y=\mathbb E\,g(\sup_{t\le T}S_t)$.
  - For (2), the laws match those of a single GBM sampled on nested dyadic grids. The grid maxima increase to the
    continuous supremum, and dominated convergence applies with the bound $|g(0)|+K\sup S$, which is integrable by
    Doob.
  - (1) and (3) follow from the telescoping estimate $\sum_{\ell'\ge\ell}\sqrt{\mathbb E D_{\ell'}^2}$ using the #6
    bounds, together with (2).
- **Edge case $T=0$:** both sequences are constantly $g(s_0)$, and the right side of (3) is $0$.
- **Junk values:** the integrands are integrable, because Lipschitz $g$ is dominated by the sum of $|Y_n|$, which have
  finite means. So the "non-integrable gives 0" convention is not in play. The exponent $(1-\delta)/2>0$.
- **Vacuity:** no.
- **Hypotheses:** the rate $(1-\delta)/2$ is weaker than the true $\tfrac12$.
- **Standard fact:** weak convergence of order $\approx\tfrac12$ of discretely monitored lookback prices to the
  continuously monitored price; MLMC parameter $\alpha$.

## 10. `gbm_em_gridLookbackMin_mean_converges`

**Rendering and assessment.** As #9 with $\min$, where $Y=\mathbb E\,g(\inf_{t\le T}S_t)$. True. It is not vacuous
and does not rely on junk values.

## 11. `gbm_em_gridFloatLookback_mean_converges`

**Rendering and assessment.** As #9 with payoff $g(S_T-\min)$, where $Y=\mathbb E\,g(S_T-\inf_{t\le T}S_t)$. True.
It is not vacuous and does not rely on junk values.

## 12. `gbm_em_gridLookback_theorem1`

**Rendering.** For $r,\sigma,s_0$, $T\ge0$ and $K$-Lipschitz $g$ there is $Y$ such that:
- $\mathbb E\,g(\max_{n\le2^\ell}X^{(T/2^\ell)}_n)\to Y$ (exact-GBM grid lookback), and
- for every $\eta>0$ there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb N$ and
  $N:\mathbb N\to\mathbb N$ with $N_\ell\ge1$ for all $\ell$, satisfying both:
  - $\mathbb E\Big[\big(\sum_{\ell=0}^{L}\tfrac1{N_\ell}\sum_{n<N_\ell}\Delta P_\ell(x_{\ell,n})-Y\big)^2\Big]<\varepsilon^2$,
    where $x_{\ell,n}$ are i.i.d. `stdNormalSeq` sequences (product measure over $\mathbb N\times\mathbb N$);
    $\Delta P_0=g(\max(Y_0,Y_1))$ with step $T$; and
    $\Delta P_{\ell+1}(z)=g(\max\text{EM}_{T/2^{\ell+1}}(z))-g(\max\text{EM}_{T/2^\ell}(\mathrm{pairAvg}\,z))$;
  - the cost $\sum_{\ell\le L}N_\ell2^\ell\le c_4\,\varepsilon^{-2-\eta}$.

**Assessment.**
- **Truth:** true. Apply Giles' MLMC complexity theorem with $\alpha=(1-\delta)/2$ (from #9(3)),
  $\beta=1-\delta$ (from #6) and $\gamma=1$. Then $\alpha\ge\tfrac12\beta$, and in the case $\beta<\gamma$ the cost
  is $O(\varepsilon^{-2-(\gamma-\beta)/\alpha})=O(\varepsilon^{-2-2\delta/(1-\delta)})$. Choose $\delta$ with
  $2\delta/(1-\delta)\le\eta$.
- **Not trivially satisfiable:** plain Monte Carlo (single level) would cost about $\varepsilon^{-4}$, and
  $L=0$ leaves a fixed bias. So the content is genuinely MLMC.
- **Edge case $T=0$:** take $L=0$, $N_0=1$, $c_4=1$. The MSE is $0$, and $1\le\varepsilon^{-2-\eta}$.
- **Quantifiers:** $c_4$ depends on $\eta$ and the problem data only; $L$ and $N$ depend on $\varepsilon$. These are
  correct. The condition $N_\ell>0$ for all $\ell$ (also $\ell>L$) is harmless and avoids $1/0$ in `blockMean`.
- **Vacuity:** no.
- **Junk values:** none; the estimator is $L^2$, and $\varepsilon^{-2-\eta}$ is `rpow` of a positive base.
- **Hypotheses:** the cost exponent $-2-\eta$ (for every $\eta>0$) is weaker than the
  $\varepsilon^{-2}(\log\varepsilon)^2$ one would get with $\beta=1$.
- **Target:** $Y$ is the continuously monitored lookback price, so the MSE is measured against the true price, not
  against the EM limit.
- **Standard fact:** Giles (2008, Oper. Res.), Theorem 3.1, the MLMC complexity theorem, applied to the EM lookback.

## 13. `gbm_em_gridLookbackMin_theorem1`

**Rendering and assessment.** As #12 with `lookbackMinPayoff`, where $Y=\mathbb E\,g(\inf S)$. True, using #7 and
#10. It is not vacuous and does not rely on junk values.

## 14. `gbm_em_gridFloatLookback_theorem1`

**Rendering and assessment.** As #12 with `floatLookbackPayoff`, where $Y=\mathbb E\,g(S_T-\inf S)$. True, using #8
and #11. It is not vacuous and does not rely on junk values.
