# Blind read-back report: R30 (GBM weak order / MLMC Theorem 1 for GBM)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round21/packet_R30_gbmweak.lean` |
| declarations audited | 16 theorems (plus the 3 local definitions `gbmWeakPowConst`, `gbmBackOp`, `gbmWeakSmoothConst`, rendered for reference) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round21/work_R30/` (`check_pow.py/.out`, `check_smooth.py/.out`, `check_var.py/.out`, `scratch.lean/.out`) |

Elaboration was confirmed by compiling a scratch copy of the packet (namespace renamed to
`MLMCAudit`, the three local definitions suffixed `A`) against `import MlmcLean`; all 16
statements elaborate. In particular `(p - 1)` in `integral_gbmExp_pow` / `integral_gbmExact_pow`
elaborates as the **real** subtraction `(↑p - 1 : ℝ)`, `emFineM` uses step `h₀ / (↑M)^ℓ` and
`emCoarseM` step `↑M * (h₀ / (↑M)^(ℓ+1))` (see `scratch.out`).

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `integral_emPath_gbm_pow` | theorem | true | no | no |
| 2 | `integral_gbmExp_pow` | theorem | true | no | no |
| 3 | `integral_gbmExact_pow` | theorem | true | no | no |
| 4 | `gbm_em_weak_error_pow` | theorem | true | no | no |
| 5 | `gbm_weak_error_pow` | theorem | true | no | no |
| 6 | `gbm_weak_error_poly` | theorem | true | no | no |
| 7 | `gbm_weak_error_poly_M` | theorem | true | no | no |
| 8 | `gbm_em_weak_error_smooth` | theorem | true (proof sketch + numerical spot checks) | no | no |
| 9 | `gbm_weak_error_smooth` | theorem | true | no | no |
| 10 | `gbm_weak_error_smooth_M` | theorem | true | no | no |
| 11 | `gbm_mlmc_theorem1_smooth_M` | theorem | true | no | no |
| 12 | `gbm_mlmc_theorem1_smooth` | theorem | true | no | no |
| 13 | `gbm_poly_correction_variance_le` | theorem | true (exact numerical check) | no | no |
| 14 | `gbm_poly_correction_variance_le_M` | theorem | true (exact numerical check) | no | no |
| 15 | `gbm_mlmc_theorem1_poly_M` | theorem | true | no | no |
| 16 | `gbm_mlmc_theorem1_poly` | theorem | true | no | no |

## Main points for a human auditor

1. **All 16 theorems are true as stated**, none is vacuous, and none holds only because of a junk value. Every integrand is a polynomial, or a function of linear growth, of finitely many Gaussians, so all integrals and variances are genuine and finite. The hypotheses $h\ge0$ / $T\ge0$ are necessary: `Real.sqrt` of a negative number is $0$, which would break the identities (#2, #3). $m,M>0$ are necessary in the `_M` weak-error statements.
2. **The constants are explicit, non-asymptotic and valid for all $h\ge0$, $n$, $\ell$, but loose.** The power weak-error bound (#4) has slack $\ge4\times$ in an exact test over 34 848 cases. The smooth bound (#8) has slack $\approx300\times$ in the spot checks. The level-variance bounds (#13, #14) are loose by a factor of about $10^5$–$10^6$ in exact tests, which is harmless because only the order $O(h_\ell)$ ($\beta=1$) is used.
3. **#8 (smooth weak order 1) was checked numerically and by an operator-splitting proof sketch, not proved line by line.** The assumptions are $C^4$-type, with $|g^{(k)}|\le K$ for $k=1..4$ (Talay–Tubaro-type), which is stronger than needed for GBM.
4. **Scope of the MLMC theorems (#11, #12, #15, #16).** They are Giles (2008) Theorem 1 with $\alpha=\beta=\gamma=1$, giving cost $O(\varepsilon^{-2}(\log\varepsilon)^2)$, for GBM with either a $C^4$ payoff with bounded derivatives or a polynomial payoff. They do **not** cover the non-smooth European call payoff of Giles §5. Quantifier order is the standard one ($c_4,c_5$ before $\varepsilon$). The extra conclusion $M^L\le c_5/\varepsilon$ is not in Giles' statement but follows from the standard choice of $L$. The cost counts only the fine-path steps $N_\ell\,mM^\ell$; adding the coarse steps changes only a constant factor.
5. **Coupling checked.** `emCoarseM` / `emCoarse` give the level-$\ell$ EM path driven by the block-summed or pair-summed level-$(\ell+1)$ increments (`blockAvg`, `pairAvg`), evaluated at the final time $T$. This is the standard MLMC fine/coarse coupling, and the coarse sample has the same law as the fine sample of the previous level, so the sum telescopes.
6. **`gbmBackOp` is defined but used by no theorem in this packet.** It is $(Pf)^{(j)}$-style notation: $\mathbb E[Y^jf(xY)]$.
7. **Lean-level detail confirmed by elaboration:** `(p - 1)` in the lognormal moment formulas is real subtraction `(↑p - 1 : ℝ)`. In $B_d$, `3 ^ (2 * (2 * d) - 1)` uses truncated ℕ subtraction, which matters only when $d=0$, where the whole bound is multiplied by $0$ anyway.

## Common notation and conventions

* `stdNormalSeq` $=\bigotimes_{i\in\mathbb N}N(0,1)$ on $\mathbb R^{\mathbb N}$: the coordinates $z_0,z_1,\dots$ are i.i.d. standard normal.
* `gbmDrift r` $=(S,t)\mapsto rS$, `gbmVol σ` $=(S,t)\mapsto\sigma S$. Hence `emPath (gbmDrift r) (gbmVol σ) h s₀ z` is the Euler–Maruyama (EM) recursion $S_0=s_0$, $S_{i+1}=S_i(1+rh+\sigma\sqrt h\,z_i)$, i.e. $S_n=s_0\prod_{i<n}(1+rh+\sigma\sqrt h z_i)$ (`Real.sqrt h = 0` for $h<0$).
* `gbmEMFactor r σ h x` $=1+rh+\sigma\sqrt h x$; `gbmExpFactor r σ h x` $=e^{(r-\sigma^2/2)h+\sigma\sqrt h x}$.
* `gbmEM r σ T s₀ ℓ z` $=S_{2^\ell}$ with $h=T/2^\ell$; `gbmExact r σ T s₀ ℓ z` $=s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt{T/2^\ell}\sum_{i<2^\ell}z_i\big)$, the exact GBM at time $T$ driven by the same Brownian increments.
* `emFineM a b h₀ s₀ M Φ ℓ z` $=\Phi_\ell(\text{EM path with step }h_0/M^\ell\text{ driven by }z)$; `emCoarseM … ℓ z` $=\Phi_\ell(\text{EM path with step }M\cdot h_0/M^{\ell+1}=h_0/M^\ell\text{ driven by }\texttt{blockAvg}\,M\,z)$, where `blockAvg M z k` $=(\sum_{i<M}z_{Mk+i})/\sqrt M$. With $\Phi_\ell(\text{path})=g(\text{path}(mM^\ell))$ and $h_0=T/m$, the fine level-$\ell$ sample is $g$ of the EM approximation of $S_T$ with $mM^\ell$ steps, and the coarse level-$\ell$ sample is the level-$\ell$ EM approximation driven by the aggregated increments of the level-$(\ell+1)$ noise (the standard MLMC coupling). For GBM, one coarse step is $S\mapsto S(1+Mrh+\sigma\sqrt h\sum_{j<M}z_j)$ with $h=h_{\ell+1}$.
* `emFine`/`emCoarse` with `europeanPayoff g` are the $M=2$, $m=1$ versions (coarse path uses `pairAvg`), so `fineCoarseDiff … (ℓ+1)` $=g(S^{(\ell+1)}_T)-g(S^{(\ell),\text{coarse}}_T)$.
* `fineCoarseDiff Pf Pc 0 = Pf 0`, `fineCoarseDiff Pf Pc (ℓ+1) = Pf (ℓ+1) − Pc ℓ`.
* `blockMean f (fun p x => x p) ℓ N x` $=\frac1N\sum_{n<N}f_\ell(x_{(\ell,n)})$ (and $0$ if $N=0$); under `Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq` the $x_{(\ell,n)}$ are i.i.d. copies of `stdNormalSeq`.
* `variance X μ` is `(evariance X μ).toReal` (Mathlib, `Probability/Moments/Variance.lean`), so it would be $0$ for a non-$L^2$ variable; all variables in this packet are polynomials (or linear-growth functions) of finitely many Gaussians, so they have all moments and no junk arises.
* $\mu_p:=p(|r|+p\sigma^2)$ and
  `gbmWeakPowConst p r σ t s₀` $=2|s_0|^p\mu_p^2\,t\,e^{\mu_p t}$.
* $c:=4|r|+8\sigma^2$ and `gbmWeakSmoothConst K r σ s₀ t` $=5Kc^2(1+s_0^4)\,t\,e^{ct}$.
* `gbmBackOp r σ h j f x` $=\int (\texttt{gbmExpFactor}\ r\,\sigma\,h\,w)^j f(x\cdot\texttt{gbmExpFactor}\ r\,\sigma\,h\,w)\,dN(0,1)(w)=\mathbb E[Y^jf(xY)]$ with $Y=e^{(r-\sigma^2/2)h+\sigma\sqrt hW}$ (the $j$-th derivative of the one-step exact transition operator, $(Pf)^{(j)}(x)=\mathbb E[Y^jf^{(j)}(xY)]$, applied to $f=g^{(j)}$). It is a definition only and is not used by any theorem in the packet. (If the integrand is not integrable the Bochner integral is $0$; no theorem depends on it.)
* $A:=$`gbmEMMomentConst 2 r σ T s₀` (full definition appended to the packet; it is $s_0^4\,T\cdot(\text{explicit polynomial-type factor in }|r|,\sigma,\sqrt T)\cdot e^{(\text{rate}+1)T}\ge0$) and, with $d=\deg q$ (`natDegree`), $B_d:=3^{4d-1}\big(1+2s_0^{4d}e^{(4d|r|+8d^2\sigma^2)T}\big)$ where $4d-1$ is truncated ℕ-subtraction ($3^{0-1}=3^0=1$ when $d=0$). $B_d$ is the natural bound for $\mathbb E(1+|X|+|Y|)^{4d}\le3^{4d-1}(1+\mathbb E|X|^{4d}+\mathbb E|Y|^{4d})$ with the EM moment bound $\mathbb E|S|^{p}\le |s_0|^pe^{(p|r|+p^2\sigma^2/2)T}$, $p=4d$.

## Per-declaration sections

### 1. `integral_emPath_gbm_pow`

**Rendering.** For all $r,\sigma,h,s_0\in\mathbb R$ and $N,p\in\mathbb N$ (no hypotheses; $h$ may be negative):
$$\mathbb E\big[S_N^p\big]=s_0^p\Big(\mathbb E\big[(1+rh+\sigma\sqrt h Z)^p\big]\Big)^N,\qquad Z\sim N(0,1),$$
where $S_N$ is the GBM Euler–Maruyama value after $N$ steps of size $h$ driven by i.i.d. $z_i\sim N(0,1)$.

**Assessment.** True: $S_N=s_0\prod_{i<N}(1+rh+\sigma\sqrt hz_i)$ and the factors are independent, so $\mathbb E S_N^p=s_0^p\prod_i\mathbb E(\cdot)^p$. Both sides use the same `Real.sqrt`, so the identity also holds for $h<0$ (no junk dependence; for $h<0$ it is just the deterministic identity $(s_0(1+rh)^N)^p$). Not vacuous (any values). $N=0$ gives $s_0^p=s_0^p$. Standard: moments of a product of independent factors (the multiplicative structure of EM for GBM). The one-step moment formula used later was checked by quadrature (`check_pow.out`).

### 2. `integral_gbmExp_pow`

**Rendering.** For $r,\sigma,s_0\in\mathbb R$, $h\ge0$, $n,p\in\mathbb N$:
$$\mathbb E\Big[\Big(s_0\exp\big((r-\tfrac{\sigma^2}{2})nh+\sigma\sqrt h\textstyle\sum_{i<n}z_i\big)\Big)^p\Big]=s_0^p\exp\big(p\,(r+(p-1)\sigma^2/2)\,nh\big),$$
with $p-1$ computed in $\mathbb R$ (confirmed by elaboration: `(↑p - 1 : ℝ)`).

**Assessment.** True: $\sigma\sqrt h\sum_{i<n}z_i\sim N(0,\sigma^2nh)$, so the left side is $s_0^pe^{p(r-\sigma^2/2)nh}e^{p^2\sigma^2nh/2}=s_0^pe^{p(r+(p-1)\sigma^2/2)nh}$ (lognormal moments $=$ moments of exact GBM, $\mathbb E S_t^p=s_0^pe^{(pr+p(p-1)\sigma^2/2)t}$). Checked by quadrature for several $(r,\sigma,s_0,h,n,p)$ including $p=0$, odd $p$ and negative $s_0$ (`check_pow.out`). The hypothesis $h\ge0$ is necessary (for $h<0$, $\sqrt h=0$ and the two sides differ; example in `check_pow.out`), so it is not superfluous. Not vacuous. No junk.

### 3. `integral_gbmExact_pow`

**Rendering.** For $T\ge0$, $\ell,p\in\mathbb N$: $\mathbb E[(\texttt{gbmExact}\ r\,\sigma\,T\,s_0\,\ell)^p]=s_0^p\exp\big(p(r+(p-1)\sigma^2/2)T\big)$ (real $p-1$).

**Assessment.** True: special case of #2 with $n=2^\ell$, $h=T/2^\ell$ (or directly: $\sigma\sqrt{T/2^\ell}\sum_{i<2^\ell}z_i\sim N(0,\sigma^2T)$). $T\ge0$ is necessary for the same reason as in #2. The $p$-th moment of exact GBM, $\mathbb E S_T^p$. Not vacuous; no junk.

### 4. `gbm_em_weak_error_pow`

**Rendering.** For $r,\sigma,s_0$, $h\ge0$, $n,p\in\mathbb N$:
$$\Big|\mathbb E[S_n^p]-\mathbb E\Big[\Big(s_0e^{(r-\sigma^2/2)nh+\sigma\sqrt h\sum_{i<n}z_i}\Big)^p\Big]\Big|\le 2|s_0|^p\mu_p^2\,(nh)\,e^{\mu_p nh}\cdot h,\qquad \mu_p=p(|r|+p\sigma^2).$$
Non-asymptotic: for every $h\ge0$ and every $n$, with the explicit constant.

**Assessment.** True. By #1/#2 the left side is $|s_0|^p|a^n-b^n|$ with $a=\mathbb E(1+rh+\sigma\sqrt hZ)^p$, $b=e^{\lambda h}$, $\lambda=pr+p(p-1)\sigma^2/2$. Bounds: $|a|\le(1+|r|h)^p\sum_j\binom p{2j}(2j-1)!!(\sigma^2h)^j\le e^{p|r|h}e^{p^2\sigma^2h/2}\le e^{\mu_ph}$ (using $\binom p{2j}(2j-1)!!\le (p^2/2)^j/j!$); $|b|\le e^{\mu_ph}$; and expanding to second order, $|a-1-\lambda h|\le\frac12\mu_p^2h^2e^{\mu_ph}$, $|b-1-\lambda h|\le\frac12\lambda^2h^2e^{|\lambda|h}\le\frac12\mu_p^2h^2e^{\mu_ph}$. Then $|a^n-b^n|\le n\max(|a|,|b|)^{n-1}|a-b|\le\mu_p^2\,n h^2e^{\mu_pnh}$, half the stated bound. Exact high-precision check over 34 848 parameter combinations ($p\le10$, $r\in[-20,20]$, $\sigma\le5$, $h\in[10^{-6},5]$, $n\le1000$): no violation; worst ratio LHS/RHS $=0.2503$ (`check_pow.out`). Edge cases $p=0$ or $n=0$: both sides $0$. Not vacuous. No junk (the moments are finite; $|s_0|^p$ with ℕ exponent). This is the weak order-1 estimate of Euler–Maruyama for GBM tested on monomials, with fully explicit constant.

### 5. `gbm_weak_error_pow`

**Rendering.** For $T\ge0$, $\ell,p$: $\big|\mathbb E[\texttt{gbmEM}^p]-\mathbb E[\texttt{gbmExact}^p]\big|\le \texttt{gbmWeakPowConst}\ p\,r\,\sigma\,T\,s_0\cdot T/2^\ell$, i.e. the level-$\ell$ EM approximation (step $T/2^\ell$, $2^\ell$ steps) of $S_T$ has $p$-th-moment weak error $\le2|s_0|^p\mu_p^2Te^{\mu_pT}\cdot T/2^\ell$.

**Assessment.** True: #4 with $n=2^\ell$, $h=T/2^\ell$ ($nh=T$, and the exact expression in #4 coincides with `gbmExact`). Weak order 1 in $h_\ell=T/2^\ell$. Not vacuous; no junk.

### 6. `gbm_weak_error_poly`

**Rendering.** For $T\ge0$, $\ell$, any real polynomial $q$ of degree $d$ (`natDegree`):
$\big|\mathbb E q(\texttt{gbmEM})-\mathbb E q(\texttt{gbmExact})\big|\le\Big(\sum_{i=0}^{d}|q_i|\,\texttt{gbmWeakPowConst}\ i\,r\,\sigma\,T\,s_0\Big)\cdot T/2^\ell$.

**Assessment.** True by linearity of the integral (all moments finite, so integrals split) and the triangle inequality applied to #5. $q=0$: both sides $0$. Not vacuous; no junk. Weak order 1 for polynomial payoffs.

### 7. `gbm_weak_error_poly_M`

**Rendering.** For $T\ge0$, $m\ge1$, $M\ge1$ (ℕ), polynomial $q$, level $\ell$:
$$\Big|\mathbb E\,q\big(S^{\text{EM}}_{mM^\ell}\big)-\int q\big(s_0e^{(r-\sigma^2/2)T+\sigma\sqrt T w}\big)\,dN(0,1)(w)\Big|\le\Big(\sum_{i\le d}|q_i|\,\texttt{gbmWeakPowConst}\ i\,r\,\sigma\,T\,s_0\Big)\cdot\frac{T}{mM^\ell},$$
where $S^{\text{EM}}$ uses step $h_\ell=(T/m)/M^\ell$; the second integral is $\mathbb E\,q(S_T)$ for exact GBM.

**Assessment.** True: #4 with $n=mM^\ell$, $h=T/(mM^\ell)$ (so $nh=T$), plus $\sqrt h\sum_{i<n}z_i\sim\sqrt T\,W$ to rewrite the exact side as a one-dimensional Gaussian integral. $m,M>0$ are needed (if $m=0$ then $T/m=0$, the path is constant $s_0$ evaluated at step $0$, and the right side is $0$ while the left side is generally not). Not vacuous; no junk.

### 8. `gbm_em_weak_error_smooth`

**Rendering.** Let $g:\mathbb R\to\mathbb R$ with `iteratedDeriv k g` differentiable for $k=0,1,2,3$ (so $g$ is four times differentiable everywhere) and $|g^{(k)}(x)|\le K$ for all $x$ and $k=1,2,3,4$ ($g$ itself need not be bounded; $K\ge0$ is forced). Then for $r,\sigma,s_0$, $h\ge0$, $n\in\mathbb N$:
$$\Big|\mathbb E\,g(S_n)-\mathbb E\,g\Big(s_0e^{(r-\sigma^2/2)nh+\sigma\sqrt h\sum_{i<n}z_i}\Big)\Big|\le5Kc^2(1+s_0^4)\,(nh)\,e^{c\,nh}\cdot h,\qquad c=4|r|+8\sigma^2.$$

**Assessment.** True (I did not find a counterexample; argument sketch). Write $Q$, $P$ for the one-step EM and exact transition operators, so the error is $|\sum_{k<n}Q^k(Q-P)P^{n-1-k}g(s_0)|$. For $u=P^jg$ one has $u^{(i)}(x)=\mathbb E[Y_j^ig^{(i)}(xY_j)]$, so $\|u^{(i)}\|_\infty\le K e^{(4|r|+6\sigma^2)jh}$ for $i\le4$. A fourth-order Taylor expansion with Lagrange remainder gives $|(Q-P)u(x)|\le K'(h)\,h^2(|x|+x^2+|x|^3+x^4)$ with $K'(h)$ of the form (polynomial in $|r|,\sigma^2$)$\cdot e^{O(h)}$; the small-$h$ coefficient is $|{-\tfrac12}r^2xu'-(r\sigma^2+\tfrac14\sigma^4)x^2u''-\tfrac12\sigma^4x^3u'''|$, far below $5c^2$. EM fourth moments grow at most like $e^{(4|r|+6\sigma^2)kh}$, and $|x|+x^2+|x|^3+x^4\le2.1(1+x^4)$. Summing $n$ terms gives the stated form, with slack in both the prefactor and the rate ($8\sigma^2$ versus $6\sigma^2$). Numerical spot checks (mpmath quadrature, $n=1,2$; $g=\sin(ax+\varphi)$ with $K=\max(a,a^4)$, and $g(x)=x$; $r\in\{-1,0,0.5,2\}$, $\sigma\le2$, $s_0\in\{0.5,1,2\}$): no violation; 566 non-trivial cases computed (EM side via the closed form $\mathbb E\sin(\alpha+\beta Z)=\sin\alpha\,e^{-\beta^2/2}$ for the last step and quadrature for the earlier ones, $n=3$ on a small grid), and 1170 further cases are trivially satisfied because RHS $\ge2\ge|$LHS$|$ for sine payoffs; worst ratio LHS/RHS $=0.0028$; for $g(x)=x$ (closed form $|s_0||(1+rh)^n-e^{rnh}|$, $n\le100$) the worst ratio is $0.0031$ (`check_smooth.out`). Integrability: $|g(x)|\le|g(0)|+K|x|$ and both random variables have all moments, so no junk-zero integrals. Not vacuous ($g=\sin$, $K=1$). The hypotheses ($C^4$-type with bounded derivatives $1..4$) are the usual Talay–Tubaro-type conditions for weak order 1. They are stronger than necessary for GBM (e.g. polynomial growth would do) and exclude the non-smooth European call. This is the weak order-1 convergence of Euler–Maruyama (Kloeden–Platen Thm 14.5.1 type), specialised to GBM with an explicit constant.

### 9. `gbm_weak_error_smooth`

**Rendering.** Same hypotheses on $g,K$, $T\ge0$, $\ell\in\mathbb N$: $|\mathbb E g(\texttt{gbmEM})-\mathbb E g(\texttt{gbmExact})|\le5Kc^2(1+s_0^4)Te^{cT}\cdot T/2^\ell$.

**Assessment.** True: #8 with $n=2^\ell$, $h=T/2^\ell$. Not vacuous; no junk.

### 10. `gbm_weak_error_smooth_M`

**Rendering.** Same $g,K$; $T\ge0$, $m\ge1$, $M\ge1$, $\ell$: $\big|\mathbb E g(S^{\text{EM}}_{mM^\ell})-\int g(s_0e^{(r-\sigma^2/2)T+\sigma\sqrt Tw})dN(0,1)(w)\big|\le5Kc^2(1+s_0^4)Te^{cT}\cdot T/(mM^\ell)$, EM step $(T/m)/M^\ell$.

**Assessment.** True: #8 with $n=mM^\ell$, $h=T/(mM^\ell)$, and the exact side rewritten as a 1-D Gaussian integral (as in #7). $m,M>0$ are needed for the same reason as in #7. Not vacuous; no junk. This is the bias hypothesis (i) of Giles' Theorem 1 with $\alpha=1$.

### 11. `gbm_mlmc_theorem1_smooth_M`

**Rendering.** Fix $r,\sigma,s_0$, $T\ge0$, $m\ge1$, $M\ge2$, and $g$ as in #8 with constant $K$. Then there exist constants $c_4>0$, $c_5>0$ (depending on all of these, but **not** on $\varepsilon$) such that for every $\varepsilon\in(0,e^{-1})$ there are $L\in\mathbb N$ and sample sizes $N:\mathbb N\to\mathbb N$ with every $N_\ell\ge1$ for which the MLMC estimator
$$\hat Y=\sum_{\ell=0}^{L}\frac1{N_\ell}\sum_{n<N_\ell}\Delta_\ell\big(x_{(\ell,n)}\big),\quad \Delta_0=g(S^{(0)}_T),\ \Delta_\ell=g(S^{(\ell)}_T)-g(S^{(\ell-1),\text{coarse}}_T),$$
built from i.i.d. Gaussian sequences $x_{(\ell,n)}$ (level-$\ell$ EM uses $mM^\ell$ steps of size $T/(mM^\ell)$), satisfies:
(a) $(\hat Y-\mathbb E g(S_T))^2$ is integrable;
(b) $\mathbb E[(\hat Y-\mathbb E g(S_T))^2]<\varepsilon^2$;
(c) cost $\sum_{\ell\le L}N_\ell\,mM^\ell\le c_4\,\varepsilon^{-2}(\log\varepsilon)^2$;
(d) $M^L\le c_5/\varepsilon$.

**Assessment.** True. It is Giles (2008) Theorem 1 in the case $\alpha=\beta=\gamma=1$ (so $\beta=\gamma$ and the cost is $O(\varepsilon^{-2}(\log\varepsilon)^2)$), instantiated for GBM. The ingredients are: bias $\le c_1h_L$ from #10; $\mathbb E\Delta_\ell=\mathbb E g(S^{(\ell)})-\mathbb E g(S^{(\ell-1)})$ because `blockAvg M z` is again i.i.d. $N(0,1)$, so the sum telescopes; $\operatorname{Var}\Delta_\ell\le K^2\mathbb E|S^{(\ell)}-S^{(\ell-1)}|^2=O(h_\ell)$ (strong order ½); independence across $(\ell,n)$ from `infinitePi`; and the choices $L=\lceil\log_M(\sqrt2c_1T/(m\varepsilon))\rceil$, $N_\ell=\lceil2\varepsilon^{-2}(L+1)c_2h_\ell\rceil$. The extra conclusion (d) follows from that choice of $L$ (with $c_5\ge1$ covering $L=0$). Quantifier order is the standard one ($c_4,c_5$ before $\varepsilon$). $\varepsilon<e^{-1}$ makes $(\log\varepsilon)^2>1$, so nothing junk-like happens: $\varepsilon^{-2}$ is `rpow` of a positive base, and the division is by $\varepsilon>0$. $T=0$ is allowed and trivial (estimator exact). Not vacuous ($g=\sin$, $K=1$, $m=1$, $M=2$, $T=1$). Minor modelling remarks: the cost counts only fine-path steps $mM^\ell$ per sample (coarse steps add a factor $\le1+1/M$, which is harmless), and the conclusion is for $C^4$ payoffs with bounded derivatives, so it does **not** cover the European call of Giles' §5.

### 12. `gbm_mlmc_theorem1_smooth`

**Rendering.** As #11 with $M=2$, $m=1$, using `emFine`/`emCoarse` (`pairAvg` coupling) and `europeanPayoff g`: $\exists c_4,c_5>0\ \forall\varepsilon\in(0,e^{-1})\ \exists L,N$ ($N_\ell\ge1$) with integrable squared error, MSE $<\varepsilon^2$, cost $\sum_{\ell\le L}N_\ell2^\ell\le c_4\varepsilon^{-2}(\log\varepsilon)^2$, and $2^L\le c_5/\varepsilon$.

**Assessment.** True; same argument. I checked `emCoarse ℓ` $=g(\text{emCoarsePath}(T/2^{\ell+1})\ s_0\ z\ (2\cdot2^\ell))=g(\text{EM with step }T/2^\ell\text{ driven by pairAvg }z\text{ at step }2^\ell)$, which is the correct coarse partner of `emFine (ℓ+1)`. Not vacuous; no junk. Giles (2008) Theorem 1, $M=2$.

### 13. `gbm_poly_correction_variance_le`

**Rendering.** For $T\ge0$, polynomial $q$ of degree $d$, $\ell\in\mathbb N$, let $X$ be the level-$(\ell+1)$ EM value (step $h=T/2^{\ell+1}$, $2^{\ell+1}$ steps) and $Y$ the level-$\ell$ EM value driven by `pairAvg z` (step $2h$). Then
$$\operatorname{Var}\big(q(X)-q(Y)\big)\le3\Big(\sum_{k\le d}k|q_k|\Big)^2\,T\,(A+B_d)\cdot2^{-(\ell+1)}.$$

**Assessment.** True according to an exact computation; I did not derive the constant by hand. Proof idea: $|q(X)-q(Y)|\le\big(\sum_k k|q_k|\big)|X-Y|(1+|X|+|Y|)^{d-1}$, then Young/Cauchy–Schwarz with a strong $L^4$ bound on $X-Y$ ($A$, of order $h^2$ after scaling) and the moment bound $B_d$. Since the bound carries only $T\cdot2^{-(\ell+1)}=h$ while the true variance is $\approx s_0^2\sigma^4hT/2$ (e.g. exactly $s_0^2\sigma^4h^2$ for $q=x$, $r=0$, $\ell=0$), the inequality is an $O(h_\ell)$ variance bound, i.e. $\beta=1$. Exact check: `check_var.py` computes $\operatorname{Var}(q(X)-q(Y))$ exactly from Gaussian moments, using the block structure $\mathbb E[X^aY^b]=s_0^{a+b}(\mathbb E F^aG^b)^{\#\text{blocks}}$, and implements $A$ and $B_d$ literally from the appended definitions (truncated ℕ subtractions, `rpow` scale factors). Over 8000 combinations ($q\in\{x,x^2,x^3,1+2x-x^2,x^3-3x\}$, $r\in\{-1,0,0.5,2\}$, $\sigma\in\{0.05,0.3,1,2,4\}$, $T\in\{10^{-4},0.01,0.1,1,3\}$, $s_0\in\{0.1,0.5,1,2\}$, $\ell\in\{0,1,3,6\}$) there is no violation; the worst ratio Var/bound is $1.26\times10^{-6}$, so the bound is very loose (already $B_d\ge3^{4d-1}$ dominates), but it is valid and has the right order $O(h_\ell)$. A sanity check against the closed form $s_0^2\sigma^4h^2$ matched (`check_var.out`). Edge cases: $d=0$ gives prefactor $0$ and LHS $=\operatorname{Var}(0)=0$; $s_0=0$ gives LHS $0$. No junk: $q(X)-q(Y)\in L^2$, so `variance` is the true variance; $s_0^4$ and $s_0^{4d}$ are even powers. Not vacuous. This is the MLMC level-variance hypothesis (iii) of Giles' Theorem 1 with $\beta=1$ for polynomial payoffs.

### 14. `gbm_poly_correction_variance_le_M`

**Rendering.** For $T\ge0$, $m\ge1$, $M\ge1$, polynomial $q$, $\ell$: with fine step $h=(T/m)/M^{\ell+1}$ ($mM^{\ell+1}$ steps) and coarse step $Mh$ driven by `blockAvg M z` ($mM^\ell$ steps),
$$\operatorname{Var}\big(q(X^{\text{fine}}_{\ell+1})-q(Y^{\text{coarse}}_{\ell})\big)\le\Big(\sum_{k\le d}k|q_k|\Big)^2(A+B_d)\cdot\frac Tm\cdot\frac{M+1}{M^{\ell+1}}.$$

**Assessment.** True (exact check). For $M=2$, $m=1$ it reduces to #13 exactly ($M+1=3$). Asymptotically the true variance is $\approx s_0^2\sigma^4h\,T(M-1)/2$, while the bound is $(\cdot)(M+1)h$, so the $M$-dependence is of the right order. Exact check over $(M,m)\in\{(3,1),(4,2),(2,3)\}$ and the same grid as #13: no violation; worst ratio Var/bound $=2.26\times10^{-6}$ (`check_var.out`). $M\ge1$, $m\ge1$ prevent division by zero; with $M=1$ the coarse and fine paths coincide and the LHS is $0$, so the statement is still true. Not vacuous; no junk.

### 15. `gbm_mlmc_theorem1_poly_M`

**Rendering.** As #11, but with polynomial payoff $q$ (no smoothness or derivative hypotheses beyond $q$ being a polynomial), $T\ge0$, $m\ge1$, $M\ge2$: $\exists c_4,c_5>0\ \forall\varepsilon\in(0,e^{-1})\ \exists L,N$ ($N_\ell\ge1$ for all $\ell$) with integrable squared error, MSE $<\varepsilon^2$, cost $\sum_{\ell\le L}N_\ell mM^\ell\le c_4\varepsilon^{-2}(\log\varepsilon)^2$, $M^L\le c_5/\varepsilon$, where the target is $\int q(s_0e^{(r-\sigma^2/2)T+\sigma\sqrt Tw})dN(0,1)=\mathbb E q(S_T)$.

**Assessment.** True: Giles Theorem 1 ($\alpha=\beta=\gamma=1$) with bias from #7 and level variances from #14 ($V_\ell\le c\,h_\ell$; level 0 has finite variance). Constant $q$ gives an exact estimator and MSE $0$. Not vacuous ($q=x$). No junk.

### 16. `gbm_mlmc_theorem1_poly`

**Rendering.** As #12 ($M=2$, $m=1$, `emFine`/`emCoarse`, `europeanPayoff (fun x => q.eval x)`) for a polynomial payoff $q$, with cost $\sum_{\ell\le L}N_\ell2^\ell$ and $2^L\le c_5/\varepsilon$.

**Assessment.** True: same as #15 with $M=2$, $m=1$ (bias #6, variance #13). Not vacuous; no junk.
