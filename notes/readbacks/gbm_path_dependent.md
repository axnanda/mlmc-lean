# Blind read-back R14: GBM path-dependent MLMC (EM and Milstein, discrete monitoring)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round17/packet_R14_gbmpath.lean` |
| declarations audited | 49: 32 theorems, 6 local definitions, 11 appended definitions |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round17/work_R14/` (`s1_strong_consts.py`, `s2_coupling.py`, `s3_level_variance_mc.py`, `s4_giles_alloc.py`, `s5_random_search.py`, each with a `.out`; `Elab.lean`/`Elab.out` is a scratch elaboration check) |

## Notation used below

All quantities are real unless stated. $m, j, k, n \in \mathbb N$, and every cast $\mathbb N \to \mathbb R$ sits at the leaves, which `Elab.out` confirms (for example `T / (↑m * (2:ℝ) ^ j)`). Write
$h_j := T/(m\,2^j)$ (Lean: $=0$ when $m=0$, because $x/0=0$), $t_k := kT/m$, and $q := |r|+\sigma^2$. Further, $\mathbb P :=$ `stdNormalSeq` $=\bigotimes_{i\in\mathbb N} N(0,1)$ on $\mathbb R^{\mathbb N}$, and $\mathbb E$ is the expectation under it.
$C_{EM}(t) :=$ `gbmStrongConst r σ t s₀` $= s_0^2 e^{(2|r|+\sigma^2)t}\,q\,(5qt+4)$ and
$C_{Mil}(t) :=$ `gbmMilStrongConst r σ t s₀` $= s_0^2 e^{(2|r|+\sigma^2)t}\,q^2(30q^2t^2+16qt+4)$.
$X^{ex}_j, X^{EM}_j, X^{Mil}_j : \mathbb R^{\mathbb N}\to\mathbb R^{\mathbb N}$ are the monitored paths `gbmMonExact/EM/Mil r σ T s₀ m j`.

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `gbmMonExact_pairAvg` | theorem | true | no | no (also holds in the degenerate cases $m=0$ and $T<0$) |
| 2 | `gbm_em_monitored_mse_le` | theorem | true | no | no ($m=0$ is trivial, but not because of a junk value) |
| 3 | `gbm_em_monitored_bias_le` | theorem | true | no | no |
| 4 | `gbm_em_monitored_variance_le` | theorem | true | no | no (the function is in $L^2$, so `variance` is genuine) |
| 5 | `gbm_em_monitored_theorem1` | theorem | true | no | no (the integrand is integrable) |
| 6 | `gbm_mil_monitored_mse_le` | theorem | true | no | no |
| 7 | `gbm_mil_monitored_bias_le` | theorem | true | no | no |
| 8 | `gbm_mil_monitored_variance_le` | theorem | true | no | no |
| 9 | `gbm_mil_monitored_theorem1` | theorem | true | no | no |
| 10 | `asianPayoff_sq_sub_le` | theorem | true | no | no |
| 11 | `lookbackPayoff_sq_sub_le` | theorem | true | no | no |
| 12 | `floatLookbackPayoff_sq_sub_le` | theorem | true (the constant 4 is loose; 2 suffices) | no | no |
| 13 | `gbm_em_asian_mse_le` | theorem | true | no | no |
| 14 | `gbm_em_asian_bias_le` | theorem | true | no | no |
| 15 | `gbm_em_asian_variance_le` | theorem | true | no | no |
| 16 | `gbm_em_asian_theorem1` | theorem | true | no | no |
| 17 | `gbm_mil_asian_mse_le` | theorem | true | no | no |
| 18 | `gbm_mil_asian_bias_le` | theorem | true | no | no |
| 19 | `gbm_mil_asian_variance_le` | theorem | true | no | no |
| 20 | `gbm_mil_asian_theorem1` | theorem | true | no | no |
| 21 | `gbm_em_lookback_mse_le` | theorem | true | no | no |
| 22 | `gbm_em_lookback_bias_le` | theorem | true | no | no |
| 23 | `gbm_em_lookback_variance_le` | theorem | true | no | no |
| 24 | `gbm_em_lookback_theorem1` | theorem | true | no | no |
| 25 | `gbm_mil_lookback_mse_le` | theorem | true | no | no |
| 26 | `gbm_mil_lookback_bias_le` | theorem | true | no | no |
| 27 | `gbm_mil_lookback_variance_le` | theorem | true | no | no |
| 28 | `gbm_mil_lookback_theorem1` | theorem | true | no | no |
| 29 | `gbm_em_floatLookback_variance_le` | theorem | true | no | no |
| 30 | `gbm_em_floatLookback_theorem1` | theorem | true | no | no |
| 31 | `gbm_mil_floatLookback_variance_le` | theorem | true | no | no |
| 32 | `gbm_mil_floatLookback_theorem1` | theorem | true | no | no |
| D1–D6 | `gbmMonExact`, `gbmMonEM`, `gbmMonMil`, `asianPayoff`, `lookbackPayoff`, `floatLookbackPayoff` | def | faithful | – | the only junk is $h_j=T/0=0$ when $m=0$, and it does not matter |
| D7–D17 | `blockMean`, `fineCoarseDiff`, `emPath`, `pairAvg`, `stdNormalSeq`, `gbmDrift`, `gbmVol`, `gbmStrongConst`, `milsteinPath`, `gbmMilStrongConst`, `milsteinStep` | def (appended) | faithful | – | – |

## Main points for a human auditor

1. **I found no false, vacuous or junk-dependent statement.** All 32 theorems are true. Each has a non-degenerate instance satisfying its hypotheses, for example
   $r=0.05,\ \sigma=0.5,\ s_0=1,\ T=1,\ m=4,\ g(x)=(x-1)^+,\ K=1,\ \Phi(a)=g(a_4),\ c=1$.
2. **Coupling laws are right.** The coarse level $j$ inside the level-$(j+1)$ correction is driven by `pairAvg z`, where $(\text{pairAvg}\,z)_k=(z_{2k}+z_{2k+1})/\sqrt2$:
   - `pairAvg` pushes $\mathbb P$ forward to $\mathbb P$, because the pairs are disjoint (checked by Monte Carlo in `s2`).
   - The coarse Brownian increment $\sqrt{h_j}\,(\text{pairAvg}\,z)_k$ equals $\sqrt{h_{j+1}}(z_{2k}+z_{2k+1})$, the sum of the two fine increments.
   - Fine index $k2^{j+1}$ and coarse index $k2^j$ both correspond to $t_k$.
   - Theorem 1 states $X^{ex}_j\circ\text{pairAvg}=X^{ex}_{j+1}$ pathwise. It holds for all inputs (error $\le 10^{-37}$ in `s2`) and gives the telescoping identity and the $j$-independence of the exact monitored law.
3. **The strong constants are valid with margin** (`s1`, `s5`, exact closed forms checked against Monte Carlo).
   - Over a grid and 60,000 random parameter draws: $\sup \text{MSE}_{EM}(t_n)/(C_{EM}(t_n)h)\approx0.098$, which tends to the analytic $1/10$ at $r=0$, and $\sup\text{MSE}_{Mil}/(C_{Mil}h^2)\approx0.0082$.
   - The ratios converge as $h\to0$, which confirms the rates: strong order ½ for EM (MSE $\propto h$) and strong order 1 for Milstein (MSE $\propto h^2$).
   - When $qh\ge1$ the bounds hold trivially, because $\mathbb E S_n^2\le s_0^2e^{(2|r|+\sigma^2)t}$ for both schemes.
   - The Monte Carlo level variances (`s3`) halve per level for EM and quarter per level for Milstein. They sit 3 to 5 orders of magnitude below the stated bounds.
4. **No `variance` or integral is applied to a non-integrable function.**
   - `hΦ` forces $c\ge0$, and it makes $\Phi$ depend only on $a_0,\dots,a_m$, $\sqrt c$-Lipschitz in them. So $\Phi$ is continuous, hence measurable, and has linear growth.
   - `hg` forces $K\ge0$ and $g$ Lipschitz.
   - EM and Milstein path values are polynomials in Gaussians, and exact values are lognormal, so every integrand is in $L^1$ and every `variance` argument is in $L^2$. None of the bounds is rescued by `variance = 0` or `∫ = 0`.
5. **The $m=0$ case.** The theorems without `hm` are trivially true at $m=0$: the right-hand side carries a factor $m=0$, and the left-hand side is 0. This is not junk-dependent. `hΦ` with $m=0$ forces $\Phi$ to depend only on $a_0$, and coordinate 0 of every path is $s_0$ (index $0\cdot2^j=0$), whatever $h_j=T/0=0$ is. All Theorem-1 statements assume $0<m$. The `hm` hypotheses in the Asian mse/bias/variance lemmas and in `asianPayoff_sq_sub_le` are unnecessary but harmless.
6. **Quantifier order in the Theorem-1 statements is the standard one.**
   - The form is $\exists c_4>0\ \forall\varepsilon\in(0,e^{-1})\ \exists L,N\ (\forall j,\ N_j\ge1)\wedge \text{MSE}<\varepsilon^2\wedge\text{cost}\le\ldots$.
   - $c_4$ is chosen before $\varepsilon$. It may depend on $r,\sigma,s_0,T,m$ and on $\Phi,c$ (or $g,K$), for example through $\operatorname{Var}\Phi(X^{EM}_0)$; this is the usual dependence in Giles's Theorem 1. $L$ and $N$ depend on $\varepsilon$.
   - The MSE is a genuine integral over independent sample blocks $x_{(j,n)}\sim\mathbb P$, and the target is $\mathbb E\,\Phi(X^{ex}_0)$, the exact discretely monitored price.
   - The rates are as in Giles: EM with $\beta=\gamma=1$ gives $\varepsilon^{-2}(\log\varepsilon)^2$; Milstein with $\beta=2>\gamma=1$ gives $\varepsilon^{-2}$. The allocation illustration in `s4` shows the cost ratio staying bounded (EM about $10^3$ times $\varepsilon^{-2}\log^2\varepsilon$; Milstein about 190 times $\varepsilon^{-2}$, down to $\varepsilon=3\cdot10^{-12}$).
7. **Minor modelling remarks (not defects).**
   - The cost counts only the $m2^j$ fine steps per level-$j$ sample. The coarse path adds a factor of at most 1.5.
   - The bias bounds come only from the strong error. For EM this is $O(h^{1/2})$, weaker than the classical weak order 1, but it is enough for $\alpha\ge\frac12\min(\beta,\gamma)$.
   - `hT : 0 ≤ T` is genuinely needed. With $T<0$ the square root is 0 but the drift factor $(1+rh)$ is not, so the left-hand side is positive while the right-hand side is negative.

---

## Definitions

### D1 `gbmMonExact r σ T s₀ m j z k`
**Rendering.** $s_0\exp\big((r-\sigma^2/2)\,k\,(T/m)+\sigma\sqrt{h_j}\sum_{i<k2^j}z_i\big)$.
For $m>0$ and $T\ge0$, $\sqrt{h_j}\sum_{i<k2^j}z_i$ is $W(t_k)$ built from the level-$j$ fine increments $\sqrt{h_j}z_i$, so this is exact GBM at the monitoring date $t_k$, coupled to level $j$.
At $m=0$: $T/0=0$, so the value is $\equiv s_0$ (confirmed in Lean, `Elab.lean`).

### D2 `gbmMonEM r σ T s₀ m j z k`
**Rendering.** Euler–Maruyama for $dS=rS\,dt+\sigma S\,dW$ with step $h_j$ and increments $\sqrt{h_j}z_i$, evaluated at step $k2^j$ (time $t_k$): $S_{i+1}=S_i(1+rh_j+\sigma\sqrt{h_j}z_i)$, $S_0=s_0$.

### D3 `gbmMonMil r σ T s₀ m j z k`
**Rendering.** Milstein with $a(S)=rS$, $b(S)=\sigma S$ and $b'(S)=\sigma$ (Lean `deriv (fun S => σ*S) S = σ`, checked by `simp` in `Elab.lean`):
$S_{i+1}=S_i\big(1+rh+\sigma\Delta W_i+\tfrac{\sigma^2}{2}(\Delta W_i^2-h)\big)$, with $\Delta W_i=\sqrt{h_j}z_i$, evaluated at step $k2^j$.

### D4 `asianPayoff g m S`
**Rendering.** $g\big(\frac1m\sum_{k=1}^{m}S_k\big)$, the arithmetic average over $t_1,\dots,t_m$, excluding $S_0$. At $m=0$ it is $g(0)$.

### D5 `lookbackPayoff g m S`
**Rendering.** $g(\max_{0\le k\le m}S_k)$.

### D6 `floatLookbackPayoff g m S`
**Rendering.** $g(S_m-\min_{0\le k\le m}S_k)$.

### D7–D17 (appended)
- `blockMean f ω i N x` $=N^{-1}\sum_{n<N}f_i(\omega_{(i,n)}(x))$. Here $\omega_p(x)=x_p$, so level $i$ uses the samples $x_{(i,0)},\dots,x_{(i,N-1)}$. For $N=0$ the value is 0, but every Theorem 1 requires $N_j>0$.
- `fineCoarseDiff Pf Pc` gives $Y_0=P^f_0$ and $Y_{\ell+1}=P^f_{\ell+1}-P^c_\ell$.
- `emPath a b h S₀ z` is the generic EM recursion with time argument $ih$.
- `pairAvg` is $(z_{2k}+z_{2k+1})/\sqrt2$.
- `stdNormalSeq` is the i.i.d. $N(0,1)$ product measure; `gaussianReal 0 1` has variance parameter 1.
- `gbmDrift r` $=rS$ and `gbmVol σ` $=\sigma S$.
- `gbmStrongConst` and `gbmMilStrongConst` are $C_{EM}$ and $C_{Mil}$ above.
- `milsteinPath` and `milsteinStep` are the generic Milstein scheme $S+a h+b\,\Delta W+\frac12 b b'(\Delta W^2-h)$.

---

## Theorems

### 1. `gbmMonExact_pairAvg`
**Rendering.** For all $r,\sigma,T,s_0\in\mathbb R$, $m,j\in\mathbb N$ and $z$: $X^{ex}_j(\text{pairAvg}\,z)=X^{ex}_{j+1}(z)$ as functions of $k$.

**Assessment.** True.
$\sqrt{h_j}\sum_{i<k2^j}(z_{2i}+z_{2i+1})/\sqrt2=\sqrt{h_j/2}\sum_{i<k2^{j+1}}z_i=\sqrt{h_{j+1}}\sum_{i<k2^{j+1}}z_i$, and the drift term does not depend on $j$.
It also holds when $h_j\le0$ (both square roots are 0) and when $m=0$. Numerically the maximum difference is $1.5\times10^{-38}$ over 200 random trials, including $m=0$ and $T<0$ (`s2.out`).
No hypotheses, so the statement cannot be vacuous. It is the standard MLMC coupling identity: each coarse Brownian increment is the sum of two fine increments.

### 2. `gbm_em_monitored_mse_le`
**Rendering.** Let $T\ge0$ and $m\in\mathbb N$, and let $\Phi:\mathbb R^{\mathbb N}\to\mathbb R$ and $c$ satisfy $(\Phi a-\Phi b)^2\le c\sum_{k=0}^m(a_k-b_k)^2$ for all $a,b$. Then for every $j$:
$\mathbb E[(\Phi(X^{ex}_j)-\Phi(X^{EM}_j))^2]\le c\,m\,C_{EM}(T)\,h_j$.

**Assessment.** True.
- The left-hand side is at most $c\sum_{k=1}^m\mathbb E|S(t_k)-S^{EM}_{k2^j}|^2$; the $k=0$ term vanishes.
- Each term is at most $C_{EM}(t_k)h_j\le C_{EM}(T)h_j$, because $C_{EM}$ is increasing in $t$.
- I verified the per-time bound from the exact closed form $\text{MSE}=s_0^2[e^{(2r+\sigma^2)t}+((1+rh)^2+\sigma^2h)^n-2(e^{rh}(1+rh+\sigma^2h))^n]$ (Monte Carlo agrees, `s1`). The worst ratio is about 0.098 (`s1`, `s5`).
- The integrand is integrable, so the bound is genuine.
- Non-vacuous: e.g. $\Phi(a)=a_m$, $c=1$.
- $m=0$: both sides are 0, and this does not rely on a junk value (point 5).

This is the standard result that EM has strong order ½ for GBM, transferred to a Lipschitz functional of the discretely monitored path.

### 3. `gbm_em_monitored_bias_le`
**Rendering.** Same hypotheses. $\big|\mathbb E[\Phi(X^{EM}_j)-\Phi(X^{ex}_0)]\big|\le\sqrt{c\,m\,C_{EM}(T)h_j}$.

**Assessment.** True.
- Both terms are integrable, so the left-hand side is $|\mathbb E\Phi(X^{EM}_j)-\mathbb E\Phi(X^{ex}_0)|$.
- $X^{ex}_0\circ\text{pairAvg}^j=X^{ex}_j$ and pairAvg preserves $\mathbb P$, so $\mathbb E\Phi(X^{ex}_0)=\mathbb E\Phi(X^{ex}_j)$.
- Jensen and statement 2 then give the bound.

This is the weak error bounded by the strong error, giving $\alpha=\frac12$. It is weaker than the classical weak order 1, but sufficient for Theorem 1.

### 4. `gbm_em_monitored_variance_le`
**Rendering.** Same hypotheses. $\operatorname{Var}\big(\Phi(X^{EM}_{j+1}(z))-\Phi(X^{EM}_j(\text{pairAvg}\,z))\big)\le 6\,c\,m\,C_{EM}(T)\,h_{j+1}$.

**Assessment.** True.
- $\operatorname{Var}\le\mathbb E[D^2]\le2\mathbb E[(\Phi X^{EM}_{j+1}-\Phi X^{ex}_{j+1})^2]+2\mathbb E[(\Phi X^{ex}_j(\text{pairAvg}\,z)-\Phi X^{EM}_j(\text{pairAvg}\,z))^2]$, using statement 1.
- The second expectation equals the level-$j$ MSE by measure preservation.
- So the total is at most $2cmCh_{j+1}+2cmC(2h_{j+1})=6cmCh_{j+1}$.
- $D\in L^2$, so `variance` is the genuine variance.
- Monte Carlo (`s3`): the variance halves per level and the ratio to the bound is between $4\times10^{-5}$ and $10^{-3}$.

This is the MLMC level-variance bound with $\beta=1$.

### 5. `gbm_em_monitored_theorem1`
**Rendering.** Assume $T\ge0$, $0<m$ and `hΦ`. Then there is $c_4>0$, depending only on $(r,\sigma,s_0,T,m,\Phi,c)$, such that for every $\varepsilon\in(0,e^{-1})$ there are $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N_{\ge1}$ with:
- $\mathbb E_{x\sim\mathbb P^{\otimes(\mathbb N\times\mathbb N)}}\Big[\big(\sum_{j=0}^L N_j^{-1}\sum_{n<N_j}Y_j(x_{(j,n)})-\mathbb E\Phi(X^{ex}_0)\big)^2\Big]<\varepsilon^2$, where $Y_0=\Phi(X^{EM}_0)$ and $Y_j=\Phi(X^{EM}_j(z))-\Phi(X^{EM}_{j-1}(\text{pairAvg}\,z))$;
- $\sum_{j=0}^L N_j\,m2^j\le c_4\,\varepsilon^{-2}(\log\varepsilon)^2$.

**Assessment.** True.
- The MSE equals $\text{bias}^2+\sum_j V_j/N_j$, with telescoping mean $\mathbb E\Phi(X^{EM}_L)$.
- Statement 3 gives $\text{bias}^2\le cmCh_L$.
- Statement 4 bounds $V_j$ for $j\ge1$, and $V_0<\infty$.
- Giles's Theorem 1 with $\alpha=\frac12$, $\beta=\gamma=1$ gives $\varepsilon^{-2}\log^2\varepsilon$; see the `s4` illustration.
- The quantifier order is correct: $c_4$ before $\varepsilon$.
- The integrand is integrable for every $L,N$, so "$<\varepsilon^2$" cannot be met through `∫ = 0`.
- Non-vacuous (instance in point 1).
- The cost omits the coarse-path steps, a factor of at most 1.5.

### 6. `gbm_mil_monitored_mse_le`
**Rendering.** As in statement 2 with Milstein: $\mathbb E[(\Phi X^{ex}_j-\Phi X^{Mil}_j)^2]\le c\,m\,C_{Mil}(T)\,h_j^2$.

**Assessment.** True.
- The exact closed form is $\text{MSE}=s_0^2\big[e^{(2r+\sigma^2)t}+\big((1+rh)^2+\sigma^2h+\tfrac{\sigma^4h^2}{2}\big)^n-2\big(e^{rh}(1+rh+\sigma^2h+\tfrac{\sigma^4h^2}{2})\big)^n\big]$: the second term is $\mathbb E S_n^2/s_0^2$ and the third is the cross term.
- Monte Carlo confirms the closed form, and the worst ratio to $C_{Mil}h^2$ is 0.0082 (`s1`, `s5`).
- MSE$/h^2$ converges as $h\to0$ (strong order 1).

This is Milstein's strong order 1 for GBM.

### 7. `gbm_mil_monitored_bias_le`
**Rendering.** $|\mathbb E[\Phi X^{Mil}_j-\Phi X^{ex}_0]|\le\sqrt{c\,m\,C_{Mil}(T)}\;h_j$.

**Assessment.** True, as in statement 3, using $\sqrt{h_j^2}=h_j$ since $h_j\ge0$. This gives $\alpha=1$.

### 8. `gbm_mil_monitored_variance_le`
**Rendering.** $\operatorname{Var}(\Phi X^{Mil}_{j+1}(z)-\Phi X^{Mil}_j(\text{pairAvg}\,z))\le10\,c\,m\,C_{Mil}(T)\,h_{j+1}^2$.

**Assessment.** True: $2h_{j+1}^2+2(2h_{j+1})^2=10h_{j+1}^2$. In Monte Carlo the variance quarters per level, with ratios of about $10^{-4}$ to $2\times10^{-5}$. This is $\beta=2$.

### 9. `gbm_mil_monitored_theorem1`
**Rendering.** As in statement 5 with Milstein levels, and cost $\le c_4\varepsilon^{-2}$.

**Assessment.** True: Giles's Theorem 1 with $\alpha=1$, $\beta=2>\gamma=1$. The quantifier order is correct and the integrand is integrable. In `s4` the cost$\cdot\varepsilon^2$ ratio levels off at about 190.

### 10. `asianPayoff_sq_sub_le`
**Rendering.** If $|g(x)-g(y)|\le K|x-y|$ for all $x,y$ and $0<m$, then for all $a,b$:
$(g(\bar a)-g(\bar b))^2\le\frac{K^2}{m}\sum_{k=0}^m(a_k-b_k)^2$, where $\bar a=\frac1m\sum_{k=1}^m a_k$.

**Assessment.** True by Lipschitz continuity and Cauchy–Schwarz: $(\frac1m\sum d_k)^2\le\frac1m\sum d_k^2$.
- `hg` forces $K\ge0$.
- `hm` is unnecessary: at $m=0$ both sides are 0.

This is the Lipschitz constant of the arithmetic-Asian payoff in $\ell^2$.

### 11. `lookbackPayoff_sq_sub_le`
**Rendering.** For all $m,a,b$: $(g(\max_{k\le m}a_k)-g(\max_{k\le m}b_k))^2\le K^2\sum_{k\le m}(a_k-b_k)^2$.

**Assessment.** True, since $|\max a-\max b|\le\max_k|a_k-b_k|\le\|a-b\|_2$.

### 12. `floatLookbackPayoff_sq_sub_le`
**Rendering.** $(g(a_m-\min a)-g(b_m-\min b))^2\le4K^2\sum_{k\le m}(a_k-b_k)^2$.

**Assessment.** True: $(|a_m-b_m|+|\min a-\min b|)^2\le2\|a-b\|^2+2\|a-b\|^2$. The constant 4 is loose; 2 also works. With $d=a-b$, the difference is $d_m-\delta$ for some $\delta\in[\min d,\max d]$, so its absolute value is at most $\max d-\min d\le|d_i|+|d_l|$ with $i\ne l$. Loose is still valid.

### 13–16. `gbm_em_asian_{mse,bias,variance,theorem1}`
**Rendering.** Assume $T\ge0$, $0<m$ and `hg`. Statements 2–5 then hold for $\Phi=$ `asianPayoff g m` with $c=K^2/m$:
- MSE $\le K^2C_{EM}(T)h_j$;
- bias $\le K\sqrt{C_{EM}(T)h_j}$;
- level variance $\le6K^2C_{EM}(T)h_{j+1}$;
- complexity $\varepsilon^{-2}\log^2\varepsilon$, with $c_4$ chosen before $\varepsilon$.

**Assessment.** All true. They follow from statement 10 together with statements 2–5, where $c\,m=K^2$; $K\ge0$ gives $\sqrt{K^2C}=K\sqrt C$. Monte Carlo (`s3`, Asian rows) is consistent, with the bound ratio at most $10^{-3}$. Non-vacuous: $g=(x-1)^+$, $K=1$.

### 17–20. `gbm_mil_asian_{mse,bias,variance,theorem1}`
**Rendering / Assessment.** As 13–16 with Milstein:
- MSE $\le K^2C_{Mil}h_j^2$;
- bias $\le K\sqrt{C_{Mil}}\,h_j$;
- variance $\le10K^2C_{Mil}h_{j+1}^2$;
- cost $\le c_4\varepsilon^{-2}$.

All true, by statement 10 with statements 6–9.

### 21–24. `gbm_em_lookback_{mse,bias,variance,theorem1}`
**Rendering.** $\Phi=$ `lookbackPayoff g m`, $c=K^2$:
- MSE $\le K^2mC_{EM}h_j$;
- bias $\le K\sqrt{mC_{EM}h_j}$;
- variance $\le6K^2mC_{EM}h_{j+1}$;
- Theorem 1 with $0<m$, cost $\varepsilon^{-2}\log^2\varepsilon$.

There is no `hm` in mse/bias/variance.

**Assessment.** True, by statement 11 with statements 2–5. At $m=0$ the payoff depends only on $S_0=s_0$, so both sides are 0. Monte Carlo is consistent.

### 25–28. `gbm_mil_lookback_{mse,bias,variance,theorem1}`
**Rendering / Assessment.** As 21–24 with Milstein:
- MSE $\le K^2mC_{Mil}h_j^2$;
- bias $\le K\sqrt{mC_{Mil}}\,h_j$;
- variance $\le10K^2mC_{Mil}h_{j+1}^2$;
- cost $\le c_4\varepsilon^{-2}$.

All true.

### 29–30. `gbm_em_floatLookback_{variance,theorem1}`
**Rendering.** $\Phi=$ `floatLookbackPayoff g m`, $c=4K^2$: variance $\le24K^2mC_{EM}h_{j+1}$, which is $6\cdot4$; Theorem 1 with $0<m$, cost $\varepsilon^{-2}\log^2\varepsilon$.

**Assessment.** True, by statement 12 with statements 4–5. Monte Carlo ratio is about $5\times10^{-5}$.

### 31–32. `gbm_mil_floatLookback_{variance,theorem1}`
**Rendering / Assessment.** Variance $\le40K^2mC_{Mil}h_{j+1}^2$, which is $10\cdot4$; Theorem 1 with cost $\le c_4\varepsilon^{-2}$. True.
