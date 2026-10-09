# Blind read-back report: packet R55 (ML2R weights, lower bounds, Gaussian instance)

| Field | Value |
|---|---|
| Date | 2026-10-09 |
| Packet (relative to scratchpad) | `readback/round28/packet_R55_ml2r.lean` |
| Declarations audited | 8 in the packet: 7 theorems and 1 definition (`ml2rInstPl`). The 5 definitions appended from other modules (`levelDiff`, `ml2rNode`, `ml2rWeight`, `ml2rEstimator`, `blockMean`) are also rendered. The packet's `section core` is empty, so it shows no helper lemmas. |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round28/work_R55_ml2r/`: `check_weights.py`, `check_weights2.py`, `check_T5i.py`, `check_instance_cost.py` (each with a `.out`); `Scratch_R55.lean` (packet copy plus parse checks) and `Witness_R55.lean` (non-vacuity witness), each with a `.lean.out` |
| Lean | v4.33.1 + Mathlib. `Scratch_R55.lean` elaborates with only the 7 `sorry` warnings, and all its `rfl`/`with_reducible rfl` parse checks pass. `Witness_R55.lean` compiles with no `sorry`. |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `ml2r_sum_weight_mul_div_one_add` | theorem | **true** | no | no |
| 2 | `ml2r_cost_lower` | theorem | **true** | no | no |
| 3 | `ml2r_cost_lower_sqrt` | theorem | **true** | no | no |
| 4 | `ml2r_printed_cost_fails` | theorem | **true** | no | no |
| 5 | `ml2rInstPl` | definition | n/a | n/a | n/a |
| 6 | `ml2r_instance_hypotheses` | theorem | **true** | no (only `0 < α`) | no |
| 7 | `ml2r_instance_cost` | theorem | **true** | no | no |
| 8 | `ml2r_instance_printed_cost_false` | theorem | **true** | no | no |
| A1–A5 | `levelDiff`, `ml2rNode`, `ml2rWeight`, `ml2rEstimator`, `blockMean` | definitions (other modules) | n/a | n/a | Their junk branches ($x/0$ when two nodes coincide, i.e. $\alpha=0$; $0^{-1}\cdot 0$ when $N_\ell=0$) can't be reached under the theorems' hypotheses. |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.** All 7 theorems are true. I give a proof sketch for each, plus numerical evidence: exact rational arithmetic, mpmath at up to 400 digits, and $\log_2(1/\varepsilon)$ up to 25 600 for 5 parameter triples.
2. **Quantifiers are right.** The lower bounds (2, 3, 7B) quantify over every $\varepsilon$, every $L$ and every $N$ with all $N_\ell\ge1$, given MSE $\le\varepsilon^2$. Their constants are fixed before $\varepsilon$: $c_2c_3$ in 2; $c_2c_3 2^{-(\gamma-\beta)\kappa_b}$ and $\kappa_b$ in 3; $c_4,c_5,\kappa$ in 7. The upper bound (7A) chooses $(L,N)$ per $\varepsilon$ with a constant $c_4$ that doesn't depend on $\varepsilon$.
3. **`logb` and `sqrt` arguments are never junk.** $b/\varepsilon>0$ in 2. In 3, $\log_2\varepsilon^{-1}>0$ because $\varepsilon<1$, and $\log_2 b^{-1}\ge0$ because $b\le1$; the $b\le1$ assumption loses nothing, since you can replace $b$ by $\min(b,1)$. In 4 and 8 the argument is $|\log_2\varepsilon|/\alpha\ge0$. In 7, $\varepsilon<e^{-1}$ gives $\log_2\varepsilon^{-1}>\log_2 e>0$ (checked in Lean).
4. **The MSE is a genuine integral.** In 2–4, `hPl` (MemLp 2) and `hω` (measure-preserving) put $Y-EP$ in $L^2(\mu)$, so the integral is not the junk 0. If it were, the lower bounds would be false; for example $L=0$, $N\equiv1$ would violate the cost bound. In 6–8, $Y$ is a finite affine combination of Gaussian coordinates, so $Y^2$ is integrable automatically (7A also asserts it). `Measure.infinitePi` is defined by `if ∀ i, IsProbabilityMeasure … then … else 0`; it takes the genuine branch because `gaussianReal 0 1` is a probability measure (checked in Lean). `variance` is genuine because everything is in $L^2$.
5. **The parses checked in Lean are as intended.** `|∑ ℓ, w ℓ * ∫ Pl ℓ ∂ν - EP|` is $|(\sum_\ell w_\ell\,\mathbb E P_\ell)-EP|$, not $\sum_\ell(w_\ell\mathbb E P_\ell-EP)$; the two differ by $L\cdot EP$. `Real.logb 2 ε⁻¹` is $\log_2(\varepsilon^{-1})$. The `1 / 2` in 3 is the real number $0.5$. `μ[f]` is $\int f\,d\mu$. The appended definitions unfold exactly as displayed.
6. **The "cannot hold" statements (4, 8) negate exactly the natural claim.** The negated claim is: $\exists c,\ \exists\varepsilon_0>0,\ \forall\varepsilon\in(0,\varepsilon_0),\ \exists$ admissible $(L,N)$ with MSE $\le\varepsilon^2$ and cost $\le c\,\varepsilon^{-2}2^{(\gamma-\beta)\sqrt{|\log_2\varepsilon|/\alpha}}$. That is "cost $=O(\cdot)$ as $\varepsilon\to0$". Because the claim uses $\le\varepsilon^2$ rather than $<$, the refutation is the stronger one. The true rate, proved matching from both sides in 3 and 7, has exponent $\sqrt{2\log_2(1/\varepsilon)/\alpha}$, so the "printed" exponent is off by a factor $\sqrt2$. The cost ratio diverges like $2^{(\gamma-\beta)(\sqrt2-1)\sqrt{\log_2(1/\varepsilon)/\alpha}}$; numerically it reaches $2\cdot10^{21}$ to $8\cdot10^{59}$.
7. **Scope and modelling (for the human to check against the paper).** The refutation covers one ML2R family only: nodes $2^{-\alpha\ell}$ (refinement factor 2, coarsest level 0), $\ell=0..L$, Lagrange weights, and $N_\ell\ge1$. Under a different convention, the printed exponent could be correct; for example refiner $M$ with $\log_2M=\tfrac12$, or $\alpha$ defined differently. Whether the source paper uses these conventions has to be checked against it. Also, 2–4 assume *lower* bounds on the bias (for every $L$, in the exact form $b\,2^{-\alpha L(L+1)/2}$), on $V_\ell$ and on $C_\ell$. The link to the paper's upper-bound hypotheses comes only through the instance (theorems 6–8).
8. **Theorem 6(i)** states the bias expansion with remainder $1\cdot x_\ell^{L}$. That is weaker than the truth, $x_\ell^{L+1}/(1+x_\ell)$, but this form is still enough for an ML2R bias $O(2^{-\alpha L(L+1)/2})$, because $\sum_\ell|w_\ell|x_\ell^L=O(2^{-\alpha L(L+1)/2})$. A human should check that it matches the hypothesis of the repo's ML2R upper-bound theorem, which is not in this packet.
9. **Some hypotheses are stronger than needed, harmlessly.** Theorem 1 assumes $0<\alpha$; $\alpha\ne0$ suffices, and I checked $\alpha<0$ numerically. Theorem 3 assumes $0<c_2$, which isn't needed. Theorem 7 assumes $0<\gamma$, which isn't needed. `hPlm` is redundant with MemLp up to a.e. equality. "$N_\ell>0$ for all $\ell\in\mathbb N$" also constrains $\ell>L$, but those values affect neither the estimator nor the cost. For $\beta\le0$ the instance's $P_\ell$ has $\operatorname{Var}P_\ell\to\infty$. That is outside the usual MLMC regime but doesn't affect truth, and the theorems also cover $0<\beta<\gamma$.

## Notation (used below)

- $x_\ell=$ `ml2rNode α ℓ` $=2^{-\alpha\ell}$.
- $w^{(L)}_\ell=$ `ml2rWeight α L ℓ` $=\prod_{k\in\{0..L\}\setminus\{\ell\}}\frac{x_k}{x_k-x_\ell}$.
- $W^{(L)}_\ell=\sum_{k=\ell}^{L}w^{(L)}_k$.
- $\Delta P_0=P_0$ and $\Delta P_\ell=P_\ell-P_{\ell-1}$.
- $V_\ell=\operatorname{Var}_\nu(\Delta P_\ell)$.
- $\operatorname{cost}(L,N)=\sum_{\ell=0}^{L}N_\ell C_\ell$.
- For $\alpha>0$, the weights have the closed form
  $w^{(L)}_\ell=(-1)^{L-\ell}\prod_{j=1}^{\ell}\frac{1}{1-2^{-\alpha j}}\prod_{j=1}^{L-\ell}\frac{2^{-\alpha j}}{1-2^{-\alpha j}}$.
  Hence $w^{(L)}_L=\prod_{j=1}^{L}(1-2^{-\alpha j})^{-1}\ge1$ and $\sup_{L,\ell}|W^{(L)}_\ell|<\infty$. Numerically: $w_L\ge1$ always; $\max|W|\approx3.46$ for $\alpha=1$ and $\approx1.4\cdot10^{11}$ for $\alpha=0.1$.
- **MSE identity.** Under the hypotheses of 2–4, $\mathbb E_\mu[(Y-EP)^2]=\big(\sum_\ell w_\ell\,\mathbb E_\nu P_\ell-EP\big)^2+\sum_{\ell\le L}W_\ell^2V_\ell/N_\ell$. This uses Abel summation, $\sum_\ell W_\ell\,\mathbb E\Delta P_\ell=\sum_\ell w_\ell\,\mathbb E P_\ell$, together with independence and measure preservation.

## A1–A5. Supporting definitions (from other modules)

**Rendering.**
- `levelDiff Pl`: $\Delta P_0=P_0$ and $\Delta P_{\ell+1}=P_{\ell+1}-P_\ell$, pointwise.
- `ml2rNode α ℓ` $=2^{-\alpha\ell}$ (`Real.rpow`, base $2>0$, so always $>0$).
- `ml2rWeight α L ℓ` $=\prod_{k\le L,\,k\ne\ell}\frac{x_k}{x_k-x_\ell}$. This is the Lagrange basis polynomial at $0$, $L_\ell(0)$. In Lean a coincident node gives a factor $x/0=0$, which happens only when $\alpha=0$.
- `blockMean f ω i N x` $=N^{-1}\sum_{n<N}f_i(\omega_{(i,n)}(x))$, which is $0$ when $N=0$.
- `ml2rEstimator α Pl ω L N x` $=\sum_{\ell=0}^{L}\frac1{N_\ell}\sum_{n<N_\ell}W^{(L)}_\ell\,\Delta P_\ell(\omega_{(\ell,n)}(x))$. This is the standard ML2R estimator: independent samples per level, with $P_\ell$ and $P_{\ell-1}$ coupled within a level, and $W_0=1$.

**Assessment.** The `rfl` checks (P3) in `Scratch_R55.lean` confirm that these unfold exactly as displayed. The junk branches are excluded everywhere by $\alpha>0$ and $N_\ell\ge1$.

## 1. `ml2r_sum_weight_mul_div_one_add`

**Rendering.** For real $\alpha>0$ and $L\in\mathbb N$:
$$\sum_{\ell=0}^{L}w^{(L)}_\ell\,\frac{x_\ell}{1+x_\ell}=\prod_{k=0}^{L}\frac{x_k}{1+x_k},\qquad x_k=2^{-\alpha k}.$$

**Assessment.** *True.* The $w_\ell$ are the Lagrange basis values $L_\ell(0)$ for the distinct nodes $x_0,\dots,x_L$, so the left side is $p(0)$, where $p$ interpolates $f(x)=x/(1+x)$. Interpolation error: $f(0)-p(0)=f[x_0,\dots,x_L,0]\prod_k(0-x_k)$. For $g=1/(1+x)$ we have $g[y_0..y_n]=(-1)^n/\prod_i(1+y_i)$ and $f=1-g$. Together these give $p(0)=\prod_k x_k/(1+x_k)$.

- *Numerics* (`check_weights2.out`, `check_weights.out`):
  - Exact rational check for $\alpha\in\{1,2,3,-1,-2\}$, $L\le18$. This also confirms $\sum w=1$, $\sum w x^j=0$ for $1\le j\le L$, $\sum w x^{L+1}=(-1)^L\prod x$, and $w_L\ge1$.
  - 400-digit check for $\alpha\in\{0.1,0.5,1.5,-0.3,-1.7\}$, $L\le25$: relative error $\le5\cdot10^{-220}$.
  - At 80 digits the check showed spurious errors from cancellation (the RHS is about $2^{-650}$). That was a precision artifact; the script now runs at 400 digits.
- *Vacuity:* none ($\alpha=1$, any $L$).
- *Junk:* none. The denominators satisfy $x_k-x_\ell\ne0$ and $1+x_k>0$.
- *Hypothesis:* $0<\alpha$ is stronger than needed ($\alpha\neq0$ suffices). At $\alpha=0$ the identity is false through $x/0=0$: for $L\ge1$ the LHS is $0$ and the RHS is $2^{-(L+1)}$.
- *Standard fact:* Lagrange (Richardson–Romberg) extrapolation to $0$ is exact for polynomials of degree $\le L$; for $x/(1+x)$ the error is the divided-difference formula.

## 2. `ml2r_cost_lower`

**Rendering.**
- *Setting.* $\Omega_0,\Omega$ are measurable spaces, $\mu$ is a probability measure on $\Omega$, and $\nu$ is a measure on $\Omega_0$. The family $\omega_p:\Omega\to\Omega_0$, $p\in\mathbb N\times\mathbb N$, is mutually independent under $\mu$, and each $\omega_p$ is measure-preserving $\mu\to\nu$ (so $\nu$ is a probability measure, the common law). Each $P_\ell:\Omega_0\to\mathbb R$ is measurable and in $L^2(\nu)$.
- *Constants.* Real $EP,\beta,\gamma,c_2$ (any sign), $\alpha>0$, $b>0$, $c_3\ge0$, and $C:\mathbb N\to\mathbb R$.
- *Hypotheses:*
  - (bias) $\forall L$: $b\,2^{-\alpha L(L+1)/2}\le\big|\sum_{\ell\le L}w^{(L)}_\ell\,\mathbb E_\nu P_\ell-EP\big|$;
  - (var) $\forall\ell$: $c_22^{-\beta\ell}\le V_\ell$;
  - (cost) $\forall\ell$: $c_32^{\gamma\ell}\le C_\ell$.
- *Conclusion.* For every $\varepsilon>0$, every $L\in\mathbb N$ and every $N:\mathbb N\to\mathbb N$ with all $N_\ell\ge1$: if $\mathbb E_\mu[(Y_{L,N}-EP)^2]\le\varepsilon^2$, then
  - (a) $\log_2(b/\varepsilon)\le\alpha L(L+1)/2$, and
  - (b) $c_2c_3\,\varepsilon^{-2}2^{(\gamma-\beta)L}\le\operatorname{cost}(L,N)$.

All constants come from the hypotheses, and the lower bound is universal over admissible $(L,N)$, as it should be.

**Assessment.** *True.*
- (a) From the MSE identity, $|\text{bias}_L|\le\varepsilon$; combined with (bias) at $L$ this gives the bound.
- (b) Since $\alpha>0$, $W_L=w_L\ge1$, so $\varepsilon^2\ge W_L^2V_L/N_L\ge c_22^{-\beta L}/N_L$ when $c_2>0$. Then $\operatorname{cost}\ge N_LC_L\ge N_L c_32^{\gamma L}\ge c_2c_3\varepsilon^{-2}2^{(\gamma-\beta)L}$; the other terms are $\ge0$ because $C_\ell\ge c_32^{\gamma\ell}\ge0$. If $c_2\le0$ the left side is $\le0$.
- *Vacuity:* no. The Gaussian instance satisfies every hypothesis: $\Omega_0=\mathbb R$, $\nu=N(0,1)$, $\mu=\bigotimes_{\mathbb N\times\mathbb N}N(0,1)$, $\omega_p=$ coordinate $p$, $P=$ `ml2rInstPl α β`, $EP=0$, $b=e^{-1/(1-2^{-\alpha})}$, $c_2=c_3=1$, $C_\ell=2^{\gamma\ell}$.
  - `hω`, `hind`, `hPlm`, `hPl` are proved in Lean in `Witness_R55.lean`.
  - (bias) and (var) are theorem 6 (iv) and (ii), numerically confirmed.
  - The premise MSE $\le\varepsilon^2$ is attainable. For example $\alpha=\beta=1$, $\gamma=2$, $\varepsilon=2^{-20}$, $L=7$ with the construction of theorem 7 gives MSE$/\varepsilon^2=0.500001$.
- *Junk:* none. $b/\varepsilon>0$. The MSE integral and the variances are genuine because everything is in $L^2$ (main point 4).
- *Hypotheses:* `hPlm` is redundant up to a.e. equality; otherwise nothing unusual.
- *Standard result:* the elementary MLMC/ML2R complexity lower bound. The bias floor forces the depth; the top-level variance forces $N_L\gtrsim\varepsilon^{-2}V_L$.

## 3. `ml2r_cost_lower_sqrt`

**Rendering.** Same setting as 2, plus $\beta\le\gamma$, $0<b\le1$, $c_2>0$ and $c_3>0$. Let $\kappa_b=\tfrac12+\sqrt{2\log_2(1/b)/\alpha}$. For every $\varepsilon\in(0,1)$, every $L$ and every $N$ with all $N_\ell\ge1$ and MSE $\le\varepsilon^2$:
- (a) $\sqrt{2\log_2(1/\varepsilon)/\alpha}-\kappa_b\le L$;
- (b) $c_2c_3\,2^{-(\gamma-\beta)\kappa_b}\;\varepsilon^{-2}\,2^{(\gamma-\beta)\sqrt{2\log_2(1/\varepsilon)/\alpha}}\le\operatorname{cost}(L,N)$.

The constants don't depend on $\varepsilon$, $L$ or $N$.

**Assessment.** *True.*
- (a) Theorem 2(a) gives $L(L+1)\ge A-B$, with $A=2\log_2(1/\varepsilon)/\alpha>0$ and $B=2\log_2(1/b)/\alpha\ge0$. Then $(L+\tfrac12)^2>A-B$ gives $L+\tfrac12\ge\sqrt A-\sqrt B$; this is trivial if $A\le B$.
- (b) Follows from theorem 2(b) and the monotonicity of $2^{(\gamma-\beta)L}$ when $\gamma\ge\beta$.
- *Junk:* both square roots have non-negative arguments, by $\varepsilon<1$ and $b\le1$; the latter loses nothing. The `1 / 2` is real (checked in Lean).
- *Numerics* (`check_instance_cost.out`, 5 triples $(\alpha,\beta,\gamma)$, $t=\log_2(1/\varepsilon)\in[1.44,25600]$):
  - The smallest feasible $L$ always satisfies $L\ge\sqrt{2t/\alpha}-\kappa_b$.
  - The minimum achievable cost (over all $L$ and real $N$, a lower bound for integer $N$) is always $\ge20\times$ the theorem-3 bound.
- *Vacuity:* no. The same instance works with $b=e^{-1/(1-2^{-\alpha})}\le e^{-1}<1$.
- *Hypotheses:* $c_2>0$ is not needed (harmless).
- *Standard result:* the lower half of the ML2R complexity for $\beta<\gamma$ with refiner 2 (Lemaire–Pagès type): $\text{cost}\asymp\varepsilon^{-2}\exp\big(\tfrac{\gamma-\beta}{\sqrt\alpha}\sqrt{2\ln2\,\ln(1/\varepsilon)}\big)=\varepsilon^{-2}2^{(\gamma-\beta)\sqrt{2\log_2(1/\varepsilon)/\alpha}}$.

## 4. `ml2r_printed_cost_fails`

**Rendering.** Same setting as 2, with $\alpha>0$, $\beta<\gamma$, $b>0$, $c_2>0$ and $c_3>0$ (no $b\le1$). Conclusion: there are **no** $c\in\mathbb R$ and $\varepsilon_0>0$ such that, for every $\varepsilon\in(0,\varepsilon_0)$, some $L$ and $N$ (all $N_\ell\ge1$) satisfy
$$\mathbb E_\mu[(Y_{L,N}-EP)^2]\le\varepsilon^2\quad\text{and}\quad\operatorname{cost}(L,N)\le c\,\varepsilon^{-2}2^{(\gamma-\beta)\sqrt{|\log_2\varepsilon|/\alpha}}.$$

**Assessment.** *True.* Apply theorem 3 with $b'=\min(b,1)$ and $\varepsilon<\min(\varepsilon_0,1)$. This gives $K\,2^{(\gamma-\beta)\sqrt2\sqrt{t/\alpha}}\le c\,2^{(\gamma-\beta)\sqrt{t/\alpha}}$ with $K>0$ and $t=|\log_2\varepsilon|\to\infty$. That is impossible because $\gamma>\beta$, and for $c\le0$ it fails at once.
- *Negated claim:* exactly the $O(\cdot)$ achievability claim (main point 6). The negation reads: for every $c$ and $\varepsilon_0$ there is an $\varepsilon<\varepsilon_0$ at which every admissible estimator with MSE $\le\varepsilon^2$ costs more than $c(\cdots)$. That is the right strength.
- *Numerics:* the ratio of the minimum achievable cost to the printed bound grows from about 8 to $2\cdot10^{21}$ ($\alpha=\beta=1,\gamma=2$) and to $7.7\cdot10^{59}$ ($\alpha=0.5,\beta=1,\gamma=3$).
- *Junk:* none. $|\log_2\varepsilon|\ge0$, and the integral is genuine as in 2. If it were junk 0, the negated claim would be easier and the refutation harder, but that doesn't happen.
- *Vacuity:* no. The instance satisfies all hypotheses, and for it the inner premise is attainable for every $\varepsilon$ (theorem 7A).
- *Scope:* see main point 7.

## 5. `ml2rInstPl` (definition)

**Rendering.** $P_\ell(z)=\dfrac{x_\ell}{1+x_\ell}+\Big(\sum_{j=0}^{\ell}2^{-\beta j/2}\Big)z$ for $z\in\mathbb R$; the exponent parses as $(-(\beta j))/2$ (checked in Lean). Under $z\sim N(0,1)$:
- $\mathbb E P_\ell=x_\ell/(1+x_\ell)\to0$, so $EP=0$ is the genuine limit;
- $\Delta P_\ell=\text{const}+2^{-\beta\ell/2}z$, so $V_\ell=2^{-\beta\ell}$ (and $V_0=1$).

For $\beta\le0$, $\operatorname{Var}P_\ell\to\infty$ (main point 9).

## 6. `ml2r_instance_hypotheses`

**Rendering.** For $\alpha>0$ and $\beta\in\mathbb R$, with $\mathbb E$ and Var under $N(0,1)$:
- (i) $\forall L,\ \forall\ell\le L$: $\big|\mathbb E P_\ell-0-\sum_{n=1}^{L}(-1)^{n+1}x_\ell^n\big|\le1\cdot x_\ell^{L}$;
- (ii) $\forall\ell$: $\operatorname{Var}(\Delta P_\ell)=2^{-\beta\ell}$;
- (iii) $\forall L$: $\sum_{\ell\le L}w^{(L)}_\ell\,\mathbb E P_\ell-0=\prod_{k\le L}\frac{x_k}{1+x_k}$;
- (iv) $\forall L$: $e^{-1/(1-2^{-\alpha})}2^{-\alpha L(L+1)/2}\le|\text{bias}_L|\le2^{-\alpha L(L+1)/2}$.

The groupings `|∫… - 0 - ∑…|` and `(∑ … * ∫ …) - 0` were confirmed in Lean.

**Assessment.** *True.*
- (i) The remainder is $(-1)^Lx^{L+1}/(1+x)$, with absolute value $\le x^L$; the worst ratio, found at $\ell=0$ ($x=1$), is $0.5$ (`check_T5i.out`, adaptive precision).
- (ii) Direct computation.
- (iii) Theorem 1 plus $\int(a+bz)\,dN(0,1)=a$.
- (iv) $1\le\prod_k(1+x_k)\le e^{\sum_k x_k}\le e^{1/(1-2^{-\alpha})}$.
- *Numerics:* all four parts are confirmed numerically for $L\le60$ and $L<40$ respectively, and for 5 values of $\alpha$. An earlier 50-digit run reported a spurious "False" for (i), caused by cancellation; the fixed script reports True.
- *Junk:* none. The integrals and variances are of affine functions of a Gaussian, and $1-2^{-\alpha}>0$.
- *Vacuity:* not applicable.
- *Note:* (i) is weaker than the truth (main point 8). Parts (i) and (ii) are paper-style upper-bound hypotheses with constants 1. Part (iv) is the `hbias` of 2–4 with $b=e^{-1/(1-2^{-\alpha})}$.

## 7. `ml2r_instance_cost`

**Rendering.** For $\alpha>0$, $\gamma>0$ and $\beta<\gamma$, there exist $c_4>0$, $c_5>0$ and $\kappa\in\mathbb R$ (chosen before $\varepsilon$) such that the following holds for every $\varepsilon\in(0,e^{-1})$. Here $\mu=\bigotimes_{\mathbb N\times\mathbb N}N(0,1)$, $\omega_p(x)=x_p$, $Y=$ ML2R estimator of the instance, and $s=\sqrt{2\log_2(1/\varepsilon)/\alpha}$.
- **(A)** Some $(L,N)$ with all $N_\ell\ge1$ has $Y^2\in L^1(\mu)$, $\int Y^2\,d\mu<\varepsilon^2$, and $\sum_{\ell\le L}N_\ell2^{\gamma\ell}\le c_4\varepsilon^{-2}2^{(\gamma-\beta)s}$.
- **(B)** Every $(L,N)$ with all $N_\ell\ge1$ and $\int Y^2\,d\mu\le\varepsilon^2$ satisfies $L\ge s-\kappa$ and $\sum_{\ell\le L}N_\ell2^{\gamma\ell}\ge c_5\varepsilon^{-2}2^{(\gamma-\beta)s}$.

Since $EP=0$, $\int Y^2\,d\mu$ is the MSE.

**Assessment.** *True.*
- (B) is theorem 3 applied to the instance, with $\kappa=\kappa_b$ and $c_5=2^{-(\gamma-\beta)\kappa_b}$.
- (A): take $L=\lceil s\rceil$.
  - Bias: $\le\tfrac12\,2^{-\alpha L(L+1)/2}\le\tfrac12\varepsilon\,2^{-\alpha s/2}<\varepsilon/2$.
  - Samples: $N_\ell=\lceil2\varepsilon^{-2}S|W_\ell|\sqrt{V_\ell/C_\ell}\rceil$ with $S=\sum_\ell|W_\ell|\sqrt{V_\ell C_\ell}$. This gives variance $\le\varepsilon^2/2$.
  - Cost: $\le2\varepsilon^{-2}S^2+\sum_{\ell\le L}2^{\gamma\ell}$. Here $S\lesssim\sup|W|\cdot2^{(\gamma-\beta)L/2}$, $L\le s+1$, and the rounding-term ratio $2^{\gamma}2^{\beta s}\varepsilon^2=2^{\gamma+\beta s-\alpha s^2}$ is bounded.
- *Numerics:*
  - The construction gives MSE$/\varepsilon^2\approx0.5$, and cost$/(\varepsilon^{-2}2^{(\gamma-\beta)s})$ stays bounded: between about 15 and 175 for four of the triples, and up to about $1.9\cdot10^4$ for $\alpha=0.5,\beta=1,\gamma=3$.
  - The minimum achievable cost divided by $\varepsilon^{-2}2^{(\gamma-\beta)s}$ stays between about $2.88$ and $2.86\cdot10^{3}$.
  - Both hold for every $t\in[1.44,25600]$.
- *Junk:* none.
  - $\log_2\varepsilon^{-1}>0$ (checked in Lean).
  - The integrals are genuine: in (A) integrability is asserted; in (B) it is automatic.
  - `infinitePi` is the genuine product measure (checked in Lean).
- *Hypotheses:* $\gamma>0$ is not needed (harmless).
- *Standard result:* the two-sided ($\Theta$) ML2R complexity for $\beta<\gamma$ on an explicit example.

## 8. `ml2r_instance_printed_cost_false`

**Rendering.** For $\alpha>0$ and $\beta<\gamma$ (no sign condition on $\gamma$), there are no $c\in\mathbb R$ and $\varepsilon_0>0$ such that, for every $\varepsilon\in(0,\varepsilon_0)$, some $(L,N)$ with all $N_\ell\ge1$ has
$$\int Y^2\,d\mu\le\varepsilon^2\quad\text{and}\quad\sum_{\ell\le L}N_\ell2^{\gamma\ell}\le c\,\varepsilon^{-2}2^{(\gamma-\beta)\sqrt{|\log_2\varepsilon|/\alpha}}$$
(same instance and $\mu$ as in 7).

**Assessment.** *True.* It is theorem 4 applied to the instance. The hypotheses hold: the Lean witness, theorem 6 (ii) and (iv), and $C_\ell=2^{\gamma\ell}$ with $c_3=1$. Also $\int Y^2=\int(Y-0)^2$.
- *Junk:* none. $Y^2$ is always integrable, so no junk 0 makes the negated existential easier, and $|\log_2\varepsilon|\ge0$.
- *Numerics:* as for 4.
- *Vacuity:* not applicable; the hypotheses $\alpha>0$, $\beta<\gamma$ are satisfiable.
- *Standard result:* the refutation of the printed rate (exponent missing $\sqrt2$) on a concrete instance.
