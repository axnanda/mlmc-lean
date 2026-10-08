# Blind read-back report: packet R41 (Gaussian change of measure / likelihood ratios)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round23/packet_R41_com.lean` |
| declarations audited | 5 (5 theorems) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round23/work_R41_com/` (`check_lr_second_moment.py` / `.out`; elaboration check `scratch_R41.lean` / `scratch_R41.out`) |

Conventions confirmed in Mathlib:
- `gaussianPDFReal μ v x` $=(\sqrt{2\pi v})^{-1}\exp(-(x-\mu)^2/(2v))$. It is $>0$ when $v\ne0$ and
  identically $0$ when $v=0$.
- `gaussianReal μ v` is `dirac μ` when $v=0$, and otherwise Lebesgue measure with density
  `gaussianPDF`.

Every theorem assumes all variances are $\neq0$. So every denominator is a strictly positive
density and every Gaussian is non-degenerate.

I compiled the packet against `Mathlib.Probability.Distributions.Gaussian.Real` with
`pp.numericTypes`. The hypotheses `vf < 2 * v` etc. are comparisons in `ℝ≥0` (they are monotone,
so they are equivalent to the real comparisons). In the closed form of #2, `2 * v - vf` elaborates
as **real** subtraction `(2:ℝ) * ↑v - ↑vf`. In #4, `(vf + vc) / 2` is a genuine `ℝ≥0` division.

Notation: $\varphi_{\mu,s}$ is the $N(\mu,s)$ density, $L_f=\varphi_{m_f,v_f}/\varphi_{m,v}$,
$L_c=\varphi_{m_c,v_c}/\varphi_{m,v}$, $P=N(m,v)$.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `memLp_two_likelihoodRatio_iff` | theorem | true | no | no |
| 2 | `integral_likelihoodRatio_sq` | theorem | true | no | no |
| 3 | `memLp_two_mul_sub_likelihoodRatio` | theorem | true | no | no |
| 4 | `changeOfMeasure_average_memLp_two` | theorem | true | no | no |
| 5 | `not_memLp_two_mul_sub_likelihoodRatio` | theorem | true | no | no |

## Main points for a human auditor

- All 5 theorems are true and non-vacuous. None depends on a junk value. The `v ≠ 0` hypotheses
  rule out the degenerate case. In that case `gaussianPDFReal m 0 = 0`, so every ratio would be
  $x/0=0$ and the `MemLp` claims would hold trivially.
- I checked the closed form in #2 numerically to about $10^{-24}$ relative error on 6 parameter
  sets, including $v_f<v$, $v<v_f<2v$ and $m_f\ne m$.
- #5 has no measurability hypothesis on $g$. It does not need one: if $g\,(L_f-L_c)$ were in $L^2$,
  then $|L_f-L_c|\le|g(L_f-L_c)|/c$ with $L_f-L_c$ continuous would put $L_f-L_c$ in $L^2$, a
  contradiction. Its hypothesis $|g|\ge c>0$ **everywhere** is much stronger than needed, which makes the
  negative result narrower than it could be. It excludes, for example, indicator ("digital")
  payoffs. Since the divergence comes from both tails, $g$ bounded away from $0$ on one tail would
  suffice.
- In #4 the first two conjuncts ($v_f<v_f+v_c$, $v_c<v_f+v_c$) are trivial consequences of
  $v_f,v_c>0$. The content is in the `MemLp` and integral conjuncts.

---

## 1. `memLp_two_likelihoodRatio_iff`

**Rendering.** For any $m,m_f\in\mathbb R$ and $v,v_f\in\mathbb R_{\ge0}$ with $v\ne0$ and $v_f\ne0$:
$$L_f=\frac{\varphi_{m_f,v_f}}{\varphi_{m,v}}\in L^2(N(m,v))\iff v_f<2v .$$

**Assessment.**
- *Truth:* true.
  $\int L_f^2\,dP=\int\varphi_{m_f,v_f}^2/\varphi_{m,v}\,dz\propto\int\exp\big(-z^2(\tfrac1{v_f}-\tfrac1{2v})+\text{linear}\big)dz$.
  This is finite iff $\tfrac1{v_f}>\tfrac1{2v}$, i.e. $v_f<2v$. At $v_f=2v$ the exponent is
  affine in $z$ (constant if $m_f=m$), so the integral over ℝ is $+\infty$. Measurability holds
  because the ratio is continuous. Truncated integrals grow without bound for $v_f=2v$
  ($m_f=m$ and $m_f\ne m$) and $v_f=2.5v$, and stabilise for $v_f=1.9v$
  (`check_lr_second_moment.out`).
- *Vacuity:* not vacuous. Both sides can be true ($v=v_f=1$) or false ($v=1,v_f=2$).
- *Junk:* none. The denominator is $>0$ because $v\ne0$. Without `hv` the forward direction would
  fail through the junk $x/0=0$, and the theorem correctly excludes that case.
- *Standard result:* the importance-sampling weight between Gaussians has finite second moment
  ($\chi^2$-divergence $<\infty$) iff the proposal variance exceeds half the target variance.

## 2. `integral_likelihoodRatio_sq`

**Rendering.** For $v,v_f\ne0$ and $v_f<2v$: $L_f^2$ is $N(m,v)$-integrable and
$$\int L_f^2\,dN(m,v)=\frac{v}{\sqrt{v_f(2v-v_f)}}\exp\!\Big(\frac{(m_f-m)^2}{2v-v_f}\Big),$$
where $2v-v_f$ is computed in ℝ (and is $>0$ here).

**Assessment.**
- *Truth:* true. Complete the square with $a=\frac{2v-v_f}{2vv_f}>0$. The prefactor is
  $\frac{\sqrt{2\pi v}}{2\pi v_f}\sqrt{\pi/a}=\frac{v}{\sqrt{v_f(2v-v_f)}}$ and the exponent is
  $\frac{(m_f-m)^2}{2v-v_f}$. Sanity check: $v_f=v$, $m_f=m$ gives $1$. The numerical
  quadrature matches to $\le 2\times10^{-24}$ relative error on 6 cases.
- *Vacuity:* not vacuous ($m=m_f=0$, $v=v_f=1$).
- *Junk:* none. Integrability is asserted, `Real.sqrt` has a positive argument, and the division is
  by a positive number. Even if the subtraction had been in `ℝ≥0`, it would agree here because
  $v_f<2v$.
- *Standard result:* the closed form of $1+\chi^2(N(m_f,v_f)\,\|\,N(m,v))$, the second moment of the
  Gaussian likelihood ratio.

## 3. `memLp_two_mul_sub_likelihoodRatio`

**Rendering.** For $v,v_f,v_c\ne0$ with $v_f<2v$ and $v_c<2v$, any measurable $g:\mathbb R\to\mathbb R$
with $|g(z)|\le C$ for all $z$ (some real $C$):
$g\,(L_f-L_c)\in L^2(N(m,v))$.

**Assessment.**
- *Truth:* true. $L_f,L_c\in L^2(P)$ by #1, so their difference is in $L^2$. Multiplying by a bounded
  measurable function keeps it in $L^2$.
- *Vacuity:* not vacuous ($v=v_f=v_c=1$, $g\equiv1$, $C=1$). If $C<0$ the hypotheses cannot hold,
  but $C\ge0$ is the normal case.
- *Junk:* none.
- *Standard result:* the MLMC level correction under a common change of measure has finite
  variance when both proposal-to-reference variance ratios are below 2.

## 4. `changeOfMeasure_average_memLp_two`

**Rendering.** For $v_f,v_c\ne0$, measurable $g$ with $|g|\le C$, put
$\bar m=(m_f+m_c)/2$ and $\bar v=(v_f+v_c)/2$ (in `ℝ≥0`). Then:
(i) $v_f<2\bar v$; (ii) $v_c<2\bar v$;
(iii) $g\,(\varphi_{m_f,v_f}/\varphi_{\bar m,\bar v}-\varphi_{m_c,v_c}/\varphi_{\bar m,\bar v})\in L^2(N(\bar m,\bar v))$;
(iv) $\int g\,(\bar L_f-\bar L_c)\,dN(\bar m,\bar v)=\int g\,dN(m_f,v_f)-\int g\,dN(m_c,v_c)$.

**Assessment.**
- *Truth:* true. (i) and (ii) say $v_f<v_f+v_c$ and $v_c<v_f+v_c$, which hold because
  $v_c,v_f>0$. (iii) is #3 with $(m,v)=(\bar m,\bar v)$. (iv): $\bar v\ne0$, so
  $N(m_f,v_f)\ll N(\bar m,\bar v)$ with density $\bar L_f$. Then
  $\int g\bar L_f\,dN(\bar m,\bar v)=\int g\,\varphi_{m_f,v_f}\,dz=\mathbb E_f[g]$. Both pieces are
  integrable since $g$ is bounded and $\bar L_f,\bar L_c\in L^1$, so linearity applies. Checked
  numerically for $g\in\{\sin,\tanh,\cos,\text{a step function}\}$ on 4 parameter sets, including a
  very unbalanced pair $v_f=5$, $v_c=0.1$.
- *Vacuity:* not vacuous. *Junk:* none; all integrals are of integrable functions.
- *Hypotheses:* (i) and (ii) are trivial consequences of the hypotheses. Nothing unusual.
- *Standard result:* the Radon–Nikodym change of measure $\mathbb E_Q[g]=\mathbb E_P[g\,dQ/dP]$,
  applied with the "midpoint" Gaussian as a common reference measure for coupled fine and
  coarse levels. The choice $\bar v=(v_f+v_c)/2$ automatically makes both likelihood ratios
  square-integrable.

## 5. `not_memLp_two_mul_sub_likelihoodRatio`

**Rendering.** For $v,v_f,v_c\ne0$ with $2v\le v_f$ and $v_c<2v$, and any $g:\mathbb R\to\mathbb R$
(**not** assumed measurable) and $c>0$ with $c\le|g(z)|$ for all $z$:
$g\,(L_f-L_c)\notin L^2(N(m,v))$.

**Assessment.**
- *Truth:* true. $L_c\in L^2$ and $L_f\notin L^2$ (by #1), so $h:=L_f-L_c\notin L^2$, and $h$ is
  continuous. If $g h$ were in $L^2$, then since $|h|\le|gh|/c$ pointwise and $h$ is
  AE-strongly-measurable, $h$ would be in $L^2$, a contradiction. If $g h$ is not even
  AE-strongly-measurable, it is not in `MemLp` anyway. Truncated second moments of $h$ blow up
  numerically for three cases, including $v_c=1.99$, $v_f=2$, $v=1$.
- *Vacuity:* not vacuous ($m=m_f=m_c=0$, $v=1$, $v_f=2$, $v_c=1$, $g\equiv1$, $c=1$).
- *Junk:* none. The conclusion is a genuine $L^2$-divergence, not a measurability artefact.
- *Hypotheses:* "$|g|\ge c>0$ everywhere" is much stronger than needed. Non-vanishing of $g$ on a
  neighbourhood of either tail would do. So this negative result covers fewer payoffs (for
  example, not digital/indicator payoffs).
- *Standard result:* the sharpness counterpart of #1 and #3: once the fine-level proposal variance
  reaches twice the reference variance, the change-of-measure level correction has infinite
  variance.
