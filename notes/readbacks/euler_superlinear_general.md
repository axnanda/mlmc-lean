# Blind read-back report: packet R32 (HJK divergence of the Euler scheme)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round21/packet_R32_hjk.lean` |
| declarations audited | 18: 1 definition (`hjkRadius`) and 17 theorems. The appended `emPath` is rendered for reference. |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round21/work_R32/` (`check_pathwise.py/.out`, `check_worstcase.py/.out`, `check_event_prob.py/.out`, `check_examples.py/.out`, `probe1.lean/.out`, `packet_scratch.lean/.out`) |

I compiled a scratch copy of the packet with `import MlmcLean`, renaming the namespace to `AuditR32`. All 17 statements
elaborate (`packet_scratch.out`). Elaboration checks (`probe1.out`):

- `(2 : ℝ) ^ β ^ M` is `2 ^ (β ^ M)`. The inner power is `Monoid.npow` (ℝ to an ℕ power) and the outer one is `Real.rpow`.
- `max C 1 ^ 2` is `(max C 1)^2`.
- `T / (N₀ * 2 ^ ℓ : ℕ)` is `T / ↑(N₀ * 2 ^ ℓ)`.
- `emPath` is `MLMC.emPath`.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 0 | `hjkRadius` | def | n/a | n/a | no (all `rpow` bases are $>0$) |
| 1 | `emPath_superlinear_abs_ge` | theorem | true | no | no |
| 2 | `emPath_drift_superlinear_abs_ge` | theorem | true | no | no |
| 3 | `emPath_superlinear_lintegral_ge` | theorem | true | no | no |
| 4 | `hjk_event_prob_ge` | theorem | true | no | no |
| 5 | `hjk_divergence_event_measure_ge` | theorem | true | no | no |
| 6 | `emPath_superlinear_lintegral_ge_exp` | theorem | true | no | no |
| 7 | `emPath_superlinear_payoff_lintegral_tendsto` | theorem | true | no | no |
| 8 | `emPath_superlinear_payoff_integral_tendsto` | theorem | true | no | no. Integrability is assumed eventually (`hint`), so the Bochner junk value 0 is never used. |
| 9 | `emPath_superlinear_moment_lintegral_tendsto` | theorem | true | no | no |
| 10 | `mlmc_level_payoff_lintegral_tendsto` | theorem | true | no | no |
| 11 | `mlmc_level_payoff_sq_lintegral_tendsto` | theorem | true | no | no |
| 12 | `emPath_superlinear_moment_tendsto_atTop` | theorem | true | no | no. Integrability follows from the measurability and polynomial-growth hypotheses. |
| 13 | `emPath_superlinear_integral_abs_tendsto_atTop` | theorem | true | no | no (same as #12) |
| 14 | `hjk_cubic_moment_tendsto_atTop` | theorem | true | no | no |
| 15 | `hjk_xabs_moment_tendsto_atTop` | theorem | true | no | no |
| 16 | `hjk_ginzburgLandau_moment_tendsto_atTop` | theorem | true | no | no |
| 17 | `hjk_quadVol_moment_tendsto_atTop` | theorem | true | no | no |

## Main points for a human auditor

1. **All 17 theorems are true and non-vacuous, and none depends on a junk value.** I proved the pathwise core (#1, #2)
   by hand with the packet's explicit constant `hjkRadius`. I also checked it numerically, both on concrete SDEs
   (`check_pathwise.out`) and with a worst-case adversarial iteration over a parameter grid (`check_worstcase.out`,
   5400 cases, 0 failures).
2. **"Arbitrary measure μ" is not a gap.** `iIndepFun … μ` forces `IsProbabilityMeasure μ` in Mathlib
   (`iIndepFun.isProbabilityMeasure`, from the empty index set), even when `N = 0`. Each `μ.map (Z n) = gaussianReal 0 1`
   forces `Z n` to be a.e.-measurable, since otherwise the map would be `0`.
3. **The Bochner-integral versions need integrability, which the statements supply.**
   - #8 assumes `hint` (eventual integrability of $g(Y_N)$).
   - #12 and #13 add measurability of $a(\cdot,t)$ and $b(\cdot,t)$ and polynomial growth $|a|,|b|\le K(1+|x|^r)$.
     These hypotheses are not in HJK Thm 2.1, which is stated in $[0,\infty]$, but they are needed to make
     $\int|Y_N|^p\,d\mu$ the true moment.
   - Without them, the junk value $\int f = 0$ for non-integrable $f$ would make the statements false. The `∫⁻` versions
     (#7, #9–#11) carry no such extra hypotheses.
4. **The `mlmc_level_*` names may overstate what is proved.** #10 and #11 concern the **fine-level payoff alone**,
   $g(Y^{N_\ell}_{N_\ell})$ with $N_\ell=N_0 2^\ell$: its first absolute moment and its second moment diverge. They do not
   concern the MLMC correction $P_\ell-P_{\ell-1}$ or the MLMC estimator. In particular they are not the HJK (2013)
   divergence theorem for the MLMC Euler method.
5. **The noise is a separate Gaussian array for each $N$.** `Z N n` is required to be independent only within each $N$,
   and the arrays for different $N$ are not coupled. This is harmless, because every statement concerns one $N$ at a time.
6. **Mild modelling choices, none affecting truth.**
   - The coefficient condition `hcoef` is required for all $t\in\mathbb R$; only the grid times $t=ih$ are used.
   - #1 concludes $|Y_{M+1}|\ge 2^{\beta^M}$, which is weaker than the $r^{\beta^M}$-type bound in HJK but sufficient.
   - #3 and #5 use the one-sided event $Z_0\ge r$, while #1 needs only $|z_0|\ge r$. This is fine for a lower bound.
   - In #2 (the drift-dominant variant) the first step is still driven by the noise through $|b(x_0,0)|$.
7. **The quantifier order is correct.** In #4 and #5 the constant $c$ is chosen before $N$ and $Z$. In #6 it is chosen
   before $p$, $N$ and $Z$. The exponent $e$ is a parameter in #1–#3 and #6, and is chosen internally in #7–#13.

---

## Per-declaration analysis

### Appended definition `emPath` (for reference)

**Rendering.** This is the Euler–Maruyama recursion with step $h$ and driving numbers $z_0,z_1,\dots$:
$$Y_0=S_0,\qquad Y_{i+1}=Y_i+a(Y_i,ih)\,h+b(Y_i,ih)\sqrt h\,z_i .$$
`Real.sqrt` of a negative $h$ would be $0$, but every $h$ used below is $>0$ (or $T/0=0$ at $N=0$, which is irrelevant
for limits). $Y_N$ depends only on $z_0,\dots,z_{N-1}$.

### 0. `hjkRadius` (def)

**Rendering.** With $D=\max(C,1)$:
$$R(C,\alpha,\beta)=D+2(8D)^{1/(\beta-1)}+(8D^2)^{1/(\beta-\alpha)}$$
using real `rpow`. Both bases are $\ge 8>0$, so there is no junk. When $\beta>1$ and $\beta>\alpha$:
- $R\ge D\ge1$;
- $R^{\beta-1}\ge 2^{\beta-1}\cdot 8D$;
- $R^{\beta-\alpha}\ge 8D^2$;
- $R\ge 3$.

### 1. `emPath_superlinear_abs_ge`

**Rendering.** Let $a,b:\mathbb R^2\to\mathbb R$ and $C,\alpha,\beta\in\mathbb R$ with $\beta>1$ and $\alpha<\beta$. Assume
$$\forall x,t:\ |x|\ge C\Rightarrow |x|^\beta\le C\max(|a(x,t)|,|b(x,t)|)\ \wedge\ \min(|a(x,t)|,|b(x,t)|)\le C|x|^\alpha .$$
Let $e\in\mathbb R$ with $e(\beta-1)\ge1$ and $2e(\beta-\alpha)\ge1$. Let $h\in(0,1]$, $x_0\in\mathbb R$, $z:\mathbb N\to\mathbb R$
and $M\in\mathbb N$. Assume
- $R\,h^{-e}+|x_0|+|a(x_0,0)|\le |b(x_0,0)|\sqrt h\,|z_0|$, and
- $\tfrac12\le|z_k|\le1$ for $1\le k\le M$.

Then $2^{(\beta^M)}\le |Y_{M+1}|$, where $Y$ is `emPath a b h x₀ z`.

**Assessment.**

*Truth: true.* Taking $x=1$ in `hcoef` forces $C>0$. Write $D=\max(C,1)$.

- *Step 1.* Because $h\le1$, $|Y_1|\ge |b|\sqrt h|z_0|-|x_0|-|a|h\ge R h^{-e}$.
- *Invariant.* Suppose $u=|Y_k|\ge Rh^{-e}$, which is $\ge D\ge C$.
- *Two consequences of the invariant.* From $h\ge (R/u)^{1/e}\ge (R/u)^{\beta-1}$, using $R/u\le1$ and $1/e\le\beta-1$, we
  get $u\le u^\beta h/R^{\beta-1}\le u^\beta h/(8D)$. From $h^{-1/2}\le (u/R)^{1/(2e)}\le (u/R)^{\beta-\alpha}$ we get
  $Du^\alpha\sqrt h\le u^\beta h\,D/R^{\beta-\alpha}\le u^\beta h/(8D)$.
- *Drift-dominant case* ($|a|\ge|b|$). Then $|Y_{k+1}|\ge u^\beta h/D-u-Du^\alpha\sqrt h$.
- *Diffusion-dominant case* ($|b|>|a|$). Then $|Y_{k+1}|\ge u^\beta\sqrt h/(2D)-u-Du^\alpha h$.
- *Combining the cases.* Since $\sqrt h\ge h$, both cases give $|Y_{k+1}|\ge u^\beta h/(4D)\ge 2^\beta u$, so the
  invariant propagates.
- *Doubly exponential growth.* Put $\lambda=(h/4D)^{1/(\beta-1)}\le1$ and $w_k=\lambda|Y_k|$. Then $w_{k+1}\ge w_k^\beta$
  and $w_1\ge R(4D)^{-1/(\beta-1)}h^{1/(\beta-1)-e}\ge 2\cdot2^{1/(\beta-1)}\ge2$. Hence
  $|Y_{M+1}|\ge w_{M+1}\ge 2^{\beta^M}$.

Numerical checks:
- `check_pathwise.out`: 6 SDEs, random and adversarial $z$, all pass.
- `check_worstcase.out`: adversarial worst-case recursion over 5400 parameter combinations, with $C\in[0.05,10]$,
  $\beta\in[1.02,5]$, $\alpha\in[-3,\beta)$ and $h$ down to $10^{-8}$. There are 0 failures, and the minimum of
  $\log|Y|/\log 2^{\beta^M}$ is $2.25$.

*Vacuity: not vacuous.* Take $a=-x^3$, $b=1$, $C=1$, $\alpha=0$, $\beta=3$, $e=\tfrac12$, $h=1$, $x_0=0$ (so $R\approx8.66$),
$z_0=9$ and $z_k=1$.

*Junk values: none.* All `rpow` bases are $\ge0$, and $\sqrt h$ has $h>0$.

*Hypotheses.* The hypotheses are natural. `hcoef` for all $t$ is slightly more than needed, since only $t=ih$ is used.

*Standard result.* This is the pathwise core of Hutzenthaler–Jentzen–Kloeden (2011, Proc. R. Soc. A), Thm 2.1: on the
event "first increment huge, later normalised increments in $[\tfrac12,1]$ in absolute value", the Euler iterates grow
doubly exponentially.

### 2. `emPath_drift_superlinear_abs_ge`

**Rendering.** Same as #1, with two changes:
- the coefficient condition is the drift-dominant one,
  $|x|\ge C\Rightarrow |x|^\beta\le C|a(x,t)|\ \wedge\ |b(x,t)|\le C|x|^\alpha$;
- the later increments need only $|z_k|\le1$ for $1\le k\le M$.

The conclusion is again $2^{\beta^M}\le|Y_{M+1}|$.

**Assessment.**

*Truth: true.* The proof of #1 in the drift-dominant case uses only $|a|\ge u^\beta/C$, $|b|\le Cu^\alpha$ and $|z|\le1$.
The first step uses `hz0` exactly as in #1.

*Vacuity: not vacuous.* The instance of #1 works ($|x|^3\le|x^3|$ and $1\le|x|^0$).

*Junk values: none.*

*Hypotheses.* The first step is driven by the noise ($|b(x_0,0)|>0$ is implicitly forced by `hz0`) even though the drift
dominates. That is a valid sufficient condition.

*Standard result.* This is a variant of HJK's pathwise lemma for drift-dominated coefficients.

### 3. `emPath_superlinear_lintegral_ge`

**Rendering.** Take the hypotheses of #1 on $a,b,C,\alpha,\beta,e$, and also:
- $b(x_0,0)\ne0$;
- $T>0$, $p\ge0$, and $N\in\mathbb N$ with $T\le N$, so $N\ge1$ and $h=T/N\in(0,1]$;
- $Z:\mathbb N\to\Omega\to\mathbb R$ with $\mathrm{Law}_\mu(Z_n)=\mathcal N(0,1)$ for $n<N$, and $(Z_n)_{n<N}$ independent
  under $\mu$.

Then
$$\Phi^c(r_N)\cdot P(\tfrac12\le G\le1)^{N-1}\cdot \big(2^{\beta^{N-1}}\big)^p\ \le\ \int^- |Y_N|^p\,d\mu$$
in $[0,\infty]$, where:
- $r_N=\dfrac{R(N/T)^e+|x_0|+|a(x_0,0)|}{|b(x_0,0)|\sqrt{T/N}}$;
- $\Phi^c(r)=\mathcal N(0,1)[r,\infty)$;
- $Y_N$ is the Euler path with step $T/N$ driven by $Z_n(\omega)$.

The power $N-1$ is ℕ-subtraction, which is harmless since $N\ge1$.

**Assessment.**

*Truth: true.* Let $E$ be the event $\{Z_0\ge r_N\}\cap\bigcap_{k=1}^{N-1}\{Z_k\in[\tfrac12,1]\}$. Since $r_N>0$, $E$ gives
$|Z_0|\ge r_N$, which is `hz0` with $h^{-1}=N/T$. So #1 with $M=N-1$ gives $|Y_N|\ge 2^{\beta^{N-1}}$ on $E$, and
`rpow` with $p\ge0$ is monotone. Then $\int^-\ge \mu(E)\,(2^{\beta^{N-1}})^p$. By independence (Fin $N$ family, with the
measurable preimages of `Ici` and `Icc`) and the Gaussian laws, $\mu(E)$ is exactly the stated product. `iIndepFun`
forces $\mu$ to be a probability measure.

*Vacuity: not vacuous.* Take $\Omega=\mathbb R^{\mathbb N}$ with the infinite product of $\mathcal N(0,1)$ and the
coordinate maps as $Z$, together with the instance from #1.

*Junk values: none.* The `∫⁻` of a non-measurable integrand would be a lower integral, but the bound goes through an
indicator of a null-measurable set.

*Hypotheses.* They are natural. $p=0$ gives the trivial bound $\mu(E)\le1$.

*Standard result.* This is the lower bound $E|Y_N|^p\ge P(\Omega_N)\,2^{p\beta^{N-1}}$ in HJK (2011).

### 4. `hjk_event_prob_ge`

**Rendering.** Let $K\ge0$, $B\ge0$, $c_0>0$, $T>0$ and $e\ge0$. Then there is $c\ge0$ such that for every $N\in\mathbb N$
with $N\ge1$:
$$e^{-cN^{2e+1}}\le \mathcal N(0,1)\big[\tfrac{K(N/T)^e+B}{c_0\sqrt{T/N}},\infty\big)\cdot \mathcal N(0,1)[\tfrac12,1]^{\,N-1}.$$
The right-hand side is in $[0,\infty]$; $c$ does not depend on $N$.

**Assessment.**

*Truth: true.*
- Bound the threshold: $r_N\le A N^{e+1/2}$ with $A=(KT^{-e}+B)/(c_0\sqrt T)$, using $N\ge1$ and $e\ge0$.
- Bound the tail: $P(G\ge r)\ge P(r\le G\le r+1)\ge \varphi(r+1)\ge e^{-(A+1)^2N^{2e+1}/2-\log\sqrt{2\pi}}$.
- Bound the product: $q^{N-1}=e^{-(N-1)\log(1/q)}$ with $q=P(\tfrac12\le G\le1)\approx0.1499$.
- Since $N\le N^{2e+1}$, $c=(A+1)^2/2+\log\sqrt{2\pi}+\log(1/q)$ works.

`check_event_prob.out` shows that $-\log(\mathrm{RHS})/N^{2e+1}$ stays bounded for $N$ up to $10^5$ for six parameter
sets.

*Vacuity: not vacuous.* For example $K=B=0$, $c_0=T=1$, $e=0$.

*Junk values: none.* The denominator $c_0\sqrt{T/N}>0$.

*Standard result.* This is a Gaussian tail lower bound (Mills ratio), the probability estimate for HJK's event $\Omega_N$.

### 5. `hjk_divergence_event_measure_ge`

**Rendering.** Fix a measure $\mu$ and $K,B,c_0,T,e$ as in #4. Then there is $c\ge0$ such that for all $N\ge1$ and all
$Z:\mathbb N\to\Omega\to\mathbb R$ with $\mathrm{Law}_\mu(Z_n)=\mathcal N(0,1)$ for $n<N$ and $(Z_n)_{n<N}$ independent:
$$e^{-cN^{2e+1}}\le\mu\{\omega: r_N\le Z_0(\omega)\ \wedge\ \forall k,\ 1\le k<N\Rightarrow \tfrac12\le Z_k(\omega)\le1\},$$
where $r_N$ is the threshold of #4.

**Assessment.**

*Truth: true.* By independence and the laws, the measure equals the right-hand side of #4. `iIndepFun` forces $\mu$ to be
a probability measure, and the $Z_n$ are a.e.-measurable. The constant $c$ from #4 does not depend on $\mu$, $N$ or $Z$.

*Vacuity: not vacuous.* The product-space instance of #3 works.

*Junk values: none.*

*Standard result.* This is HJK's $P(\Omega_N)\ge e^{-cN^{2e+1}}$.

### 6. `emPath_superlinear_lintegral_ge_exp`

**Rendering.** Take $\mu$ and the hypotheses of #3 on $a,b,C,\alpha,\beta,e$, with $b(x_0,0)\ne0$ and $T>0$. Then there is
$c\ge0$ such that for all $p\ge0$, all $N\in\mathbb N$ with $T\le N$, and all i.i.d.-standard-Gaussian $(Z_n)_{n<N}$:
$$e^{-cN^{2e+1}}\,\big(2^{\beta^{N-1}}\big)^p\le\int^-|Y_N|^p\,d\mu .$$

**Assessment.**

*Truth: true.* Combine #3 with #4, taking $K=R$, $B=|x_0|+|a(x_0,0)|$ and $c_0=|b(x_0,0)|>0$. Here $e>0$ by `he1`, and
`ENNReal.ofReal` is multiplicative on nonnegative reals. The constant $c$ is uniform in $p$, $N$ and $Z$.

*Vacuity: not vacuous.*

*Junk values: none.*

*Standard result.* This is the key estimate in HJK (2011), Thm 2.1:
$E|Y_N|^p\ge e^{-cN^{2e+1}}2^{p\beta^{N-1}}$.

### 7. `emPath_superlinear_payoff_lintegral_tendsto`

**Rendering.** Take the HJK coefficient condition on $a,b$ (with $\beta>1$ and $\alpha<\beta$), $b(x_0,0)\ne0$ and $T>0$.
Let $g:\mathbb R\to\mathbb R$, $q>0$ and $D$ satisfy $\forall x,\ |x|\ge D\Rightarrow |x|^q\le D|g(x)|$. Let
$Z:\mathbb N\to\mathbb N\to\Omega\to\mathbb R$ be such that for each $N$, $(Z_{N,n})_{n<N}$ are i.i.d. $\mathcal N(0,1)$
under $\mu$. Then
$$\int^-|g(Y^N_N)|\,d\mu\to\infty \quad\text{as } N\to\infty,$$
where $Y^N$ is the Euler path with step $T/N$ driven by $Z_{N,\cdot}$. No measurability is assumed on $a$, $b$ or $g$.

**Assessment.**

*Truth: true.*
- Taking $x=1$ in `hg` forces $D>0$.
- Fix $e=\max(1/(\beta-1),1/(2(\beta-\alpha)))$ and apply #6.
- On the event, $|Y_N|\ge 2^{\beta^{N-1}}\ge D$ for large $N$, so $|g(Y_N)|\ge 2^{q\beta^{N-1}}/D$.
- Therefore $\int^-\ge e^{-cN^{2e+1}}2^{q\beta^{N-1}}/D\to\infty$, since the doubly exponential term beats the polynomial
  exponent.

*Vacuity: not vacuous.* Take $a=-x^3$, $b=1$, $g=\mathrm{id}$, $q=D=1$ and a product space.

*Junk values: none.*

*Hypotheses.* $q>0$ is needed: with $q=0$, a bounded $g$ is allowed and the claim fails.

*Standard result.* This is HJK (2011), Thm 2.1, in the version for payoffs with polynomial growth from below.

### 8. `emPath_superlinear_payoff_integral_tendsto`

**Rendering.** Take the hypotheses of #7, plus (`hint`) that eventually in $N$, $\omega\mapsto g(Y^N_N(\omega))$ is
Bochner-integrable. Then $\int|g(Y^N_N)|\,d\mu\to+\infty$ (Bochner integral, `atTop`).

**Assessment.**

*Truth: true.* For large $N$ the integrand is integrable, so the Bochner integral equals the `toReal` of the `∫⁻` in #7,
which is finite and tends to $\infty$.

*Vacuity: not vacuous.* `hint` holds for $a=-x^3$, $b=1$, $g=\mathrm{id}$ and measurable Gaussian $Z$, because $Y_N$ is
then a polynomial in Gaussians.

*Junk values: none.* `hint` is exactly what prevents the junk value $\int f=0$ for non-integrable $f$; without `hint` the
statement could fail.

*Hypotheses.* `hint` is a hypothesis on the composite (not on primitive data), but it is natural.

*Standard result.* HJK (2011), Thm 2.1, $E|g(Y_N)|\to\infty$.

### 9. `emPath_superlinear_moment_lintegral_tendsto`

**Rendering.** Take the hypotheses of #7 without $g$, and with $p>0$. Then $\int^-|Y^N_N|^p\,d\mu\to\infty$.

**Assessment.**

*Truth: true,* by #6 with $(2^{\beta^{N-1}})^p e^{-cN^{2e+1}}\to\infty$. The condition $p>0$ is needed, since $p=0$
gives the constant $1$.

*Vacuity: not vacuous.*

*Junk values: none.*

*Standard result.* HJK (2011), Thm 2.1 (strong divergence): $\lim_N E|Y_N|^p=\infty$ for all $p>0$.

### 10. `mlmc_level_payoff_lintegral_tendsto`

**Rendering.** Take the hypotheses of #7 and $N_0\in\mathbb N$ with $N_0\ge1$. Let $N_\ell=N_0 2^\ell$, computed in ℕ and
then cast. Then, as $\ell\to\infty$,
$$\int^-\big|g\big(Y^{N_\ell}_{N_\ell}\big)\big|\,d\mu\to\infty,$$
where $Y^{N_\ell}$ has step $T/N_\ell$ and noise $Z_{N_\ell,\cdot}$.

**Assessment.**

*Truth: true.* This is the composition of #7 with $N_\ell\to\infty$; $N_0\ge1$ is needed.

*Vacuity: not vacuous.*

*Junk values: none.*

*Hypotheses / naming.* The statement concerns the **fine-level payoff** $P_\ell$ alone, not the MLMC correction
$P_\ell-P_{\ell-1}$.

*Standard result.* A consequence of HJK (2011) along the MLMC grid sequence.

### 11. `mlmc_level_payoff_sq_lintegral_tendsto`

**Rendering.** Same as #10, with the integrand $g(Y)^2$ in place of $|g(Y)|$: $\int^- g(Y^{N_\ell}_{N_\ell})^2\,d\mu\to\infty$.

**Assessment.**

*Truth: true.* On the event of #6, $g^2\ge(2^{q\beta^{N-1}}/D)^2$, which also beats $e^{-cN^{2e+1}}$.

*Vacuity: not vacuous.*

*Junk values: none.*

*Hypotheses / naming.* As in #10, this is the second moment of the level payoff, not of the level difference.

*Standard result.* The second moment of the level payoff diverges, a consequence of HJK (2011).

### 12. `emPath_superlinear_moment_tendsto_atTop`

**Rendering.** Take the hypotheses of #9, plus:
- $x\mapsto a(x,t)$ and $x\mapsto b(x,t)$ are measurable for each $t$;
- $|a(x,t)|,|b(x,t)|\le K(1+|x|^r)$ for all $x,t$, with $r\in\mathbb N$.

Then $\int|Y^N_N|^p\,d\mu\to+\infty$ (Bochner integral).

**Assessment.**

*Truth: true.*
- *Measurability.* $Y_N$ is a measurable function of $(Z_{N,0},\dots,Z_{N,N-1})$, because the times $ih$ are fixed. The
  $Z$ are a.e.-measurable, so $Y_N$ is a.e.-measurable.
- *Integrability.* By induction, $|Y_N|$ is bounded by a polynomial in $|Z_{N,j}|$, and Gaussian moments are finite. So
  $|Y_N|^p$ is integrable under the probability measure $\mu$.
- Hence the Bochner integral equals the `toReal` of the `∫⁻` in #9, which tends to $\infty$.

*Vacuity: not vacuous.* $a=-x^3$, $b=1$, $K=1$, $r=3$.

*Junk values: none.* The extra hypotheses rule out the non-integrable junk value 0.

*Hypotheses.* Measurability and polynomial growth are extra relative to HJK, which works in $[0,\infty]$. They serve only
to make the Bochner integral meaningful.

*Standard result.* HJK (2011), Thm 2.1.

### 13. `emPath_superlinear_integral_abs_tendsto_atTop`

**Rendering.** Same as #12 with $p=1$: $\int|Y^N_N|\,d\mu\to+\infty$.

**Assessment.**

*Truth: true,* as the special case $p=1$ of #12.

*Vacuity: not vacuous.*

*Junk values: none.*

*Standard result.* HJK (2011), Thm 2.1, first absolute moment.

### 14. `hjk_cubic_moment_tendsto_atTop`

**Rendering.** For any $x_0$, $T>0$, $p>0$ and i.i.d. standard Gaussian arrays $Z$ as above, consider the Euler scheme for
$dX=-X^3\,dt+dW$ ($a(S,t)=-S^3$, $b\equiv1$). Then $\int|Y^N_N|^p\,d\mu\to+\infty$.

**Assessment.**

*Truth: true.* This is #12 with $C=1$, $\beta=3$, $\alpha=0$, $K=1$, $r=3$ (checked in `check_examples.out`):
- $|x|^3\le\max(|x|^3,1)$ and $\min(|x|^3,1)\le1$ for $|x|\ge1$;
- $b\equiv1\ne0$, so no condition on $x_0$ is needed.

*Vacuity: not vacuous.* Any product-space Gaussian array works.

*Junk values: none.*

*Standard result.* This is HJK's flagship example: Euler moments diverge for $dX=-X^3dt+dW$, although the exact solution
has all moments.

### 15. `hjk_xabs_moment_tendsto_atTop`

**Rendering.** Same as #14 with drift $a(S)=-S|S|$ and $b\equiv1$.

**Assessment.**

*Truth: true.* Use $\beta=2$, $\alpha=0$, $C=1$, $K=1$, $r=2$ (`check_examples.out`).

*Vacuity: not vacuous.*

*Junk values: none.*

*Standard result.* HJK divergence for the drift $-x|x|$.

### 16. `hjk_ginzburgLandau_moment_tendsto_atTop`

**Rendering.** Let $\sigma\ne0$, $x_0\ne0$, $T>0$ and $p>0$. Consider the stochastic Ginzburg–Landau Euler scheme
$a(S)=S-S^3$, $b(S)=\sigma S$. Then $\int|Y^N_N|^p\,d\mu\to+\infty$.

**Assessment.**

*Truth: true.* Use $\beta=3$, $\alpha=1$, $C=\max(2,|\sigma|)$:
- for $|x|\ge2$, $|x-x^3|\ge\tfrac34|x|^3$, so $|x|^3\le 2|x-x^3|\le C\max(|a|,|b|)$;
- $\min(|a|,|b|)\le|\sigma||x|\le C|x|$;
- $b(x_0,0)=\sigma x_0\ne0$;
- polynomial growth with $K=C$, $r=3$ (`check_examples.out`).

*Vacuity: not vacuous.*

*Junk values: none.*

*Hypotheses.* Both hypotheses are necessary. If $x_0=0$ then $Y\equiv0$. If $\sigma=0$ the scheme is deterministic and
bounded for small $h$.

*Standard result.* The HJK example of the stochastic Ginzburg–Landau equation.

### 17. `hjk_quadVol_moment_tendsto_atTop`

**Rendering.** Let $x_0\ne0$, $T>0$ and $p>0$. Consider the Euler scheme for $dX=-X\,dt+X^2\,dW$. Then
$\int|Y^N_N|^p\,d\mu\to+\infty$.

**Assessment.**

*Truth: true.* Use $\beta=2$, $\alpha=1$, $C=1$:
- for $|x|\ge1$, $\max(|x|,x^2)=x^2$ and $\min(|x|,x^2)=|x|=|x|^{1}$;
- $b(x_0,0)=x_0^2\ne0$;
- polynomial growth with $K=1$, $r=2$.

This example exercises the diffusion-dominant case, which uses $|z_k|\ge\tfrac12$.

*Vacuity: not vacuous.*

*Junk values: none.*

*Hypotheses.* $x_0\ne0$ is necessary, since $x_0=0$ gives $Y\equiv0$.

*Standard result.* An HJK-type divergence example with superlinear diffusion.
