# Blind statement audit: `packet_L3_complexity_theorem2.lean`

| field | value |
|---|---|
| date | 2026-09-29 |
| packet | `readback/round10/packet_L3_complexity_theorem2.lean` |
| declarations audited | 28 (13 theorems/lemmas, 15 definitions, including the 5 appended definitions) |
| auditor | independent blind auditor (sub-agent) |
| scripts | `readback/round10/work_L3/` (`s01`–`s07`; each `.py` has its `.out` beside it) |

Sources consulted: the packet, plus Mathlib sources for the conventions below. Nothing else in the repository was read.

- `∑ x ∈ s, body` parses `body` at `term:67` (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`, l. 181). So `∑ ℓ ∈ 𝓛, Y ℓ (N ℓ) ω - μ[P]` means $(\sum_{\ell} Y_\ell) - \mathbb E P$, while `*` and `/` stay inside the sum.
- `μ[X]` is `∫ x, X x ∂μ` (`Probability/Notation.lean`).
- `variance X μ = (evariance X μ).toReal`, where `evariance` is $\int^- \|X-\mu[X]\|_e^2$.
- `IndepFun f g μ` is defined for any measure, via `Kernel.const Unit μ` and `dirac ()`.
- `IndepFun.variance_sum` needs only pairwise independence.
- `Real.logb b x = log x / log b`. `⌈x⌉₊ = 0` for $x\le 0$, and `⌊x⌋₊ = 0` for $x\le0$.
- In `(1 + (L:ℝ)) ^ (crit δ - 1)` the exponent is a natural number, so the subtraction truncates. `Monoid.Pow` is the default instance.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `complexityBound` | def | n/a | n/a | no; positive and finite for $0<\varepsilon<e^{-1}$ |
| 2 | `Vb` | def | n/a | n/a | no |
| 3 | `Cb` | def | n/a | n/a | no |
| 4 | `sqrt_Vb_mul_Cb` | lemma | **true** | no | no |
| 5 | `levelL` | def | n/a | n/a | no; the `⌈·⌉₊` clamp to 0 is intended |
| 6 | `two_rpow_levelL_le` | lemma | **true** | no | no |
| 7 | `K1` | def | n/a | n/a | no |
| 8 | `K2` | def | n/a | n/a | no |
| 9 | `exists_L_N` | theorem | **true** | no | no |
| 10 | `tail_cost_bound` | lemma | **true** | no | no ($\gamma>0$ keeps $2^\gamma-1\neq0$) |
| 11 | `cost_le_of_level` | theorem | **true** | no | no |
| 12 | `mimcEta` | def | n/a | n/a | no, given $\alpha_d>0$ |
| 13 | `mimcD2` | def | n/a | n/a | no |
| 14 | `mimcD3` | def | n/a | n/a | no |
| 15 | `mimcBound` | def | n/a | n/a | no; positive for $0<\varepsilon<e^{-1}$ |
| 16 | `mimc_exists_level` | lemma | **true** | no | no. The ℕ-subtraction `crit δ - 1` gives exponent 0 when `crit δ = 0`, and the lemma would even hold with $-1$ |
| 17 | `mimc_construction` | lemma | **true** | no | no |
| 18 | `mimc_level_power` | lemma | **true** | no | no |
| 19 | `mimc_complexity` | theorem | **true** | no | no |
| 20 | `integrable_integral_crossDiff` | theorem | **true** | no | no |
| 21 | `mimc_mse_cost_of` | theorem | **true** | no | no, under the probability-measure reading (see main point 4) |
| 22 | `mimc_mse_cost` | theorem | **true** | no | no |
| 23 | `mimcD3_eq_zero` | lemma | **true** (trivial) | no | no |
| 24 | `crossDiff` | def | n/a | n/a | no |
| 25 | `dot` | def | n/a | n/a | no |
| 26 | `box` | def | n/a | n/a | no |
| 27 | `crit` | def | n/a | n/a | no |
| 28 | `indexSet` | def | n/a | n/a | faithful only when every $\theta_d>0$, which every use assumes |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.** All 13 theorem/lemma statements are true as stated, and each has a meaningful instance satisfying every hypothesis. The numerical checks (s01–s06b) agree with the proof sketches below.
2. **`mimc_complexity` assumes the strict condition $\beta_d/2<\alpha_d$ for every $d$.** This forces $d_3:=\#\{d:\alpha_d=\beta_d/2\}=0$ (lemma 23).
   - As I recall, the published MIMC theorem allows $\alpha_d\ge\tfrac12\beta_d$ and has $d_3$-dependent log factors. I cannot confirm the exact exponents from memory.
   - So the formalised statement is a special case. For $D=1$ it excludes, for example, the Milstein-type case $\beta=2\alpha$, which the MLMC theorem allows. The MLMC theorem needs only $\alpha\ge\tfrac12\min(\beta,\gamma)$, and it is covered separately by `cost_le_of_level`.
   - s07 illustrates the excluded case $d_3=2$: the natural witness gains a factor of $|\log\varepsilon|$ there.
3. **`mimc_complexity` is only the deterministic half of the MIMC theorem.** It proves that an index set $\mathcal L$ and sample sizes $N$ exist that meet the bias, variance and cost budgets.
   - The probabilistic content (MSE $<\varepsilon^2$ and expected cost) is in `mimc_mse_cost_of` and `mimc_mse_cost`. Feeding the conclusion of 19 into `hdet` of 22 gives the full theorem, since the conjuncts have identical shape.
   - No declaration in this packet states the combined result. The dangling `universe u` before `end MLMC` suggests a declaration was omitted from the packet.
   - Likewise, `exists_L_N` together with `cost_le_of_level` (with $K=K_1$) gives the deterministic core of the MLMC theorem, but no combined statement appears here.
4. **Packet rendering caveat.** Two consecutive `open Filter Topology in` lines come before `variable [IsProbabilityMeasure μ]`.
   - Read literally, `open … in variable …` scopes the instance to that single command. Then 21 and 22 would *not* assume a probability measure.
   - Most likely these lines are left over from declarations omitted from the packet.
   - Truth is the same in both readings. For $D\ge1$, pairwise independence of an infinite family forces $\mu(\Omega)\in\{0,1,\infty\}$. The case $\mu=0$ is trivial.
   - The case $\mu(\Omega)=\infty$ forces every $Y=0$ a.e. Then (iii), the telescoping identity and (i) give $\mathbb EP=0$, so the MSE is a genuine 0.
   - For $D=0$ there are no pairs, so $\mu$ is arbitrary.
     - With finite mass other than 1, `h_var` for all $n$ forces $\mathbb EP=0$, and the MSE equals the variance.
     - With infinite mass, the MSE integral can be 0 only through the "non-integrable ⇒ 0" convention. This is the one place where the literal reading would depend on a junk value.
   - The maintainers should confirm from the source that the instance really is in force.
5. **The log exponents in `mimc_complexity` are not trivially achievable.** With the naive index weights $\theta=\alpha$, the cost is one $|\log\varepsilon|$ factor too large (s06b: log-log slope 0.92). With the weights $\theta=\alpha+(\gamma-\beta)/2$ the ratio stays bounded out to $\varepsilon=10^{-150}$. So the statement is sharp enough that the proof must choose the index set carefully.
6. **ℕ-subtraction in lemmas 16 and 17.** When `crit δ = 0`, the exponent `crit δ - 1` becomes 0 rather than $-1$. This makes the statement weaker but still true. s05 case 3 shows that even the exponent $-1$ would hold there, so truth does not depend on the truncation.
7. **Minor hypothesis notes.**
   - The positivity hypotheses in 4 are unnecessary.
   - $\gamma>0$ in 11 is standard but not needed.
   - $\gamma>0$ in 10 *is* needed: at $\gamma=0$, Lean evaluates $2^0/(2^0-1)$ as $1/0=0$, which would make 10 false.
   - The independence hypothesis `hind` in 21 and 22 is quantified over *all* positive allocations $N$. This is a strong but natural modelling choice (independent sampling on each level), and it is satisfiable.

---

## Per-declaration analysis

Notation: $\ell\in\mathbb N^D$, $a\cdot\ell=\sum_d a_d\ell_d$ (`dot`), and $\log$ is the natural log. Any power with a real exponent is `Real.rpow`, and every such base in this packet is positive in the ranges where it is used.

### 1. `complexityBound` (def)

**Rendering.**

$$\mathrm{cB}(\alpha,\beta,\gamma,\varepsilon)=\begin{cases}\varepsilon^{-2}&\gamma<\beta\\ \varepsilon^{-2}(\log\varepsilon)^2&\beta=\gamma\\ \varepsilon^{-2-(\gamma-\beta)/\alpha}&\gamma>\beta\end{cases}$$

The square is a natural-number power. For $0<\varepsilon<e^{-1}$ every branch is positive, and $(\log\varepsilon)^2>1$. These are the three regimes of the MLMC complexity theorem (Giles 2008, Thm 3.1; Cliffe–Giles–Scheichl–Teckentrup 2011, Thm 1).

### 2. `Vb` / 3. `Cb` (defs)

**Rendering.** $V_b(\ell)=c_2\,2^{-\beta\ell}$ and $C_b(\ell)=c_3\,2^{\gamma\ell}$ for $\ell\in\mathbb N$ cast to ℝ. These are the variance and cost bounds on level $\ell$.

### 4. `sqrt_Vb_mul_Cb` (lemma)

**Rendering.** For $c_2,c_3>0$, all real $\beta,\gamma$ and all $\ell\in\mathbb N$:

$$\sqrt{V_b(\ell)C_b(\ell)}=\sqrt{c_2c_3}\,\big(2^{(\gamma-\beta)/2}\big)^{\ell}.$$

**Assessment.**
- Truth: true. $V_bC_b=c_2c_3\,2^{(\gamma-\beta)\ell}$, and $\sqrt{xy}=\sqrt x\sqrt y$ for $x\ge 0$. s01: maximum relative error $3\cdot10^{-60}$ over 3000 samples.
- Vacuity: not vacuous (take $c_2=c_3=1$).
- Junk values: none.
- Hypotheses: the positivity hypotheses are stronger than needed, but harmless.

### 5. `levelL` (def)

**Rendering.** $\mathrm{levelL}(\alpha,c_1,\delta)=\lceil \log_2(c_1/\delta)/\alpha\rceil_+\in\mathbb N$. This is 0 when the argument is $\le 0$. It is the smallest level $L$ with $c_1 2^{-\alpha L}\le\delta$ when $\alpha>0$.

### 6. `two_rpow_levelL_le` (lemma)

**Rendering.** For $\alpha,c_1,\delta>0$ and $L=\mathrm{levelL}(\alpha,c_1,\delta)$: $\;2^{\alpha L}\le 2^{\alpha}\max(1,c_1/\delta)$.

**Assessment.**
- Truth: true.
  - If $x=\log_2(c_1/\delta)/\alpha\le0$, then $L=0$ and $1\le 2^\alpha$.
  - Otherwise $L<x+1$, so $2^{\alpha L}<2^{\alpha}c_1/\delta$.
  - s01: no violations in 20000 samples; maximum ratio 0.9999985.
- Vacuity: not vacuous (for example $\alpha=c_1=1$, $\delta=1/2$).
- Junk values: the $L=0$ branch uses the intended clamp of `⌈·⌉₊`. A real-valued ceiling would only make the left side smaller, so truth does not depend on the clamp.
- Hypotheses: $c_1>0$ is needed, because `logb` takes $|\cdot|$ of a negative argument.

### 7. `K1` / 8. `K2` (defs)

**Rendering.**
- $K_1(\alpha,c_1)=2^\alpha(1+2c_1)$.
- $K_2(\alpha,c_1)=\dfrac{|\log(2c_1)|+1}{\alpha\log 2}+2$.

These are explicit constants that depend only on $\alpha$ and $c_1$.

### 9. `exists_L_N` (theorem)

**Rendering.** Let $\alpha,c_1,c_2,c_3>0$, let $\beta,\gamma\in\mathbb R$ be arbitrary, and let $0<\varepsilon<e^{-1}$. Then there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$, both depending on all the data including $\varepsilon$, such that:

- (a) $N_\ell\ge1$ for every $\ell$.
- (b) $(c_12^{-\alpha L})^2\le\varepsilon^2/4$, that is, the bias is at most $\varepsilon/2$.
- (c) $\sum_{\ell=0}^{L}V_b(\ell)/N_\ell\le\varepsilon^2/2$.
- (d) $\displaystyle\sum_{\ell=0}^{L}N_\ell C_b(\ell)\le 2\varepsilon^{-2}c_2c_3\Big(\sum_{\ell=0}^{L}(2^{(\gamma-\beta)/2})^{\ell}\Big)^2+c_3\sum_{\ell=0}^{L}(2^{\gamma})^{\ell}$.
- (e) $2^{\alpha L}\le K_1/\varepsilon$.
- (f) $L+1\le K_2\cdot(-\log\varepsilon)$.

**Assessment.**
- Truth: true. Witness:
  - Take $L=\mathrm{levelL}(\alpha,c_1,\varepsilon/2)$.
  - Take $N_\ell=\lceil2\varepsilon^{-2}\sqrt{V_\ell/C_\ell}\,S\rceil$, where $S=\sum_{k\le L}\sqrt{V_kC_k}$. Set $N_\ell=1$ for $\ell>L$.
- Why each conjunct holds:
  - (b) holds because $L\ge\log_2(2c_1/\varepsilon)/\alpha$.
  - (c): $\sum V_\ell/N_\ell\le\frac{\varepsilon^2}{2S}\sum\sqrt{V_\ell C_\ell}=\varepsilon^2/2$.
  - (d): $N_\ell C_\ell\le2\varepsilon^{-2}S\sqrt{V_\ell C_\ell}+C_\ell$, and $S^2=c_2c_3(\sum r^\ell)^2$ by lemma 4.
  - (e): lemma 6, together with $\max(1,2c_1/\varepsilon)\le(1+2c_1)/\varepsilon$ since $\varepsilon<1$.
  - (f): write $u=-\log\varepsilon>1$. Then $L+1\le\max(x,0)+2$, with $x\le\frac{|\log2c_1|+u}{\alpha\log2}\le\frac{(|\log 2c_1|+1)u}{\alpha\log2}$ and $2\le2u$.
- Numerical check (s02, 4000 random instances with $\beta,\gamma\in[-4,4]$ and $\varepsilon$ from $10^{-14}$ up to $e^{-1}(1-10^{-12})$):
  - (a), (b), (e) and (f) never fail.
  - (c) and (d) "fail" only at relative size $\le10^{-98}$ (at 100 digits). This happens only when $N_\ell$ exceeds the working precision, so these are rounding artefacts at an exact equality.
  - s02b confirms this: there are zero failures when every $N_\ell$ is resolvable at 100 digits.
- Vacuity: not vacuous (for example $\alpha=c_i=1$, $\varepsilon=0.1$).
- Junk values: none. $N_\ell>0$, so there is no division by zero, and $\log\varepsilon<-1$.
- Standard result: this is the choice of $L$ and of the Lagrange-optimal $N_\ell$ in the MLMC complexity theorem.

### 10. `tail_cost_bound` (lemma)

**Rendering.** Let $\alpha,\gamma,c_3,K,\varepsilon>0$ and $L\in\mathbb N$ with $2^{\alpha L}\le K/\varepsilon$. Then

$$c_3\sum_{\ell=0}^{L}(2^\gamma)^\ell\le c_3\frac{2^\gamma}{2^\gamma-1}K^{\gamma/\alpha}\varepsilon^{-\gamma/\alpha}.$$

**Assessment.**
- Truth: true. With $r=2^\gamma>1$, the sum is at most $r^{L+1}/(r-1)$, and $r^L=(2^{\alpha L})^{\gamma/\alpha}\le(K/\varepsilon)^{\gamma/\alpha}$. s01: 20000 checks, no violations.
- Vacuity: not vacuous (for example $L=0$, $K=\varepsilon$).
- Junk values: none, because $\gamma>0$ is assumed. That hypothesis is genuinely needed: at $\gamma=0$ Lean would evaluate $1/0=0$, and the statement would be false.

### 11. `cost_le_of_level` (theorem)

**Rendering.** Fix $\alpha>0$, $\gamma>0$, $c_2,c_3,K>0$ and $\beta\in\mathbb R$ with $\tfrac12\min(\beta,\gamma)\le\alpha$. Then there is $c_4>0$, depending only on $(\alpha,\beta,\gamma,c_2,c_3,K)$, such that the following holds for every $\varepsilon\in(0,e^{-1})$ and every $L\in\mathbb N$ with $2^{\alpha L}\le K/\varepsilon$:

$$2\varepsilon^{-2}c_2c_3\Big(\sum_{\ell=0}^{L}(2^{(\gamma-\beta)/2})^\ell\Big)^2+c_3\sum_{\ell=0}^{L}(2^\gamma)^\ell\le c_4\,\mathrm{cB}(\alpha,\beta,\gamma,\varepsilon).$$

**Assessment.**
- Truth: true. By cases:
  - $\gamma<\beta$: the first sum is at most $1/(1-2^{(\gamma-\beta)/2})$. The tail is at most $C\varepsilon^{-\gamma/\alpha}\le C\varepsilon^{-2}$, because $\gamma\le2\alpha$.
  - $\beta=\gamma$: the first sum is $L+1\le C|\log\varepsilon|$, using $2^{\alpha L}\le K/\varepsilon$ and $|\log\varepsilon|>1$. The tail is at most $C\varepsilon^{-2}\le C\varepsilon^{-2}\log^2\varepsilon$.
  - $\gamma>\beta$: the first sum squared is at most $C2^{(\gamma-\beta)L}\le C(K/\varepsilon)^{(\gamma-\beta)/\alpha}$. The tail $\varepsilon^{-\gamma/\alpha}$ is at most $\varepsilon^{-2-(\gamma-\beta)/\alpha}$ if and only if $\beta\le2\alpha$.
- Numerical check (s03): the supremum over admissible $L$ of LHS/cB stays bounded down to $\varepsilon=10^{-80}$ in 7 parameter sets. These include all three boundary cases $\alpha=\tfrac12\min(\beta,\gamma)$ and a case with $\beta<0$.
- The set that violates the hypothesis ($\alpha=0.4$, $\beta=2$, $\gamma=1$) blows up like $\varepsilon^{-1/2}$, so the hypothesis is needed.
- Vacuity: not vacuous. Junk values: none.
- Standard result: the hypothesis is exactly the standard condition of the MLMC theorem. $\gamma>0$ is not strictly needed here.

### 12. `mimcEta` (def, under `[NeZero D]`)

**Rendering.** $\eta=\max_{d<D}(\gamma_d-\beta_d)/\alpha_d$, computed with `Finset.sup'` over the nonempty `univ`. If some $\alpha_d=0$ that quotient would be 0 by Lean's convention, but theorem 19 assumes $\alpha_d>0$.

### 13. `mimcD2` (def)

**Rendering.** $d_2=\#\{d:(\gamma_d-\beta_d)/\alpha_d=\eta\}$, the number of directions attaining the maximum. It is always at least 1.

### 14. `mimcD3` (def)

**Rendering.** $d_3=\#\{d:\alpha_d=\beta_d/2\}$.

### 15. `mimcBound` (def)

**Rendering.**

$$\varepsilon^{-2}\ (\eta<0);\qquad \varepsilon^{-2}|\log\varepsilon|^{e_1}\ (\eta=0);\qquad \varepsilon^{-2-\eta}|\log\varepsilon|^{e_2}\ (\eta>0).$$

Both powers are `rpow`. The base $|\log\varepsilon|$ exceeds 1 for $\varepsilon<e^{-1}$.

### 16. `mimc_exists_level` (lemma)

**Rendering.** $D$ is arbitrary, and $D=0$ is allowed. Assume $\theta_d>0$, $\delta_d\ge0$, $a>0$ and $c_1>0$. Then there exist $K_P,K_L>0$, depending on $(\theta,\delta,a,c_1,D)$ only, such that for every $\varepsilon\in(0,e^{-1})$ there is an $L\in\mathbb N$ with:

- (i) for every $n$, $c_1\sum_{\ell\in\{0..n-1\}^D,\ \theta\cdot\ell>L}2^{-a\,\theta\cdot\ell-\delta\cdot\ell}\le\varepsilon/2$. This is equivalent to $c_1T(L)\le\varepsilon/2$ for the full tail sum $T(L)$.
- (ii) $2^{aL}\le K_P(1+L)^{(\mathrm{crit}\,\delta-1)^+}/\varepsilon$. The exponent uses natural-number subtraction, and $\mathrm{crit}\,\delta=\#\{d:\delta_d=0\}$.
- (iii) $1+L\le K_L(-\log\varepsilon)$.

**Assessment.**
- Truth: true.
  - Split the coordinates into the $c=\mathrm{crit}\,\delta$ directions with $\delta_d=0$ and the rest, which contribute a summable factor.
  - A unit shell of the $c$-dimensional weighted simplex contains $O((1+L)^{c-1})$ lattice points. Hence $T(L)\le C\,2^{-aL}(1+L)^{(c-1)^+}$.
  - Take the minimal $L$ with $c_1T(L)\le\varepsilon/2$. Minimality gives (ii), and $L=O(\log 1/\varepsilon)$ gives (iii).
- Numerical check (s05): the $K_P$ and $K_L$ that each $\varepsilon$ requires stay bounded (at most 25.6 and 6.95) in five cases, with $D=2,3$, crit $=0,1,2,3$, and $\varepsilon$ down to $10^{-32}$.
- The truncated exponent when crit $=0$: truth does not depend on it. In s05 case 3 even the exponent $-1$ holds, because the tail then decays at the faster rate $a+\min_d\delta_d/\theta_d$.
- $D=0$: (i) reads $0\le\varepsilon/2$, and $L=0$ works.
- Vacuity: not vacuous. Junk values: none.

### 17. `mimc_construction` (lemma)

**Rendering.** Assume $\theta_d>0$, $\delta_d\ge0$ and $a,c_1,c_2,c_3>0$, with $\alpha_d=a\theta_d+\delta_d$ and $g_d=\tfrac12\gamma_d-\tfrac12\beta_d$. Here $\beta$ and $\gamma$ are arbitrary. Then there exist $K_P,K_L>0$ such that for every $\varepsilon\in(0,e^{-1})$ there are $L\in\mathbb N$ and $N:\mathbb N^D\to\mathbb N$ with $N>0$ satisfying the following, where $\mathcal L=\mathrm{indexSet}\,\theta\,L=\{\ell:\theta\cdot\ell\le L\}$:

- Bias: $c_1\sum_{\ell\in s\setminus\mathcal L}2^{-\alpha\cdot\ell}\le\varepsilon/2$ for every finite $s$.
- Variance: $\sum_{\mathcal L}c_22^{-\beta\cdot\ell}/N_\ell\le\varepsilon^2/2$.
- Cost: $\sum_{\mathcal L}N_\ell c_32^{\gamma\cdot\ell}\le2c_2c_3\varepsilon^{-2}\big(\sum_{\mathcal L}2^{g\cdot\ell}\big)^2+c_3\sum_{\mathcal L}2^{\gamma\cdot\ell}$.
- Conditions (ii) and (iii) of lemma 16.

**Assessment.**
- Truth: true.
  - $L$ comes from lemma 16. Because $\theta>0$, `indexSet` equals $\{\theta\cdot\ell\le L\}$ exactly.
  - Any finite $s\setminus\mathcal L$ lies in some $\mathrm{box}\cap\{\theta\cdot\ell>L\}$, and $2^{-\alpha\cdot\ell}=2^{-a\theta\cdot\ell-\delta\cdot\ell}$.
  - $N$ is given by the Lagrange formula, with $\sqrt{V_\ell C_\ell}=\sqrt{c_2c_3}\,2^{g\cdot\ell}$.
- Vacuity: not vacuous. Junk values: none.
- The odd forms `1 * δ d` and `(1/2) * γ d + (-1/2) * β d` are harmless.

### 18. `mimc_level_power` (lemma)

**Rendering.** Let $a>0$, $b\ge0$, $K,K_L,\varepsilon>0$, $t\ge0$ and $q\ge0$ be reals, and let $p,L\in\mathbb N$. If $2^{aL}\le K(1+L)^p/\varepsilon$ and $1+L\le K_Lt$, then

$$(1+L)^q2^{bL}\le K^{b/a}K_L^{\,q+pb/a}\,t^{\,q+pb/a}\,\varepsilon^{-b/a}.$$

**Assessment.**
- Truth: true.
  - Raise the first hypothesis to the power $b/a\ge0$; rpow is monotone on nonnegative bases.
  - Multiply by $(1+L)^q$.
  - Bound $(1+L)^{q+pb/a}\le(K_Lt)^{q+pb/a}$.
  - s01: no violations in 20000 samples; the ratio reaches exactly 1, so equality is attainable.
- Vacuity: not vacuous. Junk values: none. $t>0$ is forced by the second hypothesis.

### 19. `mimc_complexity` (theorem)

**Rendering.** Assume $D\ge1$ and, for every $d$: $\alpha_d>0$, $\gamma_d>0$ and $\beta_d/2<\alpha_d$ (strict). Assume $c_1,c_2,c_3>0$. Then there is $c_4>0$, depending only on $(\alpha,\beta,\gamma,c_1,c_2,c_3)$, such that for every $\varepsilon\in(0,e^{-1})$ there exist a finite $\mathcal L\subset\mathbb N^D$ and $N:\mathbb N^D\to\mathbb N_{>0}$ with:

- $c_1\sum_{\ell\notin\mathcal L}2^{-\alpha\cdot\ell}\le\varepsilon/2$, stated as a bound on every finite partial sum.
- $\sum_{\mathcal L}c_22^{-\beta\cdot\ell}/N_\ell\le\varepsilon^2/2$.
- $\sum_{\mathcal L}N_\ell\,c_32^{\gamma\cdot\ell}\le c_4\cdot\mathrm{mimcBound}(\eta,2d_2,(d_2-1)(2+\eta),\varepsilon)$. That is, at most $c_4\varepsilon^{-2}$ if $\eta<0$; $c_4\varepsilon^{-2}|\log\varepsilon|^{2d_2}$ if $\eta=0$; and $c_4\varepsilon^{-2-\eta}|\log\varepsilon|^{(d_2-1)(2+\eta)}$ if $\eta>0$.

**Assessment.** True. My own proof sketch follows.

- **Choice of weights.** Let $g=(\gamma-\beta)/2$ and $\theta=\alpha+g$.
  - $\theta_d=(\alpha_d-\beta_d/2)+\gamma_d/2>0$. This uses both the strict hypothesis and $\gamma_d>0$.
  - With $x_d=g_d/\alpha_d$, so that $\max_d x_d=\eta/2$: $\alpha_d/\theta_d=1/(1+x_d)$ and $g_d/\theta_d=x_d/(1+x_d)$.
  - So $a=\min\alpha_d/\theta_d=1/(1+\eta/2)$ and $\max_d g_d/\theta_d$ are attained on the same $d_2$ directions. This gives $\mathrm{crit}\,\delta=d_2$ and $2\max(g/\theta)/a=\eta$.
- **Level and index set.** Lemmas 16 and 17 give $\mathcal L=\{\theta\cdot\ell\le L\}$ with $2^{aL}\lesssim(1+L)^{d_2-1}/\varepsilon$ and $1+L\lesssim|\log\varepsilon|$.
- **Main term.**
  - $\eta>0$: $(\sum_{\mathcal L}2^{g\cdot\ell})^2\lesssim2^{\eta aL}(1+L)^{2(d_2-1)}\lesssim\varepsilon^{-\eta}|\log\varepsilon|^{(d_2-1)(2+\eta)}$, using lemma 18.
  - $\eta=0$: the square is $\lesssim(1+L)^{2d_2}$.
  - $\eta<0$: the square is bounded.
- **Rounding term.** $c_3\sum_{\mathcal L}2^{\gamma\cdot\ell}\lesssim(1+L)^D2^{mL}$ with $m=\max_d\gamma_d/\theta_d$.
  - $m/a<2+\max(\eta,0)$ strictly. When $\eta\ge0$ this is exactly $\beta_d<2\alpha_d$; when $\eta<0$ it is automatic.
  - So the polylog factor is absorbed.
- **Numerical checks** (s06 and s06b), comparing the witness cost upper bound with mimcBound:
  - The ratio stays bounded in 9 parameter sets: $D=2,3$; $\eta<0$, $=0$, $>0$; $d_2=1,2$; and a near-boundary case. It was tested down to $\varepsilon=10^{-40}$, and down to $10^{-150}$ in two cases (log-log slopes $-0.04$ and $0.04$).
  - Exact integer-$N$ checks confirm the bias, variance and cost inequalities.
  - The naive $\theta=\alpha$ grows by one extra $|\log\varepsilon|$ factor (slope 0.92). So the claimed exponents are non-trivial.
- **Vacuity:** not vacuous. For example, $D=1$ and $\alpha=\beta=\gamma=1$ gives the MLMC case $\beta=\gamma$ with bound $\varepsilon^{-2}|\log\varepsilon|^2$.
- **Junk values:** none. mimcBound is positive on the range.
- **Hypotheses:**
  - The strict $\beta_d<2\alpha_d$ is stronger than the published condition. It excludes $d_3\ge1$; see main point 2 and s07.
  - $\gamma_d>0$ is standard.
- **Standard result:** the MIMC complexity theorem (Haji-Ali, Nobile & Tempone 2016, Thm 2.2; as restated in Giles, Acta Numerica 2015), restricted to $d_3=0$. This declaration is the deterministic, budget-level half.

### 20. `integrable_integral_crossDiff` (theorem)

**Rendering.** Let $\mu$ be any measure; a probability measure is *not* required. For every $D$ and every family $P_\ell$ ($\ell\in\mathbb N^D$) of integrable functions, and every $\ell$:
- $\omega\mapsto\Delta_\ell(P_\cdot(\omega))$ is integrable, and
- $\int\Delta_\ell P\,d\mu=\Delta_\ell\big(\int P_\cdot\,d\mu\big)$.

**Assessment.**
- Truth: true. $\Delta_\ell$ is a finite signed combination whose coefficients do not depend on $\omega$; induct on $D$ using `integral_sub`. s04 checks this exactly on finite measure spaces that are not probability spaces.
- Vacuity: not vacuous.
- Junk values: none. Integrability is part of the conclusion, so the identity is not a $0=0$ artefact.

### 21. `mimc_mse_cost_of` (theorem)

**Rendering.** $(\Omega,\mu)$ is a probability space (see main point 4), and $D\ge0$ is arbitrary. The data are:
- a target $P$ and approximations $P_\ell$;
- estimators $Y_\ell^{(n)}$ built from $n$ samples;
- random costs $\mathrm{Cost}_\ell^{(n)}$;
- numbers $V_\ell$ and $C_\ell$;
- rates $\alpha,\beta,\gamma$ and constants $c_1,c_2,c_3$, $\varepsilon>0$ and $b$.

Given a finite $\mathcal L$ and $N>0$ satisfying three budgets:
- bias: as in 19;
- variance: $\sum_{\mathcal L}c_22^{-\beta\cdot\ell}/N_\ell\le\varepsilon^2/2$;
- cost: $\sum_{\mathcal L}N_\ell c_32^{\gamma\cdot\ell}\le b$.

And given the following modelling assumptions:
- $P$ and every $P_\ell$ are integrable.
- $Y_\ell^{(n)}\in L^2$ for $n>0$.
- For every positive $N$, the family $(Y_\ell^{(N_\ell)})_\ell$ is pairwise independent.
- Every cost is integrable, with $\mathbb E\,\mathrm{Cost}_\ell^{(n)}=nC_\ell$.
- $\mathrm{Var}\,Y_\ell^{(n)}=V_\ell/n$.
- (i) $\mathbb E[P_\ell-P]\to0$ as $\min_d\ell_d\to\infty$ (uniformly over all such $\ell$).
- (iii) $\mathbb EY_\ell^{(n)}=\mathbb E\,\Delta_\ell P$.
- (ii) $|\mathbb EY_\ell^{(n)}|\le c_12^{-\alpha\cdot\ell}$.
- (iv) $V_\ell\le c_22^{-\beta\cdot\ell}$.
- (v) $C_\ell\le c_32^{\gamma\cdot\ell}$.

Then:
- $\mathbb E\big[(\sum_{\mathcal L}Y_\ell^{(N_\ell)}-\mathbb EP)^2\big]<\varepsilon^2$, and
- $\mathbb E\sum_{\mathcal L}\mathrm{Cost}_\ell^{(N_\ell)}\le b$.

The term $\mathbb EP$ is subtracted once, outside the sum, as intended; this follows from the `term:67` rule for `∑`.

**Assessment.**
- Truth: true.
  - MSE $=$ Var $+$ bias².
  - By pairwise independence, Var $=\sum V_\ell/N_\ell\le\varepsilon^2/2$, using (iv) and the variance budget.
  - For the bias, the telescoping identity $\sum_{\ell\in\mathrm{box}(n)}\Delta_\ell p=p(n-1,\dots,n-1)$ (s04) together with (i) gives $\mathbb EP=\lim_n\sum_{\mathrm{box}(n)}\mathbb E\Delta_\ell P$.
  - Hence $|\mathbb EP-\sum_{\mathcal L}\mathbb EY_\ell|\le\sup_s c_1\sum_{s\setminus\mathcal L}2^{-\alpha\cdot\ell}\le\varepsilon/2$, using (ii) and (iii).
  - So MSE $\le3\varepsilon^2/4<\varepsilon^2$. The cost bound follows by linearity and (v).
  - $D=0$, which is plain Monte Carlo, also works.
- Vacuity: not vacuous. For example, take an infinite product of standard Gaussians with $Y_\ell^{(n)}=a_\ell+\frac{\sigma_\ell}{n}\sum_{i<n}\xi_{\ell,i}$ on disjoint coordinates, deterministic $P_\ell=\sum_{k\le\ell}a_k$ ($D=1$), $a_k=2^{-k}$, $\sigma_\ell^2=2^{-2\ell}$ and costs $n2^\ell$.
- Junk values: none. Under a probability measure every integrand is integrable.
- Hypotheses: `hind` over all $N$ is a strong but natural modelling assumption.

### 22. `mimc_mse_cost` (theorem)

**Rendering.** Take the same modelling hypotheses as 21. Assume also `hdet`: there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there are $\mathcal L$ and $N>0$ meeting the bias and variance budgets, with cost-rate sum at most $c_4B(\varepsilon)$, where $B:\mathbb R\to\mathbb R$ is arbitrary. Then there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there are $\mathcal L$ and $N>0$ with MSE $<\varepsilon^2$ and expected cost at most $c_4B(\varepsilon)$.

**Assessment.**
- Truth: true; it follows immediately from 21 with $b=c_4B(\varepsilon)$.
- Vacuity: not vacuous. Theorem 19 supplies `hdet` with $B=\mathrm{mimcBound}(\eta,2d_2,(d_2-1)(2+\eta),\cdot)$, which gives the probabilistic MIMC complexity theorem.
- Junk values: none.

### 23. `mimcD3_eq_zero` (lemma)

**Rendering.** If $\beta_d/2<\alpha_d$ for every $d$, then $\#\{d:\alpha_d=\beta_d/2\}=0$.

**Assessment.** Trivially true, since the filter is empty. It is not vacuous, and no junk values are involved. It records that the strict hypothesis of 19 removes the $d_3$ term.

### 24. `crossDiff` (def, appended)

**Rendering.** $\Delta_\ell p=\sum_{S\subseteq\{d:\ell_d>0\}}(-1)^{|S|}p(\ell-e_S)$. This is the first-order mixed backward difference; directions with $\ell_d=0$ are not differenced. s04 checks this against the recursion exactly, and also the telescoping of the box sum to $p$ at the corner.

### 25. `dot` (def)

**Rendering.** $a\cdot\ell=\sum_d a_d\ell_d$.

### 26. `box` (def)

**Rendering.** $\mathrm{box}\,D\,n=\{0,\dots,n-1\}^D$. For $D=0$ it is the singleton $\{()\}$ for every $n$.

### 27. `crit` (def)

**Rendering.** $\#\{d:\delta_d=0\}$.

### 28. `indexSet` (def)

**Rendering.** $\{\ell\in\prod_d\{0,\dots,\lfloor L/\theta_d\rfloor_+\}:\theta\cdot\ell\le L\}$.
- If every $\theta_d>0$, this equals $\{\ell\in\mathbb N^D:\theta\cdot\ell\le L\}$ for every real $L$; both are empty when $L<0$.
- If some $\theta_d=0$, then $L/0=0$ in Lean and that coordinate collapses to $\{0\}$, which is not the mathematical set. Every use in the packet assumes $\theta_d>0$.

## Scripts (in `readback/round10/work_L3/`)

| script | purpose | result |
|---|---|---|
| `s01_basic_lemmas` | random checks of 4, 6, 10, 18 | no violations |
| `s02_exists_L_N` | standard witness for 9, 4000 random instances | (a), (b), (e), (f) always hold; (c) and (d) only rounding-level excess |
| `s02b_exists_L_N_rounding` | confirms the s02 excess is rounding at an exact equality | excess $\le10^{-98}$ at 100 digits; 0 failures when resolvable |
| `s03_cost_le_of_level` | sup of LHS/cB for $\varepsilon$ down to $10^{-80}$ | bounded under the hypothesis; the violating case grows like $\varepsilon^{-1/2}$ |
| `s04_crossdiff` | exact checks: formula, telescoping, integral commutation | all true |
| `s05_mimc_exists_level` | required $K_P$ and $K_L$ versus $\varepsilon$ | bounded; the crit $=0$ case works even with exponent $-1$ |
| `s06_mimc_complexity` | witness cost/mimcBound, 9 parameter sets | bounded with $\theta=\alpha+g$; the naive $\theta=\alpha$ grows |
| `s06b_mimc_phase_check` | $\varepsilon$ down to $10^{-150}$ | slope ≈ 0 with $\theta=\alpha+g$; slope 0.92 with naive weights |
| `s07_d3_illustration` | excluded equality case $d_3=2$ (illustrative only) | the natural witness picks up a factor $\propto L$ |
