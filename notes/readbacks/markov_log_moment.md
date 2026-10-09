# Blind read-back R53: `MlmcLean.MarkovLogMoment` (log-moment convergence of $X_{n+1}=cX_n+\xi_n$)

| Field | Value |
|---|---|
| Date | 2026-10-09 |
| Packet | `readback/round28/packet_R53_logmoment.lean` |
| Declarations audited | 11 (10 theorems + 1 definition) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `/tmp/claude-0/-home-user-mlmc-lean/8f263d87-ec2c-550e-ae99-ab3862cfe2e3/scratchpad/readback/round28/work_R53_logmoment` |

Files in the scripts directory:
- `scratch1.lean`/`.out`: the packet compiled with `sorry` under `import MlmcLean`, with the elaborated statements printed. It also has `rfl` checks of the parsing: `Real.log t ^ 2 = (Real.log t)^2`, `dist … ^ p` is `Real.rpow`, `dist x₀ (halfStep x₀ e) = |e - x₀/2|`, and two-step unfoldings of `backIter`/`fwdIter`.
- `scratch2.lean`/`.out`: shows that `u ↦ exp(1/√u)` is measurable, `IsProbabilityMeasure logSqTailLaw`, $\mathrm{vol}|_{(0,1)}(-\infty,0]=0$, the Lean junk values used, and `ofReal (log |e|) = ofReal (max 0 (log |e|))`. Exit 0.
- `scratch3.lean`/`.out`: proves the exact statement of `exists_iid_logSqTailLaw` (axioms: `propext`, `Classical.choice`, `Quot.sound`) and gives a Lean-checked instance for the hypotheses of theorems 1 and 2. Exit 0.
- `check_tail.py`/`.out`: the tail formula, checked exactly by bisection and by Monte Carlo, plus a check that the formula fails for $t<e$.
- `check_moments.py`/`.out`: the log moment ($\approx 2.19410$, computed two ways) and the blow-up of the power moments.
- `check_ineq.py`/`.out`: the pointwise inequalities behind theorems 3 and 4, on 200 000 random cases each.
- `simulate.py`/`.out`: sample paths of $\sum_j \xi_j/2^j$ for `logSqTailLaw` noise, and for contrast noise $e^{1/U}$, which has an infinite log moment.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `tendstoInDistribution_fwdIter_affine` | theorem | true | no | no |
| 2 | `tendstoInDistribution_fwdIter_halfStep_of_log` | theorem | true | no | no |
| 3 | `lintegral_log_one_add_abs_ne_top_iff` | theorem | true | no | no |
| 4 | `lintegral_log_ne_top_of_hc` | theorem | true | no | no |
| 5 | `logSqTailLaw` | definition | well-formed: a probability measure, the law of $e^{1/\sqrt U}$ | n/a | no (the map is not the junk zero measure; values off $(0,1)$ sit on a null set) |
| 6 | `logSqTailLaw_Ioi` | theorem | true | no | no |
| 7 | `lintegral_log_logSqTailLaw_ne_top` | theorem | true | n/a (no hypotheses) | no |
| 8 | `lintegral_logSqTailLaw_eq_top` | theorem | true | no | no (a genuine $\top$) |
| 9 | `exists_iid_logSqTailLaw` | theorem | true (proved in scratch Lean) | n/a | no |
| 10 | `tendstoInDistribution_fwdIter_logSqTailLaw` | theorem | true | no (#9 gives an instance) | no |
| 11 | `halfStep_log_moment_strictly_weaker` | theorem | true; it does separate the two conditions | n/a | no |

## Main points for a human auditor

- I found no statement that is false, vacuous, or true only because of a junk value.
- **The separation in #11 is real.** Part (a) says: for every finite $\nu$, every $p>0$ and every $x_0$, a finite first-step $p$-moment implies a finite log moment. Part (b) gives a probability measure ($\nu$ = `logSqTailLaw` works) whose log moment is finite but whose first-step $p$-moment is $\infty$ for **every** $x_0$ and **every** $p>0$. So the converse fails even in its weakest form ("for some $x_0$ and some $p$"). The explicit `IsProbabilityMeasure ν` rules out the degenerate $\nu=0$, for which every lintegral is $0$.
  - Part (a) repeats #4 verbatim apart from binder order.
  - The convergence clause in part (b) only says $\exists X\,\forall x_0$, laws of the forward iterates converge weakly to the law of $X$. $X$ is not tied to the series, so this is weaker than #10, but still a genuine statement.
- **`ofReal (Real.log |e|)` in #3 is exactly $\log^+|e|$.** `ofReal` clips negative values to $0$, and Lean's `Real.log 0 = 0` agrees with the usual $\log^+0 = 0$. I confirmed the identity in Lean. This is the intended $\log^+$ moment, not a junk artefact.
- **`logSqTailLaw` is a genuine probability measure.** I checked in Lean that the map function is measurable and that the measure is a probability measure. Off $(0,1)$ the Lean function takes junk values ($u\le0$: $\sqrt u=0$, $1/0=0$, $e^0=1$), but the measure is restricted to $(0,1)$, so they don't matter. The support is $(e,\infty)$ and $P(E>t)=(\log t)^{-2}$ for $t\ge e$.
- **The hypothesis $t\ge e$ in #6 is needed and not superfluous.** For $t=2$ the formula gives $1/\log^2 2\approx2.08$, but the true value is $1$. At $t=0$ the junk value $\log 0=0$ would give $0$ against a true value of $1$; the hypothesis excludes this.
- **`TendstoInDistribution` (Mathlib) carries `forall_aemeasurable` and `aemeasurable_limit` fields**, and its `tendsto` field is weak convergence in `ProbabilityMeasure ℝ`. So #10 and #11(b), which omit `AEMeasurable X`, lose nothing.
- **#1 and #2 state only the sufficiency half of the sharp perpetuity criterion.** The log-moment hypothesis is not stronger than needed: for $c\neq0$ and $\nu\neq\delta_0$, an infinite $\log^+$ moment makes the series diverge a.s. by the second Borel–Cantelli lemma (illustrated in `simulate.out`, case B). $X$ is chosen before $x_0$, and the a.s. set for the backward iterates may depend on $x_0$.
- **`IsFiniteMeasure ν` in #3 (direction ⇐) and in #4 is needed.** Counterexamples with infinite $\nu$ are given below.

---

## 1. `tendstoInDistribution_fwdIter_affine`

**Rendering.**

Setting: $(\Omega,\mu)$ is a probability space, $\nu$ a measure on $\mathbb R$, $\xi=(\xi_i)_{i\in\mathbb N}$ real functions on $\Omega$, and $c\in\mathbb R$.

Hypotheses:
- $|c|<1$;
- the $\xi_i$ are mutually independent under $\mu$ (`iIndepFun`);
- every $\xi_i$ is measurable;
- $\mu\circ\xi_i^{-1}=\nu$ for all $i$, so $\nu$ is a probability measure and the $\xi_i$ are iid with law $\nu$;
- $\int\log(1+|e|)\,\nu(de)<\infty$. Here `ofReal` changes nothing, because $\log(1+|e|)\ge0$.

Conclusion: there is one function $X:\Omega\to\mathbb R$, chosen before $x_0$, such that:
- $X$ is $\mu$-a.e. measurable;
- for $\mu$-a.e. $\omega$, `HasSum` holds for $\sum_{j\ge0}c^j\xi_j(\omega)$ with sum $X(\omega)$. In $\mathbb R$ this is unconditional, hence absolute, convergence. Here $c^j$ is the monoid power, so $0^0=1$.
- for every $x_0\in\mathbb R$, both of the following hold:
  - (i) For $\mu$-a.e. $\omega$ (the null set may depend on $x_0$), the backward iterates converge: $B_n(\omega)\to X(\omega)$. From `backIter φ (n+1) e x = φ (backIter φ n (e ∘ succ) x) (e 0)` we get $B_n=\sum_{j<n}c^j\xi_j+c^nx_0$.
  - (ii) The forward iterates $F_0=x_0$, $F_{n+1}=cF_n+\xi_n$, that is $F_n=c^nx_0+\sum_{k<n}c^{n-1-k}\xi_k$, converge in distribution to $X$ under $\mu$. This means every $F_n$ and $X$ are a.e.-measurable and $\mathrm{law}(F_n)\to\mathrm{law}(X)$ weakly.

**Assessment.**

*Truth: true.*
- If $c=0$, take $X=\xi_0$: then $B_n=\xi_0$ for $n\ge1$ and $F_n=\xi_{n-1}\sim\nu$.
- If $c\ne0$, pick $\varepsilon>0$ with $|c|e^{\varepsilon}<1$. Then $\sum_{j\ge1}P(\log(1+|\xi_j|)>\varepsilon j)\le E\log(1+|\xi_0|)/\varepsilon<\infty$. By the first Borel–Cantelli lemma, a.s. $|\xi_j|\le e^{\varepsilon j}$ eventually, so $\sum|c|^j|\xi_j|<\infty$ a.s. and `HasSum` holds.
- Take $X:=\sum'$, the a.e. limit of measurable partial sums; it is AEMeasurable.
- (i) holds because $B_n$ is a partial sum plus $c^nx_0\to0$.
- (ii) holds because $(\xi_0,\dots,\xi_{n-1})$ is iid, hence exchangeable, so $F_n\overset d=B_n$. Then $\mathrm{law}(F_n)=\mathrm{law}(B_n)\to\mathrm{law}(X)$, since a.s. convergence implies convergence in distribution.

*Vacuity: not vacuous.*
- A degenerate instance, checked in Lean (`scratch3`): $\Omega=\mathbb R^{\mathbb N}$, $\mu=$ `infinitePi (dirac 0)`, $\xi_i=$ the $i$-th coordinate, $\nu=\delta_0$, $c=1/2$.
- A non-degenerate instance: $\nu=$ `logSqTailLaw` with the product construction of #9; its log moment is $\approx2.194$.

*Junk values: none.*
- The integrand is $\ge0$.
- `HasSum` is genuine summability, not a `tsum` junk value.
- `TendstoInDistribution` contains the measurability fields.
- `μ.map (ξ i)` cannot be the junk zero measure, because `Measurable (ξ i)` is assumed.

*Hypotheses.*
- `Measurable` rather than `AEMeasurable` is slightly stronger than needed; this is standard.
- The log moment is the sharp condition. Simulation case B, with noise $e^{1/U}$, shows the partial sums never settling.
- Stating convergence in distribution for each $x_0$ separately is fine.

*Standard result:* the sufficiency half of the perpetuity criterion (Vervaat 1979; Goldie–Maller 2000: $\sum c^j\xi_j$ converges a.s. iff $E\log^+|\xi|<\infty$, for $0<|c|<1$ and $\xi\not\equiv0$), together with Letac's backward-iteration principle.

## 2. `tendstoInDistribution_fwdIter_halfStep_of_log`

**Rendering.** This is #1 with $c=1/2$ written through `halfStep x e = x/2 + e`.
- Hypotheses: iid $\xi_i$ with law $\nu$ and $\int\log(1+|e|)\,d\nu<\infty$.
- Conclusion: $\exists X$, a.e.-measurable, such that:
  - a.s. `HasSum` holds for $\sum_j\xi_j/2^j$ with sum $X$;
  - for every $x_0$, a.s. $B_n=\sum_{j<n}\xi_j/2^j+x_0/2^n\to X$;
  - for every $x_0$, the forward iterates $F_{n+1}=F_n/2+\xi_n$, $F_0=x_0$, converge in distribution to $X$.

**Assessment.**
- Truth: true. It is the special case $c=1/2$ of #1 ($c^j\xi_j=\xi_j/2^j$, and `halfStep` is $x\mapsto x/2+e$).
- Vacuity: not vacuous; the same instances as #1 apply.
- Junk values: none.
- Hypotheses: natural.
- Standard result: as #1.

## 3. `lintegral_log_one_add_abs_ne_top_iff`

**Rendering.** For every finite measure $\nu$ on $\mathbb R$:
$$\int\log(1+|e|)\,d\nu<\infty\iff\int\log^+|e|\,d\nu<\infty.$$
The right-hand integrand is `ofReal (Real.log |e|)`. This is $\max(0,\log|e|)$ for $e\ne0$, and $0$ at $e=0$ (Lean's $\log0=0$). Both cases equal $\log^+|e|$; the identity is checked in Lean.

**Assessment.**

*Truth: true.* For $x\ge0$ we have $\log^+x\le\log(1+x)\le\log^+x+\log2$, because $1+x\le2\max(1,x)$; this is checked numerically in `check_ineq.out` (1). The two integrals therefore differ by at most $\nu(\mathbb R)\log2<\infty$.

*Vacuity: not vacuous.* For example, $\nu=\delta_0$, where both sides are true.

*Junk values:* $\log0=0$ at $e=0$ coincides with the mathematical $\log^+0=0$, so nothing depends on it.

*Hypotheses:* `IsFiniteMeasure` is needed for ⇐. With $\nu=\sum_n\delta_{1/n}$, the $\log^+$ integral is $0$ but $\sum_n\log(1+1/n)=\infty$. The ⇒ direction holds for any $\nu$.

*Standard result:* the elementary equivalence $E\log(1+|\xi|)<\infty\iff E\log^+|\xi|<\infty$.

## 4. `lintegral_log_ne_top_of_hc`

**Rendering.** Let $\nu$ be a finite measure on $\mathbb R$, $p>0$ real and $x_0\in\mathbb R$.
- Hypothesis: $\int d(x_0,\mathrm{halfStep}(x_0,e))^p\,\nu(de)=\int|e-x_0/2|^p\,\nu(de)<\infty$. The power is `Real.rpow` of a nonnegative base, and $0^p=0$ since $p>0$.
- Conclusion: $\int\log(1+|e|)\,d\nu<\infty$.

**Assessment.**

*Truth: true.*
- Pointwise, $\log(1+|e|)\le C_p\,(1+|e-a|^p+|a|^p)$ with $a=x_0/2$ and $C_p=\max(1,2^{p-1})^2/p$.
- This follows from $\log y\le y^p/p$ and $(s+t)^p\le\max(1,2^{p-1})(s^p+t^p)$; it is checked on 200 000 random cases in `check_ineq.out` (2).
- Integrate, using that $\nu$ is finite.

*Vacuity: not vacuous.* For example, $\nu=\delta_0$, $p=1$, $x_0=0$.

*Junk values: none.*

*Hypotheses:* finiteness of $\nu$ is needed. Take $\nu=\sum_n n^2\delta_{1/n}$, $x_0=0$, $p=4$: the hypothesis is $\sum n^{-2}<\infty$, but $\sum n^2\log(1+1/n)=\infty$.

*Standard result:* a power moment implies a log moment. This is the comparison between the Diaconis–Freedman (1999, Thm 1) "algebraic tail" condition $\int\rho(x_0,f_\theta(x_0))^p<\infty$ and the log-moment condition.

## 5. `logSqTailLaw` (definition)

**Rendering.** $\mathrm{logSqTailLaw}=(\mathrm{Leb}|_{(0,1)})\circ f^{-1}$ with $f(u)=\exp(1/\sqrt u)$. In other words it is the law of $E=e^{U^{-1/2}}$ with $U\sim\mathrm{Unif}(0,1)$.

**Assessment.**
- On $(0,1)$ the map takes values in $(e,\infty)$.
- Off $(0,1)$ the Lean function takes junk values ($u\le0$: $\sqrt u=0$, $1/0=0$, $f=1$), but the restricted measure gives these points mass $0$ (checked in Lean).
- $f$ is measurable (`fun_prop`), so `Measure.map` is the true pushforward and not the junk $0$.
- `IsProbabilityMeasure logSqTailLaw` is proved in `scratch2`.
- The name fits: $P(E>t)=(\log t)^{-2}$, which is #6.

## 6. `logSqTailLaw_Ioi`

**Rendering.** For real $t\ge e$: $\mathrm{logSqTailLaw}((t,\infty))=\mathrm{ofReal}\big(1/(\log t)^2\big)$. The `^2` applies to $\log t$, as checked by `rfl`.

**Assessment.**

*Truth: true.* Since $\log t\ge1>0$, we have $\{u\in(0,1):e^{1/\sqrt u}>t\}=\{u\in(0,1):\sqrt u<1/\log t\}=(0,(\log t)^{-2})$. Its Lebesgue measure is $(\log t)^{-2}\in(0,1]$, because $(\log t)^{-2}\le1$. In `check_tail.out` the bisection value agrees with the formula to 15 digits for $t\in\{e,\,3,\,10,\,100,\,10^{10},\,10^{100}\}$, and Monte Carlo agrees too.

*Vacuity: not vacuous.* For example $t=e$, where the value is $1$, or $t=10$.

*Junk values: none.* `ofReal` of a positive number.

*Hypotheses:* $t\ge e$ is exactly the right condition. For $t<e$ the formula fails: at $t=2$ it gives $2.08$ against a true value of $1$. At $t=0$, Lean's $\log0=0$ would give $0$ against $1$.

*Standard result:* a tail computation by inverse-transform sampling.

## 7. `lintegral_log_logSqTailLaw_ne_top`

**Rendering.** $\int\log(1+|e|)\,d\,\mathrm{logSqTailLaw}(e)<\infty$.

**Assessment.**
- Truth: true. By `lintegral_map` the integral is $\int_0^1\log(1+e^{1/\sqrt u})\,du\le\log2+\int_0^1u^{-1/2}\,du=\log2+2$. Numerically it is $2.1941006\ldots$ (computed two ways in `check_moments.out`). Also $E\log^+E=E[U^{-1/2}]=2$.
- Vacuity: n/a (no hypotheses).
- Junk values: none. The statement is not trivial, because the measure is a probability measure and not $0$.
- Standard result: an elementary computation.

## 8. `lintegral_logSqTailLaw_eq_top`

**Rendering.** For every $x_0\in\mathbb R$ and every real $p>0$: $\int|e-x_0/2|^p\,d\,\mathrm{logSqTailLaw}(e)=\infty$.

**Assessment.**
- Truth: true. For $e\ge|x_0|$ we have $|e-x_0/2|\ge e/2$. Also $E[E^p]=\int_0^1e^{p/\sqrt u}\,du=\int_1^\infty2e^{pv}v^{-3}\,dv=\infty$, and the region $e<|x_0|$ contributes only a finite amount. Equivalently, $P(E^p>s)=p^2/(\log s)^2$, which is not integrable in $s$.
- Numerically, the truncated integrals for $p\in\{0.01,\,0.1,\,1\}$ and $a\in\{0,\pm5,1000\}$ blow up (`check_moments.out`).
- Vacuity: not vacuous; $p=1$, $x_0=0$.
- Junk values: none. This is a genuine $\top$ of a measurable, pointwise-finite, nonnegative integrand.
- Standard result: a slowly varying ($\log^{-2}$) tail has no power moments.

## 9. `exists_iid_logSqTailLaw`

**Rendering.** There exist a type $\Omega$ in `Type` (universe 0), a σ-algebra on it, a probability measure $\mu$, and functions $\xi_i:\Omega\to\mathbb R$ that are mutually independent and measurable, each with law `logSqTailLaw`.

**Assessment.**
- Truth: true. I proved this exact statement in Lean (`scratch3`) with $\Omega=\mathbb R^{\mathbb N}$, $\mu=$ `Measure.infinitePi (fun _ => logSqTailLaw)` and $\xi_i=$ coordinate $i$, using Mathlib's `iIndepFun_infinitePi` and `infinitePi_map_eval`. Axioms used: `propext`, `Classical.choice`, `Quot.sound`.
- Vacuity: n/a.
- Junk values: none.
- Standard result: existence of iid sequences via a countable product of probability measures (Kolmogorov / Ionescu-Tulcea).

## 10. `tendstoInDistribution_fwdIter_logSqTailLaw`

**Rendering.** Take any probability space and $\xi_i$ that are iid, measurable, with law `logSqTailLaw`. Then $\exists X$ such that:
- a.s. `HasSum` holds for $\sum_j\xi_j/2^j$ with sum $X$;
- for every $x_0$, the forward `halfStep` iterates converge in distribution to $X$.

**Assessment.**
- Truth: true. It follows from #2 with #7. The measurability of $X$ is contained in `TendstoInDistribution.aemeasurable_limit`.
- Vacuity: not vacuous; #9 supplies an instance.
- Junk values: none.
- Supporting evidence: in `simulate.out` (case A), six sample paths settle after at most about 40 terms. The Borel–Cantelli sum $\sum_jP(U^{-1/2}>j\log2/2)\approx5.29$ is finite.
- Standard result: an application of #2.

## 11. `halfStep_log_moment_strictly_weaker`

**Rendering.** This is the conjunction of (a) and (b).

(a) For every finite measure $\nu$ on $\mathbb R$, every $p,x_0\in\mathbb R$ with $p>0$: if $\int|e-x_0/2|^p\,d\nu<\infty$ then $\int\log(1+|e|)\,d\nu<\infty$.

(b) There is a probability measure $\nu$ on $\mathbb R$ such that all of the following hold:
- $\int\log(1+|e|)\,d\nu<\infty$;
- for every $x_0$ and every $p>0$, $\int|e-x_0/2|^p\,d\nu=\infty$;
- there exist a probability space $(\Omega:\mathsf{Type},\mu)$ and $\xi_i$ that are mutually independent, measurable, with law $\nu$, and a single $X$ such that for every $x_0$ the forward `halfStep` iterates converge in distribution to $X$.

**Assessment.**

*Truth: true.* Part (a) is #4. For part (b), take $\nu=$ `logSqTailLaw` and use #5 (probability measure), #7, #8, #9 and #10.

*Separation: genuine.*
- (a) gives "power moment ⇒ log moment" for every finite $\nu$.
- (b) gives a probability $\nu$ satisfying the log condition while violating the power condition for every $(x_0,p)$. So the converse fails even for the weakest form, $\exists x_0\,\exists p>0$.
- Requiring a probability measure blocks the junk witness $\nu=0$.
- The convergence clause shows the log-moment theorem actually applies to this $\nu$.

*Remarks.*
- (a) duplicates #4.
- The convergence clause in (b) only asserts weak convergence of laws to some law realised on $(\Omega,\mu)$, with no link to the series. This is weaker than #10, but still a genuine, non-trivial claim: it fails, for instance, for noise with an infinite log moment.

*Junk values: none.*

*Standard result:* the log-moment condition (Vervaat / Goldie–Maller; Elton; Bougerol–Picard type) is strictly weaker than the Diaconis–Freedman first-step $p$-moment condition, here for the contraction $x\mapsto x/2+e$.
