# Blind read-back report: packet R48 (Markov chain with heavy-tailed noise)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round25/packet_R48_markov.lean` |
| declarations audited | 12 (1 definition `logTailLaw` + 11 theorems) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round25/work_R48_markov/` (`Scratch.lean`/`.out`, `InnerSatisfiable.lean`/`.out`, `markov_checks.py`/`.out`) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 0 | `logTailLaw` | def | n/a (genuine law of $e^{1/U}$, $U\sim\mathrm{Unif}(0,1)$) | n/a | no |
| 1 | `logTailLaw_Ioi` | theorem | true | no | no |
| 2 | `halfStep_contracting` | theorem | true (it holds with equality) | no | no |
| 3 | `lintegral_logTailLaw_eq_top` | theorem | true | no | no |
| 4 | `logTailLaw_counterexample` | theorem | true | no | no |
| 5 | `tendsto_measure_backIter_halfStep_le` | theorem | true | no | no |
| 6 | `tendsto_measure_fwdIter_halfStep_le` | theorem | true | no | no |
| 7 | `tendsto_measure_lt_fwdIter_halfStep` | theorem | true | no | no |
| 8 | `markov_no_weak_limit` | theorem | true | no | no |
| 9 | `not_tendstoInDistribution_fwdIter_halfStep` | theorem | true | no | no |
| 10 | `exists_iid_logTailLaw` | theorem | true | no (the theorem is itself the witness) | no |
| 11 | `hc_cannot_be_dropped` | theorem | true | no: the negation is meaningful (see below) | no |

## Main points for a human auditor

- **No false, vacuous or junk-dependent statement.** I compiled each packet statement as an `example … := MLMC.<name>` against `import MlmcLean`, and all 11 elaborate. So the packet text matches the compiled declarations (`Scratch.out`). `#print axioms` lists only `propext, Classical.choice, Quot.sound` for the 7 theorems I checked.
- **`hc_cannot_be_dropped` (the negated universal statement) is meaningful.** (a) In Lean, I checked a degenerate instance where all of the inner statement's hypotheses hold *and* its conclusion holds: $\Omega=\mathrm{Unit}$, $\xi\equiv0$, $\nu=\delta_0$, $\varphi=$`halfStep`, $p=1$, $\rho=1/2$, $x_0=0$ (`InnerSatisfiable.lean`, which compiles). So `TendstoInDistribution` is not unsatisfiable, and the negation does not come cheaply from an impossible conclusion. (b) Mathematically, the universal statement becomes a true theorem (Wu–Shao 2004; Diaconis–Freedman 1999) once a moment condition $\int d(x_0,\varphi(x_0,e))^p\,d\nu<\infty$ is added. So any refutation has to use a failing moment, and the packet's witness does exactly that: `exists_iid_logTailLaw` + `halfStep` + `logTailLaw` + $\rho=2^{-p}$, $x_0=0$, combined with #3 and #9.
- **Minor: the conclusion of the universal statement asks for $X$ on the same $\Omega$.** On its own, `hc_cannot_be_dropped` is therefore formally weaker than "no weak limit exists". I found no cheap counterexample that exploits this; under the moment condition the a.s. limit of the backward iterates lives on $\Omega$. The strong form, with no limit law on any space, is #8/#9.
- **Minor: #5 omits `[IsProbabilityMeasure μ]`.** This is harmless: `hlaw` together with measurability of $\xi_0$ forces $\mu(\Omega)=\mathrm{logTailLaw}(\mathbb R)=1$.
- **Context: #5–#9 use only the starting point $x_0=0$.** That is enough for a counterexample. The noise has $P(\xi>t)=1/\log t$, so even $E\log^+\xi=\infty$. It breaks every polynomial moment at once, and it also breaks the sharp (logarithmic) condition for this AR(1) chain. That is why mass escapes.
- **The hypothesis $e\le t$ in #1 is exactly the right range.** For $1<t<e$ the right-hand side $1/\log t$ exceeds 1, while the true value is 1.

---

## 0. `logTailLaw` (definition)

**Rendering.** $\mathrm{logTailLaw}=(\lambda|_{(0,1)})\circ g^{-1}$ with $g(u)=\exp(1/u)$. This is the law of $\xi=e^{1/U}$ for $U\sim\mathrm{Unif}(0,1)$. The map $g$ is Borel measurable, so `Measure.map` is the genuine pushforward and not the junk value $0$. Junk at $u=0$ ($1/0=0$) is irrelevant because $0\notin(0,1)$. It is a probability measure, supported on $(e,\infty)$, with $P(\xi>t)=1/\log t$ for $t\ge e$ (#1 certifies that it is not the zero measure).

## 1. `logTailLaw_Ioi`

**Rendering.** For real $t$ with $e^1\le t$: $\mathrm{logTailLaw}((t,\infty))=\mathrm{ofReal}(1/\log t)$.

**Assessment.** True. For $u\in(0,1)$ and $t>1$, $e^{1/u}>t\iff u<1/\log t$. Since $\log t\ge1$, the set is $(0,1/\log t)$, with Lebesgue measure $1/\log t$. Monte Carlo agrees at $t=e,3,10,100,10^6,10^{30}$ (`markov_checks.out` §1). Not vacuous ($t=e$ gives $1$). No junk: $\log t\ge1$. The hypothesis is necessary, since for $t\in(1,e)$ the right-hand side would be $>1$. **Standard fact:** the elementary tail computation for a "log-Pareto" variable.

## 2. `halfStep_contracting`

**Rendering.** For every probability measure $\nu$ on $\mathbb R$ and every real $p>0$: $0\le 2^{-p}$, $2^{-p}<1$, and for all $x,y\in\mathbb R$,
$\int^- \mathrm{ofReal}(|(x/2+e)-(y/2+e)|^p)\,d\nu(e)\le \mathrm{ofReal}(2^{-p})\cdot\mathrm{ofReal}(|x-y|^p)$. Here `^` is `Real.rpow` with nonnegative bases.

**Assessment.** True with equality. The integrand is the constant $(|x-y|/2)^p=2^{-p}|x-y|^p$, and $\nu$ has total mass 1. `ofReal` is multiplicative on nonnegative reals. Not vacuous (any $\nu$, e.g. $\delta_0$). No junk: $0^p=0$ for $p>0$ is the honest value. **Standard fact:** the AR(1) map $x\mapsto x/2+e$ is a strict $1/2$-Lipschitz contraction, so it is "contracting on average" in $L^p$ with $\rho=2^{-p}$ for any noise law. This is the Wu–Shao geometric-moment contraction condition.

## 3. `lintegral_logTailLaw_eq_top`

**Rendering.** For real $p>0$: $\int^- \mathrm{ofReal}(|0-(0/2+e)|^p)\,d\,\mathrm{logTailLaw}(e)=\infty$, i.e. $E[|\xi|^p]=\infty$.

**Assessment.** True. $E\xi^p=\int_0^1 e^{p/u}\,du=p\int_p^\infty e^s s^{-2}\,ds=\infty$, and truncated integrals blow up for $p=0.01,\dots,3$ (§2). In fact even $E\log^+\xi=\int_1^\infty s^{-1}ds=\infty$. Not vacuous. No junk: a genuine $\infty$ in `ℝ≥0∞`. **Standard fact:** a variable with $P(\xi>t)=1/\log t$ has no finite moment of any positive order.

## 4. `logTailLaw_counterexample`

**Rendering.** For real $p>0$: (i) $0\le2^{-p}<1$; (ii) for all $x,y$, $\int^-\mathrm{ofReal}(|\mathrm{halfStep}(x,e)-\mathrm{halfStep}(y,e)|^p)\,d\,\mathrm{logTailLaw}\le\mathrm{ofReal}(2^{-p})\,\mathrm{ofReal}(|x-y|^p)$; (iii) $\neg\big(\int^-\mathrm{ofReal}(|0-\mathrm{halfStep}(0,e)|^p)\,d\,\mathrm{logTailLaw}\neq\infty\big)$, i.e. classically "$=\infty$".

**Assessment.** True: it is #2 with $\nu=\mathrm{logTailLaw}$ (a probability measure) together with #3. The $\neg(\cdot\ne\infty)$ form evidently mirrors a hypothesis `hc : … ≠ ∞` of a general theorem. It states that the contraction hypotheses hold while the moment hypothesis fails at $x_0=0$. Not vacuous. No junk. **Standard fact:** the hypotheses of the Wu–Shao/Diaconis–Freedman theorem, with the moment condition failing.

## 5. `tendsto_measure_backIter_halfStep_le`

**Rendering.** Let $(\Omega,\mathcal F,\mu)$ be a measure space (the probability instance is omitted), and let $\xi_i:\Omega\to\mathbb R$ be mutually independent (`iIndepFun`) and measurable, each with law $\mathrm{logTailLaw}$. For every real $M$: $\mu\{\omega: B_n(\omega)\le M\}\to0$ as $n\to\infty$, where $B_n=\mathrm{backIter}\ \mathrm{halfStep}\ n\ \xi\ 0=\varphi_{\xi_0}\circ\cdots\circ\varphi_{\xi_{n-1}}(0)=\sum_{k<n}2^{-k}\xi_k$. I checked the definitional unfolding for $n=2,3$ in Lean.

**Assessment.** True. Since $\xi_k>0$, $B_n\ge\max_{k<n}2^{-k}\xi_k$. By independence, $\mu(B_n\le M)\le\prod_{k<n}P(\xi\le M2^k)=\prod_{k<n}\bigl(1-\tfrac1{\log M+k\log2}\bigr)\to0$, because $\sum 1/(c+k\log 2)=\infty$. The rate is about $n^{-1/\log2}$ (§3 has the bound and a Monte Carlo check). For $M<e$ the set is empty for $n\ge1$. Omitting `IsProbabilityMeasure` is harmless: `hlaw` forces $\mu(\Omega)=1$. Not vacuous (#10 supplies an instance). No junk. **Standard fact:** divergence of the perpetuity $\sum 2^{-k}\xi_k$ when $E\log^+\xi=\infty$ (Kesten 1973; Vervaat 1979; Goldie–Maller 2000).

## 6. `tendsto_measure_fwdIter_halfStep_le`

**Rendering.** Same setting with $\mu$ a probability measure. For every real $M$: $\mu\{X_n\le M\}\to0$, where $X_0=0$, $X_{n+1}=X_n/2+\xi_n$, i.e. $X_n=\sum_{k<n}2^{-(n-1-k)}\xi_k$ (checked in Lean for $n=3$).

**Assessment.** True. $(\xi_0,\dots,\xi_{n-1})$ and its reversal have the same law (i.i.d.), so $X_n\overset d=B_n$, and #5 applies. Monte Carlo shows forward and backward frequencies agree (§3). Not vacuous. No junk. **Standard fact:** the backward-iteration principle (Letac; Diaconis–Freedman) combined with #5.

## 7. `tendsto_measure_lt_fwdIter_halfStep`

**Rendering.** Same setting: for every real $M$, $\mu\{M<X_n\}\to1$.

**Assessment.** True: the complement of #6 in a probability space. Not vacuous. No junk. **Standard fact:** $X_n\to+\infty$ in probability (escape of mass).

## 8. `markov_no_weak_limit`

**Rendering.** Same setting. For every Borel probability measure $\pi$ on $\mathbb R$ and every sequence $P_n$ of probability measures with $P_n=\mathrm{Law}_\mu(X_n)$: $P_n\not\to\pi$ in the topology of `ProbabilityMeasure ℝ`, which is weak convergence (convergence in distribution).

**Assessment.** True. If $P_n\Rightarrow\pi$, the portmanteau theorem on the open set $(-\infty,M)$ gives $\pi((-\infty,M))\le\liminf P_n((-\infty,M))\le\lim\mu(X_n\le M)=0$ for every $M$. Then $\pi(\mathbb R)=0$, a contradiction. Not vacuous: `hP` is satisfiable because $X_n$ is measurable, so the pushforward is a probability measure. No junk. **Standard fact:** a sequence that is not tight, with all its mass escaping to infinity, has no weak limit (Prokhorov).

## 9. `not_tendstoInDistribution_fwdIter_halfStep`

**Rendering.** Same setting. For every probability space $(\Omega',\mu')$ (any universe) and every $X:\Omega'\to\mathbb R$: it is not the case that $X_n\to X$ in distribution. Mathlib's `TendstoInDistribution` means: every $X_n$ is a.e.-measurable, $X$ is a.e.-measurable, and $\mathrm{Law}(X_n)\to\mathrm{Law}(X)$ weakly.

**Assessment.** True by #8. For a non-measurable $X$ the negation is trivial, but every law on $\mathbb R$ arises from a measurable $X$, e.g. the identity on $(\mathbb R,\pi)$, so the statement has full content. Not vacuous. No junk. **Standard fact:** same as #8.

## 10. `exists_iid_logTailLaw`

**Rendering.** There exist a type $\Omega$ in `Type`, a σ-algebra on it, a probability measure $\mu$, and measurable $\xi:\mathbb N\to\Omega\to\mathbb R$ that are mutually independent with every $\mathrm{Law}(\xi_i)=\mathrm{logTailLaw}$.

**Assessment.** True: take $\Omega=\mathbb R^{\mathbb N}$ with the infinite product measure (`Measure.infinitePi`) and coordinate projections. This supplies a non-vacuity witness for the hypotheses of #5–#9 and for #11. No junk. **Standard fact:** existence of i.i.d. sequences (Kolmogorov extension / infinite product measure).

## 11. `hc_cannot_be_dropped`

**Rendering.** It is NOT the case that the following holds:

> For every $\Omega$ in `Type` with a σ-algebra, every probability measure $\mu$ on $\Omega$, every measure $\nu$ on $\mathbb R$, every $\varphi:\mathbb R\times\mathbb R\to\mathbb R$ and every $\xi:\mathbb N\to\Omega\to\mathbb R$: if $(x,e)\mapsto\varphi(x,e)$ is jointly Borel measurable, then for all reals $p,\rho$ with $p>0$ and $0\le\rho<1$, the following implication holds. Suppose that
> - for all $x,y\in\mathbb R$, $\int^-\mathrm{ofReal}(|\varphi(x,e)-\varphi(y,e)|^p)\,d\nu(e)\le\mathrm{ofReal}(\rho)\cdot\mathrm{ofReal}(|x-y|^p)$ (contraction on average in $L^p$), and
> - the $\xi_i$ are mutually independent under $\mu$, each measurable, each with law $\nu$.
>
> Then for every $x_0\in\mathbb R$ there is $X:\Omega\to\mathbb R$ on the same $\Omega$ such that $X_n\to X$ in distribution, where $X_n=\mathrm{fwdIter}\ \varphi\ n\ \xi\ x_0$ (that is, $X_0=x_0$, $X_{n+1}=\varphi(X_n,\xi_n)$) and $X$ is a.e.-measurable.

This is the Wu–Shao / Diaconis–Freedman convergence theorem for iterated random functions, with the moment hypothesis $\int d(x_0,\varphi(x_0,e))^p\,d\nu<\infty$ ("hc") removed.

**Assessment.** True. Witness: $\Omega,\mu,\xi$ from #10, $\nu=\mathrm{logTailLaw}$, $\varphi=\mathrm{halfStep}$ (jointly measurable), any $p>0$, $\rho=2^{-p}$ (contraction by #2), $x_0=0$. Theorem #9 with $\Omega'=\Omega$, $\mu'=\mu$ then refutes the conclusion for every $X$.

**Meaningfulness (non-vacuity of the negation).**
- (a) The inner conclusion is attainable. `InnerSatisfiable.lean` (which compiles) exhibits an instance where *all* hypotheses of the inner statement hold *and* the conclusion holds: $\Omega=\mathrm{Unit}$, $\mu=\delta$, $\xi\equiv0$, $\nu=\delta_0$, $\varphi=\mathrm{halfStep}$, $p=1$, $\rho=1/2$, $x_0=0$, $X\equiv0$. So the negation is not a cheap consequence of an unsatisfiable `TendstoInDistribution`.
- (b) The universal statement is not refutable by a technicality. With hc added it is true: the backward iterates satisfy $E\,d(Z_{n+1},Z_n)^p\le\rho^n E\,d(\varphi(x_0,\xi),x_0)^p$, which only needs the pointwise-in-$(x,y)$ contraction, independence and Fubini, not continuity. By Borel–Cantelli they converge a.s. to a measurable $Z$ on $\Omega$, and $X_n\overset d=Z_n$. Hence $X=Z$ works on the same $\Omega$. For degenerate $\nu=\delta_c$ the limit is the deterministic fixed point.

So any refutation must break the moment condition, and the witness does exactly that.

Caveats:
- Because the conclusion requires $X$ on the same $\Omega$, this negation alone is formally weaker than "no limit law exists". #8/#9 supply the strong form.
- The witness breaks even the log-moment, so it shows that no $L^p$ moment hypothesis can be dropped. It does not separate hc from the sharp condition $E\log^+|\xi|<\infty$. That is expected and not a defect.

No junk: `ofReal ρ` has $\rho\ge0$, and the `rpow` bases are nonnegative. **Standard fact:** the moment condition in the Diaconis–Freedman (1999) / Wu–Shao (2004) theorem cannot be dropped; the counterexample is the divergent perpetuity of an AR(1) chain with $E\log^+\xi=\infty$.
