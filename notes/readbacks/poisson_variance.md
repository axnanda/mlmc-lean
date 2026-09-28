# Blind read-back: packet F (`packet_F_poisson_variance.lean`)

- **Date:** 2026-09-28
- **Packet:** `readback/round6/packet_F_poisson_variance.lean` (namespace `MLMC`)
- **Declarations audited:** 12, made up of 6 definitions (`couplePair`, `coupledIncr`, `tauStep`, `tauChain`, `coupledTwoStep`, `coupledChain`) and 6 lemmas/theorems (`lintegral_sq_coupledIncr_le`, `lintegral_sq_coupledTwoStep_le`, `lintegral_sq_coupledChain_le`, `coupledChain_sq_le`, `variance_coupledChain_le`, `tauLeaping_level_variance`).
- **Content that is not a declaration:** the `open MeasureTheory ProbabilityTheory Finset` and `open scoped NNReal ENNReal` lines, and an empty `section Discrete`. That section declares variables `α β γ` with measurable-space instances and then closes before any declaration, so the variables affect nothing.

**Rules followed**

1. **Sources.** I read only the auditor mission file, the packet and Mathlib sources. Mathlib was used only to confirm the meaning of Mathlib definitions. I opened no other project file, paper, note, README, plan, script, git history or web page. I inferred no meaning from declaration or file names.
2. **Mission principles 1–7:**
   - I translated the code, not the intent.
   - Every binder, hypothesis and implicit instance is accounted for.
   - Every packet definition is unfolded inline in every rendering, so each rendering stands alone.
   - Edge cases are surfaced: $h=0$, $k=0$, empty sums, truncated subtraction in $\mathbb R_{\ge0}$, and junk values. The junk values are: the integral of a non-integrable function is $0$, the variance of a non-$L^2$ function is $0$, and the pushforward along a non-measurable map is the zero measure.
   - The exact strength of every relation is kept.
   - Notation is plain mathematics (Markdown + KaTeX, single backslashes).
   - Renderings contain no judgement.
3. **Assessments kept separate.** The sections **Truth**, **Non-vacuity**, **Junk values** and **Concerns** are kept apart from the renderings. Proofs are not audited. They are `sorry`, except for the note under §9.
4. **Numerical checks.** These are in `readback/round6/work_F/`, written in pure Python:
   - `coupling.py` is a literal re-implementation of the six definitions as finitely supported probability vectors. Poisson tails are truncated below $10^{-18}$.
   - `check_incr.py`, `check_twostep.py` and `check_chain.py` check the stated bounds.
   - `mc_chain.py` is an independent Monte Carlo simulation.
   - Outputs are in `out_*.txt`.
5. **Lean was not run.** Compiled Mathlib is not present in this environment. The placement of casts, such as $2kh$ with $k$ cast from $\mathbb N$ to $\mathbb R$, was read from the source using the standard Lean 4 elaboration rules.

## Mathlib conventions confirmed

Paths are relative to `.lake/packages/mathlib/Mathlib/`.

| Item | Convention used in the renderings | Source (file:line) |
|---|---|---|
| `poissonMeasure r`, r in NNReal | Measure on ℕ equal to the sum over n of `ofReal(exp(-r) r^n / n!)` times the point mass at n. It is a probability measure. Rate 0 gives the point mass at 0 because `0^0 = 1`. | `Probability/Distributions/Poisson/Basic.lean:41` (def), `:50` (singleton mass), `:68` (probability instance); `Algebra/Group/Defs.lean:692` (`pow_zero`) |
| Poisson additivity (used only in my checks) | Po(r1) convolved with Po(r2) is Po(r1 + r2) | `Probability/Distributions/Poisson/Basic.lean:178` |
| σ-algebra on ℕ | top (every subset is measurable) | `MeasureTheory/MeasurableSpace/Instances.lean:30` |
| σ-algebra on ℕ × ℕ | Product σ-algebra with measurable singletons. The space is countable, hence discrete, so every function out of ℕ × ℕ is measurable. | `MeasureTheory/MeasurableSpace/Constructions.lean:376`, `:474`; `MeasureTheory/MeasurableSpace/Defs.lean:551`, `:561`; `MeasureTheory/MeasurableSpace/Basic.lean:287` |
| `Measure.map f μ` | Pushforward if f is a.e.-measurable, otherwise the zero measure | `MeasureTheory/Measure/Map.lean:74`, `:91` |
| `Measure.bind m f` | Defined as `join (map f m)`. For measurable f, `bind m f s` is the lower integral of `f a s` with respect to m. The lower integral against a bind can be taken iteratively. | `MeasureTheory/Measure/GiryMonad.lean:125` (join), `:228` (bind), `:235` (bind_apply), `:285` (lintegral_bind) |
| `Measure.prod μ ν` | Defined as `bind μ (fun x => map (Prod.mk x) ν)` | `MeasureTheory/Measure/Prod.lean:171` |
| `Measure.dirac a` | Point mass at a | `MeasureTheory/Measure/Dirac.lean:35` |
| Probability is preserved | map, prod and bind of probability measures (with measurable kernel) are probability measures | `MeasureTheory/Measure/Typeclasses/Probability.lean:124`; `MeasureTheory/Measure/Prod.lean:322`; `MeasureTheory/Measure/ProbabilityMeasure.lean:672` |
| Lower (Lebesgue) integral | Value in [0, ∞], always defined, may equal ∞ | `MeasureTheory/Integral/Lebesgue/Basic.lean:48` |
| `lintegral_dirac` | The integral against the point mass at a is f(a) | `MeasureTheory/Integral/Lebesgue/Countable.lean:67` |
| `ENNReal.ofReal r` | `Real.toNNReal r`, which is max(r, 0) | `Data/ENNReal/Basic.lean:230`; `Data/NNReal/Defs.lean:155` |
| `ENNReal.toReal` | Sends ∞ to 0 | `Data/ENNReal/Basic.lean:224`, `:227`, `:283` |
| `Integrable f μ` | a.e.-strongly measurable, and the lower integral of the extended norm of f is finite | `MeasureTheory/Function/L1Space/Integrable.lean:59`; `MeasureTheory/Function/L1Space/HasFiniteIntegral.lean:80` |
| Bochner integral | 0 when f is not integrable. For nonnegative f it equals `toReal` of the lower integral of `ofReal f`. | `MeasureTheory/Integral/Bochner/Basic.lean:156`, `:202`, `:483` |
| `variance X μ` | `toReal` of the lower integral of the squared extended norm of `X - μ[X]`, where `μ[X]` is the Bochner mean. It is 0 when X is not in L² (finite μ). Var is at most E[X²] for probability measures. | `Probability/Moments/Variance.lean:58`, `:64`, `:132`, `:339` |
| Subtraction in NNReal | Truncated: r - p is `toNNReal(r - p)`, i.e. max(r - p, 0). It is exact when p ≤ r. | `Data/NNReal/Defs.lean:745`, `:748`, `:226` |
| Casts NNReal to ℝ of products and quotients | The cast of r1·r2 is r1·r2 and the cast of r1/r2 is r1/r2. Both are definitional. | `Data/NNReal/Defs.lean:212`, `:220` |
| Sums over `Finset.range k` | Sum over i = 0, …, k-1. Empty, hence 0, when k = 0. | `Algebra/BigOperators/Group/Finset/Defs.lean:599` (`prod_range_zero`; its additive version is `sum_range_zero`) |

## Summary of findings

| # | Declaration | Kind | Truth | Vacuous? | Weakened by a junk value? |
|---|---|---|---|---|---|
| 1 | `couplePair` | definition | n/a | n/a | no |
| 2 | `coupledIncr` | definition | n/a (marginals Po(a), Po(b) verified) | n/a | no |
| 3 | `tauStep` | definition | n/a | n/a | no |
| 4 | `tauChain` | definition | n/a (not used by any theorem) | n/a | no |
| 5 | `coupledTwoStep` | definition | n/a | n/a | no |
| 6 | `coupledChain` | definition | n/a | n/a | no |
| 7 | `lintegral_sq_coupledIncr_le` | lemma | true, and sharp | no hypotheses | no |
| 8 | `lintegral_sq_coupledTwoStep_le` | theorem | true | no | no |
| 9 | `lintegral_sq_coupledChain_le` | theorem | true | no | no |
| 10 | `coupledChain_sq_le` | theorem | true | no | no (integrability is asserted) |
| 11 | `variance_coupledChain_le` | theorem | true | no (vacuous only for L < 0) | no (junk cannot trigger, but L² is not asserted) |
| 12 | `tauLeaping_level_variance` | theorem | true | no | no |

No statement was found false, vacuous, or made trivially true by a junk value. Points for the human auditor:

- `tauChain` is not used by any theorem. No theorem links `coupledChain` to `tauChain`.
- The rate function is assumed to be globally bounded and globally Lipschitz.
- The last theorem covers only indices with $T\le 2^{\ell+1}$.
- The proof text of `lintegral_sq_coupledChain_le` in the packet is not a pure `sorry` (see §9).

---

## 1. `couplePair` (definition)

**Rendering.** For nonnegative reals $a,b\in\mathbb R_{\ge0}$ and a pair of natural numbers $p=(p_1,p_2)\in\mathbb N\times\mathbb N$ (with $\mathbb N=\{0,1,2,\dots\}$), the function $\pi_{a,b}:\mathbb N\times\mathbb N\to\mathbb N\times\mathbb N$ is

$$\pi_{a,b}(p_1,p_2)=\bigl(p_1+\mathbf 1[b<a]\,p_2,\;\;p_1+\mathbf 1[a<b]\,p_2\bigr),$$

where $\mathbf 1[\,\cdot\,]$ is $1$ when the strict inequality holds and $0$ otherwise. So $\pi_{a,b}(p_1,p_2)$ is:

- $(p_1+p_2,\;p_1)$ when $a>b$;
- $(p_1,\;p_1+p_2)$ when $a<b$;
- $(p_1,\;p_1)$ when $a=b$, in which case $p_2$ does not enter.

**Truth.** Not applicable, since this is a definition. It is a total, well-defined function.

**Non-vacuity.** Not applicable. Examples: $\pi_{2,1}(3,4)=(7,3)$, $\pi_{1,2}(3,4)=(3,7)$ and $\pi_{1,1}(3,4)=(3,3)$.

**Junk values.** None. It uses only addition of natural numbers, with no subtraction or division.

**Concerns.** When $a=b$ the input $p_2$ is discarded. In its only use (§2), $p_2$ is then drawn from $\mathrm{Poi}(0)=\delta_0$, so nothing is lost.

---

## 2. `coupledIncr` (definition)

**Rendering.** For $a,b\in\mathbb R_{\ge0}$, $\mathcal C_{a,b}$ is a measure on $\mathbb N\times\mathbb N$ (with the σ-algebra of all subsets). It is the image of the product measure $\mathrm{Poi}(\min(a,b))\otimes\mathrm{Poi}(\max(a,b)\ominus\min(a,b))$ under the map $(n,m)\mapsto\bigl(n+\mathbf 1[b<a]\,m,\;n+\mathbf 1[a<b]\,m\bigr)$. Here:

- for $r\ge0$, $\mathrm{Poi}(r)$ is the probability measure on $\mathbb N$ with $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$; since $0^0=1$, $\mathrm{Poi}(0)=\delta_0$;
- $\ominus$ is subtraction in $\mathbb R_{\ge0}$, truncated at $0$. Because $\max(a,b)\ge\min(a,b)$, it equals $|a-b|$.

Equivalently, $\mathcal C_{a,b}$ is the joint law of

$$\bigl(N+\mathbf 1[a>b]\,M,\;\;N+\mathbf 1[a<b]\,M\bigr),\qquad N\sim\mathrm{Poi}(\min(a,b)),\;\;M\sim\mathrm{Poi}(|a-b|)\ \text{independent}.$$

That is, for every $A\subseteq\mathbb N^2$,

$$\mathcal C_{a,b}(A)=\sum_{n,m\ge0}\mathrm{Poi}(\min(a,b))(\{n\})\,\mathrm{Poi}(|a-b|)(\{m\})\,\mathbf 1\bigl[(n+\mathbf 1[b<a]m,\;n+\mathbf 1[a<b]m)\in A\bigr].$$

**Truth.** This is a definition, not a statement. Properties I checked:

- $\mathcal C_{a,b}$ is a probability measure.
- Its first marginal is $\mathrm{Poi}(a)$ and its second marginal is $\mathrm{Poi}(b)$. For example, if $a>b$ the first coordinate is $N+M\sim\mathrm{Poi}(b+(a-b))$.
- Its difference satisfies $i-j=\operatorname{sign}(a-b)\,M$. When $a=b$ this is $0$ almost surely.

Numerically, the marginals and the law of the difference match to within $2\times10^{-16}$ for 8 rate pairs. These include $a=b$, $a=0$ or $b=0$, and nearly equal rates.

**Non-vacuity.** Not applicable. Examples: $\mathcal C_{1,0}$ is the law of $(M,0)$ with $M\sim\mathrm{Poi}(1)$, and $\mathcal C_{a,a}$ is the law of $(N,N)$ with $N\sim\mathrm{Poi}(a)$.

**Junk values.**

- The truncated subtraction in $\mathbb R_{\ge0}$ is exact here.
- The pushforward would be the zero measure if the map were not measurable. Every map out of the countable space $\mathbb N^2$ with measurable singletons is measurable, so the pushforward is genuine.
- Rates equal to $0$ are allowed and give $\delta_0$.

**Concerns.** None about the definition itself. The two coordinates share the $\mathrm{Poi}(\min)$ part. The surplus $\mathrm{Poi}(|a-b|)$ goes to the coordinate with the strictly larger rate.

---

## 3. `tauStep` (definition)

**Rendering.** Take a function $\lambda:\mathbb N\to\mathbb R_{\ge0}$, a number $h\in\mathbb R_{\ge0}$ and a state $x\in\mathbb N$. Then $S_{\lambda,h}(x)$ is the measure on $\mathbb N$ (with all subsets measurable) obtained as the image of $\mathrm{Poi}(h\lambda(x))$ under $n\mapsto x+n$. Here $h\lambda(x)$ is the product in $\mathbb R_{\ge0}$ and $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$. So $S_{\lambda,h}(x)$ is the law of $x+P$ with $P\sim\mathrm{Poi}(h\lambda(x))$:

$$S_{\lambda,h}(x)(\{y\})=\begin{cases}e^{-h\lambda(x)}\,\dfrac{(h\lambda(x))^{\,y-x}}{(y-x)!}, & y\ge x,\\[6pt] 0, & y<x.\end{cases}$$

If $h\lambda(x)=0$ (for instance when $h=0$ or $\lambda(x)=0$), this is the point mass $\delta_x$.

**Truth.** Not applicable. $S_{\lambda,h}(x)$ is a probability measure.

**Non-vacuity.** Not applicable.

**Junk values.** None. The map $n\mapsto x+n$ is measurable because $\mathbb N$ is discrete, and rate $0$ gives $\delta_x$.

**Concerns.** Increments are nonnegative, so the state never decreases. The rate is evaluated at the current state $x$.

---

## 4. `tauChain` (definition)

**Rendering.** Take $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $h\in\mathbb R_{\ge0}$ and $x_0\in\mathbb N$. The sequence $(\tau_n)_{n\in\mathbb N}$ of measures on $\mathbb N$ is defined by recursion on $n$:

$$\tau_0=\delta_{x_0},\qquad \tau_{n+1}(A)=\sum_{x\in\mathbb N}\tau_n(\{x\})\,S_{\lambda,h}(x)(A)\quad(A\subseteq\mathbb N).$$

Here $S_{\lambda,h}(x)$ is the law of $x+P$ with $P\sim\mathrm{Poi}(h\lambda(x))$, where $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$ and $h\lambda(x)\in\mathbb R_{\ge0}$. Equivalently, $\tau_n$ is the law of $X_n$ for the Markov chain with $X_0=x_0$ and $X_{m+1}=X_m+P_m$. Conditionally on $X_0,\dots,X_m$, the increment $P_m$ has law $\mathrm{Poi}(h\lambda(X_m))$.

**Truth.** Not applicable. Every $\tau_n$ is a probability measure.

**Non-vacuity.** Not applicable.

**Junk values.** None. The composition would degenerate if the kernel $x\mapsto S_{\lambda,h}(x)$ were not measurable. It is measurable because $\mathbb N$ is discrete.

**Concerns.** No theorem in this packet refers to `tauChain`. In particular, no theorem states that the coordinates of `coupledChain` have laws given by `tauChain`. Numerically they do; see §6.

---

## 5. `coupledTwoStep` (definition)

**Rendering.** Take $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $h\in\mathbb R_{\ge0}$ and $s=(s_1,s_2)\in\mathbb N^2$. Then $Q_s$ is the measure on $\mathbb N^2$ (with all subsets measurable) given for $A\subseteq\mathbb N^2$ by

$$Q_s(A)=\sum_{(i,j)\in\mathbb N^2}\mathcal C_{h\lambda(s_1),\,h\lambda(s_2)}\bigl(\{(i,j)\}\bigr)\;\mathcal C_{h\lambda(s_1+i),\,h\lambda(s_2)}\Bigl(\bigl\{(i',j'):(s_1+i+i',\;s_2+j+j')\in A\bigr\}\Bigr).$$

Equivalently, $Q_s$ is the law of $(s_1+I+I',\;s_2+J+J')$, where:

- $(I,J)\sim\mathcal C_{h\lambda(s_1),\,h\lambda(s_2)}$;
- conditionally on $(I,J)$, $(I',J')\sim\mathcal C_{h\lambda(s_1+I),\,h\lambda(s_2)}$.

The first rate of the second draw is evaluated at $s_1+I$. The second rate is evaluated at $s_2$ in both draws.

For $a,b\ge0$, $\mathcal C_{a,b}$ is the joint law of $(N+\mathbf 1[a>b]M,\;N+\mathbf 1[a<b]M)$, with $N\sim\mathrm{Poi}(\min(a,b))$ and $M\sim\mathrm{Poi}(\max(a,b)-\min(a,b))=\mathrm{Poi}(|a-b|)$ independent. The subtraction is in $\mathbb R_{\ge0}$ and is exact here. As before, $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$ and $\mathrm{Poi}(0)=\delta_0$. All products $h\lambda(\cdot)$ are taken in $\mathbb R_{\ge0}$.

**Truth.** Not applicable. Properties I checked:

- $Q_s$ is a probability measure.
- Its first marginal is the law after two steps of $S_{\lambda,h}$ started at $s_1$, with the rate re-evaluated at $s_1+I$.
- Its second marginal is $s_2+\mathrm{Poi}(2h\lambda(s_2))$. The reason is that $J'$ has conditional law $\mathrm{Poi}(h\lambda(s_2))$ whatever $(I,J)$ is, so $J'$ is independent of $J$.

Both marginals were confirmed numerically to within $2\times10^{-16}$ (`check_twostep.py`).

**Non-vacuity.** Not applicable.

**Junk values.** None. The kernel and the inner map are measurable because the domain is discrete.

**Concerns.** The two coordinates are treated asymmetrically. The first coordinate takes two sub-steps and re-evaluates its rate after the first one. The second coordinate uses the rate at $s_2$ for both draws, so its total increment has law $\mathrm{Poi}(2h\lambda(s_2))$. Whether this is the intended pairing should be checked against the intended construction.

---

## 6. `coupledChain` (definition)

**Rendering.** Take $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $h\in\mathbb R_{\ge0}$ and $x_0\in\mathbb N$. The sequence $(\mu_k)_{k\in\mathbb N}=(\mu^{\lambda,h,x_0}_k)_k$ of measures on $\mathbb N^2$ (with all subsets measurable) is defined by

$$\mu_0=\delta_{(x_0,x_0)},\qquad \mu_{k+1}(A)=\sum_{s\in\mathbb N^2}\mu_k(\{s\})\,Q_s(A)\quad(A\subseteq\mathbb N^2).$$

So $\mu_k$ is the law after $k$ steps of the Markov chain on $\mathbb N^2$ with transition kernel $s\mapsto Q_s$, started at $(x_0,x_0)$. The pieces are:

- for $s=(s_1,s_2)$, $Q_s$ is the law of $(s_1+I+I',\;s_2+J+J')$, where $(I,J)\sim\mathcal C_{h\lambda(s_1),\,h\lambda(s_2)}$ and, given $(I,J)$, $(I',J')\sim\mathcal C_{h\lambda(s_1+I),\,h\lambda(s_2)}$;
- for $a,b\ge0$, $\mathcal C_{a,b}$ is the joint law of $(N+\mathbf 1[a>b]M,\;N+\mathbf 1[a<b]M)$, with $N\sim\mathrm{Poi}(\min(a,b))$ and $M\sim\mathrm{Poi}(\max(a,b)-\min(a,b))=\mathrm{Poi}(|a-b|)$ independent;
- $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$ and $\mathrm{Poi}(0)=\delta_0$;
- all products $h\lambda(\cdot)$ are taken in $\mathbb R_{\ge0}$.

**Truth.** Not applicable. Every $\mu_k$ is a probability measure. Numerically:

- the first marginal of $\mu_k$ equals `tauChain` $\lambda$, $h$, $x_0$ at step $2k$;
- the second marginal of $\mu_k$ equals `tauChain` $\lambda$, $2h$, $x_0$ at step $k$.

Both hold to within $10^{-16}$ in 3 configurations. The packet does not state this.

**Non-vacuity.** Not applicable.

**Junk values.** None. The kernels are measurable because the domain is discrete. When $h=0$, every $\mathcal C$ is $\delta_{(0,0)}$ and $\mu_k=\delta_{(x_0,x_0)}$.

**Concerns.** The concerns of §4 and §5 apply here. Both coordinates start at the same deterministic state $x_0$.

---

## 7. `lintegral_sq_coupledIncr_le` (lemma)

**Rendering.** For all $a,b\in\mathbb R_{\ge0}$ and all $x,y\in\mathbb N$, with no further hypotheses,

$$\int_{\mathbb N^2}\bigl((x+i)-(y+j)\bigr)^2\;\mathcal C_{a,b}\bigl(d(i,j)\bigr)\;\le\;(x-y)^2+2\,|x-y|\,|a-b|+1\cdot\bigl(|a-b|+|a-b|^2\bigr).$$

Here $\mathcal C_{a,b}$ is the probability measure on $\mathbb N^2$ (all subsets measurable) defined as the joint law of $(N+\mathbf 1[a>b]M,\;N+\mathbf 1[a<b]M)$, with $N\sim\mathrm{Poi}(\min(a,b))$ and $M\sim\mathrm{Poi}(\max(a,b)-\min(a,b))=\mathrm{Poi}(|a-b|)$ independent. As before, $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$ and $\mathrm{Poi}(0)=\delta_0$.

- The sums $x+i$ and $y+j$ are formed in $\mathbb N$ and then read as reals.
- The left side is the $[0,\infty]$-valued integral of the nonnegative function $(i,j)\mapsto((x+i)-(y+j))^2$, namely $\sum_{(i,j)}\mathcal C_{a,b}(\{(i,j)\})\,((x+i)-(y+j))^2$. A priori it may be $+\infty$.
- The right side is a real number, mapped into $[0,\infty]$ by $r\mapsto\max(r,0)$. It is always $\ge0$, so the map leaves it unchanged.
- The inequality holds in $[0,\infty]$, so it also asserts that the left side is finite.
- The factor $1$ appears literally in the statement.

**Truth.** True. Put $d=x-y$, $\delta=|a-b|$ and $\sigma=\operatorname{sign}(a-b)$. Under $\mathcal C_{a,b}$ we have $i-j=\sigma M$; if $a=b$ then $M=0$ almost surely. Hence

$$\text{LHS}=E\bigl[(d+\sigma M)^2\bigr]=d^2+2d(a-b)+\delta+\delta^2\;\le\;d^2+2|d|\,\delta+\delta+\delta^2=\text{RHS}.$$

Equality holds if and only if $(x-y)(a-b)\ge0$, so the bound is sharp.

Numerically (`check_incr.py`) I tested 4,764 cases, on a grid plus random points:

- the left side matched the closed form above to within a relative error of $10^{-9}$;
- the left side never exceeded the right side;
- in the equality cases the relative gap was at most $4\times10^{-15}$;
- a strict example is $a=1$, $b=0$, $x=0$, $y=1$, where the left side is $1$ and the right side is $5$.

**Non-vacuity.** There are no hypotheses. Example: $a=1$, $b=0$, $x=y=0$ gives left side $E[M^2]=2$, equal to the right side.

**Junk values.** None.

- The integrand is a square, so the embedding into $[0,\infty]$ is exact.
- The right side is $\ge0$.
- The pushforward is genuine.
- The truncated subtraction is exact.

**Concerns.** Minor only. The cross term uses $|x-y|\,|a-b|$ rather than the signed product, and the literal factor $1\cdot$ is present.

---

## 8. `lintegral_sq_coupledTwoStep_le` (theorem)

**Rendering.** Let $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $h\in\mathbb R_{\ge0}$ and $\kappa,\ell\in\mathbb R$ be arbitrary. Assume:

1. $\kappa\ge0$;
2. $|h\lambda(x)-h\lambda(y)|\le\kappa\,|x-y|$ for all $x,y\in\mathbb N$, where the products $h\lambda(\cdot)$ are formed in $\mathbb R_{\ge0}$ and compared as reals;
3. $h\lambda(y)\le\ell$ for all $y\in\mathbb N$.

Then for every $s=(s_1,s_2)\in\mathbb N^2$,

$$\int_{\mathbb N^2}(q_1-q_2)^2\;Q_s(dq)\;\le\;(1+4\kappa+2\kappa^2)^2\,(s_1-s_2)^2+\Bigl((\kappa+2\kappa^2)(\ell+\ell^2)+\kappa\ell\Bigr).$$

The measures are unfolded as follows:

- $Q_s$ is the probability measure on $\mathbb N^2$ (all subsets measurable) defined as the law of $(s_1+I+I',\;s_2+J+J')$. Here $(I,J)\sim\mathcal C_{h\lambda(s_1),\,h\lambda(s_2)}$ and, conditionally on $(I,J)$, $(I',J')\sim\mathcal C_{h\lambda(s_1+I),\,h\lambda(s_2)}$. The second rate is evaluated at $s_2$ in both draws.
- For $a,b\ge0$, $\mathcal C_{a,b}$ is the joint law of $(N+\mathbf 1[a>b]M,\;N+\mathbf 1[a<b]M)$, with $N\sim\mathrm{Poi}(\min(a,b))$ and $M\sim\mathrm{Poi}(\max(a,b)-\min(a,b))=\mathrm{Poi}(|a-b|)$ independent.
- $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$ and $\mathrm{Poi}(0)=\delta_0$.

Reading the inequality:

- The left side is the $[0,\infty]$-valued integral of the nonnegative function $q\mapsto(q_1-q_2)^2$, so the inequality includes its finiteness.
- The right side is mapped into $[0,\infty]$ by $r\mapsto\max(r,0)$. Under the hypotheses it is $\ge0$, because $\kappa\ge0$ and, by hypothesis 3, $\ell\ge h\lambda(0)\ge0$.
- Apart from hypotheses 2 and 3, nothing constrains the size of $h$.

**Truth.** True. Proof sketch: put $d=s_1-s_2$, $b=h\lambda(s_2)$, $d_1=d+I-J$ and $a_2=h\lambda(s_1+I)$.

1. Apply the exact formula from §7 conditionally on $(I,J)$:
   $$E\bigl[(q_1-q_2)^2\mid I,J\bigr]=d_1^2+2d_1(a_2-b)+|a_2-b|+|a_2-b|^2.$$
2. By hypothesis 2, and because $d+I=d_1+J$ with $J\ge0$, we get $|a_2-b|\le\kappa|d_1+J|\le\kappa(|d_1|+J)$.
3. Use $|d_1|\le d_1^2$, which holds because $d_1$ is an integer, together with $2|d_1|J\le d_1^2+J^2$. This bounds the conditional expectation by
   $$(1+4\kappa+2\kappa^2)\,d_1^2+(\kappa+2\kappa^2)\,J^2+\kappa J.$$
4. Since $J\sim\mathrm{Poi}(b)$ with $0\le b\le\ell$, we have $E[J]\le\ell$ and $E[J^2]=b+b^2\le\ell+\ell^2$.
5. By §7 again, with $|h\lambda(s_1)-b|\le\kappa|d|$ and $|d|\le d^2$:
   $$E[d_1^2]\le(1+3\kappa+\kappa^2)\,d^2\le(1+4\kappa+2\kappa^2)\,d^2.$$

Combining these steps gives the stated bound. Numerically (`check_twostep.py`) I tested 48,672 cases $(\lambda,h,s)$. They covered 16 rate functions (capped linear, decreasing, zigzag, constant and random Lipschitz), $h\in\{0.05,\dots,2\}$ and $s\in[0,25]^2$, with the tightest $\kappa$ and $\ell$ for each case.

- No case violated the bound.
- The largest ratio of left side to right side was $0.970$ when $\kappa>0$.
- The ratio is exactly $1$ when $\kappa=0$ (constant $h\lambda$), where the left side equals $(s_1-s_2)^2$.
- For small rates, the full two-step law was cross-checked against the fast formula in 1,116 cases.

**Non-vacuity.** Take $\lambda(x)=1+(x\bmod 2)$, $h=\tfrac14$, $\kappa=\tfrac14$ and $\ell=\tfrac12$. All hypotheses hold, and the right side's constant term is $\tfrac{13}{32}$.

| $s$ | Left side | Right side |
|---|---|---|
| $(0,0)$ | $\tfrac{1-e^{-1/2}}{2}\cdot\tfrac5{16}\approx0.0615$ | $0.406$ |
| $(1,0)$ | $2.408$ | $4.922$ |
| $(3,7)$ | $16.73$ | $72.66$ |

**Junk values.** None, for the same reasons as in §7. The right side is nonnegative under the hypotheses.

**Concerns.**

- Hypothesis 1 ($\kappa\ge0$) is redundant: hypothesis 2 with $x=0$, $y=1$ already forces it.
- Nonnegativity of $\ell$ is implicit in hypothesis 3.
- The hypotheses bound $h\lambda$ jointly rather than $\lambda$ and $h$ separately.
- The bound concerns a single application of $Q$ from a deterministic state $s$.

---

## 9. `lintegral_sq_coupledChain_le` (theorem)

**Rendering.** Let $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $h\in\mathbb R_{\ge0}$ and $\kappa,\ell\in\mathbb R$ satisfy:

1. $\kappa\ge0$;
2. $|h\lambda(x)-h\lambda(y)|\le\kappa|x-y|$ for all $x,y\in\mathbb N$, with products in $\mathbb R_{\ge0}$ compared as reals;
3. $h\lambda(y)\le\ell$ for all $y\in\mathbb N$.

Let $x_0\in\mathbb N$. Then for every $k\in\mathbb N$,

$$\int_{\mathbb N^2}(q_1-q_2)^2\;\mu_k(dq)\;\le\;\Bigl((\kappa+2\kappa^2)(\ell+\ell^2)+\kappa\ell\Bigr)\cdot\sum_{i=0}^{k-1}\bigl((1+4\kappa+2\kappa^2)^2\bigr)^{i}.$$

For $k=0$ the sum is empty, so the right side is $0$. The measures are unfolded as follows:

- $\mu_k$ is the probability measure on $\mathbb N^2$ (all subsets measurable) given by $\mu_0=\delta_{(x_0,x_0)}$ and $\mu_{k+1}(A)=\sum_{s\in\mathbb N^2}\mu_k(\{s\})\,Q_s(A)$.
- $Q_s$, for $s=(s_1,s_2)$, is the law of $(s_1+I+I',\;s_2+J+J')$, where $(I,J)\sim\mathcal C_{h\lambda(s_1),\,h\lambda(s_2)}$ and, given $(I,J)$, $(I',J')\sim\mathcal C_{h\lambda(s_1+I),\,h\lambda(s_2)}$.
- $\mathcal C_{a,b}$ is the joint law of $(N+\mathbf 1[a>b]M,\;N+\mathbf 1[a<b]M)$, with $N\sim\mathrm{Poi}(\min(a,b))$ and $M\sim\mathrm{Poi}(|a-b|)$ independent.
- $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$ and $\mathrm{Poi}(0)=\delta_0$.

The left side is a $[0,\infty]$-valued integral, so its finiteness is part of the claim. The right side is mapped into $[0,\infty]$ by $r\mapsto\max(r,0)$ and is $\ge0$ under the hypotheses.

**Truth.** True. Write $m_k$ for the left side, $C=1+4\kappa+2\kappa^2$, and $D=(\kappa+2\kappa^2)(\ell+\ell^2)+\kappa\ell\ge0$.

- The integral against $\mu_{k+1}$ is the $\mu_k$-integral of the $Q_s$-integrals, since the kernel is measurable.
- Applying §8 pointwise in $s$ and using $\mu_k(\mathbb N^2)=1$ gives $m_{k+1}\le C^2m_k+D$.
- With $m_0=0$, induction gives $m_k\le D\sum_{i<k}C^{2i}$.

Numerically (`check_chain.py`) I checked every $k\le T/(2h)$ with $T=2$, over 36 configurations: 3 rate functions, $h\in\{1,\tfrac12,\tfrac14,\tfrac18\}$ and $x_0\in\{0,2,5\}$, using the tightest $\kappa$ and $\ell$. No case violated the bound, and the largest ratio of left side to right side was $0.35$.

**Non-vacuity.** Use the same data as in §8, with $x_0=0$. For $k=0,1,2,3$, the left side is $0,\ 0.0615,\ 0.133,\ 0.237$ and the right side is $0,\ 0.406,\ 2.24,\ 10.5$.

**Junk values.** None. Every term is a nonnegative real.

**Concerns.**

- **Proof text.** In the packet, the proof of this theorem is not a pure `sorry`. It is a recursion on $k$. The $k+1$ branch contains only `have hℓ : 0 ≤ ℓ := sorry` and leaves the goal open, so the declaration would not compile as written. The statement itself is well formed.
- **Growth in $k$.** For $\kappa>0$ the bound grows geometrically in $k$. A bound uniform in the number of steps needs $\kappa$ small; §10 obtains this by taking $\kappa=hK$.

---

## 10. `coupledChain_sq_le` (theorem)

**Rendering.** Let $\lambda:\mathbb N\to\mathbb R_{\ge0}$ and $K,\Lambda\in\mathbb R_{\ge0}$ satisfy:

- $|\lambda(x)-\lambda(y)|\le K\,|x-y|$ for all $x,y\in\mathbb N$, compared in $\mathbb R$;
- $\lambda(x)\le\Lambda$ for all $x\in\mathbb N$.

Let $T\in\mathbb R$ with $T\ge0$. Then there exists a real number $c\ge0$ such that the following holds for every $h\in\mathbb R_{\ge0}$ and all $k,x_0\in\mathbb N$ with

$$h\le1\qquad\text{and}\qquad 2kh\le T.$$

Here $k$ is read as a real number. The number $c$ is chosen after $\lambda,K,\Lambda,T$, so it may depend on them, but not on $h,k,x_0$. For the measure $\mu=\mu^{\lambda,h,x_0}_k$:

- **(a)** the function $q\mapsto(q_1-q_2)^2$ on $\mathbb N^2$ is integrable with respect to $\mu$, meaning it is measurable and $\int(q_1-q_2)^2\,d\mu<\infty$;
- **(b)** the real-valued integral satisfies $\displaystyle\int_{\mathbb N^2}(q_1-q_2)^2\;\mu(dq)\;\le\;c\,h$.

The measures are unfolded as follows:

- $\mu^{\lambda,h,x_0}_k$ is the probability measure on $\mathbb N^2$ (all subsets measurable) given by $\mu_0=\delta_{(x_0,x_0)}$ and $\mu_{k+1}(A)=\sum_{s}\mu_k(\{s\})\,Q_s(A)$.
- $Q_s$, for $s=(s_1,s_2)$, is the law of $(s_1+I+I',\;s_2+J+J')$, where $(I,J)\sim\mathcal C_{h\lambda(s_1),\,h\lambda(s_2)}$ and, given $(I,J)$, $(I',J')\sim\mathcal C_{h\lambda(s_1+I),\,h\lambda(s_2)}$.
- $\mathcal C_{a,b}$ is the joint law of $(N+\mathbf 1[a>b]M,\;N+\mathbf 1[a<b]M)$, with $N\sim\mathrm{Poi}(\min(a,b))$ and $M\sim\mathrm{Poi}(|a-b|)$ independent.
- $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$ and $\mathrm{Poi}(0)=\delta_0$.
- The products $h\lambda(\cdot)$ are taken in $\mathbb R_{\ge0}$.

**Truth.** True.

- Apply §9 with $\kappa=hK$ and $\ell=h\Lambda$; both hypotheses hold.
- For $h\le1$, $D\le h^2D_0$ with $D_0=(K+2K^2)(\Lambda+\Lambda^2)+K\Lambda$.
- Also $C=1+4hK+2h^2K^2\le e^{h(4K+2K^2)}$, so $\sum_{i<k}C^{2i}\le k\,e^{2kh(4K+2K^2)}\le k\,e^{T(4K+2K^2)}$.
- Hence $m_k\le h\cdot(kh)\,D_0\,e^{T(4K+2K^2)}\le h\cdot\tfrac T2\,D_0\,e^{T(4K+2K^2)}$.
- So $c=\tfrac T2D_0\,e^{T(4K+2K^2)}\ge0$ works.
- The lower integral is finite, which gives (a). For a nonnegative integrable function the real integral is the finite lower integral, which gives (b).

Numerically, with $T=1$, $h=2^{-(\ell+1)}$, $k=2^\ell$ and $\ell=0,\dots,7$ (`out_chain.txt`), the ratio of the integral to $h$ stays at most $1.25$ in every tested case and converges as $h\to0$. It is exactly $0$ in one degenerate case: $\lambda=0.5+\min(x,3)$ with $x_0=3$, where $\lambda$ is constant on the reachable states.

**Non-vacuity.** Take $\lambda(x)=1+(x\bmod2)$, with $K=1$, $\Lambda=2$ and $T=1$.

- With $h=\tfrac12$, $k=1$ and $x_0=0$, the integral is $0.237$, which is positive.
- With $x_0=3$, the ratio of the integral to $h$ is $0.65,\ 1.00,\ 1.16,\ \dots,\ 1.25$ for $h=2^{-1},\dots,2^{-8}$.

**Junk values.** None. Integrability is part of the conclusion, so the real integral in (b) is not the junk value $0$. When $h=0$ the premise $2kh\le T$ holds for every $k$, but then $\mu_k=\delta_{(x_0,x_0)}$ and both sides are $0$.

**Concerns.**

- $c$ may depend on the particular function $\lambda$, not only on $K,\Lambda,T$, because of the quantifier order. The proof sketch gives a $c$ that depends only on $K,\Lambda,T$, but the statement does not say so.
- The hypothesis $T\ge0$ is not needed for truth. If $T<0$, no $(h,k)$ satisfies $2kh\le T$.
- The rate function must be globally bounded and globally Lipschitz on $\mathbb N$.
- The condition is $2kh\le T$, an inequality rather than an equality. It is paired with $h\le1$.
- Only the final-time second moment of $q_1-q_2$ is bounded, and $c$ is uniform in $x_0$.

---

## 11. `variance_coupledChain_le` (theorem)

**Rendering.** Let $\lambda:\mathbb N\to\mathbb R_{\ge0}$ and $K,\Lambda\in\mathbb R_{\ge0}$ satisfy:

- $|\lambda(x)-\lambda(y)|\le K|x-y|$ for all $x,y\in\mathbb N$;
- $\lambda(x)\le\Lambda$ for all $x\in\mathbb N$.

Let $T\in\mathbb R$ with $T\ge0$. Let $\Phi:\mathbb N\to\mathbb R$ and $L\in\mathbb R$ satisfy $|\Phi(x)-\Phi(y)|\le L\,|x-y|$ for all $x,y\in\mathbb N$. Then there exists a real $c\ge0$ such that for every $h\in\mathbb R_{\ge0}$ and all $k,x_0\in\mathbb N$ with $h\le1$ and $2kh\le T$,

$$\operatorname{Var}_{\mu}\bigl[\,q\mapsto\Phi(q_1)-\Phi(q_2)\,\bigr]\;\le\;c\,h,\qquad \mu=\mu^{\lambda,h,x_0}_k.$$

The number $c$ is chosen after $\lambda,K,\Lambda,T,\Phi,L$, so it may depend on all of them, but not on $h,k,x_0$.

**Variance.** For a real function $X$ on $\mathbb N^2$, $\operatorname{Var}_\mu[X]$ is built from the $[0,\infty]$-valued integral $\int|X-m|^2\,d\mu$ by sending $+\infty$ to $0$. Here $m=\int X\,d\mu$ if $X$ is $\mu$-integrable, and $m=0$ otherwise. It is therefore the usual variance when $X$ is square-integrable, and $0$ when it is not ($\mu$ being a probability measure).

The measures are unfolded as follows:

- $\mu^{\lambda,h,x_0}_k$ is the probability measure on $\mathbb N^2$ (all subsets measurable) with $\mu_0=\delta_{(x_0,x_0)}$ and $\mu_{k+1}(A)=\sum_s\mu_k(\{s\})\,Q_s(A)$.
- $Q_s$ is the law of $(s_1+I+I',\;s_2+J+J')$, where $(I,J)\sim\mathcal C_{h\lambda(s_1),\,h\lambda(s_2)}$ and, given $(I,J)$, $(I',J')\sim\mathcal C_{h\lambda(s_1+I),\,h\lambda(s_2)}$.
- $\mathcal C_{a,b}$ is the joint law of $(N+\mathbf 1[a>b]M,\;N+\mathbf 1[a<b]M)$, with $N\sim\mathrm{Poi}(\min(a,b))$ and $M\sim\mathrm{Poi}(|a-b|)$ independent.
- $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$ and $\mathrm{Poi}(0)=\delta_0$.
- The products $h\lambda(\cdot)$ are taken in $\mathbb R_{\ge0}$.

**Truth.** True. Let $Y=\Phi(q_1)-\Phi(q_2)$.

- If $L<0$, the hypothesis on $\Phi$ fails for every $x\ne y$, so the statement holds vacuously.
- If $L\ge0$, then $|Y|\le L|q_1-q_2|$, so $Y\in L^2(\mu)$ by §10(a).
- Mathlib's `variance_le_expectation_sq` gives $\operatorname{Var}_\mu[Y]\le E_\mu[Y^2]\le L^2E_\mu[(q_1-q_2)^2]\le L^2c_{10}\,h$, where $c_{10}$ is the constant from §10. So $c=L^2c_{10}$ works.

Numerically, with $T=1$, $h=2^{-(\ell+1)}$ and $k=2^\ell$, the quantity $2^\ell\cdot\operatorname{Var}$ stays bounded. This holds for three rate functions, two starting points and three choices of $\Phi$ ($x$, $|x-3|$, $\min(x,5)$). A Monte Carlo run with 400k paths matched the exact computation, giving $0.1118$ against $0.1111$.

**Non-vacuity.** Take $\lambda(x)=1+(x\bmod2)$ (with $K=1$, $\Lambda=2$), $T=1$, $\Phi(x)=x$ and $L=1$. With $h=\tfrac12$, $k=1$ and $x_0=0$, the variance is $\approx0.212$, which is positive.

**Junk values.** The convention that $\operatorname{Var}=0$ off $L^2$, and the convention that the mean is $0$ for non-integrable $X$, cannot trigger under these hypotheses, since $Y\in L^2(\mu)$. However, the statement itself does not assert that $Y$ is square-integrable, unlike §10(a).

**Concerns.**

- The bound is on the variance, not on the second moment.
- $c$ may depend on the particular functions $\lambda$ and $\Phi$, not only on $K,\Lambda,L,T$.
- For $L<0$ the statement is vacuous; this is harmless.
- The hypothesis $T\ge0$ is redundant.
- The same global boundedness and Lipschitz assumptions as in §10 apply.

---

## 12. `tauLeaping_level_variance` (theorem)

**Rendering.** Let $\lambda:\mathbb N\to\mathbb R_{\ge0}$ and $K,\Lambda\in\mathbb R_{\ge0}$ satisfy:

- $|\lambda(x)-\lambda(y)|\le K|x-y|$ for all $x,y\in\mathbb N$;
- $\lambda(x)\le\Lambda$ for all $x\in\mathbb N$.

Let $T\in\mathbb R_{\ge0}$. Let $\Phi:\mathbb N\to\mathbb R$ and $L\in\mathbb R$ satisfy $|\Phi(x)-\Phi(y)|\le L|x-y|$ for all $x,y\in\mathbb N$. Then there exists a real $c\ge0$ such that for all $\ell\in\mathbb N$ and $x_0\in\mathbb N$ with $T\le2^{\ell+1}$,

$$\operatorname{Var}_{\nu}\bigl[\,q\mapsto\Phi(q_1)-\Phi(q_2)\,\bigr]\;\le\;\frac{c}{2^{\ell}},\qquad \nu=\mu^{\lambda,\,h_\ell,\,x_0}_{2^\ell},\quad h_\ell=\frac{T}{2^{\ell+1}}\in\mathbb R_{\ge0}.$$

The number $c$ is chosen after $\lambda,K,\Lambda,T,\Phi,L$, and does not depend on $\ell$ or $x_0$. The quotient $h_\ell$ is computed in $\mathbb R_{\ge0}$ with a nonzero denominator, so it equals the real number $T/2^{\ell+1}$. The chain is run for $k=2^\ell$ steps.

**Variance.** $\operatorname{Var}_\nu[X]$ is built from the $[0,\infty]$-valued integral $\int|X-m|^2\,d\nu$ by sending $+\infty$ to $0$. Here $m=\int X\,d\nu$ if $X$ is integrable, and $m=0$ otherwise. It is the usual variance for square-integrable $X$ and $0$ otherwise.

The measures are unfolded as follows:

- $\mu^{\lambda,h,x_0}_k$ is the probability measure on $\mathbb N^2$ (all subsets measurable) with $\mu_0=\delta_{(x_0,x_0)}$ and $\mu_{k+1}(A)=\sum_s\mu_k(\{s\})\,Q_s(A)$.
- $Q_s$ is the law of $(s_1+I+I',\;s_2+J+J')$, where $(I,J)\sim\mathcal C_{h\lambda(s_1),\,h\lambda(s_2)}$ and, given $(I,J)$, $(I',J')\sim\mathcal C_{h\lambda(s_1+I),\,h\lambda(s_2)}$.
- $\mathcal C_{a,b}$ is the joint law of $(N+\mathbf 1[a>b]M,\;N+\mathbf 1[a<b]M)$, with $N\sim\mathrm{Poi}(\min(a,b))$ and $M\sim\mathrm{Poi}(|a-b|)$ independent.
- $\mathrm{Poi}(r)(\{n\})=e^{-r}r^n/n!$ and $\mathrm{Poi}(0)=\delta_0$.
- The products $h\lambda(\cdot)$ are taken in $\mathbb R_{\ge0}$.

**Truth.** True. Take $h=h_\ell$ and $k=2^\ell$ in §11. Then $2kh=2\cdot2^\ell\cdot T/2^{\ell+1}=T$, and $h_\ell\le1$ if and only if $T\le2^{\ell+1}$. So §11 gives $\operatorname{Var}\le c_{11}h_\ell=(c_{11}T/2)/2^\ell$, and $c=c_{11}T/2\ge0$ works.

Numerically, with $T=1$, $\lambda(x)=1+(x\bmod2)$, $x_0=0$ and $\Phi(x)=x$, the values of $2^\ell\cdot\operatorname{Var}$ for $\ell=0,\dots,7$ are:

$$0.212,\ 0.261,\ 0.313,\ 0.343,\ 0.358,\ 0.365,\ 0.369,\ 0.370.$$

These are bounded, which is consistent with a bound of order $1/2^\ell$.

**Non-vacuity.** Take the same data as above ($K=1$, $\Lambda=2$, $L=1$). Every $\ell\ge0$ is admissible because $T=1\le2^{\ell+1}$. For example, at $\ell=0$ the variance is $0.212$, which is positive.

**Junk values.** None. As in §11, the variance is genuine because $\Phi(q_1)-\Phi(q_2)\in L^2$, but square-integrability is not asserted in the statement. There is no division by zero, since $2^{\ell+1}>0$ and $2^\ell>0$.

**Concerns.**

- **Which indices are covered.** Only indices with $T\le2^{\ell+1}$, i.e. $h_\ell\le1$, are covered. For $T>2$ the first few indices are excluded; for example, $T=8$ excludes $\ell=0,1$.
- **What the coordinates are.** As computed in §6, the first coordinate of $\nu$ makes $2^{\ell+1}$ steps of size $T/2^{\ell+1}$. The second coordinate makes $2^\ell$ steps of size $T/2^\ell$. The packet contains no theorem stating this; `tauChain` is unused.
- **Dependence of $c$.** $c$ may depend on the particular $\lambda$ and $\Phi$.
- **Name clash.** The symbol $\ell$ here is a natural number (the exponent). It is unrelated to the real bound $\ell$ in §8 and §9.
- **Assumptions.** The same global boundedness and Lipschitz assumptions as in §10 apply.
