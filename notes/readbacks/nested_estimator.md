# Blind read-back — packet 9

**Declarations covered** (all in namespace `MLMC`)

- Definitions: `levelDiff`, `blockMean`, `nIdx`, `pairFam`, `nestedTerm`, `nestedEstimator`, `nestedCost`
- Theorems: `nested_cost_isLeast`, `nested_saving`, `nestedEstimator_mean_variance`, `nestedCost_mean`, `nested_mlmc_mse`

**Inputs used:** `readback/packet9.lean` and `prove2me_workspace/references/mission_auditor.md`, plus library source only. From Mathlib `0df444a` I read `MeasurePreserving`, `iIndepFun`/`IndepFun` and their `_iff` lemmas, `Set.Pairwise`, `MemLp`, `Integrable`/`HasFiniteIntegral`, `evariance`/`variance`, `IsLeast`/`lowerBounds`, the `P[X]` macro in `Probability/Notation.lean`, the `∑` syntax, `Real.sqrt_eq_zero_of_nonpos`, `integral_undef` and `Measure.infinitePi`. From Lean core v4.33.1 I read the `boolToProp` coercion and the section-variable inclusion rule in `Elab/MutualDef.lean`. I opened no other project file and compiled nothing.

**Notation used throughout.**

- $\mathbb N=\{0,1,2,\dots\}$.
- $\sum_{\ell=0}^{L}$ always means the sum over `range (L + 1)` $=\{0,1,\dots,L\}$. This set is never empty.
- Boolean flags are written $\mathrm{true}$ and $\mathrm{false}$.
- A natural number that appears inside a real expression is cast to $\mathbb R$.
- $\mathbb E_\mu[f]$ stands for Mathlib's `μ[f]`. The macro unfolds to the Bochner integral $\int f\,d\mu$ and inserts a coercion that is the identity on real-valued $f$. The Bochner integral of a non-integrable function is defined to be $0$.
- On a real number, Lean's inverse satisfies $0^{-1}=0$, so $x/0=0$. Lean's real square root returns $0$ on negative inputs.

**Section variables.** Lean adds a section variable to a theorem's signature only in two cases. The first is when the statement mentions it, directly or through a dependency. The second is when it is an instance argument whose own dependencies are all included. Included variables come first, in the order they were declared, before the theorem's own binders. This rule fixes the argument lists given below.

---

## 0. The definitions in the packet

### `levelDiff`

Take any type $\Omega_0$ and a sequence $P=(P_\ell)_{\ell\in\mathbb N}$ of functions $P_\ell:\Omega_0\to\mathbb R$. Then `levelDiff P` is the sequence $(\Delta P_\ell)_{\ell\in\mathbb N}$ defined by
$$\Delta P_0=P_0,\qquad \Delta P_{\ell}(y)=P_{\ell}(y)-P_{\ell-1}(y)\quad(\ell\ge 1,\ y\in\Omega_0).$$
The definition involves no measurability. As a consequence (not part of the definition), the sum telescopes pointwise: $\sum_{\ell=0}^{L}\Delta P_\ell=P_L$.

### `blockMean`

The inputs are:

- an index type $\iota$;
- functions $f_i:\Omega_0\to\mathbb R$ for $i\in\iota$;
- maps $\omega_{(i,n)}:\Omega\to\Omega_0$ indexed by $(i,n)\in\iota\times\mathbb N$;
- an index $i$, a natural number $N$ and a point $x\in\Omega$.

The value is
$$\operatorname{blockMean}(f,\omega,i,N)(x)=N^{-1}\sum_{n=0}^{N-1}f_i\big(\omega_{(i,n)}(x)\big).$$
It uses only block $i$ of $\omega$, and only its first $N$ members. When $N=0$ the sum is empty and $0^{-1}=0$, so the value is $0$.

### `nIdx`

$\operatorname{nIdx}(L)=\{0,\dots,L\}\times\{\mathrm{true},\mathrm{false}\}$. The second factor is `Finset.univ` on `Bool`, which contains both values, so the set has $2(L+1)$ elements.

### `pairFam`

Take any type $X$ and two sequences $f,g:\mathbb N\to X$. Then `pairFam f g` is the family on $\mathbb N\times\mathrm{Bool}$ given by
$$\operatorname{pairFam}(f,g)(\ell,b)=\begin{cases}f_\ell,& b=\mathrm{true},\\ g_\ell,& b=\mathrm{false}.\end{cases}$$
The first coordinate is the level and the second is the flag. In Lean, `if b then … else …` with a Boolean `b` coerces `b` to the proposition "$b=\mathrm{true}$", so the reading above is exact.

### `nestedTerm`

For $P,D:\mathbb N\to(\Omega_0\to\mathbb R)$, `nestedTerm P D` $=\operatorname{pairFam}\big(D,\ \ell\mapsto\Delta P_\ell-D_\ell\big)$. That is:

- $(\ell,\mathrm{true})\mapsto D_\ell$;
- $(\ell,\mathrm{false})\mapsto\big(y\mapsto\Delta P_\ell(y)-D_\ell(y)\big)$.

### `nestedEstimator`

The inputs are:

- $P,D$ as above;
- a family of maps $\omega_q:\Omega\to\Omega_0$ indexed by $q=((\ell,b),n)\in(\mathbb N\times\mathrm{Bool})\times\mathbb N$, where $\ell$ is the level, $b$ the flag and $n$ the sample number;
- $L\in\mathbb N$ and $N^t,N^\Delta:\mathbb N\to\mathbb N$;
- a point $x\in\Omega$.

The value is
$$\widehat Y(x)=\sum_{\ell=0}^{L}\Bigg[\frac{1}{N^t_\ell}\sum_{n=0}^{N^t_\ell-1}D_\ell\big(\omega_{((\ell,\mathrm{true}),n)}(x)\big)+\frac{1}{N^\Delta_\ell}\sum_{n=0}^{N^\Delta_\ell-1}\big(\Delta P_\ell-D_\ell\big)\big(\omega_{((\ell,\mathrm{false}),n)}(x)\big)\Bigg].$$

- Each $\frac1N$ is $N^{-1}$ with $0^{-1}=0$, so a block with zero samples contributes $0$.
- The flag-true block of level $\ell$ uses $N^t_\ell$ samples and evaluates only $D_\ell$.
- The flag-false block uses $N^\Delta_\ell$ samples. Each of its sample points $y=\omega_{((\ell,\mathrm{false}),n)}(x)$ is fed to $P_\ell$, to $P_{\ell-1}$ (when $\ell\ge1$) and to $D_\ell$.
- Different $(\ell,b)$ blocks read disjoint members of $\omega$.

### `nestedCost`

The inputs are:

- cost functions $c^t_{\ell,n},c^\Delta_{\ell,n}:\Omega\to\mathbb R$, indexed by level $\ell$ and sample number $n$;
- $L$, $N^t$, $N^\Delta$ and a point $x$.

The value is
$$\operatorname{Cost}(x)=\sum_{\ell=0}^{L}\Big(\sum_{n=0}^{N^t_\ell-1}c^t_{\ell,n}(x)+\sum_{n=0}^{N^\Delta_\ell-1}c^\Delta_{\ell,n}(x)\Big).$$
This is a raw total with no averaging. A zero sample number gives an empty sum, which is $0$.

---

## 1. `nested_cost_isLeast`

**Reading in one paragraph.** Fix $L\in\mathbb N$, four real sequences $V^t,C^t,V^\Delta,C^\Delta$ that are strictly positive at every index in $\mathbb N$, and a real $\varepsilon>0$. Consider every choice of strictly positive real sequences $n^t,n^\Delta$ with
$$\sum_{\ell=0}^{L}\Big(\frac{V^t_\ell}{n^t_\ell}+\frac{V^\Delta_\ell}{n^\Delta_\ell}\Big)\le\varepsilon^2.$$
Over these choices, the quantity $\sum_{\ell=0}^{L}(n^t_\ell C^t_\ell+n^\Delta_\ell C^\Delta_\ell)$ has a smallest value, and that value is
$$(\varepsilon^2)^{-1}\Big(\sum_{\ell=0}^{L}\big(\sqrt{V^t_\ell C^t_\ell}+\sqrt{V^\Delta_\ell C^\Delta_\ell}\big)\Big)^2.$$

**Arguments, in order.**

1. $L\in\mathbb N$ (explicit; section variable).
2. $V^t,C^t,V^\Delta,C^\Delta:\mathbb N\to\mathbb R$ (explicit; section variables in the declared order `Vt Ct VΔ CΔ`). The hypotheses below come in a different order: $V^t,V^\Delta,C^t,C^\Delta$.
3. $\varepsilon\in\mathbb R$ (implicit).
4. The five hypotheses below (explicit).

There are no typeclass or instance arguments; the statement is purely about real numbers. The quantifier order is: for all $L$, all four sequences and all $\varepsilon$, the hypotheses imply the conclusion.

**Hypotheses.**

1. $0<\varepsilon$.
2. $0<V^t_\ell$ for every $\ell\in\mathbb N$.
3. $0<V^\Delta_\ell$ for every $\ell\in\mathbb N$.
4. $0<C^t_\ell$ for every $\ell\in\mathbb N$.
5. $0<C^\Delta_\ell$ for every $\ell\in\mathbb N$.

**Conclusion.** Define the set
$$\mathcal S=\Big\{c\in\mathbb R\ :\ \exists\,n^t,n^\Delta:\mathbb N\to\mathbb R\ \text{such that}\ \forall\ell\ n^t_\ell>0,\ \ \forall\ell\ n^\Delta_\ell>0,\ \ \sum_{\ell=0}^{L}\Big(\frac{V^t_\ell}{n^t_\ell}+\frac{V^\Delta_\ell}{n^\Delta_\ell}\Big)\le\varepsilon^2,\ \ c=\sum_{\ell=0}^{L}\big(n^t_\ell C^t_\ell+n^\Delta_\ell C^\Delta_\ell\big)\Big\}$$
and the number
$$c^\star=(\varepsilon^2)^{-1}\Big(\sum_{\ell=0}^{L}\big(\sqrt{V^t_\ell C^t_\ell}+\sqrt{V^\Delta_\ell C^\Delta_\ell}\big)\Big)^2 .$$
In the definition of $\mathcal S$, "$\forall\ell$" ranges over all of $\mathbb N$. The conclusion is `IsLeast` $\mathcal S$ $c^\star$, which has two parts:

- **(a) Attainment.** $c^\star\in\mathcal S$. So there exist real sequences $n^t,n^\Delta$, strictly positive at every $\ell\in\mathbb N$, that satisfy the constraint and whose cost is exactly $c^\star$.
- **(b) Lower bound.** $c^\star\le c$ for every $c\in\mathcal S$.

**Library notions and conventions.**

- `IsLeast s a` means $a\in s$ and $a$ is a lower bound of $s$, that is, $a\le b$ for every $b\in s$.
- The square roots are of positive numbers, so the "$\sqrt{\text{negative}}=0$" convention is never triggered.
- $(\varepsilon^2)^{-1}$ is a genuine inverse because $\varepsilon>0$.
- The divisions $V/n$ inside $\mathcal S$ are genuine because $n>0$ is required.
- The square applies to the whole sum over levels. It is not taken term by term.

**Edge cases and observations.**

- **Continuous relaxation.** The sample sizes $n^t_\ell,n^\Delta_\ell$ are real numbers, not natural numbers, and there is no rounding. Every positive-integer allocation is also a positive-real one, so part (b) is also a lower bound for integer allocations that meet the constraint. Part (a), attainment, is only claimed over real allocations, and the attaining allocation is generally not integral.
- **The constraint.** The only constraint is $\sum(V^t/n^t+V^\Delta/n^\Delta)\le\varepsilon^2$, with "$\le$" rather than "$=$". It contains no bias term and no splitting constant. The cost model is linear: $n\cdot C$ per block.
- **Strict positivity of the $n$'s matters.** Since Lean has $V/0=0$, allowing $n_\ell=0$ would make that level's variance term vanish at zero cost.
- **Strict positivity of $V$ and $C$ also matters.** For example, if some $V^t_\ell$ or $V^\Delta_\ell$ with $\ell\le L$ were $0$, the value $c^\star$ would not be attained by strictly positive $n$'s.
- **Levels beyond $L$.** The positivity conditions on $V,C$ and on the $n$'s are imposed at every $\ell\in\mathbb N$, although only $\ell\le L$ enters the constraint and the cost. For the $n$'s this changes nothing, since values beyond $L$ are free. For $V,C$ it makes the hypothesis stronger than the conclusion needs.
- **No link to other declarations.** Nothing in the statement ties $V^t,V^\Delta,C^t,C^\Delta$ to random variables, to `nestedEstimator` or to `nestedCost`. It is an optimisation statement about arbitrary positive numbers.
- **Not vacuous.** The hypotheses can be satisfied, for example with all values equal to $1$. My own consistency check, which is not part of the statement: let $S=\sum_{\ell\le L}\big(\sqrt{V^t_\ell C^t_\ell}+\sqrt{V^\Delta_\ell C^\Delta_\ell}\big)>0$ and take, for $\ell\le L$,
  $$n^t_\ell=\varepsilon^{-2}S\sqrt{V^t_\ell/C^t_\ell},\qquad n^\Delta_\ell=\varepsilon^{-2}S\sqrt{V^\Delta_\ell/C^\Delta_\ell},$$
  with any positive values beyond $L$. This allocation meets the constraint with equality and costs exactly $c^\star$. The Cauchy–Schwarz inequality gives (b).

---

## 2. `nested_saving`

**Reading in one paragraph.** Take any $L\in\mathbb N$, real sequences $V^t,C^t,V^\Delta,C^\Delta,V,C$ and reals $\varepsilon,\delta,\theta,\kappa,r$ that satisfy the sign conditions and the level-wise comparison conditions listed below. Then
$$(\varepsilon^2)^{-1}\Big(\sum_{\ell=0}^{L}\big(\sqrt{V^t_\ell C^t_\ell}+\sqrt{V^\Delta_\ell C^\Delta_\ell}\big)\Big)^2\ \le\ (1+\delta)^2\,\theta\,(1+\kappa)\,r\cdot(\varepsilon^2)^{-1}\Big(\sum_{\ell=0}^{L}\sqrt{V_\ell C_\ell}\Big)^2 .$$

**Arguments, in order.**

1. $L\in\mathbb N$ (explicit; section variable).
2. $V^t,C^t,V^\Delta,C^\Delta:\mathbb N\to\mathbb R$ (explicit; section variables in the order `Vt Ct VΔ CΔ`).
3. $V,C:\mathbb N\to\mathbb R$ (explicit).
4. $\varepsilon,\delta,\theta,\kappa,r\in\mathbb R$ (implicit). $\varepsilon$ occurs only in the conclusion.
5. The twelve hypotheses below (explicit).

There are no typeclass or instance arguments. The statement is universally quantified over everything above, and the hypotheses imply the conclusion.

**Hypotheses, in order.**

1. $V^t_\ell\ge0$ for all $\ell\in\mathbb N$.
2. $C^t_\ell\ge0$ for all $\ell\in\mathbb N$.
3. $C^\Delta_\ell>0$ for all $\ell\in\mathbb N$.
4. $V_\ell\ge0$ for all $\ell\in\mathbb N$.
5. $C_\ell\ge0$ for all $\ell\in\mathbb N$.
6. $\delta\ge0$.
7. $\theta\ge0$.
8. $1+\kappa\ge0$.
9. For every $\ell\in\{0,\dots,L\}$: $\;C^t_\ell/C^\Delta_\ell\le r$.
10. For every $\ell\in\{0,\dots,L\}$: $\;V^\Delta_\ell\le\delta^2\,(C^t_\ell/C^\Delta_\ell)\,V^t_\ell$.
11. For every $\ell\in\{0,\dots,L\}$: $\;V^t_\ell\le\theta\,V_\ell$.
12. For every $\ell\in\{0,\dots,L\}$: $\;C^\Delta_\ell\le(1+\kappa)\,C_\ell$.

**Conclusion.** Exactly the displayed inequality above. On the right, the product is $(1+\delta)^2\cdot\theta\cdot(1+\kappa)\cdot r$ times the whole bracket $(\varepsilon^2)^{-1}\big(\sum_\ell\sqrt{V_\ell C_\ell}\big)^2$. On both sides the square applies to the whole sum over levels.

**Conventions that matter here.**

- $(\varepsilon^2)^{-1}=0$ when $\varepsilon=0$.
- $\sqrt{x}=0$ for $x<0$.
- Every division is by $C^\Delta_\ell>0$, so none is a junk division.

**Edge cases and observations.**

- **The role of $\varepsilon$.** There is no hypothesis on $\varepsilon$.
  - If $\varepsilon=0$, both sides equal $0$ and the claim is $0\le0$, which is trivially true.
  - If $\varepsilon\ne0$, the common factor $\varepsilon^{-2}>0$ cancels, and the sign of $\varepsilon$ is irrelevant.
  - So the statement is equivalent to the $\varepsilon$-free inequality
  $$\Big(\sum_{\ell=0}^{L}\big(\sqrt{V^t_\ell C^t_\ell}+\sqrt{V^\Delta_\ell C^\Delta_\ell}\big)\Big)^2\le(1+\delta)^2\theta(1+\kappa)\,r\Big(\sum_{\ell=0}^{L}\sqrt{V_\ell C_\ell}\Big)^2 .$$
- **Signs of the parameters.**
  - $r<0$ is impossible under the hypotheses. Hypothesis 9 at $\ell=0$, together with $C^t_0\ge0$ and $C^\Delta_0>0$, forces $r\ge0$.
  - $\delta<0$ is excluded by hypothesis 6.
  - $\kappa$ may be negative. However, hypothesis 12 with $C^\Delta_\ell>0$ forces $1+\kappa>0$ and $C_\ell>0$ for all $\ell\le L$.
- **No sign condition on $V^\Delta$.** If $V^\Delta_\ell<0$, the corresponding term $\sqrt{V^\Delta_\ell C^\Delta_\ell}$ is $0$.
- **What the inequality compares.** It compares two closed-form numbers.
  - The statement does not assert that the factor $(1+\delta)^2\theta(1+\kappa)r$ is below $1$. It holds whatever the size of that factor.
  - Neither side is related to an estimator, a random variable or an actual cost.
  - $V$ and $C$ are arbitrary non-negative sequences. They are connected to the other data only through hypotheses 11 and 12.
  - The left side is literally the same expression as the least value in `nested_cost_isLeast`. The right-hand bracket has the same shape with a single square-root term per level. Nothing in this packet states that the right-hand bracket is the minimum of any optimisation problem.
- **Levels covered.** The sign hypotheses are imposed at every $\ell\in\mathbb N$. The comparison hypotheses 9–12 are imposed only for $\ell\le L$.
- **Not vacuous.** For example, take all of $V^t,C^t,C^\Delta,V,C$ equal to $1$, $V^\Delta=0$, $\delta=0$, $\theta=r=1$ and $\kappa=0$. All hypotheses hold and the conclusion holds with equality.
- **Consistency check** (mine, not part of the statement). Term by term, $\sqrt{V^\Delta C^\Delta}\le\delta\sqrt{V^tC^t}$ and
  $$\sqrt{V^tC^t}=\sqrt{V^t\,(C^t/C^\Delta)\,C^\Delta}\le\sqrt{\theta r(1+\kappa)}\,\sqrt{VC}.$$

---

## 3. `nestedEstimator_mean_variance`

**Reading in one paragraph.**

- Let $(\Omega,\mu)$ be a probability space and $(\Omega_0,\nu)$ a measurable space with a measure.
- Let $\omega_q:\Omega\to\Omega_0$, for $q=((\ell,b),n)\in(\mathbb N\times\mathrm{Bool})\times\mathbb N$, be mutually independent random elements, each with law $\nu$.
- Let $P_\ell,D_\ell:\Omega_0\to\mathbb R$ be measurable and square-integrable under $\nu$ for every $\ell$.
- Let the sample numbers $N^t_\ell,N^\Delta_\ell$ be $\ge1$ for every $\ell$.

Then the estimator $\widehat Y$ (expanded below) has $\mu$-mean $\int P_L\,d\nu$. Its $\mu$-variance is
$$\sum_{\ell=0}^{L}\Big(\frac{\operatorname{Var}_\nu(D_\ell)}{N^t_\ell}+\frac{\operatorname{Var}_\nu(\Delta P_\ell-D_\ell)}{N^\Delta_\ell}\Big).$$

**Arguments, in order.**

1. Section variables, all included because the statement uses them:
   - implicit types $\Omega_0,\Omega$;
   - instance arguments: a σ-algebra on $\Omega_0$ and a σ-algebra on $\Omega$;
   - an implicit measure $\nu$ on $\Omega_0$ and an implicit measure $\mu$ on $\Omega$;
   - implicit sequences $P=(P_\ell)$ and $D=(D_\ell)$ of functions $\Omega_0\to\mathbb R$ (Lean `Pl`, `Dt`);
   - the implicit family $\omega=(\omega_q)$ of maps $\Omega\to\Omega_0$.
2. The theorem's own binders:
   - the instance argument "$\mu$ is a probability measure";
   - hypotheses 1–6 below;
   - explicit $L\in\mathbb N$;
   - implicit $N^t,N^\Delta:\mathbb N\to\mathbb N$;
   - hypotheses 7–8 below.

Hypotheses 1–6 do not mention $L$ or the $N$'s, so the statement is equivalent to "for all of the data, the hypotheses imply the conclusion".

**Hypotheses, in order.**

0. (Instance) $\mu$ is a probability measure: $\mu(\Omega)=1$.
1. For every index $q=((\ell,b),n)$, the map $\omega_q$ is measure-preserving from $(\Omega,\mu)$ to $(\Omega_0,\nu)$. That is, $\omega_q$ is measurable and its image measure is $\nu$: $\mu(\omega_q^{-1}(A))=\nu(A)$ for every measurable $A\subseteq\Omega_0$.
2. The whole family $(\omega_q)_q$ is mutually independent under $\mu$ (`iIndepFun`). For every finite set $F$ of indices and every choice of measurable sets $A_q\subseteq\Omega_0$ for $q\in F$,
   $$\mu\Big(\bigcap_{q\in F}\omega_q^{-1}(A_q)\Big)=\prod_{q\in F}\mu\big(\omega_q^{-1}(A_q)\big).$$
3. Every $P_\ell$ is measurable, from the σ-algebra of $\Omega_0$ to the Borel sets of $\mathbb R$.
4. Every $D_\ell$ is measurable.
5. Every $P_\ell$ is in $L^2(\nu)$: it is a.e. strongly measurable and $\int|P_\ell|^2\,d\nu<\infty$.
6. Every $D_\ell$ is in $L^2(\nu)$.
7. $N^t_\ell>0$, that is $N^t_\ell\ge1$, for every $\ell\in\mathbb N$.
8. $N^\Delta_\ell>0$ for every $\ell\in\mathbb N$.

**Definitions used, expanded.** Write $\Delta P_0=P_0$ and $\Delta P_\ell=P_\ell-P_{\ell-1}$ for $\ell\ge1$ (this is `levelDiff`).

`nestedTerm P D` is built with `pairFam` on the index $(\ell,b)$. It sends flag $\mathrm{true}$ to $D_\ell$ and flag $\mathrm{false}$ to $\Delta P_\ell-D_\ell$. Here "if $b$ then" means "if $b=\mathrm{true}$".

`nestedEstimator Pl Dt ω L Nt NΔ` sums, over levels $\ell\le L$, two `blockMean`s. The first is block $(\ell,\mathrm{true})$ with $N^t_\ell$ samples. The second is block $(\ell,\mathrm{false})$ with $N^\Delta_\ell$ samples. Written out:
$$\widehat Y(x)=\sum_{\ell=0}^{L}\Bigg[\frac{1}{N^t_\ell}\sum_{n=0}^{N^t_\ell-1}D_\ell\big(\omega_{((\ell,\mathrm{true}),n)}(x)\big)+\frac{1}{N^\Delta_\ell}\sum_{n=0}^{N^\Delta_\ell-1}\Big(\Delta P_\ell\big(\omega_{((\ell,\mathrm{false}),n)}(x)\big)-D_\ell\big(\omega_{((\ell,\mathrm{false}),n)}(x)\big)\Big)\Bigg].$$
The false-block evaluates $P_\ell$, $P_{\ell-1}$ and $D_\ell$ at the same sample point.

**Conclusion.** Both of the following hold:
$$\text{(i)}\qquad \int_\Omega\widehat Y\,d\mu=\int_{\Omega_0}P_L\,d\nu ;$$
$$\text{(ii)}\qquad \operatorname{Var}_\mu\big(\widehat Y\big)=\sum_{\ell=0}^{L}\Bigg(\frac{\operatorname{Var}_\nu(D_\ell)}{N^t_\ell}+\frac{\operatorname{Var}_\nu\big(\Delta P_\ell-D_\ell\big)}{N^\Delta_\ell}\Bigg).$$
In (ii), $N^t_\ell$ and $N^\Delta_\ell$ are cast to reals and are nonzero.

**Library notions and conventions.**

- The integrals are Bochner integrals, which would be $0$ for a non-integrable integrand; that case does not arise here.
- `variance X m` is `ENNReal.toReal` of the extended-real lower integral $\int^{-}|X-\mathbb E_m X|^2\,dm\in[0,\infty]$; `toReal` sends $\infty$ to $0$. For $X\in L^2$ of a probability measure it is the usual variance. The $\infty\mapsto0$ case does not arise here.
- `MeasurePreserving` and `iIndepFun` are exactly as spelled out in hypotheses 1–2.

**Edge cases and observations.**

- **$\nu$ is forced to be a probability measure.** It is not declared to be one, but hypothesis 1 makes $\nu$ the image of the probability measure $\mu$, so $\nu(\Omega_0)=1$.
- **The i.i.d. family.** Hypotheses 1 and 2 together say the $\omega_q$ are i.i.d. with law $\nu$.
  - The family is countably infinite: every level $\ell\in\mathbb N$, both flags and every $n\in\mathbb N$, although only $\ell\le L$ and $n<N$ are used.
  - Such a family exists for every probability measure $\nu$: take the infinite product space with its coordinate maps (Mathlib has `Measure.infinitePi`). So the statement is **not vacuous**.
- **One sample law for all levels.** The same law $\nu$ is used at every level and for both flags. The dependence on the level enters only through the functions $P_\ell$ and $D_\ell$.
- **Mutual independence.** The hypothesis is full mutual independence, which is stronger than the pairwise independence a variance identity alone would use. The theorem therefore covers fewer situations than a pairwise version would.
- **Zero sample numbers are excluded.** Sample numbers must be $\ge1$ at every $\ell\in\mathbb N$, not only for $\ell\le L$; the part beyond $L$ is stronger than needed. With a zero count the corresponding block would contribute $0$ (because $0^{-1}=0$), and (i) would generally fail.
- **Extra measurability.** Hypotheses 3–4 require everywhere Borel measurability. This is on top of the a.e. strong measurability already contained in hypotheses 5–6.
- **What the conclusions refer to.** (i) is the $\nu$-mean of the single function $P_L$. (ii) uses $\nu$-variances of $D_\ell$ and of $\Delta P_\ell-D_\ell$. The variance of $\Delta P_\ell$ alone does not appear. Costs play no role.

---

## 4. `nestedCost_mean`

**Reading in one paragraph.** Let $\mu$ be any measure on a measurable space $\Omega$; it need not be finite or a probability measure. Let $c^t_{\ell,n},c^\Delta_{\ell,n}:\Omega\to\mathbb R$ be $\mu$-integrable for all $\ell,n\in\mathbb N$, with $\int c^t_{\ell,n}\,d\mu=C^t_\ell$ and $\int c^\Delta_{\ell,n}\,d\mu=C^\Delta_\ell$ for all $\ell,n$. Then for every $L\in\mathbb N$ and all $N^t,N^\Delta:\mathbb N\to\mathbb N$, the $\mu$-integral of the total cost equals $\sum_{\ell=0}^{L}\big(N^t_\ell C^t_\ell+N^\Delta_\ell C^\Delta_\ell\big)$.

**Arguments, in order.**

1. Section variables:
   - the implicit type $\Omega$;
   - the instance argument: a σ-algebra on $\Omega$;
   - the implicit measure $\mu$ on $\Omega$.
   The section's other variables are not mentioned in the statement, so they are not arguments: $\Omega_0$ and its σ-algebra, $\nu$, $P$, $D$ and $\omega$.
2. Explicit $c^t,c^\Delta:\mathbb N\to\mathbb N\to(\Omega\to\mathbb R)$ (Lean `costT`, `costΔ`).
3. Explicit $C^t,C^\Delta:\mathbb N\to\mathbb R$.
4. Hypotheses 1–4 below.
5. Explicit $L\in\mathbb N$ and explicit $N^t,N^\Delta:\mathbb N\to\mathbb N$.

There is no probability-measure instance.

**Hypotheses.**

1. $c^t_{\ell,n}$ is $\mu$-integrable for all $\ell,n\in\mathbb N$: it is a.e. strongly measurable and $\int|c^t_{\ell,n}|\,d\mu<\infty$.
2. $c^\Delta_{\ell,n}$ is $\mu$-integrable for all $\ell,n\in\mathbb N$.
3. $\int_\Omega c^t_{\ell,n}\,d\mu=C^t_\ell$ for all $\ell,n\in\mathbb N$.
4. $\int_\Omega c^\Delta_{\ell,n}\,d\mu=C^\Delta_\ell$ for all $\ell,n\in\mathbb N$.

**Definition used, expanded** (`nestedCost`, a raw total):
$$\operatorname{Cost}(x)=\sum_{\ell=0}^{L}\Big(\sum_{n=0}^{N^t_\ell-1}c^t_{\ell,n}(x)+\sum_{n=0}^{N^\Delta_\ell-1}c^\Delta_{\ell,n}(x)\Big).$$

**Conclusion.**
$$\int_\Omega\operatorname{Cost}\,d\mu=\sum_{\ell=0}^{L}\big(N^t_\ell\,C^t_\ell+N^\Delta_\ell\,C^\Delta_\ell\big),$$
with $N^t_\ell$ and $N^\Delta_\ell$ cast to reals.

**Edge cases and observations.**

- **Only linearity.** This is a direct consequence of linearity of the integral. It uses no independence, no probability normalisation and no sign condition; costs may be negative. There is no link between the cost functions and any sampler, estimator, or the section's $\omega$ and $\nu$.
- **What is assumed.** The sample counts are deterministic. Every sample at a given level has the same mean ($C^t_\ell$, respectively $C^\Delta_\ell$). The hypotheses are imposed for all $(\ell,n)\in\mathbb N^2$, including indices the sum never uses.
- **Zero counts are allowed.** A zero count gives an empty sum, which is $0$, on both sides consistently.
- **Integrability matters.** Hypotheses 1–2 make the integrals in 3–4 genuine. Without them the Bochner integral could be the junk value $0$.
- **Not vacuous.** For example, constant cost functions on a probability space satisfy everything.

---

## 5. `nested_mlmc_mse`

**Reading in one paragraph.**

- Let $(\Omega,\mu)$ be a probability space.
- Let $P_\ell$ and $D_\ell$ be $\mu$-integrable real random variables.
- Let $Y^t_\ell$ and $Y^\Delta_\ell$ be square-integrable real random variables, for every $\ell\in\mathbb N$.
- Suppose that among levels $0,\dots,L$ the $2(L+1)$ variables $Y^t_\ell,Y^\Delta_\ell$ are pairwise independent.
- Suppose that $\mathbb E Y^t_\ell=\mathbb E D_\ell$ and $\mathbb E Y^\Delta_\ell=\mathbb E[\Delta P_\ell-D_\ell]$ for every $\ell$.

Then $Z=\sum_{\ell=0}^{L}(Y^t_\ell+Y^\Delta_\ell)$ has mean $\mathbb E P_L$ and variance $\sum_{\ell=0}^{L}(\operatorname{Var}Y^t_\ell+\operatorname{Var}Y^\Delta_\ell)$. For every real $m$, its mean-square deviation from $m$ equals that variance plus $(\mathbb E P_L-m)^2$.

**Arguments, in order.**

1. Section variables:
   - the implicit type $\Omega$;
   - the instance argument: a σ-algebra on $\Omega$;
   - the implicit measure $\mu$;
   - the instance argument "$\mu$ is a probability measure", included because its only dependency, $\mu$, is included.
2. Explicit $P,D,Y^t,Y^\Delta:\mathbb N\to(\Omega\to\mathbb R)$ (Lean `Pℓ Dt Yt YΔ`; here `Pℓ` names the whole sequence).
3. Explicit $L\in\mathbb N$ and explicit $m\in\mathbb R$.
4. The seven hypotheses below.

All four sequences live on the same space $\Omega$. The bound variable called $\omega$ inside `fun ω => …` is just a point of $\Omega$.

**Hypotheses, in order.**

0. (Instance) $\mu(\Omega)=1$.
1. $Y^t_\ell\in L^2(\mu)$ for every $\ell\in\mathbb N$.
2. $Y^\Delta_\ell\in L^2(\mu)$ for every $\ell\in\mathbb N$.
3. $P_\ell$ is $\mu$-integrable for every $\ell\in\mathbb N$.
4. $D_\ell$ is $\mu$-integrable for every $\ell\in\mathbb N$.
5. Pairwise independence on $\operatorname{nIdx}(L)=\{0,\dots,L\}\times\{\mathrm{true},\mathrm{false}\}$.
   - Put $Z_{(\ell,\mathrm{true})}=Y^t_\ell$ and $Z_{(\ell,\mathrm{false})}=Y^\Delta_\ell$ (this is `pairFam`, where "if $b$" means "if $b=\mathrm{true}$").
   - For all distinct $i\ne j$ in $\operatorname{nIdx}(L)$, the variables $Z_i$ and $Z_j$ are independent under $\mu$. That is, $\mu(Z_i^{-1}A\cap Z_j^{-1}B)=\mu(Z_i^{-1}A)\,\mu(Z_j^{-1}B)$ for all Borel $A,B\subseteq\mathbb R$.
   - This covers $Y^t_\ell$ versus $Y^\Delta_\ell$ at the same level, as well as every cross-level pair.
6. $\mathbb E_\mu[Y^t_\ell]=\mathbb E_\mu[D_\ell]$ for every $\ell\in\mathbb N$.
7. $\mathbb E_\mu[Y^\Delta_\ell]=\mathbb E_\mu[\Delta P_\ell-D_\ell]$ for every $\ell\in\mathbb N$. Here $\Delta P_0=P_0$ and $\Delta P_\ell=P_\ell-P_{\ell-1}$ for $\ell\ge1$ (`levelDiff`).

**Conclusion.** Let $Z=\sum_{\ell=0}^{L}(Y^t_\ell+Y^\Delta_\ell)$. All three of the following hold:
$$\text{(i)}\quad \mathbb E_\mu[Z]=\mathbb E_\mu[P_L];$$
$$\text{(ii)}\quad \operatorname{Var}_\mu(Z)=\sum_{\ell=0}^{L}\big(\operatorname{Var}_\mu(Y^t_\ell)+\operatorname{Var}_\mu(Y^\Delta_\ell)\big);$$
$$\text{(iii)}\quad \mathbb E_\mu\big[(Z-m)^2\big]=\sum_{\ell=0}^{L}\big(\operatorname{Var}_\mu(Y^t_\ell)+\operatorname{Var}_\mu(Y^\Delta_\ell)\big)+\big(\mathbb E_\mu[P_L]-m\big)^2 .$$
How the operators parse: Lean parses the body of a `∑` at precedence 67, higher than that of `+` and `-` (65). So a `+` or `-` written after the parenthesised summand ends the sum. In (iii) this means $m$ is subtracted from the whole sum $Z$ (not per term), and the squared bias is added once, outside the sum over levels.

**Library notions and conventions.**

- $\mathbb E_\mu$ is the Bochner integral, and hypotheses 1–4 make every expectation here genuine.
- `variance` is `ENNReal.toReal` of the $[0,\infty]$-valued $\int^-|X-\mathbb E X|^2\,d\mu$, with $\infty$ sent to $0$. It is the usual variance for these $L^2$ variables.
- `IndepFun` is independence of the σ-algebras generated by the two variables, with the Borel σ-algebra on $\mathbb R$.
- `Set.Pairwise s r` means $r(i,j)$ for all $i,j\in s$ with $i\ne j$.

**Edge cases and observations.**

- **The statement is abstract.** $Y^t_\ell$ and $Y^\Delta_\ell$ are arbitrary square-integrable variables with prescribed means. The statement involves no sample averages, no sample sizes, no sample law and no reference to `nestedEstimator` or `blockMean`.
  - $P$ and $D$ enter only through their means $\mathbb E P_L$, $\mathbb E D_\ell$ and $\mathbb E[\Delta P_\ell-D_\ell]$.
  - Conclusions (ii) and (iii) involve variances of the $Y$'s only, never of $D_\ell$ or $\Delta P_\ell-D_\ell$.
- **Only pairwise independence.** It is only pairwise, not mutual, and only among levels $0,\dots,L$.
- **Levels beyond $L$.** Hypotheses 1–4, 6 and 7 are imposed for all $\ell\in\mathbb N$, which is stronger than needed.
- **$m$ is arbitrary.** It is any real number.
- **Not vacuous.** Take $Y^t_\ell$ to be the constant $\mathbb E D_\ell$ and $Y^\Delta_\ell$ the constant $\mathbb E[\Delta P_\ell-D_\ell]$. Constants are independent of everything, so all hypotheses hold for any integrable $P,D$, and then (ii) reads $0=0$.

---

## Flags at a glance

- **Vacuous statements:** none. Every hypothesis set is satisfiable; the witnesses are given above.
- **Trivial in a special case:** `nested_saving` at $\varepsilon=0$, where both sides are $0$. For $\varepsilon\ne0$ the factor $\varepsilon^{-2}$ cancels, so $\varepsilon$ plays no real role.
- **Weaker or different from what it may look like:**
  - `nested_cost_isLeast` is over real, not integer, sample sizes, with a variance-only constraint $\le\varepsilon^2$.
  - `nested_saving` is an inequality between closed-form numbers with free $V,C$, and it does not assert that the factor is $<1$.
  - `nestedCost_mean` is a pure linearity identity for an arbitrary measure, with costs unrelated to sampling.
  - `nested_mlmc_mse` concerns arbitrary pairwise-independent $L^2$ variables with prescribed means, not the `nestedEstimator` construction.
- **Hypotheses stronger than needed (harmless):**
  - positivity or integrability conditions imposed at every $\ell\in\mathbb N$ rather than only $\ell\le L$ (all five theorems);
  - full mutual independence, and everywhere measurability on top of $L^2$ (`nestedEstimator_mean_variance`).
