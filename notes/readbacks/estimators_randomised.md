# Blind read-back — packets 7 and 8

**Declarations covered** (all in namespace `MLMC`)

*Packet 7*

1. `levelDiff` (definition)
2. `sum_integral_levelDiff` (lemma)
3. `blockMean` (definition)
4. `integral_blockMean` (lemma)
5. `variance_blockMean` (lemma)
6. `indepFun_blockMean` (lemma)
7. `levelEstimator` (definition)
8. `mlmcEstimator` (definition)
9. `mlmcEstimator_mean_variance` (theorem)

*Packet 8*

10. `levelDiff` (definition; same code as item 1, used with $\Omega_0 := \Omega$)
11. `singleTerm` (definition)
12. `singleTermN` (definition)
13. `geomLevelProb` (definition)
14. `optimalLevelProb` (definition)
15. `integral_cost_level` (theorem)
16. `randomised_necessary` (theorem)
17. `singleTermN_mean_variance` (theorem)
18. `randomised_optimal_p_isLeast` (theorem)
19. `randomised_mlmc_finite` (theorem)

**Inputs used:** `readback/packet7.lean`, `readback/packet8.lean`, `prove2me_workspace/references/mission_auditor.md`. Library meanings were checked in Mathlib source at commit 0df444a: the independence definitions (`iIndepFun`, `IndepFun` and their kernel versions), `iIndepFun.isProbabilityMeasure`, `variance`/`evariance`/`variance_of_not_memLp`, the `P[X]` expectation macro, the Bochner `integral`, `Measure.real`, `MeasurePreserving`, `MemLp`, `Integrable`, `HasSum`/`Summable`/`tsum` with the `unconditional` summation filter, `Real.sqrt`, `Real.rpow`, `IsLeast`/`lowerBounds` and `Nat.instMeasurableSpace`. To check that the hypotheses can be satisfied I also used `Measure.infinitePi` and `iIndepFun_infinitePi`. The Lean core rule for including section variables comes from `Lean/Elab/MutualDef.lean`. Apart from a directory listing, I opened no other project file, and I compiled nothing.

---

## Conventions that apply throughout (checked in the library source)

- **Section variables.** A section `variable` becomes part of a statement only in two cases: the statement mentions it, or it is an instance argument whose own parameters are all already included. `omit` removes a variable. So a section's `[IsProbabilityMeasure μ]` is a hypothesis of every statement that mentions $\mu$, unless it is omitted.
- **Integral.** $\int f\,d\mu$ is written `∫ x, f x ∂μ` in Lean, and `μ[f]` is the `ProbabilityTheory` macro for the same expression. It is the Bochner integral: the usual integral when $f$ is $\mu$-integrable, and **defined to be $0$ when $f$ is not integrable**.
- `Integrable f μ` means $f$ is $\mu$-a.e. strongly measurable and $\int^-|f|\,d\mu<\infty$. Here $\int^-$ is the Lebesgue integral with values in $[0,\infty]$.
- `MemLp f 2 μ` means $f$ is $\mu$-a.e. strongly measurable and $\int^-|f|^2\,d\mu<\infty$, i.e. $f\in L^2(\mu)$. On a finite measure this implies integrability.
- `Measurable` refers to the Borel σ-algebra on $\mathbb R$. On $\mathbb N$ every subset is measurable, so $K:\Omega\to\mathbb N$ is measurable exactly when every fibre $\{K=\ell\}$ is measurable.
- `MeasurePreserving g μ ν` means $g$ is measurable and the image measure $\mu\circ g^{-1}$ equals $\nu$. If $\mu$ is a probability measure, $\nu$ must then be one too.
- `μ.real s` is $\operatorname{toReal}(\mu(s))$: the measure as a real number, with $\infty\mapsto 0$.
- `IndepFun X Y μ` means: for every $A\in\sigma(X)$ and every $B\in\sigma(Y)$ (the preimage σ-algebras), $\mu(A\cap B)=\mu(A)\,\mu(B)$ in $[0,\infty]$. This alone does **not** make $\mu$ a probability measure. Taking $A=B=\Omega$ only gives $\mu(\Omega)\in\{0,1,\infty\}$.
- `iIndepFun X μ` for a family $(X_q)_{q\in Q}$ is mutual independence: for every finite $S\subseteq Q$ and every choice $A_q\in\sigma(X_q)$, $\mu\big(\bigcap_{q\in S}A_q\big)=\prod_{q\in S}\mu(A_q)$. The case $S=\varnothing$ gives $\mu(\Omega)=1$, so `iIndepFun` **forces $\mu$ to be a probability measure** (Mathlib lemma `iIndepFun.isProbabilityMeasure`).
- **Variance.** Mathlib's `variance X μ` is $\operatorname{Var}_\mu(X)=\operatorname{toReal}\big(\int^-|X-\mu[X]|^2\,d\mu\big)$, where $\mu[X]$ is the Bochner integral above.
  - It is always $\ge 0$.
  - It is the usual variance when $\mu$ is a probability measure and $X\in L^2(\mu)$.
  - It is **$0$** when $\mu$ is finite and $X$ is a.e. strongly measurable but not in $L^2(\mu)$ (`variance_of_not_memLp`).
- **Series.**
  - `HasSum a s` means the finite partial sums $\sum_{\ell\in F}a_\ell$ (over finite $F\subseteq\mathbb N$) converge to $s$ along the directed family of finite sets. This is unconditional summation, the default summation filter at this commit.
  - `Summable a` means some such $s$ exists. For real sequences this is the same as $\sum_\ell|a_\ell|<\infty$.
  - $\sum'_\ell a_\ell$ (`tsum`) is that sum when the series is summable, and **$0$ otherwise**.
- `IsLeast S a` means $a\in S$ and $a\le x$ for every $x\in S$: $a$ is a minimum of $S$ and is attained.
- `Tendsto u atTop (𝓝 a)` for $u:\mathbb N\to\mathbb R$ means $u_L\to a$ as $L\to\infty$.
- **Square roots and powers.** $\sqrt{x}$ (`Real.sqrt`) equals $\sqrt{\max(x,0)}$, so it is $0$ for negative $x$. A power $2^{t}$ with real exponent is `Real.rpow` and is $>0$ for every real $t$. A power $y^{\ell}$ with $\ell\in\mathbb N$ is the ordinary power.
- **Arithmetic.** $(N:\mathbb R)$ is the cast of $N\in\mathbb N$. By convention $0^{-1}=0$ and $x/0=0$. The index set $\{0,\dots,N-1\}$ (`range N`) is empty for $N=0$, and an empty sum is $0$.

---

## Packet 7

Context: `open MeasureTheory ProbabilityTheory Finset`. In this packet $\omega$ always names a *family of maps* $\Omega\to\Omega_0$, and points of $\Omega$ are written $x$.

### 1. `levelDiff` (definition)

**Parameters.** A type $\Omega_0$, with no σ-algebra needed, and a sequence $P=(P_\ell)_{\ell\in\mathbb N}$ of functions $P_\ell:\Omega_0\to\mathbb R$ (Lean `Pl`).

**Value.** The sequence $(\Delta P_\ell)_{\ell\in\mathbb N}$ of functions $\Omega_0\to\mathbb R$ given by
$$\Delta P_0=P_0,\qquad \Delta P_{\ell+1}(y)=P_{\ell+1}(y)-P_\ell(y)\qquad(\ell\in\mathbb N,\ y\in\Omega_0).$$

**Remarks.** The two terms of each difference are evaluated at the same point $y$. The definition is total and produces no junk values.

### 2. `sum_integral_levelDiff` (lemma)

**Binders, in order** (all universally quantified; no instance other than the σ-algebra):

1. a type $\Omega_0$ with a σ-algebra;
2. a measure $\nu$ on $\Omega_0$. It is **arbitrary**: no finiteness or probability assumption appears;
3. a sequence $P=(P_\ell)_{\ell\in\mathbb N}$ with $P_\ell:\Omega_0\to\mathbb R$;
4. (`hPl`) for **every** $\ell\in\mathbb N$, $P_\ell$ is $\nu$-integrable;
5. $L\in\mathbb N$.

**Definition used.** $\Delta P_0=P_0$ and $\Delta P_\ell=P_\ell-P_{\ell-1}$ for $\ell\ge1$, pointwise.

**Conclusion.**
$$\sum_{\ell=0}^{L}\int_{\Omega_0}\Delta P_\ell\,d\nu\;=\;\int_{\Omega_0}P_L\,d\nu .$$

**Library notions and edge cases.**
- The integrals are Bochner integrals, which are $0$ when the integrand is not integrable. Under `hPl` every integrand here is integrable, so all of them are genuine integrals.
- For $L=0$ the statement reads $\int P_0\,d\nu=\int P_0\,d\nu$. For $\nu=0$ both sides are $0$.

**Observations.**
- This is a telescoping identity that holds for any measure.
- `hPl` is required for all $\ell$, including $\ell>L$, which the conclusion never uses. The hypothesis is stronger than needed, which is harmless.
- The statement is not vacuous, and nothing about it is suspicious.

### 3. `blockMean` (definition)

**Parameters.**
- Types $\iota$, $\Omega_0$, $\Omega$, with no σ-algebras.
- A family $f=(f_i)_{i\in\iota}$ with $f_i:\Omega_0\to\mathbb R$.
- A doubly indexed family $\omega=(\omega_{(i,n)})_{(i,n)\in\iota\times\mathbb N}$ of maps $\omega_{(i,n)}:\Omega\to\Omega_0$.
- An index $i\in\iota$, a number $N\in\mathbb N$ and a point $x\in\Omega$.

**Value.**
$$\bar f_{i,N}(x)=(N)^{-1}\sum_{n=0}^{N-1}f_i\big(\omega_{(i,n)}(x)\big).$$

**Remarks.**
- For $N\ge1$ this is the arithmetic mean of $f_i(\omega_{(i,0)}(x)),\dots,f_i(\omega_{(i,N-1)}(x))$.
- For $N=0$ it is $0^{-1}=0$ times an empty sum, so $\bar f_{i,0}\equiv 0$.
- Only the maps whose first index is $i$ and whose second index is below $N$ enter.

### 4. `integral_blockMean` (lemma)

**Binders, in order.**
1. types $\iota,\Omega_0,\Omega$, with σ-algebras on $\Omega_0$ and $\Omega$;
2. a measure $\nu$ on $\Omega_0$ and a measure $\mu$ on $\Omega$;
3. a family $f=(f_i)_{i\in\iota}$ with $f_i:\Omega_0\to\mathbb R$, and a family $\omega=(\omega_q)_{q\in\iota\times\mathbb N}$ with $\omega_q:\Omega\to\Omega_0$;
4. **instance: $\mu$ is a probability measure**;
5. (`hω`) for **every** $q\in\iota\times\mathbb N$, $\omega_q$ is measure preserving from $(\Omega,\mu)$ to $(\Omega_0,\nu)$: it is measurable and $\mu\circ\omega_q^{-1}=\nu$;
6. (`hf`) for every $i\in\iota$, $f_i$ is $\nu$-integrable;
7. an index $i\in\iota$;
8. $N\in\mathbb N$ (implicit) with (`hN`) $0<N$.

**Definition used.** $\bar f_{i,N}(x)=N^{-1}\sum_{n=0}^{N-1}f_i(\omega_{(i,n)}(x))$.

**Conclusion.**
$$\int_\Omega \bar f_{i,N}\,d\mu\;=\;\int_{\Omega_0}f_i\,d\nu .$$

**Library notions and edge cases.**
- The left side is written `μ[blockMean f ω i N]`, which is the Bochner integral of $\bar f_{i,N}$ against $\mu$.
- Under the hypotheses both integrands are integrable ($f_i\circ\omega_{(i,n)}$ is $\mu$-integrable because $\omega_{(i,n)}$ preserves measure), so both integrals are genuine.
- $N=0$ is excluded, and the exclusion matters: it would make the left side $0$.

**Observations.**
- No independence is assumed, only that each $\omega_q$ has law $\nu$.
- $\mu$ is a probability measure and each $\omega_q$ is measurable, so `hω` forces $\nu$ to be a probability measure. If $\nu$ is not one, the hypotheses cannot hold.
- `hω` and `hf` are required for all $q$ and all $i$, not only for the ones $\bar f_{i,N}$ uses. They are stronger than needed, which is harmless.
- If $\iota$ is empty there is no $i$ and the statement is empty.
- Otherwise the hypotheses can be satisfied. For example, take a probability measure $\nu$, let $\Omega=\Omega_0^{\iota\times\mathbb N}$ carry the product measure, and let $\omega_q$ be the coordinate maps.
- The statement is not vacuous.

### 5. `variance_blockMean` (lemma)

**Binders, in order.**
1. types $\iota,\Omega_0,\Omega$, with σ-algebras on $\Omega_0$ and $\Omega$;
2. a measure $\nu$ on $\Omega_0$ and a measure $\mu$ on $\Omega$;
3. a family $f=(f_i)_{i\in\iota}$ with $f_i:\Omega_0\to\mathbb R$, and a family $\omega=(\omega_q)_{q\in\iota\times\mathbb N}$ with $\omega_q:\Omega\to\Omega_0$;
4. **instance: $\mu$ is a probability measure**;
5. (`hω`) every $\omega_q$ is measure preserving from $(\Omega,\mu)$ to $(\Omega_0,\nu)$;
6. (`hind`) the whole family $(\omega_q)_{q\in\iota\times\mathbb N}$ of $\Omega_0$-valued maps is mutually independent under $\mu$;
7. (`hfm`) every $f_i$ is Borel measurable;
8. (`hf`) every $f_i$ is in $L^2(\nu)$;
9. an index $i\in\iota$;
10. $N\in\mathbb N$ (implicit) with (`hN`) $0<N$.

**Definition used.** $\bar f_{i,N}(x)=N^{-1}\sum_{n=0}^{N-1}f_i(\omega_{(i,n)}(x))$.

**Conclusion.**
$$\operatorname{Var}_\mu\big(\bar f_{i,N}\big)\;=\;\frac{\operatorname{Var}_\nu(f_i)}{N}.$$
The division is real division by the cast of $N$, and both sides use Mathlib's variance.

**Library notions and edge cases.**
- Mathlib's variance is $\operatorname{toReal}\int^-|X-\int X|^2$. It is the usual variance for an $L^2$ function under a probability measure, and on a finite measure it is $0$ for a measurable function outside $L^2$.
- Here $\nu$ is forced to be a probability measure by `hω`, $f_i\in L^2(\nu)$, and each $f_i\circ\omega_{(i,n)}\in L^2(\mu)$. So both sides are genuine variances, not the junk value.
- The probability assumption on $\mu$ is stated explicitly and is also implied by `hind`.

**Observations.**
- Mutual independence is assumed for the entire family over $\iota\times\mathbb N$, not only for the $N$ maps that are used. This is stronger than needed and harmless.
- The hypotheses can be satisfied with an infinite product measure, so the statement is not vacuous.
- If $N=0$, both sides would be $0$: $\bar f_{i,0}\equiv0$ has variance $0$, and $x/0=0$. So `hN` is not actually needed for the equation to hold; this is harmless.

### 6. `indepFun_blockMean` (lemma)

**Binders, in order.**
1. types $\iota,\Omega_0,\Omega$, with σ-algebras on $\Omega_0$ and $\Omega$;
2. a measure $\mu$ on $\Omega$. The section's $\nu$ is not mentioned and so is not part of the statement, and **no probability-measure instance is written**;
3. a family $f=(f_i)_{i\in\iota}$ with $f_i:\Omega_0\to\mathbb R$, and a family $\omega=(\omega_q)_{q\in\iota\times\mathbb N}$ with $\omega_q:\Omega\to\Omega_0$;
4. (`hωm`) every $\omega_q$ is measurable;
5. (`hind`) the family $(\omega_q)_{q\in\iota\times\mathbb N}$ is mutually independent under $\mu$;
6. (`hfm`) every $f_i$ is Borel measurable;
7. indices $i,j\in\iota$ (implicit) with (`hij`) $i\neq j$;
8. $N_i,N_j\in\mathbb N$, arbitrary, with $0$ allowed.

**Definition used.** $\bar f_{k,M}(x)=M^{-1}\sum_{n=0}^{M-1}f_k(\omega_{(k,n)}(x))$, which is identically $0$ when $M=0$.

**Conclusion.** $\bar f_{i,N_i}$ and $\bar f_{j,N_j}$ are independent real random variables under $\mu$. That is, for all Borel sets $A,B\subseteq\mathbb R$,
$$\mu\big(\{\bar f_{i,N_i}\in A\}\cap\{\bar f_{j,N_j}\in B\}\big)=\mu\{\bar f_{i,N_i}\in A\}\cdot\mu\{\bar f_{j,N_j}\in B\}.$$

**Observations.**
- `IsProbabilityMeasure μ` is not written, but `hind` forces $\mu(\Omega)=1$ (the empty-intersection case of mutual independence). So $\mu$ is in fact a probability measure, and no generality is gained or lost.
- No integrability and no identical distribution are assumed.
- If $N_i=0$ or $N_j=0$, the corresponding block mean is the constant $0$, and the conclusion is trivially true in that case.
- The case $i=j$ is not covered.
- The statement is not vacuous.

### 7. `levelEstimator` (definition)

**Parameters.**
- Types $\Omega_0,\Omega$.
- A sequence $P=(P_\ell)$ with $P_\ell:\Omega_0\to\mathbb R$.
- A family $\omega=(\omega_{(\ell,n)})_{(\ell,n)\in\mathbb N\times\mathbb N}$ of maps $\omega_{(\ell,n)}:\Omega\to\Omega_0$.
- Numbers $\ell,N\in\mathbb N$ and a point $x\in\Omega$.

**Value.**
$$\hat Y_{\ell,N}(x)=(N)^{-1}\sum_{n=0}^{N-1}\Delta P_\ell\big(\omega_{(\ell,n)}(x)\big),\qquad \Delta P_0=P_0,\ \ \Delta P_\ell=P_\ell-P_{\ell-1}\ (\ell\ge1).$$

**Remarks.**
- For $\ell\ge1$ each summand is $P_\ell(\omega_{(\ell,n)}(x))-P_{\ell-1}(\omega_{(\ell,n)}(x))$, so both levels are evaluated at the same sample point.
- Level $\ell$ uses the maps $\omega_{(\ell,0)},\dots,\omega_{(\ell,N-1)}$.
- $N=0$ gives the value $0$.
- The formula is literally `blockMean` with index set $\mathbb N$ and functions $\Delta P$.

### 8. `mlmcEstimator` (definition)

**Parameters.**
- Types $\Omega_0,\Omega$.
- A sequence $P$ and a family $\omega$ as in item 7.
- $L\in\mathbb N$, and $N:\mathbb N\to\mathbb N$ giving a sample size for each level.
- A point $x\in\Omega$.

**Value.**
$$\hat Y_{L,N}(x)=\sum_{\ell=0}^{L}\hat Y_{\ell,N_\ell}(x)=\sum_{\ell=0}^{L}(N_\ell)^{-1}\sum_{n=0}^{N_\ell-1}\Delta P_\ell\big(\omega_{(\ell,n)}(x)\big).$$

**Remarks.** Only $N_0,\dots,N_L$ are used. A level with $N_\ell=0$ contributes $0$.

### 9. `mlmcEstimator_mean_variance` (theorem)

**Binders, in order.**
1. types $\Omega_0,\Omega$ with σ-algebras;
2. a measure $\nu$ on $\Omega_0$ and a measure $\mu$ on $\Omega$;
3. a sequence $P=(P_\ell)_{\ell\in\mathbb N}$ with $P_\ell:\Omega_0\to\mathbb R$, and a family $\omega=(\omega_{(\ell,n)})_{(\ell,n)\in\mathbb N\times\mathbb N}$ with $\omega_{(\ell,n)}:\Omega\to\Omega_0$;
4. **instance: $\mu$ is a probability measure**;
5. (`hω`) every $\omega_{(\ell,n)}$ is measure preserving from $(\Omega,\mu)$ to $(\Omega_0,\nu)$;
6. (`hind`) the whole family $(\omega_{(\ell,n)})_{(\ell,n)\in\mathbb N\times\mathbb N}$ is mutually independent under $\mu$;
7. (`hPlm`) every $P_\ell$ is Borel measurable;
8. (`hPl`) every $P_\ell$ is in $L^2(\nu)$;
9. $L\in\mathbb N$;
10. $N:\mathbb N\to\mathbb N$ (implicit) with (`hN`) $N_\ell>0$ for **every** $\ell\in\mathbb N$.

**Definitions used.**
- $\Delta P_0=P_0$ and $\Delta P_\ell=P_\ell-P_{\ell-1}$ for $\ell\ge 1$.
- $\hat Y_{L,N}=\sum_{\ell=0}^{L}N_\ell^{-1}\sum_{n=0}^{N_\ell-1}\Delta P_\ell\circ\omega_{(\ell,n)}$.

**Conclusion** (a conjunction of two equations).
$$\int_\Omega\hat Y_{L,N}\,d\mu=\int_{\Omega_0}P_L\,d\nu
\qquad\text{and}\qquad
\operatorname{Var}_\mu\big(\hat Y_{L,N}\big)=\sum_{\ell=0}^{L}\frac{\operatorname{Var}_\nu(\Delta P_\ell)}{N_\ell}.$$
Each summand is its own quotient $\operatorname{Var}_\nu(\Delta P_\ell)/N_\ell$, with $N_\ell$ cast to $\mathbb R$. The $\ell=0$ term is $\operatorname{Var}_\nu(P_0)/N_0$.

**Library notions and edge cases.**
- The integrals are Bochner integrals, which are $0$ when the integrand is not integrable.
- The variances are Mathlib's: $\operatorname{toReal}\int^-|X-\int X|^2$, which is $0$ on a finite measure for measurable functions outside $L^2$.
- Here `hω` forces $\nu$ to be a probability measure. With $P_\ell\in L^2(\nu)$, every $\Delta P_\ell$ is in $L^2(\nu)$ and $\hat Y_{L,N}\in L^2(\mu)$, so all integrals and variances in the statement are genuine.

**Observations.**
- The mean identity is exact and refers only to the finest level $P_L$. No limiting target quantity appears.
- `hN` is imposed for all $\ell$, although only $\ell\le L$ affects the estimator. This is harmless, since the conclusion depends only on $N_0,\dots,N_L$.
- Independence is assumed for the entire $\mathbb N\times\mathbb N$ family.
- The hypotheses can be satisfied with an i.i.d. family from an infinite product measure, so the statement is not vacuous.

---

## Packet 8

Context: `open MeasureTheory ProbabilityTheory Finset Filter Topology`, and the global variables $\Omega$ (a type), its σ-algebra and $\mu$ (a measure on $\Omega$). In this packet $\omega$ denotes a *point* of $\Omega$. $(P_\ell)_{\ell\in\mathbb N}$ is Lean `Pl`. Where a separate function $P$ (Lean `P`) occurs, it is unrelated to $(P_\ell)$ except through the stated hypotheses.

### 10. `levelDiff` (definition)

**Parameters and value.** This is the same code as item 1. For a type $\Omega_0$ and functions $P_\ell:\Omega_0\to\mathbb R$:
$$\Delta P_0=P_0,\qquad \Delta P_{\ell+1}(y)=P_{\ell+1}(y)-P_\ell(y).$$
In this packet it is applied with $\Omega_0=\Omega$.

### 11. `singleTerm` (definition)

**Parameters.**
- A type $\Omega$; its σ-algebra is explicitly omitted and not needed.
- A sequence $P=(P_\ell)$ with $P_\ell:\Omega\to\mathbb R$.
- A map $K:\Omega\to\mathbb N$ and a sequence $p:\mathbb N\to\mathbb R$.
- A point $\omega\in\Omega$.

**Value.**
$$Y(\omega)=\big(p_{K(\omega)}\big)^{-1}\cdot\Delta P_{K(\omega)}(\omega),\qquad \Delta P_0=P_0,\ \ \Delta P_\ell=P_\ell-P_{\ell-1}\ (\ell\ge1).$$

**Remarks.**
- The level $K(\omega)$ and the level difference are evaluated at the **same point** $\omega$ of one space $\Omega$.
- The definition puts no constraint on $p$. If $p_{K(\omega)}=0$ then $Y(\omega)=0$, because $0^{-1}=0$. Negative $p$ is allowed.

### 12. `singleTermN` (definition)

**Parameters.**
- Types $\Omega,\Omega'$; their σ-algebras are omitted.
- $P$, $K$ and $p$ as in item 11.
- A sequence $\xi=(\xi_n)_{n\in\mathbb N}$ of maps $\xi_n:\Omega'\to\Omega$.
- $N\in\mathbb N$ and a point $x\in\Omega'$.

**Value.**
$$\bar Y_N(x)=(N)^{-1}\sum_{n=0}^{N-1}Y\big(\xi_n(x)\big),\qquad Y(\omega)=\big(p_{K(\omega)}\big)^{-1}\Delta P_{K(\omega)}(\omega),$$
with the conventions $0^{-1}=0$ and $\bar Y_0\equiv0$.

### 13. `geomLevelProb` (definition)

**Parameters.** $\beta,\gamma\in\mathbb R$ and $\ell\in\mathbb N$.

**Value.** Let $r=2^{-(\beta+\gamma)/2}$, a real power, so $r>0$ always. Then
$$g_{\beta,\gamma}(\ell)=(1-r)\,r^{\ell}.$$

**Remarks.**
- If $\beta+\gamma>0$, then $0<r<1$, every $g_{\beta,\gamma}(\ell)>0$, and $\sum_{\ell\ge0}g_{\beta,\gamma}(\ell)=1$. This is a geometric distribution on $\mathbb N$.
- If $\beta+\gamma=0$, then $g\equiv0$.
- If $\beta+\gamma<0$, then every value is negative.
- The definition itself imposes no restriction on $\beta,\gamma$.

### 14. `optimalLevelProb` (definition)

**Parameters.** Sequences $V,C:\mathbb N\to\mathbb R$ and $\ell\in\mathbb N$.

**Value.**
$$q^*_{V,C}(\ell)=\frac{\sqrt{V_\ell/C_\ell}}{\sum'_{k\ge0}\sqrt{V_k/C_k}} .$$

**Remarks.**
- The square root of a negative number is $0$, and $V_\ell/0=0$.
- If $(\sqrt{V_k/C_k})_k$ is not summable, the denominator is the junk value $0$, and then $q^*\equiv0$ because $x/0=0$.
- When all $V_k,C_k>0$ and the series converges, $q^*$ is a strictly positive sequence that sums to $1$.

**Observation.** No statement in packets 7–8 mentions `optimalLevelProb`. In particular, `randomised_optimal_p_isLeast` (item 18) does **not** state that this sequence attains the minimum. It only states that *some* admissible sequence does.

### 15. `integral_cost_level` (theorem)

**Binders, in order.**
1. a type $\Omega$ with a σ-algebra, and a measure $\mu$ on $\Omega$. The measure is **arbitrary**: the section's `[IsProbabilityMeasure μ]` is explicitly omitted, and no finiteness is assumed;
2. $K:\Omega\to\mathbb N$ and $p:\mathbb N\to\mathbb R$ (section variables; the section's `Pl` is not mentioned and not included);
3. (`hK`) $K$ is measurable;
4. a family $\kappa=(\kappa_\ell)_{\ell\in\mathbb N}$ with $\kappa_\ell:\Omega\to\mathbb R$ (implicit);
5. (`hκm`) every $\kappa_\ell$ is Borel measurable;
6. (`hκ0`) $\kappa_\ell(\omega)\ge0$ for every $\ell$ and **every** $\omega$, not just almost every $\omega$;
7. (`hκi`) every $\kappa_\ell$ is $\mu$-integrable;
8. (`hind`) for each $\ell$, $K$ and $\kappa_\ell$ are independent under $\mu$. These are separate pairwise statements, one for each $\ell$;
9. (`hp`) for each $\ell$, $\operatorname{toReal}\,\mu\{K=\ell\}=p_\ell$.

**Conclusion** (a conjunction of two parts).

(a) Integrability of the cost at the random level is equivalent to summability:
$$\Big(\omega\mapsto\kappa_{K(\omega)}(\omega)\ \text{is }\mu\text{-integrable}\Big)\iff\Big(\big(p_\ell\textstyle\int_\Omega\kappa_\ell\,d\mu\big)_{\ell\in\mathbb N}\ \text{is summable}\Big).$$

(b) If $\big(p_\ell\int\kappa_\ell\,d\mu\big)_\ell$ is summable, then
$$\int_\Omega\kappa_{K(\omega)}(\omega)\,\mu(d\omega)=\sum_{\ell=0}^{\infty}p_\ell\int_\Omega\kappa_\ell\,d\mu .$$

**Library notions and edge cases.**
- $p$ is not free: `hp` fixes $p_\ell=\operatorname{toReal}\mu\{K=\ell\}\ge0$.
- Each $\int\kappa_\ell\,d\mu\ge0$, so every term is $\ge0$, and "summable" just means the series of nonnegative terms converges.

**Observations.**
- **No probability measure is assumed.** For each $\ell$, `hind` with $A=B=\Omega$ gives $\mu(\Omega)=\mu(\Omega)^2$, so $\mu(\Omega)\in\{0,1,\infty\}$.
  - If $\mu(\Omega)=1$, this is the probability statement.
  - If $\mu=0$, everything is $0$.
  - If $\mu(\Omega)=\infty$, apply `hind` with one of the two sets equal to $\Omega$. This gives $\mu(E)=\infty\cdot\mu(E)$, so $\mu(E)\in\{0,\infty\}$, for every $E\in\sigma(\kappa_\ell)$ and for every $E=\{K=\ell\}$. Integrability of $\kappa_\ell\ge0$ then forces $\mu\{\kappa_\ell>t\}<\infty$, hence $=0$, for every $t>0$. So $\kappa_\ell=0$ a.e., and $p_\ell=\operatorname{toReal}(0\text{ or }\infty)=0$. Both sides are then $0$, and the statement holds trivially.

  So omitting the probability assumption makes the statement more general, with degenerate extra cases. It does not make it false or vacuous.
- Part (b) is weaker than necessary. By part (a) and the junk-value conventions (a non-integrable integrand has integral $0$, and a non-summable series has $\sum'=0$), the equation also holds without the summability premise.
- Independence is only pairwise between $K$ and each $\kappa_\ell$. Joint independence of $K$ from the whole family is not assumed.
- The hypotheses can be satisfied, for example on a product space where $K$ is a coordinate independent of all $\kappa_\ell$. The statement is not vacuous.

### 16. `randomised_necessary` (theorem)

**Binders, in order.**
1. a type $\Omega$ with a σ-algebra and a measure $\mu$; **instance: $\mu$ is a probability measure** (from the section, not omitted);
2. $K:\Omega\to\mathbb N$, a sequence $P=(P_\ell)$ with $P_\ell:\Omega\to\mathbb R$, and $p:\mathbb N\to\mathbb R$ (section variables, implicit);
3. (`hK`) $K$ is measurable;
4. (`hPlm`) every $P_\ell$ is Borel measurable;
5. (`hPl`) every $P_\ell$ is in $L^2(\mu)$;
6. (`hp`) $\mu\{K=\ell\}=p_\ell$ for every $\ell$, as real numbers;
7. (`hp0`) $p_\ell>0$ for **every** $\ell\in\mathbb N$;
8. (`hind`) for each $\ell$, $K$ and $\Delta P_\ell$ are independent under $\mu$;
9. a family $\kappa=(\kappa_\ell)$ with $\kappa_\ell:\Omega\to\mathbb R$, and a sequence $C:\mathbb N\to\mathbb R$ (both implicit);
10. (`hκm`) every $\kappa_\ell$ is measurable;
11. (`hκ0`) $\kappa_\ell\ge0$ everywhere;
12. (`hκi`) every $\kappa_\ell$ is $\mu$-integrable;
13. (`hκind`) for each $\ell$, $K$ is independent of $\kappa_\ell$;
14. (`hC`) $\int_\Omega\kappa_\ell\,d\mu=C_\ell$ for every $\ell$;
15. (`hY`) $Y\in L^2(\mu)$, where $Y(\omega)=\Delta P_{K(\omega)}(\omega)/p_{K(\omega)}$ (`singleTerm`; no division by $0$ occurs since $p>0$);
16. (`hcost`) $\omega\mapsto\kappa_{K(\omega)}(\omega)$ is $\mu$-integrable.

**Definition used.** $\Delta P_0=P_0$ and $\Delta P_\ell=P_\ell-P_{\ell-1}$ for $\ell\ge 1$.

**Conclusion** (a conjunction).
$$\Big(\frac{\operatorname{Var}_\mu(\Delta P_\ell)}{p_\ell}\Big)_{\ell\in\mathbb N}\ \text{is summable}\qquad\text{and}\qquad\big(p_\ell\,C_\ell\big)_{\ell\in\mathbb N}\ \text{is summable}.$$

**Library notions and edge cases.**
- Both sequences are nonnegative, because variance is $\ge0$, $p>0$ and $C_\ell=\int\kappa_\ell\ge0$. So "summable" means the ordinary series converges.
- $\operatorname{Var}_\mu$ is Mathlib's variance. Here $\Delta P_\ell\in L^2(\mu)$ on a probability space, so it is the genuine variance.
- By `hp` and `hp0`, $K$ takes every value in $\mathbb N$ with positive probability. $\sum_\ell p_\ell=1$ holds automatically, since the events $\{K=\ell\}$ partition $\Omega$.

**Observations.**
- The first conjunct is about **variances** $\operatorname{Var}(\Delta P_\ell)$, not second moments $\int(\Delta P_\ell)^2$. It is weaker than summability of $\int(\Delta P_\ell)^2\,d\mu/p_\ell$.
- Independence of $K$ from $\Delta P_\ell$ and from $\kappa_\ell$ is assumed separately for each $\ell$, pairwise only.
- $C$ is not free: `hC` fixes it as the sequence of mean costs.
- The hypotheses can be satisfied, for example with $P_\ell\equiv0$, $\kappa\equiv0$, and $K$ geometrically distributed on a product space. The statement is not vacuous.

### 17. `singleTermN_mean_variance` (theorem)

**Binders, in order.**
1. a type $\Omega$ with a σ-algebra and a measure $\mu$; a type $\Omega'$ with a σ-algebra and a measure $\mu'$;
2. **instances: $\mu$ and $\mu'$ are both probability measures** (written explicitly);
3. $K:\Omega\to\mathbb N$, a sequence $P=(P_\ell)$ with $P_\ell:\Omega\to\mathbb R$, and $p:\mathbb N\to\mathbb R$ (implicit);
4. a function $P:\Omega\to\mathbb R$ (explicit), with (`hP`) $P$ $\mu$-integrable;
5. (`hK`) $K$ is measurable;
6. (`hPlm`) every $P_\ell$ is measurable;
7. (`hPl`) every $P_\ell$ is in $L^2(\mu)$;
8. (`hp`) $\mu\{K=\ell\}=p_\ell$ for every $\ell$, as reals;
9. (`hp0`) $p_\ell>0$ for every $\ell$;
10. (`hind`) for each $\ell$, $K$ and $\Delta P_\ell$ are independent under $\mu$;
11. (`hsum2`) the sequence $\Big(\dfrac{\int_\Omega(\Delta P_\ell)^2\,d\mu}{p_\ell}\Big)_{\ell\in\mathbb N}$ is summable;
12. (`hconv`) $\int_\Omega P_L\,d\mu\to\int_\Omega P\,d\mu$ as $L\to\infty$;
13. a sequence $\xi=(\xi_n)_{n\in\mathbb N}$ with $\xi_n:\Omega'\to\Omega$ (implicit);
14. (`hξ`) every $\xi_n$ is measure preserving from $(\Omega',\mu')$ to $(\Omega,\mu)$;
15. (`hξind`) the maps $(\xi_n)_{n\in\mathbb N}$ are mutually independent under $\mu'$;
16. $N\in\mathbb N$ (implicit) with (`hN`) $0<N$.

**Definitions used.**
- $\Delta P_0=P_0$ and $\Delta P_\ell=P_\ell-P_{\ell-1}$ for $\ell\ge 1$.
- $Y(\omega)=\Delta P_{K(\omega)}(\omega)/p_{K(\omega)}$ (`singleTerm`).
- $\bar Y_N(x)=N^{-1}\sum_{n=0}^{N-1}Y(\xi_n(x))$ (`singleTermN`).

**Conclusion** (a conjunction).
$$\int_{\Omega'}\bar Y_N\,d\mu'=\int_\Omega P\,d\mu\qquad\text{and}\qquad\operatorname{Var}_{\mu'}\big(\bar Y_N\big)=\frac{\operatorname{Var}_\mu(Y)}{N}.$$

**Library notions and edge cases.**
- The integrals are Bochner integrals and the variances are Mathlib's; both are $0$ in degenerate cases.
- My own derivation: `hind`, `hp` and `hp0` give $\int Y^2\,d\mu=\sum_\ell\int(\Delta P_\ell)^2\,d\mu/p_\ell$, which `hsum2` makes finite. So $Y\in L^2(\mu)$, $\bar Y_N\in L^2(\mu')$, and every integral and variance in the conclusion is genuine, not a junk $0$.
- The squared term is $(\Delta P_\ell(\omega))^2$, and its integral is genuine because $\Delta P_\ell\in L^2(\mu)$.
- `hN` excludes $N=0$, where the left mean would be $0$. At $N=0$ the variance equation would read $0=0$.

**Observations.**
- The target $P$ is tied to $(P_\ell)$ only through `hconv`, which says the means converge. In the conclusion $P$ appears only through its mean $\int P\,d\mu$.
- The theorem gives no formula for $\operatorname{Var}_\mu(Y)$. It only gives the $1/N$ scaling.
- `hξ` and `hξind` say that $(\xi_n)$ is i.i.d. with law $\mu$. Such families exist, for example as coordinates of an infinite product.
- The hypotheses can be satisfied, and the statement is not vacuous.

### 18. `randomised_optimal_p_isLeast` (theorem)

**Binders, in order.** No measure, space or random variable appears; the section variables are not mentioned and not included.
1. sequences $V,C:\mathbb N\to\mathbb R$ (implicit);
2. (`hV`) $V_\ell>0$ for every $\ell$;
3. (`hC`) $C_\ell>0$ for every $\ell$;
4. (`hS`) $\big(\sqrt{V_\ell C_\ell}\big)_\ell$ is summable;
5. (`hZ`) $\big(\sqrt{V_\ell/C_\ell}\big)_\ell$ is summable.

**The set.** Let $\mathcal A$ be the set of all $p:\mathbb N\to\mathbb R$ such that
- $p_\ell>0$ for every $\ell$;
- `HasSum p 1`, i.e. $\sum_\ell p_\ell=1$;
- $(V_\ell/p_\ell)_\ell$ is summable;
- $(p_\ell C_\ell)_\ell$ is summable.

Then define
$$S=\Big\{\Big(\sum_{\ell}\frac{V_\ell}{p_\ell}\Big)\Big(\sum_\ell p_\ell C_\ell\Big)\ :\ p\in\mathcal A\Big\}\subseteq\mathbb R .$$

**Conclusion.** `IsLeast S` $\big(\sum_\ell\sqrt{V_\ell C_\ell}\big)^2$. Explicitly:
1. (attainment) there exists $p\in\mathcal A$ with $\Big(\sum_\ell V_\ell/p_\ell\Big)\Big(\sum_\ell p_\ell C_\ell\Big)=\Big(\sum_\ell\sqrt{V_\ell C_\ell}\Big)^2$;
2. (lower bound) for every $p\in\mathcal A$, $\Big(\sum_\ell\sqrt{V_\ell C_\ell}\Big)^2\le\Big(\sum_\ell V_\ell/p_\ell\Big)\Big(\sum_\ell p_\ell C_\ell\Big)$.

**Library notions and edge cases.**
- All sums are unconditional sums of positive terms and are genuine, because summability is either a hypothesis or part of membership in $\mathcal A$. So the junk value $\sum'=0$ never enters $S$.
- If one of the two series diverges for some $p$, that $p$ is not in $\mathcal A$, and the theorem says nothing about it.

**Observations.**
- The minimising $p$ is not named, and `optimalLevelProb` does not appear.
- $V$ and $C$ are arbitrary positive sequences. The statement has no probabilistic content and does not tie them to variances or costs.
- The objective $\big(\sum V/p\big)\big(\sum pC\big)$ is unchanged when $p$ is multiplied by a constant, so the normalisation $\sum p=1$ does not change which values occur.
- The hypotheses can be satisfied, for example with $V_\ell=4^{-\ell}$ and $C_\ell=1$. The statement is not vacuous.

### 19. `randomised_mlmc_finite` (theorem)

**Binders, in order.**
1. a type $\Omega$ with a σ-algebra and a measure $\mu$; **instance: $\mu$ is a probability measure** (written explicitly);
2. $K:\Omega\to\mathbb N$ and a sequence $P=(P_\ell)$ with $P_\ell:\Omega\to\mathbb R$ (implicit); a function $P:\Omega\to\mathbb R$ (explicit); a family $\kappa=(\kappa_\ell)$ with $\kappa_\ell:\Omega\to\mathbb R$ (implicit); real numbers $\alpha,\beta,\gamma,c_1,c_2,c_3$ (implicit);
3. (`hα`) $0<\alpha$;
4. (`hγ`) $0<\gamma$;
5. (`hγβ`) $\gamma<\beta$;
6. (`hK`) $K$ is measurable;
7. (`hPlm`) every $P_\ell$ is measurable;
8. (`hPl`) every $P_\ell$ is in $L^2(\mu)$;
9. (`hP`) $P$ is $\mu$-integrable;
10. (`hp`) for every $\ell$, $\mu\{K=\ell\}=g_{\beta,\gamma}(\ell)=(1-r)\,r^\ell$ with $r=2^{-(\beta+\gamma)/2}$ (`geomLevelProb`);
11. (`hind`) for each $\ell$, $K$ and $\Delta P_\ell$ are independent under $\mu$;
12. (`h_i`) for every $\ell\in\mathbb N$, $\Big|\int_\Omega(P_\ell-P)\,d\mu\Big|\le c_1\,2^{-\alpha\ell}$;
13. (`h_iii`) for every $\ell$, $\int_\Omega(\Delta P_\ell)^2\,d\mu\le c_2\,2^{-\beta\ell}$;
14. (`hκm`) every $\kappa_\ell$ is measurable;
15. (`hκ0`) $\kappa_\ell\ge0$ everywhere;
16. (`hκi`) every $\kappa_\ell$ is $\mu$-integrable;
17. (`hκind`) for each $\ell$, $K$ is independent of $\kappa_\ell$;
18. (`h_iv`) for every $\ell$, $\int_\Omega\kappa_\ell\,d\mu\le c_3\,2^{\gamma\ell}$.

**Definitions used.**
- $\Delta P_0=P_0$ and $\Delta P_\ell=P_\ell-P_{\ell-1}$ for $\ell\ge 1$.
- $Y(\omega)=\big(g_{\beta,\gamma}(K(\omega))\big)^{-1}\,\Delta P_{K(\omega)}(\omega)$ (`singleTerm` with $p=g_{\beta,\gamma}$).
- $g_{\beta,\gamma}(\ell)=(1-2^{-(\beta+\gamma)/2})\,(2^{-(\beta+\gamma)/2})^\ell$.

**Conclusion** (a conjunction of five statements).
1. $Y$ is $\mu$-integrable;
2. $\int_\Omega Y\,d\mu=\int_\Omega P\,d\mu$;
3. $Y\in L^2(\mu)$;
4. $\omega\mapsto\kappa_{K(\omega)}(\omega)$ is $\mu$-integrable;
5. $\displaystyle\int_\Omega\kappa_{K(\omega)}(\omega)\,\mu(d\omega)=\sum_{\ell\ge0}{}'\ g_{\beta,\gamma}(\ell)\int_\Omega\kappa_\ell\,d\mu$.

**Library notions and edge cases.**
- $\beta>\gamma>0$ gives $\beta+\gamma>0$, hence $0<r<1$. So $g_{\beta,\gamma}(\ell)>0$ for all $\ell$ and $\sum_\ell g_{\beta,\gamma}(\ell)=1$, which is consistent with `hp` on a probability space. No division by $0$ occurs in $Y$.
- The powers $2^{-\alpha\ell}$, $2^{-\beta\ell}$, $2^{\gamma\ell}$ are real powers with the exponent cast to $\mathbb R$.
- The constants $c_1,c_2,c_3$ have no sign hypotheses. The hypotheses still force them to be $\ge0$, because the left-hand sides are $\ge0$ and the powers of $2$ are $>0$.
- In conjunct 5 the series converges; its terms are at most $c_3(1-r)\,2^{-(\beta-\gamma)\ell/2}$. So $\sum'$ is the genuine sum.

**Observations.**
- `h_i` bounds the bias of the means. `h_iii` bounds the **second moment**, not the variance, of $\Delta P_\ell$. `h_iv` bounds the mean cost.
- $\alpha$ only has to be positive; no relation between $\alpha$ and $\beta,\gamma$ is required. $\alpha$ and $c_1$ matter only for conjunct 2.
- The conclusion is **qualitative**. It asserts finiteness (integrability and $L^2$) and two exact identities. It gives no explicit numerical bound on $\int Y^2$, $\operatorname{Var}(Y)$ or the expected cost, and no statement about $N$-sample averages or an accuracy/cost trade-off.
- Conjunct 1 follows from conjunct 3 on a probability space, so it is redundant.
- The hypotheses can be satisfied, for example with all $P_\ell=P=0$, $\kappa\equiv0$, $c_i=0$, and $K$ with law $g_{\beta,\gamma}$ on a product space. The statement is not vacuous.
