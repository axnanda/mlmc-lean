# Blind read-back audit — packet E (`g_applications`)

- **Date:** 2026-09-27
- **Packet:** `packet_E_g_applications.lean`
- **Number of declarations audited:** **98** = 67 theorems/lemmas + 31 definitions (29 `def` + 2 `abbrev`). Of the 31 definitions, 9 come from the trailing section "definitions used above, from other modules" (`optimalN`, `levelDiff`, `complexityBound`, `totalCost`, `blockMean`, `mimcEta`, `mimcBound`, `lagrangeN`, `sumSqrtVC`).
- **Rules followed:**
  - I read only the packet, `references/mission_auditor.md`, and Mathlib sources under `.lake/packages/mathlib/Mathlib`, and only to confirm the definitions and conventions listed below. I needed no core Lean sources. I opened no project Lean sources, `docs/`, `notes/`, README, PLAN, `prove2me/`, scripts, git history, papers or web pages. I did not open the other packets that sit in the `round5` folder.
  - The audit is blind: I inferred no meaning from declaration or file names. Each **Rendering** translates the code literally (mission_auditor principles 1–6). It names every binder, hypothesis and typeclass assumption, unfolds every project definition, and keeps the exact strength of every relation. Renderings contain no judgement (principle 7). The judgements the task asks for are kept apart, under **Truth / Non-vacuity / Junk values / Concerns**.
  - This is a Markdown file, not a JSON payload, so LaTeX uses single backslashes.
  - Numerical sanity checks are pure Python (exact `Fraction` arithmetic where possible, otherwise truncated exact sums or Monte Carlo). They live in `work_E_g_applications/`: `check_pde.py`, `check_poisson.py`, `check_nested.py`, `check_markov.py`. All checks pass.

---

## Conventions (confirmed in the Mathlib sources)

| # | Convention | Where confirmed |
|---|---|---|
| C1 | The Bochner integral $\int f\,d\mu$ is **0 when $f$ is not $\mu$-integrable** (`integral_undef`). Notation `∫ x, body ∂μ` parses `body` at precedence 60, so the body includes `+` and `-`. | `MeasureTheory/Integral/Bochner/Basic.lean:166,202` |
| C2 | `μ[X]` is a macro for `∫ x, X x ∂μ` (a Bochner integral). | `Probability/Notation.lean:53` |
| C3 | `∫⁻` (lower Lebesgue integral) takes values in $[0,\infty]$, so it has no junk. | `MeasureTheory/Integral/Lebesgue/Basic.lean:56` |
| C4 | `Integrable f μ` := `AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ`. `MemLp f p μ` := `AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞`. | `Function/L1Space/Integrable.lean:59`, `Function/LpSeminorm/Defs.lean:118` |
| C5 | `variance X μ := (evariance X μ).toReal`, where `evariance X μ := ∫⁻ ω, ‖X ω − μ[X]‖ₑ^2 ∂μ`. For an a.e.-strongly-measurable $X\notin L^2$ on a finite measure, `evariance = ∞` (`evariance_eq_top`), and therefore **variance $=0$**, because `ENNReal.toReal ∞ = 0` (`toReal_top`). `variance_le_expectation_sq`: $\operatorname{Var}\le\mu[X^2]$ for a.e.-strongly-measurable $X$ under a probability measure. | `Probability/Moments/Variance.lean:58,64,110,339`; `Data/ENNReal/Basic.lean:283` |
| C6 | `ENNReal.ofReal t = 0 ↔ t ≤ 0`, i.e. $\mathrm{ofReal}(t)=\max(t,0)$. | `Data/ENNReal/Real.lean:181` |
| C7 | Real power $x^y$ (`Real.rpow`) is the real part of the complex power. For $x>0$ it is $e^{y\log x}$. **$0^0=1$, and $0^y=0$ for $y\ne0$.** For $x<0$ it is $e^{y\log\lvert x\rvert}\cos(\pi y)$. `mul_rpow`: $(xy)^z=x^zy^z$ for $x,y\ge0$. A natural-number exponent `x ^ (n:ℕ)` is the ordinary monoid power ($0^0=1$), and an integer exponent is `zpow`. | `Analysis/SpecialFunctions/Pow/Real.lean:35–128,478` |
| C8 | $\log 0=0$ and $\log(-x)=\log x$. | `Analysis/SpecialFunctions/Log/Basic.lean:103,121` |
| C9 | $\sqrt{x}=0$ for $x\le0$. | `Analysis/Real/Sqrt.lean:142` |
| C10 | $\lceil x\rceil_{+}$ (`Nat.ceil`) $=0 \iff x\le0$. | `Algebra/Order/Floor/Semiring.lean:187` |
| C11 | $0^{-1}=0$ (`inv_zero`), hence $x/0=0$. | `Algebra/GroupWithZero/Defs.lean:236` |
| C12 | `deriv f x = 0` if $f$ is not differentiable at $x$. `HasDerivAt f f' x` is the usual derivative. | `Analysis/Calculus/Deriv/Basic.lean:130,153,250` |
| C13 | `Measure.map f μ = 0` unless $f$ is $\mu$-a.e.-measurable. `Measure.bind m κ := join (map κ m)`. `Measure.prod μ ν := bind μ (x ↦ map (Prod.mk x) ν)`. | `Measure/Map.lean:91`, `Measure/GiryMonad.lean:125,228`, `Measure/Prod.lean:171` |
| C14 | `Measure.infinitePi μ` is the product measure **if every factor is a probability measure, and the zero measure otherwise** (defined with an `if`). | `Probability/ProductMeasure.lean:358` |
| C15 | `poissonMeasure r := Σₙ ofReal(e^{−r} r^n / n!) • δₙ` on ℕ, for $r\in[0,\infty)$. It is a probability measure (instance). Because $r^0=1$ is a monoid power, `poissonMeasure 0 = δ₀`. Mathlib already has `IndepFun.hasLaw_add_poissonMeasure`. | `Probability/Distributions/Poisson/Basic.lean:41,68,191` |
| C16 | `HasLaw X λ P` := (`AEMeasurable X P`) ∧ (`P.map X = λ`). | `Probability/HasLaw.lean:39` |
| C17 | `IndepFun f g μ` / `iIndepFun f μ` mean independence of the σ-algebras $f^{-1}(\mathcal B)$: the product formula holds for every finite subfamily. | `Probability/Independence/Basic.lean:136,144` |
| C18 | `MeasurePreserving f μa μb` := `Measurable f ∧ map f μa = μb`. | `Dynamics/Ergodic/MeasurePreserving.lean:45` |
| C19 | `Measurable[m] f` means measurability with the σ-algebra $m$ on the domain. | `MeasureTheory/MeasurableSpace/Defs.lean:505` |
| C20 | `ConvexOn 𝕜 s f` := $s$ is convex and $f(ax+by)\le af(x)+bf(y)$ for $x,y\in s$, $a,b\ge0$, $a+b=1$. | `Analysis/Convex/Function.lean:54` |
| C21 | ℕ carries the σ-algebra ⊤. A countable type with measurable singletons (e.g. ℕ×ℕ) is a discrete measurable space, so **every function out of ℕ or ℕ×ℕ is measurable**, and `map`/`bind` over them has no junk. | `MeasurableSpace/Instances.lean:30`, `MeasurableSpace/Defs.lean:551` |
| C22 | Subtraction on ℝ≥0 is truncated: $r-p=\max(r-p,0)$. | `Data/NNReal/Defs.lean:745–748` |
| C23 | `Finset.sup' s H f` is the maximum of $f$ over a nonempty finset. `Finset.univ_nonempty` needs `[Nonempty α]`. | `Data/Finset/Lattice/Fold.lean:519`, `Data/Finset/BooleanAlgebra.lean:52` |
| C24 | **Parsing:** in `∑ x ∈ s, body`, `body` is parsed at precedence 67, so `∑ ℓ ∈ S, a ℓ - b` means $(\sum_\ell a_\ell)-b$ and the sum stops before `≤`, `=`, `<`. | `Algebra/BigOperators/Group/Finset/Defs.lean:181` |
| C25 | Decimal literals in a division ring are exact rationals (`Rat.cast_ofScientific`): `(1.5:ℝ) = 3/2` and `(-2.5:ℝ) = -5/2`. | `Data/Rat/Cast/Lemmas.lean:59` |

### Notation used below

- $\mathbb N=\{0,1,2,\dots\}$. $\mathbb R_{\ge0}=[0,\infty)$ (Mathlib ℝ≥0). $[0,\infty]$ is the extended half-line.
- $\mathbb E_\mu[X]$ or $\int X\,d\mu$: the **Bochner** integral (C1).
- $\int^{-}F\,d\mu\in[0,\infty]$: the lower Lebesgue integral.
- $t^{+}:=\mathrm{ofReal}(t)=\max(t,0)$, as an element of $[0,\infty]$.
- $\operatorname{Var}_\mu(X)$: Mathlib's `variance` (C5).
- $f_\#m$: push-forward (C13). $\delta_x$: Dirac mass. $\mathrm{Po}(r)$: `poissonMeasure r` (C15).
- "$X$ has law $\lambda$ under $\mu$" is `HasLaw` (C16).
- $\operatorname{bind}(m,\kappa)$ is the mixture $B\mapsto\int\kappa(x)(B)\,m(dx)$. On countable discrete spaces this equals $\sum_x m\{x\}\,\kappa(x)(B)$.
- $\rho^{\otimes\mathbb N}$ and $\lambda^{\otimes(\mathbb N\times\mathbb N)}$: `Measure.infinitePi` (C14).
- $d$ is the (pseudo)distance. $d^p$ with real $p$ is a real power (C7).

---

## Block 1 — `MlmcLean.PDEExamples` (13 declarations)

Ambient context of the `rates` section: $\Omega$ is an arbitrary type with a σ-algebra $\mathcal F$, and $\mu$ is a **probability** measure on $(\Omega,\mathcal F)$.

### 1. `rates_of_pathwise` (theorem)

**Rendering.** Let $P:\Omega\to\mathbb R$ be any function; **no measurability or integrability is assumed.** Let $(P_\ell)_{\ell\in\mathbb N}$ be functions $\Omega\to\mathbb R$, and let $K,p\in\mathbb R$ be arbitrary. Assume:
- **(hPl)** every $P_\ell$ is $\mu$-integrable;
- **(herr)** for **every** $\ell\in\mathbb N$ and **every** $\omega\in\Omega$ (surely, not almost surely): $\lvert P(\omega)-P_\ell(\omega)\rvert\le K\,2^{-p\ell}$.

Then both of the following hold:
$$\text{(1)}\ \ \forall\ell\in\mathbb N:\ \Big\lvert\int_\Omega\big(P_\ell-P\big)\,d\mu\Big\rvert\le K\,2^{-p\ell},\qquad \text{(2)}\ \ \forall\ell\in\mathbb N:\ \operatorname{Var}_\mu\big(P_{\ell+1}-P_\ell\big)\le(1+2^{p})^2K^2\,2^{-2p(\ell+1)}.$$
All powers of 2 are real powers with base 2.

**Truth.** True.
- $K\ge0$ is forced: take $\ell=0$ and any $\omega$ ($\Omega\neq\emptyset$ because $\mu$ is a probability measure).
- (1): If $P$ is a.e.-strongly measurable, then $P_\ell-P$ is measurable and bounded by $K2^{-p\ell}$, so $\lvert\int\rvert\le\int\lvert\cdot\rvert\le K2^{-p\ell}$. Otherwise the integrand is not integrable and the integral is $0\le K2^{-p\ell}$.
- (2): Pointwise, $\lvert P_{\ell+1}-P_\ell\rvert\le K2^{-p(\ell+1)}+K2^{-p\ell}=(1+2^p)K2^{-p(\ell+1)}$. So $\operatorname{Var}\le\mathbb E[(P_{\ell+1}-P_\ell)^2]\le$ the stated bound.
- The constant is sharp: the two-point example in `check_pde.py` gives ratio exactly 1.

**Non-vacuity.** Any $\Omega$ with $P\equiv P_\ell\equiv0$ and $K=0$. Less trivially, $P$ bounded measurable and $P_\ell=P+K2^{-p\ell}$.

**Junk values.** Conclusion (1) uses the Bochner integral. When $P$ is not measurable, (1) holds only because the non-integrable integral is set to $0$. (2) has no junk: $P_{\ell+1}-P_\ell$ is integrable and bounded, hence in $L^2$, so the variance is the genuine one. The powers have base $2>0$, so no rpow junk.

**Concerns.** Minor: $P$ has no measurability hypothesis, so (1) carries content only for measurable $P$. The error hypothesis is a sure, uniform-in-$\omega$ bound, which is stronger than an a.s. or $L^q$ bound. $p$ may be $\le0$, in which case the bounds do not decay. None of this makes the statement false or vacuous.

### 2. `elliptic_rates` (theorem)

**Rendering.** Same ambient context ($\mu$ a probability measure on $\Omega$). $P:\Omega\to\mathbb R$ is arbitrary (no measurability). $P_\ell:\Omega\to\mathbb R$ ($\ell\in\mathbb N$) are each $\mu$-integrable, and $K\in\mathbb R$. Assume that for every $\ell\in\mathbb N$ and every $\omega$:
$$\lvert P(\omega)-P_\ell(\omega)\rvert\le K\big(2^{-(\ell+1)}\big)^2 .$$
Then:
$$\forall\ell:\ \Big\lvert\int(P_\ell-P)\,d\mu\Big\rvert\le\tfrac K4\,2^{-2\ell}\qquad\text{and}\qquad\forall\ell:\ \operatorname{Var}_\mu(P_{\ell+1}-P_\ell)\le\tfrac{25}{16}K^2\,2^{-4(\ell+1)}.$$

**Truth.** True.
- $K(2^{-(\ell+1)})^2=\tfrac K4 2^{-2\ell}$.
- $\lvert P_{\ell+1}-P_\ell\rvert\le K4^{-(\ell+2)}+K4^{-(\ell+1)}=\tfrac54K\,4^{-(\ell+1)}$; squaring gives $\tfrac{25}{16}K^2 2^{-4(\ell+1)}$.
- This is the case $p=2$, $K\mapsto K/4$ of #1. The constant is sharp (checked).

**Non-vacuity.** As in #1.

**Junk values.** As in #1: the bias part is trivially satisfied, via the 0-integral convention, when $P$ is non-measurable.

**Concerns.** Same minor points as #1.

### 3. `heatStep` (def)

**Rendering.** For $\lambda\in\mathbb R$, $u:\mathbb Z\to\mathbb R$ and $j\in\mathbb Z$:
$$\mathrm{heatStep}_\lambda(u)_j=u_j+\lambda\,(u_{j+1}-2u_j+u_{j-1})=(1-2\lambda)u_j+\lambda u_{j+1}+\lambda u_{j-1}.$$

**Truth / Non-vacuity.** Not applicable (definition).
**Junk values.** None.
**Concerns.** None. The update acts on the whole lattice $\mathbb Z$ (no boundary), and $\lambda$ is any real.

### 4. `abs_heatStep_le` (theorem)

**Rendering.** For real $\lambda,M$ with $0\le\lambda\le\tfrac12$, every $u:\mathbb Z\to\mathbb R$ with $\lvert u_i\rvert\le M$ for all $i\in\mathbb Z$, and every $j\in\mathbb Z$: $\ \lvert\mathrm{heatStep}_\lambda(u)_j\rvert\le M$.

**Truth.** True: the update is a convex combination with weights $1-2\lambda,\lambda,\lambda\ge0$. 2000 random tests pass.
**Non-vacuity.** $\lambda=\tfrac14$, $u\equiv0$, $M=0$. (The hypothesis forces $M\ge0$.)
**Junk values.** None.
**Concerns.** None.

### 5. `heatStep_sub` (theorem)

**Rendering.** For all $\lambda\in\mathbb R$, $u,v,w:\mathbb Z\to\mathbb R$ and $j\in\mathbb Z$:
$$\big(\mathrm{heatStep}_\lambda(u)_j+w_j\big)-\big(\mathrm{heatStep}_\lambda(v)_j+w_j\big)=\mathrm{heatStep}_\lambda(u-v)_j ,$$
where $u-v$ is the pointwise difference.

**Truth.** True: $w_j$ cancels, and the update is linear in $u$.
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** $w$ cancels identically, so the statement is only linearity of the update.

### 6. `heatStep_alternating` (theorem)

**Rendering.** For all $\lambda\in\mathbb R$ and $j\in\mathbb Z$: $\ \mathrm{heatStep}_\lambda\big(i\mapsto(-1)^i\big)_j=(1-4\lambda)(-1)^j$. Here $(-1)^i$ is an integer power.

**Truth.** True (exact check).
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 7. `one_lt_abs_one_sub_four_mul` (lemma)

**Rendering.** For every real $\lambda>\tfrac12$: $\ 1<\lvert1-4\lambda\rvert$.

**Truth.** True, since $1-4\lambda<-1$.
**Non-vacuity.** $\lambda=1$.
**Junk values.** None.
**Concerns.** None. Combined with #6, it gives amplification by a factor $>1$ per step of the mode $(-1)^j$ when $\lambda>\tfrac12$; the lemma itself states only the scalar inequality.

### 8. `parabolic_ratio` (theorem)

**Rendering.** For every $\ell\in\mathbb N$, with $h_\ell:=2^{-(\ell+1)}$ (a real power): $\ \dfrac{h_\ell^2/4}{h_\ell^2}=\dfrac14$.

**Truth.** True, since $h_\ell>0$.
**Non-vacuity.** No hypotheses.
**Junk values.** None (no division by zero).
**Concerns.** A pure arithmetic identity.

### 9. `parabolic_cost` (theorem)

**Rendering.** For every $T\in\mathbb R$ and $\ell\in\mathbb N$, with $h_\ell=2^{-(\ell+1)}$:
$$h_\ell^{-1}\cdot\frac{T}{h_\ell^2/4}=32\,T\,2^{3\ell}\qquad(2^{3\ell}\text{ a real power}).$$

**Truth.** True: $4T/h_\ell^3=4T\,2^{3\ell+3}$. Checked exactly for $\ell\le11$.
**Non-vacuity.** No hypotheses.
**Junk values.** None ($h_\ell\ne0$).
**Concerns.** A pure arithmetic identity. $T$ may be any real.

### 10. `emStep` (def)

**Rendering.** For $a,b:\mathbb R\to\mathbb R$ and $h,S,\Delta W\in\mathbb R$: $\ \mathrm{emStep}(a,b,h,S,\Delta W)=S+a(S)\,h+b(S)\,\Delta W$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 11. `milsteinStep` (def)

**Rendering.** $\mathrm{milsteinStep}(a,b,h,S,\Delta W)=S+a(S)h+b(S)\Delta W+\tfrac12\,b(S)\,b'(S)\,(\Delta W^2-h)$. Here $b'(S)$ is Mathlib's `deriv b S`: the derivative of $b$ at $S$ if $b$ is differentiable there, **and $0$ otherwise**.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** Yes: where $b$ is not differentiable, the correction term is silently $0$ (C12).
**Concerns.** None beyond the `deriv` convention.

### 12. `milsteinStep_eq_emStep` (theorem)

**Rendering.** For all $a:\mathbb R\to\mathbb R$ and $\sigma,h,S,\Delta W\in\mathbb R$, with $b\equiv\sigma$ constant:
$$\mathrm{milsteinStep}(a,\,b\equiv\sigma,\,h,S,\Delta W)=\mathrm{emStep}(a,\,b\equiv\sigma,\,h,S,\Delta W).$$

**Truth.** True: the derivative of a constant is $0$.
**Non-vacuity.** No hypotheses.
**Junk values.** None (the constant function is differentiable).
**Concerns.** Covers only a constant $b$; pure algebra.

### 13. `pde_complexity` (theorem)

**Rendering.** For every $\varepsilon\in\mathbb R$: $\ \mathrm{complexityBound}(2,4,1,\varepsilon)=\varepsilon^{-2}$ **and** $\mathrm{complexityBound}(2,4,3,\varepsilon)=\varepsilon^{-2}$. Here (see #92)
$$\mathrm{complexityBound}(\alpha,\beta,\gamma,\varepsilon)=\begin{cases}\varepsilon^{-2}&\gamma<\beta\\ \varepsilon^{-2}(\log\varepsilon)^2&\beta=\gamma\text{ (and not }\gamma<\beta)\\ \varepsilon^{-2-(\gamma-\beta)/\alpha}&\text{otherwise}\end{cases}$$
and $\varepsilon^{-2}$ is a real power.

**Truth.** True: $\gamma=1<4$ and $\gamma=3<4$, so the first branch applies both times.
**Non-vacuity.** No hypotheses.
**Junk values.** The statement quantifies over all real $\varepsilon$. At $\varepsilon=0$, $\varepsilon^{-2}=0$ (rpow junk; mathematically $\infty$). Both sides are the same expression, so the identity holds regardless.
**Concerns.** **Weaker than it may look:** the conclusion only evaluates a case-defined formula at fixed parameters. It says nothing about any estimator, error or cost.

---

## Block 2 — `MlmcLean.PoissonCoupling` (21 declarations)

(The empty `section Discrete` declares variables only; it contains no declaration.)

### 14. `poisson_add_hasLaw` (theorem)

**Rendering.** $\Omega$ is a type with a σ-algebra, and $\mu$ is **any** measure on it (not assumed finite). Let $t_1,t_2\in\mathbb R_{\ge0}$ and $X,Y:\Omega\to\mathbb N$. Assume:
- $X$ and $Y$ are independent under $\mu$;
- $X$ has law $\mathrm{Po}(t_1)$ under $\mu$ ($X$ is $\mu$-a.e.-measurable and $X_\#\mu=\mathrm{Po}(t_1)$);
- $Y$ has law $\mathrm{Po}(t_2)$.

Then the pointwise sum $X+Y$ is $\mu$-a.e.-measurable and $(X+Y)_\#\mu=\mathrm{Po}(t_1+t_2)$.

**Truth.** True. This is Mathlib's `IndepFun.hasLaw_add_poissonMeasure` verbatim.
**Non-vacuity.** Take $\Omega=\mathbb N^2$ with $\mathrm{Po}(t_1)\otimes\mathrm{Po}(t_2)$ and the coordinate maps. The hypotheses force $\mu(\Omega)=1$.
**Junk values.** $\mathrm{Po}(0)=\delta_0$ ($0^0=1$), which is the natural convention.
**Concerns.** None (it duplicates an existing Mathlib lemma).

### 15. `integral_poissonMeasure_id` (theorem)

**Rendering.** For every $r\in\mathbb R_{\ge0}$: $\ \int_{\mathbb N}n\;\mathrm{Po}(r)(dn)=r$ (Bochner integral; $n$ is cast to $\mathbb R$).

**Truth.** True (Poisson mean; the integrand is integrable). Checked.
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 16. `integral_sq_poissonMeasure` (theorem)

**Rendering.** For every $r\in\mathbb R_{\ge0}$: $\ \int n^2\,\mathrm{Po}(r)(dn)=r+r^2$.

**Truth.** True (checked).
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 17. `couplePair` (def)

**Rendering.** For $a,b\in\mathbb R_{\ge0}$ and $(p_1,p_2)\in\mathbb N^2$:
$$\mathrm{couplePair}_{a,b}(p_1,p_2)=\big(p_1+\mathbf 1[b<a]\,p_2,\ \ p_1+\mathbf 1[a<b]\,p_2\big).$$
So $p_2$ is added to the first coordinate if $a>b$, to the second if $a<b$, and to neither if $a=b$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 18. `coupledIncr` (def)

**Rendering.** For $a,b\in\mathbb R_{\ge0}$:
$$\mathrm{CI}(a,b):=(\mathrm{couplePair}_{a,b})_\#\big(\mathrm{Po}(\min(a,b))\otimes\mathrm{Po}(\max(a,b)-\min(a,b))\big),$$
a measure on $\mathbb N^2$. Equivalently, it is the joint law of $(N_1+\mathbf 1[b<a]N_2,\ N_1+\mathbf 1[a<b]N_2)$ with $N_1\sim\mathrm{Po}(\min(a,b))$ and $N_2\sim\mathrm{Po}(\lvert a-b\rvert)$ independent.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** ℝ≥0 subtraction is truncated (C22), but $\max-\min\ge0$, so it equals $\lvert a-b\rvert$ exactly. The push-forward is non-junk because every map on $\mathbb N^2$ is measurable (C21).
**Concerns.** None.

### 19. `coupledIncr_fst` (theorem)

**Rendering.** For all $a,b\in\mathbb R_{\ge0}$, the first marginal $(\mathrm{pr}_1)_\#\mathrm{CI}(a,b)$ equals $\mathrm{Po}(a)$.

**Truth.** True. If $b<a$, the first coordinate is $N_1+N_2\sim\mathrm{Po}(\min+(\max-\min))=\mathrm{Po}(a)$. Otherwise it is $N_1\sim\mathrm{Po}(\min(a,b))=\mathrm{Po}(a)$. Checked numerically.
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 20. `coupledIncr_snd` (theorem)

**Rendering.** For all $a,b\in\mathbb R_{\ge0}$: $\ (\mathrm{pr}_2)_\#\mathrm{CI}(a,b)=\mathrm{Po}(b)$.

**Truth.** True (symmetric to #19; checked).
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 21. `coupled_increments_hasLaw` (theorem)

**Rendering.** Let $\Omega$ carry a σ-algebra and a **probability** measure $\mu$. Let $P_1,P_2:\Omega\to\mathbb N$ and $a,b\in\mathbb R_{\ge0}$. Assume $P_1$ and $P_2$ are independent under $\mu$, $P_1$ has law $\mathrm{Po}(\min(a,b))$, and $P_2$ has law $\mathrm{Po}(\max(a,b)-\min(a,b))$. Then
- $\omega\mapsto P_1(\omega)+\mathbf 1[b<a]P_2(\omega)$ has law $\mathrm{Po}(a)$ under $\mu$, and
- $\omega\mapsto P_1(\omega)+\mathbf 1[a<b]P_2(\omega)$ has law $\mathrm{Po}(b)$ under $\mu$.

(These are the two coordinates of $\mathrm{couplePair}_{a,b}(P_1,P_2)$; "has law" includes a.e.-measurability.)

**Truth.** True (case split as in #19, plus #14).
**Non-vacuity.** The product space of the two Poisson laws.
**Junk values.** None.
**Concerns.** Only the two **marginal** laws are asserted, not the joint law.

### 22. `integral_sq_coupledIncr_sub` (theorem)

**Rendering.** For all $a,b\in\mathbb R_{\ge0}$ (cast to $\mathbb R$):
$$\int_{\mathbb N^2}(p_1-p_2)^2\;\mathrm{CI}(a,b)(dp)=\lvert a-b\rvert+\lvert a-b\rvert^2 .$$

**Truth.** True. Under the coupling $p_1-p_2=\pm N_2$ (or $0$ when $a=b$, where $N_2\sim\delta_0$ anyway), and $\mathbb E N_2^2=\lvert a-b\rvert+\lvert a-b\rvert^2$. Checked numerically.
**Non-vacuity.** No hypotheses.
**Junk values.** None (the integrand is integrable).
**Concerns.** None.

### 23. `tauStep` (def)

**Rendering.** For $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $h\in\mathbb R_{\ge0}$ and $x\in\mathbb N$: $\ \mathrm{tauStep}_{\lambda,h}(x):=(n\mapsto x+n)_\#\,\mathrm{Po}\big(h\,\lambda(x)\big)$. This is the law of $x+N$ with $N\sim\mathrm{Po}(h\lambda(x))$, a probability measure on $\mathbb N$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 24. `tauChain` (def)

**Rendering.** With $\lambda,h$ as above and $x_0\in\mathbb N$:
$$\tau^{(0)}_{\lambda,h,x_0}=\delta_{x_0},\qquad\tau^{(n+1)}_{\lambda,h,x_0}=\operatorname{bind}\big(\tau^{(n)}_{\lambda,h,x_0},\ \mathrm{tauStep}_{\lambda,h}\big),$$
i.e. $\tau^{(n+1)}(B)=\sum_x\tau^{(n)}\{x\}\,\mathrm{tauStep}_{\lambda,h}(x)(B)$. So $\tau^{(n)}$ is the law after $n$ steps of the Markov chain on $\mathbb N$ started at $x_0$ with kernel $\mathrm{tauStep}_{\lambda,h}$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None (the kernel is measurable on discrete ℕ, C21).
**Concerns.** None.

### 25. `coupledTwoStep` (def)

**Rendering.** For $\lambda,h$ as above and $s=(s_1,s_2)\in\mathbb N^2$:
$$\mathrm{CTS}_{\lambda,h}(s)=\operatorname{bind}\Big(\mathrm{CI}\big(h\lambda(s_1),\,h\lambda(s_2)\big),\ (i_1,i_2)\mapsto\big((i_1',i_2')\mapsto(s_1+i_1+i_1',\ s_2+i_2+i_2')\big)_\#\,\mathrm{CI}\big(h\lambda(s_1+i_1),\,h\lambda(s_2)\big)\Big).$$
In words, it is the law of $(s_1+I_1+I_1',\ s_2+I_2+I_2')$, where:
- $(I_1,I_2)\sim\mathrm{CI}(h\lambda(s_1),h\lambda(s_2))$;
- given $(I_1,I_2)$, $(I_1',I_2')\sim\mathrm{CI}(h\lambda(s_1+I_1),h\lambda(s_2))$.

The first coordinate's rate is re-evaluated after the first sub-step. The second coordinate uses $\lambda(s_2)$ in both sub-steps.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 26. `coupledTwoStep_fst` (theorem)

**Rendering.** For all $\lambda,h,s$: $\ (\mathrm{pr}_1)_\#\mathrm{CTS}_{\lambda,h}(s)=\operatorname{bind}\big(\mathrm{tauStep}_{\lambda,h}(s_1),\ \mathrm{tauStep}_{\lambda,h}\big)$, i.e. two consecutive $\mathrm{tauStep}_{\lambda,h}$ transitions from $s_1$.

**Truth.** True. The inner first marginal is $\mathrm{tauStep}_{\lambda,h}(s_1+i_1)$, and the outer first marginal is $\mathrm{Po}(h\lambda(s_1))$. Checked numerically ($L^1$ error about $10^{-16}$).
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 27. `coupledTwoStep_snd` (theorem)

**Rendering.** For all $\lambda,h,s$: $\ (\mathrm{pr}_2)_\#\mathrm{CTS}_{\lambda,h}(s)=\mathrm{tauStep}_{\lambda,2h}(s_2)$, a single step with step size $2h$ from $s_2$.

**Truth.** True: the second marginal is $s_2+N+N'$ with $N,N'$ i.i.d. $\mathrm{Po}(h\lambda(s_2))$. Checked.
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 28. `coupledChain` (def)

**Rendering.**
$$\Gamma^{(0)}_{\lambda,h,x_0}=\delta_{(x_0,x_0)},\qquad\Gamma^{(k+1)}_{\lambda,h,x_0}=\operatorname{bind}\big(\Gamma^{(k)}_{\lambda,h,x_0},\ \mathrm{CTS}_{\lambda,h}\big),$$
a measure on $\mathbb N^2$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 29. `coupledChain_fst` (theorem)

**Rendering.** For all $\lambda,h,x_0$ and every $k\in\mathbb N$: $\ (\mathrm{pr}_1)_\#\Gamma^{(k)}_{\lambda,h,x_0}=\tau^{(2k)}_{\lambda,h,x_0}$.

**Truth.** True (induction using #26 and associativity of bind; checked for $k=1,2$).
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 30. `coupledChain_snd` (theorem)

**Rendering.** For all $\lambda,h,x_0$ and $k$: $\ (\mathrm{pr}_2)_\#\Gamma^{(k)}_{\lambda,h,x_0}=\tau^{(k)}_{\lambda,2h,x_0}$.

**Truth.** True (induction using #27; checked).
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 31. `tauLeaping_2_4` (theorem)

**Rendering.** For all $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $h\in\mathbb R_{\ge0}$, $x_0,k\in\mathbb N$ and every $\Phi:\mathbb N\to\mathbb R$:
$$\int\Phi(s_2)\,\Gamma^{(k)}_{\lambda,h,x_0}(ds)=\int\Phi\,d\tau^{(k)}_{\lambda,2h,x_0}\quad\text{and}\quad\int\Phi(s_1)\,\Gamma^{(k)}_{\lambda,h,x_0}(ds)=\int\Phi\,d\tau^{(2k)}_{\lambda,h,x_0}$$
(Bochner integrals).

**Truth.** True, from #29, #30 and the change of variables for push-forwards (no integrability needed).
**Non-vacuity.** No hypotheses.
**Junk values.** If $\Phi$ is not integrable against the chain law, both sides are $0$ (C1). Integrability is equivalent on the two sides, so this only produces $0=0$. The identity is substantive for integrable $\Phi$.
**Concerns.** None.

### 32. `tauLeaping_level` (theorem)

**Rendering.** For all $\lambda$, $T\in\mathbb R_{\ge0}$, $x_0,\ell\in\mathbb N$ and $\Phi:\mathbb N\to\mathbb R$, put $h=T/2^{\ell+1}$ (in $\mathbb R_{\ge0}$). Then:
$$\int\Phi(s_2)\,\Gamma^{(2^\ell)}_{\lambda,\,T/2^{\ell+1},\,x_0}(ds)=\int\Phi\,d\tau^{(2^\ell)}_{\lambda,\,T/2^{\ell},\,x_0},\qquad\int\Phi(s_1)\,\Gamma^{(2^\ell)}_{\lambda,\,T/2^{\ell+1},\,x_0}(ds)=\int\Phi\,d\tau^{(2^{\ell+1})}_{\lambda,\,T/2^{\ell+1},\,x_0}.$$

**Truth.** True: #31 with $2\cdot T/2^{\ell+1}=T/2^\ell$ and $2\cdot2^\ell=2^{\ell+1}$.
**Non-vacuity.** No hypotheses.
**Junk values.** Same as #31.
**Concerns.** None.

### 33. `tauLeaping_complexity` (theorem)

**Rendering.** For every $\varepsilon\in\mathbb R$: $\ \mathrm{complexityBound}(1,1,1,\varepsilon)=\varepsilon^{-2}(\log\varepsilon)^2$.

**Truth.** True ($\beta=\gamma$ branch).
**Non-vacuity.** No hypotheses.
**Junk values.** At $\varepsilon\le0$ both sides use the rpow/log conventions (C7, C8), identically on both sides.
**Concerns.** **Pure evaluation** of the formula; no probabilistic content.

### 34. `fixed_levels_cost` (theorem)

**Rendering.** Let $\iota$ be any type and $s\subseteq\iota$ a **nonempty finite** set. Let $V,C:\iota\to\mathbb R$ with $V_i>0$ and $C_i>0$ for every $i\in s$ (nothing is assumed off $s$). Then there is a constant $c>0$ such that for **every** $\varepsilon$ with $0<\varepsilon\le1$:
$$\sum_{i\in s}\frac{V_i}{N_i(\varepsilon)}\le\varepsilon^2\qquad\text{and}\qquad\sum_{i\in s}N_i(\varepsilon)\,C_i\le\frac{c}{\varepsilon^2}.$$
Here
$$N_i(\varepsilon)=\mathrm{optimalN}(s,V,C,\varepsilon^2)(i)=\Big\lceil\varepsilon^{-2}\sqrt{V_i/C_i}\ \textstyle\sum_{j\in s}\sqrt{V_jC_j}\Big\rceil_{+}\in\mathbb N$$
(cast to $\mathbb R$). $c$ is chosen before $\varepsilon$.

**Truth.** True with $c=\big(\sum_{j\in s}\sqrt{V_jC_j}\big)^2+\sum_{i\in s}C_i$. Randomised checks give maximum ratios $1.000$ (variance) and $0.9996$ (cost).
**Non-vacuity.** $s=\{i\}$, $V_i=C_i=1$.
**Junk values.** None: $N_i\ge1$, so there is no division by $0$; the square-root arguments are positive; $\tau=\varepsilon^2>0$.
**Concerns.** None.

---

## Block 3 — `MlmcLean.NestedSimulation` (14 declarations)

Throughout, **"$f'$ is a $K$-Lipschitz derivative of $f$"** abbreviates the pair of hypotheses:
- **(hf)** for every $x\in\mathbb R$, $f$ has derivative $f'(x)$ at $x$;
- **(hf′)** for all $x\le y$, $\lvert f'(y)-f'(x)\rvert\le K(y-x)$.

With $x<y$, (hf′) forces $K\ge0$.

### 35. `antithetic_quadratic` (theorem)

**Rendering.** Let $f:\mathbb R\to\mathbb R$ and $c_0,c_1,K\in\mathbb R$ with $f(x)=c_0+c_1x+\tfrac K2x^2$ for all $x$, and let $A,B\in\mathbb R$. Then
$$f\big(\tfrac{A+B}2\big)-\tfrac{f(A)}2-\tfrac{f(B)}2=-\tfrac K8(A-B)^2 ,$$
and, if $K\ne0$ and $A\ne B$, the same quantity is $\ne-\tfrac K4(A-B)^2$.

**Truth.** True (exact check).
**Non-vacuity.** Any quadratic.
**Junk values.** None.
**Concerns.** None.

### 36. `convexOn_half_sq_sub_add` (lemma)

**Rendering.** Let $f,f':\mathbb R\to\mathbb R$ and $K\in\mathbb R$, with $f'$ a $K$-Lipschitz derivative of $f$. Then both $x\mapsto\tfrac K2x^2-f(x)$ and $x\mapsto\tfrac K2x^2+f(x)$ are convex on $\mathbb R$.

**Truth.** True: their derivatives $Kx\mp f'(x)$ are nondecreasing.
**Non-vacuity.** $f=\sin$, $f'=\cos$, $K=1$.
**Junk values.** None.
**Concerns.** None.

### 37. `abs_midpoint_sub_avg_le` (theorem)

**Rendering.** Under the same hypotheses on $f,f',K$, for all $A,B\in\mathbb R$:
$$\Big\lvert f\big(\tfrac{A+B}2\big)-\tfrac{f(A)}2-\tfrac{f(B)}2\Big\rvert\le\tfrac K8(A-B)^2 .$$

**Truth.** True (from #36 applied at the midpoint). Sharp for quadratics (#35). Random tests pass.
**Non-vacuity.** As #36.
**Junk values.** None.
**Concerns.** None.

### 38. `abs_taylor_first_le` (theorem)

**Rendering.** Same hypotheses. For all $x,y$: $\ \lvert f(y)-f(x)-f'(x)(y-x)\rvert\le\tfrac K2(y-x)^2$.

**Truth.** True. Random tests pass.
**Non-vacuity.** As #36.
**Junk values.** None.
**Concerns.** None.

### 39. `abs_deriv_sub_le_of_deriv2` (theorem)

**Rendering.** Let $f',f'':\mathbb R\to\mathbb R$ and $K\in\mathbb R$. Assume $f'$ has derivative $f''(x)$ at every $x$, and $\lvert f''(x)\rvert\le K$ for every $x$. Then for all $x\le y$: $\ \lvert f'(y)-f'(x)\rvert\le K(y-x)$.

**Truth.** True (mean value inequality).
**Non-vacuity.** $f'=\sin$, $f''=\cos$, $K=1$.
**Junk values.** None.
**Concerns.** None.

### 40. `abs_midpoint_sub_avg_le_of_deriv2` (theorem)

**Rendering.** Let $f,f',f'':\mathbb R\to\mathbb R$ and $K$. Assume $f$ has derivative $f'(x)$ at every $x$, $f'$ has derivative $f''(x)$ at every $x$, and $\lvert f''\rvert\le K$ everywhere. Then for all $A,B$: $\ \big\lvert f(\tfrac{A+B}2)-\tfrac{f(A)}2-\tfrac{f(B)}2\big\rvert\le\tfrac K8(A-B)^2$.

**Truth.** True (#39 then #37).
**Non-vacuity.** $f=\sin$, $K=1$.
**Junk values.** None.
**Concerns.** None.

### 41. `mimc_diff_sq` (theorem)

**Rendering.** For all real $a_1,a_2,b_1,b_2$:
$$(a_1-b_1)^2-(a_2-b_2)^2=\big((a_1+a_2)-(b_1+b_2)\big)\big((a_1-a_2)-(b_1-b_2)\big).$$

**Truth.** True (difference of squares; exact check).
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 42. `abs_mimc_diff_sq_le` (theorem)

**Rendering.** For real $a_1,a_2,b_1,b_2,s,t$ with $\lvert a_1+a_2\rvert\le s$, $\lvert b_1+b_2\rvert\le s$, $\lvert a_1-a_2\rvert\le t$ and $\lvert b_1-b_2\rvert\le t$:
$$\big\lvert(a_1-b_1)^2-(a_2-b_2)^2\big\rvert\le4st .$$

**Truth.** True (the two factors of #41 are bounded by $2s$ and $2t$).
**Non-vacuity.** All variables $0$.
**Junk values.** None.
**Concerns.** None.

### 43. `abs_mimc_diff_sq_le_rpow` (theorem)

**Rendering.** For real $a_1,a_2,b_1,b_2,c$ and **real** $\ell_1,\ell_2$, assume:
- $\lvert a_1+a_2\rvert\le c\,2^{-\ell_1/2}$ and $\lvert b_1+b_2\rvert\le c\,2^{-\ell_1/2}$;
- $\lvert a_1-a_2\rvert\le c\,2^{-\ell_1/2-\ell_2}$ and $\lvert b_1-b_2\rvert\le c\,2^{-\ell_1/2-\ell_2}$.

Then $\ \big\lvert(a_1-b_1)^2-(a_2-b_2)^2\big\rvert\le4c^2\,2^{-\ell_1-\ell_2}$.

**Truth.** True (#42 with $s\,t=c^2 2^{-\ell_1-\ell_2}$).
**Non-vacuity.** All variables $0$. (The hypotheses force $c\ge0$.)
**Junk values.** None (base 2).
**Concerns.** None.

### 44. `nested_complexity` (theorem)

**Rendering.** For every $\varepsilon\in\mathbb R$, all four of the following hold:
- $\mathrm{complexityBound}(1,2,1,\varepsilon)=\varepsilon^{-2}$;
- $\mathrm{complexityBound}(1,\tfrac32,1,\varepsilon)=\varepsilon^{-2}$;
- $\mathrm{complexityBound}(1,2,2,\varepsilon)=\varepsilon^{-2}(\log\varepsilon)^2$;
- $\mathrm{complexityBound}(1,\tfrac32,2,\varepsilon)=\varepsilon^{-5/2}$.

The literals `1.5` and `-2.5` are exactly $3/2$ and $-5/2$ (C25).

**Truth.** True: the branches are $1<2$; $1<\tfrac32$; $2=2$; and $2>\tfrac32$ with exponent $-2-\tfrac{2-3/2}1=-\tfrac52$.
**Non-vacuity.** No hypotheses.
**Junk values.** Formal identities for every real $\varepsilon$, including $\varepsilon\le0$.
**Concerns.** **Pure evaluation** of the formula.

### 45. `nested_mimc_complexity` (theorem)

**Rendering.** For all $e_1,e_2,\varepsilon\in\mathbb R$, with $D=2$ and constant vectors on $\{0,1\}$:
- $\mathrm{mimcEta}(\alpha\equiv1,\beta\equiv2,\gamma\equiv1)=-1$;
- $\mathrm{mimcEta}(\alpha\equiv1,\beta\equiv\tfrac32,\gamma\equiv1)=-\tfrac12$;
- $\mathrm{mimcBound}(-1,e_1,e_2,\varepsilon)=\varepsilon^{-2}$;
- $\mathrm{mimcBound}(-\tfrac12,e_1,e_2,\varepsilon)=\varepsilon^{-2}$.

Here $\mathrm{mimcEta}(\alpha,\beta,\gamma)=\max_{d}\,(\gamma_d-\beta_d)/\alpha_d$, and $\mathrm{mimcBound}(\eta,e_1,e_2,\varepsilon)$ equals $\varepsilon^{-2}$ if $\eta<0$, $\varepsilon^{-2}\lvert\log\varepsilon\rvert^{e_1}$ if $\eta=0$, and $\varepsilon^{-2-\eta}\lvert\log\varepsilon\rvert^{e_2}$ otherwise (see #95, #96).

**Truth.** True.
**Non-vacuity.** No hypotheses.
**Junk values.** Same formal identities for all real $\varepsilon$.
**Concerns.** **Pure evaluation.** $e_1,e_2$ play no role (the $\eta<0$ branch applies).

### 46. `integrable_pow_of_pow_four` (lemma)

**Rendering.** $\Omega$ has a σ-algebra and $\mu$ is a **finite** measure. Let $Y:\Omega\to\mathbb R$ be measurable with $Y^4$ $\mu$-integrable, and $k\in\mathbb N$ with $k\le4$. Then $Y^k$ is $\mu$-integrable.

**Truth.** True, since $\lvert Y\rvert^k\le1+Y^4$.
**Non-vacuity.** $Y=0$.
**Junk values.** None.
**Concerns.** None ($k=0$ is included and trivially true).

### 47. `moments_add_indep` (theorem)

**Rendering.** $\mu$ is a **probability** measure on $\Omega$. Let $S,X:\Omega\to\mathbb R$ be independent and measurable, with $S^4$ and $X^4$ integrable and $\mathbb E S=\mathbb E X=0$. Then:
- $(S+X)^4$ is integrable;
- $\mathbb E(S+X)^2=\mathbb E S^2+\mathbb E X^2$;
- $\mathbb E(S+X)^4=\mathbb E S^4+6\,\mathbb E S^2\,\mathbb E X^2+\mathbb E X^4$.

**Truth.** True (the odd cross moments vanish by independence and centring).
**Non-vacuity.** $S=X=0$.
**Junk values.** None.
**Concerns.** None.

### 48. `moments_sum_indep` (theorem)

**Rendering.** $\mu$ is a probability measure. $(X_i)_{i\in\mathbb N}$ are real random variables that are **mutually** independent and each measurable, with $X_i^4$ integrable and $\mathbb E X_i=0$. Let $v,q\in\mathbb R$ with $\mathbb E X_i^2=v$ for every $i$ and $\mathbb E X_i^4\le q$ for every $i$, and let $n\in\mathbb N$. Then, with $S_n=\sum_{i<n}X_i$:
- $S_n^4$ is integrable;
- $\mathbb E S_n^2=nv$;
- $\mathbb E S_n^4\le nq+3n^2v^2$.

**Truth.** True. Exactly, $\mathbb E S_n^4=\sum_{i<n}\mathbb E X_i^4+3n(n-1)v^2$; checked for discrete laws.
**Non-vacuity.** $X_i\equiv0$, $v=q=0$.
**Junk values.** None.
**Concerns.** None.

---

## Block 4 — `MlmcLean.NestedMLMC` (27 declarations)

Ambient context: $\mathcal Z$ and $\mathcal W$ are arbitrary types with σ-algebras. $\mathcal W^{\mathbb N}$ carries the product σ-algebra, and $\mathcal Z\times\mathcal W^{\mathbb N}$ the product σ-algebra. In sections `Centred`, `Fiber` and `Product`, the measures $\mu$ (on $\Omega$), $\rho$ (on $\mathcal W$) and $\nu$ (on $\mathcal Z$) come with **probability-measure** instances, and these are included whenever the measure appears in the statement.

### 49. `abs_le_quadratic` (lemma)

**Rendering.** Let $f'$ be a $K$-Lipschitz derivative of $f$ (as in Block 3). For every $y\in\mathbb R$:
$$\lvert f(y)\rvert\le\lvert f(0)\rvert+\lvert f'(0)\rvert+\big(\lvert f'(0)\rvert+\tfrac K2\big)y^2 .$$

**Truth.** True (#38 at $x=0$, together with $\lvert y\rvert\le1+y^2$). Random tests pass.
**Non-vacuity.** $f=\sin$.
**Junk values.** None.
**Concerns.** None.

### 50. `centred_moments_le` (theorem)

**Rendering.** $\mu$ is a probability measure on $\Omega$. Let $Y:\Omega\to\mathbb R$ be measurable with $Y^4$ integrable, and $m:=\int Y\,d\mu$. Then all four hold:
- $(Y-m)^4$ is integrable;
- $\mathbb E(Y-m)^4\le16\,\mathbb EY^4$;
- $\big(\mathbb E(Y-m)^2\big)^2\le\mathbb E(Y-m)^4$;
- $\mathbb E(Y-m)^2\le1+16\,\mathbb EY^4$.

**Truth.** True. Use $(a+b)^4\le8(a^4+b^4)$, Jensen's inequality, and $x\le1+x^2$. Random discrete checks pass (worst observed ratio $2.12$ against the bound 16).
**Non-vacuity.** $Y=0$.
**Junk values.** None.
**Concerns.** Informational only: the last bound is not scale-invariant (it adds 1). That makes it crude, not wrong.

### 51. `memLp_two_comp_of_pow_four` (lemma)

**Rendering.** Let $f'$ be a $K$-Lipschitz derivative of $f$, $\mu$ a probability measure, and $X:\Omega\to\mathbb R$ measurable with $X^4$ integrable. Then $f\circ X\in L^2(\mu)$ (a.e.-strongly measurable with finite second moment).

**Truth.** True (quadratic growth from #49).
**Non-vacuity.** $X=0$.
**Junk values.** None.
**Concerns.** None.

### 52. `innerMean` (def)

**Rendering.** For $g:\mathcal Z\to\mathcal W\to\mathbb R$, $M\in\mathbb N$, $z\in\mathcal Z$ and $w=(w_m)_{m\in\mathbb N}\in\mathcal W^{\mathbb N}$:
$$\mathrm{innerMean}(g,M,z,w)=M^{-1}\sum_{m=0}^{M-1}g(z,w_m).$$

**Truth / Non-vacuity.** Not applicable.
**Junk values.** For $M=0$ the value is $0^{-1}\cdot0=0$ (C11).
**Concerns.** None.

### 53. `shiftSeq` (def)

**Rendering.** $\mathrm{shiftSeq}(M,w)=(w_{M+m})_{m\in\mathbb N}$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 54. `nestedSign` (def)

**Rendering.** $\mathrm{nestedSign}(M,m)=1$ if $m<M$, and $-1$ otherwise (as a real number).

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 55. `innerLaw` (abbrev)

**Rendering.** For a measure $\rho$ on $\mathcal W$: $\ \mathrm{innerLaw}(\rho)=\rho^{\otimes\mathbb N}$ on $\mathcal W^{\mathbb N}$, the law of an i.i.d. $\rho$ sequence.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** **The zero measure if $\rho$ is not a probability measure** (C14).
**Concerns.** None in context: every theorem using it assumes $\rho$ is a probability measure.

### 56. `nestedLaw` (abbrev)

**Rendering.** $\mathrm{nestedLaw}(\nu,\rho)=\nu\otimes\rho^{\otimes\mathbb N}$ on $\mathcal Z\times\mathcal W^{\mathbb N}$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** Inherits #55.
**Concerns.** None in context.

### 57. `nestedP` (def)

**Rendering.** For $f:\mathbb R\to\mathbb R$, $g$, $\ell\in\mathbb N$ and $(z,w)$:
$$\mathrm{nestedP}(f,g,\ell)(z,w)=f\big(\mathrm{innerMean}(g,2^\ell,z,w)\big)=f\Big(2^{-\ell}\sum_{m<2^\ell}g(z,w_m)\Big).$$

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None ($2^\ell\ge1$).
**Concerns.** None.

### 58. `nestedDelta` (def)

**Rendering.** Write $\bar Y_M(z,w)=\mathrm{innerMean}(g,M,z,w)$. Then:
- $\mathrm{nestedDelta}(f,g,0)(z,w)=\mathrm{nestedP}(f,g,0)(z,w)=f(g(z,w_0))$;
- $\mathrm{nestedDelta}(f,g,\ell+1)(z,w)=f\big(\bar Y_{2^{\ell+1}}(z,w)\big)-\tfrac12f\big(\bar Y_{2^\ell}(z,w)\big)-\tfrac12f\big(\bar Y_{2^\ell}(z,\mathrm{shiftSeq}(2^\ell,w))\big)$.

The last term averages the second block $w_{2^\ell},\dots,w_{2^{\ell+1}-1}$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 59. `nestedTarget` (def)

**Rendering.** $\mathrm{nestedTarget}(f,g,\rho)(z,w)=f\big(\int_{\mathcal W}g(z,v)\,\rho(dv)\big)$. It does not depend on $w$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** The inner integral is a Bochner integral, so it is $0$ when $g(z,\cdot)\notin L^1(\rho)$ (C1).
**Concerns.** Under the $L^4$ hypotheses used later, this happens only on a $\nu$-null set of $z$, so it is harmless there.

### 60. `innerMean_two_mul` (theorem)

**Rendering.** For all $g,M,z,w$:
$$\mathrm{innerMean}(g,2M,z,w)=\tfrac12\big(\mathrm{innerMean}(g,M,z,w)+\mathrm{innerMean}(g,M,z,\mathrm{shiftSeq}(M,w))\big).$$

**Truth.** True for all $M$ (at $M=0$ both sides are $0$ by C11).
**Non-vacuity.** No hypotheses.
**Junk values.** The $M=0$ case holds through $0^{-1}=0$; this is harmless.
**Concerns.** None.

### 61. `signed_sum_eq` (lemma)

**Rendering.** For all $g,M,z,w$ and every $a\in\mathbb R$:
$$\mathrm{innerMean}(g,M,z,w)-\mathrm{innerMean}(g,M,z,\mathrm{shiftSeq}(M,w))=M^{-1}\sum_{m<2M}\mathrm{nestedSign}(M,m)\,\big(g(z,w_m)-a\big).$$

**Truth.** True: the $\pm a$ terms cancel. At $M=0$ both sides are $0$.
**Non-vacuity.** No hypotheses.
**Junk values.** The $M=0$ case uses $0^{-1}=0$; harmless.
**Concerns.** None.

### 62. `centred_sum_eq` (lemma)

**Rendering.** For $g$, $M\in\mathbb N$ with $M>0$, and all $z,w,a$:
$$\mathrm{innerMean}(g,M,z,w)-a=M^{-1}\sum_{m<M}\mathrm{nestedSign}(M,m)\,\big(g(z,w_m)-a\big).$$

**Truth.** True. (It would be false for $M=0$, $a\neq0$, so $M>0$ is needed.)
**Non-vacuity.** $M=1$.
**Junk values.** None.
**Concerns.** None.

### 63. `measurePreserving_shiftSeq` (theorem)

**Rendering.** Let $\rho$ be a probability measure on $\mathcal W$ and $M\in\mathbb N$. The map $w\mapsto\mathrm{shiftSeq}(M,w)$, from $\mathcal W^{\mathbb N}$ to itself, is measurable and $(\mathrm{shiftSeq}(M,\cdot))_\#\rho^{\otimes\mathbb N}=\rho^{\otimes\mathbb N}$.

**Truth.** True (a shifted i.i.d. sequence is i.i.d. with the same marginal).
**Non-vacuity.** Any probability measure $\rho$ (e.g. a Dirac mass).
**Junk values.** None.
**Concerns.** None.

### 64. `integral_nestedDelta` (theorem)

**Rendering.** Let $\nu,\rho$ be probability measures, $f:\mathbb R\to\mathbb R$ and $g:\mathcal Z\to\mathcal W\to\mathbb R$ arbitrary (**no measurability assumed**). Assume $\mathrm{nestedP}(f,g,\ell)$ is $\mathrm{nestedLaw}(\nu,\rho)$-integrable **for every** $\ell\in\mathbb N$. Then for every $\ell$:
$$\int\mathrm{nestedDelta}(f,g,\ell)\,d\,\mathrm{nestedLaw}(\nu,\rho)=\int\mathrm{levelDiff}\big(\mathrm{nestedP}(f,g)\big)(\ell)\,d\,\mathrm{nestedLaw}(\nu,\rho).$$
Here $\mathrm{levelDiff}(P)(0)=P_0$ and $\mathrm{levelDiff}(P)(\ell+1)=P_{\ell+1}-P_\ell$ (#91).

**Truth.** True. $\ell=0$ holds by definition. For $\ell+1$, use linearity and invariance of $\mathrm{nestedLaw}$ under $(z,w)\mapsto(z,\mathrm{shiftSeq}(2^\ell,w))$ (from #63), which also gives integrability of the shifted term.
**Non-vacuity.** $f=\sin$, $g=0$.
**Junk values.** None (integrability is assumed).
**Concerns.** None (it assumes integrability at all levels, more than it uses).

### 65. `fiber_sum_moments` (theorem)

**Rendering.** Let $\rho$ be a probability measure on $\mathcal W$ and $h:\mathcal W\to\mathbb R$ measurable with $h^4\in L^1(\rho)$. Let $c:\mathbb N\to\mathbb R$ with $c_m^2=1$ for all $m$, and $n\in\mathbb N$. Put
- $a=\int h\,d\rho$, $\sigma^2=\int(h-a)^2d\rho$, $\kappa=\int(h-a)^4d\rho$;
- $S_n(w)=\sum_{m<n}c_m\big(h(w_m)-a\big)$.

Under $\rho^{\otimes\mathbb N}$:
- $S_n^4$ is integrable;
- $\mathbb E S_n=0$;
- $\mathbb E S_n^2=n\sigma^2$;
- $\mathbb E S_n^4\le n\kappa+3n^2\sigma^4$.

**Truth.** True (the coordinates are i.i.d.; see #48).
**Non-vacuity.** $h=0$, $c\equiv1$.
**Junk values.** None.
**Concerns.** None.

### 66. `fiber_nested_moments` (theorem)

**Rendering.** Let $\rho$ be a probability measure, $g:\mathcal Z\to\mathcal W\to\mathbb R$, and $z\in\mathcal Z$ fixed with $g(z,\cdot)$ measurable and $g(z,\cdot)^4\in L^1(\rho)$. Let $M\in\mathbb N$, $M>0$. Put:
- $G_4=\int g(z,v)^4\rho(dv)$ and $a=\int g(z,v)\rho(dv)$;
- $D(w)=\mathrm{innerMean}(g,M,z,w)-\mathrm{innerMean}(g,M,z,\mathrm{shiftSeq}(M,w))$;
- $E(w)=\mathrm{innerMean}(g,M,z,w)-a$.

Then under $\rho^{\otimes\mathbb N}$:
- $D^4$ is integrable;
- $M\,\mathbb E D^2\le2(1+16G_4)$;
- $M^2\,\mathbb E D^4\le224\,G_4$;
- $E^4$ is integrable;
- $M\,\mathbb E E^2\le1+16G_4$;
- $\mathbb E E=0$.

**Truth.** True. $M\mathbb ED^2=2\sigma^2$ and $M^2\mathbb ED^4\le2\kappa+12\sigma^4\le14\kappa\le224G_4$, then apply #50. Exact enumeration for four discrete laws and $M\le3$ passes (worst ratio against 224 is $0.048$).
**Non-vacuity.** $g=0$, $M=1$.
**Junk values.** None.
**Concerns.** None ($M>0$ is needed for $\mathbb EE=0$).

### 67. `fiber_bias_le` (theorem)

**Rendering.** Let $f'$ be a $K$-Lipschitz derivative of $f$, $\rho$ a probability measure, and $g,z$ with $g(z,\cdot)$ measurable and $g(z,\cdot)^4\in L^1(\rho)$. Let $M>0$. Then
$$M\cdot\Big\lvert\int\Big(f\big(\mathrm{innerMean}(g,M,z,w)\big)-f\big(\textstyle\int g(z,v)\rho(dv)\big)\Big)\,\rho^{\otimes\mathbb N}(dw)\Big\rvert\le\tfrac K2\big(1+16G_4\big).$$

**Truth.** True: by Taylor (#38) the bias is at most $\tfrac K2\,\sigma^2/M$, and $\sigma^2\le1+16G_4$. Monte Carlo checks pass.
**Non-vacuity.** $f=\sin$, $g=0$.
**Junk values.** None.
**Concerns.** Minor: $M>0$ is superfluous (for $M=0$ the left side is $0$ and $K\ge0$).

### 68. `integrable_of_fiber_bound` (lemma)

**Rendering.** Let $\nu,\rho$ be probability measures. Let $F:\mathcal Z\times\mathcal W^{\mathbb N}\to\mathbb R$ be measurable with $F\ge0$ everywhere, and $B:\mathcal Z\to\mathbb R$ $\nu$-integrable. Assume that for $\nu$-a.e. $z$, $F(z,\cdot)$ is $\rho^{\otimes\mathbb N}$-integrable and $\int F(z,w)\rho^{\otimes\mathbb N}(dw)\le B(z)$. Then $F$ is $\mathrm{nestedLaw}(\nu,\rho)$-integrable and $\int F\,d\,\mathrm{nestedLaw}\le\int B\,d\nu$.

**Truth.** True (Tonelli/Fubini).
**Non-vacuity.** $F=0$, $B=0$.
**Junk values.** None.
**Concerns.** None.

### 69. `nested_variance_rate` (theorem)

**Rendering.** Let $f'$ be a $K$-Lipschitz derivative of $f$ and $\nu,\rho$ probability measures. Let $g:\mathcal Z\to\mathcal W\to\mathbb R$ with $(z,v)\mapsto g(z,v)$ jointly measurable and $g^4\in L^1(\nu\otimes\rho)$, and let $\ell\in\mathbb N$. Then $\mathrm{nestedDelta}(f,g,\ell+1)\in L^2(\mathrm{nestedLaw}(\nu,\rho))$ and
$$(2^\ell)^2\int\mathrm{nestedDelta}(f,g,\ell+1)^2\,d\,\mathrm{nestedLaw}(\nu,\rho)\le\big(\tfrac K8\big)^2\cdot224\int g^4\,d(\nu\otimes\rho).$$

**Truth.** True: $\lvert\Delta\rvert\le\tfrac K8D^2$ by #37 and #60, then #66 fibrewise and #68.
**Non-vacuity.** $f(x)=x^2$ ($K=2$), $g=0$.
**Junk values.** None.
**Concerns.** None.

### 70. `nested_mean_rate` (theorem)

**Rendering.** Same hypotheses as #69. For every $\ell$:
$$2^\ell\,\Big\lvert\int\mathrm{nestedDelta}(f,g,\ell+1)\,d\,\mathrm{nestedLaw}(\nu,\rho)\Big\rvert\le\tfrac K4\Big(1+16\int g^4\,d(\nu\otimes\rho)\Big).$$

**Truth.** True: $2^\ell\,\mathbb E\lvert\Delta\rvert\le\tfrac K8\,\mathbb E_z[2\sigma^2(z)]$. Monte Carlo with $f=x^2$ gives about $0.5$ against the bound $96.5$.
**Non-vacuity.** As #69.
**Junk values.** None.
**Concerns.** None.

### 71. `integrable_innerMean_pow_four` (lemma)

**Rendering.** Let $\nu,\rho$ be probability measures, $g$ jointly measurable with $g^4\in L^1(\nu\otimes\rho)$, and $M>0$. Then $(z,w)\mapsto\mathrm{innerMean}(g,M,z,w)^4$ is $\mathrm{nestedLaw}(\nu,\rho)$-integrable.

**Truth.** True (power-mean inequality; each $(z,w_m)$ has law $\nu\otimes\rho$).
**Non-vacuity.** $g=0$.
**Junk values.** None.
**Concerns.** Minor: $M>0$ is superfluous ($M=0$ gives the zero function via C11).

### 72. `integrable_condMean_pow_four` (lemma)

**Rendering.** With $\nu,\rho,g$ as in #71: the map $z\mapsto\int g(z,v)\rho(dv)$ is measurable, and its fourth power is $\nu$-integrable.

**Truth.** True (measurability of parametric integrals, Jensen, Fubini).
**Non-vacuity.** $g=0$.
**Junk values.** The inner Bochner integral is $0$ on the ($\nu$-null) set where $g(z,\cdot)\notin L^1(\rho)$. This is harmless.
**Concerns.** None.

### 73. `nested_bias_rate` (theorem)

**Rendering.** Same hypotheses as #69. For every $\ell$:
$$2^\ell\,\Big\lvert\int\Big(\mathrm{nestedP}(f,g,\ell)-\mathrm{nestedTarget}(f,g,\rho)\Big)\,d\,\mathrm{nestedLaw}(\nu,\rho)\Big\rvert\le\tfrac K2\Big(1+16\int g^4\,d(\nu\otimes\rho)\Big),$$
i.e. $2^\ell\big\lvert\mathbb E\big[f(\bar Y_{2^\ell})-f(\int g(z,v)\rho(dv))\big]\big\rvert\le\dots$

**Truth.** True (#67 fibrewise with $M=2^\ell$, integrated over $z$). Monte Carlo passes.
**Non-vacuity.** As #69.
**Junk values.** `nestedTarget` has an inner-integral junk value only on a $\nu$-null set.
**Concerns.** None.

### 74. `nested_mlmc_complexity` (theorem)

**Rendering.** Ambient data: probability measures $\nu$ on $\mathcal Z$ and $\rho$ on $\mathcal W$; a type $\Omega$ with a σ-algebra and a **probability** measure $\mu$. Binders and hypotheses:
- $f,f':\mathbb R\to\mathbb R$ and $K\in\mathbb R$, with $f'$ a $K$-Lipschitz derivative of $f$ (hf, hf′).
- $g:\mathcal Z\to\mathcal W\to\mathbb R$ with **(hg)** $(z,v)\mapsto g(z,v)$ jointly measurable and **(hg4)** $g^4\in L^1(\nu\otimes\rho)$.
- A doubly indexed family $\omega_{(\ell,n)}:\Omega\to\mathcal Z\times\mathcal W^{\mathbb N}$, $(\ell,n)\in\mathbb N\times\mathbb N$, with:
  - **(hω)** each $\omega_{(\ell,n)}$ measurable with law $\mathrm{nestedLaw}(\nu,\rho)=\nu\otimes\rho^{\otimes\mathbb N}$;
  - **(hind)** the whole family $(\omega_p)_{p\in\mathbb N\times\mathbb N}$ is mutually independent under $\mu$.
- $\mathrm{cost}:\mathbb N\to\mathbb N\to\Omega\to\mathbb R$, $C:\mathbb N\to\mathbb R$ and $c_3\in\mathbb R$, with:
  - **(hc₃)** $c_3>0$;
  - **(hcost)** each $\mathrm{cost}_{\ell,n}$ is $\mu$-integrable;
  - **(hcostC)** $\mathbb E_\mu[\mathrm{cost}_{\ell,n}]=C_\ell$ for all $\ell,n$;
  - **(hC)** $C_\ell\le c_3\,2^\ell$ for all $\ell$.

Conclusion: **there exists $c_4>0$ such that for every $\varepsilon$ with $0<\varepsilon<e^{-1}$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with $N_\ell\ge1$ for every $\ell\in\mathbb N$** such that
$$\mathbb E_\mu\Big[\Big(\sum_{\ell=0}^{L}\hat Y_\ell-\theta\Big)^2\Big]<\varepsilon^2\qquad\text{and}\qquad\mathbb E_\mu\Big[\sum_{\ell=0}^{L}\sum_{n=0}^{N_\ell-1}\mathrm{cost}_{\ell,n}\Big]\le c_4\,\varepsilon^{-2}.$$
Here:
- $\hat Y_\ell(x)=\mathrm{blockMean}(\Delta,\omega,\ell,N_\ell)(x)=N_\ell^{-1}\sum_{n<N_\ell}\Delta_\ell\big(\omega_{(\ell,n)}(x)\big)$ with $\Delta_\ell=\mathrm{nestedDelta}(f,g,\ell)$ (#58, #94);
- $\theta=\int_{\mathcal Z}f\big(\int_{\mathcal W}g(z,v)\rho(dv)\big)\nu(dz)$ (subtracted **once**, outside the sum; parsing checked, C24);
- the left conjunct is a Bochner integral; the right one is $\mathbb E_\mu[\mathrm{totalCost}(\mathrm{cost},L,N)]$ (#93).

**Truth.** True.
- Telescoping (#64, #91) gives $\mathbb E\sum_{\ell\le L}\hat Y_\ell=\mathbb E\,\mathrm{nestedP}(f,g,L)$, so by #73 the bias is at most $\tfrac K2(1+16\mathbb Eg^4)2^{-L}$.
- $\operatorname{Var}\Delta_0<\infty$ (#49 and $g\in L^4$), and $\operatorname{Var}\Delta_\ell\le A\,4^{-\ell}$ for $\ell\ge1$ (#69).
- Independence gives MSE $=$ bias$^2+\sum_\ell\operatorname{Var}\Delta_\ell/N_\ell$.
- Choose $2^L=O(1/\varepsilon)$ with bias$^2<\varepsilon^2/2$, and the usual allocation $N_\ell\approx\varepsilon^{-2}2^{-3\ell/2}\cdot$const (with $N_\ell\ge1$). Then the variance is at most $\varepsilon^2/2$, and $\sum_{\ell\le L}N_\ell c_32^\ell=O(\varepsilon^{-2})+c_3 2^{L+1}=O(\varepsilon^{-2})$.
- Since $N_\ell\ge0$ and $C_\ell\le c_32^\ell$, the expected cost $\sum N_\ell C_\ell$ is at most that.

**Non-vacuity.** Take $\Omega=(\mathcal Z\times\mathcal W^{\mathbb N})^{\mathbb N\times\mathbb N}$ with $\mathrm{nestedLaw}^{\otimes(\mathbb N\times\mathbb N)}$ and $\omega_p=$ coordinate $p$ (i.i.d.), $f(x)=x^2$ ($K=2$), $g=0$ (or any bounded measurable $g$), $\mathrm{cost}_{\ell,n}\equiv2^\ell$, $C_\ell=2^\ell$, $c_3=1$.
**Junk values.** None that can be exploited. For every choice of $L,N$ the squared-error integrand is integrable (each $\Delta_\ell\in L^2$, and $\theta$ is finite), so the Bochner-0 convention never applies. The inner integral in $\theta$ is junk only on a $\nu$-null set. $\varepsilon>0$, so $\varepsilon^{-2}$ is ordinary.
**Concerns.** Informational, not errors:
- only $\varepsilon\in(0,e^{-1})$ is covered;
- $c_4$ may depend on all data ($f,K,g,\nu,\rho,c_3,C$) and is only independent of $\varepsilon$;
- the costs are arbitrary integrable random variables constrained only through their means, which are only **upper**-bounded (they may be $\le0$);
- $c_3>0$ is not actually needed;
- $N_\ell\ge1$ is demanded for all $\ell$, including $\ell>L$, which is irrelevant.

### 75. `nested_mlmc_complexity_iid` (theorem)

**Rendering.** Let $\nu,\rho$ be probability measures and $f,f',K,g$ with (hf), (hf′), (hg), (hg4) as in #74. Let $\Pi:=\mathrm{nestedLaw}(\nu,\rho)^{\otimes(\mathbb N\times\mathbb N)}$ on $(\mathcal Z\times\mathcal W^{\mathbb N})^{\mathbb N\times\mathbb N}$, with generic point $x=(x_p)_p$. Then there exists $c_4>0$ such that for every $0<\varepsilon<e^{-1}$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with all $N_\ell\ge1$ such that
$$\int\Big(\sum_{\ell=0}^{L}N_\ell^{-1}\sum_{n<N_\ell}\Delta_\ell(x_{(\ell,n)})-\theta\Big)^2\Pi(dx)<\varepsilon^2\quad\text{and}\quad\int\sum_{\ell=0}^{L}\sum_{n<N_\ell}2^\ell\,\Pi(dx)\;\Big(=\sum_{\ell\le L}N_\ell2^\ell\Big)\le c_4\varepsilon^{-2}.$$
$\Delta_\ell$ and $\theta$ are as in #74.

**Truth.** True: the special case of #74 with coordinate maps (i.i.d. under $\Pi$) and deterministic cost $2^\ell$.
**Non-vacuity.** The same example as #74.
**Junk values.** $\Pi$ is non-zero because $\mathrm{nestedLaw}(\nu,\rho)$ is a probability measure (otherwise C14 would make it $0$ and the first conjunct trivial). Otherwise as #74.
**Concerns.** As #74. Here the cost conjunct is the deterministic inequality $\sum_{\ell\le L}N_\ell2^\ell\le c_4\varepsilon^{-2}$.

---

## Block 5 — `MlmcLean.MarkovChain` (14 declarations)

### 76. `backIter` (def)

**Rendering.** For $\varphi:\alpha\to E\to\alpha$ (write $\varphi_e:=\varphi(\cdot,e)$), $n\in\mathbb N$, $e=(e_k)_{k\in\mathbb N}\in E^{\mathbb N}$ and $x\in\alpha$:
$$\mathrm{backIter}(\varphi,0,e,x)=x,\qquad\mathrm{backIter}(\varphi,n+1,e,x)=\varphi\big(\mathrm{backIter}(\varphi,n,(e_{k+1})_k,x),\,e_0\big).$$
Unrolled: $\mathrm{backIter}(\varphi,n,e,x)=\varphi_{e_0}\circ\varphi_{e_1}\circ\cdots\circ\varphi_{e_{n-1}}(x)$. So $e_{n-1}$ is applied **first** and $e_0$ **last** (backward composition; checked symbolically).

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 77. `backIter_add` (lemma)

**Rendering.** For all $\varphi,n,m,e,x$:
$$\mathrm{backIter}(\varphi,n+m,e,x)=\mathrm{backIter}\big(\varphi,m,e,\ \mathrm{backIter}(\varphi,n,(e_{k+m})_k,x)\big).$$

**Truth.** True (symbolic check for $n,m<4$).
**Non-vacuity.** No hypotheses.
**Junk values.** None.
**Concerns.** None.

### 78. `noiseFrom` (def)

**Rendering.** For $\xi:\mathbb N\to\Omega\to E$ ($E$ with σ-algebra $\mathcal E$) and $m\in\mathbb N$:
$$\mathrm{noiseFrom}(\xi,m)=\bigvee_{i\ge m}\xi_i^{-1}(\mathcal E)=\sigma(\xi_m,\xi_{m+1},\dots),$$
a σ-algebra on $\Omega$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

Ambient context of the `contraction` section, used by #79–#82:
- $\alpha$ is a pseudometric space with distance $d$, carrying a σ-algebra that contains the open sets, and with second-countable topology.
- $E$ is a measurable space.
- $\Omega$ is a measurable space with a **probability** measure $\mu$.
- $\nu$ is a measure on $E$ (not assumed probability).
- $\varphi:\alpha\to E\to\alpha$ and $\xi:\mathbb N\to\Omega\to E$.

The shared hypotheses are:
- **(hφm)** $(x,e)\mapsto\varphi(x,e)$ is measurable on $\alpha\times E$;
- **(hξ)** $(\xi_i)_{i\in\mathbb N}$ is mutually independent under $\mu$;
- **(hξm)** each $\xi_i$ is measurable;
- **(hlaw)** $(\xi_i)_\#\mu=\nu$ for all $i$ (which forces $\nu$ to be a probability measure).

### 79. `lintegral_dist_backIter_le` (theorem)

**Rendering.** Assume (hφm), (hξ), (hξm), (hlaw). Let $p,\rho\in\mathbb R$ be **arbitrary**, and assume
- **(hφ)** $\forall x,y\in\alpha:\ \int^{-}\big(d(\varphi(x,e),\varphi(y,e))^p\big)^{+}\nu(de)\le\rho^{+}\cdot\big(d(x,y)^p\big)^{+}$ (in $[0,\infty]$).

Let $n\in\mathbb N$. Then for every $m\in\mathbb N$ and all $U,V:\Omega\to\alpha$ that are measurable with respect to $\mathrm{noiseFrom}(\xi,m+n)=\sigma(\xi_i:i\ge m+n)$:
$$\int^{-}\Big(d\big(X^U(\omega),X^V(\omega)\big)^p\Big)^{+}\mu(d\omega)\le(\rho^{+})^n\int^{-}\big(d(U(\omega),V(\omega))^p\big)^{+}\mu(d\omega),$$
where $X^U(\omega)=\mathrm{backIter}\big(\varphi,n,(\xi_{k+m}(\omega))_k,U(\omega)\big)=\varphi_{\xi_m(\omega)}\circ\cdots\circ\varphi_{\xi_{m+n-1}(\omega)}(U(\omega))$, and similarly for $V$.

**Truth.** True. Induct on $n$, generalising $m$: $\xi_m$ is independent of $\mathrm{noiseFrom}(\xi,m+1)$, so Fubini plus (hφ) gives one factor $\rho^+$ per step.
**Non-vacuity.** $\alpha=E=\mathbb R$, $\varphi=$ `halfStep`, $\nu=$ `fairCoin`, $\rho=(1/2)^p$ (#86), $\xi$ i.i.d. fair coins on a product space, $U,V$ constants.
**Junk values.** $p$ and $\rho$ are unconstrained. For $p\le0$ the integrands use $0^0=1$ and $0^p=0$ at zero distance (C7), where mathematically $d^p=\infty$ for $p<0$. For $\rho<0$, $\rho^+=0$. The statement is still true in these degenerate cases. The meaningful range is $p>0$, $\rho\ge0$.
**Concerns.** None substantive.

### 80. `lintegral_dist_start_le` (theorem)

**Rendering.** Assume (hφm), (hξ), (hξm), (hlaw). Let $\gamma,\rho\in\mathbb R$, assume **(hφ)** with exponent $2\gamma$ (i.e. $\forall x,y:\int^{-}(d(\varphi(x,e),\varphi(y,e))^{2\gamma})^{+}\nu(de)\le\rho^{+}(d(x,y)^{2\gamma})^{+}$), and assume $0<\gamma\le1$ and $0\le\rho<1$. Let $x_0\in\alpha$ and $k,m\in\mathbb N$. Then
$$\int^{-}\Big(d\big(x_0,\ \mathrm{backIter}(\varphi,k,(\xi_{j+m}(\omega))_j,x_0)\big)^{2\gamma}\Big)^{+}\mu(d\omega)\le\Big(\frac4{(1-\rho)^2}\Big)^{+}\cdot\int^{-}\big(d(x_0,\varphi(x_0,e))^{2\gamma}\big)^{+}\nu(de).$$
The bound is uniform in $k$ and $m$.

**Truth.** True. Telescope $d(x_0,X_k)\le\sum_{j<k}d(X_j,X_{j+1})$ and apply #79 to each term ($\le\rho^jc$). Then use subadditivity of $t^{2\gamma}$ if $2\gamma\le1$, or Minkowski if $1<2\gamma\le2$, with $(1-\rho^{1/q})^q\ge(1-\rho)^2/4$.
- Exact enumeration on the halfStep chain passes.
- A deterministic contraction shows the constant 4 is attained in the limit (ratio $0.995$).
- The hypothesis $\gamma\le1$ is genuinely needed ($\gamma=3$ counterexample printed in `check_markov.py`).

**Non-vacuity.** The halfStep example with any $\gamma\in(0,1]$ (#86, #87).
**Junk values.** None: both sides are in $[0,\infty]$, and the right side may be $\infty$.
**Concerns.** None.

### 81. `lintegral_dist_levels_le` (theorem)

**Rendering.** Same hypotheses as #80 (with $x_0\in\alpha$), plus $N,N'\in\mathbb N$ with $N'\le N$. Write $X_n(\omega)=\mathrm{backIter}(\varphi,n,(\xi_k(\omega))_k,x_0)$, which uses the noise from index $0$. Then
$$\int^{-}\Big(d\big(X_N(\omega),X_{N'}(\omega)\big)^{2\gamma}\Big)^{+}\mu(d\omega)\le(\rho^{+})^{N'}\cdot\Big(\Big(\frac4{(1-\rho)^2}\Big)^{+}\int^{-}\big(d(x_0,\varphi(x_0,e))^{2\gamma}\big)^{+}\nu(de)\Big).$$

**Truth.** True: $X_N=\mathrm{backIter}(N',\xi,U)$ with $U=\mathrm{backIter}(N-N',(\xi_{k+N'}),x_0)$, which is measurable for $\mathrm{noiseFrom}(\xi,N')$ (#77). Then apply #79 and #80. Exact enumeration on the halfStep chain passes.
**Non-vacuity.** As #80.
**Junk values.** None.
**Concerns.** None.

### 82. `variance_levels_le` (theorem)

**Rendering.** Same hypotheses as #81, plus:
- **(hc)** $c:=\int^{-}(d(x_0,\varphi(x_0,e))^{2\gamma})^{+}\nu(de)<\infty$;
- $f:\alpha\to\mathbb R$ measurable with $\lvert f(x)-f(y)\rvert\le d(x,y)^\gamma$ for all $x,y$ ($\gamma$-Hölder with constant 1);
- $N'\le N$.

Then
$$\operatorname{Var}_\mu\big(f(X_N)-f(X_{N'})\big)\le\frac4{(1-\rho)^2}\cdot c_{\mathbb R}\cdot\rho^{N'},\qquad c_{\mathbb R}=\text{the real number }c.$$

**Truth.** True: $\operatorname{Var}\le\mathbb E Y^2\le\mathbb E\,d^{2\gamma}\le$ the right side of #81. Exact enumeration on the halfStep chain passes.
**Non-vacuity.** The halfStep chain with $\gamma=\tfrac12$ and $f=\lvert\cdot\rvert^{1/2}$ (or $f=0$).
**Junk values.** Converting $c$ to a real is meaningful only because of (hc); without it, $\infty\mapsto0$ would make the right side $0$. The Mathlib variance is the true variance here because the difference is in $L^2$.
**Concerns.** None.

### 83. `halfStep` (def)

**Rendering.** $\mathrm{halfStep}(x,e)=x/2+e$ for $x,e\in\mathbb R$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 84. `fairCoin` (def)

**Rendering.** $\mathrm{fairCoin}=\tfrac12\delta_0+\tfrac12\delta_1$, a probability measure on $\mathbb R$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 85. `uniform02` (def)

**Rendering.** $\mathrm{uniform02}=\tfrac12\,\mathrm{Leb}|_{(0,2]}$, the uniform probability law on $(0,2]$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 86. `lintegral_dist_halfStep` (theorem)

**Rendering.** For all $p,x,y\in\mathbb R$:
$$\int^{-}\Big(\big\lvert\mathrm{halfStep}(x,e)-\mathrm{halfStep}(y,e)\big\rvert^p\Big)^{+}\mathrm{fairCoin}(de)=\big((1/2)^p\big)^{+}\cdot\big(\lvert x-y\rvert^p\big)^{+}.$$

**Truth.** True: the distance is $\lvert x-y\rvert/2$ for both values of $e$, and $\mathrm{mul\_rpow}$ applies. It also holds for $p\le0$ under Lean's $0^p$ conventions (checked).
**Non-vacuity.** No hypotheses.
**Junk values.** For $p\le0$ and $x=y$, both sides follow the $0^0=1$ / $0^p=0$ conventions consistently.
**Concerns.** None.

### 87. `half_rpow_lt_one` (lemma)

**Rendering.** For every real $\gamma>0$: $\ (1/2)^{2\gamma}<1$.

**Truth.** True.
**Non-vacuity.** $\gamma=1$.
**Junk values.** None.
**Concerns.** None.

### 88. `halfStep_invariant` (theorem)

**Rendering.**
$$\tfrac12\,(x\mapsto x/2)_\#\,\mathrm{uniform02}+\tfrac12\,(x\mapsto x/2+1)_\#\,\mathrm{uniform02}=\mathrm{uniform02}.$$

**Truth.** True: $\tfrac12U(0,1]+\tfrac12U(1,2]=U(0,2]$ (CDF check).
**Non-vacuity.** No hypotheses.
**Junk values.** None (the maps are continuous).
**Concerns.** None.

### 89. `map_halfStep` (theorem)

**Rendering.** $\Omega$ has a σ-algebra and a probability measure $\mu$. Let $X,\xi:\Omega\to\mathbb R$ be measurable, with $\xi$ independent of $X$, $X_\#\mu=\mathrm{uniform02}$ and $\xi_\#\mu=\mathrm{fairCoin}$. Then $\big(\omega\mapsto X(\omega)/2+\xi(\omega)\big)_\#\mu=\mathrm{uniform02}$.

**Truth.** True (independence plus #88).
**Non-vacuity.** The product space $\mathrm{uniform02}\otimes\mathrm{fairCoin}$ with coordinate maps.
**Junk values.** None.
**Concerns.** None.

---

## Block 6 — auxiliary definitions ("definitions used above, from other modules", 9 declarations)

The packet shows these without their `variable` context: the implicit types $\iota,\Omega_0,\Omega$, the implicit $D$, and any instances. For `mimcEta`, the use of `univ_nonempty` requires a `Nonempty (Fin D)` instance (C23) from the hidden context. At $D=2$ (the only use, #45) one exists.

### 90. `optimalN` (def)

**Rendering.** For a finset $s\subseteq\iota$, $V,C:\iota\to\mathbb R$, $\tau\in\mathbb R$ and $i\in\iota$:
$$\mathrm{optimalN}(s,V,C,\tau)(i)=\big\lceil\mathrm{lagrangeN}(s,V,C,\tau)(i)\big\rceil_{+}=\Big\lceil\tau^{-1}\sqrt{V_i/C_i}\ \textstyle\sum_{j\in s}\sqrt{V_jC_j}\Big\rceil_{+}\in\mathbb N .$$

**Truth / Non-vacuity.** Not applicable.
**Junk values.** $\tau=0$ gives $\tau^{-1}=0$ and hence $N=0$. $C_i=0$ gives $V_i/0=0$. A negative radicand gives $\sqrt{\cdot}=0$. A nonpositive value gives ceiling $0$ (C9–C11).
**Concerns.** None in context (#34 has positive data).

### 91. `levelDiff` (def)

**Rendering.** For $P:\mathbb N\to\Omega_0\to\mathbb R$: $\ \mathrm{levelDiff}(P)(0)=P_0$ and $\mathrm{levelDiff}(P)(\ell+1)=P_{\ell+1}-P_\ell$ (pointwise).

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 92. `complexityBound` (def)

**Rendering.** For $\alpha,\beta,\gamma,\varepsilon\in\mathbb R$: $\varepsilon^{-2}$ if $\gamma<\beta$; otherwise $\varepsilon^{-2}(\log\varepsilon)^2$ if $\beta=\gamma$; otherwise $\varepsilon^{-2-(\gamma-\beta)/\alpha}$. All are real powers.

**Truth / Non-vacuity.** Not applicable.
**Junk values.**
- $\alpha=0$ gives $(\gamma-\beta)/0=0$.
- $\varepsilon=0$ gives $0^{-2}=0$ and $\log0=0$.
- $\varepsilon<0$ puts a $\cos(\pi y)$ factor in the third branch (C7, C8, C11).
**Concerns.** None for the definition itself; it is only evaluated (#13, #33, #44).

### 93. `totalCost` (def)

**Rendering.** $\mathrm{totalCost}(\mathrm{cost},L,N)(x)=\sum_{\ell=0}^{L}\sum_{n=0}^{N_\ell-1}\mathrm{cost}_{\ell,n}(x)$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** None.
**Concerns.** None.

### 94. `blockMean` (def)

**Rendering.** For $f:\iota\to\Omega_0\to\mathbb R$, $\omega:\iota\times\mathbb N\to\Omega\to\Omega_0$, $i\in\iota$, $N\in\mathbb N$ and $x\in\Omega$:
$$\mathrm{blockMean}(f,\omega,i,N)(x)=N^{-1}\sum_{n<N}f_i\big(\omega_{(i,n)}(x)\big).$$

**Truth / Non-vacuity.** Not applicable.
**Junk values.** $N=0$ gives $0$ (C11).
**Concerns.** None (#74 and #75 require $N_\ell\ge1$).

### 95. `mimcEta` (def)

**Rendering.** For $\alpha,\beta,\gamma:\{0,\dots,D-1\}\to\mathbb R$: $\ \mathrm{mimcEta}(\alpha,\beta,\gamma)=\max_{d<D}\,(\gamma_d-\beta_d)/\alpha_d$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** $\alpha_d=0$ gives the quotient $0$.
**Concerns.** It needs $D\ge1$ through a hidden instance (see the block header).

### 96. `mimcBound` (def)

**Rendering.** For $\eta,e_1,e_2,\varepsilon\in\mathbb R$: $\varepsilon^{-2}$ if $\eta<0$; $\varepsilon^{-2}\lvert\log\varepsilon\rvert^{e_1}$ if $\eta=0$; $\varepsilon^{-2-\eta}\lvert\log\varepsilon\rvert^{e_2}$ if $\eta>0$. All are real powers.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** At $\varepsilon\in\{0,\pm1\}$, $\lvert\log\varepsilon\rvert=0$, so $0^{e}$ follows the C7 conventions. $\varepsilon\le0$ follows the rpow/log conventions.
**Concerns.** None for the definition.

### 97. `lagrangeN` (def)

**Rendering.** $\mathrm{lagrangeN}(s,V,C,\tau)(i)=\tau^{-1}\sqrt{V_i/C_i}\cdot\mathrm{sumSqrtVC}(s,V,C)$, a real number.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** As #90.
**Concerns.** None.

### 98. `sumSqrtVC` (def)

**Rendering.** $\mathrm{sumSqrtVC}(s,V,C)=\sum_{i\in s}\sqrt{V_iC_i}$.

**Truth / Non-vacuity.** Not applicable.
**Junk values.** $\sqrt{\cdot}=0$ for negative products.
**Concerns.** None.

---

## Summary

- **False statements:** none. All 67 theorems/lemmas are judged true. Numerical checks agree, including sharpness of the constants in #1, #2, #34 and #80.
- **Vacuous statements:** none. Every hypothesis set has an explicit witness above.
- **Junk-dependent in a way that changes meaning:** none. The following junk dependencies are harmless but worth knowing:
  - #1/#2: the bias bound holds via the 0-integral convention when $P$ is non-measurable.
  - #31/#32: $0=0$ for non-integrable $\Phi$.
  - #11: `deriv`$=0$ at non-differentiable points.
  - #55/#56: the zero measure for non-probability $\rho$.
  - #59/#72/#73: inner-integral junk on a null set.
  - #79: degenerate $p\le0$ and $\rho<0$ conventions.
  - #13/#33/#44/#45: stated for all real $\varepsilon$, including $\varepsilon\le0$.
  - #90/#92/#94–#96: division-by-zero and ceiling conventions in the definitions.
- **Otherwise concerning (the content is weaker than it may look):**
  - #13 `pde_complexity`, #33 `tauLeaping_complexity`, #44 `nested_complexity`, #45 `nested_mimc_complexity`: pure evaluations of case-defined formulas, with no probabilistic, error or cost content. In #45, $e_1,e_2$ are unused.
  - #5 `heatStep_sub` ($w$ cancels), #8/#9 (arithmetic identities) and #12 (constant-$b$ only) are elementary identities.
  - #74/#75: only $\varepsilon\in(0,e^{-1})$ is covered; $c_4$ may depend on all problem data; the costs in #74 are constrained only through upper bounds on their means; $c_3>0$ is superfluous.
  - Superfluous (harmless) hypotheses: $M>0$ in #67 and #71.
  - #21 asserts only the marginal laws, not the joint law.
