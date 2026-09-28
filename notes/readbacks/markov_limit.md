# Blind read-back audit: packet H (`MlmcLean.MarkovLimit`)

| | |
|---|---|
| Date | 2026-09-28 |
| Packet | `readback/round7/packet_H_markov_limit.lean` (module `MlmcLean.MarkovLimit`, plus `backIter` appended from `MlmcLean.MarkovChain`) |
| Declarations audited | **7**: 4 definitions (`fwdIter`, `revFun`, `revPerm`, `backIter`) and 3 theorems (`map_backIter_eq_map_fwdIter`, `ae_tendsto_backIter`, `tendstoInDistribution_fwdIter`) |
| Auditor | independent blind auditor (sub-agent), fresh context |
| Numerical work | `readback/round7/work_H/`: `common.py` plus 5 scripts, with outputs in `out_*.txt` |

## Summary

- **Verdict.** There are 7 declarations: 4 definitions and 3 theorems. **No theorem is false, none is vacuous, and none holds only because of a Lean junk value.** A proof sketch for each theorem is given below. Exact rational-arithmetic checks and Monte Carlo checks on four concrete chains agree with every statement. Negative controls confirm that the key hypotheses are needed.
- **What the theorems literally say.** Write $f_c := \varphi(\cdot, c)$.
  - **T1** (`map_backIter_eq_map_fwdIter`). Take i.i.d. noise and a fixed $n$. The composition $f_{\xi_0}\circ\cdots\circ f_{\xi_{n-1}}(x_0)$ has the same law as the composition in the opposite order, $f_{\xi_{n-1}}\circ\cdots\circ f_{\xi_0}(x_0)$. The theorem covers only the **one-time marginal at each fixed $n$**. The joint laws at several times differ: in the exact checks, the total variation (TV) distance between the laws of the pairs at times $(3,4)$ reaches 0.55.
  - **T2** (`ae_tendsto_backIter`). Assume $\int d(\varphi(x,c),\varphi(y,c))^p\,\nu(dc)\le\rho\,d(x,y)^p$ for all $x,y$, with $0<p$ and $0\le\rho<1$, and assume a finite $p$-th moment of $d(x_0,\varphi(x_0,\cdot))$. Then the backward compositions $f_{\xi_0}\circ\cdots\circ f_{\xi_{n-1}}(x_0)$ converge for almost every $\omega$, to a limit that depends on $\omega$.
  - **T3** (`tendstoInDistribution_fwdIter`). Under the same hypotheses there is an a.e.-measurable $X$ such that the backward compositions converge to $X$ almost surely, and the forward chain converges to $X$ in distribution. Here "in distribution" is Mathlib's `TendstoInDistribution`: a.e.-measurability plus weak convergence of the laws.
- **Main points for a human auditor.**
  1. **Not asserted anywhere:**
     - that $\mathrm{law}(X)$ is invariant (stationary) for the chain, or unique;
     - that $\mathrm{law}(X)$ does not depend on $x_0$;
     - any rate of convergence;
     - almost-sure convergence of the forward chain. This is false in general: 91% of simulated paths of $X_{n+1}=X_n/2+\xi_n$ still move by more than 0.1 at step 60.
  2. **Form of the contraction hypothesis `hφ`.**
     - $\rho$ multiplies $d^p$, so the contraction factor on the metric scale is $\rho^{1/p}$.
     - It must hold for **all** pairs $x,y$ (it is global).
     - It holds on average over **one** noise draw and for **one** fixed $p$.
     - It allows some individual maps to expand. Tested with $\varphi(x,c)=cx+1$, $c\in\{0.1,1.8\}$: it holds for $p=1$ with $\rho=0.95$ but fails for $p=2$.
  3. **Redundant hypotheses (harmless):**
     - `[IsProbabilityMeasure μ]` follows from `hξ` (Mathlib `iIndepFun.isProbabilityMeasure`). It is still needed syntactically in T3, where `TendstoInDistribution` requires it.
     - `hρ0 : 0 ≤ ρ` is not needed for truth: a negative $\rho$ has `ENNReal.ofReal ρ = 0`, which is the $\rho=0$ case.
     - The measure $\nu$ is not free: `hlaw` forces it to be the common law of the $\xi_i$, a probability measure.
     - T2 follows directly from T3.
     - The first conjunct of T3 repeats a field of `TendstoInDistribution`.
  4. **Load-bearing hypotheses** (each backed by a counterexample or numerical control):
     - `hp : 0 < p`. With $p<0$, Lean's convention $0^{p}=0$ lets the *expanding* map $x\mapsto 2x$ satisfy `hφ`. With $p=0$ the hypotheses contradict each other.
     - `hρ1 : ρ < 1`.
     - `hc` (heavy-tailed noise gives a counterexample).
     - `CompleteSpace α` ($\mathbb Q$ gives a counterexample).
     - `hξ` and `hlaw` for T1. Exact counterexamples when either is dropped give TV 0.70 and 0.53.
  5. **Scope.** T2 and T3 automatically include the section instances `[BorelSpace α]` and `[SecondCountableTopology α]`, and add `[CompleteSpace α]`. They therefore apply only to complete, separable metric spaces with the Borel σ-algebra.
  6. **Unused definitions.** `revFun` and `revPerm` appear in no theorem statement. `revPerm` uses a lemma `revFun_involutive` that is not in the packet. Its type is forced to be "$r_n\circ r_n=\mathrm{id}$", which is true (checked for $n<40$, $i<90$).

## Rules followed

- **Files read:** only the packet, `references/mission_auditor.md`, and Mathlib sources under `.lake/packages/mathlib/Mathlib`, the latter only to confirm the meaning of Mathlib definitions.
- **Files not read:** no project sources, `docs/`, `notes/`, README, PLAN, `prove2me/`, `scripts/`, git history, other packets or their outputs, papers or web pages.
- **Names:** declaration names and file names were not used to infer meaning.
- **Lean:** not run. Elaboration (implicit arguments, which section variables are included, notation) was read from the source.
- **Renderings:** literal, with no judgement. Every binder, hypothesis and instance argument is listed, packet definitions are unfolded inline, and the exact strength of every relation and the order of quantifiers are kept.
- **Judgement** is given separately for each theorem, under Truth / Non-vacuity / Junk values / Concerns.
- **Section-variable inclusion (Lean 4 rule).** A section `variable` is part of a theorem if the statement mentions it. An instance-implicit section variable is also included whenever every variable it mentions is included. Mathlib's `omit [...] in` idiom exists to remove such auto-included instances; see `MeasureTheory/Function/LpSeminorm/Count.lean:37` (variable declared at `:17`) and `linter.unusedSectionVars` (`RingTheory/Unramified/Basic.lean:313`). The packet contains no `omit` or `include`. Hence:
  - T1 carries `[MeasurableSpace E] [MeasurableSpace α] [MeasurableSpace Ω] [IsProbabilityMeasure μ]`.
  - T2 and T3 carry `[MetricSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] [MeasurableSpace E] [MeasurableSpace Ω] [IsProbabilityMeasure μ]`, plus their own `[CompleteSpace α]`.

## Mathlib conventions confirmed

Paths are relative to `.lake/packages/mathlib/Mathlib/`.

| Notion in the packet | Where (file:line) | Convention confirmed |
|---|---|---|
| `Measure.map f μ` | `MeasureTheory/Measure/Map.lean:91-93`, `:112` (`map_of_not_aemeasurable`) | Pushforward if `f` is μ-a.e.-measurable (`AEMeasurable`); **the zero measure otherwise** (junk value). |
| `map_const` | `MeasureTheory/Measure/Dirac.lean:91` | `μ.map (fun _ => c) = μ univ • dirac c`. For $n=0$ in T1, both sides are $\delta_{x_0}$. |
| `Measure.isProbabilityMeasure_map` | `MeasureTheory/Measure/Typeclasses/Probability.lean:124` | A pushforward of a probability measure along an a.e.-measurable map is a probability measure. |
| `IsProbabilityMeasure μ` | `MeasureTheory/Measure/Typeclasses/Probability.lean:64-65` | `μ univ = 1`. |
| `ENNReal.ofReal r` | `Data/ENNReal/Basic.lean:230`; `Real.toNNReal` at `Data/NNReal/Defs.lean:155-156` | $\max(r,0)$ in $[0,\infty]$. **A negative input gives 0** (junk value). |
| `x ^ y` for `x y : ℝ` (`Real.rpow`) | `Analysis/SpecialFunctions/Pow/Real.lean:35-38` (definition and `Pow ℝ ℝ` instance) | Real part of the complex power. |
| `rpow_def_of_nonneg` | same file `:45` | For $x\ge 0$: $x^y = $ (if $x=0$ then (if $y=0$ then 1 else 0) else $e^{y\log x}$). |
| `zero_rpow`, `rpow_zero` | same file `:128`, `:120` | $0^y=0$ for every $y\neq0$, **including $y<0$** (junk value; the true value would be $+\infty$). $x^0=1$ for every $x$, including $0^0=1$. |
| `rpow_def_of_neg` | same file `:95` | For $x<0$: $x^y=e^{y\log x}\cos(y\pi)$ (junk value). Never reached here, since every base in the packet is a distance, hence $\ge 0$. |
| `lintegral` (`∫⁻`) | `MeasureTheory/Integral/Lebesgue/Basic.lean:48-49` | Supremum of the integrals of measurable simple functions lying below `f`. Defined for every `f`, measurable or not. |
| `ae`, `∀ᵐ ω ∂μ, P ω` | `MeasureTheory/OuterMeasure/AE.lean:49`, `:57` (notation), `:80` (`ae_iff`) | $\mu\{\omega:\neg P(\omega)\}=0$, with μ applied as an outer measure (the set need not be measurable). |
| `AEMeasurable f μ` | `MeasureTheory/Measure/MeasureSpaceDef.lean:409-410` | There is a measurable $g$ with $f=g$ μ-a.e. |
| `Measurable` | `MeasureTheory/MeasurableSpace/Defs.lean:493-494` | Preimages of measurable sets are measurable. |
| σ-algebra on `α × E` | `MeasureTheory/MeasurableSpace/Constructions.lean:372-378` | Product σ-algebra `comap fst ⊔ comap snd`, generated by the two projections. |
| `iIndepFun ξ μ` | `Probability/Independence/Basic.lean:136-138` → `Kernel/IndepFun.lean:47-50` → `Kernel/Indep.lean:81-83`, `:68-71` | Defined through the constant kernel and `dirac ()`. |
| `iIndepFun_iff_measure_inter_preimage_eq_mul` | `Probability/Independence/Basic.lean:654-660` | Equivalent to: for every finite $S\subset\mathbb N$ and measurable $B_i$, $\mu(\bigcap_{i\in S}\xi_i^{-1}B_i)=\prod_{i\in S}\mu(\xi_i^{-1}B_i)$. |
| `iIndepFun.isProbabilityMeasure` | `Probability/Independence/Basic.lean:790-791` | **`iIndepFun f μ` implies `IsProbabilityMeasure μ`** (take $S=\emptyset$). |
| `iIndepFun.map_fun_eq_infinitePi_map₀` | `Probability/Independence/InfinitePi.lean:43-45` | Joint law of an independent family = infinite product of the marginal laws. |
| `Measure.infinitePi`, `infinitePi_map_eval`, `iIndepFun_infinitePi` | `Probability/ProductMeasure.lean:358`, `:381`, `:481`; `Probability/Independence/InfinitePi.lean:127` | Used for the non-vacuity witness: the coordinates of $\nu^{\otimes\mathbb N}$ are independent, each with law $\nu$. |
| `TendstoInDistribution X l Z μ μ'` | `MeasureTheory/Function/ConvergenceInDistribution.lean:64-71` (`[TopologicalSpace E]` from `:59`) | A structure. Instance arguments: `[OpensMeasurableSpace E]`, `[∀ i, IsProbabilityMeasure (μ i)]`, `[IsProbabilityMeasure μ']`. Fields: (1) `∀ i, AEMeasurable (X i) (μ i)`; (2) `AEMeasurable Z μ'`; (3) the laws `⟨(μ n).map (X n), _⟩` tend to `⟨μ'.map Z, _⟩` along `l` in the topology of `ProbabilityMeasure E`. |
| `tendstoInDistribution_of_ae_tendsto` | same file `:137-142` | Almost-sure convergence implies convergence in distribution. |
| Topology of `ProbabilityMeasure` | `MeasureTheory/Measure/ProbabilityMeasure.lean:289-290` (induced from `FiniteMeasure`); `MeasureTheory/Measure/FiniteMeasure.lean:505-506`, `:393`, `:499-500` | Weak convergence: tested against bounded continuous $f:\alpha\to[0,\infty)$ via $\int f\,d\mu$. |
| `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` | `MeasureTheory/Measure/ProbabilityMeasure.lean:346-351` | Equivalent: $\int f\,d\mu_n\to\int f\,d\mu$ for every bounded continuous real $f$. |
| `BorelSpace`, `OpensMeasurableSpace` | `MeasureTheory/Constructions/BorelSpace/Basic.lean:113-115`, `:107-109` | Measurable sets = Borel sets, respectively Borel ⊆ measurable. |
| `Prod.borelSpace` | same file `:656-658` | Borel(α × β) = product σ-algebra, provided one factor is second countable. |
| `measurable_dist` | `MeasureTheory/Constructions/BorelSpace/Metric.lean:73`, under `[SecondCountableTopology α]` at `:71` | The distance is measurable on `α × α`. |
| `aemeasurable_of_tendsto_metrizable_ae'` | `MeasureTheory/Constructions/BorelSpace/Metrizable.lean:79-82` | An a.e. limit of a.e.-measurable maps into a metrizable Borel space is a.e.-measurable. |
| `Function.Involutive f` | `Logic/Function/Basic.lean:1010-1011` | $\forall x,\ f(f(x))=x$. |
| `Function.Involutive.toPerm f h` | `Logic/Equiv/Basic.lean:774-775` | The permutation `⟨f, f, h.leftInverse, h.rightInverse⟩`: forward map = inverse map = $f$. |
| ℕ subtraction (Lean core, not Mathlib) | none | Truncated: $a-b=0$ when $b\ge a$. |

## Notation used in all renderings

- $\varphi(x,c)$ denotes `φ x c`, and $f_c:=\varphi(\cdot,c):\alpha\to\alpha$ for $c\in E$.
- $\xi_k(\omega)$ denotes `ξ k ω`, and $\xi(\omega):=(\xi_k(\omega))_{k\in\mathbb N}\in E^{\mathbb N}$ (the sequence `fun k => ξ k ω`).
- **Pushforward.** $g_{\#}\mu$ denotes Mathlib's `μ.map g`. It equals $B\mapsto\mu(g^{-1}B)$ on measurable $B$ when $g$ is μ-a.e.-measurable, and the zero measure otherwise.
- **Positive part.** $\mathrm{ofReal}(r):=\max(r,0)\in[0,\infty]$.
- **Real powers.** $t^p$ for $t\ge0$, $p\in\mathbb R$ is Mathlib's real power: $e^{p\log t}$ for $t>0$, $0^p=0$ for $p\ne0$, and $0^0=1$.
- **Integrals.** $\int_E h(c)\,\nu(\mathrm dc)\in[0,\infty]$ for $h:E\to[0,\infty]$ is the lower Lebesgue integral `∫⁻`.
- **Almost everywhere.** "For μ-a.e. $\omega$, $P(\omega)$" means $\mu\{\omega:\neg P(\omega)\}=0$.
- **A.e.-measurable.** "μ-a.e.-measurable" means equal μ-a.e. to a measurable map.
- **Mutual independence.** "$(\xi_i)_{i\in\mathbb N}$ mutually independent under μ" means: for every finite $S\subset\mathbb N$ and every family of measurable $B_i\subseteq E$ ($i\in S$),
$$\mu\Big(\bigcap_{i\in S}\xi_i^{-1}(B_i)\Big)=\prod_{i\in S}\mu\big(\xi_i^{-1}(B_i)\big).$$
  For $S=\emptyset$ this reads $\mu(\Omega)=1$.

---

## D1. `fwdIter` (definition)

**Rendering.** Let $\alpha$ and $E$ be arbitrary types (implicit section variables; no structure is assumed on them). Given an explicit function $\varphi:\alpha\to E\to\alpha$, `fwdIter φ` is the map $(n,e,x)\mapsto \mathrm{fwd}^{\varphi}_n(e,x)$ from $\mathbb N\times E^{\mathbb N}\times\alpha$ to $\alpha$, defined by recursion on $n$:
$$\mathrm{fwd}^{\varphi}_0(e,x)=x,\qquad \mathrm{fwd}^{\varphi}_{n+1}(e,x)=\varphi\big(\mathrm{fwd}^{\varphi}_n(e,x),\,e_n\big).$$
Unfolded:
$$\mathrm{fwd}^{\varphi}_n(e,x)=f_{e_{n-1}}\circ\cdots\circ f_{e_1}\circ f_{e_0}(x).$$
- The map $f_{e_0}$ is applied first.
- Only $e_0,\dots,e_{n-1}$ are read.
- For $n=0$ the value is $x$; for $n=1$ it is $\varphi(x,e_0)$.
- The Lean argument order is `fwdIter φ n e x`.

## D2. `revFun` (definition)

**Rendering.** For natural numbers $n,i$:
$$r_n(i)=\begin{cases}n-1-i, & i<n,\\ i, & i\ge n,\end{cases}$$
where $-$ is truncated natural-number subtraction ($a-b=0$ if $b\ge a$).
- When $i<n$ we have $n\ge1$ and $i\le n-1$, so $n-1-i$ is the ordinary difference.
- So $r_n$ sends $\{0,\dots,n-1\}$ to itself by $i\mapsto n-1-i$ and fixes every $i\ge n$.
- For $n=0$, $r_0$ is the identity of $\mathbb N$.
- No section variables are used.

## D3. `revPerm` (definition)

**Rendering.** For $n\in\mathbb N$, `revPerm n` is the permutation of $\mathbb N$ (a bijection packaged with its inverse) whose forward map and inverse map are both $r_n$ from D2.
- It is built by `Function.Involutive.toPerm` from a proof, called `revFun_involutive n`, of the statement "$r_n(r_n(i))=i$ for every $i\in\mathbb N$".
- That proof is not displayed in the packet. Its type is forced by the signature of `toPerm`.
- The permutation does not depend on how that proof goes.
- No section variables are used.

## D4. `backIter` (definition, from `MlmcLean.MarkovChain`)

**Rendering.** For arbitrary types $\alpha,E$ (implicit) and an explicit function $\varphi:\alpha\to E\to\alpha$, `backIter φ` is the map $(n,e,x)\mapsto\mathrm{back}^{\varphi}_n(e,x)$ from $\mathbb N\times E^{\mathbb N}\times\alpha$ to $\alpha$, defined by
$$\mathrm{back}^{\varphi}_0(e,x)=x,\qquad \mathrm{back}^{\varphi}_{n+1}(e,x)=\varphi\big(\mathrm{back}^{\varphi}_n(\sigma e,x),\,e_0\big),\qquad(\sigma e)_k:=e_{k+1}.$$
Unfolded:
$$\mathrm{back}^{\varphi}_n(e,x)=f_{e_0}\circ f_{e_1}\circ\cdots\circ f_{e_{n-1}}(x).$$
- These are the same maps as in D1, composed in the opposite order: $f_{e_{n-1}}$ is applied first and $f_{e_0}$ last.
- Only $e_0,\dots,e_{n-1}$ are read.
- For $n=0$ the value is $x$; for $n=1$ it is $\varphi(x,e_0)$.

*Remarks on D1–D4 (not part of the renderings):*
- `check_defs.py` confirms, for these clause-by-clause transcriptions:
  - the composition order (e.g. $n=3$: forward `f2(f1(f0(x)))`, backward `f0(f1(f2(x)))`);
  - that $r_n$ is an involution which reverses $\{0,\dots,n-1\}$, fixes the tail and never truncates (0 violations for $n<40$, $i<90$);
  - the identity $\mathrm{back}^{\varphi}_n(e,x)=\mathrm{fwd}^{\varphi}_n(e\circ r_n,x)$ (0 mismatches in 600 exact and floating-point cases).
- That identity is the link between `revPerm` and the two iterations. It is **not** stated in the packet.

---

## T1. `map_backIter_eq_map_fwdIter`

**Rendering.**

*Setting.*
- Types $\alpha$, $E$, $\Omega$, each carrying a σ-algebra. No topology or metric is assumed on $\alpha$ or $E$.
- A measure $\mu$ on $\Omega$ with $\mu(\Omega)=1$ (instance `IsProbabilityMeasure μ`).
- A measure $\nu$ on $E$.
- A function $\varphi:\alpha\to E\to\alpha$ and a family $\xi=(\xi_i)_{i\in\mathbb N}$ of functions $\xi_i:\Omega\to E$.

All of these are implicit or instance arguments coming from the section.

*Hypotheses.*
- **(hφm)** The map $\alpha\times E\to\alpha$, $(x,c)\mapsto\varphi(x,c)$, is measurable, where $\alpha\times E$ carries the product σ-algebra generated by the two coordinate projections.
- **(hξ)** $(\xi_i)_{i\in\mathbb N}$ are mutually independent under $\mu$, in the sense given in the notation section.
- **(hξm)** Every $\xi_i$ is measurable.
- **(hlaw)** $\xi_{i\#}\mu=\nu$ for every $i\in\mathbb N$.

*Conclusion.* For every $n\in\mathbb N$ and every $x_0\in\alpha$ (explicit arguments, bound after the hypotheses):
$$\big(\omega\mapsto \mathrm{back}^{\varphi}_n(\xi(\omega),x_0)\big)_{\#}\mu \;=\; \big(\omega\mapsto \mathrm{fwd}^{\varphi}_n(\xi(\omega),x_0)\big)_{\#}\mu \qquad\text{(equality of measures on }\alpha\text{)}.$$
Unfolded: the pushforward of $\mu$ under
$$\omega\mapsto f_{\xi_0(\omega)}\circ f_{\xi_1(\omega)}\circ\cdots\circ f_{\xi_{n-1}(\omega)}(x_0)$$
equals the pushforward of $\mu$ under
$$\omega\mapsto f_{\xi_{n-1}(\omega)}\circ\cdots\circ f_{\xi_1(\omega)}\circ f_{\xi_0(\omega)}(x_0).$$
Here "pushforward" follows Mathlib's convention: the zero measure if the map is not μ-a.e.-measurable. The statement includes $n=0$ and $n=1$.

**Truth: true.** Proof sketch:
1. **Measurability.** By induction on $n$ (for `backIter`, generalising over the family, since the recursion shifts it), the maps $\omega\mapsto\mathrm{fwd}^{\varphi}_n(\xi(\omega),x_0)$ and $\omega\mapsto\mathrm{back}^{\varphi}_n(\xi(\omega),x_0)$ are measurable. Each step composes the measurable map $(x,c)\mapsto\varphi(x,c)$ (hφm) with a measurable pairing (hξm).
2. **Factorisation.** Let $V=(\xi_0,\dots,\xi_{n-1}):\Omega\to E^n$. Let $G(c_0,\dots,c_{n-1})=f_{c_{n-1}}\circ\cdots\circ f_{c_0}(x_0)$, which is measurable, and let $R$ be the coordinate reversal. Then the forward map is $G\circ V$ and the backward map is $G\circ R\circ V$; this is the identity $\mathrm{back}_n(e,\cdot)=\mathrm{fwd}_n(e\circ r_n,\cdot)$.
3. **Joint law.** By hξ, hξm and hlaw, $V_{\#}\mu$ and $\nu^{\otimes n}$ agree on measurable rectangles, both taking the value $\prod_i\nu(B_i)$. Rectangles form a π-system generating the product σ-algebra, and both measures are probability measures, so $V_{\#}\mu=\nu^{\otimes n}$. This product measure is invariant under $R$.
4. **Conclusion.** Hence $(G\circ R\circ V)_{\#}\mu=G_{\#}R_{\#}\nu^{\otimes n}=G_{\#}\nu^{\otimes n}=(G\circ V)_{\#}\mu$.

For $n=0$ both sides equal $\delta_{x_0}$ (`map_const`, with $\mu(\Omega)=1$). For $n=1$ the two maps coincide.

**Non-vacuity: satisfiable with non-trivial data.**
- Take $\alpha=E=\mathbb R$ with Borel σ-algebras and $\nu=$ the uniform law on $[-1,1]$.
- Take $\Omega=\mathbb R^{\mathbb N}$ with $\mu=$ `Measure.infinitePi (fun _ => ν)`, which is a probability measure, and $\xi_i(\omega)=\omega_i$.
- hξ holds by `iIndepFun_infinitePi` (with the identity maps), hlaw by `infinitePi_map_eval`, and hξm because coordinate projections are measurable.
- For $\varphi(x,c)=x/2+c$, hφm holds because $\varphi$ is continuous and Borel$(\mathbb R^2)$ is the product σ-algebra.
- For $n\ge2$ the two sides come from *different* functions of $\omega$, so the equality is not trivial pathwise. For example, at $n=2$ the functions are $x_0/4+\xi_0/2+\xi_1$ and $x_0/4+\xi_1/2+\xi_0$.
- In the exact finite-state checks, 360 of the 480 cases have forward ≠ backward as functions of the noise, and the laws are still exactly equal.

**Junk values: none.**
- Both maps are measurable (hφm, hξm), so both sides are genuine pushforwards and probability measures (`isProbabilityMeasure_map`). The equality is not "0 = 0".
- The only natural-number subtraction (in `revFun`) is not part of the statement.

**Concerns.**
- **Marginals only.** The statement is about the **one-time marginal law at each fixed $n$**. It says nothing about the laws of the processes $(\mathrm{back}_n)_n$ and $(\mathrm{fwd}_n)_n$, which differ. For example, the exact TV between the joint laws of the pairs at times 3 and 4 reaches 0.5525.
- **Redundant instance.** `[IsProbabilityMeasure μ]` (auto-included) is implied by hξ (`iIndepFun.isProbabilityMeasure`).
- **ν is fixed.** hlaw forces $\nu=\xi_{0\#}\mu$, so $\nu$ is automatically a probability measure.
- **hξ and hlaw are both needed.** Exact counterexamples when either is dropped:
  - Stationary, non-reversible Markov noise with uniform marginals (identically distributed but dependent): TV up to 0.70 at $n=2$.
  - Independent noise with $\xi_0\sim\nu$ and $\xi_k\sim\nu'\ne\nu$ for $k\ge1$: TV up to 0.53.
- **Role of hφm.** Only measurable structure is assumed on $\alpha$. hφm is what rules out the degenerate reading "0 = 0" of `Measure.map`.

---

## T2. `ae_tendsto_backIter`

**Rendering.**

*Setting.*
- $\alpha$ is a type with a metric $d$ (`MetricSpace α`) and a σ-algebra equal to the Borel σ-algebra of the metric topology (`MeasurableSpace α`, `BorelSpace α`).
- The metric topology is second countable (`SecondCountableTopology α`).
- $(\alpha,d)$ is complete (`CompleteSpace α`, an instance argument of the theorem itself).
- $E$ and $\Omega$ are types with σ-algebras.
- $\mu$ is a measure on $\Omega$ with $\mu(\Omega)=1$, and $\nu$ is a measure on $E$.
- $\varphi:\alpha\to E\to\alpha$, and $\xi=(\xi_i)_{i\in\mathbb N}$ with $\xi_i:\Omega\to E$.

*Hypotheses.*
- **(hφm)** $(x,c)\mapsto\varphi(x,c)$ is measurable from $\alpha\times E$, with the product of the Borel σ-algebra of $\alpha$ and the σ-algebra of $E$, to $\alpha$ with its Borel σ-algebra.
- **Parameters.** Real numbers $p$ and $\rho$ (implicit) with **(hp)** $0<p$, **(hρ0)** $0\le\rho$ and **(hρ1)** $\rho<1$.
- **(hφ)** For all $x,y\in\alpha$, in $[0,\infty]$:
$$\int_E \mathrm{ofReal}\big(d(\varphi(x,c),\varphi(y,c))^{p}\big)\,\nu(\mathrm dc)\;\le\;\mathrm{ofReal}(\rho)\cdot\mathrm{ofReal}\big(d(x,y)^{p}\big).$$
  Because $d\ge0$, $p>0$ and $\rho\ge0$, this reads $\int_E d(\varphi(x,c),\varphi(y,c))^p\,\nu(\mathrm dc)\le\rho\,d(x,y)^p$ with ordinary powers.
- **(hξ)** $(\xi_i)$ mutually independent under $\mu$; **(hξm)** every $\xi_i$ measurable; **(hlaw)** $\xi_{i\#}\mu=\nu$ for all $i$.
- **Starting point.** A point $x_0\in\alpha$ (explicit).
- **(hc)** $\displaystyle\int_E \mathrm{ofReal}\big(d(x_0,\varphi(x_0,c))^{p}\big)\,\nu(\mathrm dc)\neq\infty$, that is, $\int_E d(x_0,\varphi(x_0,c))^p\,\nu(\mathrm dc)<\infty$.

*Conclusion.* For μ-almost every $\omega\in\Omega$ there exists a point $x\in\alpha$, chosen after $\omega$ and so allowed to depend on it, such that
$$\mathrm{back}^{\varphi}_n(\xi(\omega),x_0)=f_{\xi_0(\omega)}\circ f_{\xi_1(\omega)}\circ\cdots\circ f_{\xi_{n-1}(\omega)}(x_0)\;\xrightarrow[n\to\infty]{}\;x$$
in the metric topology of $\alpha$. Equivalently, the set of $\omega$ for which the sequence has no limit in $\alpha$ has $\mu$-measure 0.

**Truth: true.** This is the classical backward-iteration argument.
1. **Setup.** Let $Y_n(\omega):=\mathrm{back}^{\varphi}_n(\xi(\omega),x_0)$ and $C:=\int d(x_0,\varphi(x_0,c))^p\,\nu(\mathrm dc)<\infty$ (hc). Since $\mathrm{back}_{n+1}(e,x_0)=\mathrm{back}_n(e,\varphi(x_0,e_n))$, the points $Y_{n+1}$ and $Y_n$ come from applying the same composition $f_{\xi_0}\circ\cdots\circ f_{\xi_{n-1}}$ to the two points $A=\varphi(x_0,\xi_n)$ and $B=x_0$.
2. **Peeling one map at a time.** Remove the outer maps one by one. At stage $k$ the current pair is a function of $\xi_{k+1},\dots,\xi_n$, hence independent of $\xi_k$. By Tonelli and hφ,
$$\mathbb E\,d(\varphi(A,\xi_k),\varphi(B,\xi_k))^p\le\rho\,\mathbb E\,d(A,B)^p.$$
   The integrand $(a,b,c)\mapsto d(\varphi(a,c),\varphi(b,c))^p$ is measurable because of `BorelSpace`, `SecondCountableTopology`, `Prod.borelSpace` and `measurable_dist`.
3. **Geometric bound.** Therefore $\mathbb E\,d(Y_{n+1},Y_n)^p\le\rho^n C$.
4. **Borel–Cantelli.** Pick $r$ with $\rho^{1/p}<r<1$; this is possible because $0\le\rho<1$ and $p>0$. By Markov's inequality, $\mu(d(Y_{n+1},Y_n)>r^n)\le C(\rho/r^p)^n$, which is summable. Borel–Cantelli then gives, almost surely, $d(Y_{n+1},Y_n)\le r^n$ for all large $n$.
5. **Completeness.** So $(Y_n)$ is almost surely Cauchy, and it converges because $\alpha$ is complete.

**Non-vacuity: satisfiable with non-trivial data.**
- **Contracting instance.** Take $\alpha=\mathbb R$ (complete, separable, Borel), $E=\mathbb R$, $\nu=U[-1,1]$, and $\Omega,\mu,\xi$ as in T1. Let $\varphi(x,c)=x/2+c$, $p=1$, $\rho=1/2$. Then hφ holds with equality, because the noise cancels, and hc holds: $\int|x_0/2-c|\,\nu(\mathrm dc)<\infty$. The choice $p=2$, $\rho=1/4$ also works.
- **Contracting only on average.** Take $\varphi(x,c)=cx+1$, $\nu=\tfrac12\delta_{0.1}+\tfrac12\delta_{1.8}$, $p=1$, $\rho=0.95$. Here $x\mapsto1.8x+1$ is expanding.
- **Degenerate case $\rho=0$.** Take $\varphi(x,c)=c$.

**Junk values: none.**
- Every base of a real power is a distance, hence $\ge0$, and $p>0$. So $t^p$ is the ordinary power, and $0^p=0$ is the true value.
- $\rho\ge0$ gives $\mathrm{ofReal}(\rho)=\rho$.
- The integrands are measurable, so `∫⁻` is the ordinary integral in $[0,\infty]$.
- $\mu$ is a probability measure, so "almost every" is not vacuous.

**Concerns.**
- **`hp` is essential because of `rpow` conventions.** With $p=-1$, Lean's $0^{-1}=0$ and $d(2x,2y)^{-1}=\tfrac12 d(x,y)^{-1}$ make the expanding map $\varphi(x,c)=2x$ satisfy hφ with $\rho=\tfrac12$ and hc at $x_0=1$. Yet the backward iterates $2^n x_0$ diverge (checked numerically with emulated Lean conventions: 0 violations of hφ out of 20 000). With $p=0$ we get $d^0=1$, including $0^0=1$, so hφ says $\nu(E)\le\rho<1$, which contradicts $\nu(E)=1$. The theorem assumes $0<p$, so both cases are excluded.
- **`hρ0` is not needed for truth.** For $\rho<0$, $\mathrm{ofReal}(\rho)=0$, which is exactly the $\rho=0$ case.
- **`hρ1` is essential.** $\varphi(x,c)=x+c$ with $c=\pm1$ satisfies hφ with $\rho=1$ and satisfies hc, but the random walk does not converge.
- **`hc` is essential.** $\varphi(x,c)=x/2+c$ satisfies hφ for *every* $\nu$. Now take $|c|=2^V$ with $\mathbb P(V\ge v)=1/v$ for $v\ge1$:
  - hc fails for every $p>0$;
  - $|2^{-k}c_k|\ge1$ happens for infinitely many $k$ almost surely (second Borel–Cantelli lemma), so the backward series diverges;
  - numerically, 8–17 such $k\le10^6$ appear per run, the largest near $6.5$–$9\times10^5$.
- **`CompleteSpace` is essential.** Take $\alpha=\mathbb Q$ with $\varphi(x,c)=(x+c)/2$, $c\in\{0,1\}$ fair. In $\mathbb R$ the backward iterates converge to a uniform random variable, which is irrational almost surely, so they have no limit in $\mathbb Q$.
- **Scope.** `BorelSpace α` and `SecondCountableTopology α` are auto-included section instances. They restrict the theorem to separable spaces with the Borel σ-algebra; a complete but non-separable space such as $\ell^\infty$ is outside its scope.
- **Redundant instance.** `[IsProbabilityMeasure μ]` is implied by hξ.
- **What is and is not claimed.**
  - The limit $x$ may depend on $\omega$.
  - The statement says nothing about the measurability or the law of $\omega\mapsto x$; that is in T3.
  - Only the **backward** compositions are claimed to converge.
- **Form of `hφ`.**
  - It is a single-step, all-pairs, $L^p$-on-average bound on the $d^p$ scale; the contraction factor on the metric scale is $\rho^{1/p}$.
  - It is required for one fixed $p$.
  - It allows individual maps to expand.
  - hc is required only at the starting point $x_0$.

---

## T3. `tendstoInDistribution_fwdIter`

**Rendering.**

*Setting and hypotheses.* Exactly as in T2:
- $\alpha$: metric space $(\alpha,d)$ with its Borel σ-algebra, second countable, complete.
- $E$, $\Omega$: types with σ-algebras; $\mu$ a probability measure on $\Omega$; $\nu$ a measure on $E$; $\varphi:\alpha\to E\to\alpha$; $\xi_i:\Omega\to E$.
- (hφm) $(x,c)\mapsto\varphi(x,c)$ is measurable for the product σ-algebra.
- Real numbers $p,\rho$ with (hp) $0<p$, (hρ0) $0\le\rho$, (hρ1) $\rho<1$.
- (hφ) $\int_E\mathrm{ofReal}(d(\varphi(x,c),\varphi(y,c))^p)\,\nu(\mathrm dc)\le\mathrm{ofReal}(\rho)\cdot\mathrm{ofReal}(d(x,y)^p)$ for all $x,y\in\alpha$.
- (hξ) mutual independence under $\mu$; (hξm) each $\xi_i$ measurable; (hlaw) $\xi_{i\#}\mu=\nu$ for all $i$.
- A point $x_0\in\alpha$, and (hc) $\int_E\mathrm{ofReal}(d(x_0,\varphi(x_0,c))^p)\,\nu(\mathrm dc)\ne\infty$.

*Conclusion.* Write
$$Z_n(\omega):=\mathrm{fwd}^{\varphi}_n(\xi(\omega),x_0)=f_{\xi_{n-1}(\omega)}\circ\cdots\circ f_{\xi_0(\omega)}(x_0).$$
There exists a function $X:\Omega\to\alpha$ such that all of the following hold:
1. $X$ is μ-a.e.-measurable.
2. For μ-almost every $\omega$, $\mathrm{back}^{\varphi}_n(\xi(\omega),x_0)=f_{\xi_0(\omega)}\circ\cdots\circ f_{\xi_{n-1}(\omega)}(x_0)\to X(\omega)$ as $n\to\infty$.
3. `TendstoInDistribution Z atTop X (fun _ => μ) μ`. Here every $Z_n$ and $X$ live on the same space $(\Omega,\mu)$, and this is the conjunction of:
   - (a) every $Z_n$ is μ-a.e.-measurable;
   - (b) $X$ is μ-a.e.-measurable;
   - (c) as $n\to\infty$, the probability measures $Z_{n\#}\mu$ converge to $X_{\#}\mu$ in the weak topology of probability measures on $\alpha$: $\int_\alpha f\,\mathrm d(Z_{n\#}\mu)\to\int_\alpha f\,\mathrm d(X_{\#}\mu)$ for every bounded continuous $f:\alpha\to[0,\infty)$, equivalently for every bounded continuous $f:\alpha\to\mathbb R$.

**Truth: true.** Proof sketch:
1. **Definition of $X$.** Set $X(\omega):=\lim_n Y_n(\omega)$ where this limit exists, and $X(\omega):=x_0$ otherwise.
2. **Items 1 and 2.** By T2 the limit exists μ-a.s., which gives item 2. $X$ is then μ-a.e.-measurable as an a.e. limit of measurable maps into a metrizable Borel space (`aemeasurable_of_tendsto_metrizable_ae'`), which gives item 1 and item 3(b).
3. **Item 3(a).** Each $Z_n$ is measurable, by hφm and hξm.
4. **Item 3(c).** By `tendstoInDistribution_of_ae_tendsto`, $Y_n\to X$ in distribution. By T1, $Z_{n\#}\mu=Y_{n\#}\mu$ for every $n$, so the sequence of laws in 3(c) is the same sequence, and it converges to $X_{\#}\mu$.

**Non-vacuity.** The instances listed for T2 work here. A fully explicit one:
- Take $\varphi(x,c)=(x+c)/2$ with $c\in\{0,1\}$ fair and $x_0=0$.
- The law of $Z_n$ is uniform on $\{j/2^n : 0\le j<2^n\}$.
- $X=\sum_k\xi_k2^{-(k+1)}\sim U[0,1]$.
- The Kolmogorov–Smirnov (KS) distance between the two laws is exactly $2^{-n}$, verified with rational arithmetic up to $n=12$.

**Junk values: none.**
- `TendstoInDistribution` contains a.e.-measurability fields, so the laws are genuine probability measures.
- Its topology is the standard weak topology.
- The remaining ingredients (powers, `ofReal`, integrals) are as in T2.

**Concerns.**
- **Not asserted:**
  - that $X_{\#}\mu$ is invariant for the chain (stationary);
  - that the invariant law is unique;
  - that $X_{\#}\mu$ does not depend on $x_0$;
  - any rate of convergence (e.g. geometric, or in a Wasserstein distance);
  - almost-sure convergence of the forward chain $Z_n$.

  The first and third hold in the affine example: KS p-value 0.50 for independence of $x_0$ ($x_0=3$ against $x_0=-7$) and 0.62 for invariance under one step. They are simply not part of the statement. The last is false in general: at step 60, 91% of simulated forward paths still move by more than 0.1.
- **Duplication.** Conjunct 1 repeats field 3(b), and conjunct 2 contains T2's conclusion, so T2 follows directly from T3.
- **Instance needed to state it.** `[IsProbabilityMeasure μ]` is needed to *state* `TendstoInDistribution`, because of its instance arguments, even though hξ implies it.
- **Same probability space.** The forward chain and the limit $X$ live on the same probability space. Only the laws are compared in 3(c); the random variables are not coupled.
- **Uniqueness of $X$.** $X$ is determined μ-a.e. by conjunct 2, so its law is determined too.
- **Hypotheses.** The remarks on hp, hρ0, hρ1, hc, `CompleteSpace` and scope made for T2 apply unchanged.

---

## Numerical sanity checks

All scripts use the standard library only and live in `readback/round7/work_H/`.
- `common.py` transcribes `fwdIter`, `backIter` and `revFun` **clause by clause** from the Lean equations; a noise sequence is a callable $k\mapsto e_k$.
- It also provides fast loop versions, which are cross-checked against the literal ones before any Monte Carlo use.
- It emulates Lean's `Real.rpow` on $[0,\infty)$ and `ENNReal.ofReal`.
- Two-sample KS tests use independent samples, with the asymptotic Kolmogorov p-value.

| Script (output) | Instance | Result |
|---|---|---|
| `check_defs.py` (`out_check_defs.txt`) | Symbolic maps; random rational affine maps and a nonlinear float map | Composition order as rendered: forward `f2(f1(f0(x)))`, backward `f0(f1(f2(x)))`. `revFun`: 0 violations (involution, reversal, fixed tail, no truncation) for $n<40$, $i<90$; $r_0=\mathrm{id}$. $\mathrm{back}_n(e,x)=\mathrm{fwd}_n(e\circ r_n,x)$: 0 mismatches in 600 cases. Fast versus literal: 0 mismatches in 1200. $n=0$ gives $x_0$; at $n=1$ the two maps are identical. |
| `exact_law.py` (`out_exact_law.txt`) | $\alpha=\{0,\dots,4\}$, $E=\{0,1,2\}$, $\nu=(\tfrac12,\tfrac13,\tfrac16)$, 12 random transition tables, exact fractions | **T1:** TV(law fwd$_n$, law back$_n$) $=0$ exactly in all 480 cases ($n=0..7$, 5 starting points); in 360 of them forward ≠ backward pathwise. Joint law at times $(3,4)$: TV from 0 to 0.5525, so only marginals are equal. Dropping identical distribution: TV up to 0.5278. Dropping independence (stationary non-reversible Markov noise with uniform marginals): TV up to 0.70. |
| `affine_chain.py` (`out_affine_chain.txt`) | $\varphi(x,c)=x/2+c$, $\nu=U[-1,1]$ or $N(0,1)$, $x_0=3$ | **hφ:** ratio LHS/RHS $=1.000000000000$ with $\rho=2^{-p}$ for $p\in\{0.5,1,2\}$. **hc:** finite (1.20, 1.50, 2.58). **T1:** KS tests at $n\in\{1,2,3,5,10,20\}$ for both noises. 12 tests; the two nominal p-values below 0.05 (0.006, 0.039) have p-values 0.19–0.97 on five fresh replications of size 80 000 each. Means and variances match theory. Power control with non-identically distributed noise: KS 0.12, $p\approx10^{-128}$. **T2:** on all 4000 paths, $\sup_{m\ge n}\lvert Y_m-Y_n\rvert\le 2^{1-n}+2^{-n}\lvert x_0\rvert$ (for example $4.5\times10^{-6}$ at $n=20$). The forward chain does not converge pathwise: mean $\lvert X_{60}-X_{59}\rvert=0.56$, and 90.8% of paths have a jump above 0.1. **T3:** KS(fwd$_n$, back$_{60}$) = 1.00, 0.75, 0.38, 0.19, 0.10, 0.028, 0.009, … reaching the Monte Carlo floor (about 0.014) by $n=8$. **Bernoulli case:** exact law equality, and KS to $U[0,1]$ exactly $2^{-n}$ for $n\le12$. |
| `average_contraction.py` (`out_average_contraction.txt`) | $\varphi(x,c)=cx+1$, $c\in\{0.1,1.8\}$ fair | $\mathbb E c^{p}$ = 0.829 ($p=0.5$), 0.95 ($p=1$), 1.625 ($p=2$): hφ holds for $p\in\{0.5,1\}$ and fails for $p=2$. **T1** exactly: equal laws for $x_0\in\{0,1,-2\}$, $n\le14$. **T2:** median of $\sup_{m\ge n}\lvert Y_m-Y_n\rvert$ is $4.7\times10^{-2}$, $4.3\times10^{-4}$, $7.8\times10^{-8}$, $2.2\times10^{-15}$ at $n=5,10,20,40$. The largest value over 5000 paths is $2.6\times10^{-8}$ at $n=80$, so convergence is not uniform across paths but holds on all of them. The forward chain still moves by more than 0.1 at step 400 on 4475 of 5000 paths. **T1** Monte Carlo: KS p = 0.99, 0.46, 0.13 at $n=3,10,40$. **T3:** KS(fwd$_n$, back$_{300}$) = 0.58, 0.31, 0.18, 0.053, 0.010, … at the Monte Carlo floor by $n=10$. |
| `hypothesis_roles.py` (`out_hypothesis_roles.txt`) | Controls | **$p=-1$:** $2x$ satisfies hφ under Lean conventions (0 violations out of 20 000) and hc, while back$_n=2^n$ diverges. **$p=0$:** $d^0=1$ (including $0^0$), so hφ is unsatisfiable. **$\rho<0$:** $\mathrm{ofReal}(-0.3)=0$. **$\rho=0$** ($\varphi(x,c)=c$): back$_n=\xi_0$ for all $n\ge1$ on all 2000 paths; forward jumps above 0.1 on 18 085 of 20 000 paths; the laws are equal (KS p = 0.68). **Not stated but true in the affine example:** the limit law does not depend on $x_0$ (KS p = 0.50) and is invariant under one step (KS p = 0.62). **hc dropped** (heavy tails): 14, 17 and 8 terms with $\lvert 2^{-k}c_k\rvert\ge1$ for $k\le10^6$ in three runs (about 14.4 expected), so no convergence. |

Limitations:
- The numerical checks test instances; they do not prove the general statements. The truth verdicts rest on the proof sketches above.
- The Monte Carlo tests can only detect discrepancies of roughly 0.01 or more in KS distance at the sample sizes used. The exact rational checks, which settle T1 for finite state spaces, have no such limit.
