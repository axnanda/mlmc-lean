# Read-back audit: packet J (GBM, Euler–Maruyama, MLMC)

| Field | Value |
|---|---|
| Date | 2026-09-28 |
| Packet | `scratchpad/readback/round8/packet_J_gbm_euler_maruyama.lean` |
| Declarations audited | 26: 16 definitions (8 in the packet body, 8 appended from other modules) and 10 theorems/lemmas |
| Auditor | independent blind auditor (sub-agent) |
| Numerical work | `scratchpad/readback/round8/work_J/` (pure Python 3, standard library only; every `check_*.py` has its output next to it as `check_*.out`) |

---

## Summary

### Verdicts

| # | Declaration | Truth | Non-vacuous | Holds only because of a junk value? |
|---|---|---|---|---|
| T1 | `emPath_gbm` | True | Yes (it has no hypotheses) | No |
| T2 | `gbmExp_eq_prod` | True | Yes (it has no hypotheses) | No |
| T3 | `gbmExact_pairAvg` | True | Yes (it has no hypotheses) | No. For $T<0$ it holds in a degenerate way because $\sqrt{\text{negative}}=0$ on both sides. For $T\ge 0$ it holds genuinely. |
| T4 | `map_gbmExact` | True | Yes (it has no hypotheses) | No. The same remark applies for $T<0$. The pushforward is of a measurable map. |
| T5 | `integral_sq_prod_sub_prod` | True | Yes | No |
| T6 | `gbm_em_strong_error` | True | Yes | No |
| T7 | `gbm_strong_error` | True | Yes | No |
| T8 | `gbm_weak_error_le` | True | Yes | No |
| T9 | `gbm_correction_variance_le` | True | Yes | No |
| T10 | `gbm_mlmc_theorem1` | True | Yes | No |

### Main points for a human auditor

1. **I audited the statements, not the proofs.** Every proof in the packet is `sorry`. Each truth verdict rests on my own proof sketch (given below) and on numerical checks. Whether the real proofs exist and are axiom-clean has to be checked separately.
2. **What is modelled.** All randomness is one real sequence $z=(z_i)_{i\in\mathbb N}$ drawn from $\gamma$ = `stdNormalSeq`, under which the $z_i$ are i.i.d. $\mathcal N(0,1)$. A Brownian increment over a step $h$ is modelled as $\sqrt h\,z_i$.
   - The "exact" GBM value `gbmExact` is *defined* by the closed form $s_0\exp\big((r-\sigma^2/2)T+\sigma W\big)$ with $W=\sqrt{T/2^\ell}\sum_{i<2^\ell}z_i$.
   - The packet contains no SDE, no Brownian-motion object and no Itô calculus. That this closed form is "the solution of $dS=rS\,dt+\sigma S\,dW$" holds by definition only.
   - Euler–Maruyama is the generic recursion `emPath` with drift $(S,t)\mapsto rS$ and diffusion $(S,t)\mapsto\sigma S$.
3. **Fine/coarse coupling.** The coarse level is driven by `pairAvg`: $w_k=(z_{2k}+z_{2k+1})/\sqrt2$. This is a variance-preserving normalised sum, not an average, despite the name.
   - The estimator in T10 unfolds to the usual MLMC estimator. Level $0$ is $g$ of a one-step EM value. Level $m+1$ is $g(\text{fine EM, }2^{m+1}\text{ steps})-g(\text{coarse EM, }2^m\text{ steps, driven by }w)$.
   - Every (level, sample) pair has its own independent sequence. I checked the unfolding numerically against a literal transcription.
4. **The constants are explicit but loose.**
   - $\mathrm{gbmStrongConst}(r,\sigma,t,s_0)=s_0^2e^{(2|r|+\sigma^2)t}(|r|+\sigma^2)(5(|r|+\sigma^2)t+4)$.
   - In exact 110-digit arithmetic, the true mean-square error never exceeded about $0.100$ times the stated bound. The supremum $1/10$ is approached as $r\to0$, $h\to0$ and $\sigma^2 nh\to\infty$.
   - For $r<0$ the bound is extremely loose, because it contains $e^{2|r|t}$ where the truth behaves like $e^{2rt}$.
   - The weak-error rate stated is only $2^{-\ell/2}$, which is what the strong error implies. It is not the first-order weak rate.
5. **T10 (`gbm_mlmc_theorem1`).**
   - $c_4$ is only asserted to exist. It may depend on $(r,\sigma,s_0,T,g,K)$ and is not explicit.
   - Cost is the proxy $\sum_{\ell\le L}N_\ell 2^\ell$. It counts fine steps only, not the coarse path or pairing, so it is off by a bounded factor.
   - The target is the *undiscounted* $\mathbb E[g(S_T)]$ with $S_T=s_0\exp((r-\sigma^2/2)T+\sigma\sqrt T\,W)$, $W\sim\mathcal N(0,1)$.
   - $\varepsilon$ ranges over $(0,e^{-1})$ and the MSE is the exact second moment. The complexity claimed is $\varepsilon^{-2}(\ln\varepsilon)^2$, not $\varepsilon^{-2}$.
   - The name suggests "Theorem 1" of some source. I read no source, so whether the hypotheses, cost model and $\varepsilon$-range match it must be checked separately.
6. **Every sign hypothesis is load-bearing.** Without $0\le h$ (T5, T6) or $0\le T$ (T7–T10) the statements are false. With $h<0$ or $T<0$, Mathlib's $\sqrt{\text{negative}}=0$ switches the noise off. Explicit counterexamples:
   - `integral_sq_prod_sub_prod` with $h=-0.1$: the formula gives $4.84\times10^{-3}$ where the true value is $2.63\times10^{-3}$.
   - `gbm_mlmc_theorem1` with $T=-1$, $g=\mathrm{id}$: the MSE is $0.42>e^{-2}$ for every choice of $(L,N)$.
7. **No junk value rescues any statement.**
   - Every integral and variance is of an $L^2$ function; Lipschitz $g$ gives linear growth and all Gaussian/lognormal moments are finite.
   - The map in T4 is measurable.
   - Every factor of each `infinitePi` is a probability measure, so neither product is the junk $0$ measure.
   - $N_\ell\ge1$ rules out $0^{-1}$.
   - $\varepsilon>0$ makes `rpow` and `log` standard.

---

## Rules followed

- **Read:** the packet; the mission file (`prove2me_workspace/references/mission_auditor.md`); Mathlib sources under `.lake/packages/mathlib/Mathlib/`, only to confirm the conventions tabulated below.
- **Not opened:** any project source (`MlmcLean/`), `docs/`, `notes/`, README, PLAN, papers, project scripts, other packets or outputs, git history, the web. The session harness showed the repository's generic build/rules instruction file at start-up. It contains no statement content and was not used.
- **Lean was not run.** I read parsing, precedence, elaboration and casts from the source; the precedences are confirmed in the Mathlib table below.
- **Renderings translate the code only.** Declaration and file names were not used to infer meaning. Where a name and the code differ (e.g. `pairAvg`), the rendering follows the code.
- **Numerics:** pure Python 3 standard library with fixed seeds. Scripts and outputs are in `scratchpad/readback/round8/work_J/`.

---

## Mathlib conventions confirmed

Paths are relative to `.lake/packages/mathlib/Mathlib/`.

| Convention | File:line | Where it matters |
|---|---|---|
| `gaussianReal μ v` is the Gaussian with **mean** $\mu$ and **variance** $v$ ($v:\mathbb R_{\ge0}$). It is `dirac μ` if $v=0$, otherwise it has density $(\sqrt{2\pi v})^{-1}e^{-(x-\mu)^2/(2v)}$. | `Probability/Distributions/Gaussian/Real.lean:219-223` (def), `:49-50` (pdf) | `gaussianReal 0 1` $=\mathcal N(0,1)$ |
| `gaussianReal` is a probability measure | `Probability/Distributions/Gaussian/Real.lean:231` | factors of `stdNormalSeq` |
| `Measure.infinitePi μ` is defined as `if h : ∀ i, IsProbabilityMeasure (μ i) then (product) else 0` (junk $0$ if some factor is not a probability measure) | `Probability/ProductMeasure.lean:358-362` | `stdNormalSeq`; the $\mathbb N\times\mathbb N$ product in T10 |
| Finite-dimensional marginals of `infinitePi` are the finite products: `infinitePi_map_restrict`, `infinitePi_pi` | `Probability/ProductMeasure.lean:377`, `:405` | coordinates are i.i.d. |
| `infinitePi μ` is a probability measure | `Probability/ProductMeasure.lean:381` | the outer product in T10 is not the junk $0$ |
| Coordinate projections are measure preserving: `measurePreserving_eval_infinitePi`, `infinitePi_map_eval` | `Probability/ProductMeasure.lean:470`, `:481` | coordinate $0$ of $\gamma$ is $\mathcal N(0,1)$ |
| `Measure.map f μ` is $0$ unless $f$ is a.e.-measurable (`map_of_not_aemeasurable`) | `MeasureTheory/Measure/Map.lean:88-93`, `:112` | T4 |
| Bochner integral of a non-integrable function is $0$ (`integral_undef`) | `MeasureTheory/Integral/Bochner/Basic.lean:202` | T5–T10 |
| Notation `∫ x, r ∂μ`: body `r` at precedence 60 (so it contains `+`/`-`), measure `μ` at precedence 70 | `MeasureTheory/Integral/Bochner/Basic.lean:166` | integrand of T8; `∂gaussianReal 0 1`; `≤`/`<` stay outside the integral |
| Notation `∑ x ∈ s, f` / `∏ x ∈ s, f`: body at precedence 67 (`+`/`-` end it; `*`, `^` and application do not) | `Algebra/BigOperators/Group/Finset/Defs.lean:181`, `:196` (library note `:82-99`) | T5 difference of products; T10 target subtracted after the level sum; cost $=\sum(N_\ell\cdot2^\ell)$ |
| `variance X μ = (evariance X μ).toReal`, with `evariance X μ = ∫⁻ ‖X − μ[X]‖ₑ²` | `Probability/Moments/Variance.lean:58`, `:64` | T9 |
| `variance` is $0$ for $X\notin L^2$ (`variance_of_not_memLp`) | `Probability/Moments/Variance.lean:132` | T9 (not triggered) |
| `variance X μ ≤ μ[X²]` (`variance_le_expectation_sq`) | `Probability/Moments/Variance.lean:339` | T9 proof sketch |
| `Real.sqrt x = NNReal.sqrt (Real.toNNReal x)`, so $\sqrt x=0$ for $x\le0$ (`sqrt_eq_zero_of_nonpos`) | `Analysis/Real/Sqrt.lean:109-113`, `:142` | $\sqrt h$, $\sqrt T$, $\sqrt{T/2^\ell}$ for negative arguments |
| $(\sqrt x)^2=x$ for $x\ge0$ (`sq_sqrt`); $(\sqrt x)^2=\max(x,0)$ in general (`sq_sqrt'`) | `Analysis/Real/Sqrt.lean:178`, `:276` | T5 (Gaussian moments need $h\ge0$) |
| $\sqrt{x/y}=\sqrt x/\sqrt y$ for $y\ge0$, any $x$ (`sqrt_div'`) | `Analysis/Real/Sqrt.lean:382` | T3 |
| `Real.rpow`: $x^y=\exp(y\log x)$ for $x>0$ (`rpow_def_of_pos`); instance `Pow ℝ ℝ` | `Analysis/SpecialFunctions/Pow/Real.lean:30-38`, `:51` | $2^{-\ell/2}$ in T8, $\varepsilon^{-2}$ in T10 |
| `rpow_neg` ($x\ge0$), `rpow_natCast`, `rpow_two` | `Analysis/SpecialFunctions/Pow/Real.lean:259`, `:62`, `:470` | $\varepsilon^{(-2:\mathbb R)}=1/\varepsilon^2$ |
| `Real.log`: $\log0=0$, $\log x=\log\lvert x\rvert$ | `Analysis/SpecialFunctions/Log/Basic.lean:44-45`, `:103`, `:115` | not triggered ($\varepsilon>0$) |
| $0^{-1}=0$ (`inv_zero`); $a/0=0$ (`div_zero`) | `Algebra/GroupWithZero/Defs.lean:236`; `Algebra/GroupWithZero/Basic.lean:407` | `blockMean` with $N=0$ (excluded in T10) |
| $a^0=1$ for natural powers (`pow_zero`) | `Algebra/Group/Defs.lean:692` | $n=0$ cases, empty products |
| `Finset.range n` $=\{0,\dots,n-1\}$ | `Data/Finset/Range.lean:53`, `:64` | all sums and products |
| $\exp\big(\sum_{x\in s}f(x)\big)=\prod_{x\in s}\exp f(x)$ (`Real.exp_sum`) | `Analysis/Complex/Exponential.lean:226` | T2 |
| Lean core (no Mathlib file): `/`, `%` and `-` on $\mathbb N$ are floor division, remainder and truncated subtraction. Numerals in `1 / 2 * (ℓ : ℝ)` elaborate in $\mathbb R$, so $1/2=0.5$. | none | `emCoarsePath`; exponent $-\ell/2$ in T8 |

### Parsing notes that apply throughout

- `s₀ * ∏ i ∈ range n, F i - s₀ * ∏ i ∈ range n, G i` is $(s_0\prod_i F_i)-(s_0\prod_i G_i)$.
- `∑ ℓ ∈ range (L+1), blockMean … x - ∫ w, … ∂gaussianReal 0 1` is $\big(\sum_\ell\text{blockMean}\big)-\int\cdots$. The target is subtracted once, not per level.
- `∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ …` is $\big(\sum_\ell N_\ell 2^\ell\big)\le\cdots$.
- `Real.log ε ^ 2` $=(\ln\varepsilon)^2$ and `Real.exp (…) ^ n` $=(\exp(\dots))^n$, because application binds tighter than `^`.
- `(n * h)` and `(i * h)` cast the natural number to $\mathbb R$.
- In `range (2 ^ ℓ)` and `path (2 ^ ℓ)`, $2^\ell$ is a natural number. In `T / 2 ^ ℓ`, `((2:ℝ) ^ (ℓ+1))⁻¹` and `(N ℓ : ℝ) * 2 ^ ℓ` it is a natural-number power of the real $2$.
- `(2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ)))` and `ε ^ (-2 : ℝ)` are real powers.

---

## Definitions

Throughout, $\sqrt{\cdot}$ is Mathlib's real square root, with $\sqrt x=0$ for $x\le0$. $\mathbb R^{\mathbb N}$ carries the product $\sigma$-algebra and $\mathbb R$ the Borel $\sigma$-algebra.

### D1. `gbmExpFactor (r σ h x : ℝ) : ℝ`

**Rendering.** For real numbers $r,\sigma,h,x$:
$$\mathrm{gbmExpFactor}(r,\sigma,h,x)=\exp\Big(\big(r-\tfrac{\sigma^2}{2}\big)h+\sigma\sqrt h\,x\Big).$$
Edge cases: for $h<0$ the value is $\exp\big((r-\sigma^2/2)h\big)$ and does not depend on $x$. For $h=0$ it is $1$.

### D2. `gbmEMFactor (r σ h x : ℝ) : ℝ`

**Rendering.** For real numbers $r,\sigma,h,x$:
$$\mathrm{gbmEMFactor}(r,\sigma,h,x)=1+rh+\sigma\sqrt h\,x.$$
It can be zero or negative. For $h<0$ it equals $1+rh$; for $h=0$ it equals $1$.

### D3. `gbmDrift (r : ℝ) : ℝ → ℝ → ℝ`

**Rendering.** For real $r$, the two-argument function $(S,t)\mapsto rS$. The second argument (time) is ignored.

### D4. `gbmVol (σ : ℝ) : ℝ → ℝ → ℝ`

**Rendering.** For real $\sigma$, the two-argument function $(S,t)\mapsto\sigma S$. The second argument is ignored.

### D5. `gbmExact (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ`

**Rendering.** For reals $r,\sigma,T,s_0$, a natural number $\ell$ and a real sequence $z$:
$$X_\ell(z):=\mathrm{gbmExact}(r,\sigma,T,s_0,\ell,z)=s_0\exp\Big(\big(r-\tfrac{\sigma^2}{2}\big)T+\sigma\sqrt{T/2^\ell}\sum_{i=0}^{2^\ell-1}z_i\Big).$$
Only $z_0,\dots,z_{2^\ell-1}$ are used, and there is no sign restriction on $s_0$, $\sigma$ or $T$.
- For $\ell=0$: $s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt T\,z_0\big)$.
- For $T<0$: $\sqrt{T/2^\ell}=0$, so the value is the constant $s_0e^{(r-\sigma^2/2)T}$.
- For $T=0$: the value is $s_0$.

### D6. `gbmEM (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ`

**Rendering.** For reals $r,\sigma,T,s_0$, $\ell\in\mathbb N$ and a real sequence $z$, let $h_\ell=T/2^\ell$ and define $Y_0=s_0$ and
$$Y_{i+1}=Y_i+(rY_i)\,h_\ell+(\sigma Y_i)\sqrt{h_\ell}\,z_i.$$
This is `emPath` with drift $(S,t)\mapsto rS$ and diffusion $(S,t)\mapsto\sigma S$; the time argument $i h_\ell$ is ignored. Then $\mathrm{EM}_\ell(z):=\mathrm{gbmEM}(r,\sigma,T,s_0,\ell,z)=Y_{2^\ell}$, which uses $z_0,\dots,z_{2^\ell-1}$.
- For $T<0$ the noise term vanishes and the value is $s_0(1+rT/2^\ell)^{2^\ell}$.
- For $T=0$ the value is $s_0$.

### D7. `gbmStrongConst (r σ t s₀ : ℝ) : ℝ`

**Rendering.** For reals $r,\sigma,t,s_0$:
$$C(r,\sigma,t,s_0):=s_0^2\,e^{(2|r|+\sigma^2)t}\,\big(|r|+\sigma^2\big)\,\big(5(|r|+\sigma^2)t+4\big).$$
- For $t\ge0$ it is $\ge0$, and it is $0$ exactly when $s_0=0$ or $r=\sigma=0$.
- It is negative exactly when $s_0\ne0$, $(r,\sigma)\ne(0,0)$ and $t<-4/(5(|r|+\sigma^2))$.

### D8. `europeanPayoff (g : ℝ → ℝ) : ℕ → (ℕ → ℝ) → ℝ`

**Rendering.** For $g:\mathbb R\to\mathbb R$, the function $(\ell,p)\mapsto g(p_{2^\ell})$. It applies $g$ to the entry with index $2^\ell$ of a real sequence $p$.

### D9. `blockMean` (appended, from module `SampleMean`)

**Rendering.** For arbitrary types $\iota,\Omega_0,\Omega$ (implicit arguments), $f:\iota\to(\Omega_0\to\mathbb R)$, $\omega:\iota\times\mathbb N\to(\Omega\to\Omega_0)$, $i\in\iota$, $N\in\mathbb N$ and $x\in\Omega$:
$$\mathrm{blockMean}(f,\omega,i,N,x)=N^{-1}\sum_{n=0}^{N-1}f_i\big(\omega_{(i,n)}(x)\big).$$
For $N=0$ the value is $0$, because $0^{-1}=0$ and the sum is empty.

### D10. `fineCoarseDiff` (appended, from module `Corrections`)

**Rendering.** For a type $\Omega_0$ and $P^{f},P^{c}:\mathbb N\to(\Omega_0\to\mathbb R)$, the sequence of functions defined by
- $\mathrm{fineCoarseDiff}(P^f,P^c)_0=P^f_0$;
- $\mathrm{fineCoarseDiff}(P^f,P^c)_{\ell+1}(y)=P^f_{\ell+1}(y)-P^c_\ell(y)$ for $\ell\in\mathbb N$, $y\in\Omega_0$.

### D11. `emPath (a b : ℝ → ℝ → ℝ) (h S₀ : ℝ) (z : ℕ → ℝ) : ℕ → ℝ` (appended, from module `EulerMaruyama`)

**Rendering.** For two-argument real functions $a,b$, reals $h,S_0$ and a real sequence $z$, the sequence $(Y_k)_{k\in\mathbb N}$ given by $Y_0=S_0$ and
$$Y_{i+1}=Y_i+a\big(Y_i,\,i\,h\big)\,h+b\big(Y_i,\,i\,h\big)\,\sqrt h\,z_i\qquad(i\in\mathbb N).$$
Here $i\,h$ is the real product of $i$ (cast to $\mathbb R$) with $h$. For $h<0$ the $z$-term vanishes because $\sqrt h=0$. $Y_k$ depends only on $z_0,\dots,z_{k-1}$.

### D12. `pairAvg (z : ℕ → ℝ) (k : ℕ) : ℝ` (appended)

**Rendering.** For a real sequence $z$, the sequence
$$\mathrm{pairAvg}(z)_k=\frac{z_{2k}+z_{2k+1}}{\sqrt2}.$$
It divides by $\sqrt2$, not by $2$, so it is not the arithmetic mean of the pair.

### D13. `stdNormalSeq : Measure (ℕ → ℝ)` (appended, `abbrev`)

**Rendering.** The measure $\gamma$ on $\mathbb R^{\mathbb N}$ given by Mathlib's infinite product `Measure.infinitePi` of the constant family $\mathcal N(0,1)$ (`gaussianReal 0 1`: mean $0$, variance $1$). Every factor is a probability measure, so this is the genuine product: the probability measure with
$$\gamma\{z:\ z_i\in A_i\ \forall i\in F\}=\prod_{i\in F}\mathcal N(0,1)(A_i)$$
for every finite $F\subset\mathbb N$ and Borel sets $A_i$. Under $\gamma$ the coordinates $z_i$ are i.i.d. standard normal. (Had some factor not been a probability measure, the definition would return the zero measure; that does not happen here.)

### D14. `emFine (a b) (T S₀) (Φ) (ℓ) (z)` (appended)

**Rendering.** For $a,b$ as in D11, reals $T,S_0$, $\Phi:\mathbb N\to((\mathbb N\to\mathbb R)\to\mathbb R)$, $\ell\in\mathbb N$ and a real sequence $z$: the value $\Phi_\ell(Y)$. Here $Y$ is the whole sequence $k\mapsto\mathrm{emPath}(a,b,T/2^\ell,S_0,z)_k$, the EM path with step $T/2^\ell$.

### D15. `emCoarse (a b) (T S₀) (Φ) (ℓ) (z)` (appended)

**Rendering.** With the same arguments as D14: the value $\Phi_\ell(p)$, where $p$ is the sequence $k\mapsto\mathrm{emCoarsePath}(a,b,T/2^{\ell+1},S_0,z,2k)$.

### D16. `emCoarsePath (a b) (h S₀) (z) (i : ℕ)` (appended)

**Rendering.** Let $w=\mathrm{pairAvg}(z)$ and let $\bar Y=\mathrm{emPath}(a,b,2h,S_0,w)$. This is the EM path with step $2h$: $\bar Y_0=S_0$ and
$$\bar Y_{j+1}=\bar Y_j+a(\bar Y_j,\,j\cdot2h)\,2h+b(\bar Y_j,\,j\cdot2h)\sqrt{2h}\,w_j.$$
Then:
- if $i$ is even, the value is $\bar Y_{i/2}$;
- if $i$ is odd, with $m=\lfloor i/2\rfloor$, the value is $\bar Y_m+a(\bar Y_m,\,2m\,h)\,h+b(\bar Y_m,\,2m\,h)\sqrt h\,z_{i-1}$, where $i-1=2m$.

(In this packet only even indices are evaluated, through `emCoarse`.)

---

## Theorems

In the renderings, $\gamma$ is always the measure of D13 (the $z_i$ are i.i.d. $\mathcal N(0,1)$), and every $\int$ is a Bochner integral, which Mathlib sets to $0$ for a non-integrable integrand.

### T1. `emPath_gbm (r σ h s₀ : ℝ) (z : ℕ → ℝ) (n : ℕ)`

**Rendering.** For all reals $r,\sigma,h,s_0$, every real sequence $z$ and every $n\in\mathbb N$:
$$Y_n=s_0\prod_{i=0}^{n-1}\big(1+rh+\sigma\sqrt h\,z_i\big),$$
where $Y_0=s_0$ and $Y_{i+1}=Y_i+(rY_i)h+(\sigma Y_i)\sqrt h\,z_i$ (`emPath` with `gbmDrift r`, `gbmVol σ`).
- There is no hypothesis on $h$. For $h<0$, $\sqrt h=0$ on both sides.
- For $n=0$ the product is empty and equals $1$.

**Assessment.**
- **Truth:** true. The recursion is $Y_{i+1}=Y_i(1+rh+\sigma\sqrt h z_i)$, then induct on $n$.
- **Non-vacuity:** there are no hypotheses. Example: $r=0.05$, $\sigma=0.2$, $h=0.1$, $s_0=100$, $z_0=z_1=1$, $n=2$. Then $Y_1=106.8246$ and $Y_2=114.1149=100\cdot1.0682456^2$.
- **Junk values:** none is needed. The $h<0$ case uses $\sqrt h=0$ identically on both sides.
- **Concerns:** none. Checked on 3000 random inputs, including $h<0$; the largest relative difference was $6.7\times10^{-14}$.

### T2. `gbmExp_eq_prod (r σ h s₀ : ℝ) (n : ℕ) (z : ℕ → ℝ)`

**Rendering.** For all reals $r,\sigma,h,s_0$, every $n\in\mathbb N$ and every real sequence $z$:
$$s_0\exp\Big(\big(r-\tfrac{\sigma^2}{2}\big)(n h)+\sigma\Big(\sqrt h\sum_{i=0}^{n-1}z_i\Big)\Big)=s_0\prod_{i=0}^{n-1}\exp\Big(\big(r-\tfrac{\sigma^2}{2}\big)h+\sigma\sqrt h\,z_i\Big).$$
There is no hypothesis on $h$.

**Assessment.**
- **Truth:** true. $\exp$ of a finite sum is the product of the exponentials (`Real.exp_sum`), and $\sum_{i<n}[(r-\sigma^2/2)h+\sigma\sqrt h z_i]=(r-\sigma^2/2)nh+\sigma\sqrt h\sum_{i<n}z_i$.
- **Non-vacuity:** there are no hypotheses. Example: $r=0.05$, $\sigma=0.2$, $h=0.1$, $n=2$, $z=(1,-1)$. Both sides equal $s_0e^{0.006}$.
- **Junk values:** none.
- **Concerns:** none. Largest relative difference over 3000 random inputs: $3.9\times10^{-14}$.

### T3. `gbmExact_pairAvg (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ)`

**Rendering.** For all reals $r,\sigma,T,s_0$, every $\ell\in\mathbb N$ and every real sequence $z$:
$$s_0\exp\Big(\big(r-\tfrac{\sigma^2}{2}\big)T+\sigma\sqrt{T/2^\ell}\sum_{k=0}^{2^\ell-1}\frac{z_{2k}+z_{2k+1}}{\sqrt2}\Big)=s_0\exp\Big(\big(r-\tfrac{\sigma^2}{2}\big)T+\sigma\sqrt{T/2^{\ell+1}}\sum_{i=0}^{2^{\ell+1}-1}z_i\Big).$$
This is $X_\ell(\mathrm{pairAvg}(z))=X_{\ell+1}(z)$ with $X$ from D5. There is no sign hypothesis on $T$.

**Assessment.**
- **Truth:** true. First, $\sum_{k<2^\ell}(z_{2k}+z_{2k+1})=\sum_{i<2^{\ell+1}}z_i$. Second, $\sqrt{T/2^\ell}/\sqrt2=\sqrt{T/2^{\ell+1}}$: for $T\ge0$ by `sqrt_div'`, and for $T<0$ both square roots are $0$.
- **Non-vacuity:** there are no hypotheses. Example: $\ell=0$, $T=1$. Both sides equal $s_0\exp\big(r-\sigma^2/2+\sigma(z_0+z_1)/\sqrt2\big)$.
- **Junk values:** for $T<0$ both sides reduce to $s_0e^{(r-\sigma^2/2)T}$ only because $\sqrt{\text{negative}}=0$. That instance is degenerate but correct. The meaningful case $T\ge0$ holds genuinely.
- **Concerns:** none. Largest relative difference over 3000 random inputs, including $T<0$ and $T=0$: $3.6\times10^{-15}$ (exactly $0$ for $T\le0$).

### T4. `map_gbmExact (r σ T s₀ : ℝ) (ℓ : ℕ)`

**Rendering.** For all reals $r,\sigma,T,s_0$ and every $\ell\in\mathbb N$, two measures on $\mathbb R$ are equal:
- the image of $\gamma$ under $z\mapsto X_\ell(z)=s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt{T/2^\ell}\sum_{i<2^\ell}z_i\big)$;
- the image of $\gamma$ under $z\mapsto X_0(z)=s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt T\,z_0\big)$.

In Mathlib the image measure `Measure.map` is defined to be $0$ for a map that is not a.e.-measurable. There is no sign hypothesis on $T$.

**Assessment.**
- **Truth:** true. Under $\gamma$, $S=\sum_{i<2^\ell}z_i\sim\mathcal N(0,2^\ell)$.
  - For $T>0$: $\sqrt{T/2^\ell}\,S\sim\mathcal N(0,T)$, which is the law of $\sqrt T z_0$.
  - For $T\le0$: both maps are the constant $s_0e^{(r-\sigma^2/2)T}$.
  - Both maps are continuous functions of finitely many coordinates, hence measurable, so both sides are genuine image measures.
- **Non-vacuity:** there are no hypotheses. Example: $\ell=1$, $T=1$, $\sigma=0.2$, $s_0=100$, $r=0.05$. Both sides are the lognormal law with log-mean $\ln100+0.03$ and log-variance $0.04$.
- **Junk values:** the `map` junk is not triggered because the maps are measurable. The case $T<0$ is degenerate (both sides are the same Dirac mass) but correct.
- **Concerns:** none. A two-sample Kolmogorov–Smirnov test (20000 draws each, 3 parameter sets including $r<0$, $\sigma<0$, $s_0<0$) gave $D\in\{0.011,0.006,0.009\}$, below the 5% critical value $0.0136$.

### T5. `integral_sq_prod_sub_prod (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (s₀ : ℝ) (n : ℕ)`

**Rendering.** For all reals $r,\sigma$, every real $h$ with $0\le h$, every real $s_0$ and every $n\in\mathbb N$:
$$\int_{\mathbb R^{\mathbb N}}\Big(s_0\prod_{i=0}^{n-1}E_i(z)-s_0\prod_{i=0}^{n-1}M_i(z)\Big)^2\,\gamma(dz)=s_0^2\Big(\big(e^{(2r+\sigma^2)h}\big)^n-2\big(e^{rh}(1+rh+\sigma^2h)\big)^n+\big((1+rh)^2+\sigma^2h\big)^n\Big),$$
where:
- $E_i(z)=\exp\big((r-\sigma^2/2)h+\sigma\sqrt h\,z_i\big)$ (`gbmExpFactor`);
- $M_i(z)=1+rh+\sigma\sqrt h\,z_i$ (`gbmEMFactor`).

The square is of the difference of the two products. For $n=0$ both sides are $0$.

**Assessment.**
- **Truth:** true.
  - Expand the square. By independence under $\gamma$, $\int\prod_{i<n}f(z_i)\,d\gamma=(\mathbb E f(Z))^n$ for $Z\sim\mathcal N(0,1)$.
  - With $a=\sigma\sqrt h$ and using $\mathbb Ee^{aZ}=e^{a^2/2}$, $\mathbb E[Ze^{aZ}]=ae^{a^2/2}$ and $(\sqrt h)^2=h$ (this step needs $h\ge0$):
    - $\mathbb E E^2=e^{(2r+\sigma^2)h}$;
    - $\mathbb E[EM]=e^{rh}(1+rh+\sigma^2h)$;
    - $\mathbb EM^2=(1+rh)^2+\sigma^2h$.
  - All exponential moments are finite, so the integrand is integrable and the Bochner integral is the true expectation.
- **Non-vacuity:** example $r=0.05$, $\sigma=0.2$, $h=0.1$, $s_0=1$, $n=10$. The formula gives $9.302\times10^{-5}$; Monte Carlo gives $9.33\times10^{-5}\pm1.0\times10^{-6}$ (3 SE).
- **Junk values:** none; the integrand is integrable.
- **Concerns:** `hh` is load-bearing. For $h<0$ the literal left side is $s_0^2\big(e^{(r-\sigma^2/2)nh}-(1+rh)^n\big)^2$, which differs from the formula. For example, with $r=0$, $\sigma=1$, $h=-0.1$, $n=1$ the left side is $2.63\times10^{-3}$ and the formula gives $4.84\times10^{-3}$.

### T6. `gbm_em_strong_error (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ)`

**Rendering.** For all reals $r,\sigma,s_0$, every real $h$ with $0\le h$ and every $n\in\mathbb N$:
$$\int_{\mathbb R^{\mathbb N}}\Big(s_0\exp\Big(\big(r-\tfrac{\sigma^2}{2}\big)(nh)+\sigma\sqrt h\sum_{i=0}^{n-1}z_i\Big)-Y_n(z)\Big)^2\gamma(dz)\ \le\ s_0^2\,e^{(2|r|+\sigma^2)nh}\,(|r|+\sigma^2)\,\big(5(|r|+\sigma^2)nh+4\big)\cdot h,$$
where $Y_0=s_0$ and $Y_{i+1}=Y_i+rY_ih+\sigma Y_i\sqrt h\,z_i$ (`emPath (gbmDrift r) (gbmVol σ) h s₀ z n`).
- The right side is $C(r,\sigma,nh,s_0)\cdot h$ with $C$ from D7. It is explicit and evaluated at $t=nh$.
- For $n=0$ the left side is $0$ and the right side is $4s_0^2(|r|+\sigma^2)h\ge0$.

**Assessment.**
- **Truth:** true. Proof sketch.
  - Set $\lambda=|r|+\sigma^2$, $G=e^{(2|r|+\sigma^2)h}$, $A=e^{(2r+\sigma^2)h}$, $B=e^{rh}(1+rh+\sigma^2h)$, $D=(1+rh)^2+\sigma^2h$.
  - By T1, T2 and T5, the left side is $s_0^2\epsilon_n$ with $\epsilon_n=A^n-2B^n+D^n$. The right side is $s_0^2G^n\lambda(5\lambda nh+4)h$.
  - For $h\ge0$: $0<A\le G$, $0\le D\le G$, $|B|\le G$, and $B\le A$ (since $1+x\le e^x$).
  - **Case $\lambda h\ge1$:** $\epsilon_n\le A^n+2|B|^n+D^n\le4G^n\le4\lambda hG^n$, which is at most the bound.
  - **Case $\lambda h<1$:**
    - Here $B>0$. Write $Q_k=\prod_{i<k}E_i$ and $e_k=Q_k-\prod_{i<k}M_i$ (factors from T5). Direct algebra, or the one-step error recursion $e_{k+1}=e_kM_k+Q_k(E_k-M_k)$ with independence, gives $\epsilon_{k+1}=D\epsilon_k+2(B-D)(A^k-B^k)+A^k(A-2B+D)$.
    - Since $0\le A^k-B^k\le G^k$ and $0\le D\le G$, this yields $\epsilon_n\le nG^{n-1}\big(2|B-D|+|A-2B+D|\big)$.
    - Taylor with Lagrange remainder gives $0\le A-B=e^{rh}\big(e^{(r+\sigma^2)h}-1-(r+\sigma^2)h\big)\le\tfrac12\lambda^2h^2G$.
    - The identity $B-D=(e^{rh}-1-rh)(1+(r+\sigma^2)h)+r\sigma^2h^2$ gives $|B-D|\le(\tfrac12r^2+|r|\sigma^2)h^2G$.
    - Hence $2|B-D|+|A-2B+D|\le3|B-D|+(A-B)\le2\lambda^2h^2G$.
    - Therefore $\epsilon_n\le2\lambda^2(nh)hG^n\le\lambda h(5\lambda nh+4)G^n$.
  - Both case inequalities were also confirmed numerically on 9600 grid cases, with no violations.
- **Non-vacuity:** example $r=0.05$, $\sigma=0.2$, $s_0=1$, $h=0.1$, $n=10$: $9.30\times10^{-5}\le0.04607$.
- **Junk values:** none; the integrand is integrable and $h\ge0$.
- **Concerns:**
  - `hh` is load-bearing. With $h=-0.1$, $n=1$, $r=0$, $\sigma=1$, $s_0=1$: the left side is $2.63\times10^{-3}$ and the right side is $-0.317$.
  - The bound is never tight. The largest ratio found (left side / right side) is $0.1000$. For $r=0$ one can show the ratio is below $1/10$. For $r<0$ the ratio can be around $10^{-20}$.
  - "Exact" here means the closed form driven by the same increments $\sqrt h z_i$ (see main point 2).

### T7. `gbm_strong_error (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (ℓ : ℕ)`

**Rendering.** For all reals $r,\sigma,s_0$, every real $T$ with $0\le T$ and every $\ell\in\mathbb N$:
$$\int_{\mathbb R^{\mathbb N}}\big(X_\ell(z)-\mathrm{EM}_\ell(z)\big)^2\gamma(dz)\le s_0^2e^{(2|r|+\sigma^2)T}(|r|+\sigma^2)\big(5(|r|+\sigma^2)T+4\big)\cdot\frac{T}{2^\ell},$$
where:
- $X_\ell(z)=s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt{T/2^\ell}\sum_{i<2^\ell}z_i\big)$;
- $\mathrm{EM}_\ell(z)=Y_{2^\ell}$ with $Y_0=s_0$ and $Y_{i+1}=Y_i+rY_i\,T/2^\ell+\sigma Y_i\sqrt{T/2^\ell}\,z_i$.

**Assessment.**
- **Truth:** true. This is T6 with $h=T/2^\ell\ge0$ and $n=2^\ell$. Then $nh=T$, and $X_\ell$ is exactly T6's closed form.
- **Non-vacuity:** example $r=0.05$, $\sigma=0.2$, $s_0=100$, $T=1$, $\ell=4$: the exact left side is $0.5791$ and the right side is $287.93$.
- **Junk values:** none.
- **Concerns:**
  - `hT` is load-bearing. With $T=-0.1$, $\ell=0$, $r=0$, $\sigma=1$, $s_0=1$: the left side is $2.63\times10^{-3}$ and the right side is $-0.317$.
  - Across the tabulated cases the ratio ranges from $4\times10^{-21}$ to $0.091$.

### T8. `gbm_weak_error_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (ℓ : ℕ)`

**Rendering.** For all reals $r,\sigma,s_0$, every real $T\ge0$, every function $g:\mathbb R\to\mathbb R$, every real $K$ with $|g(x)-g(y)|\le K|x-y|$ for all $x,y\in\mathbb R$, and every $\ell\in\mathbb N$:
$$\Big|\int_{\mathbb R^{\mathbb N}}\Big(g\big(\mathrm{EM}_\ell(z)\big)-g\big(X_0(z)\big)\Big)\gamma(dz)\Big|\le K\sqrt{C(r,\sigma,T,s_0)\,T}\ 2^{-\ell/2},$$
where:
- $\mathrm{EM}_\ell$ is as in T7 ($2^\ell$ EM steps of size $T/2^\ell$ driven by $z_0,\dots,z_{2^\ell-1}$);
- $X_0(z)=s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt T\,z_0\big)$, which uses only $z_0$;
- $C$ is from D7.

The Lipschitz hypothesis forces $K\ge0$. $2^{-\ell/2}$ is a real power, and the integrand is the difference of the two terms.

**Assessment.**
- **Truth:** true. Proof sketch:
  - $|g(x)|\le|g(0)|+K|x|$, and all Gaussian and lognormal moments are finite, so both terms are integrable and the integral is $\mathbb Eg(\mathrm{EM}_\ell)-\mathbb Eg(X_0)$.
  - By T4, $\mathbb Eg(X_0)=\mathbb Eg(X_\ell)$.
  - So the left side is $|\mathbb E[g(\mathrm{EM}_\ell)-g(X_\ell)]|\le K\,\mathbb E|\mathrm{EM}_\ell-X_\ell|\le K\big(\mathbb E|\mathrm{EM}_\ell-X_\ell|^2\big)^{1/2}$.
  - By T7 this is at most $K\sqrt{CT/2^\ell}=K\sqrt{CT}\,2^{-\ell/2}$.
- **Non-vacuity:** example $g=\mathrm{id}$, $K=1$, $r=-0.5$, $\sigma=0.8$, $s_0=2$, $T=2$, $\ell=0$. The left side is exactly $|s_0(1+rT)-s_0e^{rT}|=0.7358$ and the right side is $61.09$.
- **Junk values:** none. $CT\ge0$ so the square root is genuine; $2^{x}$ with base $2>0$ is standard; $1/2$ elaborates as the real $0.5$.
- **Concerns:**
  - The rate is $2^{-\ell/2}$, which is weak order $\tfrac12$ inherited from the strong error.
  - For $\ell\ge1$ the integrand is not a pathwise error, because $X_0$ uses only $z_0$. Only its integral, a difference of expectations, is meaningful.
  - `hT` is load-bearing. With $T=-0.1$, $r=0$, $\sigma=1$, $s_0=1$, $g=\mathrm{id}$: the left side is $0.0513$ and the right side is $0$, since $\sqrt{CT}=\sqrt{\text{negative}}=0$.
  - Monte Carlo over 5 parameter sets and $\ell\le6$ gives $|\text{weak error}|/\text{bound}\le0.055$.

### T9. `gbm_correction_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (ℓ : ℕ)`

**Rendering.** For all reals $r,\sigma,s_0$, every $T\ge0$, every $g:\mathbb R\to\mathbb R$ and real $K$ with $|g(x)-g(y)|\le K|x-y|$ for all $x,y$, and every $\ell\in\mathbb N$:
$$\operatorname{Var}_\gamma\Big[z\mapsto g\big(\mathrm{EM}_{\ell+1}(z)\big)-g\big(\mathrm{EM}_\ell(\mathrm{pairAvg}(z))\big)\Big]\le6K^2\,\big(C(r,\sigma,T,s_0)\,T\big)\,\frac1{2^{\ell+1}},$$
where:
- $\mathrm{EM}_{\ell+1}(z)$ is $2^{\ell+1}$ EM steps of size $T/2^{\ell+1}$ driven by $z$;
- $\mathrm{EM}_\ell(\mathrm{pairAvg}(z))$ is $2^\ell$ EM steps of size $T/2^\ell$ driven by $w_k=(z_{2k}+z_{2k+1})/\sqrt2$ (drift $rS$, diffusion $\sigma S$ in both);
- $C$ is from D7;
- $\operatorname{Var}_\gamma[X]$ is Mathlib's `variance`, i.e. $\int|X-\mathbb EX|^2d\gamma\in[0,\infty]$ converted to a real, with $\infty\mapsto0$.

**Assessment.**
- **Truth:** true. Proof sketch:
  - The random variable $\Delta$ is in $L^2$, so `variance` is the genuine variance. Then $\operatorname{Var}\Delta\le\mathbb E\Delta^2\le K^2\,\mathbb E\big(\mathrm{EM}_{\ell+1}(z)-\mathrm{EM}_\ell(w)\big)^2$.
  - Insert $X_{\ell+1}(z)=X_\ell(w)$ (T3) and use $(a+b)^2\le2a^2+2b^2$.
  - The first term is at most $CT/2^{\ell+1}$ by T7.
  - The second term is at most $CT/2^\ell$ by T7 after pushing $\gamma$ forward by $\mathrm{pairAvg}$, which preserves $\gamma$ because the pairs are disjoint and $(z_{2k}+z_{2k+1})/\sqrt2\sim\mathcal N(0,1)$ independently.
  - Total: $2K^2(CT/2^{\ell+1}+2CT/2^{\ell+1})=6K^2CT/2^{\ell+1}$.
- **Non-vacuity:** example $r=0.05$, $\sigma=0.2$, $s_0=100$, $T=1$, $g(x)=\max(x-100,0)$, $K=1$, $\ell=0$: Monte Carlo variance $\approx2.52$, bound $1.38\times10^4$.
- **Junk values:** none; $\Delta\in L^2$ so `evariance` is finite.
- **Concerns:**
  - The constant is $6=2(1+2)$.
  - Monte Carlo gives variance/bound $\le1.13\times10^{-2}$ over 5 parameter sets and $\ell\le6$.
  - `hT` is load-bearing. With $T=-0.1$, $r=0$, $\sigma=1$: the variance is $0$ and the right side is $-0.95$.
  - The measure-preservation of `pairAvg` is needed by any proof but is not a statement in this packet.

### T10. `gbm_mlmc_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|)`

**Rendering.** Fix the data:
- reals $r,\sigma,s_0$;
- a real $T$ with $0\le T$;
- a function $g:\mathbb R\to\mathbb R$ and a real $K$ with $|g(x)-g(y)|\le K|x-y|$ for all $x,y\in\mathbb R$.

Objects used in the statement (unfolded from the packet):
- **EM paths.** For a real sequence $y$ and $m\in\mathbb N$, put $h_m=T/2^m$. Let $Y^{(m)}(y)$ be $Y^{(m)}_0=s_0$ and $Y^{(m)}_{i+1}=Y^{(m)}_i+rY^{(m)}_ih_m+\sigma Y^{(m)}_i\sqrt{h_m}\,y_i$.
- **Pairing.** $w(y)_k=(y_{2k}+y_{2k+1})/\sqrt2$.
- **Level terms.** `fineCoarseDiff (emFine …) (emCoarse …)` with payoff `europeanPayoff g` unfolds to
$$P_0(y)=g\big(Y^{(0)}_1(y)\big)=g\big(s_0+rs_0T+\sigma s_0\sqrt T\,y_0\big),\qquad P_{m+1}(y)=g\big(Y^{(m+1)}_{2^{m+1}}(y)\big)-g\big(Y^{(m)}_{2^m}(w(y))\big).$$
  For the coarse term, `emCoarse` at level $m$ evaluates `emCoarsePath` with step $T/2^{m+1}$ at the even index $2\cdot2^m$. That is the EM path with step $2\cdot T/2^{m+1}=T/2^m$, driven by $w(y)$, at index $2^m$.
- **Sample space.** $\Pi$ is the infinite-product probability measure on families $x=(x_{(\ell,n)})_{(\ell,n)\in\mathbb N\times\mathbb N}$ of real sequences, every factor being $\gamma$. Under $\Pi$ all entries $x_{(\ell,n)}(i)$ are independent $\mathcal N(0,1)$.
- **Estimator and target.** For $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$,
$$\widehat Y_{L,N}(x)=\sum_{\ell=0}^{L}\frac1{N_\ell}\sum_{n=0}^{N_\ell-1}P_\ell\big(x_{(\ell,n)}\big),\qquad\mu_g=\int_{\mathbb R}g\Big(s_0\exp\big((r-\tfrac{\sigma^2}{2})T+\sigma\sqrt T\,w\big)\Big)\,\mathcal N(0,1)(dw).$$
  The inner average is `blockMean` with $\omega_{(\ell,n)}(x)=x_{(\ell,n)}$.

The theorem asserts: **there exists a real $c_4>0$ such that for every real $\varepsilon$ with $0<\varepsilon$ and $\varepsilon<e^{-1}$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with**
1. $N_\ell\ge1$ for **every** $\ell\in\mathbb N$ (not only $\ell\le L$);
2. $\displaystyle\int\big(\widehat Y_{L,N}(x)-\mu_g\big)^2\,\Pi(dx)<\varepsilon^2$ (strict);
3. $\displaystyle\sum_{\ell=0}^{L}N_\ell\,2^\ell\le c_4\,\varepsilon^{-2}(\ln\varepsilon)^2$.

Dependencies and edge cases:
- $c_4$ may depend on $r,\sigma,s_0,T,g,K$ but not on $\varepsilon$. $L$ and $N$ may depend on everything, including $\varepsilon$.
- $\varepsilon^{-2}$ is the real power. $(\ln\varepsilon)^2$ is the square of $\ln\varepsilon$, not $\ln(\varepsilon^2)$; it exceeds $1$ on the range.
- $\mu_g$ is subtracted once, after the sum over levels.
- The integrals are Bochner integrals (value $0$ if not integrable).
- $T=0$ is allowed. $K\ge0$ is forced, and $K=0$ means $g$ is constant.

**Assessment.**
- **Truth:** true. Proof sketch:
  - **(i) Integrability.** $|g(x)|\le|g(0)|+K|x|$ and every $Y^{(m)}$ is a polynomial in finitely many Gaussians, so every $P_\ell\in L^2$ and $\mu_g$ is finite. Hence the MSE integral is the genuine second moment.
  - **(ii) Bias–variance split.** Independence under $\Pi$ gives $\mathrm{MSE}=\sum_{\ell\le L}V_\ell/N_\ell+(\mathbb E\widehat Y-\mu_g)^2$ with $V_\ell=\operatorname{Var}P_\ell$.
  - **(iii) Bias.** `pairAvg` preserves $\gamma$, so the expectations telescope: $\mathbb E\widehat Y=\mathbb Eg(Y^{(L)}_{2^L})$. Also $\mu_g=\int g(X_0)\,d\gamma$, because coordinate $0$ is $\mathcal N(0,1)$. By T8, $|\text{bias}|\le c_1 2^{-L/2}$ with $c_1=K\sqrt{CT}$.
  - **(iv) Variances.** $V_0\le K^2s_0^2(r^2T^2+\sigma^2T)$ and, by T9, $V_{m+1}\le6K^2CT\,2^{-(m+1)}$. So $V_\ell\le c_2 2^{-\ell}$ with $c_2=\max\big(K^2s_0^2(r^2T^2+\sigma^2T),\,6K^2CT\big)$.
  - **(v) Choice of $L$ and $N$.** Take $L$ minimal with $c_1^22^{-L}<\varepsilon^2/2$ and $N_\ell=\max\big(1,\lceil2(L+1)c_2 2^{-\ell}/\varepsilon^2\rceil\big)$, with $N_\ell=1$ for $\ell>L$. Then $\mathrm{MSE}<\varepsilon^2$.
  - **(vi) Cost.** $\text{cost}\le2(L+1)^2c_2\varepsilon^{-2}+2^{L+1}$. Here $2^{L-1}\le2c_1^2/\varepsilon^2$ when $L\ge1$, and $\ln(1/\varepsilon)>1$, so the cost is at most $c_4\varepsilon^{-2}(\ln\varepsilon)^2$ for a suitable $c_4$.
- **Non-vacuity:** example $r=0.05$, $\sigma=0.2$, $s_0=1$, $T=1$, $g(x)=\max(x-1,0)$, $K=1$, which satisfies all hypotheses. The conclusion is not trivial:
  - $V_0=\operatorname{Var}g(1.05+0.2Z)\approx0.0178>0$ and $\mathrm{MSE}\ge V_0/N_0$, so any admissible $(L,N)$ has cost at least $V_0\varepsilon^{-2}$. The statement is therefore a real upper bound on an unavoidable cost.
  - For this instance the construction above gives cost$/(\varepsilon^{-2}\ln^2\varepsilon)\le120.1$ over 4001 values $\varepsilon\in[10^{-15},e^{-1})$, tending to about $46$ as $\varepsilon\to0$.
  - The empirical MSE of the actual estimator with those $(L,N)$ was $2.3\times10^{-5}$, $4.7\times10^{-6}$ and $1.3\times10^{-6}$ for $\varepsilon=0.2,0.1,0.05$, against targets $\varepsilon^2=0.04,0.01,0.0025$.
- **Junk values:** none. The MSE integrand is integrable; the `infinitePi` factors are probability measures (so $\Pi\ne0$); $N_\ell\ge1$ excludes $0^{-1}$; $\varepsilon>0$ makes $\varepsilon^{-2}$ and $\ln\varepsilon$ standard.
- **Concerns:**
  - $c_4$ is existential and not explicit. It may depend on $g$ as well as $(r,\sigma,s_0,T,K)$; the construction shows $(r,\sigma,s_0,T,K)$ suffices.
  - The theorem asserts that some $(L,N)$ exists. It does not specify an allocation rule or algorithm.
  - The cost proxy $\sum_{\ell\le L}N_\ell2^\ell$ ignores the $2^{\ell-1}$ coarse steps and the pairing work per sample. The true work is within a constant factor, so the order claim is unaffected, but the constant differs.
  - The target is $\mathbb E[g(S_T)]$ without a discount factor $e^{-rT}$. Discounting can be absorbed into $g$.
  - The complexity class is $\varepsilon^{-2}(\ln\varepsilon)^2$, the case where variance decay and cost growth rates are equal (both $2^{\pm\ell}$), with weak rate $\tfrac12$.
  - `hT` is load-bearing. With $r=0$, $\sigma=1$, $s_0=1$, $T=-1$, $g=\mathrm{id}$, every path is deterministic because $\sqrt{-1}=0$ in Mathlib. Then $\widehat Y\equiv1$ while $\mu_g=e^{0.5}$, so the MSE is $0.4208>e^{-2}>\varepsilon^2$ for every admissible $\varepsilon$ and every $(L,N)$.
  - The name suggests "Theorem 1" of a source. Its fidelity to that source was not assessed, because no source was read.

---

## Numerical sanity checks

All scripts are in `scratchpad/readback/round8/work_J/`; `defs.py` is a literal float transcription of every packet definition, including $\sqrt{x\le0}=0$ and $\mathbb N$ index arithmetic. Seeds are fixed. Outputs are the matching `*.out` files.

| Statement | Script (section) | Method | Result |
|---|---|---|---|
| T1 `emPath_gbm` | `check_identities.py` (a) | 3000 random inputs, including $h<0$, $n\le40$ | max relative difference $6.7\times10^{-14}$ |
| T2 `gbmExp_eq_prod` | `check_identities.py` (b) | 3000 random inputs | max relative difference $3.9\times10^{-14}$ |
| T3 `gbmExact_pairAvg` | `check_identities.py` (c) | 3000 random inputs with $T<0$, $T=0$, $T>0$ and $\ell\le7$ | max relative difference $3.6\times10^{-15}$ (exactly $0$ for $T\le0$) |
| Unfolding of the T10 estimator | `check_identities.py` (d) | literal `fineCoarseDiff`/`emFine`/`emCoarse`/`europeanPayoff`/`blockMean` compared with $P_\ell$ as rendered in T10 | differences $0$ and $8.7\times10^{-19}$; `blockMean` with $N=0$ returns $0$ |
| T4 `map_gbmExact` | `check_identities.py` (e) | two-sample KS test, 20000 draws each, 3 sets (incl. $r<0$, $\sigma<0$, $s_0<0$) | $D=0.011,\,0.006,\,0.009$ (critical $0.0136$); sample means match $s_0e^{rT}$ |
| T5 per-factor moments | `check_sq_prod.py` (1) | 1-D Simpson quadrature, 8 sets (e.g. $r=-5$, $\sigma=4$, $h=1$) | max relative difference $1.7\times10^{-14}$ |
| T5 whole integrand | `check_sq_prod.py` (2) | direct 1-D quadrature ($n=1$) and 2-D quadrature ($n=2$), 5 sets | relative difference $\le3.6\times10^{-11}$ |
| T5 whole integrand | `check_sq_prod.py` (3) | Monte Carlo, $4\times10^5$ draws, $n=3,\dots,10$, 6 sets | every set within $1.05$ SE of the formula |
| T5 with $h<0$ | `check_sq_prod.py` (4) | literal (deterministic) left side vs formula | formula wrong, e.g. $2.63\times10^{-3}$ vs $4.84\times10^{-3}$ |
| T6 exact ratio, grid | `check_strong.py` A | 9600 cases, 110-digit decimals; $r\in[-20,20]$, $\sigma\in[0,8]$, $h\in[10^{-5},5]$, $n\le10^4$ | 0 violations; max ratio $0.0952$; 0 violations of the two proof-sketch inequalities |
| T6 exact ratio, search | `check_strong.py` B, C | 20000 log-uniform draws plus local maximisation | 0 violations; max ratio $0.0947$ (random) and $0.1000$ (optimised, at $r\approx0$, $h\approx1.4\times10^{-8}$, $\sigma^2nh\approx3.7\times10^3$) |
| T7 exact table | `check_strong.py` D | 7 sets × $\ell\in\{0,\dots,12\}$ (incl. $T=0$, $s_0=-2$, $r=-5$, $\sigma=3$) | ratios from $4\times10^{-21}$ to $0.091$; $T=0$ gives $0\le0$ |
| T7 literal left side | `check_strong.py` E | Monte Carlo, $10^5$ draws, literal definitions | agrees with the exact value within 3 SE (4 sets) |
| T6/T7 without the sign hypothesis | `check_strong.py` F | $h=-0.1,-0.2$; $T=-0.1,-0.5$ | left side exceeds right side in every case (statements false) |
| T8 weak error | `check_weak_var.py` | Monte Carlo, calls and $g=\mathrm{id}$, 5 sets ($r\in\{-1,-0.5,0,0.05,2\}$, $\sigma$ up to $1.5$), $\ell=0..6$; exact target from the Black–Scholes formula without discount, cross-checked by quadrature | $\lvert\text{weak error}\rvert\le0.055\times$ bound in all cases |
| T9 correction variance | `check_weak_var.py` | Monte Carlo, $2\times10^4$ draws per level, $\ell=0..6$, same 5 sets | variance / bound $\le1.13\times10^{-2}$ |
| T8–T10 without $0\le T$ | `check_hyp_dropped.py` | $T=-0.1$ (T8, T9) and $T=-1$ (T10), literal definitions | all three statements false (see Concerns) |
| T10 construction | `check_mlmc.py` (1) | $(L,N)$ from the proved constants, 4001 values $\varepsilon\in[10^{-15},e^{-1})$ | MSE bound $<\varepsilon^2$ everywhere; cost$/(\varepsilon^{-2}\ln^2\varepsilon)\le120.1$, tending to about $46$ |
| T10 empirical | `check_mlmc.py` (2) | 400 / 200 / 60 independent runs at $\varepsilon=0.2$ / $0.1$ / $0.05$; fast estimator checked against the literal one | empirical MSE $2.3\times10^{-5}$ / $4.7\times10^{-6}$ / $1.3\times10^{-6}$, far below $\varepsilon^2$ |

The numerical evidence agrees with every truth verdict above. It also locates the tightest case of the strong-error constant: a ratio of about $1/10$, approached at $r=0$ with small steps and long horizons. No numerical result contradicts any statement.
