# Read-back audit: packet I (`packet_I_tau_leaping_mlmc.lean`)

| | |
|---|---|
| **Date** | 2026-09-28 |
| **Packet** | `scratchpad/readback/round7/packet_I_tau_leaping_mlmc.lean` (78 lines, namespace `MLMC`, module header `MlmcLean.TauLeapingMLMC`) |
| **Declarations audited** | **17** in total: **12 definitions** (4 in the module: `tauLevelLaw`, `tauInputLaw`, `tauFine`, `tauCoarse`; 8 appended from other modules: `blockMean`, `fineCoarseDiff`, `tauChain`, `coupledChain`, `tauStep`, `coupledTwoStep`, `coupledIncr`, `couplePair`) and **5 theorems** (`lintegral_sq_tauChain_lt_top`, `integral_tauFine`, `integral_tauCoarse`, `variance_tauCorrection_le`, `tauLeaping_mlmc_theorem1`) |
| **Auditor** | independent blind auditor (sub-agent) |
| **Files opened** | the packet; `prove2me_workspace/references/mission_auditor.md`; Mathlib sources under `.lake/packages/mathlib/Mathlib` (only to confirm conventions). No project sources, papers, notes, README/PLAN, git history or other packets or outputs were opened. |
| **Numerical work** | `scratchpad/readback/round7/work_I/` (pure Python 3.11, standard library only). The scripts and their outputs are listed in Part 3. |

**Rules followed** (from `mission_auditor.md` and the task brief):
1. I translated the code, not the intent. Declaration and file names were not used as evidence of meaning.
2. Every binder is named, whether explicit, implicit or instance.
3. Every packet definition is unfolded inline.
4. Degenerate cases and Lean junk values are brought to the surface.
5. The exact strength of each relation (for example $<$ versus $\le$) and the quantifier order are kept, including which constants may depend on which data.
6. Renderings contain no judgement. Truth, non-vacuity, junk values and concerns are assessed separately in Part 2.
7. Lean was not run. Casts, precedence and elaboration were read from the source and checked against the Mathlib notation declarations.

---

## Summary

- **17 declarations** (12 definitions, 5 theorems). **All 5 theorems appear true as stated.** None is vacuous: for each theorem there are instances where all hypotheses hold and the conclusion is non-trivial. **None holds only because of a junk value.** Proof sketches are in Part 2 and numerical confirmation is in Part 3.
- **Main points for a human auditor:**
  1. **A hidden junk channel that does not fire.** `tauInputLaw` is Mathlib's `Measure.infinitePi`. By definition it is the **zero measure unless every factor is a probability measure** (`Probability/ProductMeasure.lean:358-362`). Every level law here is a probability measure, because every map starts from the countable discrete space $\mathbb N$ or $\mathbb N\times\mathbb N$ and Poisson laws are probability measures. So the product is genuine. The packet itself never states this fact. If it failed, `variance_tauCorrection_le` and `tauLeaping_mlmc_theorem1` would hold trivially (variance 0, and a mean-square-error integral of 0).
  2. **The Lipschitz hypothesis on $\lambda$ is redundant.** On $\mathbb N$ a function with values in $[0,\Lambda]$ is automatically $\Lambda$-Lipschitz, because distinct naturals are at distance at least 1. So `hK` always holds with $K=\Lambda$, and both theorems that assume it are really statements about bounded $\lambda$.
  3. **`tauLeaping_mlmc_theorem1` assumes the weak-error rate rather than proving it.** The hypothesis `hweak` requires $|E_\ell-P|\le c_1 2^{-\alpha\ell}$ with $\alpha\ge \tfrac12$ toward an arbitrary real $P$, where $E_\ell=\int\Phi\,d\mu^{\lambda,T/2^\ell,x_0}_{2^\ell}$ is the expectation under `tauChain`. It forces $P=\lim_\ell E_\ell$. No continuous-time process appears anywhere in the packet.
  4. Several modelling choices are hard-coded in the statements:
     - the cost functional $\sum_\ell N_\ell 2^\ell$;
     - the variance rate $2^{-\ell}$ (written `-(1 * ℓ)`);
     - the fixed estimator structure: independent full input sequences for each index $(\ell,n)$.

     The constant $c_4$ may depend on all the data ($\lambda,K,\Lambda,T,x_0,\Phi,L_\Phi,P,\alpha,c_1$); it is uniform only in $\varepsilon$.
  5. `integral_tauFine` and `integral_tauCoarse` have **no hypotheses**. For unbounded $\lambda$ and fast-growing $\Phi$, both sides can be the Bochner junk value $0$. The identity then still holds, as a consequence of an identity between image laws.
  6. `lintegral_sq_tauChain_lt_top` states **finiteness only**: the bound is neither quantitative nor uniform in $n$. Its boundedness hypothesis is genuinely needed; a counterexample without it is given in Part 2.
  7. **Numerics** use exact truncated laws accurate to about $10^{-14}$:
     - the marginal identities hold, with total-variation distance at most $1.6\times10^{-14}$;
     - $2^\ell\,\mathrm{Var}(D_\ell)$ converges to positive constants, so the $2^{-\ell}$ rate is attained and sharp;
     - the weak error is $\approx 1.129\cdot 2^{-\ell}$ for $\lambda(x)=\min(x,5)+1$;
     - the constructive allocation gives $\text{MSE}<\varepsilon^2$ with $\text{cost}/(\varepsilon^{-2}\log^2\varepsilon)\le 141$ for $\varepsilon\in[10^{-4},0.35]$ (level variances beyond $\ell=10$ extrapolated);
     - a Monte Carlo run of the actual estimator reproduces the mean-square-error formula (for example $2.75\times10^{-3}$ empirical against $2.79\times10^{-3}$ predicted at $\varepsilon=0.1$).

---

## Mathlib conventions confirmed

Paths are relative to `.lake/packages/mathlib/Mathlib`.

| Concept | Convention (as read in source) | Location |
|---|---|---|
| `poissonMeasure r` ($r\in\mathbb R_{\ge0}$) | $\sum_n \mathrm{ofReal}(e^{-r} r^n/n!)\,\delta_n$ on $\mathbb N$. Here $r^n$ is a monoid power, so $0^0=1$ and $\mathrm{Po}(0)=\delta_0$. | `Probability/Distributions/Poisson/Basic.lean:41-42` |
| Poisson is a probability measure | instance | `…/Poisson/Basic.lean:68` |
| Poisson convolution | $\mathrm{Po}(r_1)*\mathrm{Po}(r_2)=\mathrm{Po}(r_1+r_2)$ | `…/Poisson/Basic.lean:178` |
| `Measure.map f μ` | `if AEMeasurable f μ then mapₗ (mk f) μ else 0`, so **the pushforward along a non-a.e.-measurable map is 0** | `MeasureTheory/Measure/Map.lean:91-93`, `:112` (`map_of_not_aemeasurable`) |
| `Measure.bind m f` | `join (map f m)`: the mixture $\int f(a)\,m(da)$ if $f$ is measurable, **and 0 if $f$ is not a.e.-measurable** (because `map` is then 0) | `MeasureTheory/Measure/GiryMonad.lean:228-229`; `join` at `:125` |
| Measurability on $\mathbb N$, $\mathbb N\times\mathbb N$ | $\mathbb N$ has σ-algebra $\top$. Every map out of a countable space with measurable singletons is measurable. $\mathbb N\times\mathbb N$ has measurable singletons. | `MeasureTheory/MeasurableSpace/Instances.lean:30`; `MeasurableSpace/Basic.lean:287` (`measurable_of_countable`); `MeasurableSpace/Constructions.lean:475` |
| `Measure.prod μ ν` | `bind μ (x ↦ map (Prod.mk x) ν)`; a product of probability measures is a probability measure | `MeasureTheory/Measure/Prod.lean:171`, `:322` |
| `Measure.infinitePi μ` | `if ∀ i, IsProbabilityMeasure (μ i) then` (the Carathéodory extension of the cylinder content) `else 0`. **It takes no instance argument, so it is the zero measure if some factor is not a probability measure.** | `Probability/ProductMeasure.lean:358-362` |
| `infinitePi` facts | probability instance (needs all factors to be probability measures); `infinitePi_pi` (value on finite boxes); `infinitePi_map_eval` (coordinate $i$ has law $\mu_i$) | `ProductMeasure.lean:381`, `:405`, `:481` |
| Independence of `infinitePi` coordinates | `iIndepFun_infinitePi` | `Probability/Independence/InfinitePi.lean:127` |
| Bochner `∫ x, f x ∂μ` | `if CompleteSpace G then (if Integrable f μ then L1.integral … else 0) else 0`, so **the integral of a non-integrable function is 0**. The integral against the zero measure is 0. | `MeasureTheory/Integral/Bochner/Basic.lean:156-159`, `:202` (`integral_undef`), `:982` |
| `integral_map` | $\int f\,d(\varphi_\#\mu)=\int f\circ\varphi\,d\mu$ for a.e.-measurable $\varphi$ and a.e.-strongly-measurable $f$; **no integrability assumption** | `Bochner/Basic.lean:1043` |
| Integral notation | `∫ x, r ∂μ`: the body is parsed at precedence 60 and the measure at 70, so `∫ x, Φ x ∂(μ) - P` means $(\int\Phi\,d\mu)-P$ | `Bochner/Basic.lean:166`; `Lebesgue/Basic.lean:56` for `∫⁻` |
| `lintegral` | supremum of the integrals of simple functions below $f$; always defined in $[0,\infty]$, with no junk value | `MeasureTheory/Integral/Lebesgue/Basic.lean:48-49` |
| `variance X μ` | `(evariance X μ).toReal` with `evariance X μ = ∫⁻ ‖X ω - μ[X]‖ₑ^2 ∂μ`. Since $\infty.\mathrm{toReal}=0$, **the variance of a non-$L^2$ variable is 0**. The variance is always $\ge 0$. | `Probability/Moments/Variance.lean:58`, `:64`, `:132-134`, `:202`; `Data/ENNReal/Basic.lean:283` (`toReal_top`) |
| `Real.rpow` | $x^y=\mathrm{Re}((x:\mathbb C)^{(y:\mathbb C)})$, which equals $\exp(y\log x)$ for $x>0$; $x^{-y}=(x^y)^{-1}$ for $x\ge0$ | `Analysis/SpecialFunctions/Pow/Real.lean:35`, `:51`, `:259` |
| `Real.log` | $\log 0=0$ and $\log x=\log\lvert x\rvert$; the ordinary logarithm on $(0,\infty)$ | `Analysis/SpecialFunctions/Log/Basic.lean:44-45`, `:103` |
| `ℝ≥0` arithmetic | a semifield, so $a/0=0$ (`div_zero`); subtraction is truncated, $r-p=\max(r-p,0)$ | `Data/NNReal/Defs.lean:113`, `:745`; `Algebra/GroupWithZero/Basic.lean:407` |
| Real inverse | $0^{-1}=0$ (`inv_zero`), which is relevant to `blockMean` with $N=0$ | `Algebra/GroupWithZero/Defs.lean:236` |
| Big-sum notation | `∑ x ∈ s, body` parses `body` at precedence 67, above `-` (65) and below `*` (70). So `∑ ℓ ∈ range (L+1), a ℓ - P` means $(\sum_\ell a_\ell)-P$, and `∑ ℓ ∈ …, (N ℓ:ℝ) * 2^ℓ ≤ …` means $(\sum_\ell N_\ell 2^\ell)\le\dots$ | `Algebra/BigOperators/Group/Finset/Defs.lean:181` |

Cast and elaboration notes (read from the code):
- In `hK` and `hΦ`, `(x : ℝ) - y` is **real** subtraction, not natural-number subtraction. The coefficient `K : ℝ≥0` is cast to $\mathbb R$.
- `1 / 2 ≤ α` is real division, so the condition is $\alpha\ge 0.5$.
- `(2:ℝ) ^ (-(α * ℓ))`, `(2:ℝ) ^ (-(1 * ℓ))` and `ε ^ (-2 : ℝ)` are real powers (`rpow`) with positive bases.
- `ε ^ 2`, `x ^ 2` and `(N ℓ : ℝ) * 2 ^ ℓ` are monoid powers.
- `Real.log ε ^ 2` is $(\log\varepsilon)^2$.
- `T / 2 ^ ℓ` is computed in $\mathbb R_{\ge0}$ with a non-zero denominator. The last argument of `tauChain`, written `(2 ^ ℓ)`, is a natural number.

---

## Notation used below

| Symbol | Lean | Meaning (unfolded in each rendering) |
|---|---|---|
| $\mathrm{Po}(r)$ | `poissonMeasure r` | Poisson measure on $\mathbb N$: $\mathrm{Po}(r)(\{n\})=e^{-r}r^n/n!$, with $\mathrm{Po}(0)=\delta_0$ |
| $\pi_1,\pi_2$ | `.1`, `.2` | coordinate projections $\mathbb N\times\mathbb N\to\mathbb N$ |
| $c_{a,b}$ | `couplePair a b` | D1 |
| $Q_{a,b}$ | `coupledIncr a b` | D2 |
| $S_{\lambda,h}(x)$ | `tauStep lam h x` | D3 |
| $R_{\lambda,h}(s)$ | `coupledTwoStep lam h s` | D4 |
| $\mu^{\lambda,h,x_0}_n$ | `tauChain lam h x₀ n` | D5 |
| $\nu^{\lambda,h,x_0}_k$ | `coupledChain lam h x₀ k` | D6 |
| $\rho^{\lambda,T,x_0}_\ell$ | `tauLevelLaw lam T x₀ ℓ` | D9 |
| $\Pi_{\lambda,T,x_0}$ | `tauInputLaw lam T x₀` | D10 |
| $D_\ell$ | `fineCoarseDiff (tauFine Φ) (tauCoarse Φ) ℓ` | D7, D11 and D12 combined: $D_0(y)=\Phi(\pi_1 y_0)$ and $D_{\ell+1}(y)=\Phi(\pi_1 y_{\ell+1})-\Phi(\pi_2 y_{\ell+1})$ |

---

# Part 1: Renderings (no judgement)

The appended building blocks come first, then the module definitions, then the theorems. Packet line numbers are given for each declaration.

### D1. `couplePair` (packet lines 77–78, from `MlmcLean.PoissonCoupling`)

For $a,b\in\mathbb R_{\ge0}$ and $p=(p_1,p_2)\in\mathbb N\times\mathbb N$,
$$
c_{a,b}(p_1,p_2)\;=\;\bigl(p_1+\mathbf 1[b<a]\,p_2,\;\;p_1+\mathbf 1[a<b]\,p_2\bigr)\in\mathbb N\times\mathbb N .
$$
Explicitly, the value is $(p_1+p_2,\,p_1)$ if $a>b$, $(p_1,\,p_1+p_2)$ if $a<b$, and $(p_1,p_1)$ if $a=b$. In the last case $p_2$ is ignored.

### D2. `coupledIncr` (lines 73–74)

For $a,b\in\mathbb R_{\ge0}$, $Q_{a,b}$ is a measure on $\mathbb N\times\mathbb N$. It is the image, under $c_{a,b}$ (D1), of the product measure
$$
\mathrm{Po}\bigl(\min(a,b)\bigr)\otimes\mathrm{Po}\bigl(\max(a,b)-\min(a,b)\bigr).
$$
The subtraction is taken in $\mathbb R_{\ge0}$ and truncated at $0$. Since $\max\ge\min$, it equals $|a-b|$. Equivalently, $Q_{a,b}$ is the law of $c_{a,b}(U,V)$ where $U\sim\mathrm{Po}(\min(a,b))$ and $V\sim\mathrm{Po}(\max(a,b)-\min(a,b))$ are independent. The image is Mathlib's `Measure.map`; the map $c_{a,b}$ has the countable discrete domain $\mathbb N\times\mathbb N$.

### D3. `tauStep` (lines 63–64)

For $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $h\in\mathbb R_{\ge0}$ and $x\in\mathbb N$, $S_{\lambda,h}(x)$ is the image of $\mathrm{Po}(h\,\lambda(x))$ under $k\mapsto x+k$. The product $h\lambda(x)$ is taken in $\mathbb R_{\ge0}$. In other words, $S_{\lambda,h}(x)$ is the law of $x+K$ with $K\sim\mathrm{Po}(h\lambda(x))$.

### D4. `coupledTwoStep` (lines 67–70)

For $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $h\in\mathbb R_{\ge0}$ and $s=(s_1,s_2)\in\mathbb N\times\mathbb N$, $R_{\lambda,h}(s)$ is the measure on $\mathbb N\times\mathbb N$ given by the Mathlib `bind`:
$$
R_{\lambda,h}(s)\;=\;\int_{\mathbb N\times\mathbb N}\Bigl[(i',j')\mapsto (s_1+i+i',\;s_2+j+j')\Bigr]_{\#}\,Q_{\,h\lambda(s_1+i),\;h\lambda(s_2)}\;\;Q_{\,h\lambda(s_1),\;h\lambda(s_2)}\bigl(d(i,j)\bigr).
$$
Here $[\cdot]_\#$ denotes the image measure. Equivalently, it is the law of $(s_1+I+I',\;s_2+J+J')$, built in two draws:
- first, $(I,J)\sim Q_{h\lambda(s_1),\,h\lambda(s_2)}$;
- then, conditionally on $(I,J)$, $(I',J')\sim Q_{h\lambda(s_1+I),\,h\lambda(s_2)}$.

In both draws the second rate argument is $h\lambda(s_2)$, with $\lambda$ evaluated at the original $s_2$.

### D5. `tauChain` (lines 53–55)

For $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $h\in\mathbb R_{\ge0}$, $x_0\in\mathbb N$ and $n\in\mathbb N$, the measures $\mu^{\lambda,h,x_0}_n$ on $\mathbb N$ are defined by recursion on $n$:
$$
\mu_0=\delta_{x_0},\qquad \mu_{n+1}=\mathrm{bind}(\mu_n,S_{\lambda,h}),\quad\text{i.e.}\quad \mu_{n+1}(\{y\})=\sum_{x\in\mathbb N}\mu_n(\{x\})\,S_{\lambda,h}(x)(\{y\}).
$$
So $\mu_n$ is the law of $X_n$ for the chain $X_0=x_0$, $X_{k+1}=X_k+K_k$, where conditionally on the past $K_k\sim\mathrm{Po}(h\lambda(X_k))$.

### D6. `coupledChain` (lines 58–60)

For $\lambda$, $h$, $x_0$ as above and $k\in\mathbb N$, the measures $\nu^{\lambda,h,x_0}_k$ on $\mathbb N\times\mathbb N$ are defined by
$$
\nu_0=\delta_{(x_0,x_0)},\qquad \nu_{k+1}=\mathrm{bind}(\nu_k,R_{\lambda,h}),\quad\text{i.e.}\quad \nu_{k+1}(\{t\})=\sum_{s}\nu_k(\{s\})\,R_{\lambda,h}(s)(\{t\}),
$$
with $R_{\lambda,h}$ from D4.

### D7. `fineCoarseDiff` (lines 48–50, from `MlmcLean.Corrections`)

Let $\Omega_0$ be an arbitrary type. It is an implicit argument, and its binder is not displayed in the packet. Given two families $P^{\mathrm f},P^{\mathrm c}:\mathbb N\to(\Omega_0\to\mathbb R)$, the declaration defines the family $\mathrm{fcd}(P^{\mathrm f},P^{\mathrm c}):\mathbb N\to(\Omega_0\to\mathbb R)$ by
$$
\mathrm{fcd}_0=P^{\mathrm f}_0,\qquad \mathrm{fcd}_{\ell+1}(y)=P^{\mathrm f}_{\ell+1}(y)-P^{\mathrm c}_{\ell}(y)\quad(y\in\Omega_0).
$$

### D8. `blockMean` (lines 44–45, from `MlmcLean.SampleMean`)

Let $\iota,\Omega_0,\Omega$ be arbitrary types (implicit; their binders are not displayed in the packet). Take $f:\iota\to\Omega_0\to\mathbb R$, $\omega:\iota\times\mathbb N\to\Omega\to\Omega_0$, $i\in\iota$, $N\in\mathbb N$ and $x\in\Omega$. Then
$$
\mathrm{blockMean}(f,\omega,i,N,x)\;=\;N^{-1}\sum_{n=0}^{N-1} f_i\bigl(\omega_{(i,n)}(x)\bigr),
$$
where $N$ is cast to $\mathbb R$ and $0^{-1}=0$. For $N=0$ the sum is empty and the value is $0$.

### D9. `tauLevelLaw` (lines 5–7)

For $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $T\in\mathbb R_{\ge0}$ and $x_0\in\mathbb N$, this is a sequence of measures $\rho^{\lambda,T,x_0}_\ell$ on $\mathbb N\times\mathbb N$ indexed by $\ell\in\mathbb N$:
- $\rho_0$ is the image of $\mu^{\lambda,T,x_0}_1$ under $x\mapsto(x,x)$. Here $\mu_1=\mathrm{bind}(\delta_{x_0},S_{\lambda,T})$, the law of $x_0+\mathrm{Po}(T\lambda(x_0))$. So $\rho_0$ is the law of $(X,X)$ with $X=x_0+K$ and $K\sim\mathrm{Po}(T\lambda(x_0))$.
- $\rho_{\ell+1}=\nu^{\lambda,\,T/2^{\ell+1},\,x_0}_{2^\ell}$. This is the law after $2^\ell$ steps of the kernel $R_{\lambda,h}$ (D4) started at $(x_0,x_0)$, with $h=T/2^{\ell+1}$ computed in $\mathbb R_{\ge0}$.

### D10. `tauInputLaw` (lines 8–9)

For $\lambda$, $T$ and $x_0$, $\Pi_{\lambda,T,x_0}$ is Mathlib's `Measure.infinitePi` of the family $(\rho^{\lambda,T,x_0}_\ell)_{\ell\in\mathbb N}$ (D9). It is a measure on sequences $y=(y_\ell)_{\ell\in\mathbb N}\in(\mathbb N\times\mathbb N)^{\mathbb N}$, with the product σ-algebra. By Mathlib's definition:
- if every $\rho_\ell$ is a probability measure, it is the unique measure with $\Pi\bigl(\{y:\ y_\ell\in A_\ell\ \forall \ell\in F\}\bigr)=\prod_{\ell\in F}\rho_\ell(A_\ell)$ for every finite $F\subset\mathbb N$ and all sets $A_\ell\subseteq\mathbb N\times\mathbb N$;
- otherwise it is the zero measure.

### D11. `tauFine` (line 10)

For $\Phi:\mathbb N\to\mathbb R$, $\ell\in\mathbb N$ and $y\in(\mathbb N\times\mathbb N)^{\mathbb N}$:
$$
\mathrm{tauFine}(\Phi,\ell,y)=\Phi\bigl(\pi_1(y_\ell)\bigr),
$$
that is, $\Phi$ applied to the first component of the $\ell$-th entry of $y$.

### D12. `tauCoarse` (line 11)

For $\Phi:\mathbb N\to\mathbb R$, $\ell\in\mathbb N$ and $y\in(\mathbb N\times\mathbb N)^{\mathbb N}$:
$$
\mathrm{tauCoarse}(\Phi,\ell,y)=\Phi\bigl(\pi_2(y_{\ell+1})\bigr),
$$
that is, $\Phi$ applied to the second component of the $(\ell+1)$-st entry of $y$.

Consequently, with D7, $D_\ell:=\mathrm{fcd}_\ell(\mathrm{tauFine}(\Phi,\cdot),\mathrm{tauCoarse}(\Phi,\cdot))$ satisfies
$$
D_0(y)=\Phi(\pi_1 y_0),\qquad D_{\ell+1}(y)=\Phi(\pi_1 y_{\ell+1})-\Phi(\pi_2 y_{\ell+1}).
$$

---

### T1. `lintegral_sq_tauChain_lt_top` (lines 12–13)

**Binders and hypotheses.**
- A function $\lambda:\mathbb N\to\mathbb R_{\ge0}$ (implicit).
- A number $\Lambda\in\mathbb R_{\ge0}$ (implicit).
- Hypothesis $h_\Lambda$: $\lambda(x)\le\Lambda$ for every $x\in\mathbb N$.
- A step $h\in\mathbb R_{\ge0}$ and a start $x_0\in\mathbb N$ (explicit).

**Conclusion.** For every $n\in\mathbb N$,
$$
\int_{\mathbb N}\mathrm{ofReal}\bigl(x^2\bigr)\;\mu^{\lambda,h,x_0}_n(dx)\;<\;\infty .
$$
This is the Lebesgue integral in $[0,\infty]$. The natural number $x$ is cast to $\mathbb R$, squared and embedded in $[0,\infty]$. Because the space is $\mathbb N$, this says $\sum_{x\in\mathbb N}x^2\,\mu_n(\{x\})<\infty$. The measures are unfolded as follows:
- $\mu_0=\delta_{x_0}$;
- $\mu_{m+1}(\{y\})=\sum_x\mu_m(\{x\})\,\mathrm{Po}(h\lambda(x))(\{y-x\})$, where the term is $0$ for $y<x$.

### T2. `integral_tauFine` (lines 14–16)

**Binders.** $\lambda:\mathbb N\to\mathbb R_{\ge0}$, $T\in\mathbb R_{\ge0}$, $x_0\in\mathbb N$, $\Phi:\mathbb N\to\mathbb R$ and $\ell\in\mathbb N$, all explicit. There are no hypotheses.

**Conclusion.**
$$
\int_{(\mathbb N\times\mathbb N)^{\mathbb N}}\Phi\bigl(\pi_1(y_\ell)\bigr)\;\Pi_{\lambda,T,x_0}(dy)\;=\;\int_{\mathbb N}\Phi(x)\;\mu^{\lambda,\,T/2^\ell,\,x_0}_{2^\ell}(dx).
$$
Both sides are Bochner integrals, each defined to be $0$ if its integrand is not integrable. The right-hand side uses step size $T/2^\ell$ (in $\mathbb R_{\ge0}$) and $2^\ell$ steps.

Unfolded:
- $\Pi$ is the infinite product of the $\rho_\ell$, or the zero measure if some $\rho_\ell$ is not a probability measure.
- $\rho_0$ is the law of $(X,X)$ with $X=x_0+\mathrm{Po}(T\lambda(x_0))$.
- $\rho_{m+1}$ is the law after $2^m$ steps of $R_{\lambda,T/2^{m+1}}$ from $(x_0,x_0)$. One step of $R_{\lambda,h}$ from $(s_1,s_2)$ goes to $(s_1+I+I',\,s_2+J+J')$, with $(I,J)\sim Q_{h\lambda(s_1),h\lambda(s_2)}$ and then $(I',J')\sim Q_{h\lambda(s_1+I),h\lambda(s_2)}$.
- $Q_{a,b}$ is the law of $(U+\mathbf 1[b<a]V,\ U+\mathbf 1[a<b]V)$ with $U\sim\mathrm{Po}(\min(a,b))$ and $V\sim\mathrm{Po}(\max(a,b)-\min(a,b))$ independent.
- $\mu^{\lambda,h,x_0}_n$ is the law after $n$ steps $x\mapsto x+\mathrm{Po}(h\lambda(x))$ from $x_0$.

### T3. `integral_tauCoarse` (lines 17–19)

**Binders.** The same as T2: $\lambda,T,x_0,\Phi,\ell$, all explicit, with no hypotheses.

**Conclusion.**
$$
\int_{(\mathbb N\times\mathbb N)^{\mathbb N}}\Phi\bigl(\pi_2(y_{\ell+1})\bigr)\;\Pi_{\lambda,T,x_0}(dy)\;=\;\int_{\mathbb N}\Phi(x)\;\mu^{\lambda,\,T/2^\ell,\,x_0}_{2^\ell}(dx).
$$
Both sides are Bochner integrals (0 if not integrable). The left side reads the **second** component of the entry with index $\ell+1$. That entry has law $\rho_{\ell+1}=\nu^{\lambda,T/2^{\ell+1},x_0}_{2^\ell}$, unfolded as in T2. The right side uses step size $T/2^\ell$ and $2^\ell$ steps.

### T4. `variance_tauCorrection_le` (lines 20–26)

**Binders and hypotheses.**
- $\lambda:\mathbb N\to\mathbb R_{\ge0}$ (implicit) and $K,\Lambda\in\mathbb R_{\ge0}$ (implicit).
- $h_K$: for all $x,y\in\mathbb N$, $|\lambda(x)-\lambda(y)|\le K\,|x-y|$. Values are cast to $\mathbb R$ and the subtraction is real.
- $h_\Lambda$: $\lambda(x)\le\Lambda$ for all $x\in\mathbb N$.
- $T\in\mathbb R_{\ge0}$ and $x_0\in\mathbb N$ (explicit).
- $\Phi:\mathbb N\to\mathbb R$ (implicit) and $L_\Phi\in\mathbb R$ (implicit).
- $h_\Phi$: for all $x,y\in\mathbb N$, $|\Phi(x)-\Phi(y)|\le L_\Phi\,|x-y|$ (real).

**Conclusion.** There exists $c_2\in\mathbb R$ with $c_2>0$ such that for every $\ell\in\mathbb N$
$$
\mathrm{Var}_{\Pi_{\lambda,T,x_0}}\bigl(D_\ell\bigr)\;\le\;c_2\cdot 2^{-(1\cdot\ell)},
$$
where the power is a real power.

Unfolded:
- $D_0(y)=\Phi(\pi_1 y_0)$ and $D_{\ell+1}(y)=\Phi(\pi_1 y_{\ell+1})-\Phi(\pi_2 y_{\ell+1})$.
- $\mathrm{Var}_\Pi(X)$ is Mathlib's `variance`: the real number $\mathrm{toReal}\bigl(\int^{[0,\infty]}|X-\textstyle\int X\,d\Pi|^2\,d\Pi\bigr)$, where $\int X\,d\Pi$ is the Bochner integral and $\mathrm{toReal}(\infty)=0$.
- $\Pi$ and the $\rho_\ell$ are as in T2.

**Quantifier order.** $c_2$ is chosen after $\lambda,K,\Lambda,T,x_0,\Phi,L_\Phi$ (and the hypotheses) and before $\ell$. So $c_2$ may depend on all of these but not on $\ell$.

### T5. `tauLeaping_mlmc_theorem1` (lines 27–39)

**Binders and hypotheses.**
- $\lambda:\mathbb N\to\mathbb R_{\ge0}$ and $K,\Lambda\in\mathbb R_{\ge0}$ (implicit), with $h_K$ and $h_\Lambda$ exactly as in T4.
- $T\in\mathbb R_{\ge0}$ and $x_0\in\mathbb N$ (explicit).
- $\Phi:\mathbb N\to\mathbb R$ and $L_\Phi\in\mathbb R$ (implicit), with $h_\Phi$ as in T4.
- $P\in\mathbb R$ (explicit).
- $\alpha,c_1\in\mathbb R$ (implicit), with $h_\alpha$: $\tfrac12\le\alpha$, and $h_{c_1}$: $0<c_1$.
- $h_{\mathrm{weak}}$: for every $\ell\in\mathbb N$,
$$
\Bigl|\int_{\mathbb N}\Phi(x)\,\mu^{\lambda,\,T/2^\ell,\,x_0}_{2^\ell}(dx)\;-\;P\Bigr|\;\le\;c_1\cdot 2^{-\alpha\ell}.
$$
Here the integral is a Bochner integral (0 if not integrable) and the power is a real power.

**Conclusion.** There exists $c_4\in\mathbb R$ with $c_4>0$ such that for every real $\varepsilon$ with $0<\varepsilon<e^{-1}$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ satisfying all three of:
1. $N(\ell)>0$ for **every** $\ell\in\mathbb N$;
2. the integral bound
$$
\int\Biggl(\;\sum_{\ell=0}^{L}\;N(\ell)^{-1}\sum_{n=0}^{N(\ell)-1}D_\ell\bigl(x_{(\ell,n)}\bigr)\;-\;P\Biggr)^{2}\;\Pi^{\otimes(\mathbb N\times\mathbb N)}_{\lambda,T,x_0}(dx)\;<\;\varepsilon^2;
$$
3. the sum bound
$$
\sum_{\ell=0}^{L}N(\ell)\cdot 2^{\ell}\;\le\;c_4\cdot\bigl(\varepsilon^{-2}\cdot(\log\varepsilon)^2\bigr).
$$

Unfolded:
- $\Pi^{\otimes(\mathbb N\times\mathbb N)}_{\lambda,T,x_0}$ is Mathlib's `infinitePi` over the index set $\mathbb N\times\mathbb N$ with every factor equal to $\Pi_{\lambda,T,x_0}$ (D10). Its points are families $x=(x_{(\ell,n)})_{(\ell,n)\in\mathbb N\times\mathbb N}$ with each $x_{(\ell,n)}\in(\mathbb N\times\mathbb N)^{\mathbb N}$. As with D10, it is the zero measure if $\Pi_{\lambda,T,x_0}$ is not a probability measure.
- The inner expression is `blockMean` (D8) with $\omega_{(\ell,n)}(x)=x_{(\ell,n)}$ and $f=D$.
- $D_0(y)=\Phi(\pi_1 y_0)$ and $D_{\ell+1}(y)=\Phi(\pi_1 y_{\ell+1})-\Phi(\pi_2 y_{\ell+1})$.
- $P$ is subtracted **after** the sum over $\ell$.
- The integral in item 2 is a Bochner integral (0 if not integrable).
- $\varepsilon^{-2}$ is a real power, $\log$ is `Real.log`, and $e^{-1}$ is `Real.exp (-1)`.
- $\Pi$, $\rho_\ell$, $R$, $Q$ and $\mu$ are as unfolded in T2.

**Quantifier order.** $c_4$ may depend on $\lambda,K,\Lambda,T,x_0,\Phi,L_\Phi,P,\alpha,c_1$ (and the hypotheses) but not on $\varepsilon$. $L$ and $N$ may depend on $\varepsilon$ and on all of the above.

---

# Part 2: Assessment of the theorems

Facts A1–A7 used below are proved in the Appendix and checked numerically in Part 3.

### T1. `lintegral_sq_tauChain_lt_top`

- **Truth: true.** Each $\mu_n$ is a probability measure on $\mathbb N$ (A4). Let $M_n=\sum_x x^2\mu_n(\{x\})\in[0,\infty]$. For $K\sim\mathrm{Po}(r)$, $E(x+K)^2=x^2+2xr+r+r^2$. With $r=h\lambda(x)\le h\Lambda$ and $x\le x^2$ on $\mathbb N$, this gives $M_{n+1}\le(1+2h\Lambda)M_n+h\Lambda+h^2\Lambda^2$, and induction from $M_0=x_0^2$ gives $M_n<\infty$. A sharper statement: $X_n-x_0$ is stochastically dominated by $\mathrm{Po}(nh\Lambda)$, so $M_n\le(x_0+nh\Lambda)^2+nh\Lambda$, with equality when $\lambda\equiv\Lambda$ (confirmed numerically in N2).
- **Non-vacuity.** The only hypothesis is satisfiable. For example, $\lambda\equiv1$ and $\Lambda=1$ give $\mu_n=\text{law of }x_0+\mathrm{Po}(nh)$ and $M_n=(x_0+nh)^2+nh$.
- **Junk values.** None. `lintegral` has no junk value. A trivial "$<\infty$" would need $\mu_n=0$ (a degenerate `bind`/`map`), which does not happen (A4; numerically the total mass is $1\pm10^{-14}$).
- **Concerns.**
  - The statement gives finiteness only, not a quantitative or $n$-uniform bound.
  - The hypothesis $h_\Lambda$ is **not** redundant. Take $\lambda(x)=x!$, $h=1$, $x_0=0$, $n=2$. Then $M_2=\sum_k e^{-1}(k^2+2k\,k!+k!+(k!)^2)/k!=\infty$. The partial sums in N2 reach $10^{32}$ by $k=30$.
  - Edge cases: $h=0$ or $\lambda\equiv0$ gives $\mu_n=\delta_{x_0}$ (because $\mathrm{Po}(0)=\delta_0$); $n=0$ gives $M_0=x_0^2$.

### T2. `integral_tauFine`

- **Truth: true, for every $\lambda,T,x_0,\Phi,\ell$.** The proof has four steps.
  1. Every $\rho_\ell$ is a probability measure (A4), so $\Pi$ is the genuine product measure and the $\ell$-th coordinate has law $\rho_\ell$ (`infinitePi_map_eval`).
  2. The first marginal of $\rho_\ell$ is $\mu^{\lambda,T/2^\ell,x_0}_{2^\ell}$.
     - For $\ell=0$: the first marginal of $\rho_0$ is $\mu^{\lambda,T,x_0}_1$, and $T/2^0=T$, $2^0=1$.
     - For $\ell=m+1$: by A3, the first marginal of $\nu^{\lambda,h,x_0}_k$ is $\mu^{\lambda,h,x_0}_{2k}$. With $h=T/2^{m+1}$ and $k=2^m$, this is $\mu^{\lambda,T/2^{m+1},x_0}_{2^{m+1}}$.
  3. `integral_map` needs no integrability, so $\int\Phi\circ\varphi\,d\Pi=\int\Phi\,d(\varphi_\#\Pi)$ with $\varphi(y)=\pi_1(y_\ell)$.
  4. Combining steps 1–3 gives the identity.
- **Non-vacuity.** There are no hypotheses. A non-trivial instance: $\lambda(x)=\min(x,5)+1$, $T=1$, $x_0=0$, $\Phi=\mathrm{id}$. Both sides equal $E_\ell$ ($1.0,\ 1.24999,\ 1.43862,\dots$), with numerical agreement at the $10^{-14}$ level for $\ell\le9$ (N3).
- **Junk values.** When $\Phi$ is not integrable against the right-hand law, both sides are the Bochner junk value $0$ and the statement reads $0=0$. No hypothesis excludes this, and it can happen for unbounded $\lambda$. Example: $\lambda(x)=x!$, $T=2$, $x_0=0$, $\ell=1$, $\Phi(x)=x^2$, using the divergence shown in T1. It remains a correct consequence of the identity between image laws; it is not a loophole.

  The other junk channel, $\Pi=0$, would make the left side $0$ and the statement false for $\Phi\equiv1$. It does not fire (A4). Under the hypotheses of T4/T5 (bounded $\lambda$, Lipschitz $\Phi$) both sides are genuine (A7).
- **Concerns.**
  - None of substance.
  - At $\ell=0$ the level law is the diagonal image of a one-step law.
  - The statement is about the **first** component of entry $\ell$ only.

### T3. `integral_tauCoarse`

- **Truth: true, for every $\lambda,T,x_0,\Phi,\ell$.** By A3, the second marginal of $\nu^{\lambda,h,x_0}_k$ is $\mu^{\lambda,2h,x_0}_k$. This uses A2: $J$ and $J'$ are independent $\mathrm{Po}(h\lambda(s_2))$ variables, and $\mathrm{Po}(r)*\mathrm{Po}(r)=\mathrm{Po}(2r)$ (`Poisson/Basic.lean:178`). Now set $h=T/2^{\ell+1}$ and $k=2^\ell$. Since $2\cdot(T/2^{\ell+1})=T/2^\ell$ exactly in $\mathbb R_{\ge0}$, the second marginal of $\rho_{\ell+1}$ is $\mu^{\lambda,T/2^\ell,x_0}_{2^\ell}$. The rest of the proof is as in T2 (A4, `infinitePi_map_eval`, `integral_map`).
- **Non-vacuity.** The same instance as T2. The identity is not trivially the same statement as T2 at another index: the first and second components of $\rho_{\ell+1}$ have different laws when $\lambda$ is not constant. For example, $E_1-E_0=0.25$ for $\lambda=\min(x,5)+1$, $x_0=0$, $\Phi=\mathrm{id}$ (N4).
- **Junk values.** As for T2: $0=0$ only in the non-integrable case, which needs unbounded $\lambda$, and $\Pi\neq0$.
- **Concerns.**
  - None of substance.
  - The code shifts the index by one: the second component of entry $\ell+1$ is compared with step size $T/2^\ell$ and $2^\ell$ steps.
  - The second component of $\rho_0$ is never read by any theorem.

### T4. `variance_tauCorrection_le`

- **Truth: true.** The proof sketch has three parts.
  - **Reduction.** $D_\ell$ depends only on $y_\ell$, so $\mathrm{Var}_\Pi(D_\ell)=\mathrm{Var}_{\rho_\ell}$ (A4 and `infinitePi_map_eval`).
  - **Level $0$.** Let $X=x_0+\mathrm{Po}(T\lambda(x_0))$. Then $\mathrm{Var}(\Phi(X))\le E(\Phi(X)-\Phi(x_0))^2\le L_\Phi^2(T\lambda(x_0)+T^2\lambda(x_0)^2)\le L_\Phi^2(T\Lambda+T^2\Lambda^2)$.
  - **Level $\ell+1$.** Let $(F,C)\sim\nu^{\lambda,h,x_0}_{2^\ell}$ with $h=T/2^{\ell+1}$. Then $\mathrm{Var}(D_{\ell+1})\le E(\Phi(F)-\Phi(C))^2\le L_\Phi^2\,E(F-C)^2$.
    - By A5, one step of $R_{\lambda,h}$ changes $e=F-C$ to $e'$ with $E[e'^2\mid F,C]\le(1+a h)e^2+b h^2$, where $a,b$ depend only on $K,\Lambda,T$. This uses $|e|\le e^2$ on $\mathbb Z$ and $h\le T$.
    - Start from $e_0=0$ and run $k=2^\ell$ steps, so that $hk=T/2$. The discrete Grönwall inequality gives $E(F-C)^2\le b\,h\,(T/2)\,e^{aT/2}=\tfrac{bT^2}{4}e^{aT/2}\,2^{-\ell}$.
  - **Constant.** For level $\ell+1$ this gives $\mathrm{Var}(D_{\ell+1})\le L_\Phi^2\tfrac{bT^2}{2}e^{aT/2}\,2^{-(\ell+1)}$. So $c_2=1+L_\Phi^2\max\bigl(T\Lambda+T^2\Lambda^2,\ \tfrac{bT^2}{2}e^{aT/2}\bigr)>0$ works. The rate $2^{-\ell}$ is **sharp** in general: for $\lambda=\min(x,5)+1$, $x_0=0$, $\Phi=\mathrm{id}$, numerically $2^\ell\mathrm{Var}(D_\ell)\to2.30$ (N4).
- **Non-vacuity.** All hypotheses hold with non-constant data. Take $\lambda(x)=\min(x,5)+1$ ($K=1$, $\Lambda=6$) or $\lambda(x)=1+(x\bmod2)$ ($K=1$, $\Lambda=2$), together with $\Phi(x)=x$ ($L_\Phi=1$), $T=1$, $x_0\in\{0,3\}$. The variances are strictly positive at every computed level, so the bound is not met merely because the variance is $0$.
- **Junk values.** None. `variance` would be $0$ if $D_\ell\notin L^2$ (`Variance.lean:132`) or if $\Pi=0$. Neither happens: $D_\ell\in L^2$ by A7 (Lipschitz $\Phi$ and all moments finite), and $\Pi$ is a probability measure by A4.
- **Concerns.**
  1. $h_K$ is implied by $h_\Lambda$ with $K=\Lambda$ (A6). The theorem is therefore effectively about bounded $\lambda$, and $K$ enters only through the existential constant.
  2. If $L_\Phi<0$, $h_\Phi$ is unsatisfiable (take $x=0$, $y=1$), which is a vacuous but harmless corner.
  3. The rate exponent is hard-coded as $1\cdot\ell$.
  4. Degenerate cases: $T=0$, $\lambda\equiv0$ or constant $\lambda$ (perfect coupling, N4), $L_\Phi=0$, and some combinations with $\Phi$ constant beyond a threshold (for example $\Phi=\min(x,4)$ with $x_0=3$) all give $\mathrm{Var}(D_{\ell})=0$ for $\ell\ge1$. The bound is then trivially true but correctly so.

### T5. `tauLeaping_mlmc_theorem1`

- **Truth: true.** The proof sketch uses T2–T4 and A4, A7.
  - **Estimator and independence.** Let $Y(x)=\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}D_\ell(x_{(\ell,n)})$. The coordinates $x_{(\ell,n)}$ are i.i.d. with law $\Pi$ (`iIndepFun_infinitePi`, `infinitePi_map_eval`), and $D_\ell\in L^2(\Pi)$.
  - **Mean.** Telescoping with T2 and T3 gives $E[Y]=\int\Phi\,d\mu^{\lambda,T/2^L,x_0}_{2^L}=:E_L$.
  - **Variance and MSE.** $\mathrm{Var}(Y)=\sum_\ell\mathrm{Var}(D_\ell)/N_\ell\le c_2\sum_\ell2^{-\ell}/N_\ell$. Hence $\text{MSE}=\mathrm{Var}(Y)+(E_L-P)^2\le c_2\sum_\ell 2^{-\ell}/N_\ell+c_1^2 2^{-2\alpha L}$.
  - **Choice of $L$ and $N$.** Take $L$ minimal with $c_1 2^{-\alpha L}\le\varepsilon/2$. Take $N_\ell=\lceil 4c_2(L+1)2^{-\ell}\varepsilon^{-2}\rceil$ for $\ell\le L$ and $N_\ell=1$ for $\ell>L$. Then $\text{MSE}\le\varepsilon^2/4+\varepsilon^2/4<\varepsilon^2$.
  - **Cost.** The cost is at most $4c_2(L+1)^2\varepsilon^{-2}+2^{L+1}$. Put $t=-\log\varepsilon>1$.
    - First term: $L+1\le A+Bt\le(A+B)t$ with $A=2+\max(0,\log_2 2c_1)/\alpha$ and $B=1/(\alpha\ln2)$.
    - Second term: $2^{L+1}\le4\max\bigl(1,(2c_1/\varepsilon)^{1/\alpha}\bigr)\le4\max(1,(2c_1)^{1/\alpha})\,\varepsilon^{-2}t^2$. This step uses $1/\alpha\le2$, which is where $\alpha\ge\frac12$ enters, together with $\varepsilon<1$.
    - Therefore $c_4=4c_2(A+B)^2+4\max(1,(2c_1)^{1/\alpha})$ works for all $\varepsilon\in(0,e^{-1})$.
- **Non-vacuity.**
  - **(a) A rigorous instance.** Take $\lambda\equiv3$ ($K=0$, $\Lambda=3$), any $T$ and $x_0$, $\Phi=\mathrm{id}$, $P=x_0+3T$, $\alpha=1$, $c_1=1$. By Poisson convolution, $\mu^{\lambda,T/2^\ell,x_0}_{2^\ell}$ is the law of $x_0+\mathrm{Po}(3T)$ for every $\ell$, so $h_{\mathrm{weak}}$ holds. The conclusion is then genuine but easy: $D_{\ell\ge1}\equiv0$, and it needs $N_0>3T\varepsilon^{-2}$.
  - **(b) A non-constant instance, with numerical evidence.** Take $\lambda=\min(x,5)+1$, $T=1$, $x_0=0$, $\Phi=\mathrm{id}$ and $P=E[X_T]=1.687648258$ for the pure-birth jump process with rates $\lambda$. Then $2^\ell|E_\ell-P|$ increases to $1.1288$ for $\ell\le16$, so $h_{\mathrm{weak}}$ holds with $\alpha=1$ and $c_1=1.19$ on the computed range. The allocation above gives $\text{MSE}<\varepsilon^2$ for 13 values of $\varepsilon$ in $[10^{-4},0.35]$, with $\text{cost}/(\varepsilon^{-2}\log^2\varepsilon)\le141$ (N5).
- **Junk values.** None needed.
  - The mean-square-error Bochner integral would be $0$, hence trivially $<\varepsilon^2$, if $(Y-P)^2$ were non-integrable or if $\Pi^{\otimes(\mathbb N\times\mathbb N)}=0$. Neither happens (A4, A7).
  - The integral in $h_{\mathrm{weak}}$ would be the junk value $0$ for non-integrable $\Phi$, which would force $P=0$. This cannot happen under $h_\Lambda,h_\Phi$.
  - The real power and logarithm are evaluated at $\varepsilon>0$ and base $2>0$, so they are genuine.
  - `blockMean`'s $N=0$ convention is excluded by conclusion item 1.
- **Concerns.**
  1. $h_K$ is redundant given $h_\Lambda$ (A6).
  2. $h_{\mathrm{weak}}$ is an **assumption**: a weak-error rate with $\alpha\ge\frac12$ toward an arbitrary real $P$. The theorem does not connect $P$ to any continuous-time process. The hypothesis forces $P=\lim_\ell E_\ell$ (the limit exists by the hypothesis).
  3. The cost functional $\sum_{\ell\le L}N(\ell)2^\ell$ is stipulated. The per-sample work at level $\ell\ge1$ is $2^{\ell-1}$ applications of $R$ (4 Poisson draws each), which is proportional to $2^\ell$.
  4. $c_4$ depends on all the problem data and on $P,\alpha,c_1$. It is uniform only in $\varepsilon$.
  5. Only $\varepsilon<e^{-1}$ is covered, and the MSE bound is strict ($<\varepsilon^2$).
  6. $N(\ell)>0$ is also required for $\ell>L$. Those levels do not enter anything, so this is harmless.
  7. Every sample index $(\ell,n)$ draws a whole independent sequence $x_{(\ell,n)}\in(\mathbb N\times\mathbb N)^{\mathbb N}$, of which $D_\ell$ reads only entry $\ell$. Different levels therefore use independent samples.
  8. The implied variance rate $\beta=1$ and cost rate $\gamma=1$ put the result in the $\varepsilon^{-2}(\log\varepsilon)^2$ regime. Numerically $\text{cost}\cdot\varepsilon^2$ grows ($155\to2474$ as $\varepsilon$ goes from $0.35$ to $10^{-4}$), consistent with the $\log^2$ factor being needed.

---

# Part 3: Numerical sanity checks

All scripts are in `scratchpad/readback/round7/work_I/`. They use Python 3.11 with the standard library only. Run them from that directory with `python3 <script>`; `check_mlmc.py` reads `variances.json`, which `check_variance.py` writes.

**Method.**
- `tau_defs.py` re-implements every packet definition (`couplePair`, `coupledIncr`, `tauStep`, `coupledTwoStep`, `tauChain`, `coupledChain`, `tauLevelLaw`, `fineCoarseDiff∘tauFine/tauCoarse`) as exact discrete laws, stored as dictionaries.
- Poisson laws are truncated below $10^{-19}$ and states below $10^{-18}$ are pruned.
- With $T=1$ and integer-valued $\lambda$, every rate $h\lambda(x)$ is a dyadic rational, so the comparisons `b < a` in `couplePair` are exact in floating point.
- Test propensities: $\lambda(x)=1+(x\bmod2)$ ($\Lambda=2$, $K=1$), $\lambda(x)=\min(x,5)+1$ ($\Lambda=6$, $K=1$) and $\lambda\equiv3$ ($K=0$).
- Test functions: $\Phi(x)=x$, $\min(x,4)$ and $\sin x$ (all 1-Lipschitz).

| # | Script (output file) | Checks | Result |
|---|---|---|---|
| N1 | `check_coupled_incr.py` (`out_coupled_incr.txt`) | A1 and A2: the marginals of $Q_{a,b}$, the law $\lvert I-J\rvert\sim\mathrm{Po}(\lvert a-b\rvert)$ and its sign, for 7 pairs including $a=b$ and $a=0$; the marginals of $R_{\lambda,h}(s)$ against $S_h S_h$ and $S_{2h}$ | worst total-variation distance $1.8\times10^{-16}$; sign always correct |
| N2 | `check_moments.py` (`out_moments.txt`) | T1: $E[X_n^2]$ against $(x_0+nh\Lambda)^2+nh\Lambda$ for 3 choices of $\lambda$, $h\in\{1,\frac14,\frac1{64}\}$, $x_0\in\{0,3\}$, $n\le64$ | always within the bound (maximum ratio 1.000, attained for constant $\lambda$); total mass $1\pm6\times10^{-15}$; counterexample $\lambda=x!$ has partial sums $7.2\times10^{1}$, $1.5\times10^{6}$, $9.4\times10^{17}$, $1.0\times10^{32}$ at $k=5,10,20,30$ |
| N3 | `check_marginals.py` (`out_marginals.txt`) | T2 and T3: the first marginal of $\rho_\ell$ and the second marginal of $\rho_{\ell+1}$ against $\mu^{T/2^\ell}_{2^\ell}$ for $\ell\le9$, 3 choices of $\lambda$, 2 of $x_0$, 3 of $\Phi$; total mass of each $\rho_\ell$; $T=0$ | worst $\lvert\text{mass}-1\rvert=2.5\times10^{-14}$; worst TV $=1.6\times10^{-14}$; worst mean difference $2.6\times10^{-13}$; $\rho_0$ is diagonal; constant $\lambda$ puts mass $0$ off the diagonal; $T=0$ makes every $\rho_\ell=\delta_{(x_0,x_0)}$ |
| N4 | `check_variance.py` (`out_variance.txt`, `variances.json`) | T4: $\mathrm{Var}(D_\ell)$, $2^\ell\mathrm{Var}(D_\ell)$ and $2^\ell E(F-C)^2$ for $\ell\le10$ | $2^\ell\mathrm{Var}$ converges to positive constants (table below); constant $\lambda$ gives $\mathrm{Var}(D_{\ell\ge1})=0$ exactly |
| N5 | `check_mlmc.py` (`out_mlmc.txt`) | T5: weak error for $\ell\le16$ against the exact pure-birth mean (uniformization); constructive allocation; Monte Carlo of the estimator | tables below |

**N4 excerpt: $2^\ell\,\mathrm{Var}(D_\ell)$.**

| $\ell$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| $\min(x,5)+1$, $x_0=0$, $\Phi=x$ | 1.000 | 0.750 | 1.391 | 1.823 | 2.057 | 2.179 | 2.242 | 2.273 | 2.289 | 2.297 | 2.301 |
| $\min(x,5)+1$, $x_0=0$, $\Phi=\sin$ | 0.204 | 0.243 | 0.384 | 0.481 | 0.529 | 0.552 | 0.563 | 0.569 | 0.572 | 0.573 | 0.574 |
| $1+(x\bmod2)$, $x_0=3$, $\Phi=x$ | 2.000 | 0.555 | 0.948 | 1.126 | 1.197 | 1.226 | 1.238 | 1.243 | 1.246 | 1.247 | 1.247 |
| $\equiv3$, $x_0=0$, $\Phi=x$ | 3.000 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

The empirical constant $\sup_\ell 2^\ell\mathrm{Var}(D_\ell)$ over all 18 cases lies in $[0.018,\,4.0]$. The rate $2^{-\ell}$ is attained and not beaten: the probability that $F\ne C$ itself decays like $2^{-\ell}$.

**N5 excerpt: weak error**, for $\lambda=\min(x,5)+1$, $T=1$, $x_0=0$, $\Phi=x$. The exact value is $P=1.687648258112$; Richardson extrapolation from $\ell=15,16$ gives $1.687648257858$.

| $\ell$ | 0 | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 |
|---|---|---|---|---|---|---|---|---|---|
| $2^\ell\lvert E_\ell-P\rvert$ | 0.688 | 0.996 | 1.095 | 1.120 | 1.127 | 1.1283 | 1.1287 | 1.1288 | 1.1288 |

**N5 excerpt: allocation**, with $c_1=1.185$, $c_2=2.416$ and $\alpha=1$. The MSE is computed as $\sum_\ell\mathrm{Var}(D_\ell)/N_\ell+(E_L-P)^2$; for $\ell>10$, $V_\ell$ is extrapolated by halving.

| $\varepsilon$ | 0.35 | 0.2 | 0.1 | 0.05 | 0.01 | 0.005 | 0.001 | 0.0001 |
|---|---|---|---|---|---|---|---|---|
| $L$ | 3 | 4 | 5 | 6 | 8 | 9 | 12 | 15 |
| MSE$/\varepsilon^2$ | 0.27 | 0.26 | 0.28 | 0.29 | 0.38 | 0.38 | 0.28 | 0.33 |
| cost$/(\varepsilon^{-2}\log^2\varepsilon)$ | 140.9 | 93.4 | 65.7 | 52.8 | 36.9 | 34.4 | 34.2 | 29.2 |

**N5 excerpt: Monte Carlo of the actual estimator.** Independent samples are drawn for each index $(\ell,n)$, using the `coupledIncr` sampler.

| $\varepsilon$ | $R$ (replicates) | $L$, $N$ | empirical mean of $Y$ | $E_L$ | empirical MSE | formula MSE | $\varepsilon^2$ |
|---|---|---|---|---|---|---|---|
| 0.2 | 400 | 4, [1208, 604, 302, 151, 76] | 1.61864 (s.e. 0.0038) | 1.61922 | $1.067\times10^{-2}$ | $1.048\times10^{-2}$ | $4\times10^{-2}$ |
| 0.1 | 150 | 5, [5799, …, 182] | 1.65403 (s.e. 0.0033) | 1.65290 | $2.752\times10^{-3}$ | $2.791\times10^{-3}$ | $10^{-2}$ |

The numerics are sanity checks, not proofs. In particular, they give no rigorous certificate that the weak error rate holds for all $\ell$, or that the variance bound holds beyond $\ell=10$.

---

# Appendix: derived facts used in Part 2

- **A1 (marginals of $Q_{a,b}$).** If $(I,J)\sim Q_{a,b}$, then $I\sim\mathrm{Po}(a)$ and $J\sim\mathrm{Po}(b)$. Moreover $I-J=\operatorname{sgn}(a-b)\,V$ with $V\sim\mathrm{Po}(|a-b|)$.
  - Proof: case analysis on $a>b$, $a<b$ and $a=b$. In the last case $V\sim\mathrm{Po}(0)=\delta_0$. The marginals follow from $\mathrm{Po}(\min)*\mathrm{Po}(\max-\min)=\mathrm{Po}(\max)$.
  - Checked in N1.
- **A2 (marginals of $R_{\lambda,h}(s)$).**
  - The $\pi_1$-image of $R_{\lambda,h}(s)$ is $\mathrm{bind}(S_{\lambda,h}(s_1),S_{\lambda,h})$ and depends only on $s_1$. By A1, $I\sim\mathrm{Po}(h\lambda(s_1))$, and given $I$, $I'\sim\mathrm{Po}(h\lambda(s_1+I))$.
  - The $\pi_2$-image is $S_{\lambda,2h}(s_2)$. We have $J\sim\mathrm{Po}(h\lambda(s_2))$. The conditional law of $J'$ given $(I,J)$ is $\mathrm{Po}(h\lambda(s_2))$ whatever $(I,J)$ is, so $J'$ is independent of $J$. Therefore $J+J'\sim\mathrm{Po}(2h\lambda(s_2))$.
  - Checked in N1.
- **A3 (marginals of $\nu_k$).** $(\pi_1)_\#\nu^{\lambda,h,x_0}_k=\mu^{\lambda,h,x_0}_{2k}$ and $(\pi_2)_\#\nu^{\lambda,h,x_0}_k=\mu^{\lambda,2h,x_0}_k$.
  - Proof: induction on $k$ using A2 and the fact that `bind` commutes with an image under a function of one coordinate. All maps involved are measurable, having countable discrete domains.
  - Checked in N3.
- **A4 (every law is a probability measure).**
  - $\mathrm{Po}(r)$ is a probability measure (`Poisson/Basic.lean:68`), and so are products of probability measures (`Prod.lean:322`).
  - Images under measurable maps preserve total mass, and every map here has domain $\mathbb N$ or $\mathbb N\times\mathbb N$, hence is measurable (`MeasurableSpace/Basic.lean:287`).
  - `bind` of a probability measure with a measurable kernel of probability measures has mass $\int 1=1$ (`GiryMonad.lean:235`).
  - Hence all of $S$, $Q$, $R$, $\mu_n$, $\nu_k$ and $\rho_\ell$ are probability measures. Consequently $\Pi$ and $\Pi^{\otimes(\mathbb N\times\mathbb N)}$ are genuine product probability measures, not the zero measure of `ProductMeasure.lean:362`.
  - Checked in N2 and N3 (mass $1\pm2.5\times10^{-14}$).
- **A5 (one-step $L^2$ estimate).** Fix $F,C$ and let $e=F-C$ and $h\le T$. Let $\delta_1$ and $\delta_2$ be the differences of the two half-step increments.
  - By A1 and the Lipschitz bound: $E[\delta_1]=h(\lambda(F)-\lambda(C))$ and $E[\delta_1^2]\le hK|e|+h^2K^2e^2$.
  - For the second half-step, $|\lambda(F+I)-\lambda(C)|\le K(|e|+I)$ with $EI\le h\Lambda$ and $EI^2\le h\Lambda+h^2\Lambda^2$. Hence $|E[\delta_2]|\le hK|e|+h^2K\Lambda$ and $E[\delta_2^2]\le hK|e|+h^2K\Lambda+2h^2K^2(e^2+h\Lambda+h^2\Lambda^2)$.
  - Combining, $E[e'^2]\le e^2+2|e|\,|E\delta_1+E\delta_2|+2E\delta_1^2+2E\delta_2^2\le(1+ah)e^2+bh^2$ with $a,b$ depending on $K,\Lambda,T$. This uses $|e|\le e^2$ for $e\in\mathbb Z$.
- **A6 (bounded implies Lipschitz on $\mathbb N$).** If $0\le\lambda\le\Lambda$, then for $x\ne y$ in $\mathbb N$ we have $|\lambda(x)-\lambda(y)|\le\Lambda\le\Lambda|x-y|$, since $|x-y|\ge1$. So $h_K$ holds with $K=\Lambda$.
- **A7 (moments).** Under $h_\Lambda$, $X_n-x_0$ is stochastically dominated by $\mathrm{Po}(nh\Lambda)$, so every moment is finite. For $(F,C)\sim\nu_k$, each coordinate has such moments by A3. Lipschitz $\Phi$ therefore gives $\Phi(\cdot)\in L^2$ and $D_\ell\in L^2(\Pi)$.
