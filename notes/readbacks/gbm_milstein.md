# Blind audit: packet K (GBM, Milstein scheme, MLMC)

| Field | Value |
|---|---|
| Date | 2026-09-28 |
| Packet | `scratchpad/readback/round9/packet_K_gbm_milstein.lean` |
| Declarations audited | 18 in total: 10 definitions and 8 theorems. The main module has 4 definitions and 8 theorems; 6 definitions are appended from other modules. |
| Auditor | independent blind auditor (sub-agent) |
| Scripts and outputs | `scratchpad/readback/round9/work_K/` (`s1` to `s8`, plus the re-checks `s2b` and `s5b`; each `.py` saved next to its `.out`) |

---

## Summary

### Verdicts

| # | Declaration | Kind | Truth | Vacuous? | Holds only because of a junk value? |
|---|---|---|---|---|---|
| M3 | `milsteinPath_gbm` | theorem | **True** for every real $h$, negative $h$ included | No (it has no hypotheses) | No |
| M4 | `integral_sq_prod_sub_prod_of` | theorem | **True** | No | No |
| M5 | `abs_pow_sub_two_mul_pow_add_pow_le` | theorem | **True** and sharp: the supremum of LHS/RHS is $1$ | No | No |
| M7 | `gbm_mil_strong_error` | theorem | **True**: proof route checked; about $2.9\cdot10^4$ exact high-precision cases with 0 violations; numerically true/bound $\le 1/120$ | No | No |
| M9 | `gbm_mil_strong_error_level` | theorem | **True** (the special case $n=2^\ell$ of M7) | No | No |
| M10 | `gbm_mil_weak_error_le` | theorem | **True** | No | No |
| M11 | `gbm_mil_correction_variance_le` | theorem | **True** | No | No |
| M12 | `gbm_mil_mlmc_theorem1` | theorem | **True** | No | No |

The 10 definitions (M1, M2, M6, M8, D1 to D6) are rendered below without judgement. The theorems pass them no arguments that trigger a misleading junk value:

- The junk value $\sqrt x=0$ for a negative argument arises only if $h<0$ or $T<0$, and M7 and M9 to M12 exclude both cases by hypothesis.
- `deriv` is only ever applied to $S\mapsto\sigma S$, whose derivative $\sigma$ exists everywhere.

### Main points for a human auditor

1. **What is modelled.** Everything is a statement about explicit random variables on the sequence space $\mathbb R^{\mathbb N}$ carrying the product of standard normals.
   - The "exact solution" is the closed-form lognormal expression $s_0\exp((r-\sigma^2/2)T+\sigma W_T)$, with $W_T$ represented as $\sqrt{T/2^\ell}\sum_{i<2^\ell}z_i$ (or $\sqrt h\sum_{i<n}z_i$).
   - No SDE, Brownian motion or Itô integral is formalised.
   - The scheme is a general Milstein step using Mathlib's `deriv` of the diffusion coefficient, specialised to $a(S)=rS$ and $b(S)=\sigma S$. For this $b$ the derivative is exactly $\sigma$, so each step is multiplication by $1+rh+\sigma\sqrt h z_i+\tfrac{\sigma^2}{2}(hz_i^2-h)$.
2. **Strong error (M7, M9).**
   - The bound is on the mean-square error at the terminal time only (not the RMS error, and not uniform over the grid): $\mathbb E[(S_T-X_T)^2]\le C\,h^2$.
   - $C$ is fully explicit: $s_0^2e^{(2|r|+\sigma^2)T}\lambda^2(30\lambda^2T^2+16\lambda T+4)$ with $\lambda=|r|+\sigma^2$.
   - The $h^2$ rate is attained. The exact MSE$/h^2$ tends to $s_0^2e^{(2r+\sigma^2)T}\big(T(\sigma^2r^2+\sigma^6/6)+T^2(r^2/2+r\sigma^2)^2\big)$.
   - The constant is conservative by a factor of at least about $120$ everywhere tested, and by an extra factor $e^{4|r|T}$ when $r<0$.
3. **Weak error and correction variance (M10, M11).**
   - Both are derived from the strong bound for a $K$-Lipschitz payoff $g$ (no smoothness), with explicit constants $K\sqrt{CT^2}\,2^{-\ell}$ and $10K^2CT^2\,4^{-(\ell+1)}$.
   - M10 compares the Milstein path with the level-0 exact sample $s_0e^{(r-\sigma^2/2)T+\sigma\sqrt T z_0}$, which is not the same-path solution. It has the same law, so the statement is exactly the weak error $|\mathbb E g(X_T)-\mathbb E g(S_T)|$.
   - M11 uses the standard pairwise Brownian coupling `pairAvg`.
4. **MLMC theorem (M12).**
   - Statement: $\exists c_4>0\ \forall\varepsilon\in(0,e^{-1})\ \exists L,N$ such that the actual multilevel estimator (independent standard-normal sequences for every level and sample index) has MSE $<\varepsilon^2$ and cost $\sum_{\ell\le L}N_\ell2^\ell\le c_4\varepsilon^{-2}$.
   - $c_4$ is existential and not explicit. It may depend on $r,\sigma,s_0,T,g,K$.
   - Cost is counted as $2^\ell$ per level-$\ell$ sample; the coarse path's steps are not counted, which only changes constants.
   - From the packet's own bounds I get a valid explicit $c_4=2S_\infty^2+8B/e+1$. It is astronomically large for large $(|r|+\sigma^2)T$ (e.g. $1.2\cdot10^{17}$ at $r=2,\sigma=1.5,s_0=3,T=3$).
5. **Junk values.**
   - Every integral in the theorems is of a genuinely integrable function, and `variance` is applied to an $L^2$ function.
   - Both product measures are products of probability measures, so they are genuine and not Mathlib's junk zero measure.
   - Caution: M7, M9 and M10 have the form "integral $\le$ non-negative quantity", and M12 has "integral $<\varepsilon^2$". A junk value $0$, which Mathlib returns for a non-integrable integrand, would satisfy all of them, and integrability is not stated in the theorems. I checked that it holds, so none of them relies on the junk value.
6. **Hypotheses.**
   - In M4, $h_{FG}$ is implied by the others ($|FG|\le(F^2+G^2)/2$). Conversely, $h_F,h_G$ become unnecessary once $h_{FG}$ is present.
   - In M5, $1\le M$ is load-bearing. Counterexample: $M=\tfrac12$, $(a,b,c)=(\tfrac12,0,-\tfrac12)$, $n=2$ gives $\tfrac12>\tfrac14$.
   - $0\le h$ (M7) and $0\le T$ (M9, M10) are load-bearing: counterexamples with negative time step exist.
   - $0\le T$ is not needed in M11 or M12, where everything becomes deterministic when $T<0$.
7. **Numerics.** Every numerical check agrees with the statements:
   - closed-form one-step moments;
   - the product identity, by Monte Carlo and 2-D quadrature;
   - about $2.9\cdot10^4$ exact strong-error cases (negative $r$, $\sigma$ up to 5, $h$ up to 10, $n$ up to $10^6$), with 0 violations;
   - $92{,}768$ exact rational tests of M5, plus an adversarial search;
   - weak error, correction variance and MLMC MSE by Monte Carlo for call payoffs.

---

## Rules followed

- **Read:** the packet; the mission file `prove2me_workspace/references/mission_auditor.md`; and, only to confirm the meaning of Mathlib definitions and conventions, Mathlib sources under `.lake/packages/mathlib/Mathlib/`:
  - `Probability/Distributions/Gaussian/Real.lean`
  - `Probability/ProductMeasure.lean`
  - `Probability/Independence/InfinitePi.lean`
  - `Probability/Moments/Variance.lean`
  - `MeasureTheory/Integral/Bochner/Basic.lean`
  - `Analysis/Calculus/Deriv/Basic.lean`
  - `Analysis/Calculus/Deriv/Mul.lean`
  - `Analysis/Real/Sqrt.lean`
  - `Analysis/SpecialFunctions/Pow/Real.lean`
  - `Algebra/GroupWithZero/Defs.lean`
  - `Algebra/BigOperators/Group/Finset/Defs.lean`
  - `Data/Finset/Range.lean`
- **Not read:** any project source (`MlmcLean/…`), `docs/`, `notes/`, README, PLAN, papers, scripts, other packets or their outputs (nothing else under `readback/`), git history, or the web.
- **Names:** I did not infer meaning from declaration or file names. The renderings translate the code.
- **Lean:** not run. Elaboration, casts and parsing were read from the source. The packet's proofs are `sorry`, so every truth verdict below rests on my own mathematical argument plus the numerical checks, not on the project's proofs.
- **Scripts:** pure Python 3 with `mpmath` and `sympy`, all in `scratchpad/readback/round9/work_K/` with their outputs saved next to them.

---

## Mathlib conventions confirmed

Paths are relative to `.lake/packages/mathlib/Mathlib/`.

| Convention relied on | Location | Where it matters |
|---|---|---|
| `gaussianReal μ v` is `Measure.dirac μ` if `v = 0`, else `volume.withDensity (gaussianPDF μ v)`. The density is $(\sqrt{2\pi v})^{-1}e^{-(x-\mu)^2/(2v)}$ (`gaussianPDF` is the `ofReal` of it). | `Probability/Distributions/Gaussian/Real.lean:222`, `:49`, `:166`, `:229` | `gaussianReal 0 1` is $\mathcal N(0,1)$ with density $(2\pi)^{-1/2}e^{-x^2/2}$ (here $v=1\neq0$) |
| `gaussianReal μ v` is a probability measure | same file, `:231` | the product measures below are not junk |
| `Measure.infinitePi μ` is the product measure if every `μ i` is a probability measure, and otherwise **the zero measure** (junk) | `Probability/ProductMeasure.lean:358` | `stdNormalSeq` and the $\mathbb N\times\mathbb N$ product in M12. All factors are probability measures, so there is no junk. |
| `infinitePi` is a probability measure; its finite marginals are `Measure.pi` | `Probability/ProductMeasure.lean:381`, `:377` | ditto |
| Coordinate evaluation is measure preserving from `infinitePi μ` to `μ i` | `Probability/ProductMeasure.lean:470` | coordinates are $\mathcal N(0,1)$ |
| Coordinates are mutually independent under `infinitePi` (`iIndepFun_infinitePi`) | `Probability/Independence/InfinitePi.lean:127` | M4, M11, M12 |
| Notation `∫ x, f x ∂μ`: the body is parsed at precedence 60 (so it includes `+`/`-`), the measure at 70 | `MeasureTheory/Integral/Bochner/Basic.lean:166` | parsing of M10 and M12 |
| The Bochner integral of a non-integrable (or non-a.e.-strongly-measurable) function is $0$ | `MeasureTheory/Integral/Bochner/Basic.lean:202` (`integral_undef`), `:209` | junk analysis of M4, M7, M9, M10, M12 |
| `evariance X μ = ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ` and `variance X μ = (evariance X μ).toReal`, so the variance is $0$ when $X\notin L^2$ | `Probability/Moments/Variance.lean:58`, `:64`, `:132` (`variance_of_not_memLp`) | M11 |
| `variance X μ ≤ μ[X ^ 2]` for a probability measure | `Probability/Moments/Variance.lean:339` | proof of M11 |
| `deriv f x = fderiv 𝕜 f x 1`, and it is $0$ at points where `f` is not differentiable | `Analysis/Calculus/Deriv/Basic.lean:153`, `:250` | `milsteinStep` |
| `deriv (fun y => u * v y) x = u * deriv v x`, and `deriv (fun x => x) = fun _ => 1` | `Analysis/Calculus/Deriv/Mul.lean:386`; `Analysis/Calculus/Deriv/Basic.lean:693` | $b'(S)=\sigma$ for $b(S)=\sigma S$ |
| `Real.sqrt x = NNReal.sqrt (Real.toNNReal x)`, which is $0$ for $x\le0$ | `Analysis/Real/Sqrt.lean:112`, `:142`, `:268` | $\sqrt h$ for $h<0$; $\sqrt{T/2^\ell}$ for $T<0$ |
| `x ^ (y : ℝ)` is `Real.rpow`. For $x>0$ it equals $\exp(y\log x)$; `rpow_neg` and `rpow_two` give $\varepsilon^{(-2:\mathbb R)}=1/\varepsilon^2$ | `Analysis/SpecialFunctions/Pow/Real.lean:35`–`38`, `:51`, `:259`, `:470`, `:62` | $\varepsilon^{-2}$ in M12 |
| `(0 : G₀)⁻¹ = 0` | `Algebra/GroupWithZero/Defs.lean:236` | `blockMean` with $N=0$ |
| `∑ x ∈ s, body` and `∏ x ∈ s, body` parse the body at precedence 67, so `+` and `-` end the body while `*` and `^` do not | `Algebra/BigOperators/Group/Finset/Defs.lean:181`, `:196` | M4, M7, M12 |
| `Finset.range n` $=\{0,\dots,n-1\}$ | `Data/Finset/Range.lean:53`, `:64` | everywhere |

The operator precedences used for parsing come from Lean core, not Mathlib: `+`/`-` 65, `*`/`/` 70, `^` 75 (right-associative), `<`/`≤` 50, `∧` 35 (right-associative). Natural-number casts: $n$, $N_\ell$ and $2^\ell$ appear as reals where they multiply or divide reals. In `range (2 ^ ℓ)` and in the last argument of `milsteinPath`, $2^\ell$ is a natural number.

---

## Standing notation used in the renderings

- $\mathcal N$ is the standard Gaussian probability measure on $\mathbb R$ (`gaussianReal 0 1`), with density $(2\pi)^{-1/2}e^{-x^2/2}$.
- $\mathbb P$ is `stdNormalSeq` (D1), a probability measure on $\mathbb R^{\mathbb N}$. A point is a real sequence $z=(z_0,z_1,\dots)$.
- $\int\cdot\,d\mu$ is the Bochner integral. Its value is $0$ whenever the integrand is not $\mu$-integrable.
- $\sqrt x$ is Mathlib's real square root, which is $0$ for $x\le0$.
- $\sum_{i=0}^{n-1}$ and $\prod_{i=0}^{n-1}$ range over $\{0,\dots,n-1\}$. They are empty (sum $0$, product $1$) when $n=0$.
- $\lambda:=|r|+\sigma^2$ whenever $r$ and $\sigma$ are given.

---

## Part I: definitions appended from other modules

### D1. `stdNormalSeq` (abbreviation)

**Rendering.** $\mathbb P$ is the measure on the space $\mathbb R^{\mathbb N}$ of real sequences $z=(z_0,z_1,z_2,\dots)$ with the product σ-algebra, given by Mathlib's infinite product of the constant family $i\mapsto\mathcal N$:
$$\mathbb P=\bigotimes_{i\in\mathbb N}\mathcal N .$$
Mathlib's construction returns the measure whose finite-dimensional marginals are the finite products of the factors when every factor is a probability measure, and the zero measure otherwise. Here every factor is the probability measure $\mathcal N$. Under $\mathbb P$ the coordinates $z_0,z_1,\dots$ are therefore independent, each with law $\mathcal N(0,1)$.

### D2. `pairAvg`

**Rendering.** For a real sequence $z:\mathbb N\to\mathbb R$ and $k\in\mathbb N$,
$$\operatorname{pairAvg}(z)_k=\frac{z_{2k}+z_{2k+1}}{\sqrt 2}.$$
So $\operatorname{pairAvg}$ maps a real sequence to a real sequence, and its $k$-th entry uses only entries $2k$ and $2k+1$ of $z$.

### D3. `milsteinStep`

**Rendering.** For functions $a,b:\mathbb R\to\mathbb R$ and reals $h,S,\Delta W$,
$$\operatorname{milsteinStep}(a,b,h,S,\Delta W)=S+a(S)\,h+b(S)\,\Delta W+\tfrac12\,b(S)\,b'(S)\,\big(\Delta W^2-h\big),$$
where $\tfrac12$ is the real number $0.5$. The last product is grouped as $((\tfrac12 b(S))\,b'(S))\,(\Delta W^2-h)$. $b'(S)$ is Mathlib's `deriv b S`: the derivative of $b$ at $S$ if $b$ is differentiable at $S$, and $0$ if it is not. No condition is imposed on $a$, $b$ or $h$; the sign of $h$ is unrestricted.

### D4. `blockMean`

**Rendering.** Let $\iota,\Omega_0,\Omega$ be arbitrary types (no measurable-space or other structure appears in the displayed code). Take
- a family $f=(f_i)_{i\in\iota}$ of functions $f_i:\Omega_0\to\mathbb R$,
- a family $\omega=(\omega_{(i,n)})_{(i,n)\in\iota\times\mathbb N}$ of maps $\omega_{(i,n)}:\Omega\to\Omega_0$,
- an index $i\in\iota$, a natural number $N$ and a point $x\in\Omega$.

Then
$$\operatorname{blockMean}(f,\omega,i,N,x)=N^{-1}\sum_{n=0}^{N-1}f_i\big(\omega_{(i,n)}(x)\big),$$
with $N^{-1}$ the real inverse of $N$. When $N=0$ this is $0^{-1}=0$ (and the sum is empty anyway), so the value is $0$. No measure is involved.

### D5. `fineCoarseDiff`

**Rendering.** For two families $P^{f}=(P^f_\ell)_{\ell\in\mathbb N}$ and $P^{c}=(P^c_\ell)_{\ell\in\mathbb N}$ of functions $\Omega_0\to\mathbb R$ ($\Omega_0$ an arbitrary type), $\operatorname{fineCoarseDiff}(P^f,P^c)$ is the family of functions $\Omega_0\to\mathbb R$ given by
$$\operatorname{fineCoarseDiff}(P^f,P^c)_0=P^f_0,\qquad \operatorname{fineCoarseDiff}(P^f,P^c)_{\ell+1}(y)=P^f_{\ell+1}(y)-P^c_{\ell}(y)\quad(y\in\Omega_0).$$

### D6. `gbmExact`

**Rendering.** For reals $r,\sigma,T,s_0$, a level $\ell\in\mathbb N$ and a real sequence $z$,
$$\operatorname{gbmExact}(r,\sigma,T,s_0,\ell,z)=s_0\exp\!\Big(\big(r-\tfrac{\sigma^2}{2}\big)T+\sigma\sqrt{T/2^{\ell}}\;\sum_{i=0}^{2^\ell-1}z_i\Big).$$
It uses exactly $z_0,\dots,z_{2^\ell-1}$. Edge cases:
- For $\ell=0$ it is $s_0\exp((r-\sigma^2/2)T+\sigma\sqrt T\,z_0)$.
- For $T<0$ the square root is $0$, so the value is $s_0e^{(r-\sigma^2/2)T}$ whatever $z$ is.
- For $T=0$ it is $s_0$.

---

## Part II: the main module

### M1. `gbmMilFactor` (definition)

**Rendering.** For reals $r,\sigma,h,x$,
$$\mathrm{MF}_{r,\sigma,h}(x):=\operatorname{gbmMilFactor}(r,\sigma,h,x)=1+rh+\sigma\big(\sqrt h\,x\big)+\frac{\sigma^2}{2}\Big(\big(\sqrt h\,x\big)^2-h\Big).$$
- For $h\ge0$ this is $1+rh+\sigma\sqrt h\,x+\tfrac{\sigma^2h}{2}(x^2-1)$.
- For $h<0$ (so $\sqrt h=0$) it is $1+rh-\tfrac{\sigma^2h}{2}$, independent of $x$.

The value may be negative.

### M2. `milsteinPath` (definition)

**Rendering.** For functions $a,b:\mathbb R\to\mathbb R$, reals $h,S_0$ and a real sequence $z$, $\operatorname{milsteinPath}(a,b,h,S_0,z)$ is the real sequence $(X_n)_{n\in\mathbb N}$ defined by
$$X_0=S_0,\qquad X_{i+1}=\operatorname{milsteinStep}\big(a,b,h,X_i,\sqrt h\,z_i\big)=X_i+a(X_i)h+b(X_i)\sqrt h\,z_i+\tfrac12\,b(X_i)\,b'(X_i)\big((\sqrt h\,z_i)^2-h\big),$$
with $b'$ as in D3 (the derivative where it exists, $0$ elsewhere). $X_n$ depends only on $z_0,\dots,z_{n-1}$.
- For $h\ge0$, $(\sqrt h z_i)^2=hz_i^2$.
- For $h<0$, $\sqrt h=0$, so $X_{i+1}=X_i+a(X_i)h-\tfrac12b(X_i)b'(X_i)h$ does not depend on $z$.

### M3. `milsteinPath_gbm` (theorem)

**Rendering.** For all real numbers $r,\sigma,h,s_0$, every real sequence $z$ and every $n\in\mathbb N$,
$$X_n=s_0\prod_{i=0}^{n-1}\mathrm{MF}_{r,\sigma,h}(z_i)=s_0\prod_{i=0}^{n-1}\Big(1+rh+\sigma\sqrt h\,z_i+\tfrac{\sigma^2}{2}\big((\sqrt h\,z_i)^2-h\big)\Big),$$
where $(X_n)$ is the recursion of M2 with drift $a(S)=rS$ and diffusion $b(S)=\sigma S$:
$$X_0=s_0,\qquad X_{i+1}=X_i+rX_ih+\sigma X_i\sqrt h\,z_i+\tfrac12\,\sigma X_i\,b'(X_i)\big((\sqrt h z_i)^2-h\big).$$
Here $b'(X_i)$ is the derivative of $S\mapsto\sigma S$ at $X_i$, which exists at every point and equals $\sigma$. The drift is never differentiated.

There are no hypotheses:
- $h$ may be negative, in which case $\sqrt h=0$ and every factor equals $1+rh-\sigma^2h/2$;
- $n=0$ is allowed, and both sides are then $s_0$;
- $\sigma=0$ and $s_0=0$ are allowed.

**Assessment.**
- **Truth: true.** Induction on $n$. With $b'\equiv\sigma$,
  $$\operatorname{milsteinStep}(rS,\sigma S,h,X,\sqrt h z)=X+rXh+\sigma X\sqrt h z+\tfrac12\sigma^2X\big((\sqrt hz)^2-h\big)=X\cdot\mathrm{MF}_{r,\sigma,h}(z).$$
  Then use $\prod_{i<n+1}=\big(\prod_{i<n}\big)\cdot(\text{factor }n)$. The one-step identity was checked symbolically with an arbitrary real symbol standing for $\sqrt h$ (s1, Part 1), so it also covers the junk value $\sqrt h=0$ when $h<0$.
- **Non-vacuity:** there are no hypotheses. For example, $r=0.05$, $\sigma=0.2$, $h=0.01$, $s_0=100$, $n=3$ equates two non-constant functions of $(z_0,z_1,z_2)$.
- **Junk values:** $\sqrt h=0$ for $h<0$ enters both sides identically, and the identity stays a correct algebraic identity. `deriv` is applied only to the everywhere-differentiable $S\mapsto\sigma S$, so no junk derivative arises.
- **Concerns:** none of substance. The statement identifies the general-purpose Milstein recursion, specialised to linear coefficients, with a product of one-step factors. For $h<0$ the recursion is not a meaningful scheme, but the identity is still true.

### M4. `integral_sq_prod_sub_prod_of` (theorem)

**Rendering.** Let $F,G:\mathbb R\to\mathbb R$ be functions such that:
- $F$ and $G$ are Borel measurable;
- $x\mapsto F(x)^2$, $x\mapsto G(x)^2$ and $x\mapsto F(x)G(x)$ are each integrable with respect to $\mathcal N$.

Then for every real $s_0$ and every $n\in\mathbb N$,
$$\int_{\mathbb R^{\mathbb N}}\Big(s_0\prod_{i=0}^{n-1}F(z_i)\;-\;s_0\prod_{i=0}^{n-1}G(z_i)\Big)^2\,d\mathbb P(z)
= s_0^2\Big(\Big(\int F^2\,d\mathcal N\Big)^n-2\Big(\int FG\,d\mathcal N\Big)^n+\Big(\int G^2\,d\mathcal N\Big)^n\Big).$$
Each product stops before the minus sign, so the integrand is the square of the difference of the two scaled products. For $n=0$ both sides are $0$.

**Assessment.**
- **Truth: true.**
  1. Pointwise, $(s_0\prod F(z_i)-s_0\prod G(z_i))^2=s_0^2\big(\prod F(z_i)^2-2\prod F(z_i)G(z_i)+\prod G(z_i)^2\big)$.
  2. Under $\mathbb P$ the coordinates are independent with law $\mathcal N$ (Mathlib: `iIndepFun_infinitePi`, `measurePreserving_eval_infinitePi`).
  3. A product of integrable functions of distinct independent coordinates is integrable, and its integral is the product of the integrals. This gives $(\int F^2)^n$, $(\int FG)^n$ and $(\int G^2)^n$.
  4. Hence the integrand is integrable and the identity is a genuine one.
- **Non-vacuity:** take the exact GBM factor $F(x)=e^{(r-\sigma^2/2)h+\sigma\sqrt hx}$ and the Milstein factor $G=\mathrm{MF}_{r,\sigma,h}$, with $(r,\sigma,h)=(0.05,0.2,0.25)$, $s_0=1$, $n=4$. All hypotheses hold and both sides equal $8.398\cdot10^{-6}$ (closed form; Monte Carlo $8.35(4)\cdot10^{-6}$; s2).
- **Junk values:** none. Under the hypotheses the left integrand is integrable, and the three right-hand integrals are of integrable functions by hypothesis.
- **Concerns:**
  - Redundant hypotheses. Given $h_{F2}$ and $h_{G2}$, the hypothesis $h_{FG}$ follows from $h_F,h_G$ (measurability of $FG$ and $|FG|\le(F^2+G^2)/2$). Conversely, $h_F,h_G$ are not needed once $h_{FG}$ holds, because the integrand only involves $F^2$, $FG$ and $G^2$. This is harmless.
  - The lemma is specific to the i.i.d. standard-normal product measure, but $F$ and $G$ are otherwise arbitrary.

### M5. `abs_pow_sub_two_mul_pow_add_pow_le` (theorem)

**Rendering.** For all real numbers $a,b,c,M$ with $|a|\le M$, $|b|\le M$, $|c|\le M$ and $1\le M$, and for every $n\in\mathbb N$,
$$\big|a^n-2b^n+c^n\big|\;\le\;n^2M^n\,\big(|a-b|\,|b-c|\big)+n\,M^n\,|a-2b+c| ,$$
where $n$ is cast to a real. For $n=0$ both sides are $0$.

**Assessment.**
- **Truth: true.** Let $P(x,y)=\sum_{k=0}^{n-1}x^ky^{n-1-k}$, so $x^n-y^n=(x-y)P(x,y)$, $P$ is symmetric, and $|P|\le nM^{n-1}$ on $[-M,M]^2$. Assume $|a-b|\le|b-c|$ (the other case is symmetric, exchanging $a$ and $c$). Then
  $$a^n-2b^n+c^n=(a-b)\big(P(a,b)-P(c,b)\big)+(a-2b+c)P(b,c).$$
  Also $P(a,b)-P(c,b)=\sum_k(a^k-c^k)b^{n-1-k}$ is bounded by $|a-c|\,M^{n-2}\binom n2$, and $|a-c|\le2|b-c|$. So the first term is at most $n(n-1)M^{n-2}|a-b||b-c|$ and the second at most $nM^{n-1}|a-2b+c|$. Finally use $M\ge1$ and $n(n-1)\le n^2$.
- **Non-vacuity:** $a=1$, $b=0.9$, $c=0.8$, $M=1$, $n=2$ gives $0.02\le0.04$.
- **Junk values:** none; this is pure real algebra.
- **Concerns:**
  - The inequality is sharp. For $n=1$ equality holds when $a=b$. For every $n\ge1$ the ratio LHS/RHS tends to $1$ as $a=b\to\pm M$, $c\to b$ with $M=1$. On second differences ($a-2b+c=0$) the ratio tends to $(n-1)/n$.
  - $1\le M$ is load-bearing: $M=\tfrac12$, $(a,b,c)=(\tfrac12,0,-\tfrac12)$, $n=2$ gives $\tfrac12>\tfrac14$. The bounds $|a|,|b|,|c|\le M$ are also load-bearing (the LHS grows like $|a|^n$).
  - Evidence: s4.

### M6. `gbmMilStrongConst` (definition)

**Rendering.** For reals $r,\sigma,t,s_0$, with $\lambda=|r|+\sigma^2$,
$$C(r,\sigma,t,s_0):=\operatorname{gbmMilStrongConst}(r,\sigma,t,s_0)=s_0^2\,e^{(2|r|+\sigma^2)t}\,\lambda^2\,\big(30\lambda^2t^2+16\lambda t+4\big).$$
- It is $\ge0$ for every real $t$, including $t<0$, because $30u^2+16u+4>0$ for all real $u$.
- It is $0$ exactly when $s_0=0$ or $r=\sigma=0$.
- It depends on $r$ only through $|r|$.

### M7. `gbm_mil_strong_error` (theorem)

**Rendering.** For all real numbers $r,\sigma,s_0$, every real $h$ with $0\le h$, and every $n\in\mathbb N$,
$$\int_{\mathbb R^{\mathbb N}}\Big(s_0\exp\!\Big(\big(r-\tfrac{\sigma^2}{2}\big)(nh)+\sigma\sqrt h\sum_{i=0}^{n-1}z_i\Big)-X_n(z)\Big)^2\,d\mathbb P(z)\;\le\;C(r,\sigma,nh,s_0)\,h^2 .$$
Here:
- $X_n(z)$ is the recursion of M2/M3 with $a(S)=rS$, $b(S)=\sigma S$, step $h$ and start $s_0$. Since $h\ge0$ and $b'\equiv\sigma$, this is $X_0=s_0$ and $X_{i+1}=X_i\big(1+rh+\sigma\sqrt h\,z_i+\tfrac{\sigma^2h}{2}(z_i^2-1)\big)$.
- $C$ is M6 evaluated at the horizon $t=nh$ (with $n$ cast to a real), so the right-hand side is explicitly
  $$s_0^2\,e^{(2|r|+\sigma^2)nh}\,\lambda^2\big(30\lambda^2n^2h^2+16\lambda nh+4\big)\,h^2 .$$
- Both terms of the integrand use the same $z_0,\dots,z_{n-1}$. The right-hand side is an explicit closed-form expression; no existential constant appears.

Edge cases:
- $h=0$: both sides are $0$.
- $n=0$: the left side is $0$ and the right side is $4s_0^2\lambda^2h^2$.
- $s_0=0$, or $r=\sigma=0$: both sides are $0$.

**Assessment.**
- **Truth: true.** Proof route, with numbers checked in s1, s3 and s7:
  1. $s_0e^{(r-\sigma^2/2)nh+\sigma\sqrt h\sum z_i}=s_0\prod_{i<n}A(z_i)$ with $A(x)=e^{(r-\sigma^2/2)h+\sigma\sqrt hx}$, and $X_n=s_0\prod_{i<n}\mathrm{MF}_{r,\sigma,h}(z_i)$ by M3.
  2. By M4 the left side equals $s_0^2(\alpha^n-2\beta^n+\gamma^n)$, where
     $$\alpha=\mathbb E A^2=e^{(2r+\sigma^2)h},\quad \beta=\mathbb E[A\,\mathrm{MF}]=e^{rh}\big(1+rh+\sigma^2h+\tfrac{\sigma^4h^2}{2}\big),\quad \gamma=\mathbb E\,\mathrm{MF}^2=(1+rh)^2+\sigma^2h+\tfrac{\sigma^4h^2}{2}.$$
     These were verified symbolically and by quadrature; the maximum relative error is $7\cdot10^{-26}$.
  3. Let $M=e^{(2|r|+\sigma^2)h}\ge1$. Then $|\alpha|,|\beta|,|\gamma|\le M$ (elementary, and checked on a grid).
  4. Let $w=\lambda h$. If $w\ge1$, the left side is $\le2s_0^2(\alpha^n+\gamma^n)\le4s_0^2M^n\le4s_0^2M^nw^2\le$ RHS.
  5. If $w<1$, apply M5 with $(a,b,c)=(\alpha,\beta,\gamma)$ and the local bounds $|\alpha-\beta|\le c_aw^2$, $|\beta-\gamma|\le c_bw^2$ and $|\alpha-2\beta+\gamma|\le c_cw^3$. Numerically, $c_a\approx1.95$, $c_b\approx1.44$ and $c_c\approx0.54$ on $w\le1$ (s7). This gives LHS $\le s_0^2M^nw^2\big(c_ac_b(nw)^2+c_c\,nw\big)$, which is $\le$ RHS because $c_ac_b\approx2.8\le30$ and $c_c\le16$, and because $nw=\lambda nh$ and $M^n=e^{(2|r|+\sigma^2)nh}$.
  6. Numerically: 0 violations in $10{,}164$ natural-parameter cases, $17{,}616$ reduced-parameter cases and $1{,}644$ level cases. These cover $r\in[-20,20]$, $\sigma\le5$, $h\le10$ (so $(|r|+\sigma^2)h$ up to $450$) and $n\le10^6$. The largest true/bound found is $0.00825$ on the grids; the supremum appears to be $1/120\approx0.00833$, approached as $\sigma=0$, $h\to0$, $rT\to\infty$.
- **Non-vacuity:** $r=0.05$, $\sigma=0.2$, $s_0=100$, $h=1/16$, $n=16$: the left side is $5.396\cdot10^{-3}>0$ and the right side is $2.068$.
- **Junk values:** the right side is always $\ge0$. So if the integrand were not integrable, the junk value $0$ of the integral would make the statement trivially true; integrability is not a hypothesis. It does hold, since the integrand is $s_0^2(\prod A-\prod\mathrm{MF})^2$ with all Gaussian moments finite. $\sqrt h$ is the genuine square root because $h\ge0$. No junk value is used.
- **Concerns:**
  - The "exact solution" is the explicit lognormal formula driven by the increments $\sqrt h z_i$; no SDE is involved.
  - The error is the mean-square error at the final time $nh$ only (RMS order 1).
  - The constant is explicit but loose: true/bound is at most about $1/120$, and it carries an extra slack factor $e^{4|r|nh}$ when $r<0$ (e.g. true/bound $\approx1.7\cdot10^{-6}$ for $r=-2$, $\sigma=0.3$, $s_0=1$, $T=1$).
  - The $h^2$ rate is attained. For fixed $T=nh$, true$/h^2\to s_0^2e^{(2r+\sigma^2)T}\big(T(\sigma^2r^2+\tfrac{\sigma^6}{6})+T^2(\tfrac{r^2}2+r\sigma^2)^2\big)$, confirmed to 6 digits (s3, Part C).
  - The hypothesis $0\le h$ is load-bearing: with $h=-1$, $n=10$, $r=0$, $\sigma=1$, $s_0=1$ the left side is $8235$ and the right side $0.129$ (s8).

### M8. `gbmMil` (definition)

**Rendering.** For reals $r,\sigma,T,s_0$, a level $\ell\in\mathbb N$ and a real sequence $z$, let $h_\ell=T/2^\ell$ ($2^\ell$ as a real). Then
$$\mathrm{Mil}_\ell(z):=\operatorname{gbmMil}(r,\sigma,T,s_0,\ell,z)=X_{2^\ell},$$
where $X_0=s_0$ and
$$X_{i+1}=X_i+rX_ih_\ell+\sigma X_i\sqrt{h_\ell}\,z_i+\tfrac12\,\sigma X_i\,\sigma\,\big((\sqrt{h_\ell}z_i)^2-h_\ell\big).$$
This is the recursion of M2 with $a(S)=rS$ and $b(S)=\sigma S$, whose derivative is $\sigma$ everywhere. It runs for $2^\ell$ steps (a natural number) and uses exactly $z_0,\dots,z_{2^\ell-1}$. Edge cases:
- $\ell=0$: one step of size $T$, giving $s_0\big(1+rT+\sigma\sqrt Tz_0+\tfrac{\sigma^2}{2}((\sqrt Tz_0)^2-T)\big)$.
- $T<0$: deterministic, $s_0(1+(r-\sigma^2/2)h_\ell)^{2^\ell}$.
- $T=0$: $s_0$.

### M9. `gbm_mil_strong_error_level` (theorem)

**Rendering.** For all real $r,\sigma,s_0$, every real $T$ with $0\le T$ and every $\ell\in\mathbb N$, with $h_\ell=T/2^\ell$,
$$\int_{\mathbb R^{\mathbb N}}\Big(s_0\exp\!\Big(\big(r-\tfrac{\sigma^2}{2}\big)T+\sigma\sqrt{h_\ell}\sum_{i=0}^{2^\ell-1}z_i\Big)-\mathrm{Mil}_\ell(z)\Big)^2 d\mathbb P(z)\;\le\;C(r,\sigma,T,s_0)\,h_\ell^2 .$$
The first term is gbmExact (D6) at level $\ell$, and $\mathrm{Mil}_\ell$ is as in M8; both use the same $z_0,\dots,z_{2^\ell-1}$. The right side is $s_0^2e^{(2|r|+\sigma^2)T}\lambda^2(30\lambda^2T^2+16\lambda T+4)\,T^2/4^\ell$; its constant does not depend on $\ell$. For $T=0$ both sides are $0$.

**Assessment.**
- **Truth: true.** It is M7 with $n=2^\ell$ and $h=T/2^\ell\ge0$, since $(2^\ell)\cdot(T/2^\ell)=T$ as reals and $\sqrt{h}\sum_{i<2^\ell}z_i$ matches D6. Numerically: 0 violations over 9 parameter sets with $\ell\le24$ and 1,500 random $(r,\sigma,T,\ell)$; the maximum ratio is $0.0083$ (s3).
- **Non-vacuity:** $r=0.05$, $\sigma=0.2$, $s_0=100$, $T=1$, $\ell=4$ gives $5.396\cdot10^{-3}\le2.068$.
- **Junk values:** as in M7. $T\ge0$ makes $\sqrt{T/2^\ell}$ the genuine root, and the integrand is integrable.
- **Concerns:**
  - As in M7: explicit, loose constant; sharp $h^2$ rate (successive ratios tend to $4$); strong coupling through the same normals.
  - $0\le T$ is load-bearing: $T=-10$, $\ell=0$, $r=0$, $\sigma=1$, $s_0=1$ gives $20281>12.9$ (s8).

### M10. `gbm_mil_weak_error_le` (theorem)

**Rendering.** Let $r,\sigma,s_0$ be real, $T$ real with $0\le T$, $g:\mathbb R\to\mathbb R$ a function and $K$ a real number such that
$$|g(x)-g(y)|\le K|x-y|\quad\text{for all real }x,y .$$
Then for every $\ell\in\mathbb N$,
$$\Big|\int_{\mathbb R^{\mathbb N}}\Big[g\big(\mathrm{Mil}_\ell(z)\big)-g\Big(s_0\exp\!\big((r-\tfrac{\sigma^2}{2})T+\sigma\sqrt T\,z_0\big)\Big)\Big]\,d\mathbb P(z)\Big|\;\le\;K\,\sqrt{C(r,\sigma,T,s_0)\,T^2}\;\big(2^\ell\big)^{-1}.$$
Details:
- The second term is gbmExact at level $0$: it uses only $z_0$, with $\sqrt{T/1}\sum_{i<1}z_i=\sqrt Tz_0$.
- $\mathrm{Mil}_\ell$ (M8) uses $z_0,\dots,z_{2^\ell-1}$ with step $T/2^\ell$.
- The integral is of the difference, because the integral body extends over the minus sign, and the absolute value is taken of the whole integral.
- The hypothesis on $g$ forces $K\ge0$ (take $x\neq y$). No separate measurability assumption on $g$ is made.

**Assessment.**
- **Truth: true.**
  1. $g$ is continuous, hence measurable, and $|g(x)|\le|g(0)|+K|x|$. So $g(\mathrm{Mil}_\ell)$, $g(\mathrm{Ex}_0)$ and $g(\mathrm{Ex}_\ell)$ are integrable, where $\mathrm{Ex}_\ell$ is gbmExact at level $\ell$.
  2. $\mathrm{Ex}_\ell$ and $\mathrm{Ex}_0$ have the same law under $\mathbb P$, because $\sqrt{T/2^\ell}\sum_{i<2^\ell}z_i$ and $\sqrt Tz_0$ are both $\mathcal N(0,T)$. So the integral equals $\int[g(\mathrm{Mil}_\ell)-g(\mathrm{Ex}_\ell)]\,d\mathbb P$.
  3. Its absolute value is $\le K\int|\mathrm{Mil}_\ell-\mathrm{Ex}_\ell|\le K\big(\int|\mathrm{Mil}_\ell-\mathrm{Ex}_\ell|^2\big)^{1/2}\le K\sqrt{CT^2/4^\ell}$ by M9.
  4. Numerically, for three call-payoff settings and $\ell=0,\dots,6$, the weak error is between $0.2\%$ and $2.1\%$ of the bound and halves with each level (s5).
- **Non-vacuity:** $g(x)=\max(x-1,0)$, $K=1$, $s_0=1$, $r=0.05$, $\sigma=0.2$, $T=1$, $\ell=0$: the left side is $4.170\cdot10^{-3}$ (exact quadrature) and the right side is $0.2301$.
- **Junk values:** the integrand is integrable, so the integral is genuine. The right side is $\ge0$. For $K<0$ the hypothesis on $g$ is unsatisfiable, which only means that every instance has $K\ge0$; nothing holds for a wrong reason.
- **Concerns:**
  - The reference value is a level-0 exact sample driven by $z_0$, not the same-path solution. Only its law matters, so the statement is exactly $|\mathbb E g(\mathrm{Mil}_\ell)-\mathbb E g(S_T)|\le K\sqrt{CT^2}\,2^{-\ell}$.
  - This weak bound is derived from the strong bound (first order in $h$, Lipschitz $g$). It is not a separate weak-order analysis, though order 1 is also the observed order.
  - The constant is explicit and depends on $g$ only through $K$.
  - $0\le T$ is load-bearing: $T=-10$, $g=\mathrm{id}$, $r=0$, $\sigma=1$ gives $142>3.59$ (s8).

### M11. `gbm_mil_correction_variance_le` (theorem)

**Rendering.** With $r,\sigma,s_0,T\ge0,g,K$ and the Lipschitz hypothesis exactly as in M10, for every $\ell\in\mathbb N$,
$$\operatorname{Var}_{\mathbb P}\big[D_{\ell+1}\big]\;\le\;10\,K^2\,\big(C(r,\sigma,T,s_0)\,T^2\big)\,\big(4^{\ell+1}\big)^{-1},$$
where
$$D_{\ell+1}(z)=g\big(\mathrm{Mil}_{\ell+1}(z)\big)-g\big(\mathrm{Mil}_\ell(\operatorname{pairAvg}z)\big).$$
- The fine term runs $2^{\ell+1}$ Milstein steps of size $T/2^{\ell+1}$ with normals $z_0,\dots,z_{2^{\ell+1}-1}$.
- The coarse term runs $2^\ell$ steps of size $T/2^\ell$ with normals $(z_{2k}+z_{2k+1})/\sqrt2$ for $k=0,\dots,2^\ell-1$.
- The recursion is that of M8.
- $\operatorname{Var}_{\mathbb P}[D]$ is Mathlib's `variance`: the $[0,\infty]$-valued integral $\int\big|D-\int D\,d\mathbb P\big|^2d\mathbb P$, converted to a real number by `toReal`, which sends $+\infty$ to $0$. Here $\int D\,d\mathbb P$ is the Bochner integral, itself $0$ if $D$ is not integrable. So the variance is $0$ whenever that integral is $+\infty$.

**Assessment.**
- **Truth: true.**
  1. Pointwise, $\mathrm{Ex}_{\ell+1}(z)=\mathrm{Ex}_\ell(\operatorname{pairAvg}z)$, because $\sqrt{T/2^\ell}/\sqrt2=\sqrt{T/2^{\ell+1}}$ and $\sum_{k<2^\ell}(z_{2k}+z_{2k+1})=\sum_{i<2^{\ell+1}}z_i$.
  2. `pairAvg` pushes $\mathbb P$ forward to $\mathbb P$: disjoint pairs, and each $(z_{2k}+z_{2k+1})/\sqrt2\sim\mathcal N(0,1)$.
  3. Hence $\operatorname{Var}D\le\mathbb E D^2\le K^2\,\mathbb E(\mathrm{Mil}_{\ell+1}-\mathrm{Mil}_\ell\circ\operatorname{pairAvg})^2\le2K^2\big(CT^2/4^{\ell+1}+CT^2/4^\ell\big)=10K^2CT^2/4^{\ell+1}$, using M9 twice.
  4. Numerically, the Monte Carlo variance is $2\cdot10^{-5}$ to $5\cdot10^{-4}$ of the bound and decays like $4^{-\ell}$ (s5).
- **Non-vacuity:** the call example of M10 with $\ell=0$ gives $\operatorname{Var}D_1\approx1.63\cdot10^{-5}$ against a bound of $0.132$.
- **Junk values:** `variance` would be $0$ for $D\notin L^2$, but $D$ is in $L^2$ (Lipschitz $g$ of variables with finite second moments), so the variance is genuine.
- **Concerns:**
  - The constant is $10=2(1+4)$.
  - The hypothesis $0\le T$ is not needed: for $T<0$ both paths are deterministic and the variance is $0$.
  - The statement bounds the variance of the level-$(\ell+1)$ MLMC correction under the standard pairwise coupling; the rate is $\beta=2$.

### M12. `gbm_mil_mlmc_theorem1` (theorem)

**Rendering.** Let $r,\sigma,s_0$ be real, $T$ real with $0\le T$, and $g:\mathbb R\to\mathbb R$, $K\in\mathbb R$ with $|g(x)-g(y)|\le K|x-y|$ for all real $x,y$. Then **there exists** a real $c_4>0$ such that **for every** real $\varepsilon$ with $0<\varepsilon<e^{-1}$ **there exist** $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ satisfying all of:
1. $N_\ell>0$ for **every** $\ell\in\mathbb N$ (not only for $\ell\le L$);
2. the mean-square bound
   $$\int_{\Omega}\Big(\sum_{\ell=0}^{L}\frac{1}{N_\ell}\sum_{n=0}^{N_\ell-1}D_\ell\big(x_{(\ell,n)}\big)\;-\;\mu_g\Big)^2\,d\mathbb Q(x)\;<\;\varepsilon^2 ;$$
3. the cost bound
   $$\sum_{\ell=0}^{L}N_\ell\,2^\ell\;\le\;c_4\,\varepsilon^{-2}.$$

The objects are as follows.
- $\Omega=(\mathbb R^{\mathbb N})^{\mathbb N\times\mathbb N}$. A point $x$ assigns a real sequence $x_{(\ell,n)}\in\mathbb R^{\mathbb N}$ to every pair $(\ell,n)$.
- $\mathbb Q=\bigotimes_{(\ell,n)\in\mathbb N\times\mathbb N}\mathbb P$ is the product of copies of $\mathbb P$ (D1). The $x_{(\ell,n)}$ are therefore independent, each a sequence of i.i.d. standard normals.
- The inner average is `blockMean` (D4) of `fineCoarseDiff` (D5) with the sampling map $(p,x)\mapsto x_p$. Unfolded, it is $N_\ell^{-1}\sum_{n<N_\ell}D_\ell(x_{(\ell,n)})$, with
  $$D_0(y)=g\big(\mathrm{Mil}_0(y)\big),\qquad D_{\ell+1}(y)=g\big(\mathrm{Mil}_{\ell+1}(y)\big)-g\big(\mathrm{Mil}_\ell(\operatorname{pairAvg}y)\big).$$
  Here $\mathrm{Mil}_\ell$ is the $2^\ell$-step Milstein recursion of M8 with step $T/2^\ell$, and $\mathrm{Mil}_0(y)=s_0\big(1+rT+\sigma\sqrt Ty_0+\tfrac{\sigma^2}2((\sqrt Ty_0)^2-T)\big)$.
- $\mu_g=\int_{\mathbb R}g\big(s_0\exp((r-\tfrac{\sigma^2}{2})T+\sigma\sqrt T\,w)\big)\,d\mathcal N(w)$.
- $\varepsilon^{-2}$ is the real-exponent power, equal to $1/\varepsilon^2$ since $\varepsilon>0$.
- Both integrals are Bochner integrals.
- The sum over $\ell$ ends before the minus sign, so $\mu_g$ is subtracted once, from the whole sum.

Quantifier order and dependence: $c_4$ is chosen after $r,\sigma,s_0,T,g,K$ (and the two hypotheses) and before $\varepsilon$, so it may depend on all of these but not on $\varepsilon$. $L$ and $N$ are chosen after $\varepsilon$.

**Assessment.**
- **Truth: true.** This is the multilevel complexity argument with bias rate $2^{-L}$ (M10: $B=K\sqrt{CT^2}$), variance rate $V_\ell\le V4^{-\ell}$ for $\ell\ge1$ (M11: $V=10K^2CT^2$) and cost $2^\ell$.
  1. The level-0 variance is bounded by $V_0\le K^2s_0^2(\sigma^2T+\sigma^4T^2/2)$.
  2. By independence of the $x_{(\ell,n)}$ under $\mathbb Q$, the MSE equals $\big(\mathbb E g(\mathrm{Mil}_L)-\mu_g\big)^2+\sum_\ell\operatorname{Var}(D_\ell)/N_\ell$. The mean telescopes to $\mathbb E g(\mathrm{Mil}_L)$ because `pairAvg` preserves $\mathbb P$.
  3. Choose the least $L$ with $B^24^{-L}\le\varepsilon^2/4$, and $N_\ell=\max\big(1,\lceil2\varepsilon^{-2}S_L\sqrt{V_\ell/2^\ell}\rceil\big)$ with $S_L=\sum_{\ell\le L}\sqrt{V_\ell2^\ell}$.
  4. Then MSE $\le\tfrac34\varepsilon^2<\varepsilon^2$, and cost $\le2\varepsilon^{-2}S_\infty^2+\max(2,8B/\varepsilon)\le c_4\varepsilon^{-2}$ with $c_4=2S_\infty^2+8B/e+1$ and $S_\infty=\sqrt{V_0}+\sqrt V/(\sqrt2-1)$. The step uses $\varepsilon<e^{-1}$.
  5. Checked in s6 for four parameter sets over $\varepsilon\in[3.7\cdot10^{-9},e^{-1})$. The actual estimator, simulated for a call, has empirical MSE $\approx0.03$–$0.04\,\varepsilon^2$.
- **Non-vacuity:** call payoff $g(x)=\max(x-1,0)$, $K=1$, $r=0.05$, $\sigma=0.2$, $s_0=1$, $T=1$. Here $c_4=9.35$ works. For example, at $\varepsilon=0.05$: $L=4$, $N=(246,313,111,40,14)$, cost $1860\le3740$, simulated MSE $8.4\cdot10^{-5}<2.5\cdot10^{-3}$. The conclusion is not trivial: the level-$L$ bias is nonzero for every $L$, so $L\to\infty$ is forced while the cost must stay $O(\varepsilon^{-2})$; single-level Monte Carlo would cost order $\varepsilon^{-3}$.
- **Junk values:**
  - $N_\ell^{-1}$ is genuine because $N_\ell>0$ is required.
  - $\varepsilon^{(-2)}$ is genuine because $\varepsilon>0$.
  - $\mathbb Q$ and $\mathbb P$ are genuine products of probability measures.
  - The integrand $(Y-\mu_g)^2$ is integrable (a finite sum of $L^2$ functions of finitely many coordinates). So the integral is the true MSE and not the junk $0$, which would trivially be $<\varepsilon^2$.
- **Concerns:**
  - $c_4$ is existential and not explicit. It may depend on $g$ itself, not only on $K$.
  - The constants the packet's bounds yield are astronomically large when $(|r|+\sigma^2)T$ is large: $c_4\approx1.2\cdot10^{17}$ at $r=2$, $\sigma=1.5$, $s_0=3$, $T=3$.
  - The cost counts $2^\ell$ per level-$\ell$ sample; the $2^{\ell-1}$ coarse steps are not counted.
  - Only $\varepsilon<e^{-1}$ is covered, and the MSE inequality is strict.
  - The estimator draws a fresh independent normal sequence for every $(\ell,n)$. The coarse path of $D_\ell$ uses the pairwise-averaged normals of the same sample.
  - $0\le T$ is not needed: for $T<0$ everything is deterministic, the estimator equals $g(\mathrm{Mil}_L)$, the bias is $O(2^{-L})$, and $N_\ell=1$ gives cost $O(\varepsilon^{-1})$.

---

## Numerical sanity checks

All scripts are in `scratchpad/readback/round9/work_K/`, each saved next to its output (`.out`). The exact computations use `mpmath` at 50 to 110 significant digits, because $\alpha^n$, $\beta^n$ and $\gamma^n$ cancel almost completely. Monte Carlo runs use seeded pure-Python `random`.

### N1. One-step moments (`s1_symbolic_and_moments`)

| Check | Result |
|---|---|
| Symbolic check of $\operatorname{milsteinStep}(rS,\sigma S,h,S,s\,x)-S\cdot\mathrm{MF}$, with $s$ an arbitrary real standing for $\sqrt h$ | simplifies to $0$; $b'=\sigma$; with $s=0$ the factor is $1+rh-\sigma^2h/2$ |
| $\mathbb E[A^2]$, $\mathbb E[AB]$, $\mathbb E[B^2]$ by symbolic Gaussian integration, compared with the closed forms $\alpha,\beta,\gamma$ | all differences $=0$; also $\mathbb E A=e^{rh}$ and $\mathbb E B=1+rh$ |
| Taylor expansion | $\alpha-\beta=(\tfrac{r^2}2+r\sigma^2)h^2+O(h^3)$; $\beta-\gamma$ has the same $h^2$ term; $\alpha-2\beta+\gamma=(\sigma^2r^2+\tfrac{\sigma^6}6)h^3+O(h^4)$ |
| Quadrature (30 digits) against the closed forms at 9 triples $(r,\sigma,h)$, including $(-10,0,1)$, $(0,3,1)$, $(1,0.3,5)$, $(0.3,1.5,3)$ | maximum relative error $6.7\cdot10^{-26}$ |
| $\max(\lvert\alpha\rvert,\lvert\beta\rvert,\lvert\gamma\rvert)/e^{(2\lvert r\rvert+\sigma^2)h}$ on a grid ($r\in[-20,20]$, $\sigma\le5$, $h\le10$) | $1.0$ (never exceeded) |

### N2. Product identity M4 (`s2_product_identity`, `s2b_recheck_sign_tanh`)

| $(F,G)$ | Parameters | Closed-form RHS | Check | Agreement |
|---|---|---|---|---|
| $(A,\mathrm{MF})$ | $r=0.05,\sigma=0.2,h=0.25,s_0=1,n=4$ | $8.398062\cdot10^{-6}$ | Monte Carlo ($4\cdot10^5$ samples) $8.3515\cdot10^{-6}\pm3.6\cdot10^{-8}$ (1 s.e.) | $z=-1.28$ |
| $(A,\mathrm{MF})$ | $r=-0.5,\sigma=1,h=0.25,s_0=2,n=4$ | $0.1317934$ | Monte Carlo $0.13054\pm0.0018$ | $z=-0.70$ |
| $(A,\mathrm{MF})$ | $r=1,\sigma=0.5,h=0.1,s_0=1,n=10$ | $0.05937421$ | Monte Carlo $0.059378\pm0.00037$ | $z=0.01$ |
| $(A,\mathrm{MF})$, 4 more settings | including $r=-2$ and $n=1,2,3$ | — | Monte Carlo | $\lvert z\rvert\le0.94$ |
| $(A,\mathrm{MF})$, $n=2$ | 5 settings | — | 2-D Gauss–Hermite quadrature (80 nodes, 40 digits) | relative difference $\le2.9\cdot10^{-32}$ |
| $(\cos x,\,x^2)$, $(x,\,1+x)$, $(\operatorname{sign}x,\tanh x)$ | $s_0=1.5$, $n=0,\dots,3$ | quadrature moments | Monte Carlo ($2\cdot10^5$) | $\lvert z\rvert\le2.46$. The one $z=-2.46$ case, re-run with $10^6$ samples and 3 fresh seeds, gives $z=-0.37,-0.53,1.38$ |

### N3. Strong error M7 and M9 against exact values (`s3_strong_error`)

The exact left side is $s_0^2(\alpha^n-2\beta^n+\gamma^n)$, validated in N2. The bound is $C(r,\sigma,nh,s_0)h^2$. The ratio does not depend on $s_0\neq0$.

| Scan | Cases | Violations | Max true/bound (location) |
|---|---|---|---|
| Grid: $r\in\{-20,-5,-1,-0.3,-0.05,0,0.05,0.3,1,5,20\}$, $\sigma\in\{0,0.05,0.2,0.5,1,2,5\}$, $h\in\{10^{-8},\dots,10\}$ (11 values), $n\in\{0,1,2,3,5,10,30,100,10^3,10^4,10^5,10^6\}$ | 10,164 | 0 | $0.00825$ at $(r,\sigma,h,n)=(1,0.05,10^{-4},10^6)$ |
| ditto, restricted to $(\lvert r\rvert+\sigma^2)h>1$ | (subset) | 0 | $0.00160$ at $(0.3,0.2,3,1)$ |
| Reduced variables $u=rh$, $v=\sigma^2h$: grid over $w=\lvert u\rvert+v\in[10^{-6},3]$ and $n\le10^6$ | 11,616 | 0 | $0.00825$ |
| Random $(u,v,n)$ | 6,000 | 0 | $0.00809$ |
| Local maximisation | — | — | $0.0083333$, approached as $u\to0^+$, $v=0$, $nw\to\infty$, i.e. **$1/120$** |
| Level version: 9 settings ($r\in[-2,3]$, $\sigma\le2.5$, $s_0\le100$, $T\le10$) with $\ell\le24$, plus 1,500 random settings ($\lvert r\rvert\le20$, $\sigma\le5$, $T\le16$, $\ell\le22$) | 1,644 | 0 | $0.0083$ |
| Edge cases: $h=0$; $n=0$; $s_0\in\{0,-3,100\}$; $T=0$ | — | 0 | $0\le0$ for $h=0$ and $T=0$; $0\le0.399$ for $n=0$ |

The $h^2$ rate is attained. Write $\mathcal L=s_0^2e^{(2r+\sigma^2)T}\big(T(\sigma^2r^2+\sigma^6/6)+T^2(r^2/2+r\sigma^2)^2\big)$.

| Setting $(r,\sigma,s_0,T)$ | $\ell$ | $h_\ell$ | Exact MSE | Bound | True/bound | MSE$/(h_\ell^2\mathcal L)$ | MSE$_{\ell-1}$/MSE$_\ell$ |
|---|---|---|---|---|---|---|---|
| $(0.05,0.2,100,1)$ | 0 | 1 | $1.2078$ | $529.50$ | $2.28\cdot10^{-3}$ | $0.866$ | – |
| | 4 | $1/16$ | $5.3965\cdot10^{-3}$ | $2.0684$ | $2.61\cdot10^{-3}$ | $0.9907$ | $3.963$ |
| | 12 | $2.44\cdot10^{-4}$ | $8.3114\cdot10^{-8}$ | $3.1561\cdot10^{-5}$ | $2.63\cdot10^{-3}$ | $0.99996$ | $3.99985$ |
| | 24 | $5.96\cdot10^{-8}$ | $4.9541\cdot10^{-15}$ | $1.8812\cdot10^{-12}$ | $2.63\cdot10^{-3}$ | $1.000000$ | – |
| $(-2,0.3,1,1)$ | 0 | 1 | $1.3593$ | $4.3966\cdot10^{4}$ | $3.1\cdot10^{-5}$ | $18.47$ | – |
| | 4 | $1/16$ | $2.9975\cdot10^{-4}$ | $171.74$ | $1.75\cdot10^{-6}$ | $1.0426$ | $4.165$ |
| | 24 | $5.96\cdot10^{-8}$ | $2.6148\cdot10^{-16}$ | $1.5620\cdot10^{-10}$ | $1.67\cdot10^{-6}$ | $1.000000$ | – |
| $(1,0.5,1,2)$ | 0 | 2 | $46.07$ | $1.3024\cdot10^{5}$ | $3.5\cdot10^{-4}$ | $0.046$ | – |
| | 8 | $7.8\cdot10^{-3}$ | $1.4728\cdot10^{-2}$ | $1.9874$ | $7.41\cdot10^{-3}$ | $0.9729$ | $3.893$ |
| | 24 | $1.19\cdot10^{-7}$ | $3.5245\cdot10^{-12}$ | $4.6272\cdot10^{-10}$ | $7.62\cdot10^{-3}$ | $1.000000$ | – |

The same behaviour holds for $(-0.5,1,1,1)$, $(0,0.8,1,5)$, $(0.3,1.5,1,1)$, $(3,0,1,1)$, $(0.1,2.5,1,0.5)$ and $(-0.05,0.1,50,10)$; see the output file.

### N4. Inequality M5 (`s4_pow_ineq`, exact rational arithmetic)

| Test | Cases | Violations | Max LHS/RHS |
|---|---|---|---|
| Random $a,b,c\in[-M,M]$, $M\in\{1\}\cup[1,50]$, often with near-coincident points, $n\in\{0,\dots,12,15,20,30\}$ | 60,000 | 0 | $1.000000$ ($n=1$, $a\approx b$) |
| Corners and boundaries: $a,b,c\in\{\pm M,\pm M/2,0,M/3,M\mp10^{-3}\}$, $M\in\{1,1.5,2,10\}$, $n\le15$ | 32,768 | 0 | $1$ (equality in 112 cases) |
| Adversarial pattern search, $n\in\{1,2,3,4,5,8,12,20\}$ | 60 starts per $n$ | 0 | $\to1$ for every $n$ (at $a=b\to\pm1$, $c\to b$); on the family $a-2b+c=0$ the ratio tends to $(n-1)/n$ |
| Dropping $1\le M$: $M=\tfrac12$, $(\tfrac12,0,-\tfrac12)$, $n=2$ | — | fails: $\tfrac12>\tfrac14$ | also fails for $M=0.7$, $n=2$ and for $M=0.1$, $n=4$ |

### N5. Weak error M10 and correction variance M11 by Monte Carlo (`s5_weak_variance_mc`)

The payoff is the call $g(x)=\max(x-k,0)$ with $K=1$.
- **Weak error** is $\mathbb E g(\mathrm{Mil}_\ell)-\mathbb E g(S_T)$. At $\ell=0$ it is computed exactly by 1-D quadrature; for $\ell\ge1$ by the coupled Monte Carlo estimator $g(\mathrm{Mil}_\ell)-g(\mathrm{Ex}_\ell)$, which has the same mean as the literal integrand of M10 and lower variance. The literal-integrand estimate was also computed and agrees within its larger error bars.
- **Target:** $\mathbb E g(S_T)$ from Black–Scholes (undiscounted) matches the literal target integral of M12 by quadrature to 10 digits.
- **Variance:** the unbiased sample variance of $D_{\ell+1}$.
- Sample sizes: $N=2\cdot10^5$ for $\ell\le2$, $10^5$ for $\ell\le4$, $4\cdot10^4$ for $\ell\le6$.
- Digits in parentheses give $\pm2$ standard errors in the last digits shown; for example $-1.153(10)\cdot10^{-3}$ means $(-1.153\pm0.010)\cdot10^{-3}$.

| Setting | $\ell$ | Weak error | Weak bound | Ratio | $\operatorname{Var}D_{\ell+1}$ | Variance bound | Ratio |
|---|---|---|---|---|---|---|---|
| $r=0.05,\sigma=0.2,s_0=1,T=1,k=1$ ($C=0.05295$) | 0 | $-4.170\cdot10^{-3}$ (exact) | $0.2301$ | $0.018$ | $1.625\cdot10^{-5}$ | $0.1324$ | $1.2\cdot10^{-4}$ |
| | 2 | $-1.153(10)\cdot10^{-3}$ | $0.05753$ | $0.020$ | $1.327\cdot10^{-6}$ | $8.273\cdot10^{-3}$ | $1.6\cdot10^{-4}$ |
| | 4 | $-2.961(35)\cdot10^{-4}$ | $0.01438$ | $0.021$ | $9.195\cdot10^{-8}$ | $5.171\cdot10^{-4}$ | $1.8\cdot10^{-4}$ |
| | 6 | $-7.44(14)\cdot10^{-5}$ | $3.595\cdot10^{-3}$ | $0.021$ | $6.040\cdot10^{-9}$ | $3.232\cdot10^{-5}$ | $1.9\cdot10^{-4}$ |
| $r=-0.5,\sigma=1,s_0=1,T=1,k=1$ ($C=1587.7$) | 0 | $+0.1581$ (exact) | $39.85$ | $0.0040$ | $8.41\cdot10^{-2}$ | $3969$ | $2.1\cdot10^{-5}$ |
| | 2 | $+2.73(7)\cdot10^{-2}$ | $9.962$ | $0.0027$ | $1.205\cdot10^{-2}$ | $248.1$ | $4.9\cdot10^{-5}$ |
| | 4 | $+5.55(28)\cdot10^{-3}$ | $2.490$ | $0.0022$ | $7.72\cdot10^{-4}$ | $15.51$ | $5.0\cdot10^{-5}$ |
| | 6 | $+1.46(12)\cdot10^{-3}$ | $0.6226$ | $0.0023$ | $5.44\cdot10^{-5}$ | $0.9691$ | $5.6\cdot10^{-5}$ |
| $r=0.3,\sigma=0.6,s_0=2,T=2,k=1.5$ ($C=919.8$) | 0 | $-0.5861$ (exact) | $60.66$ | $0.0097$ | $0.4184$ | $9198$ | $4.5\cdot10^{-5}$ |
| | 2 | $-0.1921(35)$ | $15.16$ | $0.013$ | $0.1448$ | $574.9$ | $2.5\cdot10^{-4}$ |
| | 4 | $-5.27(16)\cdot10^{-2}$ | $3.791$ | $0.014$ | $1.621\cdot10^{-2}$ | $35.93$ | $4.5\cdot10^{-4}$ |
| | 6 | $-1.35(6)\cdot10^{-2}$ | $0.9478$ | $0.014$ | $1.154\cdot10^{-3}$ | $2.246$ | $5.1\cdot10^{-4}$ |

The weak errors halve per level (order 1) and the correction variances quarter per level ($\beta=2$), as the bounds predict; the bounds hold with wide margins. The same run also estimated the strong MSE by Monte Carlo and compared it with the exact formula of N3. They agree within 6% in every case except $\sigma=1$, $\ell\ge5$, where the estimate is 16–18% off with $4\cdot10^4$ samples. A re-run of that case with $2\cdot10^5$ samples and 4 seeds (`s5b_strong_mse_recheck`) gives $|z|\le0.93$ against the exact values $5.427\cdot10^{-4}$ ($\ell=5$) and $1.359\cdot10^{-4}$ ($\ell=6$). The deviation is therefore sampling noise from heavy-tailed squared errors; even at $2\cdot10^5$ samples the relative standard error is 4–9%.

### N6. MLMC complexity M12 (`s6_mlmc`)

(a) Using only the packet's bounds (M10, M11 and the elementary $V_0$ bound), with the plan described in the M12 assessment, over 161 values of $\varepsilon$ from $3.7\cdot10^{-9}$ up to $e^{-1}$:

| $(r,\sigma,s_0,T)$ | $C$ | $B$ | $V$ | $V_0\le$ | Explicit $c_4$ | Max cost$\cdot\varepsilon^2$ | MSE bound $<\varepsilon^2$ and cost $\le c_4\varepsilon^{-2}$ for all $\varepsilon$ |
|---|---|---|---|---|---|---|---|
| $(0.05,0.2,1,1)$ | $0.05295$ | $0.2301$ | $0.5295$ | $0.0408$ | $9.35$ | $7.67$ | yes |
| $(-0.5,1,1,1)$ | $1588$ | $39.85$ | $1.588\cdot10^4$ | $1.5$ | $1.87\cdot10^5$ | $1.87\cdot10^5$ | yes |
| $(0.3,0.6,2,2)$ | $919.8$ | $60.66$ | $3.68\cdot10^4$ | $3.92$ | $4.33\cdot10^5$ | $4.33\cdot10^5$ | yes |
| $(2,1.5,3,3)$ | $1.15\cdot10^{14}$ | $3.22\cdot10^7$ | $1.03\cdot10^{16}$ | $265.8$ | $1.21\cdot10^{17}$ | $1.21\cdot10^{17}$ | yes |

(b) Replications of the actual estimator for the call with $r=0.05$, $\sigma=0.2$, $s_0=1$, $T=1$, strike $1$:

| $\varepsilon$ | $L$ | $N_\ell$ | Cost | Cost$\cdot\varepsilon^2$ | Replications | Empirical MSE | MSE$/\varepsilon^2$ |
|---|---|---|---|---|---|---|---|
| $0.1$ | 3 | $(55,69,25,9)$ | 365 | 3.65 | 2000 | $3.92\cdot10^{-4}$ | $0.039$ |
| $0.05$ | 4 | $(246,313,111,40,14)$ | 1860 | 4.65 | 1000 | $8.36\cdot10^{-5}$ | $0.033$ |
| $0.02$ | 5 | $(1665,2121,750,266,94,34)$ | 13627 | 5.45 | 300 | $1.29\cdot10^{-5}$ | $0.032$ |

### N7. Local constants behind the M7 proof route (`s7_local_constants`)

On $0<w=(|r|+\sigma^2)h\le1$ (grid of $400\times201\times2$ points in $(w,|u|/w,\operatorname{sign}u)$):
- $\sup|\alpha-\beta|/w^2\approx1.952$ and $\sup|\beta-\gamma|/w^2\approx1.437$, both at $u=1$, $v=0$, giving $c_ac_b\approx2.80$ (needs $\le30$);
- $\sup|\alpha-2\beta+\gamma|/w^3\approx0.538$ (needs $\le16$);
- $\max(|\alpha|,|\beta|,|\gamma|)/M=1$.

The proof route through M4 and M5 therefore closes with large slack. The regime $w\ge1$ is covered by the trivial bound $4M^n\le4M^nw^2$.

### N8. Negative time (`s8_negative_time`)

| Statement with its nonnegativity hypothesis dropped | Instance | LHS | RHS | Holds? |
|---|---|---|---|---|
| M7 without $0\le h$ | $r=0,\sigma=1,s_0=1,h=-1,n=10$ | $8235.2$ | $0.129$ | **no** |
| M9 without $0\le T$ | $r=0,\sigma=1,s_0=1,T=-10,\ell=0$ | $20281$ | $12.9$ | **no** |
| M10 without $0\le T$ | same, $g=\mathrm{id}$, $K=1$ | $142.4$ | $3.59$ | **no** |
| M11 without $0\le T$ | any $T<0$ | $0$ (deterministic) | $\ge0$ | yes: hypothesis not needed |

---

## Files

- `scratchpad/readback/round9/work_K/s1_symbolic_and_moments.py` / `.out`: symbolic one-step identity, closed-form moments, Taylor terms, quadrature.
- `scratchpad/readback/round9/work_K/s2_product_identity.py` / `.out`, `s2b_recheck_sign_tanh.py` / `.out`: product identity by Monte Carlo and 2-D quadrature.
- `scratchpad/readback/round9/work_K/s3_strong_error.py` / `.out`: exact strong-error scans, supremum search, $h^2$ rate.
- `scratchpad/readback/round9/work_K/s4_pow_ineq.py` / `.out`: exact tests of M5.
- `scratchpad/readback/round9/work_K/s5_weak_variance_mc.py` / `.out`: weak error and correction variance by Monte Carlo.
- `scratchpad/readback/round9/work_K/s5b_strong_mse_recheck.py` / `.out`: larger re-run of the heavy-tailed strong-MSE Monte Carlo ($\sigma=1$, $\ell=5,6$).
- `scratchpad/readback/round9/work_K/s6_mlmc.py` / `.out`: explicit complexity constant and MLMC estimator replications.
- `scratchpad/readback/round9/work_K/s7_local_constants.py` / `.out`: local constants for the M7 proof route.
- `scratchpad/readback/round9/work_K/s8_negative_time.py` / `.out`: counterexamples for negative time.
