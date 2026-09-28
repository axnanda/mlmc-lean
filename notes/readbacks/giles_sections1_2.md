# Blind read-back audit: packet C (`packet_C_g_section1_2.lean`)

- **Date:** 2026-09-27
- **Packet:** `packet_C_g_section1_2.lean`
- **Number of declarations audited:** **60**
  - 49 in the seven module sections: 39 theorems or lemmas and 10 definitions (`rectSet`, `ml2rWeightBound`, `ml2rLevel`, `crossDiff`, `singleTerm`, `singleTermN`, `geomLevelProb`, `optimalLevelProb`, `subsetCorr`, `subsetCost`).
  - 11 supporting definitions in the trailing section "definitions used above, from other modules" (`sumSqrtVC`, `lagrangeN`, `levelDiff`, `complexityBound`, `Vb`, `Cb`, `levelL`, `dot`, `box`, `ml2rWeight`, `ml2rNode`).
  - The sections `levelSelection` and `prob` declare only variables, so there is nothing in them to audit.
- **Auditor:** an independent session, working blind.
- **Rules followed:**
  1. I read only three things: the packet, `prove2me_workspace/references/mission_auditor.md`, and the Mathlib and Lean-core sources, the last only to confirm the conventions of constants the statements use. I did not open project Lean sources, `docs/`, `notes/`, README, PLAN, `prove2me/` (except the one allowed file), `scripts/`, git history, papers or the web.
  2. I inferred no meaning from declaration names or file names. Every "Rendering" paragraph translates the code literally: every binder, hypothesis and typeclass assumption is listed, project definitions are expanded inline, and the exact strength of each relation and the order of quantifiers are kept. This follows the principles in `mission_auditor.md`: translate the code, not the intent; account for every binder; expand non-standard definitions; surface degenerate and junk cases; keep logical precision; use mathematical notation.
  3. "Rendering" paragraphs contain no judgment. All assessments are in the other four parts (Truth, Non-vacuity, Junk values, Concerns), as the task requires.
  4. This is a Markdown file, not a JSON payload, so LaTeX is written with single backslashes.
  5. Numerical sanity checks are in `readback/round5/work_C_g_section1_2/` (listed at the end). All of them passed.

---

## Verdict overview

| # | Declaration | Kind | Truth | Hypotheses satisfiable | Junk-sensitive in a meaning-changing way | Flag |
|---|---|---|---|---|---|---|
| A1 | `sumSqrtVC` | def | – | – | no | – |
| A2 | `lagrangeN` | def | – | – | no | mild (τ = 0 gives 0) |
| A3 | `levelDiff` | def | – | – | no | – |
| A4 | `complexityBound` | def | – | – | no | mild (uses (log ε)², not \|log ε\|) |
| A5 | `Vb` | def | – | – | no | – |
| A6 | `Cb` | def | – | – | no | – |
| A7 | `levelL` | def | – | – | no | – |
| A8 | `dot` | def | – | – | no | – |
| A9 | `box` | def | – | – | no | – |
| A10 | `ml2rWeight` | def | – | – | no | mild (α = 0 makes all weights 0) |
| A11 | `ml2rNode` | def | – | – | no | – |
| 1 | `lagrangeN_geometric` | thm | true | yes | no | – |
| 2 | `complexityBound_of_two_mul` | thm | true | yes | no | mild (pure exponent identity) |
| 3 | `cost_of_beta_eq_two_alpha` | thm | true | yes | no | mild |
| 4 | `mc_cost` | thm | true | yes | no | – |
| 5 | `mc_cost_lower` | thm | true | yes | no | mild (C is a free scalar) |
| 6 | `mc_complexity` | thm | true | yes | no | – |
| 7 | `mlmc_vs_mc_increasing` | thm | true | yes | no | **concern**: V_P cancels |
| 8 | `mlmc_vs_mc_decreasing` | thm | true | yes | no | **concern**: V_P and C_L cancel |
| 9 | `coarsest_level_dominant` | thm | true | yes | no | – |
| 10 | `finest_cost_le` | thm | true | yes | no | – |
| 11 | `equal_cost_per_level` | thm | true | yes | no | – |
| 12 | `split_cost` | thm | true | yes | no | – |
| 13 | `equal_split_cost_le` | thm | true | yes | no | **concern**: θ cancels; only monotonicity of partial sums |
| 14 | `summable_sqrt_Vb_mul_Cb` | thm | true | yes | no | – |
| 15 | `tendsto_equal_split_cost` | thm | true | yes | no | – |
| 16 | `tendsto_split_cost` | thm | true | yes | no | – |
| 17 | `randomised_half_cost` | thm | true | yes | no | mild (conjunct (b) repeats #15) |
| 18 | `rectSet` | def | – | – | no | – |
| 19 | `sum_rectSet_crossDiff` | thm | true | yes | no | – |
| 20 | `sum_filter_box_lt_le` | lemma | true | yes | no | – |
| 21 | `sum_sdiff_rectSet_le` | thm | true | yes | no | – |
| 22 | `mimc_rect_core` | thm | true | yes | no | – |
| 23 | `giles_mimc_rectangular` | thm | true | yes | no | **concern**: weak cost model, strong independence |
| 24 | `mimc_rect_lower_bounds` | thm | true | yes | no | **concern**: strong uniform bias lower bound |
| 25 | `mimc_rect_necessary` | thm | true | yes | no | **concern**: same as #24 |
| 26 | `abs_ml2rWeight_le` | thm | true | yes | no | – |
| 27 | `ml2rWeightBound` | def | – | – | no | mild (junk value 0 at α = 0) |
| 28 | `sum_abs_ml2rWeight_le` | thm | true | yes | no | – |
| 29 | `abs_ml2r_coeff_le` | thm | true | yes | no | – |
| 30 | `ml2rLevel` | def | – | – | no | – |
| 31 | `ml2rLevel_bias` | thm | true | yes | no | – |
| 32 | `ml2rLevel_lt_sqrt_levelL` | thm | true | yes | no | mild (no sign hypotheses on c₁, ε) |
| 33 | `ml2r_mse_cost` | thm | true | yes | no | – |
| 34 | `ml2r_complexity_eq` | thm | true | yes | no | – |
| 35 | `ml2r_complexity_lt` | thm | true | yes | no | – |
| 36 | `crossDiff` | def | – | – | no | – |
| 37 | `crossDiff_two` | thm | true | yes | no | – |
| 38 | `singleTerm` | def | – | – | no | mild (p = 0 gives 0) |
| 39 | `singleTermN` | def | – | – | no | mild (N = 0 gives 0) |
| 40 | `geomLevelProb` | def | – | – | no | mild (not a probability vector if β + γ ≤ 0) |
| 41 | `optimalLevelProb` | def | – | – | no | mild (0 if the series is not summable) |
| 42 | `randomised_optimal_cost` | thm | true | yes | no | mild (ε unconstrained) |
| 43 | `subsetCorr` | def | – | – | no | – |
| 44 | `subsetCost` | def | – | – | no | – |
| 45 | `subsetCost_eq` | thm | true | yes | no | – |
| 46 | `sum_subsetCorr` | thm | true | yes | no | – |
| 47 | `subset_optimal_cost` | thm | true | yes | no | mild (`hs` not needed; N real-valued) |
| 48 | `card_levelSubsets` | thm | true | yes | no | – |
| 49 | `exists_optimal_subset` | thm | true | yes | no | **concern**: content-free finite minimum |

No statement is false, none has contradictory hypotheses, and none depends on a junk value in a way that changes its meaning.

---

## Conventions confirmed in the sources

Paths are relative to `/home/user/mlmc-lean/.lake/packages/mathlib/Mathlib` unless marked *core*, which means `/root/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`.

1. **Square root.** `Real.sqrt x := NNReal.sqrt (Real.toNNReal x)` (`Analysis/Real/Sqrt.lean:112`). So $\sqrt{x}=0$ for $x\le 0$ (`Real.sqrt_eq_zero_of_nonpos`, l.142), and $\sqrt{x}\ge 0$ always.
2. **Division and inverse by zero.** `inv_zero : (0)⁻¹ = 0` (`Algebra/GroupWithZero/Defs.lean:236`) and `div_zero : a / 0 = 0` (`Algebra/GroupWithZero/Basic.lean:407`).
3. **Real power `rpow`.**
   - Definition: `x ^ y := ((x:ℂ)^(y:ℂ)).re` (`Analysis/SpecialFunctions/Pow/Real.lean:35`).
   - For $x\ge0$ (`rpow_def_of_nonneg`, l.45): $x^y=$ if $x=0$ then ($1$ if $y=0$, else $0$), else $\exp(y\log x)$.
   - For $x<0$ (`rpow_def_of_neg`, l.95): $x^y=\exp(y\log x)\cos(y\pi)$.
   - `rpow_natCast` (l.62): $x^{(n:\mathbb R)}=x^n$.
4. **How `^` elaborates.**
   - `x ^ y` becomes `rightact% HPow.hPow x y` (*core* `Init/Notation.lean:311`). The base joins the surrounding arithmetic tree; the exponent does not.
   - A numeral exponent defaults to `ℕ` via the `@[default_instance high]` instance `NPow.toPow` (`Algebra/Group/Defs.lean:654`). So `ε ^ 2` is the natural square.
   - `(2:ℝ) ^ t` with `t : ℝ` is `rpow`. `((2:ℝ) ^ t) ^ ℓ` with `ℓ : ℕ` is an `rpow` followed by a natural power.
5. **Logarithms.**
   - `Real.log x := if x = 0 then 0 else (exp-inverse of |x|)`, so $\log 0=0$ and $\log x=\log|x|$ (`Analysis/SpecialFunctions/Log/Basic.lean:44`).
   - `Real.logb b x := log x / log b` (`Log/Base.lean:43`). So $\log_2 0=0$ and $\log_2 x=\log_2|x|$.
6. **Natural ceiling.** `⌈a⌉₊ = 0 ↔ a ≤ 0` (`Algebra/Order/Floor/Semiring.lean:187`). Also `a ≤ ⌈a⌉₊` (l.178), and `⌈a⌉₊ < a + 1` for `a ≥ 0` (l.357).
7. **Infinite sums.**
   - `HasSum f a` is the limit of finite partial sums along the filter of finite sets, i.e. unconditional summation (`Topology/Algebra/InfiniteSum/Defs.lean:106`).
   - `∑' i, f i` is $0$ when `f` is not summable (`tprod`, l.142, additivised).
   - Partial sums over `range n` of a summable $f:\mathbb N\to\mathbb R$ converge to the tsum (`HasProd.tendsto_prod_nat`, additivised, `InfiniteSum/NatInt.lean:48`).
8. **Bochner integral.**
   - `integral_undef`: a non-integrable function has integral $0$ (`MeasureTheory/Integral/Bochner/Basic.lean:202`).
   - The notation `μ[X]` is `∫ x, X x ∂μ` (`Probability/Notation.lean:53`).
9. **Variance.**
   - `evariance X μ := ∫⁻ ‖X − μ[X]‖ₑ² dμ` and `variance X μ := (evariance X μ).toReal` (`Probability/Moments/Variance.lean:58,64`).
   - Hence variance is $0$ for an a.e.-strongly-measurable $X\notin L^2$ (`variance_of_not_memLp`, l.132).
   - Variance equals $\int (X-\mathbb E X)^2$ for a.e.-measurable $X$ (l.155).
10. **`MemLp f p μ`** means `f` is a.e. strongly measurable and `eLpNorm f p μ < ∞` (`MeasureTheory/Function/LpSeminorm/Defs.lean:118`).
11. **Independence.** `IndepFun f g μ` and `iIndepFun f μ` mean independence of the σ-algebras $f^{-1}(\cdot)$, defined through `Kernel.const Unit μ` (`Probability/Independence/Basic.lean:136,144`). Measurability of the functions is not required.
12. **`MeasurePreserving f μa μb`** means `f` is measurable and `map f μa = μb` (`Dynamics/Ergodic/MeasurePreserving.lean:45`).
13. **`IsLeast S a`** means $a\in S$ and $a$ is a lower bound of $S$ (`Order/Bounds/Defs.lean:45`).
14. **`Pairwise r`** means $\forall i\ne j,\ r\,i\,j$ (`Logic/Pairwise.lean:34`).
15. **`Fintype.piFinset t`** is the finite set of functions $f$ with $f(a)\in t(a)$ for all $a$ (`Data/Fintype/Pi.lean:32`). Over an empty index type it is the singleton containing the empty tuple.
16. **Tuples.**
   - `Fin.cons x p` is the tuple $(x,p_0,p_1,\dots)$, and `Fin.tail q` is $(q_1,q_2,\dots)$ (`Data/Fin/Tuple/Basic.lean:106,113`).
   - `Fin.succ ⟨i,_⟩ = ⟨i+1,_⟩` and `Fin.castSucc` keeps the value (*core* `Init/Data/Fin/Basic.lean:43,337`).
17. **`Finset.max' s H`** is `s.sup' H id`, the maximum of a nonempty finite set (`Data/Finset/Max.lean:186`).
18. **Finite sets of naturals.** `range n = {0,…,n−1}` (`Data/Finset/Range.lean:64`) and `Ico a b = {x : a ≤ x < b}` (`Order/Interval/Finset/Defs.lean:305`).
19. **Big-operator precedence.**
   - `∑ x ∈ s, body` parses `body` at precedence 67 (`Algebra/BigOperators/Group/Finset/Defs.lean`, syntax `bigsum` and the library note). Hence `∑ ℓ ∈ s, a ℓ - b` means $(\sum_\ell a_\ell)-b$, while `∑ ℓ ∈ s, a ℓ * b ℓ` and `∑ ℓ ∈ s, a ℓ / b ℓ` sum the whole product or quotient.
   - `∑'` has the same body precedence (`r:67`).
   - Other operators (*core* `Init/Notation.lean`): prefix `-` is at 75, infix `+`/`-` at 65, `*`/`/` at 70, `^` is right-associative at 75, `⁻¹` is postfix at max. So `ε⁻¹ ^ 2 = (ε⁻¹)^2`, `-dot α ℓ = −(dot α ℓ)`, and `max 1 (c₁/δ) ^ (γ/α) = (max 1 (c₁/δ))^{γ/α}`.
20. **Natural subtraction truncates:** `n − m = 0` if `n ≤ m` (*core* `Init/Data/Nat/Basic.lean:1057`).

## Notation used below

- $\sqrt{\cdot}$ is the real square root, extended by $0$ on negative arguments.
- $\lceil x\rceil_{\mathbb N}$ is the natural ceiling: $0$ if $x\le0$, else the least natural number $\ge x$.
- $\log$ is the natural logarithm with the conventions above, and $\log_2 x:=\log x/\log 2$.
- Powers with a real exponent (of $2$, of $\varepsilon$, of $q$) are real powers. Powers with a natural-number exponent (such as $\ell$, $L-\ell$, $2$) are iterated products.
- $\sum'$ is Mathlib's infinite sum.
- $\{0..L\}:=\{0,1,\dots,L\}$.
- Multi-indices are $\ell\in\mathbb N^D$, i.e. functions from $\{0,\dots,D-1\}$ to $\mathbb N$.
- $\mathbb E[X]:=\int X\,d\mu$ is the Bochner integral, and $\operatorname{Var}(X)$ is Mathlib's variance.
- Project definitions are written as follows (full expansions in Part A):
  - $\mathrm S_s(V,C)$ for `sumSqrtVC`
  - $N^{s}_\tau(i)$ for `lagrangeN`
  - $V^{\mathrm b}_{\beta,c_2}(\ell)=c_2 2^{-\beta\ell}$ for `Vb`
  - $C^{\mathrm b}_{\gamma,c_3}(\ell)=c_3 2^{\gamma\ell}$ for `Cb`
  - $\Lambda(\alpha,c_1,\delta)$ for `levelL`
  - $\langle a,\ell\rangle$ for `dot`
  - $\mathrm{Rect}(L)$ for `rectSet`
  - $\boldsymbol\Delta p(\ell)$ for `crossDiff`
  - $w^{(L)}_\ell$ for `ml2rWeight`
  - $B(\alpha)$ for `ml2rWeightBound`
  - $R(\alpha,c_1,\varepsilon)$ for `ml2rLevel`

---

## Part A. Supporting definitions (trailing section)

### A1. `sumSqrtVC` (definition)

**Rendering.** Let $\iota$ be any type, $s$ a finite subset of $\iota$, and $V,C:\iota\to\mathbb R$. Then
$$\mathrm S_s(V,C):=\sum_{i\in s}\sqrt{V_i\,C_i}.$$

- **Truth:** not applicable (definition).
- **Non-vacuity:** not applicable.
- **Junk values:** a term with $V_iC_i<0$ contributes $\sqrt{\text{negative}}=0$, so $\mathrm S_s(V,C)\ge 0$ always.
- **Concerns:** none.

### A2. `lagrangeN` (definition)

**Rendering.** Let $\iota$, $s$, $V$, $C$ be as in A1, $\tau\in\mathbb R$ and $i\in\iota$. Then
$$N^{s}_{\tau}(i):=\tau^{-1}\,\sqrt{V_i/C_i}\;\mathrm S_s(V,C)=\tau^{-1}\sqrt{V_i/C_i}\sum_{j\in s}\sqrt{V_jC_j}.$$
The index $i$ need not belong to $s$. The value is a real number and is not rounded.

- **Truth:** not applicable.
- **Junk values:**
  - $\tau=0$ gives $\tau^{-1}=0$, so the value is $0$.
  - $C_i=0$ gives $V_i/C_i=0$, so the value is $0$.
  - $V_i/C_i<0$ gives $\sqrt{\cdot}=0$.
  - $\tau<0$ gives a value $\le 0$.
- **Concerns:** only these conventions. In the theorems below the definition is always used with explicit positivity hypotheses, except where noted.

### A3. `levelDiff` (definition)

**Rendering.** Let $\Omega_0$ be a type and $P:\mathbb N\to(\Omega_0\to\mathbb R)$, written $\ell\mapsto P_\ell$. Then $\Delta P:\mathbb N\to(\Omega_0\to\mathbb R)$ is given by
$$\Delta P_0=P_0,\qquad \Delta P_{\ell+1}(y)=P_{\ell+1}(y)-P_\ell(y).$$

- **Truth / non-vacuity:** not applicable.
- **Junk values:** none.
- **Concerns:** none.

### A4. `complexityBound` (definition)

**Rendering.** For real $\alpha,\beta,\gamma,\varepsilon$:
$$\mathcal B(\alpha,\beta,\gamma,\varepsilon)=\begin{cases}\varepsilon^{-2}&\text{if }\gamma<\beta,\\ \varepsilon^{-2}\,(\log\varepsilon)^2&\text{if }\beta=\gamma,\\ \varepsilon^{-2-(\gamma-\beta)/\alpha}&\text{otherwise (}\gamma>\beta\text{)},\end{cases}$$
All exponents are real.

- **Junk values:**
  - For $\varepsilon=0$: $0^{y}=0$ for $y\ne0$, and $\log 0=0$.
  - For $\varepsilon<0$: $\varepsilon^{y}=\exp(y\log|\varepsilon|)\cos(\pi y)$, and $\log\varepsilon=\log|\varepsilon|$.
  - For $\alpha=0$ in the third case: $(\gamma-\beta)/0=0$, so the value is $\varepsilon^{-2}$.
- **Concerns:** the middle case uses $(\log\varepsilon)^2$, the square of the logarithm (not $|\log\varepsilon|$).

### A5. `Vb` (definition)

**Rendering.** For $\beta,c_2\in\mathbb R$ and $\ell\in\mathbb N$: $V^{\mathrm b}_{\beta,c_2}(\ell)=c_2\cdot 2^{-\beta\ell}$, with a real exponent and $\ell$ cast to $\mathbb R$.

- **Junk values:** none.
- **Concerns:** none.

### A6. `Cb` (definition)

**Rendering.** For $\gamma,c_3\in\mathbb R$ and $\ell\in\mathbb N$: $C^{\mathrm b}_{\gamma,c_3}(\ell)=c_3\cdot 2^{\gamma\ell}$, with a real exponent.

- **Junk values:** none.
- **Concerns:** none.

### A7. `levelL` (definition)

**Rendering.** For real $\alpha,c_1,\delta$:
$$\Lambda(\alpha,c_1,\delta)=\Big\lceil \log_2(c_1/\delta)/\alpha\Big\rceil_{\mathbb N}\in\mathbb N.$$

- **Junk values:**
  - The value is $0$ whenever $\log_2(c_1/\delta)/\alpha\le0$.
  - $\delta=0$ gives $c_1/0=0$, $\log 0=0$, and value $0$.
  - $\alpha=0$ gives division by $0$ and value $0$.
  - $c_1/\delta<0$ uses $\log_2|c_1/\delta|$.
- **Concerns:** none. The theorems below use it only with $\alpha>0$, $c_1>0$ and $\delta>0$, except #32, which holds for all $c_1,\varepsilon$.

### A8. `dot` (definition)

**Rendering.** For $D\in\mathbb N$, $a\in\mathbb R^D$ and $\ell\in\mathbb N^D$: $\langle a,\ell\rangle=\sum_{d=0}^{D-1}a_d\,\ell_d$.

- **Junk values:** none. For $D=0$ the value is $0$.

### A9. `box` (definition)

**Rendering.** For $D,n\in\mathbb N$:
$$\mathrm{Box}_D(n)=\{\ell\in\mathbb N^D:\ \ell_d<n\ \forall d\}=\{0,\dots,n-1\}^D,$$
as a finite set.

- **Junk values:** for $D=0$ this is the singleton $\{()\}$ for every $n$, including $n=0$.
- **Concerns:** none relevant, since #20 uses it only with $D\ge1$.

### A10. `ml2rWeight` (definition)

**Rendering.** For $\alpha\in\mathbb R$ and $L,\ell\in\mathbb N$, with nodes $\nu_k=2^{-\alpha k}$:
$$w^{(L)}_\ell(\alpha)=\prod_{k\in\{0..L\}\setminus\{\ell\}}\frac{\nu_k}{\nu_k-\nu_\ell}.$$
If $\ell>L$, the product runs over all $k\in\{0..L\}$.

- **Junk values:** if $\alpha=0$, every node equals $1$ and every factor is $1/0=0$. So $w^{(L)}_\ell(0)=0$ whenever the product is nonempty (for example all $\ell\le L$ when $L\ge1$); for $L=0,\ell=0$ the empty product is $1$. For $\alpha\ne0$ the nodes are distinct and no junk occurs.
- **Checked fact:** for $\alpha\ne0$ and $\ell\le L$, $\sum_{\ell=0}^{L}w^{(L)}_\ell\nu_\ell^{\,j}=1$ for $j=0$ and $=0$ for $1\le j\le L$. This was checked numerically in `check_ml2r.py`.
- **Concerns:** the $\alpha=0$ degeneracy only (not used by any theorem).

### A11. `ml2rNode` (definition)

**Rendering.** $\nu_\alpha(\ell)=2^{-\alpha\ell}$ for $\alpha\in\mathbb R$ and $\ell\in\mathbb N$, with a real exponent.

- **Junk values:** none.

---

## Part B. Module `MlmcLean.GeometricRates`

### 1. `lagrangeN_geometric` (theorem)

**Rendering.** Take real numbers $\beta,\gamma,c_2,c_3$ with $c_2>0$ and $c_3>0$, any finite set $s\subseteq\mathbb N$, any real $\tau$, and any $\ell\in\mathbb N$. Write $V=V^{\mathrm b}_{\beta,c_2}$ and $C=C^{\mathrm b}_{\gamma,c_3}$, $\mathrm S=\mathrm S_s(V,C)=\sum_{k\in s}\sqrt{c_22^{-\beta k}\,c_32^{\gamma k}}$, and
$$N_\tau(\ell)=\tau^{-1}\sqrt{\frac{c_2 2^{-\beta\ell}}{c_3 2^{\gamma\ell}}}\;\mathrm S$$
(here $\ell$ need not lie in $s$). Then both of the following hold:
$$\text{(a)}\quad N_\tau(\ell)=\tau^{-1}\,\mathrm S\,\sqrt{c_2/c_3}\,\big(2^{-(\beta+\gamma)/2}\big)^{\ell},$$
$$\text{(b)}\quad N_\tau(\ell)\cdot c_32^{\gamma\ell}=\tau^{-1}\,\mathrm S\,\sqrt{c_2c_3}\,\big(2^{(\gamma-\beta)/2}\big)^{\ell}.$$

- **Truth: true.**
  - Since $c_2,c_3>0$: $\sqrt{V_\ell/C_\ell}=\sqrt{c_2/c_3}\,2^{-(\beta+\gamma)\ell/2}$. This gives (a).
  - Multiplying by $c_32^{\gamma\ell}$ and using $\sqrt{c_2/c_3}\,c_3=\sqrt{c_2c_3}$ gives (b).
  - Checked numerically, including $\tau=0$ and $\tau<0$.
- **Non-vacuity:** $c_2=c_3=1$ with any $\beta,\gamma,s,\tau,\ell$.
- **Junk values:** $\tau$ is unconstrained. At $\tau=0$ both sides are $0$ via $0^{-1}=0$; for $\tau<0$ both sides are negative. The identity holds in all cases, so the meaning is unaffected.
- **Concerns:** none. $\mathrm S$ is left unexpanded on the right-hand side.

### 2. `complexityBound_of_two_mul` (theorem)

**Rendering.** Take real $\alpha,\beta,\gamma$ with $\alpha>0$, $\beta=2\alpha$ and $\beta<\gamma$, and any real $\varepsilon$. Then $\mathcal B(\alpha,\beta,\gamma,\varepsilon)=\varepsilon^{-\gamma/\alpha}$ (real power). Because $\beta<\gamma$, the definition gives $\mathcal B=\varepsilon^{-2-(\gamma-\beta)/\alpha}$, so the claim is
$$\varepsilon^{-2-(\gamma-2\alpha)/\alpha}=\varepsilon^{-\gamma/\alpha}.$$

- **Truth: true.** The exponents are equal real numbers, since $-2-(\gamma-2\alpha)/\alpha=-\gamma/\alpha$ when $\alpha\ne0$.
- **Non-vacuity:** $\alpha=1,\beta=2,\gamma=3$.
- **Junk values:** $\varepsilon\le0$ is allowed. Both sides are the same real-power expression with identical exponents, so junk conventions apply identically to both. The statement is meaningful for $\varepsilon>0$.
- **Concerns:** it is a pure exponent identity for the third branch of $\mathcal B$.

### 3. `cost_of_beta_eq_two_alpha` (theorem)

**Rendering.** Take real $\alpha,\gamma,c_2,c_3,K,\varepsilon$ with $2\alpha<\gamma$, $c_2>0$, $c_3>0$ and $\varepsilon>0$. Take $L\in\mathbb N$ with
$$2^{-\alpha L}\le K\varepsilon.$$
Define:
- $V_\ell=c_22^{-2\alpha\ell}$ and $C_\ell=c_32^{\gamma\ell}$;
- $\tau=\varepsilon^2/2$;
- $N_\ell=\tau^{-1}\sqrt{V_\ell/C_\ell}\sum_{k=0}^{L}\sqrt{V_kC_k}$ for $\ell\in\mathbb N$ (real numbers);
- $\rho=2^{(\gamma-2\alpha)/2}$.

Then both of the following hold:
$$\text{(a)}\quad N_L\le 2c_2K^2\cdot\frac{\rho}{\rho-1},\qquad \text{(b)}\quad \sum_{\ell=0}^{L}N_\ell C_\ell\le 2c_2K^2\Big(\frac{\rho}{\rho-1}\Big)^2\,c_32^{\gamma L}.$$

- **Truth: true.**
  - Compute $N_L=\tfrac{2}{\varepsilon^2}c_2\,2^{-(2\alpha+\gamma)L/2}\sum_{k=0}^{L}\rho^k$.
  - Since $\rho>1$: $\sum_{k\le L}\rho^k\le\rho^L\rho/(\rho-1)$.
  - Also $2^{-(2\alpha+\gamma)L/2}\rho^L=2^{-2\alpha L}=(2^{-\alpha L})^2\le K^2\varepsilon^2$. This gives (a).
  - For (b): $\sum N_\ell C_\ell=\tau^{-1}\big(\sum_k\sqrt{V_kC_k}\big)^2=\tfrac2{\varepsilon^2}c_2c_3(\sum\rho^k)^2\le \tfrac2{\varepsilon^2}c_2c_3\rho^{2L}(\rho/(\rho-1))^2$, and $\rho^{2L}c_3=2^{-2\alpha L}c_32^{\gamma L}$.
  - Random tests show both bounds are nearly tight (ratio up to $0.99993$) and never violated.
- **Non-vacuity:** $\alpha=1,\gamma=3,c_2=c_3=\varepsilon=K=1,L=0$.
- **Junk values:** none ($\tau>0$ and $\rho>1$).
- **Concerns:**
  - $\alpha$ has no sign condition. If $\alpha\le0$, the hypothesis forces $K\varepsilon\ge1$.
  - $K$ is not assumed positive but is forced positive by the hypothesis.
  - The $N_\ell$ are unrounded reals.
  - The conclusion contains no statement about $\sum V_\ell/N_\ell$.

---

## Part C. Module `MlmcLean.CostComparison`

### 4. `mc_cost` (theorem)

**Rendering.** Take real $V,C,\varepsilon$ with $V\ge0$, $C\ge0$ and $\varepsilon>0$. Put $x=(\varepsilon^{-1})^2V$ and $M=\max(1,\lceil x\rceil_{\mathbb N})\in\mathbb N$. Then all four hold:
- (a) every $N\in\mathbb N$ with $N>0$ and $V/N\le\varepsilon^2$ satisfies $x\,C\le N\,C$;
- (b) $M>0$ (as a natural number);
- (c) $V/M\le\varepsilon^2$;
- (d) $M\,C\le x\,C+C$.

- **Truth: true.**
  - (a): $V\le N\varepsilon^2$, so $x\le N$; multiply by $C\ge0$.
  - (b) is immediate from $M\ge1$.
  - (c): $M\ge x$, so $V/M\le V/x=\varepsilon^2$ when $V>0$; when $V=0$ it is trivial.
  - (d): $M\le x+1$, because either $M=\lceil x\rceil<x+1$ or $M=1\le x+1$.
  - Checked numerically.
- **Non-vacuity:** $V=C=\varepsilon=1$.
- **Junk values:** none ($N\ge1$ and $M\ge1$).
- **Concerns:** a purely arithmetic statement; $V$ and $C$ are arbitrary numbers.

### 5. `mc_cost_lower` (theorem)

**Rendering.** Let $\Omega_0$ and $\Omega$ be types carrying σ-algebras. Let $\nu$ be a measure on $\Omega_0$ and $\mu$ a probability measure on $\Omega$. Let $\omega=(\omega_n)_{n\in\mathbb N}$ be maps $\Omega\to\Omega_0$ such that:
- each $\omega_n$ is measurable, with pushforward $\omega_n{}_\#\mu=\nu$;
- the family $(\omega_n)_{n\in\mathbb N}$ is mutually independent under $\mu$.

Let $P:\Omega_0\to\mathbb R$ be measurable with $P\in L^2(\nu)$. Let $N\in\mathbb N$ with $N>0$, and real $\varepsilon>0$, $C\ge0$. Assume
$$\sqrt{\int_\Omega\Big(\frac1N\sum_{n=0}^{N-1}P(\omega_n(x))-\int_{\Omega_0}P\,d\nu\Big)^2 d\mu(x)}\ \le\ \varepsilon .$$
Then
$$(\varepsilon^{-1})^2\cdot\operatorname{Var}_\nu(P)\cdot C\le N\cdot C,$$
where $\operatorname{Var}_\nu(P)$ is Mathlib's variance of $P$ under $\nu$ (finite here, since $P\in L^2(\nu)$).

- **Truth: true.**
  - $\nu$ is a probability measure, being the pushforward of $\mu$.
  - The $P\circ\omega_n$ are i.i.d. with the law of $P$ under $\nu$ and lie in $L^2$.
  - So the integral equals $\operatorname{Var}_\nu(P)/N$, and the hypothesis gives $\operatorname{Var}_\nu(P)\le N\varepsilon^2$. Multiply by $C\varepsilon^{-2}\ge0$.
  - A Monte Carlo check of the identity $\mathbb E[(\bar P_N-\mathbb E P)^2]=\operatorname{Var}(P)/N$ agrees (`check_mc_montecarlo.py`).
- **Non-vacuity:**
  - Trivial witness: one-point spaces and $P=0$. Then all hypotheses hold, since constant maps are independent and $\sqrt0\le\varepsilon$.
  - Non-trivial witness: $\Omega=\{0,1\}^{\mathbb N}$ with fair-coin product measure, $\omega_n$ the coordinates, $P=\mathrm{id}$, $N=1$, $\varepsilon=1/2$.
- **Junk values:** none are active. The integrand is integrable, the variance is the true variance, and $\nu$'s total mass $1$ follows from the pushforward.
- **Concerns:**
  - $C$ is a free nonnegative scalar. For $C>0$ the conclusion is equivalent to $\operatorname{Var}_\nu(P)\le N\varepsilon^2$; for $C=0$ it is trivial.
  - $\nu$ being a probability measure is implied, not assumed.

### 6. `mc_complexity` (theorem)

**Rendering.** Take real $\alpha,\gamma,c_1,c_3,\bar V$ with $\alpha>0$, $\gamma>0$, $c_1>0$, $c_3>0$ and $\bar V\ge0$. Then there is $c_4>0$ such that for every $\varepsilon$ with $0<\varepsilon<1$ there exist $L,N\in\mathbb N$ with $N>0$ and
$$\big(c_12^{-\alpha L}\big)^2+\bar V/N\le\varepsilon^2,\qquad N\cdot\big(c_32^{\gamma L}\big)\le c_4\,\varepsilon^{-2-\gamma/\alpha}.$$
Here $c_4$ is chosen before $\varepsilon$.

- **Truth: true.**
  - Take $L=\lceil\log_2(\sqrt2c_1/\varepsilon)/\alpha\rceil_{\mathbb N}$ and $N=\max(1,\lceil2\bar V/\varepsilon^2\rceil)$.
  - Then $N\le(2\bar V+1)\varepsilon^{-2}$ and $2^{\gamma L}\le2^\gamma\max(1,(\sqrt2c_1)^{\gamma/\alpha})\varepsilon^{-\gamma/\alpha}$ for $\varepsilon<1$.
  - The numerical ratio stays bounded as $\varepsilon\to0$.
- **Non-vacuity:** all parameters equal to $1$ and $\bar V=0$.
- **Junk values:** none ($\varepsilon\in(0,1)$).
- **Concerns:** a deterministic statement; $\bar V$ does not depend on $L$.

### 7. `mlmc_vs_mc_increasing` (theorem)

**Rendering.** Let $V,C:\mathbb N\to\mathbb R$ and real $r,\tau,V_P$ satisfy:
- $r>1$, $\tau>0$ and $V_P>0$;
- $V_\ell\ge0$ and $C_\ell\ge0$ for all $\ell$;
- $r\sqrt{V_\ell C_\ell}\le\sqrt{V_{\ell+1}C_{\ell+1}}$ for all $\ell$.

Let $L\in\mathbb N$ and $A_L=\sum_{\ell=0}^{L}\sqrt{V_\ell C_\ell}$. Then
$$\frac{V_L}{V_P}\big(\tau^{-1}V_PC_L\big)\ \le\ \tau^{-1}A_L^2\ \le\ \Big(\frac{r}{r-1}\Big)^2\frac{V_L}{V_P}\big(\tau^{-1}V_PC_L\big).$$

- **Truth: true.**
  - The outer expressions equal $\tau^{-1}V_LC_L$ and $(r/(r-1))^2\tau^{-1}V_LC_L$.
  - Lower bound: keep only the $\ell=L$ term of $A_L$.
  - Upper bound: $\sqrt{V_\ell C_\ell}\le r^{-(L-\ell)}\sqrt{V_LC_L}$, so $A_L\le\sqrt{V_LC_L}\,r/(r-1)$.
  - Checked numerically.
- **Non-vacuity:** $V\equiv1$, $C_\ell=4^\ell$, $r=2$, $\tau=V_P=1$.
- **Junk values:** none.
- **Concerns:**
  - $V_P$ cancels identically, so the statement is equivalent to $V_LC_L\le A_L^2\le(r/(r-1))^2V_LC_L$ (times $\tau^{-1}$). $V_P$ plays no role beyond $V_P\ne0$.
  - The degenerate case $V_\ell C_\ell\equiv0$ is allowed.

### 8. `mlmc_vs_mc_decreasing` (theorem)

**Rendering.** Let $V,C:\mathbb N\to\mathbb R$ and real $r,\tau,V_P$ satisfy:
- $0\le r<1$, $\tau>0$ and $V_P>0$;
- $V_\ell\ge0$ and $C_\ell\ge0$ for all $\ell$;
- $\sqrt{V_{\ell+1}C_{\ell+1}}\le r\sqrt{V_\ell C_\ell}$ for all $\ell$.

Let $L\in\mathbb N$ with $C_L>0$, and $A_L=\sum_{\ell=0}^{L}\sqrt{V_\ell C_\ell}$. Then
$$\frac{V_0}{V_P}\frac{C_0}{C_L}\big(\tau^{-1}V_PC_L\big)\le\tau^{-1}A_L^2\le(1-r)^{-2}\,\frac{V_0}{V_P}\frac{C_0}{C_L}\big(\tau^{-1}V_PC_L\big).$$

- **Truth: true.**
  - The outer expressions equal $\tau^{-1}V_0C_0$ and $(1-r)^{-2}\tau^{-1}V_0C_0$.
  - $\sqrt{V_\ell C_\ell}\le r^\ell\sqrt{V_0C_0}$, so $A_L\le\sqrt{V_0C_0}/(1-r)$.
  - Checked numerically.
- **Non-vacuity:** $V_\ell=4^{-\ell}$, $C\equiv1$, $r=1/2$.
- **Junk values:** none ($C_L>0$ and $V_P>0$).
- **Concerns:** $V_P$ and $C_L$ cancel. The statement is equivalent to $V_0C_0\le A_L^2\le(1-r)^{-2}V_0C_0$ (times $\tau^{-1}$).

### 9. `coarsest_level_dominant` (theorem)

**Rendering.** Let $V,C:\mathbb N\to\mathbb R$ with $V_\ell>0$ and $C_\ell>0$ for all $\ell$, such that $\ell\mapsto\sqrt{V_\ell C_\ell}$ is summable. Let $\tau>0$ and $L\in\mathbb N$. Write:
- $S_L=\sum_{k=0}^{L}\sqrt{V_kC_k}$;
- $S_\infty=\sum'_{k}\sqrt{V_kC_k}$;
- $N_\ell=\tau^{-1}\sqrt{V_\ell/C_\ell}\,S_L$.

Then:
- (a) $\tau^{-1}V_0\le N_0$;
- (b) $N_0\le\tau^{-1}\sqrt{V_0/C_0}\,S_\infty$;
- (c) $\dfrac{\sqrt{V_0C_0}}{S_\infty}\cdot\sum_{\ell=0}^{L}N_\ell C_\ell\le N_0C_0$.

- **Truth: true.**
  - (a): $S_L\ge\sqrt{V_0C_0}$.
  - (b): $S_L\le S_\infty$, since the terms are nonnegative and summable.
  - (c): $\sum N_\ell C_\ell=\tau^{-1}S_L^2$ and $N_0C_0=\tau^{-1}\sqrt{V_0C_0}\,S_L$, so the claim reduces to $S_L\le S_\infty$.
  - Checked numerically.
- **Non-vacuity:** $V_\ell=4^{-\ell}$, $C\equiv1$.
- **Junk values:** none ($S_\infty>0$ is a genuine sum).
- **Concerns:** none.

### 10. `finest_cost_le` (theorem)

**Rendering.** Take real $\alpha,\gamma,c_1,c_3,\delta$ with $\alpha>0$, $\gamma\ge0$, $c_1>0$, $c_3\ge0$ and $\delta>0$. With $\Lambda=\lceil\log_2(c_1/\delta)/\alpha\rceil_{\mathbb N}$:
$$c_3\,2^{\gamma\Lambda}\le c_3\Big(2^{\gamma}\,\big(\max(1,c_1/\delta)\big)^{\gamma/\alpha}\Big).$$

- **Truth: true.**
  - If $c_1\le\delta$, then $\Lambda=0$ and the claim is $c_3\le c_32^\gamma$.
  - Otherwise $\Lambda<\log_2(c_1/\delta)/\alpha+1$, so $2^{\gamma\Lambda}\le2^\gamma(c_1/\delta)^{\gamma/\alpha}$.
  - Checked numerically.
- **Non-vacuity:** trivial (all parameters equal to 1).
- **Junk values:** the case $\log_2(c_1/\delta)\le0$ uses $\lceil\cdot\rceil_{\mathbb N}=0$, which is the intended floor at $0$ and is matched by the $\max(1,\cdot)$.
- **Concerns:** none ($c_3=0$ is trivial).

### 11. `equal_cost_per_level` (theorem)

**Rendering.** Let $V,C:\mathbb N\to\mathbb R$ with $V_\ell>0$ and $C_\ell>0$ for all $\ell$. Let $\tau,s\in\mathbb R$ with $\tau>0$, and $L\in\mathbb N$ with $\sqrt{V_\ell C_\ell}=s$ for all $\ell\le L$. Let $N_\ell=\tau^{-1}\sqrt{V_\ell/C_\ell}\sum_{k=0}^{L}\sqrt{V_kC_k}$. Then:
- (a) for all $\ell\le L$, $V_\ell/N_\ell=\tau/(L+1)$;
- (b) for all $\ell\le L$, $N_\ell C_\ell=\tau^{-1}(L+1)s^2$;
- (c) $\sum_{\ell=0}^{L}N_\ell C_\ell=\tau^{-1}(L+1)^2s^2$.

- **Truth: true.** The sum is $(L+1)s$ and $\sqrt{V_\ell/C_\ell}\,s=V_\ell$. Checked numerically.
- **Non-vacuity:** $V=C\equiv1$, $s=1$.
- **Junk values:** none.
- **Concerns:** none ($s>0$ is forced).

### 12. `split_cost` (theorem)

**Rendering.** Let $V_\ell>0$ and $C_\ell>0$ for all $\ell$. Let $\theta,\varepsilon\in\mathbb R$ with $\theta<1$ and $\varepsilon>0$, and let $L\in\mathbb N$. With $\tau=(1-\theta)\varepsilon^2$, $S_L=\sum_{k=0}^{L}\sqrt{V_kC_k}$ and $N_\ell=\tau^{-1}\sqrt{V_\ell/C_\ell}\,S_L$:
$$\text{(a)}\ \sum_{\ell=0}^{L}V_\ell/N_\ell=(1-\theta)\varepsilon^2,\qquad\text{(b)}\ \sum_{\ell=0}^{L}N_\ell C_\ell=(1-\theta)^{-1}\big((\varepsilon^2)^{-1}S_L^2\big).$$

- **Truth: true.** $V_\ell/N_\ell=\tau\sqrt{V_\ell C_\ell}/S_L$ and $\sum N_\ell C_\ell=\tau^{-1}S_L^2$. Checked numerically, including $\theta<0$.
- **Non-vacuity:** trivial.
- **Junk values:** none.
- **Concerns:** $\theta$ may be negative, since only $\theta<1$ is assumed.

### 13. `equal_split_cost_le` (theorem)

**Rendering.** Let $V,C:\mathbb N\to\mathbb R$ be arbitrary (no hypotheses). Let $\theta,\varepsilon\in\mathbb R$ with $\theta<1$ and $\varepsilon>0$, and $L\le L'$ in $\mathbb N$. With $S_M=\sum_{\ell=0}^{M}\sqrt{V_\ell C_\ell}$:
$$(\varepsilon^2/2)^{-1}S_L^2\ \le\ 2(1-\theta)\Big(\big((1-\theta)\varepsilon^2\big)^{-1}S_{L'}^2\Big).$$

- **Truth: true.** The right side equals $2\varepsilon^{-2}S_{L'}^2$ and the left side $2\varepsilon^{-2}S_L^2$. Since every $\sqrt{\cdot}\ge0$, we have $0\le S_L\le S_{L'}$. Checked numerically with arbitrary-sign $V,C$.
- **Non-vacuity:** trivial.
- **Junk values:** when $V_\ell C_\ell<0$ the term is $\sqrt{\cdot}=0$. This convention is what makes the statement hold without sign hypotheses, and it does not change the meaning.
- **Concerns:** $\theta$ cancels exactly; its only role is $1-\theta\ne0$. After cancellation the statement is monotonicity of partial sums of nonnegative terms, which is weaker than its form suggests.

### 14. `summable_sqrt_Vb_mul_Cb` (theorem)

**Rendering.** Take real $\beta,\gamma,c_2,c_3$ with $c_2>0$, $c_3>0$ and $\gamma<\beta$. Then the sequence $\ell\mapsto\sqrt{c_22^{-\beta\ell}\cdot c_32^{\gamma\ell}}$ ($\ell\in\mathbb N$) is summable.

- **Truth: true.** The terms equal $\sqrt{c_2c_3}\,(2^{(\gamma-\beta)/2})^\ell$, a geometric sequence with ratio $<1$.
- **Non-vacuity:** $\beta=1,\gamma=0,c_2=c_3=1$.
- **Junk values:** none.
- **Concerns:** none.

### 15. `tendsto_equal_split_cost` (theorem)

**Rendering.** Let $V,C:\mathbb N\to\mathbb R$ be such that $\ell\mapsto\sqrt{V_\ell C_\ell}$ is summable, and let $\varepsilon>0$. With $S_L$ as above and $S_\infty=\sum'_\ell\sqrt{V_\ell C_\ell}$, as $L\to\infty$:
$$(\varepsilon^2/2)^{-1}S_L^2\ \longrightarrow\ 2\big((\varepsilon^2)^{-1}S_\infty^2\big).$$

- **Truth: true.** The partial sums $S_L$ (over $\{0..L\}$) converge to $S_\infty$, and $(\varepsilon^2/2)^{-1}=2/\varepsilon^2$.
- **Non-vacuity:** $V_\ell=4^{-\ell}$, $C\equiv1$.
- **Junk values:** none (summability is assumed; no sign hypotheses are needed).
- **Concerns:** none.

### 16. `tendsto_split_cost` (theorem)

**Rendering.** Assume summability as in #15 and $\varepsilon>0$. Let $\theta:\mathbb N\to\mathbb R$ with $\theta_k\to0$, and $L:\mathbb N\to\mathbb N$ with $L_k\to\infty$. Then, as $k\to\infty$,
$$\big((1-\theta_k)\varepsilon^2\big)^{-1}S_{L_k}^2\ \longrightarrow\ (\varepsilon^2)^{-1}S_\infty^2 .$$

- **Truth: true.** Inversion is continuous at $\varepsilon^2\ne0$, and $S_{L_k}\to S_\infty$.
- **Non-vacuity:** $\theta\equiv0$, $L=\mathrm{id}$.
- **Junk values:** $\theta_k\ge1$ is not excluded. The (finitely many) $k$ with $\theta_k=1$ give $0^{-1}=0$, which does not affect the limit.
- **Concerns:** none.

### 17. `randomised_half_cost` (theorem)

**Rendering.** Let $V,C:\mathbb N\to\mathbb R$ with $V_\ell>0$ and $C_\ell>0$ for all $\ell$, such that both $\ell\mapsto\sqrt{V_\ell C_\ell}$ and $\ell\mapsto\sqrt{V_\ell/C_\ell}$ are summable. Let $\varepsilon>0$ and $S_\infty=\sum'_\ell\sqrt{V_\ell C_\ell}$. Let $\mathcal X\subseteq\mathbb R$ be the set of $x$ for which there is $p:\mathbb N\to\mathbb R$ with all of:
- $p_\ell>0$ for all $\ell$;
- $\sum_\ell p_\ell=1$ (as an unconditional sum);
- $\ell\mapsto V_\ell/p_\ell$ summable;
- $\ell\mapsto p_\ell C_\ell$ summable;
- $x=(\varepsilon^2)^{-1}\big((\sum'_\ell V_\ell/p_\ell)(\sum'_\ell p_\ell C_\ell)\big)$.

Then:
- (a) $(\varepsilon^2)^{-1}S_\infty^2$ is the least element of $\mathcal X$: it belongs to $\mathcal X$ and is $\le$ every element of $\mathcal X$;
- (b) as $L\to\infty$, $(\varepsilon^2/2)^{-1}S_L^2\to2\big((\varepsilon^2)^{-1}S_\infty^2\big)$.

- **Truth: true.**
  - Lower bound: by Cauchy–Schwarz on partial sums, $(\sum_{\ell<n}\sqrt{V_\ell C_\ell})^2\le(\sum' V/p)(\sum' pC)$; let $n\to\infty$.
  - Attainment: take $p_\ell=\sqrt{V_\ell/C_\ell}/\sum'_k\sqrt{V_k/C_k}$.
  - (b) as in #15.
  - Checked numerically, including random geometric competitors $p$.
- **Non-vacuity:** $V_\ell=4^{-\ell}$, $C\equiv1$.
- **Junk values:** none. The set definition includes both summability requirements, so every tsum in it is genuine.
- **Concerns:**
  - Conjunct (b) is literally the conclusion of #15, and nothing connects it to (a).
  - The condition $\sum p=1$ is not needed for the lower bound, only for membership of the minimiser.

---

## Part D. Module `MlmcLean.RectangularMIMC`

Throughout, $D\in\mathbb N$ is arbitrary (including $D=0$), and multi-indices are $\ell\in\mathbb N^D$.

### 18. `rectSet` (definition)

**Rendering.** For $L\in\mathbb N^D$:
$$\mathrm{Rect}(L)=\{\ell\in\mathbb N^D:\ \ell_d\le L_d\ \forall d\}=\prod_{d}\{0..L_d\},$$
as a finite set.

- **Junk values:** for $D=0$ this is $\{()\}$, the singleton containing the empty tuple.
- **Concerns:** none.

### 19. `sum_rectSet_crossDiff` (theorem)

**Rendering.** For every $D$, every $p:\mathbb N^D\to\mathbb R$ and every $L\in\mathbb N^D$:
$$\sum_{\ell\in\mathrm{Rect}(L)}\boldsymbol\Delta p(\ell)=p(L),$$
where $\boldsymbol\Delta$ is the mixed backward difference `crossDiff` (#36).

- **Truth: true.** Telescoping in each coordinate, using the convention that the "$\ell_d-1$" term is dropped when $\ell_d=0$. For $D=0$ both sides equal $p(())$. Verified exactly with rationals for $D\le4$.
- **Non-vacuity:** no hypotheses.
- **Junk values:** none (natural-number subtraction in `crossDiff` is guarded).
- **Concerns:** none.

### 20. `sum_filter_box_lt_le` (lemma)

**Rendering.** Let $\alpha\in\mathbb R^D$ with $\alpha_d>0$ for all $d$. Let $L\in\mathbb N^D$, a coordinate $d\in\{0,\dots,D-1\}$ and $n\in\mathbb N$. Then
$$\sum_{\substack{\ell\in\{0,\dots,n-1\}^D\\ \ell_d>L_d}}2^{-\langle\alpha,\ell\rangle}\ \le\ \big(2^{-\alpha_d}\big)^{L_d+1}\prod_{d'}\big(1-2^{-\alpha_{d'}}\big)^{-1}.$$

- **Truth: true.** Extend the sum to all $\ell$ with $\ell_d\ge L_d+1$ and sum the geometric series factor by factor. Checked numerically.
- **Non-vacuity:** requires $D\ge1$ (so that $d$ exists); for example $D=1$, $\alpha=1$.
- **Junk values:** none ($1-2^{-\alpha_{d'}}\in(0,1)$).
- **Concerns:** the bound does not depend on $n$.

### 21. `sum_sdiff_rectSet_le` (theorem)

**Rendering.** Let $\alpha_d>0$ for all $d$, $L\in\mathbb N^D$, and $s$ any finite set of multi-indices. Then
$$\sum_{\ell\in s\setminus\mathrm{Rect}(L)}2^{-\langle\alpha,\ell\rangle}\le\Big(\sum_d\big(2^{-\alpha_d}\big)^{L_d+1}\Big)\prod_{d'}\big(1-2^{-\alpha_{d'}}\big)^{-1}.$$

- **Truth: true.** Each $\ell\notin\mathrm{Rect}(L)$ has some $\ell_d>L_d$; apply a union bound and #20. For $D=0$ both sides are $0$. Checked numerically.
- **Non-vacuity:** trivial.
- **Junk values:** none.
- **Concerns:** the bound is uniform over all finite $s$.

### 22. `mimc_rect_core` (theorem)

**Rendering.** Let $\alpha,\beta,\gamma\in\mathbb R^D$ with $\alpha_d>0$, $\gamma_d>0$ and $\gamma_d<\beta_d$ for all $d$, and $\sum_d\gamma_d/\alpha_d\le2$. Let $c_1,c_2,c_3>0$. Then there is $c_4>0$ such that for every $\varepsilon\in(0,1)$ there exist $L\in\mathbb N^D$ and $N:\mathbb N^D\to\mathbb N$ with $N_\ell>0$ for every $\ell$, such that:
- (i) for every finite set $s$ of multi-indices, $c_1\sum_{\ell\in s\setminus\mathrm{Rect}(L)}2^{-\langle\alpha,\ell\rangle}\le\varepsilon/2$;
- (ii) $\sum_{\ell\in\mathrm{Rect}(L)}c_22^{-\langle\beta,\ell\rangle}/N_\ell\le\varepsilon^2/2$;
- (iii) $\sum_{\ell\in\mathrm{Rect}(L)}N_\ell\,c_32^{\langle\gamma,\ell\rangle}\le c_4\,\varepsilon^{-2}$ (real power).

- **Truth: true.**
  - Choose each $L_d$ so that $2^{-\alpha_d(L_d+1)}\le\varepsilon/(2c_1K\max(D,1))$ with $K=\prod(1-2^{-\alpha_d})^{-1}$; then (i) follows from #21.
  - Choose $N_\ell=\lceil\tfrac2{\varepsilon^2}\sqrt{V_\ell/C_\ell}\sum_{\mathrm{Rect}}\sqrt{V_kC_k}\rceil$, where $V,C$ are the two bounding functions; then (ii) holds.
  - For (iii): the cost is at most $\tfrac2{\varepsilon^2}(\sum_{\mathrm{Rect}}\sqrt{V_kC_k})^2+\sum_{\mathrm{Rect}}C_\ell$. The first term is $O(\varepsilon^{-2})$ because $\gamma_d<\beta_d$. The second is $O(\prod_d2^{\gamma_dL_d})=O(\varepsilon^{-\sum\gamma_d/\alpha_d})=O(\varepsilon^{-2})$.
  - The numerical ratio cost$/\varepsilon^{-2}$ converges ($D=1,2,3$).
- **Non-vacuity:** $D=1$, $\alpha=\gamma=1$, $\beta=2$, $c_i=1$.
- **Junk values:** none.
- **Concerns:**
  - A deterministic statement with no random variables.
  - $N_\ell>0$ is required for all $\ell$, including outside $\mathrm{Rect}(L)$; this is harmless.

### 23. `giles_mimc_rectangular` (theorem)

**Rendering.** Data:
- $D\in\mathbb N$ and a type $\Omega$ with a σ-algebra and a **probability** measure $\mu$; write $\mathbb E[X]=\int X\,d\mu$;
- functions $P:\Omega\to\mathbb R$ and $P_\ell:\Omega\to\mathbb R$ for $\ell\in\mathbb N^D$;
- functions $Y_\ell^n,\ \mathrm{Cost}_\ell^n:\Omega\to\mathbb R$ for $\ell\in\mathbb N^D$ and $n\in\mathbb N$;
- real numbers $V_\ell,C_\ell$ for $\ell\in\mathbb N^D$;
- vectors $\alpha,\beta,\gamma\in\mathbb R^D$ and reals $c_1,c_2,c_3$.

Hypotheses:
1. $\alpha_d>0$, $\gamma_d>0$ and $\gamma_d<\beta_d$ for all $d$; $\sum_d\gamma_d/\alpha_d\le2$; $c_1,c_2,c_3>0$.
2. $P$ and every $P_\ell$ are $\mu$-integrable.
3. For every $\ell$ and every $n\ge1$: $Y_\ell^n\in L^2(\mu)$, and $\mathrm{Cost}_\ell^n$ is $\mu$-integrable.
4. For **every** $N:\mathbb N^D\to\mathbb N$ with $N_\ell\ge1$ for all $\ell$, and every pair of distinct multi-indices $i\ne j$, the functions $Y_i^{N_i}$ and $Y_j^{N_j}$ are independent under $\mu$.
5. For every $\ell$ and $n\ge1$: $\mathbb E[\mathrm{Cost}_\ell^n]=n\,C_\ell$ and $\operatorname{Var}(Y_\ell^n)=V_\ell/n$.
6. For every $\delta>0$ there is $n_0\in\mathbb N$ such that every $\ell$ with $\ell_d\ge n_0$ for all $d$ satisfies $|\mathbb E[P_\ell-P]|<\delta$.
7. For every $\ell$ and $n\ge1$: $\mathbb E[Y_\ell^n]=\mathbb E\big[\omega\mapsto\boldsymbol\Delta\big(m\mapsto P_m(\omega)\big)(\ell)\big]$, where $\boldsymbol\Delta$ is `crossDiff` (#36) applied for each fixed $\omega$ to $m\mapsto P_m(\omega)$.
8. For every $\ell$ and $n\ge1$: $|\mathbb E[Y_\ell^n]|\le c_12^{-\langle\alpha,\ell\rangle}$.
9. For every $\ell$: $V_\ell\le c_22^{-\langle\beta,\ell\rangle}$ and $C_\ell\le c_32^{\langle\gamma,\ell\rangle}$.

Conclusion: there is $c_4>0$ such that for every $\varepsilon\in(0,1)$ there exist $L\in\mathbb N^D$ and $N:\mathbb N^D\to\mathbb N$ with $N_\ell\ge1$ for all $\ell$ and
$$\mathbb E\Big[\Big(\sum_{\ell\in\mathrm{Rect}(L)}Y_\ell^{N_\ell}-\mathbb E[P]\Big)^2\Big]<\varepsilon^2,\qquad \mathbb E\Big[\sum_{\ell\in\mathrm{Rect}(L)}\mathrm{Cost}_\ell^{N_\ell}\Big]\le c_4\,\varepsilon^{-2}.$$
By big-operator precedence, $\mathbb E[P]$ is subtracted once from the whole sum, not from each term.

- **Truth: true.**
  - By hypotheses 3–5 (pairwise independence and $L^2$), the left quantity equals $\sum_{\mathrm{Rect}(L)}V_\ell/N_\ell+\big(\sum_{\mathrm{Rect}(L)}\mathbb E[Y_\ell^{N_\ell}]-\mathbb E P\big)^2$.
  - By hypothesis 7, #19 applied pointwise in $\omega$, and linearity: $\sum_{\mathrm{Rect}(L)}\mathbb E[Y_\ell]=\mathbb E[P_L]$.
  - By hypotheses 6 and 8 (with $n=1$) and #21: $|\mathbb E[P]-\mathbb E[P_L]|\le c_1K\sum_d2^{-\alpha_d(L_d+1)}$.
  - Then the choice of #22, with $V_\ell\le c_22^{-\langle\beta,\ell\rangle}$ and $C_\ell\le c_32^{\langle\gamma,\ell\rangle}$, gives squared bias $\le\varepsilon^2/4$, variance part $\le\varepsilon^2/2$ (so total $<\varepsilon^2$), and expected cost $=\sum N_\ell C_\ell\le\sum N_\ell c_32^{\langle\gamma,\ell\rangle}\le c_4\varepsilon^{-2}$.
  - Monte Carlo confirms the variance-plus-squared-bias decomposition (`check_mc_montecarlo.py`).
- **Non-vacuity:**
  - Trivial witness: $\Omega$ a single point, with $P,P_\ell,Y,\mathrm{Cost}\equiv0$ and $V=C\equiv0$. All hypotheses hold (constants are independent, the variance is $0$, and so on).
  - Non-trivial witness: $\Omega=[0,1]$ with Lebesgue measure and disjoint families of Rademacher functions, $Y_\ell^n=m_\ell+\sigma_\ell\cdot\frac1n\sum_{k<n}r_{\phi(\ell,k)}$ with $\phi$ injective, deterministic $P_\ell$, and $m_\ell=\boldsymbol\Delta P(\ell)$. Hypothesis 4 then holds for every $N$ simultaneously.
- **Junk values:** none active. All integrals are of integrable functions, and every variance is of an $L^2$ function. $V_\ell\ge0$ is forced by hypothesis 5.
- **Concerns:**
  1. $C_\ell$ (and hence $\mathbb E[\mathrm{Cost}_\ell^n]$) is **not** required to be nonnegative. Only upper bounds are assumed, which only makes the upper-bound conclusion easier.
  2. $\mathrm{Cost}_\ell^n$ is constrained only through its mean, and $Y_\ell^n$ only through its mean, variance and pairwise independence; no sample-average structure is imposed.
  3. Hypothesis 4 is quantified over all allocations $N$ at once and over infinitely many multi-indices. It is strong, but satisfiable as shown.
  4. Hypothesis 8 is stated for $\mathbb E[Y_\ell^n]$, which by hypothesis 7 equals $\mathbb E[\boldsymbol\Delta P(\ell)]$ for every $n$.
  5. The conclusion is an existence statement (some $L,N$).

### 24. `mimc_rect_lower_bounds` (theorem)

**Rendering.** Data:
- $D$, $(\Omega,\mu)$ with $\mu$ a probability measure;
- $P$, $P_\ell$, $Y_\ell^n$, $\mathrm{Cost}_\ell^n$, $V_\ell$, $C_\ell$, $\alpha,\beta,\gamma\in\mathbb R^D$ as in #23;
- reals $a_1,a_2,a_3,\varepsilon$, a fixed $L\in\mathbb N^D$ and a fixed $N:\mathbb N^D\to\mathbb N$.

Hypotheses:
1. $\alpha_d>0$ and $\gamma_d\ge0$ for all $d$ (no condition on $\beta$); $a_1,a_2,a_3>0$; $\varepsilon>0$; $N_\ell\ge1$ for all $\ell$.
2. $P$ and every $P_\ell$ are integrable. For $n\ge1$: $Y_\ell^n\in L^2(\mu)$ and $\mathrm{Cost}_\ell^n$ is integrable.
3. For **this** $N$: $Y_i^{N_i}$ and $Y_j^{N_j}$ are independent for all $i\ne j$.
4. For $n\ge1$: $\mathbb E[\mathrm{Cost}_\ell^n]=nC_\ell$, $\operatorname{Var}(Y_\ell^n)=V_\ell/n$, and $\mathbb E[Y_\ell^n]=\mathbb E[\boldsymbol\Delta(m\mapsto P_m(\cdot))(\ell)]$.
5. For every $\ell$ and **every** coordinate $d$: $a_12^{-\alpha_d\ell_d}\le|\mathbb E[P_\ell-P]|$.
6. For every $\ell$: $a_22^{-\langle\beta,\ell\rangle}\le V_\ell$ and $a_32^{\langle\gamma,\ell\rangle}\le C_\ell$.
7. $\mathbb E\big[(\sum_{\ell\in\mathrm{Rect}(L)}Y_\ell^{N_\ell}-\mathbb E[P])^2\big]<\varepsilon^2$.

Conclusions (all three):
- (A) for every $d$: $a_1/\varepsilon<2^{\alpha_dL_d}$;
- (B) $a_3\,(a_1/\varepsilon)^{\sum_d\gamma_d/\alpha_d}\le\mathbb E\big[\sum_{\ell\in\mathrm{Rect}(L)}\mathrm{Cost}_\ell^{N_\ell}\big]$ (real power);
- (C) for every $d$ with $\beta_d\le\gamma_d$: $a_2a_3(L_d+1)^2\varepsilon^{-2}\le\mathbb E\big[\sum_{\ell\in\mathrm{Rect}(L)}\mathrm{Cost}_\ell^{N_\ell}\big]$.

- **Truth: true.**
  - (A): as in #23, the bias $\mathbb E[\sum Y]-\mathbb E P$ equals $\mathbb E[P_L-P]$ and its square is at most the left side of hypothesis 7, which is $<\varepsilon^2$. So $a_12^{-\alpha_dL_d}\le|\mathbb E[P_L-P]|<\varepsilon$.
  - (B): the expected cost is $\sum N_\ell C_\ell\ge C_L\ge a_32^{\langle\gamma,L\rangle}=a_3\prod_d(2^{\alpha_dL_d})^{\gamma_d/\alpha_d}\ge a_3(a_1/\varepsilon)^{\sum\gamma_d/\alpha_d}$. This uses $\gamma_d\ge0$ and positivity of all terms.
  - (C): the variance part $\sum V_\ell/N_\ell$ is at most the left side of hypothesis 7, which is $<\varepsilon^2$. Cauchy–Schwarz gives $\big(\sum_{\mathrm{Rect}}\sqrt{V_\ell C_\ell}\big)^2\le\varepsilon^2\sum N_\ell C_\ell$. Restricting to $\ell=k e_d$ ($k\le L_d$) gives $\sum\sqrt{V_\ell C_\ell}\ge(L_d+1)\sqrt{a_2a_3}$ when $\gamma_d\ge\beta_d$.
- **Non-vacuity:** jointly satisfiable, but hypothesis 6 forces $V_\ell>0$ for infinitely many pairwise independent $Y$'s, so the witness must be non-trivial.
  - Take $D=1$, $\alpha=1$, $\beta=2$, $\gamma=1$, $a_i=1$, $P\equiv0$, $P_\ell\equiv2^{-\ell}$.
  - Take $Y_\ell^n=\boldsymbol\Delta P(\ell)+2^{-\ell}\frac1n\sum_{k<n}r_{\phi(\ell,k)}$ with Rademacher functions on $[0,1]$.
  - Take $V_\ell=4^{-\ell}$, $C_\ell=2^\ell$, $\mathrm{Cost}_\ell^n\equiv n2^\ell$, $L=0$, $N\equiv1$ and $\varepsilon=2$; the left side of hypothesis 7 is $2<4$.
- **Junk values:** none active (all integrands integrable, $a_1/\varepsilon>0$ in the real power).
- **Concerns:**
  - Hypothesis 5 is strong: it requires $|\mathbb E[P_\ell-P]|\ge a_1\max_d2^{-\alpha_d\ell_d}$ uniformly in the other coordinates. For example, the bias stays $\ge a_1$ along any ray on which one coordinate stays $0$. Conclusions (A) and (B) depend on this form.
  - (C) is conditional on $\beta_d\le\gamma_d$.
  - The strict inequality in (A) comes from the strict inequality in hypothesis 7.

### 25. `mimc_rect_necessary` (theorem)

**Rendering.** Data are as in #24, without $\varepsilon$, $L$ and $N$. Hypotheses:
1. $\alpha_d>0$ and $\gamma_d\ge0$ for all $d$; $a_1,a_2,a_3>0$.
2. Integrability and $L^2$ conditions as in #24.
3. For **every** $N$ with all $N_\ell\ge1$: $Y_i^{N_i}$ and $Y_j^{N_j}$ are independent for $i\ne j$.
4. The mean, variance and $\boldsymbol\Delta$-mean identities of #24.
5. The per-direction lower bound $a_12^{-\alpha_d\ell_d}\le|\mathbb E[P_\ell-P]|$ for all $\ell$ and all $d$.
6. $a_22^{-\langle\beta,\ell\rangle}\le V_\ell$ and $a_32^{\langle\gamma,\ell\rangle}\le C_\ell$ for all $\ell$.
7. There are reals $c_4$ and $\varepsilon_0>0$ (no sign condition on $c_4$) such that for every $\varepsilon\in(0,\varepsilon_0)$ there exist $L\in\mathbb N^D$ and $N$ with all $N_\ell\ge1$ satisfying both:
   $$\mathbb E\Big[\Big(\sum_{\mathrm{Rect}(L)}Y_\ell^{N_\ell}-\mathbb E P\Big)^2\Big]<\varepsilon^2,\qquad\mathbb E\Big[\sum_{\mathrm{Rect}(L)}\mathrm{Cost}_\ell^{N_\ell}\Big]\le c_4\varepsilon^{-2}.$$

Conclusion: $\gamma_d<\beta_d$ for every $d$, and $\sum_d\gamma_d/\alpha_d\le2$.

- **Truth: true.**
  - From #24(B): $a_3a_1^{s}\varepsilon^{-s}\le c_4\varepsilon^{-2}$ for all small $\varepsilon$, with $s=\sum\gamma_d/\alpha_d$. This forces $s\le2$.
  - If $\beta_d\le\gamma_d$ for some $d$, #24(C) gives $(L_d+1)^2\le c_4/(a_2a_3)$, so $L_d$ is bounded. But #24(A) forces $L_d\to\infty$ as $\varepsilon\to0$. Contradiction.
  - For $D=0$ the conclusion is trivial ($0\le2$).
- **Non-vacuity:** the model in #24 (with $\gamma=1<\beta=2$) also satisfies all hypotheses of #23 (take $c_1=c_2=c_3=1$). So hypothesis 7 holds with $\varepsilon_0=1$ by #23, and the hypotheses are jointly satisfiable.
- **Junk values:** none.
- **Concerns:** the conclusion rests entirely on the lower-bound hypotheses (5)–(6), especially the uniform per-direction form of (5); see #24.

---

## Part E. Module `MlmcLean.ML2RComplexity`

Throughout, $q:=2^{-\alpha}$ (a real power), and $w^{(L)}_\ell=w^{(L)}_\ell(\alpha)$ as in A10.

### 26. `abs_ml2rWeight_le` (theorem)

**Rendering.** Let $\alpha>0$ and $L,\ell\in\mathbb N$ with $\ell\le L$. Then
$$\big|w^{(L)}_\ell\big|\le\Big(\exp\!\big(q/(1-q)^2\big)\Big)^2\cdot q^{\,L-\ell},\qquad q=2^{-\alpha}.$$

- **Truth: true.**
  - With $m=L-\ell$: $|w_\ell^{(L)}|=q^{m(m+1)/2}\prod_{j=1}^{\ell}(1-q^j)^{-1}\prod_{j=1}^{m}(1-q^j)^{-1}$.
  - Each product is at most $\prod_{j\ge1}(1-q^j)^{-1}\le\exp\big(\sum_j q^j/(1-q^j)\big)\le\exp(q/(1-q)^2)$.
  - And $q^{m(m+1)/2}\le q^m$.
  - High-precision checks (80–100 digits, $\alpha\in[0.05,12]$, $L\le29$) find a maximum ratio of $0.99999988$, which approaches 1 as $\alpha\to\infty$ and is never exceeded.
- **Non-vacuity:** $\alpha=1$, $L=\ell=0$.
- **Junk values:** $L-\ell$ is natural subtraction, but $\ell\le L$ prevents truncation.
- **Concerns:** none.

### 27. `ml2rWeightBound` (definition)

**Rendering.** For $\alpha\in\mathbb R$:
$$B(\alpha)=\frac{\big(\exp(q/(1-q)^2)\big)^2}{1-q},\qquad q=2^{-\alpha}.$$

- **Junk values:**
  - At $\alpha=0$: $q=1$, so $q/0^2=0$, $\exp0=1$ and $1/0=0$, giving $B(0)=0$.
  - For $\alpha<0$: $B(\alpha)<0$.
- **Concerns:** only used with $\alpha>0$ in this packet.

### 28. `sum_abs_ml2rWeight_le` (theorem)

**Rendering.** For $\alpha>0$ and $L\in\mathbb N$: $\sum_{\ell=0}^{L}|w^{(L)}_\ell|\le B(\alpha)$.

- **Truth: true.** Sum #26 over $\ell$: $\sum_{j=0}^{L}q^j\le1/(1-q)$. Checked numerically.
- **Non-vacuity:** trivial.
- **Junk values:** none.
- **Concerns:** none.

### 29. `abs_ml2r_coeff_le` (theorem)

**Rendering.** For $\alpha>0$ and any $L,\ell\in\mathbb N$ (no order between them): $\big|\sum_{k=\ell}^{L}w^{(L)}_k\big|\le B(\alpha)$. The sum runs over $\{\ell,\dots,L\}$ and is empty when $\ell>L$.

- **Truth: true.** The sum is bounded by #28; for $\ell>L$ the left side is $0<B(\alpha)$. Checked numerically.
- **Non-vacuity:** trivial.
- **Junk values:** empty sum when $\ell>L$ (harmless).
- **Concerns:** none.

### 30. `ml2rLevel` (definition)

**Rendering.** For real $\alpha,c_1,\varepsilon$:
$$R(\alpha,c_1,\varepsilon)=\Big\lceil\sqrt{2\max\big(0,\log_2(2c_1/\varepsilon)\big)/\alpha}\Big\rceil_{\mathbb N}\in\mathbb N.$$

- **Junk values:**
  - $\alpha\le0$ makes the radicand $\le0$ (or divides by $0$), giving $R=0$.
  - $\varepsilon=0$ gives $2c_1/0=0$, $\log_20=0$, and $R=0$.
  - Negative arguments use $\log_2|\cdot|$.
- **Concerns:** none.

### 31. `ml2rLevel_bias` (theorem)

**Rendering.** For $\alpha>0$, $c_1>0$ and $\varepsilon>0$, with $R=R(\alpha,c_1,\varepsilon)$ and $R(R+1)/2$ computed in $\mathbb R$:
$$c_1\,2^{-\alpha R(R+1)/2}\le\varepsilon/2 .$$

- **Truth: true.**
  - If $2c_1\le\varepsilon$, then $R=0$ and the claim is $c_1\le\varepsilon/2$.
  - Otherwise, with $x=\log_2(2c_1/\varepsilon)>0$: $R^2\ge2x/\alpha$, so $\alpha R(R+1)/2\ge x$.
  - 20,000 random checks pass.
- **Non-vacuity:** trivial.
- **Junk values:** none.
- **Concerns:** none.

### 32. `ml2rLevel_lt_sqrt_levelL` (theorem)

**Rendering.** For $\alpha>0$ and **any** real $c_1,\varepsilon$ (no sign conditions):
$$R(\alpha,c_1,\varepsilon)<\sqrt{2\,\Lambda(\alpha,c_1,\varepsilon/2)}+1,\qquad \Lambda(\alpha,c_1,\varepsilon/2)=\big\lceil\log_2\big(c_1/(\varepsilon/2)\big)/\alpha\big\rceil_{\mathbb N}.$$

- **Truth: true.**
  - $c_1/(\varepsilon/2)$ and $2c_1/\varepsilon$ are the same real number, including the value $0$ at $\varepsilon=0$. Call its base-2 logarithm $x$.
  - $R<\sqrt{2\max(0,x)/\alpha}+1$, and $\Lambda\ge\max(0,x)/\alpha$.
  - Checked numerically, including negative and zero $c_1,\varepsilon$.
- **Non-vacuity:** trivial.
- **Junk values:** for $c_1\le0$ or $\varepsilon\le0$ both sides use the same junk logarithm, so the inequality still holds, but it has no quantitative content there.
- **Concerns:** there are no positivity hypotheses on $c_1$ and $\varepsilon$ (a mild point).

### 33. `ml2r_mse_cost` (theorem)

**Rendering.** Take real $\alpha,\beta,\gamma,c_1,c_2,c_3,\varepsilon$ with $\alpha>0$, $c_1\ge0$, $c_2>0$, $c_3>0$ and $\varepsilon>0$ ($\beta,\gamma$ arbitrary). Let $L\in\mathbb N$ with $c_12^{-\alpha L(L+1)/2}\le\varepsilon/2$. Then there is $N:\mathbb N\to\mathbb N$ with $N_\ell\ge1$ for all $\ell$ such that
$$\big(c_12^{-\alpha L(L+1)/2}\big)^2+\sum_{\ell=0}^{L}\Big(\sum_{k=\ell}^{L}w^{(L)}_k\Big)^2\frac{c_22^{-\beta\ell}}{N_\ell}<\varepsilon^2$$
and
$$\sum_{\ell=0}^{L}N_\ell\,c_32^{\gamma\ell}\le2(\varepsilon^2)^{-1}\big(B(\alpha)^2c_2c_3\big)\Big(\sum_{\ell=0}^{L}\big(2^{(\gamma-\beta)/2}\big)^{\ell}\Big)^2+\sum_{\ell=0}^{L}c_32^{\gamma\ell}.$$

- **Truth: true.**
  - Take $N_\ell=\big\lceil\frac2{\varepsilon^2}B^2\sqrt{V_\ell/C_\ell}\sum_{k\le L}\sqrt{V_kC_k}\big\rceil$ for $\ell\le L$ (and $1$ otherwise), with $V_\ell=c_22^{-\beta\ell}$ and $C_\ell=c_32^{\gamma\ell}$.
  - Using #29, the weighted sum is $\le\varepsilon^2/2$, and the first term is $\le\varepsilon^2/4$, so the total is $<\varepsilon^2$.
  - The cost bound follows from $\lceil x\rceil\le x+1$.
  - 300 random high-precision checks pass.
- **Non-vacuity:** $c_1=0$ (hypothesis trivial), all other constants $1$.
- **Junk values:** none.
- **Concerns:** deterministic: the left-hand expression is an explicit formula, with no random variables.

### 34. `ml2r_complexity_eq` (theorem)

**Rendering.** Take real $\alpha,\beta,\gamma,c_1,c_2,c_3$ with $\alpha>0$, $\gamma>0$, $\beta=\gamma$ and $c_1,c_2,c_3>0$. Then there is $c_4>0$ such that for every $\varepsilon$ with $0<\varepsilon<e^{-1}$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with all $N_\ell\ge1$ satisfying both:
- the same "$<\varepsilon^2$" inequality as in #33 (with this $L$ and $N$);
- $\sum_{\ell=0}^{L}N_\ell c_32^{\gamma\ell}\le c_4\big(\varepsilon^{-2}|\log\varepsilon|\big)$.

- **Truth: true.**
  - Take $L=R(\alpha,c_1,\varepsilon)$ and $N$ from #33 (the hypothesis is supplied by #31).
  - With $\beta=\gamma$ the first cost term is $\frac2{\varepsilon^2}B^2c_2c_3(L+1)^2$, and $(L+1)^2=O(|\log\varepsilon|)$ uniformly on $(0,e^{-1})$.
  - The second term is $O(2^{\gamma L})=\exp(O(\sqrt{|\log\varepsilon|}))=O(\varepsilon^{-2})$.
  - The numerical ratio converges (to about $4B^2c_2c_3/(\alpha\log2)$).
- **Non-vacuity:** all parameters equal to $1$.
- **Junk values:** none ($|\log\varepsilon|>1$ on the range).
- **Concerns:** none. $c_4$ is uniform in $\varepsilon$ but very large, because of the $B(\alpha)^2$ factor.

### 35. `ml2r_complexity_lt` (theorem)

**Rendering.** As #34, but with $\beta<\gamma$ in place of $\beta=\gamma$. The cost conclusion becomes
$$\sum_{\ell=0}^{L}N_\ell c_32^{\gamma\ell}\le c_4\Big(\varepsilon^{-2}\cdot2^{(\gamma-\beta)\sqrt{2\log_2(1/\varepsilon)/\alpha}}\Big).$$

- **Truth: true.**
  - With $L=R(\alpha,c_1,\varepsilon)$: $L\le\sqrt{2\log_2(1/\varepsilon)/\alpha}+\text{const}$, by subadditivity of $\sqrt{\cdot}$ applied to $\log_2(2c_1/\varepsilon)=\log_2(1/\varepsilon)+\log_2(2c_1)$.
  - Hence $(\sum_{\ell\le L}\rho^\ell)^2=O(2^{(\gamma-\beta)L})$ with $\rho=2^{(\gamma-\beta)/2}>1$.
  - The second term is $O(2^{\gamma s})$ with $s=\sqrt{2\log_2(1/\varepsilon)/\alpha}$. It is at most $\text{const}\cdot\varepsilon^{-2}2^{(\gamma-\beta)s}$ because $\beta s-\alpha s^2$ is bounded above (this holds even for $\beta<0$).
  - The numerical ratio is bounded.
- **Non-vacuity:** $\alpha=1,\beta=0.5,\gamma=1.5$, $c_i=1$.
- **Junk values:** none.
- **Concerns:** none.

---

## Part F. Module `MlmcLean.MultiIndex`

### 36. `crossDiff` (definition)

**Rendering.** For $D\in\mathbb N$, $p:\mathbb N^D\to\mathbb R$ and $\ell\in\mathbb N^D$, $\boldsymbol\Delta p(\ell)$ is defined by recursion on $D$:
- $D=0$: $\boldsymbol\Delta p(\ell)=p(\ell)$.
- $D=n+1$: write $\ell=(\ell_0,\ell')$ with $\ell'\in\mathbb N^{n}$ the tail. Then
$$\boldsymbol\Delta p(\ell)=\boldsymbol\Delta\big(m\mapsto p(\ell_0,m)\big)(\ell')-\begin{cases}0&\ell_0=0\\ \boldsymbol\Delta\big(m\mapsto p(\ell_0-1,m)\big)(\ell')&\ell_0\ne0.\end{cases}$$

Equivalently (verified exactly for $D\le4$):
$$\boldsymbol\Delta p(\ell)=\sum_{S\subseteq\{d:\ell_d>0\}}(-1)^{|S|}p(\ell-\mathbf 1_S).$$
This is the product over coordinates of backward differences, where a term with a would-be index $-1$ is dropped.

- **Junk values:** $\ell_0-1$ is natural subtraction, but it is used only when $\ell_0\ne0$.
- **Concerns:** none.

### 37. `crossDiff_two` (theorem)

**Rendering.** Let $p:\mathbb N^2\to\mathbb R$, let $e$ be the (unique) empty tuple, and let $a,b\in\mathbb N$ with $a\ne0$ and $b\ne0$. Writing $(a,b)$ for the tuple $a,b$ followed by $e$:
$$\boldsymbol\Delta p(a,b)=p(a,b)-p(a-1,b)-p(a,b-1)+p(a-1,b-1).$$

- **Truth: true.** Unfold the recursion twice. Verified exactly.
- **Non-vacuity:** $a=b=1$.
- **Junk values:** none. The hypotheses $a,b\ne0$ are needed: for $a=0$ the definition drops the $a-1$ terms, whereas the formula would read $0-1=0$.
- **Concerns:** the binder $e$ is a dummy.

---

## Part G. Module `MlmcLean.Randomised`

### 38. `singleTerm` (definition)

**Rendering.** Let $\Omega$ be a type (no measurable structure is required). For $P:\mathbb N\to(\Omega\to\mathbb R)$, $K:\Omega\to\mathbb N$, $p:\mathbb N\to\mathbb R$ and $\omega\in\Omega$:
$$Z(\omega)=\big(p_{K(\omega)}\big)^{-1}\,\Delta P_{K(\omega)}(\omega),$$
with $\Delta P$ as in A3: $\Delta P_0=P_0$ and $\Delta P_{k}=P_k-P_{k-1}$ for $k\ge1$.

- **Junk values:** if $p_{K(\omega)}=0$, then $0^{-1}=0$ and $Z(\omega)=0$.
- **Concerns:** no theorem in this packet uses it.

### 39. `singleTermN` (definition)

**Rendering.** For types $\Omega,\Omega'$, $\xi:\mathbb N\to(\Omega'\to\Omega)$, $N\in\mathbb N$ and $x\in\Omega'$:
$$\bar Z_N(x)=N^{-1}\sum_{n=0}^{N-1}Z(\xi_n(x)),$$
with $Z$ as in #38.

- **Junk values:** $N=0$ gives $0^{-1}\cdot0=0$.
- **Concerns:** no theorem in this packet uses it.

### 40. `geomLevelProb` (definition)

**Rendering.** For real $\beta,\gamma$ and $\ell\in\mathbb N$, with $q=2^{-(\beta+\gamma)/2}$ (real power):
$$\pi_{\beta,\gamma}(\ell)=(1-q)\,q^{\ell}.$$

- **Junk values:** none as such. However, it is a probability vector ($\ge0$, summing to $1$) only when $\beta+\gamma>0$. For $\beta+\gamma=0$ all values are $0$; for $\beta+\gamma<0$ they are negative.
- **Concerns:** no theorem in this packet uses it.

### 41. `optimalLevelProb` (definition)

**Rendering.** For $V,C:\mathbb N\to\mathbb R$ and $\ell\in\mathbb N$:
$$\pi^*(\ell)=\frac{\sqrt{V_\ell/C_\ell}}{\sum'_k\sqrt{V_k/C_k}}.$$

- **Junk values:** if $k\mapsto\sqrt{V_k/C_k}$ is not summable, the denominator is $0$ and $\pi^*\equiv0$. Also $C_\ell=0$ gives $\sqrt0=0$.
- **Concerns:** #42 assumes summability and positivity, so no junk arises there.

### 42. `randomised_optimal_cost` (theorem)

**Rendering.** Let $V,C:\mathbb N\to\mathbb R$ with $V_\ell>0$ and $C_\ell>0$ for all $\ell$, such that $\ell\mapsto\sqrt{V_\ell C_\ell}$ and $\ell\mapsto\sqrt{V_\ell/C_\ell}$ are both summable. Let $\varepsilon\in\mathbb R$ be arbitrary. Write $S=\sum'\sqrt{V_\ell C_\ell}$, $Z=\sum'\sqrt{V_\ell/C_\ell}$ and $\pi^*$ as in #41. Then:
- (a) $\sum'_\ell V_\ell/\pi^*(\ell)=S\cdot Z$;
- (b) $\sum'_\ell\pi^*(\ell)C_\ell=S/Z$;
- (c) $(\varepsilon^2)^{-1}\big(\sum'_\ell V_\ell/\pi^*(\ell)\big)\big(\sum'_\ell\pi^*(\ell)C_\ell\big)=(\varepsilon^2)^{-1}S^2$.

- **Truth: true.** $V_\ell/\pi^*(\ell)=Z\sqrt{V_\ell C_\ell}$ and $\pi^*(\ell)C_\ell=\sqrt{V_\ell C_\ell}/Z$, both summable, and $Z>0$. Checked numerically.
- **Non-vacuity:** $V_\ell=4^{-\ell}$, $C\equiv1$.
- **Junk values:** $\varepsilon$ is unconstrained. At $\varepsilon=0$ both sides of (c) are $0$ via $0^{-1}=0$. This is harmless: (c) follows from (a) and (b) for every $\varepsilon$.
- **Concerns:** none.

---

## Part H. Module `MlmcLean.LevelDropping`

### 43. `subsetCorr` (definition)

**Rendering.** For $f:\mathbb N\to\mathbb R$, $f_2:\mathbb N\times\mathbb N\to\mathbb R$, a finite $s\subseteq\mathbb N$ and $\ell\in\mathbb N$, let $\ell^-=\max\{k\in s:k<\ell\}$ when that set is nonempty. Then
$$\tilde f_s(\ell)=\begin{cases}f_2(\ell^-,\ell)&\text{if }\{k\in s:k<\ell\}\ne\varnothing,\\ f(\ell)&\text{otherwise}.\end{cases}$$
$\ell$ itself need not lie in $s$.

- **Junk values:** none.
- **Concerns:** none.

### 44. `subsetCost` (definition)

**Rendering.** For $V,C:\mathbb N\to\mathbb R$, $V_2,C_2:\mathbb N\times\mathbb N\to\mathbb R$, $\varepsilon\in\mathbb R$ and a finite $s\subseteq\mathbb N$:
$$\mathcal C_\varepsilon(s)=(\varepsilon^2)^{-1}\Big(\sum_{\ell\in s}\sqrt{\tilde V_s(\ell)\,\tilde C_s(\ell)}\Big)^2,$$
where $\tilde V_s$ is $\tilde f_s$ with $(f,f_2)=(V,V_2)$, and $\tilde C_s$ is $\tilde f_s$ with $(f,f_2)=(C,C_2)$.

- **Junk values:** $\varepsilon=0$ gives the value $0$; negative products give $\sqrt{\cdot}=0$.
- **Concerns:** none.

### 45. `subsetCost_eq` (theorem)

**Rendering.** Let $M\in\mathbb N$ and $\ell:\{0,\dots,M\}\to\mathbb N$ strictly increasing. Let $V,C,V_2,C_2,\varepsilon$ be arbitrary (no hypotheses). With $s=\{\ell_0,\dots,\ell_M\}$:
$$\mathcal C_\varepsilon(s)=(\varepsilon^2)^{-1}\Big(\sqrt{V(\ell_0)C(\ell_0)}+\sum_{m=0}^{M-1}\sqrt{V_2(\ell_m,\ell_{m+1})\,C_2(\ell_m,\ell_{m+1})}\Big)^2.$$

- **Truth: true.** $\ell_0$ has no smaller element in $s$, and the predecessor of $\ell_{m+1}$ in $s$ is $\ell_m$. Checked numerically with arbitrary-sign inputs, including $\varepsilon=0$ and negative $\varepsilon$.
- **Non-vacuity:** $M=0$.
- **Junk values:** the identity holds regardless of conventions, since both sides apply them identically.
- **Concerns:** none.

### 46. `sum_subsetCorr` (theorem)

**Rendering.** For $p:\mathbb N\to\mathbb R$ and a nonempty finite $s\subseteq\mathbb N$, take $f=p$ and $f_2(i,j)=p_j-p_i$ in $\tilde f_s$. Then
$$\sum_{\ell\in s}\tilde f_s(\ell)=p(\max s).$$

- **Truth: true** (telescoping). Checked numerically.
- **Non-vacuity:** $s=\{0\}$.
- **Junk values:** none.
- **Concerns:** none.

### 47. `subset_optimal_cost` (theorem)

**Rendering.** Let $V,C:\mathbb N\to\mathbb R$ and $V_2,C_2:\mathbb N\times\mathbb N\to\mathbb R$ be positive everywhere. Let $\varepsilon>0$ and $s$ a nonempty finite subset of $\mathbb N$. Let $\mathcal Y$ be the set of reals $c$ for which there is $N:\mathbb N\to\mathbb R$ with:
- $N_\ell>0$ for all $\ell\in s$;
- $\sum_{\ell\in s}\tilde V_s(\ell)/N_\ell\le\varepsilon^2$;
- $c=\sum_{\ell\in s}N_\ell\,\tilde C_s(\ell)$.

Then $\mathcal C_\varepsilon(s)$ is the least element of $\mathcal Y$.

- **Truth: true.**
  - Cauchy–Schwarz: $\big(\sum\sqrt{\tilde V\tilde C}\big)^2\le\big(\sum\tilde V/N\big)\big(\sum N\tilde C\big)\le\varepsilon^2\sum N\tilde C$.
  - Equality is attained at $N_\ell=\varepsilon^{-2}\sqrt{\tilde V_s(\ell)/\tilde C_s(\ell)}\sum_{k\in s}\sqrt{\tilde V_s(k)\tilde C_s(k)}$.
  - Checked numerically.
- **Non-vacuity:** all functions $\equiv1$, $s=\{0\}$, $\varepsilon=1$.
- **Junk values:** none.
- **Concerns:**
  - $N$ is real-valued, so this is a continuous relaxation.
  - The nonemptiness hypothesis is not needed: for $s=\varnothing$ both sides are $0$.
  - The positivity hypotheses are required for all arguments, which is more than is used.

### 48. `card_levelSubsets` (theorem)

**Rendering.** For every $L\in\mathbb N$, the number of subsets of $\{0..L\}$ that contain $L$ is $2^L$.

- **Truth: true.** Checked for $L\le11$.
- **Non-vacuity:** no hypotheses.
- **Junk values:** none.
- **Concerns:** none.

### 49. `exists_optimal_subset` (theorem)

**Rendering.** For arbitrary $V,C,V_2,C_2,\varepsilon$ and $L\in\mathbb N$, let $\mathcal F_L$ be the family of subsets of $\{0..L\}$ that contain $L$. Then there is $s\in\mathcal F_L$ with $\mathcal C_\varepsilon(s)\le\mathcal C_\varepsilon(t)$ for every $t\in\mathcal F_L$.

- **Truth: true.** $\mathcal F_L$ is finite and nonempty (it contains $\{L\}$), so a minimiser exists.
- **Non-vacuity:** no hypotheses.
- **Junk values:** $\mathcal C_\varepsilon$ may take junk values (for $\varepsilon=0$, or negative inputs under $\sqrt{\cdot}$), but a minimiser exists regardless.
- **Concerns:** the statement is true for any real-valued function on a finite nonempty family. It says nothing specific about $\mathcal C_\varepsilon$ and needs no hypotheses.

---

## Numerical checks (work directory)

All scripts are in `work_C_g_section1_2/`. All of them report `FAILS: 0`.

| Script | Statements covered |
|---|---|
| `check_costs.py` | #1, #3, #4, #6 (bounded ratio), #7, #8, #9, #10, #11, #12, #13 |
| `check_ml2r.py` | #26, #28, #29, #31, #32 (including junk ranges), #33, #34/#35 (bounded ratios); the moment property of A10 |
| `check_ml2r_extra.py` | #26 for large $\alpha$ (worst ratio 0.99999988); the $\alpha=0$ junk values of A10 and #27 |
| `check_mimc.py` | #19 and #36 (exact rationals, $D\le4$, closed form), #37, #20, #21, #22 (bounded ratio) |
| `check_subsets_randomised.py` | #45, #46, #47, #48, #42, #17 (Cauchy–Schwarz lower bound) |
| `check_mc_montecarlo.py` | the i.i.d. MSE identity behind #5; the variance-plus-squared-bias decomposition behind #23 and #24 |
