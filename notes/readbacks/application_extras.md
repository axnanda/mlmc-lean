# Blind read-back report: packet M7 (`MlmcLean.ApplicationExtras`)

| Field | Value |
|---|---|
| Date | 2026-09-29 |
| Packet | `readback/round11/packet_M7_application_extras.lean` |
| Declarations audited | 34 (20 theorems, 14 definitions including the appended `roundFixed`) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round11/work_M7/`: `levy_checks.py`, `exponential_checks.py`, `fem_checks.py`, `rates_checks.py`, `spde_checks.py`, `bridge_checks.py`, `roundfixed_checks.py` (each with its `.out`), plus the Lean scratch copies `scratch_packet.lean` / `scratch_eqns.lean` (with `.out`) |

The packet's module is not built, so `import MlmcLean` does not contain it. Instead I compiled a scratch copy of the packet with proofs `sorry`, targeted Mathlib imports and `roundFixed` moved to the top. It compiles with no errors. `#check`/`#print` output with `pp.numericTypes` and `pp.coercions.types` confirmed these casts:

- `(e + 1 / 2) * h` and `(j - 1 / 2) * h` are real arithmetic, $(\uparrow j - 0.5)h$.
- `u (j - 1)` is ℕ-subtraction, which is safe because `1 ≤ j`.
- In `bb_telescoping`, `2 * i` is `(2:ℕ) * (↑i:ℕ)`, not `Fin` arithmetic.
- `roundFixed` uses `zpow` with exponent `e - ↑d : ℤ`.
- The `bbPath` equation lemmas match the rendering below.

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `levyPairSum` | def | n/a | n/a | no |
| 2 | `levyPath` | def | n/a | n/a | no |
| 3 | `levyPath_levyPairSum` | theorem | true | no | no |
| 4 | `measurePreserving_levyPairSum` | theorem | true | no | no |
| 5 | `integral_levyCoarse` | theorem | true | no | no |
| 6 | `levy_telescoping` | theorem | true | no | no |
| 7 | `map_levyPath_levyPairSum` | theorem | true | no | no |
| 8 | `sum_exponential_periods` | theorem | true | no | no |
| 9 | `exponential_periods_clt` | theorem | true | no | no |
| 10 | `hatNodal` | def | n/a | n/a | no |
| 11 | `feStiffness` | def | n/a | n/a | no (x/0 = 0 matters only at h = 0) |
| 12 | `feLoad` | def | n/a | n/a | no |
| 13 | `fe_eq_centralDiff` | theorem | true | no | no |
| 14 | `rates_of_pathwise_random` | theorem | true | no | no |
| 15 | `elliptic_rates_random` | theorem | true | no | no |
| 16 | `not_ae_abs_gaussian_sq_mul_le` | theorem | true | no | no |
| 17 | `spdeD1` | def | n/a | n/a | no |
| 18 | `spdeD2` | def | n/a | n/a | no |
| 19 | `spdeNoiseOp` | def | n/a | n/a | uses `deriv` (0 where not differentiable) and `Real.sqrt` (0 for ρ < 0) |
| 20 | `spdeMilsteinStep` | def | n/a | n/a | same as #19 |
| 21 | `spdeMilsteinStep_eq` | theorem | true | no | no |
| 22 | `spdeScheme` | def | n/a | n/a | no |
| 23 | `spdeScheme_eq_milstein` | theorem | true | no | no |
| 24 | `bbPath` | def | n/a | n/a | values at nodes $i > 2^\ell$ are off-grid junk |
| 25 | `bbPath_nested` | theorem | true | no | no |
| 26 | `bbPath_congr` | theorem | true | no | no |
| 27 | `bb_telescoping` | theorem | true | no | no |
| 28 | `vpInputs` | def | n/a | n/a | pads with 0 beyond index $m$ |
| 29 | `vpPath` | def | n/a | n/a | no |
| 30 | `vpPath_castLE` | theorem | true | no | no |
| 31 | `integral_vpCoarse` | theorem | true | no | no |
| 32 | `vp_telescoping` | theorem | true | no | no |
| 33 | `roundFixed_sum_inconsistent` | theorem | true | no | no (but it depends on Mathlib's tie rule for `round`, see below) |
| 34 | `roundFixed` (appended, from `MlmcLean.RoundingError`) | def | n/a | n/a | no |

## Main points for a human auditor

- **No false, vacuous or junk-dependent theorem.** All 20 theorems are true. I checked them exactly, symbolically or numerically, and every one has a non-degenerate instance.
- **`roundFixed_sum_inconsistent` depends on how ties are rounded.** The witness uses the exact tie $\mathrm{roundFixed}\,0\,1\,(1/4) = \tfrac12\,\mathrm{round}(1/2) = \tfrac12$, which relies on Mathlib's `round` sending ties up ($\lfloor x + 1/2\rfloor$). Under round-half-to-even all three quantities are $0$ on the whole box, so this particular inconsistency disappears. Double rounding is still inconsistent under half-even for other inputs, e.g. $z = 0.37$.
- **Redundant hypotheses (harmless):**
  - `fe_eq_centralDiff`: `hh : h ≠ 0` is unnecessary. At $h = 0$ both sides are $0$ under $x/0 = 0$.
  - `sum_exponential_periods`: `hT` is implied by `hX` together with `hn`. `expMeasure r` is the zero measure for $r \le 0$, which cannot be a law under a probability measure.
  - `integral_levyCoarse`: `[IsProbabilityMeasure ν₂]` is implied by `h`.
- **Hypotheses weaker than usual, but still correct:**
  - `sum_exponential_periods` assumes only pairwise independence.
  - `rates_of_pathwise_random` has no sign condition on $e$ or $K$. It is still true because the hypothesis forces $K e_\ell \ge 0$ a.e.
  - `integral_vpCoarse` has no measurability or integrability hypothesis on $F$. This is fine: ℕ carries the discrete σ-algebra and `Fin k → ℕ` is countable, so every function is measurable and integrability transfers along the coordinate projection.
- **`spdeMilsteinStep_eq` holds for every function $p$.** Mathlib's `deriv_const_mul_field` needs no differentiability, so $B(Bp) = \rho\,p''$ always holds when $\rho \ge 0$. Both `hρ` and `hk` are genuinely needed: dropping either gives numerical counterexamples.
- **The telescoping theorems are exact identities.** `bb_telescoping` and `vp_telescoping` telescope pathwise or in expectation. Their real content is nestedness ($W^{\ell+1}_{2i} = W^\ell_i$) and the level-$\ell$ path depending only on the first $2^\ell$ inputs.
- **`bbPath` models Brownian motion correctly.** As a modelling check, with $r = \mathrm{id}$ its grid covariance equals $\min(s,t)$ exactly, for levels 0 to 3.

---

## Per-declaration sections

### 1. `levyPairSum` (def)

**Rendering.** For a type $M$ with an addition and a sequence $z : \mathbb N \to M$: $(\mathrm{levyPairSum}\,z)_k = z_{2k} + z_{2k+1}$. The order of the summands matters when $+$ is not commutative.

### 2. `levyPath` (def)

**Rendering.** For an additive commutative monoid $M$: $(\mathrm{levyPath}\,z)_n = S_n(z) = \sum_{i<n} z_i$, with $S_0 = 0$. These are the partial sums, i.e. the path at grid times built from its increments.

### 3. `levyPath_levyPairSum` (theorem)

**Rendering.** For every additive commutative monoid $M$, every $z : \mathbb N \to M$ and every $m \in \mathbb N$:
$$\sum_{k<m} (z_{2k} + z_{2k+1}) = \sum_{i<2m} z_i .$$

**Assessment.**
- Truth: true, by induction on $m$ (split `range (2m+2)`). I checked it on 200 random integer sequences (`levy_checks.out`).
- Vacuity: there are no hypotheses.
- Junk values: none.
- Standard fact: regrouping a finite sum into consecutive pairs.

### 4. `measurePreserving_levyPairSum` (theorem)

**Rendering.** Assume $M$ is an additive monoid (not necessarily commutative) with a measurable space structure and jointly measurable addition (`MeasurableAdd₂`), and $\nu$ is a probability measure on $M$. Then `levyPairSum` $: M^{\mathbb N} \to M^{\mathbb N}$ is measurable for the product σ-algebras, and it pushes $\nu^{\otimes\mathbb N}$ (Mathlib's `Measure.infinitePi`) forward to $(\nu*\nu)^{\otimes\mathbb N}$. Here $\nu*\nu$ is the image of $\nu\otimes\nu$ under $(a,b)\mapsto a+b$, with $a$ from the first factor.

**Assessment.**
- Truth: true.
  - Measurability holds coordinatewise, from `MeasurableAdd₂`.
  - Both sides are probability measures on the product σ-algebra, so they are equal if they agree on finite boxes $\prod_{k\in s} A_k$.
  - The blocks $\{2k, 2k+1\}$ are disjoint, so $\nu^{\otimes\mathbb N}\{z : z_{2k}+z_{2k+1}\in A_k,\ k\in s\} = \prod_{k\in s}(\nu\otimes\nu)\{a+b\in A_k\} = \prod_{k\in s}(\nu*\nu)(A_k)$.
  - I checked the law of the first 3 pair sums exactly, both for a discrete ℤ-valued $\nu$ and for a non-commutative free monoid of words (`levy_checks.out`).
- Vacuity: not vacuous, e.g. $M = \mathbb R$, $\nu = N(0,1)$.
- Junk values: none. `MeasurePreserving` includes measurability, so there is no "map of a non-measurable function is 0" issue.
- Standard fact: grouping i.i.d. increments in blocks of two gives i.i.d. increments with the convolution law. This is how the coarse level is coupled to the fine level in MLMC for Lévy-driven processes.

### 5. `integral_levyCoarse` (theorem)

**Rendering.** Let $\nu, \nu_2$ be probability measures on $M$ with $\nu * \nu = \nu_2$, and let $F : M^{\mathbb N}\to\mathbb R$ be a.e.-strongly measurable for $\nu_2^{\otimes\mathbb N}$. Then
$$\int F(\mathrm{levyPairSum}\,z)\,d\nu^{\otimes\mathbb N}(z) = \int F\,d\nu_2^{\otimes\mathbb N}$$
(Bochner integrals).

**Assessment.**
- Truth: true, by `integral_map` for the measure-preserving map in #4.
- Junk values: $F\circ\mathrm{levyPairSum}$ is integrable under $\nu^{\otimes\mathbb N}$ exactly when $F$ is integrable under the image measure. So the non-integrable case is consistently $0 = 0$, and the statement does not rely on that convention.
- Hypotheses: `[IsProbabilityMeasure ν₂]` is redundant given `h`. `hF` is the standard hypothesis for change of variables.
- Vacuity: not vacuous, e.g. $\nu = N(0,1)$, $\nu_2 = N(0,2)$, and $F$ a bounded measurable function of finitely many coordinates.
- Standard fact: change of variables under a measure-preserving map. In MLMC terms, the coarse path built from pair-summed fine increments has the coarse law.

### 6. `levy_telescoping` (theorem)

**Rendering.** Let $(\nu_\ell)_{\ell\in\mathbb N}$ be probability measures on $M$ with $\nu_{\ell+1}*\nu_{\ell+1} = \nu_\ell$ for all $\ell$. Let $F_\ell : M^{\mathbb N}\to\mathbb R$ with $F_\ell \in L^1(\nu_\ell^{\otimes\mathbb N})$ for all $\ell$. Then for every $L$:
$$\mathbb E_{\nu_0^{\otimes\mathbb N}}[F_0] + \sum_{\ell<L} \mathbb E_{\nu_{\ell+1}^{\otimes\mathbb N}}\big[F_{\ell+1}(z) - F_\ell(\mathrm{levyPairSum}\,z)\big] = \mathbb E_{\nu_L^{\otimes\mathbb N}}[F_L].$$

**Assessment.**
- Truth: true.
  - Apply #4 and #5 with $\nu := \nu_{\ell+1}$ and $\nu_2 := \nu_\ell$.
  - This gives $F_\ell\circ\mathrm{levyPairSum} \in L^1(\nu_{\ell+1}^{\otimes\mathbb N})$, with the same mean as $F_\ell$ under $\nu_\ell^{\otimes\mathbb N}$.
  - Split each correction integral by linearity, which needs `hF`, and telescope.
  - I checked it exactly with a consistent 4-level family of discrete laws and a nonlinear $F_\ell$, for $L = 0,\dots,3$ (`levy_checks.out`).
- Vacuity: not vacuous, e.g. $\nu_\ell = N(0,2^{-\ell})$ (or $\nu_\ell = \delta_0$) with bounded measurable $F_\ell$.
- Junk values: none.
- Standard fact: the MLMC telescoping identity $\mathbb E P_L = \mathbb E P_0 + \sum_\ell \mathbb E[P_{\ell+1}-P_\ell]$, where the coarse path is driven by pair-summed fine increments of an infinitely divisible (Lévy) increment law.

### 7. `map_levyPath_levyPairSum` (theorem)

**Rendering.** Let $M$ be an additive commutative monoid with measurable addition and $\nu$ a probability measure. The image of $\nu^{\otimes\mathbb N}$ under $z\mapsto(S_{2m}(z))_{m\in\mathbb N}$ equals the image of $(\nu*\nu)^{\otimes\mathbb N}$ under $z\mapsto(S_m(z))_{m}$, where $S_n(z) = \sum_{i<n} z_i$.

**Assessment.**
- Truth: true.
  - $S_{2m}(z) = S_m(\mathrm{levyPairSum}\,z)$ by #3.
  - Then combine `map_map` with #4.
  - I checked the joint law of $(S_0,S_2,S_4,S_6)$ exactly (`levy_checks.out`).
- Junk values: both maps are measurable (finite sums of coordinates), so neither side is the junk zero measure.
- Vacuity: not vacuous, e.g. $\nu = N(0,1)$.
- Standard fact: a random walk observed at even times is a random walk whose step law is the convolved one (subsampling a Lévy path).

### 8. `sum_exponential_periods` (theorem)

**Rendering.** Setting:
- $(\Omega,\mu)$ is a probability space, $T > 0$ and $n \ge 1$ ($n \in \mathbb N$, cast to ℝ).
- $X_0,\dots,X_{n-1}$ are real random variables, each with law $\mathrm{Exp}(n/T)$.
  - Mathlib's `expMeasure r` is `gammaMeasure 1 r`, with density $r e^{-rx}\mathbf 1_{x\ge0}$, i.e. $r$ is the rate.
- The $X_i$ are pairwise independent.

Conclusions:
1. $\int \sum_i X_i\,d\mu = T$.
2. $\mathrm{Var}(\sum_i X_i) = T^2/n$.
3. For every $\delta > 0$: $\mu\{\delta \le |\sum_i X_i - T|\} \le \mathrm{ofReal}\big(T^2/(n\delta^2)\big)$.

**Assessment.**
- Truth: true.
  - Each $X_i$ has mean $T/n$ and variance $T^2/n^2$.
  - Pairwise independence makes the $X_i$ uncorrelated, so variances add.
  - Then apply Chebyshev (`meas_ge_le_variance_div_sq`).
  - Sympy moment computations and exact Gamma-cdf tail probabilities agree (`exponential_checks.out`).
- Vacuity: not vacuous, e.g. $\mathbb R^n$ with $\mathrm{Exp}(n/T)^{\otimes n}$ and the coordinate maps.
- Junk values: none.
- Hypotheses:
  - `hT` is redundant: `hX` and `hn` force $n/T > 0$, because `expMeasure r` is the zero measure for $r \le 0$ and cannot be the law of a random variable under a probability measure.
  - `hn` is needed: with $n = 0$ the sum is $0 \ne T$.
  - Only pairwise independence is assumed, which is weaker than i.i.d.
- Standard fact: the moments of an Erlang/Gamma$(n, n/T)$ sum, plus Chebyshev's inequality.

### 9. `exponential_periods_clt` (theorem)

**Rendering.** Setting:
- $(\Omega,P)$ and $(\Omega',P')$ are probability spaces.
- $(E_k)_{k\in\mathbb N}$ are mutually independent (`iIndepFun`), each with law $\mathrm{Exp}(1)$.
- $Y \sim N(0,1)$ on $\Omega'$, and $T > 0$.

Conclusions:
1. For all $n \ge 1$ and all $k$: $(T/n)E_k \sim \mathrm{Exp}(n/T)$.
2. $\frac{\sqrt n}{T}\big(\sum_{k<n}\frac Tn E_k - T\big) \to Y$ in distribution as $n\to\infty$.
   - Mathlib's `TendstoInDistribution` means every term and $Y$ are a.e.-measurable and the laws converge weakly in `ProbabilityMeasure ℝ`.

**Assessment.**
- Truth: true.
  - (1) Scaling an $\mathrm{Exp}(1)$ variable by $c > 0$ gives $\mathrm{Exp}(1/c)$.
  - (2) For $n \ge 1$ the expression equals $(\sum_{k<n}E_k - n)/\sqrt n$ (sympy check), so the Lindeberg–Lévy CLT applies with mean 1 and variance 1. The $n = 0$ term is the constant 0, which does not affect the limit.
  - The exact Kolmogorov distance to $N(0,1)$, computed via the Gamma cdf, is $\approx 0.133/\sqrt n$ (`exponential_checks.out`).
- Hypotheses: `hT` is needed. With $T = 0$ the sequence is identically $0$; with $T < 0$, conclusion (1) fails.
- Vacuity: not vacuous, e.g. $\Omega = \mathbb R^{\mathbb N}$ with $\mathrm{Exp}(1)^{\otimes\mathbb N}$, and $\Omega' = \mathbb R$ with $N(0,1)$.
- Junk values: none.
- Standard fact: the classical CLT applied to a sum of $n$ exponential waiting times of mean $T/n$.

### 10. `hatNodal` (def)

**Rendering.** $\mathrm{hatNodal}\,j\,i = \delta_{ij} \in \{0,1\}$: the value of the P1 hat function $\varphi_j$ at node $i$.

### 11. `feStiffness` (def)

**Rendering.**
$$\mathrm{feStiffness}(N,h,c,u,j) = \sum_{e=0}^{N-1} h\,c\big((e+\tfrac12)h\big)\,\frac{u_{e+1}-u_e}{h}\,\frac{\varphi_j(e+1)-\varphi_j(e)}{h}$$
(the $\tfrac12$ is the real number $0.5$, confirmed in Lean). This is row $j$ of the P1 FE bilinear form $\int c\,u_h'\varphi_j'$ on the uniform mesh $x_e = eh$, using one-point midpoint quadrature on each element.

### 12. `feLoad` (def)

**Rendering.** $\sum_{e<N} h\,f\big((e+\tfrac12)h\big)\,\frac{\varphi_j(e+1)+\varphi_j(e)}{2}$. This is midpoint quadrature for $\int f\varphi_j$: $\varphi_j$ is linear on each element, so its midpoint value is the average of its nodal values.

### 13. `fe_eq_centralDiff` (theorem)

**Rendering.** For naturals $1 \le j < N$, real $h \ne 0$, and arbitrary $c, f : \mathbb R\to\mathbb R$ and $u : \mathbb N\to\mathbb R$:
$$\mathrm{feStiffness}(N,h,c,u,j) = h\cdot\frac{-\big(c_{j+1/2}(u_{j+1}-u_j) - c_{j-1/2}(u_j-u_{j-1})\big)}{h^2}$$
and
$$\mathrm{feLoad}(N,h,f,j) = h\,\frac{f((j-\tfrac12)h) + f((j+\tfrac12)h)}{2},$$
where $c_{j\pm1/2} = c((j\pm\tfrac12)h)$ in real arithmetic. $u_{j-1}$ uses ℕ-subtraction, which is safe because $j \ge 1$.

**Assessment.**
- Truth: true. Only the elements $e = j-1$ and $e = j$ contribute:
  - $e = j-1$: the $\varphi_j$ difference is $+1$ and the average is $\tfrac12$.
  - $e = j$: the difference is $-1$ and the average is $\tfrac12$.
  - Every other element gives 0. Both are in range because $1 \le j < N$.
  - Sympy verified every interior row for $N \le 7$ (`fem_checks.out`).
- Hypotheses: `hh` is redundant. At $h = 0$ both sides are $0$ under $x/0 = 0$ (also checked).
- Vacuity: not vacuous, e.g. $N=2$, $j=1$, $h=\tfrac12$.
- Junk values: none.
- Standard fact: on a uniform 1-D mesh, P1 finite elements with midpoint quadrature give $h$ times the conservative (flux-form) three-point finite-difference operator for $-(cu')'$. The load is $h$ times the average of $f$ at the two adjacent midpoints.

### 14. `rates_of_pathwise_random` (theorem)

**Rendering.** Setting:
- $(\Omega,\mu)$ is a probability space.
- $P$ and $P_\ell$ ($\ell\in\mathbb N$) are a.e.-strongly measurable real random variables.
- $K \in L^2(\mu)$, with no sign condition.
- $e : \mathbb N\to\mathbb R$, with no sign condition.
- For each $\ell$, almost surely $|P - P_\ell| \le K\,e_\ell$.

Then for every $\ell$:
- (a) $P_\ell - P \in L^1$;
- (b) $|\mathbb E[P_\ell - P]| \le \mathbb E[K]\,e_\ell$;
- (c) $P_{\ell+1}-P_\ell \in L^2$;
- (d) $\mathrm{Var}(P_{\ell+1}-P_\ell) \le \mathbb E[(P_{\ell+1}-P_\ell)^2]$;
- (e) $\mathbb E[(P_{\ell+1}-P_\ell)^2] \le \mathbb E[K^2]\,(e_{\ell+1}+e_\ell)^2$.

**Assessment.**
- Truth: true.
  - The hypothesis forces $K e_\ell \ge 0$ a.e.
  - (a): $|P_\ell - P| \le |K|\,|e_\ell|$, which is in $L^1$ because $L^2 \subset L^1$ on a probability space.
  - (b): $|\int (P_\ell-P)| \le \int K e_\ell = e_\ell\,\mathbb E K$.
  - (c) and (e): a.e. $|P_{\ell+1}-P_\ell| \le K(e_{\ell+1}+e_\ell)$. This bound is nonnegative, so squaring it and integrating gives (e).
  - (d): variance is at most the second moment (`variance_le_expectation_sq`).
  - 2000 random finite examples, 1807 of them with negative $e_\ell$, gave no violations (`rates_checks.out`).
- Vacuity: not vacuous, e.g. $P = P_\ell = 0$, $K = 1$, $e = 0$; or $P_\ell = P + 2^{-\ell}KU$ with $|U|\le1$.
- Junk values: none.
- Standard fact: the Cliffe–Giles–Scheichl–Teckentrup (2011) argument. A pathwise error bound with a random constant $K\in L^2$ gives the MLMC weak rate $\alpha$ and variance rate $\beta = 2\alpha$.

### 15. `elliptic_rates_random` (theorem)

**Rendering.** The setting of #14 with $e_\ell = h_\ell^2$ and $h_\ell = 2^{-(\ell+1)}$. For all $\ell$:
- $|\mathbb E[P_\ell-P]| \le \mathbb E[K]\,h_\ell^2$;
- variance $\le$ second moment;
- $\mathbb E[(P_{\ell+1}-P_\ell)^2] \le 25\,\mathbb E[K^2]\,(2^{-(\ell+2)})^4 = 25\,\mathbb E[K^2]\,h_{\ell+1}^4$.

**Assessment.**
- Truth: true, as a corollary of #14, because $(h_{\ell+1}^2 + h_\ell^2)^2 = (5h_{\ell+1}^2)^2 = 25h_{\ell+1}^4$. I checked this exactly for $\ell < 60$.
- Vacuity: not vacuous (same instances as #14).
- Junk values: none.
- Standard fact: the rates $\alpha = 2$, $\beta = 4$ (in $h$) for FE approximations of smooth functionals of elliptic PDEs with random coefficients.

### 16. `not_ae_abs_gaussian_sq_mul_le` (theorem)

**Rendering.** Let $Z$ be a real random variable on $(\Omega,\mu)$ with law $N(0,1)$. No probability instance is assumed, but `HasLaw` forces $\mu(\Omega) = 1$. For every $e \ne 0$ and every $K\in\mathbb R$: it is not the case that $|Z^2 e| \le K$ holds $\mu$-a.e.

**Assessment.**
- Truth: true.
  - $\mu(|Z^2e| > K) \ge P(|Z| > \sqrt{K^+/|e|}) > 0$, because the Gaussian density is positive everywhere.
  - For $K < 0$ the event is the whole space.
  - mpmath tail values are in `rates_checks.out`.
- Vacuity: not vacuous, e.g. $\Omega = \mathbb R$, $\mu = N(0,1)$, $Z = \mathrm{id}$, $e = 1$.
- Junk values: none. If $\mu$ were $0$ the negated statement would fail, but `HasLaw` rules that out.
- Standard fact: the Gaussian distribution is unbounded. So no deterministic pathwise constant can bound an error of the form $e\,Z^2$, which is why #14 uses a random $K\in L^2$.

### 17. `spdeD1` (def)

**Rendering.** The central first difference on a ℤ-indexed grid: $D_1p_j = (p_{j+1}-p_{j-1})/(2h)$.

### 18. `spdeD2` (def)

**Rendering.** The central second difference: $D_2p_j = (p_{j+1}-2p_j+p_{j-1})/h^2$.

### 19. `spdeNoiseOp` (def)

**Rendering.** $(Bp)(x) = -\sqrt\rho\,p'(x)$. Mathlib's `deriv` is $0$ where $p$ is not differentiable, and `Real.sqrt` $\rho = 0$ for $\rho < 0$.

### 20. `spdeMilsteinStep` (def)

**Rendering.**
$$p(x) + \big(-\mu p'(x) + \tfrac12 p''(x)\big)k + (Bp)(x)\,\Delta M + \tfrac12\,(B(Bp))(x)\,(\Delta M^2 - k).$$
This is one Milstein step of size $k$ for the SPDE $dv = (-\mu\partial_x + \tfrac12\partial_{xx})v\,dt - \sqrt\rho\,\partial_x v\,dM_t$.

### 21. `spdeMilsteinStep_eq` (theorem)

**Rendering.** For $\rho \ge 0$, $k \ge 0$ and arbitrary $\mu, Z, p, x$: `spdeMilsteinStep` with $\Delta M = \sqrt k\,Z$ equals
$$p(x) - (\mu k + \sqrt{\rho k}\,Z)\,p'(x) + \frac{(1-\rho)k + \rho k Z^2}{2}\,p''(x).$$

**Assessment.**
- Truth: true.
  - $B(Bp) = (-\sqrt\rho)^2 p'' = \rho p''$ for every $p$, because `deriv_const_mul_field` needs no differentiability.
  - $(\sqrt k Z)^2 = kZ^2$ and $\sqrt\rho\sqrt k = \sqrt{\rho k}$ when $\rho, k \ge 0$.
  - Sympy verified the identity (`spde_checks.out`).
- Hypotheses: both are needed. $\rho = -\tfrac12$ or $k = -\tfrac13$ gives numerical counterexamples under Lean's $\sqrt{\cdot}$ convention.
- Junk values: none. The identity holds for every $p$; for non-differentiable $p$ both sides use the same junk derivatives, and the smooth case is the meaningful one.
- Vacuity: not vacuous.
- Standard fact: the Milstein scheme for the Giles–Reisinger (2012) credit-portfolio SPDE.

### 22. `spdeScheme` (def)

**Rendering.**
$$p_j - \frac{\mu k + \sqrt{\rho k}Z}{2h}(p_{j+1}-p_{j-1}) + \frac{(1-\rho)k + \rho k Z^2}{2h^2}(p_{j+1}-2p_j+p_{j-1}).$$

### 23. `spdeScheme_eq_milstein` (theorem)

**Rendering.** For $\rho, k \ge 0$ and arbitrary $\mu, h, Z$, $p : \mathbb Z\to\mathbb R$, $j\in\mathbb Z$:
- (i) the scheme equals $p_j - (\mu k + \sqrt{\rho k}Z)D_1p_j + \frac{(1-\rho)k+\rho kZ^2}{2}D_2p_j$;
- (ii) the scheme equals $p_j + (-\mu D_1p_j + \tfrac12 D_2p_j)k + (-\sqrt\rho D_1p_j)(\sqrt kZ) + \tfrac12(\rho D_2p_j)((\sqrt kZ)^2 - k)$.

Form (ii) is the Milstein step of #20 with $\partial_x \to D_1$ and $B^2 \to \rho D_2$.

**Assessment.**
- Truth: true, by algebra.
  - (i) needs no hypotheses.
  - (ii) uses $\rho, k \ge 0$.
  - Sympy verified both; both also hold at $h = 0$ in the $x/0 = 0$ convention (`spde_checks.out`).
- Vacuity: not vacuous.
- Junk values: none.
- Standard fact: the central-difference discretisation of the Milstein step (Giles–Reisinger 2012).

### 24. `bbPath` (def)

**Rendering.** A recursive definition $W^\ell_i$, where $r$ is a rounding map:
- Level 0: node $0 \mapsto 0$. Every other node maps to $r(\sqrt T Z_0)$; the intended node is $1$, i.e. $W(T)$.
- Level $\ell+1$, even $i$: copy the level-$\ell$ value at node $i/2$.
- Level $\ell+1$, odd $i$: $r\big(\frac{W^\ell_{\lfloor i/2\rfloor}+W^\ell_{\lfloor i/2\rfloor+1}}{2} + \frac{\sqrt{T/2^\ell}}{2}Z_{2^\ell+\lfloor i/2\rfloor}\big)$.

This is Brownian-bridge midpoint refinement with rounding $r$. Level $\ell$ uses $Z_0,\dots,Z_{2^\ell-1}$. Values at nodes $i > 2^\ell$ are off-grid junk.

Modelling check: with $r = \mathrm{id}$, the covariance on the grid is exactly $\min(s,t)$ for levels 0 to 3 (`bridge_checks.out`).

### 25. `bbPath_nested` (theorem)

**Rendering.** For all $r, T, Z, \ell, m, i$: $W^{\ell+m}_{2^m i} = W^\ell_i$.

**Assessment.**
- Truth: true, by induction on $m$ through the even branch; it holds for all $i$. Checked numerically (`bridge_checks.out`).
- Vacuity: there are no hypotheses.
- Junk values: none.
- Standard fact: the dyadic Brownian-bridge construction is nested, i.e. consistent across levels.

### 26. `bbPath_congr` (theorem)

**Rendering.** If $Z_1(n) = Z_2(n)$ for all $n < 2^\ell$, then the level-$\ell$ paths agree at every node $i \le 2^\ell$.

**Assessment.**
- Truth: true, by induction on $\ell$. An odd $i \le 2^{\ell+1}-1$ uses coarse nodes $\le 2^\ell$ and input index $2^\ell + \lfloor i/2\rfloor \le 2^{\ell+1}-1$.
- Hypotheses: $i \le 2^\ell$ is needed. At $i = 2^\ell+1$ the paths can differ (observed in `bridge_checks.out`).
- Vacuity: not vacuous, e.g. inputs that differ only at indices $\ge 2^\ell$.
- Junk values: none.
- Standard fact: level $\ell$ depends only on the first $2^\ell$ normals.

### 27. `bb_telescoping` (theorem)

**Rendering.** For any $Z$, any family $F_\ell : \mathbb R^{\mathrm{Fin}(2^\ell+1)}\to\mathbb R$, and any $L$:
$$F_0(W^0) + \sum_{\ell<L}\big[F_{\ell+1}(W^{\ell+1}) - F_\ell\big((W^{\ell+1}_{2i})_{i\le2^\ell}\big)\big] = F_L(W^L).$$
Here $2i$ is ℕ multiplication of the cast index (confirmed in Lean).

**Assessment.**
- Truth: true. By the definition (or #25), $W^{\ell+1}_{2i} = W^\ell_i$, and the sum then telescopes.
  - It is a pathwise identity, so no integrability is needed.
  - I checked it exactly for $L \le 4$ with a nonlinear $F$ (`bridge_checks.out`).
- Vacuity: there are no hypotheses.
- Junk values: none.
- Standard fact: MLMC telescoping in which the coarse path is the even-node restriction of the fine path.

### 28. `vpInputs` (def)

**Rendering.** $Z_n = G(I_n)$ for $n < m$, and $0$ otherwise.

### 29. `vpPath` (def)

**Rendering.** The level-$\ell$ path `bbPath (rnd ℓ) T (vpInputs (G ℓ) I) ℓ` on nodes $i \le 2^\ell$. It uses the level-$\ell$ rounding `rnd ℓ` and the level-$\ell$ input map `G ℓ`, applied to integer inputs $I : \mathrm{Fin}\,m\to\mathbb N$.

### 30. `vpPath_castLE` (theorem)

**Rendering.** If $2^\ell \le m$, then the level-$\ell$ path built from $I$ equals the level-$\ell$ path built from the first $2^\ell$ entries of $I$ (an equality of functions on $\mathrm{Fin}(2^\ell+1)$).

**Assessment.**
- Truth: true, from #26: the two input sequences agree on $n < 2^\ell$. Checked on 200 random cases.
- Vacuity: not vacuous, e.g. $m = 2^\ell$ or larger.
- Junk values: none.

### 31. `integral_vpCoarse` (theorem)

**Rendering.** Let $\nu$ be a probability measure on ℕ. For any $F : \mathbb R^{\mathrm{Fin}(2^\ell+1)}\to\mathbb R$:
$$\int F(\mathrm{vp}_\ell(I))\,d\nu^{\otimes 2^{\ell+1}}(I) = \int F(\mathrm{vp}_\ell(I))\,d\nu^{\otimes 2^\ell}(I).$$

**Assessment.**
- Truth: true.
  - By #30, the level-$\ell$ path factors through projection onto the first $2^\ell$ coordinates.
  - That projection pushes $\nu^{\otimes2^{\ell+1}}$ forward to $\nu^{\otimes2^\ell}$.
  - ℕ carries the σ-algebra $\top$ and $\mathrm{Fin}\,k\to\mathbb N$ is countable, so every function is measurable. Hence `integral_map` applies with no hypothesis on $F$.
  - I checked it exactly for $\nu$ on $\{0,1,2\}$ and $\ell \le 2$.
- Junk values: none. Integrability holds on both sides or on neither, so the non-integrable case is consistently $0 = 0$.
- Vacuity: not vacuous.
- Standard fact: the coarse level's law is unchanged by the extra fine inputs (the level-$\ell$ path depends only on the first $2^\ell$ inputs).

### 32. `vp_telescoping` (theorem)

**Rendering.** Assume $F_\ell\circ\mathrm{vp}_\ell \in L^1(\nu^{\otimes2^\ell})$ for every $\ell$. Then for every $L$:
$$\mathbb E_{\nu^{\otimes1}}[F_0(\mathrm{vp}_0)] + \sum_{\ell<L}\mathbb E_{\nu^{\otimes2^{\ell+1}}}\big[F_{\ell+1}(\mathrm{vp}_{\ell+1}(I)) - F_\ell(\mathrm{vp}_\ell(I))\big] = \mathbb E_{\nu^{\otimes2^L}}[F_L(\mathrm{vp}_L)].$$
The coarse term inside each correction is recomputed at coarse precision from the same inputs.

**Assessment.**
- Truth: true.
  - Integrability transfers along the projection.
  - Apply #31 to each coarse term, then telescope.
  - Checked exactly for $L \le 3$.
- Vacuity: not vacuous, e.g. bounded $F$.
- Junk values: none. `hF` is needed for linearity.
- Standard fact: MLMC telescoping with variable- or reduced-precision paths, which stays exact when the coarse path is recomputed at its own precision.

### 33. `roundFixed_sum_inconsistent` (theorem)

**Rendering.** Write $\mathrm{rF}_d(z) = 2^{-d}\,\mathrm{round}(2^d z)$, where Mathlib's $\mathrm{round}(z) = \lfloor z + \tfrac12\rfloor$ (ties go up). For $0 < x < \tfrac1{20}$ and $\tfrac3{20} < y < \tfrac15$:
- (i) $\mathrm{rF}_1(x+y) = 0$;
- (ii) $\mathrm{rF}_1(\mathrm{rF}_2x) + \mathrm{rF}_1(\mathrm{rF}_2y) = \tfrac12$;
- (iii) $\mathrm{rF}_1(\mathrm{rF}_2x + \mathrm{rF}_2y) = \tfrac12$.

**Assessment.**
- Truth: true.
  - $\mathrm{rF}_2x = 0$ and $\mathrm{rF}_2y = \tfrac14$.
  - $\mathrm{rF}_1(\tfrac14) = \tfrac12\,\mathrm{round}(\tfrac12) = \tfrac12$.
  - $2(x+y)\in(0.3, 0.5)$, so $\mathrm{rF}_1(x+y) = 0$.
  - Checked on 20000 random rational points and at near-boundary points (`roundfixed_checks.out`); Lean confirms `round (1/2 : ℝ) = 1`.
- Vacuity: not vacuous, e.g. $x = \tfrac1{40}$, $y = \tfrac7{40}$.
- Junk values: none, but the statement depends on the tie rule. (ii) and (iii) hinge on the tie at $\tfrac14 \mapsto \tfrac12$. Under round-half-to-even all three quantities would be $0$ on this box.
- Standard fact: double rounding is not consistent across precisions (rounding fine-precision results to coarse precision differs from rounding directly at coarse precision). This motivates recomputing the coarse path from the inputs, as `vpPath` does.

### 34. `roundFixed` (def, from `MlmcLean.RoundingError`)

**Rendering.** $\mathrm{roundFixed}(e,d,x) = 2^{e-d}\,\mathrm{round}(x/2^{e-d})$, with an integer exponent (`zpow`). This rounds $x$ to the nearest multiple of $2^{e-d}$, with ties going up.
