# Blind read-back report: packet M5 (SDE miscellany)

| Field | Value |
|---|---|
| Date | 2026-09-29 |
| Packet | `readback/round11/packet_M5_sde_misc.lean` |
| Declarations audited | 23 (20 theorems and 3 definitions, including the appended `smoothCDF`). For #13 `eulerCubic_bounded` and #17 `tamedCubic_bounded` the packet printed no conclusion; the exact statements were supplied afterwards by the coordinator (point 1) and are audited here. |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round11/work_M5/` (`antithetic_taylor.py`, `call_payoff.py`, `call_variance.py`, `euler_tamed.py`, `cubic_bounded.py`, `smooth_cdf.py`, `density_recovery.py`, each with its `.out`; Lean scratch files `scratch_packet.lean`/`.out`, `prove_cubic_bounded.lean`/`.out`, `check_missing.lean`/`.out`, `check_missing2.lean`/`.out`) |
| Toolchain | Lean v4.33.1, Mathlib 0df444a. The scratch copy of the packet (all proofs `sorry`, with the two supplied statements) elaborates without errors (`scratch_packet.out`). |

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `abs_midpoint_sub_avg_le_fderiv` | theorem | true (sharp) | no | no |
| 2 | `abs_antithetic_le_fderiv` | theorem | true (sharp) | no | no |
| 3 | `abs_antithetic_le_midpoint` | theorem | true | no | no |
| 4 | `variance_antithetic_le_fderiv` | theorem | true | no | no |
| 5 | `variance_antithetic_le_midpoint` | theorem | true | no | no |
| 6 | `abs_call_antithetic_le` | theorem | true (sharp) | no | no |
| 7 | `variance_call_antithetic_le` | theorem | true | no | no. The hypothesis `hdens` is strong and non-standard (see point 2 below) |
| 8 | `variance_call_antithetic_le_holder` | theorem | true | no | no |
| 9 | `eulerDriftStep` | def | n/a (explicit Euler drift step) | n/a | n/a |
| 10 | `tamedDriftStep` | def | n/a (tamed drift step) | n/a | n/a (for $h<0$ the denominator can be $0$, but it is never used there) |
| 11 | `eulerCubic_growth` | theorem | true | no | no |
| 12 | `eulerCubic_tendsto_atTop` | theorem | true | no | no |
| 13 | `eulerCubic_bounded` (statement supplied by the coordinator) | theorem | true (sharp; proved in my scratch file) | no | no |
| 14 | `abs_tamedDrift_lt` | theorem | true | no | no |
| 15 | `abs_tamedDriftStep_sub_eulerDriftStep_le` | theorem | true | no | no |
| 16 | `tamedDriftStep_iterate_bounded` | theorem | true (also proved in my scratch file) | no | no |
| 17 | `tamedCubic_bounded` (statement supplied by the coordinator) | theorem | true (proved in my scratch file) | no | no |
| 18 | `abs_smoothCDF_sub_le_of_bounded` | theorem | true | no | no |
| 19 | `tendsto_smoothCDF_of_bounded` | theorem | true | no | no |
| 20 | `tendsto_smoothCDF_of_continuous` | theorem | true | no | no |
| 21 | `tendsto_density_multidim` | theorem | true | no | no |
| 22 | `tendsto_density_euclidean` | theorem | true | no | no |
| 23 | `smoothCDF` (appended, from `MlmcLean.SDEExtras`) | def | n/a (smoothed CDF $\mathbb E[g((x-P)/\delta)]$) | n/a | n/a ($\delta=0$ gives the junk value $g(0)$, but no statement uses $\delta\le 0$) |

## Main points for a human auditor

1. **Packet defect, now resolved: two statements were printed without a conclusion.** In the packet,
   `eulerCubic_bounded` and `tamedCubic_bounded` read `theorem … (n : ℕ) : := sorry`.
   - **Cause.** The coordinator reports a packet-generator bug: a conclusion line that starts with `|…|` and contains
     `fun … =>` was taken for a match arm.
   - **Statements supplied.** The coordinator then sent the exact statements:
     - `eulerCubic_bounded`: `|(eulerDriftStep (fun S => -S ^ 3) h)^[n] S| ≤ |S|`
     - `tamedCubic_bounded`: `|(tamedDriftStep (fun S => -S ^ 3) h)^[n] S| ≤ max |S| 1`

     Both are word-for-word the conclusions I had guessed.
   - **Verdict: both are true.** I proved both in my own scratch file, `prove_cubic_bounded.lean`, which copies the
     packet definitions. It also proves #16 as a helper. `#print axioms` lists only `propext`, `Classical.choice` and
     `Quot.sound` (`prove_cubic_bounded.out`). Numerical checks: `cubic_bounded.out`.
   - **Sharpness and necessity.** The Euler bound is attained at $hS^2=2$, and the threshold $2$ is sharp. The
     "$\max(\cdot,1)$" in the tamed bound cannot be dropped: $S=1/10$, $h=1000$ gives $T(S)=-2/5$. Both need
     $0\le h$ (the counterexamples are proved by `norm_num` in the same file).
   - **Build status.** Before the statements arrived, I could not recover them with `#check`: `MlmcLean.SDEMisc` has
     no `.olean` (`check_missing2.out`), and its declarations cannot be reached through `import MlmcLean`
     (`check_missing.out`). The coordinator says this is only because the full build is deferred, and that the module
     is registered in the root module and in `scripts/AxiomCheck.lean`. Under the blind rules I have not checked
     either claim. After the deferred build, confirm that `lake build` and the axiom check actually cover the module.
2. **`hdens` in `variance_call_antithetic_le` is a strong and non-standard modelling hypothesis.** It says
   $\mathrm{Law}(|A-B|,\tfrac{A+B}{2})\le \mathrm{Law}(|A-B|)\otimes \rho_0\,\mathrm{Leb}$. In words: given $|A-B|$,
   the midpoint has a conditional density of at most $\rho_0$. The hypothesis can be satisfied (example below), and
   it makes the $O(h^{3/2})$ bound true. However, it is an assumption on the joint law of the fine and antithetic
   *approximations*, not a consequence of assumptions on the SDE. It also forces $\rho_0>0$. The Hölder version (#8)
   is closer to the usual argument.
3. **`h ^ (3/2 : ℝ)` is `Real.rpow`, so it equals $0$ in Lean for $h<0$.** This is proved in `scratch_packet.lean`
   ($\cos(3\pi/2)=0$). For $h<0$, `h2` then forces $A=B$ a.s., and #7 is still true in that case. So the theorem does
   not depend on the junk value, but only $h>0$ is a meaningful reading.
4. **#1–#5 have no hypothesis $0\le K$.** This is harmless: `hf'` forces $K\ge0$ unless $E=\{0\}$, and when
   $E=\{0\}$ every one of these statements is trivially true (both sides are $0$, or the right-hand side is
   $\ge 0$ by `h1`–`h3`).
5. **`tamedDriftStep` divides by $1+h|b(S)|$.** For $h<0$ this can be $0$, where Lean returns $x/0=0$. Every theorem
   that uses the step assumes $0\le h$, so the junk value is never reached.
6. **The smoothed-CDF limits (#19, #20) converge to $P(P<x)$, with a strict inequality.** The no-atom hypothesis `hx`
   is genuinely needed unless $g(0)=0$: at an atom the limit is $P(P<x)+g(0)P(P=x)$ (`smooth_cdf.out`).
   **The density limits (#21, #22) genuinely need $\rho$ to be continuous at $x$.** At a jump the limit is
   $\int_{z\le0}g\neq\rho(x)$ (`density_recovery.out`). The kernel orientation $g((x-P)/\delta)$ is handled
   correctly, including for non-symmetric $g$.
7. **All the constants follow from the pointwise bounds** together with $(x+y)^2\le 2x^2+2y^2$:
   - $K/8$ (#1): sharp; equality for a quadratic.
   - $K/4$ (#2): sharp.
   - $|a-b|/4$ (#6): sharp.
   - $2L^2D_1+K^2D_2/2$ (#4) and $2L^2D_1+K^2D_2/32$ (#5).
   - $2D_1h^2+\rho_0D_2h^{3/2}/8$ (#7).

   No statement is false, none is vacuous, and none depends on a junk value. This includes the two supplied
   statements, #13 and #17.
8. **Taming, in one contrast.** Explicit Euler for the drift $-S^3$ blows up exactly when $hS^2>2$ (#11, #12) and
   is non-expanding when $hS^2\le2$ (#13). The tamed step is bounded by $\max(|S|,1)$ for every $h\ge0$ (#16, #17).
   Numerically, with $h=10$ and $S=3$, six Euler steps reach $|x|\approx4\cdot10^{710}$, while six tamed steps give
   $|x|\approx0.078$ (`cubic_bounded.out`).

---

## Per-declaration sections

Throughout, $m:=\mathrm{midpoint}_{\mathbb R}(a,b)=\tfrac12(a+b)$ in Mathlib. `variance X μ` is
$\big(\int^-\|X-\mu[X]\|_e^2\,d\mu\big)$ converted to a real (`toReal`). This equals the usual variance when
$X\in L^2$, and is $0$ when the lower integral is $\infty$. `Real.HolderConjugate p q` means $p,q>0$ and
$p^{-1}+q^{-1}=1$, which implies $p,q>1$. Measure order `≤` is setwise ($\mu_1\le\mu_2\iff\forall s,\ \mu_1 s\le\mu_2 s$).

### 1. `abs_midpoint_sub_avg_le_fderiv` (theorem)

**Rendering.** Setting:
- $E$ is a real normed space (not assumed complete or finite-dimensional).
- $f:E\to\mathbb R$ and $f':E\to L(E,\mathbb R)$, the continuous linear functionals with the operator norm.
- $K\in\mathbb R$, with no sign condition.

Hypotheses:
- (hf) For every $x$, $f$ is Fréchet-differentiable at $x$ with derivative $f'(x)$.
- (hf′) For all $x,y$, $\|f'(y)-f'(x)\|\le K\|y-x\|$.

Conclusion: for all $a,b\in E$,
$$\Big|f\big(\tfrac{a+b}2\big)-\tfrac{f(a)}2-\tfrac{f(b)}2\Big|\le \tfrac K8\|a-b\|^2 .$$

**Assessment.**
- **Truth: true.** Put $v=(a-b)/2$, so $a=m+v$ and $b=m-v$. Then
  $\tfrac{f(a)+f(b)}2-f(m)=\tfrac12\int_0^1\big(f'(m+tv)-f'(m-tv)\big)v\,dt$. The derivative difference has norm at
  most $2tK\|v\|$, so the left-hand side is at most $\tfrac K2\|v\|^2=\tfrac K8\|a-b\|^2$. Alternatively, Taylor-expand
  at $m$ with remainder $\le\tfrac K2\|a-m\|^2$ for each end point.
- **Sharpness.** The bound is attained by $f(x)=\tfrac K2\|x\|^2$, and $0.99\cdot K/8$ already fails
  (`antithetic_taylor.out`). In 20 000 random tests in $\mathbb R^2$ with
  $f=\sin(u\cdot x)+\log\cosh(v\cdot x)+\tfrac12x^\top Qx$ there were no violations; the largest ratio was $0.985$.
- **Vacuity: none.** Example: $E=\mathbb R$, $f=\sin$, $K=1$.
- **Junk values: none.**
- **Hypotheses.** No hypothesis $K\ge0$, but (hf′) forces it whenever $E\ne0$; when $E=0$ both sides are $0$.
- **Standard fact.** This is the second-difference (midpoint) estimate for functions with a Lipschitz gradient
  (Taylor/descent lemma). It is the basic deterministic lemma of antithetic MLMC (Giles–Szpruch 2014).

### 2. `abs_antithetic_le_fderiv` (theorem)

**Rendering.** Same $E,f,f',K$, (hf) and (hf′) as #1. Conclusion: for all $a,b,c\in E$,
$$\Big|\tfrac{f(a)+f(b)}2-f(c)\Big|\le\|f'(c)\|\,\|m-c\|+\tfrac K4\big(\|a-c\|^2+\|b-c\|^2\big).$$

**Assessment.**
- **Truth: true.** Taylor-expand at $c$: $f(a)=f(c)+f'(c)(a-c)+R_a$ with $|R_a|\le\tfrac K2\|a-c\|^2$, and likewise
  for $b$. Averaging gives $f'(c)(m-c)+\tfrac12(R_a+R_b)$.
- **Sharpness.** Equality holds for $f=\tfrac K2\|x\|^2$ with $c=m$. Random tests found no violations; the largest
  ratio was $0.9995$.
- **Vacuity: none. Junk values: none.**
- **Standard fact.** First-order Taylor expansion with a Lipschitz-gradient remainder; the antithetic difference bound
  of Giles–Szpruch.

### 3. `abs_antithetic_le_midpoint` (theorem)

**Rendering.** As #2, plus $L\in\mathbb R$ with (hL) $\|f'(x)\|\le L$ for every $x$. Conclusion: for all $a,b,c$,
$$\Big|\tfrac{f(a)+f(b)}2-f(c)\Big|\le L\|m-c\|+\tfrac K8\|a-b\|^2 .$$

**Assessment.**
- **Truth: true.** Split the left-hand side as $\big[\tfrac{f(a)+f(b)}2-f(m)\big]+[f(m)-f(c)]$. The first term is at
  most $\tfrac K8\|a-b\|^2$ by #1. The second is at most $L\|m-c\|$ by the mean-value inequality.
- **Numerics.** Random tests with $Q=0$ (so that $L=\|u\|+\|v\|$ is a valid global bound) found no violations; the
  largest ratio was $0.987$.
- **Vacuity: none** ($f=\sin$, $L=K=1$). **Junk values: none.**
- **Standard fact.** The Giles–Szpruch inequality $|\bar P-P(c)|\le L_1|\bar a-c|+\tfrac{L_2}{8}|a-b|^2$ for
  payoffs with bounded first and Lipschitz first derivative.

### 4. `variance_antithetic_le_fderiv` (theorem)

**Rendering.** Setting:
- $(\Omega,\mu)$ is a probability space.
- $E$ carries a σ-algebra containing the open sets (`OpensMeasurableSpace`; not assumed Borel or separable).
- $f,f',K$ satisfy (hf) and (hf′), and $\|f'\|\le L$.
- $A,B,C:\Omega\to E$ are measurable, and $D_1,D_2,h\in\mathbb R$ are arbitrary.

Hypotheses:
- $\|m(A,B)-C\|^2$, $\|A-C\|^4$ and $\|B-C\|^4$ are $\mu$-integrable.
- $\mathbb E\|m(A,B)-C\|^2\le D_1h^2$.
- $\mathbb E\|A-C\|^4\le D_2h^2$ and $\mathbb E\|B-C\|^4\le D_2h^2$.

Conclusion:
$$\mathrm{Var}\Big[\tfrac{f(A)+f(B)}2-f(C)\Big]\le\big(2L^2D_1+\tfrac{K^2D_2}{2}\big)h^2 .$$

**Assessment.**
- **Truth: true.** Let $Y$ denote the random variable inside the variance. By #2 and (hL),
  $|Y|\le L\|m-C\|+\tfrac K4(\|A-C\|^2+\|B-C\|^2)$. Hence
  $Y^2\le2L^2\|m-C\|^2+\tfrac{K^2}{4}(\|A-C\|^4+\|B-C\|^4)$, and
  $\mathrm{Var}\,Y\le\mathbb EY^2\le 2L^2D_1h^2+\tfrac{K^2}{4}\cdot2D_2h^2$.
- **No junk values.**
  - $Y$ is measurable, because $f$ is continuous and $E$ is `OpensMeasurableSpace`.
  - $Y\in L^2$, because it is dominated by $L^2$ functions. So `variance` is the genuine variance.
  - Because integrability is assumed, the hypothesis integrals are genuine.
  - If $h=0$, all three differences vanish a.s. and both sides are $0$.
  - If $E=0$, the right-hand side is $2L^2(D_1h^2)+\tfrac{K^2}2(D_2h^2)\ge0$.
- **Vacuity: none.** Example: $E=\mathbb R$, $f=\sin$, $\Omega=[0,1]$ with Lebesgue measure, $A=\omega$, $B=-\omega$,
  $C=0$, $D_1=0$, $D_2=\tfrac15$, $h=1$.
- **Standard fact.** Antithetic MLMC has $V_\ell=O(h^2)$ for smooth payoffs, given
  $\mathbb E\|\bar X^f-X^c\|^2=O(h^2)$ and fourth-moment strong order $1/2$ (Giles–Szpruch 2014).

### 5. `variance_antithetic_le_midpoint` (theorem)

**Rendering.** Same setting as #4. The integrability and moment hypotheses are now:
- $\|m-C\|^2$ and $\|A-B\|^4$ are integrable.
- $\mathbb E\|m-C\|^2\le D_1h^2$ and $\mathbb E\|A-B\|^4\le D_2h^2$.

Conclusion:
$$\mathrm{Var}\Big[\tfrac{f(A)+f(B)}2-f(C)\Big]\le\big(2L^2D_1+\tfrac{K^2D_2}{32}\big)h^2 .$$

**Assessment.**
- **Truth: true.** By #3, $|Y|\le L\|m-C\|+\tfrac K8\|A-B\|^2$, so
  $Y^2\le2L^2\|m-C\|^2+\tfrac{K^2}{32}\|A-B\|^4$. Taking expectations gives the claim.
- **Other checks.** The measurability, $L^2$ and edge-case remarks are as in #4.
- **Vacuity: none.** Same example with $D_2=\mathbb E|2\omega|^4=\tfrac{16}5$.
- **Junk values: none.**
- **Standard fact.** The same Giles–Szpruch $O(h^2)$ variance bound, stated in terms of $\|A-B\|$.

### 6. `abs_call_antithetic_le` (theorem)

**Rendering.** For all real $K,a,b,c$,
$$\Big|\tfrac{(a-K)^++(b-K)^+}2-(c-K)^+\Big|\le\Big|\tfrac{a+b}2-c\Big|+\begin{cases}|a-b|/4&\text{if }\min(a,b)<K<\max(a,b),\\0&\text{otherwise.}\end{cases}$$
The `if` binds as the right operand of `+`.

**Assessment.**
- **Truth: true.** $\varphi(x)=(x-K)^+$ is convex and 1-Lipschitz, so $|\varphi(m)-\varphi(c)|\le|m-c|$. The convexity
  gap $\tfrac{\varphi(a)+\varphi(b)}2-\varphi(m)$ is nonnegative, and it is $0$ unless $K$ lies strictly between $a$
  and $b$, since otherwise $\varphi$ is affine on $[\min,\max]$. If $a<K<b$, the gap is
  $\tfrac12\min(K-a,b-K)\le\tfrac{b-a}4$.
- **Numerics.** Exact rational tests over 228 561 cases, including every tie ($K=a$, $K=b$, $a=b$, $c=m$), found no
  violations (`call_payoff.out`).
- **Sharpness.** $a=-1$, $b=3$, $K=c=1$ gives equality.
- **Vacuity: none. Junk values: none.**
- **Standard fact.** An elementary inequality for the call payoff, used in the analysis of antithetic MLMC for
  piecewise-linear payoffs.

### 7. `variance_call_antithetic_le` (theorem)

**Rendering.** Setting: $(\Omega,\mu)$ is a probability space; $A,B,C:\Omega\to\mathbb R$ are measurable;
$K\in\mathbb R$; $\rho_0\in\mathbb R_{\ge0}$; $D_1,D_2,h\in\mathbb R$.

Hypotheses:
- **(hdens)** As measures on $\mathbb R^2$:
  $\mathrm{Law}\big(|A-B|,\tfrac{A+B}2\big)\le\mathrm{Law}(|A-B|)\otimes(\rho_0\cdot\mathrm{Leb})$. Equivalently,
  $P(|A-B|\in U,\ \tfrac{A+B}2\in V)\le\rho_0\,\mathrm{Leb}(V)\,P(|A-B|\in U)$ for all measurable $U,V$.
- $(\tfrac{A+B}2-C)^2$ and $|A-B|^3$ (a natural-number power) are integrable.
- $\mathbb E(\tfrac{A+B}2-C)^2\le D_1h^2$.
- $\mathbb E|A-B|^3\le D_2h^{3/2}$, where $h^{3/2}$ is `Real.rpow`.

Conclusion:
$$\mathrm{Var}\Big[\tfrac{(A-K)^++(B-K)^+}2-(C-K)^+\Big]\le 2D_1h^2+\tfrac{\rho_0D_2}{8}h^{3/2}.$$

**Assessment.**
- **Truth: true.**
  - By #6 and $(x+y)^2\le2x^2+2y^2$: $Y^2\le2(m-C)^2+\tfrac18\mathbf 1_S|A-B|^2$, where
    $S=\{\min<K<\max\}=\{|m-K|<|A-B|/2\}$ (the set identity is checked exactly in `call_payoff.out`).
  - By (hdens), monotonicity of the lower integral in the measure, and Tonelli (the factor $\rho_0\mathrm{Leb}$ is
    s-finite): $\mathbb E[\mathbf 1_S|A-B|^2]\le\int u^2\rho_0\,\mathrm{Leb}\{v:|v-K|<u/2\}\,d\mathrm{Law}(u)=\rho_0\mathbb E|A-B|^3$.
  - Hence $\mathrm{Var}\le\mathbb EY^2\le 2D_1h^2+\rho_0D_2h^{3/2}/8$.
- **Numerics** (`call_variance.out`). Model: $Z\sim U[0,1]$, $W\sim U[0,\sqrt h]$ independent, $A=Z+W$, $B=Z-W$,
  $C=Z+\sqrt h\,W$, so that $\rho_0=1$, $D_1=1/3$, $D_2=2$.
  - Var/bound $=0.094,\ 0.139,\ 0.157,\ 0.164$ for $h=10^{-1},\dots,10^{-4}$, with $\mathrm{Var}\propto h^{3/2}$.
  - A Monte Carlo cross-check agrees with the quadrature.
- **Vacuity: none.** The example above satisfies every hypothesis.
- **Junk values: no dependence.**
  - For $h<0$, `Real.rpow` gives $h^{3/2}=0$, so $\mathbb E|A-B|^3\le0$ and $A=B$ a.s. The claim then reduces to
    $\mathrm{Var}\le2D_1h^2$, which holds since $|Y|\le|m-C|$.
  - `Measure.map` returns $0$ for non-measurable maps, but $A$ and $B$ are assumed measurable, so (hdens) is not
    trivialised.
  - (hdens) forces $\rho_0>0$.
- **Suspicious hypothesis: (hdens)** is strong and non-standard; see main point 2. It holds, for instance, if the
  midpoint is independent of $|A-B|$ and has density at most $\rho_0$.
- **Standard fact.** Antithetic MLMC for the European call has $V_\ell=O(h^{3/2})$ (Giles–Szpruch 2014), here under
  a density-type assumption.

### 8. `variance_call_antithetic_le_holder` (theorem)

**Rendering.** Setting: as #7 without (hdens); $K\in\mathbb R$; $p,q$ are real Hölder conjugates (so $p,q>1$).

Hypotheses: $(\tfrac{A+B}2-C)^2$ and $|A-B|^{2p}$ (`rpow`) are integrable.

Conclusion:
$$\mathrm{Var}(Y)\le2\,\mathbb E\big(\tfrac{A+B}2-C\big)^2+\tfrac18\big(\mathbb E|A-B|^{2p}\big)^{1/p}\,P\big(\min(A,B)<K<\max(A,B)\big)^{1/q}.$$
Here $Y$ is the same call-payoff difference as in #7, and $P(\cdot)$ is `μ.real`.

**Assessment.**
- **Truth: true.** Use the pointwise bound of #7, then Hölder:
  $\mathbb E[\mathbf 1_S|A-B|^2]\le\||A-B|^2\|_p\|\mathbf 1_S\|_q$.
- **Numerics.** With $(p,q)=(2,2)$ and $(3,\tfrac32)$ in the model of #7, the largest ratio is $0.071$.
- **No junk values.** All `rpow` bases are nonnegative and $1/p,1/q\in(0,1)$. $Y\in L^2$ because
  $|A-B|^2\in L^1$ when $p>1$.
- **Vacuity: none.**
- **Standard fact.** The Hölder step in the Giles–Szpruch analysis of piecewise-linear payoffs.

### 9. `eulerDriftStep` (def)

**Rendering.** $E_{b,h}(S)=S+h\,b(S)$: one explicit Euler step for $\dot S=b(S)$, i.e. the drift part of
Euler–Maruyama.

**Assessment.** Faithful definition; no junk values.

### 10. `tamedDriftStep` (def)

**Rendering.** $T_{b,h}(S)=S+\dfrac{h\,b(S)}{1+h|b(S)|}$: the drift part of the tamed Euler scheme of
Hutzenthaler–Jentzen–Kloeden (2012).

**Assessment.** Faithful definition. For $h\ge0$ the denominator is at least $1$. For $h<0$ it can be $0$, where
Lean's $x/0=0$ applies, but every theorem that uses the step assumes $0\le h$.

### 11. `eulerCubic_growth` (theorem)

**Rendering.** Take $b(S)=-S^3$, so that $E(S)=S(1-hS^2)$; in Lean `-S ^ 3` is $-(S^3)$, checked by `rfl`.
For $h,S\in\mathbb R$ with $2\le hS^2$ and every $n\in\mathbb N$:
$$(hS^2-1)^n|S|\le|E^{n}(S)|,$$
where $E^n$ is the $n$-fold iterate.

**Assessment.**
- **Truth: true, by induction.** If $hS_k^2\ge hS^2\ge2$, then $|S_{k+1}|=|S_k|(hS_k^2-1)\ge|S_k|(hS^2-1)\ge|S_k|$,
  so also $hS_{k+1}^2\ge hS_k^2$.
- **Sharpness.** Equality holds for all $n$ when $hS^2=2$.
- **Numerics.** Exact rational tests found no violations (`euler_tamed.out`).
- **Vacuity: none** ($h=2$, $S=1$). **Junk values: none.**
- **Standard fact.** Explicit Euler is unstable for superlinear drift (Hutzenthaler–Jentzen–Kloeden 2011).

### 12. `eulerCubic_tendsto_atTop` (theorem)

**Rendering.** If $2<hS^2$, then $|E^n(S)|\to\infty$ as $n\to\infty$, for $n\in\mathbb N$.

**Assessment.**
- **Truth: true.** Follows from #11, since $hS^2-1>1$ and $|S|>0$.
- **The strict inequality is necessary.** At $hS^2=2$ the orbit is $S,-S,S,\dots$.
- **Numerics.** With $hS^2=2+10^{-6}$, $|E^n(S)|$ passes $10^{30}$ after 14 steps.
- **Vacuity: none. Junk values: none.**
- **Standard fact.** The divergence threshold of explicit Euler for $\dot S=-S^3$.

### 13. `eulerCubic_bounded` (theorem; statement supplied by the coordinator)

The packet printed `… (n : ℕ) : := sorry` because of a generator bug. The coordinator supplied:

```lean
theorem eulerCubic_bounded {h S : ℝ} (hh : 0 ≤ h) (hS : h * S ^ 2 ≤ 2) (n : ℕ) :
    |(eulerDriftStep (fun S => -S ^ 3) h)^[n] S| ≤ |S|
```

**Rendering.** Take $b(y)=-y^3$, so the Euler step is $E(y)=y+h(-y^3)=y(1-hy^2)$. For real $h,S$ with $0\le h$ and
$hS^2\le2$, and every $n\in\mathbb N$ (with $E^n$ the $n$-fold iterate, $E^0=\mathrm{id}$):
$$|E^n(S)|\le|S| .$$
Only $S$ is bounded; nothing is claimed about convergence.

**Assessment.**
- **Truth: true.** Induct with the invariant $|x_k|\le|S|$, where $x_k=E^k(S)$.
  - The invariant gives $0\le hx_k^2\le hS^2\le2$, hence $|1-hx_k^2|\le1$.
  - So $|x_{k+1}|=|x_k|\,|1-hx_k^2|\le|x_k|\le|S|$. In fact $|x_k|$ is non-increasing.
  - Machine-checked: `prove_cubic_bounded.lean` proves the statement verbatim, and `#print axioms` lists only
    `propext`, `Classical.choice` and `Quot.sound`.
- **Numerics** (`cubic_bounded.out`).
  - Exact rationals: 14 000 cases, including $hS^2=2$ exactly and $h=0$. No violations. ($S=0$ is trivial:
    $E(0)=0$.)
  - 80-digit floats: 1 500 orbits of 301 steps with $hS^2\in[0,2)$, some within $10^{-20}$ of the boundary. No
    violations.
  - At the exact boundary the float orbit can drift away. The 2-cycle $\{S,-S\}$ is repelling, with multiplier
    $(1-3hS^2)^2=25$ per period, so rounding errors grow. In exact arithmetic $|E^n(S)|=|S|$ for every $n$. This is a
    floating-point artefact, not a counterexample, and is recorded in the `.out`.
- **Sharpness.** Equality holds for all $n$ when $hS^2=2$ (the orbit is $S,-S,S,\dots$). The threshold $2$ is sharp:
  for $hS^2>2$ the first step already gives $|E(S)|=|S|(hS^2-1)>|S|$, and #12 then shows divergence.
- **Hypotheses.** Both are necessary.
  - $0\le h$: $h=-1$, $S=1$ gives $E(S)=2>|S|$ (proved by `norm_num` in the scratch file).
  - $hS^2\le2$: see sharpness.
- **Vacuity: none** ($h=1$, $S=1$). **Junk values: none.**
- **Standard fact.** The step-size restriction $hS^2\le2$ for explicit Euler applied to $\dot S=-S^3$. It is the
  stable counterpart of the blow-up in #11 and #12 (Hutzenthaler–Jentzen–Kloeden): Euler is stable only while
  $h|S|^2$ stays below the threshold.

### 14. `abs_tamedDrift_lt` (theorem)

**Rendering.** For every $b:\mathbb R\to\mathbb R$, every $h\ge0$ and every $S$:
$\Big|\dfrac{h\,b(S)}{1+h|b(S)|}\Big|<1$.

**Assessment.**
- **Truth: true.** The left-hand side equals $\dfrac{h|b|}{1+h|b|}<1$.
- **Numerics.** Exact rational tests found no violations. 50-digit floating point rounds the ratio to $1$ when
  $h|b|\sim10^{150}$; that is only a rounding artefact and is noted in `euler_tamed.out`.
- **Vacuity: none. Junk values: none** (the denominator is at least 1).
- **Standard fact.** A tamed increment is bounded by 1.

### 15. `abs_tamedDriftStep_sub_eulerDriftStep_le` (theorem)

**Rendering.** For every $b$, every $h\ge0$ and every $S$: $|T_{b,h}(S)-E_{b,h}(S)|\le h^2\,b(S)^2$.

**Assessment.**
- **Truth: true.** $|T-E|=\dfrac{h^2b^2}{1+h|b|}\le h^2b^2$.
- **Numerics.** No violations.
- **Vacuity: none. Junk values: none.**
- **Standard fact.** Taming perturbs each step by $O(h^2 b^2)$.

### 16. `tamedDriftStep_iterate_bounded` (theorem)

**Rendering.** Let $b$ satisfy $S\,b(S)\le0$ for every $S$: the drift points towards $0$, and $b(0)$ is arbitrary.
For $h\ge0$, every $S$ and every $n\in\mathbb N$: $|T^n(S)|\le\max(|S|,1)$.

**Assessment.**
- **Truth: true.** The increment $\beta$ satisfies $|\beta|<1$ (by #14) and $S\beta\le0$. Hence
  $|S+\beta|\le\max(|S|,1-|S|)\le\max(|S|,1)$. The quantity $\max(|T^nS|,1)$ is therefore non-increasing in $n$.
- **The "1" is needed.** With $S=0.1$, $b\equiv-5$ near $0$ and $h=1000$, $T(S)\approx-0.8998$.
- **Numerics.** Five drifts ($-S^3$, $-S^5$, a discontinuous one, $-Se^{S^2}$, a step) with 60 iterates each: no
  violations.
- **Machine-checked.** This statement, copied verbatim, is also proved in `prove_cubic_bounded.lean` as the helper
  for #17, using only the standard axioms.
- **Vacuity: none. Junk values: none.**
- **Standard fact.** The deterministic a-priori bound for tamed schemes.

### 17. `tamedCubic_bounded` (theorem; statement supplied by the coordinator)

The packet printed `… (n : ℕ) : := sorry` because of a generator bug. The coordinator supplied:

```lean
theorem tamedCubic_bounded {h : ℝ} (hh : 0 ≤ h) (S : ℝ) (n : ℕ) :
    |(tamedDriftStep (fun S => -S ^ 3) h)^[n] S| ≤ max |S| 1
```

**Rendering.** Take $b(y)=-y^3$, so the tamed step is
$$T(y)=y+\frac{h(-y^3)}{1+h|{-y^3}|}=y-\frac{hy^3}{1+h|y|^3}.$$
For real $h\ge0$, every real $S$ and every $n\in\mathbb N$:
$$|T^n(S)|\le\max(|S|,1).$$
There is **no** restriction on the step size $h$ beyond $h\ge0$.

**Assessment.**
- **Truth: true.** It is the special case of #16 with $b(y)=-y^3$, since $y\cdot b(y)=-y^4\le0$. Directly: the
  increment $\beta=-hy^3/(1+h|y|^3)$ has $|\beta|<1$ and sign opposite to $y$, so
  $|y+\beta|\le\max(|y|,1)$. Then $\max(|T^nS|,1)$ is non-increasing in $n$.
- **Machine-checked.** `prove_cubic_bounded.lean` proves #16 in general and derives this statement verbatim.
  `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.
- **Numerics** (`cubic_bounded.out`).
  - Exact rationals: 12 000 cases, including $S=0$ and $h$ up to about $10^{12}$. No violations.
  - 80-digit floats: 3 000 orbits of 301 steps, $h\in[10^{-10},10^{14}]$, $|S|$ up to $10^{4}$ on a logarithmic
    scale reaching below $10^{-6}$. No violations; the largest ratio is exactly $1$, attained at $n=0$ when
    $|S|\ge1$.
  - Contrast with Euler at $h=10$, $S=3$ (so $hS^2=90$): after six steps $|\text{Euler}|\approx4.4\cdot10^{710}$,
    while $|\text{tamed}|\approx0.078$.
- **Is the "$\max(\cdot,1)$" needed? Yes, and the constant $1$ is sharp.**
  - $S=\tfrac1{10}$, $h=1000$ gives $T(S)=-\tfrac25$ exactly, so the variant $|T^nS|\le|S|$ would be **false**
    (proved by `norm_num` in the scratch file).
  - $S=10^{-3}$, $h=10^{12}$ gives $T(S)\approx-0.998$, so the $1$ cannot be lowered.
- **Is $0\le h$ needed? Yes.**
  - $h=-\tfrac12$, $S=1$ gives $T(S)=2>\max(|S|,1)=1$ (proved by `norm_num`).
  - $h=-1$, $S=1$ makes the denominator $0$, where Lean's $x/0=0$ gives $T(S)=S$.

  Under $0\le h$ the denominator is at least $1$, so no junk value is reached.
- **Vacuity: none** ($h=1$, any $S$). **Junk values: none.**
- **Standard fact.** The tamed Euler scheme of Hutzenthaler–Jentzen–Kloeden (2012). With a dissipative
  (sign-condition) drift, the tamed drift iteration stays bounded for every step size, whereas explicit Euler blows up
  once $hS^2>2$ (#11–#13).

### 18. `abs_smoothCDF_sub_le_of_bounded` (theorem)

**Rendering.** Setting:
- $(\Omega,\mu)$ is a probability space and $P:\Omega\to\mathbb R$ is measurable.
- $g$ is measurable, with $g(y)=0$ for $y<-1$ and $g(y)=1$ for $y>1$.
- $|g|\le B$ everywhere, $\delta>0$, and $x\in\mathbb R$.

Conclusion:
$$\big|\mathbb E\,g\big(\tfrac{x-P}\delta\big)-P(P<x)\big|\le(1+B)\,P(|P-x|\le\delta).$$

**Assessment.**
- **Truth: true.** Pointwise, $|g(\tfrac{x-P}\delta)-\mathbf 1\{P<x\}|$ is $0$ off $\{|P-x|\le\delta\}$. On that set
  it is at most $B+1$; this includes the boundary points $P=x\mp\delta$, where $g(\pm1)$ is unconstrained.
- **Numerics.** 198 cases in `smooth_cdf.out`, using three $g$'s (overshooting, discontinuous, smoothstep) and a law
  with atoms: no violations, largest ratio $0.749$.
- **Junk values: none.** The integrand is bounded and measurable, hence integrable.
- **Hypotheses.** $B\ge1$ automatically, since $g(2)=1$.
- **Vacuity: none.**
- **Standard fact.** The smoothing-error bound for MLMC estimation of distribution functions
  (Giles–Nagapetyan–Ritter).

### 19. `tendsto_smoothCDF_of_bounded` (theorem)

**Rendering.** Same hypotheses on $g$ as #18 ($B$ does not appear in the conclusion), plus $\mu\{P=x\}=0$. Then
$\mathbb E\,g(\tfrac{x-P}\delta)\to P(P<x)$ as $\delta\to0^+$ (filter `𝓝[>] 0`).

**Assessment.**
- **Truth: true.** By #18 and continuity from above, $P(|P-x|\le\delta)\downarrow P(P=x)=0$.
- **The no-atom hypothesis is necessary** unless $g(0)=0$: at an atom the limit is $P(P<x)+g(0)P(P=x)$
  (`smooth_cdf.out`).
- **Vacuity: none. Junk values: none.**
- **Standard fact.** Convergence of the smoothed CDF at continuity points.

### 20. `tendsto_smoothCDF_of_continuous` (theorem)

**Rendering.** $g$ is continuous with the same tails; no bound $B$ is assumed. The conclusion is the same limit as #19.

**Assessment.**
- **Truth: true.** A continuous $g$ is measurable and bounded (constant outside $[-1,1]$, continuous on a compact set),
  so #19 applies.
- **Vacuity: none. Junk values: none.**

### 21. `tendsto_density_multidim` (theorem)

**Rendering.** Setting:
- $F$ is a finite-dimensional real normed space with its Borel σ-algebra, and $\nu$ is an additive Haar measure.
- $(\Omega,\mu)$ is a probability space and $P:\Omega\to F$ is measurable.
- The law of $P$ is $\rho\,\nu$, for a measurable $\rho:F\to\mathbb R_{\ge0}$.
- $\rho$, viewed as a real-valued function, is continuous at $x$.
- $g:F\to\mathbb R$ is continuous, $g(y)=0$ whenever $\|y\|>1$, and $\int g\,d\nu=1$.

Conclusion, with $d=\operatorname{finrank}F$ (a natural-number power):
$$\mathbb E\big[\delta^{-d}g\big(\delta^{-1}(x-P)\big)\big]\to\rho(x)\quad(\delta\to0^+).$$

**Assessment.**
- **Truth: true.** Substitute $y=x-\delta z$, using translation and negation invariance of $\nu$ and
  $\nu(\delta S)=\delta^d\nu(S)$. This gives $\mathbb E[\cdot]=\int g(z)\rho(x-\delta z)\,d\nu(z)$. Continuity at
  $x$ makes $\rho$ bounded near $x$, and $\rho(x-\delta z)\to\rho(x)$ uniformly on $\|z\|\le1$. Since $g\in L^1$,
  the limit is $\rho(x)\int g=\rho(x)$.
- **Junk values: none.** For $\delta>0$ the integrand is bounded and measurable, and $\int g$ is a genuine integral
  because $g$ has compact support.
- **Numerics** (`density_recovery.out`).
  - 1-D Gaussian with a non-symmetric $g$: error $O(\delta)$.
  - 2-D Gaussian with a radial $g$ (error $O(\delta^2)$) and a non-radial $g$ (error $O(\delta)$). A direct
    evaluation confirms the $\delta^{-2}$ scaling.
  - At a jump of $\rho$ the limit is $\int_{z\le0}g=0.34375\neq1$, so continuity at $x$ is required.
- **Vacuity: none** ($F=\mathbb R$, $\nu$ = Lebesgue, Gaussian $P$, a bump $g$).
- **Hypotheses.** Continuity of $g$ is stronger than needed (bounded measurable would do), which is harmless.
- **Standard fact.** Approximate identity / Parzen–Rosenblatt kernel density consistency at continuity points.

### 22. `tendsto_density_euclidean` (theorem)

**Rendering.** The same statement as #21 for $F=\mathbb R^d$ (`EuclideanSpace ℝ (Fin d)`, Euclidean norm) with
$\nu$ = `volume` (Lebesgue measure), the weight $\delta^{-d}$, and $\int g=1$ with respect to `volume`.

**Assessment.**
- **Truth: true.** It is the special case of #21: `volume` is an additive Haar measure and $\operatorname{finrank}=d$.
  The case $d=0$ is also consistent: `volume` is the unit Dirac mass, so $g(0)=1=\rho(0)$.
- **Vacuity: none. Junk values: none.**

### 23. `smoothCDF` (def, appended from `MlmcLean.SDEExtras`)

**Rendering.** `smoothCDF μ P g δ x` $=\int g\big((x-P(\omega))/\delta\big)\,d\mu(\omega)$. The compiled signature and
the definitional unfolding are confirmed by `#check` and `rfl` (`scratch_packet.lean`). For a step-like $g$ this is
a smoothed version of $P(P<x)$.

**Assessment.** Faithful to the usual smoothed-indicator estimator. For $\delta=0$ Lean gives $g(0)$, because
$y/0=0$, but no statement uses $\delta\le0$. A non-integrable composite would integrate to $0$, but every statement
makes it bounded and measurable.
