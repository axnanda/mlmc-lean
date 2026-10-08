# Blind read-back report: packet R44 (GBM sensitivities / Greeks)

| Field | Value |
|---|---|
| Date | 2026-10-08 |
| Packet | `readback/round24/packet_R44_sens.lean` |
| Declarations audited | 13 in the module (11 theorems + 2 definitions); the appended definitions are also rendered |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round24/work_R44_sens/` (`r44_algebra.py`, `r44_identities.py`, `r44_mc_rates.py`, each with `.out`; elaboration check `scratch_R44.lean`) |

Elaboration check: a copy of the packet compiled with `import MlmcLean` (only the `sorry` warnings).
Every packet definition is equal by `rfl` to the library constant: the two `…Delta` definitions,
`pairAvg`, `gbmEM`, `gbmMil`, `gbmCond{Mean,Std}{Fine,Coarse}`, `gbmDigitalCond{Fine,Coarse}`,
`gbmMilEM`, `emStep` and `milsteinStep`, the defining equations of `emPath`, `milsteinPath`,
`fineCoarseDiff` and `blockMean`, and `gbmDrift`/`gbmVol`. How the notation elaborates:

- `(Set.Ioi K).indicator 1 y` uses `1 = Pi.one : ℝ → ℝ`, so it equals $\mathbf 1\{y>K\}$.
- `(T / 2 ^ (ℓ+1)) ^ q` and `ε ^ (-3 - η)` are `Real.rpow` of positive bases.
- `variance` is `ProbabilityTheory.variance`.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `gbm_em_call_pathwise_delta` | theorem | true | no | no |
| 2 | `gbm_mil_call_pathwise_delta` | theorem | true | no | no |
| 3 | `gbm_call_delta` | theorem | true | no | no |
| 4 | `gbm_em_call_delta_rate` | theorem | true | no | no |
| 5 | `gbm_mil_call_delta_rate` | theorem | true | no | no |
| 6 | `gbm_em_call_delta_weak_rate` | theorem | true | no | no |
| 7 | `gbm_mil_call_delta_weak_rate` | theorem | true | no | no |
| 8 | `gbm_em_call_delta_theorem1` | theorem | true | no | no |
| 9 | `gbm_mil_call_delta_theorem1` | theorem | true | no | no |
| D1 | `gbmDigitalCondFineDelta` | def | n/a | n/a | $x/0=0$ only on a null set |
| D2 | `gbmDigitalCondCoarseDelta` | def | n/a | n/a | $x/0=0$ only on a null set |
| 10 | `gbm_digital_condExp_delta` | theorem | true | no | no |
| 11 | `gbm_digital_condExp_delta_telescope` | theorem | true | no | no |

## Main points for a human auditor

- **All 11 theorems are true, none is vacuous, and none depends on a junk value.**
- **The hypotheses are justified.**
  - In theorems 1–3, `hsK : s₀ ≠ 0 ∨ K ≠ 0` is necessary. For $s_0=K=0$, the map
    $s\mapsto\mathbb E\max(sX,0)=s^+\mathbb E X$ has one-sided derivatives $e^{rT}$ and $0$ at
    $0$ (`r44_identities.out`).
  - In theorems 1–3, `hσ` and `hT` make the kink event $\{s_0X=K\}$ null. With $\sigma=0$ or
    $T\le0$ the terminal value is deterministic.
  - In theorems 6–7, `hσ` is necessary. Counterexample: $\sigma=0$, $r=0.1$, $T=1$, $s_0=-1$,
    $K=-e^{0.1}$. Then the weak error tends to $e^{0.1}\approx1.105$, not to 0
    (`r44_identities.out`).
  - Theorems 4–5 have no `hσ`, and correctly so: for $\sigma=0$ the level difference is
    deterministic and has variance 0.
  - In theorems 10–11, `hs₀`, `hσ` and `hT` are needed. Without them the conditional standard
    deviation can be 0, which triggers the junk value $\Phi(x/0)=\Phi(0)=1/2$.
- **Some rate statements are weaker than the known sharp results, but they are true.**
  - The level-variance rates $q<1/2$ (Euler–Maruyama, EM) and $q<1$ (Milstein) match the known
    $\beta=1/2$ and $\beta=1$ for the pathwise call delta. Monte Carlo slopes are about 0.5 and
    1.0 (`r44_mc_rates.out`).
  - The weak rates $q<1/2$ and $q<1$ are weaker than the classical weak order 1. As a result, the
    EM complexity $\varepsilon^{-3-\eta}$ (theorem 8) is weaker than the $\varepsilon^{-2.5}$ that
    Giles' theorem gives with $\alpha=1$, $\beta=1/2$, $\gamma=1$. The Milstein bound
    $\varepsilon^{-2-\eta}$ (theorem 9) is slightly weaker than the sharp
    $\varepsilon^{-2}(\log\varepsilon)^2$.
  - Every $q<1/2$ (or $q<1$) is allowed, including $q\le0$. For those $q$ the statement only says
    the quantity is bounded, which is weaker but still true.
- **Modelling choice in the digital theorems (10–11).** The telescoped derivative is the
  derivative of $\mathbb P(\texttt{gbmMilEM}_L>K)$. This scheme takes $2^L-1$ Milstein steps
  followed by a final Euler step. It is not the pure Milstein `gbmMil`. This matches Giles'
  conditional-expectation technique.
  - The delta formula $\varphi(\cdot)\,K/(s_0\,\mathrm{std}(s_0))$ is correct for both signs of
    $s_0$ (checked with sympy).
  - The coarse conditional mean conditions on the first half $z_{2^{\ell+1}-2}$ of the last coarse
    Brownian increment. That variable is independent of the first $2^\ell-1$ coarse steps.
- **No truncation from ℕ-subtraction.** The indices $2^\ell-1$ and $2^{\ell+1}-2$ never truncate.
- **Integrability is stated explicitly.** Every expectation and variance comes with an
  integrability or `MemLp` conjunct, so integrals of non-integrable functions (which Lean sets to
  0) never occur. Likewise $\texttt{variance}=\texttt{evariance.toReal}$ never meets the
  $\infty\mapsto0$ conversion.

## Per-declaration sections

Notation.

- **Probability space.** $\mathbb P$ = `stdNormalSeq` $=\bigotimes_{n}N(0,1)$, so $z=(z_i)$ are
  i.i.d. $N(0,1)$.
- **Step sizes.** $h_\ell=T/2^\ell$.
- **Coarse increments.** $\bar z$ = `pairAvg z`, with $\bar z_k=(z_{2k}+z_{2k+1})/\sqrt2$.
- **EM scheme (`gbmEM r σ T s ℓ z`).** The EM recursion for $dS=rS\,dt+\sigma S\,dW$ with $2^\ell$
  steps of size $h_\ell$:
  $$X^E_\ell(s;z)=s\prod_{i<2^\ell}\bigl(1+rh_\ell+\sigma\sqrt{h_\ell}\,z_i\bigr).$$
- **Milstein scheme (`gbmMil`).** Since $b(S)=\sigma S$ and $b'=\sigma$:
  $$X^M_\ell(s;z)=s\prod_{i<2^\ell}\bigl(1+rh_\ell+\sigma\sqrt{h_\ell}z_i+\tfrac12\sigma^2h_\ell(z_i^2-1)\bigr).$$
- **Exact factor.** $E(w)=\exp((r-\sigma^2/2)T+\sigma\sqrt T\,w)$.
- **Exact (undiscounted) delta.**
  $$\Delta^{\rm ex}=\int\mathbf 1\{s_0E(w)>K\}E(w)\,N(0,1)(dw),$$
  which equals $e^{rT}N(d_1)$ when $s_0>0$.
- **Level payoff.** For a scheme $X_\ell$: $P_\ell(z)=\mathbf 1\{X_\ell(s_0;z)>K\}X_\ell(1;z)$.
- **Level difference.** $D_\ell(z)=P_{\ell+1}(z)-P_\ell(\bar z)$.

### 1. `gbm_em_call_pathwise_delta`

**Rendering.** For all $r,\sigma,K\in\mathbb R$, $T>0$, $\sigma\ne0$, $s_0\in\mathbb R$ with
($s_0\ne0$ or $K\ne0$), and $\ell\in\mathbb N$:
(i) $X^E_\ell(s;z)=s\,X^E_\ell(1;z)$ for all $s,z$;
(ii) for $\mathbb P$-a.e. $z$, the map $s\mapsto\max(X^E_\ell(s;z)-K,0)$ is differentiable at
$s_0$ with derivative $\mathbf 1\{X^E_\ell(s_0;z)>K\}\,X^E_\ell(1;z)$;
(iii) for every $s$, $\max(X^E_\ell(s)-K,0)$ is integrable;
(iv) $\mathbf 1\{X^E_\ell(s_0)>K\}X^E_\ell(1)$ is integrable;
(v) $s\mapsto\mathbb E\max(X^E_\ell(s)-K,0)$ is differentiable at $s_0$ with derivative
$\mathbb E[\mathbf 1\{X^E_\ell(s_0)>K\}X^E_\ell(1)]$.

**Assessment.** True.
(i) Each EM step is linear in $S$ (checked with sympy).
(ii) Write $X=X^E_\ell(1)$. A kink occurs only on $\{s_0X=K,\ X\ne0\}$.
- If $X=0$ and $K=0$, both sides are 0.
- If $s_0\ne0$: $X$ is a product of independent non-degenerate affine Gaussians (since
  $\sigma\ne0$ and $h>0$), so $X$ has no atoms and $\mathbb P(X=K/s_0)=0$.
- If $s_0=0$ and $K\ne0$, the event is empty.

(iii)–(iv) $X$ has all moments.
(v) The map is Lipschitz in $s$ with constant $|X|\in L^1$. Combined with a.e. differentiability,
dominated differentiation applies.

Not vacuous: $r=0.05$, $\sigma=0.2$, $T=1$, $s_0=K=1$. There is no junk dependence. `hsK` is
necessary (see main points). This is the pathwise (likelihood-free) delta for a call under EM,
i.e. interchanging the derivative and the expectation.

### 2. `gbm_mil_call_pathwise_delta`

**Rendering.** This is the same as theorem 1 with $X^M_\ell$ (Milstein) in place of $X^E_\ell$.

**Assessment.** True.
- Linearity in $s$ is checked with sympy.
- Each Milstein factor is a non-constant quadratic in $z_i$, since its leading coefficient
  $\tfrac12\sigma^2h\ne0$. So each factor is atomless and vanishes with probability 0, and the
  product is atomless.
- The moments are finite and the rest is as in theorem 1.

Not vacuous. There is no junk dependence. This is the pathwise delta under the Milstein scheme.

### 3. `gbm_call_delta`

**Rendering.** For all $r,\sigma,K$, $T>0$, $\sigma\ne0$, and ($s_0\ne0$ or $K\ne0$), with
$w\sim N(0,1)$:
(i) for a.e. $w$, $s\mapsto\max(sE(w)-K,0)$ has derivative $\mathbf 1\{s_0E(w)>K\}E(w)$ at $s_0$;
(ii) $\max(sE-K,0)$ is integrable for every $s$;
(iii) $\mathbf 1\{s_0E>K\}E$ is integrable;
(iv) $\frac{d}{ds}\mathbb E\max(sE-K,0)\big|_{s_0}=\Delta^{\rm ex}$.

**Assessment.** True. $E$ is strictly monotone in $w$ because $\sigma\sqrt T\ne0$, so the kink set
has at most one point. $E$ is lognormal and integrable. The derivative follows by dominated
differentiation. Central finite differences match $\Delta^{\rm ex}$ for
$(s_0,K)\in\{(1,1),(0.8,1),(-1,-1),(0,-1),(0,1)\}$ (`r44_identities.out`). Not vacuous. There is
no junk dependence. This is the Black–Scholes call delta (undiscounted), $e^{rT}N(d_1)$.

### 4. `gbm_em_call_delta_rate`

**Rendering.** For all $r,\sigma$ (with no condition on $\sigma$), $T>0$, $q<1/2$ and
$s_0,K\in\mathbb R$, there is $C\ge0$ (depending on $r,\sigma,T,q,s_0,K$) such that for every
$\ell\in\mathbb N$, with the EM payoff $P$:
$$D_\ell(z)=\mathbf 1\{X^E_{\ell+1}(s_0;z)>K\}X^E_{\ell+1}(1;z)-\mathbf 1\{X^E_\ell(s_0;\bar z)>K\}X^E_\ell(1;\bar z)\in L^2(\mathbb P)$$
and $\mathrm{Var}(D_\ell)\le C\,(T/2^{\ell+1})^q$.

**Assessment.** True.
- If $\sigma=0$: $D_\ell$ is deterministic, so its variance is 0.
- If $s_0=0$: $D_\ell=\mathbf 1\{0>K\}(X_f-X_c)$, whose variance is $O(h)$.
- Otherwise:
  - EM is uniformly $L^p$-bounded and of strong order $1/2$ (fine and coarse paths are driven by
    the same Brownian path through `pairAvg`).
  - The exact GBM has bounded density at $K/s_0$.
  - An Avikainen-type argument then gives $\mathbb P(\text{indicators differ})=O(h^{1/2-\delta})$.
  - Then $\mathbb E D_\ell^2\le2\mathbb E(X_f-X_c)^2+2\mathbb E[X_c^2\mathbf 1_{\rm differ}]=O(h^{1/2-\delta'})$
    by Hölder.

The Monte Carlo variance decay has slope ≈ 0.5 per level (`r44_mc_rates.out`). Not vacuous. There
is no junk dependence, because `MemLp` is asserted, so the variance is finite. This is the MLMC
level-variance bound $V_\ell=O(h^{1/2-})$ for the EM pathwise call delta (Giles; Burgos–Giles).

### 5. `gbm_mil_call_delta_rate`

**Rendering.** This is the same as theorem 4 for Milstein, with $q<1$.

**Assessment.** True. Milstein has strong order 1 for GBM (scalar noise), so
$\mathbb P(\text{differ})=O(h^{1-\delta})$ and $\mathrm{Var}\,D_\ell=O(h^{1-\delta'})$. The Monte
Carlo slope is about 1 (`r44_mc_rates.out`; this is noisy because events are rare at fine levels).
Not vacuous. There is no junk dependence. This is $V_\ell=O(h^{1-})$ for the Milstein pathwise call
delta.

### 6. `gbm_em_call_delta_weak_rate`

**Rendering.** For $\sigma\ne0$, $T>0$, $q<1/2$ and any $s_0,K$, there is $C\ge0$ such that for
all $\ell$:
$$\bigl|\mathbb E[\mathbf 1\{X^E_\ell(s_0)>K\}X^E_\ell(1)]-\Delta^{\rm ex}\bigr|\le C(T/2^\ell)^q.$$

**Assessment.** True. Couple with the exact solution through $W_T=\sqrt h\sum z_i$. Then
$\mathbb E|P_\ell-P|\le\mathbb E|X_\ell-X|+\mathbb E[|X|\mathbf 1_{\rm differ}]=O(h^{1/2-})$ by
strong order $1/2$ and the bounded density of $X$ at $K/s_0$. The case $s_0=0$ is trivial.
`hσ` is necessary (counterexample in main points, `r44_identities.out`). The statement is weaker
than the true weak order 1 (Bally–Talay type), but true. Not vacuous. There is no junk dependence.

### 7. `gbm_mil_call_delta_weak_rate`

**Rendering.** This is the same as theorem 6 for Milstein, with $q<1$.

**Assessment.** True, by the same argument with strong order 1. Not vacuous. There is no junk
dependence. `hσ` is necessary, by the same counterexample (with $\sigma=0$, Milstein coincides
with EM).

### 8. `gbm_em_call_delta_theorem1`

**Rendering.** For all $r,\sigma\ne0,s_0,K$, $T>0$ and $\eta>0$, there is $c_4>0$ such that for
every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ with
$N_\ell\ge1$ for all $\ell$ satisfying the following.

Let $x=(x_{\ell,n})_{(\ell,n)\in\mathbb N^2}$ be i.i.d. copies of $z$
(`Measure.infinitePi` of `stdNormalSeq`). Define the MLMC estimator
$$\hat Y(x)=\sum_{\ell=0}^{L}\frac1{N_\ell}\sum_{n<N_\ell}\Delta_\ell(x_{\ell,n}),$$
where $\Delta_0=P_0$ and $\Delta_{\ell+1}(y)=P_{\ell+1}(y)-P_\ell(\bar y)$, with the EM payoffs
$P$. Then:
- $(\hat Y-\Delta^{\rm ex})^2$ is integrable;
- $\mathbb E(\hat Y-\Delta^{\rm ex})^2<\varepsilon^2$;
- $\sum_{\ell\le L}N_\ell2^\ell\le c_4\varepsilon^{-3-\eta}$.

**Assessment.** True. Take theorems 4 and 6 with $\alpha=\beta=1/2-\delta$, and $\gamma=1$ (cost
$2^\ell$ per sample). Giles' complexity theorem in the case $\beta<\gamma$ gives cost
$O(\varepsilon^{-2-(\gamma-\beta)/\alpha})$, with
$(\gamma-\beta)/\alpha=1+4\delta/(1-2\delta)\le1+\eta$ for $\delta$ small. The ceiling effects
$\sum2^\ell=O(\varepsilon^{-1/\alpha})$ are dominated. The quantifier order is correct: $c_4$ is
independent of $\varepsilon$, while $L$ and $N$ depend on $\varepsilon$. Not vacuous. There is no
junk dependence, because $N_\ell>0$ and integrability is asserted. The exponent is weaker than the
sharp $\varepsilon^{-2.5}$ (true weak order 1), but true. This is Giles (2008), Theorem 1, applied
to the EM pathwise delta.

### 9. `gbm_mil_call_delta_theorem1`

**Rendering.** This is the same as theorem 8 with Milstein payoffs and the cost bound
$c_4\varepsilon^{-2-\eta}$.

**Assessment.** True. With $\alpha=\beta=1-\delta$ and $\gamma=1$, we get
$(\gamma-\beta)/\alpha=\delta/(1-\delta)\le\eta$. The sharp result is
$\varepsilon^{-2}(\log\varepsilon)^2$ ($\beta=\gamma$), which is at most $c\,\varepsilon^{-2-\eta}$.
Not vacuous. There is no junk dependence.

### D1. `gbmDigitalCondFineDelta`

**Rendering.** Let $M^f=M^f_\ell(s_0;z)$ be the Milstein path with step $h_\ell$, started at
$s_0$, after $2^\ell-1$ steps on $z$. Set $m_f=M^f(1+rh_\ell)$ (`gbmCondMeanFine`) and
$\varsigma_f=|\sigma M^f|\sqrt{h_\ell}$ (`gbmCondStdFine`). The value is
$$\varphi\bigl((m_f-K)/\varsigma_f\bigr)\cdot K/(s_0\varsigma_f),$$
where $\varphi$ is the $N(0,1)$ density (`gaussianPDFReal 0 1`).

**Assessment.** This is a definition. It is $\partial_s$ of
$\texttt{gbmDigitalCondFine}=\Phi((m_f-K)/\varsigma_f)$, the conditional probability that the
final Euler step exceeds $K$. Because $m_f$ is linear in $s$ and $\varsigma_f=|s|\cdot$const, the
formula holds for both signs of $s$ (checked with sympy, `r44_algebra.out`). If $\varsigma_f=0$,
Lean's $x/0=0$ gives $0$. This happens only if $M^f=0$ or $s_0=0$, which is a null event under
the theorems' hypotheses.

### D2. `gbmDigitalCondCoarseDelta`

**Rendering.** Let $M^c$ be the Milstein path with step $h_\ell$, started at $s_0$, after
$2^\ell-1$ steps on $\bar z$. Set
$m_c=M^c(1+rh_\ell)+\sigma M^c\sqrt{h_{\ell+1}}\,z_{2^{\ell+1}-2}$ and
$\varsigma_c=|\sigma M^c|\sqrt{h_{\ell+1}}$. The value is
$\varphi((m_c-K)/\varsigma_c)\cdot K/(s_0\varsigma_c)$.

**Assessment.** This is a definition. It is the $s$-derivative of the coarse conditional
probability $\Phi((m_c-K)/\varsigma_c)$, which conditions on the first fine half
$z_{2^{\ell+1}-2}$ of the last coarse increment
$\sqrt{h_{\ell+1}}(z_{2^{\ell+1}-2}+z_{2^{\ell+1}-1})$. This is Giles' conditional-expectation
coupling.

### 10. `gbm_digital_condExp_delta`

**Rendering.** For $s_0\ne0$, $\sigma\ne0$, $T>0$ and any $K$, $\ell$:
(i) for a.e. $z$, $s\mapsto\Phi((m_f(s)-K)/\varsigma_f(s))$ has derivative
$\texttt{FineDelta}(s_0;z)$ at $s_0$;
(ii) the same for the coarse quantity with $\texttt{CoarseDelta}$;
(iii), (iv) both deltas are in $L^2(\mathbb P)$;
(v), (vi) $\frac{d}{ds}\mathbb E[\texttt{gbmDigitalCond}\{\texttt{Fine},\texttt{Coarse}\}(s)]$ at
$s_0$ equals $\mathbb E[\texttt{FineDelta}]$, respectively $\mathbb E[\texttt{CoarseDelta}]$;
(vii) $\mathbb E[\texttt{FineDelta}_\ell]=\mathbb E[\texttt{CoarseDelta}_\ell]$.

**Assessment.** True.
- (i)–(ii): $M\ne0$ a.s., since the Milstein factors are non-constant quadratics; for $\ell=0$,
  $M=s_0\ne0$. The map is smooth near $s_0\ne0$.
- (iii): $|\texttt{FineDelta}|\le\sup_v|\varphi(A-v)v|/|s_0|<\infty$, with
  $A=\pm(1+rh)/(|\sigma|\sqrt h)$ constant, so the delta is bounded.
- (iv): $|\texttt{CoarseDelta}|\le(c+|z'|)/|s_0|$, which is in $L^2$.
- (v)–(vi): these bounds hold uniformly for $s$ near $s_0$, so dominated differentiation applies.
- (vii): $\mathbb E[\texttt{Coarse}(s)]=\mathbb E[\texttt{Fine}(s)]$ for every $s\ne0$. This uses
  $\mathbb E_{z'}\Phi((a+bz')/|b|)=\Phi(a/(\sqrt2|b|))$ (checked by quadrature) and the fact that
  $\bar z$ is again i.i.d. $N(0,1)$. Hence the derivatives agree.

Monte Carlo: $\mathbb E[\texttt{FineDelta}]$, $\mathbb E[\texttt{CoarseDelta}]$ and a finite
difference of $\mathbb E[\texttt{Fine}]$ agree within noise for $\ell=0..3$ (`r44_mc_rates.out`).
Not vacuous. There is no junk dependence: the $x/0$ cases are null under `hs₀`, `hσ` and `hT`.
This is Giles' conditional-expectation smoothing for the digital delta in MLMC.

### 11. `gbm_digital_condExp_delta_telescope`

**Rendering.** For $s_0\ne0$, $\sigma\ne0$, $T>0$, any $K$ and $L\in\mathbb N$:
(i) for every $\ell$, the level difference
$\texttt{fineCoarseDiff}_\ell$ ($=\texttt{FineDelta}_0$ if $\ell=0$, and
$\texttt{FineDelta}_{\ell}-\texttt{CoarseDelta}_{\ell-1}$ otherwise) is in $L^2(\mathbb P)$;
(ii) $s\mapsto\mathbb P(\texttt{gbmMilEM}_L(s;z)>K)$ is differentiable at $s_0$ with derivative
$\sum_{\ell=0}^{L}\mathbb E[\texttt{fineCoarseDiff}_\ell]$. Here
$\texttt{gbmMilEM}_L(s;z)=M^f+rM^fh_L+\sigma M^f\sqrt{h_L}\,z_{2^L-1}$, i.e. $2^L-1$ Milstein steps
and then one Euler step.

**Assessment.** True.
- (i) follows from theorem 10 (iii)–(iv).
- (ii): by theorem 10 (vii) the sum telescopes to $\mathbb E[\texttt{FineDelta}_L]$. By the tower
  property, $\mathbb P(\texttt{gbmMilEM}_L(s)>K)=\mathbb E[\Phi((m_f(s)-K)/\varsigma_f(s))]$ for
  $s\ne0$; this was checked by quadrature, including $M<0$ and $\sigma<0$. Theorem 10 (v) then
  gives the derivative.

Not vacuous. There is no junk dependence. The target scheme is `gbmMilEM`, not `gbmMil` (see main
points). This is the MLMC telescoping identity for the smoothed digital delta.

### Appended definitions (rendered for completeness)

- `blockMean f ω i N x` $=N^{-1}\sum_{n<N}f_i(\omega_{(i,n)}(x))$.
- `fineCoarseDiff Pf Pc` gives $\texttt{Pf}_0$ at level 0, and $y\mapsto \texttt{Pf}_{\ell+1}(y)-\texttt{Pc}_\ell(y)$ at level $\ell+1$.
- `pairAvg z k` $=(z_{2k}+z_{2k+1})/\sqrt2$.
- `stdNormalSeq` $=\bigotimes_n N(0,1)$.
- `emPath a b h S₀ z` is $S_0$ at step 0, and $S_{i+1}=S_i+a(S_i,ih)h+b(S_i,ih)\sqrt h\,z_i$.
- `emStep a b h S dW` $=S+a(S)h+b(S)\,dW$.
- `milsteinPath` iterates `milsteinStep a b h S dW` $=S+a(S)h+b(S)dW+\tfrac12b(S)b'(S)(dW^2-h)$ with $dW=\sqrt h\,z_i$.
- `gbmDrift r S t` $=rS$ and `gbmVol σ S t` $=\sigma S$.
- `gbmEM`, `gbmMil`, `gbmCond*`, `gbmDigitalCond{Fine,Coarse}` and `gbmMilEM` are as in the notation above.
