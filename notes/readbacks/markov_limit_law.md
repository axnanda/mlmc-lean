# Blind read-back: M8 `MlmcLean.MarkovLimitLaw`

| Field | Value |
|---|---|
| Date | 2026-09-29 |
| Packet (relative to scratchpad) | `readback/round11/packet_M8_markov_limit_law.lean`. The conclusions of #3 and #4 come from the coordinator's corrected `readback/round11/packet_M8_markov_limit_law_v2.lean`; `diff` shows those two conclusions are the only changes. |
| Declarations audited | 14 theorems, plus 11 supporting definitions (rendered only) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round11/work_M8/` (Python `*.py` with `*.out`; Lean scratch `*.lean` with `*.out`) |
| Toolchain | Lean v4.33.1, Mathlib 0df444a |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `lintegral_dist_limit_le` | theorem | true | no | no. Edge case $\rho=0$, $c=\infty$: ENNReal $0\cdot\infty=0$ makes the RHS $0$, and the LHS is still $0$. |
| 2 | `sq_integral_sub_limit_le` | theorem | true | no | no |
| 3 | `abs_integral_sub_limit_le` (v2) | theorem | true | no | no |
| 4 | `abs_integral_fwdIter_sub_limit_le` (v2) | theorem | true | no | no |
| 5 | `map_limit_invariant` | theorem | true | no | no |
| 6 | `map_limit_eq_of_invariant` | theorem | true | no | no |
| 7 | `invariant_unique` | theorem | true | no | no |
| 8 | `existsUnique_invariant` | theorem | true | no | no |
| 9 | `map_limit_halfStep` | theorem | true | no | no |
| 10 | `halfStep_limit_uniform` | theorem | true | no | no |
| 11 | `halfStep_invariant_unique` | theorem | true | no | no |
| 12 | `markov_mlmc_rates` | theorem | true | no | no |
| 13 | `markov_randomised_mlmc` | theorem | true | no | no |
| 14 | `markov_mlmc_theorem1` | theorem | true | no | no |

## Main points for a human auditor

1. **The packet had defects.**
   - v1 printed `(n : ℕ) : := sorry` and `(N : ℕ) : := sorry`, dropping the conclusions of #3 and #4. The coordinator's v2 fixes this.
   - The definition of `singleTerm`, which #13 uses, is still missing from the appendix in both v1 and v2. Only a dangling `omit [MeasurableSpace Ω] in` line is left.
   - I recovered `singleTerm` with `#print MLMC.singleTerm` in a scratch compile (see `sigs.out`). It is $\mathrm{singleTerm}(P,K,p)(\omega) = p(K\omega)^{-1}\cdot \mathrm{levelDiff}\,P\,(K\omega)\,\omega$.
2. **The module was not built.** `MlmcLean.MarkovLimitLaw` has no `.olean` in `.lake/build`: `import MlmcLean.MarkovLimitLaw` fails, and `import MlmcLean` does not contain these names (`sigs.out`, `sigs2.out`).
   - So I could not cross-check the packet against the compiled theorems. I only confirmed that all 14 packet statements elaborate against the built definitions (`scratch_packet.out`).
   - Please confirm that CI builds this module and that `scripts/AxiomCheck.lean` lists these theorems.
3. **Verdict.** All 14 statements are true and satisfiable (the half-step instance satisfies every hypothesis). None depends on a junk value.
4. **Uniqueness is claimed among all Borel probability measures, and that is correct.** Theorems #6, #7, #8 and #11 put no moment condition on $\pi,\pi_1,\pi_2,\pi'$.
   - No moments are needed: run the chains with the same noise; the conditional Markov inequality plus dominated convergence give convergence in probability.
   - Example: Cauchy AR(1) with $p=1/2$ satisfies the hypotheses, and its invariant law has no mean.
5. **The moment hypothesis `hc` ($c<\infty$).**
   - Necessary wherever `.toReal` of $c$ appears (#2–#4, #12–#14). Without it the RHS becomes $0$ and the claims are false: a Cauchy AR(1) counterexample is in `hc_necessity.out`.
   - Necessary for existence in #8.
   - Superfluous in #5 (given `hX`), #6 and #7.
   - #1 has no `hc`, and that is fine. When $c=\infty$ its RHS is $\infty$, except when $\rho=0$ and $n\ge1$; there the ENNReal $0\cdot\infty=0$ makes the RHS $0$, and the claim is still true.
6. **`hγ1 : γ ≤ 1` is essential for the constant $4/(1-\rho)^2$.** For $\gamma=1.1$ the bound fails for the deterministic map $x\mapsto ax$ (ratio 3.0; `const_check.out`). The constant is sharp at $\gamma=1$ (ratio $\to1$ as $a\to1$).
7. **Some hypotheses are superfluous but harmless.**
   - `[CompleteSpace α]` in #5, #6, #7 and #14. It is needed only for existence (#8).
   - `hfm`: it follows from the Hölder condition, because $f$ is continuous.
   - `hN : Monotone N` in #12: the bounds only use $\min(N_\ell,N_{\ell-1})\ge a(\ell-1)$.
   - $\delta$ in #14: it only serves as a witness that $\beta>0$.
8. **Modelling choices.**
   - $f$ is Hölder with constant 1, and its exponent $\gamma$ is tied to the contraction exponent $2\gamma$.
   - The cost in #13 and #14 charges $N_\ell$ per level-$\ell$ sample. It does not charge the $N_{\ell-1}$ steps of the coarse path or the evaluation of $f$. With $N$ monotone this is within a factor 2, which $c_4$ absorbs.
9. **Conventions that could hide junk values are all genuine here:** `variance` (= `toReal` of `evariance`), Bochner integrals, `Measure.map` (which is $0$ for a non-AE-measurable map), and `Measure.infinitePi` (which is $0$ unless every factor is a probability measure).
   - I proved in Lean (`nonjunk.out`) that $X$ is AE-measurable, that $\nu$ is a probability measure (from `hlaw`+`hξm`), and that $p_\ell>0$. Square integrability follows from Hölder plus `hc`.
   - However, the variance and second-moment bounds in #12 and the MSE bound in #14 do not themselves certify square integrability. #13 does certify `MemLp 2`.

## Notation and standing hypotheses

- $\varphi_e(x):=\varphi(x,e)$.
- `backIter φ n e x` $=B_n(e,x)=\varphi_{e_0}\circ\varphi_{e_1}\circ\cdots\circ\varphi_{e_{n-1}}(x)$, with $B_0=x$. This is coupling from the past: the newest noise $e_0$ is applied last. Checked by `rfl` in `semantics.lean`.
- `fwdIter φ n e x` $=F_n(e,x)=\varphi_{e_{n-1}}\circ\cdots\circ\varphi_{e_0}(x)$, the ordinary forward chain.
- $Y_n(\omega):=B_n((\xi_k(\omega))_k,x_0)$.
- $c:=\int_E d(x_0,\varphi(x_0,e))^{2\gamma}\,\nu(de)\in[0,\infty]$ and $C:=4c/(1-\rho)^2$.

**(S) Standing hypotheses.**
- $(\alpha,d)$ is a second-countable metric space with its Borel $\sigma$-algebra.
- $E$ is an arbitrary measurable space, and $(\Omega,\mu)$ is a probability space.
- $\nu$ is a measure on $E$. There is no instance, but (L) forces $\nu$ to be a probability measure.
- $\varphi:\alpha\times E\to\alpha$ is jointly measurable (`hφm`).
- (C$_q$) contraction on average: $\forall x,y$, $\int d(\varphi(x,e),\varphi(y,e))^{q}\,d\nu\le\rho\,d(x,y)^{q}$ in $[0,\infty]$. Here $q=2\gamma$ unless stated otherwise.
- (I) the $\xi_k$ are measurable and mutually independent (`iIndepFun`).
- (L) each $\xi_k$ has law $\nu$.
- $0<\gamma\le1$ and $0\le\rho<1$.
- (A) $X:\Omega\to\alpha$ is arbitrary (no measurability assumed) and $Y_n\to X$ $\mu$-a.s.

**Further hypotheses.**
- (M) = `hc`: $c<\infty$.
- (H) = `hfm`+`hf`: $f:\alpha\to\mathbb R$ is measurable and $|f(x)-f(y)|\le d(x,y)^\gamma$.

**Lean conventions.** Every `^` with a real exponent is `Real.rpow` with base $\ge0$ and exponent $>0$, so no `rpow` junk arises. `ρ ^ n` and `Real.sqrt ρ ^ n` $=(\sqrt\rho)^n$ are natural-number powers.

**Satisfying instance ("H½").** This instance satisfies all hypotheses; I use it for the vacuity checks.
- $\alpha=E=\mathbb R$, $\varphi=$`halfStep` ($x/2+e$), $\nu=$`fairCoin`.
- $\gamma=1$ and $\rho=1/4$, since $\int|x/2+e-y/2-e|^2d\nu=|x-y|^2/4$.
- $x_0=0$, so $c=\mathbb E\xi^2=1/2$.
- $\Omega=\mathbb R^{\mathbb N}$ with `infinitePi fairCoin`, $\xi_k$ the coordinates, and $X=\sum_k\xi_k2^{-k}$.
- $f=\mathrm{id}$.
- For #12–#14: $N_\ell=\ell$, $a=b=1$, $\beta=2$ (then $\rho^a=2^{-\beta}$), $\delta=1$.
- For #13, add an independent geometric $K$ on $\Omega\times\mathbb N$.

---

### 1. `lintegral_dist_limit_le`

**Rendering.** Assume (S), without (M). Then for every $n\in\mathbb N$:
$$\int^- d(Y_n,X)^{2\gamma}\,d\mu\;\le\;\rho^n\cdot\frac{4}{(1-\rho)^2}\cdot c\quad\text{in }[0,\infty].$$
The arithmetic is ENNReal, so $0\cdot\infty=0$.

**Assessment.**
- *Truth: true.* Let $p=2\gamma\in(0,2]$ and $D_k=d(Y_k,Y_{k+1})$.
  - We have $Y_k=\Phi_k(x_0)$ and $Y_{k+1}=\Phi_k(\varphi(x_0,\xi_k))$, where $\Phi_k=\varphi_{\xi_0}\circ\cdots\circ\varphi_{\xi_{k-1}}$ is independent of $\xi_k$.
  - Iterating (C) with independence and Fubini gives $\mathbb E D_k^p\le\rho^kc$.
  - Almost surely $d(Y_n,X)\le\sum_{k\ge n}D_k$.
  - If $p\le1$, subadditivity gives the bound $\rho^nc/(1-\rho)$.
  - If $1<p\le2$, Minkowski gives $c\rho^n/(1-\rho^{1/p})^p\le c\rho^n(2/(1-\rho))^p\le4c\rho^n/(1-\rho)^2$, using $1-\rho^{1/p}\ge1-\sqrt\rho\ge(1-\rho)/2$.
- *Numerical check.*
  - The tail constant stays below $4/(1-\rho)^2$ on the whole grid (maximum ratio 0.9995).
  - Random-coefficient linear chains: maximum ratio 0.99989 at $p=2$, 0.21 at $p=1$, 0.13 at $p=1/2$ (`const_check.out`, `linear_chain_check.out`).
  - The constant is sharp at $\gamma=1$.
  - For the deterministic map $x\mapsto ax$ the bound fails when $\gamma>1$ (ratios 3.0, 18.4 and 296 for $\gamma=1.1, 1.5, 2$), so `hγ1` is essential.
- *Vacuity:* not vacuous (H½).
- *Junk values.*
  - If $c=\infty$ and $\rho>0$ (or $n=0$), the RHS is $\infty$ and the statement is trivial. That is the natural reading of an ENNReal inequality.
  - If $\rho=0$, $n\ge1$ and $c=\infty$, then $0\cdot\infty=0$ makes the RHS $0$, and the claim becomes "LHS $=0$". This is still true:
    - $\rho=0$ forces $\varphi(x,\cdot)=\varphi(y,\cdot)$ $\nu$-a.e. for each pair $(x,y)$.
    - $Y_m=\varphi(Y'_{m-1},\xi_0)$ with $Y'_{m-1}$ independent of $\xi_0$, so by Fubini $Y_m=Y_n$ a.s. for all $m,n\ge1$, and hence $X=Y_n$ a.s.
  - $X$ is not assumed measurable, but it is AE-measurable as an a.e. limit (checked in Lean).
- *Hypotheses:* no finiteness assumption is needed, and that is correct.
- *Standard result:* geometric $L^p$ contraction of backward iterates for random maps that contract on average (Diaconis–Freedman 1999; Wu–Shao 2004; Glynn–Rhee 2014).

### 2. `sq_integral_sub_limit_le`

**Rendering.** Assume (S), (M) and (H). Then for every $n$:
$$\Big(\int f(Y_n)\,d\mu-\int f(X)\,d\mu\Big)^2\le\frac{4}{(1-\rho)^2}\,c\,\rho^n.$$

**Assessment.**
- *Truth: true.*
  - Jensen gives $(\mathbb E[f(Y_n)-f(X)])^2\le\mathbb E|f(Y_n)-f(X)|^2\le\mathbb E\,d(Y_n,X)^{2\gamma}$; then apply #1.
  - Both integrals are genuine: $f(y)^2\le2f(x_0)^2+2d(y,x_0)^{2\gamma}$, and $\mathbb E\,d(Y_n,x_0)^{2\gamma}$ and $\mathbb E\,d(X,x_0)^{2\gamma}$ are both $\le C<\infty$.
- *Vacuity:* not vacuous (H½).
- *Junk values:* none.
- *Hypotheses.*
  - (M) is necessary. Without it `toReal ∞ = 0` gives RHS $0$.
    - Counterexample: $x/2+e$ with Cauchy noise, $\gamma=1/2$, $f=\sqrt{|\cdot|}$. The LHS is $0.343>0$ at $n=1$ (`hc_necessity.out`).
  - `hfm` is redundant, since Hölder implies continuous.
- *Standard result:* geometric bias bound for Hölder observables.

### 3. `abs_integral_sub_limit_le` (conclusion from v2)

**Rendering.** Same hypotheses as #2. For every $n$:
$$\Big|\int f(Y_n)\,d\mu-\int f(X)\,d\mu\Big|\le\frac{2}{1-\rho}\sqrt{c}\,(\sqrt\rho)^n.$$

**Assessment.**
- *Truth: true.* Take the square root of #2, using $\sqrt{\rho^n}=(\sqrt\rho)^n$.
- *Vacuity:* not vacuous.
- *Junk values:* none.
- *Hypotheses:* the same remarks as #2 apply.
- *Standard result:* the same bias bound as #2, in absolute-value form.

### 4. `abs_integral_fwdIter_sub_limit_le` (conclusion from v2)

**Rendering.** Same hypotheses as #2. For every $N$:
$$\Big|\int f\big(F_N(\xi,x_0)\big)\,d\mu-\int f(X)\,d\mu\Big|\le\frac{2}{1-\rho}\sqrt{c}\,(\sqrt\rho)^N.$$
Here $F_N(\xi,x_0)=\varphi_{\xi_{N-1}}\circ\cdots\circ\varphi_{\xi_0}(x_0)$ is the ordinary chain started at $x_0$. $X$ is still the backward limit.

**Assessment.**
- *Truth: true.* $(\xi_0,\dots,\xi_{N-1})$ and its reversal have the same law, so $F_N(\xi,x_0)\overset{d}{=}Y_N$; then apply #3.
- *Numerical check:* for the half-step chain the forward and backward laws are identical for $n\le14$ (`halfstep_law.out`).
- *Vacuity:* not vacuous.
- *Junk values:* none.
- *Standard result:* geometric convergence of $\mathbb E f(X_N)$ to the stationary mean.

### 5. `map_limit_invariant`

**Rendering.** Assume `[CompleteSpace α]`, (S) and (M). Let $\pi:=\mu\circ X^{-1}$. Then
$$(\pi\otimes\nu)\circ\varphi^{-1}=\pi,$$
that is, $\pi P=\pi$ for the kernel $P(x,\cdot)=\mathrm{law}\,\varphi(x,\xi)$.

**Assessment.**
- *Truth: true.*
  - $Y_{n+1}=\varphi(Y'_n,\xi_0)$, where $Y'_n$ is built from the shifted noise. $Y'_n\to X'$ a.s., where $X'$ is independent of $\xi_0$ and $X'\overset d=X$.
  - $\varphi(\cdot,e)$ need not be continuous, so the limit is passed inside $\varphi$ using (C) and the conditional Markov inequality with dominated convergence. This gives $\varphi(Y'_n,\xi_0)\to\varphi(X',\xi_0)$ in probability.
  - Hence $X=\varphi(X',\xi_0)$ a.s.
- *Vacuity:* not vacuous (H½).
- *Junk values:* none. `μ.map X` would be $0$ if $X$ were not AE-measurable, but $X$ is AE-measurable (`nonjunk.lean`).
- *Hypotheses:* given `hX`, (M) is not needed, because the argument above uses no moments. Completeness at most helps with the measurability of $X'$. Both are harmless.
- *Standard result:* Letac's principle, i.e. the coupling-from-the-past limit is stationary.

### 6. `map_limit_eq_of_invariant`

**Rendering.** Assume `[CompleteSpace α]`, some real $p>0$, $0\le\rho<1$, (C$_p$), (I), (L), and a finite $p$-moment $\int d(x_0,\varphi(x_0,e))^p\,d\nu<\infty$. Let $X$ be the a.s. limit of $Y_n$. Let $\pi$ be **any** Borel probability measure on $\alpha$ with $(\pi\otimes\nu)\circ\varphi^{-1}=\pi$. Then $\mu\circ X^{-1}=\pi$.

**Assessment.**
- *Truth: true, with no moment condition on $\pi$.*
  - Take $Z\sim\pi$ independent of the noise. Then $B_n(\xi,Z)\sim\pi P^n=\pi$.
  - For each $z$, $\mathbb E\,d(B_n(\xi,x_0),B_n(\xi,z))^p\le\rho^nd(x_0,z)^p$. Markov's inequality and dominated convergence then give $d(B_n(\xi,x_0),B_n(\xi,Z))\to0$ in probability.
  - Hence $B_n(\xi,Z)\to X$ in probability, so $\mathrm{law}(X)=\pi$.
- *Vacuity:* not vacuous (H½ with $\pi=$ `uniform02`).
- *Junk values:* none.
- *Hypotheses:* the moment hypothesis and completeness are both superfluous but harmless.
- *Standard result:* uniqueness of the stationary law under contraction on average.

### 7. `invariant_unique`

**Rendering.** Assume `[CompleteSpace α]`, $p>0$, $0\le\rho<1$, (C$_p$), $\nu$ a probability measure, and some $x_0$ with a finite one-step $p$-moment. Then any two Borel probability measures $\pi_1,\pi_2$ with $\pi_iP=\pi_i$ are equal. No moment condition is placed on $\pi_i$.

**Assessment.**
- *Truth: true.* Couple both chains through the same noise from $(Z_1,Z_2)\sim\pi_1\otimes\pi_2$. The same convergence-in-probability argument as #6 applies, and bounded Lipschitz test functions determine the measures.
- *Example:* Cauchy AR(1) with $p=1/2$ satisfies the hypotheses ($c=\sqrt2$), and its unique invariant law has no mean. So uniqueness really does range over heavy-tailed laws.
- *Vacuity:* not vacuous.
- *Junk values:* none.
- *Hypotheses:* the moment hypothesis and completeness are superfluous.
- *Standard result:* uniqueness of the invariant measure for an iterated random function system that contracts on average.

### 8. `existsUnique_invariant`

**Rendering.** Assume `[CompleteSpace α]`, (C$_{2\gamma}$), $\nu$ a probability measure, $0<\gamma\le1$, $0\le\rho<1$ and (M). Then there is a probability measure $\pi$ such that:
1. $\pi P=\pi$;
2. $\int^- d(y,x_0)^{2\gamma}\,d\pi<\infty$;
3. every probability measure $\pi'$ with $\pi'P=\pi'$ equals $\pi$.

**Assessment.**
- *Truth: true.*
  - Existence: build i.i.d. noise with `infinitePi`; the backward limit exists by completeness and Borel–Cantelli; then apply #5.
  - The moment is $\le C$ by #1 with $n=0$.
  - Uniqueness holds among all probability measures, as in #7.
- *Vacuity:* not vacuous.
- *Junk values:* none.
- *Hypotheses:* completeness and (M) are really needed for existence.
  - Completeness: on $(0,1]$ with $x\mapsto x/2$, no invariant probability measure exists.
  - Moments: AR(1) with $\mathbb E\log^+|e|=\infty$ has no stationary law.
  - $\gamma\le1$ loses no generality, since Jensen lowers any exponent.
- *Standard result:* existence and uniqueness of the stationary law (Letac 1986; Diaconis–Freedman 1999).

### 9. `map_limit_halfStep`

**Rendering.** Let $\xi_k$ be i.i.d. fair coins on $\{0,1\}$ (as `fairCoin` measures on $\mathbb R$). Take any $x_0\in\mathbb R$ and any $X$ with $B_n(\xi,x_0)=x_02^{-n}+\sum_{k<n}\xi_k2^{-k}\to X$ a.s. Then $\mathrm{law}(X)=$ `uniform02` $=\tfrac12\,\mathrm{Leb}|_{(0,2]}$, which is the uniform law on $[0,2]$.

**Assessment.**
- *Truth: true.* $X=\sum_k\xi_k2^{-k}$ a.s. is a binary expansion with fair digits.
- *Numerical check:* the KS distance to $U[0,2]$ is at most $1.6\cdot10^{-4}$ at $n=14$ for $x_0\in\{0,5,-3/7\}$ (`halfstep_law.out`).
- *Vacuity:* not vacuous.
- *Junk values:* none.
- *Standard result:* the uniform law as the Bernoulli convolution with ratio $1/2$.

### 10. `halfStep_limit_uniform`

**Rendering.** Under the coin hypotheses there exists $X$ such that:
1. $\mathrm{law}(X)=$ `uniform02`;
2. $B_n(\xi,0)\to X$ a.s.;
3. the forward chain $F_n(\xi,0)$ converges to $X$ in distribution (`TendstoInDistribution`).

Point 3 means: each $F_n$ is AE-measurable, $X$ is AE-measurable, and the laws converge weakly in `ProbabilityMeasure ℝ`.

**Assessment.**
- *Truth: true.* The forward and backward laws are equal at every $n$, and the backward chain converges a.s.
- The forward chain does not converge pathwise: on the alternating path it oscillates between $4/3$ and $2/3$ (`halfstep_law.out`). Convergence in distribution is therefore the right notion.
- *Vacuity:* not vacuous.
- *Junk values:* none.
- *Standard result:* the Propp–Wilson contrast between forward and backward iteration.

### 11. `halfStep_invariant_unique`

**Rendering.** Any probability measure $\pi$ on $\mathbb R$ with $(\pi\otimes\text{fairCoin})\circ(x,e\mapsto x/2+e)^{-1}=\pi$ equals `uniform02`. The `omit [IsProbabilityMeasure μ]` line is irrelevant, since $\mu$ does not appear.

**Assessment.**
- *Truth: true*, among all probability measures. Two proofs:
  - by #7;
  - by characteristic functions: $\hat\pi(t)=\hat\pi(t/2)\tfrac{1+e^{it}}2$, so $\hat\pi(t)=\prod_{k\ge0}\tfrac{1+e^{it2^{-k}}}{2}=e^{it}\tfrac{\sin t}{t}$ (Viète), which is the characteristic function of $U[0,2]$.
- *Numerical check:* exact invariance on a rational grid (`halfstep_law.out`).
- *Vacuity:* not vacuous.
- *Junk values:* none.

### 12. `markov_mlmc_rates`

**Rendering.** Assume (S), (M) and (H). Let $N:\mathbb N\to\mathbb N$ be monotone and $a\in\mathbb N$ with $a\ell\le N_\ell$. Let $\beta\ge0$ with $\rho^a\le2^{-\beta}$. Put $P_\ell=f(Y_{N_\ell})$, $\Delta_0=P_0$ and $\Delta_\ell=P_\ell-P_{\ell-1}$. Then for all $\ell$:
1. $|\mathbb E[P_\ell-f(X)]|\le\frac{2}{1-\rho}\sqrt c\,2^{-\beta\ell/2}$;
2. $\mathrm{Var}(\Delta_\ell)\le2^\beta C\,2^{-\beta\ell}$;
3. $\mathbb E\Delta_\ell^2\le\big(2f(x_0)^2+(2+2^\beta)C\big)2^{-\beta\ell}$.

**Assessment.**
- *Truth: true.*
  - (1): apply #3 with $\rho^{N_\ell}\le\rho^{a\ell}\le2^{-\beta\ell}$.
  - For $m\ge n$, $\mathbb E\,d(Y_m,Y_n)^{2\gamma}\le C\rho^n$, by the tail argument of #1 over $k\in[n,m)$.
  - Level 0: $\mathrm{Var}\,P_0\le\mathbb E(P_0-f(x_0))^2\le C\le2^\beta C$, and $\mathbb E P_0^2\le2f(x_0)^2+2C$.
  - Level $\ell\ge1$: $\mathbb E\Delta_\ell^2\le C\rho^{\min(N_\ell,N_{\ell-1})}\le C2^{-\beta(\ell-1)}=2^\beta C\,2^{-\beta\ell}$.
- *Numerical check:* the H½ instance satisfies all three bounds for $\ell\le39$ (`mlmc_check.out`).
- *Vacuity:* not vacuous.
- *Junk values:* none. `variance` and the Bochner integral are genuine, because the levels are in $L^2$.
- *Hypotheses:* `hN` (monotone) is not needed.
- *Standard result:* the MLMC level conditions (bias rate $\beta/2$, variance rate $\beta$) of Giles 2008, Theorem 1.

### 13. `markov_randomised_mlmc`

**Rendering.** Assume the hypotheses of #12 without $\beta\ge0$, plus:
- $b$ with $N_\ell\le b(\ell+1)$;
- $0<\delta<\beta$;
- $K:\Omega\to\mathbb N$ measurable and independent of the whole sequence $(\xi_k)_k$, with $\mu(K=\ell)=p_\ell:=(1-r)r^\ell$ where $r=2^{-(\beta+\delta)/2}$.

Let $Z=p_K^{-1}\Delta_K$ (this is `singleTerm`, recovered via `#print`). Then:
1. $Z\in L^1$;
2. $\mathbb E Z=\mathbb E f(X)$;
3. $Z\in L^2$;
4. $N_K\in L^1$;
5. $\mathbb E N_K=\sum_\ell p_\ell N_\ell$.

**Assessment.**
- *Truth: true.*
  - $\mathbb E|Z|=\sum_\ell\mathbb E|\Delta_\ell|<\infty$.
  - $\mathbb E Z=\sum_\ell\mathbb E\Delta_\ell=\lim_L\mathbb E P_L=\mathbb E f(X)$. The hypotheses force $a\ge1$, since $\beta>0$.
  - $\mathbb E Z^2=\sum_\ell\mathbb E\Delta_\ell^2/p_\ell$ is finite because $2^{-\beta}/r=2^{-(\beta-\delta)/2}<1$.
  - $\sum_\ell p_\ell b(\ell+1)<\infty$.
- *Numerical check (H½, exact):* $\sum_\ell p_\ell=1$, $\sum_\ell\mathbb E\Delta_\ell=1=\mathbb E X$, $\mathbb E Z^2=7.469$. At $\delta=\beta$ the ratio of consecutive terms is exactly 1, so the series diverges (`mlmc_check.out`). Hence `hδβ` is needed, and `hNb` is needed for finite cost.
- *Vacuity:* not vacuous.
- *Junk values:* none. $p_\ell>0$ (proved in Lean), so there is no $x/0$; the `tsum` is summable.
- *Standard result:* the Rhee–Glynn unbiased single-term estimator (Glynn–Rhee 2014, Markov-chain equilibrium).

### 14. `markov_mlmc_theorem1`

**Rendering.** Assume the hypotheses of #13 without $K$, plus `[CompleteSpace α]`. Then there is $c_4>0$ (independent of $\varepsilon$) such that for every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb N$ and $M:\mathbb N\to\mathbb N_{\ge1}$ with the following properties. On $\big((E^{\mathbb N})^{\mathbb N\times\mathbb N},\ \bigotimes_{(\ell,n)}\nu^{\otimes\mathbb N}\big)$, define the estimator
$$\hat Y(x)=\sum_{\ell\le L}M_\ell^{-1}\sum_{n<M_\ell}\Delta'_\ell(x_{\ell,n}).$$
Here $\Delta'_\ell$ is the level difference of $e\mapsto f(B_{N_\ell}(e,x_0))$, so fine and coarse use the same noise sequence. Then:
- $\mathbb E(\hat Y-\int f(X)\,d\mu)^2<\varepsilon^2$;
- $\mathbb E[\text{cost}]=\sum_{\ell\le L}M_\ell N_\ell\le c_4\varepsilon^{-2}$.

**Assessment.**
- *Truth: true.* This is Giles' theorem with bias rate $\beta/2$, variance rate $\beta$, and cost $N_\ell\le b(\ell+1)$ growing sub-exponentially. That gives $O(\varepsilon^{-2})$; the $O(\log^2(1/\varepsilon))$ ceiling overhead is absorbed for $\varepsilon<1/e$.
- *Numerical check (H½, exact):* MSE/$\varepsilon^2\in[0.63,0.87]$ and cost$\cdot\varepsilon^2\to3.63$ for $\varepsilon$ from $0.3$ down to $10^{-12}$ (`mlmc_check.out`).
- *Vacuity:* not vacuous.
- *Junk values:* none.
  - `infinitePi` would be $0$ if $\nu$ were not a probability measure, but `hlaw` forces $\nu$ to be one (proved in Lean).
  - The MSE integrand is in $L^2$, so the Bochner integral is genuine.
- *Hypotheses.*
  - $\delta$ only encodes $\beta>0$.
  - Completeness is unnecessary.
  - The cost model ignores the coarse path and $f$-evaluations; this is within a factor 2.
- *Standard result:* Giles 2008 Theorem 1 / Cliffe–Giles–Scheichl–Teckentrup 2011, for invariant-measure expectations.

## Supporting definitions (rendered)

- **`backIter`** $=B_n$ and **`fwdIter`** $=F_n$, as above.
- **`halfStep`** $(x,e)\mapsto x/2+e$.
- **`fairCoin`** $=\tfrac12\delta_0+\tfrac12\delta_1$.
- **`uniform02`** $=\tfrac12\,\mathrm{Leb}|_{(0,2]}$.
- **`levelDiff`** $P$: $\Delta_0=P_0$, $\Delta_{\ell+1}=P_{\ell+1}-P_\ell$.
- **`levelEstimator`** $=N^{-1}\sum_{n<N}\Delta_\ell(\omega(\ell,n)x)$. With $N=0$ it gives $0^{-1}\cdot0=0$, which #14 excludes by requiring $M_\ell\ge1$.
- **`mlmcEstimator`** $=\sum_{\ell\le L}$ `levelEstimator`.
- **`totalCost`** $=\sum_{\ell\le L}\sum_{n<N_\ell}\mathrm{cost}$.
- **`geomLevelProb`** $\beta\,\gamma\,\ell=(1-2^{-(\beta+\gamma)/2})(2^{-(\beta+\gamma)/2})^\ell$.
- **`singleTerm`** $P\,K\,p\,\omega=p(K\omega)^{-1}\,\Delta_{K\omega}(\omega)$. This one is missing from the packet.

## Scripts (in `readback/round11/work_M8/`)

| File | Contents |
|---|---|
| `const_check` | the $4/(1-\rho)^2$ constant, and the necessity of $\gamma\le1$ |
| `linear_chain_check` | random-coefficient chains at $p=2,1,1/2$ |
| `halfstep_law` | exact laws, forward = backward, invariance, forward non-convergence |
| `mlmc_check` | #12, #13 and #14 on H½ |
| `hc_necessity` | Cauchy counterexample without (M) |
| `sigs`, `sigs2` | definition signatures and `#print singleTerm`; the MarkovLimitLaw olean is missing |
| `scratch_packet` | all 14 v2 statements elaborate |
| `semantics` | definitional checks by `rfl` |
| `nonjunk` | Lean proofs that $X$ is AE-measurable, $\nu$ is a probability measure, and $p_\ell>0$ |
