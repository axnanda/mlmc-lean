# Blind read-back report: `MlmcLean.SDEDigital` (M6)

| Field | Value |
|---|---|
| Date | 2026-09-29 |
| Packet | `readback/round11/packet_M6_sde_digital.lean` |
| Declarations audited | 25: 18 theorems plus the 7 appended definitions (`pairAvg`, `stdNormalSeq`, `gbmEM`, `gbmStrongConst`, `emPath`, `gbmDrift`, `gbmVol`) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round11/work_M6/`: `gbm_strong_const.py/.out`, `gbm_density_and_mc.py/.out`, `digital_mismatch_sharpness.py/.out`, `gaussian_identities.py/.out`, `lipschitz_payoffs.py/.out`, and the Lean elaboration checks `scratch_elab.lean/.out` and `scratch_elab2.lean/.out` (all 18 statements compiled with `sorry` under `import MlmcLean`: no errors) |

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `lipschitz_european_asian_lookback` | theorem | true | no (no hypotheses) | no |
| 2 | `variance_lipschitz_payoff_le` | theorem | true | no | no |
| 3 | `digital_mismatch_le` | theorem | true | no | no |
| 4 | `variance_digital_le` | theorem | true | no | no |
| 5 | `variance_digital_levelDiff_le` | theorem | true | no | no |
| 6 | `variance_digital_rate` | theorem | true | no | no |
| 7 | `digital_mismatch_le_of_tail` | theorem | true | no | no |
| 8 | `digital_mismatch_le_of_moment` | theorem | true | no | no |
| 9 | `gbm_digital_variance_le` | theorem | true | no | no |
| 10 | `integral_digital_final_step` | theorem | true | no | no |
| 11 | `condExp_digital_last_step` | theorem | true | no | no |
| 12 | `digital_smoothing` | theorem | true | no | no |
| 13 | `digital_smoothing_coarse` | theorem | true | no | no |
| 14 | `digital_smoothing_level_zero` | theorem | true | no | no |
| 15 | `gaussian_change_of_measure` | theorem | true | no | no |
| 16 | `integral_mul_likelihoodRatio` | theorem | true | no | no |
| 17 | `integral_mul_sub_likelihoodRatio` | theorem | true | no | no |
| 18 | `hasDerivAt_call_payoff` | theorem | true | no (no hypotheses) | no |
| 19 | `pairAvg` | def | n/a (faithful) | n/a | n/a |
| 20 | `stdNormalSeq` | abbrev | n/a (faithful) | n/a | n/a |
| 21 | `gbmEM` | def | n/a (faithful) | n/a | n/a |
| 22 | `gbmStrongConst` | def | n/a (a valid strong-error constant, checked numerically) | n/a | n/a |
| 23 | `emPath` | def | n/a (faithful) | n/a | n/a |
| 24 | `gbmDrift` | def | n/a (faithful) | n/a | n/a |
| 25 | `gbmVol` | def | n/a (faithful) | n/a | n/a |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement.** All 18 theorems are true. Each has a concrete instance satisfying its hypotheses, and each elaborates as rendered below (checked with scratch copies).
2. **Constants and exponents in the digital bounds (3–6).** The hypothesis is $\mu\{|X-K|\le\delta\}\le 2\rho\delta$ for all $\delta>0$. Under it, the best constant in $\mu(\text{mismatch})\le C\rho^{2/3}(E(X-Y)^2)^{1/3}$ is $C=12^{1/3}\approx 2.289$, so the stated $3$ is valid but about 31% above optimal. The exponent $1/3$ is **sharp**: a uniform $X$ near $K$, with $Y$ pushed just across $K$ on $\{|X-K|\le t\}$, attains the ratio $12^{1/3}$ for every $t$. Because that example's difference has mean 0, the variance bounds are sharp in the exponent too.
3. **The rate is not sharp for Euler–Maruyama.** The rate $h^{1/3}$ in 6 and 9 is sharp only for the abstract lemma. For EM/GBM, Monte Carlo gives $V_\ell$ falling about $0.44$ per level in $\log_2$ over $\ell=2..8$. That is consistent with the known $h^{1/2}$ rate (up to logs, Giles–Higham–Mao) and faster than $h^{1/3}$. The right-hand side of 9 is $\ge 1$, so trivially true, until $\ell\approx 7$–$9$ at typical parameters. It is an asymptotic bound.
4. **Theorem 9 relies on two unstated facts, both checked:**
   - The GBM–EM strong error satisfies $E|S_T-S^{EM}_T|^2\le\texttt{gbmStrongConst}\cdot h$. Using the closed form over 76,670 grid points plus 20,000 random points, the largest ratio is 0.09998. Its asymptote is exactly $1/10$, so there is a factor-10 margin.
   - $\rho$ equals the maximum of the lognormal density of $S_T$ exactly.
5. **`digital_mismatch_le_of_tail` has a stronger hypothesis than it uses.** The Gaussian-tail bound is required for all $\delta>0$ but used only at $\delta=\sqrt{Bh\log(1/h)}$. It is **never** satisfied by GBM–EM errors, whose lognormal tails beat any $Ae^{-\delta^2/(Bh)}$, so this lemma cannot feed Theorem 9. It is satisfiable, for example by $Y=X+\sqrt h\,N$ with $A=1$, $B=2$.
6. **`digital_mismatch_le_of_moment` is not optimised.** Its bound $(2\rho+1)M_p^{1/(p+1)}$ comes from a fixed choice $\delta=M_p^{1/(p+1)}$ and is not scale-invariant. It is true, and has the standard exponent in $M_p$. For $p=0$ it is trivial, and for $p=2$ it is never better than 3(c), by AM–GM.
7. **Generality, all harmless:**
   - Theorem 3 allows any finite measure and non-measurable $X,Y$; Theorem 5 allows a non-measurable $X$. `μ.real` is then outer measure, and the proofs (monotonicity, subadditivity, Markov for an a.e.-measurable $(X-Y)^2$) still hold.
   - The hypothesis `hρ` forces $\rho\ge0$, and $\rho=0$ forces $\mu=0$.
   - In Theorem 13, $h_c$ is unconstrained.
8. **Division by zero only on null sets.** The junk value $\Phi(\cdot/0)=\Phi(0)=1/2$ appears in 11–13 only on sets that the "$s(X)\ne0$ a.s." or "$b(\cdot)\ne0$ a.s." hypotheses make null.

---

## 1. `lipschitz_european_asian_lookback` (theorem)

**Rendering.** Take any $n\in\mathbb N$ and $K\in\mathbb R$. Work on $\mathbb R^{n+1}$ with coordinates $x_0,\dots,x_n$ (`Fin.last n` $=n$), using Mathlib's product metric $d(x,y)=\max_i|x_i-y_i|$ (the sup norm). Each map below is `LipschitzWith` the stated constant, i.e. $|f(x)-f(y)|\le L\|x-y\|_\infty$ for all $x,y$:

- (i) $(x_n-K)^+$ with $L=1$;
- (ii) $\big(\tfrac1{n+1}\sum_{i=0}^n x_i-K\big)^+$ with $L=1$, where the divisor elaborates to the real number $(n:\mathbb R)+1$;
- (iii) $(\max_i x_i-K)^+$ with $L=1$;
- (iv) $x_n-\min_i x_i$ with $L=2$;
- (v) $\max_i x_i-x_n$ with $L=2$.

**Assessment.** True. We have $|a^+-b^+|\le|a-b|$, and each of $|x_n-y_n|$, $|\bar x-\bar y|$, $|\max x-\max y|$, $|\min x-\min y|$ is at most $\|x-y\|_\infty$. Parts (iv) and (v) then follow from the triangle inequality.

The constants are optimal:
- $1$ is attained.
- $2$ is attained for $n\ge1$, e.g. $x=(0,1)$, $y=(-\varepsilon,1+\varepsilon)$ in (iv).
- For $n=0$, (iv) and (v) are identically 0.

A random search in exact rational arithmetic (`lipschitz_payoffs.py`) found no ratio above the stated constants. There are no hypotheses, so the statement is not vacuous. There is no junk: the only division is by $n+1\ge1$. Standard fact: the European call, arithmetic Asian call, fixed-strike lookback call and floating-strike lookback call and put on a discretely monitored path are Lipschitz in the sup norm of the path. This is the Lipschitz-payoff setting of MLMC (Giles 2008).

## 2. `variance_lipschitz_payoff_le` (theorem)

**Rendering.** Let $(\Omega,\mu)$ be a probability space and $E$ a seminormed additive commutative group. Let $g:E\to\mathbb R$ be $L$-Lipschitz with $L\in\mathbb R_{\ge0}$. Let $S,S_l:\Omega\to E$ be a.e.-strongly measurable with $\|S-S_l\|^2\in L^1(\mu)$. Then
$$\operatorname{Var}\big(g(S)-g(S_l)\big)\le E\big[(g(S)-g(S_l))^2\big]\le L^2\,E\|S-S_l\|^2 .$$

**Assessment.** True. Pointwise $|g(S)-g(S_l)|\le L\|S-S_l\|$. The difference is a.e.-strongly measurable (a continuous map composed with an AE-strongly measurable one) and lies in $L^2$. Then use $\operatorname{Var}\le E[\cdot^2]$ (Mathlib `variance_le_expectation_sq`) and monotonicity of the integral.

Since the difference is in $L^2$, neither `variance`'s junk value $0$ nor a junk Bochner integral is involved. Not vacuous: $E=\mathbb R$, $g=\mathrm{id}$, $S\sim N(0,1)$, $S_l=0$. Standard MLMC fact: for a Lipschitz payoff, $V_\ell\le L^2E\|S-S_\ell\|^2$, i.e. strong convergence gives variance decay. Together with Theorem 1 it covers $E=\mathbb R^{n+1}$ with the sup norm.

## 3. `digital_mismatch_le` (theorem)

**Rendering.** Let $\mu$ be any **finite** measure, not necessarily a probability. Let $X,Y:\Omega\to\mathbb R$ be **arbitrary** functions (no measurability assumed), and $K,\rho\in\mathbb R$.

Hypotheses:
- (hρ) For every $\delta>0$, $\mu\{|X-K|\le\delta\}\le2\rho\delta$. Here `μ.real s` is $(\mu s)$`.toReal`, i.e. the outer measure when the set is not measurable.
- (hint) $(X-Y)^2\in L^1(\mu)$.

Notation:
- $M=\{\omega:\mathbf 1_{(K,\infty)}(X(\omega))\ne\mathbf 1_{(K,\infty)}(Y(\omega))\}$, the event that $X$ and $Y$ lie on different sides of $K$ ("above" means $>K$).
- $D=\int(X-Y)^2\,d\mu$.

Conclusions:
- (a) For all $\delta>0$: $\mu(M)\le2\rho\delta+\mu\{|X-Y|>\delta\}$.
- (b) For all $\delta>0$: $\mu(M)\le2\rho\delta+D/\delta^2$.
- (c) $\mu(M)\le3\rho^{2/3}D^{1/3}$, using `Real.rpow`; here $\rho\ge0$ and $D\ge0$.

**Assessment.** True.

- (a) If $|X-K|>\delta$ and $X,Y$ are on opposite sides of $K$, then $|X-Y|\ge|X-K|>\delta$. So $M\subseteq\{|X-K|\le\delta\}\cup\{|X-Y|>\delta\}$. Outer measure is monotone and subadditive, and $\mu$ is finite, so `toReal` preserves this.
- (b) This is Chebyshev. It is valid for outer measure because $(X-Y)^2$ is a.e.-measurable, being integrable.
- (c) Take $\delta=(D/\rho)^{1/3}$. Then $2\rho\delta+D/\delta^2=3\rho^{2/3}D^{1/3}$ (checked with sympy).

Edge cases:
- `hρ` at $\delta=1$ forces $\rho\ge0$.
- If $\rho=0$, then $\mu\{|X-K|\le n\}=0$ for all $n$, so $\mu=0$ and everything is 0.
- If $D=0$, then $X=Y$ a.e. and (b) gives $\mu(M)=0$.
- $0^{2/3}=0$ is the true value here, not a junk one.

**Constants and sharpness** (`digital_mismatch_sharpness.py`). A mismatch at $X=x$ costs at least $(x-K)^2$ in $D$. Combined with $F(s)=\mu\{|X-K|\le s\}\le2\rho s$, this gives $D\ge\mu(M)^3/(12\rho^2)$, i.e. $\mu(M)\le(12\rho^2D)^{1/3}$. Equality is approached by $X\sim U[K-1,K+1]$ ($\rho=\tfrac12$) with $Y=K$ on $(K,K+t]$, $Y=K+\eta$ on $[K-t,K)$ and $\eta\downarrow0$; the ratio is $2.28943$ for every $t$. So:
- the exponent $1/3$ is sharp;
- the constant $3$ is valid but not optimal (optimum $12^{1/3}\approx2.289$).

Not vacuous: the example above. No junk.

The hypotheses are more general than usual (any finite measure, no measurability), which is harmless. `hρ` is the usual global "density bounded by $\rho$" form; a density bound only near $K$ would not be enough for mid-range $\delta$, which is a minor point. Standard result: Avikainen's (2009) lemma $E|\mathbf 1_{X>K}-\mathbf 1_{Y>K}|\le C(E|X-Y|^q)^{1/(q+1)}$ for $X$ with bounded density (here $q=2$), proved with the $\delta$-splitting of Giles–Higham–Mao (2009).

## 4. `variance_digital_le` (theorem)

**Rendering.** Let $\mu$ be a probability measure, $X,Y$ measurable, with `hρ` and `hint` as in 3. Write $\Delta=\mathbf 1_{X>K}-\mathbf 1_{Y>K}$. Then:
- $\operatorname{Var}(\Delta)\le E[\Delta^2]$;
- $E[\Delta^2]=P(M)$;
- $P(M)\le3\rho^{2/3}D^{1/3}$.

**Assessment.** True. $\Delta\in\{-1,0,1\}$, so $\Delta^2=\mathbf 1_M$ with $M$ measurable, and the equality is exact. The last part is 3(c). Not vacuous; no junk. The exponent is sharp for the variance too: the extremal example of 3 has $E\Delta=0$, so $\operatorname{Var}\Delta=P(M)$. Standard: the digital-payoff variance bound (Avikainen).

## 5. `variance_digital_levelDiff_le` (theorem)

**Rendering.** Let $\mu$ be a probability measure. $Y_1,Y_2$ are measurable; $X$ is **arbitrary** (not assumed measurable), with `hρ` for $X$ and $(X-Y_i)^2\in L^1$ for $i=1,2$. Then
$$\operatorname{Var}\big(\mathbf 1_{Y_1>K}-\mathbf 1_{Y_2>K}\big)\le3\rho^{2/3}\big(D_1^{1/3}+D_2^{1/3}\big),\qquad D_i=E(X-Y_i)^2 .$$

**Assessment.** True. The variance is at most $P(\mathbf 1_{Y_1>K}\ne\mathbf 1_{Y_2>K})$. If $Y_1$ and $Y_2$ disagree, then $X$ disagrees with at least one of them, so this is at most $\mu^*(M_1)+\mu^*(M_2)$. Then apply 3(c) twice; that step does not need $X$ measurable. Not vacuous ($X$ the exact solution, $Y_i$ two approximations). No junk. Standard: the MLMC level-difference bound, routed through the exact solution.

## 6. `variance_digital_rate` (theorem)

**Rendering.** Let $\mu$ be a probability measure.

Hypotheses:
- $X$ measurable, and each $Y_\ell$ ($\ell\in\mathbb N$) measurable;
- $c\ge0$;
- `hρ`;
- $(X-Y_\ell)^2\in L^1$ for all $\ell$;
- $h:\mathbb N\to\mathbb R$ with $h_\ell\ge0$ and $E(X-Y_\ell)^2\le c\,h_\ell$ for all $\ell$.

Conclusions, for every $\ell$:
- (a) $\operatorname{Var}(\mathbf 1_{X>K}-\mathbf 1_{Y_\ell>K})\le3\rho^{2/3}c^{1/3}h_\ell^{1/3}$;
- (b) $\operatorname{Var}(\mathbf 1_{Y_{\ell+1}>K}-\mathbf 1_{Y_\ell>K})\le3\rho^{2/3}c^{1/3}\big(h_{\ell+1}^{1/3}+h_\ell^{1/3}\big)$.

**Assessment.** True. It follows from 4 and 5, using that $t\mapsto t^{1/3}$ is monotone on $[0,\infty)$ and $(ch)^{1/3}=c^{1/3}h^{1/3}$ for $c,h\ge0$. Not vacuous. No junk: every rpow base is $\ge0$.

Standard: strong order $1/2$ in $L^2$ gives the MLMC variance rate $\beta=1/3$ for digital payoffs (Avikainen). That exponent is sharp for the abstract statement but **not** for Euler–Maruyama, where $\beta\approx1/2$ (see 9).

## 7. `digital_mismatch_le_of_tail` (theorem)

**Rendering.** Let $\mu$ be a probability measure, $X,Y$ measurable, and $K,\rho,A,B,h$ reals with $B>0$ and $0<h<1$. Assume `hρ` and

(htail) for every $\delta>0$, $P(|X-Y|>\delta)\le A\,e^{-\delta^2/(Bh)}$.

Then $\operatorname{Var}(\mathbf 1_{X>K}-\mathbf 1_{Y>K})\le P(M)$ and $P(M)\le2\rho\sqrt{Bh\log(1/h)}+Ah$.

**Assessment.** True. Apply 3(a) with $\delta=\sqrt{Bh\log(1/h)}$, which is positive because $\log(1/h)>0$ for $h<1$ (no junk log or sqrt). Then $Ae^{-\log(1/h)}=Ah$ (sympy). The variance part is $\operatorname{Var}\le E\Delta^2=P(M)$.

Not vacuous: take $X\sim U[K-1,K+1]$ ($\rho=\tfrac12$) and $Y=X+\sqrt h\,N$ with $N\sim N(0,1)$ independent. Then $P(|X-Y|>\delta)=2Q(\delta/\sqrt h)\le e^{-\delta^2/(2h)}$, so $A=1$, $B=2$ work (numerically $\max_u 2Q(u)e^{u^2/2}=1$). The hypothesis forces $A\ge0$.

**Hypothesis stronger than needed.** `htail` is required for every $\delta$ but used at a single $\delta$. It also **fails for every $A,B$ when $Y$ is the EM approximation of GBM**. The error then has lognormal tails, of order $e^{-c(\log\delta)^2}$. For example, with one step and $A=10^6$, $B=100$, the tail bound is already violated at $\delta=100$ (`digital_mismatch_sharpness.py`). So this lemma is not a route to Theorem 9. Standard: the Giles–Higham–Mao $\delta$-splitting with sub-Gaussian error tails, giving an $O(\sqrt{h\log(1/h)})$ mismatch probability.

## 8. `digital_mismatch_le_of_moment` (theorem)

**Rendering.** Let $\mu$ be a probability measure, $X,Y$ measurable, with `hρ`. Let $p\in\mathbb N$ with $|X-Y|^p\in L^1$ (a natural-number power), and write $M_p=E|X-Y|^p$. Then $\operatorname{Var}(\Delta)\le P(M)$ and
$$P(M)\le(2\rho+1)\,M_p^{1/(p+1)},$$
where the exponent is the real number $1/((p:\mathbb R)+1)$.

**Assessment.** True. For $p\ge1$, Markov gives $P(|X-Y|>\delta)\le M_p/\delta^p$. Putting $\delta=M_p^{1/(p+1)}$ into 3(a) gives $(2\rho+1)M_p^{1/(p+1)}$ (sympy).

Edge cases:
- $M_p=0$: then $X=Y$ a.s. and both sides are 0.
- $p=0$: then $M_0=1$ and the right-hand side is $2\rho+1\ge1$, so the claim is trivially true. This is not a junk value.

The bound is not optimised and not scale-invariant. The optimum over $\delta$ is $\frac{p+1}{p^{p/(p+1)}}(2\rho)^{p/(p+1)}M_p^{1/(p+1)}$. For $p=2$, AM–GM gives $2\rho+1\ge3\rho^{2/3}$, so the result is never better than 3(c). The exponent in $M_p$ is the standard one, so the rate conclusion $V_\ell=O(h^{p/(2(p+1))})$ from strong $L^p$ order $1/2$ is standard (Avikainen; Giles–Higham–Mao). Not vacuous; no junk.

## 9. `gbm_digital_variance_le` (theorem)

**Rendering.** Take any $r,\sigma\in\mathbb R$ with $\sigma\ne0$, $s_0\ne0$, $T>0$, $K\in\mathbb R$ and $\ell\in\mathbb N$. Work on $(\mathbb R^{\mathbb N},\bigotimes N(0,1))$ (`stdNormalSeq`), with $z=(z_i)$ i.i.d. standard normal. The two approximations of geometric Brownian motion $dS=rS\,dt+\sigma S\,dW$, $S_0=s_0$, at time $T$ are:
- **Fine:** Euler–Maruyama with $2^{\ell+1}$ steps of size $h_f=T/2^{\ell+1}$, driven by $z_0,\dots,z_{2^{\ell+1}-1}$:
  $$S^f=s_0\prod_{i<2^{\ell+1}}\big(1+rh_f+\sigma\sqrt{h_f}\,z_i\big).$$
- **Coarse:** EM with $2^\ell$ steps of size $h_c=T/2^\ell$, driven by $(z_{2k}+z_{2k+1})/\sqrt2$. This is the correct MLMC coupling: both paths use the same Brownian increments.

Then
$$\operatorname{Var}\big(\mathbf 1_{S^f>K}-\mathbf 1_{S^c>K}\big)\le3\rho^{2/3}C^{1/3}\big(h_f^{1/3}+h_c^{1/3}\big),$$
where
- $\rho=\dfrac{e^{(\sigma^2-r)T}}{\sqrt{2\pi}\,|s_0|\,|\sigma|\sqrt T}$;
- $C=\texttt{gbmStrongConst}(r,\sigma,T,s_0)=s_0^2e^{(2|r|+\sigma^2)T}(|r|+\sigma^2)\big(5(|r|+\sigma^2)T+4\big)$.

**Assessment.** True. The proof route and its numerical checks:

1. Let $X=s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt{h_f}\sum_{i<2^{\ell+1}}z_i\big)$, the exact GBM value at $T$ driven by the same increments. It is the same for the coarse path, since $\sqrt{h_c}\sum_k(z_{2k}+z_{2k+1})/\sqrt2=\sqrt{h_f}\sum_i z_i$.
2. $X$ is $s_0$ times a lognormal variable. Its density is maximal at the mode, and that maximum equals $\rho$ exactly; this was confirmed numerically, including for $s_0<0$. Hence $P(|X-K|\le\delta)\le2\rho\delta$ (worst ratio over a $(K,\delta)$ grid is 1.0; `gbm_density_and_mc.py`).
3. With $n$ steps of size $h$, the closed form is
   $$E|X-S^{EM}_n|^2=s_0^2\Big(e^{(2r+\sigma^2)T}+\big((1+rh)^2+\sigma^2h\big)^n-2\big(e^{rh}(1+rh+\sigma^2h)\big)^n\Big).$$
   It was checked against 1-D and 2-D quadrature. It stays $\le C h$ for every $n=2^j$: over 76,670 grid points and 20,000 random points the largest ratio is 0.09998. The asymptote is exactly $1/10$, reached as $r=0$, $\sigma^2T\to\infty$, $h\to0$ (`gbm_strong_const.py`).
4. Apply 5 (equivalently 6(b)).

Monte Carlo check with $r=0$, $\sigma=0.2$, $T=1$, $s_0=K=1$ and $4\times10^4$ paths per level:

| $\ell$ | $V_\ell$ (MC) | stated RHS |
|---|---|---|
| 0 | 0.020 | 4.90 |
| 8 | 0.0021 | 0.77 |

The inequality holds with a wide margin at every level from 0 to 8.

Not vacuous: the only hypotheses are $s_0\ne0$, $\sigma\ne0$, $T>0$. No junk: every rpow base is $>0$ and $\sqrt T$ has $T>0$.

Remarks:
- The right-hand side is $\ge1$, so the claim is trivial, for $\ell\lesssim7$–$9$ at typical parameters. It is meaningful only asymptotically.
- The rate $h^{1/3}$ is **not sharp for EM**. The MC decay is about $0.44$ per level in $\log_2$, consistent with the known $h^{1/2}$ rate up to logs (Giles–Higham–Mao 2009).

Standard: the MLMC variance bound for digital options under the Euler scheme for GBM, via Avikainen's lemma.

## 10. `integral_digital_final_step` (theorem)

**Rendering.** For $x,a,b,h,K\in\mathbb R$ with $b\ne0$ and $h>0$:
$$\int\mathbf 1\{x+ah+b\sqrt h\,z>K\}\,N(0,1)(dz)=\Phi\Big(\frac{x+ah-K}{|b|\sqrt h}\Big),$$
where $\Phi$ is `cdf (gaussianReal 0 1)` (`gaussianReal m v` has variance $v$).

**Assessment.** True. The left side is $P(bZ>(K-x-ah)/\sqrt h)$. For $b<0$ use the symmetry of $Z$; whether the inequality is strict does not matter since $\Phi$ is continuous. Checked for $b$ of both signs to 12 digits (`gaussian_identities.py`). Not vacuous. No junk: $b\ne0$ and $h>0$ rule out division by 0. Standard: the Gaussian tail probability for the last Euler step.

## 11. `condExp_digital_last_step` (theorem)

**Rendering.** Let $(\Omega,\mu)$ be a probability space and $E$ any measurable space. Let $X:\Omega\to E$ and $Z:\Omega\to\mathbb R$ be measurable and independent, with $Z\sim N(0,1)$ (`μ.map Z = gaussianReal 0 1`). Let $m,s:E\to\mathbb R$ be measurable with $s(X)\ne0$ a.s., and $K\in\mathbb R$. Then, with $\sigma(X)$ = `mE.comap X`,
$$E\big[\mathbf 1\{m(X)+s(X)Z>K\}\,\big|\,\sigma(X)\big]=\Phi\Big(\frac{m(X)-K}{|s(X)|}\Big)\quad\text{a.s.}$$

**Assessment.** True.
1. Freezing lemma: independence and joint measurability of $(x,z)\mapsto\mathbf 1\{m(x)+s(x)z>K\}$ give $E[f(X,Z)\mid X]=\varphi(X)$ with $\varphi(x)=E f(x,Z)$.
2. For $s\ne0$, $P(m+sZ>K)=\Phi((m-K)/|s|)$.

On $\{s(X)=0\}$ the right-hand side would be the junk $\Phi(0)=1/2$, but that set is null by `hs0`. Not vacuous. Standard: the Doob–Dynkin/freezing lemma plus the Gaussian conditional probability.

## 12. `digital_smoothing` (theorem)

**Rendering.** Let $\mu$ be a probability measure. Let $X,Z$ be real, measurable and independent, with $Z\sim N(0,1)$. Let $a,b:\mathbb R\to\mathbb R$ be measurable with $b(X)\ne0$ a.s., and let $h>0$ and $K\in\mathbb R$. Define
- $Y=\mathbf 1\{X+a(X)h+b(X)\sqrt h\,Z>K\}$, the digital payoff after one Euler step from $X$;
- $\tilde Y=\Phi\big(\frac{X+a(X)h-K}{|b(X)|\sqrt h}\big)$.

Then:
- (a) $E[Y\mid\sigma(X)]=\tilde Y$ a.s.;
- (b) $E\tilde Y=EY$;
- (c) $\operatorname{Var}\tilde Y\le\operatorname{Var}Y$.

**Assessment.** True.
- (a) is 11 with $m(x)=x+a(x)h$ and $s(x)=b(x)\sqrt h$, so $|s|=|b|\sqrt h$.
- (b) is the tower property.
- (c) is $\operatorname{Var}(E[Y\mid\mathcal G])\le\operatorname{Var}(Y)$ (law of total variance), with $Y$ bounded.

Checked numerically with $X\sim N(1,0.09)$: $E\tilde Y$ equals $EY$ to about 4e-6 (the gap is 2-D quadrature error), and $\operatorname{Var}\tilde Y=0.198\le0.246$. Not vacuous. No junk beyond the null set of 11. Standard: conditional-expectation smoothing of the final timestep for digital options in MLMC (Giles 2008, Milstein-scheme MLMC), i.e. conditional Monte Carlo.

## 13. `digital_smoothing_coarse` (theorem)

**Rendering.** Let $\mu$ be a probability measure. Let $S,W,Z$ be real and measurable, with $(S,W)$ independent of $Z$ and $Z\sim N(0,1)$. Let $a,b$ be measurable with $b(S)\ne0$ a.s. Let $h_c\in\mathbb R$ be **arbitrary**, $h_f>0$, and $K\in\mathbb R$. Then
$$E\big[\mathbf 1\{S+a(S)h_c+b(S)(W+\sqrt{h_f}Z)>K\}\,\big|\,\sigma(S,W)\big]=\Phi\Big(\frac{S+a(S)h_c+b(S)W-K}{|b(S)|\sqrt{h_f}}\Big)\ \text{a.s.}$$

**Assessment.** True. This is 11 with $X=(S,W)$, $m(s,w)=s+a(s)h_c+b(s)w$ and $s'(s,w)=b(s)\sqrt{h_f}$. Checked pointwise in $(s,w)$ to 12 digits.

The statement is more general than its MLMC use, where $h_c=2h_f$ and $W$ is the first fine Brownian increment; that is harmless. Not vacuous; no junk. Standard: the coarse path's final-step conditional expectation given the first fine increment (Giles' treatment of digital options).

## 14. `digital_smoothing_level_zero` (theorem)

**Rendering.** Let $\mu$ be a probability measure and $Z$ measurable with $Z\sim N(0,1)$. Let $S_0,a,b,h_0,K\in\mathbb R$ with $b\ne0$ and $h_0>0$. Write
$$q=\frac{S_0+ah_0-K}{|b|\sqrt{h_0}},\qquad Y=\mathbf 1\{S_0+ah_0+b\sqrt{h_0}Z>K\}.$$
The conditioning σ-algebra is the one generated by the constant map $\omega\mapsto S_0$. Then:
- (a) $E[Y\mid\cdot]=\Phi(q)$ a.s.;
- (b) $\operatorname{Var}(E[Y\mid\cdot])=0$;
- (c) $\operatorname{Var}Y=\Phi(q)(1-\Phi(q))$;
- (d) $\Phi(q)(1-\Phi(q))>0$.

**Assessment.** True.
- The comap of a constant map is $\bot$ (confirmed in Lean with `MeasurableSpace.comap_const`), and $E[Y\mid\bot]=EY=\Phi(q)$ by 10. This gives (a) and (b).
- (c) is the Bernoulli variance.
- (d) holds because $0<\Phi(q)<1$ for every real $q$.

Not vacuous; no junk. Standard: at level 0 (a single step) the smoothed estimator is deterministic, while the plain digital estimator has Bernoulli variance.

## 15. `gaussian_change_of_measure` (theorem)

**Rendering.** Take $m,m'\in\mathbb R$ and variances $v,v'\in\mathbb R_{\ge0}$ with $v\ne0$ and $v'\ne0$. Then:
- (a) $N(m',v')=N(m,v)$`.withDensity` $(z\mapsto\varphi_{m',v'}(z)/\varphi_{m,v}(z))$, with `ENNReal`-valued pdfs and `ENNReal` division;
- (b) $\frac{dN(m',v')}{dN(m,v)}=\varphi_{m',v'}/\varphi_{m,v}$, $N(m,v)$-a.e.

**Assessment.** True.
- (a) $N(m,v)=\lambda$`.withDensity`$(\varphi_{m,v})$, and $\varphi_{m,v}\cdot(\varphi_{m',v'}/\varphi_{m,v})=\varphi_{m',v'}$ because $0<\varphi_{m,v}<\infty$. The pointwise identity was checked to 1e-32.
- (b) follows from (a) by `rnDeriv_withDensity`.

$v,v'\ne0$ is necessary, since `gaussianReal m 0` is a Dirac mass. Not vacuous; no junk. Standard: the Radon–Nikodym derivative between equivalent Gaussians.

## 16. `integral_mul_likelihoodRatio` (theorem)

**Rendering.** Let $v,v'\ne0$ and $g\in L^1(N(m',v'))$, and let $L=\varphi_{m',v'}/\varphi_{m,v}$ (real pdfs). Then $gL\in L^1(N(m,v))$ and $\int gL\,dN(m,v)=\int g\,dN(m',v')$.

**Assessment.** True: $\int|g|L\,\varphi_{m,v}\,d\lambda=\int|g|\varphi_{m',v'}\,d\lambda$. Checked numerically for several $g$ (smooth, digital, call), including $v'>2v$. There $E_{N(m,v)}[L^2]=\infty$, but that does not affect this first-moment claim. Not vacuous; no junk. Standard: the importance-sampling / likelihood-ratio identity.

## 17. `integral_mul_sub_likelihoodRatio` (theorem)

**Rendering.** Let $v,v_f,v_c\ne0$, and let $g$ be integrable under both $N(m_f,v_f)$ and $N(m_c,v_c)$. With $L_\bullet=\varphi_{m_\bullet,v_\bullet}/\varphi_{m,v}$,
$$\int g\,(L_f-L_c)\,dN(m,v)=\int g\,dN(m_f,v_f)-\int g\,dN(m_c,v_c).$$

**Assessment.** True: apply 16 twice and use linearity. Both terms are integrable, so no junk integral appears. Not vacuous. Standard: the likelihood-ratio MLMC estimator of a fine-minus-coarse difference, reweighting both final-step Gaussian laws to one sampling law.

## 18. `hasDerivAt_call_payoff` (theorem)

**Rendering.** For $K\in\mathbb R$ and $f(y)=\max(y-K,0)$:
- (a) for all $x\ne K$, $f'(x)=\mathbf 1_{x>K}$;
- (b) $f$ is not differentiable at $K$;
- (c) there is no $g:\mathbb R\to\mathbb R$, continuous at $K$, with $f'(x)=g(x)$ for all $x\ne K$.

**Assessment.** True. The one-sided derivatives at $K$ are $0$ and $1$. Any such $g$ must equal $0$ on $(-\infty,K)$ and $1$ on $(K,\infty)$, so it has no limit at $K$. There are no hypotheses. Standard: the derivative of the call payoff is the Heaviside (digital) payoff, which is discontinuous at the strike. This is why pathwise sensitivities fail for digitals.

## 19. `pairAvg` (def)

**Rendering.** $\texttt{pairAvg}(z)_k=(z_{2k}+z_{2k+1})/\sqrt2$.

**Assessment.** A faithful MLMC coupling of normalised increments: $\sqrt{2h}\,\texttt{pairAvg}(z)_k=\sqrt h(z_{2k}+z_{2k+1})$. Under i.i.d. $N(0,1)$ inputs the output is again i.i.d. $N(0,1)$.

## 20. `stdNormalSeq` (abbrev)

**Rendering.** `Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)`, the law of an i.i.d. standard normal sequence on $\mathbb R^{\mathbb N}$.

**Assessment.** A faithful model; it is a probability measure.

## 21. `gbmEM` (def)

**Rendering.** $\texttt{gbmEM}(r,\sigma,T,s_0,\ell,z)=\texttt{emPath}(rS,\sigma S,\,T/2^\ell,\,s_0,\,z)(2^\ell)=s_0\prod_{i<2^\ell}(1+rh+\sigma\sqrt h\,z_i)$ with $h=T/2^\ell$.

**Assessment.** A faithful EM approximation of GBM at time $T$. If $T\le0$ the `sqrt` would return junk, but Theorem 9 assumes $T>0$.

## 22. `gbmStrongConst` (def)

**Rendering.** $C(r,\sigma,t,s_0)=s_0^2e^{(2|r|+\sigma^2)t}(|r|+\sigma^2)(5(|r|+\sigma^2)t+4)$.

**Assessment.** $C>0$ whenever $s_0\ne0$ and $\sigma\ne0$. Numerically it is a valid GBM–EM strong-error constant, $E|S_T-S^{EM}_T|^2\le C\,T/2^j$ for all $j$, with a factor-10 margin (item 9).

## 23. `emPath` (def)

**Rendering.** $S_0=S_0$, and $S_{i+1}=S_i+a(S_i,ih)\,h+b(S_i,ih)\sqrt h\,z_i$, with $i$ cast to $\mathbb R$.

**Assessment.** The standard Euler–Maruyama recursion with $\Delta W_i=\sqrt h\,z_i$. Step $i$ uses $z_i$, so step $2^\ell$ uses $z_0,\dots,z_{2^\ell-1}$.

## 24. `gbmDrift` (def)

**Rendering.** $a(S,t)=rS$.

**Assessment.** The GBM drift.

## 25. `gbmVol` (def)

**Rendering.** $b(S,t)=\sigma S$.

**Assessment.** The GBM volatility.
