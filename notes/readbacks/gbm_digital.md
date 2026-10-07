# Blind read-back report: round 18, packet R18 (GBM digital payoffs)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round18/packet_R18_gbmdigital.lean` |
| declarations audited | 9 theorems, plus the 13 supporting definitions rendered (22 in all) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round18/work_R18/` (each `*.py` has an `*.out` with the same name; `scratch_packet.lean` and `.out` hold the elaboration check) |

Elaboration check: a scratch copy of the packet (with `import MlmcLean`, proofs `sorry`) compiles. `kurtosis`
resolves to `MLMC.kurtosis` (the raw-moment ratio shown in the packet). `volume[|Set.Icc (-1) 1]` is
`ProbabilityTheory.cond volume (Icc (-1) 1)`. All numerals in `2 * (1 / 2) * δ`, `d / 2 - d ^ 2 / 4` and
`1 / 3 < q` elaborate in `ℝ`, with no ℕ-division. Exponents `(2/3 : ℝ)` and `(1/3 : ℝ)` are `Real.rpow`.

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `gbm_mil_digital_variance_le` | theorem | true | no | no |
| 2 | `gbm_em_digital_fourth_moment_le` | theorem | true | no | no |
| 3 | `gbm_mil_digital_fourth_moment_le` | theorem | true | no | no |
| 4 | `digital_mismatch_example` | theorem | true | no | no |
| 5 | `digital_mismatch_exponent_sharp` | theorem | true | no | no |
| 6 | `map_milsteinEM_coarse_eq_fine` | theorem | true | no | no. For $h\le 0$ it reduces to two equal Dirac laws, which is still true. |
| 7 | `integral_condExp_milsteinEM_coarse_eq_fine` | theorem | true | no | partly: when $g\circ X$ is not integrable, both conjuncts read $0=0$ (condExp and integral junk). The statement is meaningful for integrable $g\circ X$. |
| 8 | `digital_smoothing_milsteinEM_mean_eq` | theorem | true | no | no |
| 9 | `gbm_digital_smoothing_mean_eq` | theorem | true | no | no |
| D | 13 definitions (`kurtosis`, `pairAvg`, `stdNormalSeq`, `emStep`, `emPath`, `gbmDrift`, `gbmVol`, `gbmEM`, `gbmStrongConst`, `milsteinStep`, `milsteinPath`, `gbmMilStrongConst`, `gbmMil`) | def | n/a | n/a | `kurtosis` uses raw moments, not central ones (see point 3) |

## Main points for a human auditor

1. **All 9 statements are true.** For #1 to #3, truth rests on two facts:
   - the supremum of the density of the exact $S_T$ equals $M=e^{(\sigma^2-r)T}/(\sqrt{2\pi}|s_0||\sigma|\sqrt T)$ (checked analytically and numerically);
   - the two strong-error constants hold: $E|X^{EM}_N-S_T|^2\le C_{EM}h$ and $E|X^{Mil}_N-S_T|^2\le C_{Mil}h^2$.

   I computed these mean-square errors in closed form with mpmath. The largest ratio of error to bound is about $0.0997$ for EM (it tends to $1/10$) and about $0.0083$ for Milstein (it tends to $1/120$). The scan covered $r\in[-20,20]$, $\sigma\in[10^{-3},5]$, $T\in[10^{-3},5000]$ and levels $\ell\le 26$. A Monte Carlo of the mismatch probability gives $p/\text{bound}\le 0.008$ in every case.
2. **The GBM bounds are very loose.** The constant slack is more than a factor of 100. The rates are $h^{1/3}$ (EM) and $h^{2/3}$ (Milstein), while Monte Carlo shows about $h^{1/2}$ and $h$. At practical levels the bound $B$ exceeds 1. For example, with $r=0.05$, $\sigma=0.2$, $T=1$: EM has $B>1$ for all $\ell\le 8$, and Milstein has $B>1$ for $\ell\le 2$. At those levels the probability bound says nothing, and the kurtosis lower bound $1/B<1$ is trivial.
3. **Kurtosis convention.** `kurtosis` is the raw-moment ratio $E[D^4]/(E[D^2])^2$. For $D\in\{-1,0,1\}$ this equals exactly $1/p$. The usual (central) kurtosis $E[(D-\mu)^4]/\operatorname{Var}(D)^2$, used in MLMC practice, can be smaller. When all mismatches have the same sign it is about $1/p-2$; one Monte Carlo case gives raw 12.19 against central 10.28. The bound $1/B\le$ kurtosis is proved for the raw quantity only. It does not follow formally for the central one; it holds there only because of the large slack.
4. **What "best possible" covers (#4, #5).** The sharpness result concerns the generic lemma: mismatch probability $\lesssim M^{2/3}(E|X-Y|^2)^{1/3}$ for an exact $X$ with bounded density. The family used is $X\sim U[-1,1]$, $Y=X-2d\,1_{(0,d)}(X)$. It does **not** show that the GBM rates in #1 to #3 are sharp; they are not (point 2). The quantifier order, $\forall C\ \forall q>1/3\ \exists d$, is the correct one. At $q=1/3$ the claim fails for $C\ge 2^{-4/3}$, as checked.
5. **#7 is weaker than it looks.** It is only the tower property, $\int E[f\mid m]=\int f$, together with the equality of laws from #6. The conditioning σ-algebras play no role in its truth. There is no integrability assumption on $g$, so for non-integrable $g\circ X$ both sides are $0$ by Mathlib conventions.
6. **#8: the σ-algebras and laws are right.** On the coarse side the conditioning is on $\sigma(X^c_n,\sqrt h\,z_{2n})$, the coarse state plus the first fine half-increment of the last coarse step, as in Giles' Milstein digital smoothing. The remaining randomness $\sqrt h\,z_{2n+1}\sim N(0,h)$ is independent of it. On the other side the conditioning is on $\sigma(X_n)$, with $\sqrt{2h}\,w_n\sim N(0,2h)$ independent. Both $\Phi$ formulas are correct, including for $b<0$, because $|b|$ appears in the denominator.
   - The hypotheses $h>0$ and "$b(X_n)\ne0$ a.s." are **needed** for the two conditional-expectation identities. If $b=0$, the formula gives $\Phi(\cdot/0)=\Phi(0)=1/2$ by Lean's $x/0=0$, while the true value is 0 or 1.
   - The third conjunct (equal means) holds even without these hypotheses.
7. **Degenerate parameters.** #2(b) and #3(b) would be **false** with $\sigma=0$:
   - Then $M=\dots/0=0$, so the bound is $0$.
   - The fine and coarse paths are deterministic and can lie on either side of $K$. With $r=1$, $T=1$, $\ell=0$, $s_0=1$ the paths end at $2.25$ (fine) and $2$ (coarse), so $K=2.1$ gives $p=1$.

   The hypothesis $\sigma\ne0$ is therefore necessary, and it is present. With $s_0=0$ the bound would also be $0$, but then $p=0$. In #1 to #3, $T>0$ guarantees $h>0$.
8. **Harmless extra hypotheses.**
   - #1 would also hold without $s_0\ne0$ and $\sigma\ne0$, because the degenerate cases give $\operatorname{Var}=0\le 0$.
   - #9 would also hold without $s_0\ne0$ and $\sigma\ne0$, because the degenerate cases give $1/2=1/2$ by junk.

   With these hypotheses, the a.s.-nonvanishing hypothesis of #8 holds for GBM. Each Milstein factor $1+2rh+\sigma y+\tfrac12\sigma^2(y^2-2h)$, with $y=\sqrt{2h}\,w_i$, is a non-degenerate quadratic in a Gaussian, so it is nonzero a.s.

## Notation used below

- $\mathbb P$ = `stdNormalSeq` $=\bigotimes_{k\in\mathbb N}N(0,1)$ on $\mathbb R^{\mathbb N}$, with coordinates $z=(z_0,z_1,\dots)$.
- $\bar z=$ `pairAvg z`, where $\bar z_k=(z_{2k}+z_{2k+1})/\sqrt2$. Under $\mathbb P$, $\bar z$ is again an iid $N(0,1)$ sequence, since disjoint pairs give independent coordinates. For $h\ge0$, $\sqrt{2h}\,\bar z_k=\sqrt h(z_{2k}+z_{2k+1})$.
- $h_f=T/2^{\ell+1}$ and $h_c=T/2^{\ell}=2h_f$.
- $X^f=$ `gbmMil r σ T s₀ (ℓ+1) z` and $X^c=$ `gbmMil r σ T s₀ ℓ (pairAvg z)`. EM analogues are written $X^{f,EM}$ and $X^{c,EM}$.
- The coarse increments are $\sqrt{h_c}\,\bar z_k=\sqrt{h_f}(z_{2k}+z_{2k+1})$. This is the standard MLMC coupling: the same Brownian path, with $W_T=\sqrt{h_f}\sum_{i<2^{\ell+1}}z_i$.
- $D=1\{X^f>K\}-1\{X^c>K\}\in\{-1,0,1\}$ and $p=\mathbb P(D\ne0)$.
- $M=\dfrac{e^{(\sigma^2-r)T}}{\sqrt{2\pi}\,|s_0|\,|\sigma|\sqrt T}$, $C_{EM}=$ `gbmStrongConst r σ T s₀` and $C_{Mil}=$ `gbmMilStrongConst r σ T s₀`.
- $\Phi=$ `cdf (gaussianReal 0 1)`, the standard normal cdf.

**Common argument for #1 to #3.** Let $S_T=s_0\exp((r-\sigma^2/2)T+\sigma W_T)$.

- If $D\neq0$, then for any $\delta>0$ at least one of these holds: $|S_T-K|\le\delta$, $|X^f-S_T|>\delta$, or $|X^c-S_T|>\delta$. To see this, take $X^f>K\ge X^c$. If $S_T>K+\delta$, then $|X^c-S_T|>\delta$. If $S_T<K-\delta$, then $|X^f-S_T|>\delta$. The other orientation is symmetric.
- The density of $S_T$ is bounded by $M$, and Chebyshev bounds the other two events. So $p\le 2M\delta+(E_f+E_c)/\delta^2$.
- Choosing $\delta=((E_f+E_c)/M)^{1/3}$ gives $p\le 3M^{2/3}(E_f+E_c)^{1/3}$.
- With $E\le C h^{\alpha}$ and subadditivity of $t\mapsto t^{1/3}$: $(C(h_f^\alpha+h_c^\alpha))^{1/3}\le C^{1/3}(h_f^{\alpha/3}+h_c^{\alpha/3})$.
- Finally $\operatorname{Var}D\le E[D^2]=E[D^4]=p$.

The supremum of the lognormal density is attained at $|s|=|s_0|e^{(r-3\sigma^2/2)T}$ and equals $M$; for $s_0<0$ the density is reflected. The script `example_and_density.py` confirms this to 12 digits.

**Exact strong errors** (`strong_const_exact.py`, `strong_const_exact_longT.py`). Write $F$ for the one-step factor of the scheme and $G=e^{(r-\sigma^2/2)h+\sigma\sqrt h Z}$ for the exact one. The steps are iid and driven by the same $Z$, so
$$E|X_N-S_T|^2=s_0^2\big[(EF^2)^N-2(EFG)^N+(EG^2)^N\big].$$
- EM: $EF^2=(1+rh)^2+\sigma^2h$ and $EFG=e^{rh}(1+rh+\sigma^2h)$.
- Milstein: $EF^2=(1+rh)^2+\sigma^2h+\sigma^4h^2/2$ and $EFG=e^{rh}(1+rh+\sigma^2h+\sigma^4h^2/2)$. These were cross-checked by quadrature.

Over all scans, the largest value of $\text{MSE}/(C h^{p})$ is $0.0997$ (EM) and $0.00829$ (Milstein).

---

## Definitions

**`kurtosis X ν`** $:=\big(\int X^4\,d\nu\big)/\big(\int X^2\,d\nu\big)^2$.
- Moments are raw (not centred). This is a non-standard convention; the usual one is $E(X-\mu)^4/\operatorname{Var}^2$.
- The value is $0/0=0$ if $X=0$ a.e., and integrals of non-integrable functions are $0$.

**`pairAvg z k`** $=(z_{2k}+z_{2k+1})/\sqrt2$.

**`stdNormalSeq`** = `Measure.infinitePi (fun _ => gaussianReal 0 1)`, the iid standard normal sequence.

**`emStep a b h S dW`** $=S+a(S)h+b(S)\,dW$.

**`emPath a b h S₀ z`** is defined by $X_0=S_0$ and $X_{i+1}=X_i+a(X_i,ih)h+b(X_i,ih)\sqrt h\,z_i$. Here $i$ is cast to $\mathbb R$, and $\sqrt h=0$ for $h<0$ (`Real.sqrt`).

**`gbmDrift r`** $=(S,t)\mapsto rS$. **`gbmVol σ`** $=(S,t)\mapsto\sigma S$.

**`gbmEM r σ T s₀ ℓ z`** is the EM approximation of GBM at time $T$ with $2^\ell$ steps of size $T/2^\ell$ and normals $z_0,\dots,z_{2^\ell-1}$.

**`gbmStrongConst r σ t s₀`** $=s_0^2e^{(2|r|+\sigma^2)t}(|r|+\sigma^2)(5(|r|+\sigma^2)t+4)$. It is a valid mean-square EM constant: $E|X^{EM}_N-S_t|^2\le C\,h$ for all $N$. Numerically, over the scanned grid, the slack is at least 10; the asymptotic ratio is $1/10$.

**`milsteinStep a b h S dW`** $=S+a(S)h+b(S)dW+\tfrac12 b(S)b'(S)(dW^2-h)$, where $b'=$ `deriv b`. Mathlib's `deriv` is $0$ where $b$ is not differentiable, and it is measurable for any $b$ (`measurable_deriv`). For GBM, $b'(S)=\sigma$ everywhere.

**`milsteinPath a b h S₀ z`** is defined by $X_0=S_0$ and $X_{i+1}=$ `milsteinStep a b h X_i (√h z_i)`.

**`gbmMilStrongConst r σ t s₀`** $=s_0^2e^{(2|r|+\sigma^2)t}(|r|+\sigma^2)^2(30(|r|+\sigma^2)^2t^2+16(|r|+\sigma^2)t+4)$. It is a valid mean-square Milstein constant: $E|X^{Mil}_N-S_t|^2\le C h^2$. Numerically, over the scanned grid, the slack is at least 120; the asymptotic ratio is $1/120$.

**`gbmMil r σ T s₀ ℓ z`** is the Milstein approximation of GBM ($a(S)=rS$, $b(S)=\sigma S$) at $T$ with $2^\ell$ steps of size $T/2^\ell$.

---

## 1. `gbm_mil_digital_variance_le`

**Rendering.** Take $r,\sigma,s_0,T,K\in\mathbb R$ and $\ell\in\mathbb N$, with $s_0\neq0$, $\sigma\ne0$ and $T>0$. Then
$$\operatorname{Var}_{\mathbb P}\big(1\{X^f>K\}-1\{X^c>K\}\big)\le 3\,M^{2/3}\,C_{Mil}^{1/3}\,\big(h_f^{2/3}+h_c^{2/3}\big),$$
where $X^f$ and $X^c$ are the coupled Milstein approximations of GBM at levels $\ell+1$ and $\ell$. `variance` is Mathlib's `(evariance X μ).toReal`.

**Assessment.**
- *Truth: true.* It follows from the common argument with $E\le C_{Mil}h^2$; the Milstein constant was verified exactly (largest ratio $0.0083$).
- *Monte Carlo* (`digital_mc.py`): $p/\text{bound}\le 0.006$ in all cases tried, and $\operatorname{Var}\le p$.
- *Non-vacuous.* Example: $r=0.05$, $\sigma=0.2$, $s_0=1$, $T=1$, $K=1$, $\ell=4$, where the bound is $0.455$.
- *Junk.* None. The denominators of $M$ are nonzero by hypothesis, and the rpow bases are positive.
- *Hypotheses.* $s_0\ne0$ and $\sigma\ne0$ are not needed for this inequality alone: the degenerate cases give $\operatorname{Var}=0\le 0$.
- *Rate.* The rate $h^{2/3}$ is a weakening of $(h_f^2+h_c^2)^{1/3}$ and is not the true rate, which is about $h$ for Milstein digitals.

**Standard fact.** This is the Avikainen / Giles–Higham–Mao bound: the mismatch probability is at most $3M^{2/3}(E|X-Y|^2)^{1/3}$ for an exact variable with bounded density. It is combined with strong order 1 of Milstein for GBM and the lognormal density bound.

## 2. `gbm_em_digital_fourth_moment_le`

**Rendering.** Same hypotheses, with EM paths $X^{f,EM}$ (level $\ell+1$, normals $z$) and $X^{c,EM}$ (level $\ell$, normals $\bar z$). Let $D$ be the corresponding difference of indicators, $p=\mathbb P(D\ne0)$ (as `.real`), and $B_{EM}=3M^{2/3}C_{EM}^{1/3}(h_f^{1/3}+h_c^{1/3})$. Then:

- (a) $E[D^4]=p$;
- (b) $p\le B_{EM}$;
- (c) if $p>0$, then $B_{EM}^{-1}\le$ `kurtosis D` $=E[D^4]/(E[D^2])^2$.

**Assessment.**
- *Truth: true.*
  - (a) holds because $D^4=1\{D\ne0\}$.
  - (b) follows from the common argument with $E\le C_{EM}h$, whose constant was verified exactly (largest ratio $0.0997$). Monte Carlo gives $p/B\le 0.008$.
  - (c) holds because, by (a), $E[D^2]=E[D^4]=p$, so kurtosis $=p/p^2=1/p\ge 1/B$. Note $B>0$ under the hypotheses.
- *Non-vacuous.* Example: $r=0$, $\sigma=1$, $s_0=1$, $T=1$, $K=1$, $\ell=0$, where $p\approx0.082>0$. Analytically, at $\ell=0$, $X^{f,EM}-X^{c,EM}=s_0AB$ with $A=rh_f+\sigma\sqrt{h_f}z_0$ and $B=rh_f+\sigma\sqrt{h_f}z_1$, so a mismatch has positive probability. The bound is below 1, so (b) has content, only for small $h$; for example $r=0.05$, $\sigma=0.2$, $\ell=10$ gives $B\approx0.65$.
- *Junk.* None: the hypothesis $p>0$ excludes $0/0$.
- *Hypotheses.* $\sigma\neq0$ is necessary: with $\sigma=0$, (b) is false (point 7). Kurtosis uses raw moments (point 3).

**Standard fact.** EM has strong order 1/2 for GBM, combined with the same bound. The kurtosis of a digital MLMC correction is about $1/p$, which grows as levels are refined (Giles).

## 3. `gbm_mil_digital_fourth_moment_le`

**Rendering.** As in #2, with the Milstein paths $X^f$ and $X^c$ and $B_{Mil}=3M^{2/3}C_{Mil}^{1/3}(h_f^{2/3}+h_c^{2/3})$:

- (a) $E[D^4]=p$;
- (b) $p\le B_{Mil}$;
- (c) if $p>0$, then $B_{Mil}^{-1}\le$ `kurtosis D`.

**Assessment.**
- *Truth: true*, by the same reasoning as #2, using the Milstein constant. Monte Carlo gives $p/B\le0.006$.
- *Non-vacuous.* Example: $r=0$, $\sigma=1$, $s_0=1$, $T=1$, $K=1$, $\ell=0$, where $p\approx0.054$.
- *Junk.* None.
- *Hypotheses.* $\sigma\ne0$ is necessary for (b) (point 7). Raw-moment kurtosis (point 3). The rates are not sharp (point 2).

**Standard fact.** Milstein has strong order 1, combined with the same bound.

## 4. `digital_mismatch_example`

**Rendering.** Let $\nu$ be the uniform probability on $[-1,1]$ (`volume[|Icc (-1) 1]` $=\lambda([-1,1])^{-1}\lambda|_{[-1,1]}$). For $0<d\le1$ let $Y_d(x)=x-2d\,1_{(0,d)}(x)$ and $D_d=1\{x>0\}-1\{Y_d>0\}$. The theorem states:

- (i) for all $\delta>0$, $\nu\{|x|\le\delta\}\le 2\cdot\tfrac12\cdot\delta$;
- (ii) $\int(x-Y_d)^2d\nu=2d^3$;
- (iii) $\nu\{D_d\ne0\}=d/2$;
- (iv) $\operatorname{Var}_\nu D_d=d/2-d^2/4$;
- (v) $\nu\{D_d\ne0\}=\big(\int(x-Y_d)^2d\nu/16\big)^{1/3}$.

**Assessment.**
- *Truth: true.*
  - (i): $\nu\{|x|\le\delta\}=\min(\delta,1)\le\delta$.
  - (ii): $(x-Y_d)^2=4d^2\,1_{(0,d)}$, and $(0,d)\subseteq[-1,1]$, so the integral is $4d^2\cdot d/2=2d^3$.
  - (iii): for $x\in(0,d)$, $Y_d\in(-2d,-d)$, so there is a mismatch; elsewhere $Y_d=x$.
  - (iv): $D_d=1_{(0,d)}$, a Bernoulli$(d/2)$ variable.
  - (v): $(2d^3/16)^{1/3}=d/2$.
- *Numerics.* All five checked for $d\in\{0.01,0.3,0.77,1\}$ by quadrature (`example_and_density.py`).
- *Non-vacuous.* Example: $d=1/2$.
- *Junk.* None; everything is bounded.

**Standard fact.** This is an extremal example for the bounded-density mismatch lemma: the density bound $1/2$ is clause (i), and the exponent $1/3$ is attained.

## 5. `digital_mismatch_exponent_sharp`

**Rendering.** For every $C\in\mathbb R$ and every real $q>1/3$ there is $d\in(0,1]$ such that, in the notation of #4,
$$C\Big(\int(x-Y_d)^2d\nu\Big)^q<\nu\{D_d\ne0\}\quad\text{and}\quad C\Big(\int(x-Y_d)^2d\nu\Big)^q<\operatorname{Var}_\nu D_d.$$
The quantifiers are $\forall C\,\forall q\,\exists d$, so $d$ may depend on both $C$ and $q$.

**Assessment.**
- *Truth: true.* By #4 the inequalities read $C(2d^3)^q<d/2$ and $C(2d^3)^q<d/2-d^2/4$. If $C\le0$, any $d$ works. If $C>0$, take $d=\min\big(\tfrac12,(8\max(C,1)2^q)^{-1/(3q-1)}\big)$. Then $C(2d^3)^q\le d/8<3d/8\le d/2-d^2/4$.
- *Witnesses checked numerically*:
  - $C=10^6$, $q=0.34$: $d\approx5\cdot10^{-351}$;
  - $C=100$, $q=1/2$: $d\approx 7.8\cdot10^{-7}$;
  - $C=-5$, $q=0.4$;
  - $C=1000$, $q=0.3334$.
- *Failure at the boundary.* At $q=1/3$ the statement fails for $C=0.4\ge2^{-4/3}$, confirming that the threshold is tight.
- *Quantifier order.* This order is the correct formalisation of "no bound $P\le C\,E^q$ with $q>1/3$ holds uniformly". For large $C$ the witness $d$ is forced to be small, so the counterexamples lie in the small-error regime.
- *Non-vacuous.* Every $C$ and $q$ qualify; there are no other hypotheses.
- *Junk.* None.
- *Caveat.* Sharpness is for the generic lemma, not for the GBM schemes of #1 to #3 (point 4).

**Standard fact.** The exponent $p/(p+1)$ in Avikainen's lemma is optimal; this is the case $p=2$.

## 6. `map_milsteinEM_coarse_eq_fine`

**Rendering.** Let $a,b:\mathbb R\to\mathbb R$ be measurable, and take any $h,S_0\in\mathbb R$ and $n\in\mathbb N$. Define:

- $X^c_n(z)=$ `milsteinPath a b (2h) S₀ (pairAvg z) n`, which is $n$ coarse Milstein steps of size $2h$;
- $L(z)=X^c_n+a(X^c_n)2h+b(X^c_n)(\sqrt h z_{2n}+\sqrt h z_{2n+1})$, a final EM step;
- $R(w)=X_n(w)+a(X_n)2h+b(X_n)\sqrt{2h}\,w_n$, where $X_n(w)=$ `milsteinPath a b (2h) S₀ w n`.

Then $\mathbb P\circ L^{-1}=\mathbb P\circ R^{-1}$, as equal pushforward measures.

**Assessment.**
- *Truth: true.* Pointwise $L=R\circ\text{pairAvg}$:
  - for $h\ge0$, $\sqrt h(z_{2n}+z_{2n+1})=\sqrt{2h}\,\bar z_n$, and the Milstein part uses $\bar z_0,\dots,\bar z_{n-1}$;
  - for $h<0$, every `Real.sqrt` is $0$ on both sides.

  `pairAvg` pushes $\mathbb P$ to $\mathbb P$, because disjoint pairs give iid $N(0,1)$ coordinates. Both maps are measurable, since `deriv b` is measurable for any $b$, so no `map` junk arises.
- *Numerics.* Monte Carlo (`law_coarse_fine.py`) finds the pathwise identity $L(z)=R(\bar z)$ holds to $4\cdot10^{-16}$, and the KS statistics lie below the 5% critical value. For $h<0$ the two laws are the same point mass.
- *Non-vacuous.* Example: $a=b=\mathrm{id}$, $h=0.1$.
- *Junk.* None that matters. For $h\le0$ the statement degenerates to two equal Dirac laws.
- *Remark.* For a non-differentiable $b$ the "Milstein" correction uses `deriv b = 0` at those points, but the statement holds for any measurable step map, so this is irrelevant.

**Standard fact.** In MLMC, the coarse path built from pair sums of fine increments has the law of an independent coarse-level path. This preserves the telescoping sum.

## 7. `integral_condExp_milsteinEM_coarse_eq_fine`

**Rendering.** With the setting of #6 and any strongly measurable $g:\mathbb R\to\mathbb R$:

- (a) $\displaystyle\int E\big[g(L)\,\big|\,\sigma(X^c_n,\sqrt h z_{2n})\big]\,d\mathbb P=\int E\big[g(R)\,\big|\,\sigma(X_n)\big]\,d\mathbb P$;
- (b) $\displaystyle\int E[g(R)\mid\sigma(X_n)]\,d\mathbb P=\int g(R)\,d\mathbb P$.

The σ-algebras are `MeasurableSpace.comap` of the stated maps with the Borel structure on $\mathbb R^2$ or $\mathbb R$; they are contained in the product σ-algebra because the maps are measurable.

**Assessment.**
- *Truth: true.*
  - (b) is Mathlib's `integral_condExp`, which needs no integrability.
  - (a) holds because each side equals $\int g(\cdot)$ of its variable (`integral_condExp`), and $\int g(L)\,d\mathbb P=\int g(R)\,d\mathbb P$ by #6 and `integral_map`. Integrability of $g\circ L$ and of $g\circ R$ are equivalent, since the two have the same law.
- *Non-vacuous.* Example: bounded $g=\arctan$.
- *Junk, partial.* There is no integrability hypothesis. For non-integrable $g\circ R$, the condExps are $0$ (`condExp_of_not_integrable`) and so are the integrals, so both conjuncts read $0=0$.
- *Weaker than it looks.* The choice of σ-algebras is irrelevant to truth: the identity holds for any sub-σ-algebras. The statement does not identify the conditional expectations; #8 does that.

**Standard fact.** Tower property, plus equality of laws.

## 8. `digital_smoothing_milsteinEM_mean_eq`

**Rendering.** Let $a,b$ be measurable, $h>0$, and $S_0,K\in\mathbb R$, $n\in\mathbb N$. Assume $b(X_n(w))\ne0$ for $\mathbb P$-a.e. $w$. With the notation of #6:

- (a) $E\big[1\{L>K\}\mid\sigma(X^c_n,\sqrt h z_{2n})\big]=\Phi\!\Big(\dfrac{X^c_n+2h\,a(X^c_n)+b(X^c_n)\sqrt h z_{2n}-K}{|b(X^c_n)|\sqrt h}\Big)$ $\mathbb P$-a.e.
- (b) $E\big[1\{R>K\}\mid\sigma(X_n)\big]=\Phi\!\Big(\dfrac{X_n+2h\,a(X_n)-K}{|b(X_n)|\sqrt{2h}}\Big)$ $\mathbb P$-a.e.
- (c) The $\mathbb P$-integrals of the two right-hand sides are equal.

**Assessment.**
- *Truth of (a).* $X^c_n$ depends only on $z_0,\dots,z_{2n-1}$, and $z_{2n+1}$ is independent of $(z_0,\dots,z_{2n})$. Given $X^c_n=x$ and $\sqrt h z_{2n}=u$:
  $$P\big(x+2ha(x)+b(x)(u+\sqrt h Z)>K\big)=\Phi\big((x+2ha(x)+b(x)u-K)/(|b(x)|\sqrt h)\big)\quad\text{for }b(x)\neq0,$$
  for either sign of $b$. The a.s. condition transfers to $X^c_n=X_n\circ\text{pairAvg}$ by measure preservation.
- *Truth of (b).* Same argument, with the remaining increment $\sqrt{2h}\,w_n$.
- *Truth of (c).* Each side equals $\mathbb P(L>K)=\mathbb P(R>K)$, by the tower property and #6. It even holds without the a.s. hypothesis on $b$: where $b=0$ both integrands are $\Phi(0)=1/2$.
- *Numerics.* `condexp_smoothing.py` checks (a) and (b) pointwise against direct integrals for a nonlinear $a$ and a negative $b$, with agreement to 12 digits.
- *Right σ-algebra.* Yes: it is the coarse state at $T-2h$ plus the first fine half-increment, as in Giles' scheme.
- *Hypotheses.* $h>0$ and $b(X_n)\ne0$ a.s. are necessary for (a) and (b). Where $b=0$ the right side is $\Phi(0)=1/2$ by $x/0=0$, while the left side is 0 or 1. For $h\le0$, likewise $\sqrt h=0$.
- *Non-vacuous.* Example: $a=0$, $b\equiv1$, $h=0.1$.
- *Junk.* None. The $x/0$ cases are $\mathbb P$-null under the hypothesis.

**Standard fact.** Conditional-expectation smoothing of a digital payoff at the last timestep, with an Euler final step; the coarse path uses the fine half-step increment (Giles 2008). Part (c) is the telescoping-mean identity.

## 9. `gbm_digital_smoothing_mean_eq`

**Rendering.** Take $r,\sigma,s_0,h,K\in\mathbb R$ and $n\in\mathbb N$, with $s_0\ne0$, $\sigma\ne0$ and $h>0$. Let $X$ be the Milstein path for GBM ($a(S)=rS$, $b(S)=\sigma S$) with step $2h$. Then
$$\int\Phi\Big(\frac{X^c_n+2rh\,X^c_n+\sigma X^c_n\sqrt h z_{2n}-K}{|\sigma X^c_n|\sqrt h}\Big)d\mathbb P=\int\Phi\Big(\frac{X_n+2rhX_n-K}{|\sigma X_n|\sqrt{2h}}\Big)d\mathbb P,$$
where $X^c_n$ uses `pairAvg z` and $X_n$ uses $w$. This is #8(c) for GBM.

**Assessment.**
- *Truth: true.* It is #8(c) with measurable $a$ and $b$. The hypothesis of #8 holds: $X_{i+1}=X_i\,q(\sqrt{2h}w_i)$, where $q(y)=1+2rh+\sigma y+\tfrac12\sigma^2(y^2-2h)$ is a quadratic with leading coefficient $\sigma^2/2\ne0$, so $q(\sqrt{2h}w_i)\ne0$ a.s. Hence $X_n\ne0$ a.s., and $\sigma X_n\ne0$ a.s.
- *Numerics.* `condexp_smoothing.py` part (3), for $n=1$, gives LHS = RHS = direct $P(R>K)$ to 12 digits in three parameter sets, including $\sigma<0$ and $s_0<0$.
- *Non-vacuous.* Example: $r=0.05$, $\sigma=0.2$, $s_0=1$, $h=0.1$, $K=1.02$, $n=1$, where both sides equal $0.48149$.
- *Junk.* None.
- *Hypotheses.* $s_0\ne0$ and $\sigma\ne0$ are not needed for the bare equality: the degenerate cases give $1/2=1/2$ by $x/0=0$. Harmless.

**Standard fact.** The telescoping-mean property of Giles' smoothed Milstein digital estimator for GBM.
