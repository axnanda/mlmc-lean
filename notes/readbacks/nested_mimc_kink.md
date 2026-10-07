# Blind read-back report: R6 (nested MIMC with a kink)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round14/packet_R6_mimc_kink.lean` |
| declarations audited | 6 theorems (`nested_mimc_kink_variance_rate`, `nested_mimc_kink_mean_rate`, `nested_mimc_kink_rate_sharp`, `nested_mimc_kink_exponents`, `nested_mimc_kink_complexity`, `nested_mimc_kink_beats_mlmc`), plus the 15 definitions appended to the packet |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round14/work_R6/` (every `.py` has a matching `.out`; there are also two Lean scratch files, `r6_scratch_check.lean` and `r6_nonvacuity.lean`, each with a `.out`) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `nested_mimc_kink_variance_rate` | theorem | true. I checked the rate with a proof sketch; I did not re-derive the explicit constant, but no violation turned up (largest LHS/RHS in the scans is about $1.1\cdot10^{-4}$) | no. Lean confirms that the example meets every hypothesis | no |
| 2 | `nested_mimc_kink_mean_rate` | theorem | true. Same status as #1 (largest LHS/RHS about $4.8\cdot10^{-4}$) | no. Lean confirms the example meets every hypothesis | no |
| 3 | `nested_mimc_kink_rate_sharp` | theorem | true (exact computation, plus an analytic lower bound) | n/a (it has no hypotheses) | no |
| 4 | `nested_mimc_kink_exponents` | theorem | true. It follows from the definitions, for every $\varepsilon\in\mathbb R$ | n/a | No for the outcome: my own derivation also gives exponent 4. But the $D_3$ term drops out only through truncated ℕ subtraction (see the points below) |
| 5 | `nested_mimc_kink_complexity` | theorem | true (the standard MIMC argument, using the rates of #1) | no | no. The MSE integrand is in $L^2$, so its integral is a genuine value |
| 6 | `nested_mimc_kink_beats_mlmc` | theorem | true. The worst case is $4096e^{-4}\approx75.02\le384$ | n/a | no |

## Main points for a human auditor

1. **All six statements are true. I found no violation.** I computed $D=\texttt{nestedMimcDelta}\,f\,\texttt{kinkInnerApprox}\,(\ell_1+1)(\ell_2+1)$ exactly in two ways:
   - by literal enumeration of every inner coin-flip sequence for $\ell_1\le3$ (up to 16 flips), with exact `Fraction` integration over $Z\sim U[0,1]$;
   - by an exact binomial "tent" reduction for $\ell_1\le11$ and $\ell_2\le13$, which matches the literal values to every digit.

   The results:
   - $\mathbb E D=0$ exactly.
   - $\sup 2^{\ell_1+\ell_2}\operatorname{Var}D=1.0745\cdot10^{-4}$, against the claimed 19.
   - Along the diagonal $(2j,j+1)$ the value is at least $5.34\cdot10^{-5}$ for every $j$ (the limit is $5.486\cdot10^{-5}$), against the claimed $2^{-18}\approx3.8\cdot10^{-6}$.
2. **The hypotheses of #1 and #2 can all hold at once.** In `r6_nonvacuity.lean` I proved, in Lean and without `sorry`, every hypothesis of both theorems for the example, with:
   - $g(z,b)=z+\mathrm{sign}(b)/8$, $f=(x-\tfrac12)^+$;
   - $c_d=2$, $m_4=1/4096$, $c_w=1/8$, $c_s=1/256$ (this value works for both the $2^\ell$ and the $4^\ell$ form of `hs`).

   Both theorems then elaborate when applied to this instance. One wrinkle: `IsProbabilityMeasure kinkOuter` is not a global instance, so applying the theorems needs a local instance; it is provable with `simp`.
3. **#2 assumes a stronger strong-error rate than #1 and #5.** Its `hs` is $(2^\ell)^2\,\mathbb E(g_{\ell+1}-g_\ell)^2\le c_s$, i.e. strong order 1, as for Milstein rather than Euler–Maruyama.
   - #5 does not assume this, so its proof cannot use the $\alpha_2=1$ mean rate from #2.
   - #5 effectively uses $|\mathbb E D_\ell|\le\sqrt{\mathbb E D_\ell^2}\lesssim2^{-|\ell|/2}$, i.e. $\alpha=(\tfrac12,\tfrac12)$. That is the first parameter set in #4, where $D_3=2$ (the boundary case $\alpha=\beta/2$).
4. **The example is degenerate, and "sharpness" in #3(c) is only against symmetric rates.**
   - In the example $g_{\ell+1}-g_\ell=-2^{-\ell}/16$ is deterministic, and $\mathbb E D\equiv0$. So the example does not test the mean-rate theorem (#2). I tested #2 on a separate instance with a density jump at the kink.
   - #3(c) excludes only bounds of the form $C\,2^{-\beta(\ell_1+\ell_2)}$. The example also satisfies the asymmetric bound $2^{\ell_1/2+2\ell_2}\operatorname{Var}D\le1.4\cdot10^{-4}$ (exponents summing to 2.5).
   - Part (b) still implies $2a+b\le3$ for any valid bound $C2^{-a\ell_1-b\ell_2}$. So $(1,1)$ is the only pair with both $a,b\ge1$, which is the only way to get $\eta\le0$.
5. **#4 holds for every ε, but the $D_3$ term never matters.**
   - The equality holds by definition for every real $\varepsilon$, including $\varepsilon\le0$ and $\varepsilon\ge1$: at $\eta=0$, `mimcBound` is literally $\varepsilon^{-2}|\log\varepsilon|^{e_1}$, and $e_1=4$.
   - The $D_3$ contribution enters only as the truncated ℕ difference $(D_3-3)$, which is 0 for both $D_3=2$ and $D_3=0$. So the theorem never exercises the $D_3$ part of the "Theorem 2" formula.
   - If the source formula used an ordinary difference instead, the two equalities would give exponents 3 and 1 and would be false. Someone should compare this against the paper.
   - My own derivation for $D=2$, $\alpha=(\tfrac12,\tfrac12)$, $\beta=\gamma=(1,1)$ does give $\varepsilon^{-2}|\log\varepsilon|^4$.
6. **#5 is stated in the standard form.**
   - Quantifier order: $\exists c_4>0\ \forall\varepsilon\in(0,e^{-1})\ \exists(\mathcal L,N)$. $c_4$ may depend on all the data (including ω and the costs) but not on ε.
   - The costs are only bounded above, and may even be negative. This is harmless, because the conclusion is an upper bound.
   - The target $\int f(\int g\,d\rho)\,d\nu$ is a genuine value, not a junk one: $G=\int g(z,\cdot)\,d\rho$ is pinned down by `hw` as the uniform a.e. limit of $\mathbb E[g_\ell\mid z]$, and `hg0` makes it $L^2$.
7. **In #1, #2 and #5, $g$ enters only through $G(z)=\int g(z,v)\,\rho(dv)$, and $g(z,\cdot)$ is never assumed integrable.** This is harmless (see point 6), but strictly the theorems are about an arbitrary function $G$ that satisfies `hw` and `hball`.
8. **The constant 384 in #6 is $4!\cdot2^4$,** from $e^y\ge y^4/4!$ with $y=-\tfrac12\log\varepsilon$. The true supremum of $\varepsilon^{1/2}|\log\varepsilon|^4$ on $(0,1]$ is $4096e^{-4}\approx75.02$, at $\varepsilon=e^{-8}$. So the bound is valid but not tight.

---

## Common definitions (as I read them)

- **Inner mean.** $\texttt{innerMean}\,g\,M\,z\,w=\frac1M\sum_{m<M}g(z,w_m)$, with $w\in\mathcal W^{\mathbb N}$.
- **Antithetic difference.** $\texttt{nestedDelta}\,f\,g\,0=f(g(z,w_0))$, and
  $$\texttt{nestedDelta}\,f\,g\,(\ell+1)=f(\bar g_{2^{\ell+1}})-\tfrac12f(\bar g^{(a)}_{2^\ell})-\tfrac12f(\bar g^{(b)}_{2^\ell}),$$
  where $(a)$ uses the first $2^\ell$ samples and $(b)$ the next $2^\ell$ (via `shiftSeq`).
- **Mixed difference.** $\texttt{nestedMimcDelta}\,f\,gh\,\ell_1\,0=\texttt{nestedDelta}\,f\,(gh\,0)\,\ell_1$, and
  $$\texttt{nestedMimcDelta}\,f\,gh\,\ell_1\,(\ell_2+1)=\texttt{nestedDelta}\,f\,(gh(\ell_2+1))\,\ell_1-\texttt{nestedDelta}\,f\,(gh\,\ell_2)\,\ell_1.$$
  So $D:=\texttt{nestedMimcDelta}\,f\,gh\,(\ell_1+1)(\ell_2+1)$ is the antithetic difference with $M=2^{\ell_1}$ samples per half, applied to $g_{\ell_2+1}$ minus the same applied to $g_{\ell_2}$, with common inner samples.
- **Law.** $\texttt{nestedLaw}\,\nu\,\rho=\nu\otimes\rho^{\otimes\mathbb N}$.
- **The example.**
  - $\texttt{kinkOuter}=\mathrm{Leb}|_{[0,1]}$ and $\texttt{kinkCoin}$ is the fair coin on `Bool`.
  - $\texttt{kinkInnerApprox}\,\ell\,z\,b=z\pm\tfrac18+2^{-\ell}/8$.
- **MIMC exponents.**
  - $\texttt{mimcEta}=\max_d(\gamma_d-\beta_d)/\alpha_d$.
  - $\texttt{mimcD2}=\#\{d:(\gamma_d-\beta_d)/\alpha_d=\eta\}$.
  - $\texttt{mimcD3}=\#\{d:\alpha_d=\beta_d/2\}$.
  - $\texttt{mimcBound}(\eta,e_1,e_2,\varepsilon)$ equals $\varepsilon^{-2}$ if $\eta<0$, $\varepsilon^{-2}|\log\varepsilon|^{e_1}$ if $\eta=0$, and $\varepsilon^{-2-\eta}|\log\varepsilon|^{e_2}$ otherwise.
- **A fact used throughout.** For the kink payoff $f=a_0+a_1x+c(x-k)^+$, the affine part cancels exactly in every antithetic difference. What remains is $c\,\varphi(a,b)$, with
  $$\varphi(a,b)=-\tfrac12\min(|a-k|,|b-k|)\,\mathbf 1\{a,b\text{ on opposite sides of }k\}.$$
  This function is 1-Lipschitz in each argument.

---

## 1. `nested_mimc_kink_variance_rate`

**Rendering.**

Setting: $\nu$ and $\rho$ are probability measures on $\mathcal Z$ and $\mathcal W$.

Hypotheses:
- **(hf)** $f(x)=a_0+a_1x+c\,(x-k)^+$.
- **(hgh)** Each $(z,v)\mapsto gh_\ell(z,v)$ is jointly measurable.
- **(hfib)** For every $\ell$ and $\nu$-a.e. $z$: $gh_\ell(z,\cdot)\in L^4(\rho)$, and the central fourth moment $\int(gh_\ell(z,v)-\int gh_\ell(z,\cdot)d\rho)^4d\rho\le m_4$. This bound is uniform in $\ell$ and $z$.
- **(hw)** For all $\ell$ and $\nu$-a.e. $z$: $2^\ell\,|G_\ell(z)-G(z)|\le c_w$, where $G_\ell(z)=\int gh_\ell(z,\cdot)d\rho$ and $G(z)=\int g(z,\cdot)d\rho$. This is a weak error of order 1, uniform in $z$.
- **(hball)** For all $t>0$: $\nu\{z:|G(z)-k|\le t\}\le c_d t$ (an `ENNReal.ofReal` bound).
- **(hs)** For all $\ell\in\mathbb N$: $2^\ell\iint(gh_{\ell+1}-gh_\ell)^2\,d(\nu\otimes\rho)\le c_s$. This is a variance rate $\beta=1$.

Conclusion, for all $\ell_1,\ell_2\in\mathbb N$: $D=\texttt{nestedMimcDelta}\,f\,gh\,(\ell_1+1)(\ell_2+1)\in L^2(\texttt{nestedLaw}\,\nu\,\rho)$, and
$$2^{\ell_1+\ell_2}\,\mathbb E[D^2]\le 8c_dc^2(1+16m_4)(1+c_w)+c^2\big(8c_s+\tfrac94c_dc_w^2(7+96m_4+3c_w)\big).$$
Here $2^{\ell_1+\ell_2}$ is a natural-number power in ℝ.

**Assessment.**

*Truth.* The statement is true; it is the expected $2^{-\ell_1-\ell_2}$ rate. Proof sketch, with $M=2^{\ell_1}$:

- **Direct bound.** $\mathbb E\Delta^2\le c^2\mathbb E[(a-b)^2\mathbf 1_{\text{straddle}}]$. The fourth moments, Markov's inequality, and the small-ball bound for $G_{\ell_2}$ (which is $c_d(t+c_w2^{-\ell_2})$, since $G_{\ell_2}$ lies within $c_w2^{-\ell_2}$ of $G$) give
  $$\mathbb E\Delta^2\lesssim c_dc^2\big(m_4^{3/4}M^{-3/2}+c_w\sqrt{m_4}\,2^{-\ell_2}M^{-1}\big).$$
  This is $\lesssim2^{-\ell_1-\ell_2}$ when $2^{-\ell_2}\ge M^{-1/2}$.
- **Lipschitz bound.** $|D|\le|c|(|\Delta a|+|\Delta b|)\mathbf 1_{R\cup R'}$, where $\Delta a=e(z)+\text{fluct}$ and $|e|\le\tfrac32c_w2^{-\ell_2}$.
  - The fluctuation part gives $\mathbb E[\text{fluct}^2]\le c_s2^{-\ell_2}/M$.
  - The bias part gives $c_w^2 2^{-2\ell_2}P(R\cup R')\lesssim c_dc_w^2 2^{-2\ell_2}(M^{-1/2}+c_w2^{-\ell_2})$, which is $\lesssim2^{-\ell_1-\ell_2}$ when $2^{-\ell_2}\le M^{-1/2}$.

The structure of the RHS (a $c_d(1+16m_4)(1+c_w)$ term, a $c_s$ term and a $c_dc_w^2(\dots)$ term) matches this two-regime proof. I did not re-derive the explicit constants.

Numerical stress tests (`r6_scale_scan.py`):
- Family: $gh_\ell=z+\sigma\,\mathrm{sign}(b)+\tau2^{-\ell}$, with $\nu$ uniform on $[k-R,k+R]$.
- Grid: $\sigma\in[2^{-6},2^3]$, $\tau\in[2^{-6},2^6]$, $\ell_1\le10$, $\ell_2\le17$.
- Result: max LHS/RHS $=1.1\cdot10^{-4}$.

On the literal example the RHS is $18.62$, while the LHS is at most $1.0745\cdot10^{-4}$ (`r6_reduced_grid_big.out`).

*Vacuity.* Not vacuous. `r6_nonvacuity.lean` compiles with axioms {propext, Classical.choice, Quot.sound}. It proves `hgh`, `hfib`, `hw`, `hball` and `hs` for the example and applies the theorem.

*Junk values.* None.
- `hs`: the difference $gh_{\ell+1}-gh_\ell$ has a bounded conditional second moment, by `hfib` and `hw`. So its integral is a genuine integral, not the junk 0.
- MemLp is part of the conclusion, so $\int D^2$ is genuine as well.
- $c_d\le0$ or $c_w<0$ would make `hball` or `hw` false, not the conclusion trivial.

*Unusual hypotheses.* $g$ appears only through $G$, and $g(z,\cdot)$ need not be integrable (see point 7). The fourth-moment bound must be uniform in $z$ and $\ell$; this is standard for the antithetic kink analysis.

*Standard result.* This is the variance rate of the antithetic nested-MLMC correction with a kink payoff (Giles–Haji-Ali style), lifted to the multi-index mixed difference. On its own, the inner direction has rate $M^{-3/2}$; the mixed difference has $2^{-\ell_1-\ell_2}$.

## 2. `nested_mimc_kink_mean_rate`

**Rendering.** The hypotheses are the same as in #1, except that `hs` is replaced by:
- **(hs)** $(2^\ell)^2\iint(gh_{\ell+1}-gh_\ell)^2\,d(\nu\otimes\rho)\le c_s$, i.e. a strong rate of $4^{-\ell}$ in variance.

Conclusion, for all $\ell_1,\ell_2$: $D\in L^2$, and
$$2^{\ell_1/2+\ell_2}\,|\mathbb E D|\le 12c_d|c|(1+80m_4)(1+c_w)+|c|\big(1+c_s+3c_dc_w(7+96m_4+3c_w)\big).$$
The exponent $\ell_1/2+\ell_2$ is real (`rpow`, base 2).

**Assessment.**

*Truth.* True. Proof sketch:
- **Lipschitz bound with Cauchy–Schwarz on the fluctuation.** This gives $|\mathbb E D|\le|c|\big(2\sqrt{c_s}\,2^{-\ell_2}M^{-1/2}+3c_w2^{-\ell_2}P(R\cup R')\big)$, with $P(R\cup R')\lesssim c_d(M^{-1/2}+c_w2^{-\ell_2})$.
- **Direct bound.** $|\mathbb E\Delta|\lesssim c_dM^{-1/2}(M^{-1/2}+c_w2^{-\ell_2})$.

Taking the better of the two bounds in each regime gives $\lesssim2^{-\ell_1/2-\ell_2}$. The $4^{-\ell}$ strong rate is what turns $\sqrt{\mathbb E\,\text{fluct}^2}$ into $2^{-\ell_2}M^{-1/2}$.

The rate is attained. With a density jump at the kink (density 2/3 then 4/3, still $c_d=2$), exact enumeration in `r6_literal_enum.out` and `r6_literal_enum_l3.out` gives $2^{\ell_1/2+\ell_2}|\mathbb ED|\approx5\cdot10^{-4}$ to $1.3\cdot10^{-3}$, against an RHS of $34.08$. The scaled-family scan gives max LHS/RHS $=4.8\cdot10^{-4}$.

*Vacuity.* Not vacuous: the same Lean instance works, with `hs2`.

*Junk values.* None.

*Unusual hypotheses.* `hs` requires strong order 1, which is stronger than in #1 and #5 (see point 3). On `kinkOuter` itself the example has $\mathbb ED\equiv0$, so the conclusion is trivial there; it is not trivial for the density-jump variant.

*Standard result.* The weak or bias rate of the MIMC mixed difference for the antithetic kink estimator: $\alpha=(\tfrac12,1)$.

## 3. `nested_mimc_kink_rate_sharp`

**Rendering.** Take $f=(x-\tfrac12)^+$, $gh=\texttt{kinkInnerApprox}$, $\nu=U[0,1]$ and $\rho=$ fair coin, and write $D_{\ell_1,\ell_2}=\texttt{nestedMimcDelta}\,f\,gh\,(\ell_1+1)(\ell_2+1)$. The statement has three parts:
- **(a)** For all $\ell_1,\ell_2$: $D_{\ell_1,\ell_2}\in L^2$, $\mathbb E D_{\ell_1,\ell_2}=0$, and $2^{\ell_1+\ell_2}\operatorname{Var}D_{\ell_1,\ell_2}\le19$.
- **(b)** For all $j$: $2^{-18}\le2^{3j+1}\operatorname{Var}D_{2j,\,j+1}$. The packet writes this with indices $(2j+1,\,j+2)$ and factor $2^{2j+(j+1)}$.
- **(c)** For every real $\beta>1$, there is no $C\in\mathbb R$ with $\operatorname{Var}D_{\ell_1,\ell_2}\le C\,2^{-(\beta\ell_1+\beta\ell_2)}$ for all $\ell_1,\ell_2$.

`variance` is Mathlib's `(evariance X μ).toReal`. Since $D$ is bounded, this equals the ordinary variance.

**Assessment.**

*Truth.* True. Write $D(z)=\psi(z+s)-\psi(z+s')$ with:
- $s=2^{-\ell_2-1}/8$ and $s'=2^{-\ell_2}/8$;
- $\psi$ a non-positive tent of base $w=|S_a-S_b|/(8M)$ and slopes $\pm\tfrac12$;
- all supports inside $[0,1]$.

Then:
- **$\mathbb ED=0$** by translation invariance.
- **$\mathbb ED^2=\mathbb E\,F(W,\delta)$**, where $\delta=2^{-\ell_2-4}$ and $F(w,\delta)=\int(\psi(y+\delta)-\psi(y))^2dy$. This equals $\delta^2(w-\delta)/4$ for $\delta\le w/2$, and $w^3/24$ for $\delta\ge w$.
- **(a)** The bound is $\max=1.0745\cdot10^{-4}$, at $(\ell_1,\ell_2)=(2,0)$. The Gaussian-limit envelope is $1.063\cdot10^{-4}$.
- **(b)** The values for $j=0,\dots,6$ are $5.34,5.57,5.52,5.49,5.487,5.486,5.486\,(\times10^{-5})$, about 14.4 times $2^{-18}$. An analytic bound for all $j$ follows from Szarek's inequality $\mathbb E|T|\ge\sqrt M$:
  $$\mathbb EF\ge\tfrac{\delta^2}{8}\big(\mathbb EW-2\delta\big)\ge2^{-3j-17},$$
  so $2^{3j+1}\operatorname{Var}\ge2^{-16}$.
- **(c)** follows from (b): $C\ge2^{-18}2^{(\beta-1)(3j+1)}\to\infty$. A $C\le0$ is impossible because the variance is positive.

The literal enumeration (`r6_literal_enum*.out`) agrees exactly with the reduction (`r6_reduced_grid.out`).

*Vacuity.* Not applicable: the statement has no hypotheses.

*Junk values.* None. $\operatorname{Var}=\mathbb ED^2$ is a genuine value.

*Remarks.* The constants are loose (19, against an actual value of about $10^{-4}$). The "sharpness" in (c) is only against symmetric rates. The example satisfies $\operatorname{Var}\le C2^{-\ell_1/2-2\ell_2}$ (`r6_asym_rate.out`), though (b) still rules out any separable pair other than $(1,1)$ with both exponents at least 1 (point 4).

*Standard result.* A lower-bound or sharpness example for the mixed-difference variance rate.

## 4. `nested_mimc_kink_exponents`

**Rendering.** With $D=2$:
- For $\alpha=(\tfrac12,\tfrac12)$, $\beta=\gamma=(1,1)$: $\eta=0$, $D_2=2$, $D_3=2$.
- For $\alpha=(1,1)$: $D_3=0$.
- For every real $\varepsilon$, $\texttt{mimcBound}(\eta,\;2D_2+(D_3\dot-3),\;(D_2-1)(2+\eta)+(D_3\dot-1),\;\varepsilon)=\varepsilon^{-2}|\log\varepsilon|^4$, for both parameter sets. Here $\dot-$ is truncated ℕ subtraction, cast to ℝ.

**Assessment.**

*Truth.* True by direct computation:
- $(1-1)/\tfrac12=0$ in both coordinates, so $\eta=0$ and $D_2=2$.
- $\tfrac12=1/2$ in both coordinates gives $D_3=2$; $1\ne1/2$ gives $D_3=0$.
- $e_1=4+0=4$ in both cases.

My scratch checks in `r6_scratch_check.lean` re-prove $\eta=0$, both $D_3$ values, and `mimcBound 0 4 _ ε = ε^(-2)·|log ε|^4` for every ε. Since the $\eta=0$ branch is syntactically the RHS, the equality holds for all $\varepsilon$, including $\varepsilon\le0$ and $\varepsilon\ge1$.

Independent check: MIMC with $V_\ell\asymp2^{-|\ell|}$, $C_\ell\asymp2^{|\ell|}$ and bias $\lesssim2^{-|\ell|/2}$ over total-degree sets has cost $\asymp\varepsilon^{-2}L^4$ with $L\approx2\log_2(1/\varepsilon)$. That is $\varepsilon^{-2}|\log\varepsilon|^4$ (`r6_complexity_model.out`).

*Junk values.* The $D_3$ term vanishes only through truncated ℕ subtraction ($2\dot-3=0\dot-3=0$). The outcome agrees with my independent derivation, so this looks intended (as $\max(0,D_3-3)$), but it means the $D_3$ part of the "Theorem 2" formula is never tested here (point 5).

## 5. `nested_mimc_kink_complexity`

**Rendering.**

Data and hypotheses:
- The hypotheses of #1, with the $2^\ell$ form of `hs`, plus `hg0`: $gh_0^2$ is integrable on $\nu\otimes\rho$.
- A probability space $(\Omega,\mu)$ and samples $\omega_{(\ell,n)}:\Omega\to\mathcal Z\times\mathcal W^{\mathbb N}$, indexed by $(\ell,n)\in\mathbb N^{2}\times\mathbb N$. Each sample is measure-preserving onto `nestedLaw ν ρ`, and the whole family is mutually independent (`iIndepFun`).
- Integrable costs with $\mathbb E[\mathrm{cost}_{\ell,n}]=C_\ell\le c_3\,2^{\ell_0+\ell_1}$, where $c_3>0$.

Conclusion: there is a $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist a finite $\mathcal L\subset\mathbb N^2$ and $N:\mathbb N^2\to\mathbb N_{>0}$ with:
- $\mathbb E_\mu\big[\big(\sum_{\ell\in\mathcal L}\frac1{N_\ell}\sum_{n<N_\ell}D_\ell(\omega_{\ell,n})-\int f(G)\,d\nu\big)^2\big]<\varepsilon^2$, where $D_\ell=\texttt{nestedMimcDelta}\,f\,gh\,\ell_0\,\ell_1$ (base levels included);
- $\mathbb E_\mu\big[\sum_{\ell\in\mathcal L}\sum_{n<N_\ell}\mathrm{cost}_{\ell,n}\big]\le c_4\,\varepsilon^{-2}|\log\varepsilon|^4$.

**Assessment.**

*Truth.* True. The argument:
- All $D_\ell$ have $V_\ell\lesssim2^{-|\ell|}$:
  - #1 covers interior levels;
  - base levels $(\ell_0,0)$ follow from a small-ball estimate with offset $c_w$;
  - base levels $(0,\ell_1)$ follow from $f$ being Lipschitz together with `hs`;
  - $(0,0)$ follows from `hg0`.
- $|\mathbb ED_\ell|\le\sqrt{V_\ell}$. The double telescoping sum converges to $\int f(G)\,d\nu$, by `hw` and the $L^2$ law of large numbers for the inner mean.
- Total-degree sets with standard allocation then give cost $\lesssim\varepsilon^{-2}L^4+\sum_{|\ell|\le L}C_\ell\lesssim\varepsilon^{-2}|\log\varepsilon|^4$. The model run (`r6_complexity_model.out`) shows cost$/(\varepsilon^{-2}|\log\varepsilon|^4)$ decreasing towards a constant.

Quantifier order is standard (point 6).

*Vacuity.* Not vacuous. Use the example (where `hg0` holds because $\nu$ is supported on $[0,1]$), $\Omega=$ an infinite product of `nestedLaw` with coordinate maps, and $\mathrm{cost}=2^{|\ell|}$.

*Junk values.* None.
- The estimator is in $L^2$, so the MSE integral is genuine.
- The target $\int f(G)\,d\nu$ is genuine: $G$ is a.e.-measurable, being a uniform limit of the measurable $G_\ell$, and $G\in L^2$.
- Negative costs would only help, and the hypotheses only bound costs above.

*Standard result.* The MIMC complexity theorem in the boundary case $\eta=0$ with $D_2=2$: cost $\varepsilon^{-2}|\log\varepsilon|^{4}$.

## 6. `nested_mimc_kink_beats_mlmc`

**Rendering.**
- **(i)** For all $0<\varepsilon\le1$: $\varepsilon^{-2}|\log\varepsilon|^4\le384\,\varepsilon^{-2.5}$.
- **(ii)** $\varepsilon^{-2}|\log\varepsilon|^4=o(\varepsilon^{-2.5})$ as $\varepsilon\to0^+$, along `𝓝[>] 0`.

All powers are `rpow` with a positive base.

**Assessment.**
- **(i)** is equivalent to $x^4e^{-x/2}\le384$ for $x=-\log\varepsilon\ge0$. The maximum is $4096e^{-4}=75.02$, at $x=8$. The constant is $384=4!\cdot2^4$, from $e^{x/2}\ge(x/2)^4/24$.
- **(ii)** holds because $\varepsilon^{1/2}|\log\varepsilon|^4\to0$; at $\varepsilon=10^{-32}$ it is already $3\cdot10^{-9}$ (`r6_beats_mlmc.out`).

Both parts are true, with no junk values: $\varepsilon>0$ throughout, and $|\log1|=0$ is handled correctly. This is the elementary comparison $\varepsilon^{-2}|\log\varepsilon|^4\ll\varepsilon^{-2.5}$; the docstring presumably sets it against single-index nested MLMC at $\varepsilon^{-2.5}$.
