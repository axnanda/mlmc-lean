# Blind read-back: `packet_R56_condexp` (round 28)

| | |
|---|---|
| Date | 2026-10-09 |
| Packet | `readback/round28/packet_R56_condexp.lean` |
| Declarations audited | 4 (1 new definition, 3 theorems) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round28/work_R56_condexp/`: `Scratch.lean`/`.out` (elaboration and junk checks), `MemLpCheck.lean`/`.out` (formal proof of the `MemLp` conjunct), `mc_check.py`/`.out` (Monte Carlo), `cross_check.py`/`.out` (independent cross-checks), `asymptotic_constant.py`/`.out` (leading-order constant compared with the Monte Carlo) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `MLMC.gbmMilLogRatio` | def | n/a (definition; not used by #2–#4) | n/a | n/a |
| 2 | `MLMC.gbm_digital_condExp_variance_endpoint` | theorem | **true** | no | no |
| 3 | `MLMC.gbm_digital_condExp_variance_rate_endpoint` | theorem | **true** (special case of #2) | no | no |
| 4 | `MLMC.gbm_digital_condExp_variance_endpoint_log` | theorem | **true** (same as #2 up to the constant) | no | no |

## Main points for a human auditor

- **Which constant depends on what.** In #2 and #4 the constant $C$ depends only on $(r,\sigma,T)$. It holds for every $s_0\neq0$, every $K\in\mathbb R$ and every $\ell\in\mathbb N$. In #3, $C$ may also depend on $s_0$ and $K$.
  - The uniformity in $(s_0,K)$ is genuine, but it reduces exactly to uniformity in the single ratio $K/s_0$. The Milstein path is linear in $s_0$ (proved in Lean in `Scratch.lean`). The map $(s_0,K)\mapsto(-s_0,-K)$ sends $\Delta$ to $-\Delta$ (checked numerically to $3\times10^{-14}$).
- **No junk value enters any conclusion** when $\sigma\ne0$, $T>0$ and $s_0\neq0$:
  - The denominators $|\sigma S|\sqrt h$ vanish only on a null set, and never once $h$ is small.
  - $|\Delta|\le 1$ and $\Delta$ is measurable. I proved the `MemLp Δ 2` conjunct formally for all parameters in `MemLpCheck.lean`, using only `propext`, `Classical.choice` and `Quot.sound`.
  - `stdNormalSeq` is a genuine probability measure, not the junk `0` branch of `infinitePi`.
  - Every `rpow` base is $>0$.
  - `Real.log (T / 2 ^ (ℓ + 1))⁻¹ ^ (5/2 : ℝ)` is $(\log(1/h))^{5/2}$ (checked by `rfl`), and $\log(1/h)>1$ under #4's hypothesis.
  - The ℕ-subtractions `2^ℓ - 1` and `2^(ℓ+1) - 2` never truncate.
- **The excluded parameter values are exactly the junk ones.** For $s_0=0$, $\sigma=0$ or $T\le 0$, both payoffs become `cdf (x/0) = Φ(0)`, so $\Delta\equiv 0$ (proved in `Scratch.lean`). The hypotheses remove these cases, so nothing depends on a junk value. None of the hypotheses is stronger than needed in a harmful way.
- **The rate is slack, not wrong.** A Monte Carlo of the definitions as written ($s_0=K=1$, $r=0.05$, $\sigma=0.2$, $T=1$) gives $E[\Delta_\ell^2]/h_\ell^{3/2}\approx 0.0045$, flat for $\ell=4,\dots,11$.
  - My leading-order expansion gives $E[\Delta^2]\sim\kappa(K/s_0)\,h^{3/2}$ with $\kappa$ bounded in $K$. It matches the Monte Carlo to within about 3% for both tested parameter sets.
  - So the sharp rate is $O(h^{3/2})$, and the factors $(\ell+1)^{5/2}$ and $\log^{5/2}(1/h)$ are proof artefacts. They are harmless for MLMC complexity, since $\beta=3/2>\gamma=1$.
- **Redundancy.** The variance conjunct follows from the second-moment conjunct, because $\operatorname{Var}X\le E X^2$. #3 is #2 specialised. #4 and #2 imply each other up to the constant, since $\ell+1\le\frac{1+\log^+T}{\log 2}\log(1/h)$ whenever $h<e^{-1}$.
- **Minor points (no effect on meaning).**
  - In #3, `K` is an implicit argument that no hypothesis determines, so a caller must supply it by unification or with `(K := …)`.
  - The payoff is undiscounted (there is no $e^{-rT}$).
  - `gbmMilLogRatio` does not appear in any of the three statements.

## Notation (from the appended definitions)

- `stdNormalSeq` $=\bigotimes_{i\in\mathbb N}N(0,1)$ on $\mathbb R^{\mathbb N}$ (Mathlib `Measure.infinitePi`). Every factor is a probability measure, so this is the genuine product (instance `IsProbabilityMeasure`, re-checked in `MemLpCheck.lean`). Write $z=(z_0,z_1,\dots)$.
- $\Phi$ = `cdf (gaussianReal 0 1)`, the standard normal CDF. `gaussianReal 0 1` has mean 0 and variance 1, and `cdf_eq_real` applies.
- `milsteinStep a b h S dW` $=S+a(S)h+b(S)\,dW+\tfrac12 b(S)\,b'(S)\,(dW^2-h)$, where $b'$ = `deriv b`.
  - With $a(S)=rS$, $b(S)=\sigma S$ (so $b'\equiv\sigma$) and $dW=\sqrt h\,x$, one step is $S\mapsto S\cdot F_h(x)$, where $F_h(x)$ = `gbmMilFactor r σ h x` $=1+rh+\sigma\sqrt h\,x+\tfrac{\sigma^2}{2}\big((\sqrt h\,x)^2-h\big)$. This identity is verified in Lean.
  - Hence `milsteinPath … h s₀ w n` $=s_0\prod_{i<n}F_h(w_i)$.
- `pairAvg z k` $=(z_{2k}+z_{2k+1})/\sqrt2$.
- Fix $\ell$ and set $N=2^\ell$, coarse step $H=T/2^\ell$, fine step $h=h_\ell=T/2^{\ell+1}=H/2$.
  - Fine path: $S_n=s_0\prod_{i<n}F_h(z_i)$.
  - Coarse path: $\hat S_k=s_0\prod_{j<k}F_H\big((z_{2j}+z_{2j+1})/\sqrt2\big)$.
- `gbmDigitalCondFine r σ T s₀ K (ℓ+1) z` $=P^f:=\Phi\Big(\dfrac{S_{2N-1}(1+rh)-K}{|\sigma S_{2N-1}|\sqrt h}\Big)$.
- `gbmDigitalCondCoarse r σ T s₀ K ℓ z` $=P^c:=\Phi\Big(\dfrac{\hat S_{N-1}(1+rH)+\sigma\hat S_{N-1}\sqrt h\,z_{2N-2}-K}{|\sigma\hat S_{N-1}|\sqrt h}\Big)$.
- In both payoffs Lean's $x/0=0$ applies whenever a denominator vanishes.
- $\Delta_\ell:=P^f-P^c$. It depends only on $z_0,\dots,z_{2N-2}$.

**Interpretation.** I checked that this reading is correct, including for $S<0$, thanks to the $|\cdot|$ in the standard deviations.
- $P^f=\mathbb P(S_{2N}>K\mid z_0,\dots,z_{2N-2})$ when the last fine step is the Euler step $S_{2N}=S_{2N-1}(1+rh+\sigma\sqrt h\,z_{2N-1})$.
- $P^c=\mathbb P(\hat S_N>K\mid z_0,\dots,z_{2N-2})$ when the last coarse step is the Euler step $\hat S_N=\hat S_{N-1}\big(1+rH+\sigma\sqrt h(z_{2N-2}+z_{2N-1})\big)$, conditioned on its first-half fine increment.
- This is Giles' conditional-expectation estimator for the digital payoff $\mathbf 1\{S_T>K\}$ under the GBM $dS=rS\,dt+\sigma S\,dW$, with Milstein steps and no discount factor.
- $E[P^c_\ell]=E[P^f_\ell]$, so the telescoping sum is consistent.

---

## 1. `gbmMilLogRatio` (definition)

**Rendering.** For $r,\sigma,k,x\in\mathbb R$:
$$\mathrm{gbmMilLogRatio}(r,\sigma,k,x)=\log F_k(x)-\Big(\big(r-\tfrac{\sigma^2}{2}\big)k+\sigma\sqrt k\,x\Big),$$
where $F_k$ is `gbmMilFactor`.
- `Real.log` follows Mathlib's conventions: $\log y=\log|y|$ for $y\ne0$, and $\log 0=0$.
- `Real.sqrt` gives $\sqrt k=0$ for $k<0$.
- The argument `k` is a step size, not a level.

For $k\ge0$ the definition is the log of the one-step Milstein growth factor for GBM, minus the exact GBM log-increment $(r-\sigma^2/2)k+\sigma\,\Delta W$ for the same $\Delta W=\sqrt k\,x$. That is, it is the one-step log-error of the Milstein scheme.

**Assessment.** This is a definition, so there is nothing to prove.
- $F_k(x)=\tfrac12(\sigma\sqrt k\,x+1)^2+\tfrac12+(r-\tfrac{\sigma^2}{2})k$. So $F_k>0$ for every $x$ if and only if $\tfrac12+(r-\sigma^2/2)k>0$, which always holds for small $k\ge0$.
- Otherwise `Real.log` returns the junk value $\log|F_k|$ near $x=-1/(\sigma\sqrt k)$.
- For fixed $x$ and small $k$, the value is $k^{3/2}\big[(\tfrac{\sigma^3}{2}-\sigma r)x-\tfrac{\sigma^3}{6}x^3\big]+O(k^2)$, consistent with strong order 1.
- The definition does not appear in the statements of #2–#4 (presumably it is a proof helper), so its junk regime cannot affect them.
- Standard fact: the Milstein scheme for GBM is multiplicative, and its one-step log-error is $O(k^{3/2})$.

## 2. `gbm_digital_condExp_variance_endpoint`

**Rendering.** For all $r,\sigma\in\mathbb R$ and $T\in\mathbb R$ (implicit) with $\sigma\neq0$ and $T>0$, there exists a real $C\ge0$, depending only on $(r,\sigma,T)$, such that for all real $s_0\ne0$, all real $K$ and all $\ell\in\mathbb N$, with $h_\ell=T/2^{\ell+1}$ (a natural-number power in $\mathbb R$):
1. $\Delta_\ell\in L^2(\texttt{stdNormalSeq})$ (`MemLp _ 2`);
2. $\int\Delta_\ell^2\,d\,\texttt{stdNormalSeq}\le C\,h_\ell^{3/2}\,(\ell+1)^{5/2}$. Here the integral is the Bochner integral, the square is a natural-number power, $3/2$ and $5/2$ are real exponents (`Real.rpow`), and $(\ell+1)$ is the real number `(ℓ:ℝ)+1`;
3. $\operatorname{Var}(\Delta_\ell)\le C\,h_\ell^{3/2}(\ell+1)^{5/2}$, where `ProbabilityTheory.variance` is `(evariance …).toReal`.

**Assessment.**
- **Truth: true.** Proof sketch:
  1. *Reductions.* Each payoff is $\Phi$ of $\operatorname{sgn}(s_0)\cdot(\text{path-only quantity}-K/s_0)/(\text{path-only quantity})$. So $\Delta$ depends on $(s_0,K)$ only through $K/s_0$, and $(s_0,K)\to(-s_0,-K)$ sends $\Delta$ to $-\Delta$. Also, $(\sigma,z)\to(-\sigma,-z)$ leaves $\Delta$ unchanged and preserves the law of $z$. So we may assume $s_0=1$, $\sigma>0$ and $K\in\mathbb R$ arbitrary.
  2. *Small levels.* $|\Delta|\le1$ and the right-hand side is $>0$, so any finite set of levels costs nothing. For $H<H_0(r,\sigma)$, every factor satisfies $F_h,F_H\ge\tfrac12+(r-\tfrac{\sigma^2}{2})H>0$, so all paths are positive.
  3. *Main estimate.* Put $u=S_{2N-2}$, $v=\hat S_{N-1}$ and $z=z_{2N-2}$, which is independent of $(u,v)$. Let $x_f$ and $x_c$ be the two arguments of $\Phi$. Then
     - $x_c=(1-K/v)/(\sigma\sqrt h)+z+O(\sqrt h)$;
     - $x_f-x_c=\sqrt h\,\big[-\sigma x_c z+\tfrac{\sigma}{2}(z^2-1)+\xi/\sigma\big]+O(h)$, where $\xi=\log(u/v)/h$ is bounded in every $L^p$ by the strong order 1 of Milstein for the fine–coarse pair.
  4. *Where $\Delta$ is non-negligible.* On the event $\{|x_c|\le c\sqrt{\log(1/h)}\}$ we have $|\Delta|\lesssim\sqrt h\cdot\mathrm{polylog}$. Off it, $|\Delta|\le h^{c'}$. The event has probability $O(\sqrt{h\log(1/h)})$ uniformly in $K$: $\log v$ is a sum of $N-1$ i.i.d. terms of size $\sqrt H$, so its concentration function at scale $\sqrt h$ is $O(\sqrt h)$ by the Kolmogorov–Rogozin inequality.
  5. *Conclusion.* Truncating $\xi$ gives $E\Delta^2=O(h^{3/2}\,\mathrm{polylog}(1/h))$ uniformly in $K$, which is at most the stated bound. More precisely, $E\Delta^2\sim\kappa(K/s_0)\,h^{3/2}$ with $\kappa=\frac{\sigma\,p(\log K)}{2\sqrt\pi}\big(\sigma^2+E[\xi^2\mid W_T]/\sigma^2\big)$, where $p$ is the density of $\log S_T$. $\kappa$ is bounded in $K$.
  6. *The other conjuncts.* Conjunct 3 follows from conjunct 2, since $\operatorname{Var}X\le EX^2$ for $X\in L^2$. Conjunct 1 holds because $\Delta$ is bounded and measurable (proved formally).
- **Numerics** (`mc_check.out`). Parameters: $s_0=K=1$, $r=0.05$, $\sigma=0.2$, $T=1$. The inner $z_{2N-2}$ integral is done by quadrature. I used 20000 paths for $\ell\le9$ and 8000 paths for $\ell=10,11$.

  | $\ell$ | $h$ | $E\Delta^2$ | rel. SE | $E\Delta^2/h^{3/2}$ | $\operatorname{Var}/h^{3/2}$ | $E\Delta^2/(h^{3/2}(\ell+1)^{5/2})$ |
  |---|---|---|---|---|---|---|
  | 0 | 0.5 | 8.30e-4 | exact | 0.0023 | 0.0001 | 0.0023 |
  | 1 | 0.25 | 2.69e-4 | 0.4% | 0.0021 | 0.0017 | 0.00038 |
  | 2 | 0.125 | 1.46e-4 | 0.5% | 0.0033 | 0.0032 | 0.00021 |
  | 3 | 6.25e-2 | 6.14e-5 | 0.6% | 0.0039 | 0.0039 | 0.00012 |
  | 4 | 3.13e-2 | 2.36e-5 | 0.8% | 0.0043 | 0.0043 | 8e-5 |
  | 5 | 1.56e-2 | 8.66e-6 | 1.0% | 0.0044 | 0.0044 | 5e-5 |
  | 6 | 7.81e-3 | 3.12e-6 | 1.2% | 0.0045 | 0.0045 | 3e-5 |
  | 7 | 3.91e-3 | 1.11e-6 | 1.5% | 0.0046 | 0.0046 | 3e-5 |
  | 8 | 1.95e-3 | 3.93e-7 | 1.9% | 0.0046 | 0.0046 | 2e-5 |
  | 9 | 9.77e-4 | 1.35e-7 | 2.3% | 0.0044 | 0.0044 | 1e-5 |
  | 10 | 4.88e-4 | 5.19e-8 | 4.2% | 0.0048 | 0.0048 | 1e-5 |
  | 11 | 2.44e-4 | 1.68e-8 | 5.3% | 0.0044 | 0.0044 | 1e-5 |

  - $E\Delta^2/h^{3/2}$ (and the variance ratio) stays bounded and approaches the predicted $\kappa(1)=0.00455$.
  - For $K\in\{0.85,1,1.03,1.1,1.25\}$, the predicted and Monte Carlo constants agree within 2.5% (`asymptotic_constant.out`).
  - A wide $K$ grid at $\ell=6$ shows a single bump at the mode of $S_T$, and $\approx0$ for $K\le0.01$ and $K=5$ (`cross_check.out`).
  - A second parameter set ($\sigma=1$, $r=0$; $K=1$ and $K=e^{-1/2}$) gives $E/h^{3/2}\in[0.11,0.21]$ for $\ell=2,\dots,9$ with no growth. The predictions are 0.149 and 0.169; the level 5–9 Monte Carlo means are 0.146 and 0.174, within 3.2%.
  - Independent checks: at $\ell=0$, `mpmath` quadrature matches the trapezoid rule to 9 digits. At $\ell=4$, a crude Monte Carlo that samples every normal through the direct transcription gives $(2.31\pm0.08)\times10^{-5}$, against $2.36\times10^{-5}$.
  - The direct transcription (including the Lean $x/0$ and $\sqrt{\cdot}$ conventions) and the fast formulas agree path by path to $5\times10^{-14}$.
  - For these parameters, $C\approx0.0025$ suffices on the tested grid of $K$ and $\ell$. The worst case is $\ell=0$, $K=1.03$, with ratio 0.00245.
- **Vacuity: no.** Take $r=0.05$, $\sigma=0.2$, $T=1$, $s_0=K=1$. Then $E\Delta_0^2=8.3\times10^{-4}>0$ and the right-hand side tends to $0$, so the bound has real content.
- **Junk values: none.**
  - With $\sigma\neq0$, $T>0$ and $s_0\ne0$, each Milstein factor is a nondegenerate quadratic in its normal. So $S_{2N-1}=0$ or $\hat S_{N-1}=0$ only on a null set, and never once $\tfrac12+(r-\sigma^2/2)H>0$. The $x/0$ junk in $\Phi$'s argument therefore never affects the integrals.
  - $\sqrt{T/2^{\ell}}$ and $\sqrt{T/2^{\ell+1}}$ are square roots of positive numbers.
  - The integrand is bounded and measurable on a probability space.
  - All rpow bases are positive: $h>0$ and $\ell+1\ge1$.
  - In the excluded cases ($s_0=0$, $\sigma=0$, $T\le0$) the statement would hold trivially through junk ($\Delta\equiv0$; for $T<0$, Mathlib gives $x^{3/2}=0$ for $x<0$). The hypotheses rule these cases out.
- **Hypotheses.** These are standard non-degeneracy conditions, and they are harmless. In Lean they are not even needed for truth.
  - The statement is weaker than the sharp $O(h^{3/2})$ only by the polylog factor.
  - It is stronger than the $O(h^{3/2-\delta})$ rate that, as I recall, is proved in the literature.
- **Standard result.**
  - Giles (2008), "Improved multilevel Monte Carlo convergence using the Milstein scheme" (MCQMC 2006): for the digital option, the final step is handled analytically by a conditional expectation, and $V_\ell=O(h_\ell^{3/2})$ is observed numerically.
  - Giles, Debrabant and Rößler, "Analysis of multilevel Monte Carlo path simulation using the Milstein discretisation" (arXiv 2013; DCDS-B 2019): as I recall, this proves $O(h^{3/2-\delta})$ for every $\delta>0$.

## 3. `gbm_digital_condExp_variance_rate_endpoint`

**Rendering.** For all $r,\sigma$ and implicit $s_0,T,K\in\mathbb R$ with $s_0\ne0$, $\sigma\ne0$ and $T>0$, there exists $C\ge0$, now allowed to depend on $(r,\sigma,s_0,T,K)$, such that for every $\ell\in\mathbb N$ the same three conjuncts as in #2 hold: `MemLp`, $E\Delta_\ell^2\le C h_\ell^{3/2}(\ell+1)^{5/2}$, and $\operatorname{Var}\Delta_\ell\le C h_\ell^{3/2}(\ell+1)^{5/2}$.

**Assessment.**
- **Truth: true.** Instantiate #2 at the given $s_0$ and $K$.
- **Vacuity: no** (same instance as #2).
- **Junk values: none**, for the same reasons as #2.
- **Hypotheses.** Nothing unusual. One minor point: `K` is implicit but appears in no hypothesis, so a caller must supply it by unification or with `(K := …)`. This affects usability only.
- **Standard result.** This is the fixed-parameter "variance rate" form used by MLMC complexity theorems: $V_\ell\le c\,2^{-\beta\ell}$ with $\beta=3/2$, here up to an $(\ell+1)^{5/2}$ factor.

## 4. `gbm_digital_condExp_variance_endpoint_log`

**Rendering.** For all $r,\sigma$ and implicit $T$ with $\sigma\ne0$ and $T>0$, there exists $C\ge0$, depending only on $(r,\sigma,T)$, such that for all $s_0\neq0$, all $K$ and all $\ell\in\mathbb N$ with $h_\ell=T/2^{\ell+1}<e^{-1}$:
1. $\Delta_\ell\in L^2$;
2. $E\Delta_\ell^2\le C\,h_\ell^{3/2}\,\big(\log(1/h_\ell)\big)^{5/2}$;
3. $\operatorname{Var}\Delta_\ell\le C\,h_\ell^{3/2}\,\big(\log(1/h_\ell)\big)^{5/2}$.

`Real.log (T / 2 ^ (ℓ + 1))⁻¹ ^ (5 / 2 : ℝ)` elaborates as `(Real.log ((T / 2 ^ (ℓ + 1))⁻¹)) ^ (5/2 : ℝ)`, checked by `rfl` in `Scratch.lean`.

**Assessment.**
- **Truth: true.** It is the same statement as #2 up to the constant.
  - If $h<e^{-1}$ then $\log(1/h)>1$, and $(\ell+1)\log2=\log T+\log(1/h)\le(1+\log^+T)\log(1/h)$. So #2 implies #4 with $C_4=C_2\big((1+\log^+T)/\log2\big)^{5/2}$. I confirmed this numerically for $T\in\{0.01,0.5,1,10,1000\}$ (`cross_check.out`).
  - Conversely, #4 together with $|\Delta|\le1$ for the finitely many remaining levels gives #2.
- **Vacuity: no.** For $T=1$, every $\ell\ge1$ satisfies the hypothesis ($h\le1/4<e^{-1}\approx0.368$).
- **Junk values: none.** Both rpow bases, $h>0$ and $\log(1/h)>1$, are positive.
- **Hypotheses.** The condition $h<e^{-1}$ is needed and not suspicious. At $h=1$ the right-hand side is $0$ (since $\log1=0$). For $h>1$ it is $|\log h|^{5/2}\cos(5\pi/2)=0$ in Mathlib's negative-base rpow. So without the restriction the claim would fail at such levels.
- **Standard result.** Same as #2, in the $\log(1/h)$ form.
