# Blind read-back report: R29 (`MlmcLean.GBMStrongLp`)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round20/packet_R29_gbmlp.lean` (relative to the scratchpad) |
| declarations audited | 23: 9 definitions + 14 theorems in the module. The 11 definitions appended from other modules are rendered in §0. |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round20/work_R29/` (`moment_check.py/.out`, `moment_check2.py/.out`, `digital_bound.py/.out`, `digital_mc.py/.out`, and the Lean scratch files `names.lean`, `scratch_full.lean`, `elab.lean` with `.out`) |

**Elaboration check.** I compiled `work_R29/scratch_full.lean`. It is a verbatim copy of the packet, with every definition and theorem placed in a separate namespace `R29`. For each of the 20 definitions I checked `@R29.d = @MLMC.d`: by `rfl`, or by `funext` plus induction for the recursive `emPath` and `milsteinPath`. For each of the 14 theorems I checked `type_of% @R29.t = type_of% @MLMC.t`. Everything compiled with no errors, so the packet statements are exactly the elaborated ones. `elab.lean` (with `pp.numericTypes`) shows the casts:
- $m$ is cast ℕ→ℝ wherever it multiplies reals.
- `3 - a`, `k - 1`, `2*m - (k+1)`, `2*k - 1` and `4*k - 1` are ℕ-subtractions. Each is only evaluated where it does not truncate, except `3 - a` with `a ∈ {2,3}` (exponent 1 or 0, as intended).
- `(4/5 : ℝ)`, `(1/5 : ℝ)` and `2*(m:ℝ)/(2*m+1)` are real divisions.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| D1 | `gbmLpWeight` | def | n/a | n/a | ℕ-subtractions `3-a`, `k-1` are harmless here |
| D2 | `gbmLpScale` | def | n/a | n/a | no (rpow base ≥ 1 in all uses) |
| D3 | `gbmLpIncr` | def | n/a | n/a | no |
| D4 | `gbmLpRate` | def | n/a | n/a | no |
| D5 | `gbmEMStepConst` | def | n/a | n/a | no (used only at $k\ge 2$) |
| D6 | `gbmEMMomentConst` | def | n/a | n/a | no (used with $t\ge 0$) |
| D7 | `gbmMilStepConst` | def | n/a | n/a | no |
| D8 | `gbmMilLpRate` | def | n/a | n/a | no |
| D9 | `gbmMilMomentConst` | def | n/a | n/a | no |
| 1 | `gbm_em_moment_error` | theorem | true (numerically verified exactly, margin ≥ 156) | no | no |
| 2 | `gbm_em_moment_error_le` | theorem | true | no | no |
| 3 | `gbm_em_strong_error_four` | theorem | true | no | no |
| 4 | `gbm_em_moment_error_level` | theorem | true | no | no |
| 5 | `gbm_mil_moment_error` | theorem | true (numerically verified exactly, margin ≥ 232) | no | no |
| 6 | `gbm_mil_moment_error_le` | theorem | true | no | no |
| 7 | `gbm_mil_strong_error_four` | theorem | true | no | no |
| 8 | `gbm_mil_moment_error_level` | theorem | true | no | no |
| 9 | `gbm_em_digital_variance_le_moment` | theorem | true | no (but the bound is ≥ 1, hence trivial, at shallow levels) | no |
| 10 | `gbm_mil_digital_variance_le_moment` | theorem | true | no (same remark) | no |
| 11 | `gbm_em_digital_fourth_moment_le_of_four` | theorem | true | no | no (the `0 < P` guard avoids `0/0`) |
| 12 | `gbm_mil_digital_fourth_moment_le_of_four` | theorem | true | no | no (same) |
| 13 | `gbm_em_digital_rate` | theorem | true | no | no |
| 14 | `gbm_mil_digital_rate` | theorem | true | no | no |

## Main points for a human auditor

1. **All 14 theorems are true, and none relies on a junk value.** The explicit moment constants (theorems 1 and 5) are not standard closed forms. I checked them against *exact* error moments: for GBM the moments factor over the steps, so I evaluated them in 260-digit mpmath and confirmed the formula by quadrature. The grid covered $m\le 5$, $r\in[-10,10]$, $\sigma\in[0,4]$, $h\in[10^{-6},10]$ and $n\le 10^5$, 15,594 cases per scheme. There were no violations. The smallest RHS/LHS ratio was ≈ 156 for EM. This is exactly the limit at $n=1$, $m=1$, $h\to0$, where LHS $\sim\sigma^4h^2/2$ and RHS $\sim 78\sigma^4h^2$. For Milstein the smallest ratio was ≈ 232.
2. **The constants are very loose.** In theorems 9, 10, 11 and 12 the bound on $P(D\neq0)$ is $\ge 1$, so the conjunct is trivial, until fairly deep levels. With $r=0.05$, $\sigma=0.2$, $T=1$ and $m=1$, the bound first drops below 1 at $\ell=9$ (EM) and $\ell=5$ (Milstein). With $r=1$, $\sigma=1$, $T=2$ this happens only at $\ell=39$ (EM) and $\ell=33$ (Milstein). The statements are non-trivial asymptotically, and a Monte Carlo check at those levels agrees with them.
3. **`kurtosis` is the non-centred ratio $E[X^4]/(E[X^2])^2$,** not the usual centred one $E[(X-EX)^4]/\mathrm{Var}(X)^2$. For $D\in\{-1,0,1\}$ it equals $1/P(D\neq0)$. The kurtosis lower bounds in theorems 11 to 14 are therefore just the reciprocals of the probability upper bounds. The `0 < P` hypothesis is exactly what avoids Lean's $0/0=0$.
4. **In theorems 13 and 14 the constant $C$ is uniform in $s_0$ and $K$,** including $s_0=0$. This is legitimate. The bound from theorems 9 and 10 does not depend on $s_0$ or $K$: the density factor scales as $|s_0|^{-2m/(2m+1)}$ and the moment factor as $|s_0|^{2m/(2m+1)}$, so they cancel. I confirmed this numerically. When $s_0=0$, $D\equiv0$.
5. **The rates are open-ended:** $q<1/2$ for EM and $q<1$ for Milstein. This is the standard output of the "bounded density + Markov" argument (Giles–Higham–Mao; Avikainen). It is slightly weaker than a sharp $O(h^{1/2})$ or $O(h)$ statement, but not misleading.
6. **No hypothesis is unusual.** `hh : 0 ≤ h` and `hm : 0 < m` are needed. With $m=0$ the statement reads $1\le0$. With $h<0$ and even $m$ the right-hand side can be negative while the left-hand side is positive. `hs₀ : s₀ ≠ 0`, `hσ : σ ≠ 0` and `hT : 0 < T` in theorems 9 to 12 are what make the density bound finite.

---

## 0. Definitions appended from other modules (supporting rendering)

- `kurtosis X ν` $=\big(\int X^4\,d\nu\big)/\big(\int X^2\,d\nu\big)^2$, which is non-centred. Lean's $x/0=0$ applies.
- `emPath a b h S₀ z`: $S_0$ at $i=0$, then $S_{i+1}=S_i+a(S_i,ih)h+b(S_i,ih)\sqrt h\,z_i$. This is the Euler–Maruyama recursion driven by $\Delta W_i=\sqrt h z_i$.
- `pairAvg z k` $=(z_{2k}+z_{2k+1})/\sqrt2$. This is the coarse-level Brownian increment built from two fine increments.
- `stdNormalSeq` is the product measure $\bigotimes_{i\in\mathbb N}N(0,1)$ on $\mathbb R^{\mathbb N}$ (`Measure.infinitePi`). It is a probability measure, and `pairAvg` preserves it.
- `gbmDrift r` is $(S,t)\mapsto rS$ and `gbmVol σ` is $(S,t)\mapsto\sigma S$.
- `gbmExact r σ T s₀ ℓ z` $=s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt{T/2^\ell}\sum_{i<2^\ell}z_i\big)$. This is the exact GBM solution at time $T$ on the level-$\ell$ grid. Note that `gbmExact ℓ (pairAvg z) = gbmExact (ℓ+1) z`.
- `gbmEM r σ T s₀ ℓ z` $=$ the EM path with $h=T/2^\ell$ after $2^\ell$ steps, which equals $s_0\prod_{i<2^\ell}(1+rh+\sigma\sqrt h z_i)$.
- `milsteinStep a b h S dW` $=S+a(S)h+b(S)dW+\tfrac12 b(S)b'(S)(dW^2-h)$, where `deriv` gives $b'$.
- `milsteinPath` iterates `milsteinStep` with $dW_i=\sqrt h z_i$. For $a=rS$ and $b=\sigma S$ (so $b'=\sigma$) one step multiplies by $1+rh+\sigma\sqrt h z_i+\tfrac12\sigma^2h(z_i^2-1)$.
- `gbmMil r σ T s₀ ℓ z` is the Milstein path with $h=T/2^\ell$ after $2^\ell$ steps.

## D1. `gbmLpWeight`

**Rendering.** $w_k(m,a,\beta_1,\tau,E)=2m\beta_1\tau^{3\dot-a}$ if $k=0$, and $w_k=\binom{2m}{k+1}E(k+1)\,\tau^{k-1}$ for $k\ge1$. Here $\dot-$ is ℕ-subtraction, and the module only uses $a\in\{2,3\}$, giving $\tau^1$ or $\tau^0$.

## D2. `gbmLpScale`

**Rendering.** $s_k=(1+2m\,w_k)^{1/(k+1)}$, a real rpow. In all uses $w_k\ge0$, so the base is $\ge1$.

## D3. `gbmLpIncr`

**Rendering.** $I(m,a,\beta_1,\tau,E)=\sum_{k=0}^{2m-1}w_k\,s_k^{\,2m-(k+1)}$, with natural powers and $k+1\le 2m$, so there is no truncation. It is $\ge0$ whenever $\beta_1,\tau\ge0$ and $E\ge0$.

## D4. `gbmLpRate`

**Rendering.** $\rho(m,r,\sigma)=2m|r-\sigma^2/2|+2m^2\sigma^2+|r|+2m\sigma^2$. This dominates the $2m$-th moment growth rate of both the exact solution, $2mr-m\sigma^2+2m^2\sigma^2$, and the EM solution.

## D5. `gbmEMStepConst`

**Rendering.** $E^{EM}_k(t)=2\cdot3^{k\dot-1}\big[(\sigma^2+2(|r-\sigma^2/2|+2m\sigma^2)^2t)^k+(2\sigma^2)^k(2k-1)!!\big]$. Here $(2k-1)!!=E[Z^{2k}]$, cast to ℝ. It is used only at $k\ge2$, and it is nonnegative and nondecreasing in $t\ge0$.

## D6. `gbmEMMomentConst`

**Rendering.** $C^{EM}_m(r,\sigma,t,s_0)=s_0^{2m}\,t\,I\big(m,2,(|r|+2m\sigma^2)^2,\sqrt t,E^{EM}(t)\big)\,e^{(\rho+1)t}$. For $t\ge0$ it is $\ge0$ and nondecreasing in $t$. It is $>0$ when $s_0\neq0$, $t>0$ and $\sigma\ne0$, because $w_1=\binom{2m}{2}E^{EM}_2>0$.

## D7. `gbmMilStepConst`

**Rendering.** Write $\mu=|r-\sigma^2/2|$ and $\beta=\mu+2m\sigma^2$. Then $E^{Mil}_k(t)=2\cdot3^{k\dot-1}\big[(4\beta^3t\sqrt t+(\mu^2/2+\mu\beta)\sqrt t+\mu|\sigma|/2)^k+(2|\sigma|^3+\mu|\sigma|/2)^k(2k-1)!!+(2|\sigma|^3)^k(4k-1)!!\big]$. It is nonnegative and nondecreasing in $t$.

## D8. `gbmMilLpRate`

**Rendering.** $\rho^{Mil}=4m|r-\sigma^2/2|+8m^2\sigma^2+|r|+2m\sigma^2$.

## D9. `gbmMilMomentConst`

**Rendering.** $C^{Mil}_m(r,\sigma,t,s_0)=s_0^{2m}\,t\,I\big(m,3,b^3t+b^2,\sqrt t,E^{Mil}(t)\big)\,e^{(\rho^{Mil}+1)t}$ with $b=|r|+2m\sigma^2$. Since $a=3$, $w_0=2m(b^3t+b^2)$. It is $\ge0$ and nondecreasing in $t\ge0$.

---

## 1. `gbm_em_moment_error`

**Rendering.** Let $r,\sigma,s_0\in\mathbb R$ be arbitrary, $h\ge0$ real, $n\in\mathbb N$ and $m\in\mathbb N$ with $m\ge1$. Under $z\sim\bigotimes N(0,1)$, the exact solution is $S=s_0\exp\big((r-\tfrac{\sigma^2}{2})nh+\sigma\sqrt h\sum_{i<n}z_i\big)$, the GBM value at $t=nh$ driven by $W_{nh}=\sqrt h\sum z_i$. The scheme value is $X_n=s_0\prod_{i<n}(1+rh+\sigma\sqrt hz_i)$, the EM value. The claim is
$$\int (S-X_n)^{2m}\,d\mathbb P\le C^{EM}_m(r,\sigma,nh,s_0)\,h^m .$$

**Assessment.**
- *Truth: true.* This is $L^{2m}$ strong order $1/2$ of EM for GBM with an explicit Gronwall-type constant. I did not re-derive the constant symbolically. I verified it against the exact moment: by independence, $E[(S-X_n)^{2m}]=s_0^{2m}\sum_j\binom{2m}{j}(-1)^j\big(E[e^{(2m-j)X}f(Z)^j]\big)^n$, with $E[e^{cZ}p(Z)]=e^{c^2/2}E[p(Z+c)]$. The formula matches quadrature for $n=1,2$.
- *Numerical coverage.* There were 13,824 grid cases ($m\le4$, $r\in\{-10..10\}$, $\sigma\in\{0..4\}$, $h\in\{10^{-6}..10\}$, $n\le1000$) and 1,770 random or large-$n$ cases ($n$ up to $10^5$, $m\le5$). There were no violations, and the minimum ratio was ≈ 156 (`moment_check.out`, `moment_check2.out`).
- *Asymptotic regimes.* The ratio of 156 is the exact $n=1$, $m=1$, $h\to0$ limit: $\sigma^4h^2/2$ against $78\sigma^4h^2$. For large $t$ the factor $e^{(\rho+1)t}$ dominates both the exact rate $2mr-m\sigma^2+2m^2\sigma^2$ and the EM rate. The edge cases $h=0$ and $n=0$ give $0\le0$.
- *Vacuity:* not vacuous. Example: $r=0.05$, $\sigma=0.2$, $s_0=1$, $h=0.01$, $n=100$, $m=1$.
- *Junk:* none. The integrand is integrable (polynomial in Gaussians times exponentials of Gaussians, finitely many coordinates), $\sqrt h$ uses $h\ge0$, and the RHS is $\ge0$.
- *Hypotheses:* `hm` is needed ($m=0$ reads $1\le0$). `hh` is needed: for $h<0$ and even $m$ the RHS can be negative.
- *Standard fact:* EM strong convergence of order 1/2 in every $L^p$ (Kloeden–Platen Thm 10.2.2, specialised to GBM with explicit constants).

## 2. `gbm_em_moment_error_le`

**Rendering.** The setting of theorem 1 plus a real $T$ with $nh\le T$. The claim is $E[(S-X_n)^{2m}]\le C^{EM}_m(r,\sigma,T,s_0)\,h^m$.

**Assessment.**
- *Truth: true.* It follows from theorem 1 because $t\mapsto C^{EM}_m(t)$ is nondecreasing on $t\ge0$: $\sqrt t$, $E^{EM}_k(t)$, the weights, the scales, $t$ and $e^{(\rho+1)t}$ are all nonnegative and nondecreasing.
- *Vacuity and junk:* not vacuous ($T=1$ in the example above), and no junk values.
- *Standard fact:* a uniform-in-time version of the strong error bound.

## 3. `gbm_em_strong_error_four`

**Rendering.** For $h\ge0$, $n$ and $nh\le T$: $E[(S-X_n)^4]\le C^{EM}_2(r,\sigma,T,s_0)\,h^2$.

**Assessment.**
- *Truth: true.* It is theorem 2 with $m=2$.
- *Vacuity and junk:* not vacuous, no junk.
- *Standard fact:* the $L^4$ strong error of EM is $O(h^{1/2})$.

## 4. `gbm_em_moment_error_level`

**Rendering.** For $T\ge0$, $\ell\in\mathbb N$ and $m\ge1$: $E[(\texttt{gbmExact}_\ell-\texttt{gbmEM}_\ell)^{2m}]\le C^{EM}_m(r,\sigma,T,s_0)(T/2^\ell)^m$. Both quantities are on the grid with $2^\ell$ steps of size $T/2^\ell$ and are driven by the same $z$.

**Assessment.**
- *Truth: true.* It is theorem 1 with $h=T/2^\ell\ge0$ and $n=2^\ell$, since $nh=T$ exactly in ℝ.
- *Vacuity and junk:* not vacuous ($T=1$, $\ell=3$, $m=1$), no junk.
- *Standard fact:* the level-$\ell$ form of the EM strong error used in MLMC variance analysis.

## 5. `gbm_mil_moment_error`

**Rendering.** As in theorem 1, but the scheme is Milstein: $Y_n=s_0\prod_{i<n}\big(1+rh+\sigma\sqrt hz_i+\tfrac12\sigma^2h(z_i^2-1)\big)$. Here `deriv (fun S => σ*S) = σ`. The claim is $E[(S-Y_n)^{2m}]\le C^{Mil}_m(r,\sigma,nh,s_0)\,h^{2m}$.

**Assessment.**
- *Truth: true.* This is $L^{2m}$ strong order 1 of Milstein.
- *Numerical check.* The same exact-moment method as in theorem 1 (matches quadrature) found no violations in 15,594 cases. The minimum ratio was ≈ 232.6 on the grid and ≈ 267.7 in the random cases. In the $n=1$, $h\to0$ regime the true error is $O(h^{3m})$ against the bound's $O(h^{2m+1})$.
- *Vacuity and junk:* not vacuous (same parameters as theorem 1), no junk (integrable, RHS $\ge0$).
- *Hypotheses:* `hm` is necessary.
- *Standard fact:* Milstein strong order 1 (Kloeden–Platen Thm 10.3.5) for GBM.

## 6. `gbm_mil_moment_error_le`

**Rendering.** As in theorem 5 with $nh\le T$. The claim is $E[(S-Y_n)^{2m}]\le C^{Mil}_m(r,\sigma,T,s_0)h^{2m}$.

**Assessment.**
- *Truth: true,* by the monotonicity of $C^{Mil}_m$ in $t\ge0$ (every ingredient is nondecreasing).
- *Vacuity and junk:* not vacuous, no junk.

## 7. `gbm_mil_strong_error_four`

**Rendering.** $E[(S-Y_n)^4]\le C^{Mil}_2(r,\sigma,T,s_0)h^4$ for $h\ge0$ and $nh\le T$.

**Assessment.**
- *Truth: true.* It is theorem 6 with $m=2$.
- *Vacuity and junk:* not vacuous, no junk.
- *Standard fact:* the $L^4$ strong error of Milstein is $O(h)$.

## 8. `gbm_mil_moment_error_level`

**Rendering.** For $T\ge0$ and $m\ge1$: $E[(\texttt{gbmExact}_\ell-\texttt{gbmMil}_\ell)^{2m}]\le C^{Mil}_m(r,\sigma,T,s_0)(T/2^\ell)^{2m}$.

**Assessment.**
- *Truth: true.* It is theorem 5 with $h=T/2^\ell$ and $n=2^\ell$.
- *Vacuity and junk:* not vacuous, no junk.

## 9. `gbm_em_digital_variance_le_moment`

**Rendering.** Assume $s_0\neq0$, $\sigma\neq0$, $T>0$, $K\in\mathbb R$, $m\ge1$ and $\ell\in\mathbb N$. Define:
- the fine-minus-coarse digital payoff $D=\mathbf 1\{X^f>K\}-\mathbf 1\{X^c>K\}$, where $X^f=\texttt{gbmEM}_{\ell+1}(z)$ and $X^c=\texttt{gbmEM}_\ell(\texttt{pairAvg}\,z)$;
- $p=P(\mathbf 1\{X^f>K\}\ne\mathbf 1\{X^c>K\})$, the measure of the set as a real number;
- $M=e^{(\sigma^2-r)T}/(\sqrt{2\pi}|s_0||\sigma|\sqrt T)$.

The claim is a conjunction:
(a) $\mathrm{Var}(D)\le p$, and
(b) $p\le 2(2M)^{2m/(2m+1)}\,(C^{EM}_m(r,\sigma,T,s_0))^{1/(2m+1)}\big((T/2^{\ell+1})^{m/(2m+1)}+(T/2^\ell)^{m/(2m+1)}\big)$, with real rpow exponents.

**Assessment.**
- *Truth: true.*
- *Part (a).* $D\in\{-1,0,1\}$, so $\mathrm{Var}(D)\le E[D^2]=p$. Mathlib's `variance` is `(evariance).toReal`, which is finite here because $D$ is bounded and measurable.
- *Part (b), coupling.* Let $S=\texttt{gbmExact}_{\ell+1}(z)=\texttt{gbmExact}_\ell(\texttt{pairAvg}\,z)$, which is the same exact solution for both levels. Since `pairAvg` preserves `stdNormalSeq`, theorem 4 applies to both levels.
- *Part (b), splitting the event.* If the indicators of $X$ and $S$ differ, then $|S-K|\le|X-S|$. So $P(\cdot)\le P(|S-K|<\delta)+P(|X-S|\ge\delta)$.
- *Part (b), density bound.* $S$ is (± a) lognormal with maximal density exactly $M$: the mode is at $\ln|x/s_0|=(r-\tfrac32\sigma^2)T$, which gives $e^{(\sigma^2-r)T}/(\sqrt{2\pi}|s_0||\sigma|\sqrt T)$. So $P(|S-K|<\delta)\le2M\delta$.
- *Part (b), Markov and optimisation.* Markov gives $P(|X-S|\ge\delta)\le C h^m/\delta^{2m}$. Choosing $\delta=(Ch^m/2M)^{1/(2m+1)}$ gives $2(2M)^{2m/(2m+1)}C^{1/(2m+1)}h^{m/(2m+1)}$ per level. Adding the two levels gives the stated formula exactly.
- *Monte Carlo.* At $r=0.05$, $\sigma=0.2$, $T=1$, $\ell=9$, $m=1$: $p\approx0.002$ against a bound of 0.959 (`digital_mc.out`).
- *Vacuity:* not vacuous. However, the bound is $\ge1$ (so (b) is trivial) for small $\ell$. It first falls below 1 at $\ell=9$ for $(r,\sigma,T)=(0.05,0.2,1)$ and $m=1$, and only at $\ell=39$ for $(1,1,2)$ (`digital_bound.out`).
- *Junk:* none. Every rpow base is $>0$ ($M>0$, $C^{EM}_m>0$, $T/2^\ell>0$), and the denominator is $>0$ by the hypotheses.
- *Hypotheses:* the three nondegeneracy hypotheses are natural and needed for $M<\infty$.
- *Standard fact:* the Giles–Higham–Mao (2009) and Avikainen (2009) argument, "bounded density + Markov", for digital payoffs in MLMC.

## 10. `gbm_mil_digital_variance_le_moment`

**Rendering.** The same as theorem 9 with Milstein paths ($X^f=\texttt{gbmMil}_{\ell+1}(z)$, $X^c=\texttt{gbmMil}_\ell(\texttt{pairAvg}\,z)$) and the constant $C^{Mil}_m$. The step exponent is $2m/(2m+1)$. The claim is (a) $\mathrm{Var}(D)\le p$ and (b) $p\le2(2M)^{2m/(2m+1)}(C^{Mil}_m)^{1/(2m+1)}\big((T/2^{\ell+1})^{2m/(2m+1)}+(T/2^\ell)^{2m/(2m+1)}\big)$.

**Assessment.**
- *Truth: true.* It is the same argument with the $h^{2m}$ moment bound from theorem 8: $(Ch^{2m})^{1/(2m+1)}=C^{1/(2m+1)}h^{2m/(2m+1)}$.
- *Monte Carlo.* At $\ell=5$ and $\ell=6$: $p\approx10^{-4}$ against bounds of 0.81 and 0.51.
- *Vacuity:* not vacuous. The bound is below 1 from $\ell=5$ for $(0.05,0.2,1)$ with $m=1$, and only from $\ell=33$ for $(1,1,2)$.
- *Junk:* none.
- *Standard fact:* Milstein digital MLMC variance of order $O(h^{1-\delta})$ (Giles 2008, Milstein MLMC).

## 11. `gbm_em_digital_fourth_moment_le_of_four`

**Rendering.** With $D$, $p$ and $M$ as in theorem 9 (EM), under $s_0\ne0$, $\sigma\ne0$, $T>0$ and any $K$, $\ell$, the claim is the conjunction:
(i) $\mathrm{Var}(D)\le p$;
(ii) $E[D^4]=p$;
(iii) $p\le B:=2(2M)^{4/5}(C^{EM}_2)^{1/5}\big((T/2^{\ell+1})^{2/5}+(T/2^\ell)^{2/5}\big)$;
(iv) if $p>0$ then $B^{-1}\le\texttt{kurtosis}(D)=E[D^4]/(E[D^2])^2$.

**Assessment.**
- *Truth: true.* (i) and (iii) are theorem 9 with $m=2$. (ii) holds because $D^4=\mathbf 1\{D\ne0\}$. (iv) holds because $E[D^2]=E[D^4]=p$, so the kurtosis is $1/p\ge1/B$, using $B\ge p>0$.
- *Vacuity:* not vacuous ($r=0.05$, $\sigma=0.2$, $s_0=1$, $T=1$, $K=1$, $\ell=12$).
- *Junk:* none. The guard $p>0$ prevents `kurtosis` $=0/0=0$, and $B^{-1}$ is taken with $B>0$.
- *Note:* `kurtosis` is non-centred, so (iv) is a restatement of (iii).
- *Standard fact:* the kurtosis of the digital MLMC correction blows up as $h\to0$ (Giles, Acta Numerica 2015).

## 12. `gbm_mil_digital_fourth_moment_le_of_four`

**Rendering.** The Milstein analogue of theorem 11: (i) $\mathrm{Var}(D)\le p$; (ii) $E[D^4]=p$; (iii) $p\le B:=2(2M)^{4/5}(C^{Mil}_2)^{1/5}\big((T/2^{\ell+1})^{4/5}+(T/2^\ell)^{4/5}\big)$; (iv) if $p>0$ then $B^{-1}\le\texttt{kurtosis}(D)$.

**Assessment.**
- *Truth: true.* (iii) is theorem 10 with $m=2$; (i), (ii) and (iv) follow as in theorem 11.
- *Vacuity and junk:* not vacuous, no junk.

## 13. `gbm_em_digital_rate`

**Rendering.** For all $r$, $\sigma\ne0$, $T>0$ and $q<1/2$ there is a $C\ge0$, depending only on $(r,\sigma,T,q)$, such that for all real $s_0$, real $K$ and $\ell\in\mathbb N$, with $h_f=T/2^{\ell+1}$ and the EM digital correction $D$ and $p$ as in theorem 9:
- $\mathrm{Var}(D)\le Ch_f^q$;
- $p\le Ch_f^q$;
- $E[D^4]\le Ch_f^q$;
- if $p>0$ then $(Ch_f^q)^{-1}\le\texttt{kurtosis}(D)$.

**Assessment.**
- *Truth: true.*
- *Case $s_0=0$.* Then $D\equiv0$ and everything is trivial.
- *Case $s_0\ne0$.* Pick $m$ with $\pi:=m/(2m+1)\ge q$, which is possible because $m/(2m+1)\uparrow1/2$. The bound of theorem 9 does not depend on $s_0$ (the $|s_0|$ powers cancel) or on $K$. Then $h_f^\pi+h_c^\pi=(1+2^\pi)h_f^\pi\le(1+2^\pi)(T/2)^{\pi-q}h_f^q$. The fourth-moment and kurtosis parts follow as in theorem 11.
- *Vacuity:* not vacuous ($r=0.05$, $\sigma=0.2$, $T=1$, $q=0.4$).
- *Junk:* none, since $h_f>0$.
- *Hypotheses:* nothing unusual. The range $q<1/2$ (any $q$, including $q\le0$) is the standard "$O(h^{1/2-\delta})$" result. It is slightly weaker than a sharp $h^{1/2}$ statement.
- *Standard fact:* EM digital MLMC variance $V_\ell=O(h_\ell^{1/2-\delta})$ (Giles–Higham–Mao 2009; Avikainen 2009). The kurtosis grows like $h^{-q}$.

## 14. `gbm_mil_digital_rate`

**Rendering.** The same as theorem 13 with Milstein paths and $q<1$: there is a $C\ge0$, depending on $(r,\sigma,T,q)$ and uniform in $s_0$, $K$ and $\ell$, such that $\mathrm{Var}(D)$, $p$ and $E[D^4]$ are all $\le Ch_f^q$, and $p>0$ implies $(Ch_f^q)^{-1}\le\texttt{kurtosis}(D)$.

**Assessment.**
- *Truth: true.* Choose $m$ with $2m/(2m+1)\ge q$ in theorem 10. The rest is as in theorem 13.
- *Vacuity and junk:* not vacuous ($q=0.9$), no junk.
- *Standard fact:* Milstein digital MLMC variance $O(h^{1-\delta})$ (Giles 2008).
