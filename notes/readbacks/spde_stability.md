# Blind read-back report: R15 (SPDE finite-difference stability)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round17/packet_R15_spdestab.lean` |
| declarations audited | 23 (17 theorems + 6 definitions: `spdeStep`, `spdePath`, `fourierMode`, `spdeAmp`, `stdNormalSeq`, `heatStep`) |
| auditor | independent blind auditor (sub-agent) |
| scripts | `readback/round17/work_R15/` (`s01`–`s08` `.py` + `.out`, helper `polyexp.py`, Lean elaboration check `scratch_packet.lean` + `.out`) |

Lean elaboration: a self-contained copy of the packet (own namespace, Mathlib imports only, proofs `sorry`) elaborates without errors; the `#check` output confirms the casts: `n * k` means $(n:\mathbb R)\,k$, `4 ^ ℓ` and `2 ^ ℓ` are real powers with $\ell\in\mathbb N$, `⌊T / k⌋₊` is `Nat.floor`, the index $j$ in `range N` is cast ℕ→ℤ, and $m, N$ in $2\pi m/N$ are cast to ℝ (`scratch_packet.out`).

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `spdeStep_eq_milstein` | theorem | true | no | no |
| 2 | `spdeStep_fourierMode` | theorem | true | no | no (the $h=0$ instance is a junk identity, but the theorem also holds for $h\neq0$) |
| 3 | `spdePath_fourierMode` | theorem | true | no | no |
| 4 | `integral_normSq_spdeAmp` | theorem | true | no | no |
| 5 | `integral_normSq_spdeAmp_le` | theorem | true | no | no |
| 6 | `integral_normSq_spdePath` | theorem | true | no | no |
| 7 | `spde_meanSquare_stable` | theorem | true | no | no |
| 8 | `integral_normSq_spdeAmp_pi` | theorem | true | no | no |
| 9 | `spde_meanSquare_unstable` | theorem | true | no | no |
| 10 | `spde_level_refinement` | theorem | true | no | no |
| 11 | `spde_level_refinement_stable` | theorem | true | no | no |
| 12 | `spde_level_cost` | theorem | true | no | no (it also holds in the junk cases $h=0$ or $k=0$) |
| 13 | `spde_levels_stable` | theorem | true | no | no |
| 14 | `integral_sum_normSq_spdePath_periodic` | theorem | true | no | no |
| 15 | `spde_meanSquare_stable_periodic` | theorem | true | no | no |
| 16 | `spdeStep_heat` | theorem | true | no | no |
| 17 | `norm_spdeStep_heat_le` | theorem | true | no | no |

## Main points for a human auditor

- **All 17 theorems are true and none is vacuous.** Every closed-form Gaussian expectation was confirmed three ways: with moments in sympy, by symbolic Gaussian integration in sympy, and by mpmath quadrature (relative error below $10^{-24}$). The path-level and periodic statements were checked exactly. The Lean recursion was run on symbolic $Z_0,\dots,Z_{n-1}$ and the expectation was taken with exact iid-$N(0,1)$ moments, for $n\le3$, $N=1,\dots,7$ and parameters of all signs, including the Lean junk values (errors of about $10^{-40}$).
- **The stability condition is exactly sharp.** For $0\le\rho\le1$ and $k\ge0$, write $\lambda=k/h^2$. If $\lambda(1+2\rho^2)\le1$, then $\mathbb E|A_\theta|^2\le 1+\mu^2\lambda k$ for every $\theta$ (#5, #7). The certificate is $1+\mu^2\lambda k-\mathbb E|A|^2=4\lambda s^2[(1-\rho)(1-s^2)+s^2(1-\lambda(1+2\rho^2))]+\mu^2\lambda k\cos^2\theta$, with $s=\sin(\theta/2)$. If instead $\lambda(1+2\rho^2)>1$, then $\mathbb E|A_\pi|^2=1+4\lambda(\lambda(1+2\rho^2)-1)>1$, and the mean square blows up as $k\downarrow0$ with $\lambda$ fixed (#8, #9; #9 assumes nothing on $\rho$ or $\mu$). At equality the growth factor is exactly 1. The two theorems are exact complements.
- **The hypotheses $0\le\rho\le1$ and $k\ge0$ in #5, #7, #13, #15 are genuinely needed, not decorative.** With $\rho=1.5$ and $\lambda=0.1$ (so $\lambda(1+2\rho^2)=0.55\le1$), $\mu=0$ and $\theta=0.3$: $\mathbb E|A|^2=1.00428>1$. With $k=-0.2$, $h=1$ and $\theta=\pi$: $\mathbb E|A|^2=2.04>1$.
- **How independence is modelled.** `stdNormalSeq` is `Measure.infinitePi` of $N(0,1)$, the law of an iid standard normal sequence; Mathlib's `iIndepFun_iff_map_fun_eq_infinitePi_map` characterises iid sequences this way. Step $n$ uses coordinate $Z_n$, and the same $Z_n$ is used at every grid point $j$: a common (market) noise per time step, as intended.
- **Degenerate cases $h=0$ and $k=0$.** Because `x/0 = 0`, `spdeStep` becomes the identity, $A\equiv1$ and $\lambda=0$. All theorems remain true there; in the stability theorems $h=0$ satisfies the condition $\lambda(1+2\rho^2)\le1$ trivially and gives the trivial bound $1\le1$. No theorem relies on this to be true: the meaningful range $h\neq0$ is fully covered. In #9, `hmesh` with $\lambda\neq0$ forces $\mathrm{mesh}(k)\neq0$, so no junk mesh is possible there.
- **The periodic Parseval statement (#14) is correct for every $N$, including $N=1$ and $N=2$, and for all parameter values.** The hypothesis $0<N$ (in #14 and #15) is actually superfluous, since both sides are $0$ when $N=0$. Harmless.
- **Minor: #1 and #4 assume $\rho\ge0$ and $k\ge0$.** #4 only needs $\rho k\ge0$ (it also holds for $\rho<0$, $k<0$); #1 does need both, because of `Real.sqrt` of negatives. Both choices are natural.

---

## Definitions

### `spdeStep mu rho k h z p j`
**Rendering.** For $p:\mathbb Z\to\mathbb C$,
$$(Sp)_j=p_j-\frac{\mu k+\sqrt{\rho k}\,z}{2h}(p_{j+1}-p_{j-1})+\frac{(1-\rho)k+\rho k z^2}{2h^2}(p_{j+1}-2p_j+p_{j-1}).$$
The real coefficients are cast to ℂ. `Real.sqrt` returns $0$ on negative arguments, and $x/0=0$ (so $h=0$ makes $S$ the identity). This is the Giles–Reisinger Milstein finite-difference scheme for $dv=-\mu v_x\,dt+\tfrac12 v_{xx}\,dt-\sqrt\rho\,v_x\,dM_t$ with $\Delta M=\sqrt k\,z$, centred first difference and standard second difference.

### `spdePath mu rho k h p₀ Z n`
**Rendering.** $v^0=p_0$ and $v^{n+1}=S_{Z_n}v^n$: the step from time $n$ to $n+1$ uses coordinate $Z_n$ of $Z:\mathbb N\to\mathbb R$, the same at every $j$.

### `fourierMode θ j`
**Rendering.** $e_\theta(j)=\exp(i\,j\theta)$ with $j\in\mathbb Z$ cast to ℝ.

### `spdeAmp mu rho k h θ z`
**Rendering.**
$$A_\theta(z)=1-2\frac{k}{h^2}\sin^2(\theta/2)\big((1-\rho)+\rho z^2\big)-i\,\frac{(\mu k+\sqrt{\rho k}\,z)\sin\theta}{h}.$$
This is the Fourier symbol (amplification factor) of the scheme.

### `stdNormalSeq`
**Rendering.** $\bigotimes_{n\in\mathbb N}N(0,1)$ on $\mathbb R^{\mathbb N}$ (`Measure.infinitePi`; `gaussianReal 0 1` is a probability measure, so this is the genuine product measure, not the `0` fallback). The coordinates are iid $N(0,1)$.

### `heatStep lam u j`
**Rendering.** $u_j+\lambda(u_{j+1}-2u_j+u_{j-1})$ for real $u$: the explicit Euler step for the heat equation.

---

## 1. `spdeStep_eq_milstein`
**Rendering.** For $\rho\ge0$, $k\ge0$ and all $\mu,h,z,p,j$:
$$(S p)_j=p_j-\frac{\mu k+\sqrt\rho(\sqrt k z)}{2h}(p_{j+1}-p_{j-1})+\frac{k+\rho((\sqrt k z)^2-k)}{2h^2}(p_{j+1}-2p_j+p_{j-1}).$$

**Assessment.**
- **Truth:** true. $\sqrt{\rho k}=\sqrt\rho\sqrt k$ needs $\rho\ge0$ (`Real.sqrt_mul`), and $(\sqrt k z)^2=kz^2$ needs $k\ge0$; then $k+\rho(kz^2-k)=(1-\rho)k+\rho kz^2$. Sympy residual 0 (`s01`).
- **Hypotheses:** both are needed. With $\rho=k=-1$, $\sqrt{\rho k}=1$ but $\sqrt\rho\sqrt k=0$; with $k=-1$, $\rho=\tfrac12$, $z=1$ the second coefficients differ ($-1$ vs $-0.5$).
- **Vacuity:** not vacuous ($\rho=\tfrac12$, $k=0.1$).
- **Junk values:** none.
- **Standard fact:** the scheme is the Milstein time-stepping with $\Delta W=\sqrt k z$ and Milstein correction $\tfrac\rho2 v_{xx}((\Delta W)^2-k)$.

## 2. `spdeStep_fourierMode`
**Rendering.** For all real $\mu,\rho,k,h,z,\theta$ and $j\in\mathbb Z$: $(S e_\theta)_j=A_\theta(z)\,e_\theta(j)$.

**Assessment.**
- **Truth:** true. $e_\theta(j+1)-e_\theta(j-1)=2i\sin\theta\,e_\theta(j)$ and $e_\theta(j+1)-2e_\theta(j)+e_\theta(j-1)=-4\sin^2(\theta/2)\,e_\theta(j)$. Sympy residual 0 for an arbitrary value of the square root, and a 60-digit residual of about $10^{-187}$ at 200 random rational points (`s01`). Since `Real.sqrt(rho*k)` appears identically on both sides, the identity holds for all signs.
- **Junk values:** for $h=0$ both sides reduce to $p_j=1\cdot p_j$ (Lean `x/0=0`), which is junk but consistent; the theorem is not true *only* because of it.
- **Vacuity:** no hypotheses, so not vacuous.
- **Standard fact:** von Neumann (Fourier) analysis of a constant-coefficient linear scheme.

## 3. `spdePath_fourierMode`
**Rendering.** For all parameters, $Z$, $n$, $j$: $v^n_j=\big(\prod_{m<n}A_\theta(Z_m)\big)e_\theta(j)$ when $v^0=e_\theta$.

**Assessment.**
- **Truth:** true, by induction using #2 and the linearity of $S$ in $p$. Checked pathwise at random $Z$ for $n\le3$ (error $2\cdot10^{-32}$, `s04`).
- **Vacuity:** no hypotheses.
- **Junk values:** none.
- **Standard fact:** a Fourier mode stays a Fourier mode, multiplied by the product of the random symbols.

## 4. `integral_normSq_spdeAmp`
**Rendering.** For $\rho\ge0$, $k\ge0$, with $\lambda=k/h^2$ and $s=\sin(\theta/2)$, and $z\sim N(0,1)$:
$$\mathbb E|A_\theta(z)|^2=1-4\lambda s^2\big[(1-\rho)+\rho s^2-\lambda s^2(1+2\rho^2)\big]+4\lambda\mu^2 k\,s^2(1-s^2).$$

**Assessment.**
- **Truth:** true. Write $a=2\lambda s^2$. The real part gives $\mathbb E(1-a(1-\rho+\rho z^2))^2=1-2a+a^2(1+2\rho^2)$ (using $\mathbb Ez^2=1$, $\mathbb Ez^4=3$). The imaginary part gives $\sin^2\theta\,(\mu^2k^2+\rho k)/h^2$ with $\sin^2\theta=4s^2(1-s^2)$.
- **Checks:** sympy moments equal sympy's symbolic Gaussian integral; difference from the claimed form is 0 once $\sqrt{\rho k}^2=\rho k$; mpmath quadrature agrees to $10^{-25}$ at 60 random points, and also in the degenerate cases $h=0$, $k=0$ and $\rho=0$ (`s02`).
- **Hypotheses:** only $\rho k\ge0$ is used. The identity also holds for $\rho<0$, $k<0$ (quadrature 1.44178 = closed form), and fails when $\rho k<0$ (for example 1.3043 vs 1.1981), so $\rho\ge0$, $k\ge0$ is slightly stronger than needed but natural.
- **Integrability:** the integrand is a degree-4 polynomial in $z$, so it is integrable and the Bochner integral is genuine (no junk 0).
- **Vacuity:** not vacuous ($\rho=0.5$, $k=0.1$).
- **Standard fact:** the mean-square amplification factor (Giles–Reisinger Fourier analysis).

## 5. `integral_normSq_spdeAmp_le`
**Rendering.** For $0\le\rho\le1$, $k\ge0$ and $\lambda(1+2\rho^2)\le1$ (with $\lambda=k/h^2$), for every $\theta$: $\mathbb E|A_\theta(z)|^2\le1+\mu^2\lambda k$.

**Assessment.**
- **Truth:** true. Sympy-verified certificate: $1+\mu^2\lambda k-\mathbb E|A|^2=4\lambda s^2[(1-\rho)(1-s^2)+s^2(1-\lambda(1+2\rho^2))]+\mu^2\lambda k(1-\sin^2\theta)$, and each term is $\ge0$ under the hypotheses ($\lambda\ge0$ because $k\ge0$). Over 20000 admissible samples the maximum of $\mathbb E|A|^2-$bound was $<0$ (`s03`).
- **Sharpness:** at $\mu=0$, $\sup_\theta\mathbb E|A|^2=1$ exactly at $\lambda(1+2\rho^2)\le1$, and it exceeds 1 at $1.001\times$ the critical $\lambda$, for $\rho\in\{0,0.3,0.7,1\}$.
- **Hypotheses:** $\rho\le1$ and $k\ge0$ are needed (counterexamples in Main points).
- **Vacuity:** not vacuous ($\rho=0.5$, $k=0.01$, $h=0.2$, so $\lambda=0.25$).
- **Junk values:** $h=0$ is admitted (giving $\lambda=0$, $A=1$, $1\le1$) but not needed.
- **Standard fact:** the Giles–Reisinger mean-square stability condition $k/h^2\le1/(1+2\rho^2)$.

## 6. `integral_normSq_spdePath`
**Rendering.** For all parameters, $\theta$, $n$, $j$:
$$\mathbb E_{Z\sim\otimes N(0,1)}|v^n_j|^2=\big(\mathbb E_{z\sim N(0,1)}|A_\theta(z)|^2\big)^n,\qquad v^0=e_\theta.$$

**Assessment.**
- **Truth:** true. $|v^n_j|^2=\prod_{m<n}|A_\theta(Z_m)|^2$ since $|e_\theta(j)|=1$, and under the product measure the coordinates are independent with law $N(0,1)$, so the expectation factorises. The integrand is a polynomial in finitely many coordinates, hence integrable.
- **Checks:** exact iid-moment expectation of the Lean recursion matches $(\text{quadrature})^n$ to $10^{-40}$ for 15 parameter sets of all signs (including $h=0$, $k=0$, $\theta=\pi$), $n\le3$ (`s04`).
- **Vacuity:** no hypotheses.
- **Junk values:** none.
- **Standard fact:** multiplicativity of second moments of products of independent factors.

## 7. `spde_meanSquare_stable`
**Rendering.** Under $0\le\rho\le1$, $k\ge0$, $\lambda(1+2\rho^2)\le1$, for every $\theta$, every $n\in\mathbb N$ with $nk\le T$, and every $j$:
$$\mathbb E|v^n_j|^2\le(1+\mu^2\lambda k)^n\le e^{\mu^2\lambda T}\qquad(v^0=e_\theta).$$

**Assessment.**
- **Truth:** true, by #6, #5 and $\mathbb E|A|^2\ge0$ (pow monotone), then $1+x\le e^x$ together with $\mu^2\lambda\ge0$ and $nk\le T$. Numeric maximum of the second gap was $-5\cdot10^{-8}$ (`s03`).
- **Degenerate cases:** $k=0$ gives $1\le1\le1$; $h=0$ gives the same.
- **Vacuity:** not vacuous ($\rho=0.5$, $k=0.01$, $h=0.2$, $n=10$, $T=0.1$).
- **Junk values:** none needed.
- **Standard fact:** mean-square stability, i.e. a bound uniform in the refinement at fixed $\lambda$ and $T$; the $e^{\mu^2\lambda T}$ factor comes from the drift's centred difference.

## 8. `integral_normSq_spdeAmp_pi`
**Rendering.** For all real $\mu,\rho,k,h$: $\mathbb E|A_\pi(z)|^2=1+4\lambda(\lambda(1+2\rho^2)-1)$.

**Assessment.**
- **Truth:** true with no sign hypotheses. `Real.sin π = 0` exactly, so the $\sqrt{\rho k}$ term vanishes, and $\mathbb E(1-\rho+\rho z^2)^2=1+2\rho^2$ for every real $\rho$. Sympy residual 0; quadrature to $2\cdot10^{-28}$ over 40 random parameter sets of all signs (`s02`).
- **Vacuity:** no hypotheses.
- **Junk values:** none.
- **Standard fact:** the growth factor of the sawtooth (highest-frequency) mode.

## 9. `spde_meanSquare_unstable`
**Rendering.** Let $\lambda(1+2\rho^2)>1$, $T>0$, and let $\mathrm{mesh}:\mathbb R\to\mathbb R$ satisfy $k/\mathrm{mesh}(k)^2=\lambda$ for every $k>0$. Then for every $j$ (and every $\mu$), as $k\to0^+$,
$$\mathbb E|v^{\lfloor T/k\rfloor}_j|^2\to+\infty,$$
where $v^0=e_\pi=((-1)^j)$, mesh width $h=\mathrm{mesh}(k)$ and time step $k$.

**Assessment.**
- **Truth:** true. By #6 and #8 the expectation is $G^{\lfloor T/k\rfloor}$ with $G=1+4\lambda(\lambda c-1)$ and $c=1+2\rho^2>0$. From $\lambda c>1$ we get $\lambda>0$, so $G>1$, and $\lfloor T/k\rfloor\to\infty$. Exact recursion check: $\mathbb E|v^4_0|^2=G^4=2.2387$ for $\mu=0$ and $\mu=3$ (`s06`).
- **Vacuity:** not vacuous ($\lambda=1$, $\rho=0.5$, $T=1$, $\mathrm{mesh}(k)=\sqrt{k/\lambda}$).
- **Junk values:** `hmesh` forces $\mathrm{mesh}(k)\neq0$ for $k>0$, because otherwise $k/0=0\neq\lambda$, so the theorem never uses $h=0$. Its truth needs genuine integrability (a junk integral of 0 would make it false), which holds.
- **Sharpness:** at $\lambda c=1$ we get $G=1$ exactly, so with #7 this is an exact dichotomy.
- **Scope:** no restriction on $\rho$ or $\mu$. The family has fixed ratio $k/h^2$, and only the $\theta=\pi$ mode is exhibited, which is the standard formulation.
- **Standard fact:** the necessity half of the von Neumann mean-square stability condition.

## 10. `spde_level_refinement`
**Rendering.** If $h_0\neq0$, $h_1=h_0/2$ and $k_0/h_0^2=\lambda$, then $(k_1/h_1^2\le\lambda\iff k_1\le k_0/4)$ and $(k_1/h_1^2=\lambda\iff k_1=k_0/4)$, for every real $k_1$.

**Assessment.**
- **Truth:** true, since $k_1/h_1^2=4k_1/h_0^2$ and $h_0^2>0$. 20000 random rational checks, 0 failures (`s08`).
- **Hypotheses:** `hh` is necessary. With $h_0=0$ we get $\lambda=0$ and $k_1/h_1^2=0\le0$, yet $k_1\le k_0/4$ can fail.
- **Vacuity:** not vacuous.
- **Junk values:** none.
- **Standard fact:** halving $h$ at fixed $\lambda$ requires quartering $k$ (parabolic scaling in the MLMC hierarchy).

## 11. `spde_level_refinement_stable`
**Rendering.** If $h_1=h_0/2$ and $\frac{k_0}{h_0^2}(1+2\rho^2)=1$, then $\frac{k_1}{h_1^2}(1+2\rho^2)\le1\iff k_1\le k_0/4$.

**Assessment.**
- **Truth:** true. `hmax` forces $h_0\neq0$ (otherwise it reads $0=1$), and $c=1+2\rho^2>0$; then this is the same algebra as #10. Random rational checks: 0 failures.
- **Vacuity:** not vacuous ($\rho=0$, $h_0=k_0=1$).
- **Junk values:** none.
- **Standard fact:** stable time-step refinement at the critical ratio.

## 12. `spde_level_cost`
**Rendering.** For all real $X,T,h,k$: $\frac{X}{h/2}\cdot\frac{T}{k/4}=8\cdot\frac Xh\cdot\frac Tk$.

**Assessment.**
- **Truth:** true identically, including with Lean `x/0=0` (both sides $0$ when $h=0$ or $k=0$). Exhaustive grid including zeros: 0 failures (`s08`).
- **Vacuity:** no hypotheses.
- **Junk values:** none.
- **Standard fact:** cost (grid points × time steps) grows by a factor of 8 per MLMC level.

## 13. `spde_levels_stable`
**Rendering.** Under $0\le\rho\le1$, $k_0\ge0$ and $\frac{k_0}{h_0^2}(1+2\rho^2)\le1$, for every $\theta$, level $\ell\in\mathbb N$, $n$ with $n\,k_0/4^\ell\le T$, and every $j$: with $k=k_0/4^\ell$ and $h=h_0/2^\ell$,
$$\mathbb E|v^n_j|^2\le e^{\mu^2(k_0/h_0^2)T}.$$

**Assessment.**
- **Truth:** true. $(k_0/4^\ell)/(h_0/2^\ell)^2=k_0/h_0^2$ exactly, including the case $h_0=0$ (0 failures, `s08`); then apply #7.
- **Vacuity:** not vacuous ($\rho=0.5$, $k_0=0.01$, $h_0=0.2$, $\ell=2$, $n=16$, $T=0.01$).
- **Junk values:** none.
- **Standard fact:** a mean-square bound uniform over all levels of the hierarchy.

## 14. `integral_sum_normSq_spdePath_periodic`
**Rendering.** For all real $\mu,\rho,k,h$, every $N\ge1$, every $N$-periodic $p:\mathbb Z\to\mathbb C$ and every $n$: with $\theta_m=2\pi m/N$ and $\hat p_m=N^{-1}\sum_{j<N}p_j\overline{e^{ij\theta_m}}$,
$$\mathbb E\sum_{j=0}^{N-1}|v^n_j|^2=N\sum_{m=0}^{N-1}|\hat p_m|^2\big(\mathbb E|A_{\theta_m}(z)|^2\big)^n .$$

**Assessment.**
- **Truth:** true. Discrete Fourier inversion gives $p_j=\sum_m\hat p_m e^{ij\theta_m}$ for all $j\in\mathbb Z$ (using periodicity). By linearity and #3, $v^n=\sum_m\hat p_m\prod_l A_{\theta_m}(Z_l)\,e_{\theta_m}$. Parseval applied pathwise (orthogonality of $e_{\theta_m}$ over $j<N$ holds for every $N$) removes the cross terms; then #6 applies term by term. The common noise is harmless because Parseval is applied before taking the expectation.
- **Checks:** exact iid-moment computation of the Lean recursion on $\mathbb Z$ with $p_j=\text{base}[j\bmod N]$, against the RHS (quadrature), for $N=1,\dots,7$, $n=0,\dots,3$, parameters of all signs including junk, 84 cases: maximum relative error $6\cdot10^{-41}$ (`s05`).
- **Hypotheses:** $0<N$ is superfluous ($N=0$ gives $0=0$).
- **Vacuity:** not vacuous ($N=3$).
- **Junk values:** none.
- **Standard fact:** Parseval/DFT diagonalisation of a periodic constant-coefficient scheme.

## 15. `spde_meanSquare_stable_periodic`
**Rendering.** Under the hypotheses of #7, with $N\ge1$, $p$ $N$-periodic and $nk\le T$:
$$\mathbb E\sum_{j<N}|v^n_j|^2\le(1+\mu^2\lambda k)^n\sum_{j<N}|p_j|^2\le e^{\mu^2\lambda T}\sum_{j<N}|p_j|^2 .$$

**Assessment.**
- **Truth:** true, by #14, #5 and discrete Parseval $\sum_j|p_j|^2=N\sum_m|\hat p_m|^2$, then $1+x\le e^x$. No violations in the admissible cases of `s05`.
- **Hypotheses:** $0<N$ is again superfluous.
- **Vacuity:** not vacuous.
- **Junk values:** none.
- **Standard fact:** $\ell^2$ mean-square stability on the periodic grid.

## 16. `spdeStep_heat`
**Rendering.** For all real $k,h,z$ and real $u$: $S$ with $\mu=\rho=0$ applied to $u$ (cast to ℂ) equals $\mathrm{heatStep}(k/(2h^2))\,u$, cast to ℂ.

**Assessment.**
- **Truth:** true. The first coefficient is $(0\cdot k+\sqrt0\,z)/(2h)=0$ and the second is $k/(2h^2)$. Sympy residual 0 (`s01`).
- **Vacuity:** no hypotheses.
- **Junk values:** none.
- **Standard fact:** with no noise and no drift, the scheme is explicit Euler for $v_t=\tfrac12v_{xx}$.

## 17. `norm_spdeStep_heat_le`
**Rendering.** If $k\ge0$, $k/h^2\le1$ and $|u_j|\le M$ for all $j$, then $|(S_{0,0}u)_j|\le M$ for every $z$ and $j$.

**Assessment.**
- **Truth:** true. With $r=k/(2h^2)\in[0,\tfrac12]$ the step is the convex combination $(1-2r)u_j+r u_{j+1}+r u_{j-1}$. Over 20000 samples the maximum of $|\cdot|-M$ was $0$ (`s07`).
- **Sharpness:** the condition is sharp. With $k/h^2=1.01$ and $u=(-1)^j$, $|\cdot|=1.02>1$; with $k=-0.1$ the bound also fails, so `hk` is needed.
- **Degenerate case:** $h=0$ gives the identity step (junk but harmless).
- **Hypotheses:** `hu` is required for all $j$ although only $j-1$, $j$, $j+1$ matter; slightly stronger than needed and harmless.
- **Vacuity:** not vacuous ($k=0.5$, $h=1$, $u=(-1)^j$, $M=1$).
- **Standard fact:** the discrete maximum principle for the explicit heat scheme ($r\le1/2$).
