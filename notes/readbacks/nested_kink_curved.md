# Blind read-back report: packet R36 (kink / nested SDE / axes-MIMC)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round22/packet_R36_kink.lean` |
| declarations audited | 8 (all theorems) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round22/work_R36` (`*.py` with matching `*.out`, plus the Lean scratch copy `scratch_R36.lean` / `.out`) |

**Elaboration check.** I made a scratch copy of the packet (`import MlmcLean`, theorems renamed `*_audit` in namespace `MLMC.AuditR36`, proofs `sorry`). It compiles. I also added these checks:
- `example : type_of% @X_audit := @MLMC.X` for all 8 theorems. All succeed, so the packet statements are the repository statements.
- Small `norm_num` tests. They confirm that `∑ x ∈ s, body` takes its body at precedence 67. So `(∑ ℓ ∈ range (L+1), blockMean … x - T)^2` means $\big((\sum_\ell \text{blockMean}) - T\big)^2$, and `∑ a, … + ∑ b, … - T` means $(\sum_a) + (\sum_b) - T$.
- Definitional checks on `nestedMimcDelta` at indices $(a,0)$ and $(0,b+1)$.
- `#print axioms` on the 8 repository theorems. It lists only `propext`, `Classical.choice` and `Quot.sound`.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `nested_sde_bias_le_of_weak` | theorem | true | no | no |
| 2 | `nested_kinks_sde_bias_rate` | theorem | true | no | no |
| 3 | `nested_kinks_sde_variance_rate` | theorem | true | no | no |
| 4 | `nested_kinks_sde_mlmc_complexity` | theorem | true | no | no |
| 5 | `nested_piecewise_linear_sde_bias_rate` | theorem | true | no | no |
| 6 | `nested_piecewise_linear_sde_variance_rate` | theorem | true | no | no (the integral in `hs` is genuine: see §6) |
| 7 | `nested_piecewise_linear_sde_mlmc_complexity` | theorem | true | no | no |
| 8 | `kinkInnerApprox_mimc_axes_complexity` | theorem | true | no | no |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.** Every explicit constant I checked has slack. Analytic bounds come out well inside the stated constants. Exact-enumeration tests reach at most 0.68 of the bound for Thm 1 and Thms 2/5, 0.32 for Thm 6 and 0.12 for the smooth part of Thm 3.
2. **The target $G(z)=\int g(z,v)\,\rho(dv)$ is a Bochner integral.** No measurability or integrability of $g$ is assumed, so $G$ may be the junk value 0. This is harmless. `hw` forces $G(z)=\lim_\ell \mu_\ell(z)$ for $\nu$-a.e. $z$, where $\mu_\ell(z)=\int gh_\ell(z,\cdot)\,d\rho$. So in effect $G$ is defined as that limit, and it is a.e. equal to a measurable function.
3. **`hs` in Thms 3/4 is stronger than needed.** It requires $(2^\ell)^4\,\mathbb E(gh_{\ell+1}-gh_\ell)^4\le c_s$, i.e. one-sample $L^4$ strong error $O(2^{-\ell})$ (Milstein-type). That excludes a plain Euler–Maruyama inner sampler. The variance rate $3/2$ would survive a weaker condition, because the averaging over $2^{\ell+1}$ inner samples gains an extra factor. Thms 6/7 assume only $2^{\ell/2}\,\mathbb E(gh_{\ell+1}-gh_\ell)^2\le c_s$.
4. **Thms 5/6/7 assume `[Nonempty ι]`.** This is unnecessary and only a harmless weakening. Thms 5/6 need no global moments of $gh$. They state integrability and bounds only for the *difference* $f(\bar Y)-f(G)$ and for $\Delta$, which is correct design. Thm 7 adds `hg0` ($gh_0\in L^2(\nu\otimes\rho)$), which is needed for $\Delta_0\in L^2$ and for the target $\int f(G)\,d\nu$ not to be junk.
5. **The structural hypotheses are standard for nested MLMC but strong.**
   - `hw` is a $\nu$-a.e. uniform conditional weak error.
   - `hcent` is a uniform conditional 4th central moment.
   - `hball` is a bounded "density" of $G$ near each kink, stated with outer measure.
   - Several constants are forced to have a sign: $K\ge0$, $c_w\ge0$, $c_{d,i}>0$, and $m_4,\kappa_4,c_s\ge0$.
6. **Thm 8 is about one specific toy model, and the estimator uses only the two axes of the multi-index set.** It is consistent only because, in this model, $\mathbb E f(\bar Y)$ separates into a function of $M$ plus a function of $\ell$: $\tfrac12(\tfrac12+2^{-\ell}/8)^2+\tfrac1{128M}$. So mixed differences have mean 0. I verified this exactly (`t8_axes_example.out`: bias $=2^{-L}(\tfrac1{16}+\tfrac1{128})+4^{-L}/128$, and the mixed difference is $0$). It is not a general MIMC theorem.

---

## Common notation

- $(\mathcal Z,\nu)$ and $(\mathcal W,\rho)$ are probability spaces. $\mathbb P:=$ `nestedLaw ν ρ` $=\nu\otimes\rho^{\otimes\mathbb N}$ on $\mathcal Z\times\mathcal W^{\mathbb N}$, with points $p=(z,w)$.
- $gh_\ell:\mathcal Z\times\mathcal W\to\mathbb R$ for $\ell\in\mathbb N$, and $\mu_\ell(z):=\int gh_\ell(z,v)\,\rho(dv)$.
- $G(z):=\int g(z,v)\,\rho(dv)$, a Bochner integral that is $0$ if $g(z,\cdot)\notin L^1$.
- $\bar Y_\ell^{M}(z,w):=\frac1M\sum_{m<M}gh_\ell(z,w_m)$ (`innerMean`). $\theta^M w:=(w_{M+m})_m$ (`shiftSeq`).
- `nestedSdeP f gh ℓ` $=P_\ell:=f(\bar Y^{2^\ell}_\ell)$ and `nestedTarget f g ρ` $=f(G(z))$.
- `nestedSdeDelta f gh 0` $=P_0=f(gh_0(z,w_0))$.
- `nestedSdeDelta f gh (ℓ+1)` $=\Delta_{\ell+1}:=f(\bar Y_{\ell+1}^{2^{\ell+1}}(z,w))-\tfrac12 f(\bar Y_\ell^{2^\ell}(z,w))-\tfrac12 f(\bar Y_\ell^{2^\ell}(z,\theta^{2^\ell}w))$. This is the antithetic difference: the fine level uses $gh_{\ell+1}$ with $2M$ samples, and the two coarse halves use $gh_\ell$ with $M=2^\ell$ samples each.
- `blockMean F ω i N x` $=\frac1N\sum_{n<N}F_i(\omega(i,n)(x))$. `totalCost cost L N x` $=\sum_{\ell\le L}\sum_{n<N_\ell}\mathrm{cost}_{\ell,n}(x)$.

## 1. `nested_sde_bias_le_of_weak`

**Rendering.** Data:
- $f,f':\mathbb R\to\mathbb R$ with $f$ differentiable everywhere and derivative $f'$.
- $|f'(y)-f'(x)|\le K(y-x)$ for $x\le y$, i.e. $f'$ is $K$-Lipschitz. This forces $K\ge0$.

Hypotheses on $gh$ and $g$, all with constants independent of $\ell$:
- each $gh_\ell$ is jointly measurable;
- $gh_\ell^4\in L^1(\nu\otimes\rho)$ with $\int gh_\ell^4\,d(\nu\otimes\rho)\le m_4$ for all $\ell$;
- for $\nu$-a.e. $z$, $2^\ell|\mu_\ell(z)-G(z)|\le c_w$ for all $\ell$. This forces $c_w\ge0$.

Conclusion, for every $\ell\in\mathbb N$: $P_\ell-f\circ G\in L^1(\mathbb P)$, and
$$2^\ell\Big|\mathbb E_{\mathbb P}[f(\bar Y^{2^\ell}_\ell)-f(G)]\Big|\le \tfrac K2(1+16m_4)+c_w\big(|f'(0)|+K(1+m_4)\big)+\tfrac K2c_w^2.$$

**Assessment.**
- *Truth: true.* Fix $z$ and put $M=2^\ell$. Write $f(\bar Y)-f(G)=[f(\bar Y)-f(\mu_\ell)]+[f(\mu_\ell)-f(G)]$.
  - First bracket, by Taylor about $\mu_\ell$: $\mathbb E[\cdot\mid z]\le \frac K2\operatorname{Var}(gh_\ell\mid z)/M$, because the linear term has conditional mean 0.
  - Second bracket: it is at most $|f'(\mu_\ell)|\,c_w/M+\frac K2c_w^2/M^2$, with $|f'(\mu)|\le|f'(0)|+K|\mu|$.
  - Multiplying by $M$ and averaging gives $\frac K2\mathbb E\,gh^2+c_w(|f'(0)|+K\mathbb E|\mu_\ell|)+\frac K2c_w^2 2^{-\ell}$.
  - This fits inside the bound because $\mathbb E\,gh^2\le(1+m_4)/2$ and $\mathbb E|\mu_\ell|\le m_4^{1/4}\le 1+m_4$.
  - Integrability: $f$ grows at most quadratically, $gh_\ell\in L^4$, and $|G|\le|\mu_\ell|+c_w$ a.e. Measurability: $G$ is the a.e. limit of the measurable $\mu_\ell$.
  - Numerics (`bias_bounds_check.out`, quadratic $f$ saturating the Taylor remainder): the largest ratio of the left side to the bound is 0.67.
- *Vacuity: no.* For example take $f(x)=x^2$, $f'=2x$, $K=2$, with the toy model of §2 ($\nu=U[0,1]$, $\rho$ a fair coin, $gh_\ell=z\pm\frac18+2^{-\ell}/8$, $c_w=\frac18$).
- *Junk: no.* The $m_4$ integral is genuine (by `hgh4`). A junk $G$ is pinned a.e. by `hw` (main point 2).
- The constant $16m_4$ is loose.
- *Standard result:* nested-simulation bias of order $O(1/M)$ plus the inner weak error $O(2^{-\ell})$ for a $C^{1,1}$ outer function (Taylor argument, e.g. Giles–Haji-Ali, multilevel nested simulation).

## 2. `nested_kinks_sde_bias_rate`

**Rendering.** Here $f=f_0+\sum_{i\in\iota}c_i\,(x-k_i)^+$, with $\iota$ a finite type that may be empty, and $f_0\in C^{1,1}$ with constant $K$ as in §1. The hypotheses are those of §1 for $gh$, $m_4$ and $c_w$, plus:
- `hcent`: for all $\ell$ and $\nu$-a.e. $z$, $\int(gh_\ell(z,v)-\mu_\ell(z))^4\rho(dv)\le\kappa_4$.
- `hball`: for all $i$ and all $t>0$, $\nu^*\{z:|G(z)-k_i|\le t\}\le c_{d,i}\,t$. This uses outer measure, written via `ENNReal.ofReal`, and it forces $c_{d,i}>0$.

Conclusion, for every $\ell$: $P_\ell-f\circ G\in L^1(\mathbb P)$, and
$$2^\ell|\mathbb E[P_\ell-f(G)]|\le[\text{bound of §1 for }f_0]+\sum_i|c_i|\big(4c_{d,i}(1+80\kappa_4)(1+c_w)+c_w\big).$$

**Assessment.**
- *Truth: true.* The bound is linear in $f$. The $f_0$ part is §1. Each kink $\varphi=(\cdot-k)^+$ splits into $|\varphi(\mu_\ell)-\varphi(G)|\le c_w/M$ (the "$+c_w$" term) plus $\mathbb E[\varphi(\mu+e)-\varphi(\mu)\mid z]$, with $e=\bar Y-\mu$.
  - The second piece is at most $\mathbb E[(|e|-d)^+\mid z]$, where $d=|\mu_\ell-k|$.
  - That is at most $\min\big(\kappa_4^{1/4}M^{-1/2},\ \tfrac{27}{256}\cdot 3\kappa_4/(M^2d^3)\big)$, using $\mathbb E e^4\le3\kappa_4/M^2$.
  - Use $\nu\{d\le r\}\le c_d(r+c_w/M)$ and a layer-cake integration.
  - Result: $M\cdot(\ldots)\le c_d(1.02\sqrt{\kappa_4}+\kappa_4^{1/4}c_w M^{-1/2})\le c_d(1+\kappa_4)(1+c_w)$, far inside $4c_d(1+80\kappa_4)(1+c_w)$.
  - Numerics: the worst ratio on a grid of skewed two-point inner laws and uniform or one-sided $G$ is 0.68, attained where the $c_w$ term dominates.
- *Vacuity: no.* Take $\nu=U[0,1]$, $\rho$ a fair coin, $gh_\ell(z,b)=z\pm\frac18+2^{-\ell}/8$ and $g(z,b)=z\pm\frac18$, so $G(z)=z$. Take $f=(x-\frac12)^+$, $f_0=0$, $K=0$, $\iota$ a singleton, $c=1$, $k=\frac12$, $c_d=2$, $c_w=\frac18$, $\kappa_4=8^{-4}$, $m_4=3$.
- *Junk: no.* The `hcent` integrals are genuine, since by Fubini $gh_\ell(z,\cdot)\in L^4(\rho)$ for a.e. $z$.
- *Standard result:* $O(1/M)$ bias of nested MC for piecewise-linear outer functions under a bounded density of the conditional mean near the kinks (Giles–Haji-Ali; Bujok–Hambly–Reisinger), combined with an $O(2^{-\ell})$ inner weak error.

## 3. `nested_kinks_sde_variance_rate`

**Rendering.** Same $f$ and hypotheses as §2, plus `hs`: for all $\ell$, $(2^\ell)^4\int(gh_{\ell+1}-gh_\ell)^4\,d(\nu\otimes\rho)\le c_s$. Conclusion, for every $\ell$: $\Delta_{\ell+1}\in L^2(\mathbb P)$, and
$$2^{\frac32\ell}\,\mathbb E\Delta_{\ell+1}^2\le(|\iota|+1)\Big(3(\tfrac K8)^2\,224m_4+\tfrac32\big(8(|f_0'(0)|^4+K^4m_4)+(1+\tfrac{K^2}2)c_s\big)+\sum_ic_i^2\big(6c_{d,i}(1+16\kappa_4)(1+c_w)+\tfrac32(\tfrac94c_w^2+\tfrac{1+c_s}2)\big)\Big).$$

**Assessment.**
- *Truth: true.* $\Delta$ is linear in $f$, which gives the factor $|\iota|+1$ by Cauchy–Schwarz. Split $\Delta=A+B$, where:
  - $A$ is the antithetic term on the coarse pair $(a,b)$;
  - $B=f(x)-f(\tfrac{a+b}2)$, with $x-\tfrac{a+b}2=D$ the average over $2M$ of $gh_{\ell+1}-gh_\ell$;
  - $(A+B)^2\le3A^2+\tfrac32B^2$.

  Smooth part:
  - $|A_{f_0}|\le\frac K8(a-b)^2$ and $\mathbb E(a-b)^4\le 12\cdot16m_4/M^2=192m_4/M^2\le224m_4$.
  - $B_{f_0}^2\le 2f_0'(y)^2D^2+\frac{K^2}2D^4$, and $2f_0'^2D^2\le 4^{-\ell}f_0'^4+4^\ell D^4$.
  - $\mathbb E D^4\le c_s16^{-\ell}$ and $\mathbb E f_0'(y)^4\le8(|f_0'(0)|^4+K^4m_4)$. This reproduces the stated term exactly.

  Kinks:
  - $|A_\varphi|\le\frac12\min(|a-k|,|b-k|)$ on a straddle, which gives $\mathbb E A_\varphi^2\le\frac12c_d(0.87\kappa_4^{3/4}M^{-3/2}+\sqrt{\kappa_4}c_wM^{-2})$.
  - $|B_\varphi|\le|D|$ with $\mathbb E D^2\le\sqrt{c_s}4^{-\ell}\le\frac{1+c_s}2 4^{-\ell}$.

  Numerics: the smooth part (empty $\iota$, quadratic $f_0$) reaches at most 0.12 of the bound.
- *Vacuity: no.* Use the toy model of §2 with $c_s=16^{-4}$.
- *Junk: no.* The `hs` integrand is integrable by `hgh4`.
- *Remark:* `hs` is one-sample $L^4$ strong order 1 (Milstein-type). This is stronger than needed for $\beta=3/2$ (main point 3), so the theorem is weaker than it could be, but it is correct.
- *Standard result:* the antithetic nested-MLMC variance $O(M^{-3/2})$ for kinks (Bujok–Hambly–Reisinger 2015; Giles–Haji-Ali 2019), here with level-dependent inner samplers.

## 4. `nested_kinks_sde_mlmc_complexity`

**Rendering.** The hypotheses of §3 (including `hball` and `hs`) hold, and in addition:
- $(\Omega,\mu)$ is a measure space and $\omega:\mathbb N\times\mathbb N\to\Omega\to\mathcal Z\times\mathcal W^{\mathbb N}$.
- Each $\omega_{(\ell,n)}$ is measure-preserving onto $\mathbb P$, which forces $\mu$ to be a probability measure.
- The family $(\omega_p)_p$ is mutually independent.
- $\mathrm{cost}_{\ell,n}\in L^1(\mu)$ with mean $C_\ell\le c_3\,4^\ell$, and $c_3>0$.

Conclusion: there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N_{>0}$ with:
- the squared error $\big(\sum_{\ell\le L}\mathrm{blockMean}(\Delta_\ell)-\int f(G)\,d\nu\big)^2$ lies in $L^1(\mu)$;
- its mean is $<\varepsilon^2$;
- $\mathbb E_\mu[\mathrm{totalCost}]\le c_4\varepsilon^{-5/2}$.

The constant $c_4$ does not depend on $\varepsilon$.

**Assessment.**
- *Truth: true.* The expectations telescope, $\sum_{\ell\le L}\mathbb E\Delta_\ell=\mathbb E P_L$, because the shift preserves $\rho^{\otimes\mathbb N}$.
  - Bias $\le c\,2^{-L}$ by §2, so $\alpha=1$.
  - $\mathbb E\Delta_{\ell+1}^2\le V2^{-3\ell/2}$ by §3, so $\beta=3/2$. Also $\Delta_0\in L^2$ by quadratic growth and `hgh4`.
  - Cost $\gamma=2$.
  - Giles' theorem with $\beta<\gamma$ gives $\varepsilon^{-2-(\gamma-\beta)/\alpha}=\varepsilon^{-5/2}$.
  - The target $\int f(G)\,d\nu$ is a genuine integral, since $|G|\le|\mu_0|+c_w$ a.e. and $\mu_0\in L^4$.
  - Numerics (`complexity_check.out`): $\text{cost}\cdot\varepsilon^{5/2}$ stays bounded (150–340) as $\varepsilon\to0$.
- *Vacuity: no.* Use the toy model, with $\Omega$ an infinite product of copies of $\mathbb P$, $\omega$ the coordinates, and $\mathrm{cost}=C_\ell=4^\ell$.
- *Junk: no.* $N_\ell>0$, so `blockMean` never divides by 0. The bound uses only upper bounds on $C_\ell$, which is fine because $N_\ell\ge0$.
- *Standard result:* the MLMC complexity theorem (Giles 2008; Cliffe–Giles–Scheichl–Teckentrup), here with $\alpha=1$, $\beta=3/2$, $\gamma=2$.

## 5. `nested_piecewise_linear_sde_bias_rate`

**Rendering.**
- $\iota$ is finite and **nonempty**, and $f(x)=a_0+a_1x+\sum_ic_i(x-k_i)^+$.
- $gh_\ell$ is jointly measurable.
- `hfib`: for all $\ell$ and $\nu$-a.e. $z$, $gh_\ell(z,\cdot)^4\in L^1(\rho)$ and the 4th central moment is at most $\kappa_4$. **There is no global moment assumption.**
- `hw` and `hball` are as before.

Conclusion, for every $\ell$: $P_\ell-f\circ G\in L^1(\mathbb P)$, and $2^\ell|\mathbb E[P_\ell-f(G)]|\le|a_1|c_w+\sum_i|c_i|(4c_{d,i}(1+80\kappa_4)(1+c_w)+c_w)$.

**Assessment.**
- *Truth: true.*
  - Integrability: $f$ is Lipschitz, $|\bar Y-G|\le|e|+c_w/M$, and $\mathbb E[|e|\mid z]\le(3\kappa_4)^{1/4}M^{-1/2}$ uniformly in $z$.
  - Affine part: $a_1\mathbb E[\mu_\ell-G]$, bounded by $|a_1|c_w/M$.
  - Kinks: as in §2.
  - Only the difference is claimed integrable. $f(\bar Y)$ and $f(G)$ separately need not be, which is correct design.
- *Vacuity: no.* Use the toy model with $a_0=a_1=0$.
- *Junk: no.*
- `[Nonempty ι]` is an unnecessary hypothesis and a harmless weakening.
- *Standard result:* as in §2, for piecewise-linear payoffs.

## 6. `nested_piecewise_linear_sde_variance_rate`

**Rendering.** Same setting as §5, plus `hs`: for all $\ell$, $2^{\ell/2}\int(gh_{\ell+1}-gh_\ell)^2\,d(\nu\otimes\rho)\le c_s$ (real power). Conclusion, for every $\ell$: $\Delta_{\ell+1}\in L^2(\mathbb P)$, and
$$2^{\frac32\ell}\mathbb E\Delta_{\ell+1}^2\le(|\iota|+1)\Big(\tfrac32a_1^2(\tfrac94c_w^2+c_s)+\sum_ic_i^2\big(6c_{d,i}(1+16\kappa_4)(1+c_w)+\tfrac32(\tfrac94c_w^2+c_s)\big)\Big).$$

**Assessment.**
- *Truth: true.* $A_{\text{affine}}=0$ and $B_{\text{affine}}=a_1D$.
  - $\mathbb E D^2=\mathbb E[(\mu_{\ell+1}-\mu_\ell)^2]+\mathbb E\operatorname{Var}(\mathrm{diff}\mid z)/(2M)$.
  - This is at most $\frac94c_w^2 4^{-\ell}+\frac{c_s}2 2^{-3\ell/2}$.
  - Kinks: as in §3.
  - Numerics (`var_bounds_check.out`): the worst ratio over a grid, with the drift sign alternating to saturate $\frac94c_w^2$ and the noise $\tau_\ell\propto2^{-\ell/4}$ saturating `hs`, is 0.32.
- *Vacuity: no.* Use the toy model with $c_s=1/256$.
- *Junk: no.* Square-integrability of $gh_{\ell+1}-gh_\ell$ over $\nu\otimes\rho$ is not assumed explicitly, but it follows from `hfib` and `hw`: $\mathbb E[\mathrm{diff}^2\mid z]\le4\sqrt{\kappa_4}+\frac94c_w^24^{-\ell}$ a.e. So the integral in `hs` is genuine, not the junk value 0.
- `hs` itself is weak: $L^2$ strong order only $1/4$.
- `[Nonempty ι]` is unnecessary.
- *Standard result:* antithetic nested MLMC with $\beta=3/2$ for piecewise-linear payoffs.

## 7. `nested_piecewise_linear_sde_mlmc_complexity`

**Rendering.** The hypotheses of §6, plus `hg0` ($gh_0^2\in L^1(\nu\otimes\rho)$) and the sampling and cost hypotheses of §4 ($C_\ell\le c_3 4^\ell$). The conclusion is identical to §4: there is $c_4>0$ such that for all $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N>0$ with $\mathrm{MSE}<\varepsilon^2$ and $\mathbb E[\text{cost}]\le c_4\varepsilon^{-5/2}$.

**Assessment.**
- *Truth: true.* This is §4's argument with §5 and §6.
  - `hg0` gives $\Delta_0=f(gh_0)\in L^2$ and $f\circ G\in L^1(\nu)$, since $|G|\le|\mu_0|+c_w$.
  - So the target integral is genuine, every $P_\ell$ is integrable, and the telescoping is valid.
- *Vacuity: no.* Use the toy model.
- *Junk: no.* `hg0` is exactly what prevents a junk target.
- *Standard result:* the MLMC complexity theorem with $(\alpha,\beta,\gamma)=(1,3/2,2)$, giving $\varepsilon^{-5/2}$.

## 8. `kinkInnerApprox_mimc_axes_complexity`

**Rendering.** A concrete model:
- Outer $z\sim U[0,1]$ (`kinkOuter` = Lebesgue on $[0,1]$); inner $b\sim$ fair coin (`kinkCoin`).
- `kinkInner` $=z\pm\frac18$, so the inner mean is $z$; `kinkInnerApprox ℓ` $=z\pm\frac18+2^{-\ell}/8$.
- $f(y)=(y-\frac12)^+$; the target is $\int_0^1(z-\frac12)^+dz=\frac18$.
- $\omega:(\mathrm{Fin}\,2\to\mathbb N)\times\mathbb N\to\Omega\to\mathbb R\times\mathrm{Bool}^{\mathbb N}$ are i.i.d. with law `nestedLaw kinkOuter kinkCoin`.
- Costs satisfy $C_{(\ell_0,\ell_1)}\le c_3 2^{\ell_0+\ell_1}$.

Conclusion: there is $c_4>0$ such that for all $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N>0$ such that the **axes-only** MIMC estimator has $\mathrm{MSE}<\varepsilon^2$ (and is square-integrable) and expected cost $\le c_4\varepsilon^{-2}$. The estimator is
$$\sum_{a\le L}\mathrm{blockMean}\big(\Delta^{\rm MI}_{(a,0)}\big)+\sum_{b<L}\mathrm{blockMean}\big(\Delta^{\rm MI}_{(0,b+1)}\big),$$
where:
- $\Delta^{\rm MI}_{(a,0)}$ = `nestedDelta f (gh 0) a` is antithetic in the number of inner samples, with $2^a$ samples;
- $\Delta^{\rm MI}_{(0,b+1)}=f(gh_{b+1}(z,w_0))-f(gh_b(z,w_0))$, as checked in Lean.

The expected cost is the sum of the costs over the samples used.

**Assessment.**
- *Truth: true.*
  - Exactly, $\mathbb E f(\bar Y^M_\ell)=\frac12(\frac12+2^{-\ell}/8)^2+\frac1{128M}$, which separates into a term in $\ell$ plus a term in $M$. So the axes telescope to the bias $2^{-L}(\frac1{16}+\frac1{128})+\frac{4^{-L}}{128}$, verified exactly for $L\le12$.
  - Variances: $\mathbb E\Delta_{(a,0)}^2\approx1.8\cdot10^{-4}\,2^{-1.5(a-1)}$, with cost $2^a$. $\mathbb E\Delta_{(0,b+1)}^2\le4^{-b}/256$, with cost $2^{b+1}$.
  - Both series $\sum\sqrt{VC}$ converge, giving cost $O(\varepsilon^{-2})$. Numerically $\text{cost}\cdot\varepsilon^2\to\approx1.5$.
  - The indices $(a,0)$ and $(0,b+1)$ are distinct, so the block means are independent.
- *Vacuity: no.* Use a product space, $\omega$ the coordinates, and $\mathrm{cost}=2^{\ell_0+\ell_1}$.
- *Junk: no.* The target is a genuine integral, and $N>0$.
- *Caveat:* the result depends on this example's additive structure, which makes mixed differences zero in mean (main point 6). It is a model-specific corollary, not a general MIMC theorem.
- *Standard result:* MIMC (Haji-Ali–Nobile–Tempone 2016) restricted to the axes, reaching the canonical $\varepsilon^{-2}$ when $\beta_i>\gamma_i$ in each direction.
