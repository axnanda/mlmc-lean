# Blind statement audit: `packet_M1_ml2r_thm2_indexset.lean`

| Field | Value |
|---|---|
| Date | 2026-09-29 |
| Packet | `readback/round11/packet_M1_ml2r_thm2_indexset.lean` |
| Declarations audited | 23 (9 theorems, 14 definitions: 6 in the two modules, 8 appended) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round11/work_M1/`, containing `ml2r_weights.py`, `ml2r_complexity.py`, `mimc_complexity.py`, `mimc_boundary_split.py`, `mimc_core_rounding.py` and `defs_check.py`, each with a `.out` of the same name |

Sources consulted: the packet; Mathlib at `.lake/packages/mathlib` (`variance`/`evariance`, `IndepFun`/`iIndepFun`,
`MeasurePreserving`, `Fintype.piFinset`, `Nat.floor`, big-operator syntax); and the Lean 4.33.1 core source for
the `in` combinator, which lives in the elan toolchain outside the repository. I did not open any other repository file.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `abs_ml2rWeight_le_sharp` | theorem | **true** | no | no |
| 2 | `ml2rBiasConst` | def | faithful | n/a | n/a (junk only at α ≤ 0, never used) |
| 3 | `ml2r_bias_le` | theorem | **true** | no | no |
| 4 | `ml2rEstimator` | def | faithful ML2R estimator | n/a | n/a (`N ℓ = 0` junk excluded by every use) |
| 5 | `ml2r_theorem_eq` | theorem | **true** | no | no |
| 6 | `ml2r_theorem_lt` | theorem | **true** | no | no |
| 7 | `mimcEta` | def | faithful | n/a | n/a |
| 8 | `mimcD2` | def | faithful | n/a | n/a |
| 9 | `mimcD3` | def | faithful | n/a | n/a |
| 10 | `mimcBound` | def | faithful | n/a | n/a |
| 11 | `mimc_complexity_core_indexSet` | theorem | **true** | no | no |
| 12 | `mimc_complexity_indexSet` | theorem | **true** | no | no |
| 13 | `mimc_complexity_boundary_indexSet` | theorem | **true** | no | no (the ℕ-subtraction is exactly the intended $\max(0,\cdot)$) |
| 14 | `giles_theorem2_indexSet` | theorem | **true** | no | no (see main point 1 on scoping) |
| 15 | `giles_theorem2_boundary_indexSet` | theorem | **true** | no | no (same) |
| 16 | `levelDiff` (appended) | def | faithful | n/a | n/a |
| 17 | `blockMean` (appended) | def | faithful | n/a | n/a ($N=0$ gives 0; always excluded) |
| 18 | `crossDiff` (appended) | def | faithful | n/a | n/a (`ℓ 0 - 1` guarded by `if ℓ 0 = 0`) |
| 19 | `dot` (appended) | def | faithful | n/a | n/a |
| 20 | `crit` (appended) | def | faithful | n/a | n/a |
| 21 | `indexSet` (appended) | def | faithful for $\theta>0$ | n/a | n/a (box truncation is exact when $\theta_d>0$, which always holds here) |
| 22 | `ml2rNode` (appended) | def | faithful | n/a | n/a |
| 23 | `ml2rWeight` (appended) | def | faithful | n/a | n/a (denominators $\neq0$ for $\alpha>0$) |

No statement is false, none is vacuous, and none depends on a junk value.

## Main points for a human auditor

1. **Scoping artefact on `variable [IsProbabilityMeasure μ]` (packet lines 121–123).** In the packet, this `variable`
   command is preceded by `open Filter Topology in` twice. In Lean 4.33.1, `cmd₁ in cmd₂` expands to
   `section cmd₁ … cmd₂ end` (`Lean/Elab/BuiltinCommand.lean`, `expandInCmd`). Read literally, the `variable` is
   therefore discarded at once, and **neither `giles_theorem2_indexSet` nor `giles_theorem2_boundary_indexSet`
   assumes that μ is a probability measure.** The most likely explanation is that the two `open … in` lines belonged
   to helper declarations the packet generator left out, and that the real source has a standalone `variable`.
   Please check with `#check @MLMC.giles_theorem2_indexSet`.
   **Truth is unaffected under either reading:**
   - `hind` applied to the sets `univ, univ` gives $\mu(\Omega)=\mu(\Omega)^2$, so $\mu(\Omega)\in\{0,1,\infty\}$.
   - If $\mu=0$, the conclusion is trivial.
   - If $\mu(\Omega)=\infty$, independence plus $Y_{\ell,n}\in L^2$ gives $\mu(|Y|>t)\in\{0,\infty\}$ and also $\mu(|Y|>t)<\infty$. So $Y=0$ a.e. Then `h_iii` and telescoping give $E P_\ell=0$, and `h_i` gives $E P=0$. The MSE is $0$, and the cost bound is the deterministic one.
2. **The ML2R hypothesis `hexp` is strong but satisfiable.** One remainder constant $K$ must work for *every*
   expansion order $L$, and the coarse node is fixed at $x_0=2^0=1$.
   - At $\ell=0$ it forces bounded partial sums of $(a_n)$, hence $|a_n|\le 2K$.
   - For $\ell\ge1$ it forces $E P_\ell-EP=\sum_{n\ge1}a_n2^{-\alpha\ell n}$.
   - It holds, for example, whenever $E P_\ell-EP=\sum_n a_n 2^{-\alpha\ell n}$ with $\sum|a_n|<\infty$ (take $K=\sum|a_n|$). This includes a pure first-order bias.

   It is stronger than Lemaire–Pagès' $(WE^\infty_\alpha)$, which has a free coarse step $h$, order-dependent remainders and a growth condition on $c_R$. It is a modelling choice, not an error.
3. **The boundary exponents $2d_2+(d_3-3)_+$ and $(d_2-1)(2+\eta)+(d_3-1)_+$ in #13/#15 are correct and cannot be
   dropped.** They come from the rounding cost $\sum_{\ell\in I(L)}c_3 2^{\gamma\cdot\ell}\asymp 2^{2L}L^{d_3-1}$. That cost is forced because $N_\ell\ge1$ on all of $I(L)$ and because the bias condition sets a minimum $L$.
   - With $\eta=0$ and $d_3\ge4$, it exceeds the Lagrange part $\varepsilon^{-2}|\log\varepsilon|^{2d_2}$.
   - Numerically, in the symmetric model with $D=d_2=d_3\in\{4,5,6\}$, the local log-slope of the rounding part tends to $3D-3$ (`mimc_boundary_split.out`). For $D=4$ the exponent must therefore be 9, not 8.
   - The truncated ℕ-subtraction is exactly the intended $\max(0,\cdot)$.
4. **Rates.**
   - Richardson–Romberg weights on the nodes $x_\ell=2^{-\alpha\ell}$ satisfy $\sum_\ell w_\ell x_\ell^{L+1}=(-1)^L2^{-\alpha L(L+1)/2}$ (checked exactly). The ML2R bias rate $2^{-\alpha L(L+1)/2}$ is therefore the natural one, and it forces $L\approx\sqrt{2\log_2(1/\varepsilon)/\alpha}$.
   - The resulting cost $\varepsilon^{-2}2^{(\gamma-\beta)\sqrt{2\log_2(1/\varepsilon)/\alpha}}=\varepsilon^{-2}\exp\!\big(\tfrac{\gamma-\beta}{\sqrt\alpha}\sqrt{2\ln2\,\ln(1/\varepsilon)}\big)$ is Lemaire–Pagès' ML2R rate with $M=2$ and their cost exponent 1 replaced by $\gamma$.
   - $\{\ell:\theta\cdot\ell\le L\}$ with $\theta_d=\alpha_d+(\gamma_d-\beta_d)/2$ is the optimal total-degree index set of Haji-Ali–Nobile–Tempone.
5. **Minor points, none affecting truth:**
   - The constant $e^{2q/(1-q)^2}$ ($q=2^{-\alpha}$) in #1 and #2 is far cruder than the classical $\prod_{j\ge1}(1-q^j)^{-2}$ for small $\alpha$: $5\cdot10^{180}$ against $4.5\cdot10^{18}$ at $\alpha=0.1$. It is still valid.
   - `_hβ` in #14/#15 is unused.
   - In #5/#6, `hγ : 0 < γ`, `hPlm` and $c_2,c_3>0$ are not needed.
   - The costs $C_\ell$ are only bounded above, which is harmless for an upper bound.
   - In #14/#15, $c_4$ is chosen after the random data, which is weaker than "depends only on $c_i,\alpha,\beta,\gamma$". The deterministic #12/#13 already supply such a constant.

---

## Per-declaration audit

Notation: $q=2^{-\alpha}$, $x_\ell=\texttt{ml2rNode}\ \alpha\ \ell=2^{-\alpha\ell}$,
$w^{(L)}_\ell=\texttt{ml2rWeight}\ \alpha\ L\ \ell$, $W^{(L)}_\ell=\sum_{k=\ell}^{L}w^{(L)}_k$,
$\Delta P_\ell=\texttt{levelDiff}$, $\theta_d=\alpha_d+(\gamma_d-\beta_d)/2$, $I(L)=\texttt{indexSet}\ \theta\ L$,
$\eta,d_2,d_3$ as in #7–#9, $B(\eta,e_1,e_2;\varepsilon)=\texttt{mimcBound}$.

Parsing notes:
- The Mathlib big-operator body is `term:67` (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`, l.181). So `∑ ℓ ∈ s, f ℓ - c` means $(\sum f)-c$. This is the intended reading in #3 and #14/#15.
- All `(2:ℝ) ^ x` are `Real.rpow` with a positive base.
- `ε ^ (-2:ℝ)`, `|log ε| ^ e` and `(-log ε) ^ e` are rpow with bases $>0$ (indeed $>1$ for the log terms) on $0<\varepsilon<e^{-1}$.

### 1. `abs_ml2rWeight_le_sharp` (theorem)

**Rendering.** For real $\alpha>0$ and natural numbers $\ell\le L$:
$$|w^{(L)}_\ell|\le \big(e^{q/(1-q)^2}\big)^2\,2^{-\alpha(L-\ell)(L-\ell+1)/2},$$
where $L-\ell$ is computed in ℝ.

**Assessment.** **True.**
- *Proof.* Put $m=L-\ell$. For $k<\ell$ the factor is $1/(1-q^{\ell-k})$; for $k>\ell$ it is $-q^{k-\ell}/(1-q^{k-\ell})$. Hence $w_\ell=(-1)^m q^{m(m+1)/2}\big/\big(\prod_{j=1}^{\ell}(1-q^j)\prod_{j=1}^{m}(1-q^j)\big)$. Each partial product is at least $\Pi_\infty=\prod_{j\ge1}(1-q^j)$, and $-\ln\Pi_\infty\le\sum_j q^j/(1-q^j)\le q/(1-q)^2$ because $-\ln(1-x)\le x/(1-x)$.
- *Numerics* (`ml2r_weights.out`, 400 digits, $\alpha\in[0.05,30]$, $L\le40$): the maximum of $|w|/\text{bound}$ stays below 1. The margin shrinks to $\approx 9\cdot10^{-19}$ at $\alpha=30$ but stays positive. The sign pattern $(-1)^{L-\ell}$ is confirmed.
- *Vacuity.* Not vacuous: for $\alpha=1,L=2,\ell=1$, $w=-2$ and the bound is $e^4/2\approx27.3$.
- *Junk.* None: $x_k\ne x_\ell$ because $\alpha>0$.
- *Standard result.* This is the classical closed form of multistep Richardson–Romberg weights (Pagès 2007; Lemaire–Pagès 2017) with refiners $2^{i-1}$. The word "sharp" refers to the Gaussian-type exponent $(L-\ell)(L-\ell+1)/2$, not to the constant, which is crude for small $\alpha$ (main point 5).

### 2. `ml2rBiasConst` (def)

**Rendering.** $C_{\rm b}(\alpha)=\big(e^{q/(1-q)^2}\big)^2\,\big(1+(1-q)^{-1}\big)$.

**Assessment.** For $\alpha>0$ this is finite and at least 2. At $\alpha\le0$ it would involve junk (division by $0$ at $\alpha=0$), but every use assumes $\alpha>0$.

### 3. `ml2r_bias_le` (theorem)

**Rendering.** Let $\alpha>0$ and $L\in\mathbb N$. Let $(E_\ell)$ be real numbers, and let $EP$, $(a_n)$ and $K$ be reals. Suppose that for all $\ell\le L$,
$$\Big|E_\ell-EP-\sum_{n=1}^{L}a_nx_\ell^n\Big|\le Kx_\ell^L.$$
Then
$$\Big|\sum_{\ell=0}^{L}w^{(L)}_\ell E_\ell-EP\Big|\le C_{\rm b}(\alpha)\,K\,2^{-\alpha L(L+1)/2}.$$

**Assessment.** **True.**
- *Proof.* The weights are the Lagrange weights at $0$, so $\sum_\ell w_\ell=1$ and $\sum_\ell w_\ell x_\ell^n=0$ for $1\le n\le L$ (checked to $10^{-378}$). The bias is therefore $\sum_\ell w_\ell r_\ell$ with $|r_\ell|\le Kx_\ell^L$. The exponent identity $\tfrac{m(m+1)}2+\ell L=\tfrac{L(L+1)}2+\tfrac{\ell(\ell-1)}2$ and #1 give $|w_\ell|x_\ell^L\le\Pi_\infty^{-2}q^{L(L+1)/2}q^{\ell(\ell-1)/2}$. Finally $\sum_{\ell\ge0}q^{\ell(\ell-1)/2}\le1+(1-q)^{-1}$.
- *Numerics.* The worst case $K\sum|w_\ell|x_\ell^L$ is below the bound for every tested $\alpha$.
- *Vacuity.* If $K<0$ the hypothesis fails at $\ell=0$, which is harmless. The theorem is not vacuous: take $\alpha=L=1$, $E_\ell=EP+x_\ell+x_\ell^2$, $a_1=K=1$; the bias is $-1/2$.
- *Hypothesis.* The remainder is $Kx^L$ rather than the textbook $Kx^{L+1}$, which is a *weaker* hypothesis. The rate is the same because the $\ell=0$ term dominates.
- *Standard result.* This is the ML2R bias estimate of Lemaire–Pagès, bias $\approx c_R(h^R/\underline n!)^\alpha$ with $M=2$, $h=1$, $R=L+1$, $\underline n!=2^{L(L+1)/2}$. The rate is exactly right: $\sum_\ell w_\ell x_\ell^{L+1}=(-1)^L2^{-\alpha L(L+1)/2}$ (verified).

### 4. `ml2rEstimator` (def)

**Rendering.**
$$\hat Y_{L,N}(x)=\sum_{\ell=0}^{L}\frac1{N_\ell}\sum_{n<N_\ell}W^{(L)}_\ell\,\Delta P_\ell\big(\omega_{(\ell,n)}(x)\big).$$
The inner `ℓ` in the lambda is rebound, and `blockMean` applies it at the outer `ℓ`, so the reading is as intended.

**Assessment.** This is the Lemaire–Pagès ML2R estimator. $W_0=\sum_kw_k=1$, and by Abel summation $E\hat Y=\sum_\ell w_\ell E P_\ell$ (checked symbolically in `defs_check.out`). Different $(\ell,n)$ use distinct coordinates of ω.

### 5. `ml2r_theorem_eq` (theorem)

**Rendering.**
- *Setting.* $(\Omega,\mu)$ is a probability space. $\nu$ is a measure on $\Omega_0$. Each $\omega_p:\Omega\to\Omega_0$ ($p\in\mathbb N^2$) is measure-preserving from μ to ν, so ν is a probability measure. The family $(\omega_p)_p$ is mutually independent.
- *Levels.* Each $P_\ell$ is measurable and lies in $L^2(\nu)$.
- *Parameters.* $\alpha>0$, $\gamma>0$, $\beta=\gamma$, $c_2,c_3>0$, and $a,C:\mathbb N\to\mathbb R$.
- *(hexp)* For all $L$ and $\ell\le L$: $|E_\nu P_\ell-EP-\sum_{n=1}^La_nx_\ell^n|\le Kx_\ell^L$.
- *(hV)* $\operatorname{Var}_\nu(\Delta P_\ell)\le c_22^{-\beta\ell}$.
- *(hC)* $C_\ell\le c_32^{\gamma\ell}$.
- *Conclusion.* There is $c_4>0$, which may depend on all the data but not on ε, such that for every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N_{>0}$ with $E_\mu[(\hat Y_{L,N}-EP)^2]<\varepsilon^2$ and $\sum_{\ell=0}^LN_\ell C_\ell\le c_4\varepsilon^{-2}|\ln\varepsilon|$.

**Assessment.** **True.**
- *MSE decomposition.* The MSE is $\text{bias}^2+\sum_\ell W_\ell^2\operatorname{Var}(\Delta P_\ell)/N_\ell$, by independence and identical laws. Also $|W_\ell|\le\sum_k|w_k|\le c(\alpha)$.
- *Choice of $L$.* Take $L$ minimal with $C_{\rm b}K2^{-\alpha L(L+1)/2}\le\varepsilon/2$. Then $L\le\sqrt{2\log_2(1/\varepsilon)/\alpha}+c$.
- *Choice of $N$.* Take $N_\ell=\lceil2\varepsilon^{-2}|W_\ell|\sqrt{V_\ell/C_\ell}\,S\rceil$. The variance is then at most $\varepsilon^2/2$, and the cost is at most $2\varepsilon^{-2}S^2+\sum_\ell c_32^{\gamma\ell}$ with $S\asymp L+1$.
- *Cost.* This gives $\varepsilon^{-2}O(\log(1/\varepsilon))+2^{O(\sqrt{\log(1/\varepsilon)})}$.
- *Numerics* (`ml2r_complexity.out`, $\varepsilon$ down to $10^{-281}$): cost/bound stays bounded, while cost·ε² grows.
- *Vacuity.* Not vacuous. A point space with $P_\ell\equiv EP+2^{-\alpha\ell}$, $a_1=K=1$ works, and so does a random product-space example.
- *Junk.* None: everything is in $L^2$, and $|\ln\varepsilon|>1$.
- *Standard result.* This is the ML2R complexity theorem of Lemaire–Pagès (Bernoulli 2017, "Multilevel Richardson–Romberg extrapolation"; I do not recall the theorem number), case $\beta=\gamma$ (their $\beta=1$): $\varepsilon^{-2}\log(1/\varepsilon)$, against $\varepsilon^{-2}\log^2(1/\varepsilon)$ for MLMC.
- *Hypotheses.* `hexp` is strong (main point 2). `hγ` and `hPlm` are harmless extras.

### 6. `ml2r_theorem_lt` (theorem)

**Rendering.** Same as #5 but with $\beta<\gamma$ instead of $\beta=\gamma$. The cost bound becomes
$$\sum_{\ell\le L}N_\ell C_\ell\le c_4\,\varepsilon^{-2}\,2^{(\gamma-\beta)\sqrt{2\log_2(\varepsilon^{-1})/\alpha}}.$$

**Assessment.** **True.**
- *Proof.* Use the same construction as #5. Now $S\asymp2^{(\gamma-\beta)L/2}$, so the main cost is $\asymp\varepsilon^{-2}2^{(\gamma-\beta)L}\le c\,\varepsilon^{-2}2^{(\gamma-\beta)\sqrt{2\log_2(1/\varepsilon)/\alpha}}$. The rounding cost $\asymp2^{\gamma L}$ is at most $c\varepsilon^{-2}$, since $\gamma\sqrt{2x/\alpha}\le2x+\gamma^2/(4\alpha)$.
- *Range of β.* The theorem also holds for $\beta\le0$; only $\beta<\gamma$ is used.
- *Numerics.* Four parameter sets give a bounded ratio.
- *Vacuity and junk.* Not vacuous (same instances as #5, with $\beta<\gamma$). No junk: $\log_2\varepsilon^{-1}>0$.
- *Standard result.* This is Lemaire–Pagès' case $\beta<1$, cost $\varepsilon^{-2}e^{\frac{1-\beta}{\sqrt\alpha}\sqrt{2\ln M\ln(1/\varepsilon)}}$. It matches exactly for $M=2$ with $1\to\gamma$. The exponent $\sqrt{2\log_2(1/\varepsilon)/\alpha}$ is exactly the depth $L$ forced by the bias rate $2^{-\alpha L(L+1)/2}$ (main point 4).

### 7. `mimcEta` (def)

**Rendering.** For $D\ge1$: $\eta=\max_d(\gamma_d-\beta_d)/\alpha_d$, computed with `sup'` over the nonempty `Fin D`.

**Assessment.** This is Giles' η, and it equals $2\zeta$ in Haji-Ali–Nobile–Tempone's notation. Under the theorems' hypotheses $\alpha_d>0$, so there is no junk. Also $\eta>-2$.

### 8. `mimcD2` (def)

**Rendering.** $d_2=\#\{d:(\gamma_d-\beta_d)/\alpha_d=\eta\}$.

**Assessment.** $d_2\ge1$. This is HNT's $z$ and Giles' $d_2$. It is also the number of directions attaining $\min_d\alpha_d/\theta_d=2/(2+\eta)$ and $\max_d\frac{(\gamma_d-\beta_d)/2}{\theta_d}=\frac{\eta}{2+\eta}$.

### 9. `mimcD3` (def)

**Rendering.** $d_3=\#\{d:\alpha_d=\beta_d/2\}$, the number of boundary directions. It is declared outside the `NeZero` section.

**Assessment.** Faithful. It is also the number of directions with $\gamma_d=2\theta_d$.

### 10. `mimcBound` (def)

**Rendering.**
$$B(\eta,e_1,e_2;\varepsilon)=\begin{cases}\varepsilon^{-2}, & \eta<0,\\ \varepsilon^{-2}|\ln\varepsilon|^{e_1}, & \eta=0,\\ \varepsilon^{-2-\eta}|\ln\varepsilon|^{e_2}, & \eta>0.\end{cases}$$

**Assessment.** Faithful to the MLMC and MIMC case split. There is no junk on $(0,e^{-1})$.

### 11. `mimc_complexity_core_indexSet` (theorem)

**Rendering.**
- *Hypotheses.* $D\ge1$. For all $d$: $\alpha_d>0$, $\gamma_d>0$ and $\beta_d/2\le\alpha_d$, so $\theta_d\ge\gamma_d/2>0$. Also $c_1,c_2,c_3>0$. The real $c$ satisfies $\gamma_d\le c\theta_d$ for all $d$ (so $c>0$). The natural number $k$ satisfies $\#\{d:c\theta_d=\gamma_d\}\le k+1$.
- *Quantifiers.* There exist $K_M,K_X\ge0$, depending only on $(D,\alpha,\beta,\gamma,c_i,c,k)$, such that for every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb R$ and $N:\mathbb N^D\to\mathbb N_{>0}$ satisfying (i)–(iii) below.
- *(i) Bias.* $c_1\sum_{\ell\notin I(L)}2^{-\alpha\cdot\ell}\le\varepsilon/2$. The statement quantifies over all finite $s$ and sums over $s\setminus I(L)$, which is equivalent because the terms are positive.
- *(ii) Variance.* $\sum_{\ell\in I(L)}c_22^{-\beta\cdot\ell}/N_\ell\le\varepsilon^2/2$.
- *(iii) Cost.*
$$\sum_{\ell\in I(L)}N_\ell c_32^{\gamma\cdot\ell}\le K_M\,B\big(\eta,2d_2,(d_2-1)(2+\eta);\varepsilon\big)+K_X(-\ln\varepsilon)^{k+(d_2-1)c(2+\eta)/2}\varepsilon^{-c(2+\eta)/2}.$$

**Assessment.** **True.**
- *Bias.* Let $a=\min_d\alpha_d/\theta_d=2/(2+\eta)$. The tail is at most $C(L+1)^{d_2-1}2^{-aL}$. Choose $L=\tfrac{2+\eta}{2}\log_2\!\big(M\varepsilon^{-1}|\ln\varepsilon|^{d_2-1}\big)$, so that $2^L\asymp\varepsilon^{-(2+\eta)/2}|\ln\varepsilon|^{(d_2-1)(2+\eta)/2}$.
- *Lagrange part.* Use Lagrange-optimal $N$ rounded up. Then $S=\sum_I2^{(\gamma-\beta)\cdot\ell/2}$ is $\asymp2^{L\eta/(2+\eta)}L^{d_2-1}$ if $\eta>0$, $\asymp L^{d_2}$ if $\eta=0$, and $O(1)$ if $\eta<0$. This gives the $K_M$ term.
- *Rounding part.* $\sum_I2^{\gamma\cdot\ell}\le C2^{cL}(L+1)^{(\mathrm{crit}-1)_+}$, which gives the $K_X$ term.
- *Numerics.* `mimc_core_rounding.out` shows a bounded ratio in five settings, with tight $c$, slack $c$, boundary and strict cases.
- *Vacuity.* Not vacuous: $D=1$, $\alpha=\beta=\gamma=1$, $c=2$, $k=0$.
- *Junk.* None: for $\theta>0$ the box in `indexSet` is exact, and $N>0$.

### 12. `mimc_complexity_indexSet` (theorem)

**Rendering.** Hypotheses as in #11 but with $\beta_d/2<\alpha_d$ strict, and without $c$ and $k$. Conclusion: there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N>0$ satisfying (i) and (ii), and the cost is at most $c_4B(\eta,2d_2,(d_2-1)(2+\eta);\varepsilon)$.

**Assessment.** **True.**
- *Proof.* Apply #11 with $c=\max_d\gamma_d/\theta_d<2$ (strict inequality is equivalent to $\gamma_d<2\theta_d$) and $k=D$. The $K_X$ term is $\varepsilon^{-c(2+\eta)/2}\cdot\text{polylog}$ with $c(2+\eta)/2<2+\eta$, and $<2$ when $\eta<0$, so it is absorbed.
- *Numerics* (`mimc_complexity.out`, cases F, G, H, M, N): the ratio stays bounded.
- *Vacuity and junk.* Not vacuous: $D=1$, $\alpha=\beta=\gamma=1$, $c_i=1$ satisfies the hypotheses. No junk.
- *Standard result.* This is the MIMC complexity theorem of Haji-Ali–Nobile–Tempone (Numer. Math. 2016; Thm 2.2 as I recall the numbering) for their optimal total-degree set. With $\zeta=\eta/2$ and $z=d_2$, it reads: $\varepsilon^{-2}$; $\varepsilon^{-2}\log^{2z}$; $\varepsilon^{-2(1+\zeta)}\log^{2(z-1)(1+\zeta)}$.
- *Index set.* $\theta_d=\alpha_d+(\gamma_d-\beta_d)/2$ gives the natural index set: the profit of index $\ell$ is $2^{-\alpha\cdot\ell}/\sqrt{V_\ell C_\ell}\propto2^{-\theta\cdot\ell}$.

### 13. `mimc_complexity_boundary_indexSet` (theorem)

**Rendering.** As #12 but with $\beta_d/2\le\alpha_d$, and with the cost bounded by
$$c_4\,B\big(\eta,\;2d_2+(d_3-3)_+,\;(d_2-1)(2+\eta)+(d_3-1)_+;\varepsilon\big),$$
where the ℕ-subtraction is truncated.

**Assessment.** **True.**
- *Proof.* Apply #11 with $c=2$ (valid because $\beta_d\le2\alpha_d$), $\mathrm{crit}=d_3$ and $k=(d_3-1)_+$. The $K_X$ term becomes $(-\ln\varepsilon)^{(d_3-1)_++(d_2-1)(2+\eta)}\varepsilon^{-(2+\eta)}$.
  - If $\eta>0$, this equals the claimed term.
  - If $\eta=0$, it is covered because $2d_2-2+(d_3-1)_+\le2d_2+(d_3-3)_+$.
  - If $\eta<0$, then $\varepsilon^{-(2+\eta)}\cdot\text{polylog}\le C\varepsilon^{-2}$.
- *Sharpness.* The exponents are sharp for this index set, and the $(\cdot)_+$ is exactly the intended $\max(0,\cdot)$ (main point 3).
- *Numerics.* Cases A–E, I, J and K in `mimc_complexity.out`, and `mimc_boundary_split.out`, agree.
- *Vacuity and junk.* Not vacuous: $D=1$, $\alpha=1$, $\beta=\gamma=2$ is a boundary instance. No junk.
- *Standard result.* This is the boundary case $\alpha_d\ge\beta_d/2$ of Giles' Acta Numerica (2015) MIMC Theorem 2. I cannot reproduce Giles' printed boundary exponents from memory. The packet's exponents agree with my independent derivation.

### 14. `giles_theorem2_indexSet` (theorem)

**Rendering.** Assume $\mu$ is a probability measure on Ω, subject to main point 1. The data are:
- $P$ and each $P_\ell$ are integrable.
- $Y_{\ell,n}\in L^2$ for $n>0$.
- For every $N>0$, the family $(Y_{\ell,N_\ell})_\ell$ is pairwise independent.
- $\mathrm{Cost}_{\ell,n}$ is integrable with $E\,\mathrm{Cost}_{\ell,n}=nC_\ell$.
- $\operatorname{Var}Y_{\ell,n}=V_\ell/n$.
- (i) $E[P_\ell-P]\to0$ as $\min_d\ell_d\to\infty$.
- (iii) $E Y_{\ell,n}=E[\text{crossDiff}\,P](\ell)$, the mixed difference.
- (ii) $|EY_{\ell,n}|\le c_12^{-\alpha\cdot\ell}$.
- (iv) $V_\ell\le c_22^{-\beta\cdot\ell}$.
- (v) $C_\ell\le c_32^{\gamma\cdot\ell}$.
- $\alpha_d,\beta_d,\gamma_d>0$, $\beta_d/2<\alpha_d$, and $c_i>0$.

Conclusion: there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $L\in\mathbb R$ and $N>0$ with
$$E\Big[\Big(\sum_{\ell\in I(L)}Y_{\ell,N_\ell}-EP\Big)^2\Big]<\varepsilon^2\quad\text{and}\quad E\sum_{\ell\in I(L)}\mathrm{Cost}_{\ell,N_\ell}\le c_4B(\eta,2d_2,(d_2-1)(2+\eta);\varepsilon).$$

**Assessment.** **True.**
- *Bias.* $EP=\sum_{\ell\in\mathbb N^D}E\Delta P_\ell$, using telescoping over boxes, (i), and absolute summability from (ii)+(iii). Hence $|\text{bias}|\le c_1\sum_{\ell\notin I}2^{-\alpha\cdot\ell}\le\varepsilon/2$ by #12(i).
- *Variance.* Pairwise independence gives variance $\sum_IV_\ell/N_\ell\le\varepsilon^2/2$. So the MSE is at most $3\varepsilon^2/4<\varepsilon^2$.
- *Cost.* $\sum N_\ell C_\ell\le\sum N_\ell c_32^{\gamma\cdot\ell}$.
- *Without a probability measure.* The theorem remains true if the probability-measure assumption is absent (main point 1).
- *Vacuity.* Not vacuous: the trivial instance $P=P_\ell=Y=0$, $V=0$, $\mathrm{Cost}_{\ell,n}\equiv nC_\ell$ satisfies all hypotheses, and so does any genuine MIMC setup.
- *Junk.* None: all integrands are integrable.
- *Hypotheses.* `_hβ` is unused. `h_ii` is required for every $n$, which is redundant given `h_iii`.
- *Standard result.* This is Giles (2015) Theorem 2 / Haji-Ali–Nobile–Tempone (2016) Theorem 2.2 with the explicit total-degree index set.

### 15. `giles_theorem2_boundary_indexSet` (theorem)

**Rendering.** As #14 but with $\beta_d/2\le\alpha_d$ and the boundary bound of #13.

**Assessment.** **True**, by the same reduction applied to #13. The scoping remark of main point 1 also applies. Not vacuous: the trivial instance of #14 works with boundary parameters. No junk.

### 16. `levelDiff` (def, appended)

**Rendering.** $\Delta P_0=P_0$ and $\Delta P_{\ell+1}=P_{\ell+1}-P_\ell$.

**Assessment.** Standard.

### 17. `blockMean` (def, appended)

**Rendering.** $\frac1N\sum_{n<N}f_i(\omega_{(i,n)}(x))$.

**Assessment.** $N=0$ gives the junk value 0, but it is always excluded by $N_\ell>0$.

### 18. `crossDiff` (def, appended)

**Rendering.** The mixed first backward difference with zero padding:
$$\text{crossDiff}\,p\,\ell=\sum_{j\in\{0,1\}^D,\ j\le\ell}(-1)^{|j|}\,p(\ell-j).$$

**Assessment.** Verified symbolically for $D\le3$, including the telescoping identity $\sum_{0\le\ell\le m}\text{crossDiff}\,p\,\ell=p(m)$ (`defs_check.out`).

### 19. `dot` (def, appended)

**Rendering.** $a\cdot\ell=\sum_da_d\ell_d$.

**Assessment.** Standard.

### 20. `crit` (def, appended)

**Rendering.** $\#\{d:\delta_d=0\}$.

**Assessment.** Standard.

### 21. `indexSet` (def, appended)

**Rendering.** The box $\prod_d\{0,\dots,\lfloor L/\theta_d\rfloor_+\}$, filtered by $\theta\cdot\ell\le L$.

**Assessment.** For $\theta_d>0$ this equals $\{\ell\in\mathbb N^D:\theta\cdot\ell\le L\}$, and it is empty when $L<0$ (300 random rational tests). Every use has $\theta_d\ge\gamma_d/2>0$.

### 22. `ml2rNode` (def, appended)

**Rendering.** $x_\ell=2^{-\alpha\ell}$.

**Assessment.** Standard.

### 23. `ml2rWeight` (def, appended)

**Rendering.** $w^{(L)}_\ell=\prod_{k\le L,\,k\ne\ell}x_k/(x_k-x_\ell)$, the Lagrange weight at 0.

**Assessment.** These are the Richardson–Romberg weights. The moment conditions are checked in `ml2r_weights.out`; for example, for $\alpha=1$, $L=4$ the weights are $(1/315,-2/21,8/9,-64/21,1024/315)$.
