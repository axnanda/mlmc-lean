# Blind read-back report: packet M4 (Haas–Giles remarks)

| field | value |
|---|---|
| date | 2026-09-29 |
| packet | `readback/round11/packet_M4_haas_giles_remarks.lean` |
| declarations audited | 16 (the section `recursion` is empty) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round11/work_M4/` (`cost_factor_check.py`, `gbm_moments_check.py`, `rounding_variance_check.py`, `strong_error_check.py`, `compare_statements.py`, each with a `.out`; Lean scratch files `packet_scratch.lean`, `checks_tail.lean`, and the elaborated statements `packet_statements.txt`, `real_statements.txt`) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `levelCost34_eq_mul_costFactor` | theorem | true | no | no |
| 2 | `nestedCost_le_of_costFactor_le` | theorem | true | no | no (trivial $0\le0$ at $\varepsilon=0$ via $0^{-1}=0$, harmless) |
| 3 | `nestedCost_lt_of_costFactor_le` | theorem | true | no | no |
| 4 | `exists_costFactor_lt_one_nestedCost_gt` | theorem (∃) | true | no | no |
| 5 | `integral_sq_mul1_sum1_eq` | theorem | true | no | no |
| 6 | `integral_sq_mul1_sum1_bounds` | theorem | true | no | no |
| 7 | `integral_gbmPath_eq` | theorem | true | no | no |
| 8 | `integral_sq_gbmPath_mul2_eq_pow` | theorem | true | no | no |
| 9 | `gbmPath_size_bounds` | theorem | true (full statement recovered; **packet truncated**) | no | no |
| 10 | `integral_sq_mul2_bounds` | theorem | true | no | no |
| 11 | `gbmPath_sq_largest` | theorem | true | no | no |
| 12 | `variance_linearised_indep_eq` | theorem | true | no | no |
| 13 | `variance_linearised_indep_ge` | theorem | true | no | no |
| 14 | `perturbed_path_sub_mean_variance` | theorem | true | no | no |
| 15 | `integral_sq_perturbed_path_sub_bounds` | theorem | true | no | no |
| 16 | `strongError_lt_integral_sq_perturbed_path_sub` | theorem | true | no | no |

## Main points for a human auditor

1. **Packet defect (#9).** In the packet, the statement of `gbmPath_size_bounds` is cut off after its first conjunct (`… ∧ := sorry`, which does not parse). Three of its four conjuncts were missing. I recovered the full statement without reading any source: I piped the module plus my own `#check` commands into one `lake env lean --stdin` process, discarded all other output unseen, and confirmed that the module produced no warnings or errors. I then compared statements mechanically (`compare_statements.out`): the other 15 statements are verbatim identical to the packet. All four conjuncts of #9 are true.
2. **Cost factor $\rho<1$ vs savings (#2–#4).** Here $\rho_\ell=\sqrt{C_{t,\ell}/C_\ell}+\sqrt{V_{d,\ell}/V_\ell}$. $\rho<1$ implies a saving only in the cost model where the correction estimator costs $C_\ell$ (form (a)). When it is charged $C_\ell+C_{t,\ell}$ (form (b), the realistic one), $\rho<1$ is not enough. #4's witness has factor $0.99$ yet costs $1.098\times$ standard MLMC. The sufficient condition proved in #3, $\rho^2(1+\rho^2)<1$ (i.e. $\rho<0.786$), is correct but not sharp: for a uniform per-level bound the sharp threshold is $\rho\approx0.943$. Both nested cost formulas also idealise the variance of the approximate-sample level estimator as $V_\ell$.
3. **Strong hypothesis in #12/#13.** `hind` requires the *products* $\bar x_i\delta_i$ to be pairwise independent. That is stronger than needed and fails in the natural case: correlated exact values $\bar x_i$ multiplied by independent, centred rounding errors. That case already gives zero covariances, and the variance formula stays true. This is not a truth problem, but it limits how widely the lemma applies. The path result #14 does not use it and is proved from a different, weaker model.
4. **Rounding model (#14–#16).** Rounding errors are modelled as uniform "half-ulp" absolute errors on $[-2^{e-d-1},2^{e-d-1}]$ with one fixed exponent. They are independent across steps; within a step, dependence on $Z_k$ is allowed. This is a modelling assumption, not derived from real fixed-point rounding (which depends on the state being rounded).
5. **#16 rests on the Euler–Maruyama (EM) strong-error constant `gbmStrongConst`.** I computed the exact EM mean-square error for GBM in closed form (checked by quadrature). Over broad scans it is at most $\approx0.095\cdot$`gbmStrongConst`$\cdot h$, and analytically $<\tfrac1{10}$ of it when $r=0$. So the hypothesis `hsmall` is a valid, conservative sufficient condition, and the conclusion is true. #16 correctly omits $h\le1$ and $E Z^2\le1$, which the lower bound it uses does not need.
6. **Minor.** In #2, $(\varepsilon^2)^{-1}$ is a common factor, so $\varepsilon=0$ gives $0\le0$. Negative $V_d$ is sent to $0$ on both sides consistently by $\sqrt{\cdot}$. `hCt` is unnecessary there. In #6/#10, $m$ may be negative, which makes the lower bounds trivial. In #11, `hsmall` forces $s_0\neq0$.

Notation used below: $\hat S_n:=$ `gbmPath r σ h s₀ Z n`. By `gbmStep`, $\hat S_{i+1}=\hat S_i+\hat S_i\,(rh+\sqrt h\,\sigma Z_i)$, so $\hat S_n=s_0\prod_{j<n}A_j$ with $A_j:=1+rh+\sqrt h\,\sigma Z_j$. Here $\sqrt{\cdot}$ is `Real.sqrt` ($=0$ on negatives). The intermediate variables are $\mathrm{mul1}_i=\sqrt h\sigma Z_i$, $\mathrm{sum1}_i=rh+\mathrm{mul1}_i$ and $\mathrm{mul2}_i=\hat S_i\,\mathrm{sum1}_i$. $v_j:=E[Z_j^2]$. In #5–#16, $(\Omega,\mu)$ is a probability space. All `n * h`, `i * h` are real products with $n,i\in\mathbb N$ cast to $\mathbb R$. All exponents `e - d - 1`, `e - d` are integers ($d$ cast to $\mathbb Z$; `zpow`, no ℕ-subtraction), which I confirmed by elaboration. `-(2:ℝ)^k` parses as $-(2^k)$ (checked by `rfl`), so the uniform intervals are symmetric. `pdf.IsUniform X s μ ℙ` means `map X μ = cond volume s`, i.e. the law of $X$ is the normalised Lebesgue measure on $s$. Since $s$ has positive finite length here, this also forces $X$ to be AE-measurable.

---

## 1. `levelCost34_eq_mul_costFactor`

**Rendering.** For real $V,V_d,C,C_t$ with $V>0$ and $C>0$ (no sign condition on $V_d,C_t$):
$\sqrt{VC_t}+\sqrt{V_dC}=\sqrt{VC}\,\bigl(\sqrt{C_t/C}+\sqrt{V_d/V}\bigr)$.

**Assessment.** True. Since $VC\ge0$, `Real.sqrt_mul` gives $\sqrt{VC}\sqrt{C_t/C}=\sqrt{VC\cdot C_t/C}=\sqrt{VC_t}$, and likewise $\sqrt{VC}\sqrt{V_d/V}=\sqrt{V_dC}$. If $C_t<0$ or $V_d<0$, the corresponding terms are $0$ on both sides. Checked at 20000 random points, including negative $C_t,V_d$ (max relative difference $4\cdot10^{-41}$). Not vacuous: $V=C=1$, $C_t=V_d=\tfrac14$. Junk values: none. The meaningful case $C_t,V_d\ge0$ does not use the convention, and negative arguments give $0=0$ consistently. Both hypotheses are needed: $C=0$, $V=C_t=V_d=1$ gives LHS $1$ and RHS $0$. Standard fact: the per-level "cost factor" identity of nested MLMC with approximate random variables, $\sqrt{V_\ell\tilde C_\ell}+\sqrt{\hat V_\ell C_\ell}=\sqrt{V_\ell C_\ell}\,\rho_\ell$ (Giles–Sheridan-Methven type).

## 2. `nestedCost_le_of_costFactor_le`

**Rendering.** Take $L\in\mathbb N$, sequences $V,V_d,C,C_t:\mathbb N\to\mathbb R$ and reals $\varepsilon,\rho$. Suppose that for all $\ell\le L$: $V_\ell>0$, $C_\ell>0$, $C_{t,\ell}\ge0$ and $\sqrt{C_{t,\ell}/C_\ell}+\sqrt{V_{d,\ell}/V_\ell}\le\rho$. Let $K:=(\varepsilon^2)^{-1}\bigl(\sum_{\ell=0}^{L}\sqrt{V_\ell C_\ell}\bigr)^2$ (Lean: $=0$ if $\varepsilon=0$). Then
(a) $(\varepsilon^2)^{-1}\bigl(\sum_{\ell\le L}(\sqrt{V_\ell C_{t,\ell}}+\sqrt{V_{d,\ell}C_\ell})\bigr)^2\le\rho^2K$;
(b) $(\varepsilon^2)^{-1}\bigl(\sum_{\ell\le L}(\sqrt{V_\ell C_{t,\ell}}+\sqrt{V_{d,\ell}(C_\ell+C_{t,\ell})})\bigr)^2\le\rho^2(1+\rho^2)K$.

**Assessment.** True. Because $\mathrm{range}(L+1)\ne\emptyset$, $\rho\ge0$. By #1, each summand in (a) is $\sqrt{V_\ell C_\ell}\,\rho_\ell\le\rho\sqrt{V_\ell C_\ell}$; sum, square (both sides $\ge0$) and multiply by $(\varepsilon^2)^{-1}\ge0$. For (b), $C_t/C\le\rho^2$ gives $\sqrt{V_d(C+C_t)}\le\sqrt{1+\rho^2}\sqrt{V_dC}$, and trivially $\sqrt{VC_t}\le\sqrt{1+\rho^2}\sqrt{VC_t}$. Random tests: 20000 cases, 0 violations. Not vacuous: $L=0$, $V=C=1$, $C_t=V_d=0.01$, $\rho=0.2$, $\varepsilon=0.1$. Junk values: at $\varepsilon=0$ both sides are $0$ ($0^{-1}=0$), which is harmless. The statement is meaningful and true for $\varepsilon\ne0$. Negative $V_d$ becomes $0$ consistently on both sides. `hCt` is not really needed. Standard fact: the optimal MLMC cost $\varepsilon^{-2}(\sum_\ell\sqrt{V_\ell C_\ell})^2$ (Giles) compared with the nested-MLMC cost. Form (b) charges the correction estimator $C_\ell+C_{t,\ell}$. Modelling note: the approximate-level variance is taken equal to $V_\ell$, and costs are the idealised optimal-allocation costs.

## 3. `nestedCost_lt_of_costFactor_le`

**Rendering.** Same data and hypotheses as #2, plus $\varepsilon\ne0$. Then (i) if $\rho<1$, the nested cost (a) is strictly less than the standard cost $K$; and (ii) if $\rho^2(1+\rho^2)<1$, the nested cost (b) is strictly less than $K$.

**Assessment.** True. $K>0$ because $\varepsilon\ne0$, $V_\ell,C_\ell>0$ and there is at least one term. With $0\le\rho<1$ we get $\rho^2<1$, so (a) $\le\rho^2K<K$; similarly (b) $\le\rho^2(1+\rho^2)K<K$. Random tests: 0 violations (4836 cases with $\rho<1$, 3625 with $\rho^2(1+\rho^2)<1$). Not vacuous. No junk values. Remark: (ii)'s condition means $\rho<\sqrt{(\sqrt5-1)/2}\approx0.786$. It is sufficient but not necessary: for a uniform per-level bound, the sharp condition is $\sup_{t+u\le\rho}\,t+u\sqrt{1+t^2}<1$, i.e. $\rho\lesssim0.943$ (`cost_factor_check.out`).

## 4. `exists_costFactor_lt_one_nestedCost_gt`

**Rendering.** There exist sequences $V,V_d,C,C_t:\mathbb N\to\mathbb R$, the same for all $L$ and $\varepsilon$, with the following properties. For every $\ell$: $V_\ell>0$, $C_\ell>0$, $V_{d,\ell}\ge0$, $C_{t,\ell}\ge0$ and $\sqrt{C_{t,\ell}/C_\ell}+\sqrt{V_{d,\ell}/V_\ell}<1$. And for every $L\in\mathbb N$ and every real $\varepsilon\ne0$, the standard cost $(\varepsilon^2)^{-1}(\sum_{\ell\le L}\sqrt{V_\ell C_\ell})^2$ is strictly less than the nested cost (b).

**Assessment.** True. Witness: constant sequences $V=C=1$, $C_t=\tfrac14$, $V_d=0.49^2$. The cost factor is $0.5+0.49=0.99<1$. Each (b)-summand is $0.5+0.49\sqrt{1.25}=1.0478>1=\sqrt{VC}$, so nested(b) $=1.098\,K>K$ for all $L$ and all $\varepsilon\ne0$ (checked for several $L,\varepsilon$). Not vacuous: it is an existence statement with an explicit witness. No junk values ($\varepsilon\ne0$). Meaning: in cost model (b), a cost factor below 1 does **not** guarantee savings. This justifies the extra hypothesis in #3(ii).

## 5. `integral_sq_mul1_sum1_eq`

**Rendering.** Let $Y\in L^2(\mu)$ with $E[Y]=0$, let $r,\sigma\in\mathbb R$ and $h\ge0$. Then $E[(\sqrt h\sigma Y)^2]=\sigma^2hE[Y^2]$ and $E[(rh+\sqrt h\sigma Y)^2]=r^2h^2+\sigma^2hE[Y^2]$.

**Assessment.** True: $(\sqrt h)^2=h$ for $h\ge0$, the cross term $2rh\sqrt h\sigma E[Y]$ vanishes, and $Y,Y^2$ are integrable. Not vacuous: $Y=\pm1$ with probability $\tfrac12$ each. No junk values. $h\ge0$ is necessary: for $h<0$, $\sqrt h=0$ and the first identity fails. Standard fact: second moment of an affine function of a centred variable (the `mul1`, `sum1` variables of `gbmStep`).

## 6. `integral_sq_mul1_sum1_bounds`

**Rendering.** Same setting as #5, with additionally $m\le E[Y^2]\le1$ ($m\in\mathbb R$) and $0\le h\le1$. Then $m\sigma^2h\le E[\mathrm{mul1}^2]\le\sigma^2h$ and $m\sigma^2h\le E[\mathrm{sum1}^2]\le(r^2+\sigma^2)h$.

**Assessment.** True: immediate from #5, using $r^2h^2\ge0$ and $h^2\le h$. Random tests: 0 violations. Not vacuous: $m=1$, $Y=\pm1$. No junk values. A negative $m$ makes the lower bounds trivial, which is harmless.

## 7. `integral_gbmPath_eq`

**Rendering.** Let $(Z_i)_{i\in\mathbb N}$ be mutually independent (`iIndepFun`), measurable, integrable, with $E[Z_i]=0$. Then for all real $r,\sigma,h,s_0$ and all $n\in\mathbb N$: $E[\hat S_n]=s_0(1+rh)^n$.

**Assessment.** True: $\hat S_n=s_0\prod_{j<n}A_j$ with independent integrable factors, so $E[\hat S_n]=s_0\prod E[A_j]=s_0(1+rh)^n$. No sign condition on $h$ is needed: $h<0$ gives $\sqrt h=0$, still consistent. Checked by exact enumeration with two- and three-point centred laws (relative error $<10^{-39}$). Not vacuous: iid $N(0,1)$. No junk values. Standard fact: the mean of the Euler–Maruyama GBM path.

## 8. `integral_sq_gbmPath_mul2_eq_pow`

**Rendering.** Same as #7, but with $Z_i\in L^2$, $E[Z_i]=0$ and $E[Z_i^2]=v$ for all $i$, and $h\ge0$. For all $r,\sigma,s_0$ and $i$: $E[\hat S_i^2]=s_0^2\bigl((1+rh)^2+\sigma^2hv\bigr)^i$ and $E[\mathrm{mul2}_i^2]=E[(\hat S_i(rh+\sqrt h\sigma Z_i))^2]=s_0^2\bigl((1+rh)^2+\sigma^2hv\bigr)^i(r^2h^2+\sigma^2hv)$.

**Assessment.** True. $E[A_j^2]=(1+rh)^2+\sigma^2hv$, and $\hat S_i$ is a function of $Z_0,\dots,Z_{i-1}$, hence independent of $Z_i$. Confirmed by exact enumeration. Not vacuous: iid $N(0,1)$, $v=1$. No junk values. Standard fact: the mean-square growth factor of EM for GBM.

## 9. `gbmPath_size_bounds` (packet truncated; full statement recovered)

**Rendering.** Suppose $(Z_i)$ are mutually independent, measurable and in $L^2$, with $E[Z_i]=0$ and $E[Z_i^2]\le1$. Suppose $0\le h\le1$, $|r|h\le\tfrac12$, and $n\in\mathbb N$ with $nh\le T$. Then, for all $s_0,\sigma$:
$|s_0|e^{-2|r|T}\le|E\hat S_n|\ \wedge\ |E\hat S_n|\le|s_0|e^{|r|T}\ \wedge\ s_0^2e^{-4|r|T}\le E[\hat S_n^2]\ \wedge\ E[\hat S_n^2]\le s_0^2e^{(2|r|+r^2+\sigma^2)T}$.
(The packet shows only the first conjunct followed by `∧ := sorry`. The other three come from `#check` on the real declaration.)

**Assessment.** True. By #7, $E\hat S_n=s_0(1+rh)^n$, and $e^{-2|r|h}\le1-|r|h\le|1+rh|\le1+|r|h\le e^{|r|h}$; the first inequality holds on $|r|h\le\tfrac12$ (min over the grid $\ge0$). Also $E\hat S_n^2=s_0^2\prod_{j<n}((1+rh)^2+\sigma^2hv_j)$ with $v_j\in[0,1]$, and each factor lies in $[e^{-4|r|h},e^{(2|r|+r^2+\sigma^2)h}]$ (using $h^2\le h$). Finally use $nh\le T$. Random tests: 40000 cases, 0 violations. Not vacuous. No junk values.

## 10. `integral_sq_mul2_bounds`

**Rendering.** Hypotheses of #9, plus $m\le E[Z_i^2]$ for all $i$. For $i\in\mathbb N$ with $ih\le T$:
$s_0^2e^{-4|r|T}\,(m\sigma^2h)\le E[\mathrm{mul2}_i^2]\le s_0^2e^{(2|r|+r^2+\sigma^2)T}(r^2+\sigma^2)h$.

**Assessment.** True: $E[\mathrm{mul2}_i^2]=s_0^2\prod_{j<i}((1+rh)^2+\sigma^2hv_j)\cdot(r^2h^2+\sigma^2hv_i)$, and the factors are bounded as in #9 and #6. Random tests: 0 violations. Not vacuous. No junk values. A negative $m$ makes the lower bound trivial.

## 11. `gbmPath_sq_largest`

**Rendering.** Hypotheses of #9, plus $i,n\in\mathbb N$ with $ih\le T$, $nh\le T$, and
`hsmall`: $(r^2+\sigma^2)\bigl(1+s_0^2e^{(2|r|+r^2+\sigma^2)T}\bigr)h<s_0^2e^{-4|r|T}$.
Then each of $(rh)^2$, $(\sqrt h\sigma)^2$, $E[\mathrm{mul1}_i^2]$, $E[\mathrm{sum1}_i^2]$ and $E[\mathrm{mul2}_i^2]$ is strictly less than $E[\hat S_n^2]$.

**Assessment.** True. The first four quantities are $\le(r^2+\sigma^2)h$, by #6 with $h^2\le h$. The last is $\le s_0^2e^{(2|r|+r^2+\sigma^2)T}(r^2+\sigma^2)h$ by #10. Both are $\le$ the LHS of `hsmall`, which is $<s_0^2e^{-4|r|T}\le E\hat S_n^2$ by #9. `hsmall` forces $s_0\ne0$. Random tests: 9257 cases satisfying `hsmall`, 0 violations. Not vacuous: $r=0$, $\sigma=1$, $s_0=1$, $T=1$, $h=0.01$, $i=n=100$ (LHS $0.037<1$). No junk values. Meaning: a range analysis for fixed point, showing every intermediate variable is smaller in RMS than the state.

## 12. `variance_linearised_indep_eq`

**Rendering.** Let $s$ be a finite index set, with $\bar x_i,\delta_i:\Omega\to\mathbb R$, $e_i\in\mathbb Z$ and $d_i\in\mathbb N$. Suppose that for $i\in s$: $\bar x_i\in L^2$; $\delta_i$ is uniform on $[-2^{e_i-d_i-1},2^{e_i-d_i-1}]$ (integer exponent, reference measure Lebesgue); and $\bar x_i$ is independent of $\delta_i$. Suppose also that for $i\ne j$ in $s$, $\bar x_i\delta_i$ is independent of $\bar x_j\delta_j$. Then $\mathrm{Var}\bigl(\sum_{i\in s}\bar x_i\delta_i\bigr)=\frac1{12}\sum_{i\in s}E[\bar x_i^2]\,4^{e_i-d_i}$ (Mathlib `variance`).

**Assessment.** True. We have $E\delta_i=0$ and $E\delta_i^2=(2^{e_i-d_i-1})^2/3=4^{e_i-d_i}/12$ (sympy, symbolic in $k$). Also $\bar x_i\delta_i\in L^2$ with mean $0$ and variance $E\bar x_i^2E\delta_i^2$. Pairwise independent $L^2$ terms are uncorrelated, so the variances add. Not vacuous: independent $\bar x_0,\bar x_1,\delta_0,\delta_1$ on a product space. No junk values: the sum is in $L^2$, so `variance` is the true variance. **Suspicious (too strong) hypothesis:** `hind` (pairwise independence of the *products*) is stronger than needed. It fails for correlated $\bar x_i$ (e.g. $\bar x_0=\bar x_1=X$) times independent centred $\delta_i$, even though the covariances are still $0$ and the formula still holds. Standard fact: the uniform quantisation-noise model, variance $\Delta^2/12$ with $\Delta=2^{e-d}$, plus additivity of variances.

## 13. `variance_linearised_indep_ge`

**Rendering.** As in #12, but with a common $e\in\mathbb Z$, $d\in\mathbb N$ and a real $c$ with $c\le E[\bar x_i^2]$ for $i\in s$. Then $|s|\,c\,4^{e-d}/12\le\mathrm{Var}\bigl(\sum_{i\in s}\bar x_i\delta_i\bigr)$.

**Assessment.** True: immediate from #12. Not vacuous. No junk values. `hind` has the same over-strength as in #12.

## 14. `perturbed_path_sub_mean_variance`

**Rendering.** Let $Z,\rho:\mathbb N\to\Omega\to\mathbb R$ be such that the pairs $W_k=(Z_k,\rho_k)$ are mutually independent across $k$ (dependence within a pair is allowed). Each $Z_k$ and $\rho_k$ is measurable, $Z_k\in L^2$, and each $\rho_k$ is uniform on $[-2^{e-d-1},2^{e-d-1}]$. Let $r,\sigma,h,s_0\in\mathbb R$ be arbitrary. Let $St$ satisfy, pointwise, $St_0=s_0$ and $St_{k+1}=St_k\,A_k+\rho_k$. Then for every $n$: $E[St_n-\hat S_n]=0$ and $\mathrm{Var}(St_n-\hat S_n)=\frac{4^{e-d}}{12}\sum_{k<n}E\Bigl[\bigl(\prod_{j=k+1}^{n-1}A_j\bigr)^2\Bigr]$.

**Assessment.** True. $D_n:=St_n-\hat S_n=\sum_{k<n}\rho_kP_k$ with $P_k=\prod_{k<j<n}A_j$. The factor $\rho_k$ is independent of everything with index $>k$ and has mean $0$. So $E[\rho_kP_k]=0$ and, for $k<l$, $E[\rho_kP_k\rho_lP_l]=0$. Also $E[\rho_k^2P_k^2]=E\rho_k^2\,E P_k^2$, and everything needed is integrable. No $E Z=0$ and no $h\ge0$ is needed. An exact sympy computation with $n\le3$, deliberately *dependent* pairs ($\rho_k=aU_k$, $Z_k=\sqrt3U_k+\mu$) and $\mu\ne0$ gives $E D_n=0$ and Var $-$ formula $=0$. Not vacuous: $Z\equiv0$ and iid uniforms $\rho_k$ on $(\mathbb N\to\mathbb R)$ with `infinitePi`. No junk values: $D_n\in L^2$. Modelling note: rounding is an independent uniform additive error with a fixed exponent. Standard fact: propagation of additive noise through a linear random recursion (orthogonality of increments).

## 15. `integral_sq_perturbed_path_sub_bounds`

**Rendering.** Hypotheses of #14, plus $E Z_k=0$, $E Z_k^2\le1$, $0\le h\le1$, $|r|h\le\tfrac12$ and $nh\le T$. Then
$n\frac{4^{e-d}}{12}e^{-4|r|T}\le E[(St_n-\hat S_n)^2]\le n\frac{4^{e-d}}{12}e^{(2|r|+r^2+\sigma^2)T}$.

**Assessment.** True. Since the mean is $0$, $E D_n^2=\mathrm{Var}$ from #14, with $E P_k^2=\prod_{k<j<n}((1+rh)^2+\sigma^2hv_j)$. Each factor lies in $[e^{-4|r|h},e^{(2|r|+r^2+\sigma^2)h}]$, there are at most $n-1$ factors, and $nh\le T$. There are $n$ summands. A spot check with an exact example passes. Not vacuous. No junk values. For $n=0$ it reads $0\le0\le0$.

## 16. `strongError_lt_integral_sq_perturbed_path_sub`

**Rendering.** Hypotheses of #14 plus $E Z_k=0$; $h>0$, $|r|h\le\tfrac12$, $n\in\mathbb N$ with $nh=T$; and
`hsmall`: $G\,h^2<T\,\frac{4^{e-d}}{12}\,e^{-4|r|T}$, where $G=$ `gbmStrongConst r σ T s₀` $=s_0^2e^{(2|r|+\sigma^2)T}(|r|+\sigma^2)\bigl(5(|r|+\sigma^2)T+4\bigr)$.
Then
$\displaystyle\int\Bigl(s_0e^{(r-\sigma^2/2)T+\sigma\sqrt h\sum_{i<n}z_i}-\hat S_n(z)\Bigr)^2\,d\,\mathcal N(0,1)^{\otimes\mathbb N}(z)\;<\;E_\mu[(St_n-\hat S_n)^2]$.
In words: the mean-square error of exact-arithmetic EM against exact GBM, driven by the same Brownian increments $\sqrt h z_i$, is strictly smaller than the mean-square accumulated rounding error.

**Assessment.** True. The lower bound of #15 needs only $v_j\ge0$, not $h\le1$ or $v_j\le1$, and gives $E D_n^2\ge nq e^{-4|r|T}$ with $q=4^{e-d}/12$. The exact EM error is $\mathrm{MSE}=s_0^2\bigl[e^{(2r+\sigma^2)T}-2e^{rT}(1+(r+\sigma^2)h)^n+((1+rh)^2+\sigma^2h)^n\bigr]$, which I checked by quadrature for $n=1,2$. Scans over $r\in[-200,200]$, $\sigma\le10$ (random search up to $\approx60$), $T\le47$, $n\le10^4$, plus random search with refinement, give $\max\mathrm{MSE}/(Gh)\approx0.095$. For $r=0$ it is analytically $\le\frac{nb}{2(5nb+4)}<\frac1{10}$ with $b=\sigma^2h$. So $h\,\mathrm{MSE}\le Gh^2<Tqe^{-4|r|T}=nhq e^{-4|r|T}$, hence $\mathrm{MSE}<nqe^{-4|r|T}\le E D_n^2$. The exact worst case over admissible $Z$ is $Z\equiv0$. There, the ratio of $\mathrm{MSE}$ to the largest value `hsmall` permits never exceeds $\approx0.095$. `hsmall` forces $n\ge1$. Not vacuous: $r=0$, $\sigma=s_0=T=1$, $n=100$, $e-d=-2$ gives $Gh^2=0.00245<0.00521$. No junk values: the integrands are integrable and the RHS is $>0$. Standard facts: EM has strong order ½ for GBM ($E|S_T-\hat S_T|^2\le Ch$), and the accumulated rounding variance $\approx T\Delta^2/(12h)$ grows as $h\to0$, so rounding eventually dominates discretisation.
