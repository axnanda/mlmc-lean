# Blind read-back report: R25 (contracting levels)

| Field | Value |
|---|---|
| Date | 2026-10-07 |
| Packet | `readback/round19/packet_R25_contracting.lean` |
| Declarations audited | 18: 4 theorems, 7 packet definitions and 7 appended definitions |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round19/work_R25/`: `*.py` with matching `*.out`, plus the Lean scratch files `Check1.lean` and `Instances.lean` with their `.out` |

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `contractM` | def | n/a (well defined; it is a valid uniform second-moment bound) | n/a | no |
| 2 | `contractL` | def | n/a | n/a | no |
| 3 | `contractC1` | def | n/a | n/a | no |
| 4 | `contractC2` | def | n/a | n/a | no |
| 5 | `pairEM` | def (not used in the 4 statements) | n/a | n/a | no |
| 6 | `integral_sq_fine_sub_coarse_le` | theorem | **true**: no counterexample in any test; asymptotically sharp at $N_c\in\{0,1\}$ as $h\to0$ | no | no |
| 7 | `contractPath` | def | n/a | n/a | no |
| 8 | `variance_contractLevels_le` | theorem | **true** (corollary of #6) | no | no |
| 9 | `variance_contractLevels_le_two_pow` | theorem | **true** (corollary of #8) | no | no |
| 10 | `contractLimit` | def (`limUnder`) | n/a | n/a | the value is arbitrary off the convergence set, which #11 shows is a null set |
| 11 | `contracting_levels_mlmc` | theorem | **true** | no | no |
| 12–18 | `totalCost`, `blockMean`, `fineCoarseDiff`, `pairAvg`, `stdNormalSeq`, `backIter`, `emStep` | defs (appended) | n/a | n/a | `blockMean` gives $0^{-1}=0$ when $N=0$; #11 rules this out with $M_\ell>0$ |

**Overall:** no statement is false, vacuous or dependent on a junk value. Points 4–7 below are about modelling choices and strength.

## Main points for a human auditor

1. **The coupling is correct: it couples from the past.**
   - `backIter φ n e x` $=\varphi(\cdots\varphi(\varphi(x,e_{n-1}),e_{n-2})\cdots,e_0)$, so $e_0$ is the *most recent* increment. I checked this with `rfl` in Lean, together with the identity `backIter φ (n+1) e x = backIter φ n e (φ x (e n))`.
   - The fine chain starts from $x_0$ at time $-N_fh$ and uses $\xi_k$ on $[-(k+1)h,-kh]$.
   - The coarse chain starts from $x_0$ at time $-2N_ch$, which is no earlier because $2N_c\le N_f$. It uses $\xi_{2k}+\xi_{2k+1}$ on $[-(2k+2)h,-2kh]$, which is exactly the sum of the two fine increments on the same interval.
   - **Shared increments:** $\xi_0,\dots,\xi_{2N_c-1}$, the most recent ones. **Fine-only (burn-in):** $\xi_{2N_c},\dots,\xi_{N_f-1}$.
   - At time $-2N_ch$ the two chains differ by the fine chain's displacement from $x_0$, and the contraction removes this difference.
   - In the level theorems, $\xi_k=\sqrt{h_{\ell+1}}z_k$. `pairAvg` gives the coarse increments $\sqrt{h_\ell}\,(z_{2k}+z_{2k+1})/\sqrt2=\sqrt{h_{\ell+1}}\,(z_{2k}+z_{2k+1})$, as required.
2. **The constants hold, but in one corner they leave no slack.**
   - **Exact OU check.** I iterated the exact second-moment recursion for affine coefficients: OU with additive and with multiplicative noise, about 2 200 parameter cases. Most used the tightest admissible $H=h$ and $\delta=\delta_{\max}$, with $N_c$ up to 4000 and fine burn-ins from 0 to $\infty$. No case exceeds the bound.
   - **Worst ratios.** At $N_c=0$ the worst ratio is $0.99995$ (noise-free, fine chain relaxed, $h=10^{-5}H_{\max}$); at $N_c=1$ it is $0.999915$. Analytically the ratio is $\approx1-5\lambda h$ at $N_c=0$ and $\approx1-8.5\lambda h$ at $N_c=1$. It tends to 1 but stays below it.
   - The $N_c=0$ case follows rigorously because `contractM` bounds $\mathbb E|X_n-x_0|^2$ uniformly in $n$ (proof under #1).
   - **Nonlinear Monte Carlo.** Three nonlinear drifts were tested, including strong multiplicative noise with $K_b^2=0.75\cdot2\kappa$. The worst value of (mean + 3 s.e.)/bound is $0.37$.
   - The $C_1h$ (stationary) part of the bound is loose by factors of $10^{2}$ to $10^{7}$.
3. **Step-size restrictions.**
   - `hmargin` ($K_b^2+2K_a^2H+\delta\le2\kappa$) is the mean-square contractivity condition for the coarse step $2h\le2H$.
   - Combined with the Lipschitz assumptions and `hdiss`, it forces $\kappa\le K_a$, $K_aH<1$ and $h\delta\le\tfrac12$. Hence $1-h\delta/4\in[7/8,1)$, so the power never has a negative base.
   - The level version $K_b^2+K_a^2h_0+\delta\le2\kappa$ is the same condition with $H=h_0/2$. It also makes every level (step $\le h_0$) contracting.
4. **The target $P$ of the complexity statement.**
   - $P$ is not assumed. Its existence is part of the conclusion, and since limits in $\mathbb R$ are unique it is fixed: $P=\lim_\ell\mathbb E f(\text{contractPath}_\ell)=\lim_\ell\mathbb E f(\text{contractLimit}_\ell)$.
   - $\text{contractLimit}_\ell$ is the almost-sure backward limit (coupling from the past, Letac's principle). It is a draw from the invariant law $\pi_{h_\ell}$ of the Euler–Maruyama chain with step $h_\ell$.
   - So $P=\lim_{h\to0}\pi_h(f)$. It is **not** identified with $\pi(f)$ for the SDE's own invariant measure, because no SDE object appears in the statement.
   - The limit does exist: $\mathbb E f(\text{contractPath}_\ell)$ is Cauchy by #6. This is also illustrated numerically.
5. **Quantifier order is correct.**
   - In #6, $C_1$ and $C_2$ are explicit functions of $(a,b,K_a,K_b,\delta,H,x_0)$ and are uniform in $h\in(0,H]$, $N_f$ and $N_c$.
   - In #11, $P$ is chosen first, then $c_4$ (which depends on all the data, including $\eta$) before $\varepsilon$. $L$ and $M$ are chosen after $\varepsilon$.
6. **The complexity bound is weaker than the standard one.**
   - #11 proves cost $\le c_4\varepsilon^{-2-2\eta}$ for every fixed $\eta>0$. The standard result is $O(\varepsilon^{-2}|\log\varepsilon|^3)$.
   - The cost model charges $N_\ell$ fine steps per level-$\ell$ sample. It does not count the coarse partner's $N_{\ell-1}\le N_\ell/2$ steps. That undercounts by at most a factor of 1.5, which does not matter.
7. **`hc` is conservative.** The hypothesis $8\log2\le c\delta$ comes from the proof's decay rate $e^{-\delta T/8}$. The synchronous coupling actually contracts the mean-square difference at a rate of about $e^{-\delta T}$. The hypothesis is therefore stronger than needed, but not wrong.
8. **No junk-value dependence anywhere.**
   - $h$, $h_0$ and $\delta$ are all assumed positive.
   - Every integral and variance used comes with an asserted `Integrable` or `MemLp 2`.
   - `limUnder` is backed by asserted almost-sure convergence.
   - $M_\ell>0$ is asserted.
   - There is no natural-number subtraction, and every `rpow` has a positive base.

## Per-declaration sections

Notation: $\mathrm{EM}_s(S,w)=S+a(S)\,s+b(S)\,w$ (`emStep a b s S w`); $h_\ell=h_0/2^\ell$.

### 1. `contractM` (def)

**Rendering.**
$$M(a,b,K_a,K_b,\delta,H,x_0)=\frac{2}{\delta}\Big(\frac{2\big(|a(x_0)|(1+HK_a)+|b(x_0)|K_b\big)^2}{\delta}+a(x_0)^2H+b(x_0)^2\Big).$$

**Assessment.**
- **What it is.** It is a uniform second-moment bound. Let $X_{n+1}=X_n+s\,a(X_n)+b(X_n)W_n$, with $W_n\sim N(0,s)$ independent, $X_0=x_0$, $0<s\le H$, and the hypotheses of #6 in force.
- **Derivation.** Write $D_n=X_n-x_0$, $A=|a(x_0)|(1+HK_a)+|b(x_0)|K_b$ and $B=Ha(x_0)^2+b(x_0)^2$. Expanding and using $D\,\Delta a\le-\kappa D^2$, $|\Delta a|\le K_a|D|$, $|\Delta b|\le K_b|D|$, $1-2\kappa s+K_a^2s^2+K_b^2s\le1-s\delta$ and $2A|D|\le\frac\delta2D^2+\frac2\delta A^2$ gives
  $$\mathbb E D_{n+1}^2\le(1-\tfrac{s\delta}2)\,\mathbb E D_n^2+s\big(\tfrac{2A^2}\delta+B\big).$$
  By induction, $\sup_n\mathbb E D_n^2\le M$.
- **Sharpness.** The bound is asymptotically sharp: $M/(x_0-x^*)^2\to1$ in the noise-free linear case as $s\to0$.
- **Junk values.** In every use $\delta>0$, so there is no division by zero.

### 2. `contractL` (def)

**Rendering.** $L=\big(\frac{1+K_b^2}{\delta}+H\big)K_a^2+\big(1+\frac{1+K_b^2}{\delta}\big)K_b^2$, which is $\ge0$ when $\delta>0$ and $H\ge0$.

**Assessment.** This is an auxiliary constant: it collects the Young-inequality weights for the local-error terms. No issues.

### 3. `contractC1` (def)

**Rendering.** $C_1=\frac8\delta\,L\,\big(a(x_0)^2H+b(x_0)^2+4(K_a^2H+K_b^2)M\big)$, which is $\ge0$.

**Assessment.** This is the coefficient of $h$, the discretisation part of the bound in #6. No issues.

### 4. `contractC2` (def)

**Rendering.** $C_2=\big(1+\frac{8HL(K_a^2H+K_b^2)}{\delta}\big)M$, so $C_2\ge M\ge0$.

**Assessment.** This is the coefficient of the decaying term, the initial-discrepancy part of the bound in #6. Because $C_2\ge M$, the case $N_c=0$ of #6 is immediate. No issues.

### 5. `pairEM` (def)

**Rendering.** $\big((z_1,z_2),(p_1,p_2)\big)\mapsto\big(\mathrm{EM}_h(\mathrm{EM}_h(z_1,p_1),p_2),\ \mathrm{EM}_{2h}(z_2,p_1+p_2)\big)$. This is one coarse step of the coupled pair: two fine steps (with $p_1$ then $p_2$) against one coarse step (with $p_1+p_2$).

**Assessment.** It is not used in the four statements, presumably only in proofs. It matches the coupling in #6, where $p_1=\xi_{2k+1}$ is the earlier increment and $p_2=\xi_{2k}$.

### 6. `integral_sq_fine_sub_coarse_le` (theorem)

**Rendering.** Take $a,b:\mathbb R\to\mathbb R$, $K_a,K_b\in\mathbb R_{\ge0}$ and $\kappa,\delta,H\in\mathbb R$. Take any probability space $(\Omega,\mu)$ (with `IsProbabilityMeasure` from the section variables) and any $\xi:\mathbb N\to\Omega\to\mathbb R$. Assume:
- $a$ is $K_a$-Lipschitz and $b$ is $K_b$-Lipschitz;
- $(x-y)(a(x)-a(y))\le-\kappa(x-y)^2$ for all $x,y$;
- $\delta>0$;
- $h\in\mathbb R_{\ge0}$ with $0<h$ and $(h:\mathbb R)\le H$;
- $K_b^2+2K_a^2H+\delta\le2\kappa$;
- `iIndepFun ξ μ`, each $\xi_i$ is measurable, and $\mu\circ\xi_i^{-1}=N(0,h)$ (variance $h$, the convention of `gaussianReal`).

Then for every $x_0\in\mathbb R$ and every $N_f,N_c\in\mathbb N$ with $2N_c\le N_f$, set
$$F=\text{backIter}(\mathrm{EM}_h,N_f,(\xi_k)_k,x_0),\qquad C=\text{backIter}(\mathrm{EM}_{2h},N_c,(\xi_{2k}+\xi_{2k+1})_k,x_0).$$
These are the chains at time 0: the fine one started at $x_0$ at time $-N_fh$, the coarse one at $x_0$ at time $-2N_ch$ (see main point 1). The conclusions are:
1. $(F-C)^2$ is $\mu$-integrable;
2. $\mathbb E(F-C)^2\le C_1h+C_2(1-h\delta/4)^{N_c}$;
3. $\mathbb E(F-C)^2\le C_1h+C_2\exp\!\big(-\delta(2hN_c)/8\big)$.

Here $C_i=C_i(a,b,K_a,K_b,\delta,H,x_0)$. All arithmetic is in $\mathbb R$, with casts at the leaves; I confirmed this with `#check` and `pp.coercions`.

**Assessment.**
- **Truth: true as far as I can test.**
  - Conclusion 1: $F$ and $C$ are polynomially bounded functions of finitely many Gaussians, so every moment is finite.
  - Conclusion 2 at $N_c=0$ is rigorous: $\mathbb E(F-x_0)^2\le M\le C_2$ (see #1).
  - For $N_c\ge1$, the expected proof is the standard one-coarse-step recursion for $D=F-C$:
    - the contraction factor is $(1-2\lambda h)^2+2h\beta^2$ in the OU case, $\le1-2h\delta$ in general;
    - the local errors $h(a(F_{1/2})-a(F))$ and $(b(F_{1/2})-b(F))\xi$ are bounded with Young's inequality;
    - summing the geometric series gives the bound.
  - Conclusion 3 follows from conclusion 2, because $0\le1-x\le e^{-x}$ (with $x=h\delta/4\le1/8$) and $C_2\ge0$.
- **Exact checks for OU.** These cover affine $a=-\lambda x+\alpha$, $b=\beta x+\gamma$, with $K_a=\kappa=\lambda$ and $K_b=|\beta|$ (`ou_exact.py`, `ou_exact_detail.py`).
  - The exact moment recursion agrees with Monte Carlo (`ou_mc_crosscheck.py`: $0.26875$ exact against $0.2735\pm0.0049$).
  - The tightest choice $H=h$, $\delta=\delta_{\max}$ gives:
    - worst ratio $0.995$ at $h=10^{-3}H_{\max}$;
    - $0.99995$ at $N_c=0$ and $0.999915$ at $N_c=1$ when $h=10^{-5}H_{\max}$;
    - the ratio stays $<1$ and decreases in $N_c$.
  - The non-tight choice $H=3h$, $\delta=\delta_{\max}/2$ gives a worst ratio of $0.19$.
- **Nonlinear Monte Carlo** (`nonlinear_mc.py`). The three test cases were:
  - (A) $a=-x-\tanh x+0.5$, $b=0.5+0.3\sin x$;
  - (B) $a=-2x+\sin x$, $b=0.8\sqrt{1+x^2}$;
  - (C) $a=-1.5x-0.5x/\sqrt{1+x^2}$, $b=0.9\cos x+0.6x$, so $K_b^2=2.25$ against $2\kappa=3$.

  With tight $H$ and $\delta$, the worst (mean + 3 s.e.)/bound is $0.37$ (case A, $x_0=4$, relaxed fine chain, $N_c=0$). In the stationary regime the ratios are $10^{-7}$ to $10^{-2}$.
- **Vacuity: not vacuous.** `Instances.lean` applies the theorem with $\Omega=\mathbb R^{\mathbb N}$, $\mu=$ `infinitePi` of $N(0,1/10)$, $\xi_i=$ the coordinates, $a=-x$, $b=1$, $K_a=1$, $K_b=0$, $\kappa=\delta=1$, $H=h=1/10$, $N_f=5$, $N_c=2$. Every hypothesis is discharged and the file compiles.
- **Junk values: none.** $h>0$ and $\delta>0$; integrability is asserted; the base $1-h\delta/4$ lies in $[7/8,1)$.
- **Hypotheses.**
  - They are natural. The factor 2 in `hmargin` covers the coarse step $2h$; $H$ is a free step cap.
  - The bound is uniform in the burn-in $N_f-2N_c$.
  - The order is mean-square $O(h)$, i.e. strong order 1/2. That is the correct general order. It is not sharp for additive noise, where the true order is $O(h^2)$.
- **Standard result.** This is the mean-square coupling estimate for fine and coarse Euler–Maruyama chains of a contractive SDE with shifted start times, $\mathbb E|X^f_0-X^c_0|^2\le C(h+e^{-cT_c})$. It is the key lemma of MLMC for invariant measures (Giles–Majka–Szpruch–Vollmer–Zygalakis 2020).

### 7. `contractPath` (def)

**Rendering.** $\text{contractPath}_\ell(z)=\text{backIter}\big(\mathrm{EM}_{h_\ell},N(\ell),(\sqrt{h_\ell}\,z_k)_k,x_0\big)$. This is the level-$\ell$ Euler–Maruyama chain with step $h_\ell$, started at $x_0$ at time $-N(\ell)h_\ell$ and read at time 0. It uses the increment $\sqrt{h_\ell}z_k$ on $[-(k+1)h_\ell,-kh_\ell]$.

**Assessment.** Checked by `rfl`. Since $h_0>0$ in every use, the square root is never junk.

### 8. `variance_contractLevels_le` (theorem)

**Rendering.** Assume:
- $a$ is $K_a$-Lipschitz, $b$ is $K_b$-Lipschitz, and `hdiss` holds with $\kappa$;
- $\delta>0$ and $h_0>0$, with $K_b^2+K_a^2h_0+\delta\le2\kappa$;
- $x_0\in\mathbb R$, $N:\mathbb N\to\mathbb N$, and $f$ is $K_f$-Lipschitz;
- $\ell$ satisfies $2N(\ell)\le N(\ell+1)$.

On $(\mathbb R^{\mathbb N},\text{stdNormalSeq})$ let $Y(z)=f(\text{contractPath}_{\ell+1}(z))-f(\text{contractPath}_\ell(\text{pairAvg}\,z))$. Then $Y\in L^2$ and
$$\mathrm{Var}(Y)\le K_f^2\Big(C_1\,\tfrac{h_0}{2^{\ell+1}}+C_2\exp\!\big(-\delta N(\ell)\,h_0 2^{-\ell}/8\big)\Big),$$
with $C_1$ and $C_2$ evaluated at $H=h_0/2$.

**Assessment.**
- **Truth: true.** It is #6 with $H=h_0/2$, $h=h_{\ell+1}\le H$, `hmargin` matching, $N_f=N(\ell+1)$, $N_c=N(\ell)$, $\xi_k=\sqrt{h_{\ell+1}}z_k$ and $2hN_c=N(\ell)h_\ell$. Then $\mathrm{Var}\le\mathbb E Y^2\le K_f^2\,\mathbb E(F-C)^2$.
- **Exact OU check** (`levels_exact.py`: $a=1-x$, $b=0.5x+0.5$, $h_0=0.5$, tight $\delta$). For $\ell=0,\dots,21$ the ratio $\mathbb E(F-C)^2/\text{bound}$ lies in $[7.4\cdot10^{-5},\,2.5\cdot10^{-4}]$.
- **Vacuity: not vacuous** (Lean instance).
- **Junk values: none.** `variance` is `evariance.toReal`, and it is meaningful here because `MemLp 2` is asserted.
- **Standard result.** MLMC variance decay $V_\ell=O(h_\ell+e^{-cT_\ell})$.

### 9. `variance_contractLevels_le_two_pow` (theorem)

**Rendering.** The hypotheses of #8, plus $c\in\mathbb R$ with $8\log2\le c\delta$ and $c\ell\le N(\ell)\,h_0/2^\ell$ (the coarse horizon is $\ge c\ell$). The conclusion is $Y\in L^2$ and $\mathrm{Var}(Y)\le K_f^2(C_1h_0+2C_2)\cdot2^{-(\ell+1)}$, where the power is real `rpow` with base 2.

**Assessment.**
- **Truth: true.** Since $c\delta>0$ and $\delta>0$, $c>0$. Then $e^{-\delta T_\ell/8}\le e^{-c\delta\ell/8}\le2^{-\ell}$, $C_2\ge0$, and $h_0/2^{\ell+1}=h_0\,2^{-(\ell+1)}$.
- **Edge case.** At $\ell=0$ the hypothesis `hT` is trivial and the bound reduces to $C_1h_0/2+C_2$, which is fine.
- **Vacuity: not vacuous** (Lean instance with $c=8\log2$).
- **Junk values: none.**
- **Hypotheses.** `hc` is conservative (main point 7).
- **Standard result.** $V_\ell=O(2^{-\ell})$ when $T_\ell\gtrsim\ell$.

### 10. `contractLimit` (def)

**Rendering.** $\text{contractLimit}_\ell(z)=\text{limUnder}_{n\to\infty}\,\text{backIter}(\mathrm{EM}_{h_\ell},n,(\sqrt{h_\ell}z_k)_k,x_0)$. This is the value at time 0 as the start time recedes to $-\infty$ (coupling from the past). When the limit does not exist it is an arbitrary `Classical.choice` value.

**Assessment.**
- **The arbitrary value is never used.** #11 asserts almost-sure convergence, and every quantity built from `contractLimit` in #11 is an integral, which does not see null sets.
- **Numerical illustration** (`backward_limit.py`).
  - The backward iterates converge to machine precision: by $n=80$ for $h=0.2$ and by $n=640$ for $h=0.05$.
  - The limit is the same for $x_0=0$ and $x_0=25$.
  - The forward iteration does not converge.
  - Monte Carlo confirms $\mathbb E|Z_{n+1}-Z_n|^2\le(1-h\delta)^n(h^2a(x_0)^2+hb(x_0)^2)$.

### 11. `contracting_levels_mlmc` (theorem)

**Rendering.** Assume the hypotheses of #8, with `hmargin` at $h_0$, plus:
- $2N(\ell)\le N(\ell+1)$ for all $\ell$;
- $8\log2\le c\delta$, and $c\ell\le N(\ell)h_0/2^\ell$ for all $\ell$;
- $N(\ell)\le m(\ell+1)2^\ell$ in $\mathbb N$, for all $\ell$;
- $f$ is $K_f$-Lipschitz and $\eta>0$.

The conclusions are:
1. **For every $\ell$:**
   - $f\circ\text{contractPath}_\ell$ is integrable;
   - for almost every $z$, the backward iterates at level $\ell$ converge as $n\to\infty$ to $\text{contractLimit}_\ell(z)$;
   - $f\circ\text{contractLimit}_\ell$ is integrable.
2. **$P$ exists:** there is $P\in\mathbb R$ with $\mathbb E f(\text{contractPath}_\ell)\to P$ and $\mathbb E f(\text{contractLimit}_\ell)\to P$ as $\ell\to\infty$.
3. **Complexity:** there is $c_4>0$ such that for every $\varepsilon\in(0,e^{-1})$ there exist $L$ and $M:\mathbb N\to\mathbb N$ with $M>0$ such that the estimator
   $$\hat Y=\sum_{\ell=0}^L\frac1{M_\ell}\sum_{n<M_\ell}\Delta_\ell(x_{(\ell,n)}),$$
   computed on i.i.d. standard normal sequences $x_{(\ell,n)}$ (`infinitePi` over $\mathbb N\times\mathbb N$), satisfies:
   - $(\hat Y-P)^2$ is integrable;
   - $\mathbb E(\hat Y-P)^2<\varepsilon^2$;
   - the expected cost $\sum_{\ell\le L}M_\ell N(\ell)$ is at most $c_4\varepsilon^{-2-2\eta}$.

   Here $\Delta_0=f\circ\text{contractPath}_0$ and $\Delta_{\ell+1}=Y_\ell$ as in #8.

**Assessment.**
- **Truth: true.**
  - *Almost-sure convergence.* $\mathbb E|Z_{n+1}-Z_n|^2\le(1-h_\ell\delta)^n(h_\ell^2a(x_0)^2+h_\ell b(x_0)^2)$ (synchronous contraction; every level has step $\le h_0$). The square roots are summable, so the series converges absolutely almost surely.
  - *Integrability.* $\text{contractLimit}_\ell\in L^2$ by Fatou, and it is a.e. equal to a measurable function.
  - *Existence of $P$.*
    - `pairAvg` preserves stdNormalSeq, so $|\mathbb E f(\text{Path}_{\ell+1})-\mathbb E f(\text{Path}_\ell)|\le K_f\sqrt{(C_1h_0+2C_2)2^{-(\ell+1)}}$. This is summable, so the sequence is Cauchy.
    - Also $|\mathbb E f(\text{Lim}_\ell)-\mathbb E f(\text{Path}_\ell)|\to0$, because $T_\ell\ge c\ell\to\infty$.
  - *Complexity.* Apply the standard MLMC theorem with:
    - $V_\ell\le K2^{-\ell}$;
    - $C_\ell\le m(\ell+1)2^\ell$;
    - bias $\le K'2^{-L/2}$;
    - $L\approx2\log_2(1/\varepsilon)$.

    This gives cost $O(\varepsilon^{-2}|\log\varepsilon|^3)\le c_4\varepsilon^{-2-2\eta}$.
- **Semi-analytic check** (`levels_exact.py`, using the theorem's own bounds in the OU example). For $\varepsilon$ from $3.6\cdot10^{-2}$ down to $3.6\cdot10^{-13}$, $\text{cost}\cdot\varepsilon^2/\log^3(1/\varepsilon)$ decreases from $2.1\cdot10^6$ to $2.1\cdot10^5$, and $\text{cost}\cdot\varepsilon^{2.1}$ stays $\le2.9\cdot10^8$. Exact means give $\mathbb E\,\text{contractPath}_\ell\to P=\alpha/\lambda$ for $f=\mathrm{id}$.
- **Quantifier order:** correct (main point 5).
- **Vacuity: not vacuous.** `Instances.lean` uses $a=-x$, $b=1$, $h_0=\delta=\kappa=K_a=1$, $K_b=0$, $c=8\log2$, $N(\ell)=6(\ell+1)2^\ell$, $m=6$, $f=\mathrm{id}$, $\eta=1$. The hypothesis `hT` is proved via `Real.log_two_lt_d9`.
- **Junk values: none** (main point 8).
- **Modelling points.**
  - $P$ is the $h\to0$ limit of the invariant means of the Euler–Maruyama chain. It is not the SDE's $\pi(f)$, which is not mentioned.
  - The cost bound $\varepsilon^{-2-2\eta}$ is weaker than the standard $\varepsilon^{-2}|\log\varepsilon|^3$.
  - The cost counts only fine steps.
  - `hc` is conservative.
  - The restriction $\varepsilon<e^{-1}$ is harmless.
- **Standard result.** MLMC for invariant measures of contractive SDEs (Giles–Majka–Szpruch–Vollmer–Zygalakis 2020), together with coupling from the past (Propp–Wilson; Diaconis–Freedman, iterated random functions).

### 12–18. Appended definitions

**Rendering.**
- `totalCost cost L N x` $=\sum_{\ell\le L}\sum_{n<N_\ell}\text{cost}(\ell,n,x)$. In #11 this is the deterministic $\sum_\ell M_\ell N(\ell)$.
- `blockMean f ω i N x` $=N^{-1}\sum_{n<N}f_i(\omega_{(i,n)}(x))$. When $N=0$, Lean gives $0^{-1}=0$; #11 excludes this with $M_\ell>0$.
- `fineCoarseDiff Pf Pc`: at 0 it is $Pf_0$; at $\ell+1$ it is $Pf_{\ell+1}-Pc_\ell$.
- `pairAvg z k` $=(z_{2k}+z_{2k+1})/\sqrt2$, which is again i.i.d. $N(0,1)$ under stdNormalSeq.
- `stdNormalSeq` $=\bigotimes_{k\in\mathbb N}N(0,1)$ on $\mathbb R^{\mathbb N}$, a probability measure.
- `backIter`: $\text{backIter}(\varphi,0,e,x)=x$ and $\text{backIter}(\varphi,n+1,e,x)=\varphi(\text{backIter}(\varphi,n,e\circ\mathrm{succ},x),e_0)$. So $e_{n-1}$ is applied first and $e_0$ last (checked by `rfl`).
- `emStep a b h S dW` $=S+a(S)h+b(S)\,dW$.

**Assessment.** All are standard and are used consistently with the intended meaning. The only junk value, in `blockMean` at $N=0$, is excluded where it matters.

## Scripts (in `work_R25/`)

- `Check1.lean` / `.out`: `rfl` checks of the `backIter` ordering and of every packet definition; `#check` of the four statements with `pp.coercions` and `pp.numericTypes`.
- `Instances.lean` / `.out`: concrete instances discharging every hypothesis of #6, #8, #9 and #11 (non-vacuity). It compiles with one linter warning only.
- `ou_exact.py` / `.out`: exact second-moment recursion for affine coefficients (576 cases).
- `ou_exact_detail.py` / `.out`: 1 404 tight cases, split by $N_c=0$ versus $N_c\ge1$ and noisy versus noise-free; the $h\to0$ sharpness at 40 digits; non-tight $H$ and $\delta$.
- `ou_mc_crosscheck.py` / `.out`: Monte Carlo cross-check of the exact recursion.
- `nonlinear_mc.py` / `.out`: three nonlinear dissipative examples, with sanity checks of the Lipschitz and dissipativity hypotheses.
- `backward_limit.py` / `.out`: backward versus forward iteration, independence of $x_0$, and the increment bound.
- `levels_exact.py` / `.out`: exact level-by-level variance check for $\ell\le21$, convergence to $P$, and the complexity arithmetic.
- `stepsize_facts.py` / `.out`: $h\delta\le1/2$, $K_aH<1$, and $(1-h\delta/4)^{N_c}\le e^{-\delta 2hN_c/8}$. At the default 15 digits the last check showed a spurious $+5\cdot10^{-11}$, caused by rounding; at 50 digits it is negative.
