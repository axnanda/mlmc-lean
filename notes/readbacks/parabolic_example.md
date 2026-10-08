# Blind read-back report: R35 (parabolic example)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round22/packet_R35_parabolic.lean` |
| declarations audited | 9 theorems (the 8 packet definitions and the 4 appended definitions are also rendered) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round22/work_R35/` (`identities.py`, `brute.py`, `modes.py`, `weak_ext.py`, `mlmc_cost.py`, each with its `.out`; `scratch.lean`/`scratch.out` is the elaboration check) |

Elaboration was confirmed by compiling a self-contained copy of the packet (proofs `sorry`, targeted Mathlib
imports, the appended definitions placed first) with `pp.coercions`/`pp.numericTypes`. All casts are as
described below. Mathlib's `∑ x ∈ s, body` parses `body` at `term:67`
(`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:181`). So `∑ ℓ ∈ range (L+1), blockMean … x - parabolicLimit`
means $(\sum_\ell \dots) - \text{parabolicLimit}$, which is the intended reading.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `sineCoef_eq` | theorem | true | no | no |
| 2 | `parabolicPath_eq_sum` | theorem | true | no | no |
| 3 | `sum_sq_parabolicPath` | theorem | true | no | no |
| 4 | `integral_parabolicP` | theorem | true | no | no |
| 5 | `parabolic_coupling` | theorem | true | no | no |
| 6 | `parabolic_variance_rate` | theorem | true (constant ~35 000× loose) | no | no |
| 7 | `parabolic_mean_tendsto` | theorem | true | no | no |
| 8 | `parabolic_weak_rate` | theorem | true (constants ~770× loose) | no | no |
| 9 | `parabolic_mlmc_theorem1` | theorem | true | no | no |

## Main points for a human auditor

1. All 9 theorems are true. None is vacuous, and none depends on a Lean junk value. Every integral is a genuine
   Lebesgue integral: each integrand is a polynomial in finitely many i.i.d. $N(0,1)$ coordinates, so it is
   integrable. The `MemLp`/`Integrable` conjuncts state this explicitly where it matters.
2. **The numerical constants are very loose.** These are the exact sharp values I computed:
   - $\sup_\ell 16^{\ell+1}E[D_\ell^2]\approx 43.3$, against the stated $1\,500\,000$.
   - $\sup_\ell 4^{\ell+1}|E P_{\ell+1}-E P_\ell|\approx 1.598$, against the stated $1225$.
   - $\sup_\ell 4^\ell|E P_\ell-\text{limit}|\approx 0.533$, against the stated $409$.

   The statements are correct, but the constants carry no quantitative information. Only the rates
   $16^{-\ell}$ ($\beta=4$) and $4^{-\ell}$ ($\alpha=2$) matter.
3. **The model.** The scheme is the explicit FTCS scheme for $du = u_{xx}\,dt + 10\,dW(t)$ on $(0,1)$, with
   zero Dirichlet data, $u(\cdot,0)=0$ and $T=\tfrac14$.
   - The noise is a single scalar Brownian motion added uniformly at every interior node. It is spatially
     constant, not space-time white noise.
   - $\lambda=\Delta t/h^2=\tfrac14$ is hard-coded. Level $\ell$ has $J=2^{\ell+1}$ cells (so level 0 already
     has 2 cells) and $N=4^{\ell+1}$ steps.
   - The quantity of interest is $P_\ell = h\sum_j u_j^2\approx\int_0^1 u(x,\tfrac14)^2dx$.
   - The Lean statements never mention the SPDE. Their only link to the continuum is `parabolicLimit` together
     with the `Tendsto` statement. I checked independently that `parabolicLimit` is exactly
     $E\int_0^1u(x,\tfrac14)^2dx$ for this SPDE ($\approx 4.1371339679$).
4. The variance bound in #6 is on the raw second moment $E[D_\ell^2]$, which is stronger than bounding the
   variance. That is fine.
5. In #9 the cost of one level-$\ell$ sample is $2^{\ell+1}4^{\ell+1}=J_\ell N_\ell$. This is the fine path
   only; the coarse path's extra $1/8$ is not counted. This is a harmless constant-factor modelling choice.
   The hypothesis $\varepsilon<e^{-1}$ comes from the statement of Giles' theorem and is harmless.
6. Redundancies:
   - `parabolic_mean_tendsto` (#7) is repeated as the first conjunct of #9.
   - In the second conjunct of #5, the quantifier over $\ell$ is cosmetic (the identity is uniform in $\ell$).
   - The packet contains an empty `section moments`, with an unused `variable` line and no declarations.
7. #2 and #3 hold for every real $\lambda$ and every $J$, so there is no hidden stability (CFL) assumption.
   They are purely algebraic.

---

## Definitions (rendering only)

Notation: $\pi$ is `Real.pi`. Every ℕ argument is cast to ℝ at the leaves (confirmed by elaboration).

- **`sineMode J m j`** $=\sin(\pi m j/J)$. If $J=0$ the argument is $0$ (since $x/0=0$), so the value is $0$.
- **`sineCoef J m`** $=\frac{2}{J}\sum_{i=1}^{J-1}\sin(\pi m i/J)$. This is the discrete sine-transform
  (DST-I) coefficient of the constant vector $1$ on the interior nodes $1,\dots,J-1$. It is $0$ if $J=0$.
- **`sineEig lam J m`** $=1-4\lambda\sin^2\!\big(\pi m/(2J)\big)$. This is the FTCS amplification factor of
  the $m$-th discrete Dirichlet sine mode. For $\lambda=\tfrac14$ it equals $\cos^2(\pi m/(2J))\in(0,1)$ when
  $0<m<J$.
- **`parabolicStep lam J w u j`**:
  - for $0<j<J$ it is $u_j+\lambda(u_{j+1}-2u_j+u_{j-1})+w$;
  - for every other $j$ (that is, $j=0$ or $j\ge J$) it is $u_j$.

  The ℕ subtraction $j-1$ only occurs when $j>0$, so it is honest. One step is FTCS plus a spatially
  constant forcing $w$ at the interior nodes; the boundary nodes stay fixed.
- **`parabolicPath lam J dW n`** $=u^{(n)}$, where $u^{(0)}\equiv0$ and
  $u^{(k+1)}=\text{step}(w=10\,dW_k,\,u^{(k)})$. Nodes $j\ge J$ and $j=0$ stay $0$.
- **`modeAmp μ c dW n`** $=a_n$, where $a_0=0$ and $a_{k+1}=\mu a_k+10c\,dW_k$. Equivalently
  $a_n=10c\sum_{k<n}\mu^{n-1-k}dW_k$.
- **`parabolicP ℓ z`** $=\frac{1}{2^{\ell+1}}\sum_{j=0}^{2^{\ell+1}}\big(u^{(N)}_j\big)^2$. Here
  $u=$`parabolicPath`$(\tfrac14,\,J=2^{\ell+1},\,dW_n=z_n/2^{\ell+2})$ is evaluated after
  $N=4^{\ell+1}$ steps.
  - With $h=1/J$ we get $\Delta t=\lambda h^2=4^{-(\ell+2)}$, so $dW_n=\sqrt{\Delta t}\,z_n$ and
    $T=N\Delta t=\tfrac14$.
  - $P_\ell$ is the discrete $L^2(0,1)$-norm squared of the FTCS solution at $T=\tfrac14$.
- **`parabolicLimit`** $=\sum_{k\ge0}\dfrac{400\,(1-e^{-\pi^2(2k+1)^2/2})}{\pi^4(2k+1)^4}\approx
  4.137133967903197$.
  - The series is summable (terms are $O(k^{-4})$), so the `tsum` is genuine.
  - This is the exact value of $E\int_0^1u(x,\tfrac14)^2dx$ for $du=u_{xx}dt+10\,dW(t)$ with zero data.
  - Derivation: $1=\sum_{m\text{ odd}}\frac{4}{m\pi}\sin m\pi x$ and
    $E a_m(T)^2=\frac{1600}{m^2\pi^2}\cdot\frac{1-e^{-2m^2\pi^2T}}{2m^2\pi^2}$, with $T=\tfrac14$.
- Appended definitions:
  - **`blockMean f ω i N x`** $=N^{-1}\sum_{n<N}f_i(\omega_{(i,n)}(x))$. It is $0$ if $N=0$.
  - **`fineCoarseDiff Pf Pc`**: at level $0$ it is $Pf_0$; at level $\ell+1$ it is
    $y\mapsto Pf_{\ell+1}(y)-Pc_\ell(y)$.
  - **`pairAvg z k`** $=(z_{2k}+z_{2k+1})/\sqrt2$.
  - **`stdNormalSeq`** is the product measure $\bigotimes_{n\in\mathbb N}N(0,1)$ on $\mathbb R^{\mathbb N}$.
    Here `gaussianReal 0 1` has variance 1.

---

## 1. `sineCoef_eq`

**Rendering.** For all $J,m\in\mathbb N$ with $0<m<2J$:
$$\frac2J\sum_{i=1}^{J-1}\sin\frac{\pi m i}{J}=\frac{1-\cos(\pi m)}{J}\cdot\frac{\cos(\pi m/(2J))}{\sin(\pi m/(2J))}.$$

**Assessment.**
- **True.** This is Lagrange's identity
  $\sum_{i=1}^{J-1}\sin i\theta=\frac{\cos(\theta/2)-\cos((J-\frac12)\theta)}{2\sin(\theta/2)}$ with
  $\theta=\pi m/J$. Since $m\in\mathbb Z$, $\cos(\pi m-\theta/2)=\cos(\pi m)\cos(\theta/2)$. The factor
  $1-\cos\pi m$ is $2$ for odd $m$ and $0$ for even $m$.
- **Hypotheses.** $0<m<2J$ forces $J\ge1$ and $0<\pi m/(2J)<\pi$, so the denominator $\sin$ is nonzero.
- **Junk values.** No junk value is involved: no division by zero occurs, and the identity also covers
  $J\le m<2J$.
- **Strength of hypotheses.** They are slightly stronger than needed. The identity holds whenever
  $\sin(\pi m/(2J))\ne0$, and when $\sin=0$ it holds trivially, with both sides $0$ by the junk value.
- **Checked numerically** for $J\le13$ and all $0<m<2J$: maximum error $2\times10^{-40}$
  (`identities.out`).
- **Non-vacuous instance:** $J=2,m=1$ gives $1=1$.
- **Standard fact:** the closed form of a finite sine sum, equivalently the DST-I coefficients of the
  constant function.

## 2. `parabolicPath_eq_sum`

**Rendering.** For all $\lambda\in\mathbb R$, $J,n\in\mathbb N$, $dW:\mathbb N\to\mathbb R$, and $j\le J$:
$$u^{(n)}_j=\sum_{m=1}^{J-1}a^{(m)}_n\sin\frac{\pi mj}{J},\qquad a^{(m)}=\texttt{modeAmp}\big(\texttt{sineEig}\,\lambda J m,\ \texttt{sineCoef}\,J m,\ dW\big).$$

**Assessment.**
- **True.** Let $\phi_m(j)=\sin(\pi mj/J)$.
  - $\phi_m$ vanishes at $j=0$ and $j=J$.
  - $\phi_m$ is an eigenvector of the 3-point Dirichlet Laplacian, with
    $\phi_m(j+1)-2\phi_m(j)+\phi_m(j-1)=-4\sin^2(\pi m/(2J))\phi_m(j)$.
  - The interior constant vector satisfies $1=\sum_m c_m\phi_m$ (DST-I inversion).

  An induction on $n$ then gives the result. The boundary nodes stay $0$ on both sides. The restriction
  $j\le J$ is genuinely needed: for $j>J$ the path is $0$ but the sine series need not be.
- **Edge cases.** For $J\in\{0,1\}$ both sides are $0$. No stability condition on $\lambda$ is needed.
- **Checked numerically** on 40 random $(\lambda\in[-1,1],J\le8,n\le7,dW)$: maximum error $2\times10^{-37}$.
- **Not vacuous.** **Junk values:** none.
- **Standard fact:** the spectral (DST) solution of the explicit FTCS scheme with additive forcing.

## 3. `sum_sq_parabolicPath`

**Rendering.** For all $\lambda,J,dW,n$:
$$\sum_{j=0}^{J}(u^{(n)}_j)^2=\frac J2\sum_{m=1}^{J-1}(a^{(m)}_n)^2.$$

**Assessment.**
- **True.** This is discrete Parseval for DST-I: for $1\le m,m'\le J-1$,
  $\sum_{j=1}^{J-1}\sin\frac{\pi mj}J\sin\frac{\pi m'j}J=\frac J2\delta_{mm'}$. The terms $j=0$ and $j=J$
  vanish.
- **Edge cases.** No hypotheses. For $J=0$ and $J=1$ it reads $0=0$, which is consistent rather than junk.
- **Checked numerically** (relative error $10^{-39}$).
- **Not vacuous.** **Junk values:** none.
- **Standard fact:** Parseval for the discrete sine transform.

## 4. `integral_parabolicP`

**Rendering.** For every $\ell$, put $J=2^{\ell+1}$, $N=4^{\ell+1}$, $c_m=$`sineCoef J m` and
$\mu_m=$`sineEig (1/4) J m`. Then
$$\int P_\ell\,d\,\text{stdNormalSeq}=\frac12\sum_{m=1}^{J-1}\sum_{i=0}^{N-1}\Big(\frac{10}{2J}\,c_m\,\mu_m^{\,N-1-i}\Big)^2.$$
The exponent $N-1-i$ is an ℕ subtraction, but $i<N$ makes it honest. Note that $10/(2J)=10\sqrt{\Delta t}$.

**Assessment.**
- **True.** By #3, $P_\ell=h\cdot\frac J2\sum_m a_m^2=\frac12\sum_m a_m^2$. Each $a_m=\sum_i b_{m,i}z_i$
  with $b_{m,i}=10c_m\mu_m^{N-1-i}/2^{\ell+2}$, and $E(\sum_i b_iz_i)^2=\sum_i b_i^2$.
- **Integrability.** $P_\ell$ is a quadratic form in $z_0,\dots,z_{N-1}$, so it is integrable. The RHS is
  $>0$ (the $m=1$ term), so the equation cannot hold through a junk integral $0$.
- **Checked numerically** for $\ell=0..3$: the literal RHS, a spectral closed form, and a brute-force
  $\operatorname{tr}(A^TA)$ obtained by running `parabolicStep` on unit vectors all agree. For example
  $E P_0=4.150390625$ (`brute.out`, `modes.out`).
- **Not vacuous.** **Junk values:** none.
- **Standard fact:** the Itô isometry (discrete) plus Parseval.

## 5. `parabolic_coupling`

**Rendering.**
- (a) The map $z\mapsto \text{pairAvg}(\text{pairAvg}\,z)$ is measurable and pushes
  $\bigotimes N(0,1)$ forward to $\bigotimes N(0,1)$ on $\mathbb R^{\mathbb N}$.
- (b) For all $\ell,z,p$:
  $\text{pairAvg}(\text{pairAvg}\,z)_p/2^{\ell+2}=\sum_{q=0}^{3}z_{4p+q}/2^{\ell+3}$.

**Assessment.**
- **(b) True by algebra.** $\text{pairAvg}^2(z)_p=(z_{4p}+z_{4p+1}+z_{4p+2}+z_{4p+3})/2$, and the
  quantifier over $\ell$ is cosmetic. Checked numerically.
- **(a) True.**
  - Each output coordinate is half a sum of 4 i.i.d. $N(0,1)$ variables, hence $N(0,1)$.
  - Outputs use disjoint index blocks, hence they are independent.
  - The product measure is determined by its finite-dimensional marginals.
  - The map is measurable coordinatewise (it is linear in finitely many coordinates).
- **Interpretation.** The coarse Brownian increment over $\Delta t_\ell=4\Delta t_{\ell+1}$ is the sum of 4
  fine increments, which is the standard MLMC coupling. Here $z_k/2^{\ell+3}$ is the fine-level increment.
- **No hypotheses.** **Not vacuous.** **Junk values:** none.

## 6. `parabolic_variance_rate`

**Rendering.** For every $\ell$, let $D_\ell(z)=P_{\ell+1}(z)-P_\ell(\text{pairAvg}^2 z)$. Then
$D_\ell\in L^2(\text{stdNormalSeq})$ and $\int D_\ell^2\,d\,\text{stdNormalSeq}\le 1\,500\,000/16^{\ell+1}$.

**Assessment.**
- **True.** $D_\ell=z^TBz$ is a quadratic form in $4^{\ell+2}$ coordinates, so $D_\ell\in L^2$ and
  $E D_\ell^2=(\operatorname{tr}B)^2+2\operatorname{tr}B^2$.
- **Exact computation.** I computed this two independent ways: a spectral closed form for $\ell\le8$, and
  brute-force matrices built literally from `parabolicStep`/`pairAvg` for $\ell\le2$. The two agree to all
  printed digits. The values of $16^{\ell+1}E D_\ell^2$ for $\ell=0,\dots,8$ are
  $35.90, 39.44, 41.48, 42.45, 42.90, 43.11, 43.22, 43.27, 43.29$.
  - The sequence is increasing, with increments halving, so it converges to about $43.32$.
  - The stated constant is therefore about $3.5\times10^4$ times larger than necessary.
  - For comparison, $(E D_\ell)^2\cdot16^{\ell+1}\to\approx2.55$.
- **Strength.** It bounds the second moment, which is stronger than bounding the variance.
- **Not vacuous.** **Junk values:** none.
- **Standard result:** the MLMC level-variance decay $V_\ell=O(h_\ell^4)=O(16^{-\ell})$ ($\beta=4$) for the
  explicit scheme with $\Delta t\propto h^2$ and additive noise.

## 7. `parabolic_mean_tendsto`

**Rendering.** $E[P_\ell]\to\text{parabolicLimit}$ as $\ell\to\infty$, with $\ell\in\mathbb N$.

**Assessment.**
- **True.** Use #4 per mode, in closed form:
  $E P_\ell=50\sum_{m\text{ odd}}c_m^2\Delta t\frac{1-\mu_m^{2N}}{(1-\mu_m)(1+\mu_m)}$.
- **Termwise limit:**
  - $c_m\to4/(\pi m)$;
  - $\Delta t/(1-\mu_m)\to1/(\pi m)^2$;
  - $\mu_m^{2N}=(1-\sin^2\frac{\pi m}{2J})^{2J^2}\to e^{-\pi^2m^2/2}$.
- **Domination.** $c_m\le 4/(\pi m)$ because $\cot x\le1/x$. Jordan's inequality gives
  $\Delta t/(1-\mu_m)\le 1/(4m^2)$. Finally $(1-\mu^{2N})/(1+\mu)\le1$.
- **Checked numerically:** $E P_{12}-\text{limit}\approx3.2\times10^{-8}$.
- **Not vacuous.** **Junk values:** none (the `tsum` is summable).
- **Standard fact:** weak convergence of the FTCS discretisation, by dominated convergence over Fourier modes.

## 8. `parabolic_weak_rate`

**Rendering.** All three of the following hold:
- for every $\ell$, $P_\ell\in L^2(\text{stdNormalSeq})$;
- for every $\ell$, $|E P_{\ell+1}-E P_\ell|\le 1225/4^{\ell+1}$;
- for every $\ell$, $|E P_\ell-\text{parabolicLimit}|\le409/4^{\ell}$.

**Assessment.**
- **True.** $P_\ell$ is a Gaussian quadratic form, so it is in $L^2$.
- **Exact values** for $\ell\le17$:
  - $4^\ell|E P_\ell-L|$ increases monotonically, from $0.0133$ at $\ell=0$, converging geometrically to
    $\approx0.53278$.
  - $4^{\ell+1}|E P_{\ell+1}-E P_\ell|$ increases to $\approx1.5983$, which is $3\times0.533$, as expected
    from an $O(h^2)$ expansion.

  Both stated constants are about 770 times larger than necessary (`modes.out`, `weak_ext.out`).
- The middle conjunct is not implied by the third conjunct, which would only give $2045/4^{\ell+1}$.
- **Not vacuous.** **Junk values:** none.
- **Standard result:** the weak order is $O(h^2)=O(\Delta t)$, so $\alpha=2$ in units of $2^{-\ell}$.

## 9. `parabolic_mlmc_theorem1`

**Rendering.** Both of the following hold:
- (i) $E P_\ell\to\text{parabolicLimit}$;
- (ii) there exists $c_4>0$ such that for every real $\varepsilon$ with $0<\varepsilon<e^{-1}$ there exist
  $L\in\mathbb N$ and $N:\mathbb N\to\mathbb N$ satisfying all of the conditions below.

The conditions in (ii):
- $N_\ell\ge1$ for all $\ell$.
- The setting: let $x=(x_{(\ell,n)})_{(\ell,n)\in\mathbb N^2}$ be distributed as
  $\bigotimes_{\mathbb N\times\mathbb N}\text{stdNormalSeq}$, i.e. an i.i.d. array of standard normal
  sequences. Define
  $$\hat Y(x)=\sum_{\ell=0}^{L}\frac1{N_\ell}\sum_{n<N_\ell}Y_\ell(x_{(\ell,n)}),$$
  where $Y_0=P_0$ and $Y_{\ell+1}(y)=P_{\ell+1}(y)-P_\ell(\text{pairAvg}^2y)$.
- $(\hat Y-\text{parabolicLimit})^2$ is integrable.
- $E(\hat Y-\text{parabolicLimit})^2<\varepsilon^2$.
- $\sum_{\ell=0}^{L}N_\ell\,2^{\ell+1}4^{\ell+1}\le c_4\varepsilon^{-2}$, where $\varepsilon^{-2}$ is `rpow`
  and honest since $\varepsilon>0$.

The constant $c_4$ is uniform in $\varepsilon$; $L$ and $N$ may depend on $\varepsilon$.

**Assessment.**
- **True.** This is Giles' MLMC complexity theorem with:
  - $|E P_\ell-P|\le c_1 4^{-\ell}$ ($\alpha=2$, from #8);
  - $V_\ell\le E D^2\le c_2 16^{-\ell}$ ($\beta=4$, from #6, with $\operatorname{Var}P_0<\infty$);
  - $C_\ell=8^{\ell+1}$ ($\gamma=3$);
  - telescoping via the measure-preserving coupling (#5).

  Since $\beta>\gamma$, the cost is $O(\varepsilon^{-2})$.
- **Integrability.** $\hat Y$ is a finite sum of Gaussian quadratic forms, so its square is integrable and
  the MSE is a genuine integral. It equals $\text{bias}^2+\sum_\ell\operatorname{Var}(Y_\ell)/N_\ell$.
- **Illustration.** With the computed constants and the standard choice
  $N_\ell=\lceil2\varepsilon^{-2}\sqrt{V_\ell/C_\ell}\sum_k\sqrt{V_kC_k}\rceil$, the MSE stays below
  $\varepsilon^2$ and $\text{cost}\cdot\varepsilon^2\le\approx7.6\times10^3$ for
  $\varepsilon\in(10^{-10},e^{-1})$ (`mlmc_cost.out`).
- **Parsing.** By the big-operator precedence noted above, the subtraction applies to the whole sum.
- **Assumptions.**
  - The restriction $\varepsilon<e^{-1}$ is inherited from the statement of Giles' theorem and is harmless.
  - Requiring $N_\ell\ge1$ for all $\ell$, including $\ell>L$, costs nothing.
  - The cost counts only the fine path per sample (see Main point 5).
- **Not vacuous**, because the set of admissible $\varepsilon$ is nonempty. **Junk values:** none.
- Conjunct (i) duplicates #7.
- **Standard result:** Giles (2008), *Multilevel Monte Carlo path simulation*, Theorem 3.1 (the $\beta>\gamma$
  case), specialised to the explicit finite-difference SPDE example.
