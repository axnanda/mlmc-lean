# Blind read-back report: packet R24 (SDE extensions)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round19/packet_R24_sdeext.lean` |
| declarations audited | 15 module declarations (1 definition, 14 theorems); the 12 appended definitions are also rendered |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round19/work_R24/` (`*.py` with matching `*.out`; `Scratch.lean` / `Scratch.out` is an elaboration check) |
| Lean check | I compiled a scratch copy of the packet (imports from targeted Mathlib modules only, proofs left as `sorry`). All 14 statements elaborate without errors. Convention checks also compiled: `implicitStep (fun _ => 0) h r = r`; `antitheticBM 0 B t ω = B 0 ω`; `reverseFirstStep H B H ω = B H ω - B 0 ω`; `iIndepFun` over `Fin 0` already gives `IsProbabilityMeasure μ`; the real `⨆` of an unbounded family is `0`. |

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 0 | `implicitPathMult` | def | n/a (drift-implicit Euler–Maruyama scheme) | n/a | `invFun` returns an arbitrary value when $y-ha(y)=r$ has no solution. No theorem reaches that branch. |
| 1 | `implicitPathMult_second_moment_le` | theorem | true | no | no |
| 2 | `implicitPathMult_second_moment_sharp` | theorem | true (exact identity) | no | no (`hc` rules out $\sqrt{\text{negative}}=0$) |
| 3 | `implicitPathMult_second_moment_le_uniform` | theorem | true | no | no |
| 4 | `implicitPathMult_second_moment_le_div` | theorem | true | no | no ($N=0$ gives $T/0=0$, but $X_0=x_0$ does not depend on $h$) |
| 5 | `implicitCubicMult_second_moment_le` | theorem | true | no | no |
| 6 | `continuous_antitheticBM` | theorem | true (for every path) | no | no ($H=0$ is a degenerate constant path, from $t/0=0$ and truncated subtraction) |
| 7 | `isBrownianReal_antitheticBM` | theorem | true | no (mathematically; Mathlib has no constructed BM yet) | no |
| 8 | `iIndepFun_isBrownianReal_antitheticBM` | theorem | true | no (same caveat) | no |
| 9 | `isBrownianReal_reverseFirstStep` | theorem | true | no (same caveat) | no |
| 10 | `map_iSup_Icc_eq_of_isBrownianReal` | theorem | true | no (same caveat) | no (the real-`sSup` junk value can occur only on a null set) |
| 11 | `map_iSup_antitheticBM` | theorem | true | no (same caveat) | no |
| 12 | `nested_kinks_variance_rate` | theorem | true | no | no |
| 13 | `nested_kinks_bias_rate` | theorem | true | no | no |
| 14 | `nested_kinks_mlmc_complexity` | theorem | true | no | no (`∀ ℓ, 0 < N ℓ` blocks the $0^{-1}=0$ shortcut) |

## Main points for a human auditor

1. **All 14 theorems are true, none is vacuous, and none relies on a junk value.** I found no false statement.
2. **The implicit step never takes its unspecified value.** `implicitStep a h r = Function.invFun (y ↦ y - h a y) r`. In theorems 1, 3 and 4 the hypotheses are: $a$ continuous, $(a x-a y)(x-y)\le K(x-y)^2$, $h\ge0$ and $hK<1$ (in theorem 4, $TK<1$). Then $F(y)=y-ha(y)$ satisfies $(Fx-Fy)(x-y)\ge(1-hK)(x-y)^2>0$, so $F$ is an increasing homeomorphism of $\mathbb R$ and `invFun` returns the unique root. Theorem 2 uses $a=0$, where $F=\mathrm{id}$. Theorem 5 uses $a=-y^3$, where $F(y)=y+hy^3$.
   - Surjectivity already follows from continuity plus `hdiss`, since $y\,F(y)\ge y^2$. The one-sided Lipschitz hypothesis `hK`/`hhK` is needed only for uniqueness, and therefore for measurability.
3. **`hdiss : ∀ y, y * a y ≤ 0` is much stronger than the usual condition.** It is dissipativity with zero constant. It forces $a(0)=0$, and it excludes common drifts such as $x-x^3$ and mean reversion to a non-zero level, $\theta(m-x)$. The usual implicit-Euler moment bounds assume a monotone or coercivity condition such as $2xa(x)+b(x)^2\le\alpha+\beta x^2$. So theorems 1, 3, 4 and 5 are true but weaker than the standard result. The drift plays no part in the bound; this is why $a=0$ attains it.
4. **Sharpness.** Theorem 2 shows equality in the $(1+ch)^N$ bound, for $a=0$ and $b=\sqrt{c(1+x^2)}$. Nested Gauss–Hermite quadrature matches the formula to within $10^{-27}$. The $e^{cNh}$ and $e^{cT}$ forms are never attained when $ch>0$ and $N\ge1$; they are only approached as $h\to0$.
5. **Brownian motion in Mathlib.** `IsBrownianReal X P` means two things. Every finite-dimensional law is `projectiveFamily I`, the centred Gaussian with covariance $\min(s,t)$. And `∀ᵐ ω ∂P, Continuous (X · ω)`, i.e. paths are continuous **almost surely**.
   - Theorem 6 is a pathwise statement: `antitheticBM` is continuous for **every** $\omega$ at which $B(\cdot,\omega)$ is continuous, and it does not need $B_0=0$. So if every path of $B$ is continuous, every path of the reversed process is too.
   - `reverseFirstStep` is continuous only almost surely. It jumps by $B_0(\omega)$ at $t=H$ (shown in `brownian.out`).
   - $H\neq0$ is genuinely needed in theorems 7, 8 and 11: when $H=0$, `antitheticBM` is the constant $B_0$.
   - Exact rational covariance checks found 0 mismatches against $\min(s,t)$ in 20,000 random triples, for each of the two constructions.
6. **Running maximum.** The supremum is the real `⨆` over the compact interval `Set.Icc 0 T` in $\mathbb R_{\ge0}$, of $F(t,X_t)$ with $F$ jointly continuous. It is taken jointly with $X_T$.
   - Measurability is stated as `AEMeasurable`, not `Measurable`. That is the right notion here, because paths are continuous only almost surely.
   - Lean's real `sSup` returns $0$ for an unbounded family, but that can happen only on the null set of discontinuous paths.
   - The equality of laws is a real equality of probability measures, because the first conjunct rules out the `map` of a non-measurable function being $0$.
   - Monte Carlo two-sample KS tests are consistent with equal laws. On a grid aligned with $H$, the antithetic path uses $B$'s increments at distinct indices.
7. **Kinked payoffs.**
   - The rates are right and sharp. In exact computations, $2^{3\ell/2}E[\Delta_{\ell+1}^2]$ and $2^\ell|\text{bias}_\ell|$ converge to positive constants.
   - The constants are very generous: the computed values are at most about $1.4\cdot10^{-3}$ (variance) and $7\cdot10^{-3}$ (bias) of the stated right-hand sides.
   - The small-ball hypothesis is essential. Taking $\nu=\delta_k$ violates it, and then the scaled variance and the scaled bias both grow like $2^{\ell/2}$, i.e. $\beta=1$ and $\alpha=1/2$.
   - `hfib` asks for a uniform-in-$z$ bound on the *uncentred* fourth moment. That is stronger than some assumptions in the literature, but natural for the clean $3/2$ rate.
   - Covered payoffs are $C^{1,1}$ functions plus finitely many hinges (calls, $|x-k|$, max or min of affine functions). Discontinuous payoffs, such as the indicators used for VaR, are not covered.
8. **Vacuity caveat for theorems 7–11.** Mathlib at this commit defines `IsBrownianReal` but does not construct a Brownian motion; the module notes that Kolmogorov extension is "not in Mathlib yet". These statements are non-vacuous mathematically, because Wiener measure exists, but no Lean witness is available.

## Numerical evidence (all scripts in `work_R24/`)

| script | what it checks | result |
|---|---|---|
| `moments.py` | Monte Carlo of the scheme for $a=0$; for $a=-y^3$, $b=\sigma x$; and for a non-monotone drift $a(y)=-\arctan(y)(1+0.9\sin y)$ (numerical $K\approx1.394$, $y\,a(y)\le0$); also the pointwise contraction $\lvert Y\rvert\le\lvert R\rvert$ | All values are below the bounds. Cubic case: $E X_N^2\approx0.16$–$0.36$ against bounds $4.4$–$93.9$. $\max(\lvert Y\rvert-\lvert R\rvert)=0$. |
| `sharp_quadrature.py` | Theorem 2 identity for $N\le3$, by nested Gauss–Hermite quadrature | Differences $\le1.2\cdot10^{-27}$. With $c<0$ (excluded by `hc`) the formula fails ($1.0$ vs $0.71$). |
| `brownian.py` | Exact covariance of both reversals; the $H=0$ degeneracy; continuity on a fixed path with $B_0=1$ | 0/20,000 mismatches for each construction. `antitheticBM` is continuous; `reverseFirstStep` jumps by $B_0$ at $H$. |
| `running_max.py`, `running_max_seeds.py` | Law of $(\max F(t,W_t),W_T)$ against $B$, for three choices of $F$, with $T/H$ not an integer; distinct-increment check | KS statistics are within the null range across seeds. Increments are distinct, so the discrete laws are identical. |
| `kinks_exact.py`, `kinks_exact2.py` | Exact level variance and bias for $g=z+w$, $z\sim U[-A,A]$, $w=\pm s$, $f=\tfrac K2x^2+c(x-k)^+$; plus the Dirac (hypothesis-violating) case | Plateaus such as $0.005877$ and $0.1175$ (the latter matches the asymptotic prediction $0.11754$). Ratios to the right-hand side are $\le1.4\cdot10^{-3}$ (variance) and $\le7\cdot10^{-3}$ (bias). In the Dirac case both scaled quantities grow $\propto2^{\ell/2}$. |
| `kinks_mc.py` | Heteroscedastic Gaussian inner noise; softplus plus two kinks | Scaled variance plateaus at $\approx0.32$ (right-hand side $12628$). $2^\ell\lvert\text{bias}\rvert\to0.4587$ (right-hand side $12782$). |
| `mlmc_complexity.py` | MLMC runs and planned cost | $\text{MSE}/\varepsilon^2\approx0.43$–$0.58$. $\text{cost}\cdot\varepsilon^2$ is $13.6\to26.4$ in the runs ($\varepsilon=0.08\ldots0.01$) and saturates near $52$ in the planned table down to $\varepsilon=10^{-8}$. |

---

## Appended definitions (rendering only)

- **`implicitStep a h r`** $=\texttt{invFun}(y\mapsto y-h\,a(y))(r)$. If some $y$ solves $y-ha(y)=r$, it returns a chosen solution (`Classical.choose`); otherwise it returns `Classical.arbitrary ℝ`.
- **`antitheticBM H B t ω`**. Let $k=\lfloor t/H\rfloor$, computed in $\mathbb R_{\ge0}$ with $t/0=0$. Then
  $$W_t=B_{kH}+B_{(k+1)H}-B_{kH+(k+1)H-t}.$$
  The last time uses truncated subtraction; for $H>0$ it never truncates, because $t<(k+1)H$. On $[kH,(k+1)H)$ this is $B_{kH}$ plus the time reversal of $B$'s increment over that block. Hence $W_{kH}=B_{kH}$ on the grid. When $H=0$, $W\equiv B_0$.
- **`reverseFirstStep H B t ω`** $=B_H-B_{H-t}$ if $t\le H$, and $=B_t$ otherwise.
- **`innerMean g M z w`** $=M^{-1}\sum_{m<M}g(z,w_m)$, with $M$ cast to $\mathbb R$.
- **`shiftSeq M w`** $=(w_{M+m})_{m}$.
- **`innerLaw ρ`** $=\rho^{\otimes\mathbb N}$ (`Measure.infinitePi`). This requires `[IsProbabilityMeasure ρ]`; the packet omits that instance argument, but it is present in every use.
- **`nestedLaw ν ρ`** $=\nu\otimes\rho^{\otimes\mathbb N}$.
- **`nestedP f g ℓ (z,w)`** $=f(\text{innerMean } g\;2^\ell\;z\;w)$.
- **`nestedDelta f g`**. At level 0 it is `nestedP f g 0` $=f(g(z,w_0))$. At level $\ell+1$, with $M=2^\ell$,
  $$\Delta_{\ell+1}=f(\bar a_{2M})-\tfrac12f(\bar a_M)-\tfrac12f(\bar a'_M),$$
  where $\bar a_M$ averages $w_0..w_{M-1}$ and $\bar a'_M$ averages $w_M..w_{2M-1}$. This is the antithetic nested difference; note $\bar a_{2M}=(\bar a_M+\bar a'_M)/2$.
- **`nestedTarget f g ρ (z,w)`** $=f\big(\int g(z,v)\,d\rho(v)\big)$.
- **`blockMean F ω i N x`** $=N^{-1}\sum_{n<N}F_i(\omega(i,n)(x))$, with $0^{-1}=0$.
- **`totalCost cost L N x`** $=\sum_{\ell\le L}\sum_{n<N_\ell}\text{cost}(\ell,n,x)$.

---

## 0. `implicitPathMult` (definition)

**Rendering.** For $a,b:\mathbb R\to\mathbb R$, step $h$, start $x_0$ and a sequence $z$:
$$X_0=x_0,\qquad X_{n+1}=\texttt{implicitStep}\,a\,h\big(X_n+b(X_n)\sqrt h\,z_n\big).$$
So $X_{n+1}$ is a solution $y$ of $y-h\,a(y)=X_n+b(X_n)\sqrt h\,z_n$. Here $\sqrt h$ is `Real.sqrt`, equal to $0$ for $h<0$.

**Assessment.** This is the standard drift-implicit (backward) Euler–Maruyama scheme for $dX=a(X)\,dt+b(X)\,dW$, with $\Delta W_n=\sqrt h\,z_n$. Uniqueness of the root is not built in; every theorem below supplies it (see point 2).

## 1. `implicitPathMult_second_moment_le`

**Rendering.** Hypotheses:
- $a$ is continuous and one-sided Lipschitz: $(a(x)-a(y))(x-y)\le K(x-y)^2$.
- $y\,a(y)\le0$ for all $y$.
- $h\ge0$ and $hK<1$.
- $b$ is Borel measurable with $b(x)^2\le c(1+x^2)$. This forces $c\ge0$.
- $Z_n\sim N(0,1)$ under $\mu$ for $n<N$, and $(Z_0,\dots,Z_{N-1})$ are mutually independent. `iIndepFun` alone forces $\mu$ to be a probability measure, even when $N=0$.

Conclusion: $X_N\in L^2(\mu)$, $\;E X_N^2\le(x_0^2+1)(1+ch)^N-1$, and $E X_N^2\le(x_0^2+1)e^{cNh}-1$, with $N$ cast to $\mathbb R$.

**Assessment.** True.
- *Proof.* $F(y)=y-ha(y)$ is a strictly increasing homeomorphism, so $Y=F^{-1}(R)$. Then $Y^2=YR+hYa(Y)\le YR$, hence $\lvert Y\rvert\le\lvert R\rvert$. With $R=X+b(X)\sqrt hZ$ and $Z$ independent of $X$, $E R^2=EX^2+hEb(X)^2\le(1+ch)EX^2+ch$. So $EX_{n+1}^2+1\le(1+ch)(EX_n^2+1)$; finish by induction and $1+x\le e^x$.
- *Measurability.* $X_N$ is a continuous/measurable function of the AE-measurable $Z_n$. AE-measurability holds because `map` is nonzero.
- *Non-vacuous.* For example $a=-y^3$ (with $K=0$), $b=x$, $c=1$, $h=0.1$, and $Z_n$ the coordinates under `infinitePi (fun _ => gaussianReal 0 1)`.
- *No junk dependence.* The MemLp conjunct guards against the Bochner-integral junk value, and the `invFun` arbitrary branch is unreachable. When $N=0$ the bound holds with equality.
- *Unusual hypothesis.* `hdiss` is a strong, non-standard sufficient condition (see point 3). `hK`/`hhK` serve only uniqueness.
- *Standard fact.* This is a discrete-Gronwall mean-square bound for backward Euler under dissipativity and linear growth of the diffusion (cf. Higham–Mao–Stuart 2002; Mao–Szpruch 2013).
- *Numerics.* `moments.py`.

## 2. `implicitPathMult_second_moment_sharp`

**Rendering.** Let $h\ge0$, $c\ge0$, and let $Z$ be as above. With $a\equiv0$ (so the implicit step is the identity) and $b(x)=\sqrt{c(1+x^2)}$: $X_N\in L^2$ and $E X_N^2=(x_0^2+1)(1+ch)^N-1$ **exactly**.

**Assessment.** True. The exact recursion is $EX_{n+1}^2=EX_n^2+ch(1+EX_n^2)$. Quadrature confirms it to within $10^{-27}$ (`sharp_quadrature.py`).
- This shows the first bound of theorem 1 is attained: $a=0$ satisfies `hdiss` and `hK` with $K=0$, and $b^2=c(1+x^2)$ holds with equality.
- It does **not** show the exponential forms are attained.
- `hc` is necessary: for $c<0$, Lean's $\sqrt{\cdot}=0$ makes $b\equiv0$ and the identity fails.
- Non-vacuous (same $Z$). No junk dependence.

## 3. `implicitPathMult_second_moment_le_uniform`

**Rendering.** The hypotheses of theorem 1 plus $Nh\le T$, with $N$ cast to $\mathbb R$. Conclusion: $X_N\in L^2$ and $EX_N^2\le(x_0^2+1)e^{cT}-1$. Note $T\ge0$ is implied.

**Assessment.** True, from theorem 1 and the monotonicity of $\exp$ (since $c\ge0$). Non-vacuous; no junk dependence. The same remark on `hdiss` applies. This is the step-size-uniform Gronwall bound.

## 4. `implicitPathMult_second_moment_le_div`

**Rendering.** Hypotheses as in theorem 1, but with $h=T/N$ (real division; $T/0=0$), $T\ge0$ and $TK<1$, for every $N\in\mathbb N$. Conclusion: $X_N\in L^2$ and $EX_N^2\le(x_0^2+1)e^{cT}-1$.

**Assessment.** True.
- For $N\ge1$: $h=T/N\ge0$ and $Nh=T$. Also $hK=TK/N<1$: if $K>0$ then $TK/N\le TK<1$, and if $K\le0$ then $hK\le0$. Theorem 3 then applies.
- For $N=0$: $X_0=x_0$ does not depend on the junk $h=0$, and $x_0^2\le(x_0^2+1)e^{cT}-1$ holds because $e^{cT}\ge1$.
- `hTK` is exactly the $N=1$ requirement, so it is natural.
- Non-vacuous; no junk dependence. This is the equidistant-grid version of the same bound.

## 5. `implicitCubicMult_second_moment_le`

**Rendering.** For any $\sigma,x_0$, $h\ge0$ and $Nh\le T$, with $Z$ as above: the scheme with $a(y)=-y^3$ and $b(x)=\sigma x$ satisfies $X_N\in L^2$ and $EX_N^2\le(x_0^2+1)e^{\sigma^2T}-1$.

**Assessment.** True; it is an instance of theorem 3.
- $K=0$ works, because $-(x^3-y^3)(x-y)=-(x-y)^2(x^2+xy+y^2)\le0$.
- $y\,a(y)=-y^4\le0$, and $c=\sigma^2$.
- The step solves $y+hy^3=r$, which has a unique real root.
- The bound is loose: one actually has $EX_N^2\le x_0^2(1+\sigma^2h)^N$, and Monte Carlo gives $\approx0.16$–$0.36$ against bounds $4.4$–$93.9$ (`moments.py`).
- Non-vacuous; no junk dependence. The setting is cubic damping with linear multiplicative noise.

## 6. `continuous_antitheticBM`

**Rendering.** For every $H\in\mathbb R_{\ge0}$, every $B:\mathbb R_{\ge0}\to\Omega\to\mathbb R$ and every $\omega$ such that $t\mapsto B_t(\omega)$ is continuous, the map $t\mapsto W_t(\omega)$ (`antitheticBM`) is continuous. No measure is involved, and it holds for every such $\omega$.

**Assessment.** True.
- On $[kH,(k+1)H)$, $W_t=B_{kH}+B_{(k+1)H}-B_{(2k+1)H-t}$ is continuous. The left limit at $(k+1)H$ is $B_{(k+1)H}=W_{(k+1)H}$.
- $B_0=0$ is not needed (`brownian.py`, with a path having $B_0=1$).
- When $H=0$, $W\equiv B_0$ by $t/0=0$ and truncated subtraction. That case is trivially continuous; it is junk-degenerate but harmless.
- Non-vacuous: take any continuous path.

## 7. `isBrownianReal_antitheticBM`

**Rendering.** If $B$ is a Brownian motion under $P$ in Mathlib's sense and $H\ne0$, then $W=$ `antitheticBM H B` is a Brownian motion in the same sense. Mathlib's sense means: for every finite $I$, the law of $(B_t)_{t\in I}$ is `projectiveFamily I`, the centred Gaussian with covariance $\min(s,t)$; and paths are continuous $P$-a.s.

**Assessment.** True.
- $W$ is a linear image of $B$, so it is centred Gaussian. Its covariance is $\min(s,t)$, checked exactly on 20,000 random rational triples with 0 mismatches.
- Equivalently, $W$ concatenates the independent block reversals $B_{(k+1)H}-B_{(k+1)H-s}$.
- Almost-sure continuity follows from theorem 6. `IsBrownianReal` asks only for a.s. continuity, and that is what is concluded.
- $H\ne0$ is needed: $H=0$ gives the constant $B_0$.
- Non-vacuous mathematically (Wiener measure). Mathlib has no constructed BM at this commit. No junk dependence.
- *Standard fact.* Time reversal of Brownian increments on a bounded interval is a Brownian motion; combine with independent increments.

## 8. `iIndepFun_isBrownianReal_antitheticBM`

**Rendering.** Let $(B^i)_{i\in\iota}$ be Brownian motions that are mutually independent as random elements of $\mathbb R^{\mathbb R_{\ge0}}$ (product σ-algebra), and let $H\ne0$. Then every $W^i=$ `antitheticBM H B^i` is a Brownian motion, and the $W^i$ are mutually independent.

**Assessment.** True. $W^i=\Phi_H\circ B^i$, where $\Phi_H$ is measurable for the product σ-algebra: each coordinate is a combination of three coordinates. Then apply theorem 7 and `iIndepFun.comp`. Non-vacuous: two independent BMs on a product space (same caveat as theorem 7). No junk dependence.

## 9. `isBrownianReal_reverseFirstStep`

**Rendering.** If $B$ is a Brownian motion, then so is $R_t=B_H-B_{H-t}$ for $t\le H$, with $R_t=B_t$ for $t>H$. This holds for every $H\ge0$, including $H=0$, where $R_0=0$ and $R=B$ elsewhere.

**Assessment.** True.
- The covariance is exactly $\min(s,t)$ (0/20,000 mismatches). For $t>H$, $R_t=R_H+(B_t-B_H)$ a.s., and these increments are independent of $\sigma(B_s:s\le H)$.
- Paths are continuous only a.s.: at $t=H$ the path jumps by $B_0(\omega)$. There is no pathwise analogue of theorem 6, and none would hold.
- Non-vacuous (same caveat). No junk dependence; the subtraction $H-t$ with $t\le H$ never truncates.

## 10. `map_iSup_Icc_eq_of_isBrownianReal`

**Rendering.** Let $X$ be a Brownian motion on $(\Omega,P)$ and $Y$ one on $(\Omega',P')$. Let $F:\mathbb R_{\ge0}\times\mathbb R\to\mathbb R$ be jointly continuous and $T\in\mathbb R_{\ge0}$. Then:
- $\omega\mapsto\big(\sup_{t\in[0,T]}F(t,X_t(\omega)),\,X_T(\omega)\big)$ is $P$-a.e. measurable; and
- its law under $P$ equals the law of the corresponding pair for $Y$ under $P'$.

The supremum is the real `⨆` over `Set.Icc 0 T`, a compact interval of $\mathbb R_{\ge0}$, and it equals $0$ if the family is unbounded.

**Assessment.** True.
- On the full-measure set of continuous paths, the supremum equals the supremum over the countable dense set $(\mathbb Q\cap[0,T])\cup\{T\}$. So the pair is a.e. a measurable function of countably many coordinates.
- The joint law of those coordinates is fixed by the finite-dimensional laws (π–λ argument on cylinder sets).
- The junk value can occur only on a null set.
- `AEMeasurable` is the appropriate claim. The equality is non-trivial, because the first conjunct ensures `map` is not $0$.
- Non-vacuous: $X=Y=$ BM, $F(t,x)=x$ (same caveat). No junk dependence.
- *Standard fact.* The law of a continuous-path process is determined by its finite-dimensional laws (uniqueness of Wiener measure); this is the joint law of running max and endpoint, as in the reflection principle.

## 11. `map_iSup_antitheticBM`

**Rendering.** Let $B$ be a Brownian motion, $H\ne0$, $F$ jointly continuous and $T\ge0$. Then $\big(\sup_{[0,T]}F(t,W_t),W_T\big)$ is a.e. measurable and has the same law under $P$ as $\big(\sup_{[0,T]}F(t,B_t),B_T\big)$.

**Assessment.** True; it is theorem 10 applied to theorem 7.
- Monte Carlo with $T/H=3.33$ and $F\in\{x,\;x-t/2,\;\lvert x\rvert\}$: KS statistics are within the null distribution across seeds.
- On an $H$-aligned grid, $W$'s increments are $B$'s increments at distinct indices, so the discrete laws coincide (`running_max*.py`).
- Non-vacuous (same caveat). No junk dependence.
- This is the law-invariance needed for antithetic MLMC of path-dependent (lookback or barrier type) functionals.

## 12. `nested_kinks_variance_rate`

**Rendering.** Setting: probability spaces $(\mathcal Z,\nu)$ and $(\mathcal W,\rho)$, and a jointly measurable $g$. Write $\mu(z)=\int g(z,v)\,d\rho$. Hypotheses:
- $f=f_0+\sum_{i\in\iota}c_i(x-k_i)^+$, with $\iota$ finite.
- $f_0$ is differentiable everywhere and $f_0'$ is $K$-Lipschitz. This forces $K\ge0$.
- For $\nu$-a.e. $z$: $g(z,\cdot)^4\in L^1(\rho)$ and $\int g(z,v)^4\,d\rho\le m_4$. This is an uncentred bound, uniform in $z$, and forces $m_4\ge0$.
- For all $i$ and all $t>0$: $\nu\{\lvert\mu(z)-k_i\rvert\le t\}\le c_{d,i}\,t$. This forces $c_{d,i}>0$.

Conclusion, for every $\ell\in\mathbb N$: $\Delta_{\ell+1}\in L^2(\nu\otimes\rho^{\otimes\mathbb N})$ and
$$2^{3\ell/2}\,E[\Delta_{\ell+1}^2]\le(\lvert\iota\rvert+1)\Big[(K/8)^2\,224\,m_4+\sum_ic_i^2\,2c_{d,i}\sqrt{8m_4(1+16m_4)}\Big].$$
Here $2^{3\ell/2}$ is a real power (`rpow`).

**Assessment.** True.
- *Smooth part.* By Taylor, $\lvert\Delta_{f_0}\rvert\le\frac K8(\bar a_M-\bar a'_M)^2$, and $E(\bar a_M-\bar a'_M)^4\le28m_4/M^2$. So this part is $O(2^{-2\ell})$.
- *Kink part.* $\Delta_\varphi\ne0$ only if $k$ lies between the two half-means, and then $\lvert\Delta_\varphi\rvert\le\lvert\bar a_M-\bar a'_M\rvert/4$. Conditional Cauchy–Schwarz and Markov's inequality with fourth moments give $\min(1,C/(MD^2))$, and the small-ball layer cake gives $2c_d\sqrt{C/M}$. Together this is $O(M^{-3/2})$.
- The combination uses $\big(\sum_{j=0}^{n}x_j\big)^2\le(n+1)\sum_jx_j^2$.
- Exact computations show the rate is sharp (scaled variance converges to a positive constant), and the constant is very generous (ratio at most $1.4\cdot10^{-3}$).
- The hypothesis `hball` is essential: under $\nu=\delta_k$ the scaled variance grows like $2^{\ell/2}$.
- `hfib` is uniform in $z$ and uncentred, which is stronger than global-moment versions in the literature but natural.
- Non-vacuous: $z\sim U[-1,1]$, $w=\pm\frac12$, $g=z+w$, $f=\frac12x^2+x^+$ ($K=1$, $c_d=1$, $m_4=2.5625$).
- No junk dependence: the MemLp conjunct; $2^\ell\ge1$ so no $0^{-1}$; the square root's argument is $\ge0$; any non-integrable $\int g\,d\rho$ occurs only on a $\nu$-null set.
- *Standard fact.* The antithetic nested-MLMC variance rate $V_\ell=O(M_\ell^{-3/2})$ for payoffs with kinks under a bounded-density condition (Bujok–Hambly–Reisinger 2015; Giles 2015; Giles–Goda 2019).

## 13. `nested_kinks_bias_rate`

**Rendering.** Same $f$, $f_0$ and `hball`. Also: $g$ jointly measurable with $g^4\in L^1(\nu\otimes\rho)$, and for $\nu$-a.e. $z$ the **centred** fourth moment satisfies $\int(g(z,v)-\mu(z))^4\,d\rho\le m_4$. Conclusion, for every $\ell$: $P_\ell-f(\mu)\in L^1$ and
$$2^\ell\,\big\lvert E[P_\ell-f(\mu(z))]\big\rvert\le\frac K2\big(1+16\,E_{\nu\otimes\rho}g^4\big)+\sum_i\lvert c_i\rvert\,3c_{d,i}(1+80m_4).$$

**Assessment.** True.
- *Smooth part.* $\lvert E f_0(\bar a)-f_0(\mu)\rvert\le\frac K2E\operatorname{Var}_z(g)/M$, since the linear term has conditional mean zero.
- *Kink part.* $E\big[\lvert\bar a-\mu\rvert\,1\{\lvert\bar a-\mu\rvert\ge\lvert\mu-k\rvert\}\big]$ is bounded via $\min(s,\;s^2/d,\;3m_4/(M^2d^3))$ and the small-ball bound, giving $O(1/M)$.
- Exact computations show $2^\ell\lvert\text{bias}\rvert$ converges to a positive constant: $\alpha=1$ is sharp. Ratios to the right-hand side are at most $7\cdot10^{-3}$.
- `hball` is essential: under $\nu=\delta_k$, $2^\ell\lvert\text{bias}\rvert\propto2^{\ell/2}$.
- Non-vacuous: the same example, with $m_4=s^4$. No junk dependence: the Integrable conjunct, and integrals of non-integrable functions occur only on null sets.
- *Standard fact.* The $O(1/M)$ bias of nested simulation (cf. Gordy–Juneja 2010; Giles–Haji-Ali 2019) for $C^{1,1}$ payoffs plus kinks.

## 14. `nested_kinks_mlmc_complexity`

**Rendering.** Assume the hypotheses of theorem 12. Assume also:
- samples $\omega(\ell,n):\Omega\to\mathcal Z\times\mathcal W^{\mathbb N}$, each with law $\nu\otimes\rho^{\otimes\mathbb N}$ under $\mu$, and the whole family over $\mathbb N\times\mathbb N$ mutually independent;
- integrable costs with $E\,\text{cost}(\ell,n)=C_\ell\le c_3\,2^\ell$, where $c_3>0$.

Conclusion: there is $c_4>0$ (independent of $\varepsilon$) such that for every $\varepsilon\in(0,e^{-1})$ there exist $L$ and $N:\mathbb N\to\mathbb N$ with all $N_\ell\ge1$ for which
$$\hat Y=\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}\Delta_\ell(\omega(\ell,n))$$
satisfies: $(\hat Y-E_\nu f(\mu))^2$ is integrable, $E(\hat Y-E_\nu f(\mu))^2<\varepsilon^2$, and $E[\text{totalCost}]=\sum_{\ell\le L}N_\ell C_\ell\le c_4\varepsilon^{-2}$.

**Assessment.** True.
- This is the MLMC complexity theorem (Giles 2008; Cliffe–Giles–Scheichl–Teckentrup 2011) with $\alpha=1$, $\beta=3/2$ and $\gamma=1$. Since $\beta>\gamma$, the cost is $O(\varepsilon^{-2})$.
- $\alpha=1$ comes from theorem 13, whose hypotheses follow from `hfib`: $Eg^4\le m_4$, and the centred fourth moment is $\le16m_4$.
- $\beta=3/2$ comes from theorem 12; $V_0<\infty$ by quadratic growth of $f$ and the bound on the fourth moment.
- Telescoping works because `shiftSeq` preserves $\rho^{\otimes\mathbb N}$.
- Simulation: $\text{MSE}/\varepsilon^2\approx0.43$–$0.58$, and $\text{cost}\cdot\varepsilon^2$ saturates near $52$.
- The restriction $\varepsilon<e^{-1}$ is cosmetic. Costs are only bounded above, possibly negative, which is harmless.
- `∀ ℓ, 0 < N ℓ` blocks a $0^{-1}=0$ shortcut, such as a zero-cost, zero estimator when the target is $0$. The expected cost is a genuine integral (`hcost`).
- Non-vacuous: the example of theorem 12, with $\Omega$ an `infinitePi` of copies of `nestedLaw`, $\omega$ the coordinate maps, and $\text{cost}(\ell,n)\equiv2^\ell$ ($c_3=1$). No junk dependence.
