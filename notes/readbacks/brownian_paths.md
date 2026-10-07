# Blind read-back report: R17 (Brownian-path constructions)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round17/packet_R17_brownian.lean` |
| declarations audited | 21 (14 theorems + 7 definitions) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round17/work_R17/` |

Scripts (each with a `.out` of the same name):

- `cov_reversal.py`: exact-rational covariance check of `antitheticBM` and `reverseFirstStep` against $\min(s,t)$ (39,605 $(H,s,t)$ triples each, including grid points, midpoints and $H=0$), with NNReal truncated subtraction, $x/0=0$ and `Nat.floor` modelled; it also checks the pathwise identities.
- `symbolic_cases.py`: sympy case analysis of the same covariances (same coarse step / different steps; $s\le t\le H$, $s\le H<t$, $H<s$), the bridge-midpoint variances and covariances, and union-grid telescoping.
- `union_grid_exact.py`: exact check, over random monotone grids with repeated values and repeated indices, that union-grid increments use disjoint blocks and have variance $u(\tau_{j+1})-u(\tau_j)$.
- `Scratch.lean`: a scratch copy of the packet (proofs `sorry`), compiled against Mathlib alone, to confirm elaboration and casts. Its one error, at line 77, is my own first failed proof attempt for `bridgeInterp_weighted_sum`; `Det.lean` redoes it successfully.
- `Det.lean`: complete Lean proofs, with no `sorry`, of `bridgeInterp_weighted_sum`, `antitheticBM_natCast_mul` and `fineIncrements_antitheticBM`. `reverseFirstStep_fineIncrements` was proved in `Scratch.lean` and compiled without error.

Transparency note: I read the one-line `lean-toolchain` file of the repository (`v4.33.1`, as already stated in the rules). I opened no other repository file except Mathlib sources.

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `iIndepFun_blockSum` | theorem | True | No | No |
| 2 | `unionGridBM` | def | n/a | n/a | n/a (`√` is applied only to nonnegative values when `u` is monotone) |
| 3 | `unionGridBM_increments` | theorem | True | No | No (`.toNNReal` is the identity under `hu`, `hτ`) |
| 4 | `unionGridBM_hasLaw` | theorem | True | No | No |
| 5 | `unionGridBM_map_eq` | theorem | True | No | No |
| 6 | `unionGrid_brownian_map_eq` | theorem | True | No | No. It is only the conjunction of two instances of #5 and makes no joint (coupling) claim. |
| 7 | `bridge_midpoint_law` | theorem | True | No | No |
| 8 | `brownian_bridge_midpoint` | theorem | True | No | No |
| 9 | `bridgeInterp` | def | n/a | n/a | n/a |
| 10 | `bridgeInterp_weighted_sum` | theorem | True (proved in Lean) | No | No |
| 11 | `antitheticBM` | def | n/a | n/a | For $H=0$ it collapses to $B(0)$ via $t/0=0$; for $H>0$ the NNReal subtraction never truncates. |
| 12 | `isPreBrownianReal_antitheticBM` | theorem | True | No | No (`hH` is necessary) |
| 13 | `iIndepFun_antitheticBM` | theorem | True | No | No |
| 14 | `antitheticBM_natCast_mul` | theorem | True (proved in Lean) | No | No. The $H=0$ case uses $0/0=0$, but both sides are then $B(0)$. |
| 15 | `fineIncrements` | def | n/a | n/a | n/a |
| 16 | `fineIncrements_antitheticBM` | theorem | True (proved in Lean) | No | No. At $h=0$ both sides are $0$. |
| 17 | `reverseFirstStep` | def | n/a | n/a | n/a ($H-t$ is exact when $t\le H$) |
| 18 | `isPreBrownianReal_reverseFirstStep` | theorem | True | No | No |
| 19 | `reverseFirstStep_fineIncrements` | theorem | True (proved in Lean) | No | No |
| 20 | `swapIncrements` | def | n/a | n/a | n/a |
| 21 | `pairSwap` | def | n/a | n/a | n/a (ℕ subtraction $i-1$ is exact for odd $i$) |

## Main points for a human auditor

1. **All 14 theorems are true as stated.** None is vacuous, and none holds only through a junk value. No false statement was found.
2. **`unionGrid_brownian_map_eq` (#6) is weaker than its name suggests.** It is literally two independent copies of `unionGridBM_map_eq`, one for $\tau_f$ and one for $\tau_c$. It asserts only the *marginal* law of the fine increment vector and, separately, of the coarse one. It says nothing about their *joint* law, which is the MLMC coupling. No hypothesis links $\tau_f$, $\tau_c$ and $u$ (for example, that $u$ is their union, or that $\tau_c$ is a subsequence of $\tau_f$).
   - Marginal laws are what the telescoping (unbiasedness) step needs.
   - The joint law does follow from #3 applied with $\tau=\mathrm{id}$, since the union-grid increments are then independent $N(0,\Delta u_i)$.
   - Using the same $Z_j$ on both right-hand sides has no joint meaning, because each equation is a separate equality of image measures.
3. **Degenerate cases behave correctly.**
   - Empty blocks (`S k = ∅`) and repeated grid indices ($\tau_{j+1}=\tau_j$) give the sum $0 \sim N(0,0)=\delta_0$, which matches the claimed variance $0$.
   - Repeated grid values ($u_{i+1}=u_i$) give $\sqrt0\,Z_i=0$.
   - $n=0$ is fine, because `iIndepFun` (empty finset) and `HasLaw … gaussianReal` both force $\mu$ to be a probability measure.
   - Coarse step $H=0$ is excluded by `hH` in #12 and #13, and the exclusion is necessary: `antitheticBM 0 B t = B 0` for all $t$, which is not pre-Brownian (`cov_reversal.py` shows the mismatch).
   - The pathwise identities (#14, #16, #19) also hold, trivially, at $H=0$ or $h=0$.
4. **The time-reversed process really is pre-Brownian.** For $H>0$ and $t\in[kH,(k+1)H)$, $\tilde W(t)=B(kH)+B((k+1)H)-B((2k+1)H-t)$. The covariance is $\min(s,t)$ in every case: same coarse step (with $s\le t$, giving $a+b-(a+b-s)=s$) and different steps (giving $s$). This holds at grid points and at midpoints, checked symbolically (sympy) and exactly (39,605 rational triples). The NNReal truncated subtraction never truncates when $H>0$. `reverseFirstStep` also has covariance $\min(s,t)$ in all three cases, for every $H\ge0$, with no $H\neq0$ hypothesis needed.
5. **Several dimensions (#13).** The hypothesis is mutual independence of the component *paths* $\omega\mapsto(t\mapsto B_i(t,\omega))$, with the product σ-algebra on $\mathbb R_{\ge0}\to\mathbb R$ and an arbitrary index type. The conclusion is that each reflected component is pre-Brownian and that the reflected component paths are mutually independent. This is just composition with a measurable path map. Nothing is claimed about the joint law of $(B,\tilde B)$, which are of course dependent.

---

## Per-declaration sections

### 1. `iIndepFun_blockSum` (theorem)

**Rendering.** Let $(\Omega,\mu)$ be a measure space, $\iota,\kappa$ arbitrary types, $X_i:\Omega\to\mathbb R$, $m_i\in\mathbb R$, $v_i\in\mathbb R_{\ge0}$. Assume:

- $(X_i)_{i\in\iota}$ are mutually independent (`iIndepFun`, which forces $\mu(\Omega)=1$ through the empty finset);
- $X_i\sim N(m_i,v_i)$ (`HasLaw`: $X_i$ is a.e.-measurable and $\mu\circ X_i^{-1}=N(m_i,v_i)$, where variance $0$ means the Dirac mass);
- $S:\kappa\to\mathrm{Finset}\,\iota$ has pairwise disjoint values ($k\ne k'\Rightarrow S_k\cap S_{k'}=\emptyset$).

Then the block sums $Y_k=\sum_{i\in S_k}X_i$ are mutually independent, and $Y_k\sim N\big(\sum_{i\in S_k}m_i,\ \sum_{i\in S_k}v_i\big)$ for every $k$.

**Assessment.**

- *Truth:* true. Functions of disjoint subfamilies of an independent family are independent. A finite sum of independent Gaussians is Gaussian, with means and variances adding (convolution of `gaussianReal`).
- *Empty block:* $Y_k=0$ and $N(0,0)=\delta_0$ ✓. Constants are independent of everything ✓.
- *Infinite $\kappa$:* fine, since `iIndepFun` concerns finite subfamilies.
- *Vacuity:* not vacuous. Take $\Omega=\mathbb R^{\mathbb N}$ with `Measure.infinitePi (fun _ => gaussianReal 0 1)`, $X_i$ the coordinates, $S_k=\{2k,2k+1\}$.
- *Junk:* none.
- *Hypotheses:* standard and not stronger than needed.

**Standard fact:** independence of grouped variables, plus stability of the Gaussian family under independent sums.

### 2. `unionGridBM` (def)

**Rendering.** For $u:\mathbb N\to\mathbb R$, $z:\mathbb N\to\mathbb R$ and $k\in\mathbb N$, $\ \mathrm{unionGridBM}(u,z,k)=\sum_{i=0}^{k-1}\sqrt{u_{i+1}-u_i}\,z_i$. Here `Real.sqrt` of a negative number is $0$, but every theorem assumes $u$ monotone, so the argument is always $\ge0$. With i.i.d. $N(0,1)$ inputs $z_i$, this is the standard sampling of Brownian motion at the times $u_k$, relative to $u_0$, by summing scaled Gaussian increments.

### 3. `unionGridBM_increments` (theorem)

**Rendering.** Assume:

- $Z_i$ ($i\in\mathbb N$) are mutually independent, each $\sim N(0,1)$ under $\mu$;
- $u:\mathbb N\to\mathbb R$ is monotone (non-decreasing);
- $n\in\mathbb N$ and $\tau:\{0,\dots,n\}\to\mathbb N$ is monotone.

Put $D_j(\omega)=\mathrm{unionGridBM}(u,Z(\omega),\tau_{j+1})-\mathrm{unionGridBM}(u,Z(\omega),\tau_j)$ for $j<n$. Then $(D_j)_{j<n}$ are mutually independent, and $D_j\sim N\big(0,\ (u(\tau_{j+1})-u(\tau_j))^+\big)$.

**Assessment.**

- *Truth:* true. $D_j=\sum_{i=\tau_j}^{\tau_{j+1}-1}\sqrt{\Delta u_i}\,Z_i$. The index blocks $[\tau_j,\tau_{j+1})$ are pairwise disjoint because $\tau$ is monotone, so independence follows from #1. The variance telescopes: $\sum_i\Delta u_i=u(\tau_{j+1})-u(\tau_j)\ge0$. Confirmed exactly on 2,000 random grids with repeated values and indices (`union_grid_exact.py`).
- *`.toNNReal`:* the identity here, since the difference is $\ge0$ under `hu` and `hτ`. Not junk.
- *Degenerate cases:* a repeated $\tau$ gives an empty block and $N(0,0)=\delta_0$ ✓. A repeated $u$ gives a zero coefficient ✓. $n=0$ is a trivial statement ✓.
- *Vacuity:* not vacuous (the infinite product of $N(0,1)$, $u_i=i$, $\tau=\mathrm{id}$).
- *Hypotheses:* `hu` is needed. Without it, `√` of a negative number becomes $0$ and the telescoping fails.

**Standard fact:** a Gaussian random walk with step variances $\Delta u_i$ is Brownian motion sampled at the times $u_i$, and its increments over any monotone sub-index are independent $N(0,\Delta u)$.

### 4. `unionGridBM_hasLaw` (theorem)

**Rendering.** Same hypotheses as #3. The random vector $(D_j)_{j\in\mathrm{Fin}\,n}$ has law $\bigotimes_{j<n}N\big(0,(u(\tau_{j+1})-u(\tau_j))^+\big)$ (`Measure.pi`, the finite product of probability measures).

**Assessment.**

- *Truth:* true. For a finite index set, mutual independence plus the marginal laws (#3) is equivalent to the joint law being the product measure. With $n=0$ both sides are the Dirac mass on the unique point of `Fin 0 → ℝ`, using $\mu(\Omega)=1$.
- *Vacuity, junk:* not vacuous; no junk.

**Standard fact:** the Brownian increment vector has a product Gaussian law.

### 5. `unionGridBM_map_eq` (theorem)

**Rendering.** Same hypotheses as #3. The law of $(D_j)_{j<n}$ equals the law of $\big(\sqrt{u(\tau_{j+1})-u(\tau_j)}\,Z_j\big)_{j<n}$. On the right-hand side $Z_j$ is $Z_{\uparrow j}$, with $j:\mathrm{Fin}\,n$ cast to ℕ; this was checked by elaboration.

**Assessment.**

- *Truth:* true. Both vectors have independent coordinates with law $N(0,\Delta_j)$, so both laws equal the product measure of #4. The square root is applied to a nonnegative number.
- *Vacuity, junk:* not vacuous; no junk. Both maps are a.e.-measurable, so `Measure.map` is not the junk $0$.

**Standard fact:** BM increments on a grid can be generated as $\sqrt{\Delta t}\,Z$.

### 6. `unionGrid_brownian_map_eq` (theorem)

**Rendering.** Same i.i.d. $N(0,1)$ assumptions and monotone $u$. Let $\tau_f:\{0..n_f\}\to\mathbb N$ and $\tau_c:\{0..n_c\}\to\mathbb N$ be monotone. Then:

- (a) the law of the $\tau_f$-increment vector equals the law of $(\sqrt{\Delta^f_j}\,Z_j)_{j<n_f}$; **and**
- (b) the law of the $\tau_c$-increment vector equals the law of $(\sqrt{\Delta^c_j}\,Z_j)_{j<n_c}$.

**Assessment.**

- *Truth:* true. These are exactly #5 applied to $\tau_f$ and to $\tau_c$.
- *Vacuity, junk:* not vacuous; no junk.
- **Finding (weaker than the name suggests).** The statement contains only two *marginal* equalities in law. It makes no statement about the joint law of the (fine, coarse) pair. Nothing relates $\tau_f$ and $\tau_c$ to each other or to $u$: neither "u enumerates the union of the fine and coarse grids" nor "$\tau_c$ is a sub-grid" is assumed. The same $Z_j$ appear on both right-hand sides, but that has no joint meaning.
  - For MLMC telescoping (unbiasedness), marginals are what is needed.
  - The coupling, that fine and coarse come from one Brownian path, holds by construction. It is formally a consequence of #3 with $\tau=\mathrm{id}$, not of this theorem.

**Standard fact:** sampling BM on the union of two time grids gives the correct marginal law on each grid.

### 7. `bridge_midpoint_law` (theorem)

**Rendering.** Let $h\in\mathbb R_{\ge0}$, and let $dW_1,dW_2:\Omega\to\mathbb R$ be independent (`IndepFun`), each $\sim N(0,h/2)$. NNReal division is exact. Then:

- (i) $dW_1+dW_2\sim N(0,h)$;
- (ii) $(dW_1-dW_2)/2\sim N(0,h/4)$;
- (iii) $dW_1+dW_2$ and $(dW_1-dW_2)/2$ are independent;
- (iv) for all $\omega$ and all $W_0\in\mathbb R$, $W_0+dW_1=\tfrac{W_0+(W_0+dW_1+dW_2)}2+\tfrac{dW_1-dW_2}2$.

**Assessment.**

- *Truth:* true. For (i), variances add. For (ii), $\operatorname{Var}=(h/2+h/2)/4=h/4$. For (iii), $(dW_1,dW_2)$ is jointly Gaussian and $\operatorname{Cov}(a+b,(a-b)/2)=(\operatorname{Var}a-\operatorname{Var}b)/2=0$. For (iv), the residual simplifies to $0$ (`symbolic_cases.out`).
- *$h=0$:* everything is $\delta_0$ ✓.
- *Probability measure:* $\mu(\Omega)=1$ is forced by `HasLaw`, so the fact that `IndepFun` alone does not force a probability measure is irrelevant.
- *Vacuity, junk:* not vacuous; no junk. Conjunct (iv) is a pure algebraic identity that does not use the hypotheses.

**Standard fact:** Brownian bridge / Lévy midpoint refinement. The midpoint equals the average of the endpoints plus an independent $N(0,h/4)$ term.

### 8. `brownian_bridge_midpoint` (theorem)

**Rendering.** Let $B$ be a pre-Brownian motion on $(\Omega,\mu)$ (`IsPreBrownianReal`: for every finite $I\subset\mathbb R_{\ge0}$, $(B_t)_{t\in I}$ is centred Gaussian with covariance $\min(s,t)$). For all $s,h\in\mathbb R_{\ge0}$, put $M=B_{s+h/2}-\tfrac12(B_s+B_{s+h})$. Then:

- $M\sim N(0,h/4)$; and
- $M$ is independent of the pair $\big(B_{s+h},\ (B_r)_{r\in[0,s]}\big)$, valued in $\mathbb R\times\mathbb R^{[0,s]}$ with the product σ-algebra.

**Assessment.**

- *Truth:* true. By symbolic check, $\operatorname{Var}M=h/4$, $\operatorname{Cov}(M,B_{s+h})=0$, and $\operatorname{Cov}(M,B_r)=0$ for $r\le s$. Everything is jointly Gaussian (a pre-BM is a Gaussian process), so zero covariance with every finite subfamily gives independence from the generated σ-algebra. Mathlib uses the same mechanism in `IsPreBrownianReal.indepFun_shift`.
- *Degenerate cases:* $h=0$ gives $M=0\sim\delta_0$ ✓. $s=0$ ✓.
- *Vacuity:* not vacuous. Brownian motion exists, for example as the coordinate process under the Kolmogorov extension of Mathlib's `projectiveFamily` (shown projective in `isProjectiveMeasureFamily_projectiveFamily`), or via a Lévy construction. This Mathlib snapshot has no packaged instance.
- *Junk:* none.

**Standard fact:** Brownian bridge midpoint law. Conditional on $\mathcal F_s$ and $B_{s+h}$, $B_{s+h/2}\sim N\big(\tfrac{B_s+B_{s+h}}2,\tfrac h4\big)$.

### 9. `bridgeInterp` (def)

**Rendering.** $\mathrm{bridgeInterp}(S_0,S_1,b,W_0,W_1,W_t,\lambda)=S_0+\lambda(S_1-S_0)+b\big(W_t-W_0-\lambda(W_1-W_0)\big)$. This is linear interpolation between $S_0$ and $S_1$ plus $b$ times the Brownian-bridge fluctuation $W_t-[W_0+\lambda(W_1-W_0)]$.

### 10. `bridgeInterp_weighted_sum` (theorem)

**Rendering.** For any finset $s$ of indices and real families $w,S_0,S_1,b,W_0,W_1,W_t$, and $\lambda\in\mathbb R$:
$$\sum_{a\in s}w_a\,\mathrm{bridgeInterp}(S_{0a},S_{1a},b_a,W_{0a},W_{1a},W_{ta},\lambda)=\mathrm{bridgeInterp}\Big(\sum w S_0,\sum wS_1,1,\sum wbW_0,\sum wbW_1,\sum wbW_t,\lambda\Big).$$

**Assessment.**

- *Truth:* true. The expression is linear in $(S_0,S_1,bW_0,bW_1,bW_t)$ for fixed $\lambda$. **Proved in Lean** (`Det.lean`): `simp` distribution, then `ring` termwise.
- *Empty $s$:* both sides are $0$ ✓.
- *Vacuity, junk:* no hypotheses; no junk.

**Standard fact:** linearity of the bridge interpolant.

### 11. `antitheticBM` (def)

**Rendering.** For $H\in\mathbb R_{\ge0}$, a process $B$ and $t\ge0$, let $k=\lfloor t/H\rfloor_+$ (`Nat.floor` in ℝ≥0, with $t/0=0$), $a=kH$ and $b=(k+1)H$. Then $\mathrm{antitheticBM}(t)=B_a+B_b-B_{a+b\,\dot-\,t}$, where $\dot-$ is truncated NNReal subtraction.

- For $H>0$: $t\in[a,b)$, so $a+b-t\in(a,b]$ and no truncation occurs (checked).
- The process is $B$ with its path *time-reversed inside each coarse step* $[kH,(k+1)H]$: $\tilde W(t)-\tilde W(a)=B_b-B_{a+b-t}$.
- It agrees with $B$ at the coarse grid points and is continuous at them when $B$ is.
- For $H=0$: $\tilde W(t)=B_0+B_0-B_0=B_0$ for all $t$, a degenerate value.

### 12. `isPreBrownianReal_antitheticBM` (theorem)

**Rendering.** If $B$ is pre-Brownian under $P$ and $H\ne0$, then `antitheticBM H B` is pre-Brownian under $P$.

**Assessment.**

- *Truth:* true. $\tilde W$ is a finite linear combination of $B$, hence a centred Gaussian process. Its covariance is $\min(s,t)$ in every case.
  - **Same coarse step**, $s=(k+\alpha)H\le t=(k+\beta)H$ with $\alpha\le\beta<1$:
    $\operatorname{Cov}=(a+a-a)+(a+b-y)-(a+x-y)=a+b-x=s$, where $x=a+b-s$ and $y=a+b-t$.
  - **Different steps** $k<l$: all times of $\tilde W(s)$ are $\le(k+1)H\le lH\le$ all times of $\tilde W(t)$, so $\operatorname{Cov}=a+b-(a+b-s)=s$.
  - The symbolic check is in `symbolic_cases.out`. The exact rational check covers 39,605 triples, including $s$ or $t$ at grid points and at midpoints, with 0 mismatches (`cov_reversal.out`).
  - Mathlib's `IsGaussianProcess.isPreBrownianReal_of_covariance` then applies.
- *`hH`:* necessary. With $H=0$ the process is constantly $B_0$, which has covariance $0\neq\min(s,t)$ (`cov_reversal.out`).
- *Vacuity, junk:* not vacuous (any BM with $H=1$); no junk.

**Standard fact:** time reversal of Brownian increments on an interval preserves the law: $(B_b-B_{b-u})_{u\in[0,b-a]}$ has the law of BM increments. This is the Giles–Szpruch antithetic construction.

### 13. `iIndepFun_antitheticBM` (theorem)

**Rendering.** Let $\iota$ be arbitrary and $(B_i)_{i\in\iota}$ a family where each $B_i$ is pre-Brownian under $P$. Assume the path-valued maps $\omega\mapsto(t\mapsto B_i(t,\omega))$, valued in $\mathbb R^{\mathbb R_{\ge0}}$ with the product σ-algebra, are mutually independent. Let $H\ne0$. Then:

- (a) each `antitheticBM H (B i)` is pre-Brownian; and
- (b) the reflected paths $\omega\mapsto(t\mapsto\tilde W_i(t,\omega))$ are mutually independent.

**Assessment.**

- *Truth:* true. (a) is #12. For (b), the reflection is a measurable map $\Phi_H:\mathbb R^{\mathbb R_{\ge0}}\to\mathbb R^{\mathbb R_{\ge0}}$, since each output coordinate is a combination of 3 input coordinates. Independence is preserved under composition with measurable maps (`iIndepFun.comp`).
- *What is claimed in several dimensions:* the reflected $d$-dimensional process again has independent pre-Brownian components, so it is a $d$-dimensional pre-BM. Nothing is claimed about the joint law of $(B,\tilde B)$.
- *Vacuity, junk:* not vacuous (independent copies of BM); no junk. `hH` is needed only for (a).

**Standard fact:** componentwise antithetic reflection of a multi-dimensional BM is again a BM with independent components.

### 14. `antitheticBM_natCast_mul` (theorem)

**Rendering.** For all $H\ge0$, $B$, $\omega$ and $k\in\mathbb N$: $\tilde W(kH,\omega)=B(kH,\omega)$, where $k$ is cast to ℝ≥0.

**Assessment.**

- *Truth:* true. **Proved in Lean** (`Det.lean`).
  - $H\ne0$: $\lfloor kH/H\rfloor=k$, and $kH+(k+1)H\,\dot-\,kH=(k+1)H$.
  - $H=0$: both sides are $B_0$, with $0/0=0$ used in an unimportant way.
- *Vacuity:* no hypotheses.
- *Junk:* not junk-dependent.

**Standard fact:** the reflected path agrees with the original at coarse grid times.

### 15. `fineIncrements` (def)

**Rendering.** $\mathrm{fineIncrements}(h,W,\omega)(i)=W((i+1)h,\omega)-W(ih,\omega)$, with $i$ and $i+1$ cast ℕ → ℝ≥0 (confirmed by `#print`). This is the $i$-th increment on the uniform fine grid of step $h$.

### 16. `fineIncrements_antitheticBM` (theorem)

**Rendering.** For all $h\ge0$, $B$ and $\omega$, with coarse step $H=2h$: for every $i$, $\mathrm{fineIncr}(h,\tilde W,\omega)(i)=\mathrm{fineIncr}(h,B,\omega)(\mathrm{pairSwap}\,i)$. Here $\mathrm{pairSwap}(2m)=2m+1$ and $\mathrm{pairSwap}(2m+1)=2m$, so the two fine increments in each coarse step are swapped.

**Assessment.**

- *Truth:* true. **Proved in Lean** (`Det.lean`).
  - The midpoint satisfies $\lfloor(2m+1)h/(2h)\rfloor=m$ and reflects to itself: $\tilde W((2m+1)h)=B_{2mh}+B_{(2m+2)h}-B_{(2m+1)h}$.
  - Hence increment $2m$ is $B_{(2m+2)h}-B_{(2m+1)h}$ and increment $2m+1$ is $B_{(2m+1)h}-B_{2mh}$.
  - Also checked exactly in `cov_reversal.out`.
- *$h=0$:* both sides are $0$.
- *Vacuity, junk:* no hypotheses; no junk.

**Standard fact:** the Giles–Szpruch antithetic fine path swaps the two Brownian increments in each coarse step.

### 17. `reverseFirstStep` (def)

**Rendering.** $R(t)=B_H-B_{H-t}$ for $t\le H$ (exact subtraction), and $R(t)=B_t$ for $t>H$. This reverses time only on the first coarse step $[0,H]$. Note $R(0)=0$ exactly, and $R(H)=B_H-B_0$, which equals $B_H$ a.s.

### 18. `isPreBrownianReal_reverseFirstStep` (theorem)

**Rendering.** For any $H\ge0$, if $B$ is pre-Brownian under $P$ then `reverseFirstStep H B` is pre-Brownian.

**Assessment.**

- *Truth:* true. The covariance is $\min(s,t)$ in all cases (symbolic and exact checks):
  - $s\le t\le H$: $H-(H-t)-(H-s)+(H-t)=s$;
  - $s\le H<t$: $H-(H-s)=s$;
  - $H<s\le t$: $s$.
- *$H=0$:* fine. Then $R$ equals $B$ except $R(0)=0$, a modification at $t=0$. No $H\ne0$ hypothesis is needed and none is imposed.
- *Vacuity, junk:* not vacuous; no junk.

**Standard fact:** time-reversal invariance of Brownian increments on $[0,H]$.

### 19. `reverseFirstStep_fineIncrements` (theorem)

**Rendering.** For all $B$, $\omega$ and $h\ge0$, with $R$ = `reverseFirstStep (2h) B`:

- $R(h)-R(0)=B_{2h}-B_h$; and
- $R(2h)-R(h)=B_h-B_0$.

**Assessment.**

- *Truth:* true. **Proved in Lean** (`Scratch.lean`, `simp` with $h\le 2h$ and $2h-h=h$).
- *$h=0$:* both identities read $0=0$.
- *Vacuity, junk:* no hypotheses; no junk.

**Standard fact:** the fine increments in the first coarse step are swapped by the reversal.

### 20. `swapIncrements` (def)

**Rendering.** $(\mathrm{swapIncrements}\,z)(i)=z(\mathrm{pairSwap}\,i)$.

### 21. `pairSwap` (def)

**Rendering.** $\mathrm{pairSwap}(i)=i+1$ if $i$ is even and $i-1$ if $i$ is odd. The ℕ subtraction is exact because odd $i\ge1$. It is an involution swapping $2m\leftrightarrow2m+1$.
