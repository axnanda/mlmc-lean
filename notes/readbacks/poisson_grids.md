# Blind read-back report: `packet_M3_poisson_grids.lean` (round 11)

| Field | Value |
|---|---|
| Date | 2026-09-29 |
| Packet | `readback/round11/packet_M3_poisson_grids.lean` |
| Declarations audited | 28: the 23 declarations of `MlmcLean.PoissonGrids` (13 theorems, 10 definitions), plus the 5 appended definitions (`roundFixed`, `coupledIncr`, `tauStep`, `tauChain`, `couplePair`) rendered for context |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round11/work_M3/`: `poisson_blocks.py/.out`, `union_chain.py/.out`, `round_fixed.py/.out`, `Scratch.lean/.out` (elaboration check of the verbatim statements), `Proofs.lean/.out` (auditor's own Lean proofs) |
| Toolchain | Lean v4.33.1, Mathlib 0df444a. The scratch files use targeted Mathlib imports only (no `import MlmcLean`); the appended definitions were copied from the packet. |

**Conventions used below.**
- $\mathrm{Po}(r)$ is Mathlib's `poissonMeasure r` $=\sum_{n\ge 0} e^{-r} r^n/n!\,\delta_n$ for $r\in\mathbb R_{\ge 0}$. Since $0^0=1$, $\mathrm{Po}(0)=\delta_0$.
- `HasLaw X ν P` means that $X$ is $P$-a.e. measurable and $P\circ X^{-1}=\nu$.
- `iIndepFun X μ` is mutual independence: for every finite $S$ and measurable $A_i$, $\mu(\bigcap_{i\in S}X_i^{-1}A_i)=\prod_{i\in S}\mu(X_i^{-1}A_i)$. The case $S=\emptyset$ forces $\mu(\Omega)=1$ (Mathlib `iIndepFun.isProbabilityMeasure`).
- The spaces $\mathbb N$, $\mathbb N\times\mathbb N$, $(\mathbb N\times\mathbb N)^2$ and $\mathbb N^\kappa$ (for finite $\kappa$) are countable with measurable singletons, so they carry the discrete σ-algebra (Mathlib instance `MeasurableSingletonClass.toDiscreteMeasurableSpace`). Every function out of them is therefore measurable. As a result, every `Measure.map` and `Measure.bind` in this packet is a genuine push-forward or mixture, never the junk value $0$.

## Summary verdict table

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `hasLaw_finsetSum_poisson` | theorem | true | no | no |
| 2 | `stepCounts` | def | n/a (faithful) | n/a | n/a |
| 3 | `map_stepCounts_pi_poisson` | theorem | true | no (no hypotheses) | no |
| 4 | `stepCounts_hasLaw` | theorem | true | no | no |
| 5 | `iIndepFun_stepCounts` | theorem | true | no | no |
| 6 | `unionGrid_hasLaw` | theorem | true | no | no |
| 7 | `map_comp_stepCounts_eq` | theorem | true | no | no |
| 8 | `integral_comp_stepCounts_eq` | theorem | true | no | no (non-integrable case is 0 = 0, but integrability is proved to be simultaneous) |
| 9 | `unionGrid_2_4` | theorem | true | no | no (same remark as #8) |
| 10 | `tauChainVar` | def | n/a (faithful) | n/a | n/a |
| 11 | `gridStepLength` | def | n/a (faithful) | n/a | n/a |
| 12 | `gridStepEnd` | def | n/a (faithful) | n/a | n/a |
| 13 | `pathAdvance` | def | n/a (faithful) | n/a | n/a |
| 14 | `pathSubStep` | def | n/a (faithful) | n/a | n/a |
| 15 | `unionStep` | def | n/a (faithful) | n/a | n/a |
| 16 | `unionChain` | def | n/a (faithful) | n/a | n/a |
| 17 | `pathChain` | def (no statement uses it) | n/a | n/a | n/a |
| 18 | `pathRun` | def (no statement uses it) | n/a | n/a | n/a |
| 19 | `unionChain_fine` | theorem | true | no | no |
| 20 | `unionChain_coarse` | theorem | true | no | no |
| 21 | `unionChain_nested` | theorem | true | no (no hypotheses) | no |
| 22 | `unionChain_2_4` | theorem | true | no | no (non-integrable $\Phi$ gives 0 = 0 on both sides, and integrability is simultaneous because the laws are equal) |
| 23 | `roundFixed_sum_inconsistent_general` | theorem | true (fully proved in scratch) | no | no junk value, but the theorem relies on Mathlib's tie convention (`round` rounds halves toward $+\infty$); see main point 2 |
| A1–A5 | appended `roundFixed`, `coupledIncr`, `tauStep`, `tauChain`, `couplePair` | defs | n/a (faithful) | n/a | n/a |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.** Evidence for each group:
   - **#23:** I proved it fully in Lean (`Proofs.lean`, no `sorry`).
   - **#21 and #22:** I derived both in Lean from #19 and #20. The only `sorry`s there are those two assumed lemmas.
   - **#1 and #3–#5:** checked exactly with finite sums at 50 digits (errors ≤ 7e-52). The examples include an empty block, a zero rate and $\iota=\emptyset$.
   - **#19–#22:** checked with a literal implementation of the packet's chain definitions. The grids were nested, non-nested (fine 1/3 vs coarse 1/2) and irregular (with a shared interior point), and the propensity was nonlinear. Total-variation error was ≤ 2e-16.
   - **Negative controls:** wrong step sizes gave TV ≈ 5.8e-3, and a frozen state updated one sub-step late gave TV ≈ 1.8e-3. So the chain test does detect errors.
2. **The rounding counterexample (#23) depends on the tie-breaking rule.** `roundFixed` uses Mathlib's `round x = ⌊x + 1/2⌋`, so $\mathrm{round}(1/2)=1$ and $\mathrm{round}(-1/2)=0$ (ties toward $+\infty$). Claims (c) and (d) evaluate `round` exactly at the tie $1/2$. The boundary cases $x=2^{e-B-2}$ and $y=-2^{e-B-2}$ of claim (b) are also ties. I tested 28,512 points satisfying the hypotheses, in exact rational arithmetic:

   | tie-breaking rule | (a) fails | (b) fails | (c) fails | (d) fails |
   |---|---|---|---|---|
   | Mathlib `round` (ties toward $+\infty$) | 0 | 0 | 0 | 0 |
   | round-half-to-even (IEEE default) | 0 | 1,728 (all at $x=2^{e-B-2}$) | 28,512 (every point) | 28,512 (every point) |
   | round-half-away-from-zero | 0 | 1,728 (all at $y=-2^{e-B-2}$) | 1,728 | 1,728 |

   Under half-even the double-rounding inconsistency still exists, but in the mirrored region where $x+y$ is slightly above $2^{e-B-1}$. The theorem is true as stated, but its specific configuration is a ties-toward-$+\infty$ phenomenon. **Please check that "round half up" matches the rounding model in the paper.**
3. **The chain theorems give only one-time marginal laws.** #19, #20 and #22 give the law of the running count at a single grid point, not the law of the whole path. So the telescoping identity in #22 is established only for final-time functionals $\Phi(X_{t_K})$. Path functionals are covered only by the state-independent Poisson-count version, #9, which allows any $F$ of the whole step-count vector.
4. **#6 `unionGrid_hasLaw` states two separate marginal laws.** It says nothing about the joint law of the fine and coarse counts (the coupling). It is an immediate corollary of #4.
5. **Model scope.** The state space is $\mathbb N$, increments are nonnegative, and there is a single propensity $\lambda:\mathbb N\to\mathbb R_{\ge0}$. This is a scalar pure-birth (single-reaction counting) process under explicit tau-leaping. Multi-channel reaction networks, as in the general Anderson–Higham setting, are not covered.
6. **Harmless extras.**
   - The section instance `[Fintype κ]` is included but not used in the statement types of #5, #7, #8 and #9. For #7 and #8 it is exactly what makes an arbitrary $F$ automatically measurable.
   - `pathChain` and `pathRun` appear in no statement; they are presumably proof auxiliaries.
   - The packet shows `couplePair` as a plain `def`. My scratch copy needed `noncomputable` because `NNReal`'s order is noncomputable. This affects code generation only, not the statements.

## Per-declaration analysis

### 1. `hasLaw_finsetSum_poisson` (theorem)

**Rendering.** Let $\Omega$ and $\iota$ be arbitrary types ($\iota$ need not be finite), and let $\mu$ be a measure on a measurable space $\Omega$. Let $X_i:\Omega\to\mathbb N$ be random variables and $m_i\in\mathbb R_{\ge0}$ rates, for $i\in\iota$. Assume:
- the family $(X_i)_{i\in\iota}$ is mutually independent under $\mu$;
- each $X_i$ is a.e.-measurable with law $\mathrm{Po}(m_i)$.

Then for every finite set $s\subseteq\iota$, the sum $\sum_{i\in s}X_i$ is a.e.-measurable with law $\mathrm{Po}\big(\sum_{i\in s}m_i\big)$.

**Assessment.** True.
- **Proof sketch:** induction on $s$.
  - For $s=\emptyset$, the sum is the constant $0$, and $\mu\circ 0^{-1}=\mu(\Omega)\,\delta_0=\delta_0=\mathrm{Po}(0)$ because independence forces $\mu(\Omega)=1$.
  - For $a\notin s$, $X_a$ is independent of $\sum_{i\in s}X_i$, and $\mathrm{Po}(r_1)*\mathrm{Po}(r_2)=\mathrm{Po}(r_1+r_2)$ (Mathlib `IndepFun.hasLaw_add_poissonMeasure`).
- **Numerics:** `poisson_blocks.py`, error ≤ 2e-56.
- **Vacuity:** not vacuous. Take $\Omega=\mathbb N^\iota$ with $\mu=\bigotimes_i\mathrm{Po}(m_i)$ and $X_i$ the coordinates; `Proofs.lean` gives a Lean witness via `iIndepFun_pi` and `measurePreserving_eval`.
- **Junk values:** none. The edge cases $s=\emptyset$ and $m_i=0$ use the correct convention $\mathrm{Po}(0)=\delta_0$.
- **Hypotheses:** independence of the whole family is more than needed (only $i\in s$ matters), which is standard.
- **Standard fact:** the Poisson family is closed under convolution (independent Poisson variables add).

### 2. `stepCounts` (def)

**Rendering.** For a finite $\iota$, a map $b:\iota\to\kappa$ (with decidable equality on $\kappa$), a count vector $x\in\mathbb N^\iota$ and $k\in\kappa$:
$$\mathrm{stepCounts}_b(x)_k=\sum_{i\in\iota,\ b(i)=k}x_i .$$
The sum runs over `Finset.univ.filter`, which I confirmed by `#print`. An empty block $b^{-1}\{k\}=\emptyset$ gives $0$.

**Assessment.** A faithful "counts per grid step". Here $\iota$ is the set of union-grid sub-intervals and $b(i)$ is the step of a grid that contains sub-interval $i$. The map $b$ need not be monotone or surjective, which is more general than needed.

### 3. `map_stepCounts_pi_poisson` (theorem)

**Rendering.** Let $\iota$ and $\kappa$ be finite, $b:\iota\to\kappa$ any map and $m\in\mathbb R_{\ge0}^\iota$. Push the product measure $\bigotimes_{i\in\iota}\mathrm{Po}(m_i)$ on $\mathbb N^\iota$ forward under $\mathrm{stepCounts}_b:\mathbb N^\iota\to\mathbb N^\kappa$. The result is the product measure $\bigotimes_{k\in\kappa}\mathrm{Po}(M_k)$, where $M_k=\sum_{b(i)=k}m_i$.

**Assessment.** True.
- **Proof sketch:** block sums over disjoint blocks of independent coordinates are independent, and each block sum is $\mathrm{Po}(M_k)$ by #1. An empty block gives $\delta_0=\mathrm{Po}(0)$. The push-forward is genuine because the domain is discrete.
- **Numerics:** verified exactly for all targets whose coordinates are $\le N$. Every preimage point of such a target has $x_i\le y_{b(i)}\le N$, so the enumerated box $\{0..N\}^\iota$ captures all of the mass. Maximum errors were 3.3e-52 and 6.7e-52 on two examples (one with an empty block, one with a zero rate), 1.7e-52 for a single block, and 0 for $\iota=\emptyset$.
- **Vacuity:** the theorem has no hypotheses.
- **Standard fact:** the mapping (aggregation) property of Poisson random measures: independent Poisson counts aggregated over the blocks of a partition are independent Poisson variables with summed rates.

### 4. `stepCounts_hasLaw` (theorem)

**Rendering.** Take the section variables: finite $\iota$ and $\kappa$, decidable equality on $\kappa$, a measure $\mu$ on $\Omega$, $X:\iota\to\Omega\to\mathbb N$ and $m$. Assume $(X_i)$ is mutually independent and $X_i\sim\mathrm{Po}(m_i)$ under $\mu$. Then for every $b:\iota\to\kappa$, the random vector
$$\omega\mapsto\Big(\sum_{b(i)=k}X_i(\omega)\Big)_{k\in\kappa}\in\mathbb N^\kappa$$
is a.e.-measurable with law $\bigotimes_k\mathrm{Po}(M_k)$.

**Assessment.** True.
- **Proof sketch:** independence plus the marginal laws is equivalent to the joint law being $\bigotimes_i\mathrm{Po}(m_i)$ (`iIndepFun_iff_map_fun_eq_pi_map`, which needs only AE-measurability). Then apply #3.
- **Vacuity:** the canonical product instance of #1 satisfies the hypotheses.
- **Junk values:** none.
- **Standard fact:** the random-variable form of #3.

### 5. `iIndepFun_stepCounts` (theorem)

**Rendering.** Same hypotheses as #4. The theorem also carries an included but unused `[Fintype κ]`. Conclusions:
- (a) the block sums $Y_k=\sum_{b(i)=k}X_i$, $k\in\kappa$, are mutually independent under $\mu$;
- (b) $Y_k\sim\mathrm{Po}(M_k)$ for every $k$.

**Assessment.** True. By #4 the joint law is a product with these marginals, which is equivalent to independence. **Standard fact:** the grouping lemma for independent families, plus Poisson additivity.

### 6. `unionGrid_hasLaw` (theorem)

**Rendering.** Let $\iota$ be the finite set of union-grid sub-intervals, with lengths $h_i\ge 0$, and let $\lambda\ge0$ be a rate. Assume $(X_i)$ is independent with $X_i\sim\mathrm{Po}(\lambda h_i)$. Let $b_f:\iota\to\kappa_f$ and $b_c:\iota\to\kappa_c$ map into finite types. Then:
- the fine step counts $\mathrm{stepCounts}_{b_f}(X)$ have law $\bigotimes_{k\in\kappa_f}\mathrm{Po}\big(\lambda\sum_{b_f(i)=k}h_i\big)$;
- the coarse step counts $\mathrm{stepCounts}_{b_c}(X)$ have law $\bigotimes_{k\in\kappa_c}\mathrm{Po}\big(\lambda\sum_{b_c(i)=k}h_i\big)$.

**Assessment.** True: apply #4 twice with $m_i=\lambda h_i$ and use $\sum_i\lambda h_i=\lambda\sum_i h_i$.
- The conclusion is two separate marginal statements. It says nothing about the joint (coupled) law of the fine and coarse counts.
- $b_f$ and $b_c$ need not be interval partitions.
- **Standard fact:** the counts of a homogeneous Poisson process of rate $\lambda$ on the steps of any grid are independent $\mathrm{Po}(\lambda\cdot\text{step length})$.

### 7. `map_comp_stepCounts_eq` (theorem)

**Rendering.** Take the hypotheses of #4 and add:
- a second measure space $(\Omega',\nu)$ and a measurable space $\alpha$;
- $Z:\kappa\to\Omega'\to\mathbb N$ with $(Z_k)$ mutually independent under $\nu$ and $Z_k\sim\mathrm{Po}(M_k)$.

Then for every function $F:\mathbb N^\kappa\to\alpha$ (no measurability hypothesis):
$$\mu\circ\big(F\circ\mathrm{stepCounts}_b(X)\big)^{-1}=\nu\circ\big(F\circ Z\big)^{-1}.$$

**Assessment.** True. Both vectors have law $\bigotimes_k\mathrm{Po}(M_k)$: #4 for $X$, and the independence/product-law equivalence for $Z$. $F$ is automatically measurable because $\mathbb N^\kappa$ is discrete when $\kappa$ is finite (this is where the assumed `[Fintype κ]` matters). So both sides are genuine push-forwards. **Standard fact:** equality in law is preserved by measurable maps.

### 8. `integral_comp_stepCounts_eq` (theorem)

**Rendering.** Same hypotheses as #7, with $F:\mathbb N^\kappa\to\mathbb R$. Conclusions:
- $F(\mathrm{stepCounts}_bX)\in L^1(\mu)\iff F(Z)\in L^1(\nu)$;
- $\int F(\mathrm{stepCounts}_bX)\,d\mu=\int F(Z)\,d\nu$.

**Assessment.** True, by change of variables (`integrable_map_measure`, `integral_map`) and #7. If $F$ is not integrable, both Bochner integrals take the junk value $0$. However, the stated equivalence shows that integrability fails on both sides at once, so the equation does not depend on the junk value. **Standard fact:** the law of the unconscious statistician under equality in law.

### 9. `unionGrid_2_4` (theorem)

**Rendering.** Take two setups:
- $(X_{1,i})_{i\in\iota_1}$ on $(\Omega_1,\mu_1)$, independent, with $X_{1,i}\sim\mathrm{Po}(m_{1,i})$;
- $(X_{2,i})_{i\in\iota_2}$ on $(\Omega_2,\mu_2)$, independent, with $X_{2,i}\sim\mathrm{Po}(m_{2,i})$.

Here $\iota_1$ and $\iota_2$ are finite. Let $b_1:\iota_1\to\kappa$ and $b_2:\iota_2\to\kappa$ map into a common finite $\kappa$, with equal block rates: $\sum_{b_1(i)=k}m_{1,i}=\sum_{b_2(i)=k}m_{2,i}$ for all $k$. Then for every $F:\mathbb N^\kappa\to\mathbb R$:
- $F(\mathrm{stepCounts}_{b_1}X_1)$ is $\mu_1$-integrable if and only if $F(\mathrm{stepCounts}_{b_2}X_2)$ is $\mu_2$-integrable;
- the two expectations are equal.

**Assessment.** True. By #4 both vectors have law $\bigotimes_k\mathrm{Po}(M_k)$; then argue as in #8.
- **Vacuity:** not vacuous. Take $m_j=\lambda h_j$ for the two union grids in `union_chain.py`: the level-$\ell$ coarse grid (step 1/2) and the level-$(\ell-1)$ fine grid (step 1/2) have the same block rates.
- **MLMC reading:** compare the level-$\ell$ coarse grid (inside the level-$\ell$ union grid) with the level-$(\ell-1)$ fine grid (inside another union grid). When the two grids have the same steps, $\mathbb E[P^c]=\mathbb E[P^f]$ for any functional of the whole step-count vector.
- **Standard fact:** the MLMC telescoping condition, for state-independent (Poisson-process) counts. The `_2_4` suffix presumably refers to an equation (2.4) in the source paper; I cannot check this blind.

### 10. `tauChainVar` (def)

**Rendering.** The recursion is $\mathrm{tauChainVar}_0=\delta_{x_0}$ and
$$\mathrm{tauChainVar}_{k+1}=\sum_x \mathrm{tauChainVar}_k(\{x\})\;\mathrm{tauStep}(H_k,x),$$
where $\mathrm{tauStep}(h,x)$ is the law of $x+N$ with $N\sim\mathrm{Po}(h\lambda(x))$. So $\mathrm{tauChainVar}_k$ is the law after $k$ steps of explicit tau-leaping $Y_{k+1}=Y_k+\mathrm{Po}(H_k\lambda(Y_k))$ with variable step sizes $H_k$.

**Assessment.** Faithful: Gillespie's explicit tau-leap for a scalar counting process. The `bind` is genuine because all spaces are discrete.

### 11. `gridStepLength` (def)

**Rendering.** $\mathrm{gridStepLength}(h,t,k)=\sum_{j=t_k}^{t_{k+1}-1}h_j$, and the empty sum $0$ when $t_{k+1}\le t_k$. This is the length of the $k$-th step of the grid whose points are the union points $t_0,t_1,\dots$, where $h_j$ is the length of union sub-interval $j$.

**Assessment.** Faithful for increasing $t$.

### 12. `gridStepEnd` (def)

**Rendering.** $\mathrm{gridStepEnd}(t,j)=\mathbf 1[\exists k\in\mathbb N:\ t_{k+1}=j+1]$, via classical `decide`. It means "union sub-interval $[j,j+1]$ ends at a grid point other than $t_0$". For strictly increasing $t$ with $t_0=0$ it equals $\mathbf 1[j+1\in t(\mathbb N)]$. Examples: for $t=\mathrm{id}$ it is always true; for $t=2\,\cdot$ it is true exactly when $j$ is odd.

**Assessment.** Faithful.

### 13. `pathAdvance` (def)

**Rendering.** $(p_1,p_2)\mapsto\big(p_1+i,\ \text{if } e \text{ then } p_1+i \text{ else } p_2\big)$. Here $p_1$ is the running count and $p_2$ is the state frozen at the path's last grid point. The frozen value is refreshed exactly when the sub-step ends at a grid point.

**Assessment.** Faithful.

### 14. `pathSubStep` (def)

**Rendering.** A kernel: from $p$, draw $N\sim\mathrm{Po}(h\lambda(p_2))$, with the propensity evaluated at the frozen grid-point state, and return $\mathrm{pathAdvance}(e,p,N)$.

**Assessment.** Faithful. This is how one tau-leap step of a grid is split over the union sub-intervals it contains.

### 15. `unionStep` (def)

**Rendering.** A kernel on $s=((f_1,f_2),(c_1,c_2))$: draw $(N_f,N_c)\sim\mathrm{coupledIncr}(h\lambda(f_2),\,h\lambda(c_2))$ and return
$$\big(\mathrm{pathAdvance}(e_f,(f_1,f_2),N_f),\ \mathrm{pathAdvance}(e_c,(c_1,c_2),N_c)\big).$$

**Assessment.** Faithful.

### 16. `unionChain` (def)

**Rendering.** The recursion is $\mathrm{unionChain}_0=\delta_{((x_0,x_0),(x_0,x_0))}$ and
$$\mathrm{unionChain}_{n+1}=\mathrm{unionChain}_n.\mathrm{bind}\ \mathrm{unionStep}\big(h_n,\mathrm{gridStepEnd}(t_f,n),\mathrm{gridStepEnd}(t_c,n)\big).$$
This is the joint law, after $n$ union sub-steps, of a fine and a coarse tau-leap path coupled by `coupledIncr` on each union sub-interval.

**Assessment.** Faithful. It is an Anderson–Higham-type coupling on non-nested grids built from their union grid.

### 17. `pathChain` (def)

**Rendering.** The single-path analogue of `unionChain`, built from `pathSubStep`.

**Assessment.** No theorem statement in the packet uses it.

### 18. `pathRun` (def)

**Rendering.** $\mathrm{pathRun}(n,0,p)=\delta_p$ and
$$\mathrm{pathRun}(n,r+1,p)=\mathrm{pathRun}(n,r,p).\mathrm{bind}\ \mathrm{pathSubStep}\big(h_{n+r},\mathrm{gridStepEnd}(t,n+r)\big),$$
i.e. the $r$-step transition kernel starting from union index $n$.

**Assessment.** No theorem statement in the packet uses it.

### 19. `unionChain_fine` (theorem)

**Rendering.** Fix $\lambda$ and $h$. Let $t_c:\mathbb N\to\mathbb N$ be arbitrary, and let $t_f$ be strictly increasing with $t_f(0)=0$. Then for all $x_0,k\in\mathbb N$, the law of the fine running count $s_{1,1}$ under $\mathrm{unionChain}_{t_f(k)}$ equals $\mathrm{tauChainVar}\big(\lambda,\ \mathrm{gridStepLength}(h,t_f),\ x_0\big)_k$.

**Assessment.** True. Proof sketch in two steps:
1. **The fine component is a Markov chain on its own.** The first marginal of $\mathrm{coupledIncr}(a,b)$ is $\mathrm{Po}(a)$: if $b<a$ it is the law of $U+V\sim\mathrm{Po}(b+(a-b))$, and otherwise it is $U\sim\mathrm{Po}(\min(a,b))=\mathrm{Po}(a)$. So the first marginal of `unionStep` at $s$ is `pathSubStep` at $s_1$, which depends on $s_1$ only. Interchanging bind and map on discrete spaces gives $\mathrm{unionChain}_n\circ\mathrm{fst}^{-1}=\mathrm{pathChain}_n$.
2. **One grid step of the fine path is one tau-leap step.** Because $t_f$ is strictly increasing with $t_f(0)=0$, `gridStepEnd` is false inside step $k$ (for $j\in[t_f(k),t_f(k+1))$) except at $j=t_f(k+1)-1$. So the frozen state equals $X_{t_f(k)}$ throughout the step. The independent increments $\mathrm{Po}(h_j\lambda(X_{t_f(k)}))$ then add up to $\mathrm{Po}(H_k\lambda(X_{t_f(k)}))$ with $H_k=\sum_j h_j$. At the end of the step the frozen state is set to the running state. Induction on $k$ finishes the proof.

- **Numerics (`union_chain.py`):**
  - TV ≤ 7.9e-17 on a non-nested grid (fine step 1/3 vs coarse step 1/2), and ≤ 7.5e-17 on irregular grids that share an interior point.
  - At grid times, $P(\text{running}\neq\text{frozen})=0$.
  - Negative controls give TV of 1.8e-3 and 5.8e-3.
- **Vacuity:** not vacuous; take $t_f=\mathrm{id}$.
- **Junk values:** none.
- **Standard fact:** marginal correctness of the coupled tau-leap scheme: each component is an exact tau-leap path on its own grid.

### 20. `unionChain_coarse` (theorem)

**Rendering.** The mirror of #19 for the coarse component. Let $t_c$ be strictly increasing with $t_c(0)=0$ and $t_f$ arbitrary. Then the law of $s_{2,1}$ under $\mathrm{unionChain}_{t_c(k)}$ equals $\mathrm{tauChainVar}\big(\lambda,\mathrm{gridStepLength}(h,t_c),x_0\big)_k$.

**Assessment.** True. The proof is the same as #19, using that the second marginal of $\mathrm{coupledIncr}(a,b)$ is $\mathrm{Po}(b)$. The numerics are the same as for #19.

### 21. `unionChain_nested` (theorem)

**Rendering.** Take a constant sub-step $h\in\mathbb R_{\ge0}$, $t_f=\mathrm{id}$ and $t_c=(n\mapsto 2n)$ on $\mathbb N$. Then for all $x_0$ and $k$:
- the fine running count at union index $k$ has law $\mathrm{tauChain}(\lambda,h,x_0)_k$;
- the coarse running count at union index $2k$ has law $\mathrm{tauChain}(\lambda,2h,x_0)_k$, where $2h\in\mathbb R_{\ge0}$.

**Assessment.** True.
- **Lean derivation:** I derived it in Lean from #19 and #20. `gridStepLength` equals $h$ and $2h$ respectively, and `tauChainVar` with constant steps equals `tauChain`.
- **Numerics:** TV ≤ 2.1e-16.
- **Vacuity:** the theorem has no hypotheses.
- **Standard fact:** the standard nested Anderson–Higham coupling with refinement factor 2.

### 22. `unionChain_2_4` (theorem)

**Rendering.** Fix $\lambda$, union-step sequences $h_1,h_2$, and grids $t_{f,1},t_{c,1},t_{f,2},t_{c,2}$. Assume $t_{c,1}$ and $t_{f,2}$ are strictly increasing and start at $0$; $t_{f,1}$ and $t_{c,2}$ are arbitrary. Fix $x_0$ and $K$, and assume
$$\mathrm{gridStepLength}(h_1,t_{c,1},k)=\mathrm{gridStepLength}(h_2,t_{f,2},k)\quad\text{for all } k<K.$$
Then:
- (a) the coarse running count of chain 1 at union index $t_{c,1}(K)$ and the fine running count of chain 2 at $t_{f,2}(K)$ have the same law;
- (b) for every $\Phi:\mathbb N\to\mathbb R$, $\int\Phi(s_{2,1})\,d\,\mathrm{unionChain}^{(1)}_{t_{c,1}(K)}=\int\Phi(s_{1,1})\,d\,\mathrm{unionChain}^{(2)}_{t_{f,2}(K)}$.

**Assessment.** True.
- **Lean derivation:** I derived it in Lean from #19 and #20, together with a lemma I proved: $\mathrm{tauChainVar}_K$ depends only on $H_0,\dots,H_{K-1}$.
- **Numerics:** I compared level $\ell$ (fine 1/3, coarse 1/2) with level $\ell-1$ (fine 1/2, coarse 1). TV ≤ 3.9e-17, and $\mathbb E\,\Phi$ agrees to 12 digits.
- **Junk values:** for non-integrable $\Phi$ both sides are $0$. The laws are equal, so integrability holds or fails on both sides together, and the statement does not depend on the junk value.
- **Scope:** only the marginal law at time $t_K$ is covered (main point 3).
- **Standard fact:** the MLMC telescoping condition $\mathbb E[P^c_\ell]=\mathbb E[P^f_{\ell-1}]$ for the coupled tau-leap estimator on non-nested grids.

### 23. `roundFixed_sum_inconsistent_general` (theorem)

**Rendering.** Let $e\in\mathbb Z$, $B\in\mathbb N$ and $u=2^{e-B}$ (an integer power). Define
$$\mathrm{rf}_d(z)=2^{e-d}\,\mathrm{round}\big(z/2^{e-d}\big),\qquad \mathrm{round}(z)=\big\lfloor z+\tfrac12\big\rfloor .$$
For real $x,y$ with $x\ge u/4$, $y\ge -u/4$ and $x+y<u/2$:
- (a) $\mathrm{rf}_B(x+y)=0$;
- (b) $\mathrm{rf}_{B+1}(x)+\mathrm{rf}_{B+1}(y)=u/2$;
- (c) $\mathrm{rf}_B\big(\mathrm{rf}_{B+1}(x)+\mathrm{rf}_{B+1}(y)\big)=u$;
- (d) $\mathrm{rf}_B(\mathrm{rf}_{B+1}(x))+\mathrm{rf}_B(\mathrm{rf}_{B+1}(y))=u$.

The exponents $e-B-2$, $e-B-1$ and $e-(B+1)$ are integers; I confirmed this by elaboration.

**Assessment.** True; I proved it fully in Lean (`Proofs.lean`).
- **Proof sketch:**
  - (a): $(x+y)/u\in[0,\tfrac12)$, so it rounds to $0$.
  - (b): $x<u/2-y\le 3u/4$, so $2x/u\in[\tfrac12,\tfrac32)$ rounds to $1$; and $2y/u\in[-\tfrac12,\tfrac12)$ rounds to $0$.
  - (c) and (d): $\mathrm{round}(\tfrac12)=1$.
- **Vacuity:** not vacuous; take $e=B=0$, $x=\tfrac14$, $y=0$.
- **Junk values:** none, since $2^{e-d}>0$.
- **Tie dependence:** (c) and (d) evaluate `round` exactly at the midpoint $\tfrac12$, and the boundary cases $x=u/4$ and $y=-u/4$ of (b) are midpoints too. The exact-rational results over 28,512 points are in the table under main point 2. Under round-half-even the inconsistency reappears in the mirrored region: for $x=0.6$, $y=-0.05$ (so $x+y$ is just above $u/2=0.5$), direct rounding gives $1$ and double rounding gives $0$.
- **Standard fact:** double rounding. Rounding to nearest at precision $B$ a value first rounded to precision $B+1$ can differ from rounding directly when the first rounding lands on a midpoint; consequently rounding is not additive.

### Appended definitions (context)

- **A1 `roundFixed e d x`** $=2^{e-d}\,\mathrm{round}(x/2^{e-d})$: the nearest multiple of $2^{e-d}$, with ties toward $+\infty$.
- **A2 `coupledIncr a b`:** the law of $\big(U+\mathbf 1[b<a]\,V,\ U+\mathbf 1[a<b]\,V\big)$, where $U\sim\mathrm{Po}(\min(a,b))$ and $V\sim\mathrm{Po}(\max(a,b)-\min(a,b))$ are independent. The truncated $\mathbb R_{\ge0}$ subtraction is harmless because $\max\ge\min$. The marginals are $\mathrm{Po}(a)$ and $\mathrm{Po}(b)$, and $P(\text{components differ})=1-e^{-|a-b|}$ (both confirmed numerically). This is the Anderson–Higham split coupling.
- **A3 `tauStep lam h x`:** the law of $x+\mathrm{Po}(h\lambda(x))$.
- **A4 `tauChain lam h x₀ n`:** the law after $n$ steps of tau-leaping with a constant step $h$.
- **A5 `couplePair a b p`** $=\big(p_1+[b<a]\,p_2,\ p_1+[a<b]\,p_2\big)$.
