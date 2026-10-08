# Blind read-back report: packet R26 (adaptive grids)

| Field | Value |
|---|---|
| Date | 2026-10-08 |
| Packet | `readback/round20/packet_R26_adaptive.lean` |
| Declarations audited | 27 theorems (full assessment) + 43 definitions (rendered: 37 in the packet, 6 appended) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round20/work_R26/` (`*.py` with matching `*.out`; scratch compile `scratch_packet.lean` / `.out`) |

Scratch compile: the packet, with the 6 appended helper definitions moved to the top, a proved stub for
the unshown `alg3_exists_reach : ∃ n, k ≤ κ n ∨ ∀ j, κ j < k`, and targeted Mathlib imports, elaborates with
`-DautoImplicit=false`. The only warnings are 27 `declaration uses sorry` (`scratch_packet.out`). `#print`/`#check` confirmed how the
casts elaborate. For example, `Real.sqrt (ν k y * δ)` elaborates as $\sqrt{(\nu_k(y):\mathbb R)\cdot(\delta:\mathbb R)}$, which has the same value as
$\sqrt{((\nu_k(y)\cdot\delta:\mathbb R_{\ge0}):\mathbb R)}$.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `map_adaptivePath_prod` | theorem | true | no | no |
| 2 | `map_adaptivePath` | theorem | true | no | no |
| 3 | `map_adaptiveIncr` | theorem | true | no | no |
| 4 | `map_freshPath` | theorem | true | no | no |
| 5 | `map_adaptiveSeq_eq_freshSeq` | theorem | true | no | no |
| 6 | `adaptiveIncr_condLaw_gaussian` | theorem | true | no | no |
| 7 | `adaptiveIncr_condDistrib_gaussian` | theorem | true | no | no |
| 8 | `adaptivePath_law_gaussian` | theorem | true | no | no |
| 9 | `freshPath_law_gaussian` | theorem | true | no | no |
| 10 | `adaptiveSeq_law_eq_fresh` | theorem | true | no | no |
| 11 | `adaptivePairs_law_eq_fresh` | theorem | true | no | no |
| 12 | `adaptiveEM_law_eq_freshEM` | theorem | true | no | no |
| 13 | `adaptiveEM_fine_coarse` | theorem | true | no | no |
| 14 | `adaptiveEM_2_4` | theorem | true | no | no (the integral equality is $0=0$ in the non-integrable case, but that case is covered by the ↔ conjunct) |
| 15 | `adaptiveEM_mlmc_theorem1` | theorem | true | no | no (`variance` and the integrals are genuine, see §15) |
| 16 | `adaptiveCount_condLaw` | theorem | true | no | no |
| 17 | `adaptiveCount_law_eq_fresh` | theorem | true | no | no |
| 18 | `map_histPath_prod` | theorem | true | no | no |
| 19 | `histIncr_condLaw_gaussian` | theorem | true | no | no |
| 20 | `adaptiveIncr_condLaw_hist_gaussian` | theorem | true | no | no |
| 21 | `histCount_condLaw` | theorem | true | no | no |
| 22 | `alg3CoarseSeq_alg3Path` | theorem | true | no | no |
| 23 | `alg3FineSeq_alg3Path` | theorem | true | no | no |
| 24 | `algorithm3_law` | theorem | true | no | no |
| 25 | `algorithm3_joint_law` | theorem | true | no | no |
| 26 | `algorithm3_EM_law` | theorem | true | no | no |
| 27 | `algorithm3_EM_joint_law` | theorem | true | no | no |

No statement was found to be false, vacuous, or dependent on a junk value.

## Main points for a human auditor

1. **Every `Measure.map` equality is substantive.** Mathlib's `Measure.map f μ` is $0$ when $f$ is not
   AE-measurable, and `Measure.bind` (inside `noiseChainLaw`) gives $0$ for a non-measurable kernel. So $0=0$ could
   in principle make these statements trivially true. Under the stated measurability hypotheses (`hν`, `hG`, `ha`, `hb`, `hs`, `hh`) all
   maps and kernels involved are measurable, so both sides are probability measures. Only #1 states
   measurability explicitly. Elsewhere it is implicit.
2. **The measure $P$ is never explicitly a probability measure in #6, #8–14, #16–21 and #24–27, and this is fine.**
   Mathlib's `iIndepFun ξ P` forces `IsProbabilityMeasure P` (lemma `iIndepFun.isProbabilityMeasure`, via the empty
   finset), and so does `HasLaw (ξ i) (gaussianReal 0 δ) P`.
3. **#15 (`adaptiveEM_mlmc_theorem1`) is Giles' MLMC complexity theorem.** Here the bias, variance and cost rates are
   *hypotheses*, not derived from the EM scheme. Three points:
   - $c_4$ is quantified after all the data ($a,b,\Phi,P,\omega,\mathrm{cost},\dots$), so it may depend on the
     instance and not only on $(\alpha,\beta,\gamma,c_1,c_2,c_3)$. This is slightly weaker than the textbook statement, though still
     uniform in $\varepsilon$.
   - No $L^2$ or integrability hypothesis is placed on the coarse functional $P^c_\ell$. It follows from `hcons` (equal step
     sizes $\nu^f_\ell\delta_\ell=\nu^c_\ell\delta_{\ell+1}$), which makes $P^c_\ell$ and $P^f_\ell$ equal in law. Hence
     `variance` in `h_iii` is a genuine variance, not the junk value `toReal ⊤ = 0`, and $E P^c_\ell = E P^f_\ell$
     (telescoping).
   - The script `mlmc_complexity.py` confirms the bound's shape. With $\alpha\ge\min(\beta,\gamma)/2$, including the boundary,
     cost/complexityBound stays bounded. With $\alpha<\min(\beta,\gamma)/2$ the ratio blows up ($10^{13}$–$10^{15}$).
4. **#22/#23 (Algorithm 3 pathwise identities) need *both* hypotheses $\nu^c\ge1$ and $\nu^f\ge1$.** If one level's
   $\nu$ can be $0$, `alg3Len` can be $0$ and the other level stalls. `alg3FirstReach` then falls back to its junk default $0$,
   and the identity fails (`alg3_check.py`: 16 of 30 instances fail with $\nu^c\in\{0,1\}$). Under the
   hypotheses the identities hold exactly: 60 random instances with exact rationals, and the invariant `alg3Inv` holds at every step.
5. **#13 states only marginal laws.** The joint fine/coarse coupling (same Brownian increments) is the content of #25/#27.
   A Monte Carlo check confirms the joint law of #27, using the coupling statistic $E(S^c_k-S^f_k)^2$ (400k paths, $|z|<2$),
   which distinguishes the shared-noise coupling from an independent one.
6. **#17 uses an unusual but legitimate fresh-noise device.** Each $\zeta_k$ is an independent bank $(\zeta_k(n))_{n\in\mathbb N}$
   of independent Poisson($n m$) variables, and step $k$ reads component $\nu_k(y)$.
7. **Conventions.** `adaptiveEMStep` evaluates the coefficients as $a(S,t)$ and $b(S,t)$ (`a x.2 x.1` with $x=(t,S)$).
   `gaussianReal 0 0 = dirac 0` and `poissonMeasure 0 = dirac 0` (Mathlib's $0^0=1$), so blocks of length $0$ (empty sum $0$) are
   consistent with the step kernels at $n=0$.

---

## Definitions (renderings)

Notation: $\mu^{\otimes\mathbb N}$ = `Measure.infinitePi (fun _ => μ)`. Mathlib defines this as $0$ unless every factor is a
probability measure, and every use in the packet has probability factors. $\mathrm{ext}_k(y,x)$ = `extendPath k y x`.

- **`noiseChainLaw κ x₀ k`**: the time-$k$ marginal of an inhomogeneous Markov chain, $m_0=\delta_{x_0}$ and $m_{k+1}=\int\kappa_k(x,\cdot)\,m_k(dx)$
  (`Measure.bind`). This is junk $0$ if $x\mapsto\kappa_k(x)$ is not Giry-measurable.
- **`blockLaw μ n`**: the law of $\sum_{i<n}\xi_i$ under $\mu^{\otimes\mathbb N}$, i.e. $\mu^{*n}$, with $\mu^{*0}=\delta_0$.
- **`extendPath k y x`**: $i\mapsto y(i)$ if $i\le k$, and $x$ if $i>k$.
- **`adaptivePath ν G x₀ ξ k`** $=(y_k,\tau_k)$: $y_0\equiv x_0$, $\tau_0=0$, $n_k=\nu_k(y_k)$,
  $e_k=\sum_{i=\tau_k}^{\tau_k+n_k-1}\xi_i$, $y_{k+1}=\mathrm{ext}_k(y_k,G_k(y_k,e_k))$, $\tau_{k+1}=\tau_k+n_k$.
  Then $y_k(i)=x_{\min(i,k)}$ with $x_i:=y_i(i)$.
- **`adaptiveIncr … k`** $=e_k$, the sum of the $\nu_k(y_k)$ fresh noises after $\tau_k$.
- **`adaptiveStep`**: the one-step map $(y,w)\mapsto(\mathrm{ext}_k(y,G_k(y,\sum_{i<\nu_k(y)}w_i)),\,w_{\nu_k(y)+\cdot})$. This helper is not used in the statements.
- **`adaptiveLaw κ G x₀ k`**: `noiseChainLaw` with the kernel $y\mapsto$ law of $\mathrm{ext}_k(y,G_k(y,e))$ for $e\sim\kappa_k(y)$,
  started from the constant path $x_0$.
- **`blockKernel μ`**: the kernel $\mathbb N\to E$, $n\mapsto\mu^{*n}$.
- **`freshPath G x₀ ζ k`**: $p_0\equiv x_0$, $p_{k+1}=\mathrm{ext}_k(p_k,G_k(p_k,\zeta_k))$, i.e. one fresh noise per step.
  **`freshStep`** is the corresponding helper.
- **`adaptiveSeq … ξ`** $=(y_k(k))_k$ and **`freshSeq … ζ`** $=(p_k(k))_k$.
- **`gaussianStepKernel δ`**: $n\mapsto N(0,n\delta)$. **`poissonStepKernel m`**: $n\mapsto\mathrm{Poi}(nm)$.
- **`adaptiveEMStep a b h (t,S) dW`** $=(t+h,\;S+a(S,t)h+b(S,t)\,dW)$.
- **`adaptiveEM a b ν δ S₀ ξ`**: the adaptive EM sequence. At state $x_k$ it uses $\nu(x_k)$ base increments, with step
  $h_k=\nu(x_k)\delta$ (computed in ℝ) and $dW$ equal to the sum of those increments. It starts at $(0,S_0)$.
- **`freshEM a b H S₀ ζ`**: EM with step $H(x_k)$ and $dW=\sqrt{H(x_k)}\,\zeta_k$.
- **`adaptiveEMFine … ℓ z`** $=\Phi_\ell(\text{adaptiveEM}(\nu^f_\ell,\delta_\ell,(\sqrt{\delta_\ell}z_i)_i))$ and
  **`adaptiveEMCoarse … ℓ z`** $=\Phi_\ell(\text{adaptiveEM}(\nu^c_\ell,\delta_{\ell+1},(\sqrt{\delta_{\ell+1}}z_i)_i))$.
- **`usedSeq τ ξ`**: $i\mapsto\xi_i$ for $i<\tau$, and $0$ otherwise. **`appendBlock τ H n ω`**: $H$ on $[0,\tau)$, then $\omega_{i-\tau}$ on
  $[\tau,\tau+n)$, then $0$. The ℕ-subtraction $i-\tau$ only occurs when $i\ge\tau$.
- **`histPath`**: like `adaptivePath`, but the state is $(y_k,\tau_k,\text{usedSeq}\,\tau_k\,\xi)$ and $\nu,G$ may depend on the whole state.
  **`histIncr`** and **`histStep`** are analogous.
- **`Alg3Part X`** $=(\text{path},\,\text{count }k,\,\text{acc}\in\mathbb R,\,\text{rem}\in\mathbb N)$, and **`Alg3State`** is a (coarse, fine) pair of these.
- **`alg3Level ν F n e p`**: if $\text{rem}\le n$, complete the step: the new point is $x'=F(\text{path}(k),\text{acc}+e)$, the path is extended,
  $k+1$, acc $0$, rem $\nu(x')$. Otherwise accumulate: acc$+e$, rem$-n$ (ℕ-subtraction, used only when rem $>n$).
- **`alg3Len s`** = the minimum of the two `rem` values. **`alg3Update`** applies `alg3Level` to both parts with $n=$`alg3Len s`. **`alg3Init`** gives
  the parts $(x_0,0,0,\nu(x_0))$.
- **`alg3Path`** is `adaptivePath` on the state space Alg3State: block length `alg3Len` of the current state, and the update is `alg3Update`.
  **`alg3Fresh`** is the `freshSeq` version, with increment $\sqrt{\text{alg3Len}\cdot\delta}\,\zeta_j$.
- **`levelPath ν F x₀ ξ`** = `adaptivePath (k y ↦ ν(y k)) (k y e ↦ F(y k) e)`. **`alg3Inv`** is the invariant "path = level path at
  count $k$, level-$\tau\le\tau$, $\tau+\text{rem}=\tau^{lev}_k+\nu(y_k(k))$, acc $=\sum_{[\tau^{lev}_k,\tau)}\xi$".
- **`alg3FirstReach κ k`**: the least $n$ with $k\le\kappa(n)$, or $0$ if no such $n$ exists (junk default).
  **`alg3CoarseSeq traj k`** / **`alg3FineSeq traj k`**: take the coarse (fine) path at the first trajectory index whose
  coarse (fine) count is $\ge k$, and evaluate it at $k$.
- Appended: **`complexityBound α β γ ε`** $=\varepsilon^{-2}$ if $\gamma<\beta$; $\varepsilon^{-2}(\log\varepsilon)^2$ if $\beta=\gamma$;
  $\varepsilon^{-2-(\gamma-\beta)/\alpha}$ otherwise (rpow). **`totalCost`** $=\sum_{\ell\le L}\sum_{n<N_\ell}\mathrm{cost}_{\ell,n}$.
  **`blockMean f ω i N x`** $=N^{-1}\sum_{n<N}f_i(\omega_{(i,n)}(x))$, which is junk $0$ at $N=0$ (excluded by $N_\ell>0$).
  **`fineCoarseDiff`**: $Y_0=P^f_0$, $Y_{\ell+1}=P^f_{\ell+1}-P^c_\ell$. **`shiftSeq M w`** $=w_{M+\cdot}$. **`stdNormalSeq`** $=N(0,1)^{\otimes\mathbb N}$.

---

## Per-declaration sections

### 1. `map_adaptivePath_prod`
**Rendering.** Let $E$ be an additive commutative monoid with measurable addition, $\mu$ a probability measure on $E$, $X$ any
measurable space, $\nu_k:(\mathbb N\to X)\to\mathbb N$ measurable, $(y,e)\mapsto G_k(y,e)$ jointly measurable, $x_0\in X$, $k\in\mathbb N$.
Then $\xi\mapsto(y_k(\xi),(\xi_{\tau_k(\xi)+m})_m)$ is measurable, and its law under $\mu^{\otimes\mathbb N}$ is
$\text{adaptiveLaw}(y\mapsto\mu^{*\nu_j(y)},G,x_0)_k\otimes\mu^{\otimes\mathbb N}$.

**Assessment.** True. $\tau_k$ is a stopping time for the natural filtration of $\xi$, and $y_k$ is determined by $\xi_{<\tau_k}$. For each $t$,
$\{y_k\in A,\tau_k=t\}\in\sigma(\xi_{<t})$ is independent of $(\xi_{t+m})_m\sim\mu^{\otimes\mathbb N}$. Summing over $t$ gives the
product law. The marginal law of $y_k$ is then the chain law by induction: $e_k$ is the sum of the first $\nu_k(y_k)$ shifted noises, which has law $\mu^{*\nu_k(y)}$.
Measurability follows by splitting on the countably many values of $(\tau_k,\nu_k(y_k))$. Non-vacuous: $E=X=\mathbb R$, $\mu=N(0,1)$,
$\nu\equiv1$, $G_k(y,e)=e$. No junk: the LHS is a probability measure, and the chain kernel is measurable because it is a composite of the measurable $\nu_k$ with a
kernel on the countable ℕ, followed by a jointly measurable map, so `bind` is not degenerate. Standard result: the strong Markov property of an i.i.d. sequence at a stopping time.

### 2. `map_adaptivePath`
**Rendering.** Same hypotheses. The law of $y_k$ under $\mu^{\otimes\mathbb N}$ equals $\text{adaptiveLaw}(y\mapsto\mu^{*\nu_j(y)},G,x_0)_k$.

**Assessment.** True: it is the first marginal of #1. Non-vacuous (as in #1), no junk. The adaptive path is a Markov chain with transition
"apply $G_k$ to a block of $\nu_k(y)$ i.i.d. noises".

### 3. `map_adaptiveIncr`
**Rendering.** Same hypotheses. The law of $(y_k,e_k)$ equals $\mathcal L(y_k)\otimes_m\kappa$, where $\kappa(y)=\mu^{*\nu_k(y)}$
(`(blockKernel μ).comap (ν k)`).

**Assessment.** True: $e_k=\sum_{i<\nu_k(y_k)}w_i$ with $(y_k,w)\sim\mathcal L(y_k)\otimes\mu^{\otimes\mathbb N}$ by #1. The kernel is Markov,
so `compProd` is genuine. Non-vacuous, no junk. This is the conditional law of the $k$-th increment given the path so far.

### 4. `map_freshPath`
**Rendering.** $\rho$ is a probability measure on any measurable space $E$, and $G$ is jointly measurable. Under $\rho^{\otimes\mathbb N}$, the law of
$p_k$ = `freshPath G x₀ ζ k` equals $\text{adaptiveLaw}(\text{const }\rho,G,x_0)_k$.

**Assessment.** True: $p_k$ depends only on $\zeta_{<k}$, and $\zeta_k\sim\rho$ is independent of it, so $p_k$ is the chain with kernel
$y\mapsto$ law of $\mathrm{ext}_k(y,G_k(y,\zeta))$. Non-vacuous ($\rho=N(0,1)$), no junk. Standard result: a random recursion driven by i.i.d. noise is a Markov chain.

### 5. `map_adaptiveSeq_eq_freshSeq`
**Rendering.** $\mu$ is a probability measure on $E$ (as in #1) and $\rho$ a probability measure on $E'$. The map $s_k:(\mathbb N\to X)\times E'\to E$ is jointly measurable with
$\rho\circ s_k(y,\cdot)^{-1}=\mu^{*\nu_k(y)}$ for all $k,y$. Then the law of $(y_k(k))_k$ under $\mu^{\otimes\mathbb N}$ equals the law of
`freshSeq` with $G'_k(y,z)=G_k(y,s_k(y,z))$ under $\rho^{\otimes\mathbb N}$.

**Assessment.** True. By #2 and #4 both path chains have the same transition kernel,
$(\rho\circ s_k(y,\cdot)^{-1})$ pushed through $e\mapsto\mathrm{ext}_k(y,G_k(y,e))$, so $\mathcal L(y_K)=\mathcal L(p_K)$ for every $K$. Since $(x_0..x_K)$ is a measurable
function of $y_K$, the finite-dimensional marginals agree, and cylinders form a π-system generating the product σ-algebra. Non-vacuous ($\rho=\mu$,
$s=$ projection, $\nu\equiv1$), no junk. Standard result: equality in law of two Markov chains with the same kernels (a "fresh noise" representation).

### 6. `adaptiveIncr_condLaw_gaussian`
**Rendering.** $\xi_i:\Omega\to\mathbb R$ are i.i.d. $N(0,\delta)$ under $P$ (`iIndepFun` + `HasLaw`, $\delta\in\mathbb R_{\ge0}$). The law of
$(y_k,e_k)$ under $P$ is $\mathcal L(y_k)\otimes_m[y\mapsto N(0,\nu_k(y)\delta)]$.

**Assessment.** True: transfer to the canonical space and apply #3, using $N(0,\delta)^{*n}=N(0,n\delta)$, including
$n=0$: $\delta_0$ = `gaussianReal 0 0` (`step_kernels.py`). `iIndepFun` forces $P$ to be a probability measure. Non-vacuous ($\Omega=\mathbb R^{\mathbb N}$,
$P=N(0,\delta)^{\otimes\mathbb N}$, coordinate maps), no junk. Brownian increments over a stopping-time-determined number of steps.

### 7. `adaptiveIncr_condDistrib_gaussian`
**Rendering.** Additionally $P$ is a probability measure. Then `condDistrib` $(e_k\mid y_k)$ equals $y\mapsto N(0,\nu_k(y)\delta)$ for
$\mathcal L(y_k)$-a.e. $y$.

**Assessment.** True: from #6 and Mathlib's `condDistrib_ae_eq_of_measure_eq_compProd`, which needs only that the target ℝ is
standard Borel, AE-measurability of $e_k$, and a finite kernel. There is no condition on the source space $\mathbb N\to X$. Non-vacuous, no junk (the a.e. is taken
with respect to a probability measure). This is the regular conditional distribution of the increment.

### 8. `adaptivePath_law_gaussian`
**Rendering.** Under the hypotheses of #6, $\mathcal L(y_k)=\text{adaptiveLaw}(y\mapsto N(0,\nu_j(y)\delta),G,x_0)_k$. The product $\nu_j(y)\cdot\delta$ is computed in $\mathbb R_{\ge0}$.

**Assessment.** True: #2 transferred, with $N(0,\delta)^{*n}=N(0,n\delta)$. Non-vacuous, no junk.

### 9. `freshPath_law_gaussian`
**Rendering.** $\zeta_i$ are i.i.d. $N(0,1)$ under $P'$, and $h_k:(\mathbb N\to X)\to\mathbb R_{\ge0}$ is measurable. The law of `freshPath` with
$G'_j(y,z)=G_j(y,\sqrt{h_j(y)}\,z)$ equals $\text{adaptiveLaw}(y\mapsto N(0,h_j(y)),G,x_0)_k$.

**Assessment.** True: #4 with $\sqrt h\,N(0,1)=N(0,h)$, and $\sqrt{\cdot}$ is applied to a nonnegative value, so it is not junk. The kernel $y\mapsto N(0,h_j(y))$ is
measurable, since $v\mapsto N(0,v)$ is measurable. Non-vacuous, no junk.

### 10. `adaptiveSeq_law_eq_fresh`
**Rendering.** $\xi$ i.i.d. $N(0,\delta)$ under $P$; $\zeta$ i.i.d. $N(0,1)$ under $P'$. Then
$\mathcal L_P\big((y_k(k))_k\big)=\mathcal L_{P'}\big(\text{freshSeq}(G_k(y,\sqrt{\nu_k(y)\delta}\,z),x_0,\zeta)\big)$.

**Assessment.** True: #5 transferred, with $\rho=N(0,1)$ and $s_k(y,z)=\sqrt{\nu_k(y)\delta}\,z$. Non-vacuous, no junk. Standard fact: adaptive
EM-type recursions driven by Brownian increments on a base grid equal, in law, recursions driven by fresh scaled normals.

### 11. `adaptivePairs_law_eq_fresh`
**Rendering.** The special case $X=\mathbb N\times\mathbb R$, $G_k(y,e)=(\nu_k(y),e)$, $x_0=(0,0)$ of #10. The joint law of the sequence of
(block length, increment) pairs is the same as that of $(\nu_k,\sqrt{\nu_k\delta}\,\zeta_k)$.

**Assessment.** True: an instance of #10, since $G$ is automatically measurable. Non-vacuous, no junk.

### 12. `adaptiveEM_law_eq_freshEM`
**Rendering.** $a,b:\mathbb R^2\to\mathbb R$ are jointly measurable, $\nu:\mathbb R^2\to\mathbb N$ is measurable, and $H=\nu\delta$ (in $\mathbb R_{\ge0}$). With $\xi$ i.i.d.
$N(0,\delta)$ and $\zeta$ i.i.d. $N(0,1)$: $\mathcal L_P(\text{adaptiveEM}(a,b,\nu,\delta,S_0,\xi))=\mathcal L_{P'}(\text{freshEM}(a,b,H,S_0,\zeta))$.

**Assessment.** True: #10 with $G_k(y,dW)=\text{EMstep}(\nu(y_k)\delta,y_k,dW)$. The real casts $\uparrow\nu\cdot\uparrow\delta=\uparrow(\nu\delta)$ agree. A Monte Carlo
check of the marginals agrees (`mc_laws.py`). Non-vacuous, no junk. Adaptive-step EM equals, in law, EM with fresh $N(0,h)$ increments.

### 13. `adaptiveEM_fine_coarse`
**Rendering.** The conjunction of #12 for $(\nu_f,H_f)$ and for $(\nu_c,H_c)$, with the same $\xi$ and $\zeta$. These are *marginal* laws only.

**Assessment.** True: #12 applied twice. Non-vacuous, no junk. It does not assert a joint (coupled) law; that is #27.

### 14. `adaptiveEM_2_4`
**Rendering.** Two setups $(P_i,\nu_i,\delta_i,\xi_i)$, $i=1,2$, with $\xi_i$ i.i.d. $N(0,\delta_i)$ and $\nu_1(x)\delta_1=\nu_2(x)\delta_2$ for all $x$.
$\Phi$ is AE-strongly measurable with respect to the law of path 1. Then $\Phi(\text{path}_1)\in L^1(P_1)\iff\Phi(\text{path}_2)\in L^1(P_2)$, and
$E_{P_1}\Phi(\text{path}_1)=E_{P_2}\Phi(\text{path}_2)$.

**Assessment.** True: by #12 both laws equal the freshEM law with $H=\nu_1\delta_1=\nu_2\delta_2$; an i.i.d. $N(0,1)$ sequence exists on
`stdNormalSeq`. Then use `integrable_map_measure` and `integral_map`. Non-vacuous ($\nu_1=2,\delta_1=1,\nu_2=1,\delta_2=2$). In the non-integrable case the integral
equality is $0=0$, but this is consistent with the ↔ conjunct, so the statement is not junk-dependent. This is the invariance of the law under refining the base grid while keeping
the step sizes.

### 15. `adaptiveEM_mlmc_theorem1`
**Rendering.** $(\Omega,\mu)$ is a probability space; $a,b$ are measurable; $\nu^f_\ell,\nu^c_\ell$ are measurable; $\delta:\mathbb N\to\mathbb R_{\ge0}$ with
$\nu^f_\ell(x)\delta_\ell=\nu^c_\ell(x)\delta_{\ell+1}$ for all $\ell,x$; $\Phi_\ell$ is measurable; $P:\mathbb R^{\mathbb N}\to\mathbb R$ is integrable for
$N(0,1)^{\otimes\mathbb N}$. The samples $\omega_{(\ell,n)}:\Omega\to\mathbb R^{\mathbb N}$ are independent, each with law $N(0,1)^{\otimes\mathbb N}$. The costs are integrable with
$E[\mathrm{cost}_{\ell,n}]=C_\ell$. The constants satisfy $\alpha,\beta,\gamma,c_1,c_2,c_3>0$ and $\min(\beta,\gamma)/2\le\alpha$. Also $P^f_\ell\in L^2$,
$|E[P^f_\ell-P]|\le c_1 2^{-\alpha\ell}$, $\mathrm{Var}(Y_\ell)\le c_2 2^{-\beta\ell}$ (with $Y_0=P^f_0$, $Y_{\ell+1}=P^f_{\ell+1}-P^c_\ell$) and
$C_\ell\le c_3 2^{\gamma\ell}$. Here $P^f_\ell(z)=\Phi_\ell(\text{adaptiveEM}(\nu^f_\ell,\delta_\ell,\sqrt{\delta_\ell}z))$ and
$P^c_\ell(z)=\Phi_\ell(\text{adaptiveEM}(\nu^c_\ell,\delta_{\ell+1},\sqrt{\delta_{\ell+1}}z))$.
Conclusion: $\exists c_4>0\ \forall\varepsilon\in(0,e^{-1})\ \exists L\in\mathbb N,\ N:\mathbb N\to\mathbb N_{>0}$ such that
$E_\mu\big[(\sum_{\ell\le L}N_\ell^{-1}\sum_{n<N_\ell}Y_\ell(\omega_{(\ell,n)})-E P)^2\big]<\varepsilon^2$ and
$E_\mu[\sum_{\ell\le L}\sum_{n<N_\ell}\mathrm{cost}_{\ell,n}]\le c_4\,\text{complexityBound}(\alpha,\beta,\gamma,\varepsilon)$.

**Assessment.** True. By #14 and `hcons`, $P^c_\ell\overset{d}{=}P^f_\ell$, so $P^c_\ell\in L^2$ and $EP^c_\ell=EP^f_\ell$. The sum of
$EY_\ell$ telescopes to $EP^f_L$. Independence gives MSE $=(EP^f_L-EP)^2+\sum V_\ell/N_\ell$, and $E[\text{totalCost}]=\sum N_\ell C_\ell\le\sum N_\ell c_3 2^{\gamma\ell}$.
Giles' choice of $L,N_\ell$ then gives the three regimes. A strict $<\varepsilon^2$ is achieved by taking bias$^2<\varepsilon^2/2$. `mlmc_complexity.py`
checks MSE $<\varepsilon^2$ and bounded cost/bound ratios for all three regimes, at and above the boundary $\alpha=\min(\beta,\gamma)/2$. The ratio blows up
when $\alpha$ is below the boundary, so that hypothesis is genuinely used.

Junk check: `variance` would be $0$ for $Y_\ell\notin L^2$, but $Y_\ell\in L^2$ by the above. The MSE integrand is integrable (a finite sum of $L^2$ terms, squared),
and the cost integrand is integrable. So no junk is involved. $C_\ell$ may be negative, which only makes the bound easier.

Non-vacuous: $\Phi\equiv0$, $P\equiv0$, $\nu^f=\nu^c=1$, $\delta\equiv1$, $\mathrm{cost}\equiv1$, $C\equiv1$, $\alpha=\beta=\gamma=1$, $c_i=1$, and
$\Omega=(\mathbb R^{\mathbb N})^{\mathbb N\times\mathbb N}$ with the product of `stdNormalSeq` and coordinate $\omega$.

Weaker than standard: $c_4$ may depend on the whole instance, not just $(\alpha,\beta,\gamma,c_i)$, though it is still uniform in $\varepsilon$. The rates are hypotheses, not
derived. Standard result: Giles (2008) / Cliffe–Giles–Scheichl–Teckentrup MLMC complexity theorem for adaptive EM with consistent fine/coarse
step sizes.

### 16. `adaptiveCount_condLaw`
**Rendering.** $N_i:\Omega\to\mathbb N$ are i.i.d. Poisson($m$) under $P$. The law of $(y_k,e_k)$ (with $e_k$ a sum of $\nu_k(y_k)$ counts) is
$\mathcal L(y_k)\otimes_m[y\mapsto\mathrm{Poi}(\nu_k(y)m)]$.

**Assessment.** True: #3 transferred, with $\mathrm{Poi}(m)^{*n}=\mathrm{Poi}(nm)$ and $\mathrm{Poi}(0)=\delta_0$ in Mathlib's formula with $0^0=1$
(`step_kernels.py`). Non-vacuous, no junk. Poisson-process increments over adaptively chosen numbers of unit intervals.

### 17. `adaptiveCount_law_eq_fresh`
**Rendering.** $N$ is as in #16. $\zeta_k:\Omega'\to\mathbb N^{\mathbb N}$ are i.i.d. in $k$, each with law $\bigotimes_n\mathrm{Poi}(nm)$. Then the law of $(y_k(k))_k$ driven by
$N$ equals the law of `freshSeq` with $G'_k(y,z)=G_k(y,z_{\nu_k(y)})$.

**Assessment.** True: #5 with $\rho=\bigotimes_n\mathrm{Poi}(nm)$ and $s_k(y,z)=z_{\nu_k(y)}$, which is measurable because $\nu_k$ is ℕ-valued. Then
$\rho\circ s_k(y,\cdot)^{-1}=\mathrm{Poi}(\nu_k(y)m)=\mathrm{Poi}(m)^{*\nu_k(y)}$. Each $\mathrm{Poi}(nm)$ is a probability measure, so `infinitePi` is not junk $0$.
Non-vacuous ($\Omega'=(\mathbb N^{\mathbb N})^{\mathbb N}$, coordinates). The fresh-noise device is unusual but valid.

### 18. `map_histPath_prod`
**Rendering.** As in #1, but the state is $(y_k,\tau_k,\xi\mathbb 1_{[0,\tau_k)})$ and $\nu,G$ may depend on all of it. The law of
$(\text{state}_k,(\xi_{\tau_k+m})_m)$ is $\mathcal L(\text{state}_k)\otimes\mu^{\otimes\mathbb N}$.

**Assessment.** True by the same stopping-time argument as #1; the state is $\mathcal F_{\tau_k}$-measurable. Measurability holds under `hν` and `hG`, so the LHS is a
probability measure and the identity is not $0=0$. Non-vacuous, no junk. Strong Markov property at a stopping time, with the full past.

### 19. `histIncr_condLaw_gaussian`
**Rendering.** $\xi$ is i.i.d. $N(0,\delta)$. The law of $(\text{histState}_k,\text{histIncr}_k)$ is $\mathcal L(\text{state}_k)\otimes_m[p\mapsto N(0,\nu_k(p)\delta)]$.

**Assessment.** True: #18 plus the Gaussian block law. Non-vacuous, no junk.

### 20. `adaptiveIncr_condLaw_hist_gaussian`
**Rendering.** For the plain adaptive path, the law of $((y_k,\tau_k,\xi\mathbb 1_{[0,\tau_k)}),e_k)$ equals
$\mathcal L(y_k,\tau_k,\xi\mathbb 1_{[0,\tau_k)})\otimes_m\big[(y,(\tau,h))\mapsto N(0,\nu_k(y)\delta)\big]$ (`prodMkRight` ignores $(\tau,h)$).

**Assessment.** True. Given the full used history, the increment is a fresh $N(0,\nu_k(y_k)\delta)$; this is #1/#18 with the extra
$\mathcal F_{\tau_k}$-measurable coordinates. Non-vacuous, no junk.

### 21. `histCount_condLaw`
**Rendering.** The Poisson analogue of #19: kernel $p\mapsto\mathrm{Poi}(\nu_k(p)m)$.

**Assessment.** True (#18 + Poisson convolution). Non-vacuous, no junk.

### 22. `alg3CoarseSeq_alg3Path`
**Rendering.** For any $X$, any $\nu^c,\nu^f:X\to\mathbb N$ with values $\ge1$, any $F^c,F^f$, $x^c_0,x^f_0$ and **every** real sequence $\xi$: the coarse
sequence extracted from the Algorithm 3 trajectory (`alg3Path`, first index where the coarse count reaches $k$, coarse path at $k$) equals
`adaptiveSeq` with block length $\nu^c(y_k)$ and update $F^c(y_k,\cdot)$, driven by the same $\xi$.

**Assessment.** True (pathwise). By induction the invariant `alg3Inv` holds for each level: the path equals the level path at the current count,
$\tau+\text{rem}=\tau^{lev}_k+\nu(y_k(k))$, and acc is the partial block sum. Since rem $\ge1$, `alg3Len` $\ge1$, so $\tau$ strictly increases, each level completes after
finitely many steps, and counts rise by at most 1 per step. Hence the first index with count $\ge k$ has count exactly $k$, and the path there is $y_k$.
`alg3_check.py` confirms this on 60 random instances with exact rationals: equality, the invariant, and 0/1 count steps all hold. Non-vacuous (any $\xi$, $\nu^c=2,\nu^f=1$).
No junk: under the hypotheses `alg3FirstReach` never uses its fallback $0$. Both hypotheses are needed. With $\nu^c\in\{0,1\}$ the
fine level can stall, and then the fallback gives a wrong value (16/30 failures). This is the correctness of an event-driven merge of two adaptive grids
on a shared Brownian path.

### 23. `alg3FineSeq_alg3Path`
**Rendering.** As #22, for the fine level ($\nu^f,F^f,x^f_0$).

**Assessment.** True (same argument, checked in `alg3_check.py`). Non-vacuous, no junk, both hypotheses needed.

### 24. `algorithm3_law`
**Rendering.** $\zeta$ is i.i.d. $N(0,1)$; $\nu^c,\nu^f$ are measurable and $\ge1$; $F^c,F^f$ are jointly measurable; $\delta\ge0$. The coarse sequence extracted from
`alg3Fresh` (fresh increments $\sqrt{\text{alg3Len}\cdot\delta}\,\zeta_j$) has the law of `freshSeq` $(F^c(y_k,\sqrt{\nu^c(y_k)\delta}\,z))$, and
likewise for the fine sequence.

**Assessment.** True. `alg3Fresh` is exactly the #10 fresh representation of the state chain `alg3Path` with $\xi$ i.i.d.
$N(0,\delta)$. `alg3CoarseSeq` is measurable (Nat.find over countably many ℕ-valued coordinates). Then apply #22 and #10. Non-vacuous, no junk.

### 25. `algorithm3_joint_law`
**Rendering.** Add $\xi$ i.i.d. $N(0,\delta)$ under $P$. The joint law of (coarse, fine) extracted from `alg3Fresh`$(\zeta)$ equals the joint law of
$(\text{adaptiveSeq}^c(\xi),\text{adaptiveSeq}^f(\xi))$ with the **same** $\xi$.

**Assessment.** True: the state-chain law is equal by #10, and the pair is a measurable function of it, so by #22/#23 it is pathwise the adaptive pair.
Monte Carlo agrees on the coupling statistic $E(S^c_k-S^f_k)^2$ (`mc_laws_big.py`, $4\times10^5$ paths, $|z|\le1.9$; the pathwise
$\xi$-block version matches to $2\cdot10^{-16}$). Non-vacuous, no junk. Standard fact: the MLMC fine/coarse coupling through a shared Brownian path.

### 26. `algorithm3_EM_law`
**Rendering.** #24 with $X=\mathbb R^2$, $F^{c/f}(x,dW)=\text{EMstep}(\nu^{c/f}(x)\delta,x,dW)$, $x_0=(0,S_0)$. The marginals equal
`freshEM` with $H=\nu^{c/f}\delta$.

**Assessment.** True: an instance of #24, using $\uparrow\nu\cdot\uparrow\delta=\uparrow(\nu\delta)$. Non-vacuous, no junk.

### 27. `algorithm3_EM_joint_law`
**Rendering.** #25 for EM: the joint (coarse, fine) law from `alg3Fresh` equals the law of $(\text{adaptiveEM}(\nu^c,\xi),\text{adaptiveEM}(\nu^f,\xi))$ with a
shared $\xi$ i.i.d. $N(0,\delta)$.

**Assessment.** True: an instance of #25. The definitions match syntactically (`(↑(νc x):ℝ) * ↑δ`). The Monte Carlo check is in `mc_laws.py`, `mc_laws_se.py` and
`mc_laws_big.py`. The two smaller runs gave $|z|$ up to about 2.9 at $k=3,6$; the $4\times10^5$ run gave $z=0.53$ and $0.43$, consistent with noise. An
independent coupling gives about $3\times$ larger values, so the statistic does discriminate. Non-vacuous, no junk. This is the MLMC coupling for adaptive EM (Algorithm 3).
