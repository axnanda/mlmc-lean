# Blind read-back report: R2 (1-D QMC, random-shift lattice rules, MLQMC complexity)

| Field | Value |
|---|---|
| Date | 2026-10-07 |
| Packet | `readback/round12/packet_R2_qmc1d.lean` |
| Declarations audited | 22: 17 theorems, plus the 5 definitions `latticeRule`, `shiftedLatticeRule`, `torusLift`, `torusLattice` and `shiftedQMC` (appended) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round12/work_R2/` (`kh_bounds.py/.out`, `random_shift.py/.out`, `complexity.py/.out`; Lean scratch files `scratch_packet.lean/.out`, `nonvacuity.lean/.out`, `bridge.lean/.out`; an empty `.out` means the file compiled with no errors) |

Sources I used: the packet; Mathlib sources under `.lake/packages/mathlib` (`eVariationOn`,
`BoundedVariationOn`, `MeasurePreserving`, `evariance`/`variance`, `UnitAddCircle`/`UnitAddTorus`,
`AddCircle.equivIco`, `QuotientAddGroup.equivIcoMod`, `toIcoMod_zero_one`, `AddCircle.measureSpace`,
`AddCircle.measure_univ`, `measurableEquivIco`, `iIndepFun_infinitePi`,
`measurePreserving_eval_infinitePi`); and my own compilations. I compiled a scratch copy of the
packet (renamed namespace `Audit`, `import MlmcLean`, proofs `sorry`). Every statement elaborates
as rendered below. All arithmetic is in $\mathbb R$ with casts at the leaves, e.g.
`(↑i + 1) / ↑N`, `↑R * (↑R - 1)` and `1 / (12 * ↑N ^ 2)`. There is no ℕ-division and no
ℕ-subtraction anywhere.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `qmc_error_le_of_monotoneOn` | theorem | true (sharp) | no | no |
| 2 | `qmc_error_le_of_boundedVariationOn` | theorem | true (sharp) | no | no |
| – | `latticeRule` | def | – | – | – |
| 3 | `latticeRule_error_le` | theorem | true (sharp for every $u$) | no | no |
| 4 | `latticeRule_error_le_variation_div` | theorem | true | no | no |
| 5 | `latticeRule_half_error_le` | theorem | true (sharp) | no | no |
| – | `shiftedLatticeRule` | def | – | – | – |
| 6 | `shiftedLatticeRule_error_le` | theorem | true (sharp) | no | no |
| 7 | `latticeRule_randomShift` | theorem | true | no | no |
| 8 | `latticeRule_replicates` | theorem | true | no | no |
| 9 | `shiftedLatticeRule_randomShift` | theorem | true | no | no |
| 10 | `latticeRule_vs_monteCarlo` | theorem | true | no | no |
| 11 | `variance_latticeRule_id_vs_mc` | theorem | true | no | no |
| – | `torusLift`, `torusLattice`, `shiftedQMC` | defs | – | – | – |
| 12 | `rank1Lattice_torus_replicates` | theorem | true | no | no |
| 13 | `mlqmc_complexity_core_of_lt` | theorem | true (exponent sharp) | no | no |
| 14 | `mlqmc_complexity_core` | theorem | true (exponent sharp) | no | no |
| 15 | `mlqmc_complexity` | theorem | true | no | no |
| 16 | `mlqmc_complexity_of_lt` | theorem | true | no | no |
| 17 | `mlqmc_complexity_lt_two` | theorem | true | no | no |

## Main points for a human auditor

1. **All 17 theorems are true, none is vacuous, and none depends on a junk value.** I found no
   false statement.
2. **`(eVariationOn f (Icc 0 1)).toReal` is never a junk 0.** Every theorem that uses it assumes
   `BoundedVariationOn f (Icc 0 1)`, which means `eVariationOn ≠ ⊤`. In T15–T17 this is
   `hf : ∀ ℓ, BoundedVariationOn (f ℓ) …`, so `hV` constrains the true variation. A function of
   bounded variation on $[0,1]$ is bounded there and agrees on $[0,1]$ with a Borel function (a
   difference of monotone functions extended monotonically). Hence every
   `∫ y in 0..1, f y` is a genuine Lebesgue integral. The same holds for every expectation,
   variance and `MemLp` in the packet: the random variables are bounded a.e. and a.e. equal to
   measurable functions.
3. **`MeasurePreserving U μ (volume.restrict (Icc 0 1))` forces `μ univ = 1`.** I proved this in
   Lean (`nonvacuity.lean`). The same holds for `MeasurePreserving U μ volume` on
   `UnitAddTorus (Fin 1)`, whose volume is a product of the Haar measure on `AddCircle 1`, of
   total mass 1. So every probabilistic statement lives on a probability space even though no
   `IsProbabilityMeasure` instance is assumed.
4. **The constants are exactly the classical Koksma constants and are sharp.** Exact
   rational-arithmetic checks are in `kh_bounds.out`.
   - The step $1_{(0,1]}$ attains equality in T1, T2 and T6.
   - The steps $1_{(u/N,1]}$ and $1_{[0,u/N)}$ attain $\max(u,1-u)V/N$ in T3 for every tested
     $u$, including $u=0, 1/2, 1$.
   - The bound $\max(u,1-u)/N$ is exactly the star discrepancy of $\{(i+u)/N\}$, and $u=1/2$
     (T5) is the optimal midpoint rule with $D^*_N = 1/(2N)$.
5. **The complexity theorems T13–T17 put `∃ K` before `∀ ε`**, so $K$ cannot depend on $\varepsilon$.
   - An explicit construction meets every bound: $L$ minimal with bias $\le\varepsilon/2$, and
     $N_\ell=\lceil\mu(s_\ell^2/C_\ell)^{1/3}\rceil$ from the Lagrange multiplier. I checked it
     for $\varepsilon$ down to $10^{-40}$, and $\text{cost}/\varepsilon^{-p}$ stays bounded.
   - A Hölder lower bound valid for every admissible $(L,N)$ shows the exponents cannot be
     lowered, so they are not trivially satisfiable.
   - The excluded regimes are genuinely false. When $b=g\le a$ there is a factor
     $|\log\varepsilon|^{3/2}$. When $b<g$ and $b<a$, $\max(1,g/a)$ is too small.
   - T17's conditions $g<2a$ and $g<a+b$ are exactly the conditions for complexity below
     $\varepsilon^{-2}$. At $g=2a$ or $g=a+b$, every scheme needs $\gtrsim\varepsilon^{-2}$.
   - Details are in `complexity.out`.
6. **Harmless generality: `C ℓ` and `c₃` may be negative in T15–T17.** Only `hC : C ℓ ≤ c₃ 2^{gℓ}`
   is assumed, and there is no `0 < c₃`. When $c_3\le0$, the cost $\sum N_\ell C_\ell\le 0$ and
   the cost inequality is trivial. The statement is monotone in $C$, so this only adds trivially
   true instances. The intended instances ($C_\ell=c_3 2^{g\ell}$ with $c_3>0$) are covered.
   `hbias` and `hV` force $c_1,c_2\ge0$, and they admit non-trivial instances, e.g. the telescoping
   $P_\ell(y)=y^2+2^{-\ell}y$ ($a=b=1$), or the discontinuous $P_\ell(y)=\lfloor 2^\ell y\rfloor/2^\ell$
   ($a=1$, $b=0$, $V(f_\ell)=1$).
7. **Coverage gap, not an error: the logarithmic boundary case is missing.** No theorem gives
   the exact-exponent bound $\varepsilon^{-1}|\log\varepsilon|^{3/2}$ for $b=g\le a$; only T17's
   "some $p<2$" covers it. Some hypotheses are stronger than needed: T12 assumes `hU` for all
   `r` and mutual (`iIndepFun`) independence, while `r < R` and pairwise independence would
   suffice.
8. **The torus bridge (T12) is exact.** `AddCircle.equivIco 1 0 ↑x` has value `Int.fract x`. I
   proved this in Lean (`bridge.lean`, via `toIcoMod_zero_one`). `Measurable (torusLift f)` holds
   genuinely (Borel, not just a.e.) even though `f` is arbitrary off $[0,1]$, because
   `torusLift f` only reads $f$ on $[0,1)$.

---

## Per-declaration sections

Throughout, $V := (\text{eVariationOn } f\ [0,1]).\text{toReal}$, which equals the true total
variation of $f$ on $[0,1]$ whenever `BoundedVariationOn f (Icc 0 1)` holds. Also
$I := \int_0^1 f(y)\,dy$ (`intervalIntegral`, i.e. the integral over $(0,1]$).

### 1. `qmc_error_le_of_monotoneOn`

**Rendering.** Let $f:\mathbb R\to\mathbb R$ be monotone (non-decreasing) on $[0,1]$, $N\in\mathbb N$
with $N>0$, and $x:\mathbb N\to\mathbb R$ with $i/N\le x_i\le (i+1)/N$ for all $i<N$ (real
division). Then
$$\Big|\tfrac1N\sum_{i<N} f(x_i)-\int_0^1 f\Big|\le \frac{f(1)-f(0)}{N}.$$

**Assessment.** True. On each cell $J_i=[i/N,(i+1)/N]$, monotonicity gives
$f(i/N)\le f(x_i)\le f((i+1)/N)$ and $\frac1N f(i/N)\le\int_{J_i}f\le\frac1N f((i+1)/N)$. So the
cell error is at most $(f((i+1)/N)-f(i/N))/N$, and summing telescopes.

- Junk values: none. A function monotone on $[0,1]$ is interval-integrable (it is bounded and
  equals a monotone function of $\mathbb R$ on $[0,1]$). All $x_i\in[0,1]$, and $f(1)\ge f(0)$.
- Sharp: $f=1_{(0,1]}$ with $x_i=i/N$ gives error $1/N=(f(1)-f(0))/N$ (`kh_bounds.out`).
- Random and adversarial tests show ratio $\le1$.
- Non-vacuous: e.g. $f=\mathrm{id}$, $x_i=i/N$.
- Standard fact: the elementary error bound for one point per cell (Riemann sums) for monotone
  integrands.

### 2. `qmc_error_le_of_boundedVariationOn`

**Rendering.** Same as T1, but with $f$ of bounded variation on $[0,1]$ ($\text{eVariationOn}\ne\infty$)
instead of monotone. Then $|\frac1N\sum_{i<N}f(x_i)-I|\le V/N$.

**Assessment.** True. For $y\in J_i$, $|f(x_i)-f(y)|\le \mathrm{Var}(f,J_i)$, so
$|\frac1N f(x_i)-\int_{J_i}f|\le \mathrm{Var}(f,J_i)/N$. Variation is additive over adjacent
closed intervals (`eVariationOn.Icc_add_Icc`), so $\sum_i\mathrm{Var}(f,J_i)=V$.

- Junk values: none. The `BoundedVariationOn` hypothesis rules out `toReal ⊤ = 0`, and BV on
  $[0,1]$ implies interval-integrable.
- Sharp: $1_{(0,1]}$, $x_i=i/N$.
- An adversarial check over 400 random piecewise-linear functions with jumps (each $x_i$ at the
  cell sup or inf) gave maximum ratio $0.98$, always $\le1$.
- Non-vacuous: any step function (BV proved in Lean for a step function, `nonvacuity.lean`).
- Standard fact: a 1-D Koksma–Hlawka-type bound with discrepancy $\le 1/N$.

### Definition `latticeRule`

**Rendering.** $\mathrm{latticeRule}(f,N,u)=\frac1N\sum_{i=0}^{N-1} f\big(\frac{i+u}{N}\big)$. This
is the 1-D rank-1 lattice rule $\{i/N\}$ shifted by $u/N$. When $N=0$ it is $0\cdot0=0$, but
every theorem assumes $N>0$.

### 3. `latticeRule_error_le`

**Rendering.** If $f$ is BV on $[0,1]$, $N>0$ and $u\in[0,1]$, then
$|\mathrm{latticeRule}(f,N,u)-I|\le \max(u,1-u)\,V/N$. The expression parses as $(\max(u,1-u)\cdot V)/N$.

**Assessment.** True. Split each cell at its node $x_i=(i+u)/N$. Then
$|\int_{\text{left}}(f(x_i)-f)|\le \frac uN\mathrm{Var}_{\text{left}}$ and
$|\int_{\text{right}}(f(x_i)-f)|\le\frac{1-u}N\mathrm{Var}_{\text{right}}$, and the left and
right variations add up to the cell variation. The bound equals Koksma's inequality, since the
star discrepancy of $\{(i+u)/N\}$ is $\frac1{2N}+\frac{|u-1/2|}N=\max(u,1-u)/N$.

- Sharp for every $u$: $1_{(u/N,1]}$ has error $(1-u)/N$ and $1_{[0,u/N)}$ has error $u/N$,
  both with $V=1$. I verified exact equality for $N\in\{1,3,8\}$ and $u\in\{0,\frac15,\frac12,\frac7{10},1\}$.
- Junk values: none. All nodes lie in $[0,1]$.
- Non-vacuous.
- Standard fact: Koksma's inequality in 1-D for a shifted equispaced rule.

### 4. `latticeRule_error_le_variation_div`

**Rendering.** Same hypotheses as T3; the conclusion is $|\mathrm{latticeRule}(f,N,u)-I|\le V/N$.

**Assessment.** True. It follows from T3 because $\max(u,1-u)\le1$; it is also a special case
of T2. Sharp at $u\in\{0,1\}$. No junk dependence; not vacuous.

### 5. `latticeRule_half_error_le`

**Rendering.** If $f$ is BV on $[0,1]$ and $N>0$, then
$|\frac1N\sum_{i<N}f(\frac{2i+1}{2N})-I|\le V/(2N)$. Here `1 / 2` is the real number $0.5$,
because `latticeRule` takes `u : ℝ`.

**Assessment.** True; it is T3 with $u=1/2$.

- Sharp: $f=1_{(1/(2N),1]}$ gives error exactly $1/(2N)$, and the $u=\frac12$ rows of
  `kh_bounds.out` show equality.
- Random ratio $\le 0.40$.
- Standard fact: the midpoint rule is the optimal-discrepancy $N$-point set ($D^*_N=1/(2N)$)
  in Koksma's inequality.

### Definition `shiftedLatticeRule`

**Rendering.** $\mathrm{shiftedLatticeRule}(f,N,\Delta)=\frac1N\sum_{i<N} f(\{i/N+\Delta\})$, where
$\{\cdot\}$ is `Int.fract`. This is the rank-1 lattice rule $\{i/N\}$ randomly shifted modulo 1 by
$\Delta\in\mathbb R$.

### 6. `shiftedLatticeRule_error_le`

**Rendering.** If $f$ is BV on $[0,1]$ and $N>0$, then for every $\Delta\in\mathbb R$,
$|\mathrm{shiftedLatticeRule}(f,N,\Delta)-I|\le V/N$.

**Assessment.** True. With $u:=\{N\{\Delta\}\}\in[0,1)$, the multiset
$\{\{i/N+\Delta\}:i<N\}$ equals $\{(j+u)/N:j<N\}$. So the rule equals
$\mathrm{latticeRule}(f,N,u)$ and T4 applies.

- I verified the point-set identity and the bound exactly for 400 random rational $\Delta$,
  including negative and large ones.
- Sharp: $\Delta\in\mathbb Z$ with $f=1_{(0,1]}$ gives error $1/N$.
- All points lie in $[0,1)$; no junk dependence.

### 7. `latticeRule_randomShift`

**Rendering.** Let $(\Omega,\mu)$ be a measure space and $U:\Omega\to\mathbb R$ measurable with
pushforward $U_*\mu=\lambda|_{[0,1]}$, so $U$ is uniform and $\mu$ is necessarily a probability
measure. Let $f$ be BV on $[0,1]$ and $N>0$. Then all of the following hold:

- (a) $\mu$-a.e., $|\mathrm{latticeRule}(f,N,U)-I|\le V/N$;
- (b) $\mathrm{latticeRule}(f,N,U)\in L^2(\mu)$;
- (c) $\mathbb E[\mathrm{latticeRule}(f,N,U)]=I$;
- (d) $\mathbb E[(\mathrm{latticeRule}(f,N,U)-I)^2]\le (V/N)^2$;
- (e) $\mathrm{Var}(\mathrm{latticeRule}(f,N,U))\le (V/N)^2$.

**Assessment.** True.

- (a): $U\in[0,1]$ a.e., then T4. The "a.e." is necessary because $U$ may leave $[0,1]$ on a
  null set.
- (b): the composition is a.e. equal to a Borel function (see main point 2) and is bounded a.e.,
  and $\mu$ is finite.
- (c): $\int_0^1\frac1N\sum_i f(\frac{i+u}N)\,du=\sum_i\int_{i/N}^{(i+1)/N}f=I$.
- (d) follows from (a) and $\mu(\Omega)=1$; (e) follows from (c) and (d).
- I checked (c)–(e) exactly for 5 integrands (polynomial, jump, kink, extremal step, identity)
  and $N\le5$ (`random_shift.out`).
- `variance` is `(evariance).toReal`. It is finite here, so (e) is a genuine statement.
- Non-vacuous: $\Omega=\mathbb R$, $\mu=\lambda|_{[0,1]}$, $U=\mathrm{id}$, or the product space in
  `nonvacuity.lean`.
- Standard fact: unbiasedness and RMSE $\le V/N$ of the randomly shifted rank-1 lattice rule.

### 8. `latticeRule_replicates`

**Rendering.** $N,R>0$, and $U_r$ is uniform on $[0,1]$ for $r<R$ (`MeasurePreserving`), with
$U_i,U_j$ independent for all distinct $i,j<R$ (pairwise only). $f$ is BV. Let
$\bar Q=\frac1R\sum_{r<R}\mathrm{latticeRule}(f,N,U_r)$. Then:

- (a) $\mathbb E\bar Q=I$;
- (b) $\mathrm{Var}\,\bar Q\le (V/N)^2/R$;
- (c) if $R\ge2$, then
  $\mathbb E\big[\frac1{R(R-1)}\sum_r(Q_r-\bar Q)^2\big]=\mathrm{Var}\,\bar Q$. The cast is
  $(\uparrow R\cdot(\uparrow R-1))^{-1}$ in $\mathbb R$ (checked by elaboration).

**Assessment.** True.

- Pairwise independence makes the $Q_r$ uncorrelated. A.e. measurability is handled by
  replacing $f$ with its Borel version on $[0,1]$, which changes nothing a.e. Equal laws give
  equal means and variances.
- (b): $\mathrm{Var}\,\bar Q=\mathrm{Var}(Q_0)/R$, then T7(e).
- (c): $\mathbb E\sum(Q_r-\bar Q)^2=(R-1)\sigma^2$. I checked this by exact enumeration for
  $R=2,3,4$.
- $\mu$ is a probability measure because $R>0$.
- No junk values; not vacuous (i.i.d. coordinates on $\prod_{\mathbb N}[0,1]$; `nonvacuity.lean`).
- Standard fact: replicated random shifts, and the unbiased standard-error estimator.

### 9. `shiftedLatticeRule_randomShift`

**Rendering.** $\Delta:\Omega\to\mathbb R$ is uniform on $[0,1]$ (measure-preserving), $f$ is BV
and $N>0$. Then:

- (a) for **every** $\omega$, $|\mathrm{shiftedLatticeRule}(f,N,\Delta(\omega))-I|\le V/N$;
- (b) the rule is in $L^2(\mu)$;
- (c) its mean is $I$;
- (d) its MSE about $I$ is at most $(V/N)^2$;
- (e) its variance is at most $(V/N)^2$.

**Assessment.** True.

- (a) is T6 and holds for all real $\Delta$, so "every $\omega$" is legitimate.
- (c): $\int_0^1 f(\{i/N+\delta\})d\delta=I$ by translation invariance mod 1. I checked this
  exactly (`random_shift.out`, "E[S]-I=0").
- The rest is as in T7. No junk; not vacuous.
- Standard fact: the random-shift lattice rule on the torus.

### 10. `latticeRule_vs_monteCarlo`

**Rendering.** $N>0$, $U_n$ is uniform on $[0,1]$ for $n<N$, and the $U_n$ are pairwise
independent for $n<N$. $f$ is BV. Then:

- (a) $\mathbb E[\frac1N\sum_{n<N}f(U_n)]=I$;
- (b) $\mathrm{Var}(\frac1N\sum f(U_n))=\mathrm{Var}(f(U_0))/N$;
- (c) $\mathbb E[(\mathrm{latticeRule}(f,N,U_0)-I)^2]\le (V/N)^2$;
- (d) if $\sigma^2:=\mathrm{Var}(f(U_0))>0$, then
  $\mathbb E[(\mathrm{latticeRule}(f,N,U_0)-I)^2]\,/\,\mathrm{Var}(\text{MC mean})\le V^2/(N\sigma^2)$.

**Assessment.** True.

- (a) and (b) are the standard Monte Carlo identities for pairwise uncorrelated, identically
  distributed, bounded samples. They are genuine: $f(U_n)$ is bounded and a.e. equal to a
  measurable function.
- (c) is T7(d).
- (d): the denominator is $\sigma^2/N>0$, so there is no division by 0, and the inequality is
  $N\cdot\mathrm{MSE}/\sigma^2\le V^2/(N\sigma^2)$.
- I checked it exactly on examples. $N$ serves both as the MC sample size and as the lattice
  size, which is the intended comparison.
- Standard fact: QMC MSE $O(N^{-2})$ versus MC variance $\sigma^2/N$.

### 11. `variance_latticeRule_id_vs_mc`

**Rendering.** Same probabilistic setup as T10, with $f=\mathrm{id}$. Then
$\mathrm{Var}(\frac1N\sum_{n<N}U_n)=\frac1{12N}$ and
$\mathrm{Var}(\mathrm{latticeRule}(\mathrm{id},N,U_0))=\frac1{12N^2}$ (real arithmetic).

**Assessment.** True.

- $\mathrm{latticeRule}(\mathrm{id},N,u)=\frac{N-1}{2N}+\frac uN$, so its variance is
  $\frac1{N^2}\cdot\frac1{12}$. The MC variance is $\frac1{12}/N$ by pairwise independence.
- I checked both exactly for $N=1,2,3,7,10$ (`random_shift.out`).
- These are equalities, and both sides are genuine (bounded variables), so there is no junk.
- Not vacuous.

### Definitions `torusLift`, `torusLattice`, `shiftedQMC`

**Rendering.**

- `torusLift f y` $=f(r(y_0))$, where $y\in\mathbb T^1=$ `Fin 1 → ℝ/ℤ` and $r$ is the
  representative in $[0,1)$ given by `AddCircle.equivIco 1 0`. I proved in Lean that
  $r(\bar x)=\{x\}$ (`bridge.lean`).
- `torusLattice N i` is the torus point $(i/N \bmod 1)$.
- `shiftedQMC f x N u` $=\frac1N\sum_{i<N}f(x_i+u)$ is the generic shifted QMC rule on
  $\mathbb T^d$.

### 12. `rank1Lattice_torus_replicates`

**Rendering.** $U_r:\Omega\to\mathbb T^1$ are measure-preserving onto `volume` (Haar
probability) for **all** $r\in\mathbb N$ and mutually independent (`iIndepFun`). $f$ is BV on
$[0,1]$, and $N,R>0$. Then:

- (a) for all $u\in\mathbb R$, `shiftedQMC (torusLift f) (torusLattice N) N (const ū)` equals
  $\mathrm{shiftedLatticeRule}(f,N,u)$;
- (b) `torusLift f` is (Borel) measurable;
- (c) `torusLift f` is in $L^2(\mathbb T^1)$;
- (d) $\int_{\mathbb T^1}\mathrm{torusLift}\,f=I$;
- (e) the variance of the torus lattice rule as a function of the shift $u\sim$ Haar is at most
  $(V/N)^2$;
- (f) the $R$-replicate mean $\frac1R\sum_{r<R}\mathrm{shiftedQMC}(\ldots)(U_r)$ has mean $I$;
- (g) that mean has variance at most $(V/N)^2/R$.

**Assessment.** True.

- (a): $(x_i+u)_0=\overline{i/N+u}$ and $r(\bar x)=\{x\}$. This is exact, not a.e.
- (b): only $f|_{[0,1)}$ is read. There $f=G-H$ with $G,H$ monotone on $\mathbb R$, hence Borel,
  and `measurableEquivIco` is measurable. So this is genuine measurability despite $f$ being
  arbitrary off $[0,1]$.
- (c): bounded, measurable, and the measure is finite.
- (d): `measurableEquivIco` carries Haar measure to Lebesgue measure on $[0,1)$, and
  `AddCircle.measure_univ` gives mass $1$.
- (e): by (a) and T6, the integrand is within $V/N$ of $I$ everywhere, and its mean is $I$.
- (f) and (g): independence plus T9.
- $\mu$ is a probability measure (proved in Lean). Mutual independence and `hU` for all $r$
  are stronger than needed (pairwise and $r<R$ suffice), which is harmless.
- Non-vacuous: $\Omega=(\mathbb T^1)^{\mathbb N}$ with `infinitePi volume` and coordinate maps
  (compiled in `nonvacuity.lean`).
- Standard fact: the 1-D rank-1 lattice rule as a special case of randomly shifted QMC on the
  torus.

### 13. `mlqmc_complexity_core_of_lt`

**Rendering.** Let $a>0$, $b<g$ and $c_1,c_2,c_3>0$ (reals; $b,g$ may be negative). There exists
$K>0$ such that for every $\varepsilon\in(0,1)$ there exist $L\in\mathbb N$ and
$N:\mathbb N\to\mathbb N_{>0}$ with
$$\big(c_12^{-aL}\big)^2+\sum_{\ell=0}^{L}\Big(\frac{c_22^{-b\ell}}{N_\ell}\Big)^2<\varepsilon^2,\qquad
\sum_{\ell=0}^{L}N_\ell\,c_32^{g\ell}\le K\varepsilon^{-\max(1+(g-b)/a,\;g/a)}$$
(real `rpow` of positive bases). $K$ depends only on $a,b,g,c_i$, not on $\varepsilon$.

**Assessment.** True.

- Upper bound: take $L$ minimal with $c_12^{-aL}\le\varepsilon/2$ and
  $N_\ell=\lceil\mu (s_\ell^2/C_\ell)^{1/3}\rceil$, where $s_\ell=c_22^{-b\ell}$ and $C_\ell=c_32^{g\ell}$.
  Then the cost is at most
  $\sqrt2\,\varepsilon^{-1}(\sum(s_\ell C_\ell)^{2/3})^{3/2}+\sum_{\ell\le L} C_\ell$, which is of
  order $\varepsilon^{-1-(g-b)/a}+\varepsilon^{-\max(0,g/a)}$.
- Numerically (`complexity.out`, $\varepsilon$ down to $10^{-40}$, several parameter sets including
  negative $b,g$), the construction always has MSE $<\varepsilon^2$ and bounded
  cost$/\varepsilon^{-p}$ (maximum about 30–174).
- Sharpness, i.e. the bound is not trivially satisfiable: the Hölder bound gives
  cost $\ge\varepsilon^{-1}(\sum_{\ell\le L_{\min}}(s_\ell C_\ell)^{2/3})^{3/2}$ and cost
  $\ge\sum_{\ell\le L_{\min}}C_\ell$ for every admissible $(L,N)$. This lower bound divided by
  $\varepsilon^{-p}$ stays $\ge 4.5$, and divided by $\varepsilon^{-(p-0.05)}$ it blows up.
- Standard result: the MLQMC complexity theorem (QMC error $V_\ell/N_\ell$) in the regime $b<g$.

### 14. `mlqmc_complexity_core`

**Rendering.** As T13, but with hypothesis $g<b\ \lor\ (a\le b\wedge a<g)$ and exponent $\max(1,g/a)$.

**Assessment.** True.

- When $g<b$: the Lagrange part is $O(\varepsilon^{-1})$ and $\sum C_\ell=O(\varepsilon^{-\max(0,g/a)})$.
- When $a\le b<g$: T13 applies, and $1+(g-b)/a\le g/a$ with $g/a>1$.
- When $a\le b=g$ and $a<g$: $\varepsilon^{-1}|\log\varepsilon|^{3/2}\ll\varepsilon^{-g/a}$.
- Numerics confirm all three regimes and also the sharpness of $p$.
- The excluded regimes really fail. For $b=g\le a$, (lower bound)$/\varepsilon^{-1}$ grows like
  $|\log\varepsilon|^{3/2}$. For $b<g$ with $b<a$ the true exponent is larger.
- No junk; not vacuous.

### 15. `mlqmc_complexity`

**Rendering.** The $U_\ell$ ($\ell\in\mathbb N$) are uniform on $[0,1]$ and pairwise independent
over all $\ell$. Each $f_\ell$ is BV on $[0,1]$, and $C:\mathbb N\to\mathbb R$; $I,a,b,g,c_i$ are
real. Hypotheses: $a>0$; $g<b\lor(a\le b\wedge a<g)$;
$|\sum_{\ell\le L}\int_0^1f_\ell-I|\le c_12^{-aL}$ for all $L$;
$V(f_\ell)\le c_22^{-b\ell}$; $C_\ell\le c_32^{g\ell}$ ($c_i$ not assumed positive).

Conclusion: there exists $K>0$ such that for every $\varepsilon\in(0,1)$ there exist $L$ and $N>0$
with
$\mathbb E[(\sum_{\ell\le L}\mathrm{latticeRule}(f_\ell,N_\ell,U_\ell)-I)^2]<\varepsilon^2$ and
$\sum_{\ell\le L}N_\ell C_\ell\le K\varepsilon^{-\max(1,g/a)}$.

**Assessment.** True.

- The MSE equals bias$^2$ plus $\sum_\ell\mathrm{Var}$, using T7(c) and pairwise independence.
  It is at most $(c_12^{-aL})^2+\sum(c_22^{-b\ell}/N_\ell)^2$ by T7(e), so T14 applies (with
  $c_i$ replaced by $\max(c_i,1)$).
- The MSE integral is genuine: the integrand is bounded a.e. and a.e. measurable, so there is
  no "non-integrable ⇒ 0" junk.
- `hbias` and `hV` force $c_1,c_2\ge0$. If $c_3\le0$ (allowed) the cost bound is trivial, but
  only as a harmless generalisation (main point 6).
- Non-trivial instance: $f_0=y^2+y$ and $f_\ell=-2^{-\ell}y$, with $I=1/3$, $a=b=1$, $c_1=1/2$,
  $c_2=2$, $C_\ell=2^{g\ell}$ and $g<1$, on i.i.d. uniforms.
- Standard result: MLQMC complexity $\varepsilon^{-\max(1,g/a)}$.

### 16. `mlqmc_complexity_of_lt`

**Rendering.** Same as T15, but with $b<g$ instead of the disjunction, and exponent
$\max(1+(g-b)/a,\,g/a)$.

**Assessment.** True. It reduces to T13 exactly as T15 reduces to T14. The exponent is sharp (see
T13). Instance: the discontinuous telescoping $P_\ell=\lfloor2^\ell y\rfloor/2^\ell$ ($a=1$, $b=0$,
$c_1=\frac12$, $c_2=1$) with $g=1$ gives exponent 2, so QMC gains nothing for jumpy levels; the
statement is still correct. No junk; not vacuous.

### 17. `mlqmc_complexity_lt_two`

**Rendering.** Same setting as T15, with hypotheses $a>0$, $g<2a$, $g<a+b$. Then there exists
$p<2$, then $K>0$, such that for every $\varepsilon\in(0,1)$ there exist $L$ and $N$ with
MSE $<\varepsilon^2$ and cost $\le K\varepsilon^{-p}$. The quantifier order is $p$, then $K$,
then $\varepsilon$.

**Assessment.** True. The choice of $p$:

- If $g<b$: $p=\max(1,g/a)<2$.
- If $b<g$: $p=\max(1+(g-b)/a,g/a)<2$, using $g<a+b$ and $g<2a$.
- If $b=g>a$: $p=g/a$.
- If $b=g\le a$: any $p\in(1,2)$, since it absorbs the log factor.

The numerics confirm bounded cost$/\varepsilon^{-p}$ in each case. The hypotheses are exactly
right: at $g=2a$, or at $g=a+b$ with $b<g$, every scheme needs $\gtrsim\varepsilon^{-2}$
(lower-bound ratio bounded away from 0). Not trivially satisfiable, because $p$ and $K$ are fixed
before $\varepsilon$. No junk.

Standard result: MLQMC beats plain MC's $\varepsilon^{-2}$.
