# Blind statement audit: packet L4 (`MlmcLean.Lattice`)

| Field | Value |
|---|---|
| Date | 2026-09-29 |
| Packet | `readback/round10/packet_L4_lattice.lean` |
| Declarations audited | 13 (5 definitions: `dot`, `box`, `crit`, `indexSet`, `boxSize`; 8 lemmas/theorems) |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round10/work_L4/` (each `check_*.py` has a matching `.out`; shared helper `lattice_common.py`; Lean scratch file `elab_check.lean` with its `.out`) |

**Sources used.** I used only the packet, the Mathlib sources under `.lake/packages/mathlib` and a Lean v4.33.1 run of my own scratch file `work_L4/elab_check.lean`. From Mathlib I read `Fintype.piFinset`, `mem_piFinset`, `piFinset_of_isEmpty`, `Nat.floor_of_nonpos`, `Real.rpow_def_of_pos`, `Real.rpow_zero` and the `Real.log` lemmas. The scratch file copies the packet's definitions verbatim, imports only Mathlib, and asks Lean how `^`, `-` and the casts elaborate. It also checks the edge cases: $D=0$, $\mathrm{crit}=0$, $0-1=0$ in ℕ, $x/0=0$, $\lfloor\text{neg}\rfloor_+=0$, and $(1-2^0)^{-1}=0$. It compiles with exit code 0. I opened no repository source, proof, docstring, note or README.

**Notation.** $z:=\mathrm{crit}\,\delta=\#\{d:\delta_d=0\}$, and $m:=z\mathbin{\dot-}1=\max(z-1,0)$ is Lean's ℕ-subtraction. $\mathrm{box}(D,n)=\{0,\dots,n-1\}^D$.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `dot` | def | n/a | n/a | no junk involved |
| 2 | `box` | def | n/a | n/a | no ($D=0$ gives a singleton for every $n$, which is the correct value, not junk) |
| 3 | `crit` | def | n/a | n/a | no junk involved |
| 4 | `card_filter_slab_le` | lemma | **true** (bound is attained) | no | no |
| 5 | `card_filter_mul_le` | lemma | **true** (bound is attained) | no | no |
| 6 | `one_add_rpow_le_exp` | lemma | **true** | no | no |
| 7 | `neg_log_rpow_mul_rpow_le` | lemma | **true** | no | no |
| 8 | `slab_bound` | theorem | **true** | no | no. The ℕ-truncated exponent at $z=0$ only makes it weaker; the version with the natural exponent $-1$ is also true. |
| 9 | `tail_bound` | theorem | **true** | no | no (same remark) |
| 10 | `inner_bound` | theorem | **true** | no | no (same remark) |
| 11 | `sum_box_two_rpow_le_prod` | lemma | **true** (tight as $n\to\infty$) | no | no. `hg` rules out the junk case $(1-2^0)^{-1}=0^{-1}=0$. |
| 12 | `indexSet` | def | n/a | n/a | only when some $\theta_d\le 0$: then the coordinate is frozen at 0 |
| 13 | `boxSize` | def | n/a | n/a | only when some $\theta_d\le0$. Note that it is a **sum** of side lengths, not a cardinality. |

## Main points for a human auditor

1. **All 8 lemmas/theorems are true, none is vacuous, and none depends on a junk value.** Each has an explicit constant, derived below and checked numerically:
   - $K_{\rm slab}=\prod_{\delta_d=0}(1+1/\theta_d)\prod_{\delta_d>0}(1-2^{-\delta_d})^{-1}$
   - $K_{\rm tail}=K_{\rm slab}\sum_{j\ge0}2^{-aj}(1+j)^m$
   - $K_{\rm inner}=K_{\rm slab}$
   - $K=\max(1,(p/\kappa)^pe^{\kappa-p})$ for `one_add_rpow_le_exp`
   - $K=\max(1,(p/(\kappa e))^p)$ for `neg_log_rpow_mul_rpow_le`

   Numerical coverage: 25 $(\theta,\delta)$ configurations with $D=1,2,3$ and crit $0..3$, all breakpoints up to $L=400/200/60$ (extended to $150$ for $D=3$), and 2,160 literal finite-$n$ checks. There were 0 violations. Every supremum stays at or below the explicit $K$, and each one either levels off or converges to its analytic limit.
2. **`crit δ - 1` is ℕ-subtraction.** Lean confirms this: `HPow ℝ ℕ ℝ` via `Monoid.toNPow`, with `HSub ℕ ℕ ℕ`. When $\mathrm{crit}\,\delta=0$ the factor $(1+\cdot)^{\mathrm{crit}\,\delta-1}$ equals $1$, not $(1+\cdot)^{-1}$. This makes the three lattice theorems **weaker, never false**. With the natural real exponent $-1$ they still hold: the sums then decay exponentially, and the numerical ratios are bounded in every $z=0$ case. In `slab_bound` at $z=0$ the second conjunct becomes "slab sum $\le K$", which already follows from the first conjunct.
3. **Quantifier order is the meaningful one.** $K$ is chosen after $(D,\theta,\delta)$, plus $a$ or $c$ where present, and before $n$ and $x$ or $L$. So $K$ is uniform in the truncation level $n$ and in $x$ or $L$. Because the summands are nonnegative, this is equivalent to the same bound for the full sums over $\mathbb N^D$.
4. **Hypotheses.** $\theta_d>0$, $\delta_d\ge0$, $a>0$ and $0\le L$ are each needed. `check_negative_controls.out` has counterexamples for dropping $\theta_d>0$, $\delta_d\ge0$, $a>0$, and $0\le L$ in `tail_bound`. For `inner_bound`, $0\le L$ is needed because at $L<-1$ with $m$ odd the right side is negative while the left side is $0$; I argued this analytically and did not run it. Two hypotheses are **stronger than needed**, which is harmless:
   - `hc : 0 ≤ c` in `inner_bound`: the statement holds for every real $c$.
   - `hp : 0 ≤ p` in `one_add_rpow_le_exp`: for $p<0$ it holds with $K=1$.

   In `neg_log_rpow_mul_rpow_le`, `hp` *is* needed.
5. **The bounds are sharp in the polynomial factor.** Lowering the exponent $m$ by one makes the ratios diverge linearly (negative controls). So the statements are non-trivial and not loose by a power.
6. **`indexSet θ L` is the anisotropic total-degree set $\{\ell\in\mathbb N^D:\theta\cdot\ell\le L\}$ only when all $\theta_d>0$.** I checked this exhaustively in 512 cases. If some $\theta_d\le0$, the junk values $L/0=0$ and $\lfloor\text{neg}\rfloor_+=0$ freeze $\ell_d=0$. Any downstream use should therefore carry $\theta>0$.
7. **`boxSize θ L` is $\sum_d(\lfloor L/\theta_d\rfloor_++1)$.** That is a sum of side lengths: neither the bounding-box cardinality $\prod_d(\cdot)$ nor $|\mathrm{indexSet}|$. It is at least every side length, so `box D (boxSize θ L)` ⊇ `indexSet θ L`, and it works as a truncation level $n$. Check downstream that it is not read as a count or a cost.
8. **$D=0$ is allowed and harmless.** `box 0 n` = {()} for every $n$, including $n=0$ (Lean-checked). The statements hold trivially and honestly: for example, the first conjunct of `slab_bound` reads $1\le K$.

---

## Per-declaration sections

### 1. `dot` (def)

**Rendering.** For $a:\mathrm{Fin}\,D\to\mathbb R$ and $\ell:\mathrm{Fin}\,D\to\mathbb N$, $\mathrm{dot}(a,\ell)=\sum_{d<D}a_d\,\ell_d\in\mathbb R$, with $\ell_d$ cast to ℝ. This is the ordinary dot product $a\cdot\ell$. For $D=0$ it is $0$ (Lean-checked).

### 2. `box` (def)

**Rendering.** `box D n` $=\{0,\dots,n-1\}^D$, as a `Finset (Fin D → ℕ)` (`Fintype.piFinset` of the constant family `range n`). It has cardinality $n^D$. For $D\ge1$, `box D 0` $=\varnothing$. For $D=0$ it is the singleton $\{()\}$ for **every** $n$, including $n=0$ (`piFinset_of_isEmpty`; Lean-checked `(box 0 n).card = 1`).

### 3. `crit` (def)

**Rendering.** $\mathrm{crit}\,\delta=\#\{d<D:\delta_d=0\}\in\mathbb N$, using exact real equality with classical decidability. In the lattice theorems this is the number of "critical" directions: those with no geometric decay. Lean check: `crit ![0,1,0] = 2`. Note that the count is discontinuous in $\delta$: a tiny positive $\delta_d$ is non-critical, and the constants blow up like $1/(1-2^{-\delta_d})$. That is inherent to the mathematics, not a defect.

### 4. `card_filter_slab_le` (lemma)

**Rendering.** For every $\theta_0>0$, $y\in\mathbb R$ and $n\in\mathbb N$:
$$\#\{k\in\{0,\dots,n-1\}: y\le\theta_0k\le y+1\}\ \le\ 1/\theta_0+1\quad(\text{in }\mathbb R).$$
The bound is uniform in $y$ and $n$.

**Assessment.**
- **Truth: true.** Such $k$ are integers in the closed interval $[y/\theta_0,(y+1)/\theta_0]$ of length $1/\theta_0$. An interval of length $h$ contains at most $\lfloor h\rfloor+1\le h+1$ integers.
- **Tightness:** the bound is attained, e.g. $\theta_0=1/4$, $y=0$, $n\ge5$ gives count $5=1/\theta_0+1$.
- **Numerics:** `check_card_filter.py` ran 19,428 exact rational cases, including the boundary cases $y=\theta_0m$ and $y=\theta_0m-1$. There were 0 violations and the minimum slack is 0.
- **Vacuity:** no. The instance above is non-trivial.
- **Junk:** none. $\theta_0>0$, so $1/\theta_0$ is a genuine value.
- **Hypotheses:** `hθ` is needed. With $\theta_0=0$ and $y\in[-1,0]$, every $k$ qualifies, so the count is $n$, while the RHS would be $0^{-1}+1=1$.
- **Standard fact:** the number of lattice points in an interval of length $h$ is at most $h+1$. This is the 1-D building block of slab counting.

### 5. `card_filter_mul_le` (lemma)

**Rendering.** For every $\theta_0>0$, $z\in\mathbb R$ and $n$:
$$\#\{k<n:\theta_0k\le z\}\le\max(z,0)/\theta_0+1.$$

**Assessment.**
- **Truth: true.** If $z<0$, no $k\ge0$ qualifies, and $0\le1$. Otherwise $k\in\{0,\dots,\lfloor z/\theta_0\rfloor\}$, so the count is at most $\lfloor z/\theta_0\rfloor+1\le z/\theta_0+1$.
- **Tightness:** $\theta_0=1/4$, $z=1$ gives $5=5$.
- **The `max` is necessary.** Without it the statement is false for $z<-\theta_0$, where the RHS would be negative.
- **Numerics:** 19,428 exact cases, 0 violations.
- **Vacuity / junk:** none.
- **Standard fact:** counting the lattice points of $\mathbb N$ below a threshold.

### 6. `one_add_rpow_le_exp` (lemma)

**Rendering.** For real $p\ge0$ and $\kappa>0$, there exists $K>0$, depending only on $p$ and $\kappa$, such that for all real $x\ge0$:
$$(1+x)^p\le K\,e^{\kappa x}.$$
Here `^` is `Real.rpow` (Lean-checked), and the base $1+x\ge1>0$.

**Assessment.**
- **Truth: true.** $\sup_{x\ge0}(1+x)^pe^{-\kappa x}$ equals $(p/\kappa)^pe^{\kappa-p}$ if $p\ge\kappa$, attained at $1+x=p/\kappa$, and $1$ otherwise. So $K=\max(1,(p/\kappa)^pe^{\kappa-p})$ works.
- **Numerics:** `check_elementary.py` uses mpmath at 50 digits on a log grid over $[0,10^6]$, for 28 pairs $(p,\kappa)$. The grid maximum never exceeds the closed form.
- **Vacuity / junk:** none.
- **Hypotheses:** `hp` is **not needed**: for $p<0$, $(1+x)^p\le1\le e^{\kappa x}$, so $K=1$ works (probed numerically). `hκ` is needed, since for $\kappa=0$ and $p>0$ the left side is unbounded.
- **Standard fact:** polynomial growth is dominated by any exponential, $(1+x)^p=O(e^{\kappa x})$.

### 7. `neg_log_rpow_mul_rpow_le` (lemma)

**Rendering.** For real $p\ge0$ and $\kappa>0$, there exists $K>0$, depending on $p$ and $\kappa$, such that for all $\varepsilon\in(0,1)$:
$$(-\log\varepsilon)^p\,\varepsilon^\kappa\le K.$$
Both powers are rpow. The base $-\log\varepsilon>0$ and $\varepsilon>0$ on this domain.

**Assessment.**
- **Truth: true.** Put $t=-\log\varepsilon>0$. Then the expression is $t^pe^{-\kappa t}$, which is at most $(p/(\kappa e))^p$ for $p>0$ and less than $1$ for $p=0$. So $K=\max(1,(p/(\kappa e))^p)$ works.
- **Numerics:** mpmath at 50 digits, including $\varepsilon=10^{-300}$. The grid maximum stays at or below the closed form.
- **Vacuity:** no.
- **Junk:** none. The domain $\varepsilon<1$ excludes $-\log\varepsilon\le0$, where rpow of a non-positive base would be junk. $\varepsilon>0$ excludes $\log 0=0$.
- **Hypotheses:** `hp` is needed. For $p<0$ the expression blows up as $\varepsilon\to1^-$ (probed: about $10^6$ at $\varepsilon=1-10^{-6}$). `hκ` is needed too.
- **Standard fact:** $|\log\varepsilon|^p=O(\varepsilon^{-\kappa})$, used to absorb logarithmic factors into an arbitrarily small power of $\varepsilon$ in complexity bounds.

### 8. `slab_bound` (theorem)

**Rendering.** For every $D$ and all $\theta,\delta\in\mathbb R^D$ with $\theta_d>0$ and $\delta_d\ge0$ for all $d$, there exists $K\ge0$, depending only on $D,\theta,\delta$, such that for all $n\in\mathbb N$ and $x\in\mathbb R$:
1. if $\mathrm{crit}\,\delta=0$ (all $\delta_d>0$), then $\displaystyle\sum_{\ell\in\{0..n-1\}^D}2^{-\delta\cdot\ell}\le K$;
2. $\displaystyle\sum_{\ell\in\{0..n-1\}^D,\ x\le\theta\cdot\ell\le x+1}2^{-\delta\cdot\ell}\ \le\ K\,(1+\max(x,0))^{m}$, with $m=\mathrm{crit}\,\delta\mathbin{\dot-}1$ in ℕ.

Lean details:
- $2^{(\cdot)}$ is rpow with base $2$.
- $(1+\max(x,0))^{m}$ is `Monoid.npow`.
- The slab is closed at both ends.
- $x$ is unrestricted.
- The theorem binds its own `∀ {D}`, which shadows the section variable. This is cosmetic.

**Assessment.**
- **Truth: true.** Proof sketch:
  - Let $Z=\{d:\delta_d=0\}$ with $|Z|=z$, and let $P$ be the complement.
  - *Count in the critical coordinates:* for $z\ge1$, $N_Z(y):=\#\{\ell_Z\in\mathbb N^Z:y\le\theta_Z\cdot\ell_Z\le y+1\}\le\prod_{d\in Z}(1+1/\theta_d)\,(1+\max(y,0))^{z-1}$.
  - Base case $z=1$: `card_filter_slab_le`.
  - Induction step: condition on one coordinate $k$ with $\theta k\le y+1$. By `card_filter_mul_le` there are at most $\max(y+1,0)/\theta+1\le(1+1/\theta)(1+\max(y,0))$ such $k$, and the remaining slab sits at $y-\theta k\le y$.
  - *Sum over $\ell_P$:* this contributes at most $\prod_{d\in P}(1-2^{-\delta_d})^{-1}$.
  - *Case $z=0$:* both conjuncts follow from the full geometric series.
  - Hence $K_{\rm slab}=\prod_{\delta_d=0}(1+1/\theta_d)\prod_{\delta_d>0}(1-2^{-\delta_d})^{-1}$ works for both conjuncts.
- **Numerics.**
  - `check_lattice.py` covers 25 configurations with $D=1,2,3$ and crit $0..3$. The full-lattice slab sums equal the supremum over $n$ and are evaluated exactly (rational $\theta\cdot\ell$) at **all** breakpoints $x\in\{t_i,t_i-1\}$, which is where the supremum is attained. This goes up to $x=400/200/60$ for $D=1/2/3$.
  - Every supremum is at or below $K_{\rm slab}$, and the explicit $K$ is attained for $D=1$, $\theta=1$, $\delta=0$.
  - Growing $D=3$ cases converge to the analytic limit in `check_lattice_extended.out`: for $\theta=(1,1,1)$, $\delta=(0,0,\tfrac25)$ the ratio is $8.116$ at $x=150$, against a limit of $2/(1-2^{-2/5})\approx8.26$.
  - `check_literal_small.py` evaluates the statement literally over `box D n` for $n\le8$ and $D=0..3$: 0 violations. The first conjunct is also checked for $n$ up to $10^6$ in closed form.
- **Vacuity:** no. With $D=2$, $\theta=(1,1)$, $\delta=0$, the slab at integer $x$ has $2x+3$ points, against the bound $K(1+x)$; the best constant is $K=3$.
- **Junk:** none that matters.
  - At $z=0$ the ℕ-truncated exponent is $0$, so conjunct 2 reads "$\le K$". That is true and implied by conjunct 1.
  - The natural exponent $-1$ also holds: when all $\delta_d>0$, $\delta\cdot\ell\ge\mu\,\theta\cdot\ell$ with $\mu=\min_d\delta_d/\theta_d$, so the slab sum decays like $2^{-\mu x/2}$. The numerical natural-exponent ratios are bounded.
  - $D=0$: the sum is $1$ (or $[x\le0\le x+1]$), which is at most $K$ for any $K\ge1$.
- **Hypotheses:** all are needed.
  - $\theta_d=0$ with $\delta_d=0$: the slab sum is $2n$ at $x=0$, so no $K$ is uniform in $n$.
  - $\delta_d<0$: exponential blow-up.
  - Conjunct 1 needs $z=0$: otherwise the box sum grows like $n^z$.
  - Lowering the exponent by one makes the ratio diverge linearly.
- **Standard fact:** this is the weighted lattice-point count in unit slabs of an anisotropic simplex. It is $O(x^{z-1})$ when $z$ directions carry no decay, and $O(1)$ in total when $z=0$. It is the basic building block of the total-degree (TD) index-set sums in the MIMC complexity analysis (Haji-Ali, Nobile & Tempone 2016, appendix summation lemmas; I recall the source but cannot check lemma numbers blind).

### 9. `tail_bound` (theorem)

**Rendering.** For implicit $D$, $\theta,\delta\in\mathbb R^D$ with $\theta>0$ and $\delta\ge0$, and real $a>0$: there exists $K\ge0$, depending on $D,\theta,\delta,a$, such that for all $n\in\mathbb N$ and all real $L\ge0$:
$$\sum_{\ell\in\{0..n-1\}^D,\ \theta\cdot\ell>L}2^{-a\,\theta\cdot\ell-\delta\cdot\ell}\ \le\ K\,(1+L)^{m}\,2^{-aL}.$$
The exponent parses as $(-(a\,\theta\cdot\ell))-\delta\cdot\ell$ (Lean-checked). The inequality in the filter is strict.

**Assessment.**
- **Truth: true.**
  - Cut $\{\theta\cdot\ell>L\}$ into the slabs $(L+j,L+j+1]$ for $j\ge0$.
  - On slab $j$ the weight satisfies $2^{-a\theta\cdot\ell}\le2^{-a(L+j)}$, and the slab sum is at most $K_{\rm slab}(1+L+j)^m\le K_{\rm slab}(1+L)^m(1+j)^m$.
  - Summing gives $K_{\rm tail}=K_{\rm slab}\sum_j2^{-aj}(1+j)^m<\infty$, which is finite because $a>0$.
- **Numerics:** 75 cases (25 configurations × $a\in\{\tfrac12,1,2\}$).
  - The part of the infinite tail beyond the enumeration is computed exactly by a recursion, validated against brute force.
  - All breakpoint endpoints are checked, which suffices because the denominator is log-concave.
  - All suprema are at or below $K_{\rm tail}$, and they stabilise or converge to analytic limits (e.g. $1/((1-2^{-a})(1-2^{-2/5}))$).
  - Literal finite-$n$ checks: 0 violations.
- **Vacuity:** no. With $D=2$, $\theta=(1,1)$, $\delta=0$, $a=1$, the left side is about $(L+3)2^{-L}$, against the bound $K(1+L)2^{-L}$.
- **Junk:** none. At $z=0$ the RHS is $K2^{-aL}$; the natural $(1+L)^{-1}2^{-aL}$ version also holds (checked numerically).
- **Hypotheses:** all are needed in general.
  - $a=0$ with $z\ge1$: the tail over `box` grows like $n$.
  - $0\le L$ is needed when $z\ge2$: at $L=-1$ the RHS is $K\cdot0^{m}\cdot2^{a}=0$, while the LHS is positive.
- **Standard fact:** the tail, or bias, estimate outside a TD index set. For weights $w=a\theta+\delta$ with $\delta\ge0$, $\sum_{\ell\notin I(L)}2^{-w\cdot\ell}\lesssim L^{z-1}2^{-aL}$, where $a=\min_dw_d/\theta_d$ and $z$ counts the directions attaining the minimum. This is the MIMC bias bound.

### 10. `inner_bound` (theorem)

**Rendering.** For $\theta>0$, $\delta\ge0$ and real $c\ge0$: there exists $K\ge0$, depending on $D,\theta,\delta,c$, such that for all $n$ and all $L\ge0$:
$$\sum_{\ell\in\{0..n-1\}^D,\ \theta\cdot\ell\le L}2^{c\,\theta\cdot\ell-\delta\cdot\ell}\ \le\ K\,(1+L)^{m}\sum_{j=0}^{\lfloor L\rfloor}2^{c(L-j)}.$$
Here $j$ is cast to ℝ, and $\lfloor L\rfloor_+=\lfloor L\rfloor$ because $L\ge0$. The range-sum is the last multiplicative factor (Lean-checked by `rfl`).

**Assessment.**
- **Truth: true.**
  - Cover $[0,L]$ by the slabs $[L-j-1,L-j]$ for $j=0..\lfloor L\rfloor$.
  - On slab $j$, $2^{c\theta\cdot\ell}\le2^{c(L-j)}$ since $c\ge0$, and the slab sum is at most $K_{\rm slab}(1+L)^m$. So $K_{\rm inner}=K_{\rm slab}$.
  - The RHS behaves like $L^{z-1}2^{cL}$ for $c>0$ and like $L^{z}$ for $c=0$, which are the standard rates.
- **Numerics:** 100 cases (25 configurations × $c\in\{0,\tfrac12,1,3\}$).
  - All suprema are at or below $K_{\rm slab}$.
  - Slowly growing $D=3$ cases converge: for $\theta=(1,1,1)$, $\delta=(0,\tfrac3{10},\tfrac9{10})$, $c=0$, the ratio is $11.06$ at $L=150$, against a limit of $1/((1-2^{-0.3})(1-2^{-0.9}))\approx11.48$.
  - Literal checks: 0 violations.
- **Vacuity:** no.
- **Junk:** none. The $z=0$ truncation behaves as before, and the natural-exponent version is bounded too.
- **Hypotheses:**
  - `hc : 0 ≤ c` is **stronger than needed**. For $c<0$ the LHS is at most $\prod_d(1-2^{-(|c|\theta_d+\delta_d)})^{-1}$, and the RHS is at least $K2^{c}$ (from the term $j=\lfloor L\rfloor$). So the statement holds for every real $c$; this is confirmed numerically for $c=-\tfrac1{10},-\tfrac12,-1,-3$. It is harmless.
  - $0\le L$ is needed. For $L<-1$ with $m$ odd, the RHS is negative while the LHS is $0$.
- **Standard fact:** the work or variance sum over a TD set. For $v=c\theta-\delta$, $\sum_{\ell\in I(L)}2^{v\cdot\ell}\lesssim L^{z-1}2^{cL}$ when $c>0$, and $\lesssim L^{z}$ when $c=0$, where $c=\max_dv_d/\theta_d$ and $z$ counts the directions attaining the maximum. These are the MIMC cost-sum lemmas.

### 11. `sum_box_two_rpow_le_prod` (lemma)

**Rendering.** For $g\in\mathbb R^D$ with all $g_d<0$, and any $n$:
$$\sum_{\ell\in\{0..n-1\}^D}2^{g\cdot\ell}\le\prod_d(1-2^{g_d})^{-1}.$$

**Assessment.**
- **Truth: true.** The LHS equals $\prod_d\sum_{k<n}(2^{g_d})^k=\prod_d\frac{1-2^{g_dn}}{1-2^{g_d}}$. This is at most the RHS, and tends to it as $n\to\infty$. For $D=0$ both sides equal $1$.
- **Numerics:** `check_sum_box.py` ran 140 literal enumerations and cross-checked them against the closed form: 0 violations. The largest ratio LHS/RHS is 1. Equality is exact at $D=0$; for very negative $g$ and large $n$ the ratio is 1 only up to floating-point rounding.
- **Vacuity:** no. For example, $g=(-1,-1)$, $n=12$ gives $3.998\le4$.
- **Junk:** none. `hg` puts $1-2^{g_d}$ in $(0,1)$. Without it, $g_d=0$ gives the Lean value $(1-2^0)^{-1}=0^{-1}=0$ (Lean-checked), and the statement becomes false. So the hypothesis is necessary and blocks the junk case.
- **Standard fact:** the multi-dimensional geometric series.

### 12. `indexSet` (def)

**Rendering.**
$$\mathrm{indexSet}(\theta,L)=\{\ell\in\textstyle\prod_d\{0,\dots,\lfloor L/\theta_d\rfloor_+\}:\ \theta\cdot\ell\le L\}.$$
When all $\theta_d>0$, this equals the anisotropic total-degree set $\{\ell\in\mathbb N^D:\theta\cdot\ell\le L\}$; the bounding box only makes the set finite.
- `check_indexset.py` confirmed this in 512 exact cases, with $D=0..3$, including $L<0$ and $L$ on lattice boundaries.
- For $L<0$ it is $\varnothing$ when $D\ge1$.
- For $D=0$ it is $\{()\}$ iff $L\ge0$.
- **Junk:** if $\theta_d=0$, then $L/0=0$; if $\theta_d<0$ and $L\ge0$, then $\lfloor L/\theta_d\rfloor_+=0$. Either way the coordinate is **frozen at $\ell_d=0$**, whereas the true set $\{\theta\cdot\ell\le L\}$ would be infinite or different. Theorems about `indexSet` need $\theta>0$.
- This is the MIMC TD index set $I(L)$.

### 13. `boxSize` (def)

**Rendering.** $\mathrm{boxSize}(\theta,L)=\sum_d(\lfloor L/\theta_d\rfloor_++1)\in\mathbb N$, the **sum** of the side lengths of `indexSet`'s bounding box.
- It is **not** the box cardinality: for $\theta=(1,1)$, $L=3$, boxSize is $8$ while $\prod$ sides $=16$ and $|\mathrm{indexSet}|=10$.
- Because it is at least every side length, `indexSet θ L` ⊆ `box D (boxSize θ L)`, and filtering `box D n` by $\theta\cdot\ell\le L$ gives back `indexSet θ L` for any $n\ge$ max side, including $n=$ boxSize (checked).
- For $D=0$ it is $0$, and `box 0 0` $=\{()\}$ still contains the only index.
- Junk only when $\theta_d\le0$, as for `indexSet`. The name could suggest a cardinality or a cost, so check how it is used downstream.

---

## Scripts (all in `work_L4/`, each output in the `.out` file of the same name)

| script | purpose | result |
|---|---|---|
| `elab_check.lean` | Lean 4.33.1 elaboration of `^`/`-`/casts and parsing; edge cases ($D=0$, crit, $0-1$, $x/0$, $\lfloor\cdot\rfloor_+$, $0^{-1}$) | compiles, exit 0 |
| `check_card_filter.py` | exact check of lemmas 4–5 | 2×19,428 cases, 0 violations, bounds attained |
| `check_elementary.py` | lemmas 6–7 vs closed-form suprema; hypothesis probes | all OK; `hp` not needed in 6, needed in 7 |
| `check_sum_box.py` | lemma 11 by enumeration | 140 cases, 0 violations |
| `lattice_common.py` | shared helper (exact enumeration, exact infinite-tail recursion) | imported, not run |
| `check_lattice.py` | theorems 8–10 over 25 configurations, running suprema, explicit $K$, natural exponent | all within explicit $K$ |
| `check_lattice_extended.py` | slowly converging $D=3$ cases up to $L=150$, compared with analytic limits | converging below $K$ |
| `check_literal_small.py` | literal finite-$n$ evaluation of 8–10, $D=0..3$ | 2,160 checks, 0 violations |
| `check_negative_controls.py` | lowered exponent; dropped hypotheses; $c<0$ | behaves as described above |
| `check_indexset.py` | defs 12–13 against an independent enumeration; junk edge cases | all as described |
