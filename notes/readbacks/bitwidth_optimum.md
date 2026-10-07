# Blind read-back report: R11 (bit-width optimisation)

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round16/packet_R11_bitwidth.lean` |
| declarations audited | 17 (13 theorems, 2 module definitions `bitLevelCost` and `lambdaBitWidth`, 2 appended definitions `sepCost` and `vIndepR`) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round16/work_R11/` (`common.py`, `noncvx.py`, `deriv_check.py`, `instance_check.py`, `kkt_check.py`, `convexity_check.py`, `squared_variant.py`, each with its `.out`; `Check.lean` with its `.out`) |

**Elaboration check (`work_R11/Check.lean`).** The file imports `MlmcLean` and checks three things:
- All four definitions agree with the packet text by `rfl`.
- Each of the 13 packet statements, re-stated verbatim, is closed by the corresponding compiled
  `MLMC.*` theorem applied to its explicit arguments. So the packet matches the compiled
  statements.
- `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for all 13.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| D1 | `sepCost` (appended) | def | n/a | n/a | no junk (polynomial) |
| D2 | `vIndepR` (appended) | def | n/a | n/a | no junk ($4^x$ with base $4>0$) |
| D3 | `bitLevelCost` | def | n/a | n/a | uses `Real.sqrt`, which is $0$ on negatives: relevant only when $V\tilde C<0$ or $V^\Delta C<0$ |
| D4 | `lambdaBitWidth` | def | n/a | n/a | `Classical.epsilon`: unspecified value when no root exists |
| 1 | `exists_isMinOn_bitLevelCost_of_nonneg` | theorem | true | no | no |
| 2 | `exists_isMinOn_bitLevelCost` | theorem | true | no | no |
| 3 | `exists_best_uniform_bitLevelCost` | theorem | true | no | no (last conjunct is trivial) |
| 4 | `eq36_eq35_of_isLocalMin` | theorem | true | no | no |
| 5 | `lagrange_of_isMinOn_bitLevelCost` | theorem | true | no | no |
| 6 | `isMinOn_lambda_bitLevelCost` | theorem | true | no | no (third conjunct follows at once from the second) |
| 7 | `bitLevelCost_lt_uniform` | theorem | true | no | no |
| 8 | `kkt_of_isMinOn_box` | theorem | true | no | no |
| 9 | `convexOn_sqrt_vIndepR` | theorem | true | no | no |
| 10 | `convexOn_bitLevelCost` | theorem | true | no | no |
| 11 | `strictConvexOn_bitLevelCost` | theorem | true | no | no |
| 12 | `existsUnique_isMinOn_bitLevelCost` | theorem | true | no | no |
| 13 | `not_convexOn_bitLevelCost` | theorem | true | no (closed statement) | no |

## Main points for a human auditor

1. **All 13 theorems are true and non-vacuous, and none depends on a junk value.** I checked the
   first-order formulas numerically:
   - At 300 random points with $\tilde C>0$ and $V^\Delta>0$, they match finite-difference partial
     derivatives of $F$ to a relative error of about $10^{-39}$.
   - At numerically computed global minimisers in two 2-variable instances (one convex, one
     non-convex), the residuals are about $10^{-16}$.
2. **`bitLevelCost` is not squared.** It is $F=\sqrt{V\tilde C}+\sqrt{V^\Delta C}$, not
   $(\sqrt{V\tilde C}+\sqrt{V^\Delta C})^2$. The results still carry over to the squared cost:
   - Minimisers are the same, and so are stationary points wherever $F>0$.
   - Convexity and strict convexity are preserved, because squaring a non-negative convex
     function keeps it convex.
   - The non-convexity example also holds for $F^2$, but only near $0$ (for example on
     $[0,0.02]$). At the points $0,1,2$ the midpoint inequality holds for $F^2$
     (`squared_variant.out`).
3. **The existence theorems allow some junk values on $S$, but are true regardless.**
   `exists_isMinOn_bitLevelCost_of_nonneg` and `exists_best_uniform_bitLevelCost` put no sign
   condition on $E$ or $C$. `exists_isMinOn_bitLevelCost` puts none on $M'$ and does not restrict
   $S$ to $d\ge0$. So $S$ may contain points where a square root is clipped to $0$. The statements
   remain true, but for the physical reading one wants $E\ge0$, $C\ge0$ and $\tilde C\ge0$ on $S$.
4. **The "minimisation over $\lambda$" conjunct is trivial.** In `isMinOn_lambda_bitLevelCost`,
   it is an immediate consequence of `lambdaBitWidth λ* = d*` together with `hmin`.
   `Classical.epsilon` does no harm here: under the hypotheses, every $\lambda>0$ gives a genuine
   unique root in every coordinate.
5. **`bitLevelCost_lt_uniform` compares $d^\star$ with any uniform width $w$, not only the best
   one.** The condition is that $w$ is an interior point of $S$ with $\tilde C(w)>0$. When
   $M'\ne0$, the non-proportionality condition depends on $w$. As is Mathlib's convention for
   `IsMinOn`, $d^\star\in S$ is not assumed, and the theorem stays true without it.
6. **The "box" in `kkt_of_isMinOn_box` has lower bounds only**:
   $\{d: b_i\le d_i\ \forall i\in s\}$, with no upper bounds.
7. **The pure-calculus theorems carry no sign hypotheses.** `eq36_eq35_of_isLocalMin` and
   `kkt_of_isMinOn_box` need no conditions on $E$, $M$ or $M'$, only $\tilde C(d^\star)>0$ and
   $V^\Delta(d^\star)>0$, which makes them more general than usual. In the other theorems, the
   sign hypotheses that appear are the natural ones and are needed:
   - $M\ge0$ for the convexity of the Lagrangian;
   - `Fintype` for strict convexity;
   - $M>0$ for existence on unbounded convex $S$.

Notation used below. $\iota$ is an arbitrary type; $s$ is a `Finset ι`; $E,M,M':\iota\to\mathbb R$;
$e:\iota\to\mathbb Z$ (cast to $\mathbb R$); $d\in\mathbb R^\iota$ with the product topology. Also:
- $\tilde C_s(d)=$ `sepCost s M M' d`;
- $V^\Delta_s(d)=$ `vIndepR s E e d`;
- $F_s(d)=$ `bitLevelCost s E e M M' V C d`;
- $A_i(d)=M_id_i+M'_i$ (this is $\partial_i\tilde C$);
- $B_i(d)=-\ln 4\,E_i4^{e_i-d_i}/12$ (this is $\partial_iV^\Delta$);
- $g_i(t;\lambda)=-\ln4\,E_i4^{e_i-t}/12+\lambda(M_it+M'_i)$;
- $\lambda^\star(d)=\sqrt{V\,V^\Delta(d)/(C\,\tilde C(d))}$.

`IsMinOn f S a` means $\forall x\in S,\ f(a)\le f(x)$, without $a\in S$
(`Mathlib/Order/Filter/Extr.lean`). `IsLocalMin f a` means $f(a)\le f(x)$ on a neighbourhood
of $a$.

---

## D1 `sepCost` (appended, from `MlmcLean.BitWidth`)

**Rendering.** $\tilde C_s(d)=\tfrac12\sum_{i\in s}M_id_i^2+\sum_{i\in s}M'_id_i$, which is the
relaxed hardware cost.

**Assessment.** A polynomial, with no junk. It is $\ge0$ when $M,M'\ge0$ and $d\ge0$, or when
$M'=0$ and $M\ge0$. Otherwise it can be negative.

## D2 `vIndepR` (appended, from `MlmcLean.BitWidth`)

**Rendering.** $V^\Delta_s(d)=\tfrac1{12}\sum_{i\in s}E_i\,4^{e_i-d_i}$, with a real power of the
positive base $4$, that is $e^{(e_i-d_i)\ln4}$.

**Assessment.** No junk, because the base is positive. This is the variance of a uniform rounding
error with step $2^{e_i-d_i}$, which is $(2^{e_i-d_i})^2/12$, weighted by $E_i$. It is $\ge0$
when $E\ge0$.

## D3 `bitLevelCost`

**Rendering.**
$F_s(d)=\sqrt{V\,\tilde C_s(d)}+\sqrt{V^\Delta_s(d)\,C}$, where `Real.sqrt` is $0$ on negative
arguments.

**Assessment.** This is the square root of the usual MLMC level cost
$(\sqrt{V\tilde C}+\sqrt{V^\Delta C})^2$. It has the same minimisers. The clipping matters only
where $V\tilde C<0$ or $V^\Delta C<0$.

## D4 `lambdaBitWidth`

**Rendering.** $\mathrm{lambdaBitWidth}(\lambda)_i=\varepsilon t.\ g_i(t;\lambda)=0$, using
Hilbert choice. This is some root if one exists, and an unspecified real otherwise.

**Assessment.** Suppose $\lambda>0$, $E_i>0$ and $M_i\ge0$. Then $t\mapsto g_i(t;\lambda)$ is
continuous and strictly increasing, and tends to $-\infty$ as $t\to-\infty$. As $t\to+\infty$ it
tends to $+\infty$ if $M_i>0$, and to $\lambda M'_i$ if $M_i=0$. So a unique root exists if and
only if $M_i>0$ or $M'_i>0$. Outside this regime the value is junk. Theorem 6 shows that no junk
is reached under its hypotheses.

---

## 1 `exists_isMinOn_bitLevelCost_of_nonneg`

**Rendering.** Assume:
- `[Fintype ι]`;
- $E,e,C$ arbitrary;
- $V>0$;
- $M_i\ge0$, $M'_i\ge0$ and $M_i+M'_i>0$ for all $i$;
- $S\subseteq\mathbb R^\iota$ closed, $S\subseteq[0,\infty)^\iota$, $S\neq\emptyset$.

Then there is $d^\star\in S$ with $F_{\rm univ}(d^\star)\le F_{\rm univ}(d)$ for all $d\in S$.

**Assessment.**
- **Truth: true.** $F$ is continuous, because `sqrt` is continuous everywhere and $x\mapsto4^x$ is
  continuous. Also $F\ge\sqrt{V\tilde C}\ge0$. On the orthant,
  $M_id_i^2/2+M'_id_i\ge0$, and it tends to $\infty$ as $d_i\to\infty$: it is
  $\ge M_id_i^2/2$ if $M_i>0$, and $\ge M'_id_i$ if $M'_i>0$. Hence, for any $d_0\in S$, the set
  $\{d\in S:F(d)\le F(d_0)\}$ is closed and bounded, so compact, and Weierstrass gives a minimiser.
- **Non-vacuous:** $\iota=$ `Unit`, $E=12$, $e=0$, $M=1$, $M'=0$, $V=C=1$,
  $S=[0,\infty)$.
- **Junk:** none needed. If $E$ or $C$ is negative, the second root may be clipped to $0$, but
  coercivity and continuity do not depend on that.
- **Hypotheses:** `hMM` and the orthant restriction are what make $F$ coercive. Without them, a
  coordinate with $M_i=M'_i=0$ gives an $F$ that is non-increasing in $d_i$.
- **Standard fact:** the extreme value theorem for a continuous, coercive function on a closed set.

## 2 `exists_isMinOn_bitLevelCost`

**Rendering.** Assume `[Fintype ι]`; $E,e,M',C$ arbitrary; $V>0$; $M_i>0$ for all $i$; and
$S$ closed and non-empty, with no sign restriction. Then there is $d^\star\in S$ with
$F_{\rm univ}(d^\star)\le F_{\rm univ}(d)$ for all $d\in S$.

**Assessment.**
- **Truth: true.** We have $\tilde C(d)\ge\sum_i(\tfrac{M_i}2d_i^2-|M'_i||d_i|)\to\infty$ as
  $\|d\|\to\infty$, so $F$ is continuous and coercive on $\mathbb R^\iota$. Weierstrass then gives
  a minimiser.
- **Non-vacuous:** the instance from theorem 1 with $S=\mathbb R$.
- **Junk:** the truth does not depend on any. Note, however, that $S$ may include points where
  $\tilde C<0$, for example $d_i\in(-2M'_i/M_i,0)$, or where $V^\Delta C<0$. There $F$ takes the
  clipped value, and the minimiser it produces may sit in such a region. For instance, a singleton
  $S$ in that region gives a trivial minimiser.
- **Standard fact:** the same extreme value argument as theorem 1.

## 3 `exists_best_uniform_bitLevelCost`

**Rendering.** Assume the hypotheses of theorem 1, but with "some constant vector $(w_1,\dots,w_1)\in S$"
in place of $S\neq\emptyset$. Then there is $w_0\in\mathbb R$ such that:
- $(w_0)_i\in S$;
- $F(w_0\mathbf 1)\le F(w\mathbf 1)$ for every $w$ with $w\mathbf1\in S$;
- there is $d^\star\in S$ minimising $F$ on $S$, with $F(d^\star)\le F(w_0\mathbf 1)$.

**Assessment.**
- **Truth: true.** The set $T=\{w: w\mathbf1\in S\}$ is the preimage of the closed set $S$ under a
  continuous map, so it is closed. It is non-empty because it contains $w_1$. If $\iota\ne\emptyset$,
  then $T\subseteq[0,\infty)$, and $w\mapsto F(w\mathbf1)$ is coercive there, so a minimiser
  $w_0$ exists. If $\iota=\emptyset$, $F(w\mathbf1)$ is constant, and $w_0=w_1$ works. The last
  conjunct follows from theorem 1 together with $w_0\mathbf1\in S$.
- **Non-vacuous:** the instance from theorem 1 with $w_1=1$.
- **Junk:** none.
- **Note:** only the second conjunct (the best uniform width exists) has real content. The final
  inequality is a trivial consequence.

## 4 `eq36_eq35_of_isLocalMin`

**Rendering.** Let $\iota$ be any type and $s$ a finite set. Take $E,e,M,M'$ arbitrary, $V>0$
and $C>0$. Suppose $d^\star$ is a local minimiser of $F_s$ on $\mathbb R^\iota$, with
$\tilde C_s(d^\star)>0$ and $V^\Delta_s(d^\star)>0$. Then for every $i\in s$:
- **(a)** $\sqrt{C/V^\Delta(d^\star)}\,B_i(d^\star)+\sqrt{V/\tilde C(d^\star)}\,A_i(d^\star)=0$;
- **(b)** $B_i(d^\star)+\lambda^\star(d^\star)\,A_i(d^\star)=0$.

**Assessment.**
- **Truth: true.** Near $d^\star$, both radicands are positive, so $F$ is differentiable there,
  with
  $2\partial_iF=\sqrt{V/\tilde C}\,A_i+\sqrt{C/V^\Delta}\,B_i
  =\sqrt{C/V^\Delta}\,(B_i+\lambda^\star A_i)$.
  The map $t\mapsto F(\mathrm{update}\,d^\star\,i\,t)$ has a local minimum at $d^\star_i$, so
  $\partial_iF=0$, which gives (a). Dividing by $\sqrt{C/V^\Delta}>0$ gives (b). The argument
  works for infinite $\iota$ too, since $F$ depends only on the coordinates in $s$.
- **Numerical check:** `deriv_check.out` confirms the derivative identity at 300 random points;
  `instance_check.out` shows residuals of about $10^{-16}$ at computed minimisers.
- **Non-vacuous:** $\iota=$ `Unit`, $E=12$, $e=0$, $M=1$, $M'=0$, $V=1$, $C=4$. Then
  $F(d)=|d|/\sqrt2+2\cdot2^{-d}$, whose global minimum is at
  $d^\star=\log_2(2\sqrt2\ln2)\approx0.97123$, with $\tilde C,V^\Delta>0$.
- **Junk:** none, because the positivity hypotheses keep everything smooth near $d^\star$.
- **Hypotheses:** no sign hypotheses on $E$, $M$ or $M'$, which is more general than usual.
- **Standard fact:** Fermat's rule (zero gradient at an interior extremum), giving the Lagrange
  condition $\nabla V^\Delta+\lambda\nabla\tilde C=0$ with
  $\lambda=\sqrt{VV^\Delta/(C\tilde C)}$.

## 5 `lagrange_of_isMinOn_bitLevelCost`

**Rendering.** Let $s$ be finite. Assume $V,C>0$; $E_i>0$ and $M_i\ge0$ for $i\in s$; $e,M'$
arbitrary. Let $S$ be a neighbourhood of $d^\star$, with $d^\star$ minimising $F_s$ on $S$ and
$\tilde C_s(d^\star)>0$. Write $\lambda=\lambda^\star(d^\star)$. Then:
- **(1)** $\lambda>0$;
- **(2)** $B_i(d^\star)+\lambda A_i(d^\star)=0$ for all $i\in s$;
- **(3)** for every $d\in\mathbb R^\iota$,
  $V^\Delta(d^\star)+\lambda\tilde C(d^\star)\le V^\Delta(d)+\lambda\tilde C(d)$;
- **(4)** every $d$ with $g_i(d_i;\lambda)=0$ for all $i\in s$ satisfies $d_i=d^\star_i$ for all
  $i\in s$.

**Assessment.**
- **Truth: true.**
  - (1): $\tilde C(d^\star)>0$ forces $s\ne\emptyset$, so $V^\Delta(d^\star)>0$ and hence
    $\lambda>0$.
  - (2): $S\in\mathcal N(d^\star)$ makes $d^\star$ a local minimiser, so theorem 4 applies.
  - (3): The Lagrangian
    $V^\Delta+\lambda\tilde C=\sum_{i\in s}h_i(d_i)$ is a sum of one-variable functions with
    $h_i''=(\ln4)^2E_i4^{e_i-t}/12+\lambda M_i\ge0$. So it is separable and convex, its gradient
    vanishes at $d^\star$ by (2), and $d^\star$ is a global minimiser.
  - (4): Each $g_i(\cdot;\lambda)=h_i'$ is strictly increasing, so its root is unique.
- **Numerical check:** both instances in `instance_check.out` give
  $\min L(d)-L(d^\star)\ge0$ over 6000 random $d$.
- **Non-vacuous:** $\iota=$ `Fin 2`, $E=(12,12)$, $e=(0,1)$, $M=(1,1)$, $M'=0$, $V=1$, $C=16$,
  $S=\mathbb R^2$. Then $d^\star\approx(2.110,2.884)$.
- **Junk:** none. Every radicand is positive, and (3) contains no square root.
- **Hypotheses:** $M\ge0$ is needed for (3) and (4).
- **Standard fact:** the Lagrangian / multiplier characterisation of a constrained optimum; a
  stationary point of a convex separable function is its global minimiser.

## 6 `isMinOn_lambda_bitLevelCost`

**Rendering.** Assume `[Fintype ι]`, $s=$ `univ`; $E_i>0$ and $M_i\ge0$ for all $i$; $M'$
arbitrary; $V,C>0$; $S\in\mathcal N(d^\star)$; $d^\star$ minimises $F$ on $S$; and
$\tilde C(d^\star)>0$. Write $\lambda^\star=\lambda^\star(d^\star)$. Then:
- **(1)** $\lambda^\star>0$;
- **(2)** $\mathrm{lambdaBitWidth}(\lambda^\star)=d^\star$, as functions on $\iota$;
- **(3)** $\lambda^\star$ minimises $\lambda\mapsto F(\mathrm{lambdaBitWidth}(\lambda))$ over
  $\{\lambda>0:\mathrm{lambdaBitWidth}(\lambda)\in S\}$.

**Assessment.**
- **Truth: true.**
  - (1) is theorem 5 (1).
  - (2): by theorem 5 (2) and (4), $d^\star_i$ is the unique root of $g_i(\cdot;\lambda^\star)$,
    so $\varepsilon$ returns it. This is confirmed numerically: the difference is about
    $10^{-16}$ (`instance_check.out`).
  - (3): for any $\lambda$ in the set, $\mathrm{lambdaBitWidth}(\lambda)\in S$, so
    $F(d^\star)\le F(\mathrm{lambdaBitWidth}(\lambda))$. By (2),
    $F(d^\star)=F(\mathrm{lambdaBitWidth}(\lambda^\star))$. This is immediate.
- **Non-vacuous:** the instance from theorem 5.
- **Junk:** none. By (2), no $i$ has $M_i=0$ and $M'_i\le0$, because that would make
  $g_i<0$ everywhere. Hence, by D4, $\mathrm{lambdaBitWidth}(\lambda)$ is the genuine unique root
  for every $\lambda>0$, and the epsilon junk is never reached.
- **Note:** (3) is formally a consequence of (2) together with `hmin`. It is the "reduce to a
  one-dimensional search over $\lambda$" principle, with no further analysis of the curve
  $\lambda\mapsto d(\lambda)$.
- **Standard fact:** parametrising the optimum by its Lagrange multiplier.

## 7 `bitLevelCost_lt_uniform`

**Rendering.** Let $s$ be finite. Assume $V,C>0$; $E_k\ge0$ for $k\in s$; $e,M,M'$ arbitrary;
$d^\star$ minimises $F_s$ on $S$; $S\in\mathcal N(w\mathbf1)$ for some $w\in\mathbb R$; and
$\tilde C_s(w\mathbf1)>0$. Suppose there are $i,j\in s$ with
$E_i4^{e_i}(M_jw+M'_j)\ne E_j4^{e_j}(M_iw+M'_i)$. Then $F_s(d^\star)<F_s(w\mathbf1)$.

**Assessment.**
- **Truth: true.** Since $w\mathbf1\in S$, we have $F(d^\star)\le F(w\mathbf1)$. Suppose
  equality holds. Then $w\mathbf1$ minimises $F$ on the neighbourhood $S$, so it is a local
  minimiser. If $E_i=E_j=0$, both sides of `hij` are $0$, so `hij` forces $E_i>0$ or $E_j>0$, and
  hence $V^\Delta(w\mathbf1)>0$. Theorem 4 (b) then gives
  $\kappa a_k=\lambda b_k$ for $k=i,j$, where $a_k=E_k4^{e_k}$, $b_k=M_kw+M'_k$,
  $\kappa=\ln4\,4^{-w}/12>0$ and $\lambda>0$. Hence $a_ib_j=a_jb_i$, contradicting `hij`. The
  argument does not need $d^\star\in S$.
- **Non-vacuous:** the instances in `instance_check.out`, with $S=\mathbb R^2$ and $w=1$ or $3$.
  The gap to the best uniform width on a grid is $0.127$ in the convex instance and $0.115$ in
  the non-convex one.
- **Junk:** none.
- **Note:** the result holds for every interior uniform $w$ with $\tilde C>0$. When $M'\neq0$,
  the non-proportionality condition depends on $w$.
- **Standard fact:** a uniform choice is optimal only if the marginal-cost ratios are equal, so
  under non-proportionality it is strictly suboptimal.

## 8 `kkt_of_isMinOn_box`

**Rendering.** Let $s$ be finite. Take $E,e,M,M'$ arbitrary and $V,C>0$. Suppose $d^\star$
minimises $F_s$ on $\{d:b_i\le d_i\ \forall i\in s\}$, that $b_i\le d^\star_i$ for $i\in s$, and
that $\tilde C(d^\star)>0$ and $V^\Delta(d^\star)>0$. Then for every $i\in s$:
- $g_i(d^\star_i;\lambda^\star)\ge0$;
- if $b_i<d^\star_i$, then $g_i(d^\star_i;\lambda^\star)=0$.

**Assessment.**
- **Truth: true.** We have
  $\partial_iF=\tfrac12\sqrt{C/V^\Delta}\,g_i(d^\star_i;\lambda^\star)$, which has the same sign
  as $g_i$. Increasing $d_i$ keeps $d$ feasible, so the one-sided derivative is $\ge0$. If
  $b_i<d^\star_i$, $d_i$ can move in both directions, so the derivative is $0$.
- **Numerical check:** `kkt_check.out` gives two cases.
  - $\iota=$ `Unit`, $E=12$, $e=0$, $M=M'=1$, $V=C=1$, $b=1$: the bound is active at
    $d^\star=1$, with $g=0.470\ge0$.
  - A two-variable case with $b=(3,0)$: $d^\star\approx(3,3.214)$, $g=(0.038,\ \approx10^{-17})$.
- **Non-vacuous:** yes, by those cases.
- **Junk:** none.
- **Note:** the "box" has lower bounds only. There are no sign hypotheses.
- **Standard fact:** KKT conditions for lower-bound constraints, with dual feasibility and
  complementary slackness.

## 9 `convexOn_sqrt_vIndepR`

**Rendering.** For any $\iota$, any finite $s$, $E_i\ge0$ on $s$ and any $e$, the map
$d\mapsto\sqrt{V^\Delta_s(d)}$ is convex on $\mathbb R^\iota$.

**Assessment.**
- **Truth: true.** Write
  $\sqrt{V^\Delta}=\big\|\big(\sqrt{E_i/12}\,2^{e_i-d_i}\big)_{i\in s}\big\|_2$. This is the
  Euclidean norm, which is convex and monotone on the non-negative orthant, applied to convex
  non-negative coordinates. Alternatively, it is $\exp$ of $\tfrac12$ log-sum-exp.
- **Numerical check:** 4000 random midpoint and weighted tests give a minimum gap of about
  $-10^{-51}$, which is rounding (`convexity_check.out`). A counter-check with $E$ of mixed sign
  fails, as it should.
- **Non-vacuous:** any $E\ge0$.
- **Junk:** none, since $V^\Delta\ge0$.
- **Standard fact:** convexity of a norm composed with convex non-negative maps (or of
  log-sum-exp).

## 10 `convexOn_bitLevelCost`

**Rendering.** Assume $E_i\ge0$, $M_i\ge0$ and $M'_i=0$ for $i\in s$, with $V,C\ge0$. Then
$F_s$ is convex on $\mathbb R^\iota$.

**Assessment.**
- **Truth: true.** The first term is
  $\sqrt{V\tilde C}=\sqrt{V/2}\,\|(\sqrt{M_i}d_i)_{i\in s}\|_2$, a seminorm. The second is
  $\sqrt{V^\Delta C}=\sqrt C\sqrt{V^\Delta}$, convex by theorem 9.
- **Numerical check:** random tests pass, including zero $V$, $C$, $M$ or $E$. With $M'\ne0$
  there are violations, with a relative gap of $-0.14$.
- **Non-vacuous:** yes.
- **Junk:** none, since both radicands are $\ge0$.
- **Standard fact:** a sum of convex functions is convex.

## 11 `strictConvexOn_bitLevelCost`

**Rendering.** Assume `[Fintype ι]`, $s=$ `univ`; $E_i>0$, $M_i\ge0$ and $M'_i=0$ for all $i$;
$V\ge0$; $C>0$. Then $F$ is strictly convex on $\mathbb R^\iota$.

**Assessment.**
- **Truth: true.** Let $x\ne y$, so some coordinate differs. Put
  $u(d)=(\sqrt{E_i/12}\,2^{e_i-d_i})_i$. Then
  $u(\tfrac{x+y}2)\le\tfrac{u(x)+u(y)}2$ coordinatewise, with strict inequality in a coordinate
  where $x$ and $y$ differ, since $\exp$ is strictly convex and $E_i>0$. Because the 2-norm is
  strictly monotone on the orthant,
  $\|u(\tfrac{x+y}2)\|<\|\tfrac{u(x)+u(y)}2\|\le\tfrac{\|u(x)\|+\|u(y)\|}2$. Multiplying by
  $\sqrt C>0$ and adding the convex first term keeps the inequality strict. This includes the
  diagonal direction $\mathbf1$, where $\sqrt{V^\Delta}$ scales by $2^{-t}$.
- **Numerical check:** 4000 tests, including diagonal and single-coordinate differences and
  $M=0$ or $V=0$, give a strictly positive minimum gap. With $C=0$, strictness fails, so the
  hypothesis is needed.
- **Non-vacuous:** yes.
- **Junk:** none.
- **Hypotheses:** `Fintype` is needed. With infinite $\iota$, coordinates outside the support of
  $F$ would break strictness.
- **Standard fact:** strict convexity of the norm of a strictly convex vector map.

## 12 `existsUnique_isMinOn_bitLevelCost`

**Rendering.** Assume `[Fintype ι]`; $E_i>0$, $M_i>0$ and $M'_i=0$ for all $i$; $V,C>0$; $S$
closed, convex and non-empty. Then there is exactly one $d^\star$ with $d^\star\in S$ minimising
$F$ on $S$.

**Assessment.**
- **Truth: true.** Existence follows from theorem 2. For uniqueness, if two minimisers differ,
  their midpoint lies in $S$ and strictly undercuts them by theorem 11.
- **Non-vacuous:** $S=\mathbb R^2$ in the convex instance, with $d^\star\approx(2.110,2.884)$.
- **Junk:** none.
- **Hypotheses:** $M>0$ is needed for existence on an unbounded $S$.
- **Standard fact:** a strictly convex, coercive function has a unique minimiser on a closed
  convex set.

## 13 `not_convexOn_bitLevelCost`

**Rendering.** Take $\iota=$ `Unit`, $s=$ `univ`, $E=12$, $e=0$, $M=M'=1$, $V=C=1$. Then
$F(d)=\sqrt{d^2/2+d}+2^{-d}$, and the claim is that $F$ is not convex on $\{d\ge0\}$.

**Assessment.**
- **Truth: true.**
  - $F(0)=1$, $F(1)=\sqrt{3/2}+\tfrac12\approx1.72474$, $F(2)=2+\tfrac14=2.25$.
  - $(F(0)+F(2))/2=1.625<F(1)$. Exactly: $\sqrt{3/2}>9/8$ is equivalent to $96/64>81/64$.
  - $F''<0$ on $(0,0.6599)$ and on $(9.6697,\infty)$ (`noncvx.out`). The first term
    $\sqrt{((d+1)^2-1)/2}$ is concave on $d>0$, and $2^{-d}$ is convex but decays exponentially,
    so it cannot compensate for large $d$.
  - The domain is convex, so the negation of `ConvexOn` really means the inequality fails.
- **Vacuity:** not applicable (a closed statement).
- **Junk:** none, since $d^2/2+d\ge0$ on the domain.
- **Note:** the squared cost $F^2$ satisfies the midpoint inequality at $0,1,2$, but violates it
  near $0$ (`squared_variant.out`).
- **Standard fact:** with $M'\ne0$, $\sqrt{V\tilde C}$ is no longer a seminorm. Here it behaves
  like $\sqrt d$ near $0$ and is concave on all of $d>0$.
