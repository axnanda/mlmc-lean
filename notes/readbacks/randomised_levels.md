# Blind read-back audit: `MlmcLean.Randomised` (packet L2)

| Field | Value |
|---|---|
| Date | 2026-09-29 |
| Packet (relative to scratchpad) | `readback/round10/packet_L2_randomised.lean` |
| Declarations audited | 17: the 16 in `MlmcLean.Randomised` (12 theorems/lemmas, 4 defs) plus the appended def `levelDiff` |
| Auditor | independent blind auditor (sub-agent) |
| Scripts directory | `readback/round10/work_L2/` (`01_…` to `08_…`, each `.py` with its `.out`) |
| Toolchain assumed | Lean v4.33.1, Mathlib `0df444a`. Definitions checked in `.lake/packages/mathlib` only |

Mathlib conventions checked in the sources and used below:
- `IndepFun f g μ` is defined for **any** measure (`Kernel.IndepFun … (Kernel.const Unit μ) (dirac ())`). By `indepFun_iff_measure_inter_preimage_eq_mul` it means $\mu(f^{-1}s\cap g^{-1}t)=\mu(f^{-1}s)\,\mu(g^{-1}t)$ with no finiteness assumption.
- `variance X μ = (evariance X μ).toReal`, where `evariance` $=\int^-\lVert X-\mu[X]\rVert_e^2$. So $\mathrm{Var}=0$ when $X\notin L^2$ (`variance_of_not_memLp`).
- `μ.real s = (μ s).toReal`, so $\infty\mapsto 0$.
- `tsum` of a non-summable family is $0$. `HasSum` and `Summable` default to unconditional summation, which for $\mathbb R$ means absolute summation.
- `MeasurePreserving f μa μb` means `Measurable f ∧ map f μa = μb`.
- `MeasurableSpace ℕ = ⊤`.
- The bodies of `∑ x ∈ s, body` and `∑' x, body` are parsed at precedence 67. So `∑ …, a * b` keeps the product inside the sum, while `∧`, `=` and `≤` end the body.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `singleTerm` | def | n/a | n/a | n/a ($p_{K}=0\Rightarrow Y=0$; every probabilistic theorem assumes $p>0$; #10 is a pure identity) |
| 2 | `setIntegral_level` | lemma (any measure) | **True** | No | No. The degenerate branches (non-integrable $h$, $\mu(\Omega)\in\{0,\infty\}$) give $0=0$ by convention; the main case is genuine |
| 3 | `hasSum_measureReal_level` | lemma | **True** | No | No |
| 4 | `integral_comp_level` | theorem (any measure) | **True** | No | No. Only the degenerate $\mu(\Omega)\in\{0,\infty\}$ branch gives $0=0$ |
| 5 | `integral_singleTerm` | theorem (any measure, forced to be a probability) | **True** | No | No |
| 6 | `sq_tsum_le_tsum_sq_div` | lemma | **True** | No | No |
| 7 | `singleTerm_variance_ge` | theorem | **True** | No | No. `hsum2` rules out the junk $\mathrm{Var}(Y)=0$; without it the statement would be false |
| 8 | `summable_of_memLp_singleTerm` | theorem | **True** | No | No |
| 9 | `singleTermN` | def | n/a | n/a | n/a ($N=0\Rightarrow 0$) |
| 10 | `singleTermN_eq_sum_levels` | theorem | **True** | No | No (an exact identity; the $0^{-1}=0$ convention appears on both sides) |
| 11 | `integral_levelCount` | theorem | **True** | No | No |
| 12 | `geomLevelProb` | def | n/a | n/a | n/a (not a distribution when $\beta+\gamma\le 0$; no theorem uses it) |
| 13 | `randomised_optimal_p` | theorem | **True** | No | No |
| 14 | `optimalLevelProb` | def | n/a | n/a | n/a ($\equiv 0$ if $\sum\sqrt{V/C}$ diverges; excluded by `hZ` in #15) |
| 15 | `randomised_optimal_p_eq` | theorem | **True** | No | No |
| 16 | `randomised_infinite_cost` | theorem | **True** | No | No (the conclusion is a lintegral $=\top$, not a Bochner junk value) |
| 17 | `levelDiff` (appended) | def | n/a | n/a | n/a |

No statement in the packet has an existential quantifier. Every quantity, including $\beta,\gamma,c_2,c_3$ in #16, is a universally quantified parameter.

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement was found.** One concrete model satisfies all hypotheses of #2–#8, #10, #11 and #16 at once. Call it the running example (E):
   - $\Omega=\mathbb N\times\{\pm1\}^{\mathbb N}$ with $\mu=\mathrm{Geom}\otimes\mathrm{Rademacher}^{\otimes\mathbb N}$;
   - $K(k,\varepsilon)=k$ with $p_\ell=2^{-(\ell+1)}$;
   - $P_\ell=\sum_{j\le\ell}2^{-j}\varepsilon_j$, so $\Delta_\ell=2^{-\ell}\varepsilon_\ell$ and $\mathrm{Var}\,\Delta_\ell=4^{-\ell}$;
   - $\kappa_\ell\equiv 4^\ell$, with $\beta=\gamma=2$ and $c_2=c_3=1$.

   In (E), $Y=2\varepsilon_K$, $\mathbb E Y=0$, $\mathrm{Var}\,Y=4=\sum\mathrm{Var}\,\Delta_\ell/p_\ell$, and $\mathbb E\kappa_K=\sum 2^{-(\ell+1)}4^\ell=\infty$. See scripts 02 and 05.
2. **Three results are stated for an arbitrary measure** (`omit [IsProbabilityMeasure μ]`): #2, #4 and #5. This is harmless. Mathlib's `IndepFun` with $s=t=$ univ gives $\mu(\Omega)=\mu(\Omega)^2$, so $\mu(\Omega)\in\{0,1,\infty\}$. In the $0$ and $\infty$ cases both sides of #2 and #4 are $0$: `μ.real` $=\mathrm{toReal}\,\infty=0$, and an integrable function independent of $K$ must vanish a.e. In #5, $0<p_\ell=\mu_{\mathbb R}\{K=\ell\}$ forces $\mu(\Omega)=1$. The extra generality is only formal (script 01).
3. **In `singleTerm_variance_ge` (#7), `hsum2` is load-bearing and prevents a junk value.** It gives $\mathbb E Y^2=\sum\mathbb E\Delta_\ell^2/p_\ell<\infty$, so `variance (singleTerm …)` is the true variance and not Mathlib's $0$. Without `hsum2` the Lean statement is false. Counterexample: $p_\ell=\tfrac34 4^{-\ell}$ and $\Delta_\ell=2^{-\ell}+8^{-\ell}\varepsilon_\ell$ give $Y\notin L^2$, so Lean's $\mathrm{Var}\,Y=0$, while $\sum\mathrm{Var}\,\Delta_\ell/p_\ell=64/45$ (script 02).
4. **#7 is only a lower bound.** The exact standard formula is $\mathrm{Var}\,Y=\sum_\ell\mathbb E[\Delta_\ell^2]/p_\ell-(\sum_\ell\mathbb E\Delta_\ell)^2$. The gap between the two is the Cauchy–Schwarz gap $\sum(\mathbb E\Delta_\ell)^2/p_\ell-(\sum\mathbb E\Delta_\ell)^2\ge 0$ from #6.
5. **Independence is only pairwise**: $K\perp\Delta_\ell$ and $K\perp\kappa_\ell$ for each $\ell$ separately. This is weaker than the usual assumption that $K$ is independent of the whole simulation, so the theorems are at least as strong as the textbook ones.
6. **#5 proves $\mathbb E Y=\sum_\ell\mathbb E\Delta_\ell$**, which telescopes to $\lim_L\mathbb E P_L$. The packet has no limit object $P$, so "unbiased for $\mathbb E P$" would still need $\mathbb E P_L\to\mathbb E P$.
7. **#16 is the contrapositive form of "finite variance and finite expected cost require $\beta>\gamma$".**
   - It correctly uses *lower* bounds on $V_\ell=\mathrm{Var}\,\Delta_\ell$ and $C_\ell$, the right direction for an impossibility result.
   - Its hypotheses implicitly force $\beta>0$.
   - `hκi` is redundant: if $\kappa_\ell$ were not integrable, then $C_\ell=\int\kappa_\ell=0$, which contradicts `hCb`.
   - The converse direction is **not** stated anywhere in the packet: for $\beta>\gamma$, `geomLevelProb` gives finite variance and finite cost. `geomLevelProb` is defined but unused.
8. **The "optimal $p$" results (#13, #15) are about the abstract functional $(\sum V/p)(\sum pC)$** for sequences $V$ and $C$. They are not tied to $\mathrm{Var}(Y)\cdot\mathbb E[\text{cost}]$ of the estimator by any statement in this packet. #13 holds for every $p>0$, normalised or not, so its name ("optimal_p") oversells it: it is the Cauchy–Schwarz lower bound.
9. **Section `Nsamples` assumes no independence among the maps $\xi_n$.** Neither of its theorems needs it. No statement about the mean or variance of `singleTermN` appears in this packet.
10. **Minor redundancies:** `ha` in #6 follows from `hq1` and `ha2`, since $|a|\le\tfrac12(a^2/q+q)$. `hκi` in #16 is redundant as noted in point 7.

---

## Per-declaration analysis

Notation: $\Delta_\ell=$ `levelDiff Pl ℓ`, $Y=$ `singleTerm Pl K p`, $\mu_{\mathbb R}(s)=$ `μ.real s` $=(\mu s).\mathrm{toReal}$, and $\mathrm{Var}=$ Mathlib `variance`.

### 1. `singleTerm` (def)

**Rendering.** For $P:\mathbb N\to\Omega\to\mathbb R$, $K:\Omega\to\mathbb N$ and $p:\mathbb N\to\mathbb R$,
$$Y(\omega)=p_{K(\omega)}^{-1}\,\Delta_{K(\omega)}(\omega).$$
Lean's convention $0^{-1}=0$ makes $Y(\omega)=0$ where $p_{K(\omega)}=0$. The definition needs no σ-algebra (`omit [MeasurableSpace Ω]`). This is the single-term randomised estimator of Rhee–Glynn and McLeish, $Z=\Delta_N/\mathbb P(N=n)$, with $N=K$.

### 2. `setIntegral_level` (lemma; arbitrary measure, `IsProbabilityMeasure` omitted)

**Rendering.** Let $\mu$ be any measure on $\Omega$ and let $\ell\in\mathbb N$. Assume $K:\Omega\to\mathbb N$ and $h:\Omega\to\mathbb R$ are measurable and $K\perp h$ under $\mu$ in Mathlib's sense. Then
$$\int_{\{K=\ell\}}h\,d\mu=\mu_{\mathbb R}\{K=\ell\}\cdot\int_\Omega h\,d\mu .$$
There is no integrability hypothesis on $h$.

**Assessment.**
- *Truth: true.* Independence with $s=t=$ univ gives $\mu(\Omega)\in\{0,1,\infty\}$ (script 01, part A).
  - $\mu(\Omega)=1$, $h$ integrable: $\mathbf 1_{\{K=\ell\}}$ is a bounded function of $K$, so $\mathbb E[\mathbf 1_{\{K=\ell\}}h]=\mathbb P(K=\ell)\,\mathbb E h$.
  - $\mu(\Omega)=1$, $h$ not integrable: RHS $=\mathbb P(K=\ell)\cdot 0=0$. By independence for lintegrals, $\int^-_{\{K=\ell\}}|h|=\mathbb P(K=\ell)\int^-|h|$. This is $\infty$ if $\mathbb P(K=\ell)>0$, so LHS $=0$ by convention; and LHS $=0$ trivially if $\mathbb P(K=\ell)=0$ (script 01, part D).
  - $\mu(\Omega)=0$: both sides are $0$.
  - $\mu(\Omega)=\infty$: every set in $\sigma(K)$ or $\sigma(h)$ has measure $0$ or $\infty$. So $\mu_{\mathbb R}\{K=\ell\}=0$, and $h$ is either a.e. $0$ on $\{K=\ell\}$ or not integrable there. Both sides are $0$ (script 01, part B).
- *Vacuity:* no. Example (E) with $h=\Delta_\ell$ works.
- *Junk:* the degenerate branches hold as $0=0$ by convention. The substantive branch (probability measure, integrable $h$) is the genuine identity, so the statement does not hold *only* because of junk.
- *Hypotheses:* not stronger than needed. `Measurable h` could be a.e.-measurability.
- *Standard result:* $\mathbb E[\mathbf 1_{\{K=\ell\}}h]=\mathbb P(K=\ell)\,\mathbb E h$ for independent $K$ and $h$.

### 3. `hasSum_measureReal_level` (lemma; probability measure)

**Rendering.** If $\mu$ is a probability measure and $K:\Omega\to\mathbb N$ is measurable, then $\sum_{\ell\in\mathbb N}\mu_{\mathbb R}\{K=\ell\}=1$, as an unconditional `HasSum`.

**Assessment.**
- *Truth: true.* The sets $\{K=\ell\}$ are disjoint, measurable and cover $\Omega$. Countable additivity applies, and all terms are finite so `toReal` commutes with the sum.
- *Vacuity:* no.
- *Junk:* no.
- *Hypotheses:* the probability assumption is necessary and is present; it is not omitted for this lemma.

### 4. `integral_comp_level` (theorem; arbitrary measure, `IsProbabilityMeasure` omitted)

**Rendering.** Let $\mu$ be any measure and $K$ be measurable. Let $g:\mathbb N\to\Omega\to\mathbb R$ be such that for every $\ell$, $g_\ell$ is measurable, $\mu$-integrable and $K\perp g_\ell$. Assume $\sum_\ell\mu_{\mathbb R}\{K=\ell\}\int|g_\ell|\,d\mu<\infty$ (`Summable`). Then $\omega\mapsto g_{K(\omega)}(\omega)$ is integrable and
$$\int g_{K(\omega)}(\omega)\,d\mu(\omega)=\sum_\ell\mu_{\mathbb R}\{K=\ell\}\int g_\ell\,d\mu .$$

**Assessment.**
- *Truth: true.*
  - Probability case: $g_K=\sum_\ell\mathbf 1_{\{K=\ell\}}g_\ell$, which is measurable. By independence ($|g_\ell|$ is a function of $g_\ell$), $\int|g_K|=\sum_\ell\mu\{K=\ell\}\int|g_\ell|<\infty$. Countable additivity of the integral plus #2 then gives the identity. The RHS series is dominated by `hsum`, so the `tsum` is a genuine sum.
  - $\mu(\Omega)=\infty$: sets in $\sigma(g_\ell)$ have measure $0$ or $\infty$. Integrability (Markov) then forces $\mu\{|g_\ell|>t\}=0$ for all $t>0$, so $g_\ell=0$ a.e. Hence $g_K=0$ a.e., and both sides are $0$ because $\mu_{\mathbb R}\{K=\ell\}=0$.
  - $\mu(\Omega)=0$: trivial.
- *Vacuity:* no. Take $g_\ell=\Delta_\ell/p_\ell$ in (E).
- *Junk:* only in the degenerate branch.
- *Hypotheses:* natural. `hsum` is exactly the integrability condition.
- *Standard result:* the random-index identity $\mathbb E[g_K]=\sum_\ell\mathbb P(K=\ell)\,\mathbb E[g_\ell]$ for $K$ independent of each $g_\ell$.

### 5. `integral_singleTerm` (theorem; arbitrary measure, `IsProbabilityMeasure` omitted)

**Rendering.** Let $\mu$ be any measure. Assume:
- $K$ is measurable;
- every $P_\ell$ is measurable and integrable;
- $\mu_{\mathbb R}\{K=\ell\}=p_\ell$ and $p_\ell>0$ for all $\ell$;
- $K\perp\Delta_\ell$ for each $\ell$ separately;
- $\sum_\ell\int|\Delta_\ell|\,d\mu<\infty$.

Then $Y$ is integrable and $\int Y\,d\mu=\sum_\ell\int\Delta_\ell\,d\mu$.

**Assessment.**
- *Truth: true.* The hypotheses force $\mu(\Omega)=1$. Independence gives $\mu(\Omega)\in\{0,1,\infty\}$, and both $0$ and $\infty$ make $\mu_{\mathbb R}\{K=\ell\}=0$, which contradicts $p_\ell>0$ (script 01, part C). Then apply #4 with $g_\ell=\Delta_\ell/p_\ell$: $\mu_{\mathbb R}\{K=\ell\}\int|g_\ell|=\int|\Delta_\ell|$ is summable, and $\mathbb E Y=\sum p_\ell\,\mathbb E\Delta_\ell/p_\ell$. The RHS series converges absolutely, so the `tsum` is genuine. Checked numerically in script 02, where $\mathbb E Y$ matches $\sum\mathbb E\Delta_\ell$ to 20 digits and a Monte Carlo run agrees.
- *Vacuity:* no. In (E), $\int|\Delta_\ell|=2^{-\ell}$.
- *Junk:* no.
- *Hypotheses:* independence is only pairwise, which is weaker than the standard assumption. `hPl` (integrability of each $P_\ell$) could be weakened to integrability of each $\Delta_\ell$.
- *Standard result:* unbiasedness of the single-term estimator (Rhee & Glynn 2015; McLeish 2011): $\mathbb E Y=\sum_\ell\mathbb E\Delta_\ell=\lim_L\mathbb E P_L$ under $\sum\mathbb E|\Delta_\ell|<\infty$. Note that the statement stops at $\sum_\ell\mathbb E\Delta_\ell$; see main point 6.

### 6. `sq_tsum_le_tsum_sq_div` (lemma)

**Rendering.** Let $a,q:\mathbb N\to\mathbb R$ with $q_\ell>0$, $\sum q_\ell=1$ (`HasSum`), $a$ summable and $a^2/q$ summable. Then $(\sum_\ell a_\ell)^2\le\sum_\ell a_\ell^2/q_\ell$.

**Assessment.**
- *Truth: true.* By Cauchy–Schwarz, $(\sum a_\ell)^2=(\sum\tfrac{a_\ell}{\sqrt{q_\ell}}\sqrt{q_\ell})^2\le\sum\tfrac{a_\ell^2}{q_\ell}\sum q_\ell$. Equality holds iff $a\propto q$. Script 03: 500 random trials, and an equality case $9=9$.
- *Vacuity:* no.
- *Junk:* no; all sums are genuinely summable.
- *Hypotheses:* `ha` is redundant, since $|a_\ell|\le\tfrac12(a_\ell^2/q_\ell+q_\ell)$ (verified in script 03).

### 7. `singleTerm_variance_ge` (theorem; probability measure)

**Rendering.** Let $\mu$ be a probability measure. Assume:
- $K$ is measurable;
- every $P_\ell$ is measurable and in $L^2(\mu)$;
- $\mu_{\mathbb R}\{K=\ell\}=p_\ell>0$;
- $K\perp\Delta_\ell$ for all $\ell$;
- $\sum_\ell\big(\int\Delta_\ell^2\,d\mu\big)/p_\ell<\infty$.

Then
$$\sum_\ell\frac{\mathrm{Var}(\Delta_\ell)}{p_\ell}\le\mathrm{Var}(Y).$$

**Assessment.**
- *Truth: true.* By independence, $\mathbb E Y^2=\sum_\ell p_\ell\,\mathbb E\Delta_\ell^2/p_\ell^2=\sum_\ell\mathbb E\Delta_\ell^2/p_\ell<\infty$. So $Y\in L^2$ and $\mathrm{Var}\,Y$ is the genuine variance. Also $\mathbb E Y=\sum\mathbb E\Delta_\ell$, which converges absolutely by Cauchy–Schwarz. Then
  $$\mathrm{Var}\,Y-\sum\frac{\mathrm{Var}\,\Delta_\ell}{p_\ell}=\sum\frac{(\mathbb E\Delta_\ell)^2}{p_\ell}-\Big(\sum\mathbb E\Delta_\ell\Big)^2\ge0$$
  by #6, using $\sum p_\ell=1$. The LHS series is genuinely summable because $0\le\mathrm{Var}\,\Delta_\ell\le\mathbb E\Delta_\ell^2$. Script 02 confirms $\mathrm{Var}\,Y=\sum\mathbb E\Delta^2/p-(\sum\mathbb E\Delta)^2$ exactly, with the gap equal to the Cauchy–Schwarz gap. The minimum gap over 200 random trials was $0.799>0$; the equality case is 4 = 4; a strict case is $8\ge 6$.
- *Vacuity:* no; (E) satisfies every hypothesis.
- *Junk:* no, and `hsum2` is essential. It is exactly what excludes the junk value $\mathrm{Var}\,Y=0$ for $Y\notin L^2$. Counterexample without it: $p_\ell=\tfrac34 4^{-\ell}$, $\Delta_\ell=2^{-\ell}+8^{-\ell}\varepsilon_\ell$. Every other hypothesis holds, but the Lean statement reads $64/45\le 0$ (script 02).
- *Hypotheses:* natural; `hsum2` is equivalent to $Y\in L^2$.
- *Standard result:* the exact variance formula for the single-term estimator (Rhee–Glynn), $\mathrm{Var}\,Y=\sum\mathbb E\Delta_\ell^2/p_\ell-(\mathbb E Y)^2$, weakened to the lower bound in terms of the MLMC variances $V_\ell$.

### 8. `summable_of_memLp_singleTerm` (theorem; probability measure)

**Rendering.** Same setting as #7, but with hypothesis $Y\in L^2(\mu)$ instead of `hsum2`. Conclusion: $\sum_\ell\mathrm{Var}(\Delta_\ell)/p_\ell$ is summable.

**Assessment.**
- *Truth: true.* By monotone convergence and independence, $\int^-Y^2=\sum_\ell\mathbb E\Delta_\ell^2/p_\ell$, which is finite. Then $0\le\mathrm{Var}\,\Delta_\ell/p_\ell\le\mathbb E\Delta_\ell^2/p_\ell$.
- *Vacuity:* no; (E) works.
- *Junk:* no. The variances are genuine because $\Delta_\ell\in L^2$.
- *Standard result:* finite variance of the randomised estimator implies $\sum V_\ell/p_\ell<\infty$.

### 9. `singleTermN` (def)

**Rendering.** For sample maps $\xi:\mathbb N\to\Omega'\to\Omega$ and $N\in\mathbb N$,
$$\bar Y_N(x)=N^{-1}\sum_{n=0}^{N-1}Y(\xi_n(x)),$$
with $N$ cast to $\mathbb R$. For $N=0$ this is $0^{-1}\cdot0=0$. The definition carries no measure structure, and nothing in the packet assumes the $\xi_n$ are independent.

### 10. `singleTermN_eq_sum_levels` (theorem)

**Rendering.** For all $P,K,p,\xi,N,x$ and every `Finset` $S\subseteq\mathbb N$ with $K(\xi_n x)\in S$ for all $n<N$, both of the following hold:
- (a) $\displaystyle\bar Y_N(x)=\sum_{\ell\in S}(p_\ell N)^{-1}\sum_{n<N,\;K(\xi_nx)=\ell}\Delta_\ell(\xi_nx)$;
- (b) $\displaystyle\sum_{\ell\in S}\#\{n<N:K(\xi_nx)=\ell\}=N$, in $\mathbb R$.

The precedence-67 rule makes the statement parse as (a) $\wedge$ (b), as intended.

**Assessment.**
- *Truth: true.* It is a fibrewise regrouping of a finite sum. The step $(p_\ell N)^{-1}=p_\ell^{-1}N^{-1}$ holds in $\mathbb R$ for all values, including $0$. Script 06 checks it exactly in 9000 random instances, including $p_\ell\in\{0,-1/3\}$, $N=0$ and $S$ strictly larger than the set of realised levels.
- *Vacuity:* no; take $S$ to be the set of realised levels.
- *Junk:* no. For $p>0$ and $N\ge1$ it is the genuine identity; the degenerate values are handled consistently on both sides.
- *Standard result:* $N$ samples of the randomised estimator form an MLMC estimator with random (multinomial) sample sizes $N_\ell$ and weights $1/(p_\ell N)=1/\mathbb E N_\ell$.

### 11. `integral_levelCount` (theorem)

**Rendering.** Let $\mu'$ be a probability measure on $\Omega'$ and $\mu$ any measure on $\Omega$. Assume $K$ is measurable and every $\xi_n$ ($n\in\mathbb N$) is measure-preserving $(\Omega',\mu')\to(\Omega,\mu)$. Then for all $N,\ell\in\mathbb N$:
$$\int\#\{n<N:K(\xi_nx)=\ell\}\,d\mu'(x)=N\,\mu_{\mathbb R}\{K=\ell\}.$$

**Assessment.**
- *Truth: true.* By linearity, the left side is $\sum_{n<N}\mu'(\xi_n^{-1}\{K=\ell\})=N\mu\{K=\ell\}$. $\mu$ is automatically a probability measure, being a pushforward of $\mu'$. No independence is needed: script 07 checks i.i.d., identical-copy and alternating couplings exactly.
- *Vacuity:* no.
- *Junk:* no; the count is bounded by $N$, hence integrable.
- *Standard result:* $\mathbb E N_\ell=Np_\ell$.

### 12. `geomLevelProb` (def)

**Rendering.** $p_\ell=(1-r)\,r^\ell$ with $r=2^{-(\beta+\gamma)/2}$. Here $2^{(\cdot)}$ is `Real.rpow` with base $2>0$, and $r^\ell$ is a natural-number power.
- For $\beta+\gamma>0$, $0<r<1$: a geometric distribution on $\mathbb N$ with $p_\ell\propto2^{-(\beta+\gamma)\ell/2}=\sqrt{2^{-\beta\ell}/2^{\gamma\ell}}$. It coincides with `optimalLevelProb` for $V_\ell=2^{-\beta\ell}$ and $C_\ell=2^{\gamma\ell}$ (script 08). This is the standard Rhee–Glynn/Giles choice.
- For $\beta+\gamma=0$: all $p_\ell=0$.
- For $\beta+\gamma<0$: all $p_\ell<0$.

No statement in this packet uses it.

### 13. `randomised_optimal_p` (theorem)

**Rendering.** Let $V,C,p:\mathbb N\to\mathbb R$ with $V,C\ge0$ and $p>0$; $p$ need not be normalised. Assume $\sum V_\ell/p_\ell<\infty$ and $\sum p_\ell C_\ell<\infty$. Then $\sqrt{V_\ell C_\ell}$ is summable and
$$\Big(\sum_\ell\sqrt{V_\ell C_\ell}\Big)^2\le\Big(\sum_\ell V_\ell/p_\ell\Big)\Big(\sum_\ell p_\ell C_\ell\Big).$$

**Assessment.**
- *Truth: true.* Write $\sqrt{V_\ell C_\ell}=\sqrt{V_\ell/p_\ell}\,\sqrt{p_\ell C_\ell}$. The bound $\le\tfrac12(V_\ell/p_\ell+p_\ell C_\ell)$ gives summability, and Cauchy–Schwarz gives the inequality. The square root only sees $V C\ge0$, so no square-root junk arises. Script 03: 500 random trials.
- *Vacuity:* no. Example: $V=4^{-\ell}$, $C=2^\ell$, $p_\ell=\tfrac23 3^{-\ell}$.
- *Junk:* no.
- *Hypotheses and naming:* this is the lower bound for every $p$, not an optimality statement; the name oversells it.
- *Standard result:* the Cauchy–Schwarz lower bound on variance × expected cost for randomised MLMC.

### 14. `optimalLevelProb` (def)

**Rendering.** $p^*_\ell=\sqrt{V_\ell/C_\ell}\,\big/\,\sum_k\sqrt{V_k/C_k}$. Junk behaviour:
- if the series diverges, the `tsum` is $0$ and $p^*\equiv0$ (because $x/0=0$);
- if $V_\ell/C_\ell<0$, the square root is $0$.

Both cases are excluded in #15.

### 15. `randomised_optimal_p_eq` (theorem)

**Rendering.** Let $V_\ell>0$ and $C_\ell>0$ for all $\ell$, with $\sum\sqrt{V_\ell C_\ell}<\infty$ and $\sum\sqrt{V_\ell/C_\ell}<\infty$. Then:
- $p^*_\ell>0$ for all $\ell$;
- $\sum_\ell p^*_\ell=1$ (`HasSum`);
- $V/p^*$ and $p^*C$ are summable;
- $\big(\sum V_\ell/p^*_\ell\big)\big(\sum p^*_\ell C_\ell\big)=\big(\sum\sqrt{V_\ell C_\ell}\big)^2$.

**Assessment.**
- *Truth: true.* With $Z=\sum\sqrt{V/C}>0$, we have $V_\ell/p^*_\ell=Z\sqrt{V_\ell C_\ell}$ and $p^*_\ell C_\ell=\sqrt{V_\ell C_\ell}/Z$. Script 04 checks these to 40 digits. Combined with #13, $p^*$ minimises the scale-invariant product; no random $p$ in script 04 beat it.
- *Hypotheses:* `hS` and `hZ` are independent. For example, $V=1$, $C=4^{-\ell}$ satisfies `hS` but not `hZ`.
- *Vacuity:* no. Example: $V=4^{-\ell}$, $C=2^\ell$.
- *Junk:* no; `hZ` rules out the $x/0$ case.
- *Standard result:* the optimal level distribution $p_\ell\propto\sqrt{V_\ell/C_\ell}$, which attains $(\sum\sqrt{V_\ell C_\ell})^2$.

### 16. `randomised_infinite_cost` (theorem; probability measure)

**Rendering.** Let $\mu$ be a probability measure. Assume:
- $K$ is measurable;
- every $P_\ell$ is measurable and in $L^2$;
- $\mu_{\mathbb R}\{K=\ell\}=p_\ell>0$ and $K\perp\Delta_\ell$ for all $\ell$;
- cost functions $\kappa_\ell:\Omega\to\mathbb R$ are measurable, $\ge0$, integrable, $K\perp\kappa_\ell$, with $\int\kappa_\ell\,d\mu=C_\ell$;
- real parameters satisfy $\beta\le\gamma$, $c_2>0$, $c_3>0$;
- $c_2\,2^{-\beta\ell}\le\mathrm{Var}(\Delta_\ell)$ and $c_3\,2^{\gamma\ell}\le C_\ell$ for all $\ell\in\mathbb N$ (real powers);
- $Y\in L^2(\mu)$.

Then
$$\int^-\mathrm{ofReal}\big(\kappa_{K(\omega)}(\omega)\big)\,d\mu=\infty,$$
i.e. the expected cost of one sample of $Y$ is infinite.

**Assessment.**
- *Truth: true.*
  1. #8 gives $\sum V_\ell/p_\ell<\infty$.
  2. By lintegral additivity and independence, $\int^-\kappa_K=\sum_\ell p_\ell C_\ell$.
  3. If this were finite, #13 would give $\sum\sqrt{V_\ell C_\ell}<\infty$.
  4. But $\sqrt{V_\ell C_\ell}\ge\sqrt{c_2c_3}\,2^{(\gamma-\beta)\ell/2}\ge\sqrt{c_2c_3}>0$, so the terms do not tend to $0$. Contradiction.
- *Vacuity:* no. (E) with $\beta=\gamma=2$ and $c_2=c_3=1$ satisfies everything, and there $\sum p_\ell C_\ell$ diverges (script 05).
- *Implicit constraint:* the hypotheses force $\beta>0$. Since $p_\ell\le1$, $V_\ell/p_\ell\ge c_2 2^{-\beta\ell}$ must be summable.
- *Junk:* no. $\mathrm{Var}\,\Delta_\ell$ is genuine because $\Delta_\ell\in L^2$. The conclusion is a lintegral equal to $\top$, not a junk Bochner value.
- *Hypotheses:* lower bounds on $V_\ell$ and $C_\ell$ are the right direction for an impossibility result. A lower bound on $\mathbb E\Delta_\ell^2$ would suffice, so bounding $\mathrm{Var}$ is slightly stronger than needed, but it is the standard $V_\ell$. `hκi` is redundant: non-integrability would give $C_\ell=0$, contradicting `hCb`.
- *Standard result:* the single-term randomised MLMC estimator can have finite variance and finite expected cost only if $\beta>\gamma$ (Rhee–Glynn 2015; Giles, Acta Numerica 2015, randomised MLMC section). Script 05 shows that with geometric $p$ both are finite iff $2^{-\beta}<r<2^{-\gamma}$, i.e. iff $\beta>\gamma$. The positive direction is not stated in this packet.

### 17. `levelDiff` (def, from `MlmcLean.LevelDiff`)

**Rendering.** $\Delta_0=P_0$ and $\Delta_{\ell+1}=P_{\ell+1}-P_\ell$ (pointwise). This is the standard MLMC correction, with $\sum_{\ell\le L}\Delta_\ell=P_L$.

---

## Scripts (`readback/round10/work_L2/`)

| script | checks |
|---|---|
| `01_indep_forces_mass.py/.out` | $x=x^2$ in $[0,\infty]$ iff $x\in\{0,1,\infty\}$; the $\infty\cdot\delta_0$ example for #2; #5's hypotheses force $\mu(\Omega)=1$; non-integrable $h$ branch of #2 |
| `02_single_term_moments.py/.out` | #5, #7 and #8 on Rademacher models (exact to 40 digits, 200 random trials, Monte Carlo); counterexample showing `hsum2` is load-bearing |
| `03_cauchy_schwarz.py/.out` | #6 and #13 (500 random trials each); redundancy of `ha` |
| `04_optimal_p_eq.py/.out` | #15 identities; $p^*$ minimises versus random $p$; junk case of #14 |
| `05_infinite_cost.py/.out` | #16 instance ($\beta=\gamma=2$); boundary $\beta>\gamma$ for geometric $p$; $\beta>0$ forced |
| `06_singleTermN_regroup.py/.out` | #10 exactly, 9000 instances with Lean's $0^{-1}=0$ |
| `07_levelCount.py/.out` | #11 exactly under three couplings |
| `08_geomLevelProb.py/.out` | #12 sums to 1 and equals `optimalLevelProb` when $\beta+\gamma>0$; degenerate when $\beta+\gamma\le0$ |
