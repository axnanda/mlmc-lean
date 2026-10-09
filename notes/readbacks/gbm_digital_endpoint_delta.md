# Blind read-back report: R49 digital (GBM, Euler–Maruyama / Milstein, digital option)

| field | value |
|---|---|
| date | 2026-10-08 |
| packet | `readback/round26/packet_R49_digital.lean` |
| declarations audited | 6 (1 definition `logRatioStep` + 5 theorems); the 15 appended supporting definitions are rendered as well |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round26/work_R49_digital/` (`thm1_mc.py/.out`, `thm1_threshold.py/.out`, `thm2_mc.py/.out`, `thm4_mc.py/.out`, Lean scratch files `Scratch.lean`, `Scratch2.lean`) |

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 0 | `logRatioStep` | def | n/a (not used in any packet statement) | n/a | n/a |
| 1 | `gbm_em_exact_mismatch_le` | theorem | true (constants very loose) | no | no (but trivially true for $n\le 1$ because $2h/T\ge 1$) |
| 2 | `gbm_em_digital_endpoint` | theorem | true | no | no |
| 3 | `gbm_em_digital_endpoint_log` | theorem | true | no | no |
| 4 | `gbm_digital_condExp_delta_variance_rate` | theorem | true | no | no |
| 5 | `gbm_digital_condExp_delta_corrections_rate` | theorem | true | no | no |

## Main points for a human auditor

1. **No false, vacuous or junk-dependent statement found.** Division by zero is ruled out by $\sigma\ne0$ and $T>0$. Theorems 4–5 assert `MemLp … 2`, so their integrals and variances are not the junk value 0. The kurtosis conjunct of Thm 2 is guarded by $P(Y\ne0)>0$.
2. **Thm 1's explicit bound is very loose.** It is $\ge 1$, so trivially true, for $n\le1$ through the $2h/T$ term. It only drops below 1 at large $n$: $n\ge13$ for $r=0.05,\sigma=0.2,T=1$ and $n\ge18$ for $\sigma=1$ (`thm1_threshold.out`). Monte Carlo puts the true worst-case-$K$ mismatch about 300–10 000 times below the bound (`thm1_mc.out`). The hypothesis $s_0\ne0$ is superfluous ($s_0=0$ gives probability 0). $\sigma\ne0$ is genuinely needed: with $\sigma=0$ the division $/0=0$ would make the statement false.
3. **Thm 2: all four conjuncts reduce to one fact.** Because $Y\in\{-1,0,1\}$, each one reduces to $p:=P(Y\ne0)\le C\sqrt{h(\ell+1)}$. In particular the kurtosis lower bound is exactly equivalent to conjunct (b), since $\mathrm{kurt}(Y)=1/p$. $C$ is uniform in $s_0$, $K$ and $\ell$. The rate is written with $(\ell+1)$, which is proportional to $\log(T/h)$, rather than with $\log(1/h)$.
4. **Thm 3 parsing.** `Real.log (T / 2 ^ (ℓ + 1))⁻¹` parses as $\log(h^{-1})=\log(1/h)$, not $(\log h)^{-1}$; this is checked in Lean (`Scratch2.lean`). The last conjunct is an elementary, $C$-free inequality, $\sqrt{hL}\le\sqrt h\,L$ for $L=\log(1/h)>1$.
5. **Thms 4–5: rate $h^q$ for every $q<1/2$.** This is the standard "$O(h^{1/2-\delta})$" form; $q$ may also be negative, which is trivial. Monte Carlo gives $E[\Delta_\ell^2]\approx0.1\,h^{1/2}$, while each single delta has second moment growing like $h^{-1/2}$ (`thm4_mc.out`). $C$ depends on $s_0$, $K$, $q$, $r$, $\sigma$, $T$ and is not uniform in $s_0$ or $K$. The hypotheses $s_0\ne0$ and $\sigma\ne0$ are harmless but not needed, because in those cases both deltas are the junk value 0. The variance conjunct follows from the second-moment conjunct.
6. **The formulas match their intended meaning.**
   - The "delta" formula $\varphi(d)\,K/(s_0\,\mathrm{std})$ equals $\partial_{s_0}\Phi((\mathrm{mean}-K)/\mathrm{std})$; this was checked by finite differences for both signs of $s_0$.
   - The coarse conditional mean uses the raw first-half increment $z_{2^{\ell+1}-2}$, which is Giles' coupling for the conditional-expectation trick.
   - The coarse EM path uses `pairAvg`, the correct Brownian coupling.
   - The exact solution at level $\ell$ driven by `pairAvg z` coincides with the exact solution at level $\ell+1$ driven by `z`.
7. **The packet matches the repository.** Each of the five packet statements is type-for-type identical (`rfl`) to the repository theorem of the same name (`Scratch2.lean`, checked via `import MlmcLean`).

---

## Supporting definitions (appended in the packet)

- `stdNormalSeq` is $\bigotimes_{i\in\mathbb N}\mathcal N(0,1)$ on $\mathbb R^{\mathbb N}$, so the coordinates $z_i$ are i.i.d. standard normal.
- `pairAvg z k` is $(z_{2k}+z_{2k+1})/\sqrt2$. Under `stdNormalSeq` it is again an i.i.d. $\mathcal N(0,1)$ sequence.
- `emPath a b h S₀ z i` is the Euler–Maruyama recursion $S_{i+1}=S_i+a(S_i,ih)h+b(S_i,ih)\sqrt h\,z_i$ with $S_0=S_0$.
  - With `gbmDrift r` $=rS$ and `gbmVol σ` $=\sigma S$, it gives $S_N=s_0\prod_{i<N}(1+rh+\sigma\sqrt h z_i)$.
- `gbmEM r σ T s₀ ℓ z` is the EM value at $T$ with $2^\ell$ steps of size $T/2^\ell$.
- `gbmExact r σ T s₀ ℓ z` is $s_0\exp\big((r-\sigma^2/2)T+\sigma\sqrt{T/2^\ell}\sum_{i<2^\ell}z_i\big)$. This is exact GBM at $T$ with $W_T=\sqrt{T/2^\ell}\sum_{i<2^\ell} z_i$.
- `milsteinStep a b h S dW` is $S+a(S)h+b(S)dW+\tfrac12 b(S)b'(S)(dW^2-h)$. For $a=rS$, $b=\sigma S$ this is $S\,(1+rh+\sigma dW+\tfrac12\sigma^2(dW^2-h))$, with $dW=\sqrt h z_i$ in `milsteinPath`.
- `gbmCondMeanFine/StdFine` (level $L$, $k=T/2^L$):
  - $M^f$ is the Milstein value after $2^L-1$ steps driven by $z$.
  - Mean $=M^f(1+rk)$; std $=|\sigma M^f|\sqrt k$.
  - These are the conditional law of a final Euler step given $z_0,\dots,z_{2^L-2}$.
- `gbmCondMeanCoarse/StdCoarse` (level $\ell$, $k=T/2^\ell$):
  - $M^c$ is the Milstein value after $2^\ell-1$ steps driven by `pairAvg z`.
  - Mean $=M^c\big(1+rk+\sigma\sqrt{k/2}\,z_{2^{\ell+1}-2}\big)$; std $=|\sigma M^c|\sqrt{k/2}$.
  - These are the conditional law of the final coarse Euler step after its first half-increment, $\sqrt{k/2}\,z_{2^{\ell+1}-2}$, is revealed. Both levels therefore condition on $z_0,\dots,z_{2^{\ell+1}-2}$.
- `gbmDigitalCondFineDelta/CoarseDelta` is $\varphi\big((\mathrm{mean}-K)/\mathrm{std}\big)\cdot K/(s_0\,\mathrm{std})$, with $\varphi$ the $\mathcal N(0,1)$ density (`gaussianPDFReal 0 1`).
  - Because mean and std are proportional to $s_0$ and $|s_0|$, this is exactly $\partial_{s_0}\Phi((\mathrm{mean}-K)/\mathrm{std})$, the pathwise delta of the conditional-expectation-smoothed digital payoff. Checked numerically in `thm4_mc.out`.
  - The junk value 0 occurs only when std $=0$ (Milstein value 0, a null set) or $s_0=0$.
- `kurtosis X ν` is $\int X^4\,d\nu/(\int X^2\,d\nu)^2$, with the junk value 0 when the denominator is 0.
- `fineCoarseDiff Pf Pc` is $Pf_0$ at $\ell=0$ and $Pf_{\ell+1}-Pc_\ell$ at $\ell+1$.

---

## 0. `logRatioStep` (definition)

**Rendering.** Let $u=a+bx$. Then
$$\mathrm{logRatioStep}(a,b,x)=\begin{cases}\log(1+u)-u+b^2/2,& u>-\tfrac12,\\ (b^2-u^2)/2,& u\le-\tfrac12.\end{cases}$$
Take $a=rh$, $b=\sigma\sqrt h$, $x=z_i$. On $\{u>-1/2\}$ the value is $\log(1+rh+\sigma\sqrt h z_i)-[(r-\sigma^2/2)h+\sigma\sqrt h z_i]$. That is the log-ratio of one EM factor to the corresponding exact GBM factor. The second branch is the quadratic surrogate given by the 2nd-order Taylor expansion, $\log(1+u)-u\approx-u^2/2$.

**Assessment.** This is a definition, so there is nothing to prove. It is not used in any of the five packet statements and is presumably a proof helper. It is discontinuous at $u=-1/2$ (a jump of about $0.068$), which is harmless for a helper.

## 1. `gbm_em_exact_mismatch_le`

**Rendering.** For all real $r$, $\sigma\ne0$, $T>0$, $s_0\ne0$, real $K$, $n\in\mathbb N$, and $h=T/2^n$, $D=\sigma^2+r^2T$:
$$P\big(\mathbf 1\{S^{ex}_T>K\}\ne\mathbf 1\{S^{EM}_T>K\}\big)\le 48ThD^2+\frac{2\big[T\big(\tfrac{r^2h}{2}+6D\sqrt{hD}\big)+160D\sqrt{Th\,n\ln2}\big]}{|\sigma|\sqrt T\sqrt{2\pi}}+\frac{2h}{T}.$$
- $S^{ex}_T=s_0e^{(r-\sigma^2/2)T+\sigma\sqrt h\sum_{i<2^n}z_i}$.
- $S^{EM}_T=s_0\prod_{i<2^n}(1+rh+\sigma\sqrt hz_i)$.
- Both are driven by the same i.i.d. $\mathcal N(0,1)$ variables $z_i$.
- $P$ is `stdNormalSeq.real`; $n$ is cast to $\mathbb R$, as Lean confirms. Note $n\ln2=\ln(T/h)$.

**Assessment.**
- **Truth: true.** Proof sketch:
  1. Let $u_i=rh+\sigma\sqrt hz_i$ and $E=\{\forall i:\ u_i>-1/2\}$. Since $E u_i^4=r^4h^4+6r^2\sigma^2h^3+3\sigma^4h^2\le3h^2D^2$ (using $h\le T$), Markov and a union bound give $P(E^c)\le16\cdot2^n\cdot3h^2D^2=48ThD^2$.
  2. On $E$, $S^{EM}$ has the sign of $s_0$, and $\log|S^{EM}|-\log|S^{ex}|=\delta:=\sum_i\mathrm{logRatioStep}(rh,\sigma\sqrt h,z_i)$. If $K$ has the opposite sign there is no mismatch on $E$; otherwise mismatch forces $|\log|S^{ex}|-\log|K||\le|\delta|$.
  3. $\log|S^{ex}|$ is Gaussian with standard deviation $|\sigma|\sqrt T$, so a window of half-width $\varepsilon$ costs at most $2\varepsilon/(|\sigma|\sqrt T\sqrt{2\pi})$.
  4. The mean of $\delta$ is $-Nr^2h^2/2$, the $Tr^2h/2$ term, plus a cubic remainder bounded by $N\cdot\frac83\sqrt3(hD)^{3/2}\le6TD\sqrt{hD}$.
  5. $\delta$ is a sum of independent sub-exponential terms of scale $hD$. Bernstein's inequality at deviation $160D\sqrt{Th\ln(T/h)}$ gives a tail far below $2h/T$.

  Monte Carlo over 10 parameter sets (including $s_0<0$, $r<0$, and non-trivial cases with bound $<1$ up to $n=16$) finds the empirical $\sup_K$ mismatch between about $10^{-4}$ and $3\cdot10^{-3}$ times the bound (`thm1_mc.out`).
- **Vacuity: none.** For example $r=0,\sigma=0.01,T=1,s_0=1,K=1,n=4$ has bound $0.657<1$.
- **Junk values: none.** All square-root arguments are $\ge0$ and the denominator is $>0$. The bound is however trivially $\ge1$ for $n\le1$, and $\ge1$ unless $n$ is large (table above).
- **Hypotheses.**
  - $s_0\ne0$ is unnecessary.
  - $\sigma\ne0$ is necessary: with $\sigma=0$ the middle term is the junk value $x/0=0$, and $K$ between $s_0e^{rT}$ and $s_0(1+rh)^N$ would make the statement false.

**Standard fact.** This is a non-asymptotic version of the $O(\sqrt{h\log(1/h)})$ (often stated $O(h^{1/2-\delta})$) bound on the probability that EM and the exact solution fall on opposite sides of a strike, in the style of Avikainen (2009) and Giles–Higham–Mao (2009). It rests on a bounded density of $\log S_T$ plus a strong-error tail bound.

## 2. `gbm_em_digital_endpoint`

**Rendering.** For real $r$, $\sigma\ne0$, $T>0$ there is $C\ge0$, depending only on $r,\sigma,T$, with the following property. For all real $s_0,K$ and $\ell\in\mathbb N$, write $h=T/2^{\ell+1}$ and
$$Y=\mathbf 1\{S^f>K\}-\mathbf 1\{S^c>K\},$$
where $S^f$ is the EM value with $2^{\ell+1}$ steps of size $h$ driven by $z$, and $S^c$ is the EM value with $2^\ell$ steps of size $2h$ driven by `pairAvg z`. Then:
- (a) $\mathrm{Var}(Y)\le C\sqrt{h(\ell+1)}$;
- (b) $P(Y\ne0)\le C\sqrt{h(\ell+1)}$;
- (c) $E[Y^4]\le C\sqrt{h(\ell+1)}$;
- (d) if $P(Y\ne0)>0$, then $(C\sqrt{h(\ell+1)})^{-1}\le E[Y^4]/(E[Y^2])^2$.

$(\ell+1)$ is the real number $\ell+1$, as Lean confirms.

**Assessment.**
- **Truth: true.** $Y\in\{-1,0,1\}$, so $E Y^4=EY^2=p:=P(Y\ne0)$, $\mathrm{Var}\,Y\le p$ and $\mathrm{kurt}(Y)=1/p$. Hence (a), (c) and (d) follow from (b); for (d), $p\le Cx$ with $Cx>0$ gives $(Cx)^{-1}\le1/p$.
  - For (b): the exact solution at level $\ell$ driven by `pairAvg z` equals the exact solution at level $\ell+1$ driven by $z$, and `pairAvg z` has law `stdNormalSeq`. A triangle inequality with Thm 1 at $n=\ell+1$ and $n=\ell$ then gives $p\le$ bound$(\ell+1)$ + bound$(\ell)$, which is $\le C\sqrt{h(\ell+1)}$ for a $C$ depending only on $(r,\sigma,T)$.
  - Thm 1's bound is free of $s_0$ and $K$, and $s_0=0$ is trivial, so the uniformity in $s_0$ and $K$ is justified.
  - Monte Carlo ($r=0.05,\sigma=0.2,T=1$, $\ell\le8$) gives $\sup_Kp_\ell/\sqrt{h(\ell+1)}\approx0.022$–$0.030$, essentially flat (`thm2_mc.out`).
- **Vacuity: none.** $\ell=0$ and any parameters satisfy the hypotheses, and $p>0$ for $K$ near $s_0$, so (d) is not vacuous.
- **Junk values: none.** $Y$ is bounded and measurable, so the integrals are genuine. Kurtosis is only used when $E Y^2=p>0$.
- **Hypotheses.** $\sigma\ne0$ is needed: with $\sigma=0$ and $r\ne0$ the two deterministic paths differ, so a $K$ between them gives $p=1$ for every $\ell$. The kurtosis conjunct carries no information beyond (b).

**Standard fact.** For the MLMC digital option with EM: $V_\ell=O(h^{1/2})$ up to a log factor (Giles–Higham–Mao 2009; Avikainen 2009). The kurtosis of the corrections blows up like $h^{-1/2}$ (Giles, Acta Numerica 2015).

## 3. `gbm_em_digital_endpoint_log`

**Rendering.** Same setting as Thm 2. There is $C\ge0$ such that for all $s_0,K,\ell$ with $h=T/2^{\ell+1}<e^{-1}$:
- (a) $\mathrm{Var}(Y)\le C\sqrt{h\log(1/h)}$;
- (b) $P(Y\ne0)\le C\sqrt{h\log(1/h)}$;
- (c) $E[Y^4]\le C\sqrt{h\log(1/h)}$;
- (d) $\sqrt{h\log(1/h)}\le\sqrt h\,\log(1/h)$.

Lean confirms that `Real.log (T / 2 ^ (ℓ + 1))⁻¹` is $\log(h^{-1})$; `rfl` against $(\log h)^{-1}$ fails.

**Assessment.**
- **Truth: true.**
  - (a)–(c) follow from Thm 2 if $\ell+1\le c\log(1/h)$. Write $x=(\ell+1)\ln2$ and $L=\log T$, so $\log(1/h)=x-L>1$.
    - If $T\le1$, then $\ell+1\le\log(1/h)/\ln2$.
    - If $T>1$, then $x/(x-L)<1+L$.

    So $C=C_2\max(1,1+\log T)/\sqrt{\ln2}$ works.
  - (d) holds because $\log(1/h)>1$ implies $\sqrt{\log(1/h)}\le\log(1/h)$.
- **Vacuity: none.** $h<e^{-1}$ holds for all large $\ell$.
- **Junk values: none.** $h>0$ and $\log(1/h)>1$.
- **Hypotheses.** Conjunct (d) is a padding inequality independent of $C$ and of the probabilistic objects.

**Standard fact.** This is the same digital-option MLMC variance bound in the $\sqrt{h\log(1/h)}$ form, together with the weaker $\sqrt h\log(1/h)$ corollary.

## 4. `gbm_digital_condExp_delta_variance_rate`

**Rendering.** Fix real $r$, $\sigma\ne0$, $T>0$, $s_0\ne0$, real $K$, and $q<1/2$. There is $C\ge0$, which may depend on all of these, such that for all $\ell\in\mathbb N$, with $h=T/2^{\ell+1}$ and $\Delta_\ell=\delta^f_{\ell+1}-\delta^c_\ell$ (fine Milstein+conditional-expectation delta at level $\ell+1$ minus coarse at level $\ell$, as rendered above):
- $\Delta_\ell\in L^2$;
- $E[\Delta_\ell^2]\le C h^q$;
- $\mathrm{Var}(\Delta_\ell)\le Ch^q$.

$h^q$ is `Real.rpow` with a positive base.

**Assessment.**
- **Truth: true.**
  - *$L^2$.* For fixed $\ell$, $|\delta^f|$ is bounded: $\varphi$ decays super-exponentially as $M^f\to0$. $|\delta^c|\le c(1+|z_{2^{\ell+1}-2}|)$: either $|\mathrm{mean}-K|\ge|K|/2$, giving a bounded value, or $1/|M^c|\lesssim1+|z|$.
  - *Rate.* $\mathrm{mean}^f-\mathrm{mean}^c=O(h)$ (Milstein strong order 1, and the $\tfrac12\sigma^2h(z^2-1)$ term) and $\mathrm{std}^f-\mathrm{std}^c=O(h)$. On the event $|\mathrm{mean}-K|\lesssim\sqrt h$, which has probability $O(\sqrt h)$, this gives $d^f-d^c=O(\sqrt h)$ and hence $\Delta=O(1)$. So $E\Delta^2=O(h^{1/2})$ up to tail and log effects, and $h^{1/2-\varepsilon}$ is the standard provable form.
  - *Monte Carlo* ($r=0.05,\sigma=0.2,T=1$; $(s_0,K)=(1,1),(1,1.15),(-1,-1)$; $\ell\le8$): $E\Delta^2/h^{1/2}\approx0.09$–$0.13$, while $E(\delta^f)^2$ grows like $h^{-1/2}$ (`thm4_mc.out`).
  - The variance conjunct follows from the second-moment conjunct.
- **Vacuity: none.** For example $r=0.05,\sigma=0.2,T=1,s_0=K=1,q=0.4$.
- **Junk values: none relied on.** Std $=0$ happens only on a null set (Milstein value 0). The $L^2$ membership is asserted, so $\int\Delta^2$ is not the junk value 0.
- **Hypotheses.** $s_0\ne0$ and $\sigma\ne0$ are superfluous: in those cases both deltas are junk 0 and the claim is trivial. Excluding them is harmless. $q$ may be $\le0$, where the claim is weaker (boundedness). $C$ is not uniform in $s_0$ or $K$.

**Standard fact.** Burgos & Giles (2012) / Giles (2008): MLMC for the digital-option delta with Milstein and conditional expectation over the final step gives $V_\ell=O(h^{1/2-\delta})$, observed as $\beta\approx1/2$.

## 5. `gbm_digital_condExp_delta_corrections_rate`

**Rendering.** Same fixed data and $q<1/2$. There is $C\ge0$ such that for all $\ell$ the MLMC correction $Y_\ell$ satisfies $Y_\ell\in L^2$ and $\mathrm{Var}(Y_\ell)\le C(T/2^\ell)^q$, where
- $Y_0=\delta^f_0$;
- $Y_{\ell}=\delta^f_{\ell}-\delta^c_{\ell-1}$ for $\ell\ge1$.

**Assessment.**
- **Truth: true.**
  - For $\ell=0$: `2^0 - 1 = 0` Milstein steps, so $M^f=s_0$ and $\delta^f_0$ is the constant $\varphi\big((s_0(1+rT)-K)/(|\sigma s_0|\sqrt T)\big)K/(s_0|\sigma s_0|\sqrt T)$. Its variance is 0, confirmed numerically.
  - For $\ell\ge1$: this is Thm 4 at $\ell-1$, with $T/2^{\ell}$ the same step size.
- **Vacuity: none.**
- **Junk values: none.** $L^2$ is asserted, and ℕ-subtraction `2^ℓ - 1` is exact since $2^\ell\ge1$.
- **Hypotheses.** Same remarks as Thm 4.

**Standard fact.** This is the MLMC level-variance hypothesis $V_\ell\le c\,h_\ell^\beta$ with $\beta<1/2$ for the digital delta, as above.
