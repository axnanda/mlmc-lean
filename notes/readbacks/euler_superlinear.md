# Blind read-back report: R8, Euler-Maruyama divergence for the cubic drift

| field | value |
|---|---|
| date | 2026-10-07 |
| packet | `readback/round15/packet_R8_euler_superlinear.lean` |
| declarations audited | 9 theorems (plus 4 definitions: `emPath`, `eulerDriftStep`, `tamedDriftStep`, `tamedPath`, rendered below) |
| auditor | independent blind auditor (sub-agent) |
| scripts directory | `readback/round15/work_R8/` (`s1_threshold54`, `s2_noise_growth`, `s3_gauss_bounds`, `s4_lower_bound`, `s5_tamed` `.py`/`.out`; `Scratch.lean`/`Scratch.out` is a scratch elaboration of the packet against Mathlib only) |

The scratch file `Scratch.lean` copies the packet into a fresh namespace with targeted Mathlib imports. It compiles with only the expected `sorry` warnings. It also checks the following in Lean, with proofs:
- `emPath` with $a(S,t)=-S^3$ and $b\equiv1$ unfolds to $X_{i+1}=X_i-hX_i^3+\sqrt h\,z_i$.
- `tamedDriftStep (-S^3) h S` $=S-hS^3/(1+h|S|^3)$.
- $T/(0:\mathbb N)=0$.
- `iIndepFun` over the empty family `Fin 0` forces `IsProbabilityMeasure μ`.
- **Non-vacuity:** there exist $\Omega,\mu,Z$ with `μ.map (Z N n) = gaussianReal 0 1` for all $n<N$ and `iIndepFun (fun n : Fin N => Z N n) μ` for every $N$. The witness is $\Omega=\mathbb R^{\mathbb N}$, $\mu=$ `infinitePi` of $N(0,1)$, and $Z_{N,n}(\omega)=\omega_n$.

## Summary verdict

| # | declaration | kind | truth | vacuous? | holds only because of a junk value? |
|---|---|---|---|---|---|
| 1 | `eulerCubic_noise_growth` | theorem | true | no | no |
| 2 | `le_gaussianReal_real_Icc` | theorem | true | no | no (when $b<a$ the left side is negative, which is genuine and not junk) |
| 3 | `le_gaussianReal_real_Ici` | theorem | true | no | no |
| 4 | `emCubic_moment_ge` | theorem | true | no | no (a junk zero integral would make it false; the integrand is integrable) |
| 5 | `emCubic_moment_tendsto_atTop` | theorem | true | no | no |
| 6 | `emCubic_integral_abs_tendsto_atTop` | theorem | true | no | no |
| 7 | `tamedPath_integral_abs_le` | theorem | true | no | no (integrability is proved in the first conjunct) |
| 8 | `tamedCubic_nonexpansive_iff` | theorem | true (threshold 54 exact) | no | no |
| 9 | `tamedCubic_second_moment_le` | theorem | true | no | no (`MemLp 2` is proved in the first conjunct) |

## Main points for a human auditor

- **The recursion is right.** `emPath (fun S _ => -S^3) (fun _ _ => 1) (T/N) x₀ z` is exactly $X_{i+1}=X_i-hX_i^3+\sqrt h\,z_i$ with $h=T/N$ (checked in Lean). `eulerDriftStep (fun S => -S^3) h x = x - h x^3`. The tamed step is $S-hS^3/(1+h|S|^3)$, the Hutzenthaler–Jentzen–Kloeden (HJK 2012) tamed Euler step.
- **The Gaussian hypotheses can hold (proved in Lean) and are what the proofs need.**
  - `μ.map (Z n) = gaussianReal 0 1` forces AE-measurability of `Z n`, because `Measure.map` of a non-AE-measurable map is $0$. It also forces $\mu(\Omega)=1$ as soon as $N\ge1$. `iIndepFun` forces $\mu(\Omega)=1$ even when $N=0$.
  - In the limit theorems there is no coupling across $N$. That is correct, because $\mathbb E|X^{(N)}_N|^p$ depends only on the joint law of $(Z_{N,0},\dots,Z_{N,N-1})$, which the hypotheses determine as i.i.d. $N(0,1)$.
- **There are no junk integrals.**
  - In #4–#6 a junk value $0$ would make the statement *false*, since the lower bound is $>0$ and the limit is $+\infty$. The integrand is genuinely integrable: $X_N$ is a polynomial in Gaussians, so all moments are finite.
  - In #7 and #9 a junk $0$ would make the upper bound trivially true, but each statement proves integrability (`Integrable` and `MemLp 2` respectively) as a conjunct.
- **$T/N$ at $N=0$ and $N-1$ do no harm.**
  - In #4, $0<T\le N$ forces $N\ge1$.
  - In #5 and #6 the $N=0$ term is irrelevant to the limit.
  - In #7 and #9, at $N=0$ the path is just $x_0$, independent of $h=T/0=0$, and #9 then forces $T=0$.
- **The lower bound in #4 holds and eventually grows (s4).** It equals $\bar\Phi(cN/T)\,P(|Z|\le1)^{N-1}\,2^{p2^{N-1}}$ with $c=2+|x_0|+|x_0|^3$.
  - It is astronomically small for small $N$, for example $10^{-47065}$ at $N=16$ for $T=1,x_0=3,p=1$.
  - Its minimum always comes before $N\approx25$ in the cases tried. It then increases monotonically and doubly exponentially. For example $\log_{10}L(40)\approx1.65\times10^{11}$ for $p=1$ in every case tried.
  - It lies below the exact quadrature value of $\mathbb E|X_N|^p$ for $N=1,2$.
  - Monte Carlo cannot see the blow-up: the MC mean of $|X_{12}|$ is about $0.57$, while the bound is $10^{488}$. The moments are carried by events of probability around $10^{-70}$ or smaller.
- **The threshold 54 in #8 is exact (sympy).** $|f(S)|\le|S|\iff 2+hS^2(2S-1)\ge0$, whose minimum over $S>0$ is $2-h/27$, attained at $S=1/3$. At $h=54$ the expression factors as $2(3S-1)^2(6S+1)$. For $h>54$, $f(1/3)<-1/3$. The hypothesis `0 ≤ h` is needed: for $h=-1$, $S=1/2$ the step gives $0.643>0.5$, while $h\le54$ holds.
- **The hypothesis $T\le54N$ in #9 is necessary for $N=1$ but apparently not for $N\ge2$.**
  - For $N=1$ it is exactly necessary. With $T=100$ and $x_0=1/3$: $\mathbb E X_1^2=f(1/3)^2+T=100.206>x_0^2+T=100.111$.
  - For $N=2$ and $N=3$ with $h>54$, quadrature finds no violation; the margin is $-10$ or below. So it is a clean sufficient step-size condition ($h\le54$), and it only restricts the coarse levels $N<T/54$.
- **#7 is a weak bound.** $\mathbb E|X_N|\le\max(|x_0|,1)+\sqrt{TN}$ grows with $N$, so it is *not* the uniform-in-$N$ moment bound of HJK 2012. No independence is assumed, and without independence the $\sqrt{TN}$ rate is attained: take $b=0$ and $Z_n\equiv Z_0$. The uniform contrast with Euler comes from #9 ($\mathbb E X_N^2\le x_0^2+T$).
- **#5 and #6 are slightly stronger than HJK 2011.** They give divergence for every $p>0$, while HJK state $p\ge1$. This is still true, via #4.

---

## Definitions (rendering only)

**`emPath a b h S₀ z`.** Given $X_0=S_0$, it computes $X_{i+1}=X_i+a(X_i,ih)\,h+b(X_i,ih)\sqrt h\,z_i$, where `Real.sqrt` gives $\sqrt h=0$ for $h<0$. In this packet $a(S,t)=-S^3$, $b\equiv1$ and $h=T/N$. So $X_{i+1}=X_i-hX_i^3+\sqrt h\,z_i$, which is the explicit Euler–Maruyama scheme for $dS=-S^3dt+dW$ (verified in Lean). $X_N$ depends only on $z_0,\dots,z_{N-1}$.

**`eulerDriftStep b h S`** $=S+h\,b(S)$.

**`tamedDriftStep b h S`** $=S+\dfrac{h\,b(S)}{1+h|b(S)|}$. For $h\ge0$ the denominator is $\ge1$, so there is no division by zero. This is the HJK (2012) tamed drift increment, whose magnitude is $<1$.

**`tamedPath b h x₀ z`.** It computes $Y_0=x_0$ and $Y_{n+1}=\texttt{tamedDriftStep}\,b\,h\,Y_n+\sqrt h\,z_n$.

---

## 1. `eulerCubic_noise_growth`

**Rendering.** Let $h\in\mathbb R$, $x,w:\mathbb N\to\mathbb R$ and $n\in\mathbb N$. Assume three things:
- $x_{k+1}=x_k-h x_k^3+w_k$ for all $k<n$;
- $4\le h x_0^2$;
- $h w_k^2\le1$ for all $k<n$.

Then $(h x_0^2)^{2^n}\le h x_n^2$. Here $2^n\in\mathbb N$ is a monoid power, as `pp.numericTypes` confirms.

**Assessment.**
- **Truth: true.** The hypothesis $h x_0^2\ge4$ forces $h>0$. Put $a_k=hx_k^2$ and $s=\sqrt{a_k}\ge2$. Then
  $$\sqrt h|x_{k+1}|\ \ge\ \sqrt h|x_k|\,|1-hx_k^2|-\sqrt h|w_k|\ \ge\ s(s^2-1)-1.$$
  This is $\ge s^2$ because $s^3-s^2-s-1\ge0$ for $s\ge2$: the polynomial equals $1$ at $s=2$, is increasing there, and its real root is $1.839$. So $a_{k+1}\ge a_k^2\ge16$, and by induction $a_n\ge a_0^{2^n}$. The case $n=0$ is equality.
- **Checks (s2).** Exact rational tests with adversarial, random and zero noise: 3000 cases, 0 violations.
- **Non-vacuity.** $h=1$, $x_0=2$, $w\equiv0$ or $w_k=\mp1$.
- **Junk values.** None.
- **Hypotheses.** Natural. In the application $w_k=\sqrt h Z_k$, so $hw_k^2=h^2Z_k^2\le1$ when $h\le1$ and $|Z_k|\le1$.
- **Standard fact.** The deterministic doubly exponential growth step in the proof of Hutzenthaler–Jentzen–Kloeden (2011, Proc. R. Soc. A, divergence of Euler's method).

## 2. `le_gaussianReal_real_Icc`

**Rendering.** For all real $a,b$:
$$(b-a)\,\frac{e^{-\max(a^2,b^2)/2}}{\sqrt{2\pi}}\ \le\ P(a\le Z\le b),\qquad Z\sim N(0,1).$$
`(gaussianReal 0 1).real` is the real-valued measure.

**Assessment.**
- **Truth: true.**
  - If $b<a$, the left side is $<0$ and the right side is $0$, because the interval is empty.
  - If $a\le b$, every $x\in[a,b]$ has $x^2\le\max(a^2,b^2)$, so the density is at least the stated constant on $[a,b]$.
- **Checks (s3).** An $81\times81$ grid gave 0 violations; the maximum ratio of left side to right side was $0.979$.
- **Non-vacuity.** It holds for all $a,b$; for example $a=-1,b=1$ gives $0.484\le0.683$.
- **Junk values.** None. The negative left side for $b<a$ is a genuine value.
- **Standard fact.** The elementary bound "mass is at least length times the minimum of the density".

## 3. `le_gaussianReal_real_Ici`

**Rendering.** For all real $x$: $\dfrac{e^{-(|x|+1)^2/2}}{\sqrt{2\pi}}\le P(Z\ge x)$, with $Z\sim N(0,1)$. The expression parses as $(-(|x|+1)^2)/2$.

**Assessment.**
- **Truth: true.** Apply #2 on $[x,x+1]$, using $\max(x^2,(x+1)^2)\le(|x|+1)^2$.
- **Checks (s3).** The grid $x\in[-20,20]$ gave 0 violations. The bound is crude: at $x=100$ the gap is $e^{96}$.
- **Non-vacuity.** It holds for all $x$.
- **Junk values.** None.
- **Standard fact.** A crude Gaussian tail lower bound, weaker than the Mills-ratio bound.

## 4. `emCubic_moment_ge`

**Rendering.** Let $(\Omega,\mu)$ be a measure space; it is not assumed to be a probability space, but the hypotheses force that. Let $x_0\in\mathbb R$, $T>0$, $p\ge0$ real, and $N\in\mathbb N$ with $T\le N$, so $N\ge1$ and $h=T/N\in(0,1]$. Let $Z:\mathbb N\to\Omega\to\mathbb R$ satisfy:
- `μ.map (Z n) = N(0,1)` for $n<N$;
- $(Z_n)_{n<N}$ is mutually independent.

Let $X_N$ be the cubic Euler path driven by $Z_n(\omega)$. Then
$$\bar\Phi\!\Big(\tfrac{(2+|x_0|+|x_0|^3)N}{T}\Big)\cdot P(|Z|\le1)^{N-1}\cdot\big(2^{2^{N-1}}\big)^p\ \le\ \int|X_N|^p\,d\mu .$$
Here $\bar\Phi(y)=P(Z\ge y)$, the power $N-1$ is a natural-number power, and the outer power $^p$ and $|\cdot|^p$ are `Real.rpow`.

**Assessment.**
- **Truth: true.** Let $c=2+|x_0|+|x_0|^3$. Consider the event
  $$E=\{Z_0\ge cN/T=c/h\}\cap\bigcap_{1\le k<N}\{|Z_k|\le1\}.$$
  - On $E$: $\sqrt hX_1\ge c-\sqrt h|x_0|-h^{3/2}|x_0|^3\ge c-|x_0|-|x_0|^3=2$, using $h\le1$. So $hX_1^2\ge4$.
  - With $w_k=\sqrt hZ_k$ we have $hw_k^2=h^2Z_k^2\le1$. Lemma #1, applied from step 1, gives $hX_N^2\ge4^{2^{N-1}}$, hence $|X_N|\ge2^{2^{N-1}}/\sqrt h\ge2^{2^{N-1}}$.
  - Independence gives $\mu(E)=\bar\Phi(c/h)\,P(|Z|\le1)^{N-1}$.
  - The integrand is nonnegative and integrable, because $X_N$ is a polynomial in $Z_0,\dots,Z_{N-1}$ and Gaussians have all moments. So $\int|X_N|^p\ge\mu(E)\,2^{p2^{N-1}}$.
- **Checks (s4).**
  - Pathwise: on sampled points of $E$ (400 trials, $N$ up to 22), $\log_2|X_N|-2^{N-1}\ge0$, with equality in the boundary case $T=1,x_0=0,N=1$.
  - Exact quadrature for $N=1,2$ confirms left side $\le$ right side; for example $0.0455\le0.798$ and $8.6\times10^{-5}\le0.660$.
  - The bound eventually grows. Over $T\in\{0.1,1,2,10\}$, $x_0\in\{0,1,3\}$ and $p\in\{0.5,1,2\}$, $\log_{10}L(N)$ reaches its minimum by $N\le24$, increases monotonically afterwards, exceeds $1$ by $N\le28$, and is about $1.65\times10^{11}\,p$ at $N=40$.
  - Monte Carlo with 20000 paths gives $\mathbb E|X_N|\approx0.57$ for $N=3$–$12$ with $T=1$, $x_0=0$. Typical paths are stable, and the moment is carried by events MC cannot sample. This is consistent with a lower bound of $10^{488}$ at $N=12$.
- **Non-vacuity.** The `infinitePi` witness (proved in Lean), with $T=1$, $N=1$, any $x_0$ and $p$.
- **Junk values.** None that help. $N-1$ is safe because $N\ge1$. A junk value $\int=0$ would contradict the statement, since the left side is $>0$. With $p=0$ both sides are $\le1=\mu(\Omega)$, which is fine.
- **Hypotheses.** Exactly the natural ones; only the laws and independence of $Z_0,\dots,Z_{N-1}$ are used. $T\le N$ means $h\le1$.
- **Standard fact.** The quantitative lower bound behind the HJK (2011) divergence theorem: $\mathbb E|Y_N|^p\ge P(\Omega_N)\cdot2^{p2^{N-1}}$, where the probability of the bad event decays only like $e^{-O(N^2)}$.

## 5. `emCubic_moment_tendsto_atTop`

**Rendering.** Let $(\Omega,\mu)$, $x_0$, $T>0$ and $p>0$ be given, and let $Z:\mathbb N\to\mathbb N\to\Omega\to\mathbb R$, a separate noise array for each $N$, satisfy for every $N$:
- `μ.map (Z N n) = N(0,1)` for $n<N$;
- $(Z_{N,n})_{n<N}$ is independent.

No relation across different $N$ is assumed. Then $N\mapsto\int|X^{(N)}_N|^p\,d\mu\to+\infty$, where $X^{(N)}$ is the cubic EM path with $h=T/N$ driven by $Z_{N,\cdot}$.

**Assessment.**
- **Truth: true.** For $N\ge T$, #4 applies with $Z=Z_{N,\cdot}$. Using #3, the log of the lower bound is at least
  $$-\tfrac12\big(cN/T+1\big)^2-\log\sqrt{2\pi}+(N-1)\log0.6827+p\,2^{N-1}\log2,$$
  which tends to $+\infty$ because $p>0$. The values $N<T$ and the junk value $T/0$ at $N=0$ do not affect the limit.
- **Non-vacuity.** The Lean witness above satisfies `hZ` and `hind` for all $N$ simultaneously.
- **Junk values.** None. A non-integrable junk $0$ would falsify the statement, and the integrands are integrable.
- **Hypotheses.** Correct and minimal. The integral depends only on the law of $(Z_{N,0..N-1})$, so no coupling across $N$ is needed. `hind` at $N=0$ forces $\mu$ to be a probability measure, which is harmless. $p>0$ is needed; at $p=0$ the integral is constantly $1$.
- **Standard fact.** Hutzenthaler–Jentzen–Kloeden (2011), Proc. R. Soc. A 467: for superlinearly growing drift, $\lim_N\mathbb E|Y^N_N|^p=\infty$. This version covers every $p>0$, slightly more than the $p\ge1$ in their statement.

## 6. `emCubic_integral_abs_tendsto_atTop`

**Rendering.** The same as #5 with $p=1$ and the plain absolute value: $\int|X^{(N)}_N|\,d\mu\to+\infty$.

**Assessment.**
- **Truth: true.** It is #5 with $p=1$, since $|x|^{1}=|x|$ for `rpow`. Alternatively, apply #4 directly.
- **Non-vacuity.** The same witness.
- **Junk values.** None, by the same reasoning as #5.
- **Standard fact.** The HJK (2011) strong divergence of $\mathbb E|Y_N|$, which implies that the explicit Euler scheme is not $L^1$-convergent.

## 7. `tamedPath_integral_abs_le`

**Rendering.** Let $(\Omega,\mu)$ be a **probability** space. Let $b:\mathbb R\to\mathbb R$ be measurable with $S\,b(S)\le0$ for all $S$. Take $x_0$, $T\ge0$, $N\in\mathbb N$, and $Z:\mathbb N\to\Omega\to\mathbb R$ with `μ.map (Z n) = N(0,1)` for $n<N$; **no independence is assumed**. Let $Y_N$ be the tamed path with $h=T/N$. Then $Y_N$ is integrable and
$$\int|Y_N|\,d\mu\le\max(|x_0|,1)+\sqrt{TN}.$$

**Assessment.**
- **Truth: true.**
  - If $Sb(S)\le0$, the tamed increment $d=hb/(1+h|b|)$ has $|d|<1$ and sign opposite to $S$. Therefore $|S+d|\le\max(|S|,1)$; when $S=0$, $b(0)$ is arbitrary but $|d|<1$.
  - With $M_n=\max(|Y_n|,1)$ this gives $M_{n+1}\le M_n+\sqrt h|Z_n|$, so $|Y_N|\le\max(|x_0|,1)+\sqrt h\sum_{n<N}|Z_n|$.
  - Taking expectations: $\mathbb E|Y_N|\le\max(|x_0|,1)+\sqrt{T/N}\cdot N\sqrt{2/\pi}\le\max(|x_0|,1)+\sqrt{TN}$.
  - Measurability holds because $b$ is measurable and each $Z_n$ is AE-measurable, the latter forced by `map`.
- **Checks (s5).** The pathwise inequality held in 200000 random cases with 0 violations. Monte Carlo is below the bound in every case.
- **Non-vacuity.** $b(S)=-S^3$ with the `infinitePi` witness.
- **$N=0$.** $h=T/0=0$, but $Y_0=x_0$, so the statement reads $|x_0|\le\max(|x_0|,1)$. It is true, and junk-independent because $\mu$ is a probability measure.
- **Junk values.** None. Integrability is proved, so the integral is genuine. The `IsProbabilityMeasure` instance is needed only for $N=0$.
- **Hypotheses and caveat.** The bound is **not uniform in $N$**. Without independence the $\sqrt{TN}$ order is attained: with $b\equiv0$ and $Z_n\equiv Z_0$, $\mathbb E|Y_N|=\sqrt{2/\pi}\sqrt{TN}$ when $x_0=0$. So this is a finiteness and polynomial-growth statement, weaker than the uniform moment bounds of HJK (2012). It contrasts with Euler's doubly exponential growth, but does not show boundedness.
- **Standard fact.** The elementary "bounded drift increment" property of the tamed Euler scheme of Hutzenthaler–Jentzen–Kloeden (2012, Ann. Appl. Probab. 22).

## 8. `tamedCubic_nonexpansive_iff`

**Rendering.** For real $h\ge0$, the following are equivalent:
- $\Big|S-\dfrac{hS^3}{1+h|S|^3}\Big|\le|S|$ for all $S\in\mathbb R$;
- $h\le54$.

**Assessment.**
- **Truth: true, and the threshold is exact (s1, sympy).** The map $f$ is odd with $f(0)=0$. For $S>0$, $f(S)\le S$ holds trivially, and
  $$f(S)\ge-S\iff g(S):=2+2hS^3-hS^2\ge0.$$
  The only critical point of $g$ in $S>0$ is $S=1/3$, where $g(1/3)=2-h/27$. Hence the condition holds for all $S$ iff $h\le54$.
  - At $h=54$: $g=2(3S-1)^2(6S+1)$ and $f(1/3)=-1/3$, so the inequality is tight.
  - In general $f(1/3)+1/3=(54-h)/(3(h+27))$, which is $<0$ for $h>54$.
- **Checks.** 200000 exact rational samples with $h\in[0,54]$ gave 0 violations.
- **Non-vacuity.** $h=1$ satisfies both sides; $h=100$ falsifies both.
- **Junk values.** None; the denominator is $\ge1$.
- **Hypotheses.** `hh0` is necessary: for $h=-1$, $S=1/2$ the step gives $0.643>0.5$, while $h\le54$ is true, so the equivalence would fail.
- **Standard fact.** An elementary calculus fact specific to the cubic tamed step. It is not a named literature result.

## 9. `tamedCubic_second_moment_le`

**Rendering.** Let $(\Omega,\mu)$ be a measure space; the hypotheses force a probability space. Let $x_0\in\mathbb R$, $T\ge0$, and $N$ with $T\le54N$, which means $h=T/N\le54$. Let $Z$ satisfy:
- `μ.map (Z n) = N(0,1)` for $n<N$;
- $(Z_n)_{n<N}$ is independent.

Let $Y_N$ be the tamed path for $b(S)=-S^3$. Then $Y_N\in L^2(\mu)$ and
$$\int Y_N^2\,d\mu\le x_0^2+T.$$

**Assessment.**
- **Truth: true.**
  - By #8, $|f(Y_n)|\le|Y_n|$.
  - $Y_n$ is a function of $Z_0,\dots,Z_{n-1}$, which is independent of $Z_n$, and $\mathbb E Z_n=0$. Hence
    $$\mathbb EY_{n+1}^2=\mathbb Ef(Y_n)^2+2\sqrt h\,\mathbb E[f(Y_n)]\,\mathbb E[Z_n]+h\le\mathbb EY_n^2+h.$$
  - Summing gives $\mathbb EY_N^2\le x_0^2+Nh=x_0^2+T$.
  - $L^2$ membership: $|Y_N|\le|x_0|+\sqrt h\sum|Z_n|$.
  - For $N=0$, the hypotheses force $T=0$ and `hind` forces $\mu(\Omega)=1$, so the claim is $x_0^2\le x_0^2$.
- **Checks (s5).** Monte Carlo is below the bound in every case. At $N=1$, $T=54$, $x_0=1/3$ the bound is attained with equality: $54.1111$.
- **Non-vacuity.** The `infinitePi` witness with $T=1$, $N=1$.
- **Junk values.** None. `MemLp 2` is proved, so $\int Y_N^2$ is genuine. Without that conjunct, a junk zero would have made the bound trivial.
- **Hypotheses.**
  - **Is $T\le54N$ needed? For $N=1$, exactly.** $\mathbb EY_1^2=f(x_0)^2+T\le x_0^2+T$ holds for all $x_0$ iff $T=h\le54$. Counterexample: $T=100$, $x_0=1/3$ gives $100.206>100.111$.
  - For $N\ge2$ it appears unnecessary. Exact quadrature for $N=2$ with $h\in\{54.5,60,100,10^3,10^5\}$ over $x_0\in[-3,3]$, and for $N=3$ with $h\in\{60,1000\}$, gives $\mathbb EY_N^2-(x_0^2+T)\le-10.8$. The reason: after the first step the noise has standard deviation $\ge7$, and the drift then removes much more than the gain of at most 1 from the first step.
  - So the hypothesis is a clean sufficient step-size condition (step-wise non-expansiveness). It only restricts coarse levels $N<T/54$, and it is necessary when $N=1$.
  - Independence is genuinely needed. With fully dependent noise $Z_n\equiv Z_0$, small $T$ and large $N$, we get $\mathbb EY_N^2\approx TN\gg T$.
- **Standard fact.** A uniform-in-$N$ second-moment bound for the tamed Euler scheme of HJK (2012). It is proved here by a simple step-wise contraction argument for the cubic drift with additive noise, and it is the real contrast with the Euler divergence in #5 and #6.
