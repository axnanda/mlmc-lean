## singleTerm_unbiased

**Setting.** $(\Omega,\mathcal F)$ is an arbitrary measurable space (a set with a σ-algebra) and $\mu$ is a probability measure on it, $\mu(\Omega)=1$. The natural numbers $\mathbb N=\{0,1,2,\dots\}$ carry the discrete σ-algebra (every subset is measurable) and $\mathbb R$ carries the Borel σ-algebra. The statement is about arbitrary

- a function $K:\Omega\to\mathbb N$,
- a sequence of functions $P_0,P_1,P_2,\dots:\Omega\to\mathbb R$,
- a sequence of real numbers $p_0,p_1,p_2,\dots$,
- a function $P:\Omega\to\mathbb R$. Nothing is assumed about $P$ (neither measurability nor integrability) apart from its appearance in hypothesis 8.

Integrals $\int_\Omega f\,d\mu$ are Bochner integrals: they equal the usual Lebesgue integral when $f$ is $\mu$-integrable and are defined to be $0$ when it is not.

**Objects built from these (definitions expanded).** The level differences are, pointwise on $\Omega$,
$$\Delta_0:=P_0,\qquad \Delta_\ell:=P_\ell-P_{\ell-1}\quad(\ell\ge 1),$$
and $Z:\Omega\to\mathbb R$ is
$$Z(\omega):=\big(p_{K(\omega)}\big)^{-1}\,\Delta_{K(\omega)}(\omega),$$
where the reciprocal follows the convention $0^{-1}=0$ (so $Z(\omega)=0$ whenever $p_{K(\omega)}=0$; hypothesis 5 rules this case out).

**Hypotheses.**

1. $K$ is measurable, i.e. every level set $\{K=\ell\}$ belongs to $\mathcal F$.
2. Every $P_\ell$ is Borel measurable.
3. Every $P_\ell$ is $\mu$-integrable ($\int_\Omega|P_\ell|\,d\mu<\infty$).
4. For every $\ell\in\mathbb N$: $\mu(\{\omega : K(\omega)=\ell\})=p_\ell$.
5. For every $\ell\in\mathbb N$: $p_\ell>0$. Together with 4 this says that $K$ takes **every** value $\ell\in\mathbb N$ with strictly positive probability.
6. For every $\ell\in\mathbb N$, the functions $K$ and $\Delta_\ell$ are independent under $\mu$: $\mu(K\in A,\ \Delta_\ell\in B)=\mu(K\in A)\,\mu(\Delta_\ell\in B)$ for all $A\subseteq\mathbb N$ and all Borel $B\subseteq\mathbb R$. This is required for each single $\Delta_\ell$ separately; independence of $K$ from the whole sequence $(\Delta_\ell)_{\ell}$ jointly is not assumed.
7. The family $\big(\int_\Omega|\Delta_\ell|\,d\mu\big)_{\ell\in\mathbb N}$ is summable, i.e. $\sum_{\ell=0}^{\infty}\int_\Omega|\Delta_\ell|\,d\mu<\infty$.
8. $\displaystyle\lim_{L\to\infty}\int_\Omega P_L\,d\mu=\int_\Omega P\,d\mu$, with $L$ running through $\mathbb N$.

**Conclusion.** Both of the following hold:
$$Z\ \text{is }\mu\text{-integrable}\qquad\text{and}\qquad\int_\Omega Z\,d\mu=\int_\Omega P\,d\mu .$$

**Edge cases.** Since $P$ is constrained only by hypothesis 8, it may be non-integrable. In that case $\int_\Omega P\,d\mu$ takes the conventional value $0$, hypothesis 8 reads $\int_\Omega P_L\,d\mu\to 0$, and the conclusion reads $\int_\Omega Z\,d\mu=0$. The integrals $\int_\Omega P_L\,d\mu$ and $\int_\Omega|\Delta_\ell|\,d\mu$ are genuine because of hypothesis 3, and because of hypothesis 5 the convention $0^{-1}=0$ in $Z$ never applies.

## singleTerm_variance

**Setting.** $(\Omega,\mathcal F)$ is an arbitrary measurable space and $\mu$ is a probability measure on it, $\mu(\Omega)=1$. $\mathbb N$ carries the discrete σ-algebra and $\mathbb R$ the Borel σ-algebra. The statement is about arbitrary

- a function $K:\Omega\to\mathbb N$,
- a sequence of functions $P_0,P_1,P_2,\dots:\Omega\to\mathbb R$,
- a sequence of real numbers $p_0,p_1,p_2,\dots$.

Write $\mathbb E[f]:=\int_\Omega f\,d\mu$ (Bochner integral, $0$ by convention if $f$ is not integrable) and $\operatorname{Var}(f)$ for the variance $\int_\Omega\big(f-\mathbb E[f]\big)^2\,d\mu$. Every function whose variance appears below is square-integrable ($\Delta_\ell$ by hypothesis 3, $Z$ by the first part of the conclusion), so these are genuine variances.

**Objects built from these (definitions expanded).** Pointwise on $\Omega$,
$$\Delta_0:=P_0,\qquad \Delta_\ell:=P_\ell-P_{\ell-1}\quad(\ell\ge 1),\qquad Z(\omega):=\big(p_{K(\omega)}\big)^{-1}\,\Delta_{K(\omega)}(\omega),$$
with the convention $0^{-1}=0$ in $Z$. Hypothesis 5 means this convention is never used.

**Hypotheses.**

1. $K$ is measurable (every level set $\{K=\ell\}$ is in $\mathcal F$).
2. Every $P_\ell$ is Borel measurable.
3. Every $P_\ell$ is in $L^2(\mu)$: almost-everywhere measurable with $\int_\Omega P_\ell^2\,d\mu<\infty$.
4. For every $\ell\in\mathbb N$: $\mu(\{\omega: K(\omega)=\ell\})=p_\ell$.
5. For every $\ell\in\mathbb N$: $p_\ell>0$, so $K$ takes every value in $\mathbb N$ with strictly positive probability.
6. For every $\ell\in\mathbb N$, $K$ and $\Delta_\ell$ are independent under $\mu$ ($\mu(K\in A,\ \Delta_\ell\in B)=\mu(K\in A)\,\mu(\Delta_\ell\in B)$ for all $A\subseteq\mathbb N$ and Borel $B\subseteq\mathbb R$). This is required for each $\ell$ separately; joint independence of $K$ from the whole sequence is not assumed.
7. The family $\big(\mathbb E[\Delta_\ell^2]/p_\ell\big)_{\ell\in\mathbb N}$ is summable: $\sum_{\ell=0}^{\infty}\mathbb E[\Delta_\ell^2]/p_\ell<\infty$.

**Conclusion.** $Z\in L^2(\mu)$ (i.e. $Z$ is a.e. measurable and $\int_\Omega Z^2\,d\mu<\infty$), and
$$\operatorname{Var}(Z)=\left(\sum_{\ell=0}^{\infty}\frac{\operatorname{Var}(\Delta_\ell)+\big(\mathbb E[\Delta_\ell]\big)^2}{p_\ell}\right)-\left(\sum_{\ell=0}^{\infty}\mathbb E[\Delta_\ell]\right)^{2}.$$
The subtraction sits outside the first infinite sum.

**Edge cases.** Each $\sum_{\ell=0}^{\infty}$ above is the sum of the family when it is summable (for real families this means absolutely convergent) and is defined to be $0$ when it is not. The statement does not separately assume either family summable. For the record: for square-integrable $\Delta_\ell$ one has $\operatorname{Var}(\Delta_\ell)+(\mathbb E[\Delta_\ell])^2=\mathbb E[\Delta_\ell^2]$, so the first family has exactly the terms of hypothesis 7. The second family is absolutely summable under hypotheses 4, 5 and 7, because $|\mathbb E[\Delta_\ell]|\le\mathbb E[\Delta_\ell^2]^{1/2}\le\tfrac12\big(\mathbb E[\Delta_\ell^2]/p_\ell+p_\ell\big)$ and $\sum_\ell p_\ell=\mu(\Omega)=1$. So the value $0$ is not substituted for either sum. The divisions by $p_\ell$ are genuine (hypothesis 5).

## randomised_summable

**Setting.** This is a statement about real numbers and real sequences only. The probability-space objects available in the surrounding context (a measurable space, a probability measure, a random index, level functions, a probability sequence) are not mentioned in it and are not part of it. It is about arbitrary

- real numbers $\beta,\gamma,c_2,c_3$,
- real sequences $(V_\ell)_{\ell\in\mathbb N}$ and $(C_\ell)_{\ell\in\mathbb N}$.

**Object built from these (definition expanded).** With the real power $r:=2^{-(\beta+\gamma)/2}$, define for $\ell\in\mathbb N$
$$q_\ell:=(1-r)\,r^{\ell}=\Big(1-2^{-(\beta+\gamma)/2}\Big)\Big(2^{-(\beta+\gamma)/2}\Big)^{\ell}.$$

**Hypotheses.**

1. $0<\gamma$.
2. $\gamma<\beta$.
3. $V_\ell\ge 0$ for every $\ell\in\mathbb N$.
4. $C_\ell\ge 0$ for every $\ell\in\mathbb N$.
5. $V_\ell\le c_2\,2^{-\beta\ell}$ for every $\ell\in\mathbb N$ (real power).
6. $C_\ell\le c_3\,2^{\gamma\ell}$ for every $\ell\in\mathbb N$ (real power).

No sign is assumed for $c_2$ or $c_3$. Hypotheses 3 and 5 force $c_2\ge 0$, and hypotheses 4 and 6 force $c_3\ge 0$.

**Conclusion.** All four of the following hold:

- (a) $q_\ell>0$ for every $\ell\in\mathbb N$;
- (b) the series $\sum_{\ell=0}^{\infty}q_\ell$ converges and its sum is exactly $1$;
- (c) the family $\big(V_\ell/q_\ell\big)_{\ell\in\mathbb N}$ is summable, i.e. $\sum_{\ell=0}^{\infty}V_\ell/q_\ell$ converges;
- (d) the family $\big(q_\ell\,C_\ell\big)_{\ell\in\mathbb N}$ is summable, i.e. $\sum_{\ell=0}^{\infty}q_\ell\,C_\ell$ converges.

**Edge cases.** Division is real division with the convention $x/0=0$; part (a) asserts that no $q_\ell$ is $0$. Hypotheses 1–2 give $\beta+\gamma>0$, so $0<r<1$. For real families, summability means unconditional (equivalently absolute) convergence. Given the hypotheses and (a), all terms in (b)–(d) are nonnegative. Parts (c) and (d) assert only that the sums converge; no value or bound for them is stated.

## randomised_not_summable

**Setting.** This is a statement about real numbers and real sequences only. The probability-space objects of the surrounding context are not mentioned in it and are not part of it. In particular, the sequence $(p_\ell)$ below is a new, arbitrary real sequence that is not tied to any random variable. The statement is about arbitrary

- real numbers $\beta,\gamma,c_2,c_3$,
- real sequences $(V_\ell)_{\ell\in\mathbb N}$, $(C_\ell)_{\ell\in\mathbb N}$ and $(p_\ell)_{\ell\in\mathbb N}$.

**Hypotheses.**

1. $\beta\le\gamma$. Apart from this, $\beta$ and $\gamma$ are unrestricted; zero or negative values are allowed.
2. $c_2>0$.
3. $c_3>0$.
4. $p_\ell>0$ for every $\ell\in\mathbb N$. Nothing else is assumed about $p$: there is no normalisation $\sum_\ell p_\ell=1$ and no bound $p_\ell\le 1$.
5. $c_2\,2^{-\beta\ell}\le V_\ell$ for every $\ell\in\mathbb N$ (real power).
6. $c_3\,2^{\gamma\ell}\le C_\ell$ for every $\ell\in\mathbb N$ (real power).

**Conclusion.** It is **not** the case that both families $\big(V_\ell/p_\ell\big)_{\ell\in\mathbb N}$ and $\big(p_\ell\,C_\ell\big)_{\ell\in\mathbb N}$ are summable. Equivalently, at least one of the series
$$\sum_{\ell=0}^{\infty}\frac{V_\ell}{p_\ell},\qquad\sum_{\ell=0}^{\infty}p_\ell\,C_\ell$$
fails to converge. Under the hypotheses, every term of both series is strictly positive, so "not summable" means that the partial sums are unbounded.

## randomised_mlmc_finite

**Setting.** $(\Omega,\mathcal F)$ is an arbitrary measurable space and $\mu$ is a probability measure on it. The assumption $\mu(\Omega)=1$ appears twice, once from the surrounding context and once among the statement's own assumptions, with identical content. $\mathbb N$ carries the discrete σ-algebra and $\mathbb R$ the Borel σ-algebra. The statement declares its own $K$ and $P_\ell$; the surrounding context's random index, level functions and probability sequence are not used. It is about arbitrary

- a function $K:\Omega\to\mathbb N$,
- a sequence of functions $P_0,P_1,P_2,\dots:\Omega\to\mathbb R$,
- a function $P:\Omega\to\mathbb R$,
- a real sequence $(C_\ell)_{\ell\in\mathbb N}$,
- real numbers $\alpha,\beta,\gamma,c_1,c_2,c_3$.

Integrals are Bochner integrals: they are $0$ by convention for non-integrable integrands, but every integrand below is integrable under the hypotheses and the conclusion.

**Objects built from these (definitions expanded).**
$$r:=2^{-(\beta+\gamma)/2}\ \text{(real power)},\qquad q_\ell:=(1-r)\,r^{\ell}\quad(\ell\in\mathbb N),$$
$$\Delta_0:=P_0,\qquad\Delta_\ell:=P_\ell-P_{\ell-1}\ (\ell\ge1),\qquad Z(\omega):=\big(q_{K(\omega)}\big)^{-1}\,\Delta_{K(\omega)}(\omega),$$
with the convention $0^{-1}=0$ in $Z$. Hypotheses 2–3 give $\beta+\gamma>0$, so $0<r<1$ and every $q_\ell>0$; the convention is therefore never used.

**Hypotheses.**

1. $\alpha>0$.
2. $\gamma>0$.
3. $\gamma<\beta$.
4. $K$ is measurable (every level set $\{K=\ell\}$ is in $\mathcal F$).
5. Every $P_\ell$ is Borel measurable.
6. Every $P_\ell$ is in $L^2(\mu)$: a.e. measurable with $\int_\Omega P_\ell^2\,d\mu<\infty$.
7. $P$ is $\mu$-integrable.
8. For every $\ell\in\mathbb N$: $\mu(\{\omega: K(\omega)=\ell\})=q_\ell=(1-r)\,r^{\ell}$.
9. For every $\ell\in\mathbb N$, $K$ and $\Delta_\ell$ are independent under $\mu$. This is required for each $\ell$ separately; joint independence from the whole sequence is not assumed.
10. For every $\ell\in\mathbb N$: $\big|\int_\Omega (P_\ell-P)\,d\mu\big|\le c_1\,2^{-\alpha\ell}$.
11. For every $\ell\in\mathbb N$: $\int_\Omega\Delta_\ell^2\,d\mu\le c_2\,2^{-\beta\ell}$. This bounds the second moment of $\Delta_\ell$, not its variance.
12. $C_\ell\ge0$ for every $\ell\in\mathbb N$.
13. $C_\ell\le c_3\,2^{\gamma\ell}$ for every $\ell\in\mathbb N$.

All powers $2^{(\cdot)}$ are real powers. No sign is assumed for $c_1,c_2,c_3$; hypotheses 10, 11 and 12–13 (at $\ell=0$) force each of them to be $\ge 0$.

**Conclusion.** All four of the following hold:

- (a) $Z$ is $\mu$-integrable;
- (b) $\int_\Omega Z\,d\mu=\int_\Omega P\,d\mu$;
- (c) $Z\in L^2(\mu)$, i.e. $Z$ is a.e. measurable and $\int_\Omega Z^2\,d\mu<\infty$. No value or bound for this quantity is stated;
- (d) the family $\big(q_\ell\,C_\ell\big)_{\ell\in\mathbb N}$ is summable, i.e. $\sum_{\ell=0}^{\infty}q_\ell\,C_\ell$ converges.

**Remarks.** No hypothesis links the sequence $(C_\ell)$ to $\Omega$, $K$ or the $P_\ell$; part (d) involves only $C$, $\beta$ and $\gamma$. The parameters $\alpha$ and $c_1$ appear only in hypothesis 10.

## nested_cost_lower_bound

**Setting.** This is a deterministic inequality between real numbers; no probability space is involved. The statement is about arbitrary

- a natural number $L$,
- real sequences $(V^t_\ell)$, $(C^t_\ell)$, $(V^\Delta_\ell)$, $(C^\Delta_\ell)$, $(n^t_\ell)$, $(n^\Delta_\ell)$ indexed by $\ell\in\mathbb N$. In particular, $n^t_\ell$ and $n^\Delta_\ell$ are real numbers and are not required to be integers,
- a real number $\varepsilon$.

**Hypotheses.**

1. $\varepsilon>0$.
2. $V^t_\ell\ge0$, $V^\Delta_\ell\ge0$, $C^t_\ell\ge0$ and $C^\Delta_\ell\ge0$ for every $\ell\in\mathbb N$.
3. $n^t_\ell>0$ and $n^\Delta_\ell>0$ for every $\ell\in\mathbb N$.
4. $\displaystyle\sum_{\ell=0}^{L}\left(\frac{V^t_\ell}{n^t_\ell}+\frac{V^\Delta_\ell}{n^\Delta_\ell}\right)\le\varepsilon^2.$

**Conclusion.**
$$\frac{1}{\varepsilon^2}\left(\sum_{\ell=0}^{L}\Big(\sqrt{V^t_\ell\,C^t_\ell}+\sqrt{V^\Delta_\ell\,C^\Delta_\ell}\Big)\right)^{2}\ \le\ \sum_{\ell=0}^{L}\Big(n^t_\ell\,C^t_\ell+n^\Delta_\ell\,C^\Delta_\ell\Big).$$

**Edge cases.** All sums run over $\ell=0,1,\dots,L$, which is $L+1\ge1$ terms; $L=0$ gives the single term $\ell=0$. $\sqrt{\cdot}$ is the real square root, which returns $0$ on negative inputs, but its arguments here are nonnegative by hypothesis 2. $1/\varepsilon^2$ is the reciprocal of $\varepsilon^2$; the convention $0^{-1}=0$ is not triggered because $\varepsilon>0$. The divisions in hypothesis 4 are genuine by hypothesis 3. Hypotheses 2–3 are also imposed for $\ell>L$, although those indices do not enter either side.

## nested_optimal_allocation

**Setting.** This is a deterministic statement about real numbers; no probability space is involved. It is about arbitrary

- a natural number $L$,
- real sequences $(V^t_\ell)$, $(C^t_\ell)$, $(V^\Delta_\ell)$, $(C^\Delta_\ell)$ indexed by $\ell\in\mathbb N$,
- a real number $\varepsilon$.

**Hypotheses.**

1. $\varepsilon>0$.
2. $V^t_\ell>0$, $V^\Delta_\ell>0$, $C^t_\ell>0$ and $C^\Delta_\ell>0$ for every $\ell\in\mathbb N$ (strict positivity).

**Conclusion.** There exist two sequences of natural numbers $(N^t_\ell)_{\ell\in\mathbb N}$ and $(N^\Delta_\ell)_{\ell\in\mathbb N}$ such that all of the following hold:

- (a) $N^t_\ell\ge1$ for every $\ell\in\mathbb N$;
- (b) $N^\Delta_\ell\ge1$ for every $\ell\in\mathbb N$;
- (c) $\displaystyle\sum_{\ell=0}^{L}\left(\frac{V^t_\ell}{N^t_\ell}+\frac{V^\Delta_\ell}{N^\Delta_\ell}\right)\le\varepsilon^2$;
- (d) $\displaystyle\sum_{\ell=0}^{L}\Big(N^t_\ell\,C^t_\ell+N^\Delta_\ell\,C^\Delta_\ell\Big)\le\frac{1}{\varepsilon^2}\left(\sum_{\ell=0}^{L}\Big(\sqrt{V^t_\ell\,C^t_\ell}+\sqrt{V^\Delta_\ell\,C^\Delta_\ell}\Big)\right)^{2}+\sum_{\ell=0}^{L}\Big(C^t_\ell+C^\Delta_\ell\Big)$.

**Edge cases.** The $N$'s are natural numbers and are treated as real numbers in (c) and (d); by (a)–(b), the divisions in (c) are genuine. This is a pure existence statement: no formula for $N^t$ or $N^\Delta$ is given. All sums run over $\ell=0,\dots,L$, and $L=0$ is allowed. For $\ell>L$ the $N$'s are constrained only by (a)–(b), while hypothesis 2 is imposed for every $\ell\in\mathbb N$. $1/\varepsilon^2$ is a genuine reciprocal because $\varepsilon>0$, and the square roots have positive arguments.

## nested_mlmc_mse

**Setting.** $(\Omega,\mathcal F)$ is an arbitrary measurable space and $\mu$ is a probability measure on it, $\mu(\Omega)=1$. $\mathbb R$ carries the Borel σ-algebra. The statement is about arbitrary

- four sequences of functions $\Omega\to\mathbb R$ indexed by $\ell\in\mathbb N$: $(P_\ell)$, $(D^t_\ell)$, $(Y^t_\ell)$ and $(Y^\Delta_\ell)$,
- a natural number $L$,
- a real number $m$.

Write $\mathbb E[f]:=\int_\Omega f\,d\mu$ for the Bochner integral, which is $0$ by convention for non-integrable $f$ (this does not occur below). Write $\operatorname{Var}(f):=\int_\Omega(f-\mathbb E[f])^2\,d\mu$; it is applied here only to square-integrable functions, so it is a genuine variance.

**Objects built from these (definitions expanded).** The index set is $I_L:=\{0,1,\dots,L\}\times\{\mathsf{true},\mathsf{false}\}$, which has $2(L+1)$ elements. The family $(X_i)_{i\in I_L}$ is given by
$$X_{(\ell,\mathsf{true})}:=Y^t_\ell,\qquad X_{(\ell,\mathsf{false})}:=Y^\Delta_\ell .$$

**Hypotheses.**

1. $Y^t_\ell\in L^2(\mu)$ (a.e. measurable, $\int_\Omega (Y^t_\ell)^2\,d\mu<\infty$) for every $\ell\in\mathbb N$.
2. $Y^\Delta_\ell\in L^2(\mu)$ for every $\ell\in\mathbb N$.
3. $P_\ell$ is $\mu$-integrable for every $\ell\in\mathbb N$.
4. $D^t_\ell$ is $\mu$-integrable for every $\ell\in\mathbb N$.
5. **Pairwise** independence on $I_L$: for all $i,j\in I_L$ with $i\ne j$, the functions $X_i$ and $X_j$ are independent under $\mu$. Spelled out, this means:
   - $Y^t_\ell$ and $Y^t_{\ell'}$ are independent for $\ell\ne\ell'$ in $\{0,\dots,L\}$;
   - $Y^\Delta_\ell$ and $Y^\Delta_{\ell'}$ are independent for $\ell\ne\ell'$ in $\{0,\dots,L\}$;
   - $Y^t_\ell$ and $Y^\Delta_{\ell'}$ are independent for all $\ell,\ell'\in\{0,\dots,L\}$, including $\ell=\ell'$.

   Only pairs are constrained; mutual independence of the whole family is not assumed. Nothing is assumed for indices $\ell>L$.
6. $\mathbb E[Y^t_\ell]=\mathbb E[D^t_\ell]$ for every $\ell\in\mathbb N$.
7. $\mathbb E[Y^\Delta_0]=\mathbb E[P_0-D^t_0]$.
8. $\mathbb E[Y^\Delta_{\ell+1}]=\mathbb E\big[(P_{\ell+1}-P_\ell)-D^t_{\ell+1}\big]$ for every $\ell\in\mathbb N$.

**Conclusion.**
$$\int_\Omega\left(\sum_{\ell=0}^{L}\big(Y^t_\ell+Y^\Delta_\ell\big)-m\right)^{2}d\mu\;=\;\sum_{\ell=0}^{L}\Big(\operatorname{Var}(Y^t_\ell)+\operatorname{Var}(Y^\Delta_\ell)\Big)+\Big(\mathbb E[P_L]-m\Big)^{2}.$$
The constant $m$ is subtracted once, outside the sum on the left. The term $(\mathbb E[P_L]-m)^2$ is added once, outside the sum on the right.

**Edge cases.** $m$ can be any real number. The functions $P_\ell$ and $D^t_\ell$ enter only through their integrals: in hypotheses 6–8 and in the term $\mathbb E[P_L]$. The integrand on the left is the square of a square-integrable function (a finite sum of $L^2$ functions minus a constant, with $\mu$ finite), so the left side is a genuine integral. For $L=0$, both sums have the single term $\ell=0$, and hypothesis 5 reduces to independence of $Y^t_0$ and $Y^\Delta_0$.
