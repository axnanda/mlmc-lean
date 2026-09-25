## sum_crossDiff

**Statement.** For every natural number $D$ (including $D=0$), every function $p:\mathbb N^D\to\mathbb R$ and every multi-index $k=(k_0,\dots,k_{D-1})\in\mathbb N^D$:

$$\sum_{\ell\in B(k)}(\Delta p)(\ell)\;=\;p(k),\qquad B(k)=\prod_{d=0}^{D-1}\{0,1,\dots,k_d\}=\{\ell\in\mathbb N^D:\ \ell_d\le k_d\ \text{for every } d\}.$$

A multi-index is a $D$-tuple of natural numbers, with coordinates labelled $d=0,1,\dots,D-1$. There are no hypotheses. $p$ is any real-valued function on $\mathbb N^D$ and $k$ is any multi-index. The sum runs over the finite box $B(k)$ of all multi-indices that lie coordinatewise between $0$ and $k$. Each factor $\{0,\dots,k_d\}$ is the set of the $k_d+1$ natural numbers below $k_d+1$ (natural-number addition, so there is no edge case). The box always contains $0$ and $k$, so it is never empty, and it has $\prod_d(k_d+1)$ elements.

**The operator $\Delta$ (the packet's `crossDiff`), expanded.** $\Delta$ maps a function $p:\mathbb N^D\to\mathbb R$ to a function $\Delta p:\mathbb N^D\to\mathbb R$. It is defined by recursion on the dimension, splitting off coordinate $0$:

- If $D=0$, then $\mathbb N^0$ has exactly one element (the empty tuple), and $(\Delta p)(\ell)=p(\ell)$.
- If $D=n+1$, write $\ell=(\ell_0,\ell')$ with $\ell'=(\ell_1,\dots,\ell_n)\in\mathbb N^n$. For $j\in\mathbb N$ let $p_j:\mathbb N^n\to\mathbb R$ be $p_j(m)=p(j,m)$, i.e. $p$ with its first coordinate fixed at $j$. Then

$$(\Delta p)(\ell)=(\Delta p_{\ell_0})(\ell')-\begin{cases}0, & \ell_0=0,\\ (\Delta p_{\ell_0-1})(\ell'), & \ell_0\ge1,\end{cases}$$

where the $\Delta$ on the right is the $n$-dimensional operator. The $\ell_0-1$ is natural-number (truncated) subtraction, but it is only evaluated when $\ell_0\ge1$, so it is ordinary subtraction.

Unfolding the recursion gives, for every $D$ and every $\ell\in\mathbb N^D$,

$$(\Delta p)(\ell)=\sum_{S\subseteq\{d\,:\,\ell_d\ge1\}}(-1)^{|S|}\,p\big(\ell-\mathbf 1_S\big),$$

where $\mathbf 1_S\in\{0,1\}^D$ is the indicator vector of $S$. So $\ell-\mathbf 1_S$ lowers by one exactly the coordinates in $S$, all of which are at least $1$, and it stays in $\mathbb N^D$. Equivalently, $\Delta=\Delta_0\Delta_1\cdots\Delta_{D-1}$, where $(\Delta_d f)(\ell)=f(\ell)-f(\ell-e_d)$ if $\ell_d\ge1$ and $(\Delta_d f)(\ell)=f(\ell)$ if $\ell_d=0$. In other words, a term that would need a coordinate equal to $-1$ is left out, which is the same as counting it as $0$. Checks, with $[\cdot]$ equal to $1$ if the condition holds and $0$ otherwise:

- $D=0$: only $S=\emptyset$ occurs, which gives $p(\ell)$.
- $D=1$: $(\Delta p)(\ell_0)=p(\ell_0)-p(\ell_0-1)$ if $\ell_0\ge1$, and $(\Delta p)(0)=p(0)$.
- $D=2$: $(\Delta p)(\ell_0,\ell_1)=p(\ell_0,\ell_1)-[\ell_1\ge1]\,p(\ell_0,\ell_1-1)-[\ell_0\ge1]\,p(\ell_0-1,\ell_1)+[\ell_0\ge1][\ell_1\ge1]\,p(\ell_0-1,\ell_1-1)$.

**Edge cases.** For $D=0$, the box $B(k)$ holds only the empty tuple, which is $k$ itself, and the statement reads $p(k)=p(k)$. For any $D$, only the values of $p$ on $B(k)$ appear on either side.

## giles_theorem2

**Objects.** All of these are universally quantified, and nothing is assumed about them beyond the hypotheses listed below.

- A natural number $D\ge1$ ($D=0$ is excluded; this is the only condition on $D$). Multi-indices are $\ell=(\ell_0,\dots,\ell_{D-1})\in\mathbb N^D$, and a vector $a\in\mathbb R^D$ has coordinates $a_0,\dots,a_{D-1}$.
- An arbitrary measurable space $(\Omega,\mathcal F)$ and a probability measure $\mu$ on it, so $\mu(\Omega)=1$. Below, $\mathbb E[f]=\int_\Omega f\,d\mu$ and $\operatorname{Var}(X)=\mathbb E\big[(X-\mathbb E[X])^2\big]$, both taken with respect to $\mu$.
- A function $P:\Omega\to\mathbb R$.
- A function $P_\ell:\Omega\to\mathbb R$ for each $\ell\in\mathbb N^D$.
- A function $Y_{\ell,n}:\Omega\to\mathbb R$ for each $\ell\in\mathbb N^D$ and each $n\in\mathbb N$, including $n=0$.
- A function $\mathrm{Cost}_{\ell,n}:\Omega\to\mathbb R$ for each $\ell\in\mathbb N^D$ and each $n\in\mathbb N$.
- Real numbers $V_\ell$ and $C_\ell$ for each $\ell\in\mathbb N^D$.
- Vectors $\alpha,\beta,\gamma\in\mathbb R^D$ and real numbers $c_1,c_2,c_3$.

**Derived quantities (the packet's definitions, expanded).**

- (`dot`) $\alpha\cdot\ell=\sum_{d=0}^{D-1}\alpha_d\,\ell_d$, with $\ell_d$ read as a real number. $\beta\cdot\ell$ and $\gamma\cdot\ell$ are defined the same way.
- (`crossDiff`) For each $\omega$, $(\Delta P)_\ell(\omega)$ is the value at $\ell$ of the operator $\Delta$ applied to the function $m\mapsto P_m(\omega)$ on $\mathbb N^D$:

$$(\Delta P)_\ell(\omega)=\sum_{S\subseteq\{d\,:\,\ell_d\ge1\}}(-1)^{|S|}\,P_{\ell-\mathbf 1_S}(\omega).$$

  Here $\mathbf 1_S\in\{0,1\}^D$ is the indicator vector of $S$. Only coordinates that are at least $1$ are lowered, so every index stays in $\mathbb N^D$. This closed form is what the recursive definition produces. The recursion splits off coordinate $0$: $(\Delta q)(\ell_0,\ell')=(\Delta q(\ell_0,\cdot))(\ell')-[\ell_0\ge1]\,(\Delta q(\ell_0-1,\cdot))(\ell')$, and $\Delta q=q$ in dimension $0$. The natural-number subtraction $\ell_0-1$ is only used when $\ell_0\ge1$. Below, $[\cdot]$ is $1$ if the condition holds and $0$ otherwise.
  - $D=1$: $(\Delta P)_\ell=P_\ell-P_{\ell-1}$ if $\ell\ge1$, and $(\Delta P)_0=P_0$.
  - $D=2$: $(\Delta P)_{(\ell_0,\ell_1)}=P_{(\ell_0,\ell_1)}-[\ell_1\ge1]\,P_{(\ell_0,\ell_1-1)}-[\ell_0\ge1]\,P_{(\ell_0-1,\ell_1)}+[\ell_0\ge1][\ell_1\ge1]\,P_{(\ell_0-1,\ell_1-1)}$.
- (`mimcEta`) $\displaystyle\eta=\max_{0\le d\le D-1}\frac{\gamma_d-\beta_d}{\alpha_d}$.
- (`mimcD2`) $d_2=\#\{d\in\{0,\dots,D-1\}:\ (\gamma_d-\beta_d)/\alpha_d=\eta\}$ is the number of coordinates where the maximum is attained, using exact equality. It is a natural number with $1\le d_2\le D$.
- (`mimcBound`, with the arguments used here) for $\varepsilon>0$, with every power a real power:

$$B(\varepsilon)=\begin{cases}\varepsilon^{-2}, & \eta<0,\\ \varepsilon^{-2}\,|\ln\varepsilon|^{\,2d_2}, & \eta=0,\\ \varepsilon^{-2-\eta}\,|\ln\varepsilon|^{\,(d_2-1)(2+\eta)}, & \eta>0.\end{cases}$$

**Hypotheses.**

1. (hα, hβ, hγ) $\alpha_d>0$, $\beta_d>0$ and $\gamma_d>0$ for every $d$.
2. (hαβ) $\alpha_d>\beta_d/2$ for every $d$ (strict inequality).
3. (hc₁, hc₂, hc₃) $c_1>0$, $c_2>0$ and $c_3>0$.
4. (hP, hPℓ) $P$ is $\mu$-integrable, and every $P_\ell$ is $\mu$-integrable.
5. (hY) For every $\ell$ and every $n\in\mathbb N$, including $n=0$, $Y_{\ell,n}\in L^2(\mu)$. That is, it is almost-everywhere measurable and $\mathbb E[Y_{\ell,n}^2]<\infty$.
6. (hind) Take any $N:\mathbb N^D\to\mathbb N$ with $N_\ell\ge1$ for all $\ell$, and any two distinct multi-indices $i\ne j$. Then $Y_{i,N_i}$ and $Y_{j,N_j}$ are independent under $\mu$: $\mu(Y_{i,N_i}\in A,\ Y_{j,N_j}\in A')=\mu(Y_{i,N_i}\in A)\,\mu(Y_{j,N_j}\in A')$ for all Borel sets $A,A'$. Equivalently, $Y_{i,n}$ and $Y_{j,n'}$ are independent whenever $i\ne j$ and $n,n'\ge1$. Only pairs are assumed independent. Nothing is said about the joint (mutual) independence of three or more of them, about $Y_{\ell,n}$ versus $Y_{\ell,n'}$ at the same $\ell$, or about independence from $P$, the $P_\ell$ or the $\mathrm{Cost}_{\ell,n}$.
7. (hCost) For every $\ell$ and every $n\ge1$, $\mathrm{Cost}_{\ell,n}$ is $\mu$-integrable.
8. (h_cost) For every $\ell$ and every $n\ge1$, $\mathbb E[\mathrm{Cost}_{\ell,n}]=n\,C_\ell$.
9. (h_var) For every $\ell$ and every $n\ge1$, $\operatorname{Var}(Y_{\ell,n})=V_\ell/n$.
10. (h_i) For every $\delta>0$ there is $n_0\in\mathbb N$ such that $|\mathbb E[P_\ell-P]|<\delta$ for every $\ell$ with $\ell_d\ge n_0$ for all $d$. In other words, $\mathbb E[P_\ell-P]\to0$ as $\min_d\ell_d\to\infty$. No rate is given.
11. (h_iii) For every $\ell$ and every $n\ge1$, $\mathbb E[Y_{\ell,n}]=\mathbb E[(\Delta P)_\ell]$. By linearity, the right side equals $\sum_{S\subseteq\{d:\ell_d\ge1\}}(-1)^{|S|}\,\mathbb E[P_{\ell-\mathbf 1_S}]$.
12. (h_ii) For every $\ell$ and every $n\ge1$, $|\mathbb E[Y_{\ell,n}]|\le c_1\,2^{-\alpha\cdot\ell}$.
13. (h_iv) For every $\ell$, $V_\ell\le c_2\,2^{-\beta\cdot\ell}$.
14. (h_v) For every $\ell$, $C_\ell\le c_3\,2^{\gamma\cdot\ell}$.

**Conclusion.** There is a real number $c_4>0$ with the property below. It is chosen after all the objects above, so it may depend on all of them (including the particular functions $P,P_\ell,Y,\mathrm{Cost}$), but it does not depend on $\varepsilon$. For every real $\varepsilon$ with $0<\varepsilon<e^{-1}$, there exist a finite set $\mathcal L\subset\mathbb N^D$ and a function $N:\mathbb N^D\to\mathbb N$ with $N_\ell\ge1$ for **every** $\ell\in\mathbb N^D$ such that both of the following hold. $\mathcal L$ and $N$ may depend on $\varepsilon$.

$$\mathbb E\Big[\Big(\sum_{\ell\in\mathcal L}Y_{\ell,N_\ell}-\mathbb E[P]\Big)^{2}\Big]<\varepsilon^{2}\qquad\text{and}\qquad \mathbb E\Big[\sum_{\ell\in\mathcal L}\mathrm{Cost}_{\ell,N_\ell}\Big]\le c_4\,B(\varepsilon).$$

In the first inequality, the constant $\mathbb E[P]$ is subtracted once from the whole sum, not once per term, and the difference is then squared. The first inequality is strict and the second is non-strict.

**Edge cases and conventions.**

- *No junk integrals.* The integral of a non-integrable function would be $0$ by convention, and the variance of a variable with infinite second moment would be $0$. Neither case arises here:
  - $Y_{\ell,n}\in L^2\subset L^1$, because $\mu$ is a probability measure.
  - $P_\ell-P$ and $(\Delta P)_\ell$ are finite signed sums of integrable functions.
  - Each $\mathrm{Cost}_{\ell,N_\ell}$ is integrable because $N_\ell\ge1$.
  - $\sum_{\ell\in\mathcal L}Y_{\ell,N_\ell}-\mathbb E[P]$ is in $L^2$, so its square is integrable.

  By (h_cost) and linearity, the expected cost in the conclusion equals $\sum_{\ell\in\mathcal L}N_\ell\,C_\ell$.
- *Casts and arithmetic.* The exponents $2d_2$ and $(d_2-1)(2+\eta)$ are real numbers. $d_2$ is converted to a real before $1$ is subtracted, and since $d_2\ge1$ there would be no truncation in any case. When $d_2=1$, the exponent in the $\eta>0$ branch is $0$ and the logarithmic factor equals $1$. In (h_cost) and (h_var), $n$ is converted to a real. $V_\ell/n$ never divides by zero because $n\ge1$, and $(\gamma_d-\beta_d)/\alpha_d$ never divides by zero because $\alpha_d>0$. (The convention $a/0=0$ is never triggered.)
- *Powers, logarithm, absolute value.* Every base is positive: the base is $2$ in (h_ii), (h_iv) and (h_v), and $\varepsilon>0$. Since $\varepsilon<e^{-1}$, $\ln\varepsilon<-1$, so $|\ln\varepsilon|=\ln(1/\varepsilon)>1$. So $x^y=e^{y\ln x}$ throughout, for example $\varepsilon^{-2}=1/\varepsilon^2$ and $\varepsilon^{-2-\eta}=(1/\varepsilon)^{2+\eta}$. The conventions for degenerate inputs are never reached. Those conventions are: $0^0=1$; $0^y=0$ for $y\ne0$; $x^y=e^{y\ln|x|}\cos(\pi y)$ for $x<0$; $\ln 0=0$; and $\ln x=\ln|x|$ for $x<0$. Which branch of $B$ applies depends on the exact sign of $\eta$.
- *Freedom in the witnesses.* $\mathcal L$ may be any finite set of multi-indices, including the empty set. If it is empty, the sum is $0$, the left side of the first inequality is $(\mathbb E[P])^2$, and the expected cost is $0$. No structural condition, such as being downward closed, is imposed on $\mathcal L$. $N$ must be at least $1$ everywhere, but only its values on $\mathcal L$ appear in the two inequalities. The statement only asserts that $\mathcal L$ and $N$ exist for each $\varepsilon$.
- *What is not assumed.*
  - No sign condition is placed on $\mathrm{Cost}_{\ell,n}$ or on $C_\ell$; there is only the upper bound (h_v). $V_\ell\ge0$ does follow from (h_var) with $n=1$.
  - Nothing is assumed about $Y_{\ell,0}$ beyond (hY), and nothing about $\mathrm{Cost}_{\ell,0}$.
  - The $Y_{\ell,n}$ are tied to the $P_\ell$ only through the mean identity (h_iii), and $P_\ell$ is tied to $P$ only through (h_i).
- *Not vacuous.* All the hypotheses can hold at once. For example, take $D=1$, $\alpha=\beta=\gamma=1$, $c_1=c_2=c_3=1$, and let $P$, every $P_\ell$, $Y_{\ell,n}$, $\mathrm{Cost}_{\ell,n}$, $V_\ell$ and $C_\ell$ be identically $0$.

## giles_theorem2_boundary

**Objects.** All of these are universally quantified, and nothing is assumed about them beyond the hypotheses listed below.

- A natural number $D\ge1$ ($D=0$ is excluded; this is the only condition on $D$). Multi-indices are $\ell=(\ell_0,\dots,\ell_{D-1})\in\mathbb N^D$, and a vector $a\in\mathbb R^D$ has coordinates $a_0,\dots,a_{D-1}$.
- An arbitrary measurable space $(\Omega,\mathcal F)$ and a probability measure $\mu$ on it, so $\mu(\Omega)=1$. Below, $\mathbb E[f]=\int_\Omega f\,d\mu$ and $\operatorname{Var}(X)=\mathbb E\big[(X-\mathbb E[X])^2\big]$, both taken with respect to $\mu$.
- A function $P:\Omega\to\mathbb R$.
- A function $P_\ell:\Omega\to\mathbb R$ for each $\ell\in\mathbb N^D$.
- A function $Y_{\ell,n}:\Omega\to\mathbb R$ for each $\ell\in\mathbb N^D$ and each $n\in\mathbb N$, including $n=0$.
- A function $\mathrm{Cost}_{\ell,n}:\Omega\to\mathbb R$ for each $\ell\in\mathbb N^D$ and each $n\in\mathbb N$.
- Real numbers $V_\ell$ and $C_\ell$ for each $\ell\in\mathbb N^D$.
- Vectors $\alpha,\beta,\gamma\in\mathbb R^D$ and real numbers $c_1,c_2,c_3$.

**Derived quantities (the packet's definitions, expanded).**

- (`dot`) $\alpha\cdot\ell=\sum_{d=0}^{D-1}\alpha_d\,\ell_d$, with $\ell_d$ read as a real number. $\beta\cdot\ell$ and $\gamma\cdot\ell$ are defined the same way.
- (`crossDiff`) For each $\omega$, $(\Delta P)_\ell(\omega)$ is the value at $\ell$ of the operator $\Delta$ applied to the function $m\mapsto P_m(\omega)$ on $\mathbb N^D$:

$$(\Delta P)_\ell(\omega)=\sum_{S\subseteq\{d\,:\,\ell_d\ge1\}}(-1)^{|S|}\,P_{\ell-\mathbf 1_S}(\omega).$$

  Here $\mathbf 1_S\in\{0,1\}^D$ is the indicator vector of $S$. Only coordinates that are at least $1$ are lowered, so every index stays in $\mathbb N^D$. This closed form is what the recursive definition produces. The recursion splits off coordinate $0$: $(\Delta q)(\ell_0,\ell')=(\Delta q(\ell_0,\cdot))(\ell')-[\ell_0\ge1]\,(\Delta q(\ell_0-1,\cdot))(\ell')$, and $\Delta q=q$ in dimension $0$. The natural-number subtraction $\ell_0-1$ is only used when $\ell_0\ge1$. Below, $[\cdot]$ is $1$ if the condition holds and $0$ otherwise.
  - $D=1$: $(\Delta P)_\ell=P_\ell-P_{\ell-1}$ if $\ell\ge1$, and $(\Delta P)_0=P_0$.
  - $D=2$: $(\Delta P)_{(\ell_0,\ell_1)}=P_{(\ell_0,\ell_1)}-[\ell_1\ge1]\,P_{(\ell_0,\ell_1-1)}-[\ell_0\ge1]\,P_{(\ell_0-1,\ell_1)}+[\ell_0\ge1][\ell_1\ge1]\,P_{(\ell_0-1,\ell_1-1)}$.
- (`mimcEta`) $\displaystyle\eta=\max_{0\le d\le D-1}\frac{\gamma_d-\beta_d}{\alpha_d}$.
- (`mimcD2`) $d_2=\#\{d\in\{0,\dots,D-1\}:\ (\gamma_d-\beta_d)/\alpha_d=\eta\}$ is the number of coordinates where the maximum is attained, using exact equality. It is a natural number with $1\le d_2\le D$.
- (`mimcBound`, with the arguments used here) for $\varepsilon>0$, with every power a real power:

$$B(\varepsilon)=\begin{cases}\varepsilon^{-2}, & \eta<0,\\ \varepsilon^{-2}\,|\ln\varepsilon|^{\,2d_2+D}, & \eta=0,\\ \varepsilon^{-2-\eta}\,|\ln\varepsilon|^{\,(d_2-1)(2+\eta)+D}, & \eta>0.\end{cases}$$

  The dimension $D$ is added to both logarithmic exponents. The $\eta<0$ branch has no logarithmic factor and does not involve $D$.

**Hypotheses.**

1. (hα, hβ, hγ) $\alpha_d>0$, $\beta_d>0$ and $\gamma_d>0$ for every $d$.
2. (hαβ) $\alpha_d\ge\beta_d/2$ for every $d$. The inequality is non-strict, so $\alpha_d=\beta_d/2$ is allowed.
3. (hc₁, hc₂, hc₃) $c_1>0$, $c_2>0$ and $c_3>0$.
4. (hP, hPℓ) $P$ is $\mu$-integrable, and every $P_\ell$ is $\mu$-integrable.
5. (hY) For every $\ell$ and every $n\in\mathbb N$, including $n=0$, $Y_{\ell,n}\in L^2(\mu)$. That is, it is almost-everywhere measurable and $\mathbb E[Y_{\ell,n}^2]<\infty$.
6. (hind) Take any $N:\mathbb N^D\to\mathbb N$ with $N_\ell\ge1$ for all $\ell$, and any two distinct multi-indices $i\ne j$. Then $Y_{i,N_i}$ and $Y_{j,N_j}$ are independent under $\mu$: $\mu(Y_{i,N_i}\in A,\ Y_{j,N_j}\in A')=\mu(Y_{i,N_i}\in A)\,\mu(Y_{j,N_j}\in A')$ for all Borel sets $A,A'$. Equivalently, $Y_{i,n}$ and $Y_{j,n'}$ are independent whenever $i\ne j$ and $n,n'\ge1$. Only pairs are assumed independent. Nothing is said about the joint (mutual) independence of three or more of them, about $Y_{\ell,n}$ versus $Y_{\ell,n'}$ at the same $\ell$, or about independence from $P$, the $P_\ell$ or the $\mathrm{Cost}_{\ell,n}$.
7. (hCost) For every $\ell$ and every $n\ge1$, $\mathrm{Cost}_{\ell,n}$ is $\mu$-integrable.
8. (h_cost) For every $\ell$ and every $n\ge1$, $\mathbb E[\mathrm{Cost}_{\ell,n}]=n\,C_\ell$.
9. (h_var) For every $\ell$ and every $n\ge1$, $\operatorname{Var}(Y_{\ell,n})=V_\ell/n$.
10. (h_i) For every $\delta>0$ there is $n_0\in\mathbb N$ such that $|\mathbb E[P_\ell-P]|<\delta$ for every $\ell$ with $\ell_d\ge n_0$ for all $d$. In other words, $\mathbb E[P_\ell-P]\to0$ as $\min_d\ell_d\to\infty$. No rate is given.
11. (h_iii) For every $\ell$ and every $n\ge1$, $\mathbb E[Y_{\ell,n}]=\mathbb E[(\Delta P)_\ell]$. By linearity, the right side equals $\sum_{S\subseteq\{d:\ell_d\ge1\}}(-1)^{|S|}\,\mathbb E[P_{\ell-\mathbf 1_S}]$.
12. (h_ii) For every $\ell$ and every $n\ge1$, $|\mathbb E[Y_{\ell,n}]|\le c_1\,2^{-\alpha\cdot\ell}$.
13. (h_iv) For every $\ell$, $V_\ell\le c_2\,2^{-\beta\cdot\ell}$.
14. (h_v) For every $\ell$, $C_\ell\le c_3\,2^{\gamma\cdot\ell}$.

**Conclusion.** There is a real number $c_4>0$ with the property below. It is chosen after all the objects above, so it may depend on all of them (including the particular functions $P,P_\ell,Y,\mathrm{Cost}$), but it does not depend on $\varepsilon$. For every real $\varepsilon$ with $0<\varepsilon<e^{-1}$, there exist a finite set $\mathcal L\subset\mathbb N^D$ and a function $N:\mathbb N^D\to\mathbb N$ with $N_\ell\ge1$ for **every** $\ell\in\mathbb N^D$ such that both of the following hold, with $B$ as defined above (the version with $+D$ in the exponents). $\mathcal L$ and $N$ may depend on $\varepsilon$.

$$\mathbb E\Big[\Big(\sum_{\ell\in\mathcal L}Y_{\ell,N_\ell}-\mathbb E[P]\Big)^{2}\Big]<\varepsilon^{2}\qquad\text{and}\qquad \mathbb E\Big[\sum_{\ell\in\mathcal L}\mathrm{Cost}_{\ell,N_\ell}\Big]\le c_4\,B(\varepsilon).$$

In the first inequality, the constant $\mathbb E[P]$ is subtracted once from the whole sum, not once per term, and the difference is then squared. The first inequality is strict and the second is non-strict.

**Edge cases and conventions.**

- *No junk integrals.* The integral of a non-integrable function would be $0$ by convention, and the variance of a variable with infinite second moment would be $0$. Neither case arises here:
  - $Y_{\ell,n}\in L^2\subset L^1$, because $\mu$ is a probability measure.
  - $P_\ell-P$ and $(\Delta P)_\ell$ are finite signed sums of integrable functions.
  - Each $\mathrm{Cost}_{\ell,N_\ell}$ is integrable because $N_\ell\ge1$.
  - $\sum_{\ell\in\mathcal L}Y_{\ell,N_\ell}-\mathbb E[P]$ is in $L^2$, so its square is integrable.

  By (h_cost) and linearity, the expected cost in the conclusion equals $\sum_{\ell\in\mathcal L}N_\ell\,C_\ell$.
- *Casts and arithmetic.* The exponents $2d_2+D$ and $(d_2-1)(2+\eta)+D$ are real numbers, and the natural numbers $d_2$ and $D$ are converted to reals. $1$ is subtracted from $d_2$ after the conversion, and since $d_2\ge1$ there would be no truncation in any case. When $d_2=1$, the exponent in the $\eta>0$ branch is exactly $D$, so the factor is $|\ln\varepsilon|^{D}$. In (h_cost) and (h_var), $n$ is converted to a real. $V_\ell/n$ never divides by zero because $n\ge1$, and $(\gamma_d-\beta_d)/\alpha_d$ never divides by zero because $\alpha_d>0$. (The convention $a/0=0$ is never triggered.)
- *Powers, logarithm, absolute value.* Every base is positive: the base is $2$ in (h_ii), (h_iv) and (h_v), and $\varepsilon>0$. Since $\varepsilon<e^{-1}$, $\ln\varepsilon<-1$, so $|\ln\varepsilon|=\ln(1/\varepsilon)>1$. So $x^y=e^{y\ln x}$ throughout, for example $\varepsilon^{-2}=1/\varepsilon^2$ and $\varepsilon^{-2-\eta}=(1/\varepsilon)^{2+\eta}$. The conventions for degenerate inputs are never reached. Those conventions are: $0^0=1$; $0^y=0$ for $y\ne0$; $x^y=e^{y\ln|x|}\cos(\pi y)$ for $x<0$; $\ln 0=0$; and $\ln x=\ln|x|$ for $x<0$. Which branch of $B$ applies depends on the exact sign of $\eta$.
- *Freedom in the witnesses.* $\mathcal L$ may be any finite set of multi-indices, including the empty set. If it is empty, the sum is $0$, the left side of the first inequality is $(\mathbb E[P])^2$, and the expected cost is $0$. No structural condition, such as being downward closed, is imposed on $\mathcal L$. $N$ must be at least $1$ everywhere, but only its values on $\mathcal L$ appear in the two inequalities. The statement only asserts that $\mathcal L$ and $N$ exist for each $\varepsilon$.
- *What is not assumed.*
  - No sign condition is placed on $\mathrm{Cost}_{\ell,n}$ or on $C_\ell$; there is only the upper bound (h_v). $V_\ell\ge0$ does follow from (h_var) with $n=1$.
  - Nothing is assumed about $Y_{\ell,0}$ beyond (hY), and nothing about $\mathrm{Cost}_{\ell,0}$.
  - The $Y_{\ell,n}$ are tied to the $P_\ell$ only through the mean identity (h_iii), and $P_\ell$ is tied to $P$ only through (h_i).
- *Not vacuous.* All the hypotheses can hold at once. For example, take $D=1$, $\alpha=\beta=\gamma=1$, $c_1=c_2=c_3=1$, and let $P$, every $P_\ell$, $Y_{\ell,n}$, $\mathrm{Cost}_{\ell,n}$, $V_\ell$ and $C_\ell$ be identically $0$.
