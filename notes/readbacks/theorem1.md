## giles_theorem1

**Setting.** $\Omega$ is a set carrying a σ-algebra, and $\mu$ is a probability measure on $\Omega$. $\mathbb{R}$ carries its Borel σ-algebra, and $\mathbb{N}=\{0,1,2,\dots\}$. For $f:\Omega\to\mathbb{R}$, $\mathbb{E}[f]$ means $\int_\Omega f\,\mathrm{d}\mu$. This is the Bochner integral, which by convention is $0$ when $f$ is not integrable. $\operatorname{Var}(f)$ means the variance $\mathbb{E}\bigl[(f-\mathbb{E}[f])^2\bigr]$ under $\mu$, which by convention is recorded as $0$ when $f$ has infinite second moment. Under the hypotheses below, every expectation that occurs is of an integrable function and every variance that occurs is of a square-integrable one, so neither convention comes into play.

**Data** (arbitrary; the statement is universally quantified over all of them):

- a function $P:\Omega\to\mathbb{R}$;
- functions $P_\ell:\Omega\to\mathbb{R}$, one for each $\ell\in\mathbb{N}$;
- functions $Y_{\ell,n}:\Omega\to\mathbb{R}$, one for each pair $(\ell,n)\in\mathbb{N}\times\mathbb{N}$;
- functions $\mathrm{Cost}_{\ell,n}:\Omega\to\mathbb{R}$, one for each pair $(\ell,n)\in\mathbb{N}\times\mathbb{N}$;
- real sequences $(V_\ell)_{\ell\in\mathbb{N}}$ and $(C_\ell)_{\ell\in\mathbb{N}}$;
- real numbers $\alpha,\beta,\gamma,c_1,c_2,c_3$.

The $Y_{\ell,n}$ are not defined in terms of $P$ or the $P_\ell$. They are tied to the rest of the data only through the hypotheses below.

**Hypotheses.**

1. $\alpha>0$, $\beta>0$, $\gamma>0$, $c_1>0$, $c_2>0$, $c_3>0$.
2. $\tfrac12\min(\beta,\gamma)\le\alpha$.
3. $P$ is integrable, and each $P_\ell$ is integrable.
4. Each $Y_{\ell,n}$ (for all $\ell,n\in\mathbb{N}$, including $n=0$) is square-integrable: it is almost everywhere equal to a measurable function, and $\mathbb{E}[Y_{\ell,n}^2]<\infty$.
5. Independence, as literally stated: take any sequence $(N_\ell)_{\ell\in\mathbb{N}}$ of natural numbers with $N_\ell>0$ for all $\ell$, and any two distinct levels $i\neq j$. Then the random variables $Y_{i,N_i}$ and $Y_{j,N_j}$ are independent under $\mu$, meaning the σ-algebras they generate are independent. The sequence is arbitrary apart from positivity, so this is equivalent to: for all $i\neq j$ in $\mathbb{N}$ and all $n,m\ge1$, $Y_{i,n}$ and $Y_{j,m}$ are independent. Only two variables at a time are involved, and they come from two different levels. No mutual independence of three or more variables is assumed. Nothing is said about $Y_{\ell,n}$ versus $Y_{\ell,m}$ at the same level, and indices $n=0$ do not enter.
6. For every $\ell\in\mathbb{N}$ and every $n\ge1$: $\mathrm{Cost}_{\ell,n}$ is integrable and $\mathbb{E}[\mathrm{Cost}_{\ell,n}]=n\,C_\ell$. In particular $C_\ell=\mathbb{E}[\mathrm{Cost}_{\ell,1}]$.
7. For every $\ell\in\mathbb{N}$: $\bigl|\mathbb{E}[P_\ell-P]\bigr|\le c_1\,2^{-\alpha\ell}$.
8. For every $n\ge1$: $\mathbb{E}[Y_{0,n}]=\mathbb{E}[P_0]$. For every $\ell\in\mathbb{N}$ and $n\ge1$: $\mathbb{E}[Y_{\ell+1,n}]=\mathbb{E}[P_{\ell+1}-P_\ell]$.
9. For every $\ell\in\mathbb{N}$ and $n\ge1$: $\operatorname{Var}(Y_{\ell,n})=V_\ell/n$ (an exact equality). Variances are non-negative, so this forces $V_\ell=\operatorname{Var}(Y_{\ell,1})\ge0$.
10. For every $\ell\in\mathbb{N}$: $V_\ell\le c_2\,2^{-\beta\ell}$.
11. For every $\ell\in\mathbb{N}$: $C_\ell\le c_3\,2^{\gamma\ell}$.

In 7, 10 and 11, $\ell$ is treated as a real number. $2^{t}=e^{t\ln 2}$ is the real power of the positive base $2$, so there is no degenerate case.

The following are not assumed anywhere:

- any sign or lower bound on $C_\ell$ or on the values of $\mathrm{Cost}_{\ell,n}$, which may be zero or negative;
- anything about $\mathrm{Cost}_{\ell,0}$, which is completely unconstrained;
- anything about the mean or variance of $Y_{\ell,0}$;
- any independence or joint-distribution condition involving $P$, the $P_\ell$ or the costs.

All the hypotheses can hold at once, for example with $\alpha=\beta=\gamma=c_1=c_2=c_3=1$, every function identically $0$, and $V_\ell=C_\ell=0$. So the statement is not vacuous.

**Auxiliary function (definition expanded).** For $\varepsilon>0$,

$$
B_{\alpha,\beta,\gamma}(\varepsilon)=
\begin{cases}
\varepsilon^{-2} & \text{if } \gamma<\beta,\\
\varepsilon^{-2}\,(\ln\varepsilon)^{2} & \text{if } \gamma=\beta,\\
\varepsilon^{-2-(\gamma-\beta)/\alpha} & \text{if } \gamma>\beta.
\end{cases}
$$

It is evaluated only at $0<\varepsilon<e^{-1}$. There, all powers are ordinary real powers of a positive number and $\ln$ is the natural logarithm with $\ln\varepsilon<-1$, so $(\ln\varepsilon)^2>1$. Since $\alpha>0$, the division by $\alpha$ is ordinary.

**Conclusion.** There exists a real number $c_4>0$ with the following property. For every real $\varepsilon$ with $0<\varepsilon<e^{-1}$ there exist $L\in\mathbb{N}$ and a sequence $N=(N_\ell)_{\ell\in\mathbb{N}}$ of natural numbers such that:

- $N_\ell\ge1$ for **every** $\ell\in\mathbb{N}$, including $\ell>L$, where $N_\ell$ plays no further role;
- the mean-square bound holds:

$$
\mathbb{E}\Bigl[\Bigl(\sum_{\ell=0}^{L}Y_{\ell,N_\ell}\;-\;\mathbb{E}[P]\Bigr)^{2}\Bigr]<\varepsilon^{2};
$$

- the cost bound holds:

$$
\mathbb{E}\Bigl[\sum_{\ell=0}^{L}\mathrm{Cost}_{\ell,N_\ell}\Bigr]\le c_4\,B_{\alpha,\beta,\gamma}(\varepsilon).
$$

Reading notes:

- In the first inequality, the constant $\mathbb{E}[P]$ is subtracted once from the whole sum, not from each summand, and the difference is then squared. This inequality is strict.
- The second inequality is non-strict. By hypothesis 6 and linearity, its left side equals $\sum_{\ell=0}^{L}N_\ell\,C_\ell$.
- $L=0$ is allowed. The sum then has the single term $Y_{0,N_0}$.
- Order of quantifiers: $c_4$ is chosen before $\varepsilon$, so it cannot depend on $\varepsilon$. It is chosen after all the data, so it may depend on $\mu$, $P$, $(P_\ell)$, $(Y_{\ell,n})$, $(\mathrm{Cost}_{\ell,n})$, $(V_\ell)$, $(C_\ell)$ and $\alpha,\beta,\gamma,c_1,c_2,c_3$. $L$ and $N$ may depend on $\varepsilon$ and on all the data.
- Nothing is asserted for $\varepsilon\ge e^{-1}$.
- The surrounding context also declares a type $\iota$, which does not occur in this statement.

## giles_theorem1_standard

**Setting.** $\Omega_0$ and $\Omega$ are sets, each carrying a σ-algebra. $\nu$ is a probability measure on $\Omega_0$, and $\mu$ is a probability measure on $\Omega$. $\mathbb{R}$ carries its Borel σ-algebra, and $\mathbb{N}=\{0,1,2,\dots\}$.

- $\mathbb{E}_\nu[g]=\int_{\Omega_0}g\,\mathrm{d}\nu$ and $\mathbb{E}_\mu[f]=\int_\Omega f\,\mathrm{d}\mu$ are Bochner integrals. By convention each is $0$ for a non-integrable integrand.
- $\operatorname{Var}_\nu(g)=\mathbb{E}_\nu\bigl[(g-\mathbb{E}_\nu[g])^2\bigr]$. By convention it is $0$ when $g$ has infinite second moment.

Under the hypotheses below, every expectation that occurs is of an integrable function and every variance is of a square-integrable one, so neither convention comes into play.

**Data** (arbitrary; universally quantified):

- a function $P:\Omega_0\to\mathbb{R}$;
- functions $P_\ell:\Omega_0\to\mathbb{R}$, one for each $\ell\in\mathbb{N}$;
- maps $\omega_{\ell,n}:\Omega\to\Omega_0$, one for each pair $(\ell,n)\in\mathbb{N}\times\mathbb{N}$. Here $\omega$ names this family of maps, not a sample point; points of $\Omega$ are written $x$;
- functions $\mathrm{cost}_{\ell,n}:\Omega\to\mathbb{R}$, one for each pair $(\ell,n)\in\mathbb{N}\times\mathbb{N}$;
- a real sequence $(C_\ell)_{\ell\in\mathbb{N}}$;
- real numbers $\alpha,\beta,\gamma,c_1,c_2,c_3$.

**Quantities built from the data (definitions expanded).**

*Level differences.* These are functions $D_\ell:\Omega_0\to\mathbb{R}$ with $D_0=P_0$ and $D_\ell=P_\ell-P_{\ell-1}$ for $\ell\ge1$.

*Estimator and total cost.* Fix $L\in\mathbb{N}$ and a sequence $N=(N_\ell)_{\ell\in\mathbb{N}}$ of natural numbers. The estimator $\widehat{Y}_{L,N}:\Omega\to\mathbb{R}$ and the total cost $\mathrm{TC}_{L,N}:\Omega\to\mathbb{R}$ are

$$
\widehat{Y}_{L,N}(x)=\sum_{\ell=0}^{L}\frac{1}{N_\ell}\sum_{n=0}^{N_\ell-1}D_\ell\bigl(\omega_{\ell,n}(x)\bigr),
\qquad
\mathrm{TC}_{L,N}(x)=\sum_{\ell=0}^{L}\sum_{n=0}^{N_\ell-1}\mathrm{cost}_{\ell,n}(x).
$$

- For $\ell\ge1$, the $(\ell,n)$-th summand of the estimator is $P_\ell(\omega_{\ell,n}(x))-P_{\ell-1}(\omega_{\ell,n}(x))$. Both terms are evaluated at the same point $\omega_{\ell,n}(x)$, and different index pairs $(\ell,n)$ use different members of the family $\omega$.
- The prefactor is literally $N_\ell^{-1}$, with the convention $0^{-1}=0$, and the inner sum is empty when $N_\ell=0$. So a level with $N_\ell=0$ would contribute $0$. In the conclusion every $N_\ell\ge1$, so this case does not arise.

*Auxiliary function.* For $\varepsilon>0$,

$$
B_{\alpha,\beta,\gamma}(\varepsilon)=
\begin{cases}
\varepsilon^{-2} & \text{if } \gamma<\beta,\\
\varepsilon^{-2}\,(\ln\varepsilon)^{2} & \text{if } \gamma=\beta,\\
\varepsilon^{-2-(\gamma-\beta)/\alpha} & \text{if } \gamma>\beta.
\end{cases}
$$

It is evaluated only at $0<\varepsilon<e^{-1}$. There the powers are ordinary real powers of a positive number, $\ln$ is the natural logarithm with $\ln\varepsilon<-1$, and $\alpha>0$.

**Hypotheses.**

1. $\alpha,\beta,\gamma,c_1,c_2,c_3>0$.
2. $\tfrac12\min(\beta,\gamma)\le\alpha$.
3. For every pair $(\ell,n)$, the map $\omega_{\ell,n}$ is measurable and measure-preserving from $(\Omega,\mu)$ to $(\Omega_0,\nu)$. That is, $\mu(\omega_{\ell,n}\in A)=\nu(A)$ for every measurable $A\subseteq\Omega_0$.
4. The whole family $(\omega_{\ell,n})_{(\ell,n)\in\mathbb{N}\times\mathbb{N}}$ is mutually independent under $\mu$. That is, for any finitely many distinct index pairs $p_1,\dots,p_k$ and measurable $A_1,\dots,A_k\subseteq\Omega_0$, $\mu\bigl(\omega_{p_1}\in A_1,\dots,\omega_{p_k}\in A_k\bigr)=\prod_{j=1}^{k}\mu(\omega_{p_j}\in A_j)$. Together with 3, the $\omega_{\ell,n}$ are i.i.d. with law $\nu$.
5. $P$ is $\nu$-integrable.
6. Each $P_\ell$ is measurable and square-integrable with respect to $\nu$.
7. For all $\ell,n\in\mathbb{N}$, including $n=0$: $\mathrm{cost}_{\ell,n}$ is $\mu$-integrable and $\mathbb{E}_\mu[\mathrm{cost}_{\ell,n}]=C_\ell$. This is the same value for every $n$.
8. For every $\ell$: $\bigl|\mathbb{E}_\nu[P_\ell-P]\bigr|\le c_1\,2^{-\alpha\ell}$.
9. For every $\ell$: $\operatorname{Var}_\nu(D_\ell)\le c_2\,2^{-\beta\ell}$. For $\ell=0$ this reads $\operatorname{Var}_\nu(P_0)\le c_2$.
10. For every $\ell$: $C_\ell\le c_3\,2^{\gamma\ell}$.

Here $\ell$ is treated as a real number, and $2^{t}=e^{t\ln 2}$ has no degenerate case.

The following are not assumed:

- any relation between the functions $\mathrm{cost}_{\ell,n}$ and the maps $\omega_{\ell,n}$, whether independence or functional dependence;
- any sign or lower bound on $C_\ell$ or on the values of $\mathrm{cost}_{\ell,n}$.

All the hypotheses can hold at once, for example with $\Omega_0$ and $\Omega$ one-point spaces, $\alpha=\dots=c_3=1$, all functions identically $0$ and $C_\ell=0$. So the statement is not vacuous.

**Conclusion.** There exists a real $c_4>0$ with the following property. For every real $\varepsilon$ with $0<\varepsilon<e^{-1}$ there exist $L\in\mathbb{N}$ and a sequence $N=(N_\ell)_{\ell\in\mathbb{N}}$ of natural numbers with $N_\ell\ge1$ for **every** $\ell\in\mathbb{N}$, such that both

$$
\mathbb{E}_\mu\Bigl[\bigl(\widehat{Y}_{L,N}-\mathbb{E}_\nu[P]\bigr)^{2}\Bigr]<\varepsilon^{2}
\qquad\text{and}\qquad
\mathbb{E}_\mu\bigl[\mathrm{TC}_{L,N}\bigr]\le c_4\,B_{\alpha,\beta,\gamma}(\varepsilon).
$$

Reading notes:

- The centring constant is $\mathbb{E}_\nu[P]$, an integral over $\Omega_0$.
- The first inequality is strict and the second is non-strict.
- By hypothesis 7 and linearity, $\mathbb{E}_\mu[\mathrm{TC}_{L,N}]=\sum_{\ell=0}^{L}N_\ell\,C_\ell$.
- $L=0$ is allowed. $N_\ell$ for $\ell>L$ must be $\ge1$ but does not enter.
- Order of quantifiers: $c_4$ is chosen before $\varepsilon$, so it cannot depend on $\varepsilon$. It is chosen after all the data, so it may depend on $\mu,\nu,P,(P_\ell),(\omega_{\ell,n}),(\mathrm{cost}_{\ell,n}),(C_\ell),\alpha,\beta,\gamma,c_1,c_2,c_3$. $L$ and $N$ may depend on $\varepsilon$ and on all the data.
- Nothing is asserted for $\varepsilon\ge e^{-1}$.
- The surrounding context also declares a type $\iota$, which does not occur in this statement.

## exists_iid_inputs

**Setting and data.** $\Omega_0$ is a set carrying a σ-algebra, and $\nu$ is a probability measure on $\Omega_0$. There are no other data and no further hypotheses.

**Objects appearing.**

- $\Omega_0^{\mathbb{N}\times\mathbb{N}}$ is the set of all families $x=(x_p)_{p\in\mathbb{N}\times\mathbb{N}}$ of points of $\Omega_0$, indexed by pairs of natural numbers. It carries the product σ-algebra, the smallest σ-algebra making every coordinate map measurable.
- $\nu^{\otimes(\mathbb{N}\times\mathbb{N})}$ is the infinite product measure of copies of $\nu$ on this space. It is characterised by giving each finite-dimensional cylinder $\{x:\ x_{p_1}\in A_1,\dots,x_{p_k}\in A_k\}$ (distinct indices $p_j$, measurable $A_j\subseteq\Omega_0$) the mass $\nu(A_1)\cdots\nu(A_k)$.
- For $p\in\mathbb{N}\times\mathbb{N}$, the map $\pi_p:\Omega_0^{\mathbb{N}\times\mathbb{N}}\to\Omega_0$, $\pi_p(x)=x_p$, is the $p$-th coordinate map.

**Claim.** All three of the following hold.

1. $\nu^{\otimes(\mathbb{N}\times\mathbb{N})}$ is a probability measure, i.e. it gives the whole space mass $1$.
2. The coordinate maps $(\pi_p)_{p\in\mathbb{N}\times\mathbb{N}}$ form a mutually independent family under $\nu^{\otimes(\mathbb{N}\times\mathbb{N})}$. That is, for any finitely many distinct indices $p_1,\dots,p_k$ and measurable $A_1,\dots,A_k\subseteq\Omega_0$, the probability that $\pi_{p_j}\in A_j$ for all $j$ equals the product over $j$ of the probabilities that $\pi_{p_j}\in A_j$.
3. For every $p\in\mathbb{N}\times\mathbb{N}$, $\pi_p$ is measurable and measure-preserving from $\bigl(\Omega_0^{\mathbb{N}\times\mathbb{N}},\nu^{\otimes(\mathbb{N}\times\mathbb{N})}\bigr)$ to $(\Omega_0,\nu)$. That is, the law (image measure) of each coordinate is exactly $\nu$.

**Remarks.** The measure $\nu$ is the one supplied explicitly to this statement. The surrounding context also declares the following, none of which occurs in this statement:

- a second measurable space with a measure on it;
- an implicit measure on $\Omega_0$ that also carries the name $\nu$;
- a type $\iota$.

## giles_theorem1_iid

**Setting.** $\Omega_0$ is a set carrying a σ-algebra, and $\nu$ is a probability measure on $\Omega_0$. $\mathbb{R}$ carries its Borel σ-algebra, and $\mathbb{N}=\{0,1,2,\dots\}$.

The probability space used in the conclusion is fixed by the statement; it is not a parameter. It is built as follows:

- the underlying set is $\Omega_0^{\mathbb{N}\times\mathbb{N}}$, the set of all families $x=(x_{\ell,n})_{(\ell,n)\in\mathbb{N}\times\mathbb{N}}$ of points of $\Omega_0$, with the product σ-algebra;
- the measure is the infinite product measure $\mathbb{P}=\nu^{\otimes(\mathbb{N}\times\mathbb{N})}$ of copies of $\nu$. It gives each cylinder $\{x:\ x_{p_1}\in A_1,\dots,x_{p_k}\in A_k\}$ (distinct $p_j$, measurable $A_j$) the mass $\prod_j\nu(A_j)$. Under it the coordinates $x_{\ell,n}$ are independent, each with law $\nu$.

Integrals and variances:

- $\mathbb{E}_\nu$ and $\int\cdot\,\mathbb{P}(\mathrm{d}x)$ are Bochner integrals. By convention each is $0$ for a non-integrable integrand.
- $\operatorname{Var}_\nu(g)=\mathbb{E}_\nu\bigl[(g-\mathbb{E}_\nu[g])^2\bigr]$. By convention it is $0$ for infinite second moment.

Under the hypotheses below, every integral that occurs is of an integrable function and every variance is of a square-integrable one, so neither convention comes into play.

**Data** (arbitrary; universally quantified):

- a function $P:\Omega_0\to\mathbb{R}$;
- functions $P_\ell:\Omega_0\to\mathbb{R}$ and $\kappa_\ell:\Omega_0\to\mathbb{R}$, one of each for every $\ell\in\mathbb{N}$;
- real numbers $\alpha,\beta,\gamma,c_1,c_2,c_3$.

**Quantities built from the data (definitions expanded).**

*Level differences.* These are functions on $\Omega_0$ with $D_0=P_0$ and $D_\ell=P_\ell-P_{\ell-1}$ for $\ell\ge1$.

*Estimator and total cost.* Fix $L\in\mathbb{N}$ and a sequence $N=(N_\ell)_{\ell\in\mathbb{N}}$ of natural numbers. On $\Omega_0^{\mathbb{N}\times\mathbb{N}}$ define

$$
\widehat{Y}_{L,N}(x)=\sum_{\ell=0}^{L}\frac{1}{N_\ell}\sum_{n=0}^{N_\ell-1}D_\ell\bigl(x_{\ell,n}\bigr),
\qquad
\mathrm{TC}_{L,N}(x)=\sum_{\ell=0}^{L}\sum_{n=0}^{N_\ell-1}\kappa_\ell\bigl(x_{\ell,n}\bigr).
$$

- The $(\ell,n)$-th summand of the estimator evaluates $D_\ell$ at the coordinate $x_{\ell,n}$. For $\ell\ge1$, this means evaluating both $P_\ell$ and $P_{\ell-1}$ at that coordinate.
- The $(\ell,n)$-th cost is $\kappa_\ell$ evaluated at that same coordinate.
- The prefactor is literally $N_\ell^{-1}$, with the convention $0^{-1}=0$. In the conclusion every $N_\ell\ge1$, so this convention does not come into play.

*Auxiliary function.* For $\varepsilon>0$,

$$
B_{\alpha,\beta,\gamma}(\varepsilon)=
\begin{cases}
\varepsilon^{-2} & \text{if } \gamma<\beta,\\
\varepsilon^{-2}\,(\ln\varepsilon)^{2} & \text{if } \gamma=\beta,\\
\varepsilon^{-2-(\gamma-\beta)/\alpha} & \text{if } \gamma>\beta.
\end{cases}
$$

It is evaluated only at $0<\varepsilon<e^{-1}$. There the powers are ordinary real powers of a positive number, $\ln$ is the natural logarithm with $\ln\varepsilon<-1$, and $\alpha>0$.

**Hypotheses.**

1. $\alpha,\beta,\gamma,c_1,c_2,c_3>0$.
2. $\tfrac12\min(\beta,\gamma)\le\alpha$.
3. $P$ is $\nu$-integrable.
4. Each $P_\ell$ is measurable and square-integrable with respect to $\nu$.
5. Each $\kappa_\ell$ is $\nu$-integrable. Nothing further is assumed about its measurability, and no sign condition is imposed.
6. For every $\ell$: $\bigl|\mathbb{E}_\nu[P_\ell-P]\bigr|\le c_1\,2^{-\alpha\ell}$.
7. For every $\ell$: $\operatorname{Var}_\nu(D_\ell)\le c_2\,2^{-\beta\ell}$. For $\ell=0$ this reads $\operatorname{Var}_\nu(P_0)\le c_2$.
8. For every $\ell$: $\mathbb{E}_\nu[\kappa_\ell]\le c_3\,2^{\gamma\ell}$.

Here $\ell$ is treated as a real number, and $2^{t}=e^{t\ln 2}$ has no degenerate case. All the hypotheses can hold at once, for example with $\alpha=\dots=c_3=1$ and $P$, $P_\ell$, $\kappa_\ell$ all identically $0$. So the statement is not vacuous.

**Conclusion.** There exists a real $c_4>0$ with the following property. For every real $\varepsilon$ with $0<\varepsilon<e^{-1}$ there exist $L\in\mathbb{N}$ and a sequence $N=(N_\ell)_{\ell\in\mathbb{N}}$ of natural numbers with $N_\ell\ge1$ for **every** $\ell\in\mathbb{N}$, such that both

$$
\int\bigl(\widehat{Y}_{L,N}(x)-\mathbb{E}_\nu[P]\bigr)^{2}\,\mathbb{P}(\mathrm{d}x)<\varepsilon^{2}
\qquad\text{and}\qquad
\int\mathrm{TC}_{L,N}(x)\,\mathbb{P}(\mathrm{d}x)\le c_4\,B_{\alpha,\beta,\gamma}(\varepsilon).
$$

Reading notes:

- The first inequality is strict and the second is non-strict.
- The expected total cost on the left of the second inequality equals $\sum_{\ell=0}^{L}N_\ell\,\mathbb{E}_\nu[\kappa_\ell]$.
- $L=0$ is allowed. $N_\ell$ for $\ell>L$ must be $\ge1$ but does not enter.
- Order of quantifiers: $c_4$ is chosen before $\varepsilon$, so it cannot depend on $\varepsilon$. It may depend on $\nu,P,(P_\ell),(\kappa_\ell),\alpha,\beta,\gamma,c_1,c_2,c_3$. $L$ and $N$ may depend on $\varepsilon$ and on all the data.
- Nothing is asserted for $\varepsilon\ge e^{-1}$.
- The measure $\nu$ is the one supplied explicitly to this statement. The surrounding context also declares a second measurable space with a measure on it, an implicit measure on $\Omega_0$ that also carries the name $\nu$, and a type $\iota$. None of these occurs in this statement.

## optimal_cost_isLeast

**Setting and data.** $\iota$ is an arbitrary index set, which may be infinite. $s\subseteq\iota$ is a finite subset, $V,C:\iota\to\mathbb{R}$ are arbitrary functions, and $\tau$ is a real number.

**Hypotheses.**

1. $\tau>0$.
2. $V_i>0$ for every $i\in s$.
3. $C_i>0$ for every $i\in s$.

The values of $V$ and $C$ outside $s$ are unconstrained and do not enter.

**Claim.** Let

$$
\mathcal{A}=\Bigl\{\,c\in\mathbb{R}\;:\;\text{there is } n:\iota\to\mathbb{R}\text{ with } n_i>0\text{ for all } i\in s,\ \ \sum_{i\in s}\frac{V_i}{n_i}\le\tau,\ \text{ and }\ c=\sum_{i\in s}n_i\,C_i\Bigr\}
$$

and

$$
c^{\ast}=\frac{1}{\tau}\Bigl(\sum_{i\in s}\sqrt{V_i\,C_i}\Bigr)^{2}.
$$

The statement asserts that $c^{\ast}$ is the least element of $\mathcal{A}$. That is, both of the following hold:

- (attained) $c^{\ast}\in\mathcal{A}$: there exists $n:\iota\to\mathbb{R}$ with $n_i>0$ for all $i\in s$, $\sum_{i\in s}V_i/n_i\le\tau$, and $\sum_{i\in s}n_iC_i=c^{\ast}$;
- (lower bound) for every $n:\iota\to\mathbb{R}$ with $n_i>0$ for all $i\in s$ and $\sum_{i\in s}V_i/n_i\le\tau$, one has $\sum_{i\in s}n_iC_i\ge c^{\ast}$.

**Reading notes.**

- The $n_i$ are arbitrary positive real numbers; they are not required to be integers. The values $n_i$ for $i\notin s$ are irrelevant.
- The constraint $\sum V_i/n_i\le\tau$ is non-strict.
- All operations are non-degenerate: division is only by $n_i>0$ ($i\in s$), square roots are taken of the positive numbers $V_iC_i$, and $\tau^{-1}=1/\tau$ with $\tau>0$.
- If $s=\varnothing$, then $\mathcal{A}=\{0\}$ and $c^{\ast}=0$.
- The context contains an auxiliary definition equal to $\sum_{i\in s}\sqrt{V_iC_i}$. The statement writes this sum out directly rather than using that definition.
