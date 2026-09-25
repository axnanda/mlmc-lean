## Motivation

Many quantities in computational finance and uncertainty quantification are expectations $\mathbb{E}[P]$ of a random variable $P$ that cannot be sampled exactly: the discounted payoff of an option on the solution of a stochastic differential equation, or a functional of the solution of a partial differential equation with random coefficients. One samples instead an approximation $P_L$, computed with a time step or mesh width that shrinks as $L$ grows. **Standard Monte Carlo** averages independent samples of $P_L$; a root-mean-square error $\varepsilon$ needs $O(\varepsilon^{-2})$ samples, and each sample of a sufficiently accurate $P_L$ costs more as $\varepsilon \to 0$.

The **multilevel Monte Carlo (MLMC)** method estimates $\mathbb{E}[P_L]$ through the telescoping sum $\mathbb{E}[P_L] = \mathbb{E}[P_0] + \sum_{\ell=1}^{L} \mathbb{E}[P_\ell - P_{\ell-1}]$, sampling each term independently: many cheap samples on coarse levels, few expensive samples on fine levels. Theorem 1 of Giles' survey in *Acta Numerica* is the standard statement of what this gains: the cost to reach accuracy $\varepsilon$, in terms of three rates. It is the reference result by which MLMC methods for SDEs, PDEs and continuous-time Markov chains are analysed ([Giles 2015](https://doi.org/10.1017/S096249291500001X), §2.1).

Timeline, as recorded in [Giles 2015](https://doi.org/10.1017/S096249291500001X), §1.4 and p. 7:

- **1998–2006**, Heinrich: multilevel Monte Carlo for parametric integration, with a complexity analysis close to Theorem 1.
- **2005**, Kebaier: a two-level method for path simulation.
- **2008**, Giles: multilevel Monte Carlo path simulation for SDEs, with the original complexity theorem ([Giles 2008](https://doi.org/10.1287/opre.1070.0496)).
- **2011**, Cliffe, Giles, Scheichl and Teckentrup: the theorem and proof in the present form, for elliptic PDEs with random coefficients.
- **2015**, Giles: the present statement, with expected costs, so that the cost of an individual sample may itself be random.

## Setting

Let $(\Omega, \mathcal{F}, \mu)$ be a probability space, $P$ an integrable random variable and $P_0, P_1, P_2, \dots$ integrable approximations of $P$. For each level $\ell \ge 0$ and each number of samples $n \ge 1$ let $Y_{\ell,n}$ be a square-integrable **level estimator** built from $n$ Monte Carlo samples, with variance $V_\ell / n$, where $V_\ell$ is the variance of one sample, and with a random computational cost $\mathrm{Cost}_{\ell,n}$ of expectation $n\,C_\ell$, where $C_\ell$ is the expected cost of one sample. Estimators on different levels are independent. For a finest level $L$ and sample sizes $N_0, \dots, N_L \ge 1$ the **multilevel estimator** and its cost are
$$
Y = \sum_{\ell=0}^{L} Y_{\ell, N_\ell}, \qquad C = \sum_{\ell=0}^{L} \mathrm{Cost}_{\ell, N_\ell},
$$
and its **mean-square error** is $\mathrm{MSE} = \mathbb{E}\big[(Y - \mathbb{E}[P])^2\big]$.

The hypotheses are four rate conditions with positive constants $\alpha, \beta, \gamma, c_1, c_2, c_3$ and $\alpha \ge \tfrac12 \min(\beta, \gamma)$:

1. (i) weak error: $\big|\mathbb{E}[P_\ell - P]\big| \le c_1 2^{-\alpha \ell}$;
2. (ii) unbiasedness: $\mathbb{E}[Y_{0,n}] = \mathbb{E}[P_0]$ and $\mathbb{E}[Y_{\ell,n}] = \mathbb{E}[P_\ell - P_{\ell-1}]$ for $\ell \ge 1$;
3. (iii) variance decay: $V_\ell \le c_2 2^{-\beta \ell}$;
4. (iv) cost growth: $C_\ell \le c_3 2^{\gamma \ell}$.

The natural level estimator is the sample mean (2.2), $Y_{\ell,N_\ell} = N_\ell^{-1} \sum_{n=1}^{N_\ell} \big(P_\ell^{(\ell,n)} - P_{\ell-1}^{(\ell,n)}\big)$ with $P_{-1} \equiv 0$, where the superscript $(\ell, n)$ marks independent samples.

## Formalization targets

### Goal: Theorem 1

There is a constant $c_4 > 0$ such that for every $0 < \varepsilon < e^{-1}$ there are a level $L$ and integers $N_\ell \ge 1$ for which $\mathrm{MSE} < \varepsilon^2$ and
$$
\mathbb{E}[C] \le
\begin{cases}
c_4\, \varepsilon^{-2}, & \beta > \gamma,\\
c_4\, \varepsilon^{-2} (\log \varepsilon)^2, & \beta = \gamma,\\
c_4\, \varepsilon^{-2-(\gamma-\beta)/\alpha}, & \beta < \gamma.
\end{cases}
$$
The constant $c_4$ is fixed before $\varepsilon$; the goal asserts the shape of the bound, not a value of $c_4$.

### The numbered equations behind it (milestones)

- (2.1): $\mathrm{MSE} = \mathbb{V}[Y] + \big(\mathbb{E}[Y] - \mathbb{E}[P]\big)^2$.
- (2.3): $\mathbb{E}[Y] = \mathbb{E}[P_L]$ and $\mathbb{V}[Y] = \sum_{\ell=0}^{L} N_\ell^{-1} V_\ell$.
- (1.1): for a variance target $\varepsilon^2$, the least total cost $\sum_\ell N_\ell C_\ell$ over real $N_\ell > 0$ is $\varepsilon^{-2}\big(\sum_\ell \sqrt{V_\ell C_\ell}\big)^2$.
- (2.2): the sample-mean estimator satisfies (ii), $\mathbb{V}[Y_{\ell,N}] = V_\ell/N$ and independence across levels, so Theorem 1 applies to it.

## Significance

*The result.* Theorem 1 converts three measurable rates into the cost of the whole method. With $\beta > \gamma$ the cost is $O(\varepsilon^{-2})$, the order of Monte Carlo with i.i.d. samples of bounded cost, whereas standard Monte Carlo on the finest level costs about $\varepsilon^{-2} V_0 C_L$ with $C_L = O(\varepsilon^{-\gamma/\alpha})$ (§1.3 and p. 7). With $\beta < \gamma$ and $\beta = 2\alpha$ the cost is $O(C_L)$, that of $O(1)$ samples on the finest level (p. 7). The theorem determines how $L$ and the $N_\ell$ are chosen, and it is the template for later results: multi-index Monte Carlo (Theorem 2 of the same paper) and randomised, unbiased MLMC (§2.2).

*Formalizing it.* Every statement in this mission already has a machine-checked proof on this platform: the linked theorems are Proved, from a Lean 4 development against Mathlib `0df444a`, with no `sorry` and only the standard axioms. The formal statements go slightly beyond the paper: the cost bound holds for random costs, the conditions are required only for sample sizes $N_\ell \ge 1$, and the theorem is also proved for the estimator (2.2) built from independent inputs, where unbiasedness, the variance formula and independence across levels are consequences rather than hypotheses. Contributions welcome: shorter or more structural proofs, explicit constants $c_4$, and formal proofs of the rate conditions (i)–(iv) for concrete discretisations, which are open.

## Difficulty

The equation (1.1) comes from a Lagrange-multiplier argument that treats the $N_\ell$ as real numbers; it produces a stationary point, not a proven minimum, and the theorem needs integers. Rounding each $N_\ell$ up adds a cost of order $\sum_{\ell \le L} C_\ell$, which is of order $\varepsilon^{-\gamma/\alpha}$ and is not automatically dominated by the main term: this is where the hypothesis $\alpha \ge \tfrac12 \min(\beta,\gamma)$ is needed, and without it the bound fails. The three regimes also need estimates that are uniform in $\varepsilon$, with $L$ an integer that jumps as $\varepsilon$ varies, and the logarithmic factor in the case $\beta = \gamma$ must come out with exponent exactly $2$.

On the probabilistic side, conditions (ii) and $\mathbb{V}[Y_{\ell,N}] = V_\ell/N$ are properties of the estimator (2.2). Deriving them needs independence of the samples within and across levels, which does not follow from a list of per-level hypotheses.

## Formalization scope

- $\Omega$ carries a probability measure; $P$ and the $P_\ell$ are integrable real random variables; each $Y_{\ell,n}$ is in $L^2$; expectations are Bochner integrals. The estimators $Y_{\ell,n}$ are given for every $n$, and conditions (ii), the variance identity and the cost identity are required for $n \ge 1$ (the sample mean with no samples is $0$ and is not unbiased).
- Independence across levels is pairwise independence of $Y_{i,N_i}$ and $Y_{j,N_j}$ for $i \ne j$ and every choice of sample sizes $N \ge 1$.
- The error target is the strict inequality $\mathrm{MSE} < \varepsilon^2$ and $\varepsilon$ ranges over $(0, e^{-1})$; powers with real exponents are real powers of positive reals.
- No trivial reading: $c_4$ is quantified before $\varepsilon$, every $N_\ell \ge 1$, and the cost is the expectation of the sum of the random level costs, so neither a zero estimator nor an $\varepsilon$-dependent constant satisfies the goal.
- Reusable parts: the Cauchy–Schwarz form of the optimal allocation, the variance of a sum of pairwise independent estimators, and the sample-mean estimator on a product of independent copies of a probability space.

## Selected references

- M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), 259–328. [doi:10.1017/S096249291500001X](https://doi.org/10.1017/S096249291500001X)
- M.B. Giles, *Multilevel Monte Carlo path simulation*, Operations Research 56(3) (2008), 607–617. [doi:10.1287/opre.1070.0496](https://doi.org/10.1287/opre.1070.0496)
- K.A. Cliffe, M.B. Giles, R. Scheichl, A.L. Teckentrup, *Multilevel Monte Carlo methods and applications to elliptic PDEs with random coefficients*, Computing and Visualization in Science 14 (2011), 3–15. [doi:10.1007/s00791-011-0160-x](https://doi.org/10.1007/s00791-011-0160-x)
- S. Heinrich, *Multilevel Monte Carlo methods*, in Large-Scale Scientific Computing, Lecture Notes in Computer Science 2179, Springer (2001), 58–67. [doi:10.1007/3-540-45346-6_5](https://doi.org/10.1007/3-540-45346-6_5)
- A. Kebaier, *Statistical Romberg extrapolation: a new variance reduction method and applications to option pricing*, Annals of Applied Probability 15(4) (2005), 2681–2705. [doi:10.1214/105051605000000511](https://doi.org/10.1214/105051605000000511)
