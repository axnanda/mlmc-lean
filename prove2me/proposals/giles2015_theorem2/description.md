## Motivation

In multilevel Monte Carlo (MLMC) the approximations of a random quantity $P$ form a single sequence $P_0, P_1, \dots$ indexed by one level $\ell$. Many simulations have several discretisation parameters that can be refined independently: the mesh widths in each spatial direction of an elliptic PDE, time step and mesh width in a parabolic SPDE, or time step and number of inner samples in a nested simulation. Refining them all together, as one MLMC level, can cost far more than refining them separately. **Multi-Index Monte Carlo (MIMC)**, introduced by Haji-Ali, Nobile and Tempone, indexes the approximations by a vector $\boldsymbol{\ell} \in \mathbb{N}^D$ and combines differences taken in all directions at once ([Giles 2015](https://doi.org/10.1017/S096249291500001X), §2.4; [Haji-Ali, Nobile, Tempone](https://arxiv.org/abs/1405.3757)).

Giles' survey states the MIMC complexity theorem (Theorem 2) in a form parallel to the MLMC theorem (Theorem 1). For an elliptic PDE or SPDE in $D$ spatial dimensions, the MLMC variance rate $\beta$ is usually independent of $D$ while the cost rate $\gamma$ increases at least linearly with $D$, so in a high enough dimension $\beta \le \gamma$ and MLMC does not reach the optimal $O(\varepsilon^{-2})$ complexity; with MIMC one can have $\beta_d > \gamma_d$ in every direction and obtain it (pp. 15–16).

Timeline:

- **2008**, Giles: MLMC for path simulation; **2011**, Cliffe, Giles, Scheichl, Teckentrup: the MLMC complexity theorem in the form of Theorem 1.
- **2014**, Haji-Ali, Nobile and Tempone: Multi-Index Monte Carlo and its complexity theorem, with the optimal index sets ([arXiv:1405.3757](https://arxiv.org/abs/1405.3757)).
- **2015**, Giles: Theorem 2, the MIMC theorem restated to match the MLMC theorem.

## Setting

Let $(\Omega, \mathcal{F}, \mu)$ be a probability space, $D \ge 1$, $P$ an integrable random variable and $P_{\boldsymbol{\ell}}$, $\boldsymbol{\ell} = (\ell_1, \dots, \ell_D) \in \mathbb{N}^D$, integrable approximations of $P$. With $\mathbf{e}_d$ the $d$-th unit vector, the **backward difference** in direction $d$ is $\Delta_d P_{\boldsymbol{\ell}} = P_{\boldsymbol{\ell}} - P_{\boldsymbol{\ell} - \mathbf{e}_d}$, with $P_{\boldsymbol{\ell} - \mathbf{e}_d} = 0$ when $\ell_d = 0$, and the **cross-difference** is
$$
\boldsymbol{\Delta} P_{\boldsymbol{\ell}} = \Big(\prod_{d=1}^{D} \Delta_d\Big) P_{\boldsymbol{\ell}},
$$
a signed combination of up to $2^D$ values (for $D = 2$, $\boldsymbol{\Delta} P_{(5,4)}$ uses $P$ at $(5,4), (4,4), (5,3), (4,3)$; Figure 2.1). The cross-differences telescope: summed over a box $\{\boldsymbol{\ell} \le \mathbf{k}\}$ they give $P_{\mathbf{k}}$.

For each index $\boldsymbol{\ell}$ and number of samples $n \ge 1$ let $Y_{\boldsymbol{\ell},n}$ be a square-integrable estimator with variance $V_{\boldsymbol{\ell}}/n$ and random cost of expectation $n\,C_{\boldsymbol{\ell}}$, independent across indices. For a finite **index set** $\mathcal{L} \subset \mathbb{N}^D$ and sample sizes $N_{\boldsymbol{\ell}} \ge 1$ the estimator is $Y = \sum_{\boldsymbol{\ell} \in \mathcal{L}} Y_{\boldsymbol{\ell}, N_{\boldsymbol{\ell}}}$. With positive vectors $\boldsymbol{\alpha}, \boldsymbol{\beta}, \boldsymbol{\gamma} \in \mathbb{R}^D$, $\alpha_d \ge \tfrac12 \beta_d$, positive constants $c_1, c_2, c_3$, and $\mathbf{a} \cdot \boldsymbol{\ell} = \sum_d a_d \ell_d$, the conditions are (with Giles' labels):

1. i) $\big|\mathbb{E}[P_{\boldsymbol{\ell}} - P]\big| \to 0$ as $\min_d \ell_d \to \infty$;
2. iii) $\mathbb{E}[Y_{\boldsymbol{\ell},n}] = \mathbb{E}[\boldsymbol{\Delta} P_{\boldsymbol{\ell}}]$;
3. ii) $\big|\mathbb{E}[Y_{\boldsymbol{\ell},n}]\big| \le c_1 2^{-\boldsymbol{\alpha} \cdot \boldsymbol{\ell}}$;
4. iv) $V_{\boldsymbol{\ell}} \le c_2 2^{-\boldsymbol{\beta} \cdot \boldsymbol{\ell}}$;
5. v) $C_{\boldsymbol{\ell}} \le c_3 2^{\boldsymbol{\gamma} \cdot \boldsymbol{\ell}}$.

The complexity is governed by
$$
\eta = \max_{d} \frac{\gamma_d - \beta_d}{\alpha_d}, \qquad D_2 = \#\Big\{ d : \frac{\gamma_d - \beta_d}{\alpha_d} = \eta \Big\}.
$$

## Formalization targets

### Goal: Theorem 2, as stated in the paper

For $\alpha_d \ge \tfrac12 \beta_d$ there are exponents $e_1, e_2$, depending only on $\boldsymbol{\alpha}, \boldsymbol{\beta}, \boldsymbol{\gamma}$, with $e_1 = 2D_2$ and $e_2 = (D_2 - 1)(2 + \eta)$ when $\alpha_d > \tfrac12 \beta_d$ for every $d$, such that under the conditions above there is $c_4 > 0$ for which, for every $0 < \varepsilon < e^{-1}$, there are a finite index set $\mathcal{L}$ and integers $N_{\boldsymbol{\ell}} \ge 1$ with $\mathbb{E}\big[(Y - \mathbb{E}[P])^2\big] < \varepsilon^2$ and
$$
\mathbb{E}[C] \le
\begin{cases}
c_4\, \varepsilon^{-2}, & \eta < 0,\\
c_4\, \varepsilon^{-2} |\log \varepsilon|^{e_1}, & \eta = 0,\\
c_4\, \varepsilon^{-2-\eta} |\log \varepsilon|^{e_2}, & \eta > 0.
\end{cases}
$$
The paper gives the exponents only when every $\alpha_d > \tfrac12 \beta_d$ and notes that "the form of the exponents is more complicated when $\alpha_d = \tfrac12 \beta_d$ for some $d$"; the goal states exactly this.

### Further targets (milestones)

- §2.4, the telescoping identity over boxes: $\sum_{\boldsymbol{\ell} \le \mathbf{k}} \boldsymbol{\Delta} P_{\boldsymbol{\ell}} = P_{\mathbf{k}}$ for every $\mathbf{k} \in \mathbb{N}^D$.
- §2.4, the telescoping sum $\mathbb{E}[P] = \sum_{\boldsymbol{\ell} \ge \mathbf{0}} \mathbb{E}[\boldsymbol{\Delta} P_{\boldsymbol{\ell}}]$, as an absolutely convergent series under conditions i)–iii).
- Theorem 2 when $\alpha_d > \tfrac12 \beta_d$ for every $d$, with the paper's exponents $e_1 = 2D_2$, $e_2 = (D_2 - 1)(2 + \eta)$.
- Theorem 2 when $\alpha_d = \tfrac12 \beta_d$ for some $d$, with explicit exponents: the linked formal version proves the bound with $e_1 = 2D_2 + (D_3 - 3)^+$ and $e_2 = (D_2 - 1)(2 + \eta) + (D_3 - 1)^+$, where $D_3 = \#\{d : \alpha_d = \tfrac12 \beta_d\}$ and $x^+ = \max(x, 0)$; for $D_3 = 0$ these are the paper's exponents. They are this formalization's and are not claimed to be sharp. This case matters in practice: Giles' own MIMC example (§9.2, p. 60) has $\boldsymbol{\alpha} = (1,1)$ and $\boldsymbol{\beta} = (2,2)$, so $\alpha_d = \tfrac12\beta_d$ in both directions.

## Significance

*The result.* Theorem 2 gives the cost of MIMC in terms of per-direction rates. When $\beta_d > \gamma_d$ in every direction, $\eta < 0$ and the cost is $O(\varepsilon^{-2})$, the optimal complexity that standard MLMC loses in high dimension; Giles describes this as the possibility of dimension-independent complexity for SPDEs and other high-dimensional stochastic applications, in the same way as sparse grids for deterministic PDEs (pp. 15–16).

*Formalizing it.* The statements in this mission already have machine-checked proofs on this platform (the linked theorems are Proved), from a Lean 4 development against Mathlib `0df444a` with no `sorry`. The formal version covers every $D \ge 1$, all three regimes and the full hypothesis $\alpha_d \ge \tfrac12 \beta_d$, with the paper's exponents $e_1 = 2D_2$, $e_2 = (D_2 - 1)(2+\eta)$ when every $\alpha_d > \tfrac12 \beta_d$. The case $\alpha_d = \tfrac12 \beta_d$ is covered with explicit exponents that reduce to the paper's when no direction is on the boundary; sharp exponents in that case are open for formalization, as are shorter proofs and the rate conditions for concrete PDE discretisations.

## Difficulty

The obvious generalisation of the MLMC argument, with a rectangular index set, gives the optimal complexity only when $\eta < 0$ and $\sum_d \gamma_d / \alpha_d \le 2$ (p. 15); the stated bounds need a simplex-shaped index set $\{\boldsymbol{\ell} : \boldsymbol{\ell} \cdot \mathbf{n} \le L\}$ with a direction vector $\mathbf{n}$ chosen from the rates. The work is then in counting: sums of exponentials over the lattice points of such a simplex and over its complement, whose polynomial factors in $L$ produce the powers of $|\log \varepsilon|$, and whose exponents must come out exactly as $2D_2$ and $(D_2 - 1)(2 + \eta)$. The directions attaining $\eta$ behave differently from the others, and the bias condition is on cross-differences, so the bias of a truncated index set is a sum over the infinite complement of $\mathcal{L}$, not a single term as in MLMC.

## Formalization scope

- Indices are functions $\mathrm{Fin}\,D \to \mathbb{N}$ with $D \ge 1$; the cross-difference is defined by recursion on $D$, with the difference in direction $d$ taken as $P_{\boldsymbol{\ell}}$ alone when $\ell_d = 0$.
- The probabilistic setting is that of Theorem 1: $\mu$ a probability measure, integrable $P$ and $P_{\boldsymbol{\ell}}$, estimators $Y_{\boldsymbol{\ell},n}$ in $L^2$ and all conditions for $n \ge 1$, pairwise independence across indices for every choice of sample sizes $N \ge 1$, random costs with expectation $n\,C_{\boldsymbol{\ell}}$, and the strict bound $\mathrm{MSE} < \varepsilon^2$ for $0 < \varepsilon < e^{-1}$.
- Condition i) is the limit along $\min_d \ell_d \to \infty$: for every $\delta > 0$ there is $n_0$ with $|\mathbb{E}[P_{\boldsymbol{\ell}} - P]| < \delta$ whenever all $\ell_d \ge n_0$.
- No trivial reading: $c_4$ is fixed before $\varepsilon$, the index set is finite, and every $N_{\boldsymbol{\ell}} \ge 1$.
- Reusable parts: the cross-difference and its telescoping over boxes, and bounds for exponential sums over lattice simplices $\{\boldsymbol{\theta} \cdot \boldsymbol{\ell} \le L\}$ and their complements.

## Selected references

- M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), 259–328, §2.4. [doi:10.1017/S096249291500001X](https://doi.org/10.1017/S096249291500001X)
- A.-L. Haji-Ali, F. Nobile, R. Tempone, *Multi-index Monte Carlo: when sparsity meets sampling*, Numerische Mathematik 132 (2016), 767–806. [arXiv:1405.3757](https://arxiv.org/abs/1405.3757)
- K.A. Cliffe, M.B. Giles, R. Scheichl, A.L. Teckentrup, *Multilevel Monte Carlo methods and applications to elliptic PDEs with random coefficients*, Computing and Visualization in Science 14 (2011), 3–15. [doi:10.1007/s00791-011-0160-x](https://doi.org/10.1007/s00791-011-0160-x)
