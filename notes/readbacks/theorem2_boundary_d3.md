# Blind read-back — packet 4

Declarations (all in namespace `MLMC`): `mimc_extra_term`, `mimc_complexity_core`, `mimc_complexity_boundary`, `giles_theorem2_boundary`.

Inputs used: the packet (statements + definitions + context header), the auditor guidance, Mathlib source, and the Lean-core source of the `binop%` elaborator (`Lean/Elab/Extra.lean`, Lean v4.33.1). No other project file was read. See the method note at the end for how the elaboration claims were checked.

---

## 0. Shared notation and expanded definitions

- $\mathbb N=\{0,1,2,\dots\}$. Coordinates are indexed by $d\in\{0,1,\dots,D-1\}$. A *multi-index* is $\ell=(\ell_0,\dots,\ell_{D-1})\in\mathbb N^D$, and $e_d$ is the $d$-th unit multi-index. "Finite set of multi-indices" means a finite subset of $\mathbb N^D$.
- $\log$ is the natural logarithm. For real $x>0$ and real $y$, $x^{y}=e^{y\log x}$ is Mathlib's real power. Its conventions for bases $\le 0$ never come into play; see the edge-case paragraphs. $x^{n}$ with $n\in\mathbb N$ is the ordinary power.
- $\max(m-n,0)$ denotes natural-number subtraction truncated at $0$ (Lean's `m - n` on `ℕ`).
- **`dot`**: for $a\in\mathbb R^D$ and $\ell\in\mathbb N^D$, $\;a\cdot\ell:=\sum_{d=0}^{D-1}a_d\,\ell_d$, with each $\ell_d$ cast to $\mathbb R$.
- **`crit`**: for $\delta\in\mathbb R^D$, $\;\operatorname{crit}(\delta):=\#\{d:\ \delta_d=0\}\in\{0,\dots,D\}$.
- **`indexSet`**: for $\theta\in\mathbb R^D$ and $L\in\mathbb R$,
  $$I(\theta,L):=\Big\{\ell\in\mathbb N^D:\ \ell_d\le\big\lfloor L/\theta_d\big\rfloor_{\mathbb N}\ \text{for every }d,\ \text{and}\ \theta\cdot\ell\le L\Big\}.$$
  Here $\lfloor x\rfloor_{\mathbb N}$ is the natural-number floor, which is $0$ for $x<0$, and Lean's division convention gives $L/0=0$. If every $\theta_d>0$ and $L\ge0$, the box constraint follows from $\theta\cdot\ell\le L$, because $\theta_d\ell_d\le\theta\cdot\ell$. Then $I(\theta,L)=\{\ell\in\mathbb N^D:\ \theta\cdot\ell\le L\}$.
- **`crossDiff`** (used only by `giles_theorem2_boundary`): defined by recursion on $D$. For $D=0$, $\Delta p=p$. For $D\ge1$,
  $$\Delta p(\ell)=\Delta\big[p(\ell_0,\cdot)\big](\ell_1,\dots,\ell_{D-1})-\begin{cases}0,&\ell_0=0,\\ \Delta\big[p(\ell_0-1,\cdot)\big](\ell_1,\dots,\ell_{D-1}),&\ell_0\ge1.\end{cases}$$
  Unrolled, this is
  $$\Delta p(\ell)=\sum_{S\subseteq\{d:\ \ell_d\ge1\}}(-1)^{|S|}\;p\Big(\ell-\sum_{d\in S}e_d\Big),$$
  that is, the product of first-order backward differences in every direction, where no difference is taken in a direction with $\ell_d=0$. For example, $\Delta p(0)=p(0)$. For $D=1$ and $\ell\ge1$, $\Delta p(\ell)=p(\ell)-p(\ell-1)$. The natural subtraction $\ell_0-1$ in the definition is evaluated only when $\ell_0\ge1$, so no truncation occurs.
- **`mimcEta`, `mimcD2`** (defined under `[NeZero D]`, i.e. $D\ge1$):
  $$\eta:=\max_{d}\frac{\gamma_d-\beta_d}{\alpha_d},\qquad d_2:=\#\Big\{d:\ \frac{\gamma_d-\beta_d}{\alpha_d}=\eta\Big\}.$$
  `Finset.sup'` over the nonempty set of coordinates is a genuine maximum, and it is attained. Hence $1\le d_2\le D$ always.
- **`mimcD3`**: $\;d_3:=\#\{d:\ \alpha_d=\beta_d/2\}\in\{0,\dots,D\}$.
- **`mimcBound`**: for real $\eta,e_1,e_2,\varepsilon$ (all powers are real powers),
  $$B(\eta,e_1,e_2,\varepsilon):=\begin{cases}\varepsilon^{-2},&\eta<0,\\[2pt] \varepsilon^{-2}\,|\log\varepsilon|^{e_1},&\eta=0,\\[2pt] \varepsilon^{-2-\eta}\,|\log\varepsilon|^{e_2},&\eta>0.\end{cases}$$
  Only one of $e_1,e_2$ is ever used, and neither is used when $\eta<0$. For $0<\varepsilon<e^{-1}$ we have $|\log\varepsilon|=-\log\varepsilon=\log(1/\varepsilon)>1$.
- The packet also defines `box`, but none of the four statements uses it.

**Elaboration rule used throughout.** In a real-valued arithmetic expression that mixes natural-number terms with real ones, Lean's `binop%` elaborator fixes $\mathbb R$ as the "maximal type". It does so from the expected type $\mathbb R$ of an argument slot, or from any real leaf. It then casts each natural-number *leaf* to $\mathbb R$ and does the arithmetic, including subtraction, in $\mathbb R$.

An explicit ascription `((e : ℕ) : ℝ)` works differently: $e$ is evaluated in $\mathbb N$, with truncated subtraction, and only the result is cast.

The exponent of `^` is elaborated as a separate leaf with no expected type (`rightact%`). Its own leaves decide its type.

---

## mimc_extra_term

**Setting / data.** All of the following are universally quantified.

- $D\in\mathbb N$ (implicit). The packet's context header puts no `[NeZero D]` in scope for this lemma, so $D=0$ is allowed.
- $\theta,\gamma\in\mathbb R^D$ (implicit).
- $a,\,c,\,c_3,\,K_P,\,K_L\in\mathbb R$ (implicit).
- $p\in\mathbb N$ (implicit).

**Hypotheses.**

1. (`hθ`) $\theta_d>0$ for every $d$.
2. (`ha`) $a>0$.
3. (`hc`) $c>0$.
4. (`hc₃`) $c_3>0$.
5. (`hK_P`) $K_P>0$.
6. (`hK_L`) $K_L>0$.
7. (`hγ`) $\gamma_d\le c\,\theta_d$ for every $d$. There is no sign condition on $\gamma$.

**Conclusion.** Put $\kappa:=\operatorname{crit}(c\theta-\gamma)=\#\{d:\ \gamma_d=c\,\theta_d\}$. Then

$$\exists\,K_E\in\mathbb R,\ K_E\ge0,\quad\forall\,\varepsilon\in\mathbb R\ \ \forall\,L\in\mathbb N:\qquad
\left.\begin{aligned}&\varepsilon>0,\\ &2^{\,aL}\le\frac{K_P\,(1+L)^{p}}{\varepsilon},\\ &1+L\le K_L\,(-\log\varepsilon)\end{aligned}\right\}
\ \Longrightarrow\
c_3\!\!\sum_{\substack{\ell\in\mathbb N^D:\ \ell_d\le\lfloor L/\theta_d\rfloor\ \forall d,\\ \sum_d\theta_d\ell_d\le L}}\!\! 2^{\sum_d\gamma_d\ell_d}
\ \le\ K_E\,(-\log\varepsilon)^{\max(\kappa-1,\,0)\,+\,p\,c/a}\;\varepsilon^{-c/a}.$$

- By Hypothesis 1 and $L\ge0$, the summation range is exactly $\{\ell\in\mathbb N^D:\ \sum_d\theta_d\ell_d\le L\}$.
- Quantifier order: $K_E$ comes after all the data $(D,\theta,\gamma,a,c,c_3,K_P,K_L,p)$ and may depend on them. It is one constant for all pairs $(\varepsilon,L)$ that satisfy the three premises. The premises are chained implications, which is equivalent to their conjunction.

**Casts and truncations.**

- The first part of the exponent of $-\log\varepsilon$ is written `((crit (…) - 1 : ℕ) : ℝ)`. This is a truncated natural subtraction, then a cast, so it equals $\max(\kappa-1,0)$. When $\kappa=0$ it contributes $0$, not $-1$.
- In `p * (c / a)` the product is real, so $p$ is cast to $\mathbb R$.
- In `(2 : ℝ) ^ (a * L)` the exponent is $a\cdot L$ with $L$ cast to $\mathbb R$, and $2^{aL}$ is a real power.
- `(1 + (L : ℝ)) ^ p` is the ordinary power with natural exponent $p$; it equals $1$ when $p=0$. The expression `K_P * (1+L)^p / ε` means $(K_P(1+L)^p)/\varepsilon$.
- `indexSet θ L` receives $L$ cast to $\mathbb R$. The floors are natural floors of $L/\theta_d\ge0$.
- $2^{\gamma\cdot\ell}$, $(-\log\varepsilon)^{(\cdot)}$ and $\varepsilon^{-c/a}$ are real powers.

**Edge cases / vacuity.**

- The premises force $0<\varepsilon<1$. Since $1+L\ge1$ and $K_L>0$, the third premise gives $-\log\varepsilon\ge(1+L)/K_L\ge1/K_L>0$. So the base $-\log\varepsilon$ of the real power is positive, and no real-power junk value arises.
- There is **no** requirement $\varepsilon<e^{-1}$. If $K_L>1$, the premises allow $-\log\varepsilon\in[1/K_L,1)$.
- There is no division by zero, since $a>0$, $\varepsilon>0$ and $\theta_d>0$.
- The premises on $(\varepsilon,L)$ can be met, for example by $L=0$ and $0<\varepsilon\le\min(K_P,\,e^{-1/K_L})$. For a fixed $\varepsilon$ only finitely many $L$ qualify, because both premises bound $L$ from above.
- Hypotheses 1–7 can hold together. Example: $D=1$, $\theta_0=\gamma_0=1$, $a=c=c_3=K_P=K_L=1$, $p=0$, giving $\kappa=1$. The claim then reads: there is $K_E\ge0$ with $\sum_{\ell=0}^{L}2^{\ell}\le K_E\,\varepsilon^{-1}$ whenever $\varepsilon>0$, $2^{L}\le1/\varepsilon$ and $1+L\le-\log\varepsilon$.
- When $D=0$, $\mathbb N^0$ has one element, the sum equals $2^0=1$, and $\kappa=0$. The claim becomes $c_3\le K_E(-\log\varepsilon)^{pc/a}\varepsilon^{-c/a}$ under the premises.
- The claim is not trivially true: the left side grows with $L$, and the premises allow $L$ of order $\log(1/\varepsilon)$.

---

## mimc_complexity_core

**Setting / data.** All universally quantified.

- $D\in\mathbb N$ (implicit) with instance `[NeZero D]`, i.e. $D\ge1$.
- $\alpha,\beta,\gamma\in\mathbb R^D$ (implicit).
- $c_1,c_2,c_3,c\in\mathbb R$ (implicit).
- $k\in\mathbb N$ (explicit).
- $\eta$ and $d_2$ are formed from $\alpha,\beta,\gamma$ as in §0.

No probability space occurs; the statement is purely deterministic.

**Hypotheses.**

1. (`hα`) $\alpha_d>0$ for every $d$.
2. (`hγ`) $\gamma_d>0$ for every $d$.
3. (`hαβ`) $\beta_d/2\le\alpha_d$ for every $d$. There is **no** sign condition on $\beta$.
4. (`hc₁`) $c_1>0$.
5. (`hc₂`) $c_2>0$.
6. (`hc₃`) $c_3>0$.
7. (`hc`) $c\ge0$.
8. (`hcγ`) $\gamma_d\le c\,\big(\alpha_d+(\gamma_d-\beta_d)/2\big)$ for every $d$.
9. (`hk`) $\#\{d:\ c(\alpha_d+(\gamma_d-\beta_d)/2)-\gamma_d=0\}\le k+1$, an inequality in $\mathbb N$.

**Conclusion.**

$$\exists\,K_M\ge0,\ \exists\,K_X\ge0\quad\forall\,\varepsilon\ \text{with}\ 0<\varepsilon<e^{-1}\quad\exists\,\text{finite}\ \mathcal L\subseteq\mathbb N^D\quad\exists\,N:\mathbb N^D\to\mathbb N\ \text{ such that (C1)–(C4) hold:}$$

- **(C1)** $N_\ell\ge1$ for **every** $\ell\in\mathbb N^D$.
- **(C2)** For every finite $S\subseteq\mathbb N^D$:
  $$c_1\sum_{\ell\in S\setminus\mathcal L}2^{-\sum_d\alpha_d\ell_d}\ \le\ \frac{\varepsilon}{2}.$$
- **(C3)**
  $$\sum_{\ell\in\mathcal L}\frac{c_2\,2^{-\sum_d\beta_d\ell_d}}{N_\ell}\ \le\ \frac{\varepsilon^2}{2}.$$
- **(C4)**
  $$\sum_{\ell\in\mathcal L}N_\ell\,c_3\,2^{\sum_d\gamma_d\ell_d}\ \le\ K_M\,B\big(\eta,\ 2d_2,\ (d_2-1)(2+\eta),\ \varepsilon\big)\ +\ K_X\,(-\log\varepsilon)^{\,k+(d_2-1)\,\frac{c(2+\eta)}{2}}\ \varepsilon^{-\frac{c(2+\eta)}{2}},$$
  where
  $$B\big(\eta,2d_2,(d_2-1)(2+\eta),\varepsilon\big)=\begin{cases}\varepsilon^{-2},&\eta<0,\\ \varepsilon^{-2}\,\log(1/\varepsilon)^{2d_2},&\eta=0,\\ \varepsilon^{-(2+\eta)}\,\log(1/\varepsilon)^{(d_2-1)(2+\eta)},&\eta>0.\end{cases}$$

Here $\eta=\max_d(\gamma_d-\beta_d)/\alpha_d$ and $d_2=\#\{d:(\gamma_d-\beta_d)/\alpha_d=\eta\}$.

- Quantifier order: $K_M$ and $K_X$ come after $D,\alpha,\beta,\gamma,c_1,c_2,c_3,c,k$ and may depend on them. They come before $\varepsilon$, so they are uniform over $\varepsilon\in(0,e^{-1})$. $\mathcal L$ and $N$ come after $\varepsilon$ and may depend on it.
- Because the terms are positive, (C2) for all finite $S$ is equivalent to $c_1\sum_{\ell\in\mathbb N^D\setminus\mathcal L}2^{-\alpha\cdot\ell}\le\varepsilon/2$. This series converges because every $\alpha_d>0$.

**Casts and truncations.**

- `2 * mimcD2 α β γ` fills a real argument slot. `binop%` casts the leaf $d_2$ and multiplies in $\mathbb R$, giving $2d_2$. There is no subtraction, so the choice of reading does not matter here.
- `(mimcD2 α β γ - 1) * (2 + mimcEta α β γ)` fills a real slot and contains the real leaf $\eta$. The cast goes on the leaf $d_2$, so this is $\big((d_2:\mathbb R)-1\big)(2+\eta)$ with **real** subtraction, not `((d₂ - 1 : ℕ) : ℝ)`.
- The exponent `(k : ℝ) + (mimcD2 α β γ - 1) * (c * (2 + mimcEta α β γ) / 2)` is elaborated on its own, and its leaves $k$ (cast), $c$ and $\eta$ are real. So again $d_2$ is cast at the leaf and the subtraction is real: $k+\big((d_2:\mathbb R)-1\big)\cdot c(2+\eta)/2$.
- Since $d_2\ge1$ always, the real and the truncated readings of $d_2-1$ agree numerically: $d_2-1\in\{0,\dots,D-1\}$.
- In (C3) and (C4), $N_\ell$ is cast to $\mathbb R$. The (C3) summand is $(c_2 2^{-\beta\cdot\ell})/N_\ell$. Hypothesis 9 is an inequality between natural numbers.
- The powers $2^{\pm(\cdot)}$, $(-\log\varepsilon)^{(\cdot)}$, $\varepsilon^{(\cdot)}$ and $|\log\varepsilon|^{(\cdot)}$ are real powers. $\varepsilon^2$ is the ordinary square.

**Edge cases / vacuity.**

- Since $D\ge1$, $\eta$ is a genuine maximum and $d_2\ge1$.
- Hypotheses 1–3 give $(\gamma_d-\beta_d)/\alpha_d\ge\gamma_d/\alpha_d-2>-2$, so $2+\eta>0$. Hence every exponent of $\log(1/\varepsilon)$ in (C4) is $\ge0$, and $c(2+\eta)/2\ge0$.
- Hypothesis 3 gives $\alpha_d+(\gamma_d-\beta_d)/2\ge\gamma_d/2>0$. Together with Hypotheses 2 and 8 (and $D\ge1$) this **forces $c>0$**, which is more than Hypothesis 7 states.
- Hypothesis 8 is equivalent to $c\ge c_*:=\max_d\dfrac{2\gamma_d}{2\alpha_d-\beta_d+\gamma_d}$, and $0<c_*\le2$. Only a lower bound on $c$ is imposed. For $c>c_*$ the count in Hypothesis 9 is $0$.
- Hypothesis 9 is equivalent to $k\ge\operatorname{crit}-1$. It holds automatically when $k\ge D-1$.
- Fix $\varepsilon\in(0,e^{-1})$ and $K_X\ge0$. The second summand of (C4) is nondecreasing in $c$ and in $k$, because $\log(1/\varepsilon)>1$, $\varepsilon<1$, $(d_2-1)(2+\eta)\ge0$ and $2+\eta>0$. For large admissible $c$, the exponent $c(2+\eta)/2$ exceeds $2+\max(\eta,0)$.
- No junk values arise. The divisors $\alpha_d$, $N_\ell$ and $2$ are nonzero. $\varepsilon>0$, and $|\log\varepsilon|=-\log\varepsilon>1$ is a positive base.
- The hypotheses can hold together. Example: $D=1$, $\alpha_0=\beta_0=\gamma_0=1$, $c_1=c_2=c_3=1$, $c=1$, $k=0$. Hypothesis 8 then holds with equality, and the count in Hypothesis 9 is $1\le1$. This gives $\eta=0$ and $d_2=1$, and (C4) reads $\sum_{\ell\in\mathcal L}N_\ell2^{\ell}\le K_M\varepsilon^{-2}\log(1/\varepsilon)^2+K_X\varepsilon^{-1}$.
- The conclusion is not trivially satisfiable. (C2) forces $\mathcal L$ to contain every $\ell$ with $c_1 2^{-\alpha\cdot\ell}>\varepsilon/2$; for instance, $\ell=0$ once $\varepsilon<2c_1$. (C3) with (C1) then forces $N_\ell$ to be large on $\mathcal L$. The left side of (C4) is at least $c_3\sum_{\ell\in\mathcal L}2^{\gamma\cdot\ell}$.
- $\mathcal L$ may be any finite set; no shape is imposed, such as downward closedness or being of the form $I(\theta,L)$. $N$ must be positive also outside $\mathcal L$, where its values do not enter (C2)–(C4).

---

## mimc_complexity_boundary

**Setting / data.** All universally quantified.

- $D\in\mathbb N$ (implicit) with `[NeZero D]`, i.e. $D\ge1$.
- $\alpha,\beta,\gamma\in\mathbb R^D$ (implicit).
- $c_1,c_2,c_3\in\mathbb R$ (implicit).
- $\eta$, $d_2$ and $d_3$ are as in §0.

The statement is purely deterministic.

**Hypotheses.**

1. (`hα`) $\alpha_d>0$ for every $d$.
2. (`hγ`) $\gamma_d>0$ for every $d$.
3. (`hαβ`) $\beta_d/2\le\alpha_d$ for every $d$. There is **no** sign condition on $\beta$.
4. (`hc₁`) $c_1>0$.
5. (`hc₂`) $c_2>0$.
6. (`hc₃`) $c_3>0$.

**Conclusion.**

$$\exists\,c_4>0\quad\forall\,\varepsilon\ \text{with}\ 0<\varepsilon<e^{-1}\quad\exists\,\text{finite}\ \mathcal L\subseteq\mathbb N^D\quad\exists\,N:\mathbb N^D\to\mathbb N\ \text{ such that:}$$

- **(C1)** $N_\ell\ge1$ for every $\ell\in\mathbb N^D$.
- **(C2)** For every finite $S\subseteq\mathbb N^D$: $\;c_1\sum_{\ell\in S\setminus\mathcal L}2^{-\alpha\cdot\ell}\le\varepsilon/2$.
- **(C3)** $\sum_{\ell\in\mathcal L}c_2\,2^{-\beta\cdot\ell}/N_\ell\le\varepsilon^2/2$.
- **(C4′)**
  $$\sum_{\ell\in\mathcal L}N_\ell\,c_3\,2^{\gamma\cdot\ell}\ \le\ c_4\,B\big(\eta,\ 2d_2+\max(d_3-3,0),\ (d_2-1)(2+\eta)+\max(d_3-1,0),\ \varepsilon\big),$$
  that is,
  $$\sum_{\ell\in\mathcal L}N_\ell\,c_3\,2^{\gamma\cdot\ell}\ \le\ c_4\cdot\begin{cases}\varepsilon^{-2},&\eta<0,\\ \varepsilon^{-2}\,\log(1/\varepsilon)^{\,2d_2+\max(d_3-3,\,0)},&\eta=0,\\ \varepsilon^{-(2+\eta)}\,\log(1/\varepsilon)^{\,(d_2-1)(2+\eta)+\max(d_3-1,\,0)},&\eta>0,\end{cases}$$

Here $\eta=\max_d(\gamma_d-\beta_d)/\alpha_d$, $d_2=\#\{d:(\gamma_d-\beta_d)/\alpha_d=\eta\}$ and $d_3=\#\{d:\alpha_d=\beta_d/2\}$.

- Quantifier order: $c_4>0$ (strictly) comes after $D,\alpha,\beta,\gamma,c_1,c_2,c_3$, which are all the data, and before $\varepsilon$. $\mathcal L$ and $N$ depend on $\varepsilon$.
- Unlike the core theorem, there is a single constant and no additional $K_X$-type term.

**Casts and truncations.**

- `2 * mimcD2 α β γ + ((mimcD3 α β - 3 : ℕ) : ℝ)` fills a real slot.
  - `binop%` casts the leaf $d_2$, giving $2d_2$ in $\mathbb R$.
  - The ascribed summand is computed in $\mathbb N$ first, giving $\max(d_3-3,0)$, and then cast.
  - So the $\eta=0$ exponent is $2d_2$ if $d_3\le3$, and $2d_2+d_3-3$ if $d_3\ge3$.
- `(mimcD2 α β γ - 1) * (2 + mimcEta α β γ) + ((mimcD3 α β - 1 : ℕ) : ℝ)` evaluates to $\big((d_2:\mathbb R)-1\big)(2+\eta)+\max(d_3-1,0)$.
  - The first subtraction is real; this is harmless since $d_2\ge1$.
  - The second is truncated: it contributes $0$ when $d_3=0$.
- All other casts and powers are as in `mimc_complexity_core`.

**Edge cases / vacuity.**

- As in the core theorem: $2+\eta>0$, all exponents of $\log(1/\varepsilon)$ are $\ge0$, $1\le d_2\le D$, and no division by zero or real-power junk occurs.
- Under Hypothesis 3, $d_3$ counts the coordinates where Hypothesis 3 holds with equality.
- $d_2$ and $d_3$ affect the bound only when $\eta\ge0$. When $\eta<0$ the bound is $c_4\varepsilon^{-2}$ whatever $d_2,d_3$ are. When $\eta=0$, $d_3$ changes the exponent only if $d_3\ge4$. When $\eta>0$, it does so only if $d_3\ge2$.
- The hypotheses can hold together. Examples with $D=1$ and $c_1=c_2=c_3=1$:
  - $\alpha_0=1,\beta_0=2,\gamma_0=1$ gives $d_3=1$ and $\eta=-1$; the bound is $c_4\varepsilon^{-2}$.
  - $\alpha_0=1,\beta_0=2,\gamma_0=2$ gives $\eta=0$, $d_2=d_3=1$; the bound is $c_4\varepsilon^{-2}\log(1/\varepsilon)^2$.

  With $D=4$ and $\alpha_d=1,\beta_d=\gamma_d=2$ for all $d$: $\eta=0$, $d_2=d_3=4$, and the exponent is $8+1=9$.
- The conclusion is not trivially satisfiable, for the same reasons as in the core theorem.

---

## giles_theorem2_boundary

**Setting / data.** All universally quantified.

- $D\in\mathbb N$ (implicit) with `[NeZero D]`, i.e. $D\ge1$.
- From the enclosing section, all implicit: a type $\Omega$ in an arbitrary universe, a $\sigma$-algebra on $\Omega$ (`[MeasurableSpace Ω]`), and a measure $\mu$ on $\Omega$ that is a probability measure (`[IsProbabilityMeasure μ]`).
- Explicit data:
  - $P:\Omega\to\mathbb R$;
  - a family $P_\ell:\Omega\to\mathbb R$ for $\ell\in\mathbb N^D$;
  - a family $Y_{\ell,n}:\Omega\to\mathbb R$ for $\ell\in\mathbb N^D$, $n\in\mathbb N$;
  - a family $\mathrm{Cost}_{\ell,n}:\Omega\to\mathbb R$ for $\ell\in\mathbb N^D$, $n\in\mathbb N$;
  - functions $V,C:\mathbb N^D\to\mathbb R$.
- Implicit: $\alpha,\beta,\gamma\in\mathbb R^D$ and $c_1,c_2,c_3\in\mathbb R$.
- $\eta$, $d_2$ and $d_3$ are as in §0.

Notation:

- $\mathbb E[X]:=\int_\Omega X\,d\mu$ is the Bochner integral (Mathlib's `μ[X]`, which unfolds to $\int\uparrow(X(\omega))\,d\mu$ with the identity coercion on $\mathbb R$). It equals $0$ for non-integrable $X$; see the edge cases.
- $\operatorname{Var}(X)$ is Mathlib's `variance`: the Lebesgue integral $\int(X-\mathbb E[X])^2\,d\mu\in[0,\infty]$ converted to a real number, with $\infty\mapsto0$.
- "Independent" for two real random variables means that the $\sigma$-algebras they generate, pulled back from the Borel sets, are independent under $\mu$. That is, $\mu(X\in A,\,Z\in B)=\mu(X\in A)\,\mu(Z\in B)$ for all Borel $A,B$.
- No measurability is assumed beyond what integrability and $L^2$ membership include (a.e.-strong measurability).

**Hypotheses.**

1. (`hα`) $\alpha_d>0$ for every $d$.
2. (`hβ`) $\beta_d>0$ for every $d$.
3. (`hγ`) $\gamma_d>0$ for every $d$.
4. (`hαβ`) $\beta_d/2\le\alpha_d$ for every $d$.
5. (`hc₁`) $c_1>0$.
6. (`hc₂`) $c_2>0$.
7. (`hc₃`) $c_3>0$.
8. (`hP`) $P$ is $\mu$-integrable.
9. (`hPℓ`) Every $P_\ell$ is $\mu$-integrable.
10. (`hY`) Every $Y_{\ell,n}$ is in $L^2(\mu)$, for all $\ell$ and **all** $n\in\mathbb N$ including $n=0$. That is, it is a.e.-strongly measurable with $\int|Y_{\ell,n}|^2\,d\mu<\infty$.
11. (`hind`) For every $N:\mathbb N^D\to\mathbb N$ with $N_\ell\ge1$ for all $\ell$, and for all multi-indices $i\ne j$, the random variables $Y_{i,N_i}$ and $Y_{j,N_j}$ are independent. This is *pairwise* independence.
    - It is equivalent to: $Y_{i,n}$ and $Y_{j,m}$ are independent whenever $i\ne j$ and $n,m\ge1$. (Given $i,j,n,m$, choose $N_i=n$, $N_j=m$ and $N=1$ elsewhere.)
    - Nothing is assumed about $Y_{\ell,n}$ versus $Y_{\ell,m}$ for the same $\ell$.
    - There is no mutual independence of three or more variables.
12. (`hCost`) $\mathrm{Cost}_{\ell,n}$ is integrable for every $\ell$ and every $n\ge1$.
13. (`h_cost`) $\mathbb E[\mathrm{Cost}_{\ell,n}]=n\,C_\ell$ for every $\ell$ and every $n\ge1$. This is an equality.
14. (`h_var`) $\operatorname{Var}(Y_{\ell,n})=V_\ell/n$ for every $\ell$ and every $n\ge1$. This is an equality.
15. (`h_i`) For every $\delta>0$ there is $n_0\in\mathbb N$ such that $\big|\mathbb E[P_\ell-P]\big|<\delta$ for every $\ell$ with $\ell_d\ge n_0$ for **all** $d$. That is, $\mathbb E[P_\ell]\to\mathbb E[P]$ as $\min_d\ell_d\to\infty$.
16. (`h_iii`) $\mathbb E[Y_{\ell,n}]=\mathbb E\big[\Delta P(\ell)\big]$ for every $\ell$ and every $n\ge1$, where
    $$\Delta P(\ell)(\omega)=\sum_{S\subseteq\{d:\ \ell_d\ge1\}}(-1)^{|S|}\,P_{\ell-\sum_{d\in S}e_d}(\omega)$$
    is the cross difference of $m\mapsto P_m(\omega)$ at $\ell$, as in §0. For example, $\Delta P(0)=P_0$.
17. (`h_ii`) $\big|\mathbb E[Y_{\ell,n}]\big|\le c_1\,2^{-\alpha\cdot\ell}$ for every $\ell$ and every $n\ge1$.
18. (`h_iv`) $V_\ell\le c_2\,2^{-\beta\cdot\ell}$ for every $\ell$.
19. (`h_v`) $C_\ell\le c_3\,2^{\gamma\cdot\ell}$ for every $\ell$.

**Conclusion.**

$$\exists\,c_4>0\quad\forall\,\varepsilon\ \text{with}\ 0<\varepsilon<e^{-1}\quad\exists\,\text{finite}\ \mathcal L\subseteq\mathbb N^D\quad\exists\,N:\mathbb N^D\to\mathbb N\ \text{ such that:}$$

- **(G1)** $N_\ell\ge1$ for every $\ell\in\mathbb N^D$.
- **(G2)** The inequality is **strict**:
  $$\int_\Omega\Big(\sum_{\ell\in\mathcal L}Y_{\ell,N_\ell}(\omega)\;-\;\int_\Omega P\,d\mu\Big)^{2}\mu(d\omega)\ <\ \varepsilon^2.$$
- **(G3)**
  $$\int_\Omega\sum_{\ell\in\mathcal L}\mathrm{Cost}_{\ell,N_\ell}(\omega)\,\mu(d\omega)\ \le\ c_4\cdot\begin{cases}\varepsilon^{-2},&\eta<0,\\ \varepsilon^{-2}\,\log(1/\varepsilon)^{\,2d_2+\max(d_3-3,\,0)},&\eta=0,\\ \varepsilon^{-(2+\eta)}\,\log(1/\varepsilon)^{\,(d_2-1)(2+\eta)+\max(d_3-1,\,0)},&\eta>0.\end{cases}$$
  This is $c_4\,B\big(\eta,\,2d_2+\max(d_3-3,0),\,(d_2-1)(2+\eta)+\max(d_3-1,0),\,\varepsilon\big)$ with $\eta=\max_d(\gamma_d-\beta_d)/\alpha_d$, $d_2=\#\{d:(\gamma_d-\beta_d)/\alpha_d=\eta\}$ and $d_3=\#\{d:\alpha_d=\beta_d/2\}$.

Quantifier order:

- $c_4$ comes after **all** the data: $D$, $\Omega$, $\mu$, $P$, $(P_\ell)$, $(Y_{\ell,n})$, $(\mathrm{Cost}_{\ell,n})$, $V$, $C$, $\alpha,\beta,\gamma,c_1,c_2,c_3$. So it may depend on the particular random variables and on $V,C$, not only on $(\alpha,\beta,\gamma,c_1,c_2,c_3)$.
- $c_4$ does not depend on $\varepsilon$.
- $\mathcal L$ and $N$ are deterministic, chosen after $\varepsilon$, and may depend on it and on all the data.

Parsing: in (G2) the sum stops before "$-\int P\,d\mu$". Mathlib's `∑ x ∈ s, body` parses its body at precedence 67, above binary minus (65). So $\mathbb E[P]$ is subtracted once from the whole sum, not once per $\ell$.

**Casts and truncations.**

- `n * C ℓ` is $(n:\mathbb R)\,C_\ell$, and `V ℓ / n` is $V_\ell/(n:\mathbb R)$. Since $n\ge1$ there, no division by zero occurs.
- The arguments of `mimcBound` are exactly as in `mimc_complexity_boundary`:
  - $2d_2+\max(d_3-3,0)$ and $\big((d_2:\mathbb R)-1\big)(2+\eta)+\max(d_3-1,0)$;
  - the $d_3$ subtractions are truncated;
  - the $d_2$ subtraction is real and equals the truncated one because $d_2\ge1$.
- Inside $\Delta P$, the natural subtraction $\ell_0-1$ occurs only when $\ell_0\ge1$.
- The squares in (G2) and $\varepsilon^2$ are ordinary powers. The powers $2^{\pm(\cdot)}$, $\varepsilon^{(\cdot)}$ and $|\log\varepsilon|^{(\cdot)}$ are real powers.

**Edge cases / vacuity.**

- Every Bochner integral in the statement is of an integrable function under the hypotheses:
  - $P$, $P_\ell$, $P_\ell-P$ and the finite signed sum $\Delta P(\ell)$, by Hypotheses 8 and 9;
  - $Y_{\ell,n}$, which is in $L^2\subset L^1$ since $\mu$ is finite;
  - $\mathrm{Cost}_{\ell,n}$ for $n\ge1$, and in (G3) each $N_\ell\ge1$;
  - the (G2) integrand, which is the square of an $L^2$ function.

  So the "integral of a non-integrable function is 0" convention never applies. By Hypothesis 10, $\operatorname{Var}(Y_{\ell,n})$ is the genuine finite variance.
- Direct consequences of the hypotheses:
  - $V_\ell=\operatorname{Var}(Y_{\ell,1})\ge0$.
  - The left side of (G3) equals $\sum_{\ell\in\mathcal L}N_\ell C_\ell$.
  - $\mathbb E[Y_{\ell,n}]$ does not depend on $n\ge1$.
  - $|\mathbb E[\Delta P(\ell)]|\le c_1 2^{-\alpha\cdot\ell}$.
  - By pairwise independence, the left side of (G2) equals $\sum_{\ell\in\mathcal L}V_\ell/N_\ell+\big(\sum_{\ell\in\mathcal L}\mathbb E[\Delta P(\ell)]-\mathbb E[P]\big)^2$.
- The statement does **not** require:
  - $C_\ell\ge0$ or $\mathrm{Cost}_{\ell,n}\ge0$ (only the upper bound in Hypothesis 19);
  - any pathwise relation between $Y$ and $P$ (only expectations are linked);
  - $Y_{\ell,n}$ to be an average of $n$ samples ($n$ enters only through Hypotheses 13 and 14);
  - any relation between $P$ and the $P_\ell$ beyond Hypothesis 15, which concerns expectations along $\min_d\ell_d\to\infty$.
- The hypotheses can hold together, non-trivially. Take $D=1$ and $\alpha_0=\beta_0=\gamma_0=c_1=c_2=c_3=1$. Let $\Omega$ carry i.i.d. standard normals $Z_0,Z_1,\dots$ under $\mu$ (e.g. a countable product). Set:
  - $P\equiv1$ and $P_\ell\equiv1-2^{-\ell}$, so that $\Delta P(0)=0$ and $\Delta P(\ell)=2^{-\ell}$ for $\ell\ge1$;
  - $Y_{\ell,n}=\Delta P(\ell)+(2^{-\ell}/n)^{1/2}Z_\ell$ for $n\ge1$, and $Y_{\ell,0}=0$;
  - $V_\ell=2^{-\ell}$, $\mathrm{Cost}_{\ell,n}\equiv n2^{\ell}$ and $C_\ell=2^{\ell}$.

  All 19 hypotheses hold. Here $\eta=0$, $d_2=1$ and $d_3=0$, and the (G3) bound is $c_4\varepsilon^{-2}\log(1/\varepsilon)^2$. A degenerate model also works: all functions $\equiv0$, $V\equiv0$, and $\mathrm{Cost}_{\ell,n}\equiv nC_\ell$ with $C_\ell=c_3 2^{\gamma\cdot\ell}$.
- The conclusion is not trivially satisfiable in general. For example, $\mathcal L=\emptyset$ gives left side $(\mathbb E[P])^2$ in (G2), which is $<\varepsilon^2$ for all small $\varepsilon$ only if $\mathbb E[P]=0$.

---

### Method note on the elaboration claims

Mathlib's compiled library files are not present in this environment, so the packet itself could not be elaborated. Instead:

- **Elaborator source.** The `binop%`/`rightact%` rules above were read from Lean v4.33.1 `Lean/Elab/Extra.lean`.
- **Cast placement.** An analogous core-Lean file, with `Int` in place of `ℝ`, a natural-valued `d2`, and a function with real-typed argument slots, elaborated as follows:
  - `bound eta (2 * d2) ((d2 - 1) * (2 + eta)) 0` became `bound eta (2 * ↑d2) ((↑d2 - 1) * (2 + eta)) 0`, i.e. a cast on the leaf and subtraction in the target type;
  - `2 * d2 + ((d3 - 3 : Nat) : Int)` became `2 * ↑d2 + ↑(d3 - 3)`, i.e. truncated subtraction inside the cast;
  - an exponent `(k : Int) + (d2 - 1) * (…)` became `↑k + (↑d2 - 1) * (…)`.
- **Sum precedence.** A replica of Mathlib's `∑ x ∈ s, body` syntax, with the body at precedence 67, parsed `(∑ l ∈ s, Y l - EP)` as `(∑ l ∈ s, Y l) - EP`.
- **`crossDiff` closed form.** The closed form in §0 was checked against a core-Lean replica of the recursive definition, with `Int` values, for $D=3$ on all of $\{0,1,2,3\}^3$.
