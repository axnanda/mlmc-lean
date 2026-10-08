import MlmcLean.TauLeapingExact

/-!
# Tau-leaping: Lipschitz payoffs against the exact chain, and adaptive grids (Giles 2015, §8)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §8
"Continuous-time Markov chains", pp. 55–56 (`docs/giles2015.txt`, ll. 2366–2447), with §5.6
(p. 44, ll. 1917–1930, and p. 45, ll. 1934–1966, Figure 5.9 and Algorithm 3) and §2.1, (2.4)
(p. 8, ll. 378–382).

§8, p. 55, ll. 2372–2375: "the 'tau-leaping' method (which is essentially the Euler-Maruyama
method, approximating the reaction rate as being constant throughout the timestep) gives the
discrete equation `x_{n+1} = x_n + P(hλ(x_n))`"; p. 56, ll. 2407–2410: the Poisson coupling "leads
to a very effective multilevel algorithm with a correction variance which is `O(h)`, leading to an
`O(ε⁻²(log ε)²)` complexity"; ll. 2442–2447: "The non-nested adaptive timestepping approach
described in Section 5.6 for SDEs is equally applicable in this setting. … the construction is
exactly the same as illustrated in Figure 5.9, but with Poisson variates for each time interval
instead of Brownian increments. This adaptive timestepping can be very helpful in cases in which
propensities vary greatly in time."

The model is that of `tauStep`, `tauChain` (`PoissonCoupling.lean`) and of the exact chain
`exactLaw` (`TauLeapingExact.lean`): one reaction, a count `x ∈ ℕ` that jumps to `x + 1` at rate
`λ(x)`.

**1. Weak order one for Lipschitz (unbounded) payoffs.**  `tauLeaping_weak_error_exact` bounds the
weak error of tau-leaping against the exact chain by `2Λ²T² sup|Φ|/N` for bounded payoffs and
bounded propensities `λ ≤ Λ`.  Here the payoff may grow linearly, `|Φ(y)| ≤ A + B y`, which covers
every Lipschitz payoff on `ℕ`, such as the count `Φ(x) = x` itself.
* `lintegral_natCast_exactLaw_le`, `lintegral_natCast_tauChain_le`: both chains have finite means,
  `E_x[X_t] ≤ x + Λt` and `E[x_n] ≤ x₀ + nΛh`; `integral_bind_of_abs_le_linear`: the Markov
  property for functions of linear growth.
* `exactLaw_tauStep_le_linear`: **the local error**,
  `|E_x[f(X_h)] − E[f(x + P(hλ(x)))]| ≤ 2(Λh)²(A + B(x + 1))` for `|f y| ≤ A + B y`.
* `exactLaw_tauChain_le_linear`: telescoping in the class of functions of linear growth, which
  both the exact semigroup and the tau-leaping kernel map into itself (`A` grows by `BΛh`).
* `tauLeaping_weak_error_exact_linear`: `|E[Φ(x_N)] − E[Φ(X_T)]| ≤ 2Λ²T²(A + B(1 + x₀ + ΛT))/N`;
  `tauLeaping_weak_error_exact_lipschitz`: `≤ 2Λ²T²K(1 + x₀ + ΛT)/N` for `K`-Lipschitz `Φ`.
* `tauLeaping_mlmc_exact_lipschitz`: **Theorem 1 with the exact chain as target for Lipschitz
  payoffs**, no assumed weak rate: square-integrable error, mean square `< ε²`, cost
  `O(ε⁻²(log ε)²)`.

The method differs from "truncation plus Poisson tails": truncating `Φ` at the level `R` and
applying the bounded result costs `O(R/N)` plus the tails `E[|Φ(X)| 1_{X > R}]` of both chains,
which are super-exponentially small in `R` (both chains are dominated by `x₀ + P(ΛT)`); optimising
`R ≈ log N / log log N` gives only `O(log N/N)` up to `log log` factors, not `O(1/N)`.  The
weighted telescoping gives the sharp `O(1/N)`.

**2. Adaptive grids with state-dependent propensities.**  All times are multiples of a base spacing
`δ` (a time unit; `T = Mδ`).  A path's state on the union grid is `(x, a, e)`: its count `x`, its
state `a` at the start of its current step, whose propensity `λ(a)` is frozen during the step, and
the base time `e` at which the step ends.  A rule `ν(t, x)` gives the number of base intervals of a
step that starts at base time `t` in the state `x` (`adaptStart`), as `h_ℓ = 2^{−ℓ} H(Ŝ_n)` of §5.6
does.  A rule is *admissible* if its steps before `M` have at least one base interval
(`1 ≤ ν(t, x)` for `t < M`), and *truncated* if moreover they end at or before `M`
(`t + ν(t, x) ≤ M`), as the truncation `t^c := min(t^c + h^c, T)` of Algorithm 3 does:
`ν(t, x) = min(n(x), M − t)` with `n ≥ 1`.  The fine and the coarse path have independent rules.
* `adaptTauStep`, `adaptTauRun`: the single-level scheme,
  `(t, x) ↦ (t + ν(t, x), x + P(ν(t, x) δ λ(x)))`, stopped at `M`.
* `adaptUnionStep`, `adaptUnionRun`, `adaptUnionInit`: **Algorithm 3 for tau-leaping**: from the
  base time `j` the loop moves to the next union grid point `u = min(e^f, e^c)`; on `[jδ, uδ]` the
  counts of the two paths are one Anderson–Higham split of `P((u − j)δλ(a^f))` and
  `P((u − j)δλ(a^c))` ("`P₁` … for the path with the smaller rate, and `P₁ + P₂` for the path with
  the larger rate", pp. 55–56), and a path whose step ends at `u` starts its next one
  (`tauAdvance`).
* `coupledIncr_bind_map_add`: **the split is additive over sub-intervals with frozen rates**;
  so the simulation on the base intervals (`adaptCoupledStep`, one split per base interval) is,
  over each union sub-interval, one split of the sub-interval (`adaptCoupledRun_union`), and
  `adaptUnion_baseGrid`: **the union-grid loop is the base-interval simulation** observed at the
  union grid points (both rules admissible, at least one of them truncated; `adaptUnionRun_eq`).
* `adaptRun_law`: **a path simulated alone on the base intervals has, at `T`, the law of its
  single-level scheme** (a whole step is one tau-leaping step, `adaptRun_step`).
* `adaptUnion_fine`, `adaptUnion_coarse`: **each path of the union-grid loop has, at `T`, the law
  of its single-level adaptive scheme**, for its own truncated rule and whatever the admissible
  rule of the other path (the split gives each path its own Poisson counts, `adaptCoupledRun_fst`,
  `adaptCoupledRun_snd`); `adaptUnion_2_4`: hence **(2.4)** `E[P^c_ℓ] = E[P^f_ℓ]` (with
  integrability of one iff the other) for every payoff of the terminal state.

**Checks.**  The constants of part 1 were checked numerically (`mpmath`, truncated state space) for
`λ(x) = min(x, 3)`, `λ ≡ 2`, `λ(x) = 1 + (x mod 2)` and `λ = 1_{x even}`: the one-step ratio
`sup_f |…| / (2(Λh)²(A + B(x + 1)))` stays below `0.75`, and `N |E[x_N] − E[X_T]|` stays below
`0.62` against the bound `90` (`λ(x) = min(x, 3)`, `Λ = 3`, `T = 1`, `x₀ = 1`).  Part 2 was
checked by computing both laws exactly (truncated Poisson laws) for `λ(x) = 1 + min(x, 4)/2`,
`δ = 0.3`, `M = 5` and two state-dependent rules: the marginals of the loop and the single-level
laws agree to the truncation error, also when the rule of the other path is admissible but not
truncated (its steps overshoot `M`).

**Scope.**  Part 1: bounded propensities (uniformisation needs `Λ < ∞`; e.g. `λ(x) = cx` is not
covered), one reaction.  Part 2: the propensity `λ(x)` is an arbitrary function of the state;
explicitly time-dependent propensities `λ(t, x)` (the paper's motivation is that "propensities
vary greatly in time") are not covered: freezing `λ` at the time and the state at the start of a
step is a routine extension, but needs the start time of the current step in the path state, and
is not formalised.  The step sizes are multiples of the base spacing `δ` (common to the samples of
all levels, e.g. the spacing of the finest level), the rules depend on the time and the state at
the start of a step (rules depending on the whole past would need a larger state), and the laws
compared are those of the state at `T` (payoffs of the terminal state; payoffs of the whole path
are not covered, as in `unionChain_2_4`).  Each path's count is added on every sub-interval, which
is the same as accumulating it as Algorithm 3 does, since the propensity is frozen during the
step.  The variance rate (`β`) of the adaptive coupling and Theorem 1 for adaptive tau-leaping are
not formalised.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace MLMC

/-! ### Payoffs of linear growth on `ℕ` -/

section LinearGrowth

/-- The constants of a linear bound are nonnegative (used for the payoffs of linear growth in Giles
2015, §8): `|f y| ≤ A + B y` for all `y ∈ ℕ` forces `A ≥ 0` (at `y = 0`) and `B ≥ 0` (otherwise
`A + B y < 0` for large `y`). -/
lemma nonneg_of_abs_le_linear {f : ℕ → ℝ} {A B : ℝ} (hf : ∀ y, |f y| ≤ A + B * y) :
    0 ≤ A ∧ 0 ≤ B := by
  have hA : 0 ≤ A := by
    have h := (abs_nonneg _).trans (hf 0)
    simpa using h
  refine ⟨hA, ?_⟩
  by_contra hB'
  have hB : B < 0 := not_le.mp hB'
  obtain ⟨n, hn⟩ := exists_nat_gt (A / -B)
  have h := (abs_nonneg _).trans (hf n)
  rw [div_lt_iff₀ (neg_pos.2 hB)] at hn
  nlinarith

/-- The first moment of a composition on `ℕ` (used for both chains of Giles 2015, §8): if
`E_μ[z] ≤ m` and `E_{κ(z)}[y] ≤ z + c` for every `z`, then `E_{μ.bind κ}[y] ≤ m + c` (moments as
lower integrals of `ofReal y`). -/
lemma lintegral_natCast_bind_le {μ : Measure ℕ} [IsProbabilityMeasure μ] {κ : ℕ → Measure ℕ}
    {c m : ℝ} (hc : 0 ≤ c) (hm0 : 0 ≤ m)
    (hm : ∫⁻ z, ENNReal.ofReal (z : ℝ) ∂μ ≤ ENNReal.ofReal m)
    (hκ : ∀ z, ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(κ z) ≤ ENNReal.ofReal (z + c)) :
    ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(μ.bind κ) ≤ ENNReal.ofReal (m + c) := by
  rw [Measure.lintegral_bind Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aemeasurable]
  calc ∫⁻ z, ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(κ z) ∂μ
      ≤ ∫⁻ z, ENNReal.ofReal (1 * (z : ℝ) + c) ∂μ :=
        lintegral_mono fun z => by rw [one_mul]; exact hκ z
    _ = ENNReal.ofReal 1 * ∫⁻ z, ENNReal.ofReal (z : ℝ) ∂μ + ENNReal.ofReal c * μ Set.univ :=
        lintegral_ofReal_mul_add μ (fun z => Nat.cast_nonneg z) zero_le_one hc
    _ ≤ ENNReal.ofReal m + ENNReal.ofReal c := by
        rw [ENNReal.ofReal_one, one_mul, measure_univ, mul_one]
        exact add_le_add hm le_rfl
    _ = ENNReal.ofReal (m + c) := (ENNReal.ofReal_add hm0 hc).symm

/-- A function of linear growth, `|f y| ≤ A + B y`, is integrable for a finite measure on `ℕ` with a
finite first moment (used for the payoffs of Giles 2015, §8). -/
lemma integrable_of_abs_le_linear {ν : Measure ℕ} [IsFiniteMeasure ν] {m : ℝ}
    (hν : ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂ν ≤ ENNReal.ofReal m) {f : ℕ → ℝ} {A B : ℝ}
    (hf : ∀ y, |f y| ≤ A + B * y) : Integrable f ν := by
  have hid : Integrable (fun y : ℕ => (y : ℝ)) ν :=
    ⟨Measurable.of_discrete.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => Nat.cast_nonneg y)).2
        (hν.trans_lt ENNReal.ofReal_lt_top)⟩
  exact Integrable.mono' ((integrable_const A).add (hid.const_mul B))
    Measurable.of_discrete.aestronglyMeasurable
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hf y)

/-- `|E_ν[f]| ≤ A + B m` for `|f y| ≤ A + B y` and a probability measure `ν` on `ℕ` with first
moment at most `m ≥ 0` (used for the payoffs of Giles 2015, §8). -/
lemma abs_integral_le_of_abs_le_linear {ν : Measure ℕ} [IsProbabilityMeasure ν] {m : ℝ}
    (hm0 : 0 ≤ m)
    (hν : ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂ν ≤ ENNReal.ofReal m) {f : ℕ → ℝ} {A B : ℝ}
    (hf : ∀ y, |f y| ≤ A + B * y) : |∫ y, f y ∂ν| ≤ A + B * m := by
  obtain ⟨-, hB⟩ := nonneg_of_abs_le_linear hf
  have hid : Integrable (fun y : ℕ => (y : ℝ)) ν :=
    integrable_of_abs_le_linear hν (A := 0) (B := 1) fun y => by simp
  have hmean : ∫ y, (y : ℝ) ∂ν ≤ m := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => Nat.cast_nonneg y)
      Measurable.of_discrete.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hm0 hν
  calc |∫ y, f y ∂ν| ≤ ∫ y, |f y| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ y, (A + B * (y : ℝ)) ∂ν :=
        integral_mono (integrable_of_abs_le_linear hν hf).abs
          ((integrable_const A).add (hid.const_mul B)) hf
    _ = A + B * ∫ y, (y : ℝ) ∂ν := by
        rw [integral_add (integrable_const A) (hid.const_mul B), integral_const, probReal_univ,
          one_smul, integral_const_mul]
    _ ≤ A + B * m := by nlinarith

/-- The integral of a nonnegative function against a composition `μ.bind κ` on `ℕ` is the iterated
integral, when the function is integrable for every `κ(z)` (used for Giles 2015, §8). -/
lemma integral_bind_of_nonneg_nat {μ : Measure ℕ} {κ : ℕ → Measure ℕ} {g : ℕ → ℝ}
    (hg : ∀ y, 0 ≤ g y) (hint : ∀ z, Integrable g (κ z)) :
    ∫ y, g y ∂(μ.bind κ) = ∫ z, ∫ y, g y ∂(κ z) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg)
      Measurable.of_discrete.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => integral_nonneg hg)
      Measurable.of_discrete.aestronglyMeasurable,
    Measure.lintegral_bind Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aemeasurable]
  congr 1
  exact lintegral_congr fun z =>
    (ofReal_integral_eq_lintegral_ofReal (hint z) (ae_of_all _ hg)).symm

/-- **The Markov property for functions of linear growth** (used for both chains of Giles 2015, §8):
on `ℕ`, if `μ` is a probability measure with first moment at most `m` and every `κ(z)` is a
probability measure with first moment at most `z + c`, then
`∫ f d(μ.bind κ) = ∫ (∫ f dκ(z)) dμ(z)` for `|f y| ≤ A + B y`.  (`integral_bind_of_abs_le` is the
bounded case.) -/
lemma integral_bind_of_abs_le_linear {μ : Measure ℕ} [IsProbabilityMeasure μ] {κ : ℕ → Measure ℕ}
    (hκ : ∀ z, IsProbabilityMeasure (κ z)) {c m : ℝ} (hc : 0 ≤ c) (hm0 : 0 ≤ m)
    (hμ : ∫⁻ z, ENNReal.ofReal (z : ℝ) ∂μ ≤ ENNReal.ofReal m)
    (hκm : ∀ z, ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(κ z) ≤ ENNReal.ofReal (z + c))
    {f : ℕ → ℝ} {A B : ℝ} (hf : ∀ y, |f y| ≤ A + B * y) :
    ∫ y, f y ∂(μ.bind κ) = ∫ z, ∫ y, f y ∂(κ z) ∂μ := by
  obtain ⟨hA, hB⟩ := nonneg_of_abs_le_linear hf
  have hP : IsProbabilityMeasure (μ.bind κ) :=
    ⟨measure_univ_bind_of_discrete μ fun z => (hκ z).measure_univ⟩
  have hbm := lintegral_natCast_bind_le hc hm0 hμ hκm
  have hw0 : ∀ y : ℕ, 0 ≤ A + B * (y : ℝ) := fun y => by positivity
  have hw : ∀ y : ℕ, |A + B * (y : ℝ)| ≤ A + B * y := fun y => (abs_of_nonneg (hw0 y)).le
  have hg0 : ∀ y : ℕ, 0 ≤ f y + (A + B * y) := fun y => by
    have := neg_abs_le (f y)
    linarith [hf y]
  have hg : ∀ y : ℕ, |f y + (A + B * y)| ≤ 2 * A + 2 * B * y := fun y => by
    rw [abs_of_nonneg (hg0 y)]
    linarith [le_abs_self (f y), hf y]
  have eg := integral_bind_of_nonneg_nat (μ := μ) hg0 fun z =>
    integrable_of_abs_le_linear (hκm z) hg
  have ew := integral_bind_of_nonneg_nat (μ := μ) hw0 fun z =>
    integrable_of_abs_le_linear (hκm z) hw
  have hoG : Integrable (fun z => ∫ y, (f y + (A + B * y)) ∂(κ z)) μ := by
    refine integrable_of_abs_le_linear hμ (A := 2 * A + 2 * B * c) (B := 2 * B) fun z => ?_
    have := hκ z
    have h := abs_integral_le_of_abs_le_linear (add_nonneg (Nat.cast_nonneg z) hc) (hκm z) hg
    nlinarith
  have hoW : Integrable (fun z => ∫ y, (A + B * (y : ℝ)) ∂(κ z)) μ := by
    refine integrable_of_abs_le_linear hμ (A := A + B * c) (B := B) fun z => ?_
    have := hκ z
    have h := abs_integral_le_of_abs_le_linear (add_nonneg (Nat.cast_nonneg z) hc) (hκm z) hw
    nlinarith
  have hfe : ∀ y : ℕ, f y = (f y + (A + B * y)) - (A + B * y) := fun y => by ring
  calc ∫ y, f y ∂(μ.bind κ)
      = ∫ y, ((f y + (A + B * y)) - (A + B * y)) ∂(μ.bind κ) :=
        integral_congr_ae (ae_of_all _ hfe)
    _ = ∫ y, (f y + (A + B * y)) ∂(μ.bind κ) - ∫ y, (A + B * (y : ℝ)) ∂(μ.bind κ) :=
        integral_sub (integrable_of_abs_le_linear hbm hg) (integrable_of_abs_le_linear hbm hw)
    _ = ∫ z, ∫ y, (f y + (A + B * y)) ∂(κ z) ∂μ - ∫ z, ∫ y, (A + B * (y : ℝ)) ∂(κ z) ∂μ := by
        rw [eg, ew]
    _ = ∫ z, (∫ y, (f y + (A + B * y)) ∂(κ z) - ∫ y, (A + B * (y : ℝ)) ∂(κ z)) ∂μ :=
        (integral_sub hoG hoW).symm
    _ = ∫ z, ∫ y, f y ∂(κ z) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        have := hκ z
        show ∫ y, (f y + (A + B * y)) ∂(κ z) - ∫ y, (A + B * (y : ℝ)) ∂(κ z) = ∫ y, f y ∂(κ z)
        rw [← integral_sub (integrable_of_abs_le_linear (hκm z) hg)
          (integrable_of_abs_le_linear (hκm z) hw)]
        exact integral_congr_ae (ae_of_all _ fun y => (hfe y).symm)

end LinearGrowth

/-! ### First moments of the chains -/

section Moments

variable {lam : ℕ → ℝ≥0} {Λ : ℝ≥0}

/-- One tau-leaping step (Giles 2015, §8, p. 55, l. 2375: "`x_{n+1} = x_n + P(hλ(x_n))`") adds at
most `Λh` to the mean: `E[x + P(hλ(x))] ≤ x + Λh` for `λ ≤ Λ`. -/
lemma lintegral_natCast_tauStep_le (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0) (x : ℕ) :
    ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(tauStep lam h x) ≤ ENNReal.ofReal (x + (Λ : ℝ) * h) := by
  rw [tauStep, lintegral_map Measurable.of_discrete Measurable.of_discrete]
  have e : ∀ n : ℕ, ENNReal.ofReal (((x + n : ℕ) : ℝ)) = ENNReal.ofReal (1 * (n : ℝ) + x) :=
    fun n => by push_cast; ring_nf
  rw [lintegral_congr e, lintegral_ofReal_mul_add _ (fun n => Nat.cast_nonneg n) zero_le_one
    (Nat.cast_nonneg x), lintegral_id_poissonMeasure, measure_univ, ENNReal.ofReal_one, one_mul,
    mul_one, ← ENNReal.ofReal_add (NNReal.coe_nonneg _) (Nat.cast_nonneg x)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ((h * lam x : ℝ≥0) : ℝ) ≤ (Λ : ℝ) * h := by
    rw [NNReal.coe_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hΛ x) h.coe_nonneg
  linarith

/-- One step `J` of the uniformised exact chain (`jumpKernel`, Giles 2015, §8) moves up by at most
one: `E_{J(z)}[y] ≤ z + 1`. -/
lemma lintegral_natCast_jumpKernel_le (hΛ : ∀ x, lam x ≤ Λ) (z : ℕ) :
    ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(jumpKernel lam Λ z) ≤ ENNReal.ofReal (z + 1) := by
  rw [jumpKernel, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
    smul_eq_mul]
  have h1 : ENNReal.ofReal (((z + 1 : ℕ)) : ℝ) = ENNReal.ofReal ((z : ℝ) + 1) := by
    push_cast
    rfl
  have h2 : ENNReal.ofReal (z : ℝ) ≤ ENNReal.ofReal ((z : ℝ) + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  rw [h1]
  calc ((lam z / Λ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ((z : ℝ) + 1) +
        ((1 - lam z / Λ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (z : ℝ)
      ≤ ((lam z / Λ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ((z : ℝ) + 1) +
        ((1 - lam z / Λ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ((z : ℝ) + 1) :=
        by gcongr
    _ = ENNReal.ofReal ((z : ℝ) + 1) := by
        rw [← add_mul, ← ENNReal.coe_add, add_tsub_cancel_of_le (rate_div_le_one hΛ z),
          ENNReal.coe_one, one_mul]

/-- `n` steps of the uniformised exact chain (`jumpPow`, Giles 2015, §8) move up by at most `n`:
`E_{J^n(x)}[y] ≤ x + n`. -/
lemma lintegral_natCast_jumpPow_le (hΛ : ∀ x, lam x ≤ Λ) :
    ∀ n x : ℕ, ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(jumpPow lam Λ n x) ≤ ENNReal.ofReal ((x : ℝ) + n)
  | 0, x => by rw [jumpPow_zero, lintegral_dirac, Nat.cast_zero, add_zero]
  | n + 1, x => by
      have : IsProbabilityMeasure (jumpPow lam Λ n x) := ⟨jumpPow_univ hΛ n x⟩
      rw [jumpPow_succ]
      refine (lintegral_natCast_bind_le zero_le_one (by positivity)
        (lintegral_natCast_jumpPow_le hΛ n x) (lintegral_natCast_jumpKernel_le hΛ)).trans
        (le_of_eq ?_)
      push_cast
      ring_nf

/-- **The exact chain has a finite mean** (Giles 2015, §8, p. 56, ll. 2413–2415: the exact algorithm
"which updates the reaction rates after every single reaction"): for `λ ≤ Λ`,
`E_x[X_t] ≤ x + Λt`, since the chain moves up by at most the number `P(Λt)` of clock ticks of the
uniformisation (`exactLaw`). -/
lemma lintegral_natCast_exactLaw_le (hΛ : ∀ x, lam x ≤ Λ) (t : ℝ≥0) (x : ℕ) :
    ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(exactLaw lam Λ t x) ≤ ENNReal.ofReal (x + (Λ : ℝ) * t) := by
  rw [exactLaw]
  have h := lintegral_natCast_bind_le (μ := poissonMeasure (Λ * t))
    (κ := fun n => jumpPow lam Λ n x) (c := x) (m := (Λ : ℝ) * t) (Nat.cast_nonneg x)
    (by positivity) (le_of_eq (by rw [lintegral_id_poissonMeasure, NNReal.coe_mul]))
    (fun n => by
      have := lintegral_natCast_jumpPow_le hΛ n x
      rwa [add_comm] at this)
  refine h.trans (le_of_eq ?_)
  rw [add_comm]

/-- **The tau-leaping chain has a finite mean** (Giles 2015, §8, p. 55, l. 2375): for `λ ≤ Λ`,
`n` steps of size `h` from `x₀` give `E[x_n] ≤ x₀ + nΛh`. -/
lemma lintegral_natCast_tauChain_le (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0) (x₀ : ℕ) :
    ∀ n : ℕ, ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(tauChain lam h x₀ n) ≤
      ENNReal.ofReal (x₀ + n * ((Λ : ℝ) * h))
  | 0 => by
      rw [tauChain, lintegral_dirac]
      simp
  | n + 1 => by
      have := isProbabilityMeasure_tauChain lam h x₀ n
      rw [tauChain]
      refine (lintegral_natCast_bind_le (by positivity) (by positivity)
        (lintegral_natCast_tauChain_le hΛ h x₀ n) (lintegral_natCast_tauStep_le hΛ h)).trans
        (le_of_eq ?_)
      push_cast
      ring_nf

end Moments

/-! ### Weak order one for payoffs of linear growth -/

section WeakLinear

variable {lam : ℕ → ℝ≥0} {Λ : ℝ≥0}

/-- A Poisson average split after its first two terms, for `|u n| ≤ c + d n` (used for the one-step
error of Giles 2015, §8): `∫ u dP(r) = e^{−r} u(0) + e^{−r} r u(1) + ρ` with `|ρ| ≤ (c + d) r²`,
since `c + d n ≤ (c + d) n(n − 1)` for `n ≥ 2` and `E[P(r)(P(r) − 1)] = r²`.  (The bounded case is
`poisson_integral_split`.) -/
lemma poisson_integral_split_linear (r : ℝ≥0) {u : ℕ → ℝ} {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hu : ∀ n, |u n| ≤ c + d * n) :
    ∃ ρ : ℝ, |ρ| ≤ (c + d) * (r : ℝ) ^ 2 ∧
      ∫ n, u n ∂(poissonMeasure r) = Real.exp (-r) * u 0 + Real.exp (-r) * r * u 1 + ρ := by
  set w : ℕ → ℝ := fun n => Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ) with hw_def
  have hw0 : ∀ n, 0 ≤ w n := fun n => by positivity
  have hD : HasSum (fun n : ℕ => w n * ((n : ℝ) * ((n : ℝ) - 1))) ((r : ℝ) ^ 2) :=
    hasSum_poissonWeight_mul_descFactorial r
  have hD2 := (hasSum_nat_add_iff' 2).2 hD
  have e0 : ∑ i ∈ range 2, w i * ((i : ℝ) * ((i : ℝ) - 1)) = 0 := by
    simp [Finset.sum_range_succ]
  rw [e0, sub_zero] at hD2
  have hbd : ∀ n : ℕ, ‖w (n + 2) * u (n + 2)‖ ≤
      (c + d) * (w (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1))) := fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 _)]
    have h1 := hu (n + 2)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast at h1 ⊢
    have h2 : c + d * ((n : ℝ) + 2) ≤ (c + d) * (((n : ℝ) + 2) * ((n : ℝ) + 2 - 1)) := by
      nlinarith [mul_nonneg hc (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 + 3 * n + 1),
        mul_nonneg hd (mul_nonneg hn (by linarith : (0 : ℝ) ≤ (n : ℝ) + 2))]
    calc w (n + 2) * |u (n + 2)|
        ≤ w (n + 2) * ((c + d) * (((n : ℝ) + 2) * ((n : ℝ) + 2 - 1))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (hw0 _)
      _ = (c + d) * (w (n + 2) * (((n : ℝ) + 2) * ((n : ℝ) + 2 - 1))) := by ring
  have hv : Summable fun n => w (n + 2) * u (n + 2) :=
    Summable.of_norm_bounded (hD2.summable.mul_left (c + d)) hbd
  refine ⟨∑' n, w (n + 2) * u (n + 2), ?_, ?_⟩
  · have h := hv.hasSum.norm_le_of_bounded (hD2.mul_left (c + d)) hbd
    rwa [Real.norm_eq_abs] at h
  · have hfull : HasSum (fun n => w n * u n)
        ((∑ i ∈ range 2, w i * u i) + ∑' n, w (n + 2) * u (n + 2)) :=
      HasSum.sum_range_add (f := fun n => w n * u n) hv.hasSum
    rw [integral_poissonMeasure]
    simp only [smul_eq_mul]
    rw [hfull.tsum_eq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hw_def]
    norm_num

/-- **The local weak error of tau-leaping is `O(h²)` for payoffs of linear growth** (Giles 2015,
§8, p. 55, ll. 2372–2375: "the 'tau-leaping' method (which is essentially the Euler-Maruyama
method, approximating the reaction rate as being constant throughout the timestep) gives the
discrete equation `x_{n+1} = x_n + P(hλ(x_n))`").  For a propensity `0 ≤ λ ≤ Λ`, a function
`|f y| ≤ A + B y`, a step `h ≥ 0` and a state `x`, `f(X_h)` and `f(x + P(hλ(x)))` are integrable
and `|E_x[f(X_h)] − E[f(x + P(hλ(x)))]| ≤ 2(Λh)²(A + B(x + 1))`, where `X` is the exact chain
(`exactLaw`).  As in `exactLaw_tauStep_le` (the bounded case `B = 0`), with no clock tick (resp. no
jump) or exactly one the two laws agree up to `O((Λh)²)`; two or more ticks contribute at most
`E[(A + B(x + N)) 1_{N ≥ 2}] ≤ (A + B(x + 1))(Λh)²` for `N ~ P(Λh)`. -/
theorem exactLaw_tauStep_le_linear (hΛ : ∀ x, lam x ≤ Λ) {f : ℕ → ℝ} {A B : ℝ}
    (hf : ∀ y, |f y| ≤ A + B * y) (h : ℝ≥0) (x : ℕ) :
    Integrable f (exactLaw lam Λ h x) ∧ Integrable f (tauStep lam h x) ∧
      |∫ y, f y ∂(exactLaw lam Λ h x) - ∫ y, f y ∂(tauStep lam h x)| ≤
        2 * ((Λ : ℝ) * h) ^ 2 * (A + B * (x + 1)) := by
  have hPE := isProbabilityMeasure_exactLaw hΛ h x
  have hPS : IsProbabilityMeasure (tauStep lam h x) := ⟨tauStep_univ lam h x⟩
  refine ⟨integrable_of_abs_le_linear (lintegral_natCast_exactLaw_le hΛ h x) hf,
    integrable_of_abs_le_linear (lintegral_natCast_tauStep_le hΛ h x) hf, ?_⟩
  obtain ⟨hA, hB⟩ := nonneg_of_abs_le_linear hf
  have hP : ∀ n y, IsProbabilityMeasure (jumpPow lam Λ n y) := fun n y => ⟨jumpPow_univ hΛ n y⟩
  set g : ℕ → ℝ := fun n => ∫ y, f y ∂(jumpPow lam Λ n x) with hg_def
  have hg : ∀ n : ℕ, |g n| ≤ (A + B * x) + B * n := fun n => by
    have := hP n x
    have h1 := abs_integral_le_of_abs_le_linear (by positivity)
      (lintegral_natCast_jumpPow_le hΛ n x) hf
    rw [mul_add] at h1
    linarith
  have hE : ∫ y, f y ∂(exactLaw lam Λ h x) = ∫ n, g n ∂(poissonMeasure (Λ * h)) := by
    rw [exactLaw]
    exact integral_bind_of_abs_le_linear (fun n => hP n x) (Nat.cast_nonneg x)
      (NNReal.coe_nonneg (Λ * h)) (le_of_eq (lintegral_id_poissonMeasure _))
      (fun n => by
        have := lintegral_natCast_jumpPow_le hΛ n x
        rwa [add_comm] at this) hf
  have hT : ∫ y, f y ∂(tauStep lam h x) = ∫ n, f (x + n) ∂(poissonMeasure (h * lam x)) := by
    rw [tauStep, integral_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable]
  have hg0 : g 0 = f x := by
    show ∫ y, f y ∂(jumpPow lam Λ 0 x) = f x
    rw [jumpPow_zero, integral_dirac]
  have hg1 : g 1 = ((lam x / Λ : ℝ≥0) : ℝ) * f (x + 1) + (1 - ((lam x / Λ : ℝ≥0) : ℝ)) * f x := by
    show ∫ y, f y ∂(jumpPow lam Λ (0 + 1) x) = _
    rw [jumpPow_succ, jumpPow_zero, Measure.dirac_bind Measurable.of_discrete,
      integral_jumpKernel hΛ]
  have hu : ∀ n : ℕ, |f (x + n)| ≤ (A + B * x) + B * n := fun n => by
    have h1 := hf (x + n)
    push_cast at h1
    linarith
  obtain ⟨ρ₁, hρ₁, e₁⟩ := poisson_integral_split_linear (Λ * h) (by positivity) hB hg
  obtain ⟨ρ₂, hρ₂, e₂⟩ := poisson_integral_split_linear (h * lam x) (by positivity) hB hu
  have hpa := rate_div_mul_eq hΛ h x
  rw [hE, hT, e₁, e₂, hg0, hg1]
  simp only [NNReal.coe_mul] at hρ₁ hρ₂ ⊢
  set a : ℝ := (Λ : ℝ) * h with ha_def
  set r : ℝ := (h : ℝ) * lam x with hr_def
  set p : ℝ := ((lam x / Λ : ℝ≥0) : ℝ) with hp_def
  set C : ℝ := A + B * (x + 1) with hC_def
  have hC : A + B * x + B = C := by rw [hC_def]; ring
  have ha0 : 0 ≤ a := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def]
    exact_mod_cast rate_div_le_one hΛ x
  have hp0 : 0 ≤ p := NNReal.coe_nonneg _
  have hra : r ≤ a := by
    rw [← hpa]
    calc p * a ≤ 1 * a := mul_le_mul_of_nonneg_right hp1 ha0
      _ = a := one_mul a
  have hfx : |f x| ≤ C := by
    have := hf x
    rw [hC_def, mul_add, mul_one]
    linarith
  have hfx1 : |f (x + 1)| ≤ C := by
    have := hf (x + 1)
    push_cast at this
    rw [hC_def]
    exact this
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hfx
  obtain ⟨hc1, hc2⟩ := uniformised_exp_coeff_bounds hr0 hra
  have key : Real.exp (-a) * f x + Real.exp (-a) * a * (p * f (x + 1) + (1 - p) * f x) + ρ₁ -
      (Real.exp (-r) * f (x + 0) + Real.exp (-r) * r * f (x + 1) + ρ₂) =
      (Real.exp (-a) * (1 + a - r) - Real.exp (-r)) * f x +
        r * (Real.exp (-a) - Real.exp (-r)) * f (x + 1) + (ρ₁ - ρ₂) := by
    rw [add_zero, ← hpa]
    ring
  have h1 : |(Real.exp (-a) * (1 + a - r) - Real.exp (-r)) * f x| ≤ (a - r) ^ 2 * C := by
    rw [abs_mul]
    exact mul_le_mul hc1 hfx (abs_nonneg _) (sq_nonneg _)
  have h2 : |r * (Real.exp (-a) - Real.exp (-r)) * f (x + 1)| ≤ r * (a - r) * C := by
    rw [abs_mul]
    exact mul_le_mul hc2 hfx1 (abs_nonneg _) (mul_nonneg hr0 (sub_nonneg.2 hra))
  rw [hC] at hρ₁ hρ₂
  have hpoly : ((a - r) ^ 2 + r * (a - r) + a ^ 2 + r ^ 2) * C ≤ 2 * a ^ 2 * C :=
    mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hr0 (sub_nonneg.2 hra)]) hC0
  have hsum : (a - r) ^ 2 * C + r * (a - r) * C + (C * a ^ 2 + C * r ^ 2) =
      ((a - r) ^ 2 + r * (a - r) + a ^ 2 + r ^ 2) * C := by ring
  rw [key]
  calc |(Real.exp (-a) * (1 + a - r) - Real.exp (-r)) * f x +
        r * (Real.exp (-a) - Real.exp (-r)) * f (x + 1) + (ρ₁ - ρ₂)|
      ≤ |(Real.exp (-a) * (1 + a - r) - Real.exp (-r)) * f x| +
        |r * (Real.exp (-a) - Real.exp (-r)) * f (x + 1)| + (|ρ₁| + |ρ₂|) :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_sub _ _))
    _ ≤ (a - r) ^ 2 * C + r * (a - r) * C + (C * a ^ 2 + C * r ^ 2) :=
        add_le_add (add_le_add h1 h2) (add_le_add hρ₁ hρ₂)
    _ = ((a - r) ^ 2 + r * (a - r) + a ^ 2 + r ^ 2) * C := hsum
    _ ≤ 2 * a ^ 2 * C := hpoly

/-- Telescoping the local errors in the class of functions of linear growth (the argument behind
the weak order one of Giles 2015, §8).  For `λ ≤ Λ`, `|f y| ≤ A + B y` and `n` tau-leaping steps of
size `h` from `x₀`, `|E_{x₀}[f(X_{nh})] − E[f(x_n)]| ≤ 2(Λh)² n (A + B(1 + x₀ + nΛh))`.  The exact
semigroup and the tau-leaping kernel map `|f| ≤ A + B y` into `|·| ≤ (A + BΛh) + B y`
(`lintegral_natCast_exactLaw_le`, `lintegral_natCast_tauStep_le`), so
`P_{(k+1)h} f − κ^{k+1} f = (P_{kh} − κ^k) P_h f + κ^k (P_h − κ) f`; the last local error
(`exactLaw_tauStep_le_linear`) is integrated against the tau-leaping law after `k` steps, whose mean
is at most `x₀ + kΛh` (`lintegral_natCast_tauChain_le`). -/
lemma exactLaw_tauChain_le_linear (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0) (x₀ : ℕ) :
    ∀ (n : ℕ) (f : ℕ → ℝ) (A B : ℝ), (∀ y, |f y| ≤ A + B * y) →
      |∫ y, f y ∂(exactLaw lam Λ (n * h) x₀) - ∫ y, f y ∂(tauChain lam h x₀ n)| ≤
        2 * ((Λ : ℝ) * h) ^ 2 * n * (A + B * (1 + x₀ + n * ((Λ : ℝ) * h)))
  | 0, f, A, B, _ => by
      rw [Nat.cast_zero, zero_mul, exactLaw_zero, tauChain, sub_self, abs_zero]
      simp
  | n + 1, f, A, B, hf => by
      obtain ⟨hA, hB⟩ := nonneg_of_abs_le_linear hf
      have ha0 : 0 ≤ (Λ : ℝ) * h := by positivity
      have hν := isProbabilityMeasure_exactLaw hΛ (n * h) x₀
      have hτ := isProbabilityMeasure_tauChain lam h x₀ n
      have hE : exactLaw lam Λ ((n + 1 : ℕ) * h) x₀ =
          (exactLaw lam Λ (n * h) x₀).bind (exactLaw lam Λ h) := by
        rw [← exactLaw_add hΛ, Nat.cast_succ, add_mul, one_mul]
      have hGb : ∀ z : ℕ, |∫ y, f y ∂(exactLaw lam Λ h z)| ≤
          (A + B * ((Λ : ℝ) * h)) + B * z := fun z => by
        have := isProbabilityMeasure_exactLaw hΛ h z
        have h1 := abs_integral_le_of_abs_le_linear (by positivity)
          (lintegral_natCast_exactLaw_le hΛ h z) hf
        rw [mul_add] at h1
        linarith
      have hSb : ∀ z : ℕ, |∫ y, f y ∂(tauStep lam h z)| ≤ (A + B * ((Λ : ℝ) * h)) + B * z :=
        fun z => by
        have : IsProbabilityMeasure (tauStep lam h z) := ⟨tauStep_univ lam h z⟩
        have h1 := abs_integral_le_of_abs_le_linear (by positivity)
          (lintegral_natCast_tauStep_le hΛ h z) hf
        rw [mul_add] at h1
        linarith
      have hmE : ∫⁻ y, ENNReal.ofReal (y : ℝ) ∂(exactLaw lam Λ (n * h) x₀) ≤
          ENNReal.ofReal (x₀ + (Λ : ℝ) * ((n * h : ℝ≥0) : ℝ)) :=
        lintegral_natCast_exactLaw_le hΛ _ x₀
      have hmτ := lintegral_natCast_tauChain_le hΛ h x₀ n
      have e1 : ∫ y, f y ∂(exactLaw lam Λ ((n + 1 : ℕ) * h) x₀) =
          ∫ z, ∫ y, f y ∂(exactLaw lam Λ h z) ∂(exactLaw lam Λ (n * h) x₀) := by
        rw [hE]
        exact integral_bind_of_abs_le_linear (fun z => isProbabilityMeasure_exactLaw hΛ h z) ha0
          (by positivity) hmE (fun z => lintegral_natCast_exactLaw_le hΛ h z) hf
      have e2 : ∫ y, f y ∂(tauChain lam h x₀ (n + 1)) =
          ∫ z, ∫ y, f y ∂(tauStep lam h z) ∂(tauChain lam h x₀ n) := by
        rw [tauChain]
        exact integral_bind_of_abs_le_linear (fun z => ⟨tauStep_univ lam h z⟩) ha0
          (by positivity) hmτ
          (lintegral_natCast_tauStep_le hΛ h) hf
      have ih := exactLaw_tauChain_le_linear hΛ h x₀ n (fun z => ∫ y, f y ∂(exactLaw lam Λ h z))
        (A + B * ((Λ : ℝ) * h)) B hGb
      have hdiff : ∀ z : ℕ, |∫ y, f y ∂(exactLaw lam Λ h z) - ∫ y, f y ∂(tauStep lam h z)| ≤
          2 * ((Λ : ℝ) * h) ^ 2 * (A + B) + 2 * ((Λ : ℝ) * h) ^ 2 * B * z := fun z => by
        have := (exactLaw_tauStep_le_linear hΛ hf h z).2.2
        nlinarith
      have hstep : |∫ z, ∫ y, f y ∂(exactLaw lam Λ h z) ∂(tauChain lam h x₀ n) -
          ∫ z, ∫ y, f y ∂(tauStep lam h z) ∂(tauChain lam h x₀ n)| ≤
          2 * ((Λ : ℝ) * h) ^ 2 * (A + B) +
            2 * ((Λ : ℝ) * h) ^ 2 * B * (x₀ + n * ((Λ : ℝ) * h)) := by
        rw [← integral_sub (integrable_of_abs_le_linear hmτ hGb)
          (integrable_of_abs_le_linear hmτ hSb)]
        exact abs_integral_le_of_abs_le_linear (by positivity) hmτ hdiff
      rw [e1, e2]
      have hfin : 2 * ((Λ : ℝ) * h) ^ 2 * n *
            (A + B * ((Λ : ℝ) * h) + B * (1 + x₀ + n * ((Λ : ℝ) * h))) +
          (2 * ((Λ : ℝ) * h) ^ 2 * (A + B) +
            2 * ((Λ : ℝ) * h) ^ 2 * B * (x₀ + n * ((Λ : ℝ) * h))) +
          2 * ((Λ : ℝ) * h) ^ 2 * B * ((Λ : ℝ) * h) =
          2 * ((Λ : ℝ) * h) ^ 2 * ((n + 1 : ℕ) : ℝ) *
            (A + B * (1 + x₀ + ((n + 1 : ℕ) : ℝ) * ((Λ : ℝ) * h))) := by
        push_cast
        ring
      have hnn : 0 ≤ 2 * ((Λ : ℝ) * h) ^ 2 * B * ((Λ : ℝ) * h) := by positivity
      calc |∫ z, ∫ y, f y ∂(exactLaw lam Λ h z) ∂(exactLaw lam Λ (n * h) x₀) -
            ∫ z, ∫ y, f y ∂(tauStep lam h z) ∂(tauChain lam h x₀ n)|
          ≤ |∫ z, ∫ y, f y ∂(exactLaw lam Λ h z) ∂(exactLaw lam Λ (n * h) x₀) -
              ∫ z, ∫ y, f y ∂(exactLaw lam Λ h z) ∂(tauChain lam h x₀ n)| +
            |∫ z, ∫ y, f y ∂(exactLaw lam Λ h z) ∂(tauChain lam h x₀ n) -
              ∫ z, ∫ y, f y ∂(tauStep lam h z) ∂(tauChain lam h x₀ n)| := abs_sub_le _ _ _
        _ ≤ _ := by linarith

/-- **Tau-leaping has weak order one against the exact chain for payoffs of linear growth**
(Giles 2015, §8, pp. 55–56, ll. 2372–2375 and 2409–2410: tau-leaping, "approximating the reaction
rate as being constant throughout the timestep", and the claimed "`O(ε⁻²(log ε)²)` complexity",
which by Theorem 1 needs a weak rate `α ≥ ½`; the weak order `α = 1` is implicit in the paper).
For a propensity `0 ≤ λ ≤ Λ`, a payoff with `|Φ(y)| ≤ A + B y` for all `y ∈ ℕ`, a final time
`T ≥ 0` and `N ≥ 1` tau-leaping steps of size `T/N` from `x₀`, `Φ(x_N)` and `Φ(X_T)` are
integrable and `|E[Φ(x_N)] − E[Φ(X_T)]| ≤ 2Λ²T²(A + B(1 + x₀ + ΛT))/N`, where `X` is the exact
chain with jump rates `λ` (`exactLaw`).  This extends `tauLeaping_weak_error_exact` (the case
`B = 0`, bounded payoffs) to unbounded payoffs such as `Φ(x) = x`.  The proof does not truncate the
payoff: a truncation at level `R` costs only `O(R/N)` plus a super-exponentially small tail
`E[|Φ(X)| 1_{X > R}]` of both chains (dominated by `x₀ + P(ΛT)`), i.e. `O(log N/N)` up to
`log log N` factors, not `O(1/N)`; the telescoping in the class of functions of linear growth
(`exactLaw_tauChain_le_linear`) gives the sharp `O(1/N)`.  Deviation: bounded propensities (as in
`TauLeapingExact.lean`; uniformisation needs `Λ < ∞`). -/
theorem tauLeaping_weak_error_exact_linear (hΛ : ∀ x, lam x ≤ Λ) {Φ : ℕ → ℝ} {A B : ℝ}
    (hΦ : ∀ y, |Φ y| ≤ A + B * y) (T : ℝ≥0) (x₀ : ℕ) {N : ℕ} (hN : 0 < N) :
    Integrable Φ (tauChain lam (T / N) x₀ N) ∧ Integrable Φ (exactLaw lam Λ T x₀) ∧
      |∫ x, Φ x ∂(tauChain lam (T / N) x₀ N) - ∫ x, Φ x ∂(exactLaw lam Λ T x₀)| ≤
        2 * (Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 * (A + B * (1 + x₀ + Λ * T)) / N := by
  have hN0 : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have := isProbabilityMeasure_tauChain lam (T / N) x₀ N
  have := isProbabilityMeasure_exactLaw hΛ T x₀
  refine ⟨integrable_of_abs_le_linear (lintegral_natCast_tauChain_le hΛ (T / N) x₀ N) hΦ,
    integrable_of_abs_le_linear (lintegral_natCast_exactLaw_le hΛ T x₀) hΦ, ?_⟩
  have h := exactLaw_tauChain_le_linear hΛ (T / N) x₀ N Φ A B hΦ
  rw [mul_div_cancel₀ T hN0, abs_sub_comm] at h
  refine h.trans (le_of_eq ?_)
  rw [NNReal.coe_div, NNReal.coe_natCast]
  field_simp

/-- **Tau-leaping has weak order one against the exact chain for Lipschitz payoffs** (Giles 2015,
§8, pp. 55–56, ll. 2372–2375 and 2409–2410; the paper does not fix a payoff class, and the weak
order `α = 1` behind its "`O(ε⁻²(log ε)²)` complexity" is implicit).  For a propensity
`0 ≤ λ ≤ Λ`, a payoff with `|Φ(x) − Φ(y)| ≤ K|x − y|`, a final time `T ≥ 0` and `N ≥ 1`
tau-leaping steps of size `T/N` from `x₀`, `Φ(x_N)` and `Φ(X_T)` are integrable and
`|E[Φ(x_N)] − E[Φ(X_T)]| ≤ 2Λ²T²K(1 + x₀ + ΛT)/N`, where `X` is the exact chain (`exactLaw`):
`tauLeaping_weak_error_exact_linear` for `Φ − Φ(0)`, which satisfies `|Φ(y) − Φ(0)| ≤ K y`. -/
theorem tauLeaping_weak_error_exact_lipschitz (hΛ : ∀ x, lam x ≤ Λ) {Φ : ℕ → ℝ} {K : ℝ}
    (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ K * |(x : ℝ) - y|) (T : ℝ≥0) (x₀ : ℕ) {N : ℕ}
    (hN : 0 < N) :
    Integrable Φ (tauChain lam (T / N) x₀ N) ∧ Integrable Φ (exactLaw lam Λ T x₀) ∧
      |∫ x, Φ x ∂(tauChain lam (T / N) x₀ N) - ∫ x, Φ x ∂(exactLaw lam Λ T x₀)| ≤
        2 * (Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 * K * (1 + x₀ + Λ * T) / N := by
  have hlin : ∀ y : ℕ, |Φ y - Φ 0| ≤ 0 + K * y := fun y => by
    have := hΦ y 0
    rwa [Nat.cast_zero, sub_zero, Nat.abs_cast, ← zero_add (K * (y : ℝ))] at this
  have hbd : ∀ y : ℕ, |Φ y| ≤ |Φ 0| + K * y := fun y => by
    have h1 := hlin y
    have h2 := abs_sub_abs_le_abs_sub (Φ y) (Φ 0)
    linarith
  have h := (tauLeaping_weak_error_exact_linear hΛ hlin T x₀ hN).2.2
  have := isProbabilityMeasure_tauChain lam (T / N) x₀ N
  have := isProbabilityMeasure_exactLaw hΛ T x₀
  have hi1 : Integrable Φ (tauChain lam (T / N) x₀ N) :=
    integrable_of_abs_le_linear (lintegral_natCast_tauChain_le hΛ (T / N) x₀ N) hbd
  have hi2 : Integrable Φ (exactLaw lam Λ T x₀) :=
    integrable_of_abs_le_linear (lintegral_natCast_exactLaw_le hΛ T x₀) hbd
  refine ⟨hi1, hi2, ?_⟩
  rw [integral_sub hi1 (integrable_const _), integral_sub hi2 (integrable_const _),
    integral_const, integral_const, probReal_univ, probReal_univ, one_smul,
    sub_sub_sub_cancel_right, zero_add] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **Theorem 1 for tau-leaping MLMC with the exact chain as target, for Lipschitz payoffs, with no
assumed weak rate** (Giles 2015, §8, p. 56, ll. 2407–2410: the Poisson coupling "leads to a very
effective multilevel algorithm with a correction variance which is `O(h)`, leading to an
`O(ε⁻²(log ε)²)` complexity").  Let the propensity be bounded, `0 ≤ λ ≤ Λ` (on `ℕ` it is then
`Λ`-Lipschitz, `abs_sub_le_mul_of_le_nat`), and the payoff `K`-Lipschitz,
`|Φ(x) − Φ(y)| ≤ K|x − y|` (unbounded payoffs such as `Φ(x) = x` are allowed).  The
Poisson-coupled tau-leaping estimator of `tauLeaping_mlmc_theorem1` (level `ℓ`: `2^ℓ` steps of size
`T 2^{−ℓ}`, the coarse path coupled by the Anderson–Higham split, independent samples of law
`tauInputLaw`, cost `2^ℓ` per sample) estimates `E[Φ(X_T)]` for the exact chain `X` (`exactLaw`):
there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the
error of the estimator is square integrable, its mean square is `< ε²`, and the cost is
`∑_ℓ N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`.  The weak rate `α = 1`, a hypothesis of
`tauLeaping_mlmc_theorem1`, is proved (`tauLeaping_weak_error_exact_lipschitz`); this extends
`tauLeaping_mlmc_exact` from bounded to Lipschitz payoffs.  Deviation: bounded propensities, one
reaction (as in `tauLeaping_mlmc_theorem1`). -/
theorem tauLeaping_mlmc_exact_lipschitz (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {K : ℝ} (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ K * |(x : ℝ) - y|) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine Φ) (tauCoarse Φ)) (fun p x => x p) ℓ (N ℓ) x -
              ∫ y, Φ y ∂(exactLaw lam Λ T x₀)) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw lam T x₀) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine Φ) (tauCoarse Φ)) (fun p x => x p) ℓ (N ℓ) x -
              ∫ y, Φ y ∂(exactLaw lam Λ T x₀)) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw lam T x₀) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) := by
  have hK : 0 ≤ K := by
    have h := (abs_nonneg _).trans (hΦ 1 0)
    simpa using h
  obtain ⟨c₄, hc₄, hth⟩ := tauLeaping_mlmc_theorem1 (abs_sub_le_mul_of_le_nat hΛ) hΛ T x₀ hΦ
    (∫ y, Φ y ∂(exactLaw lam Λ T x₀)) (α := 1)
    (c₁ := 2 * (Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 * K * (1 + x₀ + Λ * T) + 1) (by norm_num)
    (by positivity) fun ℓ => by
      have h := (tauLeaping_weak_error_exact_lipschitz hΛ hΦ T x₀ (N := 2 ^ ℓ)
        (by positivity)).2.2
      have e1 : ((2 ^ ℓ : ℕ) : ℝ≥0) = 2 ^ ℓ := by push_cast; rfl
      have e2 : (2 : ℝ) ^ (-(1 * (ℓ : ℝ))) = ((2 ^ ℓ : ℕ) : ℝ)⁻¹ := by
        rw [one_mul, Real.rpow_neg zero_le_two, Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
      rw [e1] at h
      rw [e2, ← div_eq_mul_inv]
      exact h.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
  have hν := isProbabilityMeasure_tauInputLaw lam T x₀
  obtain ⟨-, -, hω⟩ := exists_iid_inputs (tauInputLaw lam T x₀)
  have hD : ∀ ℓ, MemLp (fineCoarseDiff (tauFine Φ) (tauCoarse Φ) ℓ) 2 (tauInputLaw lam T x₀) :=
    memLp_fineCoarseDiff (memLp_tauFine hΛ T x₀ hΦ) (memLp_tauCoarse hΛ T x₀ hΦ)
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, -, hmse, hcost⟩ := hth ε hε hε1
  exact ⟨L, N, hN, ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω hD ℓ (N ℓ)).sub
    (memLp_const _)).integrable_sq, hmse, hcost⟩

end WeakLinear

/-! ### Adaptive grids with state-dependent propensities

Giles 2015, §8, p. 56, ll. 2442–2447, with §5.6, p. 45, Algorithm 3.  Times are counted in base
intervals of length `δ`; a path's state is `(x, a, e)` (count, state at the start of the current
step, end of the current step); `ν(t, x)` is the number of base intervals of a step starting at
time `t` in the state `x`. -/

section Adaptive

variable (lam : ℕ → ℝ≥0) (δ : ℝ≥0)

/-- **One path over one sub-interval of the union grid** (Giles 2015, §8, p. 56, ll. 2442–2446:
"with Poisson variates for each time interval instead of Brownian increments", and §5.6, p. 45,
ll. 1953–1955, Algorithm 3: "if `t = t^c` then update coarse path … compute adapted coarse path
timestep `h^c`").
The state of a path is `p = (x, a, e)`: its current count `x`, its state `a` at the start of its
current step (whose propensity `λ(a)` is frozen during the step) and the base time `e` at which the
step ends.  The path receives the count `i` over a sub-interval ending at base time `u`: `x` becomes
`x + i`, and if `u = e` the step ends and a new one starts from `x + i` with `ν(u, x + i)` base
intervals (the rule `ν` gives the number of base intervals of a step from the time and the state
at its start). -/
def tauAdvance (ν : ℕ → ℕ → ℕ) (u : ℕ) (p : ℕ × ℕ × ℕ) (i : ℕ) : ℕ × ℕ × ℕ :=
  if u = p.2.2 then (p.1 + i, p.1 + i, u + ν u (p.1 + i)) else (p.1 + i, p.2.1, p.2.2)

/-- The state of a path at the start of a step at base time `t` from the state `x` (Giles 2015,
§5.6, p. 44, ll. 1920–1922: "an adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)`"):
`(x, x, t + ν(t, x))`, the step having `ν(t, x)` base intervals. -/
def adaptStart (ν : ℕ → ℕ → ℕ) (t x : ℕ) : ℕ × ℕ × ℕ := (x, x, t + ν t x)

/-- The law of one path alone after base interval `j` (from base time `j` to `j + 1`), from the
state `p = (x, a, e)` (Giles 2015, §8, p. 55, l. 2375: tau-leaping, the propensity frozen at the
start `a` of the current step): the count is `P(δλ(a))`, `δ` being the base spacing. -/
noncomputable def adaptSubStep (ν : ℕ → ℕ → ℕ) (j : ℕ) (p : ℕ × ℕ × ℕ) : Measure (ℕ × ℕ × ℕ) :=
  (poissonMeasure (δ * lam p.2.1)).map (tauAdvance ν (j + 1) p)

/-- The law of one path alone after the base intervals `j, …, j + r − 1`, started from the state `p`
(Giles 2015, §8 and §5.6). -/
noncomputable def adaptRun (ν : ℕ → ℕ → ℕ) (j : ℕ) : ℕ → ℕ × ℕ × ℕ → Measure (ℕ × ℕ × ℕ)
  | 0 => Measure.dirac
  | r + 1 => fun p => (adaptRun ν j r p).bind (adaptSubStep lam δ ν (j + r))

/-- **The coupled step over one base interval** (Giles 2015, §8, pp. 55–56, ll. 2393–2407:
"`P₁ = P(h min(λ(x_n), λ(x^c_n)))`, `P₂ = P(h|λ(x_n) − λ(x^c_n)|)`, and then using `P₁` as the
Poisson variate for the path with the smaller rate, and `P₁ + P₂` for the path with the larger
rate").  From the fine state `s.1 = (x, a, e)` and the coarse state `s.2 = (y, c, e')`, the counts
of the base interval `j` are drawn from the Anderson–Higham split `coupledIncr (δλ(a)) (δλ(c))` of
the frozen propensities, and each path advances with its own rule (`νf`, `νc`).  Over a union
sub-interval this is one split with the summed means (`adaptCoupledRun_union`). -/
noncomputable def adaptCoupledStep (νf νc : ℕ → ℕ → ℕ) (j : ℕ)
    (s : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) : Measure ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  (coupledIncr (δ * lam s.1.2.1) (δ * lam s.2.2.1)).map fun ij =>
    (tauAdvance νf (j + 1) s.1 ij.1, tauAdvance νc (j + 1) s.2 ij.2)

/-- The law of the coupled pair after the base intervals `j, …, j + r − 1`, started from `s`
(Giles 2015, §8 and §5.6). -/
noncomputable def adaptCoupledRun (νf νc : ℕ → ℕ → ℕ) (j : ℕ) :
    ℕ → (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) → Measure ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ))
  | 0 => Measure.dirac
  | r + 1 => fun s => (adaptCoupledRun νf νc j r s).bind (adaptCoupledStep lam δ νf νc (j + r))

/-- **One iteration of the union-grid loop: Algorithm 3 for tau-leaping** (Giles 2015, §8, p. 56,
ll. 2442–2446: "The non-nested adaptive timestepping approach described in Section 5.6 for SDEs is
equally applicable in this setting. … the construction is exactly the same as illustrated in
Figure 5.9, but with Poisson variates for each time interval instead of Brownian increments"; §5.6,
p. 45, ll. 1947–1948, Algorithm 3: "`t := min(t^c, t^f)`, `h := t − t_old`").  The state
`q = (j, s)` is the current base time `j` and the fine and coarse path states.  If `j ≥ M` (time
`T = Mδ` is reached) the loop has stopped.  Otherwise the next point of the union grid is
`u = min(e, e')`, the earlier of the two step ends; on the sub-interval `[jδ, uδ]` of length
`h = (u − j)δ` the counts of the two paths are one Anderson–Higham split of `P(hλ(a))` and
`P(hλ(c))` (`coupledIncr`), with the propensities frozen at the starts `a`, `c` of the current
steps; each path adds its count and, if its step ends at `u`, starts its next step with its own
rule (`tauAdvance`).  The length `u − j` is a natural subtraction: along the loop started from
`adaptUnionInit`, the invariant `j < e, e'` holds while `j < M` (it is kept because the rules are
admissible, `1 ≤ ν`), so `h > 0`; without it the loop would stall with `h = 0`.  If at least one
rule is truncated, also `u ≤ M` (the invariant of `adaptUnionRun_eq`). -/
noncomputable def adaptUnionStep (νf νc : ℕ → ℕ → ℕ) (M : ℕ)
    (q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) : Measure (ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  if M ≤ q.1 then Measure.dirac q else
    (coupledIncr (((min q.2.1.2.2 q.2.2.2.2 - q.1 : ℕ) : ℝ≥0) * δ * lam q.2.1.2.1)
      (((min q.2.1.2.2 q.2.2.2.2 - q.1 : ℕ) : ℝ≥0) * δ * lam q.2.2.2.1)).map fun ij =>
      (min q.2.1.2.2 q.2.2.2.2, tauAdvance νf (min q.2.1.2.2 q.2.2.2.2) q.2.1 ij.1,
        tauAdvance νc (min q.2.1.2.2 q.2.2.2.2) q.2.2 ij.2)

/-- The law after `K` iterations of the union-grid loop started from `q` (Giles 2015, §5.6,
Algorithm 3, and §8): the first iteration, then `K − 1` more. -/
noncomputable def adaptUnionRun (νf νc : ℕ → ℕ → ℕ) (M : ℕ) :
    ℕ → ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) → Measure (ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ))
  | 0 => Measure.dirac
  | K + 1 => fun q => (adaptUnionStep lam δ νf νc M q).bind (adaptUnionRun νf νc M K)

/-- **One step of the single-level adaptive tau-leaping scheme** (Giles 2015, §8, p. 55, l. 2375:
"`x_{n+1} = x_n + P(hλ(x_n))`", with the adaptive timestep of §5.6, p. 44, l. 1922,
"`h_ℓ = 2^{−ℓ} H(Ŝ_n)`").  From the base time `t` and the state `x`, the step has
`ν(t, x)` base intervals, `h = ν(t, x) δ`, and the next pair is
`(t + ν(t, x), x + P(ν(t, x) δ λ(x)))`; at `t ≥ M` (time `T = Mδ`) the scheme has stopped. -/
noncomputable def adaptTauStep (ν : ℕ → ℕ → ℕ) (M : ℕ) (s : ℕ × ℕ) : Measure (ℕ × ℕ) :=
  if M ≤ s.1 then Measure.dirac s else
    (poissonMeasure ((ν s.1 s.2 : ℝ≥0) * δ * lam s.2)).map fun i => (s.1 + ν s.1 s.2, s.2 + i)

/-- The law after `k` steps of the single-level adaptive tau-leaping scheme (`adaptTauStep`) started
from the pair `s = (t, x)` (Giles 2015, §8 and §5.6): the first step, then `k − 1` more. -/
noncomputable def adaptTauRun (ν : ℕ → ℕ → ℕ) (M : ℕ) : ℕ → ℕ × ℕ → Measure (ℕ × ℕ)
  | 0 => Measure.dirac
  | k + 1 => fun s => (adaptTauStep lam δ ν M s).bind (adaptTauRun ν M k)

/-- Zero base intervals: `adaptRun ν j 0 p = δ_p` (Giles 2015, §8 and §5.6, Algorithm 3). -/
lemma adaptRun_zero (ν : ℕ → ℕ → ℕ) (j : ℕ) (p : ℕ × ℕ × ℕ) :
    adaptRun lam δ ν j 0 p = Measure.dirac p :=
  rfl

/-- One more base interval (Giles 2015, §8 and §5.6, Algorithm 3):
`adaptRun ν j (r + 1) p = (adaptRun ν j r p).bind (adaptSubStep (j + r))`. -/
lemma adaptRun_succ (ν : ℕ → ℕ → ℕ) (j r : ℕ) (p : ℕ × ℕ × ℕ) :
    adaptRun lam δ ν j (r + 1) p = (adaptRun lam δ ν j r p).bind (adaptSubStep lam δ ν (j + r)) :=
  rfl

/-- Zero base intervals of the coupled simulation (Giles 2015, §8 and §5.6, Algorithm 3). -/
lemma adaptCoupledRun_zero (νf νc : ℕ → ℕ → ℕ) (j : ℕ) (s : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :
    adaptCoupledRun lam δ νf νc j 0 s = Measure.dirac s :=
  rfl

/-- One more base interval of the coupled simulation (Giles 2015, §8 and §5.6, Algorithm 3). -/
lemma adaptCoupledRun_succ (νf νc : ℕ → ℕ → ℕ) (j r : ℕ) (s : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :
    adaptCoupledRun lam δ νf νc j (r + 1) s =
      (adaptCoupledRun lam δ νf νc j r s).bind (adaptCoupledStep lam δ νf νc (j + r)) :=
  rfl

/-- Zero iterations of the union-grid loop (Giles 2015, §8 and §5.6, Algorithm 3). -/
lemma adaptUnionRun_zero (νf νc : ℕ → ℕ → ℕ) (M : ℕ) (q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :
    adaptUnionRun lam δ νf νc M 0 q = Measure.dirac q :=
  rfl

/-- One iteration of the union-grid loop, then `K` more (Giles 2015, §8 and §5.6, Algorithm 3). -/
lemma adaptUnionRun_succ (νf νc : ℕ → ℕ → ℕ) (M K : ℕ) (q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :
    adaptUnionRun lam δ νf νc M (K + 1) q =
      (adaptUnionStep lam δ νf νc M q).bind (adaptUnionRun lam δ νf νc M K) :=
  rfl

/-- Zero steps of the single-level adaptive scheme (Giles 2015, §8 and §5.6, Algorithm 3). -/
lemma adaptTauRun_zero (ν : ℕ → ℕ → ℕ) (M : ℕ) (s : ℕ × ℕ) :
    adaptTauRun lam δ ν M 0 s = Measure.dirac s :=
  rfl

/-- One step of the single-level adaptive scheme, then `k` more (Giles 2015, §8 and §5.6,
Algorithm 3). -/
lemma adaptTauRun_succ (ν : ℕ → ℕ → ℕ) (M k : ℕ) (s : ℕ × ℕ) :
    adaptTauRun lam δ ν M (k + 1) s = (adaptTauStep lam δ ν M s).bind (adaptTauRun lam δ ν M k) :=
  rfl

/-- Adding an independent Poisson count (Giles 2015, §8, p. 55, ll. 2387–2389: "the sum of two
independent Poisson variates `P(t₁)`, `P(t₂)` is equivalent in distribution to `P(t₁ + t₂)`"): if
`κ(F i)` adds a `P(t)` count `i'` to `i`, then `(P(s).map F).bind κ = P(s + t).map G`. -/
lemma poisson_map_bind_add_eq {β γ : Type*} [MeasurableSpace β] [DiscreteMeasurableSpace β]
    [MeasurableSpace γ] (s t : ℝ≥0) (F : ℕ → β) (G : ℕ → γ) (κ : β → Measure γ)
    (hκ : ∀ i, κ (F i) = (poissonMeasure t).map fun i' => G (i + i')) :
    ((poissonMeasure s).map F).bind κ = (poissonMeasure (s + t)).map G := by
  rw [bind_map_of_discrete, show (fun i => κ (F i)) =
      fun i => (poissonMeasure t).map fun i' => G (i + i') from funext hκ,
    bind_map_comp_add, poissonMeasure_conv_poissonMeasure]

/-- Within a step of `m + 1` base intervals ending at `e = j + m + 1`, after `r ≤ m` base intervals
the path alone has received one `P(rδλ(a))` count (Giles 2015, §8, p. 55). -/
lemma adaptRun_within (ν : ℕ → ℕ → ℕ) (j m x a e : ℕ) (he : e = j + m + 1) :
    ∀ r, r ≤ m → adaptRun lam δ ν j r (x, a, e) =
      (poissonMeasure ((r : ℝ≥0) * δ * lam a)).map fun i => (x + i, a, e)
  | 0, _ => by
      rw [adaptRun_zero, Nat.cast_zero, zero_mul, zero_mul, poissonMeasure_zero,
        Measure.map_dirac' Measurable.of_discrete, add_zero]
  | r + 1, hr => by
      rw [adaptRun_succ, adaptRun_within ν j m x a e he r (by omega)]
      rw [poisson_map_bind_add_eq _ (δ * lam a) _ (fun i => (x + i, a, e))]
      · congr 2
        push_cast
        ring
      · intro i
        rw [adaptSubStep]
        congr 1
        funext i'
        have hne : ¬ (j + r + 1 = e) := by omega
        simp only [tauAdvance, if_neg hne]
        simp only [add_assoc]

/-- **On the base grid, a whole step is one tau-leaping step** (Giles 2015, §8, p. 55, l. 2375):
over a step of `m + 1` base intervals ending at `e = j + m + 1`, the path alone receives one
`P((m + 1)δλ(a))` count and starts its next step at `e`. -/
lemma adaptRun_step (ν : ℕ → ℕ → ℕ) (j m x a e : ℕ) (he : e = j + m + 1) :
    adaptRun lam δ ν j (m + 1) (x, a, e) =
      (poissonMeasure (((m + 1 : ℕ) : ℝ≥0) * δ * lam a)).map fun i =>
        (x + i, x + i, e + ν e (x + i)) := by
  rw [adaptRun_succ, adaptRun_within lam δ ν j m x a e he m le_rfl]
  rw [poisson_map_bind_add_eq _ (δ * lam a) _ (fun i => (x + i, x + i, e + ν e (x + i)))]
  · congr 2
    push_cast
    ring
  · intro i
    rw [adaptSubStep]
    congr 1
    funext i'
    have he' : j + m + 1 = e := he.symm
    simp only [tauAdvance, if_pos he']
    rw [he']
    simp only [add_assoc]

/-- Running a path alone for `n + r` base intervals is running it for `n`, then for `r` more
(Giles 2015, §8 and §5.6, Algorithm 3). -/
lemma adaptRun_add (ν : ℕ → ℕ → ℕ) (j n : ℕ) (p : ℕ × ℕ × ℕ) :
    ∀ r, adaptRun lam δ ν j (n + r) p = (adaptRun lam δ ν j n p).bind (adaptRun lam δ ν (j + n) r)
  | 0 => by
      rw [Nat.add_zero]
      exact Measure.bind_dirac.symm
  | r + 1 => by
      rw [← Nat.add_assoc, adaptRun_succ, adaptRun_add ν j n p r,
        Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
      congr 1
      funext q
      rw [adaptRun_succ, Nat.add_assoc]

/-- The single-level adaptive scheme stops at `M`: from the pair `(M, x)` it stays there
(Giles 2015, §8 and §5.6, Algorithm 3: "`t^c := min(t^c + h^c, T)`"). -/
lemma adaptTauRun_stop (ν : ℕ → ℕ → ℕ) (M : ℕ) :
    ∀ k x, adaptTauRun lam δ ν M k (M, x) = Measure.dirac (M, x)
  | 0, x => adaptTauRun_zero lam δ ν M (M, x)
  | k + 1, x => by
      have hs : adaptTauStep lam δ ν M (M, x) = Measure.dirac (M, x) := by
        rw [adaptTauStep, if_pos le_rfl]
      rw [adaptTauRun_succ, hs, Measure.dirac_bind Measurable.of_discrete,
        adaptTauRun_stop ν M k x]

/-- A path alone on the base grid, observed at `M`, is the single-level scheme (Giles 2015, §8 and
§5.6), by induction on the remaining time `d = M − t`: from the start of a step at `t < M`, the
whole step is one tau-leaping step (`adaptRun_step`), after which a new step starts.  The rule
must make steps of at least one base interval that end at or before `M`. -/
lemma adaptRun_eq_adaptTauRun (ν : ℕ → ℕ → ℕ) {M : ℕ} (hν1 : ∀ t < M, ∀ x, 1 ≤ ν t x)
    (hνM : ∀ t < M, ∀ x, t + ν t x ≤ M) (d : ℕ) :
    ∀ t x K, t + d = M → d ≤ K →
      (adaptRun lam δ ν t d (adaptStart ν t x)).map (fun p => p.1) =
        (adaptTauRun lam δ ν M K (t, x)).map Prod.snd := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro t x K htd hdK
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [Nat.add_zero] at htd
      subst htd
      rw [adaptRun_zero, adaptTauRun_stop lam δ ν, Measure.map_dirac' Measurable.of_discrete,
        Measure.map_dirac' measurable_snd]
      rfl
    · have ht : t < M := by omega
      obtain ⟨m, hm⟩ : ∃ m, ν t x = m + 1 := ⟨ν t x - 1, by have := hν1 t ht x; omega⟩
      have htM := hνM t ht x
      obtain ⟨d', hd'⟩ : ∃ d', d = (m + 1) + d' := ⟨d - (m + 1), by omega⟩
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have hstart : adaptStart ν t x = (x, x, t + (m + 1)) := by
        rw [adaptStart, hm]
      have hstep : adaptTauStep lam δ ν M (t, x) =
          (poissonMeasure (((m + 1 : ℕ) : ℝ≥0) * δ * lam x)).map fun i => (t + (m + 1), x + i) := by
        rw [adaptTauStep, if_neg (by simp only; omega)]
        simp only [hm]
      rw [hd', hstart, adaptRun_add,
        adaptRun_step lam δ ν t m x x (t + (m + 1)) (by omega), bind_map_of_discrete,
        map_bind_of_discrete _ _ Measurable.of_discrete, adaptTauRun_succ, hstep,
        bind_map_of_discrete, map_bind_of_discrete _ _ measurable_snd]
      congr 1
      funext i
      exact ih d' (by omega) (t + (m + 1)) (x + i) K' (by omega) (by omega)

/-- **One path simulated on the base grid has the law of its single-level adaptive scheme**
(Giles 2015, §8, p. 55, ll. 2372–2375: tau-leaping, "approximating the reaction rate as being
constant throughout the timestep", "gives the discrete equation `x_{n+1} = x_n + P(hλ(x_n))`";
§5.6, p. 44, ll. 1920–1922: "an adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)`"; §8, p. 56,
ll. 2445–2446: "with Poisson variates for each time interval").  If the rule is truncated, i.e.
makes, before `M`, steps of at least one base interval that end at or before `M` (`1 ≤ ν(t, x)`,
`t + ν(t, x) ≤ M` for `t < M`, e.g. `ν(t, x) = min(n(x), M − t)` with `n ≥ 1`, as
`t^c := min(t^c + h^c, T)` in Algorithm 3), then the state at `T = Mδ` of the path updated on every
base interval with its propensity frozen at the start of its step has the law of the state after
`M` steps of the adaptive scheme `adaptTauRun` (which stops at `M`).  Both hypotheses are needed
in general (for `λ > 0`): with `ν = 0` the scheme stalls, and a step beyond `M` is cut at `M` on the
base grid but not in `adaptTauRun`. -/
theorem adaptRun_law (ν : ℕ → ℕ → ℕ) {M : ℕ} (hν1 : ∀ t < M, ∀ x, 1 ≤ ν t x)
    (hνM : ∀ t < M, ∀ x, t + ν t x ≤ M) (x₀ : ℕ) :
    (adaptRun lam δ ν 0 M (adaptStart ν 0 x₀)).map (fun p => p.1) =
      (adaptTauRun lam δ ν M M (0, x₀)).map Prod.snd :=
  adaptRun_eq_adaptTauRun lam δ ν hν1 hνM M 0 x₀ M (Nat.zero_add M) le_rfl

/-- The fine component of the coupled step is the fine path's own step: the split gives it a
`P(δλ(a))` count (`coupledIncr_fst`; Giles 2015, §8, pp. 55–56). -/
lemma adaptCoupledStep_fst (νf νc : ℕ → ℕ → ℕ) (j : ℕ) (s : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :
    (adaptCoupledStep lam δ νf νc j s).map Prod.fst = adaptSubStep lam δ νf j s.1 := by
  rw [adaptCoupledStep, Measure.map_map measurable_fst Measurable.of_discrete, adaptSubStep,
    ← coupledIncr_fst (δ * lam s.1.2.1) (δ * lam s.2.2.1),
    Measure.map_map Measurable.of_discrete measurable_fst]
  rfl

/-- The coarse component of the coupled step is the coarse path's own step (`coupledIncr_snd`;
Giles 2015, §8, pp. 55–56). -/
lemma adaptCoupledStep_snd (νf νc : ℕ → ℕ → ℕ) (j : ℕ) (s : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :
    (adaptCoupledStep lam δ νf νc j s).map Prod.snd = adaptSubStep lam δ νc j s.2 := by
  rw [adaptCoupledStep, Measure.map_map measurable_snd Measurable.of_discrete, adaptSubStep,
    ← coupledIncr_snd (δ * lam s.1.2.1) (δ * lam s.2.2.1),
    Measure.map_map Measurable.of_discrete measurable_snd]
  rfl

/-- The fine path of the coupled base-interval simulation is the fine path alone (Giles 2015, §8):
its marginal does not depend on the coarse path. -/
lemma adaptCoupledRun_fst (νf νc : ℕ → ℕ → ℕ) (j : ℕ) :
    ∀ r s, (adaptCoupledRun lam δ νf νc j r s).map Prod.fst = adaptRun lam δ νf j r s.1
  | 0, s => by rw [adaptCoupledRun_zero, Measure.map_dirac' measurable_fst, adaptRun_zero]
  | r + 1, s => by
      rw [adaptCoupledRun_succ, map_bind_of_discrete _ _ measurable_fst]
      simp_rw [adaptCoupledStep_fst]
      rw [← bind_map_of_discrete (adaptCoupledRun lam δ νf νc j r s) Prod.fst,
        adaptCoupledRun_fst νf νc j r s, adaptRun_succ]

/-- The coarse path of the coupled base-interval simulation is the coarse path alone (Giles 2015,
§8). -/
lemma adaptCoupledRun_snd (νf νc : ℕ → ℕ → ℕ) (j : ℕ) :
    ∀ r s, (adaptCoupledRun lam δ νf νc j r s).map Prod.snd = adaptRun lam δ νc j r s.2
  | 0, s => by rw [adaptCoupledRun_zero, Measure.map_dirac' measurable_snd, adaptRun_zero]
  | r + 1, s => by
      rw [adaptCoupledRun_succ, map_bind_of_discrete _ _ measurable_snd]
      simp_rw [adaptCoupledStep_snd]
      rw [← bind_map_of_discrete (adaptCoupledRun lam δ νf νc j r s) Prod.snd,
        adaptCoupledRun_snd νf νc j r s, adaptRun_succ]

/-! #### The Anderson–Higham split is additive over sub-intervals -/

/-- The Anderson–Higham split for `a ≤ b` (Giles 2015, §8, pp. 55–56, ll. 2393–2407): `P₁ ~ P(a)`
for the path with the smaller rate and `P₁ + P₂`, `P₂ ~ P(b − a)`, for the other one. -/
lemma coupledIncr_of_le {a b : ℝ≥0} (hab : a ≤ b) :
    coupledIncr a b =
      (poissonMeasure a).bind fun i => (poissonMeasure (b - a)).map fun k => (i, i + k) := by
  rw [coupledIncr, min_eq_left hab, max_eq_right hab, Measure.prod_def,
    map_bind_of_discrete _ _ Measurable.of_discrete]
  congr 1
  funext i
  rw [Measure.map_map Measurable.of_discrete measurable_prodMk_left]
  rcases hab.lt_or_eq with hlt | heq
  · congr 1
    funext k
    simp [couplePair, not_lt.2 hab, hlt]
  · subst heq
    rw [tsub_self, poissonMeasure_zero, Measure.map_dirac' Measurable.of_discrete,
      Measure.map_dirac' Measurable.of_discrete]
    simp [couplePair]

/-- The Anderson–Higham split for `b ≤ a` (Giles 2015, §8, pp. 55–56), the mirror image of
`coupledIncr_of_le`. -/
lemma coupledIncr_of_ge {a b : ℝ≥0} (hba : b ≤ a) :
    coupledIncr a b =
      (poissonMeasure b).bind fun i => (poissonMeasure (a - b)).map fun k => (i + k, i) := by
  rw [coupledIncr, min_eq_right hba, max_eq_left hba, Measure.prod_def,
    map_bind_of_discrete _ _ Measurable.of_discrete]
  congr 1
  funext i
  rw [Measure.map_map Measurable.of_discrete measurable_prodMk_left]
  rcases hba.lt_or_eq with hlt | heq
  · congr 1
    funext k
    simp [couplePair, not_lt.2 hba, hlt]
  · subst heq
    rw [tsub_self, poissonMeasure_zero, Measure.map_dirac' Measurable.of_discrete,
      Measure.map_dirac' Measurable.of_discrete]
    simp [couplePair]

/-- With both rates zero the coupled increments vanish (Giles 2015, §8). -/
lemma coupledIncr_zero : coupledIncr 0 0 = Measure.dirac (0, 0) := by
  rw [coupledIncr_of_le le_rfl, tsub_self, poissonMeasure_zero,
    Measure.dirac_bind Measurable.of_discrete, Measure.map_dirac' Measurable.of_discrete]

/-- Adding two independent pairs built from Poisson variates by a map `g` that is additive in both
arguments (Giles 2015, §8, p. 55, ll. 2387–2389): the sum has the law of the pair built from the
summed variates. -/
lemma poisson_pair_bind_map_add {γ : Type*} [MeasurableSpace γ] (m₁ m₂ d₁ d₂ : ℝ≥0)
    (g : ℕ → ℕ → ℕ × ℕ)
    (hg : ∀ i k i' k', g i k + g i' k' = g (i + i') (k + k')) (F : ℕ × ℕ → γ) :
    ((poissonMeasure m₁).bind fun i => (poissonMeasure d₁).map (g i)).bind
        (fun ij => ((poissonMeasure m₂).bind fun i' => (poissonMeasure d₂).map (g i')).map
          fun ij' => F (ij + ij')) =
      ((poissonMeasure (m₁ + m₂)).bind fun i => (poissonMeasure (d₁ + d₂)).map (g i)).map F := by
  have e1 : ∀ ij : ℕ × ℕ,
      ((poissonMeasure m₂).bind fun i' => (poissonMeasure d₂).map (g i')).map
        (fun ij' => F (ij + ij')) =
      (poissonMeasure m₂).bind fun i' => (poissonMeasure d₂).map fun k' => F (ij + g i' k') :=
    fun ij => by
    rw [map_bind_of_discrete _ _ Measurable.of_discrete]
    congr 1
    funext i'
    rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    rfl
  simp_rw [e1]
  rw [Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  have e2 : ∀ i, ((poissonMeasure d₁).map (g i)).bind (fun ij => (poissonMeasure m₂).bind
        fun i' => (poissonMeasure d₂).map fun k' => F (ij + g i' k')) =
      (poissonMeasure m₂).bind fun i' =>
        (poissonMeasure (d₁ + d₂)).map fun k => F (g (i + i') k) := fun i => by
    rw [bind_map_of_discrete, bind_bind_comm_nat]
    congr 1
    funext i'
    have e3 : ∀ k : ℕ, ((poissonMeasure d₂).map fun k' => F (g i k + g i' k')) =
        (poissonMeasure d₂).map fun k' => F (g (i + i') (k + k')) := fun k => by
      simp_rw [hg]
    simp_rw [e3]
    rw [bind_map_comp_add (g := fun k => F (g (i + i') k)), poissonMeasure_conv_poissonMeasure]
  simp_rw [e2]
  rw [bind_bind_add_eq_bind_conv (F := fun n => (poissonMeasure (d₁ + d₂)).map fun k => F (g n k)),
    poissonMeasure_conv_poissonMeasure, map_bind_of_discrete _ _ Measurable.of_discrete]
  congr 1
  funext i
  rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  rfl

/-- **The Anderson–Higham split is additive over sub-intervals** (Giles 2015, §8, pp. 55–56,
ll. 2387–2407: "for any `t₁, t₂ > 0`, the sum of two independent Poisson variates `P(t₁)`,
`P(t₂)` is equivalent in distribution to `P(t₁ + t₂)`", and the split "`P₁ = P(h min(λ(x_n),
λ(x^c_n)))`, `P₂ = P(h|λ(x_n) − λ(x^c_n)|)`").  With the rates `α`, `β` frozen, the split over a
time `s` followed by an independent split over a time `t` adds up to one split over `s + t`:
`(coupledIncr (sα) (sβ)).bind (ij ↦ (coupledIncr (tα) (tβ)).map (ij' ↦ F(ij + ij')))` equals
`(coupledIncr ((s + t)α) ((s + t)β)).map F`, for every `F`. -/
theorem coupledIncr_bind_map_add {γ : Type*} [MeasurableSpace γ] (α β s t : ℝ≥0)
    (F : ℕ × ℕ → γ) :
    (coupledIncr (s * α) (s * β)).bind
        (fun ij => (coupledIncr (t * α) (t * β)).map fun ij' => F (ij + ij')) =
      (coupledIncr ((s + t) * α) ((s + t) * β)).map F := by
  rcases le_total α β with h | h
  · rw [coupledIncr_of_le (mul_le_mul_of_nonneg_left h (by positivity) : s * α ≤ s * β),
      coupledIncr_of_le (mul_le_mul_of_nonneg_left h (by positivity) : t * α ≤ t * β),
      coupledIncr_of_le (mul_le_mul_of_nonneg_left h (by positivity) : (s + t) * α ≤ (s + t) * β),
      ← mul_tsub, ← mul_tsub, ← mul_tsub, add_mul, add_mul]
    refine poisson_pair_bind_map_add _ _ _ _ (fun i k => (i, i + k)) (fun i k i' k' => ?_) F
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨rfl, by ring⟩
  · rw [coupledIncr_of_ge (mul_le_mul_of_nonneg_left h (by positivity) : s * β ≤ s * α),
      coupledIncr_of_ge (mul_le_mul_of_nonneg_left h (by positivity) : t * β ≤ t * α),
      coupledIncr_of_ge (mul_le_mul_of_nonneg_left h (by positivity) : (s + t) * β ≤ (s + t) * α),
      ← mul_tsub, ← mul_tsub, ← mul_tsub, add_mul, add_mul]
    refine poisson_pair_bind_map_add _ _ _ _ (fun i k => (i + k, i)) (fun i k i' k' => ?_) F
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, rfl⟩

/-- A split followed by a second split with the same frozen rates (Giles 2015, §8), in the form used
for runs of the coupled simulation (`coupledIncr_bind_map_add`). -/
lemma coupledIncr_map_bind_eq {β γ : Type*} [MeasurableSpace β] [DiscreteMeasurableSpace β]
    [MeasurableSpace γ] (α β' s t : ℝ≥0) (F : ℕ × ℕ → β) (G : ℕ × ℕ → γ) (κ : β → Measure γ)
    (hκ : ∀ ij, κ (F ij) = (coupledIncr (t * α) (t * β')).map fun ij' => G (ij + ij')) :
    ((coupledIncr (s * α) (s * β')).map F).bind κ =
      (coupledIncr ((s + t) * α) ((s + t) * β')).map G := by
  rw [bind_map_of_discrete, show (fun ij => κ (F ij)) =
      fun ij => (coupledIncr (t * α) (t * β')).map fun ij' => G (ij + ij') from funext hκ,
    coupledIncr_bind_map_add]

/-! #### One union sub-interval is one Anderson–Higham split -/

/-- A count received in two parts within a step is their sum (Giles 2015, §8). -/
lemma tauAdvance_add (ν : ℕ → ℕ → ℕ) (u x a e I I' : ℕ) :
    tauAdvance ν u (x + I, a, e) I' = tauAdvance ν u (x, a, e) (I + I') := by
  simp only [tauAdvance, add_assoc]

/-- Inside a union sub-interval (no step of either path ends before base time `j + m + 1`), after
`r ≤ m` base intervals the coupled simulation has drawn one Anderson–Higham split with the means
`rδλ(a)`, `rδλ(c)` (Giles 2015, §8, p. 55; `coupledIncr_bind_map_add`). -/
lemma adaptCoupledRun_within (νf νc : ℕ → ℕ → ℕ) (j m x a e y c e' : ℕ) (he : j + m + 1 ≤ e)
    (he' : j + m + 1 ≤ e') :
    ∀ r, r ≤ m → adaptCoupledRun lam δ νf νc j r ((x, a, e), (y, c, e')) =
      (coupledIncr ((r : ℝ≥0) * δ * lam a) ((r : ℝ≥0) * δ * lam c)).map
        fun ij => ((x + ij.1, a, e), (y + ij.2, c, e'))
  | 0, _ => by
      rw [adaptCoupledRun_zero]
      simp only [Nat.cast_zero, zero_mul]
      rw [coupledIncr_zero, Measure.map_dirac' Measurable.of_discrete]
      simp only [Nat.add_zero]
  | r + 1, hr => by
      have hne : ¬ (j + r + 1 = e) := by omega
      have hne' : ¬ (j + r + 1 = e') := by omega
      rw [adaptCoupledRun_succ, adaptCoupledRun_within νf νc j m x a e y c e' he he' r (by omega)]
      refine (coupledIncr_map_bind_eq (lam a) (lam c) ((r : ℝ≥0) * δ) δ _
        (fun ij : ℕ × ℕ => ((x + ij.1, a, e), (y + ij.2, c, e'))) _ fun ij => ?_).trans ?_
      · rw [adaptCoupledStep]
        congr 1
        funext ij'
        simp only [tauAdvance, if_neg hne, if_neg hne', Prod.fst_add, Prod.snd_add]
        simp only [add_assoc]
      · congr 3 <;> push_cast <;> ring

/-- **On a union sub-interval the base-interval simulation is one Anderson–Higham split** (Giles
2015, §8, p. 56, ll. 2442–2446: "Poisson variates for each time interval", coupled as on pp. 55–56,
ll. 2393–2407).  If no step of the fine path `(x, a, e)` or of the coarse path `(y, c, e')` ends
before base time `j + m + 1` (`j + m + 1 ≤ e, e'`), the coupled simulation over the `m + 1` base
intervals `j, …, j + m` is one split `coupledIncr ((m + 1)δλ(a)) ((m + 1)δλ(c))` of the frozen
propensities, the fine count going to the fine path and the coarse count to the coarse path, each
of which ends its step at `j + m + 1` if it is due to.  So simulating on the base intervals is
simulating on the union sub-intervals, as in Algorithm 3. -/
lemma adaptCoupledRun_union (νf νc : ℕ → ℕ → ℕ) (j m x a e y c e' : ℕ)
    (he : j + m + 1 ≤ e) (he' : j + m + 1 ≤ e') :
    adaptCoupledRun lam δ νf νc j (m + 1) ((x, a, e), (y, c, e')) =
      (coupledIncr (((m + 1 : ℕ) : ℝ≥0) * δ * lam a) (((m + 1 : ℕ) : ℝ≥0) * δ * lam c)).map
        fun ij => (tauAdvance νf (j + m + 1) (x, a, e) ij.1,
          tauAdvance νc (j + m + 1) (y, c, e') ij.2) := by
  rw [adaptCoupledRun_succ, adaptCoupledRun_within lam δ νf νc j m x a e y c e' he he' m le_rfl]
  refine (coupledIncr_map_bind_eq (lam a) (lam c) ((m : ℝ≥0) * δ) δ _
    (fun ij : ℕ × ℕ => (tauAdvance νf (j + m + 1) (x, a, e) ij.1,
      tauAdvance νc (j + m + 1) (y, c, e') ij.2)) _ fun ij => ?_).trans ?_
  · rw [adaptCoupledStep]
    congr 1
    funext ij'
    rw [tauAdvance_add, tauAdvance_add]
    rfl
  · congr 3 <;> push_cast <;> ring

/-- Running the coupled simulation for `n + r` base intervals is running it for `n`, then for `r`
more (Giles 2015, §8 and §5.6, Algorithm 3). -/
lemma adaptCoupledRun_add (νf νc : ℕ → ℕ → ℕ) (j n : ℕ) (s : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :
    ∀ r, adaptCoupledRun lam δ νf νc j (n + r) s =
      (adaptCoupledRun lam δ νf νc j n s).bind (adaptCoupledRun lam δ νf νc (j + n) r)
  | 0 => by
      rw [Nat.add_zero]
      exact Measure.bind_dirac.symm
  | r + 1 => by
      rw [← Nat.add_assoc, adaptCoupledRun_succ, adaptCoupledRun_add νf νc j n s r,
        Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
      congr 1
      funext q
      rw [adaptCoupledRun_succ, Nat.add_assoc]

/-- The union-grid loop stops at `M`: from a state at a base time `≥ M` it stays there (Giles 2015,
§8 and §5.6, Algorithm 3: "while `(t < T)` do"). -/
lemma adaptUnionRun_stop (νf νc : ℕ → ℕ → ℕ) (M : ℕ) :
    ∀ K (q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)), M ≤ q.1 →
      adaptUnionRun lam δ νf νc M K q = Measure.dirac q
  | 0, q, _ => adaptUnionRun_zero lam δ νf νc M q
  | K + 1, q, hq => by
      rw [adaptUnionRun_succ, adaptUnionStep, if_pos hq,
        Measure.dirac_bind Measurable.of_discrete, adaptUnionRun_stop νf νc M K q hq]

/-- After a union sub-interval ending at `u < M` with `u ≤ e`, the current step of a path ends after
`u`, when its rule is admissible (steps of at least one base interval before `M`; an invariant of
the union-grid loop, Giles 2015, §5.6, Algorithm 3). -/
lemma tauAdvance_end_gt {ν : ℕ → ℕ → ℕ} {M : ℕ} (hν1 : ∀ t < M, ∀ x, 1 ≤ ν t x)
    {u x a e : ℕ} (hu : u < M) (hue : u ≤ e) (i : ℕ) :
    u < (tauAdvance ν u (x, a, e) i).2.2 := by
  by_cases h : u = e
  · simp only [tauAdvance, if_pos h]
    have := hν1 u hu (x + i)
    omega
  · simp only [tauAdvance, if_neg h]
    omega

/-- After a union sub-interval ending at `u < M`, the current step of a path still ends at or before
`M` if it did before, when its rule is truncated (steps before `M` end at or before `M`, as
`t^c := min(t^c + h^c, T)` in Giles 2015, §5.6, Algorithm 3). -/
lemma tauAdvance_end_le {ν : ℕ → ℕ → ℕ} {M : ℕ} (hνM : ∀ t < M, ∀ x, t + ν t x ≤ M)
    {u x a e : ℕ} (hu : u < M) (heM : e ≤ M) (i : ℕ) :
    (tauAdvance ν u (x, a, e) i).2.2 ≤ M := by
  by_cases h : u = e
  · simp only [tauAdvance, if_pos h]
    exact hνM u hu (x + i)
  · simp only [tauAdvance, if_neg h]
    exact heM

/-- **The union-grid loop is the base-interval simulation**, general form (Giles 2015, §8 and §5.6,
Algorithm 3), by induction on the remaining time `d = M − j`.  The invariant at base time `j < M`:
both current steps end after `j`, and the step of a path whose rule is truncated ends at or before
`M`.  Since at least one rule is truncated (`hT`), the next union point `u = min(e, e')` lies in
`(j, M]`, one iteration of the loop is the base-interval simulation up to `u`
(`adaptCoupledRun_union`), and the invariant holds again at `u` (`tauAdvance_end_gt`, which needs
both rules admissible, and `tauAdvance_end_le`).  At `M` both have stopped. -/
lemma adaptUnionRun_eq (νf νc : ℕ → ℕ → ℕ) {M : ℕ} (hf1 : ∀ t < M, ∀ x, 1 ≤ νf t x)
    (hc1 : ∀ t < M, ∀ x, 1 ≤ νc t x)
    (hT : (∀ t < M, ∀ x, t + νf t x ≤ M) ∨ ∀ t < M, ∀ x, t + νc t x ≤ M) (d : ℕ) :
    ∀ (j : ℕ) (s : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) (K : ℕ), j + d = M →
      (j < M → j < s.1.2.2 ∧ j < s.2.2.2 ∧
        ((∀ t < M, ∀ x, t + νf t x ≤ M) → s.1.2.2 ≤ M) ∧
        ((∀ t < M, ∀ x, t + νc t x ≤ M) → s.2.2.2 ≤ M)) → d ≤ K →
      (adaptUnionRun lam δ νf νc M K (j, s)).map Prod.snd =
        adaptCoupledRun lam δ νf νc j d s := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j s K hjd hinv hdK
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [adaptUnionRun_stop lam δ νf νc M K (j, s) (by simp only; omega),
        Measure.map_dirac' measurable_snd, adaptCoupledRun_zero]
    · have hj : j < M := by omega
      obtain ⟨⟨x, a, e⟩, ⟨y, c, e'⟩⟩ := s
      obtain ⟨hje, hje', heM, he'M⟩ := hinv hj
      simp only at hje hje' heM he'M
      have huM : min e e' ≤ M := by
        rcases hT with hT | hT
        · exact (min_le_left e e').trans (heM hT)
        · exact (min_le_right e e').trans (he'M hT)
      obtain ⟨m, hm⟩ : ∃ m, min e e' = j + m + 1 :=
        ⟨min e e' - j - 1, by have := lt_min hje hje'; omega⟩
      have hme : j + m + 1 ≤ e := hm ▸ min_le_left e e'
      have hme' : j + m + 1 ≤ e' := hm ▸ min_le_right e e'
      obtain ⟨d', hd'⟩ : ∃ d', d = (m + 1) + d' := ⟨d - (m + 1), by omega⟩
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have hstep : adaptUnionStep lam δ νf νc M (j, (x, a, e), (y, c, e')) =
          (coupledIncr (((m + 1 : ℕ) : ℝ≥0) * δ * lam a) (((m + 1 : ℕ) : ℝ≥0) * δ * lam c)).map
            fun ij => (j + m + 1, tauAdvance νf (j + m + 1) (x, a, e) ij.1,
              tauAdvance νc (j + m + 1) (y, c, e') ij.2) := by
        have hu : min e e' - j = m + 1 := by omega
        rw [adaptUnionStep, if_neg (by simp only; omega)]
        dsimp only
        rw [hu, hm]
      rw [adaptUnionRun_succ, hstep, bind_map_of_discrete,
        map_bind_of_discrete _ _ measurable_snd, hd', adaptCoupledRun_add,
        adaptCoupledRun_union lam δ νf νc j m x a e y c e' hme hme', bind_map_of_discrete]
      congr 1
      funext ij
      refine ih d' (by omega) (j + m + 1) _ K' (by omega) (fun hu => ?_) (by omega)
      exact ⟨tauAdvance_end_gt hf1 hu hme ij.1, tauAdvance_end_gt hc1 hu hme' ij.2,
        fun hT => tauAdvance_end_le hT hu (heM hT) ij.1,
        fun hT => tauAdvance_end_le hT hu (he'M hT) ij.2⟩

/-- The initial state of the union-grid loop (Giles 2015, §5.6, p. 45, ll. 1940–1942, Algorithm 3:
"`t := 0`, `t^c := 0`, `t^f := 0`"): base time `0`, both paths at `x₀` and at the start of their
first step. -/
def adaptUnionInit (νf νc : ℕ → ℕ → ℕ) (x₀ : ℕ) : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) :=
  (0, adaptStart νf 0 x₀, adaptStart νc 0 x₀)

/-- **The union-grid loop is the simulation with one Anderson–Higham split per base interval**
(Giles 2015, §5.6, p. 44, ll. 1926–1929: "The underlying Brownian path needs to be sampled at a set
of times which are the union of the simulation times used by the coarse and fine path. The
independent Brownian increments can be simulated for each time interval, and summed to give `W(t)`
at the required times"; §8, p. 56, ll. 2444–2446: "the construction is exactly the same as
illustrated in Figure 5.9, but with Poisson variates for each time interval instead of Brownian
increments").  Let both rules be admissible (`1 ≤ ν(t, x)` for `t < M`: steps of at least one
base interval) and at least one of them truncated (`t + ν(t, x) ≤ M` for `t < M`, as
`t^c := min(t^c + h^c, T)` in Algorithm 3).  Then the pair of path states after `M` iterations of
the union-grid loop (`adaptUnionStep`, one split per union sub-interval; each iteration advances by
at least one base interval) has the law of the pair after the `M` base intervals of the simulation
`adaptCoupledRun` that draws one split `coupledIncr (δλ(a)) (δλ(c))` per base interval: the counts
of the union sub-intervals are the sums of the counts of their base intervals
(`coupledIncr_bind_map_add`).  Admissibility keeps the loop from stalling, and without a truncated
rule the last union point could lie beyond `M`. -/
theorem adaptUnion_baseGrid (νf νc : ℕ → ℕ → ℕ) {M : ℕ} (hf1 : ∀ t < M, ∀ x, 1 ≤ νf t x)
    (hc1 : ∀ t < M, ∀ x, 1 ≤ νc t x)
    (hT : (∀ t < M, ∀ x, t + νf t x ≤ M) ∨ ∀ t < M, ∀ x, t + νc t x ≤ M) (x₀ : ℕ) :
    (adaptUnionRun lam δ νf νc M M (adaptUnionInit νf νc x₀)).map Prod.snd =
      adaptCoupledRun lam δ νf νc 0 M (adaptStart νf 0 x₀, adaptStart νc 0 x₀) := by
  refine adaptUnionRun_eq lam δ νf νc hf1 hc1 hT M 0 _ M (Nat.zero_add M) (fun h0 => ?_) le_rfl
  simp only [adaptStart]
  exact ⟨by have := hf1 0 h0 x₀; omega, by have := hc1 0 h0 x₀; omega, fun h => h 0 h0 x₀,
    fun h => h 0 h0 x₀⟩

/-- **The fine path of adaptive tau-leaping MLMC has the law of its single-level scheme** (Giles
2015, §8, p. 56, ll. 2442–2447: "The non-nested adaptive timestepping approach described in
Section 5.6 for SDEs is equally applicable in this setting. … the construction is exactly the same
as illustrated in Figure 5.9, but with Poisson variates for each time interval instead of Brownian
increments. This adaptive timestepping can be very helpful in cases in which propensities vary
greatly in time"; §5.6, p. 44, ll. 1919–1920: "a completely independent adaptation on each level
of refinement").  Let the fine and the coarse path have independent adaptation rules `νf`, `νc` (in
units of a base spacing `δ`, depending on the time and the state at the start of a step, as
`h_ℓ = 2^{−ℓ} H(Ŝ_n)` does).  Let the fine rule be truncated: before `T = Mδ` it makes steps of at
least one base interval that end at or before `M` (e.g. `ν(t, x) = min(n(x), M − t)` with `n ≥ 1`,
the truncation `t^f := min(t^f + h^f, T)` of Algorithm 3); let the coarse rule be admissible: before
`M` its steps have at least one base interval (its steps may overshoot `M`; the loop still stops at
`M`).  In the union-grid loop (`adaptUnionStep`: on each union sub-interval one Anderson–Higham
split of the propensities frozen at the starts of the two current steps), after `M` iterations
(when `T` is reached) the fine state has the law of the fine single-level adaptive tau-leaping
scheme `adaptTauRun λ δ νf` at `T`, whatever the admissible coarse rule.  The propensity
`λ : ℕ → [0, ∞)` is arbitrary (state dependent, not necessarily bounded).  Deviations: step sizes
are multiples of `δ`, and the laws compared are those of the state at `T` (payoffs of the terminal
state). -/
theorem adaptUnion_fine (νf νc : ℕ → ℕ → ℕ) {M : ℕ} (hf1 : ∀ t < M, ∀ x, 1 ≤ νf t x)
    (hfM : ∀ t < M, ∀ x, t + νf t x ≤ M) (hc1 : ∀ t < M, ∀ x, 1 ≤ νc t x) (x₀ : ℕ) :
    (adaptUnionRun lam δ νf νc M M (adaptUnionInit νf νc x₀)).map (fun q => q.2.1.1) =
      (adaptTauRun lam δ νf M M (0, x₀)).map Prod.snd := by
  rw [show (fun q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => q.2.1.1) =
      ((fun p : ℕ × ℕ × ℕ => p.1) ∘ Prod.fst) ∘ Prod.snd from rfl,
    ← Measure.map_map Measurable.of_discrete measurable_snd,
    adaptUnion_baseGrid lam δ νf νc hf1 hc1 (Or.inl hfM),
    ← Measure.map_map Measurable.of_discrete measurable_fst, adaptCoupledRun_fst]
  exact adaptRun_law lam δ νf hf1 hfM x₀

/-- **The coarse path of adaptive tau-leaping MLMC has the law of its single-level scheme** (Giles
2015, §8, p. 56, ll. 2444–2446: "the construction is exactly the same as illustrated in Figure 5.9,
but with Poisson variates for each time interval instead of Brownian increments"; §5.6, p. 44,
ll. 1919–1920: "a completely independent adaptation on each level of refinement"; the mirror image
of `adaptUnion_fine`).  If the coarse rule is truncated (before `T = Mδ`, steps of at least one
base interval that end at or before `M`) and the fine rule admissible (steps of at least one base
interval before `M`), then after `M` iterations of the union-grid loop the coarse state has the law
of the coarse single-level adaptive tau-leaping scheme `adaptTauRun λ δ νc` at `T`, whatever the
admissible fine rule. -/
theorem adaptUnion_coarse (νf νc : ℕ → ℕ → ℕ) {M : ℕ} (hf1 : ∀ t < M, ∀ x, 1 ≤ νf t x)
    (hc1 : ∀ t < M, ∀ x, 1 ≤ νc t x) (hcM : ∀ t < M, ∀ x, t + νc t x ≤ M) (x₀ : ℕ) :
    (adaptUnionRun lam δ νf νc M M (adaptUnionInit νf νc x₀)).map (fun q => q.2.2.1) =
      (adaptTauRun lam δ νc M M (0, x₀)).map Prod.snd := by
  rw [show (fun q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => q.2.2.1) =
      ((fun p : ℕ × ℕ × ℕ => p.1) ∘ Prod.snd) ∘ Prod.snd from rfl,
    ← Measure.map_map Measurable.of_discrete measurable_snd,
    adaptUnion_baseGrid lam δ νf νc hf1 hc1 (Or.inr hcM),
    ← Measure.map_map Measurable.of_discrete measurable_snd, adaptCoupledRun_snd]
  exact adaptRun_law lam δ νc hc1 hcM x₀

/-- **(2.4) for adaptive tau-leaping with state-dependent propensities** (Giles 2015, §2.1, p. 8,
ll. 378–382: "Provided we maintain the identity `E[P^f_ℓ] = E[P^c_ℓ]` (2.4) so that the expectation
on level `ℓ` is the same for the two approximations"; §8, p. 56, ll. 2442–2447; §5.6, p. 44,
ll. 1923–1925: "This results in timesteps which are not naturally nested. It may appear that this
would cause difficulties in the MLMC implementation, but Figure 5.9 tries to illustrate that it
does not").  The level-`ℓ` path, with its rule `ν`, is simulated as the coarse path of a
level-`(ℓ + 1)` sample (union-grid loop with the fine rule `ν'`) and as the fine path of a
level-`ℓ` sample (union-grid loop with the coarse rule `ν''`), on the same base spacing `δ` (e.g.
that of the finest level).  If the level-`ℓ` rule is truncated (before `T = Mδ`, steps of at least
one base interval that end at or before `M`) and the rules of the neighbouring levels are
admissible (steps of at least one base interval before `M`), then the two level-`ℓ` states at `T`
have the same law; so for every payoff `Φ` of the terminal state, `P^c_ℓ = Φ(x^c_T)` is
integrable iff `P^f_ℓ = Φ(x_T)` is, and `E[P^c_ℓ] = E[P^f_ℓ]`. -/
theorem adaptUnion_2_4 (ν ν' ν'' : ℕ → ℕ → ℕ) {M : ℕ}
    (h1 : ∀ t < M, ∀ x, 1 ≤ ν t x) (hM : ∀ t < M, ∀ x, t + ν t x ≤ M)
    (h1' : ∀ t < M, ∀ x, 1 ≤ ν' t x) (h1'' : ∀ t < M, ∀ x, 1 ≤ ν'' t x) (x₀ : ℕ) (Φ : ℕ → ℝ) :
    (adaptUnionRun lam δ ν' ν M M (adaptUnionInit ν' ν x₀)).map (fun q => q.2.2.1) =
        (adaptUnionRun lam δ ν ν'' M M (adaptUnionInit ν ν'' x₀)).map (fun q => q.2.1.1) ∧
      (Integrable (fun q => Φ q.2.2.1) (adaptUnionRun lam δ ν' ν M M (adaptUnionInit ν' ν x₀)) ↔
        Integrable (fun q => Φ q.2.1.1)
          (adaptUnionRun lam δ ν ν'' M M (adaptUnionInit ν ν'' x₀))) ∧
      ∫ q, Φ q.2.2.1 ∂(adaptUnionRun lam δ ν' ν M M (adaptUnionInit ν' ν x₀)) =
        ∫ q, Φ q.2.1.1 ∂(adaptUnionRun lam δ ν ν'' M M (adaptUnionInit ν ν'' x₀)) := by
  have hlaw : (adaptUnionRun lam δ ν' ν M M (adaptUnionInit ν' ν x₀)).map (fun q => q.2.2.1) =
      (adaptUnionRun lam δ ν ν'' M M (adaptUnionInit ν ν'' x₀)).map (fun q => q.2.1.1) := by
    rw [adaptUnion_coarse lam δ ν' ν h1' h1 hM, adaptUnion_fine lam δ ν ν'' h1 hM h1'']
  refine ⟨hlaw, ?_, ?_⟩
  · show Integrable (Φ ∘ fun q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => q.2.2.1) _ ↔
      Integrable (Φ ∘ fun q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => q.2.1.1) _
    rw [← integrable_map_measure (Measurable.of_discrete (f := Φ)).aestronglyMeasurable
        (Measurable.of_discrete
          (f := fun q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => q.2.2.1)).aemeasurable,
      hlaw, integrable_map_measure (Measurable.of_discrete (f := Φ)).aestronglyMeasurable
        (Measurable.of_discrete
          (f := fun q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => q.2.1.1)).aemeasurable]
  · rw [← integral_map (Measurable.of_discrete
        (f := fun q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => q.2.2.1)).aemeasurable
        (Measurable.of_discrete (f := Φ)).aestronglyMeasurable, hlaw,
      integral_map (Measurable.of_discrete
        (f := fun q : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => q.2.1.1)).aemeasurable
        (Measurable.of_discrete (f := Φ)).aestronglyMeasurable]

end Adaptive

end MLMC
