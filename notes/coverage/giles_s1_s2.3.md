# Coverage audit C1: Giles (2015) §1 – §2.3 against `MlmcLean/`

Auditor: independent coverage audit, read-only. Paper text: `docs/giles2015.txt` lines 1–567
(pp. 1–12 of the author's version, up to the heading "2.4. Multi-Index Monte Carlo"). Formulas
that the text extraction garbles were checked against the typeset PDF with
`pdftotext -layout` (pp. 11–12: the ML2R weight conditions read "= 1", and the bias reads
`O(2^{−αL²})`, as printed).

What I checked: the Lean statements themselves, meaning every hypothesis and conclusion and the
quantifier order, and not only the docstrings. Documentation was checked in `README.md`, `PLAN.md`,
`notes/statement-audit.md`, `notes/research-notes.md` and the module docstrings. I used
`notes/readbacks/*` only as leads.

Status legend:
* **DONE**: a Lean theorem states the claim, or a stronger or corrected version of it (corrections noted).
* **DONE-DEV**: formalised with a documented deviation in the hypotheses or the modelling, so the Lean statement is not simply stronger than the paper's.
* **PARTIAL**: part of the claim is formalised, and the notes say exactly what is missing.
* **MISSING**: can be formalised with Mathlib-level mathematics, is not formalised, and is not documented as a gap.
* **OUT-OF-SCOPE**: needs theory that Mathlib lacks.
* **N/A**: empirical, historical, a definition, or informal prose.

All Lean files are in `MlmcLean/`. Lean names in `code` are declarations. Unless
the notes say otherwise, each one is a main theorem listed in `scripts/AxiomCheck.lean`; the
helper lemmas `alg1Level_spec`, `anchor_le_alg1Rem`, `crossDiff_one`, `mem_indexSet`,
`mlqmcInner_variance` and `mlqmcState_variance` cited in the §2.4–§3 tables are not listed there
themselves (they are covered through the theorems that use them).

## Counts

| Section | DONE | DONE-DEV | PARTIAL | MISSING | OUT-OF-SCOPE | N/A | total |
|---|---|---|---|---|---|---|---|
| §1 (G1) | 20 | 2 | 0 | 0 | 1 | 14 | 37 |
| §2.1 (G2.1) | 28 | 3 | 0 | 2 | 1 | 12 | 46 |
| §2.2 (G2.2) | 9 | 7 | 1 | 0 | 0 | 4 | 21 |
| §2.3 (G2.3) | 7 | 0 | 3 | 0 | 0 | 4 | 14 |
| **all** | **64** | **12** | **4** | **2** | **2** | **34** | **118** |

---

## §1 Introduction

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G1-01 | l.40–48, p.2 | "Stochastic modelling and simulation is a growing area…" | N/A | – | context |
| G1-02 | l.49–59, p.2 | low-dim uncertainty → Fokker–Planck / stochastic Galerkin / moment methods; "when … high-dimensional and strongly nonlinear, Monte Carlo simulation remains the preferred approach" | N/A | – | informal |
| G1-03 | l.60–64, p.2 | simple MC estimate `N⁻¹ ∑ P(ω⁽ⁿ⁾)` from N independent samples | N/A (def.) | the estimator in `mc_estimate` (ControlVariate.lean), `blockMean` (SampleMean.lean) | definition, formalised |
| G1-04 | l.65, p.2 | "The variance of this estimate is `N⁻¹V[P]`" | DONE | `mc_estimate`, `variance_sample_mean` (Theorem1.lean), `variance_blockMean` | exact, for i.i.d. inputs (`iIndepFun`, `MeasurePreserving`) |
| G1-05 | l.65, p.2 | "so the r.m.s. error is `O(N^{−1/2})`" | DONE | `mc_estimate` | MSE = `V[P]/N` exactly |
| G1-06 | l.66, p.2 | "an accuracy of ε requires `N = O(ε⁻²)` samples" | DONE | `mc_estimate` (r.m.s. ≤ ε ⟺ `N ≥ ε⁻²V[P]`), `mc_cost` (CostComparison.lean) | stronger (iff) |
| G1-07 | l.66–69, p.2 | "This is the weakness of Monte Carlo simulation…" | N/A | – | prose |
| G1-08 | l.70–74, p.2 | QMC: "In the best cases, the error may be `O(N⁻¹)`, up to logarithmic terms" | OUT-OF-SCOPE | – | QMC theory. Documented: README l.28–30 ("QMC … not formalised in general") and PLAN l.153–155 Round 20, in `d` dimensions (`LatticeRuleD.lean`): for a randomly shifted rank-1 lattice rule the variance is the dual-lattice sum `∑_{k ∈ L^⊥∖{0}} \|f̂(k)\|²` (`hasSum_variance_rank1Lattice`), with unbiased replicates (`rank1Lattice_replicates`) and the bound `\|Q(u) − ∫f\| ≤ ∑_{L^⊥∖{0}} \|f̂(k)\|` for every shift (`abs_rank1Lattice_sub_integral_le`); MLQMC with level-dependent dimension has cost `O(ε^{−p})` with `p < 2` when `g < 2a` and `g < a + b`, assuming dual-lattice sums `≤ (c₂ 2^{−bℓ}/N)²` for `N = 2^m` points (`mlqmcLattice_complexity`, `mlqmcLattice_complexity_of_lt`, `mlqmcLattice_complexity_lt_two`, `mlqmcLattice_complexity_rate`). That good generating vectors exist (the `O(N⁻¹)` itself) is not formalised. Spot-check 21: with round 12 (`QMC1D.lean`, one dimension) and round 20 the row is in effect PARTIAL; what is missing is the existence of good generating vectors. |
| G1-09 | l.75–78, p.2 | QMC surveyed in Acta Numerica 2013; this article covers MLMC | N/A | – | |
| G1-10 | l.83–86, p.3 | control variate `g`, well correlated with `f`, with known `E[g]` | N/A (def.) | `correlation` (ControlVariate.lean) | |
| G1-11 | l.86–92, p.3 | "unbiased estimator for `E[f]` … `N⁻¹∑{f(ω⁽ⁿ⁾) − λ(g(ω⁽ⁿ⁾) − E[g])}`" | DONE | `controlVariate_mean`, `controlVariate_estimator` | |
| G1-12 | l.93–95, p.3 | "The optimal value for λ is `ρ√(V[f]/V[g])`" | DONE | `controlVariate_optimal` | `IsLeast` plus "attained iff λ = ρ√(V[f]/V[g])", for `V[f], V[g] > 0` (needed for ρ to be defined) |
| G1-13 | l.95–96, p.3 | "variance … reduced by factor `1 − ρ²` compared to the standard estimator" | DONE | `controlVariate_optimal`, `controlVariate_estimator` (3rd conjunct) | |
| G1-14 | l.97–99, p.3 | `E[P₁] = E[P₀] + E[P₁ − P₀]` | DONE | `sum_integral_levelDiff` (LevelDiff.lean) with L = 1 | |
| G1-15 | l.100–110, p.3 | "the unbiased two-level estimator `N₀⁻¹∑P₀⁽ⁿ⁾ + N₁⁻¹∑(P₁⁽ⁿ⁾ − P₀⁽ⁿ⁾)`" | DONE | `mlmcEstimator_mean_variance` (StandardEstimator.lean), L = 1 | |
| G1-16 | l.111–118, p.3 | "`P₁⁽ⁿ⁾ − P₀⁽ⁿ⁾` is small and has a small variance" | N/A | – | heuristic |
| G1-17 | l.118–120, p.3 | the differences from a control variate: `E[P₀]` must be estimated, and λ = 1 | N/A | – | descriptive |
| G1-18 | l.121–122, p.3 | "the total cost is `N₀C₀ + N₁C₁`" | N/A (def.) | `totalCost`; E[cost] = ∑N_ℓC_ℓ by linearity inside `giles_theorem1` / `giles_theorem1_standard` | follows from the definitions |
| G1-19 | l.122–134, p.3 | "overall variance is `N₀⁻¹V₀ + N₁⁻¹V₁`, assuming … independent samples" | DONE | `mlmcEstimator_mean_variance` (L = 1), `mlmc_variance` + `variance_sample_mean` | |
| G1-20 | l.135–138, p.3 | "treating N₀, N₁ as real variables … the variance is minimised for a fixed cost by choosing `N₁/N₀ = √(V₁/C₁)/√(V₀/C₀)`" | DONE | `twoLevel_optimal_ratio`, `optimal_variance_isLeast` (Allocation.lean) | iff; global minimum, not only a stationary point |
| G1-21 | l.141–148, p.3–4 | `E[P_L] = E[P₀] + ∑_{ℓ=1}^L E[P_ℓ − P_{ℓ−1}]` | DONE | `sum_integral_levelDiff` | |
| G1-22 | l.149–162, p.4 | unbiased multilevel estimator of `E[P_L]`, "independent samples are used at each level of correction" | DONE | `mlmcEstimator_mean_variance`, `integral_levelEstimator`, `indepFun_levelEstimator` | |
| G1-23 | l.163–168, p.4 | "the overall cost and variance of the multilevel estimator is `∑N_ℓC_ℓ` and `∑N_ℓ⁻¹V_ℓ`" | DONE | `mlmcEstimator_mean_variance` (variance); cost: `totalCost` and linearity (in the proof of `giles_theorem1`) | cost part is by definition |
| G1-24 | l.169–174, p.4 | minimise `∑(N_ℓC_ℓ + μ²N_ℓ⁻¹V_ℓ)` … "This gives `N_ℓ = μ√(V_ℓ/C_ℓ)`" | DONE | `optimal_cost_isLeast`, `lagrangeN_unique`, `lagrangeN` | the minimiser is unique and has this form. The Lagrangian step itself is only the internal lemma `lagrange_term` (not audited) |
| G1-25 | l.175–177, p.4 | "variance of ε² then requires that `μ = ε⁻²∑√(V_ℓC_ℓ)`" | DONE | `lagrangeN_variance_cost` | |
| G1-26 | l.177–182, p.4 | **(1.1)** `C = ε⁻²(∑√(V_ℓC_ℓ))²` | DONE | `optimal_cost_isLeast`, `cost_lower_bound`, `optimalN_cost` | stronger: least cost over **all** real allocations (Cauchy–Schwarz), with a rounded-up integer version |
| G1-27 | l.183–185, p.4 | "important to note whether `V_ℓC_ℓ` increases or decreases with ℓ" | N/A | – | |
| G1-28 | l.185–187, p.4 | increasing product ⇒ "`C ≈ ε⁻²V_LC_L`" | DONE-DEV | `optimal_cost_increasing` (ControlVariate.lean) | assumes geometric growth `√(V_{ℓ+1}C_{ℓ+1}) ≥ r√(V_ℓC_ℓ)` with r > 1; gives `ε⁻²V_LC_L ≤ C ≤ (r/(r−1))²ε⁻²V_LC_L`. The docstring calls it the "rigorous form" |
| G1-29 | l.187–188, p.4 | decreasing product ⇒ "`C ≈ ε⁻²V₀C₀`" | DONE-DEV | `optimal_cost_decreasing` | geometric decay with 0 ≤ r < 1; same comment as G1-28 |
| G1-30 | l.188–190, p.4 | "the standard MC cost of approximately `ε⁻²V₀C_L`" (assuming cost(P_L) ≈ cost(P_L − P_{L−1}) and V[P_L] ≈ V[P₀]) | DONE | `mc_cost`, `mc_cost_lower` (CostComparison.lean), `mc_estimate` | exact version with V[P_L]: the cost is ≥ ε⁻²V C, and the minimal N costs ≤ ε⁻²V C + C |
| G1-31 | l.191–193, p.4 | first case: "MLMC cost is reduced by factor `V_L/V₀`, … ratio of `V[P_L − P_{L−1}]` and `V[P_L]`" | DONE | `mlmc_vs_mc_increasing` | an algebraic corollary of `optimal_cost_increasing`. `V_P` is a free parameter, tied to `V[P_L]` only through `mc_cost_lower` |
| G1-32 | l.193–194, p.4 | second case: "reduced by factor `C₀/C_L`" | DONE | `mlmc_vs_mc_decreasing` | factor `(V₀/V_P)(C₀/C_L)` with `V_P = V[P_L]` (≈ V₀ in the paper); stronger |
| G1-33 | l.194–195, p.4 | constant `V_ℓC_ℓ` ⇒ "total cost is `ε⁻²L²V₀C₀ = ε⁻²L²V_LC_L`" | DONE (corrected) | `optimal_cost_const_product`, `equal_cost_per_level` | exact value `ε⁻²(L+1)²V₀C₀` (levels 0..L); ControlVariate.lean docstring: "the paper's L² is its leading order" |
| G1-34 | l.200–212, p.5 | Heinrich: `½(f(x,0)+f(x,1))` as a control variate for `E[f(x,½)]`, applied recursively | N/A | – | historical description |
| G1-35 | l.213–216, p.5 | Brandt et al. multigrid MC | N/A | – | |
| G1-36 | l.217–223, p.5 | Kebaier two-level, general multiplicative factor; Li; Speight | N/A | – | historical. The general-λ control variate is `controlVariate_*` |
| G1-37 | l.224–240, p.5 | outline of the article | N/A | – | |

## §2.1 Geometric MLMC (with Theorem 1)

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G2.1-01 | l.246–251, p.6 | P_ℓ approximates a P that "cannot be simulated exactly" | N/A | – | |
| G2.1-02 | l.251–253, p.6 | **(2.1)** `MSE ≡ E[(Y−E[P])²] = V[Y] + (E[Y]−E[P])²` | DONE | `mse_eq_variance_add_sq_bias` (Estimator.lean) | any real target m |
| G2.1-03 | l.254–260, p.6 | **(2.2)** `Y = ∑Y_ℓ`, `Y_ℓ = N_ℓ⁻¹∑(P_ℓ^{(ℓ,n)} − P_{ℓ−1}^{(ℓ,n)})`, `P_{−1} ≡ 0` | N/A (def.) | `levelEstimator`, `mlmcEstimator`, `levelDiff` | formalised |
| G2.1-04 | l.261–264, p.6 | **(2.3)** `E[Y] = E[P_L]` | DONE | `mlmcEstimator_mean_variance`, `mlmc_mean` | |
| G2.1-05 | l.262–264, p.6 | **(2.3)** `V[Y] = ∑N_ℓ⁻¹V_ℓ`, `V_ℓ ≡ V[P_ℓ − P_{ℓ−1}]` | DONE | `mlmcEstimator_mean_variance`, `mlmc_variance`, `variance_sample_mean` | pairwise independence suffices |
| G2.1-06 | l.265–267, p.6 | MSE < ε² if `V[Y]` and `(E[P_L−P])²` are both `< ½ε²` | DONE | `mse_lt_of_half` (ErrorAnalysis.lean) | |
| G2.1-07 | l.267–270, p.6 | geometric levels "lead to the following theorem" | N/A | – | |
| G2.1-08 | l.271–272, p.6 | Thm 1: "P … random variable, P_ℓ … level ℓ numerical approximation" | DONE | `giles_theorem1` (Theorem1.lean) | P and P_ℓ integrable on (Ω, μ), a standing convention |
| G2.1-09 | l.273–274, p.6 | Thm 1 hyp.: "independent estimators `Y_ℓ` based on `N_ℓ` MC samples, each with expected cost `C_ℓ` and variance `V_ℓ`" | DONE | `giles_theorem1` (`hY`, `hind`, `h_var`, `hCost_int`, `hCost_mean`) | `Y ℓ n` for every n ≥ 1, `V[Y ℓ n] = V_ℓ/n`, random cost with `E[Cost ℓ n] = nC_ℓ`, pairwise independence (weaker than the paper). README "Modelling choices" |
| G2.1-10 | l.274–275, p.6 | "positive constants α, β, γ, c₁, c₂, c₃ such that `α ≥ ½min(β,γ)`" | DONE | `giles_theorem1` (`hα … hαβγ`) | |
| G2.1-11 | l.277, p.6 | (i) `\|E[P_ℓ − P]\| ≤ c₁2^{−αℓ}` | DONE | `h_i` | |
| G2.1-12 | l.278–280, p.6 | (ii) `E[Y_ℓ] = E[P₀]` (ℓ = 0), `E[P_ℓ − P_{ℓ−1}]` (ℓ > 0) | DONE | `h_ii₀`, `h_ii` | required only for n ≥ 1, a weaker hypothesis. statement-audit finding 3; proved for (2.2) (`integral_levelEstimator`) |
| G2.1-13 | l.281, p.6 | (iii) `V_ℓ ≤ c₂2^{−βℓ}` | DONE | `h_iii` | |
| G2.1-14 | l.282, p.6 | (iv) `C_ℓ ≤ c₃2^{γℓ}` | DONE | `h_iv` | |
| G2.1-15 | l.283–284, p.6 | "there exists a positive constant c₄ such that for any ε < e⁻¹ there are values L and N_ℓ" | DONE | `giles_theorem1`, `giles_theorem1_uniform`, `mlmc_complexity_core` | ∃c₄ comes before ∀ε, so c₄ does not depend on ε. `giles_theorem1_uniform`: c₄ depends only on α, β, γ, c₁, c₂, c₃ (stronger). N_ℓ ≥ 1 integers |
| G2.1-16 | l.284–292, p.6–7 | "the multilevel estimator `Y = ∑_{ℓ=0}^L Y_ℓ` has … `MSE < ε²`" | DONE | `giles_theorem1`; `giles_theorem1_standard`, `giles_theorem1_iid` for (2.2) itself | |
| G2.1-17 | l.296–297, p.7 | `E[C] ≤ c₄ε⁻²`, β > γ | DONE | `giles_theorem1` via `complexityBound` | also `giles_theorem1_isBigO` |
| G2.1-18 | l.298, p.7 | `E[C] ≤ c₄ε⁻²(log ε)²`, β = γ | DONE | same | |
| G2.1-19 | l.299, p.7 | `E[C] ≤ c₄ε^{−2−(γ−β)/α}`, β < γ | DONE | same | |
| G2.1-20 | l.300–304, p.7 | "slight generalisation of … (Giles 2008b) … (Cliffe et al. 2011) except … expected costs … simulation cost … itself random" | N/A | (random costs are in `giles_theorem1`) | historical |
| G2.1-21 | l.304–308, p.7 | if (iii) bounds `E[(P_ℓ−P_{ℓ−1})²]` then "it would follow immediately that `α ≥ ½β`" | DONE (corrected) | `weak_rate_of_second_moment` (ErrorAnalysis.lean) | proves that (i) holds with α = β/2, given `E[P_ℓ] → E[P]` (implied by (i)). ErrorAnalysis.lean docstring: taken literally the claim is false, and this is the correct reading |
| G2.1-22 | l.309–312, p.7 | "optimal `N_ℓ` … proportional to `2^{−(β+γ)ℓ/2}` … cost on level ℓ … `2^{(γ−β)ℓ/2}`" | DONE | `lagrangeN_geometric` (GeometricRates.lean) | for exact rates `V_ℓ = c₂2^{−βℓ}`, `C_ℓ = c₃2^{γℓ}` |
| G2.1-23 | l.312–316, p.7 | proof sketch: L chosen so that `(E[Y]−E[P])² < ½ε²`, N_ℓ scaled so that `V[Y] < ½ε²` | DONE-DEV | `exists_L_N`, `mlmc_complexity_core` (Complexity.lean) | split is bias ≤ ε/2, variance ≤ ε²/2 (README "Strict MSE < ε²"). A proof step, not part of the statement |
| G2.1-24 | l.316–318, p.7 | "N_ℓ must be an integer, so the optimal value is rounded up" | DONE | `optimalN_variance`, `optimalN_cost`, `cost_le_of_level` | overhead ∑C_ℓ is absorbed using α ≥ ½min(β,γ) |
| G2.1-25 | l.319–322, p.7 | β > γ: "dominant computational cost is on the coarsest levels where `C_ℓ = O(1)` and `O(ε⁻²)` samples are required" | DONE | `coarsest_level_dominant` (CostComparison.lean) | `τ⁻¹V₀ ≤ N₀ ≤ τ⁻¹√(V₀/C₀)S_∞`; level 0 carries a fixed fraction of the cost |
| G2.1-26 | l.322–324, p.7 | "standard result for … i.i.d. samples; to do better would require … Latin hypercube … or QMC" | N/A | (lower bounds `mc_cost`, `cost_lower_bound`) | informal |
| G2.1-27 | l.325, p.7 | β < γ: "dominant computational cost is on the finest levels" | DONE-DEV | `optimal_cost_increasing` (with r = 2^{(γ−β)/2}) | holds for exact rates / geometric growth only; with upper bounds (iii), (iv) alone it cannot be proved. The rigorous form is documented in the docstring |
| G2.1-28 | l.326, p.7 | "`2^{−αL} = O(ε)`, and hence `C_L = O(ε^{−γ/α})`" | DONE | `finest_cost_le`, `two_rpow_levelL_le` | |
| G2.1-29 | l.327–330, p.7 | "If β = 2α … total cost is `O(C_L)`, corresponding to `O(1)` samples on the finest level" | DONE | `complexityBound_of_two_mul`, `cost_of_beta_eq_two_alpha` (GeometricRates.lean) | for the real Lagrange allocation; rounding adds ≤ 1 sample per level |
| G2.1-30 | l.327–329, p.7 | β = 2α "usually the best that can be achieved since … V ≈ E[(ΔP)²] > (E[ΔP])²" | N/A | (the inequality is a step in `weak_rate_of_second_moment`) | heuristic Round 16: `beta_le_two_alpha`, `beta_le_two_alpha_of_bias` (`GilesCorollaries.lean`). |
| G2.1-31 | l.330, p.7 | "…which is the best that can be achieved" | N/A | – | informal; trivial, since at least one finest-level sample is needed |
| G2.1-32 | l.331–334, p.7 | β = γ: effort and variance "spread approximately evenly across all of the levels; the `(log ε)²` term corresponds to the `L²` factor" | DONE | `equal_cost_per_level`, `exists_L_N` (`L+1 ≤ K₂\|log ε\|`) | |
| G2.1-33 | l.338–345, p.8 | "assumes lots of properties … c₁, c₂ almost never known" | N/A | – | |
| G2.1-34 | l.346–349, p.8 | Collier et al.: modified theorem using the CLT to build a confidence interval for E[P] | OUT-OF-SCOPE | – | the paper cites the result without stating it. The ε → 0 setting with L(ε) → ∞ needs a triangular-array (Lindeberg–Feller) CLT, which is not in the pinned Mathlib. **Not documented** anywhere Spot-check 21: documented and largely resolved in rounds 12 and 14 (resolution table of `notes/coverage/README.md`): the Lindeberg and Lyapunov CLTs for triangular arrays (`tendstoInDistribution_lindeberg`) and Collier et al.'s confidence intervals with the exact and with estimated variances (`tendsto_measureReal_abs_mlmcEstimator_sub_le`, `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd`); the adaptive, stopped algorithm is not formalised (listed in `PLAN.md`). |
| G2.1-35 | l.350–351, p.8 | "the multilevel correction `Y_ℓ` on each level is asymptotically Normally-distributed" | **MISSING** | – | **The pinned Mathlib has the i.i.d. CLT**: `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub` (`Mathlib/Probability/CentralLimitTheorem.lean`). √N(Y_ℓ(N) − E[ΔP_ℓ]) → N(0, V_ℓ) is a direct corollary for `levelEstimator` with i.i.d. inputs. Easy. Not documented Spot-check 21: resolved in round 10, `tendstoInDistribution_levelEstimator` (`AsymptoticNormal.lean`). |
| G2.1-36 | l.351, p.8 | "…and therefore so is Y" | **MISSING** (fixed L) / out of scope (L → ∞) | – | for fixed L with all N_ℓ → ∞ proportionally: charFun factorisation over independent levels plus Lévy continuity (`ProbabilityMeasure.tendsto_iff_tendsto_charFun` is in the pinned Mathlib). Moderate. For L = L(ε) → ∞ (Collier et al.'s setting) it needs Lindeberg–Feller, which Mathlib lacks. Not documented Round 19: the counterexample is a theorem: every level estimator is asymptotically normal, the normalised MLMC estimator tends to `0` in probability, Lindeberg's and Lyapunov's conditions fail (`exists_mlmc_clt_counterexample`, `mlmc_clt_counterexample_conditions`, `EstimatorRemarks.lean`). Spot-check 21: fixed `L` resolved in round 10 (`tendstoInDistribution_mlmcEstimator`), growing `L` under Lyapunov's condition in round 12 (`tendstoInDistribution_mlmcEstimator_lyapunov`). |
| G2.1-37 | l.352–357, p.8 | Haji-Ali et al.: "under certain conditions … negligible benefit in using a non-geometric sequence" | N/A | – | cited result; the conditions are not stated in the paper |
| G2.1-38 | l.357–359, p.8 | "the equal split … is definitely not optimal" | DONE | `split_cost`, `equal_split_cost_le`, `tendsto_split_cost` | |
| G2.1-39 | l.359–362, p.8 | β > γ: "L can be increased significantly with negligible cost … allocate most of the error to the variance term" | DONE | `coarsest_level_dominant`, `tendsto_equal_split_cost`, `tendsto_split_cost` | |
| G2.1-40 | l.362–364, p.8 | "up to a factor 2× improvement in computational cost compared to the equal split" | DONE | `equal_split_cost_le` (improvement ≤ 2(1−θ) when L' ≥ L), `tendsto_equal_split_cost` + `tendsto_split_cost` (factor 2 attained in the limit) | `equal_split_cost_le` reduces to `S_L ≤ S_{L'}` (θ cancels), which is faithful to the paper's weak claim |
| G2.1-41 | l.365–368, p.8 | other estimators are allowed "provided they satisfy … condition ii) which ensures that `E[Y] = E[P_L]`" | DONE | `mlmc_mean`, `giles_theorem1` (abstract Y), `giles_theorem1_corrections` (Corrections.lean) | |
| G2.1-42 | l.369–377, p.8 | fine/coarse estimator `Y_ℓ = N_ℓ⁻¹∑(P^f_ℓ − P^c_{ℓ−1})` | N/A (def.) | `fineCoarseDiff` | |
| G2.1-43 | l.378–388, p.8–9 | **(2.4)** `E[P^f_ℓ] = E[P^c_ℓ]` ⇒ "condition ii) is satisfied and no additional bias … is introduced" | DONE | `integral_fineCoarseDiff`, `giles_theorem1_fineCoarse` | |
| G2.1-44 | l.389–398, p.9 | antithetic estimator `½(P_ℓ(ω)+P_ℓ(ω_a)) − P_{ℓ−1}(ω)` | N/A (def.) | `antitheticDiff` | |
| G2.1-45 | l.399–400, p.9 | "Since `E[P_ℓ(ω_a)] = E[P_ℓ(ω)]`, then again condition ii) is satisfied" | DONE-DEV | `integral_antitheticDiff`, `giles_theorem1_antithetic` | `ω_a = a(ω)` for a measure-preserving map a (Corrections.lean docstring). General couplings go through `giles_theorem1_corrections` |
| G2.1-46 | l.401–402, p.9 | the aim of complex estimators is "a greatly reduced variance" | N/A | – | |

## §2.2 Randomised MLMC for unbiased estimation

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G2.2-01 | l.404–409, p.9 | single-term estimator: N samples, level ℓ with probability p_ℓ | N/A (def.) | `singleTerm`, `singleTermN` (Randomised.lean) | |
| G2.2-02 | l.410–417, p.9 | `Y = N⁻¹∑ p_{ℓ(n)}⁻¹(P^{(n)}_{ℓ(n)} − P^{(n)}_{ℓ(n)−1})` | N/A (def.) | `singleTermN` | |
| G2.2-03 | l.418–429, p.9 | alternative form `Y = ∑_ℓ (p_ℓN)⁻¹∑_{n≤N_ℓ}(…)`, `∑N_ℓ = N`, `E[N_ℓ] = p_ℓN` | DONE | `singleTermN_eq_sum_levels`, `integral_levelCount` | |
| G2.2-04 | l.430–431, p.9 | "both outer summations can be trivially truncated at the (random) level L beyond which N_ℓ = 0" | DONE | `singleTermN_eq_sum_levels` (any finite S that covers the sampled levels) | |
| G2.2-05 | l.431–440, p.9 | "very similar in appearance to the standard MLMC estimator" | N/A | – | |
| G2.2-06 | l.444–452, p.10 | "naturally unbiased … `= ∑E[P_ℓ − P_{ℓ−1}] = E[P]`" | DONE-DEV | `integral_singleTerm`, `singleTerm_unbiased`, `singleTermN_mean_variance` | the implicit hypotheses are made explicit: `∑E\|ΔP_ℓ\| < ∞` (⟺ E\|Y\| < ∞), `E[P_L] → E[P]`, level independent of each ΔP_ℓ. Documented in statement-audit.md §Randomised |
| G2.2-07 | l.453–458, p.10 | `V[Y] = ∑p_ℓ⁻¹(V_ℓ + E_ℓ²) − (∑E_ℓ)²` | DONE-DEV | `singleTerm_variance` (one sample); `singleTermN_mean_variance` (÷N) | assumes `∑p_ℓ⁻¹E[ΔP_ℓ²] < ∞` (⟺ E[Y²] < ∞), documented. The paper's formula is for one sample (N = 1) |
| G2.2-08 | l.459–462, p.10 | `≥ ∑p_ℓ⁻¹V_ℓ` "due to Jensen's inequality" | DONE | `singleTerm_variance_ge` | |
| G2.2-09 | l.463, p.10 | "The choice of probabilities p_ℓ is crucial." | N/A | – | |
| G2.2-10 | l.463–468, p.10 | "for both the variance and the expected cost to be finite, it is necessary that `∑p_ℓ⁻¹V_ℓ < ∞`, `∑p_ℓC_ℓ < ∞`" | DONE-DEV | `randomised_necessary`, `summable_of_memLp_singleTerm`, `integral_cost_level` | cost model: the level-ℓ cost κ_ℓ ≥ 0 is independent of the level (README "Randomised MLMC finiteness") |
| G2.2-11 | l.469–470, p.10 | "possible when β > γ by choosing `p_ℓ ∝ 2^{−(γ+β)ℓ/2}`" | DONE | `randomised_summable`; `randomised_mlmc_finite` | both series finite. Full finiteness of the variance needs the second-moment form of (iii) (`randomised_mlmc_finite`); README and statement-audit document that PLAN M2 overstated this |
| G2.2-12 | l.470–472, p.10 | "so that `p_ℓ⁻¹V_ℓ ∝ 2^{−(β−γ)ℓ/2}`, `p_ℓC_ℓ ∝ 2^{−(β−γ)ℓ/2}`" | DONE | inside the proof of `randomised_summable`; identities `geom_identities` (not audited) | proof-internal, not exported |
| G2.2-13 | l.473, p.10 | "It is not possible when β ≤ γ" | DONE-DEV | `randomised_not_summable` | needs attained rates `V_ℓ ≥ c₂2^{−βℓ}`, `C_ℓ ≥ c₃2^{γℓ}` (the paper's "∝"); documented |
| G2.2-14 | l.473–474, p.10 | "for these cases the estimators constructed by Rhee and Glynn (2013) have infinite expected cost" | DONE-DEV | `randomised_infinite_cost` | any single-term estimator with finite variance, attained rates |
| G2.2-15 | l.475–480, p.10 | "Provided β > γ, the optimal choice for p_ℓ is `p_ℓ = √(V_ℓ/C_ℓ)(∑√(V_ℓ'/C_ℓ'))⁻¹`" | DONE-DEV | `randomised_optimal_p_isLeast`, `randomised_optimal_p_eq`, `randomised_optimal_p` | minimises the product `(∑p_ℓ⁻¹V_ℓ)(∑p_ℓC_ℓ)` (= ε² × the paper's approximate cost). Documented in statement-audit |
| G2.2-16 | l.481–484, p.10 | "If `E_ℓ² ≪ V_ℓ`, … variance ≈ ε² gives `N ≈ ε⁻²∑V_ℓ/p_ℓ`" | **PARTIAL** | `singleTerm_variance_ge` + `singleTermN_mean_variance` (lower half) | proved: N ≥ ε⁻²∑V_ℓ/p_ℓ is necessary. Missing: the matching upper bound, e.g. `E_ℓ² ≤ δV_ℓ ⇒ V[Y] ≤ (1+δ)∑V_ℓ/p_ℓ`. statement-audit documents the "≈" as a heuristic that is not formalised Spot-check 21: the upper bound is round 10's `singleTerm_variance_le_of_sq_le`, `singleTermN_samples_of_sq_le` (factor `1 + δ`). |
| G2.2-17 | l.484–489, p.10 | "`≈ ε⁻²(∑√(V_ℓC_ℓ))(∑√(V_ℓ'/C_ℓ'))`" | DONE | `randomised_optimal_cost` (1st conjunct) | exact identity for the optimal p |
| G2.2-18 | l.490–495, p.10 | "total cost `C = N∑p_ℓC_ℓ ≈ ε⁻²(∑√(V_ℓC_ℓ))²`" | DONE-DEV | `randomised_optimal_cost`, `integral_cost_level` | exact identity `ε⁻²(∑V/p)(∑pC) = ε⁻²S²`; the ≈ inherits G2.2-16 |
| G2.2-19 | l.499, p.11 | "which is the same as the total cost in Eq. (1.1)" | DONE | `randomised_optimal_cost`, `randomised_half_cost` | (1.1) with L = ∞ |
| G2.2-20 | l.499–501, p.11 | "and half the cost of the standard MLMC algorithm in which only half of the MSE budget … is allocated to the variance" | DONE | `randomised_half_cost` | as a limit L → ∞ (for finite L the ratio is S_∞²/(2S_L²) > ½) |
| G2.2-21 | l.502–508, p.11 | practical benefit limited: increase L "at negligible cost" and put almost all of the MSE budget on the variance, "leading to approximately the same total cost" | DONE | `tendsto_split_cost`, `coarsest_level_dominant` | θ_k → 0, L_k → ∞ ⇒ cost → ε⁻²S_∞² |

## §2.3 Multilevel Richardson–Romberg extrapolation

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G2.3-01 | l.510, p.11 | "Richardson extrapolation is a very old technique" | N/A | – | |
| G2.3-02 | l.511–515, p.11 | `P_h − P = ah^α + O(h^{2α})` ⇒ `P_{2h} − P = a(2h)^α + O(h^{2α})` | DONE | step `hR2` inside `richardson_extrapolation` (Richardson.lean) | proof-internal |
| G2.3-03 | l.516–521, p.11 | `P̃ = 2^α/(2^α−1)P_h − 1/(2^α−1)P_{2h}` satisfies `P̃ − P = O(h^{2α})` | DONE | `richardson_extrapolation` | O as h → 0⁺, α > 0 |
| G2.3-04 | l.522–526, p.11 | Giles 2008b: "Multilevel on its own was significantly better … the two together were even better" | N/A | – | empirical |
| G2.3-05 | l.527–528, p.11 | Lemaire–Pagès comprehensive error analysis | N/A | – | |
| G2.3-06 | l.532–535, p.11 | "the unique set of weights w_ℓ … `∑w_ℓ = 1`, `∑w_ℓ2^{−nαℓ} = 1`, n = 1..L" | DONE (corrected) | `ml2r_weights` | the typo "= 1" (confirmed in the PDF) is corrected to "= 0". Existence and uniqueness proved (Lagrange basis at 0). Documented in the Richardson.lean docstrings |
| G2.3-07 | l.537–543, p.12 | `(∑w_ℓE[P_ℓ]) − E[P] = ∑w_ℓ(E[P_ℓ] − E[P])` | DONE | `ml2r_bias_eq` | |
| G2.3-08 | l.529–531 + l.543, p.11–12 | under the regular expansion `E[P_ℓ]−E[P] = ∑_{n≤L}a_n2^{−nαℓ} + O(2^{−αℓL})`: bias `= O(2^{−αL²})` | **PARTIAL** | `ml2r_bias_eq`, `ml2r_bias`, `ml2r_moment_succ`, `abs_ml2rWeight_le`, `sum_abs_ml2rWeight_le` | the printed rate is wrong: the correct order is 2^{−αL(L+1)/2}, and this is documented. **What is missing:** a bound under the paper's hypothesis. (a) `ml2r_bias_eq` gives bias = ∑w_ℓR_ℓ but puts no size condition on R_ℓ. (b) `ml2r_bias` assumes an exact (L+1)-term expansion on the L+1 levels. By the Vandermonde argument that hypothesis holds for **any** data, so it only identifies the bias as `(−1)^L a_{L+1}(L)·2^{−αL(L+1)/2}`, with an L-dependent a_{L+1}. (c) `abs_ml2rWeight_le` (\|w_ℓ\| ≤ B²r^{L−ℓ}) is too weak to bound ∑w_ℓR_ℓ by 2^{−αL(L+1)/2}. This gap is **not documented** Spot-check 21: resolved in round 10 (`ML2RTheorem.lean`): the sharp weight bound `abs_ml2rWeight_le_sharp` and the bias `≤ C_α K 2^{−αL(L+1)/2}` uniformly in `L` (`ml2r_bias_le`). Round 22 (`SpotCheckRemarks.lean`): the level means `E[P_ℓ] = E[P] + d [ℓ = 0]` satisfy the expansion with `a = 0` and the `L`-independent constant `\|d\|`, and their ML2R bias is at least `\|d\| 2^{−αL(L+1)/2}` and not `O(2^{−αL²})` (`ml2r_bias_not_attainable`). |
| G2.3-09 | l.544–551, p.12 | re-arrangement `∑w_ℓE[P_ℓ] = ∑v_ℓE[P_ℓ−P_{ℓ−1}]`, `w_ℓ = v_ℓ − v_{ℓ+1}`, `v_ℓ = ∑_{ℓ'≥ℓ}w_ℓ'` | DONE | `ml2r_rearrange` | any weights |
| G2.3-10 | l.552–558, p.12 | ML2R estimator `Y_ℓ = N_ℓ⁻¹v_ℓ∑_n(P_ℓ^{(ℓ,n)} − P_{ℓ−1}^{(ℓ,n)})` | DONE | `ml2r_estimator_mean_variance` | mean `∑w_ℓE[P_ℓ]`, variance `∑v_ℓ²V_ℓ/N_ℓ` |
| G2.3-11 | l.559–561, p.12 | remaining error O(2^{−αL²}) ⇒ "O(ε) weak error with a value of L which is the square root of the usual value" | DONE (corrected) | `ml2rLevel_bias`, `ml2rLevel_lt_sqrt_levelL` | `L < √(2·L_usual) + 1` with the corrected rate. Conditional on the bias bound (see G2.3-08), as in the paper Round 28 (`ML2RLowerBound.lean`): conversely, if the bias is at least `b 2^{−αL(L+1)/2}` for every `L`, every `L` that admits sample sizes `N_ℓ ≥ 1` with MSE `≤ ε²` has `αL(L+1)/2 ≥ log₂(b/ε)` (`ml2r_cost_lower`), hence `L ≥ √(2 log₂(1/ε)/α) − κ` for `0 < ε < 1` (`ml2r_cost_lower_sqrt`, with `0 < b ≤ 1`): at least `√2` times the square root of the usual value `log₂(1/ε)/α`, up to an additive constant. A Gaussian example with the paper's expansion has such a bias (`ml2r_instance_hypotheses`). |
| G2.3-12 | l.561–562, p.12 | β = γ: "overall cost is reduced to `O(ε⁻²\|log ε\|)`" | **PARTIAL** | `ml2r_complexity_eq`, `ml2r_mse_cost`, `abs_ml2r_coeff_le` | only the deterministic core: it bounds `(c₁2^{−αL(L+1)/2})² + ∑v_ℓ²V_ℓ/N_ℓ < ε²` with `V_ℓ = c₂2^{−βℓ}`, `C_ℓ = c₃2^{γℓ}`. The bias bound `c₁2^{−αL(L+1)/2}` for every L is taken as given and not derived (G2.3-08). There is no probability-space statement (the actual estimator's MSE < ε² and E[cost] ≤ c₄…) like `giles_theorem1_of_core`. The gap is not documented (README states the costs as proved) Spot-check 21: resolved in round 10: MSE `< ε²` and the expected cost for the ML2R estimator itself (`ml2r_theorem_eq`, `ML2RTheorem.lean`). |
| G2.3-13 | l.562–564, p.12 | β < γ: "cost is reduced much more to `O(ε⁻²2^{(γ−β)√(\|log₂ε\|/α)})`" | **PARTIAL** | `ml2r_complexity_lt` | same gaps as G2.3-12. The exponent is `√(2log₂(1/ε)/α)`, √2 times the printed one; the ML2RComplexity.lean docstring documents this as a consequence of the corrected rate Spot-check 21: resolved in round 10 (`ml2r_theorem_lt`), with the exponent `√(2 log₂(1/ε)/α)`. Round 28 (`ML2RLowerBound.lean`): the printed exponent fails. If the bias is at least `b 2^{−αL(L+1)/2}` for every `L`, `V_ℓ ≥ c₂2^{−βℓ}` and `C_ℓ ≥ c₃2^{γℓ}`, every `L` and `N_ℓ ≥ 1` with MSE `≤ ε²` cost at least `c₂c₃ ε⁻² 2^{(γ−β)L}` (`ml2r_cost_lower`), hence at least `c ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}` for `0 < ε < 1` (`ml2r_cost_lower_sqrt`), and for `β < γ` there are no `c`, `ε₀ > 0` for which the printed bound holds for all `0 < ε < ε₀` (`ml2r_printed_cost_fails`). The Gaussian example `ml2rInstPl` satisfies the paper's expansion (`a_n = (−1)^{n+1}`, `K = 1`) and these hypotheses (`ml2r_instance_hypotheses`); for `γ > 0`, `β < γ` its least cost of MSE `ε²` lies between two constant multiples of `ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}` (`ml2r_instance_cost`), so the exponent `√(2 log₂(1/ε)/α)` is sharp, and the printed bound fails for it (`ml2r_instance_printed_cost_false`). Sample sizes fixed in advance only; the lower bound does not address `β = γ` (G2.3-12). |
| G2.3-14 | l.564–567, p.12 | numerical support; "a very useful extension … when β ≤ γ" | N/A | – | |

---

## MISSING and PARTIAL items (details)

(Round 25: all resolved — see the resolution table of `notes/coverage/README.md` and the "Spot-check
21" notes in the rows: G2.1-35 and G2.1-36 (fixed `L`) by `tendstoInDistribution_levelEstimator` and
`tendstoInDistribution_mlmcEstimator` (round 10), G2.1-36 with a growing `L` and G2.1-34 in
`MLMCCentralLimit.lean` (round 12, the adaptive stopped algorithm aside), G2.2-16 by
`singleTerm_variance_le_of_sq_le`, G2.3-08 by `ml2r_bias_le` (round 10) and
`ml2r_bias_not_attainable` (round 22), G2.3-12 and G2.3-13 by `ml2r_theorem_eq`, `ml2r_theorem_lt`
(round 10).)

1. **G2.1-35** (l.350–351, p.8), MISSING. "the multilevel correction Y_ℓ on each level is
   asymptotically Normally-distributed". The pinned Mathlib (`0df444a`) contains
   `Mathlib/Probability/CentralLimitTheorem.lean` with
   `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`: for i.i.d. L² `X`,
   `(√n)⁻¹(∑_{k<n}X_k − nμ) → N(0, v)` in distribution. Applying it to
   `levelDiff Pl ℓ ∘ ω (ℓ, ·)` gives √N(Y_ℓ(N) − E[ΔP_ℓ]) ⇒ N(0, V_ℓ). **Easy**, about 30–60 lines.
2. **G2.1-36** (l.351, p.8), MISSING (fixed L) / out of scope (L → ∞). "…and therefore so is Y".
   With L fixed and N_ℓ = ⌈n_ℓN⌉, the normalised Y converges to N(0, 1). This needs the
   characteristic-function product over the independent levels plus Lévy continuity
   (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`, present). **Moderate**, about 150–250 lines.
   The reading that matches Collier et al., with L(ε) → ∞, needs a Lindeberg–Feller
   triangular-array CLT, which is **not in Mathlib**. Neither reading is documented as a gap.
   (G2.1-34, the Collier et al. confidence-interval theorem itself, is out of scope and also
   undocumented.)
3. **G2.2-16** (l.481–484, p.10), PARTIAL (gap documented in statement-audit as a heuristic).
   "If E_ℓ² ≪ V_ℓ … N ≈ ε⁻²∑V_ℓ/p_ℓ". Proved: V[Y] ≥ ∑V_ℓ/p_ℓ and V[Y_N] = V[Y]/N, so
   N ≥ ε⁻²∑V_ℓ/p_ℓ is necessary. Missing: `(∀ℓ, E_ℓ² ≤ δV_ℓ) → V[Y] ≤ (1+δ)∑V_ℓ/p_ℓ`, a
   corollary of `singleTerm_variance` that drops `−(∑E_ℓ)²`. **Trivial**, about 20 lines. It would
   also make G2.2-18 (C ≈ ε⁻²S²) a two-sided statement.
4. **G2.3-08** (l.529–531, 543, pp.11–12), PARTIAL (gap undocumented). ML2R bias
   "`= O(2^{−αL²})`" under the regular weak-error expansion. The correction to 2^{−αL(L+1)/2} is
   documented, but no O-bound is proved under any hypothesis whose constants are independent of L.
   Needed:
   - (a) the sharp weight bound `|w_ℓ| ≤ B²·r^{(L−ℓ)(L−ℓ+1)/2}` (r = 2^{−α}). The exact product
     `∏_{k=ℓ+1}^{L} r^{k−ℓ}` is what `prod_ml2r_factor_gt_le` (a helper lemma, not in the axiom
     audit) currently weakens to `r^{L−ℓ}`.
   - (b) If `|R_ℓ| ≤ K·2^{−αℓL}` (or `2^{−αℓ(L+1)}`) for ℓ ≤ L with K independent of L, then
     `|∑w_ℓR_ℓ| ≤ K·B²·C·2^{−αL(L+1)/2}`. The exponent `(L−ℓ)(L−ℓ+1)/2 + ℓL` is minimised at
     ℓ ∈ {0, 1}.

   **Elementary, moderate**, about 100–200 lines.
5. **G2.3-12 / G2.3-13** (l.561–564, p.12), PARTIAL (gap undocumented). ML2R costs
   O(ε⁻²|log ε|) (β = γ) and O(ε⁻²2^{(γ−β)√(·)}) (β < γ). What exists is the deterministic core
   only, with the bias bound c₁2^{−αL(L+1)/2} assumed for every L. Needed: (i) item 4, to derive
   that bound from the expansion hypothesis; (ii) a probability-space wrapper in the style of
   `giles_theorem1_of_core`. The wrapper would combine `ml2r_estimator_mean_variance`,
   `mse_eq_variance_add_sq_bias`, V[ΔP_ℓ] ≤ c₂2^{−βℓ} and E[κ_ℓ] ≤ c₃2^{γℓ} (as bounds, not
   equalities) with `ml2r_complexity_eq/lt`, and conclude that the ML2R estimator has
   MSE < ε² and E[cost] ≤ c₄·(…). **Easy glue once item 4 exists**, about 100–150 lines.

## Misstatements and documentation issues found

(Round 25: resolved. After spot-check 24 the README row for `Richardson.lean` and
`ML2RComplexity.lean` describes `ml2r_bias` as the exact bias of one expansion and
`ml2r_complexity_eq`/`_lt` as deterministic cores that take the bias bound as given, and cites
`ml2r_bias_le`, `ml2r_theorem_eq` and `ml2r_theorem_lt` for the estimator itself; the
`ML2RComplexity.lean` docstrings cite `ml2r_bias_le`. PLAN no longer claims §1–§3 "in full" and
lists what is not formalised; both quotations below are corrected in the docstrings.)

No Lean main theorem in this range is false or misaligned with the paper in a way that changes its
meaning. Theorem 1 matches hypothesis by hypothesis, with c₄ before ε, and the three regimes are
correct. The following are weaker issues:

* **ML2R bias and complexity are presented as more than is proved.** The README row for
  Richardson/ML2RComplexity says "the bias O(2^{−αL(L+1)/2}) (`ml2r_bias_eq`, `ml2r_bias`) … costs
  O(ε⁻²|log ε|) … O(ε⁻²2^{…})". The docstrings of `ml2r_complexity_eq/lt` speak of "the remaining
  error bound c₁2^{−αL(L+1)/2} of `ml2r_bias`". But `ml2r_bias`'s hypothesis, an exact
  (L+1)-term expansion on the L+1 levels, is satisfiable by any data (Vandermonde). Its a_{L+1}
  therefore depends on L, and nothing gives a c₁ uniform in L. The complexity theorems are
  deterministic MSE-*bound* statements. They are true, but the chain "paper hypothesis ⇒ bias bound
  ⇒ cost" is not closed.
* **PLAN.md l.38–40** claims "Giles §1–§3 in full". That overstates coverage, given G2.1-35/36
  (CLT remark) and G2.3-08/12/13, none of which appear in PLAN's "Not formalised" list.
* **Paper errors correctly handled and documented** (not Lean misstatements):
  - ML2R weight condition "= 1" → "= 0" (`ml2r_weights`);
  - ML2R bias 2^{−αL²} → 2^{−αL(L+1)/2}, and the complexity exponent √(|log₂ε|/α) → √(2log₂(1/ε)/α);
  - "ε⁻²L²V₀C₀" → (L+1)² (`optimal_cost_const_product`);
  - "α ≥ ½β" read as "(i) holds with α = β/2" (`weak_rate_of_second_moment`);
  - randomised finiteness needs the second-moment (iii) (`randomised_mlmc_finite`; PLAN M2 overstatement recorded).
* **Minor quotation inaccuracies in docstrings** (not mathematical):
  - `singleTermN_eq_sum_levels` quotes "Another way of describing it is …", but the paper
    (l.418) says "Alternatively, their estimator can be expressed as".
  - `lagrangeN_geometric` quotes "and so the total cost on level ℓ", but the paper says "and
    therefore the cost on level ℓ".
* **Content-light but faithful statements**, flagged also by the read-backs: `mlmc_vs_mc_increasing`
  and `mlmc_vs_mc_decreasing` (V_P and C_L cancel), and `equal_split_cost_le` (θ cancels). These
  match the paper's weak claims.
