# Coverage audit C2 — Giles (2015) §2.4–§2.7 and §3 (giles2015.txt lines 568–1232, pp. 12–27)

Auditor: independent coverage audit (read-only). Sources: `docs/giles2015.txt`, cross-checked against the
typeset PDF (`pdftotext -layout`, pp. 13–27) for Theorem 2, (2.5), (3.1)–(3.3) and the MATLAB code.
Lean: every statement cited below was read in `MlmcLean/*.lean` (statement and hypotheses, not only
the docstring). Main theorems cross-checked against `scripts/AxiomCheck.lean`. Gap documentation
checked in `README.md` (table + "Modelling choices"), `PLAN.md` ("Not formalised", "Out of scope"),
`notes/statement-audit.md`, `notes/research-notes.md`, `notes/readbacks/*`, module docstrings.

Notation in cells: `∣x∣` = absolute value, `‖x‖` = norm (pipes avoided because of the table syntax).

## Summary

| Status | Count |
|---|---|
| DONE | 60 |
| DONE-DEV | 14 |
| PARTIAL | 4 |
| MISSING | 1 |
| OUT-OF-SCOPE | 4 (2 documented, 2 undocumented) |
| N/A | 49 |
| **Total claims** | **132** |

PARTIAL: G2.4-32, G2.6-09, G2.6-10, G3.3-05. MISSING: G3.5-05.
OUT-OF-SCOPE: G2.5-12 (undocumented), G2.7-04 (documented), G3.5-03 (documented), G3.5-06 (undocumented).
Lean statements that misstate the paper: none found (see end of file for paper errata that the Lean
code correctly does not reproduce).

## Table

### §2.4 Multi-Index Monte Carlo (pp. 12–16)

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G2.4-01 | 569–570 / p.12 | "MIMC is probably the most significant extension of the MLMC methodology" | N/A | — | opinion |
| G2.4-02 | 571–575 / p.12 | in MLMC changing ℓ can change several aspects (timestep and grid; timestep and sub-samples) | N/A | — | prose |
| G2.4-03 | 575–577 / p.12 | in MIMC the level "index" ℓ is a vector of integer indices | N/A (def) | multi-indices `Fin D → ℕ` (`dot`, `box`, Lattice.lean) | implemented |
| G2.4-04 | 578–580 / p.12 | 1-D backward difference ΔP_ℓ ≡ P_ℓ − P_{ℓ−1}, P_{−1} ≡ 0 | N/A (def) | `levelDiff`, `crossDiff_one` | implemented |
| G2.4-05 | 580–592 / p.12–13 | telescoping sum at the heart of MLMC: E[P] = Σ_{ℓ≥0} E[ΔP_ℓ] | DONE | `sum_integral_levelDiff` (finite form); D = 1 instance of `tendsto_sum_box_integral_crossDiff` / `hasSum_integral_crossDiff` (series, under E[P_ℓ] → E[P]) | no dedicated 1-D series lemma; the D = 1 instance (with `crossDiff_one`) is the statement |
| G2.4-06 | 593–596 / p.13 | Δ_d P_ℓ ≡ P_ℓ − P_{ℓ−e_d} | N/A (def) | built into `crossDiff` | — |
| G2.4-07 | 596–600 / p.13 | cross-difference ΔP_ℓ ≡ (∏_{d=1}^{D} Δ_d) P_ℓ | N/A (def) | `crossDiff` (Δ_1 applied to the (D−1)-dim cross-difference; P ≡ 0 at negative indices), `crossDiff_one`, `crossDiff_two` | faithful recursive definition; no general inclusion–exclusion lemma (not needed) |
| G2.4-08 | 601–603 / p.13 | MIMC telescoping sum E[P] = Σ_{ℓ≥0} E[ΔP_ℓ] | DONE | `sum_crossDiff` (boxes), `tendsto_sum_box_integral_crossDiff` (box sums → E[P] from i)), `hasSum_integral_crossDiff` (absolutely/unconditionally convergent under i)–iii)), `integrable_integral_crossDiff` | paper gives no conditions; Lean supplies them |
| G2.4-09 | 586–589, 604–605 / p.13, Fig. 2.1 | "four evaluations for cross-difference ΔP_(5,4)" | DONE | `crossDiff_two`, `example` in MultiIndex.lean | points (5,4),(4,4),(5,3),(4,3) |
| G2.4-10 | 606–608 / p.13 | HNT's MIMC theorem "expressed in the following form to match … the MLMC Theorem" | N/A | — | framing |
| G2.4-11 | 609–611 / p.13 | Thm 2 hyp.: "independent estimators Y_ℓ based on N_ℓ Monte Carlo samples, each with expected cost C_ℓ and variance V_ℓ" | DONE-DEV | `giles_theorem2`, `giles_theorem2_boundary`, `giles_theorem2_full` (hyps `hY`, `hind`, `h_var`, `hCost_int`, `hCost_mean`) | modelled as a family Y ℓ n with V[Y ℓ n] = V_ℓ/n, random cost with E = n C_ℓ, pairwise independence, conditions for n ≥ 1 — README "Modelling choices", statement-audit |
| G2.4-12 | 611–613 / p.13 | positive vectors α, β, γ with α_d ≥ ½β_d; positive c₁, c₂, c₃ | DONE | `hα hβ hγ hαβ hc₁ hc₂ hc₃` | `giles_theorem2` uses α_d > ½β_d, `_boundary`/`_full` use ≥; β_d > 0 unused by the proof |
| G2.4-13 | 614 / p.13 | i) ∣E[P_ℓ − P]∣ → 0 as min_d ℓ_d → ∞ | DONE | `h_i` | ε–δ form of that limit |
| G2.4-14 | 619 / p.14 | iii) E[Y_ℓ] = E[ΔP_ℓ] | DONE | `h_iii` | for n ≥ 1 (documented) |
| G2.4-15 | 620 / p.14 | ii) ∣E[Y_ℓ]∣ ≤ c₁ 2^{−α·ℓ} | DONE | `h_ii` | label order i), iii), ii) of the statement kept; clash with the Notes' labels documented (statement-audit) |
| G2.4-16 | 621 / p.14 | iv) V_ℓ ≤ c₂ 2^{−β·ℓ} | DONE | `h_iv` | — |
| G2.4-17 | 622 / p.14 | v) C_ℓ ≤ c₃ 2^{γ·ℓ} | DONE | `h_v` | — |
| G2.4-18 | 623–630 / p.14 | ∃ c₄ > 0 ∀ ε < e⁻¹ ∃ set of levels 𝓛 and integers N_ℓ: Y = Σ_{ℓ∈𝓛} Y_ℓ has MSE < ε² | DONE | `giles_theorem2`, `giles_theorem2_boundary`, `giles_theorem2_full` | same quantifier order; 𝓛 a Finset, N_ℓ ≥ 1 |
| G2.4-19 | 632–634 / p.14 | E[C] ≤ c₄ ε⁻² for η < 0 | DONE | `mimcBound` (η < 0 branch) in the three theorems | also in the boundary case α_d = ½β_d, as the paper states (no log exponent) |
| G2.4-20 | 635 / p.14 | E[C] ≤ c₄ ε⁻² ∣log ε∣^{e₁} for η = 0 | DONE | same | — |
| G2.4-21 | 636 / p.14 | E[C] ≤ c₄ ε^{−2−η} ∣log ε∣^{e₂} for η > 0 | DONE | same | — |
| G2.4-22 | 637–640 / p.14 | η = max_d (γ_d − β_d)/α_d | DONE | `mimcEta` | `[NeZero D]` (η needs D ≥ 1) |
| G2.4-23 | 641–646 / p.14 | if α_d > ½β_d ∀d: e₁ = 2D₂, e₂ = (D₂−1)(2+η), D₂ = #{d : (γ_d−β_d)/α_d = η} | DONE | `giles_theorem2`, `mimcD2`, third clause of `giles_theorem2_full`, `mimcD3_eq_zero`, `mimc_complexity` | — |
| G2.4-24 | 647–649 / p.14 | "The form of the exponents is more complicated when α_d = ½β_d for some d" | DONE (stronger) | `giles_theorem2_full` (∃ e₁, e₂ depending only on α, β, γ), `giles_theorem2_boundary`, `mimc_complexity_boundary` | explicit e₁ = 2D₂ + (D₃−3)⁺, e₂ = (D₂−1)(2+η) + (D₃−1)⁺ are this formalisation's, not claimed sharp (README) |
| G2.4-25 | 651 / p.14 | Note: "Condition i) ensures weak convergence to the correct value" | DONE | `tendsto_sum_box_integral_crossDiff` | from i) alone |
| G2.4-26 | 652–654 / p.14 | Note: unbiasedness allows estimators "more complicated than the natural choice Y_ℓ = ΔP_ℓ" | N/A | (generic `integral_blockMean`, `variance_blockMean`, `indepFun_blockMean` hold for any index type) | prose; no MIMC analogue of `giles_theorem1_standard` is stated (not a paper claim) |
| G2.4-27 | 655–657 / p.14 | Note: iii), iv) give weak-error and variance orders, v) the cost rate | N/A | — | prose (labels swapped relative to the statement) |
| G2.4-28 | 658–659 / p.14 | Note: "proof … significantly harder than for the MLMC theorem" | N/A | (proof: `slab_bound`, `tail_bound`, `inner_bound`, `mimc_complexity_core`) | — |
| G2.4-29 | 676–678 / p.15 | difficulty of determining α, β, γ; example in §9 | N/A | (§9: `nested_mimc_complexity`, outside range) | — |
| G2.4-30 | 679–683 / p.15, Fig. 2.2 left | rectangular 𝓛 gives Σ_{ℓ∈𝓛} Y_ℓ = P_L, L the outermost point | DONE | `sum_rectSet_crossDiff`, `sum_crossDiff`, `rectSet` | for Y_ℓ = ΔP_ℓ pointwise; in expectation for general Y_ℓ |
| G2.4-31 | 683–688 / p.15 | rectangle "gives the optimal order of complexity only when η < 0, and under the additional condition Σ_d γ_d/α_d ≤ 2" | DONE-DEV | `giles_mimc_rectangular`, `mimc_rect_core` (sufficiency), `mimc_rect_lower_bounds`, `mimc_rect_necessary` (necessity), `sum_sdiff_rectSet_le` | "optimal order" read as O(ε⁻²) (the literal "order of Theorem 2" reading fails already for D = 1, η ≥ 0, where the rectangle is plain MLMC); necessity proved under attained-rate lower bounds, which the paper does not state — documented in RectangularMIMC.lean header |
| G2.4-32 | 689–692 / p.15 | "The optimal choice for 𝓛, which yields the complexity bounds given in the theorem, is of the form ℓ·n ≤ L" with n strictly positive | PARTIAL | `indexSet`, `mem_indexSet`, `mimc_construction` (proof step), README "MIMC summation region" | the proof uses 𝓛 = {θ·ℓ ≤ L}, θ_d = α_d + (γ_d−β_d)/2, but every complexity theorem only states ∃ 𝓛 : Finset, so "this region yields the bounds" is not a theorem statement; optimality (no other index set does better) is neither formalised nor listed as a gap Spot-check 21: (a) is round 10's `giles_theorem2_indexSet`, `giles_theorem2_boundary_indexSet`; the optimality among all index sets (b) is not formalised (listed in `PLAN.md`). |
| G2.4-33 | 691–692 / p.15, Fig. 2.2 right | in 2D this is a triangular region | N/A | — | geometric remark |
| G2.4-34 | 692–695 / p.15 | analogy with sparse grids | N/A | — | — |
| G2.4-35 | 696–707 / p.15–16 | standard MLMC for (S)PDEs: β independent of D, γ grows ≥ linearly in D, so for large D β ≤ γ and the complexity is not the optimal O(ε⁻²) | N/A | (formal kernel: D = 1 case of `mimc_rect_necessary`: O(ε⁻²) under attained rates forces γ < β) | application heuristic; paper typo: "less (often much less) than the optimal" should be "worse" Round 16: `mlmc_optimal_complexity_necessary` (D = 1). |
| G2.4-36 | 707–708 / p.16 | with MIMC "we can have β_d > γ_d in each direction, and therefore obtain the optimal complexity" | DONE | `giles_theorem2` (η < 0 branch); `giles_mimc_rectangular` | ∀d β_d > γ_d ⇒ η < 0 is immediate (no separate lemma) |
| G2.4-37 | 709–712 / p.16 | MIMC offers dimension-independent complexity | N/A | — | informal |

### §2.5 Multi-dimensional output functionals (pp. 16–18)

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G2.5-01 | 714–717 / p.16 | ω → U → P | N/A | — | — |
| G2.5-02 | 718–722, 747–754 / p.16–17 | P may be several scalars or infinite-dimensional; Table 2.1 | N/A | — | descriptive |
| G2.5-03 | 722–735 / p.16 | Heinrich, Giles 2008, PDE, CDF-of-exit-time examples | N/A | — | historical |
| G2.5-04 | 736–737 / p.16 | "The standard MLMC theorem will apply to each one of the outputs" | DONE | `giles_theorem1` (instantiate with each output) | trivial instantiation |
| G2.5-05 | 738–744 / p.16 | V_ℓ ≡ max_m V_{ℓ,m}/ε_m² | N/A (def) | `M.sup' … (V ℓ m / ε m ^ 2)` in `multiOutput_*` | — |
| G2.5-06 | 755–761 / p.17 | "Enforcing … Σ N_ℓ⁻¹ V_ℓ ≤ ½ is then sufficient to ensure that all of the individual variance constraints are satisfied" | DONE | `multiOutput_variance` | individual constraint Σ N_ℓ⁻¹ V_{ℓ,m} ≤ ½ ε_m²; real N_ℓ |
| G2.5-07 | 761–763 / p.17 | "the standard Lagrange multiplier approach … can be used to determine the optimal number of samples" | DONE | `multiOutput_optimal` | least cost 2(Σ√(V_ℓC_ℓ))² over real allocations for the aggregated constraint; not optimal for the per-output problem (not claimed) |
| G2.5-08 | 764–768 / p.17 | infinite-dim outputs: with a norm and the substitutions ∣E[P_ℓ]−E[P]∣ → ‖·‖, V[·] → E‖· − E·‖², "the theory carries over" | DONE | `giles_theorem1_hilbert`, `mlmc_mse_hilbert`, `integral_norm_sub_sq_eq` | real Hilbert space (the 2-norm case); other norms see G2.5-11/12 |
| G2.5-09 | 769–771 / p.17 | independent zero-mean scalars: E[(a+b)²] = E[a²] + E[b²] | DONE (stronger) | `integral_add_sq_of_indepFun` | E[a] = 0 alone suffices |
| G2.5-10 | 772–775 / p.17 | 2-norm: E‖a+b‖² = E‖a‖² + E‖b‖² for independent zero-mean vectors / functions with an inner-product norm | DONE | `integral_norm_add_sq_of_indepFun`, `integral_norm_sum_sq_of_indepFun` | complete real inner-product space; finite sums, pairwise independence |
| G2.5-11 | 776–781 / p.17 | not for other norms: the combined variance "can not necessarily be expressed … as Σ N_ℓ⁻¹ V_ℓ" | DONE | `sq_norm_add_of_indepFun_fails_sup` | sup norm on ℝ²: 1 vs 2 |
| G2.5-12 | 782–787 / p.17–18 | "the theory can be extended to the use of other norms by using results from Banach space theory for the sums of independent random variables" | OUT-OF-SCOPE | — | needs type/cotype (Rademacher/Kahane) inequalities, absent from Mathlib; NOT documented as a gap (README, PLAN, notes silent) Spot-check 21: documented since round 10 in the out-of-scope table of `notes/coverage/README.md`. Round 25 (`BanachTheorem1.lean`): Theorem 1 in a Banach space with the type-2 inequality `E‖∑ X_i‖² ≤ τ² ∑ E‖X_i‖²` as a hypothesis on the space (`HasType2`): the MSE bound with the factors `2τ²` and `2` (`mlmc_mse_le_of_hasType2`) and Theorem 1 with mutually independent samples (`giles_theorem1_banach`); type 2 is proved for Hilbert spaces (`τ = 1`), for spaces isomorphic to a subspace of a Hilbert space and for finite-dimensional spaces, e.g. `ℝ × ℝ` with the maximum norm with `τ = √2` (`hasType2_of_innerProductSpace`, `hasType2_of_isomorphic_embedding`, `exists_hasType2_of_finiteDimensional`, `exists_hasType2_prod`, `hasType2_prod_sqrt_two`; the optimality of `√2` is not formalised). Type 2 for other infinite-dimensional spaces (e.g. `L^p`, `2 < p < ∞`) is not formalised (resolution table of `notes/coverage/README.md`). Round 27 (`SpotCheck26Extras.lean`): the optimality of `√2` is proved: the independent random signs `ε₁(1, 1)`, `ε₂(1, −1)` force `τ² ≥ 2` (`two_le_sq_of_hasType2_prod`, `not_hasType2_prod_of_lt_sqrt_two`), so type 2 for `ℝ × ℝ` with the maximum norm holds with constant `τ` iff `√2 ≤ \|τ\|` (`hasType2_prod_iff`), and `√2` is the least nonnegative constant (`isLeast_hasType2_prod`). |
| G2.5-13 | 787–790 / p.18 | Daun–Heinrich parametric integration in Banach spaces | N/A | — | literature |

### §2.6 Non-geometric MLMC (pp. 18–20)

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G2.6-01 | 792–795 / p.18 | "MLMC does not require the use of a geometric sequence of grids" | N/A | (Allocation.lean, Estimator.lean hold for arbitrary V_ℓ, C_ℓ) | prose |
| G2.6-02 | 795–798 / p.18 | the only assumptions of the §1.2/§1.3 analysis: accuracy and cost increase, correction variance decreases | N/A | (`optimal_cost_isLeast` needs only V_ℓ, C_ℓ > 0) | meta-claim |
| G2.6-03 | 804–808 / p.18 | V_ℓ = V[P_ℓ], V_{ℓ1,ℓ2} ≡ V[P_{ℓ2} − P_{ℓ1}], costs; subset "with fixed ℓ_M = L to achieve a user-specified accuracy" | DONE | `subsetCorr`, `sum_subsetCorr` | subset corrections telescope to P_{ℓ_M}: same bias as full MLMC to L |
| G2.6-04 | 808–814 / p.18 | C(ℓ₁,…,ℓ_M) = ε⁻²(√(V_{ℓ0}C_{ℓ0}) + Σ_m √(V_{ℓm,ℓm−1} C_{ℓm,ℓm−1}))², following (1.1) | DONE | `subsetCost`, `subsetCost_eq`, `subset_optimal_cost` | least cost over real N with variance ≤ ε²; paper's index slips (ℓ₀ vs ℓ₁, order of the pair) handled in docstring |
| G2.6-05 | 815–817 / p.18 | exhaustive search finds the optimal subset if the number of levels is small | DONE | `card_levelSubsets` (2^L candidates), `exists_optimal_subset` | — |
| G2.6-06 | 822–832 / p.18 | contribution of the samples involving level ℓ if kept | N/A (def) | — | — |
| G2.6-07 | 833–836 / p.18 | "for optimality N_ℓ ∝ √(V_ℓ/C_ℓ)" | DONE | `lagrangeN`, `optimal_cost_isLeast`, `lagrangeN_unique`, `optimal_variance_isLeast` | §1.3 result |
| G2.6-08 | 839–841 / p.19 | N_ℓ = N_{ℓ+1} √(V_ℓ C_{ℓ+1} / (V_{ℓ+1} C_ℓ)) | DONE | `twoLevel_optimal_ratio` | least variance at fixed cost iff this ratio |
| G2.6-09 | 844–847 / p.19 | combined variance N_ℓ⁻¹V_ℓ + N_{ℓ+1}⁻¹V_{ℓ+1} = (V_{ℓ+1}/N_{ℓ+1})(1 + √(V_ℓC_ℓ/(V_{ℓ+1}C_{ℓ+1}))) | PARTIAL | (product only: `levelKeep_product`) | identity at the optimal ratio not stated; trivial algebra Spot-check 21: resolved in round 10, `levelKeep_combined`. |
| G2.6-10 | 848–851 / p.19 | combined cost N_ℓC_ℓ + N_{ℓ+1}C_{ℓ+1} = N_{ℓ+1}C_{ℓ+1}(1 + √(…)) | PARTIAL | (product only) | same Spot-check 21: resolved in round 10, `levelKeep_combined`. |
| G2.6-11 | 852–856 / p.19 | product of combined variance and cost = V_{ℓ+1}C_{ℓ+1}(1 + √(V_ℓC_ℓ/(V_{ℓ+1}C_{ℓ+1})))² | DONE (stronger) | `levelKeep_product` | IsLeast over all real N_ℓ, N_{ℓ+1} > 0 |
| G2.6-12 | 865–875 / p.19 | dropping ℓ: estimator Ñ⁻¹Σ(P_{ℓ+1} − P_{ℓ−1}), variance Ṽ/Ñ, cost ÑC̃, product ṼC̃ | DONE | `variance_sample_mean`, `variance_blockMean`; product used in `levelDrop_test` | product identity trivial |
| G2.6-13 | 876–884 / p.19 | test (2.5); if true, dropping ℓ gives lower variance at fixed cost / lower cost at fixed variance | DONE | `levelDrop_test` | iff, for the optimal hierarchy cost τ⁻¹(Σ√(VC))², which is also the fixed-cost optimum (`optimal_variance_isLeast`) |
| G2.6-14 | 885–894 / p.19–20 | assume C̃_{ℓ+1} ≈ C_{ℓ+1}; cost ratio known a priori, variance ratio asymptotically/empirically | N/A | (C̃ = C_{ℓ+1} imposed in the ρ-lemmas) | modelling assumption |
| G2.6-15 | 896–900 / p.20 | Ṽ_{ℓ+1} = V_{ℓ+1} + 2ρ√(V_ℓV_{ℓ+1}) + V_ℓ | DONE | `levelDrop_variance` | — |
| G2.6-16 | 902–908 / p.20 | ρ = 1: Ṽ_{ℓ+1} = V_{ℓ+1}(1 + √(V_ℓ/V_{ℓ+1}))² | DONE | `levelDrop_perfect_correlation` (1st conjunct) | — |
| G2.6-17 | 909–910 / p.20 | "Since C_ℓ < C_{ℓ+1} … the test (2.5) is never satisfied" (retain ℓ) | DONE | `levelDrop_perfect_correlation` (2nd conjunct) | needs only C_ℓ ≤ C_{ℓ+1}, with C̃ = C_{ℓ+1} |
| G2.6-18 | 910–914 / p.20 | near-perfect correlation in PDE applications with finite-dim uncertainty | N/A | — | — |
| G2.6-19 | 915–922 / p.20 | ρ = 0: Ṽ = V_{ℓ+1} + V_ℓ; drop ℓ iff 1 + V_ℓ/V_{ℓ+1} < (1 + √(V_ℓC_ℓ/(V_{ℓ+1}C_{ℓ+1})))² | DONE | `levelDrop_uncorrelated` | hypothesis ρ = 0 (weaker than the paper's "independent") |

### §2.7 MLQMC (p. 20)

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G2.7-01 | 924–927 / p.20 | Giles–Waterhouse MLQMC with extensible rank-1 lattices | N/A | — | historical |
| G2.7-02 | 927–928 / p.20 | "QMC is known to be most effective for low-dimensional applications" | N/A | — | folklore/empirical |
| G2.7-03 | 928–931 / p.20 | encouraging SDE results; "no supporting theory" | N/A | — | empirical |
| G2.7-04 | 932–938 / p.20 | "under certain conditions they lead to multilevel methods with a complexity which is O(ε^{−p}) with p < 2" | OUT-OF-SCOPE | — | needs QMC error theory; the paper gives no conditions; documented (PLAN "Not formalised: … convergence orders … of QMC"; MLQMC.lean header) Round 20, in `d` dimensions (`LatticeRuleD.lean`): for a randomly shifted rank-1 lattice rule the variance is the dual-lattice sum `∑_{k ∈ L^⊥∖{0}} \|f̂(k)\|²` (`hasSum_variance_rank1Lattice`), with unbiased replicates (`rank1Lattice_replicates`) and the bound `\|Q(u) − ∫f\| ≤ ∑_{L^⊥∖{0}} \|f̂(k)\|` for every shift (`abs_rank1Lattice_sub_integral_le`); MLQMC with level-dependent dimension has cost `O(ε^{−p})` with `p < 2` when `g < 2a` and `g < a + b`, assuming dual-lattice sums `≤ (c₂ 2^{−bℓ}/N)²` for `N = 2^m` points (`mlqmcLattice_complexity`, `mlqmcLattice_complexity_of_lt`, `mlqmcLattice_complexity_lt_two`, `mlqmcLattice_complexity_rate`). That good generating vectors exist (the `O(N⁻¹)` itself) is not formalised. Spot-check 21: with round 12 (`QMC1D.lean`, one dimension) and round 20 the row is in effect PARTIAL; what is missing is the existence of good generating vectors. |

### §3.1 MLMC algorithm (p. 21)

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G3.1-01 | 946–954 / p.21 | Algorithm 1: start L = 2, N₀ samples on 0,1,2; loop: sample, estimate V_ℓ, optimal N_ℓ, test, add level | DONE-DEV | `alg1Init`, `alg1Samples`, `alg1Level`, `alg1Level_spec` | idealised: exact m_ℓ, V_ℓ; one pass reaches every target — documented (Algorithm.lean header, README) |
| G3.1-02 | 955–961 / p.21 | (3.1) N_ℓ = ⌈2ε⁻² √(V_ℓ/C_ℓ) Σ√(V_ℓC_ℓ)⌉ | DONE | `allocation_eq_3_1`, `optimalN` (τ = ε²/2) | — |
| G3.1-03 | 963–965 / p.21 | "This ensures that the estimated variance … is less than ½ε²" | DONE (corrected) | `allocation_eq_3_1`, `alg1_variance`, `optimalN_variance` | ≤, not <: equality when every ceiling argument is an integer (docstring) |
| G3.1-04 | 966–968 / p.21 | test ensures ∣E[P − P_L]∣ < ε/√2 "to achieve an MSE which is less than ε²" | DONE | `mse_lt_of_half`, `convergence_test_mse`, `robust_test_mse` | — |
| G3.1-05 | 969–971 / p.21 | if E[P_ℓ − P_{ℓ−1}] ∝ 2^{−αℓ}: E[P − P_L] = Σ_{ℓ>L} E[P_ℓ − P_{ℓ−1}] = E[P_L − P_{L−1}]/(2^α − 1) | DONE | `remaining_error` (HasSum + value), `abs_tail_le` (inequality form) | — |
| G3.1-06 | 972–973 / p.21 | convergence test ∣E[P_L − P_{L−1}]∣/(2^α − 1) < ε/√2 | DONE | `convergence_test_mse` | — |
| G3.1-07 | 973–976 / p.21 | robust: also extrapolate from E[P_{L−1}−P_{L−2}], E[P_{L−2}−P_{L−3}], take the max of three | DONE | `alg1Rem`, `abs_div_le_alg1Rem`, `anchor_le_alg1Rem`, `abs_tail_le_alg1Rem`, `abs_integral_sub_le_alg1Rem`, `robust_test_mse` | valid under at-least-geometric decay from one of the three anchors |
| G3.1-08 | 977–978 / p.21 | "this algorithm is heuristic; it is not guaranteed to achieve a MSE … less than ε²" | DONE | `alg1_not_guaranteed` | fails even with exact means |
| G3.1-09 | 978–982 / p.21 | Theorem 1 guarantees, but needs a priori c₁, c₂, which the algorithm in effect estimates | N/A | (beyond the paper: `alg1Level_le`, `alg1_complexity`) | prose |
| G3.1-10 | 983–985 / p.21 | accuracy of the variance estimate depends on the sample size | DONE | `sampleVariance_sd` | quantitative √((κ−1)/N) E[X²] |
| G3.1-11 | 985–989 / p.21–22 | "the implementation sets a minimum estimate by extrapolation from coarser levels" | DONE | `floorEst`, `le_floorEst`, `floorEst_ge_extrapolation`, `floorEst_le` | — |
| G3.1-12 | 947–954 (implicit) / p.21 | the loop terminates | DONE-DEV | `alg1_terminates`, `alg1Level_le` | exact means with m_ℓ → 0 (resp. ∣m_ℓ∣ ≤ c₁2^{−αℓ}, then L ≤ Theorem-1 level) |
| G3.1-13 | 966–968 (implicit) / p.21 | the output meets the variance and MSE targets | DONE-DEV | `alg1_variance`, `alg1_mse` | idealised; MSE ≤ ε² when the robust estimate bounds the remaining error; driver's non-strict test gives ≤ (documented) |

### §3.2 Overview of MATLAB implementation (p. 22)

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G3.2-01 | 993–998 / p.22 | mlmc.m uses a routine returning Σ_n (P_ℓ^{(n)} − P_{ℓ−1}^{(n)})^p, p = 1, 2, over independent samples | N/A | (see G3.4-05) | code interface |
| G3.2-02 | 999–1002 / p.22 | mlmctest.m runs tests then calls mlmc.m; code online | N/A | — | — |

### §3.3 MLMC test routine (pp. 22–23)

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G3.3-01 | 1004–1009 / p.22 | four plots (log₂V_ℓ, log₂∣E[P_ℓ−P_{ℓ−1}]∣, consistency, kurtosis) | N/A | — | — |
| G3.3-02 | 1010–1014 / p.22 | a, b, c estimate E[P^f_{ℓ−1}], E[P^f_ℓ], E[Y_ℓ] ⇒ "a − b + c ≈ 0" | DONE | `consistency_mean` | E[a − b + c] = 0 under (2.4) |
| G3.3-03 | 1014–1019 / p.22 | particularly important when P^f_ℓ ≠ P^c_ℓ | N/A | — | — |
| G3.3-04 | 1020–1024 / p.22 | √V[a−b+c] ≤ √V[a] + √V[b] + √V[c] | DONE | `consistency_sd`, `sqrt_variance_add_le`, `sqrt_variance_sub_le`, `covariance_sq_le` | no independence needed |
| G3.3-05 | 1025–1029 / p.22 | ratio ∣a−b+c∣ / (3(√V_a + √V_b + √V_c)) with V's "empirical estimates"; "The probability of this ratio being greater than unity is less than 0.3%" | PARTIAL | `gaussian_tail_three`, `consistency_check_gaussian`, `consistency_check_chebyshev` | proved with the TRUE variances and exact normality of a−b+c (normality documented); the paper's ratio with empirical V_a, V_b, V_c is not covered and this substitution is not documented; distribution-free bound only 1/9 Round 19: with one sample per level the check fails with probability `1` (atomless laws), with two it fails with probability `(2/π) arctan(√2/3) ≈ 0.280` (biased variance estimate) or `(2/π) arctan(1/3) ≈ 0.205` (unbiased) in the module's Gaussian example (`consistency_check_one_sample`, `consistency_check_two_samples`). Round 26: the paper's ratio with empirical means and variances was resolved in round 13 (`consistency_check_empirical`, `consistency_check_empirical_lt`: as the sample sizes grow, eventually `P(the check fails) < 0.003`; see the resolution table). |
| G3.3-06 | 1029–1031 / p.22 | ratio > 1 indicates a programming error or a violation of (2.4) | N/A | — | interpretation (contrapositive of `consistency_mean` + tail bound) |
| G3.3-07 | 1032–1038 / p.22–23 | "As few as 10 may be sufficient … many more … when there are rare outliers" | N/A | — | empirical Round 25 (spot-check 24): "`V_ℓ = V[Y_ℓ]`" here (and at l. 1113–1114) uses `Y_ℓ` for a single sample, while (2.2)–(2.3) have `V[Y_ℓ] = V_ℓ/N_ℓ`; §3.5, l. 1200, makes the switch explicit (notation; corrections table of `notes/statement-audit.md`). |
| G3.3-08 | 1038–1042 / p.23 | SD of the sample variance of zero-mean X ≈ √((κ−1)/N) E[X²], κ = E[X⁴]/(E[X²])² | DONE-DEV | `kurtosis`, `sampleVariance_sd`, `powerSum_variance_mean` | exact for the known-mean estimator N⁻¹ΣX_n²; for the driver's s₂/N − (s₁/N)² only its mean (1 − 1/N)V is proved; documented (ErrorAnalysis header) Round 19: the exact variance of the unbiased and biased sample variance and `sd = √((κ − 1)/N) σ²(1 + O(1/N))` (`sampleVar_mean_variance`, `sampleVar_sd`, `tendsto_sampleVar_sd_div`, `empVar_sd`). |
| G3.3-09 | 1042–1043 / p.23 | "Hence O(κ) samples are required" | DONE | `sampleVariance_relative_sd_le_iff` | relative SD ≤ r ⇔ N ≥ (κ−1)/r² |
| G3.3-10 | 1043–1045 / p.23 | mlmctest warns if κ_ℓ is very large | N/A | — | — |
| G3.3-11 | 1046–1052 / p.23 | P ∈ {0,1} ⇒ X = P_ℓ − P_{ℓ−1} ∈ {1, −1, 0} w.p. p, q, 1−p−q | N/A | (`measureReal_ternary_zero`) | setup; Lean assumes X ternary |
| G3.3-12 | 1053 / p.23 | p, q ≪ 1 ⇒ E[X] ≈ 0 | DONE | `integral_ternary` | E[X] = p − q exactly |
| G3.3-13 | 1053 / p.23 | κ ≈ (p+q)⁻¹ ≫ 1 | DONE | `kurtosis_of_ternary` | exact for the paper's (uncentred) κ |
| G3.3-14 | 1053–1055 / p.23 | "we may get all X^(n) = 0, which will give an estimated variance of zero" | DONE | `prob_all_zero`, `measureReal_ternary_zero`, `powerSum_variance_of_zero` | probability (1−p−q)^N |
| G3.3-15 | 1055–1056 / p.23 | "the kurtosis will become worse as ℓ → ∞ since p, q → 0 due to weak convergence" | DONE-DEV | `tendsto_kurtosis_atTop` | hypothesis E[X_ℓ²] = p + q → 0 (docstring); the paper's "due to weak convergence" is imprecise (weak convergence gives only p − q → 0) |
| G3.3-16 | 1057–1060 / p.23 | mlmctest then runs mlmc.m for several ε | N/A | — | — |

### §3.4 MLMC driver routine (pp. 23–26)

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G3.4-01 | 1064–1074 / p.23 | interface: meaning of α, β, γ; estimated if not positive | N/A | — | — |
| G3.4-02 | 1081–1091 / p.24 | mlmc_l returns ΣY, ΣY² for iid Y with mean E[P_0] / E[P_l − P_{l−1}] | N/A | — | interface (= condition ii) of Thm 1) |
| G3.4-03 | 1092–1101 / p.24 | initialisation: clamp α, β ≥ 0; L = 2; N₀ samples on levels 0,1,2 | N/A | (`alg1Init`) | code |
| G3.4-04 | 1102–1112 / p.24 | loop while Σ dNl > 0, accumulate sums | N/A | (`alg1Samples`) | code |
| G3.4-05 | 1113–1114, 1123–1125 / p.24–25 | m_ℓ = ∣s₁/N∣, V_ℓ = max(0, s₂/N − m_ℓ²) | DONE | `powerSum_variance_eq`, `powerSum_variance_nonneg`, `powerSum_variance_mean` | max(0,·) redundant in exact arithmetic; the estimate has bias −V/N Round 25 (spot-check 24): `V_ℓ ≡ V[Y_ℓ]` (l. 1113–1114) is the variance of one sample here, not of the level estimator of (2.3) (notation; see G3.3-07). |
| G3.4-06 | 1114–1115 / p.24 | "one would expect m_ℓ = 2^{−α} m_{ℓ−1}, V_ℓ = 2^{−β} V_{ℓ−1}" | N/A | — | heuristic (exact under exact geometric decay) |
| G3.4-07 | 1115–1129 / p.24–25 | estimates "not allowed to decrease by more than factor ½ relative to this anticipated value" (ℓ ≥ 2) | DONE | `floorEst`, `le_floorEst`, `floorEst_ge_extrapolation`, `floorEst_le` | — |
| G3.4-08 | 1130–1140 / p.25 | α, β "estimated by linear regression" of log₂ m_ℓ, log₂ V_ℓ on ℓ = 1..L; clamp at ½ | DONE | `lsSlope`, `lsIntercept`, `lsFit_le`, `lsSlope_affine`, `lsSlope_log_geometric` | clamp max(0.5,·) not modelled (no content) |
| G3.4-09 | 1141–1147 / p.25 | C_ℓ = 2^{γℓ}; Ns by (3.1); dNl = max(0, Ns − Nl) | DONE | `allocation_eq_3_1`, `alg1Samples` | counts become max(N_ℓ, Ns_ℓ) |
| G3.4-10 | 1158 / p.26 | test only when "(almost) converged": no level needs > 1% more samples | N/A | — | heuristic; in the exact-value model targets are met before the test (documented) |
| G3.4-11 | 1159–1161 / p.26 | rem = max(ml(L+1+range)·2^{α·range})/(2^α − 1), range = −2:0; add a level if rem > ε/√2 | DONE | `alg1Rem`, `alg1Level`, `alg1_mse` | stops at the least L ≥ 2 with rem ≤ ε/√2 |
| G3.4-12 | 1148–1150, 1162–1168 / p.25–26 | new level: "its variance is estimated by extrapolation" (V_{L+1} = V_L/2^β), N_{L+1} = 0, Ns recomputed | DONE-DEV | `alg1Samples` | exact V_{L+1} replaces the extrapolation (documented exact-value idealisation); the formula itself is not stated |
| G3.4-13 | 1172–1175 / p.26 | final estimator P = Σ_ℓ suml(1,ℓ)/N_ℓ | DONE | `mlmcEstimator`, `mlmcEstimator_mean_variance` | the estimator (2.2) |
| G3.4-14 | 1152–1153 / p.25 fn. 2 | HNT use a Bayesian approach for the variance | N/A | — | — |

### §3.5 MLQMC algorithm (pp. 26–27)

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G3.5-01 | 1177–1179 / p.26 | MLQMC after Giles–Waterhouse, aligned with §3.1 | N/A | — | — |
| G3.5-02 | 1180–1185 / p.26 | N_ℓ = size of a QMC point set (rank-1 lattices, Sobol sequences) | N/A (def) | — | — |
| G3.5-03 | 1185–1189 / p.26 | best case: QMC error O(N_ℓ⁻¹) instead of the MC O(N_ℓ^{−1/2}) | OUT-OF-SCOPE | (MC half: `variance_sample_mean`) | QMC error theory absent; documented (PLAN "Not formalised … of QMC"; MLQMC.lean header) Round 20, in `d` dimensions (`LatticeRuleD.lean`): for a randomly shifted rank-1 lattice rule the variance is the dual-lattice sum `∑_{k ∈ L^⊥∖{0}} \|f̂(k)\|²` (`hasSum_variance_rank1Lattice`), with unbiased replicates (`rank1Lattice_replicates`) and the bound `\|Q(u) − ∫f\| ≤ ∑_{L^⊥∖{0}} \|f̂(k)\|` for every shift (`abs_rank1Lattice_sub_integral_le`); MLQMC with level-dependent dimension has cost `O(ε^{−p})` with `p < 2` when `g < 2a` and `g < a + b`, assuming dual-lattice sums `≤ (c₂ 2^{−bℓ}/N)²` for `N = 2^m` points (`mlqmcLattice_complexity`, `mlqmcLattice_complexity_of_lt`, `mlqmcLattice_complexity_lt_two`, `mlqmcLattice_complexity_rate`). That good generating vectors exist (the `O(N⁻¹)` itself) is not formalised. Spot-check 21: with round 12 (`QMC1D.lean`, one dimension) and round 20 the row is in effect PARTIAL; what is missing is the existence of good generating vectors. |
| G3.5-04 | 1190–1191 / p.26 | "one set of N_ℓ points gives good accuracy, but no confidence interval" | N/A | — | descriptive |
| G3.5-05 | 1191–1193 (+1197–1198, implicit) / p.26–27 | randomised QMC via a random shift (rank-1 lattices) gives independent replicates, "32 random independent values", i.e. unbiased estimates of E[Y_ℓ] | MISSING | — (only assumed: `hmean` of `mlqmc_mse`) | Mathlib-level: a uniform shift mod 1 preserves Lebesgue/Haar measure on the unit torus, so each shifted-rule average is unbiased and independent shifts give iid replicates; not formalised, not documented Spot-check 21: resolved in round 10, `shiftedQMC_unbiased`, `randomShift_replicates` (`RandomShiftQMC.lean`). |
| G3.5-06 | 1192–1193 / p.26 | digital scrambling (Sobol) serves the same purpose | OUT-OF-SCOPE | — | Owen-scrambling theory absent from Mathlib; not documented Spot-check 21: documented since round 10 in the out-of-scope table of `notes/coverage/README.md`. Round 25 (`DigitalShiftQMC.lean`): the random digital shift in base 2 preserves the fair product measure on digit sequences (`digitalShift_measurePreserving`), so the shifted QMC average is unbiased (`digitalShiftQMC_unbiased`) and independent shifts give i.i.d. replicates with an unbiased variance estimate (`digitalShift_replicates`), and fair binary digits are uniform on `[0, 1]` and `[0, 1]^δ` (`uniformDigits_map_binaryValue`, `uniformDigits_map_binaryPoint`, `digitalShiftQMC_unbiased_cube`). Owen's scrambling, the construction of Sobol points and QMC error rates are not formalised (resolution table of `notes/coverage/README.md`). |
| G3.5-07 | 1193–1199 / p.26–27 | from the 32 set averages "the variance of their average, V_ℓ, can be estimated in the usual way" | DONE | `variance_sample_mean`, `variance_blockMean`, `powerSum_variance_mean` | generic iid results; MLQMC.lean itself takes V_ℓ exact |
| G3.5-08 | 1200–1204 / p.27 | (3.2) Σ_{ℓ≤L} V_ℓ ≤ ½ε², V_ℓ the variance of the level average | DONE-DEV | `mlqmc_algorithm`, `mlqmcState_variance`, `mlqmc_mse` | (3.2) proved at exit; V[Y] ≤ ΣV_ℓ is a hypothesis of `mlqmc_mse` (follows from `mlmc_variance` for independent levels) |
| G3.5-09 | 1205–1206 / p.27 | "Many QMC methods work naturally with N_ℓ as a power of 2" | N/A | (N_ℓ = 2^k in `mlqmcRatio`) | — |
| G3.5-10 | 1206–1212 / p.27 | (3.3): doubling "eliminate[s] a large fraction of the variance", so double on ℓ* = argmax V_ℓ/(N_ℓC_ℓ) | DONE-DEV | `mlqmc_doubling_level`, `mlqmcLevel` | only under the explicit model "the same fraction f of V_ℓ removed on every level, extra cost N_ℓC_ℓ" (near-tautological); documented in docstring |
| G3.5-11 | 1213–1229 / p.27 | Algorithm 2 steps (start L = 2, N_ℓ = 1; double N_{ℓ*} while (3.2) fails; else test, add level with N_L = 1) | DONE-DEV | `mlqmcRatio`, `mlqmcLevel`, `mlqmcStep`, `mlqmcIter`, `mlqmcInner`, `mlqmcState` | exact v ℓ k after k doublings; the 32-set estimation idealised (documented) |
| G3.5-12 | 1221–1222 (implicit) / p.27 | the doubling loop reaches (3.2) | DONE-DEV | `mlqmc_inner_terminates`, `mlqmcInner_variance` | needs v ℓ k > 0, v ℓ k → 0 as k → ∞ (rate = QMC theory, documented out of scope) |
| G3.5-13 | 1213–1214, 1224–1226 / p.27 | "the same test for weak convergence as in the MLMC algorithm"; outer loop stops | DONE-DEV | `mlqmc_algorithm` | stops at `alg1Level` with (3.2) met |
| G3.5-14 | (implicit) / p.27 | MSE ≤ ε² at exit | DONE-DEV | `mlqmc_mse` | hypotheses: geometric decay from an anchor, E[Y] = E[P_L], V[Y] ≤ ΣV_ℓ |

## Details of the PARTIAL and MISSING items

(Round 25: see the resolution table of `notes/coverage/README.md`. Resolved: G2.4-32 (a) by
`giles_theorem2_indexSet` and `giles_theorem2_boundary_indexSet`; G2.6-09 and G2.6-10 by
`levelKeep_combined`; G3.3-05 by `consistency_check_empirical` (round 13); G3.5-05 by
`shiftedQMC_unbiased` and `randomShift_replicates` (round 10). Not formalised: G2.4-32 (b), the
optimality of the simplex among all index sets (listed in `PLAN.md`).)

* **G2.4-32** (p.15, l.689–692). Missing: (a) a theorem stating that 𝓛 = {θ·ℓ ≤ L(ε)} (θ_d = α_d + (γ_d −
  β_d)/2) itself achieves Theorem 2's bounds — easy, the proof already builds this set
  (`mimc_construction` → `mimc_complexity_core`); only the existential `∃ 𝓛` hides it. (b) "optimal":
  a lower bound showing no finite index set does better in order (under attained rates), or HNT's
  profit/knapsack characterisation (the simplex is a super-level set of E_ℓ/√(V_ℓC_ℓ) ∝ 2^{−θ·ℓ}) —
  the level-set equivalence is easy; a genuine lower bound over all index sets is moderate–hard
  (lattice-point lower bounds; `mimc_rect_lower_bounds` shows the technique for rectangles).
* **G2.6-09, G2.6-10** (p.19, l.844–851). The combined-variance and combined-cost identities at the
  optimal ratio N_ℓ = N_{ℓ+1}√(V_ℓC_{ℓ+1}/(V_{ℓ+1}C_ℓ)) are not stated; only their product
  (`levelKeep_product`, in a stronger IsLeast form). Trivial algebra.
* **G3.3-05** (p.22, l.1025–1029). Proved: P(ratio > 1) < 0.003 when a−b+c is exactly normal with mean 0
  and the ratio uses the TRUE standard deviations. Missing: the paper's ratio with empirical
  variances V_a, V_b, V_c. An asymptotic version (N → ∞) is Mathlib-level now — the pinned Mathlib has
  the 1-D CLT (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`) — but needs the CLT for
  the two independent sample means in a−b+c, consistency of the variance estimates and a
  Slutsky-type step: moderate–hard. Undocumented substitution (true for empirical variances).
  (Round 26: resolved in round 13 by `consistency_check_empirical`, `consistency_check_empirical_lt`.)
* **G3.5-05** (MISSING, implicit claim, p.26–27). For a point set {x_i} ⊂ [0,1)^d and U uniform on
  [0,1)^d, the shifted rule N⁻¹ Σ f({x_i + U}) is unbiased for ∫f, and independent shifts give iid
  replicates (what "32 random independent values" and `hmean` in `mlqmc_mse` rely on). Needs
  translation invariance of the Haar/Lebesgue measure on ℝ^d/ℤ^d (e.g. `UnitAddTorus` / `AddCircle`
  in Mathlib) plus the generic `blockMean` lemmas: easy–moderate.

## Lean statements that misstate the paper

(Round 25: two of the weak spots below are resolved — the consistency check with empirical variances
is `consistency_check_empirical` (round 13), and Theorem 2 on the simplex is
`giles_theorem2_indexSet` (round 10); `mlqmc_doubling_level` still encodes (3.3) only under its
equal-fraction model, as its docstring says. The errata in the next section are all in the
corrections table of `notes/statement-audit.md`.)

None found. Weak spots worth knowing (not misstatements):
* `mlqmc_doubling_level` is near-tautological (it encodes (3.3) only under an explicit
  equal-fraction model).
* `consistency_check_gaussian` silently uses true variances where the paper uses empirical ones
  (G3.3-05).
* Theorem 2's index-set shape is only in the proof (G2.4-32).

## Paper errata in the range that the Lean code (correctly) does not reproduce

* Theorem 2 lists the conditions i), iii), ii), iv), v); the Notes use swapped labels (documented in
  statement-audit).
* p.15–16: "the overall computational complexity will be less (often much less) than the optimal
  O(ε⁻²)" — should be "worse".
* p.15: "gives the optimal order of complexity only when η < 0 and Σγ_d/α_d ≤ 2" is true only when
  "optimal order" means O(ε⁻²) (the Lean reading); for D = 1 and η ≥ 0 the rectangle is plain MLMC
  and attains Theorem 2's order.
* p.18: subset written {ℓ₁,…,ℓ_M} but the formula starts at ℓ₀; V_{ℓ_m,ℓ_{m−1}} has the indices in the
  opposite order to the definition V_{ℓ1,ℓ2}, ℓ1 < ℓ2 (docstring of `subsetCost`).
* p.20: "ρ = 0, and so the increments … are independent" (the converse direction; Lean assumes only
  ρ = 0).
* p.21: (3.1) "ensures … less than ½ε²": only ≤ (equality when all ceiling arguments are integers).
* p.23: "p, q → 0 due to weak convergence": needs E[X_ℓ²] = p + q → 0 (variance/strong convergence);
  weak convergence gives only p − q → 0.
