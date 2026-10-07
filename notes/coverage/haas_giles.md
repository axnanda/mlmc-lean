# Coverage audit C5: Haas & Giles (2025), arXiv:2502.07123, whole paper

Auditor: independent coverage audit (read-only). Sources: `docs/haas_giles2025_arxiv_src/sections/*.tex`,
`main.tex`, `docs/haas_giles2025.txt` (equation numbers (1)-(41) taken from the typeset text).
The paper has no appendices. Lean: `MlmcLean/{Allocation,LevelDiff,StandardEstimator,Nested,EulerMaruyama,
GBMEulerMaruyama,GBMMilstein,CostComparison,ControlVariate,ApproxNormal,LUTLimits,RoundingError,
FixedPointPath,BitWidth,LagrangeBitWidth}.lean`. I read the theorem statements and hypotheses, not
just the docstrings. Every Lean name cited below exists in `MlmcLean/`. Each theorem is listed in
`scripts/AxiomCheck.lean`, except the helper lemma `errorBound_eq_factor_mul`. The other unlisted names
are `def`s. `hind_i` and `hind_x` are hypothesis names.

Status legend: DONE, DONE-DEV (documented deviation or rigorous version of a "≈" claim), PARTIAL,
MISSING, OUT-OF-SCOPE (OOS), N/A.

## Table

| id | eq./line | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| H1-01 | abstract, §1 p.1 | "MLMC reduces the total computational cost ... combining SDE approximations with multiple resolutions" | N/A | (giles_theorem1, gbm_mlmc_theorem1) | Background. Not an HG25 result. |
| H1-02 | §1 p.1 | "generate an optimal number of samples on each level, such that the overall computational cost is minimised subject to the desired bound on the variance" | DONE | optimal_cost_isLeast | Same as H2-10. |
| H1-03 | §1 p.1 | "most samples are computed on the coarser levels and hence are less expensive" | N/A | (coarsest_level_dominant) | Informal. For β>γ the Lean shows that level 0 carries Θ(ε⁻²) samples and a fixed share of the cost. |
| H1-04 | §1 p.2 | [NestedOliver] "bound the resulting error at each MC level by a product of the time step and the error in the random number approximation" | N/A | — | Result cited from another paper. HG25 does not prove it, and it is not formalised or listed as a gap. |
| H1-05 | §1 p.2 | "using approximate random variables reduces the cost of path generation by a factor 7" | N/A | — | Cited empirical result. |
| H1-06 | §1 p.2 | "bit-width optimisation procedure can be performed off-line ... excluded from the on-line time complexity" | DONE | levelwise_optimisation | Independence of ε (see H6-04). |
| H1-07 | abstract; §1 | "offers higher computational savings than the existing mixed-precision MLMC frameworks" | N/A | — | Numerical comparison. |
| H1-08 | §1 p.2 | FPGA can give each variable its own bit-width and can be reconfigured | OOS | — | Hardware fact. Covered by PLAN "Out of scope: Hardware and benchmark work". |
| H2-01 | (1) | dS_t = a dt + b dW_t | N/A | — | Definition. Mathlib has no Itô SDE (documented). |
| H2-02 | (2) | S_{i+1} = S_i + a h + b √h Z_i | N/A | emPath | Definition. |
| H2-03 | §2.1 p.3 | "For L sufficiently large we have the weak convergence E[P_L] ≈ E[P]" | OOS | gbm_weak_error_le | General SDEs need Itô calculus: documented in README and PLAN "Out of scope". Proved for GBM with α=½. |
| H2-04 | (3) | E[P_L] = Σ E[P_ℓ − P_{ℓ−1}], P_{−1}=0 | DONE | sum_integral_levelDiff, levelDiff | |
| H2-05 | (4) | fine path | N/A | emPath, emFine | Definition. |
| H2-06 | (5), p.3 | coarse path. "when i is even, S^c_{i+1} and S^c_{i+2} are both computed using the drift and volatility evaluated based on S^c_i". "both terms are computed using the same Brownian motion" | DONE | emCoarsePath_succ, eq_emCoarsePath, emCoarsePath_two_mul, map_pairSum_gaussian, measurePreserving_pairAvg, emCoarse_eq, integral_emCoarse | The coarse path is EM with step 2h driven by N(0,1) increments (Z_{2k}+Z_{2k+1})/√2, so E[P^c]=E[P^f_{ℓ−1}]. |
| H2-07 | (6) | Cost = Σ N_ℓ C_ℓ | DONE | optimal_cost_isLeast (objective), nestedCost_mean | Definitional. The expected total cost is proved in nested form (nestedCost_mean) and inside giles_theorem1. |
| H2-08 | (7) | Variance = Σ N_ℓ⁻¹ V_ℓ | DONE | mlmcEstimator_mean_variance, variance_sample_mean | For the estimator built from independent samples. |
| H2-09 | §2.1 p.3 | "N_ℓ = λ√(V_ℓ/C_ℓ), where λ = ε⁻²Σ√(V_ℓC_ℓ)" (Lagrange, real N_ℓ) | DONE | lagrangeN, lagrangeN_variance_cost, lagrangeN_unique | The stationary point is proved to be the unique global minimiser. |
| H2-10 | (8) | Cost_MLMC = ε⁻²(Σ√(V_ℓC_ℓ))², "ignoring the small increase ... when N_ℓ are rounded up" | DONE | optimal_cost_isLeast, cost_lower_bound, optimalN_variance, optimalN_cost | Variance ≤ ε² gives the same minimum. The rounding overhead is at most Σ C_ℓ. |
| H2-11 | §2.1 p.3 | standard MC "overall cost would be ε⁻²VC" | DONE | mc_cost, mc_cost_lower | |
| H2-12 | §2.1 p.3 | "if the factor V_ℓC_ℓ decreases (resp. increases) with level then the total cost of MLMC is approximately ε⁻²V_0C_0 (resp. ε⁻²V_LC_L)" | DONE-DEV | optimal_cost_decreasing, optimal_cost_increasing | "Decreases" and "increases" are read as geometric with ratio r. Two-sided bounds with factors (1−r)⁻² and (r/(r−1))². Stated in the docstrings. |
| H2-13 | §2.1 p.3 | "smaller than the standard Monte Carlo cost by a factor C_0/C_L (resp. V_L/V_0)" | DONE-DEV | mlmc_vs_mc_decreasing, mlmc_vs_mc_increasing | Uses V[P_L] in place of V_0 (docstring: "≈ V₀ in the paper"). Geometric rates as in H2-12. |
| H2-14 | §2.1 p.3 | "for Lipschitz payoffs for the Euler-Maruyama scheme the variance V_ℓ decreases exponentially with level" | OOS | gbm_correction_variance_le, variance_levelDiff_of_strong | General SDE: documented (Itô). GBM: V_ℓ ≤ c·2^{−ℓ}. The general statement is only conditional on the strong rate. |
| H2-15 | §2.1 p.3 | "the former leads to the MLMC estimation being cheaper than the standard Monte Carlo estimation" | N/A | (H2-12/13, gbm_mlmc_theorem1, mc_complexity) | Informal conclusion. |
| H2-16 | (9) | E[P_L] = Σ E[Δ̃P_ℓ] + E[ΔP_ℓ − Δ̃P_ℓ], "ensures that the expectations rigorously cancel out" | DONE | nestedEstimator_mean_variance, nested_mlmc_mse | |
| H2-17 | (10) | nested cost Σ Ñ_ℓC̃_ℓ + N^Δ_ℓC^Δ_ℓ | DONE | nestedCost_mean, nestedCost | |
| H2-18 | (11) | nested variance Σ Ñ⁻¹Ṽ + (N^Δ)⁻¹V^Δ | DONE | nestedEstimator_mean_variance, nested_mlmc_mse | Assumes only pairwise independence, a documented generalisation. |
| H2-19 | §2.2 p.4 | "N^Δ_ℓ = λ_M√(V^Δ_ℓ/C^Δ_ℓ) and Ñ_ℓ = λ_M√(Ṽ_ℓ/C̃_ℓ)" | DONE | nested_cost_isLeast (lagrangeN on nIdx) | |
| H2-20 | (12) | Cost_nested = ε⁻²(Σ√(ṼC̃)+√(V^ΔC^Δ))² | DONE | nested_cost_isLeast, nested_cost_lower_bound, nested_optimal_allocation | Integer overhead Σ(C̃+C^Δ). |
| H2-21 | §2.2 p.4 | "if V^Δ/Ṽ ≪ C̃/C^Δ ≪ 1 then ... saving of a factor approximately max_ℓ C̃_ℓ/C^Δ_ℓ" | DONE-DEV | nested_saving | Proved as the inequality (12) ≤ (1+δ)²θ(1+κ)r·(8). Documented in statement-audit.md and the readbacks. |
| H2-22 | §2.2 p.4 | "C^Δ_ℓ = C_ℓ + C̃_ℓ" | N/A | (used in levelCost34_le_levelCost33 …) | Cost-model definition. Nested.lean does not impose it, which is a generalisation. |
| H2-23 | §2.2 p.4 | "C_ℓ is much larger than C̃_ℓ at least on the first MC levels" | OOS | — | Hardware/cost fact. Documented (PLAN, hardware). |
| H2-24 | (13) | S̃_{i+1} = S̃_i + a h + b √h Z̃_i | N/A | gbmStep, gbmStep_eq | Definition. For GBM, Algorithm 1 is shown to compute (13). |
| H2-25 | §2.2 p.4 | "Ideally the cost of RNG on the FPGA would be almost negligible" | OOS | — | Hardware. Documented. |
| H3-01 | §3 p.4–5 | "we exploit the symmetry of Φ⁻¹ so we only need to approximate it on [0,1/2]" | DONE | lutValue_mirror, lutValue_upper_half | Holds for any f with f(1−u) = −f(u). |
| H3-02 | §3 p.5 | U ↔ D-bit integer J; low precision ↔ d-bit integer j | N/A | coupledUniform (j = ⌊J/2^{D−d}⌋) | Notation. |
| H3-03 | §3.1 p.5 | LUT of size 2^{d−1}. "The leading bit of j gives the sign ... next d−1 bits are used to pick the right value". "Locating the interval ... is trivial" | DONE | lutValue_upper_half, midpoint_mem_cell | The Lean mirror index is 2^d−1−j, the complement of the low bits. The paper's "next d−1 bits" gives the exact coupling only when read that way (minor imprecision in the paper). |
| H3-04 | (14)–(15) | minimising the MSE (14) "gives that Z_j is the mean of Φ⁻¹": Z_j = 2^d∫Φ⁻¹ | DONE | integral_sq_sub_eq, intervalMean_isLeast, eq_intervalMean_of_integral_sq_sub_le, lutValue_isLeast | Unique minimiser. Holds for general f with f and f² interval-integrable (true for Φ⁻¹). |
| H3-05 | §3.1 p.5 | "U = 2^{−D}(J + ½)" (coupled with the interval of j) | DONE | midpoint_mem_cell | |
| H3-06 | §3.1 p.5 | "for d=10 the LUT stores 2^9=512 values", "may not fit on the FPGA" | OOS | — | Hardware. The arithmetic is trivial. |
| H3-07 | §3.2 p.5 | "each X^{(i)} follows approximately the distribution N(0,1/n). Then Σ X^{(i)} has approximately the distribution N(0,1)" | PARTIAL | map_pairSum_gaussian (EulerMaruyama.lean) | Only the n=2 exact-Gaussian fact exists ((Z₀+Z₁)/√2 ~ N(0,1)), proved for the EM coarse increments and not linked to method 2. General n and any quantitative "approximately" statement for LUT values (e.g. variance of the sum) are missing. Undocumented. |
| H3-08 | §3.2 p.6 | "same LUT of size 2^{d/2−1}". "larger LUT of size 2^d by computing all possible sums ±X_k±X_l". n streams | DONE | card_signed_sums | |
| H3-09 | §3.2 p.5 | optimisation stage "improves the quality of the estimation compared to simply taking the LUT values" | DONE-DEV | alternating_min_antitone | Proves that objective (16) does not increase. Strict improvement is empirical. |
| H3-10 | (16) | sorting defines π. Least-squares minimisation of Σ(Z_{π(j)} − Z̃_j)² | DONE | sorting_minimises | The rearrangement inequality: sorting minimises (16) over permutations when Z is monotone. |
| H3-11 | §3.2 p.6 | "update the permutation π ... repeat ... The algorithm stops when the permutation has converged" | DONE-DEV | alternating_min_eventually_const, alternating_eventually_periodic, alternating_stationary | Proved: the objective is eventually constant, the iteration is eventually periodic, and it is stationary once π repeats. Convergence (period 1) is not guaranteed. The paper only observes it. |
| H3-12 | §3.2 p.6 | "20 and 100 iterations". "considerably reduces the MSE" | N/A | — | Empirical. |
| H3-13 | (17) | U = 2^{−d}π(j) + 2^{−D}((J−2^{D−d}j)+½) = 2^{−d}(π(j)−j) + 2^{−D}(J+½) | DONE | coupledUniform_eq, coupledUniform_mem, coupledUniform_eq_index, sum_coupledIndex | Also proves U ∈ I_{π(j)} and that U is uniform. |
| H3-14 | §3.2 p.6 | permutation table (size 2^d) on the CPU, LUT 2^{d/2−1} on the FPGA | N/A | — | Implementation. |
| H3-15 | §3.2 p.6 | n>2: "divided by √n ... coupled uniform variable ... exactly the same formula" | DONE | coupledUniform (any π), card_signed_sums | The √n scaling is a design choice. |
| H3-16 | §3.3 p.6 | Z̄_j = a+bj per I'_i = [[2^{i−1}, 2^i−1]], "LUT of size d − 1" | DONE | dyadic_index | |
| H3-17 | (18) | ∫(Z̄_j−Φ⁻¹)² = 2^{−d}(Z̄_j−Z_j)² + ∫(Z_j−Φ⁻¹)² | DONE | integral_sq_sub_lutValue | |
| H3-18 | (19) | "we only need to minimise Σ(Z̄_j − Z_j)²" | DONE | sum_integral_sq_sub_lutValue, sum_integral_sq_le_iff | |
| H3-19 | §3.3 p.6 | "(18) also shows that for the same value of d this approximation cannot be as good as the method 1" | DONE | method1_le | |
| H3-20 | §3.3 p.6 | "U is defined in the same way as in method 1 and the coupling follows naturally" | DONE | midpoint_mem_cell | |
| H3-21 | §3.4 p.7 | "the MSE obtained in methods 2 and 3 are necessarily larger than in method 1" | DONE | method1_le, method1_le_perm | ≥, with equality iff w = Z. |
| H3-22 | §3.4 p.7 | "for the first two dyadic intervals there are only two points in each so Z̄_j will exactly match Z_j" | DONE | affine_fit_exact | The numerical part is N/A. By the paper's own definition I'_1 = {1} has one point (minor inconsistency in the paper). |
| H3-23 | §3.4 p.7 | d=10 "only slightly worse". d=12 "nearly a factor 2" | N/A | — | Numerical. |
| H3-24 | §3.4 p.7 | "as d tends to infinity, the uniform intervals give MSE → 0" | DONE-DEV | tendsto_method1MSE | Holds for any f monotone on (0,1) with f and f² integrable. Mathlib has no Φ⁻¹, so its properties are assumed. Documented in the module docstrings. |
| H3-25 | §3.4 p.7 | "the dyadic intervals give MSE → C, for some positive constant C" | PARTIAL | dyadic_mse_ge, method3_mse_ge, method3_mse_not_tendsto_zero | Proved: MSE ≥ c > 0 for every d ≥ k+3 if f is strongly concave on one dyadic cell (true for Φ⁻¹ with k≥2; I checked (Φ⁻¹)'' = Φ⁻¹/φ(Φ⁻¹)² ≤ 2πΦ⁻¹(1/4) < 0). Missing: existence of lim MSE = C. Documented (LUTLimits docstring, PLAN M5). Round 14: DONE, the limit exists and is positive (`exists_tendsto_method3MSE`, `LUTAsymptotics.lean`). |
| H3-26 | §3.4 p.7 | "when d increases by 1 the MSE is reduced only in the interval closest to 0, so the error due to the other intervals remains the same" | N/A | (dyadic_mse_ge) | Heuristic and only approximately true: each cell's affine fit changes with the finer grid. The robust content is H3-25. |
| H3-27 | §3.4 p.7 | [Lee] further splitting "improves the approximation" | N/A | — | Citation. |
| H3-28 | §3.4 p.7 | "most of the values in method 2 occur in pairs (X_i+X_j and X_j+X_i)", "extra values of the form X_i+X_i" | DONE | card_image_add_le, choose_two_pow_add_one | At most 2^{d−1}+2^{d/2−1} distinct values. |
| H3-29 | §3.4 p.7 | MSE "very close". "method 2 is slightly more accurate" | N/A | — | Numerical. |
| H3-30 | §3.4 p.7 | method 1 has its "MSE divided by 2 each time d increases by 1. This was theoretically expected" | OOS | — | Needs asymptotics of Φ⁻¹, which Mathlib lacks. Documented in PLAN M5 "Not formalised". Only asymptotic (MSE ≍ 2^{−d}/d). Round 14: DONE-DEV, the order `2^{−d}/d` (`method1MSE_order`, `tendsto_log_method1MSE_div`, `LUTAsymptotics.lean`); the exact ratio limit ½ is not formalised. |
| H3-31 | §3.4 p.7 | same halving "intuitively true for method 2" | N/A | — | Heuristic/empirical. |
| H3-32 | §3.4 p.7 | "only a factor 2 increase in the MSE". Optimisation takes "extreme" values | N/A | — | Empirical. |
| H3-33 | §3.4 p.7–8 | methods 2, 3 suitable; "tests on real hardware are needed" | OOS | — | Hardware. Documented. |
| H3-34 | §3.4 p.8 | "with dyadic intervals, the MSE value cannot be arbitrarily small" | DONE-DEV | method3_mse_ge, method3_mse_not_tendsto_zero | Conditional on strong concavity of f on one dyadic cell, which holds for Φ⁻¹ but is not proved in Lean. Documented. |
| H4-01 | Alg. 1 p.8 | "This algorithm details how we decomposed the operations to compute each time step from (13)" | DONE | gbmStep, gbmStep_eq, gbmPath_succ, gbmPath_eq_prod | |
| H4-02 | §4.1 p.8 | x̃ = (−1)^s 2^{e−d} n, n < 2^d | DONE | roundFixed, roundFixed_mantissa | Under the no-overflow condition \|x\| < 2^e − 2^{e−d−1}. |
| H4-03 | §4.1 p.8 | exponents from 10^6 paths. Word-length d+1 | N/A | — | |
| H4-04 | (20) | \|δx_i\| ≤ 2^{e_i−d_i−1} | DONE | abs_sub_roundFixed_le | |
| H4-05 | (21) | "E[δx_i²] = 4^{e_i−d_i−1}" | DONE-DEV | integral_sq_roundError_le | Corrected to ≤. I verified the correction: equality fails (x on the grid gives 0), and the paper itself calls (21) "the more general bound". The correction is recorded only in the RoundingError.lean docstrings (see summary). |
| H4-06 | (22) | uniform on [−2^{e−d−1}, 2^{e−d−1}] ⇒ E[δx²] = 4^{e−d}/12 | DONE | integral_sq_uniform_roundError, integral_sq_of_isUniform | |
| H4-07 | (23) | P − P̃ ≈ Σ ∂P/∂x_i δx_i | N/A | (perturbed_sub_eq) | First-order modelling approximation with no error claim. The Lean §4 results are about the linearised error Σx̄_iδx_i (documented). perturbed_sub_eq is the exact identity for Alg. 1 when only S is rounded. |
| H4-08 | (24) | x̄_i = ∂P/∂x_i | N/A | — | Definition. |
| H4-09 | (25) | V[P−P̃] = ΣV[x̄_iδx_i] + 2Σ_{i≠j}Cov(·,·) | DONE-DEV | variance_sum_eq | Corrected to Σ_{i≠j} over ordered pairs without the factor 2. The Lean identity is correct. Partial disagreement: the printed formula is correct if i≠j means unordered pairs, and the paper's own (27) assumes that reading. So this is ambiguous notation, not a mathematical error. |
| H4-10 | §4.2 p.9 | "We assume that the sensitivities x̄_i and the rounding errors δx_i are independent" | N/A | hypotheses hind_i / hind_x | Modelling assumption. |
| H4-11 | §4.2 p.9 | "It always holds that V[x̄_iδx_i] ≤ E[x̄_i²δx_i²]" | DONE | variance_le_integral_sq | |
| H4-12 | (26) | V ≤ (1/12)ΣE[x̄_i²]4^{e_i−d_i} ≜ V_indep | DONE | variance_linearised_indep, variance_sum_mul_le_of_indep, vIndep | Same hypotheses as the paper (x̄_i ⊥ δx_i, products pairwise independent, δ uniform). Stated for the linearised error. |
| H4-13 | (27) | V ≤ (Σ√E[x̄²]2^{e−d−1})² ≜ V_corr (assuming perfect correlation) | DONE | variance_linearised_corr, variance_sum_le_sq_sum_sqrt, sqrt_variance_mul_le, vCorr | Stronger than the paper: holds for any joint law given (20) a.s. (Cauchy–Schwarz). I verified this. |
| H4-14 | (28) | V'_indep = (1/12)ΣE[x̄²]4^{e−d} + (1/12)ΣE[Z̄_j²]×MSE | DONE-DEV | variance_extended_indep | Corrected: the MSE term has no 1/12. I verified that the printed bound is false (s=∅, Z̄≡1: V[δZ] = MSE > MSE/12) and inconsistent with (29). |
| H4-15 | (29) | V'_corr = (Σ√E[x̄²]2^{e−d−1} + Σ√(E[Z̄_j²]MSE))² | DONE | variance_extended_corr | Holds as printed. |
| H4-16 | §4.3 p.10 | "choose the size of the LUT such that the term containing the MSE in (28) is smaller or equal to V_indep" | DONE | variance_extended_le_two_mul | Then V ≤ 2V_indep, using the corrected (28). |
| H4-17 | §4.4 p.10 | bounds "are respected". "variance obtained numerically with approximate RNG respects the bounds V'_indep, V'_corr" | N/A | — | Numerical. |
| H4-18 | §4.4 p.10 | (26) is chosen "because this bound is tighter than (27)" | DONE | vIndep_le_vCorr | In fact V_indep ≤ V_corr/3. |
| H5-01 | §5 p.10 | "if we neglect the cost of RNG, the cost C̃_ℓ ... equals the sum of the cost of the elementary operations" | OOS | — | Hardware cost model. Documented (PLAN, hardware). |
| H5-02 | (30) | C̃ = Σ_M d_id_j + Σ_S max(d_i,d_j) (Lee et al.) | N/A | opCost | Definition. |
| H5-03 | §5 p.11 | "replacing d_id_j by its upper bound ½(d_i²+d_j²), and max(d_i,d_j) by ... d_i+d_j" ⇒ (31) | DONE | opCost_le_sepCost, opCount | M_i is counted per operand, so a square counts twice. This is needed for the bound and documented. |
| H5-04 | (31) | "sum of terms which depend on only one d_{i,ℓ}" | DONE | sepCost, hasDerivAt_sepCost_update | |
| H5-05 | §5 p.11 | "C_ℓ ≈ 2^ℓ C_RNG" | OOS | — | CPU cost fact (hardware). Documented generically. |
| H5-06 | §5 p.11 | "C_RNG is very large compared to C̃_ℓ/N" | OOS | — | Hardware. |
| H6-01 | (32) | total cost after sample optimisation = (12) | DONE | nested_cost_isLeast, totalCost32_bounds | |
| H6-02 | §6 p.11 | "Ṽ_ℓ ... approximately equal to V_ℓ". V^Δ_ℓ "approximated by V_indep" | N/A | (Ṽ=V as hypothesis in LagrangeBitWidth) | Modelling assumptions. |
| H6-03 | (33) | "bit-widths of all variables of level ℓ can be optimised independently of the other levels by minimising (33)" | DONE | levelwise_optimisation | |
| H6-04 | §6 p.11 | "this optimisation is independent of the overall desired accuracy ε" | DONE | levelwise_optimisation | |
| H6-05 | §6 p.11 | number of samples "derived analytically as shown in Section 2" | DONE | nested_cost_isLeast, nested_optimal_allocation | |
| H6-06 | §6 p.11 | on-line algorithm = classical MLMC with two expectations per level | N/A | — | |
| H6-07 | (34) | (33) "using the fact that C_ℓ ≫ C̃_ℓ, is approximated as" √(V_ℓC̃_ℓ)+√(V^Δ_ℓC_ℓ) | DONE-DEV | levelCost34_le_levelCost33, levelCost33_le_sqrt_mul, levelCost33_le_add_mul, totalCost32_bounds | Quantified: (34) ≤ (33) ≤ (1+C̃/(2C))·(34). Takes Ṽ=V exactly (docstring). |
| H6-08 | (35) | "minimising V^Δ_ℓ(d) subject to a fixed C̃_ℓ(d) leads to the equation (35)". "λ controls the trade-off" | DONE | eq35_of_isLocalMinOn, lagrangian_le_of_eq35, vIndepR_le_of_eq35, sepCost_le_of_eq35, exists_eq35_isMin | Necessity (Lagrange) and sufficiency (convexity), with (26) and (31). |
| H6-09 | §6.1 p.12 | (35) "gives a set of uncoupled nonlinear scalar equations ... easily solved" | DONE | hasDerivAt_vIndepR_update, hasDerivAt_sepCost_update, exists_unique_bitWidth | Unique solution for λ>0. |
| H6-10 | (36) | √(C/V^Δ)∂V^Δ + √(V/C̃)∂C̃ = 0 from the derivative of (34) | DONE | hasDerivAt_levelCost | |
| H6-11 | §6.1 p.12 | "again of the form (35), where λ = √(V_ℓV^Δ_ℓ/C_ℓC̃_ℓ)" | DONE | levelCost_stationary_iff | |
| H6-12 | §6.1 p.12 | "update the value of λ until we reach the optimal solution of the overall problem" | N/A | — | Algorithmic. Fixed-point existence and global optimality of the stationary point are not claimed as proved. |
| H6-13 | (37) | Σ_i∂V^Δ + λΣ_i∂C̃ = 0 at uniform bit-width | DONE | eq37_iff, lambda37_pos, eq37_of_eq35 | |
| H6-14 | §6.1 p.12 | "Although we do not prove it formally ... the resulting function is convex which ensures the existence of an optimum" | N/A | — | The paper says explicitly that it is unproven. research-notes records "convexity ... observed, not proved". |
| H6-15 | §6.1 p.12 | golden section search for λ | N/A | — | Algorithm. |
| H6-16 | §6.1 p.12, Fig. 3, 5 | "the cost factor ... is smaller than 1 which means that the nested framework is cheaper than the standard Multilevel Monte Carlo". Optimised beats best uniform | PARTIAL | nested_saving, totalCost32_bounds | The numbers are N/A. The implication (per-level factor √(C̃/C)+√(V^Δ/V) ≤ ρ < 1 ⇒ (32) ≤ (1+r)ρ²·(8)) is not stated. It is a one-liner from totalCost32_bounds. Paper typo: the Fig. 3/5 captions write √(Ṽ/V). (34)/√(VC) = √(C̃/C)+√(V^Δ/V), and with Ṽ≈V the printed factor would exceed 1. |
| H6-17 | §6.1 p.12 | factor 7 (level 0) and 5 (level 1). Costs 41, 277. C_RNG = 10^4. The C̃≪C limitation | N/A | — | Numerical. |
| H6-18 | §6.2 p.13 | Lagrange approach "good enough compared to several integer programming approaches" | N/A | — | Empirical. |
| H6-19 | (38) | ratio r_{i,ℓ} = [V_indep(d*) − V_indep(d*+e_i)]/[C̃(d*+e_i) − C̃(d*)] | DONE | vIndepR_sub_update_add_one, sepCost_update_add_one_sub | Numerator E_i4^{e_i−d_i}/16. Denominator M_i(d_i+½)+M'_i. The ratio is uncoupled. Paper typo (round-15 audit): §6.2 prints "first round down the solution to d*_{i,ℓ} = d_{i,ℓ}" without the floor; the Lean uses ⌊d⌋. |
| H6-20 | §6.2 p.13 | "This heuristic performs well and is guaranteed to obtain a feasible solution" | DONE | greedy_rounding_feasible, vIndepR_antitone | Any order. At most n added bits. "Performs well" is empirical. |
| H6-21 | (39) | con2, mul1, sum1, mul2 ∼ √h | PARTIAL | abs_con1_con2, integral_sq_mul1_le, integral_sq_sum1_le, integral_sq_mul2_le | \|con2\| = \|σ\|√h exactly. For mul1, sum1 and mul2 there are only mean-square upper bounds E[x²] ≤ c·h. Lower bounds (the two-sided "∼") are missing. The docstring states these as O-bounds but does not record the gap. |
| H6-22 | (40) | con1 ∼ h | DONE | abs_con1_con2 | Exactly \|con1\| = \|r\|h. |
| H6-23 | (41) | S ∼ 1 | PARTIAL | integral_sq_gbmPath_le | Only E[S_n²] ≤ S_0²e^{cnh}. The lower bound (S bounded away from 0, e.g. E[S_n] = S_0(1+rh)^n) is missing. Undocumented. |
| H6-24 | §6.3 p.13 | "The takeaway is that the variables S_i are the largest" | PARTIAL | (H6-21, H6-23) | Needs the H6-23 lower bound together with the H6-21 upper bounds. The comparison is not stated. |
| H6-25 | §6.3 p.13 | S "need the largest bit-widths"; bit-width increases each level | N/A | — | Heuristic explanation of numerics. |
| H6-26 | §6.3 p.13 | Fig. 4 order/slope "consistent" | N/A | — | Numerical. |
| H6-27 | §6.3 p.13 | factors of S, mul2 "approximately multiplied by 2 at every level" | N/A | (hypothesis hF of errorBound_succ) | Empirical. |
| H6-28 | §6.3 p.13 | "d_{S,ℓ+1}=d_{S,ℓ}+1 is equivalent to division by 4 ... the bound on E[S̄²δS²] is divided by 2 at every level" | DONE | rpow_four_sub_add_one, errorBound_succ, errorBound_eq_factor_mul | Conditional on the empirical doubling. |
| H6-29 | §6.3 p.13–14 | mul2 similar; Fig. 7 "all variables give a similar evolution" | N/A | — | Numerical. |
| H6-30 | §6.3 p.14 | "the portion of the overall error due to a certain variable is constant over levels" | DONE | errorShare_succ | Conditional on all bounds halving. |
| H6-31 | §6.3 p.14 | "to leading order, all errors are roughly of the same size ... if an error was 'disproportionately' small, there would be potential for cost savings" | DONE-DEV | marginalRatio_eq_of_isLocalMinOn | Formal content: equal marginal ratios at a constrained local minimum. So errors are proportional to marginal costs, not equal. "Roughly the same size" is heuristic. |
| H6-32 | Fig. 7 caption | (1/12)E[x̄²]4^{e−d} are "Upper bounds ... on the expected squared errors E[x̄²δx²]" | DONE-DEV | integral_sq_uniform_roundError, integral_sq_roundError_le | Equality under the uniform model (22) with independence. Without (22) the bound is only 3× that ((21)). Not stated as a separate theorem. |
| H6-33 | §6.3 p.14 | adapting precision "allows us to keep improving the accuracy ... as the time step tends to 0". "net error evolves like the time step h" | DONE-DEV | errorBound_eq_div_pow | Bounds ∝ 2^{−ℓ} ∝ h_ℓ, conditional on the observed doubling and d_{ℓ+1}=d_ℓ+1. |
| H6-34 | §6.3 p.14 | fixed precision: "rounding error at each time step of the EM scheme is of order O(h⁻¹2^{e_{S,ℓ}−d_{S,ℓ}})" | DONE | integral_abs_roundFixed_path_sub_le, integral_abs_perturbed_sub_le, perturbed_sub_eq, abs_perturbed_sub_le | Read as the accumulated error at the final time: E\|S̃_N−S_N\| ≤ (T/h)2^{e−d−1}e^{cT}, with S rounded after every step. |
| H6-35 | §6.3 p.14 | with fixed bit-widths "starting at a certain level, the accuracy would decrease". "for small time steps the rounding errors ... are relatively large" | PARTIAL | (integral_abs_roundFixed_path_sub_le: upper bound only) | Needs a lower bound on the accumulated rounding error, e.g. under model (22): V[S̃_N−S_N] ≥ c·N·4^{e−d}, compared with the discretisation error. Not formalised. Undocumented. |
| H7-01 | §7 | "reduces the cost at these levels by a factor 5 or 7". "overall savings are significant" | N/A | — | Numerical. |
| H7-02 | §7 | "even more efficient for the Milstein scheme because its higher order strong convergence leads to a greater proportion of the computational costs being on the coarsest levels" | N/A | (gbm_mil_correction_variance_le, coarsest_level_dominant) | Speculative. Supporting facts exist: β=2 for GBM Milstein, and for β>γ level 0 carries a fixed share of the cost. |
| H7-03 | §7 | next stage: implement on FPGAs; compare with half precision | OOS | — | Hardware. Documented. |

## Counts

129 claims in total.

| Status | Count |
|---|---|
| DONE | 57 |
| DONE-DEV | 14 |
| PARTIAL | 7 |
| MISSING | 0 |
| OOS | 12 (all documented: general SDE rates, Φ⁻¹ asymptotics, or hardware) |
| N/A | 39 |

## Checks of the repository's "corrected" versions

- **(21):** the correction is right. With "=" the statement is false, and ≤ is what the paper later uses ("the more general bound").
- **(25):** the Lean identity is right. The printed "2Σ_{i≠j}" double-counts only under the ordered-pair reading. Under the unordered-pair reading it is correct, and the paper's (27) presupposes that reading, so this is ambiguous notation rather than an error.
- **(27):** the repository's claim is right. It holds for any joint law, not only under perfect correlation.
- **(28):** the correction is right. The printed 1/12 on the MSE term is wrong: counterexample above, and it contradicts (29) and the definition MSE = E\|Z−Z̃\|².

## Documentation inconsistencies

- PLAN.md M5 (line 136) says the §4 corrections are "recorded in `notes/statement-audit.md`". They are not: statement-audit.md covers only HG25 (9)–(12). The corrections (21), (25) and (28), and the strengthening of (27), appear only in the RoundingError.lean docstrings.
- The README "Modelling choices" section does not list them either, although the PLAN ground rules require that.
- README line 24 places "(13)" in §3. It is in §2.

## Lean misstatements

None found.
