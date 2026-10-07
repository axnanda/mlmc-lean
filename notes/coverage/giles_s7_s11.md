# Coverage audit C4 — Giles (2015) §7–§11 vs `MlmcLean/`

Scope: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §7 (PDEs/SPDEs),
§8 (continuous-time Markov chains), §9 (nested simulation), §10 (other applications), §11
(conclusions) = `docs/giles2015.txt` l. 2097–2858 (author's pages 49–64). Formulas that mattered
were checked on the typeset PDF (pp. 49, 51, 54–56, 58–62).

Method: every Lean statement cited below was read in the source (hypotheses and conclusion, not
only the docstring): `PDEExamples`, `PoissonCoupling`, `TauLeapingMLMC`, `NestedSimulation`,
`NestedMLMC`, `MarkovChain`, `MarkovLimit`, plus the generic results reused (`Corrections`,
`LevelDropping`, `Allocation`, `EulerMaruyama`, `ErrorAnalysis`, `Theorem2`). All cited theorems are
in `scripts/AxiomCheck.lean`. Documentation checked: README (table + "Modelling choices"), PLAN
("Not formalised", "Out of scope"), `notes/statement-audit.md`, `notes/research-notes.md`,
`notes/readbacks/*`, module docstrings. The repository was not built (read-only audit).

Status legend: DONE / DONE-DEV / PARTIAL / MISSING / OOS (out of scope; "doc" = documented,
"NOT doc" = not documented, "generic" = only covered by the README's generic scope sentence) / N/A.

## Counts

| Status | # |
|---|---|
| DONE | 30 |
| DONE-DEV | 19 |
| PARTIAL | 7 |
| MISSING | 8 |
| OOS | 10 (6 documented, of which 1 only vaguely; 3 NOT documented; 1 generic only) |
| N/A | 51 |
| **Total** | **125** |

## Table

| id | line / page | claim (short quote) | status | Lean name(s) | notes |
|---|---|---|---|---|---|
| G7.0-01 | 2098–2101 / p.49 | "equally applicable to SPDEs … savings would be greater because the cost of a single sample increases more rapidly with grid resolution" | N/A | (cf. `mc_complexity`, `mlmc_vs_mc_increasing`) | qualitative |
| G7.0-02 | 2102–2108 | history (Graubner; elliptic/parabolic/hyperbolic SPDE papers) | N/A | — | historical |
| G7.0-03 | 2109–2112 | "construction … quite natural, geometric sequence of grids … numerical analysis of the variance … very challenging" | N/A | — | informal |
| G7.1-01 | 2116–2130 / p.49 | elliptic BVP d/dx(c du/dx) = −50Z², u(0)=u(1)=0, Z~N(0,1), c = 1+ax, a~U(0,1), P = ∫u | N/A | — | model; not defined in Lean |
| G7.1-02 | 2131–2133 | "h_ℓ = 2^{−(ℓ+1)}, so there is just one interior grid point on the coarsest level" | N/A | (h_ℓ in `elliptic_rates`) | trivial arithmetic |
| G7.1-03 | 2133–2135 | "second order central difference approximation … (equivalent to a finite element approximation with a 1-point quadrature)" | MISSING | — | Algebraic identity: P1 stiffness with midpoint quadrature, divided by h, is the conservative 3-point FD operator; load = h·50Z². Formalisable (hat-function integrals), easy–moderate, low value. Not documented. |
| G7.1-04 | 2136–2137 | "uniform second order accuracy means that there is a constant K such that \|P − P_ℓ\| < K h_ℓ²" | OOS (doc) | — | FD convergence order; README l.28–30 ("finite differences … not formalised in general"). Paper imprecision: u = 50Z²·v(x;a), so the error is ∝ Z² (unbounded) — K must be random (∝Z², E[K²] < ∞), not a constant. Round 16: the scheme is solved exactly and |P − P_ℓ| ≤ (50/3) Z² h_ℓ² with a random constant (`ellipticFD_error`, `ellipticPl_error`, `EllipticFD.lean`); no deterministic K exists. |
| G7.1-05 | 2137–2138 | "and therefore we have α = 2, β = 4" | DONE-DEV | `rates_of_pathwise`, `elliptic_rates`; L² route: `variance_levelDiff_of_strong`, `weak_rate_of_second_moment` | Constants check: \|E[P_ℓ−P]\| ≤ (K/4)2^{−2ℓ}, V[P_{ℓ+1}−P_ℓ] ≤ (25/16)K²2^{−4(ℓ+1)} ✓. The hypothesis is the paper's literal sure bound for all ω (readback `giles_applications.md` flags "sure, uniform-in-ω bound"); it is unsatisfiable for the paper's own example (Gaussian Z). The random-K version follows from the generic L² lemmas, but no §7.1 instance states it. Round 16: end to end for the actual scheme, `elliptic_fd_rates`. |
| G7.1-06 | 2138 | "and γ = 1" | DONE-DEV | `pde_complexity` (input) | cost-model input; no count lemma (unlike `parabolic_cost`); trivial |
| G7.1-07 | 2173 / p.51 | "resulting in an O(ε⁻²) complexity" | PARTIAL | `pde_complexity` (complexityBound 2 4 1 = ε⁻²), `giles_theorem1` | α ≥ ½min(β,γ) holds Post-round-17 audit: only the bound is evaluated; no end-to-end instance for the elliptic estimator (planned with `elliptic_fd_rates`). |
| G7.1-08 | 2173–2174 | "features can be verified in … Figure 7.10" | N/A | — | empirical |
| G7.1-09 | 2175–2182 | parabolic SPDE du = u_xx dt + 10 dW, zero BC/IC, P = ∫u²(x,0.25) | N/A | — | model (paper omits dx) |
| G7.1-10 | 2183–2194 | scheme u^{n+1}_j = u^n_j + (k/h²)(u_{j+1}−2u_j+u_{j−1}) + 10ΔW_n | N/A | `heatStep` (+ additive noise in `heatStep_sub`) | definition captured on a ℤ-indexed grid (no boundary) |
| G7.1-11 | 2195–2198 | h_ℓ = 2^{−(ℓ+1)}, k_ℓ = ¼h_ℓ² | DONE | `parabolic_ratio` | λ = k/h² = ¼ |
| G7.1-12 | 2199–2201 | "Keeping k_ℓ/h_ℓ² = ¼ ensures the explicit numerical discretisation is stable on all levels" | DONE | `abs_heatStep_le`, `heatStep_sub`, `heatStep_alternating`, `one_lt_abs_one_sub_four_mul`, `parabolic_ratio` | max principle for 0 ≤ λ ≤ ½ (differences of noisy solutions follow the noise-free step), growth of (−1)^j by \|1−4λ\| > 1 for λ > ½; infinite grid, Dirichlet boundary not modelled (same argument) |
| G7.1-13 | 2201–2204 | "grid points double … timesteps ×4 … cost per sample increases by factor 8, giving γ = 3" | DONE | `parabolic_cost` | (1/h_ℓ)(T/k_ℓ) = 32T·2^{3ℓ} ✓ |
| G7.1-14 | 2205–2207 | "Because the stochastic forcing is additive … Euler-Maruyama … is actually equivalent to a Milstein discretisation" | DONE-DEV | `milsteinStep_eq_emStep` | scalar step with state-independent volatility; the SPDE (componentwise additive noise) is the same identity |
| G7.1-15 | 2207 | "hence the time discretisation errors are O(k)" | OOS (doc) | — | strong order of Milstein; README l.28–30, PLAN "Out of scope" |
| G7.1-16 | 2208 | "spatial discretisation errors which are O(h²)" | OOS (doc) | — | FD convergence; README l.28–30 |
| G7.1-17 | 2209 | "therefore the solution error is O(2^{−2ℓ}) and hence α = 2 and β = 4" | PARTIAL | `rates_of_pathwise` (sure bound); generic L²: `variance_levelDiff_of_strong` (β), `weak_rate_of_second_moment` (α) | O(k)+O(h²) with k = h²/4 ⇒ O(4^{−ℓ}) is trivial. The SPDE error is an L² (strong) error, so `rates_of_pathwise` does not apply literally; the L² lemmas do but are not instantiated (P = ∫u² is quadratic: needs moment bounds). Note (round-15 audit): `rates_of_pathwise` needs a deterministic `K`, which the parabolic example (Gaussian `u`) cannot have; only the generic L² lemmas apply, and they are not instantiated for it. Post-round-17 audit: PARTIAL, nothing about the SPDE itself is proved; `rates_of_pathwise` needs a deterministic `K`, which the example cannot have. |
| G7.1-18 | 2209–2210 | "This leads to the optimal complexity of O(ε⁻²)" | PARTIAL | `pde_complexity` (complexityBound 2 4 3 = ε⁻²) | α = 2 ≥ 3/2 Post-round-17 audit: PARTIAL, evaluation of the bound only; the rates are not proved for the parabolic example. |
| G7.1-19 | 2211–2212 | "confirmed in the numerical results shown in Figure 7.11" | N/A | — | empirical |
| G7.2-01 | 2214–2217 / p.51 | −∇·(κ∇p) = 0 in D, Dirichlet/Neumann BC | N/A | — | model |
| G7.2-02 | 2218–2255 | κ lognormal: log κ Gaussian, zero mean, covariance R(x,y) = r(x−y) | N/A | — | model |
| G7.2-03 | 2255–2261 / p.53 | Karhunen–Loève: log κ = Σ √θ_n ξ_n f_n(x), θ_n eigenvalues (decreasing), f_n eigenfunctions, ξ_n iid N(0,1) | OOS (NOT doc) | — | Mercer/KL spectral theory of covariance operators; no mention in README/PLAN/notes beyond the generic scope sentence (README l.18–22) |
| G7.2-04 | 2262–2264 | "more efficient to generate them using a circulant embedding … FFTs" | N/A | — | computational |
| G7.2-05 | 2265–2269 | grid doubled per level; KL truncated after K_ℓ terms, K_ℓ increasing | N/A | — | construction |
| G7.2-06 | 2270–2273 | "variables for the fine level can be partitioned into those for the coarse level … ξ_ℓ = (ξ_{ℓ−1}, z_ℓ)" | N/A | (generic (2.4): `integral_fineCoarseDiff`) | construction; (2.4) is automatic (coarse sample = level-(ℓ−1) approximation at a sub-vector with the same law) |
| G7.2-07 | 2274–2279 | "numerical analysis … challenging because the diffusivity is unbounded, but Charrier, Scheichl & Teckentrup … successfully analysed it" | OOS (NOT doc) | — | FE error analysis with lognormal coefficients (cited); not mentioned anywhere |
| G7.3-01 | 2281–2288 / p.53 | SPDE dp = −μp_x dt + ½p_xx dt − √ρ p_x dM_t, x>0, p(0,t)=0 | N/A | — | model |
| G7.3-02 | 2288–2295 | interpretation (distance to default); payoff via ∫p dx at discrete times | N/A | — | informal |
| G7.3-03 | 2296–2320 / p.54 | "A Milstein time discretisation … and a central space discretisation … gives p^{n+1}_j = p^n_j − (μk+√(ρk)Z_n)/(2h)(p_{j+1}−p_{j−1}) + ((1−ρ)k+ρkZ_n²)/(2h²)(p_{j+1}−2p_j+p_{j−1})" | MISSING | (cf. `milsteinStep`) | Derivation = ring identity (Milstein correction ½B²p(ΔM²−k) with B = −√ρ∂_x, B² = ρ∂_xx, then ∂_x→D₁, ∂_xx→D₂); checked by hand: formula consistent. Easy. Paper typo (p.54): "√h Z_n corresponds to an increment of the driving … Brownian motion" should be √k Z_n. Round 17: the scheme is the Milstein step with increment `√k Z_n` (`spdeStep_eq_milstein`, `SPDEStability.lean`); the paper's "`√h Z_n` corresponds to an increment" should read `√k Z_n` (`k` is the time step). |
| G7.3-04 | 2321–2323 | "k_ℓ = k_{ℓ−1}/4 and h_ℓ = h_{ℓ−1}/2 due to numerical stability considerations which are analysed in the paper" | OOS (NOT doc) | (cf. `abs_heatStep_le`) | mean-square (Fourier) stability of a scheme with random coefficient ρkZ²/h² (the §7.1 max-principle argument fails, the coefficient is unbounded); cited; not mentioned Round 17: von Neumann mean-square stability (`SPDEStability.lean`): `E|G|² ≤ 1 + μ²λk` for all modes iff `λ(1 + 2ρ²) ≤ 1`, `λ = k/h²` (`spde_meanSquare_stable`, `spde_meanSquare_unstable`, also for periodic data in `ℓ²`, `spde_meanSquare_stable_periodic`), so fixed `λ` with `h_ℓ = h_{ℓ−1}/2` forces `k_ℓ = k_{ℓ−1}/4` (`spde_level_refinement`, `spde_levels_stable`, `spde_level_cost`). The condition is derived here; Giles–Reisinger (2012) is not in `docs/`. |
| G7.3-05 | 2323–2326 | coupling by "summing the fine path Brownian increments … exactly the same as for SDEs" | DONE-DEV | `measurePreserving_pairAvg`, `map_pairSum_gaussian`, `emCoarse_eq`, `integral_emCoarse` | generic SDE coupling, any functional of the increments |
| G7.3-06 | 2326–2327 | "computational cost increases by factor 8 on each level" | DONE-DEV | `parabolic_cost` | stated for h_ℓ = 2^{−(ℓ+1)}, k_ℓ = h_ℓ²/4; same scaling |
| G7.3-07 | 2327–2328 | "numerical experiments indicate that the variance decreases by factor 8" | N/A | — | empirical (β = 3) |
| G7.3-08 | 2328–2329 | "overall … complexity … is again O(ε⁻²(log ε)²)" | PARTIAL | `complexityBound_of_eq`, `giles_theorem1` | generic β = γ (= 3) regime; no §7.3 instance; needs α ≥ 3/2 (not discussed by the paper) Post-round-17 audit: PARTIAL, generic evaluation only. |
| G7.3-09 | 2330–2334 | Bujok–Reisinger extension (jumps; discrete monitoring, p = 0 for x ≤ 0) | N/A | — | cited |
| G7.4-01 | 2336–2340 / p.54 | high-accuracy FE A(ω)u(ω) = f(ω) | N/A | — | model |
| G7.4-02 | 2341–2351 | reduced basis u(ω) ≈ Σ u_k(ω)u_k, A_K(ω)(u₁…u_K)ᵀ = f_K(ω) | N/A | — | model (Galerkin projection) |
| G7.4-03 | 2355–2357 / p.55 | estimate E[f(u)]; "larger values for K lead to greater accuracy, but at a much larger cost" | N/A | — | informal |
| G7.4-04 | 2357–2359 | "makes K a function of the level ℓ, so that most simulations are performed with a small value for K" | N/A | — | description (consistent with (1.1)) |
| G7.4-05 | 2360–2365 | "geometric MLMC is not appropriate … estimate V_{ℓ1,ℓ2} ≡ V[P_{ℓ1}−P_{ℓ2}] for all pairs … determine the optimal subset of levels" | DONE-DEV | `subsetCost_eq`, `subset_optimal_cost`, `exists_optimal_subset`, `card_levelSubsets`, `sum_subsetCorr` | generic §2.6 results with pairwise V_{ℓ1,ℓ2}; real sample sizes; estimation from trial samples not modelled |
| G8-01 | 2367–2371 / p.55 | Anderson–Higham MLMC for CTMCs; "wide applicability" | N/A | — | informal |
| G8-02 | 2372–2378 | tau-leaping "x_{n+1} = x_n + P(hλ(x_n))", P(t) unit-rate Poisson on [0,t] | DONE-DEV | `tauStep`, `tauChain` | single reaction, scalar count x ∈ ℕ, stoichiometry +1 (general stoichiometric vector not covered); documented in the module docstring |
| G8-03 | 2378–2384 | coarse path "x^c_{n+2} = x^c_n + P(2hλ(x^c_n)) for even timesteps" | DONE | `tauChain lam (2*h)`, `coupledTwoStep_snd`, `coupledChain_snd` | — |
| G8-04 | 2386–2389 | "for any t1, t2 > 0, the sum of two independent Poisson variates P(t1), P(t2) is equivalent in distribution to P(t1+t2)" | DONE | `poisson_add_hasLaw` | t ≥ 0 allowed |
| G8-05 | 2389–2391 | "express the coarse path Poisson variate as the sum of two Poisson variates, P(hλ(x^c_n)) corresponding to the first and second fine path timesteps" | DONE | `coupledTwoStep`, `coupledTwoStep_snd`, `poisson_bind_shift` | — |
| G8-06 | 2391–2407 / pp.55–56 | "P1 = P(h min(λ(x_n),λ(x^c_n))), P2 = P(h\|λ(x_n)−λ(x^c_n)\|) … P1 for the path with the smaller rate, and P1+P2 for the path with the larger rate" | DONE | `couplePair`, `coupledIncr`, `coupledIncr_fst`, `coupledIncr_snd`, `coupled_increments_hasLaw` | the second fine step couples λ(x_{n+1}) with the frozen coarse rate λ(x^c_n) (the paper spells out only the first step) |
| G8-07 | 2378–2407 (implicit) | coupled paths have the fine/coarse tau-leaping laws ⇒ telescoping (2.4) respected | DONE | `coupledChain_fst`, `coupledChain_snd`, `tauLeaping_2_4`, `tauLeaping_level`, `integral_tauFine`, `integral_tauCoarse` | — |
| G8-08 | 2407–2409 / p.56 | "naturally gives a small difference in the Poisson variates when the difference in rates is small" | DONE | `integral_sq_coupledIncr_sub`, `lintegral_sq_coupledIncr_le` | E[(I_a − I_b)²] = \|a−b\| + \|a−b\|² |
| G8-09 | 2409–2410 | "a correction variance which is O(h)" (why the coupled paths stay close) | DONE-DEV | `lintegral_sq_coupledTwoStep_le`, `lintegral_sq_coupledChain_le`, `coupledChain_sq_le`, `variance_coupledChain_le`, `tauLeaping_level_variance`, `variance_tauCorrection_le` | E[(x_T − x^c_T)²] ≤ c·h: per coarse step the mean-square gap grows by (1+O(h))² plus O(h²) (frozen coarse rate), over T/(2h) steps ⇒ O(h). Hypotheses: λ K-Lipschitz AND bounded by Λ (excludes e.g. λ(x) = cx), Lipschitz payoff of the terminal state, h ≤ 1. Documented in README table/module docstring, not in README "Modelling choices" nor `statement-audit.md`. |
| G8-10 | 2410 | "leading to an O(ε⁻²(log ε)²) complexity" | DONE-DEV | `tauLeaping_complexity`, `tauLeaping_mlmc_theorem1` | Theorem 1 for the actual estimator: β = 1, γ = 1 proved (cost 2^ℓ fine steps; coarse path omitted, factor 3/2); weak rate α ≥ ½ is a hypothesis (PLAN "Not formalised", module docstring) |
| G8-11 | implicit | weak order α = 1 of tau-leaping against the exact continuous-time chain | OOS (doc) | — | PLAN "Not formalised: … the weak rate α = 1 against the exact chain … need the continuous-time chain itself". With bounded rates this is formalisable in principle (uniformisation / bounded generator). |
| G8-12 | 2411–2412 | A&H "treat more general systems with multiple reactions" | N/A | — | cited; Lean covers one reaction |
| G8-13 | 2412–2416 | extra coupling to the exact SSA on the finest level ⇒ "overall multilevel estimator is unbiased" | OOS (doc) | — | PLAN "the exact (SSA) coupling on the finest level" |
| G8-14 | 2416–2417 | "complexity is reduced to O(ε⁻²) because the number of levels remains fixed as ε → 0" | DONE-DEV | `fixed_levels_cost` | abstract: fixed finite level set, rounded (1.1) allocation gives Σ V_ℓ/N_ℓ ≤ ε² at cost ≤ cε⁻²; unbiasedness (G8-13) assumed |
| G8-15 | 2417–2420 | "complete numerical analysis of the variance … sharpened in … (Anderson, Higham and Sun 2014)" | N/A | — | cited |
| G8-16 | 2420–2423 | 1000's of reactions; savings > factor 100 | N/A | — | empirical |
| G8-17 | 2424–2427 | approximate model with fewer reactions as a control variate | N/A | (cf. `ControlVariate.lean`) | idea |
| G8-18 | 2428–2441 | Moraes et al.: adaptive switching, variance estimator (kurtosis), negativity control, per-reaction switching, coarse-level control variate, savings 1000× | N/A | — | cited/empirical |
| G8-19 | 2442–2447 | "The non-nested adaptive timestepping approach described in Section 5.6 … is equally applicable … with Poisson variates for each time interval instead of Brownian increments" | MISSING | (cf. `poisson_add_hasLaw`) | The consistency claim (each path's increments over its own steps have the right conditional law, so the telescoping sum is respected) follows from Poisson additivity over a (predictable) partition of each step: deterministic union grid = iterated `poisson_add_hasLaw`; path-dependent steps = conditional-pgf/martingale argument. Medium. PLAN documents Algorithm 3 only for SDEs ("needs Brownian motion at stopping times"); the Poisson version is not mentioned. |
| G8-20 | 2446–2447 | "adaptive timestepping can be very helpful … propensities vary greatly in time" | N/A | — | informal |
| G9.1-01 | 2453–2458 / p.57 | quantity E_Z[f(E_W[g(Z,W)])], W independent inner variable | DONE | `nestedTarget`, `nestedLaw` (ν ⊗ ρ^{⊗ℕ}) | definition |
| G9.1-02 | 2459–2465 | risk scenarios / expected shortfall interpretation | N/A | — | informal |
| G9.1-03 | 2466–2472 | standard nested MC estimator Y = N⁻¹Σ f(M⁻¹Σ g(Z⁽ⁿ⁾,W⁽ᵐ'ⁿ⁾)) | N/A | (`nestedP` = one sample with M = 2^ℓ) | definition |
| G9.1-04 | 2473–2474 | "we need to increase both M and N, and this will significantly increase the cost" | N/A | (cf. `nested_bias_rate`) | informal |
| G9.1-05 | 2475–2482 | "M_ℓ = 2^ℓ inner samples", E[P_ℓ] ≡ E_Z[f(M_ℓ⁻¹Σ g(Z,W⁽ᵐ⁾))] | DONE | `nestedP`, `innerMean` | definition |
| G9.1-06 | 2483–2505 | antithetic Y_ℓ = N_ℓ⁻¹Σ{f(M_ℓ⁻¹Σ g) − ½f(first half) − ½f(second half)} | DONE | `nestedDelta`, `innerMean_two_mul`, `blockMean` | definition matches |
| G9.1-07 | 2506 | "this has the correct expectation, i.e. E[Y_ℓ] = E[P_ℓ − P_{ℓ−1}]" | DONE | `integral_nestedDelta`, `measurePreserving_shiftSeq` | — |
| G9.1-08 | 2507–2518 / p.58 | definitions of Δg₁⁽ⁿ⁾, Δg₂⁽ⁿ⁾ | N/A | — | definition |
| G9.1-09 | 2519–2526 | "if f is twice differentiable a Taylor series expansion gives Y_ℓ ≈ −1/(4N_ℓ) Σ f″(E[g])(Δg₁−Δg₂)²" | DONE (corrected) | `antithetic_quadratic`, `abs_midpoint_sub_avg_le`, `abs_midpoint_sub_avg_le_of_deriv2`, `convexOn_half_sq_sub_add` | PAPER ERROR (typeset p.58 verified): the coefficient is −1/8. Lean: exactly −(K/8)(A−B)² for quadratic f, and ≠ −(K/4)(A−B)² unless K = 0 or A = B; rigorous \|·\| ≤ (K/8)(A−B)². Documented (README, PLAN M5, docstring). |
| G9.1-10 | 2527–2528 | "By the Central Limit Theorem, Δg₁, Δg₂ = O(M_ℓ^{−1/2})" | DONE-DEV | `moments_add_indep`, `moments_sum_indep`, `centred_moments_le`, `fiber_sum_moments`, `fiber_nested_moments` | moment bounds replace the CLT (E[S²] = nσ², E[S⁴] ≤ nκ + 3n²σ⁴); needs E[g⁴] < ∞; documented |
| G9.1-11 | 2528–2537 | "f″(E[g])(Δg₁−Δg₂)² = O(M_ℓ⁻¹)" | DONE | `abs_nestedDelta_le` (+ fibre moments) | \|Y_{ℓ+1}\| ≤ (K/8)(A_M − A'_M)² pointwise |
| G9.1-12 | 2538–2540 | "It follows that E[Y_ℓ] = O(M_ℓ⁻¹) and V_ℓ = O(M_ℓ⁻²)" | DONE-DEV | `nested_mean_rate`, `nested_variance_rate` | 2^ℓ\|E Y_{ℓ+1}\| ≤ (K/4)(1+16E[g⁴]); 4^ℓ E[Y_{ℓ+1}²] ≤ (K/8)²·224·E[g⁴]. Hypotheses: f differentiable with K-Lipschitz f′ (e.g. \|f″\| ≤ K) and E[g(Z,W)⁴] < ∞, instead of "twice differentiable" (documented in `NestedMLMC` docstring only). |
| G9.1-13 | 2540–2541 | "this corresponds to α = 1, β = 2, γ = 1, so the complexity is O(ε⁻²)" | DONE | `nested_bias_rate` (α = 1 for P_ℓ), `nested_mlmc_complexity`, `nested_mlmc_complexity_iid`, `nested_complexity` | end-to-end Theorem 1 for the antithetic nested estimator, every hypothesis derived |
| G9.1-14 | 2542–2549 | developed independently (Haji-Ali, Chen–Liu, Bujok et al.); crowds; plasma | N/A | — | historical |
| G9.1-15 | 2550–2554 | "f was piecewise linear, not twice differentiable, … β = 1.5. However, this is still sufficiently large to achieve … O(ε⁻²)" | PARTIAL | `nested_complexity` (complexityBound 1 1.5 1 = ε⁻²) | Complexity given β = 1.5 is evaluated; the rate β = 1.5 itself is NOT formalised and not documented (README: only "the exponents of §9.1–§9.2"). Formalisable: for piecewise-linear f with kink K the antithetic difference vanishes unless K lies between the half-means, \|Y\| ≤ L\|A−A'\|; with a bounded density of E[g\|Z] near K and moments of g, E[Y²] = O(M^{−3/2}). Medium–hard. |
| G9.1-16 | 2555–2565 | American options (Belomestny, Schoenmakers, Dickmann) as nested simulation | N/A | — | cited |
| G9.2-01 | 2570–2574 / p.59 | g(Z,W) no longer O(1) cost; W a Brownian path approximated with timesteps | N/A | — | setting |
| G9.2-02 | 2574–2576 | "on level ℓ … 2^ℓ timesteps. When using the Milstein discretisation (giving first order weak and strong convergence) this would still give α = 1, β = 2" | MISSING | — | The implication [first-order weak/strong convergence of the inner approximation g_ℓ, as hypotheses] ⇒ [α = 1, β = 2 for Y_ℓ = f(mean_{2M} g_ℓ) − ½f(mean_M g_{ℓ−1}) − ½f(mean'_M g_{ℓ−1})] is not formalised and not documented; the premise (Milstein's orders) is OOS and documented (README l.28–30). Medium (extends `NestedMLMC`). |
| G9.2-03 | 2576–2578 | "we would now have γ = 2, because the work on successive levels would go up by factor 4×" | DONE-DEV | `nested_complexity` (input γ = 2) | cost-model input |
| G9.2-04 | 2578–2579 | "an overall MLMC complexity which is O(ε⁻²(log ε)⁻²)" | DONE (corrected) | `nested_complexity` (complexityBound 1 2 2 = ε⁻²(log ε)²) | PAPER TYPO (typeset p.59 verified): exponent of log ε must be +2 (β = γ). Flagged only in the `nested_complexity` docstring. |
| G9.2-05 | 2580–2621 | MIMC: 2^{ℓ1} inner samples, ~2^{ℓ2} timesteps; the 6-term estimator Y_ℓ (ℓ1, ℓ2 > 0) | N/A | — | definition; not defined in Lean Now defined: `nestedMimcDelta` (`NestedRates.lean`). |
| G9.2-06 | 2622–2637 / p.60 | "Taylor series expansion around E[g(Z⁽ⁿ⁾,W)] … Y_ℓ ≈ −1/(4N_ℓ)Σ f″(E g){(Δg_{1,ℓ2}−Δg_{2,ℓ2})² − (Δg_{1,ℓ2−1}−Δg_{2,ℓ2−1})²}" | PARTIAL | `antithetic_quadratic` (the §9.1 form) | Same factor-2 error (typeset p.60 verified: should be −1/8). Y_ℓ is a difference of two §9.1 antithetic differences, so the correction carries over, but no §9.2 statement exists and README/PLAN mention only one −1/4. Trivial. |
| G9.2-07 | 2638–2659 | "The difference of squares can be re-arranged as ((Δ_{1,ℓ2}+Δ_{1,ℓ2−1}) − (Δ_{2,ℓ2}+Δ_{2,ℓ2−1})) × ((Δ_{1,ℓ2}−Δ_{1,ℓ2−1}) − (Δ_{2,ℓ2}−Δ_{2,ℓ2−1}))" | DONE | `mimc_diff_sq` | — |
| G9.2-08 | 2660–2666 | "Due to the Central Limit Theorem, Δg_{1,ℓ2}+Δg_{1,ℓ2−1} = O(2^{−ℓ1/2}), Δg_{2,ℓ2}+Δg_{2,ℓ2−1} = O(2^{−ℓ1/2})" | MISSING | (hypotheses `ha`, `hb` of `abs_mimc_diff_sq_le_rpow`) | Only assumed. Paper imprecision: with Δ measured from E[g(Z,W)] each sum contains the weak error E[g_{ℓ2}+g_{ℓ2−1}−2g\|Z] = O(2^{−ℓ2}); true after re-centring at E[g_{ℓ2}\|Z], E[g_{ℓ2−1}\|Z] (the difference of squares is invariant under it). |
| G9.2-09 | 2667–2673 | "assuming first order strong convergence … Δg_{1,ℓ2} − Δg_{1,ℓ2−1} = O(2^{−ℓ1/2−ℓ2})" (and for 2) | MISSING | (hypotheses `ha'`, `hb'` of `abs_mimc_diff_sq_le_rpow`) | Only assumed; same imprecision (the conditional mean E[g_{ℓ2}−g_{ℓ2−1}\|Z] = O(2^{−ℓ2}) does not average out; only the difference between the two halves is O(2^{−ℓ1/2−ℓ2})). |
| G9.2-10 | 2674–2683 | "Combining these results … = O(2^{−ℓ1−ℓ2})" | DONE | `abs_mimc_diff_sq_le`, `abs_mimc_diff_sq_le_rpow` | deterministic: \|(a₁−b₁)²−(a₂−b₂)²\| ≤ 4c²2^{−ℓ1−ℓ2} |
| G9.2-11 | 2684–2685 | "therefore E[Y_ℓ] = O(2^{−ℓ1−ℓ2}) and V_ℓ = O(2^{−2ℓ1−2ℓ2}) with a cost per sample … O(2^{ℓ1+ℓ2})" | MISSING | — (cost: input γ = (1,1) of `nested_mimc_complexity`) | Rates not formalised, not documented. Formalisable conditional on L⁴ first-order strong (and weak) convergence of g_{ℓ2}; a rigorous version needs f″ Lipschitz (C³-type): with f″ only bounded, near kinks of f″ one gets V_ℓ ≍ 2^{−1.5ℓ1−2ℓ2}, so "twice differentiable" is not enough. Medium–hard (NestedMLMC-size development + Theorem 2 plumbing). |
| G9.2-12 | 2580, 2685–2686 | "In Theorem 2 this corresponds to α1=α2=1, β1=β2=2, γ1=γ2=1, so the overall complexity is O(ε⁻²)" | PARTIAL | `nested_mimc_complexity` (η = −1 ⇒ mimcBound = ε⁻²), `giles_theorem2_boundary`, `giles_theorem2_full` | evaluation + generic Theorem 2 (α_d = ½β_d allowed); no Theorem 2 instance for the nested MIMC estimator (needs G9.2-11). The readbacks README ("the statements about the estimators are the instances of Theorems 1 and 2 (…, `giles_theorem2_boundary`)") overstates §9.2. Correction (round-15 audit): only the bound is evaluated; no theorem applies Theorem 2 to the smooth nested MIMC estimator (the rate theorems cover ℓ₁, ℓ₂ ≥ 1) Round 16: DONE, end to end (`nested_mimc_smooth_variance_rate`, `nested_mimc_smooth_mean_rate` on all of ℕ², `nested_mimc_smooth_complexity`: MSE < ε² at cost O(ε⁻²) on the simplex index set; `NestedMimcSmooth.lean`). |
| G9.2-13 | 2687–2690 | "if the function f is continuous and piecewise differentiable … MLMC … β = 1.5, and hence … O(ε^{−2.5})" | PARTIAL | `nested_complexity` (complexityBound 1 1.5 2 = ε^{−2.5}) | evaluation done; the rate β = 1.5 (with timesteps) not formalised (see G9.1-15). Round 13: DONE-DEV, `nested_kink_sde_variance_rate`, `nested_kink_sde_mlmc_complexity` (resolution table in README.md) |
| G9.2-14 | 2690–2691 | "with MIMC we would have β1 = β2 = 1.5 and so the complexity would remain O(ε⁻²)" | PARTIAL | `nested_mimc_complexity` (η = −½) | evaluation done; rates not formalised. Round 13: the rates are false, `nested_mimc_kink_rates_false`; round 14: corrected rates and cost `O(ε⁻²|log ε|⁴)`, `NestedMimcKink.lean` (resolution table in README.md) |
| G9.2-15 | 2691–2692 | "This illustrates the benefit of the MIMC approach" | N/A | — | informal |
| G10.1-01 | 2695–2698 / pp.60–61 | Glynn–Rhee apply randomised MLMC to Markov chains / limiting distributions | N/A | — | historical |
| G10.1-02 | 2707–2711 / p.61 | X₀ = x, X_{n+1} = φ_n(X_n), {φ_n} iid random functions on a metric space | DONE-DEV | `fwdIter`, `backIter` | φ_n = φ(·, ξ_n) with jointly measurable φ and iid ξ_n (standard representation; docstring) |
| G10.1-03 | 2711–2716 | "sup_{x≠y} E[(d(φ_n(x),φ_n(y))/d(x,y))^{2γ}] < 1 for some γ ∈ (0,1)" | DONE | hypothesis `hφ` (E[d(φx,φy)^p] ≤ ρ d(x,y)^p, ρ < 1, p = 2γ) | equivalent (ρ = the sup) |
| G10.1-04 | 2716–2718 | "it is known that the distribution of X_n converges weakly to that of a limit random variable X∞" | DONE-DEV | `tendstoInDistribution_fwdIter`, `ae_tendsto_backIter`, `map_backIter_eq_map_fwdIter` | adds a complete separable (Borel) metric space and E[d(x₀,φ(x₀,ξ))^p] < ∞; documented in `MarkovLimit` docstring only |
| G10.1-05 | 2718–2719 | objective E[f(X∞)], f γ-Hölder: \|f(y)−f(x)\| ≤ d(x,y)^γ | DONE | hypothesis `hf` of `variance_levels_le` | setting |
| G10.1-06 | 2720–2723 | example X₀ = 0, X_{n+1} = ½X_n + ξ_n, P(ξ=0)=P(ξ=1)=½, "satisfying the required conditions" | DONE | `halfStep`, `fairCoin`, `lintegral_dist_halfStep`, `half_rpow_lt_one` | ρ = 2^{−2γ} |
| G10.1-07 | 2724–2725 | "The invariant distribution in this case is the uniform distribution on [0,2]" | PARTIAL | `halfStep_invariant`, `map_halfStep` | Invariance of U[0,2] proved; uniqueness ("the") and that the limit X∞ of G10.1-04 has law U[0,2] are not stated (readback `markov_limit.md` notes stationarity of the limit is not stated). Formalisable: couple a stationary start with x₀ (same noises), d → 0 in L^p; or X∞ = Σ_k 2^{−k}ξ_k. Moderate. |
| G10.1-08 | 2726–2728 | "one would approximate E[f(X∞)] by estimating E[f(X_N)] … but this would be a biased estimate" | N/A | — | informal; no bias-size statement (see G10.1-10) The bias size is now `abs_integral_sub_limit_le` (`MarkovLimitLaw.lean`). |
| G10.1-09 | 2728–2730 | "starting a level ℓ simulation at n = −N_ℓ and terminating it at n = 0" (Fig. 10.12) | DONE | `backIter`, `map_backIter_eq_map_fwdIter` (level-ℓ sample has the law of X_{N_ℓ}) | — |
| G10.1-10 | 2728–2729 | "Glynn and Rhee (2014) circumvent this problem [the bias] by making N increase with level" | PARTIAL | `variance_levels_le` (+ generic `giles_theorem1`, `randomised_mlmc_finite`) | Missing: (a) the level bias \|E f(X^{(ℓ)}) − E f(X∞)\| ≤ Cρ^{N_ℓ/2} (needs L^{2γ} convergence of `backIter` to X∞ — weak convergence does not handle unbounded Hölder f); (b) the end-to-end (randomised) MLMC statement that the estimator of E[f(X∞)] is unbiased with finite variance/cost. Low–moderate with existing pieces; not documented. |
| G10.1-11 | 2730–2732 | "levels terminate at the same time is crucial … share the same random φ_n for n ≥ −N_{ℓ−1}" | DONE | `backIter_add` | — |
| G10.1-12 | 2733–2734 | "the effect of the initial evolution of the level ℓ path for n < −N_{ℓ−1} decays exponentially" | DONE | `lintegral_dist_backIter_le`, `lintegral_dist_start_le`, `lintegral_dist_levels_le` | E[d^{2γ}] ≤ ρ^{N_{ℓ−1}}·4c/(1−ρ)² |
| G10.1-13 | 2734–2735 | "a multilevel correction variance which decays as ℓ increases" | DONE | `variance_levels_le` | V ≤ 4c/(1−ρ)²·ρ^{N_{ℓ−1}} |
| G10.1-14 | 2735–2736 | "Because the decay is exponential in N_ℓ − N_{ℓ−1}" | DONE (corrected) | `variance_levels_le` | PAPER SLIP: decay is exponential in N_{ℓ−1} (shared steps); documented in `MarkovChain` docstring |
| G10.1-15 | 2736–2737 | "it is appropriate to choose N_ℓ to increase linearly with level" | PARTIAL | `variance_levels_le` | the consequence (N_ℓ = aℓ ⇒ V_ℓ = O(2^{−βℓ}), β = a·log₂(1/ρ), C_ℓ = O(ℓ)) is a one-line corollary, not stated. Trivial. |
| G10.1-16 | 2738–2743 | contracting SDEs: level ℓ simulates [−T_ℓ,0] with step h_ℓ, shared Brownian path on [−T_{ℓ−1},0], "the contraction property will ensure that the multilevel variance decays with level" | OOS (generic) | — | needs SDE strong convergence + contraction; only the generic SDE exclusion (README l.28–30, PLAN "Out of scope") covers it |
| G10.2-01 | 2748–2751 / p.62 | "8 single precision or 4 double precision operations … single precision … twice as fast" | N/A | — | hardware |
| G10.2-02 | 2752–2756 | single precision on level 0, double on level 1; "Estimating V0 and V1 as defined in Section 1.2 will automatically lead to the optimal allocation" | DONE-DEV | `twoLevel_optimal_ratio`, `optimal_variance_isLeast`, `optimal_cost_isLeast` | generic §1.2/§1.3 allocation, applied to precision levels |
| G10.2-03 | 2757–2762 | Brugger et al.: FPGA, number of bits increasing with level | N/A | — | description (HG25 bit-width modules are a different paper) |
| G10.2-04 | 2763–2770 | "full precision in the generation of the random numbers … This ensures that the Brownian increments computed for the coarser path ℓ−1 by summing the increments of the finer path ℓ, are consistent with … level ℓ−1 when it is the finer" | DONE-DEV | `measurePreserving_pairAvg`, `emCoarse_eq`, `integral_emCoarse`, `integral_fineCoarseDiff` | (2.4) holds for any functional of the summed full-precision increments, hence for any reduced-precision path arithmetic; no explicit precision model. PLAN lists "the floating-point remark of §10.2" as not formalised. |
| G10.2-05 | 2771–2774 | "This would not be the case if the increments on level ℓ were generated with B_ℓ bits … then summed …, regardless of whether the truncation … took place before or after the summation" | OOS (doc, vague) | — | PLAN "the floating-point remark of §10.2" (vague). Formalisable in principle as a counterexample with a rounding model (e.g. `roundFixed`): law of round_{B_{ℓ−1}}(round_{B_ℓ}X₁ + round_{B_ℓ}X₂) ≠ law of round_{B_{ℓ−1}}X, X ~ N(0,2h). |
| G10.2-06 | 2774–2781 | I_n → U_n → Z_n, "I_n is a random integer on a range [0, I_max], U_n = (I_n+½)/I_max is … approximately uniformly-distributed … on (0,1)", Z_n = Φ⁻¹(U_n) | N/A | (cf. HG25 `midpoint_mem_cell`, `coupledUniform_mem`) | construction. PAPER SLIP (p.62 verified): for I_n = I_max, U_n = 1 + 1/(2I_max) > 1 (Φ⁻¹ undefined); needs I_n ∈ [0, I_max−1] or division by I_max+1. HG25's formalised analogue uses J ∈ [0, 2^D−1]. |
| G10.2-07 | 2781–2788 | Brownian-Bridge construction: I_n generated identically on each level ⇒ "The Brownian path being generated for level ℓ is then exactly the same, regardless of whether it is the finer or coarser … Hence, the telescoping sum will be respected" | MISSING | (cf. `bridgeInterp_midpoint`) | Formalisable: in the hierarchical Brownian-bridge construction the level-ℓ path is a function of the first 2^ℓ inputs only, so both roles compute the identical level-ℓ path and (2.4) holds pathwise. Low–moderate. Not clearly documented (possibly intended by PLAN's vague "floating-point remark of §10.2"). |
| G11-01 | 2793–2800 / p.63 | key theoretical extensions: randomised estimators, Richardson–Romberg, MIMC | N/A | (§2 modules) | summary |
| G11-02 | 2800–2805 | range of applications; progress on variance analysis and MLQMC | N/A | — | summary |
| G11-03 | 2806–2809 | "in essence it is simply a recursive control variate strategy" | N/A | (cf. `ControlVariate.lean`) | conceptual |
| G11-04 | 2810–2812 | challenge: tight coupling to minimise the variance of the difference | N/A | — | informal |
| G11-05 | 2812–2818 | discontinuous outputs; three smoothing treatments (conditional expectation, splitting, change of measure) | N/A | (§5.3 results in `SDEExtras`) | summary of §5 |
| G11-06 | 2819–2821 | "antithetic variates can be used to improve the variance … without improving the strong convergence" | N/A | (`measurePreserving_swapIncrements`, `variance_antithetic_le`) | summary of §5.4 |
| G11-07 | 2822–2849 / pp.63–64 | future directions (MLQMC algorithms, MIMC applications, sensitivity analysis, LHS/importance sampling, nested simulation / mean field games) | N/A | — | outlook |
| G11-08 | 2850–2858 | MATLAB codes; community web page | N/A | — | informal |

## Paper errors and imprecisions in the range

Handled correctly by the Lean code:
* §9.1 p.58: −1/(4N_ℓ) should be −1/(8N_ℓ) (`antithetic_quadratic`). The same error recurs in §9.2
  p.60 (G9.2-06); it is not separately flagged.
* §9.2 p.59: O(ε⁻²(log ε)⁻²) should be O(ε⁻²(log ε)²) (`nested_complexity` docstring).
* §10.1 p.61: the decay is exponential in N_{ℓ−1}, not N_ℓ − N_{ℓ−1} (`MarkovChain` docstring).

Not flagged anywhere in the repo (round-10 state; all four are now in the corrections table of
`notes/statement-audit.md` and in the module docstrings):
* §7.1 p.49: "a constant K such that |P − P_ℓ| < K h_ℓ²" is false for the paper's example
  (error ∝ Z², Z Gaussian); `elliptic_rates` formalises the literal claim, so its hypothesis cannot
  hold for the example; the random-K/L² version is only available through generic lemmas.
* §7.3 p.54: "√h Z_n" should be "√k Z_n".
* §9.2 p.60: the four intermediate O(·) claims hold only after re-centring (or for the difference of
  the two halves); a rigorous V_ℓ = O(2^{−2ℓ1−2ℓ2}) needs f″ Lipschitz, not just f twice
  differentiable.
* §10.2 p.62: U_n = (I_n + ½)/I_max exceeds 1 for I_n = I_max.

## Lean misstatements

None found: every cited statement says what the paper says, or states a documented special case
or corrected version of it.

## Documentation gaps

(Round-10 state; `notes/statement-audit.md` has covered §7–§11 since round 10.)

* `notes/statement-audit.md` has no entry for §7–§11, although README l.35–36 says every deviation
  is recorded there. The §8 (bounded + Lipschitz propensity), §9 (K-Lipschitz f′, E[g⁴] < ∞) and
  §10.1 (complete separable space, first-step moment) deviations appear only in module docstrings,
  the README table and the readbacks. None of them is listed in README "Modelling choices".
* PLAN "Not formalised" ends with "the remaining claims are numerical or empirical". For §7–§10
  that is not accurate: see the MISSING and PARTIAL rows.
* PLAN's "the floating-point remark of §10.2" is too vague to tell which §10.2 claims it covers.
