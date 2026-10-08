-- Multilevel Monte Carlo complexity theorems in Lean 4 / Mathlib.
--
-- * `MlmcLean.Allocation`  — optimal sample allocation (Giles (1.1), Haas–Giles (8), (12))
-- * `MlmcLean.Estimator`   — mean / variance / MSE of the multilevel estimator (Giles (2.1)–(2.3))
-- * `MlmcLean.LevelDiff`   — the level differences `P_ℓ − P_{ℓ−1}` and the telescoping sum (2.2)
-- * `MlmcLean.Complexity`  — Giles' Theorem 1, deterministic core, three regimes
-- * `MlmcLean.Theorem1`    — Giles' Theorem 1 on a probability space (random cost, big-O forms)
-- * `MlmcLean.StandardEstimator` — the estimator (2.2) from independent samples; Theorem 1 for it
-- * `MlmcLean.SampleMean`  — sample means over independent blocks of inputs
-- * `MlmcLean.Randomised` — randomised single-term MLMC (Giles §2.2, Rhee–Glynn)
-- * `MlmcLean.MultiIndex`  — multi-indices, cross-differences, box telescoping (Giles §2.4)
-- * `MlmcLean.Lattice`     — lattice sums over the MIMC index sets `{θ·ℓ ≤ L}`
-- * `MlmcLean.Theorem2`    — Giles' Theorem 2 (Multi-Index Monte Carlo)
-- * `MlmcLean.Nested`      — Haas–Giles nested MLMC estimator (9)–(12)
-- * `MlmcLean.ControlVariate` — Giles §1.1–§1.3: plain MC, control variates, the cost (1.1)
-- * `MlmcLean.ErrorAnalysis` — Giles §2.1, §3.1, §3.3: MSE budget, weak rate, convergence test
-- * `MlmcLean.LevelDropping` — Giles §2.6: non-geometric MLMC, the cost of a subset of the levels
--   and the exhaustive search, the level-dropping test (2.5)
-- * `MlmcLean.Corrections` — Giles §2.1: (2.4) and antithetic estimators, Theorem 1 for them
-- * `MlmcLean.Richardson` — Giles §2.3: Richardson extrapolation, ML2R weights, bias, estimator
-- * `MlmcLean.MultiOutput` — Giles §2.5: several outputs, Hilbert-space outputs, Theorem 1
-- * `MlmcLean.RoundingError` — Haas–Giles §4: fixed-point rounding, the error-variance model
-- * `MlmcLean.BitWidth` — Haas–Giles §5–§6: the cost model, the bit-width optimisation
-- * `MlmcLean.GeometricRates` — Giles §2.1: allocation under geometric rates, the case β = 2α
-- * `MlmcLean.RectangularMIMC` — Giles §2.4: MIMC on a rectangular index set (η < 0, ∑ γ/α ≤ 2)
-- * `MlmcLean.Algorithm` — Giles §3.1: Algorithm 1 (robust test, termination, MSE, cost)
-- * `MlmcLean.ApproxNormal` — Haas–Giles §3: approximate normals, (14)–(19), the coupling (17)
-- * `MlmcLean.CostComparison` — Giles §1.3, §2.1–§2.2: standard MC cost, the MLMC saving, the MSE
--   split, the randomised estimator's half cost
-- * `MlmcLean.NestedSimulation` — Giles §9: nested simulation, the antithetic difference, moment
--   bounds, the exponents of §9.1–§9.2
-- * `MlmcLean.NestedMLMC` — Giles §9.1: the nested MLMC estimator, its expectation, the rates
--   α = 1, β = 2 and the complexity O(ε⁻²)
-- * `MlmcLean.EulerMaruyama` — Haas–Giles (2), (4)–(5), Giles §5.1: the Euler–Maruyama fine/coarse
--   coupling, (2.4), Theorem 1 for it, the variance rate from the strong rate
-- * `MlmcLean.Implementation` — Giles §3.3–§3.5: the driver's variance estimate, floors and
--   regression, the probability that the consistency check fails, the MLQMC rule (3.3)
-- * `MlmcLean.PoissonCoupling` — Giles §8: tau-leaping, the Anderson–Higham Poisson coupling, its
--   marginals and (2.4), the moments of the coupled difference, the correction variance O(h)
--   (β = 1) for Lipschitz propensities, the complexity statements
-- * `MlmcLean.LagrangeBitWidth` — Haas–Giles §4.3, §6: (34) against (33), the Lagrange conditions
--   (35) (sufficient and necessary) and (37), the ratio (38), the trends of §6.3, the LUT size
-- * `MlmcLean.FixedPointPath` — Haas–Giles §4.1, §6.3: Algorithm 1 (the GBM path), the sizes
--   (39)–(41) of its variables, the accumulation of rounding errors
-- * `MlmcLean.ML2RComplexity` — Giles §2.3: uniform bounds on the ML2R weights, the number of
--   levels, the costs O(ε⁻²|log ε|) (β = γ) and O(ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}) (β < γ)
-- * `MlmcLean.MarkovChain` — Giles §10.1: Markov chains started in the past, the contraction of
--   the coupled chains, the variance decay V_ℓ ≤ C ρ^{N_{ℓ−1}}, the example X_{n+1} = X_n/2 + ξ_n
--   and its uniform invariant law
-- * `MlmcLean.PDEExamples` — Giles §7.1: pathwise errors give α and β = 2α, the discrete maximum
--   principle and the stability condition k/h² ≤ ½, the cost factor 8 (γ = 3), Euler–Maruyama =
--   Milstein for additive noise
-- * `MlmcLean.SDEExtras` — Giles §5: the rates from the timestep, the kurtosis scale, conditional
--   expectations and (2.4), the Brownian-bridge midpoint, the antithetic swap and variance, the
--   stability of the explicit step for mean reversion, the smoothed CDF and the density
--   as a limit, splitting
-- * `MlmcLean.MLQMC` — Giles §3.5: Algorithm 2 (MLQMC) with exact variances, the greedy doubling
--   (3.3) terminates, the variance target (3.2) and the MSE at exit
-- * `MlmcLean.LUTLimits` — Haas–Giles §3.4: the MSE of the lookup tables as d → ∞ (uniform
--   intervals: → 0 for monotone f; dyadic intervals: bounded away from 0)
-- * `MlmcLean.MarkovLimit` — Giles §10.1: the chain started in the past converges almost surely
--   and the distribution of X_n converges weakly to that of X_∞
-- * `MlmcLean.TauLeapingMLMC` — Giles §8: Theorem 1 for tau-leaping MLMC with the Poisson
--   coupling (square-integrable payoffs, (2.4), β = 1 on every level, MSE and cost)
-- * `MlmcLean.GBMEulerMaruyama` — Giles §5.1: the Euler–Maruyama MLMC estimator for geometric
--   Brownian motion end to end (strong error O(h), α = ½, β = 1, Theorem 1 with no
--   assumed rate)
-- * `MlmcLean.GBMMilstein` — Giles §5.2: the Milstein MLMC estimator for geometric Brownian
--   motion end to end (strong error O(h²) in mean square, α = 1, β = 2, Theorem 1 with
--   cost O(ε⁻²) and no assumed rate)
-- * `MlmcLean.ML2RTheorem` — Giles §2.3: the ML2R estimator end to end (sharp weight bound,
--   bias O(2^{−αL(L+1)/2}) uniformly in L from the weak-error expansion, MSE < ε² at cost
--   O(ε⁻²|log ε|) for β = γ and O(ε⁻²2^{(γ−β)√(2 log₂(1/ε)/α)}) for β < γ)
-- * `MlmcLean.GilesRemarks` — Giles §2.2, §2.6, §5.2, §10.1: the randomised variance within
--   (1 + δ) of Σ V_ℓ/p_ℓ, the combined variance and cost of two kept levels, splitting to
--   leading order, N_ℓ linear in ℓ for Markov chains
-- * `MlmcLean.RandomShiftQMC` — Giles §3.5: a random shift makes a QMC rule unbiased; independent
--   shifts give i.i.d. replicates whose average has variance V₁/R, estimated without bias
-- * `MlmcLean.AsymptoticNormal` — Giles §2.1 (Collier et al.) and Haas–Giles §3.2: each level
--   estimator and, for a fixed number of levels, the MLMC estimator are asymptotically normal
--   (Mathlib's CLT, Lévy's continuity theorem); sums of independent N(0, 1/n) are N(0, 1)
-- * `MlmcLean.PoissonGrids` — Giles §8 (with §5.6) and §10.2: Poisson counts summed over the
--   steps of each path on a union grid have the right laws, so (2.4) holds, also for
--   tau-leaping on non-nested deterministic grids; rounding increments breaks (2.4)
-- * `MlmcLean.HaasGilesRemarks` — Haas–Giles §6: the cost factor of Fig. 3 and 5 and when the
--   nested estimator is cheaper, two-sided sizes of the path variables (39)–(41), and the
--   rounding error with fixed precision (exact variance, lower bound, beats discretisation)
-- * `MlmcLean.SDEMisc` — Giles §5.3, §5.6, §5.7: the antithetic bound for smooth payoffs in d
--   dimensions and for the call option, explicit versus tamed Euler steps for super-linear
--   drift, the smoothed CDF for any bounded smoother, the density of a d-dimensional output
-- * `MlmcLean.SDEDigital` — Giles §5.1–§5.4: Lipschitz payoffs, the digital-option variance from
--   the strong error (O(h^{1/3}), sharp; β = 1/3 for GBM with no assumption), smoothing by
--   conditional expectation (Φ formulas, (2.4), V₀ = 0), change of measure, the call derivative
-- * `MlmcLean.ApplicationExtras` — Giles §6.2, §7.1, §7.3, §10.2: summed Lévy increments keep
--   the law ((2.4)), exponential periods, FE = FD, random-K elliptic rates (no deterministic K
--   exists), the SPDE Milstein scheme, the Brownian-bridge and variable-precision paths
-- * `MlmcLean.MarkovLimitLaw` — Giles §10.1: the level bias decays geometrically, the invariant
--   law exists and is unique (U[0, 2] in the example), Glynn–Rhee's randomised estimator of
--   E[f(X_∞)] is unbiased with finite variance and cost, and MLMC reaches it at cost O(ε⁻²)
-- * `MlmcLean.NestedRates` — Giles §9.1–§9.2: the MIMC Taylor expansion (coefficient −1/8),
--   MLMC with discretised inner paths (α = 1, β = γ = 2, cost O(ε⁻²(log ε)²)), a piecewise
--   linear f (β = 3/2, cost O(ε⁻²)), and the nested MIMC rates O(2^{−ℓ₁−ℓ₂}), O(2^{−2ℓ₁−2ℓ₂})
-- * `MlmcLean.MLMCCentralLimit` — Giles §2.1: the Lindeberg and Lyapunov central limit theorems
--   for triangular arrays, asymptotic normality of the MLMC estimator with a growing number of
--   levels, and the confidence intervals of Collier et al. (around E[P_L] and around E[P])
-- * `MlmcLean.QMC1D` — Giles §2.7, §3.5 in one dimension: QMC error O(N⁻¹) for integrands of
--   bounded variation, randomly shifted rank-1 lattices (unbiased, variance O(N⁻²), replicates),
--   and the MLQMC cost O(ε^{−p}) with p < 2
-- * `MlmcLean.ConsistencyCheck` — Giles §3.3: the consistency check with empirical variances
--   fails with asymptotic probability at most P(|Z| ≥ 3) < 0.3% (strong law, two-sample CLT,
--   Slutsky); the bound is attained, and fails for small samples
-- * `MlmcLean.NestedKinkSde` — Giles §9.2: nested simulation with a piecewise linear f and
--   discretised inner paths: α = 1, β = 3/2, cost O(ε^{−5/2}); the paper's MIMC rates
--   β₁ = β₂ = 1.5 for this case are false (explicit counterexample)
-- * `MlmcLean.MLMCConfidenceEstimated` — Giles §2.1: Collier et al.'s confidence intervals with
--   estimated variances, for a fixed and for a growing number of levels (strong law, kurtosis
--   bound, Slutsky), around E[P_L] and E[P], and the tolerance test
-- * `MlmcLean.NestedMimcKink` — Giles §9.2: the corrected MIMC rates for a piecewise linear f,
--   V = O(2^{−ℓ₁−ℓ₂}) (sharp) and |E[Y]| = O(2^{−ℓ₁/2−ℓ₂}), and the cost O(ε⁻²|log ε|⁴) from
--   Theorem 2, still below MLMC's O(ε^{−5/2})
-- * `MlmcLean.LUTAsymptotics` — Haas–Giles §3.4: the MSE of the dyadic lookup tables converges
--   to a constant C > 0, and the MSE of the uniform tables is of order 2^{−d}/d
-- * `MlmcLean.EulerSuperlinear` — Giles §5.6: for dS = −S³dt + dW the explicit Euler–Maruyama
--   scheme has E|X_N|^p → ∞ as the timestep → 0 (Hutzenthaler–Jentzen–Kloeden); the tamed scheme
--   has E X_N² ≤ x₀² + T uniformly in N
-- * `MlmcLean.MLQMCBoundary` — Giles §2.7, §3.5 in one dimension: the MLQMC cost in the boundary
--   case b = g ≤ a is Θ(ε⁻¹|log ε|^{3/2}) (upper and lower bounds), and g < 2a is necessary
-- * `MlmcLean.NestedMimcSmooth` — Giles §9.2: nested MIMC with a smooth payoff end to end:
--   E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂}), V_ℓ = O(2^{−2ℓ₁−2ℓ₂}) on all of ℕ², and MSE < ε² at cost O(ε⁻²)
-- * `MlmcLean.BitWidthOptimum` — Haas–Giles §6.1: an optimal (relaxed) bit-width configuration
--   exists without convexity, satisfies (35)–(36), and beats every uniform bit-width; convexity
--   and uniqueness without additions
-- * `MlmcLean.EllipticFD` — Giles §7.1: the exact finite-difference solution of the 1-D elliptic
--   example, |P − P_ℓ| ≤ (50/3) Z² h_ℓ² with a random constant, and α = 2, β = 4 end to end
-- * `MlmcLean.GilesCorollaries` — contracting SDEs with a fixed step (§10.1), the lookup-table
--   streams tend to N(0, 1) (HG25 §3.2), plain MC complexities (§5.5), β ≤ 2α (§2.1), the D = 1
--   necessity (§2.4), Euler–Maruyama with refinement factor M (§5.1)
-- * `MlmcLean.GBMPathDependent` — Giles §5.1–§5.2, Table 5.2: discretely monitored Asian and
--   lookback options for GBM with Euler–Maruyama (β = 1) and Milstein (β = 2), Theorem 1 end to end
-- * `MlmcLean.SPDEStability` — Giles §7.3: mean-square von Neumann stability of the SPDE scheme,
--   λ(1 + 2ρ²) ≤ 1, instability otherwise, hence k_ℓ = k_{ℓ−1}/4 and the cost factor 8
-- * `MlmcLean.DriftImplicit` — Giles §5.6: the drift-implicit Euler step is well posed and its
--   moments stay bounded for every step size; the deterministic analogue; the integrating factor
-- * `MlmcLean.BrownianPaths` — Giles §5.2, §5.3, §5.6: Brownian paths on union grids
--   (Algorithm 3), the Brownian-bridge midpoint law, time reversal within coarse steps
-- * `MlmcLean.GBMDigital` — Giles §5.1–§5.2: the Milstein digital variance for GBM, fourth moments
--   of the digital correction, the sharp mismatch exponent, and E[Pc] = E[Pf] for the smoothed digital
-- * `MlmcLean.TauLeapingExact` — Giles §8: the exact chain by uniformisation, its master equations,
--   weak order 1 of tau-leaping against it for bounded payoffs, MLMC with the exact-chain target
-- * `MlmcLean.InverseNormal` — Haas–Giles §3: the normal CDF Φ and Φ⁻¹, its derivatives and
--   concavity, and the lookup-table results for f = Φ⁻¹ without hypotheses on f
-- * `MlmcLean.EndToEndInstances` — the elliptic estimator, the discounted call, GBM with refinement
--   factor M end to end; tamed fourth moments; the method-2 iteration exists; rounded increments
-- * `MlmcLean.JumpProcesses` — Giles §6: a discrete exponential-Lévy analogue of Table 6.3's Asian
--   row (β = 2), jump-adapted grids with random jump times satisfy (2.4), the thinning likelihood ratio
-- * `MlmcLean.EstimatorRemarks` — Giles §2.1, §3.3: the CLT counterexample for a growing number of
--   levels, the consistency check with one and two samples, the variance of the sample variance
-- * `MlmcLean.SDEExtensions` — drift-implicit Euler with multiplicative noise (§5.6), the time-reversed
--   path is a Brownian motion with the same running maximum (§5.3), payoffs with several kinks (§9.1)
-- * `MlmcLean.ContractingLevels` — Giles §10.1: contracting SDEs with level-dependent steps and
--   horizons, the multilevel variance decays, MLMC for the limit of the discretised chains
-- * `MlmcLean.AdaptiveGrids` — Giles §5.6, §8: path-dependent (adaptive) steps on a fixed base grid,
--   conditional laws of the increments, (2.4) and Theorem 1 for non-nested grids, Algorithm 3
-- * `MlmcLean.LatticeRuleD` — Giles §2.7, §3.5: randomly shifted rank-1 lattice rules in d
--   dimensions (variance as a dual-lattice sum) and MLQMC complexity with level-dependent dimension
-- * `MlmcLean.Theorem1Log` — Theorem 1 with costs C_ℓ ≤ c₃(ℓ+1)^κ 2^{γℓ}, sharp polylogarithmic
--   bounds, and the contracting SDEs of §10.1 at cost O(ε⁻²|log ε|³)
-- * `MlmcLean.GBMStrongLp` — Giles §5.1–§5.2: strong errors of Euler–Maruyama and Milstein for GBM in
--   every L^{2m}, and the digital option's V_ℓ and fourth moment at every rate below the paper's
-- * `MlmcLean.GBMWeakOrder` — Giles §5.1: weak order 1 of Euler–Maruyama for GBM (polynomial and
--   smooth payoffs, refinement factor M), and Theorem 1 with α = 1, resp. α = log₂ M
-- * `MlmcLean.GBMGridMax` — Giles §5.1–§5.2: the GBM Euler–Maruyama error uniformly over the grid,
--   and the lookback option monitored at every time step, Theorem 1 end to end
-- * `MlmcLean.EulerSuperlinearGeneral` — Giles §5.6: explicit Euler moments diverge for every
--   super-linearly growing drift (Hutzenthaler–Jentzen–Kloeden), with examples
-- * `MlmcLean.GBMDigitalTheorem1` — Giles §5.1–§5.2: the digital option for GBM end to end, barrier
--   options at fixed monitoring dates, splitting with a Milstein final step
-- * `MlmcLean.SpotCheckRemarks` — small results from the spot-check after round 21 (ML2R rate,
--   smoothed CDF, Dirichlet heat scheme, nested inputs, nested MC cost, OU chain, Φ⁻¹ inputs)
-- * `MlmcLean.ParabolicExample` — Giles §7.1: the parabolic example with one scalar Brownian motion,
--   α = 2, β = 4 and Theorem 1 at cost O(ε⁻²) for the limit of the level means
-- * `MlmcLean.NestedKinkCurved` — Giles §9.2: nested simulation with inner time steps for payoffs with
--   several kinks and curved pieces; MIMC on the two axes for the kink counterexample
-- * `MlmcLean.TauLeapingExtensions` — Giles §8: tau-leaping's weak rate for Lipschitz payoffs, and
--   state-dependent rates on adaptive grids with (2.4)
-- * `MlmcLean.GBMDigitalCondExp` — Giles §5.2: the conditional-expectation estimator of the digital
--   option for GBM, V_ℓ = O(h^q) for q < 3/2, Theorem 1 at cost O(ε⁻²); splitting
-- * `MlmcLean.TauLeapingSSA` — Giles §8: tau-leaping coupled with the exact SSA on the finest level,
--   an unbiased multilevel estimator at cost O(ε⁻²) with a fixed number of levels
-- * `MlmcLean.KarhunenLoeve` — Giles §7.2: the truncated Karhunen–Loève field with Mercer's
--   expansion as hypotheses: truncation error, pointwise law, moments, covariance
-- * `MlmcLean.ChangeOfMeasureVariance` — Giles §5.2: when the change-of-measure correction has
--   finite variance (sampling variance more than half the target variances)
-- * `MlmcLean.LevyTruncation` — Giles §6.2: truncation of the small jumps of a Lévy process with
--   level-dependent cutoffs; coupling, (2.4), the correction variance, the L² limit, Theorem 1
-- * `MlmcLean.KarhunenLoeveLimit` — Giles §7.2: the untruncated Karhunen–Loève field, its Gaussian
--   law and covariance, and the moments of the untruncated diffusivity
-- * `MlmcLean.GBMSensitivities` — Giles §5.4: pathwise deltas for GBM; the call delta behaves like a
--   digital option; the digital delta via the conditional expectation
import MlmcLean.Allocation
import MlmcLean.Estimator
import MlmcLean.LevelDiff
import MlmcLean.Complexity
import MlmcLean.Theorem1
import MlmcLean.StandardEstimator
import MlmcLean.SampleMean
import MlmcLean.Randomised
import MlmcLean.MultiIndex
import MlmcLean.Lattice
import MlmcLean.Theorem2
import MlmcLean.Nested
import MlmcLean.ControlVariate
import MlmcLean.ErrorAnalysis
import MlmcLean.LevelDropping
import MlmcLean.Corrections
import MlmcLean.Richardson
import MlmcLean.MultiOutput
import MlmcLean.RoundingError
import MlmcLean.BitWidth
import MlmcLean.GeometricRates
import MlmcLean.RectangularMIMC
import MlmcLean.Algorithm
import MlmcLean.ApproxNormal
import MlmcLean.CostComparison
import MlmcLean.NestedSimulation
import MlmcLean.NestedMLMC
import MlmcLean.EulerMaruyama
import MlmcLean.Implementation
import MlmcLean.PoissonCoupling
import MlmcLean.LagrangeBitWidth
import MlmcLean.FixedPointPath
import MlmcLean.ML2RComplexity
import MlmcLean.MarkovChain
import MlmcLean.PDEExamples
import MlmcLean.SDEExtras
import MlmcLean.MLQMC
import MlmcLean.LUTLimits
import MlmcLean.MarkovLimit
import MlmcLean.TauLeapingMLMC
import MlmcLean.GBMEulerMaruyama
import MlmcLean.GBMMilstein
import MlmcLean.ML2RTheorem
import MlmcLean.GilesRemarks
import MlmcLean.RandomShiftQMC
import MlmcLean.AsymptoticNormal
import MlmcLean.PoissonGrids
import MlmcLean.HaasGilesRemarks
import MlmcLean.SDEMisc
import MlmcLean.SDEDigital
import MlmcLean.ApplicationExtras
import MlmcLean.MarkovLimitLaw
import MlmcLean.NestedRates
import MlmcLean.MLMCCentralLimit
import MlmcLean.QMC1D
import MlmcLean.ConsistencyCheck
import MlmcLean.NestedKinkSde
import MlmcLean.MLMCConfidenceEstimated
import MlmcLean.NestedMimcKink
import MlmcLean.LUTAsymptotics
import MlmcLean.EulerSuperlinear
import MlmcLean.MLQMCBoundary
import MlmcLean.NestedMimcSmooth
import MlmcLean.BitWidthOptimum
import MlmcLean.EllipticFD
import MlmcLean.GilesCorollaries
import MlmcLean.GBMPathDependent
import MlmcLean.SPDEStability
import MlmcLean.DriftImplicit
import MlmcLean.BrownianPaths
import MlmcLean.GBMDigital
import MlmcLean.TauLeapingExact
import MlmcLean.InverseNormal
import MlmcLean.EndToEndInstances
import MlmcLean.JumpProcesses
import MlmcLean.EstimatorRemarks
import MlmcLean.SDEExtensions
import MlmcLean.ContractingLevels
import MlmcLean.AdaptiveGrids
import MlmcLean.LatticeRuleD
import MlmcLean.Theorem1Log
import MlmcLean.GBMStrongLp
import MlmcLean.GBMWeakOrder
import MlmcLean.GBMGridMax
import MlmcLean.EulerSuperlinearGeneral
import MlmcLean.GBMDigitalTheorem1
import MlmcLean.SpotCheckRemarks
import MlmcLean.ParabolicExample
import MlmcLean.NestedKinkCurved
import MlmcLean.TauLeapingExtensions
import MlmcLean.GBMDigitalCondExp
import MlmcLean.TauLeapingSSA
import MlmcLean.KarhunenLoeve
import MlmcLean.ChangeOfMeasureVariance
import MlmcLean.LevyTruncation
import MlmcLean.KarhunenLoeveLimit
import MlmcLean.GBMSensitivities
