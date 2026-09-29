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
