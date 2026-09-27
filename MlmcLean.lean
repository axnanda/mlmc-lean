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
-- * `MlmcLean.LevelDropping` — Giles §2.6: non-geometric MLMC, the level-dropping test (2.5)
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
--   marginals and (2.4), the moments of the coupled difference, the complexity statements
-- * `MlmcLean.LagrangeBitWidth` — Haas–Giles §4.3, §6: (34) against (33), the Lagrange conditions
--   (35) (sufficient and necessary) and (37), the ratio (38), the trends of §6.3, the LUT size
-- * `MlmcLean.FixedPointPath` — Haas–Giles §4.1, §6.3: Algorithm 1 (the GBM path), the sizes
--   (39)–(41) of its variables, the accumulation of rounding errors
-- * `MlmcLean.ML2RComplexity` — Giles §2.3: uniform bounds on the ML2R weights, the number of
--   levels, the costs O(ε⁻²|log ε|) (β = γ) and O(ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}) (β < γ)
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
