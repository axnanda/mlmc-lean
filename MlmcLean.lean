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
-- * `MlmcLean.ControlVariate` — Giles §1.1–§1.3: plain Monte Carlo, control variates, the cost (1.1)
-- * `MlmcLean.ErrorAnalysis` — Giles §2.1, §3.1, §3.3: MSE budget, weak rate, (3.1), convergence test
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
