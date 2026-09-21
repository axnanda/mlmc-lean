-- Multilevel Monte Carlo complexity theorems in Lean 4 / Mathlib.
--
-- * `MlmcLean.Allocation`  — optimal sample allocation (Giles (1.1)–(1.2), Haas–Giles (8), (12))
-- * `MlmcLean.Estimator`   — mean / variance / MSE of the multilevel estimator (Giles (2.1)–(2.3))
-- * `MlmcLean.Complexity`  — Giles' Theorem 1, deterministic core, three regimes
-- * `MlmcLean.Theorem1`    — Giles' Theorem 1 on a probability space
-- * `MlmcLean.Nested`      — Haas–Giles nested MLMC estimator (9)–(12)
import MlmcLean.Allocation
import MlmcLean.Estimator
import MlmcLean.Complexity
import MlmcLean.Theorem1
import MlmcLean.Nested
