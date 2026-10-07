# Completeness spot-check after round 15 (2026-10-07)

Two independent auditors re-read Giles (2015) §1–§5, and Giles (2015) §6–§11 with all of
Haas–Giles (2025), against the coverage tables in this directory and the Lean statements
themselves (hypotheses and conclusions, not only docstrings).  They checked about 165 rows marked
DONE or DONE-DEV and about 30 resolution entries by reading the statements, and mapped every line
of the papers to rows with a script.

**Claims missing from the tables.**  No substantive claim is missing.  Sub-claims that no row
tracks separately: the time reversal behind the antithetic Brownian path (G15 l. 1805–1809; only
the increment swap `measurePreserving_swapIncrements` is formalised), Brownian increments on fixed
non-nested union grids (l. 1926–1929; the Poisson version is `unionGrid_hasLaw`), the
deterministic analogue of drift-implicit methods (l. 1901–1905), and in Haas–Giles the existence of
the least-squares minimiser in §3.2 (assumed as `hx` by `alternating_min_*`), two trivial remarks
(§4.2, §5) and the conclusion that coarse-level savings give overall savings (§6.1).

**Rows corrected.**

| Row | Was | Now |
|---|---|---|
| G5.1-26 | DONE | PARTIAL: only the kurtosis identity is proved, not the rates `E[(ΔP)⁴] = O(h^{1/2})`, `κ = O(h^{−1/2})` |
| G5.2-09 | "the kurtosis step is done" | only the identity, not the rate `O(h^{−1})` |
| G9.2-12 | DONE | PARTIAL: the Theorem 2 bound is evaluated, but not applied to the smooth nested MIMC estimator |
| G7.1-17 | cites `rates_of_pathwise` | noted that it needs a deterministic `K`, which the parabolic example cannot have |
| G10.2-05 (README) | "truncating increments breaks (2.4)" | a pathwise statement; that the laws differ is not proved |
| G5.x (README) | "the GBM case is proved" | only the Lipschitz row of Table 5.2 and the digital option with `β = 1/3` |
| H3-07, H6-35, G9.1-15 (README) | | the assumed premise, the noise model (22) and the single kink are now stated |
| README §1 QMC row | G1-04 | G1-08 |
| G9.2-05, G10.1-08 | stale notes | point to `nestedMimcDelta`, `abs_integral_sub_limit_le` |
| legends | "all in the axiom audit" | ten cited helper lemmas are covered through the theorems that use them |

**Paper slips added to `notes/statement-audit.md`:** the method numbering in the introduction of
Haas–Giles §3, and the missing floor in §6.2.  The docstring example of
`roundFixed_sum_inconsistent` violated its strict hypothesis `ΔW₂ < 1/5` and now uses `9/50`.

**Provable with the current library (candidates for later rounds).**  End-to-end `O(ε⁻²)` for
smooth nested MIMC (G9.2-12); `|P − P_ℓ| ≤ K h²` for the actual elliptic example by the trapezoid
rule (G7.1-04); mean-square stability of the §7.3 scheme (G7.3-04); existence of an optimal
bit-width (HG25 H6-12/14); convergence of the lookup-table streams (premise of H3-07); contracting
SDEs with a fixed step (G10.1-16); Gaussian union grids; the time reversal via Mathlib's
`IsPreBrownianReal`; small corollaries (G5.5-04/05, G2.1-30, G2.4-35, G5.1-03 for a general
refinement factor); several GBM special cases of Table 5.2 (discrete Asian and lookback, the
digital with higher moments).  Out of reach: general SDE orders, continuous monitoring (reflection
principle), Feynman–Kac, information-based lower bounds, Lévy-process and SPDE theory.

**Follow-up (round 16).**  Formalised from the list above: G9.2-12 end to end
(`NestedMimcSmooth.lean`), H6-12/-14/-16 (`BitWidthOptimum.lean`), G7.1-04/-05 for the actual
scheme (`EllipticFD.lean`), and G10.1-16 with a fixed step, the premise of H3-07, G5.5-04/-05,
G2.1-30, G2.4-35 and G5.1-03 for a general refinement factor (`GilesCorollaries.lean`).

**Follow-up (round 17).**  Formalised from the remaining list: the discretely monitored Asian and
lookback rows of Table 5.2 for GBM (`GBMPathDependent.lean`), the mean-square stability of the
§7.3 scheme, G7.3-04 (`SPDEStability.lean`), the deterministic and stochastic facts behind the
drift-implicit remedy of §5.6 (`DriftImplicit.lean`), and Gaussian union grids, the
Brownian-bridge midpoint law and the time reversal via `IsPreBrownianReal` (`BrownianPaths.lean`).
Still open from the list: the digital option with higher moments (the kurtosis rates need a lower
bound on the mismatch probability).
