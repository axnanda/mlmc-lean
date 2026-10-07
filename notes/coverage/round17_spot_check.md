# Completeness spot-check after round 17 (2026-10-07)

Two independent auditors re-read Giles (2015) §1–§5, and Giles (2015) §6–§11 with all of
Haas–Giles (2025), against the coverage tables and the Lean statements themselves. They mapped
every line of the papers to rows with a script and checked that every cited name exists. They
also read the exact types (`#check`) of about 130 rows marked DONE, DONE-DEV or resolved in rounds
12–17.

**Claims missing from the tables.** None is substantive. The round-15 gaps (time reversal,
Gaussian union grids, the deterministic drift-implicit analogue) were closed in round 17. Not
tracked separately: existence of the least-squares minimiser in Haas–Giles §3.2 (assumed as `hx`
by `alternating_min_*`).

**Lean misstatements.** None: every checked statement says what the paper says, or states a
documented special case or corrected version of it.

**Rows and documentation corrected.**

| Item | Was | Now |
|---|---|---|
| G5.2-18 | DONE | PARTIAL: `integral_condExp_eq_of_map_eq` assumes the law equality that is the claim |
| G7.1-07, -17, -18, G7.3-08 | DONE / DONE-DEV | PARTIAL: only the complexity bound is evaluated |
| G5.2-09, G5.1-08 notes | stale | `digital_mismatch_le` exists; discrete monitoring needs only the dates |
| `GilesRemarks.lean` header | "zero variance on the coarsest level" not stated | `digital_smoothing_level_zero` |
| README, tamed scheme | `E X_N² ≤ x₀² + T` "uniformly in `N`" | for `N ≥ T/54` (`tamedCubic_second_moment_le` assumes `T ≤ 54N`) |
| G9.2-12 resolution | hypotheses incomplete | adds `f″` Lipschitz and fourth moments bounded uniformly in `ℓ` |
| G9.2-13/-14 resolution, statement audit | "the true rates are `β₁ = β₂ = 1`" | sharp along `ℓ₁ = 2ℓ₂`; the MIMC rates assume inner strong orders `½` and `1` |
| H3-25, H3-30 resolution | unconditional wording | under hypotheses on `f` that `Φ⁻¹` satisfies (not in Lean) |
| `not_convexOn_bitLevelCost` docstring | "contradicts the remark" | the numerical non-convexity concerns other parameters than the paper's |
| coverage README | | status columns keep the round-10 classification; "Round N" notes give the current state |

**Docstring-only claims (not formalised).** The README calls the digital `O(h^{1/3})` rate from
mean square "sharp" (example in the `digital_mismatch_le` docstring); the G2.1-36 counterexample
("therefore so is `Y`" fails without Lyapunov's condition, `MLMCCentralLimit.lean` docstring); the
0.3% consistency check failing for every `N ≤ 274` (numerical). The auditors checked the first two
examples by hand.

**Provable with the current library.** The auditors listed, with statement sketches and effort
estimates:
- **Small to medium:**
  - the Milstein digital variance for GBM;
  - `E[(ΔP)⁴] = P(ΔP ≠ 0)` bounds for the digital;
  - the sharpness example;
  - G5.2-18 for the actual construction;
  - GBM with refinement factor `M`;
  - the discounted call;
  - fourth moments of the tamed scheme;
  - the elliptic estimator end to end;
  - the least-squares minimiser of §3.2;
  - the law difference behind G10.2-05.
- **Medium:**
  - tau-leaping's weak rate against the exact chain for bounded payoffs, by uniformisation (G8-11);
  - `Φ⁻¹` in Lean, which makes the lookup-table results unconditional;
  - a discrete exponential-Lévy analogue of Table 6.3's Asian row (G6-09);
  - the constant-rate jump-adapted coupling (G6-02);
  - general piecewise-differentiable `f` (G9.1-15);
  - drift-implicit moments with multiplicative noise;
  - `IsBrownianReal` of the time-reversed path.
- **Medium to large:**
  - adaptive grids by discrete conditioning (G5.6-09, G8-19);
  - level-dependent steps for contracting SDEs (G10.1-16);
  - `L^p` strong errors for GBM;
  - the shifted-lattice variance in `d` dimensions.

**Out of reach.**
- **No Itô calculus:** strong and weak orders of general SDE schemes, Clark–Cameron, Giles–Szpruch.
- **No reflection principle or strong Markov property:** continuous monitoring and barriers.
- **No information-based complexity:** Creutzig et al.'s lower bound.
- **No PDE theory:** Feynman–Kac.
- **No Rademacher type in Banach spaces.**
- **No digital nets:** Sobol points and scrambling.
- **No Lévy–Itô theory or Wiener–Hopf factorisation.**
- **No Mercer's theorem:** Karhunen–Loève.
- **No lognormal elliptic regularity.**
- **Too fine:** the exact halving ratio of H3-30 (it needs the constant in `MSE ~ κ2^{−d}/d`).
- **Open:** whether nested MIMC reaches `O(ε⁻²)` for a piecewise linear `f`.

**Follow-up (round 18).** Formalised: the GBM digital items and G5.2-18 (`GBMDigital.lean`;
the paper's rates `O(h^{1/2})`, `O(h)` and the kurtosis rates remain open here), tau-leaping
against the exact chain for bounded payoffs (`TauLeapingExact.lean`), `Φ⁻¹` and the lookup-table
results for it (`InverseNormal.lean`), the elliptic estimator, the call, refinement factor `M`,
tamed fourth moments, the method-2 iteration and the rounded increments
(`EndToEndInstances.lean`).  Not yet: the G2.1-36 counterexample as a theorem, the medium and
large items above.
