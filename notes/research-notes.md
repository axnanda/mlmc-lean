# Research notes: nested MLMC, low precision and quantization (Sept 2026)

Working notes that go with the Lean formalisation in this repo. They record what was checked,
how, and what was concluded, so the work can be picked up without redoing it.

> **Background only, not authoritative.** Verify anything used from here against the papers in
> `docs/`. None of it is needed for the Lean milestones M0–M3 in `PLAN.md`.

Sources: **[G15]** M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015).
**[HG25]** I.-B. Haas, M.B. Giles, *A nested MLMC framework for efficient simulations on FPGAs*,
arXiv:2502.07123. PDFs, extracted text and the HG25 LaTeX source are in `docs/`.

1. How the Haas–Giles argument works
2. Evaluation: ternary-quantized random inputs
3. Weak vs strong accuracy (the "path" argument)
4. Hardware notes: AWS F2 and Inferentia/Trainium
5. Strategy: what implementations would and would not show
6. Open directions

## 1. How the Haas–Giles argument works

1. **Exact split** (HG25 eq. 9): `E[ΔP_ℓ] = E[Δ̃P_ℓ] + E[ΔP_ℓ − Δ̃P_ℓ]`. This is an identity, so any
   cheap approximation `Δ̃P` keeps the estimator unbiased. Its quality only affects variance.
2. **Optimal allocation** (eq. 12): with costs `C̃`, `C^Δ = C + C̃` and variances `Ṽ`, `V^Δ`, the
   optimal cost is `ε⁻² (Σ_ℓ √(Ṽ_ℓ C̃_ℓ) + √(V^Δ_ℓ C^Δ_ℓ))²`. Formalised in
   `MlmcLean/Allocation.lean` and `MlmcLean/Nested.lean` as a Cauchy–Schwarz lower bound for every
   allocation plus an achievable integer allocation.
3. **Error model** (§4): first-order Taylor expansion of the payoff in each rounding error, with
   sensitivities from algorithmic differentiation. This makes `V^Δ` an explicit function of every
   variable's bit-width (`V_indep` optimistic, `V_corr` pessimistic), plus an input-MSE term for
   approximate normals.
4. **Cost model** (§5): FPGA cost `Σ d_i·d_j` per multiply plus `max(d_i, d_j)` per add
   (Lee et al. 2006), relaxed to a separable quadratic. CPU cost `≈ 2^ℓ · C_RNG` with
   `C_RNG = 10⁴` units, because generating exact normals dominates.
5. **Optimisation** (§6): each level minimises the per-level factor
   `f_ℓ = √(C̃_ℓ/C_ℓ) + √(V^Δ_ℓ/V_ℓ)`. The separable model splits into one scalar equation per
   variable, solved with a golden-section search on the Lagrange multiplier and then greedy
   integer rounding. Reported: `f ≈ 1/7` at level 0 and `≈ 1/5` at level 1 (FPGA 41 and 277
   units/step against 10⁴ for the CPU), with bit-widths growing about one bit per level.

Status of HG25: all results are **modelled** in Matlab (Fixed-Point Designer for bit-accurate
arithmetic, plus the cost formula). There is no FPGA hardware or simulator, and convexity of the
optimisation is observed, not proved. A real-hardware implementation is their stated next step.

## 2. Evaluation: ternary-quantized random inputs (2026-09-23)

**Question.** Would restricting the random inputs `Z` to ternary values (like BitNet b1.58
weights), especially on the coarse levels, cut cost or wall-clock time?

**Key inequality.** Per level, `f_ℓ = √(C̃/C) + √v_ℓ ≥ √v_ℓ` with `v_ℓ = V^Δ_ℓ / V_ℓ`. A free cheap
path only removes the first term, so the nested speedup at a level is at most about
`min(C/C̃, 1/v_ℓ)`. This matches HG25 §2, where savings require `V^Δ/Ṽ ≪ C̃/C^Δ ≪ 1`.

**Method.** `experiments/quantization/ternary_check.py` uses the HG25 test case: GBM with
`r = 0.05`, `σ = 0.2`, `T = 1` (and `S0 = K = 1` assumed, since the paper doesn't state them),
Euler–Maruyama with `h_ℓ = 2^-ℓ`, and the coarse path per HG25 eq. 5. Only the inputs are
quantized, `Z̃ = q(Z)` through the inverse-CDF coupling; arithmetic is double. 400k samples per
level, levels 0–7. Output is in `experiments/quantization/results/`.

**Results (call payoff, `v_ℓ`):**

| Input quantizer | Level 0 | Levels 1–7 |
|---|---|---|
| Ternary, MSE-optimal (Lloyd–Max: 0, ±1.224) | 0.23 | 0.46–0.48 |
| Ternary, moment-matched {−√3, 0, √3} w.p. {1/6, 2/3, 1/6} | 0.34 | 0.64–0.68 |
| Ternary + error feedback (sigma-delta) | 0.23 | 0.60–0.71 |
| HG25 Method 1, 4 bits | 0.025 | 0.08–0.10 |
| HG25 Method 1, 8 bits | 0.0008 | 0.002–0.009 |
| HG25 Method 1, 12 bits | 3e-5 | 5e-5–5e-4 |

- **Smooth payoff:** `v ≈ 2 × MSE(input)` at levels ≥ 1 (0.045 against 0.044 at 4 bits; 0.349 for
  Lloyd–Max ternary). Each bit removed doubles the correction variance.
- **Digital payoff:** `v ≥ 1` from level 1 for ternary, so nesting is useless or harmful. Even
  8 bits reaches `v > 1` by level 6, so the required precision grows with level for
  discontinuous payoffs.
- **Error feedback makes it worse.** It improves the path's partial sums but lowers the
  per-step correlation that the level corrections depend on.

**Conclusion.** Ternary's best case (a free FPGA) gives `f ≥ 0.48` at level 0 and `≥ 0.68` at
levels 1+, against the paper's achieved 0.14 and 0.20: about 3.5–4× worse per level, roughly
12–17× in cost. At the paper's operating point the FPGA term is already small
(`√(41/10⁴) ≈ 0.06` at level 0); the binding term is the CPU correction variance, which ternary
inflates. Precision tricks also cannot change the ε exponent (`ε⁻²(log ε)²` for this EM test,
where `β = γ = 1`); they only move the constant. **Ternary inputs are not worth pursuing here.**

Hardware side: ternary removes the `σ√h·Z` multiply per step, but any table-based approximate
normal also removes it if the table stores `σ√h·Z_j` (or `rh + σ√h·Z_j`) directly. The
`S × (…)` multiply stays in every case.

## 3. Weak vs strong accuracy (the "path" argument)

Every correction sample runs the exact path and the cheap path **from the same random draw** and
pays for their difference. What matters is sample-by-sample closeness (strong accuracy), not
matching averages (weak accuracy).

- Example draws, exact against MSE-optimal ternary: `U = 0.10`: −1.28 vs −1.22; `U = 0.30`:
  −0.52 vs 0; `U = 0.75`: +0.67 vs +1.22. Mean squared error 0.19.
- The moment-matched ternary matches the Gaussian's first five moments. It is the 3-point
  Gauss–Hermite rule, the classic weak-order-2 increment (Kloeden & Platen): excellent for
  expectations, worse sample by sample (MSE 0.27).

Taylor argument (GBM, one pair of fine steps):

1. One Euler step multiplies `S` by `(1 + rh + σ√h·Z)`. Take logs: `log(1+x) ≈ x − x²/2`.
2. Fine path: `Z_a` then `Z_b`. Coarse path: one step with `Z_a + Z_b`. The first-order terms
   `σ√h(Z_a + Z_b)` cancel, leaving `σ²h·Z_a·Z_b` per pair. MLMC corrections only "see" products
   of consecutive increments, which is why they are small.
3. The cheap path sees `Z̃_a·Z̃_b` instead. The leftover variance ratio is
   `E[(Z_aZ_b − Z̃_aZ̃_b)²] / E[(Z_aZ_b)²] = 1 − 2E[ZZ̃]² + E[Z̃²]²`, which is 0.34 for Lloyd–Max
   (`E[ZZ̃] = E[Z̃²] = 0.81`) and 0.50 for moment-matched (`E[ZZ̃] = 0.866`, `E[Z̃²] = 1`).
   Simulated for the linear payoff: 0.345 and 0.50.

**BitNet analogy.** Nested MLMC is like distillation where you're billed for the
teacher-minus-student residual on every sample. BitNet trains with the quantizer in the loop
(straight-through estimator) and is judged on aggregate loss, so it never pays that bill.

## 4. Hardware notes (AWS, as of Sept 2026)

- **F2:** up to 8 AMD Virtex UltraScale+ VU47P FPGAs per instance. Each has 2.85M logic cells,
  9,024 DSP slices, 16 GB HBM (460 GB/s) and 64 GB DDR4. The supported flow is RTL in Vivado
  (HDK); Vitis-to-AFI wasn't officially supported according to AWS docs and re:Post. A
  DSP-mapped multiplier costs one slice at 4 or 16 bits, so HG25's bit-product cost model doesn't
  describe real F2 costs, which are step-shaped. Their optimiser needs a real resource model.
- **Inferentia2 / Trainium (NeuronCore v2/v3/v4):**
  - The Vector/Scalar engines compute in FP32 internally (about 1 TFLOPS FP32 per core on Trn2).
    BF16/FP16 inputs/outputs get a 2–4× performance mode; FP8 and smaller get no elementwise
    speedup.
  - The Tensor engine's lowest format is cFP8 on Trn2 (158 vs 79 TFLOPS for BF16). On Trn3,
    MXFP8 and MXFP4 both run at 315 TFLOPS. There is no ternary tier.
  - Hardware stochastic rounding exists from NeuronCore-v2 on. The NKI random-number call
    (`nki.language.rand`) is documented for Trn2/Trn3 only and is experimental.
  - `nki.simulate` runs NKI kernels on CPU; NKI has been stable since Neuron SDK 2.29.
- **Second check** (`experiments/quantization/neuron_formats_check.py`; FP32 math as on Neuron;
  call payoff; `v` at levels 1–7):

| Cheap path | v |
|---|---|
| Exact inputs, FP32 state | 1e-11 – 5e-7 |
| FP8 E4M3 inputs, FP32 state | 0.004 – 0.009 |
| FP8 E5M2 inputs, FP32 state | 0.014 – 0.025 |
| BF16 inputs, FP32 state | 2e-5 – 9e-5 |
| Ternary inputs, FP32 state | 0.46 – 0.48 |
| Exact inputs, FP16 state | 5e-4 → 1.6 |
| Exact inputs, BF16 state (round-to-nearest) | 0.03 → 100 |
| Exact inputs, BF16 state (stochastic rounding) | 0.07 → 200 |

Takeaways: FP8 inputs are 50–100× more accurate than ternary at the same Neuron speed. The path
state must stay FP32. Stochastic rounding doubles the rounding variance; it removes only bias,
which the nested correction already handles, so it makes nesting worse.

## 5. Strategy (2026-09-24)

- **A benchmark isn't a proof.** It shows one implementation beating one baseline on one machine
  at one date. To convince anyone it must beat a well-tuned GPU MLMC code on cost (and energy)
  per unit of accuracy.
- **The gain is a constant factor.** HG25 models about 5–7× at the first levels; the rate
  doesn't improve. What can be proved is optimality inside a cost model (what the Lean files
  do); whether the model matches silicon is empirical.
- **Why Giles & Haas did it.** The durable idea is that the nested correction makes any cheap
  but inexact computation safe (unbiased) and turns precision into an optimisable design
  variable. That's a mathematical response to AI-driven low-precision hardware.
  - The FPGA is the laboratory, because every variable can get its own bit-width; the lessons
    carry over to fixed formats (GPU half precision is their stated next step).
  - Energy efficiency is an explicit motivation.
  - The same line of work (Giles & Sheridan-Methven) previously targeted vectorised CPUs.
  - Giles has worked on GPU Monte Carlo since at least 2011 (a fast `erfinv` for GPUs).
- **Decision: hardware implementation (F2, Trainium) is not pursued for now.** The staged plan is
  recorded in case it's revisited: a local reference plus a laptop-GPU stand-in, then NKI via
  `nki.simulate` plus a few hours on trn1.2xlarge, then F2 only if a ≥10× gap remains. Any
  multi-device version needs a counter-based RNG (Threefry-style) keyed by (level, sample, step),
  so every device can regenerate the same uniforms for coupled pairs.

## 6. Open directions

1. A complexity theorem for MLMC with **level-dependent precision** (HG25 only models it). This
   extends the Lean Theorem 1 here; see `PLAN.md` (M4). Check Sheridan-Methven & Giles (2024),
   *Rounding error using low precision approximate random variables*, first.
2. Nested MLMC for **discontinuous payoffs**: how fast precision must grow per level, or which
   smoothing restores the benefit.
3. **Coupling cheap, untrusted samplers** (e.g. probabilistic/thermodynamic hardware) to exact
   simulators. Nested MLMC keeps answers exact, but without a coupling `v ≈ 1` and nesting buys
   nothing.

A general filter for any "cheap approximate X" idea: speedup ≤ `min(cost ratio, 1/v)`, and `v`
depends on strong (per-sample) accuracy.

## References

- M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015) 259–328.
- I.-B. Haas, M.B. Giles, *A nested MLMC framework for efficient simulations on FPGAs*, arXiv:2502.07123 (2025).
- M.B. Giles, O. Sheridan-Methven, *Analysis of nested multilevel Monte Carlo using approximate Normal random variables*, SIAM/ASA JUQ (2021).
- M.B. Giles, O. Sheridan-Methven, *Approximating inverse cumulative distribution functions to produce approximate random variables* (2023).
- O. Sheridan-Methven, M.B. Giles, *Rounding error using low precision approximate random variables* (2024).
- M.B. Giles, *Approximating the erfinv function*, GPU Computing Gems Jade Edition (2011): https://people.maths.ox.ac.uk/gilesm/files/gems_erfinv.pdf
- F. Belletti et al., *Tensor Processing Units for Financial Monte Carlo*, arXiv:1906.02818 (2019).
- AWS: [F2 launch](https://aws.amazon.com/blogs/aws/now-available-second-generation-fpga-powered-amazon-ec2-instances-f2),
  [NeuronCore-v2](https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/arch/neuron-hardware/neuron-core-v2.html),
  [NeuronCore-v3](https://awsdocs-neuron.readthedocs-hosted.com/en/latest/about-neuron/arch/neuron-hardware/neuron-core-v3.html),
  [Trainium2 NKI guide](https://awsdocs-neuron.readthedocs-hosted.com/en/latest/nki/guides/architecture/trainium2_arch.html),
  [NeuronCore-v4](https://awsdocs-neuron.readthedocs-hosted.com/en/latest/about-neuron/arch/neuron-hardware/neuron-core-v4.html),
  [rounding modes](https://awsdocs-neuron.readthedocs-hosted.com/en/latest/general/arch/neuron-features/rounding-modes.html),
  [nki.language.rand](https://awsdocs-neuron.readthedocs-hosted.com/en/latest/nki/api/generated/nki.language.rand.html),
  [nki.simulate_kernel](https://awsdocs-neuron.readthedocs-hosted.com/en/latest/nki/api/generated/nki.simulate_kernel.html)
