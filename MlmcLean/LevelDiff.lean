import Mathlib.Probability.Moments.Variance

/-!
# The multilevel correction `ΔP_ℓ = P_ℓ − P_{ℓ−1}`

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §1.3 (p. 4 of
the author's version) and (2.2): the multilevel identity
`E[P_L] = E[P_0] + ∑_{ℓ=1}^{L} E[P_ℓ − P_{ℓ−1}]` with the convention `P_{−1} ≡ 0`.
I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on FPGAs*,
arXiv:2502.07123 (2025), §2.1, use the same `ΔP_ℓ`.
-/

open MeasureTheory Finset

namespace MLMC

section defs

variable {Ω₀ : Type*}

/-- The level-`ℓ` correction `ΔP_ℓ = P_ℓ − P_{ℓ−1}`, with `P_{−1} ≡ 0` (Giles 2015, §1.3 and
(2.2)). -/
noncomputable def levelDiff (Pl : ℕ → Ω₀ → ℝ) : ℕ → Ω₀ → ℝ
  | 0 => Pl 0
  | ℓ + 1 => fun y => Pl (ℓ + 1) y - Pl ℓ y

@[simp] lemma levelDiff_zero (Pl : ℕ → Ω₀ → ℝ) : levelDiff Pl 0 = Pl 0 := rfl

@[simp] lemma levelDiff_succ (Pl : ℕ → Ω₀ → ℝ) (ℓ : ℕ) :
    levelDiff Pl (ℓ + 1) = fun y => Pl (ℓ + 1) y - Pl ℓ y := rfl

end defs

section prob

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀} {Pl : ℕ → Ω₀ → ℝ}

lemma measurable_levelDiff (hPl : ∀ ℓ, Measurable (Pl ℓ)) : ∀ ℓ, Measurable (levelDiff Pl ℓ)
  | 0 => hPl 0
  | ℓ + 1 => (hPl (ℓ + 1)).sub (hPl ℓ)

lemma memLp_levelDiff (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 ν) : ∀ ℓ, MemLp (levelDiff Pl ℓ) 2 ν
  | 0 => hPl 0
  | ℓ + 1 => (hPl (ℓ + 1)).sub (hPl ℓ)

lemma integrable_levelDiff (hPl : ∀ ℓ, Integrable (Pl ℓ) ν) :
    ∀ ℓ, Integrable (levelDiff Pl ℓ) ν
  | 0 => hPl 0
  | ℓ + 1 => (hPl (ℓ + 1)).sub (hPl ℓ)

/-- Telescoping: `∑_{ℓ=0}^{L} E[P_ℓ − P_{ℓ−1}] = E[P_L]` (Giles 2015, §1.3, p. 4). -/
lemma sum_integral_levelDiff (hPl : ∀ ℓ, Integrable (Pl ℓ) ν) (L : ℕ) :
    ∑ ℓ ∈ range (L + 1), ∫ y, levelDiff Pl ℓ y ∂ν = ∫ y, Pl L y ∂ν := by
  induction L with
  | zero => simp
  | succ L ih =>
    simp only [Finset.sum_range_succ, ih, levelDiff_succ]
    rw [integral_sub (hPl _) (hPl _)]
    ring

end prob

end MLMC
