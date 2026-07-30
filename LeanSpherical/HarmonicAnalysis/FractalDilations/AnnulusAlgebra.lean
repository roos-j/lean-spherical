/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Minkowski

/-!
# Exponent bookkeeping for the annulus sharpness example

The lower Minkowski witness is available at every exponent strictly below the
upper Minkowski dimension.  This file records the elementary, but important,
fact that a strict violation of the annulus inequality survives after lowering
the dimension exponent a little.  It lets the geometric packing argument use
an actual finite separated family without introducing a spurious endpoint
loss.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

noncomputable section

/-- A strict annulus violation at a positive Minkowski dimension persists at
some nonnegative exponent strictly below that dimension. -/
theorem exists_annulus_exponent_lt_minkowski
    {d : ℕ} {β p q : ℝ}
    (hβ : 0 < β) (hq : 0 < q)
    (hbad : (1 - β) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    ∃ α : ℝ, 0 ≤ α ∧ α < β ∧
      (1 - α) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹ := by
  let m : ℝ := (d : ℝ) * p⁻¹ - ((1 - β) * q⁻¹ + ((d : ℝ) - 1))
  have hm : 0 < m := by
    dsimp [m]
    linarith
  let ε : ℝ := min (β / 2) (m * q / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (by positivity)
  have hεβ : ε ≤ β / 2 := by
    dsimp [ε]
    exact min_le_left _ _
  have hεm : ε ≤ m * q / 2 := by
    dsimp [ε]
    exact min_le_right _ _
  refine ⟨β - ε, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have hqin : q * q⁻¹ = 1 := mul_inv_cancel₀ hq.ne'
    have hsmall : ε * q⁻¹ < m := by
      calc
        ε * q⁻¹ ≤ (m * q / 2) * q⁻¹ :=
          mul_le_mul_of_nonneg_right hεm (inv_nonneg.mpr hq.le)
        _ = m / 2 := by
          field_simp
        _ < m := by linarith
    have hrearrange :
        (1 - (β - ε)) * q⁻¹ + ((d : ℝ) - 1) =
          ((1 - β) * q⁻¹ + ((d : ℝ) - 1)) + ε * q⁻¹ := by
      ring
    rw [hrearrange]
    dsimp [m] at hm
    linarith

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
