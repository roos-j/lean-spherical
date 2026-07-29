/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A one-dimensional oscillatory integral

This is the elementary calculation which gives the sharp `|a|⁻¹` decay in
the three-dimensional spherical formula, once the pushforward of surface
measure to a height coordinate has been established.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory intervalIntegral

noncomputable section

/-- The elementary oscillatory integral appearing after reducing the
three-dimensional sphere to its height coordinate. -/
theorem intervalIntegral_exp_surfacePhase (a : ℝ) (ha : a ≠ 0) :
    ∫ t in (-1 : ℝ)..1, Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I) =
      (Complex.exp (((-2 * Real.pi * a : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I)) /
        (((-2 * Real.pi * a : ℝ) : ℂ) * Complex.I) := by
  rw [show (fun t : ℝ => Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I)) =
      fun (t : ℝ) => Complex.exp ((((-2 * Real.pi * a : ℝ) : ℂ) * Complex.I) * (t : ℂ)) by
        funext t
        push_cast
        ring_nf]
  rw [integral_exp_mul_complex]
  · congr 2 <;> push_cast <;> ring_nf
  · simp [ha, Real.pi_ne_zero]

/-- The preceding integral has the quantitative `|a|⁻¹` cancellation bound. -/
theorem norm_intervalIntegral_exp_surfacePhase_le (a : ℝ) (ha : a ≠ 0) :
    ‖∫ t in (-1 : ℝ)..1, Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I)‖ ≤
      1 / (Real.pi * |a|) := by
  rw [intervalIntegral_exp_surfacePhase a ha, norm_div]
  have hnum :
      ‖Complex.exp (((-2 * Real.pi * a : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I)‖ ≤ 2 := by
    calc
      ‖Complex.exp (((-2 * Real.pi * a : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I)‖ ≤
          ‖Complex.exp (((-2 * Real.pi * a : ℝ) : ℂ) * Complex.I)‖ +
            ‖Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
        norm_num
  have hden : ‖(((-2 * Real.pi * a : ℝ) : ℂ) * Complex.I)‖ = 2 * Real.pi * |a| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg Real.pi_pos.le]
    ring
  rw [hden]
  have hden_pos : 0 < 2 * Real.pi * |a| := by
    positivity
  calc
    ‖Complex.exp (((-2 * Real.pi * a : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I)‖ / (2 * Real.pi * |a|) ≤
        2 / (2 * Real.pi * |a|) := (div_le_div_iff_of_pos_right hden_pos).2 hnum
    _ = 1 / (Real.pi * |a|) := by field_simp

end

end LeanSpherical.HarmonicAnalysis
