/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The cosine substitution

The meridional change of variables used for the two-sphere sends
`φ ∈ [0, π]` to `cos φ ∈ [-1, 1]`.  This file records the corresponding
complex-valued interval-integral identity.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory
open scoped ENNReal Interval

noncomputable section

/-- The substitution `u = cos φ` on the meridian. -/
theorem integral_comp_cos_mul_sin (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ φ in (0 : ℝ)..Real.pi, g (Real.cos φ) * (Real.sin φ : ℂ)) =
      ∫ u in (-1 : ℝ)..1, g u := by
  have hsubst := intervalIntegral.integral_deriv_smul_comp
    (a := (0 : ℝ)) (b := Real.pi) (f := Real.cos) (f' := fun φ => -Real.sin φ)
    (g := g) (fun φ _ => Real.hasDerivAt_cos φ) (by fun_prop) hg
  simp only [Function.comp_apply, Real.cos_zero, Real.cos_pi] at hsubst
  calc
    (∫ φ in (0 : ℝ)..Real.pi, g (Real.cos φ) * (Real.sin φ : ℂ)) =
        -∫ φ in (0 : ℝ)..Real.pi, (-Real.sin φ) • g (Real.cos φ) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro φ _
      simp only [neg_smul, neg_neg, Complex.real_smul]
      ring
    _ = -∫ u in (1 : ℝ)..(-1 : ℝ), g u := by rw [hsubst]
    _ = ∫ u in (-1 : ℝ)..1, g u := by
      rw [intervalIntegral.integral_symm]
      ring

/-- The measurable change of variables `u = cos φ` on the open meridian. -/
theorem lintegral_comp_cos_mul_sin (u : ℝ → ℝ≥0∞) :
    (∫⁻ φ in Set.Ioo (0 : ℝ) Real.pi,
      ENNReal.ofReal (Real.sin φ) * u (Real.cos φ)) =
      ∫⁻ t in Set.Ioo (-1 : ℝ) 1, u t := by
  let s : Set ℝ := Set.Ioo (0 : ℝ) Real.pi
  have himage : Real.cos '' s = Set.Ioo (-1 : ℝ) 1 := by
    simpa [s] using Real.cosPartialHomeomorph.image_source_eq_target
  rw [← himage]
  simpa [s] using
    (lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
      (f := Real.cos) (f' := fun φ => -Real.sin φ) (s := s) measurableSet_Ioo
      (fun φ _ => (Real.hasDerivAt_cos φ).hasDerivWithinAt)
      (Real.strictAntiOn_cos.antitoneOn.mono Set.Ioo_subset_Icc_self) u).symm

end

end LeanSpherical.HarmonicAnalysis
