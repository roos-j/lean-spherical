/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Cylindrical coordinates

This is the full-dimensional change of variables needed for the elementary
three-dimensional calculation: regard the horizontal plane as `ℂ`, apply
polar coordinates there, and keep the vertical coordinate separate.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Fubini followed by polar coordinates in the horizontal plane. -/
theorem integral_cylindrical
    (F : ℂ × ℝ → ℂ) (hF : Integrable F ((volume : Measure ℂ).prod volume)) :
    (∫ x : ℂ × ℝ, F x ∂((volume : Measure ℂ).prod volume)) =
      ∫ p in Complex.polarCoord.target,
        p.1 • (∫ z : ℝ, F (Complex.polarCoord.symm p, z) ∂volume) ∂volume := by
  calc
    (∫ x : ℂ × ℝ, F x ∂((volume : Measure ℂ).prod volume)) =
        ∫ w : ℂ, (∫ z : ℝ, F (w, z) ∂volume) ∂volume :=
      integral_prod F hF
    _ = ∫ p in Complex.polarCoord.target,
        p.1 • (∫ z : ℝ, F (Complex.polarCoord.symm p, z) ∂volume) ∂volume := by
      symm
      exact Complex.integral_comp_polarCoord_symm
        (fun w : ℂ => ∫ z : ℝ, F (w, z) ∂volume)

/-- The nonnegative version of `integral_cylindrical`, suitable for computing
volumes of cones by Tonelli's theorem. -/
theorem lintegral_cylindrical
    (F : ℂ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : ℂ × ℝ, F x ∂((volume : Measure ℂ).prod volume)) =
      ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 *
          (∫⁻ z : ℝ, F (Complex.polarCoord.symm p, z) ∂volume) ∂volume := by
  calc
    (∫⁻ x : ℂ × ℝ, F x ∂((volume : Measure ℂ).prod volume)) =
        ∫⁻ w : ℂ, (∫⁻ z : ℝ, F (w, z) ∂volume) ∂volume :=
      lintegral_prod F hF.aemeasurable
    _ = ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 *
          (∫⁻ z : ℝ, F (Complex.polarCoord.symm p, z) ∂volume) ∂volume := by
      symm
      exact Complex.lintegral_comp_polarCoord_symm
        (fun w : ℂ => ∫⁻ z : ℝ, F (w, z) ∂volume)

end

end LeanSpherical.HarmonicAnalysis
