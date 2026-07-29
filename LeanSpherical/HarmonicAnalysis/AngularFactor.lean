/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.MeasureTheory.Integral.Prod

/-!
# Factoring out the azimuthal angle

The elementary Tonelli calculation below supplies the `2π` angular factor in
three-dimensional spherical coordinates when the nonnegative integrand is
independent of the azimuthal angle.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Integrating a nonnegative measurable function independent of the
azimuthal variable over the full angular interval contributes a factor
`2π`. -/
theorem lintegral_Ioi_prod_Ioo_angle_factor
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      F p.1 ∂((volume : Measure ℝ).prod volume)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Ioi (0 : ℝ), F r := by
  calc
    (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      F p.1 ∂((volume : Measure ℝ).prod volume)) =
        ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          F r ∂volume ∂volume := by
      apply setLIntegral_prod
      exact (hF.comp measurable_fst).aemeasurable
    _ = ∫⁻ r in Ioi (0 : ℝ), F r * volume (Ioo (-Real.pi) Real.pi) ∂volume := by
      apply lintegral_congr
      intro r
      simp [lintegral_const]
    _ = (∫⁻ r in Ioi (0 : ℝ), F r ∂volume) * volume (Ioo (-Real.pi) Real.pi) := by
      exact lintegral_mul_const _ hF
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in Ioi (0 : ℝ), F r := by
      rw [Real.volume_Ioo]
      have hangle : Real.pi - -Real.pi = 2 * Real.pi := by ring
      rw [hangle, mul_comm]

/-- The Bochner counterpart of the angular factorization.  The radial input
is assumed integrable on `(0, ∞)`, which is exactly what Fubini needs on the
product with the finite angular interval. -/
theorem integral_Ioi_prod_Ioo_angle_factor
    (F : ℝ → ℂ) (hF : IntegrableOn F (Ioi (0 : ℝ)) volume) :
    (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      F p.1 ∂((volume : Measure ℝ).prod volume)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ r in Ioi (0 : ℝ), F r := by
  have hprod : IntegrableOn (fun p : ℝ × ℝ => F p.1)
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) ((volume : Measure ℝ).prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hF.comp_fst (volume.restrict (Ioo (-Real.pi) Real.pi))
  have hangle : (volume : Measure ℝ).real (Ioo (-Real.pi) Real.pi) = 2 * Real.pi := by
    rw [Measure.real, Real.volume_Ioo]
    calc
      (ENNReal.ofReal (Real.pi - -Real.pi)).toReal = Real.pi - -Real.pi :=
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])
      _ = 2 * Real.pi := by ring
  calc
    (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      F p.1 ∂((volume : Measure ℝ).prod volume)) =
        ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi, F r ∂volume ∂volume := by
      exact setIntegral_prod _ hprod
    _ = ∫ r in Ioi (0 : ℝ), ((2 * Real.pi : ℝ) : ℂ) * F r ∂volume := by
      apply integral_congr_ae
      filter_upwards with r
      rw [setIntegral_const, hangle, Complex.real_smul]
    _ = ((2 * Real.pi : ℝ) : ℂ) * ∫ r in Ioi (0 : ℝ), F r := by
      rw [integral_const_mul]

end

end LeanSpherical.HarmonicAnalysis
