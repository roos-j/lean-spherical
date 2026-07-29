/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.AngularFactor
import LeanSpherical.HarmonicAnalysis.SphericalCoordinates

/-!
# Spherical coordinates in three dimensions

This is the composition of cylindrical coordinates in the horizontal plane,
azimuthal integration, and polar coordinates in the meridian half-plane.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Lebesgue integration in `ℂ × ℝ`, for functions depending on the horizontal
coordinate only through its radius, is the usual three-dimensional spherical
coordinate integral. -/
theorem lintegral_threeDimensional_spherical
    (G : ℝ × ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ y : ℂ × ℝ, G (‖y.1‖, y.2) ∂((volume : Measure ℂ).prod volume)) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
          ENNReal.ofReal p.1 * ENNReal.ofReal (p.1 * Real.sin p.2) *
            G (p.1 * Real.sin p.2, p.1 * Real.cos p.2) := by
  have hF : Measurable (fun y : ℂ × ℝ => G (‖y.1‖, y.2)) :=
    hG.comp ((measurable_norm.comp measurable_fst).prodMk measurable_snd)
  have hRadial : Measurable (fun r : ℝ =>
      ENNReal.ofReal r * ∫⁻ z : ℝ, G (r, z)) :=
    measurable_id.ennreal_ofReal.mul hG.lintegral_prod_right'
  have hMeridian : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal q.2 * G (q.2, q.1)) :=
    (measurable_snd.ennreal_ofReal).mul
      (hG.comp (measurable_snd.prodMk measurable_fst))
  calc
    (∫⁻ y : ℂ × ℝ, G (‖y.1‖, y.2) ∂((volume : Measure ℂ).prod volume)) =
        ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 *
            (∫⁻ z : ℝ, G (‖Complex.polarCoord.symm p‖, z)) :=
      lintegral_cylindrical _ hF
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 *
            (∫⁻ z : ℝ, G (‖Complex.polarCoord.symm p‖, z)) := by
      rw [Complex.polarCoord_target]
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * (∫⁻ z : ℝ, G (p.1, z)) := by
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hp0 : 0 < p.1 := hp.1
      simp [abs_of_pos hp0]
    _ = ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * ∫⁻ z : ℝ, G (r, z) :=
      lintegral_Ioi_prod_Ioo_angle_factor _ hRadial
    _ = ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ q in Set.univ ×ˢ Ioi (0 : ℝ),
            ENNReal.ofReal q.2 * G (q.2, q.1) := by
      congr 1
      calc
        (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * ∫⁻ z : ℝ, G (r, z)) =
            ∫⁻ r in Ioi (0 : ℝ), ∫⁻ z : ℝ, ENNReal.ofReal r * G (r, z) := by
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro r hr
          change ENNReal.ofReal r * (∫⁻ z : ℝ, G (r, z)) =
            ∫⁻ z : ℝ, ENNReal.ofReal r * G (r, z)
          exact (lintegral_const_mul (μ := volume) (ENNReal.ofReal r)
            (hG.comp (measurable_const.prodMk measurable_id))).symm
        _ = ∫⁻ q in Set.univ ×ˢ Ioi (0 : ℝ),
            ENNReal.ofReal q.2 * G (q.2, q.1) := by
          symm
          change
            (∫⁻ q in Set.univ ×ˢ Ioi (0 : ℝ),
              ENNReal.ofReal q.2 * G (q.2, q.1) ∂((volume : Measure ℝ).prod volume)) =
            ∫⁻ r in Ioi (0 : ℝ), ∫⁻ z : ℝ, ENNReal.ofReal r * G (r, z)
          simpa using
            (setLIntegral_prod_symm (μ := volume) (ν := volume)
              (s := Set.univ) (t := Ioi (0 : ℝ))
              (fun q : ℝ × ℝ => ENNReal.ofReal q.2 * G (q.2, q.1))
              hMeridian.aemeasurable.restrict)
    _ = ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
            ENNReal.ofReal p.1 * ENNReal.ofReal (p.1 * Real.sin p.2) *
              G (p.1 * Real.sin p.2, p.1 * Real.cos p.2) := by
      rw [lintegral_meridian_cylindrical_density]

/-- The Euclidean radius of the meridian coordinates `(ρ sin φ, ρ cos φ)` is
`ρ` when `ρ` is nonnegative. -/
theorem sqrt_spherical_meridian_norm_sq (ρ φ : ℝ) (hρ : 0 ≤ ρ) :
    Real.sqrt ((ρ * Real.sin φ) ^ 2 + (ρ * Real.cos φ) ^ 2) = ρ := by
  rw [show (ρ * Real.sin φ) ^ 2 + (ρ * Real.cos φ) ^ 2 = ρ ^ 2 by
    calc
      (ρ * Real.sin φ) ^ 2 + (ρ * Real.cos φ) ^ 2 =
          ρ ^ 2 * (Real.sin φ ^ 2 + Real.cos φ ^ 2) := by ring
      _ = ρ ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]]
  simpa [abs_of_nonneg hρ] using (Real.sqrt_sq_eq_abs ρ)

/-- In meridian spherical coordinates, normalizing the vertical coordinate
returns `cos φ` away from the origin. -/
theorem spherical_normalized_vertical_eq_cos (ρ φ : ℝ) (hρ : 0 < ρ) :
    (ρ * Real.cos φ) /
        Real.sqrt ((ρ * Real.sin φ) ^ 2 + (ρ * Real.cos φ) ^ 2) = Real.cos φ := by
  rw [sqrt_spherical_meridian_norm_sq ρ φ hρ.le]
  field_simp

end

end LeanSpherical.HarmonicAnalysis
