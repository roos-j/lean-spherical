/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SphericalAverageFourierDerivativeMultiplier

/-!
# Spherical averages of inverse-Fourier Schwartz data

The literal Fourier formulas for spherical averages specialize directly to
Schwartz data given on the frequency side.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform
open scoped FourierTransform

noncomputable section

/-- The spherical average of inverse-Fourier Schwartz data has the literal
surface-multiplier formula with the original frequency-side Schwartz map. -/
theorem sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier
    {d : ℕ} (h : SchwartzMap (Euclidean d) ℂ) (r : ℝ) :
    sphericalAverage d ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r =
      𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * h ξ) := by
  have hfourier :
      𝓕 ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) =
        (h : Euclidean d → ℂ) := by
    rw [← SchwartzMap.fourier_coe, fourier_fourierInv_eq]
  rw [sphericalAverage_eq_fourierInv_surfaceMultiplier_schwartz (𝓕⁻ h) r,
    hfourier]

/-- The radius derivative of a spherical average of inverse-Fourier Schwartz
data is the literal inverse Fourier multiplier obtained by differentiating
the surface transform. -/
theorem hasDerivAt_sphericalAverage_fourierInv_schwartz_deriv_surfaceMultiplier
    {d : ℕ} (h : SchwartzMap (Euclidean d) ℂ) (r : ℝ) (x : Euclidean d) :
    HasDerivAt
      (fun s : ℝ =>
        sphericalAverage d ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) s x)
      (𝓕⁻ (fun ξ : Euclidean d =>
        deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r * h ξ) x)
      r := by
  have hfourier :
      𝓕 ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) =
        (h : Euclidean d → ℂ) := by
    rw [← SchwartzMap.fourier_coe, fourier_fourierInv_eq]
  simpa only [hfourier] using
    (hasDerivAt_sphericalAverage_fourierInv_deriv_surfaceMultiplier_schwartz
      (𝓕⁻ h) r x)

end

end LeanSpherical.HarmonicAnalysis
