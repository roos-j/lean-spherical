/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SphericalAverageFourierDerivative

/-!
# The radius derivative as a literal Fourier multiplier

This rewrites the differentiated surface integral as the radial derivative
of the concrete Fourier transform of surface measure.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Metric Set
open scoped FourierTransform

noncomputable section

/-- For Schwartz input, the radius derivative of a spherical average is the
literal inverse Fourier multiplier obtained by differentiating
`surfaceFourier` in the radius. -/
theorem hasDerivAt_sphericalAverage_fourierInv_deriv_surfaceMultiplier_schwartz
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) (r : ℝ) (x : Euclidean d) :
    HasDerivAt
      (fun s : ℝ => sphericalAverage d (f : Euclidean d → ℂ) s x)
      (𝓕⁻ (fun ξ : Euclidean d =>
        deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r *
          𝓕 (f : Euclidean d → ℂ) ξ) x)
      r := by
  have hmult :
      (fun ξ : Euclidean d =>
        (∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω
            ∂unitSurfaceMeasure d) * 𝓕 (f : Euclidean d → ℂ) ξ) =
      fun ξ : Euclidean d =>
        deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r *
          𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    rw [(hasDerivAt_surfaceFourier_radial_at d (-ξ) r).deriv]
  rw [← hmult]
  exact hasDerivAt_sphericalAverage_fourierInv_surfaceDerivative_schwartz f r x

end

end LeanSpherical.HarmonicAnalysis
