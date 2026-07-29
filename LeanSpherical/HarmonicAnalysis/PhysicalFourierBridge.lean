/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FourierBridge
import LeanSpherical.HarmonicAnalysis.SphericalAverageContinuity
import LeanSpherical.HarmonicAnalysis.SchwartzFourierBridge
import LeanSpherical.HarmonicAnalysis.SurfaceContinuity

/-!
# A literal Fourier-inversion bridge for Schwartz inputs

For a Schwartz input, a fixed spherical average is exactly the literal
inverse Fourier integral of its concrete surface multiplier.  This is only a
fixed-radius identity; it does not exchange a radius supremum with inverse
Fourier transform.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform
open scoped FourierTransform

noncomputable section

/-- A fixed spherical average of a Schwartz input is the literal inverse
Fourier transform of its concrete surface multiplier. -/
theorem sphericalAverage_eq_fourierInv_surfaceMultiplier_schwartz
    {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ) (r : ℝ) :
    sphericalAverage d (f : Euclidean d → ℂ) r =
      𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) := by
  have hmult_integrable : Integrable (fun ξ : Euclidean d =>
      surfaceFourier d (-r • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) volume := by
    refine ((𝓕 f).integrable.norm.const_mul (surfaceMass d : ℝ)).mono' ?_ ?_
    · exact (((continuous_surfaceFourier d).comp
          ((continuous_const : Continuous fun _ : Euclidean d => -r).smul continuous_id)).mul
        (𝓕 f).continuous).aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa [surfaceMass] using norm_surfaceFourier_le_surfaceMass d (-r • ξ))
        (norm_nonneg (𝓕 (f : Euclidean d → ℂ) ξ))
  have havg_cont : Continuous (sphericalAverage d (f : Euclidean d → ℂ) r) :=
    (continuous_sphericalAverage (f : Euclidean d → ℂ) f.continuous).comp
      ((continuous_const : Continuous fun _ : Euclidean d => r).prodMk continuous_id)
  have hfourier_avg : Integrable (𝓕 (sphericalAverage d (f : Euclidean d → ℂ) r)) volume :=
    hmult_integrable.congr (Filter.Eventually.of_forall fun ξ =>
      (fourier_sphericalAverage (f : Euclidean d → ℂ) f.continuous f.integrable r ξ).symm)
  have hinv := havg_cont.fourierInv_fourier_eq
    (integrable_sphericalAverage (f : Euclidean d → ℂ) f.continuous f.integrable r)
    hfourier_avg
  have hfourier_eq : 𝓕 (sphericalAverage d (f : Euclidean d → ℂ) r) =
      fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    exact fourier_sphericalAverage (f : Euclidean d → ℂ) f.continuous f.integrable r ξ
  rw [hfourier_eq] at hinv
  exact hinv.symm

end

end LeanSpherical.HarmonicAnalysis
