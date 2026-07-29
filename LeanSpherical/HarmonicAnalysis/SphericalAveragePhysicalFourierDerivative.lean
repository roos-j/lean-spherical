/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SphericalAverageInverseFourierBridge
import LeanSpherical.HarmonicAnalysis.SphericalAverageDerivative
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Identifying the physical and Fourier radius derivatives

For inverse-Fourier Schwartz data, differentiating the physical spherical
average and differentiating its literal Fourier multiplier give the same
function.  Boundedness of the Schwartz spatial derivative supplies the
physical dominated-differentiation hypothesis.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Metric Set
open scoped BoundedContinuousFunction FourierTransform

noncomputable section

/-- The physical radius derivative of a spherical average of inverse-Fourier
Schwartz data equals its literal differentiated surface multiplier. -/
theorem sphericalAverage_radiusDerivative_fourierInv_schwartz
    {d : Nat} (h : SchwartzMap (Euclidean d) ℂ) (r : ℝ) (x : Euclidean d) :
    (∫ ω : sphere (0 : Euclidean d) 1,
      fderiv ℝ ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ)
        (x + r • (ω : Euclidean d)) (ω : Euclidean d)
        ∂unitSurfaceMeasure d) =
      𝓕⁻ (fun ξ : Euclidean d =>
        deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r * h ξ) x := by
  let p : SchwartzMap (Euclidean d) ℂ := 𝓕⁻ h
  let dp : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) p
  have hbound : ∀ y : Euclidean d, ‖fderiv ℝ (p : Euclidean d → ℂ) y‖ ≤
      ‖dp.toBoundedContinuousFunction‖ := by
    intro y
    calc
      ‖fderiv ℝ (p : Euclidean d → ℂ) y‖ = ‖dp y‖ := by
        rw [← SchwartzMap.fderivCLM_apply ℂ p y]
      _ = ‖dp.toBoundedContinuousFunction y‖ := rfl
      _ ≤ ‖dp.toBoundedContinuousFunction‖ :=
        BoundedContinuousFunction.norm_coe_le_norm
          (dp.toBoundedContinuousFunction :
            Euclidean d →ᵇ (Euclidean d →L[ℝ] ℂ)) y
  have hpderiv := hasDerivAt_sphericalAverage
    (p : Euclidean d → ℂ) (by simpa only [p] using (𝓕⁻ h).smooth (1 : ℕ∞))
    hbound x r
  have hfourier :=
    hasDerivAt_sphericalAverage_fourierInv_schwartz_deriv_surfaceMultiplier h r x
  change (∫ ω : sphere (0 : Euclidean d) 1,
      fderiv ℝ (p : Euclidean d → ℂ) (x + r • (ω : Euclidean d)) (ω : Euclidean d)
        ∂unitSurfaceMeasure d) = _
  rw [← hpderiv.deriv, hfourier.deriv]

end

end LeanSpherical.HarmonicAnalysis
