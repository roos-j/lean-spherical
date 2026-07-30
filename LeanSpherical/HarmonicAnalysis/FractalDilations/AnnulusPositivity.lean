/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.AnnulusCore

/-!
# Positivity of normalized spherical averages

The annulus test uses nonnegative real bumps.  Their complexified normalized
spherical averages are real and nonnegative, so the exact Fubini mass identity
can be converted into a positive lower bound without losing cancellations.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Metric Set

noncomputable section

/-- The real part of a normalized spherical average of a nonnegative real
input has exactly the original total mass. -/
theorem integral_re_normalizedSphericalAverage_eq_integral
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℝ)
    (hfcont : Continuous f) (hf : Integrable f volume) (r : ℝ) :
    (∫ x : Euclidean d,
      (normalizedSphericalAverage d (fun y => (f y : ℂ)) r x).re) =
      ∫ x : Euclidean d, f x := by
  have hfcontC : Continuous (fun y => (f y : ℂ)) :=
    Complex.continuous_ofReal.comp hfcont
  have hfC : Integrable (fun y => (f y : ℂ)) volume := hf.ofReal
  have havg : Integrable
      (normalizedSphericalAverage d (fun y => (f y : ℂ)) r) volume := by
    unfold normalizedSphericalAverage
    exact (integrable_sphericalAverage (fun y => (f y : ℂ)) hfcontC hfC r).const_mul _
  calc
    (∫ x : Euclidean d,
      (normalizedSphericalAverage d (fun y => (f y : ℂ)) r x).re) =
        (∫ x : Euclidean d,
          normalizedSphericalAverage d (fun y => (f y : ℂ)) r x).re :=
      integral_re havg
    _ = (∫ x : Euclidean d, (f x : ℂ)).re := by
      rw [integral_normalizedSphericalAverage_eq_integral hd
        (fun y => (f y : ℂ)) hfcontC hfC r]
    _ = ∫ x : Euclidean d, f x := by
      rw [integral_complex_ofReal]
      rfl

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
