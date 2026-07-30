/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.AnnulusBump

/-!
# Annular support of a spherical average

A compactly supported ball bump has every fixed spherical average supported
in the corresponding radial annulus.  This elementary geometric fact is kept
separate from the mass and covering arguments in the annulus sharpness test.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Metric Set

noncomputable section

/-- If the sampling sphere stays outside the support ball, its normalized
spherical average vanishes. -/
theorem normalizedSphericalAverage_eq_zero_of_radial_separation
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) {R r : ℝ}
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (x : Euclidean d) (hseparation : 2 * R ≤ abs (‖x‖ - abs r)) :
    normalizedSphericalAverage d f r x = 0 := by
  apply normalizedSphericalAverage_eq_of_eq_on_sphere hd f 0 r x
  intro ω
  apply hzero
  apply hseparation.trans
  apply abs_le.mpr
  constructor
  · have hradius : ‖r • (ω : Euclidean d)‖ = |r| := by
      rw [norm_smul, Real.norm_eq_abs]
      have hω : ‖(ω : Euclidean d)‖ = 1 := by
        simpa only [mem_sphere_zero_iff_norm] using ω.property
      rw [hω, mul_one]
    have htriangle : ‖r • (ω : Euclidean d)‖ ≤
        ‖x + r • (ω : Euclidean d)‖ + ‖x‖ := by
      calc
        ‖r • (ω : Euclidean d)‖ = ‖(x + r • (ω : Euclidean d)) - x‖ := by
          congr 1
          abel
        _ ≤ ‖x + r • (ω : Euclidean d)‖ + ‖x‖ := norm_sub_le _ _
    linarith [show |r| ≤ ‖x + r • (ω : Euclidean d)‖ + ‖x‖ by simpa [hradius] using htriangle]
  · have hradius : ‖r • (ω : Euclidean d)‖ = |r| := by
      rw [norm_smul, Real.norm_eq_abs]
      have hω : ‖(ω : Euclidean d)‖ = 1 := by
        simpa only [mem_sphere_zero_iff_norm] using ω.property
      rw [hω, mul_one]
    have htriangle : ‖x‖ ≤ ‖x + r • (ω : Euclidean d)‖ +
        ‖r • (ω : Euclidean d)‖ := by
      calc
        ‖x‖ = ‖(x + r • (ω : Euclidean d)) - r • (ω : Euclidean d)‖ := by
          congr 1
          abel
        _ ≤ ‖x + r • (ω : Euclidean d)‖ + ‖r • (ω : Euclidean d)‖ := norm_sub_le _ _
    linarith [show ‖x‖ ≤ ‖x + r • (ω : Euclidean d)‖ + |r| by simpa [hradius] using htriangle]

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
