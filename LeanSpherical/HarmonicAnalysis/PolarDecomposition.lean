/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure

/-!
# Polar decomposition through the concrete surface measure

Mathlib's `Measure.toSphere` is defined precisely so that the punctured
Lebesgue measure is carried by radius--direction coordinates to the product
of the concrete surface measure and the radial power measure.  This file
records the corresponding Bochner-integral identity.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- Polar decomposition of Lebesgue integration in positive Euclidean
dimension, using the concrete `unitSurfaceMeasure`.  The radial factor is
`Measure.volumeIoiPow (d - 1)`, i.e. Lebesgue measure on positive radii with
density `r ^ (d - 1)`. -/
theorem integral_polar_unitSurfaceMeasure {d : ℕ} (hd : 0 < d)
    (H : Euclidean d → ℂ) :
    (∫ x : Euclidean d, H x) =
      ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ),
        H (p.2.1 • (p.1 : Euclidean d)) ∂
          ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
  let i : Fin d := ⟨0, hd⟩
  letI : Nonempty (Fin d) := ⟨i⟩
  calc
    (∫ x : Euclidean d, H x) =
        ∫ x : ({0}ᶜ : Set (Euclidean d)), H x.1 ∂
          ((volume : Measure (Euclidean d)).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl H,
        restrict_compl_singleton]
    _ = ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ),
        (H ∘ Subtype.val ∘ (homeomorphUnitSphereProd (Euclidean d)).symm) p ∂
          (((volume : Measure (Euclidean d)).toSphere).prod
            (Measure.volumeIoiPow (Module.finrank ℝ (Euclidean d) - 1))) := by
      simpa using
        (volume : Measure (Euclidean d)).measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _)
          (H ∘ Subtype.val ∘ (homeomorphUnitSphereProd (Euclidean d)).symm)
    _ = ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ),
        H (p.2.1 • (p.1 : Euclidean d)) ∂
          ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
      simp [unitSurfaceMeasure]

end

end LeanSpherical.HarmonicAnalysis
