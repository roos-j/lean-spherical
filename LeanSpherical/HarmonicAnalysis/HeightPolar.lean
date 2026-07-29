/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.EuclideanCoordinates
import LeanSpherical.HarmonicAnalysis.RadialIntegration

/-!
# A dimension-uniform height--radial polar formula

This is the measure-theoretic core of the usual height-coordinate reduction
for spherical surface measure.  It separates the final Euclidean coordinate,
then applies polar integration in the remaining `d` coordinates.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

/-- A nonnegative function of the final coordinate and the radius in the
first `d` coordinates has the expected height--radial integral formula in
`Euclidean (d + 1)`. -/
theorem lintegral_euclideanSucc_radial_last {d : Nat} (hd : 0 < d)
    (G : ℝ × ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x : Euclidean (d + 1),
      G (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
        x (Fin.last d))) =
      ENNReal.ofReal (surfaceMass d) *
        ∫⁻ z : ℝ, ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal r ^ (d - 1) * G (r, z) := by
  let C : Euclidean (d + 1) → Euclidean d × ℝ := fun x =>
    (MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i)),
      x (Fin.last d))
  have hfirst : Measurable (fun x : Euclidean (d + 1) =>
      MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))) := by
    apply (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp
    apply measurable_pi_lambda
    intro i
    fun_prop
  have hC : Measurable C := by
    exact hfirst.prodMk (by fun_prop)
  have hGC : Measurable (fun q : Euclidean d × ℝ => G (‖q.1‖, q.2)) :=
    hG.comp ((measurable_norm.comp measurable_fst).prodMk measurable_snd)
  have hmeridian : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal q.2 ^ (d - 1) * G (q.2, q.1)) :=
    (measurable_snd.ennreal_ofReal.pow_const (d - 1)).mul
      (hG.comp (measurable_snd.prodMk measurable_fst))
  have hinner : Measurable (fun z : ℝ =>
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (d - 1) * G (r, z)) := by
    change Measurable (fun z : ℝ =>
      ∫⁻ r, (fun q : ℝ × ℝ =>
        ENNReal.ofReal q.2 ^ (d - 1) * G (q.2, q.1)) (z, r) ∂
          volume.restrict (Ioi (0 : ℝ)))
    exact hmeridian.lintegral_prod_right'
  calc
    (∫⁻ x : Euclidean (d + 1),
      G (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
        x (Fin.last d))) =
        ∫⁻ q : Euclidean d × ℝ, G (‖q.1‖, q.2) ∂Measure.map C volume := by
      exact (MeasureTheory.lintegral_map hGC hC).symm
    _ = ∫⁻ q : Euclidean d × ℝ,
        G (‖q.1‖, q.2) ∂((volume : Measure (Euclidean d)).prod volume) := by
      rw [show C = fun x : Euclidean (d + 1) =>
        (MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i)),
          x (Fin.last d)) by rfl,
        map_euclideanSucc_coordinates_volume]
    _ = ∫⁻ z : ℝ, ∫⁻ y : Euclidean d, G (‖y‖, z) := by
      exact lintegral_prod_symm' _ hGC
    _ = ∫⁻ z : ℝ, ENNReal.ofReal (surfaceMass d) *
          ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (d - 1) * G (r, z) := by
      apply lintegral_congr
      intro z
      exact lintegral_euclidean_radial hd (fun r => G (r, z))
        (hG.comp (measurable_id.prodMk measurable_const))
    _ = ENNReal.ofReal (surfaceMass d) *
        ∫⁻ z : ℝ, ∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal r ^ (d - 1) * G (r, z) := by
      rw [lintegral_const_mul _ hinner]

end

end LeanSpherical.HarmonicAnalysis
