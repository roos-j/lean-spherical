/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of compact-radius maximal functions

A joint-continuous family has a measurable supremum over a compact radius
interval.  Mathlib obtains this from a countable dense subset of the radius
index.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Set

noncomputable section

/-- The compact-radius supremum of the norm of a jointly continuous
complex-valued family is measurable in the spatial variable. -/
theorem measurable_iSup_ennreal_norm_of_continuous
    {d : ℕ} {F : ℝ × Euclidean d → ℂ} {a b : ℝ}
    (hF : Continuous F) :
    Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal ‖F (r.1, x)‖) := by
  have hG : Measurable (⨆ r : Icc a b, fun x : Euclidean d =>
      ENNReal.ofReal ‖F (r.1, x)‖) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro r
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_const.prodMk continuous_id)).norm)).measurable
    · intro x
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_subtype_val.prodMk continuous_const)).norm)).lowerSemicontinuous
  have hEq : (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal ‖F (r.1, x)‖) =
      ⨆ r : Icc a b, fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖ := by
    funext x
    exact (iSup_apply
      (f := fun r : Icc a b => fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖) (a := x)).symm
  rw [hEq]
  exact hG

/-- The compact-radius supremum of the squared norm of a jointly continuous
complex-valued family is measurable in the spatial variable. -/
theorem measurable_iSup_ennreal_norm_sq_of_continuous
    {d : ℕ} {F : ℝ × Euclidean d → ℂ} {a b : ℝ}
    (hF : Continuous F) :
    Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal (‖F (r.1, x)‖ ^ 2)) := by
  have hG : Measurable (⨆ r : Icc a b, fun x : Euclidean d =>
      ENNReal.ofReal (‖F (r.1, x)‖ ^ 2)) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro r
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_const.prodMk continuous_id)).norm.pow 2)).measurable
    · intro x
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_subtype_val.prodMk continuous_const)).norm.pow 2)).lowerSemicontinuous
  have hEq : (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal (‖F (r.1, x)‖ ^ 2)) =
      ⨆ r : Icc a b, fun x : Euclidean d =>
        ENNReal.ofReal (‖F (r.1, x)‖ ^ 2) := by
    funext x
    exact (iSup_apply
      (f := fun r : Icc a b => fun x : Euclidean d =>
        ENNReal.ofReal (‖F (r.1, x)‖ ^ 2)) (a := x)).symm
  rw [hEq]
  exact hG

end

end LeanSpherical.HarmonicAnalysis
