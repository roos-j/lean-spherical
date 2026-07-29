/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.RadiusSobolev
import LeanSpherical.HarmonicAnalysis.SurfaceMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating the radius Sobolev estimate

The pointwise fundamental-theorem-of-calculus estimate can be integrated in
the spatial variable.  The derivative term is handled by Fubini, so the
output integrability is derived from the two stated input integrability
hypotheses.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory intervalIntegral Set

noncomputable section

/-- Integrating the compact-radius Sobolev estimate in the spatial variable.
Besides the pointwise radial `C¹` hypotheses, this requires measurability of
the requested radius slice, square-integrability of the slice at `a`, and
integrability of the derivative square on `Icc a b × space`.  Fubini then
derives the output integrability and supplies the iterated integral in the
conclusion. -/
theorem integral_norm_sq_radius_le_of_hasDerivAt
    {d : ℕ} {F F' : ℝ → Euclidean d → ℂ} {a b r : ℝ}
    (hr : r ∈ Icc a b)
    (hFr_meas : AEStronglyMeasurable (F r) volume)
    (hF'_cont : ∀ x, Continuous (fun t => F' t x))
    (hderiv : ∀ t x, HasDerivAt (fun s => F s x) (F' t x) t)
    (hFa : Integrable (fun x => ‖F a x‖ ^ 2) volume)
    (hF' : Integrable (fun p : ℝ × Euclidean d => ‖F' p.1 p.2‖ ^ 2)
      ((volume.restrict (Icc a b)).prod volume)) :
    (∫ x : Euclidean d, ‖F r x‖ ^ 2) ≤
      2 * (∫ x : Euclidean d, ‖F a x‖ ^ 2) +
        2 * (b - a) * (∫ t in a..b, ∫ x : Euclidean d, ‖F' t x‖ ^ 2) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  have hab : a ≤ b := hr.1.trans hr.2
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
  have hG : Integrable
      (fun x : Euclidean d => ∫ t, ‖F' t x‖ ^ 2 ∂ν) volume := by
    simpa only [ν] using hF'.integral_prod_right
  have hG_interval : Integrable
      (fun x : Euclidean d => ∫ t in a..b, ‖F' t x‖ ^ 2) volume := by
    have heq :
        (fun x : Euclidean d => ∫ t in a..b, ‖F' t x‖ ^ 2) =
          fun x => ∫ t, ‖F' t x‖ ^ 2 ∂ν := by
      funext x
      simp only [ν]
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    rw [heq]
    exact hG
  have hA : Integrable (fun x : Euclidean d => 2 * ‖F a x‖ ^ 2) volume := by
    simpa only using hFa.const_mul (2 : ℝ)
  have hB : Integrable
      (fun x : Euclidean d =>
        2 * (b - a) * ∫ t in a..b, ‖F' t x‖ ^ 2) volume := by
    simpa only [mul_assoc] using hG_interval.const_mul (2 * (b - a))
  have hright : Integrable
      (fun x : Euclidean d => 2 * ‖F a x‖ ^ 2 +
        2 * (b - a) * ∫ t in a..b, ‖F' t x‖ ^ 2) volume :=
    hA.add hB
  have hpoint (x : Euclidean d) :
      ‖F r x‖ ^ 2 ≤ 2 * ‖F a x‖ ^ 2 +
        2 * (b - a) * ∫ t in a..b, ‖F' t x‖ ^ 2 :=
    norm_sq_le_two_mul_norm_sq_add_two_mul_length_mul_intervalIntegral_norm_sq_of_hasDerivAt
      hr (hF'_cont x) (fun t => hderiv t x)
  have hleft : Integrable (fun x : Euclidean d => ‖F r x‖ ^ 2) volume := by
    refine Integrable.mono hright (hFr_meas.norm.pow 2) ?_
    filter_upwards with x
    have hinterval_nonneg : 0 ≤ ∫ t in a..b, ‖F' t x‖ ^ 2 :=
      intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
    have hright_nonneg :
        0 ≤ 2 * ‖F a x‖ ^ 2 +
          2 * (b - a) * ∫ t in a..b, ‖F' t x‖ ^ 2 := by
      positivity
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hright_nonneg]
    exact hpoint x
  have hswap :
      (∫ x : Euclidean d, ∫ t in a..b, ‖F' t x‖ ^ 2) =
        ∫ t in a..b, ∫ x : Euclidean d, ‖F' t x‖ ^ 2 := by
    have hF'_uIoc : Integrable
        (fun p : ℝ × Euclidean d => ‖F' p.1 p.2‖ ^ 2)
        ((volume.restrict (uIoc a b)).prod volume) := by
      rw [uIoc_of_le hab]
      rw [restrict_Ioc_eq_restrict_Icc]
      exact hF'
    exact (intervalIntegral_integral_swap
      (f := fun t (x : Euclidean d) => ‖F' t x‖ ^ 2) hF'_uIoc).symm
  calc
    (∫ x : Euclidean d, ‖F r x‖ ^ 2) ≤
        ∫ x : Euclidean d, 2 * ‖F a x‖ ^ 2 +
          2 * (b - a) * ∫ t in a..b, ‖F' t x‖ ^ 2 := by
      apply integral_mono_ae hleft hright
      filter_upwards with x
      exact hpoint x
    _ = 2 * (∫ x : Euclidean d, ‖F a x‖ ^ 2) +
        2 * (b - a) * (∫ x : Euclidean d, ∫ t in a..b, ‖F' t x‖ ^ 2) := by
      rw [MeasureTheory.integral_add hA hB,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = 2 * (∫ x : Euclidean d, ‖F a x‖ ^ 2) +
        2 * (b - a) * (∫ t in a..b, ∫ x : Euclidean d, ‖F' t x‖ ^ 2) := by
      rw [hswap]

end

end LeanSpherical.HarmonicAnalysis
