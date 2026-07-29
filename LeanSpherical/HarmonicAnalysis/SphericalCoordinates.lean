/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.CylindricalCoordinates

/-!
# Spherical coordinates

The meridian half-plane is parametrized by polar coordinates with its first
coordinate vertical and its second coordinate horizontal.  The Jacobian in
this step is the radial coordinate; when it is combined with the cylindrical
Jacobian, it yields the usual `rho^2 * sin phi` factor.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Polar coordinates on the upper half-plane.  The input coordinate order is
`(vertical, horizontal)`, so the horizontal coordinate is `rho * sin phi`. -/
theorem lintegral_meridian_halfPlane
    (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ q in Set.univ ×ˢ Set.Ioi (0 : ℝ), F q) =
      ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi,
        ENNReal.ofReal p.1 * F (polarCoord.symm p) := by
  rw [← lintegral_indicator (MeasurableSet.univ.prod measurableSet_Ioi) F]
  rw [← lintegral_comp_polarCoord_symm
    ((Set.univ ×ˢ Set.Ioi (0 : ℝ)).indicator F)]
  rw [← lintegral_indicator polarCoord.open_target.measurableSet]
  rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ polarCoord.target
  · rw [Set.indicator_of_mem hp]
    have hmem : polarCoord.symm p ∈ Set.univ ×ˢ Set.Ioi (0 : ℝ) ↔
        p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi := by
      rw [polarCoord_symm_apply]
      simp only [Set.mem_prod, mem_univ, true_and, mem_Ioi, mem_Ioo]
      change 0 < p.1 * Real.sin p.2 ↔ 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi
      rw [polarCoord_target] at hp
      change 0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi at hp
      constructor
      · intro h
        refine ⟨hp.1, ?_, hp.2.2⟩
        by_contra hphi
        have hsin : Real.sin p.2 ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt hphi) hp.2.1.le
        exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hp.1.le hsin)) h
      · rintro ⟨_, hphi, _⟩
        exact mul_pos hp.1 (Real.sin_pos_of_pos_of_lt_pi hphi hp.2.2)
    by_cases hp' : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi
    · rw [Set.indicator_of_mem hp' _, Set.indicator_of_mem (hmem.mpr hp') _]
      exact smul_eq_mul _ _
    · rw [Set.indicator_of_notMem hp' _, Set.indicator_of_notMem (mt hmem.mp hp') _]
      simp
  · rw [Set.indicator_of_notMem hp _]
    have hp' : p ∉ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi := by
      intro h
      exact hp (by
        rw [polarCoord_target]
        change 0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi
        change 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi at h
        exact ⟨h.1, by linarith [Real.pi_pos], h.2.2⟩)
    rw [Set.indicator_of_notMem hp' _]

/-- Combining the meridian polar Jacobian with the horizontal-radius factor
from cylindrical coordinates gives the spherical density
`rho * (rho * sin phi)`. -/
theorem lintegral_meridian_cylindrical_density
    (G : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ q in Set.univ ×ˢ Set.Ioi (0 : ℝ),
      ENNReal.ofReal q.2 * G (q.2, q.1)) =
      ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi,
        ENNReal.ofReal p.1 * ENNReal.ofReal (p.1 * Real.sin p.2) *
          G (p.1 * Real.sin p.2, p.1 * Real.cos p.2) := by
  simpa only [polarCoord_symm_apply, mul_assoc] using
    (lintegral_meridian_halfPlane
      (fun q : ℝ × ℝ => ENNReal.ofReal q.2 * G (q.2, q.1)))

/-- The Bochner polar-coordinate transport on the meridian half-plane.  It
is unconditional because the underlying polar change-of-variables theorem is
stated for the Bochner integral itself. -/
theorem integral_meridian_halfPlane
    (F : ℝ × ℝ → ℂ) :
    (∫ q in Set.univ ×ˢ Set.Ioi (0 : ℝ), F q) =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi,
        p.1 • F (polarCoord.symm p) := by
  rw [← integral_indicator (MeasurableSet.univ.prod measurableSet_Ioi)]
  rw [← integral_comp_polarCoord_symm
    ((Set.univ ×ˢ Set.Ioi (0 : ℝ)).indicator F)]
  rw [← integral_indicator polarCoord.open_target.measurableSet]
  rw [← integral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  apply integral_congr_ae
  filter_upwards with p
  by_cases hp : p ∈ polarCoord.target
  · rw [Set.indicator_of_mem hp]
    have hmem : polarCoord.symm p ∈ Set.univ ×ˢ Set.Ioi (0 : ℝ) ↔
        p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi := by
      rw [polarCoord_symm_apply]
      simp only [Set.mem_prod, mem_univ, true_and, mem_Ioi, mem_Ioo]
      change 0 < p.1 * Real.sin p.2 ↔ 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi
      rw [polarCoord_target] at hp
      change 0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi at hp
      constructor
      · intro h
        refine ⟨hp.1, ?_, hp.2.2⟩
        by_contra hphi
        have hsin : Real.sin p.2 ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt hphi) hp.2.1.le
        exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hp.1.le hsin)) h
      · rintro ⟨_, hphi, _⟩
        exact mul_pos hp.1 (Real.sin_pos_of_pos_of_lt_pi hphi hp.2.2)
    by_cases hp' : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi
    · rw [Set.indicator_of_mem hp' _, Set.indicator_of_mem (hmem.mpr hp') _]
    · rw [Set.indicator_of_notMem hp' _, Set.indicator_of_notMem (mt hmem.mp hp') _]
      simp
  · rw [Set.indicator_of_notMem hp _]
    have hp' : p ∉ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi := by
      intro h
      exact hp (by
        rw [polarCoord_target]
        change 0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi
        change 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi at h
        exact ⟨h.1, by linarith [Real.pi_pos], h.2.2⟩)
    rw [Set.indicator_of_notMem hp' _]

/-- Combining the meridian Jacobian with the horizontal cylindrical factor
gives the complex-valued spherical density `ρ * (ρ * sin φ)`. -/
theorem integral_meridian_cylindrical_density
    (G : ℝ × ℝ → ℂ) :
    (∫ q in Set.univ ×ˢ Set.Ioi (0 : ℝ),
      (q.2 : ℂ) * G (q.2, q.1)) =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi,
        (p.1 : ℂ) * ((p.1 * Real.sin p.2 : ℝ) : ℂ) *
          G (p.1 * Real.sin p.2, p.1 * Real.cos p.2) := by
  simpa only [polarCoord_symm_apply, Complex.real_smul, mul_assoc] using
    (integral_meridian_halfPlane
      (fun q : ℝ × ℝ => (q.2 : ℂ) * G (q.2, q.1)))

end

end LeanSpherical.HarmonicAnalysis
