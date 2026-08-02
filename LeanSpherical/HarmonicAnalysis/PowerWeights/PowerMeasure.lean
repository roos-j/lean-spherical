/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceCore

/-!
# Radial power measures

The power weight `|x|^α` and the associated measure on Euclidean space.
The density takes values in `ℝ≥0∞`, so negative exponents have the expected
value `⊤` at the origin.  This is harmless for the ranges in which the
weighted measure is locally finite and keeps the definition total.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The radial power density `x ↦ |x|^α`, valued in `ℝ≥0∞`. -/
def radialPowerWeight (d : ℕ) (α : ℝ) (x : Euclidean d) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖x‖) ^ α

/-- Lebesgue measure weighted by the radial power `|x|^α`. -/
def powerWeightedVolume (d : ℕ) (α : ℝ) : Measure (Euclidean d) :=
  volume.withDensity (radialPowerWeight d α)

/-- The radial power weight is measurable. -/
theorem measurable_radialPowerWeight (d : ℕ) (α : ℝ) :
    Measurable (radialPowerWeight d α) := by
  unfold radialPowerWeight
  exact ENNReal.continuous_rpow_const.measurable.comp
    (continuous_norm.measurable.ennreal_ofReal)

/-- The radial power weight is almost-everywhere measurable for every measure. -/
theorem aemeasurable_radialPowerWeight (d : ℕ) (α : ℝ)
    (μ : Measure (Euclidean d)) :
    AEMeasurable (radialPowerWeight d α) μ :=
  (measurable_radialPowerWeight d α).aemeasurable

/-- The radial power weight is nonnegative. -/
theorem radialPowerWeight_nonneg (d : ℕ) (α : ℝ) (x : Euclidean d) :
    0 ≤ radialPowerWeight d α x :=
  bot_le

/-- Radial power weights have the expected pointwise homogeneity under a
positive Euclidean dilation. -/
theorem radialPowerWeight_smul {d : ℕ} (α : ℝ) {a : ℝ} (ha : 0 < a)
    (x : Euclidean d) :
    radialPowerWeight d α (a • x) =
      (ENNReal.ofReal a) ^ α * radialPowerWeight d α x := by
  unfold radialPowerWeight
  rw [norm_smul, Real.norm_of_nonneg ha.le]
  rw [ENNReal.ofReal_mul ha.le]
  exact ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top α

/-- At exponent zero, the radial power density is identically one. -/
@[simp] theorem radialPowerWeight_zero (d : ℕ) (x : Euclidean d) :
    radialPowerWeight d 0 x = 1 := by
  simp [radialPowerWeight]

/-- The zero power weight gives exactly Lebesgue measure. -/
@[simp] theorem powerWeightedVolume_zero (d : ℕ) :
    powerWeightedVolume d 0 = volume := by
  unfold powerWeightedVolume
  have hweight : radialPowerWeight d 0 = fun _ : Euclidean d => 1 := by
    funext x
    exact radialPowerWeight_zero d x
  rw [hweight]
  simp

end

end LeanSpherical.HarmonicAnalysis
