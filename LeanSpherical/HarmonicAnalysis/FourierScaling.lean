/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Scaling for the literal inverse Fourier integral

This is the change-of-variables formula for the inverse Fourier integral on a
finite-dimensional real inner-product space.  It applies to arbitrary
functions: non-integrable integrals have Mathlib's value zero on both sides.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform
open scoped FourierTransform

noncomputable section

/-- Dilating the frequency argument by `R⁻¹` dilates the literal inverse
Fourier integral by `R` in physical space, with the Jacobian factor `R ^ dim`. -/
theorem fourierInv_comp_inv_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (g : E → ℂ) {R : ℝ} (hR : 0 < R) (x : E) :
    𝓕⁻ (fun ξ : E => g (R⁻¹ • ξ)) x =
      R ^ Module.finrank ℝ E • (𝓕⁻ g) (R • x) := by
  rw [Real.fourierInv_eq]
  change (∫ v : E, Real.fourierChar (inner ℝ v x) • g (R⁻¹ • v)) = _
  let F : E → ℂ := fun y => (Real.fourierChar) (inner ℝ (R • y) x) • g y
  have hF : (fun v : E => (Real.fourierChar) (inner ℝ v x) • g (R⁻¹ • v)) =
      fun v => F (R⁻¹ • v) := by
    funext v
    dsimp [F]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  rw [hF, Measure.integral_comp_inv_smul volume F R,
    abs_of_nonneg (pow_nonneg hR.le _)]
  congr 1
  rw [Real.fourierInv_eq]
  congr with y
  dsimp [F]
  rw [inner_smul_left, inner_smul_right, conj_trivial]

end

end LeanSpherical.HarmonicAnalysis
