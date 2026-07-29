/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# `L¹` invariance under Euclidean dilation

The normalization `R ^ d` in a dilated Euclidean kernel exactly preserves its
`L¹` norm when `R > 0`.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory

noncomputable section

/-- A positive Euclidean dilation, with its usual Jacobian factor, preserves
the integral of the pointwise norm. -/
theorem integral_norm_dilate_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (k : Euclidean d → E) {R : ℝ}
    (hR : 0 < R) :
    (∫ x : Euclidean d, ‖(R ^ d) • k (R • x)‖) = ∫ x : Euclidean d, ‖k x‖ := by
  rw [show (fun x : Euclidean d => ‖(R ^ d) • k (R • x)‖) =
      fun x => R ^ d * ‖k (R • x)‖ by
        funext x
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hR.le _)],
      integral_const_mul,
      Measure.integral_comp_smul_of_nonneg volume (fun x : Euclidean d => ‖k x‖) R
        (hR := hR.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp [hR.ne']

/-- The unnormalised positive Euclidean dilation has the reciprocal Jacobian
factor in its `L¹` norm. -/
theorem integral_norm_comp_smul_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (f : Euclidean d → E) {R : ℝ} (hR : 0 < R) :
    (∫ x : Euclidean d, ‖f (R • x)‖) =
      (R ^ d)⁻¹ * ∫ x : Euclidean d, ‖f x‖ := by
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun x : Euclidean d => ‖f x‖) R (hR := hR.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]

/-- The square-energy version of Euclidean dilation.  This is the Jacobian
identity used when compact-radius `L²` estimates are transported to a
literal dyadic radius block. -/
theorem integral_norm_sq_comp_smul_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (f : Euclidean d → E) {R : ℝ} (hR : 0 < R) :
    (∫ x : Euclidean d, ‖f (R • x)‖ ^ (2 : ℕ)) =
      (R ^ d)⁻¹ * ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ) := by
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun x : Euclidean d => ‖f x‖ ^ (2 : ℕ)) R (hR := hR.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]

/-- Integrability is preserved by a positive Euclidean dilation with the
usual Jacobian factor. -/
theorem integrable_dilate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (k : Euclidean d → E) {R : ℝ}
    (hR : 0 < R) (hk : Integrable k) :
    Integrable (fun x : Euclidean d => (R ^ d) • k (R • x)) := by
  have hcomp : Integrable (fun x : Euclidean d => k (R • x)) :=
    Integrable.comp_smul hk hR.ne'
  convert Integrable.smul (R ^ d : ℝ) hcomp using 1
  ext x
  rfl

/-- The total derivative of a Euclidean dilation has the expected extra
factor of the dilation scale. -/
theorem fderiv_dilate
    {d : ℕ} (k : Euclidean d → ℂ) (hk : ContDiff ℝ 1 k)
    (R : ℝ) (x : Euclidean d) :
    fderiv ℝ (fun y : Euclidean d => (R ^ d) • k (R • y)) x =
      (R ^ (d + 1)) • fderiv ℝ k (R • x) := by
  have hcomp : DifferentiableAt ℝ (fun y : Euclidean d => k (R • y)) x :=
    (hk.differentiable (by norm_num)).differentiableAt.comp x
      (differentiableAt_id.const_smul R)
  calc
    fderiv ℝ (fun y : Euclidean d => (R ^ d) • k (R • y)) x =
        (R ^ d) • fderiv ℝ (fun y : Euclidean d => k (R • y)) x :=
      fderiv_fun_const_smul hcomp (R ^ d)
    _ = (R ^ d) • (R • fderiv ℝ k (R • x)) := by
      rw [fderiv_comp_smul]
    _ = (R ^ (d + 1)) • fderiv ℝ k (R • x) := by
      rw [smul_smul, ← pow_succ]

/-- The `L¹` norm of the derivative of a positive Euclidean dilation gains
exactly one factor of the scale. -/
theorem integral_norm_fderiv_dilate_eq
    {d : ℕ} (k : Euclidean d → ℂ) (hk : ContDiff ℝ 1 k)
    {R : ℝ} (hR : 0 < R) :
    (∫ x : Euclidean d,
      ‖fderiv ℝ (fun y : Euclidean d => (R ^ d) • k (R • y)) x‖) =
      R * ∫ x : Euclidean d, ‖fderiv ℝ k x‖ := by
  calc
    (∫ x : Euclidean d,
      ‖fderiv ℝ (fun y : Euclidean d => (R ^ d) • k (R • y)) x‖) =
        ∫ x : Euclidean d,
          ‖R • ((R ^ d) • fderiv ℝ k (R • x))‖ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [fderiv_dilate k hk R x, pow_succ, smul_smul,
          mul_comm (R ^ d) R]
    _ = R * ∫ x : Euclidean d, ‖(R ^ d) • fderiv ℝ k (R • x)‖ := by
      rw [show (fun x : Euclidean d => ‖R • ((R ^ d) • fderiv ℝ k (R • x))‖) =
        fun x => R * ‖(R ^ d) • fderiv ℝ k (R • x)‖ by
          funext x
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR],
        MeasureTheory.integral_const_mul]
    _ = R * ∫ x : Euclidean d, ‖fderiv ℝ k x‖ := by
      rw [integral_norm_dilate_eq d (fderiv ℝ k) hR]

end

end LeanSpherical.HarmonicAnalysis
