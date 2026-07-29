/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# An endpoint parametrization for the semicircle phase

The substitution used near a meridional stationary endpoint is recorded here
as two direct calculus facts.
-/

namespace LeanSpherical.HarmonicAnalysis

noncomputable section

/-- The endpoint parametrization turns the meridional sine into `1 - u²`. -/
theorem sin_pi_div_two_sub_two_arcsin_div_sqrt_two
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.sin (Real.pi / 2 - 2 * Real.arcsin (u / Real.sqrt 2)) = 1 - u ^ 2 := by
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_one : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hquot_nonneg : 0 ≤ u / Real.sqrt 2 := div_nonneg hu0 hsqrt_pos.le
  have hquot_le : u / Real.sqrt 2 ≤ 1 := by
    rw [div_le_iff₀ hsqrt_pos]
    nlinarith
  rw [Real.sin_pi_div_two_sub, Real.cos_two_mul]
  have hcos_sq : Real.cos (Real.arcsin (u / Real.sqrt 2)) ^ 2 =
      1 - (u / Real.sqrt 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.arcsin (u / Real.sqrt 2)),
      Real.sin_arcsin (by linarith : -1 ≤ u / Real.sqrt 2) hquot_le]
  rw [hcos_sq]
  field_simp [hsqrt_pos.ne']
  nlinarith

/-- The derivative of the endpoint parametrization has the explicit
semicircle Jacobian. -/
theorem hasDerivAt_pi_div_two_sub_two_arcsin_div_sqrt_two
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    HasDerivAt
      (fun v : ℝ => Real.pi / 2 - 2 * Real.arcsin (v / Real.sqrt 2))
      (-2 / Real.sqrt (2 - u ^ 2)) u := by
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_one : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hquot_nonneg : 0 ≤ u / Real.sqrt 2 := div_nonneg hu0 hsqrt_pos.le
  have hquot_le : u / Real.sqrt 2 ≤ 1 := by
    rw [div_le_iff₀ hsqrt_pos]
    nlinarith
  have hquot_ne_neg : u / Real.sqrt 2 ≠ -1 := by
    nlinarith
  have hquot_ne_one : u / Real.sqrt 2 ≠ 1 := by
    have hlt : u / Real.sqrt 2 < 1 := by
      rw [div_lt_iff₀ hsqrt_pos]
      nlinarith [hsqrt_sq, Real.sqrt_nonneg (2 : ℝ)]
    nlinarith
  have hdiv : HasDerivAt (fun v : ℝ => v / Real.sqrt 2)
      (1 / Real.sqrt 2) u := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id u).mul_const (Real.sqrt 2)⁻¹
  have harcsin : HasDerivAt
      (fun v : ℝ => Real.arcsin (v / Real.sqrt 2))
      ((1 / Real.sqrt (1 - (u / Real.sqrt 2) ^ 2)) * (1 / Real.sqrt 2)) u := by
    exact (Real.hasDerivAt_arcsin hquot_ne_neg hquot_ne_one).comp u hdiv
  have hphi : HasDerivAt
      (fun v : ℝ => Real.pi / 2 - 2 * Real.arcsin (v / Real.sqrt 2))
      (0 - 2 * ((1 / Real.sqrt (1 - (u / Real.sqrt 2) ^ 2)) *
        (1 / Real.sqrt 2))) u := by
    have h := (hasDerivAt_const u (Real.pi / 2)).sub
      (HasDerivAt.const_mul (2 : ℝ) harcsin)
    change HasDerivAt
      (fun v : ℝ => Real.pi / 2 - 2 * Real.arcsin (v / Real.sqrt 2)) _ u at h
    exact h
  have hinside : 0 < 2 - u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
  have hroot :
      Real.sqrt (1 - (u / Real.sqrt 2) ^ 2) * Real.sqrt 2 =
        Real.sqrt (2 - u ^ 2) := by
    have hleft_nonneg : 0 ≤ 1 - (u / Real.sqrt 2) ^ 2 := by
      rw [show (u / Real.sqrt 2) ^ 2 = u ^ 2 / 2 by
        field_simp [hsqrt_pos.ne']
        nlinarith]
      nlinarith [sq_nonneg (u - 1)]
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (1 - (u / Real.sqrt 2) ^ 2))]
    congr 1
    field_simp [hsqrt_pos.ne']
    nlinarith
  have hcoef :
      0 - 2 * ((1 / Real.sqrt (1 - (u / Real.sqrt 2) ^ 2)) *
        (1 / Real.sqrt 2)) = -2 / Real.sqrt (2 - u ^ 2) := by
    rw [← hroot]
    field_simp [hsqrt_pos.ne', ne_of_gt hinside]
    ring
  rw [hcoef] at hphi
  exact hphi

end

end LeanSpherical.HarmonicAnalysis
