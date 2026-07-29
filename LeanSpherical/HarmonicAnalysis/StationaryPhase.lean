/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A quadratic stationary-phase tail estimate

An integration-by-parts proof of decay away from the stationary point for a
quadratic oscillatory phase.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory intervalIntegral

noncomputable section

private theorem intervalIntegral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    exact lt_of_lt_of_le ha hx'.1
  have hcont : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.uIcc a b) := by
    refine (continuous_id.pow 2).continuousOn.inv₀ ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (hpos x hx))
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (-(fun y : ℝ => y⁻¹)) ((x ^ 2)⁻¹) x := by
    intro x hx
    simpa using (hasDerivAt_inv (ne_of_gt (hpos x hx))).neg
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun _ : ℝ => (1 : ℝ)) (u' := fun _ : ℝ => (0 : ℝ))
    (v := -(fun y : ℝ => y⁻¹)) (v' := fun y : ℝ => (y ^ 2)⁻¹)
    (fun _ _ => hasDerivAt_const _ (1 : ℝ)) hderiv
    (Continuous.intervalIntegrable (by fun_prop) a b)
    hcont.intervalIntegrable
  simp only [one_mul, Pi.neg_apply, zero_mul, intervalIntegral.integral_zero, sub_zero] at h
  calc
    (∫ t in a..b, (t ^ 2)⁻¹) = -b⁻¹ - -a⁻¹ := h
    _ = a⁻¹ - b⁻¹ := by ring

private theorem quadratic_phase_integration_by_parts {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : c ≠ 0) :
    (∫ t in a..b, Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)) =
      (((2 * c * b : ℝ) : ℂ) * Complex.I)⁻¹ *
          Complex.exp (((c * b ^ 2 : ℝ) : ℂ) * Complex.I) -
        (((2 * c * a : ℝ) : ℂ) * Complex.I)⁻¹ *
          Complex.exp (((c * a ^ 2 : ℝ) : ℂ) * Complex.I) -
        ∫ t in a..b,
          (-(((2 * c : ℝ) : ℂ) * Complex.I) /
            ((((2 * c * t : ℝ) : ℂ) * Complex.I) ^ 2)) *
          Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I) := by
  let E : ℝ → ℂ := fun t => Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)
  let u : ℝ → ℂ := fun t => (((2 * c * t : ℝ) : ℂ) * Complex.I)⁻¹
  let du : ℝ → ℂ := fun t =>
    -(((2 * c : ℝ) : ℂ) * Complex.I) /
      ((((2 * c * t : ℝ) : ℂ) * Complex.I) ^ 2)
  let dE : ℝ → ℂ := fun t =>
    E t * (((2 * c * t : ℝ) : ℂ) * Complex.I)
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    exact lt_of_lt_of_le ha hx'.1
  have hbase_ne : ∀ x ∈ Set.uIcc a b,
      ((2 * c * x : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hpos x hx)
    have hcx : (2 * c * x : ℝ) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hc) hx0
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hcx) Complex.I_ne_zero
  have hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (du x) x := by
    intro x hx
    dsimp [u, du]
    have hbase : HasDerivAt
        (fun y : ℝ => ((2 * c * y : ℝ) : ℂ) * Complex.I)
        (((2 * c : ℝ) : ℂ) * Complex.I) x := by
      have hreal : HasDerivAt (fun y : ℝ => 2 * c * y) (2 * c) x := by
        simpa [mul_assoc] using (hasDerivAt_id x).const_mul (2 * c)
      simpa only [Complex.real_smul] using hreal.smul_const Complex.I
    exact hbase.inv (hbase_ne x hx)
  have hv : ∀ x ∈ Set.uIcc a b, HasDerivAt E (dE x) x := by
    intro x hx
    dsimp [E, dE]
    have hpoly : HasDerivAt
        (fun y : ℝ => ((c * y ^ 2 : ℝ) : ℂ) * Complex.I)
        (((2 * c * x : ℝ) : ℂ) * Complex.I) x := by
      have hreal : HasDerivAt (fun y : ℝ => c * y ^ 2) (2 * c * x) x := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (hasDerivAt_pow 2 x).const_mul c
      simpa only [Complex.real_smul] using hreal.smul_const Complex.I
    simpa [mul_assoc] using hpoly.cexp
  have hdu_cont : ContinuousOn du (Set.uIcc a b) := by
    dsimp [du]
    refine ContinuousOn.div₀ (by fun_prop) (by fun_prop) ?_
    intro x hx
    exact pow_ne_zero 2 (hbase_ne x hx)
  have hdE_cont : ContinuousOn dE (Set.uIcc a b) := by
    dsimp [dE, E]
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    hdu_cont.intervalIntegrable hdE_cont.intervalIntegrable
  have hleft :
      (∫ t in a..b, E t) = ∫ t in a..b, u t * dE t := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [u, dE]
    have hcx : ((2 * c * x : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hc) (ne_of_gt (hpos x hx))
    field_simp [hbase_ne x hx, hcx]
  dsimp [E, u, du] at hparts hleft ⊢
  rw [hleft, hparts]

private theorem quadratic_phase_endpoint_norm {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ‖(((2 * c * x : ℝ) : ℂ) * Complex.I)⁻¹ *
        Complex.exp (((c * x ^ 2 : ℝ) : ℂ) * Complex.I)‖ =
      (2 * c * x)⁻¹ := by
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), Complex.norm_exp_ofReal_mul_I]
  simp [Complex.norm_I]

private theorem quadratic_phase_remainder_norm_le {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) :
    ‖∫ t in a..b,
        (-(((2 * c : ℝ) : ℂ) * Complex.I) /
          ((((2 * c * t : ℝ) : ℂ) * Complex.I) ^ 2)) *
        Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      (2 * c)⁻¹ * (a⁻¹ - b⁻¹) := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    exact lt_of_lt_of_le ha hx'.1
  have hinvsq := intervalIntegral_inv_sq ha hab
  calc
    ‖∫ t in a..b,
        (-(((2 * c : ℝ) : ℂ) * Complex.I) /
          ((((2 * c * t : ℝ) : ℂ) * Complex.I) ^ 2)) *
        Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        ∫ t in a..b,
          ‖(-(((2 * c : ℝ) : ℂ) * Complex.I) /
            ((((2 * c * t : ℝ) : ℂ) * Complex.I) ^ 2)) *
            Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b, (2 * c)⁻¹ * (t ^ 2)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp
      have hxpos : 0 < x := hpos x hx
      rw [norm_mul, norm_div, norm_neg, norm_mul, norm_pow, norm_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity), abs_of_pos (by positivity),
        Complex.norm_exp_ofReal_mul_I]
      simp [Complex.norm_I]
      field_simp
    _ = (2 * c)⁻¹ * (∫ t in a..b, (t ^ 2)⁻¹) :=
      intervalIntegral.integral_const_mul _ _
    _ = (2 * c)⁻¹ * (a⁻¹ - b⁻¹) := by rw [hinvsq]

theorem quadratic_phase_tail_norm_le_inv {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) :
    ‖∫ t in a..b, Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤ (c * a)⁻¹ := by
  have hparts := quadratic_phase_integration_by_parts ha hab hc.ne'
  have hrem := quadratic_phase_remainder_norm_le ha hab hc
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hendpoint_b := quadratic_phase_endpoint_norm hc hb
  have hendpoint_a := quadratic_phase_endpoint_norm hc ha
  calc
    ‖∫ t in a..b, Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ =
        ‖(((2 * c * b : ℝ) : ℂ) * Complex.I)⁻¹ *
            Complex.exp (((c * b ^ 2 : ℝ) : ℂ) * Complex.I) -
          (((2 * c * a : ℝ) : ℂ) * Complex.I)⁻¹ *
            Complex.exp (((c * a ^ 2 : ℝ) : ℂ) * Complex.I) -
          ∫ t in a..b,
            (-(((2 * c : ℝ) : ℂ) * Complex.I) /
              ((((2 * c * t : ℝ) : ℂ) * Complex.I) ^ 2)) *
            Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ := by rw [hparts]
    _ ≤ ‖(((2 * c * b : ℝ) : ℂ) * Complex.I)⁻¹ *
            Complex.exp (((c * b ^ 2 : ℝ) : ℂ) * Complex.I) -
          (((2 * c * a : ℝ) : ℂ) * Complex.I)⁻¹ *
            Complex.exp (((c * a ^ 2 : ℝ) : ℂ) * Complex.I)‖ +
          ‖∫ t in a..b,
            (-(((2 * c : ℝ) : ℂ) * Complex.I) /
              ((((2 * c * t : ℝ) : ℂ) * Complex.I) ^ 2)) *
            Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ :=
      norm_sub_le _ _
    _ ≤ (‖(((2 * c * b : ℝ) : ℂ) * Complex.I)⁻¹ *
            Complex.exp (((c * b ^ 2 : ℝ) : ℂ) * Complex.I)‖ +
          ‖(((2 * c * a : ℝ) : ℂ) * Complex.I)⁻¹ *
            Complex.exp (((c * a ^ 2 : ℝ) : ℂ) * Complex.I)‖) +
          ‖∫ t in a..b,
            (-(((2 * c : ℝ) : ℂ) * Complex.I) /
              ((((2 * c * t : ℝ) : ℂ) * Complex.I) ^ 2)) *
            Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ :=
      add_le_add_left (norm_sub_le _ _) _
    _ = (2 * c * b)⁻¹ + (2 * c * a)⁻¹ +
          ‖∫ t in a..b,
            (-(((2 * c : ℝ) : ℂ) * Complex.I) /
              ((((2 * c * t : ℝ) : ℂ) * Complex.I) ^ 2)) *
            Complex.exp (((c * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ := by
      rw [hendpoint_b, hendpoint_a]
    _ ≤ (2 * c * b)⁻¹ + (2 * c * a)⁻¹ +
          (2 * c)⁻¹ * (a⁻¹ - b⁻¹) := by
      gcongr
    _ = (c * a)⁻¹ := by
      field_simp
      ring

end

end LeanSpherical.HarmonicAnalysis
