/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.SmoothEndpointAmplitude
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Compact quadratic stationary phase

This file contains the one-dimensional stationary calculation used for the
endpoint symbols in the all-dimensional wave decomposition.  The phase is
the literal quadratic phase produced by the meridian change of variables.
The first lemma below is the scale `lambda^(-1/2)` estimate for an arbitrary
smooth compact endpoint amplitude; higher vanishing orders are obtained from
the exact recurrence added later in this file.

Nothing here is a maximal-function input.  It is an ordinary compact-interval
oscillatory-integral argument, built from the proved quadratic estimate in
`SurfaceDecay`.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Set
open scoped ContDiff

noncomputable section

/-- A quadratic stationary-phase moment.  The factor `u^m` records the
order of vanishing of a meridian density at the stationary endpoint. -/
def quadraticMomentIntegral (m : Nat) (h : Real -> Complex) (lambda : Real) : Complex :=
  ∫ u in (0 : Real)..1,
    ((u ^ m : Real) : Complex) * h u *
      Complex.exp (((lambda * u ^ 2 : Real) : Complex) * Complex.I)

/-- The natural stationary-phase scale of the `m`th endpoint moment.  Writing
the scale using integral powers of `sqrt lambda` avoids hiding the parity
calculation in a real-power identity. -/
def quadraticMomentScale (m : Nat) (lambda : Real) : Real :=
  Real.sqrt lambda ^ (m + 1)

/-- The endpoint-amplitude condition which removes artificial boundary terms
at `u = 1`. -/
def VanishesNearOne (h : Real -> Complex) : Prop :=
  h =ᶠ[𝓝 (1 : Real)] 0

theorem VanishesNearOne.value (h : Real -> Complex) (hh : VanishesNearOne h) :
    h 1 = 0 :=
  hh.self_of_nhds

/-- Vanishing in a neighbourhood persists after taking a derivative. -/
theorem VanishesNearOne.deriv (h : Real -> Complex) (hh : VanishesNearOne h) :
    VanishesNearOne (deriv h) := by
  exact hh.deriv.trans (Filter.Eventually.of_forall fun x => by simp)

/-- A globally smooth amplitude has a positive uniform bound on the unit
interval.  The harmless strict positivity makes it convenient to use as the
constant in the elementary quadratic estimate. -/
theorem exists_pos_norm_le_on_unit_of_contDiff
    (h : Real -> Complex) (hh : ContDiff Real (⊤ : ℕ∞) h) :
    ∃ M : Real, 0 < M ∧ ∀ u ∈ Icc (0 : Real) 1, ‖h u‖ ≤ M := by
  rcases (isCompact_Icc.image_of_continuousOn hh.continuous.continuousOn).isBounded
      .exists_pos_norm_le with ⟨M, hM, hbound⟩
  exact ⟨M, hM, fun u hu => hbound _ (mem_image_of_mem _ hu)⟩

/-- The elementary `lambda^(-1/2)` stationary bound for an arbitrary smooth
amplitude on `[0,1]`.  This is the base case for the endpoint-moment
recurrence, and is proved rather than assumed. -/
theorem exists_quadraticMoment_zero_decay
    (h : Real -> Complex) (hh : ContDiff Real (⊤ : ℕ∞) h) :
    ∃ C : Real, 0 < C ∧ ∀ lambda : Real, 1 ≤ lambda →
      ‖quadraticMomentIntegral 0 h lambda‖ ≤ C / Real.sqrt lambda := by
  obtain ⟨M, hM, hMbound⟩ := exists_pos_norm_le_on_unit_of_contDiff h hh
  obtain ⟨N, hN, hNbound⟩ :=
    exists_pos_norm_le_on_unit_of_contDiff (deriv h)
      ((contDiff_infty_iff_deriv.mp hh).2)
  refine ⟨(5 * M + N) / 2, by positivity, ?_⟩
  intro lambda hlambda
  have hlambda_pos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hsqrt_pos : 0 < Real.sqrt lambda := Real.sqrt_pos.2 hlambda_pos
  let a : Real := 1 / Real.sqrt lambda
  have ha : 0 < a := one_div_pos.mpr hsqrt_pos
  have ha_one : a ≤ 1 := by
    dsimp [a]
    rw [div_le_iff₀ hsqrt_pos]
    simpa using Real.one_le_sqrt.mpr hlambda
  have hscale : lambda * a ^ 2 = 1 := by
    dsimp [a]
    have hsq : Real.sqrt lambda ^ 2 = lambda := Real.sq_sqrt hlambda_pos.le
    field_simp [hsqrt_pos.ne']
    nlinarith
  have hderiv : ∀ u ∈ uIcc a 1, HasDerivAt h (deriv h u) u := by
    intro u hu
    exact ((hh.differentiable (by simp)) u).hasDerivAt
  have hderiv_cont : ContinuousOn (deriv h) (uIcc a 1) := by
    exact (hh.continuous_deriv (by simp)).continuousOn
  have hbound : ∀ u ∈ Icc (0 : Real) 1, ‖h u‖ ≤ M := hMbound
  have hderiv_bound : ∀ u ∈ uIcc a 1, ‖deriv h u‖ ≤ N := by
    intro u hu
    have hu' : u ∈ Icc (0 : Real) 1 := by
      have hu'' : u ∈ Icc a 1 := by
        simpa [uIcc_of_le ha_one] using hu
      exact ⟨le_trans ha.le hu''.1, hu''.2⟩
    exact hNbound u hu'
  have hbase := quadratic_phase_weighted_unit_norm_le
    (a := a) (c := lambda) (M := M) (N := N)
    ha ha_one hlambda_pos hscale hM.le hN.le h (deriv h)
    hh.continuous.continuousOn hderiv hderiv_cont hbound hderiv_bound
  change ‖∫ u in (0 : Real)..1,
      ((u ^ 0 : Real) : Complex) * h u *
        Complex.exp (((lambda * u ^ 2 : Real) : Complex) * Complex.I)‖ ≤ _
  simp only [pow_zero, Nat.cast_one, one_mul] 
  calc
    ‖∫ u in (0 : Real)..1,
        h u * Complex.exp (((lambda * u ^ 2 : Real) : Complex) * Complex.I)‖ ≤
        ((5 * M + N) / 2) * a := hbase
    _ = (5 * M + N) / 2 / Real.sqrt lambda := by
      dsimp [a]
      ring

/-- The exact two-step recurrence behind endpoint stationary phase.  It is
ordinary integration by parts against the derivative of
`exp(i * lambda * u^2)`.  The factor `u^(m+1)` kills the endpoint at zero,
while `VanishesNearOne` kills the artificial endpoint at one. -/
theorem quadraticMomentIntegral_succ_two_recurrence
    (m : Nat) (h : Real -> Complex) (hh : ContDiff Real (⊤ : ℕ∞) h)
    (hvanish : VanishesNearOne h) {lambda : Real} (hlambda : lambda ≠ 0) :
    quadraticMomentIntegral (m + 2) h lambda =
      -((((2 * lambda : Real) : Complex) * Complex.I)⁻¹) *
        (((m + 1 : Nat) : Complex) * quadraticMomentIntegral m h lambda +
          quadraticMomentIntegral (m + 1) (deriv h) lambda) := by
  let E : Real -> Complex := fun u =>
    Complex.exp (((lambda * u ^ 2 : Real) : Complex) * Complex.I)
  let q : Complex := ((2 * lambda : Real) : Complex) * Complex.I
  let s : Complex := q⁻¹
  let U : Real -> Complex := fun u => ((u ^ (m + 1) : Real) : Complex) * h u
  let U' : Real -> Complex := fun u =>
    ((m + 1 : Nat) : Complex) * ((u ^ m : Real) : Complex) * h u +
      ((u ^ (m + 1) : Real) : Complex) * deriv h u
  have hq : q ≠ 0 := by
    dsimp [q]
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hlambda)
    · exact Complex.I_ne_zero
  have hsq : s * q = 1 := by
    dsimp [s]
    exact inv_mul_cancel₀ hq
  have hUderiv (u : Real) : HasDerivAt U (U' u) u := by
    have hpow : HasDerivAt (fun z : Real => ((z ^ (m + 1) : Real) : Complex))
        ((((m + 1 : Nat) : Real) * u ^ m : Real) : Complex) u := by
      exact (hasDerivAt_pow (m + 1) u).ofReal_comp
    have hhderiv : HasDerivAt h (deriv h u) u :=
      ((hh.differentiable (by simp)) u).hasDerivAt
    change HasDerivAt U (U' u) u
    dsimp only [U, U']
    convert hpow.mul hhderiv using 1 <;> push_cast <;> ring
  have hEderiv (u : Real) : HasDerivAt E (E u * (q * (u : Complex))) u := by
    have hpoly : HasDerivAt (fun z : Real => lambda * z ^ 2)
        (lambda * (2 * u)) u := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_pow 2 u).const_mul lambda
    have harg : HasDerivAt
        (fun z : Real => ((lambda * z ^ 2 : Real) : Complex) * Complex.I)
        (((lambda * (2 * u) : Real) : Complex) * Complex.I) u := by
      simpa only [Complex.real_smul] using hpoly.smul_const Complex.I
    change HasDerivAt E (E u * (q * (u : Complex))) u
    dsimp only [E, q]
    convert harg.cexp using 1 <;> push_cast <;> ring
  have hVderiv (u : Real) :
      HasDerivAt (fun z : Real => s * E z) ((u : Complex) * E u) u := by
    have htemp := (hEderiv u).const_mul s
    have hcancel : s * (E u * (q * (u : Complex))) = (u : Complex) * E u := by
      calc
        s * (E u * (q * (u : Complex))) = (s * q) * ((u : Complex) * E u) := by ring
        _ = (u : Complex) * E u := by rw [hsq, one_mul]
    simpa only [hcancel] using htemp
  have hUprime_cont : Continuous U' := by
    dsimp only [U']
    apply Continuous.add
    · exact ((continuous_const.mul (by fun_prop)).mul hh.continuous)
    · exact ((by fun_prop).mul (hh.continuous_deriv (by simp)))
  have hV_cont : Continuous (fun z : Real => s * E z) := by
    dsimp only [E]
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := U) (u' := U') (v := fun z : Real => s * E z)
    (v' := fun z : Real => (z : Complex) * E z)
    (fun z hz => hUderiv z) (fun z hz => hVderiv z)
    hUprime_cont.continuousOn.intervalIntegrable
    hV_cont.continuousOn.intervalIntegrable
  have hUone : U 1 = 0 := by
    dsimp only [U]
    rw [hvanish.value]
    simp
  have hUzero : U 0 = 0 := by
    dsimp only [U]
    have hpos : 0 < m + 1 := by omega
    rw [zero_pow hpos.ne']
    simp
  have hleft :
      (∫ z in (0 : Real)..1, U z * ((z : Complex) * E z)) =
        quadraticMomentIntegral (m + 2) h lambda := by
    unfold quadraticMomentIntegral
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only [U, E]
    have hindex : m + 2 = (m + 1) + 1 := by omega
    rw [hindex, pow_succ]
    push_cast
    ring
  let A : Real -> Complex := fun z =>
    ((m + 1 : Nat) : Complex) * ((z ^ m : Real) : Complex) * h z * E z
  let B : Real -> Complex := fun z =>
    ((z ^ (m + 1) : Real) : Complex) * deriv h z * E z
  have hA_cont : Continuous A := by
    dsimp only [A]
    exact (((continuous_const.mul (by fun_prop)).mul hh.continuous).mul
      (by dsimp only [E]; fun_prop))
  have hB_cont : Continuous B := by
    dsimp only [B]
    exact (((by fun_prop).mul (hh.continuous_deriv (by simp))).mul
      (by dsimp only [E]; fun_prop))
  have hright :
      (∫ z in (0 : Real)..1, U' z * (s * E z)) =
        s * (((m + 1 : Nat) : Complex) * quadraticMomentIntegral m h lambda +
          quadraticMomentIntegral (m + 1) (deriv h) lambda) := by
    calc
      (∫ z in (0 : Real)..1, U' z * (s * E z)) =
          s * (∫ z in (0 : Real)..1, A z + B z) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro z hz
            dsimp only [U', A, B]
            ring
      _ = s * ((∫ z in (0 : Real)..1, A z) + ∫ z in (0 : Real)..1, B z) := by
            rw [intervalIntegral.integral_add
              hA_cont.intervalIntegrable hB_cont.intervalIntegrable]
      _ = s * (((m + 1 : Nat) : Complex) * quadraticMomentIntegral m h lambda +
          quadraticMomentIntegral (m + 1) (deriv h) lambda) := by
            congr 1
            congr 1
            · unfold quadraticMomentIntegral
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro z hz
              dsimp only [A, E]
              ring
            · unfold quadraticMomentIntegral
              apply intervalIntegral.integral_congr
              intro z hz
              dsimp only [B, E]
              ring
  calc
    quadraticMomentIntegral (m + 2) h lambda =
        ∫ z in (0 : Real)..1, U z * ((z : Complex) * E z) := hleft.symm
    _ = U 1 * (s * E 1) - U 0 * (s * E 0) -
          ∫ z in (0 : Real)..1, U' z * (s * E z) := hparts
    _ = -s * (((m + 1 : Nat) : Complex) * quadraticMomentIntegral m h lambda +
          quadraticMomentIntegral (m + 1) (deriv h) lambda) := by
          rw [hUone, hUzero, hright]
          ring
    _ = -((((2 * lambda : Real) : Complex) * Complex.I)⁻¹) *
          (((m + 1 : Nat) : Complex) * quadraticMomentIntegral m h lambda +
            quadraticMomentIntegral (m + 1) (deriv h) lambda) := by
          rfl

/-- The odd base recurrence.  Unlike the two-step formula there is a genuine
boundary contribution at zero; it has size `O(lambda⁻¹)`, exactly as needed
for the `m = 1` stationary moment. -/
theorem quadraticMomentIntegral_one_recurrence
    (h : Real -> Complex) (hh : ContDiff Real (⊤ : ℕ∞) h)
    (hvanish : VanishesNearOne h) {lambda : Real} (hlambda : lambda ≠ 0) :
    quadraticMomentIntegral 1 h lambda =
      -((((2 * lambda : Real) : Complex) * Complex.I)⁻¹) *
        (h 0 + quadraticMomentIntegral 0 (deriv h) lambda) := by
  let E : Real -> Complex := fun u =>
    Complex.exp (((lambda * u ^ 2 : Real) : Complex) * Complex.I)
  let q : Complex := ((2 * lambda : Real) : Complex) * Complex.I
  let s : Complex := q⁻¹
  have hq : q ≠ 0 := by
    dsimp [q]
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hlambda)
    · exact Complex.I_ne_zero
  have hsq : s * q = 1 := by
    dsimp [s]
    exact inv_mul_cancel₀ hq
  have hEderiv (u : Real) : HasDerivAt E (E u * (q * (u : Complex))) u := by
    have hpoly : HasDerivAt (fun z : Real => lambda * z ^ 2)
        (lambda * (2 * u)) u := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_pow 2 u).const_mul lambda
    have harg : HasDerivAt
        (fun z : Real => ((lambda * z ^ 2 : Real) : Complex) * Complex.I)
        (((lambda * (2 * u) : Real) : Complex) * Complex.I) u := by
      simpa only [Complex.real_smul] using hpoly.smul_const Complex.I
    change HasDerivAt E (E u * (q * (u : Complex))) u
    dsimp only [E, q]
    convert harg.cexp using 1 <;> push_cast <;> ring
  have hVderiv (u : Real) :
      HasDerivAt (fun z : Real => s * E z) ((u : Complex) * E u) u := by
    have htemp := (hEderiv u).const_mul s
    have hcancel : s * (E u * (q * (u : Complex))) = (u : Complex) * E u := by
      calc
        s * (E u * (q * (u : Complex))) = (s * q) * ((u : Complex) * E u) := by ring
        _ = (u : Complex) * E u := by rw [hsq, one_mul]
    simpa only [hcancel] using htemp
  have hhderiv (u : Real) : HasDerivAt h (deriv h u) u :=
    ((hh.differentiable (by simp)) u).hasDerivAt
  have hderiv_cont : Continuous (deriv h) := hh.continuous_deriv (by simp)
  have hV_cont : Continuous (fun z : Real => s * E z) := by
    dsimp only [E]
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := h) (u' := deriv h) (v := fun z : Real => s * E z)
    (v' := fun z : Real => (z : Complex) * E z)
    (fun z hz => hhderiv z) (fun z hz => hVderiv z)
    hderiv_cont.continuousOn.intervalIntegrable
    hV_cont.continuousOn.intervalIntegrable
  have hleft :
      (∫ z in (0 : Real)..1, h z * ((z : Complex) * E z)) =
        quadraticMomentIntegral 1 h lambda := by
    unfold quadraticMomentIntegral
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only [E]
    simp only [pow_one]
    push_cast
    ring
  have hright :
      (∫ z in (0 : Real)..1, deriv h z * (s * E z)) =
        s * quadraticMomentIntegral 0 (deriv h) lambda := by
    unfold quadraticMomentIntegral
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only [E]
    simp only [pow_zero, Nat.cast_one, one_mul]
    ring
  calc
    quadraticMomentIntegral 1 h lambda =
        ∫ z in (0 : Real)..1, h z * ((z : Complex) * E z) := hleft.symm
    _ = h 1 * (s * E 1) - h 0 * (s * E 0) -
          ∫ z in (0 : Real)..1, deriv h z * (s * E z) := hparts
    _ = -s * (h 0 + quadraticMomentIntegral 0 (deriv h) lambda) := by
          rw [hvanish.value, hright]
          have hEzero : E 0 = 1 := by
            dsimp only [E]
            norm_num
          rw [hEzero]
          ring
    _ = -((((2 * lambda : Real) : Complex) * Complex.I)⁻¹) *
          (h 0 + quadraticMomentIntegral 0 (deriv h) lambda) := by
          rfl

/-- The `m = 1` compact quadratic stationary estimate. -/
theorem exists_quadraticMoment_one_decay
    (h : Real -> Complex) (hh : ContDiff Real (⊤ : ℕ∞) h)
    (hvanish : VanishesNearOne h) :
    ∃ C : Real, 0 < C ∧ ∀ lambda : Real, 1 ≤ lambda →
      ‖quadraticMomentIntegral 1 h lambda‖ ≤ C / lambda := by
  obtain ⟨M, hM, hMbound⟩ := exists_pos_norm_le_on_unit_of_contDiff h hh
  obtain ⟨N, hN, hNbound⟩ :=
    exists_pos_norm_le_on_unit_of_contDiff (deriv h)
      ((contDiff_infty_iff_deriv.mp hh).2)
  refine ⟨M + N, add_pos hM hN, ?_⟩
  intro lambda hlambda
  have hlambda_pos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hlambda_ne : lambda ≠ 0 := hlambda_pos.ne'
  have hformula := quadraticMomentIntegral_one_recurrence h hh hvanish hlambda_ne
  have hs_norm : ‖(((2 * lambda : Real) : Complex) * Complex.I)⁻¹‖ =
      1 / (2 * lambda) := by
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * lambda), Complex.norm_I, mul_one]
    ring
  have hrest : ‖quadraticMomentIntegral 0 (deriv h) lambda‖ ≤ N := by
    unfold quadraticMomentIntegral
    simp only [pow_zero, Nat.cast_one, one_mul]
    calc
      ‖∫ z in (0 : Real)..1,
          deriv h z * Complex.exp (((lambda * z ^ 2 : Real) : Complex) * Complex.I)‖ ≤
          N * |(1 : Real) - 0| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro z hz
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
            exact hNbound z (by simpa using hz)
      _ = N := by norm_num
  have hzero : ‖h 0‖ ≤ M := hMbound 0 (by norm_num)
  rw [hformula, norm_mul, norm_neg, hs_norm]
  calc
    (1 / (2 * lambda)) * ‖h 0 + quadraticMomentIntegral 0 (deriv h) lambda‖ ≤
        (1 / (2 * lambda)) * (M + N) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hzero hrest)
    _ ≤ (M + N) / lambda := by
          have hnonneg : 0 ≤ M + N := (add_pos hM hN).le
          have htwo : 1 / (2 * lambda) ≤ 1 / lambda := by
            exact one_div_le_one_div_of_le hlambda_pos (by nlinarith)
          calc
            (1 / (2 * lambda)) * (M + N) ≤ (1 / lambda) * (M + N) :=
              mul_le_mul_of_nonneg_right htwo hnonneg
            _ = (M + N) / lambda := by ring

/-- Full compact quadratic stationary phase for every endpoint vanishing
order.  The proof is a strong induction using the exact two-step recurrence
above.  It is the symbol estimate behind the factor
`|xi|^(-(d-1)/2)` in the all-dimensional wave decomposition, rather than a
consequence of a spherical maximal theorem. -/
theorem exists_quadraticMoment_decay
    (m : Nat) (h : Real -> Complex) (hh : ContDiff Real (⊤ : ℕ∞) h)
    (hvanish : VanishesNearOne h) :
    ∃ C : Real, 0 < C ∧ ∀ lambda : Real, 1 ≤ lambda →
      ‖quadraticMomentIntegral m h lambda‖ ≤ C / quadraticMomentScale m lambda := by
  induction m using Nat.strong_induction_on generalizing h with
  | h m ih =>
    rcases m with _ | m
    · obtain ⟨C, hC, hbound⟩ := exists_quadraticMoment_zero_decay h hh
      refine ⟨C, hC, ?_⟩
      intro lambda hlambda
      simpa [quadraticMomentScale] using hbound lambda hlambda
    · rcases m with _ | n
      · obtain ⟨C, hC, hbound⟩ :=
          exists_quadraticMoment_one_decay h hh hvanish
        refine ⟨C, hC, ?_⟩
        intro lambda hlambda
        have hlambda_pos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
        have hsquare : Real.sqrt lambda ^ 2 = lambda :=
          Real.sq_sqrt hlambda_pos.le
        simpa [quadraticMomentScale, hsquare] using hbound lambda hlambda
      · obtain ⟨C₀, hC₀, hbound₀⟩ := ih n (by omega) h hh hvanish
        have hhderiv : ContDiff Real (⊤ : ℕ∞) (deriv h) :=
          (contDiff_infty_iff_deriv.mp hh).2
        obtain ⟨C₁, hC₁, hbound₁⟩ :=
          ih (n + 1) (by omega) (deriv h) hhderiv hvanish.deriv
        let C : Real := ((n + 1 : Nat) : Real) * C₀ + C₁
        have hC : 0 < C := by
          dsimp [C]
          have hcoeff : 0 < ((n + 1 : Nat) : Real) := by positivity
          positivity
        refine ⟨C, hC, ?_⟩
        intro lambda hlambda
        have hlambda_pos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
        have hlambda_ne : lambda ≠ 0 := hlambda_pos.ne'
        let s : Real := Real.sqrt lambda
        have hs_pos : 0 < s := by
          dsimp [s]
          exact Real.sqrt_pos.2 hlambda_pos
        have hs_one : 1 ≤ s := by
          dsimp [s]
          exact Real.one_le_sqrt.mpr hlambda
        have hs_square : s ^ 2 = lambda := by
          dsimp [s]
          exact Real.sq_sqrt hlambda_pos.le
        have hden₀_pos : 0 < s ^ (n + 1) := pow_pos hs_pos _
        have hden₁_pos : 0 < s ^ (n + 2) := pow_pos hs_pos _
        have hden_target_pos : 0 < s ^ (n + 3) := pow_pos hs_pos _
        have hden_next_pos : 0 < s ^ (n + 4) := pow_pos hs_pos _
        have hrec := quadraticMomentIntegral_succ_two_recurrence n h hh hvanish hlambda_ne
        have hqnorm : ‖(((2 * lambda : Real) : Complex) * Complex.I)⁻¹‖ =
            1 / (2 * lambda) := by
          rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity : 0 < 2 * lambda), Complex.norm_I, mul_one]
          ring
        have hsmall₀ : ‖quadraticMomentIntegral n h lambda‖ ≤
            C₀ / s ^ (n + 1) := by
          simpa [quadraticMomentScale, s] using hbound₀ lambda hlambda
        have hsmall₁ : ‖quadraticMomentIntegral (n + 1) (deriv h) lambda‖ ≤
            C₁ / s ^ (n + 2) := by
          simpa [quadraticMomentScale, s] using hbound₁ lambda hlambda
        have hsum :
            ‖((n + 1 : Nat) : Complex) * quadraticMomentIntegral n h lambda +
                quadraticMomentIntegral (n + 1) (deriv h) lambda‖ ≤
              ((n + 1 : Nat) : Real) * (C₀ / s ^ (n + 1)) +
                C₁ / s ^ (n + 2) := by
          calc
            ‖((n + 1 : Nat) : Complex) * quadraticMomentIntegral n h lambda +
                quadraticMomentIntegral (n + 1) (deriv h) lambda‖ ≤
                ‖((n + 1 : Nat) : Complex) * quadraticMomentIntegral n h lambda‖ +
                  ‖quadraticMomentIntegral (n + 1) (deriv h) lambda‖ :=
              norm_add_le _ _
            _ = ((n + 1 : Nat) : Real) * ‖quadraticMomentIntegral n h lambda‖ +
                  ‖quadraticMomentIntegral (n + 1) (deriv h) lambda‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (by positivity : 0 ≤ ((n + 1 : Nat) : Real))]
            _ ≤ ((n + 1 : Nat) : Real) * (C₀ / s ^ (n + 1)) +
                  C₁ / s ^ (n + 2) := by
                apply add_le_add
                · exact mul_le_mul_of_nonneg_left hsmall₀ (by positivity)
                · exact hsmall₁
        have hinv : 1 / (2 * lambda) ≤ 1 / lambda := by
          exact one_div_le_one_div_of_le hlambda_pos (by nlinarith)
        have hsum_nonneg : 0 ≤
            ((n + 1 : Nat) : Real) * (C₀ / s ^ (n + 1)) + C₁ / s ^ (n + 2) := by
          apply add_nonneg
          · exact mul_nonneg (by positivity)
              (div_nonneg hC₀.le hden₀_pos.le)
          · exact div_nonneg hC₁.le hden₁_pos.le
        have hmain :
            ‖quadraticMomentIntegral (n + 2) h lambda‖ ≤
              (1 / (2 * lambda)) *
                (((n + 1 : Nat) : Real) * (C₀ / s ^ (n + 1)) +
                  C₁ / s ^ (n + 2)) := by
          rw [hrec, norm_neg, norm_mul, hqnorm]
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
        have hreplace :
            (1 / (2 * lambda)) *
                (((n + 1 : Nat) : Real) * (C₀ / s ^ (n + 1)) +
                  C₁ / s ^ (n + 2)) ≤
              (1 / lambda) *
                (((n + 1 : Nat) : Real) * (C₀ / s ^ (n + 1)) +
                  C₁ / s ^ (n + 2)) :=
          mul_le_mul_of_nonneg_right hinv hsum_nonneg
        have hrearrange :
            (1 / lambda) *
                (((n + 1 : Nat) : Real) * (C₀ / s ^ (n + 1)) +
                  C₁ / s ^ (n + 2)) =
              (((n + 1 : Nat) : Real) * C₀) / s ^ (n + 3) +
                C₁ / s ^ (n + 4) := by
          rw [← hs_square]
          field_simp [hs_pos.ne']
          ring
        have hpow_le : s ^ (n + 3) ≤ s ^ (n + 4) := by
          calc
            s ^ (n + 3) ≤ s ^ (n + 3) * s :=
              le_mul_of_one_le_right (pow_nonneg hs_pos.le _) hs_one
            _ = s ^ (n + 4) := by
              rw [show n + 4 = (n + 3) + 1 by omega, pow_succ]
        have htail : C₁ / s ^ (n + 4) ≤ C₁ / s ^ (n + 3) := by
          exact div_le_div_of_nonneg_left hC₁.le hden_target_pos hpow_le
        have hcombine :
            (((n + 1 : Nat) : Real) * C₀) / s ^ (n + 3) +
                C₁ / s ^ (n + 4) ≤ C / s ^ (n + 3) := by
          calc
            (((n + 1 : Nat) : Real) * C₀) / s ^ (n + 3) +
                C₁ / s ^ (n + 4) ≤
                (((n + 1 : Nat) : Real) * C₀) / s ^ (n + 3) +
                  C₁ / s ^ (n + 3) := add_le_add_left htail _
            _ = C / s ^ (n + 3) := by
              dsimp [C]
              ring
        simpa [quadraticMomentScale, s] using
          hmain.trans (hreplace.trans (hrearrange.le.trans hcombine))

/-- The concrete smooth endpoint integral is precisely the `m`th quadratic
moment of its separated smooth profile. -/
theorem smoothEndpointQuadraticIntegral_eq_quadraticMomentIntegral
    (m : Nat) (lambda : Real) :
    smoothEndpointQuadraticIntegral m lambda =
      quadraticMomentIntegral m (smoothEndpointProfile m) lambda := by
  unfold smoothEndpointQuadraticIntegral quadraticMomentIntegral
  apply intervalIntegral.integral_congr
  intro u hu
  rw [smoothEndpointAmplitude_eq_monomial_mul_profile]
  ring

/-- Sharp compact stationary phase for the actual smooth endpoint amplitude.
This is the all-dimensional `|lambda|^(-(m+1)/2)` input which is later used
for the signed spherical wave symbols. -/
theorem exists_smoothEndpointQuadraticIntegral_decay
    (m : Nat) :
    ∃ C : Real, 0 < C ∧ ∀ lambda : Real, 1 ≤ lambda →
      ‖smoothEndpointQuadraticIntegral m lambda‖ ≤
        C / quadraticMomentScale m lambda := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_quadraticMoment_decay m (smoothEndpointProfile m)
      (contDiff_smoothEndpointProfile m)
      (smoothEndpointProfile_eventuallyEq_zero_at_one m)
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda
  rw [smoothEndpointQuadraticIntegral_eq_quadraticMomentIntegral]
  exact hbound lambda hlambda

/-- Reversing the quadratic frequency conjugates the concrete smooth endpoint
integral.  This is the signed companion of the outgoing stationary estimate
and is needed for the incoming wave. -/
theorem smoothEndpointQuadraticIntegral_neg_eq_conj
    (m : Nat) (lambda : Real) :
    smoothEndpointQuadraticIntegral m (-lambda) =
      starRingEnd Complex (smoothEndpointQuadraticIntegral m lambda) := by
  unfold smoothEndpointQuadraticIntegral
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro u hu
  unfold smoothEndpointAmplitude
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- The norm of the incoming endpoint integral equals the norm of the
outgoing one at the opposite frequency. -/
theorem norm_smoothEndpointQuadraticIntegral_neg
    (m : Nat) (lambda : Real) :
    ‖smoothEndpointQuadraticIntegral m (-lambda)‖ =
      ‖smoothEndpointQuadraticIntegral m lambda‖ := by
  rw [smoothEndpointQuadraticIntegral_neg_eq_conj, RCLike.norm_conj]

/-- Sharp compact stationary phase for both signs of the concrete endpoint
frequency.  The denominator is written with `|lambda|`, so this statement
can be used unchanged for the two signed waves in the spherical expansion. -/
theorem exists_smoothEndpointQuadraticIntegral_abs_decay
    (m : Nat) :
    ∃ C : Real, 0 < C ∧ ∀ lambda : Real, 1 ≤ |lambda| →
      ‖smoothEndpointQuadraticIntegral m lambda‖ ≤
        C / quadraticMomentScale m |lambda| := by
  obtain ⟨C, hC, hbound⟩ := exists_smoothEndpointQuadraticIntegral_decay m
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda
  by_cases hlambda_nonneg : 0 ≤ lambda
  · rw [abs_of_nonneg hlambda_nonneg]
    exact hbound lambda hlambda
  · have hlambda_neg : lambda < 0 := lt_of_not_ge hlambda_nonneg
    have hminus : 1 ≤ -lambda := by
      rw [← abs_of_neg hlambda_neg]
      exact hlambda
    have hdecay := hbound (-lambda) hminus
    have hnorm : ‖smoothEndpointQuadraticIntegral m lambda‖ =
        ‖smoothEndpointQuadraticIntegral m (-lambda)‖ := by
      convert norm_smoothEndpointQuadraticIntegral_neg m (-lambda) using 1 <;> ring
    calc
      ‖smoothEndpointQuadraticIntegral m lambda‖ =
          ‖smoothEndpointQuadraticIntegral m (-lambda)‖ := hnorm
      _ ≤ C / quadraticMomentScale m (-lambda) := hdecay
      _ = C / quadraticMomentScale m |lambda| := by
        rw [abs_of_neg hlambda_neg]


end

end LeanSpherical.HarmonicAnalysis.FractalDilations
