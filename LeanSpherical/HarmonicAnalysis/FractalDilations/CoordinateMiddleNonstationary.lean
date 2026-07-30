/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.CoordinateMeridianWaves
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The literal nonstationary coordinate remainder

The coordinate endpoint waves in `CoordinateMeridianWaves` are deliberately
cut off in the variable `sqrt (1 - sin theta)`.  Written that way, the cutoff
looks singular at a stationary pole, even though it is constant there.  The
elementary half-angle identities in this file replace it, on the meridian, by
an exactly equal smooth cutoff.  Consequently the coordinate middle term is
an honest compact nonstationary oscillatory integral, not a formal error
term.

The construction is used below the endpoint stationary calculation: it keeps
the concrete `smoothEndpointQuadraticIntegral` symbols of the coordinate
bridge while making the remainder available for ordinary integration by
parts.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Metric Set
open scoped ContDiff

noncomputable section

/-- A globally smooth representative of the north-pole coordinate cutoff.
On the upper half of the meridian it is exactly
`endpointCoreCutoff (sqrt (1 - sin theta))`. -/
noncomputable def coordinateUpperMeridianCutoff (theta : Real) : Real :=
  endpointCoreCutoff
    (Real.sqrt 2 * Real.sin (Real.pi / 4 - theta / 2))

/-- The reflected globally smooth representative of the south-pole
coordinate cutoff. -/
noncomputable def coordinateLowerMeridianCutoff (theta : Real) : Real :=
  endpointCoreCutoff
    (Real.sqrt 2 * Real.sin (Real.pi / 4 + theta / 2))

/-- The smooth complement of the two literal coordinate endpoint cutoffs. -/
noncomputable def coordinateMiddleMeridianCutoff (theta : Real) : Real :=
  1 - coordinateUpperMeridianCutoff theta - coordinateLowerMeridianCutoff theta

/-- The north-pole half-angle identity underlying the smooth replacement of
the coordinate cutoff. -/
theorem sqrt_one_sub_sin_eq_coordinateUpperArgument
    {theta : Real} (htheta : theta ∈ Icc (0 : Real) (Real.pi / 2)) :
    Real.sqrt (1 - Real.sin theta) =
      Real.sqrt 2 * Real.sin (Real.pi / 4 - theta / 2) := by
  let a : Real := Real.pi / 4 - theta / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith [htheta.2]
  have ha_pi : a ≤ Real.pi := by
    dsimp [a]
    linarith [htheta.1, Real.pi_pos]
  have hsin : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha0 ha_pi
  have hrhs : 0 ≤ Real.sqrt 2 * Real.sin a :=
    mul_nonneg (Real.sqrt_nonneg _) hsin
  apply (Real.sqrt_eq_iff_eq_sq (by
    have : Real.sin theta ≤ 1 := Real.sin_le_one theta
    linarith) hrhs).2
  have hdouble : 2 * a = Real.pi / 2 - theta := by
    dsimp [a]
    ring
  calc
    1 - Real.sin theta = 1 - Real.cos (Real.pi / 2 - theta) := by
      rw [Real.cos_pi_div_two_sub]
    _ = 1 - Real.cos (2 * a) := by rw [hdouble]
    _ = 2 * Real.sin a ^ 2 := by
      rw [Real.cos_two_mul_eq_one_sub]
      ring
    _ = (Real.sqrt 2 * Real.sin a) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
      ring

/-- The reflected half-angle identity at the south pole. -/
theorem sqrt_one_add_sin_eq_coordinateLowerArgument
    {theta : Real} (htheta : theta ∈ Icc (-(Real.pi / 2) : Real) 0) :
    Real.sqrt (1 + Real.sin theta) =
      Real.sqrt 2 * Real.sin (Real.pi / 4 + theta / 2) := by
  have hneg : -theta ∈ Icc (0 : Real) (Real.pi / 2) := by
    constructor <;> linarith [htheta.1, htheta.2]
  have h := sqrt_one_sub_sin_eq_coordinateUpperArgument hneg
  rw [Real.sin_neg] at h
  simpa [sub_eq_add_neg] using h

/-- On the upper half-meridian the smooth representative agrees exactly with
the cutoff used in `coordinateUpperMeridianLocalizedIntegral`. -/
theorem coordinateUpperMeridianCutoff_eq_coordinate
    {theta : Real} (htheta : theta ∈ Icc (0 : Real) (Real.pi / 2)) :
    coordinateUpperMeridianCutoff theta =
      endpointCoreCutoff (Real.sqrt (1 - Real.sin theta)) := by
  unfold coordinateUpperMeridianCutoff
  rw [sqrt_one_sub_sin_eq_coordinateUpperArgument htheta]

/-- On the lower half-meridian the smooth representative agrees exactly with
the cutoff used in `coordinateLowerMeridianLocalizedIntegral`. -/
theorem coordinateLowerMeridianCutoff_eq_coordinate
    {theta : Real} (htheta : theta ∈ Icc (-(Real.pi / 2) : Real) 0) :
    coordinateLowerMeridianCutoff theta =
      endpointCoreCutoff (Real.sqrt (1 + Real.sin theta)) := by
  unfold coordinateLowerMeridianCutoff
  rw [sqrt_one_add_sin_eq_coordinateLowerArgument htheta]

/-- Both representatives are globally smooth; no square root remains in
their defining formulas. -/
theorem contDiff_coordinateUpperMeridianCutoff :
    ContDiff Real (⊤ : ℕ∞) coordinateUpperMeridianCutoff := by
  unfold coordinateUpperMeridianCutoff endpointCoreCutoff
  apply endpointCoreBump.contDiff.comp
  fun_prop

theorem contDiff_coordinateLowerMeridianCutoff :
    ContDiff Real (⊤ : ℕ∞) coordinateLowerMeridianCutoff := by
  unfold coordinateLowerMeridianCutoff endpointCoreCutoff
  apply endpointCoreBump.contDiff.comp
  fun_prop

/-- The literal coordinate middle cutoff is smooth. -/
theorem contDiff_coordinateMiddleMeridianCutoff :
    ContDiff Real (⊤ : ℕ∞) coordinateMiddleMeridianCutoff := by
  unfold coordinateMiddleMeridianCutoff
  exact (contDiff_const.sub contDiff_coordinateUpperMeridianCutoff).sub
    contDiff_coordinateLowerMeridianCutoff

/-- Reflection exchanges the two smooth coordinate cutoffs. -/
theorem coordinateLowerMeridianCutoff_eq_upper_neg (theta : Real) :
    coordinateLowerMeridianCutoff theta = coordinateUpperMeridianCutoff (-theta) := by
  unfold coordinateLowerMeridianCutoff coordinateUpperMeridianCutoff
  congr 2
  rw [neg_div, sub_neg_eq_add]

private theorem one_le_sqrt_two : (1 : Real) ≤ Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2), Real.sqrt_nonneg (2 : Real)]

private theorem sqrt_two_le_two : Real.sqrt 2 ≤ (2 : Real) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2), Real.sqrt_nonneg (2 : Real)]

/-- The north-pole coordinate cutoff has already vanished by the central
quarter of the meridian.  This is the support fact which removes it from the
opposite half of the full meridian integral. -/
theorem coordinateUpperMeridianCutoff_eq_zero_of_le_pi_div_four
    {theta : Real} (htheta : theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hle : theta ≤ Real.pi / 4) :
    coordinateUpperMeridianCutoff theta = 0 := by
  let a : Real := Real.pi / 4 - theta / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    nlinarith [htheta.2]
  have ha_half : a ≤ Real.pi / 2 := by
    dsimp [a]
    nlinarith [htheta.1]
  have ha_eighth : Real.pi / 8 ≤ a := by
    dsimp [a]
    nlinarith
  have hsin_nonneg : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha0 (le_trans ha_half (by linarith [Real.pi_pos]))
  have hsin_lower : (1 / 4 : Real) ≤ Real.sin a := by
    calc
      (1 / 4 : Real) = (2 / Real.pi) * (Real.pi / 8) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ (2 / Real.pi) * a := by
        apply mul_le_mul_of_nonneg_left ha_eighth
        positivity
      _ ≤ Real.sin a := Real.mul_le_sin ha0 ha_half
  have harg : (1 / 4 : Real) ≤ Real.sqrt 2 * Real.sin a := by
    calc
      (1 / 4 : Real) = 1 * (1 / 4 : Real) := by ring
      _ ≤ Real.sqrt 2 * (1 / 4 : Real) := by
        exact mul_le_mul_of_nonneg_right one_le_sqrt_two (by norm_num)
      _ ≤ Real.sqrt 2 * Real.sin a := by
        exact mul_le_mul_of_nonneg_left hsin_lower (Real.sqrt_nonneg _)
  have harg_nonneg : 0 ≤ Real.sqrt 2 * Real.sin a :=
    mul_nonneg (Real.sqrt_nonneg _) hsin_nonneg
  unfold coordinateUpperMeridianCutoff endpointCoreCutoff
  apply endpointCoreBump.zero_of_le_dist
  change (1 / 4 : Real) ≤ dist (Real.sqrt 2 * Real.sin a) 0
  rw [Real.dist_eq, abs_of_nonneg harg_nonneg]
  exact harg

/-- Close enough to its stationary pole, the north coordinate cutoff is
identically one.  The deliberately inessential rational constants give a
convenient fixed open neighbourhood on which the middle term vanishes. -/
theorem coordinateUpperMeridianCutoff_eq_one_of_fifteen_pi_div_thirty_two_le
    {theta : Real} (htheta : theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hle : 15 * Real.pi / 32 ≤ theta) :
    coordinateUpperMeridianCutoff theta = 1 := by
  let a : Real := Real.pi / 4 - theta / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    nlinarith [htheta.2]
  have ha_small : a ≤ Real.pi / 64 := by
    dsimp [a]
    nlinarith
  have hsin_nonneg : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha0 (by
      calc
        a ≤ Real.pi / 64 := ha_small
        _ ≤ Real.pi := by nlinarith [Real.pi_pos])
  have hsin_le : Real.sin a ≤ a := Real.sin_le ha0
  have harg_nonneg : 0 ≤ Real.sqrt 2 * Real.sin a :=
    mul_nonneg (Real.sqrt_nonneg _) hsin_nonneg
  have harg_small : Real.sqrt 2 * Real.sin a ≤ (1 / 8 : Real) := by
    calc
      Real.sqrt 2 * Real.sin a ≤ 2 * Real.sin a :=
        mul_le_mul_of_nonneg_right sqrt_two_le_two hsin_nonneg
      _ ≤ 2 * a := mul_le_mul_of_nonneg_left hsin_le (by norm_num)
      _ ≤ 1 / 8 := by
        calc
          2 * a ≤ 2 * (Real.pi / 64) :=
            mul_le_mul_of_nonneg_left ha_small (by norm_num)
          _ ≤ 1 / 8 := by nlinarith [Real.pi_le_four]
  unfold coordinateUpperMeridianCutoff endpointCoreCutoff
  apply endpointCoreBump.one_of_mem_closedBall
  change dist (Real.sqrt 2 * Real.sin a) 0 ≤ (1 / 8 : Real)
  rw [Real.dist_eq, abs_of_nonneg harg_nonneg]
  exact harg_small

/-- Reflection gives the corresponding south-pole support statement. -/
theorem coordinateLowerMeridianCutoff_eq_zero_of_neg_pi_div_four_le
    {theta : Real} (htheta : theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hle : -(Real.pi / 4) ≤ theta) :
    coordinateLowerMeridianCutoff theta = 0 := by
  rw [coordinateLowerMeridianCutoff_eq_upper_neg]
  apply coordinateUpperMeridianCutoff_eq_zero_of_le_pi_div_four
  · constructor <;> linarith [htheta.1, htheta.2]
  · linarith

theorem coordinateLowerMeridianCutoff_eq_one_of_theta_le_neg_fifteen_pi_div_thirty_two
    {theta : Real} (htheta : theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hle : theta ≤ -(15 * Real.pi / 32)) :
    coordinateLowerMeridianCutoff theta = 1 := by
  rw [coordinateLowerMeridianCutoff_eq_upper_neg]
  apply coordinateUpperMeridianCutoff_eq_one_of_fifteen_pi_div_thirty_two_le
  · constructor <;> linarith [htheta.1, htheta.2]
  · linarith

/-- The coordinate middle cutoff vanishes in fixed neighbourhoods of both
stationary poles.  This is the exact compact nonstationarity fact needed for
the meridional integration-by-parts argument. -/
theorem coordinateMiddleMeridianCutoff_eq_zero_of_large_abs
    {theta : Real} (htheta : theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hlarge : 15 * Real.pi / 32 ≤ |theta|) :
    coordinateMiddleMeridianCutoff theta = 0 := by
  by_cases hnonneg : 0 ≤ theta
  · have htheta_large : 15 * Real.pi / 32 ≤ theta := by
      rwa [abs_of_nonneg hnonneg] at hlarge
    have hupper : coordinateUpperMeridianCutoff theta = 1 :=
      coordinateUpperMeridianCutoff_eq_one_of_fifteen_pi_div_thirty_two_le
        htheta htheta_large
    have hlower : coordinateLowerMeridianCutoff theta = 0 :=
      coordinateLowerMeridianCutoff_eq_zero_of_neg_pi_div_four_le htheta (by
        nlinarith [htheta_large, Real.pi_pos])
    unfold coordinateMiddleMeridianCutoff
    rw [hupper, hlower]
    ring
  · have hnonpos : theta ≤ 0 := le_of_not_ge hnonneg
    have htheta_large : theta ≤ -(15 * Real.pi / 32) := by
      rw [abs_of_nonpos hnonpos] at hlarge
      linarith
    have hlower : coordinateLowerMeridianCutoff theta = 1 :=
      coordinateLowerMeridianCutoff_eq_one_of_theta_le_neg_fifteen_pi_div_thirty_two
        htheta htheta_large
    have hupper : coordinateUpperMeridianCutoff theta = 0 :=
      coordinateUpperMeridianCutoff_eq_zero_of_le_pi_div_four htheta (by
        nlinarith [htheta_large, Real.pi_pos])
    unfold coordinateMiddleMeridianCutoff
    rw [hupper, hlower]
    ring

/-- The full-meridian representative of the upper coordinate piece.  The
smooth cutoff is identically zero on the lower half, so this is exactly the
localized integral appearing in the coordinate wave bridge. -/
theorem coordinateUpperMeridianLocalizedIntegral_eq_full_cutoff
    (m : Nat) (l : Real) :
    coordinateUpperMeridianLocalizedIntegral m l =
      ∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
        (coordinateUpperMeridianCutoff theta : Complex) *
          ((Real.cos theta ^ m : Real) : Complex) *
            Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I) := by
  let a : Real := -(Real.pi / 2)
  let b : Real := Real.pi / 2
  let F : Real -> Complex := fun theta =>
    (coordinateUpperMeridianCutoff theta : Complex) *
      ((Real.cos theta ^ m : Real) : Complex) *
        Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hneg : (∫ theta in a..0, F theta) = 0 := by
    calc
      (∫ theta in a..0, F theta) = ∫ theta in a..0, (0 : Complex) := by
        apply intervalIntegral.integral_congr
        intro theta htheta
        have htheta' : theta ∈ Icc (-(Real.pi / 2) : Real) 0 := by
          simpa only [a, uIcc_of_le (by linarith [Real.pi_pos])] using htheta
        have hcut := coordinateUpperMeridianCutoff_eq_zero_of_le_pi_div_four
          (show theta ∈ Icc (-(Real.pi / 2) : Real) (Real.pi / 2) by
            constructor
            · exact htheta'.1
            · linarith [Real.pi_pos])
          (by linarith [htheta'.2, Real.pi_pos])
        dsimp [F]
        rw [hcut]
        simp
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable a 0) (hF.intervalIntegrable 0 b)
  unfold coordinateUpperMeridianLocalizedIntegral
  change (∫ theta in (0 : Real)..b,
      (endpointCoreCutoff (Real.sqrt (1 - Real.sin theta)) : Complex) *
        ((Real.cos theta ^ m : Real) : Complex) *
          Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I) =
      ∫ theta in a..b, F theta
  rw [← hsplit, hneg, zero_add]
  apply intervalIntegral.integral_congr
  intro theta htheta
  have htheta' : theta ∈ Icc (0 : Real) (Real.pi / 2) := by
    simpa only [b, uIcc_of_le (by norm_num : (0 : Real) ≤ Real.pi / 2)] using htheta
  have hcut := coordinateUpperMeridianCutoff_eq_coordinate htheta'
  dsimp [F]
  rw [hcut]

/-- The full-meridian representative of the lower coordinate piece. -/
theorem coordinateLowerMeridianLocalizedIntegral_eq_full_cutoff
    (m : Nat) (l : Real) :
    coordinateLowerMeridianLocalizedIntegral m l =
      ∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
        (coordinateLowerMeridianCutoff theta : Complex) *
          ((Real.cos theta ^ m : Real) : Complex) *
            Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I) := by
  let a : Real := -(Real.pi / 2)
  let b : Real := Real.pi / 2
  let F : Real -> Complex := fun theta =>
    (coordinateLowerMeridianCutoff theta : Complex) *
      ((Real.cos theta ^ m : Real) : Complex) *
        Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hpos : (∫ theta in (0 : Real)..b, F theta) = 0 := by
    calc
      (∫ theta in (0 : Real)..b, F theta) = ∫ theta in (0 : Real)..b, (0 : Complex) := by
        apply intervalIntegral.integral_congr
        intro theta htheta
        have htheta' : theta ∈ Icc (0 : Real) (Real.pi / 2) := by
          simpa only [b, uIcc_of_le (by norm_num : (0 : Real) ≤ Real.pi / 2)] using htheta
        have hcut := coordinateLowerMeridianCutoff_eq_zero_of_neg_pi_div_four_le
          (show theta ∈ Icc (-(Real.pi / 2) : Real) (Real.pi / 2) by
            constructor
            · linarith [Real.pi_pos]
            · exact htheta'.2)
          (by linarith [htheta'.1, Real.pi_pos])
        dsimp [F]
        rw [hcut]
        simp
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable a 0) (hF.intervalIntegrable 0 b)
  unfold coordinateLowerMeridianLocalizedIntegral
  change (∫ theta in a..(0 : Real),
      (endpointCoreCutoff (Real.sqrt (1 + Real.sin theta)) : Complex) *
        ((Real.cos theta ^ m : Real) : Complex) *
          Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I) =
      ∫ theta in a..b, F theta
  rw [← hsplit, hpos, add_zero]
  apply intervalIntegral.integral_congr
  intro theta htheta
  have htheta' : theta ∈ Icc (-(Real.pi / 2) : Real) 0 := by
    simpa only [a, uIcc_of_le (by linarith [Real.pi_pos])] using htheta
  have hcut := coordinateLowerMeridianCutoff_eq_coordinate htheta'
  dsimp [F]
  rw [hcut]

/-- The subtraction-defined coordinate remainder is exactly the smooth
middle-cutoff meridian integral.  This is the literal bridge needed before
the nonstationary argument; no model remainder is introduced. -/
theorem coordinateMiddleMeridianLocalizedIntegral_eq_middle_cutoff
    (m : Nat) (l : Real) :
    coordinateMiddleMeridianLocalizedIntegral m l =
      ∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
        (coordinateMiddleMeridianCutoff theta : Complex) *
          ((Real.cos theta ^ m : Real) : Complex) *
            Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I) := by
  let a : Real := -(Real.pi / 2)
  let b : Real := Real.pi / 2
  let G : Real -> Complex := fun theta =>
    ((Real.cos theta ^ m : Real) : Complex) *
      Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)
  let U : Real -> Complex := fun theta =>
    (coordinateUpperMeridianCutoff theta : Complex) * G theta
  let L : Real -> Complex := fun theta =>
    (coordinateLowerMeridianCutoff theta : Complex) * G theta
  let M : Real -> Complex := fun theta =>
    (coordinateMiddleMeridianCutoff theta : Complex) * G theta
  have hG : Continuous G := by
    dsimp [G]
    fun_prop
  have hU : Continuous U := by
    dsimp [U]
    exact (Complex.continuous_ofReal.comp
      contDiff_coordinateUpperMeridianCutoff.continuous).mul hG
  have hL : Continuous L := by
    dsimp [L]
    exact (Complex.continuous_ofReal.comp
      contDiff_coordinateLowerMeridianCutoff.continuous).mul hG
  have hM : Continuous M := by
    dsimp [M]
    exact (Complex.continuous_ofReal.comp
      contDiff_coordinateMiddleMeridianCutoff.continuous).mul hG
  have hUint : IntervalIntegrable U volume a b := hU.intervalIntegrable a b
  have hLint : IntervalIntegrable L volume a b := hL.intervalIntegrable a b
  have hMint : IntervalIntegrable M volume a b := hM.intervalIntegrable a b
  have hpartition : (∫ theta in a..b, G theta) =
      (∫ theta in a..b, U theta) + (∫ theta in a..b, L theta) +
        ∫ theta in a..b, M theta := by
    have hpoint (theta : Real) : G theta = U theta + L theta + M theta := by
      dsimp [U, L, M]
      have hcuts : (coordinateUpperMeridianCutoff theta : Complex) +
          (coordinateLowerMeridianCutoff theta : Complex) +
            (coordinateMiddleMeridianCutoff theta : Complex) = 1 := by
        norm_cast
        unfold coordinateMiddleMeridianCutoff
        ring
      calc
        G theta = (1 : Complex) * G theta := by ring
        _ = ((coordinateUpperMeridianCutoff theta : Complex) +
            (coordinateLowerMeridianCutoff theta : Complex) +
              (coordinateMiddleMeridianCutoff theta : Complex)) * G theta := by rw [hcuts]
        _ = _ := by ring
    simp_rw [hpoint]
    calc
      (∫ theta in a..b, U theta + L theta + M theta) =
          (∫ theta in a..b, (U theta + L theta) + M theta) := by rfl
      _ = (∫ theta in a..b, U theta + L theta) + ∫ theta in a..b, M theta :=
          intervalIntegral.integral_add (hUint.add hLint) hMint
      _ = (∫ theta in a..b, U theta) + (∫ theta in a..b, L theta) +
          ∫ theta in a..b, M theta := by
          rw [intervalIntegral.integral_add hUint hLint]
  unfold coordinateMiddleMeridianLocalizedIntegral
  rw [coordinateUpperMeridianLocalizedIntegral_eq_full_cutoff,
    coordinateLowerMeridianLocalizedIntegral_eq_full_cutoff]
  change (∫ theta in a..b, G theta) - (∫ theta in a..b, U theta) -
      (∫ theta in a..b, L theta) = ∫ theta in a..b, M theta
  rw [hpartition]
  ring

/-- A fixed guard for dividing the coordinate middle amplitude by cosine.
It is one on the possible support of the middle cutoff and vanishes before
the meridian poles. -/
noncomputable def coordinateMiddleGuardBump : ContDiffBump (0 : Real) :=
  ⟨15 * Real.pi / 32, 31 * Real.pi / 64, by positivity,
    by nlinarith [Real.pi_pos]⟩

noncomputable def coordinateMiddleGuardCutoff (theta : Real) : Real :=
  coordinateMiddleGuardBump theta

/-- A globally nonvanishing smooth extension of cosine which agrees with
cosine everywhere the coordinate middle cutoff can be nonzero. -/
noncomputable def coordinateMiddleCosineGuard (theta : Real) : Real :=
  coordinateMiddleGuardCutoff theta * Real.cos theta +
    (1 - coordinateMiddleGuardCutoff theta)

/-- The compact angular amplitude after one variable-phase integration by
parts.  For `m = 0` this is the planar quotient; for positive `m` it includes
the remaining power of cosine. -/
noncomputable def coordinateMiddleIBPAmplitudeReal (m : Nat) (theta : Real) : Real :=
  (coordinateMiddleMeridianCutoff theta * Real.cos theta ^ (m - 1)) /
    coordinateMiddleCosineGuard theta

noncomputable def coordinateMiddleIBPAmplitude (m : Nat) (theta : Real) : Complex :=
  (coordinateMiddleIBPAmplitudeReal m theta : Complex)

private theorem coordinateMiddleGuardBump_rIn : coordinateMiddleGuardBump.rIn =
    15 * Real.pi / 32 := rfl

private theorem coordinateMiddleGuardBump_rOut : coordinateMiddleGuardBump.rOut =
    31 * Real.pi / 64 := rfl

/-- The guard is one on the full possible support of the coordinate middle
cutoff. -/
theorem coordinateMiddleGuardCutoff_eq_one_of_abs_le
    {theta : Real} (htheta : |theta| ≤ 15 * Real.pi / 32) :
    coordinateMiddleGuardCutoff theta = 1 := by
  unfold coordinateMiddleGuardCutoff
  apply coordinateMiddleGuardBump.one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq, coordinateMiddleGuardBump_rIn]
  simpa using htheta

/-- The guarded cosine is strictly positive on the real line. -/
theorem coordinateMiddleCosineGuard_pos (theta : Real) :
    0 < coordinateMiddleCosineGuard theta := by
  by_cases hzero : coordinateMiddleGuardCutoff theta = 0
  · simp [coordinateMiddleCosineGuard, hzero]
  · have hnonneg : 0 ≤ coordinateMiddleGuardCutoff theta := by
      unfold coordinateMiddleGuardCutoff
      exact ContDiffBump.nonneg' coordinateMiddleGuardBump theta
    have hpos : 0 < coordinateMiddleGuardCutoff theta :=
      lt_of_le_of_ne hnonneg (Ne.symm hzero)
    have hdist : dist theta 0 < coordinateMiddleGuardBump.rOut := by
      apply lt_of_not_ge
      intro hge
      apply hzero
      unfold coordinateMiddleGuardCutoff
      exact coordinateMiddleGuardBump.zero_of_le_dist hge
    have habs : |theta| < 31 * Real.pi / 64 := by
      rw [Real.dist_eq, coordinateMiddleGuardBump_rOut] at hdist
      simpa using hdist
    have htheta : theta ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [abs_lt] at habs
      constructor <;> nlinarith [Real.pi_pos]
    have hcos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo htheta
    have hle : coordinateMiddleGuardCutoff theta ≤ 1 := by
      unfold coordinateMiddleGuardCutoff
      exact ContDiffBump.le_one coordinateMiddleGuardBump
    unfold coordinateMiddleCosineGuard
    exact add_pos_of_pos_of_nonneg (mul_pos hpos hcos) (sub_nonneg.mpr hle)

/-- The guarded quotient is globally smooth. -/
theorem contDiff_coordinateMiddleCosineGuard :
    ContDiff Real (⊤ : ℕ∞) coordinateMiddleCosineGuard := by
  unfold coordinateMiddleCosineGuard coordinateMiddleGuardCutoff
  exact (coordinateMiddleGuardBump.contDiff.mul Real.contDiff_cos).add
    (contDiff_const.sub coordinateMiddleGuardBump.contDiff)

theorem contDiff_coordinateMiddleIBPAmplitudeReal (m : Nat) :
    ContDiff Real (⊤ : ℕ∞) (coordinateMiddleIBPAmplitudeReal m) := by
  unfold coordinateMiddleIBPAmplitudeReal
  exact ((contDiff_coordinateMiddleMeridianCutoff.mul
    (Real.contDiff_cos.pow (m - 1))).div contDiff_coordinateMiddleCosineGuard
      (fun theta => (coordinateMiddleCosineGuard_pos theta).ne'))

theorem contDiff_coordinateMiddleIBPAmplitude (m : Nat) :
    ContDiff Real (⊤ : ℕ∞) (coordinateMiddleIBPAmplitude m) := by
  change ContDiff Real (⊤ : ℕ∞)
    (fun theta : Real => Complex.ofReal (coordinateMiddleIBPAmplitudeReal m theta))
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.contDiff.comp (contDiff_coordinateMiddleIBPAmplitudeReal m))

/-- The guarded quotient recovers the exact coordinate middle density after
multiplication by the phase derivative `cos theta`. -/
theorem coordinateMiddleIBPAmplitude_mul_cos_eq_middle
    (m : Nat) {theta : Real}
    (htheta : theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    coordinateMiddleIBPAmplitude m theta * ((Real.cos theta : Real) : Complex) =
      (coordinateMiddleMeridianCutoff theta : Complex) *
        ((Real.cos theta ^ m : Real) : Complex) := by
  by_cases hmiddle : coordinateMiddleMeridianCutoff theta = 0
  · simp [coordinateMiddleIBPAmplitude, coordinateMiddleIBPAmplitudeReal, hmiddle]
  · have habs : |theta| ≤ 15 * Real.pi / 32 := by
      by_contra hnot
      exact hmiddle (coordinateMiddleMeridianCutoff_eq_zero_of_large_abs htheta
        (le_of_not_gt hnot))
    have hguardcut : coordinateMiddleGuardCutoff theta = 1 :=
      coordinateMiddleGuardCutoff_eq_one_of_abs_le habs
    have hthetaIoo : theta ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [abs_lt]
      have hstrict : |theta| < Real.pi / 2 := by
        calc
          |theta| ≤ 15 * Real.pi / 32 := habs
          _ < Real.pi / 2 := by nlinarith [Real.pi_pos]
      exact hstrict
    have hcos : Real.cos theta ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo hthetaIoo).ne'
    have hguard : coordinateMiddleCosineGuard theta = Real.cos theta := by
      unfold coordinateMiddleCosineGuard
      rw [hguardcut]
      ring
    unfold coordinateMiddleIBPAmplitude coordinateMiddleIBPAmplitudeReal
    rw [hguard]
    push_cast
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm' : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
      rw [hm', pow_succ]
      field_simp [hcos]
      ring

/-- The angular quotient has zero boundary values at both meridian poles. -/
theorem coordinateMiddleIBPAmplitude_eq_zero_at_meridian_endpoints (m : Nat) :
    coordinateMiddleIBPAmplitude m (-(Real.pi / 2)) = 0 ∧
      coordinateMiddleIBPAmplitude m (Real.pi / 2) = 0 := by
  constructor
  · have hmiddle : coordinateMiddleMeridianCutoff (-(Real.pi / 2)) = 0 :=
      coordinateMiddleMeridianCutoff_eq_zero_of_large_abs
        (by constructor <;> linarith [Real.pi_pos])
        (by rw [abs_of_nonpos] <;> nlinarith [Real.pi_pos])
    simp [coordinateMiddleIBPAmplitude, coordinateMiddleIBPAmplitudeReal, hmiddle]
  · have hmiddle : coordinateMiddleMeridianCutoff (Real.pi / 2) = 0 :=
      coordinateMiddleMeridianCutoff_eq_zero_of_large_abs
        (by constructor <;> linarith [Real.pi_pos])
        (by rw [abs_of_nonneg] <;> nlinarith [Real.pi_pos])
    simp [coordinateMiddleIBPAmplitude, coordinateMiddleIBPAmplitudeReal, hmiddle]

/-- One exact nonstationary integration by parts for the literal coordinate
middle meridian.  The reciprocal of the sine-phase derivative is absorbed in
`coordinateMiddleIBPAmplitude`; its guarded definition is what makes this an
identity on the whole closed meridian, including the planar case `m = 0`. -/
theorem coordinateMiddleMeridianLocalizedIntegral_eq_neg_inv_mul_deriv_integral
    (m : Nat) {l : Real} (hl : l ≠ 0) :
    coordinateMiddleMeridianLocalizedIntegral m l =
      -((((-l : Real) : Complex) * Complex.I)⁻¹) *
        ∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
          deriv (coordinateMiddleIBPAmplitude m) theta *
            Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I) := by
  let a : Real := -(Real.pi / 2)
  let b : Real := Real.pi / 2
  let E : Real -> Complex := fun theta =>
    Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)
  let q : Complex := ((-l : Real) : Complex) * Complex.I
  let s : Complex := q⁻¹
  let A : Real -> Complex := coordinateMiddleIBPAmplitude m
  let A' : Real -> Complex := fun theta => deriv A theta
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hl))
      Complex.I_ne_zero
  have hsq : s * q = 1 := by
    dsimp [s]
    exact inv_mul_cancel₀ hq
  have hA : ∀ theta ∈ uIcc a b, HasDerivAt A (A' theta) theta := by
    intro theta _
    exact ((contDiff_coordinateMiddleIBPAmplitude m).differentiable (by simp)
      theta).hasDerivAt
  have hE : ∀ theta ∈ uIcc a b,
      HasDerivAt E (E theta * (q * (Real.cos theta : Complex))) theta := by
    intro theta _
    dsimp [E, q]
    have hreal : HasDerivAt (fun x : Real => -l * Real.sin x)
        (-l * Real.cos theta) theta := by
      simpa [mul_comm] using (Real.hasDerivAt_sin theta).const_mul (-l)
    have harg : HasDerivAt
        (fun x : Real => ((-l * Real.sin x : Real) : Complex) * Complex.I)
        (((-l * Real.cos theta : Real) : Complex) * Complex.I) theta := by
      simpa only [Complex.real_smul] using hreal.smul_const Complex.I
    simpa [mul_assoc, mul_left_comm, mul_comm] using harg.cexp
  have hV : ∀ theta ∈ uIcc a b,
      HasDerivAt (fun x : Real => s * E x) (E theta * (Real.cos theta : Complex)) theta := by
    intro theta htheta
    have h := (hE theta htheta).const_mul s
    have hcancel : s * (E theta * (q * (Real.cos theta : Complex))) =
        E theta * (Real.cos theta : Complex) := by
      calc
        s * (E theta * (q * (Real.cos theta : Complex))) =
            (s * q) * (E theta * (Real.cos theta : Complex)) := by ring
        _ = E theta * (Real.cos theta : Complex) := by rw [hsq, one_mul]
    simpa only [hcancel] using h
  have hA'cont : Continuous A' := by
    dsimp [A']
    exact (contDiff_coordinateMiddleIBPAmplitude m).continuous_deriv (by simp)
  have hV'cont : Continuous (fun theta : Real =>
      E theta * (Real.cos theta : Complex)) := by
    dsimp [E]
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := A) (u' := A') (v := fun theta : Real => s * E theta)
    (v' := fun theta : Real => E theta * (Real.cos theta : Complex))
    hA hV (hA'cont.intervalIntegrable a b) (hV'cont.intervalIntegrable a b)
  have hboundary :
      A b * (s * E b) - A a * (s * E a) = 0 := by
    have hends := coordinateMiddleIBPAmplitude_eq_zero_at_meridian_endpoints m
    dsimp [A, a, b]
    rw [hends.1, hends.2]
    ring
  have hleft :
      (∫ theta in a..b, A theta * (E theta * (Real.cos theta : Complex))) =
        coordinateMiddleMeridianLocalizedIntegral m l := by
    rw [coordinateMiddleMeridianLocalizedIntegral_eq_middle_cutoff]
    apply intervalIntegral.integral_congr
    intro theta htheta
    have htheta' : theta ∈ Icc (-(Real.pi / 2) : Real) (Real.pi / 2) := by
      simpa only [a, b, uIcc_of_le (by linarith [Real.pi_pos])] using htheta
    have hmiddle := coordinateMiddleIBPAmplitude_mul_cos_eq_middle m htheta'
    dsimp [A, E]
    rw [show (Real.cos theta : Complex) = ((Real.cos theta : Real) : Complex) by rfl]
    calc
      coordinateMiddleIBPAmplitude m theta *
          (Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I) *
            (Real.cos theta : Complex)) =
          (coordinateMiddleIBPAmplitude m theta * (Real.cos theta : Complex)) *
            Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I) := by ring
      _ = _ := by rw [hmiddle]
  have hright :
      (∫ theta in a..b, A' theta * (s * E theta)) =
        s * ∫ theta in a..b, A' theta * E theta := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro theta _
    ring
  calc
    coordinateMiddleMeridianLocalizedIntegral m l =
        ∫ theta in a..b, A theta * (E theta * (Real.cos theta : Complex)) := hleft.symm
    _ = A b * (s * E b) - A a * (s * E a) -
        ∫ theta in a..b, A' theta * (s * E theta) := hparts
    _ = -s * ∫ theta in a..b, A' theta * E theta := by
      rw [hboundary, hright]
      ring
    _ = -((((-l : Real) : Complex) * Complex.I)⁻¹) *
        ∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
          deriv (coordinateMiddleIBPAmplitude m) theta *
            Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I) := by
      rfl

/-- The literal coordinate middle term has a uniform nonstationary
`|l|⁻¹` bound.  This is already stronger than the planar stationary order
`|l|⁻¹ᐟ²`; higher integrations by parts are used only for the harmless
all-dimensional remainders. -/
theorem exists_coordinateMiddleMeridianLocalizedIntegral_decay_one
    (m : Nat) :
    ∃ C : Real, 0 < C ∧ ∀ l : Real, 1 ≤ |l| →
      ‖coordinateMiddleMeridianLocalizedIntegral m l‖ ≤ C / |l| := by
  let A : Real -> Complex := coordinateMiddleIBPAmplitude m
  have hAcont : Continuous (deriv A) := by
    dsimp [A]
    exact (contDiff_coordinateMiddleIBPAmplitude m).continuous_deriv (by simp)
  rcases (isCompact_Icc.image_of_continuousOn hAcont.continuousOn).isBounded
      .exists_pos_norm_le with ⟨M, hM, hMbound⟩
  refine ⟨Real.pi * M, mul_pos Real.pi_pos hM, ?_⟩
  intro l hl
  have hlne : l ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hl
    norm_num at hl
  have hinv : ‖-((((-l : Real) : Complex) * Complex.I)⁻¹)‖ = 1 / |l| := by
    rw [norm_neg, norm_inv, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs, abs_neg]
    exact inv_eq_one_div _
  have hlength : |(Real.pi / 2 : Real) - -(Real.pi / 2)| = Real.pi := by
    rw [abs_of_nonneg]
    · ring
    · positivity
  have hint :
      ‖∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
          deriv A theta *
            Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)‖ ≤
        M * Real.pi := by
    calc
      ‖∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
          deriv A theta *
            Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)‖ ≤
          M * |(Real.pi / 2 : Real) - -(Real.pi / 2)| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro theta htheta
            have htheta' : theta ∈ Icc (-(Real.pi / 2) : Real) (Real.pi / 2) := by
              rw [uIoc_of_le (by linarith [Real.pi_pos])] at htheta
              exact ⟨htheta.1.le, htheta.2⟩
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
            exact hMbound _ (mem_image_of_mem _ htheta')
      _ = M * Real.pi := by rw [hlength]
  rw [coordinateMiddleMeridianLocalizedIntegral_eq_neg_inv_mul_deriv_integral m hlne]
  calc
    ‖-((((-l : Real) : Complex) * Complex.I)⁻¹) *
        ∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
          deriv (coordinateMiddleIBPAmplitude m) theta *
            Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)‖ =
        ‖-((((-l : Real) : Complex) * Complex.I)⁻¹)‖ *
          ‖∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
            deriv A theta *
              Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)‖ := by
          dsimp [A]
          rw [norm_mul]
    _ ≤ (1 / |l|) * (M * Real.pi) := by
      rw [hinv]
      exact mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (Real.pi * M) / |l| := by ring

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
