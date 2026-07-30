/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4LowerInputPhysicalLiteralRate

/-!
# Scalar dyadic bookkeeping for the lower Q4 interpolation

The lower-input part of the Q4 proof uses the physical shell endpoint
`D * 2^j` together with an `L² -> Lʳ` shell rate.  This file isolates the
elementary power calculation which turns those two factors into the actual
dyadic exponent of the weak coefficient.  In particular, it does not replace
the physical endpoint by a Fourier-ball estimate.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Set ENNReal

noncomputable section

/-- Scaling rule for one lower-input weak coefficient.  This is the scalar
calculation behind the physical lower Q4 branch: an `L¹ → L∞` factor has
scale `R`, while an `L² → Lʳ` coefficient has scale `R^b`. -/
theorem q4LowerWeakRealConstant_scale
    {A B R b p r : Real} (hA : 0 < A) (hB : 0 ≤ B) (hR : 0 < R) :
    q4LowerWeakRealConstant (A * R) (B * R ^ b) p r =
      q4LowerWeakRealConstant A B p r *
        R ^ (r * b + q4LowerWeakTailExponent p r) := by
  have htwo : 0 < (2 : Real) := by norm_num
  have htwoA : 0 ≤ 2 * A := mul_nonneg htwo.le hA.le
  have hRpow : 0 ≤ R ^ b := Real.rpow_nonneg hR.le _
  unfold q4LowerWeakRealConstant
  rw [show 2 * (A * R) = (2 * A) * R by ring]
  rw [Real.mul_rpow hB hRpow, Real.mul_rpow htwoA hR.le]
  calc
    (2 : Real) ^ r * (B ^ r * (R ^ b) ^ r) *
        ((2 * A) ^ q4LowerWeakTailExponent p r *
          R ^ q4LowerWeakTailExponent p r) =
        ((2 : Real) ^ r * B ^ r *
          (2 * A) ^ q4LowerWeakTailExponent p r) *
          ((R ^ b) ^ r * R ^ q4LowerWeakTailExponent p r) := by
          ring
    _ = ((2 : Real) ^ r * B ^ r *
          (2 * A) ^ q4LowerWeakTailExponent p r) *
          (R ^ (r * b) * R ^ q4LowerWeakTailExponent p r) := by
          rw [← Real.rpow_mul hR.le]
    _ = _ := by
          rw [← Real.rpow_add hR]

/-- The lower weak coefficient has the expected exact dyadic factor when
the `L² -> Lʳ` coefficient is a fixed constant times
`(2^(a / 2))^j`.  The first contribution to the exponent comes from the
`TT*` square root and the second from the physical `L¹ -> L∞` shell bound. -/
theorem q4LowerWeakRealConstant_physical_dyadic_factor
    {D C a p r : Real} (hD : 0 < D) (hC : 0 < C) (j : Nat) :
    q4LowerWeakRealConstant (D * (2 : Real) ^ j)
      (C * ((2 : Real) ^ (a / 2)) ^ j) p r =
      q4LowerWeakRealConstant D C p r *
        ((2 : Real) ^
          (r * a / 2 + q4LowerWeakTailExponent p r)) ^ j := by
  have htwo : 0 < (2 : Real) := by norm_num
  have hDtwo : 0 < 2 * D := mul_pos htwo hD
  have hfrequency : 0 < (2 : Real) ^ (a / 2) :=
    Real.rpow_pos_of_pos htwo _
  have hscale :
      2 * (D * (2 : Real) ^ j) = (2 * D) * (2 : Real) ^ j := by
    ring
  have hBfactor :
      (C * ((2 : Real) ^ (a / 2)) ^ j) ^ r =
        C ^ r * (((2 : Real) ^ (a / 2)) ^ j) ^ r := by
    rw [Real.mul_rpow hC.le (pow_nonneg hfrequency.le j)]
  have hAscale :
      ((2 : Real) ^ j) ^ q4LowerWeakTailExponent p r =
        ((2 : Real) ^ q4LowerWeakTailExponent p r) ^ j := by
    calc
      ((2 : Real) ^ j) ^ q4LowerWeakTailExponent p r =
          (2 : Real) ^ ((j : Real) * q4LowerWeakTailExponent p r) := by
            rw [← Real.rpow_natCast,
              ← Real.rpow_mul htwo.le]
      _ = (2 : Real) ^
          (q4LowerWeakTailExponent p r * (j : Real)) := by
            congr 1
            ring
      _ = ((2 : Real) ^ q4LowerWeakTailExponent p r) ^ j :=
        Real.rpow_mul_natCast htwo.le _ _
  have hBscale :
      (((2 : Real) ^ (a / 2)) ^ j) ^ r =
        ((2 : Real) ^ (r * a / 2)) ^ j := by
    calc
      (((2 : Real) ^ (a / 2)) ^ j) ^ r =
          ((2 : Real) ^ (a / 2)) ^ ((j : Real) * r) := by
            rw [← Real.rpow_natCast,
              ← Real.rpow_mul (Real.rpow_nonneg htwo.le _)]
      _ = (2 : Real) ^ ((a / 2) * ((j : Real) * r)) := by
            rw [← Real.rpow_mul htwo.le]
      _ = (2 : Real) ^ ((r * a / 2) * (j : Real)) := by
            congr 1
            ring
      _ = ((2 : Real) ^ (r * a / 2)) ^ j :=
        Real.rpow_mul_natCast htwo.le _ _
  unfold q4LowerWeakRealConstant
  rw [hBfactor, hscale,
    Real.mul_rpow hDtwo.le (pow_nonneg htwo.le j), hAscale, hBscale]
  calc
    (2 : Real) ^ r *
        (C ^ r * ((2 : Real) ^ (r * a / 2)) ^ j) *
        ((2 * D) ^ q4LowerWeakTailExponent p r *
          ((2 : Real) ^ q4LowerWeakTailExponent p r) ^ j) =
        ((2 : Real) ^ r * C ^ r *
          (2 * D) ^ q4LowerWeakTailExponent p r) *
          (((2 : Real) ^ (r * a / 2)) ^ j *
            ((2 : Real) ^ q4LowerWeakTailExponent p r) ^ j) := by
          ring
    _ = ((2 : Real) ^ r * C ^ r *
          (2 * D) ^ q4LowerWeakTailExponent p r) *
          ((2 : Real) ^
            (r * a / 2 + q4LowerWeakTailExponent p r)) ^ j := by
          rw [← mul_pow, ← Real.rpow_add htwo]

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
