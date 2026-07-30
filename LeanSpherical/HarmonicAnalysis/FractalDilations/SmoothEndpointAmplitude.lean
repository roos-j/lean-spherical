/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.StationaryPhaseAmplitude
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Smooth endpoint amplitudes for the spherical stationary-phase expansion

The elementary change of variables in `StationaryPhaseAmplitude` produces an
exact quadratic phase on the interval `[0,1]`.  Its raw amplitude is smooth on
that interval, but cutting it at `u = 1` is not a valid symbol construction:
after differentiating in the frequency parameter it leaves an artificial
boundary contribution.  This file makes the usual repair explicit.

We use two nested smooth bumps.  The inner bump is the actual endpoint cutoff.
The outer bump clips the coordinate before it is put under a square root.  Thus
the resulting amplitude is a globally `C^infinity` function of `u`, while it
agrees *exactly* with the geometrically obtained amplitude wherever the inner
cutoff is nonzero.  In particular every derivative vanishes at the artificial
endpoint `u = 1`.

This is the literal input for the all-dimensional stationary-phase symbol
estimates; it does not use a maximal-function assertion.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Metric Set
open scoped ContDiff

noncomputable section

/-- The small cutoff selecting the stationary endpoint in the quadratic
coordinate. -/
noncomputable def endpointCoreBump : ContDiffBump (0 : Real) :=
  ⟨(1 / 8 : Real), (1 / 4 : Real), by norm_num, by norm_num⟩

/-- A larger cutoff which is one on the support of `endpointCoreBump`.  It
keeps the square-root argument strictly positive on the whole real line. -/
noncomputable def endpointGuardBump : ContDiffBump (0 : Real) :=
  ⟨(1 / 2 : Real), (1 : Real), by norm_num, by norm_num⟩

/-- The actual stationary-endpoint cutoff. -/
noncomputable def endpointCoreCutoff (u : Real) : Real := endpointCoreBump u

/-- The auxiliary clipping cutoff. -/
noncomputable def endpointGuardCutoff (u : Real) : Real := endpointGuardBump u

/-- A globally bounded version of the endpoint coordinate. -/
noncomputable def endpointGuardedCoordinate (u : Real) : Real :=
  endpointGuardCutoff u * u

private theorem endpointCoreBump_rOut : endpointCoreBump.rOut = (1 / 4 : Real) := rfl
private theorem endpointGuardBump_rIn : endpointGuardBump.rIn = (1 / 2 : Real) := rfl
private theorem endpointGuardBump_rOut : endpointGuardBump.rOut = (1 : Real) := rfl

/-- The inner cutoff is zero outside its prescribed quarter-neighbourhood. -/
theorem endpointCoreCutoff_eq_zero_of_one_quarter_le_abs
    {u : Real} (hu : (1 / 4 : Real) ≤ |u|) :
    endpointCoreCutoff u = 0 := by
  unfold endpointCoreCutoff
  apply endpointCoreBump.zero_of_le_dist
  rw [endpointCoreBump_rOut]
  simpa [Real.dist_eq] using hu

/-- A nonzero inner cutoff lies strictly inside the region where the guard is
identically one. -/
theorem abs_lt_one_quarter_of_endpointCoreCutoff_ne_zero
    {u : Real} (hu : endpointCoreCutoff u ≠ 0) : |u| < (1 / 4 : Real) := by
  by_contra h
  exact hu (endpointCoreCutoff_eq_zero_of_one_quarter_le_abs (le_of_not_gt h))

theorem endpointGuardCutoff_eq_one_of_endpointCoreCutoff_ne_zero
    {u : Real} (hu : endpointCoreCutoff u ≠ 0) : endpointGuardCutoff u = 1 := by
  have hsmall := abs_lt_one_quarter_of_endpointCoreCutoff_ne_zero hu
  unfold endpointGuardCutoff
  apply endpointGuardBump.one_of_mem_closedBall
  rw [mem_closedBall, endpointGuardBump_rIn]
  simpa [Real.dist_eq] using
    (le_trans (le_of_lt hsmall) (by norm_num : (1 / 4 : Real) ≤ 1 / 2))

theorem endpointGuardCutoff_eq_zero_of_one_le_abs
    {u : Real} (hu : (1 : Real) ≤ |u|) : endpointGuardCutoff u = 0 := by
  unfold endpointGuardCutoff
  apply endpointGuardBump.zero_of_le_dist
  rw [endpointGuardBump_rOut]
  simpa [Real.dist_eq] using hu

/-- The clipped coordinate stays in the unit interval. -/
theorem abs_endpointGuardedCoordinate_le_one (u : Real) :
    |endpointGuardedCoordinate u| ≤ 1 := by
  by_cases hu : |u| ≤ 1
  · unfold endpointGuardedCoordinate
    rw [abs_mul]
    have hguard_nonneg : 0 ≤ endpointGuardCutoff u := by
      exact ContDiffBump.nonneg' endpointGuardBump u
    have hguard : |endpointGuardCutoff u| ≤ 1 := by
      rw [abs_of_nonneg hguard_nonneg]
      exact ContDiffBump.le_one endpointGuardBump
    exact mul_le_one₀ hguard (abs_nonneg _) hu
  · have hlarge : (1 : Real) ≤ |u| := (lt_of_not_ge hu).le
    rw [endpointGuardedCoordinate, endpointGuardCutoff_eq_zero_of_one_le_abs hlarge,
      zero_mul, abs_zero]
    norm_num

/-- The square-root argument in the smooth extension is positive globally. -/
theorem endpointGuardedCoordinate_sqrt_arg_pos (u : Real) :
    0 < 2 - endpointGuardedCoordinate u ^ 2 := by
  have h := abs_endpointGuardedCoordinate_le_one u
  have hsquare : endpointGuardedCoordinate u ^ 2 ≤ 1 := by
    have hsquare' : |endpointGuardedCoordinate u| ^ 2 ≤ (1 : Real) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 h
    simpa only [sq_abs, one_pow] using hsquare'
  linarith

/-- The real, globally smooth endpoint amplitude.  The factor `u^m` is the
stationary vanishing of the spherical meridian density. -/
noncomputable def smoothEndpointAmplitudeReal (m : Nat) (u : Real) : Real :=
  2 * u ^ m *
      (Real.sqrt (2 - endpointGuardedCoordinate u ^ 2)) ^ (m - 1) *
    endpointCoreCutoff u

/-- The smooth factor left after the explicit stationary vanishing `u^m`
has been separated from the endpoint amplitude.  This is the amplitude to
which the compact quadratic stationary-phase recurrence is applied. -/
noncomputable def smoothEndpointProfileReal (m : Nat) (u : Real) : Real :=
  2 * (Real.sqrt (2 - endpointGuardedCoordinate u ^ 2)) ^ (m - 1) *
    endpointCoreCutoff u

/-- Complex version of the actual smooth endpoint amplitude. -/
noncomputable def smoothEndpointAmplitude (m : Nat) (u : Real) : Complex :=
  (smoothEndpointAmplitudeReal m u : Complex)

/-- Complex form of the nonvanishing endpoint profile. -/
noncomputable def smoothEndpointProfile (m : Nat) (u : Real) : Complex :=
  (smoothEndpointProfileReal m u : Complex)

/-- The smooth endpoint quadratic integral after removal of the outgoing
plane wave. -/
noncomputable def smoothEndpointQuadraticIntegral (m : Nat) (lambda : Real) : Complex :=
  ∫ u in (0 : Real)..1,
    smoothEndpointAmplitude m u *
      Complex.exp (((lambda * u ^ 2 : Real) : Complex) * Complex.I)

/-- The clipped coordinate is globally smooth. -/
theorem contDiff_endpointGuardedCoordinate :
    ContDiff Real (⊤ : ℕ∞) endpointGuardedCoordinate := by
  unfold endpointGuardedCoordinate endpointGuardCutoff
  exact endpointGuardBump.contDiff.mul contDiff_id

/-- The positive square-root factor is globally smooth because the guard
prevents its argument from reaching zero. -/
theorem contDiff_endpointGuardedSqrt :
    ContDiff Real (⊤ : ℕ∞)
      (fun u : Real => Real.sqrt (2 - endpointGuardedCoordinate u ^ 2)) := by
  apply (contDiff_const.sub (contDiff_endpointGuardedCoordinate.pow 2)).sqrt
  intro u
  exact ne_of_gt (endpointGuardedCoordinate_sqrt_arg_pos u)

/-- The cutoff extension of the endpoint amplitude is genuinely smooth on
the whole real line. -/
theorem contDiff_smoothEndpointAmplitudeReal (m : Nat) :
    ContDiff Real (⊤ : ℕ∞) (smoothEndpointAmplitudeReal m) := by
  unfold smoothEndpointAmplitudeReal endpointCoreCutoff
  exact (((contDiff_const.mul (contDiff_id.pow m)).mul
    (contDiff_endpointGuardedSqrt.pow (m - 1))).mul endpointCoreBump.contDiff)

/-- The separated endpoint profile is globally smooth as well. -/
theorem contDiff_smoothEndpointProfileReal (m : Nat) :
    ContDiff Real (⊤ : ℕ∞) (smoothEndpointProfileReal m) := by
  unfold smoothEndpointProfileReal endpointCoreCutoff
  exact ((contDiff_const.mul
    (contDiff_endpointGuardedSqrt.pow (m - 1))).mul endpointCoreBump.contDiff)

/-- Complexification preserves the global smoothness of the endpoint symbol. -/
theorem contDiff_smoothEndpointAmplitude (m : Nat) :
    ContDiff Real (⊤ : ℕ∞) (smoothEndpointAmplitude m) := by
  change ContDiff Real (⊤ : ℕ∞)
    (fun u : Real => Complex.ofReal (smoothEndpointAmplitudeReal m u))
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.contDiff.comp (contDiff_smoothEndpointAmplitudeReal m))

/-- Complexification preserves smoothness of the separated endpoint profile. -/
theorem contDiff_smoothEndpointProfile (m : Nat) :
    ContDiff Real (⊤ : ℕ∞) (smoothEndpointProfile m) := by
  change ContDiff Real (⊤ : ℕ∞)
    (fun u : Real => Complex.ofReal (smoothEndpointProfileReal m u))
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.contDiff.comp (contDiff_smoothEndpointProfileReal m))

/-- The endpoint amplitude is exactly its explicit vanishing factor times
the smooth profile. -/
theorem smoothEndpointAmplitude_eq_monomial_mul_profile
    (m : Nat) (u : Real) :
    smoothEndpointAmplitude m u =
      ((u ^ m : Real) : Complex) * smoothEndpointProfile m u := by
  unfold smoothEndpointAmplitude smoothEndpointAmplitudeReal
    smoothEndpointProfile smoothEndpointProfileReal
  push_cast
  ring

/-- On the support of the inner cutoff the globally smooth extension is the
literal endpoint-coordinate amplitude from the meridian substitution. -/
theorem smoothEndpointAmplitude_eq_cutoff_mul_endpointQuadraticAmplitude
    (m : Nat) (u : Real) :
    smoothEndpointAmplitude m u =
      (endpointCoreCutoff u : Complex) * endpointQuadraticAmplitude m u := by
  by_cases hu : endpointCoreCutoff u = 0
  · simp [smoothEndpointAmplitude, smoothEndpointAmplitudeReal, hu]
  · have hguard : endpointGuardCutoff u = 1 :=
      endpointGuardCutoff_eq_one_of_endpointCoreCutoff_ne_zero hu
    unfold smoothEndpointAmplitude smoothEndpointAmplitudeReal
      endpointQuadraticAmplitude endpointGuardedCoordinate
    rw [hguard]
    push_cast
    ring

/-- The inner cutoff, hence the smooth endpoint amplitude, is zero in a
neighbourhood of the artificial endpoint `u = 1`. -/
theorem smoothEndpointAmplitude_eventuallyEq_zero_at_one (m : Nat) :
    smoothEndpointAmplitude m =ᶠ[𝓝 (1 : Real)] 0 := by
  filter_upwards [Metric.ball_mem_nhds (1 : Real) (by norm_num : (0 : Real) < 1 / 2)]
    with u hu
  rw [mem_ball, Real.dist_eq] at hu
  have hu' := (abs_lt.mp hu).1
  have hlarge : (1 / 4 : Real) ≤ |u| := by
    rw [abs_of_nonneg]
    · linarith
    · linarith
  have hcut : endpointCoreCutoff u = 0 :=
    endpointCoreCutoff_eq_zero_of_one_quarter_le_abs hlarge
  simp [smoothEndpointAmplitude, smoothEndpointAmplitudeReal, hcut]

/-- The separated profile vanishes near the artificial endpoint too. -/
theorem smoothEndpointProfile_eventuallyEq_zero_at_one (m : Nat) :
    smoothEndpointProfile m =ᶠ[𝓝 (1 : Real)] 0 := by
  filter_upwards [Metric.ball_mem_nhds (1 : Real) (by norm_num : (0 : Real) < 1 / 2)]
    with u hu
  rw [mem_ball, Real.dist_eq] at hu
  have hu' := (abs_lt.mp hu).1
  have hlarge : (1 / 4 : Real) ≤ |u| := by
    rw [abs_of_nonneg]
    · linarith
    · linarith
  have hcut : endpointCoreCutoff u = 0 :=
    endpointCoreCutoff_eq_zero_of_one_quarter_le_abs hlarge
  simp [smoothEndpointProfile, smoothEndpointProfileReal, hcut]

/-- Every ordinary derivative of the smooth endpoint amplitude vanishes at
the artificial endpoint.  This is the endpoint condition needed when radial
symbol estimates are integrated by parts later on. -/
theorem iteratedDeriv_smoothEndpointAmplitude_at_one (m k : Nat) :
    iteratedDeriv k (smoothEndpointAmplitude m) 1 = 0 := by
  have h := Filter.EventuallyEq.iteratedDeriv_eq k
    (smoothEndpointAmplitude_eventuallyEq_zero_at_one m)
  simpa using h

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
