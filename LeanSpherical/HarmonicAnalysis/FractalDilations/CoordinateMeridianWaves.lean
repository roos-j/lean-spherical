/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.QuadraticStationaryPhase

/-!
# Coordinate-localized meridian waves

This is the exact stationary-coordinate version of the two-wave expansion of
the Fourier transform of spherical measure.  Unlike the raw north/south split,
the endpoint terms are cut off by the smooth compact amplitude from
`SmoothEndpointAmplitude`.  The change of variables is written out here so
that the sharp quadratic estimate applies to *the literal meridian terms*.

The remaining middle term is defined by exact subtraction.  Its phase is
nonstationary after the endpoint cutoffs have been removed; that separate
radial integration-by-parts estimate is supplied by the wave-kernel layer.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set

noncomputable section

/-- The north-pole endpoint contribution with the smooth cutoff written in
the quadratic coordinate. -/
noncomputable def coordinateUpperMeridianLocalizedIntegral
    (m : Nat) (l : Real) : Complex :=
  ∫ theta in (0 : Real)..(Real.pi / 2),
    (endpointCoreCutoff (Real.sqrt (1 - Real.sin theta)) : Complex) *
      ((Real.cos theta ^ m : Real) : Complex) *
        Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)

/-- The south-pole endpoint contribution with the corresponding reflected
quadratic cutoff. -/
noncomputable def coordinateLowerMeridianLocalizedIntegral
    (m : Nat) (l : Real) : Complex :=
  ∫ theta in (-(Real.pi / 2) : Real)..0,
    (endpointCoreCutoff (Real.sqrt (1 + Real.sin theta)) : Complex) *
      ((Real.cos theta ^ m : Real) : Complex) *
        Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)

/-- The literal middle contribution is the original meridian integral minus
the two coordinate-localized endpoint pieces. -/
noncomputable def coordinateMiddleMeridianLocalizedIntegral
    (m : Nat) (l : Real) : Complex :=
  (∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
    ((Real.cos theta ^ m : Real) : Complex) *
      Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)) -
    coordinateUpperMeridianLocalizedIntegral m l -
      coordinateLowerMeridianLocalizedIntegral m l

private theorem continuous_coordinateUpper_integrand (m : Nat) (l : Real) :
    Continuous (fun theta : Real =>
      (endpointCoreCutoff (Real.sqrt (1 - Real.sin theta)) : Complex) *
        ((Real.cos theta ^ m : Real) : Complex) *
          Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)) := by
  fun_prop

/-- Exact north-pole stationary-coordinate formula.  The cutoff turns into
the literal smooth endpoint amplitude, so the quadratic stationary estimate
proved in `QuadraticStationaryPhase` applies directly. -/
theorem coordinateUpperMeridianLocalizedIntegral_eq_smoothEndpointQuadratic
    (m : Nat) (hm : 1 ≤ m) (l : Real) :
    coordinateUpperMeridianLocalizedIntegral m l =
      Complex.exp (((-l : Real) : Complex) * Complex.I) *
        smoothEndpointQuadraticIntegral m l := by
  let phi : Real -> Real := endpointCoordinate
  let F : Real -> Complex := fun theta =>
    (endpointCoreCutoff (Real.sqrt (1 - Real.sin theta)) : Complex) *
      ((Real.cos theta ^ m : Real) : Complex) *
        Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)
  have hphi0 : phi 0 = Real.pi / 2 := endpointCoordinate_zero
  have hphi1 : phi 1 = 0 := endpointCoordinate_one
  have hphi_deriv : ∀ u ∈ uIcc (0 : Real) 1,
      HasDerivAt phi (-2 / Real.sqrt (2 - u ^ 2)) u := by
    intro u hu
    have hu' : u ∈ Icc (0 : Real) 1 := by
      simpa [uIcc_of_le] using hu
    exact endpointCoordinate_hasDerivAt hu'.1 hu'.2
  have hphi_deriv_cont : ContinuousOn
      (fun u : Real => -2 / Real.sqrt (2 - u ^ 2)) (uIcc (0 : Real) 1) := by
    simpa [uIcc_of_le] using endpointCoordinate_deriv_continuousOn
  have hF : Continuous F := by
    dsimp [F]
    exact continuous_coordinateUpper_integrand m l
  have hsubst := intervalIntegral.integral_deriv_smul_comp
    (a := (0 : Real)) (b := (1 : Real)) (f := phi)
    (f' := fun u => -2 / Real.sqrt (2 - u ^ 2)) (g := F)
    hphi_deriv hphi_deriv_cont hF
  rw [hphi0, hphi1, intervalIntegral.integral_symm] at hsubst
  rw [intervalIntegral.integral_symm] at hsubst
  have hsubst' :
      (∫ theta in (Real.pi / 2)..(0 : Real), F theta) =
        ∫ u in (0 : Real)..1,
          (-2 / Real.sqrt (2 - u ^ 2)) • (F ∘ phi) u := by
    calc
      (∫ theta in (Real.pi / 2)..(0 : Real), F theta) =
          - -(∫ u in (0 : Real)..1,
            (-2 / Real.sqrt (2 - u ^ 2)) • (F ∘ phi) u) := hsubst.symm
      _ = ∫ u in (0 : Real)..1,
          (-2 / Real.sqrt (2 - u ^ 2)) • (F ∘ phi) u := by ring
  change (∫ theta in (0 : Real)..(Real.pi / 2), F theta) = _
  calc
    (∫ theta in (0 : Real)..(Real.pi / 2), F theta) =
        -(∫ theta in (Real.pi / 2)..(0 : Real), F theta) := by
          rw [intervalIntegral.integral_symm]
    _ = -(∫ u in (0 : Real)..1,
        (-2 / Real.sqrt (2 - u ^ 2)) • (F ∘ phi) u) := by
          rw [hsubst']
    _ = Complex.exp (((-l : Real) : Complex) * Complex.I) *
        smoothEndpointQuadraticIntegral m l := by
          rw [smoothEndpointQuadraticIntegral]
          rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro u hu
          have hu' : u ∈ Icc (0 : Real) 1 := by
            simpa [uIcc_of_le] using hu
          have hsin : Real.sin (phi u) = 1 - u ^ 2 := by
            exact sin_pi_div_two_sub_two_arcsin_div_sqrt_two hu'.1 hu'.2
          have hcos : Real.cos (phi u) = u * Real.sqrt (2 - u ^ 2) :=
            endpointCoordinate_cos hu'.1 hu'.2
          have hspos : 0 < Real.sqrt (2 - u ^ 2) := by
            have husq : u ^ 2 ≤ 1 := by
              nlinarith [mul_nonneg hu'.1 (sub_nonneg.mpr hu'.2)]
            exact Real.sqrt_pos.2 (by nlinarith)
          have hcut : endpointCoreCutoff (Real.sqrt (1 - Real.sin (phi u))) =
              endpointCoreCutoff u := by
            rw [hsin]
            have hsq : 1 - (1 - u ^ 2) = u ^ 2 := by ring
            rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hu'.1]
          have hm' : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
          have hexp :
              Complex.exp (((-l * (1 - u ^ 2) : Real) : Complex) * Complex.I) =
                Complex.exp (((-l : Real) : Complex) * Complex.I) *
                  Complex.exp (((l * u ^ 2 : Real) : Complex) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
          rw [smoothEndpointAmplitude_eq_cutoff_mul_endpointQuadraticAmplitude]
          dsimp [F, phi, Function.comp_apply, endpointQuadraticAmplitude]
          rw [hsin, hcos, hcut, hexp, hm']
          push_cast
          simp only [pow_succ, mul_pow]
          field_simp [ne_of_gt hspos]

/-- The reflected south-pole formula. -/
theorem coordinateLowerMeridianLocalizedIntegral_eq_smoothEndpointQuadratic
    (m : Nat) (hm : 1 ≤ m) (l : Real) :
    coordinateLowerMeridianLocalizedIntegral m l =
      Complex.exp (((l : Real) : Complex) * Complex.I) *
        smoothEndpointQuadraticIntegral m (-l) := by
  let F : Real -> Complex := fun theta =>
    (endpointCoreCutoff (Real.sqrt (1 + Real.sin theta)) : Complex) *
      ((Real.cos theta ^ m : Real) : Complex) *
        Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)
  have hcomp := intervalIntegral.integral_comp_neg
    (a := (0 : Real)) (b := Real.pi / 2) (f := F)
  rw [neg_zero] at hcomp
  change (∫ theta in (-(Real.pi / 2) : Real)..0, F theta) = _
  calc
    (∫ theta in (-(Real.pi / 2) : Real)..0, F theta) =
        ∫ theta in (0 : Real)..(Real.pi / 2),
          (endpointCoreCutoff (Real.sqrt (1 - Real.sin theta)) : Complex) *
            ((Real.cos theta ^ m : Real) : Complex) *
              Complex.exp (((-(-l) * Real.sin theta : Real) : Complex) * Complex.I) := by
      rw [← hcomp]
      apply intervalIntegral.integral_congr
      intro theta htheta
      dsimp [F]
      rw [Real.cos_neg, Real.sin_neg]
      push_cast
      ring_nf
    _ = Complex.exp (((-(-l) : Real) : Complex) * Complex.I) *
          smoothEndpointQuadraticIntegral m (-l) :=
      coordinateUpperMeridianLocalizedIntegral_eq_smoothEndpointQuadratic m hm (-l)
    _ = Complex.exp (((l : Real) : Complex) * Complex.I) *
          smoothEndpointQuadraticIntegral m (-l) := by
      congr 2
      congr 1
      push_cast
      ring

/-- The coordinate-localized pieces reassemble the literal meridian
integral by definition. -/
theorem intervalIntegral_meridian_eq_coordinateLocalizedPartition
    (m : Nat) (l : Real) :
    (∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
      ((Real.cos theta ^ m : Real) : Complex) *
        Complex.exp (((-l * Real.sin theta : Real) : Complex) * Complex.I)) =
      coordinateUpperMeridianLocalizedIntegral m l +
        coordinateLowerMeridianLocalizedIntegral m l +
          coordinateMiddleMeridianLocalizedIntegral m l := by
  unfold coordinateMiddleMeridianLocalizedIntegral
  ring

/-- Exact two-wave/middle decomposition of the actual spherical Fourier
factor in every ambient dimension at least three, now with endpoint symbols
which have the proved compact quadratic stationary-phase decay. -/
theorem surfaceFourier_succ_eq_coordinateSmoothWaves
    {d : Nat} (hd : 2 ≤ d) (xi : Euclidean (d + 1)) :
    surfaceFourier (d + 1) xi =
      (surfaceMass d : Complex) *
        (Complex.exp (((-(2 * Real.pi * ‖xi‖) : Real) : Complex) * Complex.I) *
            smoothEndpointQuadraticIntegral (d - 1) (2 * Real.pi * ‖xi‖) +
          Complex.exp (((2 * Real.pi * ‖xi‖ : Real) : Complex) * Complex.I) *
            smoothEndpointQuadraticIntegral (d - 1) (-(2 * Real.pi * ‖xi‖)) +
          coordinateMiddleMeridianLocalizedIntegral (d - 1)
            (2 * Real.pi * ‖xi‖)) := by
  rw [surfaceFourier_succ_height_intervalIntegral hd xi]
  congr 1
  have hheight := intervalIntegral_height_power_eq_meridian d hd
    (2 * Real.pi * ‖xi‖)
  have hphase : ∀ t : Real,
      -2 * Real.pi * ‖xi‖ * t = -(2 * Real.pi * ‖xi‖) * t := by
    intro t
    ring
  calc
    (∫ t in (-1 : Real)..1,
      ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : Real) : Complex) *
        Complex.exp (((-2 * Real.pi * ‖xi‖ * t : Real) : Complex) * Complex.I)) =
        ∫ t in (-1 : Real)..1,
          ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : Real) : Complex) *
            Complex.exp (((-(2 * Real.pi * ‖xi‖) * t : Real) : Complex) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro t ht
      congr 3
      push_cast
      ring
    _ = ∫ theta in (-(Real.pi / 2) : Real)..(Real.pi / 2),
          ((Real.cos theta ^ (d - 1) : Real) : Complex) *
            Complex.exp (((-(2 * Real.pi * ‖xi‖) * Real.sin theta : Real) : Complex) *
              Complex.I) := by
      simpa using hheight
    _ = coordinateUpperMeridianLocalizedIntegral (d - 1) (2 * Real.pi * ‖xi‖) +
          coordinateLowerMeridianLocalizedIntegral (d - 1) (2 * Real.pi * ‖xi‖) +
            coordinateMiddleMeridianLocalizedIntegral (d - 1)
              (2 * Real.pi * ‖xi‖) :=
      intervalIntegral_meridian_eq_coordinateLocalizedPartition
        (d - 1) (2 * Real.pi * ‖xi‖)
    _ = _ := by
      rw [coordinateUpperMeridianLocalizedIntegral_eq_smoothEndpointQuadratic
          (d - 1) (by omega),
        coordinateLowerMeridianLocalizedIntegral_eq_smoothEndpointQuadratic
          (d - 1) (by omega)]

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
