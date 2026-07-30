/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.AbsoluteDyadicDerivativeScaling
import LeanSpherical.HarmonicAnalysis.FractalDilations.PlanarTripleWaveNormalForm
import LeanSpherical.HarmonicAnalysis.FractalDilations.CoordinateWaveDerivatives
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4DerivativePhysicalL2

/-!
# Differentiated planar three-wave normal form

The scaled radius derivative is handled by differentiating the actual circle
three-wave identity before the radial `TT*` reduction.  In particular the
derivative is never estimated by the undifferentiated Stein kernel.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Metric Set FourierTransform
open scoped BigOperators ContDiff FourierTransform ComplexConjugate

noncomputable section

/-- The literal radius derivative of one coordinate wave, with the radius
parameter differentiated and the radial frequency held fixed. -/
def planarCoordinateWaveRadiusDerivativeTerm
    (part : CoordinateWavePart) (a rho : Real) : Complex :=
  deriv (fun b : Real => planarCoordinateWaveRadialTerm part b rho) a

/-- The three literal radius-derivative coordinate waves. -/
def planarCoordinateSurfaceRadiusDerivativeWaveSum (a rho : Real) : Complex :=
  planarCoordinateWaveRadiusDerivativeTerm .outgoing a rho +
    planarCoordinateWaveRadiusDerivativeTerm .incoming a rho +
      planarCoordinateWaveRadiusDerivativeTerm .middle a rho

/-- The coefficient of the radius in the extracted coordinate-wave phase.
Writing it separately makes the differentiated normal form retain exactly
the same three linear phases as the undifferentiated circle calculation. -/
def planarCoordinateWavePhaseSlope (part : CoordinateWavePart) : Real :=
  match part with
  | .outgoing => -(2 * Real.pi)
  | .incoming => 2 * Real.pi
  | .middle => 0

theorem coordinateWaveRadialPhase_eq_planarCoordinateWavePhaseSlope_mul
    (part : CoordinateWavePart) (a : Real) :
    coordinateWaveRadialPhase part a = planarCoordinateWavePhaseSlope part * a := by
  cases part <;> simp [coordinateWaveRadialPhase, planarCoordinateWavePhaseSlope] <;> ring

/-- The nonoscillatory coefficient after differentiating a coordinate wave
with respect to its radius.  The first term differentiates the literal
endpoint/middle amplitude and the second differentiates its displayed linear
phase. -/
def planarCoordinateWaveRadiusDerivativeAmplitude
    (part : CoordinateWavePart) (a rho : Real) : Complex :=
  deriv (fun b : Real => planarCoordinateWaveRadialAmplitude part b rho) a +
    (((planarCoordinateWavePhaseSlope part * rho : Real) : Complex) * Complex.I) *
      planarCoordinateWaveRadialAmplitude part a rho

private theorem contDiff_planarCoordinateWaveRadialAmplitude_radius
    (part : CoordinateWavePart) (rho : Real) :
    ContDiff Real (⊤ : ℕ∞)
      (fun a : Real => planarCoordinateWaveRadialAmplitude part a rho) := by
  cases part <;> unfold planarCoordinateWaveRadialAmplitude <;> fun_prop

private theorem hasDerivAt_planarCoordinateWavePhase_radius
    (part : CoordinateWavePart) (a rho : Real) :
    HasDerivAt
      (fun b : Real => oscillatoryExp (coordinateWaveRadialPhase part b) rho)
      ((((planarCoordinateWavePhaseSlope part * rho : Real) : Complex) * Complex.I) *
        oscillatoryExp (coordinateWaveRadialPhase part a) rho) a := by
  have hphase : HasDerivAt
      (fun b : Real => coordinateWaveRadialPhase part b * rho)
      (planarCoordinateWavePhaseSlope part * rho) a := by
    rw [show (fun b : Real => coordinateWaveRadialPhase part b * rho) =
        fun b : Real => (planarCoordinateWavePhaseSlope part * b) * rho by
      funext b
      rw [coordinateWaveRadialPhase_eq_planarCoordinateWavePhaseSlope_mul]
      ring]
    simpa [mul_assoc] using
      ((hasDerivAt_id a).const_mul (planarCoordinateWavePhaseSlope part)).mul_const rho
  have harg : HasDerivAt
      (fun b : Real => (((coordinateWaveRadialPhase part b * rho : Real) : Complex) *
        Complex.I))
      ((((planarCoordinateWavePhaseSlope part * rho : Real) : Complex) * Complex.I)) a := by
    simpa only [Complex.real_smul] using hphase.smul_const Complex.I
  simpa only [oscillatoryExp] using harg.cexp

/-- Factoring the radius derivative of a literal coordinate wave leaves the
same oscillatory phase and the explicit differentiated amplitude above. -/
theorem planarCoordinateWaveRadiusDerivativeTerm_eq_amplitude_mul_oscillatoryExp
    (part : CoordinateWavePart) (a rho : Real) :
    planarCoordinateWaveRadiusDerivativeTerm part a rho =
      planarCoordinateWaveRadiusDerivativeAmplitude part a rho *
        oscillatoryExp (coordinateWaveRadialPhase part a) rho := by
  have hamp : HasDerivAt
      (fun b : Real => planarCoordinateWaveRadialAmplitude part b rho)
      (deriv (fun b : Real => planarCoordinateWaveRadialAmplitude part b rho) a) a :=
    ((contDiff_planarCoordinateWaveRadialAmplitude_radius part rho).differentiable
      (by simp) a).hasDerivAt
  have hphase := hasDerivAt_planarCoordinateWavePhase_radius part a rho
  unfold planarCoordinateWaveRadiusDerivativeTerm
    planarCoordinateWaveRadiusDerivativeAmplitude
  rw [(hamp.mul hphase).deriv]
  ring

/-- The planar coordinate amplitude depends on the radius and radial
frequency only through their product. -/
theorem planarCoordinateWaveRadialAmplitude_eq_unit_frequency
    (part : CoordinateWavePart) (a rho : Real) :
    planarCoordinateWaveRadialAmplitude part a rho =
      planarCoordinateWaveRadialAmplitude part 1 (a * rho) := by
  cases part <;> unfold planarCoordinateWaveRadialAmplitude <;> congr 2 <;> ring

/-- Radius differentiation of the nonoscillatory coordinate amplitude is a
scaled radial differentiation.  This is the identity which transfers the
all-order symbol estimates already proved for the literal endpoint and
middle integrals to the radius-differentiated normal form. -/
theorem deriv_planarCoordinateWaveRadialAmplitude_radius_eq_div_mul_iteratedDeriv
    (part : CoordinateWavePart) {a : Real} (ha : a ≠ 0) (rho : Real) :
    deriv (fun b : Real => planarCoordinateWaveRadialAmplitude part b rho) a =
      ((rho / a : Real) : Complex) *
        iteratedDeriv 1
          (fun u : Real => planarCoordinateWaveRadialAmplitude part a u) rho := by
  let G : Real → Complex := fun u : Real =>
    planarCoordinateWaveRadialAmplitude part 1 u
  have hG : ContDiff Real (⊤ : ℕ∞) G :=
    contDiff_planarCoordinateWaveRadialAmplitude part 1
  have hparam : HasDerivAt (fun b : Real => G (b * rho))
      (rho • deriv G (a * rho)) a := by
    simpa only [Function.comp_apply] using
      ((hG.differentiable (by simp) (a * rho)).hasDerivAt.scomp_of_eq
        ((hasDerivAt_id a).mul_const rho) (by rfl))
  have hradial : HasDerivAt (fun u : Real => G (a * u))
      (a • deriv G (a * rho)) rho := by
    simpa only [Function.comp_apply] using
      ((hG.differentiable (by simp) (a * rho)).hasDerivAt.scomp_of_eq
        ((hasDerivAt_id rho).const_mul a) (by rfl))
  have hparam' : HasDerivAt
      (fun b : Real => planarCoordinateWaveRadialAmplitude part b rho)
      (rho • deriv G (a * rho)) a := by
    rw [show (fun b : Real => planarCoordinateWaveRadialAmplitude part b rho) =
        fun b : Real => G (b * rho) by
      funext b
      dsimp [G]
      exact planarCoordinateWaveRadialAmplitude_eq_unit_frequency part b rho]
    exact hparam
  have hradial' : HasDerivAt
      (fun u : Real => planarCoordinateWaveRadialAmplitude part a u)
      (a • deriv G (a * rho)) rho := by
    rw [show (fun u : Real => planarCoordinateWaveRadialAmplitude part a u) =
        fun u : Real => G (a * u) by
      funext u
      dsimp [G]
      exact planarCoordinateWaveRadialAmplitude_eq_unit_frequency part a u]
    exact hradial
  rw [hparam'.deriv, iteratedDeriv_one, hradial'.deriv]
  rw [Complex.real_smul, Complex.real_smul]
  have hcast : (((rho / a : Real) : Complex) * (a : Complex)) = (rho : Complex) := by
    push_cast
    field_simp [ha]
  rw [← mul_assoc, hcast]

private theorem contDiff_planarCoordinateWaveRadialTerm_radius
    (part : CoordinateWavePart) (rho : Real) :
    ContDiff Real (⊤ : ℕ∞)
      (fun a : Real => planarCoordinateWaveRadialTerm part a rho) := by
  cases part <;> unfold planarCoordinateWaveRadialTerm
    planarCoordinateWaveRadialAmplitude coordinateWaveRadialPhase oscillatoryExp <;>
    fun_prop

private theorem hasDerivAt_planarCoordinateWaveRadialTerm_radius
    (part : CoordinateWavePart) (a rho : Real) :
    HasDerivAt (fun b : Real => planarCoordinateWaveRadialTerm part b rho)
      (planarCoordinateWaveRadiusDerivativeTerm part a rho) a := by
  unfold planarCoordinateWaveRadiusDerivativeTerm
  exact ((contDiff_planarCoordinateWaveRadialTerm_radius part rho).differentiable
    (by simp) a).hasDerivAt

/-- Differentiating the actual three-wave circle identity gives the exact
sum of the three radius-derivative waves on a positive radial ray. -/
theorem deriv_surfaceFourier_two_neg_radius_smul_eq_planarDerivativeWaveSum
    {r rho : Real} (hr : 0 < r) (hrho : 0 < rho)
    (v : Euclidean 2) (hv : ‖v‖ = 1) :
    deriv (fun a : Real => surfaceFourier 2 (a • (-(rho • v)))) r =
      planarCoordinateSurfaceRadiusDerivativeWaveSum r rho := by
  let f : Real → Complex := fun a : Real => surfaceFourier 2 (a • (-(rho • v)))
  let g : Real → Complex := fun a : Real =>
    planarCoordinateWaveRadialTerm .outgoing a rho +
      planarCoordinateWaveRadialTerm .incoming a rho +
        planarCoordinateWaveRadialTerm .middle a rho
  have hfg : f =ᶠ[𝓝 r] g := by
    filter_upwards [Ioi_mem_nhds hr] with a ha
    dsimp [f, g]
    rw [show a • (-(rho • v)) = -a • (rho • v) by
      rw [smul_neg]
      ring]
    rw [surfaceFourier_two_neg_radius_smul_eq_planarCoordinateSurfaceWaveSum ha hrho v hv,
      planarCoordinateSurfaceWaveSum_eq_three_radialTerms]
  have hout := hasDerivAt_planarCoordinateWaveRadialTerm_radius .outgoing r rho
  have hin := hasDerivAt_planarCoordinateWaveRadialTerm_radius .incoming r rho
  have hmid := hasDerivAt_planarCoordinateWaveRadialTerm_radius .middle r rho
  have hg : HasDerivAt g
      (planarCoordinateSurfaceRadiusDerivativeWaveSum r rho) r := by
    dsimp [g, planarCoordinateSurfaceRadiusDerivativeWaveSum]
    exact (hout.add hin).add hmid
  have hf : HasDerivAt f
      (planarCoordinateSurfaceRadiusDerivativeWaveSum r rho) r :=
    hg.congr_of_eventuallyEq hfg.symm
  exact hf.deriv

/-- At the normalized dyadic level, one literal scaled radius-derivative
multiplier is exactly the differentiated three-wave circle sum. -/
theorem q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier_zero_eq_planarDerivativeWaves
    (psi : SchwartzMap (Euclidean 2) Complex)
    {r rho : Real} (hr : 0 < r) (hrho : 0 < rho)
    (v : Euclidean 2) (hv : ‖v‖ = 1) :
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier psi 0 r (rho • v) =
      (surfaceMass 2 : Complex)⁻¹ *
        planarCoordinateSurfaceRadiusDerivativeWaveSum r rho * psi (rho • v) := by
  unfold q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier
    q4NormalizedDyadicSurfaceRadiusDerivativeMultiplier
  have hdyadic : dyadicScale 0 = 1 := by
    simp [dyadicScale, dyadicDenom]
  rw [hdyadic]
  norm_num
  rw [deriv_surfaceFourier_two_neg_radius_smul_eq_planarDerivativeWaveSum
    hr hrho v hv]

/-- The normalized derivative `TT*` multiplier is the literal product of
two differentiated planar wave sums, with the adjoint retained explicitly. -/
theorem q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier_zero_eq_planarDerivativeWaves
    (psi : SchwartzMap (Euclidean 2) Complex)
    {r r' rho : Real} (hr : 0 < r) (hr' : 0 < r') (hrho : 0 < rho)
    (v : Euclidean 2) (hv : ‖v‖ = 1) :
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier psi 0 r r' (rho • v) =
      ((surfaceMass 2 : Complex)⁻¹ *
        planarCoordinateSurfaceRadiusDerivativeWaveSum r rho * psi (rho • v)) *
        starRingEnd Complex
          ((surfaceMass 2 : Complex)⁻¹ *
            planarCoordinateSurfaceRadiusDerivativeWaveSum r' rho * psi (rho • v)) := by
  unfold q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier
  rw [q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier_zero_eq_planarDerivativeWaves
      psi hr hrho v hv,
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier_zero_eq_planarDerivativeWaves
      psi hr' hrho v hv]

/-- The scaled derivative multiplier remains norm-radial when the cutoff is
norm-radial.  This is the exact prerequisite for the polar reduction of its
physical `TT*` kernel. -/
theorem q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier_eq_of_norm_eq
    (psi : SchwartzMap (Euclidean 2) Complex) (hpsi : IsNormRadial psi)
    (j : Nat) (r : Real) {xi eta : Euclidean 2} (hxi : ‖xi‖ = ‖eta‖) :
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier psi j r xi =
      q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier psi j r eta := by
  unfold q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier
    q4NormalizedDyadicSurfaceRadiusDerivativeMultiplier
  have hfun : (fun s : Real => surfaceFourier 2 (s • (-xi))) =
      fun s : Real => surfaceFourier 2 (s • (-eta)) := by
    funext s
    apply surfaceFourier_eq_of_norm_eq
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      norm_neg, norm_neg, hxi]
  rw [hfun, hpsi hxi]

theorem q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier_eq_of_norm_eq
    (psi : SchwartzMap (Euclidean 2) Complex) (hpsi : IsNormRadial psi)
    (j : Nat) (r r' : Real) {xi eta : Euclidean 2} (hxi : ‖xi‖ = ‖eta‖) :
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier psi j r r' xi =
      q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier psi j r r' eta := by
  unfold q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier
  rw [q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier_eq_of_norm_eq
      psi hpsi j r hxi,
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier_eq_of_norm_eq
      psi hpsi j r' hxi]

/-- Scalar radial profile for the literal scaled derivative pair multiplier. -/
def q4ScaledNormalizedDerivativeRadialPairProfile
    (psi : SchwartzMap (Euclidean 2) Complex) (j : Nat) (r r' : Real)
    (v : Euclidean 2) (rho : Real) : Complex :=
  q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier psi j r r' (rho • v)

theorem q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier_eq_radialProfile
    (psi : SchwartzMap (Euclidean 2) Complex) (hpsi : IsNormRadial psi)
    (j : Nat) (r r' : Real) (v : Euclidean 2) (hv : ‖v‖ = 1)
    (xi : Euclidean 2) :
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier psi j r r' xi =
      q4ScaledNormalizedDerivativeRadialPairProfile psi j r r' v ‖xi‖ := by
  unfold q4ScaledNormalizedDerivativeRadialPairProfile
  apply q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier_eq_of_norm_eq
    psi hpsi j r r'
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hv, mul_one]

private theorem integrable_polar_q4ScaledNormalizedDerivativeRadialPairProfile
    (psi : SchwartzMap (Euclidean 2) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean 2 → Complex))
    (hpsiRadial : IsNormRadial psi) (j : Nat) (r r' : Real)
    (v : Euclidean 2) (hv : ‖v‖ = 1) (x : Euclidean 2) :
    Integrable (fun p : sphere (0 : Euclidean 2) 1 × Ioi (0 : Real) =>
      Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean 2)) x) •
        q4ScaledNormalizedDerivativeRadialPairProfile psi j r r' v p.2.1)
      ((unitSurfaceMeasure 2).prod (Measure.volumeIoiPow 1)) := by
  obtain ⟨m, hm⟩ :=
    exists_schwartz_q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier
      psi hpsiCompact j r r'
  apply integrable_polar_fourierChar_mul_of_schwartz_radial m
    (q4ScaledNormalizedDerivativeRadialPairProfile psi j r r')
  intro xi
  rw [hm xi]
  exact q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier_eq_radialProfile
    psi hpsiRadial j r r' v hv xi

/-- Exact polar reduction of the literal scaled derivative pair kernel in
the planar branch.  The physical circle factor is still present explicitly. -/
theorem q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairKernel_eq_surfaceFourier_integral_two
    (psi : SchwartzMap (Euclidean 2) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean 2 → Complex))
    (hpsiRadial : IsNormRadial psi) (j : Nat) (r r' : Real)
    (v x : Euclidean 2) (hv : ‖v‖ = 1) :
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairKernel psi j r r' x =
      ∫ rho : Ioi (0 : Real),
        surfaceFourier 2 (-rho.1 • x) *
          q4ScaledNormalizedDerivativeRadialPairProfile psi j r r' v rho.1
          ∂Measure.volumeIoiPow 1 := by
  unfold q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairKernel
  rw [show q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier psi j r r' =
      fun xi : Euclidean 2 =>
        q4ScaledNormalizedDerivativeRadialPairProfile psi j r r' v ‖xi‖ by
    funext xi
    exact q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier_eq_radialProfile
      psi hpsiRadial j r r' v hv xi]
  exact fourierInv_radial_eq_surfaceFourier_integral (by omega)
    (q4ScaledNormalizedDerivativeRadialPairProfile psi j r r' v) x
    (integrable_polar_q4ScaledNormalizedDerivativeRadialPairProfile
      psi hpsiCompact hpsiRadial j r r' v hv x)

/-- The derivative pair kernel for the actual absolute bandpass is an honest
compact annular integral.  This is the derivative analogue of the ordinary
radial starting identity, obtained before any stationary estimate. -/
theorem q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairKernel_absoluteDyadicBandpass_eq_annular_surfaceFourier_intervalIntegral_two
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiRadial : IsNormRadial phi) (j : Nat) (r r' : Real)
    (v x : Euclidean 2) (hv : ‖v‖ = 1) :
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairKernel
      (absoluteDyadicBandpass phi hphiOne hphiZero j) j r r' x =
      ∫ rho in (2 : Real) ^ j..(2 : Real) ^ (j + 2),
        (rho : Complex) * surfaceFourier 2 (-rho • x) *
          q4ScaledNormalizedDerivativeRadialPairProfile
            (absoluteDyadicBandpass phi hphiOne hphiZero j) j r r' v rho := by
  let psi : SchwartzMap (Euclidean 2) Complex :=
    absoluteDyadicBandpass phi hphiOne hphiZero j
  have hpsiCompact : HasCompactSupport (psi : Euclidean 2 → Complex) :=
    absoluteDyadicBandpass_compact phi hphiOne hphiZero j
  have hpsiRadial : IsNormRadial psi :=
    isNormRadial_absoluteDyadicBandpass phi hphiOne hphiZero hphiRadial j
  rw [q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairKernel_eq_surfaceFourier_integral_two
    psi hpsiCompact hpsiRadial j r r' v x hv]
  rw [integral_volumeIoiPow_eq_setIntegral]
  let F : Real → Complex := fun rho =>
    (rho : Complex) * surfaceFourier 2 (-rho • x) *
      q4ScaledNormalizedDerivativeRadialPairProfile psi j r r' v rho
  have ha : 0 < (2 : Real) ^ j := by positivity
  have hab : (2 : Real) ^ j ≤ (2 : Real) ^ (j + 2) := by
    calc
      (2 : Real) ^ j ≤ (2 : Real) ^ j * 4 := by nlinarith
      _ = (2 : Real) ^ j * (2 : Real) ^ 2 := by norm_num
      _ = (2 : Real) ^ (j + 2) := by rw [← pow_add]
  have hzero : ∀ rho, rho ∈ Ioi (0 : Real) →
      rho ∉ Icc ((2 : Real) ^ j) ((2 : Real) ^ (j + 2)) → F rho = 0 := by
    intro rho hrho hnot
    have hpsiZero : psi (rho • v) = 0 := by
      rw [show psi = absoluteDyadicBandpass phi hphiOne hphiZero j by rfl,
        absoluteDyadicBandpass_spec]
      have hnorm : ‖rho • v‖ = rho := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho, hv, mul_one]
      by_cases hlow : rho < (2 : Real) ^ j
      · apply smooth_dyadic_bandpass_eq_zero_of_norm_le hphiOne
        rw [hnorm]
        exact hlow.le
      · have hleft : (2 : Real) ^ j ≤ rho := le_of_not_gt hlow
        have hright : (2 : Real) ^ (j + 2) < rho := by
          apply lt_of_not_ge
          intro hupper
          exact hnot ⟨hleft, hupper⟩
        apply smooth_dyadic_bandpass_eq_zero_of_le_norm hphiZero
        rw [hnorm]
        exact hright.le
    dsimp [F, q4ScaledNormalizedDerivativeRadialPairProfile]
    unfold q4ScaledNormalizedDyadicSurfaceRadiusDerivativePairMultiplier
      q4ScaledNormalizedDyadicSurfaceRadiusDerivativeMultiplier
      q4NormalizedDyadicSurfaceRadiusDerivativeMultiplier
    rw [hpsiZero]
    simp
  rw [setIntegral_Ioi_eq_intervalIntegral_of_eq_zero_outside_general ha hab F hzero]
  apply intervalIntegral.integral_congr
  intro rho _
  dsimp only [F, psi]
  ring

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
