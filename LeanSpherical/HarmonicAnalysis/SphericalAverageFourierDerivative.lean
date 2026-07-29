/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.DerivativePrototype
import LeanSpherical.HarmonicAnalysis.PhysicalFourierBridge
import LeanSpherical.HarmonicAnalysis.SurfaceContinuity

/-!
# Differentiating the literal Fourier formula for spherical averages

For Schwartz data, the fixed-radius Fourier identity can be differentiated in
the radius parameter by dominated differentiation.  This file establishes that
literal identity and does not make a claim about a spatial maximal operator.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Metric Set
open scoped FourierTransform

noncomputable section

/-- For Schwartz data, differentiate the literal inverse-Fourier representation
of the spherical multiplier under the frequency integral. -/
theorem hasDerivAt_fourierInv_surfaceMultiplier_radial_schwartz
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) (r : ℝ) (x : Euclidean d) :
    HasDerivAt
      (fun s : ℝ => 𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (s • (-ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x)
      (𝓕⁻ (fun ξ : Euclidean d =>
        (∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω
            ∂unitSurfaceMeasure d) * 𝓕 (f : Euclidean d → ℂ) ξ) x)
      r := by
  let D : Euclidean d → ℂ := fun ξ =>
    ∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω
        ∂unitSurfaceMeasure d
  let F : ℝ → Euclidean d → ℂ := fun s ξ =>
    (Real.fourierChar (inner ℝ ξ x) : ℂ) *
      (surfaceFourier d (s • (-ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ)
  let F' : ℝ → Euclidean d → ℂ := fun s ξ =>
    (Real.fourierChar (inner ℝ ξ x) : ℂ) *
      ((∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d (s • (-ξ)) ω) * surfacePhase d (-ξ) ω
          ∂unitSurfaceMeasure d) * 𝓕 (f : Euclidean d → ℂ) ξ)
  have hinv (s : ℝ) :
      𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (s • (-ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x =
        ∫ ξ : Euclidean d, F s ξ := by
    rw [Real.fourierInv_eq]
    rfl
  have hinv' :
      𝓕⁻ (fun ξ : Euclidean d =>
        (∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω
            ∂unitSurfaceMeasure d) * 𝓕 (f : Euclidean d → ℂ) ξ) x =
        ∫ ξ : Euclidean d, F' r ξ := by
    rw [Real.fourierInv_eq]
    rfl
  rw [show (fun s : ℝ => 𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (s • (-ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x) =
      fun s => ∫ ξ : Euclidean d, F s ξ by
        funext s
        exact hinv s,
    hinv']
  have hchar (ξ : Euclidean d) : ‖(Real.fourierChar (inner ℝ ξ x) : ℂ)‖ = 1 := by
    rw [Real.fourierChar_apply]
    exact Complex.norm_exp_ofReal_mul_I _
  have hchar_cont : Continuous
      (fun ξ : Euclidean d => (Real.fourierChar (inner ℝ ξ x) : ℂ)) :=
    (Real.continuous_fourierChar.comp
      (continuous_id.inner (continuous_const : Continuous fun _ : Euclidean d => x))
      |> continuous_subtype_val.comp)
  have hFmeas : ∀ᶠ s in nhds r, AEStronglyMeasurable (F s) volume := by
    filter_upwards [] with s
    have hsurf : Continuous (fun ξ : Euclidean d => surfaceFourier d (s • (-ξ))) :=
      (continuous_surfaceFourier d).comp
        ((continuous_const : Continuous fun _ : Euclidean d => s).smul continuous_id.neg)
    exact (hchar_cont.mul (hsurf.mul (𝓕 f).continuous)).aestronglyMeasurable
  have hFint : Integrable (F r) volume := by
    have hmeas : AEStronglyMeasurable (F r) volume :=
      hFmeas.self_of_nhds
    refine ((𝓕 f).integrable.norm.const_mul (surfaceMass d)).mono' hmeas ?_
    filter_upwards with ξ
    dsimp only [F]
    rw [norm_mul, hchar, one_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa [surfaceMass] using norm_surfaceFourier_le_surfaceMass d (r • (-ξ)))
      (norm_nonneg _)
  have hDcont : Continuous D := by
    dsimp only [D]
    have hjoint : Continuous (Function.uncurry
        (fun (ξ : Euclidean d) (ω : sphere (0 : Euclidean d) 1) =>
          Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω)) := by
      unfold surfacePhase
      fun_prop
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := unitSurfaceMeasure d) hjoint isCompact_univ)
  have hF'meas : AEStronglyMeasurable (F' r) volume := by
    change AEStronglyMeasurable (fun ξ : Euclidean d =>
      (Real.fourierChar (inner ℝ ξ x) : ℂ) *
        (D ξ * 𝓕 (f : Euclidean d → ℂ) ξ)) volume
    exact (hchar_cont.mul (hDcont.mul (𝓕 f).continuous)).aestronglyMeasurable
  have hweighted : Integrable (fun ξ : Euclidean d => ‖ξ‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖)
      volume := by
    convert (𝓕 f).integrable_pow_mul volume 1 using 1
    funext ξ
    simp only [pow_one, SchwartzMap.fourier_coe]
  have hbound_int : Integrable (fun ξ : Euclidean d =>
      (2 * Real.pi * surfaceMass d) * (‖ξ‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖)) volume :=
    hweighted.const_mul _
  have hbound : ∀ᵐ ξ : Euclidean d ∂volume, ∀ s ∈ (Set.univ : Set ℝ),
      ‖F' s ξ‖ ≤ (2 * Real.pi * surfaceMass d) *
        (‖ξ‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖) := by
    filter_upwards with ξ
    intro s hs
    have hD : ‖∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d (s • (-ξ)) ω) * surfacePhase d (-ξ) ω
          ∂unitSurfaceMeasure d‖ ≤
        (2 * Real.pi * ‖-ξ‖) * (unitSurfaceMeasure d).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards with ω
      rw [norm_mul, norm_surfaceFourier_kernel]
      simpa using norm_surfacePhase_le d (-ξ) ω
    dsimp only [F']
    rw [norm_mul, hchar, one_mul, norm_mul]
    calc
      ‖∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (s • (-ξ)) ω) * surfacePhase d (-ξ) ω
            ∂unitSurfaceMeasure d‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖ ≤
          ((2 * Real.pi * ‖-ξ‖) * (unitSurfaceMeasure d).real Set.univ) *
            ‖𝓕 (f : Euclidean d → ℂ) ξ‖ :=
        mul_le_mul_of_nonneg_right hD (norm_nonneg _)
      _ = (2 * Real.pi * surfaceMass d) *
          (‖ξ‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖) := by
        simp only [surfaceMass, norm_neg]
        ring
  have hdiff : ∀ᵐ ξ : Euclidean d ∂volume, ∀ s ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun t => F t ξ) (F' s ξ) s := by
    filter_upwards with ξ
    intro s hs
    have hsurface := hasDerivAt_surfaceFourier_radial_at d (-ξ) s
    have hmul := (hsurface.mul_const (𝓕 (f : Euclidean d → ℂ) ξ)).const_mul
      (Real.fourierChar (inner ℝ ξ x) : ℂ)
    simpa only [F, F', D] using hmul
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Set.univ) (x₀ := r)
    (bound := fun ξ : Euclidean d =>
      (2 * Real.pi * surfaceMass d) * (‖ξ‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖))
    Filter.univ_mem hFmeas hFint hF'meas hbound hbound_int hdiff).2

/-- The fixed-radius Fourier identity transfers the preceding derivative theorem
to spherical averages of Schwartz data. -/
theorem hasDerivAt_sphericalAverage_fourierInv_surfaceDerivative_schwartz
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) (r : ℝ) (x : Euclidean d) :
    HasDerivAt
      (fun s : ℝ => sphericalAverage d (f : Euclidean d → ℂ) s x)
      (𝓕⁻ (fun ξ : Euclidean d =>
        (∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω
            ∂unitSurfaceMeasure d) * 𝓕 (f : Euclidean d → ℂ) ξ) x)
      r := by
  rw [show (fun s : ℝ => sphericalAverage d (f : Euclidean d → ℂ) s x) =
      fun s => 𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (s • (-ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x by
        funext s
        rw [sphericalAverage_eq_fourierInv_surfaceMultiplier_schwartz f s]
        apply congrArg (fun g : Euclidean d → ℂ => 𝓕⁻ g x)
        funext ξ
        simp only [neg_smul, smul_neg]]
  exact hasDerivAt_fourierInv_surfaceMultiplier_radial_schwartz f r x

end

end LeanSpherical.HarmonicAnalysis
