/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Fourier identities and fixed-radius estimates for spherical averages

This file proves the Fubini bridge from the concrete geometric average to its
Fourier multiplier, together with the direct fixed-radius `L¹` estimate.
-/

open MeasureTheory Metric Set FourierTransform
open scoped FourierTransform

noncomputable section

namespace LeanSpherical.HarmonicAnalysis

variable {d : ℕ}

private theorem integrable_sphere_translate_product
    (f : Euclidean d → ℂ) (hfcont : Continuous f) (hf : Integrable f volume) (r : ℝ) :
    Integrable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        f (p.1 + r • (p.2 : Euclidean d)))
      (volume.prod (unitSurfaceMeasure d)) := by
  have hmeas : AEStronglyMeasurable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        f (p.1 + r • (p.2 : Euclidean d)))
      (volume.prod (unitSurfaceMeasure d)) := by
    apply (hfcont.comp (continuous_fst.add
      ((continuous_const : Continuous fun _ : Euclidean d × sphere (0 : Euclidean d) 1 => r).smul
        (continuous_subtype_val.comp continuous_snd)))).aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).2 ?_
  constructor
  · filter_upwards with ω
    exact hf.comp_add_right (r • (ω : Euclidean d))
  · have h_eq : (fun ω : sphere (0 : Euclidean d) 1 =>
        ∫ x : Euclidean d, ‖f (x + r • (ω : Euclidean d))‖) =
        fun _ => ∫ x : Euclidean d, ‖f x‖ := by
      funext ω
      exact integral_add_right_eq_self (fun x : Euclidean d => ‖f x‖)
        (r • (ω : Euclidean d))
    rw [h_eq]
    exact integrable_const _

private theorem integrable_fourier_sphere_translate_product
    (f : Euclidean d → ℂ) (hfcont : Continuous f) (hf : Integrable f volume)
    (r : ℝ) (ξ : Euclidean d) :
    Integrable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        Complex.exp (((-2 * Real.pi * inner ℝ p.1 ξ : ℝ) : ℂ) * Complex.I) *
          f (p.1 + r • (p.2 : Euclidean d)))
      (volume.prod (unitSurfaceMeasure d)) := by
  apply (integrable_sphere_translate_product f hfcont hf r).mono
  · exact (by
      fun_prop : Continuous (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        Complex.exp (((-2 * Real.pi * inner ℝ p.1 ξ : ℝ) : ℂ) * Complex.I) *
          f (p.1 + r • (p.2 : Euclidean d)))).aestronglyMeasurable
  · filter_upwards with p
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem integrable_sphericalAverage
    (f : Euclidean d → ℂ) (hfcont : Continuous f) (hf : Integrable f volume) (r : ℝ) :
    Integrable (sphericalAverage d f r) volume := by
  change Integrable (fun x : Euclidean d =>
    ∫ ω : sphere (0 : Euclidean d) 1,
      f (x + r • (ω : Euclidean d)) ∂unitSurfaceMeasure d) volume
  exact (integrable_sphere_translate_product f hfcont hf r).integral_prod_left

/-- A fixed spherical average satisfies the direct `L¹` estimate obtained by
Fubini and translation invariance. -/
theorem integral_norm_sphericalAverage_le_surfaceMass_mul
    (f : Euclidean d → ℂ) (hfcont : Continuous f) (hf : Integrable f volume)
    (r : ℝ) :
    (∫ x : Euclidean d, ‖sphericalAverage d f r x‖) ≤
      surfaceMass d * ∫ x : Euclidean d, ‖f x‖ := by
  have hprod : Integrable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        ‖f (p.1 + r • (p.2 : Euclidean d))‖)
      (volume.prod (unitSurfaceMeasure d)) :=
    (integrable_sphere_translate_product f hfcont hf r).norm
  calc
    (∫ x : Euclidean d, ‖sphericalAverage d f r x‖) ≤
        ∫ x : Euclidean d, ∫ ω : sphere (0 : Euclidean d) 1,
          ‖f (x + r • (ω : Euclidean d))‖ ∂unitSurfaceMeasure d := by
      apply integral_mono_ae (integrable_sphericalAverage f hfcont hf r).norm
        hprod.integral_prod_left
      filter_upwards with x
      exact norm_integral_le_integral_norm _
    _ = ∫ ω : sphere (0 : Euclidean d) 1, (∫ x : Euclidean d,
        ‖f (x + r • (ω : Euclidean d))‖) ∂unitSurfaceMeasure d :=
      integral_integral_swap hprod
    _ = ∫ _ : sphere (0 : Euclidean d) 1, (∫ x : Euclidean d, ‖f x‖)
        ∂unitSurfaceMeasure d := by
      apply integral_congr_ae
      filter_upwards with ω
      exact integral_add_right_eq_self (fun x : Euclidean d => ‖f x‖) _
    _ = surfaceMass d * ∫ x : Euclidean d, ‖f x‖ := by
      simp [surfaceMass]

private theorem fourier_comp_add_right (f : Euclidean d → ℂ) (a ξ : Euclidean d) :
    𝓕 (f ∘ fun x => x + a) ξ = 𝐞 (inner ℝ a ξ) • 𝓕 f ξ := by
  exact congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ (Euclidean d)) f a) ξ

theorem fourier_sphericalAverage
    (f : Euclidean d → ℂ) (hfcont : Continuous f) (hf : Integrable f volume)
    (r : ℝ) (ξ : Euclidean d) :
    𝓕 (sphericalAverage d f r) ξ =
      surfaceFourier d (-r • ξ) * 𝓕 f ξ := by
  have hprod := integrable_fourier_sphere_translate_product f hfcont hf r ξ
  rw [Real.fourier_eq']
  simp only [smul_eq_mul]
  calc
    ∫ x : Euclidean d,
        Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
          sphericalAverage d f r x =
        ∫ x : Euclidean d, ∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
            f (x + r • (ω : Euclidean d)) ∂unitSurfaceMeasure d := by
      apply integral_congr_ae
      filter_upwards with x
      rw [sphericalAverage, ← integral_const_mul]
    _ = ∫ ω : sphere (0 : Euclidean d) 1, (∫ x : Euclidean d,
          Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
            f (x + r • (ω : Euclidean d))) ∂unitSurfaceMeasure d := by
      exact integral_integral_swap hprod
    _ = ∫ ω : sphere (0 : Euclidean d) 1,
          (𝓕 (f ∘ fun x => x + r • (ω : Euclidean d)) ξ) ∂unitSurfaceMeasure d := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [Real.fourier_eq']
      simp only [smul_eq_mul]
      rfl
    _ = ∫ ω : sphere (0 : Euclidean d) 1,
          (Real.fourierChar (inner ℝ (r • (ω : Euclidean d)) ξ) • 𝓕 f ξ)
          ∂unitSurfaceMeasure d := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [fourier_comp_add_right]
    _ = (∫ ω : sphere (0 : Euclidean d) 1,
          (Real.fourierChar (inner ℝ (r • (ω : Euclidean d)) ξ) : ℂ)
          ∂unitSurfaceMeasure d) * 𝓕 f ξ := by
      change (∫ ω : sphere (0 : Euclidean d) 1,
          (Real.fourierChar (inner ℝ (r • (ω : Euclidean d)) ξ) : ℂ) * 𝓕 f ξ
          ∂unitSurfaceMeasure d) = _
      rw [integral_mul_const]
    _ = surfaceFourier d (-r • ξ) * 𝓕 f ξ := by
      congr 1
      symm
      unfold surfaceFourier
      apply integral_congr_ae
      filter_upwards with ω
      rw [surfacePhase, Real.fourierChar_apply]
      simp only [inner_smul_right, inner_smul_left]
      push_cast
      simp only [starRingEnd_apply, star_trivial]
      congr 1
      ring

end LeanSpherical.HarmonicAnalysis
