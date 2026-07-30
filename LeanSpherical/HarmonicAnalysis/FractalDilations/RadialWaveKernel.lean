/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.RadialPairKernel

/-!
# Polar reduction for radial wave kernels

The radius-gap estimate in the proof of Theorem 1 is an estimate for a
frequency-localized wave kernel.  When its multiplier is norm-radial, polar
coordinates first turn the inverse Fourier integral into the spherical Fourier
factor and a one-dimensional radial integral.  This file proves that reduction
in arbitrary positive dimension.  It is intentionally an exact Fubini
identity; the stationary/nonstationary estimates are proved in later files.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory FourierTransform Metric Set
open scoped FourierTransform

noncomputable section

/-- For an integrable radial profile, polar coordinates followed by Fubini
turn its inverse Fourier transform into the unit-sphere Fourier factor. -/
theorem fourierInv_radial_eq_surfaceFourier_integral
    {d : Nat} (hd : 0 < d) (F : Real -> Complex) (x : Euclidean d)
    (hInt : Integrable (fun p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) =>
      Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) • F p.2.1)
      ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) ) :
    𝓕⁻ (fun xi : Euclidean d => F ‖xi‖) x =
      ∫ rho : Ioi (0 : Real),
        surfaceFourier d (-rho.1 • x) * F rho.1
          ∂Measure.volumeIoiPow (d - 1) := by
  rw [fourierInv_radial_eq_polar hd F x]
  calc
    (∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real),
        Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) • F p.2.1
          ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1)))) =
        ∫ rho : Ioi (0 : Real),
          ∫ omega : sphere (0 : Euclidean d) 1,
            Real.fourierChar (inner Real (rho.1 • (omega : Euclidean d)) x) • F rho.1
              ∂unitSurfaceMeasure d ∂Measure.volumeIoiPow (d - 1) :=
      integral_prod_symm _ hInt
    _ = ∫ rho : Ioi (0 : Real),
          (∫ omega : sphere (0 : Euclidean d) 1,
            (Real.fourierChar (inner Real (rho.1 • (omega : Euclidean d)) x) : Complex)
              ∂unitSurfaceMeasure d) * F rho.1
            ∂Measure.volumeIoiPow (d - 1) := by
      apply integral_congr_ae
      filter_upwards with rho
      change (∫ omega : sphere (0 : Euclidean d) 1,
          (Real.fourierChar (inner Real (rho.1 • (omega : Euclidean d)) x) : Complex) *
            F rho.1 ∂unitSurfaceMeasure d) = _
      rw [integral_mul_const]
    _ = ∫ rho : Ioi (0 : Real),
          surfaceFourier d (-rho.1 • x) * F rho.1
            ∂Measure.volumeIoiPow (d - 1) := by
      apply integral_congr_ae
      filter_upwards with rho
      rw [polar_angular_fourierChar_eq_surfaceFourier]

/-- A Schwartz radial multiplier provides the integrability premise for the
polar/Fubini formula.  The oscillatory character has norm one, so this is a
literal transport of Schwartz integrability through polar coordinates. -/
theorem integrable_polar_fourierChar_mul_of_schwartz_radial
    {d : Nat} (m : SchwartzMap (Euclidean d) Complex) (F : Real -> Complex)
    (hmrad : ∀ xi : Euclidean d, m xi = F ‖xi‖) (x : Euclidean d) :
    Integrable (fun p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) =>
      Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) • F p.2.1)
      ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
  let U : Set (Euclidean d) := {0}ᶜ
  let h : U ≃ₜ (sphere (0 : Euclidean d) 1 × Ioi (0 : Real)) :=
    homeomorphUnitSphereProd (Euclidean d)
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact (measurableSet_singleton _).compl
  have hmU : Integrable (fun z : U => m (z : Euclidean d))
      ((volume : Measure (Euclidean d)).comap (fun z : U => (z : Euclidean d))) := by
    change Integrable ((m : Euclidean d -> Complex) ∘ (fun z : U => (z : Euclidean d)))
      ((volume : Measure (Euclidean d)).comap (fun z : U => (z : Euclidean d)))
    rw [← integrableOn_iff_comap_subtypeVal hUmeas]
    exact m.integrable.integrableOn
  let G : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) -> Complex :=
    (m : Euclidean d -> Complex) ∘ Subtype.val ∘ h.symm
  have hG : Integrable G ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
    have htransport :=
      MeasurePreserving.integrable_comp_emb (g := G)
        ((volume : Measure (Euclidean d)).measurePreserving_homeomorphUnitSphereProd)
        (Homeomorph.measurableEmbedding h)
    have hcomp : Integrable (G ∘ h)
        ((volume : Measure (Euclidean d)).comap (fun z : U => (z : Euclidean d))) := by
      refine hmU.congr (Filter.Eventually.of_forall ?_)
      intro z
      dsimp [G, Function.comp_def]
      rw [Homeomorph.symm_apply_apply]
    simpa [unitSurfaceMeasure] using htransport.mp hcomp
  have hGpolar : Integrable (fun p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) =>
      m (p.2.1 • (p.1 : Euclidean d)))
      ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
    refine hG.congr (Filter.Eventually.of_forall ?_)
    intro p
    change m (((h.symm p : U) : Euclidean d)) = m (p.2.1 • (p.1 : Euclidean d))
    change m (((homeomorphUnitSphereProd (Euclidean d)).symm p :
      ({0}ᶜ : Set (Euclidean d))) : Euclidean d) = m (p.2.1 • (p.1 : Euclidean d))
    rfl
  let H : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) -> Complex := fun p =>
    (Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) : Complex) *
      m (p.2.1 • (p.1 : Euclidean d))
  have hHcont : Continuous H := by
    dsimp [H]
    fun_prop
  have hH : Integrable H ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
    refine hGpolar.mono hHcont.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro p
    have hchar : ‖(Real.fourierChar
        (inner Real (p.2.1 • (p.1 : Euclidean d)) x) : Complex)‖ = 1 := by
      rw [Real.fourierChar_apply]
      exact Complex.norm_exp_ofReal_mul_I _
    simpa only [H, norm_mul, hchar, one_mul] using
      (le_refl ‖m (p.2.1 • (p.1 : Euclidean d))‖)
  refine hH.congr (Filter.Eventually.of_forall ?_)
  intro p
  have hp : ‖(p.1 : Euclidean d)‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using p.1.property
  have hnorm : ‖p.2.1 • (p.1 : Euclidean d)‖ = p.2.1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.2, hp, mul_one]
  dsimp [H]
  change (Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) : Complex) *
      m (p.2.1 • (p.1 : Euclidean d)) =
    (Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) : Complex) * F p.2.1
  rw [hmrad (p.2.1 • (p.1 : Euclidean d)), hnorm]

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
