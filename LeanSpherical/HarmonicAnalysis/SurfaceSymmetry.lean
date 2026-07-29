/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Orthogonal symmetry of the concrete sphere measure

The measure `Measure.toSphere volume` is invariant under linear isometries.
This is the geometric reduction needed to turn a decay calculation in one
fixed direction into a radial Fourier-transform estimate.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set
open scoped Pointwise

noncomputable section

/-- Restricting a linear isometry to the unit sphere preserves the concrete
surface measure. -/
private theorem map_unitSurfaceMeasure_linearIsometry (d : Nat)
    (u : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) :
    let uSphere : sphere (0 : Euclidean d) 1 ≃ₜ sphere (0 : Euclidean d) 1 :=
      u.toHomeomorph.subtype (fun x => by
        simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
        rw [u.norm_map])
    Measure.map uSphere (unitSurfaceMeasure d) = unitSurfaceMeasure d := by
  dsimp only
  let uSphere : sphere (0 : Euclidean d) 1 ≃ₜ sphere (0 : Euclidean d) 1 :=
    u.toHomeomorph.subtype (fun x => by
      simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
      rw [u.norm_map])
  have huSphere : Measure.map uSphere (unitSurfaceMeasure d) = unitSurfaceMeasure d := by
    apply Measure.ext
    intro s hs
    simp only [unitSurfaceMeasure]
    rw [Measure.map_apply uSphere.continuous.measurable hs,
      Measure.toSphere_apply' (volume : Measure (Euclidean d))
        (hs.preimage uSphere.continuous.measurable),
      Measure.toSphere_apply' (volume : Measure (Euclidean d)) hs]
    congr 1
    let A : Set (Euclidean d) :=
      Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : Euclidean d) 1 → Euclidean d) ''
        (uSphere ⁻¹' s))
    let B : Set (Euclidean d) :=
      Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : Euclidean d) 1 → Euclidean d) '' s)
    change (volume : Measure (Euclidean d)) A = (volume : Measure (Euclidean d)) B
    have himage : u '' A = B := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with ⟨r, hr, z', hz', rfl⟩
        rcases hz' with ⟨ω, hω, rfl⟩
        refine ⟨r, hr, uSphere ω, ?_, ?_⟩
        · exact ⟨uSphere ω, hω, rfl⟩
        · simp [uSphere]
      · rintro ⟨r, hr, z, hz, rfl⟩
        rcases hz with ⟨ω, hω, rfl⟩
        refine ⟨r • ((uSphere.symm ω : sphere (0 : Euclidean d) 1) : Euclidean d), ?_, ?_⟩
        · refine ⟨r, hr, ((uSphere.symm ω : sphere (0 : Euclidean d) 1) : Euclidean d), ?_, rfl⟩
          refine ⟨uSphere.symm ω, ?_, rfl⟩
          simpa using hω
        · simp [uSphere]
    calc
      (volume : Measure (Euclidean d)) A =
          (volume : Measure (Euclidean d)) (u ⁻¹' (u '' A)) := by
            congr 1
            ext x
            simp
      _ = Measure.map u volume (u '' A) := by
            simpa only [LinearIsometryEquiv.coe_toMeasurableEquiv] using
              (u.toMeasurableEquiv.map_apply (μ := volume) (u '' A)).symm
      _ = (volume : Measure (Euclidean d)) (u '' A) := by
            rw [u.measurePreserving.map_eq]
      _ = (volume : Measure (Euclidean d)) B := by rw [himage]
  simpa only [uSphere] using huSphere

/-- The Fourier transform of the concrete sphere measure is invariant under
orthogonal changes of frequency coordinates. -/
theorem surfaceFourier_linearIsometry (d : Nat)
    (u : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) (ξ : Euclidean d) :
    surfaceFourier d (u ξ) = surfaceFourier d ξ := by
  let uSphere : sphere (0 : Euclidean d) 1 ≃ₜ sphere (0 : Euclidean d) 1 :=
    u.toHomeomorph.subtype (fun x => by
      simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
      rw [u.norm_map])
  have hmeasure : Measure.map uSphere (unitSurfaceMeasure d) = unitSurfaceMeasure d := by
    simpa only [uSphere] using map_unitSurfaceMeasure_linearIsometry d u
  have hpres : MeasurePreserving uSphere (unitSurfaceMeasure d) (unitSurfaceMeasure d) :=
    ⟨uSphere.continuous.measurable, hmeasure⟩
  have hintegral := hpres.integral_comp uSphere.measurableEmbedding
    (fun ω : sphere (0 : Euclidean d) 1 =>
      Complex.exp (surfacePhase d (u ξ) ω))
  calc
    surfaceFourier d (u ξ) =
        ∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (u ξ) ω) ∂unitSurfaceMeasure d := rfl
    _ = ∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d (u ξ) (uSphere ω)) ∂unitSurfaceMeasure d := hintegral.symm
    _ = ∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d ξ ω) ∂unitSurfaceMeasure d := by
      apply integral_congr_ae
      filter_upwards with ω
      apply congrArg Complex.exp
      have hinter : inner ℝ ((uSphere ω : sphere (0 : Euclidean d) 1) : Euclidean d) (u ξ) =
          inner ℝ (ω : Euclidean d) ξ := by
        change inner ℝ (u ω) (u ξ) = inner ℝ (ω : Euclidean d) ξ
        exact u.inner_map_map _ _
      unfold surfacePhase
      rw [hinter]
    _ = surfaceFourier d ξ := rfl

/-- The concrete sphere Fourier transform is radial. -/
theorem surfaceFourier_eq_of_norm_eq (d : Nat) {ξ η : Euclidean d}
    (hξη : ‖ξ‖ = ‖η‖) :
    surfaceFourier d ξ = surfaceFourier d η := by
  let u : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
    Submodule.reflection (ℝ ∙ (ξ - η))ᗮ
  have hu : u ξ = η := Submodule.reflection_sub hξη
  calc
    surfaceFourier d ξ = surfaceFourier d (u ξ) :=
      (surfaceFourier_linearIsometry d u ξ).symm
    _ = surfaceFourier d η := by rw [hu]

/-- Central symmetry of the sphere makes its Fourier transform even. -/
theorem surfaceFourier_neg (d : Nat) (ξ : Euclidean d) :
    surfaceFourier d (-ξ) = surfaceFourier d ξ := by
  apply surfaceFourier_eq_of_norm_eq d
  simp

/-- After choosing any unit direction, the sphere Fourier transform reduces
to the radial frequency on that direction. -/
theorem surfaceFourier_eq_norm_smul_unit (d : Nat) (ξ v : Euclidean d)
    (hv : ‖v‖ = 1) :
    surfaceFourier d ξ = surfaceFourier d (‖ξ‖ • v) := by
  apply surfaceFourier_eq_of_norm_eq d
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hv, mul_one]

end

end LeanSpherical.HarmonicAnalysis
