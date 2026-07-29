/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure

/-!
# Cartesian splittings in arbitrary Euclidean dimension

The inductive geometry of spherical surface measure separates the final
coordinate of `Euclidean (d + 1)`.  These direct theorems give the
measure-preserving identification with `Euclidean d × ℝ` and the accompanying
norm identity, without introducing a new coordinate structure.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory

noncomputable section

/-- Separating the final coordinate of `Euclidean (d + 1)` pushes Lebesgue
measure forward to the product of Lebesgue measures. -/
theorem map_euclideanSucc_coordinates_volume (d : Nat) :
    Measure.map (fun x : Euclidean (d + 1) =>
      (MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i)),
        x (Fin.last d))) volume =
      ((volume : Measure (Euclidean d)).prod volume) := by
  let e₀ : Euclidean (d + 1) ≃ᵐ (Fin (d + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm
  let e₁ : (Fin (d + 1) → ℝ) ≃ᵐ (Fin d ⊕ Fin 1 → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
      (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm
  let e₂ : (Fin d ⊕ Fin 1 → ℝ) ≃ᵐ (Fin d → ℝ) × (Fin 1 → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin 1 ↦ ℝ)
  let e₃ : (Fin d → ℝ) × (Fin 1 → ℝ) ≃ᵐ Euclidean d × ℝ :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin d → ℝ))
      (MeasurableEquiv.piUnique fun _ : Fin 1 ↦ ℝ)
  let e : Euclidean (d + 1) ≃ᵐ Euclidean d × ℝ :=
    e₀.trans (e₁.trans (e₂.trans e₃))
  have he₀ : MeasurePreserving e₀ volume volume := by
    simpa only [e₀, MeasurableEquiv.coe_toLp_symm] using
      (PiLp.volume_preserving_ofLp (Fin (d + 1)))
  have he₁ : MeasurePreserving e₁ volume volume := by
    simpa only [e₁] using
      (volume_measurePreserving_piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
        (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm
  have he₂ : MeasurePreserving e₂ volume volume := by
    simpa only [e₂] using
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin d ⊕ Fin 1 ↦ ℝ))
  have he₃a : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℝ)) volume volume := by
    exact PiLp.volume_preserving_toLp (Fin d)
  have he₃b : MeasurePreserving (MeasurableEquiv.piUnique fun _ : Fin 1 ↦ ℝ)
      volume volume := by
    exact volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ)
  have he₃ : MeasurePreserving e₃ volume ((volume : Measure (Euclidean d)).prod volume) := by
    change MeasurePreserving
      (Prod.map (MeasurableEquiv.toLp 2 (Fin d → ℝ))
        (MeasurableEquiv.piUnique fun _ : Fin 1 ↦ ℝ))
      volume ((volume : Measure (Euclidean d)).prod volume)
    simpa only [Measure.volume_eq_prod] using he₃a.prod he₃b
  have he : MeasurePreserving e volume ((volume : Measure (Euclidean d)).prod volume) := by
    change MeasurePreserving (e₃ ∘ e₂ ∘ e₁ ∘ e₀) volume
      ((volume : Measure (Euclidean d)).prod volume)
    exact he₃.comp (he₂.comp (he₁.comp he₀))
  have heq : (e : Euclidean (d + 1) → Euclidean d × ℝ) =
      fun x =>
        (MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i)),
          x (Fin.last d)) := by
    funext x
    change
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)
          (fun i => (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
            (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm x.ofLp (Sum.inl i)),
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
          (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm x.ofLp (Sum.inr 0)) = _
    have hleft (i : Fin d) :
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
          (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm x.ofLp (Sum.inl i) =
          x.ofLp (Fin.castAdd 1 i) := by
      rfl
    have hright (i : Fin 1) :
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
          (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm x.ofLp (Sum.inr i) =
          x.ofLp (Fin.natAdd d i) := by
      rfl
    simp_rw [hleft]
    rw [hright 0]
    rfl
  rw [← heq]
  exact he.map_eq

/-- The Euclidean square norm splits into its first `d` coordinates and its
final coordinate. -/
theorem norm_sq_euclideanSucc_coordinates (d : Nat) (x : Euclidean (d + 1)) :
    ‖x‖ ^ 2 =
      ‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
        (x (Fin.last d)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [MeasurableEquiv.coe_toLp, PiLp.toLp_apply]
  rw [Fin.sum_univ_castSucc]
  rfl

/-- The square-root form of the arbitrary-dimensional Cartesian norm split. -/
theorem norm_euclideanSucc_coordinates (d : Nat) (x : Euclidean (d + 1)) :
    ‖x‖ =
      Real.sqrt
        (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
          (x (Fin.last d)) ^ 2) := by
  calc
    ‖x‖ = |‖x‖| := (abs_of_nonneg (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt
        (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
          (x (Fin.last d)) ^ 2) := by
      rw [norm_sq_euclideanSucc_coordinates]

end

end LeanSpherical.HarmonicAnalysis
