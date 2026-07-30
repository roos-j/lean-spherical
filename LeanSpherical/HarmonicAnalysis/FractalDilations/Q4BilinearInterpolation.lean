/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4TTStar

/-!
# Finite bilinear interpolation for the `Q4` shell argument

The radius-gap argument in Section 3 of Anderson--Hughes--Roos--Seeger has
crossed endpoints.  At one fixed shell its `TT*` operator has an `L¹ → L∞`
bound and an `L² → L²` bound.  Ordinary Marcinkiewicz interpolation is not the
right theorem for those crossed exponents.

This file contains the finite, bilinear real-interpolation calculation which
is valid without any analytic-family machinery.  First, two scalar endpoint
bounds are mixed by a weighted geometric mean.  Then a bilinear form is
expanded on finite atomic decompositions.  Thus a later measurable simple
function layer can turn the genuine kernel and counting estimates into the
usual Lorentz restricted estimate; no endpoint claim is made here.

The results are deliberately algebraic: the analytic `TT*` realization is
responsible for supplying the endpoint estimates for its atoms.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open scoped BigOperators

noncomputable section

/-- A number controlled by two nonnegative endpoint quantities is controlled
by their weighted geometric mean.  This is the scalar interpolation step
behind the finite `TT*` argument. -/
theorem le_weighted_geometric_mean_of_le
    {x a b θ : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxa : x ≤ a) (hxb : x ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    x ≤ a ^ (1 - θ) * b ^ θ := by
  by_cases hxzero : x = 0
  · rw [hxzero]
    exact mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hleft : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hpow_a : x ^ (1 - θ) ≤ a ^ (1 - θ) :=
    Real.rpow_le_rpow hx hxa hleft
  have hpow_b : x ^ θ ≤ b ^ θ :=
    Real.rpow_le_rpow hx hxb hθ0
  calc
    x = x ^ ((1 - θ) + θ) := by ring_nf; rw [Real.rpow_one]
    _ = x ^ (1 - θ) * x ^ θ := by rw [Real.rpow_add hxpos]
    _ ≤ a ^ (1 - θ) * b ^ θ :=
      mul_le_mul hpow_a hpow_b (Real.rpow_nonneg hx _) (Real.rpow_nonneg ha _)

/-- A bilinear form evaluated on two finite atomic sums is bounded by the
corresponding double sum of its atomic bounds. -/
theorem norm_bilinear_finset_sum_le
    {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [Module ℂ F] [Module ℂ G]
    {ι κ : Type*} (B : F →ₗ[ℂ] G →ₗ[ℂ] ℂ)
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → G)
    (c : ι → ℂ) (d : κ → ℂ) (M : ι → κ → ℝ)
    (hM : ∀ i ∈ s, ∀ j ∈ t, ‖B (u i) (v j)‖ ≤ M i j) :
    ‖B (∑ i ∈ s, c i • u i) (∑ j ∈ t, d j • v j)‖ ≤
      ∑ i ∈ s, ∑ j ∈ t, ‖c i‖ * ‖d j‖ * M i j := by
  have h_expand :
      B (∑ i ∈ s, c i • u i) (∑ j ∈ t, d j • v j) =
        ∑ i ∈ s, ∑ j ∈ t, (c i * d j) • B (u i) (v j) := by
    calc
      B (∑ i ∈ s, c i • u i) (∑ j ∈ t, d j • v j) =
          (∑ i ∈ s, B (c i • u i)) (∑ j ∈ t, d j • v j) := by
            rw [map_sum B]
      _ = ∑ i ∈ s, B (c i • u i) (∑ j ∈ t, d j • v j) := by
            rw [LinearMap.sum_apply]
      _ = ∑ i ∈ s, ∑ j ∈ t, B (c i • u i) (d j • v j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_sum]
      _ = ∑ i ∈ s, ∑ j ∈ t, (c i * d j) • B (u i) (v j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [map_smul, LinearMap.map_smul]
            rw [mul_comm (c i) (d j)]
            rw [LinearMap.smul_apply, smul_smul]
  rw [h_expand]
  calc
    ‖∑ i ∈ s, ∑ j ∈ t, (c i * d j) • B (u i) (v j)‖ ≤
        ∑ i ∈ s, ∑ j ∈ t, ‖(c i * d j) • B (u i) (v j)‖ :=
      calc
        ‖∑ i ∈ s, ∑ j ∈ t, (c i * d j) • B (u i) (v j)‖ ≤
            ∑ i ∈ s, ‖∑ j ∈ t, (c i * d j) • B (u i) (v j)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖(c i * d j) • B (u i) (v j)‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact norm_sum_le _ _
    _ = ∑ i ∈ s, ∑ j ∈ t, ‖c i‖ * ‖d j‖ * ‖B (u i) (v j)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_smul, norm_mul]
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖c i‖ * ‖d j‖ * M i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hM i hi j hj)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Finite atomic bilinear interpolation between crossed `L¹ × L¹` and
`L² × L²` bounds.  The conclusion is the finite Lorentz/restricted estimate
needed for a sampled-radius `TT*` shell.  It is intentionally expressed as a
double atomic sum, so it applies before any particular choice of simple
function decomposition. -/
theorem norm_bilinear_finset_sum_le_interpolate
    {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [Module ℂ F] [Module ℂ G]
    {ι κ : Type*} (B : F →ₗ[ℂ] G →ₗ[ℂ] ℂ)
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → G)
    (c : ι → ℂ) (d : κ → ℂ)
    (A₁ A₂ : ι → κ → ℝ) {θ : ℝ}
    (hA₁ : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ A₁ i j)
    (hA₂ : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ A₂ i j)
    (hone : ∀ i ∈ s, ∀ j ∈ t, ‖B (u i) (v j)‖ ≤ A₁ i j)
    (htwo : ∀ i ∈ s, ∀ j ∈ t, ‖B (u i) (v j)‖ ≤ A₂ i j)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖B (∑ i ∈ s, c i • u i) (∑ j ∈ t, d j • v j)‖ ≤
      ∑ i ∈ s, ∑ j ∈ t,
        ‖c i‖ * ‖d j‖ * (A₁ i j) ^ (1 - θ) * (A₂ i j) ^ θ := by
  let M : ι → κ → ℝ := fun i j => (A₁ i j) ^ (1 - θ) * (A₂ i j) ^ θ
  have hM : ∀ i ∈ s, ∀ j ∈ t, ‖B (u i) (v j)‖ ≤ M i j := by
    intro i hi j hj
    exact le_weighted_geometric_mean_of_le (norm_nonneg _)
      (hA₁ i hi j hj) (hA₂ i hi j hj) (hone i hi j hj) (htwo i hi j hj) hθ0 hθ1
  have hsum := norm_bilinear_finset_sum_le B s t u v c d M hM
  simpa only [M, mul_assoc] using hsum

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
