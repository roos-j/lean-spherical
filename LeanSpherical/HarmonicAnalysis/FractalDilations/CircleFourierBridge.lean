/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SphericalMaximalL2
import LeanSpherical.HarmonicAnalysis.FractalDilations.CircleSurface

/-!
# The analytic interface for the planar circle

The planar circle has a different height density from the dimensions covered
by the general height-coordinate development.  `CircleSurface` proves its
angular parametrization and sharp estimates directly.  This file packages
those facts for the existing dyadic maximal-function machinery.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set
open scoped FourierTransform

noncomputable section

/-- The two sharp circle estimates needed by the radius-Sobolev and `TT*`
arguments.  The derivative exponent is negative: differentiating the circle
transform costs one power of frequency. -/
def HasCircleSurfaceFourierSharpBounds : Prop :=
  ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
    (∀ ξ : Euclidean 2, 1 ≤ ‖ξ‖ →
      ‖surfaceFourier 2 ξ‖ ≤ C₀ / ‖ξ‖ ^ ((1 : ℝ) / 2)) ∧
    (∀ ξ : Euclidean 2, ∀ r : ℝ, 1 ≤ ‖ξ‖ → r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun s : ℝ => surfaceFourier 2 (s • ξ)) r‖ ≤
        C₁ / ‖ξ‖ ^ ((1 : ℝ) / 2 - 1))

/-- The angular circle development supplies the sharp bounds required by the
generic dyadic interface. -/
theorem hasCircleSurfaceFourierSharpBounds : HasCircleSurfaceFourierSharpBounds := by
  rcases exists_sharp_surfaceFourier_two_decay_and_deriv with
    ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩
  exact ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩

/-- The already-formalized smooth-bandpass argument specializes without any
dimension restriction once the sharp circle decay is supplied. -/
theorem norm_circle_surfaceFourier_smul_mul_smooth_dyadic_bandpass_le_of_sharp
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hdecay : ∀ ξ : Euclidean 2, 1 ≤ ‖ξ‖ →
      ‖surfaceFourier 2 ξ‖ ≤ C₀ / ‖ξ‖ ^ ((1 : ℝ) / 2))
    {φ : SchwartzMap (Euclidean 2) ℂ}
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (hφnorm : ∀ ξ, ‖φ ξ‖ ≤ 1)
    (j : ℕ) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (ξ : Euclidean 2) :
    ‖surfaceFourier 2 (r • ξ) *
      (φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        φ (((2 : ℝ) ^ j)⁻¹ • ξ))‖ ≤
      (2 * C₀) / dyadicScale j ^ ((1 : ℝ) / 2) := by
  have hdecay' : ∀ ξ : Euclidean (1 + 1), 1 ≤ ‖ξ‖ →
      ‖surfaceFourier (1 + 1) ξ‖ ≤ C₀ / ‖ξ‖ ^ (((1 : ℕ) : ℝ) / 2) := by
    simpa using hdecay
  simpa using
    norm_surfaceFourier_succ_smul_mul_smooth_dyadic_bandpass_le_of_sharp
      (d := 1) C₀ hC₀ hdecay' hφone hφzero hφnorm j r hr ξ

/-- The preceding multiplier estimate is available directly from the bundled
circle interface. -/
theorem HasCircleSurfaceFourierSharpBounds.bandpass_decay
    (hcircle : HasCircleSurfaceFourierSharpBounds)
    {φ : SchwartzMap (Euclidean 2) ℂ}
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (hφnorm : ∀ ξ, ‖φ ξ‖ ≤ 1)
    (j : ℕ) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (ξ : Euclidean 2) :
    ∃ C : ℝ, 0 < C ∧
      ‖surfaceFourier 2 (r • ξ) *
        (φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ))‖ ≤
        C / dyadicScale j ^ ((1 : ℝ) / 2) := by
  rcases hcircle with ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩
  exact ⟨2 * C₀, mul_pos (by norm_num) hC₀,
    norm_circle_surfaceFourier_smul_mul_smooth_dyadic_bandpass_le_of_sharp
      C₀ hC₀ hdecay hφone hφzero hφnorm j r hr ξ⟩

/-- In dimension two, a radius derivative grows like the square root of the
dyadic frequency.  This is the localized consequence of the circle derivative
estimate; it is deliberately separate from the unavailable circle
stationary-phase proof. -/
theorem norm_deriv_circle_surfaceFourier_smul_mul_smooth_dyadic_bandpass_le_of_sharp
    (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hderiv : ∀ ξ : Euclidean 2, ∀ r : ℝ, 1 ≤ ‖ξ‖ → r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun s : ℝ => surfaceFourier 2 (s • ξ)) r‖ ≤
        C₁ / ‖ξ‖ ^ ((1 : ℝ) / 2 - 1))
    {φ : SchwartzMap (Euclidean 2) ℂ}
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (hφnorm : ∀ ξ, ‖φ ξ‖ ≤ 1)
    (j : ℕ) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (ξ : Euclidean 2) :
    ‖deriv (fun s : ℝ => surfaceFourier 2 (s • ξ)) r *
      (φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        φ (((2 : ℝ) ^ j)⁻¹ • ξ))‖ ≤
      4 * C₁ * dyadicScale j ^ ((1 : ℝ) / 2) := by
  let q : ℂ := φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
    φ (((2 : ℝ) ^ j)⁻¹ • ξ)
  have hscale : 0 < dyadicScale j := dyadicScale_pos j
  have hscale_one : 1 ≤ dyadicScale j := by
    calc
      1 = dyadicScale 0 := by simp [dyadicScale]
      _ ≤ dyadicScale j := dyadicScale_mono (Nat.zero_le j)
  by_cases hq : q = 0
  · change ‖deriv (fun s : ℝ => surfaceFourier 2 (s • ξ)) r * q‖ ≤ _
    rw [hq, mul_zero, norm_zero]
    positivity
  have hq' : φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
      φ (((2 : ℝ) ^ j)⁻¹ • ξ) ≠ 0 := by
    simpa only [q] using hq
  have hsupport :=
    smooth_dyadic_bandpass_norm_bounds_of_ne_zero hφone hφzero hq'
  have hlower : dyadicScale j < ‖ξ‖ := by
    simpa only [dyadicScale] using hsupport.1
  have hupper : ‖ξ‖ ≤ 4 * dyadicScale j := by
    calc
      ‖ξ‖ ≤ (2 : ℝ) ^ (j + 2) := hsupport.2.le
      _ = 4 * dyadicScale j := by
        simp only [dyadicScale, pow_add]
        ring
  have hξone : 1 ≤ ‖ξ‖ := hscale_one.trans hlower.le
  have hξpos : 0 < ‖ξ‖ := lt_of_lt_of_le (by norm_num) hξone
  have hroot : ‖ξ‖ ^ ((1 : ℝ) / 2) ≤
      (4 * dyadicScale j) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (norm_nonneg _) hupper (by norm_num)
  have hfour : (4 * dyadicScale j) ^ ((1 : ℝ) / 2) =
      2 * dyadicScale j ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hscale.le]
    have hfour' : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [← Real.sqrt_eq_rpow]
      exact
        (Real.sqrt_eq_iff_mul_self_eq_of_pos (x := (4 : ℝ))
          (by norm_num : 0 < (2 : ℝ))).mpr (by norm_num)
    rw [hfour']
  have hpow : ‖ξ‖ ^ ((1 : ℝ) / 2 - 1) =
      (‖ξ‖ ^ ((1 : ℝ) / 2))⁻¹ := by
    have hexp : (1 : ℝ) / 2 - 1 = -((1 : ℝ) / 2) := by ring
    rw [hexp]
    exact Real.rpow_neg (norm_nonneg ξ) _
  have hderiv_bound : ‖deriv (fun s : ℝ => surfaceFourier 2 (s • ξ)) r‖ ≤
      2 * C₁ * dyadicScale j ^ ((1 : ℝ) / 2) := by
    calc
      ‖deriv (fun s : ℝ => surfaceFourier 2 (s • ξ)) r‖ ≤
          C₁ / ‖ξ‖ ^ ((1 : ℝ) / 2 - 1) := hderiv ξ r hξone hr
      _ = C₁ * ‖ξ‖ ^ ((1 : ℝ) / 2) := by
        rw [hpow, div_eq_mul_inv, inv_inv]
      _ ≤ C₁ * (2 * dyadicScale j ^ ((1 : ℝ) / 2)) := by
        exact mul_le_mul_of_nonneg_left (hroot.trans_eq hfour) hC₁.le
      _ = 2 * C₁ * dyadicScale j ^ ((1 : ℝ) / 2) := by ring
  have hqnorm : ‖q‖ ≤ 2 := by
    dsimp only [q]
    exact norm_smooth_dyadic_bandpass_le_two hφnorm j ξ
  change ‖deriv (fun s : ℝ => surfaceFourier 2 (s • ξ)) r * q‖ ≤ _
  rw [norm_mul]
  calc
    ‖deriv (fun s : ℝ => surfaceFourier 2 (s • ξ)) r‖ * ‖q‖ ≤
        (2 * C₁ * dyadicScale j ^ ((1 : ℝ) / 2)) * 2 :=
      mul_le_mul hderiv_bound hqnorm (norm_nonneg _)
        (by positivity)
    _ = 4 * C₁ * dyadicScale j ^ ((1 : ℝ) / 2) := by ring

/-- The derivative-frequency estimate is likewise available from the bundled
circle interface. -/
theorem HasCircleSurfaceFourierSharpBounds.bandpass_derivative
    (hcircle : HasCircleSurfaceFourierSharpBounds)
    {φ : SchwartzMap (Euclidean 2) ℂ}
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (hφnorm : ∀ ξ, ‖φ ξ‖ ≤ 1)
    (j : ℕ) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (ξ : Euclidean 2) :
    ∃ C : ℝ, 0 < C ∧
      ‖deriv (fun s : ℝ => surfaceFourier 2 (s • ξ)) r *
        (φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ))‖ ≤
        C * dyadicScale j ^ ((1 : ℝ) / 2) := by
  rcases hcircle with ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩
  exact ⟨4 * C₁, mul_pos (by norm_num) hC₁,
    norm_deriv_circle_surfaceFourier_smul_mul_smooth_dyadic_bandpass_le_of_sharp
      C₁ hC₁ hderiv hφone hφzero hφnorm j r hr ξ⟩

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
