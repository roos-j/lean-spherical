/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceFoundation
import LeanSpherical.HarmonicAnalysis.RadiusSobolev
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Radial derivatives of the Fourier transform of surface measure

This file records the elementary, non-oscillatory part of the radial
calculation.  The sharp decay of the resulting integral is a separate
stationary-phase issue.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- The elementary first-moment bound for the phase on the unit sphere. -/
theorem norm_surfacePhase_le (d : ℕ) (ξ : Euclidean d)
    (ω : sphere (0 : Euclidean d) 1) :
    ‖surfacePhase d ξ ω‖ ≤ 2 * Real.pi * ‖ξ‖ := by
  have hω : ‖(ω : Euclidean d)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  rw [surfacePhase, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one]
  calc
    |(-2 : ℝ) * Real.pi * inner ℝ (ω : Euclidean d) ξ| =
        (2 * Real.pi) * |inner ℝ (ω : Euclidean d) ξ| := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg Real.pi_pos.le]
      ring
    _ ≤ (2 * Real.pi) * (‖(ω : Euclidean d)‖ * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
    _ = 2 * Real.pi * ‖ξ‖ := by rw [hω]; ring

theorem hasDerivAt_surfaceFourier_radial (d : ℕ) (ξ : Euclidean d) :
    HasDerivAt (fun r : ℝ => surfaceFourier d (r • ξ))
      (∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d ξ ω) * surfacePhase d ξ ω
          ∂unitSurfaceMeasure d) 1 := by
  change HasDerivAt
    (fun r : ℝ => ∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d (r • ξ) ω) ∂unitSurfaceMeasure d)
    (∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d ξ ω) * surfacePhase d ξ ω ∂unitSurfaceMeasure d) 1
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := unitSurfaceMeasure d) (s := Set.univ) (x₀ := (1 : ℝ))
    (bound := fun _ : sphere (0 : Euclidean d) 1 => 2 * Real.pi * ‖ξ‖)
    (F := fun r ω => Complex.exp (surfacePhase d (r • ξ) ω))
    (F' := fun r ω =>
      Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω)
    Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [one_smul] using h.2
  · filter_upwards [] with r
    exact (by
      unfold surfacePhase
      fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
        Complex.exp (surfacePhase d (r • ξ) ω))).aestronglyMeasurable
  · apply Integrable.of_bound
    · exact (by
      unfold surfacePhase
      fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
          Complex.exp (surfacePhase d ((1 : ℝ) • ξ) ω))).aestronglyMeasurable
    · filter_upwards with ω
      exact (norm_surfaceFourier_kernel d (1 • ξ) ω).le
  · exact (by
      unfold surfacePhase
      fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
        Complex.exp (surfacePhase d ((1 : ℝ) • ξ) ω) *
          surfacePhase d ξ ω)).aestronglyMeasurable
  · filter_upwards with ω
    intro r hr
    rw [norm_mul, norm_surfaceFourier_kernel]
    simpa using norm_surfacePhase_le d ξ ω
  · exact integrable_const _
  · filter_upwards with ω
    intro r hr
    have hlin : HasDerivAt (fun x : ℝ => (x : ℂ) * surfacePhase d ξ ω)
        (surfacePhase d ξ ω) r :=
      (hasDerivAt_mul_const (surfacePhase d ξ ω) :
        HasDerivAt (fun z : ℂ => z * surfacePhase d ξ ω)
          (surfacePhase d ξ ω) (r : ℂ)).comp_ofReal
    simpa only [surfacePhase_smul] using hlin.cexp

/-- The same dominated differentiation argument works at every radius.  This
is the radius-dependent derivative used before taking a supremum over a
compact radius interval. -/
theorem hasDerivAt_surfaceFourier_radial_at (d : ℕ) (ξ : Euclidean d) (r₀ : ℝ) :
    HasDerivAt (fun r : ℝ => surfaceFourier d (r • ξ))
      (∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d (r₀ • ξ) ω) * surfacePhase d ξ ω
          ∂unitSurfaceMeasure d) r₀ := by
  change HasDerivAt
    (fun r : ℝ => ∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d (r • ξ) ω) ∂unitSurfaceMeasure d)
    (∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d (r₀ • ξ) ω) * surfacePhase d ξ ω
        ∂unitSurfaceMeasure d) r₀
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := unitSurfaceMeasure d) (s := Set.univ) (x₀ := r₀)
    (bound := fun _ : sphere (0 : Euclidean d) 1 => 2 * Real.pi * ‖ξ‖)
    (F := fun r ω => Complex.exp (surfacePhase d (r • ξ) ω))
    (F' := fun r ω =>
      Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω)
    Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact h.2
  · filter_upwards [] with r
    exact (by
      unfold surfacePhase
      fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
        Complex.exp (surfacePhase d (r • ξ) ω))).aestronglyMeasurable
  · apply Integrable.of_bound
    · exact (by
        unfold surfacePhase
        fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
          Complex.exp (surfacePhase d (r₀ • ξ) ω))).aestronglyMeasurable
    · filter_upwards with ω
      exact (norm_surfaceFourier_kernel d (r₀ • ξ) ω).le
  · exact (by
      unfold surfacePhase
      fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
        Complex.exp (surfacePhase d (r₀ • ξ) ω) *
          surfacePhase d ξ ω)).aestronglyMeasurable
  · filter_upwards with ω
    intro r hr
    rw [norm_mul, norm_surfaceFourier_kernel]
    simpa using norm_surfacePhase_le d ξ ω
  · exact integrable_const _
  · filter_upwards with ω
    intro r hr
    have hlin : HasDerivAt (fun x : ℝ => (x : ℂ) * surfacePhase d ξ ω)
        (surfacePhase d ξ ω) r :=
      (hasDerivAt_mul_const (surfacePhase d ξ ω) :
        HasDerivAt (fun z : ℂ => z * surfacePhase d ξ ω)
          (surfacePhase d ξ ω) (r : ℂ)).comp_ofReal
    simpa only [surfacePhase_smul] using hlin.cexp

/-- Differentiating after absorbing a nonzero radial scale into the frequency
variable gives the corresponding scalar factor. -/
theorem deriv_surfaceFourier_radial_rescale (d : ℕ) (ξ : Euclidean d) (r : ℝ) :
    deriv (fun t : ℝ => surfaceFourier d (t • (r • ξ))) 1 =
      r • deriv (fun s : ℝ => surfaceFourier d (s • ξ)) r := by
  have hlin : HasDerivAt (fun t : ℝ => t * r) r 1 := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id (1 : ℝ)).mul_const r
  have houter : HasDerivAt (fun s : ℝ => surfaceFourier d (s • ξ))
      (∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω
          ∂unitSurfaceMeasure d) (1 * r) := by
    simpa only [one_mul] using hasDerivAt_surfaceFourier_radial_at d ξ r
  have hcomp := HasDerivAt.scomp 1 houter hlin
  calc
    deriv (fun t : ℝ => surfaceFourier d (t • (r • ξ))) 1 =
        r • (∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω
            ∂unitSurfaceMeasure d) := by
      rw [show (fun t : ℝ => surfaceFourier d (t • (r • ξ))) =
          ((fun s : ℝ => surfaceFourier d (s • ξ)) ∘ fun t => t * r) by
            funext t
            rw [Function.comp_apply, smul_smul]]
      exact hcomp.deriv
    _ = r • deriv (fun s : ℝ => surfaceFourier d (s • ξ)) r := by
      rw [(hasDerivAt_surfaceFourier_radial_at d ξ r).deriv]

/-- The radial derivative has a uniform elementary bound at every radius.
Sharp decay of this derivative still requires stationary phase. -/
theorem norm_deriv_surfaceFourier_radial_le (d : ℕ) (ξ : Euclidean d) (r : ℝ) :
    ‖deriv (fun s : ℝ => surfaceFourier d (s • ξ)) r‖ ≤
      (2 * Real.pi * ‖ξ‖) * (unitSurfaceMeasure d).real univ := by
  rw [(hasDerivAt_surfaceFourier_radial_at d ξ r).deriv]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with ω
  rw [norm_mul, norm_surfaceFourier_kernel]
  simpa using norm_surfacePhase_le d ξ ω

/-- The integral formula for the radial derivative depends continuously on
the radius. -/
theorem continuous_surfaceFourier_radial_derivative_integral
    (d : ℕ) (ξ : Euclidean d) :
    Continuous (fun r : ℝ => ∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω
        ∂unitSurfaceMeasure d) := by
  have hcont : Continuous (Function.uncurry
      (fun (r : ℝ) (ω : sphere (0 : Euclidean d) 1) =>
        Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω)) := by
    unfold surfacePhase
    fun_prop
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (μ := unitSurfaceMeasure d) hcont isCompact_univ)

/-- Before using oscillation, the radial Fourier transform is already
Lipschitz, with the elementary first-moment constant. -/
theorem norm_surfaceFourier_radial_sub_le
    (d : ℕ) (ξ : Euclidean d) (r s : ℝ) :
    ‖surfaceFourier d (r • ξ) - surfaceFourier d (s • ξ)‖ ≤
      (2 * Real.pi * ‖ξ‖) * (unitSurfaceMeasure d).real univ * |r - s| := by
  have hdiff : ∀ t ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (fun u : ℝ => surfaceFourier d (u • ξ)) t :=
    fun t _ => (hasDerivAt_surfaceFourier_radial_at d ξ t).differentiableAt
  have hbound : ∀ t ∈ (Set.univ : Set ℝ),
      ‖deriv (fun u : ℝ => surfaceFourier d (u • ξ)) t‖ ≤
        (2 * Real.pi * ‖ξ‖) * (unitSurfaceMeasure d).real univ :=
    fun t _ => norm_deriv_surfaceFourier_radial_le d ξ t
  simpa [Real.norm_eq_abs] using
    (Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound convex_univ
      (Set.mem_univ s) (Set.mem_univ r))

/-- The one-dimensional Sobolev step applied directly to the concrete radial
surface multiplier.  The remaining analytic task is to add oscillatory decay
to both terms on the right. -/
theorem norm_sq_surfaceFourier_radial_le_radiusSobolev
    (d : ℕ) (ξ : Euclidean d) {a b r : ℝ} (hr : r ∈ Set.Icc a b) :
    ‖surfaceFourier d (r • ξ)‖ ^ 2 ≤
      2 * ‖surfaceFourier d (a • ξ)‖ ^ 2 +
        2 * (b - a) *
          ∫ t in a..b, ‖∫ ω : sphere (0 : Euclidean d) 1,
            Complex.exp (surfacePhase d (t • ξ) ω) * surfacePhase d ξ ω
              ∂unitSurfaceMeasure d‖ ^ 2 := by
  exact
    norm_sq_le_two_mul_norm_sq_add_two_mul_length_mul_intervalIntegral_norm_sq_of_hasDerivAt
      hr (continuous_surfaceFourier_radial_derivative_integral d ξ)
      (fun t => hasDerivAt_surfaceFourier_radial_at d ξ t)

end

end LeanSpherical.HarmonicAnalysis
