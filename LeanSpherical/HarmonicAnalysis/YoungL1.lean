/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The concrete `L¹` Young inequality

This is the direct Fubini proof for complex convolution on finite-dimensional
Euclidean space.  No continuity hypothesis is needed: integrability alone
gives both the integrability of the convolution and the estimate.
-/

open MeasureTheory
open scoped Convolution

noncomputable section

namespace LeanSpherical.HarmonicAnalysis

/-- The `L¹` norm of the convolution of two complex integrable functions on
finite-dimensional Euclidean space is bounded by the product of their `L¹`
norms. -/
theorem integral_norm_convolution_mul_le
    {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x : EuclideanSpace ℝ (Fin d), ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖) ≤
      (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖) *
        (∫ x : EuclideanSpace ℝ (Fin d), ‖g x‖) := by
  have hprod :
      Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        f p.2 * g (p.1 - p.2)) (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg
  have hprodNorm :
      Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖f p.2‖ * ‖g (p.1 - p.2)‖) (volume.prod volume) := by
    simpa only [norm_mul] using hprod.norm
  have hiter :
      Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        ∫ t : EuclideanSpace ℝ (Fin d), ‖f t‖ * ‖g (x - t)‖) volume :=
    hprodNorm.integral_prod_left
  have hconv :
      Integrable (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) volume :=
    hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  calc
    (∫ x : EuclideanSpace ℝ (Fin d), ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖) ≤
        ∫ x : EuclideanSpace ℝ (Fin d),
          ∫ t : EuclideanSpace ℝ (Fin d), ‖f t‖ * ‖g (x - t)‖ := by
      apply integral_mono hconv.norm hiter
      intro x
      change ‖∫ t : EuclideanSpace ℝ (Fin d), f t * g (x - t)‖ ≤ _
      simpa only [norm_mul] using
        (norm_integral_le_integral_norm
          (fun t : EuclideanSpace ℝ (Fin d) => f t * g (x - t)))
    _ = ∫ t : EuclideanSpace ℝ (Fin d),
        ∫ x : EuclideanSpace ℝ (Fin d), ‖f t‖ * ‖g (x - t)‖ := by
      exact integral_integral_swap hprodNorm
    _ = ∫ t : EuclideanSpace ℝ (Fin d), ‖f t‖ *
        ∫ x : EuclideanSpace ℝ (Fin d), ‖g x‖ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [integral_const_mul]
      rw [integral_sub_right_eq_self (μ := volume)
        (fun x : EuclideanSpace ℝ (Fin d) => ‖g x‖) t]
    _ = (∫ t : EuclideanSpace ℝ (Fin d), ‖f t‖) *
        (∫ x : EuclideanSpace ℝ (Fin d), ‖g x‖) := by
      rw [integral_mul_const]

/-- A bounded continuous function convolved with an even integrable kernel
has the expected pointwise `L∞` bound.  The evenness is exactly what lets the
literal convolution convention use translation invariance without a separate
reflection-invariance hypothesis on volume. -/
theorem norm_convolution_mul_le_bound_mul_integral_norm_of_even
    {d : Nat} (f g : EuclideanSpace ℝ (Fin d) → ℂ) (hf : Continuous f)
    {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C) (hg : Integrable g volume)
    (hgeven : ∀ y, g (-y) = g y)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x‖ ≤
      C * ∫ y : EuclideanSpace ℝ (Fin d), ‖g y‖ := by
  have hflip (y : EuclideanSpace ℝ (Fin d)) : g (x - y) = g (y - x) := by
    rw [show x - y = -(y - x) by abel, hgeven]
  have hgtranslate : Integrable (fun y : EuclideanSpace ℝ (Fin d) => g (x - y)) volume := by
    refine (hg.comp_sub_right x).congr (Filter.Eventually.of_forall ?_)
    intro y
    exact (hflip y).symm
  have hmajor : Integrable
      (fun y : EuclideanSpace ℝ (Fin d) => C * ‖g (x - y)‖) volume :=
    hgtranslate.norm.const_mul C
  have hmeas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin d) => f y * g (x - y)) volume :=
    hf.aestronglyMeasurable.mul hgtranslate.aestronglyMeasurable
  have hprod : Integrable
      (fun y : EuclideanSpace ℝ (Fin d) => f y * g (x - y)) volume := by
    refine hmajor.mono' hmeas (Filter.Eventually.of_forall ?_)
    intro y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg _)
  change ‖∫ y : EuclideanSpace ℝ (Fin d), f y * g (x - y)‖ ≤ _
  calc
    ‖∫ y : EuclideanSpace ℝ (Fin d), f y * g (x - y)‖ ≤
        ∫ y : EuclideanSpace ℝ (Fin d), ‖f y * g (x - y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : EuclideanSpace ℝ (Fin d), C * ‖g (x - y)‖ := by
      apply integral_mono hprod.norm hmajor
      intro y
      change ‖f y * g (x - y)‖ ≤ C * ‖g (x - y)‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg _)
    _ = C * ∫ y : EuclideanSpace ℝ (Fin d), ‖g y‖ := by
      rw [show (∫ y : EuclideanSpace ℝ (Fin d), C * ‖g (x - y)‖) =
          ∫ y : EuclideanSpace ℝ (Fin d), C * ‖g (y - x)‖ by
            apply integral_congr_ae
            filter_upwards with y
            rw [hflip]]
      rw [integral_const_mul]
      congr 1
      exact integral_sub_right_eq_self (μ := volume)
        (fun y : EuclideanSpace ℝ (Fin d) => ‖g y‖) x

/-- An integrable kernel convolved with a bounded continuous function has the
direct pointwise `L∞` bound.  This is the orientation used by the physical
realization of a smooth Fourier multiplier. -/
theorem norm_convolution_mul_le_integral_norm_mul_bound
    {d : Nat} (k f : EuclideanSpace ℝ (Fin d) → ℂ) (hk : Integrable k volume)
    (hf : Continuous f) {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖(k ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f) x‖ ≤
      (∫ y : EuclideanSpace ℝ (Fin d), ‖k y‖) * C := by
  have hshift : Continuous (fun y : EuclideanSpace ℝ (Fin d) => f (x - y)) :=
    hf.comp ((continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin d) => x).sub
      continuous_id)
  have hmajor : Integrable
      (fun y : EuclideanSpace ℝ (Fin d) => ‖k y‖ * C) volume :=
    hk.norm.mul_const C
  have hmeas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin d) => k y * f (x - y)) volume :=
    hk.aestronglyMeasurable.mul hshift.aestronglyMeasurable
  have hprod : Integrable
      (fun y : EuclideanSpace ℝ (Fin d) => k y * f (x - y)) volume := by
    refine hmajor.mono' hmeas (Filter.Eventually.of_forall ?_)
    intro y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
  change ‖∫ y : EuclideanSpace ℝ (Fin d), k y * f (x - y)‖ ≤ _
  calc
    ‖∫ y : EuclideanSpace ℝ (Fin d), k y * f (x - y)‖ ≤
        ∫ y : EuclideanSpace ℝ (Fin d), ‖k y * f (x - y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : EuclideanSpace ℝ (Fin d), ‖k y‖ * C := by
      apply integral_mono hprod.norm hmajor
      intro y
      change ‖k y * f (x - y)‖ ≤ ‖k y‖ * C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    _ = (∫ y : EuclideanSpace ℝ (Fin d), ‖k y‖) * C := by
      rw [integral_mul_const]

end LeanSpherical.HarmonicAnalysis
