/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# A smooth compactly supported frequency cutoff

This file records the standard cutoff used before a frequency decomposition:
a complex-valued Schwartz function which is one on the unit ball and vanishes
outside the ball of radius two.  It is obtained directly from Mathlib's
`ContDiffBump`, so no choice of an auxiliary cutoff is exposed in the API.
-/

namespace LeanSpherical.HarmonicAnalysis

open scoped ContDiff

noncomputable section

/-- There is a complex-valued Schwartz cutoff which equals one on the unit
ball and vanishes outside the ball of radius two. -/
theorem exists_schwartz_frequency_cutoff (d : Nat) :
    ∃ φ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1) ∧
      (∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) := by
  let f : ContDiffBump (0 : Euclidean d) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let g : Euclidean d → ℂ := Complex.ofRealCLM ∘ f
  have hcompact : HasCompactSupport g := by
    exact f.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff ℝ ∞ g := by
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_⟩
  · intro ξ hξ
    change (f ξ : ℂ) = 1
    have hmem : ξ ∈ Metric.closedBall (0 : Euclidean d) f.rIn := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hξ
    rw [f.one_of_mem_closedBall hmem]
    norm_num
  · intro ξ hξ
    change (f ξ : ℂ) = 0
    have hdist : f.rOut ≤ dist ξ (0 : Euclidean d) := by
      simpa only [dist_zero_right] using hξ
    rw [f.zero_of_le_dist hdist]
    norm_num

/-- The cutoff can be chosen with pointwise norm at most one. -/
theorem exists_schwartz_frequency_cutoff_norm_le_one (d : Nat) :
    ∃ φ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1) ∧
      (∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) ∧
      (∀ ξ, ‖φ ξ‖ ≤ 1) := by
  let f : ContDiffBump (0 : Euclidean d) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let g : Euclidean d → ℂ := Complex.ofRealCLM ∘ f
  have hcompact : HasCompactSupport g := by
    exact f.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff ℝ ∞ g := by
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_, ?_⟩
  · intro ξ hξ
    change (f ξ : ℂ) = 1
    have hmem : ξ ∈ Metric.closedBall (0 : Euclidean d) f.rIn := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hξ
    rw [f.one_of_mem_closedBall hmem]
    norm_num
  · intro ξ hξ
    change (f ξ : ℂ) = 0
    have hdist : f.rOut ≤ dist ξ (0 : Euclidean d) := by
      simpa only [dist_zero_right] using hξ
    rw [f.zero_of_le_dist hdist]
    norm_num
  · intro ξ
    change ‖(f ξ : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg f.nonneg]
    exact f.le_one

/-- The concrete bump cutoff is even as well as bounded by one. -/
theorem exists_even_schwartz_frequency_cutoff_norm_le_one (d : Nat) :
    ∃ φ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1) ∧
      (∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) ∧
      (∀ ξ, ‖φ ξ‖ ≤ 1) ∧
      (∀ ξ, φ (-ξ) = φ ξ) := by
  let f : ContDiffBump (0 : Euclidean d) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let g : Euclidean d → ℂ := Complex.ofRealCLM ∘ f
  have hcompact : HasCompactSupport g := by
    exact f.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff ℝ ∞ g := by
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ
    change (f ξ : ℂ) = 1
    have hmem : ξ ∈ Metric.closedBall (0 : Euclidean d) f.rIn := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hξ
    rw [f.one_of_mem_closedBall hmem]
    norm_num
  · intro ξ hξ
    change (f ξ : ℂ) = 0
    have hdist : f.rOut ≤ dist ξ (0 : Euclidean d) := by
      simpa only [dist_zero_right] using hξ
    rw [f.zero_of_le_dist hdist]
    norm_num
  · intro ξ
    change ‖(f ξ : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg f.nonneg]
    exact f.le_one
  · intro ξ
    change (f (-ξ) : ℂ) = f ξ
    rw [f.neg]

/-- The cutoff may moreover be chosen even.  Symmetrizing the concrete
cutoff preserves both of its radial support properties. -/
theorem exists_even_schwartz_frequency_cutoff (d : Nat) :
    ∃ φ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1) ∧
      (∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) ∧
      (∀ ξ, φ (-ξ) = φ ξ) := by
  rcases exists_schwartz_frequency_cutoff d with ⟨φ, hφone, hφzero⟩
  let ψ : SchwartzMap (Euclidean d) ℂ :=
    (2 : ℂ)⁻¹ • (φ +
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        ((LinearIsometryEquiv.neg ℝ : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) :
          Euclidean d ≃L[ℝ] Euclidean d)) φ)
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro ξ hξ
    change (2 : ℂ)⁻¹ * (φ ξ + φ (-ξ)) = 1
    rw [hφone ξ hξ, hφone (-ξ)]
    · norm_num
    · simpa using hξ
  · intro ξ hξ
    change (2 : ℂ)⁻¹ * (φ ξ + φ (-ξ)) = 0
    rw [hφzero ξ hξ, hφzero (-ξ)]
    · norm_num
    · simpa using hξ
  · intro ξ
    change (2 : ℂ)⁻¹ * (φ (-ξ) + φ (-(-ξ))) =
      (2 : ℂ)⁻¹ * (φ ξ + φ (-ξ))
    rw [neg_neg]
    ring

end

end LeanSpherical.HarmonicAnalysis
