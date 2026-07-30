/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.SharpnessTests

/-!
# Nonnegative smooth ball data for the annulus test

The annulus obstruction needs the small smooth ball test with its positivity
visible in the statement, rather than merely its absolute-value bound.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Metric Set

noncomputable section

/-- A compactly supported smooth ball cutoff may be chosen real-valued,
nonnegative, and bounded by one. -/
theorem exists_schwartz_ball_test_nonnegative_bounded
    (d : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ f : SchwartzMap (Euclidean d) ℂ,
      (∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1) ∧
      (∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0) ∧
      (∀ y : Euclidean d, 0 ≤ (f y).re) ∧
      (∀ y : Euclidean d, (f y).im = 0) ∧
      (∀ y : Euclidean d, ‖f y‖ ≤ 1) := by
  let b : ContDiffBump (0 : Euclidean d) := ⟨R, 2 * R, hR, by linarith⟩
  let g : Euclidean d → ℂ := Complex.ofRealCLM ∘ b
  have hcompact : HasCompactSupport g := by
    exact b.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    change (b y : ℂ) = 1
    have hmem : y ∈ closedBall (0 : Euclidean d) b.rIn := by
      simpa only [mem_closedBall, dist_zero_right] using hy
    rw [b.one_of_mem_closedBall hmem]
    norm_num
  · intro y hy
    change (b y : ℂ) = 0
    have hdist : b.rOut ≤ dist y (0 : Euclidean d) := by
      simpa only [dist_zero_right] using hy
    rw [b.zero_of_le_dist hdist]
    norm_num
  · intro y
    change 0 ≤ b y
    exact ContDiffBump.nonneg' b y
  · intro y
    change (b y : ℂ).im = 0
    simp
  · intro y
    change ‖(b y : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (ContDiffBump.nonneg' b y)]
    exact ContDiffBump.le_one b

end

/-- A nonnegative smooth ball cutoff has at least the mass of the ball on
which it is identically one. -/
theorem volume_ball_toReal_le_integral_re_of_eq_one_nonneg
    {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ) {R : ℝ}
    (hOne : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re) :
    (volume (ball (0 : Euclidean d) R)).toReal ≤
      ∫ y : Euclidean d, (f y).re := by
  let g : Euclidean d → ℝ :=
    (ball (0 : Euclidean d) R).indicator fun _ => (1 : ℝ)
  have hball_top : volume (ball (0 : Euclidean d) R) ≠ (⊤ : ENNReal) :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := R)).ne
  have hg_integrable : Integrable g volume := by
    dsimp [g]
    rw [integrable_indicator_iff isOpen_ball.measurableSet]
    exact integrableOn_const hball_top
  have hpoint : ∀ y : Euclidean d, g y ≤ (f y).re := by
    intro y
    dsimp [g]
    by_cases hy : y ∈ ball (0 : Euclidean d) R
    · rw [Set.indicator_of_mem hy]
      have hynorm : ‖y‖ ≤ R := by
        have : ‖y‖ < R := by
          simpa only [mem_ball, dist_zero_right] using hy
        exact this.le
      rw [hOne y hynorm]
      norm_num
    · rw [Set.indicator_of_notMem hy]
      exact hnonneg y
  calc
    (volume (ball (0 : Euclidean d) R)).toReal = ∫ y : Euclidean d, g y := by
      dsimp [g]
      rw [integral_indicator isOpen_ball.measurableSet, integral_const,
        Measure.real_def, Measure.restrict_apply_univ]
      simp
    _ ≤ ∫ y : Euclidean d, (f y).re :=
      integral_mono hg_integrable f.integrable.re hpoint

end LeanSpherical.HarmonicAnalysis.FractalDilations
