/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Summing geometrically decaying dyadic `Lᵖ` pieces

The theorem below is the literal finite partial-sum step used after obtaining
geometrically decaying `Lᵖ` bounds for dyadic pieces.  It combines Minkowski's
inequality with the geometric-series identity in `ℝ≥0∞`; it does not assume an
operator interface or claim convergence of a function series.
-/

open MeasureTheory ENNReal

noncomputable section

namespace LeanSpherical.HarmonicAnalysis

/-- If the `Lᵖ` norm of the `n`th piece is at most `C * ρ^n`, then every
finite dyadic partial sum has `Lᵖ` norm at most `C / (1 - ρ)`. -/
theorem eLpNorm_sum_range_le_geometric
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (p : ℝ≥0∞) (hp : 1 ≤ p) (f : ℕ → α → E)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (C ρ : ℝ≥0∞)
    (hpiece : ∀ n, eLpNorm (f n) p μ ≤ C * ρ ^ n) (N : ℕ) :
    eLpNorm (fun x => ∑ n ∈ Finset.range N, f n x) p μ ≤ C * (1 - ρ)⁻¹ := by
  calc
    eLpNorm (fun x => ∑ n ∈ Finset.range N, f n x) p μ
        = eLpNorm (∑ n ∈ Finset.range N, f n) p μ := by
          apply eLpNorm_congr_ae
          filter_upwards with x
          simp
    _ ≤ ∑ n ∈ Finset.range N, eLpNorm (f n) p μ :=
      eLpNorm_sum_le (f := f) (s := Finset.range N) (fun n _ => hf n) hp
    _ ≤ ∑ n ∈ Finset.range N, C * ρ ^ n := by
      exact Finset.sum_le_sum fun n _ => hpiece n
    _ = C * ∑ n ∈ Finset.range N, ρ ^ n := by
      rw [Finset.mul_sum]
    _ ≤ C * ∑' n : ℕ, ρ ^ n := by
      exact mul_le_mul_right (ENNReal.sum_le_tsum (Finset.range N)) C
    _ = C * (1 - ρ)⁻¹ := congrArg (C * ·) (ENNReal.tsum_geometric ρ)

end LeanSpherical.HarmonicAnalysis
