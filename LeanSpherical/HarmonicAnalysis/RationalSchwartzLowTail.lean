/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.RationalLowTailIntegration
import LeanSpherical.HarmonicAnalysis.SchwartzRationalSplit

/-!
# Schwartz rational low tail

Specialization of the generic rational low-tail estimate to Schwartz input.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Set ENNReal

noncomputable section

/-- The Schwartz-valued rational low-amplitude split has the precise weighted
`L²` tail required by the split Marcinkiewicz argument. -/
theorem rational_schwartz_low_weighted_tail
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    (low high : ℝ → SchwartzMap (Euclidean d) ℂ)
    (hlow : ∀ t x, low t x =
      ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x)
    (hhigh : ∀ t, high t = f - low t)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ))) *
        (ENNReal.ofReal t) ^ (p - 3)) ≤
      ((ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹ +
          (ENNReal.ofReal (2 - p))⁻¹) *
        ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p) := by
  apply weighted_low_tail_le_of_two_region_bounds
    (u := fun x : Euclidean d => ‖f x‖)
    (low := fun t x => low t x)
    f.continuous.norm.measurable (fun x => norm_nonneg _)
  · intro t x ht htx
    apply ENNReal.ofReal_le_ofReal
    have h := (rational_low_high_pointwise_tail_bounds f (low t) (high t)
      ht (hlow t) (hhigh t) x).1
    simpa [htx] using h
  · intro t x ht htx
    apply ENNReal.ofReal_le_ofReal
    have h := (rational_low_high_pointwise_tail_bounds f (low t) (high t)
      ht (hlow t) (hhigh t) x).1
    have hnot : ¬ t ≤ ‖f x‖ := not_le_of_gt htx
    simpa [hnot] using h
  · exact hp1
  · exact hp2

end

end LeanSpherical.HarmonicAnalysis
