/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.EntropyDilation

/-!
# Euclidean control in a normalized multiplicative window

Only the elementary logarithm-to-Euclidean estimate used by the two lower
tests lives here.  It lets the cap geometry use the multiplicative diameter
directly after normalizing the window centre to one.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set
open scoped NNReal

noncomputable section

/-- In the unit-centred logarithmic interval of diameter at most one, the
ordinary distance from one is bounded by the multiplicative diameter. -/
theorem abs_sub_one_le_diam_of_mem_multiplicativeInterval_one
    {r : ℝ} {diam : ℝ≥0} (hdiam : diam ≤ 1)
    (hr : r ∈ multiplicativeInterval ⟨1, by simp⟩ diam) :
    |r - 1| ≤ (diam : ℝ) := by
  rcases hr with ⟨hrpos, hrlog⟩
  have hlogtwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogtwo_le : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : |Real.log r / Real.log 2| ≤ (diam : ℝ) / 2 := by
    simpa only [logRadius, Real.log_one, zero_div, sub_zero] using hrlog
  have hrewrite : Real.log r = Real.log 2 * (Real.log r / Real.log 2) := by
    field_simp [hlogtwo.ne']
  have hlogbound : |Real.log r| ≤ (diam : ℝ) / 2 := by
    rw [hrewrite, abs_mul, abs_of_pos hlogtwo]
    calc
      Real.log 2 * |Real.log r / Real.log 2| ≤ 1 * ((diam : ℝ) / 2) := by
        gcongr
      _ = (diam : ℝ) / 2 := by ring
  have hdiamreal : (diam : ℝ) ≤ 1 := by exact_mod_cast hdiam
  have hsmall : |Real.log r| ≤ 1 := hlogbound.trans (by nlinarith)
  calc
    |r - 1| = |Real.exp (Real.log r) - 1| := by rw [Real.exp_log hrpos]
    _ ≤ 2 * |Real.log r| := Real.abs_exp_sub_one_le hsmall
    _ ≤ (diam : ℝ) := by nlinarith

/-- The same normalized multiplicative window is contained in the ordinary
interval `[0, 2]`. -/
theorem le_two_of_mem_multiplicativeInterval_one
    {r : ℝ} {diam : ℝ≥0} (hdiam : diam ≤ 1)
    (hr : r ∈ multiplicativeInterval ⟨1, by simp⟩ diam) :
    r ≤ 2 := by
  have h := abs_sub_one_le_diam_of_mem_multiplicativeInterval_one hdiam hr
  have hdiamreal : (diam : ℝ) ≤ 1 := by exact_mod_cast hdiam
  nlinarith [le_abs_self (r - 1)]

end

end LeanSpherical.HarmonicAnalysis
