/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.ExponentRegions

/-!
# What a gap-independent `TT*` estimate can prove near `Q4`

The `Q4` argument has two shell parameters.  If the `L¹ → L∞` estimate for a
radius-gap shell has a gain `2 ^ (-a * n)`, while its `L² → L²` estimate loses
`2 ^ (γ * n)`, interpolation has shell exponent
`θ * γ - (1 - θ) * a`.  The stationary-phase estimate in the paper supplies
`a = (d - 1) / 2`.

This file records the elementary algebra behind that fact, and the comparison
with the bound obtained when the kernel estimate has no gap gain (`a = 0`).
It deliberately contains no analytic assertion: it is a reusable guardrail
for the analytic `TT*` layer.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Set

noncomputable section

/-- The exponent of a radius-gap shell after ordinary interpolation, where
`θ` is the weight of the `L² → L²` bound. -/
def q4ShellInterpolationExponent (a γ θ : ℝ) : ℝ :=
  θ * γ - (1 - θ) * a

/-- With no gap gain at the `L¹ → L∞` endpoint, the shell exponent is simply
the nonnegative `L²` counting loss. -/
theorem q4ShellInterpolationExponent_no_gap (γ θ : ℝ) :
    q4ShellInterpolationExponent 0 γ θ = θ * γ := by
  simp [q4ShellInterpolationExponent]

/-- Thus a gap-independent kernel bound cannot make an individual shell
decay under interpolation. -/
theorem q4ShellInterpolationExponent_no_gap_nonneg
    {γ θ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) :
    0 ≤ q4ShellInterpolationExponent 0 γ θ := by
  rw [q4ShellInterpolationExponent_no_gap]
  exact mul_nonneg hθ hγ

/-- In the genuinely fractal case `γ > 0`, zero shell exponent without a gap
gain forces the interpolation parameter to be the `L¹ → L∞` endpoint. -/
theorem q4ShellInterpolationExponent_no_gap_eq_zero_iff
    {γ θ : ℝ} (hγ : 0 < γ) :
    q4ShellInterpolationExponent 0 γ θ = 0 ↔ θ = 0 := by
  rw [q4ShellInterpolationExponent_no_gap]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hθ | hγzero
    · exact hθ
    · exact False.elim (hγ.ne' hγzero)
  · rintro rfl
    ring

/-- The unique formal balance for a positive gap gain `a` and a counting loss
`γ` is obtained by giving the `L²` estimate weight `a / (a + γ)`. -/
theorem q4ShellInterpolationExponent_balanced
    {a γ : ℝ} (h : a + γ ≠ 0) :
    q4ShellInterpolationExponent a γ (a / (a + γ)) = 0 := by
  dsimp [q4ShellInterpolationExponent]
  field_simp [h]
  ring

/-- The off-diagonal point obtained by using only the global cardinality loss
`2 ^ (j * β)` and a gap-independent pair-kernel bound.  It is the `L²` input
point of the corresponding ordinary `TT*` interpolation. -/
def crudeGapIndependentTTStarPoint (d : ℕ) (β : ℝ) : ExponentPoint :=
  (1 / 2, 1 / (2 * ((d : ℝ) - β)))

/-- The interpolation point above lies exactly on the `Q1`--`Q3(β)` ray. -/
theorem crudeGapIndependentTTStarPoint_on_minkowski_diagonal
    {d : ℕ} {β : ℝ} (hden : (d : ℝ) - β ≠ 0) :
    ((d : ℝ) - β) * (crudeGapIndependentTTStarPoint d β).2 =
      (crudeGapIndependentTTStarPoint d β).1 := by
  dsimp [crudeGapIndependentTTStarPoint]
  field_simp [hden]

/-- The barycentric parameter placing the crude point on the `Q1`--`Q3(β)`
segment. -/
def crudeGapIndependentTTStarWeight (d : ℕ) (β : ℝ) : ℝ :=
  ((d : ℝ) - β + 1) / (2 * ((d : ℝ) - β))

theorem crudeGapIndependentTTStarWeight_mem_unitInterval
    {d : ℕ} {β : ℝ} (hd : 2 ≤ d) (hβ : β ≤ 1) :
    crudeGapIndependentTTStarWeight d β ∈ Icc (0 : ℝ) 1 := by
  change ((d : ℝ) - β + 1) / (2 * ((d : ℝ) - β)) ∈ Icc (0 : ℝ) 1
  have hD : (1 : ℝ) ≤ (d : ℝ) - β := by
    have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hDpos : 0 < (d : ℝ) - β := lt_of_lt_of_le zero_lt_one hD
  constructor
  · apply div_nonneg
    · linarith
    · positivity
  · rw [div_le_one (by positivity)]
    linarith

/-- The crude interpolation point is a literal convex combination of `Q1`
and `Q3(β)`. -/
theorem crudeGapIndependentTTStarPoint_eq_lineMap_Q1_Q3
    {d : ℕ} {β : ℝ} (hden : (d : ℝ) - β ≠ 0)
    (hQ3den : (d : ℝ) - β + 1 ≠ 0) :
    crudeGapIndependentTTStarPoint d β =
      AffineMap.lineMap Q1 (Q3 d β) (crudeGapIndependentTTStarWeight d β) := by
  rw [AffineMap.lineMap_apply_module]
  ext <;> dsimp [crudeGapIndependentTTStarPoint,
    crudeGapIndependentTTStarWeight, Q1, Q3]
  all_goals field_simp [hden, hQ3den]
  all_goals ring

/-- Consequently the crude point belongs to the old Minkowski triangle.  This
is the precise geometry recovered by a gap-independent pair-kernel estimate. -/
theorem crudeGapIndependentTTStarPoint_mem_minkowski_vertex_hull
    {d : ℕ} {β : ℝ} (hd : 2 ≤ d) (hβ : β ≤ 1) :
    crudeGapIndependentTTStarPoint d β ∈
      convexHull ℝ {Q1, Q2 d β, Q3 d β} := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - β := by
    have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hden : (d : ℝ) - β ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hD)
  have hQ3den : (d : ℝ) - β + 1 ≠ 0 := by linarith
  rw [crudeGapIndependentTTStarPoint_eq_lineMap_Q1_Q3 hden hQ3den]
  have hsegment :
      AffineMap.lineMap Q1 (Q3 d β) (crudeGapIndependentTTStarWeight d β) ∈
        segment ℝ Q1 (Q3 d β) :=
    lineMap_mem_segment ℝ Q1 (Q3 d β)
      (crudeGapIndependentTTStarWeight_mem_unitInterval hd hβ)
  exact (convex_convexHull ℝ {Q1, Q2 d β, Q3 d β}).segment_subset
    (subset_convexHull ℝ _ (by simp))
    (subset_convexHull ℝ _ (by simp)) hsegment

/-- For `β > 0`, `Q4(γ)` lies strictly on the other side of the
`Q1`--`Q3(β)` diagonal.  Hence the crude estimate cannot reach the new part
of the `Q4` region by ordinary convex interpolation. -/
theorem Q4_strictly_beyond_minkowski_diagonal
    {d : ℕ} {β γ : ℝ} (hd : 2 ≤ d) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    ((d : ℝ) - β) * (Q4 d γ).2 < (Q4 d γ).1 := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) ^ 2 + 2 * γ - 1 := by
    nlinarith [sq_nonneg ((d : ℝ) - 2)]
  have hnum : 0 < β * ((d : ℝ) - 1) := by
    apply mul_pos hβ
    linarith
  have hidentity :
      (Q4 d γ).1 - ((d : ℝ) - β) * (Q4 d γ).2 =
        (β * ((d : ℝ) - 1)) / ((d : ℝ) ^ 2 + 2 * γ - 1) := by
    dsimp [Q4]
    field_simp [hden.ne']
    ring
  have hdiff : 0 < (Q4 d γ).1 - ((d : ℝ) - β) * (Q4 d γ).2 := by
    rw [hidentity]
    exact div_pos hnum hden
  linarith

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
