/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.FiniteCentralShellReassembly

/-!
# Dyadic output shells for thin-radial tails

The moving-window tail estimates are stated on the closed annulus between
`s / 4` and `s / 2`.  A half-open dyadic spatial shell at the corresponding
scale lies in that annulus.  This is the literal spatial bridge used when
the finite central-ball shell decomposition is combined with those tails.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- At spatial scale `s = 2^{-k}`, the half-open dyadic shell selected by
the finite central-ball reassembly is contained in the closed annulus used
by the thin-radial tail estimates. -/
theorem dyadicSpatialShell_subset_thinRadialTailAnnulus
    (d k : Nat) :
    dyadicSpatialShell d (-(k : Int) - 2) ⊆
      euclideanAnnulus d (((2 : Real) ^ k)⁻¹ / 4)
        (((2 : Real) ^ k)⁻¹ / 2) := by
  intro x hx
  change (2 : Real) ^ (-(k : Int) - 2) < ‖x‖ ∧
    ‖x‖ ≤ (2 : Real) ^ ((-(k : Int) - 2) + 1) at hx
  rw [show (2 : Real) ^ (-(k : Int) - 2) = ((2 : Real) ^ k)⁻¹ / 4 by
    rw [show (-(k : Int) - 2) = -(k : Int) + (-2 : Int) by ring]
    rw [zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
    norm_num [zpow_neg, zpow_natCast, div_eq_mul_inv]] at hx
  rw [show (2 : Real) ^ ((-(k : Int) - 2) + 1) =
      ((2 : Real) ^ k)⁻¹ / 2 by
    rw [show (-(k : Int) - 2 + 1) = -(k : Int) + (-1 : Int) by ring]
    rw [zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
    norm_num [zpow_neg, zpow_natCast, div_eq_mul_inv]] at hx
  simp only [euclideanAnnulus, mem_diff, Metric.mem_closedBall,
    Metric.mem_ball, dist_zero_right]
  exact ⟨hx.2, not_lt.mpr hx.1.le⟩

/-- Every shell in the finite `B(0,1/32)` decomposition has a tail scale
which is admissible for a band at level `j`. -/
theorem exists_thinRadialTail_scale_of_mem_centralShell
    {j : Nat} {l : Int} (_hj : 6 ≤ j)
    (hl : l ∈ Finset.Icc (-(j : Int)) (-6)) :
    ∃ k : Nat, 4 ≤ k ∧ k + 2 ≤ j ∧ l = -(k : Int) - 2 := by
  let k : Nat := (-l - 2).toNat
  have hllow : -(j : Int) ≤ l := (Finset.mem_Icc.mp hl).1
  have hlhigh : l ≤ -6 := (Finset.mem_Icc.mp hl).2
  have hkint : 0 ≤ -l - 2 := by omega
  have hkdef : (k : Int) = -l - 2 := by
    dsimp only [k]
    exact Int.toNat_of_nonneg hkint
  refine ⟨k, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- The tail annulus controls the raw moment on its corresponding half-open
dyadic output shell. -/
theorem setLIntegral_dyadicSpatialShell_le_thinRadialTailAnnulus
    {d : Nat} (k : Nat) (mu : Measure (Euclidean d))
    (F : Euclidean d → ENNReal) :
    (∫⁻ x in dyadicSpatialShell d (-(k : Int) - 2), F x ∂mu) ≤
      ∫⁻ x in euclideanAnnulus d (((2 : Real) ^ k)⁻¹ / 4)
        (((2 : Real) ^ k)⁻¹ / 2), F x ∂mu :=
  lintegral_mono_set (dyadicSpatialShell_subset_thinRadialTailAnnulus d k)

end

end LeanSpherical.HarmonicAnalysis
