/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.ThinRadialTailSummation

/-!
# Numerical factors in strict-negative thin-radial tails

The tail reassembly has one harmless polynomial loss from the number of
distance blocks.  This file isolates that loss and the two geometric ratios
which remain after the literal tail coefficient is put in dyadic form.
-/

namespace LeanSpherical.HarmonicAnalysis

open scoped ENNReal

noncomputable section

/-- The number of dyadic distance blocks on the `k`th shell is absorbed by
the quadratic polynomial factor in the final raw band rate. -/
theorem thinRadialTail_reassembly_polynomial_factor_le
    {j k : Nat} {p : Real} (hp : 1 ≤ p) (hjk : k + 1 ≤ j) (A : ENNReal) :
    ((k + 5 : Nat) : ENNReal) ^ (p - 1) * A ≤
      ((4 : ENNReal) ^ (p - 1) *
        ((j + 1 : Nat) : ENNReal) ^ (p - 1)) * A := by
  have hpminus : 0 ≤ p - 1 := by linarith
  have hnat : k + 5 ≤ 4 * (j + 1) := by omega
  have hbase : ((k + 5 : Nat) : ENNReal) ≤
      (4 : ENNReal) * ((j + 1 : Nat) : ENNReal) := by
    exact_mod_cast hnat
  calc
    ((k + 5 : Nat) : ENNReal) ^ (p - 1) * A ≤
        ((4 : ENNReal) * ((j + 1 : Nat) : ENNReal)) ^ (p - 1) * A :=
      by
        simpa only [mul_comm] using
          mul_le_mul_right (ENNReal.rpow_le_rpow hbase hpminus) A
    _ = ((4 : ENNReal) ^ (p - 1) *
        ((j + 1 : Nat) : ENNReal) ^ (p - 1)) * A := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpminus]

/-- The distance-block reassembly emits a range indexed by the binary
logarithm of `2^(k+4)`; its cardinality is exactly `k+5`. -/
theorem thinRadialTail_distanceBlock_range_card (k : Nat) :
    ((Finset.range (Nat.log 2 (2 ^ (k + 4)) + 1)).card : ENNReal) =
      ((k + 5 : Nat) : ENNReal) := by
  rw [Nat.log_pow (by norm_num : 1 < 2)]
  simp only [Finset.card_range]

/-- The shell-distance and distance-block factors left by the raw tail
coefficient are genuine geometric gains in the strict negative range. -/
theorem thinRadialTail_geometric_ratios_lt_one
    (n : Nat) {p alpha : Real} (hp : 1 < p) (halpha : alpha ≤ 0) :
    (ENNReal.ofReal (1 / 2 : Real)) ^
        (p * ((n : Real) + 3) - ((n : Real) + alpha)) < 1 ∧
      (ENNReal.ofReal (1 / 2 : Real)) ^ (p * ((n : Real) + 3)) < 1 := by
  have hbase : ENNReal.ofReal (1 / 2 : Real) < 1 := by norm_num
  have hnthree : 0 < (n : Real) + 3 := by positivity
  have hproduct : 0 < (p - 1) * ((n : Real) + 3) := by
    exact mul_pos (by linarith) hnthree
  have hshell : 0 < p * ((n : Real) + 3) - ((n : Real) + alpha) := by
    nlinarith
  have hblock : 0 < p * ((n : Real) + 3) :=
    mul_pos (by linarith) hnthree
  exact ⟨ENNReal.rpow_lt_one hbase hshell,
    ENNReal.rpow_lt_one hbase hblock⟩

end

end LeanSpherical.HarmonicAnalysis
