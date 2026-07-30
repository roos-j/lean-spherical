/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4StrictParameters

/-!
# The critical planar radius-gap calculation

At `d = 2` and quasi-Assouad exponent `gamma = 1 / 2`, the gap exponent in
the Section 3 interpolation is positive as soon as the frequency exponent is
negative.  This does not obstruct the nonendpoint theorem: the literal gap
partition is empty beyond `n = j + O(1)`.  Combining the two exponents before
summing gives a strictly negative frequency exponent.

This is the elementary parameter calculation used for the planar critical
case.  It is deliberately separate from `Q4StrictParameters`, whose ordinary
geometric summation applies only when both exponents are negative.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

noncomputable section

open scoped BigOperators

/-- A finite increasing geometric sum is bounded by its last scale.  This
elementary form is the one needed when the positive gap exponent in the
planar critical case is compensated by the finite range `n < j + O(1)`. -/
theorem q4_finset_sum_pow_le_last_scale_of_one_lt
    {r : ℝ} (hr : 1 < r) (N : ℕ) :
    (∑ n ∈ Finset.range N, r ^ n) ≤ r ^ N / (r - 1) := by
  rw [geom_sum_of_one_lt hr N]
  apply (div_le_div_iff_of_pos_right (sub_pos.mpr hr)).mpr
  linarith

/-- A convenient strict interpolation parameter at the planar critical
dimension. -/
theorem exists_q4_planar_critical_parameter :
    ∃ theta : Real, 1 / 2 < theta ∧ theta < 1 := by
  refine ⟨3 / 4, ?_, ?_⟩ <;> norm_num

/-- In the critical planar case, a shell level bounded by `j + 3` can be
absorbed into a strictly decaying frequency factor. -/
theorem q4_planar_critical_shell_exponent_le
    {theta : Real} {j n : Nat}
    (htheta : 1 / 2 < theta) (hn : n ≤ j + 3) :
    q4FrequencyExponent 2 theta * (j : Real) +
        q4GapExponent 2 (1 / 2) theta * (n : Real) ≤
      (1 / 2 - theta) * (j : Real) + 3 * (theta - 1 / 2) := by
  have hfreq : q4FrequencyExponent 2 theta = 1 - 2 * theta := by
    norm_num [q4FrequencyExponent]
  have hgap : q4GapExponent 2 (1 / 2) theta = theta - 1 / 2 := by
    norm_num [q4GapExponent]
    ring
  rw [hfreq, hgap]
  have hnreal : (n : Real) ≤ (j : Real) + 3 := by
    exact_mod_cast hn
  have hgap_nonneg : 0 ≤ theta - 1 / 2 := by linarith
  have hmul : (theta - 1 / 2) * (n : Real) ≤
      (theta - 1 / 2) * ((j : Real) + 3) :=
    mul_le_mul_of_nonneg_left hnreal hgap_nonneg
  calc
    (1 - 2 * theta) * (j : Real) + (theta - 1 / 2) * (n : Real) ≤
        (1 - 2 * theta) * (j : Real) +
          (theta - 1 / 2) * ((j : Real) + 3) :=
      add_le_add_left hmul _
    _ = (1 / 2 - theta) * (j : Real) + 3 * (theta - 1 / 2) := by ring

/-- The combined frequency exponent above is strictly negative. -/
theorem q4_planar_critical_combined_frequency_exponent_neg
    {theta : Real} (htheta : 1 / 2 < theta) :
    1 / 2 - theta < 0 := by
  linarith

/-- The actual finite planar gap range is summable without Bourgain's
endpoint device.  At `d = 2` and `gamma = 1/2`, the gap factor grows with
`n`, but the exact active relation has only `n < j + 3`.  Summing that
increasing geometric progression gives a constant times
`rho^j`, where `rho = 2^(1/2-theta) < 1`.

This is deliberately a scalar lemma: it is consumed after Minkowski has
turned the literal finite-product shell into the sum of its level norms. -/
theorem q4_planar_critical_finite_level_sum_le
    {theta : ℝ} (htheta : 1 / 2 < theta) (j : ℕ) :
    (∑ n ∈ Finset.range (j + 3),
      (2 : ℝ) ^
        (q4FrequencyExponent 2 theta * (j : ℝ) +
          q4GapExponent 2 (1 / 2) theta * (n : ℝ))) ≤
      (((2 : ℝ) ^ (theta - 1 / 2)) ^ 3 /
        ((2 : ℝ) ^ (theta - 1 / 2) - 1)) *
        ((2 : ℝ) ^ (1 / 2 - theta)) ^ j := by
  let a : ℝ := q4FrequencyExponent 2 theta
  let b : ℝ := q4GapExponent 2 (1 / 2) theta
  let r : ℝ := (2 : ℝ) ^ (theta - 1 / 2)
  have ha : a = 1 - 2 * theta := by
    dsimp [a, q4FrequencyExponent]
    norm_num
  have hb : b = theta - 1 / 2 := by
    dsimp [b, q4GapExponent]
    norm_num
    ring
  have hbpos : 0 < theta - 1 / 2 := by linarith
  have hr : 1 < r := by
    dsimp [r]
    exact Real.one_lt_rpow (by norm_num) hbpos
  have hsum : (∑ n ∈ Finset.range (j + 3), r ^ n) ≤
      r ^ (j + 3) / (r - 1) :=
    q4_finset_sum_pow_le_last_scale_of_one_lt hr (j + 3)
  have hfactor : 0 ≤ (2 : ℝ) ^ (a * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    (∑ n ∈ Finset.range (j + 3),
      (2 : ℝ) ^
        (q4FrequencyExponent 2 theta * (j : ℝ) +
          q4GapExponent 2 (1 / 2) theta * (n : ℝ))) =
        (2 : ℝ) ^ (a * (j : ℝ)) *
          ∑ n ∈ Finset.range (j + 3), r ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [r]
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)
        (theta - 1 / 2) n]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show q4FrequencyExponent 2 theta = a by rfl,
        show q4GapExponent 2 (1 / 2) theta = b by rfl, hb]
    _ ≤ (2 : ℝ) ^ (a * (j : ℝ)) * (r ^ (j + 3) / (r - 1)) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = (((2 : ℝ) ^ (theta - 1 / 2)) ^ 3 /
        ((2 : ℝ) ^ (theta - 1 / 2) - 1)) *
        ((2 : ℝ) ^ (1 / 2 - theta)) ^ j := by
      rw [pow_add]
      dsimp [r]
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)
        (theta - 1 / 2) j,
        ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)
          (1 / 2 - theta) j]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [ha, hb]
      congr 2
      ring

/-- The dyadic base produced by the finite planar summation is strictly
smaller than one. -/
theorem q4_planar_critical_finite_level_ratio_lt_one
    {theta : ℝ} (htheta : 1 / 2 < theta) :
    (2 : ℝ) ^ (1 / 2 - theta) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (q4_planar_critical_combined_frequency_exponent_neg htheta)

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
