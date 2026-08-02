/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.StrictParameterBounds

/-!
# Parameters for the positive-weight branch

The positive argument interpolates an unweighted exponent `q` with a
codimension-one weighted endpoint.  This file extracts the needed `q` and
conjugation exponent directly from strict admissibility.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set

noncomputable section

/-- At a strictly admissible nonnegative weight, one can choose an
unweighted exponent strictly above the Minkowski threshold and a Bessel
conjugation exponent below the codimension-one endpoint. -/
theorem exists_positive_weight_interpolation_parameters
    {d : ℕ} (hd : 3 ≤ d) {E : Set ℝ} (hE : E.Nonempty)
    (hEpos : E ⊆ Ioi (0 : ℝ)) {p α : ℝ} (_hp : 1 < p) (hα : 0 ≤ α)
    (hstrict :
      max ((α : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : ℝ) - 1) * (p - 2) - α)) <
        (↑(((d : ℝ) - 1) * (p - 1)) : EReal)) :
    ∃ q a : ℝ, 1 < q ∧ q < p ∧ 0 ≤ a ∧ a < (d : ℝ) - 1 ∧
      α = a * (p - q) ∧
      multiplicativeMinkowskiExponent E <
        (↑(((d : ℝ) - 1) * (q - 1)) : EReal) := by
  let m : ℝ := (d : ℝ) - 1
  let T : ℝ := m * (p - 1)
  have hm : 0 < m := by
    dsimp only [m]
    have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hM_nonneg : (0 : EReal) ≤ multiplicativeMinkowskiExponent E :=
    multiplicativeMinkowskiExponent_nonneg_of_nonempty_of_subset_Ioi hE hEpos
  have hfirst : (α : EReal) + multiplicativeMinkowskiExponent E < (T : EReal) := by
    simpa only [T] using alpha_add_multiplicativeMinkowskiExponent_lt_of_strict hstrict
  obtain ⟨u, hu_lower, hu_upper⟩ := EReal.lt_iff_exists_real_btwn.mp hfirst
  let s : ℝ := u - α
  have hM_s : multiplicativeMinkowskiExponent E < (s : EReal) := by
    rw [show (s : EReal) = (u : EReal) - (α : EReal) by
      dsimp only [s]
      rw [← EReal.coe_sub]]
    exact (EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ne_bot α))
      (Or.inl (EReal.coe_ne_top α))).mpr (by simpa only [add_comm] using hu_lower)
  have hs_T : s < T - α := by
    have huT : u < T := by exact_mod_cast hu_upper
    dsimp only [s]
    linarith
  have hs_pos : 0 < s := by
    have hM_s0 : (0 : EReal) < (s : EReal) := lt_of_le_of_lt hM_nonneg hM_s
    exact_mod_cast hM_s0
  let q : ℝ := 1 + s / m
  have hmq : m * (p - q) = T - s := by
    dsimp only [q, T]
    field_simp [hm.ne']
    ring
  have halpha_gap : α < m * (p - q) := by
    rw [hmq]
    linarith
  have hq_one : 1 < q := by
    dsimp only [q]
    exact lt_add_of_pos_right _ (div_pos hs_pos hm)
  have hq_gap : 0 < p - q := by
    have hTs : 0 < T - s := by
      linarith [hs_T, hα]
    rw [← hmq] at hTs
    nlinarith [hm]
  let a : ℝ := α / (p - q)
  have ha_nonneg : 0 ≤ a := by
    dsimp only [a]
    exact div_nonneg hα hq_gap.le
  have ha_lt : a < m := by
    apply (div_lt_iff₀ hq_gap).mpr
    exact halpha_gap
  refine ⟨q, a, hq_one, ?_, ha_nonneg, ?_, ?_, ?_⟩
  · exact sub_pos.mp hq_gap
  · simpa only [m] using ha_lt
  · dsimp only [a]
    field_simp [hq_gap.ne']
  · have hcrit : multiplicativeMinkowskiExponent E < ((m * (q - 1) : ℝ) : EReal) := by
      have hs_eq : m * (q - 1) = s := by
        dsimp only [q]
        field_simp [hm.ne']
        ring
      rw [show ((m * (q - 1) : ℝ) : EReal) = (s : EReal) by
        exact congrArg (fun z : ℝ => (z : EReal)) hs_eq]
      exact hM_s
    change multiplicativeMinkowskiExponent E < ((m * (q - 1) : ℝ) : EReal)
    exact hcrit

end

end LeanSpherical.HarmonicAnalysis
