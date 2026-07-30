/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.DimensionSpectrum

/-!
# The zero parameter of the upper Assouad spectrum

For the upper-spectrum convention used here, the condition at `theta = 0`
only tests the radius interval `[1,2]` itself: `δ ^ 0 ≤ |I|` forces
`|I| = 1`.  Consequently the zero parameter is exactly upper Minkowski
dimension.  This is the formal bridge that makes Theorem 2(i) the
`theta = 0` instance of the spectrum sharpness statement.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Set

noncomputable section

/-- A zero-parameter upper-spectrum covering exponent is an upper Minkowski
covering exponent for a radius set in `[1,2]`. -/
theorem HasUpperAssouadSpectrumExponent.toHasUpperMinkowskiExponent_zero
    {E : Set ℝ} {γ : ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hγ : HasUpperAssouadSpectrumExponent E 0 γ) :
    HasUpperMinkowskiExponent E γ := by
  intro ε hε
  obtain ⟨C, hC, hcover⟩ := hγ
  refine ⟨C, hC, fun δ hδ hδone => ?_⟩
  obtain ⟨ι, hι, hιcard⟩ := hcover δ 1 2 hδ hδone
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ι, ?_, ?_⟩
  · apply hι.mono
    intro x hx
    exact ⟨hx, hE hx⟩
  · have hpow : δ ^ (-γ) ≤ δ ^ (-(γ + ε)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδone.le
      linarith
    calc
      (ι.card : ℝ) ≤ C * ((2 - 1) / δ) ^ γ := hιcard
      _ = C * δ ^ (-γ) := by
        rw [show (2 : ℝ) - 1 = 1 by norm_num, one_div,
          ← Real.rpow_neg_eq_inv_rpow]
      _ ≤ C * δ ^ (-(γ + ε)) := mul_le_mul_of_nonneg_left hpow hC.le

/-- The infimum defining upper Minkowski dimension is bounded by the zero
upper-spectrum infimum. -/
theorem upperMinkowskiDimension_le_upperAssouadSpectrum_zero
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) :
    upperMinkowskiDimension E ≤ upperAssouadSpectrum E 0 := by
  let M : Set ℝ := {s : ℝ | 0 ≤ s ∧ HasUpperMinkowskiExponent E s}
  let S : Set ℝ := upperAssouadAdmissibleExponents E 0
  have hMbelow : BddBelow M := by
    refine ⟨0, ?_⟩
    intro s hs
    exact hs.1
  have hSne : S.Nonempty := upperAssouadAdmissibleExponents_nonempty E zero_le_one
  change sInf M ≤ sInf S
  apply le_csInf hSne
  intro s hs
  apply csInf_le hMbelow
  exact ⟨hs.1, hs.2.toHasUpperMinkowskiExponent_zero hE⟩

/-- At parameter zero, the upper Assouad spectrum equals upper Minkowski
dimension for every radius set contained in `[1,2]`. -/
theorem upperAssouadSpectrum_zero_eq_upperMinkowskiDimension
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) :
    upperAssouadSpectrum E 0 = upperMinkowskiDimension E := by
  apply le_antisymm
  · simpa using
      (upperAssouadSpectrum_le_minkowski_ratio_of_upperMinkowskiDimension_eq
        hE (β := upperMinkowskiDimension E) rfl (by norm_num) zero_lt_one)
  · exact upperMinkowskiDimension_le_upperAssouadSpectrum_zero hE

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
