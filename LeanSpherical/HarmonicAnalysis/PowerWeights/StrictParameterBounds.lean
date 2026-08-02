/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.EntropyLowerBounds
import LeanSpherical.HarmonicAnalysis.PowerWeights.Admissibility

/-!
# Elementary finite bounds in the strict implicit region

These are the numerical consequences needed by the low-frequency part of
the local estimate.  They are stated directly, rather than introducing a
second parameter-region abstraction.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set

noncomputable section

/-- Strict admissibility forces the locally integrable lower power-weight
bound. -/
theorem one_sub_dim_lt_alpha_of_strict_powerWeightEntropyImplicitCondition
    {d : Nat} (_hd : 2 ≤ d) {E : Set ℝ} (hE : E.Nonempty)
    (hEpos : E ⊆ Ioi (0 : ℝ)) {p α : ℝ}
    (hstrict :
      max ((α : EReal) + multiplicativeMinkowskiExponent E)
        (multiplicativeLegendreAssouadExponent E
          (((d : ℝ) - 1) * (p - 2) - α)) <
        (↑(((d : ℝ) - 1) * (p - 1)) : EReal)) :
    1 - (d : ℝ) < α := by
  let ρ : ℝ := ((d : ℝ) - 1) * (p - 2) - α
  let T : ℝ := ((d : ℝ) - 1) * (p - 1)
  have hν : multiplicativeLegendreAssouadExponent E ρ < (T : EReal) :=
    (le_max_right _ _).trans_lt (by simpa only [ρ, T] using hstrict)
  have hρ : (ρ : EReal) ≤ multiplicativeLegendreAssouadExponent E ρ :=
    le_multiplicativeLegendreAssouadExponent_of_nonempty_of_subset_Ioi hE hEpos ρ
  have hreal : ρ < T := by
    exact_mod_cast hρ.trans_lt hν
  dsimp only [ρ, T] at hreal
  linarith

/-- Strict admissibility also makes the upper affine face strict for a
nonempty positive radius set. -/
theorem alpha_add_multiplicativeMinkowskiExponent_lt_of_strict
    {d : Nat} {E : Set ℝ} {p α : ℝ}
    (hstrict :
      max ((α : EReal) + multiplicativeMinkowskiExponent E)
        (multiplicativeLegendreAssouadExponent E
          (((d : ℝ) - 1) * (p - 2) - α)) <
        (↑(((d : ℝ) - 1) * (p - 1)) : EReal)) :
    (α : EReal) + multiplicativeMinkowskiExponent E <
      (↑(((d : ℝ) - 1) * (p - 1)) : EReal) := by
  exact (le_max_left _ _).trans_lt hstrict

end

end LeanSpherical.HarmonicAnalysis
