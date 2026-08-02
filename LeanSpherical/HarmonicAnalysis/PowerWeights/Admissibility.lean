/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.EntropyComparison

/-!
# The parameter region for power-weight spherical maximal estimates

This file contains the literal implicit region in Theorem 1.1.  Keeping it
separate from the final assembly lets the analytic upper and lower arguments
refer to the same condition without importing the theorem statement itself.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set

noncomputable section

/-- The implicit admissibility condition from (1.9).  Extended reals keep the
definition total until local entropy finiteness is established. -/
def powerWeightEntropyImplicitCondition (d : ℕ) (E : Set ℝ) (p α : ℝ) : Prop :=
  max ((α : EReal) + multiplicativeMinkowskiExponent E)
      (multiplicativeLegendreAssouadExponent E
        (((d : ℝ) - 1) * (p - 2) - α)) ≤
    (↑(((d : ℝ) - 1) * (p - 1)) : EReal)

/-- The right hand side of the implicit form of Theorem 1.1.  Besides its
finite-exponent points it contains the vertical limiting face reached as
`p → ∞`: finite admissible points have coordinates `(1 / p, α / p)`, and
their possible limits on the zero axis are exactly `{0} × [0, d - 1]`. -/
def powerWeightAdmissibleRegion (d : ℕ) (E : Set ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 = 0 ∧ q.2 ∈ Icc (0 : ℝ) ((d : ℝ) - 1)} ∪
    {q | ∃ p α : ℝ, 1 ≤ p ∧ q.1 = p⁻¹ ∧ q.2 = α / p ∧
      powerWeightEntropyImplicitCondition d E p α}

/-- The implicit condition already contains the critical Minkowski
inequality: the local Legendre--Assouad term dominates the unit-window
Minkowski exponent. -/
theorem multiplicativeMinkowskiExponent_le_critical_of_powerWeightEntropyImplicitCondition
    (d : ℕ) (E : Set ℝ) (p α : ℝ)
    (h : powerWeightEntropyImplicitCondition d E p α) :
    multiplicativeMinkowskiExponent E ≤
      (↑(((d : ℝ) - 1) * (p - 1)) : EReal) := by
  calc
    multiplicativeMinkowskiExponent E ≤
        multiplicativeLegendreAssouadExponent E
          (((d : ℝ) - 1) * (p - 2) - α) :=
      multiplicativeMinkowskiExponent_le_multiplicativeLegendreAssouadExponent E _
    _ ≤ max ((α : EReal) + multiplicativeMinkowskiExponent E)
        (multiplicativeLegendreAssouadExponent E
          (((d : ℝ) - 1) * (p - 2) - α)) := le_max_right _ _
    _ ≤ (↑(((d : ℝ) - 1) * (p - 1)) : EReal) := h

end

end LeanSpherical.HarmonicAnalysis
