/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.StrictParameterBounds

/-!
# The unweighted consequence of strict admissibility

Both weighted branches use the same observation: the Legendre--Assouad term
dominates the unit-window Minkowski exponent, so strict admissibility puts
the current exponent strictly above the unweighted threshold.
-/

namespace LeanSpherical.HarmonicAnalysis

noncomputable section

/-- Strict admissibility implies the strict unweighted Minkowski inequality
at the same exponent. -/
theorem multiplicativeMinkowskiExponent_lt_critical_of_strict_implicit
    {d : Nat} {E : Set ℝ} {p α : ℝ}
    (hstrict :
      max ((α : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : ℝ) - 1) * (p - 2) - α)) <
        (↑(((d : ℝ) - 1) * (p - 1)) : EReal)) :
    multiplicativeMinkowskiExponent E <
      (↑(((d : ℝ) - 1) * (p - 1)) : EReal) := by
  calc
    multiplicativeMinkowskiExponent E ≤
        multiplicativeLegendreAssouadExponent E
          (((d : ℝ) - 1) * (p - 2) - α) :=
      multiplicativeMinkowskiExponent_le_multiplicativeLegendreAssouadExponent E _
    _ ≤ max ((α : EReal) + multiplicativeMinkowskiExponent E)
        (multiplicativeLegendreAssouadExponent E
          (((d : ℝ) - 1) * (p - 2) - α)) := le_max_right _ _
    _ < _ := hstrict

end

end LeanSpherical.HarmonicAnalysis
