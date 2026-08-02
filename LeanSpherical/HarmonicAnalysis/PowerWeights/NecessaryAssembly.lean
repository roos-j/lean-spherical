/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.NecessaryNegative
import LeanSpherical.HarmonicAnalysis.PowerWeights.NecessaryNonnegative

/-!
# Assembly of the two power-weight necessity arguments

The sharp tests are naturally separated by the sign of the weight exponent.
This file joins those two finished statements in the form consumed by the
final parameter-set assembly.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set

noncomputable section

/-- Every finite weighted strong-type point satisfies the implicit entropy
condition. -/
theorem powerWeightEntropyImplicitCondition_of_restrictedStrongType
    {d : Nat} (hd : 3 <= d) {E : Set Real} (hE : E.Nonempty)
    (hEpos : E ⊆ Ioi (0 : Real)) {p alpha : Real} (hp : 1 <= p)
    (hstrong : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p alpha) :
    powerWeightEntropyImplicitCondition d E p alpha := by
  let n : Nat := d - 1
  have hn : 2 <= n := by
    dsimp only [n]
    omega
  have hdim : n + 1 = d := by
    dsimp only [n]
    omega
  have hstrong' :
      HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType (n + 1) E p alpha := by
    simpa only [hdim] using hstrong
  by_cases halpha : alpha < 0
  · have h := powerWeightEntropyImplicitCondition_of_restrictedStrongType_of_neg
      n hn hE hEpos hp halpha hstrong'
    simpa only [hdim] using h
  · have h := powerWeightEntropyImplicitCondition_of_restrictedStrongType_of_nonneg
      n hn hp (le_of_not_gt halpha) hstrong'
    simpa only [hdim] using h

end

end LeanSpherical.HarmonicAnalysis
