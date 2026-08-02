/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.HigherPParameters

/-!
# Reduction of negative high exponents to the subquadratic range

The local cap argument is formulated below exponent two.  A negative power
weight which is locally integrable has a strict ambient entropy margin at a
nearby subquadratic exponent, independently of the original exponent.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set

noncomputable section

/-- A strictly admissible negative parameter at an exponent at least two can
be reduced to a strictly admissible exponent below two, without changing the
power weight. -/
theorem exists_strict_powerWeightEntropyImplicitCondition_subtwo_of_strict_negative_ge_two
    {d : Nat} (hd : 3 <= d) {E : Set Real} (hE : E.Nonempty)
    (hEpos : E ⊆ Ioi (0 : Real)) {p alpha : Real} (hp : (2 : Real) <= p)
    (halpha : alpha < 0)
    (hstrict :
      max ((alpha : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : Real) - 1) * (p - 2) - alpha)) <
        ((((d : Real) - 1) * (p - 1) : Real) : EReal)) :
    exists q : Real, 1 < q /\ q < 2 /\ q < p /\
      max ((alpha : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : Real) - 1) * (q - 2) - alpha)) <
        ((((d : Real) - 1) * (q - 1) : Real) : EReal) := by
  have halpha_lower : 1 - (d : Real) < alpha :=
    one_sub_dim_lt_alpha_of_strict_powerWeightEntropyImplicitCondition
      (show 2 <= d by omega) hE hEpos hstrict
  obtain ⟨q, hq_one, hq_two, hq_strict⟩ :=
    exists_strict_powerWeightEntropyImplicitCondition_subtwo_of_neg
      hd halpha_lower halpha
  exact ⟨q, hq_one, hq_two, lt_of_lt_of_le hq_two hp, hq_strict⟩

end

end LeanSpherical.HarmonicAnalysis
