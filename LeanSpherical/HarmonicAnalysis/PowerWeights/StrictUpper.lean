/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.StrictNegativeHigher

/-!
# Assembly of the strict upper estimate

The analytic argument has two genuine ranges: negative weights below the
quadratic exponent, and nonnegative weights.  The negative estimate above
the quadratic exponent follows from the former by the already established
higher-exponent reduction.  This file contains only that final case split.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set

noncomputable section

/-- The subquadratic negative and the nonnegative strict estimates together
give the strict upper estimate at every finite exponent. -/
theorem hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_strict_implicit
    {d : Nat} (hd : 3 ≤ d) (E : Set ℝ) (hE : E.Nonempty)
    (hEpos : E ⊆ Ioi (0 : ℝ)) {p α : ℝ} (hp : 1 < p)
    (hstrict :
      max ((α : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : ℝ) - 1) * (p - 2) - α)) <
        (↑(((d : ℝ) - 1) * (p - 1)) : EReal))
    (hnegative : ∀ ⦃q a : ℝ⦄, 1 < q → q < 2 → a < 0 →
      max ((a : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : ℝ) - 1) * (q - 2) - a)) <
        (↑(((d : ℝ) - 1) * (q - 1)) : EReal) →
      HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E q a)
    (hnonnegative : ∀ ⦃q a : ℝ⦄, 1 < q → 0 ≤ a →
      max ((a : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : ℝ) - 1) * (q - 2) - a)) <
        (↑(((d : ℝ) - 1) * (q - 1)) : EReal) →
      HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E q a) :
    HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p α := by
  by_cases hα : α < 0
  · by_cases hp₂ : p < 2
    · exact hnegative hp hp₂ hα hstrict
    · exact
        hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_strict_negative_ge_two_of_subquadratic
          hd hE hEpos (le_of_not_gt hp₂) hα hstrict
          (fun hq hq₂ ha hqstrict => hnegative hq hq₂ ha hqstrict)
  · exact hnonnegative hp (le_of_not_gt hα) hstrict

end

end LeanSpherical.HarmonicAnalysis
