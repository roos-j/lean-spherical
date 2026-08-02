/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.Assembly
import LeanSpherical.HarmonicAnalysis.PowerWeights.NecessaryAssembly
import LeanSpherical.HarmonicAnalysis.PowerWeights.StrictPositive
import LeanSpherical.HarmonicAnalysis.PowerWeights.StrictUpper

/-!
# Final analytic assembly

Once the all-scale unweighted theorem and the subquadratic negative-weight
local theorem are available, the remaining proof of Theorem 1.1 is the two
sign case split followed by the already formalized parameter closure.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set Topology

noncomputable section

/-- The theorem follows from the all-scale unweighted input and the strict
negative subquadratic input.  This is deliberately the last assembly layer:
the two analytic inputs remain visible in its hypotheses. -/
theorem power_weight_spherical_maximal_main_of_unweighted_and_negative
    {d : Nat} (hd : 3 ≤ d) (E : Set ℝ) (hE : E.Nonempty) (hEpos : E ⊆ Ioi (0 : ℝ))
    (hunweighted : ∀ ⦃q : ℝ⦄, 1 < q →
      multiplicativeMinkowskiExponent E <
        (↑(((d : ℝ) - 1) * (q - 1)) : EReal) →
      HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E q 0)
    (hnegative : ∀ ⦃q a : ℝ⦄, 1 < q → q < 2 → a < 0 →
      max ((a : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : ℝ) - 1) * (q - 2) - a)) <
        (↑(((d : ℝ) - 1) * (q - 1)) : EReal) →
      HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E q a) :
    closure (restrictedNormalizedSphericalMaximalPowerWeightTypeSet d E) =
      powerWeightAdmissibleRegion d E := by
  apply powerWeightAdmissibleRegion_eq_closure_of_strict_upper_necessary
    hd E hE hEpos
  · intro p α hp hstrong
    exact powerWeightEntropyImplicitCondition_of_restrictedStrongType
      hd hE hEpos hp hstrong
  · intro p α hp hstrict
    apply hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_strict_implicit
      hd E hE hEpos hp hstrict
    · intro q a hq hq2 ha hqstrict
      exact hnegative hq hq2 ha hqstrict
    · intro q a hq ha hqstrict
      exact
        hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_strict_implicit_nonnegative
          hd E hE hEpos hq ha hqstrict hunweighted

end

end LeanSpherical.HarmonicAnalysis
