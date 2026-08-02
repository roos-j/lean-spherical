/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.FinitePhysicalCZWeak
import LeanSpherical.HarmonicAnalysis.PowerWeights.FinalAssembly
import LeanSpherical.HarmonicAnalysis.PowerWeights.GlobalFinitePhysicalCZBridge
import LeanSpherical.HarmonicAnalysis.PowerWeights.GlobalUnweightedParameters
import LeanSpherical.HarmonicAnalysis.PowerWeights.StrictNegativeEndpoint
import LeanSpherical.HarmonicAnalysis.PowerWeights.StrictUnweightedParameters

/-!
# Power weight inequalities for restricted spherical maximal functions

This is the statement layer for the `d ≥ 3` form of Theorem 1.1 of
Fraccaroli--Roos--Seeger.  The entropy quantities use the paper's
continuous-scale convention and take values in extended reals until their
finiteness properties have been established.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set Topology

noncomputable section

/-- The `d ≥ 3` form of the main theorem.  Its proof is built
from the sharp lower tests, the localized weighted upper estimate, and the
global-to-local reassembly developed in the companion files. -/
theorem power_weight_spherical_maximal_main
    {d : ℕ} (hd : 3 ≤ d) (E : Set ℝ) (hE : E.Nonempty) (hEpos : E ⊆ Ioi (0 : ℝ)) :
    closure (restrictedNormalizedSphericalMaximalPowerWeightTypeSet d E) =
      powerWeightAdmissibleRegion d E := by
  have hunweighted : ∀ ⦃q : Real⦄, 1 < q →
      multiplicativeMinkowskiExponent E <
        (↑(((d : Real) - 1) * (q - 1)) : EReal) →
      HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E q 0 := by
    intro q hq hcritical
    by_cases hq2 : q < 2
    · obtain ⟨beta, _hbeta, hM, hbetacritical⟩ :=
        exists_nonneg_real_between_multiplicativeMinkowskiExponent_and
          hE hEpos hcritical
      exact
        hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_zero_of_multiplicativeMinkowskiExponent_lt_and_uniform_finite_physical_CZ_weak_one_dim
          hd E hE hEpos hq hq2 hM
          (by simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
            using hbetacritical)
          (hfinite_weak_one_restrictedRelativeBandpassSphericalMaximal_of_shifted_physical_CZ
            hd E hE hEpos)
    · exact
        hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_zero_of_two_le
          hd E (le_of_not_gt hq2)
  apply power_weight_spherical_maximal_main_of_unweighted_and_negative
    hd E hE hEpos hunweighted
  intro q alpha hq hq2 halpha hstrict
  exact hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_strict_negative_subtwo
    hd E hE hEpos hq hq2 halpha hstrict
      (hunweighted hq
        (multiplicativeMinkowskiExponent_lt_critical_of_strict_implicit hstrict))

end

end LeanSpherical.HarmonicAnalysis
