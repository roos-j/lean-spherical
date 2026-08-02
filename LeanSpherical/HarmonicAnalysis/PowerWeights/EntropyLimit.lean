/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.Entropy

/-!
# Direct limit-superior tests for the entropy exponents

The sharpness argument produces lower bounds at arbitrarily small scales.
This file records just the two direct conversions of such bounds into the
continuous entropy exponents appearing in the main statement.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

/-- An eventual upper bound for the unit-window logarithmic entropy quotient
controls the upper Minkowski exponent. -/
theorem multiplicativeMinkowskiExponent_le_of_eventually_entropyLogQuotient_le
    {E : Set ℝ} {s : EReal}
    (h : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      entropyLogQuotient (unitMultiplicativeEntropy E δ) δ ≤ s) :
    multiplicativeMinkowskiExponent E ≤ s := by
  exact Filter.limsup_le_of_le (h := h)

/-- Lower bounds for the unit-window logarithmic entropy quotient at
arbitrarily small scales control the upper Minkowski exponent from below. -/
theorem le_multiplicativeMinkowskiExponent_of_frequently_le_entropyLogQuotient
    {E : Set ℝ} {s : EReal}
    (h : ∃ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      s ≤ entropyLogQuotient (unitMultiplicativeEntropy E δ) δ) :
    s ≤ multiplicativeMinkowskiExponent E := by
  exact Filter.le_limsup_of_frequently_le h

/-- An eventual upper bound for the local Legendre--Assouad logarithmic
entropy quotient controls the corresponding exponent. -/
theorem multiplicativeLegendreAssouadExponent_le_of_eventually_entropyLogQuotient_le
    {E : Set ℝ} {rho : ℝ} {s : EReal}
    (h : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      entropyLogQuotient (multiplicativeLegendreAssouadProfile E rho δ) δ ≤ s) :
    multiplicativeLegendreAssouadExponent E rho ≤ s := by
  exact Filter.limsup_le_of_le (h := h)

/-- Lower bounds for the local Legendre--Assouad logarithmic entropy quotient
at arbitrarily small scales control the corresponding exponent from below. -/
theorem le_multiplicativeLegendreAssouadExponent_of_frequently_le_entropyLogQuotient
    {E : Set ℝ} {rho : ℝ} {s : EReal}
    (h : ∃ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      s ≤ entropyLogQuotient (multiplicativeLegendreAssouadProfile E rho δ) δ) :
    s ≤ multiplicativeLegendreAssouadExponent E rho := by
  exact Filter.le_limsup_of_frequently_le h

end

end LeanSpherical.HarmonicAnalysis
