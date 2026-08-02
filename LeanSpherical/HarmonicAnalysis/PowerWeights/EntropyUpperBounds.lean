/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.EntropyComparison

/-!
# Elementary upper comparisons for multiplicative entropy

The diameter-one window dominates every smaller multiplicative interval with
the same centre.  In particular the Legendre--Assouad exponent agrees with
the Minkowski exponent for nonpositive penalty parameters, as used in the
nonnegative-weight part of the parameter region.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

/-- Enlarging the logarithmic diameter at a fixed centre enlarges the
corresponding multiplicative interval. -/
theorem multiplicativeInterval_mono
    (c : PositiveRadius) {diam diam' : ℝ≥0} (hdiam : diam ≤ diam') :
    multiplicativeInterval c diam ⊆ multiplicativeInterval c diam' := by
  intro r hr
  refine ⟨hr.1, ?_⟩
  have hreal : (diam : ℝ) / 2 ≤ (diam' : ℝ) / 2 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hdiam) (by norm_num)
  exact hr.2.trans hreal

/-- Local entropy on an interval of multiplicative diameter at most one is
bounded by the unit-window entropy. -/
theorem localMultiplicativeEntropy_le_unitMultiplicativeEntropy
    (E : Set ℝ) (c : PositiveRadius) {diam δ : ℝ≥0} (hdiam : diam ≤ 1) :
    localMultiplicativeEntropy E c diam δ ≤ unitMultiplicativeEntropy E δ := by
  calc
    localMultiplicativeEntropy E c diam δ ≤
        localMultiplicativeEntropy E c 1 δ := by
      apply multiplicativeEntropy_mono
      exact inter_subset_inter_right _ (multiplicativeInterval_mono c hdiam)
    _ ≤ unitMultiplicativeEntropy E δ :=
      le_iSup (fun c : PositiveRadius => localMultiplicativeEntropy E c 1 δ) c

/-- Nonpositive interval penalties can only reduce the Legendre--Assouad
profile to the unit-window profile. -/
theorem multiplicativeLegendreAssouadProfile_le_unit_of_nonpos
    (E : Set ℝ) {rho : ℝ} (hrho : rho ≤ 0) (δ : ℝ≥0) :
    multiplicativeLegendreAssouadProfile E rho δ ≤
      (unitMultiplicativeEntropy E δ : ENNReal) := by
  unfold multiplicativeLegendreAssouadProfile
  apply iSup_le
  intro c
  apply iSup_le
  intro diam
  have hfactor : ((diam.1 : ENNReal) ^ (-rho)) ≤ 1 := by
    apply ENNReal.rpow_le_one
    · exact_mod_cast diam.2.2
    · linarith
  calc
    ((diam.1 : ENNReal) ^ (-rho)) * localMultiplicativeEntropy E c diam.1 δ ≤
        1 * localMultiplicativeEntropy E c diam.1 δ := by
      gcongr
    _ = (localMultiplicativeEntropy E c diam.1 δ : ENNReal) := by simp
    _ ≤ unitMultiplicativeEntropy E δ :=
      by
        exact_mod_cast
          localMultiplicativeEntropy_le_unitMultiplicativeEntropy E c diam.2.2

/-- For a nonpositive penalty parameter, the Legendre--Assouad exponent is
at most the unit-window Minkowski exponent. -/
theorem multiplicativeLegendreAssouadExponent_le_multiplicativeMinkowskiExponent_of_nonpos
    (E : Set ℝ) {rho : ℝ} (hrho : rho ≤ 0) :
    multiplicativeLegendreAssouadExponent E rho ≤ multiplicativeMinkowskiExponent E := by
  change Filter.limsup
      (fun δ : ℝ≥0 => entropyLogQuotient
        (multiplicativeLegendreAssouadProfile E rho δ) δ)
      (𝓝[>] (0 : ℝ≥0)) ≤
    Filter.limsup
      (fun δ : ℝ≥0 => entropyLogQuotient (unitMultiplicativeEntropy E δ) δ)
      (𝓝[>] (0 : ℝ≥0))
  rw [← Filter.blimsup_true, ← Filter.blimsup_true]
  apply Filter.mono_blimsup'
  have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), δ ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [hsmall] with δ hδ _
  exact entropyLogQuotient_mono hδ.1 hδ.2
    (multiplicativeLegendreAssouadProfile_le_unit_of_nonpos E hrho δ)

/-- The nonpositive part of the Legendre--Assouad exponent is exactly the
Minkowski exponent. -/
theorem multiplicativeLegendreAssouadExponent_eq_multiplicativeMinkowskiExponent_of_nonpos
    (E : Set ℝ) {rho : ℝ} (hrho : rho ≤ 0) :
    multiplicativeLegendreAssouadExponent E rho = multiplicativeMinkowskiExponent E := by
  apply le_antisymm
  · exact multiplicativeLegendreAssouadExponent_le_multiplicativeMinkowskiExponent_of_nonpos
      E hrho
  · exact multiplicativeMinkowskiExponent_le_multiplicativeLegendreAssouadExponent E rho

end

end LeanSpherical.HarmonicAnalysis
