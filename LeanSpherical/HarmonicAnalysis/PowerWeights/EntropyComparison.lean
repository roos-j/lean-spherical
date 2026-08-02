/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.Entropy
import Mathlib.Algebra.Order.Floor.Extended

/-!
# Elementary comparisons between the entropy exponents

The local Legendre--Assouad profile contains the unit-window profile as its
diameter-one term.  This is the parameter fact behind the inequality
`beta ≤ nu^sharp(rho)` used in the critical-exponent condition.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

/-- A nonempty positive radius set has a nonempty logarithmic image. -/
theorem logRadiusSet_nonempty_of_nonempty_of_subset_Ioi
    {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi (0 : ℝ)) :
    (logRadiusSet E).Nonempty := by
  rcases hE with ⟨r, hr⟩
  let rpos : PositiveRadius := ⟨r, hEpos hr⟩
  exact ⟨logRadius rpos, rpos, hr, rfl⟩

/-- Nonempty positive radius sets have at least one entropy cell at every
unit-window scale. -/
theorem one_le_unitMultiplicativeEntropy_of_nonempty_of_subset_Ioi
    {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi (0 : ℝ)) (δ : ℝ≥0) :
    1 ≤ unitMultiplicativeEntropy E δ := by
  rcases hE with ⟨r, hr⟩
  let c : PositiveRadius := ⟨r, hEpos hr⟩
  have hmem : c.1 ∈ E ∩ multiplicativeInterval c 1 := by
    constructor
    · exact hr
    · constructor
      · exact c.2
      · simp [logRadius]
  have hlog : (logRadiusSet (E ∩ multiplicativeInterval c 1)).Nonempty :=
    ⟨logRadius c, c, hmem, rfl⟩
  have hlocal : 1 ≤ localMultiplicativeEntropy E c 1 δ := by
    apply Order.one_le_iff_ne_zero.mpr
    exact ne_of_gt (by
      unfold localMultiplicativeEntropy multiplicativeEntropy
      exact Metric.externalCoveringNumber_pos_iff.mpr hlog)
  exact hlocal.trans (le_iSup (fun c : PositiveRadius =>
    localMultiplicativeEntropy E c 1 δ) c)

/-- The logarithmic unit-window entropy quotient is nonnegative for a
nonempty positive radius set at every positive scale below one. -/
theorem entropyLogQuotient_unit_nonneg_of_nonempty_of_subset_Ioi
    {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi (0 : ℝ))
    {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ entropyLogQuotient (unitMultiplicativeEntropy E δ) δ := by
  unfold entropyLogQuotient
  have hone : (1 : ℝ≥0∞) ≤ (unitMultiplicativeEntropy E δ : ℝ≥0∞) :=
    by
      simpa using
        (ENat.toENNReal_mono
          (one_le_unitMultiplicativeEntropy_of_nonempty_of_subset_Ioi hE hEpos δ))
  have hlog : (0 : EReal) ≤ ENNReal.log (unitMultiplicativeEntropy E δ) := by
    calc
      (0 : EReal) = ENNReal.log 1 := ENNReal.log_one.symm
      _ ≤ ENNReal.log (unitMultiplicativeEntropy E δ) := ENNReal.log_le_log hone
  have hδreal0 : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hδreal1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hloginv : 0 < Real.log ((δ : ℝ)⁻¹) := by
    apply Real.log_pos
    exact (one_lt_inv₀ hδreal0).mpr hδreal1
  have hden : 0 ≤ (Real.log ((δ : ℝ)⁻¹) : EReal) := by
    exact_mod_cast hloginv.le
  exact EReal.div_nonneg hlog hden

/-- The multiplicative Minkowski exponent of a nonempty positive radius set
is nonnegative. -/
theorem multiplicativeMinkowskiExponent_nonneg_of_nonempty_of_subset_Ioi
    {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi (0 : ℝ)) :
    0 ≤ multiplicativeMinkowskiExponent E := by
  change 0 ≤ Filter.limsup
    (fun δ : ℝ≥0 => entropyLogQuotient (unitMultiplicativeEntropy E δ) δ)
    (𝓝[>] (0 : ℝ≥0))
  apply Filter.le_limsup_of_frequently_le'
  have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), δ ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  exact (hsmall.mono fun δ hδ =>
    entropyLogQuotient_unit_nonneg_of_nonempty_of_subset_Ioi hE hEpos hδ.1 hδ.2).frequently

/-- Each diameter-one local entropy term occurs in the Legendre--Assouad
profile. -/
theorem localMultiplicativeEntropy_unit_le_multiplicativeLegendreAssouadProfile
    (E : Set ℝ) (rho : ℝ) {δ : ℝ≥0} (hδ : δ ≤ 1) (c : PositiveRadius) :
    (localMultiplicativeEntropy E c 1 δ : ℝ≥0∞) ≤
      multiplicativeLegendreAssouadProfile E rho δ := by
  unfold multiplicativeLegendreAssouadProfile
  let diam : Icc δ 1 := ⟨1, hδ, le_rfl⟩
  have hterm := le_iSup
    (fun diam : Icc δ 1 =>
      ((diam.1 : ℝ≥0) : ℝ≥0∞) ^ (-rho) *
        localMultiplicativeEntropy E c diam.1 δ) diam
  calc
    (localMultiplicativeEntropy E c 1 δ : ℝ≥0∞) =
        ((diam.1 : ℝ≥0) : ℝ≥0∞) ^ (-rho) *
          localMultiplicativeEntropy E c diam.1 δ := by simp [diam]
    _ ≤ ⨆ diam : Icc δ 1,
        ((diam.1 : ℝ≥0) : ℝ≥0∞) ^ (-rho) *
          localMultiplicativeEntropy E c diam.1 δ := hterm
    _ ≤ ⨆ c : PositiveRadius, ⨆ diam : Icc δ 1,
        ((diam.1 : ℝ≥0) : ℝ≥0∞) ^ (-rho) *
          localMultiplicativeEntropy E c diam.1 δ :=
      le_iSup (fun c : PositiveRadius => ⨆ diam : Icc δ 1,
        ((diam.1 : ℝ≥0) : ℝ≥0∞) ^ (-rho) *
          localMultiplicativeEntropy E c diam.1 δ) c

/-- The diameter-one terms give the full unit-window entropy profile. -/
theorem unitMultiplicativeEntropy_le_multiplicativeLegendreAssouadProfile
    (E : Set ℝ) (rho : ℝ) {δ : ℝ≥0} (hδ : δ ≤ 1) :
    (unitMultiplicativeEntropy E δ : ℝ≥0∞) ≤
      multiplicativeLegendreAssouadProfile E rho δ := by
  unfold unitMultiplicativeEntropy
  rw [ENat.toENNReal_iSup]
  apply iSup_le
  intro c
  exact localMultiplicativeEntropy_unit_le_multiplicativeLegendreAssouadProfile
    E rho hδ c

/-- At a positive scale below one, logarithmic entropy quotients are
monotone in the underlying entropy number. -/
theorem entropyLogQuotient_mono
    {N M : ℝ≥0∞} {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hNM : N ≤ M) :
    entropyLogQuotient N δ ≤ entropyLogQuotient M δ := by
  unfold entropyLogQuotient
  have hδreal0 : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hδreal1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hloginv : 0 < Real.log ((δ : ℝ)⁻¹) := by
    apply Real.log_pos
    exact (one_lt_inv₀ hδreal0).mpr hδreal1
  have hden : 0 ≤ (Real.log ((δ : ℝ)⁻¹) : EReal) := by
    exact_mod_cast hloginv.le
  exact EReal.div_le_div_right_of_nonneg hden (ENNReal.log_le_log hNM)

/-- The upper Minkowski exponent is no larger than every
Legendre--Assouad exponent. -/
theorem multiplicativeMinkowskiExponent_le_multiplicativeLegendreAssouadExponent
    (E : Set ℝ) (rho : ℝ) :
    multiplicativeMinkowskiExponent E ≤
      multiplicativeLegendreAssouadExponent E rho := by
  change Filter.limsup
      (fun δ : ℝ≥0 => entropyLogQuotient (unitMultiplicativeEntropy E δ) δ)
      (𝓝[>] (0 : ℝ≥0)) ≤
    Filter.limsup
      (fun δ : ℝ≥0 => entropyLogQuotient
        (multiplicativeLegendreAssouadProfile E rho δ) δ)
      (𝓝[>] (0 : ℝ≥0))
  rw [← Filter.blimsup_true, ← Filter.blimsup_true]
  apply Filter.mono_blimsup'
  have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), δ ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [hsmall] with δ hδ _
  exact entropyLogQuotient_mono hδ.1 hδ.2
    (unitMultiplicativeEntropy_le_multiplicativeLegendreAssouadProfile E rho hδ.2.le)

/-- Increasing the interval penalty can only increase the finite-scale
Legendre--Assouad profile. -/
theorem multiplicativeLegendreAssouadProfile_mono_rho
    (E : Set ℝ) {rho sigma : ℝ} (h : rho ≤ sigma) (δ : ℝ≥0) :
    multiplicativeLegendreAssouadProfile E rho δ ≤
      multiplicativeLegendreAssouadProfile E sigma δ := by
  unfold multiplicativeLegendreAssouadProfile
  apply iSup_mono
  intro c
  apply iSup_mono
  intro diam
  simpa only [mul_comm] using
    (mul_le_mul_right
      (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast diam.2.2) (by linarith))
      (localMultiplicativeEntropy E c diam.1 δ : ℝ≥0∞))

/-- The Legendre--Assouad exponent is nondecreasing in its penalty
parameter. -/
theorem multiplicativeLegendreAssouadExponent_mono
    (E : Set ℝ) {rho sigma : ℝ} (h : rho ≤ sigma) :
    multiplicativeLegendreAssouadExponent E rho ≤
      multiplicativeLegendreAssouadExponent E sigma := by
  change Filter.limsup
      (fun δ : ℝ≥0 => entropyLogQuotient
        (multiplicativeLegendreAssouadProfile E rho δ) δ)
      (𝓝[>] (0 : ℝ≥0)) ≤
    Filter.limsup
      (fun δ : ℝ≥0 => entropyLogQuotient
        (multiplicativeLegendreAssouadProfile E sigma δ) δ)
      (𝓝[>] (0 : ℝ≥0))
  rw [← Filter.blimsup_true, ← Filter.blimsup_true]
  apply Filter.mono_blimsup'
  have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), δ ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [hsmall] with δ hδ _
  exact entropyLogQuotient_mono hδ.1 hδ.2
    (multiplicativeLegendreAssouadProfile_mono_rho E h δ)

end

end LeanSpherical.HarmonicAnalysis
