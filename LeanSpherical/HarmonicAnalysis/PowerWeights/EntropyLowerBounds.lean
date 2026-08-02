/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.EntropyComparison

/-!
# Elementary lower bounds for the Legendre--Assouad exponent

For a nonempty radius set, the local profile can always use the interval of
diameter equal to the observing scale around one radius. This gives the
basic lower bound rho ≤ nu-sharp rho; together with the unit-window term it
is the max (rho, beta) lower bound used in the parameter geometry.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

/-- A nonempty positive radius set contributes at least one cell in the
diameter-δ interval centered at one of its radii. -/
theorem one_le_localMultiplicativeEntropy_self_of_nonempty_of_subset_Ioi
    {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi (0 : ℝ))
    (δ : ℝ≥0) :
    ∃ c : PositiveRadius, 1 ≤ localMultiplicativeEntropy E c δ δ := by
  rcases hE with ⟨r, hr⟩
  let c : PositiveRadius := ⟨r, hEpos hr⟩
  refine ⟨c, ?_⟩
  apply Order.one_le_iff_ne_zero.mpr
  apply ne_of_gt
  unfold localMultiplicativeEntropy multiplicativeEntropy
  apply Metric.externalCoveringNumber_pos_iff.mpr
  refine ⟨logRadius c, c, ?_, rfl⟩
  constructor
  · exact hr
  · constructor
    · exact c.2
    · change |logRadius c - logRadius c| ≤ (δ : ℝ) / 2
      rw [sub_self, abs_zero]
      positivity

/-- At a scale below one, the local profile dominates the pure interval
penalty arising from the interval of diameter equal to that scale. -/
theorem inv_rpow_le_multiplicativeLegendreAssouadProfile_of_nonempty_of_subset_Ioi
    {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi (0 : ℝ))
    (rho : ℝ) {δ : ℝ≥0} (hδ : δ ≤ 1) :
    ((δ : ENNReal) ^ (-rho)) ≤
      multiplicativeLegendreAssouadProfile E rho δ := by
  obtain ⟨c, hlocal⟩ :=
    one_le_localMultiplicativeEntropy_self_of_nonempty_of_subset_Ioi hE hEpos δ
  let diam : Icc δ 1 := ⟨δ, le_rfl, hδ⟩
  calc
    ((δ : ENNReal) ^ (-rho)) =
        ((diam.1 : ENNReal) ^ (-rho)) * 1 := by simp [diam]
    _ ≤ ((diam.1 : ENNReal) ^ (-rho)) *
        localMultiplicativeEntropy E c diam.1 δ := by
      gcongr
      exact_mod_cast hlocal
    _ ≤ multiplicativeLegendreAssouadProfile E rho δ := by
      unfold multiplicativeLegendreAssouadProfile
      exact le_iSup_of_le c (le_iSup (fun d : Icc δ 1 =>
        ((d.1 : ENNReal) ^ (-rho)) *
          localMultiplicativeEntropy E c d.1 δ) diam)

/-- The entropy logarithmic quotient of a pure inverse scale power is its
exponent. -/
theorem entropyLogQuotient_inv_rpow
    {rho : ℝ} {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    entropyLogQuotient ((δ : ENNReal) ^ (-rho)) δ = rho := by
  unfold entropyLogQuotient
  rw [ENNReal.log_rpow]
  have hδreal0 : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hδreal1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hlogpos : 0 < Real.log ((δ : ℝ)⁻¹) := by
    apply Real.log_pos
    exact (one_lt_inv₀ hδreal0).mpr hδreal1
  have hden : (Real.log ((δ : ℝ)⁻¹) : EReal) =
      - ENNReal.log (δ : ENNReal) := by
    calc
      (Real.log ((δ : ℝ)⁻¹) : EReal) =
          ENNReal.log ((δ : ENNReal)⁻¹) := by
        rw [ENNReal.log_inv, ENNReal.log_of_nnreal hδ0.ne', Real.log_inv]
        norm_cast
      _ = - ENNReal.log (δ : ENNReal) := ENNReal.log_inv
  have hDpos : (0 : EReal) < (Real.log ((δ : ℝ)⁻¹) : EReal) := by
    exact_mod_cast hlogpos
  have hDbot : (Real.log ((δ : ℝ)⁻¹) : EReal) ≠ ⊥ :=
    EReal.coe_ne_bot _
  have hDtop : (Real.log ((δ : ℝ)⁻¹) : EReal) ≠ ⊤ :=
    EReal.coe_ne_top _
  have hDzero : (Real.log ((δ : ℝ)⁻¹) : EReal) ≠ 0 :=
    ne_of_gt hDpos
  have hlog : ENNReal.log (δ : ENNReal) =
      - (Real.log ((δ : ℝ)⁻¹) : EReal) := by
    rw [hden]
    simp
  rw [hlog]
  rw [EReal.div_eq_iff hDbot hDtop hDzero]
  have hreal : (-rho) * (-Real.log ((δ : ℝ)⁻¹)) =
      rho * Real.log ((δ : ℝ)⁻¹) := by ring
  exact_mod_cast hreal

/-- The Legendre--Assouad exponent dominates its penalty parameter. -/
theorem le_multiplicativeLegendreAssouadExponent_of_nonempty_of_subset_Ioi
    {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi (0 : ℝ)) (rho : ℝ) :
    (rho : EReal) ≤ multiplicativeLegendreAssouadExponent E rho := by
  change (rho : EReal) ≤ Filter.limsup
    (fun δ : ℝ≥0 =>
      entropyLogQuotient (multiplicativeLegendreAssouadProfile E rho δ) δ)
    (𝓝[>] (0 : ℝ≥0))
  apply Filter.le_limsup_of_frequently_le'
  have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), δ ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  exact (hsmall.mono fun δ hδ =>
    calc
      (rho : EReal) =
          entropyLogQuotient ((δ : ENNReal) ^ (-rho)) δ :=
        (entropyLogQuotient_inv_rpow hδ.1 hδ.2).symm
      _ ≤ entropyLogQuotient
          (multiplicativeLegendreAssouadProfile E rho δ) δ :=
        entropyLogQuotient_mono hδ.1 hδ.2
          (inv_rpow_le_multiplicativeLegendreAssouadProfile_of_nonempty_of_subset_Ioi
            hE hEpos rho hδ.2.le)).frequently

/-- The two elementary lower bounds for the Legendre--Assouad exponent. -/
theorem max_multiplicativeMinkowskiExponent_rho_le_multiplicativeLegendreAssouadExponent
    {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi (0 : ℝ)) (rho : ℝ) :
    max (multiplicativeMinkowskiExponent E) (rho : EReal) ≤
      multiplicativeLegendreAssouadExponent E rho := by
  exact max_le
    (multiplicativeMinkowskiExponent_le_multiplicativeLegendreAssouadExponent E rho)
    (le_multiplicativeLegendreAssouadExponent_of_nonempty_of_subset_Ioi hE hEpos rho)

end

end LeanSpherical.HarmonicAnalysis
