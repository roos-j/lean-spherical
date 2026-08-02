/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.EntropyLowerBounds
import LeanSpherical.HarmonicAnalysis.PowerWeights.EntropyLimit

/-!
# Passing a uniform profile power bound to the Legendre--Assouad exponent

The lower tests produce a finite multiplicative constant in front of an
inverse scale power.  This file removes that harmless constant directly at
the level of the full local entropy profile.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

private theorem eventually_const_le_inv_rpow_profile
    (A : ℝ≥0∞) (hAtop : A ≠ (∞ : ℝ≥0∞)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      A ≤ (δ : ℝ≥0∞) ^ (-ε) := by
  let B : ℝ := A.toReal + 1
  have hreal : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), B < x ^ (-ε) :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : -ε < 0)).eventually
      (Filter.eventually_gt_atTop B)
  have hnnreal : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      B < (δ : ℝ) ^ (-ε) := by
    have hcoe : Filter.Tendsto (fun δ : ℝ≥0 => (δ : ℝ))
        (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
      change Filter.map (fun δ : ℝ≥0 => (δ : ℝ))
          (𝓝[>] (0 : ℝ≥0)) ≤ 𝓝[>] (0 : ℝ)
      rw [NNReal.map_coe_nhdsGT]
      simpa using (le_refl (𝓝[>] (0 : ℝ)))
    exact hcoe.eventually hreal
  have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), δ ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [hnnreal, hsmall] with δ hδ hδsmall
  have hδreal : 0 < (δ : ℝ) := by exact_mod_cast hδsmall.1
  have hle : A.toReal ≤ (δ : ℝ) ^ (-ε) := by
    calc
      A.toReal ≤ B := by dsimp only [B]; linarith
      _ ≤ (δ : ℝ) ^ (-ε) := hδ.le
  calc
    A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hAtop).symm
    _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε)) := ENNReal.ofReal_le_ofReal hle
    _ = (δ : ℝ≥0∞) ^ (-ε) := by
      rw [← ENNReal.ofReal_rpow_of_pos hδreal]
      simp

/-- A finite multiplicative constant in an inverse-power bound for the
Legendre--Assouad profile does not change its exponent. -/
theorem multiplicativeLegendreAssouadExponent_le_of_profile_power_bound
    {E : Set ℝ} {A : ℝ≥0∞} {rho s : ℝ} (hAtop : A ≠ (∞ : ℝ≥0∞))
    (hbound : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      multiplicativeLegendreAssouadProfile E rho δ ≤
        A * (δ : ℝ≥0∞) ^ (-s)) :
    multiplicativeLegendreAssouadExponent E rho ≤ (s : EReal) := by
  refine (EReal.le_of_forall_lt_iff_le
    (x := (s : EReal)) (y := multiplicativeLegendreAssouadExponent E rho)).mp ?_
  intro z hsz
  let ε : ℝ := z - s
  have hε : 0 < ε := by
    dsimp only [ε]
    exact sub_pos.mpr (EReal.coe_lt_coe_iff.mp hsz)
  have hconst := eventually_const_le_inv_rpow_profile A hAtop hε
  have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), δ ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  have hquotient : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      entropyLogQuotient (multiplicativeLegendreAssouadProfile E rho δ) δ ≤
        (z : EReal) := by
    filter_upwards [hbound, hconst, hsmall] with δ hδ hA hδsmall
    have hδzero : (δ : ℝ≥0∞) ≠ 0 := ne_of_gt (by exact_mod_cast hδsmall.1)
    have hδtop : (δ : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) := ENNReal.coe_ne_top
    have hpower : A * (δ : ℝ≥0∞) ^ (-s) ≤
        (δ : ℝ≥0∞) ^ (-(s + ε)) := by
      calc
        A * (δ : ℝ≥0∞) ^ (-s) ≤
            (δ : ℝ≥0∞) ^ (-ε) * (δ : ℝ≥0∞) ^ (-s) := by
              simpa only [mul_comm] using
                mul_le_mul_right hA ((δ : ℝ≥0∞) ^ (-s))
        _ = (δ : ℝ≥0∞) ^ (-(s + ε)) := by
          rw [← ENNReal.rpow_add (-ε) (-s) hδzero hδtop]
          congr 1
          ring
    have hN : multiplicativeLegendreAssouadProfile E rho δ ≤
        (δ : ℝ≥0∞) ^ (-(s + ε)) := hδ.trans hpower
    calc
      entropyLogQuotient (multiplicativeLegendreAssouadProfile E rho δ) δ ≤
          entropyLogQuotient ((δ : ℝ≥0∞) ^ (-(s + ε))) δ :=
        entropyLogQuotient_mono hδsmall.1 hδsmall.2 hN
      _ = ((s + ε : ℝ) : EReal) :=
        entropyLogQuotient_inv_rpow hδsmall.1 hδsmall.2
      _ = (z : EReal) := by
        congr 1
        dsimp only [ε]
        ring
  exact multiplicativeLegendreAssouadExponent_le_of_eventually_entropyLogQuotient_le
    hquotient

end

end LeanSpherical.HarmonicAnalysis
