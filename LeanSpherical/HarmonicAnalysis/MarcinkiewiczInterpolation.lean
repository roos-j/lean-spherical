/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Marcinkiewicz interpolation

This file formalizes the truncation, layer-cake, Tonelli, and power-tail
argument giving a concrete strong `(1,1)`/`(2,2)` to `Lᵖ` interpolation bound.
-/

open Filter MeasureTheory Set ENNReal

noncomputable section

namespace LeanSpherical.HarmonicAnalysis

/-- Multiplication by a positive scale transports Lebesgue measure on the
positive half-line by the reciprocal scale. -/
theorem map_restrict_Ioi_mul_pos
    (s : ℝ) (hs : 0 < s) :
    Measure.map (fun t : ℝ => s * t) (volume.restrict (Ioi (0 : ℝ))) =
      ENNReal.ofReal s⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
  calc
    Measure.map (fun t : ℝ => s * t) (volume.restrict (Ioi (0 : ℝ))) =
        (Measure.map (fun t : ℝ => s * t) volume).restrict (Ioi (0 : ℝ)) := by
      rw [Measure.restrict_map (μ := volume) (measurable_const_mul s) measurableSet_Ioi]
      rw [preimage_const_mul_Ioi₀ (0 : ℝ) hs, zero_div]
    _ = (ENNReal.ofReal |s⁻¹| • volume).restrict (Ioi (0 : ℝ)) := by
      rw [Real.map_volume_mul_left hs.ne']
    _ = ENNReal.ofReal s⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
      rw [Measure.restrict_smul, abs_of_pos (inv_pos.mpr hs)]

/-- Change variables by a positive dilation on the positive half-line. -/
theorem lintegral_Ioi_comp_mul
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) (s : ℝ) (hs : 0 < s) :
    (∫⁻ t in Ioi (0 : ℝ), G (s * t)) =
      ENNReal.ofReal s⁻¹ * ∫⁻ r in Ioi (0 : ℝ), G r := by
  have hmap := map_restrict_Ioi_mul_pos s hs
  calc
    (∫⁻ t in Ioi (0 : ℝ), G (s * t)) =
        ∫⁻ t, G ((fun t : ℝ => s * t) t) ∂(volume.restrict (Ioi (0 : ℝ))) := rfl
    _ = ∫⁻ r, G r ∂Measure.map (fun t : ℝ => s * t) (volume.restrict (Ioi (0 : ℝ))) := by
      rw [lintegral_map hG (measurable_const_mul s)]
    _ = ∫⁻ r, G r ∂(ENNReal.ofReal s⁻¹ • volume.restrict (Ioi (0 : ℝ))) := by
      rw [hmap]
    _ = ENNReal.ofReal s⁻¹ * ∫⁻ r in Ioi (0 : ℝ), G r := by
      rw [lintegral_smul_measure, smul_eq_mul]

/-- The weighted positive-half-line change of variables used by a scaled
amplitude decomposition. -/
theorem lintegral_Ioi_comp_mul_weight
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) (s : ℝ) (hs : 0 < s) (q : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), G (s * t) * (ENNReal.ofReal t) ^ q) =
      (ENNReal.ofReal s) ^ (-q) *
        (ENNReal.ofReal s⁻¹ *
          ∫⁻ r in Ioi (0 : ℝ), G r * (ENNReal.ofReal r) ^ q) := by
  have hpoint (t : ℝ) (ht : 0 < t) :
      G (s * t) * (ENNReal.ofReal t) ^ q =
        (ENNReal.ofReal s) ^ (-q) *
          (G (s * t) * (ENNReal.ofReal (s * t)) ^ q) := by
    rw [ENNReal.ofReal_rpow_of_pos ht,
      ENNReal.ofReal_rpow_of_pos (mul_pos hs ht),
      ENNReal.ofReal_rpow_of_pos hs]
    have hpow : t ^ q = s ^ (-q) * (s * t) ^ q := by
      rw [Real.mul_rpow hs.le ht.le, Real.rpow_neg hs.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hs q)]
    rw [hpow]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
    ac_rfl
  let H : ℝ → ℝ≥0∞ := fun r => G r * (ENNReal.ofReal r) ^ q
  have hH : Measurable H :=
    hG.mul (ENNReal.continuous_rpow_const.measurable.comp ENNReal.continuous_ofReal.measurable)
  calc
    (∫⁻ t in Ioi (0 : ℝ), G (s * t) * (ENNReal.ofReal t) ^ q) =
        ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal s) ^ (-q) * H (s * t) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint t ht
    _ = (ENNReal.ofReal s) ^ (-q) *
        ∫⁻ t in Ioi (0 : ℝ), H (s * t) := by
      exact lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
        ((ENNReal.ofReal s) ^ (-q)) (hH.comp (measurable_const_mul s))
    _ = (ENNReal.ofReal s) ^ (-q) *
        (ENNReal.ofReal s⁻¹ * ∫⁻ r in Ioi (0 : ℝ), H r) := by
      rw [lintegral_Ioi_comp_mul H hH s hs]

theorem scale_weight_low_exponent
    (s p : ℝ) (hs : 0 < s) :
    (ENNReal.ofReal s) ^ (-(p - 3)) * ENNReal.ofReal s⁻¹ =
      (ENNReal.ofReal s) ^ (2 - p) := by
  rw [ENNReal.ofReal_inv_of_pos hs, ← ENNReal.rpow_neg_one]
  rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hs) ENNReal.ofReal_ne_top]
  congr 1
  ring

theorem scale_weight_high_exponent
    (s p : ℝ) (hs : 0 < s) :
    (ENNReal.ofReal s) ^ (-(p - 2)) * ENNReal.ofReal s⁻¹ =
      (ENNReal.ofReal s) ^ (1 - p) := by
  rw [ENNReal.ofReal_inv_of_pos hs, ← ENNReal.rpow_neg_one]
  rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hs) ENNReal.ofReal_ne_top]
  congr 1
  ring

/-- The low-side weighted tail under a positive threshold dilation. -/
theorem lintegral_Ioi_comp_mul_low_weight
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) (s : ℝ) (hs : 0 < s) (p : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), G (s * t) * (ENNReal.ofReal t) ^ (p - 3)) =
      (ENNReal.ofReal s) ^ (2 - p) *
        ∫⁻ r in Ioi (0 : ℝ), G r * (ENNReal.ofReal r) ^ (p - 3) := by
  rw [lintegral_Ioi_comp_mul_weight G hG s hs (p - 3)]
  rw [← mul_assoc, scale_weight_low_exponent s p hs]

/-- The high-side weighted tail under a positive threshold dilation. -/
theorem lintegral_Ioi_comp_mul_high_weight
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) (s : ℝ) (hs : 0 < s) (p : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), G (s * t) * (ENNReal.ofReal t) ^ (p - 2)) =
      (ENNReal.ofReal s) ^ (1 - p) *
        ∫⁻ r in Ioi (0 : ℝ), G r * (ENNReal.ofReal r) ^ (p - 2) := by
  rw [lintegral_Ioi_comp_mul_weight G hG s hs (p - 2)]
  rw [← mul_assoc, scale_weight_high_exponent s p hs]

theorem lintegral_ofReal_rpow_Ioc_zero
    {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) :
    (∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal (t ^ (p - 2))) =
      ENNReal.ofReal (c ^ (p - 1) / (p - 1)) := by
  have hpow : -1 < p - 2 := by linarith
  have hinterval : IntervalIntegrable (fun t : ℝ => t ^ (p - 2)) volume 0 c :=
    intervalIntegral.intervalIntegrable_rpow' hpow
  have hIcc : IntegrableOn (fun t : ℝ => t ^ (p - 2)) (Icc 0 c) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hc).mp hinterval
  have hIcc' : Integrable (fun t : ℝ => t ^ (p - 2)) (volume.restrict (Icc 0 c)) := hIcc
  have hIoc : Integrable (fun t : ℝ => t ^ (p - 2)) (volume.restrict (Ioc 0 c)) :=
    hIcc'.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 c)] (fun t : ℝ => t ^ (p - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hIoc hnonneg]
  rw [show (∫ t, t ^ (p - 2) ∂volume.restrict (Ioc 0 c)) =
      ∫ t in Ioc (0 : ℝ) c, t ^ (p - 2) by rfl]
  rw [← intervalIntegral.integral_of_le hc]
  rw [integral_rpow (Or.inl hpow)]
  have hpone : 0 < p - 1 := by linarith
  rw [show p - 2 + 1 = p - 1 by ring]
  rw [Real.zero_rpow hpone.ne']
  simp

theorem lintegral_ofReal_rpow_Ioi
    {p c : ℝ} (hp : p < 2) (hc : 0 < c) :
    (∫⁻ t in Ioi c, ENNReal.ofReal (t ^ (p - 3))) =
      ENNReal.ofReal (c ^ (p - 2) / (2 - p)) := by
  have hpow : p - 3 < -1 := by linarith
  have hIoi : Integrable (fun t : ℝ => t ^ (p - 3)) (volume.restrict (Ioi c)) :=
    integrableOn_Ioi_rpow_of_lt hpow hc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi c)] (fun t : ℝ => t ^ (p - 3)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hc.trans ht).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hIoi hnonneg]
  rw [integral_Ioi_rpow_of_lt hpow hc]
  rw [show p - 3 + 1 = p - 2 by ring]
  have hdenom : p - 2 ≠ 0 := by linarith
  have hdenom' : 2 - p ≠ 0 := by linarith
  congr 1
  field_simp [hdenom, hdenom']
  ring

theorem lintegral_rpow_Ioc_eq
    {p u : ℝ} (hp : 1 < p) (hu : 0 ≤ u) :
    (∫⁻ t in Ioc (0 : ℝ) u, (ENNReal.ofReal t) ^ (p - 2)) =
      ENNReal.ofReal (u ^ (p - 1) / (p - 1)) := by
  rw [show (∫⁻ t in Ioc (0 : ℝ) u, (ENNReal.ofReal t) ^ (p - 2)) =
      ∫⁻ t in Ioc (0 : ℝ) u, ENNReal.ofReal (t ^ (p - 2)) by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ENNReal.ofReal_rpow_of_pos ht.1]
  exact lintegral_ofReal_rpow_Ioc_zero hp hu

theorem lintegral_rpow_Ioi_eq
    {p u : ℝ} (hp : p < 2) (hu : 0 < u) :
    (∫⁻ t in Ioi u, (ENNReal.ofReal t) ^ (p - 3)) =
      ENNReal.ofReal (u ^ (p - 2) / (2 - p)) := by
  rw [show (∫⁻ t in Ioi u, (ENNReal.ofReal t) ^ (p - 3)) =
      ∫⁻ t in Ioi u, ENNReal.ofReal (t ^ (p - 3)) by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ENNReal.ofReal_rpow_of_pos (hu.trans ht)]
  exact lintegral_ofReal_rpow_Ioi hp hu

theorem ofReal_mul_rpow_div_eq
    {u p : ℝ} (hu : 0 ≤ u) (hp : 1 < p) :
    ENNReal.ofReal u * ENNReal.ofReal (u ^ (p - 1) / (p - 1)) =
      (ENNReal.ofReal (p - 1))⁻¹ * (ENNReal.ofReal u) ^ p := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp.le
  have hppos : 0 < p := lt_trans (by norm_num) hp
  have hpone : 0 < p - 1 := by linarith
  have hmul : u * u ^ (p - 1) = u ^ p := by
    rcases hu.eq_or_lt with rfl | hu
    · simp [Real.zero_rpow hppos.ne']
    · calc
        u * u ^ (p - 1) = u ^ (1 : ℝ) * u ^ (p - 1) := by rw [Real.rpow_one]
        _ = u ^ ((1 : ℝ) + (p - 1)) := (Real.rpow_add hu _ _).symm
        _ = u ^ p := by congr 1; ring
  have hmuldiv : u * (u ^ (p - 1) / (p - 1)) = u ^ p / (p - 1) := by
    rw [← mul_div_assoc, hmul]
  rw [← ENNReal.ofReal_mul hu, hmuldiv, ENNReal.ofReal_div_of_pos hpone]
  rw [← ENNReal.ofReal_rpow_of_nonneg hu hp0]
  simp [div_eq_mul_inv, mul_comm]

theorem ofReal_sq_mul_rpow_div_eq
    {u p : ℝ} (hu : 0 < u) (hp1 : 1 < p) (hp : p < 2) :
    ENNReal.ofReal (u ^ (2 : ℕ)) * ENNReal.ofReal (u ^ (p - 2) / (2 - p)) =
      (ENNReal.ofReal (2 - p))⁻¹ * (ENNReal.ofReal u) ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hptwo : 0 < 2 - p := by linarith
  have hsq : u ^ (2 : ℕ) = u ^ (2 : ℝ) := by
    exact (Real.rpow_natCast u 2).symm
  have hmul : u ^ (2 : ℕ) * u ^ (p - 2) = u ^ p := by
    rw [hsq, ← Real.rpow_add hu]
    congr 1; ring
  have hmuldiv : u ^ (2 : ℕ) * (u ^ (p - 2) / (2 - p)) = u ^ p / (2 - p) := by
    rw [← mul_div_assoc, hmul]
  rw [← ENNReal.ofReal_mul (sq_nonneg u), hmuldiv,
    ENNReal.ofReal_div_of_pos hptwo]
  rw [← ENNReal.ofReal_rpow_of_nonneg hu.le hp0]
  simp [div_eq_mul_inv, mul_comm]

theorem ofReal_mul_lintegral_rpow_Ioc_eq
    {u p : ℝ} (hu : 0 ≤ u) (hp : 1 < p) :
    ENNReal.ofReal u * (∫⁻ t in Ioc (0 : ℝ) u, (ENNReal.ofReal t) ^ (p - 2)) =
      (ENNReal.ofReal (p - 1))⁻¹ * (ENNReal.ofReal u) ^ p := by
  rw [lintegral_rpow_Ioc_eq hp hu]
  exact ofReal_mul_rpow_div_eq hu hp

theorem ofReal_sq_mul_lintegral_rpow_Ioi_eq
    {u p : ℝ} (hu : 0 ≤ u) (hp1 : 1 < p) (hp : p < 2) :
    ENNReal.ofReal (u ^ (2 : ℕ)) * (∫⁻ t in Ioi u, (ENNReal.ofReal t) ^ (p - 3)) =
      (ENNReal.ofReal (2 - p))⁻¹ * (ENNReal.ofReal u) ^ p := by
  rcases hu.eq_or_lt with rfl | hu
  · have hppos : 0 < p := lt_trans (by norm_num) hp1
    simp [ENNReal.zero_rpow_of_pos hppos]
  · rw [lintegral_rpow_Ioi_eq hp hu]
    exact ofReal_sq_mul_rpow_div_eq hu hp1 hp

/-- The cubic high-amplitude power tail used by the rational splitting
argument. -/
theorem ofReal_cube_mul_rpow_div_eq
    {u p : ℝ} (hu : 0 < u) (hp1 : 1 < p) (hp : p < 2) :
    ENNReal.ofReal (u ^ (3 : ℕ)) * ENNReal.ofReal (u ^ (p - 3) / (3 - p)) =
      (ENNReal.ofReal (3 - p))⁻¹ * (ENNReal.ofReal u) ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hpthree : 0 < 3 - p := by linarith
  have hcube : u ^ (3 : ℕ) = u ^ (3 : ℝ) := by
    exact (Real.rpow_natCast u 3).symm
  have hmul : u ^ (3 : ℕ) * u ^ (p - 3) = u ^ p := by
    rw [hcube, ← Real.rpow_add hu]
    congr 1
    ring_nf
  have hmuldiv : u ^ (3 : ℕ) * (u ^ (p - 3) / (3 - p)) = u ^ p / (3 - p) := by
    rw [← mul_div_assoc, hmul]
  rw [← ENNReal.ofReal_mul (pow_nonneg hu.le _), hmuldiv,
    ENNReal.ofReal_div_of_pos hpthree]
  rw [← ENNReal.ofReal_rpow_of_nonneg hu.le hp0]
  simp [div_eq_mul_inv, mul_comm]

theorem ofReal_cube_mul_lintegral_rpow_Ioi_eq
    {u p : ℝ} (hu : 0 ≤ u) (hp1 : 1 < p) (hp : p < 2) :
    ENNReal.ofReal (u ^ (3 : ℕ)) *
      (∫⁻ t in Ioi u, (ENNReal.ofReal t) ^ (p - 4)) =
      (ENNReal.ofReal (3 - p))⁻¹ * (ENNReal.ofReal u) ^ p := by
  rcases hu.eq_or_lt with rfl | hu
  · have hppos : 0 < p := lt_trans (by norm_num) hp1
    simp [ENNReal.zero_rpow_of_pos hppos]
  · rw [show (∫⁻ t in Ioi u, (ENNReal.ofReal t) ^ (p - 4)) =
      ∫⁻ t in Ioi u, (ENNReal.ofReal t) ^ ((p - 1) - 3) by
        congr 1
        funext t
        congr 1
        ring_nf]
    rw [lintegral_rpow_Ioi_eq (p := p - 1) (by linarith) hu]
    convert ofReal_cube_mul_rpow_div_eq hu hp1 hp using 1
    all_goals ring_nf

theorem lintegral_ofReal_mul_lintegral_rpow_Ioc_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : α → ℝ) (hu : Measurable u) {p : ℝ}
    (hu_nonneg : ∀ x, 0 ≤ u x) (hp : 1 < p) :
    (∫⁻ x, ENNReal.ofReal (u x) *
      (∫⁻ t in Ioc (0 : ℝ) (u x), (ENNReal.ofReal t) ^ (p - 2)) ∂μ) =
      (ENNReal.ofReal (p - 1))⁻¹ * (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
  rw [show (∫⁻ x, ENNReal.ofReal (u x) *
      (∫⁻ t in Ioc (0 : ℝ) (u x), (ENNReal.ofReal t) ^ (p - 2)) ∂μ) =
      ∫⁻ x, (ENNReal.ofReal (p - 1))⁻¹ * (ENNReal.ofReal (u x)) ^ p ∂μ by
    apply lintegral_congr
    intro x
    exact ofReal_mul_lintegral_rpow_Ioc_eq (hu_nonneg x) hp]
  exact lintegral_const_mul _
    (ENNReal.continuous_rpow_const.measurable.comp hu.ennreal_ofReal)

theorem lintegral_ofReal_sq_mul_lintegral_rpow_Ioi_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : α → ℝ) (hu : Measurable u) {p : ℝ}
    (hu_nonneg : ∀ x, 0 ≤ u x) (hp1 : 1 < p) (hp : p < 2) :
    (∫⁻ x, ENNReal.ofReal ((u x) ^ (2 : ℕ)) *
      (∫⁻ t in Ioi (u x), (ENNReal.ofReal t) ^ (p - 3)) ∂μ) =
      (ENNReal.ofReal (2 - p))⁻¹ * (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
  rw [show (∫⁻ x, ENNReal.ofReal ((u x) ^ (2 : ℕ)) *
      (∫⁻ t in Ioi (u x), (ENNReal.ofReal t) ^ (p - 3)) ∂μ) =
      ∫⁻ x, (ENNReal.ofReal (2 - p))⁻¹ * (ENNReal.ofReal (u x)) ^ p ∂μ by
    apply lintegral_congr
    intro x
    exact ofReal_sq_mul_lintegral_rpow_Ioi_eq (hu_nonneg x) hp1 hp]
  exact lintegral_const_mul _
    (ENNReal.continuous_rpow_const.measurable.comp hu.ennreal_ofReal)

theorem lintegral_swap_indicator_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (v : α → ℝ≥0∞) (hv : Measurable v)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ t in Ioi (0 : ℝ),
      w t * ∫⁻ x in {x | t ≤ u x}, v x ∂μ) =
      (∫⁻ x, v x * (∫⁻ t in Ioc (0 : ℝ) (u x), w t) ∂μ) := by
  let S : Set (ℝ × α) := {q | q.1 ≤ u q.2}
  have hS : MeasurableSet S := by
    exact measurableSet_le measurable_fst (hu.comp measurable_snd)
  let F : ℝ → α → ℝ≥0∞ := fun t x =>
    S.indicator (fun q : ℝ × α => w q.1 * v q.2) (t, x)
  have hF : Measurable (Function.uncurry F) := by
    change Measurable (S.indicator (fun q : ℝ × α => w q.1 * v q.2))
    exact (hw.comp measurable_fst).mul (hv.comp measurable_snd) |>.indicator hS
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ))) (ν := μ)
    hF.aemeasurable
  have hleft : (∫⁻ t in Ioi (0 : ℝ), w t * ∫⁻ x in {x | t ≤ u x}, v x ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, F t x ∂μ := by
    apply lintegral_congr
    intro t
    have hvind : Measurable ({x | t ≤ u x}.indicator v) :=
      hv.indicator (measurableSet_le measurable_const hu)
    rw [← lintegral_indicator (measurableSet_le measurable_const hu)]
    rw [← lintegral_const_mul (w t) hvind]
    apply lintegral_congr
    intro x
    simp only [F, S, Set.indicator_apply]
    by_cases hx : t ≤ u x <;> simp [hx]
  rw [hleft, hswap]
  apply lintegral_congr
  intro x
  change (∫⁻ t in Ioi (0 : ℝ), F t x) = v x * ∫⁻ t in Ioc (0 : ℝ) (u x), w t
  have hFx : (fun t : ℝ => F t x) =
      {t | t ≤ u x}.indicator (fun t => w t * v x) := by
    funext t
    simp only [F, S, Set.indicator_apply]
    by_cases ht : t ≤ u x <;> simp [ht]
  rw [hFx]
  change (∫⁻ t, (Iic (u x)).indicator (fun t => w t * v x) t ∂(volume.restrict (Ioi (0 : ℝ)))) = _
  rw [lintegral_indicator measurableSet_Iic]
  rw [Measure.restrict_restrict measurableSet_Iic, inter_comm, Ioi_inter_Iic]
  rw [show (fun t : ℝ => w t * v x) = fun t => v x * w t by
    funext t
    exact mul_comm _ _]
  rw [lintegral_const_mul (v x) hw]

theorem lintegral_swap_indicator_lt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (v : α → ℝ≥0∞) (hv : Measurable v)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ t in Ioi (0 : ℝ),
      w t * ∫⁻ x in {x | u x < t}, v x ∂μ) =
      (∫⁻ x, v x * (∫⁻ t in Ioi (u x), w t) ∂μ) := by
  let S : Set (ℝ × α) := {q | u q.2 < q.1}
  have hS : MeasurableSet S := by
    exact measurableSet_lt (hu.comp measurable_snd) measurable_fst
  let F : ℝ → α → ℝ≥0∞ := fun t x =>
    S.indicator (fun q : ℝ × α => w q.1 * v q.2) (t, x)
  have hF : Measurable (Function.uncurry F) := by
    change Measurable (S.indicator (fun q : ℝ × α => w q.1 * v q.2))
    exact (hw.comp measurable_fst).mul (hv.comp measurable_snd) |>.indicator hS
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ))) (ν := μ)
    hF.aemeasurable
  have hleft : (∫⁻ t in Ioi (0 : ℝ), w t * ∫⁻ x in {x | u x < t}, v x ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, F t x ∂μ := by
    apply lintegral_congr
    intro t
    have hvind : Measurable ({x | u x < t}.indicator v) :=
      hv.indicator (measurableSet_lt hu measurable_const)
    rw [← lintegral_indicator (measurableSet_lt hu measurable_const)]
    rw [← lintegral_const_mul (w t) hvind]
    apply lintegral_congr
    intro x
    simp only [F, S, Set.indicator_apply]
    by_cases hx : u x < t <;> simp [hx]
  rw [hleft, hswap]
  apply lintegral_congr
  intro x
  change (∫⁻ t in Ioi (0 : ℝ), F t x) = v x * ∫⁻ t in Ioi (u x), w t
  have hFx : (fun t : ℝ => F t x) =
      (Ioi (u x)).indicator (fun t => w t * v x) := by
    funext t
    simp only [F, S, Set.indicator_apply, mem_Ioi]
    by_cases ht : u x < t <;> simp [ht]
  rw [hFx]
  rw [lintegral_indicator measurableSet_Ioi]
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hinter : Ioi (u x) ∩ Ioi (0 : ℝ) = Ioi (u x) := by
    apply inter_eq_left.mpr
    intro t ht
    exact (hu_nonneg x).trans_lt ht
  rw [hinter]
  rw [show (fun t : ℝ => w t * v x) = fun t => v x * w t by
    funext t
    exact mul_comm _ _]
  rw [lintegral_const_mul (v x) hw]

theorem measure_distribution_split_indicator_lt_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (T : (α → E) → α → ℝ) (f : α → E) (a threshold : ℝ)
    (hsub : ∀ g h x, T (g + h) x ≤ T g x + T h x) :
    μ {x | threshold < T f x} ≤
      μ {x | threshold / 2 < T ({y | ‖f y‖ < a}.indicator f) x} +
        μ {x | threshold / 2 < T ({y | a ≤ ‖f y‖}.indicator f) x} := by
  have hsplit : f = {y | ‖f y‖ < a}.indicator f + {y | a ≤ ‖f y‖}.indicator f := by
    funext x
    by_cases hx : ‖f x‖ < a
    · simp [hx]
    · have hxa : a ≤ ‖f x‖ := le_of_not_gt hx
      simp [hx, hxa]
  calc
    μ {x | threshold < T f x} ≤
        μ ({x | threshold / 2 < T ({y | ‖f y‖ < a}.indicator f) x} ∪
          {x | threshold / 2 < T ({y | a ≤ ‖f y‖}.indicator f) x}) := by
      apply measure_mono
      intro x hx
      rw [hsplit] at hx
      by_contra h
      simp only [mem_union, mem_setOf_eq, not_or] at h
      have hsmall : T ({y | ‖f y‖ < a}.indicator f) x ≤ threshold / 2 :=
        le_of_not_gt h.1
      have hlarge : T ({y | a ≤ ‖f y‖}.indicator f) x ≤ threshold / 2 :=
        le_of_not_gt h.2
      have hbound :
          T ({y | ‖f y‖ < a}.indicator f + {y | a ≤ ‖f y‖}.indicator f) x ≤
            threshold := by
        calc
          T ({y | ‖f y‖ < a}.indicator f + {y | a ≤ ‖f y‖}.indicator f) x ≤
              T ({y | ‖f y‖ < a}.indicator f) x +
                T ({y | a ≤ ‖f y‖}.indicator f) x := hsub _ _ _
          _ ≤ threshold / 2 + threshold / 2 := add_le_add hsmall hlarge
          _ = threshold := by ring
      exact (not_lt_of_ge hbound) hx
    _ ≤ μ {x | threshold / 2 < T ({y | ‖f y‖ < a}.indicator f) x} +
          μ {x | threshold / 2 < T ({y | a ≤ ‖f y‖}.indicator f) x} :=
      measure_union_le _ _

theorem ofReal_rpow_weight_one {p t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) =
      2 * (ENNReal.ofReal (t / 2) * ENNReal.ofReal (t ^ (p - 2))) := by
  have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [htwo]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ t / 2)]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
  congr 1
  calc
    t ^ (p - 1) = t ^ ((1 : ℝ) + (p - 2)) := by congr 1; ring
    _ = t ^ (1 : ℝ) * t ^ (p - 2) := Real.rpow_add ht _ _
    _ = 2 * ((t / 2) * t ^ (p - 2)) := by
      rw [Real.rpow_one]
      ring

theorem ofReal_rpow_weight_two {p t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) =
      4 * (ENNReal.ofReal ((t / 2) ^ (2 : ℕ)) * ENNReal.ofReal (t ^ (p - 3))) := by
  have hfour : (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) := by norm_num
  rw [hfour]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (t / 2) ^ (2 : ℕ))]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4)]
  congr 1
  calc
    t ^ (p - 1) = t ^ ((2 : ℝ) + (p - 3)) := by congr 1; ring
    _ = t ^ (2 : ℝ) * t ^ (p - 3) := Real.rpow_add ht _ _
    _ = 4 * ((t / 2) ^ (2 : ℕ) * t ^ (p - 3)) := by
      rw [Real.rpow_two]
      ring

theorem direct_weak_one_weighted
    {t p : ℝ} {m C I : ℝ≥0∞} (ht : 0 < t)
    (h : ENNReal.ofReal (t / 2) * m ≤ C * I) :
    m * ENNReal.ofReal (t ^ (p - 1)) ≤
      (2 : ℝ≥0∞) * C * I * ENNReal.ofReal (t ^ (p - 2)) := by
  rw [ofReal_rpow_weight_one ht]
  calc
    m * (2 * (ENNReal.ofReal (t / 2) * ENNReal.ofReal (t ^ (p - 2)))) =
        (ENNReal.ofReal (t / 2) * m) *
          (2 * ENNReal.ofReal (t ^ (p - 2))) := by ac_rfl
    _ ≤ (C * I) * (2 * ENNReal.ofReal (t ^ (p - 2))) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = (2 : ℝ≥0∞) * C * I * ENNReal.ofReal (t ^ (p - 2)) := by ac_rfl

theorem direct_weak_two_weighted
    {t p : ℝ} {m C I : ℝ≥0∞} (ht : 0 < t)
    (h : ENNReal.ofReal ((t / 2) ^ (2 : ℕ)) * m ≤ C * I) :
    m * ENNReal.ofReal (t ^ (p - 1)) ≤
      (4 : ℝ≥0∞) * C * I * ENNReal.ofReal (t ^ (p - 3)) := by
  rw [ofReal_rpow_weight_two ht]
  calc
    m * (4 * (ENNReal.ofReal ((t / 2) ^ (2 : ℕ)) *
        ENNReal.ofReal (t ^ (p - 3)))) =
        (ENNReal.ofReal ((t / 2) ^ (2 : ℕ)) * m) *
          (4 * ENNReal.ofReal (t ^ (p - 3))) := by ac_rfl
    _ ≤ (C * I) * (4 * ENNReal.ofReal (t ^ (p - 3))) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = (4 : ℝ≥0∞) * C * I * ENNReal.ofReal (t ^ (p - 3)) := by ac_rfl

theorem measurable_lintegral_indicator_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (v : α → ℝ≥0∞) (hv : Measurable v) :
    Measurable (fun t : ℝ => ∫⁻ x in {x | t ≤ u x}, v x ∂μ) := by
  let S : Set (ℝ × α) := {q | q.1 ≤ u q.2}
  have hS : MeasurableSet S := by
    exact measurableSet_le measurable_fst (hu.comp measurable_snd)
  let F : ℝ → α → ℝ≥0∞ := fun t x =>
    S.indicator (fun q : ℝ × α => v q.2) (t, x)
  have hF : Measurable (Function.uncurry F) := by
    change Measurable (S.indicator (fun q : ℝ × α => v q.2))
    exact (hv.comp measurable_snd).indicator hS
  have hmeas : Measurable (fun t : ℝ => ∫⁻ x, F t x ∂μ) :=
    hF.lintegral_prod_right
  convert hmeas using 1
  funext t
  have hFt : (fun x : α => F t x) = {x | t ≤ u x}.indicator v := by
    funext x
    simp only [F, S, Set.indicator_apply]
    by_cases hx : t ≤ u x <;> simp [hx]
  rw [hFt, lintegral_indicator (measurableSet_le measurable_const hu)]

theorem measurable_lintegral_indicator_lt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (v : α → ℝ≥0∞) (hv : Measurable v) :
    Measurable (fun t : ℝ => ∫⁻ x in {x | u x < t}, v x ∂μ) := by
  let S : Set (ℝ × α) := {q | u q.2 < q.1}
  have hS : MeasurableSet S := by
    exact measurableSet_lt (hu.comp measurable_snd) measurable_fst
  let F : ℝ → α → ℝ≥0∞ := fun t x =>
    S.indicator (fun q : ℝ × α => v q.2) (t, x)
  have hF : Measurable (Function.uncurry F) := by
    change Measurable (S.indicator (fun q : ℝ × α => v q.2))
    exact (hv.comp measurable_snd).indicator hS
  have hmeas : Measurable (fun t : ℝ => ∫⁻ x, F t x ∂μ) :=
    hF.lintegral_prod_right
  convert hmeas using 1
  funext t
  have hFt : (fun x : α => F t x) = {x | u x < t}.indicator v := by
    funext x
    simp only [F, S, Set.indicator_apply]
    by_cases hx : u x < t <;> simp [hx]
  rw [hFt, lintegral_indicator (measurableSet_lt hu measurable_const)]

/-- The unbundled Marcinkiewicz interpolation estimate obtained by splitting
`f` at each height, applying weak `(1,1)` and `(2,2)` estimates, and using
Tonelli together with the two elementary power-tail integrals. -/
theorem marcinkiewicz_weak_one_two
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (T : (α → E) → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ g h x, T (g + h) x ≤ T g x + T h x)
    (C₁ C₂ : ℝ≥0∞)
    (hweak_one : ∀ (g : α → E) {s : ℝ}, 0 < s →
      ENNReal.ofReal s * μ {x | s < T g x} ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ))
    (hweak_two : ∀ (g : α → E) {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : α → E) (hf : Measurable f) (hTf : AEMeasurable (T f) μ) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        ((4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ +
          2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) := by
  let u : α → ℝ := fun x => ‖f x‖
  let low : ℝ → α → E := fun t => {x | u x < t}.indicator f
  let high : ℝ → α → E := fun t => {x | t ≤ u x}.indicator f
  let lowI : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x in {x | u x < t}, ENNReal.ofReal ((u x) ^ (2 : ℕ)) ∂μ
  let highI : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x in {x | t ≤ u x}, ENNReal.ofReal (u x) ∂μ
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 1))
  let wlow : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 3)
  let whigh : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 2)
  have hu : Measurable u := by
    simpa only [u] using hf.norm
  have hu_nonneg : ∀ x, 0 ≤ u x := fun x => by
    dsimp only [u]
    exact norm_nonneg _
  have hvlow : Measurable (fun x => ENNReal.ofReal ((u x) ^ (2 : ℕ))) :=
    (hu.pow_const 2).ennreal_ofReal
  have hvhigh : Measurable (fun x => ENNReal.ofReal (u x)) :=
    hu.ennreal_ofReal
  have hwlow : Measurable wlow := by
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hwhigh : Measurable whigh := by
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hinput : Measurable (fun x => (ENNReal.ofReal (u x)) ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hu.ennreal_ofReal
  have hlowI_meas : Measurable lowI := by
    exact measurable_lintegral_indicator_lt u hu _ hvlow
  have hhighI_meas : Measurable highI := by
    exact measurable_lintegral_indicator_le u hu _ hvhigh
  have hlow_norm (t : ℝ) :
      (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) = lowI t := by
    change (∫⁻ x, ENNReal.ofReal (‖{x | u x < t}.indicator f x‖ ^ (2 : ℕ)) ∂μ) = _
    dsimp only [lowI]
    rw [← lintegral_indicator (measurableSet_lt hu measurable_const)]
    apply lintegral_congr
    intro x
    by_cases hx : u x < t <;> simp [hx, u]
  have hhigh_norm (t : ℝ) :
      (∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) = highI t := by
    change (∫⁻ x, ENNReal.ofReal ‖{x | t ≤ u x}.indicator f x‖ ∂μ) = _
    dsimp only [highI]
    rw [← lintegral_indicator (measurableSet_le measurable_const hu)]
    apply lintegral_congr
    intro x
    by_cases hx : t ≤ u x <;> simp [hx, u]
  have hlow_endpoint (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal ((t / 2) ^ (2 : ℕ)) *
          μ {x | t / 2 < T (low t) x} ≤ C₂ * lowI t := by
    calc
      ENNReal.ofReal ((t / 2) ^ (2 : ℕ)) *
          μ {x | t / 2 < T (low t) x} ≤
          C₂ * (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) :=
        hweak_two (low t) (by positivity)
      _ = C₂ * lowI t := by rw [hlow_norm]
  have hhigh_endpoint (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (t / 2) * μ {x | t / 2 < T (high t) x} ≤ C₁ * highI t := by
    calc
      ENNReal.ofReal (t / 2) * μ {x | t / 2 < T (high t) x} ≤
          C₁ * (∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) :=
        hweak_one (high t) (by positivity)
      _ = C₁ * highI t := by rw [hhigh_norm]
  have hlow_weight (t : ℝ) (ht : 0 < t) :
      μ {x | t / 2 < T (low t) x} * w t ≤
        4 * C₂ * lowI t * wlow t := by
    dsimp only [w, wlow]
    simpa only [ENNReal.ofReal_rpow_of_pos ht] using
      (direct_weak_two_weighted (p := p) ht (hlow_endpoint t ht))
  have hhigh_weight (t : ℝ) (ht : 0 < t) :
      μ {x | t / 2 < T (high t) x} * w t ≤
        2 * C₁ * highI t * whigh t := by
    dsimp only [w, whigh]
    simpa only [ENNReal.ofReal_rpow_of_pos ht] using
      (direct_weak_one_weighted (p := p) ht (hhigh_endpoint t ht))
  have hdistribution (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} * w t ≤
        4 * C₂ * lowI t * wlow t + 2 * C₁ * highI t * whigh t := by
    have hsplit : μ {x | t < T f x} ≤
        μ {x | t / 2 < T (low t) x} + μ {x | t / 2 < T (high t) x} := by
      simpa only [low, high, u] using
        measure_distribution_split_indicator_lt_le μ T f t t hT_subadd
    calc
      μ {x | t < T f x} * w t ≤
          (μ {x | t / 2 < T (low t) x} +
            μ {x | t / 2 < T (high t) x}) * w t :=
        mul_le_mul_left hsplit _
      _ = μ {x | t / 2 < T (low t) x} * w t +
          μ {x | t / 2 < T (high t) x} * w t := add_mul _ _ _
      _ ≤ 4 * C₂ * lowI t * wlow t + 2 * C₁ * highI t * whigh t :=
        add_le_add (hlow_weight t ht) (hhigh_weight t ht)
  have hlow_meas : Measurable (fun t => 4 * C₂ * lowI t * wlow t) :=
    ((measurable_const.mul hlowI_meas).mul hwlow)
  have hhigh_meas : Measurable (fun t => 2 * C₁ * highI t * whigh t) :=
    ((measurable_const.mul hhighI_meas).mul hwhigh)
  have hdistribution_integral :
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) ≤
        (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) +
          ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) ≤
          ∫⁻ t in Ioi (0 : ℝ),
            4 * C₂ * lowI t * wlow t + 2 * C₁ * highI t * whigh t := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hdistribution t ht
      _ = (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) +
          ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t :=
        lintegral_add_left hlow_meas _
  have hlow_integral :
      (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) =
        4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ *
          (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
    have hconst :
        (∫⁻ t in Ioi (0 : ℝ), (4 * C₂) * (lowI t * wlow t)) =
          (4 * C₂) * (∫⁻ t in Ioi (0 : ℝ), lowI t * wlow t) :=
      lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
        (4 * C₂) (hlowI_meas.mul hwlow)
    calc
      (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) =
          ∫⁻ t in Ioi (0 : ℝ), (4 * C₂) * (lowI t * wlow t) := by
        apply lintegral_congr
        intro t
        ac_rfl
      _ = (4 * C₂) * (∫⁻ t in Ioi (0 : ℝ), lowI t * wlow t) := hconst
      _ = (4 * C₂) * (∫⁻ t in Ioi (0 : ℝ), wlow t * lowI t) := by
        congr 1
        apply lintegral_congr
        intro t
        exact mul_comm _ _
      _ = (4 * C₂) * (∫⁻ x, ENNReal.ofReal ((u x) ^ (2 : ℕ)) *
          (∫⁻ t in Ioi (u x), wlow t) ∂μ) := by
        rw [lintegral_swap_indicator_lt u hu hu_nonneg _ hvlow _ hwlow]
      _ = 4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ *
          (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
        rw [show (fun t : ℝ => wlow t) =
            fun t => (ENNReal.ofReal t) ^ (p - 3) by rfl]
        rw [lintegral_ofReal_sq_mul_lintegral_rpow_Ioi_eq u hu hu_nonneg hp1 hp2]
        ac_rfl
  have hhigh_integral :
      (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
        2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
    have hconst :
        (∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highI t * whigh t)) =
          (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) :=
      lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
        (2 * C₁) (hhighI_meas.mul hwhigh)
    calc
      (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
          ∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highI t * whigh t) := by
        apply lintegral_congr
        intro t
        ac_rfl
      _ = (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := hconst
      _ = (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), whigh t * highI t) := by
        congr 1
        apply lintegral_congr
        intro t
        exact mul_comm _ _
      _ = (2 * C₁) * (∫⁻ x, ENNReal.ofReal (u x) *
          (∫⁻ t in Ioc (0 : ℝ) (u x), whigh t) ∂μ) := by
        rw [lintegral_swap_indicator_le u hu _ hvhigh _ hwhigh]
      _ = 2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
        rw [show (fun t : ℝ => whigh t) =
            fun t => (ENNReal.ofReal t) ^ (p - 2) by rfl]
        rw [lintegral_ofReal_mul_lintegral_rpow_Ioc_eq u hu hu_nonneg hp1]
        ac_rfl
  have hp_pos : 0 < p := by linarith
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) := by
      simpa only [w] using
        (lintegral_rpow_eq_lintegral_meas_lt_mul μ
          (Filter.Eventually.of_forall (hT_nonneg f)) hTf hp_pos)
    _ ≤ ENNReal.ofReal p *
        ((∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) +
          ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) :=
      mul_le_mul_right hdistribution_integral _
    _ = ENNReal.ofReal p *
        ((4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ +
          2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
      rw [hlow_integral, hhigh_integral]
      rw [add_mul]
    _ = ENNReal.ofReal p *
        ((4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ +
          2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) := by
      rfl

/-- Scaling a nonnegative output by a positive real pulls its `p`-power out
of the lower integral. -/
theorem marcinkiewicz_lintegral_ofReal_scale_rpow
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : α → ℝ) (scale p : ℝ) (hscale : 0 < scale) (hp : 0 ≤ p)
    (hg : ∀ x, 0 ≤ g x) (hgm : AEMeasurable g μ) :
    (∫⁻ x, ENNReal.ofReal ((scale * g x) ^ p) ∂μ) =
      (ENNReal.ofReal scale) ^ p * ∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ := by
  rw [← lintegral_const_mul'' _ ((hgm.pow_const p).ennreal_ofReal)]
  apply lintegral_congr
  intro x
  rw [Real.mul_rpow hscale.le (hg x)]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hscale.le _)]
  rw [ENNReal.ofReal_rpow_of_nonneg hscale.le hp]

theorem marcinkiewicz_scale_coefficient
    (a C₁ C₂ : ℝ≥0∞) (ha0 : a ≠ 0) (hatop : a ≠ ∞) (p : ℝ) :
    a ^ p *
        (4 * C₂ * a ^ (2 - p) * (ENNReal.ofReal (2 - p))⁻¹ +
          2 * C₁ * a ^ (1 - p) * (ENNReal.ofReal (p - 1))⁻¹) =
      (4 * (a ^ (2 : ℕ) * C₂) * (ENNReal.ofReal (2 - p))⁻¹ +
        2 * (a * C₁) * (ENNReal.ofReal (p - 1))⁻¹) := by
  have htwo : a ^ p * a ^ (2 - p) = a ^ (2 : ℕ) := by
    rw [← ENNReal.rpow_add _ _ ha0 hatop]
    convert ENNReal.rpow_natCast a 2 using 1
    all_goals ring_nf
  have hone : a ^ p * a ^ (1 - p) = a := by
    rw [← ENNReal.rpow_add _ _ ha0 hatop]
    convert ENNReal.rpow_one a using 1
    all_goals ring_nf
  rw [mul_add]
  calc
    a ^ p * (4 * C₂ * a ^ (2 - p) * (ENNReal.ofReal (2 - p))⁻¹) +
        a ^ p * (2 * C₁ * a ^ (1 - p) * (ENNReal.ofReal (p - 1))⁻¹) =
      4 * C₂ * (a ^ p * a ^ (2 - p)) * (ENNReal.ofReal (2 - p))⁻¹ +
        2 * C₁ * (a ^ p * a ^ (1 - p)) * (ENNReal.ofReal (p - 1))⁻¹ := by
        ac_rfl
    _ = _ := by rw [htwo, hone]; ac_rfl

theorem marcinkiewicz_scale_weak_one
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (T : (α → E) → α → ℝ)
    (C I : ℝ≥0∞)
    (g : α → E) (hweak : ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * μ {x | s < T g x} ≤ C * I)
    (scale s : ℝ) (hscale : 0 < scale) (hs : 0 < s) :
    ENNReal.ofReal s * μ {x | s < scale * T g x} ≤
      (ENNReal.ofReal scale * C) * I := by
  have hset : {x | s < scale * T g x} = {x | s / scale < T g x} := by
    ext x
    constructor
    · intro hx
      apply (div_lt_iff₀ hscale).mpr
      simpa [mul_comm] using hx
    · intro hx
      have h := (div_lt_iff₀ hscale).mp hx
      simpa [mul_comm] using h
  have h := hweak (div_pos hs hscale)
  rw [← hset] at h
  calc
    ENNReal.ofReal s * μ {x | s < scale * T g x} =
        ENNReal.ofReal scale *
          (ENNReal.ofReal (s / scale) * μ {x | s < scale * T g x}) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hscale.le]
      congr 1
      field_simp [hscale.ne']
    _ ≤ ENNReal.ofReal scale * (C * I) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (ENNReal.ofReal scale * C) * I := by ac_rfl

theorem marcinkiewicz_scale_weak_two
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (T : (α → E) → α → ℝ)
    (C I : ℝ≥0∞)
    (g : α → E) (hweak : ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤ C * I)
    (scale s : ℝ) (hscale : 0 < scale) (hs : 0 < s) :
    ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < scale * T g x} ≤
      (ENNReal.ofReal (scale ^ (2 : ℕ)) * C) * I := by
  have hset : {x | s < scale * T g x} = {x | s / scale < T g x} := by
    ext x
    constructor
    · intro hx
      apply (div_lt_iff₀ hscale).mpr
      simpa [mul_comm] using hx
    · intro hx
      have h := (div_lt_iff₀ hscale).mp hx
      simpa [mul_comm] using h
  have h := hweak (div_pos hs hscale)
  rw [← hset] at h
  calc
    ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < scale * T g x} =
        ENNReal.ofReal (scale ^ (2 : ℕ)) *
          (ENNReal.ofReal ((s / scale) ^ (2 : ℕ)) *
            μ {x | s < scale * T g x}) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg scale)]
      congr 1
      field_simp [hscale.ne']
    _ ≤ ENNReal.ofReal (scale ^ (2 : ℕ)) * (C * I) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (ENNReal.ofReal (scale ^ (2 : ℕ)) * C) * I := by ac_rfl

/-- The Marcinkiewicz estimate with a positive amplitude split scale.  Its
weak `(1,1)` contribution has factor `scale ^ (1 - p)` and its weak `(2,2)`
contribution has factor `scale ^ (2 - p)`. -/
theorem marcinkiewicz_weak_one_two_scaled
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (T : (α → E) → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ g h x, T (g + h) x ≤ T g x + T h x)
    (C₁ C₂ : ℝ≥0∞)
    (hweak_one : ∀ (g : α → E) {s : ℝ}, 0 < s →
      ENNReal.ofReal s * μ {x | s < T g x} ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ))
    (hweak_two : ∀ (g : α → E) {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : α → E) (hf : Measurable f) (hTf : AEMeasurable (T f) μ)
    (scale : ℝ) (hscale : 0 < scale) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        ((4 * C₂ * (ENNReal.ofReal scale) ^ (2 - p) *
            (ENNReal.ofReal (2 - p))⁻¹ +
          2 * C₁ * (ENNReal.ofReal scale) ^ (1 - p) *
            (ENNReal.ofReal (p - 1))⁻¹) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) := by
  have hp0 : 0 ≤ p := by linarith
  have ha0 : ENNReal.ofReal scale ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hscale
  have hatop : ENNReal.ofReal scale ≠ ∞ := ENNReal.ofReal_ne_top
  have hscaled := marcinkiewicz_weak_one_two
    (fun g x => scale * T g x)
    (by
      intro g x
      exact mul_nonneg hscale.le (hT_nonneg g x))
    (by
      intro g h x
      calc
        scale * T (g + h) x ≤ scale * (T g x + T h x) :=
          mul_le_mul_of_nonneg_left (hT_subadd g h x) hscale.le
        _ = scale * T g x + scale * T h x := by ring)
    (ENNReal.ofReal scale * C₁)
    (ENNReal.ofReal (scale ^ (2 : ℕ)) * C₂)
    (by
      intro g s hs
      exact marcinkiewicz_scale_weak_one T C₁
        (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ) g
        (fun {q} hq => hweak_one g hq) scale s hscale hs)
    (by
      intro g s hs
      exact marcinkiewicz_scale_weak_two T C₂
        (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ) g
        (fun {q} hq => hweak_two g hq) scale s hscale hs)
    hp1 hp2 f hf (hTf.const_mul scale)
  rw [ENNReal.ofReal_pow hscale.le] at hscaled
  have hscaled_lhs :
      (∫⁻ x, ENNReal.ofReal ((scale * T f x) ^ p) ∂μ) =
        (ENNReal.ofReal scale) ^ p *
          ∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ :=
    marcinkiewicz_lintegral_ofReal_scale_rpow (T f) scale p hscale hp0
      (hT_nonneg f) hTf
  have hcoeff :=
    marcinkiewicz_scale_coefficient (ENNReal.ofReal scale) C₁ C₂ ha0 hatop p
  rw [← ENNReal.mul_le_mul_iff_right
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hscale) hatop).ne'
    (ENNReal.rpow_ne_top_of_ne_zero ha0 hatop)]
  rw [← hscaled_lhs]
  refine hscaled.trans_eq ?_
  calc
    ENNReal.ofReal p *
        ((4 * (ENNReal.ofReal scale ^ (2 : ℕ) * C₂) *
            (ENNReal.ofReal (2 - p))⁻¹ +
          2 * (ENNReal.ofReal scale * C₁) *
            (ENNReal.ofReal (p - 1))⁻¹) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) =
      (ENNReal.ofReal scale) ^ p *
        (ENNReal.ofReal p *
          ((4 * C₂ * (ENNReal.ofReal scale) ^ (2 - p) *
              (ENNReal.ofReal (2 - p))⁻¹ +
            2 * C₁ * (ENNReal.ofReal scale) ^ (1 - p) *
              (ENNReal.ofReal (p - 1))⁻¹) *
            ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ)) := by
        calc
          ENNReal.ofReal p *
              ((4 * (ENNReal.ofReal scale ^ (2 : ℕ) * C₂) *
                  (ENNReal.ofReal (2 - p))⁻¹ +
                2 * (ENNReal.ofReal scale * C₁) *
                  (ENNReal.ofReal (p - 1))⁻¹) *
                ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) =
            ENNReal.ofReal p *
              (((ENNReal.ofReal scale) ^ p *
                (4 * C₂ * (ENNReal.ofReal scale) ^ (2 - p) *
                    (ENNReal.ofReal (2 - p))⁻¹ +
                  2 * C₁ * (ENNReal.ofReal scale) ^ (1 - p) *
                    (ENNReal.ofReal (p - 1))⁻¹)) *
                ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) := by
              rw [hcoeff]
          _ = _ := by ac_rfl

theorem measure_distribution_split_add
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (T : (α → E) → α → ℝ)
    (f low high : α → E) (threshold : ℝ)
    (hsplit : f = low + high)
    (hsub : ∀ x, T (low + high) x ≤ T low x + T high x) :
    μ {x | threshold < T f x} ≤
      μ {x | threshold / 2 < T low x} +
        μ {x | threshold / 2 < T high x} := by
  calc
    μ {x | threshold < T f x} ≤
        μ ({x | threshold / 2 < T low x} ∪
          {x | threshold / 2 < T high x}) := by
      apply measure_mono
      intro x hx
      rw [hsplit] at hx
      by_contra h
      simp only [mem_union, mem_setOf_eq, not_or] at h
      have hlow : T low x ≤ threshold / 2 := le_of_not_gt h.1
      have hhigh : T high x ≤ threshold / 2 := le_of_not_gt h.2
      have hbound : T (low + high) x ≤ threshold := by
        calc
          T (low + high) x ≤ T low x + T high x := hsub x
          _ ≤ threshold / 2 + threshold / 2 := add_le_add hlow hhigh
          _ = threshold := by ring
      exact (not_lt_of_ge hbound) hx
    _ ≤ μ {x | threshold / 2 < T low x} +
          μ {x | threshold / 2 < T high x} :=
      measure_union_le _ _

/-- A strong Marcinkiewicz estimate on a supplied input domain.  The last two
hypotheses are the actual weighted lower-integral tails of the supplied
splitting family, with weights `t ^ (p - 3)` for the weak `(2,2)` part and
`t ^ (p - 2)` for the weak `(1,1)` part. -/
theorem marcinkiewicz_weak_one_two_on_split
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (D : Set (α → E))
    (T : (α → E) → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : α → E⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (C₁ C₂ : ℝ≥0∞)
    (hweak_one : ∀ (g : α → E), g ∈ D → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * μ {x | s < T g x} ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ))
    (hweak_two : ∀ (g : α → E), g ∈ D → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : α → E) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → α → E)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlowI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ))
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ))
    (A₂ A₁ : ℝ≥0∞)
    (hlow_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) ≤ A₂)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) ≤ A₁) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p * (4 * C₂ * A₂ + 2 * C₁ * A₁) := by
  let lowI : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ
  let highI : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 1))
  let wlow : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 3)
  let whigh : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 2)
  have hlowI_meas' : Measurable lowI := by
    simpa only [lowI] using hlowI_meas
  have hhighI_meas' : Measurable highI := by
    simpa only [highI] using hhighI_meas
  have hlow_prod_meas : Measurable (fun t => lowI t * wlow t) := by
    exact hlowI_meas'.mul
      (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
  have hhigh_prod_meas : Measurable (fun t => highI t * whigh t) := by
    exact hhighI_meas'.mul
      (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
  have hlow_meas : Measurable (fun t => 4 * C₂ * lowI t * wlow t) := by
    rw [show (fun t => 4 * C₂ * lowI t * wlow t) =
        fun t => (4 * C₂) * (lowI t * wlow t) by
      funext t
      ac_rfl]
    exact measurable_const.mul hlow_prod_meas
  have hhigh_meas : Measurable (fun t => 2 * C₁ * highI t * whigh t) := by
    rw [show (fun t => 2 * C₁ * highI t * whigh t) =
        fun t => (2 * C₁) * (highI t * whigh t) by
      funext t
      ac_rfl]
    exact measurable_const.mul hhigh_prod_meas
  have hlow_endpoint (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal ((t / 2) ^ (2 : ℕ)) *
          μ {x | t / 2 < T (low t) x} ≤ C₂ * lowI t := by
    simpa only [lowI] using hweak_two (low t) (hlow_mem t) (by positivity)
  have hhigh_endpoint (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (t / 2) * μ {x | t / 2 < T (high t) x} ≤ C₁ * highI t := by
    simpa only [highI] using hweak_one (high t) (hhigh_mem t) (by positivity)
  have hlow_weight (t : ℝ) (ht : 0 < t) :
      μ {x | t / 2 < T (low t) x} * w t ≤
        4 * C₂ * lowI t * wlow t := by
    dsimp only [w, wlow]
    simpa only [ENNReal.ofReal_rpow_of_pos ht] using
      (direct_weak_two_weighted (p := p) ht (hlow_endpoint t ht))
  have hhigh_weight (t : ℝ) (ht : 0 < t) :
      μ {x | t / 2 < T (high t) x} * w t ≤
        2 * C₁ * highI t * whigh t := by
    dsimp only [w, whigh]
    simpa only [ENNReal.ofReal_rpow_of_pos ht] using
      (direct_weak_one_weighted (p := p) ht (hhigh_endpoint t ht))
  have hdistribution (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} * w t ≤
        4 * C₂ * lowI t * wlow t + 2 * C₁ * highI t * whigh t := by
    have hsplit' : μ {x | t < T f x} ≤
        μ {x | t / 2 < T (low t) x} +
          μ {x | t / 2 < T (high t) x} :=
      measure_distribution_split_add μ T f (low t) (high t) t (hsplit t)
        (hT_subadd (hlow_mem t) (hhigh_mem t))
    calc
      μ {x | t < T f x} * w t ≤
          (μ {x | t / 2 < T (low t) x} +
            μ {x | t / 2 < T (high t) x}) * w t :=
        mul_le_mul_left hsplit' _
      _ = μ {x | t / 2 < T (low t) x} * w t +
          μ {x | t / 2 < T (high t) x} * w t := add_mul _ _ _
      _ ≤ 4 * C₂ * lowI t * wlow t + 2 * C₁ * highI t * whigh t :=
        add_le_add (hlow_weight t ht) (hhigh_weight t ht)
  have hdistribution_integral :
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) ≤
        (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) +
          ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) ≤
          ∫⁻ t in Ioi (0 : ℝ),
            4 * C₂ * lowI t * wlow t + 2 * C₁ * highI t * whigh t := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hdistribution t ht
      _ = (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) +
          ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t :=
        lintegral_add_left hlow_meas _
  have hlow_integral :
      (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) =
        4 * C₂ * (∫⁻ t in Ioi (0 : ℝ), lowI t * wlow t) := by
    have hconst :
        (∫⁻ t in Ioi (0 : ℝ), (4 * C₂) * (lowI t * wlow t)) =
          (4 * C₂) * (∫⁻ t in Ioi (0 : ℝ), lowI t * wlow t) :=
      lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
        (4 * C₂) hlow_prod_meas
    calc
      (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) =
          ∫⁻ t in Ioi (0 : ℝ), (4 * C₂) * (lowI t * wlow t) := by
        apply lintegral_congr
        intro t
        ac_rfl
      _ = _ := hconst
  have hhigh_integral :
      (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
        2 * C₁ * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := by
    have hconst :
        (∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highI t * whigh t)) =
          (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) :=
      lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
        (2 * C₁) hhigh_prod_meas
    calc
      (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
          ∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highI t * whigh t) := by
        apply lintegral_congr
        intro t
        ac_rfl
      _ = _ := hconst
  have hp_pos : 0 < p := by linarith
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) := by
      simpa only [w] using
        (lintegral_rpow_eq_lintegral_meas_lt_mul μ
          (Filter.Eventually.of_forall (hT_nonneg f)) hTf hp_pos)
    _ ≤ ENNReal.ofReal p *
        ((∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) +
          ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) :=
      mul_le_mul_right hdistribution_integral _
    _ = ENNReal.ofReal p *
        (4 * C₂ * (∫⁻ t in Ioi (0 : ℝ), lowI t * wlow t) +
          2 * C₁ * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t)) := by
      rw [hlow_integral, hhigh_integral]
    _ ≤ ENNReal.ofReal p * (4 * C₂ * A₂ + 2 * C₁ * A₁) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add
          (mul_le_mul_of_nonneg_left hlow_tail (by positivity))
          (mul_le_mul_of_nonneg_left hhigh_tail (by positivity))
      · positivity

/-- The strong endpoint form of `marcinkiewicz_weak_one_two_on_split`.  The
endpoints and measurability are required only on the supplied domain `D`. -/
theorem marcinkiewicz_one_two_on_split
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (D : Set (α → E))
    (T : (α → E) → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : α → E⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (hTmeas : ∀ (g : α → E), g ∈ D → AEMeasurable (T g) μ)
    (C₁ C₂ : ℝ≥0∞)
    (hstrong_one : ∀ (g : α → E), g ∈ D →
      (∫⁻ x, ENNReal.ofReal (T g x) ∂μ) ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ))
    (hstrong_two : ∀ (g : α → E), g ∈ D →
      (∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ) ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : α → E) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → α → E)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlowI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ))
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ))
    (A₂ A₁ : ℝ≥0∞)
    (hlow_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) ≤ A₂)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) ≤ A₁) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p * (4 * C₂ * A₂ + 2 * C₁ * A₁) := by
  apply marcinkiewicz_weak_one_two_on_split D T hT_nonneg hT_subadd C₁ C₂ ?_ ?_
    hp1 hp2 f hTf low high hlow_mem hhigh_mem hsplit hlowI_meas hhighI_meas A₂ A₁
    hlow_tail hhigh_tail
  · intro g hg s hs
    calc
      ENNReal.ofReal s * μ {x | s < T g x} ≤
          ENNReal.ofReal s *
            μ {x | ENNReal.ofReal s ≤ ENNReal.ofReal (T g x)} := by
        apply mul_le_mul_right
        apply measure_mono
        intro x hx
        exact ENNReal.ofReal_le_ofReal hx.le
      _ ≤ ∫⁻ x, ENNReal.ofReal (T g x) ∂μ :=
        mul_meas_ge_le_lintegral₀ (hTmeas g hg).ennreal_ofReal (ENNReal.ofReal s)
      _ ≤ C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ) := hstrong_one g hg
  · intro g hg s hs
    calc
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤
          ENNReal.ofReal (s ^ (2 : ℕ)) *
            μ {x | ENNReal.ofReal (s ^ (2 : ℕ)) ≤
              ENNReal.ofReal ((T g x) ^ (2 : ℕ))} := by
        apply mul_le_mul_right
        apply measure_mono
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        exact pow_le_pow_left₀ hs.le hx.le 2
      _ ≤ ∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ :=
        mul_meas_ge_le_lintegral₀ ((hTmeas g hg).pow_const 2).ennreal_ofReal
          (ENNReal.ofReal (s ^ (2 : ℕ)))
      _ ≤ C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ) := hstrong_two g hg

theorem measure_distribution_split_additive
    {α F : Type*} [MeasurableSpace α] [Add F]
    (μ : Measure α) (T : F → α → ℝ)
    (f low high : F) (threshold : ℝ)
    (hsplit : f = low + high)
    (hsub : ∀ x, T (low + high) x ≤ T low x + T high x) :
    μ {x | threshold < T f x} ≤
      μ {x | threshold / 2 < T low x} +
        μ {x | threshold / 2 < T high x} := by
  calc
    μ {x | threshold < T f x} ≤
        μ ({x | threshold / 2 < T low x} ∪
          {x | threshold / 2 < T high x}) := by
      apply measure_mono
      intro x hx
      rw [hsplit] at hx
      by_contra h
      simp only [mem_union, mem_setOf_eq, not_or] at h
      have hlow : T low x ≤ threshold / 2 := le_of_not_gt h.1
      have hhigh : T high x ≤ threshold / 2 := le_of_not_gt h.2
      have hbound : T (low + high) x ≤ threshold := by
        calc
          T (low + high) x ≤ T low x + T high x := hsub x
          _ ≤ threshold / 2 + threshold / 2 := add_le_add hlow hhigh
          _ = threshold := by ring
      exact (not_lt_of_ge hbound) hx
    _ ≤ μ {x | threshold / 2 < T low x} +
          μ {x | threshold / 2 < T high x} :=
      measure_union_le _ _

/-- The supplied-split Marcinkiewicz argument for an arbitrary additive input
type, evaluated pointwise by `eval`.  It is the form applicable directly to
Schwartz maps; its tail assumptions are the two displayed weighted lower
integrals, rather than any opaque interface. -/
theorem marcinkiewicz_weak_one_two_on_additive_split
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E)
    (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (C₁ C₂ : ℝ≥0∞)
    (hweak_one : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * μ {x | s < T g x} ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖eval g x‖ ∂μ))
    (hweak_two : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖eval g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlowI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ))
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ))
    (A₂ A₁ : ℝ≥0∞)
    (hlow_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) ≤ A₂)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) ≤ A₁) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p * (4 * C₂ * A₂ + 2 * C₁ * A₁) := by
  let lowI : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ
  let highI : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 1))
  let wlow : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 3)
  let whigh : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 2)
  have hlowI_meas' : Measurable lowI := by
    simpa only [lowI] using hlowI_meas
  have hhighI_meas' : Measurable highI := by
    simpa only [highI] using hhighI_meas
  have hlow_prod_meas : Measurable (fun t => lowI t * wlow t) := by
    exact hlowI_meas'.mul
      (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
  have hhigh_prod_meas : Measurable (fun t => highI t * whigh t) := by
    exact hhighI_meas'.mul
      (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
  have hlow_meas : Measurable (fun t => 4 * C₂ * lowI t * wlow t) := by
    rw [show (fun t => 4 * C₂ * lowI t * wlow t) =
        fun t => (4 * C₂) * (lowI t * wlow t) by
      funext t
      ac_rfl]
    exact measurable_const.mul hlow_prod_meas
  have hhigh_meas : Measurable (fun t => 2 * C₁ * highI t * whigh t) := by
    rw [show (fun t => 2 * C₁ * highI t * whigh t) =
        fun t => (2 * C₁) * (highI t * whigh t) by
      funext t
      ac_rfl]
    exact measurable_const.mul hhigh_prod_meas
  have hlow_endpoint (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal ((t / 2) ^ (2 : ℕ)) *
          μ {x | t / 2 < T (low t) x} ≤ C₂ * lowI t := by
    simpa only [lowI] using hweak_two (low t) (hlow_mem t) (by positivity)
  have hhigh_endpoint (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (t / 2) * μ {x | t / 2 < T (high t) x} ≤ C₁ * highI t := by
    simpa only [highI] using hweak_one (high t) (hhigh_mem t) (by positivity)
  have hlow_weight (t : ℝ) (ht : 0 < t) :
      μ {x | t / 2 < T (low t) x} * w t ≤
        4 * C₂ * lowI t * wlow t := by
    dsimp only [w, wlow]
    simpa only [ENNReal.ofReal_rpow_of_pos ht] using
      (direct_weak_two_weighted (p := p) ht (hlow_endpoint t ht))
  have hhigh_weight (t : ℝ) (ht : 0 < t) :
      μ {x | t / 2 < T (high t) x} * w t ≤
        2 * C₁ * highI t * whigh t := by
    dsimp only [w, whigh]
    simpa only [ENNReal.ofReal_rpow_of_pos ht] using
      (direct_weak_one_weighted (p := p) ht (hhigh_endpoint t ht))
  have hdistribution (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} * w t ≤
        4 * C₂ * lowI t * wlow t + 2 * C₁ * highI t * whigh t := by
    have hsplit' : μ {x | t < T f x} ≤
        μ {x | t / 2 < T (low t) x} +
          μ {x | t / 2 < T (high t) x} :=
      measure_distribution_split_additive μ T f (low t) (high t) t (hsplit t)
        (hT_subadd (hlow_mem t) (hhigh_mem t))
    calc
      μ {x | t < T f x} * w t ≤
          (μ {x | t / 2 < T (low t) x} +
            μ {x | t / 2 < T (high t) x}) * w t :=
        mul_le_mul_left hsplit' _
      _ = μ {x | t / 2 < T (low t) x} * w t +
          μ {x | t / 2 < T (high t) x} * w t := add_mul _ _ _
      _ ≤ 4 * C₂ * lowI t * wlow t + 2 * C₁ * highI t * whigh t :=
        add_le_add (hlow_weight t ht) (hhigh_weight t ht)
  have hdistribution_integral :
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) ≤
        (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) +
          ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) ≤
          ∫⁻ t in Ioi (0 : ℝ),
            4 * C₂ * lowI t * wlow t + 2 * C₁ * highI t * whigh t := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hdistribution t ht
      _ = (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) +
          ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t :=
        lintegral_add_left hlow_meas _
  have hlow_integral :
      (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) =
        4 * C₂ * (∫⁻ t in Ioi (0 : ℝ), lowI t * wlow t) := by
    have hconst :
        (∫⁻ t in Ioi (0 : ℝ), (4 * C₂) * (lowI t * wlow t)) =
          (4 * C₂) * (∫⁻ t in Ioi (0 : ℝ), lowI t * wlow t) :=
      lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
        (4 * C₂) hlow_prod_meas
    calc
      (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) =
          ∫⁻ t in Ioi (0 : ℝ), (4 * C₂) * (lowI t * wlow t) := by
        apply lintegral_congr
        intro t
        ac_rfl
      _ = _ := hconst
  have hhigh_integral :
      (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
        2 * C₁ * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := by
    have hconst :
        (∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highI t * whigh t)) =
          (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) :=
      lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
        (2 * C₁) hhigh_prod_meas
    calc
      (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
          ∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highI t * whigh t) := by
        apply lintegral_congr
        intro t
        ac_rfl
      _ = _ := hconst
  have hp_pos : 0 < p := by linarith
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) := by
      simpa only [w] using
        (lintegral_rpow_eq_lintegral_meas_lt_mul μ
          (Filter.Eventually.of_forall (hT_nonneg f)) hTf hp_pos)
    _ ≤ ENNReal.ofReal p *
        ((∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowI t * wlow t) +
          ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) :=
      mul_le_mul_right hdistribution_integral _
    _ = ENNReal.ofReal p *
        (4 * C₂ * (∫⁻ t in Ioi (0 : ℝ), lowI t * wlow t) +
          2 * C₁ * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t)) := by
      rw [hlow_integral, hhigh_integral]
    _ ≤ ENNReal.ofReal p * (4 * C₂ * A₂ + 2 * C₁ * A₁) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add
          (mul_le_mul_of_nonneg_left hlow_tail (by positivity))
          (mul_le_mul_of_nonneg_left hhigh_tail (by positivity))
      · positivity

/-- The strong endpoint version of
`marcinkiewicz_weak_one_two_on_additive_split`. -/
theorem marcinkiewicz_one_two_on_additive_split
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E)
    (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (hTmeas : ∀ (g : F), g ∈ D → AEMeasurable (T g) μ)
    (C₁ C₂ : ℝ≥0∞)
    (hstrong_one : ∀ (g : F), g ∈ D →
      (∫⁻ x, ENNReal.ofReal (T g x) ∂μ) ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖eval g x‖ ∂μ))
    (hstrong_two : ∀ (g : F), g ∈ D →
      (∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ) ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖eval g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlowI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ))
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ))
    (A₂ A₁ : ℝ≥0∞)
    (hlow_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) ≤ A₂)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) ≤ A₁) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p * (4 * C₂ * A₂ + 2 * C₁ * A₁) := by
  apply marcinkiewicz_weak_one_two_on_additive_split D eval T hT_nonneg hT_subadd C₁ C₂
    ?_ ?_ hp1 hp2 f hTf low high hlow_mem hhigh_mem hsplit hlowI_meas hhighI_meas A₂ A₁
    hlow_tail hhigh_tail
  · intro g hg s hs
    calc
      ENNReal.ofReal s * μ {x | s < T g x} ≤
          ENNReal.ofReal s *
            μ {x | ENNReal.ofReal s ≤ ENNReal.ofReal (T g x)} := by
        apply mul_le_mul_right
        apply measure_mono
        intro x hx
        exact ENNReal.ofReal_le_ofReal hx.le
      _ ≤ ∫⁻ x, ENNReal.ofReal (T g x) ∂μ :=
        mul_meas_ge_le_lintegral₀ (hTmeas g hg).ennreal_ofReal (ENNReal.ofReal s)
      _ ≤ C₁ * (∫⁻ x, ENNReal.ofReal ‖eval g x‖ ∂μ) := hstrong_one g hg
  · intro g hg s hs
    calc
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤
          ENNReal.ofReal (s ^ (2 : ℕ)) *
            μ {x | ENNReal.ofReal (s ^ (2 : ℕ)) ≤
              ENNReal.ofReal ((T g x) ^ (2 : ℕ))} := by
        apply mul_le_mul_right
        apply measure_mono
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        exact pow_le_pow_left₀ hs.le hx.le 2
      _ ≤ ∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ :=
        mul_meas_ge_le_lintegral₀ ((hTmeas g hg).pow_const 2).ennreal_ofReal
          (ENNReal.ofReal (s ^ (2 : ℕ)))
      _ ≤ C₂ * (∫⁻ x, ENNReal.ofReal (‖eval g x‖ ^ (2 : ℕ)) ∂μ) := hstrong_two g hg

/-- A nonnegative real-valued `L²` function has an integrable square. -/
theorem integrable_sq_of_memLp_two_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : α → ℝ) (hg : MemLp g 2 μ) (hnonneg : ∀ x, 0 ≤ g x) :
    Integrable (fun x => (g x) ^ (2 : ℕ)) μ := by
  have h := hg.integrable_norm_rpow (by norm_num) ENNReal.ofNat_ne_top
  convert h using 1
  funext x
  norm_num [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]

/-- Convert a nonnegative real integral inequality to its lower-integral
form. -/
theorem lintegral_ofReal_le_of_integral_le
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α}
    (eval : F → α → E) (T : F → α → ℝ) (g : F) (c : ℝ)
    (hc : 0 ≤ c) (hTnonneg : ∀ x, 0 ≤ T g x)
    (hT : Integrable (T g) μ) (heval : Integrable (fun x => ‖eval g x‖) μ)
    (hbound : (∫ x, T g x ∂μ) ≤ c * ∫ x, ‖eval g x‖ ∂μ) :
    (∫⁻ x, ENNReal.ofReal (T g x) ∂μ) ≤
      ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal ‖eval g x‖ ∂μ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hT
    (Filter.Eventually.of_forall (hTnonneg ·))]
  rw [← ofReal_integral_eq_lintegral_ofReal heval
    (Filter.Eventually.of_forall (fun x => norm_nonneg _))]
  calc
    ENNReal.ofReal (∫ x, T g x ∂μ) ≤
        ENNReal.ofReal (c * ∫ x, ‖eval g x‖ ∂μ) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal c * ENNReal.ofReal (∫ x, ‖eval g x‖ ∂μ) :=
      ENNReal.ofReal_mul hc

/-- The square-power counterpart of
`lintegral_ofReal_le_of_integral_le`. -/
theorem lintegral_ofReal_sq_le_of_integral_sq_le
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α}
    (eval : F → α → E) (T : F → α → ℝ) (g : F) (c : ℝ)
    (hc : 0 ≤ c)
    (hT : Integrable (fun x => (T g x) ^ (2 : ℕ)) μ)
    (heval : Integrable (fun x => ‖eval g x‖ ^ (2 : ℕ)) μ)
    (hbound : (∫ x, (T g x) ^ (2 : ℕ) ∂μ) ≤
      c * ∫ x, ‖eval g x‖ ^ (2 : ℕ) ∂μ) :
    (∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ) ≤
      ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (‖eval g x‖ ^ (2 : ℕ)) ∂μ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hT
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
  rw [← ofReal_integral_eq_lintegral_ofReal heval
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
  calc
    ENNReal.ofReal (∫ x, (T g x) ^ (2 : ℕ) ∂μ) ≤
        ENNReal.ofReal (c * ∫ x, ‖eval g x‖ ^ (2 : ℕ) ∂μ) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal c * ENNReal.ofReal (∫ x, ‖eval g x‖ ^ (2 : ℕ) ∂μ) :=
      ENNReal.ofReal_mul hc

/-- A real-integral endpoint form of
`marcinkiewicz_one_two_on_additive_split`.  The lower-integral endpoint
inequalities are derived here from the displayed `MemLp` and real integral
hypotheses. -/
theorem marcinkiewicz_one_two_on_additive_split_real
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hmem_one : ∀ (g : F), g ∈ D → MemLp (T g) 1 μ)
    (hbound_one : ∀ (g : F), g ∈ D →
      (∫ x, T g x ∂μ) ≤ c₁ * ∫ x, ‖eval g x‖ ∂μ)
    (hinput_one : ∀ (g : F), g ∈ D →
      Integrable (fun x => ‖eval g x‖) μ)
    (hmem_two : ∀ (g : F), g ∈ D → MemLp (T g) 2 μ)
    (hbound_two : ∀ (g : F), g ∈ D →
      (∫ x, (T g x) ^ (2 : ℕ) ∂μ) ≤
        c₂ * ∫ x, ‖eval g x‖ ^ (2 : ℕ) ∂μ)
    (hinput_two : ∀ (g : F), g ∈ D →
      Integrable (fun x => ‖eval g x‖ ^ (2 : ℕ)) μ)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlowI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ))
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ))
    (A₂ A₁ : ℝ≥0∞)
    (hlow_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) ≤ A₂)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) ≤ A₁) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        (4 * ENNReal.ofReal c₂ * A₂ + 2 * ENNReal.ofReal c₁ * A₁) := by
  apply marcinkiewicz_one_two_on_additive_split D eval T hT_nonneg hT_subadd
    (fun g hg => (hmem_one g hg).1.aemeasurable) (ENNReal.ofReal c₁) (ENNReal.ofReal c₂)
    ?_ ?_ hp1 hp2 f hTf low high hlow_mem hhigh_mem hsplit hlowI_meas hhighI_meas A₂ A₁
    hlow_tail hhigh_tail
  · intro g hg
    apply lintegral_ofReal_le_of_integral_le eval T g c₁ hc₁ (hT_nonneg g)
      (memLp_one_iff_integrable.mp (hmem_one g hg)) (hinput_one g hg) (hbound_one g hg)
  · intro g hg
    apply lintegral_ofReal_sq_le_of_integral_sq_le eval T g c₂ hc₂
      (integrable_sq_of_memLp_two_nonneg (T g) (hmem_two g hg) (hT_nonneg g))
      (hinput_two g hg) (hbound_two g hg)

/-- The split form of real-endpoint Marcinkiewicz interpolation with a
positive amplitude threshold scale.  The profiles are supplied at parameter
`r`, while the interpolation step uses the actual split at `r = s * t`; the
two displayed powers of `s` are proved by the preceding half-line
change-of-variables lemmas. -/
theorem marcinkiewicz_one_two_on_additive_split_real_scaled
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hmem_one : ∀ (g : F), g ∈ D → MemLp (T g) 1 μ)
    (hbound_one : ∀ (g : F), g ∈ D →
      (∫ x, T g x ∂μ) ≤ c₁ * ∫ x, ‖eval g x‖ ∂μ)
    (hinput_one : ∀ (g : F), g ∈ D →
      Integrable (fun x => ‖eval g x‖) μ)
    (hmem_two : ∀ (g : F), g ∈ D → MemLp (T g) 2 μ)
    (hbound_two : ∀ (g : F), g ∈ D →
      (∫ x, (T g x) ^ (2 : ℕ) ∂μ) ≤
        c₂ * ∫ x, ‖eval g x‖ ^ (2 : ℕ) ∂μ)
    (hinput_two : ∀ (g : F), g ∈ D →
      Integrable (fun x => ‖eval g x‖ ^ (2 : ℕ)) μ)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlowI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ))
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ))
    (A₂ A₁ : ℝ≥0∞)
    (hlow_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) ≤ A₂)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) ≤ A₁)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        (4 * ENNReal.ofReal c₂ * ((ENNReal.ofReal s) ^ (2 - p) * A₂) +
          2 * ENNReal.ofReal c₁ * ((ENNReal.ofReal s) ^ (1 - p) * A₁)) := by
  apply marcinkiewicz_one_two_on_additive_split_real D eval T hT_nonneg hT_subadd
    c₁ c₂ hc₁ hc₂ hmem_one hbound_one hinput_one hmem_two hbound_two hinput_two
    hp1 hp2 f hTf (fun t => low (s * t)) (fun t => high (s * t))
    ?_ ?_ ?_ ?_ ?_ ((ENNReal.ofReal s) ^ (2 - p) * A₂)
    ((ENNReal.ofReal s) ^ (1 - p) * A₁) ?_ ?_
  · intro t
    exact hlow_mem (s * t)
  · intro t
    exact hhigh_mem (s * t)
  · intro t
    exact hsplit (s * t)
  · change Measurable ((fun r : ℝ =>
        ∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ) ∘
        fun t : ℝ => s * t)
    exact hlowI_meas.comp (measurable_const_mul s)
  · change Measurable ((fun r : ℝ =>
        ∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ) ∘ fun t : ℝ => s * t)
    exact hhighI_meas.comp (measurable_const_mul s)
  · calc
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low (s * t)) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) =
          (ENNReal.ofReal s) ^ (2 - p) *
            (∫⁻ r in Ioi (0 : ℝ),
              (∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ) *
                (ENNReal.ofReal r) ^ (p - 3)) :=
        lintegral_Ioi_comp_mul_low_weight
          (fun r => ∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ)
          hlowI_meas s hs p
      _ ≤ (ENNReal.ofReal s) ^ (2 - p) * A₂ := by
        exact mul_le_mul_right hlow_tail _
  · calc
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high (s * t)) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) =
          (ENNReal.ofReal s) ^ (1 - p) *
            (∫⁻ r in Ioi (0 : ℝ),
              (∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ) *
                (ENNReal.ofReal r) ^ (p - 2)) :=
        lintegral_Ioi_comp_mul_high_weight
          (fun r => ∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ)
          hhighI_meas s hs p
      _ ≤ (ENNReal.ofReal s) ^ (1 - p) * A₁ := by
        exact mul_le_mul_right hhigh_tail _

/-- A strong `L¹`/`L²` form of `marcinkiewicz_weak_one_two`.  The endpoint
hypotheses are lower-integral estimates for an unbundled nonnegative,
subadditive operator; the conclusion is its explicit `Lᵖ` bound for
`1 < p < 2`. -/
theorem marcinkiewicz_one_two
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (T : (α → E) → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ g h x, T (g + h) x ≤ T g x + T h x)
    (hTmeas : ∀ g, AEMeasurable (T g) μ)
    (C₁ C₂ : ℝ≥0∞)
    (hstrong_one : ∀ g,
      (∫⁻ x, ENNReal.ofReal (T g x) ∂μ) ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ))
    (hstrong_two : ∀ g,
      (∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ) ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : α → E) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        ((4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ +
          2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) := by
  apply marcinkiewicz_weak_one_two T hT_nonneg hT_subadd C₁ C₂ ?_ ?_ hp1 hp2 f hf
    (hTmeas f)
  · intro g s hs
    calc
      ENNReal.ofReal s * μ {x | s < T g x} ≤
          ENNReal.ofReal s * μ {x | ENNReal.ofReal s ≤ ENNReal.ofReal (T g x)} := by
        apply mul_le_mul_right
        apply measure_mono
        intro x hx
        exact ENNReal.ofReal_le_ofReal hx.le
      _ ≤ ∫⁻ x, ENNReal.ofReal (T g x) ∂μ :=
        mul_meas_ge_le_lintegral₀ (hTmeas g).ennreal_ofReal (ENNReal.ofReal s)
      _ ≤ C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ) := hstrong_one g
  · intro g s hs
    calc
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤
          ENNReal.ofReal (s ^ (2 : ℕ)) *
            μ {x | ENNReal.ofReal (s ^ (2 : ℕ)) ≤
              ENNReal.ofReal ((T g x) ^ (2 : ℕ))} := by
        apply mul_le_mul_right
        apply measure_mono
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        exact pow_le_pow_left₀ hs.le hx.le 2
      _ ≤ ∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ :=
        mul_meas_ge_le_lintegral₀ ((hTmeas g).pow_const 2).ennreal_ofReal
          (ENNReal.ofReal (s ^ (2 : ℕ)))
      _ ≤ C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ) := hstrong_two g

theorem memLp_of_lintegral_ofReal_rpow_lt_top
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : α → ℝ) (hg : AEMeasurable g μ) (hnonneg : ∀ x, 0 ≤ g x)
    {p : ℝ} (hp : 0 < p)
    (h : (∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ) < ∞) :
    MemLp g (ENNReal.ofReal p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt).mpr
  calc
    (∫⁻ x, ‖g x‖ₑ ^ (ENNReal.ofReal p).toReal ∂μ) =
        ∫⁻ x, (ENNReal.ofReal (g x)) ^ p ∂μ := by
      rw [ENNReal.toReal_ofReal hp.le]
      apply lintegral_congr
      intro x
      rw [enorm_eq_nnnorm]
      rw [Real.nnnorm_of_nonneg (hnonneg x)]
      rw [← ENNReal.ofReal_eq_coe_nnreal (hnonneg x)]
    _ = ∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ := by
      apply lintegral_congr
      intro x
      exact ENNReal.ofReal_rpow_of_nonneg (hnonneg x) hp.le
    _ < ∞ := h

/-- Finite endpoint constants carry the explicit lower-integral estimate in
`marcinkiewicz_one_two` to membership in `Lᵖ`. -/
theorem marcinkiewicz_one_two_memLp
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (T : (α → E) → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ g h x, T (g + h) x ≤ T g x + T h x)
    (hTmeas : ∀ g, AEMeasurable (T g) μ)
    (C₁ C₂ : ℝ≥0∞) (hC₁ : C₁ < ∞) (hC₂ : C₂ < ∞)
    (hstrong_one : ∀ g,
      (∫⁻ x, ENNReal.ofReal (T g x) ∂μ) ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ))
    (hstrong_two : ∀ g,
      (∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ) ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : α → E) (hf : Measurable f) (hfp : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (T f) (ENNReal.ofReal p) μ := by
  have hp : 0 < p := by linarith
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hinput : (∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) < ∞ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt).mp hfp.2
    simpa [ENNReal.toReal_ofReal hp.le, enorm_eq_nnnorm] using h
  have hinv_one : (ENNReal.ofReal (p - 1))⁻¹ < ∞ := by
    apply ENNReal.inv_lt_top.mpr
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hinv_two : (ENNReal.ofReal (2 - p))⁻¹ < ∞ := by
    apply ENNReal.inv_lt_top.mpr
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hlarge : 4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ < ∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hC₂) hinv_two
  have hsmall : 2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ < ∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hC₁) hinv_one
  have hright : ENNReal.ofReal p *
      ((4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ +
        2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹) *
        ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) < ∞ := by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    apply ENNReal.mul_lt_top
    · exact ENNReal.add_lt_top.mpr ⟨hlarge, hsmall⟩
    · exact hinput
  apply memLp_of_lintegral_ofReal_rpow_lt_top (T f) (hTmeas f) (hT_nonneg f) hp
  apply lt_of_le_of_lt
    (marcinkiewicz_one_two T hT_nonneg hT_subadd hTmeas C₁ C₂
      hstrong_one hstrong_two hp1 hp2 f hf)
  exact hright

/-- Marcinkiewicz interpolation between weak `(1,1)` and the pointwise
`L∞` contraction, on bounded inputs.  This is the form needed for the
dyadic-ball maximal operator: the low-amplitude truncation is killed by the
contraction, and the weak endpoint is integrated only over the
high-amplitude tail.  Restricting the interface to bounded inputs is
intentional: a real-valued maximal function formed with `ENNReal.toReal`
need not remain subadditive when an unbounded input has infinite averages. -/
theorem marcinkiewicz_weak_one_top
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (T : (α → E) → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ g h, Measurable g → Measurable h →
      (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖g x‖ ≤ a) →
      (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖h x‖ ≤ a) →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (C₁ : ℝ≥0∞)
    (hweak_one : ∀ (g : α → E), Measurable g →
      (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖g x‖ ≤ a) → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * μ {x | s < T g x} ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ))
    (hT_top : ∀ (g : α → E) (a : ℝ), 0 ≤ a →
      (∀ x, ‖g x‖ ≤ a) → ∀ x, T g x ≤ a)
    {p : ℝ} (hp : 1 < p)
    (f : α → E) (hf : Measurable f)
    (hf_bounded : ∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖f x‖ ≤ a)
    (hTf : AEMeasurable (T f) μ) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        (2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) := by
  /- Split at half the output height.  The low piece has pointwise norm at
  most `t / 2`, hence contributes no points to `{t < T f}`. -/
  let u : α → ℝ := fun x => ‖f x‖
  let low : ℝ → α → E := fun t => {x | u x < t / 2}.indicator f
  let high : ℝ → α → E := fun t => {x | t / 2 ≤ u x}.indicator f
  let highI : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x in {x | t / 2 ≤ u x}, ENNReal.ofReal (u x) ∂μ
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 1))
  let whigh : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 2)
  have hu : Measurable u := by
    simpa only [u] using hf.norm
  have hu_nonneg : ∀ x, 0 ≤ u x := fun x => by
    dsimp only [u]
    exact norm_nonneg _
  have hvhigh : Measurable (fun x => ENNReal.ofReal (u x)) :=
    hu.ennreal_ofReal
  have hwhigh : Measurable whigh := by
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hhighI_meas : Measurable highI := by
    have hbase : Measurable (fun s : ℝ =>
        ∫⁻ x in {x | s ≤ u x}, ENNReal.ofReal (u x) ∂μ) :=
      measurable_lintegral_indicator_le u hu _ hvhigh
    change Measurable (fun t : ℝ =>
      (fun s : ℝ => ∫⁻ x in {x | s ≤ u x}, ENNReal.ofReal (u x) ∂μ) (t / 2))
    exact hbase.comp (measurable_id.div_const 2)
  have hhigh_norm (t : ℝ) :
      (∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) = highI t := by
    change (∫⁻ x, ENNReal.ofReal ‖{x | t / 2 ≤ u x}.indicator f x‖ ∂μ) = _
    dsimp only [highI]
    have hset : MeasurableSet {x | t / 2 ≤ u x} :=
      measurableSet_le measurable_const hu
    rw [← lintegral_indicator hset]
    apply lintegral_congr
    intro x
    by_cases hx : t / 2 ≤ u x <;> simp [hx, u]
  have hlow_meas (t : ℝ) : Measurable (low t) := by
    dsimp only [low]
    exact hf.indicator (measurableSet_lt hu measurable_const)
  have hhigh_meas (t : ℝ) : Measurable (high t) := by
    dsimp only [high]
    exact hf.indicator (measurableSet_le measurable_const hu)
  have hlow_norm (t : ℝ) (ht : 0 < t) : ∀ x, ‖low t x‖ ≤ t / 2 := by
    intro y
    change ‖{x | u x < t / 2}.indicator f y‖ ≤ t / 2
    by_cases hy : u y < t / 2
    · simpa [hy, u] using hy.le
    · simp [hy]
      positivity
  have hlow_bounded (t : ℝ) (ht : 0 < t) :
      ∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖low t x‖ ≤ a := by
    exact ⟨t / 2, (by positivity), hlow_norm t ht⟩
  have hlow_bound (t : ℝ) (ht : 0 < t) (x : α) :
      T (low t) x ≤ t / 2 := by
    apply hT_top (low t) (t / 2) (by positivity)
    exact hlow_norm t ht
  have hhigh_bounded (t : ℝ) :
      ∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖high t x‖ ≤ a := by
    rcases hf_bounded with ⟨a, ha, hfa⟩
    refine ⟨a, ha, ?_⟩
    intro y
    change ‖{x | t / 2 ≤ u x}.indicator f y‖ ≤ a
    by_cases hy : t / 2 ≤ u y
    · simpa [hy] using hfa y
    · simp [hy, ha]
  have hsplit (t : ℝ) : f = low t + high t := by
    funext x
    by_cases hx : u x < t / 2
    · simp [low, high, hx]
    · have hx' : t / 2 ≤ u x := le_of_not_gt hx
      simp [low, high, hx, hx']
  have hdistribution (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} ≤ μ {x | t / 2 < T (high t) x} := by
    apply measure_mono
    intro x hx
    rw [hsplit t] at hx
    have hsum := hT_subadd (low t) (high t) (hlow_meas t) (hhigh_meas t)
      (hlow_bounded t ht) (hhigh_bounded t) x
    have hlow := hlow_bound t ht x
    by_contra h
    have hhigh : T (high t) x ≤ t / 2 := le_of_not_gt h
    have : T (low t + high t) x ≤ t := by
      calc
        T (low t + high t) x ≤ T (low t) x + T (high t) x := hsum
        _ ≤ t / 2 + t / 2 := add_le_add hlow hhigh
        _ = t := by ring
    exact (not_lt_of_ge this) hx
  have hhigh_endpoint (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (t / 2) * μ {x | t / 2 < T (high t) x} ≤ C₁ * highI t := by
    calc
      ENNReal.ofReal (t / 2) * μ {x | t / 2 < T (high t) x} ≤
          C₁ * (∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) :=
        hweak_one (high t) (hhigh_meas t) (hhigh_bounded t)
          (by positivity)
      _ = C₁ * highI t := by rw [hhigh_norm]
  have hdistribution_weight (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} * w t ≤ 2 * C₁ * highI t * whigh t := by
    dsimp only [w, whigh]
    calc
      μ {x | t < T f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
          μ {x | t / 2 < T (high t) x} * ENNReal.ofReal (t ^ (p - 1)) :=
        mul_le_mul_of_nonneg_right (hdistribution t ht) (by simp)
      _ ≤ 2 * C₁ * highI t * ENNReal.ofReal (t ^ (p - 2)) := by
        simpa only [ENNReal.ofReal_rpow_of_pos ht] using
          (direct_weak_one_weighted (p := p) ht (hhigh_endpoint t ht))
      _ = 2 * C₁ * highI t * (ENNReal.ofReal t) ^ (p - 2) := by
        rw [ENNReal.ofReal_rpow_of_pos ht]
  /- The remaining three facts are, respectively, the measurable
  high-tail integral, the change of variables `t = 2s`, and layer cake.
  They remain explicit to expose the actual interpolation argument. -/
  have hdistribution_integral :
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) ≤
        ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hdistribution_weight t ht
  have hhigh_integral :
      (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
        2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
    let baseI : ℝ → ℝ≥0∞ := fun s =>
      ∫⁻ x in {x | s ≤ u x}, ENNReal.ofReal (u x) ∂μ
    have hbaseI_meas : Measurable baseI := by
      dsimp only [baseI]
      exact measurable_lintegral_indicator_le u hu _ hvhigh
    have hhigh_eq (t : ℝ) : highI t = baseI (t / 2) := rfl
    have hbase_tail :
        (∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2)) =
          (ENNReal.ofReal (p - 1))⁻¹ *
            ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
      calc
        (∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2)) =
            ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal t) ^ (p - 2) * baseI t := by
              apply lintegral_congr
              intro t
              exact mul_comm _ _
        _ = ∫⁻ x, ENNReal.ofReal (u x) *
            (∫⁻ t in Ioc (0 : ℝ) (u x), (ENNReal.ofReal t) ^ (p - 2)) ∂μ := by
              rw [lintegral_swap_indicator_le u hu _ hvhigh _ hwhigh]
        _ = (ENNReal.ofReal (p - 1))⁻¹ *
            ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
              exact lintegral_ofReal_mul_lintegral_rpow_Ioc_eq u hu hu_nonneg hp
    have hcoefficient :
        (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - 2)) *
            ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) =
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) := by
      have htwo0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
      have htwoT : ENNReal.ofReal (2 : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
      have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) =
          (ENNReal.ofReal (2 : ℝ))⁻¹ := by
        convert ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
      have hinvhalf : ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) = ENNReal.ofReal (2 : ℝ) := by
        norm_num
      rw [hhalf, hinvhalf, ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
      calc
        (ENNReal.ofReal (2 : ℝ)) ^ (p - 2) * ENNReal.ofReal (2 : ℝ) =
            (ENNReal.ofReal (2 : ℝ)) ^ (p - 2) *
              (ENNReal.ofReal (2 : ℝ)) ^ (1 : ℝ) := by
              rw [ENNReal.rpow_one]
        _ = (ENNReal.ofReal (2 : ℝ)) ^ ((p - 2) + 1) :=
          (ENNReal.rpow_add (p - 2) 1 htwo0 htwoT).symm
        _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) := by
          congr 1
          ring
    have hscale :
        (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) =
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
            ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2) := by
      calc
        (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) =
            ∫⁻ t in Ioi (0 : ℝ),
              baseI (((1 : ℝ) / 2) * t) * (ENNReal.ofReal t) ^ (p - 2) := by
              apply lintegral_congr
              intro t
              rw [hhigh_eq]
              dsimp only [whigh]
              congr 2
              ring
        _ = (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - 2)) *
            (ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) *
              ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2)) :=
              lintegral_Ioi_comp_mul_weight baseI hbaseI_meas ((1 : ℝ) / 2)
                (by norm_num) (p - 2)
        _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
            ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2) := by
              calc
                (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - 2)) *
                    (ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) *
                      ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2)) =
                    ((ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - 2)) *
                      ENNReal.ofReal (((1 : ℝ) / 2)⁻¹)) *
                        ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2) := by
                          ac_rfl
                _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
                    ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2) := by
                      rw [hcoefficient]
    calc
      (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
          (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := by
            have hconst :
                (∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highI t * whigh t)) =
                  (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) :=
              lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
                (2 * C₁) (hhighI_meas.mul hwhigh)
            calc
              (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
                  ∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highI t * whigh t) := by
                    apply lintegral_congr
                    intro t
                    ac_rfl
              _ = (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := hconst
      _ = (2 * C₁) * ((ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2)) := by
            rw [hscale]
      _ = 2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
            rw [hbase_tail]
            ac_rfl
  have hp_pos : 0 < p := by linarith
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) := by
      simpa only [w] using
        (lintegral_rpow_eq_lintegral_meas_lt_mul μ
          (Filter.Eventually.of_forall (hT_nonneg f)) hTf hp_pos)
    _ ≤ ENNReal.ofReal p *
        (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) :=
      mul_le_mul_right hdistribution_integral _
    _ = ENNReal.ofReal p *
        (2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by rw [hhigh_integral]
    _ = ENNReal.ofReal p *
        (2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) := by rfl

private theorem rpow_mul_lintegral_rpow_Ioc_eq
    {u q p : ℝ} (hu : 0 ≤ u) (hq : 0 < q) (hqp : 0 < p - q) :
    (ENNReal.ofReal u) ^ q *
      (∫⁻ t in Ioc (0 : ℝ) u,
        (ENNReal.ofReal t) ^ (p - q - 1)) =
      (ENNReal.ofReal (p - q))⁻¹ * (ENNReal.ofReal u) ^ p := by
  have hr : 1 < p - q + 1 := by linarith
  rw [show p - q - 1 = (p - q + 1) - 2 by ring]
  rw [lintegral_rpow_Ioc_eq hr hu]
  rw [show p - q + 1 - 1 = p - q by ring]
  rcases hu.eq_or_lt with rfl | hu
  · have hp : 0 < p := by linarith
    simp only [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq,
      zero_mul, ENNReal.zero_rpow_of_pos hp, mul_zero]
  rw [ENNReal.ofReal_div_of_pos hqp]
  rw [← ENNReal.ofReal_rpow_of_pos hu]
  have hu0 : ENNReal.ofReal u ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hu
  have hutop : ENNReal.ofReal u ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [div_eq_mul_inv]
  calc
    ENNReal.ofReal u ^ q *
        (ENNReal.ofReal u ^ (p - q) * (ENNReal.ofReal (p - q))⁻¹) =
        (ENNReal.ofReal u ^ q * ENNReal.ofReal u ^ (p - q)) *
          (ENNReal.ofReal (p - q))⁻¹ := by ac_rfl
    _ = ENNReal.ofReal u ^ p * (ENNReal.ofReal (p - q))⁻¹ := by
      rw [← ENNReal.rpow_add _ _ hu0 hutop]
      congr 1
      ring
    _ = (ENNReal.ofReal (p - q))⁻¹ * ENNReal.ofReal u ^ p := by ac_rfl

/-- The exact high-amplitude tail identity behind weak `(q,q)`--`L∞`
interpolation.  It is valid for every `0 < q < p`; the split at `t / 2`
is an amplitude threshold, not a restriction on the range of `p`. -/
theorem lintegral_high_tail_rpow_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (hu_nonneg : ∀ x, 0 ≤ u x)
    {q p : ℝ} (hq : 0 < q) (hqp : q < p) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t / 2 ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ) *
        (ENNReal.ofReal t) ^ (p - q - 1)) =
      (ENNReal.ofReal (p - q))⁻¹ *
        (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
  let baseI : ℝ → ENNReal := fun s =>
    ∫⁻ x in {x | s ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ
  let highI : ℝ → ENNReal := fun t =>
    ∫⁻ x in {x | t / 2 ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ
  let whigh : ℝ → ENNReal := fun t =>
    (ENNReal.ofReal t) ^ (p - q - 1)
  have hqp0 : 0 < p - q := sub_pos.mpr hqp
  have hv : Measurable (fun x => (ENNReal.ofReal (u x)) ^ q) :=
    ENNReal.continuous_rpow_const.measurable.comp hu.ennreal_ofReal
  have hbaseI_meas : Measurable baseI := by
    dsimp only [baseI]
    exact measurable_lintegral_indicator_le (μ := μ) u hu _ hv
  have hwhigh : Measurable whigh := by
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hbase_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        baseI t * (ENNReal.ofReal t) ^ (p - q - 1)) =
        (ENNReal.ofReal (p - q))⁻¹ *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
    calc
      (∫⁻ t in Ioi (0 : ℝ),
        baseI t * (ENNReal.ofReal t) ^ (p - q - 1)) =
          ∫⁻ t in Ioi (0 : ℝ),
            (ENNReal.ofReal t) ^ (p - q - 1) * baseI t := by
              apply lintegral_congr
              intro t
              exact mul_comm _ _
      _ = ∫⁻ x, (ENNReal.ofReal (u x)) ^ q *
          (∫⁻ t in Ioc (0 : ℝ) (u x),
            (ENNReal.ofReal t) ^ (p - q - 1)) ∂μ := by
              rw [lintegral_swap_indicator_le (μ := μ) u hu _ hv _ hwhigh]
      _ = (ENNReal.ofReal (p - q))⁻¹ *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
            rw [show (fun x => (ENNReal.ofReal (u x)) ^ q *
                (∫⁻ t in Ioc (0 : ℝ) (u x),
                  (ENNReal.ofReal t) ^ (p - q - 1))) =
                fun x => (ENNReal.ofReal (p - q))⁻¹ *
                  (ENNReal.ofReal (u x)) ^ p by
              funext x
              exact rpow_mul_lintegral_rpow_Ioc_eq (hu_nonneg x) hq hqp0]
            exact lintegral_const_mul (μ := μ) _
              (ENNReal.continuous_rpow_const.measurable.comp hu.ennreal_ofReal)
  have hcoefficient :
      (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
          ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) =
        (ENNReal.ofReal (2 : ℝ)) ^ (p - q) := by
    have htwo0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
    have htwoT : ENNReal.ofReal (2 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) =
        (ENNReal.ofReal (2 : ℝ))⁻¹ := by
      convert ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;>
        norm_num
    have hinvhalf : ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) = ENNReal.ofReal (2 : ℝ) := by
      norm_num
    rw [hhalf, hinvhalf, ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
    calc
      (ENNReal.ofReal (2 : ℝ)) ^ (p - q - 1) * ENNReal.ofReal (2 : ℝ) =
          (ENNReal.ofReal (2 : ℝ)) ^ (p - q - 1) *
            (ENNReal.ofReal (2 : ℝ)) ^ (1 : ℝ) := by
              rw [ENNReal.rpow_one]
      _ = (ENNReal.ofReal (2 : ℝ)) ^ ((p - q - 1) + 1) :=
        (ENNReal.rpow_add (p - q - 1) 1 htwo0 htwoT).symm
      _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) := by
        congr 1
        ring
  have hscale :
      (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) =
        (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
          ∫⁻ t in Ioi (0 : ℝ),
            baseI t * (ENNReal.ofReal t) ^ (p - q - 1) := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) =
          ∫⁻ t in Ioi (0 : ℝ),
            baseI (((1 : ℝ) / 2) * t) *
              (ENNReal.ofReal t) ^ (p - q - 1) := by
            apply lintegral_congr
            intro t
            change baseI (t / 2) * (ENNReal.ofReal t) ^ (p - q - 1) = _
            congr 2
            ring
      _ = (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
          (ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) *
            ∫⁻ t in Ioi (0 : ℝ),
              baseI t * (ENNReal.ofReal t) ^ (p - q - 1)) :=
        lintegral_Ioi_comp_mul_weight baseI hbaseI_meas ((1 : ℝ) / 2)
          (by norm_num) (p - q - 1)
      _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
          ∫⁻ t in Ioi (0 : ℝ),
            baseI t * (ENNReal.ofReal t) ^ (p - q - 1) := by
          calc
            (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
                (ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) *
                  ∫⁻ t in Ioi (0 : ℝ),
                    baseI t * (ENNReal.ofReal t) ^ (p - q - 1)) =
                ((ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
                  ENNReal.ofReal (((1 : ℝ) / 2)⁻¹)) *
                    ∫⁻ t in Ioi (0 : ℝ),
                      baseI t * (ENNReal.ofReal t) ^ (p - q - 1) := by ac_rfl
            _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
                ∫⁻ t in Ioi (0 : ℝ),
                  baseI t * (ENNReal.ofReal t) ^ (p - q - 1) := by
              rw [hcoefficient]
  calc
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t / 2 ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ) *
        (ENNReal.ofReal t) ^ (p - q - 1)) =
        ∫⁻ t in Ioi (0 : ℝ), highI t * whigh t := by rfl
    _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
        ∫⁻ t in Ioi (0 : ℝ),
          baseI t * (ENNReal.ofReal t) ^ (p - q - 1) := hscale
    _ = (ENNReal.ofReal (p - q))⁻¹ *
        (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
      rw [hbase_tail]
      ac_rfl

private theorem ofReal_rpow_weight_q {q p t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) =
      (ENNReal.ofReal (2 : ℝ)) ^ q *
        ((ENNReal.ofReal (t / 2)) ^ q *
          ENNReal.ofReal (t ^ (p - q - 1))) := by
  have hreal : t ^ (p - 1) =
      2 ^ q * ((t / 2) ^ q * t ^ (p - q - 1)) := by
    calc
      t ^ (p - 1) = t ^ q * t ^ (p - q - 1) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      _ = (2 * (t / 2)) ^ q * t ^ (p - q - 1) := by
        congr 2
        ring
      _ = 2 ^ q * ((t / 2) ^ q * t ^ (p - q - 1)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        ring
  calc
    ENNReal.ofReal (t ^ (p - 1)) =
        ENNReal.ofReal (2 ^ q * ((t / 2) ^ q * t ^ (p - q - 1))) :=
      congrArg ENNReal.ofReal hreal
    _ = (ENNReal.ofReal (2 : ℝ)) ^ q *
        ((ENNReal.ofReal (t / 2)) ^ q *
          ENNReal.ofReal (t ^ (p - q - 1))) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [← ENNReal.ofReal_rpow_of_pos (by positivity : 0 < t / 2)]

private theorem direct_weak_q_weighted
    {q p t : ℝ} {m C I : ENNReal} (ht : 0 < t)
    (h : (ENNReal.ofReal (t / 2)) ^ q * m ≤ C * I) :
    m * ENNReal.ofReal (t ^ (p - 1)) ≤
      (ENNReal.ofReal (2 : ℝ)) ^ q * C * I *
        ENNReal.ofReal (t ^ (p - q - 1)) := by
  rw [ofReal_rpow_weight_q ht]
  calc
    m * ((ENNReal.ofReal (2 : ℝ)) ^ q *
        ((ENNReal.ofReal (t / 2)) ^ q *
          ENNReal.ofReal (t ^ (p - q - 1)))) =
        ((ENNReal.ofReal (t / 2)) ^ q * m) *
          ((ENNReal.ofReal (2 : ℝ)) ^ q *
            ENNReal.ofReal (t ^ (p - q - 1))) := by ac_rfl
    _ ≤ (C * I) * ((ENNReal.ofReal (2 : ℝ)) ^ q *
          ENNReal.ofReal (t ^ (p - q - 1))) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = (ENNReal.ofReal (2 : ℝ)) ^ q * C * I *
          ENNReal.ofReal (t ^ (p - q - 1)) := by ac_rfl

/-- The weak `(q,q)`--`L∞` Marcinkiewicz step with a supplied additive
amplitude split.  This form applies directly to operators whose domain is a
stable test-function class, such as Schwartz maps. -/
private theorem marcinkiewicz_weak_q_top_on_additive_split
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (q : ℝ) (hq : 0 < q) (Cq : ENNReal)
    (hweak_q : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      (ENNReal.ofReal s) ^ q * μ {x | s < T g x} ≤
        Cq * (∫⁻ x, (ENNReal.ofReal ‖eval g x‖) ^ q ∂μ))
    (hT_top : ∀ (g : F), g ∈ D → ∀ (a : ℝ), 0 ≤ a →
      (∀ x, ‖eval g x‖ ≤ a) → ∀ x, T g x ≤ a)
    {p : ℝ} (hqp : q < p)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlow_norm : ∀ t, 0 < t → ∀ x, ‖eval (low t) x‖ ≤ t / 2)
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ))
    (Aq : ENNReal)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ) *
          (ENNReal.ofReal t) ^ (p - q - 1)) ≤ Aq) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p * ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq * Aq) := by
  let highI : ℝ → ENNReal := fun t =>
    ∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ
  let w : ℝ → ENNReal := fun t => ENNReal.ofReal (t ^ (p - 1))
  let whigh : ℝ → ENNReal := fun t =>
    (ENNReal.ofReal t) ^ (p - q - 1)
  have hp : 0 < p := hq.trans hqp
  have hlow_bound (t : ℝ) (ht : 0 < t) (x : α) :
      T (low t) x ≤ t / 2 := by
    apply hT_top (low t) (hlow_mem t) (t / 2) (by positivity)
    exact hlow_norm t ht
  have hdistribution (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} ≤ μ {x | t / 2 < T (high t) x} := by
    apply measure_mono
    intro x hx
    rw [hsplit t] at hx
    have hsum := hT_subadd (hlow_mem t) (hhigh_mem t) x
    have hlow := hlow_bound t ht x
    by_contra h
    have hhigh : T (high t) x ≤ t / 2 := le_of_not_gt h
    have : T (low t + high t) x ≤ t := by
      calc
        T (low t + high t) x ≤ T (low t) x + T (high t) x := hsum
        _ ≤ t / 2 + t / 2 := add_le_add hlow hhigh
        _ = t := by ring
    exact (not_lt_of_ge this) hx
  have hhigh_endpoint (t : ℝ) (ht : 0 < t) :
      (ENNReal.ofReal (t / 2)) ^ q * μ {x | t / 2 < T (high t) x} ≤
        Cq * highI t := by
    simpa only [highI] using hweak_q (high t) (hhigh_mem t) (by positivity)
  have hdistribution_weight (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} * w t ≤
        (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t := by
    dsimp only [w, whigh]
    calc
      μ {x | t < T f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
          μ {x | t / 2 < T (high t) x} * ENNReal.ofReal (t ^ (p - 1)) :=
        mul_le_mul_of_nonneg_right (hdistribution t ht) (by simp)
      _ ≤ (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t *
          ENNReal.ofReal (t ^ (p - q - 1)) := by
        exact direct_weak_q_weighted ht (hhigh_endpoint t ht)
      _ = (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t *
          (ENNReal.ofReal t) ^ (p - q - 1) := by
        rw [ENNReal.ofReal_rpow_of_pos ht]
  have hdistribution_integral :
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) ≤
        ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hdistribution_weight t ht
  have hhigh_tail' :
      (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) ≤ Aq := by
    simpa only [highI, whigh] using hhigh_tail
  have hhigh_integral :
      (∫⁻ t in Ioi (0 : ℝ),
        (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t) ≤
          (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * Aq := by
    calc
      (∫⁻ t in Ioi (0 : ℝ),
        (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t) =
          ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq) *
            (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := by
          have hconst :
              (∫⁻ t in Ioi (0 : ℝ),
                ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq) * (highI t * whigh t)) =
                ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq) *
                  (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) :=
            lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ))) _
              (hhighI_meas.mul
                (ENNReal.continuous_rpow_const.measurable.comp
                  measurable_id.ennreal_ofReal))
          calc
            (∫⁻ t in Ioi (0 : ℝ),
              (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t) =
                ∫⁻ t in Ioi (0 : ℝ),
                  ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq) * (highI t * whigh t) := by
                    apply lintegral_congr
                    intro t
                    ac_rfl
            _ = ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq) *
                (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := hconst
      _ ≤ (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * Aq :=
        mul_le_mul_of_nonneg_left hhigh_tail' (by positivity)
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) := by
      simpa only [w] using
        (lintegral_rpow_eq_lintegral_meas_lt_mul μ
          (Filter.Eventually.of_forall (hT_nonneg f)) hTf hp)
    _ ≤ ENNReal.ofReal p *
        (∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t) :=
      mul_le_mul_right hdistribution_integral _
    _ ≤ ENNReal.ofReal p * ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq * Aq) :=
      mul_le_mul_of_nonneg_left hhigh_integral (by positivity)

private theorem ofReal_q_top_coefficient
    {p q C A : ℝ} (hp : 0 ≤ p) (hA : 0 ≤ A) :
    ENNReal.ofReal p * ((ENNReal.ofReal (2 : ℝ)) ^ q *
        ENNReal.ofReal C * ENNReal.ofReal A) =
      ENNReal.ofReal (p * 2 ^ q * C * A) := by
  have htwoq : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
  calc
    ENNReal.ofReal p * ((ENNReal.ofReal (2 : ℝ)) ^ q *
        ENNReal.ofReal C * ENNReal.ofReal A) =
        ENNReal.ofReal p * (ENNReal.ofReal ((2 : ℝ) ^ q) *
          ENNReal.ofReal (C * A)) := by
          rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
          rw [ENNReal.ofReal_mul' hA]
          ac_rfl
    _ = ENNReal.ofReal p * ENNReal.ofReal ((2 : ℝ) ^ q * (C * A)) := by
      rw [ENNReal.ofReal_mul htwoq]
    _ = ENNReal.ofReal (p * ((2 : ℝ) ^ q * (C * A))) := by
      rw [ENNReal.ofReal_mul hp]
    _ = ENNReal.ofReal (p * 2 ^ q * C * A) := by ring

/-- A real-constant supplied-split weak `(q,q)`--`L∞` interpolation bound.
Its conclusion keeps the coefficient inside `ENNReal.ofReal`, so dyadic
balancing can be done entirely in `ℝ`. -/
theorem marcinkiewicz_weak_q_top_on_additive_split_real
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (q : ℝ) (hq : 0 < q) (Cq : ℝ)
    (hweak_q : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      (ENNReal.ofReal s) ^ q * μ {x | s < T g x} ≤
        ENNReal.ofReal Cq * (∫⁻ x, (ENNReal.ofReal ‖eval g x‖) ^ q ∂μ))
    (hT_top : ∀ (g : F), g ∈ D → ∀ (a : ℝ), 0 ≤ a →
      (∀ x, ‖eval g x‖ ≤ a) → ∀ x, T g x ≤ a)
    {p : ℝ} (hqp : q < p)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlow_norm : ∀ t, 0 < t → ∀ x, ‖eval (low t) x‖ ≤ t / 2)
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ))
    (Aq : ℝ)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ) *
          (ENNReal.ofReal t) ^ (p - q - 1)) ≤ ENNReal.ofReal Aq)
    (hAq : 0 ≤ Aq) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal (p * 2 ^ q * Cq * Aq) := by
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
        ENNReal.ofReal p * ((ENNReal.ofReal (2 : ℝ)) ^ q *
          ENNReal.ofReal Cq * ENNReal.ofReal Aq) :=
      marcinkiewicz_weak_q_top_on_additive_split D eval T hT_nonneg hT_subadd
        q hq (ENNReal.ofReal Cq) hweak_q hT_top hqp f hTf low high hlow_mem hhigh_mem
        hsplit hlow_norm hhighI_meas (ENNReal.ofReal Aq) hhigh_tail
    _ = ENNReal.ofReal (p * 2 ^ q * Cq * Aq) :=
      ofReal_q_top_coefficient (le_of_lt (hq.trans hqp)) hAq

/-- The supplied-split weak `(q,q)`--`L∞` estimate with an explicit
`L∞` constant.  Normalizing the operator by that constant gives the
factor `Ctop ^ (p - q)` in the conclusion. -/
theorem marcinkiewicz_weak_q_top_on_additive_split_real_top_scaled
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (q : ℝ) (hq : 0 < q) (Cq Ctop : ℝ)
    (hCtop : 0 < Ctop)
    (hweak_q : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      (ENNReal.ofReal s) ^ q * μ {x | s < T g x} ≤
        ENNReal.ofReal Cq * (∫⁻ x, (ENNReal.ofReal ‖eval g x‖) ^ q ∂μ))
    (hT_top : ∀ (g : F), g ∈ D → ∀ (a : ℝ), 0 ≤ a →
      (∀ x, ‖eval g x‖ ≤ a) → ∀ x, T g x ≤ Ctop * a)
    {p : ℝ} (hqp : q < p)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlow_norm : ∀ t, 0 < t → ∀ x, ‖eval (low t) x‖ ≤ t / 2)
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ))
    (Aq : ℝ)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ) *
          (ENNReal.ofReal t) ^ (p - q - 1)) ≤ ENNReal.ofReal Aq)
    (hAq : 0 ≤ Aq) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal (p * 2 ^ q * Cq * Aq * Ctop ^ (p - q)) := by
  let S : F → α → ℝ := fun g x => T g x / Ctop
  have hS_nonneg : ∀ g x, 0 ≤ S g x := by
    intro g x
    exact div_nonneg (hT_nonneg g x) hCtop.le
  have hS_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, S (g + h) x ≤ S g x + S h x := by
    intro g h hg hh x
    change T (g + h) x / Ctop ≤ T g x / Ctop + T h x / Ctop
    rw [← add_div]
    exact div_le_div_of_nonneg_right (hT_subadd hg hh x) hCtop.le
  have hlevel (g : F) (s : ℝ) :
      {x | s < S g x} = {x | Ctop * s < T g x} := by
    ext x
    change s < T g x / Ctop ↔ Ctop * s < T g x
    constructor
    · intro hx
      have hx' := (lt_div_iff₀ hCtop).mp hx
      simpa [mul_comm] using hx'
    · intro hx
      apply (lt_div_iff₀ hCtop).mpr
      simpa [mul_comm] using hx
  have hS_weak : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      (ENNReal.ofReal s) ^ q * μ {x | s < S g x} ≤
        ENNReal.ofReal (Cq / Ctop ^ q) *
          (∫⁻ x, (ENNReal.ofReal ‖eval g x‖) ^ q ∂μ) := by
    intro g hg s hs
    have hbase := hweak_q g hg (mul_pos hCtop hs)
    rw [← hlevel g s] at hbase
    let b : ENNReal := ENNReal.ofReal Ctop
    let v : ENNReal := (ENNReal.ofReal s) ^ q
    let m : ENNReal := μ {x | s < S g x}
    let I : ENNReal := ∫⁻ x, (ENNReal.ofReal ‖eval g x‖) ^ q ∂μ
    have hb0 : b ^ q ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hCtop)
      ENNReal.ofReal_ne_top).ne'
    have hbtop : b ^ q ≠ ⊤ := by
      rw [ENNReal.ofReal_rpow_of_pos hCtop]
      exact ENNReal.ofReal_ne_top
    have hbase' : (b ^ q * v) * m ≤ ENNReal.ofReal Cq * I := by
      rw [ENNReal.ofReal_mul hCtop.le,
        ENNReal.mul_rpow_of_nonneg _ _ hq.le] at hbase
      simpa only [b, v, m, I] using hbase
    have hmain : v * m ≤ (b ^ q)⁻¹ * ENNReal.ofReal Cq * I := by
      calc
        v * m = ((b ^ q)⁻¹ * b ^ q) * (v * m) := by
          rw [ENNReal.inv_mul_cancel hb0 hbtop, one_mul]
        _ = (b ^ q)⁻¹ * ((b ^ q * v) * m) := by ac_rfl
        _ ≤ (b ^ q)⁻¹ * (ENNReal.ofReal Cq * I) :=
          mul_le_mul_of_nonneg_left hbase' (by positivity)
        _ = (b ^ q)⁻¹ * ENNReal.ofReal Cq * I := by ac_rfl
    change v * m ≤ ENNReal.ofReal (Cq / Ctop ^ q) * I
    rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hCtop _)]
    rw [← ENNReal.ofReal_rpow_of_pos hCtop]
    rw [div_eq_mul_inv]
    simpa [mul_comm] using hmain
  have hS_top : ∀ (g : F), g ∈ D → ∀ (a : ℝ), 0 ≤ a →
      (∀ x, ‖eval g x‖ ≤ a) → ∀ x, S g x ≤ a := by
    intro g hg a ha hnorm x
    change T g x / Ctop ≤ a
    rw [div_le_iff₀ hCtop]
    simpa [mul_comm] using hT_top g hg a ha hnorm x
  have hS_meas : AEMeasurable (S f) μ := by
    change AEMeasurable (fun x => T f x / Ctop) μ
    exact hTf.div_const Ctop
  have hSbound := marcinkiewicz_weak_q_top_on_additive_split_real D eval S
    hS_nonneg hS_subadd q hq (Cq / Ctop ^ q) hS_weak hS_top hqp f hS_meas low high
    hlow_mem hhigh_mem hsplit hlow_norm hhighI_meas Aq hhigh_tail hAq
  have hp : 0 < p := hq.trans hqp
  have hTS (x : α) : T f x = Ctop * S f x := by
    change T f x = Ctop * (T f x / Ctop)
    field_simp
  have hpoint (x : α) :
      ENNReal.ofReal ((T f x) ^ p) =
        (ENNReal.ofReal Ctop) ^ p * ENNReal.ofReal ((S f x) ^ p) := by
    rw [hTS x, Real.mul_rpow hCtop.le (hS_nonneg f x),
      ENNReal.ofReal_mul (Real.rpow_nonneg hCtop.le _),
      ← ENNReal.ofReal_rpow_of_pos hCtop]
  have hscale :
      (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        (ENNReal.ofReal Ctop) ^ p *
          (∫⁻ x, ENNReal.ofReal ((S f x) ^ p) ∂μ) := by
    calc
      (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
          ∫⁻ x, (ENNReal.ofReal Ctop) ^ p * ENNReal.ofReal ((S f x) ^ p) ∂μ := by
            apply lintegral_congr
            intro x
            exact hpoint x
      _ = (ENNReal.ofReal Ctop) ^ p *
          (∫⁻ x, ENNReal.ofReal ((S f x) ^ p) ∂μ) :=
            lintegral_const_mul' _ _
              (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
  have hreal : Ctop ^ p *
      (p * 2 ^ q * (Cq / Ctop ^ q) * Aq) =
        p * 2 ^ q * Cq * Aq * Ctop ^ (p - q) := by
    rw [Real.rpow_sub hCtop p q]
    field_simp
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        (ENNReal.ofReal Ctop) ^ p *
          (∫⁻ x, ENNReal.ofReal ((S f x) ^ p) ∂μ) := hscale
    _ ≤ (ENNReal.ofReal Ctop) ^ p *
        ENNReal.ofReal (p * 2 ^ q * (Cq / Ctop ^ q) * Aq) :=
      mul_le_mul_of_nonneg_left hSbound (by positivity)
    _ = ENNReal.ofReal (p * 2 ^ q * Cq * Aq * Ctop ^ (p - q)) := by
      rw [ENNReal.ofReal_rpow_of_pos hCtop,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hCtop.le _)]
      exact congrArg ENNReal.ofReal hreal

/-! The following scaled form is the version used when the threshold in a
Calderón--Zygmund decomposition is chosen independently of the distribution
parameter.  It simply applies the preceding weak-endpoint interpolation
argument to the actual split at `s * t`, and records the resulting change of
variables in the two displayed tails. -/
theorem marcinkiewicz_weak_one_two_on_additive_split_scaled
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (C₁ C₂ : ENNReal)
    (hweak_one : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * μ {x | s < T g x} ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖eval g x‖ ∂μ))
    (hweak_two : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖eval g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlowI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ))
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ))
    (A₂ A₁ : ENNReal)
    (hlow_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) ≤ A₂)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) ≤ A₁)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        (4 * C₂ * ((ENNReal.ofReal s) ^ (2 - p) * A₂) +
          2 * C₁ * ((ENNReal.ofReal s) ^ (1 - p) * A₁)) := by
  apply marcinkiewicz_weak_one_two_on_additive_split D eval T hT_nonneg hT_subadd C₁ C₂
    hweak_one hweak_two hp1 hp2 f hTf (fun t => low (s * t)) (fun t => high (s * t))
    ?_ ?_ ?_ ?_ ?_ ((ENNReal.ofReal s) ^ (2 - p) * A₂)
    ((ENNReal.ofReal s) ^ (1 - p) * A₁) ?_ ?_
  · intro t
    exact hlow_mem (s * t)
  · intro t
    exact hhigh_mem (s * t)
  · intro t
    exact hsplit (s * t)
  · change Measurable ((fun r : ℝ =>
        ∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ) ∘
        fun t : ℝ => s * t)
    exact hlowI_meas.comp (measurable_const_mul s)
  · change Measurable ((fun r : ℝ =>
        ∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ) ∘ fun t : ℝ => s * t)
    exact hhighI_meas.comp (measurable_const_mul s)
  · calc
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low (s * t)) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) =
          (ENNReal.ofReal s) ^ (2 - p) *
            (∫⁻ r in Ioi (0 : ℝ),
              (∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ) *
                (ENNReal.ofReal r) ^ (p - 3)) :=
        lintegral_Ioi_comp_mul_low_weight
          (fun r => ∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ)
          hlowI_meas s hs p
      _ ≤ (ENNReal.ofReal s) ^ (2 - p) * A₂ := by
        exact mul_le_mul_right hlow_tail _
  · calc
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high (s * t)) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) =
          (ENNReal.ofReal s) ^ (1 - p) *
            (∫⁻ r in Ioi (0 : ℝ),
              (∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ) *
                (ENNReal.ofReal r) ^ (p - 2)) :=
        lintegral_Ioi_comp_mul_high_weight
          (fun r => ∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ)
          hhighI_meas s hs p
      _ ≤ (ENNReal.ofReal s) ^ (1 - p) * A₁ := by
        exact mul_le_mul_right hhigh_tail _

end LeanSpherical.HarmonicAnalysis
