/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.InterpolationTail
import LeanSpherical.HarmonicAnalysis.SchwartzData
import LeanSpherical.HarmonicAnalysis.SphericalAverages
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Rational tails and smooth dyadic spherical `L¹` estimates

This module collects the rational amplitude tail estimates and the local
smooth dyadic spherical maximal endpoint used by interpolation.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Set ENNReal

noncomputable section

/-- The two-region low-amplitude estimate gives its exact weighted Tonelli
tail.  This is the lower `L²` tail used by the rational truncation in the
`L¹`/`L²` interpolation argument. -/
theorem weighted_low_tail_le_of_two_region_bounds
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (low : ℝ → α → E)
    (hlow_small : ∀ t x, 0 < t → t ≤ u x →
      ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ≤ ENNReal.ofReal (t ^ (2 : ℕ) / 4))
    (hlow_large : ∀ t x, 0 < t → u x < t →
      ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ≤ ENNReal.ofReal ((u x) ^ (2 : ℕ)))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) *
        (ENNReal.ofReal t) ^ (p - 3)) ≤
      ((ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹ +
          (ENNReal.ofReal (2 - p))⁻¹) *
        ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
  let w : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 3)
  let a : ℝ → α → ℝ≥0∞ := fun t x =>
    ({x | t ≤ u x}).indicator (fun _ => ENNReal.ofReal (t ^ (2 : ℕ) / 4)) x
  let b : ℝ → α → ℝ≥0∞ := fun t x =>
    ({x | u x < t}).indicator (fun x => ENNReal.ofReal ((u x) ^ (2 : ℕ))) x
  have hw : Measurable w := by
    exact ENNReal.continuous_rpow_const.measurable.comp
      ENNReal.continuous_ofReal.measurable
  have ha_meas : Measurable (Function.uncurry a) := by
    change Measurable (({q : ℝ × α | q.1 ≤ u q.2}).indicator
      (fun q : ℝ × α => ENNReal.ofReal (q.1 ^ (2 : ℕ) / 4)))
    exact (ENNReal.continuous_ofReal.measurable.comp
      ((measurable_fst.pow_const 2).div_const 4)).indicator
      (measurableSet_le measurable_fst (hu.comp measurable_snd))
  have haI_meas : Measurable (fun t : ℝ => ∫⁻ x, a t x ∂μ) :=
    Measurable.lintegral_prod_right ha_meas
  have hbound (t : ℝ) (ht : 0 < t) :
      (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) ≤
        (∫⁻ x, a t x + b t x ∂μ) := by
    apply lintegral_mono
    intro x
    change ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ≤ a t x + b t x
    by_cases htx : t ≤ u x
    · have h1 := hlow_small t x ht htx
      rw [show a t x = ENNReal.ofReal (t ^ (2 : ℕ) / 4) by simp [a, htx]]
      rw [show b t x = 0 by simp [b, not_lt_of_ge htx]]
      simpa using h1
    · have htx' : u x < t := lt_of_not_ge htx
      rw [show a t x = 0 by simp [a, htx]]
      rw [show b t x = ENNReal.ofReal ((u x) ^ (2 : ℕ)) by simp [b, htx']]
      simpa using hlow_large t x ht htx'
  have houter :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) * w t) ≤
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, a t x + b t x ∂μ) * w t) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) * w t =
          w t * (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) := mul_comm _ _
      _ ≤ w t * (∫⁻ x, a t x + b t x ∂μ) := mul_le_mul_right (hbound t ht) _
      _ = (∫⁻ x, a t x + b t x ∂μ) * w t := mul_comm _ _
  have hsq_div_four (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (t ^ (2 : ℕ) / 4) =
        ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal t) ^ (2 : ℕ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    rw [ENNReal.ofReal_pow ht.le]
    rw [show ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) by
      norm_num [ENNReal.ofReal_natCast]]
    rw [show ENNReal.ofReal ((1 : ℝ) / 4) = (4 : ℝ≥0∞)⁻¹ by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num [ENNReal.ofReal_natCast]]
    rw [div_eq_mul_inv]
    ac_rfl
  have hat_meas (t : ℝ) : Measurable (a t) := by
    change Measurable (({x | t ≤ u x}).indicator
      (fun _ : α => ENNReal.ofReal (t ^ (2 : ℕ) / 4)))
    exact measurable_const.indicator (measurableSet_le measurable_const hu)
  have houter_split :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, a t x + b t x ∂μ) * w t) =
      (∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, a t x ∂μ) * w t) +
        ∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, b t x ∂μ) * w t := by
    calc
      (∫⁻ t in Ioi (0 : ℝ),
          (∫⁻ x, a t x + b t x ∂μ) * w t) =
          ∫⁻ t in Ioi (0 : ℝ),
            ((∫⁻ x, a t x ∂μ) + (∫⁻ x, b t x ∂μ)) * w t := by
          apply lintegral_congr
          intro t
          rw [lintegral_add_left (hat_meas t)]
      _ = ∫⁻ t in Ioi (0 : ℝ),
          (∫⁻ x, a t x ∂μ) * w t + (∫⁻ x, b t x ∂μ) * w t := by
          apply lintegral_congr
          intro t
          rw [add_mul]
      _ = _ := lintegral_add_left (haI_meas.mul hw) _
  let wa : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal t) ^ (p - 1)
  have hwa : Measurable wa := by
    exact measurable_const.mul
      (ENNReal.continuous_rpow_const.measurable.comp
        ENNReal.continuous_ofReal.measurable)
  have ha_inner (t : ℝ) (ht : 0 < t) :
      (∫⁻ x, a t x ∂μ) * w t =
        wa t * ∫⁻ x in {x | t ≤ u x}, (1 : ℝ≥0∞) ∂μ := by
    have htzero : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
    have httop : ENNReal.ofReal t ≠ ∞ := ENNReal.ofReal_ne_top
    have hpows : (ENNReal.ofReal t) ^ (2 : ℕ) *
        (ENNReal.ofReal t) ^ (p - 3) = (ENNReal.ofReal t) ^ (p - 1) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ htzero httop]
      congr 1
      ring
    change (∫⁻ x, ({x | t ≤ u x}).indicator
      (fun _ => ENNReal.ofReal (t ^ (2 : ℕ) / 4)) x ∂μ) * w t = _
    rw [lintegral_indicator (measurableSet_le measurable_const hu)]
    have hconst :
        (∫⁻ x in {x | t ≤ u x}, ENNReal.ofReal (t ^ (2 : ℕ) / 4) ∂μ) =
          ENNReal.ofReal (t ^ (2 : ℕ) / 4) *
            (∫⁻ x in {x | t ≤ u x}, (1 : ℝ≥0∞) ∂μ) := by
      rw [← lintegral_const_mul _ measurable_const]
      apply lintegral_congr
      intro x
      simp
    rw [hconst, hsq_div_four t ht]
    change (ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal t) ^ (2 : ℕ) *
        (∫⁻ x in {x | t ≤ u x}, (1 : ℝ≥0∞) ∂μ)) *
        (ENNReal.ofReal t) ^ (p - 3) = _
    change (ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal t) ^ (2 : ℕ) *
        (∫⁻ x in {x | t ≤ u x}, (1 : ℝ≥0∞) ∂μ)) *
        (ENNReal.ofReal t) ^ (p - 3) =
      (ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal t) ^ (p - 1)) *
        (∫⁻ x in {x | t ≤ u x}, (1 : ℝ≥0∞) ∂μ)
    calc
      _ = ENNReal.ofReal ((1 : ℝ) / 4) *
          ((ENNReal.ofReal t) ^ (2 : ℕ) * (ENNReal.ofReal t) ^ (p - 3)) *
          (∫⁻ x in {x | t ≤ u x}, (1 : ℝ≥0∞) ∂μ) := by ac_rfl
      _ = _ := by rw [hpows]
  have ha_outer :
      (∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, a t x ∂μ) * w t) =
        ∫⁻ t in Ioi (0 : ℝ),
          wa t * ∫⁻ x in {x | t ≤ u x}, (1 : ℝ≥0∞) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ha_inner t ht
  have hshift (v : ℝ) (hv : 0 ≤ v) :
      (∫⁻ t in Ioc (0 : ℝ) v, (ENNReal.ofReal t) ^ (p - 1)) =
        (ENNReal.ofReal p)⁻¹ * (ENNReal.ofReal v) ^ p := by
    have h := lintegral_rpow_Ioc_eq (p := p + 1) (u := v) (by linarith) hv
    have hpow : p + 1 - 2 = p - 1 := by ring
    rw [hpow] at h
    rw [h]
    have hp0 : 0 < p := by linarith
    rw [show p + 1 - 1 = p by ring]
    rw [ENNReal.ofReal_div_of_pos hp0]
    rw [ENNReal.ofReal_rpow_of_nonneg hv hp0.le]
    simp [div_eq_mul_inv, mul_comm]
  have hu_pow_meas : Measurable (fun x => (ENNReal.ofReal (u x)) ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hu.ennreal_ofReal
  have ha_eval :
      (∫⁻ t in Ioi (0 : ℝ),
        wa t * ∫⁻ x in {x | t ≤ u x}, (1 : ℝ≥0∞) ∂μ) =
        (ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹) *
          (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
    rw [lintegral_swap_indicator_le u hu (fun _ => (1 : ℝ≥0∞)) measurable_const wa hwa]
    calc
      (∫⁻ x, (1 : ℝ≥0∞) * (∫⁻ t in Ioc (0 : ℝ) (u x), wa t) ∂μ) =
          ∫⁻ x, (ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹) *
            (ENNReal.ofReal (u x)) ^ p ∂μ := by
          apply lintegral_congr
          intro x
          rw [one_mul]
          let r : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 1)
          have hr : Measurable r :=
            ENNReal.continuous_rpow_const.measurable.comp
              ENNReal.continuous_ofReal.measurable
          change (∫⁻ t in Ioc (0 : ℝ) (u x), ENNReal.ofReal ((1 : ℝ) / 4) * r t) = _
          rw [lintegral_const_mul
            (μ := volume.restrict (Ioc (0 : ℝ) (u x))) _ hr]
          change ENNReal.ofReal ((1 : ℝ) / 4) *
              (∫⁻ t in Ioc (0 : ℝ) (u x), (ENNReal.ofReal t) ^ (p - 1)) = _
          rw [hshift (u x) (hu_nonneg x)]
          ac_rfl
      _ = _ := lintegral_const_mul _ hu_pow_meas
  let v : α → ℝ≥0∞ := fun x => ENNReal.ofReal ((u x) ^ (2 : ℕ))
  have hv : Measurable v :=
    ENNReal.continuous_ofReal.measurable.comp (hu.pow_const 2)
  have hb_inner (t : ℝ) :
      (∫⁻ x, b t x ∂μ) * w t =
        w t * ∫⁻ x in {x | u x < t}, v x ∂μ := by
    change (∫⁻ x, ({x | u x < t}).indicator
      (fun x => ENNReal.ofReal ((u x) ^ (2 : ℕ))) x ∂μ) * w t = _
    rw [lintegral_indicator (measurableSet_lt hu measurable_const)]
    exact mul_comm _ _
  have hb_outer :
      (∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, b t x ∂μ) * w t) =
        ∫⁻ t in Ioi (0 : ℝ), w t * ∫⁻ x in {x | u x < t}, v x ∂μ := by
    apply lintegral_congr
    intro t
    exact hb_inner t
  have hb_eval :
      (∫⁻ t in Ioi (0 : ℝ),
        w t * ∫⁻ x in {x | u x < t}, v x ∂μ) =
        (ENNReal.ofReal (2 - p))⁻¹ *
          (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
    rw [lintegral_swap_indicator_lt u hu hu_nonneg v hv w hw]
    change (∫⁻ x, ENNReal.ofReal ((u x) ^ (2 : ℕ)) *
        (∫⁻ t in Ioi (u x), (ENNReal.ofReal t) ^ (p - 3)) ∂μ) = _
    rw [lintegral_ofReal_sq_mul_lintegral_rpow_Ioi_eq u hu hu_nonneg hp1 hp2]
  change (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) * w t) ≤ _
  calc
    (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) * w t) ≤
        ∫⁻ t in Ioi (0 : ℝ),
          (∫⁻ x, a t x + b t x ∂μ) * w t := houter
    _ = (∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, a t x ∂μ) * w t) +
          ∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, b t x ∂μ) * w t := houter_split
    _ = (ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹) *
          (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) +
        (ENNReal.ofReal (2 - p))⁻¹ *
          (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
          rw [ha_outer, ha_eval, hb_outer, hb_eval]
    _ = _ := by rw [add_mul]

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Set ENNReal

noncomputable section

theorem ofReal_high_weight_eq
    {u t p : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    ENNReal.ofReal (u ^ (3 : ℕ) / t ^ (2 : ℕ)) *
        (ENNReal.ofReal t) ^ (p - 2) =
      ENNReal.ofReal (u ^ (3 : ℕ)) * (ENNReal.ofReal t) ^ (p - 4) := by
  rw [ENNReal.ofReal_rpow_of_pos ht, ENNReal.ofReal_rpow_of_pos ht]
  rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hu 3) (sq_nonneg t))]
  rw [← ENNReal.ofReal_mul (pow_nonneg hu 3)]
  congr 1
  calc
    (u ^ (3 : ℕ) / t ^ (2 : ℕ)) * t ^ (p - 2) =
        u ^ (3 : ℕ) * (t ^ (p - 2) / t ^ (2 : ℕ)) := by ring
    _ = u ^ (3 : ℕ) * (t ^ (p - 2) / t ^ (2 : ℝ)) := by
      have hpow : t ^ (2 : ℕ) = t ^ (2 : ℝ) := (Real.rpow_natCast t 2).symm
      rw [hpow]
    _ = u ^ (3 : ℕ) * t ^ ((p - 2) - 2) := by
      rw [← Real.rpow_sub ht]
    _ = u ^ (3 : ℕ) * t ^ (p - 4) := by
      congr 2; ring

theorem rational_high_low_region_tail
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (hu_nonneg : ∀ x, 0 ≤ u x)
    {p : ℝ} (hp1 : 1 < p) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t ≤ u x}, ENNReal.ofReal (u x) ∂μ) *
        (ENNReal.ofReal t) ^ (p - 2)) =
      (ENNReal.ofReal (p - 1))⁻¹ *
        (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
  have huv : Measurable (fun x => ENNReal.ofReal (u x)) := hu.ennreal_ofReal
  have hw : Measurable (fun t : ℝ => (ENNReal.ofReal t) ^ (p - 2)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  calc
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t ≤ u x}, ENNReal.ofReal (u x) ∂μ) *
        (ENNReal.ofReal t) ^ (p - 2)) =
        ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal t) ^ (p - 2) *
            ∫⁻ x in {x | t ≤ u x}, ENNReal.ofReal (u x) ∂μ := by
      apply lintegral_congr
      intro t
      ac_rfl
    _ = ∫⁻ x, ENNReal.ofReal (u x) *
        (∫⁻ t in Ioc (0 : ℝ) (u x), (ENNReal.ofReal t) ^ (p - 2)) ∂μ := by
      exact lintegral_swap_indicator_le u hu _ huv _ hw
    _ = _ := lintegral_ofReal_mul_lintegral_rpow_Ioc_eq u hu hu_nonneg hp1

theorem rational_high_high_region_tail
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (hu_nonneg : ∀ x, 0 ≤ u x)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | u x < t}, ENNReal.ofReal (u x ^ (3 : ℕ)) ∂μ) *
        (ENNReal.ofReal t) ^ (p - 4)) =
      (ENNReal.ofReal (3 - p))⁻¹ *
        (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
  have huv : Measurable (fun x => ENNReal.ofReal (u x ^ (3 : ℕ))) :=
    (hu.pow_const 3).ennreal_ofReal
  have hw : Measurable (fun t : ℝ => (ENNReal.ofReal t) ^ (p - 4)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  calc
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | u x < t}, ENNReal.ofReal (u x ^ (3 : ℕ)) ∂μ) *
        (ENNReal.ofReal t) ^ (p - 4)) =
        ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal t) ^ (p - 4) *
            ∫⁻ x in {x | u x < t}, ENNReal.ofReal (u x ^ (3 : ℕ)) ∂μ := by
      apply lintegral_congr
      intro t
      ac_rfl
    _ = ∫⁻ x, ENNReal.ofReal (u x ^ (3 : ℕ)) *
        (∫⁻ t in Ioi (u x), (ENNReal.ofReal t) ^ (p - 4)) ∂μ := by
      exact lintegral_swap_indicator_lt u hu hu_nonneg _ huv _ hw
    _ = ∫⁻ x, (ENNReal.ofReal (3 - p))⁻¹ *
        (ENNReal.ofReal (u x)) ^ p ∂μ := by
      apply lintegral_congr
      intro x
      exact ofReal_cube_mul_lintegral_rpow_Ioi_eq (hu_nonneg x) hp1 hp2
    _ = _ := lintegral_const_mul _
      (ENNReal.continuous_rpow_const.measurable.comp hu.ennreal_ofReal)

/-- The weighted high-amplitude tail obtained from the two rational bounds
`‖highₜ(x)‖ ≤ u(x)` for `t ≤ u(x)` and
`‖highₜ(x)‖ ≤ u(x)³ / t²` for `u(x) < t`. -/
theorem rational_high_weighted_tail_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (high : ℝ → α → E)
    (hhigh_meas : Measurable (fun q : ℝ × α => ENNReal.ofReal ‖high q.1 q.2‖))
    (hbelow : ∀ t x, 0 < t → t ≤ u x →
      ENNReal.ofReal ‖high t x‖ ≤ ENNReal.ofReal (u x))
    (habove : ∀ t x, 0 < t → u x < t →
      ENNReal.ofReal ‖high t x‖ ≤ ENNReal.ofReal (u x ^ (3 : ℕ) / t ^ (2 : ℕ)))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) *
        (ENNReal.ofReal t) ^ (p - 2)) ≤
      ((ENNReal.ofReal (p - 1))⁻¹ + (ENNReal.ofReal (3 - p))⁻¹) *
        (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
  let H : ℝ → α → ℝ≥0∞ := fun t x => ENNReal.ofReal ‖high t x‖
  let U : α → ℝ≥0∞ := fun x => ENNReal.ofReal (u x)
  let V : α → ℝ≥0∞ := fun x => ENNReal.ofReal (u x ^ (3 : ℕ))
  let wlow : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 2)
  let whigh : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 4)
  let A : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x in {x | t ≤ u x}, U x ∂μ
  let B : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x in {x | u x < t}, V x ∂μ
  have hH : Measurable (Function.uncurry H) := by
    change Measurable (fun q : ℝ × α => H q.1 q.2)
    simpa only [H] using hhigh_meas
  have hU : Measurable U := by
    exact hu.ennreal_ofReal
  have hV : Measurable V := by
    exact (hu.pow_const 3).ennreal_ofReal
  have hwlow : Measurable wlow := by
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hwhigh : Measurable whigh := by
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hA : Measurable A := by
    exact measurable_lintegral_indicator_le u hu _ hU
  have hB : Measurable B := by
    exact measurable_lintegral_indicator_lt u hu _ hV
  have hpoint (t : ℝ) (ht : 0 < t) (x : α) :
      H t x * wlow t ≤
        ({x | t ≤ u x}.indicator (fun x => U x * wlow t)) x +
          ({x | u x < t}.indicator (fun x => V x * whigh t)) x := by
    by_cases htu : t ≤ u x
    · have hnot : ¬ u x < t := not_lt_of_ge htu
      simpa [Set.indicator, htu, hnot, H, U] using
        mul_le_mul_of_nonneg_right (hbelow t x ht htu) (by positivity)
    · have hut : u x < t := lt_of_not_ge htu
      have hmain : H t x * wlow t ≤ V x * whigh t := by
        calc
          H t x * wlow t ≤
              ENNReal.ofReal (u x ^ (3 : ℕ) / t ^ (2 : ℕ)) * wlow t :=
            mul_le_mul_of_nonneg_right (habove t x ht hut) (by positivity)
          _ = V x * whigh t := by
            dsimp only [V, wlow, whigh]
            exact ofReal_high_weight_eq (hu_nonneg x) ht
      simpa [Set.indicator, htu, hut] using hmain
  have hfixed (t : ℝ) (ht : 0 < t) :
      (∫⁻ x, H t x ∂μ) * wlow t ≤ A t * wlow t + B t * whigh t := by
    have hHt : Measurable (fun x => H t x) :=
      hH.comp (measurable_const.prodMk measurable_id)
    let s₁ : Set α := {x | t ≤ u x}
    let s₂ : Set α := {x | u x < t}
    have hs₁ : MeasurableSet s₁ := by
      exact measurableSet_le measurable_const hu
    have hs₂ : MeasurableSet s₂ := by
      exact measurableSet_lt hu measurable_const
    have hI₁ : Measurable (s₁.indicator (fun x => U x * wlow t)) :=
      (hU.mul measurable_const).indicator hs₁
    have hI₂ : Measurable (s₂.indicator (fun x => V x * whigh t)) :=
      (hV.mul measurable_const).indicator hs₂
    have hAeq : (∫⁻ x, s₁.indicator (fun x => U x * wlow t) x ∂μ) =
        A t * wlow t := by
      rw [show (fun x => s₁.indicator (fun x => U x * wlow t) x) =
          fun x => s₁.indicator U x * wlow t by
        funext x
        exact Set.indicator_mul_const s₁ U (wlow t) x]
      rw [lintegral_mul_const (wlow t) (hU.indicator hs₁)]
      dsimp only [A]
      rw [lintegral_indicator hs₁]
    have hBeq : (∫⁻ x, s₂.indicator (fun x => V x * whigh t) x ∂μ) =
        B t * whigh t := by
      rw [show (fun x => s₂.indicator (fun x => V x * whigh t) x) =
          fun x => s₂.indicator V x * whigh t by
        funext x
        exact Set.indicator_mul_const s₂ V (whigh t) x]
      rw [lintegral_mul_const (whigh t) (hV.indicator hs₂)]
      dsimp only [B]
      rw [lintegral_indicator hs₂]
    calc
      (∫⁻ x, H t x ∂μ) * wlow t = ∫⁻ x, H t x * wlow t ∂μ :=
        (lintegral_mul_const (wlow t) hHt).symm
      _ ≤ ∫⁻ x,
          s₁.indicator (fun x => U x * wlow t) x +
            s₂.indicator (fun x => V x * whigh t) x ∂μ := by
        apply lintegral_mono
        intro x
        simpa only [s₁, s₂] using hpoint t ht x
      _ = (∫⁻ x, s₁.indicator (fun x => U x * wlow t) x ∂μ) +
          ∫⁻ x, s₂.indicator (fun x => V x * whigh t) x ∂μ :=
        lintegral_add_left hI₁ _
      _ = A t * wlow t + B t * whigh t := by rw [hAeq, hBeq]
  have hmain :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, H t x ∂μ) * wlow t) ≤
      (∫⁻ t in Ioi (0 : ℝ), A t * wlow t) +
        ∫⁻ t in Ioi (0 : ℝ), B t * whigh t := by
    calc
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, H t x ∂μ) * wlow t) ≤
          ∫⁻ t in Ioi (0 : ℝ), A t * wlow t + B t * whigh t := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hfixed t ht
      _ = (∫⁻ t in Ioi (0 : ℝ), A t * wlow t) +
          ∫⁻ t in Ioi (0 : ℝ), B t * whigh t :=
        lintegral_add_left (hA.mul hwlow) _
  have hAtail :
      (∫⁻ t in Ioi (0 : ℝ), A t * wlow t) =
        (ENNReal.ofReal (p - 1))⁻¹ *
          (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
    simpa only [A, U, wlow] using rational_high_low_region_tail u hu hu_nonneg hp1
  have hBtail :
      (∫⁻ t in Ioi (0 : ℝ), B t * whigh t) =
        (ENNReal.ofReal (3 - p))⁻¹ *
          (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
    simpa only [B, V, whigh] using rational_high_high_region_tail u hu hu_nonneg hp1 hp2
  calc
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) *
        (ENNReal.ofReal t) ^ (p - 2)) =
        ∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, H t x ∂μ) * wlow t := by rfl
    _ ≤ (∫⁻ t in Ioi (0 : ℝ), A t * wlow t) +
        ∫⁻ t in Ioi (0 : ℝ), B t * whigh t := hmain
    _ = ((ENNReal.ofReal (p - 1))⁻¹ + (ENNReal.ofReal (3 - p))⁻¹) *
        (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by
      rw [hAtail, hBtail]
      ring

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Set ENNReal

noncomputable section

/-- The Schwartz-valued rational low-amplitude split has the precise weighted
`L²` tail required by the split Marcinkiewicz argument. -/
theorem rational_schwartz_low_weighted_tail
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    (low high : ℝ → SchwartzMap (Euclidean d) ℂ)
    (hlow : ∀ t x, low t x =
      ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x)
    (hhigh : ∀ t, high t = f - low t)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ))) *
        (ENNReal.ofReal t) ^ (p - 3)) ≤
      ((ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹ +
          (ENNReal.ofReal (2 - p))⁻¹) *
        ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p) := by
  apply weighted_low_tail_le_of_two_region_bounds
    (u := fun x : Euclidean d => ‖f x‖)
    (low := fun t x => low t x)
    f.continuous.norm.measurable (fun x => norm_nonneg _)
  · intro t x ht htx
    apply ENNReal.ofReal_le_ofReal
    have h := (rational_low_high_pointwise_tail_bounds f (low t) (high t)
      ht (hlow t) (hhigh t) x).1
    simpa [htx] using h
  · intro t x ht htx
    apply ENNReal.ofReal_le_ofReal
    have h := (rational_low_high_pointwise_tail_bounds f (low t) (high t)
      ht (hlow t) (hhigh t) x).1
    have hnot : ¬ t ≤ ‖f x‖ := not_le_of_gt htx
    simpa [hnot] using h
  · exact hp1
  · exact hp2

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Set ENNReal

noncomputable section

/-- The Schwartz-valued rational high-amplitude split has the precise
weighted `L¹` tail required by the split Marcinkiewicz argument. -/
theorem rational_schwartz_high_weighted_tail
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    (low high : ℝ → SchwartzMap (Euclidean d) ℂ)
    (hlow : ∀ t x, low t x =
      ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x)
    (hhigh : ∀ t, high t = f - low t)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, ENNReal.ofReal ‖high t x‖) *
        (ENNReal.ofReal t) ^ (p - 2)) ≤
      ((ENNReal.ofReal (p - 1))⁻¹ + (ENNReal.ofReal (3 - p))⁻¹) *
        (∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p) := by
  apply rational_high_weighted_tail_le
    (u := fun x : Euclidean d => ‖f x‖)
    (high := fun t x => high t x)
    f.continuous.norm.measurable (fun x => norm_nonneg _)
  · have heq : (fun q : ℝ × Euclidean d => ENNReal.ofReal ‖high q.1 q.2‖) =
        (fun q : ℝ × Euclidean d => ENNReal.ofReal
          ‖f q.2 - ((1 + ‖(q.1⁻¹ : ℝ) • f q.2‖ ^ 2) ^ (-1 : ℝ)) • f q.2‖) := by
      funext q
      rw [hhigh q.1]
      simp only [sub_apply]
      rw [hlow q.1 q.2]
    rw [heq]
    exact (measurable_rational_high_family f).norm.ennreal_ofReal
  · intro t x ht htx
    apply ENNReal.ofReal_le_ofReal
    have h := (rational_low_high_pointwise_tail_bounds f (low t) (high t)
      ht (hlow t) (hhigh t) x).2
    simpa [htx] using h
  · intro t x ht htx
    apply ENNReal.ofReal_le_ofReal
    have h := (rational_low_high_pointwise_tail_bounds f (low t) (high t)
      ht (hlow t) (hhigh t) x).2
    have hnot : ¬ t ≤ ‖f x‖ := not_le_of_gt htx
    simpa [hnot] using h
  · exact hp1
  · exact hp2

/-- The smooth high truncation is dominated by the hard quarter-height tail.
The smooth factor is only used to keep the split inside the Schwartz class. -/
private theorem smooth_high_rpow_le_indicator
    {d : Nat} (f low high : SchwartzMap (Euclidean d) ℂ) {t q : ℝ}
    (ht : 0 < t) (hq : 0 < q)
    (hlow : ∀ x : Euclidean d,
      low x = ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x)
    (hhigh : high = f - low) (x : Euclidean d) :
    (ENNReal.ofReal ‖high x‖) ^ q ≤
      ({y : Euclidean d | t / 4 < ‖f y‖}.indicator
        (fun y => (ENNReal.ofReal ‖f y‖) ^ q) x) := by
  by_cases htx : t / 4 < ‖f x‖
  · have hx : x ∈ {y : Euclidean d | t / 4 < ‖f y‖} := htx
    simpa [Set.indicator, hx, htx.le] using ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (smooth_high_norm_le f low high hlow hhigh x)) hq.le
  · have hx : x ∉ {y : Euclidean d | t / 4 < ‖f y‖} := htx
    have hfx : ‖f x‖ ≤ t / 4 := le_of_not_gt htx
    change (ENNReal.ofReal ‖high x‖) ^ q ≤ _
    rw [smooth_high_eq_zero_of_norm_le_quarter f low high ht hlow hhigh x hfx]
    simp [Set.indicator, hx, ENNReal.zero_rpow_of_pos hq]

/-- The exact hard quarter-height tail identity. -/
theorem lintegral_high_tail_rpow_quarter_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (hu_nonneg : ∀ x, 0 ≤ u x)
    {q p : ℝ} (hq : 0 < q) (hqp : q < p) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t / 4 ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ) *
        (ENNReal.ofReal t) ^ (p - q - 1)) =
      (ENNReal.ofReal (p - q))⁻¹ *
        (ENNReal.ofReal (4 : ℝ)) ^ (p - q) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
  let G : ℝ → ENNReal := fun s =>
    ∫⁻ x in {x | s / 2 ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ
  have hv : Measurable (fun x => (ENNReal.ofReal (u x)) ^ q) :=
    ENNReal.continuous_rpow_const.measurable.comp hu.ennreal_ofReal
  have hG : Measurable G := by
    have hbase : Measurable (fun s : ℝ =>
        ∫⁻ x in {x | s ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ) :=
      measurable_lintegral_indicator_le (μ := μ) u hu _ hv
    change Measurable (fun s : ℝ =>
      (fun r : ℝ => ∫⁻ x in {x | r ≤ u x},
        (ENNReal.ofReal (u x)) ^ q ∂μ) (s / 2))
    exact hbase.comp (measurable_id.div_const 2)
  have hcoef :
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
            (ENNReal.ofReal (2 : ℝ)) ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
      _ = (ENNReal.ofReal (2 : ℝ)) ^ ((p - q - 1) + 1) :=
        (ENNReal.rpow_add (p - q - 1) 1 htwo0 htwoT).symm
      _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) := by
        congr 1
        ring
  have htwo_tail :
      (∫⁻ t in Ioi (0 : ℝ), G t * (ENNReal.ofReal t) ^ (p - q - 1)) =
        (ENNReal.ofReal (p - q))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
            ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
    simpa only [G] using lintegral_high_tail_rpow_eq u hu hu_nonneg hq hqp
  have hfour : ENNReal.ofReal (4 : ℝ) =
      ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (2 : ℝ) := by norm_num
  have hpow :
      (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - q) =
        (ENNReal.ofReal (4 : ℝ)) ^ (p - q) := by
    rw [hfour, ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hqp.le)]
  calc
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t / 4 ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ) *
        (ENNReal.ofReal t) ^ (p - q - 1)) =
        ∫⁻ t in Ioi (0 : ℝ), G (((1 : ℝ) / 2) * t) *
          (ENNReal.ofReal t) ^ (p - q - 1) := by
      apply lintegral_congr
      intro t
      congr 2
      congr 3
      ring
    _ = (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
        (ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) *
          ∫⁻ t in Ioi (0 : ℝ), G t * (ENNReal.ofReal t) ^ (p - q - 1)) :=
      lintegral_Ioi_comp_mul_weight G hG ((1 : ℝ) / 2) (by norm_num) (p - q - 1)
    _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
        ∫⁻ t in Ioi (0 : ℝ), G t * (ENNReal.ofReal t) ^ (p - q - 1) := by
      calc
        (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
            (ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) *
              ∫⁻ t in Ioi (0 : ℝ), G t * (ENNReal.ofReal t) ^ (p - q - 1)) =
            ((ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
              ENNReal.ofReal (((1 : ℝ) / 2)⁻¹)) *
                ∫⁻ t in Ioi (0 : ℝ), G t * (ENNReal.ofReal t) ^ (p - q - 1) := by ac_rfl
        _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
            ∫⁻ t in Ioi (0 : ℝ), G t * (ENNReal.ofReal t) ^ (p - q - 1) := by
          rw [hcoef]
    _ = (ENNReal.ofReal (p - q))⁻¹ *
        (ENNReal.ofReal (4 : ℝ)) ^ (p - q) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
      rw [htwo_tail]
      calc
        (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
            ((ENNReal.ofReal (p - q))⁻¹ *
              (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
                ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) =
            (ENNReal.ofReal (p - q))⁻¹ *
              ((ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
                (ENNReal.ofReal (2 : ℝ)) ^ (p - q)) *
                  ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by ac_rfl
        _ = _ := by rw [hpow]

/-- The smooth Schwartz high truncation has the all-range `L^q` tail needed
for weak `(q,q)`--`L∞` interpolation. -/
theorem smooth_bump_schwartz_high_q_weighted_tail
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    (low high : ℝ → SchwartzMap (Euclidean d) ℂ)
    (hlow : ∀ t x, low t x =
      ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x)
    (hhigh : ∀ t, high t = f - low t)
    {q p : ℝ} (hq : 0 < q) (hqp : q < p) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, (ENNReal.ofReal ‖high t x‖) ^ q) *
        (ENNReal.ofReal t) ^ (p - q - 1)) ≤
      (ENNReal.ofReal (p - q))⁻¹ *
        (ENNReal.ofReal (4 : ℝ)) ^ (p - q) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by
  let H : ℝ → ENNReal := fun t =>
    ∫⁻ x, (ENNReal.ofReal ‖high t x‖) ^ q
  let B : ℝ → ENNReal := fun t =>
    ∫⁻ x in {x | t / 4 ≤ ‖f x‖}, (ENNReal.ofReal ‖f x‖) ^ q
  let w : ℝ → ENNReal := fun t => (ENNReal.ofReal t) ^ (p - q - 1)
  have hfixed (t : ℝ) (ht : 0 < t) : H t ≤ B t := by
    dsimp only [H, B]
    have hset : MeasurableSet {x : Euclidean d | t / 4 ≤ ‖f x‖} :=
      measurableSet_le measurable_const f.continuous.norm.measurable
    rw [← lintegral_indicator hset]
    apply lintegral_mono
    intro x
    have hpoint := smooth_high_rpow_le_indicator f (low t) (high t) ht hq
      (hlow t) (hhigh t) x
    by_cases hx : t / 4 < ‖f x‖
    · simpa [Set.indicator, hx, hx.le] using hpoint
    · have hfx : ‖f x‖ ≤ t / 4 := le_of_not_gt hx
      change (ENNReal.ofReal ‖high t x‖) ^ q ≤ _
      rw [smooth_high_eq_zero_of_norm_le_quarter f (low t) (high t)
        ht (hlow t) (hhigh t) x hfx]
      simp [ENNReal.zero_rpow_of_pos hq]
  have hmain :
      (∫⁻ t in Ioi (0 : ℝ), H t * w t) ≤
        ∫⁻ t in Ioi (0 : ℝ), B t * w t := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_le_mul_of_nonneg_right (hfixed t ht) (by positivity)
  calc
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, (ENNReal.ofReal ‖high t x‖) ^ q) *
        (ENNReal.ofReal t) ^ (p - q - 1)) =
        ∫⁻ t in Ioi (0 : ℝ), H t * w t := by rfl
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), B t * w t := hmain
    _ = (ENNReal.ofReal (p - q))⁻¹ *
        (ENNReal.ofReal (4 : ℝ)) ^ (p - q) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by
      simpa only [B, w] using
        lintegral_high_tail_rpow_quarter_eq
          (u := fun x : Euclidean d => ‖f x‖)
          f.continuous.norm.measurable (fun x => norm_nonneg _) hq hqp

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory FourierTransform Metric Set intervalIntegral
open scoped BoundedContinuousFunction Convolution FourierTransform

noncomputable section

/-- A compact-radius `L¹` maximal estimate for an explicit smooth dyadic
bandpass in every Euclidean dimension. This is the genuine radius-Sobolev
endpoint used before interpolation. -/
theorem exists_smooth_dyadic_sphericalMaximal_l1
    {d : Nat} (φ f : SchwartzMap (Euclidean d) ℂ) (j : Nat) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ)) ∧
      (∫⁻ x : Euclidean d,
        ⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal
            ‖sphericalAverage d
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖) ≤
        ENNReal.ofReal
          (surfaceMass d *
            (2 * (∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
              3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖fderiv ℝ
                  ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))) := by
  rcases exists_schwartzMap_smooth_dyadic_bandpass φ j with ⟨ψ, hψ⟩
  refine ⟨ψ, hψ, ?_⟩
  let R : ℝ := (2 : ℝ) ^ j
  let S : ℝ := (2 : ℝ) ^ (j + 1)
  let A_R : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 R⁻¹ (inv_ne_zero (by positivity : R ≠ 0)))
  let A_S : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 S⁻¹ (inv_ne_zero (by positivity : S ≠ 0)))
  let φR : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A_R) φ
  let φS : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A_S) φ
  let pR : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (φR : Euclidean d → ℂ) (𝓕 f))
  let pS : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (φS : Euclidean d → ℂ) (𝓕 f))
  let p : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f))
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hS : 0 < S := by
    dsimp only [S]
    positivity
  have hφR (ξ : Euclidean d) : φR ξ = φ (R⁻¹ • ξ) := by
    change φ (A_R ξ) = φ (R⁻¹ • ξ)
    simp [A_R]
  have hφS (ξ : Euclidean d) : φS ξ = φ (S⁻¹ • ξ) := by
    change φ (A_S ξ) = φ (S⁻¹ • ξ)
    simp [A_S]
  have hpR (x : Euclidean d) : pR x =
      𝓕⁻ (fun ξ : Euclidean d => φ (R⁻¹ • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x := by
    dsimp [pR]
    rw [SchwartzMap.fourierInv_coe]
    simp only [SchwartzMap.smulLeftCLM_apply φR.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul]
    congr 2
  have hpS (x : Euclidean d) : pS x =
      𝓕⁻ (fun ξ : Euclidean d => φ (S⁻¹ • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x := by
    dsimp [pS]
    rw [SchwartzMap.fourierInv_coe]
    simp only [SchwartzMap.smulLeftCLM_apply φS.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul]
    congr 2
  have hpR_fun : (pR : Euclidean d → ℂ) =
      fun x => 𝓕⁻ (fun ξ : Euclidean d => φ (R⁻¹ • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x := by
    funext x
    exact hpR x
  have hpS_fun : (pS : Euclidean d → ℂ) =
      fun x => 𝓕⁻ (fun ξ : Euclidean d => φ (S⁻¹ • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x := by
    funext x
    exact hpS x
  have hp_split (x : Euclidean d) : p x = pS x - pR x := by
    dsimp [p]
    rw [SchwartzMap.fourierInv_coe]
    simp only [SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul]
    rw [hpS x, hpR x]
    have hmult : (fun ξ : Euclidean d => ψ ξ *
        𝓕 (f : Euclidean d → ℂ) ξ) =
        fun ξ => (φS ξ - φR ξ) * 𝓕 (f : Euclidean d → ℂ) ξ := by
      funext ξ
      rw [hψ ξ, hφS ξ, hφR ξ]
    rw [hmult]
    exact fourierInv_sub_schwartz_multiplier φS φR f x
  have hp_fun : (p : Euclidean d → ℂ) = fun x => pS x - pR x := by
    funext x
    exact hp_split x
  have hpL1 :
      (∫ x : Euclidean d, ‖p x‖) ≤
        2 * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) := by
    rw [hp_fun]
    calc
      (∫ x : Euclidean d, ‖pS x - pR x‖) ≤
          ∫ x : Euclidean d, (‖pS x‖ + ‖pR x‖) := by
        apply MeasureTheory.integral_mono
        · exact (pS.integrable.sub pR.integrable).norm
        · exact pS.integrable.norm.add pR.integrable.norm
        · intro x
          exact norm_sub_le _ _
      _ = (∫ x : Euclidean d, ‖pS x‖) + ∫ x : Euclidean d, ‖pR x‖ := by
        rw [integral_add pS.integrable.norm pR.integrable.norm]
      _ ≤ (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
          (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) := by
        apply add_le_add
        · change (∫ x : Euclidean d, ‖(pS : Euclidean d → ℂ) x‖) ≤ _
          rw [hpS_fun]
          exact integral_norm_fourierInv_scaled_schwartz_multiplier_le φ f hS
        · change (∫ x : Euclidean d, ‖(pR : Euclidean d → ℂ) x‖) ≤ _
          rw [hpR_fun]
          exact integral_norm_fourierInv_scaled_schwartz_multiplier_le φ f hR
      _ = 2 * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) := by
        ring
  let dpR : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) pR
  let dpS : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) pS
  let dp : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) p
  have hdpR (x : Euclidean d) : dpR x =
      fderiv ℝ (pR : Euclidean d → ℂ) x := by
    exact SchwartzMap.fderivCLM_apply ℂ pR x
  have hdpS (x : Euclidean d) : dpS x =
      fderiv ℝ (pS : Euclidean d → ℂ) x := by
    exact SchwartzMap.fderivCLM_apply ℂ pS x
  have hdp (x : Euclidean d) : dp x =
      fderiv ℝ (p : Euclidean d → ℂ) x := by
    exact SchwartzMap.fderivCLM_apply ℂ p x
  have hpderiv_split (x : Euclidean d) :
      fderiv ℝ (p : Euclidean d → ℂ) x = dpS x - dpR x := by
    rw [hdpS x, hdpR x, hp_fun]
    exact fderiv_sub pS.differentiableAt pR.differentiableAt
  have hpderivL1 :
      (∫ x : Euclidean d, ‖fderiv ℝ (p : Euclidean d → ℂ) x‖) ≤
        S * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) +
          R * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) := by
    calc
      (∫ x : Euclidean d, ‖fderiv ℝ (p : Euclidean d → ℂ) x‖) =
          ∫ x : Euclidean d,
        ‖dpS x - dpR x‖ := by
        congr with x
        rw [hpderiv_split x]
      _ ≤
          ∫ x : Euclidean d, (‖dpS x‖ + ‖dpR x‖) := by
        apply MeasureTheory.integral_mono
        · exact (dpS.integrable.sub dpR.integrable).norm
        · exact dpS.integrable.norm.add dpR.integrable.norm
        · intro x
          exact norm_sub_le _ _
      _ = (∫ x : Euclidean d, ‖dpS x‖) + ∫ x : Euclidean d, ‖dpR x‖ := by
        rw [MeasureTheory.integral_add dpS.integrable.norm dpR.integrable.norm]
      _ ≤ S * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) +
          R * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) := by
        apply add_le_add
        · calc
            (∫ x : Euclidean d, ‖dpS x‖) =
                ∫ x : Euclidean d, ‖fderiv ℝ (fun y : Euclidean d =>
                  𝓕⁻ (fun ξ : Euclidean d => φ (S⁻¹ • ξ) *
                    𝓕 (f : Euclidean d → ℂ) ξ) y) x‖ := by
              congr with x
              rw [hdpS x, hpS_fun]
            _ ≤ _ :=
              integral_norm_fderiv_fourierInv_scaled_schwartz_multiplier_le φ f hS
        · calc
            (∫ x : Euclidean d, ‖dpR x‖) =
                ∫ x : Euclidean d, ‖fderiv ℝ (fun y : Euclidean d =>
                  𝓕⁻ (fun ξ : Euclidean d => φ (R⁻¹ • ξ) *
                    𝓕 (f : Euclidean d → ℂ) ξ) y) x‖ := by
              congr with x
              rw [hdpR x, hpR_fun]
            _ ≤ _ :=
              integral_norm_fderiv_fourierInv_scaled_schwartz_multiplier_le φ f hR
  have hpderivbound (x : Euclidean d) :
      ‖fderiv ℝ (p : Euclidean d → ℂ) x‖ ≤
        ‖dp.toBoundedContinuousFunction‖ := by
    calc
      ‖fderiv ℝ (p : Euclidean d → ℂ) x‖ = ‖dp x‖ := by rw [hdp x]
      _ = ‖dp.toBoundedContinuousFunction x‖ := rfl
      _ ≤ ‖dp.toBoundedContinuousFunction‖ :=
        BoundedContinuousFunction.norm_coe_le_norm dp.toBoundedContinuousFunction x
  have hp : ContDiff ℝ 1 (p : Euclidean d → ℂ) := by
    simpa only [p, WithTop.coe_one] using p.smooth (1 : ℕ∞)
  have hpderiv_integrable : Integrable (fderiv ℝ (p : Euclidean d → ℂ)) volume := by
    have hdp_fun : (dp : Euclidean d → (Euclidean d →L[ℝ] ℂ)) =
        fderiv ℝ (p : Euclidean d → ℂ) := by
      funext x
      exact hdp x
    rw [← hdp_fun]
    exact dp.integrable
  have hlocal :=
    lintegral_iSup_ennreal_norm_sphericalAverage_le_local_radiusSobolev
      (p : Euclidean d → ℂ)
      hp
      p.integrable
      hpderiv_integrable
      hpderivbound (by norm_num : (1 : ℝ) ≤ 2)
  change (∫⁻ x : Euclidean d,
    ⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal ‖sphericalAverage d (p : Euclidean d → ℂ) r.1 x‖) ≤ _
  calc
    (∫⁻ x : Euclidean d,
      ⨆ r : Icc (1 : ℝ) 2,
        ENNReal.ofReal ‖sphericalAverage d (p : Euclidean d → ℂ) r.1 x‖) ≤
        ENNReal.ofReal (surfaceMass d *
          ((∫ x : Euclidean d, ‖p x‖) +
            (2 - 1) * (∫ x : Euclidean d,
              ‖fderiv ℝ (p : Euclidean d → ℂ) x‖))) := hlocal
    _ ≤ ENNReal.ofReal
        (surfaceMass d *
          (2 * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
            3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖fderiv ℝ
                ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))) := by
      apply ENNReal.ofReal_le_ofReal
      have hmass : 0 ≤ surfaceMass d := measureReal_nonneg
      apply mul_le_mul_of_nonneg_left _ hmass
      rw [show (2 - 1 : ℝ) = 1 by norm_num, one_mul]
      calc
        (∫ x : Euclidean d, ‖p x‖) +
            ∫ x : Euclidean d, ‖fderiv ℝ (p : Euclidean d → ℂ) x‖ ≤
            (2 * (∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖)) +
              (S * (∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖fderiv ℝ
                  ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) +
                R * (∫ x : Euclidean d, ‖f x‖) *
                  (∫ x : Euclidean d, ‖fderiv ℝ
                    ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)) :=
          add_le_add hpL1 hpderivL1
        _ = 2 * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
            3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖fderiv ℝ
                ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) := by
          dsimp only [R, S]
          ring

/-- The dyadic multiplier can be chosen once, independently of the Schwartz
input, for the compact-radius `L¹` endpoint. -/
theorem exists_smooth_dyadic_sphericalMaximal_l1_uniform
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ) (j : Nat) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ)) ∧
      ∀ f : SchwartzMap (Euclidean d) ℂ,
        (∫⁻ x : Euclidean d,
          ⨆ r : Icc (1 : ℝ) 2,
            ENNReal.ofReal
              ‖sphericalAverage d
                ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                  SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖) ≤
          ENNReal.ofReal
            (surfaceMass d *
              (2 * (∫ x : Euclidean d, ‖f x‖) *
                  (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
                3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
                  (∫ x : Euclidean d, ‖fderiv ℝ
                    ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))) := by
  rcases exists_schwartzMap_smooth_dyadic_bandpass φ j with ⟨ψ, hψ⟩
  refine ⟨ψ, hψ, ?_⟩
  intro f
  rcases exists_smooth_dyadic_sphericalMaximal_l1 φ f j with ⟨χ, hχ, hbound⟩
  have hχψ : χ = ψ :=
    schwartzMap_eq_of_eq_smooth_dyadic_bandpass hχ hψ
  rw [hχψ] at hbound
  exact hbound

/-- The lower-order term in the local `L¹` endpoint is absorbed by the
geometric dyadic scale. -/
theorem smooth_dyadic_l1_coefficient_le_geometric (j : Nat) {A B : ℝ}
    (hA : 0 ≤ A) :
    2 * A + 3 * (2 : ℝ) ^ j * B ≤
      (2 : ℝ) ^ j * (2 * A + 3 * B) := by
  let s : ℝ := (2 : ℝ) ^ j
  have hsone : 1 ≤ s := by
    dsimp only [s]
    exact one_le_pow₀ (by norm_num)
  change 2 * A + 3 * s * B ≤ s * (2 * A + 3 * B)
  nlinarith

/-- The fixed literal smooth dyadic bandpass has a local `L¹` bound with a
single explicit `2^j` coefficient, uniformly for every Schwartz input. -/
theorem exists_smooth_dyadic_sphericalMaximal_l1_uniform_geometric
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ) (j : Nat) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ)) ∧
      ∀ f : SchwartzMap (Euclidean d) ℂ,
        (∫⁻ x : Euclidean d,
          ⨆ r : Icc (1 : ℝ) 2,
            ENNReal.ofReal
              ‖sphericalAverage d
                ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                  SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖) ≤
          ENNReal.ofReal
            (surfaceMass d * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
              (2 * (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
                3 * (∫ x : Euclidean d, ‖fderiv ℝ
                  ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))) := by
  rcases exists_smooth_dyadic_sphericalMaximal_l1_uniform φ j with ⟨ψ, hψ, hbound⟩
  refine ⟨ψ, hψ, ?_⟩
  intro f
  refine (hbound f).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hA : 0 ≤ (∫ x : Euclidean d, ‖f x‖) *
      (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) := by
    apply mul_nonneg
    · exact integral_nonneg fun _ => norm_nonneg _
    · exact integral_nonneg fun _ => norm_nonneg _
  have hcoefficient := smooth_dyadic_l1_coefficient_le_geometric (A :=
      (∫ x : Euclidean d, ‖f x‖) *
        (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖))
      (B := (∫ x : Euclidean d, ‖f x‖) *
        (∫ x : Euclidean d, ‖fderiv ℝ
          ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))
      j hA
  calc
    surfaceMass d *
        (2 * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
          3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)) =
        surfaceMass d *
          (2 * ((∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖)) +
            3 * (2 : ℝ) ^ j * ((∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖fderiv ℝ
                ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))) := by
          ring
    _ ≤ surfaceMass d *
          ((2 : ℝ) ^ j *
            (2 * ((∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖)) +
              3 * ((∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖fderiv ℝ
                  ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)))) :=
          mul_le_mul_of_nonneg_left hcoefficient measureReal_nonneg
    _ = (surfaceMass d * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖)) *
          (2 * (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
            3 * (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)) := by
          ring

/-- The local dyadic `L¹` estimate also supplies an actual `L¹` member for
the real compact-radius maximal norm. -/
theorem exists_smooth_dyadic_sphericalMaximal_memLp_one
    {d : Nat} (φ f : SchwartzMap (Euclidean d) ℂ) (j : Nat) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ)) ∧
      MemLp
        (fun x : Euclidean d =>
          (⨆ r : Icc (1 : ℝ) 2,
            ENNReal.ofReal
              ‖sphericalAverage d
                ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                  SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal)
        1 volume ∧
      (∫ x : Euclidean d,
        ‖(⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal
            ‖sphericalAverage d
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal‖) ≤
        surfaceMass d *
          (2 * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
            3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖fderiv ℝ
                ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)) := by
  rcases exists_smooth_dyadic_sphericalMaximal_l1 φ f j with ⟨ψ, hψ, hlin⟩
  let h : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)
  let p : SchwartzMap (Euclidean d) ℂ := 𝓕⁻ h
  let Q : Euclidean d → ENNReal := fun x =>
    ⨆ r : Icc (1 : ℝ) 2, ENNReal.ofReal ‖sphericalAverage d (p : Euclidean d → ℂ) r.1 x‖
  let K : ℝ := surfaceMass d *
    (2 * (∫ x : Euclidean d, ‖f x‖) *
        (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
      3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
        (∫ x : Euclidean d, ‖fderiv ℝ
          ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))
  have hQmeas : Measurable Q := by
    simpa only [Q] using
      measurable_iSup_ennreal_norm_sphericalAverage (p : Euclidean d → ℂ) p.continuous
  have hQlin : (∫⁻ x : Euclidean d, Q x) ≤ ENNReal.ofReal K := by
    simpa only [Q, p, h, K] using hlin
  have hK : 0 ≤ K := by
    dsimp only [K]
    apply mul_nonneg measureReal_nonneg
    apply add_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · norm_num
        · exact integral_nonneg fun _ => norm_nonneg _
      · exact integral_nonneg fun _ => norm_nonneg _
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · norm_num
          · positivity
        · exact integral_nonneg fun _ => norm_nonneg _
      · exact integral_nonneg fun _ => norm_nonneg _
  have hQfinite : (∫⁻ x : Euclidean d, Q x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQlin
  have hQint : Integrable (fun x : Euclidean d => (Q x).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hQmeas.aemeasurable hQfinite
  have hQtop : ∀ᵐ x : Euclidean d ∂volume, Q x < ⊤ :=
    ae_lt_top hQmeas hQfinite
  have hQintegral :
      (∫ x : Euclidean d, (Q x).toReal) = (∫⁻ x : Euclidean d, Q x).toReal :=
    integral_toReal hQmeas.aemeasurable hQtop
  have hQbound : (∫ x : Euclidean d, (Q x).toReal) ≤ K := by
    rw [hQintegral]
    rw [← ENNReal.toReal_ofReal hK]
    exact (ENNReal.toReal_le_toReal hQfinite ENNReal.ofReal_ne_top).2 hQlin
  refine ⟨ψ, hψ, ?_, ?_⟩
  · rw [memLp_one_iff_integrable]
    simpa only [Q, p, h] using hQint
  · change (∫ x : Euclidean d, ‖(Q x).toReal‖) ≤ K
    rw [show (fun x : Euclidean d => ‖(Q x).toReal‖) =
        fun x => (Q x).toReal by
          funext x
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]]
    exact hQbound

/-- The fixed literal dyadic bandpass has the real-valued compact-radius
`L¹` endpoint required for interpolation.  Its multiplier is independent of
the Schwartz input. -/
theorem smooth_dyadic_sphericalMaximal_memLp_one_of_bandpass_geometric
    {d : Nat} (φ f ψ : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (hψ : ∀ ξ : Euclidean d,
      ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        φ (((2 : ℝ) ^ j)⁻¹ • ξ)) :
    MemLp
      (fun x : Euclidean d =>
        (⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal
            ‖sphericalAverage d
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal)
      1 volume ∧
    (∫ x : Euclidean d,
      ‖(⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal
            ‖sphericalAverage d
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal‖) ≤
      surfaceMass d * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
        (2 * (∫ x : Euclidean d,
            ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
          3 * (∫ x : Euclidean d,
            ‖fderiv ℝ ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)) := by
  rcases exists_smooth_dyadic_sphericalMaximal_l1_uniform_geometric φ j with
    ⟨χ, hχ, hbound⟩
  have hχψ : χ = ψ :=
    schwartzMap_eq_of_eq_smooth_dyadic_bandpass hχ hψ
  rw [hχψ] at hbound
  let h : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)
  let p : SchwartzMap (Euclidean d) ℂ := 𝓕⁻ h
  let Q : Euclidean d → ENNReal := fun x =>
    ⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal ‖sphericalAverage d (p : Euclidean d → ℂ) r.1 x‖
  let K : ℝ :=
    surfaceMass d * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
      (2 * (∫ x : Euclidean d,
          ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
        3 * (∫ x : Euclidean d,
          ‖fderiv ℝ ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))
  have hQmeas : Measurable Q := by
    simpa only [Q] using
      measurable_iSup_ennreal_norm_sphericalAverage (p : Euclidean d → ℂ) p.continuous
  have hQlin : (∫⁻ x : Euclidean d, Q x) ≤ ENNReal.ofReal K := by
    simpa only [Q, p, h, K] using hbound f
  have hK : 0 ≤ K := by
    dsimp only [K]
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · exact measureReal_nonneg
        · positivity
      · exact integral_nonneg fun _ => norm_nonneg _
    · apply add_nonneg
      · apply mul_nonneg
        · norm_num
        · exact integral_nonneg fun _ => norm_nonneg _
      · apply mul_nonneg
        · norm_num
        · exact integral_nonneg fun _ => norm_nonneg _
  have hQfinite : (∫⁻ x : Euclidean d, Q x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQlin
  have hQint : Integrable (fun x : Euclidean d => (Q x).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hQmeas.aemeasurable hQfinite
  have hQtop : ∀ᵐ x : Euclidean d ∂volume, Q x < ⊤ :=
    ae_lt_top hQmeas hQfinite
  have hQintegral :
      (∫ x : Euclidean d, (Q x).toReal) = (∫⁻ x : Euclidean d, Q x).toReal :=
    integral_toReal hQmeas.aemeasurable hQtop
  have hQbound : (∫ x : Euclidean d, (Q x).toReal) ≤ K := by
    rw [hQintegral]
    rw [← ENNReal.toReal_ofReal hK]
    exact (ENNReal.toReal_le_toReal hQfinite ENNReal.ofReal_ne_top).2 hQlin
  refine ⟨?_, ?_⟩
  · rw [memLp_one_iff_integrable]
    simpa only [Q, p, h] using hQint
  · change (∫ x : Euclidean d, ‖(Q x).toReal‖) ≤ K
    rw [show (fun x : Euclidean d => ‖(Q x).toReal‖) =
        fun x => (Q x).toReal by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]]
    exact hQbound

/-- A fixed Schwartz Fourier multiplier followed by the compact-radius
spherical maximal norm is subadditive on Schwartz inputs.  The equality of
the multiplier outputs is proved before applying the concrete maximal
subadditivity theorem. -/
theorem smooth_schwartz_multiplier_compact_sphericalMaximal_add_le
    {d : Nat} (ψ f g : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    (⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal
        ‖sphericalAverage d
          ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 (f + g))) :
            SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal ≤
      (⨆ r : Icc (1 : ℝ) 2,
        ENNReal.ofReal
          ‖sphericalAverage d
            ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
              SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal +
        (⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal
            ‖sphericalAverage d
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 g)) :
                SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal := by
  let Pf : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f))
  let Pg : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 g))
  have hPadd :
      (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 (f + g))) :
        SchwartzMap (Euclidean d) ℂ) = Pf + Pg := by
    rw [fourier_add f g]
    rw [(SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ)).map_add]
    rw [fourierInv_add]
  rw [hPadd]
  exact toReal_iSup_ennreal_norm_sphericalAverage_add_le
    (Pf : Euclidean d → ℂ) (Pg : Euclidean d → ℂ) Pf.continuous Pg.continuous
    (by norm_num) x

/-- The real-valued compact-radius maximal output of a fixed Schwartz
multiplier is measurable on every Schwartz input. -/
theorem measurable_smooth_schwartz_multiplier_compact_sphericalMaximal
    {d : Nat} (ψ f : SchwartzMap (Euclidean d) ℂ) :
    Measurable (fun x : Euclidean d =>
      (⨆ r : Icc (1 : ℝ) 2,
        ENNReal.ofReal
          ‖sphericalAverage d
            ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
              SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal) := by
  let p : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f))
  exact ENNReal.measurable_toReal.comp
    (measurable_iSup_ennreal_norm_sphericalAverage (p : Euclidean d → ℂ) p.continuous)

end

end LeanSpherical.HarmonicAnalysis
