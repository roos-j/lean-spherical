/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.MarcinkiewiczInterpolation

/-!
# Low-amplitude rational tail integration

The low side of the rational split is integrated over its two amplitude
regions to provide the weighted `L²` tail for interpolation.
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
