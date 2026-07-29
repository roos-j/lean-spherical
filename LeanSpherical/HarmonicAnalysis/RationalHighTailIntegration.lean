/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.MarcinkiewiczInterpolation

/-!
# High-amplitude rational tail integration

The high side of the rational amplitude split is controlled by `u` below its
amplitude and by `u³ / t²` above it.  This file records the resulting weighted
Tonelli estimate.
-/

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
