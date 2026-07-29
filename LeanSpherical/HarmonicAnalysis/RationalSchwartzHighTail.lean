/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.RationalHighTailIntegration
import LeanSpherical.HarmonicAnalysis.RationalSchwartzLowTail
import LeanSpherical.HarmonicAnalysis.SchwartzRationalSplit

/-!
# Schwartz rational high tail

Specialization of the generic rational high-tail estimate to Schwartz input.
-/

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
