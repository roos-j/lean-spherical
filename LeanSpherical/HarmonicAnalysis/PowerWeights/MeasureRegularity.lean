/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.Density
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Regularity of radial power measures

The density argument for the weighted maximal operator needs the usual three
measure-theoretic regularity properties.  Local finiteness is in `Density`;
this file supplies positivity on open sets and temperate growth.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- In positive Euclidean dimension, the origin is Lebesgue-null. -/
theorem ae_ne_zero_volume_euclidean
    {d : ℕ} (hd : 1 ≤ d) :
    ∀ᵐ x : Euclidean d ∂(volume : Measure (Euclidean d)), x ≠ 0 := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  rw [ae_iff]
  simp

/-- Away from the origin, every radial power density is strictly positive. -/
theorem radialPowerWeight_pos_of_ne_zero
    {d : ℕ} (α : ℝ) {x : Euclidean d} (hx : x ≠ 0) :
    0 < radialPowerWeight d α x := by
  unfold radialPowerWeight
  apply ENNReal.rpow_pos
  · exact ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hx)
  · exact ENNReal.ofReal_ne_top

/-- The radial power density only vanishes at the origin (up to Lebesgue null
sets in positive dimension). -/
theorem ae_radialPowerWeight_ne_zero
    {d : ℕ} (hd : 1 ≤ d) (α : ℝ) :
    ∀ᵐ x : Euclidean d ∂(volume : Measure (Euclidean d)),
      radialPowerWeight d α x ≠ 0 := by
  filter_upwards [ae_ne_zero_volume_euclidean hd] with x hx
  exact (radialPowerWeight_pos_of_ne_zero α hx).ne'

/-- The radial power measure is positive on nonempty open sets in positive
dimension. -/
theorem powerWeightedVolume_isOpenPosMeasure
    {d : ℕ} (hd : 1 ≤ d) (α : ℝ) :
    (powerWeightedVolume d α).IsOpenPosMeasure := by
  unfold powerWeightedVolume
  exact (withDensity_absolutelyContinuous'
    (aemeasurable_radialPowerWeight d α volume)
    (ae_radialPowerWeight_ne_zero hd α)).isOpenPosMeasure

/-- The real representative of the radial power density has the expected
formula. -/
theorem radialPowerWeight_toReal
    (d : ℕ) (α : ℝ) (x : Euclidean d) :
    (radialPowerWeight d α x).toReal = ‖x‖ ^ α := by
  unfold radialPowerWeight
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (norm_nonneg x)]

private theorem exists_integrable_radialPowerWeight_mul_decay
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : -(d : ℝ) < α) :
    ∃ n : ℕ, Integrable (fun x : Euclidean d =>
      (radialPowerWeight d α x).toReal * (1 + ‖x‖) ^ (-(n : ℝ))) volume := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((d : ℝ) + max α 0)
  have hq : (d : ℝ) < (n : ℝ) - max α 0 := by
    linarith
  have hmajor : Integrable (fun x : Euclidean d =>
      (1 + ‖x‖) ^ (-((n : ℝ) - max α 0))) volume := by
    apply integrable_one_add_norm
    simpa using hq
  have hprod_meas : AEStronglyMeasurable (fun x : Euclidean d =>
      (radialPowerWeight d α x).toReal * (1 + ‖x‖) ^ (-(n : ℝ))) volume := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact (measurable_radialPowerWeight d α).ennreal_toReal
    · exact ((continuous_const.add continuous_norm).rpow_const
        (fun x => Or.inl (by
          have : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
          exact this.ne'))).measurable
  have hlocalWeight : IntegrableOn (fun x : Euclidean d =>
      (radialPowerWeight d α x).toReal) (Metric.closedBall 0 1) volume :=
    (locallyIntegrable_radialPowerWeight_toReal hd hα).integrableOn_isCompact
      (isCompact_closedBall 0 1)
  have hlocal : IntegrableOn (fun x : Euclidean d =>
      (radialPowerWeight d α x).toReal * (1 + ‖x‖) ^ (-(n : ℝ)))
      (Metric.closedBall 0 1) volume := by
    change Integrable _ (volume.restrict (Metric.closedBall 0 1))
    refine hlocalWeight.integrable.mono' hprod_meas.restrict ?_
    filter_upwards with x
    have hw : 0 ≤ (radialPowerWeight d α x).toReal := ENNReal.toReal_nonneg
    have hbase : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hdecay : (1 + ‖x‖) ^ (-(n : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (neg_nonpos.mpr (Nat.cast_nonneg n))
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hw (Real.rpow_nonneg (by linarith [norm_nonneg x]) _))]
    simpa using mul_le_mul_of_nonneg_left hdecay hw
  have htail : IntegrableOn (fun x : Euclidean d =>
      (radialPowerWeight d α x).toReal * (1 + ‖x‖) ^ (-(n : ℝ)))
      (Metric.closedBall 0 1)ᶜ volume := by
    change Integrable _ (volume.restrict (Metric.closedBall 0 1)ᶜ)
    refine hmajor.integrableOn.mono' hprod_meas.restrict ?_
    filter_upwards [ae_restrict_mem (Metric.isClosed_closedBall.measurableSet.compl)] with x hx
    have hx' : ¬ ‖x‖ ≤ 1 := by
      simpa only [mem_compl_iff, mem_closedBall_zero_iff] using hx
    have hnorm : 1 < ‖x‖ := lt_of_not_ge hx'
    have hweight : (radialPowerWeight d α x).toReal ≤
        (1 + ‖x‖) ^ max α 0 := by
      rw [radialPowerWeight_toReal]
      by_cases hα0 : 0 ≤ α
      · rw [max_eq_left hα0]
        exact Real.rpow_le_rpow (norm_nonneg x) (by linarith) hα0
      · have hαle : α ≤ 0 := le_of_not_ge hα0
        rw [max_eq_right hαle]
        simpa using Real.rpow_le_one_of_one_le_of_nonpos hnorm.le hαle
    have hbasepos : 0 < 1 + ‖x‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (by positivity) _))]
    calc
      (radialPowerWeight d α x).toReal * (1 + ‖x‖) ^ (-(n : ℝ)) ≤
          (1 + ‖x‖) ^ max α 0 * (1 + ‖x‖) ^ (-(n : ℝ)) :=
        mul_le_mul_of_nonneg_right hweight (Real.rpow_nonneg (by positivity) _)
      _ = (1 + ‖x‖) ^ (-((n : ℝ) - max α 0)) := by
        rw [← Real.rpow_add hbasepos]
        congr 1
        ring
  refine ⟨n, ?_⟩
  rw [← integrableOn_univ, ← union_compl_self (Metric.closedBall (0 : Euclidean d) 1),
    integrableOn_union]
  exact ⟨hlocal, htail⟩

/-- A radial power measure has temperate growth whenever its singularity is
locally integrable. -/
theorem powerWeightedVolume_hasTemperateGrowth
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : -(d : ℝ) < α) :
    (powerWeightedVolume d α).HasTemperateGrowth := by
  rcases exists_integrable_radialPowerWeight_mul_decay hd hα with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [powerWeightedVolume,
    integrable_withDensity_iff_integrable_smul'
      (measurable_radialPowerWeight d α) ?_]
  · simpa only [smul_eq_mul] using hn
  · filter_upwards [ae_ne_zero_volume_euclidean hd] with x hx
    exact (radialPowerWeight_ne_top_of_ne_zero α hx).lt_top

/-- Conditional instance form of temperate growth, convenient when the
dimension and the weight range have been supplied as `Fact`s. -/
instance instHasTemperateGrowth_powerWeightedVolume
    {d : ℕ} {α : ℝ} [Fact (1 ≤ d)] [Fact (-(d : ℝ) < α)] :
    (powerWeightedVolume d α).HasTemperateGrowth :=
  powerWeightedVolume_hasTemperateGrowth Fact.out Fact.out

/-- Conditional instance form of positivity on open sets. -/
instance instIsOpenPosMeasure_powerWeightedVolume
    {d : ℕ} {α : ℝ} [Fact (1 ≤ d)] :
    (powerWeightedVolume d α).IsOpenPosMeasure :=
  powerWeightedVolume_isOpenPosMeasure Fact.out α

end

end LeanSpherical.HarmonicAnalysis
