/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.PowerMeasure
import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Smooth radial power weights

The positive-weight argument first uses the nonsingular model
`(1 + |x|²)^(a / 2)`.  Unlike `|x|^a`, this and its reciprocal are Schwartz
multipliers for every real `a`.  Dilating this model and then letting the
regularization scale tend to zero recovers the literal power weight.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The smooth radial model for a power of the Euclidean norm. -/
def besselPowerWeight {d : ℕ} (a : ℝ) (x : Euclidean d) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ (a / 2)

/-- The scale-`ε` smooth radial model.  For positive `ε` this is a nonsingular
regularisation of `‖x‖ ^ a`, and a Euclidean dilation converts it to the
unit-scale model. -/
def scaledBesselPowerWeight {d : ℕ} (ε a : ℝ) (x : Euclidean d) : ℝ :=
  (ε ^ 2 + ‖x‖ ^ 2) ^ (a / 2)

/-- The measure with smooth radial density `(1 + |x|²)^(a / 2)`. -/
def besselWeightedVolume {d : ℕ} (a : ℝ) : Measure (Euclidean d) :=
  volume.withDensity (fun x => ENNReal.ofReal (besselPowerWeight a x))

/-- The weighted volume associated to the scale-`ε` regularisation. -/
def scaledBesselWeightedVolume {d : ℕ} (ε a : ℝ) : Measure (Euclidean d) :=
  volume.withDensity (fun x => ENNReal.ofReal (scaledBesselPowerWeight ε a x))

theorem besselPowerWeight_pos {d : ℕ} (a : ℝ) (x : Euclidean d) :
    0 < besselPowerWeight a x := by
  unfold besselPowerWeight
  exact Real.rpow_pos_of_pos (by positivity) _

theorem besselPowerWeight_nonneg {d : ℕ} (a : ℝ) (x : Euclidean d) :
    0 ≤ besselPowerWeight a x :=
  (besselPowerWeight_pos a x).le

theorem besselPowerWeight_ne_zero {d : ℕ} (a : ℝ) (x : Euclidean d) :
    besselPowerWeight a x ≠ 0 :=
  (besselPowerWeight_pos a x).ne'

theorem besselPowerWeight_mul {d : ℕ} (a b : ℝ) (x : Euclidean d) :
    besselPowerWeight a x * besselPowerWeight b x = besselPowerWeight (a + b) x := by
  unfold besselPowerWeight
  rw [← Real.rpow_add (by positivity : 0 < 1 + ‖x‖ ^ 2)]
  congr 1
  ring

theorem besselPowerWeight_inv {d : ℕ} (a : ℝ) (x : Euclidean d) :
    (besselPowerWeight a x)⁻¹ = besselPowerWeight (-a) x := by
  unfold besselPowerWeight
  rw [← Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖ ^ 2)]
  congr 1
  ring

theorem besselPowerWeight_zero {d : ℕ} (x : Euclidean d) :
    besselPowerWeight 0 x = 1 := by
  simp [besselPowerWeight]

theorem scaledBesselPowerWeight_pos {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (a : ℝ) (x : Euclidean d) :
    0 < scaledBesselPowerWeight ε a x := by
  unfold scaledBesselPowerWeight
  exact Real.rpow_pos_of_pos (by positivity) _

theorem scaledBesselPowerWeight_nonneg {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (a : ℝ) (x : Euclidean d) :
    0 ≤ scaledBesselPowerWeight ε a x :=
  (scaledBesselPowerWeight_pos hε a x).le

theorem scaledBesselPowerWeight_ne_zero {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (a : ℝ) (x : Euclidean d) :
    scaledBesselPowerWeight ε a x ≠ 0 :=
  (scaledBesselPowerWeight_pos hε a x).ne'

theorem scaledBesselPowerWeight_mul {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (a b : ℝ) (x : Euclidean d) :
    scaledBesselPowerWeight ε a x * scaledBesselPowerWeight ε b x =
      scaledBesselPowerWeight ε (a + b) x := by
  unfold scaledBesselPowerWeight
  rw [← Real.rpow_add (by positivity : 0 < ε ^ 2 + ‖x‖ ^ 2)]
  congr 1
  ring

theorem scaledBesselPowerWeight_inv {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (a : ℝ) (x : Euclidean d) :
    (scaledBesselPowerWeight ε a x)⁻¹ = scaledBesselPowerWeight ε (-a) x := by
  unfold scaledBesselPowerWeight
  rw [← Real.rpow_neg (by positivity : 0 ≤ ε ^ 2 + ‖x‖ ^ 2)]
  congr 1
  ring

/-- Dilation of the scale-`ε` model produces the unit Bessel model, with
the expected homogeneous scalar factor. -/
theorem scaledBesselPowerWeight_dilate {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (a : ℝ) (x : Euclidean d) :
    scaledBesselPowerWeight ε a (ε • x) =
      ε ^ a * besselPowerWeight a x := by
  unfold scaledBesselPowerWeight besselPowerWeight
  rw [norm_smul, Real.norm_of_nonneg hε.le]
  have hfactor : ε ^ 2 + (ε * ‖x‖) ^ 2 = ε ^ 2 * (1 + ‖x‖ ^ 2) := by
    ring
  rw [hfactor, Real.mul_rpow (sq_nonneg ε) (by positivity : 0 ≤ 1 + ‖x‖ ^ 2)]
  have hscale : (ε ^ 2) ^ (a / 2) = ε ^ a := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
    congr 1
    ring
  rw [hscale]

/-- The equivalent inverse-dilation form of the scale-change identity. -/
theorem scaledBesselPowerWeight_eq_rpow_mul_besselPowerWeight_dilate_inv
    {d : ℕ} {ε : ℝ} (hε : 0 < ε) (a : ℝ) (x : Euclidean d) :
    scaledBesselPowerWeight ε a x =
      ε ^ a * besselPowerWeight a (ε⁻¹ • x) := by
  rw [← scaledBesselPowerWeight_dilate hε a (ε⁻¹ • x)]
  simp [smul_smul, hε.ne']

theorem measurable_scaledBesselPowerWeight {d : ℕ} {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Measurable (scaledBesselPowerWeight (d := d) ε a) := by
  unfold scaledBesselPowerWeight
  exact ((continuous_const.pow 2).add (continuous_norm.pow 2)).rpow_const (by
    intro x
    left
    change ε ^ 2 + ‖x‖ ^ 2 ≠ 0
    exact ne_of_gt (by nlinarith [sq_pos_of_pos hε, sq_nonneg ‖x‖])) |>.measurable

private theorem exists_scaledBesselPowerWeight_le_one_add_norm_pow
    {d : ℕ} {ε a : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x : Euclidean d,
      scaledBesselPowerWeight ε a x ≤ C * (1 + ‖x‖) ^ k := by
  by_cases ha : 0 ≤ a
  · obtain ⟨k, hk⟩ := exists_nat_ge a
    let c : ℝ := max (ε ^ 2) 1
    refine ⟨c ^ (a / 2), Real.rpow_nonneg (by positivity) _, k, ?_⟩
    intro x
    have hc0 : 0 ≤ c := by
      dsimp only [c]
      positivity
    have hc1 : 1 ≤ c := by
      dsimp only [c]
      exact le_max_right _ _
    have hbase : ε ^ 2 + ‖x‖ ^ 2 ≤ c * (1 + ‖x‖ ^ 2) := by
      have hεc : ε ^ 2 ≤ c := by
        dsimp only [c]
        exact le_max_left _ _
      have hrc : ‖x‖ ^ 2 ≤ c * ‖x‖ ^ 2 := by
        exact le_mul_of_one_le_left (sq_nonneg ‖x‖) hc1
      nlinarith
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ ε ^ 2 + ‖x‖ ^ 2)
      hbase (by positivity : 0 ≤ a / 2)
    rw [Real.mul_rpow hc0 (by positivity : 0 ≤ 1 + ‖x‖ ^ 2)] at hpow
    have hquad : 1 + ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by
      nlinarith [norm_nonneg x]
    have hquadpow := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + ‖x‖ ^ 2)
      hquad (by positivity : 0 ≤ a / 2)
    have hcollapse : ((1 + ‖x‖) ^ 2) ^ (a / 2) = (1 + ‖x‖) ^ a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 1 + ‖x‖)]
      congr 1
      ring
    have hpoly : (1 + ‖x‖) ^ a ≤ (1 + ‖x‖) ^ k := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) hk
    change (ε ^ 2 + ‖x‖ ^ 2) ^ (a / 2) ≤ _
    calc
      (ε ^ 2 + ‖x‖ ^ 2) ^ (a / 2) ≤
          c ^ (a / 2) * (1 + ‖x‖ ^ 2) ^ (a / 2) := hpow
      _ ≤ c ^ (a / 2) * ((1 + ‖x‖) ^ 2) ^ (a / 2) :=
        mul_le_mul_of_nonneg_left hquadpow (Real.rpow_nonneg hc0 _)
      _ = c ^ (a / 2) * (1 + ‖x‖) ^ a := by rw [hcollapse]
      _ ≤ c ^ (a / 2) * (1 + ‖x‖) ^ k :=
        mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hc0 _)
  · refine ⟨(ε ^ 2) ^ (a / 2), Real.rpow_nonneg (sq_nonneg ε) _, 0, ?_⟩
    intro x
    change (ε ^ 2 + ‖x‖ ^ 2) ^ (a / 2) ≤ (ε ^ 2) ^ (a / 2) * (1 + ‖x‖) ^ 0
    rw [pow_zero, mul_one]
    apply Real.rpow_le_rpow_of_nonpos
    · exact sq_pos_of_pos hε
    · linarith [sq_nonneg ‖x‖]
    · linarith

/-- A positive-scale Bessel weighted volume has temperate growth.  The
proof only uses polynomial domination of its smooth density. -/
theorem scaledBesselWeightedVolume_hasTemperateGrowth
    {d : ℕ} {ε a : ℝ} (hε : 0 < ε) :
    (scaledBesselWeightedVolume (d := d) ε a).HasTemperateGrowth := by
  rcases exists_scaledBesselPowerWeight_le_one_add_norm_pow (d := d) hε with
    ⟨C, hC, k, hpoint⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((Module.finrank ℝ (Euclidean d) : ℝ) + k)
  have hn' : (Module.finrank ℝ (Euclidean d) : ℝ) < (n : ℝ) - k := by
    linarith
  have hmajor : Integrable (fun x : Euclidean d =>
      (1 + ‖x‖) ^ (-((n : ℝ) - k))) volume := by
    apply integrable_one_add_norm
    exact hn'
  have hprod_meas : AEStronglyMeasurable (fun x : Euclidean d =>
      scaledBesselPowerWeight ε a x * (1 + ‖x‖) ^ (-(n : ℝ))) volume := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact measurable_scaledBesselPowerWeight hε a
    · exact ((continuous_const.add continuous_norm).rpow_const (by
        intro x
        left
        exact (by positivity : 1 + ‖x‖ ≠ 0))).measurable
  have hprod : Integrable (fun x : Euclidean d =>
      scaledBesselPowerWeight ε a x * (1 + ‖x‖) ^ (-(n : ℝ))) volume := by
    refine (hmajor.const_mul C).mono' hprod_meas ?_
    filter_upwards with x
    have hdecay : 0 ≤ (1 + ‖x‖) ^ (-(n : ℝ)) := Real.rpow_nonneg (by positivity) _
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (scaledBesselPowerWeight_nonneg hε a x) hdecay)]
    calc
      scaledBesselPowerWeight ε a x * (1 + ‖x‖) ^ (-(n : ℝ)) ≤
          (C * (1 + ‖x‖) ^ k) * (1 + ‖x‖) ^ (-(n : ℝ)) :=
        mul_le_mul_of_nonneg_right (hpoint x) hdecay
      _ = C * (1 + ‖x‖) ^ (-((n : ℝ) - k)) := by
        calc
          C * (1 + ‖x‖) ^ k * (1 + ‖x‖) ^ (-(n : ℝ)) =
              C * ((1 + ‖x‖) ^ (k : ℝ) * (1 + ‖x‖) ^ (-(n : ℝ))) := by
                rw [Real.rpow_natCast]
                ring
          _ = C * (1 + ‖x‖) ^ ((k : ℝ) + (-(n : ℝ))) := by
                rw [← Real.rpow_add (by positivity)]
          _ = C * (1 + ‖x‖) ^ (-((n : ℝ) - k)) := by
                congr 2
                ring
  have hdensityMeas : Measurable (fun x : Euclidean d =>
      ENNReal.ofReal (scaledBesselPowerWeight ε a x)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (measurable_scaledBesselPowerWeight hε a)
  refine ⟨n, ?_⟩
  rw [scaledBesselWeightedVolume,
    integrable_withDensity_iff_integrable_smul'
      hdensityMeas ?_]
  · have hdensity : ∀ x : Euclidean d,
        (ENNReal.ofReal (scaledBesselPowerWeight ε a x)).toReal =
          scaledBesselPowerWeight ε a x := by
      intro x
      exact ENNReal.toReal_ofReal (scaledBesselPowerWeight_nonneg hε a x)
    simpa only [hdensity, smul_eq_mul] using hprod
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

/- `Euclidean d` has both a canonical `PiLp` normed-vector-space structure
and the one induced by its Hilbert structure.  The temperate-growth library
uses the latter. -/

attribute [-instance] PiLp.normedSpace in
attribute [local instance 2000] NormedField.toNormedSpace in
/-- Both the smooth radial model and its reciprocal are valid Schwartz
multipliers. -/
theorem besselPowerWeight_hasTemperateGrowth {d : ℕ} (a : ℝ) :
    (besselPowerWeight (d := d) a).HasTemperateGrowth := by
  change (fun x : Euclidean d => (1 + ‖x‖ ^ 2) ^ (a / 2)).HasTemperateGrowth
  exact Function.hasTemperateGrowth_one_add_norm_sq_rpow (Euclidean d) (a / 2)

theorem besselPowerWeight_inv_hasTemperateGrowth {d : ℕ} (a : ℝ) :
    (fun x : Euclidean d => (besselPowerWeight a x)⁻¹).HasTemperateGrowth := by
  rw [show (fun x : Euclidean d => (besselPowerWeight a x)⁻¹) =
      besselPowerWeight (-a) by
    funext x
    exact besselPowerWeight_inv a x]
  exact besselPowerWeight_hasTemperateGrowth (-a)

/-- A positive-scale Bessel regularisation is a Schwartz multiplier. -/
theorem scaledBesselPowerWeight_hasTemperateGrowth {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (a : ℝ) :
    (scaledBesselPowerWeight (d := d) ε a).HasTemperateGrowth := by
  let L : Euclidean d →L[ℝ] Euclidean d :=
    ε⁻¹ • ContinuousLinearMap.id ℝ (Euclidean d)
  have hL : (fun x : Euclidean d => L x).HasTemperateGrowth := L.hasTemperateGrowth
  have hcomp : (fun x : Euclidean d => besselPowerWeight a (L x)).HasTemperateGrowth :=
    (besselPowerWeight_hasTemperateGrowth a).comp hL
  have hrew : (scaledBesselPowerWeight (d := d) ε a) =
      fun x => ε ^ a * besselPowerWeight a (L x) := by
    funext x
    rw [← scaledBesselPowerWeight_dilate hε a (L x)]
    simp [L, smul_smul, hε.ne']
  rw [hrew]
  exact (Function.HasTemperateGrowth.const (ε ^ a)).mul hcomp

theorem scaledBesselPowerWeight_inv_hasTemperateGrowth {d : ℕ} {ε : ℝ}
    (hε : 0 < ε) (a : ℝ) :
    (fun x : Euclidean d => (scaledBesselPowerWeight ε a x)⁻¹).HasTemperateGrowth := by
  rw [show (fun x : Euclidean d => (scaledBesselPowerWeight ε a x)⁻¹) =
      scaledBesselPowerWeight ε (-a) by
    funext x
    exact scaledBesselPowerWeight_inv hε a x]
  exact scaledBesselPowerWeight_hasTemperateGrowth hε (-a)

theorem scaledBesselWeightedVolume_isFiniteMeasureOnCompacts
    {d : ℕ} {ε a : ℝ} (hε : 0 < ε) :
    IsFiniteMeasureOnCompacts (scaledBesselWeightedVolume (d := d) ε a) := by
  let w : Euclidean d → ℝ := scaledBesselPowerWeight ε a
  have hwlocal : LocallyIntegrable w (volume : Measure (Euclidean d)) := by
    exact (scaledBesselPowerWeight_hasTemperateGrowth hε a).1.continuous.locallyIntegrable
  constructor
  intro K hK
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hwK : IntegrableOn w K (volume : Measure (Euclidean d)) :=
    hwlocal.integrableOn_isCompact hK
  have hfin : IsFiniteMeasure ((volume.restrict K).withDensity fun x => ENNReal.ofReal (w x)) :=
    isFiniteMeasure_withDensity_ofReal hwK.2
  have hfin' : IsFiniteMeasure ((scaledBesselWeightedVolume (d := d) ε a).restrict K) := by
    rw [scaledBesselWeightedVolume, restrict_withDensity hKmeas]
    exact hfin
  letI : IsFiniteMeasure ((scaledBesselWeightedVolume (d := d) ε a).restrict K) := hfin'
  simpa only [Measure.restrict_apply_univ] using
    (IsFiniteMeasure.measure_univ_lt_top :
      (scaledBesselWeightedVolume (d := d) ε a).restrict K Set.univ < ⊤)

theorem scaledBesselWeightedVolume_sfinite {d : ℕ} {ε a : ℝ} (hε : 0 < ε) :
    SFinite (scaledBesselWeightedVolume (d := d) ε a) := by
  letI : IsFiniteMeasureOnCompacts (scaledBesselWeightedVolume (d := d) ε a) :=
    scaledBesselWeightedVolume_isFiniteMeasureOnCompacts hε
  infer_instance

theorem measurable_besselPowerWeight {d : ℕ} (a : ℝ) :
    Measurable (besselPowerWeight (d := d) a) :=
  (besselPowerWeight_hasTemperateGrowth a).1.continuous.measurable

theorem measurable_besselPowerDensity {d : ℕ} (a : ℝ) :
    Measurable (fun x : Euclidean d => ENNReal.ofReal (besselPowerWeight a x)) :=
  ENNReal.continuous_ofReal.measurable.comp (measurable_besselPowerWeight a)

theorem measurable_scaledBesselPowerDensity {d : ℕ} {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Measurable (fun x : Euclidean d => ENNReal.ofReal (scaledBesselPowerWeight ε a x)) :=
  ENNReal.continuous_ofReal.measurable.comp (measurable_scaledBesselPowerWeight hε a)

end

end LeanSpherical.HarmonicAnalysis
