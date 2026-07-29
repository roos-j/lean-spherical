/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PolarDecomposition
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Radial integration for the concrete surface measure

These are direct polar-coordinate identities for the concrete measure
`unitSurfaceMeasure`.  They provide the dimension-uniform measure calculation
needed before reducing a spherical Fourier integral to a one-dimensional
height integral.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

noncomputable section

/-- The nonnegative polar decomposition associated to the concrete surface
measure. -/
theorem lintegral_polar_unitSurfaceMeasure {d : ℕ} (hd : 0 < d)
    (H : Euclidean d → ℝ≥0∞) :
    (∫⁻ x : Euclidean d, H x) =
      ∫⁻ p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ),
        H (p.2.1 • (p.1 : Euclidean d)) ∂
          ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
  let i : Fin d := ⟨0, hd⟩
  letI : Nonempty (Fin d) := ⟨i⟩
  calc
    (∫⁻ x : Euclidean d, H x) =
        ∫⁻ x : ({0}ᶜ : Set (Euclidean d)), H x.1 ∂
          ((volume : Measure (Euclidean d)).comap Subtype.val) := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl H,
        restrict_compl_singleton]
    _ = ∫⁻ p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ),
        (H ∘ Subtype.val ∘ (homeomorphUnitSphereProd (Euclidean d)).symm) p ∂
          (((volume : Measure (Euclidean d)).toSphere).prod
            (Measure.volumeIoiPow (Module.finrank ℝ (Euclidean d) - 1))) := by
      let hpolar :=
        (volume : Measure (Euclidean d)).measurePreserving_homeomorphUnitSphereProd
      simpa using
        hpolar.lintegral_comp_emb
          (Homeomorph.measurableEmbedding _)
          (H ∘ Subtype.val ∘ (homeomorphUnitSphereProd (Euclidean d)).symm)
    _ = ∫⁻ p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ),
        H (p.2.1 • (p.1 : Euclidean d)) ∂
          ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
      simp [unitSurfaceMeasure]

/-- The radial power measure is Lebesgue measure on positive radii with its
literal `r ^ n` density. -/
theorem lintegral_volumeIoiPow (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ r : Ioi (0 : ℝ), F r ∂Measure.volumeIoiPow n) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ n * F r := by
  have hdensity : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ n)) :=
    (measurable_subtype_coe.pow measurable_const).ennreal_ofReal
  have hsubtype : Measurable (fun r : Ioi (0 : ℝ) => F r.1) :=
    hF.comp measurable_subtype_coe
  calc
    (∫⁻ r : Ioi (0 : ℝ), F r ∂Measure.volumeIoiPow n) =
        ∫⁻ r : Ioi (0 : ℝ),
          ENNReal.ofReal (r.1 ^ n) * F r.1 ∂(Measure.comap Subtype.val volume) := by
      unfold Measure.volumeIoiPow
      rw [lintegral_withDensity_eq_lintegral_mul _ hdensity hsubtype]
      rfl
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) * F r := by
      exact lintegral_subtype_comap (μ := volume) measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal (r ^ n) * F r)
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ n * F r := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      change ENNReal.ofReal (r ^ n) * F r = ENNReal.ofReal r ^ n * F r
      rw [ENNReal.ofReal_pow hr.le]

/-- Integrating a nonnegative radial function on Euclidean space factors into
the concrete surface mass and the radial power integral. -/
theorem lintegral_euclidean_radial {d : ℕ} (hd : 0 < d)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : Euclidean d, F ‖x‖) =
      ENNReal.ofReal (surfaceMass d) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (d - 1) * F r := by
  have hproduct : Measurable
      (fun p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ) => F p.2.1) :=
    hF.comp (measurable_subtype_coe.comp measurable_snd)
  have hmass : unitSurfaceMeasure d univ = ENNReal.ofReal (surfaceMass d) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (unitSurfaceMeasure d) univ)]
    rfl
  calc
    (∫⁻ x : Euclidean d, F ‖x‖) =
        ∫⁻ p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ),
          F ‖p.2.1 • (p.1 : Euclidean d)‖ ∂
            ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) :=
      lintegral_polar_unitSurfaceMeasure hd _
    _ = ∫⁻ p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ),
          F p.2.1 ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
      apply lintegral_congr
      rintro ⟨ω, r⟩
      have hω : ‖(ω : Euclidean d)‖ = 1 := by
        simpa only [mem_sphere_zero_iff_norm] using ω.property
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.2, hω, mul_one]
    _ = ∫⁻ ω : sphere (0 : Euclidean d) 1,
          (∫⁻ r : Ioi (0 : ℝ), F r.1 ∂Measure.volumeIoiPow (d - 1)) ∂
            unitSurfaceMeasure d :=
      lintegral_prod _ hproduct.aemeasurable
    _ = (∫⁻ r : Ioi (0 : ℝ), F r.1 ∂Measure.volumeIoiPow (d - 1)) *
          unitSurfaceMeasure d univ := by
      rw [lintegral_const]
    _ = ENNReal.ofReal (surfaceMass d) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (d - 1) * F r := by
      rw [hmass, lintegral_volumeIoiPow (d - 1) F hF]
      ac_rfl

/-- The cone over a small Euclidean cap of the unit sphere fits in a
comparably sized Euclidean ball.  Polar coordinates therefore turn the cap
measure into a literal ball-volume upper bound. -/
theorem unitSurfaceMeasure_cap_cone_le_volume_ball
    {d : Nat} (hd : 0 < d) (z : Euclidean d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    let S : Set (sphere (0 : Euclidean d) 1) :=
      (fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z ε
    let lo : Ioi (0 : ℝ) :=
      ⟨1 - ε, sub_pos.mpr (lt_of_le_of_lt hεhalf (by norm_num : (1 / 2 : ℝ) < 1))⟩
    let hi : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
    let I : Set (Ioi (0 : ℝ)) := Set.Icc lo hi
    (unitSurfaceMeasure d) S * (Measure.volumeIoiPow (d - 1)) I ≤
      volume (Metric.ball z (2 * ε)) := by
  dsimp
  let S : Set (sphere (0 : Euclidean d) 1) :=
    (fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z ε
  let lo : Ioi (0 : ℝ) :=
    ⟨1 - ε, sub_pos.mpr (lt_of_le_of_lt hεhalf (by norm_num : (1 / 2 : ℝ) < 1))⟩
  let hi : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  let I : Set (Ioi (0 : ℝ)) := Set.Icc lo hi
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_ball.preimage continuous_subtype_val.measurable
  have hI : MeasurableSet I := by
    dsimp [I]
    exact measurableSet_Icc
  have hpairs (p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ))
      (hp : p ∈ S ×ˢ I) : p.2.1 • (p.1 : Euclidean d) ∈ Metric.ball z (2 * ε) := by
    rcases hp with ⟨hpS, hpI⟩
    have hpS' : dist (p.1 : Euclidean d) z < ε := hpS
    have hpIlo : 1 - ε ≤ p.2.1 := hpI.1
    have hpIhi : p.2.1 ≤ 1 := hpI.2
    have hω : ‖(p.1 : Euclidean d)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using p.1.property
    rw [Metric.mem_ball]
    calc
      dist (p.2.1 • (p.1 : Euclidean d)) z ≤
          dist (p.2.1 • (p.1 : Euclidean d)) (p.1 : Euclidean d) +
            dist (p.1 : Euclidean d) z := dist_triangle _ _ _
      _ = ‖p.2.1 • (p.1 : Euclidean d) - (p.1 : Euclidean d)‖ +
            dist (p.1 : Euclidean d) z := by rw [dist_eq_norm]
      _ = ‖p.2.1 • (p.1 : Euclidean d) - (1 : ℝ) • (p.1 : Euclidean d)‖ +
            dist (p.1 : Euclidean d) z := by simp
      _ = ‖(p.2.1 - 1) • (p.1 : Euclidean d)‖ +
            dist (p.1 : Euclidean d) z := by
        have hsub : (p.2.1 - (1 : ℝ)) • (p.1 : Euclidean d) =
            p.2.1 • (p.1 : Euclidean d) - (1 : ℝ) • (p.1 : Euclidean d) :=
          sub_smul p.2.1 1 (p.1 : Euclidean d)
        rw [hsub]
      _ = |p.2.1 - 1| + dist (p.1 : Euclidean d) z := by
        rw [norm_smul, Real.norm_eq_abs, hω, mul_one]
      _ ≤ ε + dist (p.1 : Euclidean d) z := by
        gcongr
        rw [abs_of_nonpos (sub_nonpos.mpr hpIhi)]
        linarith
      _ < 2 * ε := by linarith
  have hindicator (p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ)) :
      (S ×ˢ I).indicator (fun _ => (1 : ℝ≥0∞)) p ≤
        (Metric.ball z (2 * ε)).indicator (fun _ => (1 : ℝ≥0∞))
          (p.2.1 • (p.1 : Euclidean d)) := by
    by_cases hp : p ∈ S ×ˢ I
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hpairs p hp)]
    · rw [Set.indicator_of_notMem hp]
      exact zero_le
  have hpolar := lintegral_polar_unitSurfaceMeasure hd
    ((Metric.ball z (2 * ε)).indicator (fun _ => (1 : ℝ≥0∞)))
  calc
    (unitSurfaceMeasure d) S * (Measure.volumeIoiPow (d - 1)) I =
        ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) (S ×ˢ I) :=
      (MeasureTheory.Measure.prod_prod S I).symm
    _ = ∫⁻ p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ),
        (S ×ˢ I).indicator (fun _ => (1 : ℝ≥0∞)) p ∂
          ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
      rw [lintegral_indicator_const (hS.prod hI)]
      simp
    _ ≤ ∫⁻ p : sphere (0 : Euclidean d) 1 × Ioi (0 : ℝ),
        (Metric.ball z (2 * ε)).indicator (fun _ => (1 : ℝ≥0∞))
          (p.2.1 • (p.1 : Euclidean d)) ∂
          ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) :=
      lintegral_mono hindicator
    _ = ∫⁻ x : Euclidean d,
        (Metric.ball z (2 * ε)).indicator (fun _ => (1 : ℝ≥0∞)) x := hpolar.symm
    _ = volume (Metric.ball z (2 * ε)) := by
      rw [lintegral_indicator_const measurableSet_ball]
      simp

/-- On the short radial interval used in the cap cone, the polar density is
bounded below by its value at `1 / 2`. -/
theorem volumeIoiPow_unit_interval_lower
    (n : Nat) {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    let lo : Ioi (0 : ℝ) :=
      ⟨1 - ε, sub_pos.mpr (lt_of_le_of_lt hεhalf (by norm_num : (1 / 2 : ℝ) < 1))⟩
    let hi : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
    let I : Set (Ioi (0 : ℝ)) := Set.Icc lo hi
    ENNReal.ofReal ((1 / 2 : ℝ) ^ n * ε) ≤
      (Measure.volumeIoiPow n) I := by
  dsimp
  let lo : Ioi (0 : ℝ) :=
    ⟨1 - ε, sub_pos.mpr (lt_of_le_of_lt hεhalf (by norm_num : (1 / 2 : ℝ) < 1))⟩
  let hi : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  let I : Set (Ioi (0 : ℝ)) := Set.Icc lo hi
  let J : Set ℝ := Set.Icc (1 - ε) 1
  have hJ : MeasurableSet J := by
    dsimp [J]
    exact measurableSet_Icc
  have hJpos : J ⊆ Ioi (0 : ℝ) := by
    intro r hr
    have : 1 - ε ≤ r := hr.1
    exact lt_of_lt_of_le
      (sub_pos.mpr (lt_of_le_of_lt hεhalf (by norm_num : (1 / 2 : ℝ) < 1))) this
  have hI : MeasurableSet I := by
    dsimp [I]
    exact measurableSet_Icc
  have hIeq : I = Subtype.val ⁻¹' J := by
    ext r
    change (lo ≤ r ∧ r ≤ hi) ↔ (1 - ε ≤ r.1 ∧ r.1 ≤ 1)
    rfl
  have hpow (r : ℝ) (hr : r ∈ J) : (1 / 2 : ℝ) ^ n ≤ r ^ n := by
    exact pow_le_pow_left₀ (by positivity)
      (by
        have : 1 - ε ≤ r := hr.1
        linarith [hεhalf]) n
  let c : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ n)
  have hpoint (r : ℝ) : J.indicator (fun _ => c) r ≤
      ENNReal.ofReal r ^ n * J.indicator (fun _ => (1 : ℝ≥0∞)) r := by
    by_cases hr : r ∈ J
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr]
      have hrnonneg : 0 ≤ r := by
        have : 1 - ε ≤ r := hr.1
        linarith [hεhalf]
      dsimp [c]
      rw [mul_one, ← ENNReal.ofReal_pow hrnonneg]
      exact ENNReal.ofReal_le_ofReal (hpow r hr)
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
      simp
  have hvolumeI :
      (Measure.volumeIoiPow n) I =
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ n *
          J.indicator (fun _ => (1 : ℝ≥0∞)) r := by
    calc
      (Measure.volumeIoiPow n) I =
          ∫⁻ r : Ioi (0 : ℝ), I.indicator (fun _ => (1 : ℝ≥0∞)) r ∂
            Measure.volumeIoiPow n := by
        rw [lintegral_indicator_const hI]
        simp
      _ = ∫⁻ r : Ioi (0 : ℝ), J.indicator (fun _ => (1 : ℝ≥0∞)) r.1 ∂
            Measure.volumeIoiPow n := by
        apply lintegral_congr
        intro r
        rw [hIeq]
        by_cases hr : r.1 ∈ J
        · have hr' : r ∈ Subtype.val ⁻¹' J := hr
          rw [Set.indicator_of_mem hr']
          rw [Set.indicator_of_mem hr]
        · have hr' : r ∉ Subtype.val ⁻¹' J := hr
          rw [Set.indicator_of_notMem hr']
          rw [Set.indicator_of_notMem hr]
      _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ n *
          J.indicator (fun _ => (1 : ℝ≥0∞)) r :=
        lintegral_volumeIoiPow n (J.indicator (fun _ => (1 : ℝ≥0∞)))
          ((measurable_indicator_const_iff 1).mpr hJ)
  have hlower :
      ∫⁻ r in Ioi (0 : ℝ), J.indicator (fun _ => c) r ≤
        (Measure.volumeIoiPow n) I := by
    rw [hvolumeI]
    exact lintegral_mono (fun r => hpoint r)
  have hleft :
      (∫⁻ r in Ioi (0 : ℝ), J.indicator (fun _ => c) r) =
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n * ε) := by
    rw [lintegral_indicator hJ]
    change ∫⁻ r : ℝ, c ∂(volume.restrict (Ioi (0 : ℝ))).restrict J = _
    rw [Measure.restrict_restrict hJ]
    simp only [Set.inter_eq_left.mpr hJpos]
    rw [setLIntegral_const, Real.volume_Icc]
    dsimp [c]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n)]
    congr 1
    ring
  rw [← hleft]
  exact hlower

/-- A small Euclidean cap of the concrete unit-sphere measure is bounded by
the volume of a comparable ball divided by its radial thickness. -/
theorem unitSurfaceMeasure_cap_le_volume_ball_div
    {d : Nat} (hd : 0 < d) (z : Euclidean d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    let S : Set (sphere (0 : Euclidean d) 1) :=
      (fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z ε
    (unitSurfaceMeasure d) S ≤
      volume (Metric.ball z (2 * ε)) /
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (d - 1) * ε) := by
  dsimp
  let S : Set (sphere (0 : Euclidean d) 1) :=
    (fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z ε
  let lo : Ioi (0 : ℝ) :=
    ⟨1 - ε, sub_pos.mpr (lt_of_le_of_lt hεhalf (by norm_num : (1 / 2 : ℝ) < 1))⟩
  let hi : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  let I : Set (Ioi (0 : ℝ)) := Set.Icc lo hi
  let q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ (d - 1) * ε)
  have hcone : (unitSurfaceMeasure d) S * (Measure.volumeIoiPow (d - 1)) I ≤
      volume (Metric.ball z (2 * ε)) := by
    simpa only [S, lo, hi, I] using
      unitSurfaceMeasure_cap_cone_le_volume_ball hd z hε hεhalf
  have hrad : q ≤ (Measure.volumeIoiPow (d - 1)) I := by
    dsimp only [q]
    simpa only [lo, hi, I] using
      volumeIoiPow_unit_interval_lower (d - 1) hε hεhalf
  have hqpos : 0 < q := by
    dsimp only [q]
    exact ENNReal.ofReal_pos.mpr (mul_pos (pow_pos (by norm_num) _) hε)
  have hmul : (unitSurfaceMeasure d) S * q ≤ volume (Metric.ball z (2 * ε)) := by
    calc
      (unitSurfaceMeasure d) S * q ≤
          (unitSurfaceMeasure d) S * (Measure.volumeIoiPow (d - 1)) I :=
        mul_le_mul_right hrad _
      _ ≤ volume (Metric.ball z (2 * ε)) := hcone
  apply (ENNReal.le_div_iff_mul_le (Or.inl hqpos.ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  exact hmul

private theorem cap_quotient_coefficient_le
    {d : Nat} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    ((2 * ε) ^ d) / ((1 / 2 : ℝ) ^ (d - 1) * ε) ≤
      (2 : ℝ) ^ (2 * d) * ε ^ (d - 1) := by
  have hden : 0 < (1 / 2 : ℝ) ^ (d - 1) * ε :=
    mul_pos (pow_pos (by norm_num) _) hε
  apply (div_le_iff₀ hden).2
  rw [mul_pow]
  rw [show ε ^ d = ε ^ (d - 1) * ε by
    rw [← pow_succ]
    congr 1
    omega]
  rw [show (1 / 2 : ℝ) ^ (d - 1) = ((2 : ℝ) ^ (d - 1))⁻¹ by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]]
  have hp : 0 < (2 : ℝ) ^ (d - 1) := pow_pos (by norm_num) _
  apply (le_of_mul_le_mul_right ?_ hp)
  field_simp
  rw [← pow_add]
  gcongr
  · norm_num
  · omega

/-- A Euclidean cap of radius at most `1 / 2` has the expected
codimension-one power bound for the concrete surface measure. -/
theorem unitSurfaceMeasure_cap_le_power
    {d : Nat} (hd : 0 < d) (z : Euclidean d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    let S : Set (sphere (0 : Euclidean d) 1) :=
      (fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z ε
    (unitSurfaceMeasure d) S ≤
      (2 : ℝ≥0∞) ^ (2 * d) * volume (Metric.ball (0 : Euclidean d) 1) *
        ENNReal.ofReal (ε ^ (d - 1)) := by
  dsimp
  let S : Set (sphere (0 : Euclidean d) 1) :=
    (fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z ε
  have hbase := unitSurfaceMeasure_cap_le_volume_ball_div hd z hε hεhalf
  have hbase' : (unitSurfaceMeasure d) S ≤
      volume (Metric.ball z (2 * ε)) /
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (d - 1) * ε) := by
    simpa only [S] using hbase
  have hradpos : 0 < (1 / 2 : ℝ) ^ (d - 1) * ε :=
    mul_pos (pow_pos (by norm_num) _) hε
  have hball : volume (Metric.ball z (2 * ε)) =
      ENNReal.ofReal ((2 * ε) ^ d) * volume (Metric.ball (0 : Euclidean d) 1) := by
    rw [Measure.addHaar_ball_of_pos volume z (mul_pos (by norm_num) hε)]
    simp only [finrank_euclideanSpace_fin]
  calc
    (unitSurfaceMeasure d) S ≤
        volume (Metric.ball z (2 * ε)) /
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (d - 1) * ε) := hbase'
    _ = volume (Metric.ball (0 : Euclidean d) 1) *
        ENNReal.ofReal (((2 * ε) ^ d) /
          ((1 / 2 : ℝ) ^ (d - 1) * ε)) := by
      rw [hball]
      rw [ENNReal.ofReal_div_of_pos hradpos]
      simp only [ENNReal.div_eq_inv_mul]
      ac_rfl
    _ ≤ (2 : ℝ≥0∞) ^ (2 * d) * volume (Metric.ball (0 : Euclidean d) 1) *
        ENNReal.ofReal (ε ^ (d - 1)) := by
      have hreal := cap_quotient_coefficient_le hd hε
      have henn : ENNReal.ofReal (((2 * ε) ^ d) /
          ((1 / 2 : ℝ) ^ (d - 1) * ε)) ≤
          (2 : ℝ≥0∞) ^ (2 * d) * ENNReal.ofReal (ε ^ (d - 1)) := by
        calc
          ENNReal.ofReal (((2 * ε) ^ d) /
              ((1 / 2 : ℝ) ^ (d - 1) * ε)) ≤
              ENNReal.ofReal ((2 : ℝ) ^ (2 * d) * ε ^ (d - 1)) :=
            ENNReal.ofReal_le_ofReal hreal
          _ = (2 : ℝ≥0∞) ^ (2 * d) * ENNReal.ofReal (ε ^ (d - 1)) := by
            rw [ENNReal.ofReal_mul (pow_nonneg (by norm_num) _)]
            rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
      calc
        volume (Metric.ball (0 : Euclidean d) 1) *
            ENNReal.ofReal (((2 * ε) ^ d) /
              ((1 / 2 : ℝ) ^ (d - 1) * ε)) ≤
            volume (Metric.ball (0 : Euclidean d) 1) *
              ((2 : ℝ≥0∞) ^ (2 * d) * ENNReal.ofReal (ε ^ (d - 1))) :=
          mul_le_mul_right henn _
        _ = (2 : ℝ≥0∞) ^ (2 * d) * volume (Metric.ball (0 : Euclidean d) 1) *
            ENNReal.ofReal (ε ^ (d - 1)) := by ac_rfl

/-- The concrete unit-sphere measure has global codimension-one ball growth.
The constant is finite and depends only on the dimension. -/
theorem exists_unitSurfaceMeasure_cap_le_power
    {d : Nat} (hd : 0 < d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (z : Euclidean d) (r : ℝ), 0 ≤ r →
      (unitSurfaceMeasure d)
        ((fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z r) ≤
        C * ENNReal.ofReal (r ^ (d - 1)) := by
  let V : ℝ≥0∞ := volume (Metric.ball (0 : Euclidean d) 1)
  let C : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (2 * d) * V +
    ENNReal.ofReal (surfaceMass d) * (2 : ℝ≥0∞) ^ (d - 1)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C, V]
    apply ENNReal.add_ne_top.2
    constructor
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
        MeasureTheory.measure_ball_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top (by norm_num))
  intro z r hr
  by_cases hrzero : r = 0
  · subst r
    rw [(Metric.ball_eq_empty.2 le_rfl), Set.preimage_empty, measure_empty]
    simp
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
  by_cases hrsmall : r ≤ 1 / 2
  · have hlocal := unitSurfaceMeasure_cap_le_power hd z hrpos hrsmall
    dsimp [C]
    have hcoefficient : (2 : ℝ≥0∞) ^ (2 * d) * V ≤
        (2 : ℝ≥0∞) ^ (2 * d) * V +
          ENNReal.ofReal (surfaceMass d) * (2 : ℝ≥0∞) ^ (d - 1) :=
      le_add_of_nonneg_right bot_le
    simpa only [V] using hlocal.trans (mul_le_mul_left hcoefficient _)
  have hrlarge : 1 / 2 < r := lt_of_not_ge hrsmall
  have hmeasure : (unitSurfaceMeasure d)
      ((fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z r) ≤
      ENNReal.ofReal (surfaceMass d) := by
    calc
      (unitSurfaceMeasure d)
          ((fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z r) ≤
          (unitSurfaceMeasure d) Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal (surfaceMass d) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        rfl
  have hfactor : 1 ≤ (2 : ℝ≥0∞) ^ (d - 1) * ENNReal.ofReal (r ^ (d - 1)) := by
    have hreal : 1 ≤ (2 * r) ^ (d - 1) := by
      apply one_le_pow₀
      linarith
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal ((2 * r) ^ (d - 1)) := ENNReal.ofReal_le_ofReal hreal
      _ = (2 : ℝ≥0∞) ^ (d - 1) * ENNReal.ofReal (r ^ (d - 1)) := by
        rw [mul_pow]
        rw [ENNReal.ofReal_mul (pow_nonneg (by norm_num) _)]
        rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hmass : ENNReal.ofReal (surfaceMass d) ≤
      (ENNReal.ofReal (surfaceMass d) * (2 : ℝ≥0∞) ^ (d - 1)) *
        ENNReal.ofReal (r ^ (d - 1)) := by
    calc
      ENNReal.ofReal (surfaceMass d) = ENNReal.ofReal (surfaceMass d) * 1 := by ring
      _ ≤ ENNReal.ofReal (surfaceMass d) *
          ((2 : ℝ≥0∞) ^ (d - 1) * ENNReal.ofReal (r ^ (d - 1))) :=
        mul_le_mul_right hfactor _
      _ = (ENNReal.ofReal (surfaceMass d) * (2 : ℝ≥0∞) ^ (d - 1)) *
          ENNReal.ofReal (r ^ (d - 1)) := by ring
  calc
    (unitSurfaceMeasure d)
        ((fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z r) ≤
        ENNReal.ofReal (surfaceMass d) := hmeasure
    _ ≤ (ENNReal.ofReal (surfaceMass d) * (2 : ℝ≥0∞) ^ (d - 1)) *
        ENNReal.ofReal (r ^ (d - 1)) := hmass
    _ ≤ C * ENNReal.ofReal (r ^ (d - 1)) := by
      apply mul_le_mul_left
      dsimp [C]
      exact le_add_of_nonneg_left bot_le

/-- Real-valued form of the global unit-sphere cap growth estimate. -/
theorem exists_unitSurfaceMeasure_cap_real_le_power
    {d : Nat} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Euclidean d) (r : ℝ), 0 ≤ r →
      ((unitSurfaceMeasure d)
        ((fun ω : sphere (0 : Euclidean d) 1 => (ω : Euclidean d)) ⁻¹' Metric.ball z r)).toReal ≤
        C * r ^ (d - 1) := by
  obtain ⟨C, hCtop, hcap⟩ := exists_unitSurfaceMeasure_cap_le_power hd
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro z r hr
  have hpow : 0 ≤ r ^ (d - 1) := pow_nonneg hr _
  have hbound := hcap z r hr
  have hright : C * ENNReal.ofReal (r ^ (d - 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top hCtop ENNReal.ofReal_ne_top
  have hrightreal : (C * ENNReal.ofReal (r ^ (d - 1))).toReal =
      C.toReal * r ^ (d - 1) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpow]
  rw [← hrightreal]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) hright).mpr hbound

end

end LeanSpherical.HarmonicAnalysis
