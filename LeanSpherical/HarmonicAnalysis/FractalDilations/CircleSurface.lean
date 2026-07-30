/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.CircleMeridian
import LeanSpherical.HarmonicAnalysis.SurfaceHeightCore

/-!
# The angular parametrization of planar surface measure

The general height-density theorem deliberately starts in ambient dimension
three, since the planar circle would have an inverse-square-root density.
For the circle it is more natural (and avoids that singular density) to keep
the angle parameter.  This file proves the needed specialization directly
from the cone definition of `unitSurfaceMeasure` and the existing polar
coordinate formula.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Metric Set
open scoped ENNReal Pointwise Topology

noncomputable section

/-- The cone through a final-coordinate slice of the unit circle has the
expected polar-coordinate volume. -/
theorem volume_height_cone_two_angle
    (A : Set ℝ) (hA : MeasurableSet A) :
    (2 : ℝ≥0∞) *
      volume {x : Euclidean 2 |
        0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x (Fin.last 1) / ‖x‖ ∈ A} =
      ENNReal.ofReal (surfaceMass 1) *
        ∫⁻ phi in Ioo (0 : ℝ) Real.pi, A.indicator 1 (Real.cos phi) := by
  let C : Set (Euclidean 2) := {x |
    0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x (Fin.last 1) / ‖x‖ ∈ A}
  let E : Set (ℝ × ℝ) := {q |
    0 < Real.sqrt (q.1 ^ 2 + q.2 ^ 2) ∧
      Real.sqrt (q.1 ^ 2 + q.2 ^ 2) < 1 ∧
        q.2 / Real.sqrt (q.1 ^ 2 + q.2 ^ 2) ∈ A}
  let G : ℝ × ℝ → ℝ≥0∞ := E.indicator 1
  let R : ℝ → ℝ≥0∞ := fun rho =>
    ENNReal.ofReal rho * (Iio (1 : ℝ)).indicator 1 rho
  let H : ℝ → ℝ≥0∞ := fun phi => A.indicator 1 (Real.cos phi)
  have hE : MeasurableSet E := by
    change MeasurableSet {q : ℝ × ℝ |
      0 < Real.sqrt (q.1 ^ 2 + q.2 ^ 2) ∧
        Real.sqrt (q.1 ^ 2 + q.2 ^ 2) < 1 ∧
          q.2 / Real.sqrt (q.1 ^ 2 + q.2 ^ 2) ∈ A}
    let radius : ℝ × ℝ → ℝ := fun q => Real.sqrt (q.1 ^ 2 + q.2 ^ 2)
    have hradius : Measurable radius :=
      ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).sqrt
    exact (measurableSet_lt measurable_const hradius).inter
      ((measurableSet_lt hradius measurable_const).inter
        (hA.preimage (measurable_snd.div hradius)))
  have hG : Measurable G := by
    change Measurable (E.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)))
    exact (measurable_indicator_const_iff 1).mpr hE
  have hcoord : Measurable (fun x : Euclidean 2 =>
      (‖MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
        x (Fin.last 1))) := by
    have hfirst : Measurable (fun x : Euclidean 2 =>
        MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))) := by
      apply (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.comp
      apply measurable_pi_lambda
      intro i
      fun_prop
    exact (measurable_norm.comp hfirst).prodMk (by fun_prop)
  have hCE : C =
      (fun x : Euclidean 2 =>
        (‖MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
          x (Fin.last 1))) ⁻¹' E := by
    ext x
    change (0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x (Fin.last 1) / ‖x‖ ∈ A) ↔
      (0 < Real.sqrt
        (‖MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
          (x (Fin.last 1)) ^ 2) ∧
        Real.sqrt
          (‖MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
            (x (Fin.last 1)) ^ 2) < 1 ∧
          x (Fin.last 1) /
              Real.sqrt
                (‖MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
                  (x (Fin.last 1)) ^ 2) ∈ A)
    rw [norm_euclideanSucc_coordinates]
  have hC : MeasurableSet C := by
    rw [hCE]
    exact hE.preimage hcoord
  have hpoint (x : Euclidean 2) :
      C.indicator 1 x =
        G (‖MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
          x (Fin.last 1)) := by
    change C.indicator 1 x = E.indicator 1
      (‖MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
        x (Fin.last 1))
    by_cases hx : x ∈ C
    · have hxE :
        (‖MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
          x (Fin.last 1)) ∈ E := by simpa [hCE] using hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxE]
      simp
    · have hxE :
        (‖MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
          x (Fin.last 1)) ∉ E := by
        intro hxE
        apply hx
        simpa [hCE] using hxE
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxE]
  have hR : Measurable R := by
    change Measurable (fun rho : ℝ =>
      ENNReal.ofReal rho * (Iio (1 : ℝ)).indicator 1 rho)
    exact measurable_id.ennreal_ofReal.mul
      ((measurable_indicator_const_iff 1).mpr measurableSet_Iio)
  have hAindicator : Measurable (A.indicator (fun _ : ℝ => (1 : ℝ≥0∞))) :=
    (measurable_indicator_const_iff 1).mpr hA
  have hH : Measurable H := by
    change Measurable (fun phi : ℝ => A.indicator 1 (Real.cos phi))
    exact hAindicator.comp Real.continuous_cos.measurable
  have hfactor (rho phi : ℝ) (hrho : 0 < rho) (hphi0 : 0 < phi) (hphipi : phi < Real.pi) :
      ENNReal.ofReal rho * ENNReal.ofReal (rho * Real.sin phi) ^ (1 - 1) *
          G (rho * Real.sin phi, rho * Real.cos phi) = R rho * H phi := by
    change ENNReal.ofReal rho * ENNReal.ofReal (rho * Real.sin phi) ^ (1 - 1) *
        E.indicator 1 (rho * Real.sin phi, rho * Real.cos phi) =
      (ENNReal.ofReal rho * (Iio (1 : ℝ)).indicator 1 rho) *
        A.indicator 1 (Real.cos phi)
    have hsin : 0 < Real.sin phi := Real.sin_pos_of_pos_of_lt_pi hphi0 hphipi
    have hsqrt := sqrt_spherical_meridian_norm_sq rho phi hrho.le
    have hvertical := spherical_normalized_vertical_eq_cos rho phi hrho
    have hmem : (rho * Real.sin phi, rho * Real.cos phi) ∈ E ↔
        rho < 1 ∧ Real.cos phi ∈ A := by
      change 0 < Real.sqrt ((rho * Real.sin phi) ^ 2 + (rho * Real.cos phi) ^ 2) ∧
        Real.sqrt ((rho * Real.sin phi) ^ 2 + (rho * Real.cos phi) ^ 2) < 1 ∧
          (rho * Real.cos phi) /
            Real.sqrt ((rho * Real.sin phi) ^ 2 + (rho * Real.cos phi) ^ 2) ∈ A ↔
        rho < 1 ∧ Real.cos phi ∈ A
      rw [hvertical, hsqrt]
      simp [hrho]
    simp only [Nat.reduceSub, pow_zero, mul_one]
    by_cases hrhoone : rho < 1 <;> by_cases hAcos : Real.cos phi ∈ A
    · have hE' : (rho * Real.sin phi, rho * Real.cos phi) ∈ E :=
        hmem.mpr ⟨hrhoone, hAcos⟩
      have hI : rho ∈ Iio (1 : ℝ) := hrhoone
      rw [Set.indicator_of_mem hE', Set.indicator_of_mem hI,
        Set.indicator_of_mem hAcos]
      simp
    · have hE' : (rho * Real.sin phi, rho * Real.cos phi) ∉ E := by
        exact fun h => hAcos (hmem.mp h).2
      have hI : rho ∈ Iio (1 : ℝ) := hrhoone
      rw [Set.indicator_of_notMem hE', Set.indicator_of_mem hI,
        Set.indicator_of_notMem hAcos]
      simp
    · have hE' : (rho * Real.sin phi, rho * Real.cos phi) ∉ E := by
        exact fun h => hrhoone (hmem.mp h).1
      have hI : rho ∉ Iio (1 : ℝ) := hrhoone
      rw [Set.indicator_of_notMem hE', Set.indicator_of_notMem hI,
        Set.indicator_of_mem hAcos]
      simp
    · have hE' : (rho * Real.sin phi, rho * Real.cos phi) ∉ E := by
        exact fun h => hrhoone (hmem.mp h).1
      have hI : rho ∉ Iio (1 : ℝ) := hrhoone
      rw [Set.indicator_of_notMem hE', Set.indicator_of_notMem hI,
        Set.indicator_of_notMem hAcos]
      simp
  have hRadial :
      (∫⁻ rho in Ioi (0 : ℝ), R rho) = ENNReal.ofReal (1 / (2 : ℝ)) := by
    let S : Set (Ioi (0 : ℝ)) := Iio ⟨1, by norm_num⟩
    let F : ℝ → ℝ≥0∞ := (Iio (1 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞))
    have hF : Measurable F := by
      change Measurable ((Iio (1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ≥0∞)))
      exact (measurable_indicator_const_iff 1).mpr measurableSet_Iio
    have hS : MeasurableSet S := by
      dsimp [S]
      exact measurableSet_Iio
    calc
      (∫⁻ rho in Ioi (0 : ℝ), R rho) =
          ∫⁻ rho : Ioi (0 : ℝ), F rho ∂Measure.volumeIoiPow 1 := by
        symm
        calc
          (∫⁻ rho : Ioi (0 : ℝ), F rho ∂Measure.volumeIoiPow 1) =
              ∫⁻ rho in Ioi (0 : ℝ), ENNReal.ofReal rho ^ 1 * F rho :=
            lintegral_volumeIoiPow 1 F hF
          _ = ∫⁻ rho in Ioi (0 : ℝ), R rho := by
            apply setLIntegral_congr_fun measurableSet_Ioi
            intro rho hrho
            change ENNReal.ofReal rho ^ 1 *
                (Iio (1 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) rho = R rho
            rw [pow_one]
            rfl
      _ = ∫⁻ rho in S, (1 : ℝ≥0∞) ∂Measure.volumeIoiPow 1 := by
        calc
          (∫⁻ rho : Ioi (0 : ℝ), F rho ∂Measure.volumeIoiPow 1) =
              ∫⁻ rho : Ioi (0 : ℝ), S.indicator (fun _ => (1 : ℝ≥0∞)) rho ∂
                Measure.volumeIoiPow 1 := by
            apply lintegral_congr
            intro rho
            change (Iio (1 : ℝ)).indicator (fun x => 1) rho =
              S.indicator (fun x => 1) rho
            by_cases hrho : rho.1 < 1
            · have hrhoS : rho ∈ S := by
                change rho < (⟨1, by norm_num⟩ : Ioi (0 : ℝ))
                exact hrho
              have hrhoI : (rho : ℝ) ∈ Iio (1 : ℝ) := hrho
              rw [Set.indicator_of_mem hrhoI, Set.indicator_of_mem hrhoS]
            · have hrhoS : rho ∉ S := by
                intro hrhoS
                apply hrho
                change rho.1 < 1 at hrhoS
                exact hrhoS
              have hrhoI : (rho : ℝ) ∉ Iio (1 : ℝ) := hrho
              rw [Set.indicator_of_notMem hrhoI, Set.indicator_of_notMem hrhoS]
          _ = ∫⁻ rho in S, (1 : ℝ≥0∞) ∂Measure.volumeIoiPow 1 :=
            lintegral_indicator hS _
      _ = Measure.volumeIoiPow 1 S := by simp
      _ = ENNReal.ofReal (1 / (2 : ℝ)) := by
        rw [Measure.volumeIoiPow_apply_Iio]
        norm_num [ENNReal.ofReal_div_of_pos]
  have hProduct :
      (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi, R p.1 * H p.2) =
        ENNReal.ofReal (1 / (2 : ℝ)) *
          (∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi) := by
    calc
      (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi, R p.1 * H p.2) =
          ∫⁻ rho in Ioi (0 : ℝ), ∫⁻ phi in Ioo (0 : ℝ) Real.pi, R rho * H phi := by
        apply setLIntegral_prod
        exact (hR.comp measurable_fst).mul (hH.comp measurable_snd) |>.aemeasurable.restrict
      _ = ∫⁻ rho in Ioi (0 : ℝ), R rho *
          (∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro rho hrho
        change (∫⁻ phi in Ioo (0 : ℝ) Real.pi, R rho * H phi) =
          R rho * (∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi)
        exact lintegral_const_mul (μ := volume.restrict (Ioo (0 : ℝ) Real.pi)) (R rho) hH
      _ = (∫⁻ rho in Ioi (0 : ℝ), R rho) *
          (∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi) := by
        exact lintegral_mul_const _ hR
      _ = ENNReal.ofReal (1 / (2 : ℝ)) *
          (∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi) := by
        rw [hRadial]
  have hVol : volume C =
      ENNReal.ofReal (surfaceMass 1) *
        (ENNReal.ofReal (1 / (2 : ℝ)) *
          ∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi) := by
    calc
      volume C = ∫⁻ x : Euclidean 2, C.indicator 1 x :=
        (lintegral_indicator_one hC).symm
      _ = ∫⁻ x : Euclidean 2,
          G (‖MeasurableEquiv.toLp 2 (Fin 1 → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
            x (Fin.last 1)) := by
        apply lintegral_congr
        intro x
        exact hpoint x
      _ = ENNReal.ofReal (surfaceMass 1) *
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
            ENNReal.ofReal p.1 * ENNReal.ofReal (p.1 * Real.sin p.2) ^ (1 - 1) *
              G (p.1 * Real.sin p.2, p.1 * Real.cos p.2) :=
        lintegral_euclideanSucc_spherical (d := 1) (by norm_num) G hG
      _ = ENNReal.ofReal (surfaceMass 1) *
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi, R p.1 * H p.2 := by
        congr 1
        apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp
        exact hfactor p.1 p.2 hp.1 hp.2.1 hp.2.2
      _ = ENNReal.ofReal (surfaceMass 1) *
          (ENNReal.ofReal (1 / (2 : ℝ)) *
            ∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi) := by
        rw [hProduct]
  have hscalar : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)) = 1 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa using ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by simp)
  change (2 : ℝ≥0∞) * volume C = _
  rw [hVol]
  calc
    (2 : ℝ≥0∞) *
        (ENNReal.ofReal (surfaceMass 1) *
          (ENNReal.ofReal (1 / (2 : ℝ)) *
            ∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi)) =
        ENNReal.ofReal (surfaceMass 1) *
          (((2 : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ))) *
            ∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi) := by ring
    _ = ENNReal.ofReal (surfaceMass 1) *
        (1 * ∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi) := by rw [hscalar]
    _ = ENNReal.ofReal (surfaceMass 1) *
        ∫⁻ phi in Ioo (0 : ℝ) Real.pi, H phi := by simp

/-- The final-coordinate projection of the concrete circle measure is the
angle measure pushed forward by cosine. -/
theorem map_unitSurfaceMeasure_two_height :
    Measure.map
        (fun omega : sphere (0 : Euclidean 2) 1 =>
          (omega : Euclidean 2) (Fin.last 1))
        (unitSurfaceMeasure 2) =
      ENNReal.ofReal (surfaceMass 1) •
        Measure.map Real.cos (volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  let height : sphere (0 : Euclidean 2) 1 → ℝ :=
    fun omega => (omega : Euclidean 2) (Fin.last 1)
  let mu : Measure ℝ := volume.restrict (Ioo (0 : ℝ) Real.pi)
  have hheight : Measurable height := by
    dsimp [height]
    fun_prop
  have hcos : Measurable Real.cos := Real.continuous_cos.measurable
  apply Measure.ext
  intro A hA
  have hS : MeasurableSet
      {omega : sphere (0 : Euclidean 2) 1 |
        (omega : Euclidean 2) (Fin.last 1) ∈ A} :=
    hA.preimage hheight
  have hpre : MeasurableSet (Real.cos ⁻¹' A) := hA.preimage hcos
  have hangle :
      (∫⁻ phi in Ioo (0 : ℝ) Real.pi, A.indicator 1 (Real.cos phi)) =
        volume ((Real.cos ⁻¹' A) ∩ Ioo (0 : ℝ) Real.pi) := by
    calc
      (∫⁻ phi in Ioo (0 : ℝ) Real.pi, A.indicator 1 (Real.cos phi)) =
          ∫⁻ phi in Ioo (0 : ℝ) Real.pi,
            (Real.cos ⁻¹' A).indicator 1 phi := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro phi hphi
        by_cases hphiA : Real.cos phi ∈ A
        · have hphiPre : phi ∈ Real.cos ⁻¹' A := hphiA
          change A.indicator 1 (Real.cos phi) = (Real.cos ⁻¹' A).indicator 1 phi
          rw [Set.indicator_of_mem hphiA, Set.indicator_of_mem hphiPre]
          simp
        · have hphiPre : phi ∉ Real.cos ⁻¹' A := hphiA
          change A.indicator 1 (Real.cos phi) = (Real.cos ⁻¹' A).indicator 1 phi
          rw [Set.indicator_of_notMem hphiA, Set.indicator_of_notMem hphiPre]
      _ = ∫⁻ phi in Real.cos ⁻¹' A, (1 : ℝ≥0∞) ∂
          volume.restrict (Ioo (0 : ℝ) Real.pi) := by
        exact lintegral_indicator hpre _
      _ = (volume.restrict (Ioo (0 : ℝ) Real.pi)) (Real.cos ⁻¹' A) := by simp
      _ = volume ((Real.cos ⁻¹' A) ∩ Ioo (0 : ℝ) Real.pi) := by
        rw [Measure.restrict_apply hpre]
  rw [Measure.map_apply hheight hA, Measure.smul_apply,
    Measure.map_apply hcos hA, Measure.restrict_apply hpre]
  change unitSurfaceMeasure 2
      {omega : sphere (0 : Euclidean 2) 1 |
        (omega : Euclidean 2) (Fin.last 1) ∈ A} =
    ENNReal.ofReal (surfaceMass 1) *
      volume ((Real.cos ⁻¹' A) ∩ Ioo (0 : ℝ) Real.pi)
  rw [unitSurfaceMeasure, Measure.toSphere_apply' volume hS,
    height_cone_succ_eq]
  rw [← hangle]
  convert volume_height_cone_two_angle A hA using 1 <;> norm_num

/-- Integrating a continuous function of the final coordinate against the
circle surface measure is integration against the angular parametrization. -/
theorem integral_comp_last_unitSurfaceMeasure_two
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ omega : sphere (0 : Euclidean 2) 1,
      F ((omega : Euclidean 2) (Fin.last 1)) ∂unitSurfaceMeasure 2) =
      (surfaceMass 1 : ℂ) *
        ∫ phi in (0 : ℝ)..Real.pi, F (Real.cos phi) := by
  let height : sphere (0 : Euclidean 2) 1 → ℝ :=
    fun omega => (omega : Euclidean 2) (Fin.last 1)
  let mu : Measure ℝ := volume.restrict (Ioo (0 : ℝ) Real.pi)
  have hheight : Measurable height := by
    dsimp [height]
    fun_prop
  have hcos : Measurable Real.cos := Real.continuous_cos.measurable
  have hmap : Measure.map height (unitSurfaceMeasure 2) =
      ENNReal.ofReal (surfaceMass 1) • Measure.map Real.cos mu := by
    dsimp [height, mu]
    exact map_unitSurfaceMeasure_two_height
  have hmass_nonneg : 0 ≤ surfaceMass 1 := measureReal_nonneg
  calc
    (∫ omega : sphere (0 : Euclidean 2) 1,
      F ((omega : Euclidean 2) (Fin.last 1)) ∂unitSurfaceMeasure 2) =
        ∫ t, F t ∂Measure.map height (unitSurfaceMeasure 2) := by
      exact (MeasureTheory.integral_map hheight.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ t, F t ∂(ENNReal.ofReal (surfaceMass 1) • Measure.map Real.cos mu) := by
      rw [hmap]
    _ = (surfaceMass 1 : ℂ) * ∫ t, F t ∂Measure.map Real.cos mu := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hmass_nonneg]
      simp only [Complex.real_smul]
    _ = (surfaceMass 1 : ℂ) * ∫ phi, F (Real.cos phi) ∂mu := by
      congr 1
      exact MeasureTheory.integral_map hcos.aemeasurable hF.aestronglyMeasurable
    _ = (surfaceMass 1 : ℂ) * ∫ phi in (0 : ℝ)..Real.pi, F (Real.cos phi) := by
      congr 1
      dsimp [mu]
      rw [intervalIntegral.integral_of_le (le_of_lt Real.pi_pos),
        integral_Ioc_eq_integral_Ioo]

/-- The cosine angle integral is the same meridian integral used in
`CircleMeridian`, after the substitution `phi = pi / 2 - theta`. -/
theorem intervalIntegral_circle_cos_eq_meridian (l : ℝ) :
    (∫ phi in (0 : ℝ)..Real.pi,
      Complex.exp (((-l * Real.cos phi : ℝ) : ℂ) * Complex.I)) =
      ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        circleMeridianPhase l theta := by
  let f : ℝ → ℂ := circleMeridianPhase l
  have hphase (phi : ℝ) :
      f (Real.pi / 2 - phi) =
        Complex.exp (((-l * Real.cos phi : ℝ) : ℂ) * Complex.I) := by
    dsimp [f, circleMeridianPhase]
    rw [Real.sin_pi_div_two_sub]
  calc
    (∫ phi in (0 : ℝ)..Real.pi,
      Complex.exp (((-l * Real.cos phi : ℝ) : ℂ) * Complex.I)) =
        ∫ phi in (0 : ℝ)..Real.pi, f (Real.pi / 2 - phi) := by
      apply intervalIntegral.integral_congr
      intro phi hphi
      change Complex.exp (((-l * Real.cos phi : ℝ) : ℂ) * Complex.I) =
        f (Real.pi / 2 - phi)
      rw [← hphase]
    _ = ∫ theta in Real.pi / 2 - Real.pi..Real.pi / 2 - 0, f theta :=
      intervalIntegral.integral_comp_sub_left f (Real.pi / 2)
    _ = ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2), f theta := by
      congr 1 <;> ring

/-- Along the final coordinate axis, the Fourier transform of circle surface
measure is exactly the angular meridian integral. -/
theorem surfaceFourier_axis_last_two (a : ℝ) :
    surfaceFourier 2
      (a • MeasurableEquiv.toLp 2 (Fin 2 → ℝ)
        (fun i => if i = Fin.last 1 then 1 else 0)) =
      (surfaceMass 1 : ℂ) *
        ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          circleMeridianPhase (2 * Real.pi * a) theta := by
  let e : Euclidean 2 :=
    MeasurableEquiv.toLp 2 (Fin 2 → ℝ)
      (fun i => if i = Fin.last 1 then 1 else 0)
  let F : ℝ → ℂ := fun t =>
    Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hinter (x : Euclidean 2) : inner ℝ x e = x (Fin.last 1) := by
    dsimp [e]
    exact inner_euclideanSucc_last 1 x
  calc
    surfaceFourier 2 (a • e) =
        ∫ omega : sphere (0 : Euclidean 2) 1,
          F ((omega : Euclidean 2) (Fin.last 1)) ∂unitSurfaceMeasure 2 := by
      unfold surfaceFourier
      apply integral_congr_ae
      filter_upwards with omega
      dsimp [F]
      unfold surfacePhase
      rw [inner_smul_right, hinter]
      push_cast
      ring_nf
    _ = (surfaceMass 1 : ℂ) *
        ∫ phi in (0 : ℝ)..Real.pi, F (Real.cos phi) :=
      integral_comp_last_unitSurfaceMeasure_two F hF
    _ = (surfaceMass 1 : ℂ) *
        ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          circleMeridianPhase (2 * Real.pi * a) theta := by
      congr 1
      calc
        (∫ phi in (0 : ℝ)..Real.pi, F (Real.cos phi)) =
            ∫ phi in (0 : ℝ)..Real.pi,
              Complex.exp (((-(2 * Real.pi * a) * Real.cos phi : ℝ) : ℂ) * Complex.I) := by
          apply intervalIntegral.integral_congr
          intro phi hphi
          dsimp [F]
          push_cast
          ring
        _ = ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            circleMeridianPhase (2 * Real.pi * a) theta :=
          intervalIntegral_circle_cos_eq_meridian (2 * Real.pi * a)

/-- Radial symmetry turns the circle Fourier transform into the meridian
integral at frequency `2*pi*‖xi‖`. -/
theorem surfaceFourier_two_meridian (xi : Euclidean 2) :
    surfaceFourier 2 xi =
      (surfaceMass 1 : ℂ) *
        ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          circleMeridianPhase (2 * Real.pi * ‖xi‖) theta := by
  let e : Euclidean 2 :=
    MeasurableEquiv.toLp 2 (Fin 2 → ℝ)
      (fun i => if i = Fin.last 1 then 1 else 0)
  have he : ‖e‖ = 1 := by
    dsimp [e]
    exact norm_euclideanSucc_last 1
  calc
    surfaceFourier 2 xi = surfaceFourier 2 (‖xi‖ • e) :=
      surfaceFourier_eq_norm_smul_unit 2 xi e he
    _ = (surfaceMass 1 : ℂ) *
        ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          circleMeridianPhase (2 * Real.pi * ‖xi‖) theta :=
      surfaceFourier_axis_last_two ‖xi‖

/-- Sharp Fourier decay for the planar circle, obtained from the angular
meridian estimate. -/
theorem exists_sharp_surfaceFourier_two_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ xi : Euclidean 2, 1 ≤ ‖xi‖ →
      ‖surfaceFourier 2 xi‖ ≤ C / ‖xi‖ ^ ((1 : ℝ) / 2) := by
  have hmass : 0 ≤ surfaceMass 1 := measureReal_nonneg
  refine ⟨(surfaceMass 1 + 1) * 124, mul_pos (by linarith) (by norm_num), ?_⟩
  intro xi hxi
  let l : ℝ := 2 * Real.pi * ‖xi‖
  have htwo_pi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hl : 1 ≤ l := by
    dsimp [l]
    calc
      1 ≤ (2 * Real.pi) * 1 := by simpa using htwo_pi
      _ ≤ (2 * Real.pi) * ‖xi‖ := by gcongr
  have hnormpos : 0 < ‖xi‖ := lt_of_lt_of_le (by norm_num) hxi
  have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hnorm_le_l : ‖xi‖ ≤ l := by
    dsimp [l]
    calc
      ‖xi‖ = 1 * ‖xi‖ := by ring
      _ ≤ (2 * Real.pi) * ‖xi‖ := mul_le_mul_of_nonneg_right htwo_pi (norm_nonneg _)
  have hroot : Real.sqrt ‖xi‖ ≤ Real.sqrt l := Real.sqrt_le_sqrt hnorm_le_l
  have hrootnormpos : 0 < Real.sqrt ‖xi‖ := Real.sqrt_pos.2 hnormpos
  have hrootlpos : 0 < Real.sqrt l := Real.sqrt_pos.2 hlpos
  have hratio : 124 / Real.sqrt l ≤ 124 / Real.sqrt ‖xi‖ := by
    rw [div_le_div_iff₀ hrootlpos hrootnormpos]
    exact mul_le_mul_of_nonneg_left hroot (by norm_num)
  have hI := norm_circle_meridian_unweighted_le l hl
  rw [surfaceFourier_two_meridian]
  change ‖(surfaceMass 1 : ℂ) *
      (∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        circleMeridianPhase (2 * Real.pi * ‖xi‖) theta)‖ ≤
      ((surfaceMass 1 + 1) * 124) / ‖xi‖ ^ ((1 : ℝ) / 2)
  change ‖(surfaceMass 1 : ℂ) *
      (∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        circleMeridianPhase l theta)‖ ≤
      ((surfaceMass 1 + 1) * 124) / ‖xi‖ ^ ((1 : ℝ) / 2)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hmass]
  rw [← Real.sqrt_eq_rpow]
  calc
    surfaceMass 1 * ‖∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
      circleMeridianPhase l theta‖ ≤ surfaceMass 1 * (124 / Real.sqrt l) :=
      mul_le_mul_of_nonneg_left hI hmass
    _ ≤ surfaceMass 1 * (124 / Real.sqrt ‖xi‖) :=
      mul_le_mul_of_nonneg_left hratio hmass
    _ ≤ (surfaceMass 1 + 1) * (124 / Real.sqrt ‖xi‖) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ((surfaceMass 1 + 1) * 124) / Real.sqrt ‖xi‖ := by ring

private theorem hasDerivAt_circle_meridian (l : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          circleMeridianPhase u theta)
      (∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        ((-Real.sin theta : ℝ) : ℂ) * circleMeridianPhase l theta * Complex.I) l := by
  let a : ℝ := -(Real.pi / 2)
  let b : ℝ := Real.pi / 2
  let F : ℝ → ℝ → ℂ := fun u theta => circleMeridianPhase u theta
  let F' : ℝ → ℝ → ℂ := fun u theta =>
    ((-Real.sin theta : ℝ) : ℂ) * circleMeridianPhase u theta * Complex.I
  have hab : a ≤ b := by
    dsimp [a, b]
    exact neg_le_self (le_of_lt (div_pos Real.pi_pos (by norm_num)))
  change HasDerivAt
    (fun u : ℝ => ∫ theta in a..b, F u theta)
    (∫ theta in a..b, F' l theta) l
  simp_rw [intervalIntegral.integral_of_le hab]
  change HasDerivAt
    (fun u : ℝ => ∫ theta, F u theta ∂volume.restrict (Set.Ioc a b))
    (∫ theta, F' l theta ∂volume.restrict (Set.Ioc a b)) l
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc a b)) (s := Set.univ) (x₀ := l)
    (bound := fun _ : ℝ => (1 : ℝ))
    (F := F) (F' := F') Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact h.2
  · filter_upwards [] with u
    exact (by
      dsimp [F, circleMeridianPhase]
      fun_prop : Continuous (fun theta : ℝ => F u theta)).aestronglyMeasurable
  · refine Integrable.of_bound ?_ 1 ?_
    · exact (by
        dsimp [F, circleMeridianPhase]
        fun_prop : Continuous (fun theta : ℝ => F l theta)).aestronglyMeasurable
    · filter_upwards with theta
      dsimp [F, circleMeridianPhase]
      rw [Complex.norm_exp_ofReal_mul_I]
  · exact (by
      dsimp [F', circleMeridianPhase]
      fun_prop : Continuous (fun theta : ℝ => F' l theta)).aestronglyMeasurable
  · filter_upwards with theta
    intro u hu
    dsimp [F', circleMeridianPhase]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_neg, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one]
    simpa using Real.abs_sin_le_one theta
  · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
  · filter_upwards with theta
    intro u hu
    dsimp [F, F', circleMeridianPhase]
    have harg : HasDerivAt
        (fun v : ℝ => ((-v * Real.sin theta : ℝ) : ℂ) * Complex.I)
        (((-Real.sin theta : ℝ) : ℂ) * Complex.I) u := by
      have hreal : HasDerivAt (fun v : ℝ => -v * Real.sin theta)
          (-Real.sin theta) u := by
        simpa [mul_comm] using (hasDerivAt_id u).mul_const (-Real.sin theta)
      simpa only [Complex.real_smul] using hreal.smul_const Complex.I
    have hexp := harg.cexp
    simpa [mul_assoc, mul_left_comm, mul_comm] using hexp

private theorem hasDerivAt_surfaceFourier_two_meridian_smul
    (xi : Euclidean 2) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => surfaceFourier 2 (s • xi))
      ((surfaceMass 1 : ℂ) *
        ((2 * Real.pi * ‖xi‖ : ℝ) : ℂ) *
          (∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((-Real.sin theta : ℝ) : ℂ) *
              circleMeridianPhase (2 * Real.pi * r * ‖xi‖) theta * Complex.I)) r := by
  let I : ℝ → ℂ := fun l =>
    ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
      circleMeridianPhase l theta
  have hlinear : HasDerivAt (fun s : ℝ => 2 * Real.pi * s * ‖xi‖)
      (2 * Real.pi * ‖xi‖) r := by
    simpa [mul_assoc] using ((hasDerivAt_id r).mul_const ‖xi‖).const_mul (2 * Real.pi)
  have hIderiv := hasDerivAt_circle_meridian (2 * Real.pi * r * ‖xi‖)
  have hcomp : HasDerivAt (fun s : ℝ => I (2 * Real.pi * s * ‖xi‖))
      (((2 * Real.pi * ‖xi‖ : ℝ) : ℂ) *
        ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          ((-Real.sin theta : ℝ) : ℂ) *
            circleMeridianPhase (2 * Real.pi * r * ‖xi‖) theta * Complex.I) r := by
    dsimp [I]
    simpa [Function.comp_def, Complex.real_smul] using
      HasDerivAt.scomp_of_eq r hIderiv hlinear (by rfl)
  have hmodel := hcomp.const_mul (surfaceMass 1 : ℂ)
  have hlocal : (fun s : ℝ => surfaceFourier 2 (s • xi)) =ᶠ[𝓝 r]
      fun s => (surfaceMass 1 : ℂ) * I (2 * Real.pi * s * ‖xi‖) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    rw [surfaceFourier_two_meridian (s • xi)]
    have hnorm : ‖s • xi‖ = s * ‖xi‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    rw [hnorm]
    dsimp [I]
    congr 1
    apply intervalIntegral.integral_congr
    intro theta htheta
    push_cast
    ring_nf
  have hresult := hmodel.congr_of_eventuallyEq hlocal
  simpa only [I, Complex.real_smul, mul_assoc] using hresult

private theorem norm_circle_meridian_derivative_integral_le (l : ℝ) (hl : 1 ≤ l) :
    ‖∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
      ((-Real.sin theta : ℝ) : ℂ) * circleMeridianPhase l theta * Complex.I‖ ≤
      16 / Real.sqrt l := by
  have hrewrite :
      (∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        ((-Real.sin theta : ℝ) : ℂ) * circleMeridianPhase l theta * Complex.I) =
        (-Complex.I) *
          (∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((Real.sin theta : ℝ) : ℂ) * circleMeridianPhase l theta) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro theta htheta
    push_cast
    ring
  rw [hrewrite, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact norm_circle_meridian_sin_le l hl

/-- The sharp radius-derivative bound for the planar circle. -/
theorem exists_sharp_surfaceFourier_two_deriv :
    ∃ C : ℝ, 0 < C ∧ ∀ xi : Euclidean 2, ∀ r : ℝ,
      1 ≤ ‖xi‖ → r ∈ Icc (1 : ℝ) 2 →
        ‖deriv (fun s : ℝ => surfaceFourier 2 (s • xi)) r‖ ≤
          C / ‖xi‖ ^ ((1 : ℝ) / 2 - 1) := by
  have hmass : 0 ≤ surfaceMass 1 := measureReal_nonneg
  have htwo_pi_pos : 0 < 2 * Real.pi := by positivity
  refine ⟨(surfaceMass 1 + 1) * (2 * Real.pi) * 16,
    mul_pos (mul_pos (by linarith) htwo_pi_pos) (by norm_num), ?_⟩
  intro xi r hxi hr
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
  let l : ℝ := 2 * Real.pi * r * ‖xi‖
  let D : ℂ := ∫ theta in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
    ((-Real.sin theta : ℝ) : ℂ) * circleMeridianPhase l theta * Complex.I
  have htwo_pi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hl : 1 ≤ l := by
    dsimp [l]
    calc
      1 ≤ (2 * Real.pi) * 1 * 1 := by simpa using htwo_pi
      _ ≤ (2 * Real.pi) * r * ‖xi‖ := by
        gcongr
        exact hr.1
  have hnormpos : 0 < ‖xi‖ := lt_of_lt_of_le (by norm_num) hxi
  have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hnorm_le_l : ‖xi‖ ≤ l := by
    dsimp [l]
    calc
      ‖xi‖ = 1 * 1 * ‖xi‖ := by ring
      _ ≤ (2 * Real.pi) * r * ‖xi‖ := by
        gcongr
        exact hr.1
  have hroot : Real.sqrt ‖xi‖ ≤ Real.sqrt l := Real.sqrt_le_sqrt hnorm_le_l
  have hrootnormpos : 0 < Real.sqrt ‖xi‖ := Real.sqrt_pos.2 hnormpos
  have hrootlpos : 0 < Real.sqrt l := Real.sqrt_pos.2 hlpos
  have hratio : 16 / Real.sqrt l ≤ 16 / Real.sqrt ‖xi‖ := by
    rw [div_le_div_iff₀ hrootlpos hrootnormpos]
    exact mul_le_mul_of_nonneg_left hroot (by norm_num)
  have hD : ‖D‖ ≤ 16 / Real.sqrt l := by
    dsimp [D]
    exact norm_circle_meridian_derivative_integral_le l hl
  have hnorm_factor : ‖xi‖ * (16 / Real.sqrt l) ≤ 16 * Real.sqrt ‖xi‖ := by
    calc
      ‖xi‖ * (16 / Real.sqrt l) ≤ ‖xi‖ * (16 / Real.sqrt ‖xi‖) :=
        mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
      _ = 16 * Real.sqrt ‖xi‖ := by
        have hsquare : Real.sqrt ‖xi‖ * Real.sqrt ‖xi‖ = ‖xi‖ :=
          Real.mul_self_sqrt (norm_nonneg _)
        calc
          ‖xi‖ * (16 / Real.sqrt ‖xi‖) =
              (Real.sqrt ‖xi‖ * Real.sqrt ‖xi‖) * (16 / Real.sqrt ‖xi‖) := by
            rw [hsquare]
          _ = 16 * Real.sqrt ‖xi‖ := by
            field_simp [hrootnormpos.ne']
  have hpow : ‖xi‖ ^ ((1 : ℝ) / 2 - 1) = (Real.sqrt ‖xi‖)⁻¹ := by
    calc
      ‖xi‖ ^ ((1 : ℝ) / 2 - 1) = ‖xi‖ ^ (-((1 : ℝ) / 2)) := by
        congr 1
        ring
      _ = (‖xi‖ ^ ((1 : ℝ) / 2))⁻¹ := Real.rpow_neg (norm_nonneg _) _
      _ = (Real.sqrt ‖xi‖)⁻¹ := by rw [← Real.sqrt_eq_rpow]
  rw [(hasDerivAt_surfaceFourier_two_meridian_smul xi hrpos).deriv]
  change ‖(surfaceMass 1 : ℂ) * ((2 * Real.pi * ‖xi‖ : ℝ) : ℂ) * D‖ ≤
    ((surfaceMass 1 + 1) * (2 * Real.pi) * 16) /
      ‖xi‖ ^ ((1 : ℝ) / 2 - 1)
  rw [hpow, div_eq_mul_inv, inv_inv]
  have hfactor_nonneg : 0 ≤ 2 * Real.pi * ‖xi‖ := by positivity
  calc
    ‖(surfaceMass 1 : ℂ) * ((2 * Real.pi * ‖xi‖ : ℝ) : ℂ) * D‖ =
        surfaceMass 1 * (2 * Real.pi * ‖xi‖) * ‖D‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hmass,
        Complex.norm_real, Real.norm_of_nonneg hfactor_nonneg]
    _ ≤ surfaceMass 1 * (2 * Real.pi * ‖xi‖) * (16 / Real.sqrt l) := by
      gcongr
    _ = (surfaceMass 1 * (2 * Real.pi)) *
        (‖xi‖ * (16 / Real.sqrt l)) := by ring
    _ ≤ (surfaceMass 1 * (2 * Real.pi)) * (16 * Real.sqrt ‖xi‖) := by
      exact mul_le_mul_of_nonneg_left hnorm_factor (by positivity)
    _ = surfaceMass 1 * ((2 * Real.pi) * 16 * Real.sqrt ‖xi‖) := by ring
    _ ≤ (surfaceMass 1 + 1) * ((2 * Real.pi) * 16 * Real.sqrt ‖xi‖) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = ((surfaceMass 1 + 1) * (2 * Real.pi) * 16) * Real.sqrt ‖xi‖ := by ring

/-- The sharp decay and radius-derivative estimates for circle surface
measure, bundled in the form used by the dyadic maximal argument. -/
theorem exists_sharp_surfaceFourier_two_decay_and_deriv :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      (∀ xi : Euclidean 2, 1 ≤ ‖xi‖ →
        ‖surfaceFourier 2 xi‖ ≤ C₀ / ‖xi‖ ^ ((1 : ℝ) / 2)) ∧
      (∀ xi : Euclidean 2, ∀ r : ℝ, 1 ≤ ‖xi‖ → r ∈ Icc (1 : ℝ) 2 →
        ‖deriv (fun s : ℝ => surfaceFourier 2 (s • xi)) r‖ ≤
          C₁ / ‖xi‖ ^ ((1 : ℝ) / 2 - 1)) := by
  rcases exists_sharp_surfaceFourier_two_decay with ⟨C₀, hC₀, hdecay⟩
  rcases exists_sharp_surfaceFourier_two_deriv with ⟨C₁, hC₁, hderiv⟩
  exact ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
