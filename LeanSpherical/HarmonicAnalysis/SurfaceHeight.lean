/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.CosineSubstitution
import LeanSpherical.HarmonicAnalysis.HeightPolar
import LeanSpherical.HarmonicAnalysis.SurfaceSymmetry
import LeanSpherical.HarmonicAnalysis.ThreeDimensionalSpherical
import LeanSpherical.HarmonicAnalysis.SemicircleDecay
import LeanSpherical.HarmonicAnalysis.OscillatoryIntegral
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The general height distribution of spherical surface measure

For `d ≥ 2`, projecting the concrete measure on the unit sphere in
`Euclidean (d + 1)` onto its final coordinate has density
`surfaceMass d * (sqrt (1 - t^2))^(d - 2)` on `(-1, 1)`.  This is the
dimension-uniform geometric reduction behind the one-dimensional
oscillatory-integral proof of surface Fourier decay.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Metric Set
open scoped ENNReal Pointwise Topology

noncomputable section

/-- The cone through a final-coordinate slice of the unit sphere has the
corresponding normalized-height description. -/
theorem height_cone_succ_eq (d : Nat) (A : Set ℝ) :
    Set.Ioo (0 : ℝ) 1 •
        ((Subtype.val : sphere (0 : Euclidean (d + 1)) 1 → Euclidean (d + 1)) ''
          {ω : sphere (0 : Euclidean (d + 1)) 1 | (ω : Euclidean (d + 1)) (Fin.last d) ∈ A}) =
      {x : Euclidean (d + 1) |
        0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x (Fin.last d) / ‖x‖ ∈ A} := by
  ext x
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩
    rcases hy with ⟨ω, hω, rfl⟩
    have hωnorm : ‖(ω : Euclidean (d + 1))‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using ω.property
    constructor
    · simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hωnorm] using hr.1
    constructor
    · simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hωnorm] using hr.2
    · change (r • (ω : Euclidean (d + 1))) (Fin.last d) /
          ‖r • (ω : Euclidean (d + 1))‖ ∈ A
      rw [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
        hωnorm, mul_one]
      simpa [mul_div_cancel_left₀ _ hr.1.ne'] using hω
  · rintro ⟨hx0, hx1, hxA⟩
    let ω : sphere (0 : Euclidean (d + 1)) 1 :=
      ⟨‖x‖⁻¹ • x, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hx0)]
        exact inv_mul_cancel₀ hx0.ne'⟩
    refine ⟨‖x‖, ⟨hx0, hx1⟩, (ω : Euclidean (d + 1)), ?_, ?_⟩
    · refine ⟨ω, ?_, rfl⟩
      change ‖x‖⁻¹ * x (Fin.last d) ∈ A
      simpa only [div_eq_mul_inv, mul_comm] using hxA
    · change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]

/-- Combining the final-coordinate split with polar coordinates in the first
`d` variables gives a two-dimensional meridional formula. -/
theorem lintegral_euclideanSucc_spherical {d : Nat} (hd : 0 < d)
    (G : ℝ × ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x : Euclidean (d + 1),
      G (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
        x (Fin.last d))) =
      ENNReal.ofReal (surfaceMass d) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
          ENNReal.ofReal p.1 * ENNReal.ofReal (p.1 * Real.sin p.2) ^ (d - 1) *
            G (p.1 * Real.sin p.2, p.1 * Real.cos p.2) := by
  have hmeridian : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal q.2 ^ (d - 1) * G (q.2, q.1)) :=
    (measurable_snd.ennreal_ofReal.pow_const (d - 1)).mul
      (hG.comp (measurable_snd.prodMk measurable_fst))
  have hinner : Measurable (fun z : ℝ =>
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (d - 1) * G (r, z)) := by
    change Measurable (fun z : ℝ =>
      ∫⁻ r, (fun q : ℝ × ℝ =>
        ENNReal.ofReal q.2 ^ (d - 1) * G (q.2, q.1)) (z, r) ∂
          volume.restrict (Ioi (0 : ℝ)))
    exact hmeridian.lintegral_prod_right'
  calc
    (∫⁻ x : Euclidean (d + 1),
      G (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
        x (Fin.last d))) =
        ENNReal.ofReal (surfaceMass d) *
          ∫⁻ z : ℝ, ∫⁻ r in Ioi (0 : ℝ),
            ENNReal.ofReal r ^ (d - 1) * G (r, z) :=
      lintegral_euclideanSucc_radial_last hd G hG
    _ = ENNReal.ofReal (surfaceMass d) *
        ∫⁻ q in Set.univ ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal q.2 ^ (d - 1) * G (q.2, q.1) := by
      congr 1
      symm
      change (∫⁻ q in Set.univ ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal q.2 ^ (d - 1) * G (q.2, q.1) ∂
          ((volume : Measure ℝ).prod volume)) = _
      simpa using
        (setLIntegral_prod (μ := volume) (ν := volume)
          (s := Set.univ) (t := Ioi (0 : ℝ))
          (fun q : ℝ × ℝ => ENNReal.ofReal q.2 ^ (d - 1) * G (q.2, q.1))
          hmeridian.aemeasurable.restrict)
    _ = ENNReal.ofReal (surfaceMass d) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
          ENNReal.ofReal p.1 * ENNReal.ofReal (p.1 * Real.sin p.2) ^ (d - 1) *
            G (p.1 * Real.sin p.2, p.1 * Real.cos p.2) := by
      congr 1
      rw [lintegral_meridian_halfPlane]
      simp only [polarCoord_symm_apply, mul_assoc]

/-- The cone through a measurable height slice has the exact weighted volume
needed to recover the surface-height density. -/
theorem volume_height_cone_succ {d : Nat} (hd : 2 ≤ d)
    (A : Set ℝ) (hA : MeasurableSet A) :
    ((d + 1 : Nat) : ℝ≥0∞) *
      volume {x : Euclidean (d + 1) |
        0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x (Fin.last d) / ‖x‖ ∈ A} =
      ENNReal.ofReal (surfaceMass d) *
        ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) := by
  let C : Set (Euclidean (d + 1)) := {x |
    0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x (Fin.last d) / ‖x‖ ∈ A}
  let E : Set (ℝ × ℝ) := {q |
    0 < Real.sqrt (q.1 ^ 2 + q.2 ^ 2) ∧
      Real.sqrt (q.1 ^ 2 + q.2 ^ 2) < 1 ∧
        q.2 / Real.sqrt (q.1 ^ 2 + q.2 ^ 2) ∈ A}
  let G : ℝ × ℝ → ℝ≥0∞ := E.indicator 1
  let R : ℝ → ℝ≥0∞ := fun ρ =>
    ENNReal.ofReal ρ ^ d * (Iio (1 : ℝ)).indicator 1 ρ
  let H : ℝ → ℝ≥0∞ := fun φ =>
    ENNReal.ofReal (Real.sin φ) ^ (d - 1) * A.indicator 1 (Real.cos φ)
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
  have hcoord : Measurable (fun x : Euclidean (d + 1) =>
      (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
        x (Fin.last d))) := by
    have hfirst : Measurable (fun x : Euclidean (d + 1) =>
        MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))) := by
      apply (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp
      apply measurable_pi_lambda
      intro i
      fun_prop
    exact (measurable_norm.comp hfirst).prodMk (by fun_prop)
  have hCE : C =
      (fun x : Euclidean (d + 1) =>
        (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
          x (Fin.last d))) ⁻¹' E := by
    ext x
    change (0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x (Fin.last d) / ‖x‖ ∈ A) ↔
      (0 < Real.sqrt
        (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
          (x (Fin.last d)) ^ 2) ∧
        Real.sqrt
          (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
            (x (Fin.last d)) ^ 2) < 1 ∧
          x (Fin.last d) /
              Real.sqrt
                (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
                  (x (Fin.last d)) ^ 2) ∈ A)
    rw [norm_euclideanSucc_coordinates]
  have hC : MeasurableSet C := by
    rw [hCE]
    exact hE.preimage hcoord
  have hpoint (x : Euclidean (d + 1)) :
      C.indicator 1 x =
        G (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
          x (Fin.last d)) := by
    change C.indicator 1 x = E.indicator 1
      (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
        x (Fin.last d))
    by_cases hx : x ∈ C
    · have hxE :
        (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
          x (Fin.last d)) ∈ E := by simpa [hCE] using hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxE]
      simp
    · have hxE :
        (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
          x (Fin.last d)) ∉ E := by
        intro hxE
        apply hx
        simpa [hCE] using hxE
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxE]
  have hR : Measurable R := by
    change Measurable (fun ρ : ℝ =>
      ENNReal.ofReal ρ ^ d * (Iio (1 : ℝ)).indicator 1 ρ)
    exact (measurable_id.ennreal_ofReal.pow_const d).mul
      ((measurable_indicator_const_iff 1).mpr measurableSet_Iio)
  have hAindicator : Measurable (A.indicator (fun _ : ℝ => (1 : ℝ≥0∞))) :=
    (measurable_indicator_const_iff 1).mpr hA
  have hH : Measurable H := by
    change Measurable (fun φ : ℝ =>
      ENNReal.ofReal (Real.sin φ) ^ (d - 1) * A.indicator 1 (Real.cos φ))
    exact (Real.continuous_sin.measurable.ennreal_ofReal.pow_const (d - 1)).mul
      (hAindicator.comp Real.continuous_cos.measurable)
  have hfactor (ρ φ : ℝ) (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφpi : φ < Real.pi) :
      ENNReal.ofReal ρ * ENNReal.ofReal (ρ * Real.sin φ) ^ (d - 1) *
          G (ρ * Real.sin φ, ρ * Real.cos φ) = R ρ * H φ := by
    change ENNReal.ofReal ρ * ENNReal.ofReal (ρ * Real.sin φ) ^ (d - 1) *
        E.indicator 1 (ρ * Real.sin φ, ρ * Real.cos φ) =
      (ENNReal.ofReal ρ ^ d * (Iio (1 : ℝ)).indicator 1 ρ) *
        (ENNReal.ofReal (Real.sin φ) ^ (d - 1) * A.indicator 1 (Real.cos φ))
    have hsin : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi
    have hsqrt := sqrt_spherical_meridian_norm_sq ρ φ hρ.le
    have hvertical := spherical_normalized_vertical_eq_cos ρ φ hρ
    have hmem : (ρ * Real.sin φ, ρ * Real.cos φ) ∈ E ↔
        ρ < 1 ∧ Real.cos φ ∈ A := by
      change 0 < Real.sqrt ((ρ * Real.sin φ) ^ 2 + (ρ * Real.cos φ) ^ 2) ∧
        Real.sqrt ((ρ * Real.sin φ) ^ 2 + (ρ * Real.cos φ) ^ 2) < 1 ∧
          (ρ * Real.cos φ) /
            Real.sqrt ((ρ * Real.sin φ) ^ 2 + (ρ * Real.cos φ) ^ 2) ∈ A ↔
        ρ < 1 ∧ Real.cos φ ∈ A
      rw [hvertical, hsqrt]
      simp [hρ]
    have hpow : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
    have hbase :
        ENNReal.ofReal ρ * ENNReal.ofReal (ρ * Real.sin φ) ^ (d - 1) =
          ENNReal.ofReal ρ ^ d * ENNReal.ofReal (Real.sin φ) ^ (d - 1) := by
      rw [ENNReal.ofReal_mul hρ.le, mul_pow]
      calc
        ENNReal.ofReal ρ *
            (ENNReal.ofReal ρ ^ (d - 1) * ENNReal.ofReal (Real.sin φ) ^ (d - 1)) =
            (ENNReal.ofReal ρ ^ (d - 1) * ENNReal.ofReal ρ) *
              ENNReal.ofReal (Real.sin φ) ^ (d - 1) := by ring
        _ = ENNReal.ofReal ρ ^ (d - 1 + 1) *
              ENNReal.ofReal (Real.sin φ) ^ (d - 1) := by rw [pow_succ]
        _ = ENNReal.ofReal ρ ^ d * ENNReal.ofReal (Real.sin φ) ^ (d - 1) := by
          rw [hpow]
    by_cases hρone : ρ < 1 <;> by_cases hAcos : Real.cos φ ∈ A
    · have hE' : (ρ * Real.sin φ, ρ * Real.cos φ) ∈ E :=
        hmem.mpr ⟨hρone, hAcos⟩
      have hI : ρ ∈ Iio (1 : ℝ) := hρone
      rw [Set.indicator_of_mem hE']
      simp only [Pi.one_apply]
      rw [Set.indicator_of_mem hI, Set.indicator_of_mem hAcos]
      simp only [Pi.one_apply, mul_one]
      rw [hbase]
    · have hE' : (ρ * Real.sin φ, ρ * Real.cos φ) ∉ E := by
        exact fun h => hAcos (hmem.mp h).2
      have hI : ρ ∈ Iio (1 : ℝ) := hρone
      rw [Set.indicator_of_notMem hE', Set.indicator_of_mem hI,
        Set.indicator_of_notMem hAcos]
      simp
    · have hE' : (ρ * Real.sin φ, ρ * Real.cos φ) ∉ E := by
        exact fun h => hρone (hmem.mp h).1
      have hI : ρ ∉ Iio (1 : ℝ) := hρone
      rw [Set.indicator_of_notMem hE', Set.indicator_of_notMem hI,
        Set.indicator_of_mem hAcos]
      simp
    · have hE' : (ρ * Real.sin φ, ρ * Real.cos φ) ∉ E := by
        exact fun h => hρone (hmem.mp h).1
      have hI : ρ ∉ Iio (1 : ℝ) := hρone
      rw [Set.indicator_of_notMem hE', Set.indicator_of_notMem hI,
        Set.indicator_of_notMem hAcos]
      simp
  have hRadial :
      (∫⁻ ρ in Ioi (0 : ℝ), R ρ) =
        ENNReal.ofReal (1 / (d + 1 : ℝ)) := by
    let S : Set (Ioi (0 : ℝ)) := Iio ⟨1, by norm_num⟩
    let F : ℝ → ℝ≥0∞ := (Iio (1 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞))
    have hF : Measurable F := by
      change Measurable ((Iio (1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ≥0∞)))
      exact (measurable_indicator_const_iff 1).mpr measurableSet_Iio
    have hS : MeasurableSet S := by
      dsimp [S]
      exact measurableSet_Iio
    calc
      (∫⁻ ρ in Ioi (0 : ℝ), R ρ) =
          ∫⁻ ρ : Ioi (0 : ℝ), F ρ ∂Measure.volumeIoiPow d := by
        symm
        calc
          (∫⁻ ρ : Ioi (0 : ℝ), F ρ ∂Measure.volumeIoiPow d) =
              ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ ^ d * F ρ :=
            lintegral_volumeIoiPow d F hF
          _ = ∫⁻ ρ in Ioi (0 : ℝ), R ρ := by
            apply setLIntegral_congr_fun measurableSet_Ioi
            intro ρ hρ
            change ENNReal.ofReal ρ ^ d *
                (Iio (1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) ρ =
              R ρ
            rfl
      _ = ∫⁻ ρ in S, (1 : ℝ≥0∞) ∂Measure.volumeIoiPow d := by
        calc
          (∫⁻ ρ : Ioi (0 : ℝ), F ρ ∂Measure.volumeIoiPow d) =
              ∫⁻ ρ : Ioi (0 : ℝ), S.indicator (fun _ => (1 : ℝ≥0∞)) ρ ∂
                Measure.volumeIoiPow d := by
            apply lintegral_congr
            intro ρ
            change (Iio (1 : ℝ)).indicator (fun x => 1) ρ =
              S.indicator (fun x => 1) ρ
            by_cases hρ : ρ.1 < 1
            · have hρS : ρ ∈ S := by
                change ρ < (⟨1, by norm_num⟩ : Ioi (0 : ℝ))
                exact hρ
              have hρI : (ρ : ℝ) ∈ Iio (1 : ℝ) := hρ
              rw [Set.indicator_of_mem hρI, Set.indicator_of_mem hρS]
            · have hρS : ρ ∉ S := by
                intro hρS
                apply hρ
                change ρ.1 < 1 at hρS
                exact hρS
              have hρI : (ρ : ℝ) ∉ Iio (1 : ℝ) := hρ
              rw [Set.indicator_of_notMem hρI, Set.indicator_of_notMem hρS]
          _ = ∫⁻ ρ in S, (1 : ℝ≥0∞) ∂Measure.volumeIoiPow d :=
            lintegral_indicator hS _
      _ = Measure.volumeIoiPow d S := by simp
      _ = ENNReal.ofReal (1 / (d + 1 : ℝ)) := by
        simpa [S] using
          (Measure.volumeIoiPow_apply_Iio d (⟨1, by norm_num⟩ : Ioi (0 : ℝ)))
  have hAngular :
      (∫⁻ φ in Ioo (0 : ℝ) Real.pi, H φ) =
        ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) := by
    let u : ℝ → ℝ≥0∞ := fun t =>
      ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) * A.indicator 1 t
    have hweight :
        (∫⁻ t in Ioo (-1 : ℝ) 1, u t) =
          ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) := by
      calc
        (∫⁻ t in Ioo (-1 : ℝ) 1, u t) =
            ∫⁻ t, A.indicator
              (fun t => ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)) t ∂
                volume.restrict (Ioo (-1 : ℝ) 1) := by
          apply lintegral_congr
          intro t
          by_cases ht : t ∈ A
          · dsimp [u]
            rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
            simp
          · dsimp [u]
            rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
            simp
        _ = ∫⁻ t in A,
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) ∂
              volume.restrict (Ioo (-1 : ℝ) 1) :=
          lintegral_indicator hA _
        _ = ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) := by
          rw [← Measure.restrict_restrict hA]
    calc
      (∫⁻ φ in Ioo (0 : ℝ) Real.pi, H φ) =
          ∫⁻ φ in Ioo (0 : ℝ) Real.pi,
            ENNReal.ofReal (Real.sin φ) * u (Real.cos φ) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro φ hφ
        have hsin : Real.sin φ = Real.sqrt (1 - Real.cos φ ^ 2) :=
          Real.sin_eq_sqrt_one_sub_cos_sq hφ.1.le hφ.2.le
        have hpow : d - 1 = (d - 2) + 1 := by omega
        change ENNReal.ofReal (Real.sin φ) ^ (d - 1) * A.indicator 1 (Real.cos φ) =
          ENNReal.ofReal (Real.sin φ) *
            (ENNReal.ofReal (Real.sqrt (1 - Real.cos φ ^ 2)) ^ (d - 2) *
              A.indicator 1 (Real.cos φ))
        rw [hpow, pow_succ, hsin]
        ring
      _ = ∫⁻ t in Ioo (-1 : ℝ) 1, u t :=
        lintegral_comp_cos_mul_sin u
      _ = ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) := hweight
  have hProduct :
      (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi, R p.1 * H p.2) =
        ENNReal.ofReal (1 / (d + 1 : ℝ)) *
          (∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)) := by
    calc
      (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi, R p.1 * H p.2) =
          ∫⁻ r in Ioi (0 : ℝ), ∫⁻ φ in Ioo (0 : ℝ) Real.pi, R r * H φ := by
        apply setLIntegral_prod
        exact (hR.comp measurable_fst).mul (hH.comp measurable_snd) |>.aemeasurable.restrict
      _ = ∫⁻ r in Ioi (0 : ℝ), R r *
          (∫⁻ φ in Ioo (0 : ℝ) Real.pi, H φ) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change (∫⁻ φ in Ioo (0 : ℝ) Real.pi, R r * H φ) =
          R r * (∫⁻ φ in Ioo (0 : ℝ) Real.pi, H φ)
        exact lintegral_const_mul (μ := volume.restrict (Ioo (0 : ℝ) Real.pi)) (R r) hH
      _ = (∫⁻ r in Ioi (0 : ℝ), R r) *
          (∫⁻ φ in Ioo (0 : ℝ) Real.pi, H φ) := by
        exact lintegral_mul_const _ hR
      _ = ENNReal.ofReal (1 / (d + 1 : ℝ)) *
          (∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)) := by
        rw [hRadial, hAngular]
  have hVol : volume C =
      ENNReal.ofReal (surfaceMass d) *
        (ENNReal.ofReal (1 / (d + 1 : ℝ)) *
          ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)) := by
    calc
      volume C = ∫⁻ x : Euclidean (d + 1), C.indicator 1 x :=
        (lintegral_indicator_one hC).symm
      _ = ∫⁻ x : Euclidean (d + 1),
          G (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖,
            x (Fin.last d)) := by
        apply lintegral_congr
        intro x
        exact hpoint x
      _ = ENNReal.ofReal (surfaceMass d) *
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
            ENNReal.ofReal p.1 * ENNReal.ofReal (p.1 * Real.sin p.2) ^ (d - 1) *
              G (p.1 * Real.sin p.2, p.1 * Real.cos p.2) :=
        lintegral_euclideanSucc_spherical (by omega) G hG
      _ = ENNReal.ofReal (surfaceMass d) *
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi, R p.1 * H p.2 := by
        congr 1
        apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp
        exact hfactor p.1 p.2 hp.1 hp.2.1 hp.2.2
      _ = ENNReal.ofReal (surfaceMass d) *
          (ENNReal.ofReal (1 / (d + 1 : ℝ)) *
            ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
              ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)) := by
        rw [hProduct]
  have hscalar :
      ((d + 1 : Nat) : ℝ≥0∞) * ENNReal.ofReal (1 / (d + 1 : ℝ)) = 1 := by
    have hpos : 0 < (d + 1 : ℝ) := by positivity
    rw [← ENNReal.ofReal_natCast (d + 1),
      ← ENNReal.ofReal_mul (p := ((d + 1 : Nat) : ℝ))
        (q := 1 / (d + 1 : ℝ)) (by positivity)]
    have hcast : ((d + 1 : Nat) : ℝ) = (d : ℝ) + 1 := by norm_num
    rw [hcast, div_eq_mul_inv, one_mul, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one]
  change ((d + 1 : Nat) : ℝ≥0∞) * volume C = _
  rw [hVol]
  calc
    ((d + 1 : Nat) : ℝ≥0∞) *
        (ENNReal.ofReal (surfaceMass d) *
          (ENNReal.ofReal (1 / (d + 1 : ℝ)) *
            ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
              ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))) =
        ENNReal.ofReal (surfaceMass d) *
          ((((d + 1 : Nat) : ℝ≥0∞) * ENNReal.ofReal (1 / (d + 1 : ℝ))) *
            ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
              ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)) := by
          ring
    _ = ENNReal.ofReal (surfaceMass d) *
        (1 * ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)) := by
          rw [hscalar]
    _ = ENNReal.ofReal (surfaceMass d) *
        ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) := by simp

/-- Projecting the concrete surface measure on `S^d` to its final coordinate
has the standard weighted height density, proved directly from the cone
definition of `Measure.toSphere`. -/
theorem map_unitSurfaceMeasure_succ_height {d : Nat} (hd : 2 ≤ d) :
    Measure.map
        (fun ω : sphere (0 : Euclidean (d + 1)) 1 =>
          (ω : Euclidean (d + 1)) (Fin.last d))
        (unitSurfaceMeasure (d + 1)) =
      ENNReal.ofReal (surfaceMass d) •
        (volume.withDensity (fun t : ℝ =>
          ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
          (Ioo (-1 : ℝ) 1) := by
  have hheight : Measurable
      (fun ω : sphere (0 : Euclidean (d + 1)) 1 =>
        (ω : Euclidean (d + 1)) (Fin.last d)) := by
    fun_prop
  apply Measure.ext
  intro A hA
  have hS : MeasurableSet
      {ω : sphere (0 : Euclidean (d + 1)) 1 |
        (ω : Euclidean (d + 1)) (Fin.last d) ∈ A} :=
    hA.preimage hheight
  have hweighted :
      (∫⁻ t in Ioo (-1 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) * A.indicator 1 t) =
        ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) := by
    calc
      (∫⁻ t in Ioo (-1 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) * A.indicator 1 t) =
          ∫⁻ t, A.indicator
            (fun t => ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)) t ∂
              volume.restrict (Ioo (-1 : ℝ) 1) := by
        apply lintegral_congr
        intro t
        by_cases ht : t ∈ A
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          simp
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
          simp
      _ = ∫⁻ t in A,
          ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) ∂
            volume.restrict (Ioo (-1 : ℝ) 1) :=
        lintegral_indicator hA _
      _ = ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2) := by
        rw [← Measure.restrict_restrict hA]
  rw [Measure.map_apply hheight hA, Measure.smul_apply,
    Measure.restrict_apply hA,
    withDensity_apply _ (hA.inter measurableSet_Ioo)]
  change unitSurfaceMeasure (d + 1)
      {ω : sphere (0 : Euclidean (d + 1)) 1 |
        (ω : Euclidean (d + 1)) (Fin.last d) ∈ A} =
    ENNReal.ofReal (surfaceMass d) *
      ∫⁻ t in A ∩ Ioo (-1 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)
  rw [unitSurfaceMeasure, Measure.toSphere_apply' volume hS,
    height_cone_succ_eq]
  simpa only [finrank_euclideanSpace_fin] using
    (volume_height_cone_succ hd A hA)

/-- Integrating a continuous function of the final coordinate against the
concrete sphere measure is exactly its weighted one-dimensional height
integral. -/
theorem integral_comp_last_unitSurfaceMeasure_succ {d : Nat} (hd : 2 ≤ d)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ ω : sphere (0 : Euclidean (d + 1)) 1,
      F ((ω : Euclidean (d + 1)) (Fin.last d)) ∂unitSurfaceMeasure (d + 1)) =
      (surfaceMass d : ℂ) *
        ∫ t, F t ∂
          (volume.withDensity (fun t : ℝ =>
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
            (Ioo (-1 : ℝ) 1) := by
  let height : sphere (0 : Euclidean (d + 1)) 1 → ℝ :=
    fun ω => (ω : Euclidean (d + 1)) (Fin.last d)
  let μ : Measure ℝ :=
    (volume.withDensity (fun t : ℝ =>
      ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
      (Ioo (-1 : ℝ) 1)
  have hheight : Measurable height := by
    dsimp [height]
    fun_prop
  have hmap : Measure.map height (unitSurfaceMeasure (d + 1)) =
      ENNReal.ofReal (surfaceMass d) • μ := by
    dsimp [height, μ]
    exact map_unitSurfaceMeasure_succ_height hd
  have hmass_nonneg : 0 ≤ surfaceMass d := measureReal_nonneg
  calc
    (∫ ω : sphere (0 : Euclidean (d + 1)) 1,
      F ((ω : Euclidean (d + 1)) (Fin.last d)) ∂unitSurfaceMeasure (d + 1)) =
        ∫ t, F t ∂Measure.map height (unitSurfaceMeasure (d + 1)) := by
      exact (MeasureTheory.integral_map hheight.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ t, F t ∂(ENNReal.ofReal (surfaceMass d) • μ) := by rw [hmap]
    _ = (surfaceMass d : ℂ) * ∫ t, F t ∂μ := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hmass_nonneg]
      simp only [Complex.real_smul]
    _ = (surfaceMass d : ℂ) *
        ∫ t, F t ∂
          (volume.withDensity (fun t : ℝ =>
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
            (Ioo (-1 : ℝ) 1) := rfl

/-- The final-coordinate unit vector in `Euclidean (d + 1)` has norm one. -/
theorem norm_euclideanSucc_last (d : Nat) :
    ‖MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)
      (fun i => if i = Fin.last d then 1 else 0)‖ = 1 := by
  have hsquare :
      ‖MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)
        (fun i => if i = Fin.last d then 1 else 0)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [MeasurableEquiv.coe_toLp, PiLp.toLp_apply]
    simp
  nlinarith [norm_nonneg
    (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)
      (fun i => if i = Fin.last d then 1 else 0))]

/-- Taking the real inner product with the final-coordinate unit vector
selects that coordinate. -/
theorem inner_euclideanSucc_last (d : Nat) (x : Euclidean (d + 1)) :
    inner ℝ x (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)
      (fun i => if i = Fin.last d then 1 else 0)) = x (Fin.last d) := by
  rw [PiLp.inner_apply]
  simp only [MeasurableEquiv.coe_toLp, PiLp.toLp_apply]
  simp

/-- Along the final coordinate axis, the concrete surface Fourier transform
is precisely the weighted one-dimensional height oscillatory integral. -/
theorem surfaceFourier_axis_last {d : Nat} (hd : 2 ≤ d) (a : ℝ) :
    surfaceFourier (d + 1)
      (a • MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)
        (fun i => if i = Fin.last d then 1 else 0)) =
      (surfaceMass d : ℂ) *
        ∫ t, Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I) ∂
          (volume.withDensity (fun t : ℝ =>
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
            (Ioo (-1 : ℝ) 1) := by
  let e : Euclidean (d + 1) :=
    MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)
      (fun i => if i = Fin.last d then 1 else 0)
  let F : ℝ → ℂ := fun t =>
    Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hinter (x : Euclidean (d + 1)) : inner ℝ x e = x (Fin.last d) := by
    dsimp [e]
    exact inner_euclideanSucc_last d x
  calc
    surfaceFourier (d + 1) (a • e) =
        ∫ ω : sphere (0 : Euclidean (d + 1)) 1,
          F ((ω : Euclidean (d + 1)) (Fin.last d)) ∂unitSurfaceMeasure (d + 1) := by
      unfold surfaceFourier
      apply integral_congr_ae
      filter_upwards with ω
      dsimp [F]
      unfold surfacePhase
      rw [inner_smul_right, hinter]
      push_cast
      ring_nf
    _ = (surfaceMass d : ℂ) *
        ∫ t, F t ∂
          (volume.withDensity (fun t : ℝ =>
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
            (Ioo (-1 : ℝ) 1) :=
      integral_comp_last_unitSurfaceMeasure_succ hd F hF
    _ = (surfaceMass d : ℂ) *
        ∫ t, Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I) ∂
          (volume.withDensity (fun t : ℝ =>
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
            (Ioo (-1 : ℝ) 1) := rfl

/-- In every ambient dimension at least three, radial symmetry and the
height-density computation give a literal one-dimensional formula for the
surface Fourier transform. -/
theorem surfaceFourier_succ_height_integral {d : Nat} (hd : 2 ≤ d)
    (ξ : Euclidean (d + 1)) :
    surfaceFourier (d + 1) ξ =
      (surfaceMass d : ℂ) *
        ∫ t, Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I) ∂
          (volume.withDensity (fun t : ℝ =>
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
            (Ioo (-1 : ℝ) 1) := by
  let e : Euclidean (d + 1) :=
    MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)
      (fun i => if i = Fin.last d then 1 else 0)
  have he : ‖e‖ = 1 := by
    dsimp [e]
    exact norm_euclideanSucc_last d
  calc
    surfaceFourier (d + 1) ξ = surfaceFourier (d + 1) (‖ξ‖ • e) :=
      surfaceFourier_eq_norm_smul_unit (d + 1) ξ e he
    _ = (surfaceMass d : ℂ) *
        ∫ t, Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I) ∂
          (volume.withDensity (fun t : ℝ =>
            ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
            (Ioo (-1 : ℝ) 1) :=
      surfaceFourier_axis_last hd ‖ξ‖

/-- In every ambient dimension at least three, the Fourier transform of the
concrete surface measure tends to zero at infinity. This is the qualitative
decay input obtained by applying the Riemann--Lebesgue lemma to the proved
height density. -/
theorem tendsto_surfaceFourier_succ_cocompact {d : Nat} (hd : 2 ≤ d) :
    Tendsto (surfaceFourier (d + 1)) (cocompact (Euclidean (d + 1))) (𝓝 0) := by
  let w : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)
  let s : Set ℝ := Ioo (-1 : ℝ) 1
  let f : ℝ → ℂ := s.indicator (fun t => ((w t).toReal : ℂ))
  let Q : ℝ → ℂ := fun a =>
    ∫ t, Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I) ∂
      (volume.withDensity w).restrict s
  have hrewrite (a : ℝ) :
      Q a = ∫ t : ℝ, Real.fourierChar (-(t * a)) • f t := by
    have hw : Measurable w := by
      dsimp [w]
      fun_prop
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_Ioo
    have hw_top : ∀ᵐ t ∂volume.restrict s, w t < ∞ := by
      filter_upwards with t
      exact lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    dsimp only [Q, f]
    rw [restrict_withDensity hs]
    rw [integral_withDensity_eq_integral_toReal_smul hw hw_top]
    rw [← MeasureTheory.integral_indicator hs]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      have hphase :
          Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I) =
            Complex.exp (((2 * Real.pi * (-(t * a)) : ℝ) : ℂ) * Complex.I) := by
        congr 1
        push_cast
        ring
      simp only [Circle.smul_def, Real.fourierChar_apply]
      rw [hphase]
      change ((w t).toReal : ℂ) * _ = _ * ((w t).toReal : ℂ)
      ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      simp
  have hosc : Tendsto Q (cocompact ℝ) (𝓝 0) := by
    refine (Real.tendsto_integral_exp_smul_cocompact f).congr' ?_
    filter_upwards with a
    exact (hrewrite a).symm
  have hradial : Tendsto (fun ξ : Euclidean (d + 1) => Q ‖ξ‖)
      (cocompact (Euclidean (d + 1))) (𝓝 0) := by
    have hosc_atTop : Tendsto Q atTop (𝓝 0) :=
      hosc.mono_left atTop_le_cocompact
    change Tendsto (Q ∘ norm) (cocompact (Euclidean (d + 1))) (𝓝 0)
    exact hosc_atTop.comp
      (tendsto_norm_cocompact_atTop (E := Euclidean (d + 1)))
  have hmul : Tendsto (fun ξ : Euclidean (d + 1) =>
      (surfaceMass d : ℂ) * Q ‖ξ‖) (cocompact (Euclidean (d + 1))) (𝓝 0) := by
    simpa using hradial.const_mul (surfaceMass d : ℂ)
  refine hmul.congr' ?_
  filter_upwards with ξ
  exact (surfaceFourier_succ_height_integral hd ξ).symm

/-- One literal integration by parts relates consecutive polynomial height
oscillatory integrals.  For the height density of the odd-dimensional sphere,
the parameter `d` is its polynomial exponent.  This is the recurrence that
produces one inverse-frequency factor at each dimension-raising step. -/
theorem intervalIntegral_height_polynomial_succ_recurrence
    (d : Nat) (l : ℝ) (hl : l ≠ 0) :
    (∫ t in (-1 : ℝ)..1,
      (((1 - t ^ 2) ^ (d + 1) : ℝ) : ℂ) *
        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)) =
      (((2 : ℂ) * ((d + 1 : ℕ) : ℂ)) *
          ((((-l : ℝ) : ℂ) * Complex.I)⁻¹)) *
        ∫ t in (-1 : ℝ)..1,
          ((t * (1 - t ^ 2) ^ d : ℝ) : ℂ) *
            Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) := by
  let E : ℝ → ℂ := fun t =>
    Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)
  let q : ℂ := ((-l : ℝ) : ℂ) * Complex.I
  let s : ℂ := q⁻¹
  let w : ℝ → ℂ := fun t => (((1 - t ^ 2) ^ (d + 1) : ℝ) : ℂ)
  let w' : ℝ → ℂ := fun t =>
    ((((d + 1 : ℕ) : ℝ) * (1 - t ^ 2) ^ d * (-2 * t) : ℝ) : ℂ)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hl)) Complex.I_ne_zero
  have hsq : s * q = 1 := by
    dsimp [s]
    exact inv_mul_cancel₀ hq
  have hE : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt E (E t * q) t := by
    intro t _
    dsimp [E, q]
    have harg : HasDerivAt
        (fun x : ℝ => ((-l * x : ℝ) : ℂ) * Complex.I)
        (((-l : ℝ) : ℂ) * Complex.I) t := by
      have hreal : HasDerivAt (fun x : ℝ => -l * x) (-l) t := by
        simpa using (hasDerivAt_id t).const_mul (-l)
      simpa only [Complex.real_smul] using hreal.smul_const Complex.I
    simpa [mul_assoc] using harg.cexp
  have hw : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt w (w' t) t := by
    intro t _
    dsimp [w, w']
    have hbase : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * t) t := by
      have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
        have h := (hasDerivAt_pow 2 t : HasDerivAt (fun x : ℝ => x ^ 2) _ t)
        simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using h
      simpa [neg_mul] using hpow.const_sub (1 : ℝ)
    have hp := hbase.fun_pow (d + 1)
    have hp' : HasDerivAt (fun x : ℝ => (1 - x ^ 2) ^ (d + 1))
        (((d + 1 : ℕ) : ℝ) * (1 - t ^ 2) ^ d * (-2 * t)) t := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hp
    exact hp'.ofReal_comp
  have hEcont : Continuous E := by
    dsimp [E]
    fun_prop
  have hw'cont : Continuous w' := by
    dsimp [w']
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := w) (u' := w') (v := fun t => s * E t)
    (v' := fun t => E t)
    hw
    (by
      intro t ht
      have h := (hE t ht).const_mul s
      have hs : s * (E t * q) = E t := by
        calc
          s * (E t * q) = (s * q) * E t := by ring
          _ = E t := by rw [hsq, one_mul]
      simpa only [hs] using h)
    (hw'cont.continuousOn.intervalIntegrable)
    (hEcont.continuousOn.intervalIntegrable)
  have hparts' :
      (∫ t in (-1 : ℝ)..1, w t * E t) =
        -∫ t in (-1 : ℝ)..1, w' t * (s * E t) := by
    rw [hparts]
    simp [w]
  have hrewrite :
      -∫ t in (-1 : ℝ)..1, w' t * (s * E t) =
        (((2 : ℂ) * ((d + 1 : ℕ) : ℂ)) * s) *
          ∫ t in (-1 : ℝ)..1,
            ((t * (1 - t ^ 2) ^ d : ℝ) : ℂ) * E t := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [w']
    push_cast
    ring
  change (∫ t in (-1 : ℝ)..1, w t * E t) = _
  rw [hparts', hrewrite]

/-- In every odd ambient dimension, the literal height formula reduces the
surface Fourier transform to the corresponding polynomial oscillatory
integral.  The ambient dimension is `(2 * n + 4) + 1`, written in successor
form to keep the geometric height theorem's indexing literal. -/
theorem surfaceFourier_odd_succ_height_polynomial
    (n : Nat) (ξ : Euclidean ((2 * n + 4) + 1)) :
    surfaceFourier ((2 * n + 4) + 1) ξ =
      (surfaceMass (2 * n + 4) : ℂ) *
        ∫ t in (-1 : ℝ)..1,
          (((1 - t ^ 2) ^ (n + 1) : ℝ) : ℂ) *
            Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I) := by
  let w : ℝ → ENNReal := fun t =>
    ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ ((2 * n + 4) - 2)
  let g : ℝ → ℂ := fun t =>
    Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I)
  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hw_top : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1), w t < ⊤ :=
    Filter.Eventually.of_forall fun _ => by
      dsimp [w]
      exact lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hn : 2 ≤ 2 * n + 4 := by omega
  calc
    surfaceFourier ((2 * n + 4) + 1) ξ =
        (surfaceMass (2 * n + 4) : ℂ) *
          ∫ t, g t ∂(volume.withDensity w).restrict (Set.Ioo (-1 : ℝ) 1) := by
      simpa only [w, g] using
        (surfaceFourier_succ_height_integral (d := 2 * n + 4) hn ξ)
    _ = (surfaceMass (2 * n + 4) : ℂ) *
        ∫ t in Set.Ioo (-1 : ℝ) 1, (w t).toReal • g t := by
      congr 1
      exact setIntegral_withDensity_eq_setIntegral_toReal_smul hw hw_top g measurableSet_Ioo
    _ = (surfaceMass (2 * n + 4) : ℂ) *
        ∫ t in (-1 : ℝ)..1,
          (((1 - t ^ 2) ^ (n + 1) : ℝ) : ℂ) *
            Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I) := by
      congr 1
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have habs : |t| < 1 := (abs_lt).mpr ⟨by linarith [ht.1], ht.2⟩
      have hsq : t ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one t).mpr habs
      have hnonneg : 0 ≤ 1 - t ^ 2 := le_of_lt (sub_pos.mpr hsq)
      have hexp : 2 * n + 4 - 2 = 2 * (n + 1) := by omega
      have hsqrt :
          (Real.sqrt (1 - t ^ 2)) ^ ((2 * n + 4) - 2) =
            (1 - t ^ 2) ^ (n + 1) := by
        rw [hexp, pow_mul, Real.sq_sqrt hnonneg]
      dsimp [w, g]
      rw [ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (Real.sqrt_nonneg _), hsqrt]

/-- Combining the polynomial height formula with the proved integration by
parts identity gives the literal odd-dimensional surface-Fourier recurrence.
The right-hand integral is the one derivative-weighted height integral needed
for the next sharp-decay induction step. -/
theorem surfaceFourier_odd_succ_height_recurrence
    (n : Nat) (ξ : Euclidean ((2 * n + 4) + 1)) (hξ : ξ ≠ 0) :
    surfaceFourier ((2 * n + 4) + 1) ξ =
      (surfaceMass (2 * n + 4) : ℂ) *
        ((((2 : ℂ) * ((n + 1 : ℕ) : ℂ)) *
            (((-(2 * Real.pi * ‖ξ‖) : ℝ) : ℂ) * Complex.I)⁻¹) *
          (∫ t in (-1 : ℝ)..1,
            ((t * (1 - t ^ 2) ^ n : ℝ) : ℂ) *
              Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I))) := by
  have hnorm : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hl : 2 * Real.pi * ‖ξ‖ ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hnorm
  have hphase (t : ℝ) :
      Complex.exp (((-(2 * Real.pi * ‖ξ‖) * t : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  have hrec := intervalIntegral_height_polynomial_succ_recurrence n
    (2 * Real.pi * ‖ξ‖) hl
  have hrec' :
      (∫ t in (-1 : ℝ)..1,
        (((1 - t ^ 2) ^ (n + 1) : ℝ) : ℂ) *
          Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I)) =
        (((2 : ℂ) * ((n + 1 : ℕ) : ℂ)) *
          ((((-(2 * Real.pi * ‖ξ‖) : ℝ) : ℂ) * Complex.I)⁻¹)) *
          ∫ t in (-1 : ℝ)..1,
            ((t * (1 - t ^ 2) ^ n : ℝ) : ℂ) *
              Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I) := by
    simpa only [hphase] using hrec
  calc
    surfaceFourier ((2 * n + 4) + 1) ξ =
        (surfaceMass (2 * n + 4) : ℂ) *
          ∫ t in (-1 : ℝ)..1,
            (((1 - t ^ 2) ^ (n + 1) : ℝ) : ℂ) *
              Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I) :=
      surfaceFourier_odd_succ_height_polynomial n ξ
    _ = (surfaceMass (2 * n + 4) : ℂ) *
        ((((2 : ℂ) * ((n + 1 : ℕ) : ℂ)) *
            (((-(2 * Real.pi * ‖ξ‖) : ℝ) : ℂ) * Complex.I)⁻¹) *
          (∫ t in (-1 : ℝ)..1,
            ((t * (1 - t ^ 2) ^ n : ℝ) : ℂ) *
              Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I))) := by
      rw [hrec']

/-! ### The all-parity two-step height recurrence -/

/-- The literal height integral becomes a smooth meridian integral after the
substitution `t = sin θ`.  Unlike the endpoint height density itself, the
meridian amplitude is smooth for every natural dimension parameter. -/
theorem intervalIntegral_height_power_eq_meridian (d : Nat) (hd : 2 ≤ d) (l : ℝ) :
    (∫ t in (-1 : ℝ)..1,
      ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)) =
      ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
          Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I) := by
  let g : ℝ → ℂ := fun t =>
    ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
      Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hsubst := intervalIntegral.integral_deriv_smul_comp
    (a := (-(Real.pi / 2) : ℝ)) (b := (Real.pi / 2 : ℝ))
    (f := Real.sin) (f' := Real.cos) (g := g)
    (fun x _ => Real.hasDerivAt_sin x) (by fun_prop) hg
  change (∫ t in (-1 : ℝ)..1, g t) = _
  rw [← Real.sin_pi_div_two, ← Real.sin_neg]
  rw [← hsubst]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hab : -(Real.pi / 2 : ℝ) ≤ Real.pi / 2 :=
    neg_le_self (le_of_lt (div_pos Real.pi_pos (by norm_num)))
  have hθ' : θ ∈ Set.Icc (-(Real.pi / 2) : ℝ) (Real.pi / 2) := by
    simpa [Set.uIcc_of_le hab] using hθ
  dsimp only [Function.comp_apply, g]
  rw [← Real.cos_eq_sqrt_one_sub_sin_sq hθ'.1 hθ'.2]
  push_cast
  rw [Complex.real_smul]
  rw [← Complex.ofReal_cos]
  have hsub : d - 1 = (d - 2) + 1 := by omega
  rw [hsub, pow_succ]
  ring

private theorem hasDerivAt_meridian_height_oscillatoryIntegral (d : Nat) (l : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
            Complex.exp (((-u * Real.sin θ : ℝ) : ℂ) * Complex.I))
      (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        ((-Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
          Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I) * Complex.I) l := by
  let a : ℝ := -(Real.pi / 2)
  let b : ℝ := Real.pi / 2
  let F : ℝ → ℝ → ℂ := fun u θ =>
    ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
      Complex.exp (((-u * Real.sin θ : ℝ) : ℂ) * Complex.I)
  let F' : ℝ → ℝ → ℂ := fun u θ =>
    ((-Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
      Complex.exp (((-u * Real.sin θ : ℝ) : ℂ) * Complex.I) * Complex.I
  have hab : a ≤ b := by
    dsimp [a, b]
    exact neg_le_self (le_of_lt (div_pos Real.pi_pos (by norm_num)))
  change HasDerivAt
    (fun u : ℝ => ∫ θ in a..b, F u θ)
    (∫ θ in a..b, F' l θ) l
  simp_rw [intervalIntegral.integral_of_le hab]
  change HasDerivAt
    (fun u : ℝ => ∫ θ, F u θ ∂volume.restrict (Set.Ioc a b))
    (∫ θ, F' l θ ∂volume.restrict (Set.Ioc a b)) l
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc a b)) (s := Set.univ) (x₀ := l)
    (bound := fun _ : ℝ => (1 : ℝ))
    (F := F) (F' := F') Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact h.2
  · filter_upwards [] with u
    exact (by
      dsimp [F]
      fun_prop : Continuous (fun θ : ℝ => F u θ)).aestronglyMeasurable
  · refine Integrable.of_bound ?_ 1 ?_
    · exact (by
        dsimp [F]
        fun_prop : Continuous (fun θ : ℝ => F l θ)).aestronglyMeasurable
    · filter_upwards with θ
      dsimp [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
  · exact (by
      dsimp [F']
      fun_prop : Continuous (fun θ : ℝ => F' l θ)).aestronglyMeasurable
  · filter_upwards with θ
    intro u hu
    dsimp [F']
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_neg, abs_pow, Complex.norm_exp_ofReal_mul_I, Complex.norm_I,
      mul_one]
    ring_nf
    apply mul_le_one₀
    · exact Real.abs_sin_le_one _
    · exact pow_nonneg (abs_nonneg _) _
    · exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
  · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
  · filter_upwards with θ
    intro u hu
    dsimp [F, F']
    have harg : HasDerivAt
        (fun v : ℝ => ((-v * Real.sin θ : ℝ) : ℂ) * Complex.I)
        (((-Real.sin θ : ℝ) : ℂ) * Complex.I) u := by
      have hreal : HasDerivAt (fun v : ℝ => -v * Real.sin θ) (-Real.sin θ) u := by
        simpa [mul_comm] using (hasDerivAt_id u).mul_const (-Real.sin θ)
      simpa only [Complex.real_smul] using hreal.smul_const Complex.I
    have hexp := harg.cexp
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      hexp.const_mul ((Real.cos θ ^ (d - 1) : ℝ) : ℂ)

private theorem intervalIntegral_meridian_height_succ_two_relation
    (d : Nat) (hd : 0 < d) (l : ℝ) (hl : l ≠ 0) :
    (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
      ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) *
        Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I)) =
      (((d : ℕ) : ℂ) * ((((-l : ℝ) : ℂ) * Complex.I)⁻¹)) *
        ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          ((Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
            Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I) := by
  let E : ℝ → ℂ := fun θ =>
    Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I)
  let q : ℂ := ((-l : ℝ) : ℂ) * Complex.I
  let s : ℂ := q⁻¹
  let w : ℝ → ℂ := fun θ => ((Real.cos θ ^ d : ℝ) : ℂ)
  let w' : ℝ → ℂ := fun θ =>
    ((-(d : ℝ) * Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hl)) Complex.I_ne_zero
  have hsq : s * q = 1 := by
    dsimp [s]
    exact inv_mul_cancel₀ hq
  have hE : ∀ θ ∈ Set.uIcc (-(Real.pi / 2) : ℝ) (Real.pi / 2),
      HasDerivAt E (E θ * (q * (Real.cos θ : ℂ))) θ := by
    intro θ _
    dsimp [E, q]
    have harg : HasDerivAt
        (fun x : ℝ => ((-l * Real.sin x : ℝ) : ℂ) * Complex.I)
        (((-l * Real.cos θ : ℝ) : ℂ) * Complex.I) θ := by
      have hreal : HasDerivAt (fun x : ℝ => -l * Real.sin x)
          (-l * Real.cos θ) θ := by
        simpa [mul_comm] using (Real.hasDerivAt_sin θ).const_mul (-l)
      simpa only [Complex.real_smul] using hreal.smul_const Complex.I
    simpa [mul_assoc, mul_left_comm, mul_comm] using harg.cexp
  have hw : ∀ θ ∈ Set.uIcc (-(Real.pi / 2) : ℝ) (Real.pi / 2),
      HasDerivAt w (w' θ) θ := by
    intro θ _
    dsimp [w, w']
    have hp := (Real.hasDerivAt_cos θ).fun_pow d
    have hp' : HasDerivAt (fun x : ℝ => Real.cos x ^ d)
        ((d : ℝ) * Real.cos θ ^ (d - 1) * (-Real.sin θ)) θ := by
      simpa only [Nat.cast_ofNat, Nat.cast_sub] using hp
    have hp'' : HasDerivAt (fun x : ℝ => Real.cos x ^ d)
        (-(d : ℝ) * Real.sin θ * Real.cos θ ^ (d - 1)) θ := by
      convert hp' using 1 ; ring
    exact hp''.ofReal_comp
  have hEcont : Continuous E := by
    dsimp [E]
    fun_prop
  have hw'cont : Continuous w' := by
    dsimp [w']
    fun_prop
  have hV'cont : Continuous (fun θ : ℝ => E θ * (Real.cos θ : ℂ)) := by
    dsimp [E]
    fun_prop
  have hV : ∀ θ ∈ Set.uIcc (-(Real.pi / 2) : ℝ) (Real.pi / 2),
      HasDerivAt (fun x : ℝ => s * E x) (E θ * (Real.cos θ : ℂ)) θ := by
    intro θ hθ
    have h := (hE θ hθ).const_mul s
    have hcancel : s * (E θ * (q * (Real.cos θ : ℂ))) =
        E θ * (Real.cos θ : ℂ) := by
      calc
        s * (E θ * (q * (Real.cos θ : ℂ))) =
            (s * q) * (E θ * (Real.cos θ : ℂ)) := by ring
        _ = E θ * (Real.cos θ : ℂ) := by rw [hsq, one_mul]
    simpa only [hcancel] using h
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := w) (u' := w') (v := fun θ => s * E θ)
    (v' := fun θ => E θ * (Real.cos θ : ℂ))
    hw hV
    (hw'cont.continuousOn.intervalIntegrable)
    (hV'cont.continuousOn.intervalIntegrable)
  have hboundary :
      w (Real.pi / 2) * (s * E (Real.pi / 2)) -
        w (-(Real.pi / 2)) * (s * E (-(Real.pi / 2))) = 0 := by
    dsimp [w]
    rw [Real.cos_pi_div_two, Real.cos_neg, Real.cos_pi_div_two]
    simp [Nat.ne_of_gt hd]
  rw [hboundary] at hparts
  have hleft :
      (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        w θ * (E θ * (Real.cos θ : ℂ))) =
        ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [w, E]
    push_cast
    rw [pow_succ]
    ring
  have hright :
      -∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2), w' θ * (s * E θ) =
        (((d : ℕ) : ℂ) * s) *
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) * E θ := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [w', E]
    push_cast
    ring
  change (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
    ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ) = _
  rw [← hleft, hparts]
  simpa only [zero_sub, s, E] using hright

private theorem intervalIntegral_meridian_height_succ_two_recurrence
    (d : Nat) (hd : 0 < d) (l : ℝ) (hl : l ≠ 0) :
    (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
      ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) *
        Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I)) =
      -(((d : ℕ) : ℂ) * ((l : ℝ) : ℂ)⁻¹) *
        deriv (fun u : ℝ =>
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
              Complex.exp (((-u * Real.sin θ : ℝ) : ℂ) * Complex.I)) l := by
  rw [(hasDerivAt_meridian_height_oscillatoryIntegral d l).deriv]
  have hrel := intervalIntegral_meridian_height_succ_two_relation d hd l hl
  have hfactor :
      (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        ((-Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
          Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I) * Complex.I) =
        (-Complex.I) *
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
              Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    push_cast
    ring
  rw [hfactor]
  have hscalar :
      (((d : ℕ) : ℂ) * ((((-l : ℝ) : ℂ) * Complex.I)⁻¹)) =
        -(((d : ℕ) : ℂ) * ((l : ℝ) : ℂ)⁻¹) * (-Complex.I) := by
    have hlc : ((l : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
    field_simp [hlc, Complex.I_ne_zero]
    rw [Complex.I_sq]
    push_cast
    ring
  calc
    (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
      ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) *
        Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I)) =
        (((d : ℕ) : ℂ) * ((((-l : ℝ) : ℂ) * Complex.I)⁻¹)) *
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
              Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I) := hrel
    _ = -(((d : ℕ) : ℂ) * ((l : ℝ) : ℂ)⁻¹) * (-Complex.I) *
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
              Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I) := by
      rw [hscalar]
    _ = -(((d : ℕ) : ℂ) * ((l : ℝ) : ℂ)⁻¹) *
          ((-Complex.I) *
            ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              ((Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
                Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I)) := by ring

/-- The exact all-parity two-step recurrence for the literal spherical height
integrals.  It is the analytic recurrence `I_{d+2}(l) = -(d/l) I_d'(l)`;
the endpoint stationary-phase estimate still needed for sharp decay is a
separate assertion. -/
theorem intervalIntegral_height_succ_two_recurrence
    {d : Nat} (hd : 2 ≤ d) (l : ℝ) (hl : l ≠ 0) :
    (∫ t in (-1 : ℝ)..1,
      ((Real.sqrt (1 - t ^ 2) ^ d : ℝ) : ℂ) *
        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)) =
      -(((d : ℕ) : ℂ) * ((l : ℝ) : ℂ)⁻¹) *
        deriv (fun u : ℝ =>
          ∫ t in (-1 : ℝ)..1,
            ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
              Complex.exp (((-u * t : ℝ) : ℂ) * Complex.I)) l := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hsucc : 2 ≤ d + 2 := by omega
  have hfun :
      (fun u : ℝ =>
        ∫ t in (-1 : ℝ)..1,
          ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
            Complex.exp (((-u * t : ℝ) : ℂ) * Complex.I)) =
      (fun u : ℝ =>
        ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
            Complex.exp (((-u * Real.sin θ : ℝ) : ℂ) * Complex.I)) := by
    funext u
    exact intervalIntegral_height_power_eq_meridian d hd u
  have hnext := intervalIntegral_height_power_eq_meridian (d + 2) hsucc l
  have hmeridian := intervalIntegral_meridian_height_succ_two_recurrence d hdpos l hl
  rw [show (d + 2) - 2 = d by omega] at hnext
  rw [hnext, hfun]
  exact hmeridian

private theorem integral_height_density_eq_intervalIntegral
    {d : Nat} (F : ℝ → ℂ) :
    (∫ t, F t ∂
      (volume.withDensity (fun t : ℝ =>
        ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
        (Ioo (-1 : ℝ) 1)) =
      ∫ t in (-1 : ℝ)..1,
        ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) * F t := by
  let w : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2)
  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hw_top : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1), w t < ⊤ :=
    Filter.Eventually.of_forall fun _ =>
      lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  change (∫ t, F t ∂(volume.withDensity w).restrict (Ioo (-1 : ℝ) 1)) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hw hw_top F measurableSet_Ioo]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  dsimp [w]
  rw [ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

private theorem intervalIntegral_t_mul_height_power_eq_meridian
    (d : Nat) (hd : 2 ≤ d) (l : ℝ) :
    (∫ t in (-1 : ℝ)..1,
      ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)) =
      ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        ((Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
          Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I) := by
  let g : ℝ → ℂ := fun t =>
    ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
      Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hsubst := intervalIntegral.integral_deriv_smul_comp
    (a := (-(Real.pi / 2) : ℝ)) (b := (Real.pi / 2 : ℝ))
    (f := Real.sin) (f' := Real.cos) (g := g)
    (fun x _ => Real.hasDerivAt_sin x) (by fun_prop) hg
  change (∫ t in (-1 : ℝ)..1, g t) = _
  rw [← Real.sin_pi_div_two, ← Real.sin_neg]
  rw [← hsubst]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hab : -(Real.pi / 2 : ℝ) ≤ Real.pi / 2 :=
    neg_le_self (le_of_lt (div_pos Real.pi_pos (by norm_num)))
  have hθ' : θ ∈ Set.Icc (-(Real.pi / 2) : ℝ) (Real.pi / 2) := by
    simpa [Set.uIcc_of_le hab] using hθ
  dsimp only [Function.comp_apply, g]
  rw [← Real.cos_eq_sqrt_one_sub_sin_sq hθ'.1 hθ'.2]
  push_cast
  rw [Complex.real_smul]
  rw [← Complex.ofReal_cos]
  have hsub : d - 1 = (d - 2) + 1 := by omega
  rw [hsub, pow_succ]
  ring

private theorem intervalIntegral_meridian_t_mul_height_succ_two_relation
    (d : Nat) (hd : 0 < d) (l : ℝ) (hl : l ≠ 0) :
    (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
      ((Real.sin θ * Real.cos θ ^ (d + 1) : ℝ) : ℂ) *
        Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I)) =
      -((((-l : ℝ) : ℂ) * Complex.I)⁻¹) *
        ((((d + 1 : ℕ) : ℂ) *
            ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) *
                Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I)) -
          ((d : ℕ) : ℂ) *
            ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
                Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I)) := by
  let E : ℝ → ℂ := fun θ =>
    Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I)
  let q : ℂ := ((-l : ℝ) : ℂ) * Complex.I
  let h : ℝ → ℂ := fun θ =>
    ((Real.sin θ * Real.cos θ ^ d : ℝ) : ℂ)
  let h' : ℝ → ℂ := fun θ =>
    ((((d : ℝ) + 1) * Real.cos θ ^ (d + 1) -
        (d : ℝ) * Real.cos θ ^ (d - 1) : ℝ) : ℂ)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hl)) Complex.I_ne_zero
  have hE : ∀ θ ∈ Set.uIcc (-(Real.pi / 2) : ℝ) (Real.pi / 2),
      HasDerivAt E (E θ * (q * (Real.cos θ : ℂ))) θ := by
    intro θ _
    dsimp [E, q]
    have harg : HasDerivAt
        (fun x : ℝ => ((-l * Real.sin x : ℝ) : ℂ) * Complex.I)
        (((-l * Real.cos θ : ℝ) : ℂ) * Complex.I) θ := by
      have hreal : HasDerivAt (fun x : ℝ => -l * Real.sin x)
          (-l * Real.cos θ) θ := by
        simpa [mul_comm] using (Real.hasDerivAt_sin θ).const_mul (-l)
      simpa only [Complex.real_smul] using hreal.smul_const Complex.I
    simpa [mul_assoc, mul_left_comm, mul_comm] using harg.cexp
  have hh : ∀ θ ∈ Set.uIcc (-(Real.pi / 2) : ℝ) (Real.pi / 2),
      HasDerivAt h (h' θ) θ := by
    intro θ _
    dsimp [h, h']
    have hsin : HasDerivAt (fun x : ℝ => Real.sin x) (Real.cos θ) θ :=
      Real.hasDerivAt_sin θ
    have hcos : HasDerivAt (fun x : ℝ => Real.cos x ^ d)
        ((d : ℝ) * Real.cos θ ^ (d - 1) * (-Real.sin θ)) θ := by
      simpa only [Nat.cast_sub] using (Real.hasDerivAt_cos θ).fun_pow d
    have hprod := hsin.mul hcos
    change HasDerivAt
      (fun x : ℝ => Real.sin x * Real.cos x ^ d)
      (Real.cos θ * Real.cos θ ^ d +
        Real.sin θ * ((d : ℝ) * Real.cos θ ^ (d - 1) * (-Real.sin θ))) θ at hprod
    have hprod' : HasDerivAt
        (fun x : ℝ => Real.sin x * Real.cos x ^ d)
        (Real.cos θ ^ (d + 1) -
          (d : ℝ) * Real.sin θ ^ 2 * Real.cos θ ^ (d - 1)) θ := by
      convert hprod using 1
      rw [pow_succ]
      ring
    have htrig : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have halgebra :
        Real.cos θ ^ (d + 1) -
            (d : ℝ) * Real.sin θ ^ 2 * Real.cos θ ^ (d - 1) =
          ((d : ℝ) + 1) * Real.cos θ ^ (d + 1) -
            (d : ℝ) * Real.cos θ ^ (d - 1) := by
      rw [htrig]
      rw [show d + 1 = (d - 1) + 2 by omega, pow_add]
      ring
    rw [halgebra] at hprod'
    exact hprod'.ofReal_comp
  have hEcont : Continuous E := by
    dsimp [E]
    fun_prop
  have hE'cont : Continuous (fun θ => E θ * (q * (Real.cos θ : ℂ))) := by
    dsimp [E, q]
    fun_prop
  have hh'cont : Continuous h' := by
    dsimp [h']
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := E) (u' := fun θ => E θ * (q * (Real.cos θ : ℂ)))
    (v := h) (v' := h') hE hh
    (hE'cont.continuousOn.intervalIntegrable)
    (hh'cont.continuousOn.intervalIntegrable)
  have hboundary :
      E (Real.pi / 2) * h (Real.pi / 2) -
        E (-(Real.pi / 2)) * h (-(Real.pi / 2)) = 0 := by
    dsimp [h]
    rw [Real.cos_pi_div_two, Real.cos_neg, Real.cos_pi_div_two]
    simp [Nat.ne_of_gt hd]
  rw [hboundary] at hparts
  simp only [zero_sub] at hparts
  have hleft :
      (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2), E θ * h' θ) =
        (((d : ℂ) + 1) *
            ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ) -
          ((d : ℕ) : ℂ) *
            ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) * E θ := by
    calc
      (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2), E θ * h' θ) =
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            (((d : ℂ) + 1) * ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ -
              (d : ℂ) * ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) * E θ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp [h']
        push_cast
        ring
      _ = (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((d : ℂ) + 1) * ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ) -
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            (d : ℂ) * ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) * E θ := by
        rw [intervalIntegral.integral_sub]
        · exact (by fun_prop : Continuous fun θ : ℝ =>
            ((d : ℂ) + 1) * ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ).continuousOn.intervalIntegrable
        · exact (by fun_prop : Continuous fun θ : ℝ =>
            (d : ℂ) * ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) * E θ).continuousOn.intervalIntegrable
      _ = _ := by
        have hfirst :
            (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              ((d : ℂ) + 1) * ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ) =
              ((d : ℂ) + 1) *
                ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
                  ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro θ _
          ring
        have hsecond :
            (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              (d : ℂ) * ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) * E θ) =
              (d : ℂ) *
                ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
                  ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) * E θ := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro θ _
          ring
        rw [hfirst, hsecond]
  have hright :
      -∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        (E θ * (q * (Real.cos θ : ℂ))) * h θ =
      -q *
        ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          ((Real.sin θ * Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [h]
    push_cast
    ring
  have hrelation :
      (((d : ℂ) + 1) *
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ) -
        ((d : ℕ) : ℂ) *
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) * E θ =
        -q *
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((Real.sin θ * Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ := by
    rw [← hleft, hparts, hright]
  have hsolve :
    (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
      ((Real.sin θ * Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ) =
      -q⁻¹ *
        ((((d : ℂ) + 1) *
            ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ) -
          ((d : ℕ) : ℂ) *
            ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) * E θ) := by
    calc
      (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        ((Real.sin θ * Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ) =
        -(q⁻¹) * (-q *
          ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
            ((Real.sin θ * Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ) := by
          field_simp [hq]
    _ = -q⁻¹ *
        ((((d : ℂ) + 1) *
            (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              ((Real.cos θ ^ (d + 1) : ℝ) : ℂ) * E θ)) -
          ((d : ℕ) : ℂ) *
            (∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
              ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) * E θ)) := by rw [← hrelation]
  have hcast : ((d + 1 : ℕ) : ℂ) = (d : ℂ) + 1 := by
    push_cast
    ring
  rw [hcast]
  simpa [E, q] using hsolve

private theorem intervalIntegral_t_mul_height_succ_two_recurrence
    {d : Nat} (hd : 2 ≤ d) (l : ℝ) (hl : l ≠ 0) :
    (∫ t in (-1 : ℝ)..1,
      ((Real.sqrt (1 - t ^ 2) ^ d : ℝ) : ℂ) *
        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)) =
      -((((-l : ℝ) : ℂ) * Complex.I)⁻¹) *
        ((((d + 1 : ℕ) : ℂ) *
            (∫ t in (-1 : ℝ)..1,
              ((Real.sqrt (1 - t ^ 2) ^ d : ℝ) : ℂ) *
                Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I))) -
          ((d : ℕ) : ℂ) *
            (∫ t in (-1 : ℝ)..1,
              ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
                Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I))) := by
  have hdnext : 2 ≤ d + 2 := by omega
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hJ := intervalIntegral_t_mul_height_power_eq_meridian (d + 2) hdnext l
  have hIhigh := intervalIntegral_height_power_eq_meridian (d + 2) hdnext l
  have hIlow := intervalIntegral_height_power_eq_meridian d hd l
  have hmeridian := intervalIntegral_meridian_t_mul_height_succ_two_relation d hdpos l hl
  rw [show (d + 2) - 2 = d by omega] at hJ hIhigh
  rw [hJ, hIhigh, hIlow]
  exact hmeridian

private theorem norm_intervalIntegral_t_mul_exp_le (l : ℝ) (hl : 1 ≤ l) :
    ‖∫ t in (-1 : ℝ)..1,
      Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)‖ ≤
      4 / l := by
  let E : ℝ → ℂ := fun t =>
    Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)
  let q : ℂ := ((-l : ℝ) : ℂ) * Complex.I
  let s : ℂ := q⁻¹
  have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hlpos.ne')) Complex.I_ne_zero
  have hsq : s * q = 1 := by
    dsimp [s]
    exact inv_mul_cancel₀ hq
  have hE : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt E (E t * q) t := by
    intro t _
    dsimp [E, q]
    have harg : HasDerivAt
        (fun x : ℝ => ((-l * x : ℝ) : ℂ) * Complex.I)
        (((-l : ℝ) : ℂ) * Complex.I) t := by
      have hreal : HasDerivAt (fun x : ℝ => -l * x) (-l) t := by
        simpa using (hasDerivAt_id t).const_mul (-l)
      simpa only [Complex.real_smul] using hreal.smul_const Complex.I
    simpa [mul_assoc] using harg.cexp
  have hu : ∀ t ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) t := by
    intro t _
    simpa using (hasDerivAt_id t).ofReal_comp
  have hEcont : Continuous E := by
    dsimp [E]
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => (t : ℂ)) (u' := fun _ : ℝ => (1 : ℂ))
    (v := fun t => s * E t) (v' := fun t => E t) hu
    (by
      intro t ht
      have h := (hE t ht).const_mul s
      have hcancel : s * (E t * q) = E t := by
        calc
          s * (E t * q) = (s * q) * E t := by ring
          _ = E t := by rw [hsq, one_mul]
      simpa only [hcancel] using h)
    (Continuous.continuousOn (by fun_prop : Continuous fun _ : ℝ => (1 : ℂ))).intervalIntegrable
    (hEcont.continuousOn.intervalIntegrable)
  have hformula :
      (∫ t in (-1 : ℝ)..1, E t * ((t : ℝ) : ℂ)) =
        (1 : ℂ) * (s * E 1) - (-1 : ℂ) * (s * E (-1)) -
          ∫ t in (-1 : ℝ)..1, (1 : ℂ) * (s * E t) := by
    calc
      (∫ t in (-1 : ℝ)..1, E t * ((t : ℝ) : ℂ)) =
          ∫ t in (-1 : ℝ)..1, ((t : ℝ) : ℂ) * E t := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by simpa using hparts
  have hEnorm (t : ℝ) : ‖E t‖ = 1 := by
    dsimp [E]
    rw [Complex.norm_exp_ofReal_mul_I]
  have hsnorm : ‖s‖ = 1 / l := by
    dsimp [s, q]
    rw [norm_inv, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_neg, abs_of_pos hlpos, Complex.norm_I, mul_one]
    ring
  have hrest :
      ‖∫ t in (-1 : ℝ)..1, (1 : ℂ) * (s * E t)‖ ≤ 2 * ‖s‖ := by
    calc
      ‖∫ t in (-1 : ℝ)..1, (1 : ℂ) * (s * E t)‖ ≤
          ‖s‖ * |(1 : ℝ) - (-1)| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t _
        simp [hEnorm]
      _ = 2 * ‖s‖ := by norm_num; ring
  change ‖∫ t in (-1 : ℝ)..1, E t * ((t : ℝ) : ℂ)‖ ≤ 4 / l
  rw [hformula]
  have hleftnorm : ‖(1 : ℂ) * (s * E 1)‖ = ‖s‖ := by
    simp [hEnorm]
  have hrightnorm : ‖(-1 : ℂ) * (s * E (-1))‖ = ‖s‖ := by
    simp [hEnorm]
  calc
    ‖(1 : ℂ) * (s * E 1) - (-1 : ℂ) * (s * E (-1)) -
        ∫ t in (-1 : ℝ)..1, (1 : ℂ) * (s * E t)‖ ≤
        ‖(1 : ℂ) * (s * E 1)‖ + ‖(-1 : ℂ) * (s * E (-1))‖ +
          ‖∫ t in (-1 : ℝ)..1, (1 : ℂ) * (s * E t)‖ := by
      calc
        _ ≤ ‖(1 : ℂ) * (s * E 1) - (-1 : ℂ) * (s * E (-1))‖ +
            ‖∫ t in (-1 : ℝ)..1, (1 : ℂ) * (s * E t)‖ := norm_sub_le _ _
        _ ≤ _ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖s‖ + ‖s‖ + 2 * ‖s‖ := by
      rw [hleftnorm, hrightnorm]
      gcongr
    _ = 4 / l := by rw [hsnorm]; ring

private theorem norm_intervalIntegral_exp_le (l : ℝ) (hl : 1 ≤ l) :
    ‖∫ t in (-1 : ℝ)..1,
      Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)‖ ≤
      2 / l := by
  have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl
  let a : ℝ := l / (2 * Real.pi)
  have hapos : 0 < a := by
    dsimp [a]
    positivity
  have ha : a ≠ 0 := hapos.ne'
  have hbound := norm_intervalIntegral_exp_surfacePhase_le a ha
  have hphase :
      (∫ t in (-1 : ℝ)..1,
        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)) =
        ∫ t in (-1 : ℝ)..1,
          Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [a]
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  calc
    ‖∫ t in (-1 : ℝ)..1,
      Complex.exp (((-2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I)‖ ≤
        1 / (Real.pi * |a|) := hbound
    _ = 2 / l := by
      rw [abs_of_pos hapos]
      dsimp [a]
      field_simp [Real.pi_ne_zero, hlpos.ne']

private theorem height_decay_exponent_succ_two (k : Nat) {l : ℝ} (hl : 0 < l) :
    l ^ (((k + 2 : Nat) : ℝ) / 2 + 1) =
      l ^ ((k : ℝ) / 2 + 1) * l := by
  calc
    l ^ (((k + 2 : Nat) : ℝ) / 2 + 1) =
        l ^ (((k : ℝ) / 2 + 1) + 1) := by
      congr 1
      push_cast
      ring
    _ = l ^ ((k : ℝ) / 2 + 1) * l ^ (1 : ℝ) :=
      Real.rpow_add hl _ _
    _ = _ := by rw [Real.rpow_one]

private theorem height_decay_exponent_one {l : ℝ} (hl : 0 < l) :
    l ^ (((1 : ℕ) : ℝ) / 2 + 1) = l * Real.sqrt l := by
  rw [Real.sqrt_eq_rpow]
  calc
    l ^ (((1 : ℕ) : ℝ) / 2 + 1) = l ^ ((1 : ℝ) / 2 + 1) := by norm_num
    _ = l ^ (1 : ℝ) * l ^ ((1 : ℝ) / 2) := by
      rw [add_comm]
      exact Real.rpow_add hl _ _
    _ = _ := by rw [Real.rpow_one]

private theorem hasDerivAt_intervalIntegral_height_power
    (d : Nat) (hd : 2 ≤ d) (l : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        ∫ t in (-1 : ℝ)..1,
          ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
            Complex.exp (((-u * t : ℝ) : ℂ) * Complex.I))
      (∫ t in (-1 : ℝ)..1,
        ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
          Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) *
            (((-t : ℝ) : ℂ) * Complex.I)) l := by
  have hmeridian := hasDerivAt_meridian_height_oscillatoryIntegral d l
  have hfun :
      (fun u : ℝ =>
        ∫ t in (-1 : ℝ)..1,
          ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
            Complex.exp (((-u * t : ℝ) : ℂ) * Complex.I)) =
      (fun u : ℝ =>
        ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          ((Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
            Complex.exp (((-u * Real.sin θ : ℝ) : ℂ) * Complex.I)) := by
    funext u
    exact intervalIntegral_height_power_eq_meridian d hd u
  rw [hfun]
  convert hmeridian using 1
  have hmoment := intervalIntegral_t_mul_height_power_eq_meridian d hd l
  calc
    (∫ t in (-1 : ℝ)..1,
      ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) *
          (((-t : ℝ) : ℂ) * Complex.I)) =
        (-Complex.I) *
          ∫ t in (-1 : ℝ)..1,
            ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
              Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      push_cast
      ring
    _ = (-Complex.I) *
        ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
          ((Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
            Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I) := by
      rw [hmoment]
    _ = ∫ θ in (-(Real.pi / 2) : ℝ)..(Real.pi / 2),
        ((-Real.sin θ * Real.cos θ ^ (d - 1) : ℝ) : ℂ) *
          Complex.exp (((-l * Real.sin θ : ℝ) : ℂ) * Complex.I) * Complex.I := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      push_cast
      ring

private theorem exists_height_power_decay_and_moment (k : Nat) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ l : ℝ, 1 ≤ l →
      ‖∫ t in (-1 : ℝ)..1,
        ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
          Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)‖ ≤
          A / l ^ ((k : ℝ) / 2 + 1) ∧
      ‖∫ t in (-1 : ℝ)..1,
        ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
          Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)‖ ≤
          B / l ^ ((k : ℝ) / 2 + 1) := by
  induction k using Nat.twoStepInduction with
  | zero =>
      refine ⟨2, 4, by norm_num, by norm_num, ?_⟩
      intro l hl
      constructor
      · simpa using norm_intervalIntegral_exp_le l hl
      · simpa using norm_intervalIntegral_t_mul_exp_le l hl
  | one =>
      refine ⟨16, 92, by norm_num, by norm_num, ?_⟩
      intro l hl
      have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl
      constructor
      · calc
          ‖∫ t in (-1 : ℝ)..1,
            ((Real.sqrt (1 - t ^ 2) ^ (1 : ℕ) : ℝ) : ℂ) *
              Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)‖ ≤
              16 / (l * Real.sqrt l) := by
            simpa using norm_intervalIntegral_semicircle_le l hl
          _ = 16 / l ^ (((1 : ℕ) : ℝ) / 2 + 1) := by
            rw [height_decay_exponent_one hlpos]
      · calc
          ‖∫ t in (-1 : ℝ)..1,
            ((Real.sqrt (1 - t ^ 2) ^ (1 : ℕ) : ℝ) : ℂ) *
              Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)‖ ≤
              92 / (l * Real.sqrt l) := by
            simpa using norm_intervalIntegral_t_mul_semicircle_le l hl
          _ = 92 / l ^ (((1 : ℕ) : ℝ) / 2 + 1) := by
            rw [height_decay_exponent_one hlpos]
  | more k hk _ =>
      rcases hk with ⟨A, B, hA, hB, hk⟩
      refine ⟨((k + 2 : ℕ) : ℝ) * B,
        ((k + 3 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) * B) +
          ((k + 2 : ℕ) : ℝ) * A,
        ?_, ?_, ?_⟩
      · positivity
      · positivity
      · intro l hl
        have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl
        have hlne : l ≠ 0 := hlpos.ne'
        have hdnext : 2 ≤ k + 2 := by omega
        have hkbound := hk l hl
        have hrec := intervalIntegral_height_succ_two_recurrence
          (d := k + 2) hdnext l hlne
        have hderiv := hasDerivAt_intervalIntegral_height_power (k + 2) hdnext l
        have hkexp : k + 2 - 2 = k := by omega
        simp only [hkexp] at hrec hderiv
        have hderivnorm :
            ‖deriv (fun u : ℝ =>
              ∫ t in (-1 : ℝ)..1,
                ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
                  Complex.exp (((-u * t : ℝ) : ℂ) * Complex.I)) l‖ =
              ‖∫ t in (-1 : ℝ)..1,
                ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
                  Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)‖ := by
          rw [hderiv.deriv]
          have hfactor :
              (∫ t in (-1 : ℝ)..1,
                ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
                  Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) *
                    (((-t : ℝ) : ℂ) * Complex.I)) =
                (-Complex.I) *
                  ∫ t in (-1 : ℝ)..1,
                    ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
                      Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro t _
            push_cast
            ring
          rw [hfactor, norm_mul, norm_neg, Complex.norm_I, one_mul]
        have hcoefnorm :
            ‖-(((k + 2 : ℕ) : ℂ) * ((l : ℝ) : ℂ)⁻¹)‖ =
              ((k + 2 : ℕ) : ℝ) / l := by
          rw [norm_neg, norm_mul, norm_natCast, norm_inv, Complex.norm_real,
            Real.norm_of_nonneg hlpos.le]
          field_simp
        have hInew :
            ‖∫ t in (-1 : ℝ)..1,
              ((Real.sqrt (1 - t ^ 2) ^ (k + 2) : ℝ) : ℂ) *
                Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)‖ ≤
              (((k + 2 : ℕ) : ℝ) * B) /
                l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1) := by
          rw [hrec, norm_mul, hcoefnorm, hderivnorm]
          calc
            ((k + 2 : ℕ) : ℝ) / l *
                ‖∫ t in (-1 : ℝ)..1,
                  ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
                    Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)‖ ≤
                ((k + 2 : ℕ) : ℝ) / l *
                  (B / l ^ ((k : ℝ) / 2 + 1)) := by
              gcongr
              exact hkbound.2
            _ = (((k + 2 : ℕ) : ℝ) * B) /
                (l ^ ((k : ℝ) / 2 + 1) * l) := by
              field_simp [hlne,
                (Real.rpow_pos_of_pos hlpos ((k : ℝ) / 2 + 1)).ne']
            _ = (((k + 2 : ℕ) : ℝ) * B) /
                l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1) := by
              rw [height_decay_exponent_succ_two k hlpos]
        constructor
        · exact hInew
        · have hJrec := intervalIntegral_t_mul_height_succ_two_recurrence
            (d := k + 2) hdnext l hlne
          have hqnorm : ‖-((((-l : ℝ) : ℂ) * Complex.I)⁻¹)‖ = 1 / l := by
            rw [norm_neg, norm_inv, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_neg, abs_of_pos hlpos, Complex.norm_I, mul_one]
            ring
          have hinside :
              ‖((k + 3 : ℕ) : ℂ) *
                  (∫ t in (-1 : ℝ)..1,
                    ((Real.sqrt (1 - t ^ 2) ^ (k + 2) : ℝ) : ℂ) *
                      Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)) -
                ((k + 2 : ℕ) : ℂ) *
                  (∫ t in (-1 : ℝ)..1,
                    ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
                      Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I))‖ ≤
                ((k + 3 : ℕ) : ℝ) *
                  ((((k + 2 : ℕ) : ℝ) * B) /
                    l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1)) +
                  ((k + 2 : ℕ) : ℝ) *
                    (A / l ^ ((k : ℝ) / 2 + 1)) := by
            calc
              ‖((k + 3 : ℕ) : ℂ) *
                    (∫ t in (-1 : ℝ)..1,
                      ((Real.sqrt (1 - t ^ 2) ^ (k + 2) : ℝ) : ℂ) *
                        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)) -
                  ((k + 2 : ℕ) : ℂ) *
                    (∫ t in (-1 : ℝ)..1,
                      ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
                        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I))‖ ≤
                  ‖((k + 3 : ℕ) : ℂ) *
                    (∫ t in (-1 : ℝ)..1,
                      ((Real.sqrt (1 - t ^ 2) ^ (k + 2) : ℝ) : ℂ) *
                        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I))‖ +
                    ‖((k + 2 : ℕ) : ℂ) *
                      (∫ t in (-1 : ℝ)..1,
                        ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
                          Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I))‖ := norm_sub_le _ _
              _ = ((k + 3 : ℕ) : ℝ) *
                    ‖∫ t in (-1 : ℝ)..1,
                      ((Real.sqrt (1 - t ^ 2) ^ (k + 2) : ℝ) : ℂ) *
                        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)‖ +
                    ((k + 2 : ℕ) : ℝ) *
                      ‖∫ t in (-1 : ℝ)..1,
                        ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
                          Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)‖ := by
                rw [norm_mul, norm_natCast, norm_mul, norm_natCast]
              _ ≤ _ := by
                apply add_le_add
                · exact mul_le_mul_of_nonneg_left hInew (by positivity)
                · exact mul_le_mul_of_nonneg_left hkbound.1 (by positivity)
          rw [hJrec, norm_mul, hqnorm]
          calc
            (1 / l) *
                ‖((k + 3 : ℕ) : ℂ) *
                    (∫ t in (-1 : ℝ)..1,
                      ((Real.sqrt (1 - t ^ 2) ^ (k + 2) : ℝ) : ℂ) *
                        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)) -
                  ((k + 2 : ℕ) : ℂ) *
                    (∫ t in (-1 : ℝ)..1,
                      ((Real.sqrt (1 - t ^ 2) ^ k : ℝ) : ℂ) *
                        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I))‖ ≤
                (1 / l) *
                  (((k + 3 : ℕ) : ℝ) *
                    ((((k + 2 : ℕ) : ℝ) * B) /
                      l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1)) +
                    ((k + 2 : ℕ) : ℝ) *
                      (A / l ^ ((k : ℝ) / 2 + 1))) := by
              gcongr
            _ ≤ (((k + 3 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) * B) +
                  ((k + 2 : ℕ) : ℝ) * A) /
                  l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1) := by
              have hone_div : 1 / l ≤ 1 := by
                exact (div_le_iff₀ hlpos).2 (by simpa using hl)
              have hDpos : 0 < l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1) :=
                Real.rpow_pos_of_pos hlpos _
              have hEpos : 0 < l ^ ((k : ℝ) / 2 + 1) :=
                Real.rpow_pos_of_pos hlpos _
              have hhigh :
                  (1 / l) *
                    (((k + 3 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) * B) /
                      l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1)) ≤
                    ((k + 3 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) * B) /
                      l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1) := by
                have hnonneg : 0 ≤
                    ((k + 3 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) * B) /
                      l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1) := by positivity
                simpa using mul_le_mul_of_nonneg_right hone_div hnonneg
              have hhigh' :
                  (1 / l) *
                    (((k + 3 : ℕ) : ℝ) *
                      ((((k + 2 : ℕ) : ℝ) * B) /
                        l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1))) ≤
                    ((k + 3 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) * B) /
                      l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1) := by
                convert hhigh using 1 <;> ring
              have hlow :
                  (1 / l) *
                    (((k + 2 : ℕ) : ℝ) * (A / l ^ ((k : ℝ) / 2 + 1))) =
                    ((k + 2 : ℕ) : ℝ) * A /
                      l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1) := by
                rw [height_decay_exponent_succ_two k hlpos]
                field_simp [hlne, hEpos.ne']
              rw [mul_add]
              calc
                _ ≤ ((k + 3 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) * B) /
                      l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1) +
                    ((k + 2 : ℕ) : ℝ) * A /
                      l ^ (((k + 2 : ℕ) : ℝ) / 2 + 1) := by
                    rw [hlow]
                    exact add_le_add hhigh' le_rfl
                _ = _ := by
                  field_simp [hDpos.ne']

private theorem surfaceFourier_succ_height_intervalIntegral
    {d : Nat} (hd : 2 ≤ d) (ξ : Euclidean (d + 1)) :
    surfaceFourier (d + 1) ξ =
      (surfaceMass d : ℂ) *
        ∫ t in (-1 : ℝ)..1,
          ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
            Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I) := by
  rw [surfaceFourier_succ_height_integral hd ξ]
  congr 1
  exact integral_height_density_eq_intervalIntegral _

private theorem exists_surfaceFourier_succ_sharp_decay {d : Nat} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Euclidean (d + 1), 1 ≤ ‖ξ‖ →
      ‖surfaceFourier (d + 1) ξ‖ ≤ C / ‖ξ‖ ^ ((d : ℝ) / 2) := by
  obtain ⟨A, B, hA, hB, hheight⟩ := exists_height_power_decay_and_moment (d - 2)
  have hmass : 0 ≤ surfaceMass d := by
    unfold surfaceMass
    exact measureReal_nonneg
  refine ⟨(surfaceMass d + 1) * A,
    mul_pos (by linarith) hA, ?_⟩
  intro ξ hξ
  let l : ℝ := 2 * Real.pi * ‖ξ‖
  have hl : 1 ≤ l := by
    dsimp [l]
    have htwo_pi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    calc
      1 ≤ 2 * Real.pi * 1 := by simpa using htwo_pi
      _ ≤ 2 * Real.pi * ‖ξ‖ := by gcongr
  have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hnormpos : 0 < ‖ξ‖ := lt_of_lt_of_le (by norm_num) hξ
  have hpow : ((d - 2 : Nat) : ℝ) / 2 + 1 = (d : ℝ) / 2 := by
    rw [Nat.cast_sub hd]
    ring
  have hheightbound := (hheight l hl).1
  have hI :
      ‖∫ t in (-1 : ℝ)..1,
        ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
          Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I)‖ ≤
        A / l ^ ((d : ℝ) / 2) := by
    simpa [l, hpow] using hheightbound
  have hbase : ‖ξ‖ ≤ l := by
    dsimp [l]
    have htwo_pi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_nonneg (sub_nonneg.mpr htwo_pi) (norm_nonneg ξ)]
  have hp : 0 ≤ (d : ℝ) / 2 := by positivity
  have hrpow : ‖ξ‖ ^ ((d : ℝ) / 2) ≤ l ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow (norm_nonneg _) hbase hp
  have hdenξ : 0 < ‖ξ‖ ^ ((d : ℝ) / 2) :=
    Real.rpow_pos_of_pos hnormpos _
  have hdenl : 0 < l ^ ((d : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlpos _
  have hratio : A / l ^ ((d : ℝ) / 2) ≤ A / ‖ξ‖ ^ ((d : ℝ) / 2) := by
    exact (div_le_div_iff_of_pos_left hA hdenl hdenξ).2 hrpow
  rw [surfaceFourier_succ_height_intervalIntegral hd ξ, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hmass]
  calc
    surfaceMass d *
        ‖∫ t in (-1 : ℝ)..1,
          ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
            Complex.exp (((-2 * Real.pi * ‖ξ‖ * t : ℝ) : ℂ) * Complex.I)‖ ≤
        surfaceMass d * (A / l ^ ((d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hI hmass
    _ ≤ surfaceMass d * (A / ‖ξ‖ ^ ((d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hratio hmass
    _ = (surfaceMass d * A) / ‖ξ‖ ^ ((d : ℝ) / 2) := by ring
    _ ≤ ((surfaceMass d + 1) * A) / ‖ξ‖ ^ ((d : ℝ) / 2) := by
      apply div_le_div_of_nonneg_right _ hdenξ.le
      nlinarith

set_option maxHeartbeats 800000 in
-- The local radial reparametrization expands a nested interval integral.
private theorem hasDerivAt_surfaceFourier_succ_height_smul
    {d : Nat} (hd : 2 ≤ d) (ξ : Euclidean (d + 1)) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => surfaceFourier (d + 1) (s • ξ))
      ((surfaceMass d : ℂ) *
        ((2 * Real.pi * ‖ξ‖ : ℝ) •
          ∫ t in (-1 : ℝ)..1,
            ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
              Complex.exp (((-(2 * Real.pi * r * ‖ξ‖) * t : ℝ) : ℂ) * Complex.I) *
                (((-t : ℝ) : ℂ) * Complex.I))) r := by
  let I : ℝ → ℂ := fun l =>
    ∫ t in (-1 : ℝ)..1,
      ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
        Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I)
  have hlinear : HasDerivAt (fun s : ℝ => 2 * Real.pi * s * ‖ξ‖)
      (2 * Real.pi * ‖ξ‖) r := by
    simpa [mul_assoc] using
      ((hasDerivAt_id r).mul_const ‖ξ‖).const_mul (2 * Real.pi)
  have hIderiv := hasDerivAt_intervalIntegral_height_power d hd
    (2 * Real.pi * r * ‖ξ‖)
  have hcomp : HasDerivAt (fun s : ℝ => I (2 * Real.pi * s * ‖ξ‖))
      (((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) *
        ∫ t in (-1 : ℝ)..1,
          ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
            Complex.exp (((-(2 * Real.pi * r * ‖ξ‖) * t : ℝ) : ℂ) * Complex.I) *
               (((-t : ℝ) : ℂ) * Complex.I)) r := by
    dsimp [I]
    simpa [Function.comp_def, Complex.real_smul] using
      HasDerivAt.scomp_of_eq r hIderiv hlinear (by rfl)
  have hmodel := hcomp.const_mul (surfaceMass d : ℂ)
  have hlocal : (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) =ᶠ[𝓝 r]
      fun s => (surfaceMass d : ℂ) * I (2 * Real.pi * s * ‖ξ‖) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    rw [surfaceFourier_succ_height_intervalIntegral hd (s • ξ)]
    have hnorm : ‖s • ξ‖ = s * ‖ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    rw [hnorm]
    dsimp [I]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    push_cast
    ring
  have hresult := hmodel.congr_of_eventuallyEq hlocal
  simpa [I, Complex.real_smul, mul_assoc, mul_left_comm, mul_comm] using hresult

private theorem exists_surfaceFourier_succ_sharp_deriv {d : Nat} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Euclidean (d + 1), ∀ r : ℝ,
      1 ≤ ‖ξ‖ → r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r‖ ≤
        C / ‖ξ‖ ^ ((d : ℝ) / 2 - 1) := by
  obtain ⟨A, B, hA, hB, hheight⟩ := exists_height_power_decay_and_moment (d - 2)
  have hmass : 0 ≤ surfaceMass d := by
    unfold surfaceMass
    exact measureReal_nonneg
  refine ⟨(surfaceMass d + 1) * (2 * Real.pi) * B, by positivity, ?_⟩
  intro ξ r hξ hr
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
  let l : ℝ := 2 * Real.pi * r * ‖ξ‖
  have hl : 1 ≤ l := by
    dsimp [l]
    have htwo_pi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    calc
      1 ≤ (2 * Real.pi) * 1 * 1 := by simpa using htwo_pi
      _ ≤ (2 * Real.pi) * r * ‖ξ‖ := by
        gcongr
        exact hr.1
  have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hnormpos : 0 < ‖ξ‖ := lt_of_lt_of_le (by norm_num) hξ
  have hpow : ((d - 2 : Nat) : ℝ) / 2 + 1 = (d : ℝ) / 2 := by
    rw [Nat.cast_sub hd]
    ring
  have hJbound := (hheight l hl).2
  have hJ :
      ‖∫ t in (-1 : ℝ)..1,
        ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
          Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)‖ ≤
        B / l ^ ((d : ℝ) / 2) := by
    simpa [hpow] using hJbound
  have hbase : ‖ξ‖ ≤ l := by
    dsimp [l]
    have htwo_pi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hfactor : 1 ≤ 2 * Real.pi * r := by
      calc
        1 ≤ 2 * Real.pi * 1 := by simpa using htwo_pi
        _ ≤ 2 * Real.pi * r := by
          gcongr
          exact hr.1
    nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) (norm_nonneg ξ)]
  have hp : 0 ≤ (d : ℝ) / 2 := by positivity
  have hrpow : ‖ξ‖ ^ ((d : ℝ) / 2) ≤ l ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow (norm_nonneg _) hbase hp
  have hdenξ : 0 < ‖ξ‖ ^ ((d : ℝ) / 2) :=
    Real.rpow_pos_of_pos hnormpos _
  have hdenl : 0 < l ^ ((d : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlpos _
  have hratio : B / l ^ ((d : ℝ) / 2) ≤ B / ‖ξ‖ ^ ((d : ℝ) / 2) := by
    exact (div_le_div_iff_of_pos_left hB hdenl hdenξ).2 hrpow
  have hderiv := hasDerivAt_surfaceFourier_succ_height_smul hd ξ hrpos
  have hmomentfactor :
      ‖∫ t in (-1 : ℝ)..1,
        ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
          Complex.exp (((-(2 * Real.pi * r * ‖ξ‖) * t : ℝ) : ℂ) * Complex.I) *
            (((-t : ℝ) : ℂ) * Complex.I)‖ =
        ‖∫ t in (-1 : ℝ)..1,
          ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
            Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)‖ := by
    have hnegfactor :
        (∫ t in (-1 : ℝ)..1,
          ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
            Complex.exp (((-(2 * Real.pi * r * ‖ξ‖) * t : ℝ) : ℂ) * Complex.I) *
              (((-t : ℝ) : ℂ) * Complex.I)) =
          (-Complex.I) *
            ∫ t in (-1 : ℝ)..1,
              ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
                Complex.exp (((-(2 * Real.pi * r * ‖ξ‖) * t : ℝ) : ℂ) * Complex.I) *
                  ((t : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      push_cast
      ring
    rw [hnegfactor, norm_mul, norm_neg, Complex.norm_I, one_mul]
  rw [hderiv.deriv]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hmass,
    norm_smul, Real.norm_of_nonneg (by positivity), hmomentfactor]
  have hpowsplit :
      ‖ξ‖ ^ ((d : ℝ) / 2) =
        ‖ξ‖ ^ ((d : ℝ) / 2 - 1) * ‖ξ‖ := by
    calc
      ‖ξ‖ ^ ((d : ℝ) / 2) =
          ‖ξ‖ ^ (((d : ℝ) / 2 - 1) + 1) := by
        congr 1
        ring
      _ = _ := by
        rw [Real.rpow_add hnormpos, Real.rpow_one]
  have hdenprev : 0 < ‖ξ‖ ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_pos_of_pos hnormpos _
  have hscale :
      surfaceMass d * (2 * Real.pi * ‖ξ‖) *
          (B / ‖ξ‖ ^ ((d : ℝ) / 2)) =
        (surfaceMass d * (2 * Real.pi) * B) /
          ‖ξ‖ ^ ((d : ℝ) / 2 - 1) := by
    rw [hpowsplit]
    field_simp [hnormpos.ne', hdenprev.ne']
  have hmassgrow :
      surfaceMass d * (2 * Real.pi) * B ≤
        (surfaceMass d + 1) * (2 * Real.pi) * B := by
    have hfactor : 0 ≤ (2 * Real.pi) * B := by positivity
    calc
      surfaceMass d * (2 * Real.pi) * B = surfaceMass d * ((2 * Real.pi) * B) := by ring
      _ ≤ (surfaceMass d + 1) * ((2 * Real.pi) * B) :=
        mul_le_mul_of_nonneg_right (by linarith) hfactor
      _ = (surfaceMass d + 1) * (2 * Real.pi) * B := by ring
  have hJξ :
      ‖∫ t in (-1 : ℝ)..1,
        ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
          Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)‖ ≤
        B / ‖ξ‖ ^ ((d : ℝ) / 2) := hJ.trans hratio
  calc
    surfaceMass d *
        (2 * Real.pi * ‖ξ‖ *
          ‖∫ t in (-1 : ℝ)..1,
            ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
              Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)‖) =
        (surfaceMass d * (2 * Real.pi * ‖ξ‖)) *
          ‖∫ t in (-1 : ℝ)..1,
            ((Real.sqrt (1 - t ^ 2) ^ (d - 2) : ℝ) : ℂ) *
              Complex.exp (((-l * t : ℝ) : ℂ) * Complex.I) * ((t : ℝ) : ℂ)‖ := by ring
    _ ≤ (surfaceMass d * (2 * Real.pi * ‖ξ‖)) *
          (B / ‖ξ‖ ^ ((d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hJξ (by positivity)
    _ = (surfaceMass d * (2 * Real.pi) * B) /
          ‖ξ‖ ^ ((d : ℝ) / 2 - 1) := hscale
    _ ≤ ((surfaceMass d + 1) * (2 * Real.pi) * B) /
          ‖ξ‖ ^ ((d : ℝ) / 2 - 1) :=
      div_le_div_of_nonneg_right hmassgrow hdenprev.le

/-- The all-dimensional sharp oscillatory estimate required for the
dyadic proof of Stein's spherical maximal theorem.  The preceding height
formula reduces this to endpoint stationary phase for the literal density
`(sqrt (1 - t²))^(d - 2)`. -/
theorem exists_sharp_surfaceFourier_succ_decay_and_deriv {d : Nat} (hd : 2 ≤ d) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      (∀ ξ : Euclidean (d + 1), 1 ≤ ‖ξ‖ →
        ‖surfaceFourier (d + 1) ξ‖ ≤ C₀ / ‖ξ‖ ^ ((d : ℝ) / 2)) ∧
      (∀ ξ : Euclidean (d + 1), ∀ r : ℝ, 1 ≤ ‖ξ‖ → r ∈ Icc (1 : ℝ) 2 →
        ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r‖ ≤
          C₁ / ‖ξ‖ ^ ((d : ℝ) / 2 - 1)) := by
  obtain ⟨C₀, hC₀, hdecay⟩ := exists_surfaceFourier_succ_sharp_decay hd
  obtain ⟨C₁, hC₁, hderiv⟩ := exists_surfaceFourier_succ_sharp_deriv hd
  exact ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩

end

end LeanSpherical.HarmonicAnalysis
