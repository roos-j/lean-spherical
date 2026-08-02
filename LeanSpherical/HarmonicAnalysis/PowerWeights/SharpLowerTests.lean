/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.NecessaryConditions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The sharp lower power-weight obstruction

This file proves the thin-shell necessary condition
`1 - d ≤ α` for a weighted strong-type estimate for a nonempty restricted
spherical maximal operator.  The proof uses a Schwartz function supported in
a thin annulus around one available radius: its maximal function is bounded
below on a small ball, while the weighted volume of the annulus is `O(ε)`.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set
open scoped ENNReal Topology

private theorem ennreal_ofReal_rpow_antitone
    {x y a : ℝ} (ha : a ≤ 0) (hx : 0 < x) (hxy : x ≤ y) :
    (ENNReal.ofReal y) ^ a ≤ (ENNReal.ofReal x) ^ a := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [ENNReal.ofReal_rpow_of_pos hy, ENNReal.ofReal_rpow_of_pos hx]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hx hxy ha)

private theorem exists_small_rpow_gt {q B r : ℝ} (hq : q < 0) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ 4 * ε ≤ r ∧ B < ε ^ q := by
  have hlarge : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), B < ε ^ q :=
    (tendsto_rpow_neg_nhdsGT_zero hq).eventually (Filter.eventually_gt_atTop B)
  have hsmall : Ioo (0 : ℝ) (r / 8) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by linarith)
  have hboth : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), B < ε ^ q ∧ ε ∈ Ioo (0 : ℝ) (r / 8) :=
    hlarge.and hsmall
  rcases hboth.exists with ⟨ε, hB, hε⟩
  refine ⟨ε, hε.1, ?_, hB⟩
  exact le_of_lt <| calc
    4 * ε < 4 * (r / 8) := mul_lt_mul_of_pos_left hε.2 (by norm_num)
    _ = r / 2 := by ring
    _ ≤ r := by linarith

private theorem ennreal_rpow_scale_cancel {ε q : ℝ} {V D : ENNReal} (hε : 0 < ε)
    (h : (ENNReal.ofReal ε) ^ (q + 1) * V ≤ D * ENNReal.ofReal ε) :
    (ENNReal.ofReal ε) ^ q * V ≤ D := by
  apply (ENNReal.mul_le_mul_iff_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.rpow_add q 1
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) ENNReal.ofReal_ne_top,
    ENNReal.rpow_one, mul_assoc, mul_comm, mul_left_comm] using h

private theorem ennreal_lt_of_toReal_div_add_one_mul
    {D V : ENNReal} (hDtop : D ≠ ∞) (hVpos : 0 < V) (hVtop : V ≠ ∞) :
    D < ENNReal.ofReal (D.toReal / V.toReal + 1) * V := by
  have hVrealpos : 0 < V.toReal := ENNReal.toReal_pos hVpos.ne' hVtop
  have hBnonneg : 0 ≤ D.toReal / V.toReal + 1 := by positivity
  apply (ENNReal.toReal_lt_toReal hDtop
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hBnonneg]
  calc
    D.toReal = (D.toReal / V.toReal) * V.toReal := by
      rw [div_mul_cancel₀ _ hVrealpos.ne']
    _ < (D.toReal / V.toReal + 1) * V.toReal := by
      gcongr
      linarith

theorem powerWeightedVolume_euclideanAnnulus_le_linear
    {d : ℕ} (hd : 0 < d) {α r R : ℝ} (hα : α ≤ 0) (hr : 0 < r) :
    powerWeightedVolume d α (euclideanAnnulus d r R) ≤
      (ENNReal.ofReal r) ^ α *
        (ENNReal.ofReal (surfaceMass d) *
          (ENNReal.ofReal R) ^ (d - 1) * ENNReal.ofReal (R - r)) := by
  have hmeas : MeasurableSet (euclideanAnnulus d r R) :=
    measurableSet_closedBall.diff measurableSet_ball
  calc
    powerWeightedVolume d α (euclideanAnnulus d r R) =
        ∫⁻ x in euclideanAnnulus d r R, radialPowerWeight d α x ∂volume := by
      rw [powerWeightedVolume, withDensity_apply _ hmeas]
    _ ≤ ∫⁻ _x in euclideanAnnulus d r R, (ENNReal.ofReal r) ^ α ∂volume := by
      apply setLIntegral_mono measurable_const
      intro x hx
      exact radialPowerWeight_le_of_mem_euclideanAnnulus hα hr hx
    _ = (ENNReal.ofReal r) ^ α * volume (euclideanAnnulus d r R) :=
      setLIntegral_const _ _
    _ ≤ (ENNReal.ofReal r) ^ α *
        (ENNReal.ofReal (surfaceMass d) *
          (ENNReal.ofReal R) ^ (d - 1) * ENNReal.ofReal (R - r)) := by
      apply mul_le_mul_of_nonneg_left
      · exact volume_euclideanAnnulus_le_linear hd hr
      · exact bot_le

theorem powerWeightedVolume_symmetricAnnulus_le_linear
    {d : ℕ} (hd : 0 < d) {α r ε : ℝ} (hα : α ≤ 0)
    (hε : 0 < ε) (hsmall : 4 * ε ≤ r) :
    powerWeightedVolume d α (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε)) ≤
      ((ENNReal.ofReal (r / 2)) ^ α *
        (ENNReal.ofReal (surfaceMass d) *
          (ENNReal.ofReal (3 * r / 2)) ^ (d - 1) * 4)) * ENNReal.ofReal ε := by
  have hinner : 0 < r - 2 * ε := by linarith
  have hinner_half : r / 2 ≤ r - 2 * ε := by linarith
  have houter : r + 2 * ε ≤ 3 * r / 2 := by linarith
  have hbase := powerWeightedVolume_euclideanAnnulus_le_linear
    (R := r + 2 * ε) hd hα hinner
  rw [show (r + 2 * ε) - (r - 2 * ε) = 4 * ε by ring] at hbase
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at hbase
  calc
    powerWeightedVolume d α (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε)) ≤
        (ENNReal.ofReal (r - 2 * ε)) ^ α *
          (ENNReal.ofReal (surfaceMass d) *
            (ENNReal.ofReal (r + 2 * ε)) ^ (d - 1) *
              (4 * ENNReal.ofReal ε)) := by simpa using hbase
    _ ≤ ((ENNReal.ofReal (r / 2)) ^ α *
        (ENNReal.ofReal (surfaceMass d) *
          (ENNReal.ofReal (3 * r / 2)) ^ (d - 1) * 4)) * ENNReal.ofReal ε := by
      have hpow_inner : (ENNReal.ofReal (r - 2 * ε)) ^ α ≤
          (ENNReal.ofReal (r / 2)) ^ α :=
        ennreal_ofReal_rpow_antitone hα (by linarith) hinner_half
      have hpow_outer : (ENNReal.ofReal (r + 2 * ε)) ^ (d - 1) ≤
          (ENNReal.ofReal (3 * r / 2)) ^ (d - 1) :=
        pow_le_pow_left' (ENNReal.ofReal_le_ofReal houter) _
      calc
        (ENNReal.ofReal (r - 2 * ε)) ^ α *
            (ENNReal.ofReal (surfaceMass d) *
              (ENNReal.ofReal (r + 2 * ε)) ^ (d - 1) *
                (4 * ENNReal.ofReal ε)) ≤
            (ENNReal.ofReal (r / 2)) ^ α *
              (ENNReal.ofReal (surfaceMass d) *
                (ENNReal.ofReal (3 * r / 2)) ^ (d - 1) *
                  (4 * ENNReal.ofReal ε)) := by
          gcongr
        _ = ((ENNReal.ofReal (r / 2)) ^ α *
            (ENNReal.ofReal (surfaceMass d) *
              (ENNReal.ofReal (3 * r / 2)) ^ (d - 1) * 4)) * ENNReal.ofReal ε := by
          ring

theorem radialPowerWeight_ball_lower
    {d : ℕ} {α R : ℝ} (hα : α < 0) (hR : 0 < R)
    {x : Euclidean d} (hx : x ∈ Metric.ball (0 : Euclidean d) R) :
    (ENNReal.ofReal R) ^ α ≤ radialPowerWeight d α x := by
  rw [Metric.mem_ball, dist_zero_right] at hx
  unfold radialPowerWeight
  by_cases hxzero : x = 0
  · subst x
    simp [ENNReal.zero_rpow_of_neg hα]
  · have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hxzero
    rw [ENNReal.ofReal_rpow_of_pos hR,
      ENNReal.ofReal_rpow_of_pos hnormpos]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos hnormpos hx.le hα.le)

theorem powerWeightedVolume_ball_lower
    {d : ℕ} {α R : ℝ} (hα : α < 0) (hR : 0 < R) :
    (ENNReal.ofReal R) ^ α * volume (Metric.ball (0 : Euclidean d) R) ≤
      powerWeightedVolume d α (Metric.ball (0 : Euclidean d) R) := by
  rw [powerWeightedVolume, withDensity_apply _ measurableSet_ball]
  calc
    (ENNReal.ofReal R) ^ α * volume (Metric.ball (0 : Euclidean d) R) =
        ∫⁻ _x in Metric.ball (0 : Euclidean d) R, (ENNReal.ofReal R) ^ α :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in Metric.ball (0 : Euclidean d) R, radialPowerWeight d α x := by
      apply setLIntegral_mono (measurable_radialPowerWeight d α)
      intro x hx
      exact radialPowerWeight_ball_lower hα hR hx

theorem volume_ball_scale {d : ℕ} (hd : 0 < d) {ε : ℝ} :
    volume (Metric.ball (0 : Euclidean d) ε) =
      (ENNReal.ofReal ε) ^ d * volume (Metric.ball (0 : Euclidean d) 1) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]

theorem powerWeightedVolume_closedBall_lower_power
    {d : ℕ} (hd : 0 < d) {α ε : ℝ} (hα : α < 0) (hε : 0 < ε) :
    (ENNReal.ofReal ε) ^ (α + (d : ℝ)) *
      volume (Metric.ball (0 : Euclidean d) 1) ≤
      powerWeightedVolume d α (Metric.closedBall (0 : Euclidean d) ε) := by
  calc
    (ENNReal.ofReal ε) ^ (α + (d : ℝ)) *
        volume (Metric.ball (0 : Euclidean d) 1) =
        (ENNReal.ofReal ε) ^ α *
          ((ENNReal.ofReal ε) ^ d * volume (Metric.ball (0 : Euclidean d) 1)) := by
      rw [ENNReal.rpow_add α (d : ℝ)
          (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) ENNReal.ofReal_ne_top,
        ENNReal.rpow_natCast]
      ring
    _ = (ENNReal.ofReal ε) ^ α * volume (Metric.ball (0 : Euclidean d) ε) := by
      congr 1
      exact (volume_ball_scale hd).symm
    _ ≤ powerWeightedVolume d α (Metric.ball (0 : Euclidean d) ε) :=
      powerWeightedVolume_ball_lower hα hε
    _ ≤ powerWeightedVolume d α (Metric.closedBall (0 : Euclidean d) ε) :=
      measure_mono Metric.ball_subset_closedBall

theorem eLpNorm_schwartz_shell_le
    {d : ℕ} {p α r ε : ℝ} (f : SchwartzMap (Euclidean d) ℂ)
    (hf_inner : ∀ y, ‖y‖ ≤ r - 2 * ε → f y = 0)
    (hf_outer : ∀ y, r + 2 * ε ≤ ‖y‖ → f y = 0)
    (hf_bound : ∀ y, ‖f y‖ ≤ 2)
    (hp0 : ENNReal.ofReal p ≠ 0) :
    eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
      2 * (powerWeightedVolume d α
        (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε))) ^
          (1 / (ENNReal.ofReal p).toReal) := by
  let A : Set (Euclidean d) := euclideanAnnulus d (r - 2 * ε) (r + 2 * ε)
  have hAmeas : MeasurableSet A :=
    measurableSet_closedBall.diff measurableSet_ball
  calc
    eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
        eLpNorm (A.indicator (fun _ : Euclidean d => (2 : ℂ)))
          (ENNReal.ofReal p) (powerWeightedVolume d α) := by
      apply eLpNorm_mono
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        simpa using hf_bound x
      · rw [Set.indicator_of_notMem hx]
        by_cases hxinner : x ∈ Metric.ball (0 : Euclidean d) (r - 2 * ε)
        · have hnorm : ‖x‖ ≤ r - 2 * ε := by
            rw [Metric.mem_ball, dist_zero_right] at hxinner
            exact le_of_lt hxinner
          simp [hf_inner x hnorm]
        · have hxouter : x ∉ Metric.closedBall (0 : Euclidean d) (r + 2 * ε) := by
            intro hclosed
            exact hx ⟨hclosed, hxinner⟩
          have hnot : ¬ ‖x‖ ≤ r + 2 * ε := by
            simpa only [Metric.mem_closedBall, dist_zero_right] using hxouter
          have hnorm : r + 2 * ε ≤ ‖x‖ := le_of_lt (lt_of_not_ge hnot)
          simp [hf_outer x hnorm]
    _ = 2 * (powerWeightedVolume d α A) ^
          (1 / (ENNReal.ofReal p).toReal) := by
      rw [eLpNorm_indicator_const hAmeas hp0 ENNReal.ofReal_ne_top]
      norm_num [enorm]
    _ = 2 * (powerWeightedVolume d α
        (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε))) ^
          (1 / (ENNReal.ofReal p).toReal) := by
      rfl

theorem strongType_bound_forces_ball_le_shell
    {d : ℕ} {E : Set ℝ} {p α r ε : ℝ} (hd : 0 < d)
    (hr : r ∈ E) (hppos : 0 < p) (hε : 0 < ε) (hrinner : 0 < r - 2 * ε)
    (C : ℝ)
    (hstrong : ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) (powerWeightedVolume d α) →
        MemLp (restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ))
          (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
          eLpNorm (restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ))
            (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
            ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ)
              (ENNReal.ofReal p) (powerWeightedVolume d α)) :
    powerWeightedVolume d α (Metric.closedBall (0 : Euclidean d) ε) ≤
      (ENNReal.ofReal C * 2) ^ p *
        powerWeightedVolume d α (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε)) := by
  rcases exists_schwartz_shell_test_lower_bound_on_closedBall hd hr hε hrinner with
    ⟨f, hf_shell, hf_inner, hf_outer, hf_bound, hMf⟩
  have hfmem : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume d α) :=
    schwartz_memLp_of_shell_support f hrinner hf_inner hf_outer hf_bound
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hppos)
  have hnorm : eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume d α) ≤
      2 * (powerWeightedVolume d α
        (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε))) ^
          (1 / (ENNReal.ofReal p).toReal) :=
    eLpNorm_schwartz_shell_le f hf_inner hf_outer hf_bound hp0
  have hroot :
      (powerWeightedVolume d α (Metric.closedBall (0 : Euclidean d) ε)) ^
          (1 / (ENNReal.ofReal p).toReal) ≤
        (ENNReal.ofReal C * 2) *
          (powerWeightedVolume d α
            (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε))) ^
            (1 / (ENNReal.ofReal p).toReal) := by
    calc
      (powerWeightedVolume d α (Metric.closedBall (0 : Euclidean d) ε)) ^
          (1 / (ENNReal.ofReal p).toReal) =
          eLpNorm ((Metric.closedBall (0 : Euclidean d) ε).indicator
            (fun _ : Euclidean d => (1 : ENNReal)))
            (ENNReal.ofReal p) (powerWeightedVolume d α) := by
        rw [eLpNorm_indicator_const measurableSet_closedBall hp0 ENNReal.ofReal_ne_top]
        simp
      _ ≤ eLpNorm (restrictedNormalizedSphericalMaximal d E
          (f : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) := by
        apply eLpNorm_mono_enorm
        intro x
        by_cases hx : x ∈ Metric.closedBall (0 : Euclidean d) ε
        · rw [Set.indicator_of_mem hx]
          exact hMf x hx
        · rw [Set.indicator_of_notMem hx]
          simp
      _ ≤ ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ)
          (ENNReal.ofReal p) (powerWeightedVolume d α) := (hstrong f hfmem).2
      _ ≤ ENNReal.ofReal C *
          (2 * (powerWeightedVolume d α
            (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε))) ^
              (1 / (ENNReal.ofReal p).toReal)) := by
        exact mul_le_mul_of_nonneg_left hnorm bot_le
      _ = (ENNReal.ofReal C * 2) *
          (powerWeightedVolume d α
            (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε))) ^
              (1 / (ENNReal.ofReal p).toReal) := by
        ring
  have hq : 1 / (ENNReal.ofReal p).toReal = p⁻¹ := by
    rw [ENNReal.toReal_ofReal hppos.le]
    simp only [one_div]
  rw [hq] at hroot
  have hpow := ENNReal.rpow_le_rpow hroot hppos.le
  calc
    powerWeightedVolume d α (Metric.closedBall (0 : Euclidean d) ε) =
        (powerWeightedVolume d α (Metric.closedBall (0 : Euclidean d) ε) ^ p⁻¹) ^ p :=
      (ENNReal.rpow_inv_rpow hppos.ne' _).symm
    _ ≤ ((ENNReal.ofReal C * 2) *
        powerWeightedVolume d α (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε)) ^ p⁻¹) ^ p := hpow
    _ = (ENNReal.ofReal C * 2) ^ p *
        powerWeightedVolume d α (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hppos.le,
        ENNReal.rpow_inv_rpow hppos.ne']

theorem strongType_forces_radial_scale_bound
    {d : ℕ} {E : Set ℝ} {p α r : ℝ} (hd : 0 < d)
    (hr : r ∈ E) (hppos : 0 < p) (hα : α < 0)
    (hstrong : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p α) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → 4 * ε ≤ r →
      (ENNReal.ofReal ε) ^ (α + (d : ℝ) - 1) *
        volume (Metric.ball (0 : Euclidean d) 1) ≤
        (ENNReal.ofReal C * 2) ^ p *
          ((ENNReal.ofReal (r / 2)) ^ α *
            (ENNReal.ofReal (surfaceMass d) *
              (ENNReal.ofReal (3 * r / 2)) ^ (d - 1) * 4)) := by
  rcases hstrong with ⟨C, hC, hstrong⟩
  refine ⟨C, hC, ?_⟩
  intro ε hε hsmall
  have hrpos : 0 < r := by linarith
  have hrinner : 0 < r - 2 * ε := by linarith
  have hclosed := strongType_bound_forces_ball_le_shell
    hd hr hppos hε hrinner C hstrong
  have hball := powerWeightedVolume_closedBall_lower_power hd hα hε
  have hann := powerWeightedVolume_symmetricAnnulus_le_linear
    hd hα.le hε hsmall
  have hcombined :
      (ENNReal.ofReal ε) ^ (α + (d : ℝ)) *
        volume (Metric.ball (0 : Euclidean d) 1) ≤
        ((ENNReal.ofReal C * 2) ^ p *
          ((ENNReal.ofReal (r / 2)) ^ α *
            (ENNReal.ofReal (surfaceMass d) *
              (ENNReal.ofReal (3 * r / 2)) ^ (d - 1) * 4))) * ENNReal.ofReal ε := by
    calc
      (ENNReal.ofReal ε) ^ (α + (d : ℝ)) *
          volume (Metric.ball (0 : Euclidean d) 1) ≤
          powerWeightedVolume d α (Metric.closedBall (0 : Euclidean d) ε) := hball
      _ ≤ (ENNReal.ofReal C * 2) ^ p *
          powerWeightedVolume d α (euclideanAnnulus d (r - 2 * ε) (r + 2 * ε)) := hclosed
      _ ≤ (ENNReal.ofReal C * 2) ^ p *
          (((ENNReal.ofReal (r / 2)) ^ α *
            (ENNReal.ofReal (surfaceMass d) *
              (ENNReal.ofReal (3 * r / 2)) ^ (d - 1) * 4)) * ENNReal.ofReal ε) := by
        exact mul_le_mul_of_nonneg_left hann bot_le
      _ = ((ENNReal.ofReal C * 2) ^ p *
          ((ENNReal.ofReal (r / 2)) ^ α *
            (ENNReal.ofReal (surfaceMass d) *
              (ENNReal.ofReal (3 * r / 2)) ^ (d - 1) * 4))) * ENNReal.ofReal ε := by
        ring
  apply ennreal_rpow_scale_cancel hε
  have hpow : α + (d : ℝ) = (α + (d : ℝ) - 1) + 1 := by ring
  rw [hpow] at hcombined
  exact hcombined

theorem one_sub_dim_le_alpha_of_restrictedStrongType
    {d : ℕ} {E : Set ℝ} {p α : ℝ} (hd : 0 < d)
    (hE : ∃ r : ℝ, r ∈ E ∧ 0 < r) (hp : 1 ≤ p)
    (hstrong : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p α) :
    1 - (d : ℝ) ≤ α := by
  rcases hE with ⟨r, hr, hrpos⟩
  by_contra hnot
  have hαlt : α < 1 - (d : ℝ) := lt_of_not_ge hnot
  have hdreal : 1 ≤ (d : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hd
  have hαneg : α < 0 := by linarith
  have hppos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rcases strongType_forces_radial_scale_bound hd hr hppos hαneg hstrong with
    ⟨C, hC, hscale⟩
  let V : ENNReal := volume (Metric.ball (0 : Euclidean d) 1)
  let K : ENNReal := (ENNReal.ofReal (r / 2)) ^ α *
    (ENNReal.ofReal (surfaceMass d) *
      (ENNReal.ofReal (3 * r / 2)) ^ (d - 1) * 4)
  let D : ENNReal := (ENNReal.ofReal C * 2) ^ p * K
  have hVpos : 0 < V := by
    dsimp only [V]
    exact Metric.measure_ball_pos volume (0 : Euclidean d) (by norm_num)
  have hVtop : V ≠ ∞ := by
    dsimp only [V]
    exact (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := (1 : ℝ))).ne
  have hDtop : D ≠ ∞ := by
    dsimp only [D, K]
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_ne_zero
      · apply mul_ne_zero
        · exact (ENNReal.ofReal_pos.mpr hC).ne'
        · norm_num
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
    · apply ENNReal.mul_ne_top
      · apply ENNReal.rpow_ne_top_of_ne_zero
        · exact (ENNReal.ofReal_pos.mpr (by linarith : 0 < r / 2)).ne'
        · exact ENNReal.ofReal_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · exact ENNReal.ofReal_ne_top
          · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        · norm_num
  let B : ℝ := D.toReal / V.toReal + 1
  have hBpos : 0 < B := by
    dsimp only [B]
    positivity
  have hDlt : D < ENNReal.ofReal B * V := by
    simpa only [B] using
      ennreal_lt_of_toReal_div_add_one_mul hDtop hVpos hVtop
  let q : ℝ := α + (d : ℝ) - 1
  have hq : q < 0 := by
    dsimp only [q]
    linarith
  rcases exists_small_rpow_gt (q := q) (B := B) (r := r) hq hrpos with
    ⟨ε, hε, hsmall, hB⟩
  have hscaleε := hscale ε hε hsmall
  have hscaleε' : (ENNReal.ofReal ε) ^ q * V ≤ D := by
    simpa only [q, V, D, K] using hscaleε
  have hBenn : ENNReal.ofReal B < (ENNReal.ofReal ε) ^ q := by
    rw [ENNReal.ofReal_rpow_of_pos hε]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans hBpos hB)).mpr hB
  have hlarge : D < (ENNReal.ofReal ε) ^ q * V :=
    hDlt.trans (by
      simpa only [mul_comm] using ENNReal.mul_lt_mul_right hVpos.ne' hVtop hBenn)
  exact (not_lt_of_ge hscaleε' hlarge)

/-- A convenient form of the sharp lower obstruction when every available
radius is positive. -/
theorem one_sub_dim_le_alpha_of_restrictedStrongType_of_nonempty
    {d : ℕ} {E : Set ℝ} {p α : ℝ} (hd : 0 < d) (hE : E.Nonempty)
    (hEpos : E ⊆ Ioi (0 : ℝ)) (hp : 1 ≤ p)
    (hstrong : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p α) :
    1 - (d : ℝ) ≤ α := by
  rcases hE with ⟨r, hr⟩
  exact one_sub_dim_le_alpha_of_restrictedStrongType hd ⟨r, hr, hEpos hr⟩ hp hstrong

end LeanSpherical.HarmonicAnalysis
