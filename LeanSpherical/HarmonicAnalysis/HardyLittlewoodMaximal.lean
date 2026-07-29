/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceCore
import LeanSpherical.HarmonicAnalysis.SphericalAverages
import LeanSpherical.HarmonicAnalysis.InterpolationTail
import LeanSpherical.HarmonicAnalysis.SmoothDyadicPhysical
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Hardy--Littlewood and lowpass spherical maximal estimates
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Set Filter
open scoped Convolution FourierTransform Topology

noncomputable section

def dyadicBallMaximal (d : ℕ) (g : Euclidean d → ℂ) (x : Euclidean d) : ℝ :=
  (⨆ n : ℤ,
    ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
      ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal

/-- The regular, low relative-frequency component of the spherical maximal
operator. -/
def relativeLowpassMaximal (d : ℕ) (φ : SchwartzMap (Euclidean d) ℂ)
    (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) : ℝ :=
  (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
    surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal

/-- The `j`th oscillatory relative-frequency annulus. -/
def relativeBandpassMaximal (d : ℕ) (φ : SchwartzMap (Euclidean d) ℂ) (j : ℕ)
    (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) : ℝ :=
  (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
    surfaceFourier d (-r.1 • ξ) *
      (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
        φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
      𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal

/-- The finite relative-frequency cutoff maximal function. -/
def relativeCutoffMaximal (d : ℕ) (φ : SchwartzMap (Euclidean d) ℂ) (N : ℕ)
    (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) : ℝ :=
  (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
    surfaceFourier d (-r.1 • ξ) *
      φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal

/-- The real-valued normalized spherical maximal function on Schwartz input. -/
def normalizedSphericalMaximalReal (d : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
    (x : Euclidean d) : ℝ :=
  (normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal

private def dyadicBallAverage {d : ℕ} (g : Euclidean d → ℂ)
    (x : Euclidean d) (n : ℤ) : ENNReal :=
  (volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
    ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖

private def dyadicBallLevelSet {d : ℕ} (g : Euclidean d → ℂ)
    (s : ℝ) (N : ℕ) : Set (Euclidean d) :=
  {x | ∃ n : ℤ, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) ∧
    ENNReal.ofReal s < dyadicBallAverage g x n}

private def dyadicBallBadPairs {d : ℕ} (g : Euclidean d → ℂ)
    (s : ℝ) (N : ℕ) : Set (Euclidean d × ℤ) :=
  {a | -(N : ℤ) ≤ a.2 ∧ a.2 ≤ (N : ℤ) ∧
    ENNReal.ofReal s < dyadicBallAverage g a.1 a.2}

private theorem dyadic_ball_average_le_of_norm_le
    {d : ℕ} [NeZero d] (g : Euclidean d → ℂ)
    {a : ℝ} (hga : ∀ x, ‖g x‖ ≤ a) (x : Euclidean d) (n : ℤ) :
    dyadicBallAverage g x n ≤ ENNReal.ofReal a := by
  let r : ℝ := (2 : ℝ) ^ n
  have hr : 0 < r := by
    dsimp only [r]
    positivity
  have hvolpos : 0 < volume (Metric.ball x r) :=
    Metric.measure_ball_pos volume x hr
  have hvoltop : volume (Metric.ball x r) ≠ (⊤ : ENNReal) :=
    measure_ball_lt_top.ne
  have hlin :
      (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤
        ENNReal.ofReal a * volume (Metric.ball x r) := by
    calc
      (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤
          ∫⁻ _y in Metric.ball x r, ENNReal.ofReal a := by
            apply lintegral_mono
            intro y
            exact ENNReal.ofReal_le_ofReal (hga y)
      _ = ENNReal.ofReal a * volume (Metric.ball x r) := by
            rw [lintegral_const]
            simp
  change (volume (Metric.ball x r))⁻¹ *
      (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤ ENNReal.ofReal a
  calc
    (volume (Metric.ball x r))⁻¹ *
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤
        (volume (Metric.ball x r))⁻¹ *
          (ENNReal.ofReal a * volume (Metric.ball x r)) :=
      mul_le_mul_right hlin _
    _ = ENNReal.ofReal a := by
      calc
        (volume (Metric.ball x r))⁻¹ *
            (ENNReal.ofReal a * volume (Metric.ball x r)) =
            ENNReal.ofReal a *
              ((volume (Metric.ball x r))⁻¹ * volume (Metric.ball x r)) := by
                ac_rfl
        _ = ENNReal.ofReal a := by
              rw [ENNReal.inv_mul_cancel hvolpos.ne' hvoltop]
              simp

private theorem dyadic_ball_average_iSup_ne_top
    {d : ℕ} [NeZero d] (g : Euclidean d → ℂ)
    {a : ℝ} (hga : ∀ x, ‖g x‖ ≤ a) (x : Euclidean d) :
    (⨆ n : ℤ, dyadicBallAverage g x n) ≠ ⊤ := by
  have hbound : (⨆ n : ℤ, dyadicBallAverage g x n) ≤ ENNReal.ofReal a :=
    iSup_le fun n => dyadic_ball_average_le_of_norm_le g hga x n
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound

private theorem dyadic_ball_level_set_eq_iUnion
    {d : ℕ} [NeZero d] (g : Euclidean d → ℂ)
    {a : ℝ} (hga : ∀ x, ‖g x‖ ≤ a)
    {s : ℝ} (hs : 0 < s) :
    {x | s < (⨆ n : ℤ, dyadicBallAverage g x n).toReal} =
      ⋃ N : ℕ, dyadicBallLevelSet g s N := by
  ext x
  simp only [dyadicBallLevelSet, mem_setOf_eq, mem_iUnion]
  constructor
  · intro hx
    have hx' : ENNReal.ofReal s < ⨆ n : ℤ, dyadicBallAverage g x n := by
      simpa using
        (ENNReal.ofReal_lt_iff_lt_toReal hs.le
          (dyadic_ball_average_iSup_ne_top g hga x)).2 hx
    rcases lt_iSup_iff.mp hx' with ⟨n, hn⟩
    have hnlo : -((n.natAbs : ℕ) : ℤ) ≤ n := by
      have h := neg_le_neg (Int.le_natAbs (a := -n))
      simpa using h
    exact ⟨n.natAbs, n, hnlo, Int.le_natAbs (a := n), hn⟩
  · rintro ⟨N, n, hnlo, hnhi, hn⟩
    have hx' : s < (⨆ n : ℤ, dyadicBallAverage g x n).toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal hs.le
        (dyadic_ball_average_iSup_ne_top g hga x)).1
          (hn.trans_le (le_iSup (fun n : ℤ => dyadicBallAverage g x n) n))
    exact hx'

private theorem dyadic_ball_level_set_monotone
    {d : ℕ} (g : Euclidean d → ℂ) (s : ℝ) :
    Monotone (dyadicBallLevelSet g s) := by
  intro N M hNM x hx
  change ∃ n : ℤ, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) ∧
    ENNReal.ofReal s < dyadicBallAverage g x n at hx
  change ∃ n : ℤ, -(M : ℤ) ≤ n ∧ n ≤ (M : ℤ) ∧
    ENNReal.ofReal s < dyadicBallAverage g x n
  rcases hx with ⟨n, hnlo, hnhi, hn⟩
  have hNM' : (N : ℤ) ≤ M := by exact_mod_cast hNM
  exact ⟨n, (neg_le_neg hNM').trans hnlo, hnhi.trans hNM', hn⟩

private theorem dyadic_ball_volume_scale
    {d : ℕ} [NeZero d] (x : Euclidean d) (r : ℝ) :
    volume (Metric.ball x (4 * r)) =
      (ENNReal.ofReal (4 : ℝ)) ^ d * volume (Metric.ball x r) := by
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), mul_pow]
  ring

private theorem dyadic_ball_level_set_select
    {d : ℕ} [NeZero d] (g : Euclidean d → ℂ) (s : ℝ) (N : ℕ) :
    ∃ u : Set (Euclidean d × ℤ),
      u ⊆ dyadicBallBadPairs g s N ∧
        u.PairwiseDisjoint (fun a => Metric.ball a.1 ((2 : ℝ) ^ a.2)) ∧
          dyadicBallLevelSet g s N ⊆ ⋃ a ∈ u,
            Metric.ball a.1 (4 * (2 : ℝ) ^ a.2) := by
  obtain ⟨u, hut, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (dyadicBallBadPairs g s N)
      (fun a : Euclidean d × ℤ => a.1) (fun a => (2 : ℝ) ^ a.2)
      ((2 : ℝ) ^ (N : ℤ)) (by
        intro a ha
        change -(N : ℤ) ≤ a.2 ∧ a.2 ≤ (N : ℤ) ∧
          ENNReal.ofReal s < dyadicBallAverage g a.1 a.2 at ha
        exact zpow_le_zpow_right₀ (by norm_num) ha.2.1)
      4 (by norm_num : (3 : ℝ) < 4)
  refine ⟨u, hut, hdisj, ?_⟩
  intro x hx
  change ∃ n : ℤ, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) ∧
    ENNReal.ofReal s < dyadicBallAverage g x n at hx
  rcases hx with ⟨n, hnlo, hnhi, hn⟩
  let a : Euclidean d × ℤ := (x, n)
  have ha : a ∈ dyadicBallBadPairs g s N := by
    dsimp [a, dyadicBallBadPairs]
    exact ⟨hnlo, hnhi, hn⟩
  rcases hcover a ha with ⟨b, hbu, hsub⟩
  refine mem_iUnion.2 ⟨b, ?_⟩
  refine mem_iUnion.2 ⟨hbu, ?_⟩
  exact hsub (Metric.mem_ball_self (zpow_pos (by norm_num) n))

private theorem dyadic_ball_selected_mass_le_lintegral
    {d : ℕ} [NeZero d] (g : Euclidean d → ℂ) (s : ℝ) (N : ℕ)
    {u : Set (Euclidean d × ℤ)}
    (hut : u ⊆ dyadicBallBadPairs g s N)
    (hdisj : u.PairwiseDisjoint (fun a => Metric.ball a.1 ((2 : ℝ) ^ a.2))) :
    ENNReal.ofReal s *
        (∑' a : u, volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2))) ≤
      ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
  have hucount : u.Countable :=
    hdisj.countable_of_isOpen
      (fun _ _ => Metric.isOpen_ball)
      (fun a _ => Metric.nonempty_ball.mpr (zpow_pos (by norm_num) a.2))
  have hselected (a : u) :
      ENNReal.ofReal s * volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)) ≤
        ∫⁻ y in Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2),
          ENNReal.ofReal ‖g y‖ := by
    have ha : a.1 ∈ dyadicBallBadPairs g s N := hut a.2
    change -(N : ℤ) ≤ a.1.2 ∧ a.1.2 ≤ (N : ℤ) ∧
      ENNReal.ofReal s < dyadicBallAverage g a.1.1 a.1.2 at ha
    have havg : ENNReal.ofReal s <
        (volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)))⁻¹ *
          (∫⁻ y in Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2),
            ENNReal.ofReal ‖g y‖) := by
      simpa only [dyadicBallAverage] using ha.2.2
    have hr : 0 < (2 : ℝ) ^ a.1.2 := zpow_pos (by norm_num) _
    have hvolpos : volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)) ≠ 0 :=
      (Metric.measure_ball_pos volume a.1.1 hr).ne'
    have hvoltop : volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)) ≠ ⊤ :=
      measure_ball_lt_top.ne
    calc
      ENNReal.ofReal s * volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)) ≤
          ((volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)))⁻¹ *
            (∫⁻ y in Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2),
              ENNReal.ofReal ‖g y‖)) *
            volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)) := by
              simpa [mul_comm] using
                mul_le_mul_right (le_of_lt havg)
                  (volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)))
      _ = (∫⁻ y in Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2),
            ENNReal.ofReal ‖g y‖) *
            ((volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)))⁻¹ *
              volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2))) := by
              ac_rfl
      _ = ∫⁻ y in Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2),
            ENNReal.ofReal ‖g y‖ := by
              rw [ENNReal.inv_mul_cancel hvolpos hvoltop, mul_one]
  calc
    ENNReal.ofReal s *
        (∑' a : u, volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2))) =
        ∑' a : u, ENNReal.ofReal s *
          volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)) :=
      ENNReal.tsum_mul_left.symm
    _ ≤ ∑' a : u, ∫⁻ y in Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2),
          ENNReal.ofReal ‖g y‖ :=
      ENNReal.tsum_le_tsum hselected
    _ = ∫⁻ x in ⋃ a ∈ u, Metric.ball a.1 ((2 : ℝ) ^ a.2),
          ENNReal.ofReal ‖g x‖ := by
      symm
      exact lintegral_biUnion hucount
        (fun _ _ => measurableSet_ball) hdisj
        (fun x => ENNReal.ofReal ‖g x‖)
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
      simpa using
        (lintegral_mono_set (μ := volume)
          (f := fun x : Euclidean d => ENNReal.ofReal ‖g x‖)
          (subset_univ (⋃ a ∈ u, Metric.ball a.1 ((2 : ℝ) ^ a.2))))

private theorem dyadic_ball_level_set_weak_one
    {d : ℕ} [NeZero d] (g : Euclidean d → ℂ) (s : ℝ) (N : ℕ) :
    ENNReal.ofReal s * volume (dyadicBallLevelSet g s N) ≤
      (ENNReal.ofReal (4 : ℝ)) ^ d *
        ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
  obtain ⟨u, hut, hdisj, hcover⟩ :=
    dyadic_ball_level_set_select g s N
  have hucount : u.Countable :=
    hdisj.countable_of_isOpen
      (fun _ _ => Metric.isOpen_ball)
      (fun a _ => Metric.nonempty_ball.mpr (zpow_pos (by norm_num) a.2))
  have hmeasurecover :
      volume (dyadicBallLevelSet g s N) ≤ ∑' a : u,
        volume (Metric.ball a.1.1 (4 * (2 : ℝ) ^ a.1.2)) := by
    calc
      volume (dyadicBallLevelSet g s N) ≤ volume (⋃ a ∈ u,
          Metric.ball a.1 (4 * (2 : ℝ) ^ a.2)) :=
        measure_mono hcover
      _ ≤ ∑' a : u, volume (Metric.ball a.1.1 (4 * (2 : ℝ) ^ a.1.2)) :=
        measure_biUnion_le volume hucount _
  have hsum := dyadic_ball_selected_mass_le_lintegral g s N hut hdisj
  have hsumscale :
      (∑' a : u, volume (Metric.ball a.1.1 (4 * (2 : ℝ) ^ a.1.2))) =
        (ENNReal.ofReal (4 : ℝ)) ^ d *
          (∑' a : u, volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2))) := by
    simp_rw [dyadic_ball_volume_scale]
    exact ENNReal.tsum_mul_left
  calc
    ENNReal.ofReal s * volume (dyadicBallLevelSet g s N) ≤
        ENNReal.ofReal s *
          (∑' a : u, volume (Metric.ball a.1.1 (4 * (2 : ℝ) ^ a.1.2))) :=
      mul_le_mul_right hmeasurecover _
    _ = (ENNReal.ofReal (4 : ℝ)) ^ d *
        (ENNReal.ofReal s *
          (∑' a : u, volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)))) := by
      rw [hsumscale]
      ring
    _ ≤ (ENNReal.ofReal (4 : ℝ)) ^ d *
        (∫⁻ x, ENNReal.ofReal ‖g x‖) :=
      mul_le_mul_right hsum _

/-- The centered dyadic-ball maximal function satisfies the literal weak
`(1,1)` estimate obtained by Vitali disjoint-ball selection. -/
theorem dyadic_ball_maximal_weak_one
    {d : ℕ} (hd : 0 < d)
    (g : Euclidean d → ℂ) (_hg : Measurable g)
    {a : ℝ} (_ha : 0 ≤ a) (hga : ∀ x, ‖g x‖ ≤ a)
    {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal s * volume {x | s <
      (⨆ n : ℤ,
        ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
          ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal} ≤
      (ENNReal.ofReal (4 : ℝ)) ^ d *
        ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  change ENNReal.ofReal s * volume
      {x | s < (⨆ n : ℤ, dyadicBallAverage g x n).toReal} ≤
    (ENNReal.ofReal (4 : ℝ)) ^ d * ∫⁻ x, ENNReal.ofReal ‖g x‖
  rw [dyadic_ball_level_set_eq_iUnion g hga hs]
  rw [(dyadic_ball_level_set_monotone g s).measure_iUnion]
  rw [ENNReal.mul_iSup _ _]
  exact iSup_le (dyadic_ball_level_set_weak_one g s)

/-- The literal relative-frequency spherical maximal piece has the weak
`(1,1)` endpoint supplied by its physical-space shell bound. -/
theorem exists_iSup_relative_surface_scaled_schwartz_multiplier_weak_one
    {d : Nat} (hd : 0 < d) (ψ : SchwartzMap (Euclidean d) ℂ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (j : Nat) (f : SchwartzMap (Euclidean d) ℂ)
      {a : ℝ}, 0 ≤ a → (∀ x, ‖f x‖ ≤ a) →
      ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * volume {x | s <
        (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal} ≤
        (ENNReal.ofReal
          (D * (2 : ℝ) ^ j *
            (volume (Metric.ball (0 : Euclidean d) 1)).toReal) *
          (ENNReal.ofReal (4 : ℝ)) ^ d) *
          ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  obtain ⟨D, hD, hpoint⟩ :=
    exists_iSup_norm_fourierInv_relative_surface_scaled_schwartz_multiplier_le_dyadic_average_sup
      hd ψ
  refine ⟨D, hD, ?_⟩
  intro j f a ha hfa s hs
  let H : (Euclidean d → ℂ) → Euclidean d → ℝ := fun g x =>
    (⨆ n : ℤ,
      ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
        ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal
  let V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal
  have hV : 0 < V := by
    dsimp [V]
    exact ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) (by norm_num)))
      (ne_of_lt measure_ball_lt_top)
  let A : ℝ := D * (2 : ℝ) ^ j * V
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (mul_pos hD (pow_pos (by norm_num) _)) hV
  have hweak : ∀ {t : ℝ}, 0 < t →
      ENNReal.ofReal t * volume {x | t < H (f : Euclidean d → ℂ) x} ≤
        (ENNReal.ofReal (4 : ℝ)) ^ d *
          ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
    intro t ht
    simpa only [H] using
      (dyadic_ball_maximal_weak_one hd (f : Euclidean d → ℂ)
        f.continuous.measurable ha hfa ht)
  have hscaled :
      ENNReal.ofReal s * volume {x | s < A * H (f : Euclidean d → ℂ) x} ≤
        (ENNReal.ofReal A * (ENNReal.ofReal (4 : ℝ)) ^ d) *
          ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
    exact marcinkiewicz_scale_weak_one H ((ENNReal.ofReal (4 : ℝ)) ^ d)
      (∫⁻ x, ENNReal.ofReal ‖f x‖) (f : Euclidean d → ℂ) hweak A s hA hs
  have hpoint' (x : Euclidean d) :
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) *
          ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal ≤
        A * H (f : Euclidean d → ℂ) x := by
    have h := hpoint j f x
    change _ ≤ A * H (f : Euclidean d → ℂ) x
    dsimp [A, V, H]
    convert h using 1 <;> ring
  have hset :
      {x | s <
        (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal} ⊆
        {x | s < A * H (f : Euclidean d → ℂ) x} := by
    intro x hx
    exact hx.trans_le (hpoint' x)
  calc
    ENNReal.ofReal s * volume {x | s <
        (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal} ≤
        ENNReal.ofReal s * volume {x | s < A * H (f : Euclidean d → ℂ) x} :=
      mul_le_mul_of_nonneg_left (measure_mono hset) (by positivity)
    _ ≤ (ENNReal.ofReal A * (ENNReal.ofReal (4 : ℝ)) ^ d) *
          ∫⁻ x, ENNReal.ofReal ‖f x‖ := hscaled
    _ = (ENNReal.ofReal
          (D * (2 : ℝ) ^ j *
            (volume (Metric.ball (0 : Euclidean d) 1)).toReal) *
          (ENNReal.ofReal (4 : ℝ)) ^ d) *
          ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
      dsimp [A, V]

/- The raw `ENNReal` dyadic-ball supremum is finite on bounded inputs. -/
private theorem dyadic_ball_maximal_raw_le_of_norm_le
    {d : ℕ} (g : Euclidean d → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hg : ∀ y, ‖g y‖ ≤ a) (x : Euclidean d) :
    (⨆ n : ℤ,
      ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
        ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)) ≤
      ENNReal.ofReal a := by
  apply iSup_le
  intro n
  let r : ℝ := (2 : ℝ) ^ n
  have hr : 0 < r := by
    dsimp only [r]
    positivity
  have hvolpos : 0 < volume (Metric.ball x r) :=
    Metric.measure_ball_pos volume x hr
  have hvoltop : volume (Metric.ball x r) ≠ (⊤ : ENNReal) :=
    measure_ball_lt_top.ne
  have hlin :
      (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤
        ENNReal.ofReal a * volume (Metric.ball x r) := by
    calc
      (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤
          ∫⁻ _y in Metric.ball x r, ENNReal.ofReal a := by
            apply lintegral_mono
            intro y
            exact ENNReal.ofReal_le_ofReal (hg y)
      _ = ENNReal.ofReal a * volume (Metric.ball x r) := by
            rw [lintegral_const]
            simp
  change (volume (Metric.ball x r))⁻¹ *
    (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤ ENNReal.ofReal a
  calc
    (volume (Metric.ball x r))⁻¹ *
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤
        (volume (Metric.ball x r))⁻¹ *
          (ENNReal.ofReal a * volume (Metric.ball x r)) :=
      mul_le_mul_right hlin _
    _ = ENNReal.ofReal a := by
      calc
        (volume (Metric.ball x r))⁻¹ *
            (ENNReal.ofReal a * volume (Metric.ball x r)) =
            ENNReal.ofReal a *
              ((volume (Metric.ball x r))⁻¹ * volume (Metric.ball x r)) := by
                ac_rfl
        _ = ENNReal.ofReal a := by
              rw [ENNReal.inv_mul_cancel hvolpos.ne' hvoltop]
              simp

/- A bounded input stays bounded under every dyadic-ball average. -/
private theorem dyadic_ball_maximal_top_bound
    {d : ℕ} (g : Euclidean d → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hg : ∀ y, ‖g y‖ ≤ a) :
    ∀ x : Euclidean d, dyadicBallMaximal d g x ≤ a := by
  intro x
  have hsup :
      (⨆ n : ℤ,
        ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
          ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)) ≤
        ENNReal.ofReal a := by
    apply iSup_le
    intro n
    let r : ℝ := (2 : ℝ) ^ n
    have hr : 0 < r := by
      dsimp only [r]
      positivity
    have hvolpos : 0 < volume (Metric.ball x r) :=
      Metric.measure_ball_pos volume x hr
    have hvoltop : volume (Metric.ball x r) ≠ (⊤ : ENNReal) :=
      measure_ball_lt_top.ne
    have hlin :
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤
          ENNReal.ofReal a * volume (Metric.ball x r) := by
      calc
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤
            ∫⁻ _y in Metric.ball x r, ENNReal.ofReal a := by
              apply lintegral_mono
              intro y
              exact ENNReal.ofReal_le_ofReal (hg y)
        _ = ENNReal.ofReal a * volume (Metric.ball x r) := by
              rw [lintegral_const]
              simp
    change (volume (Metric.ball x r))⁻¹ *
      (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤ ENNReal.ofReal a
    calc
      (volume (Metric.ball x r))⁻¹ *
          (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) ≤
          (volume (Metric.ball x r))⁻¹ *
            (ENNReal.ofReal a * volume (Metric.ball x r)) :=
        mul_le_mul_right hlin _
      _ = ENNReal.ofReal a := by
        calc
          (volume (Metric.ball x r))⁻¹ *
              (ENNReal.ofReal a * volume (Metric.ball x r)) =
              ENNReal.ofReal a *
                ((volume (Metric.ball x r))⁻¹ * volume (Metric.ball x r)) := by
                  ac_rfl
          _ = ENNReal.ofReal a := by
                rw [ENNReal.inv_mul_cancel hvolpos.ne' hvoltop]
                simp
  change (⨆ n : ℤ,
      ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
        ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal ≤ a
  calc
    (⨆ n : ℤ,
        ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
          ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal ≤
        (ENNReal.ofReal a).toReal :=
      (ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsup) ENNReal.ofReal_ne_top).mpr hsup
    _ = a := ENNReal.toReal_ofReal ha

/- The finite dyadic-ball averages are subadditive, and boundedness keeps
their `toReal` suprema finite. -/
private theorem dyadic_ball_maximal_subadditive
    {d : ℕ} (g h : Euclidean d → ℂ) (hgm : Measurable g) (_hhm : Measurable h)
    (hg_bounded : ∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖g x‖ ≤ a)
    (hh_bounded : ∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖h x‖ ≤ a) :
    ∀ x, dyadicBallMaximal d (g + h) x ≤
      dyadicBallMaximal d g x + dyadicBallMaximal d h x := by
  rintro x
  obtain ⟨a, ha, hga⟩ := hg_bounded
  obtain ⟨b, hb, hhb⟩ := hh_bounded
  let SG : ENNReal := (⨆ n : ℤ,
    ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
      ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖))
  let SH : ENNReal := (⨆ n : ℤ,
    ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
      ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖h y‖))
  let SGH : ENNReal := (⨆ n : ℤ,
    ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
      ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖(g + h) y‖))
  have hSG : SG ≤ ENNReal.ofReal a :=
    dyadic_ball_maximal_raw_le_of_norm_le g a ha hga x
  have hSH : SH ≤ ENNReal.ofReal b :=
    dyadic_ball_maximal_raw_le_of_norm_le h b hb hhb x
  have hSGH : SGH ≤ ENNReal.ofReal (a + b) := by
    apply dyadic_ball_maximal_raw_le_of_norm_le (g + h) (a + b) (add_nonneg ha hb)
    intro y
    exact (norm_add_le _ _).trans (add_le_add (hga y) (hhb y))
  have havgadd (n : ℤ) :
      ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
        ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y + h y‖) ≤
      ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
        ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖) +
      ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
        ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖h y‖) := by
    let r : ℝ := (2 : ℝ) ^ n
    change (volume (Metric.ball x r))⁻¹ *
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y + h y‖) ≤
      (volume (Metric.ball x r))⁻¹ *
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) +
      (volume (Metric.ball x r))⁻¹ *
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖h y‖)
    have hlin :
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y + h y‖) ≤
          (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) +
            (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖h y‖) := by
      calc
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y + h y‖) ≤
            ∫⁻ y in Metric.ball x r,
              ENNReal.ofReal ‖g y‖ + ENNReal.ofReal ‖h y‖ := by
                apply lintegral_mono
                intro y
                simpa only [← ENNReal.ofReal_add (norm_nonneg (g y))
                  (norm_nonneg (h y))] using
                  ENNReal.ofReal_le_ofReal (norm_add_le (g y) (h y))
        _ = (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) +
            (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖h y‖) := by
              apply lintegral_add_left
              exact hgm.norm.ennreal_ofReal
    calc
      (volume (Metric.ball x r))⁻¹ *
          (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y + h y‖) ≤
          (volume (Metric.ball x r))⁻¹ *
            ((∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) +
              (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖h y‖)) :=
        mul_le_mul_right hlin _
      _ = (volume (Metric.ball x r))⁻¹ *
          (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖) +
          (volume (Metric.ball x r))⁻¹ *
          (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖h y‖) := by
            rw [mul_add]
  have hsub : SGH ≤ SG + SH := by
    apply iSup_le
    intro n
    change ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
      ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y + h y‖) ≤ SG + SH
    calc
      ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
          ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y + h y‖) ≤
          ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
            ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖) +
          ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
            ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖h y‖) := havgadd n
      _ ≤ SG + SH := by
        apply add_le_add
        · exact le_iSup (fun n : ℤ =>
            ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
              ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)) n
        · exact le_iSup (fun n : ℤ =>
            ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
              ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖h y‖)) n
  have hSGtop : SG ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSG
  have hSHtop : SH ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSH
  have hSGHtop : SGH ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSGH
  change SGH.toReal ≤ SG.toReal + SH.toReal
  calc
    SGH.toReal ≤ (SG + SH).toReal :=
      (ENNReal.toReal_le_toReal hSGHtop
        (ENNReal.add_ne_top.mpr ⟨hSGtop, hSHtop⟩)).mpr hsub
    _ = SG.toReal + SH.toReal := ENNReal.toReal_add hSGtop hSHtop

/- Countability of the dyadic radii makes the ball maximal function
measurable for measurable inputs. -/
private theorem dyadic_ball_maximal_aemeasurable
    {d : ℕ} (hd : 0 < d) (g : Euclidean d → ℂ) (hg : Measurable g) :
    AEMeasurable (dyadicBallMaximal d g) volume := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hA (n : ℤ) : Measurable (fun x : Euclidean d =>
      ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
        ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)) := by
    let r : ℝ := (2 : ℝ) ^ n
    let S : Set (Euclidean d × Euclidean d) := {q | dist q.2 q.1 < r}
    have hS : MeasurableSet S := by
      dsimp only [S]
      exact measurableSet_lt (continuous_dist.comp
        (continuous_snd.prodMk continuous_fst)).measurable measurable_const
    let F : Euclidean d × Euclidean d → ENNReal := fun q =>
      S.indicator (fun q => ENNReal.ofReal ‖g q.2‖) q
    have hF : Measurable F := by
      dsimp only [F]
      exact (hg.norm.ennreal_ofReal.comp measurable_snd).indicator hS
    have hI : Measurable (fun x : Euclidean d => ∫⁻ y : Euclidean d, F (x, y)) :=
      hF.lintegral_prod_right
    have hI' : (fun x : Euclidean d => ∫⁻ y : Euclidean d, F (x, y)) =
        fun x : Euclidean d => ∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖ := by
      funext x
      rw [show (fun y : Euclidean d => F (x, y)) =
          (Metric.ball x r).indicator (fun y => ENNReal.ofReal ‖g y‖) by
        funext y
        dsimp only [F, S, Set.indicator_apply]
        by_cases hy : dist y x < r <;> simp [hy]]
      rw [lintegral_indicator (measurableSet_ball)]
    have hvol (x : Euclidean d) : volume (Metric.ball x r) =
        volume (Metric.ball (0 : Euclidean d) r) := by
      rw [InnerProductSpace.volume_ball, InnerProductSpace.volume_ball]
    have hmain : (fun x : Euclidean d =>
        ((volume (Metric.ball x r))⁻¹ *
          ∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖)) =
        fun x : Euclidean d => (volume (Metric.ball (0 : Euclidean d) r))⁻¹ *
          (∫⁻ y : Euclidean d, F (x, y)) := by
      funext x
      rw [hvol x, ← congrFun hI' x]
    change Measurable (fun x : Euclidean d =>
        ((volume (Metric.ball x r))⁻¹ *
          ∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖g y‖))
    rw [hmain]
    exact measurable_const.mul hI
  have hsup : Measurable (fun x : Euclidean d =>
      ⨆ n : ℤ,
        ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
          ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)) := by
    exact Measurable.iSup hA
  exact (ENNReal.measurable_toReal.comp hsup).aemeasurable

/- The dimensional constant in the physical-space Schwartz-kernel estimate. -/
private def lowpassKernelConstant {d : ℕ} (χ : SchwartzMap (Euclidean d) ℂ) : ℝ :=
  2 * ((SchwartzMap.seminorm ℂ 0 0 (𝓕⁻ χ : SchwartzMap (Euclidean d) ℂ) +
    SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ χ : SchwartzMap (Euclidean d) ℂ)) *
    (volume (Metric.ball (0 : Euclidean d) 1)).toReal * (2 : ℝ) ^ (2 * d))

/- At a fixed radius, the compact lowpass multiplier is bounded by a
dyadic-ball maximal function. -/
private theorem relative_lowpass_fixed_radius_majorant
    {d : ℕ} (φ χ : SchwartzMap (Euclidean d) ℂ)
    (hχ : ∀ ξ, χ ξ = φ ξ * surfaceFourier d (-ξ))
    (f : SchwartzMap (Euclidean d) ℂ) (r : Ioi (0 : ℝ)) (x : Euclidean d) :
    ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
      (lowpassKernelConstant χ + 1) *
        dyadicBallMaximal d (f : Euclidean d → ℂ) x := by
  let kernel : SchwartzMap (Euclidean d) ℂ := 𝓕⁻ χ
  have hmult :
      𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
          𝓕 (f : Euclidean d → ℂ) ξ) x =
        𝓕⁻ (fun ξ : Euclidean d =>
          χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x := by
    apply congrArg (fun g : Euclidean d → ℂ => 𝓕⁻ g x)
    funext ξ
    rw [hχ]
    rw [show (-(r.1) : ℝ) • ξ = -(r.1 • ξ) by rw [neg_smul]]
    ring
  have hphysical :
      𝓕⁻ (fun ξ : Euclidean d =>
        χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x =
        ((fun y : Euclidean d => (r.1⁻¹) ^ d • kernel (r.1⁻¹ • y))
          ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (f : Euclidean d → ℂ)) x := by
    simpa [kernel] using fourierInv_relative_lowpass_eq_convolution χ f r.2 x
  have hconv := norm_scaled_schwartz_convolution_le_dyadic_average_sup
    kernel f r.2 x
  have hC : 0 ≤ lowpassKernelConstant χ := by
    dsimp only [lowpassKernelConstant]
    positivity
  have hH : 0 ≤ dyadicBallMaximal d (f : Euclidean d → ℂ) x := ENNReal.toReal_nonneg
  calc
    ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ =
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖ := congrArg norm hmult
    _ = ‖((fun y : Euclidean d => (r.1⁻¹) ^ d • kernel (r.1⁻¹ • y))
        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (f : Euclidean d → ℂ)) x‖ := congrArg norm hphysical
    _ ≤ 2 * ((SchwartzMap.seminorm ℂ 0 0 kernel +
        SchwartzMap.seminorm ℂ (d + 2) 0 kernel) *
        (dyadicBallMaximal d (f : Euclidean d → ℂ) x *
          (volume (Metric.ball (0 : Euclidean d) 1)).toReal) *
        (2 : ℝ) ^ (2 * d)) := by
          simpa only [dyadicBallMaximal] using hconv
    _ = lowpassKernelConstant χ * dyadicBallMaximal d (f : Euclidean d → ℂ) x := by
      dsimp only [lowpassKernelConstant, kernel]
      ring
    _ ≤ (lowpassKernelConstant χ + 1) *
        dyadicBallMaximal d (f : Euclidean d → ℂ) x := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact hH

/- A compact relative-frequency multiplier has a Schwartz kernel.  The
standard dilate estimate controls all of its radii by dyadic ball averages. -/
private theorem relative_lowpass_kernel_majorant
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d),
      relativeLowpassMaximal d φ f x ≤
        K * dyadicBallMaximal d (f : Euclidean d → ℂ) x := by
  have hφcompact : HasCompactSupport (φ : Euclidean d → ℂ) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) 2)
    intro ξ hξ
    apply hφzero ξ
    have hlt : 2 < ‖ξ‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hξ
      exact lt_of_not_ge hξ
    exact hlt.le
  obtain ⟨χ, hχ⟩ :=
    exists_schwartz_compactSupport_mul_surfaceFourier φ hφcompact 1
  have hχ' (ξ : Euclidean d) : χ ξ = φ ξ * surfaceFourier d (-ξ) := by
    simpa using hχ ξ
  let K : ℝ := lowpassKernelConstant χ + 1
  have hC : 0 ≤ lowpassKernelConstant χ := by
    dsimp only [lowpassKernelConstant]
    positivity
  have hK : 0 < K := by
    dsimp only [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro f x
  have hpoint (r : Ioi (0 : ℝ)) :
      ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
        K * dyadicBallMaximal d (f : Euclidean d → ℂ) x := by
    dsimp only [K]
    exact relative_lowpass_fixed_radius_majorant φ χ hχ' f r x
  have hsup :
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖) ≤
        ENNReal.ofReal (K * dyadicBallMaximal d (f : Euclidean d → ℂ) x) := by
    apply iSup_le
    intro r
    exact ENNReal.ofReal_le_ofReal (hpoint r)
  calc
    relativeLowpassMaximal d φ f x ≤
        (ENNReal.ofReal (K * dyadicBallMaximal d (f : Euclidean d → ℂ) x)).toReal :=
      (ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsup)
        ENNReal.ofReal_ne_top).2 hsup
    _ = K * dyadicBallMaximal d (f : Euclidean d → ℂ) x :=
      ENNReal.toReal_ofReal (mul_nonneg hK.le ENNReal.toReal_nonneg)

/- Marcinkiewicz interpolation applied to the dyadic-ball maximal function,
kept at the lower-integral level for a later real-integral conversion. -/
private theorem dyadic_ball_maximal_lintegral_bound
    {d : ℕ} (hd : 0 < d) {p : ℝ} (hp : 1 < p)
    (f : SchwartzMap (Euclidean d) ℂ) :
    (∫⁻ x : Euclidean d,
      ENNReal.ofReal (dyadicBallMaximal d (f : Euclidean d → ℂ) x ^ p)) ≤
      ENNReal.ofReal p *
        (2 * (ENNReal.ofReal (4 : ℝ)) ^ d * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p) := by
  let D : ENNReal := (ENNReal.ofReal (4 : ℝ)) ^ d
  have hnonneg : ∀ (g : Euclidean d → ℂ) (x : Euclidean d),
      0 ≤ dyadicBallMaximal d g x := fun _ _ => ENNReal.toReal_nonneg
  have hsub : ∀ (g h : Euclidean d → ℂ), Measurable g → Measurable h →
      (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖g x‖ ≤ a) →
      (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖h x‖ ≤ a) →
      ∀ x, dyadicBallMaximal d (g + h) x ≤
        dyadicBallMaximal d g x + dyadicBallMaximal d h x := by
    intro g h hgm hhm hgb hhb x
    exact dyadic_ball_maximal_subadditive g h hgm hhm hgb hhb x
  have hweak : ∀ (g : Euclidean d → ℂ), Measurable g →
      (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖g x‖ ≤ a) → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * volume {x | s < dyadicBallMaximal d g x} ≤
        D * ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
    intro g hg ⟨a, ha, hga⟩ s hs
    simpa only [D, dyadicBallMaximal] using
      dyadic_ball_maximal_weak_one hd g hg ha hga hs
  have htop : ∀ (g : Euclidean d → ℂ) (a : ℝ), 0 ≤ a →
      (∀ x, ‖g x‖ ≤ a) → ∀ x, dyadicBallMaximal d g x ≤ a := by
    intro g a ha hga x
    exact dyadic_ball_maximal_top_bound g a ha hga x
  have hfbounded : ∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖(f : Euclidean d → ℂ) x‖ ≤ a := by
    refine ⟨‖f.toBoundedContinuousFunction‖, norm_nonneg _, ?_⟩
    intro x
    change ‖f.toBoundedContinuousFunction x‖ ≤ ‖f.toBoundedContinuousFunction‖
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  simpa only [D] using
    (marcinkiewicz_weak_one_top (dyadicBallMaximal d) hnonneg hsub D hweak htop
      hp (f : Euclidean d → ℂ) f.continuous.measurable hfbounded
      (dyadic_ball_maximal_aemeasurable hd (f : Euclidean d → ℂ)
        f.continuous.measurable))

/-- A Schwartz input has matching real and extended-real `p`-moment
integrals. -/
private theorem schwartz_lintegral_rpow_eq_ofReal_integral
    {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ) {p : ℝ} (hp0 : 0 < p) :
    (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p) =
      ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ p) := by
  have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfMem : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume :=
    f.memLp (ENNReal.ofReal p) volume
  have hfPowInt : Integrable (fun x : Euclidean d => ‖f x‖ ^ p) volume := by
    have h := hfMem.integrable_norm_rpow hpEN0 hpENT
    simpa only [ENNReal.toReal_ofReal hp0.le] using h
  calc
    (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p) =
        ∫⁻ x : Euclidean d, ENNReal.ofReal (‖f x‖ ^ p) := by
          apply lintegral_congr
          intro x
          exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
    _ = ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ p) :=
      (ofReal_integral_eq_lintegral_ofReal hfPowInt
        (Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (norm_nonneg _) p)).symm

/-- Convert a finite lower-integral estimate for dyadic ball averages into
the real strong-type form. -/
private theorem dyadic_ball_maximal_real_bound_of_lintegral
    {d : ℕ} {p : ℝ} (hd : 0 < d) (hp0 : 0 < p)
    (E : ENNReal) (hEtop : E < ⊤)
    (f : SchwartzMap (Euclidean d) ℂ)
    (hlin : (∫⁻ x : Euclidean d,
      ENNReal.ofReal (dyadicBallMaximal d (f : Euclidean d → ℂ) x ^ p)) ≤
        E * ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p) :
    MemLp (dyadicBallMaximal d (f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (dyadicBallMaximal d (f : Euclidean d → ℂ) x) ^ p) ≤
        (E.toReal + 1) * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  have hpNN : 0 ≤ p := hp0.le
  have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinput : (∫⁻ x : Euclidean d,
      (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p) < ⊤ := by
    rw [schwartz_lintegral_rpow_eq_ofReal_integral f hp0]
    exact ENNReal.ofReal_lt_top
  have hleft : (∫⁻ x : Euclidean d,
      ENNReal.ofReal (dyadicBallMaximal d (f : Euclidean d → ℂ) x ^ p)) < ⊤ :=
    hlin.trans_lt (ENNReal.mul_lt_top hEtop hinput)
  have hMem : MemLp (dyadicBallMaximal d (f : Euclidean d → ℂ))
      (ENNReal.ofReal p) volume :=
    memLp_of_lintegral_ofReal_rpow_lt_top
      (dyadicBallMaximal d (f : Euclidean d → ℂ))
      (dyadic_ball_maximal_aemeasurable hd (f : Euclidean d → ℂ)
        f.continuous.measurable)
      (fun _ => ENNReal.toReal_nonneg) hp0 hleft
  have hHnonneg (x : Euclidean d) :
      0 ≤ dyadicBallMaximal d (f : Euclidean d → ℂ) x := ENNReal.toReal_nonneg
  refine ⟨hMem, ?_⟩
  have hHPowInt : Integrable (fun x : Euclidean d =>
      (dyadicBallMaximal d (f : Euclidean d → ℂ) x) ^ p) volume := by
    have h := hMem.integrable_norm_rpow hpEN0 hpENT
    convert h using 1
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hHnonneg x),
      ENNReal.toReal_ofReal hpNN]
  have hleft_eq : (∫ x : Euclidean d,
      (dyadicBallMaximal d (f : Euclidean d → ℂ) x) ^ p) =
        (∫⁻ x : Euclidean d,
          ENNReal.ofReal (dyadicBallMaximal d (f : Euclidean d → ℂ) x ^ p)).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ =>
        Real.rpow_nonneg (hHnonneg _) p)
      hHPowInt.aestronglyMeasurable
  have hinput_eq : (∫⁻ x : Euclidean d,
      (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p).toReal =
        ∫ x : Euclidean d, ‖f x‖ ^ p := by
    rw [schwartz_lintegral_rpow_eq_ofReal_integral f hp0]
    exact ENNReal.toReal_ofReal (integral_nonneg fun _ =>
      Real.rpow_nonneg (norm_nonneg _) p)
  have hprodtop : E * (∫⁻ x : Euclidean d,
      (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p) < ⊤ :=
    ENNReal.mul_lt_top hEtop hinput
  rw [hleft_eq]
  calc
    (∫⁻ x : Euclidean d,
        ENNReal.ofReal (dyadicBallMaximal d (f : Euclidean d → ℂ) x ^ p)).toReal ≤
        (E * ∫⁻ x : Euclidean d,
          (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p).toReal :=
      (ENNReal.toReal_le_toReal hleft.ne hprodtop.ne).mpr hlin
    _ = E.toReal * (∫⁻ x : Euclidean d,
          (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p).toReal :=
      ENNReal.toReal_mul
    _ = E.toReal * ∫ x : Euclidean d, ‖f x‖ ^ p := by rw [hinput_eq]
    _ ≤ (E.toReal + 1) * ∫ x : Euclidean d, ‖f x‖ ^ p := by
      apply mul_le_mul_of_nonneg_right
      · linarith [ENNReal.toReal_nonneg (a := E)]
      · exact integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) p

/-- The dyadic ball maximal operator is of strong type `(p,p)` above one. -/
private theorem dyadic_ball_maximal_strong_type
    {d : ℕ} (hd : 3 ≤ d) {p : ℝ}
    (hp : (d : ℝ) / ((d : ℝ) - 1) < p) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (dyadicBallMaximal d (f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (dyadicBallMaximal d (f : Euclidean d → ℂ) x) ^ p) ≤
        B * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  have hd0 : 0 < d := by omega
  have hdreal : (2 : ℝ) < d := by
    exact_mod_cast (show 2 < d by omega)
  have hdenom : 0 < (d : ℝ) - 1 := by linarith
  have hcritical : 1 < (d : ℝ) / ((d : ℝ) - 1) := by
    rw [lt_div_iff₀ hdenom]
    nlinarith
  have hpone : 1 < p := hcritical.trans hp
  let E : ENNReal := ENNReal.ofReal p *
    (2 * (ENNReal.ofReal (4 : ℝ)) ^ d * (ENNReal.ofReal (p - 1))⁻¹ *
      (ENNReal.ofReal (2 : ℝ)) ^ (p - 1))
  have hinv : (ENNReal.ofReal (p - 1))⁻¹ < ⊤ := by
    apply ENNReal.inv_lt_top.mpr
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hpow : (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) < ⊤ := by
    apply ENNReal.rpow_lt_top_of_nonneg
    · linarith
    · exact ENNReal.ofReal_ne_top
  have hEtop : E < ⊤ := by
    dsimp only [E]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (by norm_num)
          (lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)))
        hinv) hpow
  let B : ℝ := E.toReal + 1
  have hB : 0 < B := by
    dsimp only [B]
    linarith [ENNReal.toReal_nonneg (a := E)]
  refine ⟨B, hB, ?_⟩
  intro f
  have hlin : (∫⁻ x : Euclidean d,
      ENNReal.ofReal (dyadicBallMaximal d (f : Euclidean d → ℂ) x ^ p)) ≤
        E * ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p := by
    simpa only [E, mul_assoc] using
      dyadic_ball_maximal_lintegral_bound hd0 hpone f
  simpa only [B] using
    dyadic_ball_maximal_real_bound_of_lintegral hd0 (by linarith) E hEtop f hlin

set_option maxHeartbeats 1000000 in
/- Compact frequency support makes the lowpass supremum a lower-semicontinuous
supremum of continuous scaled Schwartz multipliers. -/
private theorem relative_lowpass_aestrongly_measurable
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (f : SchwartzMap (Euclidean d) ℂ) :
    AEStronglyMeasurable (relativeLowpassMaximal d φ f) volume := by
  have hφcompact : HasCompactSupport (φ : Euclidean d → ℂ) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) 2)
    intro ξ hξ
    apply hφzero ξ
    have hlt : 2 < ‖ξ‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hξ
      exact lt_of_not_ge hξ
    exact hlt.le
  obtain ⟨χ, hχ⟩ :=
    exists_schwartz_compactSupport_mul_surfaceFourier φ hφcompact 1
  have hχ' (ξ : Euclidean d) : χ ξ = φ ξ * surfaceFourier d (-ξ) := by
    simpa using hχ ξ
  let R : SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
    fun g x =>
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
          𝓕 (g : Euclidean d → ℂ) ξ) x‖).toReal
  have hRχ : R f = fun x =>
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
        χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal := by
    funext x
    dsimp only [R]
    congr 1
    apply iSup_congr
    intro r
    congr 2
    apply congrArg (fun g : Euclidean d → ℂ => 𝓕⁻ g x)
    funext ξ
    rw [hχ']
    rw [show (-(r.1) : ℝ) • ξ = -(r.1 • ξ) by rw [neg_smul]]
    ring
  change AEStronglyMeasurable (R f) volume
  rw [hRχ]
  apply (ENNReal.measurable_toReal.comp ?_).aestronglyMeasurable
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_iSup
  intro r
  have hrinv : 0 < r.1⁻¹ := inv_pos.mpr r.2
  have hcont : Continuous (fun x : Euclidean d =>
      𝓕⁻ (fun ξ : Euclidean d => χ (r.1 • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x) := by
    simpa [inv_inv] using
      (continuous_fourierInv_scaled_schwartz_multiplier χ f hrinv)
  exact (ENNReal.continuous_ofReal.comp hcont.norm).lowerSemicontinuous

set_option maxHeartbeats 1000000 in
/- A pointwise lowpass majorant transfers a dyadic-ball strong estimate to
the lowpass operator. -/
private theorem relative_lowpass_strong_type_of_majorant
    {d : ℕ} {p : ℝ} (hp0 : 0 < p)
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (B K : ℝ) (hB : 0 < B) (hK : 0 < K)
    (hball : ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (dyadicBallMaximal d (f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (dyadicBallMaximal d (f : Euclidean d → ℂ) x) ^ p) ≤
        B * ∫ x : Euclidean d, ‖f x‖ ^ p)
    (hmajor : ∀ (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d),
      relativeLowpassMaximal d φ f x ≤
        K * dyadicBallMaximal d (f : Euclidean d → ℂ) x) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (relativeLowpassMaximal d φ f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (relativeLowpassMaximal d φ f x) ^ p) ≤
        C * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  refine ⟨K ^ p * B, mul_pos (Real.rpow_pos_of_pos hK _) hB, ?_⟩
  intro f
  have hballf := hball f
  have hRnonneg (x : Euclidean d) : 0 ≤ relativeLowpassMaximal d φ f x :=
    ENNReal.toReal_nonneg
  have hHnonneg (x : Euclidean d) :
      0 ≤ dyadicBallMaximal d (f : Euclidean d → ℂ) x := ENNReal.toReal_nonneg
  have hRmem : MemLp (relativeLowpassMaximal d φ f) (ENNReal.ofReal p) volume :=
    (hballf.1.const_mul K).mono (relative_lowpass_aestrongly_measurable φ hφzero f)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hRnonneg x), Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hK.le (hHnonneg x))]
        exact hmajor f x)
  refine ⟨hRmem, ?_⟩
  have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKHmem : MemLp (fun x : Euclidean d =>
      K * dyadicBallMaximal d (f : Euclidean d → ℂ) x) (ENNReal.ofReal p) volume :=
    hballf.1.const_mul K
  have hKHPowInt : Integrable (fun x : Euclidean d =>
      (K * dyadicBallMaximal d (f : Euclidean d → ℂ) x) ^ p) volume := by
    have h := hKHmem.integrable_norm_rpow hpEN0 hpENT
    convert h using 1
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK.le (hHnonneg x)),
      ENNReal.toReal_ofReal hp0.le]
  calc
    (∫ x : Euclidean d, (relativeLowpassMaximal d φ f x) ^ p) ≤
        ∫ x : Euclidean d, (K * dyadicBallMaximal d (f : Euclidean d → ℂ) x) ^ p := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hRnonneg x) p
          · exact hKHPowInt
          · exact Filter.Eventually.of_forall fun x =>
              Real.rpow_le_rpow (hRnonneg x) (hmajor f x) hp0.le
    _ = K ^ p * ∫ x : Euclidean d,
        (dyadicBallMaximal d (f : Euclidean d → ℂ) x) ^ p := by
          rw [show (fun x : Euclidean d =>
              (K * dyadicBallMaximal d (f : Euclidean d → ℂ) x) ^ p) =
              fun x => K ^ p * (dyadicBallMaximal d (f : Euclidean d → ℂ) x) ^ p by
                funext x
                exact Real.mul_rpow hK.le (hHnonneg x)]
          rw [integral_const_mul]
    _ ≤ K ^ p * (B * ∫ x : Euclidean d, ‖f x‖ ^ p) := by
          exact mul_le_mul_of_nonneg_left hballf.2 (Real.rpow_nonneg hK.le p)
    _ = (K ^ p * B) * ∫ x : Euclidean d, ‖f x‖ ^ p := by ring

/-- The regular relative-frequency component is of strong type (p,p). -/
theorem relative_lowpass_strong_type
    {d : ℕ} (hd : 3 ≤ d) {p : ℝ}
    (hp : (d : ℝ) / ((d : ℝ) - 1) < p)
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (relativeLowpassMaximal d φ f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (relativeLowpassMaximal d φ f x) ^ p) ≤
        B * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast (show 0 < d by omega)
  have hdenom : 0 < (d : ℝ) - 1 := by
    have hdgt : (1 : ℝ) < d := by
      exact_mod_cast (show 1 < d by omega)
    linarith
  have hp0 : 0 < p := (div_pos hdreal hdenom).trans hp
  obtain ⟨K, hK, hmajor⟩ := relative_lowpass_kernel_majorant φ hφzero
  obtain ⟨B, hB, hball⟩ := dyadic_ball_maximal_strong_type hd hp
  exact relative_lowpass_strong_type_of_majorant
    hp0 φ hφzero B K hB hK hball hmajor


end

end LeanSpherical.HarmonicAnalysis
