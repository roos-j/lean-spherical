/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SphericalAverageContinuity
import LeanSpherical.HarmonicAnalysis.MarcinkiewiczInterpolation
import LeanSpherical.HarmonicAnalysis.DyadicLpSummation
import LeanSpherical.HarmonicAnalysis.SmoothDyadicPartition
import LeanSpherical.HarmonicAnalysis.SmoothDyadicSchwartz
import LeanSpherical.HarmonicAnalysis.SmoothDyadicPhysical
import LeanSpherical.HarmonicAnalysis.RelativeDyadicMovingL2
import LeanSpherical.HarmonicAnalysis.PhysicalFourierBridge
import LeanSpherical.HarmonicAnalysis.SphericalAverageInverseFourierBridge
import LeanSpherical.HarmonicAnalysis.SurfaceContinuity
import LeanSpherical.HarmonicAnalysis.SurfaceHeight
import LeanSpherical.HarmonicAnalysis.RationalSchwartzLowTail
import LeanSpherical.HarmonicAnalysis.RationalSchwartzHighTail
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Concrete spherical maximal estimates

This file contains the concrete endpoint estimates and the main finite-
exponent Stein target for the literal normalized operator.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Set Filter
open scoped Convolution FourierTransform Topology

noncomputable section

/-- The normalized spherical maximal operator is a pointwise `L∞`
contraction. -/
theorem normalizedSphericalMaximal_linf_bound {d : ℕ} (hd : 0 < d)
    (f : Euclidean d → ℂ) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ∀ x, normalizedSphericalMaximal d f x ≤ ENNReal.ofReal C :=
  fun x => normalizedSphericalMaximal_le_of_norm_le hd f x hC

/-- The concrete normalized spherical maximal function obeys the `L∞`
endpoint bound inherited from the pointwise averaging estimate.  The
`ENNReal.toReal` is finite here because the same pointwise bound prevents the
supremum from taking the value `∞`. -/
theorem eLpNorm_normalizedSphericalMaximal_top_le {d : ℕ} (hd : 0 < d)
    (f : Euclidean d → ℂ) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    eLpNorm (fun x : Euclidean d => (normalizedSphericalMaximal d f x).toReal)
      ⊤ volume ≤ ENNReal.ofReal C := by
  have hC_nonneg : 0 ≤ C :=
    (norm_nonneg (f 0)).trans (hC 0)
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal hC_nonneg
      (normalizedSphericalMaximal_le_of_norm_le hd f x hC)

/-- For continuous bounded input, the concrete normalized maximal function is
an actual member of `L∞`. -/
theorem memLp_normalizedSphericalMaximal_top {d : ℕ} (hd : 0 < d)
    (f : Euclidean d → ℂ) (hf : Continuous f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    MemLp (fun x : Euclidean d => (normalizedSphericalMaximal d f x).toReal)
      ⊤ volume := by
  refine ⟨?_, ?_⟩
  · exact (ENNReal.measurable_toReal.comp
      (measurable_normalizedSphericalMaximal f hf)).aestronglyMeasurable
  · exact (eLpNorm_normalizedSphericalMaximal_top_le hd f hC).trans_lt
      ENNReal.ofReal_lt_top

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
  let A : Euclidean d → ℤ → ENNReal := fun x n =>
    ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
      ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)
  have hbound (x : Euclidean d) : (⨆ n : ℤ, A x n) ≤ ENNReal.ofReal a := by
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
  have hfinite (x : Euclidean d) : (⨆ n : ℤ, A x n) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact hbound x
  let E : ℕ → Set (Euclidean d) := fun N =>
    {x | ∃ n : ℤ, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) ∧ ENNReal.ofReal s < A x n}
  have hE_union :
      {x | s < (⨆ n : ℤ, A x n).toReal} = ⋃ N : ℕ, E N := by
    ext x
    constructor
    · intro hx
      have hx' : ENNReal.ofReal s < ⨆ n : ℤ, A x n := by
        simpa [A] using
          (ENNReal.ofReal_lt_iff_lt_toReal hs.le (hfinite x)).2 hx
      rcases lt_iSup_iff.mp hx' with ⟨n, hn⟩
      refine mem_iUnion.2 ⟨n.natAbs, ?_⟩
      have hnlo : -((n.natAbs : ℕ) : ℤ) ≤ n := by
        have h := neg_le_neg (Int.le_natAbs (a := -n))
        simpa using h
      exact ⟨n, hnlo, Int.le_natAbs (a := n), hn⟩
    · intro hx
      rcases mem_iUnion.mp hx with ⟨N, n, hnlo, hnhi, hn⟩
      have hx' : s < (⨆ n : ℤ, A x n).toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal hs.le (hfinite x)).1
          (hn.trans_le (le_iSup (fun n : ℤ => A x n) n))
      simpa [A] using hx'
  have hE_mono : Monotone E := by
    intro N M hNM x hx
    rcases hx with ⟨n, hnlo, hnhi, hn⟩
    have hNM' : (N : ℤ) ≤ M := by exact_mod_cast hNM
    exact ⟨n, (neg_le_neg hNM').trans hnlo, hnhi.trans hNM', hn⟩
  have hscale (x : Euclidean d) (r : ℝ) :
      volume (Metric.ball x (4 * r)) =
        (ENNReal.ofReal (4 : ℝ)) ^ d * volume (Metric.ball x r) := by
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
    simp only [Fintype.card_fin]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), mul_pow]
    ring
  have htrunc (N : ℕ) :
      ENNReal.ofReal s * volume (E N) ≤
        (ENNReal.ofReal (4 : ℝ)) ^ d *
          ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
    let t : Set (Euclidean d × ℤ) := {a |
      -(N : ℤ) ≤ a.2 ∧ a.2 ≤ (N : ℤ) ∧ ENNReal.ofReal s < A a.1 a.2}
    obtain ⟨u, hut, hdisj, hcover⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_ball t
        (fun a => a.1) (fun a => (2 : ℝ) ^ a.2) ((2 : ℝ) ^ (N : ℤ)) (by
          intro a ha
          exact zpow_le_zpow_right₀ (by norm_num) ha.2.1)
        4 (by norm_num : (3 : ℝ) < 4)
    have hucount : u.Countable :=
      hdisj.countable_of_isOpen
        (fun _ _ => Metric.isOpen_ball)
        (fun a _ => Metric.nonempty_ball.mpr (zpow_pos (by norm_num) a.2))
    have hEcover : E N ⊆ ⋃ a ∈ u,
        Metric.ball a.1 (4 * (2 : ℝ) ^ a.2) := by
      intro x hx
      rcases hx with ⟨n, hnlo, hnhi, hn⟩
      let a : Euclidean d × ℤ := (x, n)
      have ha : a ∈ t := by
        dsimp [a, t]
        exact ⟨hnlo, hnhi, hn⟩
      rcases hcover a ha with ⟨b, hbu, hsub⟩
      refine mem_iUnion.2 ⟨b, ?_⟩
      refine mem_iUnion.2 ⟨hbu, ?_⟩
      exact hsub (Metric.mem_ball_self (zpow_pos (by norm_num) n))
    have hmeasurecover :
        volume (E N) ≤ ∑' a : u,
          volume (Metric.ball a.1.1 (4 * (2 : ℝ) ^ a.1.2)) := by
      calc
        volume (E N) ≤ volume (⋃ a ∈ u,
            Metric.ball a.1 (4 * (2 : ℝ) ^ a.2)) :=
          measure_mono hEcover
        _ ≤ ∑' a : u,
            volume (Metric.ball a.1.1 (4 * (2 : ℝ) ^ a.1.2)) :=
          measure_biUnion_le volume hucount _
    have hselected (a : u) :
        ENNReal.ofReal s * volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)) ≤
          ∫⁻ y in Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2),
            ENNReal.ofReal ‖g y‖ := by
      have ha : a.1 ∈ t := hut a.2
      have havg : ENNReal.ofReal s <
          (volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2)))⁻¹ *
            (∫⁻ y in Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2),
              ENNReal.ofReal ‖g y‖) := by
        simpa [t, A] using ha.2.2
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
    have hsum :
        ENNReal.ofReal s *
            (∑' a : u, volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2))) ≤
          ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
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
    have hsumscale :
        (∑' a : u, volume (Metric.ball a.1.1 (4 * (2 : ℝ) ^ a.1.2))) =
          (ENNReal.ofReal (4 : ℝ)) ^ d *
            (∑' a : u, volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2))) := by
      simp_rw [hscale]
      exact ENNReal.tsum_mul_left
    calc
      ENNReal.ofReal s * volume (E N) ≤
          ENNReal.ofReal s *
            (∑' a : u, volume (Metric.ball a.1.1 (4 * (2 : ℝ) ^ a.1.2))) := by
        exact mul_le_mul_right hmeasurecover _
      _ = (ENNReal.ofReal (4 : ℝ)) ^ d *
          (ENNReal.ofReal s *
            (∑' a : u, volume (Metric.ball a.1.1 ((2 : ℝ) ^ a.1.2))) ) := by
        rw [hsumscale]
        ring
      _ ≤ (ENNReal.ofReal (4 : ℝ)) ^ d *
          (∫⁻ x, ENNReal.ofReal ‖g x‖) :=
        mul_le_mul_right hsum _
  have hE_union' :
      {x | s <
        (⨆ n : ℤ,
          ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
            ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal} =
        ⋃ N : ℕ, E N := by
    simpa [A] using hE_union
  have hfinal :
      ENNReal.ofReal s *
          volume {x | s <
            (⨆ n : ℤ,
              ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
                ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal} ≤
        (ENNReal.ofReal (4 : ℝ)) ^ d *
          ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
    calc
      ENNReal.ofReal s *
          volume {x | s <
            (⨆ n : ℤ,
              ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
                ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal} =
          ENNReal.ofReal s * volume (⋃ N : ℕ, E N) := by
            rw [hE_union']
      _ = ENNReal.ofReal s * ⨆ N : ℕ, volume (E N) := by
        rw [hE_mono.measure_iUnion]
      _ = ⨆ N : ℕ, ENNReal.ofReal s * volume (E N) :=
        ENNReal.mul_iSup _ _
      _ ≤ (ENNReal.ofReal (4 : ℝ)) ^ d *
          ∫⁻ x, ENNReal.ofReal ‖g x‖ :=
        iSup_le htrunc
  exact hfinal

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

set_option maxHeartbeats 1000000 in
-- The literal all-radii reassembly and its three interpolation regimes are
-- elaborated together in this one theorem, exceeding Lean's default budget.
/-- Stein's spherical maximal theorem, in its Schwartz-core form.  The
operator is the literal supremum over all positive radii of the normalized
spherical averages already defined in `SurfaceMeasure`.  The displayed
strong-type estimate is the single main target for the dyadic-decay and
interpolation argument. -/
theorem stein_spherical_maximal
    {d : ℕ} (hd : 3 ≤ d) {p : ℝ}
    (hp : (d : ℝ) / ((d : ℝ) - 1) < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp
        (fun x : Euclidean d => (normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal)
        (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d,
        ((normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal) ^ p) ≤
        C * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  have hdHeight : 2 ≤ d - 1 := by omega
  obtain ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩ :=
    exists_sharp_surfaceFourier_succ_decay_and_deriv (d := d - 1) hdHeight
  obtain ⟨φ, hφone, hφzero, hφnorm⟩ :=
    exists_schwartz_frequency_cutoff_norm_le_one d
  have hφsum (N : ℕ) (ξ : Euclidean d) :
      ∑ j ∈ Finset.range N,
          (φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) - φ (((2 : ℝ) ^ j)⁻¹ • ξ)) =
        φ (((2 : ℝ) ^ N)⁻¹ • ξ) - φ ξ :=
    smooth_dyadic_bandpass_sum φ N ξ
  /- `P N` is the maximal function of the relative-frequency cutoff
  `φ (2⁻ᴺ r ξ)`.  Unlike an absolute frequency cutoff, this localization is
  compatible with the supremum over all radii. -/
  let P : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
    fun N f x =>
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) *
          φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal
  /- The term with `φ (r ξ)` is the regular, low relative-frequency part. -/
  let R : SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
    fun f x =>
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal
  /- `T j` is the `j`th oscillatory relative-frequency annulus. -/
  let T : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
    fun j f x =>
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) *
          (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
            φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal
  let M : SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
    fun f x => (normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal
  /- The only auxiliary operator in the proof is the centered dyadic-ball
  maximal function.  Restricting to dyadic radii loses only a dimensional
  constant, while making the supremum countable (which is important for its
  measurability and for the covering argument below).  It controls the
  smooth low relative-frequency kernel. -/
  let H : (Euclidean d → ℂ) → Euclidean d → ℝ :=
    fun g x =>
      (⨆ n : ℤ,
        ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
          ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal
  /- First the regular term is controlled by its integrable smooth kernel. -/
  have hregular :
      ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
        MemLp (R f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (R f x) ^ p) ≤
          B * ∫ x : Euclidean d, ‖f x‖ ^ p := by
    /- Compact frequency support makes the inverse Fourier kernel Schwartz;
    its dilates are pointwise dominated by the centered ball maximal
    function. -/
    have hkernel :
        ∃ K : ℝ, 0 < K ∧ ∀ (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d),
          R f x ≤ K * H (f : Euclidean d → ℂ) x := by
      have hφcompact : HasCompactSupport (φ : Euclidean d → ℂ) := by
        apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) 2)
        intro ξ hξ
        apply hφzero ξ
        have hlt : 2 < ‖ξ‖ := by
          rw [Metric.mem_closedBall, dist_zero_right] at hξ
          exact lt_of_not_ge hξ
        exact hlt.le
      /- Bundle the compact multiplier `φ(ξ) σ̂(-ξ)` as a Schwartz map. -/
      obtain ⟨χ, hχ⟩ :=
        exists_schwartz_compactSupport_mul_surfaceFourier φ hφcompact 1
      have hχ' (ξ : Euclidean d) :
          χ ξ = φ ξ * surfaceFourier d (-ξ) := by
        simpa using hχ ξ
      have hRχ (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
          R f x =
            (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
              χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal := by
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
      /- The remaining fact is the standard weak `(1,1)` control of the
      maximal dilates of the fixed Schwartz kernel `𝓕⁻χ`; it is proved from
      the centered ball maximal inequality below. -/
      have hschwartzKernel :
          ∃ K : ℝ, 0 < K ∧ ∀ (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d),
            (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
              χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal ≤
              K * H (f : Euclidean d → ℂ) x := by
        let kernel : SchwartzMap (Euclidean d) ℂ := 𝓕⁻ χ
        /- First identify the multiplier at each radius with the literal
        physical-space dilate of `k`. -/
        have hphysical (f : SchwartzMap (Euclidean d) ℂ)
            (r : Ioi (0 : ℝ)) (x : Euclidean d) :
            𝓕⁻ (fun ξ : Euclidean d =>
              χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x =
              ((fun y : Euclidean d => (r.1⁻¹) ^ d • kernel (r.1⁻¹ • y))
                ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                (f : Euclidean d → ℂ)) x := by
          simpa [kernel] using
            fourierInv_relative_lowpass_eq_convolution χ f r.2 x
        /- A single Schwartz seminorm gives the decay used on all spatial
        annuli.  The next step converts this into ball averages. -/
        have hkernelDecay (z : Euclidean d) :
            (1 + ‖z‖) ^ (d + 1) * ‖kernel z‖ ≤
              2 ^ (d + 1) *
                (Finset.Iic (d + 1, 0)).sup
                  (fun m => SchwartzMap.seminorm ℂ m.1 m.2) kernel := by
          change (1 + ‖z‖) ^ (d + 1) *
              ‖(𝓕⁻ χ : SchwartzMap (Euclidean d) ℂ) z‖ ≤
            2 ^ (d + 1) *
              (Finset.Iic (d + 1, 0)).sup
                (fun m => SchwartzMap.seminorm ℂ m.1 m.2)
                (𝓕⁻ χ : SchwartzMap (Euclidean d) ℂ)
          simpa only [norm_iteratedFDeriv_zero] using
            (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
              (m := (d + 1, 0)) (k := d + 1) (n := 0)
              (by omega) (by omega) (𝓕⁻ χ : SchwartzMap (Euclidean d) ℂ) z)
        /- Split the convolution into `‖y‖ < r` and the annuli
        `2^n r ≤ ‖y‖ < 2^(n+1) r`.  The `d+1` decay leaves a summable
        `2⁻ⁿ`, and each annulus is bounded by the corresponding ball average. -/
        have hannularDomination :
            ∃ K : ℝ, 0 < K ∧ ∀ (f : SchwartzMap (Euclidean d) ℂ)
              (r : Ioi (0 : ℝ)) (x : Euclidean d),
              ‖((fun y : Euclidean d => (r.1⁻¹) ^ d •
                  kernel (r.1⁻¹ • y))
                ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                (f : Euclidean d → ℂ)) x‖ ≤
                K * H (f : Euclidean d → ℂ) x := by
          let C : ℝ := 2 * ((SchwartzMap.seminorm ℂ 0 0 kernel +
            SchwartzMap.seminorm ℂ (d + 2) 0 kernel) *
            (volume (Metric.ball (0 : Euclidean d) 1)).toReal * (2 : ℝ) ^ (2 * d))
          have hsemi0 : 0 ≤ SchwartzMap.seminorm ℂ 0 0 kernel := by
            calc
              0 ≤ ‖kernel (0 : Euclidean d)‖ := norm_nonneg _
              _ ≤ SchwartzMap.seminorm ℂ 0 0 kernel :=
                SchwartzMap.norm_le_seminorm ℂ kernel 0
          have hsemidecay : 0 ≤ SchwartzMap.seminorm ℂ (d + 2) 0 kernel := by
            calc
              0 ≤ ‖(0 : Euclidean d)‖ ^ (d + 2) * ‖kernel 0‖ := by positivity
              _ ≤ SchwartzMap.seminorm ℂ (d + 2) 0 kernel :=
                SchwartzMap.norm_pow_mul_le_seminorm ℂ kernel (d + 2) 0
          have hC : 0 ≤ C := by
            dsimp only [C]
            positivity
          let K : ℝ := C + 1
          refine ⟨K, ?_, ?_⟩
          · dsimp only [K]
            linarith
          intro f r x
          have hHnonneg : 0 ≤ H (f : Euclidean d → ℂ) x := ENNReal.toReal_nonneg
          have hconv := norm_scaled_schwartz_convolution_le_dyadic_average_sup
            kernel f r.2 x
          have hconv' :
              ‖((fun y : Euclidean d => (r.1⁻¹) ^ d • kernel (r.1⁻¹ • y))
                ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                (f : Euclidean d → ℂ)) x‖ ≤ C * H (f : Euclidean d → ℂ) x := by
            calc
              ‖((fun y : Euclidean d => (r.1⁻¹) ^ d • kernel (r.1⁻¹ • y))
                  ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                  (f : Euclidean d → ℂ)) x‖ ≤
                  2 * ((SchwartzMap.seminorm ℂ 0 0 kernel +
                    SchwartzMap.seminorm ℂ (d + 2) 0 kernel) *
                    ((⨆ n : ℤ,
                      ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
                        ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖f y‖)).toReal *
                      (volume (Metric.ball (0 : Euclidean d) 1)).toReal) *
                    (2 : ℝ) ^ (2 * d)) := hconv
              _ = C * H (f : Euclidean d → ℂ) x := by
                dsimp only [C, H]
                ring
          calc
            ‖((fun y : Euclidean d => (r.1⁻¹) ^ d • kernel (r.1⁻¹ • y))
                ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                (f : Euclidean d → ℂ)) x‖ ≤ C * H (f : Euclidean d → ℂ) x := hconv'
            _ ≤ K * H (f : Euclidean d → ℂ) x := by
              apply mul_le_mul_of_nonneg_right
              · dsimp only [K]
                linarith
              · exact hHnonneg
        obtain ⟨K, hK, hannularDomination⟩ := hannularDomination
        refine ⟨K, hK, ?_⟩
        intro f x
        have hKH : 0 ≤ K * H (f : Euclidean d → ℂ) x :=
          mul_nonneg hK.le ENNReal.toReal_nonneg
        have henn :
            (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
              χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖) ≤
              ENNReal.ofReal (K * H (f : Euclidean d → ℂ) x) := by
          apply iSup_le
          intro r
          rw [hphysical f r x]
          exact ENNReal.ofReal_le_ofReal (hannularDomination f r x)
        calc
          (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
            χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal ≤
              (ENNReal.ofReal (K * H (f : Euclidean d → ℂ) x)).toReal :=
            (ENNReal.toReal_le_toReal
              (ne_top_of_le_ne_top ENNReal.ofReal_ne_top henn)
              ENNReal.ofReal_ne_top).2 henn
          _ = K * H (f : Euclidean d → ℂ) x := ENNReal.toReal_ofReal hKH
      obtain ⟨K, hK, hschwartzKernel⟩ := hschwartzKernel
      refine ⟨K, hK, ?_⟩
      intro f x
      rw [hRχ]
      exact hschwartzKernel f x
    /- The centered Hardy--Littlewood inequality is the non-oscillatory
    endpoint needed here. -/
    have hhardyLittlewood :
        ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
          MemLp (H (f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume ∧
          (∫ x : Euclidean d, (H (f : Euclidean d → ℂ) x) ^ p) ≤
            B * ∫ x : Euclidean d, ‖f x‖ ^ p := by
      have hdreal : (2 : ℝ) < d := by
        exact_mod_cast (show 2 < d by omega)
      have hdenom : 0 < (d : ℝ) - 1 := by linarith
      have hcritical : 1 < (d : ℝ) / ((d : ℝ) - 1) := by
        rw [lt_div_iff₀ hdenom]
        nlinarith
      have hpone : 1 < p := hcritical.trans hp
      /- The dyadic ball supremum is nonnegative, subadditive, and a literal
      `L∞` contraction.  These are pointwise facts about its defining
      averages, before any covering argument is used. -/
      have hH_nonneg : ∀ (g : Euclidean d → ℂ) (x : Euclidean d),
          0 ≤ H g x := by
        intro g x
        exact ENNReal.toReal_nonneg
      have hH_iSup_bound : ∀ (g : Euclidean d → ℂ) (a : ℝ), 0 ≤ a →
          (∀ y, ‖g y‖ ≤ a) → ∀ x : Euclidean d,
          (⨆ n : ℤ,
            ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
              ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)) ≤
            ENNReal.ofReal a := by
        intro g a ha hg x
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
      have hH_top : ∀ (g : Euclidean d → ℂ) (a : ℝ), 0 ≤ a →
          (∀ x, ‖g x‖ ≤ a) → ∀ x, H g x ≤ a := by
        intro g a ha hg x
        have hs := hH_iSup_bound g a ha hg x
        change (⨆ n : ℤ,
            ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
              ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal ≤ a
        calc
          (⨆ n : ℤ,
            ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
              ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖)).toReal ≤
              (ENNReal.ofReal a).toReal :=
            (ENNReal.toReal_le_toReal
              (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs) ENNReal.ofReal_ne_top).mpr hs
          _ = a := ENNReal.toReal_ofReal ha
      have hH_subadd : ∀ (g h : Euclidean d → ℂ), Measurable g → Measurable h →
          (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖g x‖ ≤ a) →
          (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖h x‖ ≤ a) →
          ∀ x, H (g + h) x ≤ H g x + H h x := by
        intro g h hgm hhm ⟨a, ha, hga⟩ ⟨b, hb, hhb⟩ x
        let SG : ENNReal := (⨆ n : ℤ,
          ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
            ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖g y‖))
        let SH : ENNReal := (⨆ n : ℤ,
          ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
            ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖h y‖))
        let SGH : ENNReal := (⨆ n : ℤ,
          ((volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
            ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖(g + h) y‖))
        have hSG : SG ≤ ENNReal.ofReal a := hH_iSup_bound g a ha hga x
        have hSH : SH ≤ ENNReal.ofReal b := hH_iSup_bound h b hb hhb x
        have hSGH : SGH ≤ ENNReal.ofReal (a + b) := by
          apply hH_iSup_bound (g + h) (a + b) (add_nonneg ha hb)
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
                  ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖h y‖) :=
              havgadd n
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
      /- Because the radii are indexed by `ℤ`, this is a countable supremum
      of measurable ball averages. -/
      have hH_meas : ∀ (g : Euclidean d → ℂ), Measurable g →
          AEMeasurable (H g) volume := by
        intro g hg
        letI : NeZero d := ⟨by omega⟩
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
      let D : ENNReal := (ENNReal.ofReal (4 : ℝ)) ^ d
      have hDfinite : D ≠ ⊤ := by
        dsimp [D]
        exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
      have hH_weak_one : ∀ (g : Euclidean d → ℂ), Measurable g →
          (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖g x‖ ≤ a) → ∀ {s : ℝ}, 0 < s →
          ENNReal.ofReal s * volume {x | s < H g x} ≤
            D * ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
        intro g hg ⟨a, ha, hga⟩ s hs
        simpa only [H, D] using
          (dyadic_ball_maximal_weak_one (d := d) (by omega) g hg ha hga hs)
      /- The preceding pointwise and weak estimates now feed the explicit
      weak `(1,1)`--`L∞` Marcinkiewicz theorem proved in the supporting
      interpolation file. -/
      have hH_lintegral (f : SchwartzMap (Euclidean d) ℂ) :
          (∫⁻ x : Euclidean d, ENNReal.ofReal (H (f : Euclidean d → ℂ) x ^ p)) ≤
            ENNReal.ofReal p *
              (2 * D * (ENNReal.ofReal (p - 1))⁻¹ *
                (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
                ∫⁻ x : Euclidean d,
                  (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p) := by
        have hf_bounded : ∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖(f : Euclidean d → ℂ) x‖ ≤ a := by
          refine ⟨‖f.toBoundedContinuousFunction‖, norm_nonneg _, ?_⟩
          intro x
          change ‖f.toBoundedContinuousFunction x‖ ≤ ‖f.toBoundedContinuousFunction‖
          exact BoundedContinuousFunction.norm_coe_le_norm _ _
        exact marcinkiewicz_weak_one_top H hH_nonneg hH_subadd D hH_weak_one hH_top
          hpone (f : Euclidean d → ℂ) f.continuous.measurable hf_bounded
          (hH_meas (f : Euclidean d → ℂ) f.continuous.measurable)
      /- Finally, finiteness of the Schwartz input's `p`-moment converts the
      lower-integral conclusion to the displayed real integral and `MemLp`
      assertion. -/
      have hp0 : 0 < p := by linarith
      have hpNN : 0 ≤ p := hp0.le
      let E : ENNReal := ENNReal.ofReal p *
        (2 * D * (ENNReal.ofReal (p - 1))⁻¹ *
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
              (lt_top_iff_ne_top.mpr hDfinite)) hinv) hpow
      let B : ℝ := E.toReal + 1
      refine ⟨B, ?_, ?_⟩
      · dsimp only [B]
        have hE : 0 ≤ E.toReal := ENNReal.toReal_nonneg
        linarith
      intro f
      have hfMem : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume :=
        f.memLp (ENNReal.ofReal p) volume
      have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
      have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
      have hfin : (∫⁻ x : Euclidean d,
          (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p) < ⊤ := by
        have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpEN0 hpENT).mp hfMem.2
        simpa [ENNReal.toReal_ofReal hpNN, enorm_eq_nnnorm] using h
      have hleft : (∫⁻ x : Euclidean d,
          ENNReal.ofReal (H (f : Euclidean d → ℂ) x ^ p)) < ⊤ := by
        calc
          (∫⁻ x : Euclidean d, ENNReal.ofReal (H (f : Euclidean d → ℂ) x ^ p)) ≤
              ENNReal.ofReal p *
                (2 * D * (ENNReal.ofReal (p - 1))⁻¹ *
                  (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
                  ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p) :=
            hH_lintegral f
          _ = E * (∫⁻ x : Euclidean d,
                (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p) := by
              simp only [E, mul_assoc]
          _ < ⊤ := ENNReal.mul_lt_top hEtop hfin
      have hMem : MemLp (H (f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume :=
        memLp_of_lintegral_ofReal_rpow_lt_top (H (f : Euclidean d → ℂ))
          (hH_meas (f : Euclidean d → ℂ) f.continuous.measurable)
          (hH_nonneg (f : Euclidean d → ℂ)) hp0 hleft
      refine ⟨hMem, ?_⟩
      have hHPowInt : Integrable (fun x : Euclidean d =>
          (H (f : Euclidean d → ℂ) x) ^ p) volume := by
        have h := hMem.integrable_norm_rpow hpEN0 hpENT
        convert h using 1
        funext x
        rw [Real.norm_eq_abs, abs_of_nonneg (hH_nonneg (f : Euclidean d → ℂ) x),
          ENNReal.toReal_ofReal hpNN]
      have hfPowInt : Integrable (fun x : Euclidean d =>
          ‖(f : Euclidean d → ℂ) x‖ ^ p) volume := by
        have h := hfMem.integrable_norm_rpow hpEN0 hpENT
        simpa [ENNReal.toReal_ofReal hpNN] using h
      have hleft_eq : (∫ x : Euclidean d, (H (f : Euclidean d → ℂ) x) ^ p) =
          (∫⁻ x : Euclidean d, ENNReal.ofReal (H (f : Euclidean d → ℂ) x ^ p)).toReal := by
        exact integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun x => Real.rpow_nonneg
            (hH_nonneg (f : Euclidean d → ℂ) x) p)
          hHPowInt.aestronglyMeasurable
      have hinput_eq : (∫⁻ x : Euclidean d,
          (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p).toReal =
          ∫ x : Euclidean d, ‖f x‖ ^ p := by
        calc
          (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p).toReal =
              (∫⁻ x : Euclidean d, ENNReal.ofReal (‖(f : Euclidean d → ℂ) x‖ ^ p)).toReal := by
                congr 1
                apply lintegral_congr
                intro x
                exact ENNReal.ofReal_rpow_of_nonneg
                  (norm_nonneg ((f : Euclidean d → ℂ) x)) hpNN
          _ = (ENNReal.ofReal (∫ x : Euclidean d, ‖(f : Euclidean d → ℂ) x‖ ^ p)).toReal := by
                rw [ofReal_integral_eq_lintegral_ofReal hfPowInt]
                exact Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) p
          _ = ∫ x : Euclidean d, ‖f x‖ ^ p :=
                ENNReal.toReal_ofReal (integral_nonneg fun x =>
                  Real.rpow_nonneg (norm_nonneg _) p)
      rw [hleft_eq]
      have hprodtop : E * (∫⁻ x : Euclidean d,
          (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p) ≠ ⊤ :=
        (ENNReal.mul_lt_top hEtop hfin).ne
      have hlin := hH_lintegral f
      change (∫⁻ x : Euclidean d,
          ENNReal.ofReal (H (f : Euclidean d → ℂ) x ^ p)).toReal ≤ _
      calc
        (∫⁻ x : Euclidean d,
          ENNReal.ofReal (H (f : Euclidean d → ℂ) x ^ p)).toReal ≤
            (E * ∫⁻ x : Euclidean d,
              (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p).toReal :=
          (ENNReal.toReal_le_toReal hleft.ne hprodtop).mpr
            (by simpa only [E, mul_assoc] using hlin)
        _ = E.toReal * (∫⁻ x : Euclidean d,
              (ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖) ^ p).toReal := ENNReal.toReal_mul
        _ = E.toReal * ∫ x : Euclidean d, ‖f x‖ ^ p := by rw [hinput_eq]
        _ ≤ B * ∫ x : Euclidean d, ‖f x‖ ^ p := by
          dsimp only [B]
          apply mul_le_mul_of_nonneg_right
          · linarith
          · exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
    /- Transfer the pointwise majorization through the `Lᵖ` estimate. -/
    have htransfer :
        ∀ B K : ℝ, 0 < B → 0 < K →
          (∀ f : SchwartzMap (Euclidean d) ℂ,
            MemLp (H (f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume ∧
            (∫ x : Euclidean d, (H (f : Euclidean d → ℂ) x) ^ p) ≤
              B * ∫ x : Euclidean d, ‖f x‖ ^ p) →
          (∀ (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d),
            R f x ≤ K * H (f : Euclidean d → ℂ) x) →
          ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
            MemLp (R f) (ENNReal.ofReal p) volume ∧
            (∫ x : Euclidean d, (R f x) ^ p) ≤
              C * ∫ x : Euclidean d, ‖f x‖ ^ p := by
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
      have hχ' (ξ : Euclidean d) :
          χ ξ = φ ξ * surfaceFourier d (-ξ) := by
        simpa using hχ ξ
      have hRχ (f : SchwartzMap (Euclidean d) ℂ) :
          R f = fun x =>
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
      have hRmeas (f : SchwartzMap (Euclidean d) ℂ) :
          AEStronglyMeasurable (R f) volume := by
        rw [hRχ f]
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
      have hRnonneg (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
          0 ≤ R f x := by
        dsimp only [R]
        exact ENNReal.toReal_nonneg
      have hHnonneg (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
          0 ≤ H (f : Euclidean d → ℂ) x := by
        dsimp only [H]
        exact ENNReal.toReal_nonneg
      have hdreal : 0 < (d : ℝ) := by
        exact_mod_cast (show 0 < d by omega)
      have hdenom : 0 < (d : ℝ) - 1 := by
        have hdgt : (1 : ℝ) < d := by
          exact_mod_cast (show 1 < d by omega)
        linarith
      have hp0 : 0 < p :=
        (div_pos hdreal hdenom).trans hp
      intro B K hB hK hH hkernel
      refine ⟨K ^ p * B, mul_pos (Real.rpow_pos_of_pos hK _) hB, ?_⟩
      intro f
      have hHf := hH f
      have hRmem : MemLp (R f) (ENNReal.ofReal p) volume :=
        (hHf.1.const_mul K).mono (hRmeas f)
          (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hRnonneg f x),
              Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg hK.le (hHnonneg f x))]
            exact hkernel f x)
      refine ⟨hRmem, ?_⟩
      have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
      have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
      have hKHmem : MemLp (fun x : Euclidean d =>
          K * H (f : Euclidean d → ℂ) x) (ENNReal.ofReal p) volume :=
        hHf.1.const_mul K
      have hKHPowInt : Integrable (fun x : Euclidean d =>
          (K * H (f : Euclidean d → ℂ) x) ^ p) volume := by
        have h := hKHmem.integrable_norm_rpow hpEN0 hpENT
        convert h using 1
        funext x
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hK.le (hHnonneg f x)),
          ENNReal.toReal_ofReal hp0.le]
      calc
        (∫ x : Euclidean d, (R f x) ^ p) ≤
            ∫ x : Euclidean d, (K * H (f : Euclidean d → ℂ) x) ^ p := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun x =>
              Real.rpow_nonneg (hRnonneg f x) p
          · exact hKHPowInt
          · exact Filter.Eventually.of_forall fun x =>
              Real.rpow_le_rpow (hRnonneg f x) (hkernel f x) hp0.le
        _ = K ^ p * ∫ x : Euclidean d,
            (H (f : Euclidean d → ℂ) x) ^ p := by
          rw [show (fun x : Euclidean d =>
              (K * H (f : Euclidean d → ℂ) x) ^ p) =
              fun x => K ^ p * (H (f : Euclidean d → ℂ) x) ^ p by
                funext x
                exact Real.mul_rpow hK.le (hHnonneg f x)]
          rw [integral_const_mul]
        _ ≤ K ^ p * (B * ∫ x : Euclidean d, ‖f x‖ ^ p) := by
          exact mul_le_mul_of_nonneg_left hHf.2 (Real.rpow_nonneg hK.le p)
        _ = (K ^ p * B) * ∫ x : Euclidean d, ‖f x‖ ^ p := by ring
    obtain ⟨K, hK, hkernel⟩ := hkernel
    obtain ⟨B, hB, hhardyLittlewood⟩ := hhardyLittlewood
    exact htransfer B K hB hK hhardyLittlewood hkernel
  /- Each literal annular maximal function is measurable.  Compact support
  of the bandpass lets us fold the surface transform into one fixed Schwartz
  multiplier before taking the radius supremum. -/
  have hTmeas : ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      AEStronglyMeasurable (T j f) volume := by
    intro j f
    obtain ⟨ψ, hψ, hψcompact, _⟩ :=
      exists_compactlySupported_schwartzMap_smooth_dyadic_bandpass
        φ hφone hφzero j
    obtain ⟨χ, hχ⟩ :=
      exists_schwartz_compactSupport_mul_surfaceFourier ψ hψcompact 1
    have hχ' (ξ : Euclidean d) :
        χ ξ = ψ ξ * surfaceFourier d (-ξ) := by
      simpa using hχ ξ
    have hrewrite : T j f = fun x : Euclidean d =>
        (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
          χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal := by
      funext x
      dsimp only [T]
      congr 1
      apply iSup_congr
      intro r
      congr 2
      apply congrArg (fun g : Euclidean d → ℂ => 𝓕⁻ g x)
      funext ξ
      rw [hχ' (r.1 • ξ), hψ]
      rw [show (-(r.1) : ℝ) • ξ = -(r.1 • ξ) by rw [neg_smul]]
      ring
    rw [hrewrite]
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
  have hTnonneg (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
      0 ≤ T j f x := by
    dsimp only [T]
    exact ENNReal.toReal_nonneg
  /- Next Fourier decay, the radius derivative estimate, and interpolation
  give a summable bound for every oscillatory annulus. -/
  have hdyadic :
      ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
        MemLp (T j f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (T j f x) ^ p) ≤
          A * (2 : ℝ) ^ (-ε * j) * ∫ x : Euclidean d, ‖f x‖ ^ p := by
    /- Use one fixed band-pass `ψ(η) = φ(η / 2) - φ(η)`.  Thus every
    literal `T j` is exactly the generic relative multiplier with `ψ` at
    scale `2^j`; the following three endpoint facts are consequently about
    the displayed operator itself. -/
    obtain ⟨ψ, hψ⟩ := exists_schwartzMap_smooth_dyadic_bandpass φ 0
    have hrewrite (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
        T j f x =
          (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) *
              ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal := by
      dsimp only [T]
      congr 1
      apply iSup_congr
      intro r
      congr 2
      apply congrArg (fun q : Euclidean d → ℂ => 𝓕⁻ q x)
      funext ξ
      have hscalar : (2 : ℝ)⁻¹ * ((2 : ℝ) ^ j)⁻¹ = ((2 : ℝ) ^ (j + 1))⁻¹ := by
        rw [pow_succ, mul_inv_rev]
      have hfirst : (2 : ℝ)⁻¹ • (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) =
          ((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ) := by
        calc
          (2 : ℝ)⁻¹ • (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) =
              ((2 : ℝ)⁻¹ * ((2 : ℝ) ^ j)⁻¹) • (r.1 • ξ) := smul_smul _ _ _
          _ = _ := by rw [hscalar]
      rw [hψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))]
      simp only [zero_add, pow_one, pow_zero, inv_one, one_smul]
      rw [hfirst]
    /- The raw supremum is subadditive before `toReal`; the finiteness
    needed to pass to real values is supplied by the literal `L∞` estimate. -/
    have hT_subadd (j : ℕ) (f g : SchwartzMap (Euclidean d) ℂ)
        (x : Euclidean d) : T j (f + g) x ≤ T j f x + T j g x := by
      rw [hrewrite j (f + g) x, hrewrite j f x, hrewrite j g x]
      exact
        toReal_iSup_ennreal_norm_fourierInv_relative_surface_scaled_schwartz_multiplier_add_le
          ψ f g j x
    /- The physical shell estimate and Vitali's theorem give weak `(1,1)`
    with the actual `2^j` loss. -/
    have hT_weak_one :
        ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
          {a : ℝ}, 0 ≤ a → (∀ x, ‖f x‖ ≤ a) → ∀ {s : ℝ}, 0 < s →
          ENNReal.ofReal s * volume {x | s < T j f x} ≤
            (ENNReal.ofReal
              (D * (2 : ℝ) ^ j *
                (volume (Metric.ball (0 : Euclidean d) 1)).toReal) *
              (ENNReal.ofReal (4 : ℝ)) ^ d) *
              ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
      obtain ⟨D, hD, hweak⟩ :=
        exists_iSup_relative_surface_scaled_schwartz_multiplier_weak_one
          (d := d) (by omega) ψ
      refine ⟨D, hD, ?_⟩
      intro j f a ha hfa s hs
      have hset :
          {x | s < T j f x} =
            {x | s <
              (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
                surfaceFourier d (-r.1 • ξ) *
                  ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
                  𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal} := by
        ext x
        simp only [Set.mem_setOf_eq]
        rw [hrewrite j f x]
      rw [hset]
      exact hweak j f ha hfa hs
    /- The global moving-radius `L²` estimate is inserted here next.  It is
    proved from finite dyadic radius blocks and their frequency square
    function, then passed to the literal `Ioi` supremum by monotone
    convergence. -/
    have hT_strong_two :
        ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
          MemLp (T j f) 2 volume ∧
          (∫ x : Euclidean d, (T j f x) ^ (2 : ℕ)) ≤
            D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
              ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ) := by
      obtain ⟨D, hD, hglobal⟩ :=
        exists_memLp_two_iSup_relative_dyadic_moving_bandpass_global_exponential
          (n := d) hd φ hφone hφzero hφnorm
      refine ⟨D, hD, ?_⟩
      intro j f
      rcases hglobal j f with ⟨hmem, hbound⟩
      refine ⟨?_, ?_⟩
      · simpa only [T] using hmem
      · calc
          (∫ x : Euclidean d, (T j f x) ^ (2 : ℕ)) =
              ∫ x : Euclidean d, ‖T j f x‖ ^ (2 : ℕ) := by
                apply integral_congr_ae
                filter_upwards with x
                rw [Real.norm_of_nonneg (hTnonneg j f x)]
          _ ≤ D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
              ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ) := by
                have hexp : -((d : ℝ) - 2) * (j : ℝ) =
                    -(((d : ℝ) - 2) * (j : ℝ)) := by ring
                simpa only [T, hexp] using hbound
    /- Chebyshev turns the preceding strong estimate into the weak endpoint
    used by both interpolation arguments. -/
    have hT_weak_two :
        ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
          {s : ℝ}, 0 < s →
          ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j f x} ≤
            ENNReal.ofReal
              (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) *
              ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) := by
      obtain ⟨D, hD, hstrong⟩ := hT_strong_two
      refine ⟨D, hD, ?_⟩
      intro j f s hs
      have hTint : Integrable (fun x : Euclidean d => (T j f x) ^ (2 : ℕ)) volume :=
        (memLp_two_iff_integrable_sq (hTmeas j f)).1 (hstrong j f).1
      have hCheb :
          ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j f x} ≤
            ENNReal.ofReal
              (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
                ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ)) := by
        calc
          ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j f x} ≤
              ENNReal.ofReal (s ^ (2 : ℕ)) *
                volume {x | ENNReal.ofReal (s ^ (2 : ℕ)) ≤
                  ENNReal.ofReal ((T j f x) ^ (2 : ℕ))} := by
              apply mul_le_mul_right
              apply measure_mono
              intro x hx
              exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hs.le hx.le 2)
          _ ≤ ∫⁻ x, ENNReal.ofReal ((T j f x) ^ (2 : ℕ)) :=
            mul_meas_ge_le_lintegral₀
              ((hTmeas j f).aemeasurable.pow_const 2).ennreal_ofReal
              (ENNReal.ofReal (s ^ (2 : ℕ)))
          _ = ENNReal.ofReal (∫ x : Euclidean d, (T j f x) ^ (2 : ℕ)) := by
            symm
            exact ofReal_integral_eq_lintegral_ofReal hTint
              (Filter.Eventually.of_forall fun x => sq_nonneg (T j f x))
          _ ≤ ENNReal.ofReal
              (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
                ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ)) :=
            ENNReal.ofReal_le_ofReal (hstrong j f).2
      have hfMem : MemLp (f : Euclidean d → ℂ) 2 volume := f.memLp 2 volume
      have hfInt : Integrable (fun x : Euclidean d => ‖f x‖ ^ (2 : ℕ)) volume :=
        (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).1 hfMem
      have hInput :
          (∫⁻ x : Euclidean d, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) =
            ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ)) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hfInt
          (Filter.Eventually.of_forall fun x => sq_nonneg (‖f x‖))
      have hscale : 0 ≤ (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) :=
        Real.rpow_nonneg (by norm_num) _
      have hcoef : 0 ≤ D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) :=
        mul_nonneg hD.le hscale
      calc
        ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j f x} ≤
            ENNReal.ofReal
              (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
                ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ)) := hCheb
        _ = (ENNReal.ofReal (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)))) *
              (ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ))) := by
          rw [ENNReal.ofReal_mul hcoef]
        _ = (ENNReal.ofReal (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)))) *
              ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) := by rw [hInput]
    /- Below are the three actual interpolation regimes.  For `1 < p < 2`
    we balance the weak endpoints at `s = 2^((d-1)j)`; at `p = 2` we use the
    preceding square estimate; above `2` we interpolate weak `(2,2)` with
    the literal scale-uniform `L∞` bound using the smooth Schwartz split. -/
    rcases lt_trichotomy p 2 with hp_lt | hp_eq | hp_gt
    · have hd2 : 2 ≤ d := by omega
      have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have hd1 : 0 < (d : ℝ) - 1 := by linarith
      have hp1 : 1 < p := by
        have hone : 1 < (d : ℝ) / ((d : ℝ) - 1) := by
          apply (lt_div_iff₀ hd1).2
          linarith
        exact hone.trans hp
      have hp0 : 0 < p := by linarith
      have heps : 0 < ((d : ℝ) - 1) * p - d := by
        have hmul : (d : ℝ) < p * ((d : ℝ) - 1) :=
          (div_lt_iff₀ hd1).mp hp
        nlinarith
      have balance_one_two
          {j : ℕ} {c1 c2 a1 a2 : ℝ}
          (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
          (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (I : ENNReal) :
          ENNReal.ofReal p *
            (4 * ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
                ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) *
                  (ENNReal.ofReal a2 * I)) +
              2 * ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
                ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) *
                  (ENNReal.ofReal a1 * I))) =
            ENNReal.ofReal (p * (4 * c2 * a2 + 2 * c1 * a1)) *
              (ENNReal.ofReal (2 : ℝ)) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I := by
        have hpow (n : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ n) =
            (ENNReal.ofReal (2 : ℝ)) ^ (n : ℝ) := by
          rw [← Real.rpow_natCast]
          exact (ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).symm
        have hrpow (a : ℝ) : ENNReal.ofReal ((2 : ℝ) ^ a) =
            (ENNReal.ofReal (2 : ℝ)) ^ a :=
          (ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).symm
        have htwo0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
        have htwoT : ENNReal.ofReal (2 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
        have hbal2 :
            ENNReal.ofReal ((2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
              (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) =
                (ENNReal.ofReal (2 : ℝ)) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) := by
          calc
            ENNReal.ofReal ((2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
                (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) =
                (ENNReal.ofReal (2 : ℝ)) ^ (-((d : ℝ) - 2) * (j : ℝ)) *
                  ((ENNReal.ofReal (2 : ℝ)) ^ (((d - 1) * j : ℕ) : ℝ)) ^ (2 - p) := by
                    rw [hrpow, hpow]
            _ = (ENNReal.ofReal (2 : ℝ)) ^
                  (-((d : ℝ) - 2) * (j : ℝ) + (((d - 1) * j : ℕ) : ℝ) * (2 - p)) := by
                    rw [← ENNReal.rpow_mul]
                    rw [← ENNReal.rpow_add _ _ htwo0 htwoT]
            _ = (ENNReal.ofReal (2 : ℝ)) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) := by
                    congr 1
                    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ d)]
                    push_cast
                    ring
        have hbal1 :
            ENNReal.ofReal ((2 : ℝ) ^ (j : ℝ)) *
              (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) =
                (ENNReal.ofReal (2 : ℝ)) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) := by
          calc
            ENNReal.ofReal ((2 : ℝ) ^ (j : ℝ)) *
                (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) =
                (ENNReal.ofReal (2 : ℝ)) ^ (j : ℝ) *
                  ((ENNReal.ofReal (2 : ℝ)) ^ (((d - 1) * j : ℕ) : ℝ)) ^ (1 - p) := by
                    rw [hrpow, hpow]
            _ = (ENNReal.ofReal (2 : ℝ)) ^
                  ((j : ℝ) + (((d - 1) * j : ℕ) : ℝ) * (1 - p)) := by
                    rw [← ENNReal.rpow_mul]
                    rw [← ENNReal.rpow_add _ _ htwo0 htwoT]
            _ = (ENNReal.ofReal (2 : ℝ)) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) := by
                    congr 1
                    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ d)]
                    push_cast
                    ring
        have hterm2 :
            4 * ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
                ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) *
                  (ENNReal.ofReal a2 * I)) =
              (4 * ENNReal.ofReal c2 * ENNReal.ofReal a2) *
                (ENNReal.ofReal (2 : ℝ)) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I := by
          rw [ENNReal.ofReal_mul hc2]
          calc
            4 * (ENNReal.ofReal c2 * ENNReal.ofReal ((2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ)))) *
                ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) *
                  (ENNReal.ofReal a2 * I)) =
                (4 * ENNReal.ofReal c2 * ENNReal.ofReal a2) *
                  (ENNReal.ofReal ((2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
                    (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p)) * I := by ring
            _ = _ := by rw [hbal2]
        have hterm1 :
            2 * ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
                ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) *
                  (ENNReal.ofReal a1 * I)) =
              (2 * ENNReal.ofReal c1 * ENNReal.ofReal a1) *
                (ENNReal.ofReal (2 : ℝ)) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I := by
          rw [ENNReal.ofReal_mul hc1]
          calc
            2 * (ENNReal.ofReal c1 * ENNReal.ofReal ((2 : ℝ) ^ (j : ℝ))) *
                ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) *
                  (ENNReal.ofReal a1 * I)) =
                (2 * ENNReal.ofReal c1 * ENNReal.ofReal a1) *
                  (ENNReal.ofReal ((2 : ℝ) ^ (j : ℝ)) *
                    (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p)) * I := by ring
            _ = _ := by rw [hbal1]
        have hconst2 : 4 * ENNReal.ofReal c2 * ENNReal.ofReal a2 =
            ENNReal.ofReal (4 * c2 * a2) := by
          calc
            4 * ENNReal.ofReal c2 * ENNReal.ofReal a2 =
                ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal c2 * ENNReal.ofReal a2 := by norm_num
            _ = ENNReal.ofReal ((4 : ℝ) * c2) * ENNReal.ofReal a2 := by
                rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
            _ = ENNReal.ofReal ((4 : ℝ) * c2 * a2) := by
                rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hc2)]
        have hconst1 : 2 * ENNReal.ofReal c1 * ENNReal.ofReal a1 =
            ENNReal.ofReal (2 * c1 * a1) := by
          calc
            2 * ENNReal.ofReal c1 * ENNReal.ofReal a1 =
                ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal c1 * ENNReal.ofReal a1 := by norm_num
            _ = ENNReal.ofReal ((2 : ℝ) * c1) * ENNReal.ofReal a1 := by
                rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            _ = ENNReal.ofReal ((2 : ℝ) * c1 * a1) := by
                rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hc1)]
        have hcoeff : ENNReal.ofReal p *
            (4 * ENNReal.ofReal c2 * ENNReal.ofReal a2 +
              2 * ENNReal.ofReal c1 * ENNReal.ofReal a1) =
            ENNReal.ofReal (p * (4 * c2 * a2 + 2 * c1 * a1)) := by
          rw [hconst2, hconst1]
          rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg (by norm_num) hc2) ha2)
            (mul_nonneg (mul_nonneg (by norm_num) hc1) ha1)]
          rw [← ENNReal.ofReal_mul hp0.le]
        rw [hterm2, hterm1]
        calc
          ENNReal.ofReal p *
              ((4 * ENNReal.ofReal c2 * ENNReal.ofReal a2) *
                  (ENNReal.ofReal (2 : ℝ)) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I +
                (2 * ENNReal.ofReal c1 * ENNReal.ofReal a1) *
                  (ENNReal.ofReal (2 : ℝ)) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I) =
              (ENNReal.ofReal p *
                (4 * ENNReal.ofReal c2 * ENNReal.ofReal a2 +
                  2 * ENNReal.ofReal c1 * ENNReal.ofReal a1)) *
                (ENNReal.ofReal (2 : ℝ)) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I := by ring
          _ = _ := by rw [hcoeff]
      obtain ⟨D1, hD1, hweak1⟩ := hT_weak_one
      obtain ⟨D2, hD2, hweak2⟩ := hT_weak_two
      let V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal
      let c1 : ℝ := D1 * V * (4 : ℝ) ^ d
      let c2 : ℝ := D2
      let a1 : ℝ := (p - 1)⁻¹ + (3 - p)⁻¹
      let a2 : ℝ := ((1 : ℝ) / 4) * p⁻¹ + (2 - p)⁻¹
      have hV : 0 ≤ V := ENNReal.toReal_nonneg
      have hc1 : 0 ≤ c1 := by
        dsimp only [c1]
        positivity
      have hc2 : 0 ≤ c2 := hD2.le
      have ha1 : 0 ≤ a1 := by
        dsimp only [a1]
        exact add_nonneg (inv_nonneg.mpr (by linarith))
          (inv_nonneg.mpr (by linarith))
      have ha2 : 0 ≤ a2 := by
        dsimp only [a2]
        exact add_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hp0.le))
          (inv_nonneg.mpr (by linarith))
      have ha2pos : 0 < a2 := by
        dsimp only [a2]
        exact lt_of_lt_of_le (mul_pos (by norm_num) (inv_pos.mpr hp0))
          (le_add_of_nonneg_right (inv_nonneg.mpr (by linarith)))
      refine ⟨p * (4 * c2 * a2 + 2 * c1 * a1),
        ((d : ℝ) - 1) * p - d, ?_, heps, ?_⟩
      · have hbracket : 0 < 4 * c2 * a2 + 2 * c1 * a1 := by
          have hfirst : 0 < 4 * c2 * a2 := by
            exact mul_pos (mul_pos (by norm_num) hD2) ha2pos
          exact hfirst.trans_le (le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg (by norm_num) hc1) ha1))
        positivity
      intro j f
      obtain ⟨low, high, hlow, hhigh, hsplit⟩ :=
        exists_schwartz_rational_low_high_family f
      have hprofiles := measurable_rational_low_high_profile_lintegrals f low high hlow hhigh
        (μ := volume)
      let I : ENNReal := ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p
      have htail2raw := rational_schwartz_low_weighted_tail f low high hlow hhigh hp1 hp_lt
      have htail1raw := rational_schwartz_high_weighted_tail f low high hlow hhigh hp1 hp_lt
      have hA1 :
          (ENNReal.ofReal (p - 1))⁻¹ + (ENNReal.ofReal (3 - p))⁻¹ =
            ENNReal.ofReal a1 := by
        dsimp only [a1]
        rw [← ENNReal.ofReal_inv_of_pos (by linarith : 0 < p - 1)]
        rw [← ENNReal.ofReal_inv_of_pos (by linarith : 0 < 3 - p)]
        rw [← ENNReal.ofReal_add (inv_nonneg.mpr (by linarith))
          (inv_nonneg.mpr (by linarith))]
      have hA2 :
          ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹ +
              (ENNReal.ofReal (2 - p))⁻¹ = ENNReal.ofReal a2 := by
        dsimp only [a2]
        rw [← ENNReal.ofReal_inv_of_pos hp0]
        rw [← ENNReal.ofReal_inv_of_pos (by linarith : 0 < 2 - p)]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) (inv_nonneg.mpr hp0.le))
          (inv_nonneg.mpr (by linarith))]
      have htail2 :
          (∫⁻ t in Ioi (0 : ℝ),
            (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ))) *
              (ENNReal.ofReal t) ^ (p - 3)) ≤ ENNReal.ofReal a2 * I := by
        simpa only [I, hA2] using htail2raw
      have htail1 :
          (∫⁻ t in Ioi (0 : ℝ),
            (∫⁻ x, ENNReal.ofReal ‖high t x‖) *
              (ENNReal.ofReal t) ^ (p - 2)) ≤ ENNReal.ofReal a1 * I := by
        simpa only [I, hA1] using htail1raw
      have hweak1norm (g : SchwartzMap (Euclidean d) ℂ) {s : ℝ} (hs : 0 < s) :
          ENNReal.ofReal s * volume {x | s < T j g x} ≤
            ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
              ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
        have hbound : ∀ x : Euclidean d, ‖g x‖ ≤ ‖g.toBoundedContinuousFunction‖ := by
          intro x
          change ‖g.toBoundedContinuousFunction x‖ ≤ ‖g.toBoundedContinuousFunction‖
          exact BoundedContinuousFunction.norm_coe_le_norm _ _
        have h := hweak1 j g (norm_nonneg _) hbound hs
        have hcoeff :
            ENNReal.ofReal (D1 * (2 : ℝ) ^ j * V) * (ENNReal.ofReal (4 : ℝ)) ^ d =
              ENNReal.ofReal (c1 * (2 : ℝ) ^ j) := by
          dsimp only [c1]
          rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4)]
          rw [← ENNReal.ofReal_mul
            (mul_nonneg (mul_nonneg hD1.le (pow_nonneg (by norm_num) _)) hV)]
          congr 1
          ring
        rw [Real.rpow_natCast]
        simpa only [V, hcoeff] using h
      have hweak2norm (g : SchwartzMap (Euclidean d) ℂ) {s : ℝ} (hs : 0 < s) :
          ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j g x} ≤
            ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
              ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) := by
        have hexp : -(((d : ℝ) - 2) * (j : ℝ)) =
            -((d : ℝ) - 2) * (j : ℝ) := by ring
        simpa only [c2, hexp] using hweak2 j g hs
      let s : ℝ := (2 : ℝ) ^ ((d - 1) * j)
      have hs : 0 < s := by
        dsimp only [s]
        positivity
      have hinterp := marcinkiewicz_weak_one_two_on_additive_split_scaled
        (Set.univ : Set (SchwartzMap (Euclidean d) ℂ))
        (fun g : SchwartzMap (Euclidean d) ℂ => (g : Euclidean d → ℂ))
        (T j)
        (fun g x => hTnonneg j g x)
        (by
          intro g h _ _ x
          exact hT_subadd j g h x)
        (ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)))
        (ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))))
        (by
          intro g _ s hs
          exact hweak1norm g hs)
        (by
          intro g _ s hs
          exact hweak2norm g hs)
        hp1 hp_lt f (hTmeas j f).aemeasurable low high
        (by intro t; simp) (by intro t; simp) (by
          intro t
          ext x
          exact hsplit t x) hprofiles.1 hprofiles.2
        (ENNReal.ofReal a2 * I) (ENNReal.ofReal a1 * I)
        htail2 htail1 s hs
      have hbalanced :
          (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
            ENNReal.ofReal (p * (4 * c2 * a2 + 2 * c1 * a1)) *
              (ENNReal.ofReal (2 : ℝ)) ^
                (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I := by
        calc
          (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
              ENNReal.ofReal p *
                (4 * ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
                    ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) *
                      (ENNReal.ofReal a2 * I)) +
                  2 * ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
                    ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) *
                      (ENNReal.ofReal a1 * I))) := by
              simpa only [s] using hinterp
          _ = _ := balance_one_two hc1 hc2 ha1 ha2 I
      have hqpos : 0 < p * (4 * c2 * a2 + 2 * c1 * a1) := by
        have hfirst : 0 < 4 * c2 * a2 := by
          exact mul_pos (mul_pos (by norm_num) hD2) ha2pos
        have hbracket : 0 < 4 * c2 * a2 + 2 * c1 * a1 :=
          hfirst.trans_le (le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg (by norm_num) hc1) ha1))
        exact mul_pos hp0 hbracket
      let J : ℝ := ∫ x : Euclidean d, ‖f x‖ ^ p
      have hfMem : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume :=
        f.memLp (ENNReal.ofReal p) volume
      have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
      have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
      have hfPowInt : Integrable (fun x : Euclidean d => ‖f x‖ ^ p) volume := by
        have h := hfMem.integrable_norm_rpow hpEN0 hpENT
        simpa only [ENNReal.toReal_ofReal hp0.le] using h
      have hI : I = ENNReal.ofReal J := by
        calc
          I = ∫⁻ x : Euclidean d, ENNReal.ofReal (‖f x‖ ^ p) := by
            dsimp only [I]
            apply lintegral_congr
            intro x
            exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
          _ = ENNReal.ofReal J := by
            dsimp only [J]
            exact (ofReal_integral_eq_lintegral_ofReal hfPowInt
              (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) p)).symm
      have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have hcoeff :
          ENNReal.ofReal (p * (4 * c2 * a2 + 2 * c1 * a1)) *
              (ENNReal.ofReal (2 : ℝ)) ^
                (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I =
            ENNReal.ofReal
              (p * (4 * c2 * a2 + 2 * c1 * a1) *
                (2 : ℝ) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * J) := by
        rw [hI]
        rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
        rw [← ENNReal.ofReal_mul hqpos.le]
        rw [← ENNReal.ofReal_mul (mul_nonneg hqpos.le hpow_nonneg)]
      have hbound :
          (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
            ENNReal.ofReal
              (p * (4 * c2 * a2 + 2 * c1 * a1) *
                (2 : ℝ) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * J) := by
        rw [← hcoeff]
        exact hbalanced
      have hleft :
          (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) < ⊤ :=
        lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
      have hMem : MemLp (T j f) (ENNReal.ofReal p) volume :=
        memLp_of_lintegral_ofReal_rpow_lt_top (T j f)
          (hTmeas j f).aemeasurable (hTnonneg j f) hp0 hleft
      refine ⟨hMem, ?_⟩
      have hTPowInt : Integrable (fun x : Euclidean d => (T j f x) ^ p) volume := by
        have h := hMem.integrable_norm_rpow hpEN0 hpENT
        convert h using 1
        funext x
        rw [Real.norm_eq_abs, abs_of_nonneg (hTnonneg j f x),
          ENNReal.toReal_ofReal hp0.le]
      have hleft_eq :
          (∫ x : Euclidean d, (T j f x) ^ p) =
            (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hTnonneg j f x) p)
          hTPowInt.aestronglyMeasurable
      rw [hleft_eq]
      calc
        (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)).toReal ≤
            (ENNReal.ofReal
              (p * (4 * c2 * a2 + 2 * c1 * a1) *
                (2 : ℝ) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * J)).toReal :=
          (ENNReal.toReal_le_toReal hleft.ne ENNReal.ofReal_ne_top).mpr hbound
        _ = p * (4 * c2 * a2 + 2 * c1 * a1) *
            (2 : ℝ) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * J :=
          ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hqpos.le hpow_nonneg)
            (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p))
    · subst p
      obtain ⟨D, hD, hstrong⟩ := hT_strong_two
      refine ⟨D, (d : ℝ) - 2, hD, ?_, ?_⟩
      · have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      · intro j f
        rcases hstrong j f with ⟨hmem, hbound⟩
        constructor
        · norm_num
          exact hmem
        · have hexp : -((d : ℝ) - 2) * (j : ℝ) =
              -(((d : ℝ) - 2) * (j : ℝ)) := by ring
          simpa only [Real.rpow_two, hexp] using hbound
    · have hT_top :
          ∃ Ctop : ℝ, 0 < Ctop ∧ ∀ j (f : SchwartzMap (Euclidean d) ℂ)
            (a : ℝ), 0 ≤ a → (∀ x, ‖f x‖ ≤ a) → ∀ x,
              T j f x ≤ Ctop * a := by
        let B : ℝ :=
          (∫ y : Euclidean d,
            ‖(𝓕⁻ ψ : SchwartzMap (Euclidean d) ℂ) y‖) *
              surfaceMass d
        have hB : 0 ≤ B := by
          dsimp only [B]
          exact mul_nonneg (integral_nonneg fun y => norm_nonneg _)
            ENNReal.toReal_nonneg
        refine ⟨B + 1, by linarith, ?_⟩
        intro j f a ha hfa x
        rw [hrewrite j f x]
        calc
          (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) *
              ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal ≤
              (a * ∫ y : Euclidean d,
                ‖(𝓕⁻ ψ : SchwartzMap (Euclidean d) ℂ) y‖) *
                  surfaceMass d :=
            iSup_norm_fourierInv_relative_surface_scaled_schwartz_multiplier_le
              ψ f j hfa x
          _ = B * a := by
            dsimp only [B]
            ring
          _ ≤ (B + 1) * a := by nlinarith
      rcases hT_weak_two with ⟨D, hD, hweak⟩
      rcases hT_top with ⟨Ctop, hCtop, htop⟩
      let Atail : ℝ := (p - 2)⁻¹ * (4 : ℝ) ^ (p - 2)
      let A : ℝ := p * (2 : ℝ) ^ (2 : ℝ) * D * Atail * Ctop ^ (p - 2)
      refine ⟨A, (d : ℝ) - 2, ?_, ?_, ?_⟩
      · dsimp only [A, Atail]
        positivity
      · have : (2 : ℝ) < d := by exact_mod_cast (show 2 < d by omega)
        linarith
      intro j f
      obtain ⟨low, high, hlow, hhigh, hsplit⟩ :=
        exists_schwartz_smooth_low_high_family f
      have hp0 : 0 < p := by linarith
      have hpNN : 0 ≤ p := hp0.le
      have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
      have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
      have hfMem : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume :=
        f.memLp (ENNReal.ofReal p) volume
      have hfPowInt : Integrable (fun x : Euclidean d => ‖f x‖ ^ p) volume := by
        have h := hfMem.integrable_norm_rpow hpEN0 hpENT
        simpa [ENNReal.toReal_ofReal hpNN] using h
      let J : ℝ := ∫ x : Euclidean d, ‖f x‖ ^ p
      have hJ : 0 ≤ J := by
        dsimp only [J]
        exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
      have hinput :
          (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p) = ENNReal.ofReal J := by
        calc
          (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p) =
              ∫⁻ x : Euclidean d, ENNReal.ofReal (‖f x‖ ^ p) := by
            apply lintegral_congr
            intro x
            exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpNN
          _ = ENNReal.ofReal J := by
            dsimp only [J]
            exact (ofReal_integral_eq_lintegral_ofReal hfPowInt
              (Filter.Eventually.of_forall fun x =>
                Real.rpow_nonneg (norm_nonneg _) p)).symm
      let Aq : ℝ := Atail * J
      have hAq : 0 ≤ Aq := by
        dsimp only [Aq]
        exact mul_nonneg (by dsimp only [Atail]; positivity) hJ
      have htail :
          (∫⁻ t in Ioi (0 : ℝ),
            (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖high t x‖) ^ (2 : ℝ)) *
              (ENNReal.ofReal t) ^ (p - 2 - 1)) ≤ ENNReal.ofReal Aq := by
        have h := smooth_bump_schwartz_high_q_weighted_tail f low high hlow hhigh
          (q := (2 : ℝ)) (p := p) (by norm_num) hp_gt
        rw [hinput] at h
        have htail_eq :
            (ENNReal.ofReal (p - 2))⁻¹ * (ENNReal.ofReal (4 : ℝ)) ^ (p - 2) *
                ENNReal.ofReal J = ENNReal.ofReal Aq := by
          dsimp only [Aq, Atail]
          rw [← ENNReal.ofReal_inv_of_pos (by linarith : 0 < p - 2)]
          rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 4)]
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (p - 2)⁻¹)]
          rw [← ENNReal.ofReal_mul
            (by positivity : 0 ≤ (p - 2)⁻¹ * (4 : ℝ) ^ (p - 2))]
        rw [htail_eq] at h
        exact h
      have hlin :
          (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
            ENNReal.ofReal
              (p * (2 : ℝ) ^ (2 : ℝ) *
                (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) * Aq * Ctop ^ (p - 2)) := by
        apply marcinkiewicz_weak_q_top_on_additive_split_real_top_scaled
          (D := Set.univ) (eval := fun g : SchwartzMap (Euclidean d) ℂ =>
            (g : Euclidean d → ℂ)) (T := T j) (q := (2 : ℝ))
            (Cq := D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) (Ctop := Ctop)
            (p := p) (f := f) (low := low) (high := high) (Aq := Aq)
        · intro g x
          exact hTnonneg j g x
        · intro g h _ _ x
          exact hT_subadd j g h x
        · norm_num
        · exact hCtop
        · intro g _ s hs
          have hw := hweak j g hs
          simpa [ENNReal.ofReal_rpow_of_pos hs,
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
              (by norm_num : (0 : ℝ) ≤ 2)] using hw
        · intro g _ a ha hga x
          exact htop j g a ha hga x
        · exact hp_gt
        · exact (hTmeas j f).aemeasurable
        · intro t
          simp
        · intro t
          simp
        · intro t
          ext x
          exact hsplit t x
        · intro t ht x
          exact smooth_low_norm_le_half_height f (low t) ht (hlow t) x
        · exact measurable_smooth_high_profile_lintegrals f low high hlow hhigh 2
        · exact htail
        · exact hAq
      have hcoeff :
          p * (2 : ℝ) ^ (2 : ℝ) *
              (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) * Aq * Ctop ^ (p - 2) =
            A * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) * J := by
        dsimp only [A, Aq, Atail]
        ring
      have hlin' :
          (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
            ENNReal.ofReal (A * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) * J) := by
        rw [← hcoeff]
        exact hlin
      have hleft :
          (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) < ⊤ :=
        hlin'.trans_lt ENNReal.ofReal_lt_top
      have hMem : MemLp (T j f) (ENNReal.ofReal p) volume :=
        memLp_of_lintegral_ofReal_rpow_lt_top (T j f)
          (hTmeas j f).aemeasurable (hTnonneg j f) hp0 hleft
      have hTPowInt : Integrable (fun x : Euclidean d => (T j f x) ^ p) volume := by
        have h := hMem.integrable_norm_rpow hpEN0 hpENT
        convert h using 1
        funext x
        rw [Real.norm_eq_abs, abs_of_nonneg (hTnonneg j f x),
          ENNReal.toReal_ofReal hpNN]
      have hleft_eq :
          (∫ x : Euclidean d, (T j f x) ^ p) =
            (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)).toReal := by
        exact integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun x =>
            Real.rpow_nonneg (hTnonneg j f x) p)
          hTPowInt.aestronglyMeasurable
      refine ⟨hMem, ?_⟩
      rw [hleft_eq]
      have hright_nonneg :
          0 ≤ A * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) * J := by
        exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) hJ
      calc
        (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)).toReal ≤
            (ENNReal.ofReal
              (A * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) * J)).toReal :=
          (ENNReal.toReal_le_toReal hleft.ne ENNReal.ofReal_ne_top).mpr hlin'
        _ = A * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) * J :=
          ENNReal.toReal_ofReal hright_nonneg
        _ = A * (2 : ℝ) ^ (-((d : ℝ) - 2) * j) * ∫ x : Euclidean d, ‖f x‖ ^ p := by
          dsimp only [J]
          congr 2
          ring
  /- The finite telescoping identity for `φ` reassembles the regular term and
  the first `N` annuli with a constant independent of `N`. -/
  have hfinite :
      ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
        MemLp (P N f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (P N f x) ^ p) ≤
          A * ∫ x : Euclidean d, ‖f x‖ ^ p := by
    have hφcompact : HasCompactSupport (φ : Euclidean d → ℂ) := by
      apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) 2)
      intro ξ hξ
      apply hφzero ξ
      have hlt : 2 < ‖ξ‖ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hξ
        exact lt_of_not_ge hξ
      exact hlt.le
    /- At one fixed radius, the relative low-pass multiplier is the low
    piece plus the literal finite sum of annular pieces.  The proof is kept
    at the Schwartz level until inverse Fourier linearity has been used. -/
    have hfixed : ∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
        (r : Ioi (0 : ℝ)) (x : Euclidean d),
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
          ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖ +
          ∑ j ∈ Finset.range N, ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) *
              (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
                φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖ := by
      intro N f r x
      let Ar : Euclidean d ≃L[ℝ] Euclidean d :=
        ContinuousLinearEquiv.smulLeft (Units.mk0 r.1 r.2.ne')
      let ψ : SchwartzMap (Euclidean d) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Ar φ
      have hψ (ξ : Euclidean d) : ψ ξ = φ (r.1 • ξ) := by
        change φ (Ar ξ) = φ (r.1 • ξ)
        simp [Ar]
      let A (n : ℕ) : Euclidean d ≃L[ℝ] Euclidean d :=
        ContinuousLinearEquiv.smulLeft
          (Units.mk0 ((2 : ℝ) ^ n)⁻¹ (inv_ne_zero (pow_ne_zero n (by norm_num))))
      let ψn (n : ℕ) : SchwartzMap (Euclidean d) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (A n) ψ
      have hψn (n : ℕ) (ξ : Euclidean d) :
          ψn n ξ = φ (((2 : ℝ) ^ n)⁻¹ • (r.1 • ξ)) := by
        change ψ (A n ξ) = _
        rw [hψ]
        change φ (r.1 • (((2 : ℝ) ^ n)⁻¹ • ξ)) = _
        rw [smul_smul, smul_smul]
        congr 2
        ring
      let g0 : SchwartzMap (Euclidean d) ℂ :=
        SchwartzMap.smulLeftCLM ℂ (ψn 0 : Euclidean d → ℂ) (𝓕 f)
      let gN : SchwartzMap (Euclidean d) ℂ :=
        SchwartzMap.smulLeftCLM ℂ (ψn N : Euclidean d → ℂ) (𝓕 f)
      let gj : ℕ → SchwartzMap (Euclidean d) ℂ := fun j =>
        SchwartzMap.smulLeftCLM ℂ ((ψn (j + 1) - ψn j : SchwartzMap (Euclidean d) ℂ) :
          Euclidean d → ℂ) (𝓕 f)
      have hg0 (ξ : Euclidean d) : g0 ξ =
          φ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ := by
        simp only [g0, SchwartzMap.smulLeftCLM_apply (ψn 0).hasTemperateGrowth,
          SchwartzMap.fourier_coe, smul_eq_mul]
        rw [hψn]
        norm_num
      have hgN (ξ : Euclidean d) : gN ξ =
          φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ := by
        simp only [gN, SchwartzMap.smulLeftCLM_apply (ψn N).hasTemperateGrowth,
          SchwartzMap.fourier_coe, smul_eq_mul]
        rw [hψn]
      have hgj (j : ℕ) (ξ : Euclidean d) : gj j ξ =
          (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
            φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) * 𝓕 (f : Euclidean d → ℂ) ξ := by
        simp only [gj, SchwartzMap.smulLeftCLM_apply
          (ψn (j + 1) - ψn j).hasTemperateGrowth, SchwartzMap.fourier_coe,
          smul_eq_mul, sub_apply]
        rw [hψn, hψn]
      have hmaps : gN = g0 + ∑ j ∈ Finset.range N, gj j := by
        have hsum_apply (ξ : Euclidean d) :
            (∑ j ∈ Finset.range N, gj j) ξ =
              ∑ j ∈ Finset.range N, gj j ξ := by
          change (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
            (Euclidean d) ℂ) (∑ j ∈ Finset.range N, gj j) ξ =
              ∑ j ∈ Finset.range N,
                (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
                  (Euclidean d) ℂ) (gj j) ξ
          simpa only [Finset.sum_apply] using
            congrFun (map_sum (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
              (Euclidean d) ℂ) gj (Finset.range N)) ξ
        ext ξ
        rw [add_apply, hsum_apply]
        rw [show gN ξ = φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ by exact hgN ξ]
        rw [show g0 ξ = φ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ by exact hg0 ξ]
        have htel := hφsum N (r.1 • ξ)
        rw [show (∑ j ∈ Finset.range N, gj j ξ) =
            ∑ j ∈ Finset.range N,
              (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
                φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
                𝓕 (f : Euclidean d → ℂ) ξ by
          apply Finset.sum_congr rfl
          intro j hj
          exact hgj j ξ]
        rw [← Finset.sum_mul]
        rw [htel]
        ring
      have hinv : (𝓕⁻ gN : SchwartzMap (Euclidean d) ℂ) =
          (𝓕⁻ g0 : SchwartzMap (Euclidean d) ℂ) +
            ∑ j ∈ Finset.range N, (𝓕⁻ (gj j) : SchwartzMap (Euclidean d) ℂ) := by
        rw [hmaps, fourierInv_add, fourierInv_sum]
      let F0 : Euclidean d → ℂ := (𝓕⁻ g0 : SchwartzMap (Euclidean d) ℂ)
      let FJ : ℕ → Euclidean d → ℂ := fun j => (𝓕⁻ (gj j) : SchwartzMap (Euclidean d) ℂ)
      have hFsum : (𝓕⁻ gN : SchwartzMap (Euclidean d) ℂ) =
          F0 + ∑ j ∈ Finset.range N, FJ j := by
        have hsum_apply (y : Euclidean d) :
            (∑ j ∈ Finset.range N, (𝓕⁻ (gj j) : SchwartzMap (Euclidean d) ℂ)) y =
              ∑ j ∈ Finset.range N, (𝓕⁻ (gj j) : SchwartzMap (Euclidean d) ℂ) y := by
          change (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
            (Euclidean d) ℂ) (∑ j ∈ Finset.range N,
              (𝓕⁻ (gj j) : SchwartzMap (Euclidean d) ℂ)) y =
              ∑ j ∈ Finset.range N,
                (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
                  (Euclidean d) ℂ) (𝓕⁻ (gj j) : SchwartzMap (Euclidean d) ℂ) y
          simpa only [Finset.sum_apply] using
            congrFun (map_sum (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
              (Euclidean d) ℂ) (fun j => (𝓕⁻ (gj j) : SchwartzMap (Euclidean d) ℂ))
              (Finset.range N)) y
        ext y
        rw [hinv]
        rw [add_apply, hsum_apply]
        rw [Pi.add_apply, Finset.sum_apply]
      have hcont0 : Continuous F0 := (𝓕⁻ g0 : SchwartzMap (Euclidean d) ℂ).continuous
      have hcontJ (j : ℕ) : Continuous (FJ j) :=
        (𝓕⁻ (gj j) : SchwartzMap (Euclidean d) ℂ).continuous
      have hint0 : Integrable (fun ω : Metric.sphere (0 : Euclidean d) 1 =>
          F0 (x + r.1 • (ω : Euclidean d))) (unitSurfaceMeasure d) :=
        (hcont0.comp ((continuous_const : Continuous fun _ : Metric.sphere (0 : Euclidean d) 1 => x).add
          ((continuous_const : Continuous fun _ : Metric.sphere (0 : Euclidean d) 1 => r.1).smul
            continuous_subtype_val))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hintJ (j : ℕ) : Integrable (fun ω : Metric.sphere (0 : Euclidean d) 1 =>
          FJ j (x + r.1 • (ω : Euclidean d))) (unitSurfaceMeasure d) :=
        ((hcontJ j).comp ((continuous_const : Continuous fun _ : Metric.sphere (0 : Euclidean d) 1 => x).add
          ((continuous_const : Continuous fun _ : Metric.sphere (0 : Euclidean d) 1 => r.1).smul
            continuous_subtype_val))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hsphere : sphericalAverage d ((𝓕⁻ gN : SchwartzMap (Euclidean d) ℂ) :
          Euclidean d → ℂ) r.1 x =
          sphericalAverage d F0 r.1 x +
            ∑ j ∈ Finset.range N, sphericalAverage d (FJ j) r.1 x := by
        rw [hFsum]
        unfold sphericalAverage
        simp only [Pi.add_apply, Finset.sum_apply]
        have hintSum : Integrable (fun ω : Metric.sphere (0 : Euclidean d) 1 =>
            ∑ j ∈ Finset.range N, FJ j (x + r.1 • (ω : Euclidean d)))
            (unitSurfaceMeasure d) := by
          apply integrable_finsetSum
          intro j hj
          exact hintJ j
        rw [MeasureTheory.integral_add hint0 hintSum]
        rw [MeasureTheory.integral_finsetSum (Finset.range N) (fun j _ => hintJ j)]
      have hbridgeN := sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier gN r.1
      have hbridge0 := sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier g0 r.1
      have hbridgeJ (j : ℕ) :=
        sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier (gj j) r.1
      rw [hbridgeN, hbridge0] at hsphere
      simp only [FJ] at hsphere
      rw [show (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) * gN ξ) =
          fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) *
            φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ by
        funext ξ
        rw [hgN]
        ring] at hsphere
      rw [show (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) * g0 ξ) =
          fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
            𝓕 (f : Euclidean d → ℂ) ξ by
        funext ξ
        rw [hg0]
        ring] at hsphere
      have hsphereJ (j : ℕ) :
          sphericalAverage d ((𝓕⁻ (gj j) : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ)
            r.1 x =
          𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) *
            (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
              φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x := by
        rw [hbridgeJ]
        apply congrArg (fun q : Euclidean d → ℂ => 𝓕⁻ q x)
        funext ξ
        rw [hgj]
        ring
      rw [show (∑ j ∈ Finset.range N,
          sphericalAverage d ((𝓕⁻ (gj j) : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ)
            r.1 x) =
          ∑ j ∈ Finset.range N, 𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) *
            (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
              φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x by
        apply Finset.sum_congr rfl
        intro j hj
        exact hsphereJ j] at hsphere
      exact (congrArg norm hsphere).trans_le (norm_add_le _ _ |>.trans (by
        gcongr
        exact norm_sum_le _ _))
    /- The raw suprema in `P`, `R`, and `T` are genuinely finite at each
    point.  We record the literal low-pass and two-low-pass estimates here,
    so taking `ENNReal.toReal` below does not discard an infinite value. -/
    have hlow : ∀ (f : SchwartzMap (Euclidean d) ℂ) {a : ℝ}, 0 < a →
        ∀ (r : Ioi (0 : ℝ)) (x : Euclidean d),
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) * φ (a • (r.1 • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
          (‖f.toBoundedContinuousFunction‖ *
            ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖) *
            surfaceMass d := by
      intro f a ha r x
      let R₀ : ℝ := (a * r.1)⁻¹
      have hR₀ : 0 < R₀ := inv_pos.mpr (mul_pos ha r.2)
      let A₀ : Euclidean d ≃L[ℝ] Euclidean d :=
        ContinuousLinearEquiv.smulLeft (Units.mk0 R₀⁻¹ (inv_ne_zero hR₀.ne'))
      let ψ : SchwartzMap (Euclidean d) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A₀ φ
      let h : SchwartzMap (Euclidean d) ℂ :=
        SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)
      have hψ (ξ : Euclidean d) : ψ ξ = φ (a • (r.1 • ξ)) := by
        change φ (A₀ ξ) = φ (a • (r.1 • ξ))
        change φ (R₀⁻¹ • ξ) = φ (a • (r.1 • ξ))
        dsimp only [R₀]
        rw [inv_inv]
        simp [smul_smul]
      have hh (ξ : Euclidean d) : h ξ =
          φ (a • (r.1 • ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ := by
        simp only [h, SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth,
          SchwartzMap.fourier_coe, smul_eq_mul]
        rw [hψ]
      have hbridge := sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier h r.1
      have hbound : ∀ y : Euclidean d,
          ‖(𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) y‖ ≤
            ‖f.toBoundedContinuousFunction‖ *
              ∫ z : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) z‖ := by
        intro y
        rw [SchwartzMap.fourierInv_coe]
        rw [show (h : Euclidean d → ℂ) =
            fun ξ : Euclidean d => φ (R₀⁻¹ • ξ) *
              𝓕 (f : Euclidean d → ℂ) ξ by
          funext ξ
          rw [hh]
          exact (congrArg (fun z : ℂ => z * 𝓕 (f : Euclidean d → ℂ) ξ)
            (hψ ξ)).symm]
        exact norm_fourierInv_scaled_schwartz_multiplier_le φ f hR₀
          (fun z => by
            change ‖f.toBoundedContinuousFunction z‖ ≤ ‖f.toBoundedContinuousFunction‖
            exact BoundedContinuousFunction.norm_coe_le_norm _ _) y
      calc
        ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) * φ (a • (r.1 • ξ)) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖ =
            ‖𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) * h ξ) x‖ := by
              apply congrArg (fun q : Euclidean d → ℂ => ‖𝓕⁻ q x‖)
              funext ξ
              rw [hh]
              ring
        _ = ‖sphericalAverage d ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) :
            Euclidean d → ℂ) r.1 x‖ := by
              exact congrArg norm (congrFun hbridge x).symm
        _ ≤ _ := norm_sphericalAverage_le_surfaceMass_mul d
          ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x hbound
    have hband : ∀ (f : SchwartzMap (Euclidean d) ℂ) {a b : ℝ}, 0 < a → 0 < b →
        ∀ (r : Ioi (0 : ℝ)) (x : Euclidean d),
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            (φ (a • (r.1 • ξ)) - φ (b • (r.1 • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
          2 * ((‖f.toBoundedContinuousFunction‖ *
            ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖) *
            surfaceMass d) := by
      intro f a b ha hb r x
      let Rₐ : ℝ := (a * r.1)⁻¹
      let Rᵦ : ℝ := (b * r.1)⁻¹
      have hRₐ : 0 < Rₐ := inv_pos.mpr (mul_pos ha r.2)
      have hRᵦ : 0 < Rᵦ := inv_pos.mpr (mul_pos hb r.2)
      let Aₐ : Euclidean d ≃L[ℝ] Euclidean d :=
        ContinuousLinearEquiv.smulLeft (Units.mk0 Rₐ⁻¹ (inv_ne_zero hRₐ.ne'))
      let Aᵦ : Euclidean d ≃L[ℝ] Euclidean d :=
        ContinuousLinearEquiv.smulLeft (Units.mk0 Rᵦ⁻¹ (inv_ne_zero hRᵦ.ne'))
      let ψₐ : SchwartzMap (Euclidean d) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Aₐ φ
      let ψᵦ : SchwartzMap (Euclidean d) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Aᵦ φ
      have hψₐ (ξ : Euclidean d) : ψₐ ξ = φ (a • (r.1 • ξ)) := by
        change φ (Aₐ ξ) = φ (a • (r.1 • ξ))
        change φ (Rₐ⁻¹ • ξ) = φ (a • (r.1 • ξ))
        dsimp only [Rₐ]
        rw [inv_inv]
        simp [smul_smul]
      have hψᵦ (ξ : Euclidean d) : ψᵦ ξ = φ (b • (r.1 • ξ)) := by
        change φ (Aᵦ ξ) = φ (b • (r.1 • ξ))
        change φ (Rᵦ⁻¹ • ξ) = φ (b • (r.1 • ξ))
        dsimp only [Rᵦ]
        rw [inv_inv]
        simp [smul_smul]
      have hψₐcompact : HasCompactSupport (ψₐ : Euclidean d → ℂ) := by
        change HasCompactSupport ((φ : Euclidean d → ℂ) ∘
          (Aₐ.toHomeomorph : Euclidean d → Euclidean d))
        exact hφcompact.comp_homeomorph Aₐ.toHomeomorph
      have hψᵦcompact : HasCompactSupport (ψᵦ : Euclidean d → ℂ) := by
        change HasCompactSupport ((φ : Euclidean d → ℂ) ∘
          (Aᵦ.toHomeomorph : Euclidean d → Euclidean d))
        exact hφcompact.comp_homeomorph Aᵦ.toHomeomorph
      obtain ⟨mₐ, hmₐ⟩ :=
        exists_schwartz_compactSupport_mul_surfaceFourier ψₐ hψₐcompact r.1
      obtain ⟨mᵦ, hmᵦ⟩ :=
        exists_schwartz_compactSupport_mul_surfaceFourier ψᵦ hψᵦcompact r.1
      have hsub :
          𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) *
              (φ (a • (r.1 • ξ)) - φ (b • (r.1 • ξ))) *
              𝓕 (f : Euclidean d → ℂ) ξ) x =
            𝓕⁻ (fun ξ : Euclidean d => (mₐ ξ - mᵦ ξ) *
              𝓕 (f : Euclidean d → ℂ) ξ) x := by
        apply congrArg (fun q : Euclidean d → ℂ => 𝓕⁻ q x)
        funext ξ
        rw [hmₐ, hmᵦ, hψₐ, hψᵦ]
        ring
      have hmₐ' :
          𝓕⁻ (fun ξ : Euclidean d => mₐ ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x =
            𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) *
              φ (a • (r.1 • ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x := by
        apply congrArg (fun q : Euclidean d → ℂ => 𝓕⁻ q x)
        funext ξ
        rw [hmₐ, hψₐ]
        ring
      have hmᵦ' :
          𝓕⁻ (fun ξ : Euclidean d => mᵦ ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x =
            𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) *
              φ (b • (r.1 • ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x := by
        apply congrArg (fun q : Euclidean d → ℂ => 𝓕⁻ q x)
        funext ξ
        rw [hmᵦ, hψᵦ]
        ring
      calc
        ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) *
              (φ (a • (r.1 • ξ)) - φ (b • (r.1 • ξ))) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖ =
            ‖𝓕⁻ (fun ξ : Euclidean d => (mₐ ξ - mᵦ ξ) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖ := congrArg norm hsub
        _ = ‖𝓕⁻ (fun ξ : Euclidean d => mₐ ξ *
            𝓕 (f : Euclidean d → ℂ) ξ) x -
              𝓕⁻ (fun ξ : Euclidean d => mᵦ ξ *
                𝓕 (f : Euclidean d → ℂ) ξ) x‖ := by
          rw [fourierInv_sub_schwartz_multiplier mₐ mᵦ f x]
        _ ≤ ‖𝓕⁻ (fun ξ : Euclidean d => mₐ ξ *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ +
              ‖𝓕⁻ (fun ξ : Euclidean d => mᵦ ξ *
                𝓕 (f : Euclidean d → ℂ) ξ) x‖ := norm_sub_le _ _
        _ ≤ ((‖f.toBoundedContinuousFunction‖ *
            ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖) *
              surfaceMass d) +
            ((‖f.toBoundedContinuousFunction‖ *
              ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖) *
              surfaceMass d) := by
          rw [hmₐ', hmᵦ']
          exact add_le_add (hlow f ha r x) (hlow f hb r x)
        _ = _ := by ring
    /- Taking the countable supremum after the fixed-radius identity gives
    the exact finite maximal triangle inequality used for Minkowski. -/
    have htelescoping : ∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d),
        P N f x ≤ R f x + ∑ j ∈ Finset.range N, T j f x := by
      intro N f x
      let pval : Ioi (0 : ℝ) → ℝ := fun r =>
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖
      let rval : Ioi (0 : ℝ) → ℝ := fun r =>
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖
      let tval : ℕ → Ioi (0 : ℝ) → ℝ := fun j r =>
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
              φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖
      let C : ℝ := (‖f.toBoundedContinuousFunction‖ *
        ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖) * surfaceMass d
      have hRbound (r : Ioi (0 : ℝ)) : rval r ≤ C := by
        dsimp only [rval, C]
        simpa only [one_smul] using (hlow f (a := 1) zero_lt_one r x)
      have hRbdd : BddAbove (Set.range rval) := by
        refine ⟨C, ?_⟩
        rintro _ ⟨r, rfl⟩
        exact hRbound r
      have hTbound (j : ℕ) (r : Ioi (0 : ℝ)) : tval j r ≤ 2 * C := by
        have ha : 0 < ((2 : ℝ) ^ (j + 1))⁻¹ :=
          inv_pos.mpr (pow_pos (by norm_num) _)
        have hb : 0 < ((2 : ℝ) ^ j)⁻¹ :=
          inv_pos.mpr (pow_pos (by norm_num) _)
        dsimp only [tval, C]
        exact hband f ha hb r x
      have hTbdd (j : ℕ) : BddAbove (Set.range (tval j)) := by
        refine ⟨2 * C, ?_⟩
        rintro _ ⟨r, rfl⟩
        exact hTbound j r
      letI : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
      have hsup : (⨆ r : Ioi (0 : ℝ), pval r) ≤
          (⨆ r : Ioi (0 : ℝ), rval r) +
            ∑ j ∈ Finset.range N, ⨆ r : Ioi (0 : ℝ), tval j r := by
        apply ciSup_le
        intro r
        calc
          pval r ≤ rval r + ∑ j ∈ Finset.range N, tval j r := hfixed N f r x
          _ ≤ (⨆ r : Ioi (0 : ℝ), rval r) +
              ∑ j ∈ Finset.range N, ⨆ r : Ioi (0 : ℝ), tval j r := by
            apply add_le_add
            · exact le_ciSup hRbdd r
            · apply Finset.sum_le_sum
              intro j hj
              exact le_ciSup (hTbdd j) r
      change (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal (pval r)).toReal ≤
        (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal (rval r)).toReal +
          ∑ j ∈ Finset.range N,
            (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal (tval j r)).toReal
      simp_rw [ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
      simpa [pval, rval, tval, ENNReal.toReal_ofReal] using hsup
    /- The cutoff maximal function is measurable because each fixed-radius
    multiplier can again be written as a scaled Schwartz multiplier. -/
    have hPmeas (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
        AEStronglyMeasurable (P N f) volume := by
      let A₀ : Euclidean d ≃L[ℝ] Euclidean d :=
        ContinuousLinearEquiv.smulLeft
          (Units.mk0 ((2 : ℝ) ^ N)⁻¹ (inv_ne_zero (pow_ne_zero N (by norm_num))))
      let ψ : SchwartzMap (Euclidean d) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A₀ φ
      have hψ (ξ : Euclidean d) : ψ ξ = φ (((2 : ℝ) ^ N)⁻¹ • ξ) := by
        change φ (A₀ ξ) = _
        simp [A₀]
      have hψcompact : HasCompactSupport (ψ : Euclidean d → ℂ) := by
        change HasCompactSupport ((φ : Euclidean d → ℂ) ∘
          (A₀.toHomeomorph : Euclidean d → Euclidean d))
        exact hφcompact.comp_homeomorph A₀.toHomeomorph
      obtain ⟨χ, hχ⟩ :=
        exists_schwartz_compactSupport_mul_surfaceFourier ψ hψcompact 1
      have hχ' (ξ : Euclidean d) :
          χ ξ = ψ ξ * surfaceFourier d (-ξ) := by
        simpa using hχ ξ
      have hrewrite : P N f = fun x : Euclidean d =>
          (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
            χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal := by
        funext x
        dsimp only [P]
        congr 1
        apply iSup_congr
        intro r
        congr 2
        apply congrArg (fun g : Euclidean d → ℂ => 𝓕⁻ g x)
        funext ξ
        rw [hχ', hψ]
        simp only [neg_smul]
        ring
      rw [hrewrite]
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
    obtain ⟨B, hB, hreg⟩ := hregular
    obtain ⟨A, ε, hA, hε, hdy⟩ := hdyadic
    have hdreal : (2 : ℝ) < d := by
      exact_mod_cast (show 2 < d by omega)
    have hdenom : 0 < (d : ℝ) - 1 := by linarith
    have hcritical : 1 < (d : ℝ) / ((d : ℝ) - 1) := by
      rw [lt_div_iff₀ hdenom]
      nlinarith
    have hpone : 1 < p := hcritical.trans hp
    have hp0 : 0 < p := lt_trans zero_lt_one hpone
    have hpNN : 0 ≤ p := hp0.le
    have hpE0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
    have hpET : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
    have hpENN : (1 : ENNReal) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hpone.le
    let ρ : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (-ε / p))
    let CT : ENNReal := ENNReal.ofReal (A ^ p⁻¹)
    let CR : ENNReal := ENNReal.ofReal (B ^ p⁻¹)
    let D : ENNReal := CR + CT * (1 - ρ)⁻¹
    have hρreal : (2 : ℝ) ^ (-ε / p) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · norm_num
      · exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hε) hp0
    have hρ : ρ < 1 := by
      dsimp only [ρ]
      exact ENNReal.ofReal_lt_one.mpr hρreal
    have hρpos : 0 < 1 - ρ := tsub_pos_of_lt hρ
    have hρinvtop : (1 - ρ)⁻¹ < ⊤ := ENNReal.inv_lt_top.mpr hρpos
    have hCRtop : CR < ⊤ := by
      dsimp only [CR]
      exact ENNReal.ofReal_lt_top
    have hCTtop : CT < ⊤ := by
      dsimp only [CT]
      exact ENNReal.ofReal_lt_top
    have hDtop : D < ⊤ := by
      dsimp only [D]
      exact ENNReal.add_lt_top.mpr
        ⟨hCRtop, ENNReal.mul_lt_top hCTtop hρinvtop⟩
    let C : ℝ := D.toReal ^ p + 1
    have hC : 0 < C := by
      dsimp only [C]
      positivity
    refine ⟨C, hC, ?_⟩
    intro N f
    let I : ℝ := ∫ x : Euclidean d, ‖f x‖ ^ p
    have hI : 0 ≤ I := by
      dsimp only [I]
      exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
    let hroot : ENNReal := ENNReal.ofReal (I ^ p⁻¹)
    have hR0 (x : Euclidean d) : 0 ≤ R f x := by
      dsimp only [R]
      exact ENNReal.toReal_nonneg
    have hT0 (j : ℕ) (x : Euclidean d) : 0 ≤ T j f x := by
      dsimp only [T]
      exact ENNReal.toReal_nonneg
    have hP0 (x : Euclidean d) : 0 ≤ P N f x := by
      dsimp only [P]
      exact ENNReal.toReal_nonneg
    have hRnorm : eLpNorm (R f) (ENNReal.ofReal p) volume ≤ CR * hroot := by
      rw [(hreg f).1.eLpNorm_eq_integral_rpow_norm hpE0 hpET]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hB.le _)]
      rw [← Real.mul_rpow hB.le hI]
      apply ENNReal.ofReal_le_ofReal
      rw [ENNReal.toReal_ofReal hpNN]
      apply Real.rpow_le_rpow
      · exact integral_nonneg fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hR0 x)]
          exact Real.rpow_nonneg (hR0 x) p
      · calc
          (∫ x : Euclidean d, ‖R f x‖ ^ p) = ∫ x : Euclidean d, (R f x) ^ p := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Real.norm_eq_abs, abs_of_nonneg (hR0 x)]
          _ ≤ B * I := by simpa only [I] using (hreg f).2
      · exact inv_nonneg.mpr hpNN
    have hTnorm (j : ℕ) : eLpNorm (T j f) (ENNReal.ofReal p) volume ≤
        (CT * hroot) * ρ ^ j := by
      calc
        eLpNorm (T j f) (ENNReal.ofReal p) volume ≤
            ENNReal.ofReal ((A * (2 : ℝ) ^ (-ε * (j : ℝ)) * I) ^ p⁻¹) := by
          rw [(hdy j f).1.eLpNorm_eq_integral_rpow_norm hpE0 hpET]
          apply ENNReal.ofReal_le_ofReal
          rw [ENNReal.toReal_ofReal hpNN]
          apply Real.rpow_le_rpow
          · exact integral_nonneg fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hT0 j x)]
              exact Real.rpow_nonneg (hT0 j x) p
          · calc
              (∫ x : Euclidean d, ‖T j f x‖ ^ p) =
                  ∫ x : Euclidean d, (T j f x) ^ p := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Real.norm_eq_abs, abs_of_nonneg (hT0 j x)]
              _ ≤ A * (2 : ℝ) ^ (-ε * j) * I := by
                simpa only [I] using (hdy j f).2
          · exact inv_nonneg.mpr hpNN
        _ = (CT * hroot) * ρ ^ j := by
          dsimp only [CT, hroot, ρ]
          rw [show (A * (2 : ℝ) ^ (-ε * (j : ℝ)) * I) ^ p⁻¹ =
              (A ^ p⁻¹ * I ^ p⁻¹) * ((2 : ℝ) ^ (-ε / p)) ^ j by
            rw [show A * (2 : ℝ) ^ (-ε * (j : ℝ)) * I =
                (A * I) * (2 : ℝ) ^ (-ε * (j : ℝ)) by ring]
            rw [Real.mul_rpow (mul_nonneg hA.le hI) (Real.rpow_nonneg (by norm_num) _)]
            rw [Real.mul_rpow hA.le hI]
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            rw [show (-ε * (j : ℝ)) * p⁻¹ = (-ε / p) * (j : ℝ) by
              field_simp]
            exact Real.rpow_mul_natCast (by norm_num) _ _]
          rw [ENNReal.ofReal_mul
            (mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hI _))]
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _)]
          rw [ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _) j]
    let S : ℕ → Euclidean d → ℝ := fun n x => ∑ j ∈ Finset.range n, T j f x
    have hSmem (n : ℕ) : MemLp (S n) (ENNReal.ofReal p) volume := by
      induction n with
      | zero =>
        change MemLp 0 (ENNReal.ofReal p) volume
        exact MemLp.zero
      | succ n ih =>
        have hsum := ih.add (hdy n f).1
        convert hsum using 1
        funext x
        simp only [S, Finset.sum_range_succ, Pi.add_apply]
    have hSnorm : eLpNorm (S N) (ENNReal.ofReal p) volume ≤
        (CT * hroot) * (1 - ρ)⁻¹ := by
      apply eLpNorm_sum_range_le_geometric volume (ENNReal.ofReal p) hpENN
        (fun j => T j f)
      · intro j
        exact (hdy j f).1.1
      · exact hTnorm
    have hS0 (x : Euclidean d) : 0 ≤ S N x := by
      dsimp only [S]
      exact Finset.sum_nonneg fun j _ => hT0 j x
    let Q : ℕ → Euclidean d → ℝ := fun n x => R f x + S n x
    have hQmem (n : ℕ) : MemLp (Q n) (ENNReal.ofReal p) volume := by
      dsimp only [Q]
      exact (hreg f).1.add (hSmem n)
    have hPmem : MemLp (P N f) (ENNReal.ofReal p) volume := by
      apply (hQmem N).mono (hPmeas N f)
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x), Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (hR0 x) (hS0 x))]
      simpa only [Q, S] using htelescoping N f x
    have hPnorm : eLpNorm (P N f) (ENNReal.ofReal p) volume ≤ D * hroot := by
      calc
        eLpNorm (P N f) (ENNReal.ofReal p) volume ≤
            eLpNorm (Q N) (ENNReal.ofReal p) volume := by
              apply eLpNorm_mono
              intro x
              rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x), Real.norm_eq_abs,
                abs_of_nonneg (add_nonneg (hR0 x) (hS0 x))]
              simpa only [Q, S] using htelescoping N f x
        _ ≤ eLpNorm (R f) (ENNReal.ofReal p) volume +
            eLpNorm (S N) (ENNReal.ofReal p) volume := by
              change eLpNorm (R f + S N) _ _ ≤ _
              exact eLpNorm_add_le (hreg f).1.1 (hSmem N).1 hpENN
        _ ≤ CR * hroot + (CT * hroot) * (1 - ρ)⁻¹ := by
              exact add_le_add hRnorm hSnorm
        _ = D * hroot := by
              dsimp only [D]
              ring
    refine ⟨hPmem, ?_⟩
    change (∫ x : Euclidean d, (P N f x) ^ p) ≤ C * I
    have hPint0 : 0 ≤ ∫ x : Euclidean d, (P N f x) ^ p :=
      integral_nonneg fun x => Real.rpow_nonneg (hP0 x) p
    have hrootbound : (∫ x : Euclidean d, (P N f x) ^ p) ^ p⁻¹ ≤
        D.toReal * (I ^ p⁻¹) := by
      have hnorm : ENNReal.ofReal ((∫ x : Euclidean d, (P N f x) ^ p) ^ p⁻¹) ≤
          D * hroot := by
        have hPnormEq : eLpNorm (P N f) (ENNReal.ofReal p) volume =
            ENNReal.ofReal ((∫ x : Euclidean d, (P N f x) ^ p) ^ p⁻¹) := by
          rw [hPmem.eLpNorm_eq_integral_rpow_norm hpE0 hpET,
            ENNReal.toReal_ofReal hpNN]
          apply congrArg ENNReal.ofReal
          apply congrArg (fun z : ℝ => z ^ p⁻¹)
          apply integral_congr_ae
          filter_upwards with x
          rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x)]
        rw [← hPnormEq]
        exact hPnorm
      calc
        (∫ x : Euclidean d, (P N f x) ^ p) ^ p⁻¹ =
            (ENNReal.ofReal ((∫ x : Euclidean d, (P N f x) ^ p) ^ p⁻¹)).toReal := by
              rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hPint0 _)]
        _ ≤ (D * hroot).toReal :=
          (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
            (ENNReal.mul_ne_top hDtop.ne ENNReal.ofReal_ne_top)).mpr hnorm
        _ = D.toReal * (I ^ p⁻¹) := by
          simp only [hroot, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)]
    have hraised :=
      Real.rpow_le_rpow (Real.rpow_nonneg hPint0 _) hrootbound hpNN
    calc
      (∫ x : Euclidean d, (P N f x) ^ p) =
          ((∫ x : Euclidean d, (P N f x) ^ p) ^ p⁻¹) ^ p := by
            rw [Real.rpow_inv_rpow hPint0 (ne_of_gt hp0)]
      _ ≤ (D.toReal * (I ^ p⁻¹)) ^ p := hraised
      _ = D.toReal ^ p * I := by
            rw [Real.mul_rpow ENNReal.toReal_nonneg (Real.rpow_nonneg hI _)]
            rw [Real.rpow_inv_rpow hI (ne_of_gt hp0)]
      _ ≤ C * I := by
            dsimp only [C]
            exact mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (by norm_num)) hI
  /- Finally `φ (2⁻ᴺ r ξ) → 1` for each radius; the pointwise liminf and
  Fatou transfer the uniform finite estimate to the literal maximal
  operator.  `P` is written for the unnormalized surface multiplier, so this
  last step also inserts the fixed factor `(surfaceMass d)⁻¹` in the target
  normalized maximal function. -/
  have hlimit : ∀ A : ℝ, 0 < A →
      (∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
        MemLp (P N f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (P N f x) ^ p) ≤
          A * ∫ x : Euclidean d, ‖f x‖ ^ p) →
      ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
        MemLp (M f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (M f x) ^ p) ≤
          C * ∫ x : Euclidean d, ‖f x‖ ^ p := by
    intro A hA hfinite
    have hd0 : 0 < d := by omega
    have hmass : 0 < surfaceMass d := surfaceMass_pos hd0
    have hp0 : 0 < p := by
      have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have hden : 0 < (d : ℝ) - 1 := by linarith
      have hfrac : 0 < (d : ℝ) / ((d : ℝ) - 1) := by
        apply div_pos <;> linarith
      exact lt_trans hfrac hp
    have hpNN : 0 ≤ p := hp0.le
    have hφbound (ξ : Euclidean d) : ‖φ ξ‖ ≤ ‖φ.toBoundedContinuousFunction‖ := by
      change ‖φ.toBoundedContinuousFunction ξ‖ ≤ ‖φ.toBoundedContinuousFunction‖
      exact BoundedContinuousFunction.norm_coe_le_norm _ _
    /- At a fixed radius the low-frequency cutoff tends to one.  We prove
    this at the level of the literal inverse Fourier integral, with the
    integrable Schwartz transform as a common dominator. -/
    have hcutoff_tendsto (f : SchwartzMap (Euclidean d) ℂ) (r : ℝ)
        (x : Euclidean d) :
        Tendsto (fun N : ℕ =>
          𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r • ξ) *
              φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ)) *
              𝓕 (f : Euclidean d → ℂ) ξ) x) atTop
          (𝓝 (sphericalAverage d (f : Euclidean d → ℂ) r x)) := by
      have hchar (ξ : Euclidean d) : ‖(Real.fourierChar (inner ℝ ξ x) : ℂ)‖ = 1 := by
        rw [Real.fourierChar_apply]
        exact Complex.norm_exp_ofReal_mul_I _
      have hchar_cont : Continuous
          (fun ξ : Euclidean d => (Real.fourierChar (inner ℝ ξ x) : ℂ)) :=
        (Real.continuous_fourierChar.comp
          (continuous_id.inner (continuous_const : Continuous fun _ : Euclidean d => x))
          |> continuous_subtype_val.comp)
      let F : ℕ → Euclidean d → ℂ := fun N ξ =>
        (Real.fourierChar (inner ℝ ξ x) : ℂ) *
          (surfaceFourier d (-r • ξ) *
            φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ)
      let G : Euclidean d → ℂ := fun ξ =>
        (Real.fourierChar (inner ℝ ξ x) : ℂ) *
          (surfaceFourier d (-r • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ)
      have hFmeas (N : ℕ) : AEStronglyMeasurable (F N) volume := by
        dsimp only [F]
        have hsurf : Continuous (fun ξ : Euclidean d => surfaceFourier d (-r • ξ)) :=
          (continuous_surfaceFourier d).comp
            ((continuous_const : Continuous fun _ : Euclidean d => -r).smul continuous_id)
        have hcut : Continuous (fun ξ : Euclidean d =>
            φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ))) :=
          φ.continuous.comp
            ((continuous_const : Continuous fun _ : Euclidean d => ((2 : ℝ) ^ N)⁻¹).smul
              ((continuous_const : Continuous fun _ : Euclidean d => r).smul continuous_id))
        exact (hchar_cont.mul ((hsurf.mul hcut).mul (𝓕 f).continuous)).aestronglyMeasurable
      let B : ℝ := surfaceMass d * ‖φ.toBoundedContinuousFunction‖
      have hB : 0 ≤ B := by
        dsimp only [B]
        positivity
      have hbound_int : Integrable (fun ξ : Euclidean d =>
          B * ‖𝓕 (f : Euclidean d → ℂ) ξ‖) volume :=
        (𝓕 f).integrable.norm.const_mul B
      have hbound (N : ℕ) : ∀ᵐ ξ : Euclidean d ∂volume,
          ‖F N ξ‖ ≤ B * ‖𝓕 (f : Euclidean d → ℂ) ξ‖ := by
        filter_upwards with ξ
        dsimp only [F]
        rw [norm_mul, hchar, one_mul, norm_mul, norm_mul]
        calc
          ‖surfaceFourier d (-r • ξ)‖ * ‖φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ))‖ *
              ‖𝓕 (f : Euclidean d → ℂ) ξ‖ ≤
              (surfaceMass d * ‖φ.toBoundedContinuousFunction‖) *
                ‖𝓕 (f : Euclidean d → ℂ) ξ‖ := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul
                (by simpa [surfaceMass] using
                  norm_surfaceFourier_le_surfaceMass d (-r • ξ))
                (hφbound _)
                (norm_nonneg _) hmass.le
            · exact norm_nonneg _
          _ = B * ‖𝓕 (f : Euclidean d → ℂ) ξ‖ := rfl
      have hscale (ξ : Euclidean d) : Tendsto (fun N : ℕ =>
          ((2 : ℝ) ^ N)⁻¹ • (r • ξ)) atTop (𝓝 0) := by
        have hpow : Tendsto (fun N : ℕ => ((2 : ℝ)⁻¹) ^ N) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        have hconst : Tendsto (fun _ : ℕ => r • ξ) atTop (𝓝 (r • ξ)) :=
          tendsto_const_nhds
        simpa [inv_pow] using hpow.smul hconst
      have hφlim (ξ : Euclidean d) : Tendsto (fun N : ℕ =>
          φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ))) atTop (𝓝 (1 : ℂ)) := by
        have hzero : φ (0 : Euclidean d) = 1 := hφone 0 (by simp)
        rw [← hzero]
        exact φ.continuous.tendsto 0 |>.comp (hscale ξ)
      have hFlim : ∀ᵐ ξ : Euclidean d ∂volume,
          Tendsto (fun N : ℕ => F N ξ) atTop (𝓝 (G ξ)) := by
        filter_upwards with ξ
        dsimp only [F, G]
        have hchar' : Tendsto
            (fun _ : ℕ => (Real.fourierChar (inner ℝ ξ x) : ℂ)) atTop
            (𝓝 (Real.fourierChar (inner ℝ ξ x) : ℂ)) := tendsto_const_nhds
        have hsurf' : Tendsto (fun _ : ℕ => surfaceFourier d (-r • ξ)) atTop
            (𝓝 (surfaceFourier d (-r • ξ))) := tendsto_const_nhds
        have hfourier' : Tendsto (fun _ : ℕ => 𝓕 (f : Euclidean d → ℂ) ξ) atTop
            (𝓝 (𝓕 (f : Euclidean d → ℂ) ξ)) := tendsto_const_nhds
        simpa using hchar'.mul ((hsurf'.mul (hφlim ξ)).mul hfourier')
      have hInt := tendsto_integral_of_dominated_convergence
        (F := F) (f := G) (fun ξ : Euclidean d =>
          B * ‖𝓕 (f : Euclidean d → ℂ) ξ‖)
        hFmeas hbound_int hbound hFlim
      rw [show (fun N : ℕ =>
          𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r • ξ) *
              φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ)) *
              𝓕 (f : Euclidean d → ℂ) ξ) x) =
          fun N => ∫ ξ : Euclidean d, F N ξ by
            funext N
            rw [Real.fourierInv_eq]
            rfl,
        show sphericalAverage d (f : Euclidean d → ℂ) r x = ∫ ξ : Euclidean d, G ξ by
            rw [sphericalAverage_eq_fourierInv_surfaceMultiplier_schwartz f r,
              Real.fourierInv_eq]
            rfl]
      exact hInt
    let Q : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ENNReal :=
      fun N f x =>
        ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖
    /- The `toReal` in `P` is harmless: every cutoff supremum has a finite
    uniform Fourier-integral bound for a Schwartz input. -/
    have hQfinite (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
        Q N f x ≠ ⊤ := by
      let B : ℝ := surfaceMass d * ‖φ.toBoundedContinuousFunction‖
      have hB : 0 ≤ B := by
        dsimp only [B]
        positivity
      apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      apply iSup_le
      intro r
      apply ENNReal.ofReal_le_ofReal
      rw [Real.fourierInv_eq]
      change ‖∫ ξ : Euclidean d, (Real.fourierChar (inner ℝ ξ x) : ℂ) *
        (surfaceFourier d (-r.1 • ξ) *
          φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ)‖ ≤ _
      calc
        ‖∫ ξ : Euclidean d, (Real.fourierChar (inner ℝ ξ x) : ℂ) *
            (surfaceFourier d (-r.1 • ξ) *
              φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
              𝓕 (f : Euclidean d → ℂ) ξ)‖ ≤
            ∫ ξ : Euclidean d, ‖(Real.fourierChar (inner ℝ ξ x) : ℂ) *
              (surfaceFourier d (-r.1 • ξ) *
                φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
                𝓕 (f : Euclidean d → ℂ) ξ)‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ ξ : Euclidean d, B * ‖𝓕 (f : Euclidean d → ℂ) ξ‖ := by
          apply integral_mono_ae
          · refine ((𝓕 f).integrable.norm.const_mul B).mono' ?_ ?_
            · have hchar_cont : Continuous
                (fun ξ : Euclidean d => (Real.fourierChar (inner ℝ ξ x) : ℂ)) :=
                (Real.continuous_fourierChar.comp
                  (continuous_id.inner (continuous_const : Continuous fun _ : Euclidean d => x))
                  |> continuous_subtype_val.comp)
              have hsurf : Continuous (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ)) :=
                (continuous_surfaceFourier d).comp
                  ((continuous_const : Continuous fun _ : Euclidean d => -r.1).smul continuous_id)
              have hcut : Continuous (fun ξ : Euclidean d =>
                  φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ))) :=
                φ.continuous.comp
                  ((continuous_const : Continuous fun _ : Euclidean d => ((2 : ℝ) ^ N)⁻¹).smul
                    ((continuous_const : Continuous fun _ : Euclidean d => r.1).smul continuous_id))
              exact ((hchar_cont.mul ((hsurf.mul hcut).mul (𝓕 f).continuous)).norm).aestronglyMeasurable
            · filter_upwards with ξ
              dsimp only [B]
              have hchar : ‖(Real.fourierChar (inner ℝ ξ x) : ℂ)‖ = 1 := by
                rw [Real.fourierChar_apply]
                exact Complex.norm_exp_ofReal_mul_I _
              simp only [norm_mul, norm_norm, hchar, one_mul]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul
                  (by simpa [surfaceMass] using
                    norm_surfaceFourier_le_surfaceMass d (-r.1 • ξ))
                  (hφbound _)
                  (norm_nonneg _) hmass.le)
                (norm_nonneg _)
          · exact (𝓕 f).integrable.norm.const_mul B
          · filter_upwards with ξ
            dsimp only [B]
            have hchar : ‖(Real.fourierChar (inner ℝ ξ x) : ℂ)‖ = 1 := by
              rw [Real.fourierChar_apply]
              exact Complex.norm_exp_ofReal_mul_I _
            simp only [norm_mul, norm_norm, hchar, one_mul]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul
                (by simpa [surfaceMass] using
                  norm_surfaceFourier_le_surfaceMass d (-r.1 • ξ))
                (hφbound _)
                (norm_nonneg _) hmass.le)
              (norm_nonneg _)
        _ = B * ∫ ξ : Euclidean d, ‖𝓕 (f : Euclidean d → ℂ) ξ‖ := by
          rw [integral_const_mul]
    let U : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
      fun N f x => (Q N f x).toReal
    let V : SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
      fun f x => (normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal
    have hfiniteU : ∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
        MemLp (U N f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (U N f x) ^ p) ≤
          A * ∫ x : Euclidean d, ‖f x‖ ^ p := by
      intro N f
      simpa only [U, Q, P] using hfinite N f
    have hU_Q (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
        ENNReal.ofReal (U N f x) = Q N f x := by
      exact ENNReal.ofReal_toReal (hQfinite N f x)
    have hfixed (f : SchwartzMap (Euclidean d) ℂ)
        (r : Ioi (0 : ℝ)) (x : Euclidean d) :
        ENNReal.ofReal (‖sphericalAverage d (f : Euclidean d → ℂ) r.1 x‖ ^ p) ≤
          liminf (fun N : ℕ => ENNReal.ofReal ((U N f x) ^ p)) atTop := by
      let W : ℕ → ℂ := fun N => 𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) *
          φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x
      have hW : Tendsto W atTop
          (𝓝 (sphericalAverage d (f : Euclidean d → ℂ) r.1 x)) := by
        simpa only [W] using hcutoff_tendsto f r.1 x
      have hE : Tendsto (fun N : ℕ => ENNReal.ofReal ‖W N‖) atTop
          (𝓝 (ENNReal.ofReal ‖sphericalAverage d (f : Euclidean d → ℂ) r.1 x‖)) :=
        (ENNReal.continuous_ofReal.tendsto _).comp hW.norm
      have hPow : Tendsto (fun N : ℕ => (ENNReal.ofReal ‖W N‖) ^ p) atTop
          (𝓝 ((ENNReal.ofReal ‖sphericalAverage d (f : Euclidean d → ℂ) r.1 x‖) ^ p)) :=
        (ENNReal.continuous_rpow_const.tendsto _).comp hE
      have hPow' : Tendsto (fun N : ℕ => ENNReal.ofReal (‖W N‖ ^ p)) atTop
          (𝓝 (ENNReal.ofReal (‖sphericalAverage d (f : Euclidean d → ℂ) r.1 x‖ ^ p))) := by
        simpa only [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpNN] using hPow
      have hle (N : ℕ) : ENNReal.ofReal (‖W N‖ ^ p) ≤
          ENNReal.ofReal ((U N f x) ^ p) := by
        have hU_nonneg : 0 ≤ U N f x := ENNReal.toReal_nonneg
        rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpNN,
          ← ENNReal.ofReal_rpow_of_nonneg hU_nonneg hpNN]
        apply ENNReal.rpow_le_rpow _ hpNN
        rw [hU_Q]
        dsimp only [Q, W]
        exact le_iSup (fun s : Ioi (0 : ℝ) => ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-s.1 • ξ) *
            φ (((2 : ℝ) ^ N)⁻¹ • (s.1 • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖) r
      calc
        ENNReal.ofReal (‖sphericalAverage d (f : Euclidean d → ℂ) r.1 x‖ ^ p) =
            liminf (fun N : ℕ => ENNReal.ofReal (‖W N‖ ^ p)) atTop := hPow'.liminf_eq.symm
        _ ≤ liminf (fun N : ℕ => ENNReal.ofReal ((U N f x) ^ p)) atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)
    let K : ENNReal := (ENNReal.ofReal ((surfaceMass d)⁻¹)) ^ p
    have hKtop : K ≠ ⊤ := by
      dsimp only [K]
      exact ENNReal.rpow_ne_top_of_nonneg hpNN ENNReal.ofReal_ne_top
    have hKpos : 0 < K := by
      dsimp only [K]
      apply ENNReal.rpow_pos
      · exact ENNReal.ofReal_pos.mpr (inv_pos.mpr hmass)
      · exact ENNReal.ofReal_ne_top
    have hnorm (f : SchwartzMap (Euclidean d) ℂ)
        (r : ℝ) (x : Euclidean d) :
        ENNReal.ofReal (‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r x‖ ^ p) =
          K * ENNReal.ofReal (‖sphericalAverage d (f : Euclidean d → ℂ) r x‖ ^ p) := by
      dsimp only [K]
      rw [normalizedSphericalAverage, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hmass]
      rw [Real.mul_rpow (inv_nonneg.mpr hmass.le) (norm_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hmass.le) p)]
      rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hmass.le) hpNN]
    have hnormalfixed (f : SchwartzMap (Euclidean d) ℂ)
        (r : Ioi (0 : ℝ)) (x : Euclidean d) :
        ENNReal.ofReal (‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r.1 x‖ ^ p) ≤
          K * liminf (fun N : ℕ => ENNReal.ofReal ((U N f x) ^ p)) atTop := by
      rw [hnorm]
      exact mul_le_mul_right (hfixed f r x) K
    have hVtop (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
        normalizedSphericalMaximal d (f : Euclidean d → ℂ) x ≠ ⊤ := by
      apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      apply normalizedSphericalMaximal_le_of_norm_le hd0 _ x
      intro y
      change ‖f.toBoundedContinuousFunction y‖ ≤ ‖f.toBoundedContinuousFunction‖
      exact BoundedContinuousFunction.norm_coe_le_norm _ _
    have hV_eq (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
        ENNReal.ofReal (V f x) = normalizedSphericalMaximal d (f : Euclidean d → ℂ) x := by
      exact ENNReal.ofReal_toReal (hVtop f x)
    have hpoint (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
        ENNReal.ofReal ((V f x) ^ p) ≤
          K * liminf (fun N : ℕ => ENNReal.ofReal ((U N f x) ^ p)) atTop := by
      have hVnonneg : 0 ≤ V f x := ENNReal.toReal_nonneg
      rw [← ENNReal.ofReal_rpow_of_nonneg hVnonneg hpNN, hV_eq]
      unfold normalizedSphericalMaximal
      have hpowmax :
          (⨆ r : Ioi (0 : ℝ),
            ENNReal.ofReal ‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r.1 x‖) ^ p =
            ⨆ r : Ioi (0 : ℝ),
              (ENNReal.ofReal ‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r.1 x‖) ^ p := by
        let e : ENNReal ≃o ENNReal :=
          (ENNReal.strictMono_rpow_of_pos hp0).orderIsoOfSurjective _
            (ENNReal.rpow_left_bijective hp0.ne.symm).2
        change e (⨆ r : Ioi (0 : ℝ),
          ENNReal.ofReal ‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r.1 x‖) =
            ⨆ r : Ioi (0 : ℝ),
              e (ENNReal.ofReal ‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r.1 x‖)
        exact e.map_iSup _
      rw [hpowmax]
      apply iSup_le
      intro r
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpNN]
      exact hnormalfixed f r x
    have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
    have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
    have hUmeas (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
        AEMeasurable (fun x : Euclidean d => ENNReal.ofReal ((U N f x) ^ p)) volume := by
      have hmeas : AEMeasurable (fun x : Euclidean d =>
          (ENNReal.ofReal (U N f x)) ^ p) volume :=
        ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          ((hfiniteU N f).1.1.aemeasurable.ennreal_ofReal)
      convert hmeas using 1
      funext x
      exact (ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hpNN).symm
    have hUPowInt (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
        Integrable (fun x : Euclidean d => (U N f x) ^ p) volume := by
      have h := (hfiniteU N f).1.integrable_norm_rpow hpEN0 hpENT
      convert h using 1
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.toReal_ofReal hpNN]
    have hUint (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
        (∫⁻ x : Euclidean d, ENNReal.ofReal ((U N f x) ^ p)) ≤
          ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) := by
      calc
        (∫⁻ x : Euclidean d, ENNReal.ofReal ((U N f x) ^ p)) =
            ENNReal.ofReal (∫ x : Euclidean d, (U N f x) ^ p) := by
          rw [ofReal_integral_eq_lintegral_ofReal (hUPowInt N f)]
          exact Filter.Eventually.of_forall fun x =>
            Real.rpow_nonneg ENNReal.toReal_nonneg p
        _ ≤ ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) :=
          ENNReal.ofReal_le_ofReal (hfiniteU N f).2
    have hFatou (f : SchwartzMap (Euclidean d) ℂ) :
        (∫⁻ x : Euclidean d, ENNReal.ofReal ((V f x) ^ p)) ≤
          K * liminf (fun N : ℕ =>
            ∫⁻ x : Euclidean d, ENNReal.ofReal ((U N f x) ^ p)) atTop := by
      calc
        (∫⁻ x : Euclidean d, ENNReal.ofReal ((V f x) ^ p)) ≤
            ∫⁻ x : Euclidean d, K *
              liminf (fun N : ℕ => ENNReal.ofReal ((U N f x) ^ p)) atTop :=
          lintegral_mono (fun x => hpoint f x)
        _ = K * (∫⁻ x : Euclidean d,
            liminf (fun N : ℕ => ENNReal.ofReal ((U N f x) ^ p)) atTop) :=
          lintegral_const_mul' K _ hKtop
        _ ≤ K * liminf (fun N : ℕ =>
            ∫⁻ x : Euclidean d, ENNReal.ofReal ((U N f x) ^ p)) atTop :=
          mul_le_mul_right (lintegral_liminf_le' fun N => hUmeas N f) K
    have hLiminfBound (f : SchwartzMap (Euclidean d) ℂ) :
        liminf (fun N : ℕ =>
          ∫⁻ x : Euclidean d, ENNReal.ofReal ((U N f x) ^ p)) atTop ≤
          ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) := by
      exact Filter.liminf_le_of_frequently_le'
        (Filter.Frequently.of_forall fun N => hUint N f)
    have hlin (f : SchwartzMap (Euclidean d) ℂ) :
        (∫⁻ x : Euclidean d, ENNReal.ofReal ((V f x) ^ p)) ≤
          K * ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) :=
      (hFatou f).trans (mul_le_mul_right (hLiminfBound f) K)
    let C : ℝ := K.toReal * A
    have hKrealpos : 0 < K.toReal := ENNReal.toReal_pos hKpos.ne' hKtop
    refine ⟨C, mul_pos hKrealpos hA, ?_⟩
    intro f
    have hinput_nonneg : 0 ≤ ∫ x : Euclidean d, ‖f x‖ ^ p :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
    have hright_nonneg : 0 ≤ A * ∫ x : Euclidean d, ‖f x‖ ^ p :=
      mul_nonneg hA.le hinput_nonneg
    have hrighttop : K * ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) < ⊤ :=
      ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hKtop) ENNReal.ofReal_lt_top
    have hlefttop : (∫⁻ x : Euclidean d, ENNReal.ofReal ((V f x) ^ p)) < ⊤ :=
      lt_of_le_of_lt (hlin f) hrighttop
    have hVmeas : AEMeasurable (V f) volume := by
      dsimp only [V]
      exact (ENNReal.measurable_toReal.comp
        (measurable_normalizedSphericalMaximal (f : Euclidean d → ℂ) f.continuous)).aemeasurable
    have hVmem : MemLp (V f) (ENNReal.ofReal p) volume :=
      memLp_of_lintegral_ofReal_rpow_lt_top (V f) hVmeas
        (fun x => ENNReal.toReal_nonneg) hp0 hlefttop
    have hVPowInt : Integrable (fun x : Euclidean d => (V f x) ^ p) volume := by
      have h := hVmem.integrable_norm_rpow hpEN0 hpENT
      convert h using 1
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.toReal_ofReal hpNN]
    have hleft_eq : (∫ x : Euclidean d, (V f x) ^ p) =
        (∫⁻ x : Euclidean d, ENNReal.ofReal ((V f x) ^ p)).toReal := by
      exact integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg ENNReal.toReal_nonneg p)
        hVPowInt.aestronglyMeasurable
    refine ⟨by simpa only [M, V] using hVmem, ?_⟩
    change (∫ x : Euclidean d, (V f x) ^ p) ≤ C * ∫ x : Euclidean d, ‖f x‖ ^ p
    rw [hleft_eq]
    calc
      (∫⁻ x : Euclidean d, ENNReal.ofReal ((V f x) ^ p)).toReal ≤
          (K * ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p)).toReal :=
        (ENNReal.toReal_le_toReal hlefttop.ne hrighttop.ne).mpr (hlin f)
      _ = K.toReal * (A * ∫ x : Euclidean d, ‖f x‖ ^ p) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hright_nonneg]
      _ = C * ∫ x : Euclidean d, ‖f x‖ ^ p := by
        dsimp only [C]
        ring
  obtain ⟨A, hA, hfinite⟩ := hfinite
  obtain ⟨C, hC, hlimit⟩ := hlimit A hA hfinite
  refine ⟨C, hC, ?_⟩
  intro f
  simpa only [M] using hlimit f

end

end LeanSpherical.HarmonicAnalysis
