/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.ThinRadialGeometry

/-!
# Thin smooth radial partition

The negative-weight local argument needs to cut a fixed central annulus into
physical slices of width `s` while retaining Schwartz inputs for the cap
estimate.  The cutoffs below are literal differences of nested smooth balls.
They telescope exactly, have a quarter-slice buffer at both ends, and avoid
introducing an abstract partition-of-unity layer.
-/

namespace LeanSpherical.HarmonicAnalysis

open Metric Set
open scoped BigOperators ContDiff

noncomputable section

/-- A smooth radial step: one on the ball of radius `s (m - 1/4)` and zero
outside the ball of radius `s (m + 1/4)`.  The zero branch only treats the
irrelevant indices for which the prescribed inner radius is not positive. -/
def thinRadialStep (d : Nat) (s : Real) (hs : 0 < s) (m : Nat) :
    SchwartzMap (Euclidean d) Complex := by
  by_cases hm : 0 < s * ((m : Real) - 1 / 4)
  · let b : ContDiffBump (0 : Euclidean d) :=
      ⟨s * ((m : Real) - 1 / 4), s * ((m : Real) + 1 / 4), hm, by
        nlinarith⟩
    let q : Euclidean d → Complex := fun x => (b x : Complex)
    have hbcompact : HasCompactSupport q := by
      change HasCompactSupport (Complex.ofRealCLM ∘ b)
      exact b.hasCompactSupport.comp_left (by rfl)
    have hbsmooth : ContDiff Real (⊤ : ENat) q := by
      change ContDiff Real (⊤ : ENat) (Complex.ofRealCLM ∘ b)
      exact Complex.ofRealCLM.contDiff.comp b.contDiff
    exact hbcompact.toSchwartzMap hbsmooth
  · exact 0

theorem thinRadialStep_one_of_norm_le
    {d : Nat} {s : Real} (hs : 0 < s) (m : Nat)
    (hm : 0 < s * ((m : Real) - 1 / 4)) {x : Euclidean d}
    (hx : ‖x‖ ≤ s * ((m : Real) - 1 / 4)) :
    thinRadialStep d s hs m x = 1 := by
  rw [thinRadialStep, dif_pos hm]
  dsimp
  let b : ContDiffBump (0 : Euclidean d) :=
    ⟨s * ((m : Real) - 1 / 4), s * ((m : Real) + 1 / 4), hm, by nlinarith⟩
  have hball : x ∈ closedBall (0 : Euclidean d) (s * ((m : Real) - 1 / 4)) := by
    simpa only [mem_closedBall, dist_zero_right] using hx
  have hb : b x = 1 := b.one_of_mem_closedBall hball
  simpa [b] using congrArg (fun u : Real => (u : Complex)) hb

theorem thinRadialStep_zero_of_outer_le
    {d : Nat} {s : Real} (hs : 0 < s) (m : Nat)
    (hm : 0 < s * ((m : Real) - 1 / 4)) {x : Euclidean d}
    (hx : s * ((m : Real) + 1 / 4) ≤ ‖x‖) :
    thinRadialStep d s hs m x = 0 := by
  rw [thinRadialStep, dif_pos hm]
  dsimp
  let b : ContDiffBump (0 : Euclidean d) :=
    ⟨s * ((m : Real) - 1 / 4), s * ((m : Real) + 1 / 4), hm, by nlinarith⟩
  have hdist : s * ((m : Real) + 1 / 4) ≤ dist x (0 : Euclidean d) := by
    simpa only [dist_zero_right] using hx
  have hb : b x = 0 := b.zero_of_le_dist hdist
  simpa [b] using congrArg (fun u : Real => (u : Complex)) hb

theorem norm_thinRadialStep_le_one
    {d : Nat} {s : Real} (hs : 0 < s) (m : Nat) (x : Euclidean d) :
    ‖thinRadialStep d s hs m x‖ ≤ 1 := by
  by_cases hm : 0 < s * ((m : Real) - 1 / 4)
  · rw [thinRadialStep, dif_pos hm]
    dsimp
    let b : ContDiffBump (0 : Euclidean d) :=
      ⟨s * ((m : Real) - 1 / 4), s * ((m : Real) + 1 / 4), hm, by nlinarith⟩
    have hnonneg : 0 ≤ b x := b.nonneg
    have hle : b x ≤ 1 := b.le_one
    change ‖(b x : Complex)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hle
  · rw [thinRadialStep, dif_neg hm]
    simp

/-- The `m`th smooth thin slice is a difference of two adjacent radial
steps.  The difference telescopes over any consecutive finite range. -/
def thinRadialPartition (d : Nat) (s : Real) (hs : 0 < s) (m : Nat) :
    SchwartzMap (Euclidean d) Complex :=
  thinRadialStep d s hs (m + 1) - thinRadialStep d s hs m

theorem norm_thinRadialPartition_le_two
    {d : Nat} {s : Real} (hs : 0 < s) (m : Nat) (x : Euclidean d) :
    ‖thinRadialPartition d s hs m x‖ ≤ 2 := by
  rw [thinRadialPartition]
  calc
    ‖thinRadialStep d s hs (m + 1) x - thinRadialStep d s hs m x‖ ≤
        ‖thinRadialStep d s hs (m + 1) x‖ + ‖thinRadialStep d s hs m x‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
      gcongr
      · exact norm_thinRadialStep_le_one hs (m + 1) x
      · exact norm_thinRadialStep_le_one hs m x
    _ = 2 := by norm_num

theorem thinRadialPartition_zero_of_norm_le
    {d : Nat} {s : Real} (hs : 0 < s) (m : Nat)
    (hm : 0 < s * ((m : Real) - 1 / 4)) {x : Euclidean d}
    (hx : ‖x‖ ≤ s * ((m : Real) - 1 / 4)) :
    thinRadialPartition d s hs m x = 0 := by
  change thinRadialStep d s hs (m + 1) x - thinRadialStep d s hs m x = 0
  rw [show (thinRadialStep d s hs m) x = 1 from
      thinRadialStep_one_of_norm_le hs m hm hx]
  apply sub_eq_zero.mpr
  apply thinRadialStep_one_of_norm_le hs (m + 1)
  · calc
      0 < s * ((m : Real) - 1 / 4) := hm
      _ < s * (((m + 1 : Nat) : Real) - 1 / 4) := by
        norm_num [Nat.cast_add]
        nlinarith
  · have hle : s * ((m : Real) - 1 / 4) ≤
        s * (((m + 1 : Nat) : Real) - 1 / 4) := by
      gcongr
      norm_num
    exact hx.trans hle

theorem thinRadialPartition_zero_of_outer_le
    {d : Nat} {s : Real} (hs : 0 < s) (m : Nat)
    (hm : 0 < s * ((m : Real) - 1 / 4)) {x : Euclidean d}
    (hx : s * ((m : Real) + 5 / 4) ≤ ‖x‖) :
    thinRadialPartition d s hs m x = 0 := by
  change thinRadialStep d s hs (m + 1) x - thinRadialStep d s hs m x = 0
  rw [show (thinRadialStep d s hs m) x = 0 from
      thinRadialStep_zero_of_outer_le hs m hm (by
      apply le_trans ?_ hx
      have : s * ((m : Real) + 1 / 4) ≤ s * ((m : Real) + 5 / 4) := by
        nlinarith
      exact this)]
  simp only [sub_zero]
  apply thinRadialStep_zero_of_outer_le hs (m + 1)
  · calc
      0 < s * ((m : Real) - 1 / 4) := hm
      _ < s * (((m + 1 : Nat) : Real) - 1 / 4) := by
        norm_num [Nat.cast_add]
        nlinarith
  · calc
      s * (((m + 1 : Nat) : Real) + 1 / 4) =
          s * ((m : Real) + 5 / 4) := by
            congr 1
            norm_num [Nat.cast_add]
            ring
      _ ≤ ‖x‖ := hx

theorem sum_thinRadialPartition_Icc
    {d : Nat} {s : Real} (hs : 0 < s) (lo hi : Nat) (hlohi : lo ≤ hi)
    (x : Euclidean d) :
    (∑ m ∈ Finset.Icc lo hi, thinRadialPartition d s hs m x) =
      thinRadialStep d s hs (hi + 1) x - thinRadialStep d s hs lo x := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sub _ (by omega : lo ≤ hi + 1)]
  change
    (∑ m ∈ Finset.range (hi + 1),
      (thinRadialStep d s hs (m + 1) x - thinRadialStep d s hs m x)) -
      ∑ m ∈ Finset.range lo,
        (thinRadialStep d s hs (m + 1) x - thinRadialStep d s hs m x) = _
  have hsum (n : Nat) :
      (∑ m ∈ Finset.range n,
        (thinRadialStep d s hs (m + 1) x - thinRadialStep d s hs m x)) =
        thinRadialStep d s hs n x - thinRadialStep d s hs 0 x := by
    simpa only using Finset.sum_range_sub (fun m => thinRadialStep d s hs m x) n
  rw [hsum, hsum]
  abel

/-- The finite thin partition is identically one between its two endpoint
steps.  The hypotheses expose the literal endpoint inequalities needed for
the dyadic central-annulus specialization. -/
theorem sum_thinRadialPartition_Icc_eq_one
    {d : Nat} {s : Real} (hs : 0 < s) (lo hi : Nat) (hlohi : lo ≤ hi)
    (hlo : 0 < s * ((lo : Real) - 1 / 4))
    (hhi : 0 < s * (((hi + 1 : Nat) : Real) - 1 / 4))
    {x : Euclidean d}
    (hbelow : s * ((lo : Real) + 1 / 4) ≤ ‖x‖)
    (habove : ‖x‖ ≤ s * (((hi + 1 : Nat) : Real) - 1 / 4)) :
    (∑ m ∈ Finset.Icc lo hi, thinRadialPartition d s hs m x) = 1 := by
  rw [sum_thinRadialPartition_Icc hs lo hi hlohi x,
    thinRadialStep_one_of_norm_le hs (hi + 1) hhi habove,
    thinRadialStep_zero_of_outer_le hs lo hlo hbelow]
  norm_num

end

end LeanSpherical.HarmonicAnalysis
