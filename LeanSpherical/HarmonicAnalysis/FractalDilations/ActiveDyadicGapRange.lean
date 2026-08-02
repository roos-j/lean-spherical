/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.ActiveDyadicRadiusBounds
import LeanSpherical.HarmonicAnalysis.FractalDilations.TTStarCovering

/-!
# The finite gap range for active dyadic radii

At a fixed frequency, the Section 3 radius-gap partition is finite: active
dyadic left endpoints lie in an interval of diameter `3 / 2`, whereas the
`n`-th shell starts at `2^(n - 1) 2^(-j)`.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Set

noncomputable section

/-- Any two active dyadic left endpoints lie in a fixed interval of diameter
`3 / 2` once the dyadic level is positive. -/
theorem abs_sub_dyadicLeft_le_three_halves_of_mem_activeDyadicIndices
    {E : Set Real} {j : Nat} {k l : Int}
    (hj : 1 <= j) (hE : E ⊆ Icc (1 : Real) 2)
    (hk : k ∈ activeDyadicIndices E j) (hl : l ∈ activeDyadicIndices E j) :
    |dyadicLeft j k - dyadicLeft j l| <= 3 / 2 := by
  have hk' := dyadicLeft_mem_Icc_half_two_of_mem_activeDyadicIndices hj hE hk
  have hl' := dyadicLeft_mem_Icc_half_two_of_mem_activeDyadicIndices hj hE hl
  rcases hk' with ⟨hklo, hkhi⟩
  rcases hl' with ⟨hllo, hlhi⟩
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The exact scale identity behind the finite gap range. -/
theorem four_eq_two_pow_add_two_mul_dyadicScale (j : Nat) :
    4 = (2 : Real) ^ (j + 2) * dyadicScale j := by
  have hdenom : (dyadicDenom j : Real) = (2 : Real) ^ j := by
    simp [dyadicDenom]
  calc
    4 = 4 * (dyadicScale j * (dyadicDenom j : Real)) := by
      rw [dyadicScale_mul_denom]
      ring
    _ = (2 : Real) ^ (j + 2) * dyadicScale j := by
      rw [hdenom, pow_add]
      ring

/-- If `n` is at least `j + 3`, the lower edge of the `n`th dyadic gap
shell is already at least four. -/
theorem four_le_dyadicGapLower_of_add_three_le
    {j n : Nat} (hjn : j + 3 <= n) :
    4 <= (2 : Real) ^ (n - 1) * dyadicScale j := by
  have hindex : j + 2 <= n - 1 := by omega
  have hpow : (2 : Real) ^ (j + 2) <= (2 : Real) ^ (n - 1) :=
    pow_le_pow_right₀ (by norm_num) hindex
  calc
    4 = (2 : Real) ^ (j + 2) * dyadicScale j :=
      four_eq_two_pow_add_two_mul_dyadicScale j
    _ <= (2 : Real) ^ (n - 1) * dyadicScale j :=
      mul_le_mul_of_nonneg_right hpow (dyadicScale_pos j).le

/-- The high radius-gap shells in the literal active-dyadic relation are
empty. -/
theorem not_radiusGapShellNeighbors_dyadic_of_activeDyadic_of_add_three_le
    {E : Set Real} {j n : Nat} {k l : Int}
    (hj : 1 <= j) (hE : E ⊆ Icc (1 : Real) 2)
    (hk : k ∈ activeDyadicIndices E j) (hl : l ∈ activeDyadicIndices E j)
    (hjn : j + 3 <= n) :
    ¬ radiusGapShellNeighbors
      ((2 : Real) ^ (n - 1) * dyadicScale j)
      ((2 : Real) ^ n * dyadicScale j)
      (dyadicLeft j k) (dyadicLeft j l) := by
  intro hshell
  have hdistance :=
    abs_sub_dyadicLeft_le_three_halves_of_mem_activeDyadicIndices hj hE hk hl
  have hlower : (2 : Real) ^ (n - 1) * dyadicScale j <=
      |dyadicLeft j k - dyadicLeft j l| := hshell.1
  have hfour := four_le_dyadicGapLower_of_add_three_le hjn
  linarith

/-- Equivalently, any nonempty active dyadic gap shell has a level strictly
below `j + 3`. -/
theorem dyadicGapLevel_lt_add_three_of_activeDyadic
    {E : Set Real} {j n : Nat} {k l : Int}
    (hj : 1 <= j) (hE : E ⊆ Icc (1 : Real) 2)
    (hk : k ∈ activeDyadicIndices E j) (hl : l ∈ activeDyadicIndices E j)
    (hshell : radiusGapShellNeighbors
      ((2 : Real) ^ (n - 1) * dyadicScale j)
      ((2 : Real) ^ n * dyadicScale j)
      (dyadicLeft j k) (dyadicLeft j l)) :
    n < j + 3 := by
  by_contra hn
  have hjn : j + 3 <= n := Nat.le_of_not_gt hn
  exact not_radiusGapShellNeighbors_dyadic_of_activeDyadic_of_add_three_le
    hj hE hk hl hjn hshell

/-- The canonical dyadic level of a pair of grid indices. -/
def activeDyadicGapLevel (k l : Int) : Nat :=
  if k = l then 0 else Nat.log 2 (Int.natAbs (k - l)) + 1

/-- The physical separation of two dyadic left endpoints is the integer
separation times the grid scale. -/
theorem abs_sub_dyadicLeft_eq_natAbs_mul_dyadicScale
    (j : Nat) (k l : Int) :
    |dyadicLeft j k - dyadicLeft j l| =
      (Int.natAbs (k - l) : Real) * dyadicScale j := by
  have hdiff : dyadicLeft j k - dyadicLeft j l =
      ((k - l : Int) : Real) * dyadicScale j := by
    simp only [dyadicLeft, Int.cast_sub]
    ring
  rw [hdiff, abs_mul, abs_of_pos (dyadicScale_pos j)]
  congr 1
  calc
    |((k - l : Int) : Real)| = ((|k - l| : Int) : Real) := by norm_cast
    _ = (Int.natAbs (k - l) : Real) := by
      simp only [Int.abs_eq_natAbs, Int.cast_natCast]

/-- A nonzero canonical gap level belongs to its literal radius-gap shell. -/
theorem radiusGapShellNeighbors_of_activeDyadicGapLevel_eq
    {j n : Nat} {k l : Int}
    (hlevel : activeDyadicGapLevel k l = n) (hn : 0 < n) :
    radiusGapShellNeighbors
      ((2 : Real) ^ (n - 1) * dyadicScale j)
      ((2 : Real) ^ n * dyadicScale j)
      (dyadicLeft j k) (dyadicLeft j l) := by
  have hkl : k ≠ l := by
    intro hkl
    subst l
    have hnzero : n = 0 := by
      simpa [activeDyadicGapLevel] using hlevel.symm
    omega
  let m : Nat := Int.natAbs (k - l)
  have hm : m ≠ 0 := by
    dsimp only [m]
    exact Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hkl)
  subst n
  rw [activeDyadicGapLevel, if_neg hkl]
  simp only [Nat.add_sub_cancel]
  unfold radiusGapShellNeighbors
  rw [abs_sub_dyadicLeft_eq_natAbs_mul_dyadicScale]
  constructor
  · have hnat : 2 ^ Nat.log 2 m <= m := Nat.pow_log_le_self 2 hm
    have hreal : (2 : Real) ^ Nat.log 2 m <= (m : Real) := by
      exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_right hreal (dyadicScale_pos j).le
  · have hnat : m < 2 ^ (Nat.log 2 m + 1) := by
      simpa only [Nat.succ_eq_add_one] using
        (Nat.lt_pow_succ_log_self Nat.one_lt_two m)
    have hreal : (m : Real) < (2 : Real) ^ (Nat.log 2 m + 1) := by
      exact_mod_cast hnat
    exact mul_lt_mul_of_pos_right hreal (dyadicScale_pos j)

/-- The canonical level of an active pair is in the finite range required by
the Section 3 shell reassembly. -/
theorem activeDyadicGapLevel_lt_add_three
    {E : Set Real} {j : Nat} {k l : Int}
    (hj : 1 <= j) (hE : E ⊆ Icc (1 : Real) 2)
    (hk : k ∈ activeDyadicIndices E j) (hl : l ∈ activeDyadicIndices E j) :
    activeDyadicGapLevel k l < j + 3 := by
  by_cases hkl : k = l
  · subst l
    simp [activeDyadicGapLevel]
  · have hn : 0 < activeDyadicGapLevel k l := by
      simp [activeDyadicGapLevel, hkl]
    have hshell := radiusGapShellNeighbors_of_activeDyadicGapLevel_eq
      (j := j) (k := k) (l := l) rfl hn
    exact dyadicGapLevel_lt_add_three_of_activeDyadic hj hE hk hl hshell

/-- Finset form of the preceding finite-range fact. -/
theorem activeDyadicGapLevel_mem_range_add_three
    {E : Set Real} {j : Nat} {k l : Int}
    (hj : 1 <= j) (hE : E ⊆ Icc (1 : Real) 2)
    (hk : k ∈ activeDyadicIndices E j) (hl : l ∈ activeDyadicIndices E j) :
    activeDyadicGapLevel k l ∈ Finset.range (j + 3) :=
  Finset.mem_range.mpr (activeDyadicGapLevel_lt_add_three hj hE hk hl)

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
