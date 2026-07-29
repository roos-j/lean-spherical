/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure

/-!
# Concrete dyadic frequency annuli

This file contains the elementary geometry behind a dyadic decomposition in
Euclidean frequency space.  The annulus at level `j` has radii in
`[2^j, 2^(j + 1))`.  In particular, distinct levels cannot meet.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set

noncomputable section

/-- The positive frequency scale associated to a nonnegative dyadic level. -/
def dyadicScale (j : Nat) : Real := (2 : Real) ^ j

/-- The half-open annulus with radii between two consecutive dyadic scales. -/
def dyadicAnnulus (d j : Nat) : Set (Euclidean d) :=
  {xi | dyadicScale j <= norm xi /\ norm xi < dyadicScale (j + 1)}

/-- Dyadic scales are positive. -/
theorem dyadicScale_pos (j : Nat) : 0 < dyadicScale j := by
  simp [dyadicScale]

/-- Dyadic scales are monotone in their index. -/
theorem dyadicScale_mono {i j : Nat} (hij : i <= j) :
    dyadicScale i <= dyadicScale j := by
  unfold dyadicScale
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hij

/-- Points in strictly later annuli have strictly larger frequency norm. -/
theorem norm_lt_norm_of_mem_dyadicAnnulus_of_lt
    {d i j : Nat} (hij : i < j) {xi eta : Euclidean d}
    (hxi : xi ∈ dyadicAnnulus d i) (heta : eta ∈ dyadicAnnulus d j) :
    norm xi < norm eta := by
  rcases hxi with ⟨_, hxi_upper⟩
  rcases heta with ⟨heta_lower, _⟩
  have hscale : dyadicScale (i + 1) <= dyadicScale j :=
    dyadicScale_mono (Nat.succ_le_iff.mpr hij)
  exact lt_of_lt_of_le hxi_upper (hscale.trans heta_lower)

/-- Dyadic annuli at unequal levels are disjoint. -/
theorem dyadicAnnulus_disjoint {d i j : Nat} (hij : i ≠ j) :
    Disjoint (dyadicAnnulus d i) (dyadicAnnulus d j) := by
  rw [Set.disjoint_left]
  intro xi hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (lt_irrefl (norm xi))
      (norm_lt_norm_of_mem_dyadicAnnulus_of_lt hij hxi hxj)
  · exact (lt_irrefl (norm xi))
      (norm_lt_norm_of_mem_dyadicAnnulus_of_lt hji hxj hxi)

end

end LeanSpherical.HarmonicAnalysis
