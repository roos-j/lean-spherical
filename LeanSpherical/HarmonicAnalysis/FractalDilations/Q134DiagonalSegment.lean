/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q134SegmentCoordinates

/-!
# Passing the common `Q1`--`Q3` diagonal through `Q4`

The two open analytic triangles meet on the `Q1`--`Q3` diagonal.  This file
turns the midpoint description supplied by `StrictInteriorGeometry` into the
same `Q4`--strict-Minkowski segment used off the diagonal.  Consequently the
final Theorem 1 assembly uses one loss--gain interpolation mechanism in all
three geometric cases.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Set

noncomputable section

/-- Strict barycentric coordinates in the Minkowski triangle remain strict
under a nontrivial convex combination. -/
theorem strictTriangle123Combination_convex
    {d : Nat} {beta : Real} {x y : ExponentPoint} {s : Real}
    (hx : StrictTriangle123Combination d beta x)
    (hy : StrictTriangle123Combination d beta y)
    (hs : 0 < s) (hs_one : s < 1) :
    StrictTriangle123Combination d beta ((1 - s) • x + s • y) := by
  rcases hx with ⟨a0, b0, c0, ha0, hb0, hc0, hsum0, hrepr0⟩
  rcases hy with ⟨a1, b1, c1, ha1, hb1, hc1, hsum1, hrepr1⟩
  refine ⟨(1 - s) * a0 + s * a1, (1 - s) * b0 + s * b1,
    (1 - s) * c0 + s * c1, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · rw [show ((1 - s) * a0 + s * a1) + ((1 - s) * b0 + s * b1) +
        ((1 - s) * c0 + s * c1) =
        (1 - s) * (a0 + b0 + c0) + s * (a1 + b1 + c1) by ring,
      hsum0, hsum1]
    ring
  · rw [← hrepr0, ← hrepr1]
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul] <;> ring

/-- A point written as the midpoint of a strict Minkowski point and a strict
`Q1`--`Q3`--`Q4` point is itself on a strict Minkowski--`Q4` segment.  This
is the diagonal case in the endpoint-free assembly of Theorem 1. -/
theorem exists_strictTriangle123_q4_segment_of_midpoint
    {d : Nat} {beta gamma : Real} {x xleft xright : ExponentPoint}
    (hd : 3 <= d \/ d = 2 /\ gamma <= 1 / 2)
    (hbeta : 0 < beta) (hbeta_gamma : beta <= gamma) (hgamma_one : gamma <= 1)
    (hmid : x = (1 / 2 : Real) • xleft + (1 / 2 : Real) • xright)
    (hleft : StrictTriangle123Combination d beta xleft)
    (hright : StrictTriangle134Combination d beta gamma xright) :
    ∃ z : ExponentPoint, ∃ t : Real,
      0 < t /\ t < 1 /\
        x = (1 - t) • z + t • Q4 d gamma /\
          StrictTriangle123Combination d beta z := by
  obtain ⟨zright, u, hu, hu_one, hright_segment, hzright⟩ :=
    exists_strictTriangle123_q4_segment_of_strictTriangle134
      hd hbeta hbeta_gamma hgamma_one hright
  let den : Real := 1 - u / 2
  have hden : 0 < den := by
    dsimp only [den]
    linarith
  let s : Real := ((1 - u) / 2) / den
  have hs : 0 < s := by
    dsimp only [s]
    exact div_pos (by linarith) hden
  have hs_one : s < 1 := by
    dsimp only [s]
    rw [div_lt_one hden]
    linarith
  let z : ExponentPoint := (1 - s) • xleft + s • zright
  have hz : StrictTriangle123Combination d beta z := by
    dsimp only [z]
    exact strictTriangle123Combination_convex hleft hzright hs hs_one
  refine ⟨z, u / 2, by linarith, by linarith, ?_, hz⟩
  rw [hmid, hright_segment]
  ext <;> dsimp only [z, s, den] <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul] <;>
    field_simp [hden.ne'] <;> ring

/-- The strict interior of the full exponent polygon is reduced to the two
actual fixed-frequency sources used in the paper.  Either the point already
lies in the strict Minkowski triangle, or it lies on a nontrivial segment
from `Q4` to such a point.  The second alternative also absorbs the
artificial `Q1`--`Q3` diagonal split, so the analytic assembly has only one
loss--gain interpolation branch. -/
theorem theoremOne_strict_interior_t123_or_q4_segment
    {d : Nat} {beta gamma : Real} {x : ExponentPoint}
    (hd : 3 <= d \/ d = 2 /\ gamma <= 1 / 2)
    (hbeta : 0 < beta) (hbeta_gamma : beta <= gamma) (hgamma_one : gamma <= 1)
    (hx : x ∈ interior (Q d beta gamma)) :
    StrictTriangle123Combination d beta x ∨
      ∃ z : ExponentPoint, ∃ t : Real,
        0 < t ∧ t < 1 ∧ x = (1 - t) • z + t • Q4 d gamma ∧
          StrictTriangle123Combination d beta z := by
  rcases theoremOne_strict_analytic_triangle_cover
      hd hbeta.le hbeta_gamma hgamma_one hx with h123 | h134 | hmid
  · exact Or.inl h123
  · right
    exact exists_strictTriangle123_q4_segment_of_strictTriangle134
      hd hbeta hbeta_gamma hgamma_one h134
  · rcases hmid with ⟨xleft, xright, hmidpoint, hleft, hright⟩
    right
    exact exists_strictTriangle123_q4_segment_of_midpoint
      hd hbeta hbeta_gamma hgamma_one hmidpoint hleft hright

/-- When the Minkowski parameter is zero, the nominal `Q1Q3Q4` triangle is
contained in the cap boundary.  It therefore contributes no point of the
open polygon.  This records the small degeneracy separately, so the final
analytic assembly only invokes the Q4 loss--gain branch when `beta > 0`. -/
theorem strictTriangle134Combination_zero_beta_on_cap
    {d : Nat} {gamma : Real} {x : ExponentPoint}
    (hd : 2 <= d) (hgamma : 0 <= gamma)
    (h : StrictTriangle134Combination d 0 gamma x) :
    x.1 = (d : Real) * x.2 := by
  rcases h with ⟨a, b, c, ha, hb, hc, habc, hrepr⟩
  have hDtwo : (2 : Real) <= (d : Real) := by exact_mod_cast hd
  have hD : 0 < (d : Real) := by linarith
  have hDplus : (d : Real) + 1 ≠ 0 := by linarith
  have hq4den : (d : Real) ^ 2 + 2 * gamma - 1 ≠ 0 := by
    have : 0 < (d : Real) ^ 2 + 2 * gamma - 1 := by
      nlinarith [sq_nonneg ((d : Real) - 2)]
    exact this.ne'
  have hq1 : (Q1 : ExponentPoint).1 = (d : Real) * Q1.2 := by
    simp [Q1]
  have hq3 : (Q3 d 0).1 = (d : Real) * (Q3 d 0).2 := by
    dsimp [Q3]
    field_simp [hDplus]
    ring
  have hq4 : (Q4 d gamma).1 = (d : Real) * (Q4 d gamma).2 := by
    dsimp [Q4]
    field_simp [hq4den]
    ring
  have hfirst := congrArg Prod.fst hrepr
  have hsecond := congrArg Prod.snd hrepr
  calc
    x.1 = (a • Q1 + b • Q3 d 0 + c • Q4 d gamma).1 := by
      simpa only using hfirst.symm
    _ = a * Q1.1 + b * (Q3 d 0).1 + c * (Q4 d gamma).1 := by
      simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul]
    _ = (d : Real) * (a * Q1.2 + b * (Q3 d 0).2 + c * (Q4 d gamma).2) := by
      rw [hq1, hq3, hq4]
      ring
    _ = (d : Real) * (a • Q1 + b • Q3 d 0 + c • Q4 d gamma).2 := by
      simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
    _ = (d : Real) * x.2 := by
      rw [hsecond]

/-- The degenerate zero-Minkowski `Q1Q3Q4` combination cannot occur in the
strict interior. -/
theorem strictTriangle134Combination_zero_beta_not_mem_interior
    {d : Nat} {gamma : Real} {x : ExponentPoint}
    (hd : 2 <= d) (hgamma : 0 <= gamma)
    (hx : x ∈ interior (Q d 0 gamma))
    (h : StrictTriangle134Combination d 0 gamma x) : False := by
  have hcap := strict_first_lt_natCast_mul_second_of_mem_interior_Q
    hd (by norm_num) (by norm_num) hgamma hx
  have hline := strictTriangle134Combination_zero_beta_on_cap hd hgamma h
  linarith

/-- At zero Minkowski dimension the full polygon is already governed by the
Minkowski triangle: the strict cap inequality is exactly the missing strict
halfspace for `Q1Q2Q3`. -/
theorem strictTriangle123Combination_of_mem_interior_Q_zero_beta
    {d : Nat} {gamma : Real} {x : ExponentPoint}
    (hd : 2 <= d) (hgamma : 0 <= gamma)
    (hx : x ∈ interior (Q d 0 gamma)) :
    StrictTriangle123Combination d 0 x := by
  have htranslation := strict_second_lt_first_of_mem_interior_Q
    hd (by norm_num) hgamma hx
  have hannulus := strict_annulus_of_mem_interior_Q
    hd (by norm_num) hgamma (by norm_num) hx
  have hdiagonal := strict_first_lt_natCast_mul_second_of_mem_interior_Q
    hd (by norm_num) (by norm_num) hgamma hx
  have hdiagonal' : x.1 < ((d : Real) - 0) * x.2 := by
    simpa using hdiagonal
  have hgap : 0 < (d : Real) - 1 - 0 := by
    have hdreal : (2 : Real) <= (d : Real) := by exact_mod_cast hd
    linarith
  exact strictTriangle123Combination_of_strict_halfspaces
    hd (by norm_num) (by norm_num) hgap htranslation hannulus hdiagonal'

/-- Uniform geometric dispatch for a strict Theorem 1 exponent.  The
zero-Minkowski case stays in the physical Minkowski triangle; otherwise the
only remaining branch is a strict segment from that triangle to `Q4`. -/
theorem theoremOne_strict_interior_t123_or_q4_segment_general
    {d : Nat} {beta gamma : Real} {x : ExponentPoint}
    (hd : 3 <= d \/ d = 2 /\ gamma <= 1 / 2)
    (hbeta : 0 <= beta) (hbeta_gamma : beta <= gamma) (hgamma_one : gamma <= 1)
    (hx : x ∈ interior (Q d beta gamma)) :
    StrictTriangle123Combination d beta x ∨
      ∃ z : ExponentPoint, ∃ t : Real,
        0 < t ∧ t < 1 ∧ x = (1 - t) • z + t • Q4 d gamma ∧
          StrictTriangle123Combination d beta z := by
  by_cases hbeta_zero : beta = 0
  · subst beta
    left
    have hd2 : 2 <= d := by
      rcases hd with hd | hd <;> omega
    exact strictTriangle123Combination_of_mem_interior_Q_zero_beta
      hd2 hbeta_gamma hx
  · right
    have hbeta_pos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hbeta_zero)
    exact theoremOne_strict_interior_t123_or_q4_segment
      hd hbeta_pos hbeta_gamma hgamma_one hx

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
