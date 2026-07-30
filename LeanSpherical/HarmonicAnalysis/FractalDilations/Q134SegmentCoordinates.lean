/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q134ToQ123Segment

/-!
# Reciprocal exponents on the `Q4`--Minkowski segment

This file packages the elementary coordinate facts needed by the final
strict `Q1Q3Q4` assembly.  The geometric segment constructed in
`Q134ToQ123Segment` lives in reciprocal-exponent space, whereas the analytic
dyadic estimates are indexed by positive exponents.  We therefore record the
conversion explicitly, together with the elementary choice of an arbitrarily
small Q4 loss which is dominated by the strict Minkowski gain.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

noncomputable section

/-- A strict Minkowski-triangle point has two strictly positive reciprocal
coordinates. -/
theorem strictTriangle123_coordinates_pos
    {d : Nat} {beta : Real} {z : ExponentPoint}
    (hd : 2 <= d) (hbeta : 0 <= beta) (hbeta_one : beta <= 1)
    (hz : StrictTriangle123Combination d beta z) :
    0 < z.1 /\ 0 < z.2 := by
  rcases hz with ⟨a, b, c, ha, hb, hc, habc, hrepr⟩
  have hD : (2 : Real) <= (d : Real) := by exact_mod_cast hd
  have hH : 0 < (d : Real) - 1 := by linarith
  have hHbeta : 0 < (d : Real) - 1 + beta := by linarith
  have hDbeta : 0 < (d : Real) - beta := by linarith
  have hB3 : 0 < (d : Real) - beta + 1 := by linarith
  have hzfst :
      z.1 =
        b * (((d : Real) - 1) / ((d : Real) - 1 + beta)) +
          c * (((d : Real) - beta) / ((d : Real) - beta + 1)) := by
    have hfst := congrArg Prod.fst hrepr
    simpa [Q1, Q2, Q3, Prod.smul_fst, smul_eq_mul] using hfst.symm
  have hzsnd :
      z.2 =
        b * (((d : Real) - 1) / ((d : Real) - 1 + beta)) +
          c * (1 / ((d : Real) - beta + 1)) := by
    have hsnd := congrArg Prod.snd hrepr
    simpa [Q1, Q2, Q3, Prod.smul_snd, smul_eq_mul] using hsnd.symm
  have hq2 : 0 < ((d : Real) - 1) / ((d : Real) - 1 + beta) :=
    div_pos hH hHbeta
  have hq3fst : 0 < ((d : Real) - beta) / ((d : Real) - beta + 1) :=
    div_pos hDbeta hB3
  have hq3snd : 0 < 1 / ((d : Real) - beta + 1) :=
    one_div_pos.mpr hB3
  constructor
  · rw [hzfst]
    exact add_pos (mul_pos hb hq2) (mul_pos hc hq3fst)
  · rw [hzsnd]
    exact add_pos (mul_pos hb hq2) (mul_pos hc hq3snd)

/-- The two reciprocal coordinates of `Q4` are positive in the dimensional
range of Theorem 1. -/
theorem q4_coordinates_pos
    {d : Nat} {gamma : Real} (hd : 2 <= d) (hgamma : 0 <= gamma) :
    0 < (Q4 d gamma).1 /\ 0 < (Q4 d gamma).2 := by
  have hD : (2 : Real) <= (d : Real) := by exact_mod_cast hd
  have hDpos : 0 < (d : Real) := by linarith
  have hH : 0 < (d : Real) - 1 := by linarith
  have hT : 0 < (d : Real) ^ 2 + 2 * gamma - 1 := by
    nlinarith [sq_nonneg ((d : Real) - 2)]
  constructor
  · dsimp [Q4]
    exact div_pos (mul_pos hDpos hH) hT
  · dsimp [Q4]
    exact div_pos hH hT

/-- Taking the inverse of positive reciprocal coordinates recovers the
corresponding exponent point.  The equality itself is valid even at zero;
positivity is recorded separately where it is needed for analytic estimates.
-/
theorem reciprocalExponentPoint_inv_coordinates (z : ExponentPoint) :
    reciprocalExponentPoint z.1⁻¹ z.2⁻¹ = z := by
  ext <;> simp [reciprocalExponentPoint]

/-- Convert the full strict `Q1Q3Q4` segment into positive analytic
exponents.  The conclusion is the exact convex-coordinate datum consumed by
the two-exponent fixed-dyadic interpolation argument: the first endpoint is
strictly in the Minkowski triangle and the second is exactly `Q4`. -/
theorem exists_reciprocal_strictTriangle123_q4_segment_of_strictTriangle134
    {d : Nat} {beta gamma p q : Real}
    (hd : 3 <= d \/ d = 2 /\ gamma <= 1 / 2)
    (hbeta : 0 < beta) (hbeta_gamma : beta <= gamma) (hgamma_one : gamma <= 1)
    (h : StrictTriangle134Combination d beta gamma (reciprocalExponentPoint p q)) :
    ∃ p0 q0 p4 q4 t : Real,
      0 < p0 /\ 0 < q0 /\ 0 < p4 /\ 0 < q4 /\ 0 < t /\ t < 1 /\
        StrictTriangle123Combination d beta (reciprocalExponentPoint p0 q0) /\
          reciprocalExponentPoint p4 q4 = Q4 d gamma /\
            reciprocalExponentPoint p q =
              (1 - t) • reciprocalExponentPoint p0 q0 +
                t • reciprocalExponentPoint p4 q4 := by
  obtain ⟨z, t, ht, ht_one, hsegment, hz⟩ :=
    exists_strictTriangle123_q4_segment_of_strictTriangle134
      hd hbeta hbeta_gamma hgamma_one h
  have hd2 : 2 <= d := by
    rcases hd with hd | hd
    · omega
    · omega
  have hbeta_one : beta <= 1 := hbeta_gamma.trans hgamma_one
  have hgamma : 0 <= gamma := hbeta.le.trans hbeta_gamma
  have hzpos := strictTriangle123_coordinates_pos hd2 hbeta.le hbeta_one hz
  have hq4pos := q4_coordinates_pos hd2 hgamma
  let p0 : Real := z.1⁻¹
  let q0 : Real := z.2⁻¹
  let p4 : Real := (Q4 d gamma).1⁻¹
  let q4 : Real := (Q4 d gamma).2⁻¹
  have hp0 : 0 < p0 := by
    dsimp only [p0]
    exact inv_pos.mpr hzpos.1
  have hq0 : 0 < q0 := by
    dsimp only [q0]
    exact inv_pos.mpr hzpos.2
  have hp4 : 0 < p4 := by
    dsimp only [p4]
    exact inv_pos.mpr hq4pos.1
  have hq4 : 0 < q4 := by
    dsimp only [q4]
    exact inv_pos.mpr hq4pos.2
  have hzrec : reciprocalExponentPoint p0 q0 = z := by
    dsimp only [p0, q0]
    exact reciprocalExponentPoint_inv_coordinates z
  have hq4rec : reciprocalExponentPoint p4 q4 = Q4 d gamma := by
    dsimp only [p4, q4]
    exact reciprocalExponentPoint_inv_coordinates (Q4 d gamma)
  refine ⟨p0, q0, p4, q4, t, hp0, hq0, hp4, hq4, ht, ht_one, ?_, hq4rec, ?_⟩
  · simpa only [hzrec] using hz
  · simpa only [hzrec, hq4rec] using hsegment

/-- A strict dyadic gain of exponent `delta`, used for the Minkowski source,
dominates a sufficiently small Q4 loss after interpolation with weight `t`.
This is the scalar epsilon choice in the endpoint-free form of Corollary 3.2.
-/
theorem exists_positive_q4_loss_below_weighted_minkowski_gain
    {delta t : Real} (hdelta : 0 < delta) (ht : 0 < t) (ht_one : t < 1) :
    ∃ eps : Real, 0 < eps /\ eps < (1 - t) * delta / t := by
  have hbound : 0 < (1 - t) * delta / t := by
    exact div_pos (mul_pos (sub_pos.mpr ht_one) hdelta) ht
  refine ⟨((1 - t) * delta / t) / 2, div_pos hbound (by norm_num), ?_⟩
  nlinarith

/-- Equivalent sign form of the preceding epsilon choice, convenient when
the mixed dyadic ratio is written as `2^(eps * t - delta * (1 - t))`. -/
theorem exists_positive_q4_loss_with_weighted_exponent_neg
    {delta t : Real} (hdelta : 0 < delta) (ht : 0 < t) (ht_one : t < 1) :
    ∃ eps : Real, 0 < eps /\ eps * t - delta * (1 - t) < 0 := by
  obtain ⟨eps, heps, hsmall⟩ :=
    exists_positive_q4_loss_below_weighted_minkowski_gain hdelta ht ht_one
  refine ⟨eps, heps, ?_⟩
  have hmul : eps * t < (1 - t) * delta :=
    (lt_div_iff₀ ht).mp hsmall
  linarith

/-- Coordinate form of the strict `Q1Q3Q4` segment.  This is deliberately
stated directly in reciprocal-exponent space: it is the geometric input for
the four-corner, two-exponent interpolation step used to combine the small
`Q4` loss with a strict Minkowski-triangle gain. -/
theorem exists_coordinate_strictTriangle123_q4_segment_of_strictTriangle134
    {d : Nat} {beta gamma : Real} {x : ExponentPoint}
    (hd : 3 <= d \/ d = 2 /\ gamma <= 1 / 2)
    (hbeta : 0 < beta) (hbeta_gamma : beta <= gamma) (hgamma_one : gamma <= 1)
    (h : StrictTriangle134Combination d beta gamma x) :
    ∃ x0 y0 x4 y4 t : Real,
      0 < x0 /\ 0 < y0 /\ 0 < x4 /\ 0 < y4 /\ 0 < t /\ t < 1 /\
        StrictTriangle123Combination d beta (x0, y0) /\
          (x4, y4) = Q4 d gamma /\
            x = (1 - t) • (x0, y0) + t • (x4, y4) := by
  obtain ⟨z, t, ht, ht_one, hsegment, hz⟩ :=
    exists_strictTriangle123_q4_segment_of_strictTriangle134
      hd hbeta hbeta_gamma hgamma_one h
  have hd2 : 2 <= d := by
    rcases hd with hd | hd
    · omega
    · omega
  have hbeta_one : beta <= 1 := hbeta_gamma.trans hgamma_one
  have hgamma : 0 <= gamma := hbeta.le.trans hbeta_gamma
  have hzpos := strictTriangle123_coordinates_pos hd2 hbeta.le hbeta_one hz
  have hq4pos := q4_coordinates_pos hd2 hgamma
  refine ⟨z.1, z.2, (Q4 d gamma).1, (Q4 d gamma).2,
    t, hzpos.1, hzpos.2, hq4pos.1, hq4pos.2, ht, ht_one, ?_, ?_, ?_⟩
  · simpa only [Prod.eta] using hz
  · exact Prod.eta _
  · simpa only [Prod.eta] using hsegment

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
