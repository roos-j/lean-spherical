/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.AbsoluteMinkowski
import LeanSpherical.HarmonicAnalysis.FractalDilations.MinkowskiFacts
import LeanSpherical.HarmonicAnalysis.FractalDilations.SteinSegment

/-!
# The Minkowski diagonal of the fractal dilation theorem

This module turns the absolute-annular estimate into the paper's half-open
diagonal segment.  It keeps the dimension-equality reduction and the
classical Stein range separate from the absolute-frequency proof.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set

noncomputable section

/-- The restricted maximal operator over no radii is identically zero. -/
theorem empty_fractalSpherical_strong_type
    {d : ℕ} {p q : ℝ} :
    HasFractalSphericalStrongType d (∅ : Set ℝ) p q := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro f
  have hzero : fractalSphericalMaximalReal d (∅ : Set ℝ) f = 0 := by
    funext x
    simp [fractalSphericalMaximalReal, fractalSphericalMaximal]
  rw [hzero]
  simp

/-- Replace equality of upper Minkowski dimension by one admissible exponent,
with a small loss that remains strictly inside the diagonal summability
range. -/
theorem minkowski_diagonal_strong_type_of_upperMinkowskiDimension_eq
    {n : ℕ} (hn : 2 ≤ n)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2)
    {β p : ℝ} (hβ : 0 ≤ β)
    (hMinkowski : upperMinkowskiDimension E = β)
    (hp1 : 1 < p) (hp2 : p < 2)
    (hcritical : β < n * (p - 1)) :
    HasFractalSphericalStrongType (n + 1) E p p := by
  rcases eq_empty_or_nonempty E with rfl | hEne
  · exact empty_fractalSpherical_strong_type
  let ε : ℝ := (n * (p - 1) - β) / 2
  let α : ℝ := β + ε
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  have hα : 0 ≤ α := by
    dsimp only [α]
    exact add_nonneg hβ hε.le
  have hαcritical : α < n * (p - 1) := by
    dsimp only [α, ε]
    linarith
  have hM : HasUpperMinkowskiExponent E α := by
    simpa only [α] using
      hasUpperMinkowskiExponent_add_of_upperMinkowskiDimension_eq
        hE hMinkowski hε
  exact minkowski_diagonal_strong_type_of_hasUpperMinkowskiExponent
    hn E hE hEne hα hM hp1 hp2 hαcritical

/-- A finite positive exponent on the half-open Minkowski segment lies
strictly above the diagonal endpoint.  This is precisely the strict
inequality needed to sum the annular Minkowski estimates. -/
theorem one_lt_and_minkowski_critical_of_mem_Seg
    {d : ℕ} {β p q : ℝ} (hd : 2 ≤ d) (hβ : 0 ≤ β) (hp : 0 < p)
    (hseg : reciprocalExponentPoint p q ∈ Seg d β) :
    1 < p ∧ β < ((d : ℝ) - 1) * (p - 1) := by
  rcases hseg.1 with ⟨a, b, ha, hb, hab, hline⟩
  have hfirst := congrArg Prod.fst hline
  have hpinv : p⁻¹ = b *
      (((d : ℝ) - 1) / ((d : ℝ) - 1 + β)) := by
    simpa [Q1, Q2, reciprocalExponentPoint] using hfirst.symm
  have hdreal : 0 < (d : ℝ) := by positivity
  have hdmone : 0 < (d : ℝ) - 1 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  have hden : 0 < (d : ℝ) - 1 + β :=
    add_pos_of_pos_of_nonneg hdmone hβ
  have htpos : 0 < ((d : ℝ) - 1) / ((d : ℝ) - 1 + β) :=
    div_pos hdmone hden
  have hpinvpos : 0 < p⁻¹ := inv_pos.mpr hp
  have hb_ne_zero : b ≠ 0 := by
    intro hbzero
    have : p⁻¹ = 0 := by rw [hpinv, hbzero, zero_mul]
    exact (ne_of_gt hpinvpos) this
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb_ne_zero)
  have hb_le_one : b ≤ 1 := by linarith
  have hb_ne_one : b ≠ 1 := by
    intro hb_one
    apply hseg.2
    simp only [mem_singleton_iff]
    have ha_zero : a = 0 := by linarith
    simpa [Q1, Q2, ha_zero, hb_one] using hline.symm
  have hb_lt_one : b < 1 := lt_of_le_of_ne hb_le_one hb_ne_one
  have hinv_lt : p⁻¹ < ((d : ℝ) - 1) / ((d : ℝ) - 1 + β) := by
    rw [hpinv]
    calc
      b * (((d : ℝ) - 1) / ((d : ℝ) - 1 + β)) <
          1 * (((d : ℝ) - 1) / ((d : ℝ) - 1 + β)) :=
        mul_lt_mul_of_pos_right hb_lt_one htpos
      _ = ((d : ℝ) - 1) / ((d : ℝ) - 1 + β) := one_mul _
  have ht_le_one : ((d : ℝ) - 1) / ((d : ℝ) - 1 + β) ≤ 1 := by
    apply (div_le_one₀ hden).mpr
    linarith
  have hpone : 1 < p := by
    apply (inv_lt_inv₀ hp zero_lt_one).mp
    simpa only [inv_one] using hinv_lt.trans_le ht_le_one
  have hthreshold : ((d : ℝ) - 1 + β) / ((d : ℝ) - 1) < p := by
    apply (inv_lt_inv₀ hp (div_pos hden hdmone)).mp
    simpa only [inv_div] using hinv_lt
  have hmul : (d : ℝ) - 1 + β < p * ((d : ℝ) - 1) :=
    (div_lt_iff₀ hdmone).mp hthreshold
  refine ⟨hpone, ?_⟩
  nlinarith

/-- The half-open Minkowski segment in dimensions at least three.  Below
`p = 2` this is the absolute-annular Minkowski estimate; at and above
`p = 2` it is supplied directly by the existing Stein maximal theorem. -/
theorem minkowski_segment_strong_type_d_ge_three
    {d : ℕ} {β p q : ℝ} (hd : 3 ≤ d)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2)
    (hβ : 0 ≤ β) (hMinkowski : upperMinkowskiDimension E = β)
    (hp : 0 < p)
    (hseg : reciprocalExponentPoint p q ∈ Seg d β) :
    HasFractalSphericalStrongType d E p q := by
  have hpq : p = q := reciprocal_coordinates_eq_of_mem_Seg hseg
  subst q
  obtain ⟨hpone, hcritical⟩ :=
    one_lt_and_minkowski_critical_of_mem_Seg (by omega) hβ hp hseg
  by_cases hp2 : p < 2
  · have hn : 2 ≤ d - 1 := by omega
    have hcritical' : β < ((d - 1 : ℕ) : ℝ) * (p - 1) := by
      simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using hcritical
    have hbound := minkowski_diagonal_strong_type_of_upperMinkowskiDimension_eq
      (n := d - 1) hn E hE hβ hMinkowski hpone hp2 hcritical'
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hbound
  · have hpge : 2 ≤ p := le_of_not_gt hp2
    have hdmone : 0 < (d : ℝ) - 1 := by
      have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
      linarith
    have hstein_two : (d : ℝ) / ((d : ℝ) - 1) < 2 := by
      apply (div_lt_iff₀ hdmone).mpr
      have hdreal : (2 : ℝ) < d := by
        exact_mod_cast (show 2 < d by omega)
      nlinarith
    exact stein_diagonal_restricted_strong_type hd
      (lt_of_lt_of_le hstein_two hpge) E hE

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
