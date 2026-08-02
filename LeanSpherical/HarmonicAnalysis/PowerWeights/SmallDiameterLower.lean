/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.AnisotropicTubeLower
import LeanSpherical.HarmonicAnalysis.PowerWeights.RelativeMovingCapGeometry

/-!
# The small-diameter lower test

This file contains the geometry for the `j / 2 < k ≤ j` portion of the
sharp lower-bound construction.  The input is a thin radial cap near the
north pole and the output is a family of small horizontal slabs.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set
open scoped ENNReal ContDiff NNReal

noncomputable section

theorem northPole_eq_joinCoordinates (n : ℕ) :
    northPole n = joinCoordinates n (0, 1) := by
  apply (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.injective
  funext i
  cases i using Fin.lastCases
  · simp [northPole, joinCoordinates]
  · rename_i i
    have hi : Fin.castAdd 1 i = Fin.castSucc i := Fin.ext rfl
    simp [northPole, joinCoordinates, hi]

theorem succCoordinates_northPole (n : ℕ) :
    succCoordinates n (northPole n) = (0, 1) := by
  rw [northPole_eq_joinCoordinates, succCoordinates_joinCoordinates]

/-- The horizontal part of a unit vector in a cap about the north pole is at
most the chordal cap radius. -/
theorem norm_fst_succCoordinates_le_of_mem_northPoleCap
    (n : ℕ) {h : ℝ} {w : sphere (0 : Euclidean (n + 1)) 1}
    (hw : w ∈ northPoleCap n h) :
    ‖(succCoordinates n (w : Euclidean (n + 1))).1‖ < h := by
  change dist (w : Euclidean (n + 1)) (northPole n) < h at hw
  have hsub : succCoordinates n ((w : Euclidean (n + 1)) - northPole n) =
      ((succCoordinates n (w : Euclidean (n + 1))).1 - 0,
        (succCoordinates n (w : Euclidean (n + 1))).2 - 1) := by
    rw [succCoordinates_sub, succCoordinates_northPole]
    ext <;> simp
  calc
    ‖(succCoordinates n (w : Euclidean (n + 1))).1‖ =
        ‖(succCoordinates n ((w : Euclidean (n + 1)) - northPole n)).1‖ := by
          rw [hsub]
          simp
    _ ≤ ‖(w : Euclidean (n + 1)) - northPole n‖ :=
      norm_fst_succCoordinates_le_norm n _
    _ = dist (w : Euclidean (n + 1)) (northPole n) := by rw [dist_eq_norm_sub]
    _ < h := hw

/-- A north-pole cap has quadratic last-coordinate variation. -/
theorem abs_snd_sub_one_le_of_mem_northPoleCap
    (n : ℕ) {h : ℝ} {w : sphere (0 : Euclidean (n + 1)) 1}
    (hh : 0 ≤ h) (hquarter : h ≤ 1 / 4)
    (hw : w ∈ northPoleCap n h) :
    |(succCoordinates n (w : Euclidean (n + 1))).2 - 1| ≤ 4 * h ^ 2 := by
  change dist (w : Euclidean (n + 1)) (northPole n) < h at hw
  have hwunit : ‖(w : Euclidean (n + 1))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp w.property
  have hpoleunit : ‖northPole n‖ = 1 := norm_northPole n
  have hpolelast : 1 / 2 ≤ (succCoordinates n (northPole n)).2 := by
    rw [succCoordinates_northPole]
    norm_num
  have hbound := abs_snd_sub_le_horizontal_mul_of_unit_vectors n hwunit hpoleunit
    hh hquarter hpolelast (le_of_lt hw)
  rw [succCoordinates_northPole] at hbound
  simpa using hbound

/-- A radial cap near the north pole. -/
def northRadialCap (n : ℕ) (a s δ : ℝ) : Set (Euclidean (n + 1)) :=
  {y | ‖(succCoordinates n y).1‖ < s ∧ |‖y‖ - a| < δ ∧ 0 < (succCoordinates n y).2}

/-- Converts a bound on the squared radial error into one on the radius. -/
theorem abs_norm_sub_le_of_abs_sq_sub_le {d : ℕ} {y : Euclidean d}
    {a q : ℝ} (ha : 0 < a) (_hq : 0 ≤ q)
    (h : |‖y‖ ^ 2 - a ^ 2| ≤ q) :
    |‖y‖ - a| ≤ q / a := by
  rw [le_div_iff₀ ha]
  calc
    |‖y‖ - a| * a ≤ |‖y‖ - a| * (‖y‖ + a) := by
      apply mul_le_mul_of_nonneg_left
      · linarith [norm_nonneg y]
      · exact abs_nonneg _
    _ = |‖y‖ ^ 2 - a ^ 2| := by
      have hsum : 0 ≤ ‖y‖ + a := by positivity
      rw [← abs_of_nonneg hsum, ← abs_mul]
      congr 1
      ring
    _ ≤ q := h

/-- The squared radial error after translating an output slab by a north-pole
cap. This exact identity isolates the quadratic curvature term needed below
the parabolic scale. -/
theorem northPole_translate_sq_error
    (n : ℕ) (x : Euclidean (n + 1)) (r a : ℝ)
    (w : sphere (0 : Euclidean (n + 1)) 1) :
    ‖x + r • (w : Euclidean (n + 1))‖ ^ 2 - a ^ 2 =
      ‖(succCoordinates n x).1‖ ^ 2 +
        2 * r * inner ℝ (succCoordinates n x).1
          (succCoordinates n (w : Euclidean (n + 1))).1 +
        2 * r * (succCoordinates n x).2 *
          ((succCoordinates n (w : Euclidean (n + 1))).2 - 1) +
        2 * a * ((succCoordinates n x).2 + r - a) +
        ((succCoordinates n x).2 + r - a) ^ 2 := by
  have hw : ‖(w : Euclidean (n + 1))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp w.property
  have hsplitw := norm_sq_succCoordinates n (w : Euclidean (n + 1))
  rw [hw] at hsplitw
  norm_num at hsplitw
  have hsplit : succCoordinates n (x + r • (w : Euclidean (n + 1))) =
      succCoordinates n x + r • succCoordinates n (w : Euclidean (n + 1)) := by
    rw [succCoordinates_add, succCoordinates_smul]
  rw [norm_sq_succCoordinates, hsplit]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  rw [norm_add_sq_real]
  rw [real_inner_smul_right]
  simp only [norm_smul, Real.norm_eq_abs, smul_eq_mul]
  have hrsq : |r| ^ 2 = r ^ 2 := sq_abs r
  ring_nf
  nlinarith

/-- The quantitative radial error for the small-diameter construction.  The
third summand is the curvature gain: its cap-height contribution is quadratic
in `h`. -/
theorem abs_northPole_translate_sq_error_le
    (n : ℕ) {a r ρ b h : ℝ}
    {x : Euclidean (n + 1)} {w : sphere (0 : Euclidean (n + 1)) 1}
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hb : 0 ≤ b)
    (hh : 0 ≤ h) (hquarter : h ≤ 1 / 4)
    (hx : x ∈ horizontalSlab n ρ (a - r - b) (a - r + b))
    (hw : w ∈ northPoleCap n h) :
    |‖x + r • (w : Euclidean (n + 1))‖ ^ 2 - a ^ 2| ≤
      ρ ^ 2 + 2 * r * ρ * h + 8 * r * (|a - r| + b) * h ^ 2 +
        2 * a * b + b ^ 2 := by
  unfold horizontalSlab at hx
  simp only [mem_preimage, mem_prod, mem_ball, dist_zero_right, mem_Ioo] at hx
  rcases hx with ⟨hxhor, hxvert⟩
  have hxe : |(succCoordinates n x).2 + r - a| < b := by
    rw [abs_lt]
    constructor <;> linarith [hxvert.1, hxvert.2]
  have hwhor := norm_fst_succCoordinates_le_of_mem_northPoleCap n hw
  have hwvert := abs_snd_sub_one_le_of_mem_northPoleCap n hh hquarter hw
  have htbound : |(succCoordinates n x).2| ≤ |a - r| + b := by
    calc
      |(succCoordinates n x).2| =
          |(a - r) + ((succCoordinates n x).2 + r - a)| := by congr 1 <;> ring
      _ ≤ |a - r| + |(succCoordinates n x).2 + r - a| := abs_add_le _ _
      _ ≤ |a - r| + b := add_le_add_right hxe.le _
  have hterm1 : |‖(succCoordinates n x).1‖ ^ 2| ≤ ρ ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hρ).mpr hxhor.le
  have hterm2 :
      |2 * r * inner ℝ (succCoordinates n x).1
          (succCoordinates n (w : Euclidean (n + 1))).1| ≤ 2 * r * ρ * h := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hr]
    calc
      2 * r * |inner ℝ (succCoordinates n x).1
          (succCoordinates n (w : Euclidean (n + 1))).1| ≤
          2 * r * (‖(succCoordinates n x).1‖ *
            ‖(succCoordinates n (w : Euclidean (n + 1))).1‖) := by
        gcongr
        exact abs_real_inner_le_norm _ _
      _ ≤ 2 * r * (ρ * h) := by gcongr
      _ = 2 * r * ρ * h := by ring
  have hterm3 :
      |2 * r * (succCoordinates n x).2 *
          ((succCoordinates n (w : Euclidean (n + 1))).2 - 1)| ≤
          8 * r * (|a - r| + b) * h ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hr]
    calc
      2 * r * |(succCoordinates n x).2| *
          |(succCoordinates n (w : Euclidean (n + 1))).2 - 1| ≤
          2 * r * (|a - r| + b) * (4 * h ^ 2) := by gcongr
      _ = 8 * r * (|a - r| + b) * h ^ 2 := by ring
  have hterm4 : |2 * a * ((succCoordinates n x).2 + r - a)| ≤ 2 * a * b := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg ha]
    gcongr
  have hterm5 : |((succCoordinates n x).2 + r - a) ^ 2| ≤ b ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hb).mpr hxe.le
  rw [northPole_translate_sq_error n x r a w]
  calc
    |‖(succCoordinates n x).1‖ ^ 2 +
        2 * r * inner ℝ (succCoordinates n x).1
          (succCoordinates n (w : Euclidean (n + 1))).1 +
        2 * r * (succCoordinates n x).2 *
          ((succCoordinates n (w : Euclidean (n + 1))).2 - 1) +
        2 * a * ((succCoordinates n x).2 + r - a) +
        ((succCoordinates n x).2 + r - a) ^ 2| ≤
        |‖(succCoordinates n x).1‖ ^ 2| +
          |2 * r * inner ℝ (succCoordinates n x).1
            (succCoordinates n (w : Euclidean (n + 1))).1| +
          |2 * r * (succCoordinates n x).2 *
            ((succCoordinates n (w : Euclidean (n + 1))).2 - 1)| +
          |2 * a * ((succCoordinates n x).2 + r - a)| +
          |((succCoordinates n x).2 + r - a) ^ 2| := by
            calc
              _ ≤ |‖(succCoordinates n x).1‖ ^ 2 +
                    2 * r * inner ℝ (succCoordinates n x).1
                      (succCoordinates n (w : Euclidean (n + 1))).1 +
                    2 * r * (succCoordinates n x).2 *
                      ((succCoordinates n (w : Euclidean (n + 1))).2 - 1) +
                    2 * a * ((succCoordinates n x).2 + r - a)| +
                    |((succCoordinates n x).2 + r - a) ^ 2| := abs_add_le _ _
              _ ≤ (|‖(succCoordinates n x).1‖ ^ 2 +
                    2 * r * inner ℝ (succCoordinates n x).1
                      (succCoordinates n (w : Euclidean (n + 1))).1 +
                    2 * r * (succCoordinates n x).2 *
                      ((succCoordinates n (w : Euclidean (n + 1))).2 - 1)| +
                    |2 * a * ((succCoordinates n x).2 + r - a)|) +
                    |((succCoordinates n x).2 + r - a) ^ 2| := by
                  gcongr
                  exact abs_add_le _ _
              _ ≤ ((|‖(succCoordinates n x).1‖ ^ 2 +
                    2 * r * inner ℝ (succCoordinates n x).1
                      (succCoordinates n (w : Euclidean (n + 1))).1| +
                    |2 * r * (succCoordinates n x).2 *
                      ((succCoordinates n (w : Euclidean (n + 1))).2 - 1)|) +
                    |2 * a * ((succCoordinates n x).2 + r - a)|) +
                    |((succCoordinates n x).2 + r - a) ^ 2| := by
                  gcongr
                  exact abs_add_le _ _
              _ ≤ (((|‖(succCoordinates n x).1‖ ^ 2| +
                    |2 * r * inner ℝ (succCoordinates n x).1
                      (succCoordinates n (w : Euclidean (n + 1))).1|) +
                    |2 * r * (succCoordinates n x).2 *
                      ((succCoordinates n (w : Euclidean (n + 1))).2 - 1)|) +
                    |2 * a * ((succCoordinates n x).2 + r - a)|) +
                    |((succCoordinates n x).2 + r - a) ^ 2| := by
                  gcongr
                  exact abs_add_le _ _
              _ = _ := by ring
    _ ≤ ρ ^ 2 + 2 * r * ρ * h + 8 * r * (|a - r| + b) * h ^ 2 +
        2 * a * b + b ^ 2 := by gcongr

/-- Below the parabolic scale, translating a thin horizontal output slab by a
north-pole cap lands in a radial input cap.  The scalar hypotheses are the
ones verified by the dyadic parameter choice in the lower test. -/
theorem horizontalSlab_northPoleCap_translate_subset_northRadialCap
    (n : ℕ) {a r ρ b h s δ : ℝ}
    {x : Euclidean (n + 1)} {w : sphere (0 : Euclidean (n + 1)) 1}
    (ha : 0 < a) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hb : 0 ≤ b)
    (hh : 0 ≤ h) (hquarter : h ≤ 1 / 4)
    (hhor : ρ + r * h ≤ s)
    (herror : ρ ^ 2 + 2 * r * ρ * h + 8 * r * (|a - r| + b) * h ^ 2 +
        2 * a * b + b ^ 2 < a * δ)
    (hvertical : 0 < a - b - 4 * r * h ^ 2)
    (hx : x ∈ horizontalSlab n ρ (a - r - b) (a - r + b))
    (hw : w ∈ northPoleCap n h) :
    x + r • (w : Euclidean (n + 1)) ∈ northRadialCap n a s δ := by
  have hsq := abs_northPole_translate_sq_error_le n ha.le hr hρ hb hh hquarter hx hw
  have hsq' : |‖x + r • (w : Euclidean (n + 1))‖ ^ 2 - a ^ 2| < a * δ :=
    hsq.trans_lt herror
  have hrad : |‖x + r • (w : Euclidean (n + 1))‖ - a| < δ := by
    have hconvert := abs_norm_sub_le_of_abs_sq_sub_le ha
      (abs_nonneg (‖x + r • (w : Euclidean (n + 1))‖ ^ 2 - a ^ 2)) (le_refl _)
    calc
      |‖x + r • (w : Euclidean (n + 1))‖ - a| ≤
          |‖x + r • (w : Euclidean (n + 1))‖ ^ 2 - a ^ 2| / a := hconvert
      _ < (a * δ) / a := (div_lt_div_iff_of_pos_right ha).mpr hsq'
      _ = δ := by field_simp
  unfold horizontalSlab at hx
  simp only [mem_preimage, mem_prod, mem_ball, dist_zero_right, mem_Ioo] at hx
  rcases hx with ⟨hxhor, hxvert⟩
  have hxe : |(succCoordinates n x).2 + r - a| < b := by
    rw [abs_lt]
    constructor <;> linarith [hxvert.1, hxvert.2]
  have hwhor := norm_fst_succCoordinates_le_of_mem_northPoleCap n hw
  have hwvert := abs_snd_sub_one_le_of_mem_northPoleCap n hh hquarter hw
  have hyhor : ‖(succCoordinates n (x + r • (w : Euclidean (n + 1)))).1‖ < s := by
    rw [succCoordinates_add, succCoordinates_smul]
    simp only [Prod.fst_add, Prod.smul_fst]
    calc
      ‖(succCoordinates n x).1 + r • (succCoordinates n (w : Euclidean (n + 1))).1‖ ≤
          ‖(succCoordinates n x).1‖ + ‖r • (succCoordinates n (w : Euclidean (n + 1))).1‖ :=
        norm_add_le _ _
      _ = ‖(succCoordinates n x).1‖ + r * ‖(succCoordinates n (w : Euclidean (n + 1))).1‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      _ < ρ + r * h := by
        apply add_lt_add_of_lt_of_le hxhor
        gcongr
      _ ≤ s := hhor
  have hyvert : 0 < (succCoordinates n (x + r • (w : Euclidean (n + 1)))).2 := by
    rw [succCoordinates_add, succCoordinates_smul]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have he_lower : -b < (succCoordinates n x).2 + r - a := (abs_lt.mp hxe).1
    have hv_lower : -(4 * h ^ 2) ≤ (succCoordinates n (w : Euclidean (n + 1))).2 - 1 :=
      (abs_le.mp hwvert).1
    have hrv : -(4 * r * h ^ 2) ≤ r * ((succCoordinates n (w : Euclidean (n + 1))).2 - 1) := by
      calc
        -(4 * r * h ^ 2) = r * (-(4 * h ^ 2)) := by ring
        _ ≤ r * ((succCoordinates n (w : Euclidean (n + 1))).2 - 1) :=
          mul_le_mul_of_nonneg_left hv_lower hr
    nlinarith
  exact ⟨hyhor, hrad, hyvert⟩

/-- A sufficiently narrow north radial cap is contained in a fixed upper
horizontal slab.  This lets a standard vertical bump remove the opposite
radial branch without affecting the cap. -/
theorem northRadialCap_subset_upperHorizontalSlab
    (n : ℕ) {a s δ : ℝ}
    (ha : 0 < a) (hs : 0 ≤ s) (hsbound : s ≤ a / 4)
    (hδ : 0 ≤ δ) (hδbound : δ ≤ a / 8) :
    northRadialCap n a s δ ⊆ horizontalSlab n s (a - a / 2) (a + a / 2) := by
  intro y hy
  rcases hy with ⟨hyhor, hyrad, hypos⟩
  unfold horizontalSlab
  simp only [mem_preimage, mem_prod, mem_ball, dist_zero_right, mem_Ioo]
  constructor
  · exact hyhor
  · rw [abs_lt] at hyrad
    have hnormlo : a - δ < ‖y‖ := by linarith [hyrad.1]
    have hnormhi : ‖y‖ < a + δ := by linarith [hyrad.2]
    have hδsmall : δ < a := by linarith
    have hnormsq : ‖y‖ ^ 2 = ‖(succCoordinates n y).1‖ ^ 2 +
        (succCoordinates n y).2 ^ 2 := norm_sq_succCoordinates n y
    have hzsquare : ‖(succCoordinates n y).1‖ ^ 2 < s ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) hs).mpr hyhor
    have haδ : 0 ≤ a - δ := by linarith
    have hnormlosq : (a - δ) ^ 2 < ‖y‖ ^ 2 :=
      (sq_lt_sq₀ haδ (norm_nonneg _)).mpr hnormlo
    have htsq : (a / 2) ^ 2 < (succCoordinates n y).2 ^ 2 := by
      nlinarith
    have htlow : a / 2 < (succCoordinates n y).2 := by
      nlinarith [sq_nonneg ((succCoordinates n y).2 + a / 2)]
    have htupper : (succCoordinates n y).2 ≤ ‖y‖ := by
      calc
        (succCoordinates n y).2 ≤ |(succCoordinates n y).2| := le_abs_self _
        _ ≤ ‖y‖ := abs_snd_succCoordinates_le_norm n y
    constructor <;> linarith

/-- The north-pole cap contributes its full surface mass to the average on
each output slab in the small-diameter construction. -/
theorem horizontalSlab_northPoleCap_average_lower
    (n : ℕ) (hn : 2 ≤ n) {a r ρ b h s δ : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hb : 0 ≤ b)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (hhor : ρ + r * h ≤ s)
    (herror : ρ ^ 2 + 2 * r * ρ * h + 8 * r * (|a - r| + b) * h ^ 2 +
        2 * a * b + b ^ 2 < a * δ)
    (hvertical : 0 < a - b - 4 * r * h ^ 2)
    (g : Euclidean (n + 1) → ℝ) (hgContinuous : Continuous g)
    (hgnonneg : ∀ y, 0 ≤ g y)
    (hg_one : ∀ y ∈ northRadialCap n a s δ, g y = 1)
    {x : Euclidean (n + 1)} (hx : x ∈ horizontalSlab n ρ (a - r - b) (a - r + b)) :
    (ENNReal.ofReal (surfaceMass n) *
        ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
        ENNReal.ofReal (surfaceMass (n + 1)) ≤
      ENNReal.ofReal ‖normalizedSphericalAverage (n + 1)
        (fun y => (g y : ℂ)) r x‖ := by
  have hgi : Integrable (fun w : sphere (0 : Euclidean (n + 1)) 1 =>
      g (x + r • (w : Euclidean (n + 1))))
      (unitSurfaceMeasure (n + 1)) := by
    have hcont : Continuous (fun w : sphere (0 : Euclidean (n + 1)) 1 =>
        g (x + r • (w : Euclidean (n + 1)))) := by
      apply hgContinuous.comp
      fun_prop
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply poleCap_lower_le_ennreal_norm_normalizedSphericalAverage
    hn g r x (norm_northPole n) hh (hquarter.trans (by norm_num)) hgi
  · intro w
    exact hgnonneg _
  · intro w hw
    apply hg_one
    exact horizontalSlab_northPoleCap_translate_subset_northRadialCap n ha hr hρ hb
      hh.le hquarter hhor herror hvertical hx hw

/-- Output slabs are disjoint once their axial centres are separated by twice
their common thickness. -/
theorem disjoint_horizontalSlab_of_center_separated
    (n : ℕ) {ρ a c b : ℝ} (hsep : 2 * b ≤ |a - c|) :
    Disjoint (horizontalSlab n ρ (a - b) (a + b))
      (horizontalSlab n ρ (c - b) (c + b)) := by
  rw [Set.disjoint_left]
  intro x hxa hxc
  unfold horizontalSlab at hxa hxc
  simp only [mem_preimage, mem_prod, mem_ball, dist_zero_right, mem_Ioo] at hxa hxc
  have hclose : |a - c| < 2 * b := by
    calc
      |a - c| = |(a - (succCoordinates n x).2) + ((succCoordinates n x).2 - c)| := by
        congr 1
        ring
      _ ≤ |a - (succCoordinates n x).2| + |(succCoordinates n x).2 - c| := abs_add_le _ _
      _ = |(succCoordinates n x).2 - a| + |(succCoordinates n x).2 - c| := by
        rw [abs_sub_comm]
      _ < b + b := by
        apply add_lt_add
        · rw [abs_lt]
          constructor <;> linarith [hxa.2.1, hxa.2.2]
        · rw [abs_lt]
          constructor <;> linarith [hxc.2.1, hxc.2.2]
      _ = 2 * b := by ring
  exact (not_lt_of_ge hsep) hclose

/-- A horizontal slab lies in a ball whose radius is its axial offset plus
its horizontal and vertical widths. -/
theorem horizontalSlab_subset_ball
    (n : ℕ) {ρ a b R : ℝ}
    (hR : |a| + ρ + b ≤ R) :
    horizontalSlab n ρ (a - b) (a + b) ⊆ ball (0 : Euclidean (n + 1)) R := by
  intro x hx
  unfold horizontalSlab at hx
  simp only [mem_preimage, mem_prod, mem_ball, dist_zero_right, mem_Ioo] at hx
  rcases hx with ⟨hxhor, hxvert⟩
  have hvert : |(succCoordinates n x).2 - a| < b := by
    rw [abs_lt]
    constructor <;> linarith [hxvert.1, hxvert.2]
  have ht : |(succCoordinates n x).2| < |a| + b := by
    calc
      |(succCoordinates n x).2| =
          |a + ((succCoordinates n x).2 - a)| := by congr 1 <;> ring
      _ ≤ |a| + |(succCoordinates n x).2 - a| := abs_add_le _ _
      _ < |a| + b := by linarith
  rw [Metric.mem_ball, dist_zero_right]
  calc
    ‖x‖ ≤ ‖(succCoordinates n x).1‖ + |(succCoordinates n x).2| :=
      norm_le_succCoordinates n x
    _ < ρ + (|a| + b) := by linarith
    _ = |a| + ρ + b := by ring
    _ ≤ R := hR

/-- The weighted mass of a small horizontal slab near the origin.  This is
the direct product-slab analogue of the graph-tube lower bound. -/
theorem powerWeightedVolume_horizontalSlab_lower_of_near_origin
    (n : ℕ) {α ρ a b R : ℝ}
    (hα : α < 0) (hRpos : 0 < R) (hR : |a| + ρ + b ≤ R) :
    (ENNReal.ofReal R) ^ α *
        (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b)) ≤
      powerWeightedVolume (n + 1) α
        (horizontalSlab n ρ (a - b) (a + b)) := by
  calc
    (ENNReal.ofReal R) ^ α *
        (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b)) =
        (ENNReal.ofReal R) ^ α *
          volume (horizontalSlab n ρ (a - b) (a + b)) := by
            rw [volume_horizontalSlab]
            congr 2
            ring
    _ ≤ powerWeightedVolume (n + 1) α
        (horizontalSlab n ρ (a - b) (a + b)) :=
      powerWeightedVolume_set_lower_of_subset_ball hα hRpos
        (measurableSet_horizontalSlab n ρ (a - b) (a + b))
        (horizontalSlab_subset_ball n hR)

end

end LeanSpherical.HarmonicAnalysis
