/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.OffDiagonalReassembly

/-!
# Off-diagonal reassembly from strict dyadic decay

This is the endpoint-free final summation layer for the `Q4` argument.  A
strict dyadic `Lᵖ → Lᑫ` gain is summed by Minkowski at the *output* exponent,
and the existing absolute-cutoff Fatou argument then gives the restricted
spherical maximal bound.  No Bourgain endpoint summation is used here.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory FourierTransform Metric Set
open scoped FourierTransform Topology

noncomputable section

/-- A finite family of nonnegative output pieces with geometrically decaying
`Lᑫ` norms has a uniform `Lᑫ` norm after summation.  This is the public
off-diagonal form of the ordinary Minkowski/geometric-series step. -/
theorem finite_geometric_output_sum
    {d : ℕ} {q : ENNReal} (hq : (1 : ENNReal) ≤ q)
    (T : ℕ → Euclidean d → ℝ) (hTmem : ∀ j, MemLp (T j) q volume)
    (C ρ : ENNReal)
    (hTnorm : ∀ j, eLpNorm (T j) q volume ≤ C * ρ ^ j)
    (N : ℕ) :
    MemLp (fun x => ∑ j ∈ Finset.range N, T j x) q volume ∧
      eLpNorm (fun x => ∑ j ∈ Finset.range N, T j x) q volume ≤
        C * (1 - ρ)⁻¹ := by
  constructor
  · induction N with
    | zero =>
        change MemLp 0 q volume
        exact MemLp.zero
    | succ n ih =>
        have hsum := ih.add (hTmem n)
        convert hsum using 1
        funext x
        simp only [Finset.sum_range_succ, Pi.add_apply]
  · apply eLpNorm_sum_range_le_geometric volume q hq T
    · intro j
      exact (hTmem j).1
    · exact hTnorm

/-- Reassemble a finite absolute-frequency cutoff from a low-frequency term
and strict off-diagonal dyadic bounds.  The input appears only through its
`Lᵖ` norm, while Minkowski is used solely at the output exponent `q`. -/
theorem finite_absolute_off_diagonal_reassembly_eLpNorm
    {d : ℕ} {p q : ℝ} (hd0 : 0 < d)
    (hp : 0 < p) (hq : 1 ≤ q)
    (E : Set ℝ) (hEpos : E ⊆ Ioi (0 : ℝ))
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (CR CT ρ : ENNReal) (hρ : ρ < 1)
    (hregular : ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (fractalSphericalMaximalReal d E
        (absoluteCutoffProjection φ 0 f)) (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalSphericalMaximalReal d E
        (absoluteCutoffProjection φ 0 f)) (ENNReal.ofReal q) volume ≤
        CR * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume)
    (hdyadic : ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      MemLp (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass φ hφone hφzero j) f) (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass φ hφone hφzero j) f) (ENNReal.ofReal q) volume ≤
        (CT * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume) * ρ ^ j)
    (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
    MemLp (fractalAbsoluteCutoffMaximal d E φ N f) (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalAbsoluteCutoffMaximal d E φ N f)
        (ENNReal.ofReal q) volume ≤
        (CR + CT * (1 - ρ)⁻¹) *
          eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume := by
  let P : Euclidean d → ℝ := fractalAbsoluteCutoffMaximal d E φ N f
  let R : Euclidean d → ℝ := fractalSphericalMaximalReal d E
    (absoluteCutoffProjection φ 0 f)
  let T : ℕ → Euclidean d → ℝ := fun j =>
    fractalDyadicBandpassMaximal d E
      (absoluteDyadicBandpass φ hφone hφzero j) f
  let hroot : ENNReal := eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume
  have hqENN : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hPmeas : AEStronglyMeasurable P volume := by
    exact (measurable_fractalAbsoluteCutoffMaximal E φ N f).aestronglyMeasurable
  have hR0 : ∀ x, 0 ≤ R x := fun x => ENNReal.toReal_nonneg
  have hT0 : ∀ j x, 0 ≤ T j x := fun j x => ENNReal.toReal_nonneg
  have hP0 : ∀ x, 0 ≤ P x := fun x =>
    fractalAbsoluteCutoffMaximal_nonneg E φ N f x
  have hR := hregular f
  have hRmem : MemLp R (ENNReal.ofReal q) volume := by
    simpa only [R] using hR.1
  have hRnorm : eLpNorm R (ENNReal.ofReal q) volume ≤ CR * hroot := by
    simpa only [R, hroot] using hR.2
  have hTmem : ∀ j, MemLp (T j) (ENNReal.ofReal q) volume := by
    intro j
    simpa only [T] using (hdyadic j f).1
  have hTnorm : ∀ j, eLpNorm (T j) (ENNReal.ofReal q) volume ≤
      (CT * hroot) * ρ ^ j := by
    intro j
    simpa only [T, hroot] using (hdyadic j f).2
  let S : Euclidean d → ℝ := fun x => ∑ j ∈ Finset.range N, T j x
  have hS := finite_geometric_output_sum hqENN T hTmem (CT * hroot) ρ hTnorm N
  have hSmem : MemLp S (ENNReal.ofReal q) volume := by
    simpa only [S] using hS.1
  have hSnorm : eLpNorm S (ENNReal.ofReal q) volume ≤
      (CT * hroot) * (1 - ρ)⁻¹ := by
    simpa only [S] using hS.2
  have hS0 : ∀ x, 0 ≤ S x := fun x => by
    dsimp only [S]
    exact Finset.sum_nonneg fun j _ => hT0 j x
  have hRS0 : ∀ x, 0 ≤ R x + S x := fun x => add_nonneg (hR0 x) (hS0 x)
  have hRS_mem : MemLp (R + S) (ENNReal.ofReal q) volume := hRmem.add hSmem
  have hpoint : ∀ x, P x ≤ R x + S x := by
    intro x
    dsimp only [P, R, S, T]
    exact fractalAbsoluteCutoffMaximal_le_low_add_band_sum
      hd0 E hEpos φ hφone hφzero N f x
  have hPmem : MemLp P (ENNReal.ofReal q) volume := by
    apply hRS_mem.mono hPmeas
    filter_upwards with x
    change ‖P x‖ ≤ ‖R x + S x‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x), Real.norm_eq_abs,
      abs_of_nonneg (hRS0 x)]
    exact hpoint x
  refine ⟨by simpa only [P] using hPmem, ?_⟩
  change eLpNorm P (ENNReal.ofReal q) volume ≤
    (CR + CT * (1 - ρ)⁻¹) * hroot
  calc
    eLpNorm P (ENNReal.ofReal q) volume ≤ eLpNorm (R + S) (ENNReal.ofReal q) volume := by
      apply eLpNorm_mono
      intro x
      change ‖P x‖ ≤ ‖R x + S x‖
      rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x), Real.norm_eq_abs,
        abs_of_nonneg (hRS0 x)]
      exact hpoint x
    _ ≤ eLpNorm R (ENNReal.ofReal q) volume + eLpNorm S (ENNReal.ofReal q) volume :=
      eLpNorm_add_le hRmem.1 hSmem.1 hqENN
    _ ≤ CR * hroot + (CT * hroot) * (1 - ρ)⁻¹ :=
      add_le_add hRnorm hSnorm
    _ = (CR + CT * (1 - ρ)⁻¹) * hroot := by ring

/-- Convert an off-diagonal extended-real norm estimate into its homogeneous
moment form.  This is intentionally stated for the actual nonnegative
maximal-function output, rather than for an abstract positive operator. -/
theorem off_diagonal_moment_bound_of_eLpNorm
    {d : ℕ} {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (g : Euclidean d → ℝ) (hgmem : MemLp g (ENNReal.ofReal q) volume)
    (hg0 : ∀ x, 0 ≤ g x) (f : SchwartzMap (Euclidean d) ℂ)
    (D : ENNReal) (hDtop : D ≠ ⊤)
    (hnorm : eLpNorm g (ENNReal.ofReal q) volume ≤
      D * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume) :
    (∫ x : Euclidean d, g x ^ q) ≤
      D.toReal ^ q * (∫ x : Euclidean d, ‖f x‖ ^ p) ^ (q / p) := by
  have hpNN : 0 ≤ p := hp.le
  have hqNN : 0 ≤ q := hq.le
  have hpE0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpET : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqE0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hqET : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfmem : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume :=
    f.memLp (ENNReal.ofReal p) volume
  have hI : 0 ≤ ∫ x : Euclidean d, ‖f x‖ ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
  have hG : 0 ≤ ∫ x : Euclidean d, g x ^ q :=
    integral_nonneg fun x => Real.rpow_nonneg (hg0 x) q
  have hrootbound : (∫ x : Euclidean d, g x ^ q) ^ q⁻¹ ≤
      D.toReal * (∫ x : Euclidean d, ‖f x‖ ^ p) ^ p⁻¹ := by
    have hnormG : eLpNorm g (ENNReal.ofReal q) volume =
        ENNReal.ofReal ((∫ x : Euclidean d, g x ^ q) ^ q⁻¹) := by
      rw [hgmem.eLpNorm_eq_integral_rpow_norm hqE0 hqET,
        ENNReal.toReal_ofReal hqNN]
      apply congrArg ENNReal.ofReal
      apply congrArg (fun z : ℝ => z ^ q⁻¹)
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    have hnormF : eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume =
        ENNReal.ofReal ((∫ x : Euclidean d, ‖f x‖ ^ p) ^ p⁻¹) := by
      rw [hfmem.eLpNorm_eq_integral_rpow_norm hpE0 hpET,
        ENNReal.toReal_ofReal hpNN]
    have hnorm' : ENNReal.ofReal ((∫ x : Euclidean d, g x ^ q) ^ q⁻¹) ≤
        D * ENNReal.ofReal ((∫ x : Euclidean d, ‖f x‖ ^ p) ^ p⁻¹) := by
      rw [← hnormG, ← hnormF]
      exact hnorm
    calc
      (∫ x : Euclidean d, g x ^ q) ^ q⁻¹ =
          (ENNReal.ofReal ((∫ x : Euclidean d, g x ^ q) ^ q⁻¹)).toReal := by
            rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hG _)]
      _ ≤ (D * ENNReal.ofReal ((∫ x : Euclidean d, ‖f x‖ ^ p) ^ p⁻¹)).toReal :=
        (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top hDtop ENNReal.ofReal_ne_top)).mpr hnorm'
      _ = D.toReal * (∫ x : Euclidean d, ‖f x‖ ^ p) ^ p⁻¹ := by
        simp only [ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)]
  have hraised := Real.rpow_le_rpow
    (Real.rpow_nonneg hG _) hrootbound hqNN
  calc
    (∫ x : Euclidean d, g x ^ q) =
        ((∫ x : Euclidean d, g x ^ q) ^ q⁻¹) ^ q := by
          rw [Real.rpow_inv_rpow hG (ne_of_gt hq)]
    _ ≤ (D.toReal * (∫ x : Euclidean d, ‖f x‖ ^ p) ^ p⁻¹) ^ q := hraised
    _ = D.toReal ^ q * (∫ x : Euclidean d, ‖f x‖ ^ p) ^ (q / p) := by
      rw [Real.mul_rpow ENNReal.toReal_nonneg (Real.rpow_nonneg hI _)]
      rw [← Real.rpow_mul hI]
      congr 1
      field_simp

/-- Strict geometric `Lᵖ → Lᑫ` estimates for the literal low-frequency and
dyadic pieces imply the full restricted spherical maximal estimate.

This is the endpoint-free off-diagonal reassembly theorem used after the
paper's shell estimates have been interpolated at a strict interior exponent.
Its hypotheses concern the actual cutoff pieces, so it does not postulate a
global maximal estimate or any positivity/factorization of an oscillatory
shell. -/
theorem absolute_off_diagonal_reassembly_from_eLpNorm
    {d : ℕ} {p q : ℝ} (hd0 : 0 < d) (hp : 0 < p) (hq : 1 ≤ q)
    (E : Set ℝ) (hEpos : E ⊆ Ioi (0 : ℝ))
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (CR CT ρ : ENNReal) (hCRtop : CR < ⊤) (hCTtop : CT < ⊤) (hρ : ρ < 1)
    (hregular : ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (fractalSphericalMaximalReal d E
        (absoluteCutoffProjection φ 0 f)) (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalSphericalMaximalReal d E
        (absoluteCutoffProjection φ 0 f)) (ENNReal.ofReal q) volume ≤
        CR * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume)
    (hdyadic : ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      MemLp (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass φ hφone hφzero j) f) (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass φ hφone hφzero j) f) (ENNReal.ofReal q) volume ≤
        (CT * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume) * ρ ^ j) :
    HasFractalSphericalStrongType d E p q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let D : ENNReal := CR + CT * (1 - ρ)⁻¹
  have hρpos : 0 < 1 - ρ := tsub_pos_of_lt hρ
  have hρinvtop : (1 - ρ)⁻¹ < ⊤ := ENNReal.inv_lt_top.mpr hρpos
  have hDtop : D < ⊤ := by
    dsimp only [D]
    exact ENNReal.add_lt_top.mpr
      ⟨hCRtop, ENNReal.mul_lt_top hCTtop hρinvtop⟩
  let C : ℝ := D.toReal ^ q + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  apply absolute_reassembly_limit_off_diagonal hd0 hp hq0 E hEpos φ hφone C hC
  intro N f
  let I : ℝ := ∫ x : Euclidean d, ‖f x‖ ^ p
  have hI : 0 ≤ I := by
    dsimp only [I]
    exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
  have hP : MemLp (fractalAbsoluteCutoffMaximal d E φ N f)
      (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalAbsoluteCutoffMaximal d E φ N f)
        (ENNReal.ofReal q) volume ≤
        D * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume := by
    simpa only [D] using
      finite_absolute_off_diagonal_reassembly_eLpNorm hd0 hp hq E hEpos φ hφone hφzero
        CR CT ρ hρ hregular hdyadic N f
  refine ⟨hP.1, ?_⟩
  change (∫ x : Euclidean d,
    (fractalAbsoluteCutoffMaximal d E φ N f x) ^ q) ≤ C * I ^ (q / p)
  calc
    (∫ x : Euclidean d,
        (fractalAbsoluteCutoffMaximal d E φ N f x) ^ q) ≤
        D.toReal ^ q * I ^ (q / p) := by
      simpa only [I] using
        off_diagonal_moment_bound_of_eLpNorm hp hq0
          (fractalAbsoluteCutoffMaximal d E φ N f) hP.1
          (fractalAbsoluteCutoffMaximal_nonneg E φ N f) f D hDtop.ne hP.2
    _ ≤ C * I ^ (q / p) := by
      apply mul_le_mul_of_nonneg_right
      · dsimp only [C]
        exact le_add_of_nonneg_right (by norm_num)
      · exact Real.rpow_nonneg hI _

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
