/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.AnnulusDominance
import LeanSpherical.HarmonicAnalysis.FractalDilations.AnnulusBump

/-!
# The mass lower bound for the Minkowski annulus test

For a nonnegative real bump, a finite separated family of radii produces a
sum of spherical averages whose total mass is the number of radii times the
mass of the bump.  Its support is a finite union of thin annuli, and it is
pointwise bounded by the restricted maximal operator.  This file packages
those three facts into the exact `L^q` lower-bound inequality used by the
Minkowski sharpness test.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The `L¹` seminorm of a nonnegative annular sum is its explicitly computed
mass. -/
theorem eLpNorm_one_annulusAverageSum_eq_ofReal_card_mul_integral
    {d : ℕ} (hd : 0 < d) (f : SchwartzMap (Euclidean d) ℂ) (s : Finset ℝ)
    (hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ))
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re) :
    eLpNorm (annulusAverageSum d (f : Euclidean d → ℂ) s) 1 volume =
      ENNReal.ofReal ((s.card : ℝ) * ∫ x : Euclidean d, (f x).re) := by
  have hsum_nonneg : ∀ x : Euclidean d,
      0 ≤ annulusAverageSum d (f : Euclidean d → ℂ) s x :=
    annulusAverageSum_nonneg hd (f : Euclidean d → ℂ) s hreal hnonneg
  have hsum_integrable : Integrable
      (annulusAverageSum d (f : Euclidean d → ℂ) s) volume :=
    integrable_annulusAverageSum (f : Euclidean d → ℂ) s f.continuous f.integrable
  calc
    eLpNorm (annulusAverageSum d (f : Euclidean d → ℂ) s) 1 volume =
        ∫⁻ x : Euclidean d, ‖annulusAverageSum d (f : Euclidean d → ℂ) s x‖ₑ :=
      eLpNorm_one_eq_lintegral_enorm
    _ = ∫⁻ x : Euclidean d,
        ENNReal.ofReal (annulusAverageSum d (f : Euclidean d → ℂ) s x) := by
      congr with x
      rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal (hsum_nonneg x)]
      congr
      exact NNReal.eq (Real.norm_of_nonneg (hsum_nonneg x))
    _ = ENNReal.ofReal (∫ x : Euclidean d,
        annulusAverageSum d (f : Euclidean d → ℂ) s x) :=
      (ofReal_integral_eq_lintegral_ofReal hsum_integrable
        (Filter.Eventually.of_forall hsum_nonneg)).symm
    _ = ENNReal.ofReal ((s.card : ℝ) * ∫ x : Euclidean d, (f x).re) := by
      rw [integral_annulusAverageSum_eq_card_mul hd (f : Euclidean d → ℂ) s
        f.continuous f.integrable hreal]

/-- The exact annulus mass is bounded by the maximal-function `L^q` norm
times the finite-annulus support factor.  This is the analytic core of the
Minkowski lower-bound test. -/
theorem ofReal_card_mul_integral_le_eLpNorm_fractalSphericalMaximal_mul_annuli
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hEpos : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {R δ : ℝ} (s : Finset ℝ)
    (hsE : (↑s : Set ℝ) ⊆ E)
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (hsep : StrictlySeparated s δ) (hRδ : 4 * R ≤ δ)
    (hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ))
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re)
    {q : ℝ} (hq : 1 ≤ q) :
    ENNReal.ofReal ((s.card : ℝ) * ∫ x : Euclidean d, (f x).re) ≤
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
        volume (⋃ r ∈ s, radialAnnulus d (abs r) (2 * R)) ^ (1 - q⁻¹) := by
  let H : Euclidean d → ℝ := annulusAverageSum d (f : Euclidean d → ℂ) s
  let U : Set (Euclidean d) := ⋃ r ∈ s, radialAnnulus d (abs r) (2 * R)
  have hH_nonneg : ∀ x : Euclidean d, 0 ≤ H x := by
    exact annulusAverageSum_nonneg hd (f : Euclidean d → ℂ) s hreal hnonneg
  have hH_integrable : Integrable H volume := by
    exact integrable_annulusAverageSum (f : Euclidean d → ℂ) s f.continuous f.integrable
  have hH_support : Function.support H ⊆ U := by
    exact support_annulusAverageSum_subset hd (f : Euclidean d → ℂ) hzero s
  have hH_le_max : ∀ x : Euclidean d,
      H x ≤ fractalSphericalMaximalReal d E f x := by
    exact annulusAverageSum_le_fractalSphericalMaximalReal hd E hEpos f s hsE
      hzero hsep hRδ
  have hmax_nonneg : ∀ x : Euclidean d,
      0 ≤ fractalSphericalMaximalReal d E f x := by
    intro x
    unfold fractalSphericalMaximalReal
    exact ENNReal.toReal_nonneg
  have hH_norm_le :
      eLpNorm H (ENNReal.ofReal q) volume ≤
        eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_of_nonneg (hH_nonneg x),
      Real.norm_of_nonneg (hmax_nonneg x)]
    exact hH_le_max x
  have hfinite_support := eLpNorm_one_le_eLpNorm_of_support_subset hq
    hH_integrable.aestronglyMeasurable hH_support
  calc
    ENNReal.ofReal ((s.card : ℝ) * ∫ x : Euclidean d, (f x).re) =
        eLpNorm H 1 volume := by
      exact eLpNorm_one_annulusAverageSum_eq_ofReal_card_mul_integral
        hd f s hreal hnonneg |>.symm
    _ ≤ eLpNorm H (ENNReal.ofReal q) volume * volume U ^ (1 - q⁻¹) :=
      hfinite_support
    _ ≤ eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
        volume U ^ (1 - q⁻¹) := by
      exact mul_le_mul_left hH_norm_le _

/-- For a smooth nonnegative ball cutoff, the exact mass in the preceding
lemma is at least the cardinality times the volume of its inner ball. -/
theorem ofReal_card_mul_volume_ball_toReal_le_eLpNorm_fractalSphericalMaximal_mul_annuli
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hEpos : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {R δ : ℝ} (s : Finset ℝ)
    (hsE : (↑s : Set ℝ) ⊆ E)
    (hOne : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (hsep : StrictlySeparated s δ) (hRδ : 4 * R ≤ δ)
    (hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ))
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re)
    {q : ℝ} (hq : 1 ≤ q) :
    ENNReal.ofReal ((s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal) ≤
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
        volume (⋃ r ∈ s, radialAnnulus d (abs r) (2 * R)) ^ (1 - q⁻¹) := by
  have hball_mass : (volume (ball (0 : Euclidean d) R)).toReal ≤
      ∫ x : Euclidean d, (f x).re :=
    volume_ball_toReal_le_integral_re_of_eq_one_nonneg f hOne hnonneg
  have hmass : (s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal ≤
      (s.card : ℝ) * ∫ x : Euclidean d, (f x).re :=
    mul_le_mul_of_nonneg_left hball_mass (Nat.cast_nonneg _)
  calc
    ENNReal.ofReal ((s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal) ≤
        ENNReal.ofReal ((s.card : ℝ) * ∫ x : Euclidean d, (f x).re) :=
      ENNReal.ofReal_le_ofReal hmass
    _ ≤ eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
        volume (⋃ r ∈ s, radialAnnulus d (abs r) (2 * R)) ^ (1 - q⁻¹) :=
      ofReal_card_mul_integral_le_eLpNorm_fractalSphericalMaximal_mul_annuli
        hd E hEpos f s hsE hzero hsep hRδ hreal hnonneg hq

/-- Replacing the actual annular support by the explicit finite-union volume
bound gives the form of the mass estimate used in scale calculations. -/
theorem ofReal_card_mul_volume_ball_toReal_le_eLpNorm_fractalSphericalMaximal_mul_annulusVolumeBound
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2)
    (f : SchwartzMap (Euclidean d) ℂ) {R δ : ℝ} (s : Finset ℝ)
    (hsE : (↑s : Set ℝ) ⊆ E)
    (hOne : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (hsep : StrictlySeparated s δ) (hRδ : 4 * R ≤ δ)
    (hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ))
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re)
    (hR : 0 < R) (hRquarter : R ≤ 1 / 4)
    {q : ℝ} (hq : 1 ≤ q) :
    ENNReal.ofReal ((s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal) ≤
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
        ((s.card : ENNReal) *
          (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
            volume (ball (0 : Euclidean d) 1))) ^ (1 - q⁻¹) := by
  let U : Set (Euclidean d) := ⋃ r ∈ s, radialAnnulus d (abs r) (2 * R)
  let V : ENNReal := (s.card : ENNReal) *
    (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
      volume (ball (0 : Euclidean d) 1))
  have hEpos : E ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one (hE hr).1
  have hmass :=
    ofReal_card_mul_volume_ball_toReal_le_eLpNorm_fractalSphericalMaximal_mul_annuli
      hd E hEpos f s hsE hOne hzero hsep hRδ hreal hnonneg hq
  have hvolume : volume U ≤ V := by
    exact volume_biUnion_radialAnnulus_abs_le d hsE hE (by linarith) (by linarith)
  have hexp_nonneg : 0 ≤ 1 - q⁻¹ := by
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hq)
  have hvolume_rpow : volume U ^ (1 - q⁻¹) ≤ V ^ (1 - q⁻¹) :=
    ENNReal.rpow_le_rpow hvolume hexp_nonneg
  change ENNReal.ofReal ((s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal) ≤
    eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
      V ^ (1 - q⁻¹)
  calc
    ENNReal.ofReal ((s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal) ≤
        eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
          volume U ^ (1 - q⁻¹) := hmass
    _ ≤ eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
          V ^ (1 - q⁻¹) :=
      mul_le_mul_right hvolume_rpow _

/-- A finite nonzero support factor can be cancelled from a mass lower bound.
This is stated abstractly over `ENNReal` so that the scale calculation for
the annulus test can be carried out entirely in real numbers. -/
theorem ENNReal.ofReal_mul_lt_of_mass_le_mul_and_toReal_gap
    {C L : ℝ} {A B out : ENNReal}
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hA_top : A ≠ (⊤ : ENNReal))
    (hB_zero : B ≠ 0) (hB_top : B ≠ (⊤ : ENNReal))
    (hmass : ENNReal.ofReal L ≤ out * B)
    (hgap : C * A.toReal * B.toReal < L) :
    ENNReal.ofReal C * A < out := by
  by_cases hout_top : out = (⊤ : ENNReal)
  · rw [hout_top]
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA_top)
  · apply (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA_top) hout_top).mp
    have hmass_real : L ≤ out.toReal * B.toReal := by
      have hprod_top : out * B ≠ (⊤ : ENNReal) := ENNReal.mul_ne_top hout_top hB_top
      have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hprod_top).mpr hmass
      simpa [ENNReal.toReal_ofReal hL, ENNReal.toReal_mul] using h
    have hB_pos : 0 < B.toReal := ENNReal.toReal_pos hB_zero hB_top
    have hreal_gap : C * A.toReal < out.toReal := by
      apply lt_of_mul_lt_mul_right _ hB_pos.le
      calc
        (C * A.toReal) * B.toReal = C * A.toReal * B.toReal := by ring
        _ < L := hgap
        _ ≤ out.toReal * B.toReal := hmass_real
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hreal_gap

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
