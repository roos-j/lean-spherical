/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.CoveringMaximal
import LeanSpherical.HarmonicAnalysis.FractalDilations.Definitions

/-!
# Finite-cover reductions for fractal spherical maximal operators

This file contains the part of the Minkowski-dimension argument which is
independent of Fourier analysis.  A finite cover of the dilation set reduces
the `L^q` norm of the maximal operator to the sum of the corresponding norms
on the covering intervals.

The result is deliberately conditional on estimates for the individual
intervals.  Establishing the scale-decaying interval estimates is the
oscillatory-analysis portion of the fractal-dilation theorem; this module does
not assume it.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Set
open intervalIntegral
open scoped BigOperators

noncomputable section

/-- A finite interval cover gives a genuine `L^q` maximal-function reduction.

The positivity hypotheses make all of the extended-real radius suprema finite,
so the elementary ENNReal cover inequality can be passed to its real-valued
version.  Minkowski's inequality then turns the finite sum into the displayed
sum of `L^q` seminorms. -/
theorem eLpNorm_fractalSphericalMaximalReal_le_sum_intervalCover
    {d : ℕ} {E : Set ℝ} {δ q : ℝ} {ι : Finset ℝ}
    (hd : 0 < d) (hcover : IsIntervalCover E δ ι)
    (hEpos : E ⊆ Ioi (0 : ℝ))
    (hιpos : ∀ c ∈ ι, Icc (c - δ / 2) (c + δ / 2) ⊆ Ioi (0 : ℝ))
    (hq : 1 ≤ ENNReal.ofReal q) (f : SchwartzMap (Euclidean d) ℂ) :
    eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume ≤
      ∑ c ∈ ι,
        eLpNorm (fractalSphericalMaximalReal d
          (Icc (c - δ / 2) (c + δ / 2)) f) (ENNReal.ofReal q) volume := by
  have hpoint (x : Euclidean d) :
      fractalSphericalMaximalReal d E f x ≤
        ∑ c ∈ ι,
          fractalSphericalMaximalReal d
            (Icc (c - δ / 2) (c + δ / 2)) f x := by
    have hraw := fractalSphericalMaximal_le_sum_intervalCover hcover
      (f : Euclidean d → ℂ) x
    have hEtop : fractalSphericalMaximal d E (f : Euclidean d → ℂ) x ≠ ⊤ :=
      fractalSphericalMaximal_ne_top hd E hEpos f x
    have hItop (c : ℝ) (hc : c ∈ ι) :
        fractalSphericalMaximal d (Icc (c - δ / 2) (c + δ / 2))
          (f : Euclidean d → ℂ) x ≠ ⊤ :=
      fractalSphericalMaximal_ne_top hd _ (hιpos c hc) f x
    have hsumtop :
        (∑ c ∈ ι,
          fractalSphericalMaximal d (Icc (c - δ / 2) (c + δ / 2))
            (f : Euclidean d → ℂ) x) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 hItop
    have hreal := (ENNReal.toReal_le_toReal hEtop hsumtop).mpr hraw
    simpa only [fractalSphericalMaximalReal, ENNReal.toReal_sum hItop] using hreal
  calc
    eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume ≤
        eLpNorm (fun x => ∑ c ∈ ι,
          fractalSphericalMaximalReal d
            (Icc (c - δ / 2) (c + δ / 2)) f x) (ENNReal.ofReal q) volume :=
      eLpNorm_mono_real fun x => by
        rw [Real.norm_of_nonneg]
        · exact hpoint x
        · exact ENNReal.toReal_nonneg
    _ = eLpNorm (∑ c ∈ ι, fun x =>
          fractalSphericalMaximalReal d
            (Icc (c - δ / 2) (c + δ / 2)) f x) (ENNReal.ofReal q) volume := by
      apply eLpNorm_congr_ae
      filter_upwards with x
      simp
    _ ≤ ∑ c ∈ ι,
        eLpNorm (fractalSphericalMaximalReal d
          (Icc (c - δ / 2) (c + δ / 2)) f) (ENNReal.ofReal q) volume :=
      eLpNorm_sum_le (f := fun c =>
        fractalSphericalMaximalReal d (Icc (c - δ / 2) (c + δ / 2)) f)
        (s := ι)
        (fun c _ =>
          (measurable_fractalSphericalMaximalReal
            (Icc (c - δ / 2) (c + δ / 2)) f).aestronglyMeasurable)
        hq

/-- The uniform form of the finite-cover reduction.  If every member of a
cover has the same `L^p → L^q` norm bound `C`, the cover costs exactly its
cardinality.  This is the point at which an upper Minkowski covering estimate
enters the usual dyadic argument. -/
theorem eLpNorm_fractalSphericalMaximalReal_le_card_mul_of_intervalCover
    {d : ℕ} {E : Set ℝ} {δ p q C : ℝ} {ι : Finset ℝ}
    (hd : 0 < d) (hcover : IsIntervalCover E δ ι)
    (hEpos : E ⊆ Ioi (0 : ℝ))
    (hιpos : ∀ c ∈ ι, Icc (c - δ / 2) (c + δ / 2) ⊆ Ioi (0 : ℝ))
    (hq : 1 ≤ ENNReal.ofReal q)
    (hlocal : ∀ c ∈ ι, ∀ f : SchwartzMap (Euclidean d) ℂ,
      eLpNorm (fractalSphericalMaximalReal d
        (Icc (c - δ / 2) (c + δ / 2)) f) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume)
    (f : SchwartzMap (Euclidean d) ℂ) :
    eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume ≤
      (ι.card : ENNReal) *
        (ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume) := by
  calc
    eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume ≤
        ∑ c ∈ ι,
          eLpNorm (fractalSphericalMaximalReal d
            (Icc (c - δ / 2) (c + δ / 2)) f) (ENNReal.ofReal q) volume :=
      eLpNorm_fractalSphericalMaximalReal_le_sum_intervalCover
        hd hcover hEpos hιpos hq f
    _ ≤ ∑ _c ∈ ι,
        ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume := by
      exact Finset.sum_le_sum fun c hc => hlocal c hc f
    _ = (ι.card : ENNReal) *
        (ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume) := by
      simp [nsmul_eq_mul]

/-- The elementary radius-discretization estimate behind a short interval
cover.  A spherical average at any radius in `[a,b]` is controlled by its
value at the left endpoint and the radius variation of the average.  The
derivative is written explicitly so this statement can be combined with
frequency-local derivative estimates. -/
theorem norm_sphericalAverage_le_leftEndpoint_add_radiusVariation
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : ∀ y, ‖fderiv ℝ f y‖ ≤ C)
    (x : Euclidean d) {a b r : ℝ} (hr : r ∈ Icc a b) :
    ‖sphericalAverage d f r x‖ ≤ ‖sphericalAverage d f a x‖ +
      ∫ t in a..b, ‖∫ ω : Metric.sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ := by
  have hfderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by norm_num)
  have hderiv_joint : Continuous (fun p : ℝ × Euclidean d =>
      ∫ ω : Metric.sphere (0 : Euclidean d) 1,
        fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := unitSurfaceMeasure d)
        ((hfderiv_cont.comp
          ((continuous_snd.comp continuous_fst).add
            ((continuous_fst.comp continuous_fst).smul
              (continuous_subtype_val.comp continuous_snd)))).clm_apply
            (continuous_subtype_val.comp continuous_snd))
        isCompact_univ)
  exact norm_le_norm_add_intervalIntegral_norm_of_hasDerivAt hr
    (hderiv_joint.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)))
    (fun t => hasDerivAt_sphericalAverage f hf hC x t)

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
