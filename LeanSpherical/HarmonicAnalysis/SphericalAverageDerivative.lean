/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceFoundation
import LeanSpherical.HarmonicAnalysis.FixedRadiusL2
import LeanSpherical.HarmonicAnalysis.RadiusSobolevL2
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating spherical averages in the radius

For a `C¹` input with uniformly bounded derivative, differentiation under the
finite surface integral gives the ordinary directional-derivative formula.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Metric Set

noncomputable section

/-- A spherical average of a `C¹` function with bounded derivative is
differentiable in its radius. -/
theorem hasDerivAt_sphericalAverage
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ f y‖ ≤ C) (x : Euclidean d) (r : ℝ) :
    HasDerivAt (fun t => sphericalAverage d f t x)
      (∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d) r := by
  have hf_cont : Continuous f := hf.continuous
  have hfderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by norm_num)
  have hpath (t : ℝ) : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
      x + t • (ω : Euclidean d)) :=
    continuous_const.add
      ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => t).smul
        continuous_subtype_val)
  have hF_meas : ∀ᶠ t in nhds r, AEStronglyMeasurable
      (fun ω : sphere (0 : Euclidean d) 1 => f (x + t • (ω : Euclidean d)))
      (unitSurfaceMeasure d) := by
    filter_upwards [] with t
    exact (hf_cont.comp (hpath t)).aestronglyMeasurable
  have hF_int : Integrable
      (fun ω : sphere (0 : Euclidean d) 1 => f (x + r • (ω : Euclidean d)))
      (unitSurfaceMeasure d) := by
    have hcont := hf_cont.comp (hpath r)
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
    exact Integrable.of_bound hcont.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => hB ω (mem_univ _))
  have hF'_meas : AEStronglyMeasurable
      (fun ω : sphere (0 : Euclidean d) 1 =>
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d))
      (unitSurfaceMeasure d) := by
    exact ((hfderiv_cont.comp (hpath r)).clm_apply continuous_subtype_val).aestronglyMeasurable
  have hbound : ∀ᵐ ω : sphere (0 : Euclidean d) 1 ∂unitSurfaceMeasure d,
      ∀ t ∈ (Set.univ : Set ℝ),
        ‖fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)‖ ≤ C := by
    filter_upwards with ω
    intro t ht
    calc
      ‖fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)‖ ≤
          ‖fderiv ℝ f (x + t • (ω : Euclidean d))‖ * ‖(ω : Euclidean d)‖ :=
        (fderiv ℝ f (x + t • (ω : Euclidean d))).le_opNorm _
      _ = ‖fderiv ℝ f (x + t • (ω : Euclidean d))‖ := by
        rw [mem_sphere_zero_iff_norm.mp ω.property, mul_one]
      _ ≤ C := hC _
  have hdiff : ∀ᵐ ω : sphere (0 : Euclidean d) 1 ∂unitSurfaceMeasure d,
      ∀ t ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun s : ℝ => f (x + s • (ω : Euclidean d)))
          (fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)) t := by
    filter_upwards with ω
    intro t ht
    have hline : HasDerivAt (fun s : ℝ => x + s • (ω : Euclidean d))
        (ω : Euclidean d) t := by
      simpa using ((hasDerivAt_id t).smul_const (ω : Euclidean d)).const_add x
    simpa [Function.comp_def] using
      (hf.differentiable_one (x + t • (ω : Euclidean d))).hasFDerivAt.comp_hasDerivAt t hline
  simpa only [sphericalAverage] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := unitSurfaceMeasure d) (s := Set.univ) (x₀ := r)
      (bound := fun _ : sphere (0 : Euclidean d) 1 => C)
      (F := fun t ω => f (x + t • (ω : Euclidean d)))
      (F' := fun t ω => fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d))
      Filter.univ_mem hF_meas hF_int hF'_meas hbound (integrable_const _) hdiff).2

private theorem integrable_and_integral_norm_sq_sphericalAverage_radiusDerivative
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp (fderiv ℝ f) 2 volume) (r : ℝ) :
    Integrable (fun x : Euclidean d =>
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ ^ 2) volume ∧
      (∫ x : Euclidean d,
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ ^ 2) ≤
      surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2 := by
  have hfderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by norm_num)
  have hD_sq : Integrable (fun x : Euclidean d => ‖fderiv ℝ f x‖ ^ 2) volume := by
    rw [← memLp_one_iff_integrable]
    simpa [Real.rpow_two] using hf2.norm_rpow (by norm_num) (by norm_num)
  have hH_prod : Integrable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        ‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))‖ ^ 2)
      (volume.prod (unitSurfaceMeasure d)) := by
    have hmeas : AEStronglyMeasurable
        (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
          ‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))‖ ^ 2)
        (volume.prod (unitSurfaceMeasure d)) := by
      apply (hfderiv_cont.norm.pow 2).comp
        (continuous_fst.add
          ((continuous_const :
            Continuous fun _ : Euclidean d × sphere (0 : Euclidean d) 1 => r).smul
            (continuous_subtype_val.comp continuous_snd))) |>.aestronglyMeasurable
    refine (integrable_prod_iff' hmeas).2 ?_
    constructor
    · filter_upwards with ω
      exact hD_sq.comp_add_right (r • (ω : Euclidean d))
    · have heq : (fun ω : sphere (0 : Euclidean d) 1 =>
          ∫ x : Euclidean d, ‖‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ ^ 2‖) =
          fun _ => ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2 := by
        funext ω
        calc
          (∫ x : Euclidean d, ‖‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ ^ 2‖) =
              ∫ x : Euclidean d, ‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Real.norm_eq_abs]
            exact abs_of_nonneg (sq_nonneg _)
          _ = ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2 :=
            integral_add_right_eq_self (fun x : Euclidean d => ‖fderiv ℝ f x‖ ^ 2)
              (r • (ω : Euclidean d))
      change Integrable (fun ω : sphere (0 : Euclidean d) 1 =>
        ∫ x : Euclidean d, ‖‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ ^ 2‖)
        (unitSurfaceMeasure d)
      rw [heq]
      exact integrable_const _
  have hG_prod : Integrable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        ‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d)) (p.2 : Euclidean d)‖ ^ 2)
      (volume.prod (unitSurfaceMeasure d)) := by
    refine Integrable.mono hH_prod ?_ ?_
    · exact (hfderiv_cont.comp
        (continuous_fst.add
          ((continuous_const :
            Continuous fun _ : Euclidean d × sphere (0 : Euclidean d) 1 => r).smul
            (continuous_subtype_val.comp continuous_snd)))).clm_apply
          (continuous_subtype_val.comp continuous_snd) |>.norm.pow 2 |>.aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
      calc
        ‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d)) (p.2 : Euclidean d)‖ ^ 2 ≤
            (‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))‖ * ‖(p.2 : Euclidean d)‖) ^ 2 := by
          gcongr
          exact (fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))).le_opNorm _
        _ = ‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))‖ ^ 2 := by
          rw [mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
  have hjoint : Continuous (Function.uncurry
      (fun (x : Euclidean d) (ω : sphere (0 : Euclidean d) 1) =>
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d))) := by
    exact (hfderiv_cont.comp
      (continuous_fst.add
        ((continuous_const : Continuous fun _ : Euclidean d × sphere (0 : Euclidean d) 1 => r).smul
          (continuous_subtype_val.comp continuous_snd)))).clm_apply
            (continuous_subtype_val.comp continuous_snd)
  have houtput_cont : Continuous (fun x : Euclidean d =>
      ∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := unitSurfaceMeasure d) hjoint isCompact_univ)
  have hpoint (x : Euclidean d) :
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ ^ 2 ≤
        surfaceMass d * ∫ ω : sphere (0 : Euclidean d) 1,
          ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2
            ∂unitSurfaceMeasure d := by
    have hcont : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)) :=
      (hfderiv_cont.comp
        (continuous_const.add
          ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => r).smul
            continuous_subtype_val))).clm_apply continuous_subtype_val
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
    have hmem : MemLp (fun ω : sphere (0 : Euclidean d) 1 =>
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)) 2
        (unitSurfaceMeasure d) :=
      (memLp_top_of_bound hcont.aestronglyMeasurable B
        (Filter.Eventually.of_forall fun ω => hB ω (mem_univ _))).mono_exponent (by norm_num)
    simpa [surfaceMass] using
      norm_integral_sq_le_measureReal_mul_integral_norm_sq
        (unitSurfaceMeasure d)
        (fun ω : sphere (0 : Euclidean d) 1 =>
          fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)) hmem
  have hright : Integrable (fun x : Euclidean d =>
      surfaceMass d * ∫ ω : sphere (0 : Euclidean d) 1,
        ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2
          ∂unitSurfaceMeasure d) volume :=
    hG_prod.integral_prod_left.const_mul _
  have hleft : Integrable (fun x : Euclidean d =>
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ ^ 2) volume := by
    refine Integrable.mono hright (houtput_cont.norm.pow 2).aestronglyMeasurable ?_
    filter_upwards with x
    have hnonneg : 0 ≤ surfaceMass d * ∫ ω : sphere (0 : Euclidean d) 1,
        ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2
          ∂unitSurfaceMeasure d := by
      exact mul_nonneg measureReal_nonneg (integral_nonneg fun _ => sq_nonneg _)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hnonneg]
    exact hpoint x
  have hdirection_integrable (ω : sphere (0 : Euclidean d) 1) : Integrable
      (fun x : Euclidean d =>
        ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2) volume := by
    refine Integrable.mono (hD_sq.comp_add_right (r • (ω : Euclidean d))) ?_ ?_
    · exact ((hfderiv_cont.comp
        (continuous_id.add (continuous_const : Continuous fun _ : Euclidean d =>
          r • (ω : Euclidean d)))).clm_apply continuous_const).norm.pow 2 |>.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
      calc
        ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2 ≤
            (‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ * ‖(ω : Euclidean d)‖) ^ 2 := by
          gcongr
          exact (fderiv ℝ f (x + r • (ω : Euclidean d))).le_opNorm _
        _ = ‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ ^ 2 := by
          rw [mem_sphere_zero_iff_norm.mp ω.property, mul_one]
  have hinner (ω : sphere (0 : Euclidean d) 1) :
      (∫ x : Euclidean d,
        ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2) ≤
        ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2 := by
    calc
      (∫ x : Euclidean d,
        ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2) ≤
          ∫ x : Euclidean d, ‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ ^ 2 := by
        apply integral_mono (hdirection_integrable ω)
          (hD_sq.comp_add_right (r • (ω : Euclidean d)))
        intro x
        calc
          ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2 ≤
              (‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ * ‖(ω : Euclidean d)‖) ^ 2 := by
            gcongr
            exact (fderiv ℝ f (x + r • (ω : Euclidean d))).le_opNorm _
          _ = ‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ ^ 2 := by
            rw [mem_sphere_zero_iff_norm.mp ω.property, mul_one]
      _ = ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2 :=
        integral_add_right_eq_self (fun x : Euclidean d => ‖fderiv ℝ f x‖ ^ 2)
          (r • (ω : Euclidean d))
  have houter :
      (∫ ω : sphere (0 : Euclidean d) 1,
        (∫ x : Euclidean d,
          ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2)
            ∂unitSurfaceMeasure d) ≤
        ∫ ω : sphere (0 : Euclidean d) 1,
          (∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2) ∂unitSurfaceMeasure d := by
    apply integral_mono hG_prod.integral_prod_right (integrable_const _)
    intro ω
    exact hinner ω
  refine ⟨hleft, ?_⟩
  calc
    (∫ x : Euclidean d,
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ ^ 2) ≤
        ∫ x : Euclidean d, surfaceMass d * ∫ ω : sphere (0 : Euclidean d) 1,
          ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2
            ∂unitSurfaceMeasure d := by
      apply integral_mono_ae hleft hright
      filter_upwards with x
      exact hpoint x
    _ = surfaceMass d * ∫ x : Euclidean d,
        ∫ ω : sphere (0 : Euclidean d) 1,
          ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2
            ∂unitSurfaceMeasure d := by
      rw [integral_const_mul]
    _ = surfaceMass d * (∫ ω : sphere (0 : Euclidean d) 1,
        (∫ x : Euclidean d,
          ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ^ 2 ∂volume)
            ∂unitSurfaceMeasure d) := by
      rw [integral_integral_swap hG_prod]
    _ ≤ surfaceMass d * (∫ ω : sphere (0 : Euclidean d) 1,
        (∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2 ∂volume)
          ∂unitSurfaceMeasure d) :=
      mul_le_mul_of_nonneg_left houter measureReal_nonneg
    _ = surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2 := by
      simp [surfaceMass]
      ring

/-- The square of the radius derivative of a spherical average is integrable
in the centre variable. -/
theorem integrable_norm_sq_sphericalAverage_radiusDerivative
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp (fderiv ℝ f) 2 volume) (r : ℝ) :
    Integrable (fun x : Euclidean d =>
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ ^ 2) volume :=
  (integrable_and_integral_norm_sq_sphericalAverage_radiusDerivative f hf hf2 r).1

/-- The radius derivative of a spherical average has the same fixed-radius
`L²` bound as a spherical average, with the input replaced by its spatial
derivative. -/
theorem integral_norm_sq_sphericalAverage_radiusDerivative_le_surfaceMass_sq_mul
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp (fderiv ℝ f) 2 volume) (r : ℝ) :
    (∫ x : Euclidean d,
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ ^ 2) ≤
      surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2 :=
  (integrable_and_integral_norm_sq_sphericalAverage_radiusDerivative f hf hf2 r).2

private theorem integrable_radiusDerivative_product
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hf1 : Integrable (fderiv ℝ f) volume) (r : ℝ) :
    Integrable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        fderiv ℝ f (p.1 + r • (p.2 : Euclidean d)) (p.2 : Euclidean d))
      (volume.prod (unitSurfaceMeasure d)) := by
  have hfderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by norm_num)
  have hnorm_prod : Integrable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        ‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))‖)
      (volume.prod (unitSurfaceMeasure d)) := by
    have hmeas : AEStronglyMeasurable
        (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
          ‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))‖)
        (volume.prod (unitSurfaceMeasure d)) := by
      apply (hfderiv_cont.norm.comp
        (continuous_fst.add
          ((continuous_const :
            Continuous fun _ : Euclidean d × sphere (0 : Euclidean d) 1 => r).smul
            (continuous_subtype_val.comp continuous_snd)))).aestronglyMeasurable
    refine (integrable_prod_iff' hmeas).2 ?_
    constructor
    · filter_upwards with ω
      exact hf1.norm.comp_add_right (r • (ω : Euclidean d))
    · have heq : (fun ω : sphere (0 : Euclidean d) 1 =>
          ∫ x : Euclidean d,
            ‖‖fderiv ℝ f (x + r • (ω : Euclidean d))‖‖) =
          fun _ => ∫ x : Euclidean d, ‖fderiv ℝ f x‖ := by
        funext ω
        calc
          (∫ x : Euclidean d,
            ‖‖fderiv ℝ f (x + r • (ω : Euclidean d))‖‖) =
              ∫ x : Euclidean d, ‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Real.norm_eq_abs]
            exact abs_of_nonneg (norm_nonneg _)
          _ = ∫ x : Euclidean d, ‖fderiv ℝ f x‖ :=
            integral_add_right_eq_self (fun x : Euclidean d => ‖fderiv ℝ f x‖)
              (r • (ω : Euclidean d))
      change Integrable (fun ω : sphere (0 : Euclidean d) 1 =>
        ∫ x : Euclidean d,
          ‖‖fderiv ℝ f (x + r • (ω : Euclidean d))‖‖)
        (unitSurfaceMeasure d)
      rw [heq]
      exact integrable_const _
  refine Integrable.mono hnorm_prod ?_ ?_
  · exact ((hfderiv_cont.comp
      (continuous_fst.add
        ((continuous_const :
          Continuous fun _ : Euclidean d × sphere (0 : Euclidean d) 1 => r).smul
          (continuous_subtype_val.comp continuous_snd)))).clm_apply
        (continuous_subtype_val.comp continuous_snd)).aestronglyMeasurable
  · filter_upwards with p
    calc
      ‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d)) (p.2 : Euclidean d)‖ ≤
          ‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))‖ * ‖(p.2 : Euclidean d)‖ :=
        (fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))).le_opNorm _
      _ = ‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))‖ := by
        rw [mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
      _ = ‖‖fderiv ℝ f (p.1 + r • (p.2 : Euclidean d))‖‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- For an integrable spatial derivative, the radius derivative of a spherical
average is integrable in its centre variable. -/
theorem integrable_sphericalAverage_radiusDerivative
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hf1 : Integrable (fderiv ℝ f) volume) (r : ℝ) :
    Integrable (fun x : Euclidean d =>
      ∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d) volume :=
  (integrable_radiusDerivative_product f hf hf1 r).integral_prod_left

/-- The radius derivative of a spherical average obeys the direct fixed-radius
`L¹` estimate from Fubini and translation invariance. -/
theorem integral_norm_sphericalAverage_radiusDerivative_le_surfaceMass_mul
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hf1 : Integrable (fderiv ℝ f) volume) (r : ℝ) :
    (∫ x : Euclidean d,
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖) ≤
      surfaceMass d * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ := by
  have hfderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by norm_num)
  have hprod := integrable_radiusDerivative_product f hf hf1 r
  have hinner (ω : sphere (0 : Euclidean d) 1) :
      (∫ x : Euclidean d,
        ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖) ≤
        ∫ x : Euclidean d, ‖fderiv ℝ f x‖ := by
    have hshift : Integrable (fun x : Euclidean d =>
        fderiv ℝ f (x + r • (ω : Euclidean d))) volume :=
      hf1.comp_add_right (r • (ω : Euclidean d))
    have hdirection : Integrable (fun x : Euclidean d =>
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)) volume := by
      refine Integrable.mono hshift ?_ ?_
      · exact ((hfderiv_cont.comp
          (continuous_id.add (continuous_const : Continuous fun _ : Euclidean d =>
            r • (ω : Euclidean d)))).clm_apply continuous_const).aestronglyMeasurable
      · filter_upwards with x
        calc
          ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ≤
              ‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ * ‖(ω : Euclidean d)‖ :=
            (fderiv ℝ f (x + r • (ω : Euclidean d))).le_opNorm _
          _ = ‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ := by
            rw [mem_sphere_zero_iff_norm.mp ω.property, mul_one]
    calc
      (∫ x : Euclidean d,
        ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖) ≤
          ∫ x : Euclidean d, ‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ := by
        apply integral_mono hdirection.norm hshift.norm
        intro x
        calc
          ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖ ≤
              ‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ * ‖(ω : Euclidean d)‖ :=
            (fderiv ℝ f (x + r • (ω : Euclidean d))).le_opNorm _
          _ = ‖fderiv ℝ f (x + r • (ω : Euclidean d))‖ := by
            rw [mem_sphere_zero_iff_norm.mp ω.property, mul_one]
      _ = ∫ x : Euclidean d, ‖fderiv ℝ f x‖ :=
        integral_add_right_eq_self (fun x : Euclidean d => ‖fderiv ℝ f x‖)
          (r • (ω : Euclidean d))
  have houter :
      (∫ ω : sphere (0 : Euclidean d) 1,
        (∫ x : Euclidean d,
          ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖)
          ∂unitSurfaceMeasure d) ≤
        ∫ ω : sphere (0 : Euclidean d) 1,
          (∫ x : Euclidean d, ‖fderiv ℝ f x‖)
          ∂unitSurfaceMeasure d := by
    apply integral_mono hprod.norm.integral_prod_right (integrable_const _)
    intro ω
    exact hinner ω
  calc
    (∫ x : Euclidean d,
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖) ≤
        ∫ x : Euclidean d,
          ∫ ω : sphere (0 : Euclidean d) 1,
            ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖
              ∂unitSurfaceMeasure d := by
      apply integral_mono_ae hprod.integral_prod_left.norm hprod.norm.integral_prod_left
      filter_upwards with x
      exact norm_integral_le_integral_norm _
    _ = ∫ ω : sphere (0 : Euclidean d) 1,
        (∫ x : Euclidean d,
          ‖fderiv ℝ f (x + r • (ω : Euclidean d)) (ω : Euclidean d)‖)
          ∂unitSurfaceMeasure d :=
      integral_integral_swap hprod.norm
    _ ≤ ∫ ω : sphere (0 : Euclidean d) 1,
        (∫ x : Euclidean d, ‖fderiv ℝ f x‖)
          ∂unitSurfaceMeasure d := houter
    _ = surfaceMass d * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ := by
      simp [surfaceMass]

/-- The square of the radius derivative is integrable jointly over a compact
radius interval and the centre variable. -/
theorem integrable_sq_radiusDerivative_prod
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hfderiv2 : MemLp (fderiv ℝ f) 2 volume) (a b : ℝ) :
    Integrable (fun p : ℝ × Euclidean d =>
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ ^ 2)
      ((volume.restrict (Icc a b)).prod volume) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let K : ℝ := surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2
  change Integrable (fun p : ℝ × Euclidean d =>
    ‖∫ ω : sphere (0 : Euclidean d) 1,
      fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d)
        ∂unitSurfaceMeasure d‖ ^ 2) (ν.prod volume)
  have hfderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by norm_num)
  have hderiv_integrand : Continuous (Function.uncurry
      (fun (p : ℝ × Euclidean d) (ω : sphere (0 : Euclidean d) 1) =>
        fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d))) := by
    exact (hfderiv_cont.comp
      ((continuous_snd.comp continuous_fst).add
        ((continuous_fst.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd)))).clm_apply
            (continuous_subtype_val.comp continuous_snd)
  have hderiv_joint : Continuous (fun p : ℝ × Euclidean d =>
      ∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := unitSurfaceMeasure d) hderiv_integrand isCompact_univ)
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × Euclidean d =>
        ‖∫ ω : sphere (0 : Euclidean d) 1,
          fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d)
            ∂unitSurfaceMeasure d‖ ^ 2)
      (ν.prod volume) :=
    (hderiv_joint.norm.pow 2).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).2 ?_
  constructor
  · filter_upwards with t
    exact integrable_norm_sq_sphericalAverage_radiusDerivative f hf hfderiv2 t
  · have houter_meas : AEStronglyMeasurable
        (fun t : ℝ => ∫ x : Euclidean d,
          ‖∫ ω : sphere (0 : Euclidean d) 1,
            fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
              ∂unitSurfaceMeasure d‖ ^ 2) ν := by
      exact
        ((hderiv_joint.norm.pow 2).stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    have houter : Integrable
        (fun t : ℝ => ∫ x : Euclidean d,
          ‖∫ ω : sphere (0 : Euclidean d) 1,
            fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
              ∂unitSurfaceMeasure d‖ ^ 2) ν := by
      apply Integrable.of_bound houter_meas K
      filter_upwards with t
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact integral_norm_sq_sphericalAverage_radiusDerivative_le_surfaceMass_sq_mul
        f hf hfderiv2 t
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using houter

/-- On a compact radius interval, the square integral of a spherical average
is controlled by the square integrals of the function and its spatial
derivative. -/
theorem integral_norm_sq_sphericalAverage_le_local_radiusSobolev
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hfderiv2 : MemLp (fderiv ℝ f) 2 volume) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ f y‖ ≤ C) {a b r : ℝ} (hr : r ∈ Icc a b) :
    (∫ x : Euclidean d, ‖sphericalAverage d f r x‖ ^ 2) ≤
      2 * (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2) +
        2 * (b - a) ^ 2 *
          (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let K : ℝ := surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2
  have hab : a ≤ b := hr.1.trans hr.2
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
  have hfderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by norm_num)
  have hderiv_integrand : Continuous (Function.uncurry
      (fun (p : ℝ × Euclidean d) (ω : sphere (0 : Euclidean d) 1) =>
        fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d))) := by
    exact (hfderiv_cont.comp
      ((continuous_snd.comp continuous_fst).add
        ((continuous_fst.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd)))).clm_apply
            (continuous_subtype_val.comp continuous_snd)
  have hderiv_joint : Continuous (fun p : ℝ × Euclidean d =>
      ∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := unitSurfaceMeasure d) hderiv_integrand isCompact_univ)
  have hderiv_sq_prod : Integrable
      (fun p : ℝ × Euclidean d =>
        ‖∫ ω : sphere (0 : Euclidean d) 1,
          fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d)
            ∂unitSurfaceMeasure d‖ ^ 2)
      (ν.prod volume) := by
    simpa only [ν] using
      integrable_sq_radiusDerivative_prod
        f hf hfderiv2 a b
  have hderiv_outer : Integrable
      (fun t : ℝ => ∫ x : Euclidean d,
        ‖∫ ω : sphere (0 : Euclidean d) 1,
          fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
            ∂unitSurfaceMeasure d‖ ^ 2) ν :=
    hderiv_sq_prod.integral_prod_left
  have hderiv_interval :
      (∫ t in a..b, ∫ x : Euclidean d,
        ‖∫ ω : sphere (0 : Euclidean d) 1,
          fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
            ∂unitSurfaceMeasure d‖ ^ 2) ≤ (b - a) * K := by
    calc
      (∫ t in a..b, ∫ x : Euclidean d,
        ‖∫ ω : sphere (0 : Euclidean d) 1,
          fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
            ∂unitSurfaceMeasure d‖ ^ 2) =
          ∫ t : ℝ, (∫ x : Euclidean d,
            ‖∫ ω : sphere (0 : Euclidean d) 1,
              fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
                ∂unitSurfaceMeasure d‖ ^ 2) ∂ν := by
        simp only [ν]
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
      _ ≤ ∫ _ : ℝ, K ∂ν := by
        apply integral_mono_ae hderiv_outer (integrable_const _)
        filter_upwards with t
        exact integral_norm_sq_sphericalAverage_radiusDerivative_le_surfaceMass_sq_mul
          f hf hfderiv2 t
      _ = (b - a) * K := by
        have hν : ν.real univ = b - a := by
          simp [ν, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal hlength]
        rw [MeasureTheory.integral_const, hν]
        rfl
  have havg_cont (t : ℝ) : Continuous (fun x : Euclidean d =>
      sphericalAverage d f t x) := by
    unfold sphericalAverage
    have hintegrand : Continuous (Function.uncurry
        (fun (x : Euclidean d) (ω : sphere (0 : Euclidean d) 1) =>
          f (x + t • (ω : Euclidean d)))) := by
      exact hf.continuous.comp
        (continuous_fst.add
          ((continuous_const :
            Continuous fun _ : Euclidean d × sphere (0 : Euclidean d) 1 => t).smul
              (continuous_subtype_val.comp continuous_snd)))
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := unitSurfaceMeasure d) hintegrand isCompact_univ)
  have hsobolev := integral_norm_sq_radius_le_of_hasDerivAt
    (F := fun t x => sphericalAverage d f t x)
    (F' := fun t x => ∫ ω : sphere (0 : Euclidean d) 1,
      fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
        ∂unitSurfaceMeasure d)
    hr (havg_cont r).aestronglyMeasurable
    (fun x => hderiv_joint.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)))
    (fun t x => hasDerivAt_sphericalAverage f hf hC x t)
    (integrable_norm_sq_sphericalAverage f hf.continuous hf1 hf2 a)
    hderiv_sq_prod
  have hfixed := integral_norm_sq_sphericalAverage_le_surfaceMass_sq_mul
    f hf.continuous hf1 hf2 a
  calc
    (∫ x : Euclidean d, ‖sphericalAverage d f r x‖ ^ 2) ≤
        2 * (∫ x : Euclidean d, ‖sphericalAverage d f a x‖ ^ 2) +
          2 * (b - a) *
            (∫ t in a..b, ∫ x : Euclidean d,
              ‖∫ ω : sphere (0 : Euclidean d) 1,
                fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
                  ∂unitSurfaceMeasure d‖ ^ 2) := hsobolev
    _ ≤ 2 * (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2) +
          2 * (b - a) * ((b - a) * K) := by
      gcongr
    _ = 2 * (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2) +
          2 * (b - a) ^ 2 *
            (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2) := by
      dsimp [K]
      ring

end

end LeanSpherical.HarmonicAnalysis
