/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FourierBridge
import LeanSpherical.HarmonicAnalysis.SurfaceFoundation
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Fixed-radius `L²` estimates for spherical averages

The estimates here are proved directly from Cauchy--Schwarz on the finite
sphere measure, Fubini, and translation invariance.
-/

open MeasureTheory Metric Set

noncomputable section

namespace LeanSpherical.HarmonicAnalysis

theorem norm_integral_sq_le_measureReal_mul_integral_norm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (g : α → ℂ) (hg : MemLp g 2 μ) :
    ‖∫ x, g x ∂μ‖ ^ 2 ≤ μ.real univ * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (f := g) (g := fun _ : α => (1 : ℂ))
    (p := 2) (q := 2) (by norm_num [Real.holderConjugate_iff])
    (by simpa using hg) (memLp_const (1 : ℂ))
  have hnorm : ‖∫ x, g x ∂μ‖ ≤ ∫ x, ‖g x‖ ∂μ :=
    norm_integral_le_integral_norm _
  have hholder_sqrt : ∫ x, ‖g x‖ ∂μ ≤
      √(∫ x, ‖g x‖ ^ 2 ∂μ) * √(μ.real univ) := by
    simpa [Real.sqrt_eq_rpow] using hholder
  have hnorm_nonneg : 0 ≤ ∫ x, ‖g x‖ ∂μ :=
    integral_nonneg fun _ => norm_nonneg _
  have hsq_nonneg : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have hmass_nonneg : 0 ≤ μ.real univ := measureReal_nonneg
  calc
    ‖∫ x, g x ∂μ‖ ^ 2 ≤ (∫ x, ‖g x‖ ∂μ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hnorm_nonneg).2 hnorm
    _ ≤ (√(∫ x, ‖g x‖ ^ 2 ∂μ) * √(μ.real univ)) ^ 2 :=
      (sq_le_sq₀ hnorm_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
        hholder_sqrt
    _ = μ.real univ * ∫ x, ‖g x‖ ^ 2 ∂μ := by
      rw [mul_pow, Real.sq_sqrt hsq_nonneg, Real.sq_sqrt hmass_nonneg]
      ring

private theorem integrable_norm_sq_sphere_translate_product
    {d : ℕ} (f : Euclidean d → ℂ) (hfcont : Continuous f)
    (hf2 : MemLp f 2 volume) (r : ℝ) :
    Integrable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        ‖f (p.1 + r • (p.2 : Euclidean d))‖ ^ 2)
      (volume.prod (unitSurfaceMeasure d)) := by
  have hf_sq : Integrable (fun x : Euclidean d => ‖f x‖ ^ 2) volume := by
    rw [← memLp_one_iff_integrable]
    simpa [Real.rpow_two] using hf2.norm_rpow (by norm_num) (by norm_num)
  have hmeas : AEStronglyMeasurable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        ‖f (p.1 + r • (p.2 : Euclidean d))‖ ^ 2)
      (volume.prod (unitSurfaceMeasure d)) := by
    apply (hfcont.norm.pow 2).comp
      (continuous_fst.add
        ((continuous_const :
          Continuous fun _ : Euclidean d × sphere (0 : Euclidean d) 1 => r).smul
          (continuous_subtype_val.comp continuous_snd))) |>.aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).2 ?_
  constructor
  · filter_upwards with ω
    exact hf_sq.comp_add_right (r • (ω : Euclidean d))
  · have h_eq : (fun ω : sphere (0 : Euclidean d) 1 =>
        ∫ x : Euclidean d, ‖‖f (x + r • (ω : Euclidean d))‖ ^ 2‖) =
        fun _ => ∫ x : Euclidean d, ‖f x‖ ^ 2 := by
      funext ω
      calc
        (∫ x : Euclidean d, ‖‖f (x + r • (ω : Euclidean d))‖ ^ 2‖) =
            ∫ x : Euclidean d, ‖f (x + r • (ω : Euclidean d))‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards with y
          rw [Real.norm_eq_abs]
          exact abs_of_nonneg (sq_nonneg (‖f (y + r • (ω : Euclidean d))‖))
        _ = ∫ x : Euclidean d, ‖f x‖ ^ 2 :=
          integral_add_right_eq_self (fun x : Euclidean d => ‖f x‖ ^ 2)
            (r • (ω : Euclidean d))
    change Integrable (fun ω : sphere (0 : Euclidean d) 1 =>
      ∫ x : Euclidean d, ‖‖f (x + r • (ω : Euclidean d))‖ ^ 2‖)
      (unitSurfaceMeasure d)
    rw [h_eq]
    exact integrable_const _

private theorem norm_sq_sphericalAverage_le_surfaceMass_mul_integral_norm_sq
    {d : ℕ} (f : Euclidean d → ℂ) (hfcont : Continuous f) (r : ℝ)
    (x : Euclidean d) :
    ‖sphericalAverage d f r x‖ ^ 2 ≤
      surfaceMass d * ∫ ω : sphere (0 : Euclidean d) 1,
        ‖f (x + r • (ω : Euclidean d))‖ ^ 2 ∂unitSurfaceMeasure d := by
  have hcont_x : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
      f (x + r • (ω : Euclidean d))) :=
    hfcont.comp (continuous_const.add
      ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => r).smul
        continuous_subtype_val))
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont_x.continuousOn
  have hmem : MemLp (fun ω : sphere (0 : Euclidean d) 1 =>
      f (x + r • (ω : Euclidean d))) 2 (unitSurfaceMeasure d) :=
    (memLp_top_of_bound hcont_x.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => hC ω (mem_univ _))).mono_exponent (by norm_num)
  simpa [sphericalAverage, surfaceMass] using
    norm_integral_sq_le_measureReal_mul_integral_norm_sq
      (unitSurfaceMeasure d)
      (fun ω : sphere (0 : Euclidean d) 1 => f (x + r • (ω : Euclidean d))) hmem

/-- The square of a fixed spherical average is integrable for a continuous
`L¹ ∩ L²` input. -/
theorem integrable_norm_sq_sphericalAverage
    {d : ℕ} (f : Euclidean d → ℂ) (hfcont : Continuous f)
    (hf : Integrable f volume) (hf2 : MemLp f 2 volume) (r : ℝ) :
    Integrable (fun x : Euclidean d => ‖sphericalAverage d f r x‖ ^ 2) volume := by
  have hprod := integrable_norm_sq_sphere_translate_product f hfcont hf2 r
  have hright : Integrable
      (fun x : Euclidean d => surfaceMass d * ∫ ω : sphere (0 : Euclidean d) 1,
        ‖f (x + r • (ω : Euclidean d))‖ ^ 2 ∂unitSurfaceMeasure d) volume :=
    hprod.integral_prod_left.const_mul _
  refine Integrable.mono hright
    ((integrable_sphericalAverage f hfcont hf r).aestronglyMeasurable.norm.pow 2) ?_
  filter_upwards with x
  have hmass_nonneg : 0 ≤ surfaceMass d := measureReal_nonneg
  rw [Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg
      (mul_nonneg hmass_nonneg (integral_nonneg fun _ => sq_nonneg _))]
  exact norm_sq_sphericalAverage_le_surfaceMass_mul_integral_norm_sq f hfcont r x

/-- A continuous `L¹ ∩ L²` input has a fixed spherical average in `L²`. -/
theorem memLp_sphericalAverage_two
    {d : ℕ} (f : Euclidean d → ℂ) (hfcont : Continuous f)
    (hf : Integrable f volume) (hf2 : MemLp f 2 volume) (r : ℝ) :
    MemLp (sphericalAverage d f r) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm
    (integrable_sphericalAverage f hfcont hf r).aestronglyMeasurable).2 ?_
  exact integrable_norm_sq_sphericalAverage f hfcont hf hf2 r

theorem integral_norm_sq_sphericalAverage_le_surfaceMass_sq_mul
    {d : ℕ} (f : Euclidean d → ℂ) (hfcont : Continuous f)
    (hf : Integrable f volume) (hf2 : MemLp f 2 volume) (r : ℝ) :
    (∫ x : Euclidean d, ‖sphericalAverage d f r x‖ ^ 2) ≤
      surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2 := by
  have hprod := integrable_norm_sq_sphere_translate_product f hfcont hf2 r
  have hpoint (x : Euclidean d) :
      ‖sphericalAverage d f r x‖ ^ 2 ≤
        surfaceMass d * ∫ ω : sphere (0 : Euclidean d) 1,
          ‖f (x + r • (ω : Euclidean d))‖ ^ 2 ∂unitSurfaceMeasure d :=
    norm_sq_sphericalAverage_le_surfaceMass_mul_integral_norm_sq f hfcont r x
  have hright : Integrable
      (fun x : Euclidean d => surfaceMass d * ∫ ω : sphere (0 : Euclidean d) 1,
        ‖f (x + r • (ω : Euclidean d))‖ ^ 2 ∂unitSurfaceMeasure d) volume :=
    hprod.integral_prod_left.const_mul _
  have havg_sq := integrable_norm_sq_sphericalAverage f hfcont hf hf2 r
  calc
    (∫ x : Euclidean d, ‖sphericalAverage d f r x‖ ^ 2) ≤
        ∫ x : Euclidean d, surfaceMass d * ∫ ω : sphere (0 : Euclidean d) 1,
          ‖f (x + r • (ω : Euclidean d))‖ ^ 2 ∂unitSurfaceMeasure d := by
      apply integral_mono_ae havg_sq hright
      filter_upwards with x
      exact hpoint x
    _ = surfaceMass d * ∫ x : Euclidean d, ∫ ω : sphere (0 : Euclidean d) 1,
          ‖f (x + r • (ω : Euclidean d))‖ ^ 2 ∂unitSurfaceMeasure d := by
      rw [integral_const_mul]
    _ = surfaceMass d *
          (∫ ω : sphere (0 : Euclidean d) 1,
            (∫ x : Euclidean d, ‖f (x + r • (ω : Euclidean d))‖ ^ 2 ∂volume)
            ∂unitSurfaceMeasure d) := by
      rw [integral_integral_swap hprod]
    _ = surfaceMass d *
        (surfaceMass d * ∫ x : Euclidean d, ‖f x‖ ^ 2) := by
      congr 1
      calc
        (∫ ω : sphere (0 : Euclidean d) 1,
            (∫ x : Euclidean d, ‖f (x + r • (ω : Euclidean d))‖ ^ 2 ∂volume)
            ∂unitSurfaceMeasure d) =
            ∫ _ : sphere (0 : Euclidean d) 1,
              (∫ x : Euclidean d, ‖f x‖ ^ 2 ∂volume) ∂unitSurfaceMeasure d := by
          apply integral_congr_ae
          filter_upwards with ω
          exact integral_add_right_eq_self (fun x : Euclidean d => ‖f x‖ ^ 2) _
        _ = surfaceMass d * ∫ x : Euclidean d, ‖f x‖ ^ 2 := by
          simp [surfaceMass]
    _ = surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2 := by ring

/-- After the concrete surface measure is normalized, every fixed spherical
average is an `L²` contraction at the square-integral level. -/
theorem integral_norm_sq_normalizedSphericalAverage_le
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) (hfcont : Continuous f)
    (hf : Integrable f volume) (hf2 : MemLp f 2 volume) (r : ℝ) :
    (∫ x : Euclidean d, ‖normalizedSphericalAverage d f r x‖ ^ 2) ≤
      ∫ x : Euclidean d, ‖f x‖ ^ 2 := by
  have hmass_nonneg : 0 ≤ surfaceMass d := measureReal_nonneg
  have hmass_ne : surfaceMass d ≠ 0 := surfaceMass_ne_zero hd
  have hmain :=
    integral_norm_sq_sphericalAverage_le_surfaceMass_sq_mul f hfcont hf hf2 r
  have hrewrite :
      (fun x : Euclidean d => ‖normalizedSphericalAverage d f r x‖ ^ 2) =
        fun x => (surfaceMass d)⁻¹ ^ 2 * ‖sphericalAverage d f r x‖ ^ 2 := by
    funext x
    rw [normalizedSphericalAverage, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hmass_nonneg]
    ring
  calc
    (∫ x : Euclidean d, ‖normalizedSphericalAverage d f r x‖ ^ 2) =
        (surfaceMass d)⁻¹ ^ 2 * ∫ x : Euclidean d, ‖sphericalAverage d f r x‖ ^ 2 := by
      rw [hrewrite, integral_const_mul]
    _ ≤ (surfaceMass d)⁻¹ ^ 2 *
        (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = ∫ x : Euclidean d, ‖f x‖ ^ 2 := by
      field_simp

theorem norm_toLp_two_eq_sqrt_integral_norm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℂ)
    (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ = √(∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hI : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  rw [Lp.norm_toLp, hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)]
  simp [Real.sqrt_eq_rpow]

theorem norm_sphericalAverage_toLp_le_surfaceMass_mul
    {d : ℕ} (f : Euclidean d → ℂ) (hfcont : Continuous f)
    (hf : Integrable f volume) (hf2 : MemLp f 2 volume) (r : ℝ) :
    ‖(memLp_sphericalAverage_two f hfcont hf hf2 r).toLp
      (sphericalAverage d f r)‖ ≤
      surfaceMass d * ‖hf2.toLp f‖ := by
  rw [norm_toLp_two_eq_sqrt_integral_norm_sq volume (sphericalAverage d f r)
      (memLp_sphericalAverage_two f hfcont hf hf2 r),
    norm_toLp_two_eq_sqrt_integral_norm_sq volume f hf2]
  have hmass_nonneg : 0 ≤ surfaceMass d := measureReal_nonneg
  calc
    √(∫ x : Euclidean d, ‖sphericalAverage d f r x‖ ^ 2) ≤
        √(surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2) :=
      Real.sqrt_le_sqrt
        (integral_norm_sq_sphericalAverage_le_surfaceMass_sq_mul f hfcont hf hf2 r)
    _ = surfaceMass d * √(∫ x : Euclidean d, ‖f x‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg (surfaceMass d)), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hmass_nonneg]

end LeanSpherical.HarmonicAnalysis
