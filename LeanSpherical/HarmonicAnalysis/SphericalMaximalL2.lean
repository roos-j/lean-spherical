/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceHeight
import LeanSpherical.HarmonicAnalysis.SurfaceCore
import LeanSpherical.HarmonicAnalysis.SphericalAverages
import LeanSpherical.HarmonicAnalysis.SmoothDyadicPhysicalCore
import LeanSpherical.HarmonicAnalysis.FourierRadius
import LeanSpherical.HarmonicAnalysis.RationalTails

/-!
# A compact-radius Sobolev maximal square estimate

The pointwise radius-Sobolev estimate, together with the concrete product
integrability of the radius derivative, gives a compact-radius
Sobolev-to-`L²` bound. It is not the derivative-free `L² → L²` estimate
needed in Stein's theorem.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory FourierTransform Metric Set
open scoped BigOperators BoundedContinuousFunction FourierTransform

noncomputable section

/-- The real-valued local-radius maximal output of a fixed smooth Fourier
multiplier.  This is the one operator used by the interpolation argument. -/
def smoothDyadicSphericalLocalMaximal
    {d : Nat} (psi f : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℝ :=
  fun x =>
    (⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal ‖sphericalAverage d
        ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ
          (psi : Euclidean d → ℂ) (𝓕 f)) :
            SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal

/-- The compact-radius spherical maximal square function has the displayed
lower-integral Sobolev bound. Its measurability for continuous inputs is
proved separately in `measurable_iSup_ennreal_norm_sq_sphericalAverage`. -/
theorem lintegral_iSup_ennreal_norm_sq_sphericalAverage_le_local_radiusSobolev
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hfderiv2 : MemLp (fderiv ℝ f) 2 volume) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ f y‖ ≤ C) {a b : ℝ} (hab : a ≤ b) :
    (∫⁻ x : Euclidean d,
      ⨆ r : Icc a b, ENNReal.ofReal (‖sphericalAverage d f r.1 x‖ ^ 2)) ≤
      ENNReal.ofReal
        (2 * (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2) +
          2 * (b - a) ^ 2 *
            (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2)) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let K : ℝ := surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2
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
  have hderiv_sq_prod_uncurried : Integrable
      (Function.uncurry (fun t (x : Euclidean d) =>
        ‖∫ ω : sphere (0 : Euclidean d) 1,
          fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
            ∂unitSurfaceMeasure d‖ ^ 2))
      (ν.prod volume) := by
    change Integrable (fun p : ℝ × Euclidean d =>
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ ^ 2) (ν.prod volume)
    exact hderiv_sq_prod
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
  have hderiv_interval_integrable : Integrable (fun x : Euclidean d =>
      ∫ t in a..b,
        ‖∫ ω : sphere (0 : Euclidean d) 1,
          fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
            ∂unitSurfaceMeasure d‖ ^ 2) volume := by
    have hprod_right : Integrable (fun x : Euclidean d =>
        ∫ t : ℝ,
          ‖∫ ω : sphere (0 : Euclidean d) 1,
            fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
              ∂unitSurfaceMeasure d‖ ^ 2 ∂ν) volume :=
      hderiv_sq_prod.integral_prod_right
    have heq : (fun x : Euclidean d => ∫ t in a..b,
        ‖∫ ω : sphere (0 : Euclidean d) 1,
          fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
            ∂unitSurfaceMeasure d‖ ^ 2) =
        fun x : Euclidean d => ∫ t : ℝ,
          ‖∫ ω : sphere (0 : Euclidean d) 1,
            fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
              ∂unitSurfaceMeasure d‖ ^ 2 ∂ν := by
      funext x
      simp only [ν]
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    rw [heq]
    exact hprod_right
  have hderiv_interval_swap :
      (∫ x : Euclidean d, ∫ t in a..b,
        ‖∫ ω : sphere (0 : Euclidean d) 1,
          fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
            ∂unitSurfaceMeasure d‖ ^ 2) =
        ∫ t in a..b, ∫ x : Euclidean d,
          ‖∫ ω : sphere (0 : Euclidean d) 1,
            fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
              ∂unitSurfaceMeasure d‖ ^ 2 := by
    calc
      (∫ x : Euclidean d, ∫ t in a..b,
        ‖∫ ω : sphere (0 : Euclidean d) 1,
          fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
            ∂unitSurfaceMeasure d‖ ^ 2) =
          ∫ x : Euclidean d, (∫ t : ℝ,
            ‖∫ ω : sphere (0 : Euclidean d) 1,
              fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
                ∂unitSurfaceMeasure d‖ ^ 2 ∂ν) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [ν]
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
      _ = ∫ t : ℝ, (∫ x : Euclidean d,
          ‖∫ ω : sphere (0 : Euclidean d) 1,
            fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
              ∂unitSurfaceMeasure d‖ ^ 2 ∂volume) ∂ν := by
        exact (integral_integral_swap
          (f := fun t (x : Euclidean d) =>
            ‖∫ ω : sphere (0 : Euclidean d) 1,
              fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
                ∂unitSurfaceMeasure d‖ ^ 2)
          hderiv_sq_prod_uncurried).symm
      _ = ∫ t in a..b, ∫ x : Euclidean d,
          ‖∫ ω : sphere (0 : Euclidean d) 1,
            fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
              ∂unitSurfaceMeasure d‖ ^ 2 := by
        simp only [ν]
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hfixed_integrable : Integrable (fun x : Euclidean d =>
      ‖sphericalAverage d f a x‖ ^ 2) volume :=
    integrable_norm_sq_sphericalAverage f hf.continuous hf1 hf2 a
  have hfixed : (∫ x : Euclidean d, ‖sphericalAverage d f a x‖ ^ 2) ≤
      surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2 :=
    integral_norm_sq_sphericalAverage_le_surfaceMass_sq_mul f hf.continuous hf1 hf2 a
  have hderiv_bound : (∫ x : Euclidean d, ∫ t in a..b,
      ‖∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d‖ ^ 2) ≤ (b - a) * K := by
    rw [hderiv_interval_swap]
    exact hderiv_interval
  have hmajorant_integrable : Integrable (fun x : Euclidean d =>
      2 * ‖sphericalAverage d f a x‖ ^ 2 +
        2 * (b - a) * (∫ t in a..b,
          ‖∫ ω : sphere (0 : Euclidean d) 1,
            fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
              ∂unitSurfaceMeasure d‖ ^ 2)) volume := by
    exact hfixed_integrable.const_mul (2 : ℝ) |>.add
      (hderiv_interval_integrable.const_mul (2 * (b - a)))
  have hmajorant_nonneg : ∀ x : Euclidean d,
      0 ≤ 2 * ‖sphericalAverage d f a x‖ ^ 2 +
        2 * (b - a) * (∫ t in a..b,
          ‖∫ ω : sphere (0 : Euclidean d) 1,
            fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
              ∂unitSurfaceMeasure d‖ ^ 2) := by
    intro x
    apply add_nonneg
    · positivity
    · exact mul_nonneg (mul_nonneg (by norm_num) hlength)
        (intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _)
  have hpoint (x : Euclidean d) :
      (⨆ r : Icc a b, ENNReal.ofReal (‖sphericalAverage d f r.1 x‖ ^ 2)) ≤
        ENNReal.ofReal
          (2 * ‖sphericalAverage d f a x‖ ^ 2 +
            2 * (b - a) * (∫ t in a..b,
              ‖∫ ω : sphere (0 : Euclidean d) 1,
                fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
                  ∂unitSurfaceMeasure d‖ ^ 2)) := by
    exact iSup_ennreal_norm_sq_le_radiusSobolev
      (a := a) (b := b)
      (f := fun t => sphericalAverage d f t x)
      (f' := fun t => ∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d)
      (hderiv_joint.comp
        (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)))
      (fun t => hasDerivAt_sphericalAverage f hf hC x t)
  have hmajorant_bound :
      (∫ x : Euclidean d,
        2 * ‖sphericalAverage d f a x‖ ^ 2 +
          2 * (b - a) * (∫ t in a..b,
            ‖∫ ω : sphere (0 : Euclidean d) 1,
              fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
                ∂unitSurfaceMeasure d‖ ^ 2)) ≤
        2 * (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2) +
          2 * (b - a) ^ 2 * K := by
    calc
      (∫ x : Euclidean d,
        2 * ‖sphericalAverage d f a x‖ ^ 2 +
          2 * (b - a) * (∫ t in a..b,
            ‖∫ ω : sphere (0 : Euclidean d) 1,
              fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
                ∂unitSurfaceMeasure d‖ ^ 2)) =
          2 * (∫ x : Euclidean d, ‖sphericalAverage d f a x‖ ^ 2) +
            2 * (b - a) * (∫ x : Euclidean d, ∫ t in a..b,
              ‖∫ ω : sphere (0 : Euclidean d) 1,
                fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
                  ∂unitSurfaceMeasure d‖ ^ 2) := by
        rw [MeasureTheory.integral_add
          (hfixed_integrable.const_mul (2 : ℝ))
          (hderiv_interval_integrable.const_mul (2 * (b - a))),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ ≤ 2 * (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2) +
            2 * (b - a) * ((b - a) * K) := by
        gcongr
      _ = 2 * (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2) +
            2 * (b - a) ^ 2 * K := by ring
  calc
    (∫⁻ x : Euclidean d,
      ⨆ r : Icc a b, ENNReal.ofReal (‖sphericalAverage d f r.1 x‖ ^ 2)) ≤
        ∫⁻ x : Euclidean d,
          ENNReal.ofReal
            (2 * ‖sphericalAverage d f a x‖ ^ 2 +
              2 * (b - a) * (∫ t in a..b,
                ‖∫ ω : sphere (0 : Euclidean d) 1,
                  fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
                    ∂unitSurfaceMeasure d‖ ^ 2)) := by
      exact lintegral_mono fun x => hpoint x
    _ = ENNReal.ofReal (∫ x : Euclidean d,
      2 * ‖sphericalAverage d f a x‖ ^ 2 +
        2 * (b - a) * (∫ t in a..b,
          ‖∫ ω : sphere (0 : Euclidean d) 1,
            fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
              ∂unitSurfaceMeasure d‖ ^ 2)) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hmajorant_integrable
        (Filter.Eventually.of_forall hmajorant_nonneg)
    _ ≤ ENNReal.ofReal
        (2 * (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖f x‖ ^ 2) +
          2 * (b - a) ^ 2 *
            (surfaceMass d ^ 2 * ∫ x : Euclidean d, ‖fderiv ℝ f x‖ ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [K] using hmajorant_bound

/-- The sharp surface-transform estimate gives the fixed-radius dyadic gain
on one absolute frequency annulus, uniformly for radii in `[1, 2]`. -/
theorem exists_norm_surfaceFourier_succ_smul_le_on_dyadicAnnulus
    {d : Nat} (hd : 2 ≤ d) (j : Nat) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ξ : Euclidean (d + 1)},
      ξ ∈ dyadicAnnulus (d + 1) j →
      ‖surfaceFourier (d + 1) (r • ξ)‖ ≤
        C / (dyadicScale j) ^ ((d : ℝ) / 2) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩ :=
    exists_sharp_surfaceFourier_succ_decay_and_deriv hd
  refine ⟨C₀, hC₀, ?_⟩
  intro ξ hξ
  have hscale : 0 < dyadicScale j := dyadicScale_pos j
  have hscale_one : 1 ≤ dyadicScale j := by
    calc
      1 = dyadicScale 0 := by simp [dyadicScale]
      _ ≤ dyadicScale j := dyadicScale_mono (Nat.zero_le j)
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
  have hnorm_smul : ‖r • ξ‖ = r * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
  have hscale_le : dyadicScale j ≤ ‖r • ξ‖ := by
    rw [hnorm_smul]
    calc
      dyadicScale j = 1 * dyadicScale j := by ring
      _ ≤ r * dyadicScale j :=
        mul_le_mul_of_nonneg_right hr.1 hscale.le
      _ ≤ r * ‖ξ‖ :=
        mul_le_mul_of_nonneg_left hξ.1 hrpos.le
  have harg_one : 1 ≤ ‖r • ξ‖ := hscale_one.trans hscale_le
  have hpow : (dyadicScale j) ^ ((d : ℝ) / 2) ≤
      ‖r • ξ‖ ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow hscale.le hscale_le (by positivity)
  have hpow_pos : 0 < (dyadicScale j) ^ ((d : ℝ) / 2) :=
    Real.rpow_pos_of_pos hscale _
  calc
    ‖surfaceFourier (d + 1) (r • ξ)‖ ≤
        C₀ / ‖r • ξ‖ ^ ((d : ℝ) / 2) :=
      hdecay (r • ξ) harg_one
    _ ≤ C₀ / (dyadicScale j) ^ ((d : ℝ) / 2) :=
      div_le_div_of_nonneg_left hC₀.le hpow_pos hpow

/-- The literal annular surface multiplier is bounded on `L²`, uniformly for
radii in `[1, 2]`.  The radius interval is essential: the same absolute
annulus cannot carry this estimate after taking a supremum over all radii. -/
theorem exists_norm_fourierInv_dyadic_surfaceMultiplier_succ_smul_le
    {d : Nat} (hd : 2 ≤ d) (j : Nat) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2)
    (f : Lp ℂ 2 (volume : Measure (Euclidean (d + 1)))) :
    ∃ C : ℝ, 0 < C ∧
      ∃ hm : AEStronglyMeasurable
          ((dyadicAnnulus (d + 1) j).indicator
            (fun ξ => surfaceFourier (d + 1) (r • ξ))) volume,
        ∃ hbound : ∀ ξ,
            ‖((dyadicAnnulus (d + 1) j).indicator
              (fun η => surfaceFourier (d + 1) (r • η))) ξ‖ ≤
              C / (dyadicScale j) ^ ((d : ℝ) / 2),
          ‖𝓕⁻ (((memLp_top_of_bound hm
            (C / (dyadicScale j) ^ ((d : ℝ) / 2))
            (Filter.Eventually.of_forall hbound)).toLp
              ((dyadicAnnulus (d + 1) j).indicator
                (fun ξ => surfaceFourier (d + 1) (r • ξ))) :
                Lp ℂ ⊤ (volume : Measure (Euclidean (d + 1)))) •
              (𝓕 f) : Lp ℂ 2 (volume : Measure (Euclidean (d + 1))))‖ ≤
            (C / (dyadicScale j) ^ ((d : ℝ) / 2)) * ‖f‖ := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_surfaceFourier_succ_smul_le_on_dyadicAnnulus hd j r hr
  have hS : MeasurableSet (dyadicAnnulus (d + 1) j) := by
    dsimp [dyadicAnnulus]
    exact (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have hm : AEStronglyMeasurable
      ((dyadicAnnulus (d + 1) j).indicator
        (fun ξ => surfaceFourier (d + 1) (r • ξ))) volume := by
    exact (Measurable.indicator
      (((continuous_surfaceFourier (d + 1)).comp
        ((continuous_const : Continuous fun _ : Euclidean (d + 1) => r).smul
          continuous_id)).measurable) hS).aestronglyMeasurable
  have hpow_nonneg : 0 ≤ (dyadicScale j) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg (dyadicScale_pos j).le _
  have hbound : ∀ ξ : Euclidean (d + 1),
      ‖((dyadicAnnulus (d + 1) j).indicator
        (fun η => surfaceFourier (d + 1) (r • η))) ξ‖ ≤
        C / (dyadicScale j) ^ ((d : ℝ) / 2) := by
    intro ξ
    by_cases hξ : ξ ∈ dyadicAnnulus (d + 1) j
    · rw [Set.indicator_of_mem hξ]
      exact hpoint hξ
    · rw [Set.indicator_of_notMem hξ]
      simpa only [norm_zero] using div_nonneg hC.le hpow_nonneg
  refine ⟨C, hC, hm, hbound, ?_⟩
  exact norm_fourierInv_bounded_multiplier_fourier_le
    ((dyadicAnnulus (d + 1) j).indicator
      (fun ξ => surfaceFourier (d + 1) (r • ξ))) hm
    (C / (dyadicScale j) ^ ((d : ℝ) / 2))
    (div_nonneg hC.le hpow_nonneg) hbound f

/-- The sharp radial derivative estimate gives the expected dyadic gain on
one absolute frequency annulus, uniformly for radii in `[1, 2]`.  This is
the local estimate that is valid before the separate relative-frequency
rescaling needed for the global-radius maximal operator. -/
theorem exists_norm_deriv_surfaceFourier_succ_smul_le_on_dyadicAnnulus
    {d : Nat} (hd : 2 ≤ d) (j : Nat) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ξ : Euclidean (d + 1)},
      ξ ∈ dyadicAnnulus (d + 1) j →
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r‖ ≤
        C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩ :=
    exists_sharp_surfaceFourier_succ_decay_and_deriv hd
  refine ⟨C₁, hC₁, ?_⟩
  intro ξ hξ
  have ha : 0 ≤ (d : ℝ) / 2 - 1 := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hscale : 0 < dyadicScale j := dyadicScale_pos j
  have hscale_one : 1 ≤ dyadicScale j := by
    calc
      1 = dyadicScale 0 := by simp [dyadicScale]
      _ ≤ dyadicScale j := dyadicScale_mono (Nat.zero_le j)
  have hxi_one : 1 ≤ ‖ξ‖ := hscale_one.trans hξ.1
  have hpow : (dyadicScale j) ^ ((d : ℝ) / 2 - 1) ≤
      ‖ξ‖ ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_le_rpow hscale.le hξ.1 ha
  have hpow_pos : 0 < (dyadicScale j) ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_pos_of_pos hscale _
  calc
    ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r‖ ≤
        C₁ / ‖ξ‖ ^ ((d : ℝ) / 2 - 1) :=
      hderiv ξ r hxi_one hr
    _ ≤ C₁ / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) :=
      div_le_div_of_nonneg_left hC₁.le hpow_pos hpow

/-- The literal radial-derivative multiplier on one dyadic annulus is bounded
on `L²` at the Sobolev rate `2^{-j (d - 2) / 2}`.  As above, the statement
is deliberately localized to radii in `[1, 2]`. -/
theorem exists_norm_fourierInv_dyadic_surfaceDerivativeMultiplier_succ_smul_le
    {d : Nat} (hd : 2 ≤ d) (j : Nat) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2)
    (f : Lp ℂ 2 (volume : Measure (Euclidean (d + 1)))) :
    ∃ C : ℝ, 0 < C ∧
      ∃ hm : AEStronglyMeasurable
          ((dyadicAnnulus (d + 1) j).indicator
            (fun ξ => deriv (fun s : ℝ =>
              surfaceFourier (d + 1) (s • ξ)) r)) volume,
        ∃ hbound : ∀ ξ,
            ‖((dyadicAnnulus (d + 1) j).indicator
              (fun η => deriv (fun s : ℝ =>
                surfaceFourier (d + 1) (s • η)) r)) ξ‖ ≤
              C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1),
          ‖𝓕⁻ (((memLp_top_of_bound hm
            (C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1))
            (Filter.Eventually.of_forall hbound)).toLp
              ((dyadicAnnulus (d + 1) j).indicator
                (fun ξ => deriv (fun s : ℝ =>
                  surfaceFourier (d + 1) (s • ξ)) r)) :
                Lp ℂ ⊤ (volume : Measure (Euclidean (d + 1)))) •
              (𝓕 f) : Lp ℂ 2 (volume : Measure (Euclidean (d + 1))))‖ ≤
            (C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)) * ‖f‖ := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_deriv_surfaceFourier_succ_smul_le_on_dyadicAnnulus hd j r hr
  have hS : MeasurableSet (dyadicAnnulus (d + 1) j) := by
    dsimp [dyadicAnnulus]
    exact (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have hm : AEStronglyMeasurable
      ((dyadicAnnulus (d + 1) j).indicator
        (fun ξ => deriv (fun s : ℝ =>
          surfaceFourier (d + 1) (s • ξ)) r)) volume := by
    let g : Euclidean (d + 1) → ℂ := fun ξ =>
      ∫ ω : Metric.sphere (0 : Euclidean (d + 1)) 1,
        Complex.exp (surfacePhase (d + 1) (r • ξ) ω) *
          surfacePhase (d + 1) ξ ω ∂unitSurfaceMeasure (d + 1)
    have hcont : Continuous g := by
      have hjoint : Continuous (Function.uncurry
          (fun (ξ : Euclidean (d + 1))
              (ω : Metric.sphere (0 : Euclidean (d + 1)) 1) =>
            Complex.exp (surfacePhase (d + 1) (r • ξ) ω) *
              surfacePhase (d + 1) ξ ω)) := by
        unfold surfacePhase
        fun_prop
      simpa only [Measure.restrict_univ] using
        (continuous_parametric_integral_of_continuous
          (μ := unitSurfaceMeasure (d + 1)) hjoint isCompact_univ)
    have hEq : (fun ξ : Euclidean (d + 1) =>
        deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r) = g := by
      funext ξ
      simpa [g] using (hasDerivAt_surfaceFourier_radial_at (d + 1) ξ r).deriv
    rw [hEq]
    exact hcont.aestronglyMeasurable.indicator hS
  have hpow_nonneg : 0 ≤ (dyadicScale j) ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_nonneg (dyadicScale_pos j).le _
  have hbound : ∀ ξ : Euclidean (d + 1),
      ‖((dyadicAnnulus (d + 1) j).indicator
        (fun η => deriv (fun s : ℝ =>
          surfaceFourier (d + 1) (s • η)) r)) ξ‖ ≤
        C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := by
    intro ξ
    by_cases hξ : ξ ∈ dyadicAnnulus (d + 1) j
    · rw [Set.indicator_of_mem hξ]
      exact hpoint hξ
    · rw [Set.indicator_of_notMem hξ]
      simpa only [norm_zero] using div_nonneg hC.le hpow_nonneg
  refine ⟨C, hC, hm, hbound, ?_⟩
  exact norm_fourierInv_bounded_multiplier_fourier_le
    ((dyadicAnnulus (d + 1) j).indicator
      (fun ξ => deriv (fun s : ℝ =>
        surfaceFourier (d + 1) (s • ξ)) r)) hm
    (C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1))
    (div_nonneg hC.le hpow_nonneg) hbound f

/-- A smooth dyadic bandpass retains the sharp fixed-radius surface-transform
decay.  This is the frequency localization used in the global argument,
where the cutoff is later applied to `r • ξ` rather than to an absolute
frequency variable. -/
theorem exists_norm_surfaceFourier_succ_smul_mul_smooth_dyadic_bandpass_le
    {d : Nat} (hd : 2 ≤ d) {phi : SchwartzMap (Euclidean (d + 1)) ℂ}
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0)
    (hphi_norm : ∀ ξ, ‖phi ξ‖ ≤ 1)
    (j : Nat) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Euclidean (d + 1),
      ‖surfaceFourier (d + 1) (r • ξ) *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          phi (((2 : ℝ) ^ j)⁻¹ • ξ))‖ ≤
        C / (dyadicScale j) ^ ((d : ℝ) / 2) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩ :=
    exists_sharp_surfaceFourier_succ_decay_and_deriv hd
  refine ⟨2 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro ξ
  let q : ℂ := phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
    phi (((2 : ℝ) ^ j)⁻¹ • ξ)
  have hscale : 0 < dyadicScale j := dyadicScale_pos j
  have hscale_one : 1 ≤ dyadicScale j := by
    calc
      1 = dyadicScale 0 := by simp [dyadicScale]
      _ ≤ dyadicScale j := dyadicScale_mono (Nat.zero_le j)
  have hden_nonneg : 0 ≤ (dyadicScale j) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg hscale.le _
  by_cases hq : q = 0
  · change ‖surfaceFourier (d + 1) (r • ξ) * q‖ ≤
        (2 * C₀) / (dyadicScale j) ^ ((d : ℝ) / 2)
    rw [hq, mul_zero, norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hC₀.le) hden_nonneg
  have hq' : phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
      phi (((2 : ℝ) ^ j)⁻¹ • ξ) ≠ 0 := by
    simpa only [q] using hq
  have hsupport' :=
    smooth_dyadic_bandpass_norm_bounds_of_ne_zero hphi_one hphi_zero hq'
  have hsupport : dyadicScale j < ‖ξ‖ := by
    simpa only [dyadicScale] using hsupport'.1
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
  have hnorm_smul : ‖r • ξ‖ = r * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
  have hscale_le : dyadicScale j ≤ ‖r • ξ‖ := by
    rw [hnorm_smul]
    calc
      dyadicScale j = 1 * dyadicScale j := by ring
      _ ≤ r * dyadicScale j :=
        mul_le_mul_of_nonneg_right hr.1 hscale.le
      _ ≤ r * ‖ξ‖ :=
        mul_le_mul_of_nonneg_left hsupport.le hrpos.le
  have harg_one : 1 ≤ ‖r • ξ‖ := hscale_one.trans hscale_le
  have hpow : (dyadicScale j) ^ ((d : ℝ) / 2) ≤
      ‖r • ξ‖ ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow hscale.le hscale_le (by positivity)
  have hpow_pos : 0 < (dyadicScale j) ^ ((d : ℝ) / 2) :=
    Real.rpow_pos_of_pos hscale _
  have hsurf : ‖surfaceFourier (d + 1) (r • ξ)‖ ≤
      C₀ / (dyadicScale j) ^ ((d : ℝ) / 2) := by
    calc
      ‖surfaceFourier (d + 1) (r • ξ)‖ ≤
          C₀ / ‖r • ξ‖ ^ ((d : ℝ) / 2) :=
        hdecay (r • ξ) harg_one
      _ ≤ C₀ / (dyadicScale j) ^ ((d : ℝ) / 2) :=
        div_le_div_of_nonneg_left hC₀.le hpow_pos hpow
  have hqnorm : ‖q‖ ≤ 2 := by
    dsimp only [q]
    exact norm_smooth_dyadic_bandpass_le_two hphi_norm j ξ
  change ‖surfaceFourier (d + 1) (r • ξ) * q‖ ≤
    (2 * C₀) / (dyadicScale j) ^ ((d : ℝ) / 2)
  rw [norm_mul]
  calc
    ‖surfaceFourier (d + 1) (r • ξ)‖ * ‖q‖ ≤
        (C₀ / (dyadicScale j) ^ ((d : ℝ) / 2)) * 2 :=
      mul_le_mul hsurf hqnorm (norm_nonneg _) (div_nonneg hC₀.le hden_nonneg)
    _ = (2 * C₀) / (dyadicScale j) ^ ((d : ℝ) / 2) := by ring

/-- The radial derivative obeys the corresponding smooth-dyadic bound.  Its
power is exactly the compact-radius Sobolev exponent. -/
theorem exists_norm_deriv_surfaceFourier_succ_smul_mul_smooth_dyadic_bandpass_le
    {d : Nat} (hd : 2 ≤ d) {phi : SchwartzMap (Euclidean (d + 1)) ℂ}
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0)
    (hphi_norm : ∀ ξ, ‖phi ξ‖ ≤ 1)
    (j : Nat) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Euclidean (d + 1),
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          phi (((2 : ℝ) ^ j)⁻¹ • ξ))‖ ≤
        C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hdecay, hderiv⟩ :=
    exists_sharp_surfaceFourier_succ_decay_and_deriv hd
  refine ⟨2 * C₁, mul_pos (by norm_num) hC₁, ?_⟩
  intro ξ
  let q : ℂ := phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
    phi (((2 : ℝ) ^ j)⁻¹ • ξ)
  have ha : 0 ≤ (d : ℝ) / 2 - 1 := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hscale : 0 < dyadicScale j := dyadicScale_pos j
  have hscale_one : 1 ≤ dyadicScale j := by
    calc
      1 = dyadicScale 0 := by simp [dyadicScale]
      _ ≤ dyadicScale j := dyadicScale_mono (Nat.zero_le j)
  have hden_nonneg : 0 ≤ (dyadicScale j) ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_nonneg hscale.le _
  by_cases hq : q = 0
  · change ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r * q‖ ≤
        (2 * C₁) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)
    rw [hq, mul_zero, norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hC₁.le) hden_nonneg
  have hq' : phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
      phi (((2 : ℝ) ^ j)⁻¹ • ξ) ≠ 0 := by
    simpa only [q] using hq
  have hsupport' :=
    smooth_dyadic_bandpass_norm_bounds_of_ne_zero hphi_one hphi_zero hq'
  have hsupport : dyadicScale j < ‖ξ‖ := by
    simpa only [dyadicScale] using hsupport'.1
  have hxi_one : 1 ≤ ‖ξ‖ := hscale_one.trans hsupport.le
  have hpow : (dyadicScale j) ^ ((d : ℝ) / 2 - 1) ≤
      ‖ξ‖ ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_le_rpow hscale.le hsupport.le ha
  have hpow_pos : 0 < (dyadicScale j) ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_pos_of_pos hscale _
  have hderiv_bound :
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r‖ ≤
        C₁ / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := by
    calc
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r‖ ≤
          C₁ / ‖ξ‖ ^ ((d : ℝ) / 2 - 1) :=
        hderiv ξ r hxi_one hr
      _ ≤ C₁ / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) :=
        div_le_div_of_nonneg_left hC₁.le hpow_pos hpow
  have hqnorm : ‖q‖ ≤ 2 := by
    dsimp only [q]
    exact norm_smooth_dyadic_bandpass_le_two hphi_norm j ξ
  change ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r * q‖ ≤
    (2 * C₁) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)
  rw [norm_mul]
  calc
    ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r‖ * ‖q‖ ≤
        (C₁ / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)) * 2 :=
      mul_le_mul hderiv_bound hqnorm (norm_nonneg _)
        (div_nonneg hC₁.le hden_nonneg)
    _ = (2 * C₁) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := by ring

/-- The smooth surface-multiplier estimate with its decay constant kept
explicit.  This is the form used uniformly in the dyadic index. -/
theorem norm_surfaceFourier_succ_smul_mul_smooth_dyadic_bandpass_le_of_sharp
    {d : Nat} (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hdecay : ∀ ξ : Euclidean (d + 1), 1 ≤ ‖ξ‖ →
      ‖surfaceFourier (d + 1) ξ‖ ≤ C₀ / ‖ξ‖ ^ ((d : ℝ) / 2))
    {phi : SchwartzMap (Euclidean (d + 1)) ℂ}
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0)
    (hphi_norm : ∀ ξ, ‖phi ξ‖ ≤ 1)
    (j : Nat) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (xi : Euclidean (d + 1)) :
    ‖surfaceFourier (d + 1) (r • xi) *
      (phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) -
        phi (((2 : ℝ) ^ j)⁻¹ • xi))‖ ≤
      (2 * C₀) / (dyadicScale j) ^ ((d : ℝ) / 2) := by
  let q : ℂ := phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) -
    phi (((2 : ℝ) ^ j)⁻¹ • xi)
  have hscale : 0 < dyadicScale j := dyadicScale_pos j
  have hscale_one : 1 ≤ dyadicScale j := by
    calc
      1 = dyadicScale 0 := by simp [dyadicScale]
      _ ≤ dyadicScale j := dyadicScale_mono (Nat.zero_le j)
  have hden_nonneg : 0 ≤ (dyadicScale j) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg hscale.le _
  by_cases hq : q = 0
  · change ‖surfaceFourier (d + 1) (r • xi) * q‖ ≤
        (2 * C₀) / (dyadicScale j) ^ ((d : ℝ) / 2)
    rw [hq, mul_zero, norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hC₀.le) hden_nonneg
  have hq' : phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) -
      phi (((2 : ℝ) ^ j)⁻¹ • xi) ≠ 0 := by
    simpa only [q] using hq
  have hsupport' :=
    smooth_dyadic_bandpass_norm_bounds_of_ne_zero hphi_one hphi_zero hq'
  have hsupport : dyadicScale j < ‖xi‖ := by
    simpa only [dyadicScale] using hsupport'.1
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
  have hnorm_smul : ‖r • xi‖ = r * ‖xi‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
  have hscale_le : dyadicScale j ≤ ‖r • xi‖ := by
    rw [hnorm_smul]
    calc
      dyadicScale j = 1 * dyadicScale j := by ring
      _ ≤ r * dyadicScale j :=
        mul_le_mul_of_nonneg_right hr.1 hscale.le
      _ ≤ r * ‖xi‖ :=
        mul_le_mul_of_nonneg_left hsupport.le hrpos.le
  have harg_one : 1 ≤ ‖r • xi‖ := hscale_one.trans hscale_le
  have hpow : (dyadicScale j) ^ ((d : ℝ) / 2) ≤
      ‖r • xi‖ ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow hscale.le hscale_le (by positivity)
  have hpow_pos : 0 < (dyadicScale j) ^ ((d : ℝ) / 2) :=
    Real.rpow_pos_of_pos hscale _
  have hsurf : ‖surfaceFourier (d + 1) (r • xi)‖ ≤
      C₀ / (dyadicScale j) ^ ((d : ℝ) / 2) := by
    calc
      ‖surfaceFourier (d + 1) (r • xi)‖ ≤
          C₀ / ‖r • xi‖ ^ ((d : ℝ) / 2) := hdecay _ harg_one
      _ ≤ C₀ / (dyadicScale j) ^ ((d : ℝ) / 2) :=
        div_le_div_of_nonneg_left hC₀.le hpow_pos hpow
  have hqnorm : ‖q‖ ≤ 2 := by
    dsimp only [q]
    exact norm_smooth_dyadic_bandpass_le_two hphi_norm j xi
  change ‖surfaceFourier (d + 1) (r • xi) * q‖ ≤
    (2 * C₀) / (dyadicScale j) ^ ((d : ℝ) / 2)
  rw [norm_mul]
  calc
    ‖surfaceFourier (d + 1) (r • xi)‖ * ‖q‖ ≤
        (C₀ / (dyadicScale j) ^ ((d : ℝ) / 2)) * 2 :=
      mul_le_mul hsurf hqnorm (norm_nonneg _)
        (div_nonneg hC₀.le hden_nonneg)
    _ = (2 * C₀) / (dyadicScale j) ^ ((d : ℝ) / 2) := by ring

/-- The explicit-constant derivative counterpart of the preceding lemma. -/
theorem norm_deriv_surfaceFourier_succ_smul_mul_smooth_dyadic_bandpass_le_of_sharp
    {d : Nat} (hd : 2 ≤ d) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hderiv : ∀ ξ : Euclidean (d + 1), ∀ r : ℝ, 1 ≤ ‖ξ‖ →
      r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r‖ ≤
        C₁ / ‖ξ‖ ^ ((d : ℝ) / 2 - 1))
    {phi : SchwartzMap (Euclidean (d + 1)) ℂ}
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0)
    (hphi_norm : ∀ ξ, ‖phi ξ‖ ≤ 1)
    (j : Nat) (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (xi : Euclidean (d + 1)) :
    ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • xi)) r *
      (phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) -
        phi (((2 : ℝ) ^ j)⁻¹ • xi))‖ ≤
      (2 * C₁) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := by
  let q : ℂ := phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) -
    phi (((2 : ℝ) ^ j)⁻¹ • xi)
  have ha : 0 ≤ (d : ℝ) / 2 - 1 := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hscale : 0 < dyadicScale j := dyadicScale_pos j
  have hscale_one : 1 ≤ dyadicScale j := by
    calc
      1 = dyadicScale 0 := by simp [dyadicScale]
      _ ≤ dyadicScale j := dyadicScale_mono (Nat.zero_le j)
  have hden_nonneg : 0 ≤ (dyadicScale j) ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_nonneg hscale.le _
  by_cases hq : q = 0
  · change ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • xi)) r * q‖ ≤
        (2 * C₁) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)
    rw [hq, mul_zero, norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hC₁.le) hden_nonneg
  have hq' : phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) -
      phi (((2 : ℝ) ^ j)⁻¹ • xi) ≠ 0 := by
    simpa only [q] using hq
  have hsupport' :=
    smooth_dyadic_bandpass_norm_bounds_of_ne_zero hphi_one hphi_zero hq'
  have hsupport : dyadicScale j < ‖xi‖ := by
    simpa only [dyadicScale] using hsupport'.1
  have hxi_one : 1 ≤ ‖xi‖ := hscale_one.trans hsupport.le
  have hpow : (dyadicScale j) ^ ((d : ℝ) / 2 - 1) ≤
      ‖xi‖ ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_le_rpow hscale.le hsupport.le ha
  have hpow_pos : 0 < (dyadicScale j) ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_pos_of_pos hscale _
  have hderiv_bound :
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • xi)) r‖ ≤
        C₁ / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := by
    calc
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • xi)) r‖ ≤
          C₁ / ‖xi‖ ^ ((d : ℝ) / 2 - 1) := hderiv xi r hxi_one hr
      _ ≤ C₁ / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) :=
        div_le_div_of_nonneg_left hC₁.le hpow_pos hpow
  have hqnorm : ‖q‖ ≤ 2 := by
    dsimp only [q]
    exact norm_smooth_dyadic_bandpass_le_two hphi_norm j xi
  change ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • xi)) r * q‖ ≤
    (2 * C₁) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)
  rw [norm_mul]
  calc
    ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • xi)) r‖ * ‖q‖ ≤
        (C₁ / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)) * 2 :=
      mul_le_mul hderiv_bound hqnorm (norm_nonneg _)
        (div_nonneg hC₁.le hden_nonneg)
    _ = (2 * C₁) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := by ring

/-- Plancherel converts the preceding smooth-dyadic surface multiplier bound
into a literal physical-space `L²` estimate. -/
theorem exists_integral_norm_sq_sphericalAverage_fourierInv_smooth_dyadic_bandpass_succ_le
    {d : Nat} (hd : 2 ≤ d) (phi f psi : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0)
    (hphi_norm : ∀ ξ, ‖phi ξ‖ ≤ 1)
    (j : Nat)
    (hpsi : ∀ ξ : Euclidean (d + 1),
      psi ξ = phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        phi (((2 : ℝ) ^ j)⁻¹ • ξ))
    (hpsi_compact : HasCompactSupport (psi : Euclidean (d + 1) → ℂ))
    (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧
      (∫ x : Euclidean (d + 1),
        ‖sphericalAverage (d + 1)
          ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ
            (psi : Euclidean (d + 1) → ℂ) (𝓕 f)) :
              SchwartzMap (Euclidean (d + 1)) ℂ) : Euclidean (d + 1) → ℂ) r x‖ ^ 2) ≤
        (C / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 *
          ∫ ξ : Euclidean (d + 1), ‖𝓕 (f : Euclidean (d + 1) → ℂ) ξ‖ ^ 2 := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_surfaceFourier_succ_smul_mul_smooth_dyadic_bandpass_le
      hd hphi_one hphi_zero hphi_norm j r hr
  let h : SchwartzMap (Euclidean (d + 1)) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (psi : Euclidean (d + 1) → ℂ) (𝓕 f)
  rcases exists_schwartz_compactSupport_mul_surfaceFourier psi hpsi_compact r with
    ⟨m, hm⟩
  have hCnonneg : 0 ≤ C / (dyadicScale j) ^ ((d : ℝ) / 2) := by
    exact div_nonneg hC.le (Real.rpow_nonneg (dyadicScale_pos j).le _)
  have hmbound (ξ : Euclidean (d + 1)) : ‖m ξ‖ ≤
      C / (dyadicScale j) ^ ((d : ℝ) / 2) := by
    rw [hm ξ]
    have hneg : surfaceFourier (d + 1) (-r • ξ) =
        surfaceFourier (d + 1) (r • ξ) := by
      simpa only [neg_smul] using surfaceFourier_neg (d + 1) (r • ξ)
    calc
      ‖psi ξ * surfaceFourier (d + 1) (-r • ξ)‖ =
          ‖surfaceFourier (d + 1) (r • ξ) * psi ξ‖ := by
        rw [hneg, mul_comm]
      _ = ‖surfaceFourier (d + 1) (r • ξ) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
            phi (((2 : ℝ) ^ j)⁻¹ • ξ))‖ := by rw [hpsi ξ]
      _ ≤ C / (dyadicScale j) ^ ((d : ℝ) / 2) := hpoint ξ
  have hmult := integral_norm_sq_fourierInv_schwartz_multiplier_le
    m (𝓕 f) hCnonneg hmbound
  have hsymbol : (fun ξ : Euclidean (d + 1) =>
      surfaceFourier (d + 1) (-r • ξ) * h ξ) =
      fun ξ => m ξ * 𝓕 (f : Euclidean (d + 1) → ℂ) ξ := by
    funext ξ
    rw [hm ξ]
    simp only [h, SchwartzMap.smulLeftCLM_apply psi.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul]
    ring
  refine ⟨C, hC, ?_⟩
  rw [sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier h r, hsymbol]
  exact hmult

/-- The same Plancherel step for the literal radial derivative multiplier. -/
theorem exists_integral_norm_sq_fourierInv_smooth_dyadic_surfaceDerivativeMultiplier_succ_le
    {d : Nat} (hd : 2 ≤ d) (phi f psi : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0)
    (hphi_norm : ∀ ξ, ‖phi ξ‖ ≤ 1)
    (j : Nat)
    (hpsi : ∀ ξ : Euclidean (d + 1),
      psi ξ = phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        phi (((2 : ℝ) ^ j)⁻¹ • ξ))
    (hpsi_compact : HasCompactSupport (psi : Euclidean (d + 1) → ℂ))
    (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧
      (∫ x : Euclidean (d + 1), ‖𝓕⁻ (fun ξ : Euclidean (d + 1) =>
        deriv (fun s : ℝ => surfaceFourier (d + 1) (s • (-ξ))) r *
          (psi ξ * 𝓕 (f : Euclidean (d + 1) → ℂ) ξ)) x‖ ^ 2) ≤
        (C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)) ^ 2 *
          ∫ ξ : Euclidean (d + 1), ‖𝓕 (f : Euclidean (d + 1) → ℂ) ξ‖ ^ 2 := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_deriv_surfaceFourier_succ_smul_mul_smooth_dyadic_bandpass_le
      hd hphi_one hphi_zero hphi_norm j r hr
  rcases exists_schwartz_compactSupport_mul_surfaceFourier_radius_deriv
      psi hpsi_compact r with ⟨m, hm⟩
  have hCnonneg : 0 ≤ C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := by
    exact div_nonneg hC.le (Real.rpow_nonneg (dyadicScale_pos j).le _)
  have hmbound (ξ : Euclidean (d + 1)) : ‖m ξ‖ ≤
      C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := by
    rw [hm ξ]
    have hfun : (fun s : ℝ => surfaceFourier (d + 1) (s • (-ξ))) =
        fun s : ℝ => surfaceFourier (d + 1) (s • ξ) := by
      funext s
      simpa only [smul_neg] using surfaceFourier_neg (d + 1) (s • ξ)
    rw [hfun]
    calc
      ‖psi ξ * deriv (fun s : ℝ =>
          surfaceFourier (d + 1) (s • ξ)) r‖ =
          ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r *
            psi ξ‖ := by rw [mul_comm]
      _ = ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
            phi (((2 : ℝ) ^ j)⁻¹ • ξ))‖ := by rw [hpsi ξ]
      _ ≤ C / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) := hpoint ξ
  have hmult := integral_norm_sq_fourierInv_schwartz_multiplier_le
    m (𝓕 f) hCnonneg hmbound
  have hsymbol : (fun ξ : Euclidean (d + 1) =>
      deriv (fun s : ℝ => surfaceFourier (d + 1) (s • (-ξ))) r *
        (psi ξ * 𝓕 (f : Euclidean (d + 1) → ℂ) ξ)) =
      fun ξ => m ξ * 𝓕 (f : Euclidean (d + 1) → ℂ) ξ := by
    funext ξ
    rw [hm ξ]
    ring
  refine ⟨C, hC, ?_⟩
  rw [hsymbol]
  exact hmult

/-- The literal smooth dyadic spherical maximal piece has the compact-radius
`L²` bound supplied by sharp surface-transform decay and one-dimensional
Sobolev in the radius.  The radius set is explicitly `[1,2]`; global radii
require the separate relative-frequency dilation argument. -/
theorem exists_smooth_dyadic_sphericalMaximal_succ_memLp_two_of_sharp
    {d : Nat} (hd : 2 ≤ d) (C0 C1 : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ ξ : Euclidean (d + 1), 1 ≤ ‖ξ‖ →
      ‖surfaceFourier (d + 1) ξ‖ ≤ C0 / ‖ξ‖ ^ ((d : ℝ) / 2))
    (hderiv : ∀ ξ : Euclidean (d + 1), ∀ r : ℝ, 1 ≤ ‖ξ‖ →
      r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r‖ ≤
        C1 / ‖ξ‖ ^ ((d : ℝ) / 2 - 1))
    (phi f : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0)
    (hphi_norm : ∀ ξ, ‖phi ξ‖ ≤ 1) (j : Nat) :
    ∃ psi : SchwartzMap (Euclidean (d + 1)) ℂ,
      (∀ ξ : Euclidean (d + 1),
        psi ξ = phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          phi (((2 : ℝ) ^ j)⁻¹ • ξ)) ∧
      MemLp
        (fun x : Euclidean (d + 1) =>
          (⨆ r : Icc (1 : ℝ) 2,
            ENNReal.ofReal ‖sphericalAverage (d + 1)
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ
                (psi : Euclidean (d + 1) → ℂ) (𝓕 f)) :
                  SchwartzMap (Euclidean (d + 1)) ℂ) : Euclidean (d + 1) → ℂ)
                    r.1 x‖).toReal)
        2 volume ∧
      (∫ x : Euclidean (d + 1),
        ‖(⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal ‖sphericalAverage (d + 1)
            ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ
              (psi : Euclidean (d + 1) → ℂ) (𝓕 f)) :
                SchwartzMap (Euclidean (d + 1)) ℂ) : Euclidean (d + 1) → ℂ)
                  r.1 x‖).toReal‖ ^ 2) ≤
        (2 * ((2 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
          2 * ((2 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)) ^ 2) *
          ∫ x : Euclidean (d + 1), ‖f x‖ ^ 2 := by
  rcases exists_compactlySupported_schwartzMap_smooth_dyadic_bandpass
      phi hphi_one hphi_zero j with ⟨psi, hpsi, hpsi_compact, hpsi_zero⟩
  let h : SchwartzMap (Euclidean (d + 1)) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (psi : Euclidean (d + 1) → ℂ) (𝓕 f)
  let p : SchwartzMap (Euclidean (d + 1)) ℂ := 𝓕⁻ h
  let F : ℝ → Euclidean (d + 1) → ℂ := fun t x =>
    sphericalAverage (d + 1) (p : Euclidean (d + 1) → ℂ) t x
  let D : ℝ → Euclidean (d + 1) → ℂ := fun t x =>
    ∫ ω : sphere (0 : Euclidean (d + 1)) 1,
      fderiv ℝ (p : Euclidean (d + 1) → ℂ)
        (x + t • (ω : Euclidean (d + 1))) (ω : Euclidean (d + 1))
        ∂unitSurfaceMeasure (d + 1)
  let B : ℝ := (2 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)
  let C : ℝ := (2 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)
  let J : ℝ := ∫ ξ : Euclidean (d + 1), ‖𝓕 (f : Euclidean (d + 1) → ℂ) ξ‖ ^ 2
  have hp : ContDiff ℝ 1 (p : Euclidean (d + 1) → ℂ) := by
    simpa only [p] using (𝓕⁻ h).smooth (1 : ℕ∞)
  have hpderiv_cont : Continuous (fderiv ℝ (p : Euclidean (d + 1) → ℂ)) :=
    hp.continuous_fderiv (by norm_num)
  have hFcont : Continuous (Function.uncurry F) := by
    change Continuous (fun z : ℝ × Euclidean (d + 1) =>
      sphericalAverage (d + 1) (p : Euclidean (d + 1) → ℂ) z.1 z.2)
    exact continuous_sphericalAverage (p : Euclidean (d + 1) → ℂ) p.continuous
  have hDintegrand : Continuous (Function.uncurry
      (fun (q : ℝ × Euclidean (d + 1))
          (ω : sphere (0 : Euclidean (d + 1)) 1) =>
        fderiv ℝ (p : Euclidean (d + 1) → ℂ)
          (q.2 + q.1 • (ω : Euclidean (d + 1))) (ω : Euclidean (d + 1)))) := by
    exact (hpderiv_cont.comp
      ((continuous_snd.comp continuous_fst).add
        ((continuous_fst.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd)))).clm_apply
            (continuous_subtype_val.comp continuous_snd)
  have hDcont : Continuous (Function.uncurry D) := by
    change Continuous (fun q : ℝ × Euclidean (d + 1) =>
      ∫ ω : sphere (0 : Euclidean (d + 1)) 1,
        fderiv ℝ (p : Euclidean (d + 1) → ℂ)
          (q.2 + q.1 • (ω : Euclidean (d + 1))) (ω : Euclidean (d + 1))
          ∂unitSurfaceMeasure (d + 1))
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := unitSurfaceMeasure (d + 1)) hDintegrand isCompact_univ)
  let dp : SchwartzMap (Euclidean (d + 1))
      (Euclidean (d + 1) →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) p
  have hpbound : ∀ y : Euclidean (d + 1),
      ‖fderiv ℝ (p : Euclidean (d + 1) → ℂ) y‖ ≤
        ‖dp.toBoundedContinuousFunction‖ := by
    intro y
    calc
      ‖fderiv ℝ (p : Euclidean (d + 1) → ℂ) y‖ = ‖dp y‖ := by
        rw [← SchwartzMap.fderivCLM_apply ℂ p y]
      _ = ‖dp.toBoundedContinuousFunction y‖ := rfl
      _ ≤ ‖dp.toBoundedContinuousFunction‖ :=
        BoundedContinuousFunction.norm_coe_le_norm
          (dp.toBoundedContinuousFunction :
            Euclidean (d + 1) →ᵇ (Euclidean (d + 1) →L[ℝ] ℂ)) y
  have hphysical_deriv : ∀ t x, HasDerivAt (fun s => F s x) (D t x) t := by
    intro t x
    simpa only [F, D] using
      hasDerivAt_sphericalAverage (p : Euclidean (d + 1) → ℂ) hp hpbound x t
  have hp2 : MemLp (p : Euclidean (d + 1) → ℂ) 2 volume := p.memLp 2 volume
  have hp1 : Integrable (p : Euclidean (d + 1) → ℂ) volume := p.integrable
  have hpderiv2 : MemLp (fderiv ℝ (p : Euclidean (d + 1) → ℂ)) 2 volume := by
    let dp' : SchwartzMap (Euclidean (d + 1))
        (Euclidean (d + 1) →L[ℝ] ℂ) :=
      (SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) p
    have hdp' : (dp' : Euclidean (d + 1) →
        (Euclidean (d + 1) →L[ℝ] ℂ)) =
        fderiv ℝ (p : Euclidean (d + 1) → ℂ) := by
      funext x
      exact SchwartzMap.fderivCLM_apply ℂ p x
    rw [← hdp']
    exact dp'.memLp 2 volume
  have hFendpoint : Integrable (fun x : Euclidean (d + 1) => ‖F 1 x‖ ^ 2) volume := by
    simpa only [F] using
      integrable_norm_sq_sphericalAverage (p : Euclidean (d + 1) → ℂ)
        p.continuous hp1 hp2 1
  have hD2prod : Integrable (fun q : ℝ × Euclidean (d + 1) => ‖D q.1 q.2‖ ^ 2)
      ((volume.restrict (Icc (1 : ℝ) 2)).prod volume) := by
    simpa only [D] using
      integrable_sq_radiusDerivative_prod (p : Euclidean (d + 1) → ℂ)
        hp hpderiv2 1 2
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact div_nonneg (mul_nonneg (by norm_num) hC0.le)
      (Real.rpow_nonneg (dyadicScale_pos j).le _)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg (mul_nonneg (by norm_num) hC1.le)
      (Real.rpow_nonneg (dyadicScale_pos j).le _)
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun _ => sq_nonneg _
  have hFbound (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) :
      (∫ x : Euclidean (d + 1), ‖F t x‖ ^ 2) ≤ B ^ 2 * J := by
    rcases exists_schwartz_compactSupport_mul_surfaceFourier psi hpsi_compact t with
      ⟨m, hm⟩
    have hmbound (ξ : Euclidean (d + 1)) : ‖m ξ‖ ≤ B := by
      rw [hm ξ]
      have hneg : surfaceFourier (d + 1) (-t • ξ) =
          surfaceFourier (d + 1) (t • ξ) := by
        simpa only [neg_smul] using surfaceFourier_neg (d + 1) (t • ξ)
      calc
        ‖psi ξ * surfaceFourier (d + 1) (-t • ξ)‖ =
            ‖surfaceFourier (d + 1) (t • ξ) * psi ξ‖ := by
          rw [hneg, mul_comm]
        _ = ‖surfaceFourier (d + 1) (t • ξ) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
              phi (((2 : ℝ) ^ j)⁻¹ • ξ))‖ := by rw [hpsi ξ]
        _ ≤ B := by
          simpa only [B] using
            norm_surfaceFourier_succ_smul_mul_smooth_dyadic_bandpass_le_of_sharp
              C0 hC0 hdecay hphi_one hphi_zero hphi_norm j t ht ξ
    have hmult := integral_norm_sq_fourierInv_schwartz_multiplier_le
      m (𝓕 f) hB hmbound
    have hsymbol : (fun ξ : Euclidean (d + 1) =>
        surfaceFourier (d + 1) (-t • ξ) * h ξ) =
        fun ξ => m ξ * 𝓕 (f : Euclidean (d + 1) → ℂ) ξ := by
      funext ξ
      rw [hm ξ]
      simp only [h, SchwartzMap.smulLeftCLM_apply psi.hasTemperateGrowth,
        SchwartzMap.fourier_coe, smul_eq_mul]
      ring
    simpa only [F, p, h, B, J] using
      (show (∫ x : Euclidean (d + 1),
        ‖sphericalAverage (d + 1)
          ((𝓕⁻ h : SchwartzMap (Euclidean (d + 1)) ℂ) :
            Euclidean (d + 1) → ℂ) t x‖ ^ 2) ≤ B ^ 2 * J by
        rw [sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier h t, hsymbol]
        exact hmult)
  have hDfourier (t : ℝ) (x : Euclidean (d + 1)) :
      D t x = 𝓕⁻ (fun ξ : Euclidean (d + 1) =>
        deriv (fun s : ℝ => surfaceFourier (d + 1) (s • (-ξ))) t *
          (psi ξ * 𝓕 (f : Euclidean (d + 1) → ℂ) ξ)) x := by
    simpa only [D, p, h, SchwartzMap.smulLeftCLM_apply psi.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul] using
      sphericalAverage_radiusDerivative_fourierInv_schwartz h t x
  have hDbound (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) :
      (∫ x : Euclidean (d + 1), ‖D t x‖ ^ 2) ≤ C ^ 2 * J := by
    rcases exists_schwartz_compactSupport_mul_surfaceFourier_radius_deriv
        psi hpsi_compact t with ⟨m, hm⟩
    have hmbound (ξ : Euclidean (d + 1)) : ‖m ξ‖ ≤ C := by
      rw [hm ξ]
      have hfun : (fun s : ℝ => surfaceFourier (d + 1) (s • (-ξ))) =
          fun s : ℝ => surfaceFourier (d + 1) (s • ξ) := by
        funext s
        simpa only [smul_neg] using surfaceFourier_neg (d + 1) (s • ξ)
      rw [hfun]
      calc
        ‖psi ξ * deriv (fun s : ℝ =>
            surfaceFourier (d + 1) (s • ξ)) t‖ =
            ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) t *
              psi ξ‖ := by rw [mul_comm]
        _ = ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) t *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
              phi (((2 : ℝ) ^ j)⁻¹ • ξ))‖ := by rw [hpsi ξ]
        _ ≤ C := by
          simpa only [C] using
            norm_deriv_surfaceFourier_succ_smul_mul_smooth_dyadic_bandpass_le_of_sharp
              hd C1 hC1 hderiv hphi_one hphi_zero hphi_norm j t ht ξ
    have hmult := integral_norm_sq_fourierInv_schwartz_multiplier_le
      m (𝓕 f) hC hmbound
    have hsymbol : (fun ξ : Euclidean (d + 1) =>
        deriv (fun s : ℝ => surfaceFourier (d + 1) (s • (-ξ))) t *
          (psi ξ * 𝓕 (f : Euclidean (d + 1) → ℂ) ξ)) =
        fun ξ => m ξ * 𝓕 (f : Euclidean (d + 1) → ℂ) ξ := by
      funext ξ
      rw [hm ξ]
      ring
    calc
      (∫ x : Euclidean (d + 1), ‖D t x‖ ^ 2) =
          ∫ x : Euclidean (d + 1), ‖𝓕⁻ (fun ξ : Euclidean (d + 1) =>
            deriv (fun s : ℝ => surfaceFourier (d + 1) (s • (-ξ))) t *
              (psi ξ * 𝓕 (f : Euclidean (d + 1) → ℂ) ξ)) x‖ ^ 2 := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [hDfourier t x]
      _ ≤ C ^ 2 * J := by
        rw [hsymbol]
        exact hmult
  have hmax :=
    measurable_and_lintegral_iSup_ennreal_norm_sq_le_radiusSobolev_of_hasDerivAt
      (a := (1 : ℝ)) (b := 2) (by norm_num) hFcont hDcont hphysical_deriv
      hFendpoint hD2prod
  have hDouter : Integrable (fun t : ℝ =>
      ∫ x : Euclidean (d + 1), ‖D t x‖ ^ 2)
      (volume.restrict (Icc (1 : ℝ) 2)) :=
    hD2prod.integral_prod_left
  have hDinterval_integrable : IntervalIntegrable (fun t : ℝ =>
      ∫ x : Euclidean (d + 1), ‖D t x‖ ^ 2) volume 1 2 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    exact hDouter
  have hDinterval :
      (∫ t in (1 : ℝ)..2, ∫ x : Euclidean (d + 1), ‖D t x‖ ^ 2) ≤
        C ^ 2 * J := by
    calc
      (∫ t in (1 : ℝ)..2, ∫ x : Euclidean (d + 1), ‖D t x‖ ^ 2) ≤
          ∫ _t in (1 : ℝ)..2, C ^ 2 * J := by
        exact intervalIntegral.integral_mono_on (by norm_num)
          hDinterval_integrable intervalIntegrable_const hDbound
      _ = C ^ 2 * J := by norm_num
  have hEndpointBound :
      (∫ x : Euclidean (d + 1), ‖F 1 x‖ ^ 2) ≤ B ^ 2 * J :=
    hFbound 1 ⟨by norm_num, by norm_num⟩
  have hinside :
      2 * (∫ x : Euclidean (d + 1), ‖F 1 x‖ ^ 2) +
          2 * ((2 : ℝ) - 1) *
            (∫ t in (1 : ℝ)..2, ∫ x : Euclidean (d + 1), ‖D t x‖ ^ 2) ≤
        (2 * B ^ 2 + 2 * C ^ 2) * J := by
    norm_num
    calc
      2 * (∫ x : Euclidean (d + 1), ‖F 1 x‖ ^ 2) +
          2 * (∫ t in (1 : ℝ)..2,
            ∫ x : Euclidean (d + 1), ‖D t x‖ ^ 2) ≤
          2 * (B ^ 2 * J) + 2 * (C ^ 2 * J) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hEndpointBound (by norm_num))
          (mul_le_mul_of_nonneg_left hDinterval (by norm_num))
      _ = (2 * B ^ 2 + 2 * C ^ 2) * J := by ring
  let Q : Euclidean (d + 1) → ENNReal := fun x =>
    ⨆ r : Icc (1 : ℝ) 2, ENNReal.ofReal (‖F r.1 x‖ ^ 2)
  have hQmeas : Measurable Q := by
    simpa only [Q] using hmax.1
  have hQlin : (∫⁻ x : Euclidean (d + 1), Q x) ≤
      ENNReal.ofReal ((2 * B ^ 2 + 2 * C ^ 2) * J) := by
    change (∫⁻ x : Euclidean (d + 1),
      ⨆ r : Icc (1 : ℝ) 2, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ≤
        ENNReal.ofReal ((2 * B ^ 2 + 2 * C ^ 2) * J)
    calc
      (∫⁻ x : Euclidean (d + 1),
        ⨆ r : Icc (1 : ℝ) 2, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ≤
          ENNReal.ofReal
            (2 * (∫ x : Euclidean (d + 1), ‖F 1 x‖ ^ 2) +
              2 * ((2 : ℝ) - 1) *
                (∫ t in (1 : ℝ)..2,
                  ∫ x : Euclidean (d + 1), ‖D t x‖ ^ 2)) := hmax.2
      _ ≤ ENNReal.ofReal ((2 * B ^ 2 + 2 * C ^ 2) * J) :=
        ENNReal.ofReal_le_ofReal hinside
  have hK : 0 ≤ (2 * B ^ 2 + 2 * C ^ 2) * J := by
    apply mul_nonneg
    · exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg (by norm_num) (sq_nonneg _))
    · exact hJ
  rcases memLp_two_toReal_sqrt_of_measurable_lintegral Q hQmeas hK hQlin with
    ⟨hGmem, hGbound⟩
  simp only [Q] at hGmem hGbound
  have hJphysical : J = ∫ x : Euclidean (d + 1), ‖f x‖ ^ 2 := by
    dsimp only [J]
    exact integral_norm_sq_fourier_schwartz_eq f
  rw [hJphysical] at hGbound
  have hbridge :=
    memLp_two_iSup_ennreal_norm_of_memLp_sqrt_iSup_ennreal_norm_sq
      (F := F) (a := (1 : ℝ)) (b := 2) (by norm_num) hFcont hGmem hGbound
  refine ⟨psi, hpsi, ?_, ?_⟩
  · simpa only [F, p, h] using hbridge.1
  · simpa only [F, p, h, B, C] using hbridge.2

/-- The compact-radius `L²` estimate for a prescribed literal smooth
dyadic bandpass.  This is the form used by interpolation: the multiplier is
fixed while the Schwartz input varies. -/
theorem smooth_dyadic_sphericalMaximal_succ_memLp_two_of_sharp_of_bandpass
    {d : Nat} (hd : 2 ≤ d) (C0 C1 : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ ξ : Euclidean (d + 1), 1 ≤ ‖ξ‖ →
      ‖surfaceFourier (d + 1) ξ‖ ≤ C0 / ‖ξ‖ ^ ((d : ℝ) / 2))
    (hderiv : ∀ ξ : Euclidean (d + 1), ∀ r : ℝ, 1 ≤ ‖ξ‖ →
      r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • ξ)) r‖ ≤
        C1 / ‖ξ‖ ^ ((d : ℝ) / 2 - 1))
    (phi f psi : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0)
    (hphi_norm : ∀ ξ, ‖phi ξ‖ ≤ 1) (j : Nat)
    (hpsi : ∀ ξ : Euclidean (d + 1),
      psi ξ = phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        phi (((2 : ℝ) ^ j)⁻¹ • ξ)) :
    MemLp
      (fun x : Euclidean (d + 1) =>
        (⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal ‖sphericalAverage (d + 1)
            ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ
              (psi : Euclidean (d + 1) → ℂ) (𝓕 f)) :
                SchwartzMap (Euclidean (d + 1)) ℂ) : Euclidean (d + 1) → ℂ) r.1 x‖).toReal)
      2 volume ∧
    (∫ x : Euclidean (d + 1),
      ‖(⨆ r : Icc (1 : ℝ) 2,
        ENNReal.ofReal ‖sphericalAverage (d + 1)
          ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ
            (psi : Euclidean (d + 1) → ℂ) (𝓕 f)) :
              SchwartzMap (Euclidean (d + 1)) ℂ) : Euclidean (d + 1) → ℂ)
                r.1 x‖).toReal‖ ^ 2) ≤
      (2 * ((2 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
        2 * ((2 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)) ^ 2) *
        ∫ x : Euclidean (d + 1), ‖f x‖ ^ 2 := by
  rcases exists_smooth_dyadic_sphericalMaximal_succ_memLp_two_of_sharp
      hd C0 C1 hC0 hC1 hdecay hderiv phi f hphi_one hphi_zero hphi_norm j with
    ⟨chi, hchi, hmem, hbound⟩
  have hchi_psi : chi = psi :=
    schwartzMap_eq_of_eq_smooth_dyadic_bandpass hchi hpsi
  rw [hchi_psi] at hmem hbound
  exact ⟨hmem, hbound⟩

/-- Interpolating the literal local `L¹` growth estimate with the sharp local
`L²` estimate.  The conclusion retains the positive splitting scale `s`; in
the dyadic application it is chosen to balance the two displayed terms. -/
theorem smooth_dyadic_sphericalMaximal_succ_lintegral_rpow_le_of_sharp
    {d : Nat} (hd : 2 ≤ d) (C0 C1 : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ ξ : Euclidean (d + 1), 1 ≤ ‖ξ‖ →
      ‖surfaceFourier (d + 1) ξ‖ ≤ C0 / ‖ξ‖ ^ ((d : ℝ) / 2))
    (hderiv : ∀ ξ : Euclidean (d + 1), ∀ r : ℝ, 1 ≤ ‖ξ‖ →
      r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun u : ℝ => surfaceFourier (d + 1) (u • ξ)) r‖ ≤
        C1 / ‖ξ‖ ^ ((d : ℝ) / 2 - 1))
    (phi f psi : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0)
    (hphi_norm : ∀ ξ, ‖phi ξ‖ ≤ 1) (j : Nat)
    (hpsi : ∀ ξ : Euclidean (d + 1),
      psi ξ = phi (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        phi (((2 : ℝ) ^ j)⁻¹ • ξ))
    {q : ℝ} (hq_one : 1 < q) (hq_two : q < 2) (s : ℝ) (hs : 0 < s) :
    let T : SchwartzMap (Euclidean (d + 1)) ℂ → Euclidean (d + 1) → ℝ :=
      smoothDyadicSphericalLocalMaximal psi
    let c₁ : ℝ :=
      surfaceMass (d + 1) * (2 : ℝ) ^ j *
        (2 * (∫ x : Euclidean (d + 1),
          ‖(𝓕⁻ phi : SchwartzMap (Euclidean (d + 1)) ℂ) x‖) +
          3 * (∫ x : Euclidean (d + 1),
            ‖fderiv ℝ ((𝓕⁻ phi : SchwartzMap (Euclidean (d + 1)) ℂ) :
              Euclidean (d + 1) → ℂ) x‖))
    let c₂ : ℝ :=
      2 * ((2 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
        2 * ((2 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)) ^ 2
    let a₂ : ENNReal :=
      (ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal q)⁻¹ +
          (ENNReal.ofReal (2 - q))⁻¹) *
        (∫⁻ x : Euclidean (d + 1), (ENNReal.ofReal ‖f x‖) ^ q)
    let a₁ : ENNReal :=
      ((ENNReal.ofReal (q - 1))⁻¹ + (ENNReal.ofReal (3 - q))⁻¹) *
        (∫⁻ x : Euclidean (d + 1), (ENNReal.ofReal ‖f x‖) ^ q)
    (∫⁻ x : Euclidean (d + 1), ENNReal.ofReal ((T f x) ^ q)) ≤
      ENNReal.ofReal q *
        (4 * ENNReal.ofReal c₂ * ((ENNReal.ofReal s) ^ (2 - q) * a₂) +
          2 * ENNReal.ofReal c₁ * ((ENNReal.ofReal s) ^ (1 - q) * a₁)) := by
  dsimp only
  let T : SchwartzMap (Euclidean (d + 1)) ℂ → Euclidean (d + 1) → ℝ :=
    smoothDyadicSphericalLocalMaximal psi
  let c₁ : ℝ :=
    surfaceMass (d + 1) * (2 : ℝ) ^ j *
      (2 * (∫ x : Euclidean (d + 1),
        ‖(𝓕⁻ phi : SchwartzMap (Euclidean (d + 1)) ℂ) x‖) +
        3 * (∫ x : Euclidean (d + 1),
          ‖fderiv ℝ ((𝓕⁻ phi : SchwartzMap (Euclidean (d + 1)) ℂ) :
              Euclidean (d + 1) → ℂ) x‖))
  let c₂ : ℝ :=
    2 * ((2 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
        2 * ((2 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)) ^ 2
  let a₂ : ENNReal :=
    (ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal q)⁻¹ +
        (ENNReal.ofReal (2 - q))⁻¹) *
        (∫⁻ x : Euclidean (d + 1), (ENNReal.ofReal ‖f x‖) ^ q)
  let a₁ : ENNReal :=
    ((ENNReal.ofReal (q - 1))⁻¹ + (ENNReal.ofReal (3 - q))⁻¹) *
        (∫⁻ x : Euclidean (d + 1), (ENNReal.ofReal ‖f x‖) ^ q)
  change (∫⁻ x : Euclidean (d + 1), ENNReal.ofReal ((T f x) ^ q)) ≤
    ENNReal.ofReal q *
      (4 * ENNReal.ofReal c₂ * ((ENNReal.ofReal s) ^ (2 - q) * a₂) +
        2 * ENNReal.ofReal c₁ * ((ENNReal.ofReal s) ^ (1 - q) * a₁))
  have hT_nonneg : ∀ g x, 0 ≤ T g x := by
    intro g x
    exact ENNReal.toReal_nonneg
  have hT_subadd : ∀ g h x, T (g + h) x ≤ T g x + T h x := by
    intro g h x
    simpa only [T, smoothDyadicSphericalLocalMaximal] using
      smooth_schwartz_multiplier_compact_sphericalMaximal_add_le psi g h x
  have hc₁ : 0 ≤ c₁ := by
    dsimp only [c₁]
    apply mul_nonneg
    · apply mul_nonneg
      · exact measureReal_nonneg
      · positivity
    · apply add_nonneg
      · apply mul_nonneg
        · norm_num
        · exact integral_nonneg fun _ => norm_nonneg _
      · apply mul_nonneg
        · norm_num
        · exact integral_nonneg fun _ => norm_nonneg _
  have hc₂ : 0 ≤ c₂ := by
    dsimp only [c₂]
    positivity
  have hmem_one : ∀ g : SchwartzMap (Euclidean (d + 1)) ℂ, MemLp (T g) 1 volume := by
    intro g
    exact (smooth_dyadic_sphericalMaximal_memLp_one_of_bandpass_geometric
      phi g psi j hpsi).1
  have hbound_one : ∀ g : SchwartzMap (Euclidean (d + 1)) ℂ,
      (∫ x, T g x) ≤ c₁ * ∫ x, ‖(g : Euclidean (d + 1) → ℂ) x‖ := by
    intro g
    have hbound :=
      (smooth_dyadic_sphericalMaximal_memLp_one_of_bandpass_geometric
        phi g psi j hpsi).2
    calc
      (∫ x, T g x) = ∫ x, ‖T g x‖ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (hT_nonneg g x)]
      _ ≤ surfaceMass (d + 1) * (2 : ℝ) ^ j *
          (∫ x, ‖(g : Euclidean (d + 1) → ℂ) x‖) *
          (2 * (∫ x, ‖(𝓕⁻ phi : SchwartzMap (Euclidean (d + 1)) ℂ) x‖) +
            3 * (∫ x,
              ‖fderiv ℝ ((𝓕⁻ phi : SchwartzMap (Euclidean (d + 1)) ℂ) :
                Euclidean (d + 1) → ℂ) x‖)) := by
        exact hbound
      _ = c₁ * ∫ x, ‖(g : Euclidean (d + 1) → ℂ) x‖ := by
        dsimp only [c₁]
        ring
  have hinput_one : ∀ g : SchwartzMap (Euclidean (d + 1)) ℂ,
      Integrable (fun x => ‖(g : Euclidean (d + 1) → ℂ) x‖) volume := by
    intro g
    simpa only using g.integrable.norm
  have hmem_two : ∀ g : SchwartzMap (Euclidean (d + 1)) ℂ, MemLp (T g) 2 volume := by
    intro g
    exact (smooth_dyadic_sphericalMaximal_succ_memLp_two_of_sharp_of_bandpass
      hd C0 C1 hC0 hC1 hdecay hderiv phi g psi
      hphi_one hphi_zero hphi_norm j hpsi).1
  have hbound_two : ∀ g : SchwartzMap (Euclidean (d + 1)) ℂ,
      (∫ x, (T g x) ^ (2 : ℕ)) ≤
        c₂ * ∫ x, ‖(g : Euclidean (d + 1) → ℂ) x‖ ^ (2 : ℕ) := by
    intro g
    have hbound :=
      (smooth_dyadic_sphericalMaximal_succ_memLp_two_of_sharp_of_bandpass
        hd C0 C1 hC0 hC1 hdecay hderiv phi g psi
        hphi_one hphi_zero hphi_norm j hpsi).2
    calc
      (∫ x, (T g x) ^ (2 : ℕ)) = ∫ x, ‖T g x‖ ^ (2 : ℕ) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (hT_nonneg g x)]
      _ ≤ (2 * ((2 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
          2 * ((2 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1)) ^ 2) *
          ∫ x, ‖(g : Euclidean (d + 1) → ℂ) x‖ ^ 2 := by
        exact hbound
      _ = c₂ * ∫ x, ‖(g : Euclidean (d + 1) → ℂ) x‖ ^ (2 : ℕ) := by
        dsimp only [c₂]
  have hinput_two : ∀ g : SchwartzMap (Euclidean (d + 1)) ℂ,
      Integrable (fun x => ‖(g : Euclidean (d + 1) → ℂ) x‖ ^ (2 : ℕ)) volume := by
    intro g
    exact (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).mp
      (g.memLp 2 volume)
  have hTf : AEMeasurable (T f) volume := by
    exact (measurable_smooth_schwartz_multiplier_compact_sphericalMaximal psi f).aemeasurable
  rcases exists_schwartz_rational_low_high_family f with
    ⟨low, high, hlow, hhigh, hsplit⟩
  have hprofiles := measurable_rational_low_high_profile_lintegrals
    f low high hlow hhigh (μ := volume)
  have hsplit' : ∀ t, f = low t + high t := by
    intro t
    ext x
    exact hsplit t x
  have hlow_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ))) *
          (ENNReal.ofReal t) ^ (q - 3)) ≤ a₂ := by
    simpa only [a₂] using
      rational_schwartz_low_weighted_tail f low high hlow hhigh hq_one hq_two
  have hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖high t x‖) *
          (ENNReal.ofReal t) ^ (q - 2)) ≤ a₁ := by
    simpa only [a₁] using
      rational_schwartz_high_weighted_tail f low high hlow hhigh hq_one hq_two
  exact marcinkiewicz_one_two_on_additive_split_real_scaled
    (α := Euclidean (d + 1)) (E := ℂ)
    (F := SchwartzMap (Euclidean (d + 1)) ℂ) (μ := volume)
    (Set.univ : Set (SchwartzMap (Euclidean (d + 1)) ℂ))
    (fun g => (g : Euclidean (d + 1) → ℂ)) T hT_nonneg
    (by
      intro g h _ _ x
      exact hT_subadd g h x)
    c₁ c₂ hc₁ hc₂
    (by
      intro g _
      exact hmem_one g)
    (by
      intro g _
      exact hbound_one g)
    (by
      intro g _
      exact hinput_one g)
    (by
      intro g _
      exact hmem_two g)
    (by
      intro g _
      exact hbound_two g)
    (by
      intro g _
      exact hinput_two g)
    hq_one hq_two f hTf low high
    (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hsplit'
    hprofiles.1 hprofiles.2 a₂ a₁ hlow_tail hhigh_tail s hs

/-- A finite collection of literal radius blocks is controlled in `L²` by
its square function.  This is the order-theoretic part of the global
dyadic-scale argument: it needs no dilation or frequency claim. -/
theorem integrable_sq_finset_sup_radius_blocks
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (hs : s.Nonempty) (u : ι → α → ℝ)
    (hu_meas : ∀ i ∈ s, Measurable (u i))
    (hu_int : ∀ i ∈ s, Integrable (fun x => (u i x) ^ (2 : ℕ)) μ) :
    Integrable (fun x => (s.sup' hs (fun i => u i x)) ^ (2 : ℕ)) μ ∧
      (∫ x, (s.sup' hs (fun i => u i x)) ^ (2 : ℕ) ∂μ) ≤
        ∑ i ∈ s, ∫ x, (u i x) ^ (2 : ℕ) ∂μ := by
  have hsup_meas : Measurable (fun x => s.sup' hs (fun i => u i x)) :=
    by
      have hsup_apply : (s.sup' hs u : α → ℝ) =
          fun x => s.sup' hs (fun i => u i x) := by
        funext x
        exact Finset.sup'_apply hs u x
      rw [← hsup_apply]
      exact Finset.measurable_sup' hs hu_meas
  have hsum_int : Integrable (fun x => ∑ i ∈ s, (u i x) ^ (2 : ℕ)) μ :=
    integrable_finsetSum s hu_int
  have hpoint : ∀ x, (s.sup' hs (fun i => u i x)) ^ (2 : ℕ) ≤
      ∑ i ∈ s, (u i x) ^ (2 : ℕ) := by
    intro x
    rcases s.exists_mem_eq_sup' hs (fun i => u i x) with ⟨i, hi, hsi⟩
    rw [hsi]
    exact Finset.single_le_sum (fun k hk => sq_nonneg (u k x)) hi
  have hsup_int : Integrable (fun x => (s.sup' hs (fun i => u i x)) ^ (2 : ℕ)) μ :=
    Integrable.mono' hsum_int (hsup_meas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hpoint x)
  refine ⟨hsup_int, ?_⟩
  calc
    (∫ x, (s.sup' hs (fun i => u i x)) ^ (2 : ℕ) ∂μ) ≤
        ∫ x, ∑ i ∈ s, (u i x) ^ (2 : ℕ) ∂μ :=
      integral_mono hsup_int hsum_int hpoint
    _ = ∑ i ∈ s, ∫ x, (u i x) ^ (2 : ℕ) ∂μ :=
      integral_finsetSum s hu_int

/-- The shifted fat cutoffs which isolate finitely many literal dyadic radius
blocks obey a Plancherel square-function estimate.  The bound is obtained
from their pointwise overlap, rather than by summing separate block bounds. -/
theorem finite_fat_relative_dyadic_cutoff_square_function_le
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ)
    (hφ_one : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφ_zero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (hφ_norm : ∀ ξ, ‖φ ξ‖ ≤ 1)
    (j : Nat) (K : Finset ℤ) (f : SchwartzMap (Euclidean d) ℂ) :
    (∑ k ∈ K, ∫ x : Euclidean d,
      ‖𝓕⁻ (fun ξ : Euclidean d =>
        (φ (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ ^ (2 : ℕ)) ≤
        24 * ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ) := by
  classical
  choose m hm using fun k : ℤ =>
    exists_schwartzMap_scaled_sub φ
      ((2 : ℝ) ^ ((j : ℤ) + 3 - k))
      ((2 : ℝ) ^ ((j : ℤ) - 2 - k))
      (ne_of_gt (zpow_pos (by norm_num) _))
      (ne_of_gt (zpow_pos (by norm_num) _))
  have hoverlap : ∀ ξ : Euclidean d,
      ∑ k ∈ K, ‖m k ξ‖ ^ (2 : ℕ) ≤ 24 := by
    intro ξ
    simpa only [hm] using
      finite_relative_dyadic_fat_cutoff_square_sum_le
        hφ_one hφ_zero hφ_norm j K ξ
  simpa only [hm] using
    (sum_integral_norm_sq_fourierInv_schwartz_multipliers_le K m f hoverlap)

/-- Exact dilation of a literal relative spherical Fourier multiplier.  This
is the scale-change used before applying the compact-radius estimate to one
dyadic radius block; it is an equality of the actual inverse Fourier
integrals. -/
theorem fourierInv_relative_surface_multiplier_dilate
    {d : Nat} (a : ℝ) (ha : 0 < a) (s : ℝ)
    (g : Euclidean d → ℂ) (x : Euclidean d) :
    𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d ((- (a * s)) • ξ) * g (a • ξ)) x =
      (a⁻¹) ^ Module.finrank ℝ (Euclidean d) •
        𝓕⁻ (fun η : Euclidean d =>
          surfaceFourier d ((-s) • η) * g η) (a⁻¹ • x) := by
  let G : Euclidean d → ℂ := fun η =>
    surfaceFourier d ((-s) • η) * g η
  have hscale := fourierInv_comp_inv_smul G (R := a⁻¹) (inv_pos.mpr ha) x
  simpa only [G, inv_inv, smul_smul, neg_mul, mul_neg, mul_assoc,
    mul_comm, mul_left_comm] using hscale

/-- For a compactly localized moving relative bandpass, both the inverse
Fourier integral and its radius derivative are jointly continuous.  The
derivative is the literal product-rule derivative of the moving surface and
bandpass factors.  This is the regularity input for the radius Sobolev step
on a single dyadic radius block. -/
theorem continuous_and_hasDerivAt_fourierInv_relative_dyadic_bandpass
    {d : Nat} (phi theta f : SchwartzMap (Euclidean d) ℂ)
    (htheta_compact : HasCompactSupport (theta : Euclidean d → ℂ)) (j : Nat) :
    let B : ℝ → Euclidean d → ℂ := fun s xi =>
      phi (((2 : ℝ) ^ (j + 1))⁻¹ • (s • xi)) -
        phi (((2 : ℝ) ^ j)⁻¹ • (s • xi))
    let F : ℝ → Euclidean d → ℂ := fun s x =>
      𝓕⁻ (fun xi : Euclidean d =>
        surfaceFourier d (-s • xi) * B s xi * theta xi *
          𝓕 (f : Euclidean d → ℂ) xi) x
    let D : ℝ → Euclidean d → ℂ := fun s x =>
      𝓕⁻ (fun xi : Euclidean d =>
        (deriv (fun u : ℝ => surfaceFourier d (-u • xi)) s * B s xi +
          surfaceFourier d (-s • xi) * deriv (fun u : ℝ => B u xi) s) *
          theta xi * 𝓕 (f : Euclidean d → ℂ) xi) x
    Continuous (Function.uncurry F) ∧ Continuous (Function.uncurry D) ∧
      ∀ s x, HasDerivAt (fun t => F t x) (D s x) s := by
  dsimp only
  let B : ℝ → Euclidean d → ℂ := fun s xi =>
    phi (((2 : ℝ) ^ (j + 1))⁻¹ • (s • xi)) -
      phi (((2 : ℝ) ^ j)⁻¹ • (s • xi))
  let F : ℝ → Euclidean d → ℂ := fun s x =>
    𝓕⁻ (fun xi : Euclidean d =>
      surfaceFourier d (-s • xi) * B s xi * theta xi *
        𝓕 (f : Euclidean d → ℂ) xi) x
  let D : ℝ → Euclidean d → ℂ := fun s x =>
    𝓕⁻ (fun xi : Euclidean d =>
      (deriv (fun u : ℝ => surfaceFourier d (-u • xi)) s * B s xi +
        surfaceFourier d (-s • xi) * deriv (fun u : ℝ => B u xi) s) *
          theta xi * 𝓕 (f : Euclidean d → ℂ) xi) x
  let K : Set (Euclidean d) := tsupport (theta : Euclidean d → ℂ)
  have hK : IsCompact K := htheta_compact
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hsurface : ContDiff ℝ (↑(⊤ : ℕ∞)) (surfaceFourier d) :=
    contDiff_surfaceFourier d
  have hsurfaceArg : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : ℝ × Euclidean d => -q.1 • q.2) := by
    fun_prop
  have hU : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : ℝ × Euclidean d => surfaceFourier d (-q.1 • q.2)) :=
    hsurface.comp hsurfaceArg
  have hbandArg₁ : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : ℝ × Euclidean d =>
        ((2 : ℝ) ^ (j + 1))⁻¹ • (q.1 • q.2)) := by
    fun_prop
  have hbandArg₀ : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : ℝ × Euclidean d =>
        ((2 : ℝ) ^ j)⁻¹ • (q.1 • q.2)) := by
    fun_prop
  have hB : ContDiff ℝ (↑(⊤ : ℕ∞)) (Function.uncurry B) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × Euclidean d =>
      phi (((2 : ℝ) ^ (j + 1))⁻¹ • (q.1 • q.2)) -
        phi (((2 : ℝ) ^ j)⁻¹ • (q.1 • q.2)))
    exact ((phi.smooth (⊤ : ℕ∞)).comp hbandArg₁).sub
      ((phi.smooth (⊤ : ℕ∞)).comp hbandArg₀)
  let G : (ℝ × Euclidean d) → Euclidean d → ℂ := fun q xi =>
    (Real.fourierChar (inner ℝ xi q.2) : ℂ) *
      (surfaceFourier d (-q.1 • xi) * B q.1 xi * theta xi *
        𝓕 (f : Euclidean d → ℂ) xi)
  have hGcont : Continuous (Function.uncurry G) := by
    change Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
      (Real.fourierChar (inner ℝ q.2 q.1.2) : ℂ) *
        (surfaceFourier d (-q.1.1 • q.2) * B q.1.1 q.2 * theta q.2 *
          𝓕 (f : Euclidean d → ℂ) q.2))
    have hchar : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        (Real.fourierChar (inner ℝ q.2 q.1.2) : ℂ)) := by
      fun_prop
    have hsurfarg' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        -q.1.1 • q.2) := by
      fun_prop
    have hsurf' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        surfaceFourier d (-q.1.1 • q.2)) :=
      (continuous_surfaceFourier d).comp hsurfarg'
    have hbandarg₁' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        ((2 : ℝ) ^ (j + 1))⁻¹ • (q.1.1 • q.2)) := by
      fun_prop
    have hbandarg₀' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        ((2 : ℝ) ^ j)⁻¹ • (q.1.1 • q.2)) := by
      fun_prop
    have hband' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        B q.1.1 q.2) := by
      change Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        phi (((2 : ℝ) ^ (j + 1))⁻¹ • (q.1.1 • q.2)) -
          phi (((2 : ℝ) ^ j)⁻¹ • (q.1.1 • q.2)))
      exact (phi.continuous.comp hbandarg₁').sub (phi.continuous.comp hbandarg₀')
    exact hchar.mul (((hsurf'.mul hband').mul
      (theta.continuous.comp continuous_snd)).mul
        ((𝓕 f).continuous.comp continuous_snd))
  have hGsupport (q : ℝ × Euclidean d) : Function.support (G q) ⊆ K := by
    intro xi hxi
    by_contra hxiK
    have htheta : theta xi = 0 := by
      by_contra htheta
      exact hxiK (subset_tsupport _ htheta)
    change G q xi ≠ 0 at hxi
    exact hxi (by simp [G, htheta])
  have hGintegral (q : ℝ × Euclidean d) :
      (∫ xi : Euclidean d, G q xi) = ∫ xi in K, G q xi := by
    rw [← MeasureTheory.integral_indicator hKmeas]
    rw [Set.indicator_eq_self.mpr (hGsupport q)]
  have hF_eq (q : ℝ × Euclidean d) :
      F q.1 q.2 = ∫ xi in K, G q xi := by
    rw [show F q.1 q.2 = ∫ xi : Euclidean d, G q xi by
      dsimp only [F, G]
      rw [Real.fourierInv_eq]
      rfl]
    exact hGintegral q
  have hFcont : Continuous (Function.uncurry F) := by
    have hcont := continuous_parametric_integral_of_continuous
      (μ := volume) hGcont hK
    rw [show Function.uncurry F = fun q : ℝ × Euclidean d =>
      ∫ xi in K, G q xi by
        funext q
        exact hF_eq q]
    exact hcont
  let dU : ℝ × Euclidean d → ℂ := fun q =>
    fderiv ℝ (surfaceFourier d) (-q.1 • q.2) (-q.2)
  let surfaceFamily : (ℝ × Euclidean d) → Euclidean d → ℂ := fun _ =>
    surfaceFourier d
  have hsurfaceFamily : ContDiff ℝ (↑(⊤ : ℕ∞))
      (Function.uncurry surfaceFamily) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : (ℝ × Euclidean d) × Euclidean d => surfaceFourier d q.2)
    exact hsurface.comp contDiff_snd
  have hsurfaceVec : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : ℝ × Euclidean d => -q.2) := by
    fun_prop
  have hdU : ContDiff ℝ (↑(⊤ : ℕ∞)) dU := by
    dsimp only [dU]
    simpa only [surfaceFamily] using
      hsurfaceFamily.fderiv_apply hsurfaceArg hsurfaceVec (by simp)
  let dB : ℝ × Euclidean d → ℂ := fun q =>
    fderiv ℝ (phi : Euclidean d → ℂ)
      (((2 : ℝ) ^ (j + 1))⁻¹ • (q.1 • q.2))
      (((2 : ℝ) ^ (j + 1))⁻¹ • q.2) -
    fderiv ℝ (phi : Euclidean d → ℂ)
      (((2 : ℝ) ^ j)⁻¹ • (q.1 • q.2))
      (((2 : ℝ) ^ j)⁻¹ • q.2)
  let phiFamily : (ℝ × Euclidean d) → Euclidean d → ℂ := fun _ => phi
  have hphiFamily : ContDiff ℝ (↑(⊤ : ℕ∞))
      (Function.uncurry phiFamily) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : (ℝ × Euclidean d) × Euclidean d => phi q.2)
    exact (phi.smooth (⊤ : ℕ∞)).comp contDiff_snd
  have hbandVec₁ : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : ℝ × Euclidean d => ((2 : ℝ) ^ (j + 1))⁻¹ • q.2) := by
    fun_prop
  have hbandVec₀ : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : ℝ × Euclidean d => ((2 : ℝ) ^ j)⁻¹ • q.2) := by
    fun_prop
  have hdB : ContDiff ℝ (↑(⊤ : ℕ∞)) dB := by
    dsimp only [dB]
    exact (by
      simpa only [phiFamily] using
        (hphiFamily.fderiv_apply hbandArg₁ hbandVec₁ (by simp)).sub
          (hphiFamily.fderiv_apply hbandArg₀ hbandVec₀ (by simp)))
  have hdU_eq (q : ℝ × Euclidean d) :
      deriv (fun u : ℝ => surfaceFourier d (-u • q.2)) q.1 = dU q := by
    have hsurfaceAt : HasFDerivAt (surfaceFourier d)
        (fderiv ℝ (surfaceFourier d) (-q.1 • q.2)) (-q.1 • q.2) :=
      ((hsurface.differentiable (by simp)).differentiableAt).hasFDerivAt
    have hline : HasDerivAt (fun u : ℝ => -u • q.2) (-q.2) q.1 := by
      simpa only [id_eq, Pi.neg_apply, neg_one_smul] using
        ((hasDerivAt_id q.1).neg.smul_const q.2)
    have hcomp := (hsurfaceAt.comp_hasDerivAt q.1 hline).deriv
    rw [show (surfaceFourier d) ∘ (fun u : ℝ => -u • q.2) =
        (fun u : ℝ => surfaceFourier d (-u • q.2)) by rfl] at hcomp
    simpa only [dU] using hcomp
  have hdB_eq (q : ℝ × Euclidean d) :
      deriv (fun u : ℝ => B u q.2) q.1 = dB q := by
    have h := hasDerivAt_smooth_dyadic_bandpass_radial phi j q.1 q.2
    simpa only [B, dB] using h.deriv
  let G' : (ℝ × Euclidean d) → Euclidean d → ℂ := fun q xi =>
    (Real.fourierChar (inner ℝ xi q.2) : ℂ) *
      ((dU (q.1, xi) * B q.1 xi + surfaceFourier d (-q.1 • xi) * dB (q.1, xi)) *
        theta xi * 𝓕 (f : Euclidean d → ℂ) xi)
  have hG'cont : Continuous (Function.uncurry G') := by
    change Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
      (Real.fourierChar (inner ℝ q.2 q.1.2) : ℂ) *
        ((dU (q.1.1, q.2) * B q.1.1 q.2 +
            surfaceFourier d (-q.1.1 • q.2) * dB (q.1.1, q.2)) *
          theta q.2 * 𝓕 (f : Euclidean d → ℂ) q.2))
    have hchar : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        (Real.fourierChar (inner ℝ q.2 q.1.2) : ℂ)) := by
      fun_prop
    have hpair : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        (q.1.1, q.2)) := by
      fun_prop
    have hdU' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        dU (q.1.1, q.2)) := by
      exact hdU.continuous.comp hpair
    have hdB' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        dB (q.1.1, q.2)) := by
      exact hdB.continuous.comp hpair
    have hsurfarg' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        -q.1.1 • q.2) := by
      fun_prop
    have hsurf' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        surfaceFourier d (-q.1.1 • q.2)) :=
      (continuous_surfaceFourier d).comp hsurfarg'
    have hbandarg₁' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        ((2 : ℝ) ^ (j + 1))⁻¹ • (q.1.1 • q.2)) := by
      fun_prop
    have hbandarg₀' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        ((2 : ℝ) ^ j)⁻¹ • (q.1.1 • q.2)) := by
      fun_prop
    have hband' : Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        B q.1.1 q.2) := by
      change Continuous (fun q : (ℝ × Euclidean d) × Euclidean d =>
        phi (((2 : ℝ) ^ (j + 1))⁻¹ • (q.1.1 • q.2)) -
          phi (((2 : ℝ) ^ j)⁻¹ • (q.1.1 • q.2)))
      exact (phi.continuous.comp hbandarg₁').sub (phi.continuous.comp hbandarg₀')
    exact hchar.mul (((hdU'.mul hband').add (hsurf'.mul hdB')).mul
      (theta.continuous.comp continuous_snd) |>.mul
        ((𝓕 f).continuous.comp continuous_snd))
  have hG'support (q : ℝ × Euclidean d) : Function.support (G' q) ⊆ K := by
    intro xi hxi
    by_contra hxiK
    have htheta : theta xi = 0 := by
      by_contra htheta
      exact hxiK (subset_tsupport _ htheta)
    change G' q xi ≠ 0 at hxi
    exact hxi (by simp [G', htheta])
  have hG'integral (q : ℝ × Euclidean d) :
      (∫ xi : Euclidean d, G' q xi) = ∫ xi in K, G' q xi := by
    rw [← MeasureTheory.integral_indicator hKmeas]
    rw [Set.indicator_eq_self.mpr (hG'support q)]
  have hD_eq (q : ℝ × Euclidean d) :
      D q.1 q.2 = ∫ xi in K, G' q xi := by
    have hraw : D q.1 q.2 = ∫ xi : Euclidean d, G' q xi := by
      dsimp only [D, G']
      rw [Real.fourierInv_eq]
      apply integral_congr_ae
      filter_upwards with xi
      rw [hdU_eq (q.1, xi), hdB_eq (q.1, xi)]
      simp only [Circle.smul_def, smul_eq_mul]
    rw [hraw]
    exact hG'integral q
  have hDcont : Continuous (Function.uncurry D) := by
    have hcont := continuous_parametric_integral_of_continuous
      (μ := volume) hG'cont hK
    rw [show Function.uncurry D = fun q : ℝ × Euclidean d =>
      ∫ xi in K, G' q xi by
        funext q
        exact hD_eq q]
    exact hcont
  refine ⟨hFcont, ?_, ?_⟩
  · exact hDcont
  · intro s x
    have hGderiv (t : ℝ) (xi : Euclidean d) :
        HasDerivAt (fun u : ℝ => G (u, x) xi) (G' (t, x) xi) t := by
      have hline : DifferentiableAt ℝ (fun u : ℝ => -u • xi) t := by
        exact ((hasDerivAt_id t).neg.smul_const xi).differentiableAt
      have hsurfaceAt : DifferentiableAt ℝ
          (fun u : ℝ => surfaceFourier d (-u • xi)) t := by
        have hcomp :=
          ((hsurface.differentiable (by simp)).differentiableAt).comp t hline
        rw [show (surfaceFourier d) ∘ (fun u : ℝ => -u • xi) =
            (fun u : ℝ => surfaceFourier d (-u • xi)) by rfl] at hcomp
        exact hcomp
      have hbandAt : DifferentiableAt ℝ (fun u : ℝ => B u xi) t := by
        dsimp only [B]
        exact (hasDerivAt_smooth_dyadic_bandpass_radial phi j t xi).differentiableAt
      have hbandTail := hbandAt.hasDerivAt.mul_const
        (theta xi * 𝓕 (f : Euclidean d → ℂ) xi)
      have hproduct := hsurfaceAt.hasDerivAt.mul hbandTail
      have hfull := hproduct.const_mul (Real.fourierChar (inner ℝ xi x) : ℂ)
      rw [hdU_eq (t, xi), hdB_eq (t, xi)] at hfull
      refine (hfull.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)).congr_deriv ?_
      · intro u
        dsimp only [G]
        simp only [Pi.mul_apply]
        ring
      · dsimp only [G']
        ring
    have hFcurve : (fun t : ℝ => F t x) =
        (fun t : ℝ => ∫ xi in K, G (t, x) xi) := by
      funext t
      simpa only using hF_eq (t, x)
    have hDcurve : D s x = ∫ xi in K, G' (s, x) xi := by
      simpa only using hD_eq (s, x)
    have hGslice (t : ℝ) : Continuous (fun xi : Euclidean d => G (t, x) xi) := by
      change Continuous (fun xi : Euclidean d =>
        (Real.fourierChar (inner ℝ xi x) : ℂ) *
          (surfaceFourier d (-t • xi) * B t xi * theta xi *
            𝓕 (f : Euclidean d → ℂ) xi))
      have hchar : Continuous (fun xi : Euclidean d =>
          (Real.fourierChar (inner ℝ xi x) : ℂ)) := by
        fun_prop
      have hsurfarg : Continuous (fun xi : Euclidean d => -t • xi) := by
        fun_prop
      have hsurf : Continuous (fun xi : Euclidean d => surfaceFourier d (-t • xi)) :=
        (continuous_surfaceFourier d).comp hsurfarg
      have hbandarg₁ : Continuous (fun xi : Euclidean d =>
          ((2 : ℝ) ^ (j + 1))⁻¹ • (t • xi)) := by
        fun_prop
      have hbandarg₀ : Continuous (fun xi : Euclidean d =>
          ((2 : ℝ) ^ j)⁻¹ • (t • xi)) := by
        fun_prop
      have hband : Continuous (fun xi : Euclidean d => B t xi) := by
        change Continuous (fun xi : Euclidean d =>
          phi (((2 : ℝ) ^ (j + 1))⁻¹ • (t • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (t • xi)))
        exact (phi.continuous.comp hbandarg₁).sub (phi.continuous.comp hbandarg₀)
      exact hchar.mul (((hsurf.mul hband).mul theta.continuous).mul (𝓕 f).continuous)
    have hG'slice (t : ℝ) : Continuous (fun xi : Euclidean d => G' (t, x) xi) := by
      change Continuous (fun xi : Euclidean d =>
        (Real.fourierChar (inner ℝ xi x) : ℂ) *
          ((dU (t, xi) * B t xi + surfaceFourier d (-t • xi) * dB (t, xi)) *
            theta xi * 𝓕 (f : Euclidean d → ℂ) xi))
      have hchar : Continuous (fun xi : Euclidean d =>
          (Real.fourierChar (inner ℝ xi x) : ℂ)) := by
        fun_prop
      have hpair : Continuous (fun xi : Euclidean d => (t, xi)) := by
        fun_prop
      have hdU' : Continuous (fun xi : Euclidean d => dU (t, xi)) :=
        hdU.continuous.comp hpair
      have hdB' : Continuous (fun xi : Euclidean d => dB (t, xi)) :=
        hdB.continuous.comp hpair
      have hsurfarg : Continuous (fun xi : Euclidean d => -t • xi) := by
        fun_prop
      have hsurf : Continuous (fun xi : Euclidean d => surfaceFourier d (-t • xi)) :=
        (continuous_surfaceFourier d).comp hsurfarg
      have hbandarg₁ : Continuous (fun xi : Euclidean d =>
          ((2 : ℝ) ^ (j + 1))⁻¹ • (t • xi)) := by
        fun_prop
      have hbandarg₀ : Continuous (fun xi : Euclidean d =>
          ((2 : ℝ) ^ j)⁻¹ • (t • xi)) := by
        fun_prop
      have hband : Continuous (fun xi : Euclidean d => B t xi) := by
        change Continuous (fun xi : Euclidean d =>
          phi (((2 : ℝ) ^ (j + 1))⁻¹ • (t • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (t • xi)))
        exact (phi.continuous.comp hbandarg₁).sub (phi.continuous.comp hbandarg₀)
      exact hchar.mul (((hdU'.mul hband).add (hsurf.mul hdB')).mul theta.continuous |>.mul
        (𝓕 f).continuous)
    have hG'curve : Continuous (fun q : ℝ × Euclidean d => G' (q.1, x) q.2) := by
      change Continuous (fun q : ℝ × Euclidean d =>
        (Real.fourierChar (inner ℝ q.2 x) : ℂ) *
          ((dU q * B q.1 q.2 + surfaceFourier d (-q.1 • q.2) * dB q) *
            theta q.2 * 𝓕 (f : Euclidean d → ℂ) q.2))
      have hchar : Continuous (fun q : ℝ × Euclidean d =>
          (Real.fourierChar (inner ℝ q.2 x) : ℂ)) := by
        fun_prop
      have hsurfarg : Continuous (fun q : ℝ × Euclidean d => -q.1 • q.2) := by
        fun_prop
      have hsurf : Continuous (fun q : ℝ × Euclidean d =>
          surfaceFourier d (-q.1 • q.2)) :=
        (continuous_surfaceFourier d).comp hsurfarg
      exact hchar.mul (((hdU.continuous.mul hB.continuous).add
        (hsurf.mul hdB.continuous)).mul (theta.continuous.comp continuous_snd) |>.mul
          ((𝓕 f).continuous.comp continuous_snd))
    have hFmeas : ∀ᶠ t in nhds s,
        AEStronglyMeasurable (fun xi : Euclidean d => G (t, x) xi)
          (volume.restrict K) := by
      filter_upwards [] with t
      exact (hGslice t).aestronglyMeasurable.restrict
    have hFint : Integrable (fun xi : Euclidean d => G (s, x) xi)
        (volume.restrict K) := by
      have hcompact : HasCompactSupport (fun xi : Euclidean d => G (s, x) xi) := by
        apply HasCompactSupport.of_support_subset_isCompact hK
        exact hGsupport (s, x)
      exact ((hGslice s).integrable_of_hasCompactSupport hcompact).restrict
    have hF'meas : AEStronglyMeasurable (fun xi : Euclidean d => G' (s, x) xi)
        (volume.restrict K) := by
      exact (hG'slice s).aestronglyMeasurable.restrict
    have hLcont : Continuous (fun q : ℝ × Euclidean d => G' (q.1, x) q.2) := by
      exact hG'curve
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
      hLcont.continuousOn
    have hbound : ∀ᵐ xi : Euclidean d ∂(volume.restrict K),
        ∀ t ∈ Icc (s - 1) (s + 1), ‖G' (t, x) xi‖ ≤ C := by
      filter_upwards [ae_restrict_mem hKmeas] with xi hxi
      intro t ht
      exact hC (t, xi) ⟨ht, hxi⟩
    have hCint : Integrable (fun _ : Euclidean d => C) (volume.restrict K) := by
      simpa only [IntegrableOn] using
        (integrableOn_const (μ := volume) (s := K) hK.measure_ne_top :
          IntegrableOn (fun _ : Euclidean d => C) K volume)
    have hdiff : ∀ᵐ xi : Euclidean d ∂(volume.restrict K),
        ∀ t ∈ Icc (s - 1) (s + 1),
          HasDerivAt (fun u : ℝ => G (u, x) xi) (G' (t, x) xi) t :=
      Filter.Eventually.of_forall fun xi t _ => hGderiv t xi
    have hs : Icc (s - 1) (s + 1) ∈ nhds s :=
      Icc_mem_nhds (sub_lt_self s zero_lt_one) (lt_add_of_pos_right s zero_lt_one)
    have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict K) (s := Icc (s - 1) (s + 1)) (x₀ := s)
      (bound := fun _ : Euclidean d => C)
      (F := fun t (xi : Euclidean d) => G (t, x) xi)
      (F' := fun t (xi : Euclidean d) => G' (t, x) xi)
      hs hFmeas hFint hF'meas hbound hCint hdiff
    have hfinal : HasDerivAt (fun t => F t x) (D s x) s := by
      rw [hFcurve, hDcurve]
      exact hparam.2
    exact hfinal

end

end LeanSpherical.HarmonicAnalysis
