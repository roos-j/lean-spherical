/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceCore
import LeanSpherical.HarmonicAnalysis.FourierRadius
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Spherical-average differentiation and local maximal prerequisites

This module consolidates the physical and Fourier radius-derivative
identities for spherical averages, along with their local `L¹` estimates.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- The elementary first-moment bound for the phase on the unit sphere. -/
theorem norm_surfacePhase_le (d : ℕ) (ξ : Euclidean d)
    (ω : sphere (0 : Euclidean d) 1) :
    ‖surfacePhase d ξ ω‖ ≤ 2 * Real.pi * ‖ξ‖ := by
  have hω : ‖(ω : Euclidean d)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  rw [surfacePhase, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one]
  calc
    |(-2 : ℝ) * Real.pi * inner ℝ (ω : Euclidean d) ξ| =
        (2 * Real.pi) * |inner ℝ (ω : Euclidean d) ξ| := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg Real.pi_pos.le]
      ring
    _ ≤ (2 * Real.pi) * (‖(ω : Euclidean d)‖ * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
    _ = 2 * Real.pi * ‖ξ‖ := by rw [hω]; ring

theorem hasDerivAt_surfaceFourier_radial (d : ℕ) (ξ : Euclidean d) :
    HasDerivAt (fun r : ℝ => surfaceFourier d (r • ξ))
      (∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d ξ ω) * surfacePhase d ξ ω
          ∂unitSurfaceMeasure d) 1 := by
  change HasDerivAt
    (fun r : ℝ => ∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d (r • ξ) ω) ∂unitSurfaceMeasure d)
    (∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d ξ ω) * surfacePhase d ξ ω ∂unitSurfaceMeasure d) 1
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := unitSurfaceMeasure d) (s := Set.univ) (x₀ := (1 : ℝ))
    (bound := fun _ : sphere (0 : Euclidean d) 1 => 2 * Real.pi * ‖ξ‖)
    (F := fun r ω => Complex.exp (surfacePhase d (r • ξ) ω))
    (F' := fun r ω =>
      Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω)
    Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [one_smul] using h.2
  · filter_upwards [] with r
    exact (by
      unfold surfacePhase
      fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
        Complex.exp (surfacePhase d (r • ξ) ω))).aestronglyMeasurable
  · apply Integrable.of_bound
    · exact (by
      unfold surfacePhase
      fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
          Complex.exp (surfacePhase d ((1 : ℝ) • ξ) ω))).aestronglyMeasurable
    · filter_upwards with ω
      exact (norm_surfaceFourier_kernel d (1 • ξ) ω).le
  · exact (by
      unfold surfacePhase
      fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
        Complex.exp (surfacePhase d ((1 : ℝ) • ξ) ω) *
          surfacePhase d ξ ω)).aestronglyMeasurable
  · filter_upwards with ω
    intro r hr
    rw [norm_mul, norm_surfaceFourier_kernel]
    simpa using norm_surfacePhase_le d ξ ω
  · exact integrable_const _
  · filter_upwards with ω
    intro r hr
    have hlin : HasDerivAt (fun x : ℝ => (x : ℂ) * surfacePhase d ξ ω)
        (surfacePhase d ξ ω) r :=
      (hasDerivAt_mul_const (surfacePhase d ξ ω) :
        HasDerivAt (fun z : ℂ => z * surfacePhase d ξ ω)
          (surfacePhase d ξ ω) (r : ℂ)).comp_ofReal
    simpa only [surfacePhase_smul] using hlin.cexp

/-- The same dominated differentiation argument works at every radius.  This
is the radius-dependent derivative used before taking a supremum over a
compact radius interval. -/
theorem hasDerivAt_surfaceFourier_radial_at (d : ℕ) (ξ : Euclidean d) (r₀ : ℝ) :
    HasDerivAt (fun r : ℝ => surfaceFourier d (r • ξ))
      (∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d (r₀ • ξ) ω) * surfacePhase d ξ ω
          ∂unitSurfaceMeasure d) r₀ := by
  change HasDerivAt
    (fun r : ℝ => ∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d (r • ξ) ω) ∂unitSurfaceMeasure d)
    (∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d (r₀ • ξ) ω) * surfacePhase d ξ ω
        ∂unitSurfaceMeasure d) r₀
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := unitSurfaceMeasure d) (s := Set.univ) (x₀ := r₀)
    (bound := fun _ : sphere (0 : Euclidean d) 1 => 2 * Real.pi * ‖ξ‖)
    (F := fun r ω => Complex.exp (surfacePhase d (r • ξ) ω))
    (F' := fun r ω =>
      Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω)
    Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact h.2
  · filter_upwards [] with r
    exact (by
      unfold surfacePhase
      fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
        Complex.exp (surfacePhase d (r • ξ) ω))).aestronglyMeasurable
  · apply Integrable.of_bound
    · exact (by
        unfold surfacePhase
        fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
          Complex.exp (surfacePhase d (r₀ • ξ) ω))).aestronglyMeasurable
    · filter_upwards with ω
      exact (norm_surfaceFourier_kernel d (r₀ • ξ) ω).le
  · exact (by
      unfold surfacePhase
      fun_prop : Continuous (fun ω : sphere (0 : Euclidean d) 1 =>
        Complex.exp (surfacePhase d (r₀ • ξ) ω) *
          surfacePhase d ξ ω)).aestronglyMeasurable
  · filter_upwards with ω
    intro r hr
    rw [norm_mul, norm_surfaceFourier_kernel]
    simpa using norm_surfacePhase_le d ξ ω
  · exact integrable_const _
  · filter_upwards with ω
    intro r hr
    have hlin : HasDerivAt (fun x : ℝ => (x : ℂ) * surfacePhase d ξ ω)
        (surfacePhase d ξ ω) r :=
      (hasDerivAt_mul_const (surfacePhase d ξ ω) :
        HasDerivAt (fun z : ℂ => z * surfacePhase d ξ ω)
          (surfacePhase d ξ ω) (r : ℂ)).comp_ofReal
    simpa only [surfacePhase_smul] using hlin.cexp

/-- Differentiating after absorbing a nonzero radial scale into the frequency
variable gives the corresponding scalar factor. -/
theorem deriv_surfaceFourier_radial_rescale (d : ℕ) (ξ : Euclidean d) (r : ℝ) :
    deriv (fun t : ℝ => surfaceFourier d (t • (r • ξ))) 1 =
      r • deriv (fun s : ℝ => surfaceFourier d (s • ξ)) r := by
  have hlin : HasDerivAt (fun t : ℝ => t * r) r 1 := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id (1 : ℝ)).mul_const r
  have houter : HasDerivAt (fun s : ℝ => surfaceFourier d (s • ξ))
      (∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω
          ∂unitSurfaceMeasure d) (1 * r) := by
    simpa only [one_mul] using hasDerivAt_surfaceFourier_radial_at d ξ r
  have hcomp := HasDerivAt.scomp 1 houter hlin
  calc
    deriv (fun t : ℝ => surfaceFourier d (t • (r • ξ))) 1 =
        r • (∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω
            ∂unitSurfaceMeasure d) := by
      rw [show (fun t : ℝ => surfaceFourier d (t • (r • ξ))) =
          ((fun s : ℝ => surfaceFourier d (s • ξ)) ∘ fun t => t * r) by
            funext t
            rw [Function.comp_apply, smul_smul]]
      exact hcomp.deriv
    _ = r • deriv (fun s : ℝ => surfaceFourier d (s • ξ)) r := by
      rw [(hasDerivAt_surfaceFourier_radial_at d ξ r).deriv]

/-- The radial derivative has a uniform elementary bound at every radius.
Sharp decay of this derivative still requires stationary phase. -/
theorem norm_deriv_surfaceFourier_radial_le (d : ℕ) (ξ : Euclidean d) (r : ℝ) :
    ‖deriv (fun s : ℝ => surfaceFourier d (s • ξ)) r‖ ≤
      (2 * Real.pi * ‖ξ‖) * (unitSurfaceMeasure d).real univ := by
  rw [(hasDerivAt_surfaceFourier_radial_at d ξ r).deriv]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with ω
  rw [norm_mul, norm_surfaceFourier_kernel]
  simpa using norm_surfacePhase_le d ξ ω

/-- The integral formula for the radial derivative depends continuously on
the radius. -/
theorem continuous_surfaceFourier_radial_derivative_integral
    (d : ℕ) (ξ : Euclidean d) :
    Continuous (fun r : ℝ => ∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω
        ∂unitSurfaceMeasure d) := by
  have hcont : Continuous (Function.uncurry
      (fun (r : ℝ) (ω : sphere (0 : Euclidean d) 1) =>
        Complex.exp (surfacePhase d (r • ξ) ω) * surfacePhase d ξ ω)) := by
    unfold surfacePhase
    fun_prop
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (μ := unitSurfaceMeasure d) hcont isCompact_univ)

/-- Before using oscillation, the radial Fourier transform is already
Lipschitz, with the elementary first-moment constant. -/
theorem norm_surfaceFourier_radial_sub_le
    (d : ℕ) (ξ : Euclidean d) (r s : ℝ) :
    ‖surfaceFourier d (r • ξ) - surfaceFourier d (s • ξ)‖ ≤
      (2 * Real.pi * ‖ξ‖) * (unitSurfaceMeasure d).real univ * |r - s| := by
  have hdiff : ∀ t ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (fun u : ℝ => surfaceFourier d (u • ξ)) t :=
    fun t _ => (hasDerivAt_surfaceFourier_radial_at d ξ t).differentiableAt
  have hbound : ∀ t ∈ (Set.univ : Set ℝ),
      ‖deriv (fun u : ℝ => surfaceFourier d (u • ξ)) t‖ ≤
        (2 * Real.pi * ‖ξ‖) * (unitSurfaceMeasure d).real univ :=
    fun t _ => norm_deriv_surfaceFourier_radial_le d ξ t
  simpa [Real.norm_eq_abs] using
    (Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound convex_univ
      (Set.mem_univ s) (Set.mem_univ r))

/-- The one-dimensional Sobolev step applied directly to the concrete radial
surface multiplier.  The remaining analytic task is to add oscillatory decay
to both terms on the right. -/
theorem norm_sq_surfaceFourier_radial_le_radiusSobolev
    (d : ℕ) (ξ : Euclidean d) {a b r : ℝ} (hr : r ∈ Set.Icc a b) :
    ‖surfaceFourier d (r • ξ)‖ ^ 2 ≤
      2 * ‖surfaceFourier d (a • ξ)‖ ^ 2 +
        2 * (b - a) *
          ∫ t in a..b, ‖∫ ω : sphere (0 : Euclidean d) 1,
            Complex.exp (surfacePhase d (t • ξ) ω) * surfacePhase d ξ ω
              ∂unitSurfaceMeasure d‖ ^ 2 := by
  exact
    norm_sq_le_two_mul_norm_sq_add_two_mul_length_mul_intervalIntegral_norm_sq_of_hasDerivAt
      hr (continuous_surfaceFourier_radial_derivative_integral d ξ)
      (fun t => hasDerivAt_surfaceFourier_radial_at d ξ t)

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- A continuous input has a jointly continuous concrete spherical average. -/
theorem continuous_sphericalAverage {d : ℕ} (f : Euclidean d → ℂ)
    (hf : Continuous f) :
    Continuous (fun p : ℝ × Euclidean d => sphericalAverage d f p.1 p.2) := by
  unfold sphericalAverage
  have hjoint : Continuous (Function.uncurry
      (fun (p : ℝ × Euclidean d) (ω : sphere (0 : Euclidean d) 1) =>
        f (p.2 + p.1 • (ω : Euclidean d)))) := by
    exact hf.comp
      ((continuous_snd.comp continuous_fst).add
        ((continuous_fst.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd)))
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (μ := unitSurfaceMeasure d) hjoint isCompact_univ)

/-- For a continuous input, each radius restriction of the spherical average
is continuous. -/
theorem continuous_sphericalAverage_radial {d : ℕ} (f : Euclidean d → ℂ)
    (hf : Continuous f) (x : Euclidean d) :
    Continuous (fun r : ℝ => sphericalAverage d f r x) :=
  (continuous_sphericalAverage f hf).comp
    ((continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)))

/-- The compact-radius maximal norm of a continuous spherical average is
measurable. -/
theorem measurable_iSup_ennreal_norm_sphericalAverage
    {d : ℕ} (f : Euclidean d → ℂ) (hf : Continuous f) {a b : ℝ} :
    Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) :=
  measurable_iSup_ennreal_norm_of_continuous
    (d := d) (F := fun p => sphericalAverage d f p.1 p.2) (a := a) (b := b)
    (continuous_sphericalAverage f hf)

/-- The compact-radius maximal square function of a continuous spherical
average is measurable. -/
theorem measurable_iSup_ennreal_norm_sq_sphericalAverage
    {d : ℕ} (f : Euclidean d → ℂ) (hf : Continuous f) {a b : ℝ} :
    Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal (‖sphericalAverage d f r.1 x‖ ^ 2)) :=
  measurable_iSup_ennreal_norm_sq_of_continuous
    (d := d) (F := fun p => sphericalAverage d f p.1 p.2) (a := a) (b := b)
    (continuous_sphericalAverage f hf)

/-- The literal compact-radius maximal norm is subadditive on continuous
inputs.  This is the pointwise decomposition step used with smooth
Schwartz-preserving amplitude truncations. -/
theorem iSup_ennreal_norm_sphericalAverage_add_le
    {d : ℕ} (f g : Euclidean d → ℂ) (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (x : Euclidean d) :
    (⨆ r : Icc a b,
      ENNReal.ofReal ‖sphericalAverage d (f + g) r.1 x‖) ≤
      (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) +
        ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖ := by
  apply iSup_le
  intro r
  have hint (h : Euclidean d → ℂ) (hh : Continuous h) : Integrable
      (fun ω : sphere (0 : Euclidean d) 1 => h (x + r.1 • (ω : Euclidean d)))
      (unitSurfaceMeasure d) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hh.comp
        ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => x).add
          ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => r.1).smul
            continuous_subtype_val))
    · exact HasCompactSupport.of_compactSpace _
  have havg : sphericalAverage d (f + g) r.1 x =
      sphericalAverage d f r.1 x + sphericalAverage d g r.1 x := by
    unfold sphericalAverage
    change ∫ ω : sphere (0 : Euclidean d) 1,
      (f (x + r.1 • (ω : Euclidean d)) + g (x + r.1 • (ω : Euclidean d)))
      ∂unitSurfaceMeasure d = _
    rw [MeasureTheory.integral_add (hint f hf) (hint g hg)]
  rw [havg]
  calc
    ENNReal.ofReal ‖sphericalAverage d f r.1 x + sphericalAverage d g r.1 x‖ ≤
        ENNReal.ofReal (‖sphericalAverage d f r.1 x‖ + ‖sphericalAverage d g r.1 x‖) :=
      ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖sphericalAverage d f r.1 x‖ +
          ENNReal.ofReal ‖sphericalAverage d g r.1 x‖ := by
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    _ ≤ (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) +
          ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖ := by
      gcongr
      · exact le_iSup (fun r : Icc a b =>
          ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) r
      · exact le_iSup (fun r : Icc a b =>
          ENNReal.ofReal ‖sphericalAverage d g r.1 x‖) r

/-- A continuous spherical average attains its compact-radius maximum, so
the corresponding extended-real supremum is finite. -/
theorem iSup_ennreal_norm_sphericalAverage_ne_top
    {d : ℕ} (f : Euclidean d → ℂ) (hf : Continuous f) {a b : ℝ}
    (hab : a ≤ b) (x : Euclidean d) :
    (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) ≠ ⊤ := by
  have hnorm : Continuous (fun r : ℝ => ‖sphericalAverage d f r x‖) :=
    (continuous_sphericalAverage_radial f hf x).norm
  obtain ⟨r₀, hr₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hab) hnorm.continuousOn
  have hsup :
      (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) =
        ENNReal.ofReal ‖sphericalAverage d f r₀ x‖ := by
    apply le_antisymm
    · apply iSup_le
      intro r
      exact ENNReal.ofReal_le_ofReal (hmax r.2)
    · exact le_iSup (fun r : Icc a b =>
        ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) ⟨r₀, hr₀⟩
  rw [hsup]
  exact ENNReal.ofReal_ne_top

/-- The ordinary real-valued compact-radius maximal norm is subadditive on
continuous inputs. -/
theorem toReal_iSup_ennreal_norm_sphericalAverage_add_le
    {d : ℕ} (f g : Euclidean d → ℂ) (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) (x : Euclidean d) :
    (⨆ r : Icc a b,
      ENNReal.ofReal ‖sphericalAverage d (f + g) r.1 x‖).toReal ≤
      (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖).toReal +
        (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖).toReal := by
  have hfg : Continuous (f + g) := hf.add hg
  have hleft := iSup_ennreal_norm_sphericalAverage_add_le f g hf hg (a := a) (b := b) x
  have hfgfin := iSup_ennreal_norm_sphericalAverage_ne_top (f + g) hfg hab x
  have hffin := iSup_ennreal_norm_sphericalAverage_ne_top f hf hab x
  have hgfin := iSup_ennreal_norm_sphericalAverage_ne_top g hg hab x
  have hsumfin :
      (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) +
          ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hffin, hgfin⟩
  calc
    (⨆ r : Icc a b,
      ENNReal.ofReal ‖sphericalAverage d (f + g) r.1 x‖).toReal ≤
        ((⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) +
          ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖).toReal :=
      (ENNReal.toReal_le_toReal hfgfin hsumfin).2 hleft
    _ = (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖).toReal +
          (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖).toReal :=
      ENNReal.toReal_add hffin hgfin

/-- For a continuous input, the concrete spherical maximal function over all
positive radii is measurable.  The supremum is reduced by lower
semicontinuity to a countable dense subset of `Ioi 0`. -/
theorem measurable_sphericalMaximal {d : ℕ} (f : Euclidean d → ℂ)
    (hf : Continuous f) :
    Measurable (sphericalMaximal d f) := by
  let F : ℝ × Euclidean d → ℂ := fun p => sphericalAverage d f p.1 p.2
  have hF : Continuous F := by
    simpa only [F] using continuous_sphericalAverage f hf
  have hG : Measurable (⨆ r : Ioi (0 : ℝ), fun x : Euclidean d =>
      ENNReal.ofReal ‖F (r.1, x)‖) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro r
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_const.prodMk continuous_id)).norm)).measurable
    · intro x
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_subtype_val.prodMk continuous_const)).norm)).lowerSemicontinuous
  have hEq : sphericalMaximal d f =
      ⨆ r : Ioi (0 : ℝ), fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖ := by
    funext x
    exact (iSup_apply
      (f := fun r : Ioi (0 : ℝ) => fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖) (a := x)).symm
  rw [hEq]
  exact hG

/-- The mass-normalized positive-radius maximal function is measurable for
continuous inputs as well. -/
theorem measurable_normalizedSphericalMaximal {d : ℕ}
    (f : Euclidean d → ℂ) (hf : Continuous f) :
    Measurable (normalizedSphericalMaximal d f) := by
  let F : ℝ × Euclidean d → ℂ := fun p => normalizedSphericalAverage d f p.1 p.2
  have hF : Continuous F := by
    unfold F normalizedSphericalAverage
    exact continuous_const.mul (continuous_sphericalAverage f hf)
  have hG : Measurable (⨆ r : Ioi (0 : ℝ), fun x : Euclidean d =>
      ENNReal.ofReal ‖F (r.1, x)‖) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro r
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_const.prodMk continuous_id)).norm)).measurable
    · intro x
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_subtype_val.prodMk continuous_const)).norm)).lowerSemicontinuous
  have hEq : normalizedSphericalMaximal d f =
      ⨆ r : Ioi (0 : ℝ), fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖ := by
    funext x
    exact (iSup_apply
      (f := fun r : Ioi (0 : ℝ) => fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖) (a := x)).symm
  rw [hEq]
  exact hG

end

end LeanSpherical.HarmonicAnalysis

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

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform
open scoped FourierTransform

noncomputable section

/-- A fixed spherical average of a Schwartz input is the literal inverse
Fourier transform of its concrete surface multiplier. -/
theorem sphericalAverage_eq_fourierInv_surfaceMultiplier_schwartz
    {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ) (r : ℝ) :
    sphericalAverage d (f : Euclidean d → ℂ) r =
      𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) := by
  have hmult_integrable : Integrable (fun ξ : Euclidean d =>
      surfaceFourier d (-r • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) volume := by
    refine ((𝓕 f).integrable.norm.const_mul (surfaceMass d : ℝ)).mono' ?_ ?_
    · exact (((continuous_surfaceFourier d).comp
          ((continuous_const : Continuous fun _ : Euclidean d => -r).smul continuous_id)).mul
        (𝓕 f).continuous).aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa [surfaceMass] using norm_surfaceFourier_le_surfaceMass d (-r • ξ))
        (norm_nonneg (𝓕 (f : Euclidean d → ℂ) ξ))
  have havg_cont : Continuous (sphericalAverage d (f : Euclidean d → ℂ) r) :=
    (continuous_sphericalAverage (f : Euclidean d → ℂ) f.continuous).comp
      ((continuous_const : Continuous fun _ : Euclidean d => r).prodMk continuous_id)
  have hfourier_avg : Integrable (𝓕 (sphericalAverage d (f : Euclidean d → ℂ) r)) volume :=
    hmult_integrable.congr (Filter.Eventually.of_forall fun ξ =>
      (fourier_sphericalAverage (f : Euclidean d → ℂ) f.continuous f.integrable r ξ).symm)
  have hinv := havg_cont.fourierInv_fourier_eq
    (integrable_sphericalAverage (f : Euclidean d → ℂ) f.continuous f.integrable r)
    hfourier_avg
  have hfourier_eq : 𝓕 (sphericalAverage d (f : Euclidean d → ℂ) r) =
      fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    exact fourier_sphericalAverage (f : Euclidean d → ℂ) f.continuous f.integrable r ξ
  rw [hfourier_eq] at hinv
  exact hinv.symm

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Metric Set
open scoped FourierTransform

noncomputable section

/-- For Schwartz data, differentiate the literal inverse-Fourier representation
of the spherical multiplier under the frequency integral. -/
theorem hasDerivAt_fourierInv_surfaceMultiplier_radial_schwartz
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) (r : ℝ) (x : Euclidean d) :
    HasDerivAt
      (fun s : ℝ => 𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (s • (-ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x)
      (𝓕⁻ (fun ξ : Euclidean d =>
        (∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω
            ∂unitSurfaceMeasure d) * 𝓕 (f : Euclidean d → ℂ) ξ) x)
      r := by
  let D : Euclidean d → ℂ := fun ξ =>
    ∫ ω : sphere (0 : Euclidean d) 1,
      Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω
        ∂unitSurfaceMeasure d
  let F : ℝ → Euclidean d → ℂ := fun s ξ =>
    (Real.fourierChar (inner ℝ ξ x) : ℂ) *
      (surfaceFourier d (s • (-ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ)
  let F' : ℝ → Euclidean d → ℂ := fun s ξ =>
    (Real.fourierChar (inner ℝ ξ x) : ℂ) *
      ((∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d (s • (-ξ)) ω) * surfacePhase d (-ξ) ω
          ∂unitSurfaceMeasure d) * 𝓕 (f : Euclidean d → ℂ) ξ)
  have hinv (s : ℝ) :
      𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (s • (-ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x =
        ∫ ξ : Euclidean d, F s ξ := by
    rw [Real.fourierInv_eq]
    rfl
  have hinv' :
      𝓕⁻ (fun ξ : Euclidean d =>
        (∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω
            ∂unitSurfaceMeasure d) * 𝓕 (f : Euclidean d → ℂ) ξ) x =
        ∫ ξ : Euclidean d, F' r ξ := by
    rw [Real.fourierInv_eq]
    rfl
  rw [show (fun s : ℝ => 𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (s • (-ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x) =
      fun s => ∫ ξ : Euclidean d, F s ξ by
        funext s
        exact hinv s,
    hinv']
  have hchar (ξ : Euclidean d) : ‖(Real.fourierChar (inner ℝ ξ x) : ℂ)‖ = 1 := by
    rw [Real.fourierChar_apply]
    exact Complex.norm_exp_ofReal_mul_I _
  have hchar_cont : Continuous
      (fun ξ : Euclidean d => (Real.fourierChar (inner ℝ ξ x) : ℂ)) :=
    (Real.continuous_fourierChar.comp
      (continuous_id.inner (continuous_const : Continuous fun _ : Euclidean d => x))
      |> continuous_subtype_val.comp)
  have hFmeas : ∀ᶠ s in nhds r, AEStronglyMeasurable (F s) volume := by
    filter_upwards [] with s
    have hsurf : Continuous (fun ξ : Euclidean d => surfaceFourier d (s • (-ξ))) :=
      (continuous_surfaceFourier d).comp
        ((continuous_const : Continuous fun _ : Euclidean d => s).smul continuous_id.neg)
    exact (hchar_cont.mul (hsurf.mul (𝓕 f).continuous)).aestronglyMeasurable
  have hFint : Integrable (F r) volume := by
    have hmeas : AEStronglyMeasurable (F r) volume :=
      hFmeas.self_of_nhds
    refine ((𝓕 f).integrable.norm.const_mul (surfaceMass d)).mono' hmeas ?_
    filter_upwards with ξ
    dsimp only [F]
    rw [norm_mul, hchar, one_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa [surfaceMass] using norm_surfaceFourier_le_surfaceMass d (r • (-ξ)))
      (norm_nonneg _)
  have hDcont : Continuous D := by
    dsimp only [D]
    have hjoint : Continuous (Function.uncurry
        (fun (ξ : Euclidean d) (ω : sphere (0 : Euclidean d) 1) =>
          Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω)) := by
      unfold surfacePhase
      fun_prop
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := unitSurfaceMeasure d) hjoint isCompact_univ)
  have hF'meas : AEStronglyMeasurable (F' r) volume := by
    change AEStronglyMeasurable (fun ξ : Euclidean d =>
      (Real.fourierChar (inner ℝ ξ x) : ℂ) *
        (D ξ * 𝓕 (f : Euclidean d → ℂ) ξ)) volume
    exact (hchar_cont.mul (hDcont.mul (𝓕 f).continuous)).aestronglyMeasurable
  have hweighted : Integrable (fun ξ : Euclidean d => ‖ξ‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖)
      volume := by
    convert (𝓕 f).integrable_pow_mul volume 1 using 1
    funext ξ
    simp only [pow_one, SchwartzMap.fourier_coe]
  have hbound_int : Integrable (fun ξ : Euclidean d =>
      (2 * Real.pi * surfaceMass d) * (‖ξ‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖)) volume :=
    hweighted.const_mul _
  have hbound : ∀ᵐ ξ : Euclidean d ∂volume, ∀ s ∈ (Set.univ : Set ℝ),
      ‖F' s ξ‖ ≤ (2 * Real.pi * surfaceMass d) *
        (‖ξ‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖) := by
    filter_upwards with ξ
    intro s hs
    have hD : ‖∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d (s • (-ξ)) ω) * surfacePhase d (-ξ) ω
          ∂unitSurfaceMeasure d‖ ≤
        (2 * Real.pi * ‖-ξ‖) * (unitSurfaceMeasure d).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards with ω
      rw [norm_mul, norm_surfaceFourier_kernel]
      simpa using norm_surfacePhase_le d (-ξ) ω
    dsimp only [F']
    rw [norm_mul, hchar, one_mul, norm_mul]
    calc
      ‖∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (s • (-ξ)) ω) * surfacePhase d (-ξ) ω
            ∂unitSurfaceMeasure d‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖ ≤
          ((2 * Real.pi * ‖-ξ‖) * (unitSurfaceMeasure d).real Set.univ) *
            ‖𝓕 (f : Euclidean d → ℂ) ξ‖ :=
        mul_le_mul_of_nonneg_right hD (norm_nonneg _)
      _ = (2 * Real.pi * surfaceMass d) *
          (‖ξ‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖) := by
        simp only [surfaceMass, norm_neg]
        ring
  have hdiff : ∀ᵐ ξ : Euclidean d ∂volume, ∀ s ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun t => F t ξ) (F' s ξ) s := by
    filter_upwards with ξ
    intro s hs
    have hsurface := hasDerivAt_surfaceFourier_radial_at d (-ξ) s
    have hmul := (hsurface.mul_const (𝓕 (f : Euclidean d → ℂ) ξ)).const_mul
      (Real.fourierChar (inner ℝ ξ x) : ℂ)
    simpa only [F, F', D] using hmul
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Set.univ) (x₀ := r)
    (bound := fun ξ : Euclidean d =>
      (2 * Real.pi * surfaceMass d) * (‖ξ‖ * ‖𝓕 (f : Euclidean d → ℂ) ξ‖))
    Filter.univ_mem hFmeas hFint hF'meas hbound hbound_int hdiff).2

/-- The fixed-radius Fourier identity transfers the preceding derivative theorem
to spherical averages of Schwartz data. -/
theorem hasDerivAt_sphericalAverage_fourierInv_surfaceDerivative_schwartz
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) (r : ℝ) (x : Euclidean d) :
    HasDerivAt
      (fun s : ℝ => sphericalAverage d (f : Euclidean d → ℂ) s x)
      (𝓕⁻ (fun ξ : Euclidean d =>
        (∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω
            ∂unitSurfaceMeasure d) * 𝓕 (f : Euclidean d → ℂ) ξ) x)
      r := by
  rw [show (fun s : ℝ => sphericalAverage d (f : Euclidean d → ℂ) s x) =
      fun s => 𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (s • (-ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x by
        funext s
        rw [sphericalAverage_eq_fourierInv_surfaceMultiplier_schwartz f s]
        apply congrArg (fun g : Euclidean d → ℂ => 𝓕⁻ g x)
        funext ξ
        simp only [neg_smul, smul_neg]]
  exact hasDerivAt_fourierInv_surfaceMultiplier_radial_schwartz f r x

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Metric Set
open scoped FourierTransform

noncomputable section

/-- For Schwartz input, the radius derivative of a spherical average is the
literal inverse Fourier multiplier obtained by differentiating
`surfaceFourier` in the radius. -/
theorem hasDerivAt_sphericalAverage_fourierInv_deriv_surfaceMultiplier_schwartz
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) (r : ℝ) (x : Euclidean d) :
    HasDerivAt
      (fun s : ℝ => sphericalAverage d (f : Euclidean d → ℂ) s x)
      (𝓕⁻ (fun ξ : Euclidean d =>
        deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r *
          𝓕 (f : Euclidean d → ℂ) ξ) x)
      r := by
  have hmult :
      (fun ξ : Euclidean d =>
        (∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (r • (-ξ)) ω) * surfacePhase d (-ξ) ω
            ∂unitSurfaceMeasure d) * 𝓕 (f : Euclidean d → ℂ) ξ) =
      fun ξ : Euclidean d =>
        deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r *
          𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    rw [(hasDerivAt_surfaceFourier_radial_at d (-ξ) r).deriv]
  rw [← hmult]
  exact hasDerivAt_sphericalAverage_fourierInv_surfaceDerivative_schwartz f r x

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform
open scoped FourierTransform

noncomputable section

/-- The spherical average of inverse-Fourier Schwartz data has the literal
surface-multiplier formula with the original frequency-side Schwartz map. -/
theorem sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier
    {d : ℕ} (h : SchwartzMap (Euclidean d) ℂ) (r : ℝ) :
    sphericalAverage d ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r =
      𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * h ξ) := by
  have hfourier :
      𝓕 ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) =
        (h : Euclidean d → ℂ) := by
    rw [← SchwartzMap.fourier_coe, fourier_fourierInv_eq]
  rw [sphericalAverage_eq_fourierInv_surfaceMultiplier_schwartz (𝓕⁻ h) r,
    hfourier]

/-- The radius derivative of a spherical average of inverse-Fourier Schwartz
data is the literal inverse Fourier multiplier obtained by differentiating
the surface transform. -/
theorem hasDerivAt_sphericalAverage_fourierInv_schwartz_deriv_surfaceMultiplier
    {d : ℕ} (h : SchwartzMap (Euclidean d) ℂ) (r : ℝ) (x : Euclidean d) :
    HasDerivAt
      (fun s : ℝ =>
        sphericalAverage d ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) s x)
      (𝓕⁻ (fun ξ : Euclidean d =>
        deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r * h ξ) x)
      r := by
  have hfourier :
      𝓕 ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) =
        (h : Euclidean d → ℂ) := by
    rw [← SchwartzMap.fourier_coe, fourier_fourierInv_eq]
  simpa only [hfourier] using
    (hasDerivAt_sphericalAverage_fourierInv_deriv_surfaceMultiplier_schwartz
      (𝓕⁻ h) r x)

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Metric Set
open scoped BoundedContinuousFunction FourierTransform

noncomputable section

/-- The physical radius derivative of a spherical average of inverse-Fourier
Schwartz data equals its literal differentiated surface multiplier. -/
theorem sphericalAverage_radiusDerivative_fourierInv_schwartz
    {d : Nat} (h : SchwartzMap (Euclidean d) ℂ) (r : ℝ) (x : Euclidean d) :
    (∫ ω : sphere (0 : Euclidean d) 1,
      fderiv ℝ ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ)
        (x + r • (ω : Euclidean d)) (ω : Euclidean d)
        ∂unitSurfaceMeasure d) =
      𝓕⁻ (fun ξ : Euclidean d =>
        deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r * h ξ) x := by
  let p : SchwartzMap (Euclidean d) ℂ := 𝓕⁻ h
  let dp : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) p
  have hbound : ∀ y : Euclidean d, ‖fderiv ℝ (p : Euclidean d → ℂ) y‖ ≤
      ‖dp.toBoundedContinuousFunction‖ := by
    intro y
    calc
      ‖fderiv ℝ (p : Euclidean d → ℂ) y‖ = ‖dp y‖ := by
        rw [← SchwartzMap.fderivCLM_apply ℂ p y]
      _ = ‖dp.toBoundedContinuousFunction y‖ := rfl
      _ ≤ ‖dp.toBoundedContinuousFunction‖ :=
        BoundedContinuousFunction.norm_coe_le_norm
          (dp.toBoundedContinuousFunction :
            Euclidean d →ᵇ (Euclidean d →L[ℝ] ℂ)) y
  have hpderiv := hasDerivAt_sphericalAverage
    (p : Euclidean d → ℂ) (by simpa only [p] using (𝓕⁻ h).smooth (1 : ℕ∞))
    hbound x r
  have hfourier :=
    hasDerivAt_sphericalAverage_fourierInv_schwartz_deriv_surfaceMultiplier h r x
  change (∫ ω : sphere (0 : Euclidean d) 1,
      fderiv ℝ (p : Euclidean d → ℂ) (x + r • (ω : Euclidean d)) (ω : Euclidean d)
        ∂unitSurfaceMeasure d) = _
  rw [← hpderiv.deriv, hfourier.deriv]

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory intervalIntegral Metric Set

noncomputable section

/-- On a compact radius interval, the lower integral of the literal
spherical-average supremum is bounded by the `L¹` norm of the input and of
its spatial derivative. -/
theorem lintegral_iSup_ennreal_norm_sphericalAverage_le_local_radiusSobolev
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hf1 : Integrable f volume) (hfderiv1 : Integrable (fderiv ℝ f) volume)
    {C : ℝ} (hC : ∀ y, ‖fderiv ℝ f y‖ ≤ C) {a b : ℝ} (hab : a ≤ b) :
    (∫⁻ x : Euclidean d,
      ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) ≤
      ENNReal.ofReal
        (surfaceMass d *
          ((∫ x : Euclidean d, ‖f x‖) +
            (b - a) * (∫ x : Euclidean d, ‖fderiv ℝ f x‖))) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let D : ℝ → Euclidean d → ℂ := fun t x =>
    ∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (x + t • (ω : Euclidean d)) (ω : Euclidean d)
        ∂unitSurfaceMeasure d
  let M : ℝ := surfaceMass d * (∫ x : Euclidean d, ‖fderiv ℝ f x‖)
  have hfcont : Continuous f := hf.continuous
  have hfderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by norm_num)
  have hDjoint : Continuous (Function.uncurry D) := by
    change Continuous (fun p : ℝ × Euclidean d =>
      ∫ ω : sphere (0 : Euclidean d) 1,
        fderiv ℝ f (p.2 + p.1 • (ω : Euclidean d)) (ω : Euclidean d)
          ∂unitSurfaceMeasure d)
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := unitSurfaceMeasure d)
        ((hfderiv_cont.comp
          ((continuous_snd.comp continuous_fst).add
            ((continuous_fst.comp continuous_fst).smul
              (continuous_subtype_val.comp continuous_snd)))).clm_apply
            (continuous_subtype_val.comp continuous_snd))
        isCompact_univ)
  have hDmeas : AEStronglyMeasurable (Function.uncurry D) (ν.prod volume) :=
    hDjoint.aestronglyMeasurable
  have hDslice (t : ℝ) : Integrable (D t) volume := by
    simpa only [D] using
      integrable_sphericalAverage_radiusDerivative f hf hfderiv1 t
  have hDnorm_outer : Integrable (fun t : ℝ => ∫ x : Euclidean d, ‖D t x‖) ν := by
    refine Integrable.mono' (g := fun _ : ℝ => M) (integrable_const M) ?_ ?_
    · exact hDmeas.norm.integral_prod_right'
    · filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · simpa only [M] using
          (integral_norm_sphericalAverage_radiusDerivative_le_surfaceMass_mul
            f hf hfderiv1 t)
      · exact integral_nonneg fun x => norm_nonneg _
  have hDprod : Integrable (Function.uncurry D) (ν.prod volume) := by
    refine (integrable_prod_iff hDmeas).2 ?_
    constructor
    · filter_upwards with t
      exact hDslice t
    · exact hDnorm_outer
  have hG : Integrable (fun x : Euclidean d => ∫ t in a..b, ‖D t x‖) volume := by
    have hGν : Integrable (fun x : Euclidean d => ∫ t, ‖D t x‖ ∂ν) volume :=
      hDprod.integral_norm_prod_right
    have heq :
        (fun x : Euclidean d => ∫ t in a..b, ‖D t x‖) =
          fun x => ∫ t, ‖D t x‖ ∂ν := by
      funext x
      simp only [ν]
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    rw [heq]
    exact hGν
  have hA : Integrable (sphericalAverage d f a) volume :=
    integrable_sphericalAverage f hfcont hf1 a
  have hright : Integrable (fun x : Euclidean d =>
      ‖sphericalAverage d f a x‖ + ∫ t in a..b, ‖D t x‖) volume :=
    hA.norm.add hG
  have hDcont (x : Euclidean d) : Continuous (fun t => D t x) :=
    hDjoint.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x))
  have hderiv (t : ℝ) (x : Euclidean d) :
      HasDerivAt (fun s => sphericalAverage d f s x) (D t x) t := by
    simpa only [D] using hasDerivAt_sphericalAverage f hf hC x t
  have hpoint (x : Euclidean d) (r : Icc a b) :
      ‖sphericalAverage d f r.1 x‖ ≤
        ‖sphericalAverage d f a x‖ + ∫ t in a..b, ‖D t x‖ := by
    exact norm_le_norm_add_intervalIntegral_norm_of_hasDerivAt
      r.2 (hDcont x) (fun t => hderiv t x)
  have hright_nonneg (x : Euclidean d) :
      0 ≤ ‖sphericalAverage d f a x‖ + ∫ t in a..b, ‖D t x‖ := by
    exact add_nonneg (norm_nonneg _)
      (intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _)
  have hsup (x : Euclidean d) :
      (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) ≤
        ENNReal.ofReal
          (‖sphericalAverage d f a x‖ + ∫ t in a..b, ‖D t x‖) := by
    apply iSup_le
    intro r
    exact ENNReal.ofReal_le_ofReal (hpoint x r)
  have hswap :
      (∫ x : Euclidean d, ∫ t in a..b, ‖D t x‖) =
        ∫ t in a..b, ∫ x : Euclidean d, ‖D t x‖ := by
    have hDuIoc : Integrable (Function.uncurry (fun t (x : Euclidean d) => ‖D t x‖))
        ((volume.restrict (uIoc a b)).prod volume) := by
      change Integrable (fun p : ℝ × Euclidean d => ‖D p.1 p.2‖)
        ((volume.restrict (uIoc a b)).prod volume)
      rw [uIoc_of_le hab]
      rw [restrict_Ioc_eq_restrict_Icc]
      exact hDprod.norm
    exact (intervalIntegral_integral_swap
      (f := fun t (x : Euclidean d) => ‖D t x‖) hDuIoc).symm
  have hderiv_interval :
      (∫ t in a..b, ∫ x : Euclidean d, ‖D t x‖) ≤
        (b - a) * M := by
    have hDinterval : IntervalIntegrable (fun t : ℝ => ∫ x : Euclidean d, ‖D t x‖)
        volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      change Integrable (fun t : ℝ => ∫ x : Euclidean d, ‖D t x‖) ν
      exact hDprod.integral_norm_prod_left
    have hconst : IntervalIntegrable (fun _ : ℝ =>
        M) volume a b :=
      intervalIntegrable_const
    calc
      (∫ t in a..b, ∫ x : Euclidean d, ‖D t x‖) ≤
          ∫ t in a..b, M := by
        apply intervalIntegral.integral_mono_on hab hDinterval hconst
        intro t ht
        exact integral_norm_sphericalAverage_radiusDerivative_le_surfaceMass_mul
          f hf hfderiv1 t
      _ = (b - a) * M := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
  have hreal :
      (∫ x : Euclidean d,
        ‖sphericalAverage d f a x‖ + ∫ t in a..b, ‖D t x‖) ≤
        surfaceMass d *
          ((∫ x : Euclidean d, ‖f x‖) +
            (b - a) * (∫ x : Euclidean d, ‖fderiv ℝ f x‖)) := by
    calc
      (∫ x : Euclidean d,
        ‖sphericalAverage d f a x‖ + ∫ t in a..b, ‖D t x‖) =
          (∫ x : Euclidean d, ‖sphericalAverage d f a x‖) +
            ∫ x : Euclidean d, ∫ t in a..b, ‖D t x‖ := by
          rw [integral_add hA.norm hG]
      _ = (∫ x : Euclidean d, ‖sphericalAverage d f a x‖) +
            ∫ t in a..b, ∫ x : Euclidean d, ‖D t x‖ := by rw [hswap]
      _ ≤ surfaceMass d * (∫ x : Euclidean d, ‖f x‖) + (b - a) * M := by
          exact add_le_add
            (integral_norm_sphericalAverage_le_surfaceMass_mul f hfcont hf1 a)
            hderiv_interval
      _ = surfaceMass d *
          ((∫ x : Euclidean d, ‖f x‖) +
            (b - a) * (∫ x : Euclidean d, ‖fderiv ℝ f x‖)) := by
              dsimp only [M]
              ring
  calc
    (∫⁻ x : Euclidean d,
      ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) ≤
        ∫⁻ x : Euclidean d, ENNReal.ofReal
          (‖sphericalAverage d f a x‖ + ∫ t in a..b, ‖D t x‖) := by
      exact lintegral_mono hsup
    _ = ENNReal.ofReal (∫ x : Euclidean d,
        ‖sphericalAverage d f a x‖ + ∫ t in a..b, ‖D t x‖) := by
      rw [ofReal_integral_eq_lintegral_ofReal hright]
      filter_upwards with x
      exact hright_nonneg x
    _ ≤ ENNReal.ofReal
        (surfaceMass d *
          ((∫ x : Euclidean d, ‖f x‖) +
            (b - a) * (∫ x : Euclidean d, ‖fderiv ℝ f x‖))) :=
      ENNReal.ofReal_le_ofReal hreal

/-- The preceding compact-radius estimate also gives an actual `L¹` member:
the real-valued compact-radius maximal norm is integrable with the displayed
bound. -/
theorem memLp_one_iSup_ennreal_norm_sphericalAverage_local_radiusSobolev
    {d : ℕ} (f : Euclidean d → ℂ) (hf : ContDiff ℝ 1 f)
    (hf1 : Integrable f volume) (hfderiv1 : Integrable (fderiv ℝ f) volume)
    {C : ℝ} (hC : ∀ y, ‖fderiv ℝ f y‖ ≤ C) {a b : ℝ} (hab : a ≤ b) :
    MemLp
      (fun x : Euclidean d =>
        (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖).toReal)
      1 volume ∧
    (∫ x : Euclidean d,
      ‖(⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖).toReal‖) ≤
      surfaceMass d *
        ((∫ x : Euclidean d, ‖f x‖) +
          (b - a) * (∫ x : Euclidean d, ‖fderiv ℝ f x‖)) := by
  let Q : Euclidean d → ENNReal := fun x =>
    ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖
  let K : ℝ := surfaceMass d *
    ((∫ x : Euclidean d, ‖f x‖) +
      (b - a) * (∫ x : Euclidean d, ‖fderiv ℝ f x‖))
  have hQmeas : Measurable Q := by
    simpa only [Q] using measurable_iSup_ennreal_norm_sphericalAverage f hf.continuous
  have hQlin : (∫⁻ x : Euclidean d, Q x) ≤ ENNReal.ofReal K := by
    simpa only [Q, K] using
      lintegral_iSup_ennreal_norm_sphericalAverage_le_local_radiusSobolev
        f hf hf1 hfderiv1 hC hab
  have hK : 0 ≤ K := by
    dsimp only [K]
    apply mul_nonneg measureReal_nonneg
    apply add_nonneg
    · exact integral_nonneg fun _ => norm_nonneg _
    · apply mul_nonneg
      · exact sub_nonneg.mpr hab
      · exact integral_nonneg fun _ => norm_nonneg _
  have hQfinite : (∫⁻ x : Euclidean d, Q x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQlin
  have hQint : Integrable (fun x : Euclidean d => (Q x).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hQmeas.aemeasurable hQfinite
  have hQtop : ∀ᵐ x : Euclidean d ∂volume, Q x < ⊤ :=
    ae_lt_top hQmeas hQfinite
  have hQintegral :
      (∫ x : Euclidean d, (Q x).toReal) = (∫⁻ x : Euclidean d, Q x).toReal :=
    integral_toReal hQmeas.aemeasurable hQtop
  have hQbound : (∫ x : Euclidean d, (Q x).toReal) ≤ K := by
    rw [hQintegral]
    rw [← ENNReal.toReal_ofReal hK]
    exact (ENNReal.toReal_le_toReal hQfinite ENNReal.ofReal_ne_top).2 hQlin
  constructor
  · rw [memLp_one_iff_integrable]
    simpa only [Q] using hQint
  · change (∫ x : Euclidean d, ‖(Q x).toReal‖) ≤ K
    rw [show (fun x : Euclidean d => ‖(Q x).toReal‖) =
        fun x => (Q x).toReal by
          funext x
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]]
    exact hQbound

end

end LeanSpherical.HarmonicAnalysis
