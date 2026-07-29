/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SphericalAverageDerivative
import LeanSpherical.HarmonicAnalysis.SphericalAverageContinuity

/-!
# A compact-radius `L¹` estimate for spherical averages

The elementary radius fundamental theorem of calculus, combined with the
fixed-radius `L¹` bounds for both the average and its radius derivative,
controls the literal compact-radius supremum for `C¹` inputs.  This is a
local Sobolev estimate, not the derivative-free spherical maximal theorem.
-/

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
