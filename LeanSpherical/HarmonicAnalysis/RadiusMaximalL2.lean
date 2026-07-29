/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.RadiusMaximalMeasurable
import LeanSpherical.HarmonicAnalysis.RadiusSobolevL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# An integrated compact-radius Sobolev maximal estimate

The pointwise one-dimensional radius-Sobolev inequality controls the literal
supremum over a compact interval.  This file integrates that estimate for a
jointly continuous family, using Fubini for the derivative term.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory intervalIntegral Set

noncomputable section

/-- A measurable finite lower-integral bound for a nonnegative extended-real
square function produces its real square-root as an `L²` function. -/
theorem memLp_two_toReal_sqrt_of_measurable_lintegral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (Q : α → ENNReal) (hQmeas : Measurable Q) {K : ℝ} (hK : 0 ≤ K)
    (hQlin : (∫⁻ x, Q x ∂μ) ≤ ENNReal.ofReal K) :
    MemLp (fun x => (Q x).toReal.sqrt) 2 μ ∧
      (∫ x, ‖(Q x).toReal.sqrt‖ ^ 2 ∂μ) ≤ K := by
  let G : α → ℝ := fun x => (Q x).toReal.sqrt
  have hQfinite : (∫⁻ x, Q x ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQlin
  have hQint : Integrable (fun x => (Q x).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hQmeas.aemeasurable hQfinite
  have hGmeas : AEStronglyMeasurable G μ := by
    exact (Real.continuous_sqrt.measurable.comp hQmeas.ennreal_toReal).aestronglyMeasurable
  have hGsq (x : α) : G x ^ 2 = (Q x).toReal := by
    dsimp only [G]
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hGmem : MemLp G 2 μ := by
    apply (memLp_two_iff_integrable_sq hGmeas).2
    rw [show (fun x : α => G x ^ 2) =
        fun x => (Q x).toReal by
          funext x
          exact hGsq x]
    exact hQint
  have hGnonneg (x : α) : 0 ≤ G x := by
    dsimp only [G]
    exact Real.sqrt_nonneg _
  have hQae : ∀ᵐ x ∂μ, Q x < ⊤ :=
    ae_lt_top hQmeas hQfinite
  have hGbound : (∫ x, ‖G x‖ ^ 2 ∂μ) ≤ K := by
    calc
      (∫ x, ‖G x‖ ^ 2 ∂μ) = ∫ x, G x ^ 2 ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [Real.norm_of_nonneg (hGnonneg x)]
      _ = ∫ x, (Q x).toReal ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        exact hGsq x
      _ = (∫⁻ x, Q x ∂μ).toReal :=
        integral_toReal hQmeas.aemeasurable hQae
      _ ≤ (ENNReal.ofReal K).toReal :=
        (ENNReal.toReal_le_toReal hQfinite ENNReal.ofReal_ne_top).2 hQlin
      _ = K := ENNReal.toReal_ofReal hK
  exact ⟨hGmem, hGbound⟩

/-- On a nonempty compact radius interval, the ordinary pointwise radius
maximum is the square root of the squared radius maximum.  Compactness is used
to realize both suprema at the same radius, so no interchange of `toReal` with
an unbounded supremum is needed. -/
theorem toReal_iSup_ennreal_norm_eq_sqrt_toReal_iSup_ennreal_norm_sq_of_continuous
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    {F : ℝ → X → E} {a b : ℝ}
    (hab : a ≤ b)
    (hF : Continuous (Function.uncurry F))
    (x : X) :
    (⨆ r : Icc a b, ENNReal.ofReal ‖F r.1 x‖).toReal =
      ((⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)).toReal).sqrt := by
  have hnorm : Continuous (fun r : ℝ => ‖F r x‖) := by
    exact (hF.comp (continuous_id.prodMk
      (continuous_const : Continuous fun _ : ℝ => x))).norm
  obtain ⟨r₀, hr₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hab) hnorm.continuousOn
  have hsup :
      (⨆ r : Icc a b, ENNReal.ofReal ‖F r.1 x‖) =
        ENNReal.ofReal ‖F r₀ x‖ := by
    apply le_antisymm
    · apply iSup_le
      intro r
      exact ENNReal.ofReal_le_ofReal (hmax r.2)
    · exact le_iSup (fun r : Icc a b => ENNReal.ofReal ‖F r.1 x‖) ⟨r₀, hr₀⟩
  have hsup_sq :
      (⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) =
        ENNReal.ofReal (‖F r₀ x‖ ^ 2) := by
    apply le_antisymm
    · apply iSup_le
      intro r
      exact ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) (hmax r.2) 2)
    · exact le_iSup (fun r : Icc a b => ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ⟨r₀, hr₀⟩
  rw [hsup, hsup_sq, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- A square-maximal `L²` estimate for a jointly continuous compact-radius
family is also an `L²` estimate for its ordinary pointwise maximal norm.
The previous compact-attainment theorem identifies the two output functions
exactly. -/
theorem memLp_two_iSup_ennreal_norm_of_memLp_sqrt_iSup_ennreal_norm_sq
    {d : ℕ} {F : ℝ → Euclidean d → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hF : Continuous (Function.uncurry F)) {K : ℝ}
    (hGmem : MemLp
      (fun x : Euclidean d =>
        ((⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)).toReal).sqrt)
      2 volume)
    (hGbound : (∫ x : Euclidean d,
      ‖((⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)).toReal).sqrt‖ ^ 2) ≤ K) :
    MemLp
      (fun x : Euclidean d =>
        (⨆ r : Icc a b, ENNReal.ofReal ‖F r.1 x‖).toReal)
      2 volume ∧
    (∫ x : Euclidean d,
      ‖(⨆ r : Icc a b, ENNReal.ofReal ‖F r.1 x‖).toReal‖ ^ 2) ≤ K := by
  have heq :
      (fun x : Euclidean d =>
        (⨆ r : Icc a b, ENNReal.ofReal ‖F r.1 x‖).toReal) =
      fun x : Euclidean d =>
        ((⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)).toReal).sqrt := by
    funext x
    exact toReal_iSup_ennreal_norm_eq_sqrt_toReal_iSup_ennreal_norm_sq_of_continuous
      hab hF x
  constructor
  · rw [heq]
    exact hGmem
  · have hsq :
        (fun x : Euclidean d =>
          ‖(⨆ r : Icc a b, ENNReal.ofReal ‖F r.1 x‖).toReal‖ ^ 2) =
        fun x : Euclidean d =>
          ‖((⨆ r : Icc a b,
            ENNReal.ofReal (‖F r.1 x‖ ^ 2)).toReal).sqrt‖ ^ 2 := by
        funext x
        rw [congrFun heq x]
    rw [show (∫ x : Euclidean d,
      ‖(⨆ r : Icc a b, ENNReal.ofReal ‖F r.1 x‖).toReal‖ ^ 2) =
      ∫ x : Euclidean d,
        ‖((⨆ r : Icc a b,
          ENNReal.ofReal (‖F r.1 x‖ ^ 2)).toReal).sqrt‖ ^ 2 by
      exact congrArg (fun H : Euclidean d → ℝ => ∫ x, H x) hsq]
    exact hGbound

/-- A jointly continuous, radius-differentiable family has a measurable
compact-radius square maximal function, with its lower integral controlled by
the square integral at the left endpoint and the integrated square of the
radius derivative. -/
theorem measurable_and_lintegral_iSup_ennreal_norm_sq_le_radiusSobolev_of_hasDerivAt
    {d : ℕ} {F F' : ℝ → Euclidean d → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hderiv : ∀ t x, HasDerivAt (fun s => F s x) (F' t x) t)
    (hFa : Integrable (fun x => ‖F a x‖ ^ 2) volume)
    (hF'prod : Integrable (fun p : ℝ × Euclidean d => ‖F' p.1 p.2‖ ^ 2)
      ((volume.restrict (Icc a b)).prod volume)) :
    Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ∧
      (∫⁻ x : Euclidean d,
        ⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ≤
        ENNReal.ofReal
          (2 * (∫ x : Euclidean d, ‖F a x‖ ^ 2) +
            2 * (b - a) * ∫ t in a..b, ∫ x : Euclidean d, ‖F' t x‖ ^ 2) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
  have hmaxmeas : Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) := by
    exact measurable_iSup_ennreal_norm_sq_of_continuous
      (F := Function.uncurry F) hF
  refine ⟨hmaxmeas, ?_⟩
  have hderiv_interval_integrable : Integrable (fun x : Euclidean d =>
      ∫ t in a..b, ‖F' t x‖ ^ 2) volume := by
    have hprod_right : Integrable (fun x : Euclidean d =>
        ∫ t : ℝ, ‖F' t x‖ ^ 2 ∂ν) volume := by
      simpa only [ν] using hF'prod.integral_prod_right
    have heq : (fun x : Euclidean d => ∫ t in a..b, ‖F' t x‖ ^ 2) =
        fun x : Euclidean d => ∫ t : ℝ, ‖F' t x‖ ^ 2 ∂ν := by
      funext x
      simp only [ν]
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    rw [heq]
    exact hprod_right
  have hmajorant_integrable : Integrable (fun x : Euclidean d =>
      2 * ‖F a x‖ ^ 2 +
        2 * (b - a) * (∫ t in a..b, ‖F' t x‖ ^ 2)) volume := by
    exact (hFa.const_mul (2 : ℝ)).add
      (hderiv_interval_integrable.const_mul (2 * (b - a)))
  have hmajorant_nonneg (x : Euclidean d) :
      0 ≤ 2 * ‖F a x‖ ^ 2 +
        2 * (b - a) * (∫ t in a..b, ‖F' t x‖ ^ 2) := by
    apply add_nonneg
    · positivity
    · exact mul_nonneg (mul_nonneg (by norm_num) hlength)
        (intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _)
  have hpoint (x : Euclidean d) :
      (⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ≤
        ENNReal.ofReal
          (2 * ‖F a x‖ ^ 2 +
            2 * (b - a) * (∫ t in a..b, ‖F' t x‖ ^ 2)) := by
    exact iSup_ennreal_norm_sq_le_radiusSobolev
      (a := a) (b := b)
      (f := fun t => F t x) (f' := fun t => F' t x)
      (hF'.comp (continuous_id.prodMk
        (continuous_const : Continuous fun _ : ℝ => x)))
      (fun t => hderiv t x)
  calc
    (∫⁻ x : Euclidean d,
      ⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ≤
        ∫⁻ x : Euclidean d, ENNReal.ofReal
          (2 * ‖F a x‖ ^ 2 +
            2 * (b - a) * (∫ t in a..b, ‖F' t x‖ ^ 2)) := by
      exact lintegral_mono fun x => hpoint x
    _ = ENNReal.ofReal (∫ x : Euclidean d,
      2 * ‖F a x‖ ^ 2 +
        2 * (b - a) * (∫ t in a..b, ‖F' t x‖ ^ 2)) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hmajorant_integrable
        (Filter.Eventually.of_forall hmajorant_nonneg)
    _ = ENNReal.ofReal
        (2 * (∫ x : Euclidean d, ‖F a x‖ ^ 2) +
          2 * (b - a) * ∫ t in a..b, ∫ x : Euclidean d, ‖F' t x‖ ^ 2) := by
      congr 1
      rw [MeasureTheory.integral_add
        (hFa.const_mul (2 : ℝ))
        (hderiv_interval_integrable.const_mul (2 * (b - a))),
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      have hswap :
          (∫ x : Euclidean d, ∫ t in a..b, ‖F' t x‖ ^ 2) =
            ∫ t in a..b, ∫ x : Euclidean d, ‖F' t x‖ ^ 2 := by
        have hprod_uIoc : Integrable
            (fun p : ℝ × Euclidean d => ‖F' p.1 p.2‖ ^ 2)
            ((volume.restrict (uIoc a b)).prod volume) := by
          rw [uIoc_of_le hab]
          rw [restrict_Ioc_eq_restrict_Icc]
          exact hF'prod
        exact (intervalIntegral_integral_swap
          (f := fun t (x : Euclidean d) => ‖F' t x‖ ^ 2) hprod_uIoc).symm
      rw [hswap]

end

end LeanSpherical.HarmonicAnalysis
