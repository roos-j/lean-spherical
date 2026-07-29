/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.RadiusMaximalMeasurable
import LeanSpherical.HarmonicAnalysis.RadiusSobolevL2

/-!
# An integrated product radius-Sobolev maximal estimate

The product form of the radius-Sobolev inequality retains the factor
`‖F‖ * ‖F'‖`.  Integrating it by Fubini preserves the decay information that
would be lost by first estimating the two factors separately.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory intervalIntegral Set

noncomputable section

/-- A jointly continuous, radius-differentiable family has a measurable
compact-radius square maximal function.  Its lower integral is bounded by
the squared left-endpoint slice plus the integrated product of the family and
its radius derivative. -/
theorem measurable_and_lintegral_iSup_ennreal_norm_sq_le_radiusSobolev_product_of_hasDerivAt
    {d : Nat} {F F' : ℝ → Euclidean d → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hderiv : ∀ t x, HasDerivAt (fun s => F s x) (F' t x) t)
    (hFa : Integrable (fun x => ‖F a x‖ ^ 2) volume)
    (hFprod : Integrable (fun p : ℝ × Euclidean d =>
      ‖F p.1 p.2‖ * ‖F' p.1 p.2‖)
      ((volume.restrict (Icc a b)).prod volume)) :
    Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ∧
      (∫⁻ x : Euclidean d,
        ⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ≤
        ENNReal.ofReal
          ((∫ x : Euclidean d, ‖F a x‖ ^ 2) +
            2 * ∫ t in a..b, ∫ x : Euclidean d, ‖F t x‖ * ‖F' t x‖) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  have hmaxmeas : Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) := by
    exact measurable_iSup_ennreal_norm_sq_of_continuous
      (F := Function.uncurry F) hF
  refine ⟨hmaxmeas, ?_⟩
  have hprod_interval_integrable : Integrable (fun x : Euclidean d =>
      ∫ t in a..b, ‖F t x‖ * ‖F' t x‖) volume := by
    have hprod_right : Integrable (fun x : Euclidean d =>
        ∫ t : ℝ, ‖F t x‖ * ‖F' t x‖ ∂ν) volume := by
      simpa only [ν] using hFprod.integral_prod_right
    have heq : (fun x : Euclidean d => ∫ t in a..b, ‖F t x‖ * ‖F' t x‖) =
        fun x : Euclidean d => ∫ t : ℝ, ‖F t x‖ * ‖F' t x‖ ∂ν := by
      funext x
      simp only [ν]
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    rw [heq]
    exact hprod_right
  have hmajorant_integrable : Integrable (fun x : Euclidean d =>
      ‖F a x‖ ^ 2 +
        2 * (∫ t in a..b, ‖F t x‖ * ‖F' t x‖)) volume := by
    exact hFa.add (hprod_interval_integrable.const_mul (2 : ℝ))
  have hmajorant_nonneg (x : Euclidean d) :
      0 ≤ ‖F a x‖ ^ 2 +
        2 * (∫ t in a..b, ‖F t x‖ * ‖F' t x‖) := by
    apply add_nonneg
    · exact sq_nonneg _
    · exact mul_nonneg (by norm_num)
        (intervalIntegral.integral_nonneg hab fun _ _ =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hpoint (x : Euclidean d) :
      (⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ≤
        ENNReal.ofReal
          (‖F a x‖ ^ 2 +
            2 * (∫ t in a..b, ‖F t x‖ * ‖F' t x‖)) := by
    exact iSup_ennreal_norm_sq_le_radiusSobolev_product
      (a := a) (b := b)
      (f := fun t => F t x) (f' := fun t => F' t x)
      (hF'.comp (continuous_id.prodMk
        (continuous_const : Continuous fun _ : ℝ => x)))
      (fun t => hderiv t x)
  calc
    (∫⁻ x : Euclidean d,
      ⨆ r : Icc a b, ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ≤
        ∫⁻ x : Euclidean d, ENNReal.ofReal
          (‖F a x‖ ^ 2 +
            2 * (∫ t in a..b, ‖F t x‖ * ‖F' t x‖)) := by
      exact lintegral_mono fun x => hpoint x
    _ = ENNReal.ofReal (∫ x : Euclidean d,
      ‖F a x‖ ^ 2 +
        2 * (∫ t in a..b, ‖F t x‖ * ‖F' t x‖)) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hmajorant_integrable
        (Filter.Eventually.of_forall hmajorant_nonneg)
    _ = ENNReal.ofReal
        ((∫ x : Euclidean d, ‖F a x‖ ^ 2) +
          2 * ∫ t in a..b, ∫ x : Euclidean d, ‖F t x‖ * ‖F' t x‖) := by
      congr 1
      rw [MeasureTheory.integral_add hFa
        (hprod_interval_integrable.const_mul (2 : ℝ)),
        MeasureTheory.integral_const_mul]
      have hswap :
          (∫ x : Euclidean d, ∫ t in a..b, ‖F t x‖ * ‖F' t x‖) =
            ∫ t in a..b, ∫ x : Euclidean d, ‖F t x‖ * ‖F' t x‖ := by
        have hprod_uIoc : Integrable
            (fun p : ℝ × Euclidean d => ‖F p.1 p.2‖ * ‖F' p.1 p.2‖)
            ((volume.restrict (uIoc a b)).prod volume) := by
          rw [uIoc_of_le hab]
          rw [restrict_Ioc_eq_restrict_Icc]
          exact hFprod
        exact (intervalIntegral_integral_swap
          (f := fun t (x : Euclidean d) => ‖F t x‖ * ‖F' t x‖) hprod_uIoc).symm
      rw [hswap]

end

end LeanSpherical.HarmonicAnalysis
