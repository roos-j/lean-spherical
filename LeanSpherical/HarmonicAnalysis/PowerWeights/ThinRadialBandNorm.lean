/- 
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.GlobalUnweightedEndpoint
import LeanSpherical.HarmonicAnalysis.PowerWeights.ThinRadialBufferedWindows

/-!
# Local band norm conversion

A literal shell moment has an output measure restricted to the central
ball, while its input moment remains global. This direct conversion records
exactly that two-measure situation.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Convert a finite raw moment on an output measure into the corresponding
raw ENNReal local norm estimate, retaining a possibly different global
input measure. -/
theorem memLp_and_eLpNorm_ennreal_of_toReal_lintegral_rpow_le_of_input_measure
    {X : Type*} [MeasurableSpace X] (muOut muIn : Measure X)
    (M : X -> ENNReal) (hMmeas : AEMeasurable M muOut)
    (hMfinite : ∀ᵐ x ∂muOut, M x ≠ ⊤)
    {p : Real} (hp : 0 < p) {A : ENNReal} (hAtop : A ≠ ⊤)
    (f : X -> Complex) (hf : MemLp f (ENNReal.ofReal p) muIn)
    (hbound :
      (∫⁻ x, ENNReal.ofReal ((M x).toReal ^ p) ∂muOut) ≤
        A * ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂muIn) :
    MemLp M (ENNReal.ofReal p) muOut ∧
      eLpNorm M (ENNReal.ofReal p) muOut ≤
        A ^ p⁻¹ *
          eLpNorm f (ENNReal.ofReal p) muIn := by
  let T : X -> Real := fun x => (M x).toReal
  let I : ENNReal := ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂muIn
  let J : ENNReal := ∫⁻ x, ENNReal.ofReal ((T x) ^ p) ∂muOut
  have hp_nonneg : 0 ≤ p := hp.le
  have hp_inv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_nonneg
  have hIlt : I < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := muIn) (f := f) (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top hf.eLpNorm_lt_top
    simpa only [I, ENNReal.toReal_ofReal hp_nonneg, ofReal_norm] using h
  have hJle : J ≤ A * I := by
    simpa only [J, I, T] using hbound
  have hJlt : J < ⊤ :=
    hJle.trans_lt (ENNReal.mul_lt_top hAtop.lt_top hIlt)
  have hTmeas : AEMeasurable T muOut := by
    change AEMeasurable (ENNReal.toReal ∘ M) muOut
    exact ENNReal.measurable_toReal.comp_aemeasurable hMmeas
  have hTnonneg (x : X) : 0 ≤ T x := ENNReal.toReal_nonneg
  have hTmem : MemLp T (ENNReal.ofReal p) muOut :=
    memLp_of_lintegral_ofReal_rpow_lt_top T hTmeas hTnonneg hp hJlt
  have hInorm : eLpNorm f (ENNReal.ofReal p) muIn = I ^ p⁻¹ := by
    dsimp only [I]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal hp_nonneg, ofReal_norm]
    rw [one_div]
  have hTnorm : eLpNorm T (ENNReal.ofReal p) muOut ≤
      A ^ p⁻¹ * eLpNorm f (ENNReal.ofReal p) muIn := by
    calc
      eLpNorm T (ENNReal.ofReal p) muOut ≤ (A * I) ^ p⁻¹ :=
        eLpNorm_real_nonneg_le_of_lintegral_ofReal_rpow_le muOut T hp hTnonneg hJle
      _ = A ^ p⁻¹ * eLpNorm f (ENNReal.ofReal p) muIn := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp_inv_nonneg, <- hInorm]
  have hpoint : ∀ᵐ x ∂muOut,
      ‖M x‖ₑ ≤
        ((1 : NNReal) : ENNReal) * ‖T x‖ₑ := by
    filter_upwards [hMfinite] with x hx
    calc
      ‖M x‖ₑ = M x := enorm_eq_self _
      _ = ENNReal.ofReal (T x) := (ENNReal.ofReal_toReal hx).symm
      _ = ‖T x‖ₑ :=
        (Real.enorm_of_nonneg (hTnonneg x)).symm
      _ ≤ ((1 : NNReal) : ENNReal) * ‖T x‖ₑ := by norm_num
  have hMmem : MemLp M (ENNReal.ofReal p) muOut :=
    MemLp.of_enorm_le_mul hTmem hMmeas.aestronglyMeasurable hpoint
  have hMnorm : eLpNorm M (ENNReal.ofReal p) muOut ≤
      eLpNorm T (ENNReal.ofReal p) muOut := by
    calc
      eLpNorm M (ENNReal.ofReal p) muOut ≤
          ((1 : NNReal) : ENNReal) * eLpNorm T (ENNReal.ofReal p) muOut :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' (ENNReal.ofReal p)
          hTmem.aestronglyMeasurable hpoint
      _ = eLpNorm T (ENNReal.ofReal p) muOut := by norm_num
  exact ⟨hMmem, hMnorm.trans hTnorm⟩

end

end LeanSpherical.HarmonicAnalysis
