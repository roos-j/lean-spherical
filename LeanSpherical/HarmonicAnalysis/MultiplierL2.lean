/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.Fourier.LpSpace

/-!
# The `L²` Fourier-multiplier estimate

This is the Plancherel step used for every dyadically localized spherical
multiplier.  It is stated directly for a bounded measurable multiplier; no
regularity hypothesis is needed at this stage.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform
open scoped FourierTransform

noncomputable section

/-- A bounded measurable multiplier, followed by inverse Fourier transform,
is bounded on `L²` by its pointwise bound. -/
theorem norm_fourierInv_bounded_multiplier_fourier_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (m : E → ℂ) (hm : AEStronglyMeasurable m volume) (C : ℝ)
    (hC : 0 ≤ C) (hmC : ∀ ξ, ‖m ξ‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure E)) :
    ‖𝓕⁻ (((memLp_top_of_bound hm C (Filter.Eventually.of_forall hmC)).toLp m :
      Lp ℂ ⊤ (volume : Measure E)) • (𝓕 f : Lp ℂ 2 (volume : Measure E)) :
      Lp ℂ 2 (volume : Measure E))‖ ≤ C * ‖f‖ := by
  let mLp : Lp ℂ ⊤ (volume : Measure E) :=
    (memLp_top_of_bound hm C (Filter.Eventually.of_forall hmC)).toLp m
  have hmLp_ae : (mLp : E → ℂ) =ᵐ[volume] m := by
    exact MemLp.coeFn_toLp _
  have hmLp : ‖mLp‖ ≤ C := by
    rw [Lp.norm_def, eLpNorm_congr_ae hmLp_ae, eLpNorm_exponent_top]
    exact ENNReal.toReal_le_of_le_ofReal hC
      (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hmC))
  change ‖𝓕⁻ (mLp • 𝓕 f)‖ ≤ C * ‖f‖
  calc
    ‖𝓕⁻ (mLp • 𝓕 f)‖ = ‖𝓕 (𝓕⁻ (mLp • 𝓕 f))‖ :=
      (Lp.norm_fourier_eq _).symm
    _ = ‖mLp • 𝓕 f‖ := by rw [FourierTransform.fourier_fourierInv_eq]
    _ ≤ ‖mLp‖ * ‖𝓕 f‖ := Lp.norm_smul_le _ _
    _ = ‖mLp‖ * ‖f‖ := by rw [Lp.norm_fourier_eq]
    _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right hmLp (norm_nonneg _)

end

end LeanSpherical.HarmonicAnalysis
