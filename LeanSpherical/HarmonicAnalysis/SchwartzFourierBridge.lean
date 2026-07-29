/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.Fourier.LpSpace

/-!
# The `L²` inverse Fourier transform on Schwartz functions

For a Schwartz frequency-side function, Mathlib's `L²` inverse Fourier
transform has the literal inverse Fourier integral as a continuous
representative. This is deliberately restricted to Schwartz data: it does
not identify the `L²` transform of a hard frequency cutoff with an integral.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform
open scoped FourierTransform

noncomputable section

/-- The `L²` inverse Fourier transform of Schwartz data agrees almost
everywhere with its literal inverse Fourier integral. -/
theorem ae_eq_fourierInv_toLp_schwartz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (g : SchwartzMap E ℂ) :
    ((𝓕⁻ (g.toLp 2) : Lp ℂ 2 (volume : Measure E)) : E → ℂ) =ᵐ[volume]
      (𝓕⁻ (g : E → ℂ)) := by
  rw [SchwartzMap.toLp_fourierInv_eq]
  simpa only [SchwartzMap.fourierInv_coe] using
    (SchwartzMap.coeFn_toLp (𝓕⁻ g) 2 volume)

/-- The literal inverse Fourier integral of Schwartz data is continuous. -/
theorem continuous_fourierInv_schwartz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (g : SchwartzMap E ℂ) :
    Continuous (𝓕⁻ (g : E → ℂ)) := by
  rw [← SchwartzMap.fourierInv_coe]
  exact (𝓕⁻ g).continuous

end

end LeanSpherical.HarmonicAnalysis
