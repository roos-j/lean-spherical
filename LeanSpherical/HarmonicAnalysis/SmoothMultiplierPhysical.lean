/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SmoothFrequencyCutoff
import LeanSpherical.HarmonicAnalysis.YoungL1
import Mathlib.Analysis.Fourier.Convolution

/-!
# Physical realization of a smooth Fourier multiplier

For Schwartz input and a Schwartz frequency cutoff, the literal inverse
Fourier integral of the localized input is the ordinary convolution with the
inverse Fourier transform of the cutoff.  This is the physical-space bridge
for smooth frequency localization; no assertion about a radius supremum is
made here.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform
open scoped Convolution FourierTransform

noncomputable section

/-- Multiplication of the Fourier transform of a Schwartz function by a
Schwartz frequency cutoff is, after literal inverse Fourier transformation,
convolution with the inverse transform of that cutoff. -/
theorem fourierInv_schwartz_multiplier_eq_convolution
    {d : ℕ} (φ f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    𝓕⁻ (fun ξ : Euclidean d => φ ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x =
      (((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ)
        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (f : Euclidean d → ℂ)) x := by
  have h :
      (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (φ : Euclidean d → ℂ) (𝓕 f)) :
        SchwartzMap (Euclidean d) ℂ) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ φ) f := by
    have hinv :
        (𝓕⁻ (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ φ) f)) :
          SchwartzMap (Euclidean d) ℂ) =
        SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ φ) f := by
      exact fourierInv_fourier_eq _
    rw [← hinv]
    congr 1
    ext y
    simp [SchwartzMap.fourier_convolution, SchwartzMap.smulLeftCLM_apply_apply,
      φ.hasTemperateGrowth]
  simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe,
    SchwartzMap.smulLeftCLM_apply φ.hasTemperateGrowth, smul_eq_mul,
    SchwartzMap.convolution_apply] using
    congrArg (fun g : SchwartzMap (Euclidean d) ℂ => g x) h

/-- The physical realization of a smooth Fourier multiplier has the concrete
`L∞` estimate supplied by the `L¹` norm of its inverse-Fourier kernel. -/
theorem norm_fourierInv_schwartz_multiplier_le
    {d : Nat} (φ f : SchwartzMap (Euclidean d) ℂ)
    {C : ℝ} (hfbound : ∀ x, ‖f x‖ ≤ C) (x : Euclidean d) :
    ‖𝓕⁻ (fun ξ : Euclidean d => φ ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
      C * ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖ := by
  rw [fourierInv_schwartz_multiplier_eq_convolution]
  simpa [mul_comm] using
    norm_convolution_mul_le_integral_norm_mul_bound
      ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ)
      (f : Euclidean d → ℂ) (𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ).integrable
      f.continuous hfbound x

/-- Inverse Fourier transformation distributes over the difference of two
Schwartz-multiplied Schwartz inputs.  This is the literal band-pass identity
needed to pass from smooth low-pass projections to their differences. -/
theorem fourierInv_sub_schwartz_multiplier
    {d : Nat} (φ ψ f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    𝓕⁻ (fun ξ : Euclidean d =>
      (φ ξ - ψ ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x =
      𝓕⁻ (fun ξ : Euclidean d => φ ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x -
        𝓕⁻ (fun ξ : Euclidean d => ψ ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x := by
  let gφ : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (φ : Euclidean d → ℂ) (𝓕 f)
  let gψ : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)
  have hgφ : (gφ : Euclidean d → ℂ) =
      fun ξ : Euclidean d => φ ξ * 𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    simp only [gφ, SchwartzMap.smulLeftCLM_apply φ.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul]
  have hgψ : (gψ : Euclidean d → ℂ) =
      fun ξ : Euclidean d => ψ ξ * 𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    simp only [gψ, SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul]
  have hdiff : ((gφ - gψ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) =
      fun ξ : Euclidean d => (φ ξ - ψ ξ) * 𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    change gφ ξ - gψ ξ = _
    rw [congrFun hgφ ξ, congrFun hgψ ξ]
    ring
  calc
    𝓕⁻ (fun ξ : Euclidean d =>
        (φ ξ - ψ ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x =
        𝓕⁻ ((gφ - gψ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x := by
      rw [hdiff]
    _ = (𝓕⁻ (gφ - gψ) : SchwartzMap (Euclidean d) ℂ) x := by
      rw [SchwartzMap.fourierInv_coe]
    _ = ((𝓕⁻ gφ : SchwartzMap (Euclidean d) ℂ) -
        (𝓕⁻ gψ : SchwartzMap (Euclidean d) ℂ)) x := by
      rw [sub_eq_add_neg, fourierInv_add, fourierInv_neg]
      rfl
    _ = 𝓕⁻ (gφ : Euclidean d → ℂ) x - 𝓕⁻ (gψ : Euclidean d → ℂ) x := by
      simp only [sub_apply, SchwartzMap.fourierInv_coe]
    _ = 𝓕⁻ (fun ξ : Euclidean d => φ ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x -
        𝓕⁻ (fun ξ : Euclidean d => ψ ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x := by
      rw [hgφ, hgψ]

end

end LeanSpherical.HarmonicAnalysis
