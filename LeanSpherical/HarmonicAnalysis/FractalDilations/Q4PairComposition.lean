/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4TTStar

/-!
# Exact Schwartz and convolution realization of the `Q4` pair piece

The `Q4` pair operator is initially written as a literal inverse Fourier
integral.  This file proves that, after the usual compact annular localization,
its multiplier is itself a Schwartz map.  Consequently the pair piece is both
an exact Fourier multiplier and convolution with its literal inverse-Fourier
kernel.  No kernel estimate is used here.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory FourierTransform
open scoped Convolution FourierTransform

noncomputable section

/-- Compactly localizing a surface multiplier gives a Schwartz map, with the
factor order adjusted to the convention used by `q4DyadicSurfaceMultiplier`. -/
private theorem exists_schwartz_compactSupport_q4DyadicSurfaceMultiplier
    {d : ℕ} (ψ : SchwartzMap (Euclidean d) ℂ)
    (hψcompact : HasCompactSupport (ψ : Euclidean d → ℂ)) (r : ℝ) :
    ∃ m : SchwartzMap (Euclidean d) ℂ,
      HasCompactSupport (m : Euclidean d → ℂ) ∧
      ∀ ξ : Euclidean d, m ξ = q4DyadicSurfaceMultiplier ψ r ξ := by
  let g : Euclidean d → ℂ := fun ξ => ψ ξ * surfaceFourier d (-r • ξ)
  have hcompact : HasCompactSupport g := hψcompact.mul_right
  have hsurface : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun ξ : Euclidean d => surfaceFourier d (-r • ξ)) := by
    exact (contDiff_surfaceFourier d).comp
      (ContinuousLinearMap.contDiff (ContinuousLinearMap.lsmul ℝ ℝ (-r)))
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    exact (ψ.smooth (⊤ : ℕ∞)).mul hsurface
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_⟩
  · change HasCompactSupport g
    exact hcompact
  · intro ξ
    change ψ ξ * surfaceFourier d (-r • ξ) = q4DyadicSurfaceMultiplier ψ r ξ
    unfold q4DyadicSurfaceMultiplier
    ring

/-- Complex conjugation preserves a compactly supported Schwartz multiplier.
The scalar field is restricted to `ℝ` for this construction, since complex
conjugation is real-linear rather than complex-linear. -/
private theorem exists_star_schwartzMap_of_compact
    {d : ℕ} (m : SchwartzMap (Euclidean d) ℂ)
    (hmcompact : HasCompactSupport (m : Euclidean d → ℂ)) :
    ∃ mstar : SchwartzMap (Euclidean d) ℂ,
      HasCompactSupport (mstar : Euclidean d → ℂ) ∧
      ∀ ξ : Euclidean d, mstar ξ = starRingEnd ℂ (m ξ) := by
  let g : Euclidean d → ℂ := fun ξ => starRingEnd ℂ (m ξ)
  have hcompact : HasCompactSupport g := by
    change HasCompactSupport ((starRingEnd ℂ) ∘ (m : Euclidean d → ℂ))
    exact hmcompact.comp_left (g := starRingEnd ℂ) (by simp)
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    have hg : g = (Complex.conjCLE : ℂ → ℂ) ∘ (m : Euclidean d → ℂ) := by
      funext ξ
      simpa only [g, Function.comp_apply] using (Complex.conjCLE_apply (m ξ)).symm
    rw [hg]
    exact Complex.conjCLE.contDiff.comp (m.smooth (⊤ : ℕ∞))
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_⟩
  · change HasCompactSupport g
    exact hcompact
  · intro ξ
    rfl

/-- The compactly localized literal `Q4` pair multiplier is a Schwartz map.
This packages the two surface factors and the conjugation into one multiplier
that can be passed to the existing Fourier-convolution API. -/
theorem exists_schwartz_q4DyadicPairMultiplier
    {d : ℕ} (ψ : SchwartzMap (Euclidean d) ℂ)
    (hψcompact : HasCompactSupport (ψ : Euclidean d → ℂ)) (r r' : ℝ) :
    ∃ m : SchwartzMap (Euclidean d) ℂ,
      ∀ ξ : Euclidean d, m ξ = q4DyadicPairMultiplier ψ r r' ξ := by
  rcases exists_schwartz_compactSupport_q4DyadicSurfaceMultiplier ψ hψcompact r with
    ⟨mr, hmrcompact, hmr⟩
  rcases exists_schwartz_compactSupport_q4DyadicSurfaceMultiplier ψ hψcompact r' with
    ⟨mr', hmr'compact, hmr'⟩
  rcases exists_star_schwartzMap_of_compact mr' hmr'compact with
    ⟨mr'star, hmr'starcompact, hmr'star⟩
  refine ⟨SchwartzMap.smulLeftCLM ℂ (mr : Euclidean d → ℂ) mr'star, ?_⟩
  intro ξ
  simp only [SchwartzMap.smulLeftCLM_apply mr.hasTemperateGrowth, smul_eq_mul]
  rw [hmr ξ, hmr'star ξ, hmr' ξ]
  unfold q4DyadicPairMultiplier q4DyadicSurfaceMultiplier
  simp only [map_mul]

/-- The `Q4` pair piece is a genuine Schwartz Fourier multiplier, and its
Fourier transform is exactly the product symbol in the definition. -/
theorem exists_schwartz_q4DyadicPairPiece_fourier
    {d : ℕ} (ψ f : SchwartzMap (Euclidean d) ℂ)
    (hψcompact : HasCompactSupport (ψ : Euclidean d → ℂ)) (r r' : ℝ) :
    ∃ (m g : SchwartzMap (Euclidean d) ℂ),
      (∀ ξ : Euclidean d, m ξ = q4DyadicPairMultiplier ψ r r' ξ) ∧
      (∀ x : Euclidean d, g x = q4DyadicPairPiece ψ f r r' x) ∧
      (∀ ξ : Euclidean d,
        𝓕 (g : Euclidean d → ℂ) ξ =
          q4DyadicPairMultiplier ψ r r' ξ * 𝓕 (f : Euclidean d → ℂ) ξ) := by
  rcases exists_schwartz_q4DyadicPairMultiplier ψ hψcompact r r' with ⟨m, hm⟩
  let h : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (m : Euclidean d → ℂ) (𝓕 f)
  refine ⟨m, 𝓕⁻ h, hm, ?_, ?_⟩
  · intro x
    rw [SchwartzMap.fourierInv_coe]
    have hsymbol : (h : Euclidean d → ℂ) =
        fun ξ : Euclidean d => q4DyadicPairMultiplier ψ r r' ξ *
          𝓕 (f : Euclidean d → ℂ) ξ := by
      funext ξ
      simp only [h, SchwartzMap.smulLeftCLM_apply m.hasTemperateGrowth, smul_eq_mul]
      rw [hm ξ]
      rw [← SchwartzMap.fourier_coe]
    unfold q4DyadicPairPiece
    rw [hsymbol]
  · intro ξ
    have hfourier :
        𝓕 ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) =
          (h : Euclidean d → ℂ) := by
      rw [← SchwartzMap.fourier_coe, fourier_fourierInv_eq]
    rw [hfourier]
    rw [← SchwartzMap.fourier_coe]
    change h ξ = q4DyadicPairMultiplier ψ r r' ξ * (𝓕 f) ξ
    simp only [h, SchwartzMap.smulLeftCLM_apply m.hasTemperateGrowth, smul_eq_mul]
    rw [hm ξ]

/-- The same pair piece is exactly convolution with the inverse-Fourier
kernel of its compact Schwartz multiplier.  This is the physical-space bridge
needed before applying a signed radius-gap kernel estimate. -/
theorem exists_q4DyadicPairPiece_eq_convolution
    {d : ℕ} (ψ f : SchwartzMap (Euclidean d) ℂ)
    (hψcompact : HasCompactSupport (ψ : Euclidean d → ℂ)) (r r' : ℝ) :
    ∃ m : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d, m ξ = q4DyadicPairMultiplier ψ r r' ξ) ∧
      ∀ x : Euclidean d,
        q4DyadicPairPiece ψ f r r' x =
          (((𝓕⁻ m : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ)
            ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (f : Euclidean d → ℂ)) x := by
  rcases exists_schwartz_q4DyadicPairMultiplier ψ hψcompact r r' with ⟨m, hm⟩
  refine ⟨m, hm, ?_⟩
  intro x
  unfold q4DyadicPairPiece
  have hrewrite :
      (fun ξ : Euclidean d => q4DyadicPairMultiplier ψ r r' ξ *
        𝓕 (f : Euclidean d → ℂ) ξ) =
      fun ξ : Euclidean d => m ξ * 𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    rw [hm ξ]
  rw [hrewrite, fourierInv_schwartz_multiplier_eq_convolution]

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
