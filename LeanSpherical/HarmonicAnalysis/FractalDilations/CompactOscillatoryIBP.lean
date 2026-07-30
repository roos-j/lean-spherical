/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.RepeatedOscillatoryIBP
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Compact smooth amplitudes for repeated nonstationary phase

The radial integration-by-parts step in the proof of Lemma 2.1 is often
written using the phrase “the symbol is smooth and compactly supported on the
annulus.”  This file turns that phrase into the exact
`HasOscillatoryIBPChain` required by `RepeatedOscillatoryIBP`.

The result is deliberately one-dimensional.  Once polar coordinates and the
stationary meridian decomposition have produced a radial amplitude, every
dimension-dependent issue has already occurred; the remaining arbitrary
power of the radius-gap gain follows from the lemmas here without any extra
analytic assumption.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Set
open scoped ContDiff

noncomputable section

/-- A globally smooth amplitude which vanishes in neighbourhoods of both
endpoints supplies all of the derivative and endpoint hypotheses for the
finite repeated integration-by-parts chain. -/
theorem hasOscillatoryIBPChain_iteratedDeriv_of_contDiff
    {a b : Real} (F : Real -> Complex)
    (hF : ContDiff Real (⊤ : ℕ∞) F)
    (hFa : F =ᶠ[𝓝 a] 0) (hFb : F =ᶠ[𝓝 b] 0) (N : Nat) :
    HasOscillatoryIBPChain a b (fun k => iteratedDeriv k F) N := by
  intro k hk
  constructor
  · intro t ht
    have hdiff : Differentiable Real (iteratedDeriv k F) :=
      hF.differentiable_iteratedDeriv k (by simp)
    simpa only [iteratedDeriv_succ] using (hdiff t).hasDerivAt
  constructor
  · exact hF.continuous_iteratedDeriv (k + 1) (by simp)
  constructor
  · have h := Filter.EventuallyEq.iteratedDeriv_eq k hFa
    simpa using h
  · have h := Filter.EventuallyEq.iteratedDeriv_eq k hFb
    simpa using h

/-- The last derivative in a compact nonstationary-phase chain has a finite,
strictly positive uniform bound on the closed radial annulus. -/
theorem exists_pos_norm_iteratedDeriv_le_on_Icc_of_contDiff
    {a b : Real} (F : Real -> Complex)
    (hF : ContDiff Real (⊤ : ℕ∞) F) (N : Nat) :
    ∃ M : Real, 0 < M ∧ ∀ t ∈ Icc a b, ‖iteratedDeriv N F t‖ ≤ M := by
  have hcont : Continuous (iteratedDeriv N F) :=
    hF.continuous_iteratedDeriv N (by simp)
  rcases (isCompact_Icc.image_of_continuousOn hcont.continuousOn).isBounded
      .exists_pos_norm_le with ⟨M, hM, hbound⟩
  exact ⟨M, hM, fun t ht => hbound _ (mem_image_of_mem _ ht)⟩

/-- A fully discharged arbitrary-order nonstationary estimate.  This is the
literal final radial step after a stationary wave amplitude has been cut off
to its dyadic annulus. -/
theorem exists_norm_intervalIntegral_mul_oscillatoryExp_le_iterated_of_contDiff
    {a b freq : Real} (F : Real -> Complex)
    (hab : a ≤ b) (hfreq : freq ≠ 0)
    (hF : ContDiff Real (⊤ : ℕ∞) F)
    (hFa : F =ᶠ[𝓝 a] 0) (hFb : F =ᶠ[𝓝 b] 0) (N : Nat) :
    ∃ M : Real, 0 < M ∧
      ‖∫ t in a..b, F t * oscillatoryExp freq t‖ ≤
        (1 / |freq|) ^ N * ((b - a) * M) := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_pos_norm_iteratedDeriv_le_on_Icc_of_contDiff F hF N
  refine ⟨M, hM, ?_⟩
  exact norm_intervalIntegral_mul_oscillatoryExp_le_iterated hab hfreq
    (hasOscillatoryIBPChain_iteratedDeriv_of_contDiff F hF hFa hFb N)
    hM.le hbound

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
