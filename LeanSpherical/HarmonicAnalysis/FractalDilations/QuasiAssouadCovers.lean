/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.AssouadSpectrumFacts
import LeanSpherical.HarmonicAnalysis.FractalDilations.SmallScaleCover

/-!
# Cover estimates from quasi-Assouad dimension

This file turns the supremal definition of quasi-Assouad dimension into the
two concrete covering estimates used in the non-endpoint maximal-operator
argument.  First, at every parameter `1 - epsilon` below one, every exponent
strictly above the quasi-Assouad dimension is an upper-spectrum exponent.
Second, the elementary short-interval cover bound upgrades this to a full
local cover estimate with an arbitrarily small subpower loss.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Set

noncomputable section

private theorem upperAssouadSpectrum_image_Ico_bddAbove (E : Set ℝ) :
    BddAbove (upperAssouadSpectrum E '' Ico (0 : ℝ) 1) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨θ, hθ, rfl⟩
  exact upperAssouadSpectrum_le_one E hθ.2.le

/-- Quasi-Assouad dimension is nonnegative. -/
theorem quasiAssouadDimension_nonneg (E : Set ℝ) :
    0 ≤ quasiAssouadDimension E := by
  have hmem : upperAssouadSpectrum E 0 ∈
      upperAssouadSpectrum E '' Ico (0 : ℝ) 1 :=
    ⟨0, ⟨le_rfl, zero_lt_one⟩, rfl⟩
  unfold quasiAssouadDimension
  exact le_csSup_of_le (upperAssouadSpectrum_image_Ico_bddAbove E) hmem
    (upperAssouadSpectrum_nonneg E zero_le_one)

/-- A positive loss above the quasi-Assouad dimension gives a concrete upper
Assouad-spectrum covering exponent at every scale parameter `1 - epsilon`.
This is the usable form of the `sSup` definition. -/
theorem hasUpperAssouadSpectrumExponent_one_sub_of_quasiAssouadDimension_eq
    {E : Set ℝ} {γ ε η : ℝ}
    (hquasi : quasiAssouadDimension E = γ)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hη : 0 < η) :
    HasUpperAssouadSpectrumExponent E (1 - ε) (γ + η) := by
  have hθ0 : 0 ≤ 1 - ε := by linarith
  have hθ1 : 1 - ε ≤ 1 := by linarith
  have hθlt : 1 - ε < 1 := by linarith
  have hmem : upperAssouadSpectrum E (1 - ε) ∈
      upperAssouadSpectrum E '' Ico (0 : ℝ) 1 :=
    ⟨1 - ε, ⟨hθ0, hθlt⟩, rfl⟩
  have hspectrum_le : upperAssouadSpectrum E (1 - ε) ≤ quasiAssouadDimension E := by
    unfold quasiAssouadDimension
    exact le_csSup (upperAssouadSpectrum_image_Ico_bddAbove E) hmem
  apply hasUpperAssouadSpectrumExponent_of_upperAssouadSpectrum_lt hθ0 hθ1
  calc
    upperAssouadSpectrum E (1 - ε) ≤ quasiAssouadDimension E := hspectrum_le
    _ = γ := hquasi
    _ < γ + η := by linarith

/-- Combining the preceding spectrum estimate with the elementary short-scale
cover gives the full local subpower estimate.  The output loss `eta` must
dominate the scale loss `epsilon`; in applications one chooses epsilon smaller
than eta. -/
theorem exists_hasSubpowerAssouadCoverBound_of_quasiAssouadDimension_eq_of_scale
    {E : Set ℝ} {γ ε η : ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2)
    (hquasi : quasiAssouadDimension E = γ)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hη : 0 < η) (hεη : ε ≤ η) :
    ∃ C : ℝ, 0 < C ∧ HasSubpowerAssouadCoverBound E γ η C := by
  have hγ : 0 ≤ γ := by
    calc
      0 ≤ quasiAssouadDimension E := quasiAssouadDimension_nonneg E
      _ = γ := hquasi
  exact hasSubpowerAssouadCoverBound_of_upperSpectrum_of_subset_Icc hE
    (hasUpperAssouadSpectrumExponent_one_sub_of_quasiAssouadDimension_eq
      hquasi hε hεone hη)
    hγ hε.le hη.le hεη le_rfl

/-- The subpower local cover estimate in the form normally used away from
endpoints: every positive loss is available. -/
theorem exists_hasSubpowerAssouadCoverBound_of_quasiAssouadDimension_eq
    {E : Set ℝ} {γ η : ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2)
    (hquasi : quasiAssouadDimension E = γ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ HasSubpowerAssouadCoverBound E γ η C := by
  let ε : ℝ := η / (η + 1)
  have hden : 0 < η + 1 := by linarith
  have hε : 0 < ε := by
    dsimp only [ε]
    exact div_pos hη hden
  have hεone : ε ≤ 1 := by
    dsimp only [ε]
    apply (div_le_iff₀ hden).2
    linarith
  have hεη : ε ≤ η := by
    dsimp only [ε]
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg η]
  exact exists_hasSubpowerAssouadCoverBound_of_quasiAssouadDimension_eq_of_scale
    hE hquasi hε hεone hη hεη

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
