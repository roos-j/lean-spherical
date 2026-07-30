/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.MinkowskiFacts
import LeanSpherical.HarmonicAnalysis.FractalDilations.AssouadSpectrumFacts

/-!
# Finite interval covering numbers

The dimension definitions in this development are expressed through finite
interval covers.  This file packages their least cardinality for radius sets
contained in `[1,2]`, and records the upper and lower witness principles that
follow directly from the infimum definitions of Minkowski dimension and upper
Assouad spectrum.

No compactness assumption is needed: the ambient interval grid supplies a
finite cover at every positive scale.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Set

noncomputable section

/-- The natural numbers realized as cardinalities of finite length-`δ`
interval covers of `E`. -/
def intervalCoverCardinalities (E : Set ℝ) (δ : ℝ) : Set ℕ :=
  {n : ℕ | ∃ ι : Finset ℝ, IsIntervalCover E δ ι ∧ ι.card = n}

/-- The least cardinality of a finite length-`δ` interval cover.  For the
radius sets used here, finiteness follows from containment in `[1,2]`. -/
noncomputable def intervalCoveringNumber (E : Set ℝ) (δ : ℝ) : ℕ :=
  sInf (intervalCoverCardinalities E δ)

/-- The ambient grid makes the set of cover cardinalities nonempty. -/
theorem intervalCoverCardinalities_nonempty_of_subset_Icc
    {E : Set ℝ} {δ : ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) (hδ : 0 < δ) :
    (intervalCoverCardinalities E δ).Nonempty := by
  obtain ⟨ι, hι, _⟩ :=
    exists_intervalCover_of_subset_Icc (F := E) hδ (by norm_num) hE
  exact ⟨ι.card, ι, hι, rfl⟩

/-- A least interval cover exists for every positive scale on `[1,2]`. -/
theorem exists_intervalCover_card_eq_intervalCoveringNumber
    {E : Set ℝ} {δ : ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) (hδ : 0 < δ) :
    ∃ ι : Finset ℝ, IsIntervalCover E δ ι ∧ ι.card = intervalCoveringNumber E δ := by
  have hne : (intervalCoverCardinalities E δ).Nonempty :=
    intervalCoverCardinalities_nonempty_of_subset_Icc hE hδ
  change sInf (intervalCoverCardinalities E δ) ∈ intervalCoverCardinalities E δ
  exact Nat.sInf_mem hne

/-- The covering number is at most the cardinality of any particular cover. -/
theorem intervalCoveringNumber_le_card
    {E : Set ℝ} {δ : ℝ} {ι : Finset ℝ} (hι : IsIntervalCover E δ ι) :
    intervalCoveringNumber E δ ≤ ι.card := by
  apply Nat.sInf_le
  exact ⟨ι, hι, rfl⟩

/-- Characterization of a natural upper bound on the covering number by an
actual finite cover. -/
theorem intervalCoveringNumber_le_iff_exists_intervalCover
    {E : Set ℝ} {δ : ℝ} {n : ℕ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hδ : 0 < δ) :
    intervalCoveringNumber E δ ≤ n ↔
      ∃ ι : Finset ℝ, IsIntervalCover E δ ι ∧ ι.card ≤ n := by
  constructor
  · intro hN
    obtain ⟨ι, hι, hcard⟩ :=
      exists_intervalCover_card_eq_intervalCoveringNumber hE hδ
    exact ⟨ι, hι, hcard.symm ▸ hN⟩
  · rintro ⟨ι, hι, hcard⟩
    exact (intervalCoveringNumber_le_card hι).trans hcard

/-- A finite-cover upper bound transfers immediately to the covering number. -/
theorem intervalCoveringNumber_le_of_intervalCover_card_le
    {E : Set ℝ} {δ B : ℝ} {ι : Finset ℝ}
    (hι : IsIntervalCover E δ ι) (hcard : (ι.card : ℝ) ≤ B) :
    (intervalCoveringNumber E δ : ℝ) ≤ B := by
  have hN : intervalCoveringNumber E δ ≤ ι.card := intervalCoveringNumber_le_card hι
  have hNreal : (intervalCoveringNumber E δ : ℝ) ≤ (ι.card : ℝ) := by
    exact_mod_cast hN
  exact hNreal.trans hcard

/-- Enlarging the length of every interval preserves a finite interval
cover. -/
theorem IsIntervalCover.mono_scale
    {F : Set ℝ} {δ δ' : ℝ} {ι : Finset ℝ}
    (hδ : δ ≤ δ') (hι : IsIntervalCover F δ ι) :
    IsIntervalCover F δ' ι := by
  intro x hx
  rcases Set.mem_iUnion.mp (hι hx) with ⟨a, ha⟩
  rcases Set.mem_iUnion.mp ha with ⟨haι, hxa⟩
  refine Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨haι, ?_⟩⟩
  constructor <;> nlinarith [hxa.1, hxa.2, hδ]

/-- Upper Minkowski covering data bounds the interval covering number with
the same arbitrarily small exponent loss. -/
theorem intervalCoveringNumber_upper_bound_of_hasUpperMinkowskiExponent
    {E : Set ℝ} {β : ℝ} (hM : HasUpperMinkowskiExponent E β) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      (intervalCoveringNumber E δ : ℝ) ≤ C * δ ^ (-(β + ε)) := by
  intro ε hε
  obtain ⟨C, hC, hcover⟩ := hM ε hε
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδone
  obtain ⟨ι, hι, hcard⟩ := hcover δ hδ hδone
  exact intervalCoveringNumber_le_of_intervalCover_card_le hι hcard

/-- Upper Assouad-spectrum covering data bounds the corresponding local
interval covering number. -/
theorem intervalCoveringNumber_upper_bound_of_hasUpperAssouadSpectrumExponent
    {E : Set ℝ} {θ γ : ℝ} (hS : HasUpperAssouadSpectrumExponent E θ γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ a b : ℝ, 0 < δ → δ < 1 → 1 ≤ a → a ≤ b → b ≤ 2 →
      δ ^ θ ≤ b - a →
      (intervalCoveringNumber (E ∩ Icc a b) δ : ℝ) ≤ C * ((b - a) / δ) ^ γ := by
  obtain ⟨C, hC, hcover⟩ := hS
  refine ⟨C, hC, ?_⟩
  intro δ a b hδ hδone ha hab hb hscale
  obtain ⟨ι, hι, hcard⟩ := hcover δ a b hδ hδone ha hab hb hscale
  exact intervalCoveringNumber_le_of_intervalCover_card_le hι hcard

/-- An exponent strictly below the upper Minkowski dimension cannot satisfy
the defining uniform Minkowski cover estimate. -/
theorem not_hasUpperMinkowskiExponent_of_upperMinkowskiDimension_eq_lt
    {E : Set ℝ} {α β : ℝ}
    (hdimension : upperMinkowskiDimension E = β)
    (hα0 : 0 ≤ α) (hαβ : α < β) :
    ¬ HasUpperMinkowskiExponent E α := by
  intro hα
  have hbelow : BddBelow {s : ℝ | 0 ≤ s ∧ HasUpperMinkowskiExponent E s} := by
    refine ⟨0, ?_⟩
    intro s hs
    exact hs.1
  have hle : upperMinkowskiDimension E ≤ α := by
    unfold upperMinkowskiDimension
    exact csInf_le hbelow ⟨hα0, hα⟩
  linarith

/-- An exponent strictly below the upper spectrum cannot satisfy the defining
uniform local covering estimate. -/
theorem not_hasUpperAssouadSpectrumExponent_of_upperAssouadSpectrum_eq_lt
    {E : Set ℝ} {θ α γ : ℝ}
    (hspectrum : upperAssouadSpectrum E θ = γ)
    (hα0 : 0 ≤ α) (hαγ : α < γ) :
    ¬ HasUpperAssouadSpectrumExponent E θ α := by
  intro hα
  have hle : upperAssouadSpectrum E θ ≤ α := by
    rw [upperAssouadSpectrum_eq_sInf_admissibleExponents]
    exact csInf_le (upperAssouadAdmissibleExponents_bddBelow E θ) ⟨hα0, hα⟩
  linarith

/-- A strict lower bound on upper Minkowski dimension yields quantitative
counter-witnesses to every putative smaller-exponent cover estimate.  The
covering number is finite because the set is contained in the radius interval.

This is the direct quantifier form of the negation of an upper Minkowski
exponent; extracting a prescribed *arbitrarily small* scale is a later,
separate compactness-free argument. -/
theorem exists_upperMinkowski_coveringNumber_lower_witness
    {E : Set ℝ} {α β : ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2)
    (hdimension : upperMinkowskiDimension E = β)
    (hα0 : 0 ≤ α) (hαβ : α < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 0 < C → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      C * δ ^ (-(α + ε)) < (intervalCoveringNumber E δ : ℝ) := by
  have hnot : ¬ HasUpperMinkowskiExponent E α :=
    not_hasUpperMinkowskiExponent_of_upperMinkowskiDimension_eq_lt
      hdimension hα0 hαβ
  classical
  simp only [HasUpperMinkowskiExponent] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hfailure⟩ := hnot
  refine ⟨ε, hε, ?_⟩
  intro C hC
  obtain ⟨δ, hδ, hδone, hnoCover⟩ := hfailure C hC
  obtain ⟨ι, hι, hcard⟩ :=
    exists_intervalCover_card_eq_intervalCoveringNumber hE hδ
  refine ⟨δ, hδ, hδone, ?_⟩
  simpa only [hcard] using hnoCover ι hι

/-- The lower Minkowski covering witnesses occur below every prescribed
positive scale.  Although the definition quantifies over all `0 < δ < 1`, a
failure confined to a fixed large-scale range would be absorbed by one finite
ambient cover, so it cannot witness a strict dimension gap. -/
theorem exists_upperMinkowski_coveringNumber_lower_witness_at_small_scale
    {E : Set ℝ} {α β : ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2)
    (hdimension : upperMinkowskiDimension E = β)
    (hα0 : 0 ≤ α) (hαβ : α < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 0 < C → ∀ δ₀ : ℝ, 0 < δ₀ →
      ∃ δ : ℝ, 0 < δ ∧ δ < δ₀ ∧ δ < 1 ∧
        C * δ ^ (-(α + ε)) < (intervalCoveringNumber E δ : ℝ) := by
  obtain ⟨ε, hε, hwitness⟩ :=
    exists_upperMinkowski_coveringNumber_lower_witness hE hdimension hα0 hαβ
  refine ⟨ε, hε, ?_⟩
  intro C hC δ₀ hδ₀
  obtain ⟨ι₀, hι₀, _⟩ :=
    exists_intervalCover_card_eq_intervalCoveringNumber hE hδ₀
  let C' : ℝ := max C ((ι₀.card : ℝ) + 1)
  have hC' : 0 < C' := lt_of_lt_of_le hC (by
    dsimp [C']
    exact le_max_left _ _)
  have hCleC' : C ≤ C' := by
    dsimp [C']
    exact le_max_left _ _
  have hcardleC' : (ι₀.card : ℝ) ≤ C' := by
    calc
      (ι₀.card : ℝ) ≤ (ι₀.card : ℝ) + 1 := by linarith
      _ ≤ C' := by
        dsimp [C']
        exact le_max_right _ _
  obtain ⟨δ, hδ, hδone, hlarge⟩ := hwitness C' hC'
  have hδsmall : δ < δ₀ := by
    by_contra hnot
    have hδ₀δ : δ₀ ≤ δ := le_of_not_gt hnot
    have hι : IsIntervalCover E δ ι₀ := hι₀.mono_scale hδ₀δ
    have hNle : (intervalCoveringNumber E δ : ℝ) ≤ (ι₀.card : ℝ) := by
      exact_mod_cast intervalCoveringNumber_le_card hι
    have hpow : 1 ≤ δ ^ (-(α + ε)) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδone.le
      linarith
    have hCpow : C' ≤ C' * δ ^ (-(α + ε)) :=
      le_mul_of_one_le_right hC'.le hpow
    exact (not_lt_of_ge (hNle.trans (hcardleC'.trans hCpow))) hlarge
  refine ⟨δ, hδ, hδsmall, hδone, ?_⟩
  calc
    C * δ ^ (-(α + ε)) ≤ C' * δ ^ (-(α + ε)) :=
      mul_le_mul_of_nonneg_right hCleC' (Real.rpow_nonneg hδ.le _)
    _ < (intervalCoveringNumber E δ : ℝ) := hlarge

/-- A strict lower bound on the upper spectrum produces a local interval and
a scale at which the associated covering number defeats every proposed
smaller-exponent bound. -/
theorem exists_upperAssouadSpectrum_coveringNumber_lower_witness
    {E : Set ℝ} {θ α γ : ℝ}
    (hspectrum : upperAssouadSpectrum E θ = γ)
    (hα0 : 0 ≤ α) (hαγ : α < γ) :
    ∀ C : ℝ, 0 < C → ∃ δ a b : ℝ,
      0 < δ ∧ δ < 1 ∧ 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ δ ^ θ ≤ b - a ∧
        C * ((b - a) / δ) ^ α <
          (intervalCoveringNumber (E ∩ Icc a b) δ : ℝ) := by
  have hnot : ¬ HasUpperAssouadSpectrumExponent E θ α :=
    not_hasUpperAssouadSpectrumExponent_of_upperAssouadSpectrum_eq_lt
      hspectrum hα0 hαγ
  classical
  simp only [HasUpperAssouadSpectrumExponent] at hnot
  push Not at hnot
  intro C hC
  obtain ⟨δ, a, b, hδ, hδone, ha, hab, hb, hscale, hnoCover⟩ := hnot C hC
  have hlocal : E ∩ Icc a b ⊆ Icc (1 : ℝ) 2 := by
    intro x hx
    exact ⟨ha.trans hx.2.1, hx.2.2.trans hb⟩
  obtain ⟨ι, hι, hcard⟩ :=
    exists_intervalCover_card_eq_intervalCoveringNumber hlocal hδ
  refine ⟨δ, a, b, hδ, hδone, ha, hab, hb, hscale, ?_⟩
  simpa only [hcard] using hnoCover ι hι

/-- On the usual spectrum range, the local lower witnesses also occur below
every prescribed positive scale.  The upper-spectrum condition gives
`(b-a)/δ ≥ 1`, so one fixed cover of the ambient radius interval rules out a
large-scale-only failure. -/
theorem exists_upperAssouadSpectrum_coveringNumber_lower_witness_at_small_scale
    {E : Set ℝ} {θ α γ : ℝ}
    (_hθ0 : 0 ≤ θ) (hθone : θ ≤ 1)
    (hspectrum : upperAssouadSpectrum E θ = γ)
    (hα0 : 0 ≤ α) (hαγ : α < γ) :
    ∀ C : ℝ, 0 < C → ∀ δ₀ : ℝ, 0 < δ₀ → ∃ δ a b : ℝ,
      0 < δ ∧ δ < δ₀ ∧ δ < 1 ∧ 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧
        δ ^ θ ≤ b - a ∧
        C * ((b - a) / δ) ^ α <
          (intervalCoveringNumber (E ∩ Icc a b) δ : ℝ) := by
  intro C hC δ₀ hδ₀
  obtain ⟨ι₀, hι₀, _⟩ :=
    exists_intervalCover_card_eq_intervalCoveringNumber
      (E := Icc (1 : ℝ) 2) (by intro x hx; exact hx) hδ₀
  let C' : ℝ := max C ((ι₀.card : ℝ) + 1)
  have hC' : 0 < C' := lt_of_lt_of_le hC (by
    dsimp [C']
    exact le_max_left _ _)
  have hCleC' : C ≤ C' := by
    dsimp [C']
    exact le_max_left _ _
  have hcardleC' : (ι₀.card : ℝ) ≤ C' := by
    calc
      (ι₀.card : ℝ) ≤ (ι₀.card : ℝ) + 1 := by linarith
      _ ≤ C' := by
        dsimp [C']
        exact le_max_right _ _
  obtain ⟨δ, a, b, hδ, hδone, ha, hab, hb, hscale, hlarge⟩ :=
    exists_upperAssouadSpectrum_coveringNumber_lower_witness
      hspectrum hα0 hαγ C' hC'
  have hδsmall : δ < δ₀ := by
    by_contra hnot
    have hδ₀δ : δ₀ ≤ δ := le_of_not_gt hnot
    have hιambient : IsIntervalCover (Icc (1 : ℝ) 2) δ ι₀ :=
      hι₀.mono_scale hδ₀δ
    have hlocal : E ∩ Icc a b ⊆ Icc (1 : ℝ) 2 := by
      intro x hx
      exact ⟨ha.trans hx.2.1, hx.2.2.trans hb⟩
    have hι : IsIntervalCover (E ∩ Icc a b) δ ι₀ :=
      IsIntervalCover.mono hlocal hιambient
    have hNle : (intervalCoveringNumber (E ∩ Icc a b) δ : ℝ) ≤
        (ι₀.card : ℝ) := by
      exact_mod_cast intervalCoveringNumber_le_card hι
    have hδθ : δ ≤ δ ^ θ := by
      calc
        δ = δ ^ (1 : ℝ) := by simp
        _ ≤ δ ^ θ :=
          Real.rpow_le_rpow_of_exponent_ge hδ hδone.le hθone
    have hratio : 1 ≤ (b - a) / δ := by
      rw [le_div_iff₀ hδ]
      simpa using hδθ.trans hscale
    have hratioPow : 1 ≤ ((b - a) / δ) ^ α :=
      Real.one_le_rpow hratio hα0
    have hCpow : C' ≤ C' * ((b - a) / δ) ^ α :=
      le_mul_of_one_le_right hC'.le hratioPow
    exact (not_lt_of_ge (hNle.trans (hcardleC'.trans hCpow))) hlarge
  refine ⟨δ, a, b, hδ, hδsmall, hδone, ha, hab, hb, hscale, ?_⟩
  calc
    C * ((b - a) / δ) ^ α ≤ C' * ((b - a) / δ) ^ α :=
      mul_le_mul_of_nonneg_right hCleC'
        (Real.rpow_nonneg (div_nonneg (sub_nonneg.mpr hab) hδ.le) _)
    _ < (intervalCoveringNumber (E ∩ Icc a b) δ : ℝ) := hlarge

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
