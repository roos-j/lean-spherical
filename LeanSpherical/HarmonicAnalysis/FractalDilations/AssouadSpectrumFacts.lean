/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.AssouadSpectrum
import LeanSpherical.HarmonicAnalysis.FractalDilations.IntervalCovering

/-!
# Elementary facts about the upper Assouad spectrum

This file supplies the order-theoretic facts needed to use the upper Assouad
spectrum in the quasi-Assouad argument.  In particular, the spectrum is
monotone in its scale parameter on the usual interval `[0, 1]`.  The proofs use
only the elementary interval grid, not any maximal-operator estimates.

The regularity convention is the quasi-Assouad-regular convention: when the
quasi-Assouad dimension is positive, the upper spectrum is required to equal it
at every parameter strictly above `1 - beta / gamma`; the zero-dimensional
case is kept separate to avoid a division-by-zero condition.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Set

noncomputable section

/-- The admissible exponents whose infimum defines the upper Assouad spectrum. -/
def upperAssouadAdmissibleExponents (E : Set ℝ) (θ : ℝ) : Set ℝ :=
  {γ : ℝ | 0 ≤ γ ∧ HasUpperAssouadSpectrumExponent E θ γ}

theorem upperAssouadSpectrum_eq_sInf_admissibleExponents (E : Set ℝ) (θ : ℝ) :
    upperAssouadSpectrum E θ = sInf (upperAssouadAdmissibleExponents E θ) := rfl

/-- The admissible exponents are always bounded below by zero. -/
theorem upperAssouadAdmissibleExponents_bddBelow (E : Set ℝ) (θ : ℝ) :
    BddBelow (upperAssouadAdmissibleExponents E θ) := by
  refine ⟨0, ?_⟩
  intro γ hγ
  exact hγ.1

/-- The one-dimensional interval grid gives exponent `1` for every upper
Assouad spectrum parameter at most `1`. -/
theorem hasUpperAssouadSpectrumExponent_one
    {E : Set ℝ} {θ : ℝ} (hθ1 : θ ≤ 1) :
    HasUpperAssouadSpectrumExponent E θ 1 := by
  refine ⟨4, by norm_num, ?_⟩
  intro δ a b hδ hδone ha hab hb hscale
  obtain ⟨ι, hι, hcard⟩ := exists_intervalCover_of_subset_Icc
    (F := E ∩ Icc a b) hδ hab (inter_subset_right : E ∩ Icc a b ⊆ Icc a b)
  let L : ℝ := b - a
  have hLpos : 0 < L := by
    dsimp only [L]
    have hδθ : 0 < δ ^ θ := Real.rpow_pos_of_pos hδ θ
    exact hδθ.trans_le hscale
  have hδle : δ ≤ L := by
    have hpow : δ ≤ δ ^ θ := by
      calc
        δ = δ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ δ ^ θ := Real.rpow_le_rpow_of_exponent_ge hδ hδone.le hθ1
    exact hpow.trans (by simpa only [L] using hscale)
  have hratio : 1 ≤ L / δ := by
    rw [le_div_iff₀ hδ]
    simpa using hδle
  have hceil : (Nat.ceil (L / δ) : ℝ) ≤ L / δ + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg hLpos.le hδ.le)).le
  refine ⟨ι, hι, ?_⟩
  calc
    (ι.card : ℝ) ≤ (Nat.ceil (L / δ) : ℝ) + 2 := by
      simpa only [L] using hcard
    _ ≤ (L / δ + 1) + 2 := by linarith
    _ ≤ 4 * (L / δ) := by nlinarith
    _ = 4 * ((b - a) / δ) ^ (1 : ℝ) := by
      simp only [L, Real.rpow_one]

/-- For parameters at most `1`, the class defining the upper spectrum is
nonempty. -/
theorem upperAssouadAdmissibleExponents_nonempty
    (E : Set ℝ) {θ : ℝ} (hθ1 : θ ≤ 1) :
    (upperAssouadAdmissibleExponents E θ).Nonempty :=
  ⟨1, zero_le_one, hasUpperAssouadSpectrumExponent_one hθ1⟩

/-- The upper Assouad spectrum lies between zero and one for parameters at
most `1`. -/
theorem upperAssouadSpectrum_nonneg
    (E : Set ℝ) {θ : ℝ} (hθ1 : θ ≤ 1) :
    0 ≤ upperAssouadSpectrum E θ := by
  rw [upperAssouadSpectrum_eq_sInf_admissibleExponents]
  exact le_csInf (upperAssouadAdmissibleExponents_nonempty E hθ1)
    fun γ hγ => hγ.1

theorem upperAssouadSpectrum_le_one
    (E : Set ℝ) {θ : ℝ} (hθ1 : θ ≤ 1) :
    upperAssouadSpectrum E θ ≤ 1 := by
  rw [upperAssouadSpectrum_eq_sInf_admissibleExponents]
  apply csInf_le (upperAssouadAdmissibleExponents_bddBelow E θ)
  exact ⟨zero_le_one, hasUpperAssouadSpectrumExponent_one hθ1⟩

/-- Increasing the upper-spectrum scale parameter can only increase the
spectrum.  The interval assumptions ensure that the relevant admissible class
is nonempty. -/
theorem upperAssouadSpectrum_mono
    (E : Set ℝ) {θ θ' : ℝ} (hθθ' : θ ≤ θ') (hθ'1 : θ' ≤ 1) :
    upperAssouadSpectrum E θ ≤ upperAssouadSpectrum E θ' := by
  rw [upperAssouadSpectrum_eq_sInf_admissibleExponents,
    upperAssouadSpectrum_eq_sInf_admissibleExponents]
  apply csInf_le_csInf
  · exact upperAssouadAdmissibleExponents_bddBelow E θ
  · exact upperAssouadAdmissibleExponents_nonempty E hθ'1
  · intro γ hγ
    exact ⟨hγ.1,
      HasUpperAssouadSpectrumExponent.restrict_parameter hθθ' hγ.2⟩

/-- The monotonicity statement in the form used by left-limit arguments. -/
theorem upperAssouadSpectrum_monotoneOn (E : Set ℝ) :
    MonotoneOn (upperAssouadSpectrum E) (Icc (0 : ℝ) 1) := by
  intro θ hθ θ' hθ' hθθ'
  exact upperAssouadSpectrum_mono E hθθ' hθ'.2

/-- Any exponent strictly above the upper Assouad spectrum is an actual
covering exponent.  This is the `sInf` approximation principle that converts
dimension information into the finite-cover estimates used analytically. -/
theorem hasUpperAssouadSpectrumExponent_of_upperAssouadSpectrum_lt
    {E : Set ℝ} {θ γ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : upperAssouadSpectrum E θ < γ) :
    HasUpperAssouadSpectrumExponent E θ γ := by
  rw [upperAssouadSpectrum_eq_sInf_admissibleExponents] at hγ
  obtain ⟨γ', hγ', hγ'lt⟩ := exists_lt_of_csInf_lt
    (upperAssouadAdmissibleExponents_nonempty E hθ1) hγ
  exact HasUpperAssouadSpectrumExponent.of_le hθ0 hθ1 hγ'lt.le hγ'.2

/-- A direct usable form of the positive branch in quasi-Assouad regularity.
The ambient hypotheses `0 ≤ beta ≤ gamma` are normally supplied by the
dimension facts; `0 < gamma` rules out the separate zero-dimensional branch. -/
theorem IsQuasiAssouadRegular.upperSpectrum_eq
    {E : Set ℝ} {β γ θ : ℝ} (hregular : IsQuasiAssouadRegular E β γ)
    (hγ : 0 < γ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hthreshold : 1 - β / γ < θ) :
    upperAssouadSpectrum E θ = γ := by
  rcases hregular.2.2 with hzero | hspectrum
  · exact False.elim (ne_of_gt hγ hzero)
  · exact hspectrum θ hθ0 hθ1 hthreshold

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
