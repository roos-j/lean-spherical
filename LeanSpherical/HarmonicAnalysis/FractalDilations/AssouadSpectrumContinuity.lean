/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.AssouadSpectrumFacts

/-!
# Right continuity of the upper Assouad spectrum

The upper Assouad spectrum is monotone in its scale parameter, but the
quasi-Assouad-regular sharpness argument also needs its right continuity at a
phase transition.  This file proves the elementary interpolation estimate
directly from finite interval covers.  When an interval is shorter than the
old admissible scale, enlarge it to an interval of that old scale inside
`[1, 2]`.  No compactness or endpoint maximal-estimate argument is involved.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Set

noncomputable section

/-- An interval of length at most `D <= 1` in the radius interval is contained
in another interval of length exactly `D` in the same radius interval. -/
private theorem exists_enclosing_interval_of_length
    {a b D : ℝ} (hD : 0 < D) (hDone : D ≤ 1)
    (ha : 1 ≤ a) (_hab : a ≤ b) (hb : b ≤ 2) (hshort : b - a ≤ D) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ a' ≤ b' ∧ b' ≤ 2 ∧ b' - a' = D ∧
      Icc a b ⊆ Icc a' b' := by
  by_cases hright : a + D ≤ 2
  · refine ⟨a, a + D, ha, by linarith, hright, by ring, ?_⟩
    intro x hx
    constructor
    · exact hx.1
    · linarith [hx.2, hshort]
  · refine ⟨2 - D, 2, by linarith, by linarith, le_rfl, by ring, ?_⟩
    intro x hx
    constructor
    · have hleft : 2 - D < a := by linarith
      exact hleft.le.trans hx.1
    · exact hx.2.trans hb

/-- An upper-spectrum covering exponent at `theta` gives the interpolated
exponent at every larger parameter below one.  This is the local-covering
form of right continuity of the upper spectrum. -/
theorem HasUpperAssouadSpectrumExponent.lift_parameter
    {E : Set ℝ} {θ θ' s : ℝ}
    (hθ0 : 0 ≤ θ) (hθθ' : θ ≤ θ') (hθ' : θ' < 1) (hs : 0 ≤ s)
    (hE : HasUpperAssouadSpectrumExponent E θ s) :
    HasUpperAssouadSpectrumExponent E θ'
      (s * ((1 - θ) / (1 - θ'))) := by
  obtain ⟨C, hC, hcover⟩ := hE
  have hθ1 : θ ≤ 1 := hθθ'.trans hθ'.le
  have hθ'0 : 0 ≤ θ' := hθ0.trans hθθ'
  have hden : 0 < 1 - θ' := sub_pos.mpr hθ'
  have hratio : 1 ≤ (1 - θ) / (1 - θ') := by
    rw [le_div_iff₀ hden]
    linarith
  have hsle : s ≤ s * ((1 - θ) / (1 - θ')) := by
    exact le_mul_of_one_le_right hs hratio
  have ht0 : 0 ≤ s * ((1 - θ) / (1 - θ')) :=
    hs.trans hsle
  refine ⟨C, hC, ?_⟩
  intro δ a b hδ hδone ha hab hb hscale
  by_cases hlarge : δ ^ θ ≤ b - a
  · obtain ⟨ι, hι, hcard⟩ := hcover δ a b hδ hδone ha hab hb hlarge
    refine ⟨ι, hι, hcard.trans ?_⟩
    apply mul_le_mul_of_nonneg_left
    · have hδle : δ ≤ δ ^ θ' := by
        calc
          δ = δ ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ ≤ δ ^ θ' :=
            Real.rpow_le_rpow_of_exponent_ge hδ hδone.le hθ'.le
      have hbase : 1 ≤ (b - a) / δ := by
        rw [le_div_iff₀ hδ]
        simpa using hδle.trans hscale
      exact Real.rpow_le_rpow_of_exponent_le hbase hsle
    · exact hC.le
  · have hshort : b - a ≤ δ ^ θ := le_of_lt (lt_of_not_ge hlarge)
    have hDpos : 0 < δ ^ θ := Real.rpow_pos_of_pos hδ θ
    have hDone : δ ^ θ ≤ 1 := Real.rpow_le_one hδ.le hδone.le hθ0
    obtain ⟨a', b', ha', ha'b', hb', hlength, hcontain⟩ :=
      exists_enclosing_interval_of_length hDpos hDone ha hab hb hshort
    obtain ⟨ι, hι, hcard⟩ := hcover δ a' b' hδ hδone ha' ha'b' hb' (by
      exact hlength.symm.le)
    refine ⟨ι, hι.mono ?_, hcard.trans ?_⟩
    · intro x hx
      exact ⟨hx.1, hcontain hx.2⟩
    · apply mul_le_mul_of_nonneg_left
      · have hbase : 1 ≤ δ ^ (θ' - 1) := by
          apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδone.le
          linarith
        have hscale_div : δ ^ (θ' - 1) ≤ (b - a) / δ := by
          rw [Real.rpow_sub hδ θ' 1, Real.rpow_one]
          exact (div_le_div_iff_of_pos_right hδ).2 hscale
        have hexp :
            (θ' - 1) * (s * ((1 - θ) / (1 - θ'))) = (θ - 1) * s := by
          field_simp [ne_of_gt hden]
          ring
        have hpower_eq :
            (δ ^ (θ' - 1)) ^ (s * ((1 - θ) / (1 - θ'))) =
              (δ ^ θ / δ) ^ s := by
          calc
            (δ ^ (θ' - 1)) ^ (s * ((1 - θ) / (1 - θ'))) =
                δ ^ ((θ' - 1) * (s * ((1 - θ) / (1 - θ')))) := by
                  rw [Real.rpow_mul hδ.le]
            _ = δ ^ ((θ - 1) * s) := by rw [hexp]
            _ = (δ ^ (θ - 1)) ^ s := by
              rw [Real.rpow_mul hδ.le]
            _ = (δ ^ θ / δ) ^ s := by
              rw [Real.rpow_sub hδ θ 1, Real.rpow_one]
        calc
          ((b' - a') / δ) ^ s = (δ ^ θ / δ) ^ s := by rw [hlength]
          _ = (δ ^ (θ' - 1)) ^ (s * ((1 - θ) / (1 - θ'))) := hpower_eq.symm
          _ ≤ ((b - a) / δ) ^ (s * ((1 - θ) / (1 - θ'))) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hscale_div ht0
      · exact hC.le

/-- The corresponding inequality for the numerical upper spectrum.  In
particular, the spectrum has no upward jump immediately to the right of a
parameter below one. -/
theorem upperAssouadSpectrum_parameter_lift_le
    (E : Set ℝ) {θ θ' : ℝ}
    (hθ0 : 0 ≤ θ) (hθθ' : θ ≤ θ') (hθ' : θ' < 1) :
    upperAssouadSpectrum E θ' ≤
      upperAssouadSpectrum E θ * ((1 - θ) / (1 - θ')) := by
  have hθ1 : θ ≤ 1 := hθθ'.trans hθ'.le
  have hden : 0 < 1 - θ' := sub_pos.mpr hθ'
  have hratio : 0 < (1 - θ) / (1 - θ') := by
    apply div_pos
    · linarith
    · exact hden
  rw [upperAssouadSpectrum_eq_sInf_admissibleExponents,
    upperAssouadSpectrum_eq_sInf_admissibleExponents]
  let S : Set ℝ := upperAssouadAdmissibleExponents E θ
  let T : Set ℝ := upperAssouadAdmissibleExponents E θ'
  have hSbelow : BddBelow S := upperAssouadAdmissibleExponents_bddBelow E θ
  have hSne : S.Nonempty := upperAssouadAdmissibleExponents_nonempty E hθ1
  have hTbelow : BddBelow T := upperAssouadAdmissibleExponents_bddBelow E θ'
  by_contra hnot
  have hlt : sInf S * ((1 - θ) / (1 - θ')) < sInf T := lt_of_not_ge hnot
  have htarget : sInf S < sInf T / ((1 - θ) / (1 - θ')) := by
    apply (lt_div_iff₀ hratio).2
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hlt
  obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hSne htarget
  have hlift : HasUpperAssouadSpectrumExponent E θ'
      (s * ((1 - θ) / (1 - θ'))) :=
    hs.2.lift_parameter hθ0 hθθ' hθ' hs.1
  have hmem : s * ((1 - θ) / (1 - θ')) ∈ T := by
    refine ⟨?_, hlift⟩
    exact mul_nonneg hs.1 (div_nonneg (sub_nonneg.mpr hθ1) hden.le)
  have hle : sInf T ≤ s * ((1 - θ) / (1 - θ')) := csInf_le hTbelow hmem
  have hstrict : s * ((1 - θ) / (1 - θ')) < sInf T := by
    exact (lt_div_iff₀ hratio).mp hslt
  exact (not_lt_of_ge hle) hstrict

/-- Quasi-Assouad regularity supplies equality at the phase-transition
parameter itself, not only strictly above it.  The positive-Minkowski branch
is the one where that parameter lies below one; the zero-dimensional branch
is intentionally separate in the definition of regularity. -/
theorem IsQuasiAssouadRegular.upperSpectrum_eq_threshold
    {E : Set ℝ} {β γ : ℝ} (hregular : IsQuasiAssouadRegular E β γ)
    (hβ : 0 < β) (hβγ : β ≤ γ) :
    upperAssouadSpectrum E (1 - β / γ) = γ := by
  have hγ : 0 < γ := hβ.trans_le hβγ
  let θ₀ : ℝ := 1 - β / γ
  have hθ₀0 : 0 ≤ θ₀ := by
    dsimp [θ₀]
    apply sub_nonneg.mpr
    rw [div_le_one₀ hγ]
    simpa only [mul_one] using hβγ
  have hθ₀lt : θ₀ < 1 := by
    dsimp [θ₀]
    have hdiv : 0 < β / γ := div_pos hβ hγ
    linarith
  have hupper : upperAssouadSpectrum E θ₀ ≤ γ := by
    let θ₁ : ℝ := (θ₀ + 1) / 2
    have hθ₀θ₁ : θ₀ < θ₁ := by
      dsimp [θ₁]
      linarith
    have hθ₁0 : 0 ≤ θ₁ := hθ₀0.trans hθ₀θ₁.le
    have hθ₁lt : θ₁ < 1 := by
      dsimp [θ₁]
      linarith
    calc
      upperAssouadSpectrum E θ₀ ≤ upperAssouadSpectrum E θ₁ :=
        upperAssouadSpectrum_mono E hθ₀θ₁.le hθ₁lt.le
      _ = γ := hregular.upperSpectrum_eq hγ hθ₁0 hθ₁lt (by
        change θ₀ < θ₁
        exact hθ₀θ₁)
  apply le_antisymm hupper
  by_contra hnot
  have hsmall : upperAssouadSpectrum E θ₀ < γ := lt_of_not_ge hnot
  let r : ℝ := 1 - θ₀
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hA0 : 0 ≤ upperAssouadSpectrum E θ₀ :=
    upperAssouadSpectrum_nonneg E hθ₀lt.le
  have hquot :
      upperAssouadSpectrum E θ₀ * r / γ < r := by
    rw [div_lt_iff₀ hγ]
    nlinarith [mul_lt_mul_of_pos_right hsmall hr]
  obtain ⟨s, hslo, hshi⟩ := exists_between hquot
  let θ₁ : ℝ := 1 - s
  have hs : 0 < s := by
    have hnonneg : 0 ≤ upperAssouadSpectrum E θ₀ * r / γ :=
      div_nonneg (mul_nonneg hA0 hr.le) hγ.le
    exact hnonneg.trans_lt hslo
  have hθ₀θ₁ : θ₀ < θ₁ := by
    dsimp [θ₁, r] at hshi ⊢
    linarith
  have hθ₁0 : 0 ≤ θ₁ := hθ₀0.trans hθ₀θ₁.le
  have hθ₁lt : θ₁ < 1 := by
    dsimp [θ₁]
    linarith
  have hbound := upperAssouadSpectrum_parameter_lift_le E hθ₀0 hθ₀θ₁.le hθ₁lt
  have hbound' : upperAssouadSpectrum E θ₁ ≤
      upperAssouadSpectrum E θ₀ * r / s := by
    convert hbound using 1 <;> dsimp [θ₁, r] <;> ring
  have hratio : upperAssouadSpectrum E θ₀ * r / s < γ := by
    rw [div_lt_iff₀ hs]
    have h := (div_lt_iff₀ hγ).mp hslo
    nlinarith
  have hstrict : upperAssouadSpectrum E θ₁ < γ := hbound'.trans_lt hratio
  have heq : upperAssouadSpectrum E θ₁ = γ :=
    hregular.upperSpectrum_eq hγ hθ₁0 hθ₁lt (by
      change θ₀ < θ₁
      exact hθ₀θ₁)
  linarith

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
