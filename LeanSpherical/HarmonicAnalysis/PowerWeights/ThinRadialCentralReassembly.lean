/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.ThinRadialFiniteReassembly
import LeanSpherical.HarmonicAnalysis.PowerWeights.RelativeMovingOffWindow

/-!
# Central thin-radial reassembly

The entropy cap estimate controls the finitely many input pieces close to a
moving radius window.  The remaining pieces are put into two tail envelopes.
This file is the literal finite reassembly step: it keeps the windowed
relative band and all three moment inputs visible, so the strict-negative
argument can insert its cap and tail estimates without another operator
interface.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set
open scoped BigOperators ENNReal

noncomputable section

/-- On a normalized radius block the relative band maximal function is
pointwise finite.  Thus the raw `ENNReal` moment and the `toReal` moment
produced by the cap interpolation estimate are literally the same. -/
theorem restrictedRelativeBandpass_rpow_eq_ofReal_toReal_rpow
    {d : Nat} (hd : 0 < d) (E : Set Real) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex) (j : Nat)
    (f : SchwartzMap (Euclidean d) Complex) {p : Real} (hp : 0 ≤ p)
    (x : Euclidean d) :
    (restrictedRelativeBandpassSphericalMaximal d E phi j f x) ^ p =
      ENNReal.ofReal
        ((restrictedRelativeBandpassSphericalMaximal d E phi j f x).toReal ^ p) := by
  obtain ⟨C, hC, hphysical⟩ :=
    exists_restrictedRelativeBandpass_pointwise_le_integral hd phi
  have hfinite :
      restrictedRelativeBandpassSphericalMaximal d E phi j f x ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact hphysical j E hE f x
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp,
    ENNReal.ofReal_toReal hfinite]

/-- Integrated form of
`restrictedRelativeBandpass_rpow_eq_ofReal_toReal_rpow`. -/
theorem restrictedRelativeBandpass_lintegral_rpow_eq_lintegral_toReal_rpow
    {d : Nat} (hd : 0 < d) (E : Set Real) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex) (j : Nat)
    (f : SchwartzMap (Euclidean d) Complex) {p : Real} (hp : 0 ≤ p)
    (B : Set (Euclidean d)) (mu : Measure (Euclidean d)) :
    (∫⁻ x in B,
      (restrictedRelativeBandpassSphericalMaximal d E phi j f x) ^ p ∂mu) =
      ∫⁻ x in B, ENNReal.ofReal
        ((restrictedRelativeBandpassSphericalMaximal d E phi j f x).toReal ^ p) ∂mu := by
  apply lintegral_congr
  intro x
  exact restrictedRelativeBandpass_rpow_eq_ofReal_toReal_rpow
    hd E hE phi j f hp x

private theorem restrictedRelativeBandpassSphericalMaximal_finset_sum_le
    {n : Nat} (E : Set Real) (phi : SchwartzMap (Euclidean (n + 1)) Complex)
    (g : Nat → SchwartzMap (Euclidean (n + 1)) Complex) (S : Finset Nat)
    (hS : S.Nonempty) (j : Nat) (x : Euclidean (n + 1)) :
    restrictedRelativeBandpassSphericalMaximal (n + 1) E phi j
        (∑ m ∈ S, g m) x ≤
      ∑ m ∈ S,
        restrictedRelativeBandpassSphericalMaximal (n + 1) E phi j (g m) x := by
  obtain ⟨m, hm⟩ := hS
  have hsum : (∑ r ∈ S, g r) = g m + ∑ r ∈ S.erase m, g r := by
    rw [← Finset.sum_erase_add S g hm]
    ac_rfl
  rw [hsum]
  have h := restrictedRelativeBandpassSphericalMaximal_add_finset_sum_le
    E phi (g m) g (S.erase m) j x
  calc
    restrictedRelativeBandpassSphericalMaximal (n + 1) E phi j
        (g m + ∑ r ∈ S.erase m, g r) x ≤
        restrictedRelativeBandpassSphericalMaximal (n + 1) E phi j (g m) x +
          ∑ r ∈ S.erase m,
            restrictedRelativeBandpassSphericalMaximal (n + 1) E phi j (g r) x := h
    _ = ∑ r ∈ S,
        restrictedRelativeBandpassSphericalMaximal (n + 1) E phi j (g r) x := by
      rw [← Finset.sum_erase_add S (fun r =>
        restrictedRelativeBandpassSphericalMaximal (n + 1) E phi j (g r) x) hm]
      ac_rfl

private theorem lintegral_rpow_finset_sum_le
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (B : Set X)
    {p : Real} (hp : 1 ≤ p) (S : Finset Nat) (F : Nat → X → ENNReal)
    (hMeas : ∀ m ∈ S, Measurable (F m))
    (Q : Nat → ENNReal)
    (hQ : ∀ m ∈ S, (∫⁻ x in B, (F m x) ^ p ∂mu) ≤ Q m) :
    (∫⁻ x in B, (∑ m ∈ S, F m x) ^ p ∂mu) ≤
      ((S.card : ENNReal) ^ (p - 1)) * ∑ m ∈ S, Q m := by
  have hpoint (x : X) :
      (∑ m ∈ S, F m x) ^ p ≤
        ((S.card : ENNReal) ^ (p - 1)) * ∑ m ∈ S, (F m x) ^ p := by
    simpa only [Nat.cast_ofNat] using
      ENNReal.rpow_sum_le_const_mul_sum_rpow S (fun m => F m x) hp
  have hpowMeas : Measurable (fun x : X => ∑ m ∈ S, (F m x) ^ p) := by
    apply Finset.measurable_sum
    intro m hm
    exact ENNReal.continuous_rpow_const.measurable.comp (hMeas m hm)
  calc
    (∫⁻ x in B, (∑ m ∈ S, F m x) ^ p ∂mu) ≤
        ∫⁻ x in B, ((S.card : ENNReal) ^ (p - 1)) *
          ∑ m ∈ S, (F m x) ^ p ∂mu := by
      apply lintegral_mono
      intro x
      exact hpoint x
    _ = ((S.card : ENNReal) ^ (p - 1)) *
        ∑ m ∈ S, ∫⁻ x in B, (F m x) ^ p ∂mu := by
      rw [lintegral_const_mul _ hpowMeas]
      rw [lintegral_finsetSum]
      intro m hm
      exact ENNReal.continuous_rpow_const.measurable.comp (hMeas m hm)
    _ ≤ ((S.card : ENNReal) ^ (p - 1)) * ∑ m ∈ S, Q m := by
      gcongr with m hm
      exact hQ m hm

/-- Reassemble one nonempty thin radius window from its finite central block
and two already-controlled tails.  This is the local core of the central
shell argument; unlike the global window-cover lemma below, it does not
repeat the same decomposition over unrelated radius windows. -/
theorem restrictedRelativeBandpass_lintegral_rpow_le_of_one_thinRadiusWindow_tail_moments
    {n : Nat} (F : Set Real) {p : Real} (hp : 1 ≤ p)
    (phi : SchwartzMap (Euclidean (n + 1)) Complex) (j : Nat)
    (f : SchwartzMap (Euclidean (n + 1)) Complex)
    (g : Nat → SchwartzMap (Euclidean (n + 1)) Complex)
    (B : Set (Euclidean (n + 1))) (mu : Measure (Euclidean (n + 1)))
    (hB : MeasurableSet B) (C : Finset Nat)
    (fLow fHigh : SchwartzMap (Euclidean (n + 1)) Complex)
    (L H : Euclidean (n + 1) → ENNReal)
    (hC : C.Nonempty)
    (hsplit : f = (∑ m ∈ C, g m) + fLow + fHigh)
    (hcentralMeas : ∀ m ∈ C, Measurable (fun x : Euclidean (n + 1) =>
      restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j (g m) x))
    (hLMeas : Measurable L) (hHMeas : Measurable H)
    (hLowPoint : ∀ x ∈ B,
      restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j fLow x ≤ L x)
    (hHighPoint : ∀ x ∈ B,
      restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j fHigh x ≤ H x)
    (Q : Nat → ENNReal) (QL QH : ENNReal)
    (hcentral : ∀ m ∈ C,
      (∫⁻ x in B,
        (restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j (g m) x) ^ p ∂mu) ≤
          Q m)
    (hL : (∫⁻ x in B, (L x) ^ p ∂mu) ≤ QL)
    (hH : (∫⁻ x in B, (H x) ^ p ∂mu) ≤ QH) :
    (∫⁻ x in B,
      (restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j f x) ^ p ∂mu) ≤
      (2 ^ (p - 1) * 2 ^ (p - 1)) *
        (((C.card : ENNReal) ^ (p - 1) * ∑ m ∈ C, Q m) + QL + QH) := by
  let G : Euclidean (n + 1) → ENNReal := fun x =>
    ∑ m ∈ C, restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j (g m) x
  have hGmeas : Measurable G := by
    dsimp only [G]
    apply Finset.measurable_sum
    intro m hm
    exact hcentralMeas m hm
  have hGmoment : (∫⁻ x in B, (G x) ^ p ∂mu) ≤
      ((C.card : ENNReal) ^ (p - 1)) * ∑ m ∈ C, Q m := by
    dsimp only [G]
    apply lintegral_rpow_finset_sum_le mu B hp C
      (fun m x =>
        restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j (g m) x)
    · intro m hm
      exact hcentralMeas m hm
    · intro m hm
      exact hcentral m hm
  have hpoint (x : Euclidean (n + 1)) (hx : x ∈ B) :
      restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j f x ≤
        G x + L x + H x := by
    rw [hsplit]
    calc
      restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j
          ((∑ m ∈ C, g m) + fLow + fHigh) x ≤
          restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j
            ((∑ m ∈ C, g m) + fLow) x +
            restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j fHigh x :=
        restrictedRelativeBandpassSphericalMaximal_add_le F phi
          ((∑ m ∈ C, g m) + fLow) fHigh j x
      _ ≤
          (restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j
            (∑ m ∈ C, g m) x +
            restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j fLow x) +
              restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j fHigh x := by
          gcongr
          exact restrictedRelativeBandpassSphericalMaximal_add_le F phi
            (∑ m ∈ C, g m) fLow j x
      _ ≤ G x + L x + H x := by
          dsimp only [G]
          gcongr
          · exact restrictedRelativeBandpassSphericalMaximal_finset_sum_le
              F phi g C hC j x
          · exact hLowPoint x hx
          · exact hHighPoint x hx
  exact lintegral_rpow_restrict_le_of_le_add_add_of_moments mu B hp
    (restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j f)
    G L H hB hpoint
    (ENNReal.continuous_rpow_const.measurable.comp hGmeas)
    (ENNReal.continuous_rpow_const.measurable.comp hLMeas)
    (ENNReal.continuous_rpow_const.measurable.comp hHMeas)
    ((C.card : ENNReal) ^ (p - 1) * ∑ m ∈ C, Q m) QL QH
    hGmoment hL hH

/-- A finite thin-window cover together with central cap moments and the two
off-window tail moments controls one relative band on one output set.

The hypotheses are deliberately literal.  `g m` is the `m`-th thin radial
input piece, `C μ` is the central finite block for the radius window `μ`, and
`L μ`, `H μ` are the two pointwise tail envelopes.  A window with no radius
is allowed to have an empty central block. -/
theorem restrictedRelativeBandpass_lintegral_rpow_le_of_thinRadialCentral_tail_moments
    {n : Nat} (E : Set Real) {a b s p : Real} (hs : 0 < s) (hp : 1 ≤ p)
    (hE : E ⊆ Icc a b)
    (phi : SchwartzMap (Euclidean (n + 1)) Complex) (j : Nat)
    (f : SchwartzMap (Euclidean (n + 1)) Complex)
    (g : Nat → SchwartzMap (Euclidean (n + 1)) Complex)
    (B : Set (Euclidean (n + 1))) (mu : Measure (Euclidean (n + 1)))
    (hB : MeasurableSet B)
    (U : Finset Int) (hU : U = Finset.Icc ⌊a / s⌋ ⌈b / s⌉)
    (C : Int → Finset Nat)
    (fLow fHigh : Int → SchwartzMap (Euclidean (n + 1)) Complex)
    (L H : Int → Euclidean (n + 1) → ENNReal)
    (hcentral_or_empty : ∀ μ ∈ U,
      (C μ).Nonempty ∨ E ∩ thinRadiusWindow s μ = ∅)
    (hsplit : ∀ μ ∈ U,
      f = (∑ m ∈ C μ, g m) + fLow μ + fHigh μ)
    (hwindowMeas : ∀ μ ∈ U, Measurable (fun x : Euclidean (n + 1) =>
      restrictedRelativeBandpassSphericalMaximal (n + 1)
        (E ∩ thinRadiusWindow s μ) phi j f x))
    (hcentralMeas : ∀ μ ∈ U, ∀ m ∈ C μ,
      Measurable (fun x : Euclidean (n + 1) =>
        restrictedRelativeBandpassSphericalMaximal (n + 1)
          (E ∩ thinRadiusWindow s μ) phi j (g m) x))
    (hLMeas : ∀ μ ∈ U, Measurable (L μ))
    (hHMeas : ∀ μ ∈ U, Measurable (H μ))
    (hLowPoint : ∀ μ ∈ U, ∀ x ∈ B,
      restrictedRelativeBandpassSphericalMaximal (n + 1)
        (E ∩ thinRadiusWindow s μ) phi j (fLow μ) x ≤ L μ x)
    (hHighPoint : ∀ μ ∈ U, ∀ x ∈ B,
      restrictedRelativeBandpassSphericalMaximal (n + 1)
        (E ∩ thinRadiusWindow s μ) phi j (fHigh μ) x ≤ H μ x)
    (Q : Int → Nat → ENNReal) (QL QH : Int → ENNReal)
    (hcentral : ∀ μ ∈ U, ∀ m ∈ C μ,
      (∫⁻ x in B,
        (restrictedRelativeBandpassSphericalMaximal (n + 1)
          (E ∩ thinRadiusWindow s μ) phi j (g m) x) ^ p ∂mu) ≤ Q μ m)
    (hL : ∀ μ ∈ U, (∫⁻ x in B, (L μ x) ^ p ∂mu) ≤ QL μ)
    (hH : ∀ μ ∈ U, (∫⁻ x in B, (H μ x) ^ p ∂mu) ≤ QH μ) :
    (∫⁻ x in B,
      (restrictedRelativeBandpassSphericalMaximal (n + 1) E phi j f x) ^ p ∂mu) ≤
      ∑ μ ∈ U,
        (2 ^ (p - 1) * 2 ^ (p - 1)) *
          (((C μ).card : ENNReal) ^ (p - 1) * ∑ m ∈ C μ, Q μ m +
            QL μ + QH μ) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hwindowPowerMeas (μ : Int) (hμ : μ ∈ U) :
      Measurable (fun x : Euclidean (n + 1) =>
        (restrictedRelativeBandpassSphericalMaximal (n + 1)
          (E ∩ thinRadiusWindow s μ) phi j f x) ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp (hwindowMeas μ hμ)
  have hper (μ : Int) (hμ : μ ∈ U) :
      (∫⁻ x in B,
        (restrictedRelativeBandpassSphericalMaximal (n + 1)
          (E ∩ thinRadiusWindow s μ) phi j f x) ^ p ∂mu) ≤
        (2 ^ (p - 1) * 2 ^ (p - 1)) *
          (((C μ).card : ENNReal) ^ (p - 1) * ∑ m ∈ C μ, Q μ m +
            QL μ + QH μ) := by
    rcases hcentral_or_empty μ hμ with hC | hempty
    · let F : Set Real := E ∩ thinRadiusWindow s μ
      let G : Euclidean (n + 1) → ENNReal := fun x =>
        ∑ m ∈ C μ,
          restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j (g m) x
      have hGmeas : Measurable G := by
        dsimp only [G]
        apply Finset.measurable_sum
        intro m hm
        simpa only [F] using hcentralMeas μ hμ m hm
      have hGmoment : (∫⁻ x in B, (G x) ^ p ∂mu) ≤
          ((C μ).card : ENNReal) ^ (p - 1) * ∑ m ∈ C μ, Q μ m := by
        dsimp only [G]
        apply lintegral_rpow_finset_sum_le mu B hp (C μ)
          (fun m x =>
            restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j (g m) x)
        · intro m hm
          simpa only [F] using hcentralMeas μ hμ m hm
        · intro m hm
          simpa only [F] using hcentral μ hμ m hm
      have hpoint (x : Euclidean (n + 1)) (hx : x ∈ B) :
          restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j f x ≤
            G x + L μ x + H μ x := by
        rw [hsplit μ hμ]
        calc
          restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j
              ((∑ m ∈ C μ, g m) + fLow μ + fHigh μ) x ≤
              restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j
                ((∑ m ∈ C μ, g m) + fLow μ) x +
                restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j (fHigh μ) x :=
            restrictedRelativeBandpassSphericalMaximal_add_le F phi
              ((∑ m ∈ C μ, g m) + fLow μ) (fHigh μ) j x
          _ ≤
              (restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j
                (∑ m ∈ C μ, g m) x +
                restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j
                  (fLow μ) x) +
                restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j (fHigh μ) x := by
            gcongr
            exact restrictedRelativeBandpassSphericalMaximal_add_le F phi
              (∑ m ∈ C μ, g m) (fLow μ) j x
          _ ≤ G x + L μ x + H μ x := by
            dsimp only [G]
            gcongr
            · exact restrictedRelativeBandpassSphericalMaximal_finset_sum_le
                F phi g (C μ) hC j x
            · exact hLowPoint μ hμ x hx
            · exact hHighPoint μ hμ x hx
      simpa only [F, G] using
        (lintegral_rpow_restrict_le_of_le_add_add_of_moments mu B hp
          (restrictedRelativeBandpassSphericalMaximal (n + 1) F phi j f)
          G (L μ) (H μ) hB hpoint
          (ENNReal.continuous_rpow_const.measurable.comp hGmeas)
          (ENNReal.continuous_rpow_const.measurable.comp (hLMeas μ hμ))
          (ENNReal.continuous_rpow_const.measurable.comp (hHMeas μ hμ))
          (((C μ).card : ENNReal) ^ (p - 1) * ∑ m ∈ C μ, Q μ m)
          (QL μ) (QH μ) hGmoment (hL μ hμ) (hH μ hμ))
    · have hzero (h : SchwartzMap (Euclidean (n + 1)) Complex)
        (x : Euclidean (n + 1)) :
        restrictedRelativeBandpassSphericalMaximal (n + 1)
          (E ∩ thinRadiusWindow s μ) phi j h x = 0 := by
          rw [hempty]
          simp [restrictedRelativeBandpassSphericalMaximal]
      have hleft : (∫⁻ x in B,
          (restrictedRelativeBandpassSphericalMaximal (n + 1)
            (E ∩ thinRadiusWindow s μ) phi j f x) ^ p ∂mu) = 0 := by
        simp_rw [hzero f]
        simp [ENNReal.zero_rpow_of_pos hp0]
      rw [hleft]
      exact bot_le
  have hcover (x : Euclidean (n + 1)) :
      (restrictedRelativeBandpassSphericalMaximal (n + 1) E phi j f x) ^ p ≤
        ∑ μ ∈ U,
          (restrictedRelativeBandpassSphericalMaximal (n + 1)
            (E ∩ thinRadiusWindow s μ) phi j f x) ^ p := by
    simpa only [hU] using
      restrictedRelativeBandpassSphericalMaximal_rpow_le_sum_thinRadiusWindow
        E hs (lt_of_lt_of_le zero_lt_one hp) hE phi j f x
  calc
    (∫⁻ x in B,
      (restrictedRelativeBandpassSphericalMaximal (n + 1) E phi j f x) ^ p ∂mu) ≤
        ∫⁻ x in B, ∑ μ ∈ U,
          (restrictedRelativeBandpassSphericalMaximal (n + 1)
            (E ∩ thinRadiusWindow s μ) phi j f x) ^ p ∂mu := by
      apply lintegral_mono
      intro x
      exact hcover x
    _ = ∑ μ ∈ U,
        ∫⁻ x in B,
          (restrictedRelativeBandpassSphericalMaximal (n + 1)
            (E ∩ thinRadiusWindow s μ) phi j f x) ^ p ∂mu := by
      rw [lintegral_finsetSum]
      intro μ hμ
      exact hwindowPowerMeas μ hμ
    _ ≤ ∑ μ ∈ U,
        (2 ^ (p - 1) * 2 ^ (p - 1)) *
          (((C μ).card : ENNReal) ^ (p - 1) * ∑ m ∈ C μ, Q μ m +
            QL μ + QH μ) := by
      gcongr with μ hμ
      exact hper μ hμ

end

end LeanSpherical.HarmonicAnalysis
