/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.Admissibility
import LeanSpherical.HarmonicAnalysis.PowerWeights.EntropyRegularity

/-!
# Strict perturbations of the implicit parameter condition

The upper estimate is proved in the strict interior.  This elementary
calculation moves a boundary point into that interior while preserving the
relative amount by which the Legendre--Assouad parameter is allowed to grow.
-/

namespace LeanSpherical.HarmonicAnalysis

open Set

noncomputable section

/-- Increasing `p` by `ε` and `α` by half the dimensional increment makes a
non-strict implicit condition strict.  This is the parameter perturbation
used for the negative-weight, subquadratic upper estimate. -/
theorem powerWeightEntropyImplicitCondition_strict_add_half_dim
    {d : ℕ} (hd : 2 ≤ d) (E : Set ℝ) (p α ε : ℝ) (hε : 0 < ε)
    (h : powerWeightEntropyImplicitCondition d E p α) :
    max (((α + (((d : ℝ) - 1) / 2) * ε : ℝ) : EReal) +
        multiplicativeMinkowskiExponent E)
      (multiplicativeLegendreAssouadExponent E
        (((d : ℝ) - 1) * ((p + ε) - 2) -
          (α + (((d : ℝ) - 1) / 2) * ε))) <
      ((((d : ℝ) - 1) * ((p + ε) - 1) : ℝ) : EReal) := by
  let m : ℝ := (d : ℝ) - 1
  let δ : ℝ := (m / 2) * ε
  let T : ℝ := m * (p - 1)
  let ρ : ℝ := m * (p - 2) - α
  have hm : 0 < m := by
    dsimp only [m]
    have hdone : (1 : ℝ) < d := by
      exact_mod_cast (show 1 < d by omega)
    linarith
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hδle : 0 ≤ δ := hδ.le
  have hmε : 0 < m * ε := mul_pos hm hε
  have hδlt : δ < m * ε := by
    dsimp only [δ]
    nlinarith
  have hleft : (α : EReal) + multiplicativeMinkowskiExponent E ≤ (T : EReal) := by
    have := (le_max_left
      ((α : EReal) + multiplicativeMinkowskiExponent E)
      (multiplicativeLegendreAssouadExponent E ρ)).trans h
    simpa only [T, ρ, m] using this
  have hright : multiplicativeLegendreAssouadExponent E ρ ≤ (T : EReal) := by
    have := (le_max_right
      ((α : EReal) + multiplicativeMinkowskiExponent E)
      (multiplicativeLegendreAssouadExponent E ρ)).trans h
    simpa only [T, ρ, m] using this
  have hTδ : T + δ < T + m * ε := by linarith
  have hTδE : (T : EReal) + (δ : EReal) < ((T + m * ε : ℝ) : EReal) := by
    exact_mod_cast hTδ
  have hfirst : ((α + δ : ℝ) : EReal) + multiplicativeMinkowskiExponent E <
      ((T + m * ε : ℝ) : EReal) := by
    calc
      ((α + δ : ℝ) : EReal) + multiplicativeMinkowskiExponent E =
          ((α : EReal) + multiplicativeMinkowskiExponent E) + (δ : EReal) := by
            push_cast
            ac_rfl
      _ ≤ (T : EReal) + (δ : EReal) := by
        simpa only [add_comm] using add_le_add_left hleft (δ : EReal)
      _ < ((T + m * ε : ℝ) : EReal) := hTδE
  have hρ : ρ ≤ ρ + δ := le_add_of_nonneg_right hδle
  have hregular := multiplicativeLegendreAssouadExponent_le_add_sub E hρ
  have hregular' : multiplicativeLegendreAssouadExponent E (ρ + δ) ≤
      multiplicativeLegendreAssouadExponent E ρ + (δ : EReal) := by
    convert hregular using 1
    all_goals
      dsimp only [ρ]
      ring_nf
  have hsecond : multiplicativeLegendreAssouadExponent E (ρ + δ) <
      ((T + m * ε : ℝ) : EReal) := by
    calc
      multiplicativeLegendreAssouadExponent E (ρ + δ) ≤
          multiplicativeLegendreAssouadExponent E ρ + (δ : EReal) := hregular'
      _ ≤ (T : EReal) + (δ : EReal) := by
        simpa only [add_comm] using add_le_add_left hright (δ : EReal)
      _ < ((T + m * ε : ℝ) : EReal) := hTδE
  have hmain := max_lt hfirst hsecond
  have harg :
      ((d : ℝ) - 1) * ((p + ε) - 2) -
          (α + (((d : ℝ) - 1) / 2) * ε) = ρ + δ := by
    dsimp only [ρ, δ, m]
    ring
  have hbound : ((d : ℝ) - 1) * ((p + ε) - 1) = T + m * ε := by
    dsimp only [T, m]
    ring
  simpa only [harg, hbound, δ, m] using hmain

/-- A non-strict admissible point in the negative, subquadratic regime can
be perturbed into the strict regime without leaving that regime.  This is
the parameter form used before applying the local upper estimate. -/
theorem exists_strict_negative_subquadratic_perturbation
    {d : ℕ} (hd : 2 ≤ d) (E : Set ℝ) {p α : ℝ}
    (_hp : 1 < p) (hp2 : p < 2) (hα : α < 0)
    (h : powerWeightEntropyImplicitCondition d E p α) :
    ∃ ε : ℝ, 0 < ε ∧ p + ε < 2 ∧
      α + (((d : ℝ) - 1) / 2) * ε < 0 ∧
      max (((α + (((d : ℝ) - 1) / 2) * ε : ℝ) : EReal) +
          multiplicativeMinkowskiExponent E)
        (multiplicativeLegendreAssouadExponent E
          (((d : ℝ) - 1) * ((p + ε) - 2) -
            (α + (((d : ℝ) - 1) / 2) * ε))) <
        ((((d : ℝ) - 1) * ((p + ε) - 1) : ℝ) : EReal) := by
  let m : ℝ := (d : ℝ) - 1
  have hm : 0 < m := by
    dsimp only [m]
    have hdone : (1 : ℝ) < d := by
      exact_mod_cast (show 1 < d by omega)
    linarith
  have hmargin : 0 < min (2 - p) ((-2 * α) / m) := by
    apply lt_min
    · linarith
    · exact div_pos (by linarith) hm
  obtain ⟨ε, hε, hεmargin⟩ := exists_between hmargin
  have hεp : ε < 2 - p := lt_of_lt_of_le hεmargin (min_le_left _ _)
  have hεα : ε < (-2 * α) / m :=
    lt_of_lt_of_le hεmargin (min_le_right _ _)
  have hcross : ε * m < -2 * α := (lt_div_iff₀ hm).mp hεα
  refine ⟨ε, hε, by linarith, ?_, ?_⟩
  · dsimp only [m] at hcross
    nlinarith
  · simpa only [m] using
      (powerWeightEntropyImplicitCondition_strict_add_half_dim hd E p α ε hε h)

/-- The preceding strict perturbation can be taken arbitrarily small.  This
is the version used to put a non-strict negative subquadratic parameter on
the closure of the strict strong-type range. -/
theorem exists_strict_negative_subquadratic_perturbation_lt
    {d : ℕ} (hd : 2 ≤ d) (E : Set ℝ) {p α η : ℝ}
    (_hp : 1 < p) (hp2 : p < 2) (hα : α < 0) (hη : 0 < η)
    (h : powerWeightEntropyImplicitCondition d E p α) :
    ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ p + ε < 2 ∧
      α + (((d : ℝ) - 1) / 2) * ε < 0 ∧
      max (((α + (((d : ℝ) - 1) / 2) * ε : ℝ) : EReal) +
          multiplicativeMinkowskiExponent E)
        (multiplicativeLegendreAssouadExponent E
          (((d : ℝ) - 1) * ((p + ε) - 2) -
            (α + (((d : ℝ) - 1) / 2) * ε))) <
        ((((d : ℝ) - 1) * ((p + ε) - 1) : ℝ) : EReal) := by
  let m : ℝ := (d : ℝ) - 1
  have hm : 0 < m := by
    dsimp only [m]
    have hdone : (1 : ℝ) < d := by
      exact_mod_cast (show 1 < d by omega)
    linarith
  have hmargin : 0 < min η (min (2 - p) ((-2 * α) / m)) := by
    apply lt_min
    · exact hη
    · apply lt_min
      · linarith
      · exact div_pos (by linarith) hm
  obtain ⟨ε, hε, hεmargin⟩ := exists_between hmargin
  have hεη : ε < η :=
    lt_of_lt_of_le hεmargin (min_le_left _ _)
  have hεp : ε < 2 - p :=
    lt_of_lt_of_le hεmargin
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεα : ε < (-2 * α) / m :=
    lt_of_lt_of_le hεmargin
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have hcross : ε * m < -2 * α := (lt_div_iff₀ hm).mp hεα
  refine ⟨ε, hε, hεη, by linarith, ?_, ?_⟩
  · dsimp only [m] at hcross
    nlinarith
  · simpa only [m] using
      (powerWeightEntropyImplicitCondition_strict_add_half_dim hd E p α ε hε h)

end

end LeanSpherical.HarmonicAnalysis
