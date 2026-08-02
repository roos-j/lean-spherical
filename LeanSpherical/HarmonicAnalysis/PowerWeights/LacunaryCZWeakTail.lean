/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.LacunaryCZAtomTail

/-!
# Exterior large-radius tails for lacunary Calderón--Zygmund atoms

The cancellation estimate for the future scales is global.  This file first
records the integrability behind that estimate, so it can be restricted to the
complement of the exceptional triple of an atom ball.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory FourierTransform Metric Set
open scoped BigOperators Convolution FourierTransform

noncomputable section

/-- The finite future tail can be restricted to the complement of the
exceptional triple of an atom ball without changing its global cancellation
bound. -/
theorem setIntegral_dyadic_lacunary_future_atom_tail_le
    {d : Nat} (psi : SchwartzMap (Euclidean d) ℂ)
    (r : ℤ → PositiveRadius) (hr : IsDyadicLacunaryRadiusSelector r)
    (j : ℕ) (K : ℤ) (S : Finset ℕ)
    (b : Euclidean d → ℂ) (hb : Integrable b)
    (hzero : (∫ y : Euclidean d, b y) = 0)
    {c : Euclidean d} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hbsupp : ∀ y, b y ≠ 0 → ‖y - c‖ ≤ ρ) :
    (∫ x : Euclidean d in (Metric.closedBall c (3 * ρ))ᶜ,
      ∑ n ∈ S, ‖∫ y : Euclidean d, b y *
        sphericalAverage d
          (fun z : Euclidean d =>
            ((((((2 : ℝ) ^ j)⁻¹ * (r (K + (n : ℤ)) : ℝ))⁻¹) ^ d : ℝ) : ℂ) •
              (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ)
                (((((2 : ℝ) ^ j)⁻¹ * (r (K + (n : ℤ)) : ℝ))⁻¹) • z))
          (r (K + (n : ℤ)) : ℝ) (x - y)‖) ≤
      surfaceMass d * ρ *
        (2 * (2 : ℝ) ^ j * ((2 : ℝ) ^ K)⁻¹) *
          (∫ x : Euclidean d,
            ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) :
              Euclidean d → ℂ) x‖) *
          (∫ y : Euclidean d, ‖b y‖) := by
  let s : ℕ → ℝ := fun n =>
    (((2 : ℝ) ^ j)⁻¹ * (r (K + (n : ℤ)) : ℝ))⁻¹
  let G : Euclidean d → ℝ := fun x =>
    ∑ n ∈ S, ‖∫ y : Euclidean d, b y *
      sphericalAverage d
        (fun z : Euclidean d => (((s n) ^ d : ℝ) : ℂ) •
          (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) ((s n) • z))
        (r (K + (n : ℤ)) : ℝ) (x - y)‖
  have hs (n : ℕ) (hn : n ∈ S) : 0 < s n := by
    dsimp [s]
    apply inv_pos.mpr
    exact mul_pos
      (inv_pos.mpr (pow_pos (by norm_num) _))
      (r (K + (n : ℤ))).2
  have hsingle (n : ℕ) (hn : n ∈ S) :
      Integrable (fun x : Euclidean d => ‖∫ y : Euclidean d, b y *
        sphericalAverage d
          (fun z : Euclidean d => (((s n) ^ d : ℝ) : ℂ) •
            (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) ((s n) • z))
          (r (K + (n : ℤ)) : ℝ) (x - y)‖) volume := by
    exact integrable_norm_sphericalAverage_complexScaled_fourierInv_atom
      psi (hs n hn) (r (K + (n : ℤ)) : ℝ) b hb
  have hG : Integrable G volume := by
    dsimp [G]
    exact integrable_finsetSum S hsingle
  have hGnonneg : 0 ≤ᵐ[volume] G := by
    filter_upwards with x
    dsimp [G]
    exact Finset.sum_nonneg fun n hn => norm_nonneg _
  have hrestrict :
      (∫ x : Euclidean d in (Metric.closedBall c (3 * ρ))ᶜ, G x) ≤
        ∫ x : Euclidean d, G x :=
    setIntegral_le_integral hG hGnonneg
  have hsum :
      (∫ x : Euclidean d, G x) =
        ∑ n ∈ S, ∫ x : Euclidean d, ‖∫ y : Euclidean d, b y *
          sphericalAverage d
            (fun z : Euclidean d => (((s n) ^ d : ℝ) : ℂ) •
              (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) ((s n) • z))
            (r (K + (n : ℤ)) : ℝ) (x - y)‖ := by
    dsimp [G]
    exact integral_finsetSum S hsingle
  have htail := dyadic_lacunary_future_atom_tail_le
    psi r hr j K S b hb hzero hρ hbsupp
  calc
    (∫ x : Euclidean d in (Metric.closedBall c (3 * ρ))ᶜ,
      ∑ n ∈ S, ‖∫ y : Euclidean d, b y *
        sphericalAverage d
          (fun z : Euclidean d =>
            ((((((2 : ℝ) ^ j)⁻¹ * (r (K + (n : ℤ)) : ℝ))⁻¹) ^ d : ℝ) : ℂ) •
              (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ)
                (((((2 : ℝ) ^ j)⁻¹ * (r (K + (n : ℤ)) : ℝ))⁻¹) • z))
          (r (K + (n : ℤ)) : ℝ) (x - y)‖) =
        ∫ x : Euclidean d in (Metric.closedBall c (3 * ρ))ᶜ, G x := by
          rfl
    _ ≤ ∫ x : Euclidean d, G x := hrestrict
    _ = ∑ n ∈ S, ∫ x : Euclidean d, ‖∫ y : Euclidean d, b y *
      sphericalAverage d
        (fun z : Euclidean d => (((s n) ^ d : ℝ) : ℂ) •
          (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) ((s n) • z))
        (r (K + (n : ℤ)) : ℝ) (x - y)‖ := hsum
    _ ≤ _ := by
      simpa only [s] using htail

/-- The exterior contributions of the small and large scales of one
mean-zero atom are controlled by the two explicit Calderón--Zygmund tails.
The caller uses a past set which omits the central scale and a future set
which contains it; no disjointness fact is needed by this analytic estimate. -/
theorem setIntegral_dyadic_lacunary_two_sided_atom_tail_le
    {d : Nat} (hd : 0 < d) (psi : SchwartzMap (Euclidean d) ℂ)
    (r : ℤ → PositiveRadius) (hr : IsDyadicLacunaryRadiusSelector r)
    (j : ℕ) (K : ℤ) (Sminus Splus : Finset ℕ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsmall : ∀ n ∈ Sminus, (r (K - (n : ℤ)) : ℝ) ≤ ρ)
    (c : Euclidean d) (b : Euclidean d → ℂ) (hb : Integrable b)
    (hzero : (∫ y : Euclidean d, b y) = 0)
    (hbsupp : ∀ y, b y ≠ 0 → ‖y - c‖ ≤ ρ) :
    (∫ x : Euclidean d in (Metric.closedBall c (3 * ρ))ᶜ,
      ∑ n ∈ Sminus, ‖∫ y : Euclidean d, b y *
        sphericalAverage d
          (fun z : Euclidean d =>
            ((((((2 : ℝ) ^ j)⁻¹ * (r (K - (n : ℤ)) : ℝ))⁻¹) ^ d : ℝ) : ℂ) •
              (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ)
                (((((2 : ℝ) ^ j)⁻¹ * (r (K - (n : ℤ)) : ℝ))⁻¹) • z))
          (r (K - (n : ℤ)) : ℝ) (x - y)‖) +
      (∫ x : Euclidean d in (Metric.closedBall c (3 * ρ))ᶜ,
        ∑ n ∈ Splus, ‖∫ y : Euclidean d, b y *
          sphericalAverage d
            (fun z : Euclidean d =>
              ((((((2 : ℝ) ^ j)⁻¹ * (r (K + (n : ℤ)) : ℝ))⁻¹) ^ d : ℝ) : ℂ) •
                (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ)
                  (((((2 : ℝ) ^ j)⁻¹ * (r (K + (n : ℤ)) : ℝ))⁻¹) • z))
            (r (K + (n : ℤ)) : ℝ) (x - y)‖) ≤
      (((((2 : ℝ) ^ j)⁻¹) ^ 2 *
          SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) *
          ((16 / 3 : ℝ) * ((2 : ℝ) ^ K) ^ 2) *
          surfaceMass d * (∫ y : Euclidean d, ‖b y‖)) *
        (surfaceMass d * (3 : ℝ) ^ d / (2 * ρ ^ 2))) +
      (surfaceMass d * ρ *
        (2 * (2 : ℝ) ^ j * ((2 : ℝ) ^ K)⁻¹) *
          (∫ x : Euclidean d,
            ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) :
              Euclidean d → ℂ) x‖) *
          (∫ y : Euclidean d, ‖b y‖)) := by
  apply add_le_add
  · exact setIntegral_dyadic_lacunary_past_small_radius_atom_signed_tail_le
      hd psi r hr j K Sminus hρ hsmall c b hb hbsupp
  · exact setIntegral_dyadic_lacunary_future_atom_tail_le
      psi r hr j K Splus b hb hzero hρ.le hbsupp

end

end LeanSpherical.HarmonicAnalysis
