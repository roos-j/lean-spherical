/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.RelativeMovingIntervalL2
import LeanSpherical.HarmonicAnalysis.PowerWeights.EntropyCenters
import LeanSpherical.HarmonicAnalysis.PowerWeights.AnnularInterpolation

/-!
# Entropy-covered square estimate for literal moving relative bands

The relative frequency cutoff is evaluated at `r • ξ`, so this is not a
consequence of the fixed-band entropy theorem.  This file applies the entropy
cover directly to the moving short-interval estimate.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory FourierTransform Metric Set intervalIntegral
open scoped BigOperators BoundedContinuousFunction ENNReal FourierTransform NNReal

noncomputable section

/-- A multiplicative entropy cover controls the literal moving relative
dyadic band.  The conclusion deliberately retains the interval-by-interval
coefficient; the annular interpolation step chooses the entropy scale and
then bounds this finite sum. -/
theorem exists_entropy_interval_lintegral_iSup_literal_relative_dyadic_moving_bandpass_of_sharp
    {d : Nat} (hd : 2 ≤ d) (C0 C1 : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ xi : Euclidean (d + 1), 1 ≤ ‖xi‖ →
      ‖surfaceFourier (d + 1) xi‖ ≤ C0 / ‖xi‖ ^ ((d : ℝ) / 2))
    (hderiv : ∀ xi : Euclidean (d + 1), ∀ r : ℝ, 1 ≤ ‖xi‖ →
      r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • xi)) r‖ ≤
        C1 / ‖xi‖ ^ ((d : ℝ) / 2 - 1))
    (phi f : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphi_norm : ∀ xi, ‖phi xi‖ ≤ 1) (j : Nat)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    (δ : ℝ≥0) (N : ℕ) (hN : multiplicativeEntropy E δ ≤ N)
    (hδ : Real.log 2 * (δ : ℝ) ≤ 1) :
    ∃ T : Finset (ℝ × ℝ), T.card ≤ N ∧
      (∀ q ∈ T, q.1 ≤ q.2) ∧
      (∀ q ∈ T, q.1 ∈ Icc (1 : ℝ) 2 ∧ q.2 ∈ Icc (1 : ℝ) 2) ∧
      (∀ q ∈ T, q.2 - q.1 ≤ 8 * Real.log 2 * (δ : ℝ)) ∧
      (∫⁻ x : Euclidean (d + 1),
        ⨆ r : ↥(E ∩ Ioi (0 : ℝ)), ENNReal.ofReal
          (‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
            surfaceFourier (d + 1) (-r.1 • xi) *
              (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
                phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
              𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ^ 2)) ≤
        ∑ q ∈ T, ENNReal.ofReal
          ((2 * ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
            2 * (q.2 - q.1) ^ 2 *
              (2 * ((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
                (12 * C0 *
                  ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) phi).toBoundedContinuousFunction‖) /
                  (dyadicScale j) ^ ((d : ℝ) / 2))) ^ 2) *
            ∫ xi : Euclidean (d + 1), ‖𝓕 (f : Euclidean (d + 1) → ℂ) xi‖ ^ 2) := by
  classical
  obtain ⟨T, hTcard, hordered, hcover, hTcells, hTbounds⟩ :=
    exists_finset_clipped_interval_cover_of_multiplicativeEntropy_le
      E hE hEne δ N hN
  refine ⟨T, hTcard, hordered, hTbounds, ?_, ?_⟩
  · intro q hq
    rcases hTcells q hq with ⟨s, hsE, hq⟩
    rw [hq]
    exact unitScaleEntropyCell_length_le_linear δ
      s (hE hsE) hδ
  let F : ℝ → Euclidean (d + 1) → ℂ := fun s x =>
    𝓕⁻ (fun xi : Euclidean (d + 1) =>
      surfaceFourier (d + 1) (-s • xi) *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (s • xi)) -
          phi (((2 : ℝ) ^ j)⁻¹ • (s • xi))) *
        𝓕 (f : Euclidean (d + 1) → ℂ) xi) x
  let Q : ℝ × ℝ → Euclidean (d + 1) → ENNReal := fun q x =>
    ⨆ r : Icc q.1 q.2, ENNReal.ofReal (‖F r.1 x‖ ^ 2)
  have hpoint (x : Euclidean (d + 1)) :
      (⨆ r : ↥(E ∩ Ioi (0 : ℝ)), ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ≤
        ∑ q ∈ T, Q q x := by
    apply iSup_le
    intro r
    rcases Set.mem_iUnion.mp (hcover r.2.1) with ⟨q, hq⟩
    rcases Set.mem_iUnion.mp hq with ⟨hqT, hrq⟩
    calc
      ENNReal.ofReal (‖F r.1 x‖ ^ 2) ≤ Q q x := by
        exact le_iSup (fun s : Icc q.1 q.2 =>
          ENNReal.ofReal (‖F s.1 x‖ ^ 2)) ⟨r.1, hrq⟩
      _ ≤ ∑ z ∈ T, Q z x :=
        Finset.single_le_sum (s := T) (f := fun z => Q z x)
          (fun _ _ => bot_le) hqT
  have hQmeas : ∀ q ∈ T, Measurable (Q q) := by
    intro q hq
    have hlocal :=
      measurable_and_lintegral_iSup_literal_relative_dyadic_moving_bandpass_interval_of_sharp
        hd C0 C1 hC0 hC1 hdecay hderiv phi f hphi_one hphi_zero hphi_norm j
        (hordered q hq) (hTbounds q hq).1.1 (hTbounds q hq).2.2
    simpa only [Q, F] using hlocal.1
  calc
    (∫⁻ x : Euclidean (d + 1),
      ⨆ r : ↥(E ∩ Ioi (0 : ℝ)), ENNReal.ofReal
        (‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
          surfaceFourier (d + 1) (-r.1 • xi) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
            𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ^ 2)) =
        ∫⁻ x : Euclidean (d + 1),
          ⨆ r : ↥(E ∩ Ioi (0 : ℝ)), ENNReal.ofReal (‖F r.1 x‖ ^ 2) := by
        simp only [F]
    _ ≤ ∫⁻ x : Euclidean (d + 1), ∑ q ∈ T, Q q x :=
      lintegral_mono hpoint
    _ = ∑ q ∈ T, ∫⁻ x : Euclidean (d + 1), Q q x := by
      exact lintegral_finsetSum T hQmeas
    _ ≤ ∑ q ∈ T, ENNReal.ofReal
        ((2 * ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
          2 * (q.2 - q.1) ^ 2 *
            (2 * ((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
              (12 * C0 *
                ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) phi).toBoundedContinuousFunction‖) /
                (dyadicScale j) ^ ((d : ℝ) / 2))) ^ 2) *
          ∫ xi : Euclidean (d + 1), ‖𝓕 (f : Euclidean (d + 1) → ℂ) xi‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hlocal :=
        measurable_and_lintegral_iSup_literal_relative_dyadic_moving_bandpass_interval_of_sharp
          hd C0 C1 hC0 hC1 hdecay hderiv phi f hphi_one hphi_zero hphi_norm j
          (hordered q hq) (hTbounds q hq).1.1 (hTbounds q hq).2.2
      simpa only [Q, F] using hlocal.2

/-- The preceding finite cover with its coefficients compressed using the
cardinality and common interval-length bounds.  This is the exact `L²`
constant used at a fixed spatial shell. -/
theorem exists_entropy_interval_lintegral_iSup_literal_relative_dyadic_moving_bandpass_le_of_sharp
    {d : Nat} (hd : 2 ≤ d) (C0 C1 : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ xi : Euclidean (d + 1), 1 ≤ ‖xi‖ →
      ‖surfaceFourier (d + 1) xi‖ ≤ C0 / ‖xi‖ ^ ((d : ℝ) / 2))
    (hderiv : ∀ xi : Euclidean (d + 1), ∀ r : ℝ, 1 ≤ ‖xi‖ →
      r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • xi)) r‖ ≤
        C1 / ‖xi‖ ^ ((d : ℝ) / 2 - 1))
    (phi f : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphi_norm : ∀ xi, ‖phi xi‖ ≤ 1) (j : Nat)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    (δ : ℝ≥0) (N : ℕ) (hN : multiplicativeEntropy E δ ≤ N)
    (hδ : Real.log 2 * (δ : ℝ) ≤ 1) :
    let B : ℝ := (4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)
    let C : ℝ := 2 *
      ((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
        (12 * C0 *
          ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) phi).toBoundedContinuousFunction‖) /
          (dyadicScale j) ^ ((d : ℝ) / 2))
    let L : ℝ := 8 * Real.log 2 * (δ : ℝ)
    let J : ℝ := ∫ xi : Euclidean (d + 1), ‖𝓕 (f : Euclidean (d + 1) → ℂ) xi‖ ^ 2
    ∃ T : Finset (ℝ × ℝ), T.card ≤ N ∧
      (∀ q ∈ T, q.1 ≤ q.2) ∧
      (∀ q ∈ T, q.1 ∈ Icc (1 : ℝ) 2 ∧ q.2 ∈ Icc (1 : ℝ) 2) ∧
      (∀ q ∈ T, q.2 - q.1 ≤ L) ∧
      (∫⁻ x : Euclidean (d + 1),
        ⨆ r : ↥(E ∩ Ioi (0 : ℝ)), ENNReal.ofReal
          (‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
            surfaceFourier (d + 1) (-r.1 • xi) *
              (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
                phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
              𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ^ 2)) ≤
        (N : ENNReal) * ENNReal.ofReal
          (2 * B ^ 2 + 2 * L ^ 2 * C ^ 2) * ENNReal.ofReal J := by
  dsimp only
  let B : ℝ := (4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)
  let C : ℝ := 2 *
    ((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
      (12 * C0 *
        ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) phi).toBoundedContinuousFunction‖) /
        (dyadicScale j) ^ ((d : ℝ) / 2))
  let L : ℝ := 8 * Real.log 2 * (δ : ℝ)
  let J : ℝ := ∫ xi : Euclidean (d + 1),
    ‖𝓕 (f : Euclidean (d + 1) → ℂ) xi‖ ^ 2
  obtain ⟨T, hcard, hordered, hends, hlength, hraw⟩ :=
    exists_entropy_interval_lintegral_iSup_literal_relative_dyadic_moving_bandpass_of_sharp
      hd C0 C1 hC0 hC1 hdecay hderiv phi f hphi_one hphi_zero hphi_norm j
      E hE hEne δ N hN hδ
  refine ⟨T, hcard, hordered, hends, ?_, ?_⟩
  · intro q hq
    simpa only [L] using hlength q hq
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun _ => sq_nonneg _
  have hcoef (q : ℝ × ℝ) :
      0 ≤ 2 * B ^ 2 + 2 * (q.2 - q.1) ^ 2 * C ^ 2 := by
    positivity
  have hfactor :
      (∑ q ∈ T, ENNReal.ofReal
        ((2 * B ^ 2 + 2 * (q.2 - q.1) ^ 2 * C ^ 2) * J)) =
        (∑ q ∈ T, ENNReal.ofReal
          (2 * B ^ 2 + 2 * (q.2 - q.1) ^ 2 * C ^ 2)) * ENNReal.ofReal J := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [ENNReal.ofReal_mul (hcoef q)]
  have hsum := entropy_interval_coefficient_sum_le T N B C L
    hcard hordered (fun q hq => by simpa only [L] using hlength q hq) hL
  calc
    (∫⁻ x : Euclidean (d + 1),
      ⨆ r : ↥(E ∩ Ioi (0 : ℝ)), ENNReal.ofReal
        (‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
          surfaceFourier (d + 1) (-r.1 • xi) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
            𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ^ 2)) ≤
        ∑ q ∈ T, ENNReal.ofReal
          ((2 * ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
            2 * (q.2 - q.1) ^ 2 *
              (2 * ((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
                (12 * C0 *
                  ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) phi).toBoundedContinuousFunction‖) /
                  (dyadicScale j) ^ ((d : ℝ) / 2))) ^ 2) *
            ∫ xi : Euclidean (d + 1), ‖𝓕 (f : Euclidean (d + 1) → ℂ) xi‖ ^ 2) := hraw
    _ = ∑ q ∈ T, ENNReal.ofReal
        ((2 * B ^ 2 + 2 * (q.2 - q.1) ^ 2 * C ^ 2) * J) := by
      simp only [B, C, J]
    _ = (∑ q ∈ T, ENNReal.ofReal
        (2 * B ^ 2 + 2 * (q.2 - q.1) ^ 2 * C ^ 2)) * ENNReal.ofReal J := hfactor
    _ ≤ ((N : ENNReal) * ENNReal.ofReal
        (2 * B ^ 2 + 2 * L ^ 2 * C ^ 2)) * ENNReal.ofReal J :=
      calc
        (∑ q ∈ T, ENNReal.ofReal
          (2 * B ^ 2 + 2 * (q.2 - q.1) ^ 2 * C ^ 2)) * ENNReal.ofReal J =
            ENNReal.ofReal J *
              (∑ q ∈ T, ENNReal.ofReal
                (2 * B ^ 2 + 2 * (q.2 - q.1) ^ 2 * C ^ 2)) := mul_comm _ _
        _ ≤ ENNReal.ofReal J *
            ((N : ENNReal) * ENNReal.ofReal
              (2 * B ^ 2 + 2 * L ^ 2 * C ^ 2)) :=
          mul_le_mul_right hsum (ENNReal.ofReal J)
        _ = ((N : ENNReal) * ENNReal.ofReal
            (2 * B ^ 2 + 2 * L ^ 2 * C ^ 2)) * ENNReal.ofReal J := mul_comm _ _
    _ = (N : ENNReal) * ENNReal.ofReal
        (2 * B ^ 2 + 2 * L ^ 2 * C ^ 2) * ENNReal.ofReal J := by ring

end

end LeanSpherical.HarmonicAnalysis
