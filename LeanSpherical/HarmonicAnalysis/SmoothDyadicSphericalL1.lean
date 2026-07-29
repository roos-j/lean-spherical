/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SmoothDyadicSchwartz
import LeanSpherical.HarmonicAnalysis.SphericalMaximalL1
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Local `L¹` smooth dyadic spherical maximal estimate

This module proves the compact-radius `L¹` endpoint for an explicit smooth
dyadic bandpass in arbitrary Euclidean dimension.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory FourierTransform Metric Set intervalIntegral
open scoped BoundedContinuousFunction Convolution FourierTransform

noncomputable section

/-- A compact-radius `L¹` maximal estimate for an explicit smooth dyadic
bandpass in every Euclidean dimension. This is the genuine radius-Sobolev
endpoint used before interpolation. -/
theorem exists_smooth_dyadic_sphericalMaximal_l1
    {d : Nat} (φ f : SchwartzMap (Euclidean d) ℂ) (j : Nat) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ)) ∧
      (∫⁻ x : Euclidean d,
        ⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal
            ‖sphericalAverage d
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖) ≤
        ENNReal.ofReal
          (surfaceMass d *
            (2 * (∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
              3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖fderiv ℝ
                  ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))) := by
  rcases exists_schwartzMap_smooth_dyadic_bandpass φ j with ⟨ψ, hψ⟩
  refine ⟨ψ, hψ, ?_⟩
  let R : ℝ := (2 : ℝ) ^ j
  let S : ℝ := (2 : ℝ) ^ (j + 1)
  let A_R : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 R⁻¹ (inv_ne_zero (by positivity : R ≠ 0)))
  let A_S : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 S⁻¹ (inv_ne_zero (by positivity : S ≠ 0)))
  let φR : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A_R) φ
  let φS : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A_S) φ
  let pR : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (φR : Euclidean d → ℂ) (𝓕 f))
  let pS : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (φS : Euclidean d → ℂ) (𝓕 f))
  let p : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f))
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hS : 0 < S := by
    dsimp only [S]
    positivity
  have hφR (ξ : Euclidean d) : φR ξ = φ (R⁻¹ • ξ) := by
    change φ (A_R ξ) = φ (R⁻¹ • ξ)
    simp [A_R]
  have hφS (ξ : Euclidean d) : φS ξ = φ (S⁻¹ • ξ) := by
    change φ (A_S ξ) = φ (S⁻¹ • ξ)
    simp [A_S]
  have hpR (x : Euclidean d) : pR x =
      𝓕⁻ (fun ξ : Euclidean d => φ (R⁻¹ • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x := by
    dsimp [pR]
    rw [SchwartzMap.fourierInv_coe]
    simp only [SchwartzMap.smulLeftCLM_apply φR.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul]
    congr 2
  have hpS (x : Euclidean d) : pS x =
      𝓕⁻ (fun ξ : Euclidean d => φ (S⁻¹ • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x := by
    dsimp [pS]
    rw [SchwartzMap.fourierInv_coe]
    simp only [SchwartzMap.smulLeftCLM_apply φS.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul]
    congr 2
  have hpR_fun : (pR : Euclidean d → ℂ) =
      fun x => 𝓕⁻ (fun ξ : Euclidean d => φ (R⁻¹ • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x := by
    funext x
    exact hpR x
  have hpS_fun : (pS : Euclidean d → ℂ) =
      fun x => 𝓕⁻ (fun ξ : Euclidean d => φ (S⁻¹ • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x := by
    funext x
    exact hpS x
  have hp_split (x : Euclidean d) : p x = pS x - pR x := by
    dsimp [p]
    rw [SchwartzMap.fourierInv_coe]
    simp only [SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul]
    rw [hpS x, hpR x]
    have hmult : (fun ξ : Euclidean d => ψ ξ *
        𝓕 (f : Euclidean d → ℂ) ξ) =
        fun ξ => (φS ξ - φR ξ) * 𝓕 (f : Euclidean d → ℂ) ξ := by
      funext ξ
      rw [hψ ξ, hφS ξ, hφR ξ]
    rw [hmult]
    exact fourierInv_sub_schwartz_multiplier φS φR f x
  have hp_fun : (p : Euclidean d → ℂ) = fun x => pS x - pR x := by
    funext x
    exact hp_split x
  have hpL1 :
      (∫ x : Euclidean d, ‖p x‖) ≤
        2 * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) := by
    rw [hp_fun]
    calc
      (∫ x : Euclidean d, ‖pS x - pR x‖) ≤
          ∫ x : Euclidean d, (‖pS x‖ + ‖pR x‖) := by
        apply MeasureTheory.integral_mono
        · exact (pS.integrable.sub pR.integrable).norm
        · exact pS.integrable.norm.add pR.integrable.norm
        · intro x
          exact norm_sub_le _ _
      _ = (∫ x : Euclidean d, ‖pS x‖) + ∫ x : Euclidean d, ‖pR x‖ := by
        rw [integral_add pS.integrable.norm pR.integrable.norm]
      _ ≤ (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
          (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) := by
        apply add_le_add
        · change (∫ x : Euclidean d, ‖(pS : Euclidean d → ℂ) x‖) ≤ _
          rw [hpS_fun]
          exact integral_norm_fourierInv_scaled_schwartz_multiplier_le φ f hS
        · change (∫ x : Euclidean d, ‖(pR : Euclidean d → ℂ) x‖) ≤ _
          rw [hpR_fun]
          exact integral_norm_fourierInv_scaled_schwartz_multiplier_le φ f hR
      _ = 2 * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) := by
        ring
  let dpR : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) pR
  let dpS : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) pS
  let dp : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) p
  have hdpR (x : Euclidean d) : dpR x =
      fderiv ℝ (pR : Euclidean d → ℂ) x := by
    exact SchwartzMap.fderivCLM_apply ℂ pR x
  have hdpS (x : Euclidean d) : dpS x =
      fderiv ℝ (pS : Euclidean d → ℂ) x := by
    exact SchwartzMap.fderivCLM_apply ℂ pS x
  have hdp (x : Euclidean d) : dp x =
      fderiv ℝ (p : Euclidean d → ℂ) x := by
    exact SchwartzMap.fderivCLM_apply ℂ p x
  have hpderiv_split (x : Euclidean d) :
      fderiv ℝ (p : Euclidean d → ℂ) x = dpS x - dpR x := by
    rw [hdpS x, hdpR x, hp_fun]
    exact fderiv_sub pS.differentiableAt pR.differentiableAt
  have hpderivL1 :
      (∫ x : Euclidean d, ‖fderiv ℝ (p : Euclidean d → ℂ) x‖) ≤
        S * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) +
          R * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) := by
    calc
      (∫ x : Euclidean d, ‖fderiv ℝ (p : Euclidean d → ℂ) x‖) =
          ∫ x : Euclidean d,
        ‖dpS x - dpR x‖ := by
        congr with x
        rw [hpderiv_split x]
      _ ≤
          ∫ x : Euclidean d, (‖dpS x‖ + ‖dpR x‖) := by
        apply MeasureTheory.integral_mono
        · exact (dpS.integrable.sub dpR.integrable).norm
        · exact dpS.integrable.norm.add dpR.integrable.norm
        · intro x
          exact norm_sub_le _ _
      _ = (∫ x : Euclidean d, ‖dpS x‖) + ∫ x : Euclidean d, ‖dpR x‖ := by
        rw [MeasureTheory.integral_add dpS.integrable.norm dpR.integrable.norm]
      _ ≤ S * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) +
          R * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) := by
        apply add_le_add
        · calc
            (∫ x : Euclidean d, ‖dpS x‖) =
                ∫ x : Euclidean d, ‖fderiv ℝ (fun y : Euclidean d =>
                  𝓕⁻ (fun ξ : Euclidean d => φ (S⁻¹ • ξ) *
                    𝓕 (f : Euclidean d → ℂ) ξ) y) x‖ := by
              congr with x
              rw [hdpS x, hpS_fun]
            _ ≤ _ :=
              integral_norm_fderiv_fourierInv_scaled_schwartz_multiplier_le φ f hS
        · calc
            (∫ x : Euclidean d, ‖dpR x‖) =
                ∫ x : Euclidean d, ‖fderiv ℝ (fun y : Euclidean d =>
                  𝓕⁻ (fun ξ : Euclidean d => φ (R⁻¹ • ξ) *
                    𝓕 (f : Euclidean d → ℂ) ξ) y) x‖ := by
              congr with x
              rw [hdpR x, hpR_fun]
            _ ≤ _ :=
              integral_norm_fderiv_fourierInv_scaled_schwartz_multiplier_le φ f hR
  have hpderivbound (x : Euclidean d) :
      ‖fderiv ℝ (p : Euclidean d → ℂ) x‖ ≤
        ‖dp.toBoundedContinuousFunction‖ := by
    calc
      ‖fderiv ℝ (p : Euclidean d → ℂ) x‖ = ‖dp x‖ := by rw [hdp x]
      _ = ‖dp.toBoundedContinuousFunction x‖ := rfl
      _ ≤ ‖dp.toBoundedContinuousFunction‖ :=
        BoundedContinuousFunction.norm_coe_le_norm dp.toBoundedContinuousFunction x
  have hp : ContDiff ℝ 1 (p : Euclidean d → ℂ) := by
    simpa only [p, WithTop.coe_one] using p.smooth (1 : ℕ∞)
  have hpderiv_integrable : Integrable (fderiv ℝ (p : Euclidean d → ℂ)) volume := by
    have hdp_fun : (dp : Euclidean d → (Euclidean d →L[ℝ] ℂ)) =
        fderiv ℝ (p : Euclidean d → ℂ) := by
      funext x
      exact hdp x
    rw [← hdp_fun]
    exact dp.integrable
  have hlocal :=
    lintegral_iSup_ennreal_norm_sphericalAverage_le_local_radiusSobolev
      (p : Euclidean d → ℂ)
      hp
      p.integrable
      hpderiv_integrable
      hpderivbound (by norm_num : (1 : ℝ) ≤ 2)
  change (∫⁻ x : Euclidean d,
    ⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal ‖sphericalAverage d (p : Euclidean d → ℂ) r.1 x‖) ≤ _
  calc
    (∫⁻ x : Euclidean d,
      ⨆ r : Icc (1 : ℝ) 2,
        ENNReal.ofReal ‖sphericalAverage d (p : Euclidean d → ℂ) r.1 x‖) ≤
        ENNReal.ofReal (surfaceMass d *
          ((∫ x : Euclidean d, ‖p x‖) +
            (2 - 1) * (∫ x : Euclidean d,
              ‖fderiv ℝ (p : Euclidean d → ℂ) x‖))) := hlocal
    _ ≤ ENNReal.ofReal
        (surfaceMass d *
          (2 * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
            3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖fderiv ℝ
                ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))) := by
      apply ENNReal.ofReal_le_ofReal
      have hmass : 0 ≤ surfaceMass d := measureReal_nonneg
      apply mul_le_mul_of_nonneg_left _ hmass
      rw [show (2 - 1 : ℝ) = 1 by norm_num, one_mul]
      calc
        (∫ x : Euclidean d, ‖p x‖) +
            ∫ x : Euclidean d, ‖fderiv ℝ (p : Euclidean d → ℂ) x‖ ≤
            (2 * (∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖)) +
              (S * (∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖fderiv ℝ
                  ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) +
                R * (∫ x : Euclidean d, ‖f x‖) *
                  (∫ x : Euclidean d, ‖fderiv ℝ
                    ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)) :=
          add_le_add hpL1 hpderivL1
        _ = 2 * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
            3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖fderiv ℝ
                ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖) := by
          dsimp only [R, S]
          ring

/-- The dyadic multiplier can be chosen once, independently of the Schwartz
input, for the compact-radius `L¹` endpoint. -/
theorem exists_smooth_dyadic_sphericalMaximal_l1_uniform
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ) (j : Nat) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ)) ∧
      ∀ f : SchwartzMap (Euclidean d) ℂ,
        (∫⁻ x : Euclidean d,
          ⨆ r : Icc (1 : ℝ) 2,
            ENNReal.ofReal
              ‖sphericalAverage d
                ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                  SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖) ≤
          ENNReal.ofReal
            (surfaceMass d *
              (2 * (∫ x : Euclidean d, ‖f x‖) *
                  (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
                3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
                  (∫ x : Euclidean d, ‖fderiv ℝ
                    ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))) := by
  rcases exists_schwartzMap_smooth_dyadic_bandpass φ j with ⟨ψ, hψ⟩
  refine ⟨ψ, hψ, ?_⟩
  intro f
  rcases exists_smooth_dyadic_sphericalMaximal_l1 φ f j with ⟨χ, hχ, hbound⟩
  have hχψ : χ = ψ :=
    schwartzMap_eq_of_eq_smooth_dyadic_bandpass hχ hψ
  rw [hχψ] at hbound
  exact hbound

/-- The lower-order term in the local `L¹` endpoint is absorbed by the
geometric dyadic scale. -/
theorem smooth_dyadic_l1_coefficient_le_geometric (j : Nat) {A B : ℝ}
    (hA : 0 ≤ A) :
    2 * A + 3 * (2 : ℝ) ^ j * B ≤
      (2 : ℝ) ^ j * (2 * A + 3 * B) := by
  let s : ℝ := (2 : ℝ) ^ j
  have hsone : 1 ≤ s := by
    dsimp only [s]
    exact one_le_pow₀ (by norm_num)
  change 2 * A + 3 * s * B ≤ s * (2 * A + 3 * B)
  nlinarith

/-- The fixed literal smooth dyadic bandpass has a local `L¹` bound with a
single explicit `2^j` coefficient, uniformly for every Schwartz input. -/
theorem exists_smooth_dyadic_sphericalMaximal_l1_uniform_geometric
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ) (j : Nat) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ)) ∧
      ∀ f : SchwartzMap (Euclidean d) ℂ,
        (∫⁻ x : Euclidean d,
          ⨆ r : Icc (1 : ℝ) 2,
            ENNReal.ofReal
              ‖sphericalAverage d
                ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                  SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖) ≤
          ENNReal.ofReal
            (surfaceMass d * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
              (2 * (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
                3 * (∫ x : Euclidean d, ‖fderiv ℝ
                  ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))) := by
  rcases exists_smooth_dyadic_sphericalMaximal_l1_uniform φ j with ⟨ψ, hψ, hbound⟩
  refine ⟨ψ, hψ, ?_⟩
  intro f
  refine (hbound f).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hA : 0 ≤ (∫ x : Euclidean d, ‖f x‖) *
      (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) := by
    apply mul_nonneg
    · exact integral_nonneg fun _ => norm_nonneg _
    · exact integral_nonneg fun _ => norm_nonneg _
  have hcoefficient := smooth_dyadic_l1_coefficient_le_geometric (A :=
      (∫ x : Euclidean d, ‖f x‖) *
        (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖))
      (B := (∫ x : Euclidean d, ‖f x‖) *
        (∫ x : Euclidean d, ‖fderiv ℝ
          ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))
      j hA
  calc
    surfaceMass d *
        (2 * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
          3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
            (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)) =
        surfaceMass d *
          (2 * ((∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖)) +
            3 * (2 : ℝ) ^ j * ((∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖fderiv ℝ
                ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))) := by
          ring
    _ ≤ surfaceMass d *
          ((2 : ℝ) ^ j *
            (2 * ((∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖)) +
              3 * ((∫ x : Euclidean d, ‖f x‖) *
                (∫ x : Euclidean d, ‖fderiv ℝ
                  ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)))) :=
          mul_le_mul_of_nonneg_left hcoefficient measureReal_nonneg
    _ = (surfaceMass d * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖)) *
          (2 * (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
            3 * (∫ x : Euclidean d, ‖fderiv ℝ
              ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)) := by
          ring

/-- The local dyadic `L¹` estimate also supplies an actual `L¹` member for
the real compact-radius maximal norm. -/
theorem exists_smooth_dyadic_sphericalMaximal_memLp_one
    {d : Nat} (φ f : SchwartzMap (Euclidean d) ℂ) (j : Nat) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ)) ∧
      MemLp
        (fun x : Euclidean d =>
          (⨆ r : Icc (1 : ℝ) 2,
            ENNReal.ofReal
              ‖sphericalAverage d
                ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                  SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal)
        1 volume ∧
      (∫ x : Euclidean d,
        ‖(⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal
            ‖sphericalAverage d
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal‖) ≤
        surfaceMass d *
          (2 * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
            3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
              (∫ x : Euclidean d, ‖fderiv ℝ
                ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)) := by
  rcases exists_smooth_dyadic_sphericalMaximal_l1 φ f j with ⟨ψ, hψ, hlin⟩
  let h : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)
  let p : SchwartzMap (Euclidean d) ℂ := 𝓕⁻ h
  let Q : Euclidean d → ENNReal := fun x =>
    ⨆ r : Icc (1 : ℝ) 2, ENNReal.ofReal ‖sphericalAverage d (p : Euclidean d → ℂ) r.1 x‖
  let K : ℝ := surfaceMass d *
    (2 * (∫ x : Euclidean d, ‖f x‖) *
        (∫ x : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
      3 * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
        (∫ x : Euclidean d, ‖fderiv ℝ
          ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))
  have hQmeas : Measurable Q := by
    simpa only [Q] using
      measurable_iSup_ennreal_norm_sphericalAverage (p : Euclidean d → ℂ) p.continuous
  have hQlin : (∫⁻ x : Euclidean d, Q x) ≤ ENNReal.ofReal K := by
    simpa only [Q, p, h, K] using hlin
  have hK : 0 ≤ K := by
    dsimp only [K]
    apply mul_nonneg measureReal_nonneg
    apply add_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · norm_num
        · exact integral_nonneg fun _ => norm_nonneg _
      · exact integral_nonneg fun _ => norm_nonneg _
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · norm_num
          · positivity
        · exact integral_nonneg fun _ => norm_nonneg _
      · exact integral_nonneg fun _ => norm_nonneg _
  have hQfinite : (∫⁻ x : Euclidean d, Q x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQlin
  have hQint : Integrable (fun x : Euclidean d => (Q x).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hQmeas.aemeasurable hQfinite
  have hQtop : ∀ᵐ x : Euclidean d ∂volume, Q x < ⊤ :=
    ae_lt_top hQmeas hQfinite
  have hQintegral :
      (∫ x : Euclidean d, (Q x).toReal) = (∫⁻ x : Euclidean d, Q x).toReal :=
    integral_toReal hQmeas.aemeasurable hQtop
  have hQbound : (∫ x : Euclidean d, (Q x).toReal) ≤ K := by
    rw [hQintegral]
    rw [← ENNReal.toReal_ofReal hK]
    exact (ENNReal.toReal_le_toReal hQfinite ENNReal.ofReal_ne_top).2 hQlin
  refine ⟨ψ, hψ, ?_, ?_⟩
  · rw [memLp_one_iff_integrable]
    simpa only [Q, p, h] using hQint
  · change (∫ x : Euclidean d, ‖(Q x).toReal‖) ≤ K
    rw [show (fun x : Euclidean d => ‖(Q x).toReal‖) =
        fun x => (Q x).toReal by
          funext x
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]]
    exact hQbound

/-- The fixed literal dyadic bandpass has the real-valued compact-radius
`L¹` endpoint required for interpolation.  Its multiplier is independent of
the Schwartz input. -/
theorem smooth_dyadic_sphericalMaximal_memLp_one_of_bandpass_geometric
    {d : Nat} (φ f ψ : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (hψ : ∀ ξ : Euclidean d,
      ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        φ (((2 : ℝ) ^ j)⁻¹ • ξ)) :
    MemLp
      (fun x : Euclidean d =>
        (⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal
            ‖sphericalAverage d
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal)
      1 volume ∧
    (∫ x : Euclidean d,
      ‖(⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal
            ‖sphericalAverage d
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
                SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal‖) ≤
      surfaceMass d * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
        (2 * (∫ x : Euclidean d,
            ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
          3 * (∫ x : Euclidean d,
            ‖fderiv ℝ ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖)) := by
  rcases exists_smooth_dyadic_sphericalMaximal_l1_uniform_geometric φ j with
    ⟨χ, hχ, hbound⟩
  have hχψ : χ = ψ :=
    schwartzMap_eq_of_eq_smooth_dyadic_bandpass hχ hψ
  rw [hχψ] at hbound
  let h : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)
  let p : SchwartzMap (Euclidean d) ℂ := 𝓕⁻ h
  let Q : Euclidean d → ENNReal := fun x =>
    ⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal ‖sphericalAverage d (p : Euclidean d → ℂ) r.1 x‖
  let K : ℝ :=
    surfaceMass d * (2 : ℝ) ^ j * (∫ x : Euclidean d, ‖f x‖) *
      (2 * (∫ x : Euclidean d,
          ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) x‖) +
        3 * (∫ x : Euclidean d,
          ‖fderiv ℝ ((𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) x‖))
  have hQmeas : Measurable Q := by
    simpa only [Q] using
      measurable_iSup_ennreal_norm_sphericalAverage (p : Euclidean d → ℂ) p.continuous
  have hQlin : (∫⁻ x : Euclidean d, Q x) ≤ ENNReal.ofReal K := by
    simpa only [Q, p, h, K] using hbound f
  have hK : 0 ≤ K := by
    dsimp only [K]
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · exact measureReal_nonneg
        · positivity
      · exact integral_nonneg fun _ => norm_nonneg _
    · apply add_nonneg
      · apply mul_nonneg
        · norm_num
        · exact integral_nonneg fun _ => norm_nonneg _
      · apply mul_nonneg
        · norm_num
        · exact integral_nonneg fun _ => norm_nonneg _
  have hQfinite : (∫⁻ x : Euclidean d, Q x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQlin
  have hQint : Integrable (fun x : Euclidean d => (Q x).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hQmeas.aemeasurable hQfinite
  have hQtop : ∀ᵐ x : Euclidean d ∂volume, Q x < ⊤ :=
    ae_lt_top hQmeas hQfinite
  have hQintegral :
      (∫ x : Euclidean d, (Q x).toReal) = (∫⁻ x : Euclidean d, Q x).toReal :=
    integral_toReal hQmeas.aemeasurable hQtop
  have hQbound : (∫ x : Euclidean d, (Q x).toReal) ≤ K := by
    rw [hQintegral]
    rw [← ENNReal.toReal_ofReal hK]
    exact (ENNReal.toReal_le_toReal hQfinite ENNReal.ofReal_ne_top).2 hQlin
  refine ⟨?_, ?_⟩
  · rw [memLp_one_iff_integrable]
    simpa only [Q, p, h] using hQint
  · change (∫ x : Euclidean d, ‖(Q x).toReal‖) ≤ K
    rw [show (fun x : Euclidean d => ‖(Q x).toReal‖) =
        fun x => (Q x).toReal by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]]
    exact hQbound

/-- A fixed Schwartz Fourier multiplier followed by the compact-radius
spherical maximal norm is subadditive on Schwartz inputs.  The equality of
the multiplier outputs is proved before applying the concrete maximal
subadditivity theorem. -/
theorem smooth_schwartz_multiplier_compact_sphericalMaximal_add_le
    {d : Nat} (ψ f g : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    (⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal
        ‖sphericalAverage d
          ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 (f + g))) :
            SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal ≤
      (⨆ r : Icc (1 : ℝ) 2,
        ENNReal.ofReal
          ‖sphericalAverage d
            ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
              SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal +
        (⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal
            ‖sphericalAverage d
              ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 g)) :
                SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal := by
  let Pf : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f))
  let Pg : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 g))
  have hPadd :
      (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 (f + g))) :
        SchwartzMap (Euclidean d) ℂ) = Pf + Pg := by
    rw [fourier_add f g]
    rw [(SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ)).map_add]
    rw [fourierInv_add]
  rw [hPadd]
  exact toReal_iSup_ennreal_norm_sphericalAverage_add_le
    (Pf : Euclidean d → ℂ) (Pg : Euclidean d → ℂ) Pf.continuous Pg.continuous
    (by norm_num) x

/-- The real-valued compact-radius maximal output of a fixed Schwartz
multiplier is measurable on every Schwartz input. -/
theorem measurable_smooth_schwartz_multiplier_compact_sphericalMaximal
    {d : Nat} (ψ f : SchwartzMap (Euclidean d) ℂ) :
    Measurable (fun x : Euclidean d =>
      (⨆ r : Icc (1 : ℝ) 2,
        ENNReal.ofReal
          ‖sphericalAverage d
            ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)) :
              SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x‖).toReal) := by
  let p : SchwartzMap (Euclidean d) ℂ :=
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f))
  exact ENNReal.measurable_toReal.comp
    (measurable_iSup_ennreal_norm_sphericalAverage (p : Euclidean d → ℂ) p.continuous)

end

end LeanSpherical.HarmonicAnalysis
