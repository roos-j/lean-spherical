/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SmoothDyadicPhysical
import LeanSpherical.HarmonicAnalysis.SmoothDyadicPartition
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Schwartz realization of smooth dyadic bandpasses

The literal difference of adjacent dilates of a Schwartz cutoff is again a
Schwartz map.  For the compact cutoff used in the smooth dyadic partition, it
also has compact support and vanishes on the unit ball.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform
open scoped Convolution FourierTransform

noncomputable section

/-- The difference of two adjacent dyadic dilates of a Schwartz cutoff is a
Schwartz map. -/
theorem exists_schwartzMap_smooth_dyadic_bandpass
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ) (j : Nat) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ, ∀ ξ : Euclidean d,
      ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        φ (((2 : ℝ) ^ j)⁻¹ • ξ) := by
  let R₀ : ℝ := (2 : ℝ) ^ j
  let R₁ : ℝ := (2 : ℝ) ^ (j + 1)
  have hR₀ : R₀ ≠ 0 := by
    dsimp only [R₀]
    positivity
  have hR₁ : R₁ ≠ 0 := by
    dsimp only [R₁]
    positivity
  let A₀ : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 R₀⁻¹ (inv_ne_zero hR₀))
  let A₁ : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 R₁⁻¹ (inv_ne_zero hR₁))
  let φ₀ : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A₀) φ
  let φ₁ : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A₁) φ
  refine ⟨φ₁ - φ₀, ?_⟩
  intro ξ
  change φ (A₁ ξ) - φ (A₀ ξ) =
    φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) - φ (((2 : ℝ) ^ j)⁻¹ • ξ)
  simp only [A₀, A₁, R₀, R₁]
  rfl

/-- The difference of two arbitrary nonzero real dilates of a Schwartz cutoff
is again a Schwartz map.  This is used for the shifted cutoffs which localize
literal radius blocks. -/
theorem exists_schwartzMap_scaled_sub
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ, ∀ ξ : Euclidean d,
      ψ ξ = φ (a⁻¹ • ξ) - φ (b⁻¹ • ξ) := by
  let A : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 a⁻¹ (inv_ne_zero ha))
  let B : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 b⁻¹ (inv_ne_zero hb))
  let φA : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A) φ
  let φB : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B) φ
  refine ⟨φA - φB, ?_⟩
  intro ξ
  change φ (A ξ) - φ (B ξ) = φ (a⁻¹ • ξ) - φ (b⁻¹ • ξ)
  simp only [A, B]
  rfl

/-- If the cutoff vanishes outside the ball of radius two, a difference of
two positive dilates is compactly supported. -/
theorem exists_compactlySupported_schwartzMap_scaled_sub
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ)
    (hφ_zero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d, ψ ξ = φ (a⁻¹ • ξ) - φ (b⁻¹ • ξ)) ∧
      HasCompactSupport (ψ : Euclidean d → ℂ) := by
  rcases exists_schwartzMap_scaled_sub φ a b ha.ne' hb.ne' with ⟨ψ, hψ⟩
  refine ⟨ψ, hψ, ?_⟩
  apply HasCompactSupport.intro
      (isCompact_closedBall (0 : Euclidean d) (2 * a))
  intro ξ hξ
  rw [hψ ξ]
  have hlarge : 2 * a < ‖ξ‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hξ
    exact lt_of_not_ge hξ
  have hlarge_a : 2 ≤ ‖a⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    apply (le_inv_mul_iff₀ ha).2
    nlinarith
  have hlarge_b : 2 ≤ ‖b⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
    apply (le_inv_mul_iff₀ hb).2
    calc
      b * 2 ≤ a * 2 := mul_le_mul_of_nonneg_right hba (by norm_num)
      _ = 2 * a := by ring
      _ ≤ ‖ξ‖ := hlarge.le
  rw [hφ_zero _ hlarge_a, hφ_zero _ hlarge_b]
  norm_num

/-- After fixing a nonzero radius, the moving relative bandpass times a
compact Schwartz cutoff is again a compactly supported Schwartz map. -/
theorem exists_compactlySupported_schwartzMap_relative_dyadic_bandpass_mul
    {d : Nat} (φ θ : SchwartzMap (Euclidean d) ℂ)
    (hθ : HasCompactSupport (θ : Euclidean d → ℂ))
    (j : Nat) (s : ℝ) (hs : s ≠ 0) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d, ψ ξ =
        (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (s • ξ)) -
          φ (((2 : ℝ) ^ j)⁻¹ • (s • ξ))) * θ ξ) ∧
      HasCompactSupport (ψ : Euclidean d → ℂ) := by
  rcases exists_schwartzMap_scaled_sub φ
      (((2 : ℝ) ^ (j + 1)) / s) (((2 : ℝ) ^ j) / s)
      (div_ne_zero (pow_ne_zero _ (by norm_num)) hs)
      (div_ne_zero (pow_ne_zero _ (by norm_num)) hs) with ⟨b, hb⟩
  let ψ : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (b : Euclidean d → ℂ) θ
  refine ⟨ψ, ?_, ?_⟩
  · intro ξ
    change (SchwartzMap.smulLeftCLM ℂ (b : Euclidean d → ℂ) θ) ξ = _
    rw [SchwartzMap.smulLeftCLM_apply_apply b.hasTemperateGrowth]
    rw [hb ξ]
    change (φ ((((2 : ℝ) ^ (j + 1)) / s)⁻¹ • ξ) -
        φ ((((2 : ℝ) ^ j) / s)⁻¹ • ξ)) * θ ξ = _
    have hscale1 : ((((2 : ℝ) ^ (j + 1)) / s)⁻¹) • ξ =
        ((2 : ℝ) ^ (j + 1))⁻¹ • (s • ξ) := by
      rw [smul_smul]
      field_simp
    have hscale0 : ((((2 : ℝ) ^ j) / s)⁻¹) • ξ =
        ((2 : ℝ) ^ j)⁻¹ • (s • ξ) := by
      rw [smul_smul]
      field_simp
    rw [hscale1, hscale0]
  · have hψ : (ψ : Euclidean d → ℂ) =
        (fun x : Euclidean d => b x) * (θ : Euclidean d → ℂ) := by
      funext x
      dsimp only [ψ]
      rw [SchwartzMap.smulLeftCLM_apply_apply b.hasTemperateGrowth]
      rfl
    rw [hψ]
    exact hθ.mul_left

/-- A cutoff which is constant on the unit ball has zero derivative strictly
inside that ball. -/
theorem fderiv_schwartzMap_eq_zero_of_norm_lt_one
    {d : Nat} {φ : SchwartzMap (Euclidean d) ℂ}
    (hφ_one : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (z : Euclidean d) (hz : ‖z‖ < 1) :
    fderiv ℝ (φ : Euclidean d → ℂ) z = 0 := by
  have heq : (φ : Euclidean d → ℂ) =ᶠ[nhds z] fun _ : Euclidean d => (1 : ℂ) := by
    filter_upwards [Metric.ball_mem_nhds z (sub_pos.mpr hz)] with y hy
    apply hφ_one y
    have hdist : ‖y - z‖ < 1 - ‖z‖ := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy
    exact (calc
      ‖y‖ = ‖(y - z) + z‖ := by congr 1 <;> abel
      _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
      _ < (1 - ‖z‖) + ‖z‖ := by
        simpa only [add_comm] using add_lt_add_right hdist ‖z‖
      _ = 1 := by ring).le
  rw [heq.fderiv_eq]
  simp

/-- A cutoff which vanishes outside the ball of radius two has zero
derivative strictly outside that ball. -/
theorem fderiv_schwartzMap_eq_zero_of_two_lt_norm
    {d : Nat} {φ : SchwartzMap (Euclidean d) ℂ}
    (hφ_zero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (z : Euclidean d) (hz : 2 < ‖z‖) :
    fderiv ℝ (φ : Euclidean d → ℂ) z = 0 := by
  have heq : (φ : Euclidean d → ℂ) =ᶠ[nhds z] fun _ : Euclidean d => (0 : ℂ) := by
    filter_upwards [Metric.ball_mem_nhds z (sub_pos.mpr hz)] with y hy
    apply hφ_zero y
    have hdist : ‖y - z‖ < ‖z‖ - 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have htri : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
      calc
        ‖z‖ = ‖(z - y) + y‖ := by congr 1 <;> abel
        _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
    have hdist' : ‖z - y‖ < ‖z‖ - 2 := by
      simpa only [norm_sub_rev] using hdist
    linarith
  rw [heq.fderiv_eq]
  simp

/-- The radial derivative of a literal smooth dyadic bandpass is the
difference of the two chain-rule terms.  Keeping this formula at the
frequency level is needed for the moving relative cutoff. -/
theorem hasDerivAt_smooth_dyadic_bandpass_radial
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ)
    (j : Nat) (r : ℝ) (ξ : Euclidean d) :
    HasDerivAt (fun t : ℝ =>
      φ (((2 : ℝ) ^ (j + 1))⁻¹ • (t • ξ)) -
        φ (((2 : ℝ) ^ j)⁻¹ • (t • ξ)))
      (fderiv ℝ (φ : Euclidean d → ℂ)
        (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ))
        (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
      fderiv ℝ (φ : Euclidean d → ℂ)
        (((2 : ℝ) ^ j)⁻¹ • (r • ξ))
        (((2 : ℝ) ^ j)⁻¹ • ξ)) r := by
  apply HasDerivAt.sub
  · have hφ : HasFDerivAt (φ : Euclidean d → ℂ)
        (fderiv ℝ (φ : Euclidean d → ℂ)
          (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)))
        (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) :=
      ((φ.smooth (⊤ : ℕ∞)).differentiable (by simp)).differentiableAt.hasFDerivAt
    have hlin : HasDerivAt (fun t : ℝ =>
        ((2 : ℝ) ^ (j + 1))⁻¹ • (t • ξ))
        (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) r := by
      simpa only [id_eq, smul_smul, mul_comm, mul_one, one_mul] using
        ((hasDerivAt_id r).const_mul ((2 : ℝ) ^ (j + 1))⁻¹).smul_const ξ
    exact hφ.comp_hasDerivAt r hlin
  · have hφ : HasFDerivAt (φ : Euclidean d → ℂ)
        (fderiv ℝ (φ : Euclidean d → ℂ)
          (((2 : ℝ) ^ j)⁻¹ • (r • ξ)))
        (((2 : ℝ) ^ j)⁻¹ • (r • ξ)) :=
      ((φ.smooth (⊤ : ℕ∞)).differentiable (by simp)).differentiableAt.hasFDerivAt
    have hlin : HasDerivAt (fun t : ℝ =>
        ((2 : ℝ) ^ j)⁻¹ • (t • ξ))
        (((2 : ℝ) ^ j)⁻¹ • ξ) r := by
      simpa only [id_eq, smul_smul, mul_comm, mul_one, one_mul] using
        ((hasDerivAt_id r).const_mul ((2 : ℝ) ^ j)⁻¹).smul_const ξ
    exact hφ.comp_hasDerivAt r hlin

/-- The radial derivative of the moving dyadic bandpass vanishes below its
inner scale. -/
theorem deriv_smooth_dyadic_bandpass_radial_eq_zero_of_norm_lt
    {d : Nat} {φ : SchwartzMap (Euclidean d) ℂ}
    (hφ_one : ∀ z, ‖z‖ ≤ 1 → φ z = 1)
    (j : Nat) (r : ℝ) (ξ : Euclidean d)
    (hsmall : ‖r • ξ‖ < (2 : ℝ) ^ j) :
    deriv (fun t : ℝ =>
      φ (((2 : ℝ) ^ (j + 1))⁻¹ • (t • ξ)) -
        φ (((2 : ℝ) ^ j)⁻¹ • (t • ξ))) r = 0 := by
  rw [(hasDerivAt_smooth_dyadic_bandpass_radial φ j r ξ).deriv]
  have hp0 : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) _
  have hp1 : 0 < (2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
  have hsmall1 : ‖r • ξ‖ < (2 : ℝ) ^ (j + 1) := by
    apply hsmall.trans_le
    rw [show (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 by rw [pow_succ]]
    nlinarith
  have hz0 : ‖((2 : ℝ) ^ j)⁻¹ • (r • ξ)‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp0)]
    exact (inv_mul_lt_one₀ hp0).2 hsmall
  have hz1 : ‖((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp1)]
    exact (inv_mul_lt_one₀ hp1).2 hsmall1
  rw [fderiv_schwartzMap_eq_zero_of_norm_lt_one hφ_one _ hz1,
    fderiv_schwartzMap_eq_zero_of_norm_lt_one hφ_one _ hz0]
  simp

/-- The radial derivative of the moving dyadic bandpass vanishes above its
outer scale. -/
theorem deriv_smooth_dyadic_bandpass_radial_eq_zero_of_lt_norm
    {d : Nat} {φ : SchwartzMap (Euclidean d) ℂ}
    (hφ_zero : ∀ z, 2 ≤ ‖z‖ → φ z = 0)
    (j : Nat) (r : ℝ) (ξ : Euclidean d)
    (hlarge : (2 : ℝ) ^ (j + 2) < ‖r • ξ‖) :
    deriv (fun t : ℝ =>
      φ (((2 : ℝ) ^ (j + 1))⁻¹ • (t • ξ)) -
        φ (((2 : ℝ) ^ j)⁻¹ • (t • ξ))) r = 0 := by
  rw [(hasDerivAt_smooth_dyadic_bandpass_radial φ j r ξ).deriv]
  have hp0 : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) _
  have hp1 : 0 < (2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
  have hlarge0 : (2 : ℝ) ^ j * 2 < ‖r • ξ‖ := by
    calc
      (2 : ℝ) ^ j * 2 = (2 : ℝ) ^ (j + 1) := by rw [pow_succ]
      _ < (2 : ℝ) ^ (j + 2) := by
        rw [show (2 : ℝ) ^ (j + 2) = (2 : ℝ) ^ (j + 1) * 2 by rw [pow_succ]]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (j + 1)]
      _ < ‖r • ξ‖ := hlarge
  have hz0 : 2 < ‖((2 : ℝ) ^ j)⁻¹ • (r • ξ)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp0)]
    exact (lt_inv_mul_iff₀ hp0).2 hlarge0
  have hz1 : 2 < ‖((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp1)]
    exact (lt_inv_mul_iff₀ hp1).2 (by
      simpa only [pow_succ] using hlarge)
  rw [fderiv_schwartzMap_eq_zero_of_two_lt_norm hφ_zero _ hz1,
    fderiv_schwartzMap_eq_zero_of_two_lt_norm hφ_zero _ hz0]
  simp

/-- A nonzero derivative of the moving bandpass is confined to the same
two-scale annulus as the bandpass itself. -/
theorem deriv_smooth_dyadic_bandpass_radial_norm_bounds_of_ne_zero
    {d : Nat} {φ : SchwartzMap (Euclidean d) ℂ}
    (hφ_one : ∀ z, ‖z‖ ≤ 1 → φ z = 1)
    (hφ_zero : ∀ z, 2 ≤ ‖z‖ → φ z = 0)
    (j : Nat) (r : ℝ) (ξ : Euclidean d)
    (h : deriv (fun t : ℝ =>
      φ (((2 : ℝ) ^ (j + 1))⁻¹ • (t • ξ)) -
        φ (((2 : ℝ) ^ j)⁻¹ • (t • ξ))) r ≠ 0) :
    (2 : ℝ) ^ j ≤ ‖r • ξ‖ ∧ ‖r • ξ‖ ≤ (2 : ℝ) ^ (j + 2) := by
  constructor
  · apply le_of_not_gt
    intro hsmall
    exact h (deriv_smooth_dyadic_bandpass_radial_eq_zero_of_norm_lt
      hφ_one j r ξ hsmall)
  · apply le_of_not_gt
    intro hlarge
    exact h (deriv_smooth_dyadic_bandpass_radial_eq_zero_of_lt_norm
      hφ_zero j r ξ hlarge)

/-- The radial derivative of a smooth dyadic bandpass is controlled by the
uniform norm of the derivative of its cutoff.  The displayed factor is
explicit, so its scale dependence can be combined with surface-transform
decay without treating the moving cutoff as fixed. -/
theorem norm_deriv_smooth_dyadic_bandpass_radial_le
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ)
    (j : Nat) (r : ℝ) (ξ : Euclidean d) :
    ‖deriv (fun t : ℝ =>
      φ (((2 : ℝ) ^ (j + 1))⁻¹ • (t • ξ)) -
        φ (((2 : ℝ) ^ j)⁻¹ • (t • ξ))) r‖ ≤
      ‖((SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) φ).toBoundedContinuousFunction‖ *
        (((2 : ℝ) ^ (j + 1))⁻¹ * ‖ξ‖ + ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖) := by
  let dφ : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) φ
  have hdf (z : Euclidean d) : ‖fderiv ℝ (φ : Euclidean d → ℂ) z‖ ≤
      ‖dφ.toBoundedContinuousFunction‖ := by
    calc
      ‖fderiv ℝ (φ : Euclidean d → ℂ) z‖ = ‖dφ z‖ := by
        rw [← SchwartzMap.fderivCLM_apply ℂ φ z]
      _ = ‖dφ.toBoundedContinuousFunction z‖ := rfl
      _ ≤ ‖dφ.toBoundedContinuousFunction‖ :=
        BoundedContinuousFunction.norm_coe_le_norm dφ.toBoundedContinuousFunction z
  rw [(hasDerivAt_smooth_dyadic_bandpass_radial φ j r ξ).deriv]
  have hpos0 : 0 < (2 : ℝ) ^ j := by positivity
  have hpos1 : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  have hterm1 :
      ‖fderiv ℝ (φ : Euclidean d → ℂ)
        (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ))
        (((2 : ℝ) ^ (j + 1))⁻¹ • ξ)‖ ≤
      ‖dφ.toBoundedContinuousFunction‖ *
        ((2 : ℝ) ^ (j + 1))⁻¹ * ‖ξ‖ := by
    calc
      ‖fderiv ℝ (φ : Euclidean d → ℂ)
        (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ))
        (((2 : ℝ) ^ (j + 1))⁻¹ • ξ)‖ ≤
          ‖fderiv ℝ (φ : Euclidean d → ℂ)
            (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ))‖ *
            ‖((2 : ℝ) ^ (j + 1))⁻¹ • ξ‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖dφ.toBoundedContinuousFunction‖ *
          (((2 : ℝ) ^ (j + 1))⁻¹ * ‖ξ‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos1)]
        exact mul_le_mul_of_nonneg_right (hdf _)
          (mul_nonneg (inv_nonneg.mpr hpos1.le) (norm_nonneg _))
      _ = ‖dφ.toBoundedContinuousFunction‖ *
          ((2 : ℝ) ^ (j + 1))⁻¹ * ‖ξ‖ := by ring
  have hterm0 :
      ‖fderiv ℝ (φ : Euclidean d → ℂ)
        (((2 : ℝ) ^ j)⁻¹ • (r • ξ))
        (((2 : ℝ) ^ j)⁻¹ • ξ)‖ ≤
      ‖dφ.toBoundedContinuousFunction‖ *
        ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖ := by
    calc
      ‖fderiv ℝ (φ : Euclidean d → ℂ)
        (((2 : ℝ) ^ j)⁻¹ • (r • ξ))
        (((2 : ℝ) ^ j)⁻¹ • ξ)‖ ≤
          ‖fderiv ℝ (φ : Euclidean d → ℂ)
            (((2 : ℝ) ^ j)⁻¹ • (r • ξ))‖ *
            ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖dφ.toBoundedContinuousFunction‖ *
          (((2 : ℝ) ^ j)⁻¹ * ‖ξ‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos0)]
        exact mul_le_mul_of_nonneg_right (hdf _)
          (mul_nonneg (inv_nonneg.mpr hpos0.le) (norm_nonneg _))
      _ = ‖dφ.toBoundedContinuousFunction‖ *
          ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖ := by ring
  calc
    ‖fderiv ℝ (φ : Euclidean d → ℂ)
        (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ))
        (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
      fderiv ℝ (φ : Euclidean d → ℂ)
        (((2 : ℝ) ^ j)⁻¹ • (r • ξ))
        (((2 : ℝ) ^ j)⁻¹ • ξ)‖ ≤
      ‖fderiv ℝ (φ : Euclidean d → ℂ)
        (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ))
        (((2 : ℝ) ^ (j + 1))⁻¹ • ξ)‖ +
      ‖fderiv ℝ (φ : Euclidean d → ℂ)
        (((2 : ℝ) ^ j)⁻¹ • (r • ξ))
        (((2 : ℝ) ^ j)⁻¹ • ξ)‖ := norm_sub_le _ _
    _ ≤ ‖dφ.toBoundedContinuousFunction‖ *
        ((2 : ℝ) ^ (j + 1))⁻¹ * ‖ξ‖ +
      ‖dφ.toBoundedContinuousFunction‖ *
        ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖ := add_le_add hterm1 hterm0
    _ = ‖dφ.toBoundedContinuousFunction‖ *
        (((2 : ℝ) ^ (j + 1))⁻¹ * ‖ξ‖ + ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖) := by ring
/-- The literal smooth dyadic bandpass formula determines the Schwartz
multiplier uniquely. -/
theorem schwartzMap_eq_of_eq_smooth_dyadic_bandpass
    {d : Nat} {φ ψ χ : SchwartzMap (Euclidean d) ℂ} {j : Nat}
    (hψ : ∀ ξ : Euclidean d,
      ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        φ (((2 : ℝ) ^ j)⁻¹ • ξ))
    (hχ : ∀ ξ : Euclidean d,
      χ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        φ (((2 : ℝ) ^ j)⁻¹ • ξ)) :
    ψ = χ := by
  ext ξ
  rw [hψ ξ, hχ ξ]

/-- The inverse Fourier transform of the smooth dyadic bandpass multiplier
is exactly the difference of the two corresponding dilated convolutions. -/
theorem fourierInv_smooth_dyadic_bandpass_multiplier_eq_sub_convolution
    {d : Nat} (φ f : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (x : Euclidean d) :
    𝓕⁻ (fun ξ : Euclidean d =>
      (φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) - φ (((2 : ℝ) ^ j)⁻¹ • ξ)) *
        𝓕 (f : Euclidean d → ℂ) ξ) x =
      ((fun y : Euclidean d => ((2 : ℝ) ^ (j + 1)) ^ d •
        (𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ)
          (((2 : ℝ) ^ (j + 1)) • y))
        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (f : Euclidean d → ℂ)) x -
      ((fun y : Euclidean d => ((2 : ℝ) ^ j) ^ d •
        (𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) (((2 : ℝ) ^ j) • y))
        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (f : Euclidean d → ℂ)) x := by
  exact fourierInv_sub_scaled_schwartz_multiplier_eq_sub_convolution φ f
    (R := (2 : ℝ) ^ j) (S := (2 : ℝ) ^ (j + 1))
    (by positivity) (by positivity) x

/-- If the cutoff equals one on the unit ball and vanishes outside the ball
of radius two, its smooth dyadic bandpass has compact support and itself
vanishes on the unit ball. -/
theorem exists_compactlySupported_schwartzMap_smooth_dyadic_bandpass
    {d : Nat} (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (j : Nat) :
    ∃ ψ : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
          φ (((2 : ℝ) ^ j)⁻¹ • ξ)) ∧
      HasCompactSupport (ψ : Euclidean d → ℂ) ∧
      (∀ ξ : Euclidean d, ‖ξ‖ ≤ 1 → ψ ξ = 0) := by
  rcases exists_schwartzMap_smooth_dyadic_bandpass φ j with ⟨ψ, hψ⟩
  refine ⟨ψ, hψ, ?_, ?_⟩
  · apply HasCompactSupport.intro
      (isCompact_closedBall (0 : Euclidean d) ((2 : ℝ) ^ (j + 2)))
    intro ξ hξ
    have hnot : ¬ ‖ξ‖ ≤ (2 : ℝ) ^ (j + 2) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hξ
    rw [hψ ξ]
    exact smooth_dyadic_bandpass_eq_zero_of_le_norm hφzero
      (le_of_lt (lt_of_not_ge hnot))
  · intro ξ hξ
    rw [hψ ξ]
    apply smooth_dyadic_bandpass_eq_zero_of_norm_le hφone
    calc
      ‖ξ‖ ≤ 1 := hξ
      _ = (2 : ℝ) ^ 0 := by norm_num
      _ ≤ (2 : ℝ) ^ j := by
        exact pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)

end

end LeanSpherical.HarmonicAnalysis
