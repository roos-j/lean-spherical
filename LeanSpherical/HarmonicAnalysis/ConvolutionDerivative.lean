/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Differentiating smoothing convolutions

This is the direct Euclidean specialization needed for smooth dyadic kernels.
Besides the compact-support theorem from Mathlib, it proves the same
pointwise derivative formula when the kernel and its derivative have global
bounds; this covers Schwartz kernels without assuming false compact support.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Metric
open scoped BoundedContinuousFunction Convolution

noncomputable section

/-- If a smoothing kernel is `C¹` and compactly supported, convolution by it
has the expected total derivative. -/
theorem fderiv_convolution_right_eq_convolution_fderiv
    {d : ℕ} (f k : Euclidean d → ℂ) (hf : LocallyIntegrable f volume)
    (hk : HasCompactSupport k) (hk1 : ContDiff ℝ 1 k) (x : Euclidean d) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x =
      (f ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR (Euclidean d), volume]
        fderiv ℝ k) x := by
  exact
    (hk.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hf hk1 x).fderiv

/-- An integrable input convolved with a globally bounded `C¹` kernel is
differentiable, with derivative obtained by convolving against the kernel's
total derivative.  This is the non-compact version needed for Schwartz
kernels: the global derivative bound is an integrable majorant after it is
multiplied by the input. -/
theorem hasFDerivAt_convolution_right_of_bound
    {d : ℕ} (f k : Euclidean d → ℂ) (hf : Integrable f volume)
    (hk : ContDiff ℝ 1 k) {C₀ C₁ : ℝ}
    (hkb : ∀ z, ‖k z‖ ≤ C₀)
    (hdkb : ∀ z, ‖fderiv ℝ k z‖ ≤ C₁)
    (x₀ : Euclidean d) :
    HasFDerivAt (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k)
      ((f ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR (Euclidean d), volume]
        fderiv ℝ k) x₀) x₀ := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  let L' := L.precompR (Euclidean d)
  have hL : ∀ (z : ℂ) (A : Euclidean d →L[ℝ] ℂ), ‖L' z A‖ ≤ ‖z‖ * ‖A‖ := by
    intro z A
    have hEq : L' z A = z • A := by
      ext v
      simp [L, L', ContinuousLinearMap.precompR_apply, ContinuousLinearMap.mul_apply']
    rw [hEq, norm_smul]
  have hmeas (x : Euclidean d) : AEStronglyMeasurable
      (fun t : Euclidean d => L (f t) (k (x - t))) volume := by
    exact hf.aestronglyMeasurable.convolution_integrand_snd L
      hk.continuous.aestronglyMeasurable x
  have hdmeas (x : Euclidean d) : AEStronglyMeasurable
      (fun t : Euclidean d => L' (f t) (fderiv ℝ k (x - t))) volume := by
    exact hf.aestronglyMeasurable.convolution_integrand_snd L'
      (hk.continuous_fderiv (by norm_num)).aestronglyMeasurable x
  have hderiv (x t : Euclidean d) : HasFDerivAt
      (fun y : Euclidean d => k (y - t)) (fderiv ℝ k (x - t)) x := by
    simpa using!
      (hk.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub (hasFDerivAt_const t x))
  have hbound : ∀ᵐ t : Euclidean d ∂volume,
      ∀ x ∈ ball x₀ 1, ‖L' (f t) (fderiv ℝ k (x - t))‖ ≤ ‖f t‖ * C₁ := by
    filter_upwards with t
    intro x hx
    exact (hL _ _).trans (mul_le_mul_of_nonneg_left (hdkb _) (norm_nonneg _))
  have hmajor : Integrable (fun t : Euclidean d => ‖f t‖ * C₁) volume :=
    hf.norm.mul_const C₁
  have hexists : ∀ x : Euclidean d,
      ConvolutionExistsAt f k x L volume := by
    intro x
    change Integrable (fun t : Euclidean d => L (f t) (k (x - t))) volume
    refine Integrable.mono' (hf.norm.mul_const C₀) (hmeas x) ?_
    filter_upwards with t
    change ‖f t * k (x - t)‖ ≤ ‖f t‖ * C₀
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hkb _) (norm_nonneg _)
  simpa using!
    (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (ball_mem_nhds x₀ zero_lt_one)
      (Filter.Eventually.of_forall hmeas) (hexists x₀)
      (hdmeas x₀) hbound hmajor
      (Filter.Eventually.of_forall fun t x hx =>
        (L (f t)).hasFDerivAt.comp x (hderiv x t)))

/-- Once a convolution has the displayed pointwise derivative formula, its
total derivative satisfies the direct `L¹` Young bound. -/
theorem integral_norm_fderiv_convolution_right_le_of_hasFDerivAt
    {d : ℕ} (f k : Euclidean d → ℂ) (hf : Integrable f volume)
    (hderiv : ∀ x : Euclidean d,
      HasFDerivAt (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k)
        ((f ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR (Euclidean d), volume]
          fderiv ℝ k) x) x)
    (hdk : Integrable (fderiv ℝ k) volume) :
    (∫ x : Euclidean d,
      ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x‖) ≤
      (∫ x : Euclidean d, ‖f x‖) * (∫ x : Euclidean d, ‖fderiv ℝ k x‖) := by
  let D : Euclidean d → Euclidean d →L[ℝ] ℂ := fderiv ℝ k
  let L := (ContinuousLinearMap.mul ℝ ℂ).precompR (Euclidean d)
  have hL : ∀ (z : ℂ) (A : Euclidean d →L[ℝ] ℂ), ‖L z A‖ ≤ ‖z‖ * ‖A‖ := by
    intro z A
    have hEq : L z A = z • A := by
      ext v
      simp [L, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.mul_apply']
    rw [hEq, norm_smul]
  have hprodNorm :
      Integrable (fun p : Euclidean d × Euclidean d =>
        ‖f p.2‖ * ‖D (p.1 - p.2)‖) (volume.prod volume) := by
    simpa only [D, ContinuousLinearMap.mul_apply'] using
      (hf.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hdk.norm)
  have hscalar :
      Integrable (fun x : Euclidean d =>
        ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖) volume :=
    hprodNorm.integral_prod_left
  have hfiber : ∀ᵐ x : Euclidean d ∂volume,
      Integrable (fun t : Euclidean d => ‖f t‖ * ‖D (x - t)‖) volume := by
    exact (integrable_prod_iff hprodNorm.aestronglyMeasurable).mp hprodNorm |>.1
  have hconv : Integrable (f ⋆[L, volume] D) volume :=
    hf.integrable_convolution L hdk
  have hpoint : ∀ᵐ x : Euclidean d ∂volume,
      ‖(f ⋆[L, volume] D) x‖ ≤
        ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖ := by
    filter_upwards [hfiber] with x hx
    rw [convolution_def]
    calc
      ‖∫ t : Euclidean d, L (f t) (D (x - t))‖ ≤
          ∫ t : Euclidean d, ‖L (f t) (D (x - t))‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖ := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun t => norm_nonneg _
        · exact hx
        · exact Filter.Eventually.of_forall fun t => hL _ _
  have hfirst :
      (∫ x : Euclidean d, ‖(f ⋆[L, volume] D) x‖) ≤
        ∫ x : Euclidean d, ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖ := by
    exact integral_mono_ae hconv.norm hscalar hpoint
  have hswap :
      (∫ x : Euclidean d, ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖) =
        ∫ t : Euclidean d, ∫ x : Euclidean d, ‖f t‖ * ‖D (x - t)‖ := by
    exact integral_integral_swap hprodNorm
  have htranslate :
      (∫ t : Euclidean d, ∫ x : Euclidean d, ‖f t‖ * ‖D (x - t)‖) =
        (∫ t : Euclidean d, ‖f t‖) * (∫ x : Euclidean d, ‖D x‖) := by
    calc
      (∫ t : Euclidean d, ∫ x : Euclidean d, ‖f t‖ * ‖D (x - t)‖) =
          ∫ t : Euclidean d, ‖f t‖ * ∫ x : Euclidean d, ‖D (x - t)‖ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [integral_const_mul]
      _ = ∫ t : Euclidean d, ‖f t‖ * ∫ x : Euclidean d, ‖D x‖ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [integral_sub_right_eq_self (μ := volume)
          (fun x : Euclidean d => ‖D x‖) t]
      _ = (∫ t : Euclidean d, ‖f t‖) * (∫ x : Euclidean d, ‖D x‖) := by
        rw [integral_mul_const]
  calc
    (∫ x : Euclidean d,
      ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x‖) =
        ∫ x : Euclidean d, ‖(f ⋆[L, volume] D) x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [(hderiv x).fderiv]
    _ ≤ ∫ x : Euclidean d, ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖ := hfirst
    _ = (∫ x : Euclidean d, ‖f x‖) * (∫ x : Euclidean d, ‖D x‖) := hswap.trans htranslate
    _ = (∫ x : Euclidean d, ‖f x‖) * (∫ x : Euclidean d, ‖fderiv ℝ k x‖) := by rfl

/-- A compactly supported `C¹` smoothing convolution obeys the direct `L¹`
bound for its total derivative. -/
theorem integral_norm_fderiv_convolution_right_le
    {d : ℕ} (f k : Euclidean d → ℂ) (hf : Integrable f volume)
    (hk : HasCompactSupport k) (hk1 : ContDiff ℝ 1 k)
    (hdk : Integrable (fderiv ℝ k) volume) :
    (∫ x : Euclidean d,
      ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x‖) ≤
      (∫ x : Euclidean d, ‖f x‖) * (∫ x : Euclidean d, ‖fderiv ℝ k x‖) := by
  exact integral_norm_fderiv_convolution_right_le_of_hasFDerivAt f k hf
    (fun x => hk.hasFDerivAt_convolution_right
      (ContinuousLinearMap.mul ℝ ℂ) hf.locallyIntegrable hk1 x)
    hdk

/-- The same `L¹` derivative estimate for globally bounded smooth kernels.
This is the version applicable to Schwartz kernels. -/
theorem integral_norm_fderiv_convolution_right_le_of_bound
    {d : ℕ} (f k : Euclidean d → ℂ) (hf : Integrable f volume)
    (hk : ContDiff ℝ 1 k) {C₀ C₁ : ℝ}
    (hkb : ∀ z, ‖k z‖ ≤ C₀)
    (hdkb : ∀ z, ‖fderiv ℝ k z‖ ≤ C₁)
    (hdk : Integrable (fderiv ℝ k) volume) :
    (∫ x : Euclidean d,
      ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x‖) ≤
      (∫ x : Euclidean d, ‖f x‖) * (∫ x : Euclidean d, ‖fderiv ℝ k x‖) := by
  exact integral_norm_fderiv_convolution_right_le_of_hasFDerivAt f k hf
    (fun x => hasFDerivAt_convolution_right_of_bound f k hf hk hkb hdkb x) hdk

/-- Applying the preceding estimate to a Schwartz kernel requires no compact
support fiction: Schwartz decay supplies the global bounds and integrability
needed by the non-compact differentiation theorem. -/
theorem integral_norm_fderiv_convolution_right_le_schwartz
    {d : ℕ} (f : Euclidean d → ℂ) (hf : Integrable f volume)
    (k : SchwartzMap (Euclidean d) ℂ) :
    (∫ x : Euclidean d,
      ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (k : Euclidean d → ℂ)) x‖) ≤
      (∫ x : Euclidean d, ‖f x‖) *
        (∫ x : Euclidean d, ‖fderiv ℝ (k : Euclidean d → ℂ) x‖) := by
  let dk : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) k
  have hdk : Integrable (fderiv ℝ (k : Euclidean d → ℂ)) volume := by
    have hdk_eq : (dk : Euclidean d → (Euclidean d →L[ℝ] ℂ)) =
        fderiv ℝ (k : Euclidean d → ℂ) := by
      funext x
      exact SchwartzMap.fderivCLM_apply ℂ k x
    rw [← hdk_eq]
    exact dk.integrable
  refine integral_norm_fderiv_convolution_right_le_of_bound f (k : Euclidean d → ℂ)
    hf (by simpa using k.smooth (1 : ℕ∞))
      (C₀ := ‖k.toBoundedContinuousFunction‖)
      (C₁ := ‖dk.toBoundedContinuousFunction‖) ?_ ?_ hdk
  · intro z
    exact BoundedContinuousFunction.norm_coe_le_norm
      (k.toBoundedContinuousFunction : Euclidean d →ᵇ ℂ) z
  · intro z
    calc
      ‖fderiv ℝ (k : Euclidean d → ℂ) z‖ = ‖dk z‖ := by
        rw [← SchwartzMap.fderivCLM_apply ℂ k z]
      _ = ‖dk.toBoundedContinuousFunction z‖ := rfl
      _ ≤ ‖dk.toBoundedContinuousFunction‖ :=
        BoundedContinuousFunction.norm_coe_le_norm
          (dk.toBoundedContinuousFunction : Euclidean d →ᵇ (Euclidean d →L[ℝ] ℂ)) z

end

end LeanSpherical.HarmonicAnalysis
