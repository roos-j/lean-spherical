/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.PhysicalEndpoint

/-!
# Physical endpoint for absolute-frequency pieces

The entropy square estimate is formulated for the usual, fixed-frequency
smooth dyadic pieces.  This is its matching physical `L¹ → L∞` endpoint.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Set
open scoped BigOperators Convolution FourierTransform Pointwise

noncomputable section

private theorem powerWeight_absolute_surface_kernel_argument
    {d : Nat} (L r : ℝ) (hr : 0 < r)
    (x y w : Euclidean d) :
    (L * r⁻¹) • (x + r • w - y) =
      - (L • (r⁻¹ • (y - x) - w)) := by
  rw [mul_smul]
  simp only [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  module

/-- On `[1,2]`, a smooth projection at physical frequency scale `R ≥ 1`
followed by a spherical average has `L¹ → L∞` norm `O(R)`. -/
theorem exists_sphericalAverage_fourierInv_scaled_schwartz_multiplier_le_integral
    {d : Nat} (hd : 0 < d) (ψ : SchwartzMap (Euclidean d) ℂ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (R : ℝ), 1 ≤ R →
      ∀ (f : SchwartzMap (Euclidean d) ℂ) {r : ℝ}, r ∈ Icc (1 : ℝ) 2 →
        ∀ x : Euclidean d,
        ‖sphericalAverage d
          (fun z : Euclidean d =>
            𝓕⁻ (fun ξ : Euclidean d => ψ (R⁻¹ • ξ) *
              𝓕 (f : Euclidean d → ℂ) ξ) z) r x‖ ≤
          D * R * ∫ y : Euclidean d, ‖f y‖ := by
  let K : SchwartzMap (Euclidean d) ℂ := 𝓕⁻ ψ
  let negA : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (-1 : ℝ) (by norm_num))
  let Kneg : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ negA K
  have hKneg (u : Euclidean d) : Kneg u = K (-u) := by
    change K (negA u) = K (-u)
    simp [negA]
  obtain ⟨C, hC, hshell⟩ :=
    exists_surface_smoothed_schwartz_kernel_shell_bound hd Kneg
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro R hR f r hr x
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
  let L : ℝ := R * r
  have hL : 1 ≤ L := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ R * r := mul_le_mul hR hr.1 zero_le_one (by positivity)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLle : L ≤ 2 * R := by
    dsimp [L]
    calc
      R * r ≤ R * 2 := mul_le_mul_of_nonneg_left hr.2 (zero_le_one.trans hR)
      _ = 2 * R := by ring
  let W : Euclidean d → ℝ := fun z =>
    ∫ w : Metric.sphere (0 : Euclidean d) 1,
      ‖L ^ d • Kneg (L • (z - (w : Euclidean d)))‖ ∂unitSurfaceMeasure d
  have hWnonneg (z : Euclidean d) : 0 ≤ W z := by
    dsimp [W]
    exact integral_nonneg fun w => norm_nonneg _
  have hWnear (z : Euclidean d) : W z ≤ C * L := by
    simpa [W] using (hshell L hL z).1
  have hWjoint : Continuous (Function.uncurry
      (fun (z : Euclidean d) (w : Metric.sphere (0 : Euclidean d) 1) =>
        ‖((L ^ d : ℝ) : ℂ) * Kneg (L • (z - (w : Euclidean d)))‖)) := by
    have harg : Continuous (fun p : Euclidean d × Metric.sphere (0 : Euclidean d) 1 =>
        L • (p.1 - (p.2 : Euclidean d))) :=
      (continuous_const : Continuous
        (fun _ : Euclidean d × Metric.sphere (0 : Euclidean d) 1 => L)).smul
        (continuous_fst.sub (continuous_subtype_val.comp continuous_snd))
    have hkernel : Continuous (fun p : Euclidean d × Metric.sphere (0 : Euclidean d) 1 =>
        Kneg (L • (p.1 - (p.2 : Euclidean d)))) :=
      Kneg.continuous.comp harg
    exact (Continuous.mul
      (continuous_const : Continuous
        (fun _ : Euclidean d × Metric.sphere (0 : Euclidean d) 1 => ((L ^ d : ℝ) : ℂ)))
      hkernel).norm
  have hWcont : Continuous W := by
    dsimp [W]
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := unitSurfaceMeasure d) hWjoint isCompact_univ)
  have hphysical (z : Euclidean d) :
      𝓕⁻ (fun ξ : Euclidean d => ψ (R⁻¹ • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) z =
        ((fun y : Euclidean d => R ^ d • K (R • y))
          ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
          (f : Euclidean d → ℂ)) z := by
    simpa only [K] using
      fourierInv_scaled_schwartz_multiplier_eq_convolution ψ f
        (lt_of_lt_of_le zero_lt_one hR) z
  have hinner (y : Euclidean d) :
      (∫ w : Metric.sphere (0 : Euclidean d) 1,
        ‖R ^ d • K (R • (x + r • (w : Euclidean d) - y))‖
        ∂unitSurfaceMeasure d) =
        (r⁻¹) ^ d * W (r⁻¹ • (y - x)) := by
    dsimp [W]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with w
    have hR_eq : R = L * r⁻¹ := by
      dsimp [L]
      field_simp [hrpos.ne']
    have harg : R • (x + r • (w : Euclidean d) - y) =
        - (L • (r⁻¹ • (y - x) - (w : Euclidean d))) := by
      rw [hR_eq]
      exact powerWeight_absolute_surface_kernel_argument L r hrpos x y (w : Euclidean d)
    rw [harg, ← hKneg]
    change ‖((R ^ d : ℝ) : ℂ) * Kneg (L • (r⁻¹ • (y - x) - (w : Euclidean d)))‖ =
      (r⁻¹) ^ d * ‖((L ^ d : ℝ) : ℂ) *
        Kneg (L • (r⁻¹ • (y - x) - (w : Euclidean d)))‖
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (zero_le_one.trans hR) _),
      abs_of_nonneg (pow_nonneg hLpos.le _)]
    rw [hR_eq, mul_pow]
    ring
  have hrinv : r⁻¹ ≤ 1 := (inv_le_one₀ hrpos).mpr hr.1
  have hrpow : (r⁻¹) ^ d ≤ 1 := by
    simpa using pow_le_one₀ (inv_nonneg.mpr hrpos.le) hrinv
  have hkernel (y : Euclidean d) :
      (r⁻¹) ^ d * W (r⁻¹ • (y - x)) ≤ 2 * C * R := by
    calc
      (r⁻¹) ^ d * W (r⁻¹ • (y - x)) ≤ 1 * (C * L) :=
        mul_le_mul hrpow (hWnear _) (hWnonneg _) (by positivity)
      _ = C * L := one_mul _
      _ ≤ C * (2 * R) := mul_le_mul_of_nonneg_left hLle hC.le
      _ = 2 * C * R := by ring
  have hWargcont : Continuous (fun y : Euclidean d => W (r⁻¹ • (y - x))) :=
    hWcont.comp
      ((continuous_const : Continuous (fun _ : Euclidean d => r⁻¹)).smul
        (continuous_id.sub (continuous_const : Continuous (fun _ : Euclidean d => x))))
  have hleftcont : Continuous (fun y : Euclidean d => ‖f y‖ *
      ((r⁻¹) ^ d * W (r⁻¹ • (y - x)))) :=
    f.continuous.norm.mul (continuous_const.mul hWargcont)
  have hrightint : Integrable (fun y : Euclidean d => ‖f y‖ * (2 * C * R)) :=
    f.integrable.norm.mul_const (2 * C * R)
  have hleftint : Integrable (fun y : Euclidean d => ‖f y‖ *
      ((r⁻¹) ^ d * W (r⁻¹ • (y - x)))) := by
    refine hrightint.mono' hleftcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg]
    · exact mul_le_mul_of_nonneg_left (hkernel y) (norm_nonneg _)
    · exact mul_nonneg (norm_nonneg _)
        (mul_nonneg (pow_nonneg (inv_nonneg.mpr hrpos.le) _) (hWnonneg _))
  have hint :
      (∫ y : Euclidean d, ‖f y‖ *
        ((r⁻¹) ^ d * W (r⁻¹ • (y - x)))) ≤
        ∫ y : Euclidean d, ‖f y‖ * (2 * C * R) := by
    apply integral_mono hleftint hrightint
    intro y
    exact mul_le_mul_of_nonneg_left (hkernel y) (norm_nonneg _)
  calc
    ‖sphericalAverage d
        (fun z : Euclidean d =>
          𝓕⁻ (fun ξ : Euclidean d => ψ (R⁻¹ • ξ) *
            𝓕 (f : Euclidean d → ℂ) ξ) z) r x‖ =
        ‖sphericalAverage d
          (fun z : Euclidean d =>
            ((fun y : Euclidean d => R ^ d • K (R • y))
              ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (f : Euclidean d → ℂ)) z) r x‖ := by
      congr 2
      funext z
      exact hphysical z
    _ ≤ ∫ y : Euclidean d, ‖f y‖ *
        (∫ w : Metric.sphere (0 : Euclidean d) 1,
          ‖R ^ d • K (R • (x + r • (w : Euclidean d) - y))‖
          ∂unitSurfaceMeasure d) :=
      norm_sphericalAverage_scaled_schwartz_convolution_le K f
        (lt_of_lt_of_le zero_lt_one hR) x
    _ = ∫ y : Euclidean d, ‖f y‖ *
        ((r⁻¹) ^ d * W (r⁻¹ • (y - x))) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [hinner]
    _ ≤ ∫ y : Euclidean d, ‖f y‖ * (2 * C * R) := hint
    _ = 2 * C * R * ∫ y : Euclidean d, ‖f y‖ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring

end

end LeanSpherical.HarmonicAnalysis
