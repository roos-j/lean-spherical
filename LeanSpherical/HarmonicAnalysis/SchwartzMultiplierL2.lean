/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.MultiplierL2
import LeanSpherical.HarmonicAnalysis.SchwartzFourierBridge

/-!
# Literal `L²` estimate for smooth Fourier multipliers

For Schwartz frequency data, Plancherel's `L²` multiplier estimate agrees
with the literal inverse Fourier integral.  This supplies a genuine
square-integral estimate for smooth localized multipliers, rather than an
estimate only for abstract `Lp` representatives.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

noncomputable section

/-- Plancherel's identity for the literal Fourier transform of Schwartz
data.  Keeping this as an integral identity lets localized maximal estimates
be stated in terms of the physical-space `L²` norm of their input. -/
theorem integral_norm_sq_fourier_schwartz_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (f : SchwartzMap E ℂ) :
    (∫ ξ : E, ‖𝓕 (f : E → ℂ) ξ‖ ^ 2) =
      ∫ x : E, ‖f x‖ ^ 2 := by
  let fLp : Lp ℂ 2 (volume : Measure E) := f.toLp 2
  have hplancherel : ‖𝓕 fLp‖ = ‖fLp‖ := Lp.norm_fourier_eq fLp
  have hleft : ‖(𝓕 f).toLp 2‖ =
      √(∫ ξ : E, ‖𝓕 (f : E → ℂ) ξ‖ ^ 2) := by
    simpa [SchwartzMap.fourier_coe, Real.sqrt_eq_rpow] using
      (SchwartzMap.norm_toLp' (f := (𝓕 f)) (p := 2) (μ := volume)
        (by norm_num) (by norm_num))
  have hright : ‖f.toLp 2‖ = √(∫ x : E, ‖f x‖ ^ 2) := by
    simpa [Real.sqrt_eq_rpow] using
      (SchwartzMap.norm_toLp' (f := f) (p := 2) (μ := volume)
        (by norm_num) (by norm_num))
  rw [SchwartzMap.toLp_fourier_eq, hleft, hright] at hplancherel
  have hleft_nonneg : 0 ≤ ∫ ξ : E, ‖𝓕 (f : E → ℂ) ξ‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hright_nonneg : 0 ≤ ∫ x : E, ‖f x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hsq := congrArg (fun x : ℝ => x ^ 2) hplancherel
  simpa only [Real.sq_sqrt hleft_nonneg, Real.sq_sqrt hright_nonneg] using hsq

/-- A pointwise bounded Schwartz multiplier obeys the literal Plancherel
square-integral estimate on Schwartz data. -/
theorem integral_norm_sq_fourierInv_schwartz_multiplier_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (m g : SchwartzMap E ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hmC : ∀ ξ, ‖m ξ‖ ≤ C) :
    (∫ x : E, ‖𝓕⁻ (fun ξ : E => m ξ * g ξ) x‖ ^ 2) ≤
      C ^ 2 * ∫ ξ : E, ‖g ξ‖ ^ 2 := by
  let h : SchwartzMap E ℂ :=
    SchwartzMap.smulLeftCLM ℂ (m : E → ℂ) g
  let mLp : Lp ℂ ⊤ (volume : Measure E) :=
    (memLp_top_of_bound m.continuous.aestronglyMeasurable C
      (Filter.Eventually.of_forall hmC)).toLp m
  have hmLp_ae : (mLp : E → ℂ) =ᵐ[volume] m := by
    exact MemLp.coeFn_toLp _
  have hmLp : ‖mLp‖ ≤ C := by
    rw [Lp.norm_def, eLpNorm_congr_ae hmLp_ae, eLpNorm_exponent_top]
    exact ENNReal.toReal_le_of_le_ofReal hC
      (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hmC))
  have hmul : h.toLp 2 = mLp • g.toLp 2 := by
    apply Lp.ext
    filter_upwards [SchwartzMap.coeFn_toLp h 2 volume,
      Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) mLp (g.toLp 2), hmLp_ae,
      SchwartzMap.coeFn_toLp g 2 volume] with x hx hsmul hm hg
    rw [hx, hsmul]
    simp only [smul_eq_mul, Pi.mul_apply, hm, hg]
    simp only [h, SchwartzMap.smulLeftCLM_apply m.hasTemperateGrowth, smul_eq_mul]
  have hproduct : ‖h.toLp 2‖ ≤ C * ‖g.toLp 2‖ := by
    rw [hmul]
    exact (Lp.norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_right hmLp (norm_nonneg _))
  let hLp : Lp ℂ 2 (volume : Measure E) := h.toLp 2
  have hinvLp : 𝓕⁻ hLp = (𝓕⁻ h).toLp 2 := by
    dsimp only [hLp]
    exact SchwartzMap.toLp_fourierInv_eq h
  have hplancherel' : ‖𝓕⁻ hLp‖ = ‖hLp‖ := by
    calc
      ‖𝓕⁻ hLp‖ = ‖𝓕 (𝓕⁻ hLp)‖ := (Lp.norm_fourier_eq _).symm
      _ = ‖hLp‖ := by rw [fourier_fourierInv_eq]
  have hplancherel : ‖(𝓕⁻ h).toLp 2‖ = ‖h.toLp 2‖ := by
    rw [← hinvLp]
    exact hplancherel'
  have hnorm : ‖(𝓕⁻ h).toLp 2‖ ≤ C * ‖g.toLp 2‖ := by
    rw [hplancherel]
    exact hproduct
  have hinvnorm : ‖(𝓕⁻ h).toLp 2‖ =
      √(∫ x : E, ‖𝓕⁻ (h : E → ℂ) x‖ ^ 2) := by
    simpa [SchwartzMap.fourierInv_coe, Real.sqrt_eq_rpow] using
      (SchwartzMap.norm_toLp' (f := (𝓕⁻ h)) (p := 2) (μ := volume)
        (by norm_num) (by norm_num))
  have hgnorm : ‖g.toLp 2‖ = √(∫ x : E, ‖g x‖ ^ 2) := by
    simpa [Real.sqrt_eq_rpow] using
      (SchwartzMap.norm_toLp' (f := g) (p := 2) (μ := volume)
        (by norm_num) (by norm_num))
  rw [hinvnorm, hgnorm] at hnorm
  have hI : 0 ≤ ∫ x : E, ‖𝓕⁻ (h : E → ℂ) x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hJ : 0 ≤ ∫ x : E, ‖g x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hsq : (√(∫ x : E, ‖𝓕⁻ (h : E → ℂ) x‖ ^ 2)) ^ 2 ≤
      (C * √(∫ x : E, ‖g x‖ ^ 2)) ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).2 hnorm
  calc
    (∫ x : E, ‖𝓕⁻ (fun ξ : E => m ξ * g ξ) x‖ ^ 2) =
        (∫ x : E, ‖𝓕⁻ (h : E → ℂ) x‖ ^ 2) := by
      congr 3
      funext x
      congr 2
      simp only [h, SchwartzMap.smulLeftCLM_apply m.hasTemperateGrowth, smul_eq_mul]
    _ = (√(∫ x : E, ‖𝓕⁻ (h : E → ℂ) x‖ ^ 2)) ^ 2 :=
      (Real.sq_sqrt hI).symm
    _ ≤ (C * √(∫ x : E, ‖g x‖ ^ 2)) ^ 2 := hsq
    _ = C ^ 2 * ∫ ξ : E, ‖g ξ‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hJ]

/-- The literal Plancherel identity for one Schwartz multiplier.  This is the
equality used when finitely many scale blocks are recombined by a square
function, rather than estimating the blocks separately. -/
theorem integral_norm_sq_fourierInv_schwartz_multiplier_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (m g : SchwartzMap E ℂ) :
    (∫ x : E, ‖𝓕⁻ (fun ξ : E => m ξ * g ξ) x‖ ^ 2) =
      ∫ ξ : E, ‖m ξ * g ξ‖ ^ 2 := by
  let h : SchwartzMap E ℂ :=
    SchwartzMap.smulLeftCLM ℂ (m : E → ℂ) g
  have hh : (h : E → ℂ) = fun ξ : E => m ξ * g ξ := by
    funext ξ
    simp only [h, SchwartzMap.smulLeftCLM_apply m.hasTemperateGrowth, smul_eq_mul]
  have hinv : ((𝓕⁻ h : SchwartzMap E ℂ) : E → ℂ) =
      𝓕⁻ (fun ξ : E => m ξ * g ξ) := by
    rw [SchwartzMap.fourierInv_coe, hh]
  have hfourier : 𝓕 ((𝓕⁻ h : SchwartzMap E ℂ) : E → ℂ) = (h : E → ℂ) := by
    rw [← SchwartzMap.fourier_coe, fourier_fourierInv_eq]
  calc
    (∫ x : E, ‖𝓕⁻ (fun ξ : E => m ξ * g ξ) x‖ ^ 2) =
        ∫ x : E, ‖(𝓕⁻ h : SchwartzMap E ℂ) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hinv]
    _ = ∫ ξ : E, ‖𝓕 ((𝓕⁻ h : SchwartzMap E ℂ) : E → ℂ) ξ‖ ^ 2 :=
      (integral_norm_sq_fourier_schwartz_eq (𝓕⁻ h : SchwartzMap E ℂ)).symm
    _ = ∫ ξ : E, ‖m ξ * g ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hfourier, hh]

/-- The literal inverse transform of a product of two Schwartz multipliers
has an integrable squared norm. -/
theorem integrable_norm_sq_fourierInv_schwartz_multiplier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (m g : SchwartzMap E ℂ) :
    Integrable (fun x : E => ‖𝓕⁻ (fun ξ : E => m ξ * g ξ) x‖ ^ 2) volume := by
  let h : SchwartzMap E ℂ :=
    SchwartzMap.smulLeftCLM ℂ (m : E → ℂ) g
  have hh : (h : E → ℂ) = fun ξ : E => m ξ * g ξ := by
    funext ξ
    simp only [h, SchwartzMap.smulLeftCLM_apply m.hasTemperateGrowth, smul_eq_mul]
  have hinv : ((𝓕⁻ h : SchwartzMap E ℂ) : E → ℂ) =
      𝓕⁻ (fun ξ : E => m ξ * g ξ) := by
    rw [SchwartzMap.fourierInv_coe, hh]
  have hsq : Integrable (fun x : E => ‖(𝓕⁻ h : SchwartzMap E ℂ) x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (𝓕⁻ h : SchwartzMap E ℂ).continuous.aestronglyMeasurable).mp
      ((𝓕⁻ h : SchwartzMap E ℂ).memLp 2 volume)
  apply hsq.congr
  filter_upwards with x
  rw [hinv]

/-- Finite Plancherel square-function recombination for literal Schwartz
Fourier multipliers.  The sole analytic hypothesis is the pointwise finite
overlap bound on the multiplier family. -/
theorem sum_integral_norm_sq_fourierInv_schwartz_multipliers_le
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (s : Finset ι) (m : ι → SchwartzMap E ℂ) (f : SchwartzMap E ℂ)
    {C : ℝ}
    (hoverlap : ∀ ξ : E, ∑ i ∈ s, ‖m i ξ‖ ^ (2 : ℕ) ≤ C) :
    (∑ i ∈ s, ∫ x : E,
      ‖𝓕⁻ (fun ξ : E => m i ξ * 𝓕 (f : E → ℂ) ξ) x‖ ^ (2 : ℕ)) ≤
        C * ∫ x : E, ‖f x‖ ^ (2 : ℕ) := by
  classical
  let g : SchwartzMap E ℂ := 𝓕 f
  have hpiece_int (i : ι) (hi : i ∈ s) :
      Integrable (fun ξ : E => ‖m i ξ * g ξ‖ ^ (2 : ℕ)) volume := by
    let h : SchwartzMap E ℂ :=
      SchwartzMap.smulLeftCLM ℂ (m i : E → ℂ) g
    have hsq : Integrable (fun ξ : E => ‖h ξ‖ ^ (2 : ℕ)) volume :=
      (memLp_two_iff_integrable_sq_norm h.continuous.aestronglyMeasurable).mp
        (h.memLp 2 volume)
    simpa only [h, SchwartzMap.smulLeftCLM_apply (m i).hasTemperateGrowth,
      smul_eq_mul] using hsq
  have hsum_int : Integrable (fun ξ : E =>
      ∑ i ∈ s, ‖m i ξ * g ξ‖ ^ (2 : ℕ)) volume :=
    integrable_finsetSum s hpiece_int
  have hg_sq : Integrable (fun ξ : E => ‖g ξ‖ ^ (2 : ℕ)) volume :=
    (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).mp
      (g.memLp 2 volume)
  have hpoint (ξ : E) :
      (∑ i ∈ s, ‖m i ξ * g ξ‖ ^ (2 : ℕ)) ≤ C * ‖g ξ‖ ^ (2 : ℕ) := by
    calc
      (∑ i ∈ s, ‖m i ξ * g ξ‖ ^ (2 : ℕ)) =
          ∑ i ∈ s, ‖m i ξ‖ ^ (2 : ℕ) * ‖g ξ‖ ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_mul, mul_pow]
      _ = (∑ i ∈ s, ‖m i ξ‖ ^ (2 : ℕ)) * ‖g ξ‖ ^ (2 : ℕ) := by
        rw [Finset.sum_mul]
      _ ≤ C * ‖g ξ‖ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right (hoverlap ξ) (sq_nonneg _)
  change (∑ i ∈ s, ∫ x : E,
    ‖𝓕⁻ (fun ξ : E => m i ξ * g ξ) x‖ ^ (2 : ℕ)) ≤
      C * ∫ x : E, ‖f x‖ ^ (2 : ℕ)
  calc
    (∑ i ∈ s, ∫ x : E,
      ‖𝓕⁻ (fun ξ : E => m i ξ * g ξ) x‖ ^ (2 : ℕ)) =
        ∑ i ∈ s, ∫ ξ : E, ‖m i ξ * g ξ‖ ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_norm_sq_fourierInv_schwartz_multiplier_eq (m i) g
    _ = ∫ ξ : E, ∑ i ∈ s, ‖m i ξ * g ξ‖ ^ (2 : ℕ) := by
      exact (integral_finsetSum s hpiece_int).symm
    _ ≤ ∫ ξ : E, C * ‖g ξ‖ ^ (2 : ℕ) :=
      integral_mono hsum_int (hg_sq.const_mul C) hpoint
    _ = C * ∫ ξ : E, ‖g ξ‖ ^ (2 : ℕ) := by
      rw [integral_const_mul]
    _ = C * ∫ x : E, ‖f x‖ ^ (2 : ℕ) := by
      dsimp only [g]
      rw [SchwartzMap.fourier_coe f, integral_norm_sq_fourier_schwartz_eq f]

end

end LeanSpherical.HarmonicAnalysis
