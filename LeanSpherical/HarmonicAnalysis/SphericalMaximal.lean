/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SphericalMaximalAssembly
import LeanSpherical.HarmonicAnalysis.SurfaceCore
import LeanSpherical.HarmonicAnalysis.SphericalAverages

/-!
# Stein's spherical maximal theorem
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Set Filter
open scoped Convolution FourierTransform Topology

noncomputable section

set_option maxHeartbeats 1000000 in
private theorem relative_cutoff_tendsto_spherical_average
    {d : ℕ} (hd0 : 0 < d) (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1) (f : SchwartzMap (Euclidean d) ℂ) (r : ℝ)
    (x : Euclidean d) :
    Tendsto (fun N : ℕ =>
      𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r • ξ) *
          φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x) atTop
      (𝓝 (sphericalAverage d (f : Euclidean d → ℂ) r x)) := by
  have hmass : 0 < surfaceMass d := surfaceMass_pos hd0
  have hφbound (ξ : Euclidean d) : ‖φ ξ‖ ≤ ‖φ.toBoundedContinuousFunction‖ := by
    change ‖φ.toBoundedContinuousFunction ξ‖ ≤ ‖φ.toBoundedContinuousFunction‖
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  have hchar (ξ : Euclidean d) : ‖(Real.fourierChar (inner ℝ ξ x) : ℂ)‖ = 1 := by
    rw [Real.fourierChar_apply]
    exact Complex.norm_exp_ofReal_mul_I _
  have hchar_cont : Continuous
      (fun ξ : Euclidean d => (Real.fourierChar (inner ℝ ξ x) : ℂ)) :=
    (Real.continuous_fourierChar.comp
      (continuous_id.inner (continuous_const : Continuous fun _ : Euclidean d => x))
      |> continuous_subtype_val.comp)
  let F : ℕ → Euclidean d → ℂ := fun N ξ =>
    (Real.fourierChar (inner ℝ ξ x) : ℂ) *
      (surfaceFourier d (-r • ξ) *
        φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ)) *
        𝓕 (f : Euclidean d → ℂ) ξ)
  let G : Euclidean d → ℂ := fun ξ =>
    (Real.fourierChar (inner ℝ ξ x) : ℂ) *
      (surfaceFourier d (-r • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ)
  have hFmeas (N : ℕ) : AEStronglyMeasurable (F N) volume := by
    dsimp only [F]
    have hsurf : Continuous (fun ξ : Euclidean d => surfaceFourier d (-r • ξ)) :=
      (continuous_surfaceFourier d).comp
        ((continuous_const : Continuous fun _ : Euclidean d => -r).smul continuous_id)
    have hcut : Continuous (fun ξ : Euclidean d =>
        φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ))) :=
      φ.continuous.comp
        ((continuous_const : Continuous fun _ : Euclidean d => ((2 : ℝ) ^ N)⁻¹).smul
          ((continuous_const : Continuous fun _ : Euclidean d => r).smul continuous_id))
    exact (hchar_cont.mul ((hsurf.mul hcut).mul (𝓕 f).continuous)).aestronglyMeasurable
  let B : ℝ := surfaceMass d * ‖φ.toBoundedContinuousFunction‖
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hbound_int : Integrable (fun ξ : Euclidean d =>
      B * ‖𝓕 (f : Euclidean d → ℂ) ξ‖) volume :=
    (𝓕 f).integrable.norm.const_mul B
  have hbound (N : ℕ) : ∀ᵐ ξ : Euclidean d ∂volume,
      ‖F N ξ‖ ≤ B * ‖𝓕 (f : Euclidean d → ℂ) ξ‖ := by
    filter_upwards with ξ
    dsimp only [F]
    rw [norm_mul, hchar, one_mul, norm_mul, norm_mul]
    calc
      ‖surfaceFourier d (-r • ξ)‖ * ‖φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ))‖ *
          ‖𝓕 (f : Euclidean d → ℂ) ξ‖ ≤
          (surfaceMass d * ‖φ.toBoundedContinuousFunction‖) *
            ‖𝓕 (f : Euclidean d → ℂ) ξ‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul
            (by simpa [surfaceMass] using
              norm_surfaceFourier_le_surfaceMass d (-r • ξ))
            (hφbound _)
            (norm_nonneg _) hmass.le
        · exact norm_nonneg _
      _ = B * ‖𝓕 (f : Euclidean d → ℂ) ξ‖ := rfl
  have hscale (ξ : Euclidean d) : Tendsto (fun N : ℕ =>
      ((2 : ℝ) ^ N)⁻¹ • (r • ξ)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => ((2 : ℝ)⁻¹) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hconst : Tendsto (fun _ : ℕ => r • ξ) atTop (𝓝 (r • ξ)) :=
      tendsto_const_nhds
    simpa [inv_pow] using hpow.smul hconst
  have hφlim (ξ : Euclidean d) : Tendsto (fun N : ℕ =>
      φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ))) atTop (𝓝 (1 : ℂ)) := by
    have hzero : φ (0 : Euclidean d) = 1 := hφone 0 (by simp)
    rw [← hzero]
    exact φ.continuous.tendsto 0 |>.comp (hscale ξ)
  have hFlim : ∀ᵐ ξ : Euclidean d ∂volume,
      Tendsto (fun N : ℕ => F N ξ) atTop (𝓝 (G ξ)) := by
    filter_upwards with ξ
    dsimp only [F, G]
    have hchar' : Tendsto
        (fun _ : ℕ => (Real.fourierChar (inner ℝ ξ x) : ℂ)) atTop
        (𝓝 (Real.fourierChar (inner ℝ ξ x) : ℂ)) := tendsto_const_nhds
    have hsurf' : Tendsto (fun _ : ℕ => surfaceFourier d (-r • ξ)) atTop
        (𝓝 (surfaceFourier d (-r • ξ))) := tendsto_const_nhds
    have hfourier' : Tendsto (fun _ : ℕ => 𝓕 (f : Euclidean d → ℂ) ξ) atTop
        (𝓝 (𝓕 (f : Euclidean d → ℂ) ξ)) := tendsto_const_nhds
    simpa using hchar'.mul ((hsurf'.mul (hφlim ξ)).mul hfourier')
  have hInt := tendsto_integral_of_dominated_convergence
    (F := F) (f := G) (fun ξ : Euclidean d =>
      B * ‖𝓕 (f : Euclidean d → ℂ) ξ‖)
    hFmeas hbound_int hbound hFlim
  rw [show (fun N : ℕ =>
      𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r • ξ) *
          φ (((2 : ℝ) ^ N)⁻¹ • (r • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x) =
      fun N => ∫ ξ : Euclidean d, F N ξ by
        funext N
        rw [Real.fourierInv_eq]
        rfl,
    show sphericalAverage d (f : Euclidean d → ℂ) r x = ∫ ξ : Euclidean d, G ξ by
        rw [sphericalAverage_eq_fourierInv_surfaceMultiplier_schwartz f r,
          Real.fourierInv_eq]
        rfl]
  exact hInt

private def relativeCutoffRaw
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ) :
    ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ENNReal :=
  fun N f x =>
    ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (-r.1 • ξ) *
        φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
        𝓕 (f : Euclidean d → ℂ) ξ) x‖
/- The `toReal` in `P` is harmless: every cutoff supremum has a finite
uniform Fourier-integral bound for a Schwartz input. -/

private theorem relative_cutoff_raw_ne_top
    {d : ℕ} (hd0 : 0 < d) (φ : SchwartzMap (Euclidean d) ℂ)
    (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    relativeCutoffRaw φ N f x ≠ ⊤ := by
  change (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
    surfaceFourier d (-r.1 • ξ) *
      φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
      𝓕 (f : Euclidean d → ℂ) ξ) x‖) ≠ ⊤
  have hmass : 0 < surfaceMass d := surfaceMass_pos hd0
  have hφbound (ξ : Euclidean d) : ‖φ ξ‖ ≤ ‖φ.toBoundedContinuousFunction‖ := by
    change ‖φ.toBoundedContinuousFunction ξ‖ ≤ ‖φ.toBoundedContinuousFunction‖
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  let B : ℝ := surfaceMass d * ‖φ.toBoundedContinuousFunction‖
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply iSup_le
  intro r
  apply ENNReal.ofReal_le_ofReal
  rw [Real.fourierInv_eq]
  change ‖∫ ξ : Euclidean d, (Real.fourierChar (inner ℝ ξ x) : ℂ) *
    (surfaceFourier d (-r.1 • ξ) *
      φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
      𝓕 (f : Euclidean d → ℂ) ξ)‖ ≤ _
  calc
    ‖∫ ξ : Euclidean d, (Real.fourierChar (inner ℝ ξ x) : ℂ) *
        (surfaceFourier d (-r.1 • ξ) *
          φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ)‖ ≤
        ∫ ξ : Euclidean d, ‖(Real.fourierChar (inner ℝ ξ x) : ℂ) *
          (surfaceFourier d (-r.1 • ξ) *
            φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : Euclidean d, B * ‖𝓕 (f : Euclidean d → ℂ) ξ‖ := by
      apply integral_mono_ae
      · refine ((𝓕 f).integrable.norm.const_mul B).mono' ?_ ?_
        · have hchar_cont : Continuous
            (fun ξ : Euclidean d => (Real.fourierChar (inner ℝ ξ x) : ℂ)) :=
            (Real.continuous_fourierChar.comp
              (continuous_id.inner (continuous_const : Continuous fun _ : Euclidean d => x))
              |> continuous_subtype_val.comp)
          have hsurf : Continuous (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ)) :=
            (continuous_surfaceFourier d).comp
              ((continuous_const : Continuous fun _ : Euclidean d => -r.1).smul continuous_id)
          have hcut : Continuous (fun ξ : Euclidean d =>
              φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ))) :=
            φ.continuous.comp
              ((continuous_const : Continuous fun _ : Euclidean d => ((2 : ℝ) ^ N)⁻¹).smul
                ((continuous_const : Continuous fun _ : Euclidean d => r.1).smul continuous_id))
          exact ((hchar_cont.mul ((hsurf.mul hcut).mul (𝓕 f).continuous)).norm).aestronglyMeasurable
        · filter_upwards with ξ
          dsimp only [B]
          have hchar : ‖(Real.fourierChar (inner ℝ ξ x) : ℂ)‖ = 1 := by
            rw [Real.fourierChar_apply]
            exact Complex.norm_exp_ofReal_mul_I _
          simp only [norm_mul, norm_norm, hchar, one_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul
              (by simpa [surfaceMass] using
                norm_surfaceFourier_le_surfaceMass d (-r.1 • ξ))
              (hφbound _)
              (norm_nonneg _) hmass.le)
            (norm_nonneg _)
      · exact (𝓕 f).integrable.norm.const_mul B
      · filter_upwards with ξ
        dsimp only [B]
        have hchar : ‖(Real.fourierChar (inner ℝ ξ x) : ℂ)‖ = 1 := by
          rw [Real.fourierChar_apply]
          exact Complex.norm_exp_ofReal_mul_I _
        simp only [norm_mul, norm_norm, hchar, one_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul
            (by simpa [surfaceMass] using
              norm_surfaceFourier_le_surfaceMass d (-r.1 • ξ))
            (hφbound _)
            (norm_nonneg _) hmass.le)
          (norm_nonneg _)
    _ = B * ∫ ξ : Euclidean d, ‖𝓕 (f : Euclidean d → ℂ) ξ‖ := by
      rw [integral_const_mul]

private theorem spherical_average_power_le_liminf_relative_cutoff
    {d : ℕ} {p : ℝ} (hd0 : 0 < d) (hpNN : 0 ≤ p)
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (f : SchwartzMap (Euclidean d) ℂ)
    (r : Ioi (0 : ℝ)) (x : Euclidean d) :
    ENNReal.ofReal (‖sphericalAverage d (f : Euclidean d → ℂ) r.1 x‖ ^ p) ≤
      liminf (fun N : ℕ =>
        ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) atTop := by
  let W : ℕ → ℂ := fun N => 𝓕⁻ (fun ξ : Euclidean d =>
    surfaceFourier d (-r.1 • ξ) *
      φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
      𝓕 (f : Euclidean d → ℂ) ξ) x
  have hW : Tendsto W atTop
      (𝓝 (sphericalAverage d (f : Euclidean d → ℂ) r.1 x)) := by
    simpa only [W] using relative_cutoff_tendsto_spherical_average hd0 φ hφone f r.1 x
  have hE : Tendsto (fun N : ℕ => ENNReal.ofReal ‖W N‖) atTop
      (𝓝 (ENNReal.ofReal ‖sphericalAverage d (f : Euclidean d → ℂ) r.1 x‖)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hW.norm
  have hPow : Tendsto (fun N : ℕ => (ENNReal.ofReal ‖W N‖) ^ p) atTop
      (𝓝 ((ENNReal.ofReal ‖sphericalAverage d (f : Euclidean d → ℂ) r.1 x‖) ^ p)) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp hE
  have hPow' : Tendsto (fun N : ℕ => ENNReal.ofReal (‖W N‖ ^ p)) atTop
      (𝓝 (ENNReal.ofReal (‖sphericalAverage d (f : Euclidean d → ℂ) r.1 x‖ ^ p))) := by
    simpa only [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpNN] using hPow
  have hle (N : ℕ) : ENNReal.ofReal (‖W N‖ ^ p) ≤
      ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p) := by
    have hU_nonneg : 0 ≤ relativeCutoffMaximal d φ N f x := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpNN,
      ← ENNReal.ofReal_rpow_of_nonneg hU_nonneg hpNN]
    apply ENNReal.rpow_le_rpow _ hpNN
    rw [show ENNReal.ofReal (relativeCutoffMaximal d φ N f x) =
        relativeCutoffRaw φ N f x by
      change ENNReal.ofReal ((relativeCutoffRaw φ N f x).toReal) =
        relativeCutoffRaw φ N f x
      exact ENNReal.ofReal_toReal (relative_cutoff_raw_ne_top hd0 φ N f x)]
    dsimp only [relativeCutoffRaw, W]
    exact le_iSup (fun s : Ioi (0 : ℝ) => ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (-s.1 • ξ) *
        φ (((2 : ℝ) ^ N)⁻¹ • (s.1 • ξ)) *
        𝓕 (f : Euclidean d → ℂ) ξ) x‖) r
  calc
    ENNReal.ofReal (‖sphericalAverage d (f : Euclidean d → ℂ) r.1 x‖ ^ p) =
        liminf (fun N : ℕ => ENNReal.ofReal (‖W N‖ ^ p)) atTop := hPow'.liminf_eq.symm
    _ ≤ liminf (fun N : ℕ => ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) atTop :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)

private theorem normalized_spherical_maximal_power_le_liminf_relative_cutoff
    {d : ℕ} {p : ℝ} (hd0 : 0 < d) (hp0 : 0 < p) (hpNN : 0 ≤ p)
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    ENNReal.ofReal
        ((normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal ^ p) ≤
      (ENNReal.ofReal ((surfaceMass d)⁻¹)) ^ p *
        liminf (fun N : ℕ =>
          ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) atTop := by
  have hmass : 0 < surfaceMass d := surfaceMass_pos hd0
  let V : SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
    fun f x => (normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal
  let K : ENNReal := (ENNReal.ofReal ((surfaceMass d)⁻¹)) ^ p
  have hKtop : K ≠ ⊤ := by
    dsimp only [K]
    exact ENNReal.rpow_ne_top_of_nonneg hpNN ENNReal.ofReal_ne_top
  have hKpos : 0 < K := by
    dsimp only [K]
    apply ENNReal.rpow_pos
    · exact ENNReal.ofReal_pos.mpr (inv_pos.mpr hmass)
    · exact ENNReal.ofReal_ne_top
  have hnorm (f : SchwartzMap (Euclidean d) ℂ)
      (r : ℝ) (x : Euclidean d) :
      ENNReal.ofReal (‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r x‖ ^ p) =
        K * ENNReal.ofReal (‖sphericalAverage d (f : Euclidean d → ℂ) r x‖ ^ p) := by
    dsimp only [K]
    rw [normalizedSphericalAverage, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hmass]
    rw [Real.mul_rpow (inv_nonneg.mpr hmass.le) (norm_nonneg _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hmass.le) p)]
    rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hmass.le) hpNN]
  have hnormalfixed (f : SchwartzMap (Euclidean d) ℂ)
      (r : Ioi (0 : ℝ)) (x : Euclidean d) :
      ENNReal.ofReal (‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r.1 x‖ ^ p) ≤
        K * liminf (fun N : ℕ => ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) atTop := by
    rw [hnorm]
    exact mul_le_mul_right
      (spherical_average_power_le_liminf_relative_cutoff hd0 hpNN φ hφone f r x) K
  have hVtop (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
      normalizedSphericalMaximal d (f : Euclidean d → ℂ) x ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply normalizedSphericalMaximal_le_of_norm_le hd0 _ x
    intro y
    change ‖f.toBoundedContinuousFunction y‖ ≤ ‖f.toBoundedContinuousFunction‖
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  have hV_eq (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
      ENNReal.ofReal (V f x) = normalizedSphericalMaximal d (f : Euclidean d → ℂ) x := by
    exact ENNReal.ofReal_toReal (hVtop f x)
  have hpoint (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
      ENNReal.ofReal ((V f x) ^ p) ≤
        K * liminf (fun N : ℕ => ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) atTop := by
    have hVnonneg : 0 ≤ V f x := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_rpow_of_nonneg hVnonneg hpNN, hV_eq]
    unfold normalizedSphericalMaximal
    have hpowmax :
        (⨆ r : Ioi (0 : ℝ),
          ENNReal.ofReal ‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r.1 x‖) ^ p =
          ⨆ r : Ioi (0 : ℝ),
            (ENNReal.ofReal ‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r.1 x‖) ^ p := by
      let e : ENNReal ≃o ENNReal :=
        (ENNReal.strictMono_rpow_of_pos hp0).orderIsoOfSurjective _
          (ENNReal.rpow_left_bijective hp0.ne.symm).2
      change e (⨆ r : Ioi (0 : ℝ),
        ENNReal.ofReal ‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r.1 x‖) =
          ⨆ r : Ioi (0 : ℝ),
            e (ENNReal.ofReal ‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r.1 x‖)
      exact e.map_iSup _
    rw [hpowmax]
    apply iSup_le
    intro r
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpNN]
    exact hnormalfixed f r x
  simpa only [K, V] using hpoint f x

private theorem relative_reassembly_lintegral_bound
    {d : ℕ} {p : ℝ} (hd : 3 ≤ d)
    (hp : (d : ℝ) / ((d : ℝ) - 1) < p)
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (A : ℝ) (hA : 0 < A)
    (hfinite : ∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      MemLp (relativeCutoffMaximal d φ N f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (relativeCutoffMaximal d φ N f x) ^ p) ≤
        A * ∫ x : Euclidean d, ‖f x‖ ^ p)
    (f : SchwartzMap (Euclidean d) ℂ) :
    (∫⁻ x : Euclidean d,
      ENNReal.ofReal
        ((normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal ^ p)) ≤
      (ENNReal.ofReal ((surfaceMass d)⁻¹)) ^ p *
        ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) := by
  have hd0 : 0 < d := by omega
  have hp0 : 0 < p := by
    have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hden : 0 < (d : ℝ) - 1 := by linarith
    have hfrac : 0 < (d : ℝ) / ((d : ℝ) - 1) := by
      apply div_pos <;> linarith
    exact lt_trans hfrac hp
  have hpNN : 0 ≤ p := hp0.le
  let K : ENNReal := (ENNReal.ofReal ((surfaceMass d)⁻¹)) ^ p
  have hKtop : K ≠ ⊤ := by
    dsimp only [K]
    exact ENNReal.rpow_ne_top_of_nonneg hpNN ENNReal.ofReal_ne_top
  have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hUmeas (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
      AEMeasurable (fun x : Euclidean d => ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) volume := by
    have hmeas : AEMeasurable (fun x : Euclidean d =>
        (ENNReal.ofReal (relativeCutoffMaximal d φ N f x)) ^ p) volume :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        ((hfinite N f).1.1.aemeasurable.ennreal_ofReal)
    convert hmeas using 1
    funext x
    exact (ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hpNN).symm
  have hUPowInt (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
      Integrable (fun x : Euclidean d => (relativeCutoffMaximal d φ N f x) ^ p) volume := by
    have h := (hfinite N f).1.integrable_norm_rpow hpEN0 hpENT
    convert h using 1
    funext x
    change (relativeCutoffRaw φ N f x).toReal ^ p =
      |(relativeCutoffRaw φ N f x).toReal| ^ (ENNReal.ofReal p).toReal
    rw [abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.toReal_ofReal hpNN]
  have hUint (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
      (∫⁻ x : Euclidean d, ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) ≤
        ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) := by
    calc
      (∫⁻ x : Euclidean d, ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) =
          ENNReal.ofReal (∫ x : Euclidean d, (relativeCutoffMaximal d φ N f x) ^ p) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hUPowInt N f)]
        exact Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg ENNReal.toReal_nonneg p
      _ ≤ ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) :=
        ENNReal.ofReal_le_ofReal (hfinite N f).2
  have hFatou (f : SchwartzMap (Euclidean d) ℂ) :
      (∫⁻ x : Euclidean d, ENNReal.ofReal (((normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal) ^ p)) ≤
        K * liminf (fun N : ℕ =>
          ∫⁻ x : Euclidean d, ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) atTop := by
    calc
      (∫⁻ x : Euclidean d, ENNReal.ofReal (((normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal) ^ p)) ≤
          ∫⁻ x : Euclidean d, K *
            liminf (fun N : ℕ => ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) atTop :=
        lintegral_mono (fun x => normalized_spherical_maximal_power_le_liminf_relative_cutoff hd0 hp0 hpNN φ hφone f x)
      _ = K * (∫⁻ x : Euclidean d,
          liminf (fun N : ℕ => ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) atTop) :=
        lintegral_const_mul' K _ hKtop
      _ ≤ K * liminf (fun N : ℕ =>
          ∫⁻ x : Euclidean d, ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) atTop :=
        mul_le_mul_right (lintegral_liminf_le' fun N => hUmeas N f) K
  have hLiminfBound (f : SchwartzMap (Euclidean d) ℂ) :
      liminf (fun N : ℕ =>
        ∫⁻ x : Euclidean d, ENNReal.ofReal ((relativeCutoffMaximal d φ N f x) ^ p)) atTop ≤
        ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) := by
    exact Filter.liminf_le_of_frequently_le'
      (Filter.Frequently.of_forall fun N => hUint N f)
  have hlin (f : SchwartzMap (Euclidean d) ℂ) :
      (∫⁻ x : Euclidean d, ENNReal.ofReal (((normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal) ^ p)) ≤
        K * ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) :=
    (hFatou f).trans (mul_le_mul_right (hLiminfBound f) K)
  simpa only [K] using hlin f

private theorem relative_reassembly_finish
    {d : ℕ} {p : ℝ} (hd : 3 ≤ d)
    (hp : (d : ℝ) / ((d : ℝ) - 1) < p)
    (A : ℝ) (hA : 0 < A)
    (hlin : ∀ f : SchwartzMap (Euclidean d) ℂ,
      (∫⁻ x : Euclidean d,
        ENNReal.ofReal
          ((normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal ^ p)) ≤
        (ENNReal.ofReal ((surfaceMass d)⁻¹)) ^ p *
          ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (normalizedSphericalMaximalReal d f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (normalizedSphericalMaximalReal d f x) ^ p) ≤
        C * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  have hd0 : 0 < d := by omega
  have hmass : 0 < surfaceMass d := surfaceMass_pos hd0
  have hp0 : 0 < p := by
    have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hden : 0 < (d : ℝ) - 1 := by linarith
    have hfrac : 0 < (d : ℝ) / ((d : ℝ) - 1) := by
      apply div_pos <;> linarith
    exact lt_trans hfrac hp
  have hpNN : 0 ≤ p := hp0.le
  have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  let K : ENNReal := (ENNReal.ofReal ((surfaceMass d)⁻¹)) ^ p
  have hKtop : K ≠ ⊤ := by
    dsimp only [K]
    exact ENNReal.rpow_ne_top_of_nonneg hpNN ENNReal.ofReal_ne_top
  have hKpos : 0 < K := by
    dsimp only [K]
    apply ENNReal.rpow_pos
    · exact ENNReal.ofReal_pos.mpr (inv_pos.mpr hmass)
    · exact ENNReal.ofReal_ne_top
  let V : SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
    fun f x => (normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal
  let C : ℝ := K.toReal * A
  have hKrealpos : 0 < K.toReal := ENNReal.toReal_pos hKpos.ne' hKtop
  refine ⟨C, mul_pos hKrealpos hA, ?_⟩
  intro f
  have hinput_nonneg : 0 ≤ ∫ x : Euclidean d, ‖f x‖ ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
  have hright_nonneg : 0 ≤ A * ∫ x : Euclidean d, ‖f x‖ ^ p :=
    mul_nonneg hA.le hinput_nonneg
  have hrighttop : K * ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p) < ⊤ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hKtop) ENNReal.ofReal_lt_top
  have hlefttop : (∫⁻ x : Euclidean d, ENNReal.ofReal ((V f x) ^ p)) < ⊤ :=
    lt_of_le_of_lt (by simpa only [V] using hlin f) hrighttop
  have hVmeas : AEMeasurable (V f) volume := by
    dsimp only [V]
    exact (ENNReal.measurable_toReal.comp
      (measurable_normalizedSphericalMaximal (f : Euclidean d → ℂ) f.continuous)).aemeasurable
  have hVmem : MemLp (V f) (ENNReal.ofReal p) volume :=
    memLp_of_lintegral_ofReal_rpow_lt_top (V f) hVmeas
      (fun x => ENNReal.toReal_nonneg) hp0 hlefttop
  have hVPowInt : Integrable (fun x : Euclidean d => (V f x) ^ p) volume := by
    have h := hVmem.integrable_norm_rpow hpEN0 hpENT
    convert h using 1
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.toReal_ofReal hpNN]
  have hleft_eq : (∫ x : Euclidean d, (V f x) ^ p) =
      (∫⁻ x : Euclidean d, ENNReal.ofReal ((V f x) ^ p)).toReal := by
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg ENNReal.toReal_nonneg p)
      hVPowInt.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · change MemLp (V f) (ENNReal.ofReal p) volume
    exact hVmem
  change (∫ x : Euclidean d, (V f x) ^ p) ≤ C * ∫ x : Euclidean d, ‖f x‖ ^ p
  rw [hleft_eq]
  calc
    (∫⁻ x : Euclidean d, ENNReal.ofReal ((V f x) ^ p)).toReal ≤
        (K * ENNReal.ofReal (A * ∫ x : Euclidean d, ‖f x‖ ^ p)).toReal :=
      (ENNReal.toReal_le_toReal hlefttop.ne hrighttop.ne).mpr (by simpa only [V] using hlin f)
    _ = K.toReal * (A * ∫ x : Euclidean d, ‖f x‖ ^ p) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hright_nonneg]
    _ = C * ∫ x : Euclidean d, ‖f x‖ ^ p := by
      dsimp only [C]
      ring

set_option maxHeartbeats 1000000 in
/-- Passing uniform finite relative-cutoff estimates to all radii. -/
theorem relative_reassembly_limit
    {d : ℕ} (hd : 3 ≤ d) {p : ℝ}
    (hp : (d : ℝ) / ((d : ℝ) - 1) < p)
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1) :
    ∀ A : ℝ, 0 < A →
      (∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
        MemLp (relativeCutoffMaximal d φ N f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (relativeCutoffMaximal d φ N f x) ^ p) ≤
          A * ∫ x : Euclidean d, ‖f x‖ ^ p) →
      ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
        MemLp (normalizedSphericalMaximalReal d f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (normalizedSphericalMaximalReal d f x) ^ p) ≤
          C * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  intro A hA hfinite
  exact relative_reassembly_finish hd hp A hA
    (fun f => relative_reassembly_lintegral_bound hd hp φ hφone A hA hfinite f)

set_option maxHeartbeats 1000000 in
/-- Stein's spherical maximal theorem, in its Schwartz-core form. -/
theorem stein_spherical_maximal
    {d : ℕ} (hd : 3 ≤ d) {p : ℝ}
    (hp : (d : ℝ) / ((d : ℝ) - 1) < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp
        (fun x : Euclidean d => (normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal)
        (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d,
        ((normalizedSphericalMaximal d (f : Euclidean d → ℂ) x).toReal) ^ p) ≤
        C * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  obtain ⟨φ, hφone, hφzero, hφnorm⟩ :=
    exists_schwartz_frequency_cutoff_norm_le_one d
  obtain ⟨B, hB, hregular⟩ :=
    relative_lowpass_strong_type (d := d) (p := p) hd hp φ hφzero
  obtain ⟨A, ε, hA, hε, hdyadic⟩ :=
    relative_dyadic_strong_type (d := d) (p := p) hd hp φ hφone hφzero hφnorm
  obtain ⟨D, hD, hfinite⟩ :=
    finite_relative_reassembly (d := d) (p := p) hd hp φ hφzero
      ⟨B, hB, hregular⟩ ⟨A, ε, hA, hε, hdyadic⟩
  change ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
    MemLp (normalizedSphericalMaximalReal d f) (ENNReal.ofReal p) volume ∧
    (∫ x : Euclidean d, (normalizedSphericalMaximalReal d f x) ^ p) ≤
      C * ∫ x : Euclidean d, ‖f x‖ ^ p
  exact relative_reassembly_limit (d := d) (p := p) hd hp φ hφone D hD hfinite

end


end LeanSpherical.HarmonicAnalysis
