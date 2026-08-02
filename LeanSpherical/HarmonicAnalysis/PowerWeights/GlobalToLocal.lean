/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.LocalBlocks
import LeanSpherical.HarmonicAnalysis.PowerWeights.Scaling
import LeanSpherical.HarmonicAnalysis.PowerWeights.TypeSet
import LeanSpherical.HarmonicAnalysis.PowerWeights.RestrictedSublinear
import LeanSpherical.HarmonicAnalysis.PowerWeights.FiniteUnions
import LeanSpherical.HarmonicAnalysis.PowerWeights.NearOrigin
import LeanSpherical.HarmonicAnalysis.PowerWeights.AnnularWeightLower
import LeanSpherical.HarmonicAnalysis.PowerWeights.LocalizedUpper
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Scale transfer for the global-to-local reduction

This is the dilation part of Lemma 2.1 in the power-weight paper.  A
normalized radius block is measured at unit scale, whereas its corresponding
physical block lives in `[R, 2 R]`.  The two weighted moments have exactly
the same Jacobian factor.  Consequently a local moment estimate transfers to
the physical block with no loss in its constant.

The remaining part of the global-to-local reduction is the genuinely
off-diagonal spatial-shell reassembly; it is kept separate from this exact
scale computation.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

/-! The buffered annulus used by the spatial reassembly is stable under the
positive dilation which moves a physical radius block back to unit scale. -/
private theorem smul_mem_euclideanAnnulus_iff
    {d : ℕ} {R : ℝ} (hR : 0 < R) (x : Euclidean d) :
    R • x ∈ euclideanAnnulus d (R / 4) (8 * R) ↔
      x ∈ euclideanAnnulus d (1 / 4 : ℝ) 8 := by
  simp only [euclideanAnnulus, mem_diff, Metric.mem_closedBall,
    Metric.mem_ball, dist_zero_right]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  constructor
  · rintro ⟨hupper, hinner⟩
    constructor
    · nlinarith [norm_nonneg x]
    · intro hx
      apply hinner
      nlinarith [norm_nonneg x]
  · rintro ⟨hupper, hinner⟩
    constructor
    · nlinarith [norm_nonneg x]
    · intro hx
      apply hinner
      nlinarith [norm_nonneg x]

private theorem dyadic_buffered_annulus_eq {d : ℕ} (k : ℤ) :
    euclideanAnnulus d ((2 : ℝ) ^ k / 4) (8 * (2 : ℝ) ^ k) =
      euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3)) := by
  congr 1
  · rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num [zpow_two]
  · rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring

/-- The weighted `p`-moment of a normalized radius block, after pulling the
input back by a positive dilation, is the usual `R⁻ᵈ R⁻ᵅ` multiple of the
moment of the corresponding physical block. -/
theorem integral_restrictedNormalizedSphericalMaximal_normalizedRadiusBlock_scale
    {d : ℕ} (E : Set ℝ) {R : ℝ} (hR : 0 < R)
    (f : Euclidean d → ℂ) (p α : ℝ) :
    (∫ x : Euclidean d,
      (restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
        (fun y => f (R • y)) x).toReal ^ p *
        (radialPowerWeight d α x).toReal) =
      (R ^ d)⁻¹ * R ^ (-α) *
        ∫ y : Euclidean d,
          (restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R)) f y).toReal ^ p *
            (radialPowerWeight d α y).toReal := by
  let F : Euclidean d → ℂ := fun y =>
    ((restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R)) f y).toReal : ℂ)
  have hpoint (x : Euclidean d) :
      restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
          (fun y => f (R • y)) x =
        restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R)) f (R • x) := by
    have h := restrictedNormalizedSphericalMaximal_normalizedRadiusBlock E hR f (R • x)
    simpa [smul_smul, hR.ne'] using h
  have hF (x : Euclidean d) :
      ‖F (R • x)‖ ^ p * (radialPowerWeight d α x).toReal =
        (restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
          (fun y => f (R • y)) x).toReal ^ p *
          (radialPowerWeight d α x).toReal := by
    rw [show F (R • x) =
      ((restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R)) f (R • x)).toReal : ℂ) by
        rfl]
    rw [← hpoint x]
    simp [abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    (∫ x : Euclidean d,
      (restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
        (fun y => f (R • y)) x).toReal ^ p *
        (radialPowerWeight d α x).toReal) =
      ∫ x : Euclidean d, ‖F (R • x)‖ ^ p *
        (radialPowerWeight d α x).toReal := by
        apply integral_congr_ae
        filter_upwards with x
        exact (hF x).symm
    _ = (R ^ d)⁻¹ * R ^ (-α) *
        ∫ y : Euclidean d, ‖F y‖ ^ p *
          (radialPowerWeight d α y).toReal :=
      integral_norm_rpow_mul_radialPowerWeight_toReal_comp_smul F p α hR
    _ = (R ^ d)⁻¹ * R ^ (-α) *
        ∫ y : Euclidean d,
          (restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R)) f y).toReal ^ p *
            (radialPowerWeight d α y).toReal := by
      congr 2
      funext y
      simp [F, abs_of_nonneg ENNReal.toReal_nonneg]

/-- The density in a power-weighted `p`-moment has the pointwise dilation
rule used by the change-of-variables argument. -/
theorem norm_rpow_mul_radialPowerWeight_toReal_comp_smul_pointwise
    {d : ℕ} (f : Euclidean d → ℂ) (p α : ℝ) {R : ℝ} (hR : 0 < R)
    (x : Euclidean d) :
    ‖f (R • x)‖ ^ p * (radialPowerWeight d α x).toReal =
      R ^ (-α) *
        (‖f (R • x)‖ ^ p * (radialPowerWeight d α (R • x)).toReal) := by
  have hR0 : 0 ≤ R := hR.le
  have hnorm : ‖R • x‖ = R * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR0]
  have hrewrite : ‖x‖ ^ α = R ^ (-α) * (R * ‖x‖) ^ α := by
    calc
      ‖x‖ ^ α = 1 * ‖x‖ ^ α := (one_mul _).symm
      _ = (R ^ (-α) * R ^ α) * ‖x‖ ^ α := by
        rw [← Real.rpow_add hR]
        norm_num
      _ = R ^ (-α) * (R * ‖x‖) ^ α := by
        rw [Real.mul_rpow hR0 (norm_nonneg x)]
        ring
  calc
    ‖f (R • x)‖ ^ p * (radialPowerWeight d α x).toReal =
        ‖f (R • x)‖ ^ p * ‖x‖ ^ α := by
          rw [radialPowerWeight_toReal]
    _ = ‖f (R • x)‖ ^ p * (R ^ (-α) * (R * ‖x‖) ^ α) := by
          rw [hrewrite]
    _ = R ^ (-α) * (‖f (R • x)‖ ^ p * (R * ‖x‖) ^ α) := by
          ring
    _ = R ^ (-α) *
        (‖f (R • x)‖ ^ p * (radialPowerWeight d α (R • x)).toReal) := by
          rw [radialPowerWeight_toReal, hnorm]

/-- Positive Euclidean dilations preserve weighted `Lᵖ` membership for
continuous functions.  This is the membership half of power-weight scale
invariance and is useful when a unit-scale estimate is applied to a
rescaled Schwartz input. -/
theorem memLp_comp_smul_powerWeightedVolume_of_aestronglyMeasurable
    {d : ℕ} (hd : 1 ≤ d) {p α R : ℝ} (hp : 0 < p) (hR : 0 < R)
    (f : Euclidean d → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) (powerWeightedVolume d α))
    (hfsmeas : AEStronglyMeasurable (fun x => f (R • x))
      (powerWeightedVolume d α)) :
    MemLp (fun x => f (R • x)) (ENNReal.ofReal p) (powerWeightedVolume d α) := by
  have hweight_top : ∀ᵐ x ∂(volume : Measure (Euclidean d)),
      radialPowerWeight d α x < ∞ := by
    filter_upwards [ae_ne_zero_volume_euclidean hd] with x hx
    exact (radialPowerWeight_ne_top_of_ne_zero α hx).lt_top
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hfpow : Integrable (fun x : Euclidean d => ‖f x‖ ^ p)
      (powerWeightedVolume d α) := by
    simpa only [ENNReal.toReal_ofReal hp.le] using
      hf.integrable_norm_rpow hp0 hptop
  have hmoment : Integrable (fun x : Euclidean d =>
      ‖f x‖ ^ p * (radialPowerWeight d α x).toReal) volume := by
    rw [powerWeightedVolume,
      integrable_withDensity_iff (measurable_radialPowerWeight d α) hweight_top] at hfpow
    exact hfpow
  have hmoment_comp : Integrable (fun x : Euclidean d =>
      (‖f (R • x)‖ ^ p * (radialPowerWeight d α (R • x)).toReal)) volume := by
    exact hmoment.comp_smul hR.ne'
  have hscaled_moment : Integrable (fun x : Euclidean d =>
      ‖f (R • x)‖ ^ p * (radialPowerWeight d α x).toReal) volume := by
    convert hmoment_comp.const_mul (R ^ (-α)) using 1
    funext x
    exact norm_rpow_mul_radialPowerWeight_toReal_comp_smul_pointwise f p α hR x
  have hscaled_pow : Integrable (fun x : Euclidean d => ‖f (R • x)‖ ^ p)
      (powerWeightedVolume d α) := by
    rw [powerWeightedVolume,
      integrable_withDensity_iff (measurable_radialPowerWeight d α) hweight_top]
    exact hscaled_moment
  apply (memLp_norm_rpow_iff (p := ENNReal.ofReal p) hfsmeas hp0 hptop).mp
  have hgpow : MemLp (fun x : Euclidean d => ‖f (R • x)‖ ^ p) 1
      (powerWeightedVolume d α) := by
    apply memLp_one_iff_integrable.mpr
    exact hscaled_pow
  convert hgpow using 1
  · ext x
    simp only [ENNReal.toReal_ofReal hp.le]
  · rw [ENNReal.div_self hp0 hptop]

/-- Continuous inputs satisfy the measurability hypothesis in the preceding
scale-invariance lemma automatically. -/
theorem memLp_comp_smul_powerWeightedVolume_of_continuous
    {d : ℕ} (hd : 1 ≤ d) {p α R : ℝ} (hp : 0 < p) (hR : 0 < R)
    (f : Euclidean d → ℂ) (hfcont : Continuous f)
    (hf : MemLp f (ENNReal.ofReal p) (powerWeightedVolume d α)) :
    MemLp (fun x => f (R • x)) (ENNReal.ofReal p) (powerWeightedVolume d α) := by
  apply memLp_comp_smul_powerWeightedVolume_of_aestronglyMeasurable hd hp hR f hf
  have hcont : Continuous (fun x : Euclidean d => f (R • x)) :=
    hfcont.comp ((continuous_const : Continuous fun _ : Euclidean d => R).smul continuous_id)
  exact hcont.measurable.aestronglyMeasurable

/-- Writing a weighted moment with respect to `powerWeightedVolume` is the
same as writing its density explicitly against Lebesgue measure. -/
theorem integral_norm_rpow_powerWeightedVolume_eq
    {d : ℕ} (hd : 1 ≤ d) (g : Euclidean d → ℂ) (p α : ℝ) :
    (∫ x : Euclidean d, ‖g x‖ ^ p ∂powerWeightedVolume d α) =
      ∫ x : Euclidean d, ‖g x‖ ^ p * (radialPowerWeight d α x).toReal := by
  have hweight_top : ∀ᵐ x ∂(volume : Measure (Euclidean d)),
      radialPowerWeight d α x < ∞ := by
    filter_upwards [ae_ne_zero_volume_euclidean hd] with x hx
    exact (radialPowerWeight_ne_top_of_ne_zero α hx).lt_top
  rw [powerWeightedVolume,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_radialPowerWeight d α) hweight_top]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- The `p`-moment with respect to the power-weighted measure has the same
exact dilation factor as its density form. -/
theorem integral_norm_rpow_powerWeightedVolume_comp_smul
    {d : ℕ} (hd : 1 ≤ d) (f : Euclidean d → ℂ) (p α : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x : Euclidean d, ‖f (R • x)‖ ^ p ∂powerWeightedVolume d α) =
      (R ^ d)⁻¹ * R ^ (-α) *
        ∫ y : Euclidean d, ‖f y‖ ^ p ∂powerWeightedVolume d α := by
  rw [integral_norm_rpow_powerWeightedVolume_eq hd (fun x => f (R • x)) p α,
    integral_norm_rpow_mul_radialPowerWeight_toReal_comp_smul f p α hR,
    ← integral_norm_rpow_powerWeightedVolume_eq hd f p α]

/-- Exact finite-exponent scale invariance of the weighted `Lᵖ` seminorm.
The membership assumptions keep the statement valid without imposing an
unnecessary global integrability condition on arbitrary functions. -/
theorem eLpNorm_comp_smul_powerWeightedVolume
    {d : ℕ} (hd : 1 ≤ d) {p α R : ℝ} (hp : 0 < p) (hR : 0 < R)
    (f : Euclidean d → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) (powerWeightedVolume d α))
    (hfs : MemLp (fun x => f (R • x)) (ENNReal.ofReal p)
      (powerWeightedVolume d α)) :
    eLpNorm (fun x => f (R • x)) (ENNReal.ofReal p) (powerWeightedVolume d α) =
      ENNReal.ofReal (((R ^ d)⁻¹ * R ^ (-α)) ^ p⁻¹) *
        eLpNorm f (ENNReal.ofReal p) (powerWeightedVolume d α) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have ha : 0 < (R ^ d)⁻¹ * R ^ (-α) := by positivity
  have hmoment := integral_norm_rpow_powerWeightedVolume_comp_smul hd f p α hR
  rw [hfs.eLpNorm_eq_integral_rpow_norm hp0 hptop,
    hf.eLpNorm_eq_integral_rpow_norm hp0 hptop]
  simp only [ENNReal.toReal_ofReal hp.le]
  rw [hmoment]
  rw [Real.mul_rpow ha.le (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _),
    ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]

/-- At finite values, viewing an `ENNReal`-valued function through its real
part (and then as a complex-valued function) does not change its `Lᵖ`
seminorm.  Restricted spherical maxima on Schwartz inputs satisfy the
finiteness hypothesis below. -/
theorem eLpNorm_ennreal_eq_eLpNorm_toReal_complex_of_forall_ne_top
    {X : Type*} [MeasurableSpace X] (F : X → ENNReal) (q : ENNReal)
    (μ : Measure X) (hF : ∀ x, F x ≠ ∞) :
    eLpNorm F q μ = eLpNorm (fun x => ((F x).toReal : ℂ)) q μ := by
  apply eLpNorm_congr_enorm_ae
  filter_upwards with x
  rw [enorm_eq_self, ← ofReal_norm]
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg] using (ENNReal.ofReal_toReal (hF x)).symm

/-- The finite `ENNReal`/complex conversion also preserves `MemLp` when the
original function is measurable. -/
theorem MemLp.ennreal_toReal_complex
    {X : Type*} [MeasurableSpace X] (F : X → ENNReal) {q : ENNReal}
    {μ : Measure X} (hFmeas : Measurable F) (hFtop : ∀ x, F x ≠ ∞)
    (hF : MemLp F q μ) :
    MemLp (fun x => ((F x).toReal : ℂ)) q μ := by
  apply hF.congr_enorm
  · exact (Complex.continuous_ofReal.measurable.comp hFmeas.ennreal_toReal).aestronglyMeasurable
  · filter_upwards with x
    rw [enorm_eq_self, ← ofReal_norm]
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using (ENNReal.ofReal_toReal (hFtop x)).symm

/-- Conversely, a finite measurable `ENNReal`-valued function is in `L^p`
whenever its real-valued complex representative is. -/
theorem MemLp.of_ennreal_toReal_complex
    {X : Type*} [MeasurableSpace X] (F : X → ENNReal) {q : ENNReal}
    {μ : Measure X} (hFmeas : Measurable F) (hFtop : ∀ x, F x ≠ ∞)
    (hF : MemLp (fun x => ((F x).toReal : ℂ)) q μ) :
    MemLp F q μ := by
  apply hF.congr_enorm
  · exact hFmeas.aestronglyMeasurable
  · filter_upwards with x
    rw [enorm_eq_self, ← ofReal_norm]
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using ENNReal.ofReal_toReal (hFtop x)

/- A fixed-constant normalized radius-block estimate transfers to the
corresponding physical radius block.  Keeping the constant explicit is useful
when summing the gains furnished by the spatial-shell argument. -/
theorem restrictedNormalizedSphericalMaximal_block_bound_of_normalized
    {d : ℕ} (hd : 1 ≤ d) {E : Set ℝ} {R p α C : ℝ} (hp : 0 < p) (hR : 0 < R)
    (hlocal : ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) (powerWeightedVolume d α) →
        MemLp (restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
          (f : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
        eLpNorm (restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
          (f : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
          ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
            (powerWeightedVolume d α)) :
    ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) (powerWeightedVolume d α) →
        MemLp (restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R))
          (f : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
        eLpNorm (restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R))
          (f : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
          ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
            (powerWeightedVolume d α) := by
  intro f hf
  let D : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
  let g : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D) f
  have hgfun : (g : Euclidean d → ℂ) = fun x => f (R • x) := by
    funext x
    change f (D x) = f (R • x)
    simp [D]
  have hgmem : MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume d α) := by
    rw [hgfun]
    exact memLp_comp_smul_powerWeightedVolume_of_continuous hd hp hR
      (f : Euclidean d → ℂ) f.continuous hf
  obtain ⟨hLmem₀, hLbound₀⟩ := hlocal g hgmem
  let L : Euclidean d → ENNReal :=
    restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
      (g : Euclidean d → ℂ)
  let P : Euclidean d → ENNReal :=
    restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R))
      (f : Euclidean d → ℂ)
  have hLmem : MemLp L (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    simpa only [L] using hLmem₀
  have hLbound : eLpNorm L (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
      ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α) := by
    simpa only [L] using hLbound₀
  have hpoint (x : Euclidean d) : L x = P (R • x) := by
    dsimp [L, P]
    rw [hgfun]
    have h := restrictedNormalizedSphericalMaximal_normalizedRadiusBlock E hR
      (f : Euclidean d → ℂ) (R • x)
    simpa [smul_smul, hR.ne'] using h
  have hd0 : 0 < d := by omega
  have hLtop (x : Euclidean d) : L x ≠ ∞ := by
    dsimp [L]
    exact restrictedNormalizedSphericalMaximal_ne_top_schwartz hd0
      (normalizedRadiusBlock E R) g x
  have hPtop (x : Euclidean d) : P x ≠ ∞ := by
    dsimp [P]
    exact restrictedNormalizedSphericalMaximal_ne_top_schwartz hd0
      (E ∩ Icc R (2 * R)) f x
  have hLmeas : Measurable L := by
    dsimp [L]
    exact measurable_restrictedNormalizedSphericalMaximal
      (normalizedRadiusBlock E R) (g : Euclidean d → ℂ) g.continuous
  have hPmeas : Measurable P := by
    dsimp [P]
    exact measurable_restrictedNormalizedSphericalMaximal
      (E ∩ Icc R (2 * R)) (f : Euclidean d → ℂ) f.continuous
  let Lc : Euclidean d → ℂ := fun x => ((L x).toReal : ℂ)
  let Pc : Euclidean d → ℂ := fun x => ((P x).toReal : ℂ)
  have hLc : MemLp Lc (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    dsimp [Lc]
    exact MemLp.ennreal_toReal_complex L hLmeas hLtop hLmem
  have hPcmeas : AEStronglyMeasurable Pc (powerWeightedVolume d α) := by
    dsimp [Pc]
    exact (Complex.continuous_ofReal.measurable.comp hPmeas.ennreal_toReal).aestronglyMeasurable
  have hPpoint (x : Euclidean d) : P x = L (R⁻¹ • x) := by
    calc
      P x = P (R • (R⁻¹ • x)) := by simp [smul_smul, hR.ne']
      _ = L (R⁻¹ • x) := (hpoint (R⁻¹ • x)).symm
  have hPcInv_eq : (fun x => Lc (R⁻¹ • x)) = Pc := by
    funext x
    exact congrArg (fun t : ENNReal => ((t.toReal : ℂ))) (hPpoint x).symm
  have hLcInvmeas : AEStronglyMeasurable (fun x => Lc (R⁻¹ • x))
      (powerWeightedVolume d α) := by
    rw [hPcInv_eq]
    exact hPcmeas
  have hLcInv : MemLp (fun x => Lc (R⁻¹ • x)) (ENNReal.ofReal p)
      (powerWeightedVolume d α) :=
    memLp_comp_smul_powerWeightedVolume_of_aestronglyMeasurable hd hp (inv_pos.mpr hR)
      Lc hLc hLcInvmeas
  have hPc : MemLp Pc (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    rw [← hPcInv_eq]
    exact hLcInv
  have hPmem : MemLp P (ENNReal.ofReal p) (powerWeightedVolume d α) :=
    MemLp.of_ennreal_toReal_complex P hPmeas hPtop hPc
  have hPcR_eq : (fun x => Pc (R • x)) = Lc := by
    funext x
    exact congrArg (fun t : ENNReal => ((t.toReal : ℂ))) (hpoint x).symm
  have hPcR : MemLp (fun x => Pc (R • x)) (ENNReal.ofReal p)
      (powerWeightedVolume d α) := by
    rw [hPcR_eq]
    exact hLc
  let s : ENNReal := ENNReal.ofReal (((R ^ d)⁻¹ * R ^ (-α)) ^ p⁻¹)
  have hscaleIn : eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume d α) = s * eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    simpa only [s, hgfun] using
      (eLpNorm_comp_smul_powerWeightedVolume hd hp hR (f : Euclidean d → ℂ) hf hgmem)
  have hscaleOut : eLpNorm Lc (ENNReal.ofReal p) (powerWeightedVolume d α) =
      s * eLpNorm Pc (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    simpa only [s, hPcR_eq] using
      (eLpNorm_comp_smul_powerWeightedVolume hd hp hR Pc hPc hPcR)
  have hLnorm : eLpNorm L (ENNReal.ofReal p) (powerWeightedVolume d α) =
      eLpNorm Lc (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    exact eLpNorm_ennreal_eq_eLpNorm_toReal_complex_of_forall_ne_top L
      (ENNReal.ofReal p) (powerWeightedVolume d α) hLtop
  have hPnorm : eLpNorm P (ENNReal.ofReal p) (powerWeightedVolume d α) =
      eLpNorm Pc (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    exact eLpNorm_ennreal_eq_eLpNorm_toReal_complex_of_forall_ne_top P
      (ENNReal.ofReal p) (powerWeightedVolume d α) hPtop
  refine ⟨hPmem, ?_⟩
  have hbase : 0 < (R ^ d)⁻¹ * R ^ (-α) := by positivity
  have hspos : 0 < ((R ^ d)⁻¹ * R ^ (-α)) ^ p⁻¹ :=
    Real.rpow_pos_of_pos hbase _
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact ENNReal.ofReal_ne_zero_iff.mpr hspos
  have hstop : s ≠ ∞ := by
    dsimp [s]
    exact ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right hs0 hstop).mp
  calc
    s * eLpNorm P (ENNReal.ofReal p) (powerWeightedVolume d α) =
        eLpNorm L (ENNReal.ofReal p) (powerWeightedVolume d α) := by
      rw [hLnorm, hPnorm]
      exact hscaleOut.symm
    _ ≤ ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α) := hLbound
    _ = ENNReal.ofReal C * (s * eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume d α)) := by rw [hscaleIn]
    _ = s * (ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume d α)) := by ac_rfl

/-- The scale transfer above, restricted to precisely the buffered annular
inputs which occur in the spatial-shell reassembly.  This is intentionally
kept close to the full scale-transfer proof: no assertion about a cutoff
operator having compact spatial support is used here. -/
private theorem restrictedNormalizedSphericalMaximal_block_bound_of_normalized_buffered
    {d : ℕ} (hd : 1 ≤ d) {E : Set ℝ} {R p α C : ℝ} (hp : 0 < p) (hR : 0 < R)
    (hlocal : ∀ g : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d, x ∉ euclideanAnnulus d (1 / 4 : ℝ) 8 → g x = 0) →
      MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p) (powerWeightedVolume d α) →
        MemLp (restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
          (g : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
        eLpNorm (restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
          (g : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
          ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p)
            (powerWeightedVolume d α))
    (f : SchwartzMap (Euclidean d) ℂ)
    (hf : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume d α))
    (hfsupport : ∀ x : Euclidean d,
      x ∉ euclideanAnnulus d (R / 4) (8 * R) → f x = 0) :
    MemLp (restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R))
      (f : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
    eLpNorm (restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R))
      (f : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
      ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α) := by
  let D : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
  let g : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D) f
  have hgfun : (g : Euclidean d → ℂ) = fun x => f (R • x) := by
    funext x
    change f (D x) = f (R • x)
    simp [D]
  have hgmem : MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume d α) := by
    rw [hgfun]
    exact memLp_comp_smul_powerWeightedVolume_of_continuous hd hp hR
      (f : Euclidean d → ℂ) f.continuous hf
  have hgsupport : ∀ x : Euclidean d,
      x ∉ euclideanAnnulus d (1 / 4 : ℝ) 8 → g x = 0 := by
    intro x hx
    rw [hgfun]
    apply hfsupport (R • x)
    intro hxR
    exact hx ((smul_mem_euclideanAnnulus_iff hR x).mp hxR)
  obtain ⟨hLmem₀, hLbound₀⟩ := hlocal g hgsupport hgmem
  let L : Euclidean d → ENNReal :=
    restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
      (g : Euclidean d → ℂ)
  let P : Euclidean d → ENNReal :=
    restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R))
      (f : Euclidean d → ℂ)
  have hLmem : MemLp L (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    simpa only [L] using hLmem₀
  have hLbound : eLpNorm L (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
      ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α) := by
    simpa only [L] using hLbound₀
  have hpoint (x : Euclidean d) : L x = P (R • x) := by
    dsimp [L, P]
    rw [hgfun]
    have h := restrictedNormalizedSphericalMaximal_normalizedRadiusBlock E hR
      (f : Euclidean d → ℂ) (R • x)
    simpa [smul_smul, hR.ne'] using h
  have hd0 : 0 < d := by omega
  have hLtop (x : Euclidean d) : L x ≠ ∞ := by
    dsimp [L]
    exact restrictedNormalizedSphericalMaximal_ne_top_schwartz hd0
      (normalizedRadiusBlock E R) g x
  have hPtop (x : Euclidean d) : P x ≠ ∞ := by
    dsimp [P]
    exact restrictedNormalizedSphericalMaximal_ne_top_schwartz hd0
      (E ∩ Icc R (2 * R)) f x
  have hLmeas : Measurable L := by
    dsimp [L]
    exact measurable_restrictedNormalizedSphericalMaximal
      (normalizedRadiusBlock E R) (g : Euclidean d → ℂ) g.continuous
  have hPmeas : Measurable P := by
    dsimp [P]
    exact measurable_restrictedNormalizedSphericalMaximal
      (E ∩ Icc R (2 * R)) (f : Euclidean d → ℂ) f.continuous
  let Lc : Euclidean d → ℂ := fun x => ((L x).toReal : ℂ)
  let Pc : Euclidean d → ℂ := fun x => ((P x).toReal : ℂ)
  have hLc : MemLp Lc (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    dsimp [Lc]
    exact MemLp.ennreal_toReal_complex L hLmeas hLtop hLmem
  have hPcmeas : AEStronglyMeasurable Pc (powerWeightedVolume d α) := by
    dsimp [Pc]
    exact (Complex.continuous_ofReal.measurable.comp hPmeas.ennreal_toReal).aestronglyMeasurable
  have hPpoint (x : Euclidean d) : P x = L (R⁻¹ • x) := by
    calc
      P x = P (R • (R⁻¹ • x)) := by simp [smul_smul, hR.ne']
      _ = L (R⁻¹ • x) := (hpoint (R⁻¹ • x)).symm
  have hPcInv_eq : (fun x => Lc (R⁻¹ • x)) = Pc := by
    funext x
    exact congrArg (fun t : ENNReal => ((t.toReal : ℂ))) (hPpoint x).symm
  have hLcInvmeas : AEStronglyMeasurable (fun x => Lc (R⁻¹ • x))
      (powerWeightedVolume d α) := by
    rw [hPcInv_eq]
    exact hPcmeas
  have hLcInv : MemLp (fun x => Lc (R⁻¹ • x)) (ENNReal.ofReal p)
      (powerWeightedVolume d α) :=
    memLp_comp_smul_powerWeightedVolume_of_aestronglyMeasurable hd hp (inv_pos.mpr hR)
      Lc hLc hLcInvmeas
  have hPc : MemLp Pc (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    rw [← hPcInv_eq]
    exact hLcInv
  have hPmem : MemLp P (ENNReal.ofReal p) (powerWeightedVolume d α) :=
    MemLp.of_ennreal_toReal_complex P hPmeas hPtop hPc
  have hPcR_eq : (fun x => Pc (R • x)) = Lc := by
    funext x
    exact congrArg (fun t : ENNReal => ((t.toReal : ℂ))) (hpoint x).symm
  have hPcR : MemLp (fun x => Pc (R • x)) (ENNReal.ofReal p)
      (powerWeightedVolume d α) := by
    rw [hPcR_eq]
    exact hLc
  let s : ENNReal := ENNReal.ofReal (((R ^ d)⁻¹ * R ^ (-α)) ^ p⁻¹)
  have hscaleIn : eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume d α) = s * eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    simpa only [s, hgfun] using
      (eLpNorm_comp_smul_powerWeightedVolume hd hp hR (f : Euclidean d → ℂ) hf hgmem)
  have hscaleOut : eLpNorm Lc (ENNReal.ofReal p) (powerWeightedVolume d α) =
      s * eLpNorm Pc (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    simpa only [s, hPcR_eq] using
      (eLpNorm_comp_smul_powerWeightedVolume hd hp hR Pc hPc hPcR)
  have hLnorm : eLpNorm L (ENNReal.ofReal p) (powerWeightedVolume d α) =
      eLpNorm Lc (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    exact eLpNorm_ennreal_eq_eLpNorm_toReal_complex_of_forall_ne_top L
      (ENNReal.ofReal p) (powerWeightedVolume d α) hLtop
  have hPnorm : eLpNorm P (ENNReal.ofReal p) (powerWeightedVolume d α) =
      eLpNorm Pc (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    exact eLpNorm_ennreal_eq_eLpNorm_toReal_complex_of_forall_ne_top P
      (ENNReal.ofReal p) (powerWeightedVolume d α) hPtop
  refine ⟨hPmem, ?_⟩
  have hbase : 0 < (R ^ d)⁻¹ * R ^ (-α) := by positivity
  have hspos : 0 < ((R ^ d)⁻¹ * R ^ (-α)) ^ p⁻¹ :=
    Real.rpow_pos_of_pos hbase _
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact ENNReal.ofReal_ne_zero_iff.mpr hspos
  have hstop : s ≠ ∞ := by
    dsimp [s]
    exact ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right hs0 hstop).mp
  calc
    s * eLpNorm P (ENNReal.ofReal p) (powerWeightedVolume d α) =
        eLpNorm L (ENNReal.ofReal p) (powerWeightedVolume d α) := by
      rw [hLnorm, hPnorm]
      exact hscaleOut.symm
    _ ≤ ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α) := hLbound
    _ = ENNReal.ofReal C * (s * eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume d α)) := by rw [hscaleIn]
    _ = s * (ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume d α)) := by ac_rfl

/-- A weighted strong-type estimate for a normalized radius block transfers
to the corresponding physical radius block, with exactly the same constant.
This is the scale-invariant part of the global-to-local reduction. -/
theorem HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType.block_of_normalized
    {d : ℕ} (hd : 1 ≤ d) {E : Set ℝ} {R p α : ℝ} (hp : 0 < p) (hR : 0 < R)
    (hlocal : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d
      (normalizedRadiusBlock E R) p α) :
    HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d
      (E ∩ Icc R (2 * R)) p α := by
  rcases hlocal with ⟨C, hC, hlocal⟩
  exact ⟨C, hC,
    restrictedNormalizedSphericalMaximal_block_bound_of_normalized hd hp hR hlocal⟩

/-- Reassemble finitely many physical multiplicative radius blocks after
transporting their normalized estimates.  This is the finite version of the
radius-side part of the global-to-local reduction. -/
theorem hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_iUnion_finset_blocks_of_normalized
    {ι : Type*} (s : Finset ι) (R : ι → ℝ) {d : ℕ} {E : Set ℝ} {p α : ℝ}
    (hd : 1 ≤ d) (hp : 1 ≤ p) (hR : ∀ i ∈ s, 0 < R i)
    (hlocal : ∀ i ∈ s, HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d
      (normalizedRadiusBlock E (R i)) p α) :
    HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d
      (⋃ i ∈ (s : Set ι), E ∩ Icc (R i) (2 * R i)) p α := by
  apply hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_iUnion_finset s
    (fun i => E ∩ Icc (R i) (2 * R i)) hp
  intro i hi
  exact HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType.block_of_normalized hd
    (lt_of_lt_of_le zero_lt_one hp) (hR i hi) (hlocal i hi)

/-- A countable dyadic reassembly principle.  It is deliberately stated with
the actual summable block norms: the off-diagonal spatial-shell part of the
global-to-local argument is precisely what supplies this summability in an
application. -/
theorem restrictedNormalizedSphericalMaximal_memLp_and_eLpNorm_le_tsum_dyadic_blocks
    {d : ℕ} (hd0 : 0 < d) (E : Set ℝ) {p α : ℝ} (hp : 1 ≤ p)
    (f : SchwartzMap (Euclidean d) ℂ)
    (hblock : ∀ k : ℤ, MemLp
      (restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (f : Euclidean d → ℂ))
      (ENNReal.ofReal p) (powerWeightedVolume d α))
    (hsum : Summable fun k : ℤ =>
      (eLpNorm
        (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (f : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal) :
    MemLp (restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ))
      (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
      eLpNorm (restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
        ENNReal.ofReal (∑' k : ℤ,
          (eLpNorm
            (restrictedNormalizedSphericalMaximal d
              (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
              (f : Euclidean d → ℂ))
            (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal) := by
  let q : ENNReal := ENNReal.ofReal p
  let μ : Measure (Euclidean d) := powerWeightedVolume d α
  let B : ℤ → Euclidean d → ENNReal := fun k =>
    restrictedNormalizedSphericalMaximal d
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
      (f : Euclidean d → ℂ)
  have hBmem (k : ℤ) : MemLp (B k) q μ := by
    simpa only [B, q, μ] using hblock k
  have hBtop (k : ℤ) (x : Euclidean d) : B k x ≠ ∞ := by
    dsimp [B]
    exact restrictedNormalizedSphericalMaximal_ne_top_schwartz hd0
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) f x
  have hBmeas (k : ℤ) : Measurable (B k) := by
    dsimp [B]
    exact measurable_restrictedNormalizedSphericalMaximal
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
      (f : Euclidean d → ℂ) f.continuous
  let b : ℤ → Euclidean d → ℂ := fun k x => ((B k x).toReal : ℂ)
  have hbmem (k : ℤ) : MemLp (b k) q μ := by
    dsimp [b]
    exact MemLp.ennreal_toReal_complex (B k) (hBmeas k) (hBtop k) (hBmem k)
  letI : Fact (1 ≤ q) := ⟨by
    dsimp [q]
    simpa using ENNReal.ofReal_le_ofReal hp⟩
  let G : ℤ → Lp ℂ q μ := fun k => MemLp.toLp (b k) (hbmem k)
  have hGnorm (k : ℤ) : ‖G k‖ = (eLpNorm (B k) q μ).toReal := by
    calc
      ‖G k‖ = (eLpNorm (b k) q μ).toReal := by
        dsimp [G]
        rw [Lp.norm_toLp]
      _ = (eLpNorm (B k) q μ).toReal := by
        change (eLpNorm (fun x => ((B k x).toReal : ℂ)) q μ).toReal = _
        exact congrArg ENNReal.toReal
          (eLpNorm_ennreal_eq_eLpNorm_toReal_complex_of_forall_ne_top
            (B k) q μ (hBtop k)).symm
  have hsum' : Summable fun k : ℤ => (eLpNorm (B k) q μ).toReal := by
    simpa only [B, q, μ] using hsum
  have hsumG : Summable fun k : ℤ => ‖G k‖ :=
    hsum'.congr fun k => (hGnorm k).symm
  have hsumGnn : Summable fun k : ℤ => ‖G k‖₊ := by
    apply NNReal.summable_coe.mp
    convert hsumG using 1
    funext k
    exact coe_nnnorm (G k)
  have hGsum_ne_top : (∑' k : ℤ, ‖G k‖ₑ) ≠ ∞ := by
    rw [show (fun k : ℤ => ‖G k‖ₑ) = fun k => (↑‖G k‖₊ : ENNReal) by
      funext k
      exact enorm_eq_nnnorm (G k)]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hsumGnn
  let H : Lp ℂ q μ := ∑' k : ℤ, G k
  have hHmem : MemLp (H : Euclidean d → ℂ) q μ := Lp.memLp H
  have hGsum : ∀ᵐ x ∂μ, HasSum (fun k : ℤ => (G k : Euclidean d → ℂ) x) (H x) := by
    simpa only [H] using Lp.hasSum_coeFn_tsum hGsum_ne_top
  have hG_eq_b (k : ℤ) : (G k : Euclidean d → ℂ) =ᵐ[μ] b k := by
    dsimp [G]
    exact (hbmem k).coeFn_toLp
  have hG_eq_b_all : ∀ᵐ x ∂μ, ∀ k : ℤ, (G k : Euclidean d → ℂ) x = b k x :=
    ae_all_iff.mpr hG_eq_b
  have hMmeas : AEStronglyMeasurable
      (restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ)) μ := by
    dsimp [μ]
    exact (measurable_restrictedNormalizedSphericalMaximal E
      (f : Euclidean d → ℂ) f.continuous).aestronglyMeasurable
  have hMleH : ∀ᵐ x ∂μ,
      restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ) x ≤ ‖H x‖ₑ := by
    filter_upwards [hGsum, hG_eq_b_all] with x hxsum hxG
    have hbsum : HasSum (fun k : ℤ => b k x) (H x) :=
      HasSum.congr_fun hxsum (fun k => (hxG k).symm)
    have hrealSum : HasSum (fun k : ℤ => (B k x).toReal) (H x).re := by
      simpa only [b, Complex.ofReal_re] using Complex.hasSum_re hbsum
    have hblock_le (k : ℤ) : B k x ≤ ‖H x‖ₑ := by
      rw [← ENNReal.ofReal_toReal (hBtop k x), ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      calc
        (B k x).toReal ≤ ∑' j : ℤ, (B j x).toReal :=
          hrealSum.summable.le_tsum k (fun j _ => ENNReal.toReal_nonneg)
        _ = (H x).re := hrealSum.tsum_eq
        _ ≤ ‖H x‖ := Complex.re_le_norm _
    rw [restrictedNormalizedSphericalMaximal_eq_iSup_dyadic_blocks]
    exact iSup_le hblock_le
  have hMmem : MemLp (restrictedNormalizedSphericalMaximal d E
      (f : Euclidean d → ℂ)) q μ :=
    hHmem.enorm.mono'_enorm hMmeas hMleH
  constructor
  · simpa only [q, μ] using hMmem
  · have hnorm : ‖H‖ ≤ ∑' k : ℤ, ‖G k‖ := norm_tsum_le_tsum_norm hsumG
    have hsum_eq : (∑' k : ℤ, ‖G k‖) =
        ∑' k : ℤ, (eLpNorm (B k) q μ).toReal :=
      tsum_congr hGnorm
    calc
      eLpNorm (restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ)) q μ ≤
          eLpNorm (H : Euclidean d → ℂ) q μ :=
        eLpNorm_mono_enorm_ae hMleH
      _ = ENNReal.ofReal ‖H‖ := by
        rw [Lp.norm_def H]
        exact (ENNReal.ofReal_toReal hHmem.eLpNorm_ne_top).symm
      _ ≤ ENNReal.ofReal (∑' k : ℤ, ‖G k‖) := ENNReal.ofReal_le_ofReal hnorm
      _ = ENNReal.ofReal (∑' k : ℤ, (eLpNorm (B k) q μ).toReal) := by
        rw [hsum_eq]
      _ = ENNReal.ofReal (∑' k : ℤ,
          (eLpNorm
            (restrictedNormalizedSphericalMaximal d
              (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
              (f : Euclidean d → ℂ))
            (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal) := by
        simp only [B, q, μ]

/-- The `p`-moment of a countable supremum is at most the sum of the
individual `p`-moments.  This is the analytic reassembly estimate used by
the spatial-shell proof; unlike the earlier `Lp`-series lemma, it retains the
essential `ℓᵖ` summability. -/
theorem lintegral_iSup_rpow_le_tsum_lintegral_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (B : ℤ → X → ENNReal)
    (p : ℝ) (hp : 0 < p) (hB : ∀ k : ℤ, AEMeasurable (B k) μ) :
    (∫⁻ x, (⨆ k : ℤ, B k x) ^ p ∂μ) ≤
      ∑' k : ℤ, ∫⁻ x, (B k x) ^ p ∂μ := by
  have hpowmeas (k : ℤ) : AEMeasurable (fun x => (B k x) ^ p) μ := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hB k)
  have hpoint (x : X) : (⨆ k : ℤ, B k x) ^ p ≤ ∑' k : ℤ, (B k x) ^ p := by
    have hroot : (⨆ k : ℤ, B k x) ≤ (∑' k : ℤ, (B k x) ^ p) ^ (1 / p) := by
      apply iSup_le
      intro k
      calc
        B k x = ((B k x) ^ p) ^ (1 / p) := by
          symm
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]
        _ ≤ (∑' l : ℤ, (B l x) ^ p) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (ENNReal.le_tsum k) (one_div_nonneg.mpr hp.le)
    calc
      (⨆ k : ℤ, B k x) ^ p ≤ ((∑' k : ℤ, (B k x) ^ p) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow hroot hp.le
      _ = ∑' k : ℤ, (B k x) ^ p := by
        rw [← ENNReal.rpow_mul]
        field_simp
        simp
  calc
    (∫⁻ x, (⨆ k : ℤ, B k x) ^ p ∂μ) ≤
        ∫⁻ x, ∑' k : ℤ, (B k x) ^ p ∂μ := lintegral_mono hpoint
    _ = ∑' k : ℤ, ∫⁻ x, (B k x) ^ p ∂μ := lintegral_tsum hpowmeas

/-- The `Lᵖ` seminorm of an `ENNReal`-valued function in the finite positive
range is its usual `p`-moment raised to `1 / p`. -/
theorem eLpNorm_ennreal_eq_lintegral_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (B : X → ENNReal)
    (p : ℝ) (hp : 0 < p) :
    eLpNorm B (ENNReal.ofReal p) μ =
      (∫⁻ x, (B x) ^ p ∂μ) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le, enorm_eq_self]

/-- Raising a finite-exponent strong-type estimate to the `p`-th power gives
the corresponding nonnegative `p`-moment estimate.  Keeping this elementary
conversion in ENNReal form avoids choosing real representatives of maximal
functions during the spatial-shell argument. -/
theorem lintegral_enorm_rpow_le_of_eLpNorm_le
    {X E F : Type*} [MeasurableSpace X] [ENorm E] [ENorm F]
    (μ : Measure X) {p : ℝ} (hp : 0 < p) (A : ENNReal)
    (u : X → E) (v : X → F)
    (h : eLpNorm u (ENNReal.ofReal p) μ ≤ A * eLpNorm v (ENNReal.ofReal p) μ) :
    (∫⁻ x, ‖u x‖ₑ ^ p ∂μ) ≤
      A ^ p * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hu :
      (∫⁻ x, ‖u x‖ₑ ^ p ∂μ) =
        (eLpNorm u (ENNReal.ofReal p) μ) ^ p := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
    simp only [ENNReal.toReal_ofReal hp.le]
    rw [← ENNReal.rpow_mul]
    field_simp
    simp
  have hv :
      (A * eLpNorm v (ENNReal.ofReal p) μ) ^ p =
        A ^ p * (∫⁻ x, ‖v x‖ₑ ^ p ∂μ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
    simp only [ENNReal.toReal_ofReal hp.le]
    rw [← ENNReal.rpow_mul]
    field_simp
    simp
  rw [hu, ← hv]
  exact ENNReal.rpow_le_rpow h hp.le

/-- A summable family of normalized-block estimates gives a global weighted
strong-type estimate.  In the genuine global-to-local argument the displayed
coefficients are the summable gains supplied by the spatial-shell analysis. -/
theorem hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_summable_normalized_dyadic_bounds
    {d : ℕ} (hd : 1 ≤ d) (E : Set ℝ) {p α : ℝ} (hp : 1 ≤ p)
    (C : ℤ → ℝ) (hCpos : ∀ k, 0 < C k) (hCsum : Summable C)
    (hlocal : ∀ k : ℤ, ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) (powerWeightedVolume d α) →
        MemLp (restrictedNormalizedSphericalMaximal d
          (normalizedRadiusBlock E ((2 : ℝ) ^ k)) (f : Euclidean d → ℂ))
          (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
        eLpNorm (restrictedNormalizedSphericalMaximal d
          (normalizedRadiusBlock E ((2 : ℝ) ^ k)) (f : Euclidean d → ℂ))
          (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
          ENNReal.ofReal (C k) * eLpNorm (f : Euclidean d → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume d α)) :
    HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p α := by
  let S : ℝ := ∑' k : ℤ, C k
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun k => (hCpos k).le
  refine ⟨1 + S, add_pos_of_pos_of_nonneg zero_lt_one hSnonneg, ?_⟩
  intro f hf
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hd0 : 0 < d := by omega
  have hphysical (k : ℤ) : ∀ g : SchwartzMap (Euclidean d) ℂ,
      MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p) (powerWeightedVolume d α) →
        MemLp (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (g : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
        eLpNorm (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (g : Euclidean d → ℂ)) (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
          ENNReal.ofReal (C k) * eLpNorm (g : Euclidean d → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    have hR : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hshift : 2 * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      ring
    have h := restrictedNormalizedSphericalMaximal_block_bound_of_normalized
      hd hp0 hR (C := C k) (hlocal k)
    rw [hshift] at h
    exact h
  have hblock (k : ℤ) : MemLp
      (restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (f : Euclidean d → ℂ))
      (ENNReal.ofReal p) (powerWeightedVolume d α) :=
    (hphysical k f hf).1
  have hblockbound (k : ℤ) :
      eLpNorm (restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (f : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
        ENNReal.ofReal (C k) * eLpNorm (f : Euclidean d → ℂ)
          (ENNReal.ofReal p) (powerWeightedVolume d α) :=
    (hphysical k f hf).2
  have hblock_real_bound (k : ℤ) :
      (eLpNorm (restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (f : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal ≤
        C k * (eLpNorm (f : Euclidean d → ℂ)
          (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal := by
    have hright_top : ENNReal.ofReal (C k) *
        eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
          (powerWeightedVolume d α) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
    have hreal := (ENNReal.toReal_le_toReal (hblock k).eLpNorm_ne_top hright_top).mpr
      (hblockbound k)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hCpos k).le] using hreal
  have hCsum_mul : Summable fun k : ℤ => C k *
      (eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α)).toReal :=
    hCsum.mul_right _
  have hblock_sum : Summable fun k : ℤ =>
      (eLpNorm (restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (f : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal :=
    Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg)
      hblock_real_bound hCsum_mul
  obtain ⟨hMmem, hMbound⟩ :=
    restrictedNormalizedSphericalMaximal_memLp_and_eLpNorm_le_tsum_dyadic_blocks
      hd0 E hp f hblock hblock_sum
  refine ⟨hMmem, ?_⟩
  have hsum_bound : (∑' k : ℤ,
      (eLpNorm (restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (f : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal) ≤
      S * (eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal := by
    calc
      (∑' k : ℤ,
          (eLpNorm (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (f : Euclidean d → ℂ))
            (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal) ≤
          ∑' k : ℤ, C k * (eLpNorm (f : Euclidean d → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal :=
        Summable.tsum_le_tsum hblock_real_bound hblock_sum hCsum_mul
      _ = S * (eLpNorm (f : Euclidean d → ℂ)
          (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal := by
        dsimp [S]
        rw [tsum_mul_right]
  calc
    eLpNorm (restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
        ENNReal.ofReal (∑' k : ℤ,
          (eLpNorm (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (f : Euclidean d → ℂ))
            (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal) := hMbound
    _ ≤ ENNReal.ofReal (S * (eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume d α)).toReal) :=
      ENNReal.ofReal_le_ofReal hsum_bound
    _ = ENNReal.ofReal S * eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume d α) := by
      rw [ENNReal.ofReal_mul hSnonneg, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
    _ ≤ ENNReal.ofReal (1 + S) * eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume d α) := by
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _

/-- A unit-scale weighted moment bound transfers exactly to its block of
physical radii.  This is the scale-uniform local estimate used before the
spatial-shell reassembly in the global-to-local argument. -/
theorem restrictedNormalizedSphericalMaximal_block_moment_bound_of_normalized
    {d : ℕ} (E : Set ℝ) {R p α C : ℝ} (hR : 0 < R)
    (hlocal : ∀ g : Euclidean d → ℂ,
      (∫ x : Euclidean d,
        (restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R) g x).toReal ^ p *
          (radialPowerWeight d α x).toReal) ≤
        C * ∫ x : Euclidean d, ‖g x‖ ^ p * (radialPowerWeight d α x).toReal)
    (f : Euclidean d → ℂ) :
    (∫ x : Euclidean d,
      (restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R)) f x).toReal ^ p *
        (radialPowerWeight d α x).toReal) ≤
      C * ∫ x : Euclidean d, ‖f x‖ ^ p * (radialPowerWeight d α x).toReal := by
  let a : ℝ := (R ^ d)⁻¹ * R ^ (-α)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have houtput :=
    integral_restrictedNormalizedSphericalMaximal_normalizedRadiusBlock_scale E hR f p α
  have hinput := integral_norm_rpow_mul_radialPowerWeight_toReal_comp_smul f p α hR
  apply le_of_mul_le_mul_left ?_ ha
  calc
    a * (∫ x : Euclidean d,
      (restrictedNormalizedSphericalMaximal d (E ∩ Icc R (2 * R)) f x).toReal ^ p *
        (radialPowerWeight d α x).toReal) =
      ∫ x : Euclidean d,
        (restrictedNormalizedSphericalMaximal d (normalizedRadiusBlock E R)
          (fun y => f (R • y)) x).toReal ^ p *
          (radialPowerWeight d α x).toReal := houtput.symm
    _ ≤ C * ∫ x : Euclidean d, ‖f (R • x)‖ ^ p *
          (radialPowerWeight d α x).toReal :=
      hlocal (fun y => f (R • y))
    _ = a * (C * ∫ x : Euclidean d, ‖f x‖ ^ p *
          (radialPowerWeight d α x).toReal) := by
      rw [hinput]
      dsimp [a]
      ring

/-- A spherical average vanishes when the input vanishes at every point of
the sampling sphere. -/
theorem sphericalAverage_eq_zero_of_forall
    {d : ℕ} (f : Euclidean d → ℂ) (r : ℝ) (x : Euclidean d)
    (h : ∀ ω : sphere (0 : Euclidean d) 1,
      f (x + r • (ω : Euclidean d)) = 0) :
    sphericalAverage d f r x = 0 := by
  unfold sphericalAverage
  apply integral_eq_zero_of_ae
  filter_upwards with ω
  exact h ω

/-- The normalized spherical average has the same elementary support
vanishing property. -/
theorem normalizedSphericalAverage_eq_zero_of_forall
    {d : ℕ} (f : Euclidean d → ℂ) (r : ℝ) (x : Euclidean d)
    (h : ∀ ω : sphere (0 : Euclidean d) 1,
      f (x + r • (ω : Euclidean d)) = 0) :
    normalizedSphericalAverage d f r x = 0 := by
  unfold normalizedSphericalAverage
  rw [sphericalAverage_eq_zero_of_forall f r x h]
  simp

/-- Equality of inputs on a sampling sphere gives equality of their spherical
averages. -/
theorem sphericalAverage_eq_of_forall
    {d : ℕ} (f g : Euclidean d → ℂ) (r : ℝ) (x : Euclidean d)
    (h : ∀ ω : sphere (0 : Euclidean d) 1,
      f (x + r • (ω : Euclidean d)) = g (x + r • (ω : Euclidean d))) :
    sphericalAverage d f r x = sphericalAverage d g r x := by
  unfold sphericalAverage
  apply integral_congr_ae
  filter_upwards with ω
  exact h ω

/-- Equality of inputs on a sampling sphere gives equality of their
normalized spherical averages. -/
theorem normalizedSphericalAverage_eq_of_forall
    {d : ℕ} (f g : Euclidean d → ℂ) (r : ℝ) (x : Euclidean d)
    (h : ∀ ω : sphere (0 : Euclidean d) 1,
      f (x + r • (ω : Euclidean d)) = g (x + r • (ω : Euclidean d))) :
    normalizedSphericalAverage d f r x = normalizedSphericalAverage d g r x := by
  unfold normalizedSphericalAverage
  rw [sphericalAverage_eq_of_forall f g r x h]

/-- A maximal function using radii bounded by `T` only sees the input inside
the radius-`T` ball around its evaluation point. -/
theorem restrictedNormalizedSphericalMaximal_eq_of_eq_on_ball
    {d : ℕ} (E : Set ℝ) (f g : Euclidean d → ℂ) (x : Euclidean d) {T : ℝ}
    (hE : ∀ r : ℝ, r ∈ E ∩ Ioi (0 : ℝ) → r ≤ T)
    (hfg : ∀ y : Euclidean d, ‖y - x‖ ≤ T → f y = g y) :
    restrictedNormalizedSphericalMaximal d E f x =
      restrictedNormalizedSphericalMaximal d E g x := by
  unfold restrictedNormalizedSphericalMaximal
  congr with r
  rw [normalizedSphericalAverage_eq_of_forall f g r.1 x]
  intro ω
  apply hfg
  have hω : ‖(ω : Euclidean d)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  have hrnorm : ‖r.1 • (ω : Euclidean d)‖ = r.1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.2.2, hω, mul_one]
  calc
    ‖x + r.1 • (ω : Euclidean d) - x‖ = ‖r.1 • (ω : Euclidean d)‖ := by
      congr 1
      abel
    _ = r.1 := hrnorm
    _ ≤ T := hE r.1 r.2

/-- A restricted maximal function vanishes if every admissible sampling
sphere lies in a zero set of the input. -/
theorem restrictedNormalizedSphericalMaximal_eq_zero_of_forall
    {d : ℕ} (E : Set ℝ) (f : Euclidean d → ℂ) (x : Euclidean d)
    (h : ∀ r : ℝ, r ∈ E ∩ Ioi (0 : ℝ) →
      ∀ ω : sphere (0 : Euclidean d) 1,
        f (x + r • (ω : Euclidean d)) = 0) :
    restrictedNormalizedSphericalMaximal d E f x = 0 := by
  apply le_antisymm
  · unfold restrictedNormalizedSphericalMaximal
    apply iSup_le
    intro r
    rw [normalizedSphericalAverage_eq_zero_of_forall f r.1 x (h r.1 r.2)]
    simp
  · exact bot_le

/-- If the input is supported in the closed ball of radius `A` and all
available radii are at most `T`, then the restricted maximal function
vanishes outside the ball of radius `A + T`. -/
theorem restrictedNormalizedSphericalMaximal_eq_zero_outside_closedBall
    {d : ℕ} (E : Set ℝ) (f : Euclidean d → ℂ) {A T : ℝ}
    (hE : ∀ r : ℝ, r ∈ E ∩ Ioi (0 : ℝ) → r ≤ T)
    (hf : ∀ y : Euclidean d, A < ‖y‖ → f y = 0)
    {x : Euclidean d} (hx : A + T < ‖x‖) :
    restrictedNormalizedSphericalMaximal d E f x = 0 := by
  apply restrictedNormalizedSphericalMaximal_eq_zero_of_forall E f x
  intro r hr ω
  have hrpos : 0 < r := hr.2
  have hω : ‖(ω : Euclidean d)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  have hrnorm : ‖r • (ω : Euclidean d)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hω, mul_one]
  have htri : ‖x‖ ≤ ‖x + r • (ω : Euclidean d)‖ + ‖r • (ω : Euclidean d)‖ := by
    calc
      ‖x‖ = ‖(x + r • (ω : Euclidean d)) - r • (ω : Euclidean d)‖ := by
        congr 1
        abel
      _ ≤ ‖x + r • (ω : Euclidean d)‖ + ‖r • (ω : Euclidean d)‖ := norm_sub_le _ _
  apply hf
  rw [hrnorm] at htri
  linarith [hE r hr]

/-- If the input vanishes on the open ball of radius `A` and all available
radii are at most `T`, then the restricted maximal function vanishes on the
ball of radius `A - T` (expressed without subtraction). -/
theorem restrictedNormalizedSphericalMaximal_eq_zero_inside_ball
    {d : ℕ} (E : Set ℝ) (f : Euclidean d → ℂ) {A T : ℝ}
    (hE : ∀ r : ℝ, r ∈ E ∩ Ioi (0 : ℝ) → r ≤ T)
    (hf : ∀ y : Euclidean d, ‖y‖ < A → f y = 0)
    {x : Euclidean d} (hx : ‖x‖ + T < A) :
    restrictedNormalizedSphericalMaximal d E f x = 0 := by
  apply restrictedNormalizedSphericalMaximal_eq_zero_of_forall E f x
  intro r hr ω
  have hrpos : 0 < r := hr.2
  have hω : ‖(ω : Euclidean d)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  have hrnorm : ‖r • (ω : Euclidean d)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hω, mul_one]
  apply hf
  calc
    ‖x + r • (ω : Euclidean d)‖ ≤ ‖x‖ + ‖r • (ω : Euclidean d)‖ := norm_add_le _ _
    _ = ‖x‖ + r := by rw [hrnorm]
    _ ≤ ‖x‖ + T := by gcongr; exact hE r hr
    _ < A := hx

/-- A smooth Schwartz cutoff for a spatial ball.  This is the only cutoff
construction needed by the buffered annular decomposition in Lemma 2.1. -/
theorem exists_schwartz_spatial_ball_cutoff
    (d : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ φ : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d, ‖x‖ ≤ R → φ x = 1) ∧
      (∀ x : Euclidean d, 2 * R ≤ ‖x‖ → φ x = 0) ∧
      ∀ x : Euclidean d, ‖φ x‖ ≤ 1 := by
  rcases exists_schwartz_frequency_cutoff_norm_le_one d with
    ⟨φ, hφone, hφzero, hφnorm⟩
  let D : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 R⁻¹ (inv_ne_zero hR.ne'))
  let ψ : SchwartzMap (Euclidean d) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D) φ
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro x hx
    change φ (D x) = 1
    apply hφone
    change ‖R⁻¹ • x‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    calc
      R⁻¹ * ‖x‖ ≤ R⁻¹ * R :=
        mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  · intro x hx
    change φ (D x) = 0
    apply hφzero
    change 2 ≤ ‖R⁻¹ • x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    calc
      2 = R⁻¹ * (2 * R) := by field_simp
      _ ≤ R⁻¹ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
  · intro x
    change ‖φ (D x)‖ ≤ 1
    exact hφnorm _

/-- A single smooth cutoff for the buffered annulus seen by a dyadic radius
block.  It is one on the sampling region and has uniformly bounded overlap
when the scale varies. -/
theorem exists_schwartz_spatial_annular_cutoff
    (d : ℕ) (k : ℤ) :
    ∃ η : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d,
        (2 : ℝ) ^ (k - 1) ≤ ‖x‖ → ‖x‖ ≤ (2 : ℝ) ^ (k + 2) → η x = 1) ∧
      (∀ x : Euclidean d, ‖x‖ ≤ (2 : ℝ) ^ (k - 2) → η x = 0) ∧
      (∀ x : Euclidean d, (2 : ℝ) ^ (k + 3) ≤ ‖x‖ → η x = 0) ∧
      ∀ x : Euclidean d, ‖η x‖ ≤ 2 := by
  have hRin : 0 < (2 : ℝ) ^ (k - 2) := zpow_pos (by norm_num) _
  have hRout : 0 < (2 : ℝ) ^ (k + 2) := zpow_pos (by norm_num) _
  rcases exists_schwartz_spatial_ball_cutoff d ((2 : ℝ) ^ (k - 2)) hRin with
    ⟨φin, hφin_one, hφin_zero, hφin_norm⟩
  rcases exists_schwartz_spatial_ball_cutoff d ((2 : ℝ) ^ (k + 2)) hRout with
    ⟨φout, hφout_one, hφout_zero, hφout_norm⟩
  refine ⟨φout - φin, ?_, ?_, ?_, ?_⟩
  · intro x hxlo hxhi
    have htwo_in : 2 * (2 : ℝ) ^ (k - 2) = (2 : ℝ) ^ (k - 1) := by
      calc
        2 * (2 : ℝ) ^ (k - 2) = (2 : ℝ) ^ (k - 2) * (2 : ℝ) ^ (1 : ℤ) := by
          norm_num
          ring
        _ = (2 : ℝ) ^ ((k - 2) + 1) := (zpow_add₀ (by norm_num) (k - 2) 1).symm
        _ = (2 : ℝ) ^ (k - 1) := by congr 1 <;> omega
    have hinner : 2 * (2 : ℝ) ^ (k - 2) ≤ ‖x‖ := by
      rw [htwo_in]
      exact hxlo
    rw [show ((φout - φin : SchwartzMap (Euclidean d) ℂ) x) =
        φout x - φin x by rfl, hφout_one x hxhi, hφin_zero x hinner]
    norm_num
  · intro x hx
    have hxout : ‖x‖ ≤ (2 : ℝ) ^ (k + 2) := by
      apply hx.trans
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    rw [show ((φout - φin : SchwartzMap (Euclidean d) ℂ) x) =
        φout x - φin x by rfl, hφout_one x hxout, hφin_one x hx]
    ring
  · intro x hx
    have htwo_out : 2 * (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 3) := by
      calc
        2 * (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (1 : ℤ) := by
          norm_num
          ring
        _ = (2 : ℝ) ^ ((k + 2) + 1) := (zpow_add₀ (by norm_num) (k + 2) 1).symm
        _ = (2 : ℝ) ^ (k + 3) := by congr 1 <;> omega
    have htwo_in : 2 * (2 : ℝ) ^ (k - 2) ≤ ‖x‖ := by
      rw [show 2 * (2 : ℝ) ^ (k - 2) = (2 : ℝ) ^ (k - 1) by
        calc
          2 * (2 : ℝ) ^ (k - 2) = (2 : ℝ) ^ (k - 2) * (2 : ℝ) ^ (1 : ℤ) := by
            norm_num
            ring
          _ = (2 : ℝ) ^ ((k - 2) + 1) := (zpow_add₀ (by norm_num) (k - 2) 1).symm
          _ = (2 : ℝ) ^ (k - 1) := by congr 1 <;> omega]
      exact (zpow_le_zpow_right₀ (by norm_num) (by omega : k - 1 ≤ k + 3)).trans hx
    rw [show ((φout - φin : SchwartzMap (Euclidean d) ℂ) x) =
        φout x - φin x by rfl, hφout_zero x (htwo_out ▸ hx), hφin_zero x htwo_in]
    ring
  · intro x
    rw [show ((φout - φin : SchwartzMap (Euclidean d) ℂ) x) =
      φout x - φin x by rfl]
    calc
      ‖φout x - φin x‖ ≤ ‖φout x‖ + ‖φin x‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hφout_norm x) (hφin_norm x)
      _ = 2 := by norm_num

/-- The fixed smooth inner cutoff used at output shell `j`.  It is one well
inside that shell and vanishes beyond the buffer needed for the radius-block
locality argument. -/
noncomputable def dyadicSpatialBallCutoff (d : ℕ) (j : ℤ) :
    SchwartzMap (Euclidean d) ℂ :=
  Classical.choose (exists_schwartz_spatial_ball_cutoff d ((2 : ℝ) ^ (j + 3))
    (zpow_pos (by norm_num) _))

theorem dyadicSpatialBallCutoff_one (d : ℕ) (j : ℤ) (x : Euclidean d)
    (hx : ‖x‖ ≤ (2 : ℝ) ^ (j + 3)) :
    dyadicSpatialBallCutoff d j x = 1 := by
  exact (Classical.choose_spec (exists_schwartz_spatial_ball_cutoff d
    ((2 : ℝ) ^ (j + 3)) (zpow_pos (by norm_num) _))).1 x hx

theorem dyadicSpatialBallCutoff_zero (d : ℕ) (j : ℤ) (x : Euclidean d)
    (hx : (2 : ℝ) ^ (j + 4) ≤ ‖x‖) :
    dyadicSpatialBallCutoff d j x = 0 := by
  have htwo : 2 * (2 : ℝ) ^ (j + 3) = (2 : ℝ) ^ (j + 4) := by
    calc
      2 * (2 : ℝ) ^ (j + 3) = (2 : ℝ) ^ (j + 3) * (2 : ℝ) ^ (1 : ℤ) := by
        norm_num
        ring
      _ = (2 : ℝ) ^ ((j + 3) + 1) := (zpow_add₀ (by norm_num) (j + 3) 1).symm
      _ = (2 : ℝ) ^ (j + 4) := by congr 1 <;> omega
  exact (Classical.choose_spec (exists_schwartz_spatial_ball_cutoff d
    ((2 : ℝ) ^ (j + 3)) (zpow_pos (by norm_num) _))).2.1 x (htwo ▸ hx)

theorem norm_dyadicSpatialBallCutoff_le_one (d : ℕ) (j : ℤ) (x : Euclidean d) :
    ‖dyadicSpatialBallCutoff d j x‖ ≤ 1 := by
  exact (Classical.choose_spec (exists_schwartz_spatial_ball_cutoff d
    ((2 : ℝ) ^ (j + 3)) (zpow_pos (by norm_num) _))).2.2 x

/-- The fixed buffered annular cutoff at radius scale `2^k`. -/
noncomputable def dyadicSpatialAnnularCutoff (d : ℕ) (k : ℤ) :
    SchwartzMap (Euclidean d) ℂ :=
  Classical.choose (exists_schwartz_spatial_annular_cutoff d k)

theorem dyadicSpatialAnnularCutoff_one (d : ℕ) (k : ℤ) (x : Euclidean d)
    (hxlo : (2 : ℝ) ^ (k - 1) ≤ ‖x‖) (hxhi : ‖x‖ ≤ (2 : ℝ) ^ (k + 2)) :
    dyadicSpatialAnnularCutoff d k x = 1 := by
  exact (Classical.choose_spec (exists_schwartz_spatial_annular_cutoff d k)).1 x hxlo hxhi

theorem dyadicSpatialAnnularCutoff_zero_small (d : ℕ) (k : ℤ) (x : Euclidean d)
    (hx : ‖x‖ ≤ (2 : ℝ) ^ (k - 2)) :
    dyadicSpatialAnnularCutoff d k x = 0 := by
  exact (Classical.choose_spec (exists_schwartz_spatial_annular_cutoff d k)).2.1 x hx

theorem dyadicSpatialAnnularCutoff_zero_large (d : ℕ) (k : ℤ) (x : Euclidean d)
    (hx : (2 : ℝ) ^ (k + 3) ≤ ‖x‖) :
    dyadicSpatialAnnularCutoff d k x = 0 := by
  exact (Classical.choose_spec (exists_schwartz_spatial_annular_cutoff d k)).2.2.1 x hx

theorem norm_dyadicSpatialAnnularCutoff_le_two (d : ℕ) (k : ℤ) (x : Euclidean d) :
    ‖dyadicSpatialAnnularCutoff d k x‖ ≤ 2 := by
  exact (Classical.choose_spec (exists_schwartz_spatial_annular_cutoff d k)).2.2.2 x

/-- The inner and outer Schwartz pieces associated with an output shell. -/
noncomputable def dyadicSpatialInnerPiece {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j : ℤ) : SchwartzMap (Euclidean d) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (dyadicSpatialBallCutoff d j : Euclidean d → ℂ) f

noncomputable def dyadicSpatialOuterPiece {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j : ℤ) : SchwartzMap (Euclidean d) ℂ :=
  f - dyadicSpatialInnerPiece f j

/-- The annular localization of the outer piece at radius block `k`. -/
noncomputable def dyadicSpatialOuterAnnularPiece {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j k : ℤ) : SchwartzMap (Euclidean d) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (dyadicSpatialAnnularCutoff d k : Euclidean d → ℂ)
    (dyadicSpatialOuterPiece f j)

/-- The annular localization of the original input at radius block `k`. -/
noncomputable def dyadicSpatialAnnularPiece {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (k : ℤ) : SchwartzMap (Euclidean d) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (dyadicSpatialAnnularCutoff d k : Euclidean d → ℂ) f

theorem dyadicSpatialInnerPiece_apply {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j : ℤ) (x : Euclidean d) :
    dyadicSpatialInnerPiece f j x = dyadicSpatialBallCutoff d j x * f x := by
  simp only [dyadicSpatialInnerPiece,
    SchwartzMap.smulLeftCLM_apply (dyadicSpatialBallCutoff d j).hasTemperateGrowth,
    smul_eq_mul]

theorem dyadicSpatialOuterPiece_apply {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j : ℤ) (x : Euclidean d) :
    dyadicSpatialOuterPiece f j x = f x - dyadicSpatialBallCutoff d j x * f x := by
  rw [show dyadicSpatialOuterPiece f j x = f x - dyadicSpatialInnerPiece f j x by rfl,
    dyadicSpatialInnerPiece_apply]

theorem dyadicSpatialOuterAnnularPiece_apply {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j k : ℤ) (x : Euclidean d) :
    dyadicSpatialOuterAnnularPiece f j k x =
      dyadicSpatialAnnularCutoff d k x * dyadicSpatialOuterPiece f j x := by
  simp only [dyadicSpatialOuterAnnularPiece,
    SchwartzMap.smulLeftCLM_apply (dyadicSpatialAnnularCutoff d k).hasTemperateGrowth,
    smul_eq_mul]

/-- The buffered annular localization is literally supported where its
spatial cutoff can be nonzero.  This is the support fact used by the
Proposition 5.1 reassembly: only these annular inputs need the local weighted
estimate. -/
private theorem dyadicSpatialAnnularCutoff_eq_zero_of_not_mem_bufferedAnnulus
    {d : ℕ} (k : ℤ) {x : Euclidean d}
    (hx : x ∉ euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3))) :
    dyadicSpatialAnnularCutoff d k x = 0 := by
  unfold euclideanAnnulus at hx
  by_cases hsmall : ‖x‖ ≤ (2 : ℝ) ^ (k - 2)
  · exact dyadicSpatialAnnularCutoff_zero_small d k x hsmall
  · have hnorm : (2 : ℝ) ^ (k - 2) < ‖x‖ := lt_of_not_ge hsmall
    have hinner : x ∉ Metric.ball (0 : Euclidean d) ((2 : ℝ) ^ (k - 2)) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact not_lt_of_ge hnorm.le
    have houter : x ∉ Metric.closedBall (0 : Euclidean d) ((2 : ℝ) ^ (k + 3)) := by
      intro hxouter
      exact hx ⟨hxouter, hinner⟩
    rw [Metric.mem_closedBall, dist_zero_right] at houter
    exact dyadicSpatialAnnularCutoff_zero_large d k x (le_of_not_ge houter)

private theorem dyadicSpatialAnnularPiece_eq_zero_of_not_mem_bufferedAnnulus
    {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ) (k : ℤ) {x : Euclidean d}
    (hx : x ∉ euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3))) :
    dyadicSpatialAnnularPiece f k x = 0 := by
  simp only [dyadicSpatialAnnularPiece,
    SchwartzMap.smulLeftCLM_apply (dyadicSpatialAnnularCutoff d k).hasTemperateGrowth,
    smul_eq_mul]
  rw [
    dyadicSpatialAnnularCutoff_eq_zero_of_not_mem_bufferedAnnulus k hx, zero_mul]

private theorem dyadicSpatialOuterAnnularPiece_eq_zero_of_not_mem_bufferedAnnulus
    {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ) (j k : ℤ) {x : Euclidean d}
    (hx : x ∉ euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3))) :
    dyadicSpatialOuterAnnularPiece f j k x = 0 := by
  simp only [dyadicSpatialOuterAnnularPiece,
    SchwartzMap.smulLeftCLM_apply (dyadicSpatialAnnularCutoff d k).hasTemperateGrowth,
    smul_eq_mul]
  rw [
    dyadicSpatialAnnularCutoff_eq_zero_of_not_mem_bufferedAnnulus k hx, zero_mul]

theorem dyadicSpatialAnnularPiece_apply {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (k : ℤ) (x : Euclidean d) :
    dyadicSpatialAnnularPiece f k x = dyadicSpatialAnnularCutoff d k x * f x := by
  simp only [dyadicSpatialAnnularPiece,
    SchwartzMap.smulLeftCLM_apply (dyadicSpatialAnnularCutoff d k).hasTemperateGrowth,
    smul_eq_mul]

theorem dyadicSpatialOuterPiece_eq_zero_on_innerBall {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j : ℤ) (x : Euclidean d)
    (hx : ‖x‖ ≤ (2 : ℝ) ^ (j + 3)) :
    dyadicSpatialOuterPiece f j x = 0 := by
  rw [dyadicSpatialOuterPiece_apply, dyadicSpatialBallCutoff_one d j x hx]
  ring

theorem dyadicSpatialOuterPiece_eq_input_outside {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j : ℤ) (x : Euclidean d)
    (hx : (2 : ℝ) ^ (j + 4) ≤ ‖x‖) :
    dyadicSpatialOuterPiece f j x = f x := by
  rw [dyadicSpatialOuterPiece_apply, dyadicSpatialBallCutoff_zero d j x hx]
  ring

theorem norm_dyadicSpatialOuterPiece_le_two_mul {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j : ℤ) (x : Euclidean d) :
    ‖dyadicSpatialOuterPiece f j x‖ ≤ 2 * ‖f x‖ := by
  rw [dyadicSpatialOuterPiece_apply]
  calc
    ‖f x - dyadicSpatialBallCutoff d j x * f x‖ ≤
        ‖f x‖ + ‖dyadicSpatialBallCutoff d j x * f x‖ := norm_sub_le _ _
    _ = ‖f x‖ + ‖dyadicSpatialBallCutoff d j x‖ * ‖f x‖ := by
      rw [norm_mul]
    _ ≤ ‖f x‖ + 1 * ‖f x‖ := by
      gcongr
      exact norm_dyadicSpatialBallCutoff_le_one d j x
    _ = 2 * ‖f x‖ := by ring

theorem norm_dyadicSpatialOuterAnnularPiece_le_four_mul {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j k : ℤ) (x : Euclidean d) :
    ‖dyadicSpatialOuterAnnularPiece f j k x‖ ≤ 4 * ‖f x‖ := by
  rw [dyadicSpatialOuterAnnularPiece_apply, norm_mul]
  calc
    ‖dyadicSpatialAnnularCutoff d k x‖ * ‖dyadicSpatialOuterPiece f j x‖ ≤
        2 * (2 * ‖f x‖) := by
      gcongr
      · exact norm_dyadicSpatialAnnularCutoff_le_two d k x
      · exact norm_dyadicSpatialOuterPiece_le_two_mul f j x
    _ = 4 * ‖f x‖ := by ring

theorem norm_dyadicSpatialAnnularPiece_le_two_mul {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (k : ℤ) (x : Euclidean d) :
    ‖dyadicSpatialAnnularPiece f k x‖ ≤ 2 * ‖f x‖ := by
  rw [dyadicSpatialAnnularPiece_apply, norm_mul]
  calc
    ‖dyadicSpatialAnnularCutoff d k x‖ * ‖f x‖ ≤ 2 * ‖f x‖ := by
      gcongr
      exact norm_dyadicSpatialAnnularCutoff_le_two d k x

/-- The small-radius half of the spatial-shell argument.  If an input
vanishes on the ball well inside a dyadic spatial annulus, then radius blocks
no larger than that annulus make no contribution there.  The three powers of
two are a deliberate buffer for the later smooth cutoff. -/
theorem restrictedNormalizedSphericalMaximal_dyadic_block_eq_zero_on_shell_of_inner_vanishing
    {d : ℕ} (E : Set ℝ) (f : Euclidean d → ℂ) (j k : ℤ)
    (hf : ∀ y : Euclidean d, ‖y‖ < (2 : ℝ) ^ (j + 3) → f y = 0)
    (hkj : k ≤ j + 1) {x : Euclidean d} (hx : ‖x‖ ≤ (2 : ℝ) ^ (j + 1)) :
    restrictedNormalizedSphericalMaximal d
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) f x = 0 := by
  apply restrictedNormalizedSphericalMaximal_eq_zero_inside_ball
    (A := (2 : ℝ) ^ (j + 3)) (T := (2 : ℝ) ^ (k + 1))
  · intro r hr
    exact hr.1.2.2
  · exact hf
  · have hkpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (j + 2) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    calc
      ‖x‖ + (2 : ℝ) ^ (k + 1) ≤
          (2 : ℝ) ^ (j + 1) + (2 : ℝ) ^ (j + 2) := by gcongr
      _ < (2 : ℝ) ^ (j + 3) := by
        have hpow_one : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by
          calc
            (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * (2 : ℝ) ^ (1 : ℤ) :=
              zpow_add₀ (by norm_num) j 1
            _ = 2 * (2 : ℝ) ^ j := by norm_num; ring
        have hpow_three : (2 : ℝ) ^ (j + 3) = 8 * (2 : ℝ) ^ j := by
          calc
            (2 : ℝ) ^ (j + 3) = (2 : ℝ) ^ j * (2 : ℝ) ^ (3 : ℤ) :=
              zpow_add₀ (by norm_num) j 3
            _ = 8 * (2 : ℝ) ^ j := by norm_num; ring
        have hpow_two : (2 : ℝ) ^ (j + 2) = 4 * (2 : ℝ) ^ j := by
          calc
            (2 : ℝ) ^ (j + 2) = (2 : ℝ) ^ j * (2 : ℝ) ^ (2 : ℤ) :=
              zpow_add₀ (by norm_num) j 2
            _ = 4 * (2 : ℝ) ^ j := by norm_num; ring
        rw [hpow_one, hpow_two, hpow_three]
        nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) j]

/-- The complementary geometric fact for the spatial-shell argument.  On a
much smaller output shell, a radius block at scale `2^k` samples only the
buffered input shell at that same scale. -/
theorem restrictedNormalizedSphericalMaximal_dyadic_block_eq_of_eq_on_buffered_shell
    {d : ℕ} (E : Set ℝ) (f g : Euclidean d → ℂ) (j k : ℤ)
    (hkj : j + 2 ≤ k) {x : Euclidean d} (hx : ‖x‖ ≤ (2 : ℝ) ^ (j + 1))
    (hfg : ∀ y : Euclidean d,
      (2 : ℝ) ^ (k - 1) ≤ ‖y‖ → ‖y‖ ≤ (2 : ℝ) ^ (k + 2) → f y = g y) :
    restrictedNormalizedSphericalMaximal d
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) f x =
      restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) g x := by
  have hjpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (k - 1) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hpow_half : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
    calc
      (2 : ℝ) ^ k = (2 : ℝ) ^ ((k - 1) + 1) := by congr 1 <;> omega
      _ = (2 : ℝ) ^ (k - 1) * (2 : ℝ) ^ (1 : ℤ) :=
        zpow_add₀ (by norm_num) (k - 1) 1
      _ = 2 * (2 : ℝ) ^ (k - 1) := by norm_num; ring
  have hpow_succ : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    calc
      (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * (2 : ℝ) ^ (1 : ℤ) :=
        zpow_add₀ (by norm_num) k 1
      _ = 2 * (2 : ℝ) ^ k := by norm_num; ring
  have hpow_two : (2 : ℝ) ^ (k + 2) = 4 * (2 : ℝ) ^ k := by
    calc
      (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ k * (2 : ℝ) ^ (2 : ℤ) :=
        zpow_add₀ (by norm_num) k 2
      _ = 4 * (2 : ℝ) ^ k := by norm_num; ring
  unfold restrictedNormalizedSphericalMaximal
  congr with r
  rw [normalizedSphericalAverage_eq_of_forall f g r.1 x]
  intro ω
  have hrlo : (2 : ℝ) ^ k ≤ r.1 := r.2.1.2.1
  have hrhi : r.1 ≤ (2 : ℝ) ^ (k + 1) := r.2.1.2.2
  have hrpos : 0 < r.1 := r.2.2
  have hω : ‖(ω : Euclidean d)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  have hrnorm : ‖r.1 • (ω : Euclidean d)‖ = r.1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hω, mul_one]
  apply hfg
  · have htri : ‖r.1 • (ω : Euclidean d)‖ ≤
        ‖x + r.1 • (ω : Euclidean d)‖ + ‖x‖ := by
      calc
        ‖r.1 • (ω : Euclidean d)‖ = ‖(x + r.1 • (ω : Euclidean d)) - x‖ := by
          congr 1
          abel
        _ ≤ ‖x + r.1 • (ω : Euclidean d)‖ + ‖x‖ := norm_sub_le _ _
    rw [hrnorm] at htri
    have hx' : ‖x‖ ≤ (2 : ℝ) ^ (k - 1) := hx.trans hjpow
    have hrlo' : 2 * (2 : ℝ) ^ (k - 1) ≤ r.1 := by
      rw [← hpow_half]
      exact hrlo
    linarith
  · calc
      ‖x + r.1 • (ω : Euclidean d)‖ ≤ ‖x‖ + ‖r.1 • (ω : Euclidean d)‖ :=
        norm_add_le _ _
      _ = ‖x‖ + r.1 := by rw [hrnorm]
      _ ≤ (2 : ℝ) ^ (j + 1) + (2 : ℝ) ^ (k + 1) := by gcongr
      _ ≤ (2 : ℝ) ^ (k - 1) + (2 : ℝ) ^ (k + 1) := by gcongr
      _ ≤ (2 : ℝ) ^ (k + 2) := by
        rw [hpow_succ, hpow_two]
        nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) (k - 1)]

/-- The half-open spatial annuli used to reassemble the weighted moment.
They form a genuine partition away from the origin, so unlike closed annuli
they do not introduce an artificial overlap in the Tonelli step. -/
def dyadicSpatialShell (d : ℕ) (j : ℤ) : Set (Euclidean d) :=
  {x | ‖x‖ ∈ Ioc ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1))}

theorem measurableSet_dyadicSpatialShell (d : ℕ) (j : ℤ) :
    MeasurableSet (dyadicSpatialShell d j) := by
  unfold dyadicSpatialShell
  exact continuous_norm.measurable measurableSet_Ioc

theorem pairwiseDisjoint_dyadicSpatialShell (d : ℕ) :
    Pairwise (Function.onFun Disjoint (dyadicSpatialShell d)) := by
  intro j k hjk
  change Disjoint (dyadicSpatialShell d j) (dyadicSpatialShell d k)
  rw [Set.disjoint_left]
  intro x hxj hxk
  change (2 : ℝ) ^ j < ‖x‖ ∧ ‖x‖ ≤ (2 : ℝ) ^ (j + 1) at hxj
  change (2 : ℝ) ^ k < ‖x‖ ∧ ‖x‖ ≤ (2 : ℝ) ^ (k + 1) at hxk
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k := by
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    exact (not_lt_of_ge (hxj.2.trans hpow)) hxk.1
  · have hpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j := by
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    exact (not_lt_of_ge (hxk.2.trans hpow)) hxj.1

/-- The five-shell band containing the support of the smooth annular cutoff
at scale `2^k`. -/
def dyadicSpatialBand (d : ℕ) (k : ℤ) : Set (Euclidean d) :=
  ⋃ l ∈ (Finset.Icc (k - 2) (k + 2) : Set ℤ), dyadicSpatialShell d l

theorem mem_dyadicSpatialBand_of_annularCutoff_ne_zero
    {d : ℕ} (k : ℤ) {x : Euclidean d}
    (hx : dyadicSpatialAnnularCutoff d k x ≠ 0) :
    x ∈ dyadicSpatialBand d k := by
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hx
    apply dyadicSpatialAnnularCutoff_zero_small d k x
    rw [hx0, norm_zero]
    exact (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
  obtain ⟨l, hl⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr hx0)
    (by norm_num : (1 : ℝ) < 2)
  have hlow : k - 2 ≤ l := by
    by_contra hnot
    have hle : l + 1 ≤ k - 2 := by omega
    have hpow : (2 : ℝ) ^ (l + 1) ≤ (2 : ℝ) ^ (k - 2) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      exact hle
    apply hx
    apply dyadicSpatialAnnularCutoff_zero_small d k x
    exact hl.2.trans hpow
  have hhigh : l ≤ k + 2 := by
    by_contra hnot
    have hle : k + 3 ≤ l := by omega
    have hpow : (2 : ℝ) ^ (k + 3) ≤ (2 : ℝ) ^ l := by
      apply zpow_le_zpow_right₀ (by norm_num)
      exact hle
    apply hx
    apply dyadicSpatialAnnularCutoff_zero_large d k x
    exact hpow.trans hl.1.le
  refine Set.mem_iUnion.2 ⟨l, ?_⟩
  refine Set.mem_iUnion.2 ⟨Finset.mem_Icc.mpr ⟨hlow, hhigh⟩, ?_⟩
  exact hl

/-- If `x` lies in shell `j`, then only the five annular cutoff bands with
indices from `j - 2` through `j + 2` can contain `x`. -/
theorem mem_dyadicSpatialBand_index_mem_Icc
    {d : ℕ} {j k : ℤ} {x : Euclidean d}
    (hxj : x ∈ dyadicSpatialShell d j) (hxk : x ∈ dyadicSpatialBand d k) :
    k ∈ Finset.Icc (j - 2) (j + 2) := by
  rcases Set.mem_iUnion.mp hxk with ⟨l, hxk⟩
  rcases Set.mem_iUnion.mp hxk with ⟨hlrange, hxl⟩
  have hlj : l = j := by
    by_contra hne
    have hdisj := pairwiseDisjoint_dyadicSpatialShell d hne
    exact (Set.disjoint_left.mp hdisj hxl hxj)
  rcases Finset.mem_Icc.mp hlrange with ⟨hlow, hhigh⟩
  apply Finset.mem_Icc.mpr
  constructor <;> omega

/-- The support bands of the smooth annular cutoffs have multiplicity at most
five. -/
theorem tsum_indicator_dyadicSpatialBand_le_five (d : ℕ) (x : Euclidean d) :
    (∑' k : ℤ,
      (dyadicSpatialBand d k).indicator (fun _ : Euclidean d => (1 : ENNReal)) x) ≤ 5 := by
  classical
  by_cases hx0 : x = 0
  · subst x
    have hnot (k : ℤ) : (0 : Euclidean d) ∉ dyadicSpatialBand d k := by
      rintro h
      rcases Set.mem_iUnion.mp h with ⟨l, h⟩
      rcases Set.mem_iUnion.mp h with ⟨_, hl⟩
      change (2 : ℝ) ^ l < ‖(0 : Euclidean d)‖ ∧
        ‖(0 : Euclidean d)‖ ≤ (2 : ℝ) ^ (l + 1) at hl
      rw [norm_zero] at hl
      exact (not_lt_of_ge (zpow_pos (by norm_num : (0 : ℝ) < 2) l).le) hl.1
    calc
      (∑' k : ℤ,
          (dyadicSpatialBand d k).indicator (fun _ : Euclidean d => (1 : ENNReal)) 0) =
          ∑' _k : ℤ, (0 : ENNReal) := by
        apply tsum_congr
        intro k
        rw [Set.indicator_of_notMem (hnot k)]
      _ = 0 := tsum_zero
      _ ≤ 5 := by norm_num
  · obtain ⟨j, hxj⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr hx0)
      (by norm_num : (1 : ℝ) < 2)
    let K : Finset ℤ := Finset.Icc (j - 2) (j + 2)
    have hterm (k : ℤ) :
        (dyadicSpatialBand d k).indicator (fun _ : Euclidean d => (1 : ENNReal)) x ≤
          if k ∈ K then 1 else 0 := by
      by_cases hk : x ∈ dyadicSpatialBand d k
      · rw [Set.indicator_of_mem hk]
        have hk' : k ∈ K := by
          dsimp [K]
          exact mem_dyadicSpatialBand_index_mem_Icc hxj hk
        simp [hk']
      · rw [Set.indicator_of_notMem hk]
        simp
    have hcard : K.card = 5 := by
      dsimp [K]
      rw [Int.card_Icc]
      omega
    calc
      (∑' k : ℤ,
          (dyadicSpatialBand d k).indicator (fun _ : Euclidean d => (1 : ENNReal)) x) ≤
          ∑' k : ℤ, if k ∈ K then (1 : ENNReal) else 0 := ENNReal.tsum_le_tsum hterm
      _ = ∑ k ∈ K, (1 : ENNReal) := by
        calc
          (∑' k : ℤ, if k ∈ K then (1 : ENNReal) else 0) =
              ∑ k ∈ K, if k ∈ K then (1 : ENNReal) else 0 :=
            tsum_eq_sum (f := fun k : ℤ => if k ∈ K then (1 : ENNReal) else 0) (s := K) (by
              intro k hk
              simp only [if_neg hk])
          _ = ∑ k ∈ K, (1 : ENNReal) := by simp
      _ = 5 := by simp [hcard]

/-- A family of Schwartz inputs controlled by the dyadic annular cutoffs has
summable `p`-moments, with only the five-fold spatial overlap as a loss. -/
theorem tsum_lintegral_enorm_rpow_le_of_dyadic_annular_cutoff_control
    {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ)
    (g : ℤ → SchwartzMap (Euclidean d) ℂ) (μ : Measure (Euclidean d))
    {p : ℝ} (hp : 0 < p) (A : ENNReal)
    (hnorm : ∀ k : ℤ, ∀ x : Euclidean d,
      ‖g k x‖ₑ ≤ A * ‖f x‖ₑ)
    (hzero : ∀ k : ℤ, ∀ x : Euclidean d,
      dyadicSpatialAnnularCutoff d k x = 0 → g k x = 0) :
    (∑' k : ℤ, ∫⁻ x, ‖g k x‖ₑ ^ p ∂μ) ≤
      (A ^ p * 5) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) := by
  have hmeas (k : ℤ) : AEMeasurable (fun x : Euclidean d => ‖g k x‖ₑ ^ p) μ := by
    exact (ENNReal.continuous_rpow_const.measurable.comp
      ((g k).continuous.measurable.enorm)).aemeasurable
  have hfmeas : Measurable (fun x : Euclidean d => ‖f x‖ₑ ^ p) := by
    exact ENNReal.continuous_rpow_const.measurable.comp (f.continuous.measurable.enorm)
  have hpoint (x : Euclidean d) :
      (∑' k : ℤ, ‖g k x‖ₑ ^ p) ≤
        (A ^ p * 5) * ‖f x‖ₑ ^ p := by
    have hterm (k : ℤ) : ‖g k x‖ₑ ^ p ≤
        (A ^ p * ‖f x‖ₑ ^ p) *
          (dyadicSpatialBand d k).indicator (fun _ : Euclidean d => (1 : ENNReal)) x := by
      by_cases hk : dyadicSpatialAnnularCutoff d k x = 0
      · rw [hzero k x hk, enorm_zero, ENNReal.zero_rpow_of_pos hp]
        exact bot_le
      · have hband : x ∈ dyadicSpatialBand d k :=
          mem_dyadicSpatialBand_of_annularCutoff_ne_zero k hk
        rw [Set.indicator_of_mem hband]
        have hpow : ‖g k x‖ₑ ^ p ≤ A ^ p * ‖f x‖ₑ ^ p := by
          calc
            ‖g k x‖ₑ ^ p ≤ (A * ‖f x‖ₑ) ^ p :=
              ENNReal.rpow_le_rpow (hnorm k x) hp.le
            _ = A ^ p * ‖f x‖ₑ ^ p := ENNReal.mul_rpow_of_nonneg _ _ hp.le
        simpa only [mul_one] using hpow
    calc
      (∑' k : ℤ, ‖g k x‖ₑ ^ p) ≤
          ∑' k : ℤ, (A ^ p * ‖f x‖ₑ ^ p) *
            (dyadicSpatialBand d k).indicator (fun _ : Euclidean d => (1 : ENNReal)) x :=
        ENNReal.tsum_le_tsum hterm
      _ = (A ^ p * ‖f x‖ₑ ^ p) *
          (∑' k : ℤ,
            (dyadicSpatialBand d k).indicator (fun _ : Euclidean d => (1 : ENNReal)) x) := by
        rw [ENNReal.tsum_mul_left]
      _ ≤ (A ^ p * ‖f x‖ₑ ^ p) * 5 := by
        exact mul_le_mul_right (tsum_indicator_dyadicSpatialBand_le_five d x) _
      _ = (A ^ p * 5) * ‖f x‖ₑ ^ p := by ring
  calc
    (∑' k : ℤ, ∫⁻ x, ‖g k x‖ₑ ^ p ∂μ) =
        ∫⁻ x, ∑' k : ℤ, ‖g k x‖ₑ ^ p ∂μ := (lintegral_tsum hmeas).symm
    _ ≤ ∫⁻ x, (A ^ p * 5) * ‖f x‖ₑ ^ p ∂μ := lintegral_mono hpoint
    _ = (A ^ p * 5) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :=
      lintegral_const_mul _ hfmeas

theorem iUnion_dyadicSpatialShell_eq_compl_singleton (d : ℕ) :
    (⋃ j : ℤ, dyadicSpatialShell d j) = ({0} : Set (Euclidean d))ᶜ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hx⟩
    intro hx0
    change ‖x‖ ∈ Ioc ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)) at hx
    rw [hx0, norm_zero] at hx
    exact (not_lt_of_ge (zpow_pos (by norm_num : (0 : ℝ) < 2) j).le) hx.1
  · intro hx
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    obtain ⟨j, hj⟩ := exists_mem_Ioc_zpow hxnorm (by norm_num : (1 : ℝ) < 2)
    refine ⟨j, ?_⟩
    exact hj

/-- The radial power measure has no atom at the origin in positive
dimension.  This lets the dyadic shell partition account for the whole
weighted moment. -/
theorem powerWeightedVolume_singleton_zero
    {d : ℕ} (hd : 1 ≤ d) (α : ℝ) :
    powerWeightedVolume d α ({0} : Set (Euclidean d)) = 0 := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  unfold powerWeightedVolume
  exact withDensity_absolutelyContinuous volume (radialPowerWeight d α)
    (measure_singleton (0 : Euclidean d))

/-- Almost every point for a power-weighted measure belongs to exactly one
dyadic spatial shell. -/
theorem ae_mem_iUnion_dyadicSpatialShell
    {d : ℕ} (hd : 1 ≤ d) (α : ℝ) :
    ∀ᵐ x : Euclidean d ∂powerWeightedVolume d α,
      x ∈ ⋃ j : ℤ, dyadicSpatialShell d j := by
  rw [ae_iff]
  have hzero := powerWeightedVolume_singleton_zero hd α
  rw [iUnion_dyadicSpatialShell_eq_compl_singleton]
  have hset : {x : Euclidean d | x ∉ ({0} : Set (Euclidean d))ᶜ} = {0} := by
    ext x
    simp
  rw [hset]
  exact hzero

/-- Reassembling a nonnegative weighted moment over the dyadic spatial
shells. -/
theorem lintegral_eq_tsum_setLIntegral_dyadicSpatialShell
    {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (F : Euclidean d → ENNReal) :
    (∫⁻ x, F x ∂powerWeightedVolume d α) =
      ∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j, F x ∂powerWeightedVolume d α := by
  let S : Set (Euclidean d) := ⋃ j : ℤ, dyadicSpatialShell d j
  have hS : MeasurableSet S :=
    MeasurableSet.iUnion (fun j => measurableSet_dyadicSpatialShell d j)
  have hAE : ∀ᵐ x : Euclidean d ∂powerWeightedVolume d α, x ∈ S := by
    simpa only [S] using ae_mem_iUnion_dyadicSpatialShell hd α
  have hindicator : F =ᵐ[powerWeightedVolume d α] S.indicator F := by
    filter_upwards [hAE] with x hx
    simp [Set.indicator_of_mem hx]
  calc
    (∫⁻ x, F x ∂powerWeightedVolume d α) =
        ∫⁻ x, S.indicator F x ∂powerWeightedVolume d α :=
      lintegral_congr_ae hindicator
    _ = ∫⁻ x in S, F x ∂powerWeightedVolume d α :=
      lintegral_indicator hS F
    _ = ∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j, F x ∂powerWeightedVolume d α := by
      dsimp [S]
      rw [lintegral_iUnion (fun j => measurableSet_dyadicSpatialShell d j)
        (pairwiseDisjoint_dyadicSpatialShell d)]

/-- The small radius blocks of the smooth outer piece vanish on their
associated output shell. -/
theorem restrictedNormalizedSphericalMaximal_dyadic_block_outerPiece_eq_zero_on_shell
    {d : ℕ} (E : Set ℝ) (f : SchwartzMap (Euclidean d) ℂ) (j k : ℤ)
    (hkj : k ≤ j + 1) {x : Euclidean d} (hx : x ∈ dyadicSpatialShell d j) :
    restrictedNormalizedSphericalMaximal d
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
      (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) x = 0 := by
  apply restrictedNormalizedSphericalMaximal_dyadic_block_eq_zero_on_shell_of_inner_vanishing
    E (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) j k ?_ hkj hx.2
  intro y hy
  exact dyadicSpatialOuterPiece_eq_zero_on_innerBall f j y hy.le

/-- A far radius block only sees the buffered annular localization of the
outer piece. -/
theorem restrictedNormalizedSphericalMaximal_dyadic_block_outerPiece_eq_outerAnnularPiece
    {d : ℕ} (E : Set ℝ) (f : SchwartzMap (Euclidean d) ℂ) (j k : ℤ)
    (hkj : j + 2 ≤ k) {x : Euclidean d} (hx : x ∈ dyadicSpatialShell d j) :
    restrictedNormalizedSphericalMaximal d
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
      (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) x =
      restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (dyadicSpatialOuterAnnularPiece f j k : Euclidean d → ℂ) x := by
  apply restrictedNormalizedSphericalMaximal_dyadic_block_eq_of_eq_on_buffered_shell
    E (dyadicSpatialOuterPiece f j : Euclidean d → ℂ)
      (dyadicSpatialOuterAnnularPiece f j k : Euclidean d → ℂ) j k hkj hx.2
  intro y hylo hyhi
  rw [dyadicSpatialOuterAnnularPiece_apply,
    dyadicSpatialAnnularCutoff_one d k y hylo hyhi]
  ring

/-- Once the radius block is at least five scales beyond the output shell,
the outer piece is already the original input on the entire sampling region. -/
theorem restrictedNormalizedSphericalMaximal_dyadic_block_outerPiece_eq_annularPiece
    {d : ℕ} (E : Set ℝ) (f : SchwartzMap (Euclidean d) ℂ) (j k : ℤ)
    (hkj : j + 5 ≤ k) {x : Euclidean d} (hx : x ∈ dyadicSpatialShell d j) :
    restrictedNormalizedSphericalMaximal d
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
      (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) x =
      restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) x := by
  have hkj' : j + 2 ≤ k := by omega
  apply restrictedNormalizedSphericalMaximal_dyadic_block_eq_of_eq_on_buffered_shell
    E (dyadicSpatialOuterPiece f j : Euclidean d → ℂ)
      (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) j k hkj' hx.2
  intro y hylo hyhi
  have hfar : (2 : ℝ) ^ (j + 4) ≤ ‖y‖ := by
    apply (zpow_le_zpow_right₀ (by norm_num) (by omega : j + 4 ≤ k - 1)).trans hylo
  rw [dyadicSpatialOuterPiece_eq_input_outside f j y hfar,
    dyadicSpatialAnnularPiece_apply,
    dyadicSpatialAnnularCutoff_one d k y hylo hyhi]
  ring

/-! The following private lemmas are the spatial-shell part of the
global-to-local argument.  They are kept concrete: the cutoffs are the
literal `dyadicSpatial...` cutoffs already used above, rather than a new
operator abstraction. -/

private def globalToLocalCoeff (α : ℝ) (j : ℤ) : ENNReal :=
  ENNReal.ofReal ((2 : ℝ) ^ ((j : ℝ) * α))

private theorem globalToLocalCoeff_eq_weight (α : ℝ) (j : ℤ) :
    globalToLocalCoeff α j = (ENNReal.ofReal ((2 : ℝ) ^ j)) ^ α := by
  unfold globalToLocalCoeff
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  rw [ENNReal.ofReal_rpow_of_pos (zpow_pos (by norm_num) j)]
  congr 1
  rw [Real.rpow_mul h2, Real.rpow_intCast]

private theorem globalToLocalCoeff_succ (α : ℝ) (a : ℤ) (n : ℕ) :
    globalToLocalCoeff α (a + n) =
      globalToLocalCoeff α a * (ENNReal.ofReal ((2 : ℝ) ^ α)) ^ n := by
  unfold globalToLocalCoeff
  have h2 : 0 < (2 : ℝ) := by norm_num
  rw [show (((a + n : ℤ) : ℝ) * α) = (a : ℝ) * α + (n : ℝ) * α by
    push_cast
    ring,
    Real.rpow_add h2]
  rw [show (2 : ℝ) ^ ((n : ℝ) * α) = ((2 : ℝ) ^ α) ^ n by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul h2.le]
    congr 1
    ring]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg h2.le _),
    ENNReal.ofReal_pow (Real.rpow_nonneg h2.le _)]

private theorem globalToLocalCoeff_tail (α : ℝ) (a : ℤ) :
    (∑' l : Ici a, globalToLocalCoeff α l) ≤
      globalToLocalCoeff α a * (1 - ENNReal.ofReal ((2 : ℝ) ^ α))⁻¹ := by
  let e : ℕ → Ici a := fun n => ⟨a + n, by
    change a ≤ a + n
    omega⟩
  have he : Function.Surjective e := by
    intro l
    refine ⟨(l.1 - a).toNat, ?_⟩
    apply Subtype.ext
    dsimp [e]
    rw [Int.toNat_sub_of_le l.2]
    ring
  calc
    (∑' l : {l : ℤ // a ≤ l}, globalToLocalCoeff α l) ≤
        ∑' n : ℕ, globalToLocalCoeff α (e n) :=
      ENNReal.tsum_le_tsum_comp_of_surjective he _
    _ = ∑' n : ℕ, globalToLocalCoeff α a *
        (ENNReal.ofReal ((2 : ℝ) ^ α)) ^ n := by
      apply tsum_congr
      intro n
      exact globalToLocalCoeff_succ α a n
    _ = globalToLocalCoeff α a * ∑' n : ℕ,
        (ENNReal.ofReal ((2 : ℝ) ^ α)) ^ n := by
      simpa using
        (ENNReal.tsum_mul_left
          (f := fun n : ℕ => (ENNReal.ofReal ((2 : ℝ) ^ α)) ^ n)
          (a := globalToLocalCoeff α a))
    _ = globalToLocalCoeff α a *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ α))⁻¹ := by
      rw [ENNReal.tsum_geometric]

private theorem globalToLocalCoeff_le_weight_of_mem_shell {d : ℕ} {α : ℝ}
    (hα : α ≤ 0) {j : ℤ} {x : Euclidean d}
    (hx : x ∈ dyadicSpatialShell d j) :
    globalToLocalCoeff α (j + 1) ≤ radialPowerWeight d α x := by
  rw [globalToLocalCoeff_eq_weight]
  apply radialPowerWeight_ge_of_mem_closedBall_nonpos hα
    (zpow_pos (by norm_num) _)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2

private def globalToLocalHardyConstant (α : ℝ) : ENNReal :=
  ENNReal.ofReal ((2 : ℝ) ^ (-4 * α)) *
    (1 - ENNReal.ofReal ((2 : ℝ) ^ α))⁻¹

private theorem globalToLocalCoeff_shift_neg_four (α : ℝ) (j : ℤ) :
    globalToLocalCoeff α (j - 3) =
      ENNReal.ofReal ((2 : ℝ) ^ (-4 * α)) * globalToLocalCoeff α (j + 1) := by
  unfold globalToLocalCoeff
  have h2 : 0 < (2 : ℝ) := by norm_num
  rw [show (((j - 3 : ℤ) : ℝ) * α) =
      -4 * α + ((j + 1 : ℤ) : ℝ) * α by
    push_cast
    ring,
    Real.rpow_add h2]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg h2.le _)]

private theorem globalToLocalCoeff_tail_le_hardy (α : ℝ) (j : ℤ) :
    (∑' l : Ici (j - 3), globalToLocalCoeff α l) ≤
      globalToLocalHardyConstant α * globalToLocalCoeff α (j + 1) := by
  calc
    (∑' l : Ici (j - 3), globalToLocalCoeff α l) ≤
        globalToLocalCoeff α (j - 3) *
          (1 - ENNReal.ofReal ((2 : ℝ) ^ α))⁻¹ :=
      globalToLocalCoeff_tail α (j - 3)
    _ = globalToLocalHardyConstant α * globalToLocalCoeff α (j + 1) := by
      rw [globalToLocalCoeff_shift_neg_four]
      unfold globalToLocalHardyConstant
      ring

private theorem enorm_dyadicSpatialInnerPiece_le {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (j : ℤ) (x : Euclidean d) :
    ‖dyadicSpatialInnerPiece f j x‖ₑ ≤ ‖f x‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  apply ENNReal.coe_le_coe.mpr
  apply NNReal.coe_le_coe.mp
  change ‖dyadicSpatialInnerPiece f j x‖ ≤ ‖f x‖
  rw [dyadicSpatialInnerPiece_apply, norm_mul]
  calc
    ‖dyadicSpatialBallCutoff d j x‖ * ‖f x‖ ≤ 1 * ‖f x‖ := by
      gcongr
      exact norm_dyadicSpatialBallCutoff_le_one d j x
    _ = ‖f x‖ := one_mul _

private theorem dyadicSpatialInnerPiece_eq_zero_of_shell_lt {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) {j l : ℤ} {x : Euclidean d}
    (hx : x ∈ dyadicSpatialShell d j) (hl : l < j - 3) :
    dyadicSpatialInnerPiece f l x = 0 := by
  have hlj : l + 4 ≤ j := by omega
  have hpow : (2 : ℝ) ^ (l + 4) ≤ ‖x‖ := by
    exact (calc
      (2 : ℝ) ^ (l + 4) ≤ (2 : ℝ) ^ j :=
        zpow_le_zpow_right₀ (by norm_num) hlj
      _ < ‖x‖ := hx.1).le
  rw [dyadicSpatialInnerPiece_apply,
    dyadicSpatialBallCutoff_zero d l x hpow]
  simp

private theorem ae_dyadicSpatialInner_hardy {d : ℕ} (hd : 1 ≤ d) {p α : ℝ}
    (hp : 0 < p) (hα : α < 0) (f : SchwartzMap (Euclidean d) ℂ) :
    ∀ᵐ x ∂volume,
      (∑' l : ℤ, globalToLocalCoeff α l *
        ‖dyadicSpatialInnerPiece f l x‖ₑ ^ p) ≤
        globalToLocalHardyConstant α * ‖f x‖ₑ ^ p * radialPowerWeight d α x := by
  filter_upwards [ae_ne_zero_volume_euclidean hd] with x hx0
  have hxunion : x ∈ ⋃ j : ℤ, dyadicSpatialShell d j := by
    rw [iUnion_dyadicSpatialShell_eq_compl_singleton]
    simpa only [mem_compl_iff, mem_singleton_iff] using hx0
  rcases Set.mem_iUnion.mp hxunion with ⟨j, hxj⟩
  let P : ENNReal := ‖f x‖ₑ ^ p
  let S : Set ℤ := Ici (j - 3)
  have hterm (l : ℤ) :
      globalToLocalCoeff α l * ‖dyadicSpatialInnerPiece f l x‖ₑ ^ p ≤
        S.indicator (fun l : ℤ => globalToLocalCoeff α l * P) l := by
    by_cases hl : l ∈ S
    · rw [Set.indicator_of_mem hl]
      exact mul_le_mul_right
        (ENNReal.rpow_le_rpow (enorm_dyadicSpatialInnerPiece_le f l x) hp.le) _
    · have hlt : l < j - 3 := by
        simpa only [S, mem_Ici, not_le] using hl
      rw [dyadicSpatialInnerPiece_eq_zero_of_shell_lt f hxj hlt]
      simp [S, hl, hp]
  calc
    (∑' l : ℤ, globalToLocalCoeff α l *
        ‖dyadicSpatialInnerPiece f l x‖ₑ ^ p) ≤
        ∑' l : ℤ, S.indicator (fun l : ℤ => globalToLocalCoeff α l * P) l :=
      ENNReal.tsum_le_tsum hterm
    _ = ∑' l : Ici (j - 3), globalToLocalCoeff α l * P := by
      symm
      simpa only [S, Set.mem_Ici] using
        (tsum_subtype (Ici (j - 3))
          (fun l : ℤ => globalToLocalCoeff α l * P))
    _ = (∑' l : Ici (j - 3), globalToLocalCoeff α l) * P := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ (globalToLocalHardyConstant α * globalToLocalCoeff α (j + 1)) * P := by
      exact mul_le_mul_left (globalToLocalCoeff_tail_le_hardy α j) _
    _ ≤ globalToLocalHardyConstant α * P * radialPowerWeight d α x := by
      have hw := globalToLocalCoeff_le_weight_of_mem_shell hα.le hxj
      calc
        (globalToLocalHardyConstant α * globalToLocalCoeff α (j + 1)) * P =
            globalToLocalHardyConstant α * P * globalToLocalCoeff α (j + 1) := by ring
        _ ≤ globalToLocalHardyConstant α * P * radialPowerWeight d α x :=
          mul_le_mul_right hw _

private theorem dyadicSpatialInner_hardy_integral {d : ℕ} (hd : 1 ≤ d)
    {p α : ℝ} (hp : 0 < p) (hα : α < 0)
    (f : SchwartzMap (Euclidean d) ℂ) :
    (∑' j : ℤ, globalToLocalCoeff α j *
      (∫⁻ x, ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p ∂volume)) ≤
      globalToLocalHardyConstant α *
        (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) := by
  have hmeas (j : ℤ) : AEMeasurable
      (fun x : Euclidean d => globalToLocalCoeff α j *
        ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p) volume := by
    apply (measurable_const.mul
      (ENNReal.continuous_rpow_const.measurable.comp
        (dyadicSpatialInnerPiece f j).continuous.enorm.measurable)).aemeasurable
  have hbase (j : ℤ) : Measurable
      (fun x : Euclidean d => ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp
      (dyadicSpatialInnerPiece f j).continuous.enorm.measurable
  calc
    (∑' j : ℤ, globalToLocalCoeff α j *
        (∫⁻ x, ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p ∂volume)) =
        ∑' j : ℤ, ∫⁻ x,
          globalToLocalCoeff α j * ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p ∂volume := by
      apply tsum_congr
      intro j
      rw [lintegral_const_mul (globalToLocalCoeff α j) (hbase j)]
    _ = (∫⁻ x, ∑' j : ℤ,
        globalToLocalCoeff α j * ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p ∂volume) :=
      (lintegral_tsum hmeas).symm
    _ ≤ ∫⁻ x, globalToLocalHardyConstant α * ‖f x‖ₑ ^ p *
          radialPowerWeight d α x ∂volume :=
      lintegral_mono_ae (ae_dyadicSpatialInner_hardy hd hp hα f)
    _ = globalToLocalHardyConstant α *
        (∫⁻ x, ‖f x‖ₑ ^ p * radialPowerWeight d α x ∂volume) := by
      have hprod : Measurable (fun x : Euclidean d =>
          ‖f x‖ₑ ^ p * radialPowerWeight d α x) :=
        (ENNReal.continuous_rpow_const.measurable.comp f.continuous.enorm.measurable).mul
          (measurable_radialPowerWeight d α)
      rw [show (fun x : Euclidean d =>
        globalToLocalHardyConstant α * ‖f x‖ₑ ^ p * radialPowerWeight d α x) =
          fun x => globalToLocalHardyConstant α *
            (‖f x‖ₑ ^ p * radialPowerWeight d α x) by
          funext x
          ring]
      rw [lintegral_const_mul (globalToLocalHardyConstant α) hprod]
    _ = globalToLocalHardyConstant α *
        (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) := by
      congr 1
      rw [powerWeightedVolume]
      symm
      calc
        (∫⁻ x, ‖f x‖ₑ ^ p ∂volume.withDensity (radialPowerWeight d α)) =
            ∫⁻ x, (radialPowerWeight d α x) * ‖f x‖ₑ ^ p ∂volume :=
          lintegral_withDensity_eq_lintegral_mul volume
            (measurable_radialPowerWeight d α)
            (ENNReal.continuous_rpow_const.measurable.comp f.continuous.enorm.measurable)
        _ = ∫⁻ x, ‖f x‖ₑ ^ p * radialPowerWeight d α x ∂volume := by
          apply lintegral_congr
          intro x
          ring

private theorem setLIntegral_mono_subset_globalToLocal
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ENNReal)
    {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) :
    (∫⁻ x in s, g x ∂μ) ≤ ∫⁻ x in t, g x ∂μ := by
  calc
    (∫⁻ x in s, g x ∂μ) = ∫⁻ x, s.indicator g x ∂μ :=
      (lintegral_indicator hs g).symm
    _ ≤ ∫⁻ x, t.indicator g x ∂μ :=
      lintegral_mono (indicator_le_indicator_of_subset hst (fun _ => bot_le))
    _ = ∫⁻ x in t, g x ∂μ := lintegral_indicator ht g

private theorem dyadicSpatialShell_subset_euclideanAnnulus {d : ℕ} (j : ℤ) :
    dyadicSpatialShell d j ⊆
      euclideanAnnulus d ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)) := by
  intro x hx
  constructor
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2
  · rw [Metric.mem_ball, dist_zero_right]
    exact not_lt.mpr hx.1.le

private theorem dyadicSpatialInner_shell_bound {d : ℕ} (E : Set ℝ) {p α : ℝ}
    (hp : 0 < p) (hα : α < 0) (U : ENNReal)
    (hU : ∀ g : SchwartzMap (Euclidean d) ℂ,
      eLpNorm (restrictedNormalizedSphericalMaximal d E (g : Euclidean d → ℂ))
        (ENNReal.ofReal p) volume ≤
        U * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p) volume)
    (f : SchwartzMap (Euclidean d) ℂ) (j : ℤ) :
    (∫⁻ x in dyadicSpatialShell d j,
      (restrictedNormalizedSphericalMaximal d E
        (dyadicSpatialInnerPiece f j : Euclidean d → ℂ) x) ^ p
        ∂powerWeightedVolume d α) ≤
      globalToLocalCoeff α j * U ^ p *
        (∫⁻ x, ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p ∂volume) := by
  let g : SchwartzMap (Euclidean d) ℂ := dyadicSpatialInnerPiece f j
  let M : Euclidean d → ENNReal :=
    restrictedNormalizedSphericalMaximal d E (g : Euclidean d → ℂ)
  have hMmeas : Measurable (fun x : Euclidean d => (M x) ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp
      (measurable_restrictedNormalizedSphericalMaximal E
        (g : Euclidean d → ℂ) g.continuous)
  have hMmoment : (∫⁻ x, (M x) ^ p ∂volume) ≤
      U ^ p * (∫⁻ x, ‖g x‖ₑ ^ p ∂volume) := by
    simpa only [M, enorm_eq_self] using
      (lintegral_enorm_rpow_le_of_eLpNorm_le volume hp U
        (restrictedNormalizedSphericalMaximal d E (g : Euclidean d → ℂ))
        (g : Euclidean d → ℂ) (hU g))
  have hR : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hann : MeasurableSet
      (euclideanAnnulus d ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1))) :=
    measurableSet_closedBall.diff measurableSet_ball
  calc
    (∫⁻ x in dyadicSpatialShell d j, (M x) ^ p ∂powerWeightedVolume d α) ≤
        ∫⁻ x in euclideanAnnulus d ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)),
          (M x) ^ p ∂powerWeightedVolume d α :=
      setLIntegral_mono_subset_globalToLocal _ _
        (measurableSet_dyadicSpatialShell d j) hann
        (dyadicSpatialShell_subset_euclideanAnnulus j)
    _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ j)) ^ α *
        (∫⁻ x in euclideanAnnulus d ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)),
          (M x) ^ p ∂volume) :=
      setLIntegral_powerWeightedVolume_euclideanAnnulus_le hα.le hR _ hMmeas
    _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ j)) ^ α *
        (∫⁻ x, (M x) ^ p ∂volume) := by
      simpa only [Measure.restrict_univ] using
        (mul_le_mul_right
          (setLIntegral_mono_subset_globalToLocal volume
            (fun x : Euclidean d => (M x) ^ p)
            hann MeasurableSet.univ (subset_univ _))
          ((ENNReal.ofReal ((2 : ℝ) ^ j)) ^ α))
    _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ j)) ^ α *
        (U ^ p * (∫⁻ x, ‖g x‖ₑ ^ p ∂volume)) :=
      mul_le_mul_right hMmoment _
    _ = globalToLocalCoeff α j * U ^ p *
        (∫⁻ x, ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p ∂volume) := by
      rw [← globalToLocalCoeff_eq_weight]
      dsimp [g]
      ring

private theorem memLp_dyadicSpatialAnnularPiece {d : ℕ} {q : ENNReal}
    {μ : Measure (Euclidean d)} (f : SchwartzMap (Euclidean d) ℂ) (k : ℤ)
    (hf : MemLp (f : Euclidean d → ℂ) q μ) :
    MemLp (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) q μ := by
  refine (hf.const_mul (2 : ℂ)).mono
    (dyadicSpatialAnnularPiece f k).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [show ‖((2 : ℂ) * f x)‖ = 2 * ‖f x‖ by
    norm_num [norm_mul]]
  exact norm_dyadicSpatialAnnularPiece_le_two_mul f k x

private theorem memLp_dyadicSpatialOuterAnnularPiece {d : ℕ} {q : ENNReal}
    {μ : Measure (Euclidean d)} (f : SchwartzMap (Euclidean d) ℂ) (j k : ℤ)
    (hf : MemLp (f : Euclidean d → ℂ) q μ) :
    MemLp (dyadicSpatialOuterAnnularPiece f j k : Euclidean d → ℂ) q μ := by
  refine (hf.const_mul (4 : ℂ)).mono
    (dyadicSpatialOuterAnnularPiece f j k).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [show ‖((4 : ℂ) * f x)‖ = 4 * ‖f x‖ by
    norm_num [norm_mul]]
  exact norm_dyadicSpatialOuterAnnularPiece_le_four_mul f j k x

private theorem tsum_physicalBlock_moments_le {d : ℕ} (E : Set ℝ) {p : ℝ}
    (μ : Measure (Euclidean d)) (hp : 0 < p) (A : ENNReal)
    (hblock : ∀ k : ℤ, ∀ g : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d,
        x ∉ euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3)) →
          g x = 0) →
      MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p) μ →
        eLpNorm (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (g : Euclidean d → ℂ)) (ENNReal.ofReal p) μ ≤
          A * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p) μ)
    (g : ℤ → SchwartzMap (Euclidean d) ℂ)
    (hg : ∀ k : ℤ, MemLp (g k : Euclidean d → ℂ) (ENNReal.ofReal p) μ)
    (hgsupport : ∀ k : ℤ, ∀ x : Euclidean d,
      x ∉ euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3)) →
        g k x = 0) :
    (∑' k : ℤ, ∫⁻ x,
      (restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (g k : Euclidean d → ℂ) x) ^ p ∂μ) ≤
      A ^ p * (∑' k : ℤ, ∫⁻ x, ‖g k x‖ₑ ^ p ∂μ) := by
  calc
    (∑' k : ℤ, ∫⁻ x,
        (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (g k : Euclidean d → ℂ) x) ^ p ∂μ) ≤
        ∑' k : ℤ, A ^ p * (∫⁻ x, ‖g k x‖ₑ ^ p ∂μ) := by
      apply ENNReal.tsum_le_tsum
      intro k
      simpa only [enorm_eq_self] using
        (lintegral_enorm_rpow_le_of_eLpNorm_le μ hp A
          (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (g k : Euclidean d → ℂ))
          (g k : Euclidean d → ℂ) (hblock k (g k) (hgsupport k) (hg k)))
    _ = A ^ p * (∑' k : ℤ, ∫⁻ x, ‖g k x‖ₑ ^ p ∂μ) :=
      ENNReal.tsum_mul_left

private theorem dyadicSpatialAnnular_input_sum {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (μ : Measure (Euclidean d))
    {p : ℝ} (hp : 0 < p) :
    (∑' k : ℤ, ∫⁻ x, ‖dyadicSpatialAnnularPiece f k x‖ₑ ^ p ∂μ) ≤
      ((ENNReal.ofReal 2) ^ p * 5) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) := by
  apply tsum_lintegral_enorm_rpow_le_of_dyadic_annular_cutoff_control f
    (fun k => dyadicSpatialAnnularPiece f k) μ hp (ENNReal.ofReal 2)
  · intro k x
    rw [← ofReal_norm, ← ofReal_norm (f x), ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal
      (norm_dyadicSpatialAnnularPiece_le_two_mul f k x)
  · intro k x hx
    rw [dyadicSpatialAnnularPiece_apply, hx, zero_mul]

private theorem dyadicSpatialOuterAnnular_input_sum {d : ℕ}
    (f : SchwartzMap (Euclidean d) ℂ) (s : ℤ) (μ : Measure (Euclidean d))
    {p : ℝ} (hp : 0 < p) :
    (∑' k : ℤ, ∫⁻ x,
      ‖dyadicSpatialOuterAnnularPiece f (k - s) k x‖ₑ ^ p ∂μ) ≤
      ((ENNReal.ofReal 4) ^ p * 5) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) := by
  apply tsum_lintegral_enorm_rpow_le_of_dyadic_annular_cutoff_control f
    (fun k => dyadicSpatialOuterAnnularPiece f (k - s) k) μ hp (ENNReal.ofReal 4)
  · intro k x
    rw [← ofReal_norm, ← ofReal_norm (f x), ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal
      (norm_dyadicSpatialOuterAnnularPiece_le_four_mul f (k - s) k x)
  · intro k x hx
    rw [dyadicSpatialOuterAnnularPiece_apply, hx, zero_mul]

private theorem dyadicSpatialOuter_shell_pointwise_bound {d : ℕ} (E : Set ℝ)
    (f : SchwartzMap (Euclidean d) ℂ) (j : ℤ) {x : Euclidean d}
    (hx : x ∈ dyadicSpatialShell d j) :
    restrictedNormalizedSphericalMaximal d E
      (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) x ≤
      (⨆ k : ℤ, restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) x) +
      (⨆ k : ℤ, restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (dyadicSpatialOuterAnnularPiece f (k - 2) k : Euclidean d → ℂ) x) +
      (⨆ k : ℤ, restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (dyadicSpatialOuterAnnularPiece f (k - 3) k : Euclidean d → ℂ) x) +
      (⨆ k : ℤ, restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (dyadicSpatialOuterAnnularPiece f (k - 4) k : Euclidean d → ℂ) x) := by
  rw [restrictedNormalizedSphericalMaximal_eq_iSup_dyadic_blocks]
  apply iSup_le
  intro k
  by_cases hsmall : k ≤ j + 1
  · rw [restrictedNormalizedSphericalMaximal_dyadic_block_outerPiece_eq_zero_on_shell
      E f j k hsmall hx]
    simp
  by_cases hfar : j + 5 ≤ k
  · rw [restrictedNormalizedSphericalMaximal_dyadic_block_outerPiece_eq_annularPiece
      E f j k hfar hx]
    calc
      restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) x ≤
          ⨆ k : ℤ, restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) x :=
        le_iSup (fun k : ℤ =>
          restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) x) k
      _ ≤ _ := le_add_of_nonneg_right bot_le |>.trans
        (le_add_of_nonneg_right bot_le) |>.trans (le_add_of_nonneg_right bot_le)
  have hlarge : j + 2 ≤ k := by omega
  have hcases : k = j + 2 ∨ k = j + 3 ∨ k = j + 4 := by omega
  rcases hcases with hk | hk | hk
  · rw [restrictedNormalizedSphericalMaximal_dyadic_block_outerPiece_eq_outerAnnularPiece
      E f j k hlarge hx]
    subst k
    have hterm := le_iSup (fun k : ℤ =>
      restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (dyadicSpatialOuterAnnularPiece f (k - 2) k : Euclidean d → ℂ) x) (j + 2)
    have hsub : (j + 2 : ℤ) - 2 = j := by omega
    rw [hsub] at hterm
    exact (le_add_of_le_right hterm).trans
      ((le_add_of_nonneg_right bot_le).trans (le_add_of_nonneg_right bot_le))
  · rw [restrictedNormalizedSphericalMaximal_dyadic_block_outerPiece_eq_outerAnnularPiece
      E f j k hlarge hx]
    subst k
    have hterm := le_iSup (fun k : ℤ =>
      restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (dyadicSpatialOuterAnnularPiece f (k - 3) k : Euclidean d → ℂ) x) (j + 3)
    have hsub : (j + 3 : ℤ) - 3 = j := by omega
    rw [hsub] at hterm
    exact (le_add_of_le_right hterm).trans (le_add_of_nonneg_right bot_le)
  · rw [restrictedNormalizedSphericalMaximal_dyadic_block_outerPiece_eq_outerAnnularPiece
      E f j k hlarge hx]
    subst k
    have hterm := le_iSup (fun k : ℤ =>
      restrictedNormalizedSphericalMaximal d
        (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
        (dyadicSpatialOuterAnnularPiece f (k - 4) k : Euclidean d → ℂ) x) (j + 4)
    have hsub : (j + 4 : ℤ) - 4 = j := by omega
    rw [hsub] at hterm
    exact le_add_of_le_right hterm

private theorem rpow_four_sum_le (a b c d : ENNReal) {p : ℝ} (hp : 1 ≤ p) :
    (a + b + c + d) ^ p ≤
      (2 ^ (p - 1) * 2 ^ (p - 1)) * (a ^ p + b ^ p + c ^ p + d ^ p) := by
  let q : ENNReal := 2 ^ (p - 1)
  have hab := ENNReal.rpow_add_le_mul_rpow_add_rpow a b hp
  have hcd := ENNReal.rpow_add_le_mul_rpow_add_rpow c d hp
  have hpairs := ENNReal.rpow_add_le_mul_rpow_add_rpow (a + b) (c + d) hp
  change (a + b + c + d) ^ p ≤ (q * q) * (a ^ p + b ^ p + c ^ p + d ^ p)
  calc
    (a + b + c + d) ^ p = ((a + b) + (c + d)) ^ p := by ring
    _ ≤ q * ((a + b) ^ p + (c + d) ^ p) := hpairs
    _ ≤ q * (q * (a ^ p + b ^ p) + q * (c ^ p + d ^ p)) := by
      apply mul_le_mul_right
      exact add_le_add hab hcd
    _ = (q * q) * (a ^ p + b ^ p + c ^ p + d ^ p) := by ring

private theorem dyadicSpatialOuter_shell_moment_bound {d : ℕ} (hd : 1 ≤ d)
    (E : Set ℝ) {p α : ℝ} (hp : 1 ≤ p)
    (f : SchwartzMap (Euclidean d) ℂ) :
    (∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j,
      (restrictedNormalizedSphericalMaximal d E
        (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) x) ^ p
        ∂powerWeightedVolume d α) ≤
      (2 ^ (p - 1) * 2 ^ (p - 1)) *
        ((∑' k : ℤ, ∫⁻ x,
          (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) x) ^ p
            ∂powerWeightedVolume d α) +
        ((∑' k : ℤ, ∫⁻ x,
          (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (dyadicSpatialOuterAnnularPiece f (k - 2) k : Euclidean d → ℂ) x) ^ p
            ∂powerWeightedVolume d α) +
        ((∑' k : ℤ, ∫⁻ x,
          (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (dyadicSpatialOuterAnnularPiece f (k - 3) k : Euclidean d → ℂ) x) ^ p
            ∂powerWeightedVolume d α) +
        (∑' k : ℤ, ∫⁻ x,
          (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (dyadicSpatialOuterAnnularPiece f (k - 4) k : Euclidean d → ℂ) x) ^ p
            ∂powerWeightedVolume d α)))) := by
  let μ : Measure (Euclidean d) := powerWeightedVolume d α
  let B0 : ℤ → Euclidean d → ENNReal := fun k x =>
    restrictedNormalizedSphericalMaximal d
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
      (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) x
  let B2 : ℤ → Euclidean d → ENNReal := fun k x =>
    restrictedNormalizedSphericalMaximal d
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
      (dyadicSpatialOuterAnnularPiece f (k - 2) k : Euclidean d → ℂ) x
  let B3 : ℤ → Euclidean d → ENNReal := fun k x =>
    restrictedNormalizedSphericalMaximal d
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
      (dyadicSpatialOuterAnnularPiece f (k - 3) k : Euclidean d → ℂ) x
  let B4 : ℤ → Euclidean d → ENNReal := fun k x =>
    restrictedNormalizedSphericalMaximal d
      (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
      (dyadicSpatialOuterAnnularPiece f (k - 4) k : Euclidean d → ℂ) x
  let H0 : Euclidean d → ENNReal := fun x => ⨆ k : ℤ, B0 k x
  let H2 : Euclidean d → ENNReal := fun x => ⨆ k : ℤ, B2 k x
  let H3 : Euclidean d → ENNReal := fun x => ⨆ k : ℤ, B3 k x
  let H4 : Euclidean d → ENNReal := fun x => ⨆ k : ℤ, B4 k x
  let S : Euclidean d → ENNReal := fun x => H0 x + H2 x + H3 x + H4 x
  have hBmeas0 (k : ℤ) : Measurable (B0 k) := by
    dsimp [B0]
    exact measurable_restrictedNormalizedSphericalMaximal _ _
      (dyadicSpatialAnnularPiece f k).continuous
  have hBmeas2 (k : ℤ) : Measurable (B2 k) := by
    dsimp [B2]
    exact measurable_restrictedNormalizedSphericalMaximal _ _
      (dyadicSpatialOuterAnnularPiece f (k - 2) k).continuous
  have hBmeas3 (k : ℤ) : Measurable (B3 k) := by
    dsimp [B3]
    exact measurable_restrictedNormalizedSphericalMaximal _ _
      (dyadicSpatialOuterAnnularPiece f (k - 3) k).continuous
  have hBmeas4 (k : ℤ) : Measurable (B4 k) := by
    dsimp [B4]
    exact measurable_restrictedNormalizedSphericalMaximal _ _
      (dyadicSpatialOuterAnnularPiece f (k - 4) k).continuous
  have hHmeas0 : Measurable H0 := Measurable.iSup hBmeas0
  have hHmeas2 : Measurable H2 := Measurable.iSup hBmeas2
  have hHmeas3 : Measurable H3 := Measurable.iSup hBmeas3
  have hHmeas4 : Measurable H4 := Measurable.iSup hBmeas4
  have hHpow0 : Measurable (fun x => H0 x ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hHmeas0
  have hHpow2 : Measurable (fun x => H2 x ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hHmeas2
  have hHpow3 : Measurable (fun x => H3 x ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hHmeas3
  have hHpow4 : Measurable (fun x => H4 x ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hHmeas4
  have houter (j : ℤ) {x : Euclidean d} (hx : x ∈ dyadicSpatialShell d j) :
      restrictedNormalizedSphericalMaximal d E
        (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) x ≤ S x := by
    simpa only [B0, B2, B3, B4, H0, H2, H3, H4, S] using
      dyadicSpatialOuter_shell_pointwise_bound E f j hx
  have hshell (j : ℤ) :
      (∫⁻ x in dyadicSpatialShell d j,
        (restrictedNormalizedSphericalMaximal d E
          (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) x) ^ p ∂μ) ≤
        ∫⁻ x in dyadicSpatialShell d j, (S x) ^ p ∂μ := by
    apply setLIntegral_mono' (measurableSet_dyadicSpatialShell d j)
    intro x hx
    exact ENNReal.rpow_le_rpow (houter j hx) (by linarith)
  have hSpow (x : Euclidean d) : (S x) ^ p ≤
      (2 ^ (p - 1) * 2 ^ (p - 1)) *
        (H0 x ^ p + (H2 x ^ p + (H3 x ^ p + H4 x ^ p))) := by
    dsimp [S]
    simpa only [add_assoc] using rpow_four_sum_le (H0 x) (H2 x) (H3 x) (H4 x) hp
  have hTmeas : Measurable (fun x : Euclidean d =>
      H0 x ^ p + (H2 x ^ p + (H3 x ^ p + H4 x ^ p))) :=
    hHpow0.add (hHpow2.add (hHpow3.add hHpow4))
  have hintegral :
      (∫⁻ x, (2 ^ (p - 1) * 2 ^ (p - 1)) *
        (H0 x ^ p + (H2 x ^ p + (H3 x ^ p + H4 x ^ p))) ∂μ) =
        (2 ^ (p - 1) * 2 ^ (p - 1)) *
          ((∫⁻ x, H0 x ^ p ∂μ) +
            ((∫⁻ x, H2 x ^ p ∂μ) +
              ((∫⁻ x, H3 x ^ p ∂μ) + (∫⁻ x, H4 x ^ p ∂μ)))) := by
    rw [lintegral_const_mul _ hTmeas,
      lintegral_add_left hHpow0,
      lintegral_add_left hHpow2,
      lintegral_add_left hHpow3]
  have hH0 : (∫⁻ x, H0 x ^ p ∂μ) ≤ ∑' k : ℤ, ∫⁻ x, (B0 k x) ^ p ∂μ :=
    lintegral_iSup_rpow_le_tsum_lintegral_rpow μ B0 p (by linarith)
      (fun k => (hBmeas0 k).aemeasurable)
  have hH2 : (∫⁻ x, H2 x ^ p ∂μ) ≤ ∑' k : ℤ, ∫⁻ x, (B2 k x) ^ p ∂μ :=
    lintegral_iSup_rpow_le_tsum_lintegral_rpow μ B2 p (by linarith)
      (fun k => (hBmeas2 k).aemeasurable)
  have hH3 : (∫⁻ x, H3 x ^ p ∂μ) ≤ ∑' k : ℤ, ∫⁻ x, (B3 k x) ^ p ∂μ :=
    lintegral_iSup_rpow_le_tsum_lintegral_rpow μ B3 p (by linarith)
      (fun k => (hBmeas3 k).aemeasurable)
  have hH4 : (∫⁻ x, H4 x ^ p ∂μ) ≤ ∑' k : ℤ, ∫⁻ x, (B4 k x) ^ p ∂μ :=
    lintegral_iSup_rpow_le_tsum_lintegral_rpow μ B4 p (by linarith)
      (fun k => (hBmeas4 k).aemeasurable)
  calc
    (∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j,
        (restrictedNormalizedSphericalMaximal d E
          (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) x) ^ p ∂μ) ≤
        ∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j, (S x) ^ p ∂μ :=
      ENNReal.tsum_le_tsum hshell
    _ = ∫⁻ x, (S x) ^ p ∂μ :=
      (lintegral_eq_tsum_setLIntegral_dyadicSpatialShell hd α
        (fun x => (S x) ^ p)).symm
    _ ≤ ∫⁻ x, (2 ^ (p - 1) * 2 ^ (p - 1)) *
        (H0 x ^ p + (H2 x ^ p + (H3 x ^ p + H4 x ^ p))) ∂μ :=
      lintegral_mono hSpow
    _ = (2 ^ (p - 1) * 2 ^ (p - 1)) *
        ((∫⁻ x, H0 x ^ p ∂μ) +
          ((∫⁻ x, H2 x ^ p ∂μ) +
            ((∫⁻ x, H3 x ^ p ∂μ) + (∫⁻ x, H4 x ^ p ∂μ)))) := hintegral
    _ ≤ (2 ^ (p - 1) * 2 ^ (p - 1)) *
        ((∑' k : ℤ, ∫⁻ x, (B0 k x) ^ p ∂μ) +
          ((∑' k : ℤ, ∫⁻ x, (B2 k x) ^ p ∂μ) +
            ((∑' k : ℤ, ∫⁻ x, (B3 k x) ^ p ∂μ) +
              (∑' k : ℤ, ∫⁻ x, (B4 k x) ^ p ∂μ)))) := by
      apply mul_le_mul_right
      exact add_le_add hH0 (add_le_add hH2 (add_le_add hH3 hH4))
    _ = _ := by
      simp only [μ, B0, B2, B3, B4]

private theorem dyadicSpatialInner_shell_moment_bound {d : ℕ} (E : Set ℝ)
    (hd : 1 ≤ d) {p α : ℝ} (hp : 1 ≤ p) (hα : α < 0) (U : ENNReal)
    (hU : ∀ g : SchwartzMap (Euclidean d) ℂ,
      eLpNorm (restrictedNormalizedSphericalMaximal d E (g : Euclidean d → ℂ))
        (ENNReal.ofReal p) volume ≤
        U * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p) volume)
    (f : SchwartzMap (Euclidean d) ℂ) :
    (∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j,
      (restrictedNormalizedSphericalMaximal d E
        (dyadicSpatialInnerPiece f j : Euclidean d → ℂ) x) ^ p
        ∂powerWeightedVolume d α) ≤
      U ^ p * globalToLocalHardyConstant α *
        (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) := by
  have hpsum : 0 < p := lt_of_lt_of_le zero_lt_one hp
  calc
    (∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j,
        (restrictedNormalizedSphericalMaximal d E
          (dyadicSpatialInnerPiece f j : Euclidean d → ℂ) x) ^ p
          ∂powerWeightedVolume d α) ≤
        ∑' j : ℤ, globalToLocalCoeff α j * U ^ p *
          (∫⁻ x, ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p ∂volume) := by
      apply ENNReal.tsum_le_tsum
      intro j
      exact dyadicSpatialInner_shell_bound E hpsum hα U hU f j
    _ = U ^ p * (∑' j : ℤ, globalToLocalCoeff α j *
        (∫⁻ x, ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p ∂volume)) := by
      have hrew :
          (fun j : ℤ => globalToLocalCoeff α j * U ^ p *
            (∫⁻ x, ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p ∂volume)) =
            fun j : ℤ => U ^ p * (globalToLocalCoeff α j *
              (∫⁻ x, ‖dyadicSpatialInnerPiece f j x‖ₑ ^ p ∂volume)) := by
        funext j
        ring
      rw [hrew, ENNReal.tsum_mul_left]
    _ ≤ U ^ p * (globalToLocalHardyConstant α *
        (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α)) :=
      mul_le_mul_right (dyadicSpatialInner_hardy_integral hd hpsum hα f) _
    _ = U ^ p * globalToLocalHardyConstant α *
        (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) := by ring

private def globalToLocalOuterMomentConstant (p : ℝ) (A : ENNReal) : ENNReal :=
  (2 ^ (p - 1) * 2 ^ (p - 1)) *
    (A ^ p * ((ENNReal.ofReal 2) ^ p * 5) +
      (A ^ p * ((ENNReal.ofReal 4) ^ p * 5) +
      (A ^ p * ((ENNReal.ofReal 4) ^ p * 5) +
        A ^ p * ((ENNReal.ofReal 4) ^ p * 5))))

private theorem dyadicSpatialOuter_shell_moment_bound_of_local {d : ℕ}
    (hd : 1 ≤ d) (E : Set ℝ) {p α : ℝ} (hp : 1 ≤ p) (A : ENNReal)
    (hblock : ∀ k : ℤ, ∀ g : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d,
        x ∉ euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3)) →
          g x = 0) →
      MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p)
          (powerWeightedVolume d α) →
        eLpNorm (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (g : Euclidean d → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume d α) ≤
          A * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p)
            (powerWeightedVolume d α))
    (f : SchwartzMap (Euclidean d) ℂ)
    (hf : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume d α)) :
    (∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j,
      (restrictedNormalizedSphericalMaximal d E
        (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) x) ^ p
        ∂powerWeightedVolume d α) ≤
      globalToLocalOuterMomentConstant p A *
        (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) := by
  have hpsum : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h0 := tsum_physicalBlock_moments_le E
    (powerWeightedVolume d α) hpsum A hblock
    (fun k => dyadicSpatialAnnularPiece f k)
    (fun k => memLp_dyadicSpatialAnnularPiece f k hf)
    (fun k x hx =>
      dyadicSpatialAnnularPiece_eq_zero_of_not_mem_bufferedAnnulus f k hx)
  have h0' :
      (∑' k : ℤ, ∫⁻ x,
        (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) x) ^ p
          ∂powerWeightedVolume d α) ≤
        A ^ p * ((ENNReal.ofReal 2) ^ p * 5) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) := by
    calc
      _ ≤ A ^ p * (∑' k : ℤ, ∫⁻ x,
          ‖dyadicSpatialAnnularPiece f k x‖ₑ ^ p ∂powerWeightedVolume d α) := h0
      _ ≤ A ^ p * (((ENNReal.ofReal 2) ^ p * 5) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α)) := by
        exact mul_le_mul_right (dyadicSpatialAnnular_input_sum f
          (powerWeightedVolume d α) hpsum) _
      _ = _ := by ring
  have hshift (s : ℤ) :
      (∑' k : ℤ, ∫⁻ x,
        (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (dyadicSpatialOuterAnnularPiece f (k - s) k : Euclidean d → ℂ) x) ^ p
          ∂powerWeightedVolume d α) ≤
        A ^ p * ((ENNReal.ofReal 4) ^ p * 5) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) := by
    calc
      _ ≤ A ^ p * (∑' k : ℤ, ∫⁻ x,
          ‖dyadicSpatialOuterAnnularPiece f (k - s) k x‖ₑ ^ p
            ∂powerWeightedVolume d α) :=
        tsum_physicalBlock_moments_le E
          (powerWeightedVolume d α) hpsum A hblock
          (fun k => dyadicSpatialOuterAnnularPiece f (k - s) k)
          (fun k => memLp_dyadicSpatialOuterAnnularPiece f (k - s) k hf)
          (fun k x hx =>
            dyadicSpatialOuterAnnularPiece_eq_zero_of_not_mem_bufferedAnnulus f (k - s) k hx)
      _ ≤ A ^ p * (((ENNReal.ofReal 4) ^ p * 5) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α)) := by
        exact mul_le_mul_right (dyadicSpatialOuterAnnular_input_sum f s
          (powerWeightedVolume d α) hpsum) _
      _ = _ := by ring
  calc
    _ ≤ (2 ^ (p - 1) * 2 ^ (p - 1)) *
        ((∑' k : ℤ, ∫⁻ x,
          (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (dyadicSpatialAnnularPiece f k : Euclidean d → ℂ) x) ^ p
            ∂powerWeightedVolume d α) +
        ((∑' k : ℤ, ∫⁻ x,
          (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (dyadicSpatialOuterAnnularPiece f (k - 2) k : Euclidean d → ℂ) x) ^ p
            ∂powerWeightedVolume d α) +
        ((∑' k : ℤ, ∫⁻ x,
          (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (dyadicSpatialOuterAnnularPiece f (k - 3) k : Euclidean d → ℂ) x) ^ p
            ∂powerWeightedVolume d α) +
        (∑' k : ℤ, ∫⁻ x,
          (restrictedNormalizedSphericalMaximal d
            (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
            (dyadicSpatialOuterAnnularPiece f (k - 4) k : Euclidean d → ℂ) x) ^ p
            ∂powerWeightedVolume d α)))) :=
      dyadicSpatialOuter_shell_moment_bound hd E hp f
    _ ≤ (2 ^ (p - 1) * 2 ^ (p - 1)) *
        (A ^ p * ((ENNReal.ofReal 2) ^ p * 5) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) +
        (A ^ p * ((ENNReal.ofReal 4) ^ p * 5) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) +
        (A ^ p * ((ENNReal.ofReal 4) ^ p * 5) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) +
        A ^ p * ((ENNReal.ofReal 4) ^ p * 5) *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α)))) := by
      apply mul_le_mul_right
      exact add_le_add h0' (add_le_add (hshift 2) (add_le_add (hshift 3) (hshift 4)))
    _ = _ := by
      unfold globalToLocalOuterMomentConstant
      ring

private def globalToLocalMomentConstant (p α : ℝ) (U A : ENNReal) : ENNReal :=
  (2 ^ (p - 1)) *
    (U ^ p * globalToLocalHardyConstant α + globalToLocalOuterMomentConstant p A)

private theorem globalToLocal_moment_bound_of_unweighted_and_local {d : ℕ}
    (hd : 1 ≤ d) (E : Set ℝ) {p α : ℝ} (hp : 1 ≤ p) (hα : α < 0)
    (U A : ENNReal)
    (hU : ∀ g : SchwartzMap (Euclidean d) ℂ,
      eLpNorm (restrictedNormalizedSphericalMaximal d E (g : Euclidean d → ℂ))
        (ENNReal.ofReal p) volume ≤
        U * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p) volume)
    (hblock : ∀ k : ℤ, ∀ g : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d,
        x ∉ euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3)) →
          g x = 0) →
      MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p)
          (powerWeightedVolume d α) →
        eLpNorm (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (g : Euclidean d → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume d α) ≤
          A * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p)
            (powerWeightedVolume d α))
    (f : SchwartzMap (Euclidean d) ℂ)
    (hf : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume d α)) :
    (∫⁻ x, (restrictedNormalizedSphericalMaximal d E
      (f : Euclidean d → ℂ) x) ^ p ∂powerWeightedVolume d α) ≤
      globalToLocalMomentConstant p α U A *
        (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α) := by
  let μ : Measure (Euclidean d) := powerWeightedVolume d α
  let M : Euclidean d → ENNReal :=
    restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ)
  let I : ℤ → Euclidean d → ENNReal := fun j =>
    restrictedNormalizedSphericalMaximal d E
      (dyadicSpatialInnerPiece f j : Euclidean d → ℂ)
  let O : ℤ → Euclidean d → ENNReal := fun j =>
    restrictedNormalizedSphericalMaximal d E
      (dyadicSpatialOuterPiece f j : Euclidean d → ℂ)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hImeas (j : ℤ) : Measurable (fun x => (I j x) ^ p) := by
    exact ENNReal.continuous_rpow_const.measurable.comp
      (measurable_restrictedNormalizedSphericalMaximal E
        (dyadicSpatialInnerPiece f j : Euclidean d → ℂ)
        (dyadicSpatialInnerPiece f j).continuous)
  have hOmeas (j : ℤ) : Measurable (fun x => (O j x) ^ p) := by
    exact ENNReal.continuous_rpow_const.measurable.comp
      (measurable_restrictedNormalizedSphericalMaximal E
        (dyadicSpatialOuterPiece f j : Euclidean d → ℂ)
        (dyadicSpatialOuterPiece f j).continuous)
  have hsplit (j : ℤ) : (f : Euclidean d → ℂ) =
      (dyadicSpatialInnerPiece f j : Euclidean d → ℂ) +
        (dyadicSpatialOuterPiece f j : Euclidean d → ℂ) := by
    funext x
    change f x = dyadicSpatialInnerPiece f j x +
      (f x - dyadicSpatialInnerPiece f j x)
    ring
  have hpoint (j : ℤ) (x : Euclidean d) : M x ≤ I j x + O j x := by
    dsimp [M, I, O]
    rw [hsplit j]
    exact restrictedNormalizedSphericalMaximal_add_le E
      (dyadicSpatialInnerPiece f j : Euclidean d → ℂ)
      (dyadicSpatialOuterPiece f j : Euclidean d → ℂ)
      (dyadicSpatialInnerPiece f j).continuous
      (dyadicSpatialOuterPiece f j).continuous x
  have hpow (j : ℤ) (x : Euclidean d) : (M x) ^ p ≤
      (2 ^ (p - 1)) * ((I j x) ^ p + (O j x) ^ p) := by
    calc
      (M x) ^ p ≤ (I j x + O j x) ^ p :=
        ENNReal.rpow_le_rpow (hpoint j x) hp0.le
      _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
  have hshell (j : ℤ) :
      (∫⁻ x in dyadicSpatialShell d j, (M x) ^ p ∂μ) ≤
        ∫⁻ x in dyadicSpatialShell d j,
          (2 ^ (p - 1)) * ((I j x) ^ p + (O j x) ^ p) ∂μ := by
    apply setLIntegral_mono' (measurableSet_dyadicSpatialShell d j)
    intro x hx
    exact hpow j x
  have hterm (j : ℤ) :
      (∫⁻ x in dyadicSpatialShell d j,
        (2 ^ (p - 1)) * ((I j x) ^ p + (O j x) ^ p) ∂μ) =
        (2 ^ (p - 1)) *
          ((∫⁻ x in dyadicSpatialShell d j, (I j x) ^ p ∂μ) +
          (∫⁻ x in dyadicSpatialShell d j, (O j x) ^ p ∂μ)) := by
    change (∫⁻ x, (2 ^ (p - 1)) *
        ((fun x => (I j x) ^ p) + fun x => (O j x) ^ p) x
        ∂μ.restrict (dyadicSpatialShell d j)) =
      (2 ^ (p - 1)) *
        ((∫⁻ x, (I j x) ^ p ∂μ.restrict (dyadicSpatialShell d j)) +
        (∫⁻ x, (O j x) ^ p ∂μ.restrict (dyadicSpatialShell d j)))
    rw [lintegral_const_mul _ ((hImeas j).add (hOmeas j))]
    congr 1
    simpa only [Pi.add_apply] using
      (lintegral_add_left (μ := μ.restrict (dyadicSpatialShell d j))
        (hImeas j) (fun x => (O j x) ^ p))
  have hsumterm :
      (∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j,
        (2 ^ (p - 1)) * ((I j x) ^ p + (O j x) ^ p) ∂μ) =
        (2 ^ (p - 1)) *
          ((∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j, (I j x) ^ p ∂μ) +
          (∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j, (O j x) ^ p ∂μ)) := by
    have hrew :
        (fun j : ℤ => ∫⁻ x in dyadicSpatialShell d j,
          (2 ^ (p - 1)) * ((I j x) ^ p + (O j x) ^ p) ∂μ) =
          fun j : ℤ => (2 ^ (p - 1)) *
            ((∫⁻ x in dyadicSpatialShell d j, (I j x) ^ p ∂μ) +
            (∫⁻ x in dyadicSpatialShell d j, (O j x) ^ p ∂μ)) := by
      funext j
      exact hterm j
    rw [hrew, ENNReal.tsum_mul_left, ENNReal.tsum_add]
  have hinner :
      (∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j, (I j x) ^ p ∂μ) ≤
        U ^ p * globalToLocalHardyConstant α *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) := by
    simpa only [I, μ] using
      dyadicSpatialInner_shell_moment_bound E hd hp hα U hU f
  have houter :
      (∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j, (O j x) ^ p ∂μ) ≤
        globalToLocalOuterMomentConstant p A *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) := by
    simpa only [O, μ] using
      dyadicSpatialOuter_shell_moment_bound_of_local hd E hp A hblock f hf
  calc
    (∫⁻ x, (restrictedNormalizedSphericalMaximal d E
        (f : Euclidean d → ℂ) x) ^ p ∂powerWeightedVolume d α) =
        ∫⁻ x, (M x) ^ p ∂μ := by rfl
    _ = ∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j, (M x) ^ p ∂μ :=
      lintegral_eq_tsum_setLIntegral_dyadicSpatialShell hd α _
    _ ≤ ∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j,
        (2 ^ (p - 1)) * ((I j x) ^ p + (O j x) ^ p) ∂μ :=
      ENNReal.tsum_le_tsum hshell
    _ = (2 ^ (p - 1)) *
        ((∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j, (I j x) ^ p ∂μ) +
        (∑' j : ℤ, ∫⁻ x in dyadicSpatialShell d j, (O j x) ^ p ∂μ)) := hsumterm
    _ ≤ (2 ^ (p - 1)) *
        (U ^ p * globalToLocalHardyConstant α *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) +
        globalToLocalOuterMomentConstant p A *
          (∫⁻ x, ‖f x‖ₑ ^ p ∂μ)) := by
      apply mul_le_mul_right
      exact add_le_add hinner houter
    _ = globalToLocalMomentConstant p α U A *
        (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) := by
      unfold globalToLocalMomentConstant
      ring
    _ = _ := by rfl

private theorem globalToLocalHardyConstant_ne_top {α : ℝ} (hα : α < 0) :
    globalToLocalHardyConstant α ≠ ∞ := by
  have hq : ENNReal.ofReal ((2 : ℝ) ^ α) < 1 := by
    rw [← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr ?_
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hα
  unfold globalToLocalHardyConstant
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ENNReal.inv_ne_top.mpr
  exact ne_of_gt (tsub_pos_iff_lt.mpr hq)

private theorem globalToLocalOuterMomentConstant_ne_top {p : ℝ} {A : ENNReal}
    (hp : 0 ≤ p) (hA : A ≠ ∞) :
    globalToLocalOuterMomentConstant p A ≠ ∞ := by
  unfold globalToLocalOuterMomentConstant
  finiteness

private theorem globalToLocalMomentConstant_ne_top {p α : ℝ} {U A : ENNReal}
    (hp : 0 ≤ p) (hα : α < 0) (hU : U ≠ ∞) (hA : A ≠ ∞) :
    globalToLocalMomentConstant p α U A ≠ ∞ := by
  unfold globalToLocalMomentConstant
  finiteness [globalToLocalHardyConstant_ne_top hα,
    globalToLocalOuterMomentConstant_ne_top hp hA]

private theorem hasStrongType_of_moment_bound_globalToLocal
    {d : ℕ} (E : Set ℝ) {p α : ℝ} (hp : 1 ≤ p) (K : ENNReal)
    (hK : K ≠ ∞)
    (hmoment : ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α) →
        (∫⁻ x, (restrictedNormalizedSphericalMaximal d E
          (f : Euclidean d → ℂ) x) ^ p ∂powerWeightedVolume d α) ≤
          K * (∫⁻ x, ‖f x‖ₑ ^ p ∂powerWeightedVolume d α)) :
    HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p α := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let L : ENNReal := K ^ (1 / p)
  refine ⟨1 + L.toReal,
    add_pos_of_pos_of_nonneg zero_lt_one ENNReal.toReal_nonneg, ?_⟩
  intro f hf
  let μ : Measure (Euclidean d) := powerWeightedVolume d α
  let M : Euclidean d → ENNReal :=
    restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ)
  let I : ENNReal := ∫⁻ x, ‖f x‖ₑ ^ p ∂μ
  let J : ENNReal := ∫⁻ x, (M x) ^ p ∂μ
  have hIlt : I < ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := μ) (f := (f : Euclidean d → ℂ))
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top hf.2
    simpa only [I, ENNReal.toReal_ofReal hp0.le] using h
  have hJle : J ≤ K * I := by
    simpa only [J, I, M, μ] using hmoment f hf
  have hJlt : J < ∞ :=
    hJle.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) hIlt)
  have hMmeas : Measurable M := by
    dsimp [M]
    exact measurable_restrictedNormalizedSphericalMaximal E
      (f : Euclidean d → ℂ) f.continuous
  have hMmem : MemLp M (ENNReal.ofReal p) μ := by
    refine ⟨hMmeas.aestronglyMeasurable, ?_⟩
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (μ := μ) (f := M) (ENNReal.ofReal_ne_zero_iff.mpr hp0)
      ENNReal.ofReal_ne_top).mpr
    simpa only [ENNReal.toReal_ofReal hp0.le, enorm_eq_self] using hJlt
  have hfNorm : eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) μ =
      I ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal hp0.le, I]
  have hMnorm : eLpNorm M (ENNReal.ofReal p) μ ≤
      L * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) μ := by
    rw [eLpNorm_ennreal_eq_lintegral_rpow μ M p hp0]
    calc
      J ^ (1 / p) ≤ (K * I) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hJle (one_div_nonneg.mpr hp0.le)
      _ = K ^ (1 / p) * I ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0.le)
      _ = L * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) μ := by
        rw [← hfNorm]
  have hLtop : L ≠ ∞ := by
    dsimp [L]
    exact ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hp0.le) hK
  have hLbound : L ≤ ENNReal.ofReal (1 + L.toReal) := by
    rw [ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_toReal hLtop]
    exact le_add_of_nonneg_left bot_le
  refine ⟨?_, ?_⟩
  · simpa only [M, μ] using hMmem
  · calc
      eLpNorm (restrictedNormalizedSphericalMaximal d E
          (f : Euclidean d → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume d α) = eLpNorm M (ENNReal.ofReal p) μ := by rfl
      _ ≤ L * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) μ := hMnorm
      _ ≤ ENNReal.ofReal (1 + L.toReal) *
          eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) μ :=
        by simpa only [mul_comm] using
          (mul_le_mul_right hLbound
            (eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) μ))
      _ = _ := by rfl

/-- The `α < 0` global-to-local reduction (Lemma 2.1): a global unweighted
estimate, together with a uniform weighted estimate on every normalized
radius block, implies the global weighted estimate. -/
theorem hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_uniform_normalized_local_and_unweighted
    {d : ℕ} (hd : 1 ≤ d) (E : Set ℝ) {p α C : ℝ}
    (hp : 1 ≤ p) (hα : α < 0)
    (hunweighted : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p 0)
    (hlocal : ∀ R : ℝ, 0 < R → ∀ g : SchwartzMap (Euclidean d) ℂ,
      MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α) →
        MemLp (restrictedNormalizedSphericalMaximal d
          (normalizedRadiusBlock E R) (g : Euclidean d → ℂ))
          (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
        eLpNorm (restrictedNormalizedSphericalMaximal d
          (normalizedRadiusBlock E R) (g : Euclidean d → ℂ))
          (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
          ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume d α)) :
    HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p α := by
  rcases (hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_zero_iff d E p).mp
      hunweighted with ⟨U, _hUpos, hU⟩
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hUbound (g : SchwartzMap (Euclidean d) ℂ) :
      eLpNorm (restrictedNormalizedSphericalMaximal d E (g : Euclidean d → ℂ))
        (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal U * eLpNorm (g : Euclidean d → ℂ)
          (ENNReal.ofReal p) volume :=
    (hU g (g.memLp (ENNReal.ofReal p) volume)).2
  have hphysical (k : ℤ) : ∀ g : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d,
        x ∉ euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3)) →
          g x = 0) →
      MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p)
          (powerWeightedVolume d α) →
        eLpNorm (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (g : Euclidean d → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume d α) ≤
          ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    have hR : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hshift : 2 * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      ring
    have h := restrictedNormalizedSphericalMaximal_block_bound_of_normalized
      hd hp0 hR (C := C) (hlocal ((2 : ℝ) ^ k) hR)
    rw [hshift] at h
    intro g _hgSupport hg
    exact (h g hg).2
  let K : ENNReal := globalToLocalMomentConstant p α (ENNReal.ofReal U) (ENNReal.ofReal C)
  refine hasStrongType_of_moment_bound_globalToLocal E hp K ?_ ?_
  · dsimp [K]
    exact globalToLocalMomentConstant_ne_top hp0.le hα ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top
  · intro f hf
    exact globalToLocal_moment_bound_of_unweighted_and_local hd E hp hα
      (ENNReal.ofReal U) (ENNReal.ofReal C) hUbound hphysical f hf

/-- The buffered finite-cutoff form of the negative global-to-local
reduction.  The cutoff hypothesis is used only after a dyadic spatial piece
has been pulled back to the fixed annulus `[1/4,8]`; Fatou then produces the
actual normalized maximal estimate before the spatial-shell reassembly. -/
theorem hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_uniform_normalized_buffered_relativeCutoff_and_unweighted
    {d : ℕ} (hd : 1 ≤ d) (E : Set ℝ) {p α : ℝ}
    (hp : 1 ≤ p) (hα : α < 0)
    (hunweighted : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p 0)
    (phi : SchwartzMap (Euclidean d) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (A : ENNReal) (hAtop : A ≠ ∞)
    (hfinite : ∀ R : ℝ, 0 < R → ∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      (∀ x : Euclidean d, x ∉ euclideanAnnulus d (1 / 4 : ℝ) 8 → f x = 0) →
      AEMeasurable (fun x : Euclidean d =>
        (restrictedRelativeCutoffSphericalMaximal d
          (normalizedRadiusBlock E R) phi N f x) ^ p)
          (powerWeightedVolume d α) ∧
      (∫⁻ x : Euclidean d,
        (restrictedRelativeCutoffSphericalMaximal d
          (normalizedRadiusBlock E R) phi N f x) ^ p ∂
          powerWeightedVolume d α) ≤
        A * ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p ∂
          powerWeightedVolume d α) :
    HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p α := by
  rcases (hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_zero_iff d E p).mp
      hunweighted with ⟨U, _hUpos, hU⟩
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpNN : 0 ≤ p := hp0.le
  have hpInvNN : 0 ≤ p⁻¹ := inv_nonneg.mpr hpNN
  let Kcut : ENNReal := (ENNReal.ofReal ((surfaceMass d)⁻¹)) ^ p
  have hKcuttop : Kcut ≠ ∞ := by
    dsimp only [Kcut]
    exact ENNReal.rpow_ne_top_of_nonneg hpNN ENNReal.ofReal_ne_top
  let D : ENNReal := Kcut ^ p⁻¹ * A ^ p⁻¹
  have hDtop : D ≠ ∞ := by
    dsimp only [D]
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg hpInvNN hKcuttop
    · exact ENNReal.rpow_ne_top_of_nonneg hpInvNN hAtop
  let C : ℝ := D.toReal + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hlocal (R : ℝ) (hR : 0 < R) (g : SchwartzMap (Euclidean d) ℂ)
      (hgsupport : ∀ x : Euclidean d,
        x ∉ euclideanAnnulus d (1 / 4 : ℝ) 8 → g x = 0)
      (hg : MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α)) :
      MemLp (restrictedNormalizedSphericalMaximal d
        (normalizedRadiusBlock E R) (g : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
      eLpNorm (restrictedNormalizedSphericalMaximal d
        (normalizedRadiusBlock E R) (g : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
        ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ)
          (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    let μ : Measure (Euclidean d) := powerWeightedVolume d α
    let M : Euclidean d → ENNReal :=
      restrictedNormalizedSphericalMaximal d
        (normalizedRadiusBlock E R) (g : Euclidean d → ℂ)
    let I : ENNReal := ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖g x‖) ^ p ∂μ
    have hmoment : (∫⁻ x : Euclidean d, (M x) ^ p ∂μ) ≤ Kcut * A * I := by
      simpa only [M, I, μ, Kcut] using
        restrictedNormalizedSphericalMaximal_lintegral_rpow_le_of_uniform_relativeCutoff_on_annular_support
          (show 0 < d by omega) hp0 (normalizedRadiusBlock E R) phi hphi_one A hAtop
          (hfinite R hR) g hgsupport
    have hMnorm : eLpNorm M (ENNReal.ofReal p) μ =
        (∫⁻ x : Euclidean d, (M x) ^ p ∂μ) ^ p⁻¹ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
      simp only [ENNReal.toReal_ofReal hpNN, enorm_eq_self]
      rw [one_div]
    have hInorm : eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p) μ = I ^ p⁻¹ := by
      dsimp only [I]
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
      simp only [ENNReal.toReal_ofReal hpNN, ofReal_norm]
      rw [one_div]
    have hnormD : eLpNorm M (ENNReal.ofReal p) μ ≤
        D * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p) μ := by
      rw [hMnorm, hInorm]
      calc
        (∫⁻ x : Euclidean d, (M x) ^ p ∂μ) ^ p⁻¹ ≤
            (Kcut * A * I) ^ p⁻¹ := ENNReal.rpow_le_rpow hmoment hpInvNN
        _ = D * I ^ p⁻¹ := by
          dsimp only [D]
          rw [ENNReal.mul_rpow_of_nonneg _ _ hpInvNN,
            ENNReal.mul_rpow_of_nonneg _ _ hpInvNN]
    have hDleC : D ≤ ENNReal.ofReal C := by
      calc
        D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hDtop).symm
        _ ≤ ENNReal.ofReal C := by
          apply ENNReal.ofReal_le_ofReal
          dsimp only [C]
          exact le_add_of_nonneg_right zero_le_one
    have hnorm : eLpNorm M (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ)
          (ENNReal.ofReal p) μ :=
      hnormD.trans (by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right hDleC
            (bot_le : 0 ≤ eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p) μ))
    have hMtop : eLpNorm M (ENNReal.ofReal p) μ < ∞ :=
      lt_of_le_of_lt hnorm
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top)
    have hMmeas : AEStronglyMeasurable M μ := by
      dsimp only [M]
      exact
        (measurable_restrictedNormalizedSphericalMaximal_schwartz
          (normalizedRadiusBlock E R) g).aestronglyMeasurable
    exact ⟨⟨hMmeas, hMtop⟩, hnorm⟩
  have hUbound (g : SchwartzMap (Euclidean d) ℂ) :
      eLpNorm (restrictedNormalizedSphericalMaximal d E (g : Euclidean d → ℂ))
        (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal U * eLpNorm (g : Euclidean d → ℂ)
          (ENNReal.ofReal p) volume :=
    (hU g (g.memLp (ENNReal.ofReal p) volume)).2
  have hphysical (k : ℤ) : ∀ g : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d,
        x ∉ euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3)) →
          g x = 0) →
      MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p)
          (powerWeightedVolume d α) →
        eLpNorm (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (g : Euclidean d → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume d α) ≤
          ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    have hR : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hshift : 2 * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      ring
    intro g hgsupport hg
    have hgsupport' : ∀ x : Euclidean d,
        x ∉ euclideanAnnulus d ((2 : ℝ) ^ k / 4) (8 * (2 : ℝ) ^ k) → g x = 0 := by
      intro x hx
      apply hgsupport x
      simpa only [dyadic_buffered_annulus_eq] using hx
    have h := restrictedNormalizedSphericalMaximal_block_bound_of_normalized_buffered
      hd hp0 hR (C := C) (hlocal ((2 : ℝ) ^ k) hR) g hg hgsupport'
    rw [hshift] at h
    exact h.2
  let K : ENNReal := globalToLocalMomentConstant p α (ENNReal.ofReal U) (ENNReal.ofReal C)
  refine hasStrongType_of_moment_bound_globalToLocal E hp K ?_ ?_
  · dsimp [K]
    exact globalToLocalMomentConstant_ne_top hp0.le hα ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top
  · intro f hf
    exact globalToLocal_moment_bound_of_unweighted_and_local hd E hp hα
      (ENNReal.ofReal U) (ENNReal.ofReal C) hUbound hphysical f hf

/-- The raw-maximal version of the buffered negative global-to-local
reduction.  It is the same spatial-shell argument as the finite-cutoff form
above, but its local hypothesis is already a moment bound for the actual
normalized spherical maximal operator.  Thus no cutoff or Fatou passage is
inserted here. -/
theorem hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_uniform_normalized_buffered_raw_moment_and_unweighted
    {d : ℕ} (hd : 1 ≤ d) (E : Set ℝ) {p α : ℝ}
    (hp : 1 ≤ p) (hα : α < 0)
    (hunweighted : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p 0)
    (A : ENNReal) (hAtop : A ≠ ∞)
    (hlocal : ∀ R : ℝ, 0 < R → ∀ f : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d, x ∉ euclideanAnnulus d (1 / 4 : ℝ) 8 → f x = 0) →
      (∫⁻ x : Euclidean d,
        (restrictedNormalizedSphericalMaximal d
          (normalizedRadiusBlock E R) (f : Euclidean d → ℂ) x) ^ p ∂
          powerWeightedVolume d α) ≤
        A * ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p ∂
          powerWeightedVolume d α) :
    HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E p α := by
  rcases (hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_zero_iff d E p).mp
      hunweighted with ⟨U, _hUpos, hU⟩
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpNN : 0 ≤ p := hp0.le
  have hpInvNN : 0 ≤ p⁻¹ := inv_nonneg.mpr hpNN
  let D : ENNReal := A ^ p⁻¹
  have hDtop : D ≠ ∞ := by
    dsimp only [D]
    exact ENNReal.rpow_ne_top_of_nonneg hpInvNN hAtop
  let C : ℝ := D.toReal + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hlocalStrong (R : ℝ) (hR : 0 < R) (g : SchwartzMap (Euclidean d) ℂ)
      (hgsupport : ∀ x : Euclidean d,
        x ∉ euclideanAnnulus d (1 / 4 : ℝ) 8 → g x = 0)
      (hg : MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α)) :
      MemLp (restrictedNormalizedSphericalMaximal d
        (normalizedRadiusBlock E R) (g : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α) ∧
      eLpNorm (restrictedNormalizedSphericalMaximal d
        (normalizedRadiusBlock E R) (g : Euclidean d → ℂ))
        (ENNReal.ofReal p) (powerWeightedVolume d α) ≤
        ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ)
          (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    let μ : Measure (Euclidean d) := powerWeightedVolume d α
    let M : Euclidean d → ENNReal :=
      restrictedNormalizedSphericalMaximal d
        (normalizedRadiusBlock E R) (g : Euclidean d → ℂ)
    let I : ENNReal := ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖g x‖) ^ p ∂μ
    have hmoment : (∫⁻ x : Euclidean d, (M x) ^ p ∂μ) ≤ A * I := by
      simpa only [M, I, μ] using hlocal R hR g hgsupport
    have hMnorm : eLpNorm M (ENNReal.ofReal p) μ =
        (∫⁻ x : Euclidean d, (M x) ^ p ∂μ) ^ p⁻¹ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
      simp only [ENNReal.toReal_ofReal hpNN, enorm_eq_self]
      rw [one_div]
    have hInorm : eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p) μ = I ^ p⁻¹ := by
      dsimp only [I]
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
      simp only [ENNReal.toReal_ofReal hpNN, ofReal_norm]
      rw [one_div]
    have hnormD : eLpNorm M (ENNReal.ofReal p) μ ≤
        D * eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p) μ := by
      rw [hMnorm, hInorm]
      calc
        (∫⁻ x : Euclidean d, (M x) ^ p ∂μ) ^ p⁻¹ ≤
            (A * I) ^ p⁻¹ := ENNReal.rpow_le_rpow hmoment hpInvNN
        _ = D * I ^ p⁻¹ := by
          dsimp only [D]
          rw [ENNReal.mul_rpow_of_nonneg _ _ hpInvNN]
    have hDleC : D ≤ ENNReal.ofReal C := by
      calc
        D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hDtop).symm
        _ ≤ ENNReal.ofReal C := by
          apply ENNReal.ofReal_le_ofReal
          dsimp only [C]
          exact le_add_of_nonneg_right zero_le_one
    have hnorm : eLpNorm M (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ)
          (ENNReal.ofReal p) μ :=
      hnormD.trans (by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right hDleC
            (bot_le : 0 ≤ eLpNorm (g : Euclidean d → ℂ) (ENNReal.ofReal p) μ))
    have hMtop : eLpNorm M (ENNReal.ofReal p) μ < ∞ :=
      lt_of_le_of_lt hnorm
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top)
    have hMmeas : AEStronglyMeasurable M μ := by
      dsimp only [M]
      exact
        (measurable_restrictedNormalizedSphericalMaximal_schwartz
          (normalizedRadiusBlock E R) g).aestronglyMeasurable
    exact ⟨⟨hMmeas, hMtop⟩, hnorm⟩
  have hUbound (g : SchwartzMap (Euclidean d) ℂ) :
      eLpNorm (restrictedNormalizedSphericalMaximal d E (g : Euclidean d → ℂ))
        (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal U * eLpNorm (g : Euclidean d → ℂ)
          (ENNReal.ofReal p) volume :=
    (hU g (g.memLp (ENNReal.ofReal p) volume)).2
  have hphysical (k : ℤ) : ∀ g : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d,
        x ∉ euclideanAnnulus d ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 3)) →
          g x = 0) →
      MemLp (g : Euclidean d → ℂ) (ENNReal.ofReal p)
          (powerWeightedVolume d α) →
        eLpNorm (restrictedNormalizedSphericalMaximal d
          (E ∩ Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
          (g : Euclidean d → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume d α) ≤
          ENNReal.ofReal C * eLpNorm (g : Euclidean d → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume d α) := by
    have hR : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hshift : 2 * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      ring
    intro g hgsupport hg
    have hgsupport' : ∀ x : Euclidean d,
        x ∉ euclideanAnnulus d ((2 : ℝ) ^ k / 4) (8 * (2 : ℝ) ^ k) → g x = 0 := by
      intro x hx
      apply hgsupport x
      simpa only [dyadic_buffered_annulus_eq] using hx
    have h := restrictedNormalizedSphericalMaximal_block_bound_of_normalized_buffered
      hd hp0 hR (C := C) (hlocalStrong ((2 : ℝ) ^ k) hR) g hg hgsupport'
    rw [hshift] at h
    exact h.2
  let K : ENNReal := globalToLocalMomentConstant p α (ENNReal.ofReal U) (ENNReal.ofReal C)
  refine hasStrongType_of_moment_bound_globalToLocal E hp K ?_ ?_
  · dsimp [K]
    exact globalToLocalMomentConstant_ne_top hp0.le hα ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top
  · intro f hf
    exact globalToLocal_moment_bound_of_unweighted_and_local hd E hp hα
      (ENNReal.ofReal U) (ENNReal.ofReal C) hUbound hphysical f hf

end

end LeanSpherical.HarmonicAnalysis
