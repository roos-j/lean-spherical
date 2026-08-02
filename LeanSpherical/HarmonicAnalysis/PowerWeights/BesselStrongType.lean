/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.BesselEndpoint
import LeanSpherical.HarmonicAnalysis.PowerWeights.PositiveConjugatedInterpolation

/-!
# Strong-type Bessel regularisation from the geometric top endpoint

This module joins the concrete Bessel `L∞` endpoint to the existing
weak--top interpolation argument.  The remaining input is precisely the
diagonal `L^q` estimate for the conjugated operator.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A diagonal Bessel-conjugated estimate, together with the codimension-one
geometric condition `0 ≤ a < d - 1`, gives a strong estimate at every larger
exponent on the same Bessel reference measure. -/
theorem exists_besselConjugatedRestrictedNormalizedSphericalMaximal_strong_type_of_diagonal
    {d : ℕ} (hd : 2 ≤ d) (E : Set ℝ) {a q p C : ℝ}
    (ha : 0 ≤ a) (ha_lt : a < (d : ℝ) - 1)
    (hq : 0 < q) (hqp : q < p) (hC : 0 < C)
    (hdiagonal : ∀ f : SchwartzMap (Euclidean d) ℂ,
      eLpNorm (besselConjugatedRestrictedNormalizedSphericalMaximal a E f)
          (ENNReal.ofReal q) (besselWeightedVolume (-a * q)) ≤
        ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ)
          (ENNReal.ofReal q) (besselWeightedVolume (-a * q))) :
    ∃ D : ℝ, 0 < D ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p)
          (besselWeightedVolume (-a * q)) →
        MemLp (besselConjugatedRestrictedNormalizedSphericalMaximal a E f)
            (ENNReal.ofReal p) (besselWeightedVolume (-a * q)) ∧
          eLpNorm (besselConjugatedRestrictedNormalizedSphericalMaximal a E f)
              (ENNReal.ofReal p) (besselWeightedVolume (-a * q)) ≤
            ENNReal.ofReal D * eLpNorm (f : Euclidean d → ℂ)
              (ENNReal.ofReal p) (besselWeightedVolume (-a * q)) := by
  obtain ⟨Ctop, hCtop, htop⟩ :=
    exists_besselConjugatedRestrictedNormalizedSphericalMaximal_top_endpoint
      hd ha ha_lt E
  exact exists_besselConjugatedRestrictedNormalizedSphericalMaximal_strong_type_of_q_and_top
    (show 0 < d by omega) E hq hqp hC hCtop hdiagonal htop

/-- Two opposite Bessel multipliers cancel exactly on the Schwartz core. -/
theorem besselSchwartzMultiplier_neg_apply_besselSchwartzMultiplier
    {d : ℕ} (a : ℝ) (f : SchwartzMap (Euclidean d) ℂ) :
    besselSchwartzMultiplier (-a) (besselSchwartzMultiplier a f) = f := by
  ext x
  rw [besselSchwartzMultiplier_apply, besselSchwartzMultiplier_apply]
  have hreal : besselPowerWeight (-a) x * besselPowerWeight a x = 1 := by
    rw [besselPowerWeight_mul]
    convert besselPowerWeight_zero x using 1 <;> ring
  calc
    (besselPowerWeight (-a) x : ℂ) *
        ((besselPowerWeight a x : ℂ) * f x) =
        ((besselPowerWeight (-a) x * besselPowerWeight a x : ℝ) : ℂ) * f x := by
          push_cast
          ring
    _ = f x := by rw [hreal]; simp

/-- The conjugated maximal operator applied to `w_a f` is literally `w_a`
times the original restricted maximal operator applied to `f`. -/
theorem besselConjugatedRestrictedNormalizedSphericalMaximal_multiplier
    {d : ℕ} (a : ℝ) (E : Set ℝ) (f : SchwartzMap (Euclidean d) ℂ)
    (x : Euclidean d) :
    besselConjugatedRestrictedNormalizedSphericalMaximal a E
        (besselSchwartzMultiplier a f) x =
      besselPowerWeight a x *
        (restrictedNormalizedSphericalMaximal d E (f : Euclidean d → ℂ) x).toReal := by
  unfold besselConjugatedRestrictedNormalizedSphericalMaximal
  rw [besselSchwartzMultiplier_neg_apply_besselSchwartzMultiplier]

/-- Pointwise norm formula for the Bessel multiplier. -/
theorem norm_besselSchwartzMultiplier_apply
    {d : ℕ} (a : ℝ) (f : SchwartzMap (Euclidean d) ℂ)
    (x : Euclidean d) :
    ‖besselSchwartzMultiplier a f x‖ = besselPowerWeight a x * ‖f x‖ := by
  rw [besselSchwartzMultiplier_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (besselPowerWeight_nonneg a x)]

/-- The pointwise density algebra behind the Bessel strong-type transport. -/
theorem besselPowerWeight_rpow_mul
    {d : ℕ} (a b p : ℝ) (x : Euclidean d) :
    (besselPowerWeight a x) ^ p * besselPowerWeight b x =
      besselPowerWeight (a * p + b) x := by
  unfold besselPowerWeight
  rw [← Real.rpow_mul (by positivity : 0 ≤ 1 + ‖x‖ ^ 2)]
  rw [← Real.rpow_add (by positivity : 0 < 1 + ‖x‖ ^ 2)]
  congr 1
  ring

/-- In particular, conjugating at exponent `a` changes the Bessel density
`w_{-a q}` into the actual output density `w_{a (p-q)}`. -/
theorem besselPowerWeight_conjugation_density
    {d : ℕ} (a p q : ℝ) (x : Euclidean d) :
    (besselPowerWeight a x) ^ p * besselPowerWeight (-a * q) x =
      besselPowerWeight (a * (p - q)) x := by
  rw [besselPowerWeight_rpow_mul]
  congr 1
  ring

/-- Multiplying a Schwartz input by `w_a` transports its `L^p` norm from
the Bessel density `w_b` to `w_{a p+b}` exactly. -/
theorem eLpNorm_besselSchwartzMultiplier_eq
    {d : ℕ} (a b p : ℝ) (hp : 0 < p)
    (f : SchwartzMap (Euclidean d) ℂ) :
    eLpNorm (besselSchwartzMultiplier a f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (besselWeightedVolume b) =
      eLpNorm (f : Euclidean d → ℂ)
        (ENNReal.ofReal p) (besselWeightedVolume (a * p + b)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hleft_meas : Measurable (fun x : Euclidean d =>
      ‖besselSchwartzMultiplier a f x‖ₑ ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp
      (besselSchwartzMultiplier a f).continuous.enorm.measurable
  have hright_meas : Measurable (fun x : Euclidean d => ‖f x‖ₑ ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp f.continuous.enorm.measurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le]
  congr 1
  unfold besselWeightedVolume
  rw [lintegral_withDensity_eq_lintegral_mul volume
      (measurable_besselPowerDensity b) hleft_meas,
    lintegral_withDensity_eq_lintegral_mul volume
      (measurable_besselPowerDensity (a * p + b)) hright_meas]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (besselPowerWeight b x) *
      ‖besselSchwartzMultiplier a f x‖ₑ ^ p =
    ENNReal.ofReal (besselPowerWeight (a * p + b) x) * ‖f x‖ₑ ^ p
  rw [← ofReal_norm, norm_besselSchwartzMultiplier_apply]
  rw [ENNReal.ofReal_mul (besselPowerWeight_nonneg a x),
    ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  have hweight :
      ENNReal.ofReal (besselPowerWeight b x) *
          (ENNReal.ofReal (besselPowerWeight a x)) ^ p =
        ENNReal.ofReal (besselPowerWeight (a * p + b) x) := by
    rw [ENNReal.ofReal_rpow_of_pos (besselPowerWeight_pos a x)]
    rw [mul_comm]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (besselPowerWeight_nonneg a x) p)]
    rw [besselPowerWeight_rpow_mul]
  rw [show ENNReal.ofReal (besselPowerWeight b x) *
      ((ENNReal.ofReal (besselPowerWeight a x)) ^ p *
        (ENNReal.ofReal ‖f x‖) ^ p) =
      (ENNReal.ofReal (besselPowerWeight b x) *
        (ENNReal.ofReal (besselPowerWeight a x)) ^ p) *
        (ENNReal.ofReal ‖f x‖) ^ p by ring,
    hweight]
  rw [ofReal_norm]

/-- The same Bessel density transport holds for a nonnegative real output
function, in particular for the real-valued restricted maximal function. -/
theorem eLpNorm_bessel_weighted_real_mul_eq
    {d : ℕ} (a b p : ℝ) (hp : 0 < p)
    (g : Euclidean d → ℝ) (hg : Measurable g) (hgnonneg : ∀ x, 0 ≤ g x) :
    eLpNorm (fun x => besselPowerWeight a x * g x)
        (ENNReal.ofReal p) (besselWeightedVolume b) =
      eLpNorm g (ENNReal.ofReal p)
        (besselWeightedVolume (a * p + b)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hleft_meas : Measurable (fun x : Euclidean d =>
      ‖besselPowerWeight a x * g x‖ₑ ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp
      ((measurable_besselPowerWeight a).mul hg).enorm
  have hright_meas : Measurable (fun x : Euclidean d => ‖g x‖ₑ ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hg.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le]
  congr 1
  unfold besselWeightedVolume
  rw [lintegral_withDensity_eq_lintegral_mul volume
      (measurable_besselPowerDensity b) hleft_meas,
    lintegral_withDensity_eq_lintegral_mul volume
      (measurable_besselPowerDensity (a * p + b)) hright_meas]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (besselPowerWeight b x) *
      ‖besselPowerWeight a x * g x‖ₑ ^ p =
    ENNReal.ofReal (besselPowerWeight (a * p + b) x) * ‖g x‖ₑ ^ p
  rw [← ofReal_norm, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (besselPowerWeight_nonneg a x) (hgnonneg x)),
    ENNReal.ofReal_mul (besselPowerWeight_nonneg a x),
    ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  have hweight :
      ENNReal.ofReal (besselPowerWeight b x) *
          (ENNReal.ofReal (besselPowerWeight a x)) ^ p =
        ENNReal.ofReal (besselPowerWeight (a * p + b) x) := by
    rw [ENNReal.ofReal_rpow_of_pos (besselPowerWeight_pos a x)]
    rw [mul_comm]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (besselPowerWeight_nonneg a x) p)]
    rw [besselPowerWeight_rpow_mul]
  rw [show ENNReal.ofReal (besselPowerWeight b x) *
      ((ENNReal.ofReal (besselPowerWeight a x)) ^ p *
        (ENNReal.ofReal (g x)) ^ p) =
      (ENNReal.ofReal (besselPowerWeight b x) *
        (ENNReal.ofReal (besselPowerWeight a x)) ^ p) *
        (ENNReal.ofReal (g x)) ^ p by ring,
    hweight]
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hgnonneg x)]

end

end LeanSpherical.HarmonicAnalysis
