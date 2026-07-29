/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz-stable rational amplitude splitting

The usual hard amplitude truncations do not preserve Schwartz functions.  This
file records the elementary smooth replacement needed for interpolation: a
Schwartz function can be split into a low-amplitude rational part and its
complement, with both terms still Schwartz.
-/

namespace LeanSpherical.HarmonicAnalysis

noncomputable section

open MeasureTheory
open scoped ContDiff

/-- A Schwartz function admits the smooth rational amplitude decomposition
`f = low + high`.  The low term is
`f / (1 + ‖t⁻¹ • f‖²)`, written using a real scalar action so that it is
well-defined for complex-valued inputs. -/
theorem exists_schwartz_rational_low_high
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) (t : ℝ) :
    ∃ low high : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d,
        low x = ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x) ∧
      high = f - low ∧
      ∀ x : Euclidean d, f x = low x + high x := by
  let A : ℂ →L[ℝ] ℂ := (t⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ
  let m : Euclidean d → ℂ := fun x =>
    ((1 + ‖A (f x)‖ ^ 2) ^ (-1 : ℝ) : ℝ)
  have hA : Function.HasTemperateGrowth (A : ℂ → ℂ) :=
    A.hasTemperateGrowth
  have hAf : Function.HasTemperateGrowth
      ((A : ℂ → ℂ) ∘ (f : Euclidean d → ℂ)) :=
    hA.comp f.hasTemperateGrowth
  have hrad : Function.HasTemperateGrowth
      (fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-1 : ℝ)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow ℂ (-1 : ℝ)
  have hreal : Function.HasTemperateGrowth
      ((fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-1 : ℝ)) ∘
        ((A : ℂ → ℂ) ∘ (f : Euclidean d → ℂ))) :=
    hrad.comp hAf
  have hofReal : Function.HasTemperateGrowth (fun a : ℝ => (a : ℂ)) := by
    fun_prop
  have hm : Function.HasTemperateGrowth m := by
    simpa only [m, Function.comp_def] using
      hofReal.comp hreal
  let low : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ m f
  let high : SchwartzMap (Euclidean d) ℂ := f - low
  refine ⟨low, high, ?_, rfl, ?_⟩
  · intro x
    dsimp only [low]
    rw [SchwartzMap.smulLeftCLM_apply_apply hm]
    simp only [m]
    simp only [A, smul_apply, ContinuousLinearMap.id_apply]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ)
      ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) (f x)).symm
  · intro x
    simp only [high, sub_apply]
    ring

/-- The rational split can be chosen simultaneously at every scale.  The
separate literal measurability theorems below, rather than this choice, supply
the measurable profile facts needed for interpolation. -/
theorem exists_schwartz_rational_low_high_family
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) :
    ∃ low high : ℝ → SchwartzMap (Euclidean d) ℂ,
      (∀ t x, low t x = ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x) ∧
        (∀ t, high t = f - low t) ∧
          ∀ t x, f x = low t x + high t x := by
  choose low high hlow hhigh hsplit using
    fun t => exists_schwartz_rational_low_high f t
  exact ⟨low, high, hlow, hhigh, hsplit⟩

/-- The norm of the rational low-amplitude factor. -/
theorem norm_rational_low_amplitude
    (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖((1 + ‖(t⁻¹ : ℝ) • z‖ ^ 2) ^ (-1 : ℝ)) • z‖ =
      ‖z‖ / (1 + (‖z‖ / t) ^ 2) := by
  have hnorm : ‖(t⁻¹ : ℝ) • z‖ = ‖z‖ / t := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    ring
  rw [hnorm, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  rw [Real.rpow_neg_one]
  field_simp

/-- The norm of the complementary rational high-amplitude factor. -/
theorem norm_rational_high_amplitude
    (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖z - ((1 + ‖(t⁻¹ : ℝ) • z‖ ^ 2) ^ (-1 : ℝ)) • z‖ =
      ‖z‖ * ((‖z‖ / t) ^ 2 / (1 + (‖z‖ / t) ^ 2)) := by
  have hnorm : ‖(t⁻¹ : ℝ) • z‖ = ‖z‖ / t := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    ring
  rw [hnorm]
  have hden : 0 < 1 + (‖z‖ / t) ^ 2 := by positivity
  have hcoef : 1 - (1 + (‖z‖ / t) ^ 2) ^ (-1 : ℝ) =
      (‖z‖ / t) ^ 2 / (1 + (‖z‖ / t) ^ 2) := by
    rw [Real.rpow_neg_one]
    field_simp
    ring
  have hsub : z - ((1 + (‖z‖ / t) ^ 2) ^ (-1 : ℝ)) • z =
      (1 - (1 + (‖z‖ / t) ^ 2) ^ (-1 : ℝ)) • z := by
    rw [sub_smul, one_smul]
  rw [hsub, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by rw [hcoef]; positivity), hcoef]
  ring

/-- Scalar low-amplitude estimate used in the rational truncation argument. -/
theorem rational_low_amplitude_sq_le
    {u t p : ℝ} (hu : 0 ≤ u) (ht : 0 < t) (hp1 : 1 < p) (hp2 : p < 2) :
    (u / (1 + (u / t) ^ 2)) ^ 2 ≤ t ^ (2 - p) * u ^ p := by
  have hden : 0 < 1 + (u / t) ^ 2 := by positivity
  have hlow0 : 0 ≤ u / (1 + (u / t) ^ 2) := div_nonneg hu hden.le
  have hlow_u : u / (1 + (u / t) ^ 2) ≤ u := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (u / t)]
  have hlow_t : u / (1 + (u / t) ^ 2) ≤ t := by
    apply (div_le_iff₀ hden).2
    have hsq : 0 ≤ (u - t) ^ 2 := sq_nonneg (u - t)
    field_simp [ht.ne']
    nlinarith
  rcases hu.eq_or_lt with rfl | hu
  · simp [Real.zero_rpow (by linarith : p ≠ 0)]
  rcases le_total u t with hut | htu
  · have hpow : u ^ (2 - p) ≤ t ^ (2 - p) :=
      Real.rpow_le_rpow hu.le hut (by linarith)
    have hup : 0 ≤ u ^ p := Real.rpow_nonneg hu.le _
    calc
      (u / (1 + (u / t) ^ 2)) ^ 2 ≤ u ^ (2 : ℕ) :=
        pow_le_pow_left₀ hlow0 hlow_u 2
      _ = u ^ (2 : ℝ) := (Real.rpow_natCast u 2).symm
      _ = u ^ (2 - p) * u ^ p := by
        rw [← Real.rpow_add hu]
        congr 1
        ring
      _ ≤ t ^ (2 - p) * u ^ p :=
        mul_le_mul_of_nonneg_right hpow hup
  · have hpow : t ^ p ≤ u ^ p :=
      Real.rpow_le_rpow ht.le htu (by linarith)
    have htpart : 0 ≤ t ^ (2 - p) := Real.rpow_nonneg ht.le _
    calc
      (u / (1 + (u / t) ^ 2)) ^ 2 ≤ t ^ (2 : ℕ) :=
        pow_le_pow_left₀ hlow0 hlow_t 2
      _ = t ^ (2 : ℝ) := (Real.rpow_natCast t 2).symm
      _ = t ^ (2 - p) * t ^ p := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      _ ≤ t ^ (2 - p) * u ^ p :=
        mul_le_mul_of_nonneg_left hpow htpart

/-- Scalar high-amplitude estimate used in the rational truncation argument. -/
theorem rational_high_amplitude_le
    {u t p : ℝ} (hu : 0 ≤ u) (ht : 0 < t) (hp1 : 1 < p) (hp2 : p < 2) :
    u * ((u / t) ^ 2 / (1 + (u / t) ^ 2)) ≤ t ^ (1 - p) * u ^ p := by
  have ht0 : 0 ≤ t := ht.le
  have hdiv0 : 0 ≤ u / t := div_nonneg hu ht0
  have hden : 0 < 1 + (u / t) ^ 2 := by positivity
  have hfrac_one : (u / t) ^ 2 / (1 + (u / t) ^ 2) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (u / t)]
  have hhigh_u : u * ((u / t) ^ 2 / (1 + (u / t) ^ 2)) ≤ u := by
    calc
      u * ((u / t) ^ 2 / (1 + (u / t) ^ 2)) ≤ u * 1 :=
        mul_le_mul_of_nonneg_left hfrac_one hu
      _ = u := mul_one _
  have hfrac_linear : (u / t) ^ 2 / (1 + (u / t) ^ 2) ≤ u / t := by
    apply (div_le_iff₀ hden).2
    have haux : 0 ≤ (u / t) * ((u / t) ^ 2 - (u / t) + 1) := by
      apply mul_nonneg hdiv0
      nlinarith [sq_nonneg (u / t - 1 / 2)]
    nlinarith
  have hhigh_quad : u * ((u / t) ^ 2 / (1 + (u / t) ^ 2)) ≤ u ^ 2 / t := by
    calc
      u * ((u / t) ^ 2 / (1 + (u / t) ^ 2)) ≤ u * (u / t) :=
        mul_le_mul_of_nonneg_left hfrac_linear hu
      _ = u ^ 2 / t := by ring
  rcases hu.eq_or_lt with rfl | hu
  · simp [Real.zero_rpow (by linarith : p ≠ 0)]
  rcases le_total u t with hut | htu
  · have hpow : u ^ (2 - p) ≤ t ^ (2 - p) :=
      Real.rpow_le_rpow hu.le hut (by linarith)
    have hup : 0 ≤ u ^ p := Real.rpow_nonneg hu.le _
    calc
      u * ((u / t) ^ 2 / (1 + (u / t) ^ 2)) ≤ u ^ 2 / t := hhigh_quad
      _ = (u ^ (2 - p) * u ^ p) / t := by
        rw [← Real.rpow_natCast u 2, ← Real.rpow_add hu]
        congr 2; ring
      _ ≤ (t ^ (2 - p) * u ^ p) / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hup) ht0
      _ = t ^ (1 - p) * u ^ p := by
        calc
          (t ^ (2 - p) * u ^ p) / t = (t ^ (2 - p) / t) * u ^ p := by ring
          _ = t ^ ((2 - p) - 1) * u ^ p := by
            rw [Real.rpow_sub_one ht.ne']
          _ = t ^ (1 - p) * u ^ p := by
            congr 2; ring
  · have hpow : t ^ (p - 1) ≤ u ^ (p - 1) :=
      Real.rpow_le_rpow ht0 htu (by linarith)
    have hmul : u * t ^ (p - 1) ≤ u ^ p := by
      calc
        u * t ^ (p - 1) ≤ u * u ^ (p - 1) :=
          mul_le_mul_of_nonneg_left hpow hu.le
        _ = u ^ p := by
          calc
            u * u ^ (p - 1) = u ^ (1 : ℝ) * u ^ (p - 1) := by
              rw [Real.rpow_one]
            _ = u ^ (1 + (p - 1)) := (Real.rpow_add hu 1 (p - 1)).symm
            _ = u ^ p := by congr 1; ring
    have htweight : 0 ≤ t ^ (1 - p) := Real.rpow_nonneg ht0 _
    calc
      u * ((u / t) ^ 2 / (1 + (u / t) ^ 2)) ≤ u := hhigh_u
      _ = t ^ (1 - p) * (u * t ^ (p - 1)) := by
        symm
        calc
          t ^ (1 - p) * (u * t ^ (p - 1)) =
              u * (t ^ (1 - p) * t ^ (p - 1)) := by ring
          _ = u := by
            rw [← Real.rpow_add ht]
            norm_num
      _ ≤ t ^ (1 - p) * u ^ p :=
        mul_le_mul_of_nonneg_left hmul htweight

/-- The sharp scalar low-amplitude estimate, in a form suited to the two
frequency tails in the interpolation argument. -/
theorem rational_low_amplitude_sq_le_min
    {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    (u / (1 + (u / t) ^ 2)) ^ 2 ≤ min (u ^ 2) (t ^ 2 / 4) := by
  have hden : 0 < 1 + (u / t) ^ 2 := by positivity
  have hlow0 : 0 ≤ u / (1 + (u / t) ^ 2) := div_nonneg hu hden.le
  have hlow_u : u / (1 + (u / t) ^ 2) ≤ u := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (u / t)]
  have hcore : 2 * (u / t) ≤ 1 + (u / t) ^ 2 := by
    nlinarith [sq_nonneg (u / t - 1)]
  have hu_eq : u = t * (u / t) := by
    field_simp [ht.ne']
  have hlow_half : u / (1 + (u / t) ^ 2) ≤ t / 2 := by
    apply (div_le_iff₀ hden).2
    calc
      u = t * (u / t) := hu_eq
      t * (u / t) = (t / 2) * (2 * (u / t)) := by ring
      _ ≤ (t / 2) * (1 + (u / t) ^ 2) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
  apply le_min
  · exact pow_le_pow_left₀ hlow0 hlow_u 2
  · calc
      (u / (1 + (u / t) ^ 2)) ^ 2 ≤ (t / 2) ^ 2 :=
        pow_le_pow_left₀ hlow0 hlow_half 2
      _ = t ^ 2 / 4 := by ring

/-- The sharp scalar high-amplitude estimate, in a form suited to the two
frequency tails in the interpolation argument. -/
theorem rational_high_amplitude_le_min
    {u t : ℝ} (hu : 0 ≤ u) (_ht : 0 < t) :
    u * ((u / t) ^ 2 / (1 + (u / t) ^ 2)) ≤ min u (u ^ 3 / t ^ 2) := by
  have hsquare : 0 ≤ (u / t) ^ 2 := sq_nonneg _
  have hden : 0 < 1 + (u / t) ^ 2 := by positivity
  have hfrac_one : (u / t) ^ 2 / (1 + (u / t) ^ 2) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hfrac_quad : (u / t) ^ 2 / (1 + (u / t) ^ 2) ≤ (u / t) ^ 2 := by
    exact div_le_self hsquare (by linarith)
  apply le_min
  · calc
      u * ((u / t) ^ 2 / (1 + (u / t) ^ 2)) ≤ u * 1 :=
        mul_le_mul_of_nonneg_left hfrac_one hu
      _ = u := mul_one _
  · calc
      u * ((u / t) ^ 2 / (1 + (u / t) ^ 2)) ≤ u * (u / t) ^ 2 :=
        mul_le_mul_of_nonneg_left hfrac_quad hu
      _ = u ^ 3 / t ^ 2 := by ring

/-- Pointwise `L²` and `L¹` estimates for any rational Schwartz splitting. -/
theorem rational_low_high_pointwise_bounds
    {d : Nat} (f low high : SchwartzMap (Euclidean d) ℂ)
    {t p : ℝ} (ht : 0 < t) (hp1 : 1 < p) (hp2 : p < 2)
    (hlow : ∀ x : Euclidean d,
      low x = ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x)
    (hhigh : high = f - low) (x : Euclidean d) :
    ‖low x‖ ^ 2 ≤ t ^ (2 - p) * ‖f x‖ ^ p ∧
      ‖high x‖ ≤ t ^ (1 - p) * ‖f x‖ ^ p := by
  constructor
  · rw [hlow x, norm_rational_low_amplitude (f x) ht]
    exact rational_low_amplitude_sq_le (norm_nonneg _) ht hp1 hp2
  · rw [hhigh]
    simp only [sub_apply]
    rw [hlow x, norm_rational_high_amplitude (f x) ht]
    exact rational_high_amplitude_le (norm_nonneg _) ht hp1 hp2

/-- The sharp rational split estimates, written with the two amplitude regions
needed by the Tonelli tail argument. -/
theorem rational_low_high_pointwise_tail_bounds
    {d : Nat} (f low high : SchwartzMap (Euclidean d) ℂ)
    {t : ℝ} (ht : 0 < t)
    (hlow : ∀ x : Euclidean d,
      low x = ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x)
    (hhigh : high = f - low) (x : Euclidean d) :
    ‖low x‖ ^ 2 ≤ (if t ≤ ‖f x‖ then t ^ 2 / 4 else ‖f x‖ ^ 2) ∧
      ‖high x‖ ≤ (if t ≤ ‖f x‖ then ‖f x‖ else ‖f x‖ ^ 3 / t ^ 2) := by
  have hlow_bound : ‖low x‖ ^ 2 ≤ min (‖f x‖ ^ 2) (t ^ 2 / 4) := by
    rw [hlow x, norm_rational_low_amplitude (f x) ht]
    exact rational_low_amplitude_sq_le_min (norm_nonneg _) ht
  have hhigh_bound : ‖high x‖ ≤ min ‖f x‖ (‖f x‖ ^ 3 / t ^ 2) := by
    rw [hhigh]
    simp only [sub_apply]
    rw [hlow x, norm_rational_high_amplitude (f x) ht]
    exact rational_high_amplitude_le_min (norm_nonneg _) ht
  constructor
  · by_cases hx : t ≤ ‖f x‖
    · simpa [hx] using hlow_bound.trans (min_le_right _ _)
    · simpa [hx] using hlow_bound.trans (min_le_left _ _)
  · by_cases hx : t ≤ ‖f x‖
    · simpa [hx] using hhigh_bound.trans (min_le_left _ _)
    · simpa [hx] using hhigh_bound.trans (min_le_right _ _)

/-- The sharp rational split estimates in literal indicator form. -/
theorem rational_low_high_pointwise_indicator_bounds
    {d : Nat} (f low high : SchwartzMap (Euclidean d) ℂ)
    {t : ℝ} (ht : 0 < t)
    (hlow : ∀ x : Euclidean d,
      low x = ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x)
    (hhigh : high = f - low) (x : Euclidean d) :
    ‖low x‖ ^ 2 ≤
        (t ^ 2 / 4) * ({y : Euclidean d | t ≤ ‖f y‖}.indicator (fun _ => (1 : ℝ)) x) +
          ‖f x‖ ^ 2 * ({y : Euclidean d | ‖f y‖ < t}.indicator (fun _ => (1 : ℝ)) x) ∧
      ‖high x‖ ≤
        ‖f x‖ * ({y : Euclidean d | t ≤ ‖f y‖}.indicator (fun _ => (1 : ℝ)) x) +
          (‖f x‖ ^ 3 / t ^ 2) *
            ({y : Euclidean d | ‖f y‖ < t}.indicator (fun _ => (1 : ℝ)) x) := by
  have hbounds := rational_low_high_pointwise_tail_bounds f low high ht hlow hhigh x
  constructor
  · by_cases hx : t ≤ ‖f x‖
    · have hnot : ¬ ‖f x‖ < t := not_lt_of_ge hx
      simpa [Set.indicator, hx, hnot] using hbounds.1
    · have hlt : ‖f x‖ < t := lt_of_not_ge hx
      simpa [Set.indicator, hx, hlt] using hbounds.1
  · by_cases hx : t ≤ ‖f x‖
    · have hnot : ¬ ‖f x‖ < t := not_lt_of_ge hx
      simpa [Set.indicator, hx, hnot] using hbounds.2
    · have hlt : ‖f x‖ < t := lt_of_not_ge hx
      simpa [Set.indicator, hx, hlt] using hbounds.2

/-- The literal rational low-amplitude family is jointly measurable in the
scale and spatial variables. -/
theorem measurable_rational_low_family
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) :
    Measurable (fun q : ℝ × Euclidean d =>
      ((1 + ‖(q.1⁻¹ : ℝ) • f q.2‖ ^ 2) ^ (-1 : ℝ)) • f q.2) := by
  have hf : Measurable (fun q : ℝ × Euclidean d => f q.2) :=
    f.continuous.measurable.comp measurable_snd
  have hscale : Measurable (fun q : ℝ × Euclidean d =>
      (q.1⁻¹ : ℝ) • f q.2) :=
    measurable_fst.inv.smul hf
  have hden : Measurable (fun q : ℝ × Euclidean d =>
      1 + ‖(q.1⁻¹ : ℝ) • f q.2‖ ^ 2) :=
    measurable_const.add (hscale.norm.pow_const 2)
  simp_rw [Real.rpow_neg_one]
  exact hden.inv.smul hf

/-- The literal complementary rational high-amplitude family is jointly
measurable in the scale and spatial variables. -/
theorem measurable_rational_high_family
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) :
    Measurable (fun q : ℝ × Euclidean d =>
      f q.2 - ((1 + ‖(q.1⁻¹ : ℝ) • f q.2‖ ^ 2) ^ (-1 : ℝ)) • f q.2) := by
  have hf : Measurable (fun q : ℝ × Euclidean d => f q.2) :=
    f.continuous.measurable.comp measurable_snd
  have hscale : Measurable (fun q : ℝ × Euclidean d =>
      (q.1⁻¹ : ℝ) • f q.2) :=
    measurable_fst.inv.smul hf
  have hden : Measurable (fun q : ℝ × Euclidean d =>
      1 + ‖(q.1⁻¹ : ℝ) • f q.2‖ ^ 2) :=
    measurable_const.add (hscale.norm.pow_const 2)
  simp_rw [Real.rpow_neg_one]
  exact hf.sub (hden.inv.smul hf)

/-- The `L²` profile of the literal rational low-amplitude family is
measurable in the scale. -/
theorem measurable_rational_low_profile_lintegral
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    {μ : Measure (Euclidean d)} [SFinite μ] :
    Measurable (fun t : ℝ => ∫⁻ x,
      ENNReal.ofReal
        (‖((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x‖ ^ (2 : ℕ)) ∂μ) := by
  apply Measurable.lintegral_prod_right
  change Measurable (fun q : ℝ × Euclidean d =>
    ENNReal.ofReal
      (‖((1 + ‖(q.1⁻¹ : ℝ) • f q.2‖ ^ 2) ^ (-1 : ℝ)) • f q.2‖ ^ (2 : ℕ)))
  exact ((measurable_rational_low_family f).norm.pow_const 2).ennreal_ofReal

/-- The `L¹` profile of the literal rational high-amplitude family is
measurable in the scale. -/
theorem measurable_rational_high_profile_lintegral
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    {μ : Measure (Euclidean d)} [SFinite μ] :
    Measurable (fun t : ℝ => ∫⁻ x,
      ENNReal.ofReal
        ‖f x - ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x‖ ∂μ) := by
  apply Measurable.lintegral_prod_right
  change Measurable (fun q : ℝ × Euclidean d =>
    ENNReal.ofReal
      ‖f q.2 - ((1 + ‖(q.1⁻¹ : ℝ) • f q.2‖ ^ 2) ^ (-1 : ℝ)) • f q.2‖)
  exact (measurable_rational_high_family f).norm.ennreal_ofReal

/-- A chosen Schwartz-valued rational split has measurable `L²` and `L¹`
profiles, because its pointwise formulas agree with the literal measurable
families above. -/
theorem measurable_rational_low_high_profile_lintegrals
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    (low high : ℝ → SchwartzMap (Euclidean d) ℂ)
    (hlow : ∀ t x, low t x =
      ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x)
    (hhigh : ∀ t, high t = f - low t)
    {μ : Measure (Euclidean d)} [SFinite μ] :
    Measurable (fun t : ℝ => ∫⁻ x,
      ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) ∧
      Measurable (fun t : ℝ => ∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) := by
  constructor
  · have heq : (fun t : ℝ => ∫⁻ x,
      ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ)) ∂μ) =
        (fun t : ℝ => ∫⁻ x,
          ENNReal.ofReal
            (‖((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x‖ ^ (2 : ℕ)) ∂μ) := by
      funext t
      apply lintegral_congr
      intro x
      rw [hlow t x]
    rw [heq]
    exact measurable_rational_low_profile_lintegral f
  · have heq : (fun t : ℝ => ∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) =
        (fun t : ℝ => ∫⁻ x,
          ENNReal.ofReal
            ‖f x - ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x‖ ∂μ) := by
      funext t
      apply lintegral_congr
      intro x
      rw [hhigh t]
      simp only [sub_apply]
      rw [hlow t x]
    rw [heq]
    exact measurable_rational_high_profile_lintegral f

/-- Precomposing a rational Schwartz split by `t ↦ t / s` preserves its
literal formulas, its Schwartz-valued decomposition, and its pointwise sum. -/
theorem rational_low_high_rescaled_split
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    (low high : ℝ → SchwartzMap (Euclidean d) ℂ)
    (hlow : ∀ t x, low t x =
      ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x)
    (hhigh : ∀ t, high t = f - low t)
    (hsplit : ∀ t x, f x = low t x + high t x) (s : ℝ) :
    (∀ t x, low (t / s) x =
      ((1 + ‖((t / s)⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x) ∧
      (∀ t, high (t / s) = f - low (t / s)) ∧
        ∀ t x, f x = low (t / s) x + high (t / s) x := by
  exact ⟨fun t x => hlow (t / s) x, fun t => hhigh (t / s),
    fun t x => hsplit (t / s) x⟩

/-- The two lower-integral profiles of a rational Schwartz split remain
measurable after the inverse scale reindexing `t ↦ t / s`. -/
theorem measurable_rational_low_high_rescaled_profile_lintegrals
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    (low high : ℝ → SchwartzMap (Euclidean d) ℂ)
    (hlow : ∀ t x, low t x =
      ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x)
    (hhigh : ∀ t, high t = f - low t)
    {μ : Measure (Euclidean d)} [SFinite μ] (s : ℝ) :
    Measurable (fun t : ℝ => ∫⁻ x,
      ENNReal.ofReal (‖low (t / s) x‖ ^ (2 : ℕ)) ∂μ) ∧
      Measurable (fun t : ℝ => ∫⁻ x,
        ENNReal.ofReal ‖high (t / s) x‖ ∂μ) := by
  have hprofiles := measurable_rational_low_high_profile_lintegrals f low high hlow hhigh
    (μ := μ)
  constructor
  · simpa [Function.comp_def] using hprofiles.1.comp (measurable_id.div_const s)
  · simpa [Function.comp_def] using hprofiles.2.comp (measurable_id.div_const s)

/-- Every literal low-amplitude profile belongs to the range of Schwartz
functions.  This lets domain-restricted endpoint estimates be applied without
selecting a non-measurable family of witnesses. -/
theorem rational_low_family_mem_schwartz_range
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) (t : ℝ) :
    (fun x : Euclidean d =>
      ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x) ∈
      Set.range (fun g : SchwartzMap (Euclidean d) ℂ => (g : Euclidean d → ℂ)) := by
  rcases exists_schwartz_rational_low_high f t with
    ⟨low, high, hlow, hhigh, hsplit⟩
  refine ⟨low, ?_⟩
  funext x
  exact hlow x

/-- Every literal complementary high-amplitude profile belongs to the range
of Schwartz functions. -/
theorem rational_high_family_mem_schwartz_range
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) (t : ℝ) :
    (fun x : Euclidean d =>
      f x - ((1 + ‖(t⁻¹ : ℝ) • f x‖ ^ 2) ^ (-1 : ℝ)) • f x) ∈
      Set.range (fun g : SchwartzMap (Euclidean d) ℂ => (g : Euclidean d → ℂ)) := by
  rcases exists_schwartz_rational_low_high f t with
    ⟨low, high, hlow, hhigh, hsplit⟩
  refine ⟨high, ?_⟩
  funext x
  rw [hhigh]
  simp only [sub_apply]
  rw [hlow x]

/-- The fixed scalar cutoff used for the smooth half-height amplitude split.
It is one on the ball of radius `1 / 4` and supported in the ball of radius
`1 / 2`. -/
noncomputable def smooth_half_height_bump : ContDiffBump (0 : ℂ) :=
  ⟨(1 : ℝ) / 4, (1 : ℝ) / 2, by norm_num, by norm_num⟩

/-- A single smooth amplitude split of a Schwartz map.  Unlike hard
indicators, both pieces remain Schwartz. -/
theorem exists_schwartz_smooth_low_high
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) (t : ℝ) :
    ∃ low high : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d,
        low x = ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x) ∧
      high = f - low ∧
      ∀ x : Euclidean d, f x = low x + high x := by
  let η : ContDiffBump (0 : ℂ) := smooth_half_height_bump
  let b : ℂ → ℂ := Complex.ofRealCLM ∘ η
  have hbcompact : HasCompactSupport b := by
    exact η.hasCompactSupport.comp_left (by rfl)
  have hbsmooth : ContDiff ℝ ∞ b := by
    exact Complex.ofRealCLM.contDiff.comp η.contDiff
  have hb : Function.HasTemperateGrowth b :=
    hbcompact.hasTemperateGrowth hbsmooth
  let A : ℂ →L[ℝ] ℂ := (t⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ
  let m : Euclidean d → ℂ := fun x => b (A (f x))
  have hA : Function.HasTemperateGrowth (A : ℂ → ℂ) :=
    A.hasTemperateGrowth
  have hAf : Function.HasTemperateGrowth
      ((A : ℂ → ℂ) ∘ (f : Euclidean d → ℂ)) :=
    hA.comp f.hasTemperateGrowth
  have hm : Function.HasTemperateGrowth m := by
    simpa only [m, b, Function.comp_def] using hb.comp hAf
  let low : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ m f
  let high : SchwartzMap (Euclidean d) ℂ := f - low
  refine ⟨low, high, ?_, rfl, ?_⟩
  · intro x
    dsimp only [low]
    rw [SchwartzMap.smulLeftCLM_apply_apply hm]
    simp only [m, b, A, smul_apply, ContinuousLinearMap.id_apply]
    change ((η ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x = _
    rfl
  · intro x
    simp only [high, sub_apply]
    ring

/-- The smooth low piece is pointwise bounded by half the output height. -/
theorem smooth_low_norm_le_half_height
    {d : Nat} (f low : SchwartzMap (Euclidean d) ℂ) {t : ℝ} (ht : 0 < t)
    (hlow : ∀ x : Euclidean d,
      low x = ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x) :
    ∀ x : Euclidean d, ‖low x‖ ≤ t / 2 := by
  intro x
  let η : ContDiffBump (0 : ℂ) := smooth_half_height_bump
  let y : ℂ := (t⁻¹ : ℝ) • f x
  have hη : η y = smooth_half_height_bump ((t⁻¹ : ℝ) • f x) := by rfl
  by_cases hzero : η y = 0
  · rw [hlow x, ← hη, hzero]
    simp
    positivity
  have hyr : ‖y‖ < (1 : ℝ) / 2 := by
    have hdist : dist y (0 : ℂ) < η.rOut := by
      apply lt_of_not_ge
      intro h
      exact hzero (η.zero_of_le_dist h)
    simpa [η, smooth_half_height_bump, dist_zero_right] using hdist
  have hnorm : ‖y‖ = ‖f x‖ / t := by
    dsimp only [y]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    ring
  have hft : ‖f x‖ < t / 2 := by
    rw [hnorm] at hyr
    have h := (div_lt_iff₀ ht).mp (by simpa using hyr)
    simpa [div_eq_mul_inv, mul_comm] using h
  rw [hlow x, ← hη, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (η.nonneg)]
  calc
    η y * ‖f x‖ ≤ 1 * ‖f x‖ :=
      mul_le_mul_of_nonneg_right η.le_one (norm_nonneg _)
    _ = ‖f x‖ := one_mul _
    _ ≤ t / 2 := hft.le

/-- The complementary smooth high piece is zero below the quarter-height
threshold. -/
theorem smooth_high_eq_zero_of_norm_le_quarter
    {d : Nat} (f low high : SchwartzMap (Euclidean d) ℂ) {t : ℝ} (ht : 0 < t)
    (hlow : ∀ x : Euclidean d,
      low x = ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x)
    (hhigh : high = f - low) (x : Euclidean d) (hfx : ‖f x‖ ≤ t / 4) :
    high x = 0 := by
  let η : ContDiffBump (0 : ℂ) := smooth_half_height_bump
  let y : ℂ := (t⁻¹ : ℝ) • f x
  have hη : η y = smooth_half_height_bump ((t⁻¹ : ℝ) • f x) := by rfl
  have hdiv : ‖f x‖ / t ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ ht).mpr
    simpa [div_eq_mul_inv, mul_comm] using hfx
  have hnorm : ‖y‖ = ‖f x‖ / t := by
    dsimp only [y]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    ring
  have hmem : y ∈ Metric.closedBall (0 : ℂ) η.rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [hnorm]
    simpa [η, smooth_half_height_bump] using hdiv
  have hηone : η y = 1 := η.one_of_mem_closedBall hmem
  rw [hhigh]
  simp only [sub_apply]
  rw [hlow x, ← hη, hηone]
  simp

/-- The smooth high piece never exceeds the original input pointwise. -/
theorem smooth_high_norm_le
    {d : Nat} (f low high : SchwartzMap (Euclidean d) ℂ) {t : ℝ}
    (hlow : ∀ x : Euclidean d,
      low x = ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x)
    (hhigh : high = f - low) (x : Euclidean d) :
    ‖high x‖ ≤ ‖f x‖ := by
  let η : ContDiffBump (0 : ℂ) := smooth_half_height_bump
  let y : ℂ := (t⁻¹ : ℝ) • f x
  have hη : η y = smooth_half_height_bump ((t⁻¹ : ℝ) • f x) := by rfl
  have hsub : f x - ((η y : ℝ) : ℂ) • f x =
      (((1 - η y : ℝ) : ℂ) • f x) := by
    calc
      f x - ((η y : ℝ) : ℂ) • f x =
          (1 : ℂ) • f x - ((η y : ℝ) : ℂ) • f x := by rw [one_smul]
      _ = ((1 : ℂ) - ((η y : ℝ) : ℂ)) • f x := by rw [← sub_smul]
      _ = (((1 - η y : ℝ) : ℂ) • f x) := by norm_num
  rw [hhigh]
  simp only [sub_apply]
  rw [hlow x, ← hη, hsub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr η.le_one)]
  calc
    (1 - η y) * ‖f x‖ ≤ 1 * ‖f x‖ :=
      mul_le_mul_of_nonneg_right (sub_le_self _ η.nonneg) (norm_nonneg _)
    _ = ‖f x‖ := one_mul _

/-- The smooth low/high truncations can be chosen simultaneously at every
positive or negative scale; the estimates above are only used at `t > 0`. -/
theorem exists_schwartz_smooth_low_high_family
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) :
    ∃ low high : ℝ → SchwartzMap (Euclidean d) ℂ,
      (∀ t x, low t x =
        ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x) ∧
      (∀ t, high t = f - low t) ∧
      ∀ t x, f x = low t x + high t x := by
  choose low high hlow hhigh hsplit using
    fun t => exists_schwartz_smooth_low_high f t
  exact ⟨low, high, hlow, hhigh, hsplit⟩

/-- The literal smooth high family is jointly measurable in scale and space. -/
theorem measurable_smooth_high_family
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ) :
    Measurable (fun q : ℝ × Euclidean d =>
      f q.2 -
        ((smooth_half_height_bump ((q.1⁻¹ : ℝ) • f q.2) : ℝ) : ℂ) • f q.2) := by
  let η : ContDiffBump (0 : ℂ) := smooth_half_height_bump
  have hf : Measurable (fun q : ℝ × Euclidean d => f q.2) :=
    f.continuous.measurable.comp measurable_snd
  have hscale : Measurable (fun q : ℝ × Euclidean d =>
      (q.1⁻¹ : ℝ) • f q.2) :=
    measurable_fst.inv.smul hf
  have hcut_real : Measurable (fun q : ℝ × Euclidean d =>
      η ((q.1⁻¹ : ℝ) • f q.2)) :=
    η.continuous.measurable.comp hscale
  have hcut : Measurable (fun q : ℝ × Euclidean d =>
      ((η ((q.1⁻¹ : ℝ) • f q.2) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.measurable.comp hcut_real
  change Measurable (fun q : ℝ × Euclidean d =>
    f q.2 - ((η ((q.1⁻¹ : ℝ) • f q.2) : ℝ) : ℂ) • f q.2)
  exact hf.sub (hcut.smul hf)

/-- Measurability of every real `q`-profile of the literal smooth high
family. -/
theorem measurable_smooth_high_profile_lintegral
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    {μ : Measure (Euclidean d)} [SFinite μ] (q : ℝ) :
    Measurable (fun t : ℝ => ∫⁻ x,
      (ENNReal.ofReal
        ‖f x -
          ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x‖) ^ q ∂μ) := by
  apply Measurable.lintegral_prod_right
  exact ENNReal.continuous_rpow_const.measurable.comp
    (measurable_smooth_high_family f).norm.ennreal_ofReal

/-- The `q`-profile of any chosen smooth Schwartz high family is measurable
in its amplitude scale. -/
theorem measurable_smooth_high_profile_lintegrals
    {d : Nat} (f : SchwartzMap (Euclidean d) ℂ)
    (low high : ℝ → SchwartzMap (Euclidean d) ℂ)
    (hlow : ∀ t x, low t x =
      ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x)
    (hhigh : ∀ t, high t = f - low t)
    {μ : Measure (Euclidean d)} [SFinite μ] (q : ℝ) :
    Measurable (fun t : ℝ => ∫⁻ x,
      (ENNReal.ofReal ‖high t x‖) ^ q ∂μ) := by
  have heq : (fun t : ℝ => ∫⁻ x,
      (ENNReal.ofReal ‖high t x‖) ^ q ∂μ) =
      (fun t : ℝ => ∫⁻ x,
        (ENNReal.ofReal
          ‖f x -
            ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x‖) ^ q ∂μ) := by
    funext t
    apply lintegral_congr
    intro x
    rw [hhigh t]
    simp only [sub_apply]
    rw [hlow t x]
  rw [heq]
  exact measurable_smooth_high_profile_lintegral f q

end

end LeanSpherical.HarmonicAnalysis
