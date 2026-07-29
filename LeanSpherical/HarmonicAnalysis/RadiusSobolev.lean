/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A one-dimensional estimate in the radius variable

The elementary fundamental-theorem-of-calculus estimate used to pass from a
fixed-radius bound to a maximal bound on a compact radius interval.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory intervalIntegral Set

/-- A `C¹` function on the real line is bounded at every point of `[a, b]` by
its value at `a` plus the total variation supplied by its derivative on that
interval. -/
theorem norm_le_norm_add_intervalIntegral_norm_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b r : ℝ}
    (hr : r ∈ Icc a b)
    (hf' : Continuous f')
    (hderiv : ∀ t, HasDerivAt f (f' t) t) :
    ‖f r‖ ≤ ‖f a‖ + ∫ t in a..b, ‖f' t‖ := by
  have hftc : ∫ t in a..r, f' t = f r - f a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      exact hderiv t
    · exact hf'.continuousOn.intervalIntegrable
  have hnorm : ‖f r - f a‖ ≤ ∫ t in a..r, ‖f' t‖ := by
    rw [← hftc]
    exact intervalIntegral.norm_integral_le_integral_norm hr.1
  have hmono : (∫ t in a..r, ‖f' t‖) ≤ ∫ t in a..b, ‖f' t‖ := by
    apply intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
    · filter_upwards [] with t
      exact norm_nonneg _
    · exact hf'.norm.continuousOn.intervalIntegrable
  calc
    ‖f r‖ = ‖(f r - f a) + f a‖ := by rw [sub_add_cancel]
    _ ≤ ‖f r - f a‖ + ‖f a‖ := norm_add_le _ _
    _ = ‖f a‖ + ‖f r - f a‖ := add_comm _ _
    _ ≤ ‖f a‖ + ∫ t in a..r, ‖f' t‖ := add_le_add_right hnorm _
    _ ≤ ‖f a‖ + ∫ t in a..b, ‖f' t‖ := add_le_add_right hmono _

/-- Cauchy--Schwarz on a compact real interval, in the form used for the
radial Sobolev estimate. -/
theorem intervalIntegral_norm_sq_le_length_mul_intervalIntegral_norm_sq
    {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hg : Continuous g) :
    (∫ t in a..b, ‖g t‖) ^ 2 ≤
      (b - a) * ∫ t in a..b, ‖g t‖ ^ 2 := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hg_mem : MemLp g (ENNReal.ofReal 2) μ := by
    exact MemLp.of_bound (p := ENNReal.ofReal 2) (hg.aestronglyMeasurable.restrict) C
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht => hC t ht)
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (f := fun t => ‖g t‖) (g := fun _ : ℝ => (1 : ℝ))
    (p := 2) (q := 2) (by norm_num [Real.holderConjugate_iff]) hg_mem.norm
    (memLp_const (1 : ℝ))
  have hmass : μ.real univ = b - a := by
    simp [μ, hab]
  have hholder_sqrt :
      (∫ t, ‖g t‖ ∂μ) ≤
        √(∫ t, ‖g t‖ ^ 2 ∂μ) * √(b - a) := by
    simpa [hmass, Real.sqrt_eq_rpow] using hholder
  have hleft_nonneg : 0 ≤ ∫ t, ‖g t‖ ∂μ :=
    integral_nonneg fun _ => norm_nonneg _
  have hsq_nonneg : 0 ≤ ∫ t, ‖g t‖ ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have hlength_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have hset :
      (∫ t, ‖g t‖ ∂μ) ^ 2 ≤ (∫ t, ‖g t‖ ^ 2 ∂μ) * (b - a) := by
    calc
      (∫ t, ‖g t‖ ∂μ) ^ 2 ≤
          (√(∫ t, ‖g t‖ ^ 2 ∂μ) * √(b - a)) ^ 2 :=
        (sq_le_sq₀ hleft_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hholder_sqrt
      _ = (∫ t, ‖g t‖ ^ 2 ∂μ) * (b - a) := by
        rw [mul_pow, Real.sq_sqrt hsq_nonneg, Real.sq_sqrt hlength_nonneg]
  calc
    (∫ t in a..b, ‖g t‖) ^ 2 = (∫ t, ‖g t‖ ∂μ) ^ 2 := by
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    _ ≤ (∫ t, ‖g t‖ ^ 2 ∂μ) * (b - a) := hset
    _ = (b - a) * ∫ t in a..b, ‖g t‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
      ring

/-- A squared radius-Sobolev estimate on a compact interval.  It is the
pointwise step behind controlling a radius supremum by the fixed-radius term
at `a` and the square integral of the radial derivative. -/
theorem norm_sq_le_two_mul_norm_sq_add_two_mul_length_mul_intervalIntegral_norm_sq_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b r : ℝ}
    (hr : r ∈ Icc a b)
    (hf' : Continuous f')
    (hderiv : ∀ t, HasDerivAt f (f' t) t) :
    ‖f r‖ ^ 2 ≤ 2 * ‖f a‖ ^ 2 +
      2 * (b - a) * ∫ t in a..b, ‖f' t‖ ^ 2 := by
  have hftc := norm_le_norm_add_intervalIntegral_norm_of_hasDerivAt hr hf' hderiv
  have hcs := intervalIntegral_norm_sq_le_length_mul_intervalIntegral_norm_sq
    (hr.1.trans hr.2) hf'
  have hsum_nonneg : 0 ≤ ‖f a‖ + ∫ t in a..b, ‖f' t‖ := by
    exact add_nonneg (norm_nonneg _)
      (intervalIntegral.integral_nonneg (hr.1.trans hr.2) fun _ _ => norm_nonneg _)
  have hsq : ‖f r‖ ^ 2 ≤ (‖f a‖ + ∫ t in a..b, ‖f' t‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hsum_nonneg).2 hftc
  calc
    ‖f r‖ ^ 2 ≤ (‖f a‖ + ∫ t in a..b, ‖f' t‖) ^ 2 := hsq
    _ ≤ 2 * ‖f a‖ ^ 2 + 2 * (∫ t in a..b, ‖f' t‖) ^ 2 := by
      nlinarith [sq_nonneg (‖f a‖ - ∫ t in a..b, ‖f' t‖)]
    _ ≤ 2 * ‖f a‖ ^ 2 + 2 * ((b - a) * ∫ t in a..b, ‖f' t‖ ^ 2) := by
      gcongr
    _ = 2 * ‖f a‖ ^ 2 + 2 * (b - a) * ∫ t in a..b, ‖f' t‖ ^ 2 := by ring

/-- Taking the supremum of the squared radius-Sobolev estimate over a compact
interval gives the corresponding local maximal bound. -/
theorem iSup_ennreal_norm_sq_le_radiusSobolev
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b : ℝ}
    (hf' : Continuous f')
    (hderiv : ∀ t, HasDerivAt f (f' t) t) :
    (⨆ r : Icc a b, ENNReal.ofReal (‖f r.1‖ ^ 2)) ≤
      ENNReal.ofReal (2 * ‖f a‖ ^ 2 +
        2 * (b - a) * ∫ t in a..b, ‖f' t‖ ^ 2) := by
  apply iSup_le
  intro r
  exact ENNReal.ofReal_le_ofReal
    (norm_sq_le_two_mul_norm_sq_add_two_mul_length_mul_intervalIntegral_norm_sq_of_hasDerivAt
      r.2 hf' hderiv)

/-- The radius Sobolev estimate in the product form used in the dyadic
maximal argument.  Keeping `‖f‖ * ‖f'‖` intact is essential: after integrating
in the remaining variables, Cauchy--Schwarz combines the fixed-radius decay
with the derivative bound. -/
theorem norm_sq_le_norm_sq_add_two_mul_intervalIntegral_norm_mul_norm_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b r : ℝ}
    (hr : r ∈ Icc a b)
    (hf' : Continuous f')
    (hderiv : ∀ t, HasDerivAt f (f' t) t) :
    ‖f r‖ ^ 2 ≤ ‖f a‖ ^ 2 +
      2 * ∫ t in a..b, ‖f t‖ * ‖f' t‖ := by
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hderiv t).continuousAt
  have hderiv_sq (t : ℝ) :
      HasDerivAt (fun s => ‖f s‖ ^ 2) (2 * inner ℝ (f t) (f' t)) t := by
    simpa using (hderiv t).norm_sq
  have hinner_cont : Continuous (fun t => 2 * inner ℝ (f t) (f' t)) :=
    (hf.inner hf').const_mul (2 : ℝ)
  have hprod_cont : Continuous (fun t => 2 * (‖f t‖ * ‖f' t‖)) :=
    (hf.norm.mul hf'.norm).const_mul (2 : ℝ)
  have hftc : ∫ t in a..r, 2 * inner ℝ (f t) (f' t) = ‖f r‖ ^ 2 - ‖f a‖ ^ 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      exact hderiv_sq t
    · exact hinner_cont.intervalIntegrable (μ := volume) a r
  have hpoint (t : ℝ) : 2 * inner ℝ (f t) (f' t) ≤ 2 * (‖f t‖ * ‖f' t‖) := by
    have hinter : inner ℝ (f t) (f' t) ≤ ‖f t‖ * ‖f' t‖ := real_inner_le_norm _ _
    nlinarith
  have hinterval_nonneg (t : ℝ) : 0 ≤ 2 * (‖f t‖ * ‖f' t‖) := by positivity
  have hmono :
      (∫ t in a..r, 2 * inner ℝ (f t) (f' t)) ≤
        ∫ t in a..b, 2 * (‖f t‖ * ‖f' t‖) := by
    calc
      (∫ t in a..r, 2 * inner ℝ (f t) (f' t)) ≤
          ∫ t in a..r, 2 * (‖f t‖ * ‖f' t‖) := by
        exact intervalIntegral.integral_mono hr.1
          (hinner_cont.intervalIntegrable (μ := volume) a r)
          (hprod_cont.intervalIntegrable (μ := volume) a r) hpoint
      _ ≤ ∫ t in a..b, 2 * (‖f t‖ * ‖f' t‖) := by
        apply intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
        · filter_upwards [] with t
          exact hinterval_nonneg t
        · exact hprod_cont.intervalIntegrable (μ := volume) a b
  calc
    ‖f r‖ ^ 2 = ‖f a‖ ^ 2 + ∫ t in a..r, 2 * inner ℝ (f t) (f' t) := by
      rw [hftc]
      ring
    _ ≤ ‖f a‖ ^ 2 + ∫ t in a..b, 2 * (‖f t‖ * ‖f' t‖) :=
      add_le_add_right hmono _
    _ = ‖f a‖ ^ 2 + 2 * ∫ t in a..b, ‖f t‖ * ‖f' t‖ := by
      rw [intervalIntegral.integral_const_mul]

/-- Taking the radius supremum of the product-form Sobolev estimate. -/
theorem iSup_ennreal_norm_sq_le_radiusSobolev_product
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b : ℝ}
    (hf' : Continuous f')
    (hderiv : ∀ t, HasDerivAt f (f' t) t) :
    (⨆ r : Icc a b, ENNReal.ofReal (‖f r.1‖ ^ 2)) ≤
      ENNReal.ofReal (‖f a‖ ^ 2 +
        2 * ∫ t in a..b, ‖f t‖ * ‖f' t‖) := by
  apply iSup_le
  intro r
  exact ENNReal.ofReal_le_ofReal
    (norm_sq_le_norm_sq_add_two_mul_intervalIntegral_norm_mul_norm_of_hasDerivAt
      r.2 hf' hderiv)

/-- The unit-interval form of the squared radius-Sobolev estimate. -/
theorem norm_sq_le_two_mul_norm_sq_add_two_mul_intervalIntegral_norm_sq_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1)
    (hf' : Continuous f')
    (hderiv : ∀ t, HasDerivAt f (f' t) t) :
    ‖f r‖ ^ 2 ≤ 2 * ‖f 0‖ ^ 2 + 2 * ∫ t in (0 : ℝ)..1, ‖f' t‖ ^ 2 := by
  simpa using
    norm_sq_le_two_mul_norm_sq_add_two_mul_length_mul_intervalIntegral_norm_sq_of_hasDerivAt
      hr hf' hderiv

end LeanSpherical.HarmonicAnalysis
