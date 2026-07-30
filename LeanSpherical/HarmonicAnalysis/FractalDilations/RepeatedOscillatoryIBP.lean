/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.OscillatoryIBP

/-!
# Repeated nonstationary integration by parts

The radius-gap estimate uses arbitrarily many integrations by parts after the
stationary-phase reduction.  The one-step identity is in `OscillatoryIBP`;
this file packages its finite iteration.  Keeping the chain of amplitudes
explicit is useful for the literal dyadic symbols, whose derivatives are
obtained separately from compact support and symbol estimates.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set

noncomputable section

/-- A finite differentiability chain suitable for repeated integration by
parts on `[a,b]`.  The first `N` amplitudes vanish at both endpoints, and the
next amplitude is their derivative. -/
def HasOscillatoryIBPChain (a b : ℝ) (F : ℕ → ℝ → ℂ) (N : ℕ) : Prop :=
  ∀ k : ℕ, k < N →
    (∀ t ∈ uIcc a b, HasDerivAt (F k) (F (k + 1) t) t) ∧
      Continuous (F (k + 1)) ∧ F k a = 0 ∧ F k b = 0

/-- Repeatedly applying the exact one-step formula moves all derivatives onto
the amplitude and gains one inverse frequency at each step. -/
private theorem intervalIntegral_mul_oscillatoryExp_iterated
    {a b freq : ℝ} {F : ℕ → ℝ → ℂ} {L N k : ℕ}
    (hfreq : freq ≠ 0) (hchain : HasOscillatoryIBPChain a b F L)
    (hkn : k + N ≤ L) :
    (∫ t in a..b, F k t * oscillatoryExp freq t) =
      (-(((freq : ℂ) * Complex.I)⁻¹)) ^ N *
        ∫ t in a..b, F (k + N) t * oscillatoryExp freq t := by
  induction N generalizing k with
  | zero =>
      simp
  | succ N ih =>
      have hklt : k < L := by omega
      rcases hchain k hklt with ⟨hderiv, hcont, hleft, hright⟩
      have hone := intervalIntegral_mul_oscillatoryExp_eq_neg_inv_mul
        hfreq hderiv hcont hleft hright
      have hnext : (k + 1) + N ≤ L := by omega
      have htail := ih (k := k + 1) hnext
      rw [hone, htail, pow_succ]
      have hindex : k + 1 + N = k + (N + 1) := by omega
      rw [hindex]
      ring

/-- Quantitative finite-order nonstationary phase.  This is the precise
estimate needed once a signed pair multiplier has been reduced to a compact
one-dimensional amplitude with symbol bounds. -/
theorem norm_intervalIntegral_mul_oscillatoryExp_le_iterated
    {a b freq M : ℝ} {F : ℕ → ℝ → ℂ} {N : ℕ}
    (hab : a ≤ b) (hfreq : freq ≠ 0)
    (hchain : HasOscillatoryIBPChain a b F N)
    (_hM : 0 ≤ M) (hbound : ∀ t ∈ Icc a b, ‖F N t‖ ≤ M) :
    ‖∫ t in a..b, F 0 t * oscillatoryExp freq t‖ ≤
      (1 / |freq|) ^ N * ((b - a) * M) := by
  have hiter := intervalIntegral_mul_oscillatoryExp_iterated
    (L := N) (k := 0) (N := N) hfreq hchain (by omega)
  have hnorm_osc (t : ℝ) : ‖oscillatoryExp freq t‖ = 1 := by
    unfold oscillatoryExp
    exact Complex.norm_exp_ofReal_mul_I _
  have hlast :
      ‖∫ t in a..b, F N t * oscillatoryExp freq t‖ ≤ (b - a) * M := by
    calc
      ‖∫ t in a..b, F N t * oscillatoryExp freq t‖ ≤ M * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        have ht' : t ∈ Icc a b := by
          rw [uIoc_of_le hab] at ht
          exact ⟨ht.1.le, ht.2⟩
        rw [norm_mul, hnorm_osc, mul_one]
        exact hbound t ht'
      _ = (b - a) * M := by
        rw [abs_of_nonneg (sub_nonneg.mpr hab)]
        ring
  have hfactor : ‖-(((freq : ℂ) * Complex.I)⁻¹)‖ = 1 / |freq| := by
    rw [norm_neg, norm_inv, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs]
    exact inv_eq_one_div _
  rw [hiter, norm_mul, norm_pow, hfactor]
  exact mul_le_mul_of_nonneg_left (by simpa using hlast)
    (pow_nonneg (by positivity) _)

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
