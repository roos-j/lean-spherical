/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.StrictNegativeRawBands

/-!
# Summable raw tails from the thin-radial shell reassembly

The shell reassembly leaves two coefficient-only distance-block sums.  This
file collapses their finite spatial-shell and distance-block indices into the
same raw band rate used by the strict negative endpoint.  The input moment is
intentionally not included in the finite constant.
-/

namespace LeanSpherical.HarmonicAnalysis

open scoped BigOperators ENNReal

noncomputable section

private theorem ennreal_nat_succ_eq_ofReal (j : Nat) :
    ((j + 1 : Nat) : ENNReal) = ENNReal.ofReal ((j : Real) + 1) := by
  rw [← ENNReal.ofReal_natCast]
  congr 1
  push_cast
  ring

private theorem exists_thinRadialShellTail_single_raw_band_rate
    {n : Nat} {p alpha epsilon : Real}
    (V : ENNReal) (hVtop : V ≠ ∞) (C : Real) (hC : 0 ≤ C)
    (hp : 1 < p) (halpha : alpha ≤ 0)
    (hepsilon : 0 ≤ epsilon) (hepsilon_gain : epsilon ≤ (n : Real) + alpha) :
    ∃ Ktail : ENNReal, Ktail ≠ ∞ ∧ ∀ j : Nat,
      (∑ k ∈ Finset.Icc 4 (j - 2),
        ((k + 5 : Nat) : ENNReal) ^ (p - 1) *
          ∑ q ∈ Finset.range (Nat.log 2 (2 ^ (k + 4)) + 1),
            (V * ((ENNReal.ofReal (8 : Real)) ^ alpha)⁻¹ *
              ((ENNReal.ofReal 2) ^ p * 2)) *
              thinRadialTailRawCoefficient n j k q C p alpha) ≤
        Ktail * (ENNReal.ofReal ((j : Real) + 1)) ^ (2 * p - 1) *
          (dyadicMultiplicativeScale j : ENNReal) ^ epsilon := by
  let x : ENNReal := ENNReal.ofReal (1 / 2 : Real)
  let r : ENNReal := x ^
    (p * ((n : Real) + 3) - ((n : Real) + alpha))
  let t : ENNReal := x ^ (p * ((n : Real) + 3))
  let A : ENNReal :=
    V * ((ENNReal.ofReal (8 : Real)) ^ alpha)⁻¹ *
      ((ENNReal.ofReal 2) ^ p * 2)
  let K : ENNReal :=
    (4 : ENNReal) ^ (p - 1) * A * (ENNReal.ofReal C) ^ p *
      x ^ (-(p * (6 * (n : Real) + 26) + (n : Real) + alpha))
  have hx0 : x ≠ 0 := by
    dsimp only [x]
    exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hxtop : x ≠ ∞ := by
    dsimp only [x]
    exact ENNReal.ofReal_ne_top
  have hfourTop : (4 : ENNReal) ^ (p - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) ENNReal.coe_ne_top
  have hweightTop : ((ENNReal.ofReal (8 : Real)) ^ alpha)⁻¹ ≠ ∞ := by
    apply ENNReal.inv_ne_top.mpr
    exact (ENNReal.rpow_pos (by norm_num) ENNReal.ofReal_ne_top).ne'
  have htwoTop : (ENNReal.ofReal 2) ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) ENNReal.ofReal_ne_top
  have hAtop : A ≠ ∞ := by
    dsimp only [A]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top hVtop hweightTop
    · exact ENNReal.mul_ne_top htwoTop (by norm_num)
  have hCpowTop : (ENNReal.ofReal C) ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (lt_trans zero_lt_one hp).le ENNReal.ofReal_ne_top
  have hxpowTop :
      x ^ (-(p * (6 * (n : Real) + 26) + (n : Real) + alpha)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hx0 hxtop
  have hKtop : K ≠ ∞ := by
    dsimp only [K]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top hfourTop hAtop
      · exact hCpowTop
    · exact hxpowTop
  obtain ⟨hr, ht⟩ := thinRadialTail_geometric_ratios_lt_one n hp halpha
  have hr' : r < 1 := by
    simpa only [r, x] using hr
  have ht' : t < 1 := by
    simpa only [t, x] using ht
  have hscale (j : Nat) :
      (dyadicMultiplicativeScale j : ENNReal) ^ ((n : Real) + alpha) ≤
        (dyadicMultiplicativeScale j : ENNReal) ^ epsilon := by
    exact ENNReal.rpow_le_rpow_of_exponent_ge
      (by
        exact_mod_cast (show dyadicMultiplicativeScale j ≤ 1 by
          unfold dyadicMultiplicativeScale
          exact pow_le_one₀ (by norm_num) (by norm_num))) hepsilon_gain
  let F : Nat → Nat → Nat → ENNReal := fun j k q =>
    ((k + 5 : Nat) : ENNReal) ^ (p - 1) *
      (A * thinRadialTailRawCoefficient n j k q C p alpha)
  obtain ⟨Ktail, hKtailTop, hcollapse⟩ :=
    exists_thinRadialTail_kq_raw_band_constant (p := p) (epsilon := epsilon)
      K r t hKtop hr' ht' F (by
        intro j k q hjk _hq
        let J : ENNReal := ENNReal.ofReal ((j : Real) + 1)
        have hJ0 : J ≠ 0 := by
          dsimp only [J]
          exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
        have hJtop : J ≠ ∞ := by
          dsimp only [J]
          exact ENNReal.ofReal_ne_top
        have hJnat : ((j + 1 : Nat) : ENNReal) = J := by
          dsimp only [J]
          exact ennreal_nat_succ_eq_ofReal j
        have hJcombine : J ^ (p - 1) * J ^ p = J ^ (2 * p - 1) := by
          rw [← ENNReal.rpow_add _ _ hJ0 hJtop]
          congr 1
          ring
        have hraw :
            thinRadialTailRawCoefficient n j k q C p alpha ≤
              (ENNReal.ofReal C) ^ p *
                x ^ (-(p * (6 * (n : Real) + 26) + (n : Real) + alpha)) *
                  ((j + 1 : Nat) : ENNReal) ^ p *
                  (dyadicMultiplicativeScale j : ENNReal) ^ ((n : Real) + alpha) *
                    r ^ (j - k - 1) * t ^ q := by
          simpa only [x, r, t] using
            thinRadialTailRawCoefficient_le_geometric hjk C hC (lt_trans zero_lt_one hp).le
        have hpoly := thinRadialTail_reassembly_polynomial_factor_le hp.le hjk
          (A * thinRadialTailRawCoefficient n j k q C p alpha)
        calc
          F j k q =
              ((k + 5 : Nat) : ENNReal) ^ (p - 1) *
                (A * thinRadialTailRawCoefficient n j k q C p alpha) := rfl
          _ ≤ ((4 : ENNReal) ^ (p - 1) *
                ((j + 1 : Nat) : ENNReal) ^ (p - 1)) *
              (A * thinRadialTailRawCoefficient n j k q C p alpha) := hpoly
          _ ≤ ((4 : ENNReal) ^ (p - 1) *
                ((j + 1 : Nat) : ENNReal) ^ (p - 1)) *
              (A * ((ENNReal.ofReal C) ^ p *
                    x ^ (-(p * (6 * (n : Real) + 26) + (n : Real) + alpha)) *
                      ((j + 1 : Nat) : ENNReal) ^ p *
                  (dyadicMultiplicativeScale j : ENNReal) ^ ((n : Real) + alpha) *
                    r ^ (j - k - 1) * t ^ q)) := by
              exact mul_le_mul_right (mul_le_mul_right hraw A)
                ((4 : ENNReal) ^ (p - 1) * ((j + 1 : Nat) : ENNReal) ^ (p - 1))
          _ = ((4 : ENNReal) ^ (p - 1) *
                ((j + 1 : Nat) : ENNReal) ^ (p - 1) * A *
                  (ENNReal.ofReal C) ^ p *
                    x ^ (-(p * (6 * (n : Real) + 26) + (n : Real) + alpha)) *
                      ((j + 1 : Nat) : ENNReal) ^ p) *
                (dyadicMultiplicativeScale j : ENNReal) ^ ((n : Real) + alpha) *
                  r ^ (j - k - 1) * t ^ q := by ring
          _ ≤ ((4 : ENNReal) ^ (p - 1) *
                ((j + 1 : Nat) : ENNReal) ^ (p - 1) * A *
                  (ENNReal.ofReal C) ^ p *
                    x ^ (-(p * (6 * (n : Real) + 26) + (n : Real) + alpha)) *
                      ((j + 1 : Nat) : ENNReal) ^ p) *
                (dyadicMultiplicativeScale j : ENNReal) ^ epsilon *
                  r ^ (j - k - 1) * t ^ q := by
              exact mul_le_mul_left
                (mul_le_mul_left
                  (mul_le_mul_right (hscale j)
                    ((4 : ENNReal) ^ (p - 1) * ((j + 1 : Nat) : ENNReal) ^ (p - 1) * A *
                      (ENNReal.ofReal C) ^ p *
                        x ^ (-(p * (6 * (n : Real) + 26) + (n : Real) + alpha)) *
                          ((j + 1 : Nat) : ENNReal) ^ p))
                  (r ^ (j - k - 1)))
                (t ^ q)
          _ = K * J ^ (2 * p - 1) *
                (dyadicMultiplicativeScale j : ENNReal) ^ epsilon *
                  r ^ (j - k - 1) * t ^ q := by
              rw [hJnat]
              calc
                ((4 : ENNReal) ^ (p - 1) * J ^ (p - 1) * A *
                    (ENNReal.ofReal C) ^ p *
                      x ^ (-(p * (6 * (n : Real) + 26) + (n : Real) + alpha)) *
                        J ^ p) *
                    (dyadicMultiplicativeScale j : ENNReal) ^ epsilon *
                      r ^ (j - k - 1) * t ^ q =
                    ((4 : ENNReal) ^ (p - 1) * A *
                      (ENNReal.ofReal C) ^ p *
                        x ^ (-(p * (6 * (n : Real) + 26) + (n : Real) + alpha)) *
                      (J ^ (p - 1) * J ^ p) *
                      (dyadicMultiplicativeScale j : ENNReal) ^ epsilon *
                        r ^ (j - k - 1) * t ^ q) := by ring
                _ = K * J ^ (2 * p - 1) *
                      (dyadicMultiplicativeScale j : ENNReal) ^ epsilon *
                        r ^ (j - k - 1) * t ^ q := by
                      rw [hJcombine]
          _ = K * (ENNReal.ofReal ((j : Real) + 1)) ^ (2 * p - 1) *
                (dyadicMultiplicativeScale j : ENNReal) ^ epsilon *
                  r ^ (j - k - 1) * t ^ q := by
              rfl)
  have hqrange (k : Nat) :
      Finset.range (Nat.log 2 (2 ^ (k + 4)) + 1) = Finset.range (k + 5) := by
    rw [Nat.log_pow (by norm_num : 1 < 2)]
  have hsubset (j : Nat) : Finset.Icc 4 (j - 2) ⊆ Finset.range j := by
    intro k hk
    have hklower : 4 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkupper : k ≤ j - 2 := (Finset.mem_Icc.mp hk).2
    have hjfour : 4 ≤ j :=
      (hklower.trans hkupper).trans (Nat.sub_le _ _)
    have hjpos : 0 < j := lt_of_lt_of_le (by norm_num) hjfour
    exact Finset.mem_range.mpr
      (hkupper.trans_lt (Nat.sub_lt hjpos (by norm_num)))
  refine ⟨Ktail, hKtailTop, ?_⟩
  intro j
  calc
    (∑ k ∈ Finset.Icc 4 (j - 2),
      ((k + 5 : Nat) : ENNReal) ^ (p - 1) *
        ∑ q ∈ Finset.range (Nat.log 2 (2 ^ (k + 4)) + 1),
          (V * ((ENNReal.ofReal (8 : Real)) ^ alpha)⁻¹ *
            ((ENNReal.ofReal 2) ^ p * 2)) *
            thinRadialTailRawCoefficient n j k q C p alpha) =
        ∑ k ∈ Finset.Icc 4 (j - 2),
          ∑ q ∈ Finset.range (k + 5), F j k q := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hqrange k, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range j,
          ∑ q ∈ Finset.range (k + 5), F j k q :=
      Finset.sum_le_sum_of_subset (hsubset j)
    _ ≤ Ktail * (ENNReal.ofReal ((j : Real) + 1)) ^ (2 * p - 1) *
          (dyadicMultiplicativeScale j : ENNReal) ^ epsilon := hcollapse j

/-- The two exact tail coefficient sums emitted by the short buffered shell
reassembly have one common summable raw band rate. -/
theorem exists_thinRadialShellTail_two_raw_band_rate
    {n : Nat} {p alpha epsilon : Real}
    (V : ENNReal) (hVtop : V ≠ ∞)
    (CLower CUpper : Real) (hCLower : 0 < CLower) (hCUpper : 0 < CUpper)
    (hp : 1 < p) (halpha : alpha ≤ 0)
    (hepsilon : 0 ≤ epsilon) (hepsilon_gain : epsilon ≤ (n : Real) + alpha) :
    ∃ Ktail : ENNReal, Ktail ≠ ∞ ∧ ∀ j : Nat,
      ((∑ k ∈ Finset.Icc 4 (j - 2),
        ((k + 5 : Nat) : ENNReal) ^ (p - 1) *
          ∑ q ∈ Finset.range (Nat.log 2 (2 ^ (k + 4)) + 1),
            (V * ((ENNReal.ofReal (8 : Real)) ^ alpha)⁻¹ *
              ((ENNReal.ofReal 2) ^ p * 2)) *
              thinRadialTailRawCoefficient n j k q CLower p alpha) +
        ∑ k ∈ Finset.Icc 4 (j - 2),
          ((k + 5 : Nat) : ENNReal) ^ (p - 1) *
            ∑ q ∈ Finset.range (Nat.log 2 (2 ^ (k + 4)) + 1),
              (V * ((ENNReal.ofReal (8 : Real)) ^ alpha)⁻¹ *
                ((ENNReal.ofReal 2) ^ p * 2)) *
                thinRadialTailRawCoefficient n j k q CUpper p alpha) ≤
        Ktail * (ENNReal.ofReal ((j : Real) + 1)) ^ (2 * p - 1) *
          (dyadicMultiplicativeScale j : ENNReal) ^ epsilon := by
  obtain ⟨KLower, hKLowerTop, hLower⟩ :=
    exists_thinRadialShellTail_single_raw_band_rate V hVtop CLower hCLower.le
      hp halpha hepsilon hepsilon_gain
  obtain ⟨KUpper, hKUpperTop, hUpper⟩ :=
    exists_thinRadialShellTail_single_raw_band_rate V hVtop CUpper hCUpper.le
      hp halpha hepsilon hepsilon_gain
  let Ktail : ENNReal := KLower + KUpper
  have hKtailTop : Ktail ≠ ∞ := by
    dsimp only [Ktail]
    exact ENNReal.add_ne_top.mpr ⟨hKLowerTop, hKUpperTop⟩
  refine ⟨Ktail, hKtailTop, ?_⟩
  intro j
  calc
    _ ≤ KLower * (ENNReal.ofReal ((j : Real) + 1)) ^ (2 * p - 1) *
          (dyadicMultiplicativeScale j : ENNReal) ^ epsilon +
        KUpper * (ENNReal.ofReal ((j : Real) + 1)) ^ (2 * p - 1) *
          (dyadicMultiplicativeScale j : ENNReal) ^ epsilon :=
      add_le_add (hLower j) (hUpper j)
    _ = Ktail * (ENNReal.ofReal ((j : Real) + 1)) ^ (2 * p - 1) *
          (dyadicMultiplicativeScale j : ENNReal) ^ epsilon := by
      dsimp only [Ktail]
      ring

end

end LeanSpherical.HarmonicAnalysis
