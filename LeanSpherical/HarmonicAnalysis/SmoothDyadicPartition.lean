/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SmoothFrequencyCutoff

/-!
# Finite smooth dyadic bandpass sums

Starting from the compactly supported smooth cutoff constructed in
`SmoothFrequencyCutoff`, this file proves the elementary finite telescoping
identity for its dyadic differences.  The localization result concerns the
literal frequency-side functions.  In particular, this is not yet an infinite
Littlewood--Paley expansion or a statement about a spatial maximal operator.
-/

namespace LeanSpherical.HarmonicAnalysis

noncomputable section

/-- The finite sum of literal dyadic differences telescopes. -/
theorem smooth_dyadic_bandpass_sum
    {d : Nat} (phi : SchwartzMap (Euclidean d) ℂ) (N : Nat) (xi : Euclidean d) :
    ∑ j ∈ Finset.range N,
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ j)⁻¹ • xi)) =
      phi (((2 : ℝ) ^ N)⁻¹ • xi) - phi xi := by
  simpa using
    (Finset.sum_range_sub
      (fun j : Nat => phi (((2 : ℝ) ^ j)⁻¹ • xi)) N)

/-- The same finite telescoping identity holds after multiplication by any
literal Fourier-side input. -/
theorem smooth_dyadic_bandpass_multiplier_sum
    {d : Nat} (phi : SchwartzMap (Euclidean d) ℂ) (N : Nat)
    (g : Euclidean d → ℂ) (xi : Euclidean d) :
    ∑ j ∈ Finset.range N,
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ j)⁻¹ • xi)) * g xi =
      (phi (((2 : ℝ) ^ N)⁻¹ • xi) - phi xi) * g xi := by
  rw [← Finset.sum_mul]
  rw [smooth_dyadic_bandpass_sum]

/-- A dyadic difference vanishes below its inner frequency scale. -/
theorem smooth_dyadic_bandpass_eq_zero_of_norm_le
    {d : Nat} {phi : SchwartzMap (Euclidean d) ℂ}
    (hphi : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    {j : Nat} {xi : Euclidean d} (hxi : ‖xi‖ ≤ (2 : ℝ) ^ j) :
    phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ j)⁻¹ • xi) = 0 := by
  have hpj : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) _
  have hpj_succ : 0 < (2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
  have hjle : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (j + 1) := by
    rw [pow_succ]
    nlinarith
  have hsmall_j : ‖((2 : ℝ) ^ j)⁻¹ • xi‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpj)]
    exact (inv_mul_le_one₀ hpj).2 hxi
  have hsmall_succ : ‖((2 : ℝ) ^ (j + 1))⁻¹ • xi‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpj_succ)]
    exact (inv_mul_le_one₀ hpj_succ).2 (hxi.trans hjle)
  rw [hphi _ hsmall_succ, hphi _ hsmall_j]
  norm_num

/-- A dyadic difference vanishes above its outer frequency scale. -/
theorem smooth_dyadic_bandpass_eq_zero_of_le_norm
    {d : Nat} {phi : SchwartzMap (Euclidean d) ℂ}
    (hphi : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    {j : Nat} {xi : Euclidean d} (hxi : (2 : ℝ) ^ (j + 2) ≤ ‖xi‖) :
    phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ j)⁻¹ • xi) = 0 := by
  have hpj : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) _
  have hpj_succ : 0 < (2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
  have hpow_j : (2 : ℝ) ^ j * 2 = (2 : ℝ) ^ (j + 1) := by
    simpa using (pow_succ (2 : ℝ) j).symm
  have hpow_succ : (2 : ℝ) ^ (j + 1) * 2 = (2 : ℝ) ^ (j + 2) := by
    simpa [Nat.add_assoc] using (pow_succ (2 : ℝ) (j + 1)).symm
  have hlarge_j : 2 ≤ ‖((2 : ℝ) ^ j)⁻¹ • xi‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpj)]
    apply (le_inv_mul_iff₀ hpj).2
    calc
      (2 : ℝ) ^ j * 2 = (2 : ℝ) ^ (j + 1) := hpow_j
      _ ≤ (2 : ℝ) ^ (j + 1) * 2 := by nlinarith
      _ = (2 : ℝ) ^ (j + 2) := hpow_succ
      _ ≤ ‖xi‖ := hxi
  have hlarge_succ : 2 ≤ ‖((2 : ℝ) ^ (j + 1))⁻¹ • xi‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpj_succ)]
    apply (le_inv_mul_iff₀ hpj_succ).2
    calc
      (2 : ℝ) ^ (j + 1) * 2 = (2 : ℝ) ^ (j + 2) := hpow_succ
      _ ≤ ‖xi‖ := hxi
  rw [hphi _ hlarge_succ, hphi _ hlarge_j]
  norm_num

/-- A smooth dyadic band-pass supported by the cutoff is genuinely confined
between its inner and outer dyadic scales. -/
theorem smooth_dyadic_bandpass_norm_bounds_of_ne_zero
    {d : Nat} {phi : SchwartzMap (Euclidean d) ℂ}
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    {j : Nat} {xi : Euclidean d}
    (h : phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) -
        phi (((2 : ℝ) ^ j)⁻¹ • xi) ≠ 0) :
    (2 : ℝ) ^ j < ‖xi‖ ∧ ‖xi‖ < (2 : ℝ) ^ (j + 2) := by
  constructor
  · apply lt_of_not_ge
    intro hsmall
    exact h (smooth_dyadic_bandpass_eq_zero_of_norm_le hphi_one hsmall)
  · apply lt_of_not_ge
    intro hlarge
    exact h (smooth_dyadic_bandpass_eq_zero_of_le_norm hphi_zero hlarge)

/-- If the cutoff is pointwise bounded by one, its dyadic difference has
pointwise norm at most two. -/
theorem norm_smooth_dyadic_bandpass_le_two
    {d : Nat} {phi : SchwartzMap (Euclidean d) ℂ}
    (hphi : ∀ xi, ‖phi xi‖ ≤ 1) (j : Nat) (xi : Euclidean d) :
    ‖phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) -
        phi (((2 : ℝ) ^ j)⁻¹ • xi)‖ ≤ 2 := by
  calc
    ‖phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) -
        phi (((2 : ℝ) ^ j)⁻¹ • xi)‖ ≤
        ‖phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi)‖ +
          ‖phi (((2 : ℝ) ^ j)⁻¹ • xi)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add
      (hphi _) (hphi _)
    _ = 2 := by norm_num

/-- A two-scale cutoff can be nonzero only between its inner scale and twice
its outer scale. -/
theorem scaled_cutoff_norm_bounds_of_ne_zero
    {d : Nat} {phi : SchwartzMap (Euclidean d) ℂ}
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    {xi : Euclidean d}
    (h : phi (a⁻¹ • xi) - phi (b⁻¹ • xi) ≠ 0) :
    b < ‖xi‖ ∧ ‖xi‖ < 2 * a := by
  constructor
  · apply lt_of_not_ge
    intro hsmall
    apply h
    have hsmall_b : ‖b⁻¹ • xi‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
      exact (inv_mul_le_one₀ hb).2 hsmall
    have hsmall_a : ‖a⁻¹ • xi‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      exact (inv_mul_le_one₀ ha).2 (hsmall.trans hba)
    rw [hphi_one _ hsmall_a, hphi_one _ hsmall_b]
    norm_num
  · apply lt_of_not_ge
    intro hlarge
    apply h
    have hlarge_a : 2 ≤ ‖a⁻¹ • xi‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      apply (le_inv_mul_iff₀ ha).2
      nlinarith
    have hlarge_b : 2 ≤ ‖b⁻¹ • xi‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
      apply (le_inv_mul_iff₀ hb).2
      calc
        b * 2 ≤ a * 2 := mul_le_mul_of_nonneg_right hba (by norm_num)
        _ = 2 * a := by ring
        _ ≤ ‖xi‖ := hlarge
    rw [hphi_zero _ hlarge_a, hphi_zero _ hlarge_b]
    norm_num

/-- At a fixed frequency, the shifted fat cutoffs needed to localize the
dyadic radius blocks have uniformly bounded square overlap.  This is the
literal integer-scale counting step: no Littlewood--Paley interface is used. -/
theorem finite_relative_dyadic_fat_cutoff_square_sum_le
    {d : Nat} {phi : SchwartzMap (Euclidean d) ℂ}
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphi_norm : ∀ xi, ‖phi xi‖ ≤ 1)
    (j : Nat) (K : Finset ℤ) (xi : Euclidean d) :
    ∑ k ∈ K, ‖phi (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • xi) -
      phi (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • xi)‖ ^ (2 : ℕ) ≤ 24 := by
  let q : ℤ → ℂ := fun k =>
    phi (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • xi) -
      phi (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • xi)
  let S : Finset ℤ := K.filter fun k => q k ≠ 0
  have hSsub : S ⊆ K := Finset.filter_subset _ _
  have hzero : ∀ k ∈ K, k ∉ S → ‖q k‖ ^ (2 : ℕ) = 0 := by
    intro k hk hks
    have hq : q k = 0 := by
      by_contra hq
      exact hks (Finset.mem_filter.mpr ⟨hk, hq⟩)
    simp [hq]
  have hsum : (∑ k ∈ K, ‖q k‖ ^ (2 : ℕ)) =
      ∑ k ∈ S, ‖q k‖ ^ (2 : ℕ) := by
    exact (Finset.sum_subset hSsub hzero).symm
  by_cases hxi0 : xi = 0
  · simp [hxi0]
  have hxi_pos : 0 < ‖xi‖ := norm_pos_iff.mpr hxi0
  obtain ⟨n, hnlo, hnhi⟩ :=
    exists_mem_Ico_zpow (x := ‖xi‖) (y := (2 : ℝ)) hxi_pos (by norm_num)
  have hScard : S.card ≤ 6 := by
    have hSrange : S ⊆ Finset.Icc ((j : ℤ) - 2 - n) ((j : ℤ) + 3 - n) := by
      intro k hk
      have hkS : k ∈ S := hk
      have hq : q k ≠ 0 := (Finset.mem_filter.mp hkS).2
      have hpos_a : 0 < (2 : ℝ) ^ ((j : ℤ) + 3 - k) :=
        zpow_pos (by norm_num) _
      have hpos_b : 0 < (2 : ℝ) ^ ((j : ℤ) - 2 - k) :=
        zpow_pos (by norm_num) _
      have hba : (2 : ℝ) ^ ((j : ℤ) - 2 - k) ≤
          (2 : ℝ) ^ ((j : ℤ) + 3 - k) := by
        exact (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).monotone (by omega)
      have hsupport := scaled_cutoff_norm_bounds_of_ne_zero hphi_one hphi_zero
        hpos_a hpos_b hba hq
      have hupper : 2 * (2 : ℝ) ^ ((j : ℤ) + 3 - k) =
          (2 : ℝ) ^ ((j : ℤ) + 4 - k) := by
        calc
          2 * (2 : ℝ) ^ ((j : ℤ) + 3 - k) =
              (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ ((j : ℤ) + 3 - k) := by norm_num
          _ = (2 : ℝ) ^ ((1 : ℤ) + ((j : ℤ) + 3 - k)) :=
              (zpow_add₀ (by norm_num) _ _).symm
          _ = (2 : ℝ) ^ ((j : ℤ) + 4 - k) := by
            congr 1 <;> ring
      have hleftpow : (2 : ℝ) ^ ((j : ℤ) - 2 - k) <
          (2 : ℝ) ^ (n + 1) :=
        lt_of_lt_of_le hsupport.1 hnhi.le
      have hrightpow : (2 : ℝ) ^ n < (2 : ℝ) ^ ((j : ℤ) + 4 - k) := by
        rw [← hupper]
        exact lt_of_le_of_lt hnlo hsupport.2
      have hleft : (j : ℤ) - 2 - k < n + 1 := by
        rw [zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)] at hleftpow
        exact hleftpow
      have hright : n < (j : ℤ) + 4 - k := by
        rw [zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)] at hrightpow
        exact hrightpow
      exact Finset.mem_Icc.mpr (by omega)
    calc
      S.card ≤ (Finset.Icc ((j : ℤ) - 2 - n) ((j : ℤ) + 3 - n)).card :=
        Finset.card_le_card hSrange
      _ = 6 := by
        rw [Int.card_Icc]
        have hcard : ((j : ℤ) + 3 - n + 1 - ((j : ℤ) - 2 - n)) = 6 := by omega
        rw [hcard]
        rfl
  have hterm : ∀ k ∈ S, ‖q k‖ ^ (2 : ℕ) ≤ (4 : ℝ) := by
    intro k hk
    have hqnorm : ‖q k‖ ≤ 2 := by
      dsimp [q]
      calc
        ‖phi (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • xi) -
            phi (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • xi)‖ ≤
            ‖phi (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • xi)‖ +
              ‖phi (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • xi)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hphi_norm _) (hphi_norm _)
        _ = 2 := by norm_num
    nlinarith [norm_nonneg (q k)]
  calc
    ∑ k ∈ K, ‖phi (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • xi) -
      phi (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • xi)‖ ^ (2 : ℕ) =
        ∑ k ∈ K, ‖q k‖ ^ (2 : ℕ) := by rfl
    _ = ∑ k ∈ S, ‖q k‖ ^ (2 : ℕ) := hsum
    _ ≤ S.card • (4 : ℝ) := Finset.sum_le_card_nsmul S _ 4 hterm
    _ ≤ 6 • (4 : ℝ) := by gcongr
    _ = 24 := by norm_num

/-- The fat cutoff at a dyadic radius block is identically one on the
relative annulus selected by the corresponding bandpass. -/
theorem relative_dyadic_bandpass_fat_cutoff_eq_one
    {d : Nat} {phi : SchwartzMap (Euclidean d) ℂ}
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    {j : Nat} {k : ℤ} {r : ℝ}
    (hr : r ∈ Set.Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
    (xi : Euclidean d)
    (hband : phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • xi)) -
        phi (((2 : ℝ) ^ j)⁻¹ • (r • xi)) ≠ 0) :
    phi (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • xi) -
      phi (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • xi) = 1 := by
  have hsupport := smooth_dyadic_bandpass_norm_bounds_of_ne_zero
    hphi_one hphi_zero hband
  let a : ℝ := (2 : ℝ) ^ ((j : ℤ) + 3 - k)
  let b : ℝ := (2 : ℝ) ^ ((j : ℤ) - 2 - k)
  have hrpos : 0 < r := lt_of_lt_of_le (zpow_pos (by norm_num) k) hr.1
  have ha : 0 < a := by dsimp [a]; exact zpow_pos (by norm_num) _
  have hb : 0 < b := by dsimp [b]; exact zpow_pos (by norm_num) _
  have hscale_a : (2 : ℝ) ^ k * a = (2 : ℝ) ^ (j + 3) := by
    dsimp [a]
    calc
      (2 : ℝ) ^ k * (2 : ℝ) ^ ((j : ℤ) + 3 - k) =
          (2 : ℝ) ^ (k + ((j : ℤ) + 3 - k)) :=
        (zpow_add₀ (by norm_num) _ _).symm
      _ = (2 : ℝ) ^ ((j : ℤ) + 3) := by
        congr 1 <;> ring
      _ = (2 : ℝ) ^ (j + 3) := by norm_cast
  have hscale_b : (2 : ℝ) ^ (k + 1) * (2 * b) = (2 : ℝ) ^ j := by
    dsimp [b]
    calc
      (2 : ℝ) ^ (k + 1) * (2 * (2 : ℝ) ^ ((j : ℤ) - 2 - k)) =
          (2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (1 : ℤ) *
            (2 : ℝ) ^ ((j : ℤ) - 2 - k)) := by norm_num
      _ = (2 : ℝ) ^ ((k + 1) + ((1 : ℤ) + ((j : ℤ) - 2 - k))) := by
        rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      _ = (2 : ℝ) ^ (j : ℤ) := by
        congr 1 <;> ring
      _ = (2 : ℝ) ^ j := by norm_cast
  have hupper_scale : (2 : ℝ) ^ (j + 3) ≤ r * a := by
    calc
      (2 : ℝ) ^ (j + 3) = (2 : ℝ) ^ k * a := hscale_a.symm
      _ ≤ r * a := mul_le_mul_of_nonneg_right hr.1 ha.le
  have hpow_succ : (2 : ℝ) ^ (j + 2) < (2 : ℝ) ^ (j + 3) := by
    rw [show (2 : ℝ) ^ (j + 3) = (2 : ℝ) ^ (j + 2) * 2 by
      rw [← pow_succ]]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (j + 2)]
  have hxi_lt_a : ‖xi‖ < a := by
    refine lt_of_mul_lt_mul_left ?_ hrpos.le
    calc
      r * ‖xi‖ = ‖r • xi‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
      _ < (2 : ℝ) ^ (j + 2) := hsupport.2
      _ < (2 : ℝ) ^ (j + 3) := hpow_succ
      _ ≤ r * a := hupper_scale
  have hinner_scale : r * (2 * b) ≤ (2 : ℝ) ^ j := by
    calc
      r * (2 * b) ≤ (2 : ℝ) ^ (k + 1) * (2 * b) :=
        mul_le_mul_of_nonneg_right hr.2 (mul_nonneg (by norm_num) hb.le)
      _ = (2 : ℝ) ^ j := hscale_b
  have htwo_b_lt : 2 * b < ‖xi‖ := by
    refine lt_of_mul_lt_mul_left ?_ hrpos.le
    calc
      r * (2 * b) ≤ (2 : ℝ) ^ j := hinner_scale
      _ < ‖r • xi‖ := hsupport.1
      _ = r * ‖xi‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
  have houter : phi (a⁻¹ • xi) = 1 := by
    apply hphi_one
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    exact (inv_mul_le_one₀ ha).2 hxi_lt_a.le
  have hinner : phi (b⁻¹ • xi) = 0 := by
    apply hphi_zero
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
    apply (le_inv_mul_iff₀ hb).2
    linarith
  change phi (a⁻¹ • xi) - phi (b⁻¹ • xi) = 1
  rw [houter, hinner]
  norm_num

/-- On a dyadic radius block, inserting the corresponding fat frequency
cutoff leaves the literal relative bandpass multiplier unchanged. -/
theorem relative_dyadic_bandpass_mul_fat_cutoff
    {d : Nat} {phi : SchwartzMap (Euclidean d) ℂ}
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    {j : Nat} {k : ℤ} {r : ℝ}
    (hr : r ∈ Set.Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))
    (xi : Euclidean d) (a : ℂ) (g : Euclidean d → ℂ) :
    a * (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • xi)) -
      phi (((2 : ℝ) ^ j)⁻¹ • (r • xi))) * g xi =
      a * (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • xi)) -
        phi (((2 : ℝ) ^ j)⁻¹ • (r • xi))) *
        (phi (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • xi) -
          phi (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • xi)) * g xi := by
  by_cases hband : phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • xi)) -
      phi (((2 : ℝ) ^ j)⁻¹ • (r • xi)) = 0
  · rw [hband]
    ring
  · rw [relative_dyadic_bandpass_fat_cutoff_eq_one hphi_one hphi_zero hr xi hband]
    ring

/-- There is a Schwartz cutoff whose finite dyadic bandpass sums telescope,
and whose individual differences vanish outside their two-scale frequency
regions. -/
theorem exists_schwartz_frequency_cutoff_finite_dyadic_bandpass (d : Nat) :
    ∃ phi : SchwartzMap (Euclidean d) ℂ,
      (∀ xi, ‖xi‖ ≤ 1 → phi xi = 1) ∧
      (∀ xi, 2 ≤ ‖xi‖ → phi xi = 0) ∧
      (∀ N xi,
        ∑ j ∈ Finset.range N,
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ j)⁻¹ • xi)) =
          phi (((2 : ℝ) ^ N)⁻¹ • xi) - phi xi) ∧
      (∀ j xi, ‖xi‖ ≤ (2 : ℝ) ^ j ∨ (2 : ℝ) ^ (j + 2) ≤ ‖xi‖ →
        phi (((2 : ℝ) ^ (j + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ j)⁻¹ • xi) = 0) := by
  rcases exists_schwartz_frequency_cutoff d with ⟨phi, hphi_one, hphi_zero⟩
  refine ⟨phi, hphi_one, hphi_zero, ?_, ?_⟩
  · intro N xi
    exact smooth_dyadic_bandpass_sum phi N xi
  · intro j xi hxi
    rcases hxi with hxi | hxi
    · exact smooth_dyadic_bandpass_eq_zero_of_norm_le hphi_one hxi
    · exact smooth_dyadic_bandpass_eq_zero_of_le_norm hphi_zero hxi

end

end LeanSpherical.HarmonicAnalysis
