/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4BilinearInterpolation

/-!
# Open-neighbourhood restricted interpolation for the `Q4` argument

The fixed radius-gap shells in the `Q4` proof have crossed endpoint bounds.
Consequently one cannot turn one shell into a positive `TT*` factor.  The
valid non-endpoint argument instead uses restricted estimates at a genuine
two-dimensional neighbourhood of the desired pair of input exponents and
then sums dyadic amplitude atoms.

This file starts that argument with its finite algebraic core.  It is stated
for arbitrary complex bilinear forms, so no positivity or factorization is
being assumed.  Later lemmas turn the four restricted corner estimates into
the separable atomic majorant used here.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open scoped BigOperators

noncomputable section

/-- A finite complex-bilinear expansion is controlled by a separable
nonnegative atomic majorant.  This is the summation step in the usual
open-neighbourhood restricted-type argument. -/
theorem norm_bilinear_finset_sum_le_of_separable_majorant
    {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [Module ℂ F] [Module ℂ G]
    {ι κ : Type*} (B : F →ₗ[ℂ] G →ₗ[ℂ] ℂ)
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → G)
    (c : ι → ℂ) (d : κ → ℂ) (A : ι → ℝ) (D : κ → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (_hA : ∀ i ∈ s, 0 ≤ A i) (_hD : ∀ k ∈ t, 0 ≤ D k)
    (hpair : ∀ i ∈ s, ∀ k ∈ t,
      ‖B (u i) (v k)‖ ≤ C * A i * D k) :
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
      C * (∑ i ∈ s, ‖c i‖ * A i) * (∑ k ∈ t, ‖d k‖ * D k) := by
  have hmain := norm_bilinear_finset_sum_le B s t u v c d
    (fun i k => C * A i * D k) hpair
  calc
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
        ∑ i ∈ s, ∑ k ∈ t, ‖c i‖ * ‖d k‖ * (C * A i * D k) := hmain
    _ = ∑ i ∈ s, ∑ k ∈ t,
        C * (‖c i‖ * A i) * (‖d k‖ * D k) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ i ∈ s,
        C * (‖c i‖ * A i) * (∑ k ∈ t, ‖d k‖ * D k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
    _ = C * (∑ i ∈ s, ‖c i‖ * A i) * (∑ k ∈ t, ‖d k‖ * D k) := by
      rw [show (∑ i ∈ s,
          C * (‖c i‖ * A i) * (∑ k ∈ t, ‖d k‖ * D k)) =
          C * (∑ i ∈ s, (‖c i‖ * A i) * (∑ k ∈ t, ‖d k‖ * D k)) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring]
      rw [← Finset.sum_mul]
      ring

/-- The preceding finite summation inequality in the form used after a
dyadic level decomposition: the coefficient is absorbed into each atomic
majorant. -/
theorem norm_bilinear_finset_sum_le_of_weighted_separable_majorant
    {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [Module ℂ F] [Module ℂ G]
    {ι κ : Type*} (B : F →ₗ[ℂ] G →ₗ[ℂ] ℂ)
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → G)
    (a : ι → ℂ) (b : κ → ℂ) (A : ι → ℝ) (D : κ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ i ∈ s, 0 ≤ A i) (hD : ∀ k ∈ t, 0 ≤ D k)
    (hpair : ∀ i ∈ s, ∀ k ∈ t,
      ‖B (u i) (v k)‖ ≤ C * A i * D k) :
    ‖B (∑ i ∈ s, a i • u i) (∑ k ∈ t, b k • v k)‖ ≤
      C * (∑ i ∈ s, ‖a i‖ * A i) * (∑ k ∈ t, ‖b k‖ * D k) :=
  norm_bilinear_finset_sum_le_of_separable_majorant
    B s t u v a b A D C hC hA hD hpair

/-! ## The one-dimensional dyadic decay calculation -/

/-- The normalized `Lᵖ` mass of one dyadic atom converts a restricted
power `a` into the corresponding exponential level weight.  Choosing `a`
above or below `p⁻¹` on the two sides of level zero is exactly what produces
the geometric decay in the open-neighbourhood argument. -/
theorem dyadic_mass_scaled_rpow_le
    {m p a z : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a)
    (henergy : (2 : ℝ) ^ (z * p) * m ≤ 1) :
    (2 : ℝ) ^ z * m ^ a ≤ (2 : ℝ) ^ ((1 - p * a) * z) := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hpow_pos : 0 < (2 : ℝ) ^ (z * p) :=
    Real.rpow_pos_of_pos htwo _
  have hm_le : m ≤ (2 : ℝ) ^ (-(z * p)) := by
    rw [Real.rpow_neg htwo.le]
    rw [← one_div]
    apply (le_div_iff₀ hpow_pos).2
    simpa [mul_comm] using henergy
  have hpow_le : m ^ a ≤ ((2 : ℝ) ^ (-(z * p))) ^ a :=
    Real.rpow_le_rpow hm hm_le ha
  calc
    (2 : ℝ) ^ z * m ^ a ≤
        (2 : ℝ) ^ z * ((2 : ℝ) ^ (-(z * p))) ^ a :=
      mul_le_mul_of_nonneg_left hpow_le (Real.rpow_nonneg htwo.le _)
    _ = (2 : ℝ) ^ z * (2 : ℝ) ^ ((-(z * p)) * a) := by
      rw [← Real.rpow_mul htwo.le]
    _ = (2 : ℝ) ^ (z + (-(z * p)) * a) := by
      rw [← Real.rpow_add htwo]
    _ = (2 : ℝ) ^ ((1 - p * a) * z) := by
      congr 1
      ring

/-- Every finite partial sum of a nonnegative geometric series is bounded by
its usual infinite-series value. -/
theorem finset_sum_geometric_le
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : Finset ℕ) :
    (∑ n ∈ s, r ^ n) ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum s
    (fun n hn => pow_nonneg hr0 _)

/-- The positive dyadic levels are geometrically summable when their chosen
restricted exponent lies strictly above the target reciprocal exponent. -/
theorem finset_sum_positive_level_decay_le
    {p a : ℝ} (hp : 0 < p) (ha : p⁻¹ < a) (s : Finset ℕ) :
    (∑ n ∈ s, (2 : ℝ) ^ ((1 - p * a) * (n : ℝ))) ≤
      (1 - (2 : ℝ) ^ (1 - p * a))⁻¹ := by
  let r : ℝ := (2 : ℝ) ^ (1 - p * a)
  have hpa : 1 < p * a := by
    calc
      1 = p * p⁻¹ := (mul_inv_cancel₀ hp.ne').symm
      _ < p * a := mul_lt_mul_of_pos_left ha hp
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  calc
    (∑ n ∈ s, (2 : ℝ) ^ ((1 - p * a) * (n : ℝ))) =
        ∑ n ∈ s, r ^ n := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [r]
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    _ ≤ (1 - r)⁻¹ := finset_sum_geometric_le hr0 hr1 s
    _ = (1 - (2 : ℝ) ^ (1 - p * a))⁻¹ := rfl

/-- The negative dyadic levels are geometrically summable when their chosen
restricted exponent lies strictly below the target reciprocal exponent. -/
theorem finset_sum_negative_level_decay_le
    {p a : ℝ} (hp : 0 < p) (ha : a < p⁻¹) (s : Finset ℕ) :
    (∑ n ∈ s, (2 : ℝ) ^ ((1 - p * a) * (-(n : ℝ)))) ≤
      (1 - (2 : ℝ) ^ (-(1 - p * a)))⁻¹ := by
  let r : ℝ := (2 : ℝ) ^ (-(1 - p * a))
  have hpa : p * a < 1 := by
    calc
      p * a < p * p⁻¹ := mul_lt_mul_of_pos_left ha hp
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  calc
    (∑ n ∈ s, (2 : ℝ) ^ ((1 - p * a) * (-(n : ℝ)))) =
        ∑ n ∈ s, r ^ n := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [r]
      have hexp : (1 - p * a) * (-(n : ℝ)) =
          (-(1 - p * a)) * (n : ℝ) := by ring
      rw [hexp, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    _ ≤ (1 - r)⁻¹ := finset_sum_geometric_le hr0 hr1 s
    _ = (1 - (2 : ℝ) ^ (-(1 - p * a)))⁻¹ := rfl

/-- Finite normalized dyadic atoms obey the strong bilinear estimate dictated
by their selected restricted exponents.  This is the exact finite/simple
function form of the open-neighbourhood interpolation step.  The only
remaining bound in the conclusion is a pair of geometric level sums; when
the selected exponents lie strictly on opposite sides of `p⁻¹` and `q⁻¹`,
those sums are uniformly bounded by elementary geometric-series estimates.

No positivity of `B` is assumed: absolute values enter only after the finite
bilinear expansion. -/
theorem norm_bilinear_finset_sum_le_of_normalized_dyadic_atoms
    {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [Module ℂ F] [Module ℂ G]
    {ι κ : Type*} (B : F →ₗ[ℂ] G →ₗ[ℂ] ℂ)
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → G)
    (c : ι → ℂ) (d : κ → ℂ)
    (m : ι → ℝ) (n : κ → ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (z : ι → ℝ) (w : κ → ℝ) (p q C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ i ∈ s, 0 ≤ m i) (hn : ∀ k ∈ t, 0 ≤ n k)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ k ∈ t, 0 ≤ b k)
    (hlevelc : ∀ i ∈ s, ‖c i‖ = (2 : ℝ) ^ z i)
    (hleveld : ∀ k ∈ t, ‖d k‖ = (2 : ℝ) ^ w k)
    (hmass : ∀ i ∈ s, (2 : ℝ) ^ (z i * p) * m i ≤ 1)
    (hnorm : ∀ k ∈ t, (2 : ℝ) ^ (w k * q) * n k ≤ 1)
    (hpair : ∀ i ∈ s, ∀ k ∈ t,
      ‖B (u i) (v k)‖ ≤ C * (m i) ^ (a i) * (n k) ^ (b k)) :
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
      C * (∑ i ∈ s, (2 : ℝ) ^ ((1 - p * a i) * z i)) *
        (∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b k) * w k)) := by
  have hfirst := norm_bilinear_finset_sum_le_of_separable_majorant
    B s t u v c d (fun i => (m i) ^ (a i)) (fun k => (n k) ^ (b k)) C
    hC
    (fun i hi => Real.rpow_nonneg (hm i hi) _)
    (fun k hk => Real.rpow_nonneg (hn k hk) _)
    hpair
  have hleft :
      (∑ i ∈ s, ‖c i‖ * (m i) ^ (a i)) ≤
        ∑ i ∈ s, (2 : ℝ) ^ ((1 - p * a i) * z i) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [hlevelc i hi]
    exact dyadic_mass_scaled_rpow_le (hm i hi) (ha i hi) (hmass i hi)
  have hright :
      (∑ k ∈ t, ‖d k‖ * (n k) ^ (b k)) ≤
        ∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b k) * w k) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [hleveld k hk]
    exact dyadic_mass_scaled_rpow_le (hn k hk) (hb k hk) (hnorm k hk)
  have hright_nonneg : 0 ≤ ∑ k ∈ t, ‖d k‖ * (n k) ^ (b k) := by
    exact Finset.sum_nonneg fun k hk =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hn k hk) _)
  have hleft_decay_nonneg :
      0 ≤ ∑ i ∈ s, (2 : ℝ) ^ ((1 - p * a i) * z i) := by
    exact Finset.sum_nonneg fun i hi => Real.rpow_nonneg (by norm_num) _
  calc
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
        C * (∑ i ∈ s, ‖c i‖ * (m i) ^ (a i)) *
          (∑ k ∈ t, ‖d k‖ * (n k) ^ (b k)) := hfirst
    _ ≤ C * (∑ i ∈ s, (2 : ℝ) ^ ((1 - p * a i) * z i)) *
          (∑ k ∈ t, ‖d k‖ * (n k) ^ (b k)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hleft hC) hright_nonneg
    _ ≤ C * (∑ i ∈ s, (2 : ℝ) ^ ((1 - p * a i) * z i)) *
          (∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b k) * w k)) := by
      exact mul_le_mul_of_nonneg_left hright
        (mul_nonneg hC hleft_decay_nonneg)

/-- The positive-positive quadrant of the finite restricted interpolation
argument.  The upper-right corner of the exponent rectangle controls it. -/
theorem norm_bilinear_finset_sum_le_of_positive_dyadic_atoms
    {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [Module ℂ F] [Module ℂ G]
    (B : F →ₗ[ℂ] G →ₗ[ℂ] ℂ)
    (s : Finset ℕ) (t : Finset ℕ) (u : ℕ → F) (v : ℕ → G)
    (c : ℕ → ℂ) (d : ℕ → ℂ) (m : ℕ → ℝ) (n : ℕ → ℝ)
    (p q a b C : ℝ) (hp : 0 < p) (hq : 0 < q)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : p⁻¹ < a) (hb : q⁻¹ < b) (hC : 0 ≤ C)
    (hm : ∀ i ∈ s, 0 ≤ m i) (hn : ∀ k ∈ t, 0 ≤ n k)
    (hlevelc : ∀ i ∈ s, ‖c i‖ = (2 : ℝ) ^ (i : ℝ))
    (hleveld : ∀ k ∈ t, ‖d k‖ = (2 : ℝ) ^ (k : ℝ))
    (hmass : ∀ i ∈ s, (2 : ℝ) ^ ((i : ℝ) * p) * m i ≤ 1)
    (hnorm : ∀ k ∈ t, (2 : ℝ) ^ ((k : ℝ) * q) * n k ≤ 1)
    (hpair : ∀ i ∈ s, ∀ k ∈ t,
      ‖B (u i) (v k)‖ ≤ C * (m i) ^ a * (n k) ^ b) :
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
      C * (1 - (2 : ℝ) ^ (1 - p * a))⁻¹ *
        (1 - (2 : ℝ) ^ (1 - q * b))⁻¹ := by
  have hmain := norm_bilinear_finset_sum_le_of_normalized_dyadic_atoms
    B s t u v c d m n (fun _ => a) (fun _ => b)
    (fun i => (i : ℝ)) (fun k => (k : ℝ)) p q C hC hm hn
    (fun i hi => ha0) (fun k hk => hb0) hlevelc hleveld hmass hnorm
    (by
      intro i hi k hk
      simpa using hpair i hi k hk)
  have hleft := finset_sum_positive_level_decay_le hp ha s
  have hright := finset_sum_positive_level_decay_le hq hb t
  have hright_nonneg : 0 ≤ ∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b) * (k : ℝ)) :=
    Finset.sum_nonneg fun k hk => Real.rpow_nonneg (by norm_num) _
  have hleft_bound_nonneg : 0 ≤ (1 - (2 : ℝ) ^ (1 - p * a))⁻¹ := by
    exact (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (by norm_num) _).trans hleft
  calc
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
        C * (∑ i ∈ s, (2 : ℝ) ^ ((1 - p * a) * (i : ℝ))) *
          (∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b) * (k : ℝ))) := by
      simpa using hmain
    _ ≤ C * (1 - (2 : ℝ) ^ (1 - p * a))⁻¹ *
          (∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b) * (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hleft hC) hright_nonneg
    _ ≤ C * (1 - (2 : ℝ) ^ (1 - p * a))⁻¹ *
          (1 - (2 : ℝ) ^ (1 - q * b))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hright
        (mul_nonneg hC hleft_bound_nonneg)

/-- The negative-negative quadrant of the finite restricted interpolation
argument.  The lower-left corner of the exponent rectangle controls it. -/
theorem norm_bilinear_finset_sum_le_of_negative_dyadic_atoms
    {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [Module ℂ F] [Module ℂ G]
    (B : F →ₗ[ℂ] G →ₗ[ℂ] ℂ)
    (s : Finset ℕ) (t : Finset ℕ) (u : ℕ → F) (v : ℕ → G)
    (c : ℕ → ℂ) (d : ℕ → ℂ) (m : ℕ → ℝ) (n : ℕ → ℝ)
    (p q a b C : ℝ) (hp : 0 < p) (hq : 0 < q)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a < p⁻¹) (hb : b < q⁻¹) (hC : 0 ≤ C)
    (hm : ∀ i ∈ s, 0 ≤ m i) (hn : ∀ k ∈ t, 0 ≤ n k)
    (hlevelc : ∀ i ∈ s, ‖c i‖ = (2 : ℝ) ^ (-(i : ℝ)))
    (hleveld : ∀ k ∈ t, ‖d k‖ = (2 : ℝ) ^ (-(k : ℝ)))
    (hmass : ∀ i ∈ s, (2 : ℝ) ^ ((-(i : ℝ)) * p) * m i ≤ 1)
    (hnorm : ∀ k ∈ t, (2 : ℝ) ^ ((-(k : ℝ)) * q) * n k ≤ 1)
    (hpair : ∀ i ∈ s, ∀ k ∈ t,
      ‖B (u i) (v k)‖ ≤ C * (m i) ^ a * (n k) ^ b) :
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
      C * (1 - (2 : ℝ) ^ (-(1 - p * a)))⁻¹ *
        (1 - (2 : ℝ) ^ (-(1 - q * b)))⁻¹ := by
  have hmain := norm_bilinear_finset_sum_le_of_normalized_dyadic_atoms
    B s t u v c d m n (fun _ => a) (fun _ => b)
    (fun i => -(i : ℝ)) (fun k => -(k : ℝ)) p q C hC hm hn
    (fun i hi => ha0) (fun k hk => hb0) hlevelc hleveld hmass hnorm
    (by
      intro i hi k hk
      simpa using hpair i hi k hk)
  have hleft := finset_sum_negative_level_decay_le hp ha s
  have hright := finset_sum_negative_level_decay_le hq hb t
  have hright_nonneg : 0 ≤ ∑ k ∈ t,
      (2 : ℝ) ^ ((1 - q * b) * (-(k : ℝ))) :=
    Finset.sum_nonneg fun k hk => Real.rpow_nonneg (by norm_num) _
  have hleft_bound_nonneg : 0 ≤ (1 - (2 : ℝ) ^ (-(1 - p * a)))⁻¹ := by
    exact (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (by norm_num) _).trans hleft
  calc
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
        C * (∑ i ∈ s, (2 : ℝ) ^ ((1 - p * a) * (-(i : ℝ)))) *
          (∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b) * (-(k : ℝ)))) := by
      simpa using hmain
    _ ≤ C * (1 - (2 : ℝ) ^ (-(1 - p * a)))⁻¹ *
          (∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b) * (-(k : ℝ)))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hleft hC) hright_nonneg
    _ ≤ C * (1 - (2 : ℝ) ^ (-(1 - p * a)))⁻¹ *
          (1 - (2 : ℝ) ^ (-(1 - q * b)))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hright
        (mul_nonneg hC hleft_bound_nonneg)

/-- The positive-negative quadrant of the finite restricted interpolation
argument.  It uses the upper-left corner of the exponent rectangle. -/
theorem norm_bilinear_finset_sum_le_of_positive_negative_dyadic_atoms
    {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [Module ℂ F] [Module ℂ G]
    (B : F →ₗ[ℂ] G →ₗ[ℂ] ℂ)
    (s : Finset ℕ) (t : Finset ℕ) (u : ℕ → F) (v : ℕ → G)
    (c : ℕ → ℂ) (d : ℕ → ℂ) (m : ℕ → ℝ) (n : ℕ → ℝ)
    (p q a b C : ℝ) (hp : 0 < p) (hq : 0 < q)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : p⁻¹ < a) (hb : b < q⁻¹) (hC : 0 ≤ C)
    (hm : ∀ i ∈ s, 0 ≤ m i) (hn : ∀ k ∈ t, 0 ≤ n k)
    (hlevelc : ∀ i ∈ s, ‖c i‖ = (2 : ℝ) ^ (i : ℝ))
    (hleveld : ∀ k ∈ t, ‖d k‖ = (2 : ℝ) ^ (-(k : ℝ)))
    (hmass : ∀ i ∈ s, (2 : ℝ) ^ ((i : ℝ) * p) * m i ≤ 1)
    (hnorm : ∀ k ∈ t, (2 : ℝ) ^ ((-(k : ℝ)) * q) * n k ≤ 1)
    (hpair : ∀ i ∈ s, ∀ k ∈ t,
      ‖B (u i) (v k)‖ ≤ C * (m i) ^ a * (n k) ^ b) :
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
      C * (1 - (2 : ℝ) ^ (1 - p * a))⁻¹ *
        (1 - (2 : ℝ) ^ (-(1 - q * b)))⁻¹ := by
  have hmain := norm_bilinear_finset_sum_le_of_normalized_dyadic_atoms
    B s t u v c d m n (fun _ => a) (fun _ => b)
    (fun i => (i : ℝ)) (fun k => -(k : ℝ)) p q C hC hm hn
    (fun i hi => ha0) (fun k hk => hb0) hlevelc hleveld hmass hnorm
    (by
      intro i hi k hk
      simpa using hpair i hi k hk)
  have hleft := finset_sum_positive_level_decay_le hp ha s
  have hright := finset_sum_negative_level_decay_le hq hb t
  have hright_nonneg : 0 ≤ ∑ k ∈ t,
      (2 : ℝ) ^ ((1 - q * b) * (-(k : ℝ))) :=
    Finset.sum_nonneg fun k hk => Real.rpow_nonneg (by norm_num) _
  have hleft_bound_nonneg : 0 ≤ (1 - (2 : ℝ) ^ (1 - p * a))⁻¹ := by
    exact (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (by norm_num) _).trans hleft
  calc
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
        C * (∑ i ∈ s, (2 : ℝ) ^ ((1 - p * a) * (i : ℝ))) *
          (∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b) * (-(k : ℝ)))) := by
      simpa using hmain
    _ ≤ C * (1 - (2 : ℝ) ^ (1 - p * a))⁻¹ *
          (∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b) * (-(k : ℝ)))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hleft hC) hright_nonneg
    _ ≤ C * (1 - (2 : ℝ) ^ (1 - p * a))⁻¹ *
          (1 - (2 : ℝ) ^ (-(1 - q * b)))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hright
        (mul_nonneg hC hleft_bound_nonneg)

/-- The negative-positive quadrant of the finite restricted interpolation
argument.  It uses the lower-right corner of the exponent rectangle. -/
theorem norm_bilinear_finset_sum_le_of_negative_positive_dyadic_atoms
    {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [Module ℂ F] [Module ℂ G]
    (B : F →ₗ[ℂ] G →ₗ[ℂ] ℂ)
    (s : Finset ℕ) (t : Finset ℕ) (u : ℕ → F) (v : ℕ → G)
    (c : ℕ → ℂ) (d : ℕ → ℂ) (m : ℕ → ℝ) (n : ℕ → ℝ)
    (p q a b C : ℝ) (hp : 0 < p) (hq : 0 < q)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a < p⁻¹) (hb : q⁻¹ < b) (hC : 0 ≤ C)
    (hm : ∀ i ∈ s, 0 ≤ m i) (hn : ∀ k ∈ t, 0 ≤ n k)
    (hlevelc : ∀ i ∈ s, ‖c i‖ = (2 : ℝ) ^ (-(i : ℝ)))
    (hleveld : ∀ k ∈ t, ‖d k‖ = (2 : ℝ) ^ (k : ℝ))
    (hmass : ∀ i ∈ s, (2 : ℝ) ^ ((-(i : ℝ)) * p) * m i ≤ 1)
    (hnorm : ∀ k ∈ t, (2 : ℝ) ^ ((k : ℝ) * q) * n k ≤ 1)
    (hpair : ∀ i ∈ s, ∀ k ∈ t,
      ‖B (u i) (v k)‖ ≤ C * (m i) ^ a * (n k) ^ b) :
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
      C * (1 - (2 : ℝ) ^ (-(1 - p * a)))⁻¹ *
        (1 - (2 : ℝ) ^ (1 - q * b))⁻¹ := by
  have hmain := norm_bilinear_finset_sum_le_of_normalized_dyadic_atoms
    B s t u v c d m n (fun _ => a) (fun _ => b)
    (fun i => -(i : ℝ)) (fun k => (k : ℝ)) p q C hC hm hn
    (fun i hi => ha0) (fun k hk => hb0) hlevelc hleveld hmass hnorm
    (by
      intro i hi k hk
      simpa using hpair i hi k hk)
  have hleft := finset_sum_negative_level_decay_le hp ha s
  have hright := finset_sum_positive_level_decay_le hq hb t
  have hright_nonneg : 0 ≤ ∑ k ∈ t,
      (2 : ℝ) ^ ((1 - q * b) * (k : ℝ)) :=
    Finset.sum_nonneg fun k hk => Real.rpow_nonneg (by norm_num) _
  have hleft_bound_nonneg : 0 ≤ (1 - (2 : ℝ) ^ (-(1 - p * a)))⁻¹ := by
    exact (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (by norm_num) _).trans hleft
  calc
    ‖B (∑ i ∈ s, c i • u i) (∑ k ∈ t, d k • v k)‖ ≤
        C * (∑ i ∈ s, (2 : ℝ) ^ ((1 - p * a) * (-(i : ℝ)))) *
          (∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b) * (k : ℝ))) := by
      simpa using hmain
    _ ≤ C * (1 - (2 : ℝ) ^ (-(1 - p * a)))⁻¹ *
          (∑ k ∈ t, (2 : ℝ) ^ ((1 - q * b) * (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hleft hC) hright_nonneg
    _ ≤ C * (1 - (2 : ℝ) ^ (-(1 - p * a)))⁻¹ *
          (1 - (2 : ℝ) ^ (1 - q * b))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hright
        (mul_nonneg hC hleft_bound_nonneg)

/-- Assemble the four sign quadrants of a bilinear dyadic decomposition.
Together with the four preceding lemmas, this is the finite/simple-function
``restricted estimates on a rectangle imply a strong interior estimate''
argument. -/
theorem norm_bilinear_add_add_le_of_four_bounds
    {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [Module ℂ F] [Module ℂ G]
    (B : F →ₗ[ℂ] G →ₗ[ℂ] ℂ)
    (fPlus fMinus : F) (gPlus gMinus : G)
    (APlus AMinus DPlus DMinus C : ℝ)
    (hpp : ‖B fPlus gPlus‖ ≤ C * APlus * DPlus)
    (hpm : ‖B fPlus gMinus‖ ≤ C * APlus * DMinus)
    (hmp : ‖B fMinus gPlus‖ ≤ C * AMinus * DPlus)
    (hmm : ‖B fMinus gMinus‖ ≤ C * AMinus * DMinus) :
    ‖B (fPlus + fMinus) (gPlus + gMinus)‖ ≤
      C * (APlus + AMinus) * (DPlus + DMinus) := by
  have hexpand :
      B (fPlus + fMinus) (gPlus + gMinus) =
        ((B fPlus gPlus + B fPlus gMinus) + B fMinus gPlus) +
          B fMinus gMinus := by
    simp only [map_add, LinearMap.add_apply]
    ring
  rw [hexpand]
  calc
    ‖((B fPlus gPlus + B fPlus gMinus) + B fMinus gPlus) +
        B fMinus gMinus‖ ≤
        ‖(B fPlus gPlus + B fPlus gMinus) + B fMinus gPlus‖ +
          ‖B fMinus gMinus‖ := norm_add_le _ _
    _ ≤ (‖B fPlus gPlus + B fPlus gMinus‖ + ‖B fMinus gPlus‖) +
          ‖B fMinus gMinus‖ := by
      exact add_le_add_left
        (norm_add_le (B fPlus gPlus + B fPlus gMinus) (B fMinus gPlus))
        ‖B fMinus gMinus‖
    _ ≤ ((‖B fPlus gPlus‖ + ‖B fPlus gMinus‖) + ‖B fMinus gPlus‖) +
          ‖B fMinus gMinus‖ := by
      exact add_le_add_left
        (add_le_add_left (norm_add_le (B fPlus gPlus) (B fPlus gMinus))
          ‖B fMinus gPlus‖)
        ‖B fMinus gMinus‖
    _ ≤ ((C * APlus * DPlus + C * APlus * DMinus) +
          C * AMinus * DPlus) + C * AMinus * DMinus := by
      exact add_le_add (add_le_add (add_le_add hpp hpm) hmp) hmm
    _ = C * (APlus + AMinus) * (DPlus + DMinus) := by ring

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
