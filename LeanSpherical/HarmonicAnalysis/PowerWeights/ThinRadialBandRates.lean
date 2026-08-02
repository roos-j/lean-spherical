/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.GlobalUnweightedRates

/-!
# Summable rates for strict-negative thin-radial bands

Once the spatial and thin-radius estimates give a raw band moment of the
form `K (j + 1)^p delta_j^epsilon`, this file turns it into the summable
strong-type coefficient required by finite cutoff reassembly.
-/

namespace LeanSpherical.HarmonicAnalysis

open scoped BigOperators ENNReal

noncomputable section

/-- A raw thin-radial band coefficient with a positive dyadic gain has
summable `L^p`-root coefficients. -/
theorem exists_thinRadialRawBand_summable_rate
    {p epsilon : Real} (hp : 0 < p) (hepsilon : 0 < epsilon)
    (K : ENNReal) (hKtop : K ≠ ∞) :
    ∃ C bandSum : ENNReal, C ≠ ∞ ∧ bandSum ≠ ∞ ∧
      (∀ J : Nat, ∑ j ∈ Finset.range J,
        C * ENNReal.ofReal ((j : Real) + 1) *
          (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) ≤ bandSum) ∧
      ∀ j : Nat,
        (K * (ENNReal.ofReal ((j : Real) + 1)) ^ p *
          (dyadicMultiplicativeScale j : ENNReal) ^ epsilon) ^ p⁻¹ ≤
          C * ENNReal.ofReal ((j : Real) + 1) *
            (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) := by
  have hpInv : 0 ≤ p⁻¹ := inv_nonneg.mpr hp.le
  let C : ENNReal := K ^ p⁻¹
  have hCtop : C ≠ ∞ := by
    dsimp only [C]
    exact ENNReal.rpow_ne_top_of_nonneg hpInv hKtop
  obtain ⟨S, hStop, hS⟩ :=
    exists_globalUnweightedDyadicRate_partial_sum_bound hepsilon hp
  refine ⟨C, C * S, hCtop, ENNReal.mul_ne_top hCtop hStop, ?_, ?_⟩
  · intro J
    calc
      ∑ j ∈ Finset.range J, C * ENNReal.ofReal ((j : Real) + 1) *
          (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) =
          C * ∑ j ∈ Finset.range J, ENNReal.ofReal ((j : Real) + 1) *
            (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ ≤ C * S := by
        simpa only [mul_comm] using mul_le_mul_left (hS J) C
  · intro j
    let J : ENNReal := ENNReal.ofReal ((j : Real) + 1)
    let delta : ENNReal := (dyadicMultiplicativeScale j : ENNReal)
    have hpp : p * p⁻¹ = 1 :=
      mul_inv_cancel₀ hp.ne'
    have hdiv : epsilon * p⁻¹ = epsilon / p := by
      rw [div_eq_mul_inv]
    change (K * J ^ p * delta ^ epsilon) ^ p⁻¹ ≤ C * J * delta ^ (epsilon / p)
    calc
      (K * J ^ p * delta ^ epsilon) ^ p⁻¹ =
          K ^ p⁻¹ * (J ^ p) ^ p⁻¹ * (delta ^ epsilon) ^ p⁻¹ := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hpInv,
              ENNReal.mul_rpow_of_nonneg _ _ hpInv]
      _ = C * J * delta ^ (epsilon / p) := by
            rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hpp,
              ENNReal.rpow_one, hdiv]
      _ ≤ C * J * delta ^ (epsilon / p) := le_rfl

/-- The quadratic dyadic rate needed when the finite distance-block
reassembly leaves one extra polynomial loss. -/
private def thinRadialQuadraticDyadicRateNN (epsilon p : Real) (j : Nat) : NNReal :=
  Real.toNNReal (((j : Real) + 1) ^ (2 : Nat)) *
    (dyadicMultiplicativeScale j) ^ (epsilon / p)

private theorem summable_one_add_nat_sq_mul_two_rpow_neg_div {epsilon p : Real}
    (hepsilon : 0 < epsilon) (hp : 0 < p) :
    Summable (fun j : Nat => (((j : Real) + 1) ^ (2 : Nat)) *
      (2 : Real) ^ (-((j : Real) * epsilon / p))) := by
  let rho : Real := (2 : Real) ^ (-epsilon / p)
  have hrho0 : 0 ≤ rho := by
    exact Real.rpow_nonneg (by norm_num) _
  have hexp : -epsilon / p < 0 := by
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hepsilon) hp
  have hrho : rho < 1 := by
    change (2 : Real) ^ (-epsilon / p) < 1
    rw [← Real.rpow_zero (2 : Real)]
    exact (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : Real) < 2))
      hexp
  have hquad : Summable (fun j : Nat => ((j : Real) ^ (2 : Nat)) * rho ^ j) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := Real) 2
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hrho0] using hrho))
  have hlinear : Summable (fun j : Nat => (j : Real) * rho ^ j) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := Real) 1
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hrho0] using hrho))
  have hgeometric : Summable (fun j : Nat => rho ^ j) :=
    summable_geometric_of_lt_one hrho0 hrho
  refine (hquad.add ((hlinear.mul_left 2).add hgeometric)).congr ?_
  intro j
  have hpow : rho ^ j = (2 : Real) ^ (-((j : Real) * epsilon / p)) := by
    change ((2 : Real) ^ (-epsilon / p)) ^ j =
      (2 : Real) ^ (-((j : Real) * epsilon / p))
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
    congr 1
    ring
  rw [hpow]
  ring

private theorem summable_thinRadialQuadraticDyadicRateNN
    {epsilon p : Real} (hepsilon : 0 < epsilon) (hp : 0 < p) :
    Summable (thinRadialQuadraticDyadicRateNN epsilon p) := by
  apply NNReal.summable_coe.mp
  have hsum := summable_one_add_nat_sq_mul_two_rpow_neg_div hepsilon hp
  refine hsum.congr ?_
  intro j
  symm
  change (↑(Real.toNNReal (((j : Real) + 1) ^ (2 : Nat)) *
    (dyadicMultiplicativeScale j) ^ (epsilon / p)) : Real) = _
  rw [NNReal.coe_mul, NNReal.coe_rpow]
  rw [Real.coe_toNNReal (((j : Real) + 1) ^ (2 : Nat)) (sq_nonneg _)]
  change ((j : Real) + 1) ^ (2 : Nat) *
      (((2 : NNReal)⁻¹ ^ j : NNReal) : Real) ^ (epsilon / p) = _
  norm_num [NNReal.coe_pow, NNReal.coe_inv]
  have hhalf : (1 / 2 : Real) = (2 : Real) ^ (-1 : Real) := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    norm_num
  left
  rw [hhalf, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
  congr 1
  ring

private theorem coe_thinRadialQuadraticDyadicRateNN
    {epsilon p : Real} (hepsilon : 0 < epsilon) (hp : 0 < p) (j : Nat) :
    (thinRadialQuadraticDyadicRateNN epsilon p j : ENNReal) =
      (ENNReal.ofReal ((j : Real) + 1) ^ (2 : Nat)) *
        (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) := by
  have hdiv : 0 ≤ epsilon / p := div_nonneg hepsilon.le hp.le
  dsimp only [thinRadialQuadraticDyadicRateNN]
  rw [ENNReal.coe_mul, ENNReal.coe_nnreal_eq]
  rw [Real.coe_toNNReal (((j : Real) + 1) ^ (2 : Nat)) (sq_nonneg _)]
  rw [ENNReal.coe_rpow_of_nonneg _ hdiv,
    ENNReal.ofReal_pow (by positivity : 0 ≤ (j : Real) + 1)]

private theorem exists_thinRadialQuadraticDyadicRate_partial_sum_bound
    {epsilon p : Real} (hepsilon : 0 < epsilon) (hp : 0 < p) :
    ∃ bandSum : ENNReal, bandSum ≠ ∞ ∧ ∀ J : Nat,
      ∑ j ∈ Finset.range J,
        (ENNReal.ofReal ((j : Real) + 1) ^ (2 : Nat)) *
          (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) ≤ bandSum := by
  let b : Nat → NNReal := thinRadialQuadraticDyadicRateNN epsilon p
  let bandSum : ENNReal := ∑' j : Nat, (b j : ENNReal)
  have hsum : Summable b := summable_thinRadialQuadraticDyadicRateNN hepsilon hp
  have htop : bandSum ≠ ∞ := by
    dsimp only [bandSum]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hsum
  refine ⟨bandSum, htop, ?_⟩
  intro J
  calc
    ∑ j ∈ Finset.range J,
        (ENNReal.ofReal ((j : Real) + 1) ^ (2 : Nat)) *
          (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) =
        ∑ j ∈ Finset.range J, (b j : ENNReal) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (coe_thinRadialQuadraticDyadicRateNN hepsilon hp j).symm
    _ ≤ ∑' j : Nat, (b j : ENNReal) := ENNReal.sum_le_tsum _
    _ = bandSum := rfl

/-- A raw thin-radial band coefficient with the quadratic polynomial loss
from distance-block reassembly still has summable `L^p`-root coefficients.
This is the form used for the strict-negative tail bands. -/
theorem exists_thinRadialRawBand_quadratic_summable_rate
    {p epsilon : Real} (hp : 0 < p) (hepsilon : 0 < epsilon)
    (K : ENNReal) (hKtop : K ≠ ∞) :
    ∃ C bandSum : ENNReal, C ≠ ∞ ∧ bandSum ≠ ∞ ∧
      (∀ J : Nat, ∑ j ∈ Finset.range J,
        C * (ENNReal.ofReal ((j : Real) + 1) ^ (2 : Nat)) *
          (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) ≤ bandSum) ∧
      ∀ j : Nat,
        (K * (ENNReal.ofReal ((j : Real) + 1)) ^ (2 * p - 1) *
          (dyadicMultiplicativeScale j : ENNReal) ^ epsilon) ^ p⁻¹ ≤
          C * (ENNReal.ofReal ((j : Real) + 1) ^ (2 : Nat)) *
            (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) := by
  have hpInv : 0 ≤ p⁻¹ := inv_nonneg.mpr hp.le
  let C : ENNReal := K ^ p⁻¹
  have hCtop : C ≠ ∞ := by
    dsimp only [C]
    exact ENNReal.rpow_ne_top_of_nonneg hpInv hKtop
  obtain ⟨S, hStop, hS⟩ :=
    exists_thinRadialQuadraticDyadicRate_partial_sum_bound hepsilon hp
  refine ⟨C, C * S, hCtop, ENNReal.mul_ne_top hCtop hStop, ?_, ?_⟩
  · intro J
    calc
      ∑ j ∈ Finset.range J,
          C * (ENNReal.ofReal ((j : Real) + 1) ^ (2 : Nat)) *
            (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) =
          C * ∑ j ∈ Finset.range J,
            (ENNReal.ofReal ((j : Real) + 1) ^ (2 : Nat)) *
              (dyadicMultiplicativeScale j : ENNReal) ^ (epsilon / p) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ ≤ C * S := by
        simpa only [mul_comm] using mul_le_mul_left (hS J) C
  · intro j
    let J : ENNReal := ENNReal.ofReal ((j : Real) + 1)
    let delta : ENNReal := (dyadicMultiplicativeScale j : ENNReal)
    have hpp : p * p⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
    have hroot : (2 * p - 1) * p⁻¹ = 2 - p⁻¹ := by
      calc
        (2 * p - 1) * p⁻¹ = 2 * (p * p⁻¹) - p⁻¹ := by ring
        _ = 2 - p⁻¹ := by rw [hpp]; ring
    have hdiv : epsilon * p⁻¹ = epsilon / p := by
      rw [div_eq_mul_inv]
    have hJone : (1 : ENNReal) ≤ J := by
      dsimp only [J]
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      show (1 : Real) ≤ (j : Real) + 1
      have hj : (0 : Real) ≤ (j : Real) := by positivity
      linarith
    change (K * J ^ (2 * p - 1) * delta ^ epsilon) ^ p⁻¹ ≤
      C * J ^ (2 : Nat) * delta ^ (epsilon / p)
    calc
      (K * J ^ (2 * p - 1) * delta ^ epsilon) ^ p⁻¹ =
          K ^ p⁻¹ * (J ^ (2 * p - 1)) ^ p⁻¹ *
            (delta ^ epsilon) ^ p⁻¹ := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hpInv,
                ENNReal.mul_rpow_of_nonneg _ _ hpInv]
      _ = C * J ^ (2 - p⁻¹) * delta ^ (epsilon / p) := by
            rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hroot,
              hdiv]
      _ ≤ C * J ^ (2 : Nat) * delta ^ (epsilon / p) := by
            have hJpow : J ^ (2 - p⁻¹) ≤ J ^ (2 : Nat) := by
              rw [← ENNReal.rpow_natCast]
              exact ENNReal.rpow_le_rpow_of_exponent_le hJone (by linarith [hpInv])
            have hC : C * J ^ (2 - p⁻¹) ≤ C * J ^ (2 : Nat) :=
              mul_le_mul_of_nonneg_left hJpow (by positivity)
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_right hC (by positivity)

end

end LeanSpherical.HarmonicAnalysis
