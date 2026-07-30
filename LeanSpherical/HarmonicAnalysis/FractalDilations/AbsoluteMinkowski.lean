/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.AbsoluteAssembly

/-!
# The Minkowski interpolation calculation for absolute annuli

This module packages the exact balancing calculation behind the diagonal
Minkowski estimate.  The cover construction supplies the two endpoint
constants; choosing the amplitude split at `R^n` gives the common factor
`R^(α + n - n p)`.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory FourierTransform Metric Set
open scoped FourierTransform Topology

noncomputable section

/-- Interpolating the two Minkowski endpoint bounds at the balancing scale
`R^n` produces the diagonal power `R^(α+n-np)`. -/
theorem unnormalized_absolute_minkowski_lintegral_of_endpoints
    {n : ℕ} {E : Set ℝ} {R α c₁ c₂ p : ℝ}
    (hn : 2 ≤ n) (hR : 0 < R) (hα : 0 ≤ α)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hp1 : 1 < p) (hp2 : p < 2)
    (ψ : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hEpos : E ⊆ Ioi (0 : ℝ))
    (hone : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g) 1 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g x‖) ≤
        (c₁ * R ^ α) * ∫ x : Euclidean (n + 1), ‖g x‖)
    (htwo : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g) 2 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g x‖ ^ (2 : ℕ)) ≤
        (c₂ * R ^ (α - n)) *
          ∫ x : Euclidean (n + 1), ‖g x‖ ^ (2 : ℕ))
    (f : SchwartzMap (Euclidean (n + 1)) ℂ) :
    let a₁ : ℝ := (p - 1)⁻¹ + (3 - p)⁻¹
    let a₂ : ℝ := ((1 : ℝ) / 4) * p⁻¹ + (2 - p)⁻¹
    (∫⁻ x : Euclidean (n + 1), ENNReal.ofReal
      ((unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ f x) ^ p)) ≤
      ENNReal.ofReal (p * (4 * c₂ * a₂ + 2 * c₁ * a₁)) *
        (ENNReal.ofReal R) ^ (α + n - n * p) *
          ∫⁻ x : Euclidean (n + 1),
            (ENNReal.ofReal ‖(f : Euclidean (n + 1) → ℂ) x‖) ^ p := by
  dsimp only
  let a₁ : ℝ := (p - 1)⁻¹ + (3 - p)⁻¹
  let a₂ : ℝ := ((1 : ℝ) / 4) * p⁻¹ + (2 - p)⁻¹
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hpminus : 0 < p - 1 := by linarith
  have htwo_pos : 0 < 2 - p := by linarith
  have hthree : 0 < 3 - p := by linarith
  have ha₁ : 0 ≤ a₁ := by
    dsimp only [a₁]
    positivity
  have ha₂ : 0 ≤ a₂ := by
    dsimp only [a₂]
    positivity
  have htail₁ : ENNReal.ofReal a₁ =
      (ENNReal.ofReal (p - 1))⁻¹ + (ENNReal.ofReal (3 - p))⁻¹ := by
    dsimp only [a₁]
    rw [ENNReal.ofReal_add (inv_nonneg.mpr hpminus.le)
      (inv_nonneg.mpr hthree.le), ENNReal.ofReal_inv_of_pos hpminus,
      ENNReal.ofReal_inv_of_pos hthree]
  have htail₂ : ENNReal.ofReal a₂ =
      ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹ +
        (ENNReal.ofReal (2 - p))⁻¹ := by
    dsimp only [a₂]
    rw [ENNReal.ofReal_add
      (mul_nonneg (by norm_num) (inv_nonneg.mpr hp0.le))
      (inv_nonneg.mpr htwo_pos.le)]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
      ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_inv_of_pos htwo_pos]
  have hinterp := unnormalizedFractalDyadicBandpass_lintegral_of_one_two
    (d := n + 1) (E := E) (by omega) hEpos ψ
    (c₁ := c₁ * R ^ α) (c₂ := c₂ * R ^ (α - n))
    (mul_nonneg hc₁ (Real.rpow_nonneg hR.le _))
    (mul_nonneg hc₂ (Real.rpow_nonneg hR.le _))
    hone htwo hp1 hp2 f (R ^ (n : ℝ))
    (Real.rpow_pos_of_pos hR _)
  rw [← htail₂, ← htail₁] at hinterp
  calc
    _ ≤ _ := hinterp
    _ = _ := minkowski_balance_one_two hR hp0 hc₁ hc₂ ha₁ ha₂ _

/-- Convert an unnormalised dyadic moment bound into the corresponding bound
for the normalized restricted maximal piece. -/
theorem normalized_absolute_bandpass_moment_of_unnormalized_bound
    {d : ℕ} {E : Set ℝ} {ψ f : SchwartzMap (Euclidean d) ℂ}
    {p K I : ℝ} (hd0 : 0 < d) (hp0 : 0 < p)
    (hKI : 0 ≤ K * I)
    (hbound : (∫⁻ x : Euclidean d, ENNReal.ofReal
      ((unnormalizedFractalDyadicBandpassMaximal d E ψ f x) ^ p)) ≤
        ENNReal.ofReal (K * I)) :
    MemLp (fractalDyadicBandpassMaximal d E ψ f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d,
        (fractalDyadicBandpassMaximal d E ψ f x) ^ p) ≤
        ((surfaceMass d)⁻¹) ^ p * K * I := by
  let U : Euclidean d → ℝ := unnormalizedFractalDyadicBandpassMaximal d E ψ f
  let M : Euclidean d → ℝ := fractalDyadicBandpassMaximal d E ψ f
  have hU0 (x : Euclidean d) : 0 ≤ U x :=
    unnormalizedFractalDyadicBandpassMaximal_nonneg E ψ f x
  have hM0 (x : Euclidean d) : 0 ≤ M x :=
    fractalDyadicBandpassMaximal_nonneg E ψ f x
  have hUmeas : AEStronglyMeasurable U volume :=
    (measurable_unnormalizedFractalDyadicBandpassMaximal E ψ f).aestronglyMeasurable
  have hU : MemLp U (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, U x ^ p) ≤ K * I := by
    simpa only [U] using
      memLp_and_integral_of_lintegral_rpow_bound U hUmeas hU0 hp0 hbound hKI
  have hmass : 0 < surfaceMass d := surfaceMass_pos hd0
  have hMeq : M = fun x : Euclidean d => (surfaceMass d)⁻¹ * U x := by
    funext x
    dsimp only [M, U, unnormalizedFractalDyadicBandpassMaximal]
    rw [← mul_assoc, inv_mul_cancel₀ hmass.ne', one_mul]
  have hMmem : MemLp M (ENNReal.ofReal p) volume := by
    rw [hMeq]
    exact hU.1.const_mul _
  have hUpowint : Integrable (fun x : Euclidean d => U x ^ p) volume := by
    have h := hU.1.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    convert h using 1
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hU0 x), ENNReal.toReal_ofReal hp0.le]
  have hMpowint : Integrable (fun x : Euclidean d => M x ^ p) volume := by
    have h := hMmem.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    convert h using 1
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hM0 x), ENNReal.toReal_ofReal hp0.le]
  refine ⟨hMmem, ?_⟩
  change (∫ x : Euclidean d, M x ^ p) ≤
    ((surfaceMass d)⁻¹) ^ p * K * I
  rw [hMeq]
  calc
    (∫ x : Euclidean d, ((surfaceMass d)⁻¹ * U x) ^ p) =
        ((surfaceMass d)⁻¹) ^ p * ∫ x : Euclidean d, U x ^ p := by
          rw [show (fun x : Euclidean d => ((surfaceMass d)⁻¹ * U x) ^ p) =
              fun x => ((surfaceMass d)⁻¹) ^ p * U x ^ p by
            funext x
            rw [Real.mul_rpow (inv_nonneg.mpr hmass.le) (hU0 x)]]
          rw [integral_const_mul]
    _ ≤ ((surfaceMass d)⁻¹) ^ p * (K * I) := by
      apply mul_le_mul_of_nonneg_left hU.2
      exact Real.rpow_nonneg (inv_nonneg.mpr hmass.le) _
    _ = ((surfaceMass d)⁻¹) ^ p * K * I := by ring

/-- A Schwartz input has matching real and extended-real `p`-moment
integrals.  This is the conversion used after the scaled interpolation
estimate and before summing the dyadic pieces. -/
theorem absolute_schwartz_lintegral_rpow_eq_ofReal_integral
    {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ) {p : ℝ} (hp0 : 0 < p) :
    (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p) =
      ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ p) := by
  have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfMem : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume :=
    f.memLp (ENNReal.ofReal p) volume
  have hfPowInt : Integrable (fun x : Euclidean d => ‖f x‖ ^ p) volume := by
    have h := hfMem.integrable_norm_rpow hpEN0 hpENT
    simpa only [ENNReal.toReal_ofReal hp0.le] using h
  calc
    (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p) =
        ∫⁻ x : Euclidean d, ENNReal.ofReal (‖f x‖ ^ p) := by
          apply lintegral_congr
          intro x
          exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
    _ = ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ p) :=
      (ofReal_integral_eq_lintegral_ofReal hfPowInt
        (Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (norm_nonneg _) p)).symm

/-- The normalized diagonal Minkowski estimate obtained from abstract
unnormalized `L¹` and `L²` endpoint estimates at frequency scale `R`.

The exponent of `R` is exactly `α + n - n p`; hence it is summable over
dyadic scales whenever this exponent is negative. -/
theorem normalized_absolute_minkowski_moment_of_endpoints
    {n : ℕ} {E : Set ℝ} {R α c₁ c₂ p : ℝ}
    (hn : 2 ≤ n) (hR : 0 < R) (hα : 0 ≤ α)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hp1 : 1 < p) (hp2 : p < 2)
    (ψ : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hEpos : E ⊆ Ioi (0 : ℝ))
    (hone : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g) 1 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g x‖) ≤
        (c₁ * R ^ α) * ∫ x : Euclidean (n + 1), ‖g x‖)
    (htwo : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g) 2 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g x‖ ^ (2 : ℕ)) ≤
        (c₂ * R ^ (α - n)) *
          ∫ x : Euclidean (n + 1), ‖g x‖ ^ (2 : ℕ))
    (f : SchwartzMap (Euclidean (n + 1)) ℂ) :
    let a₁ : ℝ := (p - 1)⁻¹ + (3 - p)⁻¹
    let a₂ : ℝ := ((1 : ℝ) / 4) * p⁻¹ + (2 - p)⁻¹
    MemLp (fractalDyadicBandpassMaximal (n + 1) E ψ f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean (n + 1),
        (fractalDyadicBandpassMaximal (n + 1) E ψ f x) ^ p) ≤
        ((surfaceMass (n + 1))⁻¹) ^ p *
          (p * (4 * c₂ * a₂ + 2 * c₁ * a₁)) *
            R ^ (α + n - n * p) *
              ∫ x : Euclidean (n + 1), ‖f x‖ ^ p := by
  dsimp only
  let a₁ : ℝ := (p - 1)⁻¹ + (3 - p)⁻¹
  let a₂ : ℝ := ((1 : ℝ) / 4) * p⁻¹ + (2 - p)⁻¹
  let K : ℝ := p * (4 * c₂ * a₂ + 2 * c₁ * a₁)
  let e : ℝ := α + n - n * p
  let I : ℝ := ∫ x : Euclidean (n + 1), ‖f x‖ ^ p
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hpminus : 0 < p - 1 := by linarith
  have htwo_pos : 0 < 2 - p := by linarith
  have hthree : 0 < 3 - p := by linarith
  have ha₁ : 0 ≤ a₁ := by
    dsimp only [a₁]
    exact add_nonneg (inv_nonneg.mpr hpminus.le) (inv_nonneg.mpr hthree.le)
  have ha₂ : 0 ≤ a₂ := by
    dsimp only [a₂]
    exact add_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr hp0.le))
      (inv_nonneg.mpr htwo_pos.le)
  have hK : 0 ≤ K := by
    dsimp only [K]
    apply mul_nonneg hp0.le
    apply add_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) hc₂) ha₂
    · exact mul_nonneg (mul_nonneg (by norm_num) hc₁) ha₁
  have hRe : 0 ≤ R ^ e := Real.rpow_nonneg hR.le _
  have hI : 0 ≤ I := by
    dsimp only [I]
    exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hKI : 0 ≤ (K * R ^ e) * I :=
    mul_nonneg (mul_nonneg hK hRe) hI
  have hlin := unnormalized_absolute_minkowski_lintegral_of_endpoints
    (n := n) (E := E) (R := R) (α := α) (c₁ := c₁) (c₂ := c₂) (p := p)
    hn hR hα hc₁ hc₂ hp1 hp2 ψ hEpos hone htwo f
  have hinput :
      (∫⁻ x : Euclidean (n + 1),
        (ENNReal.ofReal ‖(f : Euclidean (n + 1) → ℂ) x‖) ^ p) =
        ENNReal.ofReal I := by
    simpa only [I] using
      absolute_schwartz_lintegral_rpow_eq_ofReal_integral f hp0
  have hlin' :
      (∫⁻ x : Euclidean (n + 1), ENNReal.ofReal
        ((unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ f x) ^ p)) ≤
        ENNReal.ofReal ((K * R ^ e) * I) := by
    calc
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal R) ^ e *
          ∫⁻ x : Euclidean (n + 1),
            (ENNReal.ofReal ‖(f : Euclidean (n + 1) → ℂ) x‖) ^ p := by
          simpa only [K, e] using hlin
      _ = ENNReal.ofReal ((K * R ^ e) * I) := by
          rw [hinput, ENNReal.ofReal_rpow_of_pos hR,
            ← ENNReal.ofReal_mul hK,
            ← ENNReal.ofReal_mul (mul_nonneg hK hRe)]
  have hnormal := normalized_absolute_bandpass_moment_of_unnormalized_bound
    (d := n + 1) (E := E) (ψ := ψ) (f := f) (p := p)
    (K := K * R ^ e) (I := I) (by omega) hp0 hKI hlin'
  simpa only [K, e, I, mul_assoc] using hnormal

/-- Package the endpoint output of a radius cover into the normalized
Minkowski diagonal estimate.  The only algebraic input about the cover scale
is `δ ^ (-α) = R ^ α`, which is supplied below by taking `δ = R⁻¹`. -/
theorem normalized_absolute_minkowski_moment_of_cover_endpoints
    {n : ℕ} {E : Set ℝ} {R δ α C D B₁ B₂ p : ℝ}
    (hn : 2 ≤ n) (hR : 0 < R) (hα : 0 ≤ α)
    (hD : 0 ≤ D) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp1 : 1 < p) (hp2 : p < 2)
    (hδscale : C * δ ^ (-α) = D * R ^ α)
    (ψ : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hEpos : E ⊆ Ioi (0 : ℝ))
    (hendpoints : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g) 1 volume ∧
        (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g x‖) ≤
        (C * δ ^ (-α)) * B₁ * ∫ x : Euclidean (n + 1), ‖g x‖ ∧
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g) 2 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g x‖ ^ (2 : ℕ)) ≤
        (C * δ ^ (-α)) * (B₂ * R ^ (-(n : ℝ))) *
          ∫ x : Euclidean (n + 1), ‖g x‖ ^ (2 : ℕ))
    (f : SchwartzMap (Euclidean (n + 1)) ℂ) :
    let a₁ : ℝ := (p - 1)⁻¹ + (3 - p)⁻¹
    let a₂ : ℝ := ((1 : ℝ) / 4) * p⁻¹ + (2 - p)⁻¹
    MemLp (fractalDyadicBandpassMaximal (n + 1) E ψ f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean (n + 1),
        (fractalDyadicBandpassMaximal (n + 1) E ψ f x) ^ p) ≤
        ((surfaceMass (n + 1))⁻¹) ^ p *
          (p * (4 * (D * B₂) * a₂ + 2 * (D * B₁) * a₁)) *
            R ^ (α + n - n * p) *
              ∫ x : Euclidean (n + 1), ‖f x‖ ^ p := by
  dsimp only
  have hc₁ : 0 ≤ D * B₁ := mul_nonneg hD hB₁
  have hc₂ : 0 ≤ D * B₂ := mul_nonneg hD hB₂
  have hpower : R ^ α * R ^ (-(n : ℝ)) = R ^ (α - n) := by
    rw [← Real.rpow_add hR]
    congr 1
  have hone : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g) 1 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g x‖) ≤
        ((D * B₁) * R ^ α) * ∫ x : Euclidean (n + 1), ‖g x‖ := by
    intro g
    rcases hendpoints g with ⟨hmem, hbound, -, -⟩
    refine ⟨hmem, hbound.trans ?_⟩
    rw [hδscale]
    exact le_of_eq (by ring)
  have htwo : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g) 2 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E ψ g x‖ ^ (2 : ℕ)) ≤
        ((D * B₂) * R ^ (α - n)) *
          ∫ x : Euclidean (n + 1), ‖g x‖ ^ (2 : ℕ) := by
    intro g
    rcases hendpoints g with ⟨-, -, hmem, hbound⟩
    refine ⟨hmem, hbound.trans ?_⟩
    rw [hδscale, ← hpower]
    exact le_of_eq (by ring)
  exact normalized_absolute_minkowski_moment_of_endpoints
    hn hR hα hc₁ hc₂ hp1 hp2 ψ hEpos hone htwo f

/-- The non-endpoint diagonal Minkowski theorem in ambient dimension at least
three.  An upper Minkowski covering exponent strictly below
`n * (p - 1)` yields a strong restricted spherical maximal bound in ambient
dimension `n + 1`.

The proof uses one cover at scale `(2 R)⁻¹` for every annulus of frequency
`R`.  The harmless factor `2^α` is incorporated into the fixed constant;
this also treats the scale-zero annulus uniformly. -/
theorem minkowski_diagonal_strong_type_of_hasUpperMinkowskiExponent
    {n : ℕ} (hn : 2 ≤ n)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    {α p : ℝ} (hα : 0 ≤ α) (hM : HasUpperMinkowskiExponent E α)
    (hp1 : 1 < p) (hp2 : p < 2)
    (hcritical : α < n * (p - 1)) :
    HasFractalSphericalStrongType (n + 1) E p p := by
  let η : ℝ := (n * (p - 1) - α) / 2
  let a : ℝ := α + η
  let κ : ℝ := n * p - n - a
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hη : 0 < η := by
    dsimp only [η]
    linarith
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact add_nonneg hα hη.le
  have hκ : 0 < κ := by
    dsimp only [κ, a, η]
    linarith
  have he : a + n - n * p = -κ := by
    dsimp only [κ]
    ring
  obtain ⟨C, hC, hCovers⟩ :=
    exists_positive_intervalCovers_of_hasUpperMinkowskiExponent hE hM η hη
  obtain ⟨φ, ψ, hφone, hφzero, hφnorm, hψ, -⟩ :=
    exists_smooth_absolute_dyadic_bandpass_family (n + 1)
  obtain ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩ :=
    exists_sharp_surfaceFourier_succ_decay_and_deriv hn
  have hEpos : E ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one (hE hr).1
  obtain ⟨B, hB, hregular⟩ :=
    absolute_lowpass_strong_type (d := n + 1) (by omega) E hE
      φ hφzero hφnorm hp1 hp2
  let a₁ : ℝ := (p - 1)⁻¹ + (3 - p)⁻¹
  let a₂ : ℝ := ((1 : ℝ) / 4) * p⁻¹ + (2 - p)⁻¹
  let B₁ : ℝ := surfaceMass (n + 1) *
    ((∫ x : Euclidean (n + 1), ‖(𝓕⁻ ψ : SchwartzMap (Euclidean (n + 1)) ℂ) x‖) +
      ∫ x : Euclidean (n + 1),
        ‖fderiv ℝ ((𝓕⁻ ψ : SchwartzMap (Euclidean (n + 1)) ℂ) :
          Euclidean (n + 1) → ℂ) x‖)
  let B₂ : ℝ := 8 * C0 ^ 2 + 8 * C1 ^ 2
  let D : ℝ := C * (2 : ℝ) ^ a
  let P : ℝ := ((surfaceMass (n + 1))⁻¹) ^ p *
    (p * (4 * (D * B₂) * a₂ + 2 * (D * B₁) * a₁))
  let A : ℝ := P + 1
  have hpminus : 0 < p - 1 := by linarith
  have htwo_pos : 0 < 2 - p := by linarith
  have hthree : 0 < 3 - p := by linarith
  have ha₁ : 0 ≤ a₁ := by
    dsimp only [a₁]
    exact add_nonneg (inv_nonneg.mpr hpminus.le) (inv_nonneg.mpr hthree.le)
  have ha₂ : 0 ≤ a₂ := by
    dsimp only [a₂]
    exact add_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr hp0.le))
      (inv_nonneg.mpr htwo_pos.le)
  have hB₁ : 0 ≤ B₁ := by
    dsimp only [B₁]
    apply mul_nonneg (surfaceMass_pos (by omega)).le
    exact add_nonneg
      (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _)
  have hB₂ : 0 ≤ B₂ := by
    dsimp only [B₂]
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) _)
  have hmass : 0 < surfaceMass (n + 1) := surfaceMass_pos (by omega)
  have hP : 0 ≤ P := by
    dsimp only [P]
    apply mul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hmass.le) _)
    apply mul_nonneg hp0.le
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg hD hB₂)) ha₂
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg hD hB₁)) ha₁
  have hA : 0 < A := by
    dsimp only [A]
    linarith
  have hP_le_A : P ≤ A := by
    dsimp only [A]
    linarith
  apply absolute_reassembly_from_estimates
    (d := n + 1) (p := p) (by omega) hp1 E hEpos φ hφone hφzero
    ⟨B, hB, hregular⟩
  refine ⟨A, κ, hA, hκ, ?_⟩
  intro j f
  let R : ℝ := LeanSpherical.HarmonicAnalysis.dyadicScale j
  let δ : ℝ := (2 * R)⁻¹
  have hR : 0 < R := by
    dsimp only [R]
    exact LeanSpherical.HarmonicAnalysis.dyadicScale_pos j
  have hRone : 1 ≤ R := by
    dsimp only [R]
    exact one_le_absolute_dyadicScale j
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact inv_pos.mpr (mul_pos (by norm_num) hR)
  have hδone : δ < 1 := by
    dsimp only [δ]
    apply inv_lt_one_of_one_lt₀
    nlinarith
  have hδR : δ ≤ R⁻¹ := by
    calc
      δ = R⁻¹ * (2 : ℝ)⁻¹ := by
        dsimp only [δ]
        rw [mul_inv_rev]
      _ ≤ R⁻¹ * 1 := by
        apply mul_le_mul_of_nonneg_left
        · norm_num
        · exact inv_nonneg.mpr hR.le
      _ = R⁻¹ := by ring
  obtain ⟨ι, hcover, hcard, -⟩ := hCovers δ hδ hδone
  have hδscale : C * δ ^ (-a) = D * R ^ a := by
    dsimp only [δ, D]
    rw [inv_rpow_neg_eq_rpow, Real.mul_rpow (by norm_num) hR.le]
    ring
  have hendpoints : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass φ hφone hφzero j) g) 1 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass φ hφone hφzero j) g x‖) ≤
        (C * δ ^ (-a)) * B₁ * ∫ x : Euclidean (n + 1), ‖g x‖ ∧
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass φ hφone hφzero j) g) 2 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass φ hφone hφzero j) g x‖ ^ (2 : ℕ)) ≤
        (C * δ ^ (-a)) * (B₂ * R ^ (-(n : ℝ))) *
          ∫ x : Euclidean (n + 1), ‖g x‖ ^ (2 : ℕ) := by
    intro g
    have hendpoint := absolute_dyadic_minkowski_endpoints_of_cover
      hn C0 C1 hC0 hC1 hdecay hderiv hE hEne hR hRone hδ hδone hδR
      ι hcover (by simpa only [a] using hcard)
      φ g ψ (absoluteDyadicBandpass φ hφone hφzero j)
      hφone hφzero hφnorm j
      (absoluteDyadicBandpass_spec φ hφone hφzero j)
      (absoluteDyadicBandpass_compact φ hφone hφzero j)
      (by rfl) (by
        intro ξ
        simpa only [R, LeanSpherical.HarmonicAnalysis.dyadicScale] using
          smooth_dyadic_bandpass_eq_scaled_base φ ψ
            (absoluteDyadicBandpass φ hφone hφzero j) hψ j
            (absoluteDyadicBandpass_spec φ hφone hφzero j) ξ)
    simpa only [B₁, B₂] using hendpoint
  have hpiece := normalized_absolute_minkowski_moment_of_cover_endpoints
    (n := n) (E := E) (R := R) (δ := δ) (α := a) (C := C) (D := D)
    (B₁ := B₁) (B₂ := B₂) (p := p)
    hn hR ha hD hB₁ hB₂ hp1 hp2 hδscale
    (absoluteDyadicBandpass φ hφone hφzero j) hEpos hendpoints f
  have hpiece' :
      MemLp (fractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass φ hφone hφzero j) f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean (n + 1),
        (fractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass φ hφone hφzero j) f x) ^ p) ≤
        P * R ^ (a + n - n * p) *
          ∫ x : Euclidean (n + 1), ‖f x‖ ^ p := by
    simpa only [a₁, a₂, P] using hpiece
  have hRpow : R ^ (a + n - n * p) =
      (2 : ℝ) ^ (-κ * (j : ℝ)) := by
    rw [he]
    dsimp only [R, LeanSpherical.HarmonicAnalysis.dyadicScale]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  refine ⟨hpiece'.1, ?_⟩
  have hI : 0 ≤ ∫ x : Euclidean (n + 1), ‖f x‖ ^ p :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  calc
    (∫ x : Euclidean (n + 1),
      (fractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass φ hφone hφzero j) f x) ^ p) ≤
        P * R ^ (a + n - n * p) *
          ∫ x : Euclidean (n + 1), ‖f x‖ ^ p := hpiece'.2
    _ = P * (2 : ℝ) ^ (-κ * j) *
          ∫ x : Euclidean (n + 1), ‖f x‖ ^ p := by rw [hRpow]
    _ ≤ A * (2 : ℝ) ^ (-κ * j) *
          ∫ x : Euclidean (n + 1), ‖f x‖ ^ p := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hP_le_A
          (Real.rpow_nonneg (by norm_num) _)) hI

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
