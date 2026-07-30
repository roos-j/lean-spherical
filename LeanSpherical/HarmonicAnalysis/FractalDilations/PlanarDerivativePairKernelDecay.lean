/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.PlanarDerivativeTripleWaveExpansion

/-!
# Cone estimates for the differentiated planar pair kernel

The radius-differentiated circle kernel is estimated from its literal
twenty-seven-term normal form.  This is deliberately separate from the
ordinary planar calculation: the multiplier-side symbols are the actual
radius derivatives, while the phase geometry and physical outer-cone decay
are unchanged.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ComplexConjugate

noncomputable section

private theorem contDiff_planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude
    (q t : CoordinateWavePart) {R R' : Real} (hR : R ≠ 0) (hR' : R' ≠ 0) :
    ContDiff Real (⊤ : ℕ∞)
      (planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude q t R R') := by
  unfold planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude
  apply ((by fun_prop : ContDiff Real (⊤ : ℕ∞)
    (fun _ : Real => (surfaceMass 2 : Complex)⁻¹)).mul
      (contDiff_planarCoordinateWaveRadiusDerivativeAmplitude q hR)).mul
  have hbase : ContDiff Real (⊤ : ℕ∞)
      (fun u : Real => (surfaceMass 2 : Complex)⁻¹ *
        planarCoordinateWaveRadiusDerivativeAmplitude t R' u) :=
    (by fun_prop).mul (contDiff_planarCoordinateWaveRadiusDerivativeAmplitude t hR')
  have heq : (fun u : Real => starRingEnd Complex
      ((surfaceMass 2 : Complex)⁻¹ *
        planarCoordinateWaveRadiusDerivativeAmplitude t R' u)) =
      (Complex.conjCLE : Complex → Complex) ∘
        (fun u : Real => (surfaceMass 2 : Complex)⁻¹ *
          planarCoordinateWaveRadiusDerivativeAmplitude t R' u) := by
    funext u
    simpa only [Function.comp_apply] using
      (Complex.conjCLE_apply
        ((surfaceMass 2 : Complex)⁻¹ *
          planarCoordinateWaveRadiusDerivativeAmplitude t R' u)).symm
  rw [heq]
  exact Complex.conjCLE.contDiff.comp hbase

/-- The two differentiated multiplier-side coordinate symbols retain the
same `s⁻¹` stationary product size as in the ordinary circle calculation. -/
private theorem exists_uniform_planarCoordinateWaveRadiusDerivativeMultiplierPair_scaled
    (N : Nat) (q t : CoordinateWavePart) :
    ∃ C : Real, 0 < C ∧ ∀ k : Nat, k ≤ N → ∀ s r r' u : Real, 1 ≤ s →
      r ∈ Icc (1 / 2 : Real) (5 / 2) →
      r' ∈ Icc (1 / 2 : Real) (5 / 2) → u ∈ Icc (1 / 2 : Real) 8 →
      ‖iteratedDeriv k
        (planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude q t (s * r) (s * r')) u‖ ≤
        C / s := by
  obtain ⟨A, hA, hAbound⟩ :=
    exists_uniform_planarCoordinateWaveRadiusDerivativeAmplitude_scaled N q
  obtain ⟨B, hB, hBbound⟩ :=
    exists_uniform_planarCoordinateWaveRadiusDerivativeAmplitude_scaled N t
  let M : Real := ‖(surfaceMass 2 : Complex)⁻¹‖
  let D : Real := ∑ l ∈ Finset.range (N + 1),
    tripleWaveLeibnizConstant l (M * A) (M * B)
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    apply Finset.sum_nonneg
    intro l hl
    exact tripleWaveLeibnizConstant_nonneg l (mul_nonneg (norm_nonneg _) hA.le)
      (mul_nonneg (norm_nonneg _) hB.le)
  refine ⟨D + 1, by linarith, ?_⟩
  intro k hk s r r' u hs hr hr' hu
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hspos
  have hR : s * r ≠ 0 := (mul_pos hspos
    (lt_of_lt_of_le (by norm_num) hr.1)).ne'
  have hR' : s * r' ≠ 0 := (mul_pos hspos
    (lt_of_lt_of_le (by norm_num) hr'.1)).ne'
  let Q : Real := Real.sqrt s
  have hQpos : 0 < Q := hsqrt
  have hqbound : ∀ i : Nat, i ≤ k →
      ‖iteratedDeriv i (fun z : Real => (surfaceMass 2 : Complex)⁻¹ *
        planarCoordinateWaveRadiusDerivativeAmplitude q (s * r) z) u‖ ≤
        (M * A) / Q := by
    intro i hi
    rw [iteratedDeriv_const_mul_field, norm_mul]
    dsimp [M, Q]
    calc
      ‖(surfaceMass 2 : Complex)⁻¹‖ *
          ‖iteratedDeriv i (fun z : Real =>
            planarCoordinateWaveRadiusDerivativeAmplitude q (s * r) z) u‖ ≤
          ‖(surfaceMass 2 : Complex)⁻¹‖ * (A / Real.sqrt s) :=
        mul_le_mul_of_nonneg_left
          (hAbound i (hi.trans hk) s r u hs hr hu) (norm_nonneg _)
      _ = (‖(surfaceMass 2 : Complex)⁻¹‖ * A) / Real.sqrt s := by ring
  have htbound : ∀ i : Nat, i ≤ k →
      ‖iteratedDeriv i (fun z : Real => starRingEnd Complex
        ((surfaceMass 2 : Complex)⁻¹ *
          planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') z)) u‖ ≤
        (M * B) / Q := by
    intro i hi
    rw [norm_iteratedDeriv_starRingEnd
      (fun z : Real => (surfaceMass 2 : Complex)⁻¹ *
        planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') z)
      ((by fun_prop : ContDiff Real (⊤ : ℕ∞)
        (fun _ : Real => (surfaceMass 2 : Complex)⁻¹)).mul
          (contDiff_planarCoordinateWaveRadiusDerivativeAmplitude t hR')) i u,
      iteratedDeriv_const_mul_field, norm_mul]
    dsimp [M, Q]
    calc
      ‖(surfaceMass 2 : Complex)⁻¹‖ *
          ‖iteratedDeriv i (fun z : Real =>
            planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') z) u‖ ≤
          ‖(surfaceMass 2 : Complex)⁻¹‖ * (B / Real.sqrt s) :=
        mul_le_mul_of_nonneg_left
          (hBbound i (hi.trans hk) s r' u hs hr' hu) (norm_nonneg _)
      _ = (‖(surfaceMass 2 : Complex)⁻¹‖ * B) / Real.sqrt s := by ring
  have hprod := norm_iteratedDeriv_mul_le_tripleWaveLeibnizConstant
    (n := k)
    ((by fun_prop : ContDiff Real (⊤ : ℕ∞)
      (fun _ : Real => (surfaceMass 2 : Complex)⁻¹)).mul
        (contDiff_planarCoordinateWaveRadiusDerivativeAmplitude q hR))
    (by
      have hbase : ContDiff Real (⊤ : ℕ∞)
          (fun z : Real => (surfaceMass 2 : Complex)⁻¹ *
            planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') z) :=
        (by fun_prop).mul (contDiff_planarCoordinateWaveRadiusDerivativeAmplitude t hR')
      have heq : (fun z : Real => starRingEnd Complex
          ((surfaceMass 2 : Complex)⁻¹ *
            planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') z)) =
          (Complex.conjCLE : Complex → Complex) ∘
            (fun z : Real => (surfaceMass 2 : Complex)⁻¹ *
              planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') z) := by
        funext z
        simpa only [Function.comp_apply] using
          (Complex.conjCLE_apply
            ((surfaceMass 2 : Complex)⁻¹ *
              planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') z)).symm
      rw [heq]
      exact Complex.conjCLE.contDiff.comp hbase)
    (div_nonneg (mul_nonneg (norm_nonneg _) hA.le) hQpos.le)
    (div_nonneg (mul_nonneg (norm_nonneg _) hB.le) hQpos.le)
    hqbound htbound
  unfold planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude
  change ‖iteratedDeriv k (fun z : Real =>
      ((surfaceMass 2 : Complex)⁻¹ *
        planarCoordinateWaveRadiusDerivativeAmplitude q (s * r) z) *
        starRingEnd Complex
          ((surfaceMass 2 : Complex)⁻¹ *
            planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') z)) u‖ ≤ _
  calc
    ‖iteratedDeriv k (fun z : Real =>
        ((surfaceMass 2 : Complex)⁻¹ *
          planarCoordinateWaveRadiusDerivativeAmplitude q (s * r) z) *
          starRingEnd Complex
            ((surfaceMass 2 : Complex)⁻¹ *
              planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') z)) u‖ ≤
        tripleWaveLeibnizConstant k (M * A / Q) (M * B / Q) := hprod
    _ = tripleWaveLeibnizConstant k (M * A) (M * B) / Q ^ 2 :=
      tripleWaveLeibnizConstant_div_div k (M * A) (M * B) Q hQpos.ne'
    _ ≤ D / Q ^ 2 := by
      apply div_le_div_of_nonneg_right
      · unfold D
        have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
        exact Finset.single_le_sum
          (fun l hl => tripleWaveLeibnizConstant_nonneg l
            (mul_nonneg (norm_nonneg _) hA.le) (mul_nonneg (norm_nonneg _) hB.le)) hmem
      · exact sq_pos_of_pos hQpos
    _ ≤ (D + 1) / s := by
      dsimp [Q]
      rw [Real.sq_sqrt (zero_le_one.trans hs)]
      apply div_le_div_of_nonneg_right
      · linarith
      · exact hspos

/-- The common physical/cutoff factor times the differentiated multiplier
pair is the literal differentiated triple coefficient. -/
private theorem planarRadiusDerivativeCoordinateTripleWaveCoefficient_eq_fixed_mul_pair
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (R R' : Real) (v x : Euclidean 2)
    (p q t : CoordinateWavePart) (u : Real) :
    planarRadiusDerivativeCoordinateTripleWaveCoefficient
      (absoluteDyadicBandpass phi hphiOne hphiZero 0)
      R R' v x p q t u =
      planarCoordinateTripleWaveFixedAmplitude phi v x p u *
        planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude q t R R' u := by
  have hcutoff := absoluteDyadicBandpass_zero_smul_eq_normalized
    phi hphiOne hphiZero v u
  unfold planarRadiusDerivativeCoordinateTripleWaveCoefficient
    planarCoordinateTripleWaveFixedAmplitude
    planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude
    normalizedDyadicCutoffSquare
  rw [hcutoff, map_mul]
  ring

/-- Smoothness of the literal differentiated triple coefficient on a positive
radial annulus.  This is exported for the finite summation source. -/
theorem contDiff_planarRadiusDerivativeCoordinateTripleWaveCoefficient
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    {R R' : Real} (hR : R ≠ 0) (hR' : R' ≠ 0)
    (v x : Euclidean 2) (p q t : CoordinateWavePart) :
    ContDiff Real (⊤ : ℕ∞) (fun u : Real =>
      planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        R R' v x p q t u) := by
  have hfun : (fun u : Real =>
      planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        R R' v x p q t u) =
      fun u : Real => planarCoordinateTripleWaveFixedAmplitude phi v x p u *
        planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude q t R R' u := by
    funext u
    exact planarRadiusDerivativeCoordinateTripleWaveCoefficient_eq_fixed_mul_pair
      phi hphiOne hphiZero R R' v x p q t u
  rw [hfun]
  exact (contDiff_planarCoordinateTripleWaveFixedAmplitude phi v x p).mul
    (contDiff_planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude q t hR hR')

/-- The literal differentiated planar triple coefficient has `s⁻¹`
stationary size through every finite radial derivative order. -/
private theorem exists_uniform_planarRadiusDerivativeCoordinateTripleWaveCoefficient_scaled
    (N : Nat) (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiRadial : IsNormRadial phi)
    (p q t : CoordinateWavePart) :
    ∃ C : Real, 0 < C ∧ ∀ k : Nat, k ≤ N →
      ∀ s r r' u : Real, 1 ≤ s →
        r ∈ Icc (1 / 2 : Real) (5 / 2) →
        r' ∈ Icc (1 / 2 : Real) (5 / 2) →
        ∀ v x : Euclidean 2, ‖v‖ = 1 → u ∈ Icc (1 / 2 : Real) 8 →
          ‖iteratedDeriv k (fun z : Real =>
            planarRadiusDerivativeCoordinateTripleWaveCoefficient
              (absoluteDyadicBandpass phi hphiOne hphiZero 0)
              (s * r) (s * r') v x p q t z) u‖ ≤ C / s := by
  obtain ⟨A, hA, hAbound⟩ :=
    exists_uniform_planarCoordinateTripleWaveFixedAmplitude_bound N phi
      hphiOne hphiZero hphiRadial p
  obtain ⟨B, hB, hBbound⟩ :=
    exists_uniform_planarCoordinateWaveRadiusDerivativeMultiplierPair_scaled N q t
  let C : Real := ∑ l ∈ Finset.range (N + 1), tripleWaveLeibnizConstant l A B
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro l hl
    exact tripleWaveLeibnizConstant_nonneg l hA.le hB.le
  refine ⟨C + 1, by linarith, ?_⟩
  intro k hk s r r' u hs hr hr' v x hv hu
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hR : s * r ≠ 0 := (mul_pos hspos
    (lt_of_lt_of_le (by norm_num) hr.1)).ne'
  have hR' : s * r' ≠ 0 := (mul_pos hspos
    (lt_of_lt_of_le (by norm_num) hr'.1)).ne'
  have hfixed : ∀ i : Nat, i ≤ k →
      ‖iteratedDeriv i (planarCoordinateTripleWaveFixedAmplitude phi v x p) u‖ ≤ A := by
    intro i hi
    exact hAbound v x hv i (hi.trans hk) u hu
  have hpair : ∀ i : Nat, i ≤ k →
      ‖iteratedDeriv i
        (planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude q t (s * r) (s * r')) u‖ ≤
        B / s := by
    intro i hi
    exact hBbound i (hi.trans hk) s r r' u hs hr hr' hu
  have hprod := norm_iteratedDeriv_mul_le_tripleWaveLeibnizConstant
    (n := k) (contDiff_planarCoordinateTripleWaveFixedAmplitude phi v x p)
      (contDiff_planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude q t hR hR')
      hA.le (div_nonneg hB.le hspos.le) hfixed hpair
  have hfactorfun : (fun z : Real =>
      planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        (s * r) (s * r') v x p q t z) =
      fun z : Real => planarCoordinateTripleWaveFixedAmplitude phi v x p z *
        planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude q t (s * r) (s * r') z := by
    funext z
    exact planarRadiusDerivativeCoordinateTripleWaveCoefficient_eq_fixed_mul_pair
      phi hphiOne hphiZero (s * r) (s * r') v x p q t z
  rw [hfactorfun]
  calc
    ‖iteratedDeriv k (fun z : Real =>
        planarCoordinateTripleWaveFixedAmplitude phi v x p z *
          planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude q t (s * r) (s * r') z) u‖ ≤
        tripleWaveLeibnizConstant k A (B / s) := hprod
    _ = tripleWaveLeibnizConstant k A B / s := by
      rw [tripleWaveLeibnizConstant_right_div k A B s hspos.ne']
    _ ≤ C / s := by
      apply div_le_div_of_nonneg_right
      · unfold C
        have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
        exact Finset.single_le_sum
          (fun l hl => tripleWaveLeibnizConstant_nonneg l hA.le hB.le) hmem
      · exact hspos
    _ ≤ (C + 1) / s := by
      apply div_le_div_of_nonneg_right
      · linarith
      · exact hspos

private theorem planarRadiusDerivativeCoordinateTripleWaveCoefficient_absoluteDyadicBandpass_eq_zero_left
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (r r' : Real) (v x : Euclidean 2) (hv : ‖v‖ = 1)
    (p q t : CoordinateWavePart) {u : Real}
    (hu : u ∈ Icc (1 / 2 : Real) 1) :
    planarRadiusDerivativeCoordinateTripleWaveCoefficient
      (absoluteDyadicBandpass phi hphiOne hphiZero 0)
      r r' v x p q t u = 0 := by
  have hpsi := absoluteDyadicBandpass_zero_on_normalized_left
    phi hphiOne hphiZero v hv hu
  unfold planarRadiusDerivativeCoordinateTripleWaveCoefficient
  rw [hpsi]
  simp

private theorem planarRadiusDerivativeCoordinateTripleWaveCoefficient_absoluteDyadicBandpass_eq_zero_right
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (r r' : Real) (v x : Euclidean 2) (hv : ‖v‖ = 1)
    (p q t : CoordinateWavePart) {u : Real}
    (hu : u ∈ Icc (4 : Real) 8) :
    planarRadiusDerivativeCoordinateTripleWaveCoefficient
      (absoluteDyadicBandpass phi hphiOne hphiZero 0)
      r r' v x p q t u = 0 := by
  have hpsi := absoluteDyadicBandpass_zero_on_normalized_right
    phi hphiOne hphiZero v hv hu
  unfold planarRadiusDerivativeCoordinateTripleWaveCoefficient
  rw [hpsi]
  simp

private theorem planarRadiusDerivativeCoordinateTripleWaveCoefficient_eventuallyEq_zero_left
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (r r' : Real) (v x : Euclidean 2) (hv : ‖v‖ = 1)
    (p q t : CoordinateWavePart) :
    planarRadiusDerivativeCoordinateTripleWaveCoefficient
      (absoluteDyadicBandpass phi hphiOne hphiZero 0)
      r r' v x p q t =ᶠ[𝓝 (1 / 2 : Real)] 0 := by
  filter_upwards [Metric.ball_mem_nhds (1 / 2 : Real)
      (by norm_num : (0 : Real) < 1 / 4)] with u hu
  rw [mem_ball, Real.dist_eq] at hu
  have huabs : |u - 1 / 2| < 1 / 4 := hu
  have hu0 : 1 / 2 ≤ u := by
    have := (abs_lt.mp huabs).1
    linarith
  have huone : u ≤ 1 := by
    have := (abs_lt.mp huabs).2
    linarith
  exact planarRadiusDerivativeCoordinateTripleWaveCoefficient_absoluteDyadicBandpass_eq_zero_left
    phi hphiOne hphiZero r r' v x hv p q t ⟨hu0, huone⟩

private theorem planarRadiusDerivativeCoordinateTripleWaveCoefficient_eventuallyEq_zero_right
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (r r' : Real) (v x : Euclidean 2) (hv : ‖v‖ = 1)
    (p q t : CoordinateWavePart) :
    planarRadiusDerivativeCoordinateTripleWaveCoefficient
      (absoluteDyadicBandpass phi hphiOne hphiZero 0)
      r r' v x p q t =ᶠ[𝓝 (8 : Real)] 0 := by
  filter_upwards [Metric.ball_mem_nhds (8 : Real)
      (by norm_num : (0 : Real) < 1)] with u hu
  rw [mem_ball, Real.dist_eq] at hu
  have huabs : |u - 8| < 1 := hu
  have hufour : 4 ≤ u := by
    have := (abs_lt.mp huabs).1
    linarith
  exact planarRadiusDerivativeCoordinateTripleWaveCoefficient_absoluteDyadicBandpass_eq_zero_right
    phi hphiOne hphiZero r r' v x hv p q t ⟨hufour, by linarith⟩

private theorem hasOscillatoryIBPChain_planarRadiusDerivativeCoordinateTripleWaveCoefficient
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    {r r' : Real} (hr : r ≠ 0) (hr' : r' ≠ 0)
    (v x : Euclidean 2) (hv : ‖v‖ = 1)
    (p q t : CoordinateWavePart) (N : Nat) :
    HasOscillatoryIBPChain (1 / 2 : Real) 8
      (fun k => iteratedDeriv k
        (planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          r r' v x p q t)) N := by
  apply hasOscillatoryIBPChain_iteratedDeriv_of_contDiff
  · exact contDiff_planarRadiusDerivativeCoordinateTripleWaveCoefficient
      phi hphiOne hphiZero hr hr' v x p q t
  · exact planarRadiusDerivativeCoordinateTripleWaveCoefficient_eventuallyEq_zero_left
      phi hphiOne hphiZero r r' v x hv p q t
  · exact planarRadiusDerivativeCoordinateTripleWaveCoefficient_eventuallyEq_zero_right
      phi hphiOne hphiZero r r' v x hv p q t

private theorem intervalIntegral_planarRadiusDerivativeCoordinateTripleWaveCoefficient_eq_expanded
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    {r r' : Real} (hr : r ≠ 0) (hr' : r' ≠ 0)
    (v x : Euclidean 2) (hv : ‖v‖ = 1)
    (p q t : CoordinateWavePart) :
    (∫ u in (1 : Real)..4,
      planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        r r' v x p q t u * oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ r r') u) =
      ∫ u in (1 / 2 : Real)..8,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          r r' v x p q t u * oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ r r') u := by
  apply intervalIntegral_eq_expanded_fixedAnnulus_of_zero
  · exact (contDiff_planarRadiusDerivativeCoordinateTripleWaveCoefficient
      phi hphiOne hphiZero hr hr' v x p q t).continuous.mul (by fun_prop)
  · intro u hu
    rw [planarRadiusDerivativeCoordinateTripleWaveCoefficient_absoluteDyadicBandpass_eq_zero_left
      phi hphiOne hphiZero r r' v x hv p q t hu]
    simp
  · intro u hu
    rw [planarRadiusDerivativeCoordinateTripleWaveCoefficient_absoluteDyadicBandpass_eq_zero_right
      phi hphiOne hphiZero r r' v x hv p q t hu]
    simp

private theorem norm_intervalIntegral_planarRadiusDerivativeCoordinateTripleWaveCoefficient_le_iterated
    (N : Nat) (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    {r r' : Real} (hr : r ≠ 0) (hr' : r' ≠ 0)
    (v x : Euclidean 2) (hv : ‖v‖ = 1)
    (p q t : CoordinateWavePart) (freq M : Real)
    (hfreq : freq ≠ 0) (hM : 0 ≤ M)
    (hbound : ∀ u ∈ Icc (1 / 2 : Real) 8,
      ‖iteratedDeriv N (planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        r r' v x p q t) u‖ ≤ M) :
    ‖∫ u in (1 : Real)..4,
      planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        r r' v x p q t u * oscillatoryExp freq u‖ ≤
      (1 / |freq|) ^ N * ((8 - (1 / 2 : Real)) * M) := by
  rw [intervalIntegral_planarRadiusDerivativeCoordinateTripleWaveCoefficient_eq_expanded
    phi hphiOne hphiZero hr hr' v x hv p q t]
  apply norm_intervalIntegral_mul_oscillatoryExp_le_iterated
    (by norm_num) hfreq
    (hasOscillatoryIBPChain_planarRadiusDerivativeCoordinateTripleWaveCoefficient
      phi hphiOne hphiZero hr hr' v x hv p q t N)
    hM hbound

/-- Inner-cone endpoint triples in the differentiated circle normal form
have the same literal nonstationary phase as the ordinary triples.  The
radius derivative changes only the coefficient, whose two integrations by
parts are controlled by the differentiated symbol calculation above. -/
private theorem exists_inner_endpoint_planarRadiusDerivativeCoordinateTripleWaveIntegral_bound
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiRadial : IsNormRadial phi)
    (p q t : CoordinateWavePart)
    (hp : p ≠ .middle) (hq : q ≠ .middle) (ht : t ≠ .middle) :
    ∃ C : Real, 0 < C ∧ ∀ s r r' : Real, 1 ≤ s →
      r ∈ Icc (1 / 2 : Real) (5 / 2) →
      r' ∈ Icc (1 / 2 : Real) (5 / 2) → r ≠ r' →
      ∀ v x : Euclidean 2, ‖v‖ = 1 → ‖x‖ ≤ |r - r'| / 4 →
      ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v (s • x) p q t u *
          oscillatoryExp
            (coordinateTripleWavePhase p q t ‖s • x‖ (s * r) (s * r')) u‖ ≤
        (4 / (s * |r - r'|)) ^ 2 *
          ((8 - (1 / 2 : Real)) * (C / s)) := by
  obtain ⟨C, hC, hCbound⟩ :=
    exists_uniform_planarRadiusDerivativeCoordinateTripleWaveCoefficient_scaled 2 phi
      hphiOne hphiZero hphiRadial p q t
  refine ⟨C, hC, ?_⟩
  intro s r r' hs hr hr' hrr v x hv hxcone
  let y : Euclidean 2 := s • x
  let freq : Real := coordinateTripleWavePhase p q t ‖y‖ (s * r) (s * r')
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
  have hr'pos : 0 < r' := lt_of_lt_of_le (by norm_num) hr'.1
  have hR : s * r ≠ 0 := (mul_pos hspos hrpos).ne'
  have hR' : s * r' ≠ 0 := (mul_pos hspos hr'pos).ne'
  have hgap : 0 < |r - r'| := abs_pos.mpr (sub_ne_zero.mpr hrr)
  have hscalednorm : ‖y‖ = s * ‖x‖ := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
  have horig : |r - r'| / 4 ≤
      |coordinateTripleWavePhase p q t ‖x‖ r r'| :=
    abs_coordinateTripleWavePhase_ge_quarter_gap_of_endpoints hp hq ht hr hr'
      (norm_nonneg _) hxcone
  have hfreqscale : freq =
      s * coordinateTripleWavePhase p q t ‖x‖ r r' := by
    dsimp [freq]
    rw [hscalednorm]
    exact coordinateTripleWavePhase_scale s ‖x‖ r r' p q t
  have hfreqlower : s * |r - r'| / 4 ≤ |freq| := by
    rw [hfreqscale, abs_mul, abs_of_pos hspos]
    calc
      s * |r - r'| / 4 = s * (|r - r'| / 4) := by ring
      _ ≤ s * |coordinateTripleWavePhase p q t ‖x‖ r r'| :=
        mul_le_mul_of_nonneg_left horig hspos.le
  have hfreqpos : 0 < |freq| := by
    have : 0 < s * |r - r'| / 4 := by positivity
    exact lt_of_lt_of_le this hfreqlower
  have hinv : 1 / |freq| ≤ 4 / (s * |r - r'|) := by
    calc
      1 / |freq| ≤ 1 / (s * |r - r'| / 4) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity) hfreqlower
      _ = 4 / (s * |r - r'|) := by
        field_simp [hspos.ne', hgap.ne']
        ring
  have hM : 0 ≤ C / s := div_nonneg hC.le hspos.le
  have hbound : ∀ u ∈ Icc (1 / 2 : Real) 8,
      ‖iteratedDeriv 2 (planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        (s * r) (s * r') v y p q t) u‖ ≤ C / s := by
    intro u hu
    exact hCbound 2 le_rfl s r r' u hs hr hr' v y hv hu
  have hIBP := norm_intervalIntegral_planarRadiusDerivativeCoordinateTripleWaveCoefficient_le_iterated
    2 phi hphiOne hphiZero hR hR' v y hv p q t freq
    (C / s) (ne_of_gt hfreqpos) hM hbound
  change ‖∫ u in (1 : Real)..4,
      planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        (s * r) (s * r') v y p q t u * oscillatoryExp freq u‖ ≤ _
  calc
    ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v y p q t u * oscillatoryExp freq u‖ ≤
        (1 / |freq|) ^ 2 * ((8 - (1 / 2 : Real)) * (C / s)) := hIBP
    _ ≤ (4 / (s * |r - r'|)) ^ 2 *
          ((8 - (1 / 2 : Real)) * (C / s)) := by
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_pow_left₀ (by positivity) hinv _
      · positivity

/-- The differentiated inner calculation when the physical factor is the
middle wave.  Its phase is independent of the physical radius exactly as in
the undifferentiated normal form. -/
private theorem exists_inner_physicalMiddle_planarRadiusDerivativeCoordinateTripleWaveIntegral_bound
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiRadial : IsNormRadial phi)
    (q t : CoordinateWavePart) (hq : q ≠ .middle) (ht : t ≠ .middle) :
    ∃ C : Real, 0 < C ∧ ∀ s r r' : Real, 1 ≤ s →
      r ∈ Icc (1 / 2 : Real) (5 / 2) →
      r' ∈ Icc (1 / 2 : Real) (5 / 2) → r ≠ r' →
      ∀ v x : Euclidean 2, ‖v‖ = 1 → ‖x‖ ≤ |r - r'| / 4 →
      ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v (s • x) .middle q t u *
          oscillatoryExp
            (coordinateTripleWavePhase .middle q t ‖s • x‖ (s * r) (s * r')) u‖ ≤
        (4 / (s * |r - r'|)) ^ 2 *
          ((8 - (1 / 2 : Real)) * (C / s)) := by
  obtain ⟨C, hC, hCbound⟩ :=
    exists_uniform_planarRadiusDerivativeCoordinateTripleWaveCoefficient_scaled 2 phi
      hphiOne hphiZero hphiRadial .middle q t
  refine ⟨C, hC, ?_⟩
  intro s r r' hs hr hr' hrr v x hv hxcone
  let y : Euclidean 2 := s • x
  let freq : Real := coordinateTripleWavePhase .middle q t ‖y‖ (s * r) (s * r')
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
  have hr'pos : 0 < r' := lt_of_lt_of_le (by norm_num) hr'.1
  have hR : s * r ≠ 0 := (mul_pos hspos hrpos).ne'
  have hR' : s * r' ≠ 0 := (mul_pos hspos hr'pos).ne'
  have hgap : 0 < |r - r'| := abs_pos.mpr (sub_ne_zero.mpr hrr)
  have horig : |r - r'| / 4 ≤
      |coordinateTripleWavePhase .middle q t 0 r r'| :=
    abs_coordinateTripleWavePhase_ge_quarter_gap_of_physical_middle hq ht hr hr'
  have hmiddlephase (a b c : Real) :
      coordinateTripleWavePhase .middle q t a b c =
        coordinateTripleWavePhase .middle q t 0 b c := by
    simp [coordinateTripleWavePhase, coordinateWaveRadialPhase]
  have hfreqscale : freq =
      s * coordinateTripleWavePhase .middle q t 0 r r' := by
    dsimp [freq]
    rw [hmiddlephase]
    exact coordinateTripleWavePhase_scale s 0 r r' .middle q t
  have hfreqlower : s * |r - r'| / 4 ≤ |freq| := by
    rw [hfreqscale, abs_mul, abs_of_pos hspos]
    calc
      s * |r - r'| / 4 = s * (|r - r'| / 4) := by ring
      _ ≤ s * |coordinateTripleWavePhase .middle q t 0 r r'| :=
        mul_le_mul_of_nonneg_left horig hspos.le
  have hfreqpos : 0 < |freq| := by
    have : 0 < s * |r - r'| / 4 := by positivity
    exact lt_of_lt_of_le this hfreqlower
  have hinv : 1 / |freq| ≤ 4 / (s * |r - r'|) := by
    calc
      1 / |freq| ≤ 1 / (s * |r - r'| / 4) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity) hfreqlower
      _ = 4 / (s * |r - r'|) := by
        field_simp [hspos.ne', hgap.ne']
        ring
  have hM : 0 ≤ C / s := div_nonneg hC.le hspos.le
  have hbound : ∀ u ∈ Icc (1 / 2 : Real) 8,
      ‖iteratedDeriv 2 (planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        (s * r) (s * r') v y .middle q t) u‖ ≤ C / s := by
    intro u hu
    exact hCbound 2 le_rfl s r r' u hs hr hr' v y hv hu
  have hIBP := norm_intervalIntegral_planarRadiusDerivativeCoordinateTripleWaveCoefficient_le_iterated
    2 phi hphiOne hphiZero hR hR' v y hv .middle q t freq
    (C / s) (ne_of_gt hfreqpos) hM hbound
  change ‖∫ u in (1 : Real)..4,
      planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        (s * r) (s * r') v y .middle q t u * oscillatoryExp freq u‖ ≤ _
  calc
    ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v y .middle q t u * oscillatoryExp freq u‖ ≤
        (1 / |freq|) ^ 2 * ((8 - (1 / 2 : Real)) * (C / s)) := hIBP
    _ ≤ (4 / (s * |r - r'|)) ^ 2 *
          ((8 - (1 / 2 : Real)) * (C / s)) := by
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_pow_left₀ (by positivity) hinv _
      · positivity

/-- A multiplier-side differentiated middle wave still has arbitrarily rapid
dyadic decay.  Here the radius derivative is rewritten as
`(u / a) ∂ᵤ A(a,u)`; the sine-moment bound for the literal middle amplitude
then supplies the prescribed power. -/
private theorem exists_planarCoordinateWaveRadiusDerivativeAmplitude_middle_scaled_power
    (L : Nat) :
    ∃ C : Real, 0 < C ∧ ∀ s r u : Real, 1 ≤ s →
      r ∈ Icc (1 / 2 : Real) (5 / 2) → u ∈ Icc (1 / 2 : Real) 8 →
      ‖planarCoordinateWaveRadiusDerivativeAmplitude .middle (s * r) u‖ ≤
        C / s ^ L := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_iteratedDeriv_planarCoordinateWaveRadialAmplitude_middle_decay 1 (L + 1)
  refine ⟨(80 * Real.pi) * C, mul_pos (by positivity) hC, ?_⟩
  intro s r u hs hr hu
  obtain ⟨hfreq, hamp, hscale, hsqrt⟩ :=
    scaled_coordinate_frequency_geometry hs hr hu
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsrhalf : (1 / 2 : Real) ≤ s * r := by
    calc
      (1 / 2 : Real) = 1 * (1 / 2 : Real) := by ring
      _ ≤ s * r := mul_le_mul hs hr.1 (by positivity) (by positivity)
  have hsrpos : 0 < s * r := lt_of_lt_of_le (by norm_num) hsrhalf
  have hsrne : s * r ≠ 0 := hsrpos.ne'
  have huover : ‖((u / (s * r) : Real) : Complex)‖ ≤ 16 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by linarith [hu.1]) hsrpos.le)]
    apply (div_le_iff₀ hsrpos).2
    nlinarith [hu.2, hsrhalf]
  have hformula :
      planarCoordinateWaveRadiusDerivativeAmplitude .middle (s * r) u =
        ((u / (s * r) : Real) : Complex) *
          iteratedDeriv 1
            (fun z : Real => planarCoordinateWaveRadialAmplitude .middle (s * r) z) u := by
    unfold planarCoordinateWaveRadiusDerivativeAmplitude
    rw [deriv_planarCoordinateWaveRadialAmplitude_radius_eq_div_mul_iteratedDeriv
      .middle hsrne u]
    simp [planarCoordinateWavePhaseSlope]
  have hmiddle :
      ‖iteratedDeriv 1
        (fun z : Real => planarCoordinateWaveRadialAmplitude .middle (s * r) z) u‖ ≤
        C * |2 * Real.pi * (s * r)| /
          |(2 * Real.pi * (s * r)) * u| ^ (L + 1) := by
    simpa using hbound (s * r) u hfreq
  have hden : s ^ (L + 1) ≤ |(2 * Real.pi * (s * r)) * u| ^ (L + 1) :=
    pow_le_pow_left₀ (zero_le_one.trans hs) hscale _
  have hnum : C * |2 * Real.pi * (s * r)| ≤ C * ((5 * Real.pi) * s) :=
    mul_le_mul_of_nonneg_left hamp hC.le
  have hquot :
      C * |2 * Real.pi * (s * r)| /
          |(2 * Real.pi * (s * r)) * u| ^ (L + 1) ≤
        C * ((5 * Real.pi) * s) / s ^ (L + 1) := by
    calc
      C * |2 * Real.pi * (s * r)| /
          |(2 * Real.pi * (s * r)) * u| ^ (L + 1) ≤
          C * |2 * Real.pi * (s * r)| / s ^ (L + 1) :=
        div_le_div_of_nonneg_left
          (mul_nonneg hC.le (abs_nonneg _)) (pow_pos hspos _) hden
      _ ≤ C * ((5 * Real.pi) * s) / s ^ (L + 1) :=
        div_le_div_of_nonneg_right hnum (pow_pos hspos _)
  rw [hformula, norm_mul]
  calc
    ‖((u / (s * r) : Real) : Complex)‖ *
        ‖iteratedDeriv 1
          (fun z : Real => planarCoordinateWaveRadialAmplitude .middle (s * r) z) u‖ ≤
        16 * (C * |2 * Real.pi * (s * r)| /
          |(2 * Real.pi * (s * r)) * u| ^ (L + 1)) := by
      exact mul_le_mul huover hmiddle (norm_nonneg _) (by positivity)
    _ ≤ 16 * (C * ((5 * Real.pi) * s) / s ^ (L + 1)) :=
      mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = ((80 * Real.pi) * C) / s ^ L := by
      rw [show L + 1 = Nat.succ L by omega, pow_succ]
      field_simp [hspos.ne']
      ring

/-- One differentiated multiplier-side middle factor supplies arbitrary
extra dyadic decay; the other differentiated factor retains its ordinary
half-order stationary size. -/
private theorem exists_planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude_oneMiddle_scaled
    (L : Nat) (q t : CoordinateWavePart)
    (hmiddle : q = .middle ∨ t = .middle) :
    ∃ C : Real, 0 < C ∧ ∀ s r r' u : Real, 1 ≤ s →
      r ∈ Icc (1 / 2 : Real) (5 / 2) →
      r' ∈ Icc (1 / 2 : Real) (5 / 2) → u ∈ Icc (1 / 2 : Real) 8 →
      ‖planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude
        q t (s * r) (s * r') u‖ ≤
        C / (s ^ L * Real.sqrt s) := by
  rcases hmiddle with hq | ht
  · subst q
    obtain ⟨A, hA, hAbound⟩ :=
      exists_planarCoordinateWaveRadiusDerivativeAmplitude_middle_scaled_power L
    obtain ⟨B, hB, hBbound⟩ :=
      exists_uniform_planarCoordinateWaveRadiusDerivativeAmplitude_scaled 0 t
    let M : Real := ‖(surfaceMass 2 : Complex)⁻¹‖
    have hM : 0 ≤ M := by
      dsimp [M]
      exact norm_nonneg _
    refine ⟨M ^ 2 * A * B + 1, by positivity, ?_⟩
    intro s r r' u hs hr hr' hu
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
    have hqbound := hAbound s r u hs hr hu
    have htbound := hBbound 0 le_rfl s r' u hs hr' hu
    have hQpos : 0 < Real.sqrt s := Real.sqrt_pos.2 hspos
    unfold planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude
    simp only [norm_mul, norm_star]
    change M * ‖planarCoordinateWaveRadiusDerivativeAmplitude .middle (s * r) u‖ *
        (M * ‖planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') u‖) ≤ _
    calc
      M * ‖planarCoordinateWaveRadiusDerivativeAmplitude .middle (s * r) u‖ *
          (M * ‖planarCoordinateWaveRadiusDerivativeAmplitude t (s * r') u‖) ≤
          M * (A / s ^ L) * (M * (B / Real.sqrt s)) := by
        gcongr
      _ = (M ^ 2 * A * B) / (s ^ L * Real.sqrt s) := by
        field_simp [hspos.ne', hQpos.ne']
        ring
      _ ≤ (M ^ 2 * A * B + 1) / (s ^ L * Real.sqrt s) := by
        apply div_le_div_of_nonneg_right
        · linarith
        · positivity
  · subst t
    obtain ⟨A, hA, hAbound⟩ :=
      exists_planarCoordinateWaveRadiusDerivativeAmplitude_middle_scaled_power L
    obtain ⟨B, hB, hBbound⟩ :=
      exists_uniform_planarCoordinateWaveRadiusDerivativeAmplitude_scaled 0 q
    let M : Real := ‖(surfaceMass 2 : Complex)⁻¹‖
    have hM : 0 ≤ M := by
      dsimp [M]
      exact norm_nonneg _
    refine ⟨M ^ 2 * B * A + 1, by positivity, ?_⟩
    intro s r r' u hs hr hr' hu
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
    have hqbound := hBbound 0 le_rfl s r u hs hr hu
    have htbound := hAbound s r' u hs hr' hu
    have hQpos : 0 < Real.sqrt s := Real.sqrt_pos.2 hspos
    unfold planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude
    simp only [norm_mul, norm_star]
    change M * ‖planarCoordinateWaveRadiusDerivativeAmplitude q (s * r) u‖ *
        (M * ‖planarCoordinateWaveRadiusDerivativeAmplitude .middle (s * r') u‖) ≤ _
    calc
      M * ‖planarCoordinateWaveRadiusDerivativeAmplitude q (s * r) u‖ *
          (M * ‖planarCoordinateWaveRadiusDerivativeAmplitude .middle (s * r') u‖) ≤
          M * (B / Real.sqrt s) * (M * (A / s ^ L)) := by
        gcongr
      _ = (M ^ 2 * B * A) / (s ^ L * Real.sqrt s) := by
        field_simp [hspos.ne', hQpos.ne']
        ring
      _ ≤ (M ^ 2 * B * A + 1) / (s ^ L * Real.sqrt s) := by
        apply div_le_div_of_nonneg_right
        · linarith
        · positivity

/-- A differentiated triple with a multiplier-side middle factor is bounded
absolutely.  This is the rapid-decay arm of the literal cone split. -/
private theorem exists_oneMiddle_planarRadiusDerivativeCoordinateTripleWaveIntegral_bound
    (L : Nat) (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiRadial : IsNormRadial phi)
    (p q t : CoordinateWavePart) (hmiddle : q = .middle ∨ t = .middle) :
    ∃ C : Real, 0 < C ∧ ∀ s r r' : Real, 1 ≤ s →
      r ∈ Icc (1 / 2 : Real) (5 / 2) →
      r' ∈ Icc (1 / 2 : Real) (5 / 2) →
      ∀ v x : Euclidean 2, ‖v‖ = 1 →
      ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v x p q t u *
          oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ (s * r) (s * r')) u‖ ≤
        C / (s ^ L * Real.sqrt s) := by
  obtain ⟨A, hA, hAbound⟩ :=
    exists_uniform_planarCoordinateTripleWaveFixedAmplitude_bound 0 phi
      hphiOne hphiZero hphiRadial p
  obtain ⟨B, hB, hBbound⟩ :=
    exists_planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude_oneMiddle_scaled
      L q t hmiddle
  refine ⟨3 * A * B, mul_pos (mul_pos (by norm_num) hA) hB, ?_⟩
  intro s r r' hs hr hr' v x hv
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hdenpos : 0 < s ^ L * Real.sqrt s := by positivity
  have hpoint : ∀ u ∈ Icc (1 : Real) 4,
      ‖planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        (s * r) (s * r') v x p q t u *
        oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ (s * r) (s * r')) u‖ ≤
        (A * B) / (s ^ L * Real.sqrt s) := by
    intro u hu
    have huwide : u ∈ Icc (1 / 2 : Real) 8 := by
      constructor <;> linarith [hu.1, hu.2]
    have hfixed := hAbound v x hv 0 le_rfl u huwide
    have hpair := hBbound s r r' u hs hr hr' huwide
    have hfactor := planarRadiusDerivativeCoordinateTripleWaveCoefficient_eq_fixed_mul_pair
      phi hphiOne hphiZero (s * r) (s * r') v x p q t u
    rw [hfactor, norm_mul, norm_oscillatoryExp, mul_one]
    calc
      ‖planarCoordinateTripleWaveFixedAmplitude phi v x p u‖ *
          ‖planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude
            q t (s * r) (s * r') u‖ ≤
          A * (B / (s ^ L * Real.sqrt s)) := by
        exact mul_le_mul hfixed hpair (norm_nonneg _) hA.le
      _ = (A * B) / (s ^ L * Real.sqrt s) := by
        field_simp [hdenpos.ne']
        ring
  calc
    ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v x p q t u *
          oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ (s * r) (s * r')) u‖ ≤
        ((A * B) / (s ^ L * Real.sqrt s)) * |4 - (1 : Real)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro u hu
      have hu' : u ∈ Icc (1 : Real) 4 := by
        rw [uIoc_of_le (by norm_num : (1 : Real) ≤ 4)] at hu
        exact ⟨hu.1.le, hu.2⟩
      exact hpoint u hu'
    _ = (3 * A * B) / (s ^ L * Real.sqrt s) := by
      norm_num
      ring

/-- The literal differentiated diagonal estimate: two differentiated
multiplier-side symbols still contribute exactly the `s⁻¹` stationary
size, without using radial oscillation. -/
private theorem exists_planarRadiusDerivativeCoordinateTripleWaveIntegral_crude_bound
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiRadial : IsNormRadial phi)
    (p q t : CoordinateWavePart) :
    ∃ C : Real, 0 < C ∧ ∀ s r r' : Real, 1 ≤ s →
      r ∈ Icc (1 / 2 : Real) (5 / 2) →
      r' ∈ Icc (1 / 2 : Real) (5 / 2) →
      ∀ v x : Euclidean 2, ‖v‖ = 1 →
      ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v x p q t u *
          oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ (s * r) (s * r')) u‖ ≤
        C / s := by
  obtain ⟨A, hA, hAbound⟩ :=
    exists_uniform_planarCoordinateTripleWaveFixedAmplitude_bound 0 phi
      hphiOne hphiZero hphiRadial p
  obtain ⟨B, hB, hBbound⟩ :=
    exists_uniform_planarCoordinateWaveRadiusDerivativeMultiplierPair_scaled 0 q t
  refine ⟨3 * A * B, mul_pos (mul_pos (by norm_num) hA) hB, ?_⟩
  intro s r r' hs hr hr' v x hv
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hpoint : ∀ u ∈ Icc (1 : Real) 4,
      ‖planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        (s * r) (s * r') v x p q t u *
        oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ (s * r) (s * r')) u‖ ≤
        (A * B) / s := by
    intro u hu
    have huwide : u ∈ Icc (1 / 2 : Real) 8 := by
      constructor <;> linarith [hu.1, hu.2]
    have hfixed := hAbound v x hv 0 le_rfl u huwide
    have hpair := hBbound 0 le_rfl s r r' u hs hr hr' huwide
    have hfactor := planarRadiusDerivativeCoordinateTripleWaveCoefficient_eq_fixed_mul_pair
      phi hphiOne hphiZero (s * r) (s * r') v x p q t u
    rw [hfactor, norm_mul, norm_oscillatoryExp, mul_one]
    calc
      ‖planarCoordinateTripleWaveFixedAmplitude phi v x p u‖ *
          ‖planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude
            q t (s * r) (s * r') u‖ ≤
          A * (B / s) := by
        exact mul_le_mul hfixed hpair (norm_nonneg _) hA.le
      _ = (A * B) / s := by
        field_simp [hspos.ne']
        ring
  calc
    ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v x p q t u *
          oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ (s * r) (s * r')) u‖ ≤
        ((A * B) / s) * |4 - (1 : Real)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro u hu
      have hu' : u ∈ Icc (1 : Real) 4 := by
        rw [uIoc_of_le (by norm_num : (1 : Real) ≤ 4)] at hu
        exact ⟨hu.1.le, hu.2⟩
      exact hpoint u hu'
    _ = (3 * A * B) / s := by
      norm_num
      ring

/-- Physical planar waves retain their literal half-order stationary decay;
this unchanged factor is what controls the outer cone for the
radius-differentiated kernel. -/
private theorem exists_planarCoordinateWaveRadialAmplitude_physical_decay_forDerivative
    (p : CoordinateWavePart) :
    ∃ C : Real, 0 < C ∧ ∀ a u : Real, 1 ≤ a → u ∈ Icc (1 / 2 : Real) 8 →
      ‖planarCoordinateWaveRadialAmplitude p a u‖ ≤ C / Real.sqrt a := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedDeriv_planarCoordinateWave_scaled 0 p
  refine ⟨C, hC, ?_⟩
  intro a u ha hu
  simpa using hbound a 1 u ha (by constructor <;> norm_num) hu

/-- In the outer cone the physical stationary factor alone supplies the
radius-gap decay.  The multiplier factors are the literal differentiated
ones, so this remains an estimate for the actual radius derivative. -/
private theorem exists_outer_planarRadiusDerivativeCoordinateTripleWaveIntegral_bound
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiRadial : IsNormRadial phi)
    (p q t : CoordinateWavePart) :
    ∃ C : Real, 0 < C ∧ ∀ s r r' : Real, 1 ≤ s →
      r ∈ Icc (1 / 2 : Real) (5 / 2) →
      r' ∈ Icc (1 / 2 : Real) (5 / 2) →
      ∀ v x : Euclidean 2, ‖v‖ = 1 → 1 ≤ ‖x‖ →
      ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v x p q t u *
          oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ (s * r) (s * r')) u‖ ≤
        C / (s * Real.sqrt ‖x‖) := by
  let density : Real → Complex := fun u : Real => (u : Complex)
  have hdensity : ContDiff Real (⊤ : ℕ∞) density := by
    dsimp [density]
    fun_prop
  obtain ⟨A, hA, hAbound⟩ :=
    exists_uniform_iteratedDeriv_bound_on_fixedAnnulus density hdensity 0
  obtain ⟨D, hD, hDbound⟩ :=
    exists_uniform_normalizedDyadicCutoffSquare_bound_on_unit (N := 0)
      (by norm_num : 1 ≤ 2) phi hphiOne hphiZero hphiRadial
  obtain ⟨P, hP, hPbound⟩ :=
    exists_planarCoordinateWaveRadialAmplitude_physical_decay_forDerivative p
  obtain ⟨B, hB, hBbound⟩ :=
    exists_uniform_planarCoordinateWaveRadiusDerivativeMultiplierPair_scaled 0 q t
  refine ⟨3 * A * P * D * B,
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hA) hP) hD) hB, ?_⟩
  intro s r r' hs hr hr' v x hv hx
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hsqrtpos : 0 < Real.sqrt ‖x‖ := Real.sqrt_pos.2 hxpos
  have hpoint : ∀ u ∈ Icc (1 : Real) 4,
      ‖planarRadiusDerivativeCoordinateTripleWaveCoefficient
        (absoluteDyadicBandpass phi hphiOne hphiZero 0)
        (s * r) (s * r') v x p q t u *
        oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ (s * r) (s * r')) u‖ ≤
        (A * P * D * B) / (s * Real.sqrt ‖x‖) := by
    intro u hu
    have huwide : u ∈ Icc (1 / 2 : Real) 8 := by
      constructor <;> linarith [hu.1, hu.2]
    have hden := hAbound 0 le_rfl u huwide
    have hcut := hDbound v hv 0 le_rfl u huwide
    have hphysical := hPbound ‖x‖ u hx huwide
    have hpair := hBbound 0 le_rfl s r r' u hs hr hr' huwide
    have hfactor := planarRadiusDerivativeCoordinateTripleWaveCoefficient_eq_fixed_mul_pair
      phi hphiOne hphiZero (s * r) (s * r') v x p q t u
    rw [hfactor, norm_mul, norm_oscillatoryExp, mul_one]
    unfold planarCoordinateTripleWaveFixedAmplitude
    rw [norm_mul, norm_mul, norm_mul]
    calc
      ‖density u‖ * ‖planarCoordinateWaveRadialAmplitude p ‖x‖ u‖ *
          ‖normalizedDyadicCutoffSquare phi v u‖ *
            ‖planarCoordinateWaveRadiusDerivativeMultiplierPairAmplitude
              q t (s * r) (s * r') u‖ ≤
          A * (P / Real.sqrt ‖x‖) * D * (B / s) := by
        gcongr
      _ = (A * P * D * B) / (s * Real.sqrt ‖x‖) := by
        field_simp [hspos.ne', hsqrtpos.ne']
        ring
  calc
    ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v x p q t u *
          oscillatoryExp (coordinateTripleWavePhase p q t ‖x‖ (s * r) (s * r')) u‖ ≤
        ((A * P * D * B) / (s * Real.sqrt ‖x‖)) * |4 - (1 : Real)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro u hu
      have hu' : u ∈ Icc (1 : Real) 4 := by
        rw [uIoc_of_le (by norm_num : (1 : Real) ≤ 4)] at hu
        exact ⟨hu.1.le, hu.2⟩
      exact hpoint u hu'
    _ = (3 * A * P * D * B) / (s * Real.sqrt ‖x‖) := by
      norm_num
      ring

/-! ## The differentiated planar conic gap split -/

private theorem planarRadiusDerivative_q4_crude_scale_le_stationaryWeight
    {C s T : Real} (hs : 1 ≤ s) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hsmall : T ≤ 4) :
    C / s ≤ (C * (5 : Real) ^ 2) / s *
      (1 + T) ^ (-q4StationaryExponent 2) := by
  simpa using q4_crude_scale_le_stationaryWeight (d := 2)
    (by norm_num : 1 ≤ 2) hs hC hT hsmall

private theorem planarRadiusDerivative_q4_inner_ibp_scale_le_stationaryWeight
    {C s T : Real} (hs : 1 ≤ s) (hC : 0 ≤ C) (hT : 1 ≤ T) :
    (4 / T) ^ 2 * ((8 - (1 / 2 : Real)) * (C / s)) ≤
      ((8 - (1 / 2 : Real)) * C * (8 : Real) ^ 2) / s *
        (1 + T) ^ (-q4StationaryExponent 2) := by
  simpa using q4_inner_ibp_scale_le_stationaryWeight (d := 2)
    (by norm_num : 1 ≤ 2) hs hC hT

private theorem planarRadiusDerivative_q4_outer_scale_le_stationaryWeight
    {C s T X : Real} (hs : 1 ≤ s) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hX : T / 4 ≤ X) :
    C / (s * Real.sqrt X) ≤ (C * (8 : Real) ^ 2) / s *
      (1 + T) ^ (-q4StationaryExponent 2) := by
  simpa using q4_outer_scale_le_stationaryWeight (d := 2)
    (by norm_num : 1 ≤ 2) hs hC hT hX

private theorem planarRadiusDerivative_q4_middle_scale_le_stationaryWeight
    {C s T : Real} (hs : 1 ≤ s) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hTscale : T ≤ 2 * s) :
    C / (s ^ 4 * Real.sqrt s) ≤ (C * (3 : Real) ^ 2) / s *
      (1 + T) ^ (-q4StationaryExponent 2) := by
  simpa using q4_middle_scale_le_stationaryWeight (d := 2)
    (by norm_num : 1 ≤ 2) hs hC hT hTscale

private theorem planarRadiusDerivative_q4_scaleWeight_mono
    {A B s T : Real} (hs : 1 ≤ s) (hT : 0 ≤ T) (hAB : A ≤ B) :
    A / s * (1 + T) ^ (-q4StationaryExponent 2) ≤
      B / s * (1 + T) ^ (-q4StationaryExponent 2) := by
  simpa using q4_scaleWeight_mono (d := 2) hs hT hAB

/-- Every literal differentiated planar coordinate triple obeys the
stationary radius-gap estimate.  This is the cone argument from the paper
applied to the actual differentiated 27-term normal form: diagonal size for
small gaps, physical stationary decay in the outer cone, integration by
parts for endpoint phases in the inner cone, and rapid sine-moment decay
when a multiplier-side factor is middle. -/
/-- The literal differentiated coordinate-triple stationary gap estimate,
exported for the finite 27-term source. -/
theorem exists_planarRadiusDerivativeCoordinateTripleWaveIntegral_stationaryGap_bound
    (phi : SchwartzMap (Euclidean 2) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiRadial : IsNormRadial phi)
    (p q t : CoordinateWavePart) :
    ∃ C : Real, 0 < C ∧ ∀ s r r' : Real, 1 ≤ s →
      r ∈ Icc (1 / 2 : Real) (5 / 2) →
      r' ∈ Icc (1 / 2 : Real) (5 / 2) →
      ∀ v x : Euclidean 2, ‖v‖ = 1 →
      ‖∫ u in (1 : Real)..4,
        planarRadiusDerivativeCoordinateTripleWaveCoefficient
          (absoluteDyadicBandpass phi hphiOne hphiZero 0)
          (s * r) (s * r') v (s • x) p q t u *
          oscillatoryExp
            (coordinateTripleWavePhase p q t ‖s • x‖ (s * r) (s * r')) u‖ ≤
        C / s * (1 + s * |r - r'|) ^ (-q4StationaryExponent 2) := by
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    exists_planarRadiusDerivativeCoordinateTripleWaveIntegral_crude_bound
      phi hphiOne hphiZero hphiRadial p q t
  obtain ⟨Couter, hCouter, houter⟩ :=
    exists_outer_planarRadiusDerivativeCoordinateTripleWaveIntegral_bound
      phi hphiOne hphiZero hphiRadial p q t
  by_cases hmiddle : q = .middle ∨ t = .middle
  · obtain ⟨Cmiddle, hCmiddle, hmiddleBound⟩ :=
      exists_oneMiddle_planarRadiusDerivativeCoordinateTripleWaveIntegral_bound 4
        phi hphiOne hphiZero hphiRadial p q t hmiddle
    let C : Real := Csmall * (5 : Real) ^ 2 + Couter * (8 : Real) ^ 2 +
      Cmiddle * (3 : Real) ^ 2
    have hCnonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    refine ⟨C + 1, by linarith, ?_⟩
    intro s r r' hs hr hr' v x hv
    let g : Real := |r - r'|
    let T : Real := s * g
    let y : Euclidean 2 := s • x
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
    have hg : 0 ≤ g := abs_nonneg _
    have hgupper : g ≤ 2 := by
      dsimp [g]
      apply (abs_le).2
      constructor <;> linarith [hr.1, hr.2, hr'.1, hr'.2]
    have hT : 0 ≤ T := by
      dsimp [T]
      positivity
    have hTscale : T ≤ 2 * s := by
      dsimp [T]
      calc
        s * g ≤ s * 2 := mul_le_mul_of_nonneg_left hgupper hs.le
        _ = 2 * s := by ring
    have hyNorm : ‖y‖ = s * ‖x‖ := by
      dsimp [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    by_cases hsmallGap : T ≤ 4
    · have hcrude := hsmall s r r' hs hr hr' v y hv
      have hnum := planarRadiusDerivative_q4_crude_scale_le_stationaryWeight
        hs hCsmall.le hT hsmallGap
      calc
        ‖∫ u in (1 : Real)..4,
            planarRadiusDerivativeCoordinateTripleWaveCoefficient
              (absoluteDyadicBandpass phi hphiOne hphiZero 0)
              (s * r) (s * r') v y p q t u *
              oscillatoryExp
                (coordinateTripleWavePhase p q t ‖y‖ (s * r) (s * r')) u‖ ≤
            Csmall / s := hcrude
        _ ≤ (Csmall * (5 : Real) ^ 2) / s *
            (1 + T) ^ (-q4StationaryExponent 2) := hnum
        _ ≤ (C + 1) / s *
            (1 + T) ^ (-q4StationaryExponent 2) := by
          apply planarRadiusDerivative_q4_scaleWeight_mono hs hT
          dsimp [C]
          positivity
    · have hlarge : 4 < T := lt_of_not_ge hsmallGap
      have hTone : 1 ≤ T := by linarith
      by_cases hphysical : g / 4 ≤ ‖x‖
      · have hyOuter : T / 4 ≤ ‖y‖ := by
          rw [hyNorm]
          dsimp [T]
          calc
            s * g / 4 = s * (g / 4) := by ring
            _ ≤ s * ‖x‖ := mul_le_mul_of_nonneg_left hphysical hs.le
        have hyOne : 1 ≤ ‖y‖ := by
          calc
            (1 : Real) ≤ T / 4 := by linarith
            _ ≤ ‖y‖ := hyOuter
        have hphysicalBound := houter s r r' hs hr hr' v y hv hyOne
        have hnum := planarRadiusDerivative_q4_outer_scale_le_stationaryWeight
          hs hCouter.le hTone hyOuter
        calc
          ‖∫ u in (1 : Real)..4,
              planarRadiusDerivativeCoordinateTripleWaveCoefficient
                (absoluteDyadicBandpass phi hphiOne hphiZero 0)
                (s * r) (s * r') v y p q t u *
                oscillatoryExp
                  (coordinateTripleWavePhase p q t ‖y‖ (s * r) (s * r')) u‖ ≤
              Couter / (s * Real.sqrt ‖y‖) := hphysicalBound
          _ ≤ (Couter * (8 : Real) ^ 2) / s *
              (1 + T) ^ (-q4StationaryExponent 2) := hnum
          _ ≤ (C + 1) / s *
              (1 + T) ^ (-q4StationaryExponent 2) := by
            apply planarRadiusDerivative_q4_scaleWeight_mono hs hT
            dsimp [C]
            positivity
      · have hmiddleBound' := hmiddleBound s r r' hs hr hr' v y hv
        have hnum := planarRadiusDerivative_q4_middle_scale_le_stationaryWeight
          hs hCmiddle.le hT hTscale
        calc
          ‖∫ u in (1 : Real)..4,
              planarRadiusDerivativeCoordinateTripleWaveCoefficient
                (absoluteDyadicBandpass phi hphiOne hphiZero 0)
                (s * r) (s * r') v y p q t u *
                oscillatoryExp
                  (coordinateTripleWavePhase p q t ‖y‖ (s * r) (s * r')) u‖ ≤
              Cmiddle / (s ^ 4 * Real.sqrt s) := hmiddleBound'
          _ ≤ (Cmiddle * (3 : Real) ^ 2) / s *
              (1 + T) ^ (-q4StationaryExponent 2) := hnum
          _ ≤ (C + 1) / s *
              (1 + T) ^ (-q4StationaryExponent 2) := by
            apply planarRadiusDerivative_q4_scaleWeight_mono hs hT
            dsimp [C]
            positivity
  · have hq : q ≠ .middle := by
      intro hq
      exact hmiddle (Or.inl hq)
    have ht : t ≠ .middle := by
      intro ht
      exact hmiddle (Or.inr ht)
    obtain ⟨Cinner, hCinner, hinnerBound⟩ :
        ∃ C : Real, 0 < C ∧ ∀ s r r' : Real, 1 ≤ s →
          r ∈ Icc (1 / 2 : Real) (5 / 2) →
          r' ∈ Icc (1 / 2 : Real) (5 / 2) → r ≠ r' →
          ∀ v x : Euclidean 2, ‖v‖ = 1 → ‖x‖ ≤ |r - r'| / 4 →
          ‖∫ u in (1 : Real)..4,
            planarRadiusDerivativeCoordinateTripleWaveCoefficient
              (absoluteDyadicBandpass phi hphiOne hphiZero 0)
              (s * r) (s * r') v (s • x) p q t u *
              oscillatoryExp
                (coordinateTripleWavePhase p q t ‖s • x‖ (s * r) (s * r')) u‖ ≤
            (4 / (s * |r - r'|)) ^ 2 *
              ((8 - (1 / 2 : Real)) * (C / s)) := by
      by_cases hp : p = .middle
      · subst p
        exact exists_inner_physicalMiddle_planarRadiusDerivativeCoordinateTripleWaveIntegral_bound
          phi hphiOne hphiZero hphiRadial q t hq ht
      · exact exists_inner_endpoint_planarRadiusDerivativeCoordinateTripleWaveIntegral_bound
          phi hphiOne hphiZero hphiRadial p q t hp hq ht
    let C : Real := Csmall * (5 : Real) ^ 2 + Couter * (8 : Real) ^ 2 +
      ((8 - (1 / 2 : Real)) * Cinner * (8 : Real) ^ 2)
    have hCnonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    refine ⟨C + 1, by linarith, ?_⟩
    intro s r r' hs hr hr' v x hv
    let g : Real := |r - r'|
    let T : Real := s * g
    let y : Euclidean 2 := s • x
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
    have hg : 0 ≤ g := abs_nonneg _
    have hT : 0 ≤ T := by
      dsimp [T]
      positivity
    have hyNorm : ‖y‖ = s * ‖x‖ := by
      dsimp [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    by_cases hsmallGap : T ≤ 4
    · have hcrude := hsmall s r r' hs hr hr' v y hv
      have hnum := planarRadiusDerivative_q4_crude_scale_le_stationaryWeight
        hs hCsmall.le hT hsmallGap
      calc
        ‖∫ u in (1 : Real)..4,
            planarRadiusDerivativeCoordinateTripleWaveCoefficient
              (absoluteDyadicBandpass phi hphiOne hphiZero 0)
              (s * r) (s * r') v y p q t u *
              oscillatoryExp
                (coordinateTripleWavePhase p q t ‖y‖ (s * r) (s * r')) u‖ ≤
            Csmall / s := hcrude
        _ ≤ (Csmall * (5 : Real) ^ 2) / s *
            (1 + T) ^ (-q4StationaryExponent 2) := hnum
        _ ≤ (C + 1) / s *
            (1 + T) ^ (-q4StationaryExponent 2) := by
          apply planarRadiusDerivative_q4_scaleWeight_mono hs hT
          dsimp [C]
          positivity
    · have hlarge : 4 < T := lt_of_not_ge hsmallGap
      have hTone : 1 ≤ T := by linarith
      by_cases hphysical : g / 4 ≤ ‖x‖
      · have hyOuter : T / 4 ≤ ‖y‖ := by
          rw [hyNorm]
          dsimp [T]
          calc
            s * g / 4 = s * (g / 4) := by ring
            _ ≤ s * ‖x‖ := mul_le_mul_of_nonneg_left hphysical hs.le
        have hyOne : 1 ≤ ‖y‖ := by
          calc
            (1 : Real) ≤ T / 4 := by linarith
            _ ≤ ‖y‖ := hyOuter
        have hphysicalBound := houter s r r' hs hr hr' v y hv hyOne
        have hnum := planarRadiusDerivative_q4_outer_scale_le_stationaryWeight
          hs hCouter.le hTone hyOuter
        calc
          ‖∫ u in (1 : Real)..4,
              planarRadiusDerivativeCoordinateTripleWaveCoefficient
                (absoluteDyadicBandpass phi hphiOne hphiZero 0)
                (s * r) (s * r') v y p q t u *
                oscillatoryExp
                  (coordinateTripleWavePhase p q t ‖y‖ (s * r) (s * r')) u‖ ≤
              Couter / (s * Real.sqrt ‖y‖) := hphysicalBound
          _ ≤ (Couter * (8 : Real) ^ 2) / s *
              (1 + T) ^ (-q4StationaryExponent 2) := hnum
          _ ≤ (C + 1) / s *
              (1 + T) ^ (-q4StationaryExponent 2) := by
            apply planarRadiusDerivative_q4_scaleWeight_mono hs hT
            dsimp [C]
            positivity
      · have hinner : ‖x‖ ≤ g / 4 := le_of_lt (lt_of_not_ge hphysical)
        have hIBP := hinnerBound s r r' hs hr hr'
          (by
            intro hrr
            have hzero : g = 0 := by
              dsimp [g]
              exact abs_eq_zero.mpr (sub_eq_zero.mpr hrr)
            dsimp [T] at hlarge
            rw [hzero, mul_zero] at hlarge
            linarith)
          v x hv hinner
        have hnum := planarRadiusDerivative_q4_inner_ibp_scale_le_stationaryWeight
          hs hCinner.le hTone
        calc
          ‖∫ u in (1 : Real)..4,
              planarRadiusDerivativeCoordinateTripleWaveCoefficient
                (absoluteDyadicBandpass phi hphiOne hphiZero 0)
                (s * r) (s * r') v y p q t u *
                oscillatoryExp
                  (coordinateTripleWavePhase p q t ‖y‖ (s * r) (s * r')) u‖ ≤
              (4 / (s * g)) ^ 2 *
                ((8 - (1 / 2 : Real)) * (Cinner / s)) := by
              simpa only [y, T, g] using hIBP
          _ ≤ ((8 - (1 / 2 : Real)) * Cinner * (8 : Real) ^ 2) / s *
              (1 + T) ^ (-q4StationaryExponent 2) := by
              simpa only [T] using hnum
          _ ≤ (C + 1) / s *
              (1 + T) ^ (-q4StationaryExponent 2) := by
            apply planarRadiusDerivative_q4_scaleWeight_mono hs hT
            dsimp [C]
            positivity

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
