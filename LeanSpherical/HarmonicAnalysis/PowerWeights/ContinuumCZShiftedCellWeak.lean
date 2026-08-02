/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.ContinuumCZWeak

/-!
# Frequency-shifted cell Calderón--Zygmund endpoint

For literal short radius cells, the bad part is split at a cube scale shifted
by the relative frequency index.  The cells between the ordinary and shifted
scales are paid directly in `L¹`; cancellation is used only beyond the shifted
scale.  This is the cell analogue of `LacunaryCZShiftedWeak`.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory FourierTransform Metric Set intervalIntegral
open scoped BigOperators Convolution FourierTransform ENNReal ComplexConjugate

noncomputable section

/-- The `j` physical dyadic blocks immediately above a stopping cube.  They
are the part of a frequency-shifted C--Z split which is paid directly in
`L¹`. -/
def lacunaryCZDyadicCubeShiftedCellMiddleIndices
    {d N : Nat} (K : Finset ℤ) (j : Nat) (q : LacunaryCZDyadicCubeIndex d) :
    Finset (ℤ × Fin N) :=
  (K.product Finset.univ).filter fun z =>
    q.scale < z.1 ∧ z.1 ≤ q.scale + (j : ℤ)

/-- The physical cells strictly beyond the frequency-shifted stopping scale. -/
def lacunaryCZDyadicCubeShiftedCellFutureIndices
    {d N : Nat} (K : Finset ℤ) (j : Nat) (q : LacunaryCZDyadicCubeIndex d) :
    Finset (ℤ × Fin N) :=
  (K.product Finset.univ).filter fun z => q.scale + (j : ℤ) < z.1

/-- Splitting literal cell oscillation into past cells, the finite middle
range, and cells beyond the frequency-shifted cube scale. -/
theorem lacunaryRelativeBandpassPhysicalCellOscillation_shifted_threeWay_scale_split
    {d N : Nat} (K : Finset ℤ) (ψ : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (a b : ℤ × Fin N → ℝ) (q : LacunaryCZDyadicCubeIndex d)
    (g : Euclidean d → ℂ) (x : Euclidean d) :
    lacunaryRelativeBandpassPhysicalCellOscillation ψ j
        (K.product Finset.univ) a b g x =
      lacunaryRelativeBandpassPhysicalCellOscillation ψ j
          ((K.product Finset.univ).filter fun z => z.1 ≤ q.scale) a b g x +
        lacunaryRelativeBandpassPhysicalCellOscillation ψ j
          (lacunaryCZDyadicCubeShiftedCellMiddleIndices K j q) a b g x +
        lacunaryRelativeBandpassPhysicalCellOscillation ψ j
          (lacunaryCZDyadicCubeShiftedCellFutureIndices K j q) a b g x := by
  classical
  unfold lacunaryRelativeBandpassPhysicalCellOscillation
    lacunaryCZDyadicCubeShiftedCellMiddleIndices
    lacunaryCZDyadicCubeShiftedCellFutureIndices
  rw [← Finset.sum_filter_add_sum_filter_not
    (p := fun z : ℤ × Fin N => z.1 ≤ q.scale)]
  simp only [not_le]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (K.product Finset.univ).filter fun z => q.scale < z.1)
    (p := fun z : ℤ × Fin N => z.1 ≤ q.scale + (j : ℤ))]
  simp only [Finset.filter_filter, not_le]
  have hfuture :
      (K.product Finset.univ).filter fun z : ℤ × Fin N =>
        q.scale < z.1 ∧ q.scale + (j : ℤ) < z.1 =
      (K.product Finset.univ).filter fun z : ℤ × Fin N =>
        q.scale + (j : ℤ) < z.1 := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, _, hshift⟩
      exact ⟨hz, hshift⟩
    · rintro ⟨hz, hshift⟩
      refine ⟨hz, ?_, hshift⟩
      have hj : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
      omega
  rw [hfuture]
  ring

/-- The usual geometric cell-width tail, started at the shifted parent of a
stopping cube. -/
theorem sum_dyadicPhysicalEntropyCell_length_mul_left_inv_sq_shiftedFuture_le
    {d N : Nat} (K : Finset ℤ) (δ : NNReal)
    (r : Fin N → ℤ → PositiveRadius)
    (hr : ∀ i, IsDyadicLacunaryRadiusSelector (r i))
    (j : Nat) (q : LacunaryCZDyadicCubeIndex d)
    (hδ : Real.log 2 * (δ : ℝ) ≤ 1) :
    (∑ z ∈ lacunaryCZDyadicCubeShiftedCellFutureIndices K j q,
      (dyadicPhysicalEntropyCellRight δ r z -
        dyadicPhysicalEntropyCellLeft δ r z) *
          (dyadicPhysicalEntropyCellLeft δ r z)⁻¹ ^ 2) ≤
        (N : ℝ) * (2 * (8 * Real.log 2 * (δ : ℝ))) *
          ((2 : ℝ) ^ (q.scale + (j : ℤ)))⁻¹ := by
  simpa only [lacunaryCZDyadicCubeShiftedCellFutureIndices,
    lacunaryCZDyadicCubeParentIter_scale] using
    sum_dyadicPhysicalEntropyCell_length_mul_left_inv_sq_future_le
      K δ r hr (lacunaryCZDyadicCubeParentIter j q) hδ

/-- There are at most `j` dyadic scales in the middle part of the shifted
split, for each palette colour. -/
theorem card_lacunaryCZDyadicCubeShiftedCellMiddleIndices_le
    {d N : Nat} (K : Finset ℤ) (j : Nat) (q : LacunaryCZDyadicCubeIndex d) :
    (lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q).card ≤ N * j := by
  have hsubset :
      lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q ⊆
        (Finset.Icc (q.scale + 1) (q.scale + (j : ℤ))).product Finset.univ := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨_, hzlow, hzup⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (by omega), Finset.mem_univ _⟩
  calc
    (lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q).card ≤
        ((Finset.Icc (q.scale + 1) (q.scale + (j : ℤ))).product
          (Finset.univ : Finset (Fin N))).card := Finset.card_le_card hsubset
    _ = j * N := by
      calc
        _ = (Finset.Icc (q.scale + 1) (q.scale + (j : ℤ))).card *
            (Finset.univ : Finset (Fin N)).card :=
          Finset.card_product _ _
        _ = _ := by
          rw [Finset.card_univ, Fintype.card_fin, Int.card_Icc]
          have hdiff : q.scale + (j : ℤ) + 1 - (q.scale + 1) = (j : ℤ) := by
            ring
          rw [hdiff]
          simp
    _ = N * j := Nat.mul_comm _ _

/-- The total relative width of the `j` middle scales is at most its cardinal
loss times the logarithmic entropy width. -/
theorem sum_dyadicPhysicalEntropyCell_length_mul_left_inv_shiftedMiddle_le
    {d N : Nat} (K : Finset ℤ) (δ : NNReal)
    (r : Fin N → ℤ → PositiveRadius)
    (hr : ∀ i, IsDyadicLacunaryRadiusSelector (r i))
    (j : Nat) (q : LacunaryCZDyadicCubeIndex d)
    (hδ : Real.log 2 * (δ : ℝ) ≤ 1) :
    (∑ z ∈ lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q,
      (dyadicPhysicalEntropyCellRight δ r z -
        dyadicPhysicalEntropyCellLeft δ r z) *
          (dyadicPhysicalEntropyCellLeft δ r z)⁻¹) ≤
        (N : ℝ) * (j : ℝ) * (8 * Real.log 2 * (δ : ℝ)) := by
  let L : ℝ := 8 * Real.log 2 * (δ : ℝ)
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) δ.2
  have hterm (z : ℤ × Fin N)
      (hz : z ∈ lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q) :
      (dyadicPhysicalEntropyCellRight δ r z -
        dyadicPhysicalEntropyCellLeft δ r z) *
          (dyadicPhysicalEntropyCellLeft δ r z)⁻¹ ≤ L := by
    let a : ℝ := dyadicPhysicalEntropyCellLeft δ r z
    let b : ℝ := dyadicPhysicalEntropyCellRight δ r z
    let R : ℝ := (2 : ℝ) ^ z.1
    have hR : 0 < R := zpow_pos (by norm_num) z.1
    have ha : 0 < a := by
      simpa only [a] using dyadicPhysicalEntropyCellLeft_pos δ r hr z
    have hlength : b - a ≤ R * L := by
      simpa only [a, b, R, L] using
        dyadicPhysicalEntropyCell_length_le_linear δ r hr z hδ
    have hleft : R ≤ a := by
      simpa only [a, R] using
        (dyadicPhysicalEntropyCell_endpoints_mem_block δ r hr z).1.1
    have hinv : a⁻¹ ≤ R⁻¹ := inv_anti₀ hR hleft
    have hRL : 0 ≤ R * L := mul_nonneg hR.le hL
    calc
      (dyadicPhysicalEntropyCellRight δ r z -
        dyadicPhysicalEntropyCellLeft δ r z) *
          (dyadicPhysicalEntropyCellLeft δ r z)⁻¹ = (b - a) * a⁻¹ := by rfl
      _ ≤ (R * L) * a⁻¹ :=
        mul_le_mul_of_nonneg_right hlength (inv_nonneg.mpr ha.le)
      _ ≤ (R * L) * R⁻¹ := mul_le_mul_of_nonneg_left hinv hRL
      _ = L := by field_simp [hR.ne']
  have hsum :
      (∑ z ∈ lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q,
        (dyadicPhysicalEntropyCellRight δ r z -
          dyadicPhysicalEntropyCellLeft δ r z) *
            (dyadicPhysicalEntropyCellLeft δ r z)⁻¹) ≤
        ((lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q).card : ℝ) * L := by
    calc
      (∑ z ∈ lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q,
        (dyadicPhysicalEntropyCellRight δ r z -
          dyadicPhysicalEntropyCellLeft δ r z) *
            (dyadicPhysicalEntropyCellLeft δ r z)⁻¹) ≤
          ∑ _z ∈ lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q, L :=
        Finset.sum_le_sum fun z hz => hterm z hz
      _ = ((lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q).card : ℝ) * L := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard :
      ((lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q).card : ℝ) ≤
        (N : ℝ) * (j : ℝ) := by
    exact_mod_cast card_lacunaryCZDyadicCubeShiftedCellMiddleIndices_le K j q
  calc
    (∑ z ∈ lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q,
      (dyadicPhysicalEntropyCellRight δ r z -
        dyadicPhysicalEntropyCellLeft δ r z) *
          (dyadicPhysicalEntropyCellLeft δ r z)⁻¹) ≤
        ((lacunaryCZDyadicCubeShiftedCellMiddleIndices (N := N) K j q).card : ℝ) * L := hsum
    _ ≤ ((N : ℝ) * (j : ℝ)) * L :=
      mul_le_mul_of_nonneg_right hcard hL
    _ = (N : ℝ) * (j : ℝ) * (8 * Real.log 2 * (δ : ℝ)) := by
      dsimp only [L]

/-- The normalized dilation of a Schwartz generator has the expected
`L¹` scaling.  This is kept private: it is only the Fubini bookkeeping
behind the direct treatment of the finitely many middle cells. -/
private theorem integral_norm_rawRadiusGeneratorDilation_eq
    {d : Nat} (G : SchwartzMap (Euclidean d) ℂ)
    {t : ℝ} (ht : 0 < t) :
    (∫ x : Euclidean d,
      ‖(t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • x)‖) =
        t⁻¹ * ∫ x : Euclidean d, ‖G x‖ := by
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  calc
    (∫ x : Euclidean d,
      ‖(t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • x)‖) =
        t⁻¹ ^ (d + 1) * ∫ x : Euclidean d, ‖G (t⁻¹ • x)‖ := by
          rw [show (fun x : Euclidean d =>
              ‖(t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • x)‖) =
              fun x => t⁻¹ ^ (d + 1) * ‖G (t⁻¹ • x)‖ by
            funext x
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg htinv.le _)], MeasureTheory.integral_const_mul]
    _ = t⁻¹ ^ (d + 1) * ((t⁻¹ ^ d)⁻¹ *
          ∫ x : Euclidean d, ‖G x‖) := by
          rw [integral_norm_comp_smul_eq d G htinv]
    _ = t⁻¹ * ∫ x : Euclidean d, ‖G x‖ := by
          have ht0 : t ≠ 0 := ht.ne'
          have hpow : t⁻¹ ^ (d + 1) * (t⁻¹ ^ d)⁻¹ = t⁻¹ := by
            have hinvpow : (t⁻¹ ^ d)⁻¹ = t ^ d := by
              rw [← inv_pow, inv_inv]
            rw [hinvpow, pow_succ]
            calc
              t⁻¹ ^ d * t⁻¹ * t ^ d =
                  t⁻¹ * (t⁻¹ ^ d * t ^ d) := by ring
              _ = t⁻¹ * ((t⁻¹ * t) ^ d) := by rw [mul_pow]
              _ = t⁻¹ := by rw [inv_mul_cancel₀ ht0, one_pow, mul_one]
          rw [← mul_assoc, hpow]

/-- Joint integrability in a compact positive radius interval for the raw
generator dilation. -/
private theorem integrable_uncurry_rawRadiusGeneratorDilation_on_Icc
    {d : Nat} (G : SchwartzMap (Euclidean d) ℂ)
    {a b : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ × Euclidean d =>
      (p.1⁻¹ ^ (d + 1) : ℝ) • G (p.1⁻¹ • p.2))
      ((volume.restrict (Icc a b)).prod volume) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let H : ℝ → Euclidean d → ℂ := fun t x =>
    (t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • x)
  have hHmeas : AEStronglyMeasurable (Function.uncurry H) (ν.prod volume) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [H]
    fun_prop
  have hHslice (t : ℝ) (ht : 0 < t) : Integrable (H t) volume := by
    dsimp only [H]
    exact Integrable.smul (t⁻¹ ^ (d + 1) : ℝ)
      (Integrable.comp_smul G.integrable (inv_ne_zero ht.ne'))
  let M : ℝ := a⁻¹ * ∫ x : Euclidean d, ‖G x‖
  have hHouter : Integrable (fun t : ℝ => ∫ x : Euclidean d, ‖H t x‖) ν := by
    refine Integrable.mono' (g := fun _ : ℝ => M) (integrable_const M) ?_ ?_
    · exact hHmeas.norm.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have htpos : 0 < t := lt_of_lt_of_le ha ht.1
      have hinv : t⁻¹ ≤ a⁻¹ := inv_anti₀ ha ht.1
      have hGnon : 0 ≤ ∫ x : Euclidean d, ‖G x‖ :=
        integral_nonneg fun _ => norm_nonneg _
      have hleftnon : 0 ≤ ∫ x : Euclidean d, ‖H t x‖ :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hleftnon]
      calc
        (∫ x : Euclidean d, ‖H t x‖) =
            t⁻¹ * ∫ x : Euclidean d, ‖G x‖ := by
              dsimp only [H]
              exact integral_norm_rawRadiusGeneratorDilation_eq G htpos
        _ ≤ a⁻¹ * ∫ x : Euclidean d, ‖G x‖ :=
          mul_le_mul_of_nonneg_right hinv hGnon
        _ = M := rfl
  have hprod : Integrable (Function.uncurry H) (ν.prod volume) := by
    refine (integrable_prod_iff hHmeas).2 ?_
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hHslice t (lt_of_lt_of_le ha ht.1)
    · exact hHouter
  change Integrable (Function.uncurry H) (ν.prod volume)
  exact hprod

/-- Spatial translation does not affect the raw product-space generator
integrability. -/
private theorem integrable_uncurry_rawRadiusGeneratorDilation_sub_right_on_Icc
    {d : Nat} (G : SchwartzMap (Euclidean d) ℂ)
    {a b : ℝ} (ha : 0 < a) (c : Euclidean d) :
    Integrable (fun p : ℝ × Euclidean d =>
      (p.1⁻¹ ^ (d + 1) : ℝ) • G (p.1⁻¹ • (p.2 - c)))
      ((volume.restrict (Icc a b)).prod volume) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let A : ℝ × Euclidean d → ℂ := fun p =>
    (p.1⁻¹ ^ (d + 1) : ℝ) • G (p.1⁻¹ • p.2)
  have hA : Integrable A (ν.prod volume) := by
    simpa only [A, ν] using
      integrable_uncurry_rawRadiusGeneratorDilation_on_Icc G (b := b) ha
  let τ : ℝ × Euclidean d → ℝ × Euclidean d := fun p => (p.1, p.2 - c)
  have hτ : MeasurePreserving τ (ν.prod volume) (ν.prod volume) := by
    change MeasurePreserving (Prod.map id (fun x : Euclidean d => x - c))
      (ν.prod volume) (ν.prod volume)
    exact (MeasurePreserving.id ν).prod
      (measurePreserving_sub_right (volume : Measure (Euclidean d)) c)
  have hcomp : Integrable (A ∘ τ) (ν.prod volume) :=
    (hτ.integrable_comp hA.aestronglyMeasurable).mpr hA
  simpa only [A, τ, Function.comp_def, ν] using hcomp

/-- The raw generator over one positive cell costs its relative width in
`L¹`. -/
private theorem integral_norm_rawRadiusGeneratorDilation_sub_right_on_Icc_le
    {d : Nat} (G : SchwartzMap (Euclidean d) ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : Euclidean d) :
    (∫ p : ℝ × Euclidean d,
      ‖(p.1⁻¹ ^ (d + 1) : ℝ) • G (p.1⁻¹ • (p.2 - c))‖
        ∂((volume.restrict (Icc a b)).prod volume)) ≤
      (b - a) * a⁻¹ * ∫ x : Euclidean d, ‖G x‖ := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let A : ℝ × Euclidean d → ℂ := fun p =>
    (p.1⁻¹ ^ (d + 1) : ℝ) • G (p.1⁻¹ • p.2)
  let B : ℝ × Euclidean d → ℂ := fun p =>
    (p.1⁻¹ ^ (d + 1) : ℝ) • G (p.1⁻¹ • (p.2 - c))
  have hA : Integrable A (ν.prod volume) := by
    simpa only [A, ν] using
      integrable_uncurry_rawRadiusGeneratorDilation_on_Icc G (b := b) ha
  have hB : Integrable B (ν.prod volume) := by
    simpa only [B, ν] using
      integrable_uncurry_rawRadiusGeneratorDilation_sub_right_on_Icc G (b := b) ha c
  have houter : Integrable (fun t : ℝ => ∫ x : Euclidean d, ‖A (t, x)‖) ν := by
    exact hA.norm.integral_prod_left
  have hinterval : IntervalIntegrable (fun t : ℝ => ∫ x : Euclidean d, ‖A (t, x)‖)
      volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact houter
  let M : ℝ := a⁻¹ * ∫ x : Euclidean d, ‖G x‖
  have hconst : IntervalIntegrable (fun _ : ℝ => M) volume a b :=
    intervalIntegrable_const
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ x : Euclidean d, ‖A (t, x)‖) ≤ M := by
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hinv : t⁻¹ ≤ a⁻¹ := inv_anti₀ ha ht.1
    have hGnon : 0 ≤ ∫ x : Euclidean d, ‖G x‖ :=
      integral_nonneg fun _ => norm_nonneg _
    calc
      (∫ x : Euclidean d, ‖A (t, x)‖) =
          t⁻¹ * ∫ x : Euclidean d, ‖G x‖ := by
            dsimp only [A]
            exact integral_norm_rawRadiusGeneratorDilation_eq G htpos
      _ ≤ a⁻¹ * ∫ x : Euclidean d, ‖G x‖ :=
        mul_le_mul_of_nonneg_right hinv hGnon
      _ = M := rfl
  have hAinterval :
      (∫ p : ℝ × Euclidean d, ‖A p‖ ∂(ν.prod volume)) ≤
        (b - a) * a⁻¹ * ∫ x : Euclidean d, ‖G x‖ := by
    calc
      (∫ p : ℝ × Euclidean d, ‖A p‖ ∂(ν.prod volume)) =
          ∫ t : ℝ, ∫ x : Euclidean d, ‖A (t, x)‖ ∂volume ∂ν :=
            integral_prod _ hA.norm
      _ = ∫ t in a..b, ∫ x : Euclidean d, ‖A (t, x)‖ := by
            simp only [ν]
            rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
      _ ≤ ∫ t in a..b, M := by
            apply intervalIntegral.integral_mono_on hab hinterval hconst
            intro t ht
            exact hpoint t ht
      _ = (b - a) * a⁻¹ * ∫ x : Euclidean d, ‖G x‖ := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            dsimp only [M]
            ring
  have htranslate (t : ℝ) :
      (∫ x : Euclidean d, ‖B (t, x)‖) =
        ∫ x : Euclidean d, ‖A (t, x)‖ := by
    let T : Euclidean d → ℝ := fun x => ‖A (t, x)‖
    calc
      (∫ x : Euclidean d, ‖B (t, x)‖) = ∫ x : Euclidean d, T (x - c) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        dsimp only [B, T, A]
      _ = ∫ x : Euclidean d, T x := integral_sub_right_eq_self T c
      _ = ∫ x : Euclidean d, ‖A (t, x)‖ := by rfl
  change (∫ p : ℝ × Euclidean d, ‖B p‖ ∂(ν.prod volume)) ≤ _
  calc
    (∫ p : ℝ × Euclidean d, ‖B p‖ ∂(ν.prod volume)) =
        ∫ t : ℝ, ∫ x : Euclidean d, ‖B (t, x)‖ ∂volume ∂ν :=
          integral_prod _ hB.norm
    _ = ∫ t : ℝ, ∫ x : Euclidean d, ‖A (t, x)‖ ∂volume ∂ν := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          exact htranslate t
    _ = ∫ p : ℝ × Euclidean d, ‖A p‖ ∂(ν.prod volume) :=
      (integral_prod _ hA.norm).symm
    _ ≤ _ := hAinterval

/-- The raw atom/generator integrand is jointly integrable on one compact
positive cell.  No cancellation or support hypothesis is used here. -/
private theorem integrable_uncurry_rawRadiusGeneratorDilation_atom_on_Icc
    {d : Nat} (G : SchwartzMap (Euclidean d) ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (atom : Euclidean d → ℂ) (hatom : Integrable atom volume) :
    Integrable (fun p : (ℝ × Euclidean d) × Euclidean d => atom p.2 *
      ((p.1.1⁻¹ ^ (d + 1) : ℝ) • G (p.1.1⁻¹ • (p.1.2 - p.2))))
      (((volume.restrict (Icc a b)).prod volume).prod volume) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let K : ℝ × Euclidean d → Euclidean d → ℂ := fun p y =>
    (p.1⁻¹ ^ (d + 1) : ℝ) • G (p.1⁻¹ • (p.2 - y))
  let F : (ℝ × Euclidean d) × Euclidean d → ℂ := fun p =>
    atom p.2 * K p.1 p.2
  let C : ℝ := (b - a) * a⁻¹ * ∫ x : Euclidean d, ‖G x‖
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hab) (inv_nonneg.mpr ha.le))
      (integral_nonneg fun _ => norm_nonneg _)
  have hKmeas : AEStronglyMeasurable
      (fun p : (ℝ × Euclidean d) × Euclidean d => K p.1 p.2)
      ((ν.prod volume).prod volume) := by
    exact (by
      fun_prop : Measurable (fun p : (ℝ × Euclidean d) × Euclidean d =>
        K p.1 p.2)).aestronglyMeasurable
  have hatommeas : AEStronglyMeasurable
      (fun p : (ℝ × Euclidean d) × Euclidean d => atom p.2)
      ((ν.prod volume).prod volume) := by
    exact AEStronglyMeasurable.comp_snd
      (μ := ν.prod (volume : Measure (Euclidean d)))
      (ν := (volume : Measure (Euclidean d))) hatom.aestronglyMeasurable
  have hFmeas : AEStronglyMeasurable F ((ν.prod volume).prod volume) := by
    exact hatommeas.mul hKmeas
  have hKint (y : Euclidean d) : Integrable (K · y) (ν.prod volume) := by
    simpa only [K, ν] using
      integrable_uncurry_rawRadiusGeneratorDilation_sub_right_on_Icc
        G (b := b) ha y
  have hKbound (y : Euclidean d) :
      (∫ p : ℝ × Euclidean d, ‖K p y‖ ∂(ν.prod volume)) ≤ C := by
    simpa only [K, C, ν] using
      integral_norm_rawRadiusGeneratorDilation_sub_right_on_Icc_le
        G ha hab y
  have hFint : Integrable F ((ν.prod volume).prod volume) := by
    refine (integrable_prod_iff' hFmeas).2 ?_
    constructor
    · filter_upwards with y
      exact (hKint y).const_mul (atom y)
    · have houtermeas : AEStronglyMeasurable
          (fun y : Euclidean d => ∫ p : ℝ × Euclidean d,
            ‖atom y * K p y‖ ∂(ν.prod volume)) volume := by
        have hswap := hFmeas.prod_swap
        exact hswap.norm.integral_prod_right'
      have hmajor : Integrable (fun y : Euclidean d => ‖atom y‖ * C) volume :=
        hatom.norm.mul_const C
      refine Integrable.mono' hmajor houtermeas ?_
      filter_upwards with y
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc
        (∫ p : ℝ × Euclidean d, ‖atom y * K p y‖ ∂(ν.prod volume)) =
            ∫ p : ℝ × Euclidean d, ‖atom y‖ * ‖K p y‖ ∂(ν.prod volume) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with p
              rw [norm_mul]
        _ = ‖atom y‖ * (∫ p : ℝ × Euclidean d,
            ‖K p y‖ ∂(ν.prod volume)) := by
              rw [MeasureTheory.integral_const_mul]
        _ ≤ ‖atom y‖ * C :=
          mul_le_mul_of_nonneg_left (hKbound y) (norm_nonneg _)
  simpa only [ν, F, K] using hFint

/-- Fubini for the raw atom/generator envelope on one positive cell. -/
theorem integrable_and_integral_lacunaryRelativeBandpassPhysicalCell_rawGenerator
    {d : Nat} (G : SchwartzMap (Euclidean d) ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (atom : Euclidean d → ℂ) (hatom : Integrable atom volume) :
    Integrable (fun x : Euclidean d =>
      ∫ t in a..b, ‖∫ y : Euclidean d, atom y *
        ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖) volume ∧
      (∫ x : Euclidean d, ∫ t in a..b, ‖∫ y : Euclidean d, atom y *
        ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖) =
        ∫ t in a..b, ∫ x : Euclidean d, ‖∫ y : Euclidean d, atom y *
          ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖ := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let K : ℝ × Euclidean d → Euclidean d → ℂ := fun p y =>
    (p.1⁻¹ ^ (d + 1) : ℝ) • G (p.1⁻¹ • (p.2 - y))
  let F : (ℝ × Euclidean d) × Euclidean d → ℂ := fun p =>
    atom p.2 * K p.1 p.2
  have hFint : Integrable F ((ν.prod volume).prod volume) := by
    simpa only [ν, F, K] using
      integrable_uncurry_rawRadiusGeneratorDilation_atom_on_Icc
        G ha hab atom hatom
  let H : ℝ × Euclidean d → ℝ := fun p => ‖∫ y : Euclidean d, F (p, y)‖
  have hHint : Integrable H (ν.prod volume) := by
    simpa only [H] using hFint.integral_prod_left.norm
  let Q : Euclidean d → ℝ := fun x => ∫ t in a..b, H (t, x)
  let Qν : Euclidean d → ℝ := fun x => ∫ t : ℝ, H (t, x) ∂ν
  have hQeq : Q = Qν := by
    funext x
    dsimp only [Q, Qν, ν]
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hQint : Integrable Qν volume := hHint.integral_prod_right
  have hswap :
      (∫ t : ℝ, ∫ x : Euclidean d, H (t, x) ∂volume ∂ν) =
        ∫ x : Euclidean d, ∫ t : ℝ, H (t, x) ∂ν ∂volume := by
    simpa only [Function.uncurry] using integral_integral_swap hHint
  have hleft :
      (∫ x : Euclidean d, Q x) =
        ∫ x : Euclidean d, ∫ t : ℝ, H (t, x) ∂ν ∂volume := by
    rw [hQeq]
  have hright :
      (∫ t in a..b, ∫ x : Euclidean d, H (t, x)) =
        ∫ t : ℝ, ∫ x : Euclidean d, H (t, x) ∂volume ∂ν := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  constructor
  · rw [show (fun x : Euclidean d =>
        ∫ t in a..b, ‖∫ y : Euclidean d, atom y *
          ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖) = Q by
        funext x
        rfl]
    rw [hQeq]
    exact hQint
  · change (∫ x : Euclidean d, Q x) =
      ∫ t in a..b, ∫ x : Euclidean d, H (t, x)
    rw [hleft, hright]
    exact hswap.symm

/-- The literal signed radius FTOC without centering.  It is used only for
the finitely many cells before the shifted stopping scale. -/
theorem norm_lacunaryRelativeBandpassPhysicalTerm_sub_left_le_intervalIntegral_raw_generator
    {d : Nat} (hd : 0 < d) (psi : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (G : SchwartzMap (Euclidean d) ℂ)
    (hG : ∀ z : Euclidean d,
      G z = lacunaryRelativeBandpassPhysicalKernelRadiusGenerator psi j z)
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : r ∈ Icc a b)
    (atom : Euclidean d → ℂ) (hatom : Integrable atom volume)
    (x : Euclidean d) :
    ‖lacunaryRelativeBandpassPhysicalTerm psi j r atom x -
        lacunaryRelativeBandpassPhysicalTerm psi j a atom x‖ ≤
      ∫ t in a..b, ‖∫ y : Euclidean d, atom y *
        ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖ := by
  let H : ℝ → ℂ := fun t => ∫ y : Euclidean d, atom y *
    ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))
  have hFTC :
      lacunaryRelativeBandpassPhysicalTerm psi j r atom x -
          lacunaryRelativeBandpassPhysicalTerm psi j a atom x =
        ∫ t in a..r, H t := by
    simpa only [H] using
      lacunaryRelativeBandpassPhysicalTerm_sub_left_eq_intervalIntegral_generator
        hd psi j G hG ha hr.1 atom hatom x
  have hFint := integrable_uncurry_radiusGeneratorDilation_atom_on_Icc
    G (a := a) (b := b) ha atom hatom x
  have hHint : IntervalIntegrable H volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    change Integrable (fun t : ℝ => ∫ y : Euclidean d, atom y *
      ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y))))
        (volume.restrict (Icc a b))
    exact hFint.integral_prod_left
  calc
    ‖lacunaryRelativeBandpassPhysicalTerm psi j r atom x -
        lacunaryRelativeBandpassPhysicalTerm psi j a atom x‖ =
        ‖∫ t in a..r, H t‖ := by rw [hFTC]
    _ ≤ ∫ t in a..r, ‖H t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hr.1
    _ ≤ ∫ t in a..b, ‖H t‖ := by
      apply intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
      · filter_upwards with t
        exact norm_nonneg _
      · exact hHint.norm
    _ = _ := rfl

/-- Integrating one raw cell envelope costs its relative width times the
`L¹` norm of the generator and of the atom. -/
private theorem intervalIntegral_integral_norm_rawRadiusGeneratorDilation_atom_le
    {d : Nat} (G : SchwartzMap (Euclidean d) ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (atom : Euclidean d → ℂ) (hatom : Integrable atom volume) :
    (∫ t in a..b, ∫ x : Euclidean d, ‖∫ y : Euclidean d, atom y *
      ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖) ≤
      (b - a) * a⁻¹ * (∫ x : Euclidean d, ‖G x‖) *
        ∫ y : Euclidean d, ‖atom y‖ := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let K : ℝ × Euclidean d → Euclidean d → ℂ := fun p y =>
    (p.1⁻¹ ^ (d + 1) : ℝ) • G (p.1⁻¹ • (p.2 - y))
  let F : (ℝ × Euclidean d) × Euclidean d → ℂ := fun p =>
    atom p.2 * K p.1 p.2
  let C : ℝ := (b - a) * a⁻¹ * ∫ x : Euclidean d, ‖G x‖
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hab) (inv_nonneg.mpr ha.le))
      (integral_nonneg fun _ => norm_nonneg _)
  have hFint : Integrable F ((ν.prod volume).prod volume) := by
    simpa only [ν, F, K] using
      integrable_uncurry_rawRadiusGeneratorDilation_atom_on_Icc
        G ha hab atom hatom
  have hDint : Integrable (fun p : ℝ × Euclidean d =>
      ∫ y : Euclidean d, F (p, y)) (ν.prod volume) :=
    hFint.integral_prod_left
  have hRint : Integrable (fun p : ℝ × Euclidean d =>
      ∫ y : Euclidean d, ‖F (p, y)‖) (ν.prod volume) :=
    hFint.norm.integral_prod_left
  have hslices : ∀ᵐ p : ℝ × Euclidean d ∂(ν.prod volume),
      Integrable (fun y : Euclidean d => F (p, y)) volume :=
    (integrable_prod_iff hFint.aestronglyMeasurable).mp hFint |>.1
  have hpoint : ∀ᵐ p : ℝ × Euclidean d ∂(ν.prod volume),
      ‖∫ y : Euclidean d, F (p, y)‖ ≤ ∫ y : Euclidean d, ‖F (p, y)‖ := by
    filter_upwards [hslices] with p hp
    exact norm_integral_le_of_norm_le hp.norm (Filter.Eventually.of_forall fun _ => le_rfl)
  have htriangle :
      (∫ p : ℝ × Euclidean d, ‖∫ y : Euclidean d, F (p, y)‖
        ∂(ν.prod volume)) ≤
        ∫ p : ℝ × Euclidean d,
          (∫ y : Euclidean d, ‖F (p, y)‖) ∂(ν.prod volume) :=
    integral_mono_ae hDint.norm hRint hpoint
  have hKbound (y : Euclidean d) :
      (∫ p : ℝ × Euclidean d, ‖K p y‖ ∂(ν.prod volume)) ≤ C := by
    simpa only [K, C, ν] using
      integral_norm_rawRadiusGeneratorDilation_sub_right_on_Icc_le
        G ha hab y
  have houterint :
      (∫ y : Euclidean d, ∫ p : ℝ × Euclidean d,
        ‖F (p, y)‖ ∂(ν.prod volume)) ≤
        ∫ y : Euclidean d, ‖atom y‖ * C := by
    have hleft : Integrable (fun y : Euclidean d => ∫ p : ℝ × Euclidean d,
        ‖F (p, y)‖ ∂(ν.prod volume)) volume :=
      hFint.norm.integral_prod_right
    have hright : Integrable (fun y : Euclidean d => ‖atom y‖ * C) volume :=
      hatom.norm.mul_const C
    apply integral_mono_ae hleft hright
    filter_upwards with y
    calc
      (∫ p : ℝ × Euclidean d, ‖F (p, y)‖ ∂(ν.prod volume)) =
          ∫ p : ℝ × Euclidean d, ‖atom y‖ * ‖K p y‖ ∂(ν.prod volume) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with p
            dsimp only [F]
            rw [norm_mul]
      _ = ‖atom y‖ * (∫ p : ℝ × Euclidean d,
          ‖K p y‖ ∂(ν.prod volume)) := by
            rw [MeasureTheory.integral_const_mul]
      _ ≤ ‖atom y‖ * C :=
        mul_le_mul_of_nonneg_left (hKbound y) (norm_nonneg _)
  have hFswap :
      (∫ p : ℝ × Euclidean d,
        (∫ y : Euclidean d, ‖F (p, y)‖) ∂(ν.prod volume)) =
        ∫ y : Euclidean d, ∫ p : ℝ × Euclidean d,
          ‖F (p, y)‖ ∂(ν.prod volume) :=
    integral_integral_swap hFint.norm
  have hmain :
      (∫ p : ℝ × Euclidean d, ‖∫ y : Euclidean d, F (p, y)‖
        ∂(ν.prod volume)) ≤ C * ∫ y : Euclidean d, ‖atom y‖ := by
    calc
      (∫ p : ℝ × Euclidean d, ‖∫ y : Euclidean d, F (p, y)‖
        ∂(ν.prod volume)) ≤
          ∫ p : ℝ × Euclidean d,
            (∫ y : Euclidean d, ‖F (p, y)‖) ∂(ν.prod volume) := htriangle
      _ = ∫ y : Euclidean d, ∫ p : ℝ × Euclidean d,
          ‖F (p, y)‖ ∂(ν.prod volume) := hFswap
      _ ≤ ∫ y : Euclidean d, ‖atom y‖ * C := houterint
      _ = C * ∫ y : Euclidean d, ‖atom y‖ := by
        rw [MeasureTheory.integral_mul_const]
        ring
  change (∫ t in a..b, ∫ x : Euclidean d,
      ‖∫ y : Euclidean d, F ((t, x), y)‖) ≤ _
  have hFubini :
      (∫ t in a..b, ∫ x : Euclidean d,
        ‖∫ y : Euclidean d, F ((t, x), y)‖) =
        ∫ p : ℝ × Euclidean d, ‖∫ y : Euclidean d, F (p, y)‖
          ∂(ν.prod volume) := by
    calc
      (∫ t in a..b, ∫ x : Euclidean d,
        ‖∫ y : Euclidean d, F ((t, x), y)‖) =
          ∫ t : ℝ, ∫ x : Euclidean d,
            ‖∫ y : Euclidean d, F ((t, x), y)‖ ∂volume ∂ν := by
              simp only [ν]
              rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
      _ = ∫ p : ℝ × Euclidean d, ‖∫ y : Euclidean d, F (p, y)‖
          ∂(ν.prod volume) :=
        (integral_prod _ hDint.norm).symm
  rw [hFubini]
  calc
    (∫ p : ℝ × Euclidean d, ‖∫ y : Euclidean d, F (p, y)‖
      ∂(ν.prod volume)) ≤ C * ∫ y : Euclidean d, ‖atom y‖ := hmain
    _ = _ := by
      dsimp only [C]

/-- Summing raw positive-cell envelopes only costs their total relative
width. -/
theorem lacunaryRelativeBandpassPhysicalCellRaw_atom_tail_le
    {d : Nat} (G : SchwartzMap (Euclidean d) ℂ)
    {ι : Type*} (I : Finset ι) (a b : ι → ℝ)
    (ha : ∀ q ∈ I, 0 < a q) (hab : ∀ q ∈ I, a q ≤ b q)
    (atom : Euclidean d → ℂ) (hatom : Integrable atom volume) :
    (∑ q ∈ I, ∫ t in a q..b q, ∫ x : Euclidean d,
      ‖∫ y : Euclidean d, atom y *
        ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖) ≤
      (∑ q ∈ I, (b q - a q) * (a q)⁻¹) *
        (∫ x : Euclidean d, ‖G x‖) *
          ∫ y : Euclidean d, ‖atom y‖ := by
  let A : ℝ := ∫ x : Euclidean d, ‖G x‖
  let B : ℝ := ∫ y : Euclidean d, ‖atom y‖
  have hsingle (q : ι) (hq : q ∈ I) :
      (∫ t in a q..b q, ∫ x : Euclidean d, ‖∫ y : Euclidean d, atom y *
        ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖) ≤
        (b q - a q) * (a q)⁻¹ * A * B := by
    simpa only [A, B] using
      intervalIntegral_integral_norm_rawRadiusGeneratorDilation_atom_le
        G (ha q hq) (hab q hq) atom hatom
  calc
    (∑ q ∈ I, ∫ t in a q..b q, ∫ x : Euclidean d,
      ‖∫ y : Euclidean d, atom y *
        ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖) ≤
        ∑ q ∈ I, (b q - a q) * (a q)⁻¹ * A * B :=
      Finset.sum_le_sum fun q hq => hsingle q hq
    _ = ∑ q ∈ I, (A * B) * ((b q - a q) * (a q)⁻¹) := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = (A * B) * (∑ q ∈ I, (b q - a q) * (a q)⁻¹) := by
      rw [Finset.mul_sum]
    _ = (∑ q ∈ I, (b q - a q) * (a q)⁻¹) * A * B := by
      ring
    _ = _ := by rfl

/-- The finitely many raw cells have an integrable pointwise majorant.  This
is deliberately an existential package, mirroring the existing past and
future C--Z atom packages. -/
theorem exists_integrable_lacunaryRelativeBandpassPhysicalCellOscillation_raw_atom_majorant
    {d : Nat} (hd : 0 < d) (psi : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (G : SchwartzMap (Euclidean d) ℂ)
    (hG : ∀ z : Euclidean d,
      G z = lacunaryRelativeBandpassPhysicalKernelRadiusGenerator psi j z)
    {ι : Type*} (I : Finset ι) (a b : ι → ℝ)
    (ha : ∀ q ∈ I, 0 < a q) (hab : ∀ q ∈ I, a q ≤ b q)
    (atom : Euclidean d → ℂ) (hatom : Integrable atom volume) :
    ∃ H : Euclidean d → ℝ, Integrable H volume ∧
      (∀ x, 0 ≤ H x) ∧
      (∀ x, lacunaryRelativeBandpassPhysicalCellOscillation psi j I a b atom x ≤
        ENNReal.ofReal (H x)) ∧
      (∫ x : Euclidean d, H x) ≤
        (∑ q ∈ I, (b q - a q) * (a q)⁻¹) *
          (∫ x : Euclidean d, ‖G x‖) *
            ∫ y : Euclidean d, ‖atom y‖ := by
  let Hq : ι → Euclidean d → ℝ := fun q x =>
    ∫ t in a q..b q, ‖∫ y : Euclidean d, atom y *
      ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖
  let H : Euclidean d → ℝ := fun x => ∑ q ∈ I, Hq q x
  have hHqint (q : ι) (hq : q ∈ I) : Integrable (Hq q) volume := by
    dsimp only [Hq]
    exact (integrable_and_integral_lacunaryRelativeBandpassPhysicalCell_rawGenerator
      G (ha q hq) (hab q hq) atom hatom).1
  have hHqeq (q : ι) (hq : q ∈ I) :
      (∫ x : Euclidean d, Hq q x) =
        ∫ t in a q..b q, ∫ x : Euclidean d, ‖∫ y : Euclidean d, atom y *
          ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖ := by
    dsimp only [Hq]
    exact (integrable_and_integral_lacunaryRelativeBandpassPhysicalCell_rawGenerator
      G (ha q hq) (hab q hq) atom hatom).2
  have hHqnon (q : ι) (hq : q ∈ I) (x : Euclidean d) : 0 ≤ Hq q x := by
    dsimp only [Hq]
    exact intervalIntegral.integral_nonneg (hab q hq) fun _ _ => norm_nonneg _
  have hHint : Integrable H volume := by
    dsimp only [H]
    exact integrable_finsetSum I fun q hq => hHqint q hq
  have hHnon (x : Euclidean d) : 0 ≤ H x := by
    dsimp only [H]
    exact Finset.sum_nonneg fun q hq => hHqnon q hq x
  have hpoint (q : ι) (hq : q ∈ I) (x : Euclidean d)
      (t : Icc (a q) (b q)) :
      ‖lacunaryRelativeBandpassPhysicalTerm psi j t.1 atom x -
          lacunaryRelativeBandpassPhysicalTerm psi j (a q) atom x‖ ≤ Hq q x := by
    simpa only [Hq] using
      norm_lacunaryRelativeBandpassPhysicalTerm_sub_left_le_intervalIntegral_raw_generator
        hd psi j G hG (ha q hq) (hab q hq) t.2 atom hatom x
  have hmajor (x : Euclidean d) :
      lacunaryRelativeBandpassPhysicalCellOscillation psi j I a b atom x ≤
        ENNReal.ofReal (H x) := by
    unfold lacunaryRelativeBandpassPhysicalCellOscillation
    calc
      (∑ q ∈ I, ⨆ t : Icc (a q) (b q), ENNReal.ofReal
        ‖lacunaryRelativeBandpassPhysicalTerm psi j t.1 atom x -
          lacunaryRelativeBandpassPhysicalTerm psi j (a q) atom x‖) ≤
          ∑ q ∈ I, ENNReal.ofReal (Hq q x) := by
        apply Finset.sum_le_sum
        intro q hq
        apply iSup_le
        intro t
        exact ENNReal.ofReal_le_ofReal (hpoint q hq x t)
      _ = ENNReal.ofReal (H x) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun q hq => hHqnon q hq x]
  refine ⟨H, hHint, hHnon, hmajor, ?_⟩
  calc
    (∫ x : Euclidean d, H x) = ∑ q ∈ I, ∫ x : Euclidean d, Hq q x := by
      dsimp only [H]
      rw [integral_finsetSum I fun q hq => hHqint q hq]
    _ = ∑ q ∈ I, ∫ t in a q..b q, ∫ x : Euclidean d,
        ‖∫ y : Euclidean d, atom y *
          ((t⁻¹ ^ (d + 1) : ℝ) • G (t⁻¹ • (x - y)))‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hHqeq q hq
    _ ≤ (∑ q ∈ I, (b q - a q) * (a q)⁻¹) *
        (∫ x : Euclidean d, ‖G x‖) *
          ∫ y : Euclidean d, ‖atom y‖ :=
      lacunaryRelativeBandpassPhysicalCellRaw_atom_tail_le
        G I a b ha hab atom hatom

/-- The scale-free coefficient from the past, raw middle, and shifted
future pieces of one literal physical-cell C--Z atom. -/
def lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant
    {d : Nat} (N : Nat) (psi : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (δ : NNReal) (G : SchwartzMap (Euclidean d) ℂ) : ℝ :=
  (2 * (((2 : ℝ) ^ j)⁻¹ ^ 2 *
      SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi)) *
      ((N : ℝ) * (16 / 3 : ℝ)) * surfaceMass d *
        (surfaceMass d * (3 : ℝ) ^ d / (2 * (d : ℝ) ^ 2))) +
    ((N : ℝ) * (j : ℝ) * (8 * Real.log 2 * (δ : ℝ)) *
      ∫ x : Euclidean d, ‖G x‖) +
    ((d : ℝ) * ((N : ℝ) * (2 * (8 * Real.log 2 * (δ : ℝ))) *
      ((2 : ℝ) ^ j)⁻¹) *
        ∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖)

theorem lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant_nonneg
    {d : Nat} (N : Nat) (psi : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (δ : NNReal) (G : SchwartzMap (Euclidean d) ℂ) :
    0 ≤ lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G := by
  have hsemi : 0 ≤ SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) := by
    calc
      0 ≤ ‖(0 : Euclidean d)‖ ^ (d + 2) * ‖(𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) 0‖ :=
        by positivity
      _ ≤ SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) :=
        SchwartzMap.norm_pow_mul_le_seminorm ℂ
          (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) (d + 2) 0
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hδ : 0 ≤ (δ : ℝ) := δ.2
  have hG : 0 ≤ ∫ x : Euclidean d, ‖G x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hderiv : 0 ≤ ∫ x : Euclidean d,
      ‖fderiv ℝ (G : Euclidean d → ℂ) x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hA : 0 ≤ ((2 : ℝ) ^ j)⁻¹ ^ 2 *
      SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) :=
    mul_nonneg (sq_nonneg _) hsemi
  have hB : 0 ≤ (N : ℝ) * (16 / 3 : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hR : 0 ≤ surfaceMass d * (3 : ℝ) ^ d /
      (2 * (d : ℝ) ^ 2) :=
    div_nonneg
      (mul_nonneg measureReal_nonneg (pow_nonneg (by norm_num) _))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have h8log : 0 ≤ 8 * Real.log 2 :=
    mul_nonneg (by norm_num) hlog
  have hscale : 0 ≤ 2 * (8 * Real.log 2 * (δ : ℝ)) :=
    mul_nonneg (by norm_num) (mul_nonneg h8log hδ)
  have hfirst : 0 ≤
      2 * (((2 : ℝ) ^ j)⁻¹ ^ 2 *
        SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi)) *
        ((N : ℝ) * (16 / 3 : ℝ)) * surfaceMass d *
          (surfaceMass d * (3 : ℝ) ^ d / (2 * (d : ℝ) ^ 2)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hA)
          hB)
        measureReal_nonneg)
      hR
  have hmid : 0 ≤ (N : ℝ) * (j : ℝ) * (8 * Real.log 2 * (δ : ℝ)) *
      ∫ x : Euclidean d, ‖G x‖ := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg h8log hδ)) hG
  have hfuture : 0 ≤ (d : ℝ) *
      ((N : ℝ) * (2 * (8 * Real.log 2 * (δ : ℝ))) * ((2 : ℝ) ^ j)⁻¹) *
        ∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖ := by
    exact mul_nonneg
      (mul_nonneg
        (Nat.cast_nonneg _)
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) hscale)
          (inv_nonneg.mpr (pow_nonneg (by norm_num) _))))
      hderiv
  unfold lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant
  exact add_nonneg (add_nonneg hfirst hmid) hfuture

/-- A scale-independent linear majorant for the shifted cell tail.  The last
term is the additional cost of differentiating the relative-radius generator
in the future-cell cancellation estimate. -/
def lacunaryRelativeBandpassPhysicalCellShiftedCZTailLinearMajorant
    {d : Nat} (psi : SchwartzMap (Euclidean d) ℂ) : ℝ :=
  (2 * SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) * (16 / 3 : ℝ) *
      surfaceMass d) *
    (surfaceMass d * (3 : ℝ) ^ d / (2 * (d : ℝ) ^ 2)) +
  surfaceMass d *
    ((d : ℝ) * (∫ x : Euclidean d,
      ‖(𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) x‖) +
      (∫ x : Euclidean d,
        ‖x‖ * ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) :
          Euclidean d → ℂ) x‖) +
      ∫ x : Euclidean d,
        ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) :
          Euclidean d → ℂ) x‖) +
  2 * (d : ℝ) *
    lacunaryRelativeBandpassPhysicalKernelRadiusGeneratorFDerivConstant psi

theorem lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant_le_linear
    {d N : Nat} (hd : 0 < d) (psi : SchwartzMap (Euclidean d) ℂ)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d → ℂ))
    (j : Nat) (δ : NNReal) (G : SchwartzMap (Euclidean d) ℂ)
    (hG : ∀ x : Euclidean d,
      G x = lacunaryRelativeBandpassPhysicalKernelRadiusGenerator psi j x)
    (hsmall : 8 * Real.log 2 * (δ : ℝ) ≤ ((2 : ℝ) ^ j)⁻¹) :
    lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G ≤
      (N : ℝ) * ((j : ℝ) + 1) *
        lacunaryRelativeBandpassPhysicalCellShiftedCZTailLinearMajorant psi := by
  letI : SeminormedAddGroup (Euclidean d →L[ℝ] Euclidean d →L[ℝ] ℂ) :=
    { __ := (inferInstance : SeminormedAddCommGroup
      (Euclidean d →L[ℝ] Euclidean d →L[ℝ] ℂ)) }
  let s : ℝ := (2 : ℝ) ^ j
  let e : ℝ := 8 * Real.log 2 * (δ : ℝ)
  let P : ℝ :=
    (2 * SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) * (16 / 3 : ℝ) *
      surfaceMass d) *
      (surfaceMass d * (3 : ℝ) ^ d / (2 * (d : ℝ) ^ 2))
  let A : ℝ := surfaceMass d *
    ((d : ℝ) * (∫ x : Euclidean d,
      ‖(𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) x‖) +
      (∫ x : Euclidean d,
        ‖x‖ * ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) :
          Euclidean d → ℂ) x‖) +
      ∫ x : Euclidean d,
        ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) :
          Euclidean d → ℂ) x‖)
  let D : ℝ :=
    lacunaryRelativeBandpassPhysicalKernelRadiusGeneratorFDerivConstant psi
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsone : 1 ≤ s := by
    dsimp only [s]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have he : 0 ≤ e := by
    dsimp only [e]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) δ.2
  have hsmall' : e ≤ s⁻¹ := by simpa only [e, s] using hsmall
  have hes : e * s ≤ 1 := by
    calc
      e * s ≤ s⁻¹ * s := mul_le_mul_of_nonneg_right hsmall' hs.le
      _ = 1 := inv_mul_cancel₀ hs.ne'
  have hsemi : 0 ≤ SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) := by
    calc
      0 ≤ ‖(0 : Euclidean d)‖ ^ (d + 2) * ‖(𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) 0‖ :=
        by positivity
      _ ≤ SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) :=
        SchwartzMap.norm_pow_mul_le_seminorm ℂ
          (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) (d + 2) 0
  have hP : 0 ≤ P := by
    dsimp only [P]
    apply mul_nonneg
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hsemi)
          (by norm_num))
        measureReal_nonneg
    · exact div_nonneg
        (mul_nonneg measureReal_nonneg (pow_nonneg (by norm_num) _))
        (mul_nonneg (by norm_num) (sq_nonneg _))
  have hA : 0 ≤ A := by
    dsimp only [A]
    apply mul_nonneg measureReal_nonneg
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (Nat.cast_nonneg d)
          (integral_nonneg fun _ => norm_nonneg _)
      · exact integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · exact integral_nonneg fun _ => norm_nonneg _
  have hD : 0 ≤ D := by
    dsimp only [D, lacunaryRelativeBandpassPhysicalKernelRadiusGeneratorFDerivConstant]
    apply mul_nonneg measureReal_nonneg
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg
          (add_nonneg (Nat.cast_nonneg d) (by norm_num))
          (integral_nonneg fun _ => norm_nonneg _)
      · exact integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · exact integral_nonneg fun _ => norm_nonneg _
  have hGint : (∫ x : Euclidean d, ‖G x‖) ≤ s * A := by
    have hGfun : (G : Euclidean d → ℂ) =
        lacunaryRelativeBandpassPhysicalKernelRadiusGenerator psi j := by
      funext x
      exact hG x
    rw [hGfun]
    simpa only [s, A, mul_assoc] using
      integral_norm_lacunaryRelativeBandpassPhysicalKernelRadiusGenerator_le hd psi j
  have hDGint :
      (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖) ≤ s ^ 2 * D := by
    simpa only [s, D] using
      integral_norm_fderiv_lacunaryRelativeBandpassPhysicalKernelRadiusGenerator_le
        hd psi hpsiCompact j G hG
  have hinv : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsone
  have hinvnonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hinvsq : s⁻¹ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (s⁻¹ - 1)]
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hfirst : s⁻¹ ^ 2 * P ≤ P := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hinvsq hP
  have hmiddle : (j : ℝ) * e * (∫ x : Euclidean d, ‖G x‖) ≤ (j : ℝ) * A := by
    calc
      (j : ℝ) * e * (∫ x : Euclidean d, ‖G x‖) ≤
          (j : ℝ) * e * (s * A) :=
        mul_le_mul_of_nonneg_left hGint (mul_nonneg hj he)
      _ = ((j : ℝ) * A) * (e * s) := by ring
      _ ≤ ((j : ℝ) * A) * 1 :=
        mul_le_mul_of_nonneg_left hes (mul_nonneg hj hA)
      _ = (j : ℝ) * A := by ring
  have hfuture : 2 * (d : ℝ) * e * s⁻¹ *
      (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖) ≤
        2 * (d : ℝ) * D := by
    have hcoeff : 0 ≤ 2 * (d : ℝ) * e * s⁻¹ := by positivity
    calc
      2 * (d : ℝ) * e * s⁻¹ *
          (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖) ≤
          2 * (d : ℝ) * e * s⁻¹ * (s ^ 2 * D) :=
        mul_le_mul_of_nonneg_left hDGint hcoeff
      _ = (2 * (d : ℝ) * D) * (e * s) := by
        field_simp [hs.ne']
      _ ≤ (2 * (d : ℝ) * D) * 1 :=
        mul_le_mul_of_nonneg_left hes
          (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hD)
      _ = 2 * (d : ℝ) * D := by ring
  have htwoD : 0 ≤ 2 * (d : ℝ) * D :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hD
  have hinside :
      s⁻¹ ^ 2 * P + (j : ℝ) * e * (∫ x : Euclidean d, ‖G x‖) +
        2 * (d : ℝ) * e * s⁻¹ *
          (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖) ≤
        ((j : ℝ) + 1) * (P + A + 2 * (d : ℝ) * D) := by
    calc
      s⁻¹ ^ 2 * P + (j : ℝ) * e * (∫ x : Euclidean d, ‖G x‖) +
          2 * (d : ℝ) * e * s⁻¹ *
            (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖) ≤
          P + (j : ℝ) * A + 2 * (d : ℝ) * D :=
        add_le_add (add_le_add hfirst hmiddle) hfuture
      _ ≤ ((j : ℝ) + 1) * (P + A + 2 * (d : ℝ) * D) := by
        nlinarith [mul_nonneg hj hP, mul_nonneg hj hA, mul_nonneg hj htwoD]
  have hform : lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G =
      (N : ℝ) *
        (s⁻¹ ^ 2 * P + (j : ℝ) * e * (∫ x : Euclidean d, ‖G x‖) +
          2 * (d : ℝ) * e * s⁻¹ *
            (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖)) := by
    dsimp only [s, e, P]
    unfold lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant
    ring
  have hmajor : lacunaryRelativeBandpassPhysicalCellShiftedCZTailLinearMajorant psi =
      P + A + 2 * (d : ℝ) * D := by
    dsimp only [lacunaryRelativeBandpassPhysicalCellShiftedCZTailLinearMajorant, P, A, D]
  rw [hform, hmajor]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg N)

theorem lacunaryRelativeBandpassPhysicalCellShiftedCZTailLinearMajorant_nonneg
    {d : Nat} (psi : SchwartzMap (Euclidean d) ℂ) :
    0 ≤ lacunaryRelativeBandpassPhysicalCellShiftedCZTailLinearMajorant psi := by
  letI : SeminormedAddGroup (Euclidean d →L[ℝ] Euclidean d →L[ℝ] ℂ) :=
    { __ := (inferInstance : SeminormedAddCommGroup
      (Euclidean d →L[ℝ] Euclidean d →L[ℝ] ℂ)) }
  have hsemi : 0 ≤ SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) := by
    calc
      0 ≤ ‖(0 : Euclidean d)‖ ^ (d + 2) * ‖(𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) 0‖ :=
        by positivity
      _ ≤ SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) :=
        SchwartzMap.norm_pow_mul_le_seminorm ℂ
          (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) (d + 2) 0
  have hP : 0 ≤
      (2 * SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi) * (16 / 3 : ℝ) *
        surfaceMass d) *
      (surfaceMass d * (3 : ℝ) ^ d / (2 * (d : ℝ) ^ 2)) := by
    apply mul_nonneg
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hsemi)
          (by norm_num))
        measureReal_nonneg
    · exact div_nonneg
        (mul_nonneg measureReal_nonneg (pow_nonneg (by norm_num) _))
        (mul_nonneg (by norm_num) (sq_nonneg _))
  have hA : 0 ≤ surfaceMass d *
      ((d : ℝ) * (∫ x : Euclidean d,
        ‖(𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) x‖) +
        (∫ x : Euclidean d,
          ‖x‖ * ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) :
            Euclidean d → ℂ) x‖) +
        ∫ x : Euclidean d,
          ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) :
            Euclidean d → ℂ) x‖) := by
    apply mul_nonneg measureReal_nonneg
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (Nat.cast_nonneg d)
          (integral_nonneg fun _ => norm_nonneg _)
      · exact integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · exact integral_nonneg fun _ => norm_nonneg _
  have hD : 0 ≤ 2 * (d : ℝ) *
      lacunaryRelativeBandpassPhysicalKernelRadiusGeneratorFDerivConstant psi := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) (Nat.cast_nonneg d)
    · unfold lacunaryRelativeBandpassPhysicalKernelRadiusGeneratorFDerivConstant
      apply mul_nonneg measureReal_nonneg
      apply add_nonneg
      · apply add_nonneg
        · exact mul_nonneg
            (add_nonneg (Nat.cast_nonneg d) (by norm_num))
            (integral_nonneg fun _ => norm_nonneg _)
        · exact integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact integral_nonneg fun _ => norm_nonneg _
  unfold lacunaryRelativeBandpassPhysicalCellShiftedCZTailLinearMajorant
  exact add_nonneg (add_nonneg hP hA) hD

/-- The cell weak coefficient after the shifted split, with every dependence
on the entropy selector and frequency index pulled into `N * (j + 1)`. -/
def lacunaryRelativeBandpassPhysicalCellShiftedWeakOneLinearMajorant
    {d : Nat} (psi : SchwartzMap (Euclidean d) ℂ) (C : ℝ) : ENNReal :=
  2 * ENNReal.ofReal
      ((volume (Metric.ball (0 : Euclidean d) 1)).toReal *
        (3 : ℝ) ^ d * (d : ℝ) ^ d) +
    (32 * ENNReal.ofReal (3 * (2 : ℝ) ^ d) * (ENNReal.ofReal C) ^ (2 : ℕ)) +
    16 * ENNReal.ofReal
      (lacunaryRelativeBandpassPhysicalCellShiftedCZTailLinearMajorant psi)

/-- The exceptional, good, and shifted bad-tail contributions to the
literal physical-cell weak-one estimate. -/
def lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant {d N : Nat}
    (psi : SchwartzMap (Euclidean d) ℂ) (j : Nat) (δ : NNReal)
    (G : SchwartzMap (Euclidean d) ℂ) (C : ℝ) : ENNReal :=
  2 * ENNReal.ofReal
      ((volume (Metric.ball (0 : Euclidean d) 1)).toReal *
        (3 : ℝ) ^ d * (d : ℝ) ^ d) +
    (32 * ENNReal.ofReal (3 * (2 : ℝ) ^ d) * (ENNReal.ofReal C) ^ (2 : ℕ)) +
      16 * ENNReal.ofReal
        (lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G)

theorem lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant_le_linear
    {d N : Nat} (hN : 1 ≤ N) (hd : 0 < d)
    (psi : SchwartzMap (Euclidean d) ℂ)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d → ℂ))
    (j : Nat) (δ : NNReal) (G : SchwartzMap (Euclidean d) ℂ)
    (hG : ∀ x : Euclidean d,
      G x = lacunaryRelativeBandpassPhysicalKernelRadiusGenerator psi j x)
    (C : ℝ) (hsmall : 8 * Real.log 2 * (δ : ℝ) ≤ ((2 : ℝ) ^ j)⁻¹) :
    lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant (N := N) psi j δ G C ≤
      (N : ENNReal) * ENNReal.ofReal ((j : ℝ) + 1) *
        lacunaryRelativeBandpassPhysicalCellShiftedWeakOneLinearMajorant psi C := by
  let T : ℝ := lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G
  let L : ℝ := lacunaryRelativeBandpassPhysicalCellShiftedCZTailLinearMajorant psi
  let B : ENNReal :=
    2 * ENNReal.ofReal
        ((volume (Metric.ball (0 : Euclidean d) 1)).toReal *
          (3 : ℝ) ^ d * (d : ℝ) ^ d) +
      (32 * ENNReal.ofReal (3 * (2 : ℝ) ^ d) * (ENNReal.ofReal C) ^ (2 : ℕ))
  let q : ENNReal := (N : ENNReal) * ENNReal.ofReal ((j : ℝ) + 1)
  have htail : T ≤ (N : ℝ) * ((j : ℝ) + 1) * L := by
    simpa only [T, L] using
      lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant_le_linear
        hd psi hpsiCompact j δ G hG hsmall
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact lacunaryRelativeBandpassPhysicalCellShiftedCZTailLinearMajorant_nonneg psi
  have htailENN : ENNReal.ofReal T ≤ q * ENNReal.ofReal L := by
    calc
      ENNReal.ofReal T ≤ ENNReal.ofReal ((N : ℝ) * ((j : ℝ) + 1) * L) :=
        ENNReal.ofReal_le_ofReal htail
      _ = q * ENNReal.ofReal L := by
        rw [ENNReal.ofReal_mul
          (mul_nonneg (Nat.cast_nonneg N) (by positivity : 0 ≤ (j : ℝ) + 1)),
          ENNReal.ofReal_mul (Nat.cast_nonneg N)]
        simp only [ENNReal.ofReal_natCast]
        ring
  have hNENN : (1 : ENNReal) ≤ (N : ENNReal) := by exact_mod_cast hN
  have hjENN : (1 : ENNReal) ≤ ENNReal.ofReal ((j : ℝ) + 1) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact one_le_mul_of_one_le_of_one_le hNENN hjENN
  have hbase : B ≤ q * B := by
    simpa only [one_mul, mul_comm] using mul_le_mul_left hq B
  have hweakform :
      lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant (N := N) psi j δ G C =
        B + 16 * ENNReal.ofReal T := by
    rfl
  have hmajorform :
      lacunaryRelativeBandpassPhysicalCellShiftedWeakOneLinearMajorant psi C =
        B + 16 * ENNReal.ofReal L := by
    rfl
  rw [hweakform, hmajorform]
  calc
    B + 16 * ENNReal.ofReal T ≤ q * B + 16 * (q * ENNReal.ofReal L) :=
      add_le_add hbase (by
        simpa only [mul_comm] using mul_le_mul_left htailENN 16)
    _ = q * (B + 16 * ENNReal.ofReal L) := by ring
    _ = (N : ENNReal) * ENNReal.ofReal ((j : ℝ) + 1) *
        (B + 16 * ENNReal.ofReal L) := by
      rfl

private theorem lacunaryRelativeBandpassPhysicalCellShiftedCZ_past_rhs_eq
    {d N : Nat} (hd : 0 < d) (psi : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (q : LacunaryCZDyadicCubeIndex d) (L : ℝ) :
    (2 * (((2 : ℝ) ^ j)⁻¹ ^ 2 *
        SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi)) *
        ((N : ℝ) * (16 / 3 : ℝ) * ((2 : ℝ) ^ q.scale) ^ 2) *
          surfaceMass d * L) *
        (surfaceMass d * (3 : ℝ) ^ d /
          (2 * (lacunaryCZDyadicCubeRadius q) ^ 2)) =
      (2 * (((2 : ℝ) ^ j)⁻¹ ^ 2 *
          SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi)) *
          ((N : ℝ) * (16 / 3 : ℝ)) * surfaceMass d *
            (surfaceMass d * (3 : ℝ) ^ d / (2 * (d : ℝ) ^ 2))) * L := by
  unfold lacunaryCZDyadicCubeRadius
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hq0 : (2 : ℝ) ^ q.scale ≠ 0 := zpow_ne_zero _ (by norm_num)
  field_simp

private theorem lacunaryRelativeBandpassPhysicalCellShiftedCZ_future_rhs_eq
    {d N : Nat} (hd : 0 < d) (δ : NNReal)
    (G : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (q : LacunaryCZDyadicCubeIndex d) (L : ℝ) :
    lacunaryCZDyadicCubeRadius q *
        ((N : ℝ) * (2 * (8 * Real.log 2 * (δ : ℝ))) *
          ((2 : ℝ) ^ (q.scale + (j : ℤ)))⁻¹) *
        (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖) * L =
      ((d : ℝ) * ((N : ℝ) * (2 * (8 * Real.log 2 * (δ : ℝ))) *
        ((2 : ℝ) ^ j)⁻¹) *
          ∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖) * L := by
  unfold lacunaryCZDyadicCubeRadius
  have hq0 : (2 : ℝ) ^ q.scale ≠ 0 := zpow_ne_zero _ (by norm_num)
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) q.scale (j : ℤ)]
  rw [zpow_natCast, mul_inv_rev]
  field_simp [hq0]

/-- One dyadic C--Z atom has an exterior majorant after the physical-cell
split is shifted upward by the relative frequency index. -/
theorem exists_integrable_lacunaryRelativeBandpassPhysicalCellShiftedCZ_atom_majorant
    {d N : Nat} (hd : 3 ≤ d) (K : Finset ℤ) (δ : NNReal)
    (hδ : Real.log 2 * (δ : ℝ) ≤ 1)
    (r : Fin N → ℤ → PositiveRadius)
    (hr : ∀ i, IsDyadicLacunaryRadiusSelector (r i))
    (psi : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (G : SchwartzMap (Euclidean d) ℂ)
    (hG : ∀ z : Euclidean d,
      G z = lacunaryRelativeBandpassPhysicalKernelRadiusGenerator psi j z)
    (q : LacunaryCZDyadicCubeIndex d) (atom : Euclidean d → ℂ)
    (hatom : Integrable atom volume)
    (hzero : (∫ y : Euclidean d, atom y) = 0)
    (hatom_supp : ∀ y, atom y ≠ 0 →
      ‖y - lacunaryCZDyadicCubeCenter q‖ ≤ lacunaryCZDyadicCubeRadius q) :
    ∃ H : Euclidean d → ℝ, Integrable H volume ∧
      (∀ x, 0 ≤ H x) ∧
      (∀ x, x ∉ Metric.closedBall (lacunaryCZDyadicCubeCenter q)
          (3 * lacunaryCZDyadicCubeRadius q) →
        lacunaryRelativeBandpassPhysicalCellOscillation psi j
          (K.product Finset.univ) (dyadicPhysicalEntropyCellLeft δ r)
          (dyadicPhysicalEntropyCellRight δ r) atom x ≤ ENNReal.ofReal (H x)) ∧
      (∫ x : Euclidean d, H x) ≤
        lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G *
          (∫ y : Euclidean d, ‖atom y‖) := by
  classical
  have hdpos : 0 < d := by omega
  letI : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
  have hdtwoNat : 2 ≤ d := by omega
  have hdtwo : (2 : ℝ) ≤ d := by exact_mod_cast hdtwoNat
  let Iminus : Finset (ℤ × Fin N) :=
    (K.product Finset.univ).filter fun z => z.1 ≤ q.scale
  let Imid : Finset (ℤ × Fin N) :=
    lacunaryCZDyadicCubeShiftedCellMiddleIndices K j q
  let Iplus : Finset (ℤ × Fin N) :=
    lacunaryCZDyadicCubeShiftedCellFutureIndices K j q
  have ha_minus : ∀ z ∈ Iminus, 0 < dyadicPhysicalEntropyCellLeft δ r z := by
    intro z hz
    exact dyadicPhysicalEntropyCellLeft_pos δ r hr z
  have hab_minus : ∀ z ∈ Iminus,
      dyadicPhysicalEntropyCellLeft δ r z ≤ dyadicPhysicalEntropyCellRight δ r z := by
    intro z hz
    exact dyadicPhysicalEntropyCellLeft_le_right δ r hr z
  have ha_mid : ∀ z ∈ Imid, 0 < dyadicPhysicalEntropyCellLeft δ r z := by
    intro z hz
    exact dyadicPhysicalEntropyCellLeft_pos δ r hr z
  have hab_mid : ∀ z ∈ Imid,
      dyadicPhysicalEntropyCellLeft δ r z ≤ dyadicPhysicalEntropyCellRight δ r z := by
    intro z hz
    exact dyadicPhysicalEntropyCellLeft_le_right δ r hr z
  have ha_plus : ∀ z ∈ Iplus, 0 < dyadicPhysicalEntropyCellLeft δ r z := by
    intro z hz
    exact dyadicPhysicalEntropyCellLeft_pos δ r hr z
  have hab_plus : ∀ z ∈ Iplus,
      dyadicPhysicalEntropyCellLeft δ r z ≤ dyadicPhysicalEntropyCellRight δ r z := by
    intro z hz
    exact dyadicPhysicalEntropyCellLeft_le_right δ r hr z
  have hsmall : ∀ z ∈ Iminus,
      dyadicPhysicalEntropyCellRight δ r z ≤ lacunaryCZDyadicCubeRadius q := by
    intro z hz
    have hzq : z.1 ≤ q.scale := by
      exact (Finset.mem_filter.mp (show z ∈
        (K.product Finset.univ).filter fun w => w.1 ≤ q.scale by
          simpa only [Iminus] using hz)).2
    have hpow : (2 : ℝ) ^ z.1 ≤ (2 : ℝ) ^ q.scale := by
      apply zpow_le_zpow_right₀ (by norm_num)
      exact hzq
    calc
      dyadicPhysicalEntropyCellRight δ r z ≤ 2 * (2 : ℝ) ^ z.1 :=
        (dyadicPhysicalEntropyCell_endpoints_mem_block δ r hr z).2.2
      _ ≤ 2 * (2 : ℝ) ^ q.scale :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ (d : ℝ) * (2 : ℝ) ^ q.scale :=
        mul_le_mul_of_nonneg_right hdtwo (zpow_nonneg (by norm_num) _)
      _ = lacunaryCZDyadicCubeRadius q := by rfl
  have hSq : ∑ z ∈ Iminus, (dyadicPhysicalEntropyCellRight δ r z) ^ 2 ≤
      (N : ℝ) * (16 / 3 : ℝ) * ((2 : ℝ) ^ q.scale) ^ 2 := by
    simpa only [Iminus] using
      sum_dyadicPhysicalEntropyCellRight_sq_past_le K δ r hr q
  have hmiddle : ∑ z ∈ Imid,
      (dyadicPhysicalEntropyCellRight δ r z - dyadicPhysicalEntropyCellLeft δ r z) *
          (dyadicPhysicalEntropyCellLeft δ r z)⁻¹ ≤
        (N : ℝ) * (j : ℝ) * (8 * Real.log 2 * (δ : ℝ)) := by
    simpa only [Imid] using
      sum_dyadicPhysicalEntropyCell_length_mul_left_inv_shiftedMiddle_le
        K δ r hr j q hδ
  have hfuture : ∑ z ∈ Iplus,
      (dyadicPhysicalEntropyCellRight δ r z - dyadicPhysicalEntropyCellLeft δ r z) *
          (dyadicPhysicalEntropyCellLeft δ r z)⁻¹ ^ 2 ≤
        (N : ℝ) * (2 * (8 * Real.log 2 * (δ : ℝ))) *
          ((2 : ℝ) ^ (q.scale + (j : ℤ)))⁻¹ := by
    simpa only [Iplus] using
      sum_dyadicPhysicalEntropyCell_length_mul_left_inv_sq_shiftedFuture_le
        K δ r hr j q hδ
  rcases exists_integrable_lacunaryRelativeBandpassPhysicalCellOscillation_past_atom_majorant
    hdpos psi j Iminus (dyadicPhysicalEntropyCellLeft δ r)
      (dyadicPhysicalEntropyCellRight δ r) ha_minus hab_minus
      (lacunaryCZDyadicCubeRadius_pos q) hsmall hSq
      (lacunaryCZDyadicCubeCenter q) atom hatom hatom_supp with
    ⟨Hp, hPint, hPnon, hPpoint, hPbound⟩
  rcases exists_integrable_lacunaryRelativeBandpassPhysicalCellOscillation_raw_atom_majorant
    hdpos psi j G hG Imid (dyadicPhysicalEntropyCellLeft δ r)
      (dyadicPhysicalEntropyCellRight δ r) ha_mid hab_mid atom hatom with
    ⟨Hm, hMint, hMnon, hMpoint, hMbound⟩
  rcases exists_integrable_lacunaryRelativeBandpassPhysicalCellOscillation_future_atom_majorant
    hdpos psi j G hG Iplus (dyadicPhysicalEntropyCellLeft δ r)
      (dyadicPhysicalEntropyCellRight δ r) ha_plus hab_plus atom hatom hzero
      (lacunaryCZDyadicCubeRadius_pos q).le hatom_supp with
    ⟨Hf, hFint, hFnon, hFpoint, hFbound⟩
  let L : ℝ := ∫ y : Euclidean d, ‖atom y‖
  let P : ℝ := 2 * (((2 : ℝ) ^ j)⁻¹ ^ 2 *
    SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi)) *
      ((N : ℝ) * (16 / 3 : ℝ)) * surfaceMass d *
        (surfaceMass d * (3 : ℝ) ^ d / (2 * (d : ℝ) ^ 2))
  let M : ℝ := (N : ℝ) * (j : ℝ) * (8 * Real.log 2 * (δ : ℝ)) *
    ∫ x : Euclidean d, ‖G x‖
  let F : ℝ := (d : ℝ) *
    ((N : ℝ) * (2 * (8 * Real.log 2 * (δ : ℝ))) * ((2 : ℝ) ^ j)⁻¹) *
      ∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖
  have hPbound' : (∫ x : Euclidean d, Hp x) ≤ P * L := by
    calc
      (∫ x : Euclidean d, Hp x) ≤
          (2 * (((2 : ℝ) ^ j)⁻¹ ^ 2 *
            SchwartzMap.seminorm ℂ (d + 2) 0 (𝓕⁻ psi)) *
            ((N : ℝ) * (16 / 3 : ℝ) * ((2 : ℝ) ^ q.scale) ^ 2) *
              surfaceMass d * (∫ y : Euclidean d, ‖atom y‖)) *
            (surfaceMass d * (3 : ℝ) ^ d /
              (2 * (lacunaryCZDyadicCubeRadius q) ^ 2)) := hPbound
      _ = P * L := by
        simpa only [P, L] using
          lacunaryRelativeBandpassPhysicalCellShiftedCZ_past_rhs_eq hdpos psi j q L
  have hMbound' : (∫ x : Euclidean d, Hm x) ≤ M * L := by
    have hGnon : 0 ≤ ∫ x : Euclidean d, ‖G x‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have hLnon : 0 ≤ ∫ y : Euclidean d, ‖atom y‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have hscale :
        (∑ z ∈ Imid,
          (dyadicPhysicalEntropyCellRight δ r z - dyadicPhysicalEntropyCellLeft δ r z) *
            (dyadicPhysicalEntropyCellLeft δ r z)⁻¹) *
            (∫ x : Euclidean d, ‖G x‖) ≤
          ((N : ℝ) * (j : ℝ) * (8 * Real.log 2 * (δ : ℝ))) *
            (∫ x : Euclidean d, ‖G x‖) :=
      mul_le_mul_of_nonneg_right hmiddle hGnon
    calc
      (∫ x : Euclidean d, Hm x) ≤
          (∑ z ∈ Imid,
            (dyadicPhysicalEntropyCellRight δ r z - dyadicPhysicalEntropyCellLeft δ r z) *
              (dyadicPhysicalEntropyCellLeft δ r z)⁻¹) *
            (∫ x : Euclidean d, ‖G x‖) *
              (∫ y : Euclidean d, ‖atom y‖) := hMbound
      _ ≤ ((N : ℝ) * (j : ℝ) * (8 * Real.log 2 * (δ : ℝ))) *
            (∫ x : Euclidean d, ‖G x‖) *
              (∫ y : Euclidean d, ‖atom y‖) :=
        mul_le_mul_of_nonneg_right hscale hLnon
      _ = M * L := by rfl
  have hFbound' : (∫ x : Euclidean d, Hf x) ≤ F * L := by
    have hderivnon : 0 ≤ ∫ x : Euclidean d,
        ‖fderiv ℝ (G : Euclidean d → ℂ) x‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have hLnon : 0 ≤ ∫ y : Euclidean d, ‖atom y‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have hscale :
        lacunaryCZDyadicCubeRadius q *
            (∑ z ∈ Iplus,
              (dyadicPhysicalEntropyCellRight δ r z - dyadicPhysicalEntropyCellLeft δ r z) *
                (dyadicPhysicalEntropyCellLeft δ r z)⁻¹ ^ 2) ≤
          lacunaryCZDyadicCubeRadius q *
            ((N : ℝ) * (2 * (8 * Real.log 2 * (δ : ℝ))) *
              ((2 : ℝ) ^ (q.scale + (j : ℤ)))⁻¹) :=
      mul_le_mul_of_nonneg_left hfuture (lacunaryCZDyadicCubeRadius_pos q).le
    have hscale' :
        (lacunaryCZDyadicCubeRadius q *
            (∑ z ∈ Iplus,
              (dyadicPhysicalEntropyCellRight δ r z - dyadicPhysicalEntropyCellLeft δ r z) *
                (dyadicPhysicalEntropyCellLeft δ r z)⁻¹ ^ 2)) *
            (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖) ≤
          (lacunaryCZDyadicCubeRadius q *
            ((N : ℝ) * (2 * (8 * Real.log 2 * (δ : ℝ))) *
              ((2 : ℝ) ^ (q.scale + (j : ℤ)))⁻¹)) *
            (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖) :=
      mul_le_mul_of_nonneg_right hscale hderivnon
    calc
      (∫ x : Euclidean d, Hf x) ≤
          (lacunaryCZDyadicCubeRadius q *
              (∑ z ∈ Iplus,
                (dyadicPhysicalEntropyCellRight δ r z - dyadicPhysicalEntropyCellLeft δ r z) *
                  (dyadicPhysicalEntropyCellLeft δ r z)⁻¹ ^ 2) *
              (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖)) *
                (∫ y : Euclidean d, ‖atom y‖) := hFbound
      _ ≤ lacunaryCZDyadicCubeRadius q *
              ((N : ℝ) * (2 * (8 * Real.log 2 * (δ : ℝ))) *
                ((2 : ℝ) ^ (q.scale + (j : ℤ)))⁻¹) *
              (∫ x : Euclidean d, ‖fderiv ℝ (G : Euclidean d → ℂ) x‖) *
                (∫ y : Euclidean d, ‖atom y‖) :=
        mul_le_mul_of_nonneg_right hscale' hLnon
      _ = F * L := by
        simpa only [F, L] using
          lacunaryRelativeBandpassPhysicalCellShiftedCZ_future_rhs_eq hdpos δ G j q L
  refine ⟨fun x => Hp x + Hm x + Hf x, (hPint.add hMint).add hFint, ?_, ?_, ?_⟩
  · intro x
    exact add_nonneg (add_nonneg (hPnon x) (hMnon x)) (hFnon x)
  · intro x hx
    have hsplit := lacunaryRelativeBandpassPhysicalCellOscillation_shifted_threeWay_scale_split
      K psi j (dyadicPhysicalEntropyCellLeft δ r)
      (dyadicPhysicalEntropyCellRight δ r) q atom x
    rw [hsplit]
    calc
      lacunaryRelativeBandpassPhysicalCellOscillation psi j Iminus
          (dyadicPhysicalEntropyCellLeft δ r)
          (dyadicPhysicalEntropyCellRight δ r) atom x +
        lacunaryRelativeBandpassPhysicalCellOscillation psi j Imid
          (dyadicPhysicalEntropyCellLeft δ r)
          (dyadicPhysicalEntropyCellRight δ r) atom x +
        lacunaryRelativeBandpassPhysicalCellOscillation psi j Iplus
          (dyadicPhysicalEntropyCellLeft δ r)
          (dyadicPhysicalEntropyCellRight δ r) atom x ≤
          ENNReal.ofReal (Hp x) + ENNReal.ofReal (Hm x) + ENNReal.ofReal (Hf x) :=
        add_le_add (add_le_add (hPpoint x hx) (hMpoint x)) (hFpoint x)
      _ = ENNReal.ofReal (Hp x + Hm x + Hf x) := by
        rw [← ENNReal.ofReal_add (hPnon x) (hMnon x),
          ← ENNReal.ofReal_add (add_nonneg (hPnon x) (hMnon x)) (hFnon x)]
  · calc
      (∫ x : Euclidean d, Hp x + Hm x + Hf x) =
          (∫ x : Euclidean d, Hp x) + (∫ x : Euclidean d, Hm x) +
            ∫ x : Euclidean d, Hf x := by
              rw [integral_add (f := fun x => Hp x + Hm x) (g := Hf)
                (hPint.add hMint) hFint,
                integral_add (f := Hp) (g := Hm) hPint hMint]
      _ ≤ P * L + M * L + F * L :=
        add_le_add (add_le_add hPbound' hMbound') hFbound'
      _ = (P + M + F) * L := by ring
      _ = lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G * L := by
        rfl

/-- Summing the shifted per-atom majorants gives the bad-part package used
by the finite physical-cell weak estimate. -/
theorem exists_integrable_lacunaryRelativeBandpassPhysicalCellShiftedCZ_bad_majorant
    {d N : Nat} (hd : 3 ≤ d) (K : Finset ℤ) (δ : NNReal)
    (hδ : Real.log 2 * (δ : ℝ) ≤ 1)
    (r : Fin N → ℤ → PositiveRadius)
    (hr : ∀ i, IsDyadicLacunaryRadiusSelector (r i))
    (psi : SchwartzMap (Euclidean d) ℂ) (j : Nat)
    (G : SchwartzMap (Euclidean d) ℂ)
    (hG : ∀ z : Euclidean d,
      G z = lacunaryRelativeBandpassPhysicalKernelRadiusGenerator psi j z)
    (f : Euclidean d → ℂ) (U : Finset (LacunaryCZDyadicCubeIndex d))
    (hf : Integrable f volume)
    (hdisj : (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
      lacunaryCZDyadicCube) :
    ∃ H : Euclidean d → ℝ, Integrable H volume ∧
      (∀ x, 0 ≤ H x) ∧
      (∀ x, x ∉ lacunaryCZDyadicCubeExceptionalTriple U →
        (∑ u ∈ U,
          lacunaryRelativeBandpassPhysicalCellOscillation psi j
            (K.product Finset.univ) (dyadicPhysicalEntropyCellLeft δ r)
            (dyadicPhysicalEntropyCellRight δ r)
            (lacunaryCZDyadicCubeBadAtom f u) x) ≤ ENNReal.ofReal (H x)) ∧
      (∫ x : Euclidean d, H x) ≤
        2 * lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G *
          (∫ y : Euclidean d, ‖f y‖) := by
  classical
  have hdpos : 0 < d := by omega
  letI : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
  have hatom (u : LacunaryCZDyadicCubeIndex d) (hu : u ∈ U) :
      ∃ H : Euclidean d → ℝ, Integrable H volume ∧
        (∀ x, 0 ≤ H x) ∧
        (∀ x, x ∉ Metric.closedBall (lacunaryCZDyadicCubeCenter u)
            (3 * lacunaryCZDyadicCubeRadius u) →
          lacunaryRelativeBandpassPhysicalCellOscillation psi j
            (K.product Finset.univ) (dyadicPhysicalEntropyCellLeft δ r)
            (dyadicPhysicalEntropyCellRight δ r)
            (lacunaryCZDyadicCubeBadAtom f u) x ≤ ENNReal.ofReal (H x)) ∧
        (∫ x : Euclidean d, H x) ≤
          lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G *
            (∫ y : Euclidean d, ‖lacunaryCZDyadicCubeBadAtom f u y‖) :=
    exists_integrable_lacunaryRelativeBandpassPhysicalCellShiftedCZ_atom_majorant
      hd K δ hδ r hr psi j G hG u (lacunaryCZDyadicCubeBadAtom f u)
      (integrable_lacunaryCZDyadicCubeBadAtom f u hf)
      (integral_lacunaryCZDyadicCubeBadAtom_eq_zero f u hf)
      (fun y hy => lacunaryCZDyadicCubeBadAtom_dist_center_le_radius f u hy)
  choose H0 hHint0 hHnon0 hHpoint0 hHbound0 using hatom
  let H : LacunaryCZDyadicCubeIndex d → Euclidean d → ℝ := fun u =>
    if hu : u ∈ U then H0 u hu else fun _ => 0
  have hHint (u : LacunaryCZDyadicCubeIndex d) (hu : u ∈ U) :
      Integrable (H u) volume := by
    simpa only [H, dif_pos hu] using hHint0 u hu
  have hHnon (u : LacunaryCZDyadicCubeIndex d) (hu : u ∈ U)
      (x : Euclidean d) : 0 ≤ H u x := by
    simpa only [H, dif_pos hu] using hHnon0 u hu x
  have hHpoint (u : LacunaryCZDyadicCubeIndex d) (hu : u ∈ U)
      (x : Euclidean d)
      (hx : x ∉ Metric.closedBall (lacunaryCZDyadicCubeCenter u)
          (3 * lacunaryCZDyadicCubeRadius u)) :
      lacunaryRelativeBandpassPhysicalCellOscillation psi j
          (K.product Finset.univ) (dyadicPhysicalEntropyCellLeft δ r)
          (dyadicPhysicalEntropyCellRight δ r)
          (lacunaryCZDyadicCubeBadAtom f u) x ≤ ENNReal.ofReal (H u x) := by
    simpa only [H, dif_pos hu] using hHpoint0 u hu x hx
  have hHbound (u : LacunaryCZDyadicCubeIndex d) (hu : u ∈ U) :
      (∫ x : Euclidean d, H u x) ≤
        lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G *
          (∫ y : Euclidean d, ‖lacunaryCZDyadicCubeBadAtom f u y‖) := by
    simpa only [H, dif_pos hu] using hHbound0 u hu
  let HT : Euclidean d → ℝ := fun x => ∑ u ∈ U, H u x
  have hHTint : Integrable HT volume := by
    dsimp only [HT]
    exact integrable_finsetSum U fun u hu => hHint u hu
  have hHTnon (x : Euclidean d) : 0 ≤ HT x := by
    dsimp only [HT]
    exact Finset.sum_nonneg fun u hu => hHnon u hu x
  have hHTpoint (x : Euclidean d)
      (hx : x ∉ lacunaryCZDyadicCubeExceptionalTriple U) :
      (∑ u ∈ U,
        lacunaryRelativeBandpassPhysicalCellOscillation psi j
          (K.product Finset.univ) (dyadicPhysicalEntropyCellLeft δ r)
          (dyadicPhysicalEntropyCellRight δ r)
          (lacunaryCZDyadicCubeBadAtom f u) x) ≤ ENNReal.ofReal (HT x) := by
    have hout (u : LacunaryCZDyadicCubeIndex d) (hu : u ∈ U) :
        x ∉ Metric.closedBall (lacunaryCZDyadicCubeCenter u)
          (3 * lacunaryCZDyadicCubeRadius u) := by
      intro hball
      apply hx
      exact Set.mem_iUnion₂.mpr ⟨u, hu, hball⟩
    calc
      (∑ u ∈ U,
        lacunaryRelativeBandpassPhysicalCellOscillation psi j
          (K.product Finset.univ) (dyadicPhysicalEntropyCellLeft δ r)
          (dyadicPhysicalEntropyCellRight δ r)
          (lacunaryCZDyadicCubeBadAtom f u) x) ≤
          ∑ u ∈ U, ENNReal.ofReal (H u x) :=
        Finset.sum_le_sum fun u hu => hHpoint u hu x (hout u hu)
      _ = ENNReal.ofReal (HT x) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun u hu => hHnon u hu x]
  refine ⟨HT, hHTint, hHTnon, hHTpoint, ?_⟩
  have hbad :
      (∑ u ∈ U, ∫ y : Euclidean d, ‖lacunaryCZDyadicCubeBadAtom f u y‖) ≤
        2 * ∫ y : Euclidean d, ‖f y‖ :=
    sum_integral_norm_lacunaryCZDyadicCubeBadAtom_le_two_mul_integral_norm
      f U hdisj hf
  have htailnon :=
    lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant_nonneg N psi j δ G
  calc
    (∫ x : Euclidean d, HT x) = ∑ u ∈ U, ∫ x : Euclidean d, H u x := by
      dsimp only [HT]
      rw [integral_finsetSum U fun u hu => hHint u hu]
    _ ≤ ∑ u ∈ U,
        lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G *
          (∫ y : Euclidean d, ‖lacunaryCZDyadicCubeBadAtom f u y‖) :=
      Finset.sum_le_sum fun u hu => hHbound u hu
    _ = lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G *
        (∑ u ∈ U, ∫ y : Euclidean d, ‖lacunaryCZDyadicCubeBadAtom f u y‖) := by
      rw [Finset.mul_sum]
    _ ≤ lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G *
        (2 * ∫ y : Euclidean d, ‖f y‖) :=
      mul_le_mul_of_nonneg_left hbad htailnon
    _ = _ := by ring

/-- The literal finite physical-cell C--Z weak estimate with the shifted
three-way atom tail. -/
theorem weak_one_lacunaryRelativeBandpassPhysicalCellSquareVariation_of_schwartz_core_shifted
    {d N : Nat} (hd : 3 ≤ d) (K : Finset ℤ) (δ : NNReal)
    (hδ : Real.log 2 * (δ : ℝ) ≤ 1)
    (r : Fin N → ℤ → PositiveRadius)
    (hr : ∀ i, IsDyadicLacunaryRadiusSelector (r i))
    (psi : SchwartzMap (Euclidean d) ℂ)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d → ℂ)) (j : Nat)
    (G : SchwartzMap (Euclidean d) ℂ)
    (hG : ∀ z : Euclidean d,
      G z = lacunaryRelativeBandpassPhysicalKernelRadiusGenerator psi j z)
    (C : ℝ)
    (hcore : ∀ g : SchwartzMap (Euclidean d) ℂ,
      (∫⁻ x, lacunaryRelativeBandpassPhysicalCellSquareVariation psi j
        (K.product Finset.univ) (dyadicPhysicalEntropyCellLeft δ r)
        (dyadicPhysicalEntropyCellRight δ r) (g : Euclidean d → ℂ) x) ≤
          (ENNReal.ofReal C) ^ 2 *
            ∫⁻ x, ENNReal.ofReal (‖(g : Euclidean d → ℂ) x‖ ^ 2))
    (f : SchwartzMap (Euclidean d) ℂ) {lambda : ℝ} (hlambda : 0 < lambda) :
    ENNReal.ofReal lambda * volume {x |
      4 * (ENNReal.ofReal (lambda / 8)) ^ 2 <
        lacunaryRelativeBandpassPhysicalCellSquareVariation psi j
          (K.product Finset.univ) (dyadicPhysicalEntropyCellLeft δ r)
          (dyadicPhysicalEntropyCellRight δ r) (f : Euclidean d → ℂ) x} ≤
      lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant (N := N) psi j δ G C *
        ∫⁻ x, ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖ := by
  classical
  have hdpos : 0 < d := by omega
  letI : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
  let I : Finset (ℤ × Fin N) := K.product Finset.univ
  let aCell : ℤ × Fin N → ℝ := dyadicPhysicalEntropyCellLeft δ r
  let bCell : ℤ × Fin N → ℝ := dyadicPhysicalEntropyCellRight δ r
  let V : (Euclidean d → ℂ) → Euclidean d → ENNReal :=
    lacunaryRelativeBandpassPhysicalCellSquareVariation psi j I aCell bCell
  have haCell (q : ℤ × Fin N) (hq : q ∈ I) : 0 < aCell q := by
    dsimp only [aCell]
    exact dyadicPhysicalEntropyCellLeft_pos δ r hr q
  have habCell (q : ℤ × Fin N) (hq : q ∈ I) : aCell q ≤ bCell q := by
    dsimp only [aCell, bCell]
    exact dyadicPhysicalEntropyCellLeft_le_right δ r hr q
  obtain ⟨U, hdisj, hbad, houtside, havg, hgoodBound, hatomInt, hzero,
    hsupp, hsum, hgoodInt, hgoodL2, hbadL1, hscale, hradius⟩ :=
    exists_lacunaryCZDyadicCube_continuous_decay_decomposition
      (f : Euclidean d → ℂ) lambda hlambda f.continuous f.integrable
      f.tendsto_cocompact
  let g : Euclidean d → ℂ := lacunaryCZDyadicCubeGoodPart (f : Euclidean d → ℂ) U
  let E : Set (Euclidean d) := lacunaryCZDyadicCubeExceptionalTriple U
  let a₀ : ENNReal := ENNReal.ofReal (lambda / 2)
  let b : ENNReal := ENNReal.ofReal (lambda / 8)
  let A : ENNReal := ENNReal.ofReal (3 * (2 : ℝ) ^ d)
  let F : ENNReal := ∫⁻ x, ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖
  let T : ℝ := lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant N psi j δ G
  have ha₀pos : 0 < a₀ := by
    dsimp only [a₀]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have ha₀ : a₀ ≠ 0 := ha₀pos.ne'
  have ha₀top : a₀ ≠ ∞ := by
    dsimp only [a₀]
    exact ENNReal.ofReal_ne_top
  have hbpos : 0 < b := by
    dsimp only [b]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hb : b ≠ 0 := hbpos.ne'
  have hbtop : b ≠ ∞ := by
    dsimp only [b]
    exact ENNReal.ofReal_ne_top
  have haeq : ENNReal.ofReal lambda = 8 * b := by
    dsimp only [b]
    rw [show lambda = 8 * (lambda / 8) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have ha₀eq : a₀ = 4 * b := by
    dsimp only [a₀, b]
    rw [show lambda / 2 = 4 * (lambda / 8) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hB : 0 ≤ (2 : ℝ) ^ d * (lambda / 2) := by positivity
  have hgB : ∀ x, ‖g x‖ ≤ (2 : ℝ) ^ d * (lambda / 2) := by
    intro x
    simpa only [g] using hgoodBound x
  have hg2 : MemLp g 2 volume :=
    memLp_two_of_integrable_of_norm_le_cell g
      (by simpa only [g] using hgoodInt) _ hB hgB
  obtain ⟨M, hMmeas, hMpoint, hMbound⟩ :=
    exists_aemeasurable_lacunaryRelativeBandpassPhysicalCellSquareVariation_majorant_of_schwartz_core
      hdpos psi hpsiCompact j I aCell bCell haCell habCell C
      (by
        intro u
        simpa only [V, I, aCell, bCell] using hcore u)
      g hg2
  obtain ⟨H, hHint, hHnon, hHpoint, hHbound⟩ :=
    exists_integrable_lacunaryRelativeBandpassPhysicalCellShiftedCZ_bad_majorant
      hd K δ hδ r hr psi j G hG (f : Euclidean d → ℂ) U f.integrable hdisj
  have hlevel :
      ({x : Euclidean d | 4 * b ^ 2 < V (f : Euclidean d → ℂ) x} :
        Set (Euclidean d)) ≤ᵐ[volume]
        Set.union E (Set.union
          ({x : Euclidean d | b ^ 2 < M x} : Set (Euclidean d))
          (Set.inter ({x : Euclidean d | b < ENNReal.ofReal (H x)} : Set (Euclidean d)) Eᶜ)) := by
    filter_upwards [hMpoint] with x hxM hx
    by_cases hxE : x ∈ E
    · exact Or.inl hxE
    · by_cases hxGood : b ^ 2 < M x
      · exact Or.inr (Or.inl hxGood)
      · by_cases hxBad : b < ENNReal.ofReal (H x)
        · exact Or.inr (Or.inr ⟨hxBad, hxE⟩)
        · exfalso
          have hsplit :=
            lacunaryRelativeBandpassPhysicalCellSquareVariation_le_two_mul_CZGood_add_badOscillation_sq
              psi j I aCell bCell haCell habCell (f : Euclidean d → ℂ)
                f.integrable U x
          have hbadpoint := hHpoint x hxE
          have hbadSq :
              (∑ u ∈ U,
                lacunaryRelativeBandpassPhysicalCellOscillation psi j I aCell bCell
                  (lacunaryCZDyadicCubeBadAtom (f : Euclidean d → ℂ) u) x) ^ 2 ≤
                (ENNReal.ofReal (H x)) ^ 2 :=
            pow_le_pow_left' hbadpoint 2
          have hbound : V (f : Euclidean d → ℂ) x ≤ 4 * b ^ 2 := by
            calc
              V (f : Euclidean d → ℂ) x ≤
                  2 * V g x +
                    2 * (∑ u ∈ U,
                      lacunaryRelativeBandpassPhysicalCellOscillation psi j I aCell bCell
                        (lacunaryCZDyadicCubeBadAtom (f : Euclidean d → ℂ) u) x) ^ 2 := by
                  simpa only [V] using hsplit
              _ ≤ 2 * M x + 2 * (ENNReal.ofReal (H x)) ^ 2 :=
                add_le_add
                  (by simpa only [mul_comm] using mul_le_mul_left hxM 2)
                  (by simpa only [mul_comm] using mul_le_mul_left hbadSq 2)
              _ ≤ 2 * b ^ 2 + 2 * b ^ 2 :=
                add_le_add
                  (by simpa only [mul_comm] using
                    mul_le_mul_left (le_of_not_gt hxGood) 2)
                  (by simpa only [mul_comm] using
                    mul_le_mul_left (pow_le_pow_left' (le_of_not_gt hxBad) 2) 2)
              _ = 4 * b ^ 2 := by ring
          exact (not_lt_of_ge hbound hx)
  have hgSq : Integrable (fun x => ‖g x‖ ^ (2 : ℕ)) volume := by
    simpa using hg2.integrable_norm_rpow (by norm_num) ENNReal.ofNat_ne_top
  have hFreal : ENNReal.ofReal (∫ x, ‖(f : Euclidean d → ℂ) x‖) = F := by
    dsimp only [F]
    exact ofReal_integral_eq_lintegral_ofReal f.integrable.norm
      (Filter.Eventually.of_forall fun x => norm_nonneg _)
  have hgoodLin :
      (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ))) ≤ A * a₀ * F := by
    calc
      (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ))) =
          ENNReal.ofReal (∫ x, ‖g x‖ ^ (2 : ℕ)) :=
        (ofReal_integral_eq_lintegral_ofReal hgSq
          (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal
          ((3 * ((2 : ℝ) ^ d * (lambda / 2))) *
            ∫ x, ‖(f : Euclidean d → ℂ) x‖) :=
        ENNReal.ofReal_le_ofReal (by simpa only [g] using hgoodL2)
      _ = A * a₀ * F := by
        have hAreal : 0 ≤ 3 * (2 : ℝ) ^ d := by positivity
        rw [show 3 * ((2 : ℝ) ^ d * (lambda / 2)) =
              (3 * (2 : ℝ) ^ d) * (lambda / 2) by ring,
          ENNReal.ofReal_mul (mul_nonneg hAreal (by linarith)),
          ENNReal.ofReal_mul hAreal, hFreal]
  have hgoodMarkov :
      b ^ 2 * volume {x | b ^ 2 < M x} ≤ ∫⁻ x, M x :=
    mul_measure_cell_level_le_lintegral_of_ae_majorant M M hMmeas
      (Filter.Eventually.of_forall fun x => le_rfl) (b ^ 2)
  have hgoodSq :
      b ^ 2 * volume {x | b ^ 2 < M x} ≤
        (ENNReal.ofReal C) ^ 2 * ((4 * A) * b * F) := by
    calc
      b ^ 2 * volume {x | b ^ 2 < M x} ≤ ∫⁻ x, M x := hgoodMarkov
      _ ≤ (ENNReal.ofReal C) ^ 2 *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) := hMbound
      _ ≤ (ENNReal.ofReal C) ^ 2 * (A * a₀ * F) :=
        by simpa only [mul_comm] using
          mul_le_mul_left hgoodLin ((ENNReal.ofReal C) ^ 2)
      _ = (ENNReal.ofReal C) ^ 2 * ((4 * A) * b * F) := by
        rw [ha₀eq]
        ring
  have hgoodScaled :
      (8 * b) * volume {x | b ^ 2 < M x} ≤
        (32 * A * (ENNReal.ofReal C) ^ 2) * F :=
    weak_square_level_scaled_eight hb hbtop hgoodSq
  have hTnon : 0 ≤ T := by
    dsimp only [T]
    exact lacunaryRelativeBandpassPhysicalCellShiftedCZTailConstant_nonneg N psi j δ G
  have hHlintegral :
      (∫⁻ x, ENNReal.ofReal (H x)) ≤ ENNReal.ofReal (2 * T) * F := by
    calc
      (∫⁻ x, ENNReal.ofReal (H x)) = ENNReal.ofReal (∫ x, H x) :=
        (ofReal_integral_eq_lintegral_ofReal hHint
          (Filter.Eventually.of_forall fun x => hHnon x)).symm
      _ ≤ ENNReal.ofReal (2 * T * ∫ x, ‖(f : Euclidean d → ℂ) x‖) :=
        ENNReal.ofReal_le_ofReal (by simpa only [T] using hHbound)
      _ = ENNReal.ofReal (2 * T) * F := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * T), hFreal]
  have hbadMarkov :
      b * volume {x | b < ENNReal.ofReal (H x)} ≤
        ∫⁻ x, ENNReal.ofReal (H x) :=
    mul_measure_cell_level_le_lintegral_of_ae_majorant
      (fun x => ENNReal.ofReal (H x)) (fun x => ENNReal.ofReal (H x))
      hHint.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => le_rfl) b
  have hbadScaled :
      (8 * b) * volume {x | b < ENNReal.ofReal (H x)} ≤
        (16 * ENNReal.ofReal T) * F := by
    calc
      (8 * b) * volume {x | b < ENNReal.ofReal (H x)} =
          8 * (b * volume {x | b < ENNReal.ofReal (H x)}) := by ring
      _ ≤ 8 * (∫⁻ x, ENNReal.ofReal (H x)) := mul_le_mul_right hbadMarkov _
      _ ≤ 8 * (ENNReal.ofReal (2 * T) * F) :=
        mul_le_mul_right hHlintegral _
      _ = (16 * ENNReal.ofReal T) * F := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
        ring
  let D : ℝ :=
    (volume (Metric.ball (0 : Euclidean d) 1)).toReal * (3 : ℝ) ^ d * (d : ℝ) ^ d
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hEreal : volume.real E ≤ D * (lambda / 2)⁻¹ *
      ∫ x, ‖(f : Euclidean d → ℂ) x‖ := by
    calc
      volume.real E ≤
          (volume (Metric.ball (0 : Euclidean d) 1)).toReal * (3 : ℝ) ^ d *
            ((d : ℝ) ^ d * ((lambda / 2)⁻¹ *
              ∫ x, ‖(f : Euclidean d → ℂ) x‖)) := by
        simpa only [E] using
          volume_real_lacunaryCZDyadicCubeExceptionalTriple_le_of_radius_sum U hradius
      _ = D * (lambda / 2)⁻¹ * ∫ x, ‖(f : Euclidean d → ℂ) x‖ := by
        dsimp only [D]
        ring
  have hEKnon : 0 ≤ D * (lambda / 2)⁻¹ *
      ∫ x, ‖(f : Euclidean d → ℂ) x‖ :=
    mul_nonneg (mul_nonneg hD (inv_nonneg.mpr (by linarith)))
      (integral_nonneg fun _ => norm_nonneg _)
  have hEraw : volume E ≤ ENNReal.ofReal
      (D * (lambda / 2)⁻¹ * ∫ x, ‖(f : Euclidean d → ℂ) x‖) :=
    measure_le_of_real_bound_cell volume E (exceptional_lt_top_cell U).ne hEKnon hEreal
  have hEbound : volume E ≤ ENNReal.ofReal D * a₀⁻¹ * F := by
    calc
      volume E ≤ ENNReal.ofReal
          (D * (lambda / 2)⁻¹ * ∫ x, ‖(f : Euclidean d → ℂ) x‖) := hEraw
      _ = ENNReal.ofReal D * a₀⁻¹ * F := by
        rw [ENNReal.ofReal_mul (mul_nonneg hD (inv_nonneg.mpr (by linarith))),
          ENNReal.ofReal_mul hD, ENNReal.ofReal_inv_of_pos (by linarith), hFreal]
  have hEScaled : (8 * b) * volume E ≤ (2 * ENNReal.ofReal D) * F := by
    calc
      (8 * b) * volume E = (2 * a₀) * volume E := by rw [ha₀eq]; ring
      _ ≤ (2 * a₀) * (ENNReal.ofReal D * a₀⁻¹ * F) :=
        mul_le_mul_right hEbound _
      _ = (2 * ENNReal.ofReal D) * F := by
        rw [show 2 * a₀ * (ENNReal.ofReal D * a₀⁻¹ * F) =
              (2 * ENNReal.ofReal D) * (a₀ * a₀⁻¹) * F by ring,
          ENNReal.mul_inv_cancel ha₀ ha₀top, mul_one]
  have hunion :
      volume {x | 4 * b ^ 2 < V (f : Euclidean d → ℂ) x} ≤
        volume E + (volume {x | b ^ 2 < M x} +
          volume ({x | b < ENNReal.ofReal (H x)} ∩ Eᶜ)) := by
    calc
      volume {x | 4 * b ^ 2 < V (f : Euclidean d → ℂ) x} ≤
          volume (Set.union E (Set.union {x | b ^ 2 < M x}
            (Set.inter {x | b < ENNReal.ofReal (H x)} Eᶜ))) := measure_mono_ae hlevel
      _ ≤ volume E + volume (Set.union {x | b ^ 2 < M x}
          (Set.inter {x | b < ENNReal.ofReal (H x)} Eᶜ)) := measure_union_le _ _
      _ ≤ volume E + (volume {x | b ^ 2 < M x} +
          volume ({x | b < ENNReal.ofReal (H x)} ∩ Eᶜ)) :=
        add_le_add le_rfl (measure_union_le _ _)
  have hsum :
      (8 * b) * volume {x | 4 * b ^ 2 < V (f : Euclidean d → ℂ) x} ≤
        ((2 * ENNReal.ofReal D) +
          (32 * A * (ENNReal.ofReal C) ^ 2) +
          (16 * ENNReal.ofReal T)) * F := by
    calc
      (8 * b) * volume {x | 4 * b ^ 2 < V (f : Euclidean d → ℂ) x} ≤
          (8 * b) * (volume E + (volume {x | b ^ 2 < M x} +
            volume ({x | b < ENNReal.ofReal (H x)} ∩ Eᶜ))) :=
        mul_le_mul_right hunion _
      _ = (8 * b) * volume E +
          ((8 * b) * volume {x | b ^ 2 < M x} +
            (8 * b) * volume ({x | b < ENNReal.ofReal (H x)} ∩ Eᶜ)) := by ring
      _ ≤ (2 * ENNReal.ofReal D) * F +
          ((32 * A * (ENNReal.ofReal C) ^ 2) * F +
            (16 * ENNReal.ofReal T) * F) :=
        add_le_add hEScaled (add_le_add hgoodScaled (by
          calc
            (8 * b) * volume ({x | b < ENNReal.ofReal (H x)} ∩ Eᶜ) ≤
                (8 * b) * volume {x | b < ENNReal.ofReal (H x)} :=
              mul_le_mul_right (measure_mono Set.inter_subset_left) _
            _ ≤ (16 * ENNReal.ofReal T) * F := hbadScaled))
      _ = ((2 * ENNReal.ofReal D) +
          (32 * A * (ENNReal.ofReal C) ^ 2) +
          (16 * ENNReal.ofReal T)) * F := by ring
  rw [haeq]
  simpa only [I, aCell, bCell, V, D, A, T,
    lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant] using hsum

/-- The finite physical-block relative band obeys weak type `(1,1)` once the
shifted literal finite-cell Schwartz core and the lacunary palette endpoint
have been supplied.  This is the finite estimate fed to the dyadic
exhaustion. -/
theorem weak_one_restrictedRelativeBandpassSphericalMaximal_dyadicRadiusBlockUnion_of_shifted_CZ_core
    {d N : Nat} (hd : 3 ≤ d) (K : Finset ℤ) (δ : NNReal)
    (hδ : Real.log 2 * (δ : ℝ) ≤ 1)
    (phi ψ : SchwartzMap (Euclidean d) ℂ)
    (hψ : ∀ ξ : Euclidean d,
      ψ ξ = phi ((2 : ℝ)⁻¹ • ξ) - phi ξ)
    (hψCompact : HasCompactSupport (ψ : Euclidean d → ℂ))
    (j : Nat) (G : SchwartzMap (Euclidean d) ℂ)
    (hG : ∀ z : Euclidean d,
      G z = lacunaryRelativeBandpassPhysicalKernelRadiusGenerator ψ j z)
    (r : Fin N → ℤ → PositiveRadius)
    (hr : ∀ i, IsDyadicLacunaryRadiusSelector (r i))
    (E : Set ℝ)
    (hcover : ∀ k ∈ K, ∀ s : PositiveRadius,
      (s : ℝ) ∈ E ∩ Icc ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k) →
        ∃ i : Fin N, |logRadius s - logRadius (r i k)| ≤ (δ : ℝ))
    (C : ℝ)
    (hcore : ∀ g : SchwartzMap (Euclidean d) ℂ,
      (∫⁻ x, lacunaryRelativeBandpassPhysicalCellSquareVariation ψ j
        (K.product Finset.univ) (dyadicPhysicalEntropyCellLeft δ r)
        (dyadicPhysicalEntropyCellRight δ r) (g : Euclidean d → ℂ) x) ≤
          (ENNReal.ofReal C) ^ 2 *
            ∫⁻ x, ENNReal.ofReal (‖(g : Euclidean d → ℂ) x‖ ^ 2))
    (Q : ENNReal) (f : SchwartzMap (Euclidean d) ℂ)
    (hpalette : ∀ {t : ℝ}, 0 < t →
      ENNReal.ofReal t * volume {x |
        ENNReal.ofReal t < lacunaryRelativeBandpassPhysicalPaletteMaximalAll ψ j r
          (f : Euclidean d → ℂ) x} ≤
        Q * ∫⁻ x, ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ENNReal.ofReal lambda * volume {x |
      ENNReal.ofReal lambda <
        restrictedRelativeBandpassSphericalMaximal d
          (dyadicRadiusBlockUnion E K) phi j f x} ≤
      (2 * Q +
        lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant (N := N) ψ j δ G C) *
          ∫⁻ x, ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖ := by
  classical
  let M : Euclidean d → ENNReal := fun x =>
    restrictedRelativeBandpassSphericalMaximal d
      (dyadicRadiusBlockUnion E K) phi j f x
  let P : Euclidean d → ENNReal := fun x =>
    lacunaryRelativeBandpassPhysicalPaletteMaximalAll ψ j r
      (f : Euclidean d → ℂ) x
  let V : Euclidean d → ENNReal :=
    lacunaryRelativeBandpassPhysicalCellSquareVariation ψ j
      (K.product Finset.univ) (dyadicPhysicalEntropyCellLeft δ r)
      (dyadicPhysicalEntropyCellRight δ r) (f : Euclidean d → ℂ)
  let a : ENNReal := ENNReal.ofReal lambda
  let b : ENNReal := ENNReal.ofReal (lambda / 8)
  let c : ENNReal := ENNReal.ofReal (lambda / 2)
  let F : ENNReal := ∫⁻ x, ENNReal.ofReal ‖(f : Euclidean d → ℂ) x‖
  by_cases hnonempty : (dyadicRadiusBlockUnion E K ∩ Ioi (0 : ℝ)).Nonempty
  · have haeq : a = 8 * b := by
      dsimp only [a, b]
      rw [show lambda = 8 * (lambda / 8) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    have hceq : c = 4 * b := by
      dsimp only [c, b]
      rw [show lambda / 2 = 4 * (lambda / 8) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    have haceq : a = 2 * c := by
      dsimp only [a, c]
      rw [show lambda = 2 * (lambda / 2) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hpoint (x : Euclidean d) :
        M x ^ 2 ≤ 2 * (P x) ^ 2 + 8 * V x := by
      simpa only [M, P, V] using
        restrictedRelativeBandpassSphericalMaximal_sq_le_palette_add_cellVariation
          phi ψ f hψ j E K δ r hr hcover hnonempty x
    have hlevel :
        {x : Euclidean d | a < M x} ⊆
          Set.union ({x : Euclidean d | c < P x} : Set (Euclidean d))
            ({x : Euclidean d | 4 * b ^ 2 < V x} : Set (Euclidean d)) := by
      intro x hx
      by_cases hxP : c < P x
      · exact Or.inl hxP
      · by_cases hxV : 4 * b ^ 2 < V x
        · exact Or.inr hxV
        · exfalso
          have hstrict : a ^ 2 < (M x) ^ 2 := by
            have h' := ENNReal.rpow_lt_rpow hx (by norm_num : (0 : ℝ) < 2)
            norm_num at h' ⊢
            exact h'
          have hbound : (M x) ^ 2 ≤ a ^ 2 := by
            calc
              (M x) ^ 2 ≤ 2 * (P x) ^ 2 + 8 * V x := hpoint x
              _ ≤ 2 * c ^ 2 + 8 * (4 * b ^ 2) :=
                add_le_add
                  (by
                    simpa only [mul_comm] using
                      mul_le_mul_left (pow_le_pow_left' (le_of_not_gt hxP) 2) 2)
                  (by
                    simpa only [mul_comm] using
                      mul_le_mul_left (le_of_not_gt hxV) 8)
              _ = (8 * b) ^ 2 := by
                rw [hceq]
                ring
              _ = a ^ 2 := by rw [haeq]
          exact (not_lt_of_ge hbound hstrict)
    have hcell :=
      weak_one_lacunaryRelativeBandpassPhysicalCellSquareVariation_of_schwartz_core_shifted
        hd K δ hδ r hr ψ hψCompact j G hG C hcore f hlambda
    have hcell' :
        a * volume {x : Euclidean d | 4 * b ^ 2 < V x} ≤
          lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant (N := N) ψ j δ G C * F := by
      simpa only [a, b, V, F] using hcell
    have hpalette' :
        a * volume {x : Euclidean d | c < P x} ≤ (2 * Q) * F := by
      have hp := hpalette (t := lambda / 2) (by linarith)
      have hp' : c * volume {x : Euclidean d | c < P x} ≤ Q * F := by
        simpa only [c, P, F] using hp
      calc
        a * volume {x : Euclidean d | c < P x} =
            2 * (c * volume {x : Euclidean d | c < P x}) := by
              rw [haceq]
              ring
        _ ≤ 2 * (Q * F) := mul_le_mul_right hp' _
        _ = (2 * Q) * F := by ring
    have hunion :
        volume {x : Euclidean d | a < M x} ≤
          volume {x : Euclidean d | c < P x} +
            volume {x : Euclidean d | 4 * b ^ 2 < V x} := by
      calc
        volume {x : Euclidean d | a < M x} ≤
            volume (Set.union {x : Euclidean d | c < P x}
              {x : Euclidean d | 4 * b ^ 2 < V x}) := measure_mono hlevel
        _ ≤ _ := measure_union_le _ _
    have hsum :
        a * volume {x : Euclidean d | a < M x} ≤
          (2 * Q +
            lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant (N := N) ψ j δ G C) * F := by
      calc
        a * volume {x : Euclidean d | a < M x} ≤
            a * (volume {x : Euclidean d | c < P x} +
              volume {x : Euclidean d | 4 * b ^ 2 < V x}) :=
          mul_le_mul_right hunion _
        _ = a * volume {x : Euclidean d | c < P x} +
            a * volume {x : Euclidean d | 4 * b ^ 2 < V x} := by ring
        _ ≤ (2 * Q) * F +
            lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant (N := N) ψ j δ G C * F :=
          add_le_add hpalette' hcell'
        _ = (2 * Q +
            lacunaryRelativeBandpassPhysicalCellShiftedWeakOneConstant (N := N) ψ j δ G C) * F := by
          ring
    simpa only [a, M, F] using hsum
  · have hempty : dyadicRadiusBlockUnion E K ∩ Ioi (0 : ℝ) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    letI : IsEmpty ↥(dyadicRadiusBlockUnion E K ∩ Ioi (0 : ℝ)) :=
      ⟨fun r => by
        have hr : r.1 ∈ (∅ : Set ℝ) := by simpa only [hempty] using r.2
        simpa only [Set.mem_empty_iff_false] using hr⟩
    have hzero (x : Euclidean d) : M x = 0 := by
      simp [M, restrictedRelativeBandpassSphericalMaximal]
    have hlevel : {x : Euclidean d | ENNReal.ofReal lambda <
        restrictedRelativeBandpassSphericalMaximal d
          (dyadicRadiusBlockUnion E K) phi j f x} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      change ¬ ENNReal.ofReal lambda < M x
      rw [hzero x]
      exact not_lt_of_ge bot_le
    rw [hlevel, measure_empty, mul_zero]
    exact bot_le

end

end LeanSpherical.HarmonicAnalysis
