/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4FiniteProductRegularity
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4FullProductMaximalBridge

/-!
# Literal full-product estimates on canonical fields

The crossed shell argument produces an `eLpNorm` bound for an actual
physical-times-counting product.  The finite-product diagonal, on the other
hand, is written in terms of fibre moments.  This file contains the small,
fully literal passage between the two.  In particular the physical shell need
only be a.e.-strongly measurable: we choose its canonical measurable
representative internally and transport it back to every finite fibre.

There is no abstract analysis or adjoint operator in this conversion.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set ENNReal
open scoped BigOperators

noncomputable section

/-- The crossed strong constant is finite in its strict range.  This is a
small but important bookkeeping fact: its only apparent inverse is
`(q - 2)⁻¹`, and strictness makes that denominator nonzero. -/
theorem q4CrossedStrongShellConstant_ne_top
    {q A E : Real} (hq : 2 < q) :
    q4CrossedStrongShellConstant q A E ≠ ⊤ := by
  have hqpos : 0 < q := lt_trans zero_lt_two hq
  have hqm2pos : 0 < q - 2 := sub_pos.mpr hq
  have hqm2nonneg : 0 ≤ q - 2 := hqm2pos.le
  unfold q4CrossedStrongShellConstant
  apply ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hqpos.le)
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · norm_num
    · exact ENNReal.ofReal_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero.mpr hqm2pos)
    · exact ENNReal.rpow_ne_top_of_nonneg hqm2nonneg ENNReal.ofReal_ne_top

/-- Every displayed level coefficient in the literal active product
reassembly is finite at a strict crossed exponent. -/
theorem q4ActiveDyadicLevelStrongConstant_ne_top
    {d : Nat} {gamma eta Ccover Ckernel B q : Real} {j n : Nat}
    (hq : 2 < q) :
    q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q ≠ ⊤ := by
  unfold q4ActiveDyadicLevelStrongConstant
  split <;> exact q4CrossedStrongShellConstant_ne_top hq

/-- A finite reassembly of strict crossed shell constants is finite. -/
theorem q4ActiveDyadicLevelStrongConstant_sum_ne_top
    {d : Nat} {gamma eta Ccover Ckernel B q : Real} {j : Nat}
    (hq : 2 < q) :
    (∑ n ∈ Finset.range (j + 3),
      q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q) ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro n hn
  exact q4ActiveDyadicLevelStrongConstant_ne_top hq

/-- An `eLpNorm` strong estimate for a literal finite product implies the
root fibre-moment estimate used in the `TT*` diagonal, even when the output
is initially supplied only with an a.e.-strongly measurable physical
representative.  The measurable representative is selected inside the proof,
so later actual derivative theorems need not expose a regularity hypothesis
for the raw convolution shell. -/
theorem q4FibreLpMoment_root_le_of_product_eLpNorm_aestronglyMeasurable
    {I X : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (mu : Measure X) [SFinite mu] (s : Finset I)
    (out inn : X × {i // i ∈ s} → Complex)
    {q qdual D : Real} (hq : 0 < q) (hqdual : 0 < qdual) (hD : 0 ≤ D)
    (houtmeas : AEStronglyMeasurable out (q4FiniteProductCountingMeasure mu s))
    (hinmeas : Measurable inn)
    (hinpow : Integrable (fun z => ‖inn z‖ ^ qdual)
      (q4FiniteProductCountingMeasure mu s))
    (hstrong : eLpNorm out (ENNReal.ofReal q) (q4FiniteProductCountingMeasure mu s) ≤
      ENNReal.ofReal D *
        eLpNorm inn (ENNReal.ofReal qdual) (q4FiniteProductCountingMeasure mu s)) :
    (q4FibreLpMoment mu s q (q4FiniteProductToFibres s out)) ^ (1 / q) ≤
      D * (q4FibreLpMoment mu s qdual (q4FiniteProductToFibres s inn)) ^ (1 / qdual) := by
  let out' : X × {i // i ∈ s} → Complex := houtmeas.aemeasurable.mk out
  have hout'meas : Measurable out' := houtmeas.aemeasurable.measurable_mk
  have hout_eq : out =ᵐ[q4FiniteProductCountingMeasure mu s] out' :=
    houtmeas.aemeasurable.ae_eq_mk
  have hinLp : MemLp inn (ENNReal.ofReal qdual)
      (q4FiniteProductCountingMeasure mu s) := by
    apply (integrable_norm_rpow_iff hinmeas.aestronglyMeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hqdual) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hqdual.le] using hinpow
  have houtLp : MemLp out (ENNReal.ofReal q)
      (q4FiniteProductCountingMeasure mu s) := by
    refine ⟨houtmeas, lt_of_le_of_lt hstrong ?_⟩
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hinLp.eLpNorm_lt_top
  have houtpow : Integrable (fun z => ‖out z‖ ^ q)
      (q4FiniteProductCountingMeasure mu s) := by
    have h := houtLp.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hq.le] using h
  have houtfib (i : I) (hi : i ∈ s) :
      Integrable (fun x => ‖q4FiniteProductToFibres s out i x‖ ^ q) mu :=
    integrable_norm_rpow_q4FiniteProductToFibres_of_integrable mu s out houtpow i hi
  have hinfib (i : I) (hi : i ∈ s) :
      Integrable (fun x => ‖q4FiniteProductToFibres s inn i x‖ ^ qdual) mu :=
    integrable_norm_rpow_q4FiniteProductToFibres_of_integrable mu s inn hinpow i hi
  have hout'fib (i : I) (hi : i ∈ s) :
      Integrable (fun x => ‖q4FiniteProductToFibres s out' i x‖ ^ q) mu := by
    refine (houtfib i hi).congr ?_
    exact (q4FiniteProductToFibres_ae_eq_of_ae_eq_product
      mu s out out' hout_eq i hi).fun_comp (fun z : Complex => ‖z‖ ^ q)
  have houtpowmeas : Measurable (fun z => ENNReal.ofReal (‖out' z‖ ^ q)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_id.rpow_const (fun _ => Or.inr hq.le)).measurable.comp hout'meas.norm)
  have hinpowmeas : Measurable (fun z => ENNReal.ofReal (‖inn z‖ ^ qdual)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_id.rpow_const (fun _ => Or.inr hqdual.le)).measurable.comp hinmeas.norm)
  have hstrong' : eLpNorm out' (ENNReal.ofReal q)
      (q4FiniteProductCountingMeasure mu s) ≤
      ENNReal.ofReal D *
        eLpNorm inn (ENNReal.ofReal qdual) (q4FiniteProductCountingMeasure mu s) := by
    calc
      eLpNorm out' (ENNReal.ofReal q) (q4FiniteProductCountingMeasure mu s) =
          eLpNorm out (ENNReal.ofReal q) (q4FiniteProductCountingMeasure mu s) :=
        (eLpNorm_congr_ae hout_eq).symm
      _ ≤ ENNReal.ofReal D *
          eLpNorm inn (ENNReal.ofReal qdual) (q4FiniteProductCountingMeasure mu s) := hstrong
  have hroot := q4FibreLpMoment_root_le_of_product_eLpNorm
    mu s out' inn hq hqdual hD houtpowmeas hinpowmeas hout'fib hinfib hstrong'
  rw [q4FibreLpMoment_toFibres_eq_of_ae_eq_product mu s out out' hout_eq q]
  exact hroot

/-- A finite-product strong estimate also supplies honest `L^q` membership
on every active physical fibre.  This is the regularity input for the
literal HÃ¶lder pairing in the `TT*` diagonal.  The result is deliberately
separate from the root-moment conversion above: a numerical moment bound by
itself would not justify applying HÃ¶lder to the raw physical shell. -/
theorem memLp_q4FiniteProductToFibres_of_product_eLpNorm_aestronglyMeasurable
    {I X : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (mu : Measure X) [SFinite mu] (s : Finset I)
    (out inn : X Ã— {i // i ∈ s} → Complex)
    {q qdual : Real} (hq : 0 < q) (hqdual : 0 < qdual)
    (C : ENNReal) (hC : C ≠ ⊤)
    (houtmeas : AEStronglyMeasurable out (q4FiniteProductCountingMeasure mu s))
    (hinmeas : Measurable inn)
    (hinpow : Integrable (fun z => ‖inn z‖ ^ qdual)
      (q4FiniteProductCountingMeasure mu s))
    (hstrong : eLpNorm out (ENNReal.ofReal q) (q4FiniteProductCountingMeasure mu s) ≤
      C * eLpNorm inn (ENNReal.ofReal qdual) (q4FiniteProductCountingMeasure mu s)) :
    ∀ i ∈ s, MemLp (q4FiniteProductToFibres s out i) (ENNReal.ofReal q) mu := by
  let out' : X Ã— {i // i ∈ s} → Complex := houtmeas.aemeasurable.mk out
  have hout'meas : Measurable out' := houtmeas.aemeasurable.measurable_mk
  have hout_eq : out =ᵐ[q4FiniteProductCountingMeasure mu s] out' :=
    houtmeas.aemeasurable.ae_eq_mk
  have hinLp : MemLp inn (ENNReal.ofReal qdual)
      (q4FiniteProductCountingMeasure mu s) := by
    apply (integrable_norm_rpow_iff hinmeas.aestronglyMeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hqdual) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hqdual.le] using hinpow
  have houtLp : MemLp out (ENNReal.ofReal q)
      (q4FiniteProductCountingMeasure mu s) := by
    refine ⟨houtmeas, lt_of_le_of_lt hstrong ?_⟩
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) hinLp.eLpNorm_lt_top
  have houtpow : Integrable (fun z => ‖out z‖ ^ q)
      (q4FiniteProductCountingMeasure mu s) := by
    have h := houtLp.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hq.le] using h
  intro i hi
  have houtfib : Integrable (fun x => ‖q4FiniteProductToFibres s out i x‖ ^ q) mu :=
    integrable_norm_rpow_q4FiniteProductToFibres_of_integrable mu s out houtpow i hi
  have houtfib_meas : AEStronglyMeasurable (q4FiniteProductToFibres s out i) mu := by
    have hout'_fib_meas : Measurable (q4FiniteProductToFibres s out' i) := by
      change Measurable (fun x : X => out' (x, ⟨i, hi⟩))
      exact hout'meas.comp (measurable_id.prodMk measurable_const)
    exact hout'_fib_meas.aestronglyMeasurable.congr_ae
      (q4FiniteProductToFibres_ae_eq_of_ae_eq_product mu s out out' hout_eq i hi).symm
  apply (integrable_norm_rpow_iff houtfib_meas
    (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hq.le] using houtfib

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
