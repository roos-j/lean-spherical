/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4DerivativeActiveFullProduct
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4ActualSelectedVariation

/-!
# The literal fixed-offset `TT*` step for the derivative family

The product-shell estimate proved from the stationary kernel and Fourier
multiplier bounds acts on the canonical power dual.  This file performs the
remaining, genuinely Hilbert-space, diagonal calculation.  In particular it
does not invoke the spherical maximal theorem as a black box and it does not
assume a variation estimate.  The physical shell is compared fibrewise with
the completed Fourier-multiplier product, whose finite `TT*` diagonal is an
exact square energy.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set ENNReal
open scoped BigOperators FourierTransform

noncomputable section

private theorem q4FiniteProductPairing_congr_left_ae
    {I X : Type*} [MeasurableSpace X] [DecidableEq I]
    (mu : Measure X) (s : Finset I)
    (f f' g : I -> X -> Complex)
    (h : ∀ i ∈ s, f i =ᵐ[mu] f' i) :
    q4FiniteProductPairing mu s f g = q4FiniteProductPairing mu s f' g := by
  unfold q4FiniteProductPairing
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [h i hi] with x hx
  rw [hx]

private theorem q4FiniteProductPairing_congr_right_ae
    {I X : Type*} [MeasurableSpace X] [DecidableEq I]
    (mu : Measure X) (s : Finset I)
    (f g g' : I -> X -> Complex)
    (h : ∀ i ∈ s, g i =ᵐ[mu] g' i) :
    q4FiniteProductPairing mu s f g = q4FiniteProductPairing mu s f g' := by
  unfold q4FiniteProductPairing
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [h i hi] with x hx
  rw [hx]

private theorem q4FiniteProductPairing_l2_coeFn_eq_sum_inner
    {I X : Type*} [MeasurableSpace X] [DecidableEq I]
    (mu : Measure X) [SFinite mu] (s : Finset I)
    (P G : I -> Lp Complex 2 mu) :
    q4FiniteProductPairing mu s
      (fun i x => ((P i : Lp Complex 2 mu) : X -> Complex) x)
      (fun i x => ((G i : Lp Complex 2 mu) : X -> Complex) x) =
      ∑ i ∈ s, inner Complex (G i) (P i) := by
  unfold q4FiniteProductPairing
  apply Finset.sum_congr rfl
  intro i hi
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

/-- The actual physical derivative full-shell diagonal is exactly the
completed finite `L²` synthesis energy.  This uses the literal
physical/`L²` comparison on every active fibre, and then the finite
Hilbert-space `TT*` identity. -/
private theorem q4ActiveDyadicScaledNormalizedDerivative_fullKernelDiagonal_eq_l2Energy
    {d : Nat} (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    (j : Nat) (u : Real) (s : Finset Int) (q : Real) (hq : 2 <= q)
    (f : SchwartzMap (Euclidean d) Complex) :
    q4FiniteProductKernelBilinear volume s (fun _ _ => True)
      (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
      (q4PowerDualField q
        (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
          psi hpsiCompact j u f))
      (q4PowerDualField q
        (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
          psi hpsiCompact j u f)) =
      inner Complex
        (q4L2FiniteFibreSynthesis s
          (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
            psi hpsiCompact j (dyadicLeft j i + u))
          (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
            psi hpsiCompact j u q hq f))
        (q4L2FiniteFibreSynthesis s
          (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
            psi hpsiCompact j (dyadicLeft j i + u))
          (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
            psi hpsiCompact j u q hq f)) := by
  let G : Int -> Euclidean d -> Complex := q4PowerDualField q
    (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
      psi hpsiCompact j u f)
  let G2 : Int -> Lp Complex 2 (volume : Measure (Euclidean d)) :=
    q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
      psi hpsiCompact j u q hq f
  let P : Int -> Lp Complex 2 (volume : Measure (Euclidean d)) :=
    q4L2FiniteProductPairShell s
      (fun a b => q4ActiveDyadicScaledNormalizedDerivativePairL2Piece
        psi hpsiCompact j u a b) G2
  let S : Lp Complex 2 (volume : Measure (Euclidean d)) :=
    q4L2FiniteFibreSynthesis s
      (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
        psi hpsiCompact j (dyadicLeft j i + u)) G2
  have hout (i : Int) (hi : i ∈ s) :
      q4FiniteProductToFibres s
        (q4FiniteProductKernelShell volume s (fun _ _ => True)
          (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
          (q4FibresToFiniteProduct s G)) i =ᵐ[volume]
        (fun x : Euclidean d => ((P i : Lp Complex 2 volume) :
          Euclidean d -> Complex) x) := by
    simpa only [G, G2, P] using
      q4ActiveDyadicScaledNormalizedDerivativeSchwartzPowerDualFullKernel_ae_eq_l2PairShell
        psi hpsiCompact j u s q hq f i hi
  have hG (i : Int) : G i =ᵐ[volume]
      (fun x : Euclidean d => ((G2 i : Lp Complex 2 volume) :
        Euclidean d -> Complex) x) := by
    simpa only [G, G2] using
      (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2_coeFn_ae_eq
        psi hpsiCompact j u q hq f i).symm
  have hpair :
      q4FiniteProductKernelBilinear volume s (fun _ _ => True)
        (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) G G =
      ∑ i ∈ s, inner Complex (G2 i) (P i) := by
    unfold q4FiniteProductKernelBilinear
    calc
      q4FiniteProductPairing volume s
          (q4FiniteProductToFibres s
            (q4FiniteProductKernelShell volume s (fun _ _ => True)
              (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
              (q4FibresToFiniteProduct s G))) G =
          q4FiniteProductPairing volume s
            (fun i x => ((P i : Lp Complex 2 volume) :
              Euclidean d -> Complex) x) G := by
        apply q4FiniteProductPairing_congr_left_ae volume s
        exact hout
      _ = q4FiniteProductPairing volume s
            (fun i x => ((P i : Lp Complex 2 volume) :
              Euclidean d -> Complex) x)
            (fun i x => ((G2 i : Lp Complex 2 volume) :
              Euclidean d -> Complex) x) := by
        apply q4FiniteProductPairing_congr_right_ae volume s
        exact hG
      _ = ∑ i ∈ s, inner Complex (G2 i) (P i) :=
        q4FiniteProductPairing_l2_coeFn_eq_sum_inner volume s P G2
  have hdiag := q4L2FiniteFibreSynthesis_inner_self_eq_pairShell_diagonal s
    (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeL2Piece
      psi hpsiCompact j (dyadicLeft j i + u))
    (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
      psi hpsiCompact j (dyadicLeft j i + u))
    (fun a b => q4ActiveDyadicScaledNormalizedDerivativePairL2Piece
      psi hpsiCompact j u a b)
    (isQ4L2FiniteProductPairComposition_activeDyadicScaledNormalizedDerivative
      psi hpsiCompact j u)
    (isQ4L2FiniteProductFormalAdjoint_activeDyadicScaledNormalizedDerivative
      psi hpsiCompact j u) G2
  change q4FiniteProductKernelBilinear volume s (fun _ _ => True)
      (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) G G =
    inner Complex S S
  rw [hpair]
  simpa only [P, S] using hdiag.symm

/-- Pairing the literal derivative analysis family against its canonical
power dual is the completed-space adjoint pairing. -/
private theorem q4ActiveDyadicScaledNormalizedDerivative_analysisPairing_eq_l2
    {d : Nat} (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    (j : Nat) (u : Real) (s : Finset Int) (q : Real) (hq : 2 <= q)
    (f : SchwartzMap (Euclidean d) Complex) :
    q4FiniteProductPairing volume s
      (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
        psi hpsiCompact j u f)
      (q4PowerDualField q
        (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
          psi hpsiCompact j u f)) =
      inner Complex
        (q4L2FiniteFibreSynthesis s
          (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
            psi hpsiCompact j (dyadicLeft j i + u))
          (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
            psi hpsiCompact j u q hq f))
        (f.toLp 2 volume) := by
  let F : Int -> Euclidean d -> Complex :=
    q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
      psi hpsiCompact j u f
  let G : Int -> Euclidean d -> Complex := q4PowerDualField q F
  let G2 : Int -> Lp Complex 2 (volume : Measure (Euclidean d)) :=
    q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
      psi hpsiCompact j u q hq f
  let T : Int -> Lp Complex 2 (volume : Measure (Euclidean d)) ->L[Complex]
      Lp Complex 2 (volume : Measure (Euclidean d)) := fun i =>
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativeL2Piece
      psi hpsiCompact j (dyadicLeft j i + u)
  let Tstar : Int -> Lp Complex 2 (volume : Measure (Euclidean d)) ->L[Complex]
      Lp Complex 2 (volume : Measure (Euclidean d)) := fun i =>
    q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
      psi hpsiCompact j (dyadicLeft j i + u)
  have hF (i : Int) : F i =ᵐ[volume]
      (fun x : Euclidean d => ((T i (f.toLp 2 volume) :
        Lp Complex 2 volume) : Euclidean d -> Complex) x) := by
    have hpiece := q4ScaledNormalizedDyadicSurfaceRadiusDerivativeL2Piece_toLp_eq_schwartz
      psi hpsiCompact j (dyadicLeft j i + u) f
    rw [hpiece]
    filter_upwards [
      (q4ScaledNormalizedDyadicSurfaceRadiusDerivativeSchwartzPiece
        psi hpsiCompact j (dyadicLeft j i + u) f).coeFn_toLp] with x hx
    rw [hx]
    rfl
  have hG (i : Int) : G i =ᵐ[volume]
      (fun x : Euclidean d => ((G2 i : Lp Complex 2 volume) :
        Euclidean d -> Complex) x) := by
    simpa only [G, F, G2] using
      (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2_coeFn_ae_eq
        psi hpsiCompact j u q hq f i).symm
  have hpair : q4FiniteProductPairing volume s F G =
      ∑ i ∈ s, inner Complex (G2 i) (T i (f.toLp 2 volume)) := by
    calc
      q4FiniteProductPairing volume s F G =
          q4FiniteProductPairing volume s
            (fun i x => ((T i (f.toLp 2 volume) : Lp Complex 2 volume) :
              Euclidean d -> Complex) x) G := by
        apply q4FiniteProductPairing_congr_left_ae volume s
        exact hF
      _ = q4FiniteProductPairing volume s
            (fun i x => ((T i (f.toLp 2 volume) : Lp Complex 2 volume) :
              Euclidean d -> Complex) x)
            (fun i x => ((G2 i : Lp Complex 2 volume) :
              Euclidean d -> Complex) x) := by
        apply q4FiniteProductPairing_congr_right_ae volume s
        exact hG
      _ = ∑ i ∈ s, inner Complex (G2 i) (T i (f.toLp 2 volume)) :=
        q4FiniteProductPairing_l2_coeFn_eq_sum_inner volume s
          (fun i => T i (f.toLp 2 volume)) G2
  have hadj := q4L2FiniteProduct_formalAdjoint s T Tstar
    (by
      simpa only [T, Tstar] using
        isQ4L2FiniteProductFormalAdjoint_activeDyadicScaledNormalizedDerivative
          psi hpsiCompact j u)
    (f.toLp 2 volume) G2
  change q4FiniteProductPairing volume s F G =
    inner Complex (q4L2FiniteFibreSynthesis s Tstar G2) (f.toLp 2 volume)
  rw [hpair]
  exact hadj

/-- The literal full-product root estimate controls the completed synthesis
operator at a fixed offset.  This is the square-root step in the paper's
`TT*` argument: HÃ¶lder bounds the physical diagonal, while the exact
physical/`L²` identity turns that diagonal into a nonnegative square. -/
private theorem q4ActiveDyadicScaledNormalizedDerivative_synthesis_norm_le_of_fullProductRoot
    {d : Nat} (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    (j : Nat) (u : Real) (s : Finset Int) {q p A : Real}
    (hq : 1 < q) (hqtwo : 2 <= q) (hp : 0 < p)
    (hconj : 1 / q + 1 / p = 1) (hA : 0 <= A)
    (f : SchwartzMap (Euclidean d) Complex)
    (hout : ∀ i ∈ s, MemLp
      (q4FiniteProductToFibres s
        (q4FiniteProductKernelShell volume s (fun _ _ => True)
          (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
          (q4FibresToFiniteProduct s
            (q4PowerDualField q
              (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
                psi hpsiCompact j u f)))) i)
      (ENNReal.ofReal q) volume)
    (hinput : ∀ i ∈ s, MemLp
      (q4PowerDualField q
        (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
          psi hpsiCompact j u f) i)
      (ENNReal.ofReal p) volume)
    (hroot :
      (q4FibreLpMoment volume s q
        (q4FiniteProductToFibres s
          (q4FiniteProductKernelShell volume s (fun _ _ => True)
            (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
            (q4FibresToFiniteProduct s
              (q4PowerDualField q
                (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
                  psi hpsiCompact j u f)))))) ^ (1 / q) <=
        A * A *
          (q4FibreLpMoment volume s p
            (q4PowerDualField q
              (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
                psi hpsiCompact j u f))) ^ (1 / p)) :
    ‖q4L2FiniteFibreSynthesis s
      (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
        psi hpsiCompact j (dyadicLeft j i + u))
      (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
        psi hpsiCompact j u q hqtwo f)‖ <=
      A *
        (q4FibreLpMoment volume s p
          (q4PowerDualField q
            (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
              psi hpsiCompact j u f))) ^ (1 / p) := by
  let G : Int -> Euclidean d -> Complex := q4PowerDualField q
    (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
      psi hpsiCompact j u f)
  let Out : Int -> Euclidean d -> Complex := q4FiniteProductToFibres s
    (q4FiniteProductKernelShell volume s (fun _ _ => True)
      (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
      (q4FibresToFiniteProduct s G))
  let G2 : Int -> Lp Complex 2 (volume : Measure (Euclidean d)) :=
    q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
      psi hpsiCompact j u q hqtwo f
  let S : Lp Complex 2 (volume : Measure (Euclidean d)) :=
    q4L2FiniteFibreSynthesis s
      (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
        psi hpsiCompact j (dyadicLeft j i + u)) G2
  let R : Real := (q4FibreLpMoment volume s p G) ^ (1 / p)
  have hR : 0 <= R := by
    exact Real.rpow_nonneg (q4FibreLpMoment_nonneg volume s p G) _
  have hholder : ‖q4FiniteProductKernelBilinear volume s (fun _ _ => True)
      (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) G G‖ <=
      (q4FibreLpMoment volume s q Out) ^ (1 / q) * R := by
    unfold q4FiniteProductKernelBilinear
    simpa only [Out, R] using
      norm_q4FiniteProductPairing_le_fibreLpMoment volume s hq hp hconj Out G
        (by
          intro i hi
          simpa only [Out, G] using hout i hi)
        (by
          intro i hi
          simpa only [G] using hinput i hi)
  have hroot' : (q4FibreLpMoment volume s q Out) ^ (1 / q) <= A * A * R := by
    simpa only [Out, G, R] using hroot
  have hdiag : ‖q4FiniteProductKernelBilinear volume s (fun _ _ => True)
      (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) G G‖ <=
      (A * R) ^ (2 : Nat) := by
    calc
      ‖q4FiniteProductKernelBilinear volume s (fun _ _ => True)
          (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) G G‖ <=
          (q4FibreLpMoment volume s q Out) ^ (1 / q) * R := hholder
      _ <= (A * A * R) * R :=
        mul_le_mul_of_nonneg_right hroot' hR
      _ = (A * R) ^ (2 : Nat) := by ring
  have henergy :=
    q4ActiveDyadicScaledNormalizedDerivative_fullKernelDiagonal_eq_l2Energy
      psi hpsiCompact j u s q hqtwo f
  have henergy' : q4FiniteProductKernelBilinear volume s (fun _ _ => True)
      (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) G G =
      inner Complex S S := by
    simpa only [G, G2, S] using henergy
  have hdiag' : ‖inner Complex S S‖ <= (A * R) ^ (2 : Nat) := by
    rw [henergy'] at hdiag
    exact hdiag
  have hsq : ‖S‖ ^ (2 : Nat) <= (A * R) ^ (2 : Nat) := by
    simpa only [inner_self_eq_norm_sq_to_K, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hdiag'
  have hAR : 0 <= A * R := mul_nonneg hA hR
  nlinarith [norm_nonneg S, sq_nonneg (‖S‖ + A * R)]

/-- The literal stationary pair-kernel estimate and literal multiplier
bound give the fixed-offset strong finite-product estimate for the actual
scaled derivative family.  This is the `TT*` conclusion used below the
FTOC integral; it has no abstract operator, carrier, selected argmax, or
variation hypothesis in its statement. -/
theorem q4ActiveDyadicScaledNormalizedDerivative_analysis_rootMoment_le_of_canonical_fullProduct
    {d : Nat} (E : Set Real) (j : Nat) (u : Real)
    (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    {p q : Real} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (C : ENNReal) (hC : C ≠ ⊤)
    (f : SchwartzMap (Euclidean d) Complex)
    (hstrong :
      eLpNorm
        (q4FiniteProductKernelShell volume (activeDyadicIndices E j) (fun _ _ => True)
          (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
          (q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
            E j psi hpsiCompact u q f))
        (ENNReal.ofReal q) (q4ActiveDyadicProductCountingMeasure d E j) <=
      C * eLpNorm
        (q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
          E j psi hpsiCompact u q f)
        (ENNReal.ofReal p) (q4ActiveDyadicProductCountingMeasure d E j)) :
    (q4FibreLpMoment volume (activeDyadicIndices E j) q
      (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
        psi hpsiCompact j u f)) ^ (1 / q) <=
      Real.sqrt C.toReal *
        ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ := by
  let s : Finset Int := activeDyadicIndices E j
  have hqgtwo : 2 < q := by
    rw [hq]
    have hpminus : 0 < p - 1 := by linarith
    apply (lt_div_iff₀ hpminus).mpr
    nlinarith
  have hqtwo : 2 <= q := hqgtwo.le
  have hqone : 1 < q := lt_trans one_lt_two hqgtwo
  have hqpos : 0 < q := lt_trans zero_lt_two hqgtwo
  have hp : 0 < p := lt_trans zero_lt_one hp1
  have hmul : (q - 1) * p = q := by
    rw [hq]
    have hpminus : p - 1 ≠ 0 := ne_of_gt (by linarith [hp1])
    field_simp [hpminus]
    ring
  have hconj : 1 / q + 1 / p = 1 := by
    rw [hq]
    have hp0 : p ≠ 0 := ne_of_gt hp
    have hpminus : p - 1 ≠ 0 := ne_of_gt (by linarith [hp1])
    field_simp [hp0, hpminus]
    ring
  let Gproduct : Euclidean d × {i // i ∈ s} -> Complex :=
    q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
      E j psi hpsiCompact u q f
  let G : Int -> Euclidean d -> Complex := q4PowerDualField q
    (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
      psi hpsiCompact j u f)
  let A : Real := Real.sqrt C.toReal
  have hA : 0 <= A := Real.sqrt_nonneg _
  have hGmeas : Measurable Gproduct := by
    simpa only [s, Gproduct] using
      measurable_q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
        E j psi hpsiCompact u q hqtwo f
  have hGpower : Integrable (fun z => ‖Gproduct z‖ ^ p)
      (q4FiniteProductCountingMeasure volume s) := by
    simpa only [s, Gproduct] using
      integrable_norm_rpow_q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
        E j psi hpsiCompact u q p hqone hqtwo hp.le hmul f
  have hstrong' : eLpNorm
      (q4FiniteProductKernelShell volume s (fun _ _ => True)
        (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) Gproduct)
      (ENNReal.ofReal q) (q4FiniteProductCountingMeasure volume s) <=
      C * eLpNorm Gproduct (ENNReal.ofReal p)
        (q4FiniteProductCountingMeasure volume s) := by
    simpa only [s, Gproduct] using hstrong
  have houtmeas : AEStronglyMeasurable
      (q4FiniteProductKernelShell volume s (fun _ _ => True)
        (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) Gproduct)
      (q4FiniteProductCountingMeasure volume s) := by
    simpa only [s, Gproduct] using
      aestronglyMeasurable_q4ActiveDyadicScaledNormalizedDerivativeFullKernelPowerDualProduct
        E j psi hpsiCompact u q hqtwo f
  have hout : ∀ i ∈ s, MemLp
      (q4FiniteProductToFibres s
        (q4FiniteProductKernelShell volume s (fun _ _ => True)
          (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
          (q4FibresToFiniteProduct s G))) i)
      (ENNReal.ofReal q) volume := by
    intro i hi
    have hmem :=
      memLp_q4FiniteProductToFibres_of_product_eLpNorm_aestronglyMeasurable
        volume s
        (q4FiniteProductKernelShell volume s (fun _ _ => True)
          (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) Gproduct)
        Gproduct hqpos hp C hC houtmeas hGmeas hGpower hstrong' i hi
    simpa only [G, Gproduct,
      q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField,
      q4FiniteProductToFibres_q4FibresToFiniteProduct_apply] using hmem
  have hinput : ∀ i ∈ s, MemLp (G i) (ENNReal.ofReal p) volume := by
    intro i hi
    have hmeas : Measurable (G i) := by
      simpa only [G] using
        (q4PowerDualField_mem_Q4PhysicalDualCarrier q hqtwo
          (fun k => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeSchwartzPiece
            psi hpsiCompact j (dyadicLeft j k + u) f) i).2.2.1.measurable
    apply (integrable_norm_rpow_iff hmeas.aestronglyMeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mp
    have hpow := integrable_norm_rpow_q4FiniteProductToFibres_of_integrable
      volume s Gproduct hGpower i hi
    rw [q4FiniteProductToFibres_q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
      E j psi hpsiCompact u q f i hi] at hpow
    simpa only [G, ENNReal.toReal_ofReal hp.le] using hpow
  have hroot :
      (q4FibreLpMoment volume s q
        (q4FiniteProductToFibres s
          (q4FiniteProductKernelShell volume s (fun _ _ => True)
            (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
            (q4FibresToFiniteProduct s G)))) ^ (1 / q) <=
        A * A * (q4FibreLpMoment volume s p G) ^ (1 / p) := by
    simpa only [s, G, A] using
      q4ActiveDyadicScaledNormalizedDerivativeCanonicalFullProduct_rootMoment_le_of_eLpStrongENNReal_sq
        E j psi hpsiCompact u q p hqone hqtwo hp hmul C hC f hstrong
  have hS := q4ActiveDyadicScaledNormalizedDerivative_synthesis_norm_le_of_fullProductRoot
    psi hpsiCompact j u s hqone hqtwo hp hconj hA f hout hinput hroot
  have hpair := q4ActiveDyadicScaledNormalizedDerivative_analysisPairing_eq_l2
    psi hpsiCompact j u s q hqtwo f
  let F : Int -> Euclidean d -> Complex :=
    q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
      psi hpsiCompact j u f
  let R : Real := (q4FibreLpMoment volume s p G) ^ (1 / p)
  have hbilinear : ‖q4FiniteProductPairing volume s F (q4PowerDualField q F)‖ <=
      A * ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ * R := by
    calc
      ‖q4FiniteProductPairing volume s F (q4PowerDualField q F)‖ =
          ‖inner Complex
            (q4L2FiniteFibreSynthesis s
              (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
                psi hpsiCompact j (dyadicLeft j i + u))
              (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
                psi hpsiCompact j u q hqtwo f))
            ((f.memLp 2 volume).toLp (f : Euclidean d -> Complex))‖ := by
        rw [show F = q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
          psi hpsiCompact j u f by rfl]
        exact congrArg norm hpair
      _ <= ‖q4L2FiniteFibreSynthesis s
            (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
              psi hpsiCompact j (dyadicLeft j i + u))
            (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
              psi hpsiCompact j u q hqtwo f)‖ *
          ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ :=
        norm_inner_le_norm _ _
      _ <= (A * R) * ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ :=
        mul_le_mul_of_nonneg_right (by simpa only [G, R] using hS) (norm_nonneg _)
      _ = A * ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ * R := by ring
  have hCF : 0 <= A * ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ :=
    mul_nonneg hA (norm_nonneg _)
  have hmoment := q4FibreLpMoment_rpow_one_div_le_of_dual_test_at_test
    volume s hqpos hp hconj hCF F
    (q4PowerDualTest volume s q p F hqone hmul) (by
      simpa only [G, F, R] using hbilinear)
  simpa only [s, F, A] using hmoment

/-- The literal stationary pair-kernel estimate and literal multiplier
bound give the fixed-offset strong finite-product estimate for the actual
scaled derivative family.  This is the `TT*` conclusion used below the
FTOC integral; it has no abstract operator, carrier, selected argmax, or
variation hypothesis in its statement. -/
theorem q4ActiveDyadicScaledNormalizedDerivative_analysis_rootMoment_le_of_active_multiplier
    {d : Nat} {E : Set Real} {gamma eta Ccover : Real} {j : Nat}
    (hd : 1 <= d) (hj : 1 <= j)
    (hE : E ⊆ Icc (1 : Real) 2)
    (hcover : HasSubpowerAssouadCoverBound E gamma eta Ccover)
    (hCcover : 0 <= Ccover) (hgamma : 0 <= gamma)
    (hdeltaone : dyadicScale j < 1)
    (u : Real) (hu : u ∈ Icc (0 : Real) (dyadicScale j))
    (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    {Ckernel B : Real} (hCkernel : 0 < Ckernel)
    (hdecay : HasQ4ScaledNormalizedDyadicSurfaceRadiusDerivativePairKernelGapDecayOn
      d (fun _ => psi) (1 / 2 : Real) (5 / 2) Ckernel)
    (hB : 0 <= B)
    (hmultiplier : forall i ∈ activeDyadicIndices E j,
      forall l ∈ activeDyadicIndices E j, forall xi : Euclidean d,
        ‖q4ActiveDyadicScaledNormalizedDerivativePairMultiplier
          psi hpsiCompact j u i l xi‖ <= B)
    {p q : Real} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : SchwartzMap (Euclidean d) Complex) :
    (q4FibreLpMoment volume (activeDyadicIndices E j) q
      (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
        psi hpsiCompact j u f)) ^ (1 / q) <=
      Real.sqrt
        (∑ n ∈ Finset.range (j + 3),
          q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q).toReal *
        ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ := by
  let s : Finset Int := activeDyadicIndices E j
  have hqgtwo : 2 < q := by
    rw [hq]
    have hpminus : 0 < p - 1 := by linarith
    apply (lt_div_iff₀ hpminus).mpr
    nlinarith
  have hqtwo : 2 <= q := hqgtwo.le
  have hqpos : 0 < q := lt_trans zero_lt_two hqgtwo
  have hp : 0 < p := lt_trans zero_lt_one hp1
  have hmul : (q - 1) * p = q := by
    rw [hq]
    have hpminus : p - 1 ≠ 0 := ne_of_gt (by linarith [hp1])
    field_simp [hpminus]
    ring
  have hconj : 1 / q + 1 / p = 1 := by
    rw [hq]
    have hp0 : p ≠ 0 := ne_of_gt hp
    have hpminus : p - 1 ≠ 0 := ne_of_gt (by linarith [hp1])
    field_simp [hp0, hpminus]
    ring
  let Gproduct : Euclidean d × {i // i ∈ s} -> Complex :=
    q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
      E j psi hpsiCompact u q f
  let G : Int -> Euclidean d -> Complex := q4PowerDualField q
    (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
      psi hpsiCompact j u f)
  let L : ENNReal := ∑ n ∈ Finset.range (j + 3),
    q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q
  let A : Real := Real.sqrt L.toReal
  have hL : L ≠ ⊤ := by
    simpa only [L] using q4ActiveDyadicLevelStrongConstant_sum_ne_top hqgtwo
  have hA : 0 <= A := by
    exact Real.sqrt_nonneg _
  have hGmeas : Measurable Gproduct := by
    simpa only [s, Gproduct] using
      measurable_q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
        E j psi hpsiCompact u q hqtwo f
  have hGint : Integrable Gproduct (q4FiniteProductCountingMeasure volume s) := by
    simpa only [s, Gproduct] using
      integrable_q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
        E j psi hpsiCompact u q hqtwo f
  have hGsq : Integrable (fun z => ‖Gproduct z‖ ^ (2 : Nat))
      (q4FiniteProductCountingMeasure volume s) := by
    simpa only [s, Gproduct] using
      integrable_norm_sq_q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
        E j psi hpsiCompact u q hqtwo f
  have hGfib : ∀ i ∈ s,
      Integrable (q4FiniteProductToFibres s Gproduct i) volume ∧
        MemLp (q4FiniteProductToFibres s Gproduct i) 2 volume := by
    intro i hi
    simpa only [s, Gproduct] using
      q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField_fibre_regular
        E j psi hpsiCompact u q hqtwo f i hi
  have hGpower : Integrable (fun z => ‖Gproduct z‖ ^ p)
      (q4FiniteProductCountingMeasure volume s) := by
    simpa only [s, Gproduct] using
      integrable_norm_rpow_q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
        E j psi hpsiCompact u q p (lt_trans one_lt_two hqgtwo)
          hqtwo hp.le hmul f
  have hfull : eLpNorm
      (fun z => ‖q4FiniteProductKernelShell volume s (fun _ _ => True)
        (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) Gproduct z‖)
      (ENNReal.ofReal q) (q4FiniteProductCountingMeasure volume s) <=
      L * eLpNorm Gproduct (ENNReal.ofReal p)
        (q4FiniteProductCountingMeasure volume s) := by
    simpa only [s, Gproduct, L] using
      q4ActiveDyadicScaledNormalizedDerivativeFullProductPairShell_eLpNorm_le_levelSum_of_active_multiplier_homogeneous
        hd hj hE hcover hCcover hgamma hdeltaone u hu psi hpsiCompact hCkernel hdecay hB
        hmultiplier hp1 hp2 hq Gproduct hGmeas hGint hGsq hGfib hGpower rfl
  have hfull' : eLpNorm
      (q4FiniteProductKernelShell volume s (fun _ _ => True)
        (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) Gproduct)
      (ENNReal.ofReal q) (q4FiniteProductCountingMeasure volume s) <=
      L * eLpNorm Gproduct (ENNReal.ofReal p)
        (q4FiniteProductCountingMeasure volume s) := by
    simpa only [eLpNorm_norm] using hfull
  have houtmeas : AEStronglyMeasurable
      (q4FiniteProductKernelShell volume s (fun _ _ => True)
        (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) Gproduct)
      (q4FiniteProductCountingMeasure volume s) := by
    simpa only [s, Gproduct] using
      aestronglyMeasurable_q4ActiveDyadicScaledNormalizedDerivativeFullKernelPowerDualProduct
        E j psi hpsiCompact u q hqtwo f
  have hout : ∀ i ∈ s, MemLp
      (q4FiniteProductToFibres s
        (q4FiniteProductKernelShell volume s (fun _ _ => True)
          (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
          (q4FibresToFiniteProduct s G)))
      (ENNReal.ofReal q) volume := by
    intro i hi
    have hmem :=
      memLp_q4FiniteProductToFibres_of_product_eLpNorm_aestronglyMeasurable
        volume s
        (q4FiniteProductKernelShell volume s (fun _ _ => True)
          (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u) Gproduct)
        Gproduct hqpos hp L hL houtmeas hGmeas hGpower hfull' i hi
    simpa only [G, Gproduct,
      q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField,
      q4FiniteProductToFibres_q4FibresToFiniteProduct_apply] using hmem
  have hinput : ∀ i ∈ s, MemLp (G i) (ENNReal.ofReal p) volume := by
    intro i hi
    have hmeas : Measurable (G i) := by
      simpa only [G] using
        (q4PowerDualField_mem_Q4PhysicalDualCarrier q hqtwo
          (fun k => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeSchwartzPiece
            psi hpsiCompact j (dyadicLeft j k + u) f) i).2.2.1.measurable
    apply (integrable_norm_rpow_iff hmeas.aestronglyMeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mp
    have hpow := integrable_norm_rpow_q4FiniteProductToFibres_of_integrable
      volume s Gproduct hGpower i hi
    rw [q4FiniteProductToFibres_q4ActiveDyadicScaledNormalizedDerivativePowerDualProductField
      E j psi hpsiCompact u q f i hi] at hpow
    simpa only [G, ENNReal.toReal_ofReal hp.le] using hpow
  have hroot :
      (q4FibreLpMoment volume s q
        (q4FiniteProductToFibres s
          (q4FiniteProductKernelShell volume s (fun _ _ => True)
            (q4ActiveDyadicScaledNormalizedDerivativePairKernel psi j u)
            (q4FibresToFiniteProduct s G)))) ^ (1 / q) <=
        A * A * (q4FibreLpMoment volume s p G) ^ (1 / p) := by
    simpa only [s, G, L, A] using
      q4ActiveDyadicScaledNormalizedDerivativeCanonicalFullProduct_rootMoment_le_of_active_multiplier
        hd hj hE hcover hCcover hgamma hdeltaone u hu psi hpsiCompact hCkernel hdecay hB
          hmultiplier hp1 hp2 hq f
  have hS := q4ActiveDyadicScaledNormalizedDerivative_synthesis_norm_le_of_fullProductRoot
    psi hpsiCompact j u s hq hqtwo hp hconj hA f hout hinput hroot
  have hpair := q4ActiveDyadicScaledNormalizedDerivative_analysisPairing_eq_l2
    psi hpsiCompact j u s q hqtwo f
  let F : Int -> Euclidean d -> Complex :=
    q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
      psi hpsiCompact j u f
  let R : Real := (q4FibreLpMoment volume s p G) ^ (1 / p)
  have hbilinear : ‖q4FiniteProductPairing volume s F (q4PowerDualField q F)‖ <=
      A * ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ * R := by
    calc
      ‖q4FiniteProductPairing volume s F (q4PowerDualField q F)‖ =
          ‖inner Complex
            (q4L2FiniteFibreSynthesis s
              (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
                psi hpsiCompact j (dyadicLeft j i + u))
              (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
                psi hpsiCompact j u q hqtwo f))
            ((f.memLp 2 volume).toLp (f : Euclidean d -> Complex))‖ := by
        rw [show F = q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
          psi hpsiCompact j u f by rfl]
        exact congrArg norm hpair
      _ <= ‖q4L2FiniteFibreSynthesis s
            (fun i => q4ScaledNormalizedDyadicSurfaceRadiusDerivativeAdjointL2Piece
              psi hpsiCompact j (dyadicLeft j i + u))
            (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisPowerDualL2
              psi hpsiCompact j u q hqtwo f)‖ *
          ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ :=
        norm_inner_le_norm _ _
      _ <= (A * R) * ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ :=
        mul_le_mul_of_nonneg_right (by simpa only [G, R] using hS) (norm_nonneg _)
      _ = A * ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ * R := by ring
  have hCF : 0 <= A * ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ :=
    mul_nonneg hA (norm_nonneg _)
  have hmoment := q4FibreLpMoment_rpow_one_div_le_of_dual_test_at_test
    volume s hqpos hp hconj hCF F
    (q4PowerDualTest volume s q p F (lt_trans one_lt_two hqgtwo) hmul) (by
      simpa only [G, F, R] using hbilinear)
  simpa only [s, F, L, A] using hmoment

/-- The fixed-offset `L² → L^q` estimate for the actual finite active
maximum of scaled derivatives.  The supremum is the finite maximum itself,
not a measurable selector; finite-max integrability is supplied directly by
the Schwartz pieces. -/
theorem q4ActiveDyadicScaledDerivativeSup_rootMoment_le_of_active_multiplier
    {d : Nat} {E : Set Real} {gamma eta Ccover : Real} {j : Nat}
    (hd : 1 <= d) (hj : 1 <= j)
    (hE : E ⊆ Icc (1 : Real) 2)
    (hcover : HasSubpowerAssouadCoverBound E gamma eta Ccover)
    (hCcover : 0 <= Ccover) (hgamma : 0 <= gamma)
    (hdeltaone : dyadicScale j < 1)
    (hs : (activeDyadicIndices E j).Nonempty)
    (u : Real) (hu : u ∈ Icc (0 : Real) (dyadicScale j))
    (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    {Ckernel B : Real} (hCkernel : 0 < Ckernel)
    (hdecay : HasQ4ScaledNormalizedDyadicSurfaceRadiusDerivativePairKernelGapDecayOn
      d (fun _ => psi) (1 / 2 : Real) (5 / 2) Ckernel)
    (hB : 0 <= B)
    (hmultiplier : forall i ∈ activeDyadicIndices E j,
      forall l ∈ activeDyadicIndices E j, forall xi : Euclidean d,
        ‖q4ActiveDyadicScaledNormalizedDerivativePairMultiplier
          psi hpsiCompact j u i l xi‖ <= B)
    {p q : Real} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : SchwartzMap (Euclidean d) Complex) :
    (integral fun x : Euclidean d =>
      activeDyadicDerivativeSup E j hs
        (fun t => q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j t x) u ^ q) ^
      (1 / q) <=
      Real.sqrt
        (∑ n ∈ Finset.range (j + 3),
          q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q).toReal *
        ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ := by
  let s : Finset Int := activeDyadicIndices E j
  let pieces : Int -> Euclidean d -> Complex := fun i x =>
    q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j (dyadicLeft j i + u) x
  have hqgtwo : 2 < q := by
    rw [hq]
    have hpminus : 0 < p - 1 := by linarith
    apply (lt_div_iff₀ hpminus).mpr
    nlinarith
  have hqpos : 0 < q := lt_trans zero_lt_two hqgtwo
  have hfibre : ∀ i ∈ s, Integrable (fun x => ‖pieces i x‖ ^ q) volume := by
    intro i hi
    simpa only [pieces] using
      integrable_norm_q4ScaledNormalizedDyadicSurfaceRadiusDerivative_rpow_of_schwartz
        psi hpsiCompact j (dyadicLeft j i + u) f hqpos
  have hmax : Integrable (fun x => q4FiniteProductMaximal s hs pieces x ^ q) volume := by
    simpa only [s, pieces, q4FiniteProductMaximal,
      activeDyadicDerivativeSup, dyadicDerivativeSup] using
      integrable_activeDyadicScaledDerivativeSup_rpow_of_schwartz
        E j hs psi hpsiCompact f u hqpos
  have hmomentAnalysis :=
    q4ActiveDyadicScaledNormalizedDerivative_analysis_rootMoment_le_of_active_multiplier
      hd hj hE hcover hCcover hgamma hdeltaone u hu psi hpsiCompact hCkernel hdecay hB
        hmultiplier hp1 hp2 hq f
  have hmomentPieces :
      (q4FibreLpMoment volume s q pieces) ^ (1 / q) <=
        Real.sqrt
          (∑ n ∈ Finset.range (j + 3),
            q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q).toReal *
          ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖ := by
    rw [show q4FibreLpMoment volume s q pieces =
        q4FibreLpMoment volume s q
          (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
            psi hpsiCompact j u f) by
      unfold q4FibreLpMoment
      apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      filter_upwards with x
      rw [show pieces i x =
          q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField
            psi hpsiCompact j u f i x by
          simpa only [pieces] using
            (q4ActiveDyadicScaledNormalizedDerivativeSchwartzAnalysisField_apply_eq
              psi hpsiCompact j u f i x).symm]]
    simpa only [s] using hmomentAnalysis
  have hmaxroot := q4FiniteProductMaximal_moment_le_of_fibreLpMoment
    volume s hs q pieces hqpos hmomentPieces hmax hfibre
  simpa only [s, pieces, q4FiniteProductMaximal,
    activeDyadicDerivativeSup, dyadicDerivativeSup] using hmaxroot

/-- The literal FTOC derivative correction obeys the dyadic `L^q` estimate
coming from the stationary pair-kernel and Fourier multiplier bounds.  The
finite active supremum is jointly continuous, its product integrability is
proved by Tonelli, and the fixed-offset estimate above supplies the only
analytic bound; thus neither a variation hypothesis nor a selector
measurability hypothesis is exposed. -/
theorem q4ActiveDyadicScaledDerivativeVariationTerm_eLpNorm_le_of_active_multiplier
    {d : Nat} {E : Set Real} {gamma eta Ccover : Real} {j : Nat}
    (hd : 1 <= d) (hj : 1 <= j)
    (hE : E ⊆ Icc (1 : Real) 2)
    (hcover : HasSubpowerAssouadCoverBound E gamma eta Ccover)
    (hCcover : 0 <= Ccover) (hgamma : 0 <= gamma)
    (hdeltaone : dyadicScale j < 1)
    (hs : (activeDyadicIndices E j).Nonempty)
    (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    {Ckernel B : Real} (hCkernel : 0 < Ckernel)
    (hdecay : HasQ4ScaledNormalizedDyadicSurfaceRadiusDerivativePairKernelGapDecayOn
      d (fun _ => psi) (1 / 2 : Real) (5 / 2) Ckernel)
    (hB : 0 <= B)
    (hmultiplier : forall u ∈ Icc (0 : Real) (dyadicScale j),
      forall i ∈ activeDyadicIndices E j,
      forall l ∈ activeDyadicIndices E j, forall xi : Euclidean d,
        ‖q4ActiveDyadicScaledNormalizedDerivativePairMultiplier
          psi hpsiCompact j u i l xi‖ <= B)
    {p q : Real} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : SchwartzMap (Euclidean d) Complex) :
    MemLp (q4ActiveDyadicScaledDerivativeVariationTerm E j hs psi f)
      (ENNReal.ofReal q) volume ∧
      eLpNorm (q4ActiveDyadicScaledDerivativeVariationTerm E j hs psi f)
        (ENNReal.ofReal q) volume <=
        ENNReal.ofReal
          (dyadicScale j *
            (Real.sqrt
              (∑ n ∈ Finset.range (j + 3),
                q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q).toReal *
              ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖)) := by
  let L : ENNReal := ∑ n ∈ Finset.range (j + 3),
    q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q
  let A : Real := Real.sqrt L.toReal *
    ‖(f.memLp 2 volume).toLp (f : Euclidean d -> Complex)‖
  have hqgtwo : 2 < q := by
    rw [hq]
    have hpminus : 0 < p - 1 := by linarith
    apply (lt_div_iff₀ hpminus).mpr
    nlinarith
  have hqone : 1 < q := lt_trans one_lt_two hqgtwo
  have hA : 0 <= A := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply q4ActiveDyadicScaledDerivativeVariationTerm_eLpNorm_le_of_uniform_root_bound
    E j hs psi f hqone hA
  · intro u hu
    exact integrable_activeDyadicScaledDerivativeSup_rpow_of_schwartz
      E j hs psi hpsiCompact f u (lt_trans zero_lt_one hqone)
  · intro u hu
    have hu' : u ∈ Icc (0 : Real) (dyadicScale j) := ⟨hu.1.le, hu.2⟩
    have hroot := q4ActiveDyadicScaledDerivativeSup_rootMoment_le_of_active_multiplier
      hd hj hE hcover hCcover hgamma hdeltaone hs u hu' psi hpsiCompact hCkernel hdecay hB
      (hmultiplier u hu') hp1 hp2 hq f
    simpa only [L, A] using hroot

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
