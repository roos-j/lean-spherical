/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4PhysicalL2Extension
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4SelectedCutoffDomain
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4MeasurableEndpointCrossed

/-!
# Literal active-dyadic pairwise `L²` bounds

This file turns the Fourier multiplier estimate for an actual active-dyadic
pair into the `L¹ ∩ L²` physical-kernel bound consumed by the selected-shell
argument.  The bridge is the proved a.e. equality between the literal
Bochner convolution and the completed Fourier multiplier; it does not
replace the physical shell by an abstract Hilbert-space operator.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory

noncomputable section

/-- A uniform Fourier multiplier bound supplies the physical pairwise `L²`
endpoint for the literal active-dyadic kernel.  The input is kept in
`L¹ ∩ L²`: `L¹` is what makes the displayed convolution a literal Bochner
integral, and `L²` is what lets the completed Plancherel multiplier act. -/
noncomputable def q4ActiveDyadicPairwiseL2OperatorBound_of_multiplier_bound
    {d : Nat} (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    (j : Nat) {B : Real} (hB : 0 <= B)
    (hmultiplier : forall (i l : Int) (xi : Euclidean d),
      ‖q4ActiveDyadicPairMultiplier psi hpsiCompact j i l xi‖ <= B) :
    Q4PairwiseL2OperatorBound volume (q4ActiveDyadicPairKernel psi j) := by
  refine
    { B := B
      nonneg := hB
      memLp := ?_
      bound := ?_ }
  · intro i l g hg1 hg2
    have htarget : MemLp
        (fun x : Euclidean d =>
          ((q4ActiveDyadicPairL2Piece psi hpsiCompact j i l (hg2.toLp g) :
            Lp Complex 2 (volume : Measure (Euclidean d))) :
            Euclidean d -> Complex) x) 2 volume :=
      Lp.memLp _
    exact htarget.congr_ae
      (q4ActiveDyadicPairKernelApply_ae_eq_l2Piece psi hpsiCompact j i l g hg1 hg2).symm
  · intro i l g hg1 hg2
    let T : Lp Complex 2 (volume : Measure (Euclidean d)) :=
      q4ActiveDyadicPairL2Piece psi hpsiCompact j i l (hg2.toLp g)
    have hphysical : q4PairwiseKernelApply volume
        (q4ActiveDyadicPairKernel psi j) i l g =ᵐ[volume]
        (fun x : Euclidean d => (T : Euclidean d -> Complex) x) := by
      simpa only [T] using
        q4ActiveDyadicPairKernelApply_ae_eq_l2Piece psi hpsiCompact j i l g hg1 hg2
    have hphysicalMem : MemLp
        (q4PairwiseKernelApply volume (q4ActiveDyadicPairKernel psi j) i l g) 2 volume := by
      have hTmem : MemLp (fun x : Euclidean d =>
          (T : Euclidean d -> Complex) x) 2 volume := Lp.memLp _
      exact hTmem.congr_ae hphysical.symm
    have hTbound : ‖T‖ <= B * ‖hg2.toLp g‖ := by
      dsimp only [T]
      exact norm_q4ActiveDyadicPairL2Piece_apply_le_of_bound
        psi hpsiCompact j i l hB (hmultiplier i l) (hg2.toLp g)
    calc
      lpNorm (q4PairwiseKernelApply volume
          (q4ActiveDyadicPairKernel psi j) i l g) 2 volume =
          (eLpNorm (q4PairwiseKernelApply volume
            (q4ActiveDyadicPairKernel psi j) i l g) 2 volume).toReal :=
        (toReal_eLpNorm hphysicalMem.aestronglyMeasurable).symm
      _ = (eLpNorm (fun x : Euclidean d =>
          (T : Euclidean d -> Complex) x) 2 volume).toReal := by
        rw [eLpNorm_congr_ae hphysical]
      _ = ‖T‖ := by
        exact (Lp.norm_def T).symm
      _ <= B * ‖hg2.toLp g‖ := hTbound
      _ = B * lpNorm g 2 volume := by
        rw [Lp.norm_toLp, toReal_eLpNorm hg2.aestronglyMeasurable]

/-- Ordinary measurable `L¹ ∩ L²` data belong to every literal selected
active-dyadic shell domain.  Pairwise Bochner integrability is not an extra
endpoint assumption: it follows from the compact Schwartz realization of
the actual kernel and integrability of each measurable selector fibre. -/
theorem mem_q4SelectedCutoffStableDomain_activeDyadic_of_regular
    {d : Nat} (E : Set Real) (j : Nat)
    (R : Int -> Int -> Prop) [DecidableRel R]
    (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    (rho : Euclidean d -> Int) (hrhoMeas : Measurable rho)
    (g : Euclidean d -> Complex)
    (hgmeas : Measurable g) (hgint : Integrable g volume)
    (hgL2 : MemLp g 2 volume) :
    g ∈ q4SelectedCutoffStableDomain volume (activeDyadicIndices E j) R
      (q4ActiveDyadicPairKernel psi j) rho := by
  apply mem_q4SelectedCutoffStableDomain
    volume (activeDyadicIndices E j) R (q4ActiveDyadicPairKernel psi j) rho
    g hgmeas hgint hgL2
  intro i l x
  exact integrable_q4ActiveDyadicPairKernel_mul_q4SelectedFibre_of_compact
    psi hpsiCompact j rho g
    (fun k =>
      integrable_q4SelectedFibre_of_measurable_selector rho hrhoMeas g hgint k)
    i l x

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
