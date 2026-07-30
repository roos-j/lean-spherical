/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4ActiveDiagonalShell
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4ActiveProductReassembly

/-!
# Reassembly of the actual active selected `Q4` shell

The full active finite-radius kernel is exactly the sum of its canonical gap
levels.  This file applies the genuine diagonal and positive-shell estimates
to that finite sum.  There are no abstract endpoint hypotheses: physical
`L¹ ∩ L²` membership, pairwise Fourier `L²`, the stationary bound, and the
upper-spectrum count are each instantiated in the proof.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set ENNReal
open scoped BigOperators

noncomputable section

/-- The levelwise strong constant in the exact finite canonical
decomposition.  The `if` is genuine: level zero is diagonal and all other
levels use the positive radius-gap bound. -/
def q4ActiveDyadicLevelStrongConstant
    (d : Nat) (gamma eta Ccover Ckernel B : Real) (j n : Nat) (q : Real) : ENNReal :=
  if n = 0 then q4ActiveDyadicDiagonalStrongConstant Ckernel B j q else
    q4ActiveDyadicPositiveGapStrongConstant d gamma eta Ccover Ckernel B j n q

/-- The actual selected full active-dyadic kernel has the finite levelwise
strong bound obtained by summing the diagonal and positive literal shells.
The left-hand operator uses the unrestricted relation on the active finite
family; `q4SelectedKernelTTStarShell_full_eq_activeDyadicRelation` proves it
is exactly the active finite product before the canonical decomposition.

This is deliberately a finite-frequency statement.  The separate strict
exponent calculation turns the displayed finite sum of constants into a
geometric dyadic gain before frequencies are reassembled. -/
theorem q4ActiveDyadicFullSelectedPairShell_eLpNorm_le_levelSum
    {d : Nat} {E : Set Real} {gamma eta Ccover : Real} {j : Nat}
    (hd : 1 <= d) (hj : 1 <= j)
    (hE : E ⊆ Icc (1 : Real) 2)
    (hcover : HasSubpowerAssouadCoverBound E gamma eta Ccover)
    (hCcover : 0 <= Ccover) (hgamma : 0 <= gamma)
    (hdeltaone : dyadicScale j < 1)
    (Psi : Nat -> SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport ((Psi j : SchwartzMap (Euclidean d) Complex) :
      Euclidean d -> Complex))
    {Ckernel B : Real} (hCkernel : 0 < Ckernel)
    (hdecay : HasQ4DyadicPairKernelGapDecayOn d Psi
      (1 / 2 : Real) (5 / 2) Ckernel)
    (hB : 0 <= B)
    (hmultiplier : forall (i l : Int) (xi : Euclidean d),
      ‖q4ActiveDyadicPairMultiplier (Psi j) hpsiCompact j i l xi‖ <= B)
    (rho : Euclidean d -> Int)
    (hrho : forall x, rho x ∈ activeDyadicIndices E j)
    (hrhoMeas : Measurable rho)
    {p q I0 : Real} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : Euclidean d -> Complex)
    (hfmeas : Measurable f) (hfint : Integrable f volume)
    (hfL2 : MemLp f 2 volume)
    (hfp : Integrable (fun x => ‖f x‖ ^ p) volume)
    (hI0 : I0 = ∫ x, ‖f x‖ ^ p) (hI0pos : 0 < I0) :
    eLpNorm (fun x => ‖q4SelectedKernelTTStarShell volume
      (activeDyadicIndices E j) (fun _ _ => True)
      (q4ActiveDyadicPairKernel (Psi j) j) rho f x‖) (ENNReal.ofReal q) volume <=
      ((∑ n ∈ Finset.range (j + 3),
        q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q) *
          eLpNorm f (ENNReal.ofReal p) volume) := by
  let K : Int -> Int -> Euclidean d -> Complex := q4ActiveDyadicPairKernel (Psi j) j
  let H := q4ActiveDyadicPairwiseL2OperatorBound_of_multiplier_bound
    (Psi j) hpsiCompact j hB hmultiplier
  let R : Int -> Int -> Prop := q4ActiveDyadicProductRelation E j
  let level : Int -> Int -> Nat := activeDyadicGapLevel
  have hqtwo : 2 < q := by
    rw [hq]
    have hpminus : 0 < p - 1 := by linarith
    apply (lt_div_iff₀ hpminus).mpr
    nlinarith
  have hqone : 1 <= ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hdomain (n : Nat) : f ∈ q4SelectedCutoffStableDomain volume
      (activeDyadicIndices E j) (q4LevelShellRelation R level n) K rho := by
    exact mem_q4SelectedCutoffStableDomain_activeDyadic_of_regular
      E j (q4LevelShellRelation R level n) (Psi j) hpsiCompact rho hrhoMeas f
      hfmeas hfint hfL2
  have hmeas (n : Nat) : AEStronglyMeasurable (fun x =>
      ‖q4SelectedKernelTTStarShell volume (activeDyadicIndices E j)
        (q4LevelShellRelation R level n) K rho f x‖) volume := by
    exact (memLp_two_q4SelectedKernelTTStarShell_of_pairwise_bound
      (activeDyadicIndices E j) (q4LevelShellRelation R level n) K rho hrho
      hrhoMeas H f (hdomain n)).aestronglyMeasurable.norm
  have hreassembly := eLpNorm_norm_q4SelectedKernelTTStarShell_le_sum_levelShells
    volume (activeDyadicIndices E j) R level (Finset.range (j + 3))
    (by
      intro i l hactive
      exact activeDyadicGapLevel_mem_range_add_three hj hE hactive.1 hactive.2)
    K rho f hqone
    (fun n hn => hmeas n)
  have hlevels : ∀ n ∈ Finset.range (j + 3),
      eLpNorm (fun x => ‖q4SelectedKernelTTStarShell volume
        (activeDyadicIndices E j) (q4LevelShellRelation R level n) K rho f x‖)
        (ENNReal.ofReal q) volume <=
        q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q *
          eLpNorm f (ENNReal.ofReal p) volume := by
    intro n hn
    by_cases hnzero : n = 0
    · subst n
      rw [q4ActiveDyadicLevelStrongConstant, if_pos rfl, eLpNorm_norm]
      exact q4ActiveDyadicDiagonalSelectedPairShell_strong_offDiagonal
        hj hE Psi hpsiCompact hCkernel hdecay hB hmultiplier rho hrho hrhoMeas
        hp1 hp2 hq f (hdomain 0) hfp hI0 hI0pos
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
      rw [q4ActiveDyadicLevelStrongConstant, if_neg hnzero, eLpNorm_norm]
      exact q4ActiveDyadicPositiveSelectedPairShell_strong_offDiagonal
        hd hj hE hcover hCcover hgamma hdeltaone hnpos
        Psi hpsiCompact hCkernel hdecay hB hmultiplier rho hrho hrhoMeas
        hp1 hp2 hq f (hdomain n) hfp hI0 hI0pos
  calc
    eLpNorm (fun x => ‖q4SelectedKernelTTStarShell volume
        (activeDyadicIndices E j) (fun _ _ => True) K rho f x‖)
        (ENNReal.ofReal q) volume =
        eLpNorm (fun x => ‖q4SelectedKernelTTStarShell volume
          (activeDyadicIndices E j) R K rho f x‖)
          (ENNReal.ofReal q) volume := by
      apply eLpNorm_congr_ae
      filter_upwards with x
      rw [q4SelectedKernelTTStarShell_full_eq_activeDyadicRelation
        E j volume K rho hrho f x]
    _ <= ∑ n ∈ Finset.range (j + 3),
        eLpNorm (fun x => ‖q4SelectedKernelTTStarShell volume
          (activeDyadicIndices E j) (q4LevelShellRelation R level n) K rho f x‖)
          (ENNReal.ofReal q) volume := by
      simpa only [R, level] using hreassembly
    _ <= ∑ n ∈ Finset.range (j + 3),
        q4ActiveDyadicLevelStrongConstant d gamma eta Ccover Ckernel B j n q *
          eLpNorm f (ENNReal.ofReal p) volume := by
      exact Finset.sum_le_sum fun n hn => hlevels n (Finset.mem_range.mp hn)

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
