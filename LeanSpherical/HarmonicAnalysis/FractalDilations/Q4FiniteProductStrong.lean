/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4StrongOffDiagonal
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4ActiveProductReassembly

/-!
# Strong strict-interior estimates for a literal finite product shell

This packages the two actual endpoints of one finite gap shell and turns the
proved crossed Marcinkiewicz power estimate into an `L^p → L^q` bound on
physical space times counting measure.  It is the non-endpoint replacement
for the Bourgain restricted-weak-type summation used at `Q4` itself.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Set ENNReal

noncomputable section

/-- Endpoint data for one literal finite-product kernel shell.  Every field
refers to `q4FiniteProductKernelShell` itself; in particular this package
does not replace a gap shell by a positive operator or a separately factored
Hilbert-space map. -/
structure Q4FiniteProductCrossedEndpoints
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {μ : Measure X} [SFinite μ]
    (s : Finset I) (R : I → I → Prop) [DecidableRel R]
    (K : I → I → X → ℂ) where
  A : ℝ
  hA : 0 < A
  hkernel : ∀ i l z, ‖K i l z‖ ≤ A
  hDmeas : ∀ g : X × {i // i ∈ s} → ℂ,
    g ∈ q4FiniteProductShellDomain μ s R K → Measurable g
  hDint : ∀ g : X × {i // i ∈ s} → ℂ,
    g ∈ q4FiniteProductShellDomain μ s R K →
      Integrable g (q4FiniteProductCountingMeasure μ s)
  hDfibres : ∀ g : X × {i // i ∈ s} → ℂ,
    g ∈ q4FiniteProductShellDomain μ s R K →
      ∀ i ∈ s, Integrable (q4FiniteProductToFibres s g i) μ
  hDpairmeas : ∀ g : X × {i // i ∈ s} → ℂ,
    g ∈ q4FiniteProductShellDomain μ s R K →
      ∀ i l x, AEStronglyMeasurable
        (fun y => K i l (x - y) * q4FiniteProductToFibres s g l y) μ
  B : ℝ
  hB : 0 ≤ B
  hDoutput : ∀ g : X × {i // i ∈ s} → ℂ,
    g ∈ q4FiniteProductShellDomain μ s R K →
      Integrable (fun z => ‖q4FiniteProductKernelShell μ s R K g z‖ ^ (2 : ℕ))
        (q4FiniteProductCountingMeasure μ s)
  hDinput : ∀ g : X × {i // i ∈ s} → ℂ,
    g ∈ q4FiniteProductShellDomain μ s R K →
      Integrable (fun z => ‖g z‖ ^ (2 : ℕ))
        (q4FiniteProductCountingMeasure μ s)
  henergy : ∀ g : X × {i // i ∈ s} → ℂ,
    g ∈ q4FiniteProductShellDomain μ s R K →
      (∫ z, ‖q4FiniteProductKernelShell μ s R K g z‖ ^ (2 : ℕ)
        ∂q4FiniteProductCountingMeasure μ s) ≤
        B * ∫ z, ‖g z‖ ^ (2 : ℕ) ∂q4FiniteProductCountingMeasure μ s

/-- One literal finite-product gap shell has a genuine strict-interior
off-diagonal strong estimate.  The constant is the explicit hard-cutoff
constant; its dependence on the shell is only through the actual pair-kernel
`L¹ → L∞` constant `A` and square-energy constant `B`.

The real/extended-real input-moment identification is discharged internally
from `hfp`; no auxiliary moment-equality premise is left in the API. -/
theorem q4FiniteProductKernelShell_strong_offDiagonal_of_pairwise_endpoints
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {μ : Measure X} [SFinite μ]
    (s : Finset I) (R : I → I → Prop) [DecidableRel R]
    (K : I → I → X → ℂ)
    (H : Q4FiniteProductCrossedEndpoints s R K)
    {p q I₀ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : X × {i // i ∈ s} → ℂ)
    (hfmeas : Measurable f)
    (hfint : Integrable f (q4FiniteProductCountingMeasure μ s))
    (hfp : Integrable (fun z => ‖f z‖ ^ p)
      (q4FiniteProductCountingMeasure μ s))
    (hfD : f ∈ q4FiniteProductShellDomain μ s R K)
    (hI₀ : I₀ = ∫ z, ‖f z‖ ^ p ∂q4FiniteProductCountingMeasure μ s)
    (hI₀pos : 0 < I₀) :
    eLpNorm (q4FiniteProductKernelShell μ s R K f) (ENNReal.ofReal q)
        (q4FiniteProductCountingMeasure μ s) ≤
      (ENNReal.ofReal q *
        (4 * ENNReal.ofReal H.B * ((ENNReal.ofReal (q - 2))⁻¹ *
          (ENNReal.ofReal (2 * H.A)) ^ (q - 2)))) ^ q⁻¹ *
        eLpNorm f (ENNReal.ofReal p) (q4FiniteProductCountingMeasure μ s) := by
  have hraw := q4FiniteProductKernelShell_crossed_strong_of_pairwise_endpoints
    (μ := μ) s R K H.A H.hA H.hkernel H.hDmeas H.hDint H.hDfibres
    H.hDpairmeas H.B H.hB H.hDoutput H.hDinput H.henergy
    hp1 hp2 hq f hfmeas hfint hfp hfD hI₀ hI₀pos
    (show 2 * H.A * I₀ = 2 * H.A * I₀ by rfl)
  have hinput := q4_lintegral_norm_rpow_eq_ofReal_integral
    (q4FiniteProductCountingMeasure μ s) f (by linarith) hfp hI₀
  have hmoment := q4_crossed_power_moment_of_hard_cutoff_bound
    (q4FiniteProductCountingMeasure μ s)
    (q4FiniteProductKernelShell μ s R K f) f
    (ENNReal.ofReal H.B) H.hA hI₀pos hp1 hp2 hq hinput hraw
  exact q4_eLpNorm_le_of_crossed_power_moment
    (q4FiniteProductCountingMeasure μ s)
    (q4FiniteProductKernelShell μ s R K f) f
    (by linarith) (by
      rw [hq]
      have hpminus : 0 < p - 1 := by linarith
      exact (div_pos (by linarith) hpminus))
    (ENNReal.ofReal q *
      (4 * ENNReal.ofReal H.B * ((ENNReal.ofReal (q - 2))⁻¹ *
        (ENNReal.ofReal (2 * H.A)) ^ (q - 2)))) hmoment

/-- The preceding strict-interior estimate specialized to an actual active
dyadic gap relation.  This short wrapper fixes both the physical measure and
the finite radius carrier appearing in Section 3, so its conclusion can be
fed directly into active-gap reassembly. -/
theorem q4ActiveDyadicGapShell_strong_offDiagonal_of_pairwise_endpoints
    {d : ℕ} (E : Set ℝ) (j n : ℕ)
    (K : ℤ → ℤ → Euclidean d → ℂ)
    (H : Q4FiniteProductCrossedEndpoints (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K)
    {p q I₀ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ)
    (hfmeas : Measurable f)
    (hfint : Integrable f (q4ActiveDyadicProductCountingMeasure d E j))
    (hfp : Integrable (fun z => ‖f z‖ ^ p)
      (q4ActiveDyadicProductCountingMeasure d E j))
    (hfD : f ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K)
    (hI₀ : I₀ = ∫ z, ‖f z‖ ^ p ∂q4ActiveDyadicProductCountingMeasure d E j)
    (hI₀pos : 0 < I₀) :
    eLpNorm (q4FiniteProductKernelShell volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K f) (ENNReal.ofReal q)
        (q4ActiveDyadicProductCountingMeasure d E j) ≤
      (ENNReal.ofReal q *
        (4 * ENNReal.ofReal H.B * ((ENNReal.ofReal (q - 2))⁻¹ *
          (ENNReal.ofReal (2 * H.A)) ^ (q - 2)))) ^ q⁻¹ *
        eLpNorm f (ENNReal.ofReal p) (q4ActiveDyadicProductCountingMeasure d E j) := by
  exact q4FiniteProductKernelShell_strong_offDiagonal_of_pairwise_endpoints
    (μ := volume) (activeDyadicIndices E j)
    (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
      activeDyadicGapLevel n) K H hp1 hp2 hq f hfmeas hfint hfp hfD
    hI₀ hI₀pos

/-- The degree quantity supplied by the upper Assouad-spectrum cover for one
positive canonical active-dyadic gap.  Naming it makes the passage from the
pairwise `L²` estimate to the crossed shell endpoint completely explicit. -/
def q4ActiveDyadicGapDegree
    (γ η C : ℝ) (j n : ℕ) : ℝ :=
  6 * C * (dyadicScale j) ^ (-η) *
    ((2 * ((2 : ℝ) ^ n * dyadicScale j + dyadicScale j)) /
      dyadicScale j) ^ γ

/-- The square-energy coefficient of an active gap shell.  If `B` is the
pairwise `L²` norm, the finite degree estimate gives this *square* coefficient
for the literal product kernel shell. -/
def q4ActiveDyadicGapEnergyConstant
    (γ η C B : ℝ) (j n : ℕ) : ℝ :=
  (B * q4ActiveDyadicGapDegree γ η C j n) ^ 2

/-- All analytic data which occur before the finite degree count in one
positive active-dyadic gap shell.  In particular `B` is a pairwise `L²`
constant, not an already-summed shell constant.  The conversion below uses
the proved literal product square-energy theorem, so the only summation in
this package is the actual finite relation on active cells. -/
structure Q4ActiveDyadicGapPairwiseEndpoints
    {d : ℕ} (E : Set ℝ) (j n : ℕ)
    (K : ℤ → ℤ → Euclidean d → ℂ) where
  A : ℝ
  hA : 0 < A
  hkernel : ∀ i l z, ‖K i l z‖ ≤ A
  hDmeas : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K → Measurable g
  hDint : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      Integrable g (q4ActiveDyadicProductCountingMeasure d E j)
  hDfibres : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      ∀ i ∈ activeDyadicIndices E j,
        Integrable (q4FiniteProductToFibres (activeDyadicIndices E j) g i) volume
  hDpairmeas : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      ∀ i l x, AEStronglyMeasurable
        (fun y => K i l (x - y) *
          q4FiniteProductToFibres (activeDyadicIndices E j) g l y) volume
  B : ℝ
  hB : 0 ≤ B
  hDinput : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      Integrable (fun z => ‖g z‖ ^ (2 : ℕ))
        (q4ActiveDyadicProductCountingMeasure d E j)
  hDinputFibres : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      ∀ i ∈ activeDyadicIndices E j,
        Integrable (fun x =>
          ‖q4FiniteProductToFibres (activeDyadicIndices E j) g i x‖ ^ (2 : ℕ)) volume
  hDfibmem : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      ∀ i ∈ activeDyadicIndices E j,
        MemLp (q4FiniteProductToFibres (activeDyadicIndices E j) g i) 2 volume
  hDpairmem : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      ∀ i l,
        q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
          activeDyadicGapLevel n i l →
        MemLp (q4PairwiseKernelApply volume K i l
          (q4FiniteProductToFibres (activeDyadicIndices E j) g l)) 2 volume
  hDpair : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      ∀ i l,
        q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
          activeDyadicGapLevel n i l →
        lpNorm (q4PairwiseKernelApply volume K i l
          (q4FiniteProductToFibres (activeDyadicIndices E j) g l)) 2 volume ≤
          B * lpNorm (q4FiniteProductToFibres (activeDyadicIndices E j) g l) 2 volume
  hDoutputMeas : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      Measurable (q4FiniteProductKernelShell volume (activeDyadicIndices E j)
        (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
          activeDyadicGapLevel n) K g)
  hDoutput : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      Integrable (fun z => ‖q4FiniteProductKernelShell volume
        (activeDyadicIndices E j)
        (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
          activeDyadicGapLevel n) K g z‖ ^ (2 : ℕ))
        (q4ActiveDyadicProductCountingMeasure d E j)
  hDoutputFibres : ∀ g : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ,
    g ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K →
      ∀ i ∈ activeDyadicIndices E j,
        Integrable (fun x =>
          ‖q4FiniteProductToFibres (activeDyadicIndices E j)
            (q4FiniteProductKernelShell volume (activeDyadicIndices E j)
              (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
                activeDyadicGapLevel n) K g) i x‖ ^ (2 : ℕ)) volume

/-- Insert the upper Assouad-spectrum degree estimate into actual pairwise
endpoint data.  This constructs the `L¹ → L∞`/square-energy package required
by crossed interpolation for the literal active-gap product shell. -/
noncomputable def Q4ActiveDyadicGapPairwiseEndpoints.toCrossedEndpoints
    {d : ℕ} {E : Set ℝ} {γ η C : ℝ} {j n : ℕ}
    (hE : E ⊆ Icc (1 : ℝ) 2)
    (hcover : HasSubpowerAssouadCoverBound E γ η C)
    (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hδone : dyadicScale j < 1) (hn : 0 < n)
    {K : ℤ → ℤ → Euclidean d → ℂ}
    (H : Q4ActiveDyadicGapPairwiseEndpoints E j n K) :
    Q4FiniteProductCrossedEndpoints (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K := by
  classical
  refine
    { A := H.A
      hA := H.hA
      hkernel := H.hkernel
      hDmeas := H.hDmeas
      hDint := H.hDint
      hDfibres := H.hDfibres
      hDpairmeas := H.hDpairmeas
      B := q4ActiveDyadicGapEnergyConstant γ η C H.B j n
      hB := sq_nonneg _
      hDoutput := H.hDoutput
      hDinput := H.hDinput
      henergy := ?_ }
  intro g hg
  simpa only [q4ActiveDyadicGapEnergyConstant, q4ActiveDyadicGapDegree] using
    (q4ActiveDyadicProductLevel_sq_integral_le_of_pairwise_bound
      hE hcover hC hγ hδone hn K g H.hB
      (H.hDfibmem g hg) (H.hDpairmem g hg) (H.hDpair g hg)
      (H.hDmeas g hg) (H.hDinput g hg) (H.hDinputFibres g hg)
      (H.hDoutputMeas g hg) (H.hDoutput g hg) (H.hDoutputFibres g hg))

/-- Strict off-diagonal strong type with the pairwise stationary bound and
upper-spectrum degree count supplied separately.  This is the direct API for
Section 3: `A` is the stationary `L¹ → L∞` bound and `H.B` is the pairwise
`L²` bound; the finite active relation is summed only by
`toCrossedEndpoints`. -/
theorem q4ActiveDyadicGapShell_strong_offDiagonal_of_active_pairwise_endpoints
    {d : ℕ} {E : Set ℝ} {γ η C : ℝ} {j n : ℕ}
    (hE : E ⊆ Icc (1 : ℝ) 2)
    (hcover : HasSubpowerAssouadCoverBound E γ η C)
    (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hδone : dyadicScale j < 1) (hn : 0 < n)
    (K : ℤ → ℤ → Euclidean d → ℂ)
    (H : Q4ActiveDyadicGapPairwiseEndpoints E j n K)
    {p q I₀ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : Euclidean d × {i // i ∈ activeDyadicIndices E j} → ℂ)
    (hfmeas : Measurable f)
    (hfint : Integrable f (q4ActiveDyadicProductCountingMeasure d E j))
    (hfp : Integrable (fun z => ‖f z‖ ^ p)
      (q4ActiveDyadicProductCountingMeasure d E j))
    (hfD : f ∈ q4FiniteProductShellDomain volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K)
    (hI₀ : I₀ = ∫ z, ‖f z‖ ^ p ∂q4ActiveDyadicProductCountingMeasure d E j)
    (hI₀pos : 0 < I₀) :
    eLpNorm (q4FiniteProductKernelShell volume (activeDyadicIndices E j)
      (q4LevelShellRelation (q4ActiveDyadicProductRelation E j)
        activeDyadicGapLevel n) K f) (ENNReal.ofReal q)
        (q4ActiveDyadicProductCountingMeasure d E j) ≤
      (ENNReal.ofReal q *
        (4 * ENNReal.ofReal
          (q4ActiveDyadicGapEnergyConstant γ η C H.B j n) *
          ((ENNReal.ofReal (q - 2))⁻¹ *
            (ENNReal.ofReal (2 * H.A)) ^ (q - 2)))) ^ q⁻¹ *
        eLpNorm f (ENNReal.ofReal p) (q4ActiveDyadicProductCountingMeasure d E j) := by
  exact q4ActiveDyadicGapShell_strong_offDiagonal_of_pairwise_endpoints E j n K
    (H.toCrossedEndpoints hE hcover hC hγ hδone hn)
    hp1 hp2 hq f hfmeas hfint hfp hfD hI₀ hI₀pos

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
