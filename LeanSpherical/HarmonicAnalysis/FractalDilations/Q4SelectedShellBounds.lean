/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4SelectedLinearization

/-!
# Endpoint bounds for a selected `Q4` shell

This file transfers the literal fibre estimates for one `TT*` radius-gap
shell to its scalar selected-radius linearization.  Unlike a factorization
argument, this uses only the fact that the selector chooses one member of a
finite family at each point.  It is therefore valid for the individual,
generally non-positive, gap shells used in the paper.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Pointwise, the selected scalar output is one member of the finite family
of fibre outputs, so its squared norm is bounded by the fibre square sum. -/
theorem norm_sq_q4SelectedKernelTTStarShell_le_sum
    {ι X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq ι]
    (μ : Measure X) (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (K : ι → ι → X → ℂ) (rho : X → ι) (hrho : ∀ x, rho x ∈ s)
    (g : X → ℂ) (x : X) :
    ‖q4SelectedKernelTTStarShell μ s R K rho g x‖ ^ (2 : ℕ) ≤
      ∑ i ∈ s,
        ‖q4KernelTTStarShell μ s R K (q4SelectedFibre rho g) i x‖ ^ (2 : ℕ) := by
  unfold q4SelectedKernelTTStarShell
  exact Finset.single_le_sum
    (fun i hi => sq_nonneg
      (‖q4KernelTTStarShell μ s R K (q4SelectedFibre rho g) i x‖))
    (hrho x)

/-- Integrating the preceding pointwise inequality gives the scalar selected
`L²` energy bound.  Measurability of an arbitrary selector is intentionally
not inferred here: the explicitly supplied integrability premise is exactly
what the analytic selected-linearization step must establish. -/
theorem q4SelectedKernelTTStarShell_energy_le_fibre_energy
    {ι X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq ι]
    (μ : Measure X) (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (K : ι → ι → X → ℂ) (rho : X → ι) (hrho : ∀ x, rho x ∈ s)
    (g : X → ℂ)
    (hselected : Integrable (fun x =>
      ‖q4SelectedKernelTTStarShell μ s R K rho g x‖ ^ (2 : ℕ)) μ)
    (hfibre : ∀ i ∈ s, Integrable (fun x =>
      ‖q4KernelTTStarShell μ s R K (q4SelectedFibre rho g) i x‖ ^ (2 : ℕ)) μ) :
    (∫ x, ‖q4SelectedKernelTTStarShell μ s R K rho g x‖ ^ (2 : ℕ) ∂μ) ≤
      q4FibreL2Energy μ s
        (q4KernelTTStarShell μ s R K (q4SelectedFibre rho g)) := by
  have hsum : Integrable (fun x => ∑ i ∈ s,
      ‖q4KernelTTStarShell μ s R K (q4SelectedFibre rho g) i x‖ ^ (2 : ℕ)) μ := by
    exact integrable_finsetSum s hfibre
  calc
    (∫ x, ‖q4SelectedKernelTTStarShell μ s R K rho g x‖ ^ (2 : ℕ) ∂μ) ≤
        ∫ x, ∑ i ∈ s,
          ‖q4KernelTTStarShell μ s R K (q4SelectedFibre rho g) i x‖ ^ (2 : ℕ) ∂μ := by
      apply integral_mono hselected hsum
      intro x
      exact norm_sq_q4SelectedKernelTTStarShell_le_sum μ s R K rho hrho g x
    _ = q4FibreL2Energy μ s
        (q4KernelTTStarShell μ s R K (q4SelectedFibre rho g)) := by
      unfold q4FibreL2Energy
      rw [integral_finsetSum s hfibre]

/-- The actual fibre energy estimate for a gap shell gives the scalar
selected-radius `L²` endpoint.  This is the exact non-positive-shell bridge
needed before applying a genuine crossed interpolation theorem. -/
theorem q4SelectedKernelTTStarShell_energy_le_of_fibre_energy
    {ι X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq ι]
    (μ : Measure X) (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (K : ι → ι → X → ℂ) (rho : X → ι) (hrho : ∀ x, rho x ∈ s)
    (g : X → ℂ) {C : ℝ}
    (hselected : Integrable (fun x =>
      ‖q4SelectedKernelTTStarShell μ s R K rho g x‖ ^ (2 : ℕ)) μ)
    (hfibre : ∀ i ∈ s, Integrable (fun x =>
      ‖q4KernelTTStarShell μ s R K (q4SelectedFibre rho g) i x‖ ^ (2 : ℕ)) μ)
    (hg_sq : ∀ i ∈ s, Integrable (fun x =>
      ‖q4SelectedFibre rho g i x‖ ^ (2 : ℕ)) μ)
    (henergy :
      q4FibreL2Energy μ s
          (q4KernelTTStarShell μ s R K (q4SelectedFibre rho g)) ≤
        C ^ 2 * q4FibreL2Energy μ s (q4SelectedFibre rho g)) :
    (∫ x, ‖q4SelectedKernelTTStarShell μ s R K rho g x‖ ^ (2 : ℕ) ∂μ) ≤
      C ^ 2 * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ := by
  calc
    (∫ x, ‖q4SelectedKernelTTStarShell μ s R K rho g x‖ ^ (2 : ℕ) ∂μ) ≤
        q4FibreL2Energy μ s
          (q4KernelTTStarShell μ s R K (q4SelectedFibre rho g)) :=
      q4SelectedKernelTTStarShell_energy_le_fibre_energy
        μ s R K rho hrho g hselected hfibre
    _ ≤ C ^ 2 * q4FibreL2Energy μ s (q4SelectedFibre rho g) := henergy
    _ = C ^ 2 * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ := by
      rw [q4FibreL2Energy_selected_eq_integral μ s rho hrho g hg_sq]

/-- The fibre `L¹ → L∞` kernel estimate is also an honest scalar estimate
after selected linearization. -/
theorem norm_q4SelectedKernelTTStarShell_le_of_bound
    {ι X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq ι]
    (μ : Measure X) (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (K : ι → ι → X → ℂ) (rho : X → ι) (hrho : ∀ x, rho x ∈ s)
    (g : X → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hg : ∀ i ∈ s, Integrable (q4SelectedFibre rho g i) μ)
    (hmeas : ∀ i j x, AEStronglyMeasurable
      (fun y => K i j (x - y) * q4SelectedFibre rho g j y) μ)
    (hkernel : ∀ i j z, ‖K i j z‖ ≤ A) (x : X) :
    ‖q4SelectedKernelTTStarShell μ s R K rho g x‖ ≤
      A * ∫ y, ‖g y‖ ∂μ := by
  unfold q4SelectedKernelTTStarShell
  rw [← q4FibreL1Size_selected_eq_integral μ s rho hrho g hg]
  exact norm_q4KernelTTStarShell_le_of_bound
    μ s R K (q4SelectedFibre rho g) hA hg hmeas hkernel (rho x) x

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
