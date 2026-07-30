/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4SelectedSublinearity

/-!
# Strict crossed estimates for a literal selected `Q4` shell

This is the direct assembly point for the paper's radius-gap argument.  The
operator below is the literal finite selected kernel shell, not a positive
surrogate and not a Hilbert factor.  A pointwise pair-kernel estimate gives
its `L¹ → L∞` endpoint; a literal square-energy estimate gives its weak
`L² → L²` endpoint; the hard-cutoff crossed Marcinkiewicz theorem then gives
the strict interior strong estimate.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Set ENNReal

noncomputable section

/-- Assemble the two literal endpoint bounds for one selected finite
radius-gap shell into a strict crossed strong estimate.  Every analytic
hypothesis is stated at the kernel or square-energy level; in particular the
conclusion is not assumed as an input. -/
theorem q4SelectedKernelTTStarShell_crossed_strong_of_literal_endpoints
    {I X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq I]
    {μ : Measure X} [SFinite μ]
    (s : Finset I) (R : I → I → Prop) [DecidableRel R]
    (kernel : I → I → X → ℂ) (rho : X → I)
    (hrho : ∀ x, rho x ∈ s)
    (A : ℝ) (hA : 0 < A)
    (hkernel : ∀ i l z, ‖kernel i l z‖ ≤ A)
    (B : ℝ) (hB : 0 ≤ B)
    (hDfibres : ∀ g : X → ℂ,
      g ∈ q4SelectedShellDomain μ s R kernel rho →
        ∀ i ∈ s, Integrable (q4SelectedFibre rho g i) μ)
    (hDpairmeas : ∀ g : X → ℂ,
      g ∈ q4SelectedShellDomain μ s R kernel rho →
        ∀ i l x, AEStronglyMeasurable
          (fun y => kernel i l (x - y) * q4SelectedFibre rho g l y) μ)
    (hDoutput : ∀ g : X → ℂ,
      g ∈ q4SelectedShellDomain μ s R kernel rho →
        Integrable (fun x =>
          ‖q4SelectedKernelTTStarShell μ s R kernel rho g x‖ ^ (2 : ℕ)) μ)
    (hDinput : ∀ g : X → ℂ,
      g ∈ q4SelectedShellDomain μ s R kernel rho →
        Integrable (fun x => ‖g x‖ ^ (2 : ℕ)) μ)
    (henergy : ∀ g : X → ℂ,
      g ∈ q4SelectedShellDomain μ s R kernel rho →
        (∫ x, ‖q4SelectedKernelTTStarShell μ s R kernel rho g x‖ ^ (2 : ℕ) ∂μ) ≤
          B * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ)
    {p q cutoff I₀ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : X → ℂ) (hfmeas : Measurable f) (hfint : Integrable f μ)
    (hfp : Integrable (fun x => ‖f x‖ ^ p) μ)
    (hfD : f ∈ q4SelectedShellDomain μ s R kernel rho)
    (hI₀ : I₀ = ∫ x, ‖f x‖ ^ p ∂μ) (hI₀pos : 0 < I₀)
    (hcutoff : cutoff = 2 * A * I₀) :
    (∫⁻ x,
      ENNReal.ofReal
        (‖q4SelectedKernelTTStarShell μ s R kernel rho f x‖ ^ q) ∂μ) ≤
      ENNReal.ofReal q * (4 * ENNReal.ofReal B *
        ((ENNReal.ofReal (q - 2))⁻¹ *
          (ENNReal.ofReal cutoff) ^ (q - 2) *
            ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ)) := by
  refine crossed_marcinkiewicz_strong_of_hard_power_cutoff
    (D := q4SelectedShellDomain μ s R kernel rho)
    (T := fun g x => ‖q4SelectedKernelTTStarShell μ s R kernel rho g x‖)
    (hT_nonneg := ?_)
    (hT_subadd := ?_)
    (C₁ := A)
    (hC₁ := hA)
    (hstrong_one_top := ?_)
    (C₂ := ENNReal.ofReal B)
    (hweak_two := ?_)
    (p := p) (q := q) (K := cutoff) (I := I₀)
    (hp1 := hp1) (hp2 := hp2) (hq := hq)
    (f := f) (hf_norm := hfmeas.norm)
    (hTf := ?_)
    (hI := hI₀) (hIpos := hI₀pos) (hK := hcutoff)
    (hlow_mem := ?_) (hhigh_mem := ?_)
    (hhigh_integrable := ?_) (hhigh_major := ?_)
    (hlowI_meas := ?_)
  · intro g x
    exact norm_nonneg _
  · intro g h hg hh x
    exact norm_q4SelectedKernelTTStarShell_add_le μ s R kernel rho g h hg hh x
  · intro g hg x
    exact norm_q4SelectedKernelTTStarShell_le_of_bound μ s R kernel rho hrho g hA.le
      (hDfibres g hg) (hDpairmeas g hg) hkernel x
  · intro g hg r hr
    exact q4_weak_two_of_square_energy g
      (q4SelectedKernelTTStarShell μ s R kernel rho g)
      (aemeasurable_norm_of_integrable_sq
        (q4SelectedKernelTTStarShell μ s R kernel rho g) (hDoutput g hg))
      (hDoutput g hg) (hDinput g hg) hB (henergy g hg) hr
  · exact aemeasurable_norm_of_integrable_sq
      (q4SelectedKernelTTStarShell μ s R kernel rho f) (hDoutput f hfD)
  · intro t
    exact q4PowerCutoffLow_mem_q4SelectedShellDomain μ s R kernel rho
      hp1 cutoff t f hfmeas hfD
  · intro t
    exact q4PowerCutoffHigh_mem_q4SelectedShellDomain μ s R kernel rho
      hp1 cutoff t f hfmeas hfD
  · intro t ht
    exact integrable_q4PowerCutoffHigh_of_integrable hp1 cutoff t f hfmeas hfint
  · intro t ht
    exact hfp.const_mul (t / cutoff)
  · exact measurable_lintegral_q4PowerCutoffLow_sq hp1 cutoff f hfmeas

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
