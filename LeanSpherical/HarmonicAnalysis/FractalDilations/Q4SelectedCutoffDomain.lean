/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4SelectedShellBounds
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4SelectedSublinearity
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4StrongOffDiagonal

/-!
# A cutoff-stable domain for the selected `Q4` shell

The strict, non-endpoint interpolation used near `Q4` applies a hard
amplitude cutoff to a *selected* finite-radius kernel shell.  Pairwise
Bochner integrability alone is enough for linearity, but it is not enough for
the square endpoint: an `L¹` field need not lie in `L²`.  This file records
the correct small domain on which all of the cutoff inputs are available.

The domain consists of measurable `L¹ ∩ L²` inputs together with the literal
pairwise integrability condition.  It is closed under both hard cutoffs.  A
genuine pairwise `L²` operator bound then supplies the output `L²` facts and
the finite-shell square energy; none of those facts is postulated for an
arbitrary merely-integrable field.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Set ENNReal
open scoped BigOperators

noncomputable section

/-- The actual domain used by the strict selected-shell interpolation.

The final component is exactly the pairwise Bochner-integrability condition
needed for the literal kernel formula.  The first three components are the
ordinary regularity facts enjoyed by Schwartz inputs and preserved by the
hard low/high amplitude cutoffs. -/
def q4SelectedCutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq I]
    (mu : Measure X) (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex) (rho : X -> I) : Set (X -> Complex) :=
  {g | Measurable g /\ Integrable g mu /\ MemLp g 2 mu /\
    g ∈ q4SelectedShellDomain mu s R K rho}

/-- A pairwise `L²` bound for the literal convolution operators on the
physical `L¹ ∩ L²` carrier.  This is the analytic Plancherel input in the
spherical application.  The harmless `L¹` hypothesis is essential for the
literal Bochner convolution to be represented pointwise; it is preserved by
both amplitude cutoffs and is exactly the carrier on which the Fourier/
physical-space bridge is proved. -/
structure Q4PairwiseL2OperatorBound
    {I X : Type*} [Sub X] [MeasurableSpace X]
    (mu : Measure X) (K : I -> I -> X -> Complex) where
  B : Real
  nonneg : 0 <= B
  memLp : forall i l (g : X -> Complex), Integrable g mu -> MemLp g 2 mu ->
    MemLp (q4PairwiseKernelApply mu K i l g) 2 mu
  bound : forall i l (g : X -> Complex), Integrable g mu -> MemLp g 2 mu ->
    lpNorm (q4PairwiseKernelApply mu K i l g) 2 mu <= B * lpNorm g 2 mu

/-- The selected fibre is an indicator of the corresponding selector cell. -/
theorem q4SelectedFibre_eq_indicator
    {I X : Type*} [DecidableEq I] (rho : X -> I)
    (g : X -> Complex) (i : I) :
    q4SelectedFibre rho g i = {x | rho x = i}.indicator g := by
  funext x
  by_cases h : rho x = i <;> simp [q4SelectedFibre, h]

/-- Integrability passes from a scalar field to every measurable selected
fibre. -/
theorem integrable_q4SelectedFibre_of_measurable_selector
    {I X : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (rho : X -> I) (hrho : Measurable rho) (g : X -> Complex)
    {mu : Measure X} (hg : Integrable g mu) (i : I) :
    Integrable (q4SelectedFibre rho g i) mu := by
  let P : Set X := {x | rho x = i}
  have hP : MeasurableSet P := by
    have hpre : MeasurableSet (rho ⁻¹' ({i} : Set I)) :=
      hrho (measurableSet_singleton i)
    convert hpre using 1
    ext x
    simp [P]
  have hfun : q4SelectedFibre rho g i = P.indicator g := by
    simpa only [P] using q4SelectedFibre_eq_indicator rho g i
  rw [hfun]
  exact hg.indicator hP

/-- `L²` membership passes from a scalar field to every measurable selected
fibre. -/
theorem memLp_two_q4SelectedFibre_of_measurable_selector
    {I X : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (rho : X -> I) (hrho : Measurable rho) (g : X -> Complex)
    {mu : Measure X} (hg : MemLp g 2 mu) (i : I) :
    MemLp (q4SelectedFibre rho g i) 2 mu := by
  let P : Set X := {x | rho x = i}
  have hP : MeasurableSet P := by
    have hpre : MeasurableSet (rho ⁻¹' ({i} : Set I)) :=
      hrho (measurableSet_singleton i)
    convert hpre using 1
    ext x
    simp [P]
  have hfun : q4SelectedFibre rho g i = P.indicator g := by
    simpa only [P] using q4SelectedFibre_eq_indicator rho g i
  rw [hfun]
  exact hg.indicator hP

/-- The hard-cutoff set is measurable for a measurable input. -/
theorem measurableSet_q4PowerCutoff
    {X : Type*} [MeasurableSpace X]
    {p cutoff t : Real} (hp1 : 1 < p) (g : X -> Complex)
    (hg : Measurable g) :
    MeasurableSet {x | t * ‖g x‖ ^ (p - 1) <= cutoff} := by
  have hpminus : 0 < p - 1 := by linarith
  have hpow : Measurable (fun x => ‖g x‖ ^ (p - 1)) :=
    (continuous_id.rpow_const (fun _ => Or.inr hpminus.le)).measurable.comp hg.norm
  exact measurableSet_le (measurable_const.mul hpow) measurable_const

/-- The low hard cutoff remains in the cutoff-stable selected-shell domain. -/
theorem q4PowerCutoffLow_mem_q4SelectedCutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq I]
    (mu : Measure X) (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex) (rho : X -> I)
    {p cutoff t : Real} (hp1 : 1 < p) (g : X -> Complex)
    (hg : g ∈ q4SelectedCutoffStableDomain mu s R K rho) :
    q4PowerCutoffLow p cutoff t g ∈
      q4SelectedCutoffStableDomain mu s R K rho := by
  let P : Set X := {x | t * ‖g x‖ ^ (p - 1) <= cutoff}
  have hP : MeasurableSet P := by
    simpa only [P] using measurableSet_q4PowerCutoff hp1 g hg.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [P, q4PowerCutoffLow] using hg.1.indicator hP
  · simpa only [P, q4PowerCutoffLow] using hg.2.1.indicator hP
  · simpa only [P, q4PowerCutoffLow] using hg.2.2.1.indicator hP
  · exact q4PowerCutoffLow_mem_q4SelectedShellDomain mu s R K rho
      hp1 cutoff t g hg.1 hg.2.2.2

/-- The complementary hard cutoff remains in the cutoff-stable selected-shell
domain. -/
theorem q4PowerCutoffHigh_mem_q4SelectedCutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq I]
    (mu : Measure X) (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex) (rho : X -> I)
    {p cutoff t : Real} (hp1 : 1 < p) (g : X -> Complex)
    (hg : g ∈ q4SelectedCutoffStableDomain mu s R K rho) :
    q4PowerCutoffHigh p cutoff t g ∈
      q4SelectedCutoffStableDomain mu s R K rho := by
  let P : Set X := {x | t * ‖g x‖ ^ (p - 1) <= cutoff}
  have hP : MeasurableSet P := by
    simpa only [P] using measurableSet_q4PowerCutoff hp1 g hg.1
  have hhigh : q4PowerCutoffHigh p cutoff t g = Pᶜ.indicator g := by
    funext x
    dsimp only [P]
    by_cases hcut : t * ‖g x‖ ^ (p - 1) <= cutoff <;>
      simp [q4PowerCutoffHigh, q4PowerCutoffLow, hcut]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hhigh]
    exact hg.1.indicator hP.compl
  · rw [hhigh]
    exact hg.2.1.indicator hP.compl
  · rw [hhigh]
    exact hg.2.2.1.indicator hP.compl
  · exact q4PowerCutoffHigh_mem_q4SelectedShellDomain mu s R K rho
      hp1 cutoff t g hg.1 hg.2.2.2

/-- A concise constructor for the cutoff-stable domain. -/
theorem mem_q4SelectedCutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq I]
    (mu : Measure X) (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex) (rho : X -> I) (g : X -> Complex)
    (hmeas : Measurable g) (hint : Integrable g mu) (hmem : MemLp g 2 mu)
    (hpair : g ∈ q4SelectedShellDomain mu s R K rho) :
    g ∈ q4SelectedCutoffStableDomain mu s R K rho :=
  ⟨hmeas, hint, hmem, hpair⟩

/-- The finite selected shell preserves `L²` once every literal pair operator
has the corresponding global `L²` bound.  This is the small but important
replacement for the former impossible hypothesis that *every* element of the
merely Bochner-integrable shell domain already have square-integrable output.

The selector is assumed measurable only here, where it is genuinely needed
to identify the selected output with a finite sum of measurable fibres. -/
theorem memLp_two_q4SelectedKernelTTStarShell_of_pairwise_bound
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex) (rho : X -> I)
    (hrho : forall x, rho x ∈ s) (hrhoMeas : Measurable rho)
    (H : Q4PairwiseL2OperatorBound mu K)
    (g : X -> Complex)
    (hg : g ∈ q4SelectedCutoffStableDomain mu s R K rho) :
    MemLp (q4SelectedKernelTTStarShell mu s R K rho g) 2 mu := by
  have hfibre (l : I) : MemLp (q4SelectedFibre rho g l) 2 mu :=
    memLp_two_q4SelectedFibre_of_measurable_selector rho hrhoMeas g hg.2.2.1 l
  have hfibreInt (l : I) : Integrable (q4SelectedFibre rho g l) mu :=
    integrable_q4SelectedFibre_of_measurable_selector rho hrhoMeas g hg.2.1 l
  have hshell (i : I) :
      MemLp (q4KernelTTStarShell mu s R K (q4SelectedFibre rho g) i) 2 mu := by
    unfold q4KernelTTStarShell
    exact memLp_finsetSum (μ := mu) (p := 2) (s.filter (R i))
      (f := fun l => q4PairwiseKernelApply mu K i l (q4SelectedFibre rho g l))
      (fun l hl => H.memLp i l _ (hfibreInt l) (hfibre l))
  let P : I -> Set X := fun i => {x | rho x = i}
  have hP (i : I) : MeasurableSet (P i) := by
    have hpre : MeasurableSet (rho ⁻¹' ({i} : Set I)) :=
      hrhoMeas (measurableSet_singleton i)
    convert hpre using 1
    ext x
    simp [P]
  have hsum : q4SelectedKernelTTStarShell mu s R K rho g =
      ∑ i ∈ s, (P i).indicator
        (q4KernelTTStarShell mu s R K (q4SelectedFibre rho g) i) := by
    funext x
    unfold q4SelectedKernelTTStarShell
    simp only [Finset.sum_apply, Set.indicator_apply, P, Set.mem_setOf_eq]
    simpa only using
      (Finset.sum_ite_eq_of_mem s (rho x)
        (fun i => q4KernelTTStarShell mu s R K (q4SelectedFibre rho g) i x)
        (hrho x)).symm
  rw [hsum]
  exact memLp_finsetSum (μ := mu) (p := 2) s
    (f := fun i => (P i).indicator
      (q4KernelTTStarShell mu s R K (q4SelectedFibre rho g) i))
    (fun i hi => (hshell i).indicator (hP i))

/-- The familiar equivalence between `L²` membership and integrability of
the squared norm, exposed in the exact form used by the literal shell
energy inequalities. -/
theorem integrable_norm_sq_of_memLp_two
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    (g : X -> Complex) (hg : MemLp g 2 mu) :
    Integrable (fun x => ‖g x‖ ^ (2 : Nat)) mu :=
  (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg

/-- The `L¹ → L∞` estimate for a selected literal shell only needs a kernel
bound on pairs which actually occur in its finite relation.  This local form
is indispensable at level zero, where stationary phase supplies the
diagonal bound but says nothing about unrelated radius pairs. -/
theorem norm_q4SelectedKernelTTStarShell_le_of_bound_on_relation
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (mu : Measure X) (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex) (rho : X -> I)
    (hrho : forall x, rho x ∈ s) (g : X -> Complex) {A : Real} (hA : 0 <= A)
    (hg : forall i ∈ s, Integrable (q4SelectedFibre rho g i) mu)
    (hmeas : forall i l x, AEStronglyMeasurable
      (fun y => K i l (x - y) * q4SelectedFibre rho g l y) mu)
    (hkernel : forall i l z, R i l -> ‖K i l z‖ <= A) (x : X) :
    ‖q4SelectedKernelTTStarShell mu s R K rho g x‖ <=
      A * ∫ y, ‖g y‖ ∂mu := by
  let Kcut : I -> I -> X -> Complex := fun i l z =>
    if R i l then K i l z else 0
  have hKcut : forall i l z, ‖Kcut i l z‖ <= A := by
    intro i l z
    by_cases hil : R i l
    · simpa only [Kcut, if_pos hil] using hkernel i l z hil
    · simpa only [Kcut, if_neg hil, norm_zero] using hA
  have hmeasCut : forall i l x, AEStronglyMeasurable
      (fun y => Kcut i l (x - y) * q4SelectedFibre rho g l y) mu := by
    intro i l z
    by_cases hil : R i l
    · simpa only [Kcut, if_pos hil] using hmeas i l z
    · simpa only [Kcut, if_neg hil, zero_mul] using
        (aestronglyMeasurable_zero : AEStronglyMeasurable (fun _ : X => (0 : Complex)) mu)
  have hshell : q4SelectedKernelTTStarShell mu s R K rho g =
      q4SelectedKernelTTStarShell mu s R Kcut rho g := by
    funext z
    unfold q4SelectedKernelTTStarShell q4KernelTTStarShell
    apply Finset.sum_congr rfl
    intro l hl
    have hrel : R (rho z) l := (Finset.mem_filter.mp hl).2
    simp only [Kcut, if_pos hrel]
  rw [hshell]
  exact norm_q4SelectedKernelTTStarShell_le_of_bound mu s R Kcut rho hrho g hA
    hg hmeasCut hKcut x

/-- The literal selected shell has the finite-graph square estimate on the
cutoff-stable domain.  The only analytic endpoint hypothesis is the global
pairwise `L²` operator estimate `H`; the degree factor is supplied separately
by the upper Assouad-spectrum count in the spherical application. -/
theorem q4SelectedKernelTTStarShell_energy_le_of_cutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (hR : Std.Symm R) (D : Real) (hD : 0 <= D)
    (hdegree : forall i ∈ s, ((s.filter (R i)).card : Real) <= D)
    (K : I -> I -> X -> Complex) (rho : X -> I)
    (hrho : forall x, rho x ∈ s) (hrhoMeas : Measurable rho)
    (H : Q4PairwiseL2OperatorBound mu K)
    (g : X -> Complex)
    (hg : g ∈ q4SelectedCutoffStableDomain mu s R K rho) :
    (∫ x, ‖q4SelectedKernelTTStarShell mu s R K rho g x‖ ^ (2 : Nat) ∂mu) <=
      (H.B * D) ^ 2 * ∫ x, ‖g x‖ ^ (2 : Nat) ∂mu := by
  have hfibre (i : I) : MemLp (q4SelectedFibre rho g i) 2 mu :=
    memLp_two_q4SelectedFibre_of_measurable_selector rho hrhoMeas g hg.2.2.1 i
  have hfibreInt (i : I) : Integrable (q4SelectedFibre rho g i) mu :=
    integrable_q4SelectedFibre_of_measurable_selector rho hrhoMeas g hg.2.1 i
  have hshell (i : I) :
      MemLp (q4KernelTTStarShell mu s R K (q4SelectedFibre rho g) i) 2 mu := by
    unfold q4KernelTTStarShell
    exact memLp_finsetSum (μ := mu) (p := 2) (s.filter (R i))
      (f := fun l => q4PairwiseKernelApply mu K i l (q4SelectedFibre rho g l))
      (fun l hl => H.memLp i l _ (hfibreInt l) (hfibre l))
  have hselected : MemLp (q4SelectedKernelTTStarShell mu s R K rho g) 2 mu :=
    memLp_two_q4SelectedKernelTTStarShell_of_pairwise_bound s R K rho hrho
      hrhoMeas H g hg
  have hselectedSq : Integrable (fun x =>
      ‖q4SelectedKernelTTStarShell mu s R K rho g x‖ ^ (2 : Nat)) mu :=
    integrable_norm_sq_of_memLp_two _ hselected
  have hshellSq (i : I) (hi : i ∈ s) : Integrable (fun x =>
      ‖q4KernelTTStarShell mu s R K (q4SelectedFibre rho g) i x‖ ^ (2 : Nat)) mu :=
    integrable_norm_sq_of_memLp_two _ (hshell i)
  have hfibreSq (i : I) (hi : i ∈ s) : Integrable (fun x =>
      ‖q4SelectedFibre rho g i x‖ ^ (2 : Nat)) mu :=
    integrable_norm_sq_of_memLp_two _ (hfibre i)
  have henergy := q4FibreL2Energy_kernelShell_le_of_pairwise_bound_on_relation
    mu s R hR D hD hdegree K (q4SelectedFibre rho g) H.nonneg
    (fun i hi => hfibre i)
    (fun i l hil => H.memLp i l _ (hfibreInt l) (hfibre l))
    (fun i l hil => H.bound i l _ (hfibreInt l) (hfibre l))
  calc
    (∫ x, ‖q4SelectedKernelTTStarShell mu s R K rho g x‖ ^ (2 : Nat) ∂mu) <=
        q4FibreL2Energy mu s
          (q4KernelTTStarShell mu s R K (q4SelectedFibre rho g)) :=
      q4SelectedKernelTTStarShell_energy_le_fibre_energy
        mu s R K rho hrho g hselectedSq hshellSq
    _ <= (H.B * D) ^ 2 * q4FibreL2Energy mu s (q4SelectedFibre rho g) :=
      henergy
    _ = (H.B * D) ^ 2 * ∫ x, ‖g x‖ ^ (2 : Nat) ∂mu := by
      rw [q4FibreL2Energy_selected_eq_integral mu s rho hrho g hfibreSq]

/-- The strict crossed estimate for a literal selected shell on the
cutoff-stable domain.  This is the usable Section 3 interpolation interface:
all domain facts needed after a hard cutoff are proved from `L¹ ∩ L²`, while
the nontrivial square endpoint is derived from the genuine pairwise `L²`
operator bound and the finite degree estimate.

In particular, no premise asserts square-integrability of outputs for an
arbitrary element of the old pairwise-Bochner domain. -/
theorem q4SelectedKernelTTStarShell_crossed_strong_of_cutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} [SFinite mu]
    (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (hR : Std.Symm R) (D : Real) (hD : 0 <= D)
    (hdegree : forall i ∈ s, ((s.filter (R i)).card : Real) <= D)
    (K : I -> I -> X -> Complex) (rho : X -> I)
    (hrho : forall x, rho x ∈ s) (hrhoMeas : Measurable rho)
    (A : Real) (hA : 0 < A)
    (hkernel : forall i l z, R i l -> ‖K i l z‖ <= A)
    (H : Q4PairwiseL2OperatorBound mu K)
    {p q cutoff I0 : Real} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : X -> Complex)
    (hfD : f ∈ q4SelectedCutoffStableDomain mu s R K rho)
    (hfp : Integrable (fun x => ‖f x‖ ^ p) mu)
    (hI0 : I0 = ∫ x, ‖f x‖ ^ p ∂mu) (hI0pos : 0 < I0)
    (hcutoff : cutoff = 2 * A * I0) :
    (∫⁻ x, ENNReal.ofReal
      (‖q4SelectedKernelTTStarShell mu s R K rho f x‖ ^ q) ∂mu) <=
      ENNReal.ofReal q *
        (4 * ENNReal.ofReal ((H.B * D) ^ 2) *
          ((ENNReal.ofReal (q - 2))⁻¹ *
            (ENNReal.ofReal cutoff) ^ (q - 2) *
              ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂mu)) := by
  have houtputSq (g : X -> Complex)
      (hg : g ∈ q4SelectedCutoffStableDomain mu s R K rho) :
      Integrable (fun x =>
        ‖q4SelectedKernelTTStarShell mu s R K rho g x‖ ^ (2 : Nat)) mu := by
    apply integrable_norm_sq_of_memLp_two
    exact memLp_two_q4SelectedKernelTTStarShell_of_pairwise_bound
      s R K rho hrho hrhoMeas H g hg
  refine crossed_marcinkiewicz_strong_of_hard_power_cutoff
    (D := q4SelectedCutoffStableDomain mu s R K rho)
    (T := fun g x => ‖q4SelectedKernelTTStarShell mu s R K rho g x‖)
    (hT_nonneg := ?_)
    (hT_subadd := ?_)
    (C₁ := A)
    (hC₁ := hA)
    (hstrong_one_top := ?_)
    (C₂ := ENNReal.ofReal ((H.B * D) ^ 2))
    (hweak_two := ?_)
    (p := p) (q := q) (K := cutoff) (I := I0)
    (hp1 := hp1) (hp2 := hp2) (hq := hq)
    (f := f) (hf_norm := hfD.1.norm)
    (hTf := ?_)
    (hI := hI0) (hIpos := hI0pos) (hK := hcutoff)
    (hlow_mem := ?_) (hhigh_mem := ?_)
    (hhigh_integrable := ?_) (hhigh_major := ?_)
    (hlowI_meas := ?_)
  · intro g x
    exact norm_nonneg _
  · intro g h hg hh x
    exact norm_q4SelectedKernelTTStarShell_add_le mu s R K rho g h
      hg.2.2.2 hh.2.2.2 x
  · intro g hg x
    exact norm_q4SelectedKernelTTStarShell_le_of_bound_on_relation
      mu s R K rho hrho g hA.le
      (fun i hi =>
        integrable_q4SelectedFibre_of_measurable_selector rho hrhoMeas g hg.2.1 i)
      (fun i l z => (hg.2.2.2 i l z).aestronglyMeasurable)
      hkernel x
  · intro g hg r hr
    exact q4_weak_two_of_square_energy g
      (q4SelectedKernelTTStarShell mu s R K rho g)
      (aemeasurable_norm_of_integrable_sq
        (q4SelectedKernelTTStarShell mu s R K rho g) (houtputSq g hg))
      (houtputSq g hg)
      (integrable_norm_sq_of_memLp_two g hg.2.2.1)
      (sq_nonneg _)
      (q4SelectedKernelTTStarShell_energy_le_of_cutoffStableDomain
        s R hR D hD hdegree K rho hrho hrhoMeas H g hg)
      hr
  · exact aemeasurable_norm_of_integrable_sq
      (q4SelectedKernelTTStarShell mu s R K rho f) (houtputSq f hfD)
  · intro t
    exact q4PowerCutoffLow_mem_q4SelectedCutoffStableDomain
      mu s R K rho hp1 f hfD
  · intro t
    exact q4PowerCutoffHigh_mem_q4SelectedCutoffStableDomain
      mu s R K rho hp1 f hfD
  · intro t ht
    exact integrable_q4PowerCutoffHigh_of_integrable hp1 cutoff t f hfD.1 hfD.2.1
  · intro t ht
    exact hfp.const_mul (t / cutoff)
  · exact measurable_lintegral_q4PowerCutoffLow_sq hp1 cutoff f hfD.1

/-- The homogeneous constant produced by strict crossed interpolation from a
pointwise kernel constant `A` and a square-energy coefficient `E`. -/
def q4CrossedStrongShellConstant (q A E : Real) : ENNReal :=
  (ENNReal.ofReal q *
    (4 * ENNReal.ofReal E *
      ((ENNReal.ofReal (q - 2))⁻¹ *
        (ENNReal.ofReal (2 * A)) ^ (q - 2)))) ^ q⁻¹

/-- Homogeneous `L^p → L^q` form of the preceding literal selected-shell
estimate.  Its shell-dependent constant is displayed rather than hidden so
that the frequency and gap exponents can be read off before dyadic
reassembly. -/
theorem q4SelectedKernelTTStarShell_strong_offDiagonal_of_cutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} [SFinite mu]
    (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (hR : Std.Symm R) (D : Real) (hD : 0 <= D)
    (hdegree : forall i ∈ s, ((s.filter (R i)).card : Real) <= D)
    (K : I -> I -> X -> Complex) (rho : X -> I)
    (hrho : forall x, rho x ∈ s) (hrhoMeas : Measurable rho)
    (A : Real) (hA : 0 < A)
    (hkernel : forall i l z, R i l -> ‖K i l z‖ <= A)
    (H : Q4PairwiseL2OperatorBound mu K)
    {p q I0 : Real} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : X -> Complex)
    (hfD : f ∈ q4SelectedCutoffStableDomain mu s R K rho)
    (hfp : Integrable (fun x => ‖f x‖ ^ p) mu)
    (hI0 : I0 = ∫ x, ‖f x‖ ^ p ∂mu) (hI0pos : 0 < I0) :
    eLpNorm (q4SelectedKernelTTStarShell mu s R K rho f) (ENNReal.ofReal q) mu <=
      q4CrossedStrongShellConstant q A ((H.B * D) ^ 2) *
        eLpNorm f (ENNReal.ofReal p) mu := by
  let cutoff : Real := 2 * A * I0
  have hraw := q4SelectedKernelTTStarShell_crossed_strong_of_cutoffStableDomain
    s R hR D hD hdegree K rho hrho hrhoMeas A hA hkernel H
    hp1 hp2 hq f hfD hfp hI0 hI0pos (show cutoff = 2 * A * I0 by rfl)
  have hinput := q4_lintegral_norm_rpow_eq_ofReal_integral mu f (by linarith)
    hfp hI0
  have hmoment := q4_crossed_power_moment_of_hard_cutoff_bound
    mu (q4SelectedKernelTTStarShell mu s R K rho f) f
    (ENNReal.ofReal ((H.B * D) ^ 2)) hA hI0pos hp1 hp2 hq hinput
    (by simpa only [cutoff] using hraw)
  exact q4_eLpNorm_le_of_crossed_power_moment
    mu (q4SelectedKernelTTStarShell mu s R K rho f) f
    (by linarith) (by
      rw [hq]
      have hpminus : 0 < p - 1 := by linarith
      exact div_pos (by linarith) hpminus)
    (q4CrossedStrongShellConstant q A ((H.B * D) ^ 2)) hmoment

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
