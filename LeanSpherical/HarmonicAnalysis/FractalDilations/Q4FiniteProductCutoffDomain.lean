/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4ActivePairwiseL2
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4FiniteProductStrong

/-!
# A cutoff-stable physical domain for literal finite-product `TT*` shells

The crossed interpolation in the `Q4` argument is applied to a literal
finite product kernel, rather than to an abstract matrix.  The old product
shell domain recorded only Bochner integrability of each displayed pair; that
is enough for additivity, but not for the square endpoint.  This file records
the small physical `L¹ ∩ L²` carrier on which both endpoints are genuinely
available.

The carrier is deliberately stated in terms of the actual counting product
and its actual active fibres.  Its two hard power cutoffs stay in the carrier,
and the output square estimate below is derived from a pairwise Fourier/L²
bound.  Thus none of the `hDinput` / `hDoutput` assumptions in the older
generic crossed-endpoint package are used by the new API.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Set ENNReal
open scoped BigOperators

noncomputable section

/-- The cutoff-stable domain for a literal finite-product kernel shell.

Besides the pairwise Bochner condition needed to interpret every displayed
physical convolution, an element has product `L¹` and square-integrability,
and every active fibre is in physical `L¹ ∩ L²`.  The fibre conditions are
what allow the proved physical/Fourier pairwise `L²` comparison to be used
without postulating an output regularity hypothesis. -/
def q4FiniteProductCutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (mu : Measure X) (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex) : Set (X × {i // i ∈ s} -> Complex) :=
  {g | Measurable g /\
    Integrable g (q4FiniteProductCountingMeasure mu s) /\
    Integrable (fun z => ‖g z‖ ^ (2 : Nat))
      (q4FiniteProductCountingMeasure mu s) /\
    (∀ i ∈ s, Integrable (q4FiniteProductToFibres s g i) mu /\
      MemLp (q4FiniteProductToFibres s g i) 2 mu) /\
    g ∈ q4FiniteProductShellDomain mu s R K}

theorem q4FiniteProductCutoffStableDomain.measurable
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} {s : Finset I} {R : I -> I -> Prop} [DecidableRel R]
    {K : I -> I -> X -> Complex} {g : X × {i // i ∈ s} -> Complex}
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K) :
    Measurable g :=
  hg.1

theorem q4FiniteProductCutoffStableDomain.integrable
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} {s : Finset I} {R : I -> I -> Prop} [DecidableRel R]
    {K : I -> I -> X -> Complex} {g : X × {i // i ∈ s} -> Complex}
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K) :
    Integrable g (q4FiniteProductCountingMeasure mu s) :=
  hg.2.1

theorem q4FiniteProductCutoffStableDomain.integrable_norm_sq
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} {s : Finset I} {R : I -> I -> Prop} [DecidableRel R]
    {K : I -> I -> X -> Complex} {g : X × {i // i ∈ s} -> Complex}
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K) :
    Integrable (fun z => ‖g z‖ ^ (2 : Nat))
      (q4FiniteProductCountingMeasure mu s) :=
  hg.2.2.1

theorem q4FiniteProductCutoffStableDomain.fibre_integrable
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} {s : Finset I} {R : I -> I -> Prop} [DecidableRel R]
    {K : I -> I -> X -> Complex} {g : X × {i // i ∈ s} -> Complex}
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K)
    (i : I) (hi : i ∈ s) :
    Integrable (q4FiniteProductToFibres s g i) mu :=
  (hg.2.2.2.1 i hi).1

theorem q4FiniteProductCutoffStableDomain.fibre_memLp_two
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} {s : Finset I} {R : I -> I -> Prop} [DecidableRel R]
    {K : I -> I -> X -> Complex} {g : X × {i // i ∈ s} -> Complex}
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K)
    (i : I) (hi : i ∈ s) :
    MemLp (q4FiniteProductToFibres s g i) 2 mu :=
  (hg.2.2.2.1 i hi).2

theorem q4FiniteProductCutoffStableDomain.pairwise
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} {s : Finset I} {R : I -> I -> Prop} [DecidableRel R]
    {K : I -> I -> X -> Complex} {g : X × {i // i ∈ s} -> Complex}
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K) :
    g ∈ q4FiniteProductShellDomain mu s R K :=
  hg.2.2.2.2

/-- Fibres outside the finite active carrier are identically zero, so the
physical `L¹ ∩ L²` facts above extend harmlessly to every index. -/
theorem q4FiniteProductCutoffStableDomain.fibre_integrable_all
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} {s : Finset I} {R : I -> I -> Prop} [DecidableRel R]
    {K : I -> I -> X -> Complex} {g : X × {i // i ∈ s} -> Complex}
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K) (i : I) :
    Integrable (q4FiniteProductToFibres s g i) mu := by
  by_cases hi : i ∈ s
  · exact hg.fibre_integrable i hi
  · simp [q4FiniteProductToFibres, hi]

theorem q4FiniteProductCutoffStableDomain.fibre_memLp_two_all
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} {s : Finset I} {R : I -> I -> Prop} [DecidableRel R]
    {K : I -> I -> X -> Complex} {g : X × {i // i ∈ s} -> Complex}
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K) (i : I) :
    MemLp (q4FiniteProductToFibres s g i) 2 mu := by
  by_cases hi : i ∈ s
  · exact hg.fibre_memLp_two i hi
  · simp [q4FiniteProductToFibres, hi]

/-- The low hard power cutoff preserves the actual finite-product carrier. -/
theorem q4PowerCutoffLow_mem_q4FiniteProductCutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (mu : Measure X) (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (Kern : I -> I -> X -> Complex)
    {p cutoff t : Real} (hp1 : 1 < p)
    (g : X × {i // i ∈ s} -> Complex)
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R Kern) :
    q4PowerCutoffLow p cutoff t g ∈
      q4FiniteProductCutoffStableDomain mu s R Kern := by
  let P : Set (X × {i // i ∈ s}) :=
    {z | t * ‖g z‖ ^ (p - 1) ≤ cutoff}
  have hP : MeasurableSet P := by
    simpa only [P] using measurableSet_q4PowerCutoff hp1 g hg.measurable
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [P, q4PowerCutoffLow] using hg.measurable.indicator hP
  · simpa only [P, q4PowerCutoffLow] using hg.integrable.indicator hP
  · have hsq : (fun z => ‖q4PowerCutoffLow p cutoff t g z‖ ^ (2 : Nat)) =
        P.indicator (fun z => ‖g z‖ ^ (2 : Nat)) := by
      funext z
      by_cases hz : z ∈ P <;> simp [P, q4PowerCutoffLow, hz]
    rw [hsq]
    exact hg.integrable_norm_sq.indicator hP
  · intro i hi
    let Pi : Set X := {x | t * ‖q4FiniteProductToFibres s g i x‖ ^ (p - 1) ≤ cutoff}
    have hPi : MeasurableSet Pi := by
      simpa only [Pi] using measurableSet_q4PowerCutoff hp1
        (q4FiniteProductToFibres s g i)
        (measurable_q4FiniteProductToFibres s g hg.measurable i)
    have hfib : q4FiniteProductToFibres s (q4PowerCutoffLow p cutoff t g) i =
        Pi.indicator (q4FiniteProductToFibres s g i) := by
      funext x
      exact q4FiniteProductToFibres_powerCutoffLow s p cutoff t g i x
    constructor
    · rw [hfib]
      exact (hg.fibre_integrable i hi).indicator hPi
    · rw [hfib]
      exact (hg.fibre_memLp_two i hi).indicator hPi
  · exact q4PowerCutoffLow_mem_q4FiniteProductShellDomain
      mu s R Kern hp1 cutoff t g hg.measurable hg.pairwise

/-- The complementary high hard power cutoff preserves the actual
finite-product carrier. -/
theorem q4PowerCutoffHigh_mem_q4FiniteProductCutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (mu : Measure X) (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (Kern : I -> I -> X -> Complex)
    {p cutoff t : Real} (hp1 : 1 < p)
    (g : X × {i // i ∈ s} -> Complex)
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R Kern) :
    q4PowerCutoffHigh p cutoff t g ∈
      q4FiniteProductCutoffStableDomain mu s R Kern := by
  let P : Set (X × {i // i ∈ s}) :=
    {z | t * ‖g z‖ ^ (p - 1) ≤ cutoff}
  have hP : MeasurableSet P := by
    simpa only [P] using measurableSet_q4PowerCutoff hp1 g hg.measurable
  have hhigh : q4PowerCutoffHigh p cutoff t g = Pᶜ.indicator g := by
    funext z
    dsimp only [P]
    by_cases hz : t * ‖g z‖ ^ (p - 1) ≤ cutoff <;>
      simp [q4PowerCutoffHigh, q4PowerCutoffLow, hz]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hhigh]
    exact hg.measurable.indicator hP.compl
  · rw [hhigh]
    exact hg.integrable.indicator hP.compl
  · have hsq : (fun z => ‖q4PowerCutoffHigh p cutoff t g z‖ ^ (2 : Nat)) =
        Pᶜ.indicator (fun z => ‖g z‖ ^ (2 : Nat)) := by
      funext z
      rw [hhigh]
      by_cases hz : z ∈ P <;> simp [hz]
    rw [hsq]
    exact hg.integrable_norm_sq.indicator hP.compl
  · intro i hi
    let Pi : Set X := {x | t * ‖q4FiniteProductToFibres s g i x‖ ^ (p - 1) ≤ cutoff}
    have hPi : MeasurableSet Pi := by
      simpa only [Pi] using measurableSet_q4PowerCutoff hp1
        (q4FiniteProductToFibres s g i)
        (measurable_q4FiniteProductToFibres s g hg.measurable i)
    have hfib : q4FiniteProductToFibres s (q4PowerCutoffHigh p cutoff t g) i =
        Piᶜ.indicator (q4FiniteProductToFibres s g i) := by
      funext x
      exact q4FiniteProductToFibres_powerCutoffHigh s p cutoff t g i x
    constructor
    · rw [hfib]
      exact (hg.fibre_integrable i hi).indicator hPi.compl
    · rw [hfib]
      exact (hg.fibre_memLp_two i hi).indicator hPi.compl
  · exact q4PowerCutoffHigh_mem_q4FiniteProductShellDomain
      mu s R Kern hp1 cutoff t g hg.measurable hg.pairwise

/-- If every fibre of a finite counting product is a.e.-strongly
measurable, then the actual product field is a.e.-strongly measurable.

This elementary finite-fibre lemma is deliberately proved here rather than
being hidden behind a product-domain assumption.  It is what lets the
physical output of the literal finite shell inherit measurability from the
proved `L²` estimates on its displayed fibres. -/
theorem aestronglyMeasurable_q4FiniteProduct_of_fibres
    {I X E : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    [NormedAddCommGroup E]
    (mu : Measure X) (s : Finset I)
    (g : X × {i // i ∈ s} -> E)
    (hg : forall i : {i // i ∈ s},
      AEStronglyMeasurable (fun x => g (x, i)) mu) :
    AEStronglyMeasurable g (q4FiniteProductCountingMeasure mu s) := by
  classical
  change AEStronglyMeasurable g (mu.prod Measure.count)
  let F : {i // i ∈ s} -> X × {i // i ∈ s} -> E := fun i =>
    {z | z.2 = i}.indicator (fun z => g (z.1, i))
  have hF (i : {i // i ∈ s}) :
      AEStronglyMeasurable (F i) (mu.prod Measure.count) := by
    have hbase : AEStronglyMeasurable (fun z : X × {i // i ∈ s} =>
        g (z.1, i)) (mu.prod Measure.count) := by
      simpa only [Function.comp_apply] using
        (hg i).comp_quasiMeasurePreserving
          (quasiMeasurePreserving_fst (μ := mu) (ν := Measure.count))
    exact hbase.indicator (measurable_snd (measurableSet_singleton i))
  have hsum : (∑ i : {i // i ∈ s}, F i) = g := by
    funext z
    simp [F]
  rw [← hsum]
  exact Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hF i)

/-- Integrability on a finite physical-times-counting product follows from
integrability of its displayed fibres. -/
theorem integrable_q4FiniteProduct_of_fibres
    {I X E : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    [NormedAddCommGroup E] {mu : Measure X} [SFinite mu]
    (s : Finset I) (g : X × {i // i ∈ s} -> E)
    (hg : AEStronglyMeasurable g (q4FiniteProductCountingMeasure mu s))
    (hfib : forall i : {i // i ∈ s}, Integrable (fun x => g (x, i)) mu) :
    Integrable g (q4FiniteProductCountingMeasure mu s) := by
  change AEStronglyMeasurable g (mu.prod Measure.count) at hg
  change Integrable g (mu.prod Measure.count)
  refine (integrable_prod_iff' hg).mpr ?_
  refine ⟨Filter.Eventually.of_forall hfib, ?_⟩
  rw [integrable_count_iff]
  exact Summable.of_finite

/-- The square of a finite product field is integrable when each physical
fibre is in `L²`. -/
theorem integrable_norm_sq_q4FiniteProduct_of_fibres
    {I X : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} [SFinite mu]
    (s : Finset I) (g : X × {i // i ∈ s} -> Complex)
    (hg : AEStronglyMeasurable g (q4FiniteProductCountingMeasure mu s))
    (hfib : forall i : {i // i ∈ s}, MemLp (fun x => g (x, i)) 2 mu) :
    Integrable (fun z => ‖g z‖ ^ (2 : Nat))
      (q4FiniteProductCountingMeasure mu s) := by
  apply integrable_q4FiniteProduct_of_fibres s
    (fun z => ‖g z‖ ^ (2 : Nat))
  · exact hg.norm.pow 2
  · intro i
    exact integrable_norm_sq_of_memLp_two _ (hfib i)

/-- The finite counting-product/fibre-energy identity only needs a.e.
strong measurability.  The older strict-measurability formulation is
recovered by choosing its canonical measurable representative; count
measure then transports the representative equality to every active
fibre. -/
theorem q4FiniteProductCountingMeasure_integral_norm_sq_eq_fibreL2Energy_of_aestronglyMeasurable
    {I X : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} [SFinite mu] (s : Finset I)
    (g : X × {i // i ∈ s} -> Complex)
    (hgmeas : AEStronglyMeasurable g (q4FiniteProductCountingMeasure mu s))
    (hg : Integrable (fun z => ‖g z‖ ^ (2 : Nat))
      (q4FiniteProductCountingMeasure mu s))
    (hfib : forall i ∈ s,
      Integrable (fun x => ‖q4FiniteProductToFibres s g i x‖ ^ (2 : Nat)) mu) :
    (∫ z, ‖g z‖ ^ (2 : Nat) ∂q4FiniteProductCountingMeasure mu s) =
      q4FibreL2Energy mu s (q4FiniteProductToFibres s g) := by
  let g' : X × {i // i ∈ s} -> Complex := hgmeas.aemeasurable.mk g
  have hg'meas : Measurable g' := hgmeas.aemeasurable.measurable_mk
  have heq : g =ᵐ[q4FiniteProductCountingMeasure mu s] g' :=
    hgmeas.aemeasurable.ae_eq_mk
  have hsqeq : (fun z => ‖g z‖ ^ (2 : Nat)) =ᵐ[q4FiniteProductCountingMeasure mu s]
      (fun z => ‖g' z‖ ^ (2 : Nat)) :=
    heq.fun_comp (fun w : Complex => ‖w‖ ^ (2 : Nat))
  have hg' : Integrable (fun z => ‖g' z‖ ^ (2 : Nat))
      (q4FiniteProductCountingMeasure mu s) :=
    hg.congr hsqeq
  have hfibEq (i : I) (hi : i ∈ s) :
      q4FiniteProductToFibres s g i =ᵐ[mu]
        q4FiniteProductToFibres s g' i := by
    change g =ᵐ[mu.prod Measure.count] g' at heq
    have hcurried := ae_ae_eq_curry_of_prod heq
    filter_upwards [hcurried] with x hx
    simpa [q4FiniteProductToFibres, hi] using
      (ae_count_iff.mp hx ⟨i, hi⟩)
  have hfib' (i : I) (hi : i ∈ s) :
      Integrable (fun x => ‖q4FiniteProductToFibres s g' i x‖ ^ (2 : Nat)) mu :=
    (hfib i hi).congr
      ((hfibEq i hi).fun_comp (fun w : Complex => ‖w‖ ^ (2 : Nat)))
  calc
    (∫ z, ‖g z‖ ^ (2 : Nat) ∂q4FiniteProductCountingMeasure mu s) =
        ∫ z, ‖g' z‖ ^ (2 : Nat) ∂q4FiniteProductCountingMeasure mu s :=
      integral_congr_ae hsqeq
    _ = q4FibreL2Energy mu s (q4FiniteProductToFibres s g') :=
      q4FiniteProductCountingMeasure_integral_norm_sq_eq_fibreL2Energy
        mu s g' hg'meas hg' hfib'
    _ = q4FibreL2Energy mu s (q4FiniteProductToFibres s g) := by
      unfold q4FibreL2Energy
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_congr_ae
        ((hfibEq i hi).fun_comp (fun w : Complex => ‖w‖ ^ (2 : Nat)))).symm

/-- The physical product-shell output has an `L²` representative on every
active fibre, obtained solely from the literal pairwise `L²` bound. -/
theorem memLp_two_q4FiniteProductKernelShell_fibre_of_pairwise_bound
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex)
    (H : Q4PairwiseL2OperatorBound mu K)
    (g : X × {i // i ∈ s} -> Complex)
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K)
    (i : I) (hi : i ∈ s) :
    MemLp (q4FiniteProductToFibres s
      (q4FiniteProductKernelShell mu s R K g) i) 2 mu := by
  have hshell : MemLp
      (q4KernelTTStarShell mu s R K (q4FiniteProductToFibres s g) i) 2 mu := by
    unfold q4KernelTTStarShell
    exact memLp_finsetSum (μ := mu) (p := 2) (s.filter (R i))
      (f := fun l => q4PairwiseKernelApply mu K i l
        (q4FiniteProductToFibres s g l))
      (fun l hl => H.memLp i l _
        (hg.fibre_integrable_all l) (hg.fibre_memLp_two_all l))
  simpa only [q4FiniteProductToFibres, dif_pos hi,
    q4FiniteProductKernelShell] using hshell

/-- The literal finite-product shell is a.e.-strongly measurable once its
physical pair operators satisfy the proved pairwise `L²` estimate.  No
measurability assertion about an abstract output operator is used. -/
theorem aestronglyMeasurable_q4FiniteProductKernelShell_of_pairwise_bound
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex)
    (H : Q4PairwiseL2OperatorBound mu K)
    (g : X × {i // i ∈ s} -> Complex)
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K) :
    AEStronglyMeasurable (q4FiniteProductKernelShell mu s R K g)
      (q4FiniteProductCountingMeasure mu s) := by
  apply aestronglyMeasurable_q4FiniteProduct_of_fibres mu s
    (q4FiniteProductKernelShell mu s R K g)
  intro i
  simpa only [q4FiniteProductToFibres, dif_pos i.property] using
    (memLp_two_q4FiniteProductKernelShell_fibre_of_pairwise_bound
      s R K H g hg i.1 i.2).aestronglyMeasurable

/-- The literal product output has a square-integrable physical-times-
counting representative, derived from its actual pairwise `L²` endpoint. -/
theorem integrable_norm_sq_q4FiniteProductKernelShell_of_pairwise_bound
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} [SFinite mu] (s : Finset I) (R : I -> I -> Prop)
    [DecidableRel R] (K : I -> I -> X -> Complex)
    (H : Q4PairwiseL2OperatorBound mu K)
    (g : X × {i // i ∈ s} -> Complex)
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K) :
    Integrable (fun z => ‖q4FiniteProductKernelShell mu s R K g z‖ ^ (2 : Nat))
      (q4FiniteProductCountingMeasure mu s) := by
  apply integrable_norm_sq_q4FiniteProduct_of_fibres s
    (q4FiniteProductKernelShell mu s R K g)
  · exact aestronglyMeasurable_q4FiniteProductKernelShell_of_pairwise_bound
      s R K H g hg
  · intro i
    simpa only [q4FiniteProductToFibres, dif_pos i.property] using
      memLp_two_q4FiniteProductKernelShell_fibre_of_pairwise_bound
        s R K H g hg i.1 i.2

/-- The square endpoint for a literal finite product shell.  Its proof is
the finite graph `TT*` estimate on physical fibres, followed by the concrete
counting-measure/Fubini reassembly above. -/
theorem q4FiniteProductKernelShell_energy_le_of_cutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} [SFinite mu] (s : Finset I) (R : I -> I -> Prop)
    [DecidableRel R] (hR : Std.Symm R) (D : Real) (hD : 0 <= D)
    (hdegree : forall i ∈ s, ((s.filter (R i)).card : Real) <= D)
    (K : I -> I -> X -> Complex) (H : Q4PairwiseL2OperatorBound mu K)
    (g : X × {i // i ∈ s} -> Complex)
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K) :
    (∫ z, ‖q4FiniteProductKernelShell mu s R K g z‖ ^ (2 : Nat)
      ∂q4FiniteProductCountingMeasure mu s) <=
      (H.B * D) ^ 2 *
        ∫ z, ‖g z‖ ^ (2 : Nat) ∂q4FiniteProductCountingMeasure mu s := by
  have houtFib (i : I) (hi : i ∈ s) :
      MemLp (q4FiniteProductToFibres s
        (q4FiniteProductKernelShell mu s R K g) i) 2 mu :=
    memLp_two_q4FiniteProductKernelShell_fibre_of_pairwise_bound
      s R K H g hg i hi
  have houtFibSq (i : I) (hi : i ∈ s) :
      Integrable (fun x => ‖q4FiniteProductToFibres s
        (q4FiniteProductKernelShell mu s R K g) i x‖ ^ (2 : Nat)) mu :=
    integrable_norm_sq_of_memLp_two _ (houtFib i hi)
  have houtAE : AEStronglyMeasurable
      (q4FiniteProductKernelShell mu s R K g)
      (q4FiniteProductCountingMeasure mu s) :=
    aestronglyMeasurable_q4FiniteProductKernelShell_of_pairwise_bound
      s R K H g hg
  have houtSq : Integrable
      (fun z => ‖q4FiniteProductKernelShell mu s R K g z‖ ^ (2 : Nat))
      (q4FiniteProductCountingMeasure mu s) :=
    integrable_norm_sq_q4FiniteProductKernelShell_of_pairwise_bound
      s R K H g hg
  have hinFibSq (i : I) (hi : i ∈ s) :
      Integrable (fun x => ‖q4FiniteProductToFibres s g i x‖ ^ (2 : Nat)) mu :=
    integrable_norm_sq_of_memLp_two _ (hg.fibre_memLp_two i hi)
  have henergy := q4FibreL2Energy_kernelShell_le_of_pairwise_bound_on_relation
    mu s R hR D hD hdegree K (q4FiniteProductToFibres s g) H.nonneg
    (fun i hi => hg.fibre_memLp_two i hi)
    (fun i l hil => H.memLp i l _
      (hg.fibre_integrable_all l) (hg.fibre_memLp_two_all l))
    (fun i l hil => H.bound i l _
      (hg.fibre_integrable_all l) (hg.fibre_memLp_two_all l))
  calc
    (∫ z, ‖q4FiniteProductKernelShell mu s R K g z‖ ^ (2 : Nat)
      ∂q4FiniteProductCountingMeasure mu s) =
        q4FibreL2Energy mu s (q4FiniteProductToFibres s
          (q4FiniteProductKernelShell mu s R K g)) :=
      q4FiniteProductCountingMeasure_integral_norm_sq_eq_fibreL2Energy_of_aestronglyMeasurable
        s (q4FiniteProductKernelShell mu s R K g) houtAE houtSq houtFibSq
    _ = q4FibreL2Energy mu s
        (q4KernelTTStarShell mu s R K (q4FiniteProductToFibres s g)) :=
      q4FibreL2Energy_toFibres_kernelShell_eq mu s R K g
    _ <= (H.B * D) ^ 2 * q4FibreL2Energy mu s
        (q4FiniteProductToFibres s g) := henergy
    _ = (H.B * D) ^ 2 *
        ∫ z, ‖g z‖ ^ (2 : Nat) ∂q4FiniteProductCountingMeasure mu s := by
      rw [q4FiniteProductCountingMeasure_integral_norm_sq_eq_fibreL2Energy_of_aestronglyMeasurable
        s g hg.measurable.aestronglyMeasurable hg.integrable_norm_sq hinFibSq]

/-- A relation-local pair-kernel estimate is a literal `L¹ -> L∞` estimate
for the finite product shell.  Off-relation entries are cut to zero before
the existing physical finite-product estimate is invoked, so no fictitious
bound is requested outside the active dyadic level. -/
theorem norm_q4FiniteProductKernelShell_le_of_bound_on_relation
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex) (A : Real) (hA : 0 <= A)
    (hkernel : forall i l z, R i l -> ‖K i l z‖ <= A)
    (g : X × {i // i ∈ s} -> Complex)
    (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K)
    (z : X × {i // i ∈ s}) :
    ‖q4FiniteProductKernelShell mu s R K g z‖ <=
      A * ∫ w, ‖g w‖ ∂q4FiniteProductCountingMeasure mu s := by
  let Kcut : I -> I -> X -> Complex := fun i l x =>
    if R i l then K i l x else 0
  have hKcut : forall i l x, ‖Kcut i l x‖ <= A := by
    intro i l x
    by_cases hil : R i l
    · simpa only [Kcut, if_pos hil] using hkernel i l x hil
    · simpa only [Kcut, if_neg hil, norm_zero] using hA
  have hmeasCut : forall i l x, AEStronglyMeasurable
      (fun y => Kcut i l (x - y) * q4FiniteProductToFibres s g l y) mu := by
    intro i l x
    by_cases hil : R i l
    · simpa only [Kcut, if_pos hil] using (hg.pairwise i l x hil).aestronglyMeasurable
    · simpa only [Kcut, if_neg hil, zero_mul] using
        (aestronglyMeasurable_zero : AEStronglyMeasurable
          (fun _ : X => (0 : Complex)) mu)
  have hshell : q4FiniteProductKernelShell mu s R K g =
      q4FiniteProductKernelShell mu s R Kcut g := by
    funext w
    unfold q4FiniteProductKernelShell q4KernelTTStarShell
    apply Finset.sum_congr rfl
    intro l hl
    have hrel : R w.2.1 l := (Finset.mem_filter.mp hl).2
    simp only [Kcut, if_pos hrel]
  rw [hshell]
  exact norm_q4FiniteProductKernelShell_le_of_bound mu s R Kcut g hA
    hg.measurable hg.integrable
    (fun l hl => hg.fibre_integrable l hl) hmeasCut hKcut z

/-- The crossed Marcinkiewicz estimate for one literal finite-product shell.
All endpoint facts are derived from the actual physical kernel, the actual
pairwise Fourier/physical `L²` comparison, and the finite relation degree.
In particular, the theorem contains none of the former abstract output- or
input-domain regularity premises. -/
theorem q4FiniteProductKernelShell_crossed_strong_of_cutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} [SFinite mu] (s : Finset I) (R : I -> I -> Prop)
    [DecidableRel R] (hR : Std.Symm R) (D : Real) (hD : 0 <= D)
    (hdegree : forall i ∈ s, ((s.filter (R i)).card : Real) <= D)
    (K : I -> I -> X -> Complex) (A : Real) (hA : 0 < A)
    (hkernel : forall i l z, R i l -> ‖K i l z‖ <= A)
    (H : Q4PairwiseL2OperatorBound mu K)
    {p q cutoff I0 : Real} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : X × {i // i ∈ s} -> Complex)
    (hfD : f ∈ q4FiniteProductCutoffStableDomain mu s R K)
    (hfp : Integrable (fun z => ‖f z‖ ^ p)
      (q4FiniteProductCountingMeasure mu s))
    (hI0 : I0 = ∫ z, ‖f z‖ ^ p ∂q4FiniteProductCountingMeasure mu s)
    (hI0pos : 0 < I0) (hcutoff : cutoff = 2 * A * I0) :
    (∫⁻ z, ENNReal.ofReal
      (‖q4FiniteProductKernelShell mu s R K f z‖ ^ q)
      ∂q4FiniteProductCountingMeasure mu s) <=
      ENNReal.ofReal q *
        (4 * ENNReal.ofReal ((H.B * D) ^ 2) *
          ((ENNReal.ofReal (q - 2))⁻¹ *
            (ENNReal.ofReal cutoff) ^ (q - 2) *
              ∫⁻ z, (ENNReal.ofReal ‖f z‖) ^ p
                ∂q4FiniteProductCountingMeasure mu s)) := by
  have houtputSq (g : X × {i // i ∈ s} -> Complex)
      (hg : g ∈ q4FiniteProductCutoffStableDomain mu s R K) :
      Integrable (fun z => ‖q4FiniteProductKernelShell mu s R K g z‖ ^ (2 : Nat))
        (q4FiniteProductCountingMeasure mu s) :=
    integrable_norm_sq_q4FiniteProductKernelShell_of_pairwise_bound s R K H g hg
  refine crossed_marcinkiewicz_strong_of_hard_power_cutoff
    (D := q4FiniteProductCutoffStableDomain mu s R K)
    (T := fun g z => ‖q4FiniteProductKernelShell mu s R K g z‖)
    (hT_nonneg := ?_)
    (hT_subadd := ?_)
    (C₁ := A)
    (hC₁ := hA)
    (hstrong_one_top := ?_)
    (C₂ := ENNReal.ofReal ((H.B * D) ^ 2))
    (hweak_two := ?_)
    (p := p) (q := q) (K := cutoff) (I := I0)
    (hp1 := hp1) (hp2 := hp2) (hq := hq)
    (f := f) (hf_norm := hfD.measurable.norm)
    (hTf := ?_)
    (hI := hI0) (hIpos := hI0pos) (hK := hcutoff)
    (hlow_mem := ?_) (hhigh_mem := ?_)
    (hhigh_integrable := ?_) (hhigh_major := ?_)
    (hlowI_meas := ?_)
  · intro g z
    exact norm_nonneg _
  · intro g h hg hh z
    exact norm_q4FiniteProductKernelShell_add_le mu s R K g h
      hg.pairwise hh.pairwise z
  · intro g hg z
    exact norm_q4FiniteProductKernelShell_le_of_bound_on_relation
      s R K A hA.le hkernel g hg z
  · intro g hg r hr
    exact q4_weak_two_of_square_energy g
      (q4FiniteProductKernelShell mu s R K g)
      (aemeasurable_norm_of_integrable_sq
        (q4FiniteProductKernelShell mu s R K g) (houtputSq g hg))
      (houtputSq g hg) hg.integrable_norm_sq (sq_nonneg _)
      (q4FiniteProductKernelShell_energy_le_of_cutoffStableDomain
        s R hR D hD hdegree K H g hg) hr
  · exact aemeasurable_norm_of_integrable_sq
      (q4FiniteProductKernelShell mu s R K f) (houtputSq f hfD)
  · intro t
    exact q4PowerCutoffLow_mem_q4FiniteProductCutoffStableDomain
      mu s R K hp1 f hfD
  · intro t
    exact q4PowerCutoffHigh_mem_q4FiniteProductCutoffStableDomain
      mu s R K hp1 f hfD
  · intro t ht
    exact integrable_q4PowerCutoffHigh_of_integrable hp1 cutoff t f
      hfD.measurable hfD.integrable
  · intro t ht
    exact hfp.const_mul (t / cutoff)
  · exact measurable_lintegral_q4PowerCutoffLow_sq hp1 cutoff f hfD.measurable

/-- Homogeneous strict strong form of the preceding literal finite-product
shell estimate.  This is the finite-product `TT*` certificate consumed by
the active-dyadic maximal reassembly. -/
theorem q4FiniteProductKernelShell_strong_offDiagonal_of_cutoffStableDomain
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    {mu : Measure X} [SFinite mu] (s : Finset I) (R : I -> I -> Prop)
    [DecidableRel R] (hR : Std.Symm R) (D : Real) (hD : 0 <= D)
    (hdegree : forall i ∈ s, ((s.filter (R i)).card : Real) <= D)
    (K : I -> I -> X -> Complex) (A : Real) (hA : 0 < A)
    (hkernel : forall i l z, R i l -> ‖K i l z‖ <= A)
    (H : Q4PairwiseL2OperatorBound mu K)
    {p q I0 : Real} (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (f : X × {i // i ∈ s} -> Complex)
    (hfD : f ∈ q4FiniteProductCutoffStableDomain mu s R K)
    (hfp : Integrable (fun z => ‖f z‖ ^ p)
      (q4FiniteProductCountingMeasure mu s))
    (hI0 : I0 = ∫ z, ‖f z‖ ^ p ∂q4FiniteProductCountingMeasure mu s)
    (hI0pos : 0 < I0) :
    eLpNorm (q4FiniteProductKernelShell mu s R K f) (ENNReal.ofReal q)
      (q4FiniteProductCountingMeasure mu s) <=
      q4CrossedStrongShellConstant q A ((H.B * D) ^ 2) *
        eLpNorm f (ENNReal.ofReal p) (q4FiniteProductCountingMeasure mu s) := by
  let cutoff : Real := 2 * A * I0
  have hraw := q4FiniteProductKernelShell_crossed_strong_of_cutoffStableDomain
    s R hR D hD hdegree K A hA hkernel H hp1 hp2 hq f hfD hfp hI0 hI0pos
    (show cutoff = 2 * A * I0 by rfl)
  have hinput := q4_lintegral_norm_rpow_eq_ofReal_integral
    (q4FiniteProductCountingMeasure mu s) f (by linarith) hfp hI0
  have hmoment := q4_crossed_power_moment_of_hard_cutoff_bound
    (q4FiniteProductCountingMeasure mu s)
    (q4FiniteProductKernelShell mu s R K f) f
    (ENNReal.ofReal ((H.B * D) ^ 2)) hA hI0pos hp1 hp2 hq hinput
    (by simpa only [cutoff] using hraw)
  exact q4_eLpNorm_le_of_crossed_power_moment
    (q4FiniteProductCountingMeasure mu s)
    (q4FiniteProductKernelShell mu s R K f) f
    (by linarith) (by
      rw [hq]
      have hpminus : 0 < p - 1 := by linarith
      exact div_pos (by linarith) hpminus)
    (q4CrossedStrongShellConstant q A ((H.B * D) ^ 2)) hmoment

/-- A compactly localized active-dyadic pair kernel maps any physical
`L¹` fibre to an integrable displayed convolution.  This is the finite-
product version of the selected-fibre fact: the proof uses the literal
Schwartz inverse transform and never turns the pair into an abstract
operator. -/
theorem integrable_q4ActiveDyadicPairKernel_mul_of_compact
    {d : Nat} (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    (j : Nat) (g : Euclidean d -> Complex) (hg : Integrable g volume)
    (i l : Int) (x : Euclidean d) :
    Integrable (fun y => q4ActiveDyadicPairKernel psi j i l (x - y) * g y)
      volume := by
  let k : SchwartzMap (Euclidean d) Complex :=
    𝓕⁻ (q4ActiveDyadicPairMultiplier psi hpsiCompact j i l)
  have hk (z : Euclidean d) : (k : Euclidean d -> Complex) z =
      q4ActiveDyadicPairKernel psi j i l z := by
    simpa only [k, q4ActiveDyadicSchwartzKernel] using
      q4ActiveDyadicSchwartzKernel_eq_pairKernel psi hpsiCompact j i l z
  have hkmeas : AEStronglyMeasurable
      (fun y : Euclidean d => (k : Euclidean d -> Complex) (x - y)) volume :=
    (k.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hkbound : ∀ᵐ y : Euclidean d ∂volume,
      ‖(k : Euclidean d -> Complex) (x - y)‖ <=
        ‖k.toBoundedContinuousFunction‖ :=
    Filter.Eventually.of_forall fun y => by
      change ‖k.toBoundedContinuousFunction (x - y)‖ <=
        ‖k.toBoundedContinuousFunction‖
      exact BoundedContinuousFunction.norm_coe_le_norm _ _
  have hprod := hg.bdd_mul hkmeas hkbound
  refine hprod.congr (Filter.Eventually.of_forall fun y => ?_)
  rw [hk (x - y)]

/-- Ordinary `L¹ ∩ L²` regularity of an actual finite active product field
places it in every literal active-dyadic level domain.  The pairwise
Bochner condition is discharged from the compact Schwartz realization of
the active pair kernel. -/
theorem mem_q4FiniteProductCutoffStableDomain_activeDyadic_of_regular
    {d : Nat} (E : Set Real) (j : Nat)
    (R : Int -> Int -> Prop) [DecidableRel R]
    (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    (g : Euclidean d × {i // i ∈ activeDyadicIndices E j} -> Complex)
    (hgmeas : Measurable g)
    (hgint : Integrable g (q4ActiveDyadicProductCountingMeasure d E j))
    (hgsq : Integrable (fun z => ‖g z‖ ^ (2 : Nat))
      (q4ActiveDyadicProductCountingMeasure d E j))
    (hfib : forall i ∈ activeDyadicIndices E j,
      Integrable (q4FiniteProductToFibres (activeDyadicIndices E j) g i) volume /\
        MemLp (q4FiniteProductToFibres (activeDyadicIndices E j) g i) 2 volume) :
    g ∈ q4FiniteProductCutoffStableDomain volume (activeDyadicIndices E j) R
      (q4ActiveDyadicPairKernel psi j) := by
  refine ⟨hgmeas, hgint, hgsq, hfib, ?_⟩
  intro i l x hil
  apply integrable_q4ActiveDyadicPairKernel_mul_of_compact psi hpsiCompact j
  by_cases hl : l ∈ activeDyadicIndices E j
  · exact (hfib l hl).1
  · simp [q4FiniteProductToFibres, hl]

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
