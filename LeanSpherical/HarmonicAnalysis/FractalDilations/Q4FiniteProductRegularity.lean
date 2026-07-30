/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4FiniteProductCutoffDomain

/-!
# Regularity of literal finite fibre products

The `Q4` product kernel is evaluated on the actual counting product
`R^d × s`.  This small file packages the elementary finite-fibre facts that
turn continuous `L¹ ∩ L²` fibres (and their finite power moments) into the
literal regularity hypotheses of the physical shell theorem.  In particular,
these facts do not hide an input-membership premise in a later maximal
estimate.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- A finite family of continuous physical fibres defines a measurable
function on the literal product with counting measure. -/
theorem measurable_q4FibresToFiniteProduct_of_continuous
    {d : Nat} (s : Finset Int) (g : Int -> Euclidean d -> Complex)
    (hg : forall i, Continuous (g i)) :
    Measurable (q4FibresToFiniteProduct s g) := by
  classical
  let F : {i // i ∈ s} ->
      Euclidean d × {i // i ∈ s} -> Complex := fun i =>
    {z | z.2 = i}.indicator (fun z => g i.1 z.1)
  have hF (i : {i // i ∈ s}) : Measurable (F i) := by
    have hbase : Measurable (fun z : Euclidean d × {i // i ∈ s} =>
        g i.1 z.1) :=
      (hg i.1).measurable.comp measurable_fst
    exact hbase.indicator (measurable_snd (measurableSet_singleton i))
  have hsum : (∑ i : {i // i ∈ s}, F i) = q4FibresToFiniteProduct s g := by
    funext z
    simp [F, q4FibresToFiniteProduct]
  rw [← hsum]
  exact Finset.measurable_sum Finset.univ (fun i _ => hF i)

/-- Integrability of each displayed active fibre gives integrability on the
literal physical-times-counting product. -/
theorem integrable_q4FibresToFiniteProduct_of_fibres
    {d : Nat} (s : Finset Int) (g : Int -> Euclidean d -> Complex)
    (hgmeas : Measurable (q4FibresToFiniteProduct s g))
    (hg : forall i ∈ s, Integrable (g i) volume) :
    Integrable (q4FibresToFiniteProduct s g)
      (q4FiniteProductCountingMeasure volume s) := by
  apply integrable_q4FiniteProduct_of_fibres s (q4FibresToFiniteProduct s g)
    hgmeas.aestronglyMeasurable
  intro i
  simpa only [q4FibresToFiniteProduct] using hg i.1 i.2

/-- Square-integrability of each displayed fibre gives an integrable square
on the literal finite product. -/
theorem integrable_norm_sq_q4FibresToFiniteProduct_of_fibres
    {d : Nat} (s : Finset Int) (g : Int -> Euclidean d -> Complex)
    (hgmeas : Measurable (q4FibresToFiniteProduct s g))
    (hg : forall i ∈ s, MemLp (g i) 2 volume) :
    Integrable (fun z => ‖q4FibresToFiniteProduct s g z‖ ^ (2 : Nat))
      (q4FiniteProductCountingMeasure volume s) := by
  apply integrable_norm_sq_q4FiniteProduct_of_fibres s
    (q4FibresToFiniteProduct s g) hgmeas.aestronglyMeasurable
  intro i
  simpa only [q4FibresToFiniteProduct] using hg i.1 i.2

/-- A finite real-power moment is reassembled exactly from its active
fibres.  The nonnegative exponent is the only condition needed for the
measurability of the power. -/
theorem integrable_norm_rpow_q4FibresToFiniteProduct_of_fibres
    {d : Nat} (s : Finset Int) (g : Int -> Euclidean d -> Complex)
    (hgmeas : Measurable (q4FibresToFiniteProduct s g))
    {p : Real} (hp : 0 <= p)
    (hg : forall i ∈ s, Integrable (fun x => ‖g i x‖ ^ p) volume) :
    Integrable (fun z => ‖q4FibresToFiniteProduct s g z‖ ^ p)
      (q4FiniteProductCountingMeasure volume s) := by
  apply integrable_q4FiniteProduct_of_fibres s
    (fun z => ‖q4FibresToFiniteProduct s g z‖ ^ p)
  · exact ((continuous_id.rpow_const (fun _ => Or.inr hp)).measurable.comp
      hgmeas.norm).aestronglyMeasurable
  · intro i
    simpa only [q4FibresToFiniteProduct] using hg i.1 i.2

/-- On an active fibre, product-to-fibres is definitionally the original
family.  Naming this elementary identity keeps later physical-domain proofs
free of index coercion bookkeeping. -/
theorem q4FiniteProductToFibres_q4FibresToFiniteProduct_apply
    {d : Nat} (s : Finset Int) (g : Int -> Euclidean d -> Complex)
    (i : Int) (hi : i ∈ s) (x : Euclidean d) :
    q4FiniteProductToFibres s (q4FibresToFiniteProduct s g) i x = g i x :=
  q4FiniteProductToFibres_fibresToProduct_apply s g i hi x

/-- Almost-everywhere equality on the literal physical-times-counting product
restricts to every active physical fibre.  Finite/counting products have no
exceptional active index, which is why this is an honest fibrewise statement
rather than merely an almost-everywhere statement in the index. -/
theorem q4FiniteProductToFibres_ae_eq_of_ae_eq_product
    {I X : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (mu : Measure X) (s : Finset I)
    (g h : X × {i // i ∈ s} -> Complex)
    (heq : g =ᵐ[q4FiniteProductCountingMeasure mu s] h)
    (i : I) (hi : i ∈ s) :
    q4FiniteProductToFibres s g i =ᵐ[mu]
      q4FiniteProductToFibres s h i := by
  change g =ᵐ[mu.prod Measure.count] h at heq
  have hcurried := ae_ae_eq_curry_of_prod heq
  filter_upwards [hcurried] with x hx
  simpa [q4FiniteProductToFibres, hi] using
    (ae_count_iff.mp hx ⟨i, hi⟩)

/-- Fibre moments are invariant under almost-everywhere equality of literal
finite product fields.  This lets a physical convolution shell be replaced
by its canonical measurable representative without changing the numerical
quantity used in the `TT*` diagonal. -/
theorem q4FibreLpMoment_toFibres_eq_of_ae_eq_product
    {I X : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (mu : Measure X) (s : Finset I)
    (g h : X × {i // i ∈ s} -> Complex)
    (heq : g =ᵐ[q4FiniteProductCountingMeasure mu s] h) (q : Real) :
    q4FibreLpMoment mu s q (q4FiniteProductToFibres s g) =
      q4FibreLpMoment mu s q (q4FiniteProductToFibres s h) := by
  unfold q4FibreLpMoment
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [q4FiniteProductToFibres_ae_eq_of_ae_eq_product
    mu s g h heq i hi] with x hx
  rw [hx]

/-- Integrability of a real power on a finite physical-times-counting
product restricts to every active fibre.  This is the Fubini fact needed to
turn the literal product strong estimate back into finite fibre moments. -/
theorem integrable_norm_rpow_q4FiniteProductToFibres_of_integrable
    {I X : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (mu : Measure X) [SFinite mu] (s : Finset I)
    (g : X × {i // i ∈ s} -> Complex) {p : Real}
    (hg : Integrable (fun z => ‖g z‖ ^ p)
      (q4FiniteProductCountingMeasure mu s))
    (i : I) (hi : i ∈ s) :
    Integrable (fun x => ‖q4FiniteProductToFibres s g i x‖ ^ p) mu := by
  change Integrable (fun z => ‖g z‖ ^ p) (mu.prod Measure.count) at hg
  have hfib := ae_count_iff.mp hg.prod_left_ae ⟨i, hi⟩
  simpa [q4FiniteProductToFibres, hi] using hfib

/-- A literal finite product shell annihilates a product field whose positive
power moment vanishes.  This is the zero-input branch needed by homogeneous
shell estimates: their Calderón--Zygmund decomposition is naturally written
for a strictly positive input moment, but the displayed convolution itself is
linear and therefore has a genuine zero case as well. -/
theorem q4FiniteProductKernelShell_eq_zero_of_integral_norm_rpow_eq_zero
    {I X : Type*} [Sub X] [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (mu : Measure X) (s : Finset I) (R : I -> I -> Prop) [DecidableRel R]
    (K : I -> I -> X -> Complex)
    (g : X × {i // i ∈ s} -> Complex) {p : Real} (hp : 0 < p)
    (hgp : Integrable (fun z => ‖g z‖ ^ p)
      (q4FiniteProductCountingMeasure mu s))
    (hzero : ∫ z, ‖g z‖ ^ p ∂q4FiniteProductCountingMeasure mu s = 0) :
    q4FiniteProductKernelShell mu s R K g = 0 := by
  have hpowzero : (fun z => ‖g z‖ ^ p) =ᵐ[q4FiniteProductCountingMeasure mu s] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun z => Real.rpow_nonneg (norm_nonneg (g z)) p) hgp).mp hzero
  have hgzero : g =ᵐ[q4FiniteProductCountingMeasure mu s] 0 := by
    filter_upwards [hpowzero] with z hz
    have hnorm : ‖g z‖ = 0 :=
      (Real.rpow_eq_zero (norm_nonneg (g z)) (ne_of_gt hp)).mp (by
        simpa only [Pi.zero_apply] using hz)
    exact norm_eq_zero.mp hnorm
  have hfibzero (i : I) (hi : i ∈ s) :
      q4FiniteProductToFibres s g i =ᵐ[mu] 0 := by
    change g =ᵐ[mu.prod Measure.count] 0 at hgzero
    have hcurried := ae_ae_eq_curry_of_prod hgzero
    filter_upwards [hcurried] with x hx
    simpa [q4FiniteProductToFibres, hi] using
      (ae_count_iff.mp hx ⟨i, hi⟩)
  funext z
  unfold q4FiniteProductKernelShell q4KernelTTStarShell
  apply Finset.sum_eq_zero
  intro l hl
  apply integral_eq_zero_of_ae
  filter_upwards [hfibzero l (Finset.mem_filter.mp hl).1] with y hy
  simp [hy]

/-- A finite extended-nonnegative strong constant has the canonical real
square-root factorization used by the literal `TT*` diagonal.  Keeping this
conversion here avoids baking an arbitrary square-root normalization into a
full-product estimate: the shell calculation naturally produces one
nonnegative `ENNReal` constant, while the `TT*` step uses its real square
root twice. -/
theorem ennreal_ofReal_sq_sqrt_toReal_eq
    (C : ENNReal) (hC : C ≠ ⊤) :
    ENNReal.ofReal ((Real.sqrt C.toReal) ^ (2 : Nat)) = C := by
  calc
    ENNReal.ofReal ((Real.sqrt C.toReal) ^ (2 : Nat)) =
        ENNReal.ofReal C.toReal := by
      rw [Real.sq_sqrt ENNReal.toReal_nonneg]
    _ = C := ENNReal.ofReal_toReal hC

/-- The same factorization in the orientation normally needed when a
full-product estimate is inserted into the finite-product diagonal. -/
theorem ennreal_eq_ofReal_sq_sqrt_toReal
    (C : ENNReal) (hC : C ≠ ⊤) :
    C = ENNReal.ofReal ((Real.sqrt C.toReal) ^ (2 : Nat)) :=
  (ennreal_ofReal_sq_sqrt_toReal_eq C hC).symm

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
