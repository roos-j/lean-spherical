/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

/-
# Mockenhaupt--Seeger--Sogge local smoothing

The implementation lives in `MSSBase`; the Kakeya proof of the light-ray
maximal estimate is consolidated in `MSSKakeya`.
-/

import LeanSpherical.Auto.Spherical.MSSBase
import LeanSpherical.Auto.Spherical.MSSKakeya
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.LinearAlgebra.Basis.Submodule

namespace Auto.Spherical.MSS

section Auto.Spherical.MSS

/-- The light-ray maximal estimate. -/
theorem hasLightRayMaximalEstimate : Auto.Spherical.MSSBase.HasLightRayMaximalEstimate :=
  Auto.Spherical.MSSKakeya.final_hasLightRayMaximalEstimate

/-!
## Truncated duality closure for the MSS square function

This is the measure-theoretic last step of the MSS argument.  Literal
time-slab support and compact spatial truncations stay in the test class, so
the proof never tests the light-ray estimate directly against an unknown
`L⁴` square function.
-/

open Filter MeasureTheory Set
open Auto.LittlewoodPaley
open Auto.Spherical.MSSBase
open Auto.Spherical.MSSKakeya
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.Auxiliary
open scoped ENNReal EuclideanSpace

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### The lattice Bessel ingredient for Fourier-cube projections -/

/- `AddCircleMulti` deliberately keeps these normalized Haar instances local
to its own file.  The fixed-lattice Fourier-series argument below uses the
same normalization, so make it explicit here as well. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Finite Bessel inequality for the two-dimensional unit additive torus.
This is the orthogonality step in the fixed-lattice Fourier-cube proof. -/
private theorem aux_unitAddTorus_fourier_bessel
    (F : Lp Complex 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (s : Finset (Fin 2 → Int)) :
    ∑ n ∈ s, ‖UnitAddTorus.mFourierCoeff F.1 n‖ ^ 2 ≤
      ∫ t : UnitAddTorus (Fin 2), ‖F.1 t‖ ^ 2 := by
  let p := UnitAddTorus.hasSum_sq_mFourierCoeff F
  calc
    ∑ n ∈ s, ‖UnitAddTorus.mFourierCoeff F.1 n‖ ^ 2 ≤
        ∑' n, ‖UnitAddTorus.mFourierCoeff F.1 n‖ ^ 2 :=
      p.summable.sum_le_tsum s (fun _ _ => sq_nonneg _)
    _ = ∫ t : UnitAddTorus (Fin 2), ‖F.1 t‖ ^ 2 := p.tsum_eq

/-- The Bessel inequality in a form for an ordinary measurable torus function.
This avoids choosing a representative of its `Lp` class at later uses. -/
private theorem aux_torus_finite_bessel_of_memLp
    (H : UnitAddTorus (Fin 2) → Complex)
    (hH : MemLp H 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (s : Finset (Fin 2 → Int)) :
    ∑ n ∈ s, ‖UnitAddTorus.mFourierCoeff (hH.toLp H).1 n‖ ^ 2 ≤
      ∫ t, ‖H t‖ ^ 2 := by
  calc
    _ ≤ ∫ t, ‖(hH.toLp H).1 t‖ ^ 2 :=
      aux_unitAddTorus_fourier_bessel (hH.toLp H) s
    _ = ∫ t, ‖H t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hH.coeFn_toLp] with t ht
      rw [ht]

/-- Bessel remains valid when the physical Fourier-cube projections agree
with the torus coefficients up to pointwise unitary phases. -/
private theorem aux_torus_bessel_of_unitary_coefficient_representation
    (H : UnitAddTorus (Fin 2) → Complex)
    (hH : MemLp H 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (s : Finset (Fin 2 → Int)) (P : (Fin 2 → Int) → Complex)
    (hP : ∀ n ∈ s, ∃ c : Complex, ‖c‖ = 1 ∧
      P n = c * UnitAddTorus.mFourierCoeff (hH.toLp H).1 n) :
    ∑ n ∈ s, ‖P n‖ ^ 2 ≤ ∫ t, ‖H t‖ ^ 2 := by
  calc
    ∑ n ∈ s, ‖P n‖ ^ 2 =
        ∑ n ∈ s, ‖UnitAddTorus.mFourierCoeff (hH.toLp H).1 n‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨c, hc, hrepr⟩ := hP n hn
      rw [hrepr, norm_mul, hc, one_mul]
    _ ≤ ∫ t, ‖H t‖ ^ 2 := aux_torus_finite_bessel_of_memLp H hH s

/-- A measurable pointwise square-energy majorization supplies both the
torus `L²` representative and its integral bound. -/
private theorem aux_memLp_two_of_sq_norm_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (H : α → Complex) (E : α → ℝ) (A : ℝ)
    (hH : AEStronglyMeasurable H μ) (hE : Integrable E μ)
    (hbound : ∀ᵐ t ∂μ, ‖H t‖ ^ 2 ≤ A * E t) :
    MemLp H 2 μ ∧ (∫ t, ‖H t‖ ^ 2 ∂μ) ≤ A * ∫ t, E t ∂μ := by
  have hAE : Integrable (fun t => A * E t) μ := hE.const_mul A
  have hsqmeas : AEStronglyMeasurable (fun t => ‖H t‖ ^ 2) μ := hH.norm.pow 2
  have hsq : Integrable (fun t => ‖H t‖ ^ 2) μ := by
    apply Integrable.mono' hAE hsqmeas
    filter_upwards [hbound] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact ht
    · positivity
  constructor
  · exact (memLp_two_iff_integrable_sq_norm hH).mpr hsq
  · calc
      (∫ t, ‖H t‖ ^ 2 ∂μ) ≤ ∫ t, A * E t ∂μ :=
        integral_mono_ae hsq hAE hbound
      _ = A * ∫ t, E t ∂μ := integral_const_mul A E

/-- The standard integer lattice point in planar Euclidean coordinates. -/
def standardLatticePoint (n : Fin 2 → Int) : Euclidean 2 :=
  WithLp.toLp 2 (fun i => (n i : Real))

/-- Private shorthand used by the Fourier-series calculation below. -/
private def aux_intVec2 (n : Fin 2 → Int) : Euclidean 2 :=
  standardLatticePoint n

/-- The integer lattice generated by the standard planar Euclidean basis. -/
private def aux_standardLattice : Submodule ℤ (Euclidean 2) :=
  Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin 2)))

/-- An integer coordinate vector, bundled as a point of the standard lattice. -/
private def aux_intVec2LatticePoint (n : Fin 2 → Int) : aux_standardLattice :=
  ⟨aux_intVec2 n, by
    change aux_intVec2 n ∈ Submodule.span ℤ
      (Set.range (PiLp.basisFun 2 ℝ (Fin 2)))
    rw [Module.Basis.mem_span_iff_repr_mem]
    intro i
    refine ⟨n i, ?_⟩
    simp [aux_intVec2, standardLatticePoint]⟩

private theorem aux_intVec2LatticePoint_coe (n : Fin 2 → Int) :
    (aux_intVec2LatticePoint n : Euclidean 2) = aux_intVec2 n := rfl

/-- The Euclidean pairing of a lattice point with real coordinate variables. -/
private lemma aux_inner_intVec2 (k : Fin 2 → Int) (u : Fin 2 → Real) :
    inner ℝ (aux_intVec2 k) (WithLp.toLp 2 u : Euclidean 2) =
      ∑ i, (k i : Real) * u i := by
  unfold aux_intVec2 standardLatticePoint
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]

/-- The ordinary torus Fourier character agrees exactly with Mathlib's
`Real.fourierChar` in the standard Euclidean coordinates. -/
private theorem aux_mFourier_coe_eq_fourierChar
    (k : Fin 2 → Int) (u : Fin 2 → Real) :
    UnitAddTorus.mFourier k (fun i => (u i : UnitAddCircle)) =
      (Real.fourierChar
        (inner ℝ (aux_intVec2 k) (WithLp.toLp 2 u : Euclidean 2)) : Complex) := by
  unfold UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk, fourier_coe_apply]
  rw [Real.fourierChar_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [aux_inner_intVec2]
  push_cast
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  ring

/-- Negating the integer frequency lattice point negates its Euclidean
realization. -/
private lemma aux_intVec2_neg (k : Fin 2 → Int) :
    aux_intVec2 (-k) = - aux_intVec2 k := by
  apply WithLp.ofLp_injective
  simp only [aux_intVec2, standardLatticePoint, WithLp.ofLp_toLp, Pi.neg_apply, Int.cast_neg,
    WithLp.ofLp_neg]
  rfl

/-- The negative mode occurring in `mFourierCoeff` is precisely the negative
physical Fourier character. -/
private theorem aux_mFourier_neg_coe_eq_fourierChar
    (k : Fin 2 → Int) (u : Fin 2 → Real) :
    UnitAddTorus.mFourier (-k) (fun i => (u i : UnitAddCircle)) =
      (Real.fourierChar
        (- inner ℝ (aux_intVec2 k) (WithLp.toLp 2 u : Euclidean 2)) : Complex) := by
  rw [aux_mFourier_coe_eq_fourierChar]
  rw [aux_intVec2_neg, inner_neg_left]

/-- The torus coefficient written as an integral over the standard unit
coordinate cell, with its exact physical Fourier character. -/
private def aux_unitCoordCell : Set (Fin 2 → Real) :=
  {u | ∀ i, u i ∈ Ioc (0 : Real) (0 + 1)}

/-- The shifted coordinate cell `(-1, 0]²`.  Unlike the usual `(0, 1]²`
cell, its image in Euclidean coordinates is literally the fundamental domain
of the negated standard lattice basis used in the tiling step below. -/
private def aux_negUnitCoordCell : Set (Fin 2 → Real) :=
  {u | ∀ i, u i ∈ Ioc (-1 : Real) ((-1 : Real) + 1)}

private theorem aux_negUnitCoordCell_measurable :
    MeasurableSet aux_negUnitCoordCell := by
  rw [aux_negUnitCoordCell, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  change MeasurableSet ((fun u : Fin 2 → Real => u i) ⁻¹'
    Ioc (-1 : Real) ((-1 : Real) + 1))
  exact measurableSet_Ioc.preimage (measurable_pi_apply i)

/-- The canonical representative of a point of the unit torus in
`(-1, 0]²`. -/
private def aux_torusMinusRep : UnitAddTorus (Fin 2) → Fin 2 → Real :=
  fun t => (UnitAddTorus.measurableEquivPiIoc
    (fun _ : Fin 2 => (-1 : Real)) t).1

private theorem aux_torusMinusRep_measurable :
    Measurable aux_torusMinusRep := by
  exact measurable_subtype_coe.comp
    (UnitAddTorus.measurableEquivPiIoc
      (fun _ : Fin 2 => (-1 : Real))).measurable

private theorem aux_torusMinusRep_mem_negUnitCoordCell
    (t : UnitAddTorus (Fin 2)) :
    aux_torusMinusRep t ∈ aux_negUnitCoordCell := by
  exact (UnitAddTorus.measurableEquivPiIoc
    (fun _ : Fin 2 => (-1 : Real)) t).property

private theorem aux_torusMinusRep_apply_on_cell (u : Fin 2 → Real)
    (hu : u ∈ aux_negUnitCoordCell) :
    aux_torusMinusRep (fun i => (u i : UnitAddCircle)) = u := by
  let e := UnitAddTorus.measurableEquivPiIoc
    (fun _ : Fin 2 => (-1 : Real))
  have he : e (fun i => (u i : UnitAddCircle)) = ⟨u, hu⟩ := by
    calc
      e (fun i => (u i : UnitAddCircle)) = e (e.symm ⟨u, hu⟩) := by simp [e]
      _ = ⟨u, hu⟩ := e.apply_symm_apply _
  change (e (fun i => (u i : UnitAddCircle))).1 = u
  exact congrArg Subtype.val he

/-- Reflection of a Schwartz kernel, retained as a Schwartz map so its
lattice envelope is available without any regularity loss. -/
private def aux_negatedSchwartz (K : SchwartzMap (Euclidean 2) Complex) :
    SchwartzMap (Euclidean 2) Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (ContinuousLinearEquiv.smulLeft (Units.mk0 (-1 : Real) (by norm_num))) K

private theorem aux_negatedSchwartz_apply
    (K : SchwartzMap (Euclidean 2) Complex) (v : Euclidean 2) :
    aux_negatedSchwartz K v = K (-v) := by
  change K ((ContinuousLinearEquiv.smulLeft
    (Units.mk0 (-1 : Real) (by norm_num))) v) = K (-v)
  simp

/-- The torus periodization whose Fourier coefficients are the common-scale
lattice cube projections.  The variable is rescaled before periodization, so
the construction is independent of the positive cube scale `R`. -/
private def aux_latticePeriodizedTorus (x : Euclidean 2) (R : Real)
    (K f : SchwartzMap (Euclidean 2) Complex) : UnitAddTorus (Fin 2) → Complex :=
  fun t => ∑' z : aux_standardLattice,
    K (-((z : Euclidean 2) - WithLp.toLp 2 (aux_torusMinusRep t))) *
      f (x + R⁻¹ • ((z : Euclidean 2) - WithLp.toLp 2 (aux_torusMinusRep t)))

private theorem aux_latticePeriodizedTorus_apply_on_cell
    (x : Euclidean 2) (R : Real) (K f : SchwartzMap (Euclidean 2) Complex)
    (u : Fin 2 → Real) (hu : u ∈ aux_negUnitCoordCell) :
    aux_latticePeriodizedTorus x R K f (fun i => (u i : UnitAddCircle)) =
      ∑' z : aux_standardLattice,
        K (-((z : Euclidean 2) - WithLp.toLp 2 u)) *
          f (x + R⁻¹ • ((z : Euclidean 2) - WithLp.toLp 2 u)) := by
  unfold aux_latticePeriodizedTorus
  rw [aux_torusMinusRep_apply_on_cell u hu]

private theorem aux_latticePeriodizedTorus_aestronglyMeasurable
    (x : Euclidean 2) (R : Real) (K f : SchwartzMap (Euclidean 2) Complex) :
    AEStronglyMeasurable (aux_latticePeriodizedTorus x R K f)
      (volume : Measure (UnitAddTorus (Fin 2))) := by
  letI : Countable aux_standardLattice := by
    change Countable (Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin 2))))
    infer_instance
  unfold aux_latticePeriodizedTorus
  apply AEStronglyMeasurable.tsum
  intro z
  have hcoord : Measurable (fun t : UnitAddTorus (Fin 2) =>
      (z : Euclidean 2) - WithLp.toLp 2 (aux_torusMinusRep t)) := by
    have hrep : Measurable (fun t : UnitAddTorus (Fin 2) =>
        (WithLp.toLp 2 (aux_torusMinusRep t) : Euclidean 2)) :=
      (WithLp.measurable_toLp 2 (Fin 2 → Real)).comp aux_torusMinusRep_measurable
    exact measurable_const.sub hrep
  exact ((K.continuous.measurable.comp hcoord.neg).mul
    (f.continuous.measurable.comp
      (measurable_const.add (hcoord.const_smul R⁻¹)))).aestronglyMeasurable

/-- The reflected coordinate equivalence maps the standard Euclidean
fundamental domain exactly to the `(-1,0]²` torus cell. -/
private def aux_negCoordEquiv : Euclidean 2 ≃ᵐ (Fin 2 → Real) :=
  (MeasurableEquiv.toLp 2 (Fin 2 → Real)).symm.trans
    (MeasurableEquiv.neg (Fin 2 → Real))

private theorem aux_negCoordEquiv_apply (v : Euclidean 2) :
    aux_negCoordEquiv v = -v.ofLp := rfl

private theorem aux_negCoord_of_mem_standardFD (v : Euclidean 2)
    (hv : v ∈ ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2))) :
    -v.ofLp ∈ aux_negUnitCoordCell := by
  rw [ZSpan.mem_fundamentalDomain] at hv
  intro i
  have hvi := hv i
  rw [PiLp.basisFun_repr] at hvi
  rw [Set.mem_Ico] at hvi
  simp only [Pi.neg_apply, Set.mem_Ioc]
  constructor <;> linarith

private theorem aux_negCoord_to_standardFD (u : Fin 2 → Real)
    (hu : u ∈ aux_negUnitCoordCell) :
    WithLp.toLp 2 (-u) ∈
      ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)) := by
  rw [ZSpan.mem_fundamentalDomain]
  intro i
  rw [PiLp.basisFun_repr]
  rw [WithLp.ofLp_toLp]
  simp only [Pi.neg_apply]
  have hui := hu i
  simp only [Set.mem_Ioc] at hui
  constructor <;> linarith

private theorem aux_negCoordEquiv_measurePreserving :
    MeasurePreserving aux_negCoordEquiv
      (volume : Measure (Euclidean 2)) (volume : Measure (Fin 2 → Real)) := by
  change MeasurePreserving (Neg.neg ∘ WithLp.ofLp) volume volume
  exact (Measure.measurePreserving_neg volume).comp
    (PiLp.volume_preserving_ofLp (Fin 2))

private theorem aux_negCoordEquiv_image_standardFD :
    aux_negCoordEquiv ''
      ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)) =
      aux_negUnitCoordCell := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [aux_negCoordEquiv_apply]
    exact aux_negCoord_of_mem_standardFD v hv
  · intro hu
    refine ⟨WithLp.toLp 2 (-u), aux_negCoord_to_standardFD u hu, ?_⟩
    rw [aux_negCoordEquiv_apply]
    rw [WithLp.ofLp_toLp]
    simp

private theorem aux_integral_negCell_eq_integral_standardFD
    (g : (Fin 2 → Real) → Real) :
    ∫ u in aux_negUnitCoordCell, g u =
      ∫ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        g (aux_negCoordEquiv v) := by
  rw [← aux_negCoordEquiv_image_standardFD]
  exact aux_negCoordEquiv_measurePreserving.setIntegral_image_emb
    aux_negCoordEquiv.measurableEmbedding g _

/-- The same reflected-cell transport for the complex coefficient integrands.
Keeping this separate from the nonnegative energy transport avoids coercing
the torus Fourier character through a real-valued auxiliary function. -/
private theorem aux_integral_negCell_eq_integral_standardFD_complex
    (g : (Fin 2 → Real) → Complex) :
    ∫ u in aux_negUnitCoordCell, g u =
      ∫ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        g (aux_negCoordEquiv v) := by
  rw [← aux_negCoordEquiv_image_standardFD]
  exact aux_negCoordEquiv_measurePreserving.setIntegral_image_emb
    aux_negCoordEquiv.measurableEmbedding g _

/-- The reflected-cell transport in the nonnegative extended-integral form
used by the periodized-energy estimate. -/
private theorem aux_lintegral_negCell_eq_lintegral_standardFD
    (g : (Fin 2 → Real) → ENNReal) :
    ∫⁻ u in aux_negUnitCoordCell, g u =
      ∫⁻ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        g (aux_negCoordEquiv v) := by
  rw [← aux_negCoordEquiv_image_standardFD]
  exact (aux_negCoordEquiv_measurePreserving.setLIntegral_comp_emb
    aux_negCoordEquiv.measurableEmbedding g _).symm

private theorem aux_latticePeriodizedTorus_apply_on_standardFD
    (x : Euclidean 2) (R : Real) (K f : SchwartzMap (Euclidean 2) Complex)
    (v : Euclidean 2)
    (hv : v ∈ ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2))) :
    aux_latticePeriodizedTorus x R K f
      (fun i => (((-v.ofLp) i : Real) : UnitAddCircle)) =
      ∑' z : aux_standardLattice,
        K (-((z : Euclidean 2) + v)) *
          f (x + R⁻¹ • ((z : Euclidean 2) + v)) := by
  rw [aux_latticePeriodizedTorus_apply_on_cell x R K f (-v.ofLp)
    (aux_negCoord_of_mem_standardFD v hv)]
  rw [WithLp.toLp_neg, WithLp.toLp_ofLp]
  simp only [sub_neg_eq_add]

private theorem aux_latticePeriodizedTorus_energy_eq_standardFD
    (x : Euclidean 2) (R : Real) (K f : SchwartzMap (Euclidean 2) Complex) :
    ∫ t : UnitAddTorus (Fin 2),
        ‖aux_latticePeriodizedTorus x R K f t‖ ^ 2 =
      ∫ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        ‖∑' z : aux_standardLattice,
          K (-((z : Euclidean 2) + v)) *
            f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2 := by
  rw [UnitAddTorus.integral_preimage
    (fun t => ‖aux_latticePeriodizedTorus x R K f t‖ ^ 2)
    (fun _ : Fin 2 => (-1 : Real))]
  change ∫ u in aux_negUnitCoordCell,
      ‖aux_latticePeriodizedTorus x R K f
        (fun i => (u i : UnitAddCircle))‖ ^ 2 = _
  rw [aux_integral_negCell_eq_integral_standardFD]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
    (ZSpan.fundamentalDomain_measurableSet _)] with v hv
  rw [aux_negCoordEquiv_apply]
  rw [aux_latticePeriodizedTorus_apply_on_standardFD x R K f v hv]

/-- The torus coefficient computed over the `(-1, 0]²` representative cell.
This is the version compatible with the exact lattice fundamental domain. -/
private theorem aux_mFourierCoeff_eq_negUnitCell_integral
    (H : UnitAddTorus (Fin 2) → Complex) (k : Fin 2 → Int) :
    UnitAddTorus.mFourierCoeff H k =
      ∫ u : Fin 2 → Real in aux_negUnitCoordCell,
        (Real.fourierChar
          (- inner ℝ (aux_intVec2 k) (WithLp.toLp 2 u : Euclidean 2)) : Complex) *
          H (fun i => (u i : UnitAddCircle)) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral H k
    (fun _ : Fin 2 => (-1 : Real))]
  change (∫ u : Fin 2 → Real in aux_negUnitCoordCell,
      UnitAddTorus.mFourier (-k) (fun i => (u i : UnitAddCircle)) •
        H (fun i => (u i : UnitAddCircle))) = _
  apply integral_congr_ae
  filter_upwards with u
  rw [aux_mFourier_neg_coe_eq_fourierChar]
  exact smul_eq_mul _ _

private theorem aux_mFourierCoeff_eq_unitCell_integral
    (H : UnitAddTorus (Fin 2) → Complex) (k : Fin 2 → Int) :
    UnitAddTorus.mFourierCoeff H k =
      ∫ u : Fin 2 → Real in aux_unitCoordCell,
        (Real.fourierChar
          (- inner ℝ (aux_intVec2 k) (WithLp.toLp 2 u : Euclidean 2)) : Complex) *
          H (fun i => (u i : UnitAddCircle)) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral H k (fun _ : Fin 2 => (0 : Real))]
  change (∫ u : Fin 2 → Real in aux_unitCoordCell,
      UnitAddTorus.mFourier (-k) (fun i => (u i : UnitAddCircle)) •
        H (fun i => (u i : UnitAddCircle))) = _
  apply integral_congr_ae
  filter_upwards with u
  rw [aux_mFourier_neg_coe_eq_fourierChar]
  exact smul_eq_mul _ _

/-- Integer frequencies have trivial `2π`-normalized Fourier character. -/
private lemma aux_fourierChar_int (n : Int) :
    (Real.fourierChar (n : Real) : Complex) = 1 := by
  rw [Real.fourierChar_apply]
  rw [show (↑(2 * Real.pi * (n : Real)) * Complex.I) =
      (n : Complex) * (2 * (Real.pi : Complex) * Complex.I) by
    push_cast
    ring]
  rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I]
  simp

/-- A standard integer-lattice pairing has trivial Fourier character. -/
private theorem aux_fourierChar_one_of_intLattice
    (k : Fin 2 → Int) (z : aux_standardLattice) :
    (Real.fourierChar (inner ℝ (aux_intVec2 k) (z : Euclidean 2)) : Complex) = 1 := by
  have hz := ((PiLp.basisFun 2 Real (Fin 2)).mem_span_iff_repr_mem Int
    (z : Euclidean 2)).mp z.property
  choose n hn using hz
  have hcoord (i : Fin 2) : WithLp.ofLp (z : Euclidean 2) i = (n i : Real) := by
    have hi := hn i
    change (n i : Real) = ((PiLp.basisFun 2 Real (Fin 2)).repr
      (z : Euclidean 2)) i at hi
    simpa only [PiLp.basisFun_repr] using hi.symm
  have hzeq : (z : Euclidean 2) = aux_intVec2 n := by
    apply WithLp.ofLp_injective
    funext i
    simpa only [aux_intVec2, standardLatticePoint, WithLp.ofLp_toLp] using hcoord i
  rw [hzeq]
  rw [show aux_intVec2 n = WithLp.toLp 2 (fun i => (n i : Real)) by
    rfl]
  rw [aux_inner_intVec2]
  rw [show (∑ i, (k i : Real) * (n i : Real)) =
      ((∑ i, k i * n i : Int) : Real) by
    push_cast
    rfl]
  exact aux_fourierChar_int (∑ i, k i * n i)

private lemma aux_fourierChar_add (a c : Real) :
    (Real.fourierChar (a + c) : Complex) =
      Real.fourierChar a * Real.fourierChar c := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The coefficient character is periodic across the standard integer
lattice, exactly as required for the periodized kernel coefficient. -/
private theorem aux_fourierChar_neg_periodic
    (k : Fin 2 → Int) (z : aux_standardLattice) (v : Euclidean 2) :
    (Real.fourierChar (-inner ℝ (aux_intVec2 k) ((z : Euclidean 2) + v)) : Complex) =
      Real.fourierChar (-inner ℝ (aux_intVec2 k) v) := by
  have hinner : inner ℝ (aux_intVec2 (-k)) (z : Euclidean 2) =
      -inner ℝ (aux_intVec2 k) (z : Euclidean 2) := by
    rw [aux_intVec2_neg, inner_neg_left]
  have hz : (Real.fourierChar
      (-inner ℝ (aux_intVec2 k) (z : Euclidean 2)) : Complex) = 1 := by
    have hz0 := aux_fourierChar_one_of_intLattice (-k) z
    rw [hinner] at hz0
    exact hz0
  rw [show -inner ℝ (aux_intVec2 k) ((z : Euclidean 2) + v) =
      (-inner ℝ (aux_intVec2 k) (z : Euclidean 2)) +
        (-inner ℝ (aux_intVec2 k) v) by
    rw [inner_add_right]
    ring]
  rw [aux_fourierChar_add, hz, one_mul]

/-- Bochner tiling of the standard lattice fundamental domain. -/
private theorem aux_integral_periodize_standardFD
    (g : Euclidean 2 → Complex) (hg : Integrable g volume) :
    ∫ u : Euclidean 2 in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        ∑' z : aux_standardLattice, g (z +ᵥ u) =
      ∫ v : Euclidean 2, g v := by
  letI : Countable aux_standardLattice := by
    change Countable (Submodule.span Int (Set.range (PiLp.basisFun 2 Real (Fin 2))))
    infer_instance
  have hU : IsAddFundamentalDomain aux_standardLattice.toAddSubgroup
      (ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2))) volume :=
    ZSpan.isAddFundamentalDomain' (PiLp.basisFun 2 ℝ (Fin 2)) volume
  have hmeas : ∀ z : aux_standardLattice,
      AEStronglyMeasurable (fun u : Euclidean 2 => g (z +ᵥ u))
        (volume.restrict (ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)))) := by
    intro z
    change AEStronglyMeasurable (fun u : Euclidean 2 => g ((z : Euclidean 2) + u))
      (volume.restrict (ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2))))
    exact (hg.comp_add_left (z : Euclidean 2)).aestronglyMeasurable.restrict
  have hFDnorm := hU.lintegral_eq_tsum'' (fun v : Euclidean 2 => ‖g v‖ₑ)
  have hfinite :
      ∑' z : aux_standardLattice,
        ∫⁻ u : Euclidean 2 in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
          ‖g (z +ᵥ u)‖ₑ ≠ ∞ := by
    intro htop
    apply (ne_of_lt hg.hasFiniteIntegral)
    exact hFDnorm.trans htop
  calc
    (∫ u : Euclidean 2 in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        ∑' z : aux_standardLattice, g (z +ᵥ u)) =
      ∑' z : aux_standardLattice,
        ∫ u : Euclidean 2 in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
          g (z +ᵥ u) :=
      MeasureTheory.integral_tsum hmeas hfinite
    _ = ∫ v : Euclidean 2, g v :=
      (hU.integral_eq_tsum'' g hg).symm

/-- Passing to the canonical `Lp` representative does not change a torus
Fourier coefficient. -/
private theorem aux_mFourierCoeff_toLp_eq
    (H : UnitAddTorus (Fin 2) → Complex)
    (hH : MemLp H 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (k : Fin 2 → Int) :
    UnitAddTorus.mFourierCoeff (hH.toLp H).1 k =
      UnitAddTorus.mFourierCoeff H k := by
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [hH.coeFn_toLp] with t ht
  rw [ht]

/-- The physical integrand whose lattice periodization is the negative
torus Fourier coefficient of a translated equal-scale cube projection. -/
private def aux_latticeCoefficientSeed (x : Euclidean 2) (R : Real)
    (K f : SchwartzMap (Euclidean 2) Complex) (k : Fin 2 → Int) (v : Euclidean 2) : Complex :=
  (Real.fourierChar (- inner ℝ (aux_intVec2 k) v) : Complex) *
    K (-v) * f (x + R⁻¹ • v)

/-- Exact coefficient identity for the periodized equal-lattice kernel.
Integrability is supplied separately from the Schwartz decay of the kernel. -/
private theorem aux_latticePeriodizedTorus_mFourierCoeff_neg_eq_seed_integral
    (x : Euclidean 2) (R : Real) (K f : SchwartzMap (Euclidean 2) Complex)
    (k : Fin 2 → Int)
    (hg : Integrable (aux_latticeCoefficientSeed x R K f k) volume) :
    UnitAddTorus.mFourierCoeff (aux_latticePeriodizedTorus x R K f) (-k) =
      ∫ v : Euclidean 2, aux_latticeCoefficientSeed x R K f k v := by
  rw [aux_mFourierCoeff_eq_negUnitCell_integral (aux_latticePeriodizedTorus x R K f) (-k)]
  have hphase (u : Fin 2 → Real) :
      -inner ℝ (aux_intVec2 (-k)) (WithLp.toLp 2 u : Euclidean 2) =
        inner ℝ (aux_intVec2 k) (WithLp.toLp 2 u : Euclidean 2) := by
    rw [aux_intVec2_neg, inner_neg_left]
    ring
  calc
    (∫ u : Fin 2 → Real in aux_negUnitCoordCell,
      (Real.fourierChar (-inner ℝ (aux_intVec2 (-k)) (WithLp.toLp 2 u : Euclidean 2)) : Complex) *
        aux_latticePeriodizedTorus x R K f (fun i => (u i : UnitAddCircle))) =
      ∫ u : Fin 2 → Real in aux_negUnitCoordCell,
        (Real.fourierChar (inner ℝ (aux_intVec2 k) (WithLp.toLp 2 u : Euclidean 2)) : Complex) *
          aux_latticePeriodizedTorus x R K f (fun i => (u i : UnitAddCircle)) := by
        apply integral_congr_ae
        filter_upwards with u
        rw [hphase]
    _ = ∫ v : Euclidean 2 in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
      (Real.fourierChar (inner ℝ (aux_intVec2 k) (WithLp.toLp 2 (aux_negCoordEquiv v) : Euclidean 2)) : Complex) *
        aux_latticePeriodizedTorus x R K f (fun i => ((aux_negCoordEquiv v i : Real) : UnitAddCircle)) :=
      aux_integral_negCell_eq_integral_standardFD_complex _
    _ = ∫ v : Euclidean 2 in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        ∑' z : aux_standardLattice, aux_latticeCoefficientSeed x R K f k (z +ᵥ v) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (ZSpan.fundamentalDomain_measurableSet _)] with v hv
      rw [aux_negCoordEquiv_apply]
      rw [aux_latticePeriodizedTorus_apply_on_standardFD x R K f v hv]
      rw [WithLp.toLp_neg, WithLp.toLp_ofLp, inner_neg_right]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      unfold aux_latticeCoefficientSeed
      change (Real.fourierChar (-inner ℝ (aux_intVec2 k) v) : Complex) *
          (K (-((z : Euclidean 2) + v)) * f (x + R⁻¹ • ((z : Euclidean 2) + v))) =
        (Real.fourierChar (-inner ℝ (aux_intVec2 k) ((z : Euclidean 2) + v)) : Complex) *
          K (-((z : Euclidean 2) + v)) *
          f (x + R⁻¹ • ((z : Euclidean 2) + v))
      rw [aux_fourierChar_neg_periodic k z v]
      ring
    _ = ∫ v : Euclidean 2, aux_latticeCoefficientSeed x R K f k v :=
      aux_integral_periodize_standardFD _ hg

/-- The coefficient seed is integrable: the Schwartz kernel is integrable and
the Schwartz input is bounded. -/
private theorem aux_latticeCoefficientSeed_integrable
    (x : Euclidean 2) (R : Real) (K f : SchwartzMap (Euclidean 2) Complex)
    (k : Fin 2 → Int) :
    Integrable (aux_latticeCoefficientSeed x R K f k) volume := by
  have hK' : Integrable (aux_negatedSchwartz K : Euclidean 2 → Complex) volume :=
    (aux_negatedSchwartz K).integrable
  have hK : Integrable (fun v : Euclidean 2 => K (-v)) volume :=
    hK'.congr (Filter.Eventually.of_forall fun v => aux_negatedSchwartz_apply K v)
  have harg : Continuous (fun v : Euclidean 2 => x + R⁻¹ • v) :=
    continuous_const.add (continuous_id.const_smul R⁻¹)
  have hbase : Integrable (fun v : Euclidean 2 =>
      K (-v) * f (x + R⁻¹ • v)) volume :=
    hK.mul_bdd
      ((f.continuous.comp harg).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun v =>
        SchwartzMap.norm_le_seminorm Complex f _)
  have hphase : AEStronglyMeasurable (fun v : Euclidean 2 =>
      Real.fourierChar (-inner ℝ (aux_intVec2 k) v)) volume := by
    exact (Real.continuous_fourierChar.comp
      ((continuous_const.inner continuous_id).neg)).aestronglyMeasurable
  have hint : Integrable (fun v : Euclidean 2 =>
      Real.fourierChar (-inner ℝ (aux_intVec2 k) v) •
        (K (-v) * f (x + R⁻¹ • v))) volume :=
    hbase.congr' (hphase.smul hbase.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _ => by simp)
  have hfun : (fun v : Euclidean 2 =>
      Real.fourierChar (-inner ℝ (aux_intVec2 k) v) •
        (K (-v) * f (x + R⁻¹ • v))) = aux_latticeCoefficientSeed x R K f k := by
    funext v
    simp only [aux_latticeCoefficientSeed, Circle.smul_def, smul_eq_mul, mul_assoc]
  rw [← hfun]
  exact hint

/-- Weighted Cauchy for a summable complex lattice periodization.  This is
the pointwise step which turns the periodized kernel into a positive
periodized energy. -/
private theorem aux_tsum_norm_sq_le_weighted
    {ι : Type*} [Countable ι]
    (a : ι → Complex) (w e : ι → Real)
    (ha : Summable (fun i => ‖a i‖))
    (hw : Summable w) (he : Summable e)
    (hw0 : ∀ i, 0 ≤ w i) (he0 : ∀ i, 0 ≤ e i)
    (hnorm : ∀ i, ‖a i‖ = Real.sqrt (w i) * Real.sqrt (e i)) :
    ‖∑' i, a i‖ ^ 2 ≤ (∑' i, w i) * (∑' i, e i) := by
  have hsqrtw_apply : (fun i => (Real.sqrt (w i)) ^ (2 : Real)) = w := by
    funext i
    rw [Real.rpow_two, Real.sq_sqrt (hw0 i)]
  have hsqrte_apply : (fun i => (Real.sqrt (e i)) ^ (2 : Real)) = e := by
    funext i
    rw [Real.rpow_two, Real.sq_sqrt (he0 i)]
  have hsqrtw : Summable (fun i => (Real.sqrt (w i)) ^ (2 : Real)) := by
    rw [hsqrtw_apply]
    exact hw
  have hsqrte : Summable (fun i => (Real.sqrt (e i)) ^ (2 : Real)) := by
    rw [hsqrte_apply]
    exact he
  obtain ⟨_, hholder⟩ :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
      (fun i => Real.sqrt_nonneg _) (fun i => Real.sqrt_nonneg _) hsqrtw hsqrte
  have htsum : ∑' i, ‖a i‖ = ∑' i, Real.sqrt (w i) * Real.sqrt (e i) := by
    apply tsum_congr
    intro i
    exact hnorm i
  have hnormle : ‖∑' i, a i‖ ≤
      (∑' i, Real.sqrt (w i) * Real.sqrt (e i)) :=
    (norm_tsum_le_tsum_norm ha).trans_eq htsum
  have hleft0 : 0 ≤ ‖∑' i, a i‖ := norm_nonneg _
  have hright0 : 0 ≤ ∑' i, Real.sqrt (w i) * Real.sqrt (e i) :=
    tsum_nonneg fun i => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    ‖∑' i, a i‖ ^ 2 ≤ (∑' i, Real.sqrt (w i) * Real.sqrt (e i)) ^ 2 :=
      (sq_le_sq₀ hleft0 hright0).mpr hnormle
    _ ≤ ((∑' i, (Real.sqrt (w i)) ^ (2 : Real)) ^ (1 / (2 : Real)) *
        (∑' i, (Real.sqrt (e i)) ^ (2 : Real)) ^ (1 / (2 : Real))) ^ 2 := by
      gcongr
    _ = (∑' i, w i) * (∑' i, e i) := by
      rw [hsqrtw_apply, hsqrte_apply]
      have hwt : 0 ≤ ∑' i, w i := tsum_nonneg hw0
      have het : 0 ≤ ∑' i, e i := tsum_nonneg he0
      have hwtroot : ((∑' i, w i) ^ (1 / (2 : Real))) ^ 2 = ∑' i, w i := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hwt]
      have hetroot : ((∑' i, e i) ^ (1 / (2 : Real))) ^ 2 = ∑' i, e i := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt het]
      rw [mul_pow, hwtroot, hetroot]

/-- The pointwise weighted Cauchy inequality in the nonnegative extended
integral form needed for the physical lattice energy. -/
private theorem aux_weighted_factor_two (a b : ENNReal) :
    a * b = a ^ (2 : Real)⁻¹ *
      (a * b ^ (2 : Real)) ^ (2 : Real)⁻¹ := by
  have hbinv : (b ^ (2 : Real)) ^ (2 : Real)⁻¹ = b := by
    calc
      (b ^ (2 : Real)) ^ (2 : Real)⁻¹ = b ^ ((2 : Real) * (2 : Real)⁻¹) :=
        (ENNReal.rpow_mul _ _ _).symm
      _ = b := by
        rw [mul_inv_cancel₀ (by norm_num : (2 : Real) ≠ 0), ENNReal.rpow_one]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (2 : Real)⁻¹)]
  rw [hbinv]
  calc
    a * b = a ^ ((2 : Real)⁻¹ + (2 : Real)⁻¹) * b := by
      rw [show (2 : Real)⁻¹ + (2 : Real)⁻¹ = 1 by norm_num, ENNReal.rpow_one]
    _ = (a ^ (2 : Real)⁻¹ * a ^ (2 : Real)⁻¹) * b := by
      rw [ENNReal.rpow_add_of_nonneg _ _
        (by positivity : 0 ≤ (2 : Real)⁻¹)
        (by positivity : 0 ≤ (2 : Real)⁻¹)]
    _ = a ^ (2 : Real)⁻¹ * (a ^ (2 : Real)⁻¹ * b) := by ring

/-- Weighted Cauchy--Schwarz for a nonnegative Euclidean integral. -/
private theorem aux_lintegral_weighted_cauchy_two
    (A B : Euclidean 2 → ENNReal)
    (hA : AEMeasurable A volume) (hB : AEMeasurable B volume) :
    (∫⁻ y : Euclidean 2, A y * B y) ^ (2 : Real) ≤
      (∫⁻ y : Euclidean 2, A y) *
        ∫⁻ y : Euclidean 2, A y * B y ^ (2 : Real) := by
  let a : Euclidean 2 → ENNReal := fun y => A y ^ (2 : Real)⁻¹
  let b : Euclidean 2 → ENNReal := fun y =>
    (A y * B y ^ (2 : Real)) ^ (2 : Real)⁻¹
  have ha : AEMeasurable a volume := by exact hA.pow_const _
  have hb : AEMeasurable b volume := by
    exact (hA.mul (hB.pow_const _)).pow_const _
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    Real.HolderConjugate.two_two ha hb
  have hleft : (∫⁻ y : Euclidean 2, (a * b) y) =
      ∫⁻ y : Euclidean 2, A y * B y := by
    apply lintegral_congr
    intro y
    simp only [a, b, Pi.mul_apply]
    exact (aux_weighted_factor_two (A y) (B y)).symm
  have hfirst : (∫⁻ y : Euclidean 2, a y ^ (2 : Real)) =
      ∫⁻ y : Euclidean 2, A y := by
    apply lintegral_congr
    intro y
    simp only [a]
    rw [← ENNReal.rpow_mul,
      inv_mul_cancel₀ (by norm_num : (2 : Real) ≠ 0), ENNReal.rpow_one]
  have hsecond : (∫⁻ y : Euclidean 2, b y ^ (2 : Real)) =
      ∫⁻ y : Euclidean 2, A y * B y ^ (2 : Real) := by
    apply lintegral_congr
    intro y
    simp only [b]
    rw [← ENNReal.rpow_mul,
      inv_mul_cancel₀ (by norm_num : (2 : Real) ≠ 0), ENNReal.rpow_one]
  have hholder' :
      (∫⁻ y : Euclidean 2, A y * B y) ≤
        (∫⁻ y : Euclidean 2, A y) ^ (2 : Real)⁻¹ *
          (∫⁻ y : Euclidean 2, A y * B y ^ (2 : Real)) ^ (2 : Real)⁻¹ := by
    rw [hleft, hfirst, hsecond] at hholder
    simpa only [one_div] using hholder
  have hpow := ENNReal.rpow_le_rpow hholder'
    (by positivity : 0 ≤ (2 : Real))
  calc
    (∫⁻ y : Euclidean 2, A y * B y) ^ (2 : Real) ≤
        ((∫⁻ y : Euclidean 2, A y) ^ (2 : Real)⁻¹ *
          (∫⁻ y : Euclidean 2, A y * B y ^ (2 : Real)) ^ (2 : Real)⁻¹) ^
            (2 : Real) := hpow
    _ = (∫⁻ y : Euclidean 2, A y) *
        ∫⁻ y : Euclidean 2, A y * B y ^ (2 : Real) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (2 : Real))]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        inv_mul_cancel₀ (by norm_num : (2 : Real) ≠ 0), ENNReal.rpow_one]
      simp only [ENNReal.rpow_one]

/-- The scale in the periodized kernel is only a translation of the physical
variable.  Thus the positive energy satisfies the exact scale-uniform
`L²` Young bound below. -/
private theorem aux_scaled_weighted_young_two
    (K q : Euclidean 2 → ENNReal)
    (hK : Measurable K) (hq : Measurable q) (R : Real) :
    ∫⁻ x : Euclidean 2,
        (∫⁻ v : Euclidean 2,
          K (-v) * q (x + R⁻¹ • v)) ^ (2 : Real) ≤
      (∫⁻ v : Euclidean 2, K v) ^ (2 : Real) *
        ∫⁻ x : Euclidean 2, q x ^ (2 : Real) := by
  have hW : Measurable (fun v : Euclidean 2 => K (-v)) :=
    hK.comp measurable_id.neg
  have hH : Measurable (fun z : Euclidean 2 × Euclidean 2 =>
      K (-z.2) * q (z.1 + R⁻¹ • z.2) ^ (2 : Real)) := by
    exact (hK.comp measurable_snd.neg).mul
      ((hq.comp (measurable_fst.add (measurable_snd.const_smul R⁻¹))).pow measurable_const)
  have hinner : Measurable (fun x : Euclidean 2 =>
      ∫⁻ v : Euclidean 2, K (-v) * q (x + R⁻¹ • v) ^ (2 : Real)) :=
    hH.lintegral_prod_right
  have hpoint (x : Euclidean 2) :
      (∫⁻ v : Euclidean 2, K (-v) * q (x + R⁻¹ • v)) ^ (2 : Real) ≤
        (∫⁻ v : Euclidean 2, K (-v)) *
          ∫⁻ v : Euclidean 2, K (-v) * q (x + R⁻¹ • v) ^ (2 : Real) := by
    apply aux_lintegral_weighted_cauchy_two
    · exact hW.aemeasurable
    · exact (hq.comp
        (measurable_const.add (measurable_id.const_smul R⁻¹))).aemeasurable
  have htranslate (v : Euclidean 2) :
      (∫⁻ x : Euclidean 2, q (x + R⁻¹ • v) ^ (2 : Real)) =
        ∫⁻ x : Euclidean 2, q x ^ (2 : Real) := by
    exact (measurePreserving_add_right (volume : Measure (Euclidean 2))
      (R⁻¹ • v)).lintegral_comp (hq.pow measurable_const)
  have hdouble :
      (∫⁻ x : Euclidean 2, ∫⁻ v : Euclidean 2,
        K (-v) * q (x + R⁻¹ • v) ^ (2 : Real)) =
        (∫⁻ v : Euclidean 2, K (-v)) *
          ∫⁻ x : Euclidean 2, q x ^ (2 : Real) := by
    calc
      (∫⁻ x : Euclidean 2, ∫⁻ v : Euclidean 2,
          K (-v) * q (x + R⁻¹ • v) ^ (2 : Real)) =
          ∫⁻ v : Euclidean 2, ∫⁻ x : Euclidean 2,
            K (-v) * q (x + R⁻¹ • v) ^ (2 : Real) := by
        exact lintegral_lintegral_swap hH.aemeasurable
      _ = ∫⁻ v : Euclidean 2, K (-v) *
          (∫⁻ x : Euclidean 2, q (x + R⁻¹ • v) ^ (2 : Real)) := by
        apply lintegral_congr
        intro v
        exact lintegral_const_mul (K (-v))
          ((hq.comp (measurable_id.add measurable_const)).pow measurable_const)
      _ = ∫⁻ v : Euclidean 2, K (-v) *
          (∫⁻ x : Euclidean 2, q x ^ (2 : Real)) := by
        apply lintegral_congr
        intro v
        rw [htranslate v]
      _ = (∫⁻ v : Euclidean 2, K (-v)) *
          ∫⁻ x : Euclidean 2, q x ^ (2 : Real) :=
        lintegral_mul_const _ hW
  have hneg : (∫⁻ v : Euclidean 2, K (-v)) =
      ∫⁻ v : Euclidean 2, K v := by
    exact (Measure.measurePreserving_neg (volume : Measure (Euclidean 2))).lintegral_comp hK
  calc
    (∫⁻ x : Euclidean 2,
        (∫⁻ v : Euclidean 2, K (-v) * q (x + R⁻¹ • v)) ^ (2 : Real)) ≤
        ∫⁻ x : Euclidean 2,
          (∫⁻ v : Euclidean 2, K (-v)) *
            (∫⁻ v : Euclidean 2,
              K (-v) * q (x + R⁻¹ • v) ^ (2 : Real)) := by
          apply lintegral_mono
          intro x
          exact hpoint x
    _ = (∫⁻ v : Euclidean 2, K (-v)) *
        (∫⁻ x : Euclidean 2, ∫⁻ v : Euclidean 2,
          K (-v) * q (x + R⁻¹ • v) ^ (2 : Real)) := by
      rw [lintegral_const_mul _ hinner]
    _ = (∫⁻ v : Euclidean 2, K (-v)) *
        ((∫⁻ v : Euclidean 2, K (-v)) *
          ∫⁻ x : Euclidean 2, q x ^ (2 : Real)) := by
      rw [hdouble]
    _ = (∫⁻ v : Euclidean 2, K (-v)) ^ (2 : Real) *
        ∫⁻ x : Euclidean 2, q x ^ (2 : Real) := by
      rw [ENNReal.rpow_two]
      ring
    _ = (∫⁻ v : Euclidean 2, K v) ^ (2 : Real) *
        ∫⁻ x : Euclidean 2, q x ^ (2 : Real) := by
      rw [hneg]

/-- Tonelli followed by the exact fundamental-domain tiling identity.  In
the cube proof `E` is the positive weighted periodized kernel energy. -/
private theorem aux_cell_lintegral_periodize
    {X : Type*} [AddCommGroup X] [MeasurableSpace X]
    (μ : Measure X) (Λ : AddSubgroup X) [Countable Λ]
    [MeasurableConstVAdd Λ X] [VAddInvariantMeasure Λ X μ]
    (U : Set X) (hU : IsAddFundamentalDomain Λ U μ)
    (E : X → ENNReal)
    (hE : ∀ z : Λ, AEMeasurable (fun u : X => E (z +ᵥ u)) (μ.restrict U)) :
    ∫⁻ u in U, (∑' z : Λ, E (z +ᵥ u)) ∂μ = ∫⁻ y, E y ∂μ := by
  rw [lintegral_tsum hE]
  exact (hU.lintegral_eq_tsum'' E).symm

/-- The additive-subgroup index used by the tiling theorem is canonically
equivalent to the submodule index used by the periodized kernel. -/
private theorem aux_reindex_standard_lattice_tsum
    (E : Euclidean 2 → ENNReal) (v : Euclidean 2) :
    ∑' z : aux_standardLattice, E ((z : Euclidean 2) + v) =
      ∑' z : aux_standardLattice.toAddSubgroup, E (z +ᵥ v) := by
  letI : Countable aux_standardLattice := by
    change Countable (Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin 2))))
    infer_instance
  letI : Countable aux_standardLattice.toAddSubgroup := by
    change Countable aux_standardLattice
    infer_instance
  let e : aux_standardLattice.toAddSubgroup ≃ aux_standardLattice :=
    { toFun := fun z => ⟨z, z.property⟩
      invFun := fun z => ⟨z, z.property⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  have hecoe (z : aux_standardLattice.toAddSubgroup) :
      ((e z : aux_standardLattice) : Euclidean 2) = (z : Euclidean 2) := by rfl
  calc
    (∑' z : aux_standardLattice, E ((z : Euclidean 2) + v)) =
        ∑' z : aux_standardLattice.toAddSubgroup,
          E (((e z : aux_standardLattice) : Euclidean 2) + v) :=
      (e.tsum_eq (fun z : aux_standardLattice => E ((z : Euclidean 2) + v))).symm
    _ = ∑' z : aux_standardLattice.toAddSubgroup, E (z +ᵥ v) := by
      apply tsum_congr
      intro z
      rw [hecoe z]
      rfl

/-- The preceding cell identity after translating the physical variable.
This is the exact Tonelli--tiling step used by the periodized kernel energy. -/
private theorem aux_zspan_lintegral_periodize_shift
    (b : Module.Basis (Fin 2) ℝ (Euclidean 2))
    (x : Euclidean 2) (E : Euclidean 2 → ENNReal)
    (hE : ∀ z : (Submodule.span ℤ (Set.range b)).toAddSubgroup,
      AEMeasurable (fun u : Euclidean 2 => E (x + (z +ᵥ u)))
        (volume.restrict (ZSpan.fundamentalDomain b))) :
    ∫⁻ u in ZSpan.fundamentalDomain b,
      (∑' z : (Submodule.span ℤ (Set.range b)).toAddSubgroup,
        E (x + (z +ᵥ u))) ∂volume =
      ∫⁻ y : Euclidean 2, E y ∂volume := by
  letI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range b))
    infer_instance
  have hU : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup
      (ZSpan.fundamentalDomain b) volume :=
    ZSpan.isAddFundamentalDomain' b volume
  have h := aux_cell_lintegral_periodize (μ := volume)
    (Submodule.span ℤ (Set.range b)).toAddSubgroup
    (ZSpan.fundamentalDomain b) hU
    (fun v : Euclidean 2 => E (x + v)) (by
      intro z
      simpa [vadd_eq_add, add_assoc] using hE z)
  simpa using h.trans (lintegral_add_left_eq_self E x)

/-- A summable Japanese-bracket majorant on a discrete integer lattice. -/
private theorem aux_summable_lattice_japanese
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (N : ℕ) (hN : Module.finrank ℤ L < N) :
    Summable (fun z : L ↦ if z = 0 then (1 : ℝ) else ‖z‖⁻¹ ^ N) := by
  classical
  have hNzero : N ≠ 0 := by omega
  have hdelta : Summable (fun z : L ↦ if z = 0 then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton (0 : L)).subset ?_
    intro z hz
    by_contra hzero
    have hne : z ≠ 0 := by simpa using hzero
    simp [Function.mem_support, hne] at hz
  have hbase := ZLattice.summable_norm_pow_inv L N hN
  refine (hdelta.add hbase).congr ?_
  intro z
  by_cases hz : z = 0
  · simp [hz, hNzero]
  · simp [hz]

/-- Uniform lattice majorant for a rapidly decaying kernel on a bounded
fundamental cell.  This supplies the finite periodization constant. -/
private theorem aux_exists_summable_uniform_lattice_majorant
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (K : E → F) (s : Set E) (R C : ℝ) (N : ℕ)
    (hN : Module.finrank ℤ L < N) (hR0 : 0 ≤ R) (hC : 0 ≤ C)
    (hR : ∀ v ∈ s, ‖v‖ ≤ R)
    (hdecay : ∀ y : E, ‖K y‖ ≤ C * (1 + ‖y‖)⁻¹ ^ N) :
    ∃ u : L → ℝ, Summable u ∧
      ∀ z : L, ∀ v ∈ s, ‖K ((z : E) + v)‖ ≤ u z := by
  classical
  let j : L → ℝ := fun z ↦ if z = 0 then 1 else ‖z‖⁻¹ ^ N
  let u : L → ℝ := fun z ↦ C * (1 + R) ^ N * j z
  refine ⟨u, ?_, ?_⟩
  · exact Summable.mul_left (C * (1 + R) ^ N)
      (aux_summable_lattice_japanese L N hN)
  intro z v hv
  have hvR : ‖v‖ ≤ R := hR v hv
  have hq : 0 < 1 + R := by linarith
  have ha : 0 < 1 + ‖(z : E) + v‖ := by positivity
  have hb : 0 < 1 + ‖(z : E)‖ := by positivity
  have hnorm : ‖(z : E)‖ ≤ ‖(z : E) + v‖ + ‖v‖ := by
    have h := norm_sub_le ((z : E) + v) v
    convert h using 1 <;> abel
  have hba : 1 + ‖(z : E)‖ ≤ (1 + R) * (1 + ‖(z : E) + v‖) := by
    nlinarith [mul_nonneg hR0 (norm_nonneg ((z : E) + v))]
  have hinv : (1 + ‖(z : E) + v‖)⁻¹ ≤
      (1 + R) * (1 + ‖(z : E)‖)⁻¹ := by
    calc
      (1 + ‖(z : E) + v‖)⁻¹ = 1 / (1 + ‖(z : E) + v‖) := (one_div _).symm
      _ ≤ (1 + R) / (1 + ‖(z : E)‖) :=
        (div_le_div_iff₀ ha hb).2 (by simpa [one_mul] using hba)
      _ = (1 + R) * (1 + ‖(z : E)‖)⁻¹ := div_eq_mul_inv _ _
  have hinvp : (1 + ‖(z : E) + v‖)⁻¹ ^ N ≤
      (1 + R) ^ N * (1 + ‖(z : E)‖)⁻¹ ^ N := by
    calc
      (1 + ‖(z : E) + v‖)⁻¹ ^ N ≤
          ((1 + R) * (1 + ‖(z : E)‖)⁻¹) ^ N :=
        pow_le_pow_left₀ (inv_nonneg.mpr ha.le) hinv N
      _ = (1 + R) ^ N * (1 + ‖(z : E)‖)⁻¹ ^ N := by rw [mul_pow]
  have hbase : (1 + ‖(z : E)‖)⁻¹ ^ N ≤ j z := by
    dsimp [j]
    by_cases hz : z = 0
    · simp [hz]
    · have hzpos : 0 < ‖(z : E)‖ := by
        exact norm_pos_iff.mpr (by simpa using hz)
      have hzb : ‖(z : E)‖ ≤ 1 + ‖(z : E)‖ := by linarith
      have hzinv : (1 + ‖(z : E)‖)⁻¹ ≤ ‖(z : E)‖⁻¹ :=
        (inv_le_inv₀ hb hzpos).2 hzb
      simpa [hz] using
        (pow_le_pow_left₀ (inv_nonneg.mpr hb.le) hzinv N)
  calc
    ‖K ((z : E) + v)‖ ≤ C * (1 + ‖(z : E) + v‖)⁻¹ ^ N := hdecay _
    _ ≤ C * ((1 + R) ^ N * j z) :=
      mul_le_mul_of_nonneg_left (hinvp.trans
        (mul_le_mul_of_nonneg_left hbase (pow_nonneg hq.le N))) hC
    _ = u z := by simp [u, mul_assoc]

/-- Every Schwartz kernel has polynomial Japanese-bracket decay of arbitrary
integer order. -/
private theorem aux_schwartz_one_add_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SchwartzMap E Complex) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E,
      ‖K y‖ ≤ C * (1 + ‖y‖)⁻¹ ^ N := by
  let C : ℝ := (2 : ℝ) ^ N *
    (Finset.Iic (N, 0)).sup (fun p ↦ SchwartzMap.seminorm Complex p.1 p.2) K
  have hweighted (y : E) : (1 + ‖y‖) ^ N * ‖K y‖ ≤ C := by
    dsimp [C]
    simpa only [norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := Complex)
        (m := (N, 0)) (k := N) (n := 0) (le_refl N) (le_refl 0) K y)
  have hC : 0 ≤ C := by
    calc
      0 ≤ (1 + ‖(0 : E)‖) ^ N * ‖K (0 : E)‖ := by positivity
      _ ≤ C := hweighted 0
  refine ⟨C, hC, ?_⟩
  intro y
  have hpos : 0 < (1 + ‖y‖) ^ N := by positivity
  calc
    ‖K y‖ ≤ C / (1 + ‖y‖) ^ N :=
      (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hweighted y)
    _ = C * (1 + ‖y‖)⁻¹ ^ N := by rw [div_eq_mul_inv, ← inv_pow]

/-- A fixed standard Euclidean cell has a summable lattice envelope for every
Schwartz kernel.  The resulting majorant is independent of the physical
translation used in the square-function proof. -/
private theorem aux_standard_euclidean_two_schwartz_envelope
    (K : SchwartzMap (Euclidean 2) Complex) (N : ℕ) (hN : 2 < N) :
    ∃ u : (Submodule.span ℤ
      (Set.range (PiLp.basisFun 2 ℝ (Fin 2)))) → ℝ, Summable u ∧
      ∀ z : (Submodule.span ℤ
        (Set.range (PiLp.basisFun 2 ℝ (Fin 2)))),
      ∀ v ∈ ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        ‖K ((z : Euclidean 2) + v)‖ ≤ u z := by
  classical
  let b : Module.Basis (Fin 2) ℝ (Euclidean 2) := PiLp.basisFun 2 ℝ (Fin 2)
  let L : Submodule ℤ (Euclidean 2) := Submodule.span ℤ (Set.range b)
  let U : Set (Euclidean 2) := ZSpan.fundamentalDomain b
  have hdim : Module.finrank ℤ L = 2 := by
    dsimp [L, b]
    rw [ZLattice.rank ℝ]
    exact finrank_euclideanSpace_fin
  obtain ⟨R0, hR0⟩ := (ZSpan.fundamentalDomain_isBounded b).subset_closedBall
    (0 : Euclidean 2)
  let R := max R0 0
  have hRnonneg : 0 ≤ R := le_max_right _ _
  have hR : ∀ v ∈ U, ‖v‖ ≤ R := by
    intro v hv
    have hvR := hR0 (by simpa [U, b] using hv)
    rw [Metric.mem_closedBall, dist_zero_right] at hvR
    exact hvR.trans (le_max_left _ _)
  obtain ⟨C, hC, hdecay⟩ := aux_schwartz_one_add_decay K N
  obtain ⟨u, hu, hubound⟩ :=
    aux_exists_summable_uniform_lattice_majorant L K U R C N
      (by rw [hdim]; exact hN) hRnonneg hC hR hdecay
  refine ⟨u, hu, ?_⟩
  intro z v hv
  exact hubound z v (by simpa [U, b] using hv)

/-- A summable lattice envelope yields absolute convergence and a uniform
bound for the periodized kernel itself on the fundamental cell. -/
private theorem aux_envelope_gives_bounded_periodization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (K : E → Complex) (s : Set E)
    (henv : ∃ u : L → ℝ, Summable u ∧
      ∀ z : L, ∀ v ∈ s, ‖K ((z : E) + v)‖ ≤ u z) :
    ∃ A : ℝ, ∀ v ∈ s,
      Summable (fun z : L ↦ K ((z : E) + v)) ∧
      ‖∑' z : L, K ((z : E) + v)‖ ≤ A := by
  obtain ⟨u, hu, hubound⟩ := henv
  refine ⟨∑' z : L, u z, ?_⟩
  intro v hv
  constructor
  · exact hu.of_norm_bounded (fun z ↦ hubound z v hv)
  · exact tsum_of_norm_bounded hu.hasSum (fun z ↦ hubound z v hv)

/-- The periodized lattice kernel is a genuine torus `L²` function.  The
proof uses only the uniform summable Schwartz envelope, before invoking
Fourier-series Bessel. -/
private theorem aux_latticePeriodizedTorus_memLp_two
    (x : Euclidean 2) (R : Real) (K f : SchwartzMap (Euclidean 2) Complex) :
    MemLp (aux_latticePeriodizedTorus x R K f) 2
      (volume : Measure (UnitAddTorus (Fin 2))) := by
  letI : Countable aux_standardLattice := by
    change Countable (Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin 2))))
    infer_instance
  obtain ⟨u, hu, hub⟩ :=
    aux_standard_euclidean_two_schwartz_envelope (aux_negatedSchwartz K) 3 (by norm_num)
  let B : Real := (SchwartzMap.seminorm Complex 0 0) f
  have hzero : (0 : Euclidean 2) ∈
      ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)) := by
    rw [ZSpan.mem_fundamentalDomain]
    intro i
    rw [PiLp.basisFun_repr]
    simp
  have hu0 : ∀ z : aux_standardLattice, 0 ≤ u z := by
    intro z
    exact (norm_nonneg _).trans (hub z 0 hzero)
  have hbound : ∀ t : UnitAddTorus (Fin 2),
      ‖aux_latticePeriodizedTorus x R K f t‖ ≤
        ∑' z : aux_standardLattice, u z * B := by
    intro t
    let r : Fin 2 → Real := aux_torusMinusRep t
    have hr : r ∈ aux_negUnitCoordCell := by
      dsimp [r]
      exact aux_torusMinusRep_mem_negUnitCoordCell t
    let v : Euclidean 2 := WithLp.toLp 2 (-r)
    have hv : v ∈ ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)) := by
      dsimp [v]
      exact aux_negCoord_to_standardFD r hr
    let a : aux_standardLattice → Complex := fun z =>
      (aux_negatedSchwartz K) ((z : Euclidean 2) + v) *
        f (x + R⁻¹ • ((z : Euclidean 2) + v))
    have hterm : ∀ z : aux_standardLattice, ‖a z‖ ≤ u z * B := by
      intro z
      rw [show ‖a z‖ = ‖(aux_negatedSchwartz K) ((z : Euclidean 2) + v)‖ *
          ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ by
        dsimp [a]
        rw [norm_mul]]
      exact mul_le_mul (hub z v hv) (SchwartzMap.norm_le_seminorm Complex f _)
        (norm_nonneg _) (hu0 z)
    have hnormsum : Summable (fun z : aux_standardLattice => ‖a z‖) := by
      apply (hu.mul_right B).of_nonneg_of_le
      · intro z
        exact norm_nonneg _
      · exact hterm
    have hH : aux_latticePeriodizedTorus x R K f t = ∑' z, a z := by
      unfold aux_latticePeriodizedTorus
      apply tsum_congr
      intro z
      dsimp [a]
      rw [← aux_negatedSchwartz_apply]
      simp only [v, r, WithLp.toLp_neg, sub_eq_add_neg]
    rw [hH]
    exact (norm_tsum_le_tsum_norm hnormsum).trans
      (hnormsum.tsum_le_tsum hterm (hu.mul_right B))
  exact MemLp.of_bound
    (aux_latticePeriodizedTorus_aestronglyMeasurable x R K f)
    (∑' z : aux_standardLattice, u z * B)
    (Filter.Eventually.of_forall hbound)

/-- The weighted Cauchy estimate for the actual periodized lattice kernel.
The `L¹` Schwartz envelope is the first factor; the second is precisely the
positive periodized energy which will tile back to a physical convolution. -/
private theorem aux_lattice_periodized_weighted_bound
    (K f Kneg : SchwartzMap (Euclidean 2) Complex)
    (hKneg : ∀ y : Euclidean 2, Kneg y = K (-y))
    (u : aux_standardLattice → Real) (hu : Summable u)
    (hub : ∀ z : aux_standardLattice,
      ∀ v ∈ ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        ‖Kneg ((z : Euclidean 2) + v)‖ ≤ u z)
    (x : Euclidean 2) (R : Real) (v : Euclidean 2)
    (hv : v ∈ ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2))) :
    ‖∑' z : aux_standardLattice,
      K (-((z : Euclidean 2) + v)) *
        f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2 ≤
      (∑' z : aux_standardLattice, u z) *
        (∑' z : aux_standardLattice, ‖K (-((z : Euclidean 2) + v))‖ *
          ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) := by
  letI : Countable aux_standardLattice := by
    change Countable (Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin 2))))
    infer_instance
  let w : aux_standardLattice → Real := fun z => ‖K (-((z : Euclidean 2) + v))‖
  let e : aux_standardLattice → Real := fun z =>
    w z * ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2
  let a : aux_standardLattice → Complex := fun z =>
    K (-((z : Euclidean 2) + v)) * f (x + R⁻¹ • ((z : Euclidean 2) + v))
  let B : Real := (SchwartzMap.seminorm Complex 0 0) f
  have hw0 : ∀ z : aux_standardLattice, 0 ≤ w z := by
    intro z
    exact norm_nonneg _
  have hwle : ∀ z : aux_standardLattice, w z ≤ u z := by
    intro z
    dsimp [w]
    rw [← hKneg]
    exact hub z v hv
  have hu0 : ∀ z : aux_standardLattice, 0 ≤ u z := by
    intro z
    exact (hw0 z).trans (hwle z)
  have hfbnd : ∀ z : aux_standardLattice,
      ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ≤ B := by
    intro z
    dsimp [B]
    exact SchwartzMap.norm_le_seminorm Complex f _
  have hfsq : ∀ z : aux_standardLattice,
      ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2 ≤ B ^ 2 := by
    intro z
    exact pow_le_pow_left₀ (norm_nonneg _) (hfbnd z) 2
  have hw : Summable w := hu.of_nonneg_of_le hw0 hwle
  have ha : Summable (fun z => ‖a z‖) := by
    apply (hu.mul_right B).of_nonneg_of_le
    · intro z
      exact norm_nonneg _
    · intro z
      rw [show ‖a z‖ = ‖K (-((z : Euclidean 2) + v))‖ *
          ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ by
          dsimp [a]
          rw [norm_mul]]
      exact mul_le_mul (hwle z) (hfbnd z) (norm_nonneg _) (hu0 z)
  have he0 : ∀ z : aux_standardLattice, 0 ≤ e z := by
    intro z
    dsimp [e]
    exact mul_nonneg (hw0 z) (sq_nonneg _)
  have hele : ∀ z : aux_standardLattice, e z ≤ u z * B ^ 2 := by
    intro z
    dsimp [e]
    exact mul_le_mul (hwle z) (hfsq z) (sq_nonneg _) (hu0 z)
  have he : Summable e := (hu.mul_right (B ^ 2)).of_nonneg_of_le he0 hele
  have hnorm : ∀ z : aux_standardLattice,
      ‖a z‖ = Real.sqrt (w z) * Real.sqrt (e z) := by
    intro z
    dsimp [a, e, w]
    rw [norm_mul, Real.sqrt_mul (norm_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
    nth_rewrite 1 [← Real.sq_sqrt (norm_nonneg (K (-((z : Euclidean 2) + v))))]
    ring
  have hmain := aux_tsum_norm_sq_le_weighted a w e ha hw he hw0 he0 hnorm
  have htsum : (∑' z : aux_standardLattice, w z) ≤ ∑' z : aux_standardLattice, u z :=
    hw.tsum_le_tsum hwle hu
  have hright : 0 ≤ ∑' z : aux_standardLattice, e z := tsum_nonneg he0
  have hlast := mul_le_mul_of_nonneg_right htsum hright
  simpa only [a, w, e] using hmain.trans hlast

/-- A single finite constant controls the weighted periodized energy at every
physical point and every common cube scale. -/
private theorem aux_lattice_weighted_bound_exists
    (K f : SchwartzMap (Euclidean 2) Complex) (N : Nat) (hN : 2 < N) :
    ∃ A : Real, 0 ≤ A ∧ ∀ (x : Euclidean 2) (R : Real) (v : Euclidean 2),
      v ∈ ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)) →
      ‖∑' z : aux_standardLattice,
        K (-((z : Euclidean 2) + v)) *
          f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2 ≤
        A * (∑' z : aux_standardLattice, ‖K (-((z : Euclidean 2) + v))‖ *
          ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) := by
  letI : Countable aux_standardLattice := by
    change Countable (Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin 2))))
    infer_instance
  obtain ⟨u, hu, hub⟩ :=
    aux_standard_euclidean_two_schwartz_envelope (aux_negatedSchwartz K) N hN
  refine ⟨∑' z : aux_standardLattice, u z, ?_, ?_⟩
  · have hzero : (0 : Euclidean 2) ∈
        ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)) := by
      rw [ZSpan.mem_fundamentalDomain]
      intro i
      rw [PiLp.basisFun_repr]
      simp
    apply tsum_nonneg
    intro z
    exact (norm_nonneg _).trans (hub z 0 hzero)
  · intro x R v hv
    exact aux_lattice_periodized_weighted_bound K f (aux_negatedSchwartz K)
      (aux_negatedSchwartz_apply K) u hu hub x R v hv

/-- The weighted periodization constant depends only on the common kernel,
not on the input or on the common cube scale. -/
private theorem aux_lattice_weighted_bound_exists_uniform
    (K : SchwartzMap (Euclidean 2) Complex) (N : Nat) (hN : 2 < N) :
    ∃ A : Real, 0 ≤ A ∧ ∀ (f : SchwartzMap (Euclidean 2) Complex)
      (x : Euclidean 2) (R : Real) (v : Euclidean 2),
      v ∈ ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)) →
      ‖∑' z : aux_standardLattice,
        K (-((z : Euclidean 2) + v)) *
          f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2 ≤
        A * (∑' z : aux_standardLattice, ‖K (-((z : Euclidean 2) + v))‖ *
          ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) := by
  letI : Countable aux_standardLattice := by
    change Countable (Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin 2))))
    infer_instance
  obtain ⟨u, hu, hub⟩ :=
    aux_standard_euclidean_two_schwartz_envelope (aux_negatedSchwartz K) N hN
  refine ⟨∑' z : aux_standardLattice, u z, ?_, ?_⟩
  · have hzero : (0 : Euclidean 2) ∈
        ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)) := by
      rw [ZSpan.mem_fundamentalDomain]
      intro i
      rw [PiLp.basisFun_repr]
      simp
    apply tsum_nonneg
    intro z
    exact (norm_nonneg _).trans (hub z 0 hzero)
  · intro f x R v hv
    exact aux_lattice_periodized_weighted_bound K f (aux_negatedSchwartz K)
      (aux_negatedSchwartz_apply K) u hu hub x R v hv

/-- The torus energy of a common-kernel lattice periodization is controlled
by a positive physical convolution, with a constant uniform in the input and
the common scale. -/
private theorem aux_latticePeriodizedTorus_energy_lintegral_le
    (K : SchwartzMap (Euclidean 2) Complex) :
    ∃ A : Real, 0 ≤ A ∧ ∀ (f : SchwartzMap (Euclidean 2) Complex)
      (x : Euclidean 2) (R : Real),
      (∫⁻ t : UnitAddTorus (Fin 2),
        ENNReal.ofReal (‖aux_latticePeriodizedTorus x R K f t‖ ^ 2)) ≤
        ENNReal.ofReal A *
          ∫⁻ v : Euclidean 2,
            ENNReal.ofReal ‖K (-v)‖ *
              ENNReal.ofReal (‖f (x + R⁻¹ • v)‖ ^ 2) := by
  letI : Countable aux_standardLattice := by
    change Countable (Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin 2))))
    infer_instance
  letI : Countable aux_standardLattice.toAddSubgroup := by
    change Countable aux_standardLattice
    infer_instance
  obtain ⟨A, hA, hbound⟩ :=
    aux_lattice_weighted_bound_exists_uniform K 3 (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro f x R
  let E : Euclidean 2 → ENNReal := fun y =>
    ENNReal.ofReal ‖K (-y)‖ *
      ENNReal.ofReal (‖f (x + R⁻¹ • y)‖ ^ 2)
  have hE : Measurable E := by
    dsimp [E]
    exact (ENNReal.measurable_ofReal.comp
      ((K.continuous.measurable.comp measurable_id.neg).norm)).mul
      (ENNReal.measurable_ofReal.comp
        ((f.continuous.measurable.comp
          (measurable_const.add (measurable_id.const_smul R⁻¹))).norm.pow_const 2))
  have hEshift (z : aux_standardLattice.toAddSubgroup) :
      Measurable (fun v : Euclidean 2 => E (z +ᵥ v)) := by
    exact hE.comp (measurable_const_vadd z)
  have hErestrict (z : aux_standardLattice.toAddSubgroup) :
      AEMeasurable (fun v : Euclidean 2 => E (z +ᵥ v))
        (volume.restrict (ZSpan.fundamentalDomain
          (PiLp.basisFun 2 ℝ (Fin 2)))) :=
    (hEshift z).aemeasurable.restrict
  have hU : IsAddFundamentalDomain aux_standardLattice.toAddSubgroup
      (ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2))) volume :=
    ZSpan.isAddFundamentalDomain' (PiLp.basisFun 2 ℝ (Fin 2)) volume
  have htile :
      ∫⁻ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        (∑' z : aux_standardLattice.toAddSubgroup, E (z +ᵥ v)) =
        ∫⁻ y : Euclidean 2, E y :=
    aux_cell_lintegral_periodize (μ := volume) aux_standardLattice.toAddSubgroup
      (ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2))) hU E hErestrict
  have htsumMeas : Measurable (fun v : Euclidean 2 =>
      ∑' z : aux_standardLattice.toAddSubgroup, E (z +ᵥ v)) :=
    Measurable.tsum hEshift
  have htorus :
      (∫⁻ t : UnitAddTorus (Fin 2),
        ENNReal.ofReal (‖aux_latticePeriodizedTorus x R K f t‖ ^ 2)) =
      ∫⁻ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        ENNReal.ofReal (‖∑' z : aux_standardLattice,
          K (-((z : Euclidean 2) + v)) *
            f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) := by
    calc
      (∫⁻ t : UnitAddTorus (Fin 2),
        ENNReal.ofReal (‖aux_latticePeriodizedTorus x R K f t‖ ^ 2)) =
        ∫⁻ t : UnitAddTorus (Fin 2),
          ‖aux_latticePeriodizedTorus x R K f t‖ₑ ^ (2 : Real) := by
            apply lintegral_congr
            intro t
            rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _) 2,
              ofReal_norm]
      _ = ∫⁻ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
          ‖∑' z : aux_standardLattice,
            K (-((z : Euclidean 2) + v)) *
              f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ₑ ^ (2 : Real) := by
        rw [UnitAddTorus.lintegral_preimage
          (fun t => ‖aux_latticePeriodizedTorus x R K f t‖ₑ ^ (2 : Real))
          (fun _ : Fin 2 => (-1 : Real))]
        change ∫⁻ u in aux_negUnitCoordCell,
            ‖aux_latticePeriodizedTorus x R K f
              (fun i => (u i : UnitAddCircle))‖ₑ ^ (2 : Real) = _
        rw [aux_lintegral_negCell_eq_lintegral_standardFD]
        apply setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
        intro v hv
        change ‖aux_latticePeriodizedTorus x R K f
            (fun i => ((aux_negCoordEquiv v i : Real) : UnitAddCircle))‖ₑ ^
              (2 : Real) = _
        rw [aux_negCoordEquiv_apply]
        rw [aux_latticePeriodizedTorus_apply_on_standardFD x R K f v hv]
      _ = ∫⁻ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
          ENNReal.ofReal (‖∑' z : aux_standardLattice,
            K (-((z : Euclidean 2) + v)) *
              f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) := by
        apply lintegral_congr
        intro v
        rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _) 2,
          ofReal_norm]
  have hsumENN (v : Euclidean 2)
      (hv : v ∈ ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2))) :
      ENNReal.ofReal (∑' z : aux_standardLattice,
        ‖K (-((z : Euclidean 2) + v))‖ *
          ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) =
        ∑' z : aux_standardLattice, E ((z : Euclidean 2) + v) := by
    obtain ⟨u, hu, hub⟩ :=
      aux_standard_euclidean_two_schwartz_envelope (aux_negatedSchwartz K) 3 (by norm_num)
    let B : Real := SchwartzMap.seminorm Complex 0 0 f
    have hsum : Summable (fun z : aux_standardLattice =>
        ‖K (-((z : Euclidean 2) + v))‖ *
          ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) := by
      apply (hu.mul_right (B ^ 2)).of_nonneg_of_le
      · intro z
        exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
      · intro z
        calc
          ‖K (-((z : Euclidean 2) + v))‖ *
              ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2 =
            ‖aux_negatedSchwartz K ((z : Euclidean 2) + v)‖ *
              ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2 := by
                rw [aux_negatedSchwartz_apply]
          _ ≤ u z * B ^ 2 := by
            apply mul_le_mul
            · exact hub z v hv
            · exact pow_le_pow_left₀ (norm_nonneg _)
                (SchwartzMap.norm_le_seminorm Complex f _) 2
            · exact sq_nonneg _
            · exact (norm_nonneg _).trans (hub z v hv)
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun z => mul_nonneg (norm_nonneg _) (sq_nonneg _)) hsum]
    apply tsum_congr
    intro z
    dsimp [E]
    rw [ENNReal.ofReal_mul (norm_nonneg _)]
  have hpoint (v : Euclidean 2)
      (hv : v ∈ ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2))) :
      ENNReal.ofReal (‖∑' z : aux_standardLattice,
        K (-((z : Euclidean 2) + v)) *
          f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) ≤
        ENNReal.ofReal A *
          ∑' z : aux_standardLattice.toAddSubgroup, E (z +ᵥ v) := by
    calc
      ENNReal.ofReal (‖∑' z : aux_standardLattice,
          K (-((z : Euclidean 2) + v)) *
            f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) ≤
          ENNReal.ofReal (A * (∑' z : aux_standardLattice,
            ‖K (-((z : Euclidean 2) + v))‖ *
              ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal (hbound f x R v hv)
      _ = ENNReal.ofReal A * ENNReal.ofReal (∑' z : aux_standardLattice,
          ‖K (-((z : Euclidean 2) + v))‖ *
            ‖f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) :=
        ENNReal.ofReal_mul hA
      _ = ENNReal.ofReal A *
          ∑' z : aux_standardLattice.toAddSubgroup, E (z +ᵥ v) := by
        rw [hsumENN v hv, aux_reindex_standard_lattice_tsum]
  calc
    (∫⁻ t : UnitAddTorus (Fin 2),
      ENNReal.ofReal (‖aux_latticePeriodizedTorus x R K f t‖ ^ 2)) =
        ∫⁻ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
          ENNReal.ofReal (‖∑' z : aux_standardLattice,
            K (-((z : Euclidean 2) + v)) *
              f (x + R⁻¹ • ((z : Euclidean 2) + v))‖ ^ 2) := htorus
    _ ≤ ∫⁻ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
        ENNReal.ofReal A *
          ∑' z : aux_standardLattice.toAddSubgroup, E (z +ᵥ v) := by
      apply setLIntegral_mono
      · exact measurable_const.mul htsumMeas
      intro v hv
      exact hpoint v hv
    _ = ENNReal.ofReal A *
        ∫⁻ v in ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 2)),
          ∑' z : aux_standardLattice.toAddSubgroup, E (z +ᵥ v) := by
      rw [lintegral_const_mul _ htsumMeas]
    _ = ENNReal.ofReal A * ∫⁻ y : Euclidean 2, E y := by rw [htile]
    _ = ENNReal.ofReal A *
        ∫⁻ v : Euclidean 2,
          ENNReal.ofReal ‖K (-v)‖ *
            ENNReal.ofReal (‖f (x + R⁻¹ • v)‖ ^ 2) := by rfl

/-- Translating a planar Schwartz multiplier in frequency modulates its
inverse Fourier transform by the corresponding unitary character. -/
private theorem aux_fourierInv_sub_e2
    (f : SchwartzMap (Euclidean 2) Complex) (a t : Euclidean 2) :
    FourierTransform.fourierInv
        (fun xi : Euclidean 2 => (f : Euclidean 2 → Complex) (xi - a)) t =
      SMul.smul (Real.fourierChar (inner ℝ a t))
        (FourierTransform.fourierInv (f : Euclidean 2 → Complex) t) := by
  rw [Real.fourierInv_eq_fourier_neg]
  have hshift := VectorFourier.fourierIntegral_comp_add_right
    (V := Euclidean 2) (W := Euclidean 2) (E := Complex)
    Real.fourierChar volume (innerₗ (Euclidean 2))
    (f : Euclidean 2 → Complex) (-a)
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (Euclidean 2))
      (fun xi : Euclidean 2 => (f : Euclidean 2 → Complex) (xi - a)) (-t) = _
  have htranslate :
      (fun xi : Euclidean 2 => (f : Euclidean 2 → Complex) (xi - a)) =
        Function.comp (f : Euclidean 2 → Complex) (fun xi : Euclidean 2 => xi + (-a)) := by
    funext xi
    rfl
  rw [htranslate, hshift]
  change SMul.smul (Real.fourierChar ((innerₗ (Euclidean 2) (-a)) (-t)))
      (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (Euclidean 2))
        (f : Euclidean 2 → Complex) (-t)) = _
  change SMul.smul (Real.fourierChar ((innerₗ (Euclidean 2) (-a)) (-t)))
      (FourierTransform.fourier (f : Euclidean 2 → Complex) (-t)) = _
  rw [← Real.fourierInv_eq_fourier_neg]
  change SMul.smul (Real.fourierChar ((innerₗ (Euclidean 2) (-a)) (-t)))
      (FourierTransform.fourierInv (f : Euclidean 2 → Complex) t) = _
  congr 1
  rw [innerₗ_apply_apply]
  rw [inner_neg_left, inner_neg_right]
  simp

/-- Physical kernel formula for a unit-scale translated Fourier-cube cutoff. -/
private theorem aux_fourierCubeKernel_translate
    (φ : SchwartzMap (Euclidean 2) Complex) (a z : Euclidean 2) :
    fourierCubeKernel (translatedDilatedSchwartzCutoff φ a 1 one_ne_zero) z =
      SMul.smul (Real.fourierChar (inner ℝ a z)) (fourierCubeKernel φ z) := by
  unfold fourierCubeKernel
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe]
  rw [show (translatedDilatedSchwartzCutoff φ a 1 one_ne_zero : Euclidean 2 → Complex) =
      fun xi : Euclidean 2 => (φ : Euclidean 2 → Complex) (xi - a) by
    funext xi
    rw [translatedDilatedSchwartzCutoff_apply]
    simp]
  exact aux_fourierInv_sub_e2 φ a z

/-- Physical kernel formula for a translated Fourier-cube cutoff at arbitrary
positive scale.  The common kernel has the expected two-dimensional Jacobian
and the translation contributes only a unitary character. -/
private theorem aux_fourierCubeKernel_translate_scale
    (φ : SchwartzMap (Euclidean 2) Complex) (a z : Euclidean 2)
    {R : Real} (hR : 0 < R) :
    fourierCubeKernel (translatedDilatedSchwartzCutoff φ a R hR.ne') z =
      SMul.smul (Real.fourierChar (inner ℝ a z))
        (SMul.smul (R ^ 2) (fourierCubeKernel φ (R • z))) := by
  let A : Euclidean 2 ≃L[Real] Euclidean 2 :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 R⁻¹ (inv_ne_zero hR.ne'))
  let ψ : SchwartzMap (Euclidean 2) Complex :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex A) φ
  have hψ (xi : Euclidean 2) : ψ xi = φ (R⁻¹ • xi) := by
    change φ (A xi) = φ (R⁻¹ • xi)
    simp [A]
  have hm (xi : Euclidean 2) :
      translatedDilatedSchwartzCutoff φ a R hR.ne' xi = ψ (xi - a) := by
    rw [translatedDilatedSchwartzCutoff_apply]
    exact (hψ (xi - a)).symm
  unfold fourierCubeKernel
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe]
  rw [show (translatedDilatedSchwartzCutoff φ a R hR.ne' : Euclidean 2 → Complex) =
      fun xi : Euclidean 2 => (ψ : Euclidean 2 → Complex) (xi - a) by
    funext xi
    exact hm xi]
  rw [aux_fourierInv_sub_e2 ψ a z]
  congr 1
  rw [show (ψ : Euclidean 2 → Complex) = fun xi : Euclidean 2 =>
      (φ : Euclidean 2 → Complex) (R⁻¹ • xi) by
    funext xi
    exact hψ xi]
  change FourierTransform.fourierInv
      (fun xi : Euclidean 2 => (φ : Euclidean 2 → Complex) (R⁻¹ • xi)) z =
    (R ^ 2 : Real) • FourierTransform.fourierInv
      (φ : Euclidean 2 → Complex) (R • z)
  simpa only [finrank_euclideanSpace_fin] using
    Auto.Spherical.Auxiliary.fourierInv_comp_inv_smul
      (φ : Euclidean 2 → Complex) hR z

/-- Source-kernel version of the arbitrary-scale lattice translation formula. -/
private theorem aux_fourierCubeSourceKernel_translate_scale
    (φ : SchwartzMap (Euclidean 2) Complex) (a x y : Euclidean 2)
    {R : Real} (hR : 0 < R) :
    fourierCubeSourceKernel
        (translatedDilatedSchwartzCutoff φ a R hR.ne') x y =
      SMul.smul (Real.fourierChar (inner ℝ a (x - y)))
        (SMul.smul (R ^ 2) (fourierCubeKernel φ (R • (x - y)))) := by
  unfold fourierCubeSourceKernel
  exact aux_fourierCubeKernel_translate_scale φ a (x - y) hR

/-- A common-scale lattice cube projection is the dilated common physical
kernel multiplied by the corresponding lattice character. -/
private theorem aux_fourierCubeProjection_translate_scale
    (φ f : SchwartzMap (Euclidean 2) Complex) (a x : Euclidean 2)
    {R : Real} (hR : 0 < R) :
    fourierCubeProjection (translatedDilatedSchwartzCutoff φ a R hR.ne') f x =
      ∫ y : Euclidean 2,
        (SMul.smul (Real.fourierChar (inner ℝ a (x - y)))
          (SMul.smul (R ^ 2) (fourierCubeKernel φ (R • (x - y))))) * f y := by
  rw [fourierCubeProjection_apply, fourierCubeProjection_eq_sourceKernel]
  apply integral_congr_ae
  filter_upwards with y
  rw [aux_fourierCubeSourceKernel_translate_scale φ a x y hR]

/-- The negative lattice coefficient seed at scale `R` is exactly the
corresponding translated/dilated Fourier-cube projection. -/
private theorem aux_latticeCoefficientSeed_integral_eq_fourierCubeProjection
    (φ f : SchwartzMap (Euclidean 2) Complex)
    (x : Euclidean 2) (R : Real) (k : Fin 2 → Int) (hR : 0 < R) :
    (∫ v : Euclidean 2,
      aux_latticeCoefficientSeed x R (FourierTransform.fourierInv φ) f k v) =
      fourierCubeProjection
        (translatedDilatedSchwartzCutoff φ (R • aux_intVec2 k) R hR.ne') f x := by
  let F : Euclidean 2 → Complex := fun y =>
    (Real.fourierChar (inner ℝ (R • aux_intVec2 k) (x - y)) : Complex) *
      fourierCubeKernel φ (R • (x - y)) * f y
  have hseed (v : Euclidean 2) :
      aux_latticeCoefficientSeed x R (FourierTransform.fourierInv φ) f k v =
        F (x + R⁻¹ • v) := by
    have hsub : x - (x + R⁻¹ • v) = -(R⁻¹ • v) := by module
    have hscaledsub : R • (x - (x + R⁻¹ • v)) = -v := by
      rw [hsub, smul_neg, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    have hphase : inner ℝ (R • aux_intVec2 k) (x - (x + R⁻¹ • v)) =
        -inner ℝ (aux_intVec2 k) v := by
      calc
        inner ℝ (R • aux_intVec2 k) (x - (x + R⁻¹ • v)) =
            inner ℝ (aux_intVec2 k) (R • (x - (x + R⁻¹ • v))) := by
              rw [real_inner_smul_left, real_inner_smul_right]
        _ = inner ℝ (aux_intVec2 k) (-v) := by rw [hscaledsub]
        _ = -inner ℝ (aux_intVec2 k) v := by rw [inner_neg_right]
    dsimp [F, aux_latticeCoefficientSeed]
    rw [hphase, hscaledsub]
    rfl
  have hdilate :
      (∫ v : Euclidean 2, F (x + R⁻¹ • v)) =
        (R ^ 2) • ∫ u : Euclidean 2, F (x + u) := by
    simpa only [finrank_euclideanSpace_fin] using
      (Measure.integral_comp_inv_smul_of_nonneg volume
        (fun u : Euclidean 2 => F (x + u)) hR.le)
  have htranslate : (∫ u : Euclidean 2, F (x + u)) = ∫ y : Euclidean 2, F y :=
    integral_add_left_eq_self F x
  calc
    (∫ v : Euclidean 2,
        aux_latticeCoefficientSeed x R (FourierTransform.fourierInv φ) f k v) =
        ∫ v : Euclidean 2, F (x + R⁻¹ • v) := by
          apply integral_congr_ae
          filter_upwards with v
          exact hseed v
    _ = (R ^ 2) • ∫ u : Euclidean 2, F (x + u) := hdilate
    _ = (R ^ 2) • ∫ y : Euclidean 2, F y := by rw [htranslate]
    _ = ∫ y : Euclidean 2, (R ^ 2) • F y := by
      rw [integral_smul]
    _ = fourierCubeProjection
        (translatedDilatedSchwartzCutoff φ (R • aux_intVec2 k) R hR.ne') f x := by
      rw [aux_fourierCubeProjection_translate_scale φ f (R • aux_intVec2 k) x hR]
      apply integral_congr_ae
      filter_upwards with y
      dsimp [F]
      change (↑(R ^ 2) : Complex) *
          ((Real.fourierChar (inner ℝ (R • aux_intVec2 k) (x - y)) : Complex) *
            fourierCubeKernel φ (R • (x - y)) * f y) =
        ((Real.fourierChar (inner ℝ (R • aux_intVec2 k) (x - y)) : Complex) *
          ((↑(R ^ 2) : Complex) * fourierCubeKernel φ (R • (x - y)))) * f y
      ring

/-- Finite common-scale lattice cube projections obey the torus Bessel
bound.  This is the exact orthogonality core of the equal-cube argument. -/
private theorem aux_lattice_fourierCubeProjection_finite_bessel
    (φ f : SchwartzMap (Euclidean 2) Complex)
    (x : Euclidean 2) (R : Real) (hR : 0 < R)
    (s : Finset (Fin 2 → Int)) :
    ∑ k ∈ s,
        ‖fourierCubeProjection
          (translatedDilatedSchwartzCutoff φ (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2 ≤
      ∫ t : UnitAddTorus (Fin 2),
        ‖aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f t‖ ^ 2 := by
  let H : UnitAddTorus (Fin 2) → Complex :=
    aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f
  have hH : MemLp H 2 (volume : Measure (UnitAddTorus (Fin 2))) := by
    change MemLp
      (aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f) 2
      (volume : Measure (UnitAddTorus (Fin 2)))
    exact aux_latticePeriodizedTorus_memLp_two
      x R (FourierTransform.fourierInv φ) f
  have hcoeff (k : Fin 2 → Int) :
      UnitAddTorus.mFourierCoeff (hH.toLp H).1 (-k) =
        fourierCubeProjection
          (translatedDilatedSchwartzCutoff φ (R • aux_intVec2 k) R hR.ne') f x := by
    calc
      UnitAddTorus.mFourierCoeff (hH.toLp H).1 (-k) =
          UnitAddTorus.mFourierCoeff H (-k) :=
        aux_mFourierCoeff_toLp_eq H hH (-k)
      _ = ∫ v : Euclidean 2,
          aux_latticeCoefficientSeed x R (FourierTransform.fourierInv φ) f k v := by
        change UnitAddTorus.mFourierCoeff
          (aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f) (-k) = _
        exact aux_latticePeriodizedTorus_mFourierCoeff_neg_eq_seed_integral
          x R (FourierTransform.fourierInv φ) f k
          (aux_latticeCoefficientSeed_integrable
            x R (FourierTransform.fourierInv φ) f k)
      _ = fourierCubeProjection
          (translatedDilatedSchwartzCutoff φ (R • aux_intVec2 k) R hR.ne') f x :=
        aux_latticeCoefficientSeed_integral_eq_fourierCubeProjection φ f x R k hR
  have hneg : Set.InjOn (fun k : Fin 2 → Int => -k)
      (s : Set (Fin 2 → Int)) :=
    neg_injective.injOn
  calc
    ∑ k ∈ s,
        ‖fourierCubeProjection
          (translatedDilatedSchwartzCutoff φ (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2 =
      ∑ k ∈ s, ‖UnitAddTorus.mFourierCoeff (hH.toLp H).1 (-k)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hcoeff k]
    _ = ∑ n ∈ s.image (fun k : Fin 2 → Int => -k),
        ‖UnitAddTorus.mFourierCoeff (hH.toLp H).1 n‖ ^ 2 := by
      symm
      exact Finset.sum_image
        (f := fun n : Fin 2 → Int =>
          ‖UnitAddTorus.mFourierCoeff (hH.toLp H).1 n‖ ^ 2) hneg
    _ ≤ ∫ t : UnitAddTorus (Fin 2), ‖H t‖ ^ 2 :=
      aux_torus_finite_bessel_of_memLp H hH
        (s.image (fun k : Fin 2 → Int => -k))

/-- The preceding Bessel bound in the nonnegative extended-integral form
needed for the fourth-moment closure. -/
private theorem aux_lattice_fourierCubeProjection_finite_bessel_ennreal
    (φ f : SchwartzMap (Euclidean 2) Complex)
    (x : Euclidean 2) (R : Real) (hR : 0 < R)
    (s : Finset (Fin 2 → Int)) :
    ENNReal.ofReal (∑ k ∈ s,
      ‖fourierCubeProjection
        (translatedDilatedSchwartzCutoff φ (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2) ≤
      ∫⁻ t : UnitAddTorus (Fin 2),
        ENNReal.ofReal
          (‖aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f t‖ ^ 2) := by
  have hHsq : Integrable (fun t : UnitAddTorus (Fin 2) =>
      ‖aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f t‖ ^
        (2 : Nat)) (volume : Measure (UnitAddTorus (Fin 2))) := by
    simpa using
      (aux_latticePeriodizedTorus_memLp_two x R
        (FourierTransform.fourierInv φ) f).integrable_norm_rpow
          (by norm_num : (2 : ENNReal) ≠ 0) ENNReal.ofNat_ne_top
  calc
    ENNReal.ofReal (∑ k ∈ s,
        ‖fourierCubeProjection
          (translatedDilatedSchwartzCutoff φ (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2) ≤
        ENNReal.ofReal (∫ t : UnitAddTorus (Fin 2),
          ‖aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f t‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (aux_lattice_fourierCubeProjection_finite_bessel φ f x R hR s)
    _ = ∫⁻ t : UnitAddTorus (Fin 2),
        ENNReal.ofReal
          (‖aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f t‖ ^ 2) :=
      ofReal_integral_eq_lintegral_ofReal hHsq
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-- Given the uniform positive torus-energy bound, Bessel and Young yield
the fourth moment of the finite common-scale lattice projection energy. -/
private theorem aux_lattice_projection_energy_lintegral_sq_le_of_energy
    (φ f : SchwartzMap (Euclidean 2) Complex)
    (R : Real) (hR : 0 < R) (s : Finset (Fin 2 → Int)) {A : Real}
    (henergy : ∀ x : Euclidean 2,
      (∫⁻ t : UnitAddTorus (Fin 2),
        ENNReal.ofReal
          (‖aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f t‖ ^ 2)) ≤
        ENNReal.ofReal A *
          ∫⁻ v : Euclidean 2,
            ENNReal.ofReal ‖(FourierTransform.fourierInv φ) (-v)‖ *
              ENNReal.ofReal (‖f (x + R⁻¹ • v)‖ ^ (2 : Nat))) :
    (∫⁻ x : Euclidean 2,
      ENNReal.ofReal ((∑ k ∈ s,
        ‖fourierCubeProjection
          (translatedDilatedSchwartzCutoff φ (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2) ^
            (2 : Nat))) ≤
      (ENNReal.ofReal A) ^ (2 : Nat) *
        (∫⁻ v : Euclidean 2,
          ENNReal.ofReal ‖(FourierTransform.fourierInv φ) v‖) ^ (2 : Nat) *
          ∫⁻ x : Euclidean 2, ENNReal.ofReal (‖f x‖ ^ (4 : Nat)) := by
  let K : SchwartzMap (Euclidean 2) Complex := FourierTransform.fourierInv φ
  let q : Euclidean 2 → ENNReal := fun y =>
    ENNReal.ofReal (‖f y‖ ^ (2 : Nat))
  let Q : Euclidean 2 → ENNReal := fun x =>
    ∫⁻ v : Euclidean 2,
      ENNReal.ofReal ‖K (-v)‖ * q (x + R⁻¹ • v)
  let T : Euclidean 2 → Real := fun x => ∑ k ∈ s,
    ‖fourierCubeProjection
      (translatedDilatedSchwartzCutoff φ (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2
  have hTnonneg (x : Euclidean 2) : 0 ≤ T x := by
    dsimp [T]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hBessel (x : Euclidean 2) :
      ENNReal.ofReal (T x) ≤
        ∫⁻ t : UnitAddTorus (Fin 2),
          ENNReal.ofReal
            (‖aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f t‖ ^ 2) := by
    simpa only [T] using
      aux_lattice_fourierCubeProjection_finite_bessel_ennreal φ f x R hR s
  have henergy' (x : Euclidean 2) :
      (∫⁻ t : UnitAddTorus (Fin 2),
        ENNReal.ofReal
          (‖aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f t‖ ^ 2)) ≤
        ENNReal.ofReal A * Q x := by
    simpa only [K, q, Q] using henergy x
  have hpoint (x : Euclidean 2) :
      ENNReal.ofReal ((T x) ^ (2 : Nat)) ≤
        (ENNReal.ofReal A) ^ (2 : Nat) * (Q x) ^ (2 : Nat) := by
    calc
      ENNReal.ofReal ((T x) ^ (2 : Nat)) =
          (ENNReal.ofReal (T x)) ^ (2 : Nat) :=
        ENNReal.ofReal_pow (hTnonneg x) 2
      _ ≤ (∫⁻ t : UnitAddTorus (Fin 2),
          ENNReal.ofReal
            (‖aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f t‖ ^ 2)) ^
              (2 : Nat) :=
        pow_le_pow_left' (hBessel x) 2
      _ ≤ (ENNReal.ofReal A * Q x) ^ (2 : Nat) :=
        pow_le_pow_left' (henergy' x) 2
      _ = (ENNReal.ofReal A) ^ (2 : Nat) * (Q x) ^ (2 : Nat) := by
        rw [mul_pow]
  have hKmeas : Measurable (fun v : Euclidean 2 => ENNReal.ofReal ‖K v‖) :=
    ENNReal.measurable_ofReal.comp (K.continuous.measurable.norm)
  have hqmeas : Measurable q := by
    dsimp [q]
    exact ENNReal.measurable_ofReal.comp
      ((f.continuous.measurable.norm).pow_const 2)
  have hQmeas : Measurable Q := by
    dsimp [Q]
    exact ((hKmeas.comp measurable_snd.neg).mul
      (hqmeas.comp (measurable_fst.add
        (measurable_snd.const_smul R⁻¹)))).lintegral_prod_right
  have hyoung :
      (∫⁻ x : Euclidean 2, (Q x) ^ (2 : Nat)) ≤
        (∫⁻ v : Euclidean 2, ENNReal.ofReal ‖K v‖) ^ (2 : Nat) *
          ∫⁻ x : Euclidean 2, (q x) ^ (2 : Nat) := by
    simpa only [Q, ENNReal.rpow_two] using
      (aux_scaled_weighted_young_two
        (fun v : Euclidean 2 => ENNReal.ofReal ‖K v‖) q hKmeas hqmeas R)
  have hqfour :
      (∫⁻ x : Euclidean 2, (q x) ^ (2 : Nat)) =
        ∫⁻ x : Euclidean 2, ENNReal.ofReal (‖f x‖ ^ (4 : Nat)) := by
    apply lintegral_congr
    intro x
    dsimp [q]
    rw [← ENNReal.ofReal_pow (sq_nonneg _) 2]
    congr 1
    ring
  have hfinal :
      (∫⁻ x : Euclidean 2, ENNReal.ofReal ((T x) ^ (2 : Nat))) ≤
        (ENNReal.ofReal A) ^ (2 : Nat) *
          (∫⁻ v : Euclidean 2, ENNReal.ofReal ‖K v‖) ^ (2 : Nat) *
            ∫⁻ x : Euclidean 2, ENNReal.ofReal (‖f x‖ ^ (4 : Nat)) := by
    calc
      (∫⁻ x : Euclidean 2, ENNReal.ofReal ((T x) ^ (2 : Nat))) ≤
          ∫⁻ x : Euclidean 2,
            (ENNReal.ofReal A) ^ (2 : Nat) * (Q x) ^ (2 : Nat) :=
        lintegral_mono hpoint
      _ = (ENNReal.ofReal A) ^ (2 : Nat) *
          ∫⁻ x : Euclidean 2, (Q x) ^ (2 : Nat) := by
        rw [lintegral_const_mul _ (hQmeas.pow_const 2)]
      _ ≤ (ENNReal.ofReal A) ^ (2 : Nat) *
          ((∫⁻ v : Euclidean 2, ENNReal.ofReal ‖K v‖) ^ (2 : Nat) *
            ∫⁻ x : Euclidean 2, (q x) ^ (2 : Nat)) :=
        by
          simpa only [mul_comm] using
            (mul_le_mul_left hyoung ((ENNReal.ofReal A) ^ (2 : Nat)))
      _ = (ENNReal.ofReal A) ^ (2 : Nat) *
          (∫⁻ v : Euclidean 2, ENNReal.ofReal ‖K v‖) ^ (2 : Nat) *
            ∫⁻ x : Euclidean 2, ENNReal.ofReal (‖f x‖ ^ (4 : Nat)) := by
        rw [hqfour]
        ac_rfl
  simpa only [K, T] using hfinal

/-- The preceding fourth-moment bound is exactly the `L⁴` bound for the
finite common-scale lattice Fourier-cube square function. -/
private theorem aux_lattice_fourierCubeSquareFunction_lintegral_four_of_energy
    (φ f : SchwartzMap (Euclidean 2) Complex)
    (R : Real) (hR : 0 < R) (s : Finset (Fin 2 → Int)) {A : Real}
    (henergy : ∀ x : Euclidean 2,
      (∫⁻ t : UnitAddTorus (Fin 2), ENNReal.ofReal
        (‖aux_latticePeriodizedTorus x R (FourierTransform.fourierInv φ) f t‖ ^ 2)) ≤
      ENNReal.ofReal A * ∫⁻ v : Euclidean 2,
        ENNReal.ofReal ‖(FourierTransform.fourierInv φ) (-v)‖ *
          ENNReal.ofReal (‖f (x + R⁻¹ • v)‖ ^ (2 : Nat))) :
    (∫⁻ x : Euclidean 2,
      ENNReal.ofReal
        (fourierCubeSquareFunction s
          (fun k => translatedDilatedSchwartzCutoff φ
            (R • aux_intVec2 k) R hR.ne') f x ^ (4 : Nat))) ≤
      (ENNReal.ofReal A) ^ (2 : Nat) *
        (∫⁻ v : Euclidean 2,
          ENNReal.ofReal ‖(FourierTransform.fourierInv φ) v‖) ^ (2 : Nat) *
          ∫⁻ x : Euclidean 2, ENNReal.ofReal (‖f x‖ ^ (4 : Nat)) := by
  calc
    (∫⁻ x : Euclidean 2,
      ENNReal.ofReal
        (fourierCubeSquareFunction s
          (fun k => translatedDilatedSchwartzCutoff φ
            (R • aux_intVec2 k) R hR.ne') f x ^ (4 : Nat))) =
        ∫⁻ x : Euclidean 2, ENNReal.ofReal
          ((∑ k ∈ s,
            ‖fourierCubeProjection
              (translatedDilatedSchwartzCutoff φ
                (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2) ^ (2 : Nat)) := by
      apply lintegral_congr
      intro x
      congr 1
      unfold fourierCubeSquareFunction
      have hnonneg : 0 ≤ ∑ k ∈ s,
          ‖fourierCubeProjection
            (translatedDilatedSchwartzCutoff φ
              (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc
        (Real.sqrt (∑ k ∈ s,
          ‖fourierCubeProjection
            (translatedDilatedSchwartzCutoff φ
              (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2)) ^ (4 : Nat) =
            (Real.sqrt (∑ k ∈ s,
              ‖fourierCubeProjection
                (translatedDilatedSchwartzCutoff φ
                  (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2) ^ 2) ^ 2 := by ring
        _ = (∑ k ∈ s,
          ‖fourierCubeProjection
            (translatedDilatedSchwartzCutoff φ
              (R • aux_intVec2 k) R hR.ne') f x‖ ^ 2) ^ (2 : Nat) := by
          rw [Real.sq_sqrt hnonneg]
    _ ≤ _ := aux_lattice_projection_energy_lintegral_sq_le_of_energy
      φ f R hR s henergy

/-- Uniform fourth-moment bound for a finite family of translated copies of
one common smooth cutoff on a common integer lattice and common positive
scale.  This is the completed fixed-lattice equal-cube square-function
estimate. -/
private theorem aux_lattice_fourierCubeSquareFunction_lintegral_four
    (φ : SchwartzMap (Euclidean 2) Complex) :
    ∃ A : Real, 0 ≤ A ∧ ∀ (f : SchwartzMap (Euclidean 2) Complex)
      (R : Real) (hR : 0 < R) (s : Finset (Fin 2 → Int)),
      (∫⁻ x : Euclidean 2,
        ENNReal.ofReal
          (fourierCubeSquareFunction s
            (fun k => translatedDilatedSchwartzCutoff φ
              (R • aux_intVec2 k) R hR.ne') f x ^ (4 : Nat))) ≤
        (ENNReal.ofReal A) ^ (2 : Nat) *
          (∫⁻ v : Euclidean 2,
            ENNReal.ofReal ‖(FourierTransform.fourierInv φ) v‖) ^ (2 : Nat) *
            ∫⁻ x : Euclidean 2, ENNReal.ofReal (‖f x‖ ^ (4 : Nat)) := by
  obtain ⟨A, hA, henergy⟩ :=
    aux_latticePeriodizedTorus_energy_lintegral_le (FourierTransform.fourierInv φ)
  refine ⟨A, hA, ?_⟩
  intro f R hR s
  apply aux_lattice_fourierCubeSquareFunction_lintegral_four_of_energy φ f R hR s
  intro x
  exact henergy f x R

/-- The finite smooth equal-cube Fourier square function on one translated
integer lattice obeys a uniform fourth-moment estimate.  This is the literal
fixed-prototype lattice case of the Fourier-cube theorem: its constant is
independent of the positive lattice scale and of the finite selected cube
family. -/
theorem latticeFourierCubeSquareFunction_lintegral_four
    (φ : SchwartzMap (Euclidean 2) Complex) :
    ∃ A : Real, 0 ≤ A ∧ ∀ (f : SchwartzMap (Euclidean 2) Complex)
      (R : Real) (hR : 0 < R) (s : Finset (Fin 2 → Int)),
      (∫⁻ x : Euclidean 2,
        ENNReal.ofReal
          (fourierCubeSquareFunction s
            (fun k => translatedDilatedSchwartzCutoff φ
              (R • standardLatticePoint k) R hR.ne') f x ^ (4 : Nat))) ≤
        (ENNReal.ofReal A) ^ (2 : Nat) *
          (∫⁻ v : Euclidean 2,
            ENNReal.ofReal ‖(FourierTransform.fourierInv φ) v‖) ^ (2 : Nat) *
            ∫⁻ x : Euclidean 2, ENNReal.ofReal (‖f x‖ ^ (4 : Nat)) := by
  simpa only [aux_intVec2] using
    aux_lattice_fourierCubeSquareFunction_lintegral_four φ

/-- The positive frequency scale of a fixed lattice of MSS analysis cubes. -/
def latticeCubeScale (spacing scale : Real) : Real :=
  spacing * Real.sqrt scale

/-- At every MSS scale, a positive lattice spacing remains positive. -/
theorem latticeCubeScale_pos {spacing scale : Real} (hspacing : 0 < spacing)
    (hscale : 2 ≤ scale) : 0 < latticeCubeScale spacing scale := by
  unfold latticeCubeScale
  exact mul_pos hspacing (Real.sqrt_pos.2 (by linarith))

/-! ### A fixed smooth planar lattice partition -/

/-- A compactly supported smooth one-dimensional lattice synthesis piece.
Its integer translates telescope to one. -/
private def mssUnitLatticeTransitionPiece (t : Real) : Real :=
  Real.smoothTransition (t + 1) - Real.smoothTransition t

private theorem mssUnitLatticeTransitionPiece_contDiff :
    ContDiff Real (⊤ : ℕ∞) mssUnitLatticeTransitionPiece := by
  unfold mssUnitLatticeTransitionPiece
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

private theorem mssUnitLatticeTransitionPiece_nonneg (t : Real) :
    0 ≤ mssUnitLatticeTransitionPiece t := by
  unfold mssUnitLatticeTransitionPiece
  exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

private theorem mssUnitLatticeTransitionPiece_le_one (t : Real) :
    mssUnitLatticeTransitionPiece t ≤ 1 := by
  unfold mssUnitLatticeTransitionPiece
  nlinarith [Real.smoothTransition.le_one (t + 1),
    Real.smoothTransition.nonneg t]

private theorem mssUnitLatticeTransitionPiece_eq_zero_of_le_neg_one
    {t : Real} (ht : t ≤ -1) : mssUnitLatticeTransitionPiece t = 0 := by
  unfold mssUnitLatticeTransitionPiece
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

private theorem mssUnitLatticeTransitionPiece_eq_zero_of_one_le
    {t : Real} (ht : 1 ≤ t) : mssUnitLatticeTransitionPiece t = 0 := by
  unfold mssUnitLatticeTransitionPiece
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le ht]
  ring

private theorem mssUnitLatticeTransitionPiece_support_subset :
    Function.support mssUnitLatticeTransitionPiece ⊆ Set.Icc (-1 : Real) 1 := by
  intro t ht
  constructor
  · by_contra h
    exact ht (mssUnitLatticeTransitionPiece_eq_zero_of_le_neg_one
      (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact ht (mssUnitLatticeTransitionPiece_eq_zero_of_one_le
      (le_of_lt (lt_of_not_ge h)))

private theorem mssUnitLatticeTransitionPiece_hasCompactSupport :
    HasCompactSupport mssUnitLatticeTransitionPiece := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (-1 : Real) 1))
  exact mssUnitLatticeTransitionPiece_support_subset

private theorem mss_sum_range_unitLatticeTransitionPiece (u : Real) :
    ∀ m : Nat,
      (∑ j ∈ Finset.range m,
        mssUnitLatticeTransitionPiece (u - (j : Real))) =
        Real.smoothTransition (u + 1) -
          Real.smoothTransition (u - (m : Real) + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      unfold mssUnitLatticeTransitionPiece
      norm_num [Nat.cast_succ]
      ring_nf

/-- Every finite consecutive sum of the nonnegative one-dimensional lattice
pieces is bounded by one, even outside the interval where it is a partition. -/
private theorem mss_sum_range_unitLatticeTransitionPiece_nonneg_le_one
    (u : Real) (m : Nat) :
    0 ≤ ∑ j ∈ Finset.range m, mssUnitLatticeTransitionPiece (u - (j : Real)) ∧
      (∑ j ∈ Finset.range m,
        mssUnitLatticeTransitionPiece (u - (j : Real))) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun j hj => mssUnitLatticeTransitionPiece_nonneg _
  · rw [mss_sum_range_unitLatticeTransitionPiece]
    have hupper : Real.smoothTransition (u + 1) ≤ 1 :=
      Real.smoothTransition.le_one _
    have hlower : 0 ≤ Real.smoothTransition (u - (m : Real) + 1) :=
      Real.smoothTransition.nonneg _
    linarith

private theorem mss_finite_unitLatticeTransition_partition
    {t : Real} (N : Nat) (ht : |t| ≤ (N : Real)) :
    (∑ j ∈ Finset.range (2 * N + 1),
      mssUnitLatticeTransitionPiece (t + (N : Real) - (j : Real))) = 1 := by
  rw [mss_sum_range_unitLatticeTransitionPiece (t + (N : Real)) (2 * N + 1)]
  rw [Real.smoothTransition.one_of_one_le (by
      rw [abs_le] at ht
      linarith),
    Real.smoothTransition.zero_of_nonpos (by
      rw [abs_le] at ht
      push_cast
      linarith)]
  norm_num

/-- The tensor product of the one-dimensional pieces is the fixed planar
smooth synthesis prototype for the lattice construction. -/
private def mssLatticeSynthesisReal (x : Euclidean 2) : Real :=
  mssUnitLatticeTransitionPiece (x 0) *
    mssUnitLatticeTransitionPiece (x 1)

private theorem mssLatticeSynthesisReal_nonneg (x : Euclidean 2) :
    0 ≤ mssLatticeSynthesisReal x := by
  unfold mssLatticeSynthesisReal
  exact mul_nonneg (mssUnitLatticeTransitionPiece_nonneg _)
    (mssUnitLatticeTransitionPiece_nonneg _)

private def mssLatticeSynthesisRaw (x : Euclidean 2) : Complex :=
  mssLatticeSynthesisReal x

private theorem mssLatticeSynthesisReal_contDiff :
    ContDiff Real (⊤ : ℕ∞) mssLatticeSynthesisReal := by
  unfold mssLatticeSynthesisReal
  exact
    (mssUnitLatticeTransitionPiece_contDiff.comp
      (contDiff_piLp_apply (p := (2 : ENNReal)) (i := (0 : Fin 2)))).mul
      (mssUnitLatticeTransitionPiece_contDiff.comp
        (contDiff_piLp_apply (p := (2 : ENNReal)) (i := (1 : Fin 2))))

private theorem mssLatticeSynthesisRaw_contDiff :
    ContDiff Real (⊤ : ℕ∞) mssLatticeSynthesisRaw := by
  unfold mssLatticeSynthesisRaw
  exact Complex.ofRealCLM.contDiff.comp mssLatticeSynthesisReal_contDiff

private theorem mssLatticeSynthesisRaw_support_subset :
    Function.support mssLatticeSynthesisRaw ⊆ frequencyCube 0 1 := by
  intro x hx
  have hprod : mssUnitLatticeTransitionPiece (x 0) *
      mssUnitLatticeTransitionPiece (x 1) ≠ 0 := by
    intro hzero
    apply hx
    simp [mssLatticeSynthesisRaw, mssLatticeSynthesisReal, hzero]
  have hnonzero := (mul_ne_zero_iff.mp hprod)
  rw [mem_frequencyCube_iff]
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · change |x 0 - (0 : Euclidean 2) 0| ≤ 1
    simpa only [WithLp.ofLp_zero, Pi.zero_apply, sub_zero] using
      (abs_le.mpr (mssUnitLatticeTransitionPiece_support_subset hnonzero.1))
  · change |x 1 - (0 : Euclidean 2) 1| ≤ 1
    simpa only [WithLp.ofLp_zero, Pi.zero_apply, sub_zero] using
      (abs_le.mpr (mssUnitLatticeTransitionPiece_support_subset hnonzero.2))

private theorem mssLatticeSynthesisRaw_norm_le_two_of_ne_zero
    {x : Euclidean 2} (hx : mssLatticeSynthesisRaw x ≠ 0) : ‖x‖ ≤ 2 := by
  have hcube := mssLatticeSynthesisRaw_support_subset hx
  have hcoord0 : -1 ≤ x 0 ∧ x 0 ≤ 1 := by
    simpa only [WithLp.ofLp_zero, Pi.zero_apply, sub_zero] using (abs_le.mp (hcube 0))
  have hcoord1 : -1 ≤ x 1 ∧ x 1 ≤ 1 := by
    simpa only [WithLp.ofLp_zero, Pi.zero_apply, sub_zero] using (abs_le.mp (hcube 1))
  have hnormsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => Real) x
  rw [Fin.sum_univ_two] at hnormsq
  simp only [Real.norm_eq_abs, sq_abs] at hnormsq
  nlinarith [norm_nonneg x]

private theorem mssLatticeSynthesisRaw_hasCompactSupport :
    HasCompactSupport mssLatticeSynthesisRaw := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean 2) 2)
  intro x hx
  by_contra hzero
  apply hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (mssLatticeSynthesisRaw_norm_le_two_of_ne_zero hzero)

private noncomputable def mssLatticeSynthesisPrototype :
    SchwartzMap (Euclidean 2) Complex :=
  mssLatticeSynthesisRaw_hasCompactSupport.toSchwartzMap mssLatticeSynthesisRaw_contDiff

private theorem mssLatticeSynthesisPrototype_apply (x : Euclidean 2) :
    mssLatticeSynthesisPrototype x = mssLatticeSynthesisRaw x := by rfl

/-- A fixed broad analysis bump, equal to one on the radius-two ball which
contains the support of the lattice synthesis profile. -/
private noncomputable def mssLatticeAnalysisBump : ContDiffBump (0 : Euclidean 2) :=
  ⟨2, 3, by norm_num, by norm_num⟩

private noncomputable def mssLatticeAnalysisRaw (x : Euclidean 2) : Complex :=
  mssLatticeAnalysisBump x

private theorem mssLatticeAnalysisRaw_contDiff :
    ContDiff Real (⊤ : ℕ∞) mssLatticeAnalysisRaw := by
  unfold mssLatticeAnalysisRaw
  exact Complex.ofRealCLM.contDiff.comp mssLatticeAnalysisBump.contDiff

private theorem mssLatticeAnalysisRaw_hasCompactSupport :
    HasCompactSupport mssLatticeAnalysisRaw := by
  unfold mssLatticeAnalysisRaw
  exact mssLatticeAnalysisBump.hasCompactSupport.comp_left Complex.ofRealCLM.map_zero

private theorem mssLatticeAnalysisRaw_support_subset :
    Function.support mssLatticeAnalysisRaw ⊆ frequencyCube 0 3 := by
  intro x hx
  have hbump : mssLatticeAnalysisBump x ≠ 0 := by
    intro hzero
    apply hx
    simp [mssLatticeAnalysisRaw, hzero]
  have hball : ‖x‖ < 3 := by
    have hmem : x ∈ Function.support mssLatticeAnalysisBump := hbump
    rw [mssLatticeAnalysisBump.support_eq] at hmem
    simpa [mssLatticeAnalysisBump] using hmem
  rw [mem_frequencyCube_iff]
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · change |x 0 - (0 : Euclidean 2) 0| ≤ 3
    simp only [WithLp.ofLp_zero, Pi.zero_apply, sub_zero]
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x 0).trans hball.le
  · change |x 1 - (0 : Euclidean 2) 1| ≤ 3
    simp only [WithLp.ofLp_zero, Pi.zero_apply, sub_zero]
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x 1).trans hball.le

private noncomputable def mssLatticeAnalysisPrototype :
    SchwartzMap (Euclidean 2) Complex :=
  mssLatticeAnalysisRaw_hasCompactSupport.toSchwartzMap mssLatticeAnalysisRaw_contDiff

private theorem mssLatticeAnalysisPrototype_apply (x : Euclidean 2) :
    mssLatticeAnalysisPrototype x = mssLatticeAnalysisRaw x := by rfl

/-- The fixed analysis prototype absorbs the fixed synthesis prototype. -/
private theorem mssLatticeSynthesisRaw_mul_analysisRaw (x : Euclidean 2) :
    mssLatticeSynthesisRaw x * mssLatticeAnalysisRaw x =
      mssLatticeSynthesisRaw x := by
  by_cases hx : mssLatticeSynthesisRaw x = 0
  · rw [hx, zero_mul]
  · have hnorm : ‖x‖ ≤ 2 := mssLatticeSynthesisRaw_norm_le_two_of_ne_zero hx
    have hmem : x ∈ Metric.closedBall (0 : Euclidean 2) 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
    have hone : mssLatticeAnalysisRaw x = 1 := by
      change (mssLatticeAnalysisBump x : Complex) = 1
      rw [mssLatticeAnalysisBump.one_of_mem_closedBall hmem]
      norm_num
    rw [hone, mul_one]

/-- The member of the finite square lattice family whose coordinate label is
`(a,b)`.  The finite grid is shifted by `N` so that it covers `[-N,N]^2`. -/
private def mssFiniteLatticeSynthesisTerm (x : Euclidean 2) (N a b : Nat) : Real :=
  mssUnitLatticeTransitionPiece (x 0 + (N : Real) - (a : Real)) *
    mssUnitLatticeTransitionPiece (x 1 + (N : Real) - (b : Real))

private theorem mssFiniteLatticeSynthesisTerm_nonneg (x : Euclidean 2) (N a b : Nat) :
    0 ≤ mssFiniteLatticeSynthesisTerm x N a b := by
  unfold mssFiniteLatticeSynthesisTerm
  exact mul_nonneg (mssUnitLatticeTransitionPiece_nonneg _)
    (mssUnitLatticeTransitionPiece_nonneg _)

private theorem mssFiniteLatticeSynthesisTerm_le_one (x : Euclidean 2) (N a b : Nat) :
    mssFiniteLatticeSynthesisTerm x N a b ≤ 1 := by
  unfold mssFiniteLatticeSynthesisTerm
  have hright_nonneg : 0 ≤ mssUnitLatticeTransitionPiece (x 1 + (N : Real) - (b : Real)) :=
    mssUnitLatticeTransitionPiece_nonneg _
  have hleft : mssUnitLatticeTransitionPiece (x 0 + (N : Real) - (a : Real)) ≤ 1 :=
    mssUnitLatticeTransitionPiece_le_one _
  have hright : mssUnitLatticeTransitionPiece (x 1 + (N : Real) - (b : Real)) ≤ 1 :=
    mssUnitLatticeTransitionPiece_le_one _
  calc
    mssUnitLatticeTransitionPiece (x 0 + (N : Real) - (a : Real)) *
        mssUnitLatticeTransitionPiece (x 1 + (N : Real) - (b : Real)) ≤
        1 * mssUnitLatticeTransitionPiece (x 1 + (N : Real) - (b : Real)) :=
      mul_le_mul_of_nonneg_right hleft hright_nonneg
    _ = mssUnitLatticeTransitionPiece (x 1 + (N : Real) - (b : Real)) := one_mul _
    _ ≤ 1 := hright

private theorem mssFiniteLatticeSynthesisTerm_sq_le
    (x : Euclidean 2) (N a b : Nat) :
    mssFiniteLatticeSynthesisTerm x N a b ^ 2 ≤
      mssFiniteLatticeSynthesisTerm x N a b := by
  rw [pow_two]
  calc
    mssFiniteLatticeSynthesisTerm x N a b * mssFiniteLatticeSynthesisTerm x N a b ≤
        mssFiniteLatticeSynthesisTerm x N a b * 1 :=
      mul_le_mul_of_nonneg_left (mssFiniteLatticeSynthesisTerm_le_one x N a b)
        (mssFiniteLatticeSynthesisTerm_nonneg x N a b)
    _ = mssFiniteLatticeSynthesisTerm x N a b := mul_one _

/-- On every coordinate square, a finite family of translates of the fixed
smooth lattice synthesis profile sums exactly to one. -/
private theorem mss_finite_latticeSynthesis_partition
    {x : Euclidean 2} (N : Nat) (hx0 : |x 0| ≤ (N : Real))
    (hx1 : |x 1| ≤ (N : Real)) :
    (∑ a ∈ Finset.range (2 * N + 1), ∑ b ∈ Finset.range (2 * N + 1),
      mssFiniteLatticeSynthesisTerm x N a b) = 1 := by
  unfold mssFiniteLatticeSynthesisTerm
  rw [← Finset.sum_mul_sum]
  rw [mss_finite_unitLatticeTransition_partition N hx0,
    mss_finite_unitLatticeTransition_partition N hx1]
  norm_num

/-- The same finite family has square overlap at most one. -/
private theorem mss_finite_latticeSynthesis_square_overlap
    {x : Euclidean 2} (N : Nat) (hx0 : |x 0| ≤ (N : Real))
    (hx1 : |x 1| ≤ (N : Real)) :
    (∑ a ∈ Finset.range (2 * N + 1), ∑ b ∈ Finset.range (2 * N + 1),
      mssFiniteLatticeSynthesisTerm x N a b ^ 2) ≤ 1 := by
  calc
    (∑ a ∈ Finset.range (2 * N + 1), ∑ b ∈ Finset.range (2 * N + 1),
      mssFiniteLatticeSynthesisTerm x N a b ^ 2) ≤
        ∑ a ∈ Finset.range (2 * N + 1), ∑ b ∈ Finset.range (2 * N + 1),
          mssFiniteLatticeSynthesisTerm x N a b := by
      refine Finset.sum_le_sum fun a ha => ?_
      refine Finset.sum_le_sum fun b hb => ?_
      exact mssFiniteLatticeSynthesisTerm_sq_le x N a b
    _ = 1 := mss_finite_latticeSynthesis_partition N hx0 hx1

/-- A finite square subfamily of the global lattice has square overlap at most
one everywhere; unlike reconstruction, this needs no coordinate-covering
hypothesis. -/
private theorem mss_finite_latticeSynthesis_square_overlap_global
    (x : Euclidean 2) (N : Nat) :
    (∑ a ∈ Finset.range (2 * N + 1), ∑ b ∈ Finset.range (2 * N + 1),
      mssFiniteLatticeSynthesisTerm x N a b ^ 2) ≤ 1 := by
  calc
    (∑ a ∈ Finset.range (2 * N + 1), ∑ b ∈ Finset.range (2 * N + 1),
      mssFiniteLatticeSynthesisTerm x N a b ^ 2) ≤
        ∑ a ∈ Finset.range (2 * N + 1), ∑ b ∈ Finset.range (2 * N + 1),
          mssFiniteLatticeSynthesisTerm x N a b := by
      refine Finset.sum_le_sum fun a ha => ?_
      refine Finset.sum_le_sum fun b hb => ?_
      exact mssFiniteLatticeSynthesisTerm_sq_le x N a b
    _ = (∑ a ∈ Finset.range (2 * N + 1),
          mssUnitLatticeTransitionPiece (x 0 + (N : Real) - (a : Real))) *
        (∑ b ∈ Finset.range (2 * N + 1),
          mssUnitLatticeTransitionPiece (x 1 + (N : Real) - (b : Real))) := by
      unfold mssFiniteLatticeSynthesisTerm
      rw [← Finset.sum_mul_sum]
    _ ≤ 1 := by
      have hleft := mss_sum_range_unitLatticeTransitionPiece_nonneg_le_one
        (x 0 + (N : Real)) (2 * N + 1)
      have hright := mss_sum_range_unitLatticeTransitionPiece_nonneg_le_one
        (x 1 + (N : Real)) (2 * N + 1)
      exact mul_le_one₀ hleft.2 hright.1 hright.2

/-- Product-indexed form of the finite lattice partition.  This is the
indexing shape used by a finite subfamily of the planar integer lattice. -/
private theorem mss_finite_latticeSynthesisReal_partition_product
    {x : Euclidean 2} (N : Nat)
    (hx : ∀ i : Fin 2, |x i| ≤ (N : Real)) :
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      mssLatticeSynthesisReal
        (WithLp.toLp 2 (fun i =>
          if i = (0 : Fin 2) then
            x 0 + (N : Real) - (ab.1 : Real)
          else
            x 1 + (N : Real) - (ab.2 : Real)))) = 1 := by
  let F : Nat → Nat → Real := fun a b =>
    mssLatticeSynthesisReal
      (WithLp.toLp 2 (fun i =>
        if i = (0 : Fin 2) then
          x 0 + (N : Real) - (a : Real)
        else
          x 1 + (N : Real) - (b : Real)))
  change (∑ ab ∈ (Finset.range (2 * N + 1)).product
      (Finset.range (2 * N + 1)), F ab.1 ab.2) = 1
  change (∑ ab ∈ (Finset.range (2 * N + 1)) ×ˢ
      (Finset.range (2 * N + 1)), F ab.1 ab.2) = 1
  rw [Finset.sum_product']
  simpa [F, mssLatticeSynthesisReal, mssFiniteLatticeSynthesisTerm,
    PiLp.toLp_apply] using
    mss_finite_latticeSynthesis_partition N (hx 0) (hx 1)

/-- The finite product family is an actual collection of standard lattice
translates of the synthesis profile. -/
private theorem mss_finite_standardLatticeSynthesis_partition
    {x : Euclidean 2} (N : Nat)
    (hx : ∀ i : Fin 2, |x i| ≤ (N : Real)) :
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      mssLatticeSynthesisReal
        (x - standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int)))) = 1 := by
  have hshift (a b : Nat) :
      x - standardLatticePoint (fun i =>
        if i = (0 : Fin 2) then (a : Int) - (N : Int)
        else (b : Int) - (N : Int)) =
      WithLp.toLp 2 (fun i =>
        if i = (0 : Fin 2) then x 0 + (N : Real) - (a : Real)
        else x 1 + (N : Real) - (b : Real)) := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;>
      simp [standardLatticePoint] <;>
      ring
  calc
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      mssLatticeSynthesisReal
        (x - standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int)))) =
        ∑ ab ∈ (Finset.range (2 * N + 1)).product
          (Finset.range (2 * N + 1)),
          mssLatticeSynthesisReal
            (WithLp.toLp 2 (fun i =>
              if i = (0 : Fin 2) then x 0 + (N : Real) - (ab.1 : Real)
              else x 1 + (N : Real) - (ab.2 : Real))) := by
          apply Finset.sum_congr rfl
          intro ab hab
          rw [hshift ab.1 ab.2]
    _ = 1 := mss_finite_latticeSynthesisReal_partition_product N hx

/-- Product-indexed square-overlap form of the finite lattice synthesis
partition. -/
private theorem mss_finite_latticeSynthesisReal_square_overlap_product
    {x : Euclidean 2} (N : Nat)
    (hx : ∀ i : Fin 2, |x i| ≤ (N : Real)) :
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      mssLatticeSynthesisReal
        (WithLp.toLp 2 (fun i =>
          if i = (0 : Fin 2) then
            x 0 + (N : Real) - (ab.1 : Real)
          else
            x 1 + (N : Real) - (ab.2 : Real))) ^ 2) ≤ 1 := by
  let F : Nat → Nat → Real := fun a b =>
    mssLatticeSynthesisReal
      (WithLp.toLp 2 (fun i =>
        if i = (0 : Fin 2) then
          x 0 + (N : Real) - (a : Real)
        else
          x 1 + (N : Real) - (b : Real)))
  let G : Nat → Nat → Real := fun a b => F a b ^ 2
  change (∑ ab ∈ (Finset.range (2 * N + 1)).product
      (Finset.range (2 * N + 1)), G ab.1 ab.2) ≤ 1
  change (∑ ab ∈ (Finset.range (2 * N + 1)) ×ˢ
      (Finset.range (2 * N + 1)), G ab.1 ab.2) ≤ 1
  rw [Finset.sum_product']
  simpa [G, F, mssLatticeSynthesisReal, mssFiniteLatticeSynthesisTerm,
    PiLp.toLp_apply] using
    mss_finite_latticeSynthesis_square_overlap N (hx 0) (hx 1)

/-- Square-overlap form for the literal standard-lattice centers. -/
private theorem mss_finite_standardLatticeSynthesis_square_overlap
    {x : Euclidean 2} (N : Nat)
    (hx : ∀ i : Fin 2, |x i| ≤ (N : Real)) :
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      mssLatticeSynthesisReal
        (x - standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int))) ^ 2) ≤ 1 := by
  have hshift (a b : Nat) :
      x - standardLatticePoint (fun i =>
        if i = (0 : Fin 2) then (a : Int) - (N : Int)
        else (b : Int) - (N : Int)) =
      WithLp.toLp 2 (fun i =>
        if i = (0 : Fin 2) then x 0 + (N : Real) - (a : Real)
        else x 1 + (N : Real) - (b : Real)) := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;>
      simp [standardLatticePoint] <;>
      ring
  calc
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      mssLatticeSynthesisReal
        (x - standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int))) ^ 2) =
        ∑ ab ∈ (Finset.range (2 * N + 1)).product
          (Finset.range (2 * N + 1)),
          mssLatticeSynthesisReal
            (WithLp.toLp 2 (fun i =>
              if i = (0 : Fin 2) then x 0 + (N : Real) - (ab.1 : Real)
              else x 1 + (N : Real) - (ab.2 : Real))) ^ 2 := by
          apply Finset.sum_congr rfl
          intro ab hab
          rw [hshift ab.1 ab.2]
    _ ≤ 1 := mss_finite_latticeSynthesisReal_square_overlap_product N hx

/-- The same finite standard-lattice family has square overlap at most one
globally, whether or not it reconstructs at the point under consideration. -/
private theorem mss_finite_standardLatticeSynthesis_square_overlap_global
    (x : Euclidean 2) (N : Nat) :
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      mssLatticeSynthesisReal
        (x - standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int))) ^ 2) ≤ 1 := by
  have hshift (a b : Nat) :
      x - standardLatticePoint (fun i =>
        if i = (0 : Fin 2) then (a : Int) - (N : Int)
        else (b : Int) - (N : Int)) =
      WithLp.toLp 2 (fun i =>
        if i = (0 : Fin 2) then x 0 + (N : Real) - (a : Real)
        else x 1 + (N : Real) - (b : Real)) := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;>
      simp [standardLatticePoint] <;>
      ring
  calc
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      mssLatticeSynthesisReal
        (x - standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int))) ^ 2) =
        ∑ ab ∈ (Finset.range (2 * N + 1)).product
          (Finset.range (2 * N + 1)),
          mssFiniteLatticeSynthesisTerm x N ab.1 ab.2 ^ 2 := by
      apply Finset.sum_congr rfl
      intro ab hab
      rw [hshift ab.1 ab.2]
      simp [mssLatticeSynthesisReal, mssFiniteLatticeSynthesisTerm]
    _ = ∑ a ∈ Finset.range (2 * N + 1), ∑ b ∈ Finset.range (2 * N + 1),
          mssFiniteLatticeSynthesisTerm x N a b ^ 2 :=
      Finset.sum_product' _ _ (fun a b =>
        mssFiniteLatticeSynthesisTerm x N a b ^ 2)
    _ ≤ 1 := mss_finite_latticeSynthesis_square_overlap_global x N

/-- Evaluation of the dilated synthesis cutoff at an actual lattice center. -/
private theorem mss_translatedDilatedLatticeSynthesis_apply
    (R : Real) (hR : R ≠ 0) (k : Fin 2 → Int) (xi : Euclidean 2) :
    translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
      (R • standardLatticePoint k) R hR xi =
        (mssLatticeSynthesisReal (R⁻¹ • xi - standardLatticePoint k) : Complex) := by
  rw [translatedDilatedSchwartzCutoff_apply, mssLatticeSynthesisPrototype_apply]
  unfold mssLatticeSynthesisRaw
  congr 1
  rw [smul_sub]
  simp [smul_smul, hR]

/-- After normalization by a nonzero cube radius, the finite standard
lattice family remains an exact complex-valued synthesis partition. -/
private theorem mss_finite_translatedDilatedLatticeSynthesis_partition
    {xi : Euclidean 2} (R : Real) (hR : R ≠ 0) (N : Nat)
    (hxi : ∀ i : Fin 2, |(R⁻¹ • xi) i| ≤ (N : Real)) :
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
        (R • standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int))) R hR xi) = 1 := by
  calc
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
        (R • standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int))) R hR xi) =
        ∑ ab ∈ (Finset.range (2 * N + 1)).product
          (Finset.range (2 * N + 1)),
          (mssLatticeSynthesisReal
            (R⁻¹ • xi - standardLatticePoint (fun i =>
              if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
              else (ab.2 : Int) - (N : Int))) : Complex) := by
          apply Finset.sum_congr rfl
          intro ab hab
          rw [mss_translatedDilatedLatticeSynthesis_apply]
    _ = 1 := by
      exact_mod_cast
        mss_finite_standardLatticeSynthesis_partition (x := R⁻¹ • xi) N hxi

/-- The scaled finite lattice synthesis family has unit square overlap. -/
private theorem mss_finite_translatedDilatedLatticeSynthesis_square_overlap
    {xi : Euclidean 2} (R : Real) (hR : R ≠ 0) (N : Nat)
    (hxi : ∀ i : Fin 2, |(R⁻¹ • xi) i| ≤ (N : Real)) :
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      ‖translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
        (R • standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int))) R hR xi‖ ^ 2) ≤ 1 := by
  calc
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      ‖translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
        (R • standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int))) R hR xi‖ ^ 2) =
        ∑ ab ∈ (Finset.range (2 * N + 1)).product
          (Finset.range (2 * N + 1)),
          mssLatticeSynthesisReal
            (R⁻¹ • xi - standardLatticePoint (fun i =>
              if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
              else (ab.2 : Int) - (N : Int))) ^ 2 := by
          apply Finset.sum_congr rfl
          intro ab hab
          rw [mss_translatedDilatedLatticeSynthesis_apply]
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mssLatticeSynthesisReal_nonneg _)]
    _ ≤ 1 := mss_finite_standardLatticeSynthesis_square_overlap
      (x := R⁻¹ • xi) N hxi

/-- Translation and dilation preserve the global finite square-overlap bound
of the canonical lattice subfamily. -/
private theorem mss_finite_translatedDilatedLatticeSynthesis_square_overlap_global
    {xi : Euclidean 2} (R : Real) (hR : R ≠ 0) (N : Nat) :
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      ‖translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
        (R • standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int))) R hR xi‖ ^ 2) ≤ 1 := by
  calc
    (∑ ab ∈ (Finset.range (2 * N + 1)).product
        (Finset.range (2 * N + 1)),
      ‖translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
        (R • standardLatticePoint (fun i =>
          if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
          else (ab.2 : Int) - (N : Int))) R hR xi‖ ^ 2) =
        ∑ ab ∈ (Finset.range (2 * N + 1)).product
          (Finset.range (2 * N + 1)),
          mssLatticeSynthesisReal
            (R⁻¹ • xi - standardLatticePoint (fun i =>
              if i = (0 : Fin 2) then (ab.1 : Int) - (N : Int)
              else (ab.2 : Int) - (N : Int))) ^ 2 := by
          apply Finset.sum_congr rfl
          intro ab hab
          rw [mss_translatedDilatedLatticeSynthesis_apply]
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mssLatticeSynthesisReal_nonneg _)]
    _ ≤ 1 := mss_finite_standardLatticeSynthesis_square_overlap_global
      (R⁻¹ • xi) N

/-- Translation and dilation preserve the exact synthesis/analysis absorption
identity of the two fixed lattice prototypes. -/
private theorem mss_translatedDilatedLattice_absorption
    (center xi : Euclidean 2) (R : Real) (hR : R ≠ 0) :
    translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype center R hR xi *
      translatedDilatedSchwartzCutoff mssLatticeAnalysisPrototype center R hR xi =
        translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype center R hR xi := by
  rw [translatedDilatedSchwartzCutoff_apply,
    mssLatticeSynthesisPrototype_apply,
    translatedDilatedSchwartzCutoff_apply,
    mssLatticeAnalysisPrototype_apply]
  exact mssLatticeSynthesisRaw_mul_analysisRaw _

/-- Every real coordinate lies within one of its integer floor. -/
private theorem mss_abs_sub_intFloor_le_one (t : Real) :
    |t - ((⌊t⌋ : Int) : Real)| ≤ 1 := by
  rw [abs_le]
  constructor
  · have hfloor : ((⌊t⌋ : Int) : Real) ≤ t := Int.floor_le t
    linarith
  · have hfloor : t < ((⌊t⌋ : Int) : Real) + 1 := Int.lt_floor_add_one t
    linarith

/-- The absolute value of the integer floor is at most one more than that of
the original real coordinate. -/
private theorem mss_abs_intFloor_le_abs_add_one (t : Real) :
    |((⌊t⌋ : Int) : Real)| ≤ |t| + 1 := by
  rw [abs_le] at ⊢
  have habs : -|t| ≤ t ∧ t ≤ |t| := abs_le.mp (le_refl |t|)
  have hfloor_le : ((⌊t⌋ : Int) : Real) ≤ t := Int.floor_le t
  have hfloor_lt : t < ((⌊t⌋ : Int) : Real) + 1 := Int.lt_floor_add_one t
  constructor <;> linarith

/-- The coordinatewise lattice base point nearest below a packet ray. -/
private def mssPacketLatticeBase (D : MSSWavefrontKernelData)
    (scale : Real) (n nu : Int) : Fin 2 → Int :=
  fun i => ⌊(n : Real) * D.directions scale nu i⌋

/-- The fixed coordinate radius needed to cover the normalized support of
one packet around the integer base point of its ray. -/
private noncomputable def mssLocalLatticeRadius (D : MSSWavefrontKernelData) : Nat :=
  ⌈2 * D.angularConstant + 15 / 4⌉₊

/-- The scale-dependent coordinate radius containing every relevant packet
base point before the fixed local offset grid is added. -/
private noncomputable def mssGlobalLatticeBaseRadius (scale : Real) : Nat :=
  ⌈2 * Real.sqrt scale + 4⌉₊

/-- The finite global lattice radius for the canonical cube family. -/
private noncomputable def mssGlobalLatticeRadius
    (D : MSSWavefrontKernelData) (scale : Real) : Nat :=
  mssGlobalLatticeBaseRadius scale + mssLocalLatticeRadius D

private theorem mss_abs_coe_relevantRadialIndex_le
    {scale : Real} (_hscale : 2 ≤ scale) {n : Int}
    (hn : n ∈ relevantRadialIndexEnumeration scale) :
    |(n : Real)| ≤ 2 * Real.sqrt scale + 3 := by
  have hrel : n ∈ relevantRadialIndices scale :=
    (mem_relevantRadialIndexEnumeration_iff scale n).mp hn
  rcases hrel with ⟨s, hs, hdist⟩
  have hsnonneg : 0 ≤ s := by
    have hsqrt : 0 ≤ Real.sqrt scale := Real.sqrt_nonneg _
    linarith [hs.1]
  have habss : |s| ≤ 2 * Real.sqrt scale := by
    rw [abs_of_nonneg hsnonneg]
    exact hs.2
  calc
    |(n : Real)| = |(n : Real) - s + s| := by ring_nf
    _ ≤ |(n : Real) - s| + |s| := abs_add_le _ _
    _ ≤ 3 + (2 * Real.sqrt scale) := add_le_add hdist.le habss
    _ = 2 * Real.sqrt scale + 3 := by ring

private theorem mss_packetLatticeBase_real_abs_le
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    {n nu : Int} (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale) (i : Fin 2) :
    |((mssPacketLatticeBase D scale n nu i : Int) : Real)| ≤
      2 * Real.sqrt scale + 4 := by
  have hnabs := mss_abs_coe_relevantRadialIndex_le hscale hn
  have hdir : |D.directions scale nu i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, D.direction_unit scale nu hnu] using
      (PiLp.norm_apply_le (D.directions scale nu) i)
  have hproduct : |(n : Real) * D.directions scale nu i| ≤
      2 * Real.sqrt scale + 3 := by
    rw [abs_mul]
    calc
      |(n : Real)| * |D.directions scale nu i| ≤ |(n : Real)| * 1 :=
        mul_le_mul_of_nonneg_left hdir (abs_nonneg _)
      _ = |(n : Real)| := mul_one _
      _ ≤ 2 * Real.sqrt scale + 3 := hnabs
  calc
    |((mssPacketLatticeBase D scale n nu i : Int) : Real)| ≤
        |(n : Real) * D.directions scale nu i| + 1 := by
      simpa [mssPacketLatticeBase] using
        mss_abs_intFloor_le_abs_add_one ((n : Real) * D.directions scale nu i)
    _ ≤ (2 * Real.sqrt scale + 3) + 1 := add_le_add hproduct le_rfl
    _ = 2 * Real.sqrt scale + 4 := by ring

private theorem mss_packetLatticeBase_natAbs_le_globalBaseRadius
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    {n nu : Int} (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale) (i : Fin 2) :
    (mssPacketLatticeBase D scale n nu i).natAbs ≤
      mssGlobalLatticeBaseRadius scale := by
  have hbase := mss_packetLatticeBase_real_abs_le D hscale hn hnu i
  have hceil : 2 * Real.sqrt scale + 4 ≤
      (mssGlobalLatticeBaseRadius scale : Real) := by
    simpa [mssGlobalLatticeBaseRadius] using
      (Nat.le_ceil (2 * Real.sqrt scale + 4))
  have hbound : |((mssPacketLatticeBase D scale n nu i : Int) : Real)| ≤
      (mssGlobalLatticeBaseRadius scale : Real) := hbase.trans hceil
  have hbound_int : |mssPacketLatticeBase D scale n nu i| ≤
      (mssGlobalLatticeBaseRadius scale : Int) := by
    exact_mod_cast hbound
  have hnat_int : ((mssPacketLatticeBase D scale n nu i).natAbs : Int) ≤
      (mssGlobalLatticeBaseRadius scale : Int) := by
    simpa only [Int.abs_eq_natAbs] using hbound_int
  exact_mod_cast hnat_int

private theorem mss_packetLatticeBase_abs_le_globalBaseRadius
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    {n nu : Int} (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale) (i : Fin 2) :
    |mssPacketLatticeBase D scale n nu i| ≤
      (mssGlobalLatticeBaseRadius scale : Int) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast mss_packetLatticeBase_natAbs_le_globalBaseRadius D hscale hn hnu i

/-- Side length of the finite square lattice grid of coordinate radius `M`. -/
private def mssLatticeGridSide (M : Nat) : Nat := 2 * M + 1

/-- Number of cells in the finite square lattice grid. -/
private def mssLatticeGridCount (M : Nat) : Nat :=
  mssLatticeGridSide M * mssLatticeGridSide M

private def mssLatticeGridPair (M : Nat)
    (k : Fin (mssLatticeGridCount M)) :
    Fin (mssLatticeGridSide M) × Fin (mssLatticeGridSide M) :=
  (finProdFinEquiv :
    Fin (mssLatticeGridSide M) × Fin (mssLatticeGridSide M) ≃
      Fin (mssLatticeGridCount M)).symm k

/-- Integer vector label of a finite square-lattice grid cell. -/
private def mssLatticeGridLabel (M : Nat)
    (k : Fin (mssLatticeGridCount M)) : Fin 2 → Int :=
  let ab := mssLatticeGridPair M k
  fun i => if i = (0 : Fin 2) then (ab.1.val : Int) - (M : Int)
    else (ab.2.val : Int) - (M : Int)

/-- Reindexing the canonical `Fin` grid by its two coordinate ranges. -/
private theorem mss_sum_latticeGridLabel_eq_product
    {α : Type*} [AddCommMonoid α] (M : Nat) (F : (Fin 2 → Int) → α) :
    (∑ k : Fin (mssLatticeGridCount M), F (mssLatticeGridLabel M k)) =
      ∑ ab ∈ (Finset.range (mssLatticeGridSide M)).product
        (Finset.range (mssLatticeGridSide M)),
        F (fun i => if i = (0 : Fin 2) then
          (ab.1 : Int) - (M : Int) else (ab.2 : Int) - (M : Int)) := by
  classical
  calc
    (∑ k : Fin (mssLatticeGridCount M), F (mssLatticeGridLabel M k)) =
        ∑ ab : Fin (mssLatticeGridSide M) × Fin (mssLatticeGridSide M),
          F (fun i => if i = (0 : Fin 2) then
            (ab.1.val : Int) - (M : Int) else (ab.2.val : Int) - (M : Int)) := by
      change
        (∑ k : Fin (mssLatticeGridSide M * mssLatticeGridSide M),
          F (fun i => if i = (0 : Fin 2) then
            (((finProdFinEquiv :
              Fin (mssLatticeGridSide M) × Fin (mssLatticeGridSide M) ≃
                Fin (mssLatticeGridSide M * mssLatticeGridSide M)).symm k).1.val : Int) -
                (M : Int)
            else
              (((finProdFinEquiv :
                Fin (mssLatticeGridSide M) × Fin (mssLatticeGridSide M) ≃
                  Fin (mssLatticeGridSide M * mssLatticeGridSide M)).symm k).2.val : Int) -
                (M : Int))) = _
      exact Equiv.sum_comp (finProdFinEquiv.symm :
        Fin (mssLatticeGridSide M * mssLatticeGridSide M) ≃
          Fin (mssLatticeGridSide M) × Fin (mssLatticeGridSide M))
        (fun ab => F (fun i => if i = (0 : Fin 2) then
          (ab.1.val : Int) - (M : Int) else (ab.2.val : Int) - (M : Int)))
    _ = ∑ a : Fin (mssLatticeGridSide M),
        ∑ b : Fin (mssLatticeGridSide M),
          F (fun i => if i = (0 : Fin 2) then
            (a.val : Int) - (M : Int) else (b.val : Int) - (M : Int)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a ∈ Finset.range (mssLatticeGridSide M),
        ∑ b ∈ Finset.range (mssLatticeGridSide M),
          F (fun i => if i = (0 : Fin 2) then
            (a : Int) - (M : Int) else (b : Int) - (M : Int)) := by
      let G : Nat → Nat → α := fun a b =>
        F (fun i => if i = (0 : Fin 2) then
          (a : Int) - (M : Int) else (b : Int) - (M : Int))
      change (∑ a : Fin (mssLatticeGridSide M),
          ∑ b : Fin (mssLatticeGridSide M), G a b) =
        ∑ a ∈ Finset.range (mssLatticeGridSide M),
          ∑ b ∈ Finset.range (mssLatticeGridSide M), G a b
      rw [Fin.sum_univ_eq_sum_range (fun a =>
        ∑ b : Fin (mssLatticeGridSide M), G a b)]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Fin.sum_univ_eq_sum_range (fun b => G a b)]
    _ = ∑ ab ∈ (Finset.range (mssLatticeGridSide M)).product
        (Finset.range (mssLatticeGridSide M)),
        F (fun i => if i = (0 : Fin 2) then
          (ab.1 : Int) - (M : Int) else (ab.2 : Int) - (M : Int)) := by
      exact (Finset.sum_product'
        (Finset.range (mssLatticeGridSide M))
        (Finset.range (mssLatticeGridSide M)) (fun (a b : Nat) =>
        F (fun i => if i = (0 : Fin 2) then
          (a : Int) - (M : Int) else (b : Int) - (M : Int)))).symm

private theorem mssLatticeGridLabel_injective (M : Nat) :
    Function.Injective (mssLatticeGridLabel M) := by
  intro k l h
  have h0 := congr_fun h (0 : Fin 2)
  have h1 := congr_fun h (1 : Fin 2)
  have hp0 : (mssLatticeGridPair M k).1 = (mssLatticeGridPair M l).1 := by
    apply Fin.ext
    change ((mssLatticeGridPair M k).1.val : Int) - (M : Int) =
      ((mssLatticeGridPair M l).1.val : Int) - (M : Int) at h0
    omega
  have hp1 : (mssLatticeGridPair M k).2 = (mssLatticeGridPair M l).2 := by
    apply Fin.ext
    change ((mssLatticeGridPair M k).2.val : Int) - (M : Int) =
      ((mssLatticeGridPair M l).2.val : Int) - (M : Int) at h1
    omega
  apply (finProdFinEquiv :
    Fin (mssLatticeGridSide M) × Fin (mssLatticeGridSide M) ≃
      Fin (mssLatticeGridCount M)).symm.injective
  exact Prod.ext hp0 hp1

private theorem mssLatticeGridLabel_abs_le (M : Nat)
    (k : Fin (mssLatticeGridCount M)) (i : Fin 2) :
    |mssLatticeGridLabel M k i| ≤ (M : Int) := by
  rw [abs_le]
  fin_cases i
  · change -(M : Int) ≤ ((mssLatticeGridPair M k).1.val : Int) - (M : Int) ∧
      ((mssLatticeGridPair M k).1.val : Int) - (M : Int) ≤ (M : Int)
    have hk := (mssLatticeGridPair M k).1.isLt
    dsimp [mssLatticeGridSide] at hk
    constructor <;> omega
  · change -(M : Int) ≤ ((mssLatticeGridPair M k).2.val : Int) - (M : Int) ∧
      ((mssLatticeGridPair M k).2.val : Int) - (M : Int) ≤ (M : Int)
    have hk := (mssLatticeGridPair M k).2.isLt
    dsimp [mssLatticeGridSide] at hk
    constructor <;> omega

private theorem mss_add_latticeGridLabel_abs_le
    (B L : Nat) (b : Fin 2 → Int)
    (hb : ∀ i, |b i| ≤ (B : Int))
    (k : Fin (mssLatticeGridCount L)) (i : Fin 2) :
    |b i + mssLatticeGridLabel L k i| ≤ ((B + L : Nat) : Int) := by
  have hbi := hb i
  rw [abs_le] at hbi ⊢
  have hk := mssLatticeGridLabel_abs_le L k i
  rw [abs_le] at hk
  push_cast
  omega

/-- A coordinate in the integer interval `[-M,M]`, encoded in the finite
coordinate grid `Fin (2*M+1)`. -/
private def mssBoundedLatticeCoordinate (M : Nat) (z : Int)
    (hz : |z| ≤ (M : Int)) : Fin (mssLatticeGridSide M) :=
  ⟨(z + (M : Int)).toNat, by
    have hz0 : 0 ≤ z + (M : Int) := by
      rw [abs_le] at hz
      omega
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg hz0]
    rw [abs_le] at hz
    dsimp [mssLatticeGridSide]
    omega⟩

private theorem mssBoundedLatticeCoordinate_label
    (M : Nat) (z : Int) (hz : |z| ≤ (M : Int)) :
    ((mssBoundedLatticeCoordinate M z hz).val : Int) - (M : Int) = z := by
  have hz0 : 0 ≤ z + (M : Int) := by
    rw [abs_le] at hz
    omega
  change (((z + (M : Int)).toNat : Nat) : Int) - (M : Int) = z
  rw [Int.toNat_of_nonneg hz0]
  ring

/-- The inverse coordinate map from an integer label in `[-M,M]^2` to the
finite square lattice grid. -/
private def mssLatticeGridIndex (M : Nat) (z : Fin 2 → Int)
    (hz : ∀ i, |z i| ≤ (M : Int)) : Fin (mssLatticeGridCount M) :=
  (finProdFinEquiv :
    Fin (mssLatticeGridSide M) × Fin (mssLatticeGridSide M) ≃
      Fin (mssLatticeGridCount M))
    ⟨mssBoundedLatticeCoordinate M (z 0) (hz 0),
      mssBoundedLatticeCoordinate M (z 1) (hz 1)⟩

private theorem mssLatticeGridLabel_index
    (M : Nat) (z : Fin 2 → Int) (hz : ∀ i, |z i| ≤ (M : Int)) :
    mssLatticeGridLabel M (mssLatticeGridIndex M z hz) = z := by
  funext i
  fin_cases i
  · simp [mssLatticeGridLabel, mssLatticeGridPair,
      mssLatticeGridIndex,
      mssBoundedLatticeCoordinate_label]
  · simp [mssLatticeGridLabel, mssLatticeGridPair,
      mssLatticeGridIndex,
      mssBoundedLatticeCoordinate_label]

/-- The global-grid index of one local lattice offset around a packet's
integer ray base point. -/
private noncomputable def mssPacketLocalGridIndex
    (D : MSSWavefrontKernelData) (scale : Real) (hscale : 2 ≤ scale) (n nu : Int)
    (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale)
    (k : Fin (mssLatticeGridCount (mssLocalLatticeRadius D))) :
    Fin (mssLatticeGridCount (mssGlobalLatticeRadius D scale)) :=
  mssLatticeGridIndex (mssGlobalLatticeRadius D scale)
    (fun i => mssPacketLatticeBase D scale n nu i +
      mssLatticeGridLabel (mssLocalLatticeRadius D) k i)
    (by
      intro i
      simpa [mssGlobalLatticeRadius] using
        mss_add_latticeGridLabel_abs_le
          (mssGlobalLatticeBaseRadius scale) (mssLocalLatticeRadius D)
          (mssPacketLatticeBase D scale n nu)
          (fun j => mss_packetLatticeBase_abs_le_globalBaseRadius
            D hscale hn hnu j)
          k i)

private theorem mssLatticeGridLabel_packetLocalGridIndex
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale)
    (k : Fin (mssLatticeGridCount (mssLocalLatticeRadius D))) :
    mssLatticeGridLabel (mssGlobalLatticeRadius D scale)
      (mssPacketLocalGridIndex D scale hscale n nu hn hnu k) =
        fun i => mssPacketLatticeBase D scale n nu i +
          mssLatticeGridLabel (mssLocalLatticeRadius D) k i := by
  unfold mssPacketLocalGridIndex
  apply mssLatticeGridLabel_index

/-- The local offset grid embeds injectively into the finite global lattice. -/
private noncomputable def mssPacketLocalGridEmbedding
    (D : MSSWavefrontKernelData) (scale : Real) (hscale : 2 ≤ scale) (n nu : Int)
    (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale) :
    Fin (mssLatticeGridCount (mssLocalLatticeRadius D)) ↪
      Fin (mssLatticeGridCount (mssGlobalLatticeRadius D scale)) where
  toFun := mssPacketLocalGridIndex D scale hscale n nu hn hnu
  inj' := by
    intro k l hkl
    have hlabels := congrArg
      (mssLatticeGridLabel (mssGlobalLatticeRadius D scale)) hkl
    rw [mssLatticeGridLabel_packetLocalGridIndex D hscale n nu hn hnu k,
      mssLatticeGridLabel_packetLocalGridIndex D hscale n nu hn hnu l] at hlabels
    apply mssLatticeGridLabel_injective (mssLocalLatticeRadius D)
    funext i
    have hi := congr_fun hlabels i
    omega

/-- A positive lattice radius defined at every real scale.  At the active MSS
scales it is exactly `sqrt scale`; the harmless `max` only makes the global
cube data total on inactive scales as required by the record. -/
private noncomputable def mssCanonicalLatticeRadius (scale : Real) : Real :=
  Real.sqrt (max scale 2)

private theorem mssCanonicalLatticeRadius_pos (scale : Real) :
    0 < mssCanonicalLatticeRadius scale := by
  unfold mssCanonicalLatticeRadius
  apply Real.sqrt_pos.2
  exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)

private theorem mssCanonicalLatticeRadius_eq_sqrt {scale : Real}
    (hscale : 2 ≤ scale) :
    mssCanonicalLatticeRadius scale = Real.sqrt scale := by
  simp [mssCanonicalLatticeRadius, max_eq_left hscale]

/-- The finite global cube type used by the canonical lattice construction. -/
private def mssCanonicalCubeCount (D : MSSWavefrontKernelData)
    (scale : Real) : Nat :=
  mssLatticeGridCount (mssGlobalLatticeRadius D scale)

/-- Centers of the canonical finite cube family. -/
private noncomputable def mssCanonicalCubeCenter (D : MSSWavefrontKernelData)
    (scale : Real) : Fin (mssCanonicalCubeCount D scale) → Euclidean 2 :=
  fun k => mssCanonicalLatticeRadius scale • standardLatticePoint
    (mssLatticeGridLabel (mssGlobalLatticeRadius D scale) k)

/-- The synthesis cutoff on one canonical cube. -/
private noncomputable def mssCanonicalCubeCutoff (D : MSSWavefrontKernelData)
    (scale : Real) :
    Fin (mssCanonicalCubeCount D scale) → SchwartzMap (Euclidean 2) Complex :=
  fun k => translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
    (mssCanonicalCubeCenter D scale k) (mssCanonicalLatticeRadius scale)
    (mssCanonicalLatticeRadius_pos scale).ne'

/-- The enlarged analysis cutoff on one canonical cube. -/
private noncomputable def mssCanonicalCubeAnalysisCutoff
    (D : MSSWavefrontKernelData) (scale : Real) :
    Fin (mssCanonicalCubeCount D scale) → SchwartzMap (Euclidean 2) Complex :=
  fun k => translatedDilatedSchwartzCutoff mssLatticeAnalysisPrototype
    (mssCanonicalCubeCenter D scale k) (mssCanonicalLatticeRadius scale)
    (mssCanonicalLatticeRadius_pos scale).ne'

/-- The local finite offset grid selected for an active packet.  It is empty
off the active index range so that the definition is total at all scales. -/
private noncomputable def mssCanonicalCubeSets (D : MSSWavefrontKernelData)
    (scale : Real) (n nu : Int) : Finset (Fin (mssCanonicalCubeCount D scale)) := by
  classical
  exact if hscale : 2 ≤ scale then
    if hn : n ∈ relevantRadialIndexEnumeration scale then
      if hnu : nu ∈ D.angularIndices scale then
        Finset.univ.map (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu)
      else ∅
    else ∅
  else ∅

private theorem mssCanonicalCubeCenter_eq_sqrt
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (k : Fin (mssCanonicalCubeCount D scale)) :
    mssCanonicalCubeCenter D scale k =
      Real.sqrt scale • standardLatticePoint
        (mssLatticeGridLabel (mssGlobalLatticeRadius D scale) k) := by
  unfold mssCanonicalCubeCenter
  rw [mssCanonicalLatticeRadius_eq_sqrt hscale]

private theorem mssCanonicalCubeSets_eq_active
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale) :
    mssCanonicalCubeSets D scale n nu =
      Finset.univ.map (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu) := by
  classical
  unfold mssCanonicalCubeSets
  simp only [dif_pos hscale, dif_pos hn, dif_pos hnu]
  rfl

private theorem mssCanonicalCubeCutoff_apply_eq_active
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (k : Fin (mssCanonicalCubeCount D scale)) (xi : Euclidean 2) :
    mssCanonicalCubeCutoff D scale k xi =
      translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
        (Real.sqrt scale • standardLatticePoint
          (mssLatticeGridLabel (mssGlobalLatticeRadius D scale) k))
        (Real.sqrt scale) (Real.sqrt_ne_zero'.mpr (by linarith)) xi := by
  unfold mssCanonicalCubeCutoff
  rw [mssCanonicalCubeCenter_eq_sqrt D hscale k]
  rw [translatedDilatedSchwartzCutoff_apply,
    translatedDilatedSchwartzCutoff_apply,
    mssCanonicalLatticeRadius_eq_sqrt hscale]

private theorem mssCanonicalCube_cutoff_mul_analysisCutoff
    (D : MSSWavefrontKernelData) (scale : Real)
    (k : Fin (mssCanonicalCubeCount D scale)) (xi : Euclidean 2) :
    mssCanonicalCubeCutoff D scale k xi *
      mssCanonicalCubeAnalysisCutoff D scale k xi =
        mssCanonicalCubeCutoff D scale k xi := by
  simpa only [mssCanonicalCubeCutoff, mssCanonicalCubeAnalysisCutoff] using
    mss_translatedDilatedLattice_absorption (mssCanonicalCubeCenter D scale k) xi
      (mssCanonicalLatticeRadius scale) (mssCanonicalLatticeRadius_pos scale).ne'

private theorem mssCanonicalCube_cube_support
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (k : Fin (mssCanonicalCubeCount D scale)) :
    isFourierCubeCutoff (mssCanonicalCubeCenter D scale k) (1 * Real.sqrt scale)
      (mssCanonicalCubeCutoff D scale k) := by
  have hsupp := isFourierCubeCutoff_translatedDilatedSchwartzCutoff
    mssLatticeSynthesisPrototype (mssCanonicalCubeCenter D scale k)
    (mssCanonicalLatticeRadius_pos scale)
    (by
      intro x hx
      apply mssLatticeSynthesisRaw_support_subset
      change mssLatticeSynthesisRaw x ≠ 0 at hx
      exact hx)
  simpa only [mssCanonicalCubeCutoff, one_mul,
    mssCanonicalLatticeRadius_eq_sqrt hscale] using hsupp

private theorem mssCanonicalCube_square_overlap
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (xi : Euclidean 2) :
    ∑ k : Fin (mssCanonicalCubeCount D scale),
      ‖mssCanonicalCubeCutoff D scale k xi‖ ^ 2 ≤ 1 := by
  classical
  have hroot : Real.sqrt scale ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  calc
    (∑ k : Fin (mssCanonicalCubeCount D scale),
      ‖mssCanonicalCubeCutoff D scale k xi‖ ^ 2) =
        ∑ k : Fin (mssLatticeGridCount (mssGlobalLatticeRadius D scale)),
          ‖translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
            (Real.sqrt scale • standardLatticePoint
              (mssLatticeGridLabel (mssGlobalLatticeRadius D scale) k))
            (Real.sqrt scale) hroot xi‖ ^ 2 := by
      change (∑ k : Fin (mssLatticeGridCount (mssGlobalLatticeRadius D scale)),
        ‖mssCanonicalCubeCutoff D scale k xi‖ ^ 2) = _
      apply Finset.sum_congr rfl
      intro k hk
      rw [mssCanonicalCubeCutoff_apply_eq_active D hscale k xi]
    _ = ∑ ab ∈ (Finset.range
          (mssLatticeGridSide (mssGlobalLatticeRadius D scale))).product
          (Finset.range (mssLatticeGridSide (mssGlobalLatticeRadius D scale))),
        ‖translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
          (Real.sqrt scale • standardLatticePoint (fun i =>
            if i = (0 : Fin 2) then
              (ab.1 : Int) - (mssGlobalLatticeRadius D scale : Int)
            else (ab.2 : Int) - (mssGlobalLatticeRadius D scale : Int)))
          (Real.sqrt scale) hroot xi‖ ^ 2 :=
      mss_sum_latticeGridLabel_eq_product (mssGlobalLatticeRadius D scale)
        (fun label => ‖translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
          (Real.sqrt scale • standardLatticePoint label)
          (Real.sqrt scale) hroot xi‖ ^ 2)
    _ ≤ 1 := by
      simpa only [mssLatticeGridSide] using
        mss_finite_translatedDilatedLatticeSynthesis_square_overlap_global
          (xi := xi) (Real.sqrt scale) hroot (mssGlobalLatticeRadius D scale)

private theorem mssCanonicalCube_cubes_per_packet
    (D : MSSWavefrontKernelData) :
    ∃ B : Nat, ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
        (mssCanonicalCubeSets D scale n nu).card ≤ B := by
  refine ⟨mssLatticeGridCount (mssLocalLatticeRadius D), ?_⟩
  intro scale hscale n hn nu hnu
  rw [mssCanonicalCubeSets_eq_active D hscale n nu hn hnu]
  change (Finset.map (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu)
    Finset.univ).card ≤ mssLatticeGridCount (mssLocalLatticeRadius D)
  simp

private theorem mssCanonicalCube_cutoff_derivative_l1
    (D : MSSWavefrontKernelData) (r : Nat) :
    ∃ A : Real, 0 ≤ A ∧ ∀ scale : Real, 2 ≤ scale →
      ∀ k : Fin (mssCanonicalCubeCount D scale),
        (∫ xi : Euclidean 2,
          ‖iteratedFDeriv Real r (mssCanonicalCubeCutoff D scale k) xi‖) ≤
          A * (1 * Real.sqrt scale) ^ 2 * ((1 * Real.sqrt scale)⁻¹) ^ r := by
  refine ⟨∫ eta : Euclidean 2,
      ‖iteratedFDeriv Real r mssLatticeSynthesisPrototype eta‖,
    integral_nonneg fun _ => norm_nonneg _, ?_⟩
  intro scale hscale k
  have hdim : Module.finrank Real (Euclidean 2) = 2 := by norm_num
  apply le_of_eq
  calc
    (∫ xi : Euclidean 2,
      ‖iteratedFDeriv Real r (mssCanonicalCubeCutoff D scale k) xi‖) =
        (mssCanonicalLatticeRadius scale) ^ 2 *
          ((mssCanonicalLatticeRadius scale)⁻¹) ^ r *
            ∫ eta : Euclidean 2,
              ‖iteratedFDeriv Real r mssLatticeSynthesisPrototype eta‖ := by
      unfold mssCanonicalCubeCutoff
      simpa only [hdim] using
        (integral_norm_iteratedFDeriv_translatedDilatedSchwartzCutoff
          mssLatticeSynthesisPrototype (mssCanonicalCubeCenter D scale k)
          (mssCanonicalLatticeRadius_pos scale) r)
    _ = (∫ eta : Euclidean 2,
          ‖iteratedFDeriv Real r mssLatticeSynthesisPrototype eta‖) *
        (1 * Real.sqrt scale) ^ 2 * ((1 * Real.sqrt scale)⁻¹) ^ r := by
      rw [mssCanonicalLatticeRadius_eq_sqrt hscale]
      simp only [one_mul]
      ring

/-- Every derivative of a canonical lattice cutoff has its natural pointwise
scale.  This is the `L∞` companion to the normalized `L¹` cutoff field and
is used when a cutoff derivative is paired with an `L¹` profile derivative. -/
private theorem exists_mssCanonicalCube_cutoff_iteratedFDeriv_norm_bound
    (D : MSSWavefrontKernelData) (r : Nat) :
    ∃ A : Real, 0 ≤ A ∧ ∀ scale : Real, 2 ≤ scale →
      ∀ k : Fin (mssCanonicalCubeCount D scale), ∀ xi : Euclidean 2,
        ‖iteratedFDeriv Real r (mssCanonicalCubeCutoff D scale k) xi‖ ≤
          A * ((Real.sqrt scale)⁻¹) ^ r := by
  let A : Real := SchwartzMap.seminorm Complex 0 r mssLatticeSynthesisPrototype
  have hA : 0 ≤ A := by
    dsimp [A]
    exact (norm_nonneg (iteratedFDeriv Real r mssLatticeSynthesisPrototype 0)).trans
      (mssLatticeSynthesisPrototype.norm_iteratedFDeriv_le_seminorm Complex r 0)
  refine ⟨A, hA, ?_⟩
  intro scale hscale k xi
  have hradius : 0 < mssCanonicalLatticeRadius scale :=
    mssCanonicalLatticeRadius_pos scale
  calc
    ‖iteratedFDeriv Real r (mssCanonicalCubeCutoff D scale k) xi‖ =
        (mssCanonicalLatticeRadius scale)⁻¹ ^ r *
          ‖iteratedFDeriv Real r mssLatticeSynthesisPrototype
            ((mssCanonicalLatticeRadius scale)⁻¹ •
              (xi - mssCanonicalCubeCenter D scale k))‖ := by
      unfold mssCanonicalCubeCutoff
      exact norm_iteratedFDeriv_translatedDilatedSchwartzCutoff
        mssLatticeSynthesisPrototype (mssCanonicalCubeCenter D scale k) xi hradius r
    _ ≤ (mssCanonicalLatticeRadius scale)⁻¹ ^ r * A := by
      apply mul_le_mul_of_nonneg_left
      · dsimp [A]
        exact mssLatticeSynthesisPrototype.norm_iteratedFDeriv_le_seminorm Complex r _
      · exact pow_nonneg (inv_nonneg.mpr hradius.le) _
    _ = A * ((Real.sqrt scale)⁻¹) ^ r := by
      rw [mssCanonicalLatticeRadius_eq_sqrt hscale]
      ring

/-- The canonical cutoffs have the same normalized derivative bounds when
their nominal cube width is enlarged from the literal lattice width `1` to
`2`.  The fixed factor is absorbed into the order-dependent uniform
constant. -/
private theorem mssCanonicalCube_cutoff_derivative_l1_width_two
    (D : MSSWavefrontKernelData) (r : Nat) :
    ∃ A : Real, 0 ≤ A ∧ ∀ scale : Real, 2 ≤ scale →
      ∀ k : Fin (mssCanonicalCubeCount D scale),
        (∫ xi : Euclidean 2,
          ‖iteratedFDeriv Real r (mssCanonicalCubeCutoff D scale k) xi‖) ≤
          A * (2 * Real.sqrt scale) ^ 2 * ((2 * Real.sqrt scale)⁻¹) ^ r := by
  obtain ⟨A, hA, hderiv⟩ := mssCanonicalCube_cutoff_derivative_l1 D r
  refine ⟨(2 : Real) ^ r * A, mul_nonneg (pow_nonneg (by norm_num) _) hA, ?_⟩
  intro scale hscale k
  have hbase :
      (∫ xi : Euclidean 2,
        ‖iteratedFDeriv Real r (mssCanonicalCubeCutoff D scale k) xi‖) ≤
        A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ r := by
    simpa only [one_mul] using hderiv scale hscale k
  have hbase_nonneg :
      0 ≤ A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ r := by
    exact mul_nonneg (mul_nonneg hA (sq_nonneg _))
      (pow_nonneg (inv_nonneg.mpr (by positivity)) _)
  have htwo : (2 : Real) ≠ 0 := by norm_num
  have hcancel : (2 : Real) ^ r * ((2 : Real)⁻¹) ^ r = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ htwo, one_pow]
  have hwide :
      ((2 : Real) ^ r * A) * (2 * Real.sqrt scale) ^ 2 *
          ((2 * Real.sqrt scale)⁻¹) ^ r =
        4 * (A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ r) := by
    calc
      ((2 : Real) ^ r * A) * (2 * Real.sqrt scale) ^ 2 *
          ((2 * Real.sqrt scale)⁻¹) ^ r =
          ((2 : Real) ^ r * ((2 : Real)⁻¹) ^ r) * 4 *
            (A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ r) := by
        simp only [mul_inv_rev, mul_pow]
        ring
      _ = 4 * (A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ r) := by
        rw [hcancel]
        ring
  calc
    (∫ xi : Euclidean 2,
      ‖iteratedFDeriv Real r (mssCanonicalCubeCutoff D scale k) xi‖) ≤
        A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ r := hbase
    _ ≤ 4 * (A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ r) := by
      nlinarith
    _ = ((2 : Real) ^ r * A) * (2 * Real.sqrt scale) ^ 2 *
        ((2 * Real.sqrt scale)⁻¹) ^ r := hwide.symm

/-- A natural-scale packet ball gives a fixed coordinate square around the
integer base point of its ray. -/
private theorem mss_normalizedProfile_coordinate_ne_packetLatticeBase_of_ray_bound
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (xi : Euclidean 2)
    (hpacket : ‖xi - ((n : Real) * Real.sqrt scale) • D.directions scale nu‖ ≤
      (2 * D.angularConstant + 11 / 4) * Real.sqrt scale) :
    ∀ i : Fin 2,
      |((Real.sqrt scale)⁻¹ • xi -
        standardLatticePoint (mssPacketLatticeBase D scale n nu)) i| ≤
        2 * D.angularConstant + 15 / 4 := by
  have hscale_pos : 0 < scale := by linarith
  have hsqrt_pos : 0 < Real.sqrt scale := Real.sqrt_pos.2 hscale_pos
  let y : Euclidean 2 := (Real.sqrt scale)⁻¹ • xi
  let r : Euclidean 2 := (n : Real) • D.directions scale nu
  have hnorm : ‖y - r‖ ≤ 2 * D.angularConstant + 11 / 4 := by
    have heq : y - r =
        (Real.sqrt scale)⁻¹ •
          (xi - ((n : Real) * Real.sqrt scale) • D.directions scale nu) := by
      dsimp only [y, r]
      rw [smul_sub, smul_smul]
      congr 1
      field_simp [hsqrt_pos.ne']
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt_pos)]
    calc
      (Real.sqrt scale)⁻¹ *
          ‖xi - ((n : Real) * Real.sqrt scale) • D.directions scale nu‖ ≤
          (Real.sqrt scale)⁻¹ *
            ((2 * D.angularConstant + 11 / 4) * Real.sqrt scale) :=
        mul_le_mul_of_nonneg_left hpacket (inv_nonneg.mpr hsqrt_pos.le)
      _ = 2 * D.angularConstant + 11 / 4 := by
        field_simp [hsqrt_pos.ne']
  intro i
  have hcoord : |(y - r) i| ≤ 2 * D.angularConstant + 11 / 4 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (y - r) i).trans hnorm
  have hfloor :
      |r i - ((⌊r i⌋ : Int) : Real)| ≤ 1 :=
    mss_abs_sub_intFloor_le_one (r i)
  change |y i - ((⌊(n : Real) * D.directions scale nu i⌋ : Int) : Real)| ≤
    2 * D.angularConstant + 15 / 4
  have hr : r i = (n : Real) * D.directions scale nu i := by
    simp [r, PiLp.smul_apply, smul_eq_mul]
  rw [← hr]
  calc
    |y i - ((⌊r i⌋ : Int) : Real)| ≤
        |y i - r i| + |r i - ((⌊r i⌋ : Int) : Real)| := abs_sub_le _ _ _
    _ ≤ (2 * D.angularConstant + 11 / 4) + 1 := add_le_add hcoord hfloor
    _ = 2 * D.angularConstant + 15 / 4 := by ring

/-- A nonzero literal MSS spatial profile lies in a uniform natural-scale
ball around its radial--angular packet center. -/
private theorem mss_spatialProfile_center_ne_packet_ray
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (_hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale) (xi : Euclidean 2)
    (hprofile : D.spatialProfile scale n nu xi ≠ 0) :
    ‖xi - ((n : Real) * Real.sqrt scale) • D.directions scale nu‖ ≤
      (2 * D.angularConstant + 11 / 4) * Real.sqrt scale := by
  have hscale_pos : 0 < scale := by linarith
  have hsqrt_pos : 0 < Real.sqrt scale :=
    Real.sqrt_pos.2 hscale_pos
  rw [D.spatialProfile_apply] at hprofile
  rcases mul_ne_zero_iff.mp hprofile with ⟨hchi, hrest⟩
  rcases mul_ne_zero_iff.mp hrest with ⟨hamp, hrad⟩

  have hsector : xi ∈ angularSector (D.directions scale nu)
      (D.angularConstant * scale ^ (-(1 / 2 : Real))) :=
    D.chi_support scale nu hnu hchi
  rcases hsector with ⟨hxi_ne, hangular⟩

  have hamp_annulus :=
    D.radialTime.amplitude_support_annulus (scale⁻¹ • xi) hamp
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hscale_pos] at hamp_annulus
  have hamp_annulus' : ‖xi‖ / scale ∈ Icc (1 / 2 : Real) 2 := by
    simpa [div_eq_mul_inv, mul_comm] using hamp_annulus
  have hxi_upper : ‖xi‖ ≤ 2 * scale :=
    (div_le_iff₀ hscale_pos).mp hamp_annulus'.2

  have hradial_window :
      |(Real.sqrt scale)⁻¹ * ‖xi‖ - (n : Real)| < 11 / 4 :=
    D.radialTime.radial_support _ hrad

  have hradial_identity :
      ‖xi‖ - (n : Real) * Real.sqrt scale =
        Real.sqrt scale *
          ((Real.sqrt scale)⁻¹ * ‖xi‖ - (n : Real)) := by
    have hcancel :
        Real.sqrt scale * ((Real.sqrt scale)⁻¹ * ‖xi‖) = ‖xi‖ := by
      field_simp [hsqrt_pos.ne']
    rw [mul_sub, hcancel]
    ring
  have hradial_bound :
      |‖xi‖ - (n : Real) * Real.sqrt scale| ≤
        (11 / 4) * Real.sqrt scale := by
    calc
      |‖xi‖ - (n : Real) * Real.sqrt scale| =
          |Real.sqrt scale *
            ((Real.sqrt scale)⁻¹ * ‖xi‖ - (n : Real))| := by
            rw [hradial_identity]
      _ = Real.sqrt scale *
          |(Real.sqrt scale)⁻¹ * ‖xi‖ - (n : Real)| := by
            rw [abs_mul, abs_of_pos hsqrt_pos]
      _ ≤ Real.sqrt scale * (11 / 4) :=
        mul_le_mul_of_nonneg_left hradial_window.le hsqrt_pos.le
      _ = (11 / 4) * Real.sqrt scale := by ring

  have hscale_rpow :
      scale ^ (-(1 / 2 : Real)) * scale = Real.sqrt scale := by
    calc
      scale ^ (-(1 / 2 : Real)) * scale =
          scale ^ (-(1 / 2 : Real)) * scale ^ (1 : Real) := by
            rw [Real.rpow_one]
      _ = scale ^ (-(1 / 2 : Real) + (1 : Real)) :=
        (Real.rpow_add hscale_pos _ _).symm
      _ = Real.sqrt scale := by
        convert (Real.sqrt_eq_rpow scale).symm using 1; norm_num

  have hxi_norm_pos : 0 < ‖xi‖ := norm_pos_iff.mpr hxi_ne
  have hnormalize : ‖xi‖ • ((‖xi‖)⁻¹ • xi) = xi := by
    rw [smul_smul, mul_inv_cancel₀ hxi_norm_pos.ne', one_smul]
  have hfirst_eq :
      xi - ‖xi‖ • D.directions scale nu =
        ‖xi‖ • ((‖xi‖)⁻¹ • xi - D.directions scale nu) := by
    calc
      xi - ‖xi‖ • D.directions scale nu =
          ‖xi‖ • ((‖xi‖)⁻¹ • xi) - ‖xi‖ • D.directions scale nu := by
            rw [hnormalize]
      _ = ‖xi‖ • ((‖xi‖)⁻¹ • xi - D.directions scale nu) := by
            rw [smul_sub]

  have htwo_scale_nonneg : 0 ≤ 2 * scale := by linarith
  have hfirst_bound :
      ‖xi - ‖xi‖ • D.directions scale nu‖ ≤
        (2 * D.angularConstant) * Real.sqrt scale := by
    calc
      ‖xi - ‖xi‖ • D.directions scale nu‖ =
          ‖xi‖ * ‖(‖xi‖)⁻¹ • xi - D.directions scale nu‖ := by
            rw [hfirst_eq, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (norm_nonneg _)]
      _ ≤ (2 * scale) *
          ‖(‖xi‖)⁻¹ • xi - D.directions scale nu‖ :=
        mul_le_mul_of_nonneg_right hxi_upper (norm_nonneg _)
      _ ≤ (2 * scale) *
          (D.angularConstant * scale ^ (-(1 / 2 : Real))) :=
        mul_le_mul_of_nonneg_left hangular htwo_scale_nonneg
      _ = (2 * D.angularConstant) * Real.sqrt scale := by
        calc
          (2 * scale) * (D.angularConstant * scale ^ (-(1 / 2 : Real))) =
              (2 * D.angularConstant) *
                (scale ^ (-(1 / 2 : Real)) * scale) := by ring
          _ = (2 * D.angularConstant) * Real.sqrt scale := by
            rw [hscale_rpow]

  have hsecond_bound :
      ‖(‖xi‖ - (n : Real) * Real.sqrt scale) • D.directions scale nu‖ ≤
        (11 / 4) * Real.sqrt scale := by
    calc
      ‖(‖xi‖ - (n : Real) * Real.sqrt scale) • D.directions scale nu‖ =
          |‖xi‖ - (n : Real) * Real.sqrt scale| *
            ‖D.directions scale nu‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = |‖xi‖ - (n : Real) * Real.sqrt scale| := by
            rw [D.direction_unit scale nu hnu, mul_one]
      _ ≤ (11 / 4) * Real.sqrt scale := hradial_bound

  have hsplit :
      xi - ((n : Real) * Real.sqrt scale) • D.directions scale nu =
        (xi - ‖xi‖ • D.directions scale nu) +
          ((‖xi‖ - (n : Real) * Real.sqrt scale) • D.directions scale nu) := by
    rw [sub_smul]
    abel
  calc
    ‖xi - ((n : Real) * Real.sqrt scale) • D.directions scale nu‖ =
        ‖(xi - ‖xi‖ • D.directions scale nu) +
          ((‖xi‖ - (n : Real) * Real.sqrt scale) •
            D.directions scale nu)‖ := by
          rw [hsplit]
    _ ≤ ‖xi - ‖xi‖ • D.directions scale nu‖ +
          ‖(‖xi‖ - (n : Real) * Real.sqrt scale) •
            D.directions scale nu‖ :=
      norm_add_le _ _
    _ ≤ (2 * D.angularConstant) * Real.sqrt scale +
          (11 / 4) * Real.sqrt scale :=
      add_le_add hfirst_bound hsecond_bound
    _ = (2 * D.angularConstant + 11 / 4) * Real.sqrt scale := by ring

/-- The literal profile form supplies the ray-bound premise for the preceding
integer-lattice coordinate estimate. -/
private theorem mss_normalizedProfile_coordinate_ne_packetLatticeBase
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale) (xi : Euclidean 2)
    (hprofile : D.spatialProfile scale n nu xi ≠ 0) :
    ∀ i : Fin 2,
      |((Real.sqrt scale)⁻¹ • xi -
        standardLatticePoint (mssPacketLatticeBase D scale n nu)) i| ≤
        2 * D.angularConstant + 15 / 4 := by
  apply mss_normalizedProfile_coordinate_ne_packetLatticeBase_of_ray_bound
    D hscale n nu xi
  exact mss_spatialProfile_center_ne_packet_ray D hscale n nu hn hnu xi hprofile

private theorem standardLatticePoint_add (a b : Fin 2 → Int) :
    standardLatticePoint (fun i => a i + b i) =
      standardLatticePoint a + standardLatticePoint b := by
  apply WithLp.ofLp_injective
  funext i
  simp [standardLatticePoint]

/-- Evaluation of a selected packet-local canonical cutoff in the local
lattice coordinates around that packet's integer ray base point. -/
private theorem mssCanonicalCubeCutoff_packetLocalGridEmbedding_apply
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale)
    (k : Fin (mssLatticeGridCount (mssLocalLatticeRadius D)))
    (xi : Euclidean 2) :
    mssCanonicalCubeCutoff D scale
      (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu k) xi =
        (mssLatticeSynthesisReal
          (((Real.sqrt scale)⁻¹ • xi -
            standardLatticePoint (mssPacketLatticeBase D scale n nu)) -
              standardLatticePoint (mssLatticeGridLabel
                (mssLocalLatticeRadius D) k)) : Complex) := by
  rw [mssCanonicalCubeCutoff_apply_eq_active D hscale
    (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu k) xi]
  change translatedDilatedSchwartzCutoff mssLatticeSynthesisPrototype
      (Real.sqrt scale • standardLatticePoint
        (mssLatticeGridLabel (mssGlobalLatticeRadius D scale)
          (mssPacketLocalGridIndex D scale hscale n nu hn hnu k)))
      (Real.sqrt scale) _ xi = _
  rw [mssLatticeGridLabel_packetLocalGridIndex D hscale n nu hn hnu k]
  rw [mss_translatedDilatedLatticeSynthesis_apply]
  congr 1
  rw [standardLatticePoint_add]
  abel

/-- The packet-local embedded cube family synthesizes one nonzero smooth
spatial profile exactly. -/
private theorem mssCanonicalCube_packetLocalGrid_partition
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale) (xi : Euclidean 2)
    (hprofile : D.spatialProfile scale n nu xi ≠ 0) :
    (∑ k : Fin (mssLatticeGridCount (mssLocalLatticeRadius D)),
      mssCanonicalCubeCutoff D scale
        (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu k) xi) = 1 := by
  let y : Euclidean 2 := (Real.sqrt scale)⁻¹ • xi -
    standardLatticePoint (mssPacketLatticeBase D scale n nu)
  have hcoordinate := mss_normalizedProfile_coordinate_ne_packetLatticeBase
    D hscale n nu hn hnu xi hprofile
  have hceil : 2 * D.angularConstant + 15 / 4 ≤
      (mssLocalLatticeRadius D : Real) := by
    simpa [mssLocalLatticeRadius] using
      (Nat.le_ceil (2 * D.angularConstant + 15 / 4))
  have hy : ∀ i : Fin 2, |y i| ≤ (mssLocalLatticeRadius D : Real) := by
    intro i
    dsimp only [y]
    exact (hcoordinate i).trans hceil
  calc
    (∑ k : Fin (mssLatticeGridCount (mssLocalLatticeRadius D)),
      mssCanonicalCubeCutoff D scale
        (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu k) xi) =
        ∑ k : Fin (mssLatticeGridCount (mssLocalLatticeRadius D)),
          (mssLatticeSynthesisReal
            (y - standardLatticePoint
              (mssLatticeGridLabel (mssLocalLatticeRadius D) k)) : Complex) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [mssCanonicalCubeCutoff_packetLocalGridEmbedding_apply
        D hscale n nu hn hnu k xi]
    _ = ∑ ab ∈ (Finset.range
          (mssLatticeGridSide (mssLocalLatticeRadius D))).product
          (Finset.range (mssLatticeGridSide (mssLocalLatticeRadius D))),
        (mssLatticeSynthesisReal
          (y - standardLatticePoint (fun i =>
            if i = (0 : Fin 2) then
              (ab.1 : Int) - (mssLocalLatticeRadius D : Int)
            else (ab.2 : Int) - (mssLocalLatticeRadius D : Int))) : Complex) :=
      mss_sum_latticeGridLabel_eq_product (mssLocalLatticeRadius D)
        (fun label => (mssLatticeSynthesisReal
          (y - standardLatticePoint label) : Complex))
    _ = 1 := by
      exact_mod_cast mss_finite_standardLatticeSynthesis_partition
        (x := y) (mssLocalLatticeRadius D) hy

/-- The selected canonical cube cutoffs reconstruct every active smooth MSS
spatial profile. -/
private theorem mssCanonicalCube_reconstruct_spatialProfile
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale) (xi : Euclidean 2) :
    ∑ k ∈ mssCanonicalCubeSets D scale n nu,
      mssCanonicalCubeCutoff D scale k xi * D.spatialProfile scale n nu xi =
        D.spatialProfile scale n nu xi := by
  classical
  rw [mssCanonicalCubeSets_eq_active D hscale n nu hn hnu]
  by_cases hprofile : D.spatialProfile scale n nu xi = 0
  · rw [hprofile]
    apply Finset.sum_eq_zero
    intro k hk
    simp
  calc
    (∑ k ∈ Finset.univ.map
        (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu),
      mssCanonicalCubeCutoff D scale k xi * D.spatialProfile scale n nu xi) =
        ∑ j : Fin (mssLatticeGridCount (mssLocalLatticeRadius D)),
          mssCanonicalCubeCutoff D scale
            (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu j) xi *
              D.spatialProfile scale n nu xi := by
      simpa only using Finset.sum_map Finset.univ
        (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu)
        (fun k => mssCanonicalCubeCutoff D scale k xi *
          D.spatialProfile scale n nu xi)
    _ = (∑ j : Fin (mssLatticeGridCount (mssLocalLatticeRadius D)),
        mssCanonicalCubeCutoff D scale
          (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu j) xi) *
            D.spatialProfile scale n nu xi := by
      rw [Finset.sum_mul]
    _ = 1 * D.spatialProfile scale n nu xi := by
      rw [mssCanonicalCube_packetLocalGrid_partition
        D hscale n nu hn hnu xi hprofile]
    _ = D.spatialProfile scale n nu xi := one_mul _

private theorem mss_coord_norm_le_two_mul {x : Euclidean 2} {A : Real}
    (hA : 0 ≤ A) (hx : ∀ i : Fin 2, |x i| ≤ A) : ‖x‖ ≤ 2 * A := by
  have h0 := hx 0
  have h1 := hx 1
  rw [abs_le] at h0 h1
  have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => Real) x
  rw [Fin.sum_univ_two] at hsq
  simp only [Real.norm_eq_abs, sq_abs] at hsq
  nlinarith [norm_nonneg x]

/-- A canonical cube in a packet-local offset grid stays a uniformly bounded
number of natural cube widths from the packet ray. -/
private theorem mssCanonicalCube_center_ne_packet_ray_local
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale)
    (k : Fin (mssLatticeGridCount (mssLocalLatticeRadius D))) :
    ‖mssCanonicalCubeCenter D scale
      (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu k) -
        ((n : Real) * Real.sqrt scale) • D.directions scale nu‖ ≤
      (2 * ((mssLocalLatticeRadius D : Real) + 1)) * Real.sqrt scale := by
  have hcoord : ∀ i : Fin 2,
      |(standardLatticePoint (fun i =>
          mssPacketLatticeBase D scale n nu i +
            mssLatticeGridLabel (mssLocalLatticeRadius D) k i) -
        (n : Real) • D.directions scale nu) i| ≤
        (mssLocalLatticeRadius D : Real) + 1 := by
    intro i
    have hfloor : |((mssPacketLatticeBase D scale n nu i : Int) : Real) -
        (n : Real) * D.directions scale nu i| ≤ 1 := by
      rw [abs_sub_comm]
      simpa [mssPacketLatticeBase] using
        mss_abs_sub_intFloor_le_one ((n : Real) * D.directions scale nu i)
    have hlabelInt := mssLatticeGridLabel_abs_le (mssLocalLatticeRadius D) k i
    have hlabel : |((mssLatticeGridLabel (mssLocalLatticeRadius D) k i : Int) : Real)| ≤
        (mssLocalLatticeRadius D : Real) := by
      exact_mod_cast hlabelInt
    change |((mssPacketLatticeBase D scale n nu i +
      mssLatticeGridLabel (mssLocalLatticeRadius D) k i : Int) : Real) -
        (n : Real) * D.directions scale nu i| ≤
          (mssLocalLatticeRadius D : Real) + 1
    calc
      |((mssPacketLatticeBase D scale n nu i +
          mssLatticeGridLabel (mssLocalLatticeRadius D) k i : Int) : Real) -
          (n : Real) * D.directions scale nu i| =
          |(((mssPacketLatticeBase D scale n nu i : Int) : Real) -
            (n : Real) * D.directions scale nu i) +
              ((mssLatticeGridLabel (mssLocalLatticeRadius D) k i : Int) : Real)| := by
            push_cast
            ring_nf
      _ ≤ |((mssPacketLatticeBase D scale n nu i : Int) : Real) -
            (n : Real) * D.directions scale nu i| +
              |((mssLatticeGridLabel (mssLocalLatticeRadius D) k i : Int) : Real)| :=
        abs_add_le _ _
      _ ≤ 1 + (mssLocalLatticeRadius D : Real) := add_le_add hfloor hlabel
      _ = (mssLocalLatticeRadius D : Real) + 1 := by ring
  have hunscaled :
      ‖standardLatticePoint (fun i =>
          mssPacketLatticeBase D scale n nu i +
            mssLatticeGridLabel (mssLocalLatticeRadius D) k i) -
        (n : Real) • D.directions scale nu‖ ≤
        2 * ((mssLocalLatticeRadius D : Real) + 1) :=
    mss_coord_norm_le_two_mul (by positivity) hcoord
  rw [mssCanonicalCubeCenter_eq_sqrt D hscale
    (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu k)]
  change ‖Real.sqrt scale • standardLatticePoint
      (mssLatticeGridLabel (mssGlobalLatticeRadius D scale)
        (mssPacketLocalGridIndex D scale hscale n nu hn hnu k)) -
        ((n : Real) * Real.sqrt scale) • D.directions scale nu‖ ≤ _
  rw [mssLatticeGridLabel_packetLocalGridIndex D hscale n nu hn hnu k]
  have hsplit :
      Real.sqrt scale • standardLatticePoint (fun i =>
          mssPacketLatticeBase D scale n nu i +
            mssLatticeGridLabel (mssLocalLatticeRadius D) k i) -
        ((n : Real) * Real.sqrt scale) • D.directions scale nu =
      Real.sqrt scale •
        (standardLatticePoint (fun i =>
          mssPacketLatticeBase D scale n nu i +
            mssLatticeGridLabel (mssLocalLatticeRadius D) k i) -
          (n : Real) • D.directions scale nu) := by
    rw [smul_sub, smul_smul]
    congr 1
    ring_nf
  rw [hsplit, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt scale *
        ‖standardLatticePoint (fun i =>
          mssPacketLatticeBase D scale n nu i +
            mssLatticeGridLabel (mssLocalLatticeRadius D) k i) -
          (n : Real) • D.directions scale nu‖ ≤
      Real.sqrt scale * (2 * ((mssLocalLatticeRadius D : Real) + 1)) :=
        mul_le_mul_of_nonneg_left hunscaled (Real.sqrt_nonneg _)
    _ = (2 * ((mssLocalLatticeRadius D : Real) + 1)) * Real.sqrt scale := by
      ring

private theorem mssCanonicalCube_center_ne_packet_ray
    (D : MSSWavefrontKernelData) :
    ∃ C : Real, 0 ≤ C ∧ ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
        ∀ k ∈ mssCanonicalCubeSets D scale n nu,
          ‖mssCanonicalCubeCenter D scale k -
            ((n : Real) * Real.sqrt scale) • D.directions scale nu‖ ≤
              C * Real.sqrt scale := by
  refine ⟨2 * ((mssLocalLatticeRadius D : Real) + 1), by positivity, ?_⟩
  intro scale hscale n hn nu hnu k hk
  rw [mssCanonicalCubeSets_eq_active D hscale n nu hn hnu] at hk
  rcases Finset.mem_map.mp hk with ⟨j, hj, hjk⟩
  subst k
  exact mssCanonicalCube_center_ne_packet_ray_local D hscale n nu hn hnu j

/-- Any cube selected by an active packet is already within a fixed distance
of that packet ray after normalizing by `sqrt scale`. -/
private theorem mssCanonicalCube_unscaled_label_ne_packet_ray
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale)
    (cube : Fin (mssCanonicalCubeCount D scale))
    (hcube : cube ∈ mssCanonicalCubeSets D scale n nu) :
    ‖standardLatticePoint
        (mssLatticeGridLabel (mssGlobalLatticeRadius D scale) cube) -
      (n : Real) • D.directions scale nu‖ ≤
        2 * ((mssLocalLatticeRadius D : Real) + 1) := by
  rw [mssCanonicalCubeSets_eq_active D hscale n nu hn hnu] at hcube
  rcases Finset.mem_map.mp hcube with ⟨k, hk, hkcube⟩
  subst cube
  change ‖standardLatticePoint
      (mssLatticeGridLabel (mssGlobalLatticeRadius D scale)
        (mssPacketLocalGridIndex D scale hscale n nu hn hnu k)) -
      (n : Real) • D.directions scale nu‖ ≤ _
  rw [mssLatticeGridLabel_packetLocalGridIndex D hscale n nu hn hnu k]
  have hscaled := mssCanonicalCube_center_ne_packet_ray_local
    D hscale n nu hn hnu k
  rw [mssCanonicalCubeCenter_eq_sqrt D hscale
    (mssPacketLocalGridEmbedding D scale hscale n nu hn hnu k)] at hscaled
  change ‖Real.sqrt scale • standardLatticePoint
      (mssLatticeGridLabel (mssGlobalLatticeRadius D scale)
        (mssPacketLocalGridIndex D scale hscale n nu hn hnu k)) -
        ((n : Real) * Real.sqrt scale) • D.directions scale nu‖ ≤ _ at hscaled
  rw [mssLatticeGridLabel_packetLocalGridIndex D hscale n nu hn hnu k] at hscaled
  have hsplit :
      Real.sqrt scale • standardLatticePoint (fun i =>
          mssPacketLatticeBase D scale n nu i +
            mssLatticeGridLabel (mssLocalLatticeRadius D) k i) -
        ((n : Real) * Real.sqrt scale) • D.directions scale nu =
      Real.sqrt scale •
        (standardLatticePoint (fun i =>
          mssPacketLatticeBase D scale n nu i +
            mssLatticeGridLabel (mssLocalLatticeRadius D) k i) -
          (n : Real) • D.directions scale nu) := by
    rw [smul_sub, smul_smul]
    congr 1
    ring_nf
  rw [hsplit, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hscaled
  have hsqrt_pos : 0 < Real.sqrt scale := Real.sqrt_pos.2 (by linarith)
  rw [mul_comm (2 * ((mssLocalLatticeRadius D : Real) + 1))
    (Real.sqrt scale)] at hscaled
  exact le_of_mul_le_mul_left hscaled hsqrt_pos

/-- Two active packets sharing a canonical cube have uniformly close
normalized ray points. -/
private theorem mssCanonicalCube_shared_ray_distance
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n₁ nu₁ n₂ nu₂ : Int)
    (hn₁ : n₁ ∈ relevantRadialIndexEnumeration scale)
    (hnu₁ : nu₁ ∈ D.angularIndices scale)
    (hn₂ : n₂ ∈ relevantRadialIndexEnumeration scale)
    (hnu₂ : nu₂ ∈ D.angularIndices scale)
    (cube : Fin (mssCanonicalCubeCount D scale))
    (hcube₁ : cube ∈ mssCanonicalCubeSets D scale n₁ nu₁)
    (hcube₂ : cube ∈ mssCanonicalCubeSets D scale n₂ nu₂) :
    ‖(n₁ : Real) • D.directions scale nu₁ -
      (n₂ : Real) • D.directions scale nu₂‖ ≤
        4 * ((mssLocalLatticeRadius D : Real) + 1) := by
  have h₁ := mssCanonicalCube_unscaled_label_ne_packet_ray
    D hscale n₁ nu₁ hn₁ hnu₁ cube hcube₁
  have h₂ := mssCanonicalCube_unscaled_label_ne_packet_ray
    D hscale n₂ nu₂ hn₂ hnu₂ cube hcube₂
  let z : Euclidean 2 := standardLatticePoint
    (mssLatticeGridLabel (mssGlobalLatticeRadius D scale) cube)
  calc
    ‖(n₁ : Real) • D.directions scale nu₁ -
        (n₂ : Real) • D.directions scale nu₂‖ =
        ‖((n₁ : Real) • D.directions scale nu₁ - z) +
          (z - (n₂ : Real) • D.directions scale nu₂)‖ := by
      congr 1
      dsimp [z]
      abel
    _ ≤ ‖(n₁ : Real) • D.directions scale nu₁ - z‖ +
        ‖z - (n₂ : Real) • D.directions scale nu₂‖ := norm_add_le _ _
    _ = ‖z - (n₁ : Real) • D.directions scale nu₁‖ +
        ‖z - (n₂ : Real) • D.directions scale nu₂‖ := by
      rw [norm_sub_rev]
    _ ≤ 2 * ((mssLocalLatticeRadius D : Real) + 1) +
        2 * ((mssLocalLatticeRadius D : Real) + 1) := by
      exact add_le_add h₁ h₂
    _ = 4 * ((mssLocalLatticeRadius D : Real) + 1) := by ring

/-- For nonnegative radial labels, ray-point distance controls radial
distance. -/
private theorem mss_radial_distance_le_ray_distance
    {n n' : Int} {d d' : Euclidean 2}
    (hn : 0 ≤ (n : Real)) (hn' : 0 ≤ (n' : Real))
    (hd : ‖d‖ = 1) (hd' : ‖d'‖ = 1) :
    |(n : Real) - (n' : Real)| ≤
      ‖(n : Real) • d - (n' : Real) • d'‖ := by
  have h := abs_norm_sub_norm_le ((n : Real) • d) ((n' : Real) • d')
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn,
    abs_of_nonneg hn', hd, hd'] using h

/-- A real bound for an integer difference gives the corresponding natural
ceiling bound. -/
private theorem mss_natAbs_sub_le_ceil
    {a b : Int} {E : Real}
    (h : |(a : Real) - (b : Real)| ≤ E) :
    (a - b).natAbs ≤ ⌈E⌉₊ := by
  have hreal : ((a - b).natAbs : Real) ≤ E := by
    simpa [Int.natCast_natAbs, Int.cast_sub] using h
  have hceil : E ≤ (⌈E⌉₊ : Real) := Nat.le_ceil _
  exact_mod_cast hreal.trans hceil

/-- Relevant radial labels are positive and comparable to `sqrt scale` once
the scale is outside a fixed bounded range. -/
private theorem mss_large_relevant_radial_lower
    {scale : Real} {n : Int}
    (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hroot : 12 ≤ Real.sqrt scale) :
    Real.sqrt scale / 4 ≤ (n : Real) ∧ 0 < (n : Real) := by
  have hrel : n ∈ relevantRadialIndices scale :=
    (mem_relevantRadialIndexEnumeration_iff scale n).mp hn
  rcases hrel with ⟨s, hs, hdist⟩
  have hdist' : -3 < (n : Real) - s := (abs_lt.mp hdist).1
  have hlower : Real.sqrt scale / 4 ≤ (n : Real) := by
    nlinarith [hs.1, hdist', hroot]
  constructor
  · exact hlower
  · nlinarith [hlower, hroot]

/-- On the bounded range of scales, two relevant radial labels have a
uniformly bounded difference. -/
private theorem mss_small_relevant_radial_difference
    {scale : Real} {n n' : Int}
    (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hn' : n' ∈ relevantRadialIndexEnumeration scale)
    (hroot : Real.sqrt scale < 12) :
    (n - n').natAbs ≤ 30 := by
  have hrel : n ∈ relevantRadialIndices scale :=
    (mem_relevantRadialIndexEnumeration_iff scale n).mp hn
  have hrel' : n' ∈ relevantRadialIndices scale :=
    (mem_relevantRadialIndexEnumeration_iff scale n').mp hn'
  rcases hrel with ⟨s, hs, hdist⟩
  rcases hrel' with ⟨s', hs', hdist'⟩
  have hdistLower : -3 < (n : Real) - s := (abs_lt.mp hdist).1
  have hdistUpper : (n : Real) - s < 3 := (abs_lt.mp hdist).2
  have hdistLower' : -3 < (n' : Real) - s' := (abs_lt.mp hdist').1
  have hdistUpper' : (n' : Real) - s' < 3 := (abs_lt.mp hdist').2
  have hnLower : (-3 : Int) < n := by
    have : (-3 : Real) < (n : Real) := by
      have hsqrt : 0 ≤ Real.sqrt scale := Real.sqrt_nonneg _
      nlinarith [hs.1, hdistLower]
    exact_mod_cast this
  have hnUpper : n < 27 := by
    have : (n : Real) < 27 := by nlinarith [hs.2, hdistUpper, hroot]
    exact_mod_cast this
  have hnLower' : (-3 : Int) < n' := by
    have : (-3 : Real) < (n' : Real) := by
      have hsqrt : 0 ≤ Real.sqrt scale := Real.sqrt_nonneg _
      nlinarith [hs'.1, hdistLower']
    exact_mod_cast this
  have hnUpper' : n' < 27 := by
    have : (n' : Real) < 27 := by nlinarith [hs'.2, hdistUpper', hroot]
    exact_mod_cast this
  omega

/-- Angular lower separation converts shared-ray geometry into a scaled
integer-label bound. -/
private theorem mss_angular_label_core
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData)
    {scale : Real} (hscale : 2 ≤ scale)
    {n n' nu nu' : Int}
    (hnu : nu ∈ D.angularIndices scale)
    (hnu' : nu' ∈ D.angularIndices scale)
    (hnpos : 0 < (n : Real)) {E : Real}
    (hray : ‖(n : Real) • D.directions scale nu -
      (n' : Real) • D.directions scale nu'‖ ≤ E)
    (hradial : |(n : Real) - (n' : Real)| ≤ E) :
    H.spacingLower * ((nu - nu').natAbs : Real) *
        scale ^ (-(1 / 2 : Real)) * (n : Real) ≤ 2 * E := by
  rcases H.geometry scale hscale with
    ⟨_, _, hspacingLower, _, _, _, hdata⟩
  have hunit : ‖D.directions scale nu'‖ = 1 := (hdata nu' hnu').1
  have hspacing := ((hdata nu hnu).2.2 nu' hnu').1
  have hangle : (n : Real) *
      ‖D.directions scale nu - D.directions scale nu'‖ ≤ 2 * E := by
    have hsplit : (n : Real) •
        (D.directions scale nu - D.directions scale nu') =
        ((n : Real) • D.directions scale nu -
          (n' : Real) • D.directions scale nu') +
        ((n' : Real) - (n : Real)) • D.directions scale nu' := by
      rw [smul_sub, sub_smul]
      module
    calc
      (n : Real) * ‖D.directions scale nu - D.directions scale nu'‖ =
          ‖(n : Real) •
            (D.directions scale nu - D.directions scale nu')‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hnpos]
      _ = ‖((n : Real) • D.directions scale nu -
          (n' : Real) • D.directions scale nu') +
          ((n' : Real) - (n : Real)) • D.directions scale nu'‖ := by
          rw [hsplit]
      _ ≤ ‖(n : Real) • D.directions scale nu -
          (n' : Real) • D.directions scale nu'‖ +
          ‖((n' : Real) - (n : Real)) • D.directions scale nu'‖ :=
          norm_add_le _ _
      _ = ‖(n : Real) • D.directions scale nu -
          (n' : Real) • D.directions scale nu'‖ +
          |(n : Real) - (n' : Real)| := by
          rw [norm_smul, Real.norm_eq_abs, hunit, mul_one, abs_sub_comm]
      _ ≤ E + E := add_le_add hray hradial
      _ = 2 * E := by ring
  calc
    H.spacingLower * ((nu - nu').natAbs : Real) *
        scale ^ (-(1 / 2 : Real)) * (n : Real) =
      (n : Real) * (H.spacingLower * ((nu - nu').natAbs : Real) *
        scale ^ (-(1 / 2 : Real))) := by ring
    _ ≤ (n : Real) * ‖D.directions scale nu -
        D.directions scale nu'‖ :=
      mul_le_mul_of_nonneg_left hspacing hnpos.le
    _ ≤ 2 * E := hangle

/-- A scaled angular-label inequality becomes scale independent once the
radial label is a fixed positive fraction of `sqrt scale`. -/
private theorem mss_large_angular_label_bound
    {scale spacingLower E n k : Real}
    (hroot : 12 ≤ Real.sqrt scale)
    (hspacing : 0 < spacingLower)
    (hn : Real.sqrt scale / 4 ≤ n)
    (hcore : spacingLower * k * scale ^ (-(1 / 2 : Real)) * n ≤ 2 * E)
    (hk : 0 ≤ k) :
    k ≤ 8 * E / spacingLower := by
  have hsqrtPos : 0 < Real.sqrt scale := by linarith
  have hscalePos : 0 < scale := Real.sqrt_pos.mp hsqrtPos
  have hinv : scale ^ (-(1 / 2 : Real)) * Real.sqrt scale = 1 := by
    calc
      scale ^ (-(1 / 2 : Real)) * Real.sqrt scale =
          scale ^ (-(1 / 2 : Real)) * scale ^ (1 / 2 : Real) := by
            rw [← Real.sqrt_eq_rpow]
      _ = scale ^ ((-(1 / 2 : Real)) + (1 / 2 : Real)) :=
        (Real.rpow_add hscalePos _ _).symm
      _ = 1 := by norm_num
  have hfactor : 0 ≤ scale ^ (-(1 / 2 : Real)) :=
    Real.rpow_nonneg (le_of_lt hscalePos) _
  have hsk : 0 ≤ spacingLower * k := mul_nonneg hspacing.le hk
  have hrad : scale ^ (-(1 / 2 : Real)) * (Real.sqrt scale / 4) ≤
      scale ^ (-(1 / 2 : Real)) * n :=
    mul_le_mul_of_nonneg_left hn hfactor
  have hscaled : spacingLower * k * (scale ^ (-(1 / 2 : Real)) *
      (Real.sqrt scale / 4)) ≤
      spacingLower * k * scale ^ (-(1 / 2 : Real)) * n := by
    calc
      spacingLower * k * (scale ^ (-(1 / 2 : Real)) *
          (Real.sqrt scale / 4)) =
          (spacingLower * k) *
            (scale ^ (-(1 / 2 : Real)) * (Real.sqrt scale / 4)) := by ring
      _ ≤ (spacingLower * k) * (scale ^ (-(1 / 2 : Real)) * n) :=
        mul_le_mul_of_nonneg_left hrad hsk
      _ = spacingLower * k * scale ^ (-(1 / 2 : Real)) * n := by ring
  have hquarter : spacingLower * k / 4 ≤ 2 * E := by
    calc
      spacingLower * k / 4 = spacingLower * k *
          (scale ^ (-(1 / 2 : Real)) * (Real.sqrt scale / 4)) := by
            rw [show scale ^ (-(1 / 2 : Real)) * (Real.sqrt scale / 4) = 1 / 4 by
              calc
                scale ^ (-(1 / 2 : Real)) * (Real.sqrt scale / 4) =
                    (scale ^ (-(1 / 2 : Real)) * Real.sqrt scale) / 4 := by ring
                _ = 1 / 4 := by rw [hinv]]
            ring
      _ ≤ spacingLower * k * scale ^ (-(1 / 2 : Real)) * n := hscaled
      _ ≤ 2 * E := hcore
  have hproduct : spacingLower * k ≤ 8 * E := by
    nlinarith
  exact (le_div_iff₀ hspacing).mpr (by simpa [mul_comm] using hproduct)

/-- The preceding normalization applied to fine angular sector data. -/
private theorem mss_large_angular_label_bound_of_core
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData)
    {scale : Real} (hscale : 2 ≤ scale) (hlarge : 12 ≤ Real.sqrt scale)
    {n nu nu' : Int} {E : Real}
    (hnlower : Real.sqrt scale / 4 ≤ (n : Real))
    (hcore : H.spacingLower * ((nu - nu').natAbs : Real) *
        scale ^ (-(1 / 2 : Real)) * (n : Real) ≤ 2 * E) :
    ((nu - nu').natAbs : Real) ≤ 8 * E / H.spacingLower := by
  rcases H.geometry scale hscale with
    ⟨_, _, hspacingLower, _, _, _, _⟩
  exact mss_large_angular_label_bound hlarge hspacingLower hnlower hcore
    (by positivity)

/-- On the bounded range of scales, the sector geometry alone gives a
uniform angular-label bound. -/
private theorem mss_small_angular_label_bound
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData)
    {scale : Real} (hscale : 2 ≤ scale) (hsmall : Real.sqrt scale < 12)
    {nu nu' : Int} (hnu : nu ∈ D.angularIndices scale)
    (hnu' : nu' ∈ D.angularIndices scale) :
    (nu - nu').natAbs ≤ ⌈6 / H.spacingLower⌉₊ := by
  have hscale_pos : 0 < scale := by linarith
  have hlabel := angularSeparation_label_bound_of_geometry hscale_pos
    (H.geometry scale hscale) hnu hnu'
  rcases H.geometry scale hscale with
    ⟨hsector_pos, hsector_upper, hspacing_pos, hspacing_upper, center,
      hcenter, hdata⟩
  have hbound : ((nu - nu').natAbs : Real) ≤ 6 / H.spacingLower := by
    calc
      ((nu - nu').natAbs : Real) ≤
          (2 * H.sectorRadius / H.spacingLower) * Real.sqrt scale := hlabel
      _ ≤ (2 * H.sectorRadius / H.spacingLower) * 12 := by
        gcongr
      _ ≤ 6 / H.spacingLower := by
        have hnum : 2 * H.sectorRadius * 12 ≤ 6 := by
          nlinarith
        calc
          (2 * H.sectorRadius / H.spacingLower) * 12 =
              (2 * H.sectorRadius * 12) / H.spacingLower := by ring
          _ ≤ 6 / H.spacingLower :=
            div_le_div_of_nonneg_right hnum hspacing_pos.le
  have hceil : (6 / H.spacingLower) ≤
      (⌈6 / H.spacingLower⌉₊ : Real) := Nat.le_ceil _
  have hreal : ((nu - nu').natAbs : Real) ≤
      (⌈6 / H.spacingLower⌉₊ : Real) := hbound.trans hceil
  exact_mod_cast hreal

/-- An integer product box around one radial--angular anchor. -/
private noncomputable def mssFiberBox (anchor : Int × Int) (A B : Nat) :
    Finset (Int × Int) :=
  Finset.Icc (anchor.1 - (A : Int)) (anchor.1 + (A : Int)) ×ˢ
    Finset.Icc (anchor.2 - (B : Int)) (anchor.2 + (B : Int))

private theorem mssFiberBox_card (anchor : Int × Int) (A B : Nat) :
    (mssFiberBox anchor A B).card = (2 * A + 1) * (2 * B + 1) := by
  simp only [mssFiberBox, Finset.card_product, Int.card_Icc]
  have hfirst :
      (anchor.1 + (A : Int) + 1 - (anchor.1 - (A : Int))).toNat =
        2 * A + 1 := by
    omega
  have hsecond :
      (anchor.2 + (B : Int) + 1 - (anchor.2 - (B : Int))).toNat =
        2 * B + 1 := by
    omega
  rw [hfirst, hsecond]

/-- Once every member of a fixed-cube assignment fiber lies in a uniform
integer box about an anchor, the fiber has the corresponding box cardinality. -/
private theorem mss_fiber_card_le_box
    {κ : Type*} [DecidableEq κ]
    (pieces : Finset (Int × Int)) (cubeSets : (Int × Int) → Finset κ)
    (cube : κ) (anchor : Int × Int) (A B : Nat)
    (hbound : ∀ assignment ∈ fineCubeAssignmentFiber pieces cubeSets cube,
      (assignment.1.1 - anchor.1).natAbs ≤ A ∧
        (assignment.1.2 - anchor.2).natAbs ≤ B) :
    (fineCubeAssignmentFiber pieces cubeSets cube).card ≤
      (2 * A + 1) * (2 * B + 1) := by
  classical
  let fiber := fineCubeAssignmentFiber pieces cubeSets cube
  have hmap : ∀ assignment ∈ fiber, assignment.1 ∈ mssFiberBox anchor A B := by
    intro assignment hassignment
    obtain ⟨hfirst, hsecond⟩ := hbound assignment hassignment
    simp only [mssFiberBox, Finset.mem_product, Finset.mem_Icc]
    constructor <;> constructor <;> omega
  have hinj : Set.InjOn
      (fun assignment : Sigma fun _ : Int × Int => κ => assignment.1)
      (↑fiber : Set (Sigma fun _ : Int × Int => κ)) := by
    intro a ha b hb hab
    rcases a with ⟨a, aVal⟩
    rcases b with ⟨b, bVal⟩
    change a = b at hab
    have haCube : aVal = cube := (Finset.mem_filter.mp ha).2
    have hbCube : bVal = cube := (Finset.mem_filter.mp hb).2
    subst b
    simp only [haCube, hbCube]
  calc
    fiber.card ≤ (mssFiberBox anchor A B).card :=
      Finset.card_le_card_of_injOn
        (f := fun assignment : Sigma fun _ : Int × Int => κ => assignment.1)
        hmap hinj
    _ = (2 * A + 1) * (2 * B + 1) := mssFiberBox_card anchor A B

/-- Unpack the radial, angular, and cube-membership data carried by one
canonical fixed-cube assignment. -/
private theorem mssCanonicalCube_fiber_assignment_data
    (D : MSSWavefrontKernelData) (scale : Real)
    (cube : Fin (mssCanonicalCubeCount D scale))
    {assignment : Sigma fun _ : Int × Int => Fin (mssCanonicalCubeCount D scale)}
    (hassignment : assignment ∈ fineCubeAssignmentFiber
      (mssFinePieceIndices D scale)
      (fun piece => mssCanonicalCubeSets D scale piece.1 piece.2) cube) :
    assignment.1.1 ∈ relevantRadialIndexEnumeration scale ∧
      assignment.1.2 ∈ D.angularIndices scale ∧
      assignment.2 = cube ∧
      cube ∈ mssCanonicalCubeSets D scale assignment.1.1 assignment.1.2 := by
  have hfilter := Finset.mem_filter.mp hassignment
  have hpiececube : assignment.1 ∈ mssFinePieceIndices D scale ∧
      assignment.2 ∈ mssCanonicalCubeSets D scale assignment.1.1 assignment.1.2 := by
    simpa only [fineCubeAssignments, Finset.mem_sigma] using hfilter.1
  have hpiece : assignment.1.1 ∈ relevantRadialIndexEnumeration scale ∧
      assignment.1.2 ∈ D.angularIndices scale := by
    simpa [mssFinePieceIndices] using hpiececube.1
  refine ⟨hpiece.1, hpiece.2, hfilter.2, ?_⟩
  simpa only [hfilter.2] using hpiececube.2

/-- A uniform coordinatewise label bound inside each fixed-cube fiber gives
the required reverse-incidence cardinality bound. -/
private theorem mss_reverse_overlap_of_bounded_difference
    {κ : Type*} [DecidableEq κ]
    (pieces : Finset (Int × Int)) (cubeSets : (Int × Int) → Finset κ)
    (A B : Nat)
    (hbound : ∀ (cube : κ) (anchor assignment : Sigma fun _ : Int × Int => κ),
      anchor ∈ fineCubeAssignmentFiber pieces cubeSets cube →
      assignment ∈ fineCubeAssignmentFiber pieces cubeSets cube →
      (assignment.1.1 - anchor.1.1).natAbs ≤ A ∧
        (assignment.1.2 - anchor.1.2).natAbs ≤ B) :
    HasFiniteFineCubeReverseOverlap pieces cubeSets ((2 * A + 1) * (2 * B + 1)) := by
  classical
  intro cube hcube
  let fiber := fineCubeAssignmentFiber pieces cubeSets cube
  by_cases hnonempty : fiber.Nonempty
  · rcases hnonempty with ⟨anchor, hanchor⟩
    exact mss_fiber_card_le_box pieces cubeSets cube anchor.1 A B
      (by
        intro assignment hassignment
        exact hbound cube anchor assignment hanchor hassignment)
  · have hempty : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [fiber, hempty, Finset.card_empty]
    omega

/-- The canonical finite lattice has scale-uniform reverse cube overlap:
a cube can belong to only boundedly many separated radial--angular packets. -/
private theorem mssCanonicalCube_reverse_overlap_of_fineAngularData
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData) :
    ∃ R : Nat, ∀ scale : Real, 2 ≤ scale →
      HasFiniteFineCubeReverseOverlap (mssFinePieceIndices D scale)
        (fun piece => mssCanonicalCubeSets D scale piece.1 piece.2) R := by
  classical
  let E : Real := 4 * ((mssLocalLatticeRadius D : Real) + 1)
  let A : Nat := max ⌈E⌉₊ 30
  let B : Nat := max ⌈8 * E / H.spacingLower⌉₊ ⌈6 / H.spacingLower⌉₊
  refine ⟨(2 * A + 1) * (2 * B + 1), ?_⟩
  intro scale hscale
  refine mss_reverse_overlap_of_bounded_difference
    (mssFinePieceIndices D scale)
    (fun piece => mssCanonicalCubeSets D scale piece.1 piece.2) A B ?_
  intro cube anchor assignment hanchor hassignment
  obtain ⟨hn0, hnu0, _, hanchorCube⟩ :=
    mssCanonicalCube_fiber_assignment_data D scale cube hanchor
  obtain ⟨hn, hnu, _, hassignmentCube⟩ :=
    mssCanonicalCube_fiber_assignment_data D scale cube
      (assignment := assignment) hassignment
  have hray : ‖(assignment.1.1 : Real) • D.directions scale assignment.1.2 -
      (anchor.1.1 : Real) • D.directions scale anchor.1.2‖ ≤ E := by
    simpa only [E] using
      mssCanonicalCube_shared_ray_distance D hscale
        assignment.1.1 assignment.1.2 anchor.1.1 anchor.1.2
        hn hnu hn0 hnu0 cube hassignmentCube hanchorCube
  by_cases hlarge : 12 ≤ Real.sqrt scale
  · obtain ⟨hnlower, hnpos⟩ :=
      mss_large_relevant_radial_lower hn hlarge
    obtain ⟨hn0lower, hn0pos⟩ :=
      mss_large_relevant_radial_lower hn0 hlarge
    rcases H.geometry scale hscale with
      ⟨_, _, _, _, _, _, hgeometry⟩
    have hradial : |(assignment.1.1 : Real) - (anchor.1.1 : Real)| ≤ E :=
      mss_radial_distance_le_ray_distance hnpos.le hn0pos.le
        (hgeometry assignment.1.2 hnu).1 (hgeometry anchor.1.2 hnu0).1 |>.trans hray
    have hradialNat : (assignment.1.1 - anchor.1.1).natAbs ≤ ⌈E⌉₊ :=
      mss_natAbs_sub_le_ceil hradial
    have hcore := mss_angular_label_core D H hscale hnu hnu0 hnpos hray hradial
    have hangularReal : ((assignment.1.2 - anchor.1.2).natAbs : Real) ≤
        8 * E / H.spacingLower :=
      mss_large_angular_label_bound_of_core D H hscale hlarge hnlower hcore
    have hangularNat : (assignment.1.2 - anchor.1.2).natAbs ≤
        ⌈8 * E / H.spacingLower⌉₊ := by
      have hceil : 8 * E / H.spacingLower ≤
          (⌈8 * E / H.spacingLower⌉₊ : Real) := Nat.le_ceil _
      exact_mod_cast hangularReal.trans hceil
    refine ⟨?_, ?_⟩
    · simpa only [A] using
        hradialNat.trans (Nat.le_max_left ⌈E⌉₊ 30)
    · simpa only [B] using
        hangularNat.trans
          (Nat.le_max_left ⌈8 * E / H.spacingLower⌉₊ ⌈6 / H.spacingLower⌉₊)
  · have hsmall : Real.sqrt scale < 12 := lt_of_not_ge hlarge
    have hradialNat : (assignment.1.1 - anchor.1.1).natAbs ≤ 30 :=
      mss_small_relevant_radial_difference hn hn0 hsmall
    have hangularNat : (assignment.1.2 - anchor.1.2).natAbs ≤
        ⌈6 / H.spacingLower⌉₊ :=
      mss_small_angular_label_bound D H hscale hsmall hnu hnu0
    refine ⟨?_, ?_⟩
    · simpa only [A] using hradialNat.trans (Nat.le_max_right ⌈E⌉₊ 30)
    · simpa only [B] using
        hangularNat.trans
          (Nat.le_max_right ⌈8 * E / H.spacingLower⌉₊ ⌈6 / H.spacingLower⌉₊)

/-- The canonical finite lattice supplies every cube-decomposition field
except the genuinely angular-geometric reverse-incidence count, which is
passed in explicitly here. -/
private noncomputable def mssCanonicalCubeDecomposition_of_reverseOverlap
    (D : MSSWavefrontKernelData)
    (hreverse : ∃ R : Nat, ∀ scale : Real, 2 ≤ scale →
      HasFiniteFineCubeReverseOverlap (mssFinePieceIndices D scale)
        (fun piece => mssCanonicalCubeSets D scale piece.1 piece.2) R) :
    MSSCubeDecomposition D where
  cubeWidth := 2
  cubeWidth_pos := by norm_num
  cubeCount := mssCanonicalCubeCount D
  center := mssCanonicalCubeCenter D
  cutoff := mssCanonicalCubeCutoff D
  analysisCutoff := mssCanonicalCubeAnalysisCutoff D
  cutoff_mul_analysisCutoff := mssCanonicalCube_cutoff_mul_analysisCutoff D
  cubeSets := mssCanonicalCubeSets D
  cube_support := by
    intro scale hscale k
    obtain ⟨_, hsupp⟩ := mssCanonicalCube_cube_support D hscale k
    refine ⟨by positivity, ?_⟩
    intro xi hxi
    have hinside := hsupp hxi
    rw [mem_frequencyCube_iff] at hinside
    rw [mem_frequencyCube_iff]
    intro i
    calc
      |xi i - mssCanonicalCubeCenter D scale k i| ≤ 1 * Real.sqrt scale :=
        hinside i
      _ ≤ 2 * Real.sqrt scale := by
        nlinarith [Real.sqrt_nonneg scale]
  reconstruct_spatialProfile := by
    intro scale hscale n hn nu hnu xi
    exact mssCanonicalCube_reconstruct_spatialProfile D hscale n nu hn hnu xi
  square_overlap := by
    intro scale hscale xi
    exact mssCanonicalCube_square_overlap D hscale xi
  cubes_per_packet := mssCanonicalCube_cubes_per_packet D
  reverse_overlap := hreverse
  center_ne_packet_ray := mssCanonicalCube_center_ne_packet_ray D
  cutoff_derivative_l1 := mssCanonicalCube_cutoff_derivative_l1_width_two D

/-- The separated fine angular geometry supplies the last reverse-incidence
field of the canonical finite MSS cube decomposition. -/
private noncomputable def mssCanonicalCubeDecomposition
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData) :
    MSSCubeDecomposition D :=
  mssCanonicalCubeDecomposition_of_reverseOverlap D
    (mssCanonicalCube_reverse_overlap_of_fineAngularData D H)

/-- The nominal width of the canonical cubes puts their reciprocal spatial
scale strictly inside the range of the light-ray maximal estimate. -/
private theorem mssCanonicalCubeDecomposition_hwidth
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData) :
    2 < (mssCanonicalCubeDecomposition D H).cubeWidth * Real.sqrt 2 := by
  change 2 < (2 : Real) * Real.sqrt 2
  nlinarith [Real.one_lt_sqrt_two]

/-- Exact fixed-lattice/prototype data for the enlarged analysis cutoffs of
an MSS cube decomposition.  The existing support, overlap, and derivative
fields alone do not provide this data; it is the precise structural bridge
from the completed equal-cube theorem to a concrete MSS cube family. -/
structure MSSAnalysisCubeLatticeData
    (D : MSSWavefrontKernelData) (Q : MSSCubeDecomposition D) where
  prototype : SchwartzMap (Euclidean 2) Complex
  spacing : Real
  spacing_pos : 0 < spacing
  grid : ∀ scale : Real, Fin (Q.cubeCount scale) ↪ (Fin 2 → Int)
  analysisCutoff_eq : ∀ (scale : Real) (hscale : 2 ≤ scale)
    (k : Fin (Q.cubeCount scale)),
      Q.analysisCutoff scale k =
        translatedDilatedSchwartzCutoff prototype
          (latticeCubeScale spacing scale • standardLatticePoint (grid scale k))
          (latticeCubeScale spacing scale)
          (latticeCubeScale_pos spacing_pos hscale).ne'

private theorem mssCanonicalCubeAnalysisCutoff_eq_lattice
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (k : Fin (mssCanonicalCubeCount D scale)) :
    mssCanonicalCubeAnalysisCutoff D scale k =
      translatedDilatedSchwartzCutoff mssLatticeAnalysisPrototype
        (latticeCubeScale 1 scale • standardLatticePoint
          (mssLatticeGridLabel (mssGlobalLatticeRadius D scale) k))
        (latticeCubeScale 1 scale)
        (latticeCubeScale_pos (by norm_num) hscale).ne' := by
  apply SchwartzMap.ext
  intro xi
  unfold mssCanonicalCubeAnalysisCutoff
  rw [mssCanonicalCubeCenter_eq_sqrt D hscale k]
  rw [translatedDilatedSchwartzCutoff_apply,
    translatedDilatedSchwartzCutoff_apply,
    mssCanonicalLatticeRadius_eq_sqrt hscale]
  simp only [latticeCubeScale, one_mul]

/-- The canonical enlarged cutoffs have the exact common-prototype lattice
form required by the proved fixed-lattice `L4` theorem. -/
private noncomputable def mssCanonicalCubeAnalysisLatticeData_of_reverseOverlap
    (D : MSSWavefrontKernelData)
    (hreverse : ∃ R : Nat, ∀ scale : Real, 2 ≤ scale →
      HasFiniteFineCubeReverseOverlap (mssFinePieceIndices D scale)
        (fun piece => mssCanonicalCubeSets D scale piece.1 piece.2) R) :
    MSSAnalysisCubeLatticeData D
      (mssCanonicalCubeDecomposition_of_reverseOverlap D hreverse) where
  prototype := mssLatticeAnalysisPrototype
  spacing := 1
  spacing_pos := by norm_num
  grid := fun scale =>
    ⟨mssLatticeGridLabel (mssGlobalLatticeRadius D scale),
      mssLatticeGridLabel_injective (mssGlobalLatticeRadius D scale)⟩
  analysisCutoff_eq := by
    intro scale hscale k
    change mssCanonicalCubeAnalysisCutoff D scale k =
      translatedDilatedSchwartzCutoff mssLatticeAnalysisPrototype
        (latticeCubeScale 1 scale • standardLatticePoint
          (mssLatticeGridLabel (mssGlobalLatticeRadius D scale) k))
        (latticeCubeScale 1 scale)
        (latticeCubeScale_pos (by norm_num) hscale).ne'
    exact mssCanonicalCubeAnalysisCutoff_eq_lattice D hscale k

/-- Exact analysis-lattice data for the fully constructed canonical cube
decomposition. -/
private noncomputable def mssCanonicalCubeAnalysisLatticeData
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData) :
    MSSAnalysisCubeLatticeData D (mssCanonicalCubeDecomposition D H) := by
  exact mssCanonicalCubeAnalysisLatticeData_of_reverseOverlap D
    (mssCanonicalCube_reverse_overlap_of_fineAngularData D H)

/-- The fourth moment of every finite Fourier-cube square function is
integrable on Schwartz input.  This is a finite algebraic fact, used only to
return the fixed-lattice lower-integral estimate to the real-integral form
of the MSS analysis-cube interface. -/
private theorem aux_integrable_fourth_fourierCubeSquareFunction
    {ι : Type*} (s : Finset ι) (m : ι → SchwartzMap (Euclidean 2) Complex)
    (f : SchwartzMap (Euclidean 2) Complex) :
    Integrable (fun x : Euclidean 2 =>
      fourierCubeSquareFunction s m f x ^ (4 : Nat)) volume := by
  classical
  let g : ι → Euclidean 2 → Complex := fun cube =>
    fourierCubeProjection (m cube) f
  have hproj (cube : ι) : fourierCubeProjection (m cube) f =
      (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz (m cube) f :
        Euclidean 2 → Complex) := by
    funext x
    exact (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz_apply (m cube) f x).symm
  have hg : ∀ cube ∈ s,
      Integrable (fun x : Euclidean 2 => ‖g cube x‖ ^ (4 : Nat)) volume := by
    intro cube hcube
    let P : SchwartzMap (Euclidean 2) Complex :=
      Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz (m cube) f
    have hP : Integrable (fun x : Euclidean 2 => ‖P x‖ ^ (4 : Nat)) volume :=
      (P.memLp 4 volume).integrable_norm_pow (by norm_num)
    rw [show (fun x : Euclidean 2 => ‖g cube x‖ ^ (4 : Nat)) =
        fun x => ‖P x‖ ^ (4 : Nat) by
      funext x
      dsimp only [g, P]
      rw [hproj cube]]
    exact hP
  have hsum : Integrable (fun x : Euclidean 2 =>
      ∑ cube ∈ s, ‖g cube x‖ ^ (4 : Nat)) volume :=
    integrable_finsetSum s hg
  have hmajor : Integrable (fun x : Euclidean 2 =>
      (s.card : Real) * ∑ cube ∈ s, ‖g cube x‖ ^ (4 : Nat)) volume :=
    hsum.const_mul _
  have hgcont (cube : ι) : Continuous (g cube) := by
    rw [show g cube = fourierCubeProjection (m cube) f by rfl, hproj cube]
    exact (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz (m cube) f).continuous
  have hmeas : AEStronglyMeasurable (fun x : Euclidean 2 =>
      Auto.LittlewoodPaley.finiteSquareEnergy s g x ^ (2 : Nat)) volume :=
    ((continuous_finsetSum s (fun cube hcube => (hgcont cube).norm.pow 2)).pow 2).aestronglyMeasurable
  have hrepr : (fun x : Euclidean 2 =>
      fourierCubeSquareFunction s m f x ^ (4 : Nat)) =
      fun x => Auto.LittlewoodPaley.finiteSquareEnergy s g x ^ (2 : Nat) := by
    funext x
    unfold fourierCubeSquareFunction Auto.LittlewoodPaley.finiteSquareEnergy
    have hnonneg : 0 ≤ ∑ cube ∈ s, ‖fourierCubeProjection (m cube) f x‖ ^ 2 :=
      Finset.sum_nonneg fun cube hcube => sq_nonneg _
    calc
      (Real.sqrt (∑ cube ∈ s, ‖fourierCubeProjection (m cube) f x‖ ^ 2)) ^ (4 : Nat) =
          (Real.sqrt (∑ cube ∈ s, ‖fourierCubeProjection (m cube) f x‖ ^ 2) ^ 2) ^ 2 := by
            ring
      _ = (∑ cube ∈ s, ‖fourierCubeProjection (m cube) f x‖ ^ 2) ^ 2 := by
        rw [Real.sq_sqrt hnonneg]
  rw [hrepr]
  apply hmajor.mono' hmeas
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Auto.LittlewoodPaley.finiteSquareEnergy_sq_le_card_mul_sum_norm_four
    s g x

/-- Reindexing an exact analysis-lattice model along its embedding preserves
the finite physical square function. -/
private theorem aux_lattice_analysisCube_squareFunction_reindex
    (D : MSSWavefrontKernelData) (Q : MSSCubeDecomposition D)
    (L : MSSAnalysisCubeLatticeData D Q)
    (scale : Real) (hscale : 2 ≤ scale)
    (s : Finset (Fin (Q.cubeCount scale)))
    (f : SchwartzMap (Euclidean 2) Complex) :
    fourierCubeSquareFunction s (Q.analysisCutoff scale) f =
      fourierCubeSquareFunction (s.map (L.grid scale))
        (fun k => translatedDilatedSchwartzCutoff L.prototype
          (latticeCubeScale L.spacing scale • standardLatticePoint k)
          (latticeCubeScale L.spacing scale)
          (latticeCubeScale_pos L.spacing_pos hscale).ne') f := by
  classical
  let R : Real := latticeCubeScale L.spacing scale
  have hR : 0 < R := latticeCubeScale_pos L.spacing_pos hscale
  have hcutoff (k : Fin (Q.cubeCount scale)) : Q.analysisCutoff scale k =
      translatedDilatedSchwartzCutoff L.prototype
        (R • standardLatticePoint (L.grid scale k)) R hR.ne' := by
    simpa only [R] using L.analysisCutoff_eq scale hscale k
  funext x
  unfold fourierCubeSquareFunction
  congr 1
  calc
    (∑ k ∈ s, ‖fourierCubeProjection (Q.analysisCutoff scale k) f x‖ ^ 2) =
        ∑ k ∈ s, ‖fourierCubeProjection
          (translatedDilatedSchwartzCutoff L.prototype
            (R • standardLatticePoint (L.grid scale k)) R hR.ne') f x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcutoff k]
    _ = ∑ k ∈ s.map (L.grid scale), ‖fourierCubeProjection
          (translatedDilatedSchwartzCutoff L.prototype
            (R • standardLatticePoint k) R hR.ne') f x‖ ^ 2 := by
      exact (Finset.sum_map s (L.grid scale) (fun k => ‖fourierCubeProjection
        (translatedDilatedSchwartzCutoff L.prototype
          (R • standardLatticePoint k) R hR.ne') f x‖ ^ 2)).symm

/-- The public fixed-lattice theorem transferred to an exact lattice model
of the MSS enlarged analysis cutoffs. -/
private theorem aux_lattice_analysisCube_lintegral_four
    (D : MSSWavefrontKernelData) (Q : MSSCubeDecomposition D)
    (L : MSSAnalysisCubeLatticeData D Q) :
    ∃ A : Real, 0 ≤ A ∧ ∀ scale : Real, 2 ≤ scale →
      ∀ (s : Finset (Fin (Q.cubeCount scale)))
      (f : SchwartzMap (Euclidean 2) Complex),
      (∫⁻ x : Euclidean 2,
        ENNReal.ofReal
          (fourierCubeSquareFunction s (Q.analysisCutoff scale) f x ^ (4 : Nat))) ≤
        (ENNReal.ofReal A) ^ (2 : Nat) *
          (∫⁻ v : Euclidean 2,
            ENNReal.ofReal ‖(FourierTransform.fourierInv L.prototype) v‖) ^ (2 : Nat) *
            ∫⁻ x : Euclidean 2, ENNReal.ofReal (‖f x‖ ^ (4 : Nat)) := by
  obtain ⟨A, hA, hcore⟩ :=
    latticeFourierCubeSquareFunction_lintegral_four L.prototype
  refine ⟨A, hA, ?_⟩
  intro scale hscale s f
  let R : Real := latticeCubeScale L.spacing scale
  have hR : 0 < R := latticeCubeScale_pos L.spacing_pos hscale
  rw [aux_lattice_analysisCube_squareFunction_reindex D Q L scale hscale s f]
  simpa only [R] using hcore f R hR (s.map (L.grid scale))

/-- Exact one-prototype lattice data for the enlarged MSS analysis cutoffs
proves the uniform finite-family `L⁴` Fourier-cube square-function bound.
This is a genuine application of the fixed-lattice theorem, not a consequence
of the weaker support/overlap/derivative record alone. -/
theorem uniformScaleMSSAnalysisCubeSquareFunctionL4_of_lattice
    (D : MSSWavefrontKernelData) (Q : MSSCubeDecomposition D)
    (L : MSSAnalysisCubeLatticeData D Q) :
    uniformScaleMSSAnalysisCubeSquareFunctionL4 D Q := by
  obtain ⟨A, hA, hcore⟩ := aux_lattice_analysisCube_lintegral_four D Q L
  let I : Real := ∫ v : Euclidean 2,
    ‖(FourierTransform.fourierInv L.prototype) v‖
  have hIint : Integrable (fun v : Euclidean 2 =>
      ‖(FourierTransform.fourierInv L.prototype) v‖) volume :=
    (FourierTransform.fourierInv L.prototype).integrable.norm
  have hI : 0 ≤ I := by
    dsimp only [I]
    exact integral_nonneg fun _ => norm_nonneg _
  let B : Real := (A * I) ^ (2 : Nat) + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro scale hscale s f
  have hSint := aux_integrable_fourth_fourierCubeSquareFunction
    s (Q.analysisCutoff scale) f
  have hSnonneg : ∀ᵐ x : Euclidean 2 ∂volume,
      0 ≤ fourierCubeSquareFunction s (Q.analysisCutoff scale) f x ^ (4 : Nat) :=
    Filter.Eventually.of_forall fun _ => pow_nonneg
      (fourierCubeSquareFunction_nonneg s (Q.analysisCutoff scale) f _) _
  have hfint : Integrable (fun x : Euclidean 2 => ‖f x‖ ^ (4 : Nat)) volume :=
    (f.memLp 4 volume).integrable_norm_pow (by norm_num)
  have hfnonneg : ∀ᵐ x : Euclidean 2 ∂volume, 0 ≤ ‖f x‖ ^ (4 : Nat) :=
    Filter.Eventually.of_forall fun _ => pow_nonneg (norm_nonneg _) _
  have hIeq : ENNReal.ofReal I =
      ∫⁻ v : Euclidean 2,
        ENNReal.ofReal ‖(FourierTransform.fourierInv L.prototype) v‖ := by
    dsimp only [I]
    exact ofReal_integral_eq_lintegral_ofReal hIint
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  have hSeq : ENNReal.ofReal
      (∫ x : Euclidean 2,
        fourierCubeSquareFunction s (Q.analysisCutoff scale) f x ^ (4 : Nat)) =
      ∫⁻ x : Euclidean 2,
        ENNReal.ofReal
          (fourierCubeSquareFunction s (Q.analysisCutoff scale) f x ^ (4 : Nat)) :=
    ofReal_integral_eq_lintegral_ofReal hSint hSnonneg
  have hfeq : ENNReal.ofReal (∫ x : Euclidean 2, ‖f x‖ ^ (4 : Nat)) =
      ∫⁻ x : Euclidean 2, ENNReal.ofReal (‖f x‖ ^ (4 : Nat)) :=
    ofReal_integral_eq_lintegral_ofReal hfint hfnonneg
  have hraw := hcore scale hscale s f
  rw [← hSeq, ← hIeq, ← hfeq] at hraw
  have hright : 0 ≤ (A * I) ^ (2 : Nat) *
      ∫ x : Euclidean 2, ‖f x‖ ^ (4 : Nat) := by
    exact mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
  have hconvert : ENNReal.ofReal
      ((A * I) ^ (2 : Nat) * ∫ x : Euclidean 2, ‖f x‖ ^ (4 : Nat)) =
      (ENNReal.ofReal A) ^ (2 : Nat) * (ENNReal.ofReal I) ^ (2 : Nat) *
        ENNReal.ofReal (∫ x : Euclidean 2, ‖f x‖ ^ (4 : Nat)) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (mul_nonneg hA hI),
      ENNReal.ofReal_mul hA]
    ring
  have hbase :
      (∫ x : Euclidean 2,
        fourierCubeSquareFunction s (Q.analysisCutoff scale) f x ^ (4 : Nat)) ≤
        (A * I) ^ (2 : Nat) * ∫ x : Euclidean 2, ‖f x‖ ^ (4 : Nat) := by
    apply (ENNReal.ofReal_le_ofReal_iff hright).mp
    rw [hconvert]
    exact hraw
  have hf : 0 ≤ ∫ x : Euclidean 2, ‖f x‖ ^ (4 : Nat) :=
    integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  calc
    (∫ x : Euclidean 2,
      fourierCubeSquareFunction s (Q.analysisCutoff scale) f x ^ (4 : Nat)) ≤
        (A * I) ^ (2 : Nat) * ∫ x : Euclidean 2, ‖f x‖ ^ (4 : Nat) := hbase
    _ ≤ ((A * I) ^ (2 : Nat) + 1) * ∫ x : Euclidean 2, ‖f x‖ ^ (4 : Nat) := by
      nlinarith [hf]
    _ = B * ∫ x : Euclidean 2, ‖f x‖ ^ (4 : Nat) := by rfl

/-- The actual canonical MSS cube family therefore satisfies the uniform
finite-family analysis-cube fourth-moment square-function estimate. -/
private theorem mssCanonicalCube_uniformAnalysisL4
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData) :
    uniformScaleMSSAnalysisCubeSquareFunctionL4 D
      (mssCanonicalCubeDecomposition D H) :=
  uniformScaleMSSAnalysisCubeSquareFunctionL4_of_lattice D
    (mssCanonicalCubeDecomposition D H)
    (mssCanonicalCubeAnalysisLatticeData D H)

/-- Source-kernel version of the preceding frequency-translation formula. -/
private theorem aux_fourierCubeSourceKernel_translate
    (φ : SchwartzMap (Euclidean 2) Complex)
    (a x y : Euclidean 2) :
    fourierCubeSourceKernel (translatedDilatedSchwartzCutoff φ a 1 one_ne_zero) x y =
      SMul.smul (Real.fourierChar (inner ℝ a (x - y)))
        (fourierCubeSourceKernel φ x y) := by
  unfold fourierCubeSourceKernel
  exact aux_fourierCubeKernel_translate φ a (x - y)

/-- A unit-lattice translated cube projection is exactly the common physical
kernel multiplied by its lattice character. -/
private theorem aux_fourierCubeProjection_translate
    (φ f : SchwartzMap (Euclidean 2) Complex)
    (a x : Euclidean 2) :
    fourierCubeProjection (translatedDilatedSchwartzCutoff φ a 1 one_ne_zero) f x =
      ∫ y : Euclidean 2,
        (SMul.smul (Real.fourierChar (inner ℝ a (x - y)))
          (fourierCubeSourceKernel φ x y)) * f y := by
  rw [fourierCubeProjection_apply, fourierCubeProjection_eq_sourceKernel]
  apply integral_congr_ae
  filter_upwards with y
  rw [aux_fourierCubeSourceKernel_translate]

/-- Uniform natural-scale symbol bounds for the actual fine angular/radial
packet profiles.  After rescaling a packet to a cube of side `sqrt scale`,
every derivative has a scale-independent `L¹` bound.  This is the quantitative
fixed-smooth-cutoff condition used by the MSS fine-square argument; merely
knowing that each individual profile is Schwartz permits scale-dependent
chirps and is not sufficient. -/
structure MSSFineSpatialProfileUniformRegularity
    (D : MSSWavefrontKernelData) : Prop where
  derivative_l1 : ∀ r : Nat, ∃ A : Real, 0 ≤ A ∧
    ∀ (scale : Real) (n nu : Int), 2 ≤ scale →
      n ∈ relevantRadialIndexEnumeration scale →
      nu ∈ D.angularIndices scale →
      (∫ xi : Euclidean 2,
        ‖iteratedFDeriv Real r
          (D.spatialProfile scale n nu : Euclidean 2 → Complex) xi‖) ≤
        A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ r

/-- Uniform natural-scale profile regularity supplies the older polynomial
regularity interface with the scale exponent fixed to one.  This is a direct
normalization consequence, not a localization or square-function estimate. -/
def MSSFineSpatialProfileUniformRegularity.toPolynomialRegularity
    {D : MSSWavefrontKernelData}
    (huniform : MSSFineSpatialProfileUniformRegularity D) :
    MSSWavefrontSpatialProfilePolynomialRegularity D := by
  refine
    { spatialExponent := fun _ => 1
      derivative_l1 := ?_ }
  intro r
  obtain ⟨A, hA, hderivative⟩ := huniform.derivative_l1 r
  refine ⟨A, hA, ?_⟩
  intro scale n nu hscale hn hnu
  have hsqrtOne : 1 ≤ Real.sqrt scale :=
    Real.one_le_sqrt.mpr (by linarith)
  have hinvNonneg : 0 ≤ (Real.sqrt scale)⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hinvLeOne : (Real.sqrt scale)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hsqrtOne
  have hinvPow : ((Real.sqrt scale)⁻¹) ^ r ≤ 1 :=
    pow_le_one₀ hinvNonneg hinvLeOne
  calc
    (∫ xi : Euclidean 2,
        ‖iteratedFDeriv Real r
          (D.spatialProfile scale n nu : Euclidean 2 → Complex) xi‖) ≤
        A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ r :=
      hderivative scale n nu hscale hn hnu
    _ ≤ A * (Real.sqrt scale) ^ 2 * 1 := by
      exact mul_le_mul_of_nonneg_left hinvPow
        (mul_nonneg hA (sq_nonneg _))
    _ = A * scale ^ (1 : Nat) := by
      rw [Real.sq_sqrt (by linarith : 0 ≤ scale)]
      ring

/-- The structured fine square-function target in the MSS blueprint.  The
angular data record the finite sector atlas and exact synthesis, the uniform
profile certificate is the fixed-smooth-cutoff condition at the natural
`sqrt scale` packet scale, and the time cutoff is supported in the fixed
light-ray slab used by the maximal estimate.  These are structural data, not
hidden kernel, cube-square-function, or maximal-function conclusions. -/
def mssFineSquareFunctionEstimate (D : MSSWavefrontKernelData)
    (_A : MSSFineAngularData D.toMSSWavefrontCutoffData)
    (_uniform : MSSFineSpatialProfileUniformRegularity D)
    (_hslab : D.HasLightRayTimeSlabSupport) : Prop :=
  ∀ η : Real, 0 < η → ∃ C : Real, 0 < C ∧
    ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
      eLpNorm (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
          (f : Euclidean 2 → Complex))
          (4 : ENNReal) volume ≤
        ENNReal.ofReal (C * scale ^ η) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume

/-- The literal fine-cube multiplier vanishes on the central ball removed by
the radial--time amplitude.  This permits the half-wave phase to be extended
smoothly through the origin when packaging the multiplier as a Schwartz map. -/
private theorem mssFineCubeSymbol_zero_near_zero
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    {scale : Real} (hscale : 2 ≤ scale) (n nu : Int)
    (cube : Fin (cubes.cubeCount scale)) (z : WaveSpaceTime) :
    ∀ xi : Euclidean 2, ‖xi‖ < scale / 2 →
      cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
        halfWaveMultiplier WaveSign.plus z.2 xi = 0 := by
  have hscale_pos : 0 < scale := by linarith
  intro xi hxi
  have hamp : D.radialTime.amplitude (scale⁻¹ • xi) = 0 := by
    by_contra hamp
    have hlow :=
      (D.radialTime.amplitude_support_annulus (scale⁻¹ • xi) hamp).1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale_pos)] at hlow
    have hmul : scale * (1 / 2 : Real) ≤ scale * (scale⁻¹ * ‖xi‖) :=
      (mul_le_mul_iff_of_pos_left hscale_pos).mpr hlow
    have hcancel : scale * (scale⁻¹ * ‖xi‖) = ‖xi‖ := by
      field_simp [hscale_pos.ne']
    have hlow' : scale / 2 ≤ ‖xi‖ := by
      calc
        scale / 2 = scale * (1 / 2 : Real) := by ring
        _ ≤ scale * (scale⁻¹ * ‖xi‖) := hmul
        _ = ‖xi‖ := hcancel
    linarith
  rw [D.spatialProfile_apply, hamp]
  simp

/-- Smoothness of the literal fine-cube multiplier, including the origin.
The only singular-looking factor is the half-wave phase, and the preceding
central-annulus vanishing handles that point. -/
private theorem mssFineCubeSymbol_contDiff
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    {scale : Real} (hscale : 2 ≤ scale) (n nu : Int)
    (cube : Fin (cubes.cubeCount scale)) (z : WaveSpaceTime) :
    ContDiff Real (⊤ : ℕ∞) (fun xi : Euclidean 2 =>
      cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
        halfWaveMultiplier WaveSign.plus z.2 xi) := by
  rw [contDiff_iff_contDiffAt]
  intro xi
  by_cases hxi : xi = 0
  · subst xi
    have hscale_pos : 0 < scale := by linarith
    refine (contDiffAt_const (c := (0 : Complex))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : Euclidean 2)
        (by linarith : 0 < scale / 2)] with eta heta
    have heta' : ‖eta‖ < scale / 2 := by
      simpa only [Metric.mem_ball, dist_zero_right] using heta
    exact mssFineCubeSymbol_zero_near_zero D cubes hscale n nu cube z eta heta'
  · exact ((cubes.cutoff scale cube).contDiffAt (⊤ : ℕ∞)).mul
      ((D.spatialProfile scale n nu).contDiffAt (⊤ : ℕ∞)) |>.mul
        (halfWaveMultiplier_contDiffAt_of_ne_zero WaveSign.plus z.2 hxi)

/-- Compactness of the literal fine-cube multiplier is inherited from the
compact radial--time amplitude. -/
private theorem mssFineCubeSymbol_hasCompactSupport
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    {scale : Real} (hscale : 2 ≤ scale) (n nu : Int)
    (cube : Fin (cubes.cubeCount scale)) (z : WaveSpaceTime) :
    HasCompactSupport (fun xi : Euclidean 2 =>
      cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
        halfWaveMultiplier WaveSign.plus z.2 xi) := by
  have hscale_pos : 0 < scale := by linarith
  have hampcompact : HasCompactSupport (fun xi : Euclidean 2 =>
      D.radialTime.amplitude (scale⁻¹ • xi)) :=
    D.radialTime.amplitude_compact.comp_smul (inv_ne_zero hscale_pos.ne')
  refine hampcompact.mono ?_
  intro xi hxi
  change D.radialTime.amplitude (scale⁻¹ • xi) ≠ 0
  change cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
    halfWaveMultiplier WaveSign.plus z.2 xi ≠ 0 at hxi
  rcases mul_ne_zero_iff.mp hxi with ⟨hleft, _⟩
  rcases mul_ne_zero_iff.mp hleft with ⟨_, hprofile⟩
  rw [D.spatialProfile_apply] at hprofile
  rcases mul_ne_zero_iff.mp hprofile with ⟨_, hradial⟩
  exact (mul_ne_zero_iff.mp hradial).1

/-- The actual fine-cube multiplier is a compactly supported smooth symbol.
This records only its automatic Schwartz realization, not any uniform
seminorm, ray-decay, or square-function bound. -/
noncomputable def mssFineCubeSchwartzSymbol
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    {scale : Real} (hscale : 2 ≤ scale) (n nu : Int)
    (cube : Fin (cubes.cubeCount scale)) (z : WaveSpaceTime) :
    SchwartzMap (Euclidean 2) Complex :=
  (mssFineCubeSymbol_hasCompactSupport D cubes hscale n nu cube z).toSchwartzMap
    (mssFineCubeSymbol_contDiff D cubes hscale n nu cube z)

theorem mssFineCubeSchwartzSymbol_apply
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    {scale : Real} (hscale : 2 ≤ scale) (n nu : Int)
    (cube : Fin (cubes.cubeCount scale)) (z : WaveSpaceTime) (xi : Euclidean 2) :
    mssFineCubeSchwartzSymbol D cubes hscale n nu cube z xi =
      cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
        halfWaveMultiplier WaveSign.plus z.2 xi := rfl

/-- The Schwartz realization of a literal fine-cube multiplier retains the
compact support inherited from the radial--time amplitude. -/
theorem hasCompactSupport_mssFineCubeSchwartzSymbol
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    {scale : Real} (hscale : 2 ≤ scale) (n nu : Int)
    (cube : Fin (cubes.cubeCount scale)) (z : WaveSpaceTime) :
    HasCompactSupport
      (mssFineCubeSchwartzSymbol D cubes hscale n nu cube z :
        Euclidean 2 → Complex) := by
  change HasCompactSupport (fun xi : Euclidean 2 =>
    cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
      halfWaveMultiplier WaveSign.plus z.2 xi)
  exact mssFineCubeSymbol_hasCompactSupport D cubes hscale n nu cube z

/-- Modulating a compact frequency symbol by the plane wave that removes a
candidate light-ray translation.  This generic helper is kept private; the
public specialization below is the literal MSS residual symbol. -/
private noncomputable def mssFinePlaneWaveResidualSymbol
    (q : SchwartzMap (Euclidean 2) Complex)
    (hqcompact : HasCompactSupport (q : Euclidean 2 → Complex))
    (t : Real) (omega : Euclidean 2) :
    SchwartzMap (Euclidean 2) Complex :=
  Auto.Spherical.Auxiliary.planeWaveModulatedCompactSchwartz (-(t • omega))
    (q : Euclidean 2 → Complex) hqcompact (q.smooth (⊤ : ℕ∞))

private theorem fourierInv_mssFinePlaneWaveResidualSymbol_shift
    (q : SchwartzMap (Euclidean 2) Complex)
    (hqcompact : HasCompactSupport (q : Euclidean 2 → Complex))
    (t : Real) (omega x : Euclidean 2) :
    FourierTransform.fourierInv
      (mssFinePlaneWaveResidualSymbol q hqcompact t omega : Euclidean 2 → Complex)
      (x + t • omega) =
      FourierTransform.fourierInv (q : Euclidean 2 → Complex) x := by
  unfold mssFinePlaneWaveResidualSymbol
  rw [Auto.Spherical.Auxiliary.fourierInv_planeWaveModulatedCompactSchwartz_eq_translate]
  simp only [add_neg_cancel_right]

private theorem fourierInv_eq_fourierCubeKernel_mssFinePlaneWaveResidualSymbol_shifted
    (q : SchwartzMap (Euclidean 2) Complex)
    (hqcompact : HasCompactSupport (q : Euclidean 2 → Complex))
    (t : Real) (omega x : Euclidean 2) :
    FourierTransform.fourierInv (q : Euclidean 2 → Complex) x =
      Auto.Spherical.Auxiliary.fourierCubeKernel
        (mssFinePlaneWaveResidualSymbol q hqcompact t omega) (x + t • omega) := by
  unfold Auto.Spherical.Auxiliary.fourierCubeKernel
  rw [SchwartzMap.fourierInv_coe]
  symm
  exact fourierInv_mssFinePlaneWaveResidualSymbol_shift q hqcompact t omega x

/-- The literal fine-cube multiplier after removing translation along its
assigned light ray.  Uniform residual seminorm estimates for this symbol are
exactly the remaining analytic input for light-ray localization. -/
noncomputable def mssFineCubeResidualSymbol
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    {scale : Real} (hscale : 2 ≤ scale) (n nu : Int)
    (cube : Fin (cubes.cubeCount scale)) (z : WaveSpaceTime) :
    SchwartzMap (Euclidean 2) Complex :=
  mssFinePlaneWaveResidualSymbol
    (mssFineCubeSchwartzSymbol D cubes hscale n nu cube z)
    (hasCompactSupport_mssFineCubeSchwartzSymbol D cubes hscale n nu cube z)
    z.2 (D.directions scale nu)

/-- After removing translation along its assigned ray, the literal fine-cube
symbol has exactly the angular phase mismatch as its oscillatory factor. -/
private theorem mssFineCubeResidualSymbol_apply_phaseMismatch
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    {scale : Real} (hscale : 2 ≤ scale) (n nu : Int)
    (cube : Fin (cubes.cubeCount scale)) (z : WaveSpaceTime) (xi : Euclidean 2) :
    mssFineCubeResidualSymbol D cubes hscale n nu cube z xi =
      Complex.exp
          (((2 * Real.pi * z.2 *
            angularDyadicRayPhaseMismatch WaveSign.plus
              (D.directions scale nu) xi : Real) : Complex) * Complex.I) *
        (cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi) := by
  rw [mssFineCubeResidualSymbol, mssFinePlaneWaveResidualSymbol,
    Auto.Spherical.Auxiliary.planeWaveModulatedCompactSchwartz_apply,
    mssFineCubeSchwartzSymbol_apply]
  simp only [Real.fourierChar_apply]
  rw [halfWaveMultiplier]
  rw [show
    Complex.exp (((2 * Real.pi * inner Real (-(z.2 • D.directions scale nu)) xi : Real) :
      Complex) * Complex.I) *
        (cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
          Complex.exp (((WaveSign.plus.toReal * (2 * Real.pi) * z.2 * ‖xi‖ : Real) :
            Complex) * Complex.I)) =
      (Complex.exp (((2 * Real.pi * inner Real (-(z.2 • D.directions scale nu)) xi : Real) :
          Complex) * Complex.I) *
        Complex.exp (((WaveSign.plus.toReal * (2 * Real.pi) * z.2 * ‖xi‖ : Real) :
          Complex) * Complex.I)) *
        (cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi) by ring]
  rw [← Complex.exp_add]
  congr 1
  simp [angularDyadicRayPhaseMismatch, inner_neg_left, inner_smul_left]
  ring_nf

/-- A nonzero literal fine profile remains in the fixed radial annulus of the
rescaled amplitude.  This separates the harmless support bookkeeping from
the later phase derivative estimates. -/
private theorem mssFineSpatialProfile_norm_bounds_of_ne_zero
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (xi : Euclidean 2)
    (hprofile : D.spatialProfile scale n nu xi ≠ 0) :
    scale / 2 ≤ ‖xi‖ ∧ ‖xi‖ ≤ 2 * scale := by
  have hscale_pos : 0 < scale := by linarith
  have hamp : D.radialTime.amplitude (scale⁻¹ • xi) ≠ 0 := by
    rw [D.spatialProfile_apply] at hprofile
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprofile).2).1
  have hannulus := D.radialTime.amplitude_support_annulus (scale⁻¹ • xi) hamp
  have hnormScale : ‖scale⁻¹ • xi‖ = scale⁻¹ * ‖xi‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale_pos)]
  rw [hnormScale] at hannulus
  have hcancel : scale * (scale⁻¹ * ‖xi‖) = ‖xi‖ := by
    field_simp [hscale_pos.ne']
  constructor
  · calc
      scale / 2 = scale * (1 / 2 : Real) := by ring
      _ ≤ scale * (scale⁻¹ * ‖xi‖) :=
        mul_le_mul_of_nonneg_left hannulus.1 hscale_pos.le
      _ = ‖xi‖ := hcancel
  · calc
      ‖xi‖ = scale * (scale⁻¹ * ‖xi‖) := hcancel.symm
      _ ≤ scale * 2 := mul_le_mul_of_nonneg_left hannulus.2 hscale_pos.le
      _ = 2 * scale := by ring

/-- The topological support of every literal fine profile stays in a closed
annular ray-sector container.  Unlike `angularSector` itself, this container
is closed at the origin; its positive radial lower bound still excludes the
origin on the relevant support. -/
private theorem mssFineSpatialProfile_tsupport_subset_closed_raySector
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (hnu : nu ∈ D.angularIndices scale) :
    tsupport (D.spatialProfile scale n nu : Euclidean 2 → Complex) ⊆
      {xi : Euclidean 2 |
        scale / 2 ≤ ‖xi‖ ∧ ‖xi‖ ≤ 2 * scale ∧
          ‖xi - ‖xi‖ • D.directions scale nu‖ ≤
            (D.angularConstant * scale ^ (-(1 / 2 : Real))) * ‖xi‖} := by
  let K : Set (Euclidean 2) :=
    {xi : Euclidean 2 |
      scale / 2 ≤ ‖xi‖ ∧ ‖xi‖ ≤ 2 * scale ∧
        ‖xi - ‖xi‖ • D.directions scale nu‖ ≤
          (D.angularConstant * scale ^ (-(1 / 2 : Real))) * ‖xi‖}
  have hKclosed : IsClosed K := by
    dsimp [K]
    exact (isClosed_le continuous_const continuous_norm).inter
      ((isClosed_le continuous_norm continuous_const).inter
        (isClosed_le
          (continuous_id.sub (continuous_norm.smul continuous_const)).norm
          (continuous_const.mul continuous_norm)))
  change closure (Function.support
    (D.spatialProfile scale n nu : Euclidean 2 → Complex)) ⊆ K
  apply closure_minimal ?_ hKclosed
  intro xi hprofile
  change D.spatialProfile scale n nu xi ≠ 0 at hprofile
  obtain ⟨hlow, hupp⟩ :=
    mssFineSpatialProfile_norm_bounds_of_ne_zero D hscale n nu xi hprofile
  have hchi : D.chi scale nu xi ≠ 0 := by
    rw [D.spatialProfile_apply] at hprofile
    exact (mul_ne_zero_iff.mp hprofile).1
  rcases D.chi_support scale nu hnu hchi with ⟨hxi0, hangular⟩
  have hnorm_pos : 0 < ‖xi‖ := norm_pos_iff.mpr hxi0
  have hnorm_ne : ‖xi‖ ≠ 0 := ne_of_gt hnorm_pos
  refine ⟨hlow, hupp, ?_⟩
  have hrewrite :
      xi - ‖xi‖ • D.directions scale nu =
        ‖xi‖ • ((‖xi‖)⁻¹ • xi - D.directions scale nu) := by
    symm
    calc
      ‖xi‖ • ((‖xi‖)⁻¹ • xi - D.directions scale nu) =
          (‖xi‖ * (‖xi‖)⁻¹) • xi - ‖xi‖ • D.directions scale nu := by
            rw [smul_sub, smul_smul]
      _ = xi - ‖xi‖ • D.directions scale nu := by
            rw [mul_inv_cancel₀ hnorm_ne, one_smul]
  rw [hrewrite, norm_smul, Real.norm_eq_abs, abs_of_pos hnorm_pos]
  calc
    ‖xi‖ * ‖(‖xi‖)⁻¹ • xi - D.directions scale nu‖ ≤
        ‖xi‖ * (D.angularConstant * scale ^ (-(1 / 2 : Real))) :=
      mul_le_mul_of_nonneg_left hangular hnorm_pos.le
    _ = (D.angularConstant * scale ^ (-(1 / 2 : Real))) * ‖xi‖ := by ring

/-- The first phase-mismatch derivative bound extends from nonzero profile
values to the support of every profile derivative.  The closed annular
ray-sector container is exactly what makes this extension legitimate. -/
private theorem aux_norm_fderiv_mssFinePhaseMismatch_plus_le_of_spatialProfile_tsupport
    (D : MSSWavefrontKernelData) (scale : Real) (n nu : Int)
    (hscale : 2 ≤ scale) (hnu : nu ∈ D.angularIndices scale) (xi : Euclidean 2)
    (hxi : xi ∈ tsupport (D.spatialProfile scale n nu : Euclidean 2 → Complex)) :
    ‖fderiv Real
        (angularDyadicRayPhaseMismatch WaveSign.plus (D.directions scale nu)) xi‖ ≤
      D.angularConstant * scale ^ (-(1 / 2 : Real)) := by
  have hcontainer :=
    mssFineSpatialProfile_tsupport_subset_closed_raySector D hscale n nu hnu hxi
  rcases hcontainer with ⟨hlow, _, hsector⟩
  have hscale_pos : 0 < scale := by linarith
  have hnorm_pos : 0 < ‖xi‖ := by
    nlinarith
  have hxi0 : xi ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hnorm_pos)
  have hrewrite :
      xi - ‖xi‖ • D.directions scale nu =
        ‖xi‖ • ((‖xi‖)⁻¹ • xi - D.directions scale nu) := by
    symm
    calc
      ‖xi‖ • ((‖xi‖)⁻¹ • xi - D.directions scale nu) =
          (‖xi‖ * (‖xi‖)⁻¹) • xi - ‖xi‖ • D.directions scale nu := by
            rw [smul_sub, smul_smul]
      _ = xi - ‖xi‖ • D.directions scale nu := by
            rw [mul_inv_cancel₀ (ne_of_gt hnorm_pos), one_smul]
  have hnormal :
      ‖(‖xi‖)⁻¹ • xi - D.directions scale nu‖ ≤
        D.angularConstant * scale ^ (-(1 / 2 : Real)) := by
    apply le_of_mul_le_mul_left ?_ hnorm_pos
    calc
      ‖xi‖ * ‖(‖xi‖)⁻¹ • xi - D.directions scale nu‖ =
          ‖xi - ‖xi‖ • D.directions scale nu‖ := by
            rw [hrewrite, norm_smul, Real.norm_eq_abs, abs_of_pos hnorm_pos]
      _ ≤ (D.angularConstant * scale ^ (-(1 / 2 : Real))) * ‖xi‖ := hsector
      _ = ‖xi‖ * (D.angularConstant * scale ^ (-(1 / 2 : Real))) := by ring
  rw [fderiv_angularDyadicRayPhaseMismatch WaveSign.plus
    (D.directions scale nu) xi hxi0]
  simp only [WaveSign.toReal, one_smul]
  have hrewriteSL :
      (‖xi‖)⁻¹ • innerSL Real xi - innerSL Real (D.directions scale nu) =
        innerSL Real ((‖xi‖)⁻¹ • xi - D.directions scale nu) := by
    ext v
    simp
  calc
    ‖(‖xi‖)⁻¹ • innerSL Real xi - innerSL Real (D.directions scale nu)‖ =
        ‖innerSL Real ((‖xi‖)⁻¹ • xi - D.directions scale nu)‖ := by
          rw [hrewriteSL]
    _ = ‖(‖xi‖)⁻¹ • xi - D.directions scale nu‖ :=
      innerSL_apply_norm (𝕜 := Real) _
    _ ≤ D.angularConstant * scale ^ (-(1 / 2 : Real)) := hnormal

/-- Higher phase-mismatch derivatives obey their natural radial scale on the
topological support of the fine profile, hence also on every profile-derivative
support used by the Leibniz expansion. -/
private theorem aux_exists_mssFinePhaseMismatch_higherDerivative_bound_of_spatialProfile_tsupport
    (r : Nat) (hr : 2 ≤ r) :
    ∃ A : Real, 0 ≤ A ∧ ∀ (D : MSSWavefrontKernelData)
      (scale : Real) (n nu : Int) (xi : Euclidean 2), 2 ≤ scale →
      nu ∈ D.angularIndices scale →
      xi ∈ tsupport (D.spatialProfile scale n nu : Euclidean 2 → Complex) →
      scale ^ (r - 1) *
        ‖iteratedFDeriv Real r
          (angularDyadicRayPhaseMismatch WaveSign.plus (D.directions scale nu)) xi‖ ≤ A := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_scaled_norm_iteratedFDeriv_bound 2 r (by omega : 1 ≤ r)
  refine ⟨A, hA, ?_⟩
  intro D scale n nu xi hscale hnu hxi
  rcases mssFineSpatialProfile_tsupport_subset_closed_raySector
    D hscale n nu hnu hxi with ⟨hlow, hupp, _⟩
  have hscale_pos : 0 < scale := by linarith
  have hxi0 : xi ≠ 0 := by
    intro hzero
    subst xi
    norm_num at hlow
    linarith
  rw [iteratedFDeriv_angularDyadicRayPhaseMismatch_plus_eq_norm_of_two_le
    hr (D.directions scale nu) xi hxi0]
  exact hbound scale xi hscale_pos hlow hupp

/-- The fixed real-to-imaginary linear isometry used to write a real phase
as the argument of a complex exponential. -/
private noncomputable def mssRealMulI : Real →ₗᵢ[Real] Complex where
  toLinearMap := (Complex.ofRealCLM.smulRight Complex.I).toLinearMap
  norm_map' := by
    intro r
    simp

/-- All real derivatives of `exp(i s)` are uniformly bounded. -/
private lemma aux_norm_iteratedFDeriv_exp_ofReal_mul_I_le_two
    (r : Nat) (s : Real) :
    ‖iteratedFDeriv Real r
      (fun u : Real => Complex.exp (((u : Complex) * Complex.I))) s‖ ≤ 2 := by
  let c : Real → Complex := fun u => (Real.cos u : Complex)
  let q : Real → Complex := fun u => (Real.sin u : Complex) * Complex.I
  have hcos : ContDiff Real (r : ℕ∞) Real.cos := Real.contDiff_cos
  have hsin : ContDiff Real (r : ℕ∞) Real.sin := Real.contDiff_sin
  have hfun : (fun u : Real => Complex.exp (((u : Complex) * Complex.I))) = c + q := by
    funext u
    simp [c, q, Complex.exp_mul_I]
  have hc : c = Complex.ofRealLI ∘ Real.cos := by rfl
  have hq : q = mssRealMulI ∘ Real.sin := by rfl
  rw [hfun, hc, hq]
  rw [iteratedFDeriv_add (Complex.ofRealLI.contDiff.comp hcos)
    (mssRealMulI.contDiff.comp hsin)]
  calc
    ‖iteratedFDeriv Real r c s + iteratedFDeriv Real r q s‖ ≤
        ‖iteratedFDeriv Real r c s‖ + ‖iteratedFDeriv Real r q s‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by
      apply add_le_add
      · rw [hc, Complex.ofRealLI.norm_iteratedFDeriv_comp_left]
        · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
          simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_cos_le_one r s
        · exact hcos.contDiffAt
        · exact_mod_cast le_rfl
      · rw [hq, mssRealMulI.norm_iteratedFDeriv_comp_left]
        · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
          simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_sin_le_one r s
        · exact hsin.contDiffAt
        · exact_mod_cast le_rfl
    _ = 2 := by norm_num

/-- A finite-order composition estimate on an open set, phrased for ordinary
derivatives rather than within-derivatives. -/
private lemma aux_norm_iteratedFDeriv_comp_le_on_open
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (s : Set E) (hs : IsOpen s) (f : E → F) (g : F → G)
    (N r : Nat) (hf : ContDiffOn Real (N : ℕ∞) f s)
    (hg : ContDiff Real (N : ℕ∞) g) {x : E} (hx : x ∈ s)
    (hrN : r ≤ N)
    {C B : Real}
    (hC : ∀ i, i ≤ r → ‖iteratedFDeriv Real i g (f x)‖ ≤ C)
    (hB : ∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDeriv Real i f x‖ ≤ B ^ i) :
    ‖iteratedFDeriv Real r (g ∘ f) x‖ ≤ (r.factorial : Real) * C * B ^ r := by
  have hr : (r : WithTop ℕ∞) ≤ (↑(N : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hrN
  have hcomp := norm_iteratedFDerivWithin_comp_le
    (s := s) (t := Set.univ) (n := r) (N := (N : ℕ∞))
    hg.contDiffOn hf
    hr
    uniqueDiffOn_univ hs.uniqueDiffOn (by simp) hx
    (C := C) (D := B)
    (by
      intro i hi
      simpa only [iteratedFDerivWithin_univ] using hC i hi)
    (by
      intro i hi1 hir
      rw [iteratedFDerivWithin_of_isOpen i hs hx]
      exact hB i hi1 hir)
  rw [iteratedFDerivWithin_of_isOpen r hs hx] at hcomp
  exact hcomp

/-- The Leibniz estimate on an open set, returned in terms of ordinary
iterated derivatives. -/
private lemma aux_norm_iteratedFDeriv_mul_le_on_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (s : Set E) (hs : IsOpen s) (f g : E → Complex)
    (N r : Nat) (hf : ContDiffOn Real (N : ℕ∞) f s)
    (hg : ContDiffOn Real (N : ℕ∞) g s) {x : E} (hx : x ∈ s)
    (hr : r ≤ N) :
    ‖iteratedFDeriv Real r (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (r + 1), (r.choose i : Real) *
        ‖iteratedFDeriv Real i f x‖ * ‖iteratedFDeriv Real (r - i) g x‖ := by
  have hr' : (r : WithTop ℕ∞) ≤ (↑(N : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hr
  have h := norm_iteratedFDerivWithin_mul_le hf hg hs.uniqueDiffOn hx hr'
  rw [iteratedFDerivWithin_of_isOpen r hs hx] at h
  calc
    ‖iteratedFDeriv Real r (fun y => f y * g y) x‖ ≤
        ∑ i ∈ Finset.range (r + 1), (r.choose i : Real) *
          ‖iteratedFDerivWithin Real i f s x‖ *
            ‖iteratedFDerivWithin Real (r - i) g s x‖ := h
    _ = ∑ i ∈ Finset.range (r + 1), (r.choose i : Real) *
          ‖iteratedFDeriv Real i f x‖ * ‖iteratedFDeriv Real (r - i) g x‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [iteratedFDerivWithin_of_isOpen i hs hx,
        iteratedFDerivWithin_of_isOpen (r - i) hs hx]

/-- The angular aperture's negative half-power is exactly the reciprocal
natural packet scale. -/
private theorem mss_rpow_neg_half_eq_sqrt_inv {scale : Real} (hscale : 0 < scale) :
    scale ^ (-(1 / 2 : Real)) = (Real.sqrt scale)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hscale.le]

/-- The time-scaled phase mismatch left after translation along a fine packet
ray. -/
private noncomputable def mssFineTimeRayPhaseMismatch
    (t : Real) (direction : Euclidean 2) : Euclidean 2 → Real := fun xi =>
  (2 * Real.pi * t) • angularDyadicRayPhaseMismatch WaveSign.plus direction xi

private lemma mssFineTimeRayPhaseMismatch_contDiffOn
    (N : Nat) (t : Real) (direction : Euclidean 2) :
    ContDiffOn Real (N : ℕ∞) (mssFineTimeRayPhaseMismatch t direction)
      {xi : Euclidean 2 | xi ≠ 0} := by
  intro xi hxi
  have hnorm : ContDiffAt Real (N : ℕ∞) (fun eta : Euclidean 2 => ‖eta‖) xi :=
    contDiffAt_norm Real hxi
  have hinner : ContDiffAt Real (N : ℕ∞)
      (innerSL Real direction : Euclidean 2 → Real) xi :=
    (innerSL Real direction).contDiff.contDiffAt
  have hphasefun : mssFineTimeRayPhaseMismatch t direction =
      fun eta : Euclidean 2 => (2 * Real.pi * t) *
        (‖eta‖ - inner Real direction eta) := by
    funext eta
    simp [mssFineTimeRayPhaseMismatch, angularDyadicRayPhaseMismatch,
      WaveSign.toReal, smul_eq_mul]
  rw [hphasefun]
  exact ((hnorm.sub hinner).const_smul (2 * Real.pi * t)).contDiffWithinAt
    (s := {eta : Euclidean 2 | eta ≠ 0})

private theorem abs_two_pi_mul_le_five_pi {t : Real}
    (ht : t ∈ lightRayTimeInterval) : |2 * Real.pi * t| ≤ 5 * Real.pi := by
  obtain ⟨htlow, htupp⟩ := (mem_lightRayTimeInterval_iff t).mp ht
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : Real)),
    abs_of_nonneg Real.pi_pos.le, abs_of_nonneg (by linarith : 0 ≤ t)]
  nlinarith [Real.pi_pos]

/-- The first time-scaled mismatch derivative has natural packet scale on
the full profile-derivative support. -/
private theorem aux_norm_fderiv_mssFineTimePhaseMismatch_le
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 2 ≤ scale)
    (n nu : Int) (hnu : nu ∈ D.angularIndices scale)
    (t : Real) (ht : t ∈ lightRayTimeInterval) (xi : Euclidean 2)
    (hxi : xi ∈ tsupport (D.spatialProfile scale n nu : Euclidean 2 → Complex)) :
    ‖fderiv Real (mssFineTimeRayPhaseMismatch t (D.directions scale nu)) xi‖ ≤
      (5 * Real.pi * D.angularConstant) * ((Real.sqrt scale)⁻¹) := by
  have hcontainer :=
    mssFineSpatialProfile_tsupport_subset_closed_raySector D hscale n nu hnu hxi
  have hscale_pos : 0 < scale := by linarith
  have hxi0 : xi ≠ 0 := by
    intro hzero
    subst xi
    norm_num at hcontainer
    linarith
  have hphase :=
    aux_norm_fderiv_mssFinePhaseMismatch_plus_le_of_spatialProfile_tsupport
      D scale n nu hscale hnu xi hxi
  have hphase' : ‖fderiv Real
      (angularDyadicRayPhaseMismatch WaveSign.plus (D.directions scale nu)) xi‖ ≤
      D.angularConstant * ((Real.sqrt scale)⁻¹) := by
    simpa only [mss_rpow_neg_half_eq_sqrt_inv hscale_pos] using hphase
  have hdiff : DifferentiableAt Real
      (angularDyadicRayPhaseMismatch WaveSign.plus (D.directions scale nu)) xi := by
    unfold angularDyadicRayPhaseMismatch
    simp only [WaveSign.toReal, one_mul]
    exact ((contDiffAt_norm Real hxi0).differentiableAt one_ne_zero).sub
      ((innerSL Real (D.directions scale nu)).differentiableAt)
  change ‖fderiv Real
      ((2 * Real.pi * t) • angularDyadicRayPhaseMismatch WaveSign.plus
        (D.directions scale nu)) xi‖ ≤ _
  rw [fderiv_const_smul hdiff, norm_smul]
  calc
    |2 * Real.pi * t| * ‖fderiv Real
        (angularDyadicRayPhaseMismatch WaveSign.plus (D.directions scale nu)) xi‖ ≤
        (5 * Real.pi) * (D.angularConstant * ((Real.sqrt scale)⁻¹)) :=
      mul_le_mul (abs_two_pi_mul_le_five_pi ht) hphase' (norm_nonneg _)
        (by positivity)
    _ = (5 * Real.pi * D.angularConstant) * ((Real.sqrt scale)⁻¹) := by ring

/-- Higher time-scaled mismatch derivatives retain the radial scale on all
profile derivative supports. -/
private theorem aux_exists_mssFineTimePhaseMismatch_higherDerivative_bound
    (r : Nat) (hr : 2 ≤ r) :
    ∃ A : Real, 0 ≤ A ∧ ∀ (D : MSSWavefrontKernelData)
      (scale : Real) (n nu : Int) (t : Real) (xi : Euclidean 2), 2 ≤ scale →
      nu ∈ D.angularIndices scale → t ∈ lightRayTimeInterval →
      xi ∈ tsupport (D.spatialProfile scale n nu : Euclidean 2 → Complex) →
      scale ^ (r - 1) * ‖iteratedFDeriv Real r
        (mssFineTimeRayPhaseMismatch t (D.directions scale nu)) xi‖ ≤ A := by
  obtain ⟨A, hA, hphase⟩ :=
    aux_exists_mssFinePhaseMismatch_higherDerivative_bound_of_spatialProfile_tsupport r hr
  refine ⟨(5 * Real.pi) * A, mul_nonneg (by positivity) hA, ?_⟩
  intro D scale n nu t xi hscale hnu ht hxi
  have hcontainer :=
    mssFineSpatialProfile_tsupport_subset_closed_raySector D hscale n nu hnu hxi
  have hxi0 : xi ≠ 0 := by
    intro hzero
    subst xi
    norm_num at hcontainer
    linarith [hscale]
  have hdiff : ContDiffAt Real (r : ℕ∞)
      (angularDyadicRayPhaseMismatch WaveSign.plus (D.directions scale nu)) xi := by
    unfold angularDyadicRayPhaseMismatch
    simp only [WaveSign.toReal, one_mul]
    exact (contDiffAt_norm Real hxi0).sub
      ((innerSL Real (D.directions scale nu)).contDiff.contDiffAt)
  change scale ^ (r - 1) * ‖iteratedFDeriv Real r
      ((2 * Real.pi * t) • angularDyadicRayPhaseMismatch WaveSign.plus
        (D.directions scale nu)) xi‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (a := 2 * Real.pi * t) hdiff, norm_smul]
  calc
    scale ^ (r - 1) *
        (|2 * Real.pi * t| * ‖iteratedFDeriv Real r
          (angularDyadicRayPhaseMismatch WaveSign.plus (D.directions scale nu)) xi‖) =
        |2 * Real.pi * t| *
          (scale ^ (r - 1) * ‖iteratedFDeriv Real r
            (angularDyadicRayPhaseMismatch WaveSign.plus (D.directions scale nu)) xi‖) := by
          ring
    _ ≤ (5 * Real.pi) * A :=
      mul_le_mul (abs_two_pi_mul_le_five_pi ht) (hphase D scale n nu xi hscale hnu hxi)
        (by positivity) (by positivity)

/-- A radial derivative estimate at scale `scale` converts to the weaker but
natural packet-scale inverse-square-root bound needed for the residual phase. -/
private theorem aux_le_sqrt_inv_pow_of_scale_derivative_bound
    (m : Nat) {scale X A : Real} (hscale : 2 ≤ scale) (hA : 0 ≤ A)
    (hbound : scale ^ (m + 1) * X ≤ A) :
    X ≤ A * ((Real.sqrt scale)⁻¹) ^ (m + 2) := by
  have hscale_pos : 0 < scale := by linarith
  have hpow_pos : 0 < scale ^ (m + 1) := pow_pos hscale_pos _
  have hdiv : X ≤ A * (scale ^ (m + 1))⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hpow_pos).mpr
    simpa [mul_comm] using hbound
  have hroot_one : 1 ≤ Real.sqrt scale :=
    Real.one_le_sqrt.mpr (by linarith)
  have hindices : m + 2 ≤ 2 * (m + 1) := by omega
  have hinvpow :
      ((Real.sqrt scale) ^ (2 * (m + 1)))⁻¹ ≤
        ((Real.sqrt scale) ^ (m + 2))⁻¹ :=
    inv_pow_le_inv_pow_of_le hroot_one hindices
  have hscalepow :
      (scale ^ (m + 1))⁻¹ =
        ((Real.sqrt scale) ^ (2 * (m + 1)))⁻¹ := by
    have hsquare : (Real.sqrt scale) ^ 2 = scale :=
      Real.sq_sqrt (by linarith : 0 ≤ scale)
    calc
      (scale ^ (m + 1))⁻¹ =
          (((Real.sqrt scale) ^ 2) ^ (m + 1))⁻¹ := by rw [hsquare]
      _ = ((Real.sqrt scale) ^ (2 * (m + 1)))⁻¹ := by rw [← pow_mul]
  calc
    X ≤ A * (scale ^ (m + 1))⁻¹ := hdiv
    _ = A * ((Real.sqrt scale) ^ (2 * (m + 1)))⁻¹ := by rw [hscalepow]
    _ ≤ A * ((Real.sqrt scale) ^ (m + 2))⁻¹ :=
      mul_le_mul_of_nonneg_left hinvpow hA
    _ = A * ((Real.sqrt scale)⁻¹) ^ (m + 2) := by rw [inv_pow]

/-- Finitely many derivatives of the time-scaled phase mismatch are controlled
by a uniform constant times the natural inverse packet scale to their order.
The constant may depend on the fixed wave-front datum and on the requested
finite order, but not on the radial or angular packet. -/
private theorem exists_mssFineTimePhaseMismatchDerivativePowerBound
    (D : MSSWavefrontKernelData) (N : Nat) :
    ∃ B : Real, 1 ≤ B ∧ ∀ (scale : Real) (n nu : Int) (t : Real)
      (i : Nat) (xi : Euclidean 2), 2 ≤ scale →
      nu ∈ D.angularIndices scale → t ∈ lightRayTimeInterval →
      xi ∈ tsupport (D.spatialProfile scale n nu : Euclidean 2 → Complex) →
      1 ≤ i → i ≤ N →
      ‖iteratedFDeriv Real i
        (mssFineTimeRayPhaseMismatch t (D.directions scale nu)) xi‖ ≤
          (B * ((Real.sqrt scale)⁻¹)) ^ i := by
  choose A hA0 hA using fun m : Nat =>
    aux_exists_mssFineTimePhaseMismatch_higherDerivative_bound (m + 2) (by omega)
  let d₁ : Real := 5 * Real.pi * D.angularConstant
  let dHigh : Nat → Real := fun m => A m
  let B : Real := 1 + d₁ + ∑ m ∈ Finset.range (N + 1), dHigh m
  have hd₁0 : 0 ≤ d₁ := by
    dsimp [d₁]
    exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      D.angularConstant_pos.le
  have hdHigh0 : ∀ m : Nat, 0 ≤ dHigh m := by
    intro m
    exact hA0 m
  have hsum0 : 0 ≤ ∑ m ∈ Finset.range (N + 1), dHigh m := by
    exact Finset.sum_nonneg fun m _ => hdHigh0 m
  have hB1 : 1 ≤ B := by
    dsimp [B]
    linarith
  refine ⟨B, hB1, ?_⟩
  intro scale n nu t i xi hscale hnu ht hxi hi1 hiN
  have hscale_pos : 0 < scale := by linarith
  have hinv0 : 0 ≤ (Real.sqrt scale)⁻¹ := by positivity
  have hBpow : B ≤ B ^ i :=
    le_self_pow₀ hB1 (Nat.ne_of_gt hi1)
  have hBpacket :
      B * ((Real.sqrt scale)⁻¹) ^ i ≤
        (B * ((Real.sqrt scale)⁻¹)) ^ i := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hBpow (pow_nonneg hinv0 _)
  by_cases hi_eq : i = 1
  · subst i
    have hphase := aux_norm_fderiv_mssFineTimePhaseMismatch_le
      D hscale n nu hnu t ht xi hxi
    have hd₁le : d₁ ≤ B := by
      dsimp [B]
      linarith
    calc
      ‖iteratedFDeriv Real 1
          (mssFineTimeRayPhaseMismatch t (D.directions scale nu)) xi‖ ≤
          d₁ * ((Real.sqrt scale)⁻¹) := by
        simpa only [norm_iteratedFDeriv_one, d₁] using hphase
      _ ≤ B * ((Real.sqrt scale)⁻¹) :=
        mul_le_mul_of_nonneg_right hd₁le hinv0
      _ = (B * ((Real.sqrt scale)⁻¹)) ^ 1 := by rw [pow_one]
  · have hi2 : 2 ≤ i := by omega
    let m : Nat := i - 2
    have him : m + 2 = i := by
      dsimp [m]
      omega
    have hmrange : m ∈ Finset.range (N + 1) := by
      apply Finset.mem_range.mpr
      dsimp [m]
      omega
    have hphase := hA m D scale n nu t xi hscale hnu ht hxi
    have hsub : (m + 2) - 1 = m + 1 := by omega
    have hphase' : scale ^ (m + 1) *
        ‖iteratedFDeriv Real (m + 2)
          (mssFineTimeRayPhaseMismatch t (D.directions scale nu)) xi‖ ≤ A m := by
      rw [hsub] at hphase
      exact hphase
    have hpacket := aux_le_sqrt_inv_pow_of_scale_derivative_bound m hscale
      (hA0 m) hphase'
    rw [him] at hpacket
    have hdHighle : dHigh m ≤ B := by
      have hterm : dHigh m ≤ ∑ q ∈ Finset.range (N + 1), dHigh q := by
        exact Finset.single_le_sum (fun q _ => hdHigh0 q) hmrange
      dsimp [B]
      linarith
    have hpacket' : A m * ((Real.sqrt scale)⁻¹) ^ i ≤
        B * ((Real.sqrt scale)⁻¹) ^ i :=
      mul_le_mul_of_nonneg_right (by simpa only [dHigh] using hdHighle)
        (pow_nonneg hinv0 _)
    exact hpacket.trans (hpacket'.trans hBpacket)

/-- The exponential of a time-scaled phase mismatch inherits the finite-order
packet-scale derivative bounds from the phase itself. -/
private lemma aux_norm_iteratedFDeriv_mssFineTimePhaseMismatchExp_le
    (N r : Nat) (t : Real) (direction : Euclidean 2) {xi : Euclidean 2}
    (hxi : xi ≠ 0) (hr : r ≤ N) {B : Real} {packetInvScale : Real}
    (hB : ∀ i, 1 ≤ i → i ≤ r →
      ‖iteratedFDeriv Real i
        (mssFineTimeRayPhaseMismatch t direction) xi‖ ≤
          (B * packetInvScale) ^ i) :
    ‖iteratedFDeriv Real r
      (fun eta : Euclidean 2 => Complex.exp
        (((mssFineTimeRayPhaseMismatch t direction eta : Real) : Complex) * Complex.I)) xi‖ ≤
      (r.factorial : Real) * 2 * (B * packetInvScale) ^ r := by
  let e : Real → Complex := fun s => Complex.exp (((s : Complex) * Complex.I))
  have he : ContDiff Real (N : ℕ∞) e := by
    let L : Real →L[Real] Complex := Complex.ofRealCLM.smulRight Complex.I
    change ContDiff Real (N : ℕ∞) (fun s => Complex.exp (L s))
    exact Complex.contDiff_exp.comp L.contDiff
  have hsopen : IsOpen {eta : Euclidean 2 | eta ≠ 0} := by
    simpa using (isOpen_ne : IsOpen {eta : Euclidean 2 | eta ≠ 0})
  have hcomp := aux_norm_iteratedFDeriv_comp_le_on_open
    {eta : Euclidean 2 | eta ≠ 0} hsopen
    (mssFineTimeRayPhaseMismatch t direction) e N r
    (mssFineTimeRayPhaseMismatch_contDiffOn N t direction) he hxi hr
    (C := 2) (B := B * packetInvScale)
    (fun i hi => aux_norm_iteratedFDeriv_exp_ofReal_mul_I_le_two i
      (mssFineTimeRayPhaseMismatch t direction xi)) hB
  change ‖iteratedFDeriv Real r
    (e ∘ mssFineTimeRayPhaseMismatch t direction) xi‖ ≤ _
  exact hcomp

/-- The product of the literal phase exponential and a canonical lattice
cutoff has packet-scale derivative bounds wherever a fine profile (or one of
its derivatives) can be nonzero. -/
private theorem exists_mssFinePhaseCanonicalCutoffDerivativeBound
    (D : MSSWavefrontKernelData) (N : Nat) :
    ∃ (B : Real) (Q : Nat → Real), 1 ≤ B ∧ (∀ k, 0 ≤ Q k) ∧
      ∀ (scale : Real) (n nu : Int) (t : Real) (k : Nat)
        (cube : Fin (mssCanonicalCubeCount D scale)) (xi : Euclidean 2),
        2 ≤ scale → nu ∈ D.angularIndices scale → t ∈ lightRayTimeInterval →
        xi ∈ tsupport (D.spatialProfile scale n nu : Euclidean 2 → Complex) →
        k ≤ N →
        ‖iteratedFDeriv Real k (fun eta : Euclidean 2 =>
          Complex.exp
            (((mssFineTimeRayPhaseMismatch t (D.directions scale nu) eta : Real) : Complex) *
              Complex.I) *
            mssCanonicalCubeCutoff D scale cube eta) xi‖ ≤
          Q k * ((Real.sqrt scale)⁻¹) ^ k := by
  obtain ⟨B, hB1, hB⟩ :=
    exists_mssFineTimePhaseMismatchDerivativePowerBound D N
  choose C hC0 hC using fun r : Nat =>
    exists_mssCanonicalCube_cutoff_iteratedFDeriv_norm_bound D r
  let Q : Nat → Real := fun k =>
    ∑ i ∈ Finset.range (k + 1), (k.choose i : Real) *
      ((i.factorial : Real) * 2 * B ^ i) * C (k - i)
  have hB0 : 0 ≤ B := le_trans zero_le_one hB1
  have hQ0 : ∀ k, 0 ≤ Q k := by
    intro k
    dsimp [Q]
    apply Finset.sum_nonneg
    intro i _
    have hfactor : 0 ≤ (i.factorial : Real) * 2 * B ^ i := by
      positivity
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hfactor) (hC0 (k - i))
  refine ⟨B, Q, hB1, hQ0, ?_⟩
  intro scale n nu t k cube xi hscale hnu ht hxi hk
  let U : Set (Euclidean 2) := {eta : Euclidean 2 | eta ≠ 0}
  have hU : IsOpen U := by
    simpa [U] using (isOpen_ne : IsOpen {eta : Euclidean 2 | eta ≠ 0})
  have hxi0 : xi ≠ 0 := by
    have hcontainer :=
      mssFineSpatialProfile_tsupport_subset_closed_raySector D hscale n nu hnu hxi
    intro hzero
    subst xi
    norm_num at hcontainer
    linarith [hscale]
  let phase : Euclidean 2 → Complex := fun eta =>
    Complex.exp
      (((mssFineTimeRayPhaseMismatch t (D.directions scale nu) eta : Real) : Complex) *
        Complex.I)
  let cutoff : Euclidean 2 → Complex := mssCanonicalCubeCutoff D scale cube
  have hphaseSmooth : ContDiffOn Real (N : ℕ∞) phase U := by
    let e : Real → Complex := fun s => Complex.exp (((s : Complex) * Complex.I))
    have he : ContDiff Real (N : ℕ∞) e := by
      let L : Real →L[Real] Complex := Complex.ofRealCLM.smulRight Complex.I
      change ContDiff Real (N : ℕ∞) (fun s => Complex.exp (L s))
      exact Complex.contDiff_exp.comp L.contDiff
    change ContDiffOn Real (N : ℕ∞)
      (e ∘ mssFineTimeRayPhaseMismatch t (D.directions scale nu)) U
    exact he.comp_contDiffOn
      (mssFineTimeRayPhaseMismatch_contDiffOn N t (D.directions scale nu))
  have hcutoffSmooth : ContDiffOn Real (N : ℕ∞) cutoff U := by
    exact ((mssCanonicalCubeCutoff D scale cube).smooth (N : ℕ∞)).contDiffOn
  have hprod := aux_norm_iteratedFDeriv_mul_le_on_open U hU phase cutoff N k
    hphaseSmooth hcutoffSmooth hxi0 hk
  change ‖iteratedFDeriv Real k (fun eta : Euclidean 2 =>
      phase eta * cutoff eta) xi‖ ≤ Q k * ((Real.sqrt scale)⁻¹) ^ k
  calc
    ‖iteratedFDeriv Real k (fun eta : Euclidean 2 => phase eta * cutoff eta) xi‖ ≤
        ∑ i ∈ Finset.range (k + 1), (k.choose i : Real) *
          ‖iteratedFDeriv Real i phase xi‖ *
            ‖iteratedFDeriv Real (k - i) cutoff xi‖ := hprod
    _ ≤ Q k * ((Real.sqrt scale)⁻¹) ^ k := by
      dsimp [Q]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hiN : i ≤ N := le_trans hik hk
      have hphase := aux_norm_iteratedFDeriv_mssFineTimePhaseMismatchExp_le
        N i t (D.directions scale nu) hxi0 hiN
        (fun r hr1 hri => hB scale n nu t r xi hscale hnu ht hxi hr1
          (le_trans hri hiN))
      have hphase' : ‖iteratedFDeriv Real i phase xi‖ ≤
          ((i.factorial : Real) * 2 * B ^ i) * ((Real.sqrt scale)⁻¹) ^ i := by
        calc
          ‖iteratedFDeriv Real i phase xi‖ ≤
              (i.factorial : Real) * 2 *
                (B * ((Real.sqrt scale)⁻¹)) ^ i := by
            simpa only [phase] using hphase
          _ = ((i.factorial : Real) * 2 * B ^ i) *
              ((Real.sqrt scale)⁻¹) ^ i := by
            rw [mul_pow]
            ring
      have hcutoff := hC (k - i) scale hscale cube xi
      have hphaseBound0 : 0 ≤
          ((i.factorial : Real) * 2 * B ^ i) * ((Real.sqrt scale)⁻¹) ^ i := by
        positivity
      have hterm : (k.choose i : Real) * ‖iteratedFDeriv Real i phase xi‖ *
          ‖iteratedFDeriv Real (k - i) cutoff xi‖ ≤
          (k.choose i : Real) *
            (((i.factorial : Real) * 2 * B ^ i) * ((Real.sqrt scale)⁻¹) ^ i) *
            (C (k - i) * ((Real.sqrt scale)⁻¹) ^ (k - i)) := by
        rw [show (k.choose i : Real) * ‖iteratedFDeriv Real i phase xi‖ *
            ‖iteratedFDeriv Real (k - i) cutoff xi‖ =
            (k.choose i : Real) *
              (‖iteratedFDeriv Real i phase xi‖ *
                ‖iteratedFDeriv Real (k - i) cutoff xi‖) by ring]
        rw [show (k.choose i : Real) *
            (((i.factorial : Real) * 2 * B ^ i) * ((Real.sqrt scale)⁻¹) ^ i) *
            (C (k - i) * ((Real.sqrt scale)⁻¹) ^ (k - i)) =
            (k.choose i : Real) *
              ((((i.factorial : Real) * 2 * B ^ i) * ((Real.sqrt scale)⁻¹) ^ i) *
                (C (k - i) * ((Real.sqrt scale)⁻¹) ^ (k - i))) by ring]
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul hphase' hcutoff (norm_nonneg _) hphaseBound0
        · exact Nat.cast_nonneg _
      calc
        (k.choose i : Real) * ‖iteratedFDeriv Real i phase xi‖ *
            ‖iteratedFDeriv Real (k - i) cutoff xi‖ ≤
            (k.choose i : Real) *
              (((i.factorial : Real) * 2 * B ^ i) * ((Real.sqrt scale)⁻¹) ^ i) *
              (C (k - i) * ((Real.sqrt scale)⁻¹) ^ (k - i)) := hterm
        _ = (k.choose i : Real) * ((i.factorial : Real) * 2 * B ^ i) * C (k - i) *
            ((Real.sqrt scale)⁻¹) ^ k := by
              have hpows : ((Real.sqrt scale)⁻¹) ^ i *
                  ((Real.sqrt scale)⁻¹) ^ (k - i) =
                    ((Real.sqrt scale)⁻¹) ^ k := by
                rw [← pow_add, Nat.add_sub_of_le hik]
              calc
                (k.choose i : Real) *
                    (((i.factorial : Real) * 2 * B ^ i) *
                      ((Real.sqrt scale)⁻¹) ^ i) *
                    (C (k - i) * ((Real.sqrt scale)⁻¹) ^ (k - i)) =
                    ((k.choose i : Real) * ((i.factorial : Real) * 2 * B ^ i) *
                      C (k - i)) *
                      (((Real.sqrt scale)⁻¹) ^ i *
                        ((Real.sqrt scale)⁻¹) ^ (k - i)) := by ring
                _ = (k.choose i : Real) * ((i.factorial : Real) * 2 * B ^ i) *
                    C (k - i) * ((Real.sqrt scale)⁻¹) ^ k := by rw [hpows]

/-- The literal fine-cube residual has packet-scale `L¹` derivative bounds
through every fixed finite order.  The estimate is obtained by first pairing
the phase with the canonical cutoff in `L∞`, and then pairing that product
with the uniformly regular fine profile in `L¹`. -/
private theorem exists_mssCanonicalCubeResidualDerivativeIntegralBound
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData)
    (uniform : MSSFineSpatialProfileUniformRegularity D) (N : Nat) :
    ∃ S : Nat → Real, (∀ j, 0 ≤ S j) ∧
      ∀ (scale : Real) (n nu : Int)
        (cube : Fin ((mssCanonicalCubeDecomposition D H).cubeCount scale))
        (z : WaveSpaceTime) (j : Nat) (hscale : 2 ≤ scale),
        n ∈ relevantRadialIndexEnumeration scale →
        nu ∈ D.angularIndices scale → z.2 ∈ lightRayTimeInterval → j ≤ N →
        (∫ xi : Euclidean 2,
          ‖iteratedFDeriv Real j
            (mssFineCubeResidualSymbol D (mssCanonicalCubeDecomposition D H)
              hscale n nu cube z : Euclidean 2 → Complex) xi‖) ≤
          S j * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ j := by
  obtain ⟨B, Q, hB1, hQ0, hbase⟩ :=
    exists_mssFinePhaseCanonicalCutoffDerivativeBound D N
  choose P hP0 hP using fun r : Nat => uniform.derivative_l1 r
  let S : Nat → Real := fun j =>
    ∑ k ∈ Finset.range (j + 1), (j.choose k : Real) * Q k * P (j - k)
  have hS0 : ∀ j, 0 ≤ S j := by
    intro j
    dsimp [S]
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hQ0 k)) (hP0 (j - k))
  refine ⟨S, hS0, ?_⟩
  intro scale n nu cube z j hscale hn hnu hz hj
  let cubes : MSSCubeDecomposition D := mssCanonicalCubeDecomposition D H
  have hcubeCount : cubes.cubeCount scale = mssCanonicalCubeCount D scale := by
    dsimp [cubes, mssCanonicalCubeDecomposition,
      mssCanonicalCubeDecomposition_of_reverseOverlap]
  let canonicalCube : Fin (mssCanonicalCubeCount D scale) :=
    Fin.cast hcubeCount cube
  let profile : Euclidean 2 → Complex := D.spatialProfile scale n nu
  let phaseCutoff : Euclidean 2 → Complex := fun eta =>
    Complex.exp
        (((mssFineTimeRayPhaseMismatch z.2 (D.directions scale nu) eta : Real) : Complex) *
        Complex.I) *
      mssCanonicalCubeCutoff D scale canonicalCube eta
  let U : Set (Euclidean 2) := {eta : Euclidean 2 | eta ≠ 0}
  have hU : IsOpen U := by
    simpa [U] using (isOpen_ne : IsOpen {eta : Euclidean 2 | eta ≠ 0})
  have hfactor :
      (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
        Euclidean 2 → Complex) =
        fun eta => phaseCutoff eta * profile eta := by
    funext eta
    rw [mssFineCubeResidualSymbol_apply_phaseMismatch]
    have hcutoff : cubes.cutoff scale cube =
        mssCanonicalCubeCutoff D scale canonicalCube := by
      dsimp [cubes, canonicalCube,
        mssCanonicalCubeDecomposition, mssCanonicalCubeDecomposition_of_reverseOverlap]
      congr 1
    rw [hcutoff]
    dsimp [phaseCutoff, profile, mssFineTimeRayPhaseMismatch]
    ring
  have hphaseCutoffSmooth : ContDiffOn Real (N : ℕ∞) phaseCutoff U := by
    let phase : Euclidean 2 → Complex := fun eta =>
      Complex.exp
        (((mssFineTimeRayPhaseMismatch z.2 (D.directions scale nu) eta : Real) : Complex) *
          Complex.I)
    let cutoff : Euclidean 2 → Complex := mssCanonicalCubeCutoff D scale canonicalCube
    have hphaseSmooth : ContDiffOn Real (N : ℕ∞) phase U := by
      let e : Real → Complex := fun s => Complex.exp (((s : Complex) * Complex.I))
      have he : ContDiff Real (N : ℕ∞) e := by
        let L : Real →L[Real] Complex := Complex.ofRealCLM.smulRight Complex.I
        change ContDiff Real (N : ℕ∞) (fun s => Complex.exp (L s))
        exact Complex.contDiff_exp.comp L.contDiff
      change ContDiffOn Real (N : ℕ∞)
        (e ∘ mssFineTimeRayPhaseMismatch z.2 (D.directions scale nu)) U
      exact he.comp_contDiffOn
        (mssFineTimeRayPhaseMismatch_contDiffOn N z.2 (D.directions scale nu))
    have hcutoffSmooth : ContDiffOn Real (N : ℕ∞) cutoff U := by
      exact ((mssCanonicalCubeCutoff D scale canonicalCube).smooth (N : ℕ∞)).contDiffOn
    change ContDiffOn Real (N : ℕ∞) (fun eta => phase eta * cutoff eta) U
    exact hphaseSmooth.mul hcutoffSmooth
  have hprofileSmooth : ContDiffOn Real (N : ℕ∞) profile U := by
    exact ((D.spatialProfile scale n nu).smooth (N : ℕ∞)).contDiffOn
  have hresint : Integrable (fun xi : Euclidean 2 =>
      ‖iteratedFDeriv Real j
        (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
          Euclidean 2 → Complex) xi‖) volume := by
    simpa only [cubes, pow_zero, one_mul] using
      SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
      (mssFineCubeResidualSymbol D (mssCanonicalCubeDecomposition D H)
        hscale n nu cube z) 0 j
  have hsumint : Integrable (fun xi : Euclidean 2 =>
      ∑ k ∈ Finset.range (j + 1), (j.choose k : Real) *
        (Q k * ((Real.sqrt scale)⁻¹) ^ k) *
          ‖iteratedFDeriv Real (j - k) profile xi‖) volume := by
    apply integrable_finsetSum
    intro k _
    have hprofileInt : Integrable (fun xi : Euclidean 2 =>
        ‖iteratedFDeriv Real (j - k) profile xi‖) volume := by
      simpa only [profile, pow_zero, one_mul] using
        SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
        (D.spatialProfile scale n nu) 0 (j - k)
    exact hprofileInt.const_mul
      ((j.choose k : Real) * (Q k * ((Real.sqrt scale)⁻¹) ^ k))
  have hpoint : ∀ᵐ xi : Euclidean 2 ∂volume,
      ‖iteratedFDeriv Real j
        (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
          Euclidean 2 → Complex) xi‖ ≤
        ∑ k ∈ Finset.range (j + 1), (j.choose k : Real) *
          (Q k * ((Real.sqrt scale)⁻¹) ^ k) *
            ‖iteratedFDeriv Real (j - k) profile xi‖ := by
    have hae : ∀ᵐ xi : Euclidean 2 ∂volume, xi ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hae] with xi hxi0
    rw [hfactor]
    have hprod := aux_norm_iteratedFDeriv_mul_le_on_open U hU phaseCutoff profile N j
      hphaseCutoffSmooth hprofileSmooth hxi0 hj
    calc
      ‖iteratedFDeriv Real j (fun eta => phaseCutoff eta * profile eta) xi‖ ≤
          ∑ k ∈ Finset.range (j + 1), (j.choose k : Real) *
            ‖iteratedFDeriv Real k phaseCutoff xi‖ *
              ‖iteratedFDeriv Real (j - k) profile xi‖ := hprod
      _ ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : Real) *
          (Q k * ((Real.sqrt scale)⁻¹) ^ k) *
            ‖iteratedFDeriv Real (j - k) profile xi‖ := by
          apply Finset.sum_le_sum
          intro k hk
          have hkj : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hkN : k ≤ N := le_trans hkj hj
          by_cases hzero : iteratedFDeriv Real (j - k) profile xi = 0
          · simp [hzero]
          · have hsupport : xi ∈ Function.support
                (iteratedFDeriv Real (j - k) profile) := hzero
            have htsupport : xi ∈ tsupport profile :=
              support_iteratedFDeriv_subset (j - k) hsupport
            have hlocal := hbase scale n nu z.2 k canonicalCube xi
              hscale hnu hz htsupport hkN
            have hcoef0 : 0 ≤ (j.choose k : Real) := Nat.cast_nonneg _
            have hbound0 : 0 ≤ Q k * ((Real.sqrt scale)⁻¹) ^ k := by
              exact mul_nonneg (hQ0 k) (by positivity)
            rw [show (j.choose k : Real) * ‖iteratedFDeriv Real k phaseCutoff xi‖ *
                ‖iteratedFDeriv Real (j - k) profile xi‖ =
                (j.choose k : Real) *
                  (‖iteratedFDeriv Real k phaseCutoff xi‖ *
                    ‖iteratedFDeriv Real (j - k) profile xi‖) by ring]
            rw [show (j.choose k : Real) * (Q k * ((Real.sqrt scale)⁻¹) ^ k) *
                ‖iteratedFDeriv Real (j - k) profile xi‖ =
                (j.choose k : Real) *
                  ((Q k * ((Real.sqrt scale)⁻¹) ^ k) *
                    ‖iteratedFDeriv Real (j - k) profile xi‖) by ring]
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul hlocal le_rfl (norm_nonneg _) hbound0
            · exact hcoef0
  have hprofileBound : ∀ k ∈ Finset.range (j + 1),
      (∫ xi : Euclidean 2,
        ‖iteratedFDeriv Real (j - k) profile xi‖) ≤
          P (j - k) * (Real.sqrt scale) ^ 2 *
            ((Real.sqrt scale)⁻¹) ^ (j - k) := by
    intro k _
    simpa only [profile] using hP (j - k) scale n nu hscale hn hnu
  calc
    (∫ xi : Euclidean 2,
      ‖iteratedFDeriv Real j
        (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
          Euclidean 2 → Complex) xi‖) ≤
        ∫ xi : Euclidean 2,
          ∑ k ∈ Finset.range (j + 1), (j.choose k : Real) *
            (Q k * ((Real.sqrt scale)⁻¹) ^ k) *
              ‖iteratedFDeriv Real (j - k) profile xi‖ :=
      integral_mono_ae hresint hsumint hpoint
    _ = ∑ k ∈ Finset.range (j + 1), (j.choose k : Real) *
        (Q k * ((Real.sqrt scale)⁻¹) ^ k) *
          ∫ xi : Euclidean 2, ‖iteratedFDeriv Real (j - k) profile xi‖ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [integral_const_mul]
      · intro k _
        have hprofileInt : Integrable (fun xi : Euclidean 2 =>
            ‖iteratedFDeriv Real (j - k) profile xi‖) volume := by
          simpa only [profile, pow_zero, one_mul] using
            SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
            (D.spatialProfile scale n nu) 0 (j - k)
        exact hprofileInt.const_mul
          ((j.choose k : Real) * (Q k * ((Real.sqrt scale)⁻¹) ^ k))
    _ ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : Real) *
        (Q k * ((Real.sqrt scale)⁻¹) ^ k) *
          (P (j - k) * (Real.sqrt scale) ^ 2 *
            ((Real.sqrt scale)⁻¹) ^ (j - k)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left (hprofileBound k hk)
      exact mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (hQ0 k) (by positivity))
    _ = S j * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ j := by
      have hterm : ∀ k ∈ Finset.range (j + 1),
          (j.choose k : Real) * (Q k * ((Real.sqrt scale)⁻¹) ^ k) *
            (P (j - k) * (Real.sqrt scale) ^ 2 *
              ((Real.sqrt scale)⁻¹) ^ (j - k)) =
            ((j.choose k : Real) * Q k * P (j - k)) *
              (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ j := by
        intro k hk
        have hkj : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hpows : ((Real.sqrt scale)⁻¹) ^ k *
            ((Real.sqrt scale)⁻¹) ^ (j - k) =
              ((Real.sqrt scale)⁻¹) ^ j := by
          rw [← pow_add, Nat.add_sub_of_le hkj]
        rw [show (j.choose k : Real) * (Q k * ((Real.sqrt scale)⁻¹) ^ k) *
            (P (j - k) * (Real.sqrt scale) ^ 2 *
              ((Real.sqrt scale)⁻¹) ^ (j - k)) =
            ((j.choose k : Real) * Q k * P (j - k)) *
              (Real.sqrt scale) ^ 2 *
              (((Real.sqrt scale)⁻¹) ^ k * ((Real.sqrt scale)⁻¹) ^ (j - k)) by ring]
        rw [hpows]
      rw [show (∑ k ∈ Finset.range (j + 1), (j.choose k : Real) *
          (Q k * ((Real.sqrt scale)⁻¹) ^ k) *
            (P (j - k) * (Real.sqrt scale) ^ 2 *
              ((Real.sqrt scale)⁻¹) ^ (j - k))) =
          ∑ k ∈ Finset.range (j + 1), ((j.choose k : Real) * Q k * P (j - k)) *
            (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ j by
          apply Finset.sum_congr rfl
          intro k hk
          exact hterm k hk]
      rw [← Finset.sum_mul]
      rw [← Finset.sum_mul]

/-- The preceding order-by-order bounds assemble into exactly the scaled
finite derivative seminorm required by the literal light-ray kernel bridge. -/
private theorem exists_mssCanonicalCubeResidual_scaledDerivativeIntegralBound
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData)
    (uniform : MSSFineSpatialProfileUniformRegularity D) (N : Nat) :
    ∃ A : Real, 0 ≤ A ∧ ∀ (scale : Real) (hscale : 2 ≤ scale)
      (n : Int), n ∈ relevantRadialIndexEnumeration scale →
      ∀ (nu : Int), nu ∈ D.angularIndices scale →
      ∀ cube : Fin ((mssCanonicalCubeDecomposition D H).cubeCount scale),
        cube ∈ (mssCanonicalCubeDecomposition D H).cubeSets scale n nu →
      ∀ z : WaveSpaceTime, z.2 ∈ lightRayTimeInterval →
        (2 : Real) ^ N * ∑ j ∈ Finset.range (N + 1),
          ((mssCanonicalCubeDecomposition D H).cubeWidth * Real.sqrt scale) ^ j *
            ∫ xi : Euclidean 2,
              ‖iteratedFDeriv Real j
                (mssFineCubeResidualSymbol D (mssCanonicalCubeDecomposition D H)
                  hscale n nu cube z : Euclidean 2 → Complex) xi‖ ≤
          A * ((mssCanonicalCubeDecomposition D H).cubeWidth * Real.sqrt scale) ^ 2 := by
  obtain ⟨S, hS0, hderiv⟩ :=
    exists_mssCanonicalCubeResidualDerivativeIntegralBound D H uniform N
  let T : Real := ∑ j ∈ Finset.range (N + 1), (2 : Real) ^ j * S j
  let A : Real := (2 : Real) ^ N * T
  have hT0 : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (pow_nonneg (by norm_num) _) (hS0 j)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (pow_nonneg (by norm_num) _) hT0
  refine ⟨A, hA0, ?_⟩
  intro scale hscale n hn nu hnu cube _ z hz
  have hwidth : (mssCanonicalCubeDecomposition D H).cubeWidth = 2 := by
    rfl
  rw [hwidth]
  have hsqrt_pos : 0 < Real.sqrt scale := by positivity
  have hsqrt_ne : Real.sqrt scale ≠ 0 := ne_of_gt hsqrt_pos
  have hsum :
      ∑ j ∈ Finset.range (N + 1), (2 * Real.sqrt scale) ^ j *
        ∫ xi : Euclidean 2,
          ‖iteratedFDeriv Real j
            (mssFineCubeResidualSymbol D (mssCanonicalCubeDecomposition D H)
              hscale n nu cube z : Euclidean 2 → Complex) xi‖ ≤
        ∑ j ∈ Finset.range (N + 1), ((2 : Real) ^ j * S j) *
          (Real.sqrt scale) ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have horder := hderiv scale n nu cube z j hscale hn hnu hz hjN
    have hfactor0 : 0 ≤ (2 * Real.sqrt scale) ^ j := by positivity
    have hpows : (Real.sqrt scale) ^ j * ((Real.sqrt scale)⁻¹) ^ j = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hsqrt_ne, one_pow]
    calc
      (2 * Real.sqrt scale) ^ j *
          ∫ xi : Euclidean 2,
            ‖iteratedFDeriv Real j
              (mssFineCubeResidualSymbol D (mssCanonicalCubeDecomposition D H)
                hscale n nu cube z : Euclidean 2 → Complex) xi‖ ≤
          (2 * Real.sqrt scale) ^ j *
            (S j * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ j) :=
        mul_le_mul_of_nonneg_left horder hfactor0
      _ = ((2 : Real) ^ j * S j) * (Real.sqrt scale) ^ 2 := by
        rw [mul_pow]
        calc
          ((2 : Real) ^ j * (Real.sqrt scale) ^ j) *
              (S j * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ j) =
              ((2 : Real) ^ j * S j) * (Real.sqrt scale) ^ 2 *
                ((Real.sqrt scale) ^ j * ((Real.sqrt scale)⁻¹) ^ j) := by ring
          _ = ((2 : Real) ^ j * S j) * (Real.sqrt scale) ^ 2 := by rw [hpows, mul_one]
  have hsumEq :
      (∑ j ∈ Finset.range (N + 1), ((2 : Real) ^ j * S j) *
        (Real.sqrt scale) ^ 2) = T * (Real.sqrt scale) ^ 2 := by
    dsimp [T]
    rw [Finset.sum_mul]
  have hsquare_le : (Real.sqrt scale) ^ 2 ≤ (2 * Real.sqrt scale) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt scale)]
  calc
    (2 : Real) ^ N *
        ∑ j ∈ Finset.range (N + 1), (2 * Real.sqrt scale) ^ j *
          ∫ xi : Euclidean 2,
            ‖iteratedFDeriv Real j
              (mssFineCubeResidualSymbol D (mssCanonicalCubeDecomposition D H)
                hscale n nu cube z : Euclidean 2 → Complex) xi‖ ≤
        (2 : Real) ^ N *
          (∑ j ∈ Finset.range (N + 1), ((2 : Real) ^ j * S j) *
            (Real.sqrt scale) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg (by norm_num) _)
    _ = A * (Real.sqrt scale) ^ 2 := by
      rw [hsumEq]
      dsimp [A]
      ring
    _ ≤ A * (2 * Real.sqrt scale) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare_le hA0

/-- On the support of an actual MSS packet profile, the plus-sheet phase
gradient differs from the packet ray direction by precisely the angular
aperture.  This is the first-order nonstationary-phase input for the literal
residual symbol. -/
private theorem aux_norm_fderiv_mssFinePhaseMismatch_plus_le_of_spatialProfile_ne_zero
    (D : MSSWavefrontKernelData) (scale : Real) (n nu : Int)
    (hnu : nu ∈ D.angularIndices scale) (xi : Euclidean 2)
    (hprofile : D.spatialProfile scale n nu xi ≠ 0) :
    ‖fderiv Real
        (angularDyadicRayPhaseMismatch WaveSign.plus (D.directions scale nu)) xi‖ ≤
      D.angularConstant * scale ^ (-(1 / 2 : Real)) := by
  have hchi : D.chi scale nu xi ≠ 0 := by
    rw [D.spatialProfile_apply] at hprofile
    exact (mul_ne_zero_iff.mp hprofile).1
  have hsector : xi ∈ angularSector (D.directions scale nu)
      (D.angularConstant * scale ^ (-(1 / 2 : Real))) :=
    D.chi_support scale nu hnu hchi
  rcases hsector with ⟨hxi, hangular⟩
  rw [fderiv_angularDyadicRayPhaseMismatch WaveSign.plus
    (D.directions scale nu) xi hxi]
  simp only [WaveSign.toReal, one_smul]
  have hrewrite :
      (‖xi‖)⁻¹ • innerSL Real xi - innerSL Real (D.directions scale nu) =
        innerSL Real ((‖xi‖)⁻¹ • xi - D.directions scale nu) := by
    ext v
    simp
  calc
    ‖(‖xi‖)⁻¹ • innerSL Real xi - innerSL Real (D.directions scale nu)‖ =
        ‖innerSL Real ((‖xi‖)⁻¹ • xi - D.directions scale nu)‖ := by
          rw [hrewrite]
    _ = ‖(‖xi‖)⁻¹ • xi - D.directions scale nu‖ :=
      innerSL_apply_norm (𝕜 := Real) _
    _ ≤ D.angularConstant * scale ^ (-(1 / 2 : Real)) := hangular

/-- Higher frequency derivatives of the plus-sheet phase mismatch have their
radial natural scale wherever an actual MSS spatial profile is nonzero.  The
linear ray term disappears from orders at least two. -/
private theorem aux_exists_mssFinePhaseMismatch_higherDerivative_bound
    (r : Nat) (hr : 2 ≤ r) :
    ∃ A : Real, 0 ≤ A ∧ ∀ (D : MSSWavefrontKernelData)
      (scale : Real) (n nu : Int) (xi : Euclidean 2), 2 ≤ scale →
      D.spatialProfile scale n nu xi ≠ 0 →
      scale ^ (r - 1) *
        ‖iteratedFDeriv Real r
          (angularDyadicRayPhaseMismatch WaveSign.plus (D.directions scale nu)) xi‖ ≤ A := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_scaled_norm_iteratedFDeriv_bound 2 r (by omega : 1 ≤ r)
  refine ⟨A, hA, ?_⟩
  intro D scale n nu xi hscale hprofile
  have hscale_pos : 0 < scale := by linarith
  have hamp : D.radialTime.amplitude (scale⁻¹ • xi) ≠ 0 := by
    rw [D.spatialProfile_apply] at hprofile
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprofile).2).1
  have hannulus := D.radialTime.amplitude_support_annulus (scale⁻¹ • xi) hamp
  have hnormScale : ‖scale⁻¹ • xi‖ = scale⁻¹ * ‖xi‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale_pos)]
  rw [hnormScale] at hannulus
  have hcancel : scale * (scale⁻¹ * ‖xi‖) = ‖xi‖ := by
    field_simp [hscale_pos.ne']
  have hlow : scale / 2 ≤ ‖xi‖ := by
    rw [show scale / 2 = scale * (1 / 2 : Real) by ring,
      ← hcancel]
    exact mul_le_mul_of_nonneg_left hannulus.1 hscale_pos.le
  have hupp : ‖xi‖ ≤ 2 * scale := by
    rw [show 2 * scale = scale * 2 by ring, ← hcancel]
    exact mul_le_mul_of_nonneg_left hannulus.2 hscale_pos.le
  have hxi : xi ≠ 0 := by
    intro hzero
    subst xi
    have hhalf_pos : 0 < scale / 2 := by positivity
    have hlow_zero : scale / 2 ≤ 0 := by simpa only [norm_zero] using hlow
    linarith
  rw [iteratedFDeriv_angularDyadicRayPhaseMismatch_plus_eq_norm_of_two_le
    hr (D.directions scale nu) xi hxi]
  exact hbound scale xi hscale_pos hlow hupp

/-- Fourier integration by parts bounds each physical seminorm of the
literal fine-cube residual by its actual frequency-side derivative integrals.
This is exact and scale-free.  It is a useful unscaled estimate, but the
natural-scale light-ray argument uses the scale-aware refinement below. -/
theorem mssFineCubeResidualSymbol_fourierInv_seminorm_le_derivativeIntegrals
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (scale : Real) (hscale : 2 ≤ scale) (n nu : Int)
    (cube : Fin (cubes.cubeCount scale)) (z : WaveSpaceTime) (N : Nat) :
    SchwartzMap.seminorm Complex N 0
      (FourierTransform.fourierInv
        (mssFineCubeResidualSymbol D cubes hscale n nu cube z) :
          SchwartzMap (Euclidean 2) Complex) ≤
      (2 : Real) ^ N * ∑ j ∈ Finset.range (N + 1),
        ∫ xi : Euclidean 2,
          ‖iteratedFDeriv Real j
            (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
              Euclidean 2 → Complex) xi‖ := by
  apply SchwartzMap.seminorm_le_bound Complex N 0
    (FourierTransform.fourierInv
      (mssFineCubeResidualSymbol D cubes hscale n nu cube z) :
        SchwartzMap (Euclidean 2) Complex)
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)
  · intro x
    rw [norm_iteratedFDeriv_zero]
    rw [SchwartzMap.fourierInv_coe]
    change ‖x‖ ^ N * ‖FourierTransform.fourierInv
      (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
        Euclidean 2 → Complex) x‖ ≤ _
    have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (f := (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
        Euclidean 2 → Complex)) (K := 0) (N := N)
      ((mssFineCubeResidualSymbol D cubes hscale n nu cube z).smooth N)
      (fun k j hk hj => by
        have hk' : k = 0 := by simpa using hk
        subst k
        simpa using SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
          (mssFineCubeResidualSymbol D cubes hscale n nu cube z) 0 j)
      (k := 0) (n := N) (by simp) (by simp) (-x)
    simpa [Real.fourierInv_eq_fourier_neg] using h

/-- The generic unscaled Fourier integration-by-parts bound.  It is kept
private because the literal MSS specialization above and the scale-aware
version below are the intended public interfaces. -/
private theorem fourierInv_seminorm_le_derivativeIntegrals
    (q : SchwartzMap (Euclidean 2) Complex) (N : Nat) :
    SchwartzMap.seminorm Complex N 0
      (FourierTransform.fourierInv q : SchwartzMap (Euclidean 2) Complex) ≤
      (2 : Real) ^ N * ∑ j ∈ Finset.range (N + 1),
        ∫ xi : Euclidean 2, ‖iteratedFDeriv Real j (q : Euclidean 2 → Complex) xi‖ := by
  apply SchwartzMap.seminorm_le_bound Complex N 0
    (FourierTransform.fourierInv q : SchwartzMap (Euclidean 2) Complex)
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)
  · intro x
    rw [norm_iteratedFDeriv_zero]
    rw [SchwartzMap.fourierInv_coe]
    change ‖x‖ ^ N * ‖FourierTransform.fourierInv
      (q : Euclidean 2 → Complex) x‖ ≤ _
    have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (f := (q : Euclidean 2 → Complex)) (K := 0) (N := N)
      (q.smooth N)
      (fun k j hk hj => by
        have hk' : k = 0 := by simpa using hk
        subst k
        simpa using SchwartzMap.integrable_pow_mul_iteratedFDeriv volume q 0 j)
      (k := 0) (n := N) (by simp) (by simp) (-x)
    simpa [Real.fourierInv_eq_fourier_neg] using h

/-- Rescaling the frequency variable before Fourier integration by parts
keeps every derivative at its natural scale.  In dimension two the physical
seminorm loses exactly `R⁻¹ ^ N`; the Jacobian cancels the `R²` size of a
frequency cube.  This is the scale-aware form needed for fine MSS packets. -/
theorem fourierInv_seminorm_le_scaled_derivativeIntegrals
    (q : SchwartzMap (Euclidean 2) Complex) (N : Nat) {R : Real} (hR : 0 < R) :
    SchwartzMap.seminorm Complex N 0
      (FourierTransform.fourierInv q : SchwartzMap (Euclidean 2) Complex) ≤
      (2 : Real) ^ N * (R⁻¹) ^ N *
        ∑ j ∈ Finset.range (N + 1), R ^ j *
          ∫ xi : Euclidean 2,
            ‖iteratedFDeriv Real j (q : Euclidean 2 → Complex) xi‖ := by
  let qR : SchwartzMap (Euclidean 2) Complex :=
    Auto.Spherical.Auxiliary.translatedDilatedSchwartzCutoff
      q 0 R⁻¹ (inv_ne_zero hR.ne')
  let S : Real := ∑ j ∈ Finset.range (N + 1),
    ∫ eta : Euclidean 2, ‖iteratedFDeriv Real j (qR : Euclidean 2 → Complex) eta‖
  have hqR (xi : Euclidean 2) : qR xi = q (R • xi) := by
    dsimp [qR]
    rw [Auto.Spherical.Auxiliary.translatedDilatedSchwartzCutoff_apply]
    simp
  have hqRfun : (qR : Euclidean 2 → Complex) = fun xi => q (R • xi) := by
    funext xi
    exact hqR xi
  have hscale' (x : Euclidean 2) :
      FourierTransform.fourierInv (qR : Euclidean 2 → Complex) (R • x) =
        (R⁻¹) ^ 2 • FourierTransform.fourierInv (q : Euclidean 2 → Complex) x := by
    simpa only [hqRfun, inv_inv, smul_smul, inv_mul_cancel₀ hR.ne', one_smul,
      finrank_euclideanSpace_fin] using
      Auto.Spherical.Auxiliary.fourierInv_comp_inv_smul
        (g := (q : Euclidean 2 → Complex)) (R := R⁻¹) (inv_pos.mpr hR) (R • x)
  have hunit : R ^ 2 * (R⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hR.ne', one_pow]
  have hkernelScale (x : Euclidean 2) :
      FourierTransform.fourierInv (q : Euclidean 2 → Complex) x =
        R ^ 2 • FourierTransform.fourierInv (qR : Euclidean 2 → Complex) (R • x) := by
    rw [hscale']
    nth_rewrite 1 [← one_smul Real (FourierTransform.fourierInv
      (q : Euclidean 2 → Complex) x)]
    rw [← hunit, ← smul_smul]
  have hnormScale (x : Euclidean 2) :
      ‖FourierTransform.fourierInv (q : Euclidean 2 → Complex) x‖ =
        R ^ 2 * ‖FourierTransform.fourierInv
          (qR : Euclidean 2 → Complex) (R • x)‖ := by
    rw [hkernelScale, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hR.le _)]
  have hIg (j : Nat) :
      (∫ eta : Euclidean 2,
        ‖iteratedFDeriv Real j (qR : Euclidean 2 → Complex) eta‖) =
        (R⁻¹) ^ 2 * R ^ j *
          ∫ xi : Euclidean 2,
            ‖iteratedFDeriv Real j (q : Euclidean 2 → Complex) xi‖ := by
    dsimp [qR]
    simpa only [finrank_euclideanSpace_fin, inv_inv] using
      Auto.Spherical.Auxiliary.integral_norm_iteratedFDeriv_translatedDilatedSchwartzCutoff
        q 0 (inv_pos.mpr hR) j
  have hS : S = (R⁻¹) ^ 2 *
      ∑ j ∈ Finset.range (N + 1), R ^ j *
        ∫ xi : Euclidean 2,
          ‖iteratedFDeriv Real j (q : Euclidean 2 → Complex) xi‖ := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hIg]
    ring
  have hpoint (x : Euclidean 2) :
      ‖R • x‖ ^ N * ‖FourierTransform.fourierInv
        (qR : Euclidean 2 → Complex) (R • x)‖ ≤ (2 : Real) ^ N * S := by
    calc
      ‖R • x‖ ^ N * ‖FourierTransform.fourierInv
          (qR : Euclidean 2 → Complex) (R • x)‖ =
          ‖R • x‖ ^ N * ‖(FourierTransform.fourierInv qR :
            SchwartzMap (Euclidean 2) Complex) (R • x)‖ := by
        rw [SchwartzMap.fourierInv_coe]
      _ ≤ SchwartzMap.seminorm Complex N 0
          (FourierTransform.fourierInv qR : SchwartzMap (Euclidean 2) Complex) :=
        SchwartzMap.norm_pow_mul_le_seminorm Complex
          (FourierTransform.fourierInv qR : SchwartzMap (Euclidean 2) Complex) N (R • x)
      _ ≤ (2 : Real) ^ N * S := fourierInv_seminorm_le_derivativeIntegrals qR N
  apply SchwartzMap.seminorm_le_bound Complex N 0 (FourierTransform.fourierInv q)
  · exact mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg (inv_nonneg.mpr hR.le) _))
      (Finset.sum_nonneg fun j hj => mul_nonneg (pow_nonneg hR.le _)
        (integral_nonneg fun xi => norm_nonneg _))
  · intro x
    rw [norm_iteratedFDeriv_zero, SchwartzMap.fourierInv_coe, hnormScale]
    have hcancel : (R⁻¹) ^ N * R ^ N = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hR.ne', one_pow]
    have hRx : ‖R • x‖ = R * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR.le]
    have hfactor : 0 ≤ R ^ 2 * (R⁻¹) ^ N :=
      mul_nonneg (pow_nonneg hR.le _) (pow_nonneg (inv_nonneg.mpr hR.le) _)
    calc
      ‖x‖ ^ N *
          (R ^ 2 * ‖FourierTransform.fourierInv
            (qR : Euclidean 2 → Complex) (R • x)‖) =
          R ^ 2 * (R⁻¹) ^ N *
            (‖R • x‖ ^ N * ‖FourierTransform.fourierInv
              (qR : Euclidean 2 → Complex) (R • x)‖) := by
        calc
          ‖x‖ ^ N * (R ^ 2 * ‖FourierTransform.fourierInv
              (qR : Euclidean 2 → Complex) (R • x)‖) =
              R ^ 2 * ((R⁻¹) ^ N * R ^ N) *
                (‖x‖ ^ N * ‖FourierTransform.fourierInv
                  (qR : Euclidean 2 → Complex) (R • x)‖) := by
                rw [hcancel]
                ring
          _ = R ^ 2 * (R⁻¹) ^ N *
                ((R * ‖x‖) ^ N * ‖FourierTransform.fourierInv
                  (qR : Euclidean 2 → Complex) (R • x)‖) := by
                rw [mul_pow]
                ring
          _ = R ^ 2 * (R⁻¹) ^ N *
                (‖R • x‖ ^ N * ‖FourierTransform.fourierInv
                  (qR : Euclidean 2 → Complex) (R • x)‖) := by rw [hRx]
      _ ≤ R ^ 2 * (R⁻¹) ^ N * ((2 : Real) ^ N * S) :=
        mul_le_mul_of_nonneg_left (hpoint x) hfactor
      _ = (2 : Real) ^ N * (R⁻¹) ^ N *
          ∑ j ∈ Finset.range (N + 1), R ^ j *
            ∫ xi : Euclidean 2,
              ‖iteratedFDeriv Real j (q : Euclidean 2 → Complex) xi‖ := by
        rw [hS]
        calc
          R ^ 2 * (R⁻¹) ^ N * ((2 : Real) ^ N *
              ((R⁻¹) ^ 2 * ∑ j ∈ Finset.range (N + 1), R ^ j *
                ∫ xi : Euclidean 2,
                  ‖iteratedFDeriv Real j (q : Euclidean 2 → Complex) xi‖)) =
              (R ^ 2 * (R⁻¹) ^ 2) * ((2 : Real) ^ N * (R⁻¹) ^ N *
                ∑ j ∈ Finset.range (N + 1), R ^ j *
                  ∫ xi : Euclidean 2,
                    ‖iteratedFDeriv Real j (q : Euclidean 2 → Complex) xi‖) := by ring
          _ = (2 : Real) ^ N * (R⁻¹) ^ N *
                ∑ j ∈ Finset.range (N + 1), R ^ j *
                  ∫ xi : Euclidean 2,
                    ‖iteratedFDeriv Real j (q : Euclidean 2 → Complex) xi‖ := by
              rw [hunit, one_mul]

/-- Exact translation from the literal fine-cube half-wave kernel to the
inverse Fourier transform of its residual symbol.  No decay estimate is used
here. -/
theorem mssFineCubeHalfWaveKernel_eq_residual_shifted
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (scale : Real) (hscale : 2 ≤ scale) (n nu : Int)
    (cube : Fin (cubes.cubeCount scale)) (z : WaveSpaceTime) (y : Euclidean 2) :
    mssFineCubeHalfWaveKernel D cubes scale n nu cube z y =
      D.radialTime.time z.2 * Auto.Spherical.Auxiliary.fourierCubeKernel
        (mssFineCubeResidualSymbol D cubes hscale n nu cube z)
        (z.1 + z.2 • D.directions scale nu - y) := by
  have hraw : (fun xi : Euclidean 2 =>
      cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
        halfWaveMultiplier WaveSign.plus z.2 xi) =
      (mssFineCubeSchwartzSymbol D cubes hscale n nu cube z :
        Euclidean 2 → Complex) := by
    funext xi
    symm
    exact mssFineCubeSchwartzSymbol_apply D cubes hscale n nu cube z xi
  have hshift : FourierTransform.fourierInv
      (mssFineCubeSchwartzSymbol D cubes hscale n nu cube z :
        Euclidean 2 → Complex) (z.1 - y) =
      Auto.Spherical.Auxiliary.fourierCubeKernel
        (mssFineCubeResidualSymbol D cubes hscale n nu cube z)
        ((z.1 - y) + z.2 • D.directions scale nu) := by
    simpa only [mssFineCubeResidualSymbol] using
      fourierInv_eq_fourierCubeKernel_mssFinePlaneWaveResidualSymbol_shifted
        (mssFineCubeSchwartzSymbol D cubes hscale n nu cube z)
        (hasCompactSupport_mssFineCubeSchwartzSymbol D cubes hscale n nu cube z)
        z.2 (D.directions scale nu) (z.1 - y)
  unfold mssFineCubeHalfWaveKernel
  rw [hraw, hshift]
  congr 2
  module

/-- The fixed Schwartz time cutoff has a uniform pointwise bound.  This is
the time-amplitude input in the residual-decay bridge and is automatic; no
light-ray localization hypothesis is needed for it. -/
theorem exists_uniform_mssFineTime_norm_bound (D : MSSWavefrontKernelData) :
    ∃ T : Real, 0 ≤ T ∧ ∀ t : Real, ‖D.radialTime.time t‖ ≤ T := by
  let T : Real := SchwartzMap.seminorm Complex 0 0 D.radialTime.time
  refine ⟨T, ?_, ?_⟩
  · dsimp [T]
    exact (norm_nonneg (D.radialTime.time 0)).trans
      (SchwartzMap.norm_le_seminorm Complex D.radialTime.time 0)
  · intro t
    exact SchwartzMap.norm_le_seminorm Complex D.radialTime.time t

/-- Explicit inverse-Fourier residual seminorm bounds on the physical time
slab imply literal light-ray decay of the actual fine-cube half-wave kernel.
Outside that slab the outer time cutoff makes the kernel zero.  This is the
reusable nonstationary-phase endpoint: proving the displayed uniform
seminorm bounds from the fixed cutoff data remains the substantive task. -/
theorem norm_mssFineCubeHalfWaveKernel_le_lightRayKernel_of_residual_seminorm
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (A T : Real)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2)
    (hslab : D.HasLightRayTimeSlabSupport) (hA : 0 ≤ A)
    (htime : ∀ t : Real, ‖D.radialTime.time t‖ ≤ T)
    (hseminormN : ∀ (scale : Real) (hscale : 2 ≤ scale),
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
      ∀ cube ∈ cubes.cubeSets scale n nu, ∀ z : WaveSpaceTime,
        z.2 ∈ lightRayTimeInterval →
        SchwartzMap.seminorm Complex N 0
          (FourierTransform.fourierInv
            (mssFineCubeResidualSymbol D cubes hscale n nu cube z) :
              SchwartzMap (Euclidean 2) Complex) ≤
          (A * ((((cubes.cubeWidth * Real.sqrt scale)⁻¹)⁻¹) ^ 2)) *
            ((cubes.cubeWidth * Real.sqrt scale)⁻¹) ^ N)
    (hseminormZero : ∀ (scale : Real) (hscale : 2 ≤ scale),
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
      ∀ cube ∈ cubes.cubeSets scale n nu, ∀ z : WaveSpaceTime,
        z.2 ∈ lightRayTimeInterval →
        SchwartzMap.seminorm Complex 0 0
          (FourierTransform.fourierInv
            (mssFineCubeResidualSymbol D cubes hscale n nu cube z) :
              SchwartzMap (Euclidean 2) Complex) ≤
          A * ((((cubes.cubeWidth * Real.sqrt scale)⁻¹)⁻¹) ^ 2)) :
    ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
      ∀ cube ∈ cubes.cubeSets scale n nu, ∀ z : WaveSpaceTime, ∀ y : Euclidean 2,
        ‖mssFineCubeHalfWaveKernel D cubes scale n nu cube z y‖ ≤
          (T * (2 : Real) ^ N * A) *
            lightRayKernel (cubes.cubeWidth * Real.sqrt scale)⁻¹ N
              (D.directions scale nu) y z := by
  intro scale hscale n hn nu hnu cube hcube z y
  let δ : Real := (cubes.cubeWidth * Real.sqrt scale)⁻¹
  have hδ : 0 < δ :=
    (cubeWidth_inv_mul_sqrt_pos_lt_half hwidth hscale).1
  have hT : 0 ≤ T := (norm_nonneg (D.radialTime.time 0)).trans (htime 0)
  by_cases hz : z.2 ∈ lightRayTimeInterval
  · have hdecay := Auto.Spherical.Auxiliary.norm_fourierCubeKernel_le_scaled_seminorm_decay
      (mssFineCubeResidualSymbol D cubes hscale n nu cube z)
      δ (A * (δ⁻¹) ^ 2) N hδ
      (by simpa only [δ] using hseminormZero scale hscale n hn nu hnu cube hcube z hz)
      (by simpa only [δ] using hseminormN scale hscale n hn nu hnu cube hcube z hz)
      (z.1 + z.2 • D.directions scale nu - y)
    calc
      ‖mssFineCubeHalfWaveKernel D cubes scale n nu cube z y‖ =
          ‖D.radialTime.time z.2‖ * ‖Auto.Spherical.Auxiliary.fourierCubeKernel
            (mssFineCubeResidualSymbol D cubes hscale n nu cube z)
            (z.1 + z.2 • D.directions scale nu - y)‖ := by
        rw [mssFineCubeHalfWaveKernel_eq_residual_shifted D cubes scale hscale n nu cube z y,
          norm_mul]
      _ ≤ T * ‖Auto.Spherical.Auxiliary.fourierCubeKernel
            (mssFineCubeResidualSymbol D cubes hscale n nu cube z)
            (z.1 + z.2 • D.directions scale nu - y)‖ :=
        mul_le_mul_of_nonneg_right (htime z.2) (norm_nonneg _)
      _ ≤ T * ((2 : Real) ^ N * (A * (δ⁻¹) ^ 2) *
            (1 + δ⁻¹ * ‖z.1 + z.2 • D.directions scale nu - y‖)⁻¹ ^ N) :=
        mul_le_mul_of_nonneg_left hdecay hT
      _ = (T * (2 : Real) ^ N * A) *
            lightRayKernel δ N (D.directions scale nu) y z := by
        unfold lightRayKernel
        ring
      _ = (T * (2 : Real) ^ N * A) *
            lightRayKernel (cubes.cubeWidth * Real.sqrt scale)⁻¹ N
              (D.directions scale nu) y z := by rfl
  · have htimezero : D.radialTime.time z.2 = 0 :=
      D.time_eq_zero_of_not_mem_lightRayTimeInterval hslab hz
    have hkernelzero : mssFineCubeHalfWaveKernel D cubes scale n nu cube z y = 0 := by
      unfold mssFineCubeHalfWaveKernel
      rw [htimezero]
      simp
    rw [hkernelzero, norm_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hT (pow_nonneg (by norm_num) N)) hA)
      (lightRayKernel_nonneg hδ N (D.directions scale nu) y z)

/-- Unweighted frequency-side residual derivative-integral bounds on the
physical time slab imply literal light-ray decay.  This asks for a stronger
single-scale bound than the natural packet estimates usually provide; the
scale-aware theorem below is the interface used by the literal MSS route. -/
theorem norm_mssFineCubeHalfWaveKernel_le_lightRayKernel_of_residual_derivativeIntegrals
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (A T : Real)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2)
    (hslab : D.HasLightRayTimeSlabSupport) (hA : 0 ≤ A)
    (htime : ∀ t : Real, ‖D.radialTime.time t‖ ≤ T)
    (hderivativeN : ∀ (scale : Real) (hscale : 2 ≤ scale),
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
      ∀ cube ∈ cubes.cubeSets scale n nu, ∀ z : WaveSpaceTime,
        z.2 ∈ lightRayTimeInterval →
        (2 : Real) ^ N * ∑ j ∈ Finset.range (N + 1),
          ∫ xi : Euclidean 2,
            ‖iteratedFDeriv Real j
              (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
                Euclidean 2 → Complex) xi‖ ≤
          (A * ((((cubes.cubeWidth * Real.sqrt scale)⁻¹)⁻¹) ^ 2)) *
            ((cubes.cubeWidth * Real.sqrt scale)⁻¹) ^ N)
    (hderivativeZero : ∀ (scale : Real) (hscale : 2 ≤ scale),
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
      ∀ cube ∈ cubes.cubeSets scale n nu, ∀ z : WaveSpaceTime,
        z.2 ∈ lightRayTimeInterval →
        (∫ xi : Euclidean 2,
          ‖mssFineCubeResidualSymbol D cubes hscale n nu cube z xi‖) ≤
          A * ((((cubes.cubeWidth * Real.sqrt scale)⁻¹)⁻¹) ^ 2)) :
    ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
      ∀ cube ∈ cubes.cubeSets scale n nu, ∀ z : WaveSpaceTime, ∀ y : Euclidean 2,
        ‖mssFineCubeHalfWaveKernel D cubes scale n nu cube z y‖ ≤
          (T * (2 : Real) ^ N * A) *
              lightRayKernel (cubes.cubeWidth * Real.sqrt scale)⁻¹ N
              (D.directions scale nu) y z := by
  apply norm_mssFineCubeHalfWaveKernel_le_lightRayKernel_of_residual_seminorm
    D cubes N A T hwidth hslab hA htime
  · intro scale hscale n hn nu hnu cube hcube z hz
    exact (mssFineCubeResidualSymbol_fourierInv_seminorm_le_derivativeIntegrals
      D cubes scale hscale n nu cube z N).trans
        (hderivativeN scale hscale n hn nu hnu cube hcube z hz)
  · intro scale hscale n hn nu hnu cube hcube z hz
    have hsemi := mssFineCubeResidualSymbol_fourierInv_seminorm_le_derivativeIntegrals
      D cubes scale hscale n nu cube z 0
    have hsemi' : SchwartzMap.seminorm Complex 0 0
        (FourierTransform.fourierInv
          (mssFineCubeResidualSymbol D cubes hscale n nu cube z) :
            SchwartzMap (Euclidean 2) Complex) ≤
        ∫ xi : Euclidean 2,
          ‖mssFineCubeResidualSymbol D cubes hscale n nu cube z xi‖ := by
      simpa only [pow_zero, one_mul, Finset.sum_range_succ,
        Finset.sum_range_zero, norm_iteratedFDeriv_zero, zero_add] using hsemi
    exact hsemi'.trans (hderivativeZero scale hscale n hn nu hnu cube hcube z hz)

/-- Natural-scale frequency-side residual derivative bounds on the physical
time slab imply literal light-ray decay.  The derivative integral of order
`j` is weighted by the fine-cube width to the power `j`; this is the
scale-invariant form supplied by the packet product and phase estimates. -/
theorem norm_mssFineCubeHalfWaveKernel_le_lightRayKernel_of_residual_scaledDerivativeIntegrals
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (A T : Real)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2)
    (hslab : D.HasLightRayTimeSlabSupport) (hA : 0 ≤ A)
    (htime : ∀ t : Real, ‖D.radialTime.time t‖ ≤ T)
    (hderivativeN : ∀ (scale : Real) (hscale : 2 ≤ scale),
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
      ∀ cube ∈ cubes.cubeSets scale n nu, ∀ z : WaveSpaceTime,
        z.2 ∈ lightRayTimeInterval →
        (2 : Real) ^ N * ∑ j ∈ Finset.range (N + 1),
          (cubes.cubeWidth * Real.sqrt scale) ^ j *
            ∫ xi : Euclidean 2,
              ‖iteratedFDeriv Real j
                (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
                  Euclidean 2 → Complex) xi‖ ≤
          A * (cubes.cubeWidth * Real.sqrt scale) ^ 2)
    (hderivativeZero : ∀ (scale : Real) (hscale : 2 ≤ scale),
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
      ∀ cube ∈ cubes.cubeSets scale n nu, ∀ z : WaveSpaceTime,
        z.2 ∈ lightRayTimeInterval →
        (∫ xi : Euclidean 2,
          ‖mssFineCubeResidualSymbol D cubes hscale n nu cube z xi‖) ≤
          A * (cubes.cubeWidth * Real.sqrt scale) ^ 2) :
    ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
      ∀ cube ∈ cubes.cubeSets scale n nu, ∀ z : WaveSpaceTime, ∀ y : Euclidean 2,
        ‖mssFineCubeHalfWaveKernel D cubes scale n nu cube z y‖ ≤
          (T * (2 : Real) ^ N * A) *
            lightRayKernel (cubes.cubeWidth * Real.sqrt scale)⁻¹ N
              (D.directions scale nu) y z := by
  apply norm_mssFineCubeHalfWaveKernel_le_lightRayKernel_of_residual_seminorm
    D cubes N A T hwidth hslab hA htime
  · intro scale hscale n hn nu hnu cube hcube z hz
    let R : Real := cubes.cubeWidth * Real.sqrt scale
    have hδ : 0 < R⁻¹ := by
      dsimp [R]
      exact (cubeWidth_inv_mul_sqrt_pos_lt_half hwidth hscale).1
    have hR : 0 < R := inv_pos.mp hδ
    have hbound : (2 : Real) ^ N * ∑ j ∈ Finset.range (N + 1), R ^ j *
        ∫ xi : Euclidean 2,
          ‖iteratedFDeriv Real j
            (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
              Euclidean 2 → Complex) xi‖ ≤ A * R ^ 2 := by
      simpa only [R] using hderivativeN scale hscale n hn nu hnu cube hcube z hz
    have hseminorm : SchwartzMap.seminorm Complex N 0
        (FourierTransform.fourierInv
          (mssFineCubeResidualSymbol D cubes hscale n nu cube z) :
            SchwartzMap (Euclidean 2) Complex) ≤
        (A * ((R⁻¹)⁻¹) ^ 2) * (R⁻¹) ^ N := by
      calc
        SchwartzMap.seminorm Complex N 0
            (FourierTransform.fourierInv
              (mssFineCubeResidualSymbol D cubes hscale n nu cube z) :
                SchwartzMap (Euclidean 2) Complex) ≤
            (2 : Real) ^ N * (R⁻¹) ^ N *
              ∑ j ∈ Finset.range (N + 1), R ^ j *
                ∫ xi : Euclidean 2,
                  ‖iteratedFDeriv Real j
                    (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
                      Euclidean 2 → Complex) xi‖ :=
          fourierInv_seminorm_le_scaled_derivativeIntegrals
            (mssFineCubeResidualSymbol D cubes hscale n nu cube z) N hR
        _ = (R⁻¹) ^ N * ((2 : Real) ^ N *
              ∑ j ∈ Finset.range (N + 1), R ^ j *
                ∫ xi : Euclidean 2,
                  ‖iteratedFDeriv Real j
                    (mssFineCubeResidualSymbol D cubes hscale n nu cube z :
                      Euclidean 2 → Complex) xi‖) := by ring
        _ ≤ (R⁻¹) ^ N * (A * R ^ 2) :=
          mul_le_mul_of_nonneg_left hbound
            (pow_nonneg (inv_nonneg.mpr hR.le) N)
        _ = (A * ((R⁻¹)⁻¹) ^ 2) * (R⁻¹) ^ N := by
          rw [inv_inv]
          ring
    simpa only [R] using hseminorm
  · intro scale hscale n hn nu hnu cube hcube z hz
    let R : Real := cubes.cubeWidth * Real.sqrt scale
    have hsemi := mssFineCubeResidualSymbol_fourierInv_seminorm_le_derivativeIntegrals
      D cubes scale hscale n nu cube z 0
    have hsemi' : SchwartzMap.seminorm Complex 0 0
        (FourierTransform.fourierInv
          (mssFineCubeResidualSymbol D cubes hscale n nu cube z) :
            SchwartzMap (Euclidean 2) Complex) ≤
        ∫ xi : Euclidean 2,
          ‖mssFineCubeResidualSymbol D cubes hscale n nu cube z xi‖ := by
      simpa only [pow_zero, one_mul, Finset.sum_range_succ,
        Finset.sum_range_zero, norm_iteratedFDeriv_zero, zero_add] using hsemi
    have hbound : (∫ xi : Euclidean 2,
        ‖mssFineCubeResidualSymbol D cubes hscale n nu cube z xi‖) ≤ A * R ^ 2 := by
      simpa only [R] using hderivativeZero scale hscale n hn nu hnu cube hcube z hz
    have hseminorm : SchwartzMap.seminorm Complex 0 0
        (FourierTransform.fourierInv
          (mssFineCubeResidualSymbol D cubes hscale n nu cube z) :
            SchwartzMap (Euclidean 2) Complex) ≤ A * ((R⁻¹)⁻¹) ^ 2 := by
      calc
        SchwartzMap.seminorm Complex 0 0
            (FourierTransform.fourierInv
              (mssFineCubeResidualSymbol D cubes hscale n nu cube z) :
                SchwartzMap (Euclidean 2) Complex) ≤
            ∫ xi : Euclidean 2,
              ‖mssFineCubeResidualSymbol D cubes hscale n nu cube z xi‖ := hsemi'
        _ ≤ A * R ^ 2 := hbound
        _ = A * ((R⁻¹)⁻¹) ^ 2 := by rw [inv_inv]
    simpa only [R] using hseminorm

/-- Each literal fine-cube half-wave kernel is integrable in its source
variable.  This is automatic from its compact smooth frequency multiplier;
it does not use any packet membership or ray-localization hypothesis. -/
theorem integrable_mssFineCubeHalfWaveKernel
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (scale : Real) (hscale : 2 ≤ scale) (n nu : Int)
    (_hn : n ∈ relevantRadialIndexEnumeration scale)
    (_hnu : nu ∈ D.angularIndices scale)
    (cube : Fin (cubes.cubeCount scale))
    (_hcube : cube ∈ cubes.cubeSets scale n nu)
    (z : WaveSpaceTime) :
    Integrable (fun y : Euclidean 2 =>
      mssFineCubeHalfWaveKernel D cubes scale n nu cube z y) volume := by
  let m : SchwartzMap (Euclidean 2) Complex :=
    mssFineCubeSchwartzSymbol D cubes hscale n nu cube z
  have hraw_eq_m : (fun xi : Euclidean 2 =>
      cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
        halfWaveMultiplier WaveSign.plus z.2 xi) = fun xi => m xi := by
    funext xi
    symm
    exact mssFineCubeSchwartzSymbol_apply D cubes hscale n nu cube z xi
  have hsource : Integrable (fun y : Euclidean 2 =>
      Auto.Spherical.Auxiliary.fourierCubeSourceKernel m z.1 y) volume :=
    Auto.Spherical.Auxiliary.integrable_fourierCubeSourceKernel m z.1
  unfold mssFineCubeHalfWaveKernel
  rw [hraw_eq_m]
  simpa only [
    Auto.Spherical.Auxiliary.fourierCubeSourceKernel,
    Auto.Spherical.Auxiliary.fourierCubeKernel,
    SchwartzMap.fourierInv_coe] using
      hsource.const_mul (D.radialTime.time z.2)

/-- The literal fine-cube packet equals integration against its actual
half-wave source kernel.  Thus the corresponding two fields in
`MSSFineCubeKernelLocalization` are proved structural consequences rather
than additional localization assumptions. -/
theorem mssFineCubePacket_eq_integral_mssFineCubeHalfWaveKernel
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (scale : Real) (hscale : 2 ≤ scale) (n nu : Int)
    (_hn : n ∈ relevantRadialIndexEnumeration scale)
    (_hnu : nu ∈ D.angularIndices scale)
    (cube : Fin (cubes.cubeCount scale))
    (_hcube : cube ∈ cubes.cubeSets scale n nu)
    (f : SchwartzMap (Euclidean 2) Complex) (z : WaveSpaceTime) :
    mssFineCubePacket D cubes scale n nu cube f z =
      ∫ y : Euclidean 2,
        mssFineCubeHalfWaveKernel D cubes scale n nu cube z y * f y := by
  let m : SchwartzMap (Euclidean 2) Complex :=
    mssFineCubeSchwartzSymbol D cubes hscale n nu cube z
  have hsymbol : (fun xi : Euclidean 2 => m xi) =
      fun xi => cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
        halfWaveMultiplier WaveSign.plus z.2 xi := by
    funext xi
    exact mssFineCubeSchwartzSymbol_apply D cubes hscale n nu cube z xi
  have hsymbol' : (m : Euclidean 2 → Complex) =
      fun xi => cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
        halfWaveMultiplier WaveSign.plus z.2 xi := by
    exact hsymbol
  have hsource := Auto.Spherical.Auxiliary.fourierCubeProjection_eq_sourceKernel
    m f z.1
  unfold mssFineCubePacket
  change D.radialTime.time z.2 * FourierTransform.fourierInv
      (fun xi : Euclidean 2 =>
        cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
          FourierTransform.fourier (f : Euclidean 2 → Complex) xi *
            halfWaveMultiplier WaveSign.plus z.2 xi) z.1 = _
  calc
    D.radialTime.time z.2 * FourierTransform.fourierInv
        (fun xi : Euclidean 2 =>
          cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
            FourierTransform.fourier (f : Euclidean 2 → Complex) xi *
              halfWaveMultiplier WaveSign.plus z.2 xi) z.1 =
        D.radialTime.time z.2 * FourierTransform.fourierInv
          (fun xi : Euclidean 2 =>
            m xi * FourierTransform.fourier (f : Euclidean 2 → Complex) xi) z.1 := by
          apply congrArg (fun g : Euclidean 2 → Complex =>
            D.radialTime.time z.2 * FourierTransform.fourierInv g z.1)
          funext xi
          calc
            cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
                FourierTransform.fourier (f : Euclidean 2 → Complex) xi *
                  halfWaveMultiplier WaveSign.plus z.2 xi =
                (cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
                  halfWaveMultiplier WaveSign.plus z.2 xi) *
                    FourierTransform.fourier (f : Euclidean 2 → Complex) xi := by ring
            _ = m xi * FourierTransform.fourier (f : Euclidean 2 → Complex) xi := by
              rw [← congrFun hsymbol xi]
    _ = D.radialTime.time z.2 * ∫ y : Euclidean 2,
        Auto.Spherical.Auxiliary.fourierCubeSourceKernel m z.1 y * f y := by
          rw [hsource]
    _ = ∫ y : Euclidean 2,
        D.radialTime.time z.2 *
          (Auto.Spherical.Auxiliary.fourierCubeSourceKernel m z.1 y * f y) := by
          rw [← integral_const_mul]
    _ = ∫ y : Euclidean 2,
        mssFineCubeHalfWaveKernel D cubes scale n nu cube z y * f y := by
          apply integral_congr_ae
          filter_upwards with y
          unfold mssFineCubeHalfWaveKernel
          simp only [Auto.Spherical.Auxiliary.fourierCubeSourceKernel,
            Auto.Spherical.Auxiliary.fourierCubeKernel]
          rw [SchwartzMap.fourierInv_coe]
          rw [hsymbol']
          ring

/-- A literal light-ray pointwise bound supplies the only non-structural
field of fine-cube localization.  The source integrability and representation
are automatic from the compact smooth multiplier above, while the mass bound
comes from integrating the light-ray majorant. -/
theorem mssFineCubeKernelLocalization_of_lightRayDominance
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (κ : Real) (hκ : 0 < κ)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 2 < N)
    (hdom : ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
      ∀ cube ∈ cubes.cubeSets scale n nu, ∀ z : WaveSpaceTime, ∀ y : Euclidean 2,
        ‖mssFineCubeHalfWaveKernel D cubes scale n nu cube z y‖ ≤
          κ * lightRayKernel (cubes.cubeWidth * Real.sqrt scale)⁻¹ N
            (D.directions scale nu) y z) :
    MSSFineCubeKernelLocalization D cubes N κ
      (κ * ∫ u : Euclidean 2, lightRayDecayProfile N u) := by
  have hprofile : 0 ≤ ∫ u : Euclidean 2, lightRayDecayProfile N u :=
    (lightRayKernel_spatial_mass_bound (δ := (1 : Real)) (by norm_num) N hN
      (0 : Euclidean 2)).1
  refine
    { kernelConstant_pos := hκ
      massConstant_nonneg := mul_nonneg hκ.le hprofile
      source_integrable := ?_
      source_representation := ?_
      light_ray_dominance := hdom
      source_mass := ?_ }
  · intro scale hscale n hn nu hnu cube hcube z
    exact integrable_mssFineCubeHalfWaveKernel D cubes scale hscale n nu hn hnu cube hcube z
  · intro scale hscale n hn nu hnu cube hcube f z
    exact mssFineCubePacket_eq_integral_mssFineCubeHalfWaveKernel
      D cubes scale hscale n nu hn hnu cube hcube f z
  · intro scale hscale n hn nu hnu cube hcube z
    let δ : Real := (cubes.cubeWidth * Real.sqrt scale)⁻¹
    have hδ : 0 < δ :=
      (cubeWidth_inv_mul_sqrt_pos_lt_half hwidth hscale).1
    have hlight :=
      (lightRayKernel_spatial_mass_bound hδ N hN (D.directions scale nu)).2 z
    calc
      (∫ y : Euclidean 2,
          ‖mssFineCubeHalfWaveKernel D cubes scale n nu cube z y‖) ≤
          ∫ y : Euclidean 2,
            κ * lightRayKernel δ N (D.directions scale nu) y z := by
              apply integral_mono
              · exact (integrable_mssFineCubeHalfWaveKernel D cubes scale hscale n nu hn hnu
                  cube hcube z).norm
              · exact hlight.1.const_mul κ
              · intro y
                simpa only [δ] using hdom scale hscale n hn nu hnu cube hcube z y
      _ = κ * ∫ y : Euclidean 2,
          lightRayKernel δ N (D.directions scale nu) y z := by
            rw [integral_const_mul]
      _ ≤ κ * ∫ u : Euclidean 2, lightRayDecayProfile N u :=
        mul_le_mul_of_nonneg_left hlight.2 hκ.le

/-- The canonical fine cubes therefore satisfy the literal light-ray kernel
localization interface, with no residual-kernel estimate assumed as data. -/
private theorem exists_mssCanonicalFineCubeKernelLocalization
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData)
    (uniform : MSSFineSpatialProfileUniformRegularity D)
    (hslab : D.HasLightRayTimeSlabSupport) :
    ∃ kernelConstant massConstant : Real, 0 < kernelConstant ∧
      MSSFineCubeKernelLocalization D (mssCanonicalCubeDecomposition D H) 4
        kernelConstant massConstant := by
  obtain ⟨Araw, hAraw0, hscaled⟩ :=
    exists_mssCanonicalCubeResidual_scaledDerivativeIntegralBound D H uniform 4
  obtain ⟨S, hS0, hderiv⟩ :=
    exists_mssCanonicalCubeResidualDerivativeIntegralBound D H uniform 4
  let A : Real := Araw + S 0 + 1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    linarith [hAraw0, hS0 0]
  have hAraw_le : Araw ≤ A := by
    dsimp [A]
    linarith [hS0 0]
  have hSzero_le : S 0 ≤ A := by
    dsimp [A]
    linarith [hAraw0]
  obtain ⟨T, hT0, htime⟩ := exists_uniform_mssFineTime_norm_bound D
  let κ : Real := T * (2 : Real) ^ 4 * A + 1
  have hκ : 0 < κ := by
    dsimp [κ]
    have hprod : 0 ≤ T * (2 : Real) ^ 4 * A := by
      exact mul_nonneg (mul_nonneg hT0 (pow_nonneg (by norm_num) _)) hA0
    linarith
  refine ⟨κ, κ * ∫ u : Euclidean 2, lightRayDecayProfile 4 u, hκ, ?_⟩
  apply mssFineCubeKernelLocalization_of_lightRayDominance
    D (mssCanonicalCubeDecomposition D H) 4 κ hκ
    (mssCanonicalCubeDecomposition_hwidth D H) (by norm_num)
  intro scale hscale n hn nu hnu cube hcube z y
  have hkernel := norm_mssFineCubeHalfWaveKernel_le_lightRayKernel_of_residual_scaledDerivativeIntegrals
    D (mssCanonicalCubeDecomposition D H) 4 A T
    (mssCanonicalCubeDecomposition_hwidth D H) hslab hA0 htime
    (by
      intro scale hscale n hn nu hnu cube hcube z hz
      have hraw := hscaled scale hscale n hn nu hnu cube hcube z hz
      exact hraw.trans
        (mul_le_mul_of_nonneg_right hAraw_le (sq_nonneg _)))
    (by
      intro scale hscale n hn nu hnu cube hcube z hz
      have hzero := hderiv scale n nu cube z 0 hscale hn hnu hz (Nat.zero_le 4)
      have hwidth : (mssCanonicalCubeDecomposition D H).cubeWidth = 2 := by rfl
      have hsquare_le : (Real.sqrt scale) ^ 2 ≤ (2 * Real.sqrt scale) ^ 2 := by
        nlinarith [sq_nonneg (Real.sqrt scale)]
      calc
        (∫ xi : Euclidean 2,
          ‖mssFineCubeResidualSymbol D (mssCanonicalCubeDecomposition D H)
            hscale n nu cube z xi‖) =
            ∫ xi : Euclidean 2,
              ‖iteratedFDeriv Real 0
                (mssFineCubeResidualSymbol D (mssCanonicalCubeDecomposition D H)
                  hscale n nu cube z : Euclidean 2 → Complex) xi‖ := by
              simp
        _ ≤ S 0 * (Real.sqrt scale) ^ 2 := by
          simpa only [pow_zero, mul_one] using hzero
        _ ≤ A * (Real.sqrt scale) ^ 2 :=
          mul_le_mul_of_nonneg_right hSzero_le (sq_nonneg _)
        _ ≤ A * (2 * Real.sqrt scale) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare_le hA0
        _ = A * ((mssCanonicalCubeDecomposition D H).cubeWidth *
            Real.sqrt scale) ^ 2 := by rw [hwidth])
    scale hscale n hn nu hnu cube hcube z y
  have hlight : 0 ≤ lightRayKernel
      ((mssCanonicalCubeDecomposition D H).cubeWidth * Real.sqrt scale)⁻¹ 4
        (D.directions scale nu) y z := by
    unfold lightRayKernel
    positivity
  calc
    ‖mssFineCubeHalfWaveKernel D (mssCanonicalCubeDecomposition D H)
        scale n nu cube z y‖ ≤
        (T * (2 : Real) ^ 4 * A) * lightRayKernel
          ((mssCanonicalCubeDecomposition D H).cubeWidth * Real.sqrt scale)⁻¹ 4
            (D.directions scale nu) y z := hkernel
    _ ≤ κ * lightRayKernel
        ((mssCanonicalCubeDecomposition D H).cubeWidth * Real.sqrt scale)⁻¹ 4
          (D.directions scale nu) y z := by
      apply mul_le_mul_of_nonneg_right
      · dsimp [κ]
        linarith
      · exact hlight

/-- The logarithmic loss at a fine cube's natural physical width is absorbed
by an arbitrary positive power of the MSS scale.  This is the exact
scale-loss conversion used after taking the fourth root of the light-ray
maximal bound. -/
theorem exists_lightRayWidth_log_rpow_bound {w : Real} (hw : 0 < w) :
    ∀ eta : Real, 0 < eta → ∃ C : Real, 0 < C ∧
      ∀ scale : Real, 2 ≤ scale →
        (1 + |Real.log ((w * Real.sqrt scale)⁻¹)|) ^ (3 / 4 : Real) ≤
          C * scale ^ eta := by
  intro eta heta
  let epsilon : Real := 4 * eta / 3
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  let W : Real := 1 + |Real.log w|
  have hWpos : 0 < W := by
    dsimp [W]
    positivity
  let C : Real := (W * (1 + epsilon⁻¹)) ^ (3 / 4 : Real)
  have hCpos : 0 < C := by
    dsimp [C]
    have : 0 < W * (1 + epsilon⁻¹) := by
      have hinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
      positivity
    exact Real.rpow_pos_of_pos this _
  refine ⟨C, hCpos, ?_⟩
  intro scale hscale
  have hscaleOne : 1 ≤ scale := by linarith
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscaleOne
  have hsqrtPos : 0 < Real.sqrt scale := Real.sqrt_pos.2 hscalePos
  have hlogNonneg : 0 ≤ Real.log scale := Real.log_nonneg hscaleOne
  have hlog : Real.log ((w * Real.sqrt scale)⁻¹) =
      -(Real.log w + Real.log scale / 2) := by
    rw [Real.log_inv, Real.log_mul hw.ne' hsqrtPos.ne', Real.log_sqrt hscalePos.le]
  have habs : |Real.log ((w * Real.sqrt scale)⁻¹)| ≤
      |Real.log w| + Real.log scale / 2 := by
    rw [hlog, abs_neg]
    calc
      |Real.log w + Real.log scale / 2| ≤
          |Real.log w| + |Real.log scale / 2| := abs_add_le _ _
      _ = |Real.log w| + Real.log scale / 2 := by
        rw [abs_of_nonneg (div_nonneg hlogNonneg (by norm_num))]
  have hbase : 1 + |Real.log ((w * Real.sqrt scale)⁻¹)| ≤
      W * (1 + Real.log scale) := by
    dsimp [W]
    have hproduct : 0 ≤ |Real.log w| * Real.log scale :=
      mul_nonneg (abs_nonneg _) hlogNonneg
    nlinarith
  have hlogPow : 1 + Real.log scale ≤
      (1 + epsilon⁻¹) * scale ^ epsilon :=
    one_add_log_le_rpow hscaleOne hepsilon
  have hlarge : 1 + |Real.log ((w * Real.sqrt scale)⁻¹)| ≤
      (W * (1 + epsilon⁻¹)) * scale ^ epsilon := by
    calc
      1 + |Real.log ((w * Real.sqrt scale)⁻¹)| ≤ W * (1 + Real.log scale) := hbase
      _ ≤ W * ((1 + epsilon⁻¹) * scale ^ epsilon) := by
        exact mul_le_mul_of_nonneg_left hlogPow hWpos.le
      _ = (W * (1 + epsilon⁻¹)) * scale ^ epsilon := by ring
  have hleftNonneg : 0 ≤ 1 + |Real.log ((w * Real.sqrt scale)⁻¹)| := by positivity
  have hrightNonneg : 0 ≤ (W * (1 + epsilon⁻¹)) * scale ^ epsilon := by
    positivity
  have hroot := Real.rpow_le_rpow hleftNonneg hlarge
    (by norm_num : (0 : Real) ≤ 3 / 4)
  calc
    (1 + |Real.log ((w * Real.sqrt scale)⁻¹)|) ^ (3 / 4 : Real) ≤
        ((W * (1 + epsilon⁻¹)) * scale ^ epsilon) ^ (3 / 4 : Real) := hroot
    _ = (W * (1 + epsilon⁻¹)) ^ (3 / 4 : Real) *
          (scale ^ epsilon) ^ (3 / 4 : Real) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
    _ = C * scale ^ eta := by
        dsimp [C]
        rw [← Real.rpow_mul hscalePos.le]
        congr 2
        dsimp [epsilon]
        ring

/-- Squaring the fourth-root logarithmic loss gives the exact power which
occurs in the fourth-moment light-ray bound. -/
private theorem exists_lightRayWidth_log_three_halves_le_square_scale
    {w : Real} (hw : 0 < w) :
    ∀ eta : Real, 0 < eta → ∃ C : Real, 0 < C ∧
      ∀ scale : Real, 2 ≤ scale →
        (1 + |Real.log ((w * Real.sqrt scale)⁻¹)|) ^ (3 / 2 : Real) ≤
          (C * scale ^ eta) ^ 2 := by
  intro eta heta
  obtain ⟨C, hC, hbound⟩ := exists_lightRayWidth_log_rpow_bound hw eta heta
  refine ⟨C, hC, ?_⟩
  intro scale hscale
  let L : Real := 1 + |Real.log ((w * Real.sqrt scale)⁻¹)|
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  have hroot : L ^ (3 / 4 : Real) ≤ C * scale ^ eta := by
    simpa only [L] using hbound scale hscale
  have hright : 0 ≤ C * scale ^ eta := by positivity
  have hsquare : (L ^ (3 / 4 : Real)) ^ 2 ≤ (C * scale ^ eta) ^ 2 :=
    (sq_le_sq₀ (Real.rpow_nonneg hLpos.le _) hright).mpr hroot
  have hpow : L ^ (3 / 2 : Real) = (L ^ (3 / 4 : Real)) ^ 2 := by
    calc
      L ^ (3 / 2 : Real) = L ^ ((3 / 4 : Real) + (3 / 4 : Real)) := by norm_num
      _ = L ^ (3 / 4 : Real) * L ^ (3 / 4 : Real) := Real.rpow_add hLpos _ _
      _ = (L ^ (3 / 4 : Real)) ^ 2 := by ring
  change L ^ (3 / 2 : Real) ≤ (C * scale ^ eta) ^ 2
  rw [hpow]
  exact hsquare

/-- A permissible literal dual test for the light-ray estimate.  Besides the
ambient `L²` condition demanded by the maximal estimate, it has literal slab
support, a uniform bound, and compact spatial support. -/
structure LightRayBoundedCompactTest (g : WaveSpaceTime → Complex) : Prop where
  memLp_two : MemLp g 2 volume
  slab : g = (Set.univ ×ˢ lightRayTimeInterval).indicator g
  bounded : ∃ B : Real, 0 ≤ B ∧ ∀ z, ‖g z‖ ≤ B
  compact_spatial : ∃ R : Real, ∀ z, R < ‖z.1‖ → g z = 0

/-- A literal slab-supported test with compact spatial support has genuinely
compact space-time support. -/
theorem LightRayBoundedCompactTest.hasCompactSupport
    {g : WaveSpaceTime → Complex} (hg : LightRayBoundedCompactTest g) :
    HasCompactSupport g := by
  obtain ⟨R, hR⟩ := hg.compact_spatial
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_closedBall (0 : Euclidean 2) R).prod
      (show IsCompact lightRayTimeInterval by
        unfold lightRayTimeInterval
        exact isCompact_Icc))
  intro z hz
  have hspatial : ‖z.1‖ ≤ R := by
    by_contra hnot
    apply hz
    exact hR z (lt_of_not_ge hnot)
  have htime : z.2 ∈ lightRayTimeInterval := by
    by_contra hnot
    apply hz
    rw [hg.slab]
    simp [hnot]
  change z.1 ∈ Metric.closedBall (0 : Euclidean 2) R ∧
    z.2 ∈ lightRayTimeInterval
  constructor
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hspatial
  · exact htime

/-- The norm of a bounded compact literal-slab test is integrable for the
continuum light-ray measure. -/
theorem LightRayBoundedCompactTest.integrable_norm_continuumLightRayMeasure
    {g : WaveSpaceTime → Complex} (hg : LightRayBoundedCompactTest g) :
    Integrable (fun z : WaveSpaceTime => ‖g z‖) continuumLightRayMeasure := by
  obtain ⟨B, hBnonneg, hB⟩ := hg.bounded
  have hmemOne : MemLp g 1 volume :=
    hg.hasCompactSupport.memLp_of_bound hg.memLp_two.aestronglyMeasurable B
      (Filter.Eventually.of_forall hB)
  have hnormVolume : Integrable (fun z : WaveSpaceTime => ‖g z‖) volume :=
    (memLp_one_iff_integrable.mp hmemOne).norm
  simpa only [continuumLightRayMeasure, scratchLightRayMeasure] using
    hnormVolume.mono_measure scratchLightRayMeasure_le_volume

/-- A continuous real multiplier remains integrable after pairing with a
bounded compact literal-slab test. -/
theorem LightRayBoundedCompactTest.integrable_mul_norm_of_continuous
    {g : WaveSpaceTime → Complex} (hg : LightRayBoundedCompactTest g)
    {F : WaveSpaceTime → Real} (hF : Continuous F) :
    Integrable (fun z : WaveSpaceTime => F z * ‖g z‖)
      continuumLightRayMeasure := by
  obtain ⟨R, hR⟩ := hg.compact_spatial
  let K : Set WaveSpaceTime :=
    Metric.closedBall (0 : Euclidean 2) R ×ˢ lightRayTimeInterval
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_closedBall (0 : Euclidean 2) R).prod (by
      unfold lightRayTimeInterval
      exact isCompact_Icc)
  obtain ⟨C, hC⟩ := hKcompact.bddAbove_image hF.norm.continuousOn
  have hFC : ∀ z ∈ K, ‖F z‖ ≤ max C 0 := by
    intro z hz
    exact (hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hgzero : ∀ z : WaveSpaceTime, z ∉ K → g z = 0 := by
    intro z hz
    by_cases htime : z.2 ∈ lightRayTimeInterval
    · apply hR z
      apply lt_of_not_ge
      intro hle
      apply hz
      change z.1 ∈ Metric.closedBall (0 : Euclidean 2) R ∧
        z.2 ∈ lightRayTimeInterval
      exact ⟨by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hle, htime⟩
    · rw [hg.slab]
      simp [htime]
  have hgnorm := hg.integrable_norm_continuumLightRayMeasure
  refine (hgnorm.const_mul (max C 0)).mono' ?_ ?_
  · exact hF.aestronglyMeasurable.mul hgnorm.aestronglyMeasurable
  · filter_upwards with z
    by_cases hz : z ∈ K
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using hFC z hz) (norm_nonneg _)
    · rw [hgzero z hz]
      norm_num

/-- A literal fine cube packet is jointly continuous in physical space and
time.  The inverse Fourier integral is controlled by the integrable Schwartz
frequency product, uniformly in the unimodular half-wave phase. -/
theorem continuous_mssFineCubePacket
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (scale : Real) (n nu : Int) (cube : Fin (cubes.cubeCount scale))
    (f : SchwartzMap (Euclidean 2) Complex) :
    Continuous (mssFineCubePacket D cubes scale n nu cube f) := by
  let B : SchwartzMap (Euclidean 2) Complex :=
    SchwartzMap.smulLeftCLM Complex
      (cubes.cutoff scale cube : Euclidean 2 → Complex)
      (SchwartzMap.smulLeftCLM Complex
        (D.spatialProfile scale n nu : Euclidean 2 → Complex)
        (FourierTransform.fourier f))
  have hB : ∀ xi : Euclidean 2, B xi =
      cubes.cutoff scale cube xi * D.spatialProfile scale n nu xi *
        FourierTransform.fourier (f : Euclidean 2 → Complex) xi := by
    intro xi
    simp only [B,
      SchwartzMap.smulLeftCLM_apply
        (cubes.cutoff scale cube).hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply
        (D.spatialProfile scale n nu).hasTemperateGrowth,
      smul_eq_mul, SchwartzMap.fourier_coe]
    ring
  let m : Real → Euclidean 2 → Complex := fun t xi =>
    B xi * halfWaveMultiplier WaveSign.plus t xi
  let U : Real × Euclidean 2 → Complex := fun p =>
    FourierTransform.fourierInv (m p.1) p.2
  have hU : Continuous U := by
    change Continuous (Function.uncurry (fun t x =>
      FourierTransform.fourierInv (m t) x))
    apply Auto.Spherical.MSSKakeya.continuous_uncurry_fourierInv_of_dominated m
      (bound := fun xi => ‖B xi‖)
    · intro xi
      have hphase : Continuous (fun p : Real × Euclidean 2 =>
          (Real.fourierChar (inner Real xi p.2) : Complex)) := by
        fun_prop
      have hm : Continuous (fun p : Real × Euclidean 2 => m p.1 xi) := by
        change Continuous (fun p : Real × Euclidean 2 =>
          B xi * halfWaveMultiplier WaveSign.plus p.1 xi)
        exact continuous_const.mul (by
          unfold halfWaveMultiplier
          fun_prop)
      exact hphase.smul hm
    · intro p
      have hphase : Continuous (fun xi : Euclidean 2 =>
          (Real.fourierChar (inner Real xi p.2) : Complex)) := by
        fun_prop
      have hm : Continuous (fun xi : Euclidean 2 => m p.1 xi) := by
        change Continuous (fun xi : Euclidean 2 =>
          B xi * halfWaveMultiplier WaveSign.plus p.1 xi)
        have hhalf : Continuous (halfWaveMultiplier WaveSign.plus p.1) := by
          unfold halfWaveMultiplier
          fun_prop
        exact B.continuous.mul hhalf
      exact (hphase.smul hm).aestronglyMeasurable
    · intro p xi
      have hchar (u : Real) : ‖(Real.fourierChar u : Complex)‖ = 1 := by
        rw [Real.fourierChar_apply, Complex.norm_exp]
        norm_num
      change ‖(Real.fourierChar (inner Real xi p.2) : Complex) •
        (B xi * halfWaveMultiplier WaveSign.plus p.1 xi)‖ ≤ ‖B xi‖
      rw [norm_smul, hchar, one_mul, norm_mul,
        norm_halfWaveMultiplier, mul_one]
    · exact B.integrable.norm
  have hrepr : mssFineCubePacket D cubes scale n nu cube f =
      fun z => D.radialTime.time z.2 * U (z.2, z.1) := by
    funext z
    unfold U
    unfold mssFineCubePacket
    apply congrArg (fun h : Euclidean 2 → Complex =>
      D.radialTime.time z.2 * FourierTransform.fourierInv h z.1)
    funext xi
    dsimp [m]
    rw [hB xi]
  rw [hrepr]
  have hswap : Continuous (fun z : WaveSpaceTime => (z.2, z.1)) :=
    continuous_snd.prodMk continuous_fst
  have hUspace : Continuous (fun z : WaveSpaceTime => U (z.2, z.1)) :=
    hU.comp hswap
  have htime : Continuous (fun z : WaveSpaceTime => D.radialTime.time z.2) :=
    D.radialTime.time.continuous.comp continuous_snd
  exact htime.mul hUspace

/-- Squaring the finite fine cube-packet square function removes the outer
square root, leaving a finite sum of continuous packet energies. -/
theorem continuous_sq_mssFineCubePacketSquareFunction
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (scale : Real) (f : SchwartzMap (Euclidean 2) Complex) :
    Continuous (fun z : WaveSpaceTime =>
      mssFineCubePacketSquareFunction D cubes scale f z ^ 2) := by
  classical
  have hsum (n nu : Int) : Continuous (fun z : WaveSpaceTime =>
      ∑ cube ∈ cubes.cubeSets scale n nu,
        mssFineCubePacket D cubes scale n nu cube
          (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
            (cubes.analysisCutoff scale cube) f) z) := by
    apply continuous_finsetSum
    intro cube hcube
    exact continuous_mssFineCubePacket D cubes scale n nu cube
      (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
        (cubes.analysisCutoff scale cube) f)
  have hpieces : Continuous (fun z : WaveSpaceTime =>
      ∑ n ∈ relevantRadialIndexEnumeration scale,
        ∑ nu ∈ D.angularIndices scale,
          ‖∑ cube ∈ cubes.cubeSets scale n nu,
            mssFineCubePacket D cubes scale n nu cube
              (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
                (cubes.analysisCutoff scale cube) f) z‖ ^ 2) := by
    apply continuous_finsetSum
    intro n hn
    apply continuous_finsetSum
    intro nu hnu
    exact (hsum n nu).norm.pow 2
  convert hpieces using 1
  funext z
  exact sq_mssFineCubePacketSquareFunction D cubes scale f z

/-- Under the explicit physical-time support condition, every summand in the
finite MSS packet square vanishes outside the light-ray time slab, hence so
does the square function itself. -/
theorem mssFineCubePacketSquareFunction_eq_zero_of_time_not_mem_lightRayTimeInterval
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (hslab : D.HasLightRayTimeSlabSupport)
    (scale : Real) (f : SchwartzMap (Euclidean 2) Complex) (z : WaveSpaceTime)
    (hz : z.2 ∉ lightRayTimeInterval) :
    mssFineCubePacketSquareFunction D cubes scale f z = 0 := by
  have hpacket (n nu : Int) (cube : Fin (cubes.cubeCount scale)) :
      mssFineCubePacket D cubes scale n nu cube
          (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
            (cubes.analysisCutoff scale cube) f) z = 0 :=
    mssFineCubePacket_eq_zero_of_time_not_mem_lightRayTimeInterval
      D cubes hslab scale n nu cube
        (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
          (cubes.analysisCutoff scale cube) f) z hz
  simp [mssFineCubePacketSquareFunction, hpacket]

/-- Literal indicator form of the preceding time-slab support statement.
This is the form consumed by bounded compact light-ray dual tests. -/
theorem mssFineCubePacketSquareFunction_eq_indicator_lightRayTimeSlab
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (hslab : D.HasLightRayTimeSlabSupport)
    (scale : Real) (f : SchwartzMap (Euclidean 2) Complex) :
    (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z) =
      (Set.univ ×ˢ lightRayTimeInterval).indicator
        (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z) := by
  funext z
  by_cases hz : z.2 ∈ lightRayTimeInterval
  · simp [hz]
  · have hzero :=
      mssFineCubePacketSquareFunction_eq_zero_of_time_not_mem_lightRayTimeInterval
        D cubes hslab scale f z hz
    simp [hz, hzero]

/-- The squared MSS packet square has the same literal light-ray slab support.
It is the target-side support fact needed when forming bounded compact dual
truncations of the nonnegative square. -/
theorem sq_mssFineCubePacketSquareFunction_eq_indicator_lightRayTimeSlab
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (hslab : D.HasLightRayTimeSlabSupport)
    (scale : Real) (f : SchwartzMap (Euclidean 2) Complex) :
    (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) =
      (Set.univ ×ˢ lightRayTimeInterval).indicator
        (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) := by
  funext z
  by_cases hz : z.2 ∈ lightRayTimeInterval
  · simp [hz]
  · have hzero :=
      mssFineCubePacketSquareFunction_eq_zero_of_time_not_mem_lightRayTimeInterval
        D cubes hslab scale f z hz
    simp [hz, hzero]

/-- A function with literal time-slab support has the same square energy for
ambient volume as for `continuumLightRayMeasure`. -/
theorem integral_sq_norm_eq_integral_sq_norm_continuumLightRayMeasure_of_slab
    (g : WaveSpaceTime → Complex)
    (hslab : g = (Set.univ ×ˢ lightRayTimeInterval).indicator g) :
    (∫ z : WaveSpaceTime, ‖g z‖ ^ 2) =
      ∫ z : WaveSpaceTime, ‖g z‖ ^ 2 ∂continuumLightRayMeasure := by
  let slab : Set WaveSpaceTime := Set.univ ×ˢ lightRayTimeInterval
  have hslabMeas : MeasurableSet slab := by
    dsimp [slab]
    exact MeasurableSet.univ.prod (by
      unfold lightRayTimeInterval
      exact measurableSet_Icc)
  have hmeasure :
      continuumLightRayMeasure = (volume : Measure WaveSpaceTime).restrict slab := by
    unfold continuumLightRayMeasure
    change (volume : Measure (Euclidean 2)).prod
        ((volume : Measure Real).restrict lightRayTimeInterval) =
      ((volume : Measure (Euclidean 2)).prod (volume : Measure Real)).restrict
        (Set.univ ×ˢ lightRayTimeInterval)
    rw [← Measure.prod_restrict]
    simp
  have hslab' : g = slab.indicator g := by
    simpa only [slab] using hslab
  have hnormIndicator :
      (fun z : WaveSpaceTime => ‖g z‖ ^ 2) =
        slab.indicator (fun z : WaveSpaceTime => ‖g z‖ ^ 2) := by
    funext z
    by_cases hz : z ∈ slab
    · simp [hz]
    · have hz0 : g z = 0 := by
        rw [hslab']
        simp [hz]
      simp [hz, hz0]
  calc
    (∫ z : WaveSpaceTime, ‖g z‖ ^ 2) =
        ∫ z : WaveSpaceTime, slab.indicator (fun z : WaveSpaceTime => ‖g z‖ ^ 2) z := by
      apply integral_congr_ae
      filter_upwards with z
      exact congrFun hnormIndicator z
    _ = ∫ z : WaveSpaceTime in slab, ‖g z‖ ^ 2 :=
      integral_indicator hslabMeas
    _ = ∫ z : WaveSpaceTime, ‖g z‖ ^ 2 ∂continuumLightRayMeasure := by
      rw [hmeasure]

/-- One HLE constant controls every admissible light-ray width and every
bounded compact literal-slab test, with the energy measured in ambient
volume. -/
theorem exists_uniform_lightRayMaximal_sq_bound_on_boundedCompactTests
    (N : Nat) (hN : 3 < N) :
    ∃ C : Real, 0 < C ∧
      ∀ {δ : Real}, 0 < δ → δ < 1 / 2 →
      ∀ g : WaveSpaceTime → Complex, LightRayBoundedCompactTest g →
        MemLp (lightRayMaximal δ N g) 2 volume ∧
          Integrable (fun y : Euclidean 2 => lightRayMaximal δ N g y ^ 2) volume ∧
          (∫ y : Euclidean 2, lightRayMaximal δ N g y ^ 2) ≤
            (C * (1 + |Real.log δ|) ^ (3 / 2 : Real)) ^ 2 *
              ∫ z : WaveSpaceTime, ‖g z‖ ^ 2 := by
  obtain ⟨C, hC, hmax⟩ := hasLightRayMaximalEstimate N hN
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδsmall g hg
  have hN' : 1 < N := by omega
  let K : Real := C * (1 + |Real.log δ|) ^ (3 / 2 : Real)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hmaxBound :
      eLpNorm (lightRayMaximal δ N g) 2 volume ≤
        ENNReal.ofReal K * eLpNorm g 2 volume := by
    simpa only [K] using hmax δ hδ hδsmall g hg.memLp_two
  have hmaxMeas : AEStronglyMeasurable (lightRayMaximal δ N g) volume :=
    (scratch_measurable_lightRayMaximal_of_memLp hδ N hN' g hg.memLp_two).aestronglyMeasurable
  have hmaxTop : eLpNorm (lightRayMaximal δ N g) 2 volume < ∞ :=
    lt_of_le_of_lt hmaxBound
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.memLp_two.eLpNorm_lt_top)
  have hmaxMem : MemLp (lightRayMaximal δ N g) 2 volume :=
    ⟨hmaxMeas, hmaxTop⟩
  have hmaxTwo : Integrable (fun y : Euclidean 2 => lightRayMaximal δ N g y ^ 2) volume :=
    (memLp_two_iff_integrable_sq hmaxMeas).mp hmaxMem
  let Iout : Real := ∫ y : Euclidean 2, lightRayMaximal δ N g y ^ 2
  let Iin : Real := ∫ z : WaveSpaceTime, ‖g z‖ ^ 2
  have hIout : 0 ≤ Iout := by
    dsimp [Iout]
    exact integral_nonneg fun y => sq_nonneg _
  have hIin : 0 ≤ Iin := by
    dsimp [Iin]
    exact integral_nonneg fun z => pow_nonneg (norm_nonneg _) _
  have hnormOut :
      eLpNorm (lightRayMaximal δ N g) 2 volume =
        ENNReal.ofReal (Iout ^ (2 : Real)⁻¹) := by
    rw [hmaxMem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    norm_num [Iout, Real.norm_eq_abs]
  have hnormIn : eLpNorm g 2 volume = ENNReal.ofReal (Iin ^ (2 : Real)⁻¹) := by
    rw [hg.memLp_two.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    norm_num [Iin]
  have hrootENN :
      ENNReal.ofReal (Iout ^ (2 : Real)⁻¹) ≤
        ENNReal.ofReal (K * Iin ^ (2 : Real)⁻¹) := by
    calc
      ENNReal.ofReal (Iout ^ (2 : Real)⁻¹) =
          eLpNorm (lightRayMaximal δ N g) 2 volume := hnormOut.symm
      _ ≤ ENNReal.ofReal K * eLpNorm g 2 volume := hmaxBound
      _ = ENNReal.ofReal K * ENNReal.ofReal (Iin ^ (2 : Real)⁻¹) := by
        rw [hnormIn]
      _ = ENNReal.ofReal (K * Iin ^ (2 : Real)⁻¹) :=
        (ENNReal.ofReal_mul hK).symm
  have hrootRight : 0 ≤ K * Iin ^ (2 : Real)⁻¹ :=
    mul_nonneg hK (Real.rpow_nonneg hIin _)
  have hroot : Iout ^ (2 : Real)⁻¹ ≤ K * Iin ^ (2 : Real)⁻¹ :=
    (ENNReal.ofReal_le_ofReal_iff hrootRight).mp hrootENN
  have hsq : (Iout ^ (2 : Real)⁻¹) ^ 2 ≤ (K * Iin ^ (2 : Real)⁻¹) ^ 2 :=
    (sq_le_sq₀ (Real.rpow_nonneg hIout _) hrootRight).mpr hroot
  have hrootSqOut : (Iout ^ (2 : Real)⁻¹) ^ 2 = Iout := by
    rw [show (2 : Real)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hIout
  have hrootSqIn : (Iin ^ (2 : Real)⁻¹) ^ 2 = Iin := by
    rw [show (2 : Real)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hIin
  have henergy : Iout ≤ K ^ 2 * Iin := by
    calc
      Iout = (Iout ^ (2 : Real)⁻¹) ^ 2 := hrootSqOut.symm
      _ ≤ (K * Iin ^ (2 : Real)⁻¹) ^ 2 := hsq
      _ = K ^ 2 * Iin := by rw [mul_pow, hrootSqIn]
  have hslabEnergy : Iin =
      ∫ z : WaveSpaceTime, ‖g z‖ ^ 2 ∂continuumLightRayMeasure := by
    simpa only [Iin] using
      integral_sq_norm_eq_integral_sq_norm_continuumLightRayMeasure_of_slab g hg.slab
  have henergySlab : Iout ≤ K ^ 2 *
      ∫ z : WaveSpaceTime, ‖g z‖ ^ 2 ∂continuumLightRayMeasure := by
    calc
      Iout ≤ K ^ 2 * Iin := henergy
      _ = K ^ 2 * ∫ z : WaveSpaceTime, ‖g z‖ ^ 2 ∂continuumLightRayMeasure := by
        rw [hslabEnergy]
  refine ⟨hmaxMem, hmaxTwo, ?_⟩
  change Iout ≤ K ^ 2 * ∫ z : WaveSpaceTime, ‖g z‖ ^ 2
  calc
    Iout ≤ K ^ 2 * ∫ z : WaveSpaceTime, ‖g z‖ ^ 2 ∂continuumLightRayMeasure := henergySlab
    _ = K ^ 2 * ∫ z : WaveSpaceTime, ‖g z‖ ^ 2 := by
      rw [← hslabEnergy]

/-- Norm-form restatement of the width-uniform squared light-ray bound.  This
is the form consumed directly by the Cauchy--Schwarz/truncated-duality
closure. -/
theorem exists_uniform_lightRayMaximal_norm_sq_bound_on_boundedCompactTests
    (N : Nat) (hN : 3 < N) :
    ∃ C : Real, 0 < C ∧
      ∀ {δ : Real}, 0 < δ → δ < 1 / 2 →
      ∀ g : WaveSpaceTime → Complex, LightRayBoundedCompactTest g →
        MemLp (lightRayMaximal δ N g) 2 volume ∧
          Integrable (fun y : Euclidean 2 => ‖lightRayMaximal δ N g y‖ ^ 2) volume ∧
          (∫ y : Euclidean 2, ‖lightRayMaximal δ N g y‖ ^ 2) ≤
            (C * (1 + |Real.log δ|) ^ (3 / 2 : Real)) ^ 2 *
              ∫ z : WaveSpaceTime, ‖g z‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_lightRayMaximal_sq_bound_on_boundedCompactTests N hN
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδsmall g hg
  obtain ⟨hmem, hint, henergy⟩ := hbound hδ hδsmall g hg
  have hN' : 1 < N := by omega
  have hnonneg : ∀ y : Euclidean 2, 0 ≤ lightRayMaximal δ N g y :=
    fun y => scratch_lightRayMaximal_nonneg_of_memLp hδ N hN' g hg.memLp_two y
  have hnormEq : (fun y : Euclidean 2 => ‖lightRayMaximal δ N g y‖ ^ 2) =
      fun y : Euclidean 2 => lightRayMaximal δ N g y ^ 2 := by
    funext y
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg y)]
  refine ⟨hmem, ?_, ?_⟩
  · refine hint.congr ?_
    filter_upwards with y
    exact (congrFun hnormEq y).symm
  · calc
      (∫ y : Euclidean 2, ‖lightRayMaximal δ N g y‖ ^ 2) =
          ∫ y : Euclidean 2, lightRayMaximal δ N g y ^ 2 := by
        apply integral_congr_ae
        filter_upwards with y
        exact congrFun hnormEq y
      _ ≤ (C * (1 + |Real.log δ|) ^ (3 / 2 : Real)) ^ 2 *
          ∫ z : WaveSpaceTime, ‖g z‖ ^ 2 := henergy

/-- The global energy of the normalized cube inputs is exactly the squared
Fourier-cube square function of the enlarged analysis family, up to the
explicit normalization factor.  This is only finite algebra; it does not use
an `L⁴` cube multiplier estimate. -/
theorem continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (kernelConstant scale : Real) (f : SchwartzMap (Euclidean 2) Complex)
    (y : Euclidean 2) :
    continuumFineCubeSquareEnergy
        (mssFinePieceIndices D scale)
        (fun piece => cubes.cubeSets scale piece.1 piece.2)
        (fun cube =>
          mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y =
      ‖(kernelConstant : Complex)‖ ^ 2 *
        fourierCubeSquareFunction
          ((mssFinePieceIndices D scale).biUnion
            (fun piece => cubes.cubeSets scale piece.1 piece.2))
          (cubes.analysisCutoff scale) f y ^ 2 := by
  classical
  unfold continuumFineCubeSquareEnergy mssFineNormalizedCubeInput
    fourierCubeSquareFunction fourierCubeProjection
  simp only [Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz_apply]
  rw [Real.sq_sqrt]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cube hcube
    rw [norm_mul, mul_pow]
  · exact Finset.sum_nonneg fun cube hcube => sq_nonneg _

/-- The finite global normalized cube energy is continuous in the spatial
variable for Schwartz input. -/
theorem continuous_continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (kernelConstant scale : Real) (f : SchwartzMap (Euclidean 2) Complex) :
    Continuous (fun y : Euclidean 2 =>
      continuumFineCubeSquareEnergy
        (mssFinePieceIndices D scale)
        (fun piece => cubes.cubeSets scale piece.1 piece.2)
        (fun cube =>
          mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) := by
  classical
  unfold continuumFineCubeSquareEnergy mssFineNormalizedCubeInput
  refine continuous_finsetSum _ ?_
  intro cube hcube
  exact (continuous_const.mul
    (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
      (cubes.analysisCutoff scale cube) f).continuous).norm.pow _

/-- The global normalized cube energy is pointwise nonnegative. -/
theorem continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput_nonneg
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (kernelConstant scale : Real) (f : SchwartzMap (Euclidean 2) Complex)
    (y : Euclidean 2) :
    0 ≤ continuumFineCubeSquareEnergy
      (mssFinePieceIndices D scale)
      (fun piece => cubes.cubeSets scale piece.1 piece.2)
      (fun cube =>
        mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y := by
  unfold continuumFineCubeSquareEnergy
  exact Finset.sum_nonneg fun cube hcube => sq_nonneg _

/-- The preceding pointwise identification also gives the exact fourth-moment
bridge needed to use an `L⁴` estimate for the analysis-cube square function.
No integrability is assumed here: this is equality of the extended integrals
of pointwise equal real-valued functions. -/
theorem integral_sq_continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (kernelConstant scale : Real) (f : SchwartzMap (Euclidean 2) Complex) :
    (∫ y : Euclidean 2,
      (continuumFineCubeSquareEnergy
        (mssFinePieceIndices D scale)
        (fun piece => cubes.cubeSets scale piece.1 piece.2)
        (fun cube =>
          mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) ^ 2) =
      ‖(kernelConstant : Complex)‖ ^ 4 *
        ∫ y : Euclidean 2,
          fourierCubeSquareFunction
            ((mssFinePieceIndices D scale).biUnion
              (fun piece => cubes.cubeSets scale piece.1 piece.2))
            (cubes.analysisCutoff scale) f y ^ 4 := by
  let E : Euclidean 2 → Real := fun y =>
    continuumFineCubeSquareEnergy
      (mssFinePieceIndices D scale)
      (fun piece => cubes.cubeSets scale piece.1 piece.2)
      (fun cube =>
        mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y
  let S : Euclidean 2 → Real := fun y =>
    fourierCubeSquareFunction
      ((mssFinePieceIndices D scale).biUnion
        (fun piece => cubes.cubeSets scale piece.1 piece.2))
      (cubes.analysisCutoff scale) f y
  have hE (y : Euclidean 2) : E y = ‖(kernelConstant : Complex)‖ ^ 2 * S y ^ 2 := by
    simpa only [E, S] using
      continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
        D cubes kernelConstant scale f y
  change (∫ y : Euclidean 2, E y ^ 2) =
    ‖(kernelConstant : Complex)‖ ^ 4 * ∫ y : Euclidean 2, S y ^ 4
  calc
    (∫ y : Euclidean 2, E y ^ 2) =
        ∫ y : Euclidean 2, (‖(kernelConstant : Complex)‖ ^ 2 * S y ^ 2) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with y
      rw [hE y]
    _ = ∫ y : Euclidean 2, ‖(kernelConstant : Complex)‖ ^ 4 * S y ^ 4 := by
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = ‖(kernelConstant : Complex)‖ ^ 4 * ∫ y : Euclidean 2, S y ^ 4 :=
      integral_const_mul _ _

/-- The fourth moment of the finite global analysis-cube energy is
integrable for every Schwartz input.  This uses only finiteness and the
Schwartz representatives of the enlarged cube projections, not an `L⁴`
multiplier estimate. -/
theorem integrable_sq_continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (kernelConstant scale : Real) (f : SchwartzMap (Euclidean 2) Complex) :
    Integrable (fun y : Euclidean 2 =>
      (continuumFineCubeSquareEnergy
        (mssFinePieceIndices D scale)
        (fun piece => cubes.cubeSets scale piece.1 piece.2)
        (fun cube =>
          mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) ^ 2) volume := by
  classical
  let S : Finset (Fin (cubes.cubeCount scale)) :=
    (mssFinePieceIndices D scale).biUnion
      (fun piece => cubes.cubeSets scale piece.1 piece.2)
  let u : Fin (cubes.cubeCount scale) → Euclidean 2 → Complex := fun cube =>
    mssFineNormalizedCubeInput D cubes kernelConstant scale cube f
  have hu4 : ∀ cube ∈ S,
      Integrable (fun y : Euclidean 2 => ‖u cube y‖ ^ (4 : Nat)) volume := by
    intro cube hcube
    let P : SchwartzMap (Euclidean 2) Complex :=
      Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
        (cubes.analysisCutoff scale cube) f
    have hP : Integrable (fun y : Euclidean 2 => ‖P y‖ ^ (4 : Nat)) volume :=
      (P.memLp 4 volume).integrable_norm_pow (by norm_num)
    simpa only [u, P, mssFineNormalizedCubeInput, norm_mul, mul_pow] using
      hP.const_mul (‖(kernelConstant : Complex)‖ ^ (4 : Nat))
  have hsum : Integrable (fun y : Euclidean 2 =>
      ∑ cube ∈ S, ‖u cube y‖ ^ (4 : Nat)) volume :=
    integrable_finsetSum S hu4
  have hmajor : Integrable (fun y : Euclidean 2 =>
      (S.card : Real) * ∑ cube ∈ S, ‖u cube y‖ ^ (4 : Nat)) volume :=
    hsum.const_mul _
  have hucont (cube : Fin (cubes.cubeCount scale)) : Continuous (u cube) := by
    dsimp only [u, mssFineNormalizedCubeInput]
    exact continuous_const.mul
      (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
        (cubes.analysisCutoff scale cube) f).continuous
  have hcont : Continuous (fun y : Euclidean 2 =>
      (continuumFineCubeSquareEnergy
        (mssFinePieceIndices D scale)
        (fun piece => cubes.cubeSets scale piece.1 piece.2) u y) ^ (2 : Nat)) := by
    change Continuous (fun y => (∑ cube ∈ S, ‖u cube y‖ ^ (2 : Nat)) ^ (2 : Nat))
    exact (continuous_finsetSum S (fun cube hcube => (hucont cube).norm.pow _)).pow _
  apply hmajor.mono'
  · exact hcont.aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [continuumFineCubeSquareEnergy,
      Auto.LittlewoodPaley.finiteSquareEnergy] using
      Auto.LittlewoodPaley.finiteSquareEnergy_sq_le_card_mul_sum_norm_four S u y

/-- An averaged Rademacher fourth-moment estimate for the enlarged analysis
cutoffs supplies the uniform `L²` bound for the global normalized cube
energy.  The Rademacher estimate remains an explicit analytic hypothesis;
this theorem only performs the finite cube-energy conversion. -/
theorem exists_uniform_mssFineNormalizedCubeEnergy_L2_bound_of_analysis_average
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (kernelConstant : Real)
    (haverage : HasScaleAverageMSSAnalysisCubeRademacherL4 D cubes) :
    ∃ C : Real, 0 < C ∧ ∀ scale : Real, 2 ≤ scale →
      ∀ f : SchwartzMap (Euclidean 2) Complex,
        Integrable (fun y : Euclidean 2 =>
          (continuumFineCubeSquareEnergy
            (mssFinePieceIndices D scale)
            (fun piece => cubes.cubeSets scale piece.1 piece.2)
            (fun cube =>
              mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) ^ 2) volume ∧
        (∫ y : Euclidean 2,
          (continuumFineCubeSquareEnergy
            (mssFinePieceIndices D scale)
            (fun piece => cubes.cubeSets scale piece.1 piece.2)
            (fun cube =>
              mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) ^ 2) ≤
          ‖(kernelConstant : Complex)‖ ^ 4 * C *
            ∫ y : Euclidean 2, ‖f y‖ ^ 4 := by
  obtain ⟨C, hC, hcube⟩ :=
    uniformScaleMSSAnalysisCubeSquareFunctionL4_of_average D cubes haverage
  refine ⟨C, hC, ?_⟩
  intro scale hscale f
  refine ⟨integrable_sq_continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
    D cubes kernelConstant scale f, ?_⟩
  have hSF := hcube scale hscale
    ((mssFinePieceIndices D scale).biUnion
      (fun piece => cubes.cubeSets scale piece.1 piece.2)) f
  have hfactor : 0 ≤ ‖(kernelConstant : Complex)‖ ^ 4 := by positivity
  calc
    (∫ y : Euclidean 2,
      (continuumFineCubeSquareEnergy
        (mssFinePieceIndices D scale)
        (fun piece => cubes.cubeSets scale piece.1 piece.2)
        (fun cube =>
          mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) ^ 2) =
        ‖(kernelConstant : Complex)‖ ^ 4 *
          ∫ y : Euclidean 2,
            fourierCubeSquareFunction
              ((mssFinePieceIndices D scale).biUnion
                (fun piece => cubes.cubeSets scale piece.1 piece.2))
              (cubes.analysisCutoff scale) f y ^ 4 :=
      integral_sq_continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
        D cubes kernelConstant scale f
    _ ≤ ‖(kernelConstant : Complex)‖ ^ 4 *
        (C * ∫ y : Euclidean 2, ‖f y‖ ^ 4) :=
      mul_le_mul_of_nonneg_left hSF hfactor
    _ = ‖(kernelConstant : Complex)‖ ^ 4 * C *
        ∫ y : Euclidean 2, ‖f y‖ ^ 4 := by ring

/-- A direct uniform analysis-cube `L⁴` square-function bound supplies the
uniform `L²` bound for the global normalized cube energy. -/
theorem exists_uniform_mssFineNormalizedCubeEnergy_L2_bound_of_analysis_L4
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (kernelConstant : Real)
    (hL4 : uniformScaleMSSAnalysisCubeSquareFunctionL4 D cubes) :
    ∃ C : Real, 0 < C ∧ ∀ scale : Real, 2 ≤ scale →
      ∀ f : SchwartzMap (Euclidean 2) Complex,
        Integrable (fun y : Euclidean 2 =>
          (continuumFineCubeSquareEnergy
            (mssFinePieceIndices D scale)
            (fun piece => cubes.cubeSets scale piece.1 piece.2)
            (fun cube =>
              mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) ^ 2) volume ∧
        (∫ y : Euclidean 2,
          (continuumFineCubeSquareEnergy
            (mssFinePieceIndices D scale)
            (fun piece => cubes.cubeSets scale piece.1 piece.2)
            (fun cube =>
              mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) ^ 2) ≤
          ‖(kernelConstant : Complex)‖ ^ 4 * C *
            ∫ y : Euclidean 2, ‖f y‖ ^ 4 := by
  obtain ⟨C, hC, hcube⟩ := hL4
  refine ⟨C, hC, ?_⟩
  intro scale hscale f
  refine ⟨integrable_sq_continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
    D cubes kernelConstant scale f, ?_⟩
  have hSF := hcube scale hscale
    ((mssFinePieceIndices D scale).biUnion
      (fun piece => cubes.cubeSets scale piece.1 piece.2)) f
  have hfactor : 0 ≤ ‖(kernelConstant : Complex)‖ ^ 4 := by positivity
  calc
    (∫ y : Euclidean 2,
      (continuumFineCubeSquareEnergy
        (mssFinePieceIndices D scale)
        (fun piece => cubes.cubeSets scale piece.1 piece.2)
        (fun cube =>
          mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) ^ 2) =
        ‖(kernelConstant : Complex)‖ ^ 4 *
          ∫ y : Euclidean 2,
            fourierCubeSquareFunction
              ((mssFinePieceIndices D scale).biUnion
                (fun piece => cubes.cubeSets scale piece.1 piece.2))
              (cubes.analysisCutoff scale) f y ^ 4 :=
      integral_sq_continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
        D cubes kernelConstant scale f
    _ ≤ ‖(kernelConstant : Complex)‖ ^ 4 *
        (C * ∫ y : Euclidean 2, ‖f y‖ ^ 4) :=
      mul_le_mul_of_nonneg_left hSF hfactor
    _ = ‖(kernelConstant : Complex)‖ ^ 4 * C *
        ∫ y : Euclidean 2, ‖f y‖ ^ 4 := by ring

/-- The literal localization data, Schwartz cube inputs, and the light-ray
maximal estimate supply every regularity and Fubini field required by the
continuum fine-cube transposition argument for a bounded compact test. -/
theorem mssFineCubeContinuumRegularity_of_localization_of_boundedCompactTest
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant : Real)
    (localization : MSSFineCubeKernelLocalization D cubes N kernelConstant massConstant)
    {scale : Real} (hscale : 2 ≤ scale)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 3 < N)
    (f : SchwartzMap (Euclidean 2) Complex) (g : WaveSpaceTime → Complex)
    (hg : LightRayBoundedCompactTest g) :
    MSSFineCubeContinuumRegularity D cubes N kernelConstant massConstant scale f g := by
  classical
  letI : MeasurableSpace (Euclidean 2) :=
    WithLp.measurableSpace 2 (Fin 2 → Real)
  letI : BorelSpace (Euclidean 2) := PiLp.borelSpace 2
  let delta : Real := (cubes.cubeWidth * Real.sqrt scale)⁻¹
  have hdelta : 0 < delta := by
    simpa [delta] using (cubeWidth_inv_mul_sqrt_pos_lt_half hwidth hscale).1
  have hdeltaSmall : delta < 1 / 2 := by
    simpa [delta] using (cubeWidth_inv_mul_sqrt_pos_lt_half hwidth hscale).2
  have hNone : 1 < N := by omega
  have hNtwo : 2 < N := by omega
  letI : SFinite continuumLightRayMeasure := by
    unfold continuumLightRayMeasure
    infer_instance
  have hmeasureLe : continuumLightRayMeasure ≤ (volume : Measure WaveSpaceTime) := by
    unfold continuumLightRayMeasure
    change (volume : Measure (Euclidean 2)).prod
        ((volume : Measure Real).restrict lightRayTimeInterval) ≤
      (volume : Measure (Euclidean 2)).prod (volume : Measure Real)
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hgMem : MemLp g 2 continuumLightRayMeasure :=
    hg.memLp_two.mono_measure hmeasureLe
  have hgNorm : Integrable (fun z : WaveSpaceTime => ‖g z‖)
      continuumLightRayMeasure :=
    hg.integrable_norm_continuumLightRayMeasure
  have hinputSq : ∀ cube : Fin (cubes.cubeCount scale),
      Integrable (fun y : Euclidean 2 =>
        ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2)
        (volume : Measure (Euclidean 2)) := by
    intro cube
    let P : SchwartzMap (Euclidean 2) Complex :=
      Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
        (cubes.analysisCutoff scale cube) f
    have hP : Integrable (fun y : Euclidean 2 => ‖P y‖ ^ (2 : Nat))
        (volume : Measure (Euclidean 2)) :=
      (P.memLp 2 volume).integrable_norm_pow (by norm_num)
    simpa only [P, mssFineNormalizedCubeInput, norm_mul, mul_pow] using
      hP.const_mul (‖(kernelConstant : Complex)‖ ^ (2 : Nat))
  have hinputSqMeas : ∀ cube : Fin (cubes.cubeCount scale),
      AEStronglyMeasurable (fun y : Euclidean 2 =>
        ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2) volume := by
    intro cube
    exact (hinputSq cube).aestronglyMeasurable
  have hinputFour : ∀ cube : Fin (cubes.cubeCount scale),
      Integrable (fun y : Euclidean 2 =>
        ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 4)
        (volume : Measure (Euclidean 2)) := by
    intro cube
    let P : SchwartzMap (Euclidean 2) Complex :=
      Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
        (cubes.analysisCutoff scale cube) f
    have hP : Integrable (fun y : Euclidean 2 => ‖P y‖ ^ (4 : Nat))
        (volume : Measure (Euclidean 2)) :=
      (P.memLp 4 volume).integrable_norm_pow (by norm_num)
    simpa only [P, mssFineNormalizedCubeInput, norm_mul, mul_pow] using
      hP.const_mul (‖(kernelConstant : Complex)‖ ^ (4 : Nat))
  have hinputSqMem : ∀ cube : Fin (cubes.cubeCount scale),
      MemLp (fun y : Euclidean 2 =>
        ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2) 2 volume := by
    intro cube
    apply (memLp_two_iff_integrable_sq (hinputSqMeas cube)).mpr
    refine (hinputFour cube).congr ?_
    filter_upwards with y
    ring
  have hlightRayMeas : ∀ (omega : Euclidean 2) (z : WaveSpaceTime),
      AEStronglyMeasurable (fun y : Euclidean 2 =>
        lightRayKernel delta N omega y z) volume := by
    intro omega z
    simpa using
      (aestronglyMeasurable_lightRayKernel_of_aestronglyMeasurable_direction_comp
        volume delta N (fun _ : Euclidean 2 => omega)
        (fun y : Euclidean 2 => y) (fun _ : Euclidean 2 => z.1)
        (fun _ : Euclidean 2 => z.2)
        aestronglyMeasurable_const measurable_id.aemeasurable
        aemeasurable_const aemeasurable_const)
  have hlightRayProdMeas : ∀ omega : Euclidean 2,
      AEStronglyMeasurable (fun p : WaveSpaceTime × Euclidean 2 =>
        lightRayKernel delta N omega p.2 p.1)
        (continuumLightRayMeasure.prod volume) := by
    intro omega
    simpa using
      (aestronglyMeasurable_lightRayKernel_of_aestronglyMeasurable_direction_comp
        (continuumLightRayMeasure.prod volume) delta N
        (fun _ : Euclidean 2 => omega) (fun p : WaveSpaceTime × Euclidean 2 => p.2)
        (fun p : WaveSpaceTime × Euclidean 2 => p.1.1)
        (fun p : WaveSpaceTime × Euclidean 2 => p.1.2)
        aestronglyMeasurable_const measurable_snd.aemeasurable
        (measurable_fst.comp measurable_fst).aemeasurable
        (measurable_snd.comp measurable_fst).aemeasurable)
  have hmeas : ∀ n ∈ relevantRadialIndexEnumeration scale,
      ∀ nu ∈ D.angularIndices scale, ∀ cube ∈ cubes.cubeSets scale n nu,
      ∀ z : WaveSpaceTime,
      AEStronglyMeasurable (fun y : Euclidean 2 =>
        (lightRayKernel delta N (D.directions scale nu) y z)⁻¹ *
          ‖mssFineNormalizedCubeKernel D cubes kernelConstant scale n nu cube z y *
            mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2) volume := by
    intro n hn nu hnu cube hcube z
    have hsource : AEStronglyMeasurable (fun y : Euclidean 2 =>
        mssFineCubeHalfWaveKernel D cubes scale n nu cube z y) volume :=
      (localization.source_integrable scale hscale n hn nu hnu cube hcube z).aestronglyMeasurable
    have hkernel : AEStronglyMeasurable (fun y : Euclidean 2 =>
        mssFineNormalizedCubeKernel D cubes kernelConstant scale n nu cube z y) volume := by
      simpa only [mssFineNormalizedCubeKernel] using
        hsource.const_mul ((kernelConstant : Complex)⁻¹)
    have hnormProduct : AEStronglyMeasurable (fun y : Euclidean 2 =>
        ‖mssFineNormalizedCubeKernel D cubes kernelConstant scale n nu cube z y‖ ^ 2 *
          ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2) volume :=
      (hkernel.norm.pow 2).mul (hinputSqMeas cube)
    refine ((hlightRayMeas (D.directions scale nu) z).aemeasurable.inv.aestronglyMeasurable.mul
      hnormProduct).congr ?_
    filter_upwards with y
    rw [norm_mul]
    simp only [Pi.inv_apply, Pi.mul_apply]
    ring
  have henergy : ∀ n ∈ relevantRadialIndexEnumeration scale,
      ∀ nu ∈ D.angularIndices scale, ∀ cube ∈ cubes.cubeSets scale n nu,
      ∀ z : WaveSpaceTime,
      Integrable (fun y : Euclidean 2 =>
        lightRayKernel delta N (D.directions scale nu) y z *
          ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2) volume := by
    intro n hn nu hnu cube hcube z
    refine ((hinputSq cube).const_mul ((delta⁻¹) ^ 2)).mono' ?_ ?_
    · exact (hlightRayMeas (D.directions scale nu) z).mul (hinputSqMeas cube)
    · filter_upwards with y
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg
          (lightRayKernel_nonneg hdelta N (D.directions scale nu) y z) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right
        (lightRayKernel_le_normalization hdelta N (D.directions scale nu) y z)
        (sq_nonneg _)
  have hprod : ∀ n ∈ relevantRadialIndexEnumeration scale,
      ∀ nu ∈ D.angularIndices scale, ∀ cube ∈ cubes.cubeSets scale n nu,
      Integrable (fun p : WaveSpaceTime × Euclidean 2 =>
        lightRayKernel delta N (D.directions scale nu) p.2 p.1 *
          ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f p.2‖ ^ 2 *
            ‖g p.1‖) (continuumLightRayMeasure.prod volume) := by
    intro n hn nu hnu cube hcube
    have hmajor : Integrable (fun p : WaveSpaceTime × Euclidean 2 =>
        (delta⁻¹) ^ 2 *
          (‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f p.2‖ ^ 2 *
            ‖g p.1‖)) (continuumLightRayMeasure.prod volume) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (hgNorm.mul_prod (hinputSq cube)).const_mul ((delta⁻¹) ^ 2)
    refine hmajor.mono' ?_ ?_
    · exact ((hlightRayProdMeas (D.directions scale nu)).mul
        ((hinputSqMeas cube).comp_snd)).mul hgMem.norm.aestronglyMeasurable.comp_fst
    · filter_upwards with p
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg
          (mul_nonneg (lightRayKernel_nonneg hdelta N (D.directions scale nu) p.2 p.1)
            (sq_nonneg _)) (norm_nonneg _))]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right
          (lightRayKernel_le_normalization hdelta N (D.directions scale nu) p.2 p.1)
          (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  have henergyWeighted : ∀ n ∈ relevantRadialIndexEnumeration scale,
      ∀ nu ∈ D.angularIndices scale, ∀ cube ∈ cubes.cubeSets scale n nu,
      Integrable (fun z : WaveSpaceTime =>
        (∫ y : Euclidean 2,
          lightRayKernel delta N (D.directions scale nu) y z *
            ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2) * ‖g z‖)
        continuumLightRayMeasure := by
    intro n hn nu hnu cube hcube
    refine (hprod n hn nu hnu cube hcube).integral_prod_left.congr ?_
    filter_upwards with z
    rw [integral_mul_const_of_integrable (henergy n hn nu hnu cube hcube z)]
  have htermWeighted : ∀ n ∈ relevantRadialIndexEnumeration scale,
      ∀ nu ∈ D.angularIndices scale, ∀ cube ∈ cubes.cubeSets scale n nu,
      Integrable (fun z : WaveSpaceTime =>
        ‖∫ y : Euclidean 2,
          mssFineNormalizedCubeKernel D cubes kernelConstant scale n nu cube z y *
            mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2 * ‖g z‖)
        continuumLightRayMeasure := by
    intro n hn nu hnu cube hcube
    let A : Real := ∫ u : Euclidean 2, lightRayDecayProfile N u
    have hA : 0 ≤ A := by
      dsimp [A]
      exact (lightRayKernel_spatial_mass_bound hdelta N hNtwo (0 : Euclidean 2)).1
    have htermMeas : AEStronglyMeasurable (fun z : WaveSpaceTime =>
        ‖∫ y : Euclidean 2,
          mssFineNormalizedCubeKernel D cubes kernelConstant scale n nu cube z y *
            mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2 * ‖g z‖)
        continuumLightRayMeasure := by
      have hpacketMeas : AEStronglyMeasurable (fun z : WaveSpaceTime =>
          ‖mssFineCubePacket D cubes scale n nu cube
            (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
              (cubes.analysisCutoff scale cube) f) z‖ ^ 2 * ‖g z‖)
          continuumLightRayMeasure :=
        ((continuous_mssFineCubePacket D cubes scale n nu cube
          (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
            (cubes.analysisCutoff scale cube) f)).norm.pow 2).aestronglyMeasurable.mul
          hgMem.norm.aestronglyMeasurable
      refine hpacketMeas.congr ?_
      filter_upwards with z
      rw [mssFineCubePacket_eq_integral_normalizedCubeKernel D cubes N
        kernelConstant massConstant localization scale hscale n nu hn hnu cube hcube f z]
    have hright : Integrable (fun z : WaveSpaceTime =>
        (A * ∫ y : Euclidean 2,
          lightRayKernel delta N (D.directions scale nu) y z *
            ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2) * ‖g z‖)
        continuumLightRayMeasure := by
      simpa only [mul_assoc] using
        (henergyWeighted n hn nu hnu cube hcube).const_mul A
    refine hright.mono' htermMeas ?_
    filter_upwards with z
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (sq_norm_continuumFineKernelTerm_le_lightRayEnergy hdelta N
        (D.directions scale nu)
        (fun z y => mssFineNormalizedCubeKernel D cubes kernelConstant scale n nu cube z y)
        (fun y => mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y)
        (norm_mssFineNormalizedCubeKernel_le_lightRayKernel D cubes N
          kernelConstant massConstant localization scale hscale n nu hn hnu cube hcube)
        (lightRayKernel_spatial_mass_bound hdelta N hNtwo
          (D.directions scale nu)).2
        (hmeas n hn nu hnu cube hcube) (henergy n hn nu hnu cube hcube) z)
      (norm_nonneg _)
  have hray : ∀ (omega y : Euclidean 2),
      Integrable (fun z : WaveSpaceTime =>
        lightRayKernel delta N omega y z * ‖g z‖) continuumLightRayMeasure := by
    intro omega y
    simpa only [delta, continuumLightRayMeasure, scratchLightRayMeasure] using
      scratch_integrable_lightRayKernel_mul_norm_of_memLp hdelta N hNone omega y g hg.memLp_two
  have hbounded : ∀ y : Euclidean 2,
      BddAbove ((fun omega : Euclidean 2 => lightRayAverage delta N omega y g) ''
        unitLightRayDirections) := by
    intro y
    exact aux_bddAbove_lightRayAverages_of_continuity delta N g
      (aux_hasContinuousLightRayDirections_of_memLp hdelta N hNone g hg.memLp_two) y
  obtain ⟨C, hC, hHLE⟩ :=
    exists_uniform_lightRayMaximal_norm_sq_bound_on_boundedCompactTests
      N hN
  have hmaxMem : MemLp (lightRayMaximal delta N g) 2 volume :=
    (hHLE hdelta hdeltaSmall g hg).1
  have hmaxWeighted : ∀ n ∈ relevantRadialIndexEnumeration scale,
      ∀ nu ∈ D.angularIndices scale, ∀ cube ∈ cubes.cubeSets scale n nu,
      Integrable (fun y : Euclidean 2 =>
        ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2 *
          lightRayMaximal delta N g y) volume := by
    intro n hn nu hnu cube hcube
    exact (hinputSqMem cube).integrable_mul hmaxMem
  refine
    { meas := ?_
      energy := ?_
      termWeighted := ?_
      energyWeighted := ?_
      prod := ?_
      ray_integrable := ?_
      bounded := ?_
      maxWeighted := ?_
      squareWeighted := ?_ }
  · intro _ n hn nu hnu cube hcube z
    simpa only [delta] using hmeas n hn nu hnu cube hcube z
  · intro _ n hn nu hnu cube hcube z
    simpa only [delta] using henergy n hn nu hnu cube hcube z
  · intro _ n hn nu hnu cube hcube
    simpa only [delta] using htermWeighted n hn nu hnu cube hcube
  · intro _ n hn nu hnu cube hcube
    simpa only [delta] using henergyWeighted n hn nu hnu cube hcube
  · intro _ n hn nu hnu cube hcube
    simpa only [delta] using hprod n hn nu hnu cube hcube
  · intro _ n hn nu hnu cube hcube y
    simpa only [delta] using hray (D.directions scale nu) y
  · intro y
    simpa only [delta] using hbounded y
  · intro _ n hn nu hnu cube hcube
    simpa only [delta] using hmaxWeighted n hn nu hnu cube hcube
  · exact hg.integrable_mul_norm_of_continuous
      (continuous_sq_mssFineCubePacketSquareFunction D cubes scale f)

/-- The per-cube weighted integrability in the continuum regularity package
assembles to integrability of the global normalized cube energy against the
light-ray maximal function. -/
theorem integrable_continuumFineCubeWeightedEnergy_of_mssFineCubeContinuumRegularity
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant scale : Real)
    (f : SchwartzMap (Euclidean 2) Complex) (g : WaveSpaceTime → Complex)
    (hscale : 2 ≤ scale)
    (regularity : MSSFineCubeContinuumRegularity D cubes N
      kernelConstant massConstant scale f g) :
    Integrable
      (continuumFineCubeWeightedEnergy
        (mssFinePieceIndices D scale)
        (fun piece => cubes.cubeSets scale piece.1 piece.2)
        (fun cube =>
          mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
        (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g)) volume := by
  classical
  have hpieceMem : ∀ piece ∈ mssFinePieceIndices D scale,
      piece.1 ∈ relevantRadialIndexEnumeration scale ∧
        piece.2 ∈ D.angularIndices scale := by
    intro piece hpiece
    simpa [mssFinePieceIndices] using hpiece
  have hcubeWeighted : ∀ cube ∈
      (mssFinePieceIndices D scale).biUnion
        (fun piece => cubes.cubeSets scale piece.1 piece.2),
      Integrable (fun y : Euclidean 2 =>
        ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2 *
          lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g y) volume := by
    intro cube hcube
    obtain ⟨piece, hpiece, hcubePiece⟩ := Finset.mem_biUnion.mp hcube
    have hmem := hpieceMem piece hpiece
    exact regularity.maxWeighted hscale piece.1 hmem.1 piece.2 hmem.2 cube hcubePiece
  have hterms : Integrable (fun y : Euclidean 2 =>
      ∑ cube ∈ (mssFinePieceIndices D scale).biUnion
        (fun piece => cubes.cubeSets scale piece.1 piece.2),
        ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2 *
          lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g y) volume :=
    integrable_finsetSum _ hcubeWeighted
  refine hterms.congr ?_
  filter_upwards with y
  change
    (∑ cube ∈ (mssFinePieceIndices D scale).biUnion
      (fun piece => cubes.cubeSets scale piece.1 piece.2),
      ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2 *
        lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g y) =
      (∑ cube ∈ (mssFinePieceIndices D scale).biUnion
        (fun piece => cubes.cubeSets scale piece.1 piece.2),
        ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2) *
          lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g y
  rw [Finset.sum_mul]

/-- A slab-supported test may be paired against any real-valued function
using either ambient volume or the literal continuum light-ray measure. -/
theorem integral_mul_norm_eq_integral_mul_norm_continuumLightRayMeasure_of_slab
    (F : WaveSpaceTime → Real) (g : WaveSpaceTime → Complex)
    (hslab : g = (Set.univ ×ˢ lightRayTimeInterval).indicator g) :
    (∫ z : WaveSpaceTime, F z * ‖g z‖) =
      ∫ z : WaveSpaceTime, F z * ‖g z‖ ∂continuumLightRayMeasure := by
  let slab : Set WaveSpaceTime := Set.univ ×ˢ lightRayTimeInterval
  have hslabMeas : MeasurableSet slab := by
    dsimp [slab]
    exact MeasurableSet.univ.prod (by
      unfold lightRayTimeInterval
      exact measurableSet_Icc)
  have hmeasure :
      continuumLightRayMeasure = (volume : Measure WaveSpaceTime).restrict slab := by
    unfold continuumLightRayMeasure
    change (volume : Measure (Euclidean 2)).prod
        ((volume : Measure Real).restrict lightRayTimeInterval) =
      ((volume : Measure (Euclidean 2)).prod (volume : Measure Real)).restrict
        (Set.univ ×ˢ lightRayTimeInterval)
    rw [← Measure.prod_restrict]
    simp
  have hslab' : g = slab.indicator g := by
    simpa only [slab] using hslab
  have hproductIndicator :
      (fun z : WaveSpaceTime => F z * ‖g z‖) =
        slab.indicator (fun z : WaveSpaceTime => F z * ‖g z‖) := by
    funext z
    by_cases hz : z ∈ slab
    · simp [hz]
    · have hz0 : g z = 0 := by
        rw [hslab']
        simp [hz]
      simp [hz, hz0]
  calc
    (∫ z : WaveSpaceTime, F z * ‖g z‖) =
        ∫ z : WaveSpaceTime,
          slab.indicator (fun z : WaveSpaceTime => F z * ‖g z‖) z := by
      apply integral_congr_ae
      filter_upwards with z
      exact congrFun hproductIndicator z
    _ = ∫ z : WaveSpaceTime in slab, F z * ‖g z‖ :=
      integral_indicator hslabMeas
    _ = ∫ z : WaveSpaceTime, F z * ‖g z‖ ∂continuumLightRayMeasure := by
      rw [hmeasure]

/-- Integrability for the same slab-supported pairing also transfers from
the continuum light-ray measure back to ambient volume. -/
theorem integrable_mul_norm_of_integrable_continuumLightRayMeasure_of_slab
    (F : WaveSpaceTime → Real) (g : WaveSpaceTime → Complex)
    (hslab : g = (Set.univ ×ˢ lightRayTimeInterval).indicator g)
    (hintegrable : Integrable (fun z : WaveSpaceTime => F z * ‖g z‖)
      continuumLightRayMeasure) :
    Integrable (fun z : WaveSpaceTime => F z * ‖g z‖) volume := by
  let slab : Set WaveSpaceTime := Set.univ ×ˢ lightRayTimeInterval
  have hslabMeas : MeasurableSet slab := by
    dsimp [slab]
    exact MeasurableSet.univ.prod (by
      unfold lightRayTimeInterval
      exact measurableSet_Icc)
  have hmeasure :
      continuumLightRayMeasure = (volume : Measure WaveSpaceTime).restrict slab := by
    unfold continuumLightRayMeasure
    change (volume : Measure (Euclidean 2)).prod
        ((volume : Measure Real).restrict lightRayTimeInterval) =
      ((volume : Measure (Euclidean 2)).prod (volume : Measure Real)).restrict
        (Set.univ ×ˢ lightRayTimeInterval)
    rw [← Measure.prod_restrict]
    simp
  have hslab' : g = slab.indicator g := by
    simpa only [slab] using hslab
  have hproductIndicator :
      (fun z : WaveSpaceTime => F z * ‖g z‖) =
        slab.indicator (fun z : WaveSpaceTime => F z * ‖g z‖) := by
    funext z
    by_cases hz : z ∈ slab
    · simp [hz]
    · have hz0 : g z = 0 := by
        rw [hslab']
        simp [hz]
      simp [hz, hz0]
  have hrestricted : Integrable (fun z : WaveSpaceTime => F z * ‖g z‖)
      ((volume : Measure WaveSpaceTime).restrict slab) := by
    rw [← hmeasure]
    exact hintegrable
  have hindicator : Integrable
      (slab.indicator (fun z : WaveSpaceTime => F z * ‖g z‖)) volume := by
    rw [integrable_indicator_iff hslabMeas]
    exact hrestricted
  refine hindicator.congr ?_
  filter_upwards with z
  exact (congrFun hproductIndicator z).symm

/-- The continuum MSS packet transposition estimate, expressed against
ambient volume for an admissible truncated light-ray test.  All spatial
cube-energy and maximal-function terms remain exactly those supplied by the
continuum estimate. -/
theorem mssFineCubePacketSquarePairing_le_lightRayCubeEnergy_ambient
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant : Real)
    (localization : MSSFineCubeKernelLocalization D cubes N kernelConstant massConstant)
    {scale : Real} (hscale : 2 ≤ scale)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 2 < N)
    (f : SchwartzMap (Euclidean 2) Complex) (g : WaveSpaceTime → Complex)
    (hg : LightRayBoundedCompactTest g)
    (regularity : MSSFineCubeContinuumRegularity D cubes N
      kernelConstant massConstant scale f g) :
    ∃ B R : Nat,
      Integrable (fun z : WaveSpaceTime =>
        mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g z‖) volume ∧
      (∫ z : WaveSpaceTime,
        mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g z‖) ≤
        ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) * (R : Real) *
          ∫ y : Euclidean 2,
            continuumFineCubeWeightedEnergy
              (mssFinePieceIndices D scale)
              (fun piece => cubes.cubeSets scale piece.1 piece.2)
              (fun cube =>
                mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
              (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g) y := by
  obtain ⟨B, R, hpair⟩ := mssFineCubePacketSquarePairing_le_lightRayCubeEnergy
    D cubes N kernelConstant massConstant localization hscale hwidth hN f g regularity
  refine ⟨B, R, ?_, ?_⟩
  · exact integrable_mul_norm_of_integrable_continuumLightRayMeasure_of_slab
      (fun z => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) g hg.slab
      regularity.squareWeighted
  · rw [integral_mul_norm_eq_integral_mul_norm_continuumLightRayMeasure_of_slab
      (fun z => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) g hg.slab]
    exact hpair

/-- The uniform-constant ambient form of the MSS cube-packet pairing.

Unlike `mssFineCubePacketSquarePairing_le_lightRayCubeEnergy_ambient`, the
packet-cardinality and reverse-overlap constants are supplied before the test
function.  Consequently its coefficient is uniform over every admissible
bounded compact light-ray test, as required by truncated duality. -/
theorem mssFineCubePacketSquarePairing_le_lightRayCubeEnergy_ambient_of_uniformBounds
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant : Real)
    (localization : MSSFineCubeKernelLocalization D cubes N kernelConstant massConstant)
    (B R : Nat)
    (hcard : ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
        ((cubes.cubeSets scale n nu).card : Real) ≤ B)
    (hoverlap : ∀ scale : Real, 2 ≤ scale →
      HasFiniteFineCubeReverseOverlap (mssFinePieceIndices D scale)
        (fun piece => cubes.cubeSets scale piece.1 piece.2) R)
    {scale : Real} (hscale : 2 ≤ scale)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 2 < N)
    (f : SchwartzMap (Euclidean 2) Complex) :
    ∀ g : WaveSpaceTime → Complex, LightRayBoundedCompactTest g →
      MSSFineCubeContinuumRegularity D cubes N kernelConstant massConstant scale f g →
        Integrable (fun z : WaveSpaceTime =>
          mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g z‖) volume ∧
        (∫ z : WaveSpaceTime,
          mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g z‖) ≤
          ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) * (R : Real) *
            ∫ y : Euclidean 2,
              continuumFineCubeWeightedEnergy
                (mssFinePieceIndices D scale)
                (fun piece => cubes.cubeSets scale piece.1 piece.2)
                (fun cube =>
                  mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
                (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g) y := by
  intro g hg regularity
  classical
  have hδ : 0 < (cubes.cubeWidth * Real.sqrt scale)⁻¹ :=
    (cubeWidth_inv_mul_sqrt_pos_lt_half hwidth hscale).1
  have hA : 0 ≤ ∫ u : Euclidean 2, lightRayDecayProfile N u :=
    (lightRayKernel_spatial_mass_bound hδ N hN (0 : Euclidean 2)).1
  have hpieceMem : ∀ piece ∈ mssFinePieceIndices D scale,
      piece.1 ∈ relevantRadialIndexEnumeration scale ∧
        piece.2 ∈ D.angularIndices scale := by
    intro piece hpiece
    simpa [mssFinePieceIndices] using hpiece
  have hsquareWeighted : Integrable (fun z : WaveSpaceTime =>
      (∑ piece ∈ mssFinePieceIndices D scale,
        ‖∑ cube ∈ cubes.cubeSets scale piece.1 piece.2,
          mssFineCubePacket D cubes scale piece.1 piece.2 cube
            (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
              (cubes.analysisCutoff scale cube) f) z‖ ^ 2) * ‖g z‖)
        continuumLightRayMeasure := by
    refine regularity.squareWeighted.congr ?_
    filter_upwards with z
    rw [sq_mssFineCubePacketSquareFunction_eq_pieceSum]
  have hassigned := continuumFineSquarePairing_le_cubeMultiplicity_mul_lightRayMaximal
    (pieces := mssFinePieceIndices D scale)
    (cubeSets := fun piece => cubes.cubeSets scale piece.1 piece.2)
    (δ := (cubes.cubeWidth * Real.sqrt scale)⁻¹)
    (A := ∫ u : Euclidean 2, lightRayDecayProfile N u)
    (B := (B : Real)) hδ hA (Nat.cast_nonneg B) N
    (fun piece => D.directions scale piece.2)
    (fun piece cube z y =>
      mssFineNormalizedCubeKernel D cubes kernelConstant scale piece.1 piece.2 cube z y)
    (fun cube y =>
      mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y)
    (fun piece cube z =>
      mssFineCubePacket D cubes scale piece.1 piece.2 cube
        (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
          (cubes.analysisCutoff scale cube) f) z)
    g
    (by
      intro piece hpiece cube hcube z
      have hmem := hpieceMem piece hpiece
      exact mssFineCubePacket_eq_integral_normalizedCubeKernel
        D cubes N kernelConstant massConstant localization scale hscale piece.1 piece.2
        hmem.1 hmem.2 cube hcube f z)
    (by
      intro piece hpiece
      have hmem := hpieceMem piece hpiece
      exact hcard scale hscale piece.1 hmem.1 piece.2 hmem.2)
    (by
      intro piece hpiece
      have hmem := hpieceMem piece hpiece
      exact D.direction_unit scale piece.2 hmem.2)
    (by
      intro piece hpiece cube hcube z y
      have hmem := hpieceMem piece hpiece
      exact norm_mssFineNormalizedCubeKernel_le_lightRayKernel
        D cubes N kernelConstant massConstant localization scale hscale piece.1 piece.2
        hmem.1 hmem.2 cube hcube z y)
    (by
      intro piece hpiece cube hcube z
      have hmem := hpieceMem piece hpiece
      exact (lightRayKernel_spatial_mass_bound hδ N hN
        (D.directions scale piece.2)).2 z)
    (by
      intro piece hpiece cube hcube z
      have hmem := hpieceMem piece hpiece
      exact regularity.meas hscale piece.1 hmem.1 piece.2 hmem.2 cube hcube z)
    (by
      intro piece hpiece cube hcube z
      have hmem := hpieceMem piece hpiece
      exact regularity.energy hscale piece.1 hmem.1 piece.2 hmem.2 cube hcube z)
    (by
      intro piece hpiece cube hcube
      have hmem := hpieceMem piece hpiece
      exact regularity.termWeighted hscale piece.1 hmem.1 piece.2 hmem.2 cube hcube)
    (by
      intro piece hpiece cube hcube
      have hmem := hpieceMem piece hpiece
      exact regularity.energyWeighted hscale piece.1 hmem.1 piece.2 hmem.2 cube hcube)
    (by
      intro piece hpiece cube hcube
      have hmem := hpieceMem piece hpiece
      exact regularity.prod hscale piece.1 hmem.1 piece.2 hmem.2 cube hcube)
    (by
      intro piece hpiece cube hcube y
      have hmem := hpieceMem piece hpiece
      exact regularity.ray_integrable hscale piece.1 hmem.1 piece.2 hmem.2 cube hcube y)
    (by
      intro piece hpiece cube hcube y
      exact regularity.bounded y)
    (by
      intro piece hpiece cube hcube
      have hmem := hpieceMem piece hpiece
      exact regularity.maxWeighted hscale piece.1 hmem.1 piece.2 hmem.2 cube hcube)
    hsquareWeighted
  have hpacket :
      (∫ z : WaveSpaceTime,
        mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g z‖
        ∂continuumLightRayMeasure) ≤
        ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) *
          ∫ y : Euclidean 2,
            continuumFineAssignedCubeWeightedEnergy
              (mssFinePieceIndices D scale)
              (fun piece => cubes.cubeSets scale piece.1 piece.2)
              (fun cube =>
                mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
              (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g) y := by
    calc
      (∫ z : WaveSpaceTime,
        mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g z‖
        ∂continuumLightRayMeasure) =
          ∫ z : WaveSpaceTime,
            (∑ piece ∈ mssFinePieceIndices D scale,
              ‖∑ cube ∈ cubes.cubeSets scale piece.1 piece.2,
                mssFineCubePacket D cubes scale piece.1 piece.2 cube
                  (Auto.Spherical.Auxiliary.fourierCubeProjectedSchwartz
                    (cubes.analysisCutoff scale cube) f) z‖ ^ 2) * ‖g z‖
            ∂continuumLightRayMeasure := by
        apply integral_congr_ae
        filter_upwards with z
        rw [sq_mssFineCubePacketSquareFunction_eq_pieceSum]
      _ ≤ ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) *
          ∫ y : Euclidean 2,
            continuumFineAssignedCubeWeightedEnergy
              (mssFinePieceIndices D scale)
              (fun piece => cubes.cubeSets scale piece.1 piece.2)
              (fun cube =>
                mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
              (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g) y := hassigned
  have hweight : ∀ y : Euclidean 2,
      0 ≤ lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g y := by
    intro y
    exact aux_lightRayMaximal_nonneg hδ N g regularity.bounded y
  have hcubeWeighted : ∀ cube ∈
      (mssFinePieceIndices D scale).biUnion
        (fun piece => cubes.cubeSets scale piece.1 piece.2),
      Integrable (fun y : Euclidean 2 =>
        ‖mssFineNormalizedCubeInput D cubes kernelConstant scale cube f y‖ ^ 2 *
          lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g y) volume := by
    intro cube hcube
    obtain ⟨piece, hpiece, hcubePiece⟩ := Finset.mem_biUnion.mp hcube
    have hmem := hpieceMem piece hpiece
    exact regularity.maxWeighted hscale piece.1 hmem.1 piece.2 hmem.2 cube hcubePiece
  have hcollapse := integral_continuumFineAssignedCubeWeightedEnergy_le_reverseOverlap_mul
    (μ := volume) (mssFinePieceIndices D scale)
    (fun piece => cubes.cubeSets scale piece.1 piece.2)
    (fun cube => mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
    (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g)
    hweight R (hoverlap scale hscale) hcubeWeighted
  have hfactor : 0 ≤ (B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u :=
    mul_nonneg (Nat.cast_nonneg B) hA
  have hcontinuum :
      (∫ z : WaveSpaceTime,
        mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g z‖
        ∂continuumLightRayMeasure) ≤
        ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) * (R : Real) *
          ∫ y : Euclidean 2,
            continuumFineCubeWeightedEnergy
              (mssFinePieceIndices D scale)
              (fun piece => cubes.cubeSets scale piece.1 piece.2)
              (fun cube =>
                mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
              (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g) y := by
    calc
      (∫ z : WaveSpaceTime,
        mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g z‖
        ∂continuumLightRayMeasure) ≤
          ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) *
            ∫ y : Euclidean 2,
              continuumFineAssignedCubeWeightedEnergy
                (mssFinePieceIndices D scale)
                (fun piece => cubes.cubeSets scale piece.1 piece.2)
                (fun cube =>
                  mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
                (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g) y := hpacket
      _ ≤ ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) *
          ((R : Real) * ∫ y : Euclidean 2,
            continuumFineCubeWeightedEnergy
              (mssFinePieceIndices D scale)
              (fun piece => cubes.cubeSets scale piece.1 piece.2)
              (fun cube =>
                mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
              (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g) y) :=
        mul_le_mul_of_nonneg_left hcollapse hfactor
      _ = ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) * (R : Real) *
          ∫ y : Euclidean 2,
            continuumFineCubeWeightedEnergy
              (mssFinePieceIndices D scale)
              (fun piece => cubes.cubeSets scale piece.1 piece.2)
              (fun cube =>
                mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
              (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g) y := by
        ring
  refine ⟨?_, ?_⟩
  · exact integrable_mul_norm_of_integrable_continuumLightRayMeasure_of_slab
      (fun z => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) g hg.slab
      regularity.squareWeighted
  · rw [integral_mul_norm_eq_integral_mul_norm_continuumLightRayMeasure_of_slab
      (fun z => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) g hg.slab]
    exact hcontinuum

/-- The decomposition supplies constants which are uniform before the
admissible light-ray test is chosen. -/
theorem exists_uniform_mssFineCubePacketSquarePairing_le_lightRayCubeEnergy_ambient
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant : Real)
    (localization : MSSFineCubeKernelLocalization D cubes N kernelConstant massConstant)
    {scale : Real} (hscale : 2 ≤ scale)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 2 < N)
    (f : SchwartzMap (Euclidean 2) Complex) :
    ∃ B R : Nat, ∀ g : WaveSpaceTime → Complex, LightRayBoundedCompactTest g →
      MSSFineCubeContinuumRegularity D cubes N kernelConstant massConstant scale f g →
        Integrable (fun z : WaveSpaceTime =>
          mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g z‖) volume ∧
        (∫ z : WaveSpaceTime,
          mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g z‖) ≤
          ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) * (R : Real) *
            ∫ y : Euclidean 2,
              continuumFineCubeWeightedEnergy
                (mssFinePieceIndices D scale)
                (fun piece => cubes.cubeSets scale piece.1 piece.2)
                (fun cube =>
                  mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
                (lightRayMaximal (cubes.cubeWidth * Real.sqrt scale)⁻¹ N g) y := by
  obtain ⟨B, hcard⟩ := cubes.cubes_per_packet
  obtain ⟨R, hoverlap⟩ := cubes.reverse_overlap
  have hcardReal : ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
        ((cubes.cubeSets scale n nu).card : Real) ≤ B := by
    intro scale hscale n hn nu hnu
    exact_mod_cast hcard scale hscale n hn nu hnu
  exact ⟨B, R,
    mssFineCubePacketSquarePairing_le_lightRayCubeEnergy_ambient_of_uniformBounds
      D cubes N kernelConstant massConstant localization B R hcardReal hoverlap hscale
      hwidth hN f⟩

/-- An abstract monotone-exhaustion closure.  The equality hypothesis is the
precise measure-theoretic content supplied by bounded compact truncations;
stating it at the `lintegral` level avoids a hidden prior integrability
assumption on `F`. -/
theorem integrable_sq_of_saturating_l2_tests
    (F : WaveSpaceTime → Real) (g : ℕ → WaveSpaceTime → Complex)
    (hFmeas : AEStronglyMeasurable F volume)
    (C : ENNReal) (hC : C < ∞)
    (hbound : ∀ n : ℕ,
      ∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g n z‖ ^ 2) ≤ C)
    (hsaturates :
      (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (F z ^ 2)) =
        ⨆ n : ℕ, ∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g n z‖ ^ 2)) :
    Integrable (fun z : WaveSpaceTime => F z ^ 2) volume ∧
      (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (F z ^ 2)) ≤ C := by
  have hfinite :
      (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (F z ^ 2)) < ∞ := by
    rw [hsaturates]
    exact (iSup_le fun n => hbound n).trans_lt hC
  have hnonneg : 0 ≤ᵐ[volume] fun z : WaveSpaceTime => F z ^ 2 :=
    Filter.Eventually.of_forall fun z => sq_nonneg (F z)
  have hFint : Integrable (fun z : WaveSpaceTime => F z ^ 2) volume := by
    refine ⟨hFmeas.pow 2, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hnonneg).mpr hfinite
  exact ⟨hFint, by rw [hsaturates]; exact iSup_le hbound⟩

/-- The elementary quadratic closure behind truncated duality. -/
private theorem sq_le_of_le_mul_sqrt {I L : Real}
    (hI : 0 ≤ I) (_hL : 0 ≤ L) (hle : I ≤ L * Real.sqrt I) :
    I ≤ L ^ 2 := by
  have hsqrt : (Real.sqrt I) ^ 2 = I := Real.sq_sqrt hI
  nlinarith [sq_nonneg (Real.sqrt I - L)]

/-- One bounded compact literal-slab test obeys the quadratic bound obtained
by combining a raw weighted pairing, Cauchy--Schwarz for `Q`, and a squared
`L²` light-ray maximal estimate. -/
theorem lightRay_test_sq_bound_of_weighted_pairing
    (F : WaveSpaceTime → Real) (Q : Euclidean 2 → Real)
    (M : (WaveSpaceTime → Complex) → Euclidean 2 → Real)
    (A B K : Real)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hK : 0 ≤ K)
    (hQmeas : AEStronglyMeasurable Q volume)
    (hQnonneg : ∀ y, 0 ≤ Q y)
    (hQsq : Integrable (fun y : Euclidean 2 => Q y ^ 2) volume)
    (hQbound : (∫ y : Euclidean 2, Q y ^ 2) ≤ B)
    (hHLE : ∀ g : WaveSpaceTime → Complex, LightRayBoundedCompactTest g →
      MemLp (M g) 2 volume ∧
      Integrable (fun y : Euclidean 2 => ‖M g y‖ ^ 2) volume ∧
      (∫ y : Euclidean 2, ‖M g y‖ ^ 2) ≤
        K ^ 2 * ∫ z : WaveSpaceTime, ‖g z‖ ^ 2)
    (hraw : ∀ g : WaveSpaceTime → Complex, LightRayBoundedCompactTest g →
      Integrable (fun z : WaveSpaceTime => F z * ‖g z‖) volume ∧
      Integrable (fun y : Euclidean 2 => Q y * ‖M g y‖) volume ∧
      (∫ z : WaveSpaceTime, F z * ‖g z‖) ≤
        A * ∫ y : Euclidean 2, Q y * ‖M g y‖)
    (g : WaveSpaceTime → Complex) (hg : LightRayBoundedCompactTest g)
    (hlower : (∫ z : WaveSpaceTime, ‖g z‖ ^ 2) ≤
      ∫ z : WaveSpaceTime, F z * ‖g z‖) :
    (∫ z : WaveSpaceTime, ‖g z‖ ^ 2) ≤
      (A * Real.sqrt B * K) ^ 2 := by
  let I : Real := ∫ z : WaveSpaceTime, ‖g z‖ ^ 2
  let J : Real := ∫ y : Euclidean 2, Q y ^ 2
  let H : Real := ∫ y : Euclidean 2, ‖M g y‖ ^ 2
  let T : Real := ∫ y : Euclidean 2, Q y * ‖M g y‖
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun z => sq_nonneg ‖g z‖
  have hQmem : MemLp Q 2 volume :=
    (memLp_two_iff_integrable_sq hQmeas).mpr hQsq
  obtain ⟨hMmem, hMsq, hH⟩ := hHLE g hg
  have hMnorm : MemLp (fun y : Euclidean 2 => ‖M g y‖) 2 volume := by
    simpa using hMmem.norm
  have hQmem' : MemLp Q (ENNReal.ofReal 2) volume := by
    norm_num
    exact hQmem
  have hMnorm' : MemLp (fun y : Euclidean 2 => ‖M g y‖)
      (ENNReal.ofReal 2) volume := by
    norm_num
    exact hMnorm
  have hholder : T ≤ Real.sqrt J * Real.sqrt H := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume) (p := (2 : Real)) (q := (2 : Real))
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall hQnonneg)
      (Filter.Eventually.of_forall fun y => norm_nonneg (M g y))
      hQmem' hMnorm'
    have hQpow :
        (∫ y : Euclidean 2, Q y ^ (2 : Real)) =
          ∫ y : Euclidean 2, Q y ^ 2 := by
      apply integral_congr_ae
      filter_upwards with y
      rw [Real.rpow_two]
    have hMpow :
        (∫ y : Euclidean 2, ‖M g y‖ ^ (2 : Real)) =
          ∫ y : Euclidean 2, ‖M g y‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with y
      rw [Real.rpow_two]
    dsimp [T, J, H]
    calc
      (∫ y : Euclidean 2, Q y * ‖M g y‖) ≤
          (∫ y : Euclidean 2, Q y ^ (2 : Real)) ^ (1 / (2 : Real)) *
            (∫ y : Euclidean 2, ‖M g y‖ ^ (2 : Real)) ^ (1 / (2 : Real)) := h
      _ = Real.sqrt (∫ y : Euclidean 2, Q y ^ 2) *
          Real.sqrt (∫ y : Euclidean 2, ‖M g y‖ ^ 2) := by
        rw [hQpow, hMpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hJ : J ≤ B := by
    simpa only [J] using hQbound
  have hH' : H ≤ K ^ 2 * I := by
    simpa only [H, I] using hH
  have hHroot : Real.sqrt H ≤ K * Real.sqrt I := by
    calc
      Real.sqrt H ≤ Real.sqrt (K ^ 2 * I) := Real.sqrt_le_sqrt hH'
      _ = Real.sqrt (K ^ 2) * Real.sqrt I :=
        Real.sqrt_mul (sq_nonneg K) I
      _ = K * Real.sqrt I := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hK]
  have hT : T ≤ (Real.sqrt B * K) * Real.sqrt I := by
    calc
      T ≤ Real.sqrt J * Real.sqrt H := hholder
      _ ≤ Real.sqrt B * Real.sqrt H :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hJ) (Real.sqrt_nonneg H)
      _ ≤ Real.sqrt B * (K * Real.sqrt I) :=
        mul_le_mul_of_nonneg_left hHroot (Real.sqrt_nonneg B)
      _ = (Real.sqrt B * K) * Real.sqrt I := by ring
  have hraw' := hraw g hg
  have hIle : I ≤ (A * Real.sqrt B * K) * Real.sqrt I := by
    calc
      I ≤ ∫ z : WaveSpaceTime, F z * ‖g z‖ := by
        simpa only [I] using hlower
      _ ≤ A * T := by
        simpa only [T] using hraw'.2.2
      _ ≤ A * ((Real.sqrt B * K) * Real.sqrt I) :=
        mul_le_mul_of_nonneg_left hT hA
      _ = (A * Real.sqrt B * K) * Real.sqrt I := by ring
  simpa only [I] using sq_le_of_le_mul_sqrt hI (by positivity) hIle

/-- Convert an ordinary square-energy bound for an `L²` function to the
nonnegative `lintegral` form needed by monotone exhaustion. -/
private theorem lintegral_sq_norm_le_of_integral_le
    (g : WaveSpaceTime → Complex) (hg : MemLp g 2 volume)
    (C : Real) (hC : (∫ z : WaveSpaceTime, ‖g z‖ ^ 2) ≤ C) :
    (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g z‖ ^ 2)) ≤ ENNReal.ofReal C := by
  have hgnorm : MemLp (fun z : WaveSpaceTime => ‖g z‖) 2 volume := by
    simpa using hg.norm
  have hgsq : Integrable (fun z : WaveSpaceTime => ‖g z‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq hgnorm.aestronglyMeasurable).mp hgnorm
  have hnonneg : 0 ≤ᵐ[volume] fun z : WaveSpaceTime => ‖g z‖ ^ 2 :=
    Filter.Eventually.of_forall fun z => sq_nonneg ‖g z‖
  have hfinite : (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g z‖ ^ 2)) < ∞ :=
    (hasFiniteIntegral_iff_ofReal hnonneg).mp hgsq.hasFiniteIntegral
  have hconvert : ENNReal.ofReal (∫ z : WaveSpaceTime, ‖g z‖ ^ 2) =
      ∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g z‖ ^ 2) := by
    rw [integral_eq_lintegral_of_nonneg_ae hnonneg hgsq.aestronglyMeasurable,
      ENNReal.ofReal_toReal hfinite.ne]
  rw [← hconvert]
  exact ENNReal.ofReal_le_ofReal hC

/-- A non-circular truncated-duality closure for the MSS square.  The raw
pairing is required only on literal slab-supported bounded compact tests.
The supplied sequence normally consists of spatial-ball and height
truncations of `F`; its saturation is explicit, so the theorem never assumes
the target `F ∈ L²` in order to invoke HLE. -/
theorem integrable_sq_of_saturating_weighted_lightRay_tests
    (F : WaveSpaceTime → Real) (Q : Euclidean 2 → Real)
    (M : (WaveSpaceTime → Complex) → Euclidean 2 → Real)
    (A B K : Real)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hFmeas : AEStronglyMeasurable F volume)
    (hQmeas : AEStronglyMeasurable Q volume)
    (hQnonneg : ∀ y, 0 ≤ Q y)
    (hQsq : Integrable (fun y : Euclidean 2 => Q y ^ 2) volume)
    (hQbound : (∫ y : Euclidean 2, Q y ^ 2) ≤ B)
    (hHLE : ∀ g : WaveSpaceTime → Complex, LightRayBoundedCompactTest g →
      MemLp (M g) 2 volume ∧
      Integrable (fun y : Euclidean 2 => ‖M g y‖ ^ 2) volume ∧
      (∫ y : Euclidean 2, ‖M g y‖ ^ 2) ≤
        K ^ 2 * ∫ z : WaveSpaceTime, ‖g z‖ ^ 2)
    (hraw : ∀ g : WaveSpaceTime → Complex, LightRayBoundedCompactTest g →
      Integrable (fun z : WaveSpaceTime => F z * ‖g z‖) volume ∧
      Integrable (fun y : Euclidean 2 => Q y * ‖M g y‖) volume ∧
      (∫ z : WaveSpaceTime, F z * ‖g z‖) ≤
        A * ∫ y : Euclidean 2, Q y * ‖M g y‖)
    (g : ℕ → WaveSpaceTime → Complex)
    (htest : ∀ n : ℕ, LightRayBoundedCompactTest (g n))
    (hlower : ∀ n : ℕ, (∫ z : WaveSpaceTime, ‖g n z‖ ^ 2) ≤
      ∫ z : WaveSpaceTime, F z * ‖g n z‖)
    (hsaturates :
      (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (F z ^ 2)) =
        ⨆ n : ℕ, ∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g n z‖ ^ 2)) :
    Integrable (fun z : WaveSpaceTime => F z ^ 2) volume ∧
      (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (F z ^ 2)) ≤
        ENNReal.ofReal ((A * Real.sqrt B * K) ^ 2) := by
  refine integrable_sq_of_saturating_l2_tests F g hFmeas
    (ENNReal.ofReal ((A * Real.sqrt B * K) ^ 2)) ENNReal.ofReal_lt_top ?_ hsaturates
  intro n
  exact lintegral_sq_norm_le_of_integral_le (g n) (htest n).memLp_two _
    (lightRay_test_sq_bound_of_weighted_pairing F Q M A B K hA hB hK
      hQmeas hQnonneg hQsq hQbound hHLE hraw (g n) (htest n) (hlower n))

/-- Bounded height and spatial-ball truncations supply the literal tests
needed by the non-circular duality closure.  The test at level `n` agrees
with `F` only where `F ≤ n` and `‖x‖ ≤ n`, so both the test and its weighted
pairing are bounded on a compact slab.  No prior `L²` assumption on `F` is
used. -/
theorem exists_saturating_lightRayBoundedCompactTests_of_measurable_nonneg_slab
    (F : WaveSpaceTime → Real) (hFmeas : Measurable F)
    (hFnonneg : ∀ z : WaveSpaceTime, 0 ≤ F z)
    (hFslab : F = (Set.univ ×ˢ lightRayTimeInterval).indicator F) :
    ∃ g : ℕ → WaveSpaceTime → Complex,
      (∀ n : ℕ, LightRayBoundedCompactTest (g n)) ∧
      (∀ n : ℕ, (∫ z : WaveSpaceTime, ‖g n z‖ ^ 2) ≤
        ∫ z : WaveSpaceTime, F z * ‖g n z‖) ∧
      (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (F z ^ 2)) =
        ⨆ n : ℕ, ∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g n z‖ ^ 2) := by
  classical
  let slab : Set WaveSpaceTime := Set.univ ×ˢ lightRayTimeInterval
  have hslabMeas : MeasurableSet slab := by
    dsimp [slab]
    exact MeasurableSet.univ.prod (by
      unfold lightRayTimeInterval
      exact measurableSet_Icc)
  let E : ℕ → Set WaveSpaceTime := fun n =>
    slab ∩ ({z : WaveSpaceTime | ‖z.1‖ ≤ (n : Real)} ∩
      {z : WaveSpaceTime | F z ≤ (n : Real)})
  have hEmeas : ∀ n : ℕ, MeasurableSet (E n) := by
    intro n
    have hspatial : MeasurableSet {z : WaveSpaceTime | ‖z.1‖ ≤ (n : Real)} := by
      exact measurableSet_le (continuous_norm.comp continuous_fst).measurable measurable_const
    have hheight : MeasurableSet {z : WaveSpaceTime | F z ≤ (n : Real)} := by
      exact measurableSet_le hFmeas measurable_const
    exact hslabMeas.inter (hspatial.inter hheight)
  let g : ℕ → WaveSpaceTime → Complex := fun n =>
    (E n).indicator (fun z : WaveSpaceTime => (F z : Complex))
  have hgmeas : ∀ n : ℕ, Measurable (g n) := by
    intro n
    exact (Complex.continuous_ofReal.measurable.comp hFmeas).indicator (hEmeas n)
  have hEmono : Monotone E := by
    intro i j hij z hz
    have hij' : (i : Real) ≤ (j : Real) := by exact_mod_cast hij
    change z ∈ slab ∧ ‖z.1‖ ≤ (i : Real) ∧ F z ≤ (i : Real) at hz
    change z ∈ slab ∧ ‖z.1‖ ≤ (j : Real) ∧ F z ≤ (j : Real)
    exact ⟨hz.1, hz.2.1.trans hij', hz.2.2.trans hij'⟩
  have htest : ∀ n : ℕ, LightRayBoundedCompactTest (g n) := by
    intro n
    have hbound : ∀ z : WaveSpaceTime, ‖g n z‖ ≤ (n : Real) := by
      intro z
      by_cases hz : z ∈ E n
      · have hFle : F z ≤ (n : Real) := by
          change z ∈ slab ∧ ‖z.1‖ ≤ (n : Real) ∧ F z ≤ (n : Real) at hz
          exact hz.2.2
        rw [show g n z = (F z : Complex) by simp [g, hz],
          Complex.norm_of_nonneg (hFnonneg z)]
        exact hFle
      · simp [g, hz]
    have hcompact : HasCompactSupport (g n) := by
      apply HasCompactSupport.of_support_subset_isCompact
        ((isCompact_closedBall (0 : Euclidean 2) (n : Real)).prod
          (show IsCompact lightRayTimeInterval by
            unfold lightRayTimeInterval
            exact isCompact_Icc))
      intro z hz
      have hzE : z ∈ E n := by
        by_contra hnot
        apply hz
        simp [g, hnot]
      change z.1 ∈ Metric.closedBall (0 : Euclidean 2) (n : Real) ∧
        z.2 ∈ lightRayTimeInterval
      constructor
      · simpa only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right] using hzE.2.1
      · change z ∈ slab ∧ ‖z.1‖ ≤ (n : Real) ∧ F z ≤ (n : Real) at hzE
        simpa only [slab, Set.mem_prod, Set.mem_univ, true_and] using hzE.1
    refine
      { memLp_two := hcompact.memLp_of_bound (hgmeas n).aestronglyMeasurable (n : Real)
          (Filter.Eventually.of_forall hbound)
        slab := ?_
        bounded := ⟨(n : Real), Nat.cast_nonneg n, hbound⟩
        compact_spatial := ?_ }
    · funext z
      by_cases hz : z ∈ slab
      · have hz' : z ∈ Set.univ ×ˢ lightRayTimeInterval := by
          simpa only [slab] using hz
        simp [hz']
      · have hnot : z ∉ E n := fun hzE => hz (by
          change z ∈ slab ∧ ‖z.1‖ ≤ (n : Real) ∧ F z ≤ (n : Real) at hzE
          exact hzE.1)
        have hz' : z ∉ Set.univ ×ˢ lightRayTimeInterval := by
          simpa only [slab] using hz
        simp [g, hnot, hz']
    · refine ⟨(n : Real), ?_⟩
      intro z hz
      have hnot : z ∉ E n := by
        intro hzE
        change z ∈ slab ∧ ‖z.1‖ ≤ (n : Real) ∧ F z ≤ (n : Real) at hzE
        exact (not_le_of_gt hz) hzE.2.1
      simp [g, hnot]
  have hlower : ∀ n : ℕ, (∫ z : WaveSpaceTime, ‖g n z‖ ^ 2) ≤
      ∫ z : WaveSpaceTime, F z * ‖g n z‖ := by
    intro n
    apply le_of_eq
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ E n
    · rw [show g n z = (F z : Complex) by simp [g, hz],
        Complex.norm_of_nonneg (hFnonneg z)]
      ring
    · simp [g, hz]
  have henergy : ∀ (n : ℕ) (z : WaveSpaceTime),
      ENNReal.ofReal (‖g n z‖ ^ 2) =
        (E n).indicator (fun z : WaveSpaceTime => ENNReal.ofReal (F z ^ 2)) z := by
    intro n z
    by_cases hz : z ∈ E n
    · simp [g, hz, Real.norm_eq_abs, abs_of_nonneg (hFnonneg z)]
    · simp [g, hz]
  have hphiMeas : ∀ n : ℕ,
      Measurable (fun z : WaveSpaceTime => ENNReal.ofReal (‖g n z‖ ^ 2)) := by
    intro n
    exact ENNReal.measurable_ofReal.comp ((hgmeas n).norm.pow_const 2)
  have hphiMono : Monotone (fun n : ℕ =>
      fun z : WaveSpaceTime => ENNReal.ofReal (‖g n z‖ ^ 2)) := by
    intro i j hij z
    change ENNReal.ofReal (‖g i z‖ ^ 2) ≤ ENNReal.ofReal (‖g j z‖ ^ 2)
    rw [henergy i z, henergy j z]
    by_cases hz : z ∈ E i
    · have hz' : z ∈ E j := hEmono hij hz
      simp [hz, hz']
    · simp [hz]
  have hsup : ∀ z : WaveSpaceTime,
      (⨆ n : ℕ, ENNReal.ofReal (‖g n z‖ ^ 2)) = ENNReal.ofReal (F z ^ 2) := by
    intro z
    apply le_antisymm
    · refine iSup_le ?_
      intro n
      rw [henergy n z]
      by_cases hz : z ∈ E n <;> simp [hz]
    · by_cases hzero : F z = 0
      · simp [hzero]
      · have hzslab : z ∈ slab := by
          have hslabAt : F z = slab.indicator F z := by
            simpa only [slab] using congrFun hFslab z
          by_contra hz
          apply hzero
          rw [hslabAt]
          simp [hz]
        obtain ⟨n, hn⟩ := exists_nat_ge (max ‖z.1‖ (F z))
        have hspatial : ‖z.1‖ ≤ (n : Real) := (le_max_left _ _).trans hn
        have hheight : F z ≤ (n : Real) := (le_max_right _ _).trans hn
        have hzE : z ∈ E n := by
          change z ∈ slab ∧ ‖z.1‖ ≤ (n : Real) ∧ F z ≤ (n : Real)
          exact ⟨hzslab, hspatial, hheight⟩
        calc
          ENNReal.ofReal (F z ^ 2) = ENNReal.ofReal (‖g n z‖ ^ 2) := by
            rw [henergy n z]
            simp [hzE]
          _ ≤ ⨆ n : ℕ, ENNReal.ofReal (‖g n z‖ ^ 2) :=
            le_iSup (fun m : ℕ => ENNReal.ofReal (‖g m z‖ ^ 2)) n
  refine ⟨g, htest, hlower, ?_⟩
  calc
    (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (F z ^ 2)) =
        ∫⁻ z : WaveSpaceTime, ⨆ n : ℕ, ENNReal.ofReal (‖g n z‖ ^ 2) := by
      apply lintegral_congr
      intro z
      exact (hsup z).symm
    _ = ⨆ n : ℕ, ∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g n z‖ ^ 2) :=
      lintegral_iSup hphiMeas hphiMono

/-- The fixed-scale truncated-duality closure with all structural constants
supplied in advance.  Keeping `Cq`, `Ch`, `B`, and `R` as inputs is what lets
the subsequent slab wrapper choose them before the scale and Schwartz input. -/
private theorem mssFineCubePacketSquareFunction_fourthMoment_of_explicit_uniform_constants
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant Cq Ch : Real) (B R : Nat)
    (localization : MSSFineCubeKernelLocalization D cubes N kernelConstant massConstant)
    (hCq : 0 < Cq)
    (hQenergy : ∀ scale : Real, 2 ≤ scale →
      ∀ f : SchwartzMap (Euclidean 2) Complex,
        Integrable (fun y : Euclidean 2 =>
          (continuumFineCubeSquareEnergy
            (mssFinePieceIndices D scale)
            (fun piece => cubes.cubeSets scale piece.1 piece.2)
            (fun cube =>
              mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) ^ 2) volume ∧
        (∫ y : Euclidean 2,
          (continuumFineCubeSquareEnergy
            (mssFinePieceIndices D scale)
            (fun piece => cubes.cubeSets scale piece.1 piece.2)
            (fun cube =>
              mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y) ^ 2) ≤
          ‖(kernelConstant : Complex)‖ ^ 4 * Cq *
            ∫ y : Euclidean 2, ‖f y‖ ^ 4)
    (hCh : 0 < Ch)
    (hHLEbound : ∀ {δ : Real}, 0 < δ → δ < 1 / 2 →
      ∀ g : WaveSpaceTime → Complex, LightRayBoundedCompactTest g →
        MemLp (lightRayMaximal δ N g) 2 volume ∧
          Integrable (fun y : Euclidean 2 => ‖lightRayMaximal δ N g y‖ ^ 2) volume ∧
          (∫ y : Euclidean 2, ‖lightRayMaximal δ N g y‖ ^ 2) ≤
            (Ch * (1 + |Real.log δ|) ^ (3 / 2 : Real)) ^ 2 *
              ∫ z : WaveSpaceTime, ‖g z‖ ^ 2)
    (hcard : ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
        ((cubes.cubeSets scale n nu).card : Real) ≤ B)
    (hoverlap : ∀ scale : Real, 2 ≤ scale →
      HasFiniteFineCubeReverseOverlap (mssFinePieceIndices D scale)
        (fun piece => cubes.cubeSets scale piece.1 piece.2) R)
    {scale : Real} (hscale : 2 ≤ scale)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 3 < N)
    (f : SchwartzMap (Euclidean 2) Complex)
    (hFmeas : AEStronglyMeasurable
      (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2)
      volume)
    (hregularity : ∀ test : WaveSpaceTime → Complex, LightRayBoundedCompactTest test →
      MSSFineCubeContinuumRegularity D cubes N kernelConstant massConstant scale f test)
    (g : ℕ → WaveSpaceTime → Complex)
    (htest : ∀ n : ℕ, LightRayBoundedCompactTest (g n))
    (hlower : ∀ n : ℕ,
      (∫ z : WaveSpaceTime, ‖g n z‖ ^ 2) ≤
        ∫ z : WaveSpaceTime,
          mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g n z‖)
    (hsaturates :
      (∫⁻ z : WaveSpaceTime,
        ENNReal.ofReal ((mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2)) =
        ⨆ n : ℕ, ∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g n z‖ ^ 2)) :
    Integrable (fun z : WaveSpaceTime =>
      (mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2) volume ∧
      (∫⁻ z : WaveSpaceTime,
        ENNReal.ofReal ((mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2)) ≤
        ENNReal.ofReal
          (((((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) * (R : Real)) *
              Real.sqrt (‖(kernelConstant : Complex)‖ ^ 4 * Cq *
                ∫ y : Euclidean 2, ‖f y‖ ^ 4) *
              (Ch * (1 + |Real.log ((cubes.cubeWidth * Real.sqrt scale)⁻¹)|) ^
                (3 / 2 : Real))) ^ 2) := by
  classical
  let F : WaveSpaceTime → Real := fun z =>
    mssFineCubePacketSquareFunction D cubes scale f z ^ 2
  let Q : Euclidean 2 → Real := fun y =>
    continuumFineCubeSquareEnergy
      (mssFinePieceIndices D scale)
      (fun piece => cubes.cubeSets scale piece.1 piece.2)
      (fun cube => mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y
  let δ : Real := (cubes.cubeWidth * Real.sqrt scale)⁻¹
  let M : (WaveSpaceTime → Complex) → Euclidean 2 → Real := fun test =>
    lightRayMaximal δ N test
  have hδ : 0 < δ := by
    simpa [δ] using (cubeWidth_inv_mul_sqrt_pos_lt_half hwidth hscale).1
  have hδsmall : δ < 1 / 2 := by
    simpa [δ] using (cubeWidth_inv_mul_sqrt_pos_lt_half hwidth hscale).2
  have hNpair : 2 < N := by omega
  obtain ⟨hQsq', hQbound'⟩ := hQenergy scale hscale f
  let E : Real := ‖(kernelConstant : Complex)‖ ^ 4 * Cq *
    ∫ y : Euclidean 2, ‖f y‖ ^ 4
  have hE : 0 ≤ E := by
    have hf : 0 ≤ ∫ y : Euclidean 2, ‖f y‖ ^ 4 :=
      integral_nonneg fun y => pow_nonneg (norm_nonneg (f y)) _
    dsimp [E]
    exact mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) hCq.le) hf
  have hQmeas : AEStronglyMeasurable Q volume := by
    simpa [Q] using
      (continuous_continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
        D cubes kernelConstant scale f).aestronglyMeasurable
  have hQnonneg : ∀ y : Euclidean 2, 0 ≤ Q y := by
    intro y
    simpa [Q] using
      continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput_nonneg
        D cubes kernelConstant scale f y
  have hQsq : Integrable (fun y : Euclidean 2 => Q y ^ 2) volume := by
    simpa [Q] using hQsq'
  have hQbound : (∫ y : Euclidean 2, Q y ^ 2) ≤ E := by
    simpa [Q, E] using hQbound'
  let K : Real := Ch * (1 + |Real.log δ|) ^ (3 / 2 : Real)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  let A : Real := ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) * (R : Real)
  have hmass : 0 ≤ ∫ u : Euclidean 2, lightRayDecayProfile N u :=
    (lightRayKernel_spatial_mass_bound hδ N hNpair (0 : Euclidean 2)).1
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg B) hmass) (Nat.cast_nonneg R)
  have hHLE : ∀ test : WaveSpaceTime → Complex, LightRayBoundedCompactTest test →
      MemLp (M test) 2 volume ∧
        Integrable (fun y : Euclidean 2 => ‖M test y‖ ^ 2) volume ∧
        (∫ y : Euclidean 2, ‖M test y‖ ^ 2) ≤
          K ^ 2 * ∫ z : WaveSpaceTime, ‖test z‖ ^ 2 := by
    intro test htest
    simpa [M, K] using hHLEbound hδ hδsmall test htest
  have hpairing :=
    mssFineCubePacketSquarePairing_le_lightRayCubeEnergy_ambient_of_uniformBounds
      D cubes N kernelConstant massConstant localization B R hcard hoverlap hscale
      hwidth hNpair f
  have hraw : ∀ test : WaveSpaceTime → Complex, LightRayBoundedCompactTest test →
      Integrable (fun z : WaveSpaceTime => F z * ‖test z‖) volume ∧
      Integrable (fun y : Euclidean 2 => Q y * ‖M test y‖) volume ∧
      (∫ z : WaveSpaceTime, F z * ‖test z‖) ≤
        A * ∫ y : Euclidean 2, Q y * ‖M test y‖ := by
    intro test htest
    have hreg := hregularity test htest
    obtain ⟨hFint, hFbound⟩ := hpairing test htest hreg
    have hQM : Integrable (fun y : Euclidean 2 => Q y * M test y) volume := by
      change Integrable
        (continuumFineCubeWeightedEnergy
          (mssFinePieceIndices D scale)
          (fun piece => cubes.cubeSets scale piece.1 piece.2)
          (fun cube => mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
          (lightRayMaximal δ N test)) volume
      simpa [δ] using
        (integrable_continuumFineCubeWeightedEnergy_of_mssFineCubeContinuumRegularity
          D cubes N kernelConstant massConstant scale f test hscale hreg)
    have hMnonneg : ∀ y : Euclidean 2, 0 ≤ M test y := by
      intro y
      have hNone : 1 < N := by omega
      simpa [M] using
        scratch_lightRayMaximal_nonneg_of_memLp hδ N hNone test htest.memLp_two y
    have hnorm : ∀ y : Euclidean 2, ‖M test y‖ = M test y := by
      intro y
      simp only [Real.norm_eq_abs, abs_of_nonneg (hMnonneg y)]
    have hQMnorm : Integrable (fun y : Euclidean 2 => Q y * ‖M test y‖) volume := by
      refine hQM.congr ?_
      filter_upwards with y
      rw [hnorm y]
    refine ⟨?_, hQMnorm, ?_⟩
    · simpa [F] using hFint
    · calc
        (∫ z : WaveSpaceTime, F z * ‖test z‖) ≤
            A * ∫ y : Euclidean 2, Q y * M test y := by
          simpa [F, Q, M, A, δ, continuumFineCubeWeightedEnergy] using hFbound
        _ = A * ∫ y : Euclidean 2, Q y * ‖M test y‖ := by
          rw [show (∫ y : Euclidean 2, Q y * M test y) =
              ∫ y : Euclidean 2, Q y * ‖M test y‖ by
            apply integral_congr_ae
            filter_upwards with y
            rw [hnorm y]]
  have hFmeas' : AEStronglyMeasurable F volume := by
    simpa [F] using hFmeas
  have hlower' : ∀ n : ℕ, (∫ z : WaveSpaceTime, ‖g n z‖ ^ 2) ≤
      ∫ z : WaveSpaceTime, F z * ‖g n z‖ := by
    intro n
    simpa [F] using hlower n
  have hsaturates' :
      (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (F z ^ 2)) =
        ⨆ n : ℕ, ∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g n z‖ ^ 2) := by
    simpa [F] using hsaturates
  simpa [F, A, E, K, δ] using
    (integrable_sq_of_saturating_weighted_lightRay_tests F Q M A E K
      hA hE hK hFmeas' hQmeas hQnonneg hQsq hQbound hHLE hraw g htest hlower'
      hsaturates')

/-- Conditional fixed-scale fourth-moment closure for the MSS fine cube
packet square.  The analysis-cube Rademacher estimate, the literal
kernel-localization/transposition data, regularity for every bounded compact
test, and the monotone truncation saturation are all retained as explicit
hypotheses.  In particular, this does not assert an unconditional fine-square
estimate. -/
theorem mssFineCubePacketSquareFunction_fourthMoment_of_analysisAverage_and_saturating_tests
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant : Real)
    (localization : MSSFineCubeKernelLocalization D cubes N kernelConstant massConstant)
    {scale : Real} (hscale : 2 ≤ scale)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 3 < N)
    (f : SchwartzMap (Euclidean 2) Complex)
    (haverage : HasScaleAverageMSSAnalysisCubeRademacherL4 D cubes)
    (hFmeas : AEStronglyMeasurable
      (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2)
      volume)
    (hregularity : ∀ test : WaveSpaceTime → Complex, LightRayBoundedCompactTest test →
      MSSFineCubeContinuumRegularity D cubes N kernelConstant massConstant scale f test)
    (g : ℕ → WaveSpaceTime → Complex)
    (htest : ∀ n : ℕ, LightRayBoundedCompactTest (g n))
    (hlower : ∀ n : ℕ,
      (∫ z : WaveSpaceTime, ‖g n z‖ ^ 2) ≤
        ∫ z : WaveSpaceTime,
          mssFineCubePacketSquareFunction D cubes scale f z ^ 2 * ‖g n z‖)
    (hsaturates :
      (∫⁻ z : WaveSpaceTime,
        ENNReal.ofReal ((mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2)) =
        ⨆ n : ℕ, ∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g n z‖ ^ 2)) :
    ∃ A E K : Real, 0 ≤ A ∧ 0 ≤ E ∧ 0 ≤ K ∧
      Integrable (fun z : WaveSpaceTime =>
        (mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2) volume ∧
      (∫⁻ z : WaveSpaceTime,
        ENNReal.ofReal ((mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2)) ≤
        ENNReal.ofReal ((A * Real.sqrt E * K) ^ 2) := by
  classical
  let F : WaveSpaceTime → Real := fun z =>
    mssFineCubePacketSquareFunction D cubes scale f z ^ 2
  let Q : Euclidean 2 → Real := fun y =>
    continuumFineCubeSquareEnergy
      (mssFinePieceIndices D scale)
      (fun piece => cubes.cubeSets scale piece.1 piece.2)
      (fun cube => mssFineNormalizedCubeInput D cubes kernelConstant scale cube f) y
  let δ : Real := (cubes.cubeWidth * Real.sqrt scale)⁻¹
  let M : (WaveSpaceTime → Complex) → Euclidean 2 → Real := fun test =>
    lightRayMaximal δ N test
  have hδ : 0 < δ := by
    simpa [δ] using (cubeWidth_inv_mul_sqrt_pos_lt_half hwidth hscale).1
  have hδsmall : δ < 1 / 2 := by
    simpa [δ] using (cubeWidth_inv_mul_sqrt_pos_lt_half hwidth hscale).2
  have hNpair : 2 < N := by omega
  obtain ⟨Cq, hCq, hQenergy⟩ :=
    exists_uniform_mssFineNormalizedCubeEnergy_L2_bound_of_analysis_average
      D cubes kernelConstant haverage
  obtain ⟨hQsq', hQbound'⟩ := hQenergy scale hscale f
  let E : Real := ‖(kernelConstant : Complex)‖ ^ 4 * Cq *
    ∫ y : Euclidean 2, ‖f y‖ ^ 4
  have hE : 0 ≤ E := by
    have hf : 0 ≤ ∫ y : Euclidean 2, ‖f y‖ ^ 4 :=
      integral_nonneg fun y => pow_nonneg (norm_nonneg (f y)) _
    dsimp [E]
    exact mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) hCq.le) hf
  have hQmeas : AEStronglyMeasurable Q volume := by
    simpa [Q] using
      (continuous_continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput
        D cubes kernelConstant scale f).aestronglyMeasurable
  have hQnonneg : ∀ y : Euclidean 2, 0 ≤ Q y := by
    intro y
    simpa [Q] using
      continuumFineCubeSquareEnergy_mssFineNormalizedCubeInput_nonneg
        D cubes kernelConstant scale f y
  have hQsq : Integrable (fun y : Euclidean 2 => Q y ^ 2) volume := by
    simpa [Q] using hQsq'
  have hQbound : (∫ y : Euclidean 2, Q y ^ 2) ≤ E := by
    simpa [Q, E] using hQbound'
  obtain ⟨Ch, hCh, hHLEbound⟩ :=
    exists_uniform_lightRayMaximal_norm_sq_bound_on_boundedCompactTests
      N hN
  let K : Real := Ch * (1 + |Real.log δ|) ^ (3 / 2 : Real)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  obtain ⟨B, R, hpairing⟩ :=
    exists_uniform_mssFineCubePacketSquarePairing_le_lightRayCubeEnergy_ambient
      D cubes N kernelConstant massConstant localization hscale hwidth hNpair f
  let A : Real := ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) * (R : Real)
  have hmass : 0 ≤ ∫ u : Euclidean 2, lightRayDecayProfile N u :=
    (lightRayKernel_spatial_mass_bound hδ N hNpair (0 : Euclidean 2)).1
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg B) hmass) (Nat.cast_nonneg R)
  have hHLE : ∀ test : WaveSpaceTime → Complex, LightRayBoundedCompactTest test →
      MemLp (M test) 2 volume ∧
        Integrable (fun y : Euclidean 2 => ‖M test y‖ ^ 2) volume ∧
        (∫ y : Euclidean 2, ‖M test y‖ ^ 2) ≤
          K ^ 2 * ∫ z : WaveSpaceTime, ‖test z‖ ^ 2 := by
    intro test htest
    simpa [M, K] using hHLEbound hδ hδsmall test htest
  have hraw : ∀ test : WaveSpaceTime → Complex, LightRayBoundedCompactTest test →
      Integrable (fun z : WaveSpaceTime => F z * ‖test z‖) volume ∧
      Integrable (fun y : Euclidean 2 => Q y * ‖M test y‖) volume ∧
      (∫ z : WaveSpaceTime, F z * ‖test z‖) ≤
        A * ∫ y : Euclidean 2, Q y * ‖M test y‖ := by
    intro test htest
    have hreg := hregularity test htest
    obtain ⟨hFint, hFbound⟩ := hpairing test htest hreg
    have hQM : Integrable (fun y : Euclidean 2 => Q y * M test y) volume := by
      change Integrable
        (continuumFineCubeWeightedEnergy
          (mssFinePieceIndices D scale)
          (fun piece => cubes.cubeSets scale piece.1 piece.2)
          (fun cube => mssFineNormalizedCubeInput D cubes kernelConstant scale cube f)
          (lightRayMaximal δ N test)) volume
      simpa [δ] using
        (integrable_continuumFineCubeWeightedEnergy_of_mssFineCubeContinuumRegularity
          D cubes N kernelConstant massConstant scale f test hscale hreg)
    have hMnonneg : ∀ y : Euclidean 2, 0 ≤ M test y := by
      intro y
      have hNone : 1 < N := by omega
      simpa [M] using
        scratch_lightRayMaximal_nonneg_of_memLp hδ N hNone test htest.memLp_two y
    have hnorm : ∀ y : Euclidean 2, ‖M test y‖ = M test y := by
      intro y
      simp only [Real.norm_eq_abs, abs_of_nonneg (hMnonneg y)]
    have hQMnorm : Integrable (fun y : Euclidean 2 => Q y * ‖M test y‖) volume := by
      refine hQM.congr ?_
      filter_upwards with y
      rw [hnorm y]
    refine ⟨?_, hQMnorm, ?_⟩
    · simpa [F] using hFint
    · calc
        (∫ z : WaveSpaceTime, F z * ‖test z‖) ≤
            A * ∫ y : Euclidean 2, Q y * M test y := by
          simpa [F, Q, M, A, δ, continuumFineCubeWeightedEnergy] using hFbound
        _ = A * ∫ y : Euclidean 2, Q y * ‖M test y‖ := by
          rw [show (∫ y : Euclidean 2, Q y * M test y) =
              ∫ y : Euclidean 2, Q y * ‖M test y‖ by
            apply integral_congr_ae
            filter_upwards with y
            rw [hnorm y]]
  have hFmeas' : AEStronglyMeasurable F volume := by
    simpa [F] using hFmeas
  have hlower' : ∀ n : ℕ, (∫ z : WaveSpaceTime, ‖g n z‖ ^ 2) ≤
      ∫ z : WaveSpaceTime, F z * ‖g n z‖ := by
    intro n
    simpa [F] using hlower n
  have hsaturates' :
      (∫⁻ z : WaveSpaceTime, ENNReal.ofReal (F z ^ 2)) =
        ⨆ n : ℕ, ∫⁻ z : WaveSpaceTime, ENNReal.ofReal (‖g n z‖ ^ 2) := by
    simpa [F] using hsaturates
  refine ⟨A, E, K, hA, hE, hK, ?_⟩
  simpa [F] using
    (integrable_sq_of_saturating_weighted_lightRay_tests F Q M A E K
      hA hE hK hFmeas' hQmeas hQnonneg hQsq hQbound hHLE hraw g htest hlower'
      hsaturates')

/-- Fixed-scale fourth-moment closure with the test exhaustion supplied
internally.  Joint continuity gives the required measurability, while literal
time-slab support and nonnegativity produce the bounded compact saturating
tests. -/
theorem mssFineCubePacketSquareFunction_fourthMoment_of_analysisAverage_slab_and_universal_regularity
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant : Real)
    (localization : MSSFineCubeKernelLocalization D cubes N kernelConstant massConstant)
    {scale : Real} (hscale : 2 ≤ scale)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 3 < N)
    (f : SchwartzMap (Euclidean 2) Complex)
    (hslab : D.HasLightRayTimeSlabSupport)
    (haverage : HasScaleAverageMSSAnalysisCubeRademacherL4 D cubes)
    (hregularity : ∀ test : WaveSpaceTime → Complex, LightRayBoundedCompactTest test →
      MSSFineCubeContinuumRegularity D cubes N kernelConstant massConstant scale f test) :
    ∃ A E K : Real, 0 ≤ A ∧ 0 ≤ E ∧ 0 ≤ K ∧
      Integrable (fun z : WaveSpaceTime =>
        (mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2) volume ∧
      (∫⁻ z : WaveSpaceTime,
        ENNReal.ofReal ((mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2)) ≤
        ENNReal.ofReal ((A * Real.sqrt E * K) ^ 2) := by
  have hFcont : Continuous (fun z : WaveSpaceTime =>
      mssFineCubePacketSquareFunction D cubes scale f z ^ 2) :=
    continuous_sq_mssFineCubePacketSquareFunction D cubes scale f
  have hFmeas : AEStronglyMeasurable (fun z : WaveSpaceTime =>
      mssFineCubePacketSquareFunction D cubes scale f z ^ 2) volume :=
    hFcont.aestronglyMeasurable
  have hFmeasurable : Measurable (fun z : WaveSpaceTime =>
      mssFineCubePacketSquareFunction D cubes scale f z ^ 2) :=
    hFcont.measurable
  have hFnonneg : ∀ z : WaveSpaceTime,
      0 ≤ mssFineCubePacketSquareFunction D cubes scale f z ^ 2 := by
    intro z
    exact sq_nonneg _
  have hFslab :
      (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) =
        (Set.univ ×ˢ lightRayTimeInterval).indicator
          (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) :=
    sq_mssFineCubePacketSquareFunction_eq_indicator_lightRayTimeSlab
      D cubes hslab scale f
  obtain ⟨g, htest, hlower, hsaturates⟩ :=
    exists_saturating_lightRayBoundedCompactTests_of_measurable_nonneg_slab
      (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2)
      hFmeasurable hFnonneg hFslab
  exact
    mssFineCubePacketSquareFunction_fourthMoment_of_analysisAverage_and_saturating_tests
      D cubes N kernelConstant massConstant localization hscale hwidth hN f haverage
      hFmeas hregularity g htest hlower hsaturates

/-- The literal kernel localization, a fixed time slab, and the averaged
analysis-cube fourth-moment input yield the fixed-scale fourth-moment closure
without a separately supplied regularity package.  The result remains
conditional on precisely those three analytic inputs. -/
theorem mssFineCubePacketSquareFunction_fourthMoment_of_analysisAverage_slab
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant : Real)
    (localization : MSSFineCubeKernelLocalization D cubes N kernelConstant massConstant)
    {scale : Real} (hscale : 2 ≤ scale)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 3 < N)
    (f : SchwartzMap (Euclidean 2) Complex)
    (hslab : D.HasLightRayTimeSlabSupport)
    (haverage : HasScaleAverageMSSAnalysisCubeRademacherL4 D cubes) :
    ∃ A E K : Real, 0 ≤ A ∧ 0 ≤ E ∧ 0 ≤ K ∧
      Integrable (fun z : WaveSpaceTime =>
        (mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2) volume ∧
      (∫⁻ z : WaveSpaceTime,
        ENNReal.ofReal ((mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2)) ≤
        ENNReal.ofReal ((A * Real.sqrt E * K) ^ 2) := by
  apply
    mssFineCubePacketSquareFunction_fourthMoment_of_analysisAverage_slab_and_universal_regularity
      D cubes N kernelConstant massConstant localization hscale hwidth hN f hslab haverage
  intro test htest
  exact mssFineCubeContinuumRegularity_of_localization_of_boundedCompactTest
    D cubes N kernelConstant massConstant localization hscale hwidth hN f test htest

/-- The literal localization, fixed time slab, and averaged analysis-cube
input choose all structural fourth-moment constants before the MSS scale and
Schwartz input.  The remaining scale dependence is displayed solely in the
natural light-ray logarithm. -/
private theorem exists_uniform_mssFineCubePacketSquareFunction_fourthMoment_of_analysisAverage_slab
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant : Real)
    (localization : MSSFineCubeKernelLocalization D cubes N kernelConstant massConstant)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 3 < N)
    (hslab : D.HasLightRayTimeSlabSupport)
    (haverage : HasScaleAverageMSSAnalysisCubeRademacherL4 D cubes) :
    ∃ Cq Ch : Real, ∃ B R : Nat, 0 < Cq ∧ 0 < Ch ∧
      ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
        Integrable (fun z : WaveSpaceTime =>
          (mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2) volume ∧
        (∫⁻ z : WaveSpaceTime,
          ENNReal.ofReal ((mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2)) ≤
          ENNReal.ofReal
            (((((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) * (R : Real)) *
                Real.sqrt (‖(kernelConstant : Complex)‖ ^ 4 * Cq *
                  ∫ y : Euclidean 2, ‖f y‖ ^ 4) *
                (Ch * (1 + |Real.log ((cubes.cubeWidth * Real.sqrt scale)⁻¹)|) ^
                  (3 / 2 : Real))) ^ 2) := by
  obtain ⟨Cq, hCq, hQenergy⟩ :=
    exists_uniform_mssFineNormalizedCubeEnergy_L2_bound_of_analysis_average
      D cubes kernelConstant haverage
  obtain ⟨Ch, hCh, hHLEbound⟩ :=
    exists_uniform_lightRayMaximal_norm_sq_bound_on_boundedCompactTests N hN
  obtain ⟨B, hcard⟩ := cubes.cubes_per_packet
  obtain ⟨R, hoverlap⟩ := cubes.reverse_overlap
  have hcardReal : ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
        ((cubes.cubeSets scale n nu).card : Real) ≤ B := by
    intro scale hscale n hn nu hnu
    exact_mod_cast hcard scale hscale n hn nu hnu
  refine ⟨Cq, Ch, B, R, hCq, hCh, ?_⟩
  intro scale hscale f
  have hFcont : Continuous (fun z : WaveSpaceTime =>
      mssFineCubePacketSquareFunction D cubes scale f z ^ 2) :=
    continuous_sq_mssFineCubePacketSquareFunction D cubes scale f
  have hFmeas : AEStronglyMeasurable (fun z : WaveSpaceTime =>
      mssFineCubePacketSquareFunction D cubes scale f z ^ 2) volume :=
    hFcont.aestronglyMeasurable
  have hFmeasurable : Measurable (fun z : WaveSpaceTime =>
      mssFineCubePacketSquareFunction D cubes scale f z ^ 2) :=
    hFcont.measurable
  have hFnonneg : ∀ z : WaveSpaceTime,
      0 ≤ mssFineCubePacketSquareFunction D cubes scale f z ^ 2 := by
    intro z
    exact sq_nonneg _
  have hFslab :
      (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) =
        (Set.univ ×ˢ lightRayTimeInterval).indicator
          (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) :=
    sq_mssFineCubePacketSquareFunction_eq_indicator_lightRayTimeSlab
      D cubes hslab scale f
  obtain ⟨g, htest, hlower, hsaturates⟩ :=
    exists_saturating_lightRayBoundedCompactTests_of_measurable_nonneg_slab
      (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2)
      hFmeasurable hFnonneg hFslab
  exact
    mssFineCubePacketSquareFunction_fourthMoment_of_explicit_uniform_constants
      D cubes N kernelConstant massConstant Cq Ch B R localization hCq hQenergy hCh hHLEbound
      hcardReal hoverlap hscale hwidth hN f hFmeas
      (fun test htest =>
        mssFineCubeContinuumRegularity_of_localization_of_boundedCompactTest
          D cubes N kernelConstant massConstant localization hscale hwidth hN f test htest)
      g htest hlower hsaturates

/-- The same uniform fourth-moment package can use the proved direct lattice
`L⁴` square-function bound, rather than the older averaged-sign hypothesis. -/
private theorem exists_uniform_mssFineCubePacketSquareFunction_fourthMoment_of_analysis_L4_slab
    (D : MSSWavefrontKernelData) (cubes : MSSCubeDecomposition D)
    (N : Nat) (kernelConstant massConstant : Real)
    (localization : MSSFineCubeKernelLocalization D cubes N kernelConstant massConstant)
    (hwidth : 2 < cubes.cubeWidth * Real.sqrt 2) (hN : 3 < N)
    (hslab : D.HasLightRayTimeSlabSupport)
    (hL4 : uniformScaleMSSAnalysisCubeSquareFunctionL4 D cubes) :
    ∃ Cq Ch : Real, ∃ B R : Nat, 0 < Cq ∧ 0 < Ch ∧
      ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
        Integrable (fun z : WaveSpaceTime =>
          (mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2) volume ∧
        (∫⁻ z : WaveSpaceTime,
          ENNReal.ofReal ((mssFineCubePacketSquareFunction D cubes scale f z ^ 2) ^ 2)) ≤
          ENNReal.ofReal
            (((((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile N u) * (R : Real)) *
                Real.sqrt (‖(kernelConstant : Complex)‖ ^ 4 * Cq *
                  ∫ y : Euclidean 2, ‖f y‖ ^ 4) *
              (Ch * (1 + |Real.log ((cubes.cubeWidth * Real.sqrt scale)⁻¹)|) ^
                (3 / 2 : Real))) ^ 2) := by
  obtain ⟨Cq, hCq, hQenergy⟩ :=
    exists_uniform_mssFineNormalizedCubeEnergy_L2_bound_of_analysis_L4
      D cubes kernelConstant hL4
  obtain ⟨Ch, hCh, hHLEbound⟩ :=
    exists_uniform_lightRayMaximal_norm_sq_bound_on_boundedCompactTests N hN
  obtain ⟨B, hcard⟩ := cubes.cubes_per_packet
  obtain ⟨R, hoverlap⟩ := cubes.reverse_overlap
  have hcardReal : ∀ scale : Real, 2 ≤ scale →
      ∀ n ∈ relevantRadialIndexEnumeration scale, ∀ nu ∈ D.angularIndices scale,
        ((cubes.cubeSets scale n nu).card : Real) ≤ B := by
    intro scale hscale n hn nu hnu
    exact_mod_cast hcard scale hscale n hn nu hnu
  refine ⟨Cq, Ch, B, R, hCq, hCh, ?_⟩
  intro scale hscale f
  have hFcont : Continuous (fun z : WaveSpaceTime =>
      mssFineCubePacketSquareFunction D cubes scale f z ^ 2) :=
    continuous_sq_mssFineCubePacketSquareFunction D cubes scale f
  have hFmeas : AEStronglyMeasurable (fun z : WaveSpaceTime =>
      mssFineCubePacketSquareFunction D cubes scale f z ^ 2) volume :=
    hFcont.aestronglyMeasurable
  have hFmeasurable : Measurable (fun z : WaveSpaceTime =>
      mssFineCubePacketSquareFunction D cubes scale f z ^ 2) :=
    hFcont.measurable
  have hFnonneg : ∀ z : WaveSpaceTime,
      0 ≤ mssFineCubePacketSquareFunction D cubes scale f z ^ 2 := by
    intro z
    exact sq_nonneg _
  have hFslab :
      (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) =
        (Set.univ ×ˢ lightRayTimeInterval).indicator
          (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2) :=
    sq_mssFineCubePacketSquareFunction_eq_indicator_lightRayTimeSlab
      D cubes hslab scale f
  obtain ⟨g, htest, hlower, hsaturates⟩ :=
    exists_saturating_lightRayBoundedCompactTests_of_measurable_nonneg_slab
      (fun z : WaveSpaceTime => mssFineCubePacketSquareFunction D cubes scale f z ^ 2)
      hFmeasurable hFnonneg hFslab
  exact
    mssFineCubePacketSquareFunction_fourthMoment_of_explicit_uniform_constants
      D cubes N kernelConstant massConstant Cq Ch B R localization hCq hQenergy hCh hHLEbound
      hcardReal hoverlap hscale hwidth hN f hFmeas
      (fun test htest =>
        mssFineCubeContinuumRegularity_of_localization_of_boundedCompactTest
          D cubes N kernelConstant massConstant localization hscale hwidth hN f test htest)
      g htest hlower hsaturates

/-- A scale-uniform fourth-moment bound for the literal cube-packet square
function is exactly the remaining measure-theoretic input for the structured
MSS fine-square estimate.  This theorem performs only the fourth-root
conversion and the already proved packet-synthesis rewrite; it introduces no
additional analytic assertion. -/
theorem mssFineSquareFunctionEstimate_of_uniform_packet_fourthMoment
    (D : MSSWavefrontKernelData) (A : MSSFineAngularData D.toMSSWavefrontCutoffData)
    (cubes : MSSCubeDecomposition D)
    (_uniform : MSSFineSpatialProfileUniformRegularity D)
    (_hslab : D.HasLightRayTimeSlabSupport)
    (hfourth : ∀ eta : Real, 0 < eta → ∃ C : Real, 0 < C ∧
      ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
        (∫⁻ z : WaveSpaceTime,
          (ENNReal.ofReal ‖mssFineCubePacketSquareFunction D cubes scale f z‖) ^
            (4 : Real)) ≤
          (ENNReal.ofReal (C * scale ^ eta)) ^ (4 : Real) *
            ∫⁻ y : Euclidean 2,
              (ENNReal.ofReal ‖(f : Euclidean 2 → Complex) y‖) ^ (4 : Real)) :
    mssFineSquareFunctionEstimate D A _uniform _hslab := by
  intro eta heta
  obtain ⟨C, hC, hfourth⟩ := hfourth eta heta
  refine ⟨C, hC, ?_⟩
  intro scale hscale f
  have hmoment := hfourth scale hscale f
  rw [Auto.LpSpaceFacts.lintegral_ofReal_norm_rpow_eq_eLpNorm_rpow
        (μ := volume) (q := (4 : Real)) (by norm_num)
        (mssFineCubePacketSquareFunction D cubes scale f),
      Auto.LpSpaceFacts.lintegral_ofReal_norm_rpow_eq_eLpNorm_rpow
        (μ := volume) (q := (4 : Real)) (by norm_num)
        (f : Euclidean 2 → Complex)] at hmoment
  norm_num at hmoment
  have hpacket :
      eLpNorm (mssFineCubePacketSquareFunction D cubes scale f)
          (4 : ENNReal) volume ≤
        ENNReal.ofReal (C * scale ^ eta) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
    rw [← ENNReal.rpow_le_rpow_iff (by norm_num : (0 : Real) < 4)]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : Real) ≤ 4)]
    convert hmoment using 1 <;> norm_num
  simpa only [mssFineCubePacketSquareFunction_eq_mssFineSquareFunction
    D cubes scale hscale f] using hpacket

/-- The canonical fine cubes, their literal kernel localization, the proved
lattice `L⁴` analysis estimate, and the light-ray maximal estimate prove the
structured MSS fine square-function estimate. -/
theorem mssFineSquareFunctionEstimate_of_canonicalData
    (D : MSSWavefrontKernelData)
    (H : MSSFineAngularData D.toMSSWavefrontCutoffData)
    (uniform : MSSFineSpatialProfileUniformRegularity D)
    (hslab : D.HasLightRayTimeSlabSupport) :
    mssFineSquareFunctionEstimate D H uniform hslab := by
  apply mssFineSquareFunctionEstimate_of_uniform_packet_fourthMoment
    D H (mssCanonicalCubeDecomposition D H) uniform hslab
  intro eta heta
  obtain ⟨kernelConstant, massConstant, hkernelConstant, localization⟩ :=
    exists_mssCanonicalFineCubeKernelLocalization D H uniform hslab
  obtain ⟨Cq, Ch, B, R, hCq, hCh, hraw⟩ :=
    exists_uniform_mssFineCubePacketSquareFunction_fourthMoment_of_analysis_L4_slab
      D (mssCanonicalCubeDecomposition D H) 4 kernelConstant massConstant localization
      (mssCanonicalCubeDecomposition_hwidth D H) (by norm_num) hslab
      (mssCanonicalCube_uniformAnalysisL4 D H)
  have hwidthPos : 0 < (mssCanonicalCubeDecomposition D H).cubeWidth := by
    change 0 < (2 : Real)
    norm_num
  obtain ⟨Clog, hClog, hlog⟩ :=
    exists_lightRayWidth_log_three_halves_le_square_scale hwidthPos eta heta
  let A : Real := ((B : Real) * ∫ u : Euclidean 2, lightRayDecayProfile 4 u) * (R : Real)
  let P : Real := ‖(kernelConstant : Complex)‖ ^ (4 : Nat) * Cq
  let K : Real := A * Real.sqrt P * Ch
  let C : Real := (K + 1) * Clog
  have hmass : 0 ≤ ∫ u : Euclidean 2, lightRayDecayProfile 4 u := by
    apply integral_nonneg
    intro u
    unfold lightRayDecayProfile
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg B) hmass) (Nat.cast_nonneg R)
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) hCq.le
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) hCh.le
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by linarith) hClog
  refine ⟨C, hC, ?_⟩
  intro scale hscale f
  obtain ⟨_, hrawbound⟩ := hraw scale hscale f
  let I : Real := ∫ y : Euclidean 2, ‖f y‖ ^ (4 : Nat)
  let L : Real := 1 + |Real.log
    (((mssCanonicalCubeDecomposition D H).cubeWidth * Real.sqrt scale)⁻¹)|
  let X : Real := Clog * scale ^ eta
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun y => pow_nonneg (norm_nonneg (f y)) _
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hscale0 : 0 ≤ scale := by linarith
  have hX : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg hClog.le (Real.rpow_nonneg hscale0 _)
  have hlogbound : L ^ (3 / 2 : Real) ≤ X ^ 2 := by
    simpa only [L, X] using hlog scale hscale
  have hsqrtI : 0 ≤ Real.sqrt I := Real.sqrt_nonneg _
  have hKle : K ≤ K + 1 := by linarith
  have hcoeff : K * Real.sqrt I ≤ (K + 1) * Real.sqrt I :=
    mul_le_mul_of_nonneg_right hKle hsqrtI
  have hbasele : K * Real.sqrt I * L ^ (3 / 2 : Real) ≤
      (K + 1) * Real.sqrt I * X ^ 2 := by
    calc
      K * Real.sqrt I * L ^ (3 / 2 : Real) ≤ K * Real.sqrt I * X ^ 2 :=
        mul_le_mul_of_nonneg_left hlogbound (mul_nonneg hK hsqrtI)
      _ ≤ (K + 1) * Real.sqrt I * X ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg X)
  have hbase0 : 0 ≤ K * Real.sqrt I * L ^ (3 / 2 : Real) :=
    mul_nonneg (mul_nonneg hK hsqrtI) (Real.rpow_nonneg hL _)
  have hright0 : 0 ≤ (K + 1) * Real.sqrt I * X ^ 2 := by positivity
  have hsq : (K * Real.sqrt I * L ^ (3 / 2 : Real)) ^ 2 ≤
      ((K + 1) * Real.sqrt I * X ^ 2) ^ 2 :=
    (sq_le_sq₀ hbase0 hright0).mpr hbasele
  have hKsq0 : 0 ≤ (K + 1) ^ 2 := sq_nonneg _
  have hKsqOne : 1 ≤ (K + 1) ^ 2 := by
    nlinarith [sq_nonneg K]
  have hKpow : (K + 1) ^ 2 ≤ (K + 1) ^ 4 := by
    calc
      (K + 1) ^ 2 = (K + 1) ^ 2 * 1 := by ring
      _ ≤ (K + 1) ^ 2 * (K + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hKsqOne hKsq0
      _ = (K + 1) ^ 4 := by ring
  have hrest : 0 ≤ X ^ 4 * I :=
    mul_nonneg (pow_nonneg hX _) hI
  have hrightSq : ((K + 1) * Real.sqrt I * X ^ 2) ^ 2 ≤
      ((K + 1) * X) ^ 4 * I := by
    calc
      ((K + 1) * Real.sqrt I * X ^ 2) ^ 2 =
          (K + 1) ^ 2 * (Real.sqrt I) ^ 2 * X ^ 4 := by ring
      _ = (K + 1) ^ 2 * X ^ 4 * I := by
        rw [Real.sq_sqrt hI]
        ring
      _ ≤ (K + 1) ^ 4 * X ^ 4 * I := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_right hKpow hrest)
      _ = ((K + 1) * X) ^ 4 * I := by ring
  have hbaseeq :
      A * Real.sqrt (P * I) * (Ch * L ^ (3 / 2 : Real)) =
        K * Real.sqrt I * L ^ (3 / 2 : Real) := by
    rw [Real.sqrt_mul hP I]
    dsimp [K]
    ring
  have hCX : C * scale ^ eta = (K + 1) * X := by
    dsimp [C, X]
    ring
  have hrealNat :
      (A * Real.sqrt (P * I) * (Ch * L ^ (3 / 2 : Real))) ^ 2 ≤
        (C * scale ^ eta) ^ (4 : Nat) * I := by
    calc
      (A * Real.sqrt (P * I) * (Ch * L ^ (3 / 2 : Real))) ^ 2 =
          (K * Real.sqrt I * L ^ (3 / 2 : Real)) ^ 2 := by rw [hbaseeq]
      _ ≤ ((K + 1) * Real.sqrt I * X ^ 2) ^ 2 := hsq
      _ ≤ ((K + 1) * X) ^ 4 * I := hrightSq
      _ = (C * scale ^ eta) ^ (4 : Nat) * I := by rw [hCX]
  have hreal :
      (A * Real.sqrt (P * I) * (Ch * L ^ (3 / 2 : Real))) ^ 2 ≤
        (C * scale ^ eta) ^ (4 : Real) * I := by
    have hfour : (4 : Real) = ((4 : Nat) : Real) := by norm_num
    rw [hfour, Real.rpow_natCast]
    exact hrealNat
  have hrawbound' :
      (∫⁻ z : WaveSpaceTime,
        ENNReal.ofReal
          ((mssFineCubePacketSquareFunction D (mssCanonicalCubeDecomposition D H)
            scale f z ^ 2) ^ 2)) ≤
        ENNReal.ofReal
          ((A * Real.sqrt (P * I) * (Ch * L ^ (3 / 2 : Real))) ^ 2) := by
    simpa only [A, P, I, L] using hrawbound
  have hpacketNonneg : ∀ z : WaveSpaceTime,
      0 ≤ mssFineCubePacketSquareFunction D (mssCanonicalCubeDecomposition D H)
        scale f z := by
    intro z
    unfold mssFineCubePacketSquareFunction
    exact Real.sqrt_nonneg _
  have hrawLhs :
      (∫⁻ z : WaveSpaceTime,
        ENNReal.ofReal
          ((mssFineCubePacketSquareFunction D (mssCanonicalCubeDecomposition D H)
            scale f z ^ 2) ^ 2)) =
        ∫⁻ z : WaveSpaceTime,
          (ENNReal.ofReal
            ‖mssFineCubePacketSquareFunction D (mssCanonicalCubeDecomposition D H)
              scale f z‖) ^ (4 : Real) := by
    apply lintegral_congr
    intro z
    rw [show
      (mssFineCubePacketSquareFunction D (mssCanonicalCubeDecomposition D H)
        scale f z ^ 2) ^ 2 =
        mssFineCubePacketSquareFunction D (mssCanonicalCubeDecomposition D H)
          scale f z ^ (4 : Nat) by ring]
    rw [Real.norm_of_nonneg (hpacketNonneg z), ← Real.rpow_natCast]
    exact (ENNReal.ofReal_rpow_of_nonneg (hpacketNonneg z)
      (by norm_num : (0 : Real) ≤ 4)).symm
  have hfint : Integrable (fun y : Euclidean 2 => ‖f y‖ ^ (4 : Nat)) volume :=
    (f.memLp 4 volume).integrable_norm_pow (by norm_num)
  have hfnonneg : ∀ᵐ y : Euclidean 2 ∂volume, 0 ≤ ‖f y‖ ^ (4 : Nat) :=
    Filter.Eventually.of_forall fun _ => pow_nonneg (norm_nonneg _) _
  have hinputNat : ENNReal.ofReal I =
      ∫⁻ y : Euclidean 2, ENNReal.ofReal (‖f y‖ ^ (4 : Nat)) := by
    dsimp [I]
    exact ofReal_integral_eq_lintegral_ofReal hfint hfnonneg
  have hinput : ENNReal.ofReal I =
      ∫⁻ y : Euclidean 2, (ENNReal.ofReal ‖(f : Euclidean 2 → Complex) y‖) ^
        (4 : Real) := by
    calc
      ENNReal.ofReal I =
          ∫⁻ y : Euclidean 2, ENNReal.ofReal (‖f y‖ ^ (4 : Nat)) := hinputNat
      _ = ∫⁻ y : Euclidean 2,
          (ENNReal.ofReal ‖(f : Euclidean 2 → Complex) y‖) ^ (4 : Real) := by
        apply lintegral_congr
        intro y
        rw [← Real.rpow_natCast]
        exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
          (by norm_num : (0 : Real) ≤ 4)).symm
  have hCscale : 0 ≤ C * scale ^ eta :=
    mul_nonneg hC.le (Real.rpow_nonneg hscale0 _)
  have hRhs :
      (ENNReal.ofReal (C * scale ^ eta)) ^ (4 : Real) *
          ∫⁻ y : Euclidean 2,
            (ENNReal.ofReal ‖(f : Euclidean 2 → Complex) y‖) ^ (4 : Real) =
        ENNReal.ofReal ((C * scale ^ eta) ^ (4 : Real) * I) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hCscale (by norm_num : (0 : Real) ≤ 4),
      ← hinput, ← ENNReal.ofReal_mul (Real.rpow_nonneg hCscale _)]
  calc
    (∫⁻ z : WaveSpaceTime,
      (ENNReal.ofReal
        ‖mssFineCubePacketSquareFunction D (mssCanonicalCubeDecomposition D H)
          scale f z‖) ^ (4 : Real)) =
        ∫⁻ z : WaveSpaceTime,
          ENNReal.ofReal
            ((mssFineCubePacketSquareFunction D (mssCanonicalCubeDecomposition D H)
              scale f z ^ 2) ^ 2) := hrawLhs.symm
    _ ≤ ENNReal.ofReal
        ((A * Real.sqrt (P * I) * (Ch * L ^ (3 / 2 : Real))) ^ 2) := hrawbound'
    _ ≤ ENNReal.ofReal ((C * scale ^ eta) ^ (4 : Real) * I) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (ENNReal.ofReal (C * scale ^ eta)) ^ (4 : Real) *
        ∫⁻ y : Euclidean 2,
          (ENNReal.ofReal ‖(f : Euclidean 2 → Complex) y‖) ^ (4 : Real) := hRhs.symm

/-! ### Exact joint-Schwartz packet realizations for recombination -/

/-- The spatial Schwartz factor of one literal MSS angular--radial packet.
It is the actual scale-indexed packet profile multiplied by the Fourier
transform of the Schwartz input. -/
private noncomputable def mssRecombinationInputSpatialProfile
    (D : MSSWavefrontKernelData) (scale : Real) (n nu : Int)
    (f : SchwartzMap (Euclidean 2) Complex) :
    SchwartzMap (Euclidean 2) Complex :=
  SchwartzMap.smulLeftCLM Complex
    (D.spatialProfile scale n nu : Euclidean 2 → Complex)
    (FourierTransform.fourier f)

private theorem mssRecombinationInputSpatialProfile_apply
    (D : MSSWavefrontKernelData) (scale : Real) (n nu : Int)
    (f : SchwartzMap (Euclidean 2) Complex) (xi : Euclidean 2) :
    mssRecombinationInputSpatialProfile D scale n nu f xi =
      D.spatialProfile scale n nu xi *
        FourierTransform.fourier (f : Euclidean 2 → Complex) xi := by
  unfold mssRecombinationInputSpatialProfile
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (D.spatialProfile scale n nu).hasTemperateGrowth]
  rw [smul_eq_mul]
  rw [← SchwartzMap.fourier_coe]

/-- The exact affine vertical-frequency factor of one MSS packet, kept as a
Schwartz map so that the vertical recombination theorem applies to the
literal packets. -/
private noncomputable def mssRecombinationVerticalProfile
    (D : MSSWavefrontKernelData) (scale : Real) (n : Int)
    (hscale : 0 < scale) : SchwartzMap Real Complex :=
  let root : Real := Real.sqrt scale
  let A : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 root⁻¹ (by
        dsimp only [root]
        exact inv_ne_zero (Real.sqrt_ne_zero'.mpr hscale)))
  ((SchwartzMap.compCLMOfContinuousLinearEquiv Complex A) D.radialTime.vertical).compSubConstCLM
    Complex (root * n)

private theorem mssRecombinationVerticalProfile_apply
    (D : MSSWavefrontKernelData) (scale : Real) (n : Int)
    (hscale : 0 < scale) (tau : Real) :
    mssRecombinationVerticalProfile D scale n hscale tau =
      D.radialTime.vertical ((Real.sqrt scale)⁻¹ * tau - n) := by
  unfold mssRecombinationVerticalProfile
  dsimp
  change D.radialTime.vertical
      ((Real.sqrt scale)⁻¹ * (tau - Real.sqrt scale * n)) = _
  have hroot : Real.sqrt scale ≠ 0 := Real.sqrt_ne_zero'.mpr hscale
  field_simp [hroot]

private def mssRecombinationJointVerticalFactor
    (m : SchwartzMap Real Complex) : JointWaveSpaceTime → Complex :=
  fun z => m z.snd

private theorem mssRecombinationJointVerticalFactor_hasTemperateGrowth
    (m : SchwartzMap Real Complex) :
    (mssRecombinationJointVerticalFactor m).HasTemperateGrowth := by
  change (m ∘ WithLp.sndL 2 Real (Euclidean 2) Real).HasTemperateGrowth
  exact m.hasTemperateGrowth.comp
    (WithLp.sndL 2 Real (Euclidean 2) Real).hasTemperateGrowth

private noncomputable def mssRecombinationApplyVerticalSpectrum
    (m : SchwartzMap Real Complex)
    (Q : SchwartzMap JointWaveSpaceTime Complex) :
    SchwartzMap JointWaveSpaceTime Complex :=
  SchwartzMap.smulLeftCLM Complex (mssRecombinationJointVerticalFactor m) Q

private theorem mssRecombinationApplyVerticalSpectrum_apply
    (m : SchwartzMap Real Complex)
    (Q : SchwartzMap JointWaveSpaceTime Complex) (zeta : WaveSpaceTime) :
    mssRecombinationApplyVerticalSpectrum m Q (WithLp.toLp 2 zeta) =
      m zeta.2 * Q (WithLp.toLp 2 zeta) := by
  unfold mssRecombinationApplyVerticalSpectrum
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (mssRecombinationJointVerticalFactor_hasTemperateGrowth m)]
  rfl

private noncomputable def mssRecombinationBaseSpectrum
    (D : MSSWavefrontKernelData) (scale : Real) (n nu : Int)
    (f : SchwartzMap (Euclidean 2) Complex) :
    SchwartzMap JointWaveSpaceTime Complex :=
  jointSchwartzModulatedAnnularProfile
    (mssRecombinationInputSpatialProfile D scale n nu f)
    D.radialTime.time (D.normalCoordinate scale)

private noncomputable def mssRecombinationSourceSpectrum
    (D : MSSWavefrontKernelData) (scale : Real) (n nu : Int)
    (f : SchwartzMap (Euclidean 2) Complex) (hscale : 0 < scale) :
    SchwartzMap JointWaveSpaceTime Complex :=
  mssRecombinationApplyVerticalSpectrum
    (mssRecombinationVerticalProfile D scale n hscale)
    (mssRecombinationBaseSpectrum D scale n nu f)

private noncomputable def mssRecombinationSourcePacket
    (D : MSSWavefrontKernelData) (scale : Real) (n nu : Int)
    (f : SchwartzMap (Euclidean 2) Complex) (hscale : 0 < scale) :
    SchwartzMap JointWaveSpaceTime Complex :=
  FourierTransform.fourierInv
    (mssRecombinationSourceSpectrum D scale n nu f hscale)

private theorem mssRecombination_normalCoordinate_eq_norm_on_input_support
    (D : MSSWavefrontKernelData) {scale : Real} (hscale : 0 < scale)
    (n nu : Int) (f : SchwartzMap (Euclidean 2) Complex) {xi : Euclidean 2}
    (hxi : mssRecombinationInputSpatialProfile D scale n nu f xi ≠ 0) :
    D.normalCoordinate scale xi = ‖xi‖ := by
  rw [mssRecombinationInputSpatialProfile_apply] at hxi
  have hspatial : D.spatialProfile scale n nu xi ≠ 0 :=
    (mul_ne_zero_iff.mp hxi).1
  rw [D.spatialProfile_apply] at hspatial
  rcases mul_ne_zero_iff.mp hspatial with ⟨_, hspatial⟩
  rcases mul_ne_zero_iff.mp hspatial with ⟨hamp, _⟩
  rw [D.normalCoordinate_apply,
    D.radialTime.normalExtension_eq_norm_on_amplitude
      (scale⁻¹ • xi) hamp,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
  field_simp [hscale.ne']

private theorem mssRecombinationBasePacket_eq_angularPiece
    (D : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization D)
    (scale : Real) (n nu : Int) (f : SchwartzMap (Euclidean 2) Complex)
    (hscale : 0 < scale) :
    jointSchwartzRaw
        (FourierTransform.fourierInv (mssRecombinationBaseSpectrum D scale n nu f)) =
      angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
        (D.chi scale nu) (D.radialTime.time : Real → Complex)
        (radialPiece (D.radialTime.radial : Real → Complex) scale n
          (f : Euclidean 2 → Complex)) := by
  funext z
  calc
    jointSchwartzRaw
        (FourierTransform.fourierInv (mssRecombinationBaseSpectrum D scale n nu f)) z =
        spaceTimeFourierInv
          (jointSchwartzRaw (mssRecombinationBaseSpectrum D scale n nu f)) z := by
          simpa only [jointSchwartzRaw, SchwartzMap.fourierInv_coe] using
            (spaceTimeFourierInv_jointSchwartzRaw
              (mssRecombinationBaseSpectrum D scale n nu f) z).symm
    _ = (fun z : WaveSpaceTime =>
        D.radialTime.time z.2 * FourierTransform.fourierInv (fun xi : Euclidean 2 =>
          mssRecombinationInputSpatialProfile D scale n nu f xi *
            halfWaveMultiplier WaveSign.plus z.2 xi) z.1) z := by
          unfold mssRecombinationBaseSpectrum
          exact spaceTimeFourierInv_jointSchwartzModulatedAnnularProfile_eq_halfWave_of_eq_norm_on_support
            (mssRecombinationInputSpatialProfile D scale n nu f)
            D.radialTime.time (D.normalCoordinate scale)
            (fun xi hxi =>
              mssRecombination_normalCoordinate_eq_norm_on_input_support
                D hscale n nu f hxi) z
    _ = angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
        (D.chi scale nu) (D.radialTime.time : Real → Complex)
        (radialPiece (D.radialTime.radial : Real → Complex) scale n
          (f : Euclidean 2 → Complex)) z := by
          exact congrFun
            (temporalSchwartzHalfWave_eq_angularPiece_of_schwartzRadialProfile
              (mssRecombinationInputSpatialProfile D scale n nu f)
              (R.radialProfile scale n) f D.radialTime.time scale
              (D.radialTime.amplitude : Euclidean 2 → Complex) (D.chi scale nu)
              (D.radialTime.radial : Real → Complex) n
              (R.radialProfile_apply scale n hscale)
              (by
                intro xi
                rw [mssRecombinationInputSpatialProfile_apply,
                  D.spatialProfile_apply, R.radialProfile_apply scale n hscale]
                ring)) z

private theorem mssRecombination_verticalProjection_eq_sourcePacket
    (D : MSSWavefrontKernelData) (scale : Real) (n : Int)
    (hscale : 0 < scale) (Q : SchwartzMap JointWaveSpaceTime Complex) :
    verticalProjection (D.radialTime.vertical : Real → Complex) scale n
        (jointSchwartzRaw (FourierTransform.fourierInv Q)) =
      jointSchwartzRaw (FourierTransform.fourierInv
        (mssRecombinationApplyVerticalSpectrum
          (mssRecombinationVerticalProfile D scale n hscale) Q)) := by
  let m : SchwartzMap Real Complex :=
    mssRecombinationVerticalProfile D scale n hscale
  let P : SchwartzMap JointWaveSpaceTime Complex :=
    mssRecombinationApplyVerticalSpectrum m Q
  have hmult :
      (fun zeta : WaveSpaceTime =>
        verticalMultiplier (D.radialTime.vertical : Real → Complex) scale n zeta *
          spaceTimeFourier (jointSchwartzRaw (FourierTransform.fourierInv Q)) zeta) =
        jointSchwartzRaw P := by
    funext zeta
    rw [spaceTimeFourier_jointSchwartzRaw]
    change verticalMultiplier (D.radialTime.vertical : Real → Complex) scale n zeta *
        FourierTransform.fourier
          (FourierTransform.fourierInv Q : JointWaveSpaceTime → Complex)
          (WithLp.toLp 2 zeta) = P (WithLp.toLp 2 zeta)
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
    dsimp only [P, m]
    rw [mssRecombinationApplyVerticalSpectrum_apply,
      mssRecombinationVerticalProfile_apply]
    rfl
  unfold verticalProjection
  rw [hmult]
  funext z
  simpa only [P, jointSchwartzRaw, SchwartzMap.fourierInv_coe] using
    (spaceTimeFourierInv_jointSchwartzRaw P z)

/-- A literal angular--radial packet has an exact joint-Schwartz
representative.  This is a raw Fourier identity, not a localization or norm
estimate. -/
private theorem mssAngularRadialWave_eq_mssRecombinationSourcePacket
    (D : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization D)
    (scale : Real) (hscale : 0 < scale) (n nu : Int)
    (f : SchwartzMap (Euclidean 2) Complex) :
    mssAngularRadialWave D.toMSSWavefrontCutoffData scale n nu
        (f : Euclidean 2 → Complex) =
      jointSchwartzRaw (mssRecombinationSourcePacket D scale n nu f hscale) := by
  unfold mssAngularRadialWave angularRadialWave mssRecombinationSourcePacket
    mssRecombinationSourceSpectrum
  rw [← mssRecombinationBasePacket_eq_angularPiece D R scale n nu f hscale]
  exact mssRecombination_verticalProjection_eq_sourcePacket
    D scale n hscale (mssRecombinationBaseSpectrum D scale n nu f)

private noncomputable def mssRecombinationNormalProfile
    (normal : SchwartzMap Real Complex) (scale gamma : Real)
    (hscale : 0 < scale) : SchwartzMap Real Complex :=
  let A : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 (scale ^ (-gamma))
        (ne_of_gt (Real.rpow_pos_of_pos hscale _)))
  (SchwartzMap.compCLMOfContinuousLinearEquiv Complex A) normal

private theorem mssRecombinationNormalProfile_apply
    (normal : SchwartzMap Real Complex) (scale gamma : Real)
    (hscale : 0 < scale) (s : Real) :
    mssRecombinationNormalProfile normal scale gamma hscale s =
      normal (scale ^ (-gamma) * s) := by
  unfold mssRecombinationNormalProfile
  dsimp
  rfl

private noncomputable def mssRecombinationWavefrontCutoff
    (D : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization D)
    (scale gamma : Real) (nu : Int) (hscale : 0 < scale) :
    SchwartzMap JointWaveSpaceTime Complex :=
  jointSchwartzSpatialNormalCutoff (R.wavefrontAngularProfile scale nu)
    (mssRecombinationNormalProfile D.normal scale gamma hscale)
    (D.normalCoordinate scale)

private noncomputable def mssRecombinationWavefrontSpectrum
    (D : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization D)
    (scale gamma : Real) (n nu : Int) (f : SchwartzMap (Euclidean 2) Complex)
    (hscale : 0 < scale) : SchwartzMap JointWaveSpaceTime Complex :=
  jointSchwartzSpectralCutoffProduct
    (mssRecombinationWavefrontCutoff D R scale gamma nu hscale)
    (mssRecombinationSourcePacket D scale n nu f hscale)

private theorem mssRecombinationSourceSpectrum_apply
    (D : MSSWavefrontKernelData) (scale : Real) (n nu : Int)
    (f : SchwartzMap (Euclidean 2) Complex) (hscale : 0 < scale)
    (zeta : WaveSpaceTime) :
    mssRecombinationSourceSpectrum D scale n nu f hscale (WithLp.toLp 2 zeta) =
      D.radialTime.vertical ((Real.sqrt scale)⁻¹ * zeta.2 - n) *
        (mssRecombinationInputSpatialProfile D scale n nu f zeta.1 *
          FourierTransform.fourier (D.radialTime.time : Real → Complex)
            (zeta.2 - D.normalCoordinate scale zeta.1)) := by
  unfold mssRecombinationSourceSpectrum mssRecombinationBaseSpectrum
  rw [mssRecombinationApplyVerticalSpectrum_apply,
    mssRecombinationVerticalProfile_apply,
    jointSchwartzModulatedAnnularProfile_apply]

private theorem mssRecombinationSourcePacket_fourier
    (D : MSSWavefrontKernelData) (scale : Real) (n nu : Int)
    (f : SchwartzMap (Euclidean 2) Complex) (hscale : 0 < scale)
    (zeta : WaveSpaceTime) :
    FourierTransform.fourier
        (mssRecombinationSourcePacket D scale n nu f hscale :
          JointWaveSpaceTime → Complex) (WithLp.toLp 2 zeta) =
      mssRecombinationSourceSpectrum D scale n nu f hscale (WithLp.toLp 2 zeta) := by
  unfold mssRecombinationSourcePacket
  rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]

private theorem mssRecombinationWavefrontCutoff_realizes_multiplier
    (D : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization D)
    (scale gamma : Real) (n nu : Int) (f : SchwartzMap (Euclidean 2) Complex)
    (hscale : 0 < scale) (zeta : WaveSpaceTime) :
    wavefrontMultiplier (D.tildeChi scale nu) (D.normal : Real → Complex) scale gamma zeta *
        FourierTransform.fourier
          (mssRecombinationSourcePacket D scale n nu f hscale :
            JointWaveSpaceTime → Complex) (WithLp.toLp 2 zeta) =
      mssRecombinationWavefrontCutoff D R scale gamma nu hscale (WithLp.toLp 2 zeta) *
        FourierTransform.fourier
          (mssRecombinationSourcePacket D scale n nu f hscale :
            JointWaveSpaceTime → Complex) (WithLp.toLp 2 zeta) := by
  by_cases hsource : FourierTransform.fourier
      (mssRecombinationSourcePacket D scale n nu f hscale :
        JointWaveSpaceTime → Complex) (WithLp.toLp 2 zeta) = 0
  · simp [hsource]
  · have hsourceSpectrum :
        mssRecombinationSourceSpectrum D scale n nu f hscale
          (WithLp.toLp 2 zeta) ≠ 0 := by
        rwa [← mssRecombinationSourcePacket_fourier D scale n nu f hscale zeta]
    rw [mssRecombinationSourceSpectrum_apply] at hsourceSpectrum
    have hinput : mssRecombinationInputSpatialProfile D scale n nu f zeta.1 ≠ 0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hsourceSpectrum).2).1
    rw [mssRecombinationInputSpatialProfile_apply] at hinput
    have hspatial : D.spatialProfile scale n nu zeta.1 ≠ 0 :=
      (mul_ne_zero_iff.mp hinput).1
    rw [wavefrontMultiplier]
    unfold mssRecombinationWavefrontCutoff
    rw [jointSchwartzSpatialNormalCutoff_apply,
      mssRecombinationNormalProfile_apply,
      R.wavefrontAngularProfile_eq_on_spatial scale n nu zeta.1 hspatial,
      mssRecombination_normalCoordinate_eq_norm_on_input_support
        D hscale n nu f (by
          rw [mssRecombinationInputSpatialProfile_apply]
          exact hinput)]

/-- The literal wave-front projection of an MSS packet is the inverse joint
Fourier transform of a concrete Schwartz spectrum.  The construction exposes
the exact object consumed by the spectral plate-overlap theorem. -/
private theorem mssWavefrontAngularRadialWave_eq_mssRecombinationWavefrontSpectrum
    (D : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization D)
    (scale gamma : Real) (hscale : 0 < scale) (n nu : Int)
    (f : SchwartzMap (Euclidean 2) Complex) :
    mssWavefrontAngularRadialWave D.toMSSWavefrontCutoffData scale gamma n nu
        (f : Euclidean 2 → Complex) =
      jointSchwartzRaw (FourierTransform.fourierInv
        (mssRecombinationWavefrontSpectrum D R scale gamma n nu f hscale)) := by
  unfold mssWavefrontAngularRadialWave
  rw [mssAngularRadialWave_eq_mssRecombinationSourcePacket D R scale hscale n nu f]
  exact wavefrontProjection_eq_jointSchwartzSpectralCutoffOutput_of_realization
    (D.tildeChi scale nu) (D.normal : Real → Complex) scale gamma
    (mssRecombinationWavefrontCutoff D R scale gamma nu hscale)
    (mssRecombinationSourcePacket D scale n nu f hscale)
    (mssRecombinationWavefrontCutoff_realizes_multiplier
      D R scale gamma n nu f hscale)

private theorem mssRecombination_integrable_angularPiece_multiplier
    (D : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization D)
    (scale : Real) (hscale : 0 < scale) (n nu : Int) (f : SchwartzMap (Euclidean 2) Complex)
    (t : Real) :
    Integrable (fun xi : Euclidean 2 =>
      D.chi scale nu xi * D.radialTime.amplitude (scale⁻¹ • xi) *
        halfWaveMultiplier WaveSign.plus t xi *
          FourierTransform.fourier
            (radialPiece (D.radialTime.radial : Real → Complex) scale n
              (f : Euclidean 2 → Complex)) xi) volume := by
  rw [show (fun xi : Euclidean 2 =>
      D.chi scale nu xi * D.radialTime.amplitude (scale⁻¹ • xi) *
        halfWaveMultiplier WaveSign.plus t xi *
          FourierTransform.fourier
            (radialPiece (D.radialTime.radial : Real → Complex) scale n
              (f : Euclidean 2 → Complex)) xi) =
      fun xi => mssRecombinationInputSpatialProfile D scale n nu f xi *
        halfWaveMultiplier WaveSign.plus t xi by
      funext xi
      rw [fourier_radialPiece_eq_schwartzProfile_mul_fourier
        (D.radialTime.radial : Real → Complex) scale n
        (R.radialProfile scale n) f (R.radialProfile_apply scale n hscale) xi,
        mssRecombinationInputSpatialProfile_apply, D.spatialProfile_apply,
        R.radialProfile_apply scale n hscale]
      ring]
  refine Integrable.mono'
    (mssRecombinationInputSpatialProfile D scale n nu f).integrable.norm ?_ ?_
  · have hhalf : Continuous (halfWaveMultiplier WaveSign.plus t) := by
      unfold halfWaveMultiplier
      fun_prop
    exact
      ((mssRecombinationInputSpatialProfile D scale n nu f).continuous.mul hhalf).aestronglyMeasurable
  · filter_upwards with xi
    rw [norm_mul, norm_halfWaveMultiplier, mul_one]

private theorem mssRecombination_aestronglyMeasurable_jointSchwartzRaw
    (P : SchwartzMap JointWaveSpaceTime Complex) :
    AEStronglyMeasurable (jointSchwartzRaw P) volume := by
  have htoLp : Continuous (WithLp.toLp 2 : WaveSpaceTime → JointWaveSpaceTime) :=
    WithLp.prod_continuous_toLp 2 _ _
  change AEStronglyMeasurable (fun z : WaveSpaceTime => P (WithLp.toLp 2 z)) volume
  exact (P.continuous.comp htoLp).aestronglyMeasurable

/-- A joint Schwartz spectrum remains measurable after the literal inverse
space--time Fourier transform.  This is the measurability bridge needed when
the exact radial residual is added back to the recombined reconstruction. -/
private theorem mssRecombination_aestronglyMeasurable_spaceTimeFourierInv_jointSchwartzRaw
    (P : SchwartzMap JointWaveSpaceTime Complex) :
    AEStronglyMeasurable (spaceTimeFourierInv (jointSchwartzRaw P)) volume := by
  have hraw :
      spaceTimeFourierInv (jointSchwartzRaw P) =
        jointSchwartzRaw (FourierTransform.fourierInv P) := by
    funext z
    rw [spaceTimeFourierInv_jointSchwartzRaw]
    change FourierTransform.fourierInv (P : JointWaveSpaceTime → Complex)
        (WithLp.toLp 2 z) =
      (FourierTransform.fourierInv P : SchwartzMap JointWaveSpaceTime Complex)
        (WithLp.toLp 2 z)
    exact (congrFun (SchwartzMap.fourierInv_coe P) (WithLp.toLp 2 z)).symm
  rw [hraw]
  exact mssRecombination_aestronglyMeasurable_jointSchwartzRaw _

private theorem mssRecombination_aestronglyMeasurable_radialTimeResidual
    (D : MSSRadialTimeCutoffs) (scale : Real) (hscale : 0 < scale)
    (f : SchwartzMap (Euclidean 2) Complex) :
    AEStronglyMeasurable
      (radialTimeResidual (D.vertical : Real → Complex) (D.radial : Real → Complex)
        relevantRadialIndexEnumeration scale (D.amplitude : Euclidean 2 → Complex)
        (D.time : Real → Complex) (f : Euclidean 2 → Complex)) volume := by
  rw [radialTimeResidual_eq_inverse_mssRadialTimeResidualSpectrum
    D relevantRadialIndexEnumeration scale hscale f]
  exact mssRecombination_aestronglyMeasurable_spaceTimeFourierInv_jointSchwartzRaw _

private theorem mssRecombinationWavefrontSpectrum_support
    (D : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization D)
    (hregularity : MSSWavefrontSpatialProfilePolynomialRegularity D)
    (scale gamma : Real) (hgamma : D.gamma = gamma) (hscale : 2 ≤ scale)
    (n nu : Int) (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ D.angularIndices scale) (f : SchwartzMap (Euclidean 2) Complex) :
    Function.support
        (jointSchwartzRaw
          (mssRecombinationWavefrontSpectrum D R scale gamma n nu f (by linarith))) ⊆
      conicPlate scale gamma D.angularConstant n (D.directions scale nu) := by
  have hplate :=
    (wavefrontLocalization_of_MSSWavefrontKernelData D R hregularity).2
      scale hscale n nu hn hnu f
  rw [hgamma] at hplate
  intro zeta hzeta
  apply hplate
  rw [mssWavefrontAngularRadialWave_eq_mssRecombinationWavefrontSpectrum
    D R scale gamma (by linarith) n nu f]
  change spaceTimeFourier
      (jointSchwartzRaw
        (FourierTransform.fourierInv
          (mssRecombinationWavefrontSpectrum D R scale gamma n nu f (by linarith)))) zeta ≠ 0
  rw [spaceTimeFourier_jointSchwartzRaw]
  change FourierTransform.fourier
      (FourierTransform.fourierInv
        (mssRecombinationWavefrontSpectrum D R scale gamma n nu f (by linarith)) :
          JointWaveSpaceTime → Complex) (WithLp.toLp 2 zeta) ≠ 0
  rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  exact hzeta

/-- The normal thickness used by the overlap proposition is selected after
the requested subpower loss.  This family keeps all radial and angular cutoff
data fixed while supplying the corresponding wave-front realization at every
admissible thickness. -/
abbrev MSSAdmissibleGamma := {gamma : Real // 0 < gamma ∧ gamma < 1 / 10}

structure MSSWavefrontGammaFamily (core : MSSWavefrontCutoffData) where
  data : MSSAdmissibleGamma → MSSWavefrontKernelData
  data_core : ∀ gamma, (data gamma).toMSSWavefrontCutoffData = core
  data_gamma : ∀ gamma, (data gamma).gamma = gamma.1
  realization : ∀ gamma, MSSWavefrontRawProfileRealization (data gamma)
  regularity : ∀ gamma,
    MSSWavefrontSpatialProfilePolynomialRegularity (data gamma)

/-- The structural data needed to run the recombination argument for a fixed
MSS cutoff core.  It contains no norm estimate: the family only supplies the
gamma-indexed packet realizations required by wave-front localization. -/
structure MSSStructuredRecombinationData (D : MSSWavefrontKernelData) where
  wavefrontFamily : MSSWavefrontGammaFamily D.toMSSWavefrontCutoffData

/-- The repaired, blueprint-faithful MSS recombination target.  Unlike the
legacy free-family predicate, every radial and angular packet is tied to the
fixed cutoff core, while the gamma-family supplies the wave-front
localization at the thickness selected by the overlap estimate. -/
def mssRecombination (D : MSSWavefrontKernelData)
    (_A : MSSFineAngularData D.toMSSWavefrontCutoffData)
    (_structured : MSSStructuredRecombinationData D)
    (_uniform : MSSFineSpatialProfileUniformRegularity D)
    (_hslab : D.HasLightRayTimeSlabSupport) : Prop :=
  ∀ eta : Real, 0 < eta → ∀ N : Nat, ∃ C : Real, 0 < C ∧
    ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
      eLpNorm
          (conicOperator scale (D.radialTime.amplitude : Euclidean 2 → Complex)
            (D.radialTime.time : Real → Complex) (f : Euclidean 2 → Complex))
          (4 : ENNReal) volume ≤
        ENNReal.ofReal (C * scale ^ ((1 / 8 : Real) + eta)) *
          eLpNorm
            (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
              (f : Euclidean 2 → Complex)) (4 : ENNReal) volume +
          ENNReal.ofReal (C * (scale⁻¹) ^ N) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume

private theorem mssRecombination_norm_le_angularRadialSquareFunction
    (radialIndices angularIndices : Finset Int)
    (H : Int → Int → WaveSpaceTime → Complex)
    {n nu : Int} (hn : n ∈ radialIndices) (hnu : nu ∈ angularIndices)
    (z : WaveSpaceTime) :
    ‖H n nu z‖ ≤ angularRadialSquareFunction radialIndices angularIndices H z := by
  unfold angularRadialSquareFunction
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).2
  calc
    ‖H n nu z‖ ^ 2 ≤ ∑ mu ∈ angularIndices, ‖H n mu z‖ ^ 2 :=
      Finset.single_le_sum (fun mu hmu => sq_nonneg (‖H n mu z‖)) hnu
    _ ≤ ∑ m ∈ radialIndices, ∑ mu ∈ angularIndices, ‖H m mu z‖ ^ 2 :=
      Finset.single_le_sum
        (fun m hm => Finset.sum_nonneg fun mu hmu => sq_nonneg (‖H m mu z‖)) hn

private theorem mssRecombination_eLpNorm_component_le_angularRadialSquareFunction
    (radialIndices angularIndices : Finset Int)
    (H : Int → Int → WaveSpaceTime → Complex)
    {n nu : Int} (hn : n ∈ radialIndices) (hnu : nu ∈ angularIndices) :
    eLpNorm (H n nu) (4 : ENNReal) volume ≤
      eLpNorm (angularRadialSquareFunction radialIndices angularIndices H)
        (4 : ENNReal) volume := by
  apply eLpNorm_mono
  intro z
  rw [Real.norm_eq_abs]
  have hnonneg : 0 ≤ angularRadialSquareFunction radialIndices angularIndices H z := by
    unfold angularRadialSquareFunction
    exact Real.sqrt_nonneg _
  rw [abs_of_nonneg hnonneg]
  exact mssRecombination_norm_le_angularRadialSquareFunction
    radialIndices angularIndices H hn hnu z

private theorem mssRecombination_aestronglyMeasurable_angularRadialSquareFunction
    (radialIndices angularIndices : Finset Int)
    (H : Int → Int → WaveSpaceTime → Complex)
    (hH : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices,
      AEStronglyMeasurable (H n nu) volume) :
    AEStronglyMeasurable
      (angularRadialSquareFunction radialIndices angularIndices H) volume := by
  unfold angularRadialSquareFunction
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  apply Finset.aestronglyMeasurable_fun_sum radialIndices
  intro n hn
  apply Finset.aestronglyMeasurable_fun_sum angularIndices
  intro nu hnu
  exact (hH n hn nu hnu).norm.pow 2

private theorem mssRecombination_aestronglyMeasurable_auxAngularRadialRecombined
    (radialIndices angularIndices : Finset Int)
    (H : Int → Int → WaveSpaceTime → Complex)
    (hH : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices,
      AEStronglyMeasurable (H n nu) volume) :
    AEStronglyMeasurable
      (aux_angularRadialRecombinedSquareFunction radialIndices angularIndices H) volume := by
  unfold aux_angularRadialRecombinedSquareFunction
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  apply Finset.aestronglyMeasurable_fun_sum radialIndices
  intro n hn
  apply AEStronglyMeasurable.pow
  apply AEStronglyMeasurable.norm
  apply Finset.aestronglyMeasurable_fun_sum angularIndices
  intro nu hnu
  exact hH n hn nu hnu

private theorem mssRecombination_eLpNorm_angularSquare_sub_le_pairCard_mul
    (radialIndices angularIndices : Finset Int)
    (full main tail : Int → Int → WaveSpaceTime → Complex)
    (hdecomp : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices, ∀ z,
      full n nu z = main n nu z + tail n nu z)
    (htailMeas : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices,
      AEStronglyMeasurable (tail n nu) volume)
    (E : ENNReal)
    (hE : eLpNorm
      (angularRadialSquareFunction radialIndices angularIndices tail)
        (4 : ENNReal) volume ≤ E) :
    eLpNorm
        (angularRadialSquareFunction radialIndices angularIndices full -
          angularRadialSquareFunction radialIndices angularIndices main)
        (4 : ENNReal) volume ≤
      ((radialIndices.card * angularIndices.card : Nat) : ENNReal) * E := by
  have hcomponent : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices,
      eLpNorm (tail n nu) (4 : ENNReal) volume ≤ E := by
    intro n hn nu hnu
    exact (mssRecombination_eLpNorm_component_le_angularRadialSquareFunction
      radialIndices angularIndices tail hn hnu).trans hE
  calc
    eLpNorm
        (angularRadialSquareFunction radialIndices angularIndices full -
          angularRadialSquareFunction radialIndices angularIndices main)
        (4 : ENNReal) volume ≤
      ∑ n ∈ radialIndices, ∑ nu ∈ angularIndices, E :=
        eLpNorm_four_angularRadialSquareFunction_sub_le_sum_of_eq_add_of_tail_bounds
          radialIndices angularIndices full main tail hdecomp htailMeas
          (fun _ _ => E) (fun n hn nu hnu => hcomponent n hn nu hnu)
    _ = ((radialIndices.card * angularIndices.card : Nat) : ENNReal) * E := by
      simp [Nat.cast_mul, mul_assoc]

private theorem mssRecombination_eLpNorm_auxSquare_sub_le_pairCard_mul
    (radialIndices angularIndices : Finset Int)
    (full main tail : Int → Int → WaveSpaceTime → Complex)
    (hdecomp : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices, ∀ z,
      full n nu z = main n nu z + tail n nu z)
    (htailMeas : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices,
      AEStronglyMeasurable (tail n nu) volume)
    (E : ENNReal)
    (hE : eLpNorm
      (angularRadialSquareFunction radialIndices angularIndices tail)
        (4 : ENNReal) volume ≤ E) :
    eLpNorm
        (aux_angularRadialRecombinedSquareFunction radialIndices angularIndices full -
          aux_angularRadialRecombinedSquareFunction radialIndices angularIndices main)
        (4 : ENNReal) volume ≤
      ((radialIndices.card * angularIndices.card : Nat) : ENNReal) * E := by
  have hcomponent : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices,
      eLpNorm (tail n nu) (4 : ENNReal) volume ≤ E := by
    intro n hn nu hnu
    exact (mssRecombination_eLpNorm_component_le_angularRadialSquareFunction
      radialIndices angularIndices tail hn hnu).trans hE
  calc
    eLpNorm
        (aux_angularRadialRecombinedSquareFunction radialIndices angularIndices full -
          aux_angularRadialRecombinedSquareFunction radialIndices angularIndices main)
        (4 : ENNReal) volume ≤
      ∑ n ∈ radialIndices, ∑ nu ∈ angularIndices, E :=
        eLpNorm_four_aux_angularRadialRecombinedSquareFunction_sub_le_sum_of_eq_add_of_tail_bounds
          radialIndices angularIndices full main tail hdecomp htailMeas
          (fun _ _ => E) (fun n hn nu hnu => hcomponent n hn nu hnu)
    _ = ((radialIndices.card * angularIndices.card : Nat) : ENNReal) * E := by
      simp [Nat.cast_mul, mul_assoc]

private theorem mssRecombination_eLpNorm_right_le_left_add_difference
    (left right : WaveSpaceTime → Real)
    (hleft : AEStronglyMeasurable left volume)
    (hright : AEStronglyMeasurable right volume) :
    eLpNorm right (4 : ENNReal) volume ≤
      eLpNorm left (4 : ENNReal) volume +
        eLpNorm (left - right) (4 : ENNReal) volume := by
  calc
    eLpNorm right (4 : ENNReal) volume =
        eLpNorm (left - (left - right)) (4 : ENNReal) volume := by
          congr 1
          funext z
          simp only [Pi.sub_apply]
          ring
    _ ≤ eLpNorm left (4 : ENNReal) volume +
          eLpNorm (left - right) (4 : ENNReal) volume :=
      eLpNorm_sub_le hleft (hleft.sub hright) (by norm_num)

private noncomputable def mssRecombinationFiniteSquare
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (H : ι → WaveSpaceTime → Complex) : WaveSpaceTime → Real :=
  fun z => Real.sqrt (∑ i ∈ indices, ‖H i z‖ ^ 2)

private theorem mssRecombinationFiniteSquare_eq_norm_piLp
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (H : ι → WaveSpaceTime → Complex) (z : WaveSpaceTime) :
    mssRecombinationFiniteSquare indices H z =
      ‖(WithLp.toLp 2 (fun i : (↑indices) => H i z) :
        PiLp (2 : ENNReal) (fun _ : (↑indices) => Complex))‖ := by
  rw [PiLp.norm_eq_of_L2]
  change mssRecombinationFiniteSquare indices H z =
    Real.sqrt (∑ i : (↑indices), ‖H i z‖ ^ (2 : Nat))
  rw [Finset.sum_coe_sort indices (fun i => ‖H i z‖ ^ (2 : Nat))]
  rfl

private theorem mssRecombinationFiniteSquare_sub_le_tail
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (full main tail : ι → WaveSpaceTime → Complex)
    (hdecomp : ∀ i ∈ indices, ∀ z, full i z = main i z + tail i z)
    (z : WaveSpaceTime) :
    |mssRecombinationFiniteSquare indices full z -
        mssRecombinationFiniteSquare indices main z| ≤
      mssRecombinationFiniteSquare indices tail z := by
  let F : PiLp (2 : ENNReal) (fun _ : (↑indices) => Complex) :=
    WithLp.toLp 2 (fun i : (↑indices) => full i z)
  let M : PiLp (2 : ENNReal) (fun _ : (↑indices) => Complex) :=
    WithLp.toLp 2 (fun i : (↑indices) => main i z)
  let T : PiLp (2 : ENNReal) (fun _ : (↑indices) => Complex) :=
    WithLp.toLp 2 (fun i : (↑indices) => tail i z)
  have hFM : F = M + T := by
    dsimp [F, M, T]
    rw [← WithLp.toLp_add]
    congr 1
    funext i
    exact hdecomp i i.property z
  calc
    |mssRecombinationFiniteSquare indices full z -
        mssRecombinationFiniteSquare indices main z| = |‖F‖ - ‖M‖| := by
          rw [mssRecombinationFiniteSquare_eq_norm_piLp,
            mssRecombinationFiniteSquare_eq_norm_piLp]
    _ ≤ ‖F - M‖ := abs_norm_sub_norm_le _ _
    _ = ‖T‖ := by rw [hFM, add_sub_cancel_left]
    _ = mssRecombinationFiniteSquare indices tail z :=
      (mssRecombinationFiniteSquare_eq_norm_piLp indices tail z).symm

private theorem mssRecombination_verticalSquare_sub_le_tail
    (indices : Finset Int)
    (full main tail : Int → WaveSpaceTime → Complex)
    (hdecomp : ∀ n ∈ indices, ∀ z, full n z = main n z + tail n z)
    (z : WaveSpaceTime) :
    |verticalSquareFunction indices full z - verticalSquareFunction indices main z| ≤
      verticalSquareFunction indices tail z := by
  let F : PiLp (2 : ENNReal) (fun _ : (↑indices) => Complex) :=
    WithLp.toLp 2 (fun n : (↑indices) => full n z)
  let M : PiLp (2 : ENNReal) (fun _ : (↑indices) => Complex) :=
    WithLp.toLp 2 (fun n : (↑indices) => main n z)
  let T : PiLp (2 : ENNReal) (fun _ : (↑indices) => Complex) :=
    WithLp.toLp 2 (fun n : (↑indices) => tail n z)
  have hFM : F = M + T := by
    dsimp [F, M, T]
    rw [← WithLp.toLp_add]
    congr 1
    funext n
    exact hdecomp n n.property z
  calc
    |verticalSquareFunction indices full z - verticalSquareFunction indices main z| =
        |‖F‖ - ‖M‖| := by
          rw [verticalSquareFunction_eq_norm_piLp,
            verticalSquareFunction_eq_norm_piLp]
    _ ≤ ‖F - M‖ := abs_norm_sub_norm_le _ _
    _ = ‖T‖ := by rw [hFM, add_sub_cancel_left]
    _ = verticalSquareFunction indices tail z :=
      (verticalSquareFunction_eq_norm_piLp indices tail z).symm

private theorem mssRecombination_angularSquare_eq_finiteSquare_product
    (radialIndices angularIndices : Finset Int)
    (H : Int → Int → WaveSpaceTime → Complex) :
    angularRadialSquareFunction radialIndices angularIndices H =
      mssRecombinationFiniteSquare (radialIndices.product angularIndices)
        (fun pair z => H pair.1 pair.2 z) := by
  funext z
  unfold angularRadialSquareFunction mssRecombinationFiniteSquare
  apply congrArg Real.sqrt
  exact (Finset.sum_product radialIndices angularIndices
    (fun pair : Int × Int => ‖H pair.1 pair.2 z‖ ^ (2 : Nat))).symm

private theorem mssRecombination_angularSquare_sub_le_tail
    (radialIndices angularIndices : Finset Int)
    (full main tail : Int → Int → WaveSpaceTime → Complex)
    (hdecomp : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices, ∀ z,
      full n nu z = main n nu z + tail n nu z)
    (z : WaveSpaceTime) :
    |angularRadialSquareFunction radialIndices angularIndices full z -
        angularRadialSquareFunction radialIndices angularIndices main z| ≤
      angularRadialSquareFunction radialIndices angularIndices tail z := by
  have hdecomp' : ∀ pair ∈ radialIndices.product angularIndices, ∀ z,
      full pair.1 pair.2 z = main pair.1 pair.2 z + tail pair.1 pair.2 z := by
    intro pair hpair z
    exact hdecomp pair.1 (Finset.mem_product.mp hpair).1 pair.2
      (Finset.mem_product.mp hpair).2 z
  rw [mssRecombination_angularSquare_eq_finiteSquare_product,
    mssRecombination_angularSquare_eq_finiteSquare_product,
    mssRecombination_angularSquare_eq_finiteSquare_product]
  exact mssRecombinationFiniteSquare_sub_le_tail
    (radialIndices.product angularIndices)
    (fun pair z => full pair.1 pair.2 z)
    (fun pair z => main pair.1 pair.2 z)
    (fun pair z => tail pair.1 pair.2 z) hdecomp' z

private theorem mssRecombination_auxSquare_eq_verticalSquare
    (radialIndices angularIndices : Finset Int)
    (H : Int → Int → WaveSpaceTime → Complex) :
    aux_angularRadialRecombinedSquareFunction radialIndices angularIndices H =
      verticalSquareFunction radialIndices
        (fun n z => ∑ nu ∈ angularIndices, H n nu z) := by
  rfl

private theorem mssRecombination_auxSquare_sub_le_tail
    (radialIndices angularIndices : Finset Int)
    (full main tail : Int → Int → WaveSpaceTime → Complex)
    (hdecomp : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices, ∀ z,
      full n nu z = main n nu z + tail n nu z)
    (z : WaveSpaceTime) :
    |aux_angularRadialRecombinedSquareFunction radialIndices angularIndices full z -
        aux_angularRadialRecombinedSquareFunction radialIndices angularIndices main z| ≤
      aux_angularRadialRecombinedSquareFunction radialIndices angularIndices tail z := by
  have hsum : ∀ n ∈ radialIndices, ∀ z,
      (∑ nu ∈ angularIndices, full n nu z) =
        (∑ nu ∈ angularIndices, main n nu z) +
          ∑ nu ∈ angularIndices, tail n nu z := by
    intro n hn z
    calc
      (∑ nu ∈ angularIndices, full n nu z) =
          ∑ nu ∈ angularIndices, (main n nu z + tail n nu z) := by
            apply Finset.sum_congr rfl
            intro nu hnu
            exact hdecomp n hn nu hnu z
      _ = _ := Finset.sum_add_distrib
  rw [mssRecombination_auxSquare_eq_verticalSquare,
    mssRecombination_auxSquare_eq_verticalSquare,
    mssRecombination_auxSquare_eq_verticalSquare]
  exact mssRecombination_verticalSquare_sub_le_tail radialIndices
    (fun n z => ∑ nu ∈ angularIndices, full n nu z)
    (fun n z => ∑ nu ∈ angularIndices, main n nu z)
    (fun n z => ∑ nu ∈ angularIndices, tail n nu z) hsum z

private theorem mssRecombination_eLpNorm_angularSquare_sub_le_tail
    (radialIndices angularIndices : Finset Int)
    (full main tail : Int → Int → WaveSpaceTime → Complex)
    (hdecomp : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices, ∀ z,
      full n nu z = main n nu z + tail n nu z) :
    eLpNorm
        (angularRadialSquareFunction radialIndices angularIndices full -
          angularRadialSquareFunction radialIndices angularIndices main)
        (4 : ENNReal) volume ≤
      eLpNorm (angularRadialSquareFunction radialIndices angularIndices tail)
        (4 : ENNReal) volume := by
  apply eLpNorm_mono
  intro z
  have hnonneg : 0 ≤ angularRadialSquareFunction radialIndices angularIndices tail z :=
    Real.sqrt_nonneg _
  calc
    ‖(angularRadialSquareFunction radialIndices angularIndices full -
        angularRadialSquareFunction radialIndices angularIndices main) z‖ =
        |(angularRadialSquareFunction radialIndices angularIndices full -
          angularRadialSquareFunction radialIndices angularIndices main) z| :=
      Real.norm_eq_abs _
    _ ≤ angularRadialSquareFunction radialIndices angularIndices tail z :=
      mssRecombination_angularSquare_sub_le_tail
        radialIndices angularIndices full main tail hdecomp z
    _ = ‖angularRadialSquareFunction radialIndices angularIndices tail z‖ :=
      (Real.norm_of_nonneg hnonneg).symm

private theorem mssRecombination_eLpNorm_auxSquare_sub_le_tail
    (radialIndices angularIndices : Finset Int)
    (full main tail : Int → Int → WaveSpaceTime → Complex)
    (hdecomp : ∀ n ∈ radialIndices, ∀ nu ∈ angularIndices, ∀ z,
      full n nu z = main n nu z + tail n nu z) :
    eLpNorm
        (aux_angularRadialRecombinedSquareFunction radialIndices angularIndices full -
          aux_angularRadialRecombinedSquareFunction radialIndices angularIndices main)
        (4 : ENNReal) volume ≤
      eLpNorm (aux_angularRadialRecombinedSquareFunction radialIndices angularIndices tail)
        (4 : ENNReal) volume := by
  apply eLpNorm_mono
  intro z
  have hnonneg : 0 ≤ aux_angularRadialRecombinedSquareFunction
      radialIndices angularIndices tail z :=
    Real.sqrt_nonneg _
  calc
    ‖(aux_angularRadialRecombinedSquareFunction radialIndices angularIndices full -
        aux_angularRadialRecombinedSquareFunction radialIndices angularIndices main) z‖ =
        |(aux_angularRadialRecombinedSquareFunction radialIndices angularIndices full -
          aux_angularRadialRecombinedSquareFunction radialIndices angularIndices main) z| :=
      Real.norm_eq_abs _
    _ ≤ aux_angularRadialRecombinedSquareFunction radialIndices angularIndices tail z :=
      mssRecombination_auxSquare_sub_le_tail
        radialIndices angularIndices full main tail hdecomp z
    _ = ‖aux_angularRadialRecombinedSquareFunction radialIndices angularIndices tail z‖ :=
      (Real.norm_of_nonneg hnonneg).symm

private theorem mssRecombination_pair_card_le
    (D : MSSWavefrontCutoffData) {scale : Real} (hscale : 2 ≤ scale) :
    (((relevantRadialIndexEnumeration scale).card *
        (D.angularIndices scale).card : Nat) : ENNReal) ≤
      ENNReal.ofReal (11 * D.angular_card.choose * scale) := by
  let Ca : Real := D.angular_card.choose
  have hCa_pos : 0 < Ca := D.angular_card.choose_spec.1
  have hCa : ((D.angularIndices scale).card : Real) ≤ Ca * Real.sqrt scale :=
    D.angular_card.choose_spec.2 scale hscale
  have hrad : ((relevantRadialIndexEnumeration scale).card : Real) ≤
      11 * Real.sqrt scale :=
    card_relevantRadialIndexEnumeration_le_eleven_mul_sqrt hscale
  have hroot_nonneg : 0 ≤ Real.sqrt scale := Real.sqrt_nonneg _
  have hright_nonneg : 0 ≤ 11 * Real.sqrt scale := by positivity
  have hang_nonneg : 0 ≤ ((D.angularIndices scale).card : Real) := by positivity
  have hpairs_real :
      (((relevantRadialIndexEnumeration scale).card *
          (D.angularIndices scale).card : Nat) : Real) ≤
        11 * Ca * scale := by
    rw [Nat.cast_mul]
    calc
      ((relevantRadialIndexEnumeration scale).card : Real) *
          ((D.angularIndices scale).card : Real) ≤
          (11 * Real.sqrt scale) * (Ca * Real.sqrt scale) :=
        mul_le_mul hrad hCa hang_nonneg hright_nonneg
      _ = 11 * Ca * (Real.sqrt scale) ^ 2 := by ring
      _ = 11 * Ca * scale := by
        rw [Real.sq_sqrt (by linarith : 0 ≤ scale)]
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (by simpa only [Ca] using hpairs_real)

private theorem mssRecombination_scale_delta_inverse_pow_le
    {scale delta : Real} (hscale : 2 ≤ scale) (hdelta : delta ≤ 1)
    (N : Nat) :
    scale ^ delta * (scale⁻¹) ^ (N + 1) ≤ (scale⁻¹) ^ N := by
  have hscale_pos : 0 < scale := by linarith
  have hscale_one : 1 ≤ scale := by linarith
  have hpower : scale ^ delta ≤ scale := by
    calc
      scale ^ delta ≤ scale ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hscale_one hdelta
      _ = scale := Real.rpow_one scale
  calc
    scale ^ delta * (scale⁻¹) ^ (N + 1) ≤
        scale * (scale⁻¹) ^ (N + 1) := by
          gcongr
    _ = (scale⁻¹) ^ N * (scale * scale⁻¹) := by
      rw [pow_succ]
      ring
    _ = (scale⁻¹) ^ N := by
      rw [mul_inv_cancel₀ hscale_pos.ne', mul_one]

private theorem mssRecombination_jointSchwartzRaw_finset_sum_apply
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (J : ι → SchwartzMap JointWaveSpaceTime Complex) (z : WaveSpaceTime) :
    jointSchwartzRaw (∑ i ∈ s, J i) z =
      ∑ i ∈ s, jointSchwartzRaw (J i) z := by
  change
    (FunLike.coeAddMonoidHom (SchwartzMap JointWaveSpaceTime Complex)
      JointWaveSpaceTime Complex) (∑ i ∈ s, J i) (WithLp.toLp 2 z) =
      ∑ i ∈ s,
        (FunLike.coeAddMonoidHom (SchwartzMap JointWaveSpaceTime Complex)
          JointWaveSpaceTime Complex) (J i) (WithLp.toLp 2 z)
  simpa only [Finset.sum_apply] using congrFun
    (map_sum (FunLike.coeAddMonoidHom (SchwartzMap JointWaveSpaceTime Complex)
      JointWaveSpaceTime Complex) J s) (WithLp.toLp 2 z)

private theorem mssRecombination_applyVerticalSpectrum_finset_sum
    (m : SchwartzMap Real Complex) (s : Finset Int)
    (Q : Int → SchwartzMap JointWaveSpaceTime Complex) :
    mssRecombinationApplyVerticalSpectrum m (∑ nu ∈ s, Q nu) =
      ∑ nu ∈ s, mssRecombinationApplyVerticalSpectrum m (Q nu) := by
  unfold mssRecombinationApplyVerticalSpectrum
  exact map_sum
    (SchwartzMap.smulLeftCLM Complex (mssRecombinationJointVerticalFactor m)) Q s

private theorem mssRecombination_sourcePacket_finset_sum
    (D : MSSWavefrontKernelData) (scale : Real) (n : Int)
    (f : SchwartzMap (Euclidean 2) Complex) (hscale : 0 < scale)
    (s : Finset Int) :
    FourierTransform.fourierInv
        (mssRecombinationApplyVerticalSpectrum
          (mssRecombinationVerticalProfile D scale n hscale)
          (∑ nu ∈ s, mssRecombinationBaseSpectrum D scale n nu f)) =
      ∑ nu ∈ s, mssRecombinationSourcePacket D scale n nu f hscale := by
  rw [mssRecombination_applyVerticalSpectrum_finset_sum,
    FourierTransform.fourierInv_sum]
  rfl

private theorem mssRecombination_outerVertical_bound
    (D : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization D) :
    ∃ C : Real, 0 < C ∧
      ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
      eLpNorm
          (verticalRecombined (D.radialTime.vertical : Real → Complex) scale
            (relevantRadialIndexEnumeration scale)
            (fun n => verticalProjection (D.radialTime.vertical : Real → Complex) scale n
              (fun z => ∑ nu ∈ D.angularIndices scale,
                angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
                  (D.chi scale nu) (D.radialTime.time : Real → Complex)
                  (radialPiece (D.radialTime.radial : Real → Complex) scale n
                    (f : Euclidean 2 → Complex)) z)))
          (4 : ENNReal) volume ≤
        ENNReal.ofReal (C * scale ^ (1 / 8 : Real)) *
          eLpNorm
            (aux_angularRadialRecombinedSquareFunction
              (relevantRadialIndexEnumeration scale) (D.angularIndices scale)
            (fun n nu =>
                mssAngularRadialWave D.toMSSWavefrontCutoffData scale n nu
                  (f : Euclidean 2 → Complex)))
            (4 : ENNReal) volume := by
  let B : MSSVerticalCutoff := D.radialTime.toMSSVerticalCutoff
  obtain ⟨C, hC, hbound⟩ :=
    verticalRecombination_of_MSSVerticalCutoff B (4 : ENNReal) 11
      (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro scale hscale f
  let I : Finset Int := relevantRadialIndexEnumeration scale
  let J : Finset Int := D.angularIndices scale
  have hscale_pos : 0 < scale := by linarith
  let H : Int → SchwartzMap JointWaveSpaceTime Complex := fun n =>
    ∑ nu ∈ J, mssRecombinationSourcePacket D scale n nu f hscale_pos
  have hcard : (I.card : Real) ≤ 11 * Real.sqrt scale := by
    dsimp only [I]
    exact card_relevantRadialIndexEnumeration_le_eleven_mul_sqrt hscale
  have hraw : ∀ n : Int, ∀ z : WaveSpaceTime,
      jointSchwartzRaw (H n) z =
        ∑ nu ∈ J,
          mssAngularRadialWave D.toMSSWavefrontCutoffData scale n nu
            (f : Euclidean 2 → Complex) z := by
    intro n z
    dsimp only [H]
    rw [mssRecombination_jointSchwartzRaw_finset_sum_apply]
    apply Finset.sum_congr rfl
    intro nu hnu
    exact congrFun
      (mssAngularRadialWave_eq_mssRecombinationSourcePacket
        D R scale hscale_pos n nu f).symm z
  have hbase : ∀ n : Int,
      jointSchwartzRaw (FourierTransform.fourierInv
          (∑ nu ∈ J, mssRecombinationBaseSpectrum D scale n nu f)) =
        (fun z => ∑ nu ∈ J,
          angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
            (D.chi scale nu) (D.radialTime.time : Real → Complex)
            (radialPiece (D.radialTime.radial : Real → Complex) scale n
              (f : Euclidean 2 → Complex)) z) := by
    intro n
    funext z
    rw [FourierTransform.fourierInv_sum,
      mssRecombination_jointSchwartzRaw_finset_sum_apply]
    apply Finset.sum_congr rfl
    intro nu hnu
    exact congrFun
      (mssRecombinationBasePacket_eq_angularPiece D R scale n nu f hscale_pos) z
  have hHvertical : ∀ n : Int,
      jointSchwartzRaw (H n) =
        verticalProjection (D.radialTime.vertical : Real → Complex) scale n
          (fun z => ∑ nu ∈ J,
            angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
              (D.chi scale nu) (D.radialTime.time : Real → Complex)
              (radialPiece (D.radialTime.radial : Real → Complex) scale n
                (f : Euclidean 2 → Complex)) z) := by
    intro n
    calc
      jointSchwartzRaw (H n) =
          jointSchwartzRaw (FourierTransform.fourierInv
            (mssRecombinationApplyVerticalSpectrum
              (mssRecombinationVerticalProfile D scale n hscale_pos)
              (∑ nu ∈ J, mssRecombinationBaseSpectrum D scale n nu f))) := by
            dsimp only [H]
            rw [← mssRecombination_sourcePacket_finset_sum
              D scale n f hscale_pos J]
      _ = verticalProjection (D.radialTime.vertical : Real → Complex) scale n
            (jointSchwartzRaw (FourierTransform.fourierInv
              (∑ nu ∈ J, mssRecombinationBaseSpectrum D scale n nu f))) := by
            exact (mssRecombination_verticalProjection_eq_sourcePacket
              D scale n hscale_pos
                (∑ nu ∈ J, mssRecombinationBaseSpectrum D scale n nu f)).symm
      _ = _ := by rw [hbase n]
  have hvertical :
      verticalRecombined (B.cutoff : Real → Complex) scale I
          (fun n => jointSchwartzRaw (H n)) =
        verticalRecombined (D.radialTime.vertical : Real → Complex) scale
          (relevantRadialIndexEnumeration scale)
          (fun n => verticalProjection (D.radialTime.vertical : Real → Complex) scale n
            (fun z => ∑ nu ∈ D.angularIndices scale,
              angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
                (D.chi scale nu) (D.radialTime.time : Real → Complex)
                (radialPiece (D.radialTime.radial : Real → Complex) scale n
                  (f : Euclidean 2 → Complex)) z)) := by
    funext z
    unfold verticalRecombined
    simp only [B, MSSRadialTimeCutoffs.toMSSVerticalCutoff, I]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hHvertical n]
  have hsquare :
      verticalSquareFunction I (fun n => jointSchwartzRaw (H n)) =
        aux_angularRadialRecombinedSquareFunction
          (relevantRadialIndexEnumeration scale) (D.angularIndices scale)
          (fun n nu =>
            mssAngularRadialWave D.toMSSWavefrontCutoffData scale n nu
              (f : Euclidean 2 → Complex)) := by
    funext z
    unfold verticalSquareFunction aux_angularRadialRecombinedSquareFunction
    simp only [I, J]
    apply congrArg Real.sqrt
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    rw [hraw n z]
  have hgain : verticalRecombinationGain (4 : ENNReal) = (1 / 8 : Real) := by
    rw [verticalRecombinationGain]
    norm_num
  have h := hbound scale hscale I hcard H
  rw [hvertical, hsquare] at h
  simpa only [hgain] using h

private theorem mssRecombination_outerVertical_bound_of_core
    (D E : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization E)
    (hcore : E.toMSSWavefrontCutoffData = D.toMSSWavefrontCutoffData) :
    ∃ C : Real, 0 < C ∧
      ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
      eLpNorm
          (verticalRecombined (D.radialTime.vertical : Real → Complex) scale
            (relevantRadialIndexEnumeration scale)
            (fun n => verticalProjection (D.radialTime.vertical : Real → Complex) scale n
              (fun z => ∑ nu ∈ D.angularIndices scale,
                angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
                  (D.chi scale nu) (D.radialTime.time : Real → Complex)
                  (radialPiece (D.radialTime.radial : Real → Complex) scale n
                    (f : Euclidean 2 → Complex)) z)))
          (4 : ENNReal) volume ≤
        ENNReal.ofReal (C * scale ^ (1 / 8 : Real)) *
          eLpNorm
            (aux_angularRadialRecombinedSquareFunction
              (relevantRadialIndexEnumeration scale) (D.angularIndices scale)
              (fun n nu =>
                mssAngularRadialWave D.toMSSWavefrontCutoffData scale n nu
                  (f : Euclidean 2 → Complex)))
            (4 : ENNReal) volume := by
  simpa only [hcore] using
    (mssRecombination_outerVertical_bound E R)

private theorem mssRecombination_aestronglyMeasurable_outerVerticalTerm
    (D : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization D)
    (scale : Real) (hscale : 0 < scale)
    (f : SchwartzMap (Euclidean 2) Complex) :
    AEStronglyMeasurable
      (verticalRecombined (D.radialTime.vertical : Real → Complex) scale
        (relevantRadialIndexEnumeration scale)
        (fun n => verticalProjection (D.radialTime.vertical : Real → Complex) scale n
          (fun z => ∑ nu ∈ D.angularIndices scale,
            angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
              (D.chi scale nu) (D.radialTime.time : Real → Complex)
              (radialPiece (D.radialTime.radial : Real → Complex) scale n
                (f : Euclidean 2 → Complex)) z))) volume := by
  classical
  let I : Finset Int := relevantRadialIndexEnumeration scale
  let J : Finset Int := D.angularIndices scale
  let B : Int → SchwartzMap JointWaveSpaceTime Complex := fun n =>
    ∑ nu ∈ J, mssRecombinationBaseSpectrum D scale n nu f
  let Q : Int → SchwartzMap JointWaveSpaceTime Complex := fun n =>
    mssRecombinationApplyVerticalSpectrum
      (mssRecombinationVerticalProfile D scale n hscale) (B n)
  let G : Int → SchwartzMap JointWaveSpaceTime Complex := fun n =>
    FourierTransform.fourierInv
      (mssRecombinationApplyVerticalSpectrum
        (mssRecombinationVerticalProfile D scale n hscale) (Q n))
  have hbase : ∀ n : Int,
      jointSchwartzRaw (FourierTransform.fourierInv (B n)) =
        (fun z => ∑ nu ∈ J,
          angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
            (D.chi scale nu) (D.radialTime.time : Real → Complex)
            (radialPiece (D.radialTime.radial : Real → Complex) scale n
              (f : Euclidean 2 → Complex)) z) := by
    intro n
    funext z
    dsimp only [B]
    rw [FourierTransform.fourierInv_sum,
      mssRecombination_jointSchwartzRaw_finset_sum_apply]
    apply Finset.sum_congr rfl
    intro nu hnu
    exact congrFun
      (mssRecombinationBasePacket_eq_angularPiece D R scale n nu f hscale) z
  have hterm : ∀ n : Int,
      jointSchwartzRaw (G n) =
        verticalProjection (D.radialTime.vertical : Real → Complex) scale n
          (verticalProjection (D.radialTime.vertical : Real → Complex) scale n
            (fun z => ∑ nu ∈ J,
              angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
                (D.chi scale nu) (D.radialTime.time : Real → Complex)
                (radialPiece (D.radialTime.radial : Real → Complex) scale n
                  (f : Euclidean 2 → Complex)) z)) := by
    intro n
    calc
      jointSchwartzRaw (G n) =
          verticalProjection (D.radialTime.vertical : Real → Complex) scale n
            (jointSchwartzRaw (FourierTransform.fourierInv (Q n))) := by
              dsimp only [G]
              exact (mssRecombination_verticalProjection_eq_sourcePacket
                D scale n hscale (Q n)).symm
      _ = verticalProjection (D.radialTime.vertical : Real → Complex) scale n
            (verticalProjection (D.radialTime.vertical : Real → Complex) scale n
              (jointSchwartzRaw (FourierTransform.fourierInv (B n)))) := by
              rw [show jointSchwartzRaw (FourierTransform.fourierInv (Q n)) =
                  verticalProjection (D.radialTime.vertical : Real → Complex) scale n
                    (jointSchwartzRaw (FourierTransform.fourierInv (B n))) by
                dsimp only [Q]
                exact (mssRecombination_verticalProjection_eq_sourcePacket
                  D scale n hscale (B n)).symm]
      _ = _ := by rw [hbase n]
  have hrepr :
      verticalRecombined (D.radialTime.vertical : Real → Complex) scale I
        (fun n => verticalProjection (D.radialTime.vertical : Real → Complex) scale n
          (fun z => ∑ nu ∈ J,
            angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
              (D.chi scale nu) (D.radialTime.time : Real → Complex)
              (radialPiece (D.radialTime.radial : Real → Complex) scale n
                (f : Euclidean 2 → Complex)) z)) =
        (fun z => ∑ n ∈ I, jointSchwartzRaw (G n) z) := by
    funext z
    unfold verticalRecombined
    apply Finset.sum_congr rfl
    intro n hn
    exact congrFun (hterm n).symm z
  have hmeas : AEStronglyMeasurable
      (fun z => ∑ n ∈ I, jointSchwartzRaw (G n) z) volume := by
    apply Finset.aestronglyMeasurable_fun_sum I
    intro n hn
    exact mssRecombination_aestronglyMeasurable_jointSchwartzRaw (G n)
  rw [← hrepr] at hmeas
  simpa only [I, J] using hmeas

private theorem mssRecombination_removeVertical_bound_of_core
    (D E : MSSWavefrontKernelData) (R : MSSWavefrontRawProfileRealization E)
    (hcore : E.toMSSWavefrontCutoffData = D.toMSSWavefrontCutoffData) :
    ∃ C : Real, 0 < C ∧
      ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
      eLpNorm
          (angularRadialSquareFunction (relevantRadialIndexEnumeration scale)
            (D.angularIndices scale)
            (fun n nu =>
              mssAngularRadialWave D.toMSSWavefrontCutoffData scale n nu
                (f : Euclidean 2 → Complex)))
          (4 : ENNReal) volume ≤
        ENNReal.ofReal C *
          eLpNorm
            (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
              (f : Euclidean 2 → Complex))
            (4 : ENNReal) volume := by
  obtain ⟨C, hC, hremove⟩ :=
    removeVerticalProjections_of_schwartz E.radialTime.vertical
  refine ⟨C, hC, ?_⟩
  intro scale hscale f
  have hscale_pos : 0 < scale := by linarith
  let I : Finset Int := relevantRadialIndexEnumeration scale
  let J : Finset Int := E.angularIndices scale
  let H : Int → Int → SchwartzMap JointWaveSpaceTime Complex :=
    fun n nu => FourierTransform.fourierInv
      (mssRecombinationBaseSpectrum E scale n nu f)
  have hprojected : ∀ n : Int, ∀ nu : Int,
      verticalProjection (E.radialTime.vertical : Real → Complex) scale n
          (jointSchwartzRaw (H n nu)) =
        mssAngularRadialWave E.toMSSWavefrontCutoffData scale n nu
          (f : Euclidean 2 → Complex) := by
    intro n nu
    dsimp only [H]
    rw [mssRecombination_verticalProjection_eq_sourcePacket E scale n hscale_pos]
    exact (mssAngularRadialWave_eq_mssRecombinationSourcePacket
      E R scale hscale_pos n nu f).symm
  have hbase : ∀ n : Int, ∀ nu : Int,
      jointSchwartzRaw (H n nu) =
        angularPiece scale (E.radialTime.amplitude : Euclidean 2 → Complex)
          (E.chi scale nu) (E.radialTime.time : Real → Complex)
          (radialPiece (E.radialTime.radial : Real → Complex) scale n
            (f : Euclidean 2 → Complex)) := by
    intro n nu
    dsimp only [H]
    exact mssRecombinationBasePacket_eq_angularPiece E R scale n nu f hscale_pos
  have hleft :
      angularRadialSquareFunction I J
          (fun n nu => verticalProjection (E.radialTime.vertical : Real → Complex)
            scale n (jointSchwartzRaw (H n nu))) =
        angularRadialSquareFunction I J
          (fun n nu => mssAngularRadialWave E.toMSSWavefrontCutoffData scale n nu
            (f : Euclidean 2 → Complex)) := by
    funext z
    unfold angularRadialSquareFunction
    apply congrArg Real.sqrt
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro nu hnu
    simpa only using congrArg (fun w : Complex => ‖w‖ ^ 2)
      (congrFun (hprojected n nu) z)
  have hright :
      angularRadialSquareFunction I J (fun n nu => jointSchwartzRaw (H n nu)) =
        mssFineSquareFunction E.toMSSWavefrontCutoffData scale
          (f : Euclidean 2 → Complex) := by
    funext z
    unfold mssFineSquareFunction fineSquareFunction angularRadialSquareFunction
    apply congrArg Real.sqrt
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro nu hnu
    simpa only using congrArg (fun w : Complex => ‖w‖ ^ 2)
      (congrFun (hbase n nu) z)
  have h := hremove scale hscale I J H
  rw [hleft, hright] at h
  simpa only [I, J, hcore] using h

private theorem mssRecombination_aux_bound
    (D : MSSWavefrontKernelData)
    (A : MSSFineAngularData D.toMSSWavefrontCutoffData)
    (structured : MSSStructuredRecombinationData D)
    (eta : Real) (heta : 0 < eta) (N : Nat) :
    ∃ C : Real, 0 < C ∧
      ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
        eLpNorm
            (aux_angularRadialRecombinedSquareFunction
              (relevantRadialIndexEnumeration scale) (D.angularIndices scale)
              (fun n nu =>
                mssAngularRadialWave D.toMSSWavefrontCutoffData scale n nu
                  (f : Euclidean 2 → Complex)))
            (4 : ENNReal) volume ≤
          ENNReal.ofReal (C * scale ^ eta) *
            eLpNorm
              (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
                (f : Euclidean 2 → Complex))
              (4 : ENNReal) volume +
          ENNReal.ofReal (C * (scale⁻¹) ^ N) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
  let delta : Real := min (eta / 2) (1 / 2)
  have hdelta_pos : 0 < delta := by
    dsimp only [delta]
    exact lt_min (by linarith) (by norm_num)
  have hdelta_le_eta : delta ≤ eta := by
    calc
      delta ≤ eta / 2 := min_le_left _ _
      _ ≤ eta := by linarith
  have hdelta_le_one : delta ≤ 1 := by
    calc
      delta ≤ 1 / 2 := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hgeometry_two := A.geometry 2 (by norm_num)
  have hsector : 0 < A.sectorRadius := hgeometry_two.1
  have hspacing : 0 < A.spacingLower := hgeometry_two.2.2.1
  have hplate := plateOverlap_of_angularSectorGeometry
    (mssAngularMaxLevel A.sectorRadius A.spacingLower) D.angularConstant
    A.sectorRadius A.spacingLower A.spacingUpper D.angularConstant_pos
  have hlevels := mssAngularMaxLevel_levelData
    (spacingUpper := A.spacingUpper) hsector hspacing
  obtain ⟨gamma, hgamma_pos, hgamma_upper, Ceta, hCeta, hOverlap⟩ :=
    (overlapSquareFunction_of_levelData
      (mssAngularMaxLevel A.sectorRadius A.spacingLower) D.angularConstant
      A.sectorRadius A.spacingLower A.spacingUpper)
      hplate hlevels delta hdelta_pos
  let g : MSSAdmissibleGamma := ⟨gamma, hgamma_pos, hgamma_upper⟩
  let E : MSSWavefrontKernelData := structured.wavefrontFamily.data g
  let R : MSSWavefrontRawProfileRealization E :=
    structured.wavefrontFamily.realization g
  let hregularity : MSSWavefrontSpatialProfilePolynomialRegularity E :=
    structured.wavefrontFamily.regularity g
  have hcore : E.toMSSWavefrontCutoffData = D.toMSSWavefrontCutoffData := by
    simpa only [E] using structured.wavefrontFamily.data_core g
  have hgammaE : E.gamma = gamma := by
    simpa only [E, g] using structured.wavefrontFamily.data_gamma g
  obtain ⟨Cremove, hCremove, hremove⟩ :=
    mssRecombination_removeVertical_bound_of_core E E R rfl
  have hWF := wavefrontLocalization_of_MSSWavefrontKernelData E R hregularity
  obtain ⟨Cerror, hCerror, herror⟩ :=
    hWF.1 E.gamma_pos E.gamma_lt_tenth (N + 1) (by omega)
  let Cpair : Real := 11 * E.angular_card.choose
  let Cfine : Real := Ceta * Cremove
  let Cresidual : Real := Ceta * Cerror + Cpair * Cerror
  let C : Real := Cfine + Cresidual
  have hCpair : 0 < Cpair := by
    dsimp only [Cpair]
    exact mul_pos (by norm_num) E.angular_card.choose_spec.1
  have hCfine : 0 < Cfine := by
    dsimp only [Cfine]
    exact mul_pos hCeta hCremove
  have hCresidual : 0 < Cresidual := by
    dsimp only [Cresidual]
    exact add_pos (mul_pos hCeta hCerror) (mul_pos hCpair hCerror)
  refine ⟨C, add_pos hCfine hCresidual, ?_⟩
  intro scale hscale f
  have hscale_pos : 0 < scale := by linarith
  have hscale_one : 1 ≤ scale := by linarith
  let I : Finset Int := relevantRadialIndexEnumeration scale
  let J : Finset Int := E.angularIndices scale
  let Raw : Int → Int → WaveSpaceTime → Complex := fun n nu =>
    mssAngularRadialWave E.toMSSWavefrontCutoffData scale n nu
      (f : Euclidean 2 → Complex)
  let W : Int → Int → WaveSpaceTime → Complex := fun n nu =>
    mssWavefrontAngularRadialWave E.toMSSWavefrontCutoffData scale gamma n nu
      (f : Euclidean 2 → Complex)
  let Tail : Int → Int → WaveSpaceTime → Complex := fun n nu => Raw n nu - W n nu
  let P : Int → Int → SchwartzMap JointWaveSpaceTime Complex := fun n nu =>
    mssRecombinationWavefrontSpectrum E R scale gamma n nu f hscale_pos
  let overlapCoeff : ENNReal := ENNReal.ofReal (Ceta * scale ^ delta)
  let errorBudget : ENNReal :=
    ENNReal.ofReal (Cerror * (scale⁻¹) ^ (N + 1)) *
      eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume
  have hgeometry : angularSectorGeometry scale J (E.directions scale)
      A.sectorRadius A.spacingLower A.spacingUpper := by
    simpa only [J, hcore] using A.geometry scale hscale
  have hsupport : ∀ n ∈ I, ∀ nu ∈ J,
      Function.support (jointSchwartzRaw (P n nu)) ⊆
        conicPlate scale gamma D.angularConstant n (E.directions scale nu) := by
    intro n hn nu hnu
    dsimp only [P]
    simpa only [I, J, hcore] using
      (mssRecombinationWavefrontSpectrum_support E R hregularity
        scale gamma hgammaE hscale n nu hn hnu f)
  have hOverlapAt := hOverlap scale hscale I J (E.directions scale)
    hgeometry P hsupport
  have hPtoW :
      (fun n nu => jointSchwartzRaw (FourierTransform.fourierInv (P n nu))) = W := by
    funext n nu z
    dsimp only [P, W]
    exact congrFun
      (mssWavefrontAngularRadialWave_eq_mssRecombinationWavefrontSpectrum
        E R scale gamma hscale_pos n nu f).symm z
  rw [hPtoW] at hOverlapAt
  have herrorAt :
      eLpNorm (angularRadialSquareFunction I J Tail) (4 : ENNReal) volume ≤
        errorBudget := by
    change eLpNorm
        (angularRadialSquareFunction I J (fun n nu z => Raw n nu z - W n nu z))
        (4 : ENNReal) volume ≤ errorBudget
    dsimp only [Raw, W, errorBudget]
    simpa only [I, J, hgammaE] using herror scale hscale f
  have hRawMeas : ∀ n ∈ I, ∀ nu ∈ J,
      AEStronglyMeasurable (Raw n nu) volume := by
    intro n hn nu hnu
    dsimp only [Raw]
    rw [mssAngularRadialWave_eq_mssRecombinationSourcePacket
      E R scale hscale_pos n nu f]
    exact mssRecombination_aestronglyMeasurable_jointSchwartzRaw _
  have hWMeas : ∀ n ∈ I, ∀ nu ∈ J,
      AEStronglyMeasurable (W n nu) volume := by
    intro n hn nu hnu
    dsimp only [W]
    rw [mssWavefrontAngularRadialWave_eq_mssRecombinationWavefrontSpectrum
      E R scale gamma hscale_pos n nu f]
    exact mssRecombination_aestronglyMeasurable_jointSchwartzRaw _
  have hTailMeas : ∀ n ∈ I, ∀ nu ∈ J,
      AEStronglyMeasurable (Tail n nu) volume := by
    intro n hn nu hnu
    simpa only [Tail] using (hRawMeas n hn nu hnu).sub (hWMeas n hn nu hnu)
  have hdecomp : ∀ n ∈ I, ∀ nu ∈ J, ∀ z,
      Raw n nu z = W n nu z + Tail n nu z := by
    intro n hn nu hnu z
    simp only [Tail, Pi.sub_apply]
    ring
  have hRawSquareMeas :=
    mssRecombination_aestronglyMeasurable_angularRadialSquareFunction
      I J Raw hRawMeas
  have hWSquareMeas :=
    mssRecombination_aestronglyMeasurable_angularRadialSquareFunction
      I J W hWMeas
  have hRawAuxMeas :=
    mssRecombination_aestronglyMeasurable_auxAngularRadialRecombined
      I J Raw hRawMeas
  have hWAuxMeas :=
    mssRecombination_aestronglyMeasurable_auxAngularRadialRecombined
      I J W hWMeas
  have hSquareDiff :
      eLpNorm
          (angularRadialSquareFunction I J Raw -
            angularRadialSquareFunction I J W)
          (4 : ENNReal) volume ≤
        eLpNorm (angularRadialSquareFunction I J Tail) (4 : ENNReal) volume := by
    exact mssRecombination_eLpNorm_angularSquare_sub_le_tail
      I J Raw W Tail hdecomp
  have hSquareError :
      eLpNorm
          (angularRadialSquareFunction I J Raw -
            angularRadialSquareFunction I J W)
          (4 : ENNReal) volume ≤ errorBudget :=
    hSquareDiff.trans herrorAt
  have hWsquare :
      eLpNorm (angularRadialSquareFunction I J W) (4 : ENNReal) volume ≤
        eLpNorm (angularRadialSquareFunction I J Raw) (4 : ENNReal) volume +
          errorBudget := by
    calc
      eLpNorm (angularRadialSquareFunction I J W) (4 : ENNReal) volume ≤
          eLpNorm (angularRadialSquareFunction I J Raw) (4 : ENNReal) volume +
            eLpNorm (angularRadialSquareFunction I J Raw -
              angularRadialSquareFunction I J W) (4 : ENNReal) volume :=
        mssRecombination_eLpNorm_right_le_left_add_difference
          (angularRadialSquareFunction I J Raw)
          (angularRadialSquareFunction I J W) hRawSquareMeas hWSquareMeas
      _ ≤ eLpNorm (angularRadialSquareFunction I J Raw) (4 : ENNReal) volume +
            errorBudget := add_le_add_right hSquareError _
  have hAuxDiff := mssRecombination_eLpNorm_auxSquare_sub_le_pairCard_mul
    I J Raw W Tail hdecomp hTailMeas errorBudget herrorAt
  have hpair : ((I.card * J.card : Nat) : ENNReal) ≤
      ENNReal.ofReal (Cpair * scale) := by
    simpa only [I, J, Cpair] using
      (mssRecombination_pair_card_le E.toMSSWavefrontCutoffData hscale)
  have hAuxDiffRev :
      eLpNorm
          (aux_angularRadialRecombinedSquareFunction I J W -
            aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume ≤
        ENNReal.ofReal (Cpair * scale) * errorBudget := by
    calc
      eLpNorm
          (aux_angularRadialRecombinedSquareFunction I J W -
            aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume =
        eLpNorm
          (aux_angularRadialRecombinedSquareFunction I J Raw -
            aux_angularRadialRecombinedSquareFunction I J W)
          (4 : ENNReal) volume := by
            rw [show
              aux_angularRadialRecombinedSquareFunction I J W -
                  aux_angularRadialRecombinedSquareFunction I J Raw =
                -(aux_angularRadialRecombinedSquareFunction I J Raw -
                  aux_angularRadialRecombinedSquareFunction I J W) by
                funext z
                simp only [Pi.sub_apply, Pi.neg_apply]
                ring,
              eLpNorm_neg]
      _ ≤ ((I.card * J.card : Nat) : ENNReal) * errorBudget := hAuxDiff
      _ ≤ ENNReal.ofReal (Cpair * scale) * errorBudget :=
        mul_le_mul_of_nonneg_right hpair bot_le
  have hRawAux :
      eLpNorm (aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume ≤
        eLpNorm (aux_angularRadialRecombinedSquareFunction I J W)
          (4 : ENNReal) volume +
          ENNReal.ofReal (Cpair * scale) * errorBudget := by
    calc
      eLpNorm (aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume ≤
        eLpNorm (aux_angularRadialRecombinedSquareFunction I J W)
          (4 : ENNReal) volume +
          eLpNorm
            (aux_angularRadialRecombinedSquareFunction I J W -
              aux_angularRadialRecombinedSquareFunction I J Raw)
            (4 : ENNReal) volume :=
        mssRecombination_eLpNorm_right_le_left_add_difference
          (aux_angularRadialRecombinedSquareFunction I J W)
          (aux_angularRadialRecombinedSquareFunction I J Raw) hWAuxMeas hRawAuxMeas
      _ ≤ eLpNorm (aux_angularRadialRecombinedSquareFunction I J W)
            (4 : ENNReal) volume +
          ENNReal.ofReal (Cpair * scale) * errorBudget :=
        add_le_add_right hAuxDiffRev _
  have hAuxBase :
      eLpNorm (aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume ≤
        overlapCoeff * eLpNorm (angularRadialSquareFunction I J Raw)
          (4 : ENNReal) volume +
          overlapCoeff * errorBudget +
            ENNReal.ofReal (Cpair * scale) * errorBudget := by
    calc
      eLpNorm (aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume ≤
        eLpNorm (aux_angularRadialRecombinedSquareFunction I J W)
          (4 : ENNReal) volume +
          ENNReal.ofReal (Cpair * scale) * errorBudget := hRawAux
      _ ≤ overlapCoeff * eLpNorm (angularRadialSquareFunction I J W)
            (4 : ENNReal) volume +
          ENNReal.ofReal (Cpair * scale) * errorBudget :=
        add_le_add (by simpa only [overlapCoeff] using hOverlapAt) le_rfl
      _ ≤ overlapCoeff *
            (eLpNorm (angularRadialSquareFunction I J Raw) (4 : ENNReal) volume +
              errorBudget) +
          ENNReal.ofReal (Cpair * scale) * errorBudget :=
        add_le_add (mul_le_mul_right hWsquare overlapCoeff) le_rfl
      _ = overlapCoeff * eLpNorm (angularRadialSquareFunction I J Raw)
            (4 : ENNReal) volume +
          overlapCoeff * errorBudget +
            ENNReal.ofReal (Cpair * scale) * errorBudget := by ring
  have hRemoveRaw :
      eLpNorm (angularRadialSquareFunction I J Raw) (4 : ENNReal) volume ≤
        ENNReal.ofReal Cremove *
          eLpNorm
            (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
              (f : Euclidean 2 → Complex))
            (4 : ENNReal) volume := by
    simpa only [I, J, Raw] using hremove scale hscale f
  have hAuxWithFine :
      eLpNorm (aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume ≤
        overlapCoeff *
            (ENNReal.ofReal Cremove *
              eLpNorm
                (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
                  (f : Euclidean 2 → Complex))
                (4 : ENNReal) volume) +
          (overlapCoeff * errorBudget +
            ENNReal.ofReal (Cpair * scale) * errorBudget) := by
    calc
      eLpNorm (aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume ≤
        overlapCoeff * eLpNorm (angularRadialSquareFunction I J Raw)
          (4 : ENNReal) volume +
          overlapCoeff * errorBudget +
            ENNReal.ofReal (Cpair * scale) * errorBudget := hAuxBase
      _ = overlapCoeff * eLpNorm (angularRadialSquareFunction I J Raw)
            (4 : ENNReal) volume +
          (overlapCoeff * errorBudget +
            ENNReal.ofReal (Cpair * scale) * errorBudget) := by ring
      _ ≤ overlapCoeff *
            (ENNReal.ofReal Cremove *
              eLpNorm
                (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
                  (f : Euclidean 2 → Complex))
                (4 : ENNReal) volume) +
          (overlapCoeff * errorBudget +
            ENNReal.ofReal (Cpair * scale) * errorBudget) :=
        add_le_add (mul_le_mul_right hRemoveRaw overlapCoeff) le_rfl
  have hscale_delta_eta : scale ^ delta ≤ scale ^ eta :=
    Real.rpow_le_rpow_of_exponent_le hscale_one hdelta_le_eta
  have hfineCoeff : overlapCoeff * ENNReal.ofReal Cremove ≤
      ENNReal.ofReal (Cfine * scale ^ eta) := by
    dsimp only [overlapCoeff, Cfine]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Ceta * scale ^ delta)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (Ceta * scale ^ delta) * Cremove =
          (Ceta * Cremove) * scale ^ delta := by ring
      _ ≤ (Ceta * Cremove) * scale ^ eta :=
        mul_le_mul_of_nonneg_left hscale_delta_eta
          (mul_nonneg hCeta.le hCremove.le)
  have hdelta_error :=
    mssRecombination_scale_delta_inverse_pow_le hscale hdelta_le_one N
  have hOverlapErrorScalar :
      overlapCoeff * ENNReal.ofReal (Cerror * (scale⁻¹) ^ (N + 1)) ≤
        ENNReal.ofReal (Ceta * Cerror * (scale⁻¹) ^ N) := by
    dsimp only [overlapCoeff]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Ceta * scale ^ delta)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (Ceta * scale ^ delta) * (Cerror * (scale⁻¹) ^ (N + 1)) =
          (Ceta * Cerror) *
            (scale ^ delta * (scale⁻¹) ^ (N + 1)) := by ring
      _ ≤ (Ceta * Cerror) * (scale⁻¹) ^ N :=
        mul_le_mul_of_nonneg_left hdelta_error (mul_nonneg hCeta.le hCerror.le)
  have hscale_inverse :
      scale * (scale⁻¹) ^ (N + 1) = (scale⁻¹) ^ N := by
    rw [pow_succ]
    calc
      scale * ((scale⁻¹) ^ N * scale⁻¹) =
          (scale⁻¹) ^ N * (scale * scale⁻¹) := by ring
      _ = (scale⁻¹) ^ N := by
        rw [mul_inv_cancel₀ hscale_pos.ne', mul_one]
  have hPairErrorScalar :
      ENNReal.ofReal (Cpair * scale) *
          ENNReal.ofReal (Cerror * (scale⁻¹) ^ (N + 1)) =
        ENNReal.ofReal (Cpair * Cerror * (scale⁻¹) ^ N) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Cpair * scale)]
    congr 1
    calc
      (Cpair * scale) * (Cerror * (scale⁻¹) ^ (N + 1)) =
          (Cpair * Cerror) * (scale * (scale⁻¹) ^ (N + 1)) := by ring
      _ = Cpair * Cerror * (scale⁻¹) ^ N := by rw [hscale_inverse]
  have hOverlapError : overlapCoeff * errorBudget ≤
      ENNReal.ofReal (Ceta * Cerror * (scale⁻¹) ^ N) *
        eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
    dsimp only [errorBudget]
    calc
      overlapCoeff *
          (ENNReal.ofReal (Cerror * (scale⁻¹) ^ (N + 1)) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume) =
        (overlapCoeff * ENNReal.ofReal (Cerror * (scale⁻¹) ^ (N + 1))) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by ring
      _ ≤ ENNReal.ofReal (Ceta * Cerror * (scale⁻¹) ^ N) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume :=
        mul_le_mul_left hOverlapErrorScalar _
  have hPairError : ENNReal.ofReal (Cpair * scale) * errorBudget =
      ENNReal.ofReal (Cpair * Cerror * (scale⁻¹) ^ N) *
        eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
    change ENNReal.ofReal (Cpair * scale) *
        (ENNReal.ofReal (Cerror * (scale⁻¹) ^ (N + 1)) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume) = _
    calc
      ENNReal.ofReal (Cpair * scale) *
          (ENNReal.ofReal (Cerror * (scale⁻¹) ^ (N + 1)) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume) =
        (ENNReal.ofReal (Cpair * scale) *
          ENNReal.ofReal (Cerror * (scale⁻¹) ^ (N + 1))) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by ring
      _ = _ := by rw [hPairErrorScalar]
  have hErrorSum :
      ENNReal.ofReal (Ceta * Cerror * (scale⁻¹) ^ N) +
          ENNReal.ofReal (Cpair * Cerror * (scale⁻¹) ^ N) =
        ENNReal.ofReal (Cresidual * (scale⁻¹) ^ N) := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ Ceta * Cerror * (scale⁻¹) ^ N)
      (by positivity : 0 ≤ Cpair * Cerror * (scale⁻¹) ^ N)]
    congr 1
    dsimp only [Cresidual]
    ring
  have hAuxE :
      eLpNorm (aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume ≤
        ENNReal.ofReal (Cfine * scale ^ eta) *
          eLpNorm
            (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
              (f : Euclidean 2 → Complex))
            (4 : ENNReal) volume +
          ENNReal.ofReal (Cresidual * (scale⁻¹) ^ N) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
    calc
      eLpNorm (aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume ≤
        overlapCoeff *
            (ENNReal.ofReal Cremove *
              eLpNorm
                (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
                  (f : Euclidean 2 → Complex))
                (4 : ENNReal) volume) +
          (overlapCoeff * errorBudget +
            ENNReal.ofReal (Cpair * scale) * errorBudget) := hAuxWithFine
      _ ≤ ENNReal.ofReal (Cfine * scale ^ eta) *
            eLpNorm
              (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
                (f : Euclidean 2 → Complex))
              (4 : ENNReal) volume +
          (ENNReal.ofReal (Ceta * Cerror * (scale⁻¹) ^ N) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume +
            ENNReal.ofReal (Cpair * Cerror * (scale⁻¹) ^ N) *
              eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume) := by
        apply add_le_add
        · calc
            overlapCoeff *
                (ENNReal.ofReal Cremove *
                  eLpNorm
                    (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
                      (f : Euclidean 2 → Complex))
                    (4 : ENNReal) volume) =
              (overlapCoeff * ENNReal.ofReal Cremove) *
                eLpNorm
                  (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
                    (f : Euclidean 2 → Complex))
                  (4 : ENNReal) volume := by ring
            _ ≤ ENNReal.ofReal (Cfine * scale ^ eta) *
                eLpNorm
                  (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
                    (f : Euclidean 2 → Complex))
                  (4 : ENNReal) volume :=
              mul_le_mul_left hfineCoeff _
        · exact add_le_add hOverlapError (by rw [hPairError])
      _ = ENNReal.ofReal (Cfine * scale ^ eta) *
            eLpNorm
              (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
                (f : Euclidean 2 → Complex))
              (4 : ENNReal) volume +
          ENNReal.ofReal (Cresidual * (scale⁻¹) ^ N) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
        rw [← hErrorSum]
        ring
  have hCfine_le : Cfine ≤ C := le_add_of_nonneg_right hCresidual.le
  have hCresidual_le : Cresidual ≤ C := le_add_of_nonneg_left hCfine.le
  have hFineCoeff_le : ENNReal.ofReal (Cfine * scale ^ eta) ≤
      ENNReal.ofReal (C * scale ^ eta) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right hCfine_le (Real.rpow_nonneg hscale_pos.le _)
  have hResidualCoeff_le : ENNReal.ofReal (Cresidual * (scale⁻¹) ^ N) ≤
      ENNReal.ofReal (C * (scale⁻¹) ^ N) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right hCresidual_le
      (pow_nonneg (inv_nonneg.mpr hscale_pos.le) _)
  have hAuxEfinal :
      eLpNorm (aux_angularRadialRecombinedSquareFunction I J Raw)
          (4 : ENNReal) volume ≤
        ENNReal.ofReal (C * scale ^ eta) *
          eLpNorm
            (mssFineSquareFunction E.toMSSWavefrontCutoffData scale
              (f : Euclidean 2 → Complex))
            (4 : ENNReal) volume +
          ENNReal.ofReal (C * (scale⁻¹) ^ N) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume :=
    hAuxE.trans (add_le_add
      (mul_le_mul_left hFineCoeff_le _)
      (mul_le_mul_left hResidualCoeff_le _))
  simpa only [I, J, Raw, hcore] using hAuxEfinal

/-- The structured gamma-family data close the MSS recombination estimate.
The outer vertical estimate supplies the `1 / 8` gain, wave-front overlap
supplies the arbitrarily small loss, and the exact radial-time residual is
absorbed at arbitrary rapid decay. -/
theorem mssRecombination_of_structuredData
    (D : MSSWavefrontKernelData)
    (A : MSSFineAngularData D.toMSSWavefrontCutoffData)
    (structured : MSSStructuredRecombinationData D)
    (uniform : MSSFineSpatialProfileUniformRegularity D)
    (hslab : D.HasLightRayTimeSlabSupport) :
    mssRecombination D A structured uniform hslab := by
  unfold mssRecombination
  intro eta heta N
  obtain ⟨Ca, hCa, haux⟩ :=
    mssRecombination_aux_bound D A structured eta heta (N + 1)
  let g0 : MSSAdmissibleGamma :=
    ⟨(1 / 20 : Real), by norm_num, by norm_num⟩
  let E0 : MSSWavefrontKernelData := structured.wavefrontFamily.data g0
  let R0 : MSSWavefrontRawProfileRealization E0 :=
    structured.wavefrontFamily.realization g0
  have hcore0 : E0.toMSSWavefrontCutoffData = D.toMSSWavefrontCutoffData := by
    simpa only [E0] using structured.wavefrontFamily.data_core g0
  obtain ⟨Cv, hCv, hvert⟩ :=
    mssRecombination_outerVertical_bound_of_core D E0 R0 hcore0
  obtain ⟨Cr, hCr, hradial⟩ :=
    (radialTimeLocalization_of_MSSRadialTimeCutoffs D.radialTime)
      (4 : ENNReal) N (by norm_num)
  let Cmain : Real := Cv * Ca
  let C : Real := Cmain + Cr
  have hCmain : 0 < Cmain := by
    dsimp only [Cmain]
    exact mul_pos hCv hCa
  refine ⟨C, add_pos hCmain hCr, ?_⟩
  intro scale hscale f
  have hscale_pos : 0 < scale := by linarith
  have hintegrable : ∀ n ∈ relevantRadialIndexEnumeration scale,
      ∀ (t : Real) (nu : Int), nu ∈ D.angularIndices scale →
        Integrable (fun xi : Euclidean 2 =>
          D.chi scale nu xi * D.radialTime.amplitude (scale⁻¹ • xi) *
            halfWaveMultiplier WaveSign.plus t xi *
              FourierTransform.fourier
                (radialPiece (D.radialTime.radial : Real → Complex) scale n
                  (f : Euclidean 2 → Complex)) xi) volume := by
    intro n hn t nu hnu
    simpa only [hcore0] using
      (mssRecombination_integrable_angularPiece_multiplier E0 R0 scale hscale_pos n nu f t)
  have hchi : ∀ n ∈ relevantRadialIndexEnumeration scale,
      ∀ xi ∈ Function.support (fun xi : Euclidean 2 =>
        D.radialTime.amplitude (scale⁻¹ • xi) *
          FourierTransform.fourier
            (radialPiece (D.radialTime.radial : Real → Complex) scale n
              (f : Euclidean 2 → Complex)) xi),
        ∑ nu ∈ D.angularIndices scale, D.chi scale nu xi = 1 := by
    intro n hn xi hxi
    apply A.partition_on_active_amplitude scale hscale xi
    intro hzero
    exact hxi (by simp [hzero])
  have hconic :=
    conicOperator_eq_verticalRecombined_angularPiece_add_radialTimeResidual_of_sum_eq_one_on_support
      (D.radialTime.vertical : Real → Complex) (D.radialTime.radial : Real → Complex)
      relevantRadialIndexEnumeration (D.angularIndices scale) (D.chi scale) scale
      (D.radialTime.amplitude : Euclidean 2 → Complex) (D.radialTime.time : Real → Complex)
      (f : Euclidean 2 → Complex) hchi hintegrable
  have houterMeas : AEStronglyMeasurable
      (verticalRecombined (D.radialTime.vertical : Real → Complex) scale
        (relevantRadialIndexEnumeration scale)
        (fun n => verticalProjection (D.radialTime.vertical : Real → Complex) scale n
          (fun z => ∑ nu ∈ D.angularIndices scale,
            angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
              (D.chi scale nu) (D.radialTime.time : Real → Complex)
              (radialPiece (D.radialTime.radial : Real → Complex) scale n
                (f : Euclidean 2 → Complex)) z))) volume := by
    simpa only [hcore0] using
      (mssRecombination_aestronglyMeasurable_outerVerticalTerm
        E0 R0 scale hscale_pos f)
  have hresidualMeas :=
    mssRecombination_aestronglyMeasurable_radialTimeResidual
      D.radialTime scale hscale_pos f
  have htriangle :
      eLpNorm
          (conicOperator scale (D.radialTime.amplitude : Euclidean 2 → Complex)
            (D.radialTime.time : Real → Complex) (f : Euclidean 2 → Complex))
          (4 : ENNReal) volume ≤
        eLpNorm
          (verticalRecombined (D.radialTime.vertical : Real → Complex) scale
            (relevantRadialIndexEnumeration scale)
            (fun n => verticalProjection (D.radialTime.vertical : Real → Complex) scale n
              (fun z => ∑ nu ∈ D.angularIndices scale,
                angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
                  (D.chi scale nu) (D.radialTime.time : Real → Complex)
                  (radialPiece (D.radialTime.radial : Real → Complex) scale n
                    (f : Euclidean 2 → Complex)) z)))
          (4 : ENNReal) volume +
        eLpNorm
          (radialTimeResidual (D.radialTime.vertical : Real → Complex)
            (D.radialTime.radial : Real → Complex) relevantRadialIndexEnumeration
            scale (D.radialTime.amplitude : Euclidean 2 → Complex)
            (D.radialTime.time : Real → Complex) (f : Euclidean 2 → Complex))
          (4 : ENNReal) volume := by
    rw [hconic]
    exact eLpNorm_add_le houterMeas hresidualMeas (by norm_num)
  have hfineCoeff :
      ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) *
          ENNReal.ofReal (Ca * scale ^ eta) ≤
        ENNReal.ofReal (C * scale ^ ((1 / 8 : Real) + eta)) := by
    rw [← ENNReal.ofReal_mul
      (mul_nonneg hCv.le (Real.rpow_nonneg hscale_pos.le _))]
    apply ENNReal.ofReal_le_ofReal
    calc
      (Cv * scale ^ (1 / 8 : Real)) * (Ca * scale ^ eta) =
          Cmain * (scale ^ (1 / 8 : Real) * scale ^ eta) := by
            dsimp only [Cmain]
            ring
      _ = Cmain * scale ^ ((1 / 8 : Real) + eta) := by
            rw [← Real.rpow_add hscale_pos]
      _ ≤ C * scale ^ ((1 / 8 : Real) + eta) := by
            apply mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hCr.le)
              (Real.rpow_nonneg hscale_pos.le _)
  have hverticalErrorScalar :=
    mssRecombination_scale_delta_inverse_pow_le hscale
      (by norm_num : (1 / 8 : Real) ≤ 1) N
  have hmainErrorCoeff :
      ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) *
          ENNReal.ofReal (Ca * (scale⁻¹) ^ (N + 1)) ≤
        ENNReal.ofReal (Cmain * (scale⁻¹) ^ N) := by
    rw [← ENNReal.ofReal_mul
      (mul_nonneg hCv.le (Real.rpow_nonneg hscale_pos.le _))]
    apply ENNReal.ofReal_le_ofReal
    calc
      (Cv * scale ^ (1 / 8 : Real)) * (Ca * (scale⁻¹) ^ (N + 1)) =
          Cmain * (scale ^ (1 / 8 : Real) * (scale⁻¹) ^ (N + 1)) := by
            dsimp only [Cmain]
            ring
      _ ≤ Cmain * (scale⁻¹) ^ N :=
        mul_le_mul_of_nonneg_left hverticalErrorScalar hCmain.le
  have herrorCoeff :
      ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) *
          ENNReal.ofReal (Ca * (scale⁻¹) ^ (N + 1)) +
        ENNReal.ofReal (Cr * (scale⁻¹) ^ N) ≤
          ENNReal.ofReal (C * (scale⁻¹) ^ N) := by
    calc
      ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) *
          ENNReal.ofReal (Ca * (scale⁻¹) ^ (N + 1)) +
        ENNReal.ofReal (Cr * (scale⁻¹) ^ N) ≤
          ENNReal.ofReal (Cmain * (scale⁻¹) ^ N) +
            ENNReal.ofReal (Cr * (scale⁻¹) ^ N) :=
              add_le_add hmainErrorCoeff le_rfl
      _ = ENNReal.ofReal (C * (scale⁻¹) ^ N) := by
        rw [← ENNReal.ofReal_add
          (mul_nonneg hCmain.le (pow_nonneg (inv_nonneg.mpr hscale_pos.le) _))
          (mul_nonneg hCr.le (pow_nonneg (inv_nonneg.mpr hscale_pos.le) _))]
        congr 1
        dsimp only [C]
        ring
  have hvertAt := hvert scale hscale f
  have hauxAt := haux scale hscale f
  have hradialAt := hradial scale hscale f
  have hverticalAt :
      eLpNorm
          (verticalRecombined (D.radialTime.vertical : Real → Complex) scale
            (relevantRadialIndexEnumeration scale)
            (fun n => verticalProjection (D.radialTime.vertical : Real → Complex) scale n
              (fun z => ∑ nu ∈ D.angularIndices scale,
                angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
                  (D.chi scale nu) (D.radialTime.time : Real → Complex)
                  (radialPiece (D.radialTime.radial : Real → Complex) scale n
                    (f : Euclidean 2 → Complex)) z)))
          (4 : ENNReal) volume ≤
        ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) *
          (ENNReal.ofReal (Ca * scale ^ eta) *
            eLpNorm
              (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
                (f : Euclidean 2 → Complex))
              (4 : ENNReal) volume +
            ENNReal.ofReal (Ca * (scale⁻¹) ^ (N + 1)) *
              eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume) :=
    calc
      eLpNorm
          (verticalRecombined (D.radialTime.vertical : Real → Complex) scale
            (relevantRadialIndexEnumeration scale)
            (fun n => verticalProjection (D.radialTime.vertical : Real → Complex) scale n
              (fun z => ∑ nu ∈ D.angularIndices scale,
                angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
                  (D.chi scale nu) (D.radialTime.time : Real → Complex)
                  (radialPiece (D.radialTime.radial : Real → Complex) scale n
                    (f : Euclidean 2 → Complex)) z)))
          (4 : ENNReal) volume ≤
        ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) *
          eLpNorm
            (aux_angularRadialRecombinedSquareFunction
              (relevantRadialIndexEnumeration scale) (D.angularIndices scale)
              (fun n nu =>
                mssAngularRadialWave D.toMSSWavefrontCutoffData scale n nu
                  (f : Euclidean 2 → Complex)))
            (4 : ENNReal) volume := hvertAt
      _ = eLpNorm
            (aux_angularRadialRecombinedSquareFunction
              (relevantRadialIndexEnumeration scale) (D.angularIndices scale)
              (fun n nu =>
                mssAngularRadialWave D.toMSSWavefrontCutoffData scale n nu
                  (f : Euclidean 2 → Complex)))
            (4 : ENNReal) volume *
          ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) := by ring
      _ ≤ (ENNReal.ofReal (Ca * scale ^ eta) *
            eLpNorm
              (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
                (f : Euclidean 2 → Complex))
              (4 : ENNReal) volume +
            ENNReal.ofReal (Ca * (scale⁻¹) ^ (N + 1)) *
              eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume) *
          ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) :=
        mul_le_mul_left hauxAt _
      _ = ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) *
          (ENNReal.ofReal (Ca * scale ^ eta) *
            eLpNorm
              (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
                (f : Euclidean 2 → Complex))
              (4 : ENNReal) volume +
            ENNReal.ofReal (Ca * (scale⁻¹) ^ (N + 1)) *
              eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume) := by ring
  calc
    eLpNorm
        (conicOperator scale (D.radialTime.amplitude : Euclidean 2 → Complex)
          (D.radialTime.time : Real → Complex) (f : Euclidean 2 → Complex))
        (4 : ENNReal) volume ≤
      eLpNorm
        (verticalRecombined (D.radialTime.vertical : Real → Complex) scale
          (relevantRadialIndexEnumeration scale)
          (fun n => verticalProjection (D.radialTime.vertical : Real → Complex) scale n
            (fun z => ∑ nu ∈ D.angularIndices scale,
              angularPiece scale (D.radialTime.amplitude : Euclidean 2 → Complex)
                (D.chi scale nu) (D.radialTime.time : Real → Complex)
                (radialPiece (D.radialTime.radial : Real → Complex) scale n
                  (f : Euclidean 2 → Complex)) z)))
        (4 : ENNReal) volume +
      eLpNorm
        (radialTimeResidual (D.radialTime.vertical : Real → Complex)
          (D.radialTime.radial : Real → Complex) relevantRadialIndexEnumeration
          scale (D.radialTime.amplitude : Euclidean 2 → Complex)
          (D.radialTime.time : Real → Complex) (f : Euclidean 2 → Complex))
        (4 : ENNReal) volume := htriangle
    _ ≤ ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) *
          (ENNReal.ofReal (Ca * scale ^ eta) *
            eLpNorm
              (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
                (f : Euclidean 2 → Complex))
              (4 : ENNReal) volume +
            ENNReal.ofReal (Ca * (scale⁻¹) ^ (N + 1)) *
              eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume) +
        ENNReal.ofReal (Cr * (scale⁻¹) ^ N) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume :=
      add_le_add hverticalAt hradialAt
    _ = (ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) *
            ENNReal.ofReal (Ca * scale ^ eta)) *
          eLpNorm
            (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
              (f : Euclidean 2 → Complex))
            (4 : ENNReal) volume +
        (ENNReal.ofReal (Cv * scale ^ (1 / 8 : Real)) *
            ENNReal.ofReal (Ca * (scale⁻¹) ^ (N + 1)) +
          ENNReal.ofReal (Cr * (scale⁻¹) ^ N)) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by ring
    _ ≤ ENNReal.ofReal (C * scale ^ ((1 / 8 : Real) + eta)) *
          eLpNorm
            (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
              (f : Euclidean 2 → Complex))
            (4 : ENNReal) volume +
        ENNReal.ofReal (C * (scale⁻¹) ^ N) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume :=
      add_le_add (mul_le_mul_left hfineCoeff _) (mul_le_mul_left herrorCoeff _)

/-- The repaired structured recombination theorem and the structured fine
square-function estimate give the conic endpoint estimate for one fixed
wave-front datum.  This is the analytic core of the `p = 4` assembly; the
finite coarse angular atlas and sign transport assembled below yield
`p4LocalSmoothing`. -/
theorem mssConicL4Estimate_of_structuredData
    (D : MSSWavefrontKernelData)
    (A : MSSFineAngularData D.toMSSWavefrontCutoffData)
    (structured : MSSStructuredRecombinationData D)
    (uniform : MSSFineSpatialProfileUniformRegularity D)
    (hslab : D.HasLightRayTimeSlabSupport) :
    ∀ eta : Real, 0 < eta → ∃ C : Real, 0 < C ∧
      ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
        eLpNorm
            (conicOperator scale (D.radialTime.amplitude : Euclidean 2 → Complex)
              (D.radialTime.time : Real → Complex) (f : Euclidean 2 → Complex))
            (4 : ENNReal) volume ≤
          ENNReal.ofReal (C * scale ^ ((1 / 8 : Real) + eta)) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
  intro eta heta
  have hetaHalf : 0 < eta / 2 := by linarith
  obtain ⟨Crec, hCrec, hrec⟩ :=
    mssRecombination_of_structuredData D A structured uniform hslab
      (eta / 2) hetaHalf 0
  obtain ⟨Cfine, hCfine, hfine⟩ :=
    mssFineSquareFunctionEstimate_of_canonicalData D A uniform hslab
      (eta / 2) hetaHalf
  let C : Real := Crec * Cfine + Crec
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro scale hscale f
  have hscalePos : 0 < scale := by linarith
  have hscaleNonneg : 0 ≤ scale := hscalePos.le
  have hexponentNonneg : 0 ≤ (1 / 8 : Real) + eta := by linarith
  have hpow : 1 ≤ scale ^ ((1 / 8 : Real) + eta) :=
    Real.one_le_rpow (by linarith) hexponentNonneg
  have hmainA : 0 ≤ Crec * scale ^ ((1 / 8 : Real) + eta / 2) :=
    mul_nonneg hCrec.le (Real.rpow_nonneg hscaleNonneg _)
  have hmainB : 0 ≤ Cfine * scale ^ (eta / 2) :=
    mul_nonneg hCfine.le (Real.rpow_nonneg hscaleNonneg _)
  have hresidual : 0 ≤ Crec * (scale⁻¹) ^ (0 : Nat) :=
    mul_nonneg hCrec.le (pow_nonneg (inv_nonneg.mpr hscaleNonneg) _)
  have hpows :
      scale ^ ((1 / 8 : Real) + eta / 2) * scale ^ (eta / 2) =
        scale ^ ((1 / 8 : Real) + eta) := by
    rw [← Real.rpow_add hscalePos]
    congr 1
    ring
  have hcoeff :
      ENNReal.ofReal (Crec * scale ^ ((1 / 8 : Real) + eta / 2)) *
          ENNReal.ofReal (Cfine * scale ^ (eta / 2)) +
        ENNReal.ofReal (Crec * (scale⁻¹) ^ (0 : Nat)) ≤
          ENNReal.ofReal (C * scale ^ ((1 / 8 : Real) + eta)) := by
    rw [← ENNReal.ofReal_mul hmainA,
      ← ENNReal.ofReal_add (mul_nonneg hmainA hmainB) hresidual]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [C]
    rw [show (Crec * scale ^ ((1 / 8 : Real) + eta / 2)) *
          (Cfine * scale ^ (eta / 2)) =
        (Crec * Cfine) *
          (scale ^ ((1 / 8 : Real) + eta / 2) * scale ^ (eta / 2)) by ring,
      hpows]
    simp only [pow_zero, mul_one]
    have hCrecScale : Crec ≤ Crec * scale ^ ((1 / 8 : Real) + eta) := by
      simpa using mul_le_mul_of_nonneg_left hpow hCrec.le
    calc
      (Crec * Cfine) * scale ^ ((1 / 8 : Real) + eta) + Crec ≤
          (Crec * Cfine) * scale ^ ((1 / 8 : Real) + eta) +
            Crec * scale ^ ((1 / 8 : Real) + eta) :=
        add_le_add_right hCrecScale _
      _ = (Crec * Cfine + Crec) * scale ^ ((1 / 8 : Real) + eta) := by ring
  have hrecAt := hrec scale hscale f
  have hfineAt := hfine scale hscale f
  calc
    eLpNorm
        (conicOperator scale (D.radialTime.amplitude : Euclidean 2 → Complex)
          (D.radialTime.time : Real → Complex) (f : Euclidean 2 → Complex))
        (4 : ENNReal) volume ≤
      ENNReal.ofReal (Crec * scale ^ ((1 / 8 : Real) + eta / 2)) *
          eLpNorm
            (mssFineSquareFunction D.toMSSWavefrontCutoffData scale
              (f : Euclidean 2 → Complex))
            (4 : ENNReal) volume +
        ENNReal.ofReal (Crec * (scale⁻¹) ^ (0 : Nat)) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
      simpa using hrecAt
    _ ≤ ENNReal.ofReal (Crec * scale ^ ((1 / 8 : Real) + eta / 2)) *
          (ENNReal.ofReal (Cfine * scale ^ (eta / 2)) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume) +
        ENNReal.ofReal (Crec * (scale⁻¹) ^ (0 : Nat)) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
      exact add_le_add (mul_le_mul_right hfineAt _) le_rfl
    _ = (ENNReal.ofReal (Crec * scale ^ ((1 / 8 : Real) + eta / 2)) *
          ENNReal.ofReal (Cfine * scale ^ (eta / 2)) +
        ENNReal.ofReal (Crec * (scale⁻¹) ^ (0 : Nat))) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by ring
    _ ≤ ENNReal.ofReal (C * scale ^ ((1 / 8 : Real) + eta)) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume :=
      mul_le_mul_left hcoeff _

/-- One fully structured narrow conic datum, including precisely the
geometric and regularity certificates consumed by the MSS conic estimate.
This package contains no norm estimate: that estimate is supplied by
`mssConicL4Estimate_of_structuredData`. -/
structure MSSStructuredConicDatum where
  D : MSSWavefrontKernelData
  angular : MSSFineAngularData D.toMSSWavefrontCutoffData
  recombination : MSSStructuredRecombinationData D
  uniform : MSSFineSpatialProfileUniformRegularity D
  timeSlab : D.HasLightRayTimeSlabSupport

/-- The conic scale which matches a dyadic band-pass after the latter is
rescaled into the structured annulus `[1/2, 2]`.  The extra factor of two is
forced by the support convention for `dyadicBandpassMultiplier`. -/
def mssP4ConicScale (j : Nat) : Real := (2 : Real) ^ (j + 1)

/-- The unit-annular multiplier used by the endpoint atlas.  It is the
level-zero Littlewood--Paley band-pass pulled back by the factor-two radial
dilation, so its support lies in the structured annulus `[1/2, 2]`. -/
noncomputable def mssP4ScaledBandpassAmplitude (C : lpCutoffs 2) :
    SchwartzMap (Euclidean 2) Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : Real) (by norm_num)))
    (dyadicBandpassMultiplier C.cutoff 0)

theorem mssP4ScaledBandpassAmplitude_apply (C : lpCutoffs 2)
    (xi : Euclidean 2) :
    mssP4ScaledBandpassAmplitude C xi =
      dyadicBandpassMultiplier C.cutoff 0 ((2 : Real) • xi) := by
  change dyadicBandpassMultiplier C.cutoff 0
      ((ContinuousLinearEquiv.smulLeft
        (Units.mk0 (2 : Real) (by norm_num))) xi) = _
  simp

/-- The rescaled level-zero band-pass is supported in the annulus required
by `MSSRadialTimeCutoffs`. -/
theorem mssP4ScaledBandpassAmplitude_support_annulus (C : lpCutoffs 2)
    {xi : Euclidean 2}
    (hxi : xi ∈ Function.support
      (mssP4ScaledBandpassAmplitude C : Euclidean 2 → Complex)) :
    ‖xi‖ ∈ Icc (1 / 2 : Real) 2 := by
  have hnonzero : dyadicBandpassMultiplier C.cutoff 0 ((2 : Real) • xi) ≠ 0 := by
    have hxi' : mssP4ScaledBandpassAmplitude C xi ≠ 0 :=
      Function.mem_support.mp hxi
    rwa [mssP4ScaledBandpassAmplitude_apply] at hxi'
  have hlo : 1 < ‖(2 : Real) • xi‖ := by
    apply lt_of_not_ge
    intro h
    apply hnonzero
    exact dyadicBandpass_eq_zero_of_norm_le C (j := 0) (by simpa using h)
  have hhi : ‖(2 : Real) • xi‖ < 4 := by
    apply lt_of_not_ge
    intro h
    apply hnonzero
    apply dyadicBandpass_eq_zero_of_le_norm C (j := 0)
    norm_num at h ⊢
    exact h
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)] at hlo hhi
  constructor <;> nlinarith [norm_nonneg xi]

/-- The rescaled endpoint amplitude remains compactly supported.  This is
the compactness certificate required when it is installed as the amplitude
field of `MSSRadialTimeCutoffs`. -/
theorem mssP4ScaledBandpassAmplitude_compact (C : lpCutoffs 2) :
    HasCompactSupport
      (mssP4ScaledBandpassAmplitude C : Euclidean 2 → Complex) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean 2) 2)
  intro xi hxi
  have hxiNorm : 2 < ‖xi‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hxi
    exact lt_of_not_ge hxi
  rw [mssP4ScaledBandpassAmplitude_apply]
  apply dyadicBandpass_eq_zero_of_le_norm C (j := 0)
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  norm_num
  linarith

/-- The fixed radial cutoff used in the endpoint atlas.  Its inner radius
is the overlap radius in the MSS radial partition, while its outer radius
is strictly smaller than three. -/
noncomputable def mssCanonicalRadialBump : ContDiffBump (0 : Real) :=
  ⟨(9 : Real) / 4, 11 / 4, by norm_num, by norm_num⟩

/-- The canonical radial cutoff, packaged as a Schwartz function. -/
noncomputable def mssCanonicalRadial : SchwartzMap Real Complex := by
  let raw : Real → Complex := fun s => (mssCanonicalRadialBump s : Real)
  have hcompact : HasCompactSupport raw := by
    change HasCompactSupport
      (Complex.ofRealCLM ∘ (mssCanonicalRadialBump : Real → Real))
    exact mssCanonicalRadialBump.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff Real (⊤ : ℕ∞) raw := by
    change ContDiff Real (⊤ : ℕ∞)
      (Complex.ofRealCLM ∘ (mssCanonicalRadialBump : Real → Real))
    exact Complex.ofRealCLM.contDiff.comp mssCanonicalRadialBump.contDiff
  exact hcompact.toSchwartzMap hsmooth

theorem mssCanonicalRadial_apply (s : Real) :
    mssCanonicalRadial s = (mssCanonicalRadialBump s : Real) := by
  rfl

theorem mssCanonicalRadial_support (s : Real)
    (hs : mssCanonicalRadial s ≠ 0) :
    |s| < 11 / 4 := by
  have hs' : mssCanonicalRadialBump s ≠ 0 := by
    rw [mssCanonicalRadial_apply] at hs
    exact_mod_cast hs
  apply lt_of_not_ge
  intro h
  apply hs'
  apply mssCanonicalRadialBump.zero_of_le_dist
  simpa [mssCanonicalRadialBump, Real.dist_eq, dist_zero_right,
    Real.norm_eq_abs] using h

theorem mssCanonicalRadial_one (s : Real) (hs : |s| ≤ 9 / 4) :
    mssCanonicalRadial s = 1 := by
  rw [mssCanonicalRadial_apply]
  have hmem : s ∈ Metric.closedBall (0 : Real) mssCanonicalRadialBump.rIn := by
    simpa [mssCanonicalRadialBump, Metric.mem_closedBall, Real.dist_eq,
      dist_zero_right, Real.norm_eq_abs] using hs
  rw [mssCanonicalRadialBump.one_of_mem_closedBall hmem]
  norm_num

/-- A compact time cutoff which is one on the local smoothing slab and is
supported strictly inside the larger light-ray time interval. -/
noncomputable def mssCanonicalTimeBump : ContDiffBump (3 / 2 : Real) :=
  ⟨(1 : Real) / 2, 3 / 4, by norm_num, by norm_num⟩

/-- The canonical compact physical-time cutoff as a Schwartz function. -/
noncomputable def mssCanonicalTime : SchwartzMap Real Complex := by
  let raw : Real → Complex := fun t => (mssCanonicalTimeBump t : Real)
  have hcompact : HasCompactSupport raw := by
    change HasCompactSupport
      (Complex.ofRealCLM ∘ (mssCanonicalTimeBump : Real → Real))
    exact mssCanonicalTimeBump.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff Real (⊤ : ℕ∞) raw := by
    change ContDiff Real (⊤ : ℕ∞)
      (Complex.ofRealCLM ∘ (mssCanonicalTimeBump : Real → Real))
    exact Complex.ofRealCLM.contDiff.comp mssCanonicalTimeBump.contDiff
  exact hcompact.toSchwartzMap hsmooth

theorem mssCanonicalTime_apply (t : Real) :
    mssCanonicalTime t = (mssCanonicalTimeBump t : Real) := by
  rfl

theorem mssCanonicalTime_compact :
    HasCompactSupport (mssCanonicalTime : Real → Complex) := by
  change HasCompactSupport
    (Complex.ofRealCLM ∘ (mssCanonicalTimeBump : Real → Real))
  exact mssCanonicalTimeBump.hasCompactSupport.comp_left (by rfl)

theorem mssCanonicalTime_one (t : Real) (ht : t ∈ Icc (1 : Real) 2) :
    mssCanonicalTime t = 1 := by
  rw [mssCanonicalTime_apply]
  have hmem : t ∈ Metric.closedBall (3 / 2 : Real) mssCanonicalTimeBump.rIn := by
    change |t - 3 / 2| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  rw [mssCanonicalTimeBump.one_of_mem_closedBall hmem]
  norm_num

theorem mssCanonicalTime_support_lightRayTimeInterval :
    Function.support (mssCanonicalTime : Real → Complex) ⊆ lightRayTimeInterval := by
  intro t ht
  have ht0 : mssCanonicalTime t ≠ 0 := Function.mem_support.mp ht
  have ht' : mssCanonicalTimeBump t ≠ 0 := by
    intro hzero
    apply ht0
    rw [mssCanonicalTime_apply]
    exact_mod_cast hzero
  have hdist : dist t (3 / 2 : Real) < 3 / 4 := by
    apply lt_of_not_ge
    intro h
    exact ht' (mssCanonicalTimeBump.zero_of_le_dist h)
  rw [Real.dist_eq, abs_lt] at hdist
  rw [mem_lightRayTimeInterval_iff]
  constructor <;> linarith

/-- A compact smooth real cutoff equal to one on the structured annulus.
Multiplying it by the norm gives a globally Schwartz smooth extension of the
radial phase. -/
noncomputable def mssAnnularNormCutoff : SchwartzMap (Euclidean 2) Real :=
  (Auto.Spherical.MSSKakeya.hasCompactSupport_sectorAnnularCutoff).toSchwartzMap
    Auto.Spherical.MSSKakeya.contDiff_sectorAnnularCutoff

theorem mssAnnularNormCutoff_apply (xi : Euclidean 2) :
    mssAnnularNormCutoff xi = Auto.Spherical.MSSKakeya.sectorAnnularCutoff xi := by
  rfl

theorem mssAnnularNormCutoff_compact :
    HasCompactSupport (mssAnnularNormCutoff : Euclidean 2 → Real) := by
  change HasCompactSupport Auto.Spherical.MSSKakeya.sectorAnnularCutoff
  exact Auto.Spherical.MSSKakeya.hasCompactSupport_sectorAnnularCutoff

private theorem mssAnnularNormCutoff_eq_zero_near_zero
    (xi : Euclidean 2) (hxi : ‖xi‖ < 1 / 4) :
    mssAnnularNormCutoff xi = 0 := by
  rw [mssAnnularNormCutoff_apply]
  exact Auto.Spherical.MSSKakeya.sectorAnnularCutoff_eq_zero_of_norm_le_quarter hxi.le

/-- A fixed global Schwartz extension of the norm which agrees with the
literal norm on the entire structured annulus. -/
noncomputable def mssAnnularNormExtension : SchwartzMap (Euclidean 2) Real :=
  smoothAnnularNormExtension mssAnnularNormCutoff mssAnnularNormCutoff_compact
    (1 / 4 : Real) (by norm_num) mssAnnularNormCutoff_eq_zero_near_zero

theorem mssAnnularNormExtension_eq_norm {xi : Euclidean 2}
    (hlo : 1 / 2 ≤ ‖xi‖) (hhi : ‖xi‖ ≤ 2) :
    mssAnnularNormExtension xi = ‖xi‖ := by
  apply smoothAnnularNormExtension_eq_norm_of_eq_one
    mssAnnularNormCutoff mssAnnularNormCutoff_compact (1 / 4 : Real)
    (by norm_num) mssAnnularNormCutoff_eq_zero_near_zero xi
  rw [mssAnnularNormCutoff_apply]
  exact Auto.Spherical.MSSKakeya.sectorAnnularCutoff_eq_one hlo hhi

/-- A single smooth sine transition gives a compactly supported square
partition of unity under integer translation.  On adjacent unit intervals it
is respectively a sine and a complementary cosine. -/
private noncomputable def mssCanonicalVerticalReal (s : Real) : Real :=
  Real.sin ((Real.pi / 2) *
    (Real.smoothTransition (s + 1) - Real.smoothTransition s))

private theorem mssCanonicalVerticalReal_contDiff :
    ContDiff Real (⊤ : ℕ∞) mssCanonicalVerticalReal := by
  unfold mssCanonicalVerticalReal
  apply Real.contDiff_sin.comp
  apply contDiff_const.mul
  exact (Real.smoothTransition.contDiff.comp
    (contDiff_id.add contDiff_const)).sub Real.smoothTransition.contDiff

private theorem mssCanonicalVerticalReal_zero_left {s : Real} (hs : s ≤ -1) :
    mssCanonicalVerticalReal s = 0 := by
  unfold mssCanonicalVerticalReal
  have hplus : Real.smoothTransition (s + 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hself : Real.smoothTransition s = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [hplus, hself]
  norm_num

private theorem mssCanonicalVerticalReal_zero_right {s : Real} (hs : 1 ≤ s) :
    mssCanonicalVerticalReal s = 0 := by
  unfold mssCanonicalVerticalReal
  have hplus : Real.smoothTransition (s + 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hself : Real.smoothTransition s = 1 :=
    Real.smoothTransition.one_of_one_le hs
  rw [hplus, hself]
  norm_num

private theorem mssCanonicalVerticalReal_support_subset :
    Function.support mssCanonicalVerticalReal ⊆ Icc (-1 : Real) 1 := by
  intro s hs
  constructor
  · by_contra h
    have h' : s ≤ -1 := by linarith
    exact hs (mssCanonicalVerticalReal_zero_left h')
  · by_contra h
    have h' : 1 ≤ s := by linarith
    exact hs (mssCanonicalVerticalReal_zero_right h')

private theorem mssCanonicalVerticalReal_compact :
    HasCompactSupport mssCanonicalVerticalReal := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-1 : Real) 1))
  exact mssCanonicalVerticalReal_support_subset

/-- The canonical vertical cutoff as a compactly supported Schwartz
function. -/
noncomputable def mssCanonicalVertical : SchwartzMap Real Complex := by
  let raw : Real → Complex := fun s => (mssCanonicalVerticalReal s : Complex)
  have hcompact : HasCompactSupport raw := by
    change HasCompactSupport (Complex.ofRealCLM ∘ mssCanonicalVerticalReal)
    exact mssCanonicalVerticalReal_compact.comp_left (by rfl)
  have hsmooth : ContDiff Real (⊤ : ℕ∞) raw := by
    change ContDiff Real (⊤ : ℕ∞) (Complex.ofRealCLM ∘ mssCanonicalVerticalReal)
    exact Complex.ofRealCLM.contDiff.comp mssCanonicalVerticalReal_contDiff
  exact hcompact.toSchwartzMap hsmooth

private theorem mssCanonicalVertical_apply (s : Real) :
    mssCanonicalVertical s = (mssCanonicalVerticalReal s : Complex) := by
  rfl

theorem mssCanonicalVertical_support (s : Real)
    (hs : mssCanonicalVertical s ≠ 0) :
    |s| < 1 := by
  rw [abs_lt]
  constructor
  · by_contra h
    have h' : s ≤ -1 := by linarith
    apply hs
    rw [mssCanonicalVertical_apply, mssCanonicalVerticalReal_zero_left h']
    norm_num
  · by_contra h
    have h' : 1 ≤ s := by linarith
    apply hs
    rw [mssCanonicalVertical_apply, mssCanonicalVerticalReal_zero_right h']
    norm_num

private theorem mssCanonicalVerticalReal_at_floor_remainder
    {r : Real} (hr0 : 0 ≤ r) :
    mssCanonicalVerticalReal r =
      Real.cos ((Real.pi / 2) * Real.smoothTransition r) := by
  unfold mssCanonicalVerticalReal
  have hT : Real.smoothTransition (r + 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  rw [hT]
  have hphase : (Real.pi / 2) * (1 - Real.smoothTransition r) =
      Real.pi / 2 - (Real.pi / 2) * Real.smoothTransition r := by
    ring
  rw [hphase, Real.sin_pi_div_two_sub]

private theorem mssCanonicalVerticalReal_at_floor_remainder_sub_one
    {r : Real} (hr1 : r < 1) :
    mssCanonicalVerticalReal (r - 1) =
      Real.sin ((Real.pi / 2) * Real.smoothTransition r) := by
  unfold mssCanonicalVerticalReal
  have hzero : Real.smoothTransition (r - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [show r - 1 + 1 = r by ring, hzero]
  simp

/-- The canonical vertical cutoff has the exact squared integer-translate
partition required by the MSS radial-time decomposition. -/
theorem mssCanonicalVertical_square_partition (s : Real) :
    ∑' n : Int, (mssCanonicalVertical (s - n)) ^ 2 = 1 := by
  let k : Int := ⌊s⌋
  let r : Real := s - (k : Real)
  have hfloor : (k : Real) ≤ s := by
    dsimp [k]
    exact Int.floor_le s
  have hfloor_lt : s < (k : Real) + 1 := by
    dsimp [k]
    exact Int.lt_floor_add_one s
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hzero : ∀ n ∉ Finset.Icc k (k + 1),
      (mssCanonicalVertical (s - n)) ^ 2 = 0 := by
    intro n hn
    have hn' : n < k ∨ k + 1 < n := by
      simp only [Finset.mem_Icc] at hn
      omega
    rcases hn' with hn' | hn'
    · have hnkInt : n + 1 ≤ k := by omega
      have hnkCast : ((n + 1 : Int) : Real) ≤ (k : Real) := by
        exact_mod_cast hnkInt
      have harg : 1 ≤ s - (n : Real) := by
        push_cast at hnkCast
        linarith
      have hv : mssCanonicalVertical (s - (n : Real)) = 0 := by
        rw [mssCanonicalVertical_apply,
          mssCanonicalVerticalReal_zero_right harg]
        norm_num
      simp [hv]
    · have hknInt : k + 2 ≤ n := by omega
      have hknCast : ((k + 2 : Int) : Real) ≤ (n : Real) := by
        exact_mod_cast hknInt
      have harg : s - (n : Real) ≤ -1 := by
        push_cast at hknCast
        linarith
      have hv : mssCanonicalVertical (s - (n : Real)) = 0 := by
        rw [mssCanonicalVertical_apply,
          mssCanonicalVerticalReal_zero_left harg]
        norm_num
      simp [hv]
  have hIcc : Finset.Icc k (k + 1) = {k, k + 1} := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hleft : mssCanonicalVertical (s - (k : Real)) =
      (Real.cos ((Real.pi / 2) * Real.smoothTransition r) : Complex) := by
    change (mssCanonicalVerticalReal (s - (k : Real)) : Complex) = _
    rw [show s - (k : Real) = r by rfl,
      mssCanonicalVerticalReal_at_floor_remainder hr0]
  have hright : mssCanonicalVertical (s - ((k + 1 : Int) : Real)) =
      (Real.sin ((Real.pi / 2) * Real.smoothTransition r) : Complex) := by
    have hshift : s - ((k + 1 : Int) : Real) = r - 1 := by
      dsimp [r]
      push_cast
      ring
    change (mssCanonicalVerticalReal
      (s - ((k + 1 : Int) : Real)) : Complex) = _
    rw [hshift, mssCanonicalVerticalReal_at_floor_remainder_sub_one hr1]
  calc
    ∑' n : Int, (mssCanonicalVertical (s - n)) ^ 2 =
        ∑ n ∈ Finset.Icc k (k + 1), (mssCanonicalVertical (s - n)) ^ 2 :=
      tsum_eq_sum hzero
    _ = (Real.cos ((Real.pi / 2) * Real.smoothTransition r) : Complex) ^ 2 +
          (Real.sin ((Real.pi / 2) * Real.smoothTransition r) : Complex) ^ 2 := by
      have hright' : mssCanonicalVertical (s - ((k : Real) + 1)) =
          (Real.sin ((Real.pi / 2) * Real.smoothTransition r) : Complex) := by
        convert hright using 1
        push_cast
        ring
      rw [hIcc]
      simp [hleft, hright']
    _ = 1 := by
      norm_cast
      exact Real.cos_sq_add_sin_sq _

/-- Install any compact amplitude supported in the structured unit annulus
into the fixed radial--time cutoff package.  All auxiliary cutoffs are now
concrete; only the amplitude varies from one coarse sector to another. -/
noncomputable def mssRadialTimeCutoffsOfAnnular
    (a : SchwartzMap (Euclidean 2) Complex)
    (ha : HasCompactSupport (a : Euclidean 2 → Complex))
    (hann : ∀ xi ∈ Function.support (a : Euclidean 2 → Complex),
      ‖xi‖ ∈ Icc (1 / 2 : Real) 2) : MSSRadialTimeCutoffs where
  vertical := mssCanonicalVertical
  radial := mssCanonicalRadial
  amplitude := a
  time := mssCanonicalTime
  normalExtension := mssAnnularNormExtension
  amplitude_compact := ha
  amplitude_support_annulus := hann
  normalExtension_eq_norm_on_amplitude := by
    intro xi hxi
    exact mssAnnularNormExtension_eq_norm (hann xi hxi).1 (hann xi hxi).2
  time_compact := mssCanonicalTime_compact
  time_one_on_unit_slab := mssCanonicalTime_one
  vertical_support := mssCanonicalVertical_support
  vertical_square_partition := mssCanonicalVertical_square_partition
  radial_support := mssCanonicalRadial_support
  radial_one := mssCanonicalRadial_one

/-- The level-zero band-pass, normalized to the structured annulus, has its
fully concrete radial--time data package. -/
noncomputable def mssP4RadialTimeCutoffs (C : lpCutoffs 2) :
    MSSRadialTimeCutoffs :=
  mssRadialTimeCutoffsOfAnnular (mssP4ScaledBandpassAmplitude C)
    (mssP4ScaledBandpassAmplitude_compact C)
    (fun xi hxi => mssP4ScaledBandpassAmplitude_support_annulus C hxi)

/-- The factor-two rescaled annular multiplier at scale `2^(j+1)` is
exactly the `j`th Littlewood--Paley band-pass.  This is the normalization
bridge required before a structured conic datum, whose amplitude lives in
`[1/2,2]`, can reconstruct the dyadic half-wave. -/
theorem conicOperator_eq_dyadicHalfWaveSpaceTime_plus_shifted
    (C : lpCutoffs 2) (vartheta : Real → Complex) (j : Nat)
    (f : SchwartzMap (Euclidean 2) Complex) (z : WaveSpaceTime)
    (hvartheta : vartheta z.2 = 1) :
    conicOperator ((2 : Real) ^ (j + 1))
        (mssP4ScaledBandpassAmplitude C : Euclidean 2 → Complex) vartheta
        (f : Euclidean 2 → Complex) z =
      dyadicHalfWaveSpaceTime C.cutoff WaveSign.plus j f z := by
  rw [conicOperator, dyadicHalfWaveSpaceTime, dyadicHalfWave, hvartheta, one_mul]
  apply congrArg (fun g : Euclidean 2 → Complex =>
    FourierTransformInv.fourierInv g z.1)
  funext xi
  rw [mssP4ScaledBandpassAmplitude_apply]
  change dyadicBandpassMultiplier C.cutoff 0
      ((2 : Real) • (((2 : Real) ^ (j + 1))⁻¹ • xi)) *
      halfWaveMultiplier WaveSign.plus z.2 xi *
        FourierTransform.fourier (f : Euclidean 2 → Complex) xi =
      halfWaveMultiplier WaveSign.plus z.2 xi *
        dyadicBandpassMultiplier C.cutoff j xi *
          FourierTransform.fourier (f : Euclidean 2 → Complex) xi
  have hscalar : ((2 : Real) ^ (j + 1))⁻¹ =
      (2 : Real)⁻¹ * ((2 : Real) ^ j)⁻¹ := by
    rw [pow_succ, mul_inv_rev]
  have hscale : (2 : Real) • (((2 : Real) ^ (j + 1))⁻¹ • xi) =
      ((2 : Real) ^ j)⁻¹ • xi := by
    rw [smul_smul, hscalar, ← mul_assoc]
    norm_num
  rw [hscale, ← dyadicBandpassMultiplier_eq_levelZero_scaled C j xi]
  ring

/-- The shifted half-wave identity written with the endpoint scale
abbreviation. -/
theorem conicOperator_eq_dyadicHalfWaveSpaceTime_plus_mssP4ConicScale
    (C : lpCutoffs 2) (vartheta : Real → Complex) (j : Nat)
    (f : SchwartzMap (Euclidean 2) Complex) (z : WaveSpaceTime)
    (hvartheta : vartheta z.2 = 1) :
    conicOperator (mssP4ConicScale j)
        (mssP4ScaledBandpassAmplitude C : Euclidean 2 → Complex) vartheta
        (f : Euclidean 2 → Complex) z =
      dyadicHalfWaveSpaceTime C.cutoff WaveSign.plus j f z := by
  simpa only [mssP4ConicScale] using
    conicOperator_eq_dyadicHalfWaveSpaceTime_plus_shifted C vartheta j f z hvartheta

/-- The innermost member of a three-level chart carrier.  It vanishes through
the boundary `projection ≤ 3/16` and is one from `projection = 1/4` onward.
The resulting four ordered weights still cover the unit annulus, while their
strict buffer permits genuine angular cutoffs and enlarged angular cutoffs
later in the MSS packet construction. -/
private def mssP4SourceChartBump (q : Fin 4) (xi : Euclidean 2) : Real :=
  Real.smoothTransition
    (16 * Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi - 3)

private theorem mssP4SourceChartBump_contDiff (q : Fin 4) :
    ContDiff Real (⊤ : ℕ∞) (mssP4SourceChartBump q) := by
  unfold mssP4SourceChartBump
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul
      (Auto.Spherical.MSSKakeya.contDiff_sectorProjection
        (Auto.Spherical.MSSKakeya.chartSectorIndex q))).sub contDiff_const)

private theorem mssP4SourceChartBump_eq_one_of_quarter_le_projection
    {q : Fin 4} {xi : Euclidean 2}
    (h : 1 / 4 ≤ Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi) :
    mssP4SourceChartBump q xi = 1 := by
  unfold mssP4SourceChartBump
  apply Real.smoothTransition.one_of_one_le
  linarith

private theorem mssP4SourceChartBump_ne_zero_imp_three_sixteenths_lt_projection
    {q : Fin 4} {xi : Euclidean 2}
    (h : mssP4SourceChartBump q xi ≠ 0) :
    3 / 16 < Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi := by
  apply lt_of_not_ge
  intro hle
  apply h
  unfold mssP4SourceChartBump
  apply Real.smoothTransition.zero_of_nonpos
  linarith

/-- The ordered source weights use the buffered source bumps rather than the
unbuffered four-chart weights. -/
private def mssP4SourceChartOrderedWeight (q : Fin 4) (xi : Euclidean 2) : Real :=
  if q = 0 then mssP4SourceChartBump 0 xi else
  if q = 1 then (1 - mssP4SourceChartBump 0 xi) * mssP4SourceChartBump 1 xi else
  if q = 2 then (1 - mssP4SourceChartBump 0 xi) *
      (1 - mssP4SourceChartBump 1 xi) * mssP4SourceChartBump 2 xi else
    (1 - mssP4SourceChartBump 0 xi) * (1 - mssP4SourceChartBump 1 xi) *
      (1 - mssP4SourceChartBump 2 xi) * mssP4SourceChartBump 3 xi

private theorem mssP4SourceChartOrderedWeight_contDiff (q : Fin 4) :
    ContDiff Real (⊤ : ℕ∞) (mssP4SourceChartOrderedWeight q) := by
  fin_cases q <;>
    simp [mssP4SourceChartOrderedWeight] <;>
    first
    | exact mssP4SourceChartBump_contDiff 0
    | exact (contDiff_const.sub (mssP4SourceChartBump_contDiff 0)).mul
        (mssP4SourceChartBump_contDiff 1)
    | exact ((contDiff_const.sub (mssP4SourceChartBump_contDiff 0)).mul
        (contDiff_const.sub (mssP4SourceChartBump_contDiff 1))).mul
          (mssP4SourceChartBump_contDiff 2)
    | exact (((contDiff_const.sub (mssP4SourceChartBump_contDiff 0)).mul
        (contDiff_const.sub (mssP4SourceChartBump_contDiff 1))).mul
          (contDiff_const.sub (mssP4SourceChartBump_contDiff 2))).mul
            (mssP4SourceChartBump_contDiff 3)

private theorem mssP4SourceChartOrderedWeight_eq_zero_of_bump_eq_zero
    (q : Fin 4) (xi : Euclidean 2)
    (h : mssP4SourceChartBump q xi = 0) :
    mssP4SourceChartOrderedWeight q xi = 0 := by
  fin_cases q <;> simp_all [mssP4SourceChartOrderedWeight]

private theorem mssP4SourceChartOrderedWeight_ne_zero_imp_bump_ne_zero
    {q : Fin 4} {xi : Euclidean 2}
    (h : mssP4SourceChartOrderedWeight q xi ≠ 0) :
    mssP4SourceChartBump q xi ≠ 0 := by
  intro hz
  exact h (mssP4SourceChartOrderedWeight_eq_zero_of_bump_eq_zero q xi hz)

private theorem sum_mssP4SourceChartOrderedWeight_eq_one_sub_product
    (xi : Euclidean 2) :
    ∑ q : Fin 4, mssP4SourceChartOrderedWeight q xi =
      1 - (1 - mssP4SourceChartBump 0 xi) *
        (1 - mssP4SourceChartBump 1 xi) *
        (1 - mssP4SourceChartBump 2 xi) *
        (1 - mssP4SourceChartBump 3 xi) := by
  simp [Fin.sum_univ_succ, mssP4SourceChartOrderedWeight]
  ring

private theorem sum_mssP4SourceChartOrderedWeight_eq_one_of_exists_bump_eq_one
    (xi : Euclidean 2)
    (h : ∃ q : Fin 4, mssP4SourceChartBump q xi = 1) :
    ∑ q : Fin 4, mssP4SourceChartOrderedWeight q xi = 1 := by
  rcases h with ⟨q, hq⟩
  rw [sum_mssP4SourceChartOrderedWeight_eq_one_sub_product]
  fin_cases q <;> simp_all

private theorem exists_mssP4SourceChartBump_eq_one_of_norm_half_le
    (xi : Euclidean 2) (hnorm : 1 / 2 ≤ ‖xi‖) :
    ∃ q : Fin 4, mssP4SourceChartBump q xi = 1 := by
  rcases Auto.Spherical.MSSKakeya.exists_sectorProjection_quarter_le_of_norm_half_le
    xi hnorm with ⟨q, hq⟩
  rcases q with ⟨b, k⟩
  cases b <;> fin_cases k
  · refine ⟨1, ?_⟩
    exact mssP4SourceChartBump_eq_one_of_quarter_le_projection
      (q := (1 : Fin 4)) (xi := xi) (by simpa using hq)
  · refine ⟨3, ?_⟩
    exact mssP4SourceChartBump_eq_one_of_quarter_le_projection
      (q := (3 : Fin 4)) (xi := xi) (by simpa using hq)
  · refine ⟨0, ?_⟩
    exact mssP4SourceChartBump_eq_one_of_quarter_le_projection
      (q := (0 : Fin 4)) (xi := xi) (by simpa using hq)
  · refine ⟨2, ?_⟩
    exact mssP4SourceChartBump_eq_one_of_quarter_le_projection
      (q := (2 : Fin 4)) (xi := xi) (by simpa using hq)

/-- The compact annular source multiplier for a buffered coarse chart. -/
private noncomputable def mssP4SourceChartMultiplier (q : Fin 4)
    (xi : Euclidean 2) : Complex :=
  (Auto.Spherical.MSSKakeya.sectorAnnularCutoff xi : Complex) *
    (mssP4SourceChartOrderedWeight q xi : Complex)

private theorem mssP4SourceChartMultiplier_contDiff (q : Fin 4) :
    ContDiff Real (⊤ : ℕ∞) (mssP4SourceChartMultiplier q) := by
  unfold mssP4SourceChartMultiplier
  exact Auto.Spherical.MSSKakeya.contDiff_sectorAnnularCutoff_complex.mul
    (Complex.ofRealCLM.contDiff.comp (mssP4SourceChartOrderedWeight_contDiff q))

private theorem mssP4SourceChartMultiplier_compact (q : Fin 4) :
    HasCompactSupport (mssP4SourceChartMultiplier q) := by
  unfold mssP4SourceChartMultiplier
  exact Auto.Spherical.MSSKakeya.hasCompactSupport_sectorAnnularCutoff_complex.mul_right

private theorem sum_mssP4SourceChartMultiplier_eq_one_on_unit_annulus
    {xi : Euclidean 2} (hxi : ‖xi‖ ∈ Icc (1 / 2 : Real) 2) :
    ∑ q : Fin 4, mssP4SourceChartMultiplier q xi = 1 := by
  unfold mssP4SourceChartMultiplier
  rw [← Finset.mul_sum]
  have hweights : ∑ q : Fin 4, mssP4SourceChartOrderedWeight q xi = 1 :=
    sum_mssP4SourceChartOrderedWeight_eq_one_of_exists_bump_eq_one xi
      (exists_mssP4SourceChartBump_eq_one_of_norm_half_le xi hxi.1)
  have hcut : (Auto.Spherical.MSSKakeya.sectorAnnularCutoff xi : Complex) = 1 := by
    norm_cast
    exact Auto.Spherical.MSSKakeya.sectorAnnularCutoff_eq_one hxi.1 hxi.2
  have hweightsC : ∑ q : Fin 4,
      (mssP4SourceChartOrderedWeight q xi : Complex) = 1 := by
    exact_mod_cast hweights
  rw [hcut, hweightsC, mul_one]

/-- The middle chart carrier equals one on every nonzero source-chart weight.
Its support remains in the region where the chart's global angle is the
literal polar angle. -/
private def mssP4ChiChartGate (q : Fin 4) (xi : Euclidean 2) : Real :=
  Real.smoothTransition
    (16 * Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi - 2)

private theorem mssP4ChiChartGate_contDiff (q : Fin 4) :
    ContDiff Real (⊤ : ℕ∞) (mssP4ChiChartGate q) := by
  unfold mssP4ChiChartGate
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul
      (Auto.Spherical.MSSKakeya.contDiff_sectorProjection
        (Auto.Spherical.MSSKakeya.chartSectorIndex q))).sub contDiff_const)

private theorem mssP4ChiChartGate_eq_one_of_source_weight_ne_zero
    {q : Fin 4} {xi : Euclidean 2}
    (h : mssP4SourceChartOrderedWeight q xi ≠ 0) :
    mssP4ChiChartGate q xi = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hsource : 3 / 16 < Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi :=
    mssP4SourceChartBump_ne_zero_imp_three_sixteenths_lt_projection
      (mssP4SourceChartOrderedWeight_ne_zero_imp_bump_ne_zero h)
  linarith

private theorem mssP4ChiChartGate_ne_zero_imp_eighth_lt_projection
    {q : Fin 4} {xi : Euclidean 2}
    (h : mssP4ChiChartGate q xi ≠ 0) :
    1 / 8 < Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi := by
  apply lt_of_not_ge
  intro hle
  apply h
  unfold mssP4ChiChartGate
  apply Real.smoothTransition.zero_of_nonpos
  linarith

/-- The outer carrier is one on the support of the middle carrier.  The
`1/16` buffer is enough to identify the regularized chart angle with the
literal polar angle. -/
private def mssP4TildeChiChartGate (q : Fin 4) (xi : Euclidean 2) : Real :=
  Real.smoothTransition
    (16 * Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi - 1)

private theorem mssP4TildeChiChartGate_contDiff (q : Fin 4) :
    ContDiff Real (⊤ : ℕ∞) (mssP4TildeChiChartGate q) := by
  unfold mssP4TildeChiChartGate
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul
      (Auto.Spherical.MSSKakeya.contDiff_sectorProjection
        (Auto.Spherical.MSSKakeya.chartSectorIndex q))).sub contDiff_const)

private theorem mssP4TildeChiChartGate_eq_one_of_chi_gate_ne_zero
    {q : Fin 4} {xi : Euclidean 2}
    (h : mssP4ChiChartGate q xi ≠ 0) :
    mssP4TildeChiChartGate q xi = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hchi : 1 / 8 < Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi :=
    mssP4ChiChartGate_ne_zero_imp_eighth_lt_projection h
  linarith

private theorem mssP4TildeChiChartGate_ne_zero_imp_sixteenth_lt_projection
    {q : Fin 4} {xi : Euclidean 2}
    (h : mssP4TildeChiChartGate q xi ≠ 0) :
    1 / 16 < Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi := by
  apply lt_of_not_ge
  intro hle
  apply h
  unfold mssP4TildeChiChartGate
  apply Real.smoothTransition.zero_of_nonpos
  linarith

/-- A finite smooth lattice partition in the globally smooth angular
coordinate of one of the four annular charts.  The range `Fin 193` is the
explicit interval `[-96,96]`; the global chart angle lies in `(-4,6)`, so
this range contains every active integer translate after multiplication by
`16`. -/
def mssP4AngleLattice (q : Fin 4) (r : Fin 193) (xi : Euclidean 2) : Real :=
  mssUnitLatticeTransitionPiece
    (16 * Auto.Spherical.MSSKakeya.globalSectorAngle
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi + 96 - (r.val : Real))

theorem mssP4AngleLattice_contDiff (q : Fin 4) (r : Fin 193) :
    ContDiff Real (⊤ : ℕ∞) (mssP4AngleLattice q r) := by
  unfold mssP4AngleLattice
  apply mssUnitLatticeTransitionPiece_contDiff.comp
  exact ((contDiff_const.mul
    (Auto.Spherical.MSSKakeya.contDiff_globalSectorAngle
      (Auto.Spherical.MSSKakeya.chartSectorIndex q))).add contDiff_const).sub
        contDiff_const

/-- The finite angular lattice exactly synthesizes one in every chart. -/
theorem sum_mssP4AngleLattice (q : Fin 4) (xi : Euclidean 2) :
    ∑ r : Fin 193, mssP4AngleLattice q r xi = 1 := by
  let θ : Real := Auto.Spherical.MSSKakeya.globalSectorAngle
    (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi
  have hθlo : -4 < θ := by
    dsimp only [θ]
    exact Auto.Spherical.MSSKakeya.neg_four_lt_globalSectorAngle
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi
  have hθhi : θ < 6 := by
    dsimp only [θ]
    exact Auto.Spherical.MSSKakeya.globalSectorAngle_lt_six
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi
  have habs : |16 * θ| ≤ (96 : Real) := by
    rw [abs_le]
    constructor <;> nlinarith
  let F : Nat → Real := fun r =>
    mssP4AngleLattice q ⟨r % 193, Nat.mod_lt _ (by norm_num)⟩ xi
  calc
    ∑ r : Fin 193, mssP4AngleLattice q r xi = ∑ r : Fin 193, F r := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [F, Nat.mod_eq_of_lt r.isLt]
    _ = ∑ r ∈ Finset.range 193, F r := Fin.sum_univ_eq_sum_range F 193
    _ = ∑ r ∈ Finset.range 193,
        mssUnitLatticeTransitionPiece (16 * θ + 96 - (r : Real)) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [F, Nat.mod_eq_of_lt (Finset.mem_range.mp hr),
        mssP4AngleLattice, θ]
    _ = 1 := by
      simpa using
        (mss_finite_unitLatticeTransition_partition (t := 16 * θ) 96 habs)

theorem sum_mssP4AngleLattice_complex (q : Fin 4) (xi : Euclidean 2) :
    ∑ r : Fin 193, (mssP4AngleLattice q r xi : Complex) = 1 := by
  exact_mod_cast sum_mssP4AngleLattice q xi

/-- The angular center of one of the finite coarse lattice pieces. -/
private def mssP4CoarseAngleCenter (r : Fin 193) : Real :=
  ((r.val : Real) - 96) / 16

private theorem mssP4AngleLattice_ne_zero_imp_abs_sub_center_le
    {q : Fin 4} {r : Fin 193} {xi : Euclidean 2}
    (h : mssP4AngleLattice q r xi ≠ 0) :
    |Auto.Spherical.MSSKakeya.globalSectorAngle
        (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi -
        mssP4CoarseAngleCenter r| ≤ 1 / 16 := by
  have hsupport :
      16 * Auto.Spherical.MSSKakeya.globalSectorAngle
          (Auto.Spherical.MSSKakeya.chartSectorIndex q) xi + 96 - (r.val : Real) ∈
        Icc (-1 : Real) 1 := by
    apply mssUnitLatticeTransitionPiece_support_subset
    exact Function.mem_support.mpr (by
      simpa only [mssP4AngleLattice] using h)
  unfold mssP4CoarseAngleCenter
  rw [abs_le]
  constructor <;> nlinarith [hsupport.1, hsupport.2]

/-- The regularized angular coordinate is the literal polar coordinate on
the slightly enlarged chart support.  The public chart lemma uses the more
conservative `1/8` threshold; the denominator definition already gives this
at `1/16`. -/
private theorem mssP4_globalSectorAngle_eq_sectorAngle_of_sixteenth_lt_projection
    {q : Auto.Spherical.MSSKakeya.SectorIndex} {xi : Euclidean 2}
    (h : 1 / 16 < Auto.Spherical.MSSKakeya.sectorProjection q xi) :
    Auto.Spherical.MSSKakeya.globalSectorAngle q xi =
      Auto.Spherical.MSSKakeya.sectorAngle q xi := by
  unfold Auto.Spherical.MSSKakeya.globalSectorAngle Auto.Spherical.MSSKakeya.sectorAngle
  rw [Auto.Spherical.MSSKakeya.sectorAngleDenom_eq_self_of_one_sixteenth_le h.le]

private theorem mssP4_polar_of_sixteenth_lt_projection
    {q : Auto.Spherical.MSSKakeya.SectorIndex} {xi : Euclidean 2}
    (h : 1 / 16 < Auto.Spherical.MSSKakeya.sectorProjection q xi) :
    xi = ‖xi‖ • Auto.Spherical.MSSKakeya.circleDirection
      (Auto.Spherical.MSSKakeya.globalSectorAngle q xi) := by
  rw [mssP4_globalSectorAngle_eq_sectorAngle_of_sixteenth_lt_projection h]
  exact Auto.Spherical.MSSKakeya.sectorAngle_polar_of_projection_pos
    (lt_trans (by norm_num) h)

/-- The number of scale-dependent fine angular lattice steps on either side
of a coarse angular center. -/
private def mssP4FineIndexRadius (scale : Real) : Nat :=
  ⌈4 * Real.sqrt scale⌉₊

/-- The active fine angular labels.  Below the MSS scale range they are empty,
which makes all geometric cutoff requirements vacuous there. -/
private def mssP4FineAngularIndices (scale : Real) : Finset Int :=
  if 2 ≤ scale then
    (Finset.range (2 * mssP4FineIndexRadius scale + 1)).map
      ⟨fun k : Nat => (k : Int) - (mssP4FineIndexRadius scale : Int), by
        intro a b hab
        have hab' : (a : Int) = (b : Int) := sub_left_inj.mp hab
        exact_mod_cast hab'⟩
  else ∅

/-- The globally smooth chart angle evaluated at the scale-normalized
frequency variable. -/
private def mssP4FineChartAngle (q : Fin 4) (scale : Real)
    (xi : Euclidean 2) : Real :=
  Auto.Spherical.MSSKakeya.scaledChartAngle scale q xi

/-- The coarse angular lattice coordinate transported to the MSS scale. -/
private def mssP4FineCoarseCoordinate (q : Fin 4) (r : Fin 193)
    (scale : Real) (xi : Euclidean 2) : Real :=
  16 * mssP4FineChartAngle q scale xi + 96 - (r.val : Real)

/-- The natural `sqrt scale` coordinate used for the fine angular lattice. -/
private def mssP4FineCoordinate (q : Fin 4) (r : Fin 193)
    (scale : Real) (xi : Euclidean 2) : Real :=
  4 * Real.sqrt scale * mssP4FineCoarseCoordinate q r scale xi

/-- Fine angular centers at separation `1 / (64 sqrt scale)`. -/
private noncomputable def mssP4FineDirection (r : Fin 193)
    (scale : Real) (nu : Int) : Euclidean 2 :=
  Auto.Spherical.MSSKakeya.circleDirection
    (mssP4CoarseAngleCenter r +
      (nu : Real) / (64 * Real.sqrt scale))

/-- The compact one-dimensional bump which enlarges a unit lattice piece. -/
private noncomputable def mssP4FineOuterLatticeBump : ContDiffBump (0 : Real) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The two radial bumps which enlarge the compact annular factor of a fine
angular cutoff. -/
private noncomputable def mssP4FineOuterRadialBump :
    ContDiffBump (0 : Euclidean 2) :=
  ⟨3, 4, by norm_num, by norm_num⟩

private noncomputable def mssP4FineInnerRadialBump :
    ContDiffBump (0 : Euclidean 2) :=
  ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

/-- The fixed normal cutoff for every narrow endpoint packet.  It is one on
the unit normal window and supported strictly inside the window of radius
two required by the wave-front localization interface. -/
private noncomputable def mssP4NormalBump : ContDiffBump (0 : Real) :=
  ⟨1, 3 / 2, by norm_num, by norm_num⟩

private noncomputable def mssP4Normal : SchwartzMap Real Complex := by
  let raw : Real → Complex := fun s => (mssP4NormalBump s : Real)
  have hcompact : HasCompactSupport raw := by
    change HasCompactSupport (Complex.ofRealCLM ∘ mssP4NormalBump)
    exact mssP4NormalBump.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff Real (⊤ : ℕ∞) raw := by
    change ContDiff Real (⊤ : ℕ∞) (Complex.ofRealCLM ∘ mssP4NormalBump)
    exact Complex.ofRealCLM.contDiff.comp mssP4NormalBump.contDiff
  exact hcompact.toSchwartzMap hsmooth

private theorem mssP4Normal_apply (s : Real) :
    mssP4Normal s = (mssP4NormalBump s : Real) := by
  rfl

private theorem mssP4Normal_support (s : Real) (hs : mssP4Normal s ≠ 0) :
    |s| < 2 := by
  have hs' : mssP4NormalBump s ≠ 0 := by
    rw [mssP4Normal_apply] at hs
    exact Complex.ofReal_ne_zero.mp hs
  apply lt_of_not_ge
  intro h
  apply hs'
  apply mssP4NormalBump.zero_of_le_dist
  simpa only [mssP4NormalBump, Real.dist_eq, dist_zero_right,
    Real.norm_eq_abs] using
    (show 3 / 2 ≤ |s| by linarith)

private theorem mssP4Normal_one_on_unit (s : Real) (hs : |s| ≤ 1) :
    mssP4Normal s = 1 := by
  rw [mssP4Normal_apply]
  have hmem : s ∈ Metric.closedBall (0 : Real) mssP4NormalBump.rIn := by
    simpa only [mssP4NormalBump, Metric.mem_closedBall, Real.dist_eq,
      dist_zero_right, Real.norm_eq_abs] using hs
  rw [mssP4NormalBump.one_of_mem_closedBall hmem]
  norm_num

private theorem mssP4Normal_tsupport_subset :
    tsupport (mssP4Normal : Real → Complex) ⊆ Set.Ioo (-2) 2 := by
  have hsupp : Function.support (mssP4Normal : Real → Complex) ⊆
      Set.Icc (-3 / 2 : Real) (3 / 2 : Real) := by
    intro s hs
    have hs0 : mssP4Normal s ≠ 0 := Function.mem_support.mp hs
    have hs' : mssP4NormalBump s ≠ 0 := by
      rw [mssP4Normal_apply] at hs0
      exact Complex.ofReal_ne_zero.mp hs0
    have hdist : dist s (0 : Real) < 3 / 2 := by
      apply lt_of_not_ge
      intro h
      exact hs' (mssP4NormalBump.zero_of_le_dist h)
    rw [Real.dist_eq, abs_lt] at hdist
    constructor <;> linarith
  have hclosure : tsupport (mssP4Normal : Real → Complex) ⊆
      Set.Icc (-3 / 2 : Real) (3 / 2 : Real) := by
    change closure (Function.support (mssP4Normal : Real → Complex)) ⊆ _
    exact closure_minimal hsupp isClosed_Icc
  exact hclosure.trans (by
    intro s hs
    constructor <;> linarith [hs.1, hs.2])

private def mssP4FineTildeRadialGate (eta : Euclidean 2) : Real :=
  mssP4FineOuterRadialBump eta * (1 - mssP4FineInnerRadialBump eta)

/-- The enlarged radial gate is identically one wherever the annular source
cutoff is active.  The two independent buffers respectively handle the outer
and inner edge of the annulus. -/
private theorem mssP4FineTildeRadialGate_eq_one_of_sectorAnnularCutoff_ne_zero
    {eta : Euclidean 2}
    (h : Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta ≠ 0) :
    mssP4FineTildeRadialGate eta = 1 := by
  have houter : Auto.Spherical.MSSKakeya.outerSectorRadialBump eta ≠ 0 := by
    unfold Auto.Spherical.MSSKakeya.sectorAnnularCutoff at h
    exact (mul_ne_zero_iff.mp h).1
  have hnormlt : ‖eta‖ < 3 := by
    apply lt_of_not_ge
    intro hge
    apply houter
    apply Auto.Spherical.MSSKakeya.outerSectorRadialBump.zero_of_le_dist
    simpa only [Auto.Spherical.MSSKakeya.outerSectorRadialBump,
      dist_zero_right] using hge
  have hnormgt : 1 / 4 < ‖eta‖ := by
    apply lt_of_not_ge
    intro hle
    apply h
    exact Auto.Spherical.MSSKakeya.sectorAnnularCutoff_eq_zero_of_norm_le_quarter hle
  have houterMem : eta ∈ Metric.closedBall (0 : Euclidean 2)
      mssP4FineOuterRadialBump.rIn := by
    simpa only [mssP4FineOuterRadialBump, Metric.mem_closedBall,
      dist_zero_right] using hnormlt.le
  have hinnerDist : mssP4FineInnerRadialBump.rOut ≤ dist eta (0 : Euclidean 2) := by
    simpa only [mssP4FineInnerRadialBump, dist_zero_right] using
      (show 1 / 8 ≤ ‖eta‖ by linarith)
  unfold mssP4FineTildeRadialGate
  rw [mssP4FineOuterRadialBump.one_of_mem_closedBall houterMem,
    mssP4FineInnerRadialBump.zero_of_le_dist hinnerDist]
  norm_num

/-- The literal scale-dependent angular cutoff.  Keeping its factors real
makes the exact nesting and support arguments transparent before the final
complexification. -/
private def mssP4FineChiReal (q : Fin 4) (r : Fin 193) (scale : Real)
    (nu : Int) (xi : Euclidean 2) : Real :=
  if 2 ≤ scale then
    let eta : Euclidean 2 := scale⁻¹ • xi
    Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
      mssP4ChiChartGate q eta *
      mssUnitLatticeTransitionPiece
        (mssP4FineCoordinate q r scale xi - nu)
  else 0

/-- The enlarged cutoff which is one on the support of
`mssP4FineChiReal`. -/
private def mssP4FineTildeChiReal (q : Fin 4) (r : Fin 193) (scale : Real)
    (nu : Int) (xi : Euclidean 2) : Real :=
  if 2 ≤ scale then
    let eta : Euclidean 2 := scale⁻¹ • xi
    mssP4FineTildeRadialGate eta *
      mssP4TildeChiChartGate q eta *
      mssP4FineOuterLatticeBump
        (mssP4FineCoordinate q r scale xi - nu)
  else 0

private def mssP4FineChi (q : Fin 4) (r : Fin 193) (scale : Real)
    (nu : Int) (xi : Euclidean 2) : Complex :=
  (mssP4FineChiReal q r scale nu xi : Complex)

private def mssP4FineTildeChi (q : Fin 4) (r : Fin 193) (scale : Real)
    (nu : Int) (xi : Euclidean 2) : Complex :=
  (mssP4FineTildeChiReal q r scale nu xi : Complex)

/-- The active fine labels form the explicit translated integer interval
`[-N,N]`, where `N = ceil (4 sqrt scale)`. -/
private theorem mssP4FineAngularIndices_card
    {scale : Real} (hscale : 2 ≤ scale) :
    (mssP4FineAngularIndices scale).card =
      2 * mssP4FineIndexRadius scale + 1 := by
  simp [mssP4FineAngularIndices, hscale]

private theorem mssP4FineAngularIndex_abs_le_radius
    {scale : Real} (hscale : 2 ≤ scale) {nu : Int}
    (hnu : nu ∈ mssP4FineAngularIndices scale) :
    |nu| ≤ (mssP4FineIndexRadius scale : Int) := by
  rw [mssP4FineAngularIndices, if_pos hscale, Finset.mem_map] at hnu
  rcases hnu with ⟨k, hk, rfl⟩
  have hk' : k < 2 * mssP4FineIndexRadius scale + 1 :=
    Finset.mem_range.mp hk
  have hk'' : (k : Int) ≤ 2 * (mssP4FineIndexRadius scale : Int) := by
    exact_mod_cast Nat.le_of_lt_succ hk'
  change |(k : Int) - (mssP4FineIndexRadius scale : Int)| ≤
    (mssP4FineIndexRadius scale : Int)
  rw [abs_le]
  constructor <;> omega

private theorem mssP4FineIndexRadius_le_four_sqrt_add_one (scale : Real) :
    (mssP4FineIndexRadius scale : Real) ≤ 4 * Real.sqrt scale + 1 := by
  unfold mssP4FineIndexRadius
  exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * Real.sqrt scale)).le

private theorem mssP4FineIndexRadius_le_five_sqrt
    {scale : Real} (hscale : 2 ≤ scale) :
    (mssP4FineIndexRadius scale : Real) ≤ 5 * Real.sqrt scale := by
  have hsqrt : 1 ≤ Real.sqrt scale :=
    Real.one_le_sqrt.mpr (by linarith)
  have hceil := mssP4FineIndexRadius_le_four_sqrt_add_one scale
  nlinarith

private theorem mssP4FineAngularIndex_real_abs_le_five_sqrt
    {scale : Real} (hscale : 2 ≤ scale) {nu : Int}
    (hnu : nu ∈ mssP4FineAngularIndices scale) :
    |(nu : Real)| ≤ 5 * Real.sqrt scale := by
  have hindex := mssP4FineAngularIndex_abs_le_radius hscale hnu
  have hindexReal : |(nu : Real)| ≤ (mssP4FineIndexRadius scale : Real) := by
    exact_mod_cast hindex
  exact hindexReal.trans (mssP4FineIndexRadius_le_five_sqrt hscale)

private theorem mssP4FineAngularIndices_card_le_eleven_sqrt
    {scale : Real} (hscale : 2 ≤ scale) :
    ((mssP4FineAngularIndices scale).card : Real) ≤ 11 * Real.sqrt scale := by
  rw [mssP4FineAngularIndices_card hscale]
  push_cast
  have hsqrt : 1 ≤ Real.sqrt scale :=
    Real.one_le_sqrt.mpr (by linarith)
  have hceil := mssP4FineIndexRadius_le_four_sqrt_add_one scale
  nlinarith

/-- The finite translated fine lattice is an exact partition on the interval
covered by its labels. -/
private theorem sum_mssP4Fine_unitLattice_eq_one
    {scale t : Real} (hscale : 2 ≤ scale)
    (ht : |t| ≤ (mssP4FineIndexRadius scale : Real)) :
    ∑ nu ∈ mssP4FineAngularIndices scale,
      mssUnitLatticeTransitionPiece (t - (nu : Real)) = 1 := by
  classical
  let N : Nat := mssP4FineIndexRadius scale
  rw [mssP4FineAngularIndices, if_pos hscale, Finset.sum_map]
  change ∑ k ∈ Finset.range (2 * N + 1),
      mssUnitLatticeTransitionPiece
        (t - (((k : Int) - (N : Int) : Int) : Real)) = 1
  calc
    ∑ k ∈ Finset.range (2 * N + 1),
        mssUnitLatticeTransitionPiece
          (t - (((k : Int) - (N : Int) : Int) : Real)) =
        ∑ k ∈ Finset.range (2 * N + 1),
          mssUnitLatticeTransitionPiece (t + (N : Real) - (k : Real)) := by
            apply Finset.sum_congr rfl
            intro k hk
            push_cast
            ring
    _ = 1 := by
      simpa only [N] using
        (mss_finite_unitLatticeTransition_partition N (by simpa only [N] using ht))

private theorem mssP4FineOuterLatticeBump_one_of_unitPiece_ne_zero
    {s : Real} (h : mssUnitLatticeTransitionPiece s ≠ 0) :
    mssP4FineOuterLatticeBump s = 1 := by
  have hsupp : s ∈ Icc (-1 : Real) 1 :=
    mssUnitLatticeTransitionPiece_support_subset (Function.mem_support.mpr h)
  have hmem : s ∈ Metric.closedBall (0 : Real) mssP4FineOuterLatticeBump.rIn := by
    simpa [mssP4FineOuterLatticeBump, Metric.mem_closedBall, Real.dist_eq,
      Real.norm_eq_abs] using (abs_le.mpr hsupp)
  rw [mssP4FineOuterLatticeBump.one_of_mem_closedBall hmem]

/-- The enlarged fine angular cutoff is one on the support of the fine
cutoff.  This is the exact three-buffer nesting used by wave-front
localization. -/
private theorem mssP4FineTildeChiReal_eq_one_of_chiReal_ne_zero
    {q : Fin 4} {r : Fin 193} {scale : Real} {nu : Int} {xi : Euclidean 2}
    (hscale : 2 ≤ scale) (h : mssP4FineChiReal q r scale nu xi ≠ 0) :
    mssP4FineTildeChiReal q r scale nu xi = 1 := by
  rw [mssP4FineChiReal, if_pos hscale] at h
  let eta : Euclidean 2 := scale⁻¹ • xi
  have hfac : Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta ≠ 0 ∧
      mssP4ChiChartGate q eta ≠ 0 ∧
      mssUnitLatticeTransitionPiece
        (mssP4FineCoordinate q r scale xi - nu) ≠ 0 := by
    change Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
        mssP4ChiChartGate q eta *
        mssUnitLatticeTransitionPiece
          (mssP4FineCoordinate q r scale xi - nu) ≠ 0 at h
    rcases mul_ne_zero_iff.mp h with ⟨hab, hc⟩
    rcases mul_ne_zero_iff.mp hab with ⟨ha, hb⟩
    exact ⟨ha, hb, hc⟩
  rw [mssP4FineTildeChiReal, if_pos hscale]
  change mssP4FineTildeRadialGate eta * mssP4TildeChiChartGate q eta *
      mssP4FineOuterLatticeBump
        (mssP4FineCoordinate q r scale xi - nu) = 1
  rw [mssP4FineTildeRadialGate_eq_one_of_sectorAnnularCutoff_ne_zero hfac.1,
    mssP4TildeChiChartGate_eq_one_of_chi_gate_ne_zero hfac.2.1,
    mssP4FineOuterLatticeBump_one_of_unitPiece_ne_zero hfac.2.2]
  norm_num

private theorem mssP4FineTildeChi_eq_one_of_chi_ne_zero
    {q : Fin 4} {r : Fin 193} {scale : Real} {nu : Int} {xi : Euclidean 2}
    (hscale : 2 ≤ scale) (h : mssP4FineChi q r scale nu xi ≠ 0) :
    mssP4FineTildeChi q r scale nu xi = 1 := by
  unfold mssP4FineChi at h
  have hreal : mssP4FineChiReal q r scale nu xi ≠ 0 := by
    exact_mod_cast h
  unfold mssP4FineTildeChi
  norm_cast
  exact mssP4FineTildeChiReal_eq_one_of_chiReal_ne_zero hscale hreal

private theorem mssP4FineChiReal_nonneg
    (q : Fin 4) (r : Fin 193) {scale : Real} (hscale : 2 ≤ scale)
    (nu : Int) (xi : Euclidean 2) :
    0 ≤ mssP4FineChiReal q r scale nu xi := by
  rw [mssP4FineChiReal, if_pos hscale]
  exact mul_nonneg
    (mul_nonneg (Auto.Spherical.MSSKakeya.sectorAnnularCutoff_nonneg _)
      (by
        unfold mssP4ChiChartGate
        exact Real.smoothTransition.nonneg _))
    (mssUnitLatticeTransitionPiece_nonneg _)

private theorem mssP4FineChiReal_le_one
    (q : Fin 4) (r : Fin 193) {scale : Real} (hscale : 2 ≤ scale)
    (nu : Int) (xi : Euclidean 2) :
    mssP4FineChiReal q r scale nu xi ≤ 1 := by
  rw [mssP4FineChiReal, if_pos hscale]
  apply mul_le_one₀
  · apply mul_le_one₀
    · exact Auto.Spherical.MSSKakeya.sectorAnnularCutoff_le_one _
    · unfold mssP4ChiChartGate
      exact Real.smoothTransition.nonneg _
    · unfold mssP4ChiChartGate
      exact Real.smoothTransition.le_one _
  · exact mssUnitLatticeTransitionPiece_nonneg _
  · exact mssUnitLatticeTransitionPiece_le_one _

private theorem mssP4FineChi_norm_le_one
    (q : Fin 4) (r : Fin 193) {scale : Real} (hscale : 2 ≤ scale)
    (nu : Int) (xi : Euclidean 2) :
    ‖mssP4FineChi q r scale nu xi‖ ≤ 1 := by
  rw [mssP4FineChi, Complex.norm_real,
    Real.norm_of_nonneg (mssP4FineChiReal_nonneg q r hscale nu xi)]
  exact mssP4FineChiReal_le_one q r hscale nu xi

/-- Chordal distance on the unit circle is globally controlled by twice the
absolute angular difference.  This deliberately coarse constant keeps the
subsequent sector calculations elementary. -/
private theorem mssP4_circleDirection_sub_le_two_abs (a b : Real) :
    ‖Auto.Spherical.MSSKakeya.circleDirection a -
      Auto.Spherical.MSSKakeya.circleDirection b‖ ≤ 2 * |a - b| := by
  let u : Real := a - b
  have hdecomp : Auto.Spherical.MSSKakeya.circleDirection a =
      Real.cos u • Auto.Spherical.MSSKakeya.circleDirection b +
        Real.sin u • Auto.Spherical.MSSKakeya.circleDirectionDeriv b := by
    rw [show a = b + u by dsimp only [u]; ring,
      Auto.Spherical.MSSKakeya.circleDirection_add_decompose]
  have hrewrite :
      Real.cos u • Auto.Spherical.MSSKakeya.circleDirection b +
          Real.sin u • Auto.Spherical.MSSKakeya.circleDirectionDeriv b -
          Auto.Spherical.MSSKakeya.circleDirection b =
        (Real.cos u - 1) • Auto.Spherical.MSSKakeya.circleDirection b +
          Real.sin u • Auto.Spherical.MSSKakeya.circleDirectionDeriv b := by
    module
  have hcos : |Real.cos u - 1| ≤ |u| := by
    rw [show (1 : Real) = Real.cos 0 by norm_num]
    simpa using Real.abs_cos_sub_cos_le u 0
  have hsin : |Real.sin u| ≤ |u| := Real.abs_sin_le_abs
  rw [hdecomp, hrewrite]
  calc
    ‖(Real.cos u - 1) • Auto.Spherical.MSSKakeya.circleDirection b +
        Real.sin u • Auto.Spherical.MSSKakeya.circleDirectionDeriv b‖ ≤
        ‖(Real.cos u - 1) • Auto.Spherical.MSSKakeya.circleDirection b‖ +
          ‖Real.sin u • Auto.Spherical.MSSKakeya.circleDirectionDeriv b‖ :=
      norm_add_le _ _
    _ = |Real.cos u - 1| + |Real.sin u| := by
      rw [norm_smul, norm_smul,
        Auto.Spherical.MSSKakeya.norm_circleDirection,
        Auto.Spherical.MSSKakeya.norm_circleDirectionDeriv,
        mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |u| + |u| := add_le_add hcos hsin
    _ = 2 * |a - b| := by
      dsimp only [u]
      ring

/-- On angular gaps at most `π / 2`, the chordal distance is bounded below
by one half of the angular distance. -/
private theorem mssP4_half_abs_sub_le_circleDirection_sub {a b : Real}
    (hab : |a - b| ≤ Real.pi / 2) :
    (1 / 2 : Real) * |a - b| ≤
      ‖Auto.Spherical.MSSKakeya.circleDirection a -
        Auto.Spherical.MSSKakeya.circleDirection b‖ := by
  let u : Real := a - b
  have hdecomp : Auto.Spherical.MSSKakeya.circleDirection a =
      Real.cos u • Auto.Spherical.MSSKakeya.circleDirection b +
        Real.sin u • Auto.Spherical.MSSKakeya.circleDirectionDeriv b := by
    rw [show a = b + u by dsimp only [u]; ring,
      Auto.Spherical.MSSKakeya.circleDirection_add_decompose]
  have hinner : inner Real
      (Auto.Spherical.MSSKakeya.circleDirection a -
        Auto.Spherical.MSSKakeya.circleDirection b)
      (Auto.Spherical.MSSKakeya.circleDirectionDeriv b) = Real.sin u := by
    rw [hdecomp, inner_sub_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left,
      Auto.Spherical.MSSKakeya.inner_circleDirection_circleDirectionDeriv,
      real_inner_self_eq_norm_sq,
      Auto.Spherical.MSSKakeya.norm_circleDirectionDeriv]
    ring
  have hinnerabs : |Real.sin u| ≤
      ‖Auto.Spherical.MSSKakeya.circleDirection a -
        Auto.Spherical.MSSKakeya.circleDirection b‖ := by
    calc
      |Real.sin u| = |inner Real
          (Auto.Spherical.MSSKakeya.circleDirection a -
            Auto.Spherical.MSSKakeya.circleDirection b)
          (Auto.Spherical.MSSKakeya.circleDirectionDeriv b)| := by rw [hinner]
      _ ≤ ‖Auto.Spherical.MSSKakeya.circleDirection a -
            Auto.Spherical.MSSKakeya.circleDirection b‖ *
          ‖Auto.Spherical.MSSKakeya.circleDirectionDeriv b‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖Auto.Spherical.MSSKakeya.circleDirection a -
            Auto.Spherical.MSSKakeya.circleDirection b‖ := by
        rw [Auto.Spherical.MSSKakeya.norm_circleDirectionDeriv, mul_one]
  have hratio : (1 / 2 : Real) ≤ 2 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_le_four]
  calc
    (1 / 2 : Real) * |a - b| = (1 / 2 : Real) * |u| := by
      rfl
    _ ≤ (2 / Real.pi) * |u| :=
      mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
    _ ≤ |Real.sin u| := by
      apply Real.mul_abs_le_abs_sin
      simpa only [u] using hab
    _ ≤ ‖Auto.Spherical.MSSKakeya.circleDirection a -
          Auto.Spherical.MSSKakeya.circleDirection b‖ := hinnerabs

private theorem mssP4FineDirection_center_angle_abs
    (r : Fin 193) {scale : Real} (hscale : 0 < scale) (nu : Int) :
    |(mssP4CoarseAngleCenter r + (nu : Real) / (64 * Real.sqrt scale)) -
      mssP4CoarseAngleCenter r| =
      |(nu : Real)| / (64 * Real.sqrt scale) := by
  have hroot : 0 < Real.sqrt scale := Real.sqrt_pos.2 hscale
  rw [show (mssP4CoarseAngleCenter r + (nu : Real) /
      (64 * Real.sqrt scale)) - mssP4CoarseAngleCenter r =
      (nu : Real) / (64 * Real.sqrt scale) by ring,
    abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 64),
    abs_of_pos hroot]

private theorem mssP4FineDirection_pair_angle_abs
    (r : Fin 193) {scale : Real} (hscale : 0 < scale) (nu nu' : Int) :
    |(mssP4CoarseAngleCenter r + (nu : Real) / (64 * Real.sqrt scale)) -
      (mssP4CoarseAngleCenter r + (nu' : Real) / (64 * Real.sqrt scale))| =
      |(nu : Real) - (nu' : Real)| / (64 * Real.sqrt scale) := by
  have hroot : 0 < Real.sqrt scale := Real.sqrt_pos.2 hscale
  rw [show (mssP4CoarseAngleCenter r + (nu : Real) /
      (64 * Real.sqrt scale)) -
      (mssP4CoarseAngleCenter r + (nu' : Real) /
        (64 * Real.sqrt scale)) =
      ((nu : Real) - (nu' : Real)) / (64 * Real.sqrt scale) by ring,
    abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 64),
    abs_of_pos hroot]

private theorem mssP4FineDirection_center_dist_le_quarter (r : Fin 193)
    {scale : Real} (hscale : 2 ≤ scale) {nu : Int}
    (hnu : nu ∈ mssP4FineAngularIndices scale) :
    ‖mssP4FineDirection r scale nu -
      Auto.Spherical.MSSKakeya.circleDirection (mssP4CoarseAngleCenter r)‖ ≤
      1 / 4 := by
  have hscalePos : 0 < scale := by linarith
  have hroot : 0 < Real.sqrt scale := Real.sqrt_pos.2 hscalePos
  have hnuabs : |(nu : Real)| ≤ 5 * Real.sqrt scale :=
    mssP4FineAngularIndex_real_abs_le_five_sqrt hscale hnu
  have hangle : |(nu : Real) / (64 * Real.sqrt scale)| ≤ 5 / 64 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 64),
      abs_of_pos hroot]
    apply (div_le_iff₀ (by positivity : 0 < 64 * Real.sqrt scale)).mpr
    nlinarith
  unfold mssP4FineDirection
  calc
    ‖Auto.Spherical.MSSKakeya.circleDirection
          (mssP4CoarseAngleCenter r + (nu : Real) / (64 * Real.sqrt scale)) -
        Auto.Spherical.MSSKakeya.circleDirection (mssP4CoarseAngleCenter r)‖ ≤
        2 * |(mssP4CoarseAngleCenter r + (nu : Real) /
          (64 * Real.sqrt scale)) - mssP4CoarseAngleCenter r| :=
      mssP4_circleDirection_sub_le_two_abs _ _
    _ = 2 * |(nu : Real) / (64 * Real.sqrt scale)| := by
      rw [mssP4FineDirection_center_angle_abs r hscalePos, abs_div,
        abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 64),
        abs_of_pos hroot]
    _ ≤ 2 * (5 / 64 : Real) :=
      mul_le_mul_of_nonneg_left hangle (by norm_num)
    _ ≤ 1 / 4 := by norm_num

private theorem mssP4FineAngularIndex_difference_real_abs_le_ten_sqrt
    {scale : Real} (hscale : 2 ≤ scale) {nu nu' : Int}
    (hnu : nu ∈ mssP4FineAngularIndices scale)
    (hnu' : nu' ∈ mssP4FineAngularIndices scale) :
    |(nu : Real) - (nu' : Real)| ≤ 10 * Real.sqrt scale := by
  have hnuabs : |(nu : Real)| ≤ 5 * Real.sqrt scale :=
    mssP4FineAngularIndex_real_abs_le_five_sqrt hscale hnu
  have hnuabs' : |(nu' : Real)| ≤ 5 * Real.sqrt scale :=
    mssP4FineAngularIndex_real_abs_le_five_sqrt hscale hnu'
  calc
    |(nu : Real) - (nu' : Real)| ≤ |(nu : Real)| + |(nu' : Real)| :=
      by simpa using (abs_sub_le (nu : Real) 0 (nu' : Real))
    _ ≤ 5 * Real.sqrt scale + 5 * Real.sqrt scale :=
      add_le_add hnuabs hnuabs'
    _ = 10 * Real.sqrt scale := by ring

private theorem mssP4FineDirection_spacing_upper (r : Fin 193)
    {scale : Real} (hscale : 2 ≤ scale) {nu nu' : Int}
    (hnu : nu ∈ mssP4FineAngularIndices scale)
    (hnu' : nu' ∈ mssP4FineAngularIndices scale) :
    ‖mssP4FineDirection r scale nu - mssP4FineDirection r scale nu'‖ ≤
      (1 / 32 : Real) * ((nu - nu').natAbs : Real) *
        scale ^ (-(1 / 2 : Real)) := by
  have hscalePos : 0 < scale := by linarith
  have hroot : 0 < Real.sqrt scale := Real.sqrt_pos.2 hscalePos
  have hlabel : |(nu : Real) - (nu' : Real)| ≤ 10 * Real.sqrt scale :=
    mssP4FineAngularIndex_difference_real_abs_le_ten_sqrt hscale hnu hnu'
  have hcast : |(nu : Real) - (nu' : Real)| =
      ((nu - nu').natAbs : Real) := by
    simpa [Int.natCast_natAbs, Int.cast_sub]
  rw [mss_rpow_neg_half_eq_sqrt_inv hscalePos]
  unfold mssP4FineDirection
  calc
    ‖Auto.Spherical.MSSKakeya.circleDirection
          (mssP4CoarseAngleCenter r + (nu : Real) / (64 * Real.sqrt scale)) -
        Auto.Spherical.MSSKakeya.circleDirection
          (mssP4CoarseAngleCenter r + (nu' : Real) /
            (64 * Real.sqrt scale))‖ ≤
        2 * |(mssP4CoarseAngleCenter r + (nu : Real) /
          (64 * Real.sqrt scale)) -
          (mssP4CoarseAngleCenter r + (nu' : Real) /
            (64 * Real.sqrt scale))| :=
      mssP4_circleDirection_sub_le_two_abs _ _
    _ = 2 * (|(nu : Real) - (nu' : Real)| /
        (64 * Real.sqrt scale)) := by
      rw [mssP4FineDirection_pair_angle_abs r hscalePos]
    _ = (1 / 32 : Real) * ((nu - nu').natAbs : Real) *
        (Real.sqrt scale)⁻¹ := by
      rw [hcast]
      field_simp [hroot.ne']
      ring

private theorem mssP4FineDirection_spacing_lower (r : Fin 193)
    {scale : Real} (hscale : 2 ≤ scale) {nu nu' : Int}
    (hnu : nu ∈ mssP4FineAngularIndices scale)
    (hnu' : nu' ∈ mssP4FineAngularIndices scale) :
    (1 / 128 : Real) * ((nu - nu').natAbs : Real) *
        scale ^ (-(1 / 2 : Real)) ≤
      ‖mssP4FineDirection r scale nu - mssP4FineDirection r scale nu'‖ := by
  have hscalePos : 0 < scale := by linarith
  have hroot : 0 < Real.sqrt scale := Real.sqrt_pos.2 hscalePos
  have hlabel : |(nu : Real) - (nu' : Real)| ≤ 10 * Real.sqrt scale :=
    mssP4FineAngularIndex_difference_real_abs_le_ten_sqrt hscale hnu hnu'
  have hcast : |(nu : Real) - (nu' : Real)| =
      ((nu - nu').natAbs : Real) := by
    simpa [Int.natCast_natAbs, Int.cast_sub]
  have hangle : |(mssP4CoarseAngleCenter r + (nu : Real) /
      (64 * Real.sqrt scale)) -
      (mssP4CoarseAngleCenter r + (nu' : Real) /
        (64 * Real.sqrt scale))| ≤ Real.pi / 2 := by
    rw [mssP4FineDirection_pair_angle_abs r hscalePos]
    apply (div_le_iff₀ (by positivity : 0 < 64 * Real.sqrt scale)).mpr
    nlinarith [hlabel, Real.pi_gt_three]
  rw [mss_rpow_neg_half_eq_sqrt_inv hscalePos]
  unfold mssP4FineDirection
  calc
    (1 / 128 : Real) * ((nu - nu').natAbs : Real) *
        (Real.sqrt scale)⁻¹ =
        (1 / 2 : Real) * |(mssP4CoarseAngleCenter r + (nu : Real) /
          (64 * Real.sqrt scale)) -
          (mssP4CoarseAngleCenter r + (nu' : Real) /
            (64 * Real.sqrt scale))| := by
      rw [mssP4FineDirection_pair_angle_abs r hscalePos, hcast]
      field_simp [hroot.ne']
      ring
    _ ≤ ‖Auto.Spherical.MSSKakeya.circleDirection
          (mssP4CoarseAngleCenter r + (nu : Real) / (64 * Real.sqrt scale)) -
        Auto.Spherical.MSSKakeya.circleDirection
          (mssP4CoarseAngleCenter r + (nu' : Real) /
            (64 * Real.sqrt scale))‖ :=
      mssP4_half_abs_sub_le_circleDirection_sub hangle

/-- A nonzero fine cutoff lies in the stated scale-dependent angular sector.
The proof first returns to the normalized chart variable, then uses the
literal polar-coordinate identity on the buffered chart carrier. -/
private theorem mssP4Fine_mem_angularSector_of_projection_and_coordinate
    {q : Fin 4} {r : Fin 193} {scale : Real} {nu : Int} {xi : Euclidean 2}
    (hscale : 2 ≤ scale)
    (hproj : 1 / 16 < Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) (scale⁻¹ • xi))
    (hcoord : |mssP4FineCoordinate q r scale xi - nu| ≤ 2) :
    xi ∈ angularSector (mssP4FineDirection r scale nu)
      (scale ^ (-(1 / 2 : Real))) := by
  have hscalePos : 0 < scale := by linarith
  have hrootPos : 0 < Real.sqrt scale := Real.sqrt_pos.2 hscalePos
  have hdenPos : 0 < 64 * Real.sqrt scale := by positivity
  let eta : Euclidean 2 := scale⁻¹ • xi
  have hetaProj : 1 / 16 < Auto.Spherical.MSSKakeya.sectorProjection
      (Auto.Spherical.MSSKakeya.chartSectorIndex q) eta := by
    simpa only [eta] using hproj
  have heta0 : eta ≠ 0 := by
    intro hz
    rw [hz] at hetaProj
    have hfalse : (1 / 16 : Real) < 0 := by
      simpa [Auto.Spherical.MSSKakeya.sectorProjection] using hetaProj
    norm_num at hfalse
  have hetaNormPos : 0 < ‖eta‖ := norm_pos_iff.mpr heta0
  have hxi0 : xi ≠ 0 := by
    intro hz
    apply heta0
    simpa [eta, hz]
  have hpolar : eta = ‖eta‖ •
      Auto.Spherical.MSSKakeya.circleDirection (mssP4FineChartAngle q scale xi) := by
    simpa only [eta, mssP4FineChartAngle,
      Auto.Spherical.MSSKakeya.scaledChartAngle] using
      (mssP4_polar_of_sixteenth_lt_projection hetaProj)
  have hxiScale : xi = scale • eta := by
    dsimp [eta]
    exact (Auto.Spherical.MSSKakeya.smul_inv_smul_eq_self hscalePos xi).symm
  have hnormalize : (‖xi‖)⁻¹ • xi =
      Auto.Spherical.MSSKakeya.circleDirection (mssP4FineChartAngle q scale xi) := by
    change NormedSpace.normalize xi = _
    calc
      NormedSpace.normalize xi = NormedSpace.normalize (scale • eta) :=
        congrArg NormedSpace.normalize hxiScale
      _ = NormedSpace.normalize eta :=
        NormedSpace.normalize_smul_of_pos hscalePos eta
      _ = Auto.Spherical.MSSKakeya.circleDirection
          (mssP4FineChartAngle q scale xi) := by
        change (‖eta‖)⁻¹ • eta = _
        calc
          (‖eta‖)⁻¹ • eta =
              (‖eta‖)⁻¹ • (‖eta‖ •
                Auto.Spherical.MSSKakeya.circleDirection
                  (mssP4FineChartAngle q scale xi)) :=
            congrArg (fun z : Euclidean 2 => (‖eta‖)⁻¹ • z) hpolar
          _ = Auto.Spherical.MSSKakeya.circleDirection
              (mssP4FineChartAngle q scale xi) := by
            rw [smul_smul, inv_mul_cancel₀ hetaNormPos.ne', one_smul]
  have hid : mssP4FineCoordinate q r scale xi - (nu : Real) =
      (64 * Real.sqrt scale) *
        (mssP4FineChartAngle q scale xi -
          (mssP4CoarseAngleCenter r + (nu : Real) /
            (64 * Real.sqrt scale))) := by
    unfold mssP4FineCoordinate mssP4FineCoarseCoordinate mssP4CoarseAngleCenter
    field_simp [hrootPos.ne']
    ring
  have hangle : |mssP4FineChartAngle q scale xi -
      (mssP4CoarseAngleCenter r + (nu : Real) /
        (64 * Real.sqrt scale))| ≤ 2 / (64 * Real.sqrt scale) := by
    calc
      |mssP4FineChartAngle q scale xi -
          (mssP4CoarseAngleCenter r + (nu : Real) /
            (64 * Real.sqrt scale))| =
          |(64 * Real.sqrt scale) *
            (mssP4FineChartAngle q scale xi -
              (mssP4CoarseAngleCenter r + (nu : Real) /
                (64 * Real.sqrt scale)))| /
            (64 * Real.sqrt scale) := by
              rw [abs_mul, abs_of_pos hdenPos]
              field_simp [hdenPos.ne']
      _ = |mssP4FineCoordinate q r scale xi - (nu : Real)| /
            (64 * Real.sqrt scale) := by rw [← hid]
      _ ≤ 2 / (64 * Real.sqrt scale) :=
        div_le_div_of_nonneg_right hcoord hdenPos.le
  have hchord : ‖Auto.Spherical.MSSKakeya.circleDirection
      (mssP4FineChartAngle q scale xi) -
      mssP4FineDirection r scale nu‖ ≤
        scale ^ (-(1 / 2 : Real)) := by
    change ‖Auto.Spherical.MSSKakeya.circleDirection (mssP4FineChartAngle q scale xi) -
      Auto.Spherical.MSSKakeya.circleDirection
        (mssP4CoarseAngleCenter r + (nu : Real) /
          (64 * Real.sqrt scale))‖ ≤ _
    calc
      ‖Auto.Spherical.MSSKakeya.circleDirection
          (mssP4FineChartAngle q scale xi) -
          Auto.Spherical.MSSKakeya.circleDirection
            (mssP4CoarseAngleCenter r + (nu : Real) /
              (64 * Real.sqrt scale))‖ ≤
          2 * |mssP4FineChartAngle q scale xi -
            (mssP4CoarseAngleCenter r + (nu : Real) /
              (64 * Real.sqrt scale))| :=
        mssP4_circleDirection_sub_le_two_abs _ _
      _ ≤ 2 * (2 / (64 * Real.sqrt scale)) :=
        mul_le_mul_of_nonneg_left hangle (by norm_num)
      _ = (1 / 16 : Real) * (Real.sqrt scale)⁻¹ := by
        field_simp [hrootPos.ne']
        ring
      _ ≤ (Real.sqrt scale)⁻¹ := by
        have hinv : 0 ≤ (Real.sqrt scale)⁻¹ := inv_nonneg.mpr hrootPos.le
        nlinarith
      _ = scale ^ (-(1 / 2 : Real)) :=
        (mss_rpow_neg_half_eq_sqrt_inv hscalePos).symm
  change xi ≠ 0 ∧ ‖(‖xi‖)⁻¹ • xi -
      mssP4FineDirection r scale nu‖ ≤ scale ^ (-(1 / 2 : Real))
  refine ⟨hxi0, ?_⟩
  rw [hnormalize]
  exact hchord

private theorem mssP4FineOuterLatticeBump_ne_zero_imp_abs_lt_two {s : Real}
    (h : mssP4FineOuterLatticeBump s ≠ 0) : |s| < 2 := by
  apply lt_of_not_ge
  intro hge
  apply h
  apply mssP4FineOuterLatticeBump.zero_of_le_dist
  simpa [mssP4FineOuterLatticeBump, Real.dist_eq] using hge

private theorem mssP4FineChi_support (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) (_hnu : nu ∈ mssP4FineAngularIndices scale) :
    Function.support (mssP4FineChi q r scale nu) ⊆
      angularSector (mssP4FineDirection r scale nu)
        (scale ^ (-(1 / 2 : Real))) := by
  intro xi hxi
  by_cases hscale : 2 ≤ scale
  · have hreal : mssP4FineChiReal q r scale nu xi ≠ 0 := by
      have hxi0 : mssP4FineChi q r scale nu xi ≠ 0 :=
        Function.mem_support.mp hxi
      unfold mssP4FineChi at hxi0
      exact Complex.ofReal_ne_zero.mp hxi0
    rw [mssP4FineChiReal, if_pos hscale] at hreal
    let eta : Euclidean 2 := scale⁻¹ • xi
    have hfac : mssP4ChiChartGate q eta ≠ 0 ∧
        mssUnitLatticeTransitionPiece
          (mssP4FineCoordinate q r scale xi - nu) ≠ 0 := by
      change Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
          mssP4ChiChartGate q eta *
          mssUnitLatticeTransitionPiece
            (mssP4FineCoordinate q r scale xi - nu) ≠ 0 at hreal
      rcases mul_ne_zero_iff.mp hreal with ⟨hab, hc⟩
      rcases mul_ne_zero_iff.mp hab with ⟨ha, hb⟩
      exact ⟨hb, hc⟩
    have hproj : 1 / 16 < Auto.Spherical.MSSKakeya.sectorProjection
        (Auto.Spherical.MSSKakeya.chartSectorIndex q) (scale⁻¹ • xi) := by
      have heighth := mssP4ChiChartGate_ne_zero_imp_eighth_lt_projection hfac.1
      simpa only [eta] using (show 1 / 16 < Auto.Spherical.MSSKakeya.sectorProjection
        (Auto.Spherical.MSSKakeya.chartSectorIndex q) eta by linarith)
    have hcoord : |mssP4FineCoordinate q r scale xi - nu| ≤ 2 := by
      have hpiece : mssP4FineCoordinate q r scale xi - nu ∈ Icc (-1 : Real) 1 :=
        mssUnitLatticeTransitionPiece_support_subset
          (Function.mem_support.mpr hfac.2)
      exact (abs_le.mpr hpiece).trans (by norm_num)
    exact mssP4Fine_mem_angularSector_of_projection_and_coordinate
      hscale hproj hcoord
  · have hxi0 : mssP4FineChi q r scale nu xi ≠ 0 :=
      Function.mem_support.mp hxi
    have hzero : mssP4FineChi q r scale nu xi = 0 := by
      simp [mssP4FineChi, mssP4FineChiReal, hscale]
    exact (hxi0 hzero).elim

private theorem mssP4FineTildeChi_support (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) (_hnu : nu ∈ mssP4FineAngularIndices scale) :
    Function.support (mssP4FineTildeChi q r scale nu) ⊆
      angularSector (mssP4FineDirection r scale nu)
        (scale ^ (-(1 / 2 : Real))) := by
  intro xi hxi
  by_cases hscale : 2 ≤ scale
  · have hreal : mssP4FineTildeChiReal q r scale nu xi ≠ 0 := by
      have hxi0 : mssP4FineTildeChi q r scale nu xi ≠ 0 :=
        Function.mem_support.mp hxi
      unfold mssP4FineTildeChi at hxi0
      exact Complex.ofReal_ne_zero.mp hxi0
    rw [mssP4FineTildeChiReal, if_pos hscale] at hreal
    let eta : Euclidean 2 := scale⁻¹ • xi
    have hfac : mssP4TildeChiChartGate q eta ≠ 0 ∧
        mssP4FineOuterLatticeBump
          (mssP4FineCoordinate q r scale xi - nu) ≠ 0 := by
      change mssP4FineTildeRadialGate eta *
          mssP4TildeChiChartGate q eta *
          mssP4FineOuterLatticeBump
            (mssP4FineCoordinate q r scale xi - nu) ≠ 0 at hreal
      rcases mul_ne_zero_iff.mp hreal with ⟨hab, hc⟩
      rcases mul_ne_zero_iff.mp hab with ⟨ha, hb⟩
      exact ⟨hb, hc⟩
    have hproj : 1 / 16 < Auto.Spherical.MSSKakeya.sectorProjection
        (Auto.Spherical.MSSKakeya.chartSectorIndex q) (scale⁻¹ • xi) := by
      simpa only [eta] using
        mssP4TildeChiChartGate_ne_zero_imp_sixteenth_lt_projection hfac.1
    have hcoord : |mssP4FineCoordinate q r scale xi - nu| ≤ 2 :=
      (mssP4FineOuterLatticeBump_ne_zero_imp_abs_lt_two hfac.2).le
    exact mssP4Fine_mem_angularSector_of_projection_and_coordinate
      hscale hproj hcoord
  · have hxi0 : mssP4FineTildeChi q r scale nu xi ≠ 0 :=
      Function.mem_support.mp hxi
    have hzero : mssP4FineTildeChi q r scale nu xi = 0 := by
      simp [mssP4FineTildeChi, mssP4FineTildeChiReal, hscale]
    exact (hxi0 hzero).elim

private theorem mssP4FineCoordinate_contDiff (q : Fin 4) (r : Fin 193)
    (scale : Real) :
    ContDiff Real (⊤ : ℕ∞) (mssP4FineCoordinate q r scale) := by
  unfold mssP4FineCoordinate mssP4FineCoarseCoordinate mssP4FineChartAngle
  exact contDiff_const.mul
    (((contDiff_const.mul
      (Auto.Spherical.MSSKakeya.contDiff_scaledChartAngle scale q)).add
        contDiff_const).sub contDiff_const)

private theorem mssP4FineTildeRadialGate_contDiff :
    ContDiff Real (⊤ : ℕ∞) mssP4FineTildeRadialGate := by
  unfold mssP4FineTildeRadialGate
  exact mssP4FineOuterRadialBump.contDiff.mul
    (contDiff_const.sub mssP4FineInnerRadialBump.contDiff)

/-- The outer radial gate makes the otherwise global chart angle into a
compact smooth function.  On the literal fine-cutoff carrier the two buffer
gates are both one, so this is an exact replacement there. -/
private theorem mssP4FineTildeRadialGate_compact :
    HasCompactSupport mssP4FineTildeRadialGate := by
  change HasCompactSupport (fun eta : Euclidean 2 =>
    mssP4FineOuterRadialBump eta *
      (1 - mssP4FineInnerRadialBump eta))
  exact mssP4FineOuterRadialBump.hasCompactSupport.mul_right

private noncomputable def mssP4BoundedChartAngle (q : Fin 4) :
    SchwartzMap (Euclidean 2) Real := by
  let raw : Euclidean 2 → Real := fun eta =>
    mssP4FineTildeRadialGate eta *
      mssP4TildeChiChartGate q eta *
      Auto.Spherical.MSSKakeya.globalSectorAngle
        (Auto.Spherical.MSSKakeya.chartSectorIndex q) eta
  have hcompact : HasCompactSupport raw := by
    change HasCompactSupport (fun eta : Euclidean 2 =>
      mssP4FineTildeRadialGate eta *
        mssP4TildeChiChartGate q eta *
        Auto.Spherical.MSSKakeya.globalSectorAngle
          (Auto.Spherical.MSSKakeya.chartSectorIndex q) eta)
    exact mssP4FineTildeRadialGate_compact.mul_right.mul_right
  have hsmooth : ContDiff Real (⊤ : ℕ∞) raw := by
    change ContDiff Real (⊤ : ℕ∞) (fun eta : Euclidean 2 =>
      mssP4FineTildeRadialGate eta *
        mssP4TildeChiChartGate q eta *
        Auto.Spherical.MSSKakeya.globalSectorAngle
          (Auto.Spherical.MSSKakeya.chartSectorIndex q) eta)
    exact
      ((mssP4FineTildeRadialGate_contDiff.mul
        (mssP4TildeChiChartGate_contDiff q)).mul
        (Auto.Spherical.MSSKakeya.contDiff_globalSectorAngle
          (Auto.Spherical.MSSKakeya.chartSectorIndex q)))
  exact hcompact.toSchwartzMap hsmooth

private theorem mssP4BoundedChartAngle_apply (q : Fin 4)
    (eta : Euclidean 2) :
    mssP4BoundedChartAngle q eta =
      mssP4FineTildeRadialGate eta *
        mssP4TildeChiChartGate q eta *
        Auto.Spherical.MSSKakeya.globalSectorAngle
          (Auto.Spherical.MSSKakeya.chartSectorIndex q) eta := by
  rfl

private theorem mssP4BoundedChartAngle_eq_globalSectorAngle_of_carrier_ne_zero
    {q : Fin 4} {eta : Euclidean 2}
    (hcarrier :
      Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
        mssP4ChiChartGate q eta ≠ 0) :
    mssP4BoundedChartAngle q eta =
      Auto.Spherical.MSSKakeya.globalSectorAngle
        (Auto.Spherical.MSSKakeya.chartSectorIndex q) eta := by
  rcases mul_ne_zero_iff.mp hcarrier with ⟨hann, hgate⟩
  rw [mssP4BoundedChartAngle_apply,
    mssP4FineTildeRadialGate_eq_one_of_sectorAnnularCutoff_ne_zero hann,
    mssP4TildeChiChartGate_eq_one_of_chi_gate_ne_zero hgate]
  ring

/-- The fixed compact annular/chart carrier of every fine angular cutoff. -/
private noncomputable def mssP4FineChiCarrier (q : Fin 4) :
    SchwartzMap (Euclidean 2) Complex := by
  let raw : Euclidean 2 → Complex := fun eta =>
    (Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
      mssP4ChiChartGate q eta : Real)
  have hcompactReal : HasCompactSupport (fun eta : Euclidean 2 =>
      Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
        mssP4ChiChartGate q eta) :=
    Auto.Spherical.MSSKakeya.hasCompactSupport_sectorAnnularCutoff.mul_right
  have hcompact : HasCompactSupport raw := by
    change HasCompactSupport
      (Complex.ofRealCLM ∘ fun eta : Euclidean 2 =>
        Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
          mssP4ChiChartGate q eta)
    exact hcompactReal.comp_left (by rfl)
  have hsmooth : ContDiff Real (⊤ : ℕ∞) raw := by
    change ContDiff Real (⊤ : ℕ∞)
      (Complex.ofRealCLM ∘ fun eta : Euclidean 2 =>
        Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
          mssP4ChiChartGate q eta)
    exact Complex.ofRealCLM.contDiff.comp
      (Auto.Spherical.MSSKakeya.contDiff_sectorAnnularCutoff.mul
        (mssP4ChiChartGate_contDiff q))
  exact hcompact.toSchwartzMap hsmooth

private theorem mssP4FineChiCarrier_apply (q : Fin 4)
    (eta : Euclidean 2) :
    mssP4FineChiCarrier q eta =
      (Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
        mssP4ChiChartGate q eta : Real) := by
  rfl

/-- A globally regular coordinate which agrees with the geometric angular
coordinate wherever the fine angular carrier is nonzero. -/
private def mssP4FineRegularCoordinate (q : Fin 4) (r : Fin 193)
    (scale : Real) (xi : Euclidean 2) : Real :=
  4 * Real.sqrt scale *
    (16 * mssP4BoundedChartAngle q (scale⁻¹ • xi) + 96 - (r.val : Real))

private theorem
    mssP4FineRegularCoordinate_eq_mssP4FineCoordinate_of_carrier_ne_zero
    {q : Fin 4} {r : Fin 193} {scale : Real} {xi : Euclidean 2}
    (hcarrier :
      Auto.Spherical.MSSKakeya.sectorAnnularCutoff (scale⁻¹ • xi) *
        mssP4ChiChartGate q (scale⁻¹ • xi) ≠ 0) :
    mssP4FineRegularCoordinate q r scale xi =
      mssP4FineCoordinate q r scale xi := by
  unfold mssP4FineRegularCoordinate mssP4FineCoordinate
    mssP4FineCoarseCoordinate mssP4FineChartAngle
    Auto.Spherical.MSSKakeya.scaledChartAngle
  change 4 * Real.sqrt scale *
      (16 * mssP4BoundedChartAngle q (scale⁻¹ • xi) + 96 - (r.val : Real)) =
    4 * Real.sqrt scale *
      (16 * Auto.Spherical.MSSKakeya.globalSectorAngle
        (Auto.Spherical.MSSKakeya.chartSectorIndex q) (scale⁻¹ • xi) +
          96 - (r.val : Real))
  rw [mssP4BoundedChartAngle_eq_globalSectorAngle_of_carrier_ne_zero hcarrier]

/-- The fine cutoff with the compact smooth angular extension substituted
inside its lattice factor.  It is pointwise identical to the literal cutoff,
but exposes global derivative bounds for the regularity proof. -/
private def mssP4FineRegularChiReal (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) (xi : Euclidean 2) : Real :=
  if 2 ≤ scale then
    let eta : Euclidean 2 := scale⁻¹ • xi
    Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
      mssP4ChiChartGate q eta *
      mssUnitLatticeTransitionPiece
        (mssP4FineRegularCoordinate q r scale xi - nu)
  else 0

private theorem mssP4FineRegularChiReal_eq_mssP4FineChiReal
    (q : Fin 4) (r : Fin 193) (scale : Real) (nu : Int) :
    mssP4FineRegularChiReal q r scale nu =
      mssP4FineChiReal q r scale nu := by
  funext xi
  by_cases hscale : 2 ≤ scale
  · rw [mssP4FineRegularChiReal, mssP4FineChiReal,
      if_pos hscale, if_pos hscale]
    let eta : Euclidean 2 := scale⁻¹ • xi
    by_cases hcarrier :
        Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
          mssP4ChiChartGate q eta = 0
    · simp [eta, hcarrier]
    · have hcoord :=
        mssP4FineRegularCoordinate_eq_mssP4FineCoordinate_of_carrier_ne_zero
          (q := q) (r := r) (scale := scale) (xi := xi)
          (by simpa only [eta] using hcarrier)
      rw [hcoord]
  · simp [mssP4FineRegularChiReal, mssP4FineChiReal, hscale]

private theorem mssP4FineChi_eq_regularChiReal
    (q : Fin 4) (r : Fin 193) (scale : Real) (nu : Int)
    (xi : Euclidean 2) :
    mssP4FineChi q r scale nu xi =
      (mssP4FineRegularChiReal q r scale nu xi : Complex) := by
  change (mssP4FineChiReal q r scale nu xi : Complex) = _
  rw [mssP4FineRegularChiReal_eq_mssP4FineChiReal]

private theorem mssP4FineRegularCoordinate_contDiff (q : Fin 4) (r : Fin 193)
    (scale : Real) :
    ContDiff Real (⊤ : ℕ∞) (mssP4FineRegularCoordinate q r scale) := by
  unfold mssP4FineRegularCoordinate
  exact contDiff_const.mul
    (((contDiff_const.mul
      (((mssP4BoundedChartAngle q).smooth (⊤ : ℕ∞)).comp
        (contDiff_id.const_smul scale⁻¹))).add
        contDiff_const).sub contDiff_const)

private theorem mssP4FineRegularChiReal_contDiff (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) (hscale : 2 ≤ scale) :
    ContDiff Real (⊤ : ℕ∞) (mssP4FineRegularChiReal q r scale nu) := by
  change ContDiff Real (⊤ : ℕ∞) (fun xi : Euclidean 2 =>
    if 2 ≤ scale then
      let eta : Euclidean 2 := scale⁻¹ • xi
      Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
        mssP4ChiChartGate q eta *
        mssUnitLatticeTransitionPiece
          (mssP4FineRegularCoordinate q r scale xi - nu)
    else 0)
  simp only [if_pos hscale]
  change ContDiff Real (⊤ : ℕ∞) (fun xi : Euclidean 2 =>
    Auto.Spherical.MSSKakeya.sectorAnnularCutoff (scale⁻¹ • xi) *
      mssP4ChiChartGate q (scale⁻¹ • xi) *
      mssUnitLatticeTransitionPiece
        (mssP4FineRegularCoordinate q r scale xi - nu))
  exact
    ((Auto.Spherical.MSSKakeya.contDiff_sectorAnnularCutoff.comp
      (contDiff_id.const_smul scale⁻¹)).mul
      ((mssP4ChiChartGate_contDiff q).comp
        (contDiff_id.const_smul scale⁻¹))).mul
      (mssUnitLatticeTransitionPiece_contDiff.comp
        ((mssP4FineRegularCoordinate_contDiff q r scale).sub contDiff_const))

private theorem mssP4FineRegularChiReal_compact (q : Fin 4) (r : Fin 193)
    {scale : Real} (nu : Int) (hscale : 2 ≤ scale) :
    HasCompactSupport (mssP4FineRegularChiReal q r scale nu) := by
  have hscalePos : 0 < scale := by linarith
  have hann : HasCompactSupport (fun xi : Euclidean 2 =>
      Auto.Spherical.MSSKakeya.sectorAnnularCutoff (scale⁻¹ • xi)) :=
    Auto.Spherical.MSSKakeya.hasCompactSupport_sectorAnnularCutoff.comp_smul
      (c := scale⁻¹) (inv_ne_zero hscalePos.ne')
  change HasCompactSupport (fun xi : Euclidean 2 =>
    if 2 ≤ scale then
      let eta : Euclidean 2 := scale⁻¹ • xi
      Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
        mssP4ChiChartGate q eta *
        mssUnitLatticeTransitionPiece
          (mssP4FineRegularCoordinate q r scale xi - nu)
    else 0)
  simp only [if_pos hscale]
  change HasCompactSupport (fun xi : Euclidean 2 =>
    Auto.Spherical.MSSKakeya.sectorAnnularCutoff (scale⁻¹ • xi) *
      mssP4ChiChartGate q (scale⁻¹ • xi) *
      mssUnitLatticeTransitionPiece
        (mssP4FineRegularCoordinate q r scale xi - nu))
  exact hann.mul_right.mul_right

private noncomputable def mssP4FineRegularChiSchwartz (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) : SchwartzMap (Euclidean 2) Complex := by
  by_cases hscale : 2 ≤ scale
  · have hcompact : HasCompactSupport (fun xi : Euclidean 2 =>
        (mssP4FineRegularChiReal q r scale nu xi : Complex)) := by
      change HasCompactSupport
        (Complex.ofRealCLM ∘ mssP4FineRegularChiReal q r scale nu)
      exact (mssP4FineRegularChiReal_compact q r nu hscale).comp_left (by rfl)
    have hsmooth : ContDiff Real (⊤ : ℕ∞) (fun xi : Euclidean 2 =>
        (mssP4FineRegularChiReal q r scale nu xi : Complex)) := by
      change ContDiff Real (⊤ : ℕ∞)
        (Complex.ofRealCLM ∘ mssP4FineRegularChiReal q r scale nu)
      exact Complex.ofRealCLM.contDiff.comp
        (mssP4FineRegularChiReal_contDiff q r scale nu hscale)
    exact hcompact.toSchwartzMap hsmooth
  · exact 0

private theorem mssP4FineRegularChiSchwartz_apply (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) (xi : Euclidean 2) :
    mssP4FineRegularChiSchwartz q r scale nu xi =
      (mssP4FineRegularChiReal q r scale nu xi : Complex) := by
  by_cases hscale : 2 ≤ scale
  · simp [mssP4FineRegularChiSchwartz, mssP4FineRegularChiReal, hscale]
  · simp [mssP4FineRegularChiSchwartz, mssP4FineRegularChiReal, hscale]

/-- The one-dimensional fine lattice factor, viewed as a fixed Schwartz
function.  This is used only to take global derivative seminorms after the
fine packet has been normalized to its natural `sqrt scale` spatial size. -/
private noncomputable def mssP4UnitLatticeTransitionSchwartz :
    SchwartzMap Real Complex := by
  let raw : Real → Complex := fun u => (mssUnitLatticeTransitionPiece u : Complex)
  have hcompact : HasCompactSupport raw := by
    change HasCompactSupport
      (Complex.ofRealCLM ∘ mssUnitLatticeTransitionPiece)
    exact mssUnitLatticeTransitionPiece_hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff Real (⊤ : ℕ∞) raw := by
    change ContDiff Real (⊤ : ℕ∞)
      (Complex.ofRealCLM ∘ mssUnitLatticeTransitionPiece)
    exact Complex.ofRealCLM.contDiff.comp
      mssUnitLatticeTransitionPiece_contDiff
  exact hcompact.toSchwartzMap hsmooth

private theorem mssP4UnitLatticeTransitionSchwartz_apply (u : Real) :
    mssP4UnitLatticeTransitionSchwartz u =
      (mssUnitLatticeTransitionPiece u : Complex) := by
  rfl

/-- A fixed Schwartz function remains uniformly bounded in every derivative
after contraction by a scalar of norm at most one. -/
private theorem aux_p4_norm_iteratedFDeriv_schwartz_comp_inv_smul_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (H : SchwartzMap (Euclidean 2) F) {R : Real} (hR : 1 ≤ R)
    (i : Nat) (y : Euclidean 2) :
    ‖iteratedFDeriv Real i (fun z : Euclidean 2 => H (R⁻¹ • z)) y‖ ≤
      SchwartzMap.seminorm Real 0 i H := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hchain : iteratedFDeriv Real i
      (fun z : Euclidean 2 => H (R⁻¹ • z)) =
      fun z => R⁻¹ ^ i • iteratedFDeriv Real i (H : Euclidean 2 → F)
        (R⁻¹ • z) := by
    exact iteratedFDeriv_comp_const_smul R⁻¹ (H.smooth (i : ℕ∞))
  rw [hchain, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hRpos.le) _)]
  have hinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hinv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
  calc
    R⁻¹ ^ i * ‖iteratedFDeriv Real i (H : Euclidean 2 → F) (R⁻¹ • y)‖ ≤
        1 * ‖iteratedFDeriv Real i (H : Euclidean 2 → F) (R⁻¹ • y)‖ := by
      gcongr
      exact pow_le_one₀ hinv0 hinv
    _ ≤ SchwartzMap.seminorm Real 0 i H := by
      simpa using H.norm_iteratedFDeriv_le_seminorm Real i (R⁻¹ • y)

/-- Positive-order derivatives of the natural rescaling
`y ↦ R • H (R⁻¹ • y)` have scale-independent bounds.  The zero-order
term is deliberately excluded: translations of the outer packet arguments
are harmless only after the positive-order chain-rule estimate. -/
private theorem aux_p4_norm_iteratedFDeriv_smul_schwartz_comp_inv_smul_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (H : SchwartzMap (Euclidean 2) F) {R : Real} (hR : 1 ≤ R)
    (i : Nat) (hi : 1 ≤ i) (y : Euclidean 2) :
    ‖iteratedFDeriv Real i
      (fun z : Euclidean 2 => R • H (R⁻¹ • z)) y‖ ≤
      SchwartzMap.seminorm Real 0 i H := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hsmooth : ContDiff Real i (fun z : Euclidean 2 => H (R⁻¹ • z)) :=
    (H.smooth (i : ℕ∞)).comp (contDiff_id.const_smul R⁻¹)
  have hchain : iteratedFDeriv Real i
      (fun z : Euclidean 2 => H (R⁻¹ • z)) y =
      R⁻¹ ^ i • iteratedFDeriv Real i (H : Euclidean 2 → F) (R⁻¹ • y) := by
    simpa using congrFun
      (iteratedFDeriv_comp_const_smul R⁻¹ (H.smooth (i : ℕ∞))) y
  change ‖iteratedFDeriv Real i
      (R • (fun z : Euclidean 2 => H (R⁻¹ • z))) y‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply hsmooth.contDiffAt, hchain,
    norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hRpos,
    Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (inv_nonneg.mpr hRpos.le)]
  have hinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hinv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
  have hpow : R * R⁻¹ ^ i ≤ 1 := by
    have htail : R⁻¹ ^ (i - 1) ≤ 1 :=
      pow_le_one₀ hinv0 hinv
    have hi' : i = (i - 1) + 1 := (Nat.sub_add_cancel hi).symm
    calc
      R * R⁻¹ ^ i = R * R⁻¹ ^ ((i - 1) + 1) := by
        exact congrArg (fun x : Real => R * x)
          (congrArg (fun n : Nat => R⁻¹ ^ n) hi')
      _ = R * (R⁻¹ ^ (i - 1) * R⁻¹) := by
        exact congrArg (fun x : Real => R * x) (pow_succ R⁻¹ (i - 1))
      _ = (R * R⁻¹) * R⁻¹ ^ (i - 1) := by ring
      _ = R⁻¹ ^ (i - 1) := by
        rw [mul_inv_cancel₀ hRpos.ne', one_mul]
      _ ≤ 1 := htail
  calc
    R * (R⁻¹ ^ i *
        ‖iteratedFDeriv Real i (H : Euclidean 2 → F) (R⁻¹ • y)‖) =
        (R * R⁻¹ ^ i) *
          ‖iteratedFDeriv Real i (H : Euclidean 2 → F) (R⁻¹ • y)‖ := by ring
    _ ≤ 1 * ‖iteratedFDeriv Real i (H : Euclidean 2 → F) (R⁻¹ • y)‖ := by
      gcongr
    _ ≤ SchwartzMap.seminorm Real 0 i H := by
      simpa using H.norm_iteratedFDeriv_le_seminorm Real i (R⁻¹ • y)

/-- A fixed one-dimensional Schwartz profile composed with an affine
rescaled two-dimensional Schwartz coordinate has a derivative envelope
independent of the dilation and translation parameters.  This is the sole
chain-rule package needed for both the angular lattice and normal radial
factors of the normalized p=4 packet. -/
private theorem aux_p4_exists_outer_comp_rescaled_schwartz_bound
    (outer : SchwartzMap Real Complex)
    (H : SchwartzMap (Euclidean 2) Real) (a : Real) (k : Nat) :
    ∃ B : Real, 0 ≤ B ∧ ∀ (R b : Real) (y : Euclidean 2), 1 ≤ R →
      ‖iteratedFDeriv Real k
        (outer ∘ fun z : Euclidean 2 =>
          a • (R • H (R⁻¹ • z)) + b) y‖ ≤ B := by
  let C : Real := ∑ i ∈ Finset.range (k + 1),
    SchwartzMap.seminorm Real 0 i outer
  have houter0 (i : Nat) : 0 ≤ SchwartzMap.seminorm Real 0 i outer := by
    exact (norm_nonneg (iteratedFDeriv Real i (outer : Real → Complex) 0)).trans
      (outer.norm_iteratedFDeriv_le_seminorm Real i 0)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun i _ => houter0 i
  have hCbound {i : Nat} (hi : i ≤ k) :
      SchwartzMap.seminorm Real 0 i outer ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun j => SchwartzMap.seminorm Real 0 j outer)
      (fun j _ => houter0 j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  let S : Real := ∑ i ∈ Finset.range (k + 1),
    SchwartzMap.seminorm Real 0 i H
  have hH0 (i : Nat) : 0 ≤ SchwartzMap.seminorm Real 0 i H := by
    exact (norm_nonneg (iteratedFDeriv Real i (H : Euclidean 2 → Real) 0)).trans
      (H.norm_iteratedFDeriv_le_seminorm Real i 0)
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => hH0 i
  have hSbound {i : Nat} (hi : i ≤ k) :
      SchwartzMap.seminorm Real 0 i H ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun j => SchwartzMap.seminorm Real 0 j H)
      (fun j _ => hH0 j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  let D : Real := 1 + |a| * S
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg zero_le_one (mul_nonneg (abs_nonneg _) hS0)
  have hDone : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) hS0)
  have hDterm {i : Nat} (hi : i ≤ k) :
      |a| * SchwartzMap.seminorm Real 0 i H ≤ D := by
    calc
      |a| * SchwartzMap.seminorm Real 0 i H ≤ |a| * S :=
        mul_le_mul_of_nonneg_left (hSbound hi) (abs_nonneg _)
      _ ≤ 1 + |a| * S := by
        exact le_add_of_nonneg_left zero_le_one
      _ = D := rfl
  refine ⟨(k.factorial : Real) * C * D ^ k,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC0) (pow_nonneg hD0 _), ?_⟩
  intro R b y hR
  have hinner : ContDiff Real (k : ℕ∞)
      (fun z : Euclidean 2 => a • (R • H (R⁻¹ • z)) + b) := by
    exact ((((H.smooth (k : ℕ∞)).comp
      (contDiff_id.const_smul R⁻¹)).const_smul R).const_smul a).add
        contDiff_const
  apply norm_iteratedFDeriv_comp_le (outer.smooth (k : ℕ∞)) hinner
    (by simp : (k : WithTop ℕ∞) ≤ ((k : ℕ∞) : WithTop ℕ∞)) y
  · intro i hi
    exact (outer.norm_iteratedFDeriv_le_seminorm Real i
      (a • (R • H (R⁻¹ • y)) + b)).trans (hCbound hi)
  · intro i hi1 hi
    have hu : ContDiff Real i (fun z : Euclidean 2 => R • H (R⁻¹ • z)) :=
      ((H.smooth (i : ℕ∞)).comp (contDiff_id.const_smul R⁻¹)).const_smul R
    have hscaled : ContDiffAt Real i
        (fun z : Euclidean 2 => a • (R • H (R⁻¹ • z))) y :=
      (hu.const_smul a).contDiffAt
    have hconst : ContDiffAt Real i (fun _ : Euclidean 2 => b) y :=
      contDiffAt_const
    have hderiv :
        iteratedFDeriv Real i
          (fun z : Euclidean 2 => a • (R • H (R⁻¹ • z)) + b) y =
          a • iteratedFDeriv Real i
            (fun z : Euclidean 2 => R • H (R⁻¹ • z)) y := by
      rw [show (fun z : Euclidean 2 =>
          a • (R • H (R⁻¹ • z)) + b) =
          (fun z : Euclidean 2 => a • (R • H (R⁻¹ • z))) +
            fun _ : Euclidean 2 => b by rfl,
        iteratedFDeriv_add_apply hscaled hconst,
        iteratedFDeriv_const_smul_apply' (a := a) hu.contDiffAt,
        iteratedFDeriv_const_of_ne
          (Nat.ne_of_gt (Nat.zero_lt_of_lt hi1)) b]
      simp
    rw [hderiv, norm_smul, Real.norm_eq_abs]
    calc
      |a| * ‖iteratedFDeriv Real i
          (fun z : Euclidean 2 => R • H (R⁻¹ • z)) y‖ ≤
          |a| * SchwartzMap.seminorm Real 0 i H :=
        mul_le_mul_of_nonneg_left
          (aux_p4_norm_iteratedFDeriv_smul_schwartz_comp_inv_smul_le
            H hR i hi1 y)
          (abs_nonneg _)
      _ ≤ D := hDterm hi
      _ ≤ D ^ i := le_self_pow₀ hDone (Nat.ne_of_gt (Nat.zero_lt_of_lt hi1))

/-- The finite Leibniz envelope used to combine the four normalized fine
packet factors. -/
private def aux_p4_leibnizBound (F G : Nat → Real) (r : Nat) : Real :=
  ∑ i ∈ Finset.range (r + 1), (r.choose i : Real) * F i * G (r - i)

private theorem aux_p4_leibnizBound_nonneg (F G : Nat → Real)
    (hF : ∀ i, 0 ≤ F i) (hG : ∀ i, 0 ≤ G i) (r : Nat) :
    0 ≤ aux_p4_leibnizBound F G r := by
  unfold aux_p4_leibnizBound
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (hF i))
    (hG (r - i))

/-- Pointwise global derivative envelopes are stable under multiplication.
The constants are deliberately explicit finite Leibniz sums so no compactness
or unproved uniformity is hidden in this step. -/
private theorem aux_p4_norm_iteratedFDeriv_mul_le_of_bounds
    (f g : Euclidean 2 → Complex) (hf : ContDiff Real (⊤ : ℕ∞) f)
    (hg : ContDiff Real (⊤ : ℕ∞) g) (F G : Nat → Real)
    (hF : ∀ i x, ‖iteratedFDeriv Real i f x‖ ≤ F i)
    (hG : ∀ i x, ‖iteratedFDeriv Real i g x‖ ≤ G i)
    (r : Nat) (x : Euclidean 2) :
    ‖iteratedFDeriv Real r (fun y => f y * g y) x‖ ≤
      aux_p4_leibnizBound F G r := by
  calc
    ‖iteratedFDeriv Real r (fun y => f y * g y) x‖ ≤
        ∑ i ∈ Finset.range (r + 1), (r.choose i : Real) *
          ‖iteratedFDeriv Real i f x‖ *
            ‖iteratedFDeriv Real (r - i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast le_top)
    _ ≤ aux_p4_leibnizBound F G r := by
      unfold aux_p4_leibnizBound
      apply Finset.sum_le_sum
      intro i hi
      have hFi : 0 ≤ F i :=
        (norm_nonneg (iteratedFDeriv Real i f x)).trans (hF i x)
      calc
        (r.choose i : Real) * ‖iteratedFDeriv Real i f x‖ *
            ‖iteratedFDeriv Real (r - i) g x‖ ≤
            (r.choose i : Real) * F i *
              ‖iteratedFDeriv Real (r - i) g x‖ := by
          apply mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hF i x) (Nat.cast_nonneg _))
            (norm_nonneg _)
        _ ≤ (r.choose i : Real) * F i * G (r - i) := by
          exact mul_le_mul_of_nonneg_left (hG (r - i) x)
            (mul_nonneg (Nat.cast_nonneg _) hFi)

private theorem mssP4FineChiReal_contDiff (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) (hscale : 2 ≤ scale) :
    ContDiff Real (⊤ : ℕ∞) (mssP4FineChiReal q r scale nu) := by
  unfold mssP4FineChiReal
  simp only [if_pos hscale]
  change ContDiff Real (⊤ : ℕ∞) (fun xi : Euclidean 2 =>
    Auto.Spherical.MSSKakeya.sectorAnnularCutoff (scale⁻¹ • xi) *
      mssP4ChiChartGate q (scale⁻¹ • xi) *
      mssUnitLatticeTransitionPiece
        (mssP4FineCoordinate q r scale xi - nu))
  exact
    ((Auto.Spherical.MSSKakeya.contDiff_sectorAnnularCutoff.comp
      (contDiff_id.const_smul scale⁻¹)).mul
      ((mssP4ChiChartGate_contDiff q).comp
        (contDiff_id.const_smul scale⁻¹))).mul
      (mssUnitLatticeTransitionPiece_contDiff.comp
        ((mssP4FineCoordinate_contDiff q r scale).sub contDiff_const))

private theorem mssP4FineTildeChiReal_contDiff (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) (hscale : 2 ≤ scale) :
    ContDiff Real (⊤ : ℕ∞) (mssP4FineTildeChiReal q r scale nu) := by
  unfold mssP4FineTildeChiReal
  simp only [if_pos hscale]
  change ContDiff Real (⊤ : ℕ∞) (fun xi : Euclidean 2 =>
    mssP4FineTildeRadialGate (scale⁻¹ • xi) *
      mssP4TildeChiChartGate q (scale⁻¹ • xi) *
      mssP4FineOuterLatticeBump
        (mssP4FineCoordinate q r scale xi - nu))
  exact
    ((mssP4FineTildeRadialGate_contDiff.comp
      (contDiff_id.const_smul scale⁻¹)).mul
      ((mssP4TildeChiChartGate_contDiff q).comp
        (contDiff_id.const_smul scale⁻¹))).mul
      (mssP4FineOuterLatticeBump.contDiff.comp
        ((mssP4FineCoordinate_contDiff q r scale).sub contDiff_const))

private theorem mssP4FineChiReal_compact (q : Fin 4) (r : Fin 193)
    {scale : Real} (nu : Int) (hscale : 2 ≤ scale) :
    HasCompactSupport (mssP4FineChiReal q r scale nu) := by
  have hscalePos : 0 < scale := by linarith
  have hann : HasCompactSupport (fun xi : Euclidean 2 =>
      Auto.Spherical.MSSKakeya.sectorAnnularCutoff (scale⁻¹ • xi)) :=
    Auto.Spherical.MSSKakeya.hasCompactSupport_sectorAnnularCutoff.comp_smul
      (c := scale⁻¹) (inv_ne_zero hscalePos.ne')
  unfold mssP4FineChiReal
  simp only [if_pos hscale]
  change HasCompactSupport (fun xi : Euclidean 2 =>
    Auto.Spherical.MSSKakeya.sectorAnnularCutoff (scale⁻¹ • xi) *
      mssP4ChiChartGate q (scale⁻¹ • xi) *
      mssUnitLatticeTransitionPiece
        (mssP4FineCoordinate q r scale xi - nu))
  exact hann.mul_right.mul_right

private theorem mssP4FineTildeChiReal_compact (q : Fin 4) (r : Fin 193)
    {scale : Real} (nu : Int) (hscale : 2 ≤ scale) :
    HasCompactSupport (mssP4FineTildeChiReal q r scale nu) := by
  have hscalePos : 0 < scale := by linarith
  have hann : HasCompactSupport (fun xi : Euclidean 2 =>
      mssP4FineTildeRadialGate (scale⁻¹ • xi)) := by
    change HasCompactSupport (fun xi : Euclidean 2 =>
      (mssP4FineOuterRadialBump (scale⁻¹ • xi)) *
        (1 - mssP4FineInnerRadialBump (scale⁻¹ • xi)))
    exact
      (mssP4FineOuterRadialBump.hasCompactSupport.comp_smul
        (c := scale⁻¹) (inv_ne_zero hscalePos.ne')).mul_right
  unfold mssP4FineTildeChiReal
  simp only [if_pos hscale]
  change HasCompactSupport (fun xi : Euclidean 2 =>
    mssP4FineTildeRadialGate (scale⁻¹ • xi) *
      mssP4TildeChiChartGate q (scale⁻¹ • xi) *
      mssP4FineOuterLatticeBump
        (mssP4FineCoordinate q r scale xi - nu))
  exact hann.mul_right.mul_right

private noncomputable def mssP4FineChiSchwartz (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) : SchwartzMap (Euclidean 2) Complex := by
  by_cases hscale : 2 ≤ scale
  · have hcompact : HasCompactSupport (fun xi : Euclidean 2 =>
        (mssP4FineChiReal q r scale nu xi : Complex)) := by
      change HasCompactSupport (Complex.ofRealCLM ∘ mssP4FineChiReal q r scale nu)
      exact (mssP4FineChiReal_compact q r nu hscale).comp_left (by rfl)
    have hsmooth : ContDiff Real (⊤ : ℕ∞) (fun xi : Euclidean 2 =>
        (mssP4FineChiReal q r scale nu xi : Complex)) := by
      change ContDiff Real (⊤ : ℕ∞)
        (Complex.ofRealCLM ∘ mssP4FineChiReal q r scale nu)
      exact Complex.ofRealCLM.contDiff.comp
        (mssP4FineChiReal_contDiff q r scale nu hscale)
    exact hcompact.toSchwartzMap hsmooth
  · exact 0

private theorem mssP4FineChiSchwartz_apply (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) (xi : Euclidean 2) :
    mssP4FineChiSchwartz q r scale nu xi =
      mssP4FineChi q r scale nu xi := by
  by_cases hscale : 2 ≤ scale
  · simp [mssP4FineChiSchwartz, mssP4FineChi, mssP4FineChiReal, hscale]
  · simp [mssP4FineChiSchwartz, mssP4FineChi, mssP4FineChiReal, hscale]

private noncomputable def mssP4FineTildeChiSchwartz (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) : SchwartzMap (Euclidean 2) Complex := by
  by_cases hscale : 2 ≤ scale
  · have hcompact : HasCompactSupport (fun xi : Euclidean 2 =>
        (mssP4FineTildeChiReal q r scale nu xi : Complex)) := by
      change HasCompactSupport (Complex.ofRealCLM ∘ mssP4FineTildeChiReal q r scale nu)
      exact (mssP4FineTildeChiReal_compact q r nu hscale).comp_left (by rfl)
    have hsmooth : ContDiff Real (⊤ : ℕ∞) (fun xi : Euclidean 2 =>
        (mssP4FineTildeChiReal q r scale nu xi : Complex)) := by
      change ContDiff Real (⊤ : ℕ∞)
        (Complex.ofRealCLM ∘ mssP4FineTildeChiReal q r scale nu)
      exact Complex.ofRealCLM.contDiff.comp
        (mssP4FineTildeChiReal_contDiff q r scale nu hscale)
    exact hcompact.toSchwartzMap hsmooth
  · exact 0

private theorem mssP4FineTildeChiSchwartz_apply (q : Fin 4) (r : Fin 193)
    (scale : Real) (nu : Int) (xi : Euclidean 2) :
    mssP4FineTildeChiSchwartz q r scale nu xi =
      mssP4FineTildeChi q r scale nu xi := by
  by_cases hscale : 2 ≤ scale
  · simp [mssP4FineTildeChiSchwartz, mssP4FineTildeChi,
      mssP4FineTildeChiReal, hscale]
  · simp [mssP4FineTildeChiSchwartz, mssP4FineTildeChi,
      mssP4FineTildeChiReal, hscale]

/-- One compact, smooth coarse-angular multiplier.  It is the product of a
buffered four-chart annular multiplier with one member of the finite angular
lattice.  The chart buffer is retained by the subsequent fine packet data. -/
noncomputable def mssP4CoarseAngleMultiplier (q : Fin 4) (r : Fin 193) :
    SchwartzMap (Euclidean 2) Complex := by
  let raw : Euclidean 2 → Complex := fun xi =>
    mssP4SourceChartMultiplier q xi *
      (mssP4AngleLattice q r xi : Complex)
  have hcompact : HasCompactSupport raw := by
    change HasCompactSupport (fun xi =>
      mssP4SourceChartMultiplier q xi *
        (mssP4AngleLattice q r xi : Complex))
    exact (mssP4SourceChartMultiplier_compact q).mul_right
  have hsmooth : ContDiff Real (⊤ : ℕ∞) raw := by
    change ContDiff Real (⊤ : ℕ∞) (fun xi =>
      mssP4SourceChartMultiplier q xi *
        (mssP4AngleLattice q r xi : Complex))
    exact (mssP4SourceChartMultiplier_contDiff q).mul
      (Complex.ofRealCLM.contDiff.comp (mssP4AngleLattice_contDiff q r))
  exact hcompact.toSchwartzMap hsmooth

theorem mssP4CoarseAngleMultiplier_apply (q : Fin 4) (r : Fin 193)
    (xi : Euclidean 2) :
    mssP4CoarseAngleMultiplier q r xi =
      mssP4SourceChartMultiplier q xi *
        (mssP4AngleLattice q r xi : Complex) := by
  rfl

theorem mssP4CoarseAngleMultiplier_compact (q : Fin 4) (r : Fin 193) :
    HasCompactSupport (mssP4CoarseAngleMultiplier q r : Euclidean 2 → Complex) := by
  change HasCompactSupport (fun xi =>
    mssP4SourceChartMultiplier q xi *
      (mssP4AngleLattice q r xi : Complex))
  exact (mssP4SourceChartMultiplier_compact q).mul_right

/-- Summing the fine pieces inside one coarse chart recovers that chart. -/
theorem sum_mssP4CoarseAngleMultiplier (q : Fin 4) (xi : Euclidean 2) :
    ∑ r : Fin 193, mssP4CoarseAngleMultiplier q r xi =
      mssP4SourceChartMultiplier q xi := by
  simp_rw [mssP4CoarseAngleMultiplier_apply]
  rw [← Finset.mul_sum, sum_mssP4AngleLattice_complex, mul_one]

/-- The actual unit-annular Littlewood--Paley amplitude split into its finite
coarse angular pieces. -/
noncomputable def mssP4CoarseAmplitude (C : lpCutoffs 2)
    (q : Fin 4) (r : Fin 193) : SchwartzMap (Euclidean 2) Complex :=
  SchwartzMap.smulLeftCLM Complex
    (mssP4CoarseAngleMultiplier q r : Euclidean 2 → Complex)
    (mssP4ScaledBandpassAmplitude C)

theorem mssP4CoarseAmplitude_apply (C : lpCutoffs 2)
    (q : Fin 4) (r : Fin 193) (xi : Euclidean 2) :
    mssP4CoarseAmplitude C q r xi =
      mssP4CoarseAngleMultiplier q r xi * mssP4ScaledBandpassAmplitude C xi := by
  unfold mssP4CoarseAmplitude
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (mssP4CoarseAngleMultiplier q r).hasTemperateGrowth]
  simp only [smul_eq_mul]

theorem mssP4CoarseAmplitude_compact (C : lpCutoffs 2)
    (q : Fin 4) (r : Fin 193) :
    HasCompactSupport (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex) := by
  have happly : (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex) =
      fun xi => mssP4CoarseAngleMultiplier q r xi *
        mssP4ScaledBandpassAmplitude C xi := by
    funext xi
    exact mssP4CoarseAmplitude_apply C q r xi
  rw [happly]
  exact (mssP4CoarseAngleMultiplier_compact q r).mul_right

theorem mssP4CoarseAmplitude_support_annulus (C : lpCutoffs 2)
    (q : Fin 4) (r : Fin 193) {xi : Euclidean 2}
    (hxi : xi ∈ Function.support
      (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex)) :
    ‖xi‖ ∈ Icc (1 / 2 : Real) 2 := by
  have hxi0 : mssP4CoarseAmplitude C q r xi ≠ 0 := Function.mem_support.mp hxi
  rw [mssP4CoarseAmplitude_apply] at hxi0
  exact mssP4ScaledBandpassAmplitude_support_annulus C
    (mul_ne_zero_iff.mp hxi0).2

private theorem mssP4CoarseAmplitude_ne_zero_imp_source_weight_ne_zero
    (C : lpCutoffs 2) {q : Fin 4} {r : Fin 193} {xi : Euclidean 2}
    (h : mssP4CoarseAmplitude C q r xi ≠ 0) :
    mssP4SourceChartOrderedWeight q xi ≠ 0 := by
  rw [mssP4CoarseAmplitude_apply] at h
  have hcoarse : mssP4CoarseAngleMultiplier q r xi ≠ 0 :=
    (mul_ne_zero_iff.mp h).1
  rw [mssP4CoarseAngleMultiplier_apply] at hcoarse
  have hsource : mssP4SourceChartMultiplier q xi ≠ 0 :=
    (mul_ne_zero_iff.mp hcoarse).1
  intro hweight
  apply hsource
  simp [mssP4SourceChartMultiplier, hweight]

private theorem mssP4CoarseAmplitude_ne_zero_imp_angleLattice_ne_zero
    (C : lpCutoffs 2) {q : Fin 4} {r : Fin 193} {xi : Euclidean 2}
    (h : mssP4CoarseAmplitude C q r xi ≠ 0) :
    mssP4AngleLattice q r xi ≠ 0 := by
  rw [mssP4CoarseAmplitude_apply] at h
  have hcoarse : mssP4CoarseAngleMultiplier q r xi ≠ 0 :=
    (mul_ne_zero_iff.mp h).1
  rw [mssP4CoarseAngleMultiplier_apply] at hcoarse
  exact Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hcoarse).2

private theorem mssP4FineCoarseCoordinate_abs_le_one_of_coarseAmplitude_ne_zero
    (C : lpCutoffs 2) {q : Fin 4} {r : Fin 193} {scale : Real}
    {xi : Euclidean 2}
    (h : mssP4CoarseAmplitude C q r (scale⁻¹ • xi) ≠ 0) :
    |mssP4FineCoarseCoordinate q r scale xi| ≤ 1 := by
  have hlattice : mssP4AngleLattice q r (scale⁻¹ • xi) ≠ 0 :=
    mssP4CoarseAmplitude_ne_zero_imp_angleLattice_ne_zero C h
  have hpiece : mssUnitLatticeTransitionPiece
      (mssP4FineCoarseCoordinate q r scale xi) ≠ 0 := by
    simpa only [mssP4FineCoarseCoordinate, mssP4FineChartAngle,
      Auto.Spherical.MSSKakeya.scaledChartAngle, mssP4AngleLattice] using hlattice
  exact abs_le.mpr (mssUnitLatticeTransitionPiece_support_subset
    (Function.mem_support.mpr hpiece))

private theorem mssP4FineCoordinate_abs_le_indexRadius_of_coarseAmplitude_ne_zero
    (C : lpCutoffs 2) {q : Fin 4} {r : Fin 193} {scale : Real}
    {xi : Euclidean 2}
    (h : mssP4CoarseAmplitude C q r (scale⁻¹ • xi) ≠ 0) :
    |mssP4FineCoordinate q r scale xi| ≤
      (mssP4FineIndexRadius scale : Real) := by
  have hcoarse : |mssP4FineCoarseCoordinate q r scale xi| ≤ 1 :=
    mssP4FineCoarseCoordinate_abs_le_one_of_coarseAmplitude_ne_zero C h
  have hfactor : 0 ≤ 4 * Real.sqrt scale :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hfour : |mssP4FineCoordinate q r scale xi| ≤ 4 * Real.sqrt scale := by
    calc
      |mssP4FineCoordinate q r scale xi| =
          (4 * Real.sqrt scale) * |mssP4FineCoarseCoordinate q r scale xi| := by
        rw [mssP4FineCoordinate, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : Real) ≤ 4),
          abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ (4 * Real.sqrt scale) * 1 :=
        mul_le_mul_of_nonneg_left hcoarse hfactor
      _ = 4 * Real.sqrt scale := by ring
  exact hfour.trans (Nat.le_ceil _)

/-- The fine angular lattice synthesizes one on the active part of one
coarse amplitude.  The annular and chart carriers are already one there, so
only the finite one-dimensional lattice sum remains. -/
private theorem sum_mssP4FineChi_eq_one_on_coarseAmplitude
    (C : lpCutoffs 2) {q : Fin 4} {r : Fin 193} {scale : Real}
    (hscale : 2 ≤ scale) (xi : Euclidean 2)
    (h : mssP4CoarseAmplitude C q r (scale⁻¹ • xi) ≠ 0) :
    ∑ nu ∈ mssP4FineAngularIndices scale,
      mssP4FineChi q r scale nu xi = 1 := by
  let eta : Euclidean 2 := scale⁻¹ • xi
  have hann : ‖eta‖ ∈ Icc (1 / 2 : Real) 2 := by
    apply mssP4CoarseAmplitude_support_annulus C q r
    exact Function.mem_support.mpr (by simpa only [eta] using h)
  have hcut : Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta = 1 :=
    Auto.Spherical.MSSKakeya.sectorAnnularCutoff_eq_one hann.1 hann.2
  have hweight : mssP4SourceChartOrderedWeight q eta ≠ 0 := by
    apply mssP4CoarseAmplitude_ne_zero_imp_source_weight_ne_zero C
    simpa only [eta] using h
  have hchart : mssP4ChiChartGate q eta = 1 :=
    mssP4ChiChartGate_eq_one_of_source_weight_ne_zero hweight
  have hcoord : |mssP4FineCoordinate q r scale xi| ≤
      (mssP4FineIndexRadius scale : Real) :=
    mssP4FineCoordinate_abs_le_indexRadius_of_coarseAmplitude_ne_zero C h
  have hsum : ∑ nu ∈ mssP4FineAngularIndices scale,
      mssUnitLatticeTransitionPiece
        (mssP4FineCoordinate q r scale xi - (nu : Real)) = 1 :=
    sum_mssP4Fine_unitLattice_eq_one hscale hcoord
  have hreal : ∑ nu ∈ mssP4FineAngularIndices scale,
      mssP4FineChiReal q r scale nu xi = 1 := by
    simp_rw [mssP4FineChiReal, if_pos hscale]
    change ∑ nu ∈ mssP4FineAngularIndices scale,
        Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
          mssP4ChiChartGate q eta *
          mssUnitLatticeTransitionPiece
            (mssP4FineCoordinate q r scale xi - nu) = 1
    calc
      ∑ nu ∈ mssP4FineAngularIndices scale,
          Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
            mssP4ChiChartGate q eta *
            mssUnitLatticeTransitionPiece
              (mssP4FineCoordinate q r scale xi - nu) =
          (Auto.Spherical.MSSKakeya.sectorAnnularCutoff eta *
            mssP4ChiChartGate q eta) *
            ∑ nu ∈ mssP4FineAngularIndices scale,
              mssUnitLatticeTransitionPiece
                (mssP4FineCoordinate q r scale xi - nu) := by
              rw [← Finset.mul_sum]
      _ = 1 := by rw [hcut, hchart, hsum]; norm_num
  unfold mssP4FineChi
  exact_mod_cast hreal

/-- The `4 × 193` coarse pieces exactly synthesize the normalized
Littlewood--Paley amplitude on the structured unit annulus. -/
theorem sum_mssP4CoarseAmplitude (C : lpCutoffs 2) (xi : Euclidean 2) :
    ∑ q : Fin 4, ∑ r : Fin 193, mssP4CoarseAmplitude C q r xi =
      mssP4ScaledBandpassAmplitude C xi := by
  by_cases hbase : mssP4ScaledBandpassAmplitude C xi = 0
  · simp [mssP4CoarseAmplitude_apply, hbase]
  · have hann : xi ∈ Auto.Spherical.MSSKakeya.unitDyadicFrequencyAnnulus :=
      mssP4ScaledBandpassAmplitude_support_annulus C hbase
    calc
      ∑ q : Fin 4, ∑ r : Fin 193, mssP4CoarseAmplitude C q r xi =
          ∑ q : Fin 4,
            (∑ r : Fin 193, mssP4CoarseAngleMultiplier q r xi) *
              mssP4ScaledBandpassAmplitude C xi := by
            apply Finset.sum_congr rfl
            intro q _
            simp_rw [mssP4CoarseAmplitude_apply]
            rw [← Finset.sum_mul]
      _ = (∑ q : Fin 4, mssP4SourceChartMultiplier q xi) *
            mssP4ScaledBandpassAmplitude C xi := by
            simp_rw [sum_mssP4CoarseAngleMultiplier]
            rw [Finset.sum_mul]
      _ = mssP4ScaledBandpassAmplitude C xi := by
            rw [sum_mssP4SourceChartMultiplier_eq_one_on_unit_annulus hann, one_mul]

/-- The radial--time package associated to one coarse angular piece.  The
only varying field is its compact annular amplitude; all radial, vertical,
normal-extension, and physical-time cutoffs are the canonical ones already
proved for the MSS decomposition. -/
private noncomputable def mssP4FineRadialTimeCutoffs
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193) : MSSRadialTimeCutoffs :=
  mssRadialTimeCutoffsOfAnnular (mssP4CoarseAmplitude C q r)
    (mssP4CoarseAmplitude_compact C q r)
    (fun eta heta => mssP4CoarseAmplitude_support_annulus C q r heta)

/-- The concrete cutoff core for a single member of the finite endpoint
atlas.  It contains only the explicit radial--time data and the fine angular
partition; the smooth packet realizations are added separately below. -/
private noncomputable def mssP4FineCutoffData
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193) : MSSWavefrontCutoffData where
  radialTime := mssP4FineRadialTimeCutoffs C q r
  angularConstant := 1
  angularConstant_pos := by norm_num
  angularIndices := mssP4FineAngularIndices
  directions := mssP4FineDirection r
  chi := mssP4FineChi q r
  tildeChi := mssP4FineTildeChi q r
  normal := mssP4Normal
  angular_card := by
    refine ⟨11, by norm_num, ?_⟩
    intro scale hscale
    exact mssP4FineAngularIndices_card_le_eleven_sqrt hscale
  direction_unit := by
    intro scale nu _hnu
    exact Auto.Spherical.MSSKakeya.norm_circleDirection _
  chi_support := by
    intro scale nu hnu
    simpa using mssP4FineChi_support q r scale nu hnu
  tildeChi_support := by
    intro scale nu hnu
    simpa using mssP4FineTildeChi_support q r scale nu hnu
  tildeChi_one_on_chi_support := by
    intro scale nu _hnu xi hchi
    by_cases hscale : 2 ≤ scale
    · exact mssP4FineTildeChi_eq_one_of_chi_ne_zero hscale hchi
    · have hzero : mssP4FineChi q r scale nu xi = 0 := by
        simp [mssP4FineChi, mssP4FineChiReal, hscale]
      exact (hchi hzero).elim
  normal_tsupport_subset := mssP4Normal_tsupport_subset
  normal_support := mssP4Normal_support
  normal_one_on_unit := mssP4Normal_one_on_unit

/-- The concrete narrow-sector geometry and exact fine synthesis attached to
one coarse angular member of the endpoint atlas. -/
private noncomputable def mssP4FineAngularData
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193) :
    MSSFineAngularData (mssP4FineCutoffData C q r) where
  sectorRadius := 1 / 4
  spacingLower := 1 / 128
  spacingUpper := 1 / 32
  geometry := by
    intro scale hscale
    change angularSectorGeometry scale (mssP4FineAngularIndices scale)
      (mssP4FineDirection r scale) (1 / 4) (1 / 128) (1 / 32)
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    refine ⟨Auto.Spherical.MSSKakeya.circleDirection (mssP4CoarseAngleCenter r),
      Auto.Spherical.MSSKakeya.norm_circleDirection _, ?_⟩
    intro nu hnu
    refine ⟨Auto.Spherical.MSSKakeya.norm_circleDirection _,
      mssP4FineDirection_center_dist_le_quarter r hscale hnu, ?_⟩
    intro nu' hnu'
    exact ⟨mssP4FineDirection_spacing_lower r hscale hnu hnu',
      mssP4FineDirection_spacing_upper r hscale hnu hnu'⟩
  partition_on_active_amplitude := by
    intro scale hscale xi hamp
    change mssP4CoarseAmplitude C q r (scale⁻¹ • xi) ≠ 0 at hamp
    exact sum_mssP4FineChi_eq_one_on_coarseAmplitude C hscale xi hamp
  chi_norm_le_one := by
    intro scale hscale nu _hnu xi
    exact mssP4FineChi_norm_le_one q r hscale nu xi

/-- The spatial dilation of one compact coarse annular amplitude. -/
private noncomputable def mssP4FineScaledCoarseAmplitude
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (hscale : 0 < scale) :
    SchwartzMap (Euclidean 2) Complex :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (Auto.Spherical.MSSKakeya.frequencyScaleEquiv scale hscale.ne'))
      (mssP4CoarseAmplitude C q r)

private theorem mssP4FineScaledCoarseAmplitude_apply
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (hscale : 0 < scale) (xi : Euclidean 2) :
    mssP4FineScaledCoarseAmplitude C q r scale hscale xi =
      mssP4CoarseAmplitude C q r (scale⁻¹ • xi) := by
  simp [mssP4FineScaledCoarseAmplitude,
    Auto.Spherical.MSSKakeya.frequencyScaleEquiv]

/-- The active spatial multiplier is a literal product of the fine angular,
scaled annular, and raw radial Schwartz profiles. -/
private noncomputable def mssP4FineSpatialProfileAux
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (hscale : 0 < scale) :
    SchwartzMap (Euclidean 2) Complex :=
  SchwartzMap.smulLeftCLM Complex
    (mssP4FineChiSchwartz q r scale nu : Euclidean 2 → Complex)
    (SchwartzMap.smulLeftCLM Complex
      (mssP4FineScaledCoarseAmplitude C q r scale hscale : Euclidean 2 → Complex)
      (mssRawRadialSchwartzProfile (mssP4FineRadialTimeCutoffs C q r)
        scale hscale n))

private theorem mssP4FineSpatialProfileAux_apply
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (hscale : 0 < scale) (xi : Euclidean 2) :
    mssP4FineSpatialProfileAux C q r scale n nu hscale xi =
      mssP4FineChi q r scale nu xi *
        (mssP4CoarseAmplitude C q r (scale⁻¹ • xi) *
          (mssP4FineRadialTimeCutoffs C q r).radial
            ((Real.sqrt scale)⁻¹ * ‖xi‖ - n)) := by
  unfold mssP4FineSpatialProfileAux
  rw [SchwartzMap.smulLeftCLM_apply_apply
      (mssP4FineChiSchwartz q r scale nu).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (mssP4FineScaledCoarseAmplitude C q r scale hscale).hasTemperateGrowth]
  simp only [smul_eq_mul]
  rw [mssP4FineChiSchwartz_apply,
    mssP4FineScaledCoarseAmplitude_apply,
    mssRawRadialSchwartzProfile_apply]

private theorem mssP4FineRadialTimeCutoffs_amplitude_apply
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193) (xi : Euclidean 2) :
    (mssP4FineRadialTimeCutoffs C q r).amplitude xi =
      mssP4CoarseAmplitude C q r xi := rfl

/-- The total spatial profile is zero outside the MSS scale range, so the
raw radial normalization is used only at positive scales. -/
private noncomputable def mssP4FineSpatialProfile
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) : SchwartzMap (Euclidean 2) Complex :=
  if hscale : 2 ≤ scale then
    mssP4FineSpatialProfileAux C q r scale n nu (by linarith)
  else 0

private theorem mssP4FineSpatialProfile_apply
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (xi : Euclidean 2) :
    mssP4FineSpatialProfile C q r scale n nu xi =
      mssP4FineChi q r scale nu xi *
        ((mssP4FineRadialTimeCutoffs C q r).amplitude (scale⁻¹ • xi) *
          (mssP4FineRadialTimeCutoffs C q r).radial
            ((Real.sqrt scale)⁻¹ * ‖xi‖ - n)) := by
  by_cases hscale : 2 ≤ scale
  · simp only [mssP4FineSpatialProfile, dif_pos hscale]
    simpa only [mssP4FineRadialTimeCutoffs_amplitude_apply] using
      (mssP4FineSpatialProfileAux_apply C q r scale n nu (by linarith) xi)
  · rw [mssP4FineSpatialProfile, dif_neg hscale]
    simp [mssP4FineChi, mssP4FineChiReal, hscale]

/-- A total Schwartz realization of the scaled normal coordinate.  Only the
zero scale is exceptional; the wave-front fields also quantify over negative
scales, so the nonzero branch deliberately does not assume positivity. -/
private noncomputable def mssP4FineNormalCoordinate
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) : SchwartzMap (Euclidean 2) Real :=
  if hzero : scale = 0 then 0 else
    let A : Euclidean 2 ≃L[Real] Euclidean 2 :=
      ContinuousLinearEquiv.smulLeft
        (Units.mk0 scale⁻¹ (inv_ne_zero hzero))
    scale • ((SchwartzMap.compCLMOfContinuousLinearEquiv Real A)
      (mssP4FineRadialTimeCutoffs C q r).normalExtension)

private theorem mssP4FineNormalCoordinate_apply
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (xi : Euclidean 2) :
    mssP4FineNormalCoordinate C q r scale xi =
      scale * (mssP4FineRadialTimeCutoffs C q r).normalExtension
        (scale⁻¹ • xi) := by
  by_cases hzero : scale = 0
  · subst scale
    simp [mssP4FineNormalCoordinate]
  · rw [mssP4FineNormalCoordinate, dif_neg hzero]
    dsimp
    change scale • (mssP4FineRadialTimeCutoffs C q r).normalExtension
      (scale⁻¹ • xi) = _
    rfl

/-- On the active coarse amplitude, the smooth normal-coordinate extension
is exactly the literal Euclidean norm.  This lets derivative estimates use
the smooth extension while retaining the required raw profile formula. -/
private theorem mssP4FineNormalCoordinate_eq_norm_of_coarseAmplitude_ne_zero
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    {scale : Real} (hscale : 0 < scale) (xi : Euclidean 2)
    (hamp : mssP4CoarseAmplitude C q r (scale⁻¹ • xi) ≠ 0) :
    mssP4FineNormalCoordinate C q r scale xi = ‖xi‖ := by
  have hnormal : (mssP4FineRadialTimeCutoffs C q r).normalExtension
      (scale⁻¹ • xi) = ‖scale⁻¹ • xi‖ := by
    apply (mssP4FineRadialTimeCutoffs C q r).normalExtension_eq_norm_on_amplitude
    simpa [mssP4FineRadialTimeCutoffs, mssRadialTimeCutoffsOfAnnular] using hamp
  rw [mssP4FineNormalCoordinate_apply, hnormal,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
  field_simp [hscale.ne']

/-- The radial packet factor written through the globally smooth normal
extension.  It agrees with the raw radial factor once it is multiplied by the
coarse annular amplitude. -/
private noncomputable def mssP4FineSmoothNormalRadialFactor
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n : Int) : Euclidean 2 → Complex := fun xi =>
  (mssP4FineRadialTimeCutoffs C q r).radial
    ((Real.sqrt scale)⁻¹ * mssP4FineNormalCoordinate C q r scale xi - n)

private theorem mssP4FineSmoothNormalRadialFactor_temperate
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n : Int) :
    (mssP4FineSmoothNormalRadialFactor C q r scale n).HasTemperateGrowth := by
  unfold mssP4FineSmoothNormalRadialFactor
  fun_prop

/-- A smooth-normal representative of the literal spatial profile.  It is
definitionally Schwartz because the compact coarse amplitude multiplies the
possibly noncompact normal radial factor. -/
private noncomputable def mssP4FineRegularSpatialProfileAux
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (hscale : 0 < scale) :
    SchwartzMap (Euclidean 2) Complex :=
  SchwartzMap.smulLeftCLM Complex
    (mssP4FineRegularChiSchwartz q r scale nu : Euclidean 2 → Complex)
    (SchwartzMap.smulLeftCLM Complex
      (mssP4FineSmoothNormalRadialFactor C q r scale n)
      (mssP4FineScaledCoarseAmplitude C q r scale hscale))

private theorem mssP4FineRegularSpatialProfileAux_apply
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (hscale : 0 < scale) (xi : Euclidean 2) :
    mssP4FineRegularSpatialProfileAux C q r scale n nu hscale xi =
      (mssP4FineRegularChiReal q r scale nu xi : Complex) *
        (mssP4FineSmoothNormalRadialFactor C q r scale n xi *
          mssP4CoarseAmplitude C q r (scale⁻¹ • xi)) := by
  unfold mssP4FineRegularSpatialProfileAux
  rw [SchwartzMap.smulLeftCLM_apply_apply
      (mssP4FineRegularChiSchwartz q r scale nu).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (mssP4FineSmoothNormalRadialFactor_temperate C q r scale n)]
  simp only [smul_eq_mul]
  rw [mssP4FineRegularChiSchwartz_apply,
    mssP4FineScaledCoarseAmplitude_apply]

/-- The smooth-normal representative is literally the already installed raw
profile.  This equality is the bridge used for all subsequent derivative
estimates. -/
private theorem mssP4FineRegularSpatialProfileAux_eq
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (hscale : 0 < scale) :
    mssP4FineRegularSpatialProfileAux C q r scale n nu hscale =
      mssP4FineSpatialProfileAux C q r scale n nu hscale := by
  ext xi
  rw [mssP4FineRegularSpatialProfileAux_apply,
    mssP4FineSpatialProfileAux_apply]
  by_cases hamp : mssP4CoarseAmplitude C q r (scale⁻¹ • xi) = 0
  · simp [hamp]
  · rw [mssP4FineSmoothNormalRadialFactor,
      mssP4FineNormalCoordinate_eq_norm_of_coarseAmplitude_ne_zero
        C q r hscale xi hamp]
    rw [mssP4FineChi_eq_regularChiReal]
    ring

private theorem mssP4FineNormalDefect_temperate (scale gamma : Real) :
    (fun u : Real => (1 : Complex) -
      mssP4Normal (scale ^ (-gamma) * u)).HasTemperateGrowth := by
  fun_prop

private noncomputable def mssP4FineNormalTail
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (gamma scale : Real) : SchwartzMap Real Complex :=
  SchwartzMap.smulLeftCLM Complex
    (fun u : Real => (1 : Complex) -
      mssP4Normal (scale ^ (-gamma) * u))
    (FourierTransform.fourier (mssP4FineRadialTimeCutoffs C q r).time)

private theorem mssP4FineNormalTail_apply
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (gamma scale u : Real) :
    mssP4FineNormalTail C q r gamma scale u =
      ((1 : Complex) - mssP4Normal (scale ^ (-gamma) * u)) *
        FourierTransform.fourier (mssP4FineRadialTimeCutoffs C q r).time u := by
  unfold mssP4FineNormalTail
  rw [SchwartzMap.smulLeftCLM_apply_apply
      (mssP4FineNormalDefect_temperate scale gamma),
    SchwartzMap.fourier_coe]
  rfl

/-- The actual smooth wave-front kernel data for one endpoint atlas member
and one admissible thickness. -/
private noncomputable def mssP4FineKernelData
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (gamma : MSSAdmissibleGamma) : MSSWavefrontKernelData where
  toMSSWavefrontCutoffData := mssP4FineCutoffData C q r
  gamma := gamma.1
  gamma_pos := gamma.2.1
  gamma_lt_tenth := gamma.2.2
  spatialProfile := mssP4FineSpatialProfile C q r
  spatialProfile_apply := by
    intro scale n nu xi
    simpa [mssP4FineCutoffData] using
      mssP4FineSpatialProfile_apply C q r scale n nu xi
  normalCoordinate := mssP4FineNormalCoordinate C q r
  normalCoordinate_apply := by
    intro scale xi
    simpa [mssP4FineCutoffData] using
      mssP4FineNormalCoordinate_apply C q r scale xi
  normalTail := mssP4FineNormalTail C q r gamma.1
  normalTail_apply := by
    intro scale u
    rw [mssP4FineNormalTail_apply, ← SchwartzMap.fourier_coe]
    rfl

private noncomputable def mssP4FineRawRadialProfile
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n : Int) : SchwartzMap (Euclidean 2) Complex :=
  if hscale : 0 < scale then
    mssRawRadialSchwartzProfile (mssP4FineRadialTimeCutoffs C q r)
      scale hscale n
  else 0

private theorem mssP4FineRawRadialProfile_apply
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n : Int) (hscale : 0 < scale) (xi : Euclidean 2) :
    mssP4FineRawRadialProfile C q r scale n xi =
      (mssP4FineRadialTimeCutoffs C q r).radial
        ((Real.sqrt scale)⁻¹ * ‖xi‖ - n) := by
  rw [mssP4FineRawRadialProfile, dif_pos hscale,
    mssRawRadialSchwartzProfile_apply]

/-- The raw radial and enlarged angular Schwartz realizations required by
the literal wave-front Fourier bridge. -/
private noncomputable def mssP4FineRawProfileRealization
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (gamma : MSSAdmissibleGamma) :
    MSSWavefrontRawProfileRealization (mssP4FineKernelData C q r gamma) where
  radialProfile := mssP4FineRawRadialProfile C q r
  radialProfile_apply := by
    intro scale n hscale xi
    simpa [mssP4FineKernelData, mssP4FineCutoffData] using
      mssP4FineRawRadialProfile_apply C q r scale n hscale xi
  wavefrontAngularProfile := mssP4FineTildeChiSchwartz q r
  wavefrontAngularProfile_eq_on_spatial := by
    intro scale n nu xi _hprofile
    simpa [mssP4FineKernelData, mssP4FineCutoffData] using
      mssP4FineTildeChiSchwartz_apply q r scale nu xi

/-- Every concrete fine packet uses the canonical physical-time cutoff, hence
is supported in the fixed slab required by the light-ray square-function
argument. -/
private theorem mssP4FineKernelData_hasLightRayTimeSlabSupport
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (gamma : MSSAdmissibleGamma) :
    (mssP4FineKernelData C q r gamma).HasLightRayTimeSlabSupport := by
  change Function.support
      ((mssP4FineRadialTimeCutoffs C q r).time : Real → Complex) ⊆
        lightRayTimeInterval
  simpa [mssP4FineRadialTimeCutoffs, mssRadialTimeCutoffsOfAnnular] using
    mssCanonicalTime_support_lightRayTimeInterval

/-- Pull one regular fine profile back to its natural `sqrt scale` spatial
scale.  The definition is a Schwartz-map pullback through an invertible
dilation; its explicit normalized product formula is recorded below. -/
private noncomputable def mssP4FineNormalizedRegularProfile
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (hscale : 2 ≤ scale) :
    SchwartzMap (Euclidean 2) Complex :=
  let R : Real := Real.sqrt scale
  let A : Euclidean 2 ≃L[Real] Euclidean 2 :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 R (Real.sqrt_ne_zero'.mpr (by linarith)))
  (SchwartzMap.compCLMOfContinuousLinearEquiv Complex A)
    (mssP4FineRegularSpatialProfileAux C q r scale n nu (by linarith))

private theorem mssP4FineNormalizedRegularProfile_apply
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (hscale : 2 ≤ scale) (y : Euclidean 2) :
    mssP4FineNormalizedRegularProfile C q r scale n nu hscale y =
      mssP4FineRegularSpatialProfileAux C q r scale n nu (by linarith)
        (Real.sqrt scale • y) := by
  simp [mssP4FineNormalizedRegularProfile]

private def mssP4FineNormalizedCarrier (q : Fin 4) (R : Real) :
    Euclidean 2 → Complex := fun y =>
  mssP4FineChiCarrier q (R⁻¹ • y)

private def mssP4FineNormalizedLatticeFactor
    (q : Fin 4) (r : Fin 193) (R : Real) (nu : Int) :
    Euclidean 2 → Complex :=
  mssP4UnitLatticeTransitionSchwartz ∘ fun y : Euclidean 2 =>
    (64 : Real) • (R • mssP4BoundedChartAngle q (R⁻¹ • y)) +
      (4 * R * (96 - (r.val : Real)) - (nu : Real))

private def mssP4FineNormalizedNormalFactor
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (R : Real) (n : Int) : Euclidean 2 → Complex :=
  (mssP4FineRadialTimeCutoffs C q r).radial ∘ fun y : Euclidean 2 =>
    R • (mssP4FineRadialTimeCutoffs C q r).normalExtension (R⁻¹ • y) -
      (n : Real)

private def mssP4FineNormalizedCoarseFactor
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193) (R : Real) :
    Euclidean 2 → Complex := fun y =>
  mssP4CoarseAmplitude C q r (R⁻¹ • y)

/-- The elementary scalar identity behind every normalized packet formula. -/
private theorem aux_p4_inv_smul_sqrt_smul
    {scale : Real} (hscale : 0 < scale) (y : Euclidean 2) :
    scale⁻¹ • (Real.sqrt scale • y) = (Real.sqrt scale)⁻¹ • y := by
  have hroot : Real.sqrt scale ≠ 0 := Real.sqrt_ne_zero'.mpr hscale
  have hsquare : Real.sqrt scale * Real.sqrt scale = scale := by
    nlinarith [Real.sq_sqrt hscale.le]
  rw [smul_smul]
  congr 1
  calc
    scale⁻¹ * Real.sqrt scale =
        (Real.sqrt scale * Real.sqrt scale)⁻¹ * Real.sqrt scale := by
      rw [hsquare]
    _ = (Real.sqrt scale)⁻¹ := by field_simp [hroot]

/-- The smooth-normal fine profile has four fixed normalized factors: a
compact carrier, a translated lattice bump, a translated radial bump, and
a compact coarse amplitude. -/
private theorem mssP4FineNormalizedRegularProfile_formula
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (hscale : 2 ≤ scale) (y : Euclidean 2) :
    mssP4FineNormalizedRegularProfile C q r scale n nu hscale y =
      mssP4FineNormalizedCarrier q (Real.sqrt scale) y *
        (mssP4FineNormalizedLatticeFactor q r (Real.sqrt scale) nu y *
          (mssP4FineNormalizedNormalFactor C q r (Real.sqrt scale) n y *
            mssP4FineNormalizedCoarseFactor C q r (Real.sqrt scale) y)) := by
  have hscalePos : 0 < scale := by linarith
  have hsmul := aux_p4_inv_smul_sqrt_smul hscalePos y
  have hcoord :
      mssP4FineRegularCoordinate q r scale (Real.sqrt scale • y) - (nu : Real) =
        (64 : Real) *
          (Real.sqrt scale * mssP4BoundedChartAngle q
            ((Real.sqrt scale)⁻¹ • y)) +
          (4 * Real.sqrt scale * (96 - (r.val : Real)) - (nu : Real)) := by
    unfold mssP4FineRegularCoordinate
    rw [hsmul]
    ring
  have hnormal :
      (Real.sqrt scale)⁻¹ *
          mssP4FineNormalCoordinate C q r scale (Real.sqrt scale • y) - (n : Real) =
        Real.sqrt scale *
          (mssP4FineRadialTimeCutoffs C q r).normalExtension
            ((Real.sqrt scale)⁻¹ • y) - (n : Real) := by
    have hroot : Real.sqrt scale ≠ 0 := Real.sqrt_ne_zero'.mpr hscalePos
    have hsquare : Real.sqrt scale * Real.sqrt scale = scale := by
      nlinarith [Real.sq_sqrt hscalePos.le]
    have hscalar : (Real.sqrt scale)⁻¹ * scale = Real.sqrt scale := by
      calc
        (Real.sqrt scale)⁻¹ * scale =
            (Real.sqrt scale)⁻¹ *
              (Real.sqrt scale * Real.sqrt scale) := by rw [hsquare]
        _ = Real.sqrt scale := by field_simp [hroot]
    rw [mssP4FineNormalCoordinate_apply, hsmul]
    calc
      (Real.sqrt scale)⁻¹ *
          (scale * (mssP4FineRadialTimeCutoffs C q r).normalExtension
            ((Real.sqrt scale)⁻¹ • y)) - (n : Real) =
          ((Real.sqrt scale)⁻¹ * scale) *
            (mssP4FineRadialTimeCutoffs C q r).normalExtension
              ((Real.sqrt scale)⁻¹ • y) - (n : Real) := by ring
      _ = Real.sqrt scale *
          (mssP4FineRadialTimeCutoffs C q r).normalExtension
            ((Real.sqrt scale)⁻¹ • y) - (n : Real) := by rw [hscalar]
  rw [mssP4FineNormalizedRegularProfile_apply,
    mssP4FineRegularSpatialProfileAux_apply,
    mssP4FineRegularChiReal, if_pos hscale, hsmul, hcoord,
    mssP4FineSmoothNormalRadialFactor, hnormal,
    mssP4FineNormalizedCarrier, mssP4FineNormalizedLatticeFactor,
    mssP4FineNormalizedNormalFactor, mssP4FineNormalizedCoarseFactor,
    mssP4FineChiCarrier_apply]
  simp only [Function.comp_def, mssP4UnitLatticeTransitionSchwartz_apply,
    smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The normalized profile is exactly the concrete spatial-profile field of
the p=4 kernel data, evaluated at the inverse dilation. -/
private theorem mssP4FineNormalizedRegularProfile_eq_spatialProfile
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (hscale : 2 ≤ scale) (y : Euclidean 2) :
    mssP4FineNormalizedRegularProfile C q r scale n nu hscale y =
      mssP4FineSpatialProfile C q r scale n nu (Real.sqrt scale • y) := by
  rw [mssP4FineNormalizedRegularProfile_apply,
    mssP4FineRegularSpatialProfileAux_eq]
  simp only [mssP4FineSpatialProfile, dif_pos hscale]

private theorem mssP4FineNormalizedCarrier_contDiff
    (q : Fin 4) (R : Real) :
    ContDiff Real (⊤ : ℕ∞) (mssP4FineNormalizedCarrier q R) := by
  unfold mssP4FineNormalizedCarrier
  exact ((mssP4FineChiCarrier q).smooth (⊤ : ℕ∞)).comp
    (contDiff_id.const_smul R⁻¹)

private theorem mssP4FineNormalizedLatticeFactor_contDiff
    (q : Fin 4) (r : Fin 193) (R : Real) (nu : Int) :
    ContDiff Real (⊤ : ℕ∞)
      (mssP4FineNormalizedLatticeFactor q r R nu) := by
  unfold mssP4FineNormalizedLatticeFactor
  apply (mssP4UnitLatticeTransitionSchwartz.smooth (⊤ : ℕ∞)).comp
  exact (((((mssP4BoundedChartAngle q).smooth (⊤ : ℕ∞)).comp
    (contDiff_id.const_smul R⁻¹)).const_smul R).const_smul 64).add contDiff_const

private theorem mssP4FineNormalizedNormalFactor_contDiff
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (R : Real) (n : Int) :
    ContDiff Real (⊤ : ℕ∞)
      (mssP4FineNormalizedNormalFactor C q r R n) := by
  unfold mssP4FineNormalizedNormalFactor
  apply ((mssP4FineRadialTimeCutoffs C q r).radial.smooth (⊤ : ℕ∞)).comp
  exact ((((mssP4FineRadialTimeCutoffs C q r).normalExtension.smooth
    (⊤ : ℕ∞)).comp (contDiff_id.const_smul R⁻¹)).const_smul R).sub contDiff_const

private theorem mssP4FineNormalizedCoarseFactor_contDiff
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193) (R : Real) :
    ContDiff Real (⊤ : ℕ∞)
      (mssP4FineNormalizedCoarseFactor C q r R) := by
  unfold mssP4FineNormalizedCoarseFactor
  exact ((mssP4CoarseAmplitude C q r).smooth (⊤ : ℕ∞)).comp
    (contDiff_id.const_smul R⁻¹)

/-- At its natural spatial scale, every derivative of the concrete p=4
packet has a global bound independent of scale and of both lattice labels. -/
private theorem exists_mssP4FineNormalizedRegularProfile_iteratedFDeriv_uniform_bound
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193) (k : Nat) :
    ∃ B : Real, 0 ≤ B ∧ ∀ (scale : Real) (n nu : Int) (hscale : 2 ≤ scale)
      (y : Euclidean 2),
      ‖iteratedFDeriv Real k
        (mssP4FineNormalizedRegularProfile C q r scale n nu hscale :
          Euclidean 2 → Complex) y‖ ≤ B := by
  let FC : Nat → Real := fun i =>
    SchwartzMap.seminorm Real 0 i (mssP4FineChiCarrier q)
  have hFC0 (i : Nat) : 0 ≤ FC i := by
    dsimp [FC]
    exact (norm_nonneg (iteratedFDeriv Real i
      (mssP4FineChiCarrier q : Euclidean 2 → Complex) 0)).trans
      ((mssP4FineChiCarrier q).norm_iteratedFDeriv_le_seminorm Real i 0)
  let FL : Nat → Real := fun i =>
    (aux_p4_exists_outer_comp_rescaled_schwartz_bound
      mssP4UnitLatticeTransitionSchwartz (mssP4BoundedChartAngle q) 64 i).choose
  have hFL0 (i : Nat) : 0 ≤ FL i := by
    dsimp [FL]
    exact (aux_p4_exists_outer_comp_rescaled_schwartz_bound
      mssP4UnitLatticeTransitionSchwartz (mssP4BoundedChartAngle q) 64 i).choose_spec.1
  let FN : Nat → Real := fun i =>
    (aux_p4_exists_outer_comp_rescaled_schwartz_bound
      (mssP4FineRadialTimeCutoffs C q r).radial
      (mssP4FineRadialTimeCutoffs C q r).normalExtension 1 i).choose
  have hFN0 (i : Nat) : 0 ≤ FN i := by
    dsimp [FN]
    exact (aux_p4_exists_outer_comp_rescaled_schwartz_bound
      (mssP4FineRadialTimeCutoffs C q r).radial
      (mssP4FineRadialTimeCutoffs C q r).normalExtension 1 i).choose_spec.1
  let FA : Nat → Real := fun i =>
    SchwartzMap.seminorm Real 0 i (mssP4CoarseAmplitude C q r)
  have hFA0 (i : Nat) : 0 ≤ FA i := by
    dsimp [FA]
    exact (norm_nonneg (iteratedFDeriv Real i
      (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex) 0)).trans
      ((mssP4CoarseAmplitude C q r).norm_iteratedFDeriv_le_seminorm Real i 0)
  let FR : Nat → Real := fun i => aux_p4_leibnizBound FN FA i
  let FT : Nat → Real := fun i => aux_p4_leibnizBound FL FR i
  let B : Real := aux_p4_leibnizBound FC FT k
  have hFR0 (i : Nat) : 0 ≤ FR i := by
    dsimp [FR]
    exact aux_p4_leibnizBound_nonneg FN FA hFN0 hFA0 i
  have hFT0 (i : Nat) : 0 ≤ FT i := by
    dsimp [FT]
    exact aux_p4_leibnizBound_nonneg FL FR hFL0 hFR0 i
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact aux_p4_leibnizBound_nonneg FC FT hFC0 hFT0 k
  refine ⟨B, hB0, ?_⟩
  intro scale n nu hscale y
  let R : Real := Real.sqrt scale
  have hR : 1 ≤ R := by
    dsimp [R]
    exact Real.one_le_sqrt.mpr (by linarith)
  have hcarrier (i : Nat) (z : Euclidean 2) :
      ‖iteratedFDeriv Real i (mssP4FineNormalizedCarrier q R) z‖ ≤ FC i := by
    dsimp [FC]
    change ‖iteratedFDeriv Real i
      (fun w : Euclidean 2 =>
        (mssP4FineChiCarrier q : Euclidean 2 → Complex) (R⁻¹ • w)) z‖ ≤ _
    exact aux_p4_norm_iteratedFDeriv_schwartz_comp_inv_smul_le
      (mssP4FineChiCarrier q) hR i z
  have hlattice (i : Nat) (z : Euclidean 2) :
      ‖iteratedFDeriv Real i
        (mssP4FineNormalizedLatticeFactor q r R nu) z‖ ≤ FL i := by
    dsimp [FL]
    change ‖iteratedFDeriv Real i
      (mssP4UnitLatticeTransitionSchwartz ∘ fun w : Euclidean 2 =>
        (64 : Real) • (R • mssP4BoundedChartAngle q (R⁻¹ • w)) +
          (4 * R * (96 - (r.val : Real)) - (nu : Real))) z‖ ≤ _
    exact (aux_p4_exists_outer_comp_rescaled_schwartz_bound
      mssP4UnitLatticeTransitionSchwartz (mssP4BoundedChartAngle q) 64 i).choose_spec.2
        R (4 * R * (96 - (r.val : Real)) - (nu : Real)) z hR
  have hnormal (i : Nat) (z : Euclidean 2) :
      ‖iteratedFDeriv Real i
        (mssP4FineNormalizedNormalFactor C q r R n) z‖ ≤ FN i := by
    dsimp [FN]
    change ‖iteratedFDeriv Real i
      ((mssP4FineRadialTimeCutoffs C q r).radial ∘ fun w : Euclidean 2 =>
        R • (mssP4FineRadialTimeCutoffs C q r).normalExtension (R⁻¹ • w) -
          (n : Real)) z‖ ≤ _
    convert (aux_p4_exists_outer_comp_rescaled_schwartz_bound
      (mssP4FineRadialTimeCutoffs C q r).radial
      (mssP4FineRadialTimeCutoffs C q r).normalExtension 1 i).choose_spec.2
        R (-(n : Real)) z hR using 1 <;>
      simp only [Function.comp_def, one_smul, sub_eq_add_neg]
  have hamplitude (i : Nat) (z : Euclidean 2) :
      ‖iteratedFDeriv Real i
        (mssP4FineNormalizedCoarseFactor C q r R) z‖ ≤ FA i := by
    dsimp [FA]
    change ‖iteratedFDeriv Real i
      (fun w : Euclidean 2 =>
        (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex) (R⁻¹ • w)) z‖ ≤ _
    exact aux_p4_norm_iteratedFDeriv_schwartz_comp_inv_smul_le
      (mssP4CoarseAmplitude C q r) hR i z
  have hright (i : Nat) (z : Euclidean 2) :
      ‖iteratedFDeriv Real i
        (fun w : Euclidean 2 =>
          mssP4FineNormalizedNormalFactor C q r R n w *
            mssP4FineNormalizedCoarseFactor C q r R w) z‖ ≤ FR i := by
    dsimp [FR]
    exact aux_p4_norm_iteratedFDeriv_mul_le_of_bounds
      (mssP4FineNormalizedNormalFactor C q r R n)
      (mssP4FineNormalizedCoarseFactor C q r R)
      (mssP4FineNormalizedNormalFactor_contDiff C q r R n)
      (mssP4FineNormalizedCoarseFactor_contDiff C q r R)
      FN FA hnormal hamplitude i z
  have htail (i : Nat) (z : Euclidean 2) :
      ‖iteratedFDeriv Real i
        (fun w : Euclidean 2 =>
          mssP4FineNormalizedLatticeFactor q r R nu w *
            (mssP4FineNormalizedNormalFactor C q r R n w *
              mssP4FineNormalizedCoarseFactor C q r R w)) z‖ ≤ FT i := by
    dsimp [FT]
    exact aux_p4_norm_iteratedFDeriv_mul_le_of_bounds
      (mssP4FineNormalizedLatticeFactor q r R nu)
      (fun w : Euclidean 2 =>
        mssP4FineNormalizedNormalFactor C q r R n w *
          mssP4FineNormalizedCoarseFactor C q r R w)
      (mssP4FineNormalizedLatticeFactor_contDiff q r R nu)
      ((mssP4FineNormalizedNormalFactor_contDiff C q r R n).mul
        (mssP4FineNormalizedCoarseFactor_contDiff C q r R))
      FL FR hlattice hright i z
  have hformula :
      (mssP4FineNormalizedRegularProfile C q r scale n nu hscale :
        Euclidean 2 → Complex) =
        fun w : Euclidean 2 =>
          mssP4FineNormalizedCarrier q R w *
            (mssP4FineNormalizedLatticeFactor q r R nu w *
              (mssP4FineNormalizedNormalFactor C q r R n w *
                mssP4FineNormalizedCoarseFactor C q r R w)) := by
    ext w
    dsimp [R]
    exact mssP4FineNormalizedRegularProfile_formula C q r scale n nu hscale w
  rw [hformula]
  dsimp [B]
  exact aux_p4_norm_iteratedFDeriv_mul_le_of_bounds
    (mssP4FineNormalizedCarrier q R)
    (fun w : Euclidean 2 =>
      mssP4FineNormalizedLatticeFactor q r R nu w *
        (mssP4FineNormalizedNormalFactor C q r R n w *
          mssP4FineNormalizedCoarseFactor C q r R w))
    (mssP4FineNormalizedCarrier_contDiff q R)
    ((mssP4FineNormalizedLatticeFactor_contDiff q r R nu).mul
      ((mssP4FineNormalizedNormalFactor_contDiff C q r R n).mul
        (mssP4FineNormalizedCoarseFactor_contDiff C q r R)))
    FC FT hcarrier htail k y

/-- The existing packet-ray localization becomes a fixed-radius support
container after the natural `sqrt scale` pullback. -/
private theorem mssP4FineNormalizedRegularProfile_support_subset_closedBall
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (gamma : MSSAdmissibleGamma) (scale : Real) (n nu : Int)
    (hscale : 2 ≤ scale) (hn : n ∈ relevantRadialIndexEnumeration scale)
    (hnu : nu ∈ (mssP4FineKernelData C q r gamma).angularIndices scale) :
    Function.support
      (mssP4FineNormalizedRegularProfile C q r scale n nu hscale :
        Euclidean 2 → Complex) ⊆
      Metric.closedBall ((n : Real) • mssP4FineDirection r scale nu)
        (19 / 4 : Real) := by
  have hscalePos : 0 < scale := by linarith
  have hrootPos : 0 < Real.sqrt scale := Real.sqrt_pos.2 hscalePos
  intro y hy
  have hspatial :
      mssP4FineSpatialProfile C q r scale n nu (Real.sqrt scale • y) ≠ 0 := by
    rw [← mssP4FineNormalizedRegularProfile_eq_spatialProfile
      C q r scale n nu hscale y]
    exact hy
  have hdataSpatial :
      (mssP4FineKernelData C q r gamma).spatialProfile scale n nu
        (Real.sqrt scale • y) ≠ 0 := by
    simpa [mssP4FineKernelData] using hspatial
  have hpacket := mss_spatialProfile_center_ne_packet_ray
    (mssP4FineKernelData C q r gamma) hscale n nu hn hnu
      (Real.sqrt scale • y) hdataSpatial
  have hpacket' :
      ‖Real.sqrt scale • y - ((n : Real) * Real.sqrt scale) •
          mssP4FineDirection r scale nu‖ ≤
        (19 / 4 : Real) * Real.sqrt scale := by
    convert hpacket using 1 <;>
      norm_num [mssP4FineKernelData, mssP4FineCutoffData]
  rw [Metric.mem_closedBall, dist_eq_norm]
  have heq : y - (n : Real) • mssP4FineDirection r scale nu =
      (Real.sqrt scale)⁻¹ •
        (Real.sqrt scale • y - ((n : Real) * Real.sqrt scale) •
          mssP4FineDirection r scale nu) := by
    symm
    rw [smul_sub, smul_smul, smul_smul]
    have hcancel : (Real.sqrt scale)⁻¹ * Real.sqrt scale = 1 :=
      inv_mul_cancel₀ hrootPos.ne'
    have hlabel : (Real.sqrt scale)⁻¹ *
        ((n : Real) * Real.sqrt scale) = (n : Real) := by
      calc
        (Real.sqrt scale)⁻¹ * ((n : Real) * Real.sqrt scale) =
            (n : Real) * ((Real.sqrt scale)⁻¹ * Real.sqrt scale) := by ring
        _ = (n : Real) := by rw [hcancel]; ring
    rw [hcancel, hlabel, one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hrootPos)]
  calc
    (Real.sqrt scale)⁻¹ *
        ‖Real.sqrt scale • y - ((n : Real) * Real.sqrt scale) •
          mssP4FineDirection r scale nu‖ ≤
        (Real.sqrt scale)⁻¹ * ((19 / 4 : Real) * Real.sqrt scale) :=
      mul_le_mul_of_nonneg_left hpacket' (inv_nonneg.mpr hrootPos.le)
    _ = 19 / 4 := by field_simp [hrootPos.ne']

/-- Exact derivative-integral scaling from the normalized p=4 packet back
to the literal spatial profile. -/
private theorem integral_norm_iteratedFDeriv_mssP4FineSpatialProfile_eq_normalized
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (n nu : Int) (hscale : 2 ≤ scale) (k : Nat) :
    (∫ x : Euclidean 2,
      ‖iteratedFDeriv Real k
        (mssP4FineSpatialProfile C q r scale n nu :
          Euclidean 2 → Complex) x‖) =
      (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ k *
        ∫ y : Euclidean 2,
          ‖iteratedFDeriv Real k
            (mssP4FineNormalizedRegularProfile C q r scale n nu hscale :
              Euclidean 2 → Complex) y‖ := by
  have hscalePos : 0 < scale := by linarith
  have hrootPos : 0 < Real.sqrt scale := Real.sqrt_pos.2 hscalePos
  have hfun :
      (mssP4FineSpatialProfile C q r scale n nu : Euclidean 2 → Complex) =
        fun x : Euclidean 2 =>
          mssP4FineNormalizedRegularProfile C q r scale n nu hscale
            ((Real.sqrt scale)⁻¹ • x) := by
    funext x
    rw [mssP4FineNormalizedRegularProfile_eq_spatialProfile]
    rw [smul_smul, mul_inv_cancel₀ hrootPos.ne', one_smul]
  have hsmooth : ContDiff Real k
      (fun x : Euclidean 2 =>
        mssP4FineNormalizedRegularProfile C q r scale n nu hscale
          ((Real.sqrt scale)⁻¹ • x)) := by
    exact
      ((mssP4FineNormalizedRegularProfile C q r scale n nu hscale).smooth
        (k : ℕ∞)).comp (contDiff_id.const_smul (Real.sqrt scale)⁻¹)
  have hchain : iteratedFDeriv Real k
      (fun x : Euclidean 2 =>
        mssP4FineNormalizedRegularProfile C q r scale n nu hscale
          ((Real.sqrt scale)⁻¹ • x)) =
      fun x => (Real.sqrt scale)⁻¹ ^ k •
        iteratedFDeriv Real k
          (mssP4FineNormalizedRegularProfile C q r scale n nu hscale :
            Euclidean 2 → Complex)
          ((Real.sqrt scale)⁻¹ • x) := by
    exact iteratedFDeriv_comp_const_smul (Real.sqrt scale)⁻¹
      ((mssP4FineNormalizedRegularProfile C q r scale n nu hscale).smooth
        (k : ℕ∞))
  rw [hfun]
  change (∫ x : Euclidean 2,
    ‖iteratedFDeriv Real k
      (fun z : Euclidean 2 =>
        mssP4FineNormalizedRegularProfile C q r scale n nu hscale
          ((Real.sqrt scale)⁻¹ • z)) x‖) = _
  simp_rw [hchain]
  rw [show (fun x : Euclidean 2 =>
      ‖(Real.sqrt scale)⁻¹ ^ k •
        iteratedFDeriv Real k
          (mssP4FineNormalizedRegularProfile C q r scale n nu hscale :
            Euclidean 2 → Complex)
          ((Real.sqrt scale)⁻¹ • x)‖) =
      fun x => (Real.sqrt scale)⁻¹ ^ k *
        ‖iteratedFDeriv Real k
          (mssP4FineNormalizedRegularProfile C q r scale n nu hscale :
            Euclidean 2 → Complex)
          ((Real.sqrt scale)⁻¹ • x)‖ by
        funext x
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hrootPos.le) k)],
    integral_const_mul]
  rw [Auto.Spherical.SurfaceMeasureDecay.integral_norm_comp_smul_eq 2
    (iteratedFDeriv Real k
      (mssP4FineNormalizedRegularProfile C q r scale n nu hscale :
        Euclidean 2 → Complex))
    (inv_pos.mpr hrootPos)]
  have hinvpow : (((Real.sqrt scale)⁻¹) ^ 2)⁻¹ =
      (Real.sqrt scale) ^ 2 := by
    rw [← inv_pow, inv_inv]
  rw [hinvpow]
  ring

/-- The concrete p=4 fine packets satisfy the fixed-smooth-cutoff condition
required by the MSS fine-square argument.  The proof normalizes each packet
to a fixed-radius ball, uses the four-factor derivative envelope above, and
then transports the estimate back through the exact spatial dilation. -/
private theorem mssP4FineUniformRegularity
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (gamma : MSSAdmissibleGamma) :
    MSSFineSpatialProfileUniformRegularity (mssP4FineKernelData C q r gamma) := by
  refine ⟨?_⟩
  intro k
  obtain ⟨B, hB0, hB⟩ :=
    exists_mssP4FineNormalizedRegularProfile_iteratedFDeriv_uniform_bound C q r k
  let V : Real := volume.real (Metric.closedBall (0 : Euclidean 2) (19 / 4 : Real))
  let A : Real := B * V
  have hV0 : 0 ≤ V := by
    dsimp [V]
    exact measureReal_nonneg
  have hA0 : 0 ≤ A := mul_nonneg hB0 hV0
  refine ⟨A, hA0, ?_⟩
  intro scale n nu hscale hn hnu
  change (∫ x : Euclidean 2,
    ‖iteratedFDeriv Real k
      (mssP4FineSpatialProfile C q r scale n nu : Euclidean 2 → Complex) x‖) ≤
      A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ k
  let Q : SchwartzMap (Euclidean 2) Complex :=
    mssP4FineNormalizedRegularProfile C q r scale n nu hscale
  let center : Euclidean 2 := (n : Real) • mssP4FineDirection r scale nu
  let K : Set (Euclidean 2) := Metric.closedBall center (19 / 4 : Real)
  have hQpoint (y : Euclidean 2) :
      ‖iteratedFDeriv Real k (Q : Euclidean 2 → Complex) y‖ ≤ B := by
    dsimp [Q]
    exact hB scale n nu hscale y
  have hQsupport : Function.support (Q : Euclidean 2 → Complex) ⊆ K := by
    dsimp [Q, K, center]
    exact mssP4FineNormalizedRegularProfile_support_subset_closedBall
      C q r gamma scale n nu hscale hn hnu
  have hQderivSupport : Function.support
      (iteratedFDeriv Real k (Q : Euclidean 2 → Complex)) ⊆ K := by
    apply (support_iteratedFDeriv_subset k).trans
    change closure (Function.support (Q : Euclidean 2 → Complex)) ⊆ K
    exact closure_minimal hQsupport (by
      dsimp [K]
      exact Metric.isClosed_closedBall)
  have hQintegrable : Integrable (fun y : Euclidean 2 =>
      ‖iteratedFDeriv Real k (Q : Euclidean 2 → Complex) y‖) volume := by
    dsimp [Q]
    simpa using SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
      (mssP4FineNormalizedRegularProfile C q r scale n nu hscale) 0 k
  have hKmeas : MeasurableSet K := by
    dsimp [K]
    exact measurableSet_closedBall
  have hKfinite : volume K ≠ (⊤ : ENNReal) := by
    dsimp [K]
    exact measure_closedBall_lt_top.ne
  have hQintegral :
      (∫ y : Euclidean 2,
        ‖iteratedFDeriv Real k (Q : Euclidean 2 → Complex) y‖) ≤
        B * (volume K).toReal := by
    exact _root_.Auto.MikhlinHormander.integral_norm_le_of_support_subset_of_norm_le
        (iteratedFDeriv Real k (Q : Euclidean 2 → Complex)) K hKmeas hKfinite
        hQintegrable hQpoint hQderivSupport
  have hKvolume : (volume K).toReal = V := by
    dsimp [K, center, V]
    simpa [Measure.real] using
      (Measure.addHaar_real_closedBall_center volume
        ((n : Real) • mssP4FineDirection r scale nu) (19 / 4 : Real))
  have hQintegral' :
      (∫ y : Euclidean 2,
        ‖iteratedFDeriv Real k (Q : Euclidean 2 → Complex) y‖) ≤ B * V := by
    calc
      (∫ y : Euclidean 2,
        ‖iteratedFDeriv Real k (Q : Euclidean 2 → Complex) y‖) ≤
          B * (volume K).toReal := hQintegral
      _ = B * V := by rw [hKvolume]
  have hscaleIdentity :
      (∫ x : Euclidean 2,
        ‖iteratedFDeriv Real k
          (mssP4FineSpatialProfile C q r scale n nu :
            Euclidean 2 → Complex) x‖) =
        (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ k *
          ∫ y : Euclidean 2,
            ‖iteratedFDeriv Real k (Q : Euclidean 2 → Complex) y‖ := by
    dsimp [Q]
    exact integral_norm_iteratedFDeriv_mssP4FineSpatialProfile_eq_normalized
      C q r scale n nu hscale k
  have hfactor : 0 ≤ (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ k := by
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (inv_nonneg.mpr
      (Real.sqrt_nonneg _)) _)
  calc
    (∫ x : Euclidean 2,
      ‖iteratedFDeriv Real k
        (mssP4FineSpatialProfile C q r scale n nu : Euclidean 2 → Complex) x‖) =
        (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ k *
          ∫ y : Euclidean 2,
            ‖iteratedFDeriv Real k (Q : Euclidean 2 → Complex) y‖ := hscaleIdentity
    _ ≤ (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ k * (B * V) :=
      mul_le_mul_of_nonneg_left hQintegral' hfactor
    _ = A * (Real.sqrt scale) ^ 2 * ((Real.sqrt scale)⁻¹) ^ k := by
      dsimp [A]
      ring

/-- The concrete gamma-family behind one member of the finite endpoint
atlas.  The cutoff core is fixed; only the admissible wave-front thickness
varies. -/
private noncomputable def mssP4FineWavefrontFamily
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193) :
    MSSWavefrontGammaFamily (mssP4FineCutoffData C q r) where
  data := mssP4FineKernelData C q r
  data_core := by
    intro gamma
    rfl
  data_gamma := by
    intro gamma
    rfl
  realization := mssP4FineRawProfileRealization C q r
  regularity := by
    intro gamma
    exact (mssP4FineUniformRegularity C q r gamma).toPolynomialRegularity

/-- A fixed admissible thickness used to expose one concrete datum from the
gamma-family.  Recombination itself continues to use the entire family. -/
private noncomputable def mssP4BaseGamma : MSSAdmissibleGamma :=
  ⟨(1 / 20 : Real), by norm_num, by norm_num⟩

/-- One fully certified member of the finite coarse endpoint atlas. -/
private noncomputable def mssP4StructuredConicDatum
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193) : MSSStructuredConicDatum where
  D := mssP4FineKernelData C q r mssP4BaseGamma
  angular := by
    simpa [mssP4FineKernelData] using mssP4FineAngularData C q r
  recombination :=
    { wavefrontFamily := mssP4FineWavefrontFamily C q r }
  uniform := mssP4FineUniformRegularity C q r mssP4BaseGamma
  timeSlab := mssP4FineKernelData_hasLightRayTimeSlabSupport C q r mssP4BaseGamma

/-- The already verified structured conic estimate specialized to one
concrete endpoint-atlas member. -/
private theorem mssP4ConicL4Estimate
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193) :
    ∀ eta : Real, 0 < eta → ∃ K : Real, 0 < K ∧
      ∀ scale : Real, 2 ≤ scale → ∀ f : SchwartzMap (Euclidean 2) Complex,
        eLpNorm
            (conicOperator scale
              ((mssP4StructuredConicDatum C q r).D.radialTime.amplitude :
                Euclidean 2 → Complex)
              ((mssP4StructuredConicDatum C q r).D.radialTime.time :
                Real → Complex)
              (f : Euclidean 2 → Complex))
            (4 : ENNReal) volume ≤
          ENNReal.ofReal (K * scale ^ ((1 / 8 : Real) + eta)) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
  exact mssConicL4Estimate_of_structuredData
    (mssP4StructuredConicDatum C q r).D
    (mssP4StructuredConicDatum C q r).angular
    (mssP4StructuredConicDatum C q r).recombination
    (mssP4StructuredConicDatum C q r).uniform
    (mssP4StructuredConicDatum C q r).timeSlab

/-- Every concrete coarse conic summand is jointly continuous.  This gives
the local measurability needed to take the finite `L⁴` triangle inequality;
the proof is the standard dominated inverse-Fourier continuity argument,
with the compact coarse amplitude providing the dominating Schwartz factor. -/
private theorem continuous_mssP4CoarseConicOperator
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (hscale : 0 < scale)
    (f : SchwartzMap (Euclidean 2) Complex) :
    Continuous
      (conicOperator scale (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex)
        (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex)) := by
  let B : SchwartzMap (Euclidean 2) Complex :=
    SchwartzMap.smulLeftCLM Complex
      (mssP4FineScaledCoarseAmplitude C q r scale hscale :
        Euclidean 2 → Complex)
      (FourierTransform.fourier f)
  have hB : ∀ xi : Euclidean 2, B xi =
      mssP4CoarseAmplitude C q r (scale⁻¹ • xi) *
        FourierTransform.fourier (f : Euclidean 2 → Complex) xi := by
    intro xi
    unfold B
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (mssP4FineScaledCoarseAmplitude C q r scale hscale).hasTemperateGrowth,
      mssP4FineScaledCoarseAmplitude_apply]
    simp only [smul_eq_mul, SchwartzMap.fourier_coe]
  let m : Real → Euclidean 2 → Complex := fun t xi =>
    B xi * halfWaveMultiplier WaveSign.plus t xi
  let U : Real × Euclidean 2 → Complex := fun p =>
    FourierTransform.fourierInv (m p.1) p.2
  have hU : Continuous U := by
    change Continuous (Function.uncurry (fun t x =>
      FourierTransform.fourierInv (m t) x))
    apply Auto.Spherical.MSSKakeya.continuous_uncurry_fourierInv_of_dominated m
      (bound := fun xi => ‖B xi‖)
    · intro xi
      have hphase : Continuous (fun p : Real × Euclidean 2 =>
          (Real.fourierChar (inner Real xi p.2) : Complex)) := by
        fun_prop
      have hm : Continuous (fun p : Real × Euclidean 2 => m p.1 xi) := by
        change Continuous (fun p : Real × Euclidean 2 =>
          B xi * halfWaveMultiplier WaveSign.plus p.1 xi)
        exact continuous_const.mul (by
          unfold halfWaveMultiplier
          fun_prop)
      exact hphase.smul hm
    · intro p
      have hphase : Continuous (fun xi : Euclidean 2 =>
          (Real.fourierChar (inner Real xi p.2) : Complex)) := by
        fun_prop
      have hm : Continuous (fun xi : Euclidean 2 => m p.1 xi) := by
        change Continuous (fun xi : Euclidean 2 =>
          B xi * halfWaveMultiplier WaveSign.plus p.1 xi)
        have hhalf : Continuous (halfWaveMultiplier WaveSign.plus p.1) := by
          unfold halfWaveMultiplier
          fun_prop
        exact B.continuous.mul hhalf
      exact (hphase.smul hm).aestronglyMeasurable
    · intro p xi
      have hchar (u : Real) : ‖(Real.fourierChar u : Complex)‖ = 1 := by
        rw [Real.fourierChar_apply, Complex.norm_exp]
        norm_num
      change ‖(Real.fourierChar (inner Real xi p.2) : Complex) •
        (B xi * halfWaveMultiplier WaveSign.plus p.1 xi)‖ ≤ ‖B xi‖
      rw [norm_smul, hchar, one_mul, norm_mul,
        norm_halfWaveMultiplier, mul_one]
    · exact B.integrable.norm
  have hrepr : conicOperator scale
      (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex)
      (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex) =
      fun z => mssCanonicalTime z.2 * U (z.2, z.1) := by
    funext z
    unfold U
    unfold conicOperator
    apply congrArg (fun h : Euclidean 2 → Complex =>
      mssCanonicalTime z.2 * FourierTransform.fourierInv h z.1)
    funext xi
    dsimp [m]
    rw [hB xi]
    ring
  rw [hrepr]
  have hswap : Continuous (fun z : WaveSpaceTime => (z.2, z.1)) :=
    continuous_snd.prodMk continuous_fst
  have hUspace : Continuous (fun z : WaveSpaceTime => U (z.2, z.1)) :=
    hU.comp hswap
  have htime : Continuous (fun z : WaveSpaceTime => mssCanonicalTime z.2) :=
    mssCanonicalTime.continuous.comp continuous_snd
  exact htime.mul hUspace

/-- The frequency integrand of one concrete coarse conic term is integrable.
Compact support of the coarse amplitude reduces this to the integrable
Schwartz product with the unit-modulus half-wave phase. -/
private theorem integrable_mssP4CoarseSpectrum
    (C : lpCutoffs 2) (q : Fin 4) (r : Fin 193)
    (scale : Real) (hscale : 0 < scale)
    (f : SchwartzMap (Euclidean 2) Complex) (t : Real) :
    Integrable (fun xi : Euclidean 2 =>
      mssP4CoarseAmplitude C q r (scale⁻¹ • xi) *
        halfWaveMultiplier WaveSign.plus t xi *
          FourierTransform.fourier (f : Euclidean 2 → Complex) xi) volume := by
  let B : SchwartzMap (Euclidean 2) Complex :=
    SchwartzMap.smulLeftCLM Complex
      (mssP4FineScaledCoarseAmplitude C q r scale hscale :
        Euclidean 2 → Complex)
      (FourierTransform.fourier f)
  have hB : ∀ xi : Euclidean 2, B xi =
      mssP4CoarseAmplitude C q r (scale⁻¹ • xi) *
        FourierTransform.fourier (f : Euclidean 2 → Complex) xi := by
    intro xi
    unfold B
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (mssP4FineScaledCoarseAmplitude C q r scale hscale).hasTemperateGrowth,
      mssP4FineScaledCoarseAmplitude_apply]
    simp only [smul_eq_mul, SchwartzMap.fourier_coe]
  have hrepr : (fun xi : Euclidean 2 =>
      mssP4CoarseAmplitude C q r (scale⁻¹ • xi) *
        halfWaveMultiplier WaveSign.plus t xi *
          FourierTransform.fourier (f : Euclidean 2 → Complex) xi) =
      fun xi => B xi * halfWaveMultiplier WaveSign.plus t xi := by
    funext xi
    rw [hB xi]
    ring
  rw [hrepr]
  refine Integrable.mono' B.integrable.norm ?_ ?_
  · have hhalf : Continuous (halfWaveMultiplier WaveSign.plus t) := by
      unfold halfWaveMultiplier
      fun_prop
    exact (B.continuous.mul hhalf).aestronglyMeasurable
  · filter_upwards with xi
    rw [norm_mul, norm_halfWaveMultiplier, mul_one]

/-- The finite coarse angular partition commutes with the conic Fourier
formula.  This is an exact identity, not an estimate. -/
private theorem sum_mssP4CoarseConicOperator
    (C : lpCutoffs 2) (scale : Real) (hscale : 0 < scale)
    (f : SchwartzMap (Euclidean 2) Complex) :
    (∑ q : Fin 4, ∑ r : Fin 193,
      conicOperator scale (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex)
        (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex)) =
      conicOperator scale (mssP4ScaledBandpassAmplitude C : Euclidean 2 → Complex)
        (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex) := by
  classical
  funext z
  let g : Fin 4 × Fin 193 → Euclidean 2 → Complex := fun qr xi =>
    mssP4CoarseAmplitude C qr.1 qr.2 (scale⁻¹ • xi) *
      halfWaveMultiplier WaveSign.plus z.2 xi *
        FourierTransform.fourier (f : Euclidean 2 → Complex) xi
  have hg : ∀ qr ∈ (Finset.univ : Finset (Fin 4)).product Finset.univ,
      Integrable (g qr) volume := by
    intro qr _
    exact integrable_mssP4CoarseSpectrum C qr.1 qr.2 scale hscale f z.2
  have hfourier :=
    _root_.Auto.MikhlinHormander.fourierInv_finset_sum_of_integrable
      ((Finset.univ : Finset (Fin 4)).product Finset.univ) g hg z.1
  have hsum : (fun xi : Euclidean 2 =>
      ∑ qr ∈ (Finset.univ : Finset (Fin 4)).product Finset.univ, g qr xi) =
      fun xi => mssP4ScaledBandpassAmplitude C (scale⁻¹ • xi) *
        halfWaveMultiplier WaveSign.plus z.2 xi *
          FourierTransform.fourier (f : Euclidean 2 → Complex) xi := by
    funext xi
    have hprod := Finset.sum_product (Finset.univ : Finset (Fin 4))
      (Finset.univ : Finset (Fin 193)) (fun qr : Fin 4 × Fin 193 => g qr xi)
    rw [show (∑ qr ∈ (Finset.univ : Finset (Fin 4)).product Finset.univ,
        g qr xi) = ∑ q : Fin 4, ∑ r : Fin 193, g (q, r) xi by
      simpa using hprod]
    simp only [g]
    calc
      (∑ q : Fin 4, ∑ r : Fin 193,
          mssP4CoarseAmplitude C q r (scale⁻¹ • xi) *
            halfWaveMultiplier WaveSign.plus z.2 xi *
              FourierTransform.fourier (f : Euclidean 2 → Complex) xi) =
          (∑ q : Fin 4, ∑ r : Fin 193,
            mssP4CoarseAmplitude C q r (scale⁻¹ • xi)) *
            halfWaveMultiplier WaveSign.plus z.2 xi *
              FourierTransform.fourier (f : Euclidean 2 → Complex) xi := by
            rw [Finset.sum_mul]
            simp_rw [← Finset.sum_mul]
      _ = _ := by rw [sum_mssP4CoarseAmplitude]
  have hflat :
      (∑ q : Fin 4, ∑ r : Fin 193,
        FourierTransform.fourierInv (g (q, r)) z.1) =
        ∑ qr ∈ (Finset.univ : Finset (Fin 4)).product Finset.univ,
          FourierTransform.fourierInv (g qr) z.1 := by
    symm
    simpa using Finset.sum_product (Finset.univ : Finset (Fin 4))
      (Finset.univ : Finset (Fin 193))
      (fun qr : Fin 4 × Fin 193 => FourierTransform.fourierInv (g qr) z.1)
  calc
    (∑ q : Fin 4, ∑ r : Fin 193,
        conicOperator scale (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex)
          (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex)) z =
        mssCanonicalTime z.2 *
          ∑ q : Fin 4, ∑ r : Fin 193,
            FourierTransform.fourierInv (g (q, r)) z.1 := by
          simp only [conicOperator, g, Finset.sum_apply]
          simpa only [Finset.mul_sum]
    _ = mssCanonicalTime z.2 *
        ∑ qr ∈ (Finset.univ : Finset (Fin 4)).product Finset.univ,
          FourierTransform.fourierInv (g qr) z.1 := by rw [hflat]
    _ = mssCanonicalTime z.2 * FourierTransform.fourierInv
        (fun xi => ∑ qr ∈ (Finset.univ : Finset (Fin 4)).product Finset.univ,
          g qr xi) z.1 := by rw [← hfourier]
    _ = mssCanonicalTime z.2 * FourierTransform.fourierInv
        (fun xi => mssP4ScaledBandpassAmplitude C (scale⁻¹ • xi) *
          halfWaveMultiplier WaveSign.plus z.2 xi *
            FourierTransform.fourier (f : Euclidean 2 → Complex) xi) z.1 := by
          rw [hsum]
    _ = conicOperator scale
        (mssP4ScaledBandpassAmplitude C : Euclidean 2 → Complex)
        (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex) z := by
          rfl

/-- On the local time slab the finite coarse conic sum reconstructs the
positive dyadic half-wave exactly almost everywhere. -/
private theorem ae_eq_sum_mssP4CoarseConicOperator
    (C : lpCutoffs 2) (j : Nat) (f : SchwartzMap (Euclidean 2) Complex) :
    dyadicHalfWaveSpaceTime C.cutoff WaveSign.plus j f =ᵐ[localSmoothingMeasure]
      ∑ q : Fin 4, ∑ r : Fin 193,
        conicOperator (mssP4ConicScale j)
          (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex)
          (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex) := by
  have htime : ∀ᵐ t : Real ∂(volume.restrict (Icc (1 : Real) 2)),
      t ∈ Icc (1 : Real) 2 := ae_restrict_mem measurableSet_Icc
  have hslab : ∀ᵐ z : WaveSpaceTime ∂localSmoothingMeasure,
      z.2 ∈ Icc (1 : Real) 2 := by
    rw [localSmoothingMeasure]
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards with x
      exact htime
    · exact measurableSet_Icc.preimage measurable_snd
  have hscale : 0 < mssP4ConicScale j := by
    dsimp [mssP4ConicScale]
    positivity
  filter_upwards [hslab] with z hz
  calc
    dyadicHalfWaveSpaceTime C.cutoff WaveSign.plus j f z =
        conicOperator (mssP4ConicScale j)
          (mssP4ScaledBandpassAmplitude C : Euclidean 2 → Complex)
          (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex) z :=
      (conicOperator_eq_dyadicHalfWaveSpaceTime_plus_mssP4ConicScale
        C mssCanonicalTime j f z (mssCanonicalTime_one z.2 hz)).symm
    _ = (∑ q : Fin 4, ∑ r : Fin 193,
        conicOperator (mssP4ConicScale j)
          (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex)
          (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex)) z := by
      exact congrFun
        (sum_mssP4CoarseConicOperator C (mssP4ConicScale j) hscale f).symm z

/-- Finite Minkowski assembles the concrete `4 × 193` positive conic atlas
into the dyadic positive half-wave estimate at its natural conic scale. -/
private theorem mssP4PositiveL4AtConicScale
    (C : lpCutoffs 2) (eta : Real) (heta : 0 < eta) :
    ∃ K : Real, 0 < K ∧ ∀ j : Nat,
      ∀ f : SchwartzMap (Euclidean 2) Complex,
        eLpNorm (dyadicHalfWaveSpaceTime C.cutoff WaveSign.plus j f)
            (4 : ENNReal) localSmoothingMeasure ≤
          ENNReal.ofReal
            (K * (mssP4ConicScale j) ^ ((1 / 8 : Real) + eta)) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
  classical
  choose K hKpos hK using fun q r => mssP4ConicL4Estimate C q r eta heta
  let I := Fin 4 × Fin 193
  let Ktot : Real := ∑ i : I, K i.1 i.2
  have hKtot_pos : 0 < Ktot := by
    dsimp [Ktot]
    exact lt_of_lt_of_le (hKpos 0 0)
      (Finset.single_le_sum (s := (Finset.univ : Finset I))
        (fun i _ => (hKpos i.1 i.2).le) (Finset.mem_univ ⟨0, 0⟩))
  refine ⟨Ktot, hKtot_pos, ?_⟩
  intro j f
  let scale : Real := mssP4ConicScale j
  let a : Real := (1 / 8 : Real) + eta
  let S : Real := scale ^ a
  let F : ENNReal := eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume
  have hscale_pos : 0 < scale := by
    dsimp [scale, mssP4ConicScale]
    positivity
  have hscale : 2 ≤ scale := by
    dsimp [scale, mssP4ConicScale]
    have hpow : (1 : Real) ≤ (2 : Real) ^ j :=
      one_le_pow₀ (by norm_num)
    calc
      (2 : Real) = 1 * 2 := by norm_num
      _ ≤ (2 : Real) ^ j * 2 := mul_le_mul_of_nonneg_right hpow (by norm_num)
      _ = (2 : Real) ^ (j + 1) := by rw [pow_succ]
  let u : I → WaveSpaceTime → Complex := fun i =>
    conicOperator scale (mssP4CoarseAmplitude C i.1 i.2 : Euclidean 2 → Complex)
      (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex)
  have hu : ∀ i, AEStronglyMeasurable (u i) localSmoothingMeasure := by
    intro i
    have hcont := continuous_mssP4CoarseConicOperator C i.1 i.2 scale hscale_pos f
    exact hcont.aestronglyMeasurable
  have hpiece (i : I) :
      eLpNorm (u i) (4 : ENNReal) localSmoothingMeasure ≤
        ENNReal.ofReal (K i.1 i.2 * S) * F := by
    calc
      eLpNorm (u i) (4 : ENNReal) localSmoothingMeasure ≤
          eLpNorm (u i) (4 : ENNReal) volume :=
        eLpNorm_mono_measure _ localSmoothingMeasure_le_volume
      _ ≤ ENNReal.ofReal (K i.1 i.2 * S) * F := by
        change eLpNorm
            (conicOperator scale
              ((mssP4StructuredConicDatum C i.1 i.2).D.radialTime.amplitude :
                Euclidean 2 → Complex)
              ((mssP4StructuredConicDatum C i.1 i.2).D.radialTime.time :
                Real → Complex)
              (f : Euclidean 2 → Complex))
            (4 : ENNReal) volume ≤
              ENNReal.ofReal (K i.1 i.2 * scale ^ ((1 / 8 : Real) + eta)) *
                eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume
        exact hK i.1 i.2 scale hscale f
  have hcoeffsum :
      (∑ i : I, ENNReal.ofReal (K i.1 i.2 * S)) =
        ENNReal.ofReal (Ktot * S) := by
    calc
      (∑ i : I, ENNReal.ofReal (K i.1 i.2 * S)) =
          ∑ i : I, ENNReal.ofReal (K i.1 i.2) * ENNReal.ofReal S := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            exact ENNReal.ofReal_mul (hKpos i.1 i.2).le
      _ = (∑ i : I, ENNReal.ofReal (K i.1 i.2)) * ENNReal.ofReal S := by
            rw [Finset.sum_mul]
      _ = ENNReal.ofReal Ktot * ENNReal.ofReal S := by
            rw [show (∑ i : I, ENNReal.ofReal (K i.1 i.2)) =
                ENNReal.ofReal Ktot by
              symm
              dsimp [Ktot]
              exact ENNReal.ofReal_sum_of_nonneg
                (fun i _ => (hKpos i.1 i.2).le)]
      _ = ENNReal.ofReal (Ktot * S) := by
            symm
            exact ENNReal.ofReal_mul hKtot_pos.le
  have hflat : eLpNorm (∑ i : I, u i) (4 : ENNReal)
      localSmoothingMeasure ≤ ENNReal.ofReal (Ktot * S) * F := by
    calc
      eLpNorm (∑ i : I, u i) (4 : ENNReal) localSmoothingMeasure ≤
          ∑ i : I, eLpNorm (u i) (4 : ENNReal) localSmoothingMeasure :=
        eLpNorm_sum_le (s := Finset.univ) (f := u)
          (fun i _ => hu i) (by norm_num)
      _ ≤ ∑ i : I, ENNReal.ofReal (K i.1 i.2 * S) * F :=
        Finset.sum_le_sum (fun i _ => hpiece i)
      _ = ENNReal.ofReal (Ktot * S) * F := by
        rw [← Finset.sum_mul, hcoeffsum]
  have hreindex : (∑ i : I, u i) =
      ∑ q : Fin 4, ∑ r : Fin 193,
        conicOperator scale (mssP4CoarseAmplitude C q r : Euclidean 2 → Complex)
          (mssCanonicalTime : Real → Complex) (f : Euclidean 2 → Complex) := by
    rw [Fintype.sum_prod_type]
  rw [eLpNorm_congr_ae (ae_eq_sum_mssP4CoarseConicOperator C j f)]
  rw [← hreindex]
  simpa only [S, F, scale, a] using hflat

/-- Re-expressing the conic scale `2^(j+1)` only changes the endpoint
constant, so the positive estimate has exactly the dyadic exponent required
by the local-smoothing statement. -/
private theorem mssP4PositiveL4
    (C : lpCutoffs 2) (eta : Real) (heta : 0 < eta) :
    ∃ A : Real, 0 < A ∧ ∀ j : Nat,
      ∀ f : SchwartzMap (Euclidean 2) Complex,
        eLpNorm (dyadicHalfWaveSpaceTime C.cutoff WaveSign.plus j f)
            (4 : ENNReal) localSmoothingMeasure ≤
          ENNReal.ofReal
            (A * (2 : Real) ^ ((j : Real) * ((1 / 8 : Real) + eta))) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
  obtain ⟨K, hKpos, hK⟩ := mssP4PositiveL4AtConicScale C eta heta
  let a : Real := (1 / 8 : Real) + eta
  let A : Real := K * (2 : Real) ^ a
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos hKpos (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨A, hApos, ?_⟩
  intro j f
  have hscalePow : (mssP4ConicScale j) ^ a =
      (2 : Real) ^ a * (2 : Real) ^ ((j : Real) * a) := by
    unfold mssP4ConicScale
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : 0 ≤ (2 : Real))]
    rw [show ((j + 1 : Nat) : Real) * a = a + (j : Real) * a by
      push_cast
      ring]
    rw [Real.rpow_add (by norm_num : (0 : Real) < 2)]
  calc
    eLpNorm (dyadicHalfWaveSpaceTime C.cutoff WaveSign.plus j f)
        (4 : ENNReal) localSmoothingMeasure ≤
        ENNReal.ofReal
          (K * (mssP4ConicScale j) ^ ((1 / 8 : Real) + eta)) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := hK j f
    _ = ENNReal.ofReal
          (A * (2 : Real) ^ ((j : Real) * ((1 / 8 : Real) + eta))) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
          congr 1
          change ENNReal.ofReal (K * (mssP4ConicScale j) ^ a) =
            ENNReal.ofReal
              ((K * (2 : Real) ^ a) * (2 : Real) ^ ((j : Real) * a))
          rw [hscalePow]
          ring

/-- The reflected-conjugate cutoff is the correct frequency-side symmetry
for the negative half-wave.  It preserves the Littlewood--Paley cutoff
axioms without assuming that the original cutoff is real or even. -/
private noncomputable def mssP4ReflectedConjugateCutoffs
    (C : lpCutoffs 2) : lpCutoffs 2 where
  cutoff := Auto.Spherical.MSSKakeya.testNeg
    (Auto.Spherical.MSSKakeya.testConj C.cutoff)
  cutoff_one := by
    intro xi hxi
    rw [Auto.Spherical.MSSKakeya.testNeg_apply,
      Auto.Spherical.MSSKakeya.testConj_apply,
      C.cutoff_one (-xi) (by simpa using hxi)]
    norm_num
  cutoff_zero := by
    intro xi hxi
    rw [Auto.Spherical.MSSKakeya.testNeg_apply,
      Auto.Spherical.MSSKakeya.testConj_apply,
      C.cutoff_zero (-xi) (by simpa using hxi)]
    norm_num
  norm_le_one := by
    intro xi
    rw [Auto.Spherical.MSSKakeya.testNeg_apply,
      Auto.Spherical.MSSKakeya.testConj_apply, norm_star]
    exact C.norm_le_one (-xi)

/-- The dyadic band-pass of the reflected-conjugate cutoff is the reflected
complex conjugate of the original band-pass. -/
private theorem dyadicBandpassMultiplier_mssP4ReflectedConjugateCutoffs_apply
    (C : lpCutoffs 2) (j : Nat) (xi : Euclidean 2) :
    dyadicBandpassMultiplier (mssP4ReflectedConjugateCutoffs C).cutoff j xi =
      star (dyadicBandpassMultiplier C.cutoff j (-xi)) := by
  rw [dyadicBandpassMultiplier_apply, dyadicBandpassMultiplier_apply]
  simp only [mssP4ReflectedConjugateCutoffs,
    Auto.Spherical.MSSKakeya.testNeg_apply,
    Auto.Spherical.MSSKakeya.testConj_apply]
  simp

/-- Conjugating the reflected positive half-wave phase gives the negative
phase at the original frequency. -/
private theorem star_halfWaveMultiplier_plus_neg_eq_minus
    (t : Real) (xi : Euclidean 2) :
    star (halfWaveMultiplier WaveSign.plus t (-xi)) =
      halfWaveMultiplier WaveSign.minus t xi := by
  simp only [halfWaveMultiplier, WaveSign.toReal]
  rw [norm_neg]
  change starRingEnd Complex
      (Complex.exp (((1 * (2 * Real.pi) * t * ‖xi‖ : Real) : Complex) *
        Complex.I)) = _
  rw [(Complex.exp_conj _).symm]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Schwartz frequency spectra for the two sides of the reflected-conjugate
symmetry.  The annular dyadic symbol removes the apparent nonsmoothness of
the wave phase at the origin. -/
private noncomputable def mssP4ReflectedPlusSpectrum
    (C : lpCutoffs 2) (j : Nat) (t : Real)
    (f : SchwartzMap (Euclidean 2) Complex) :
    SchwartzMap (Euclidean 2) Complex :=
  SchwartzMap.smulLeftCLM Complex
    (dyadicHalfWaveSchwartzSymbol (mssP4ReflectedConjugateCutoffs C)
      WaveSign.plus j t : Euclidean 2 → Complex)
    (FourierTransform.fourier
      (Auto.Spherical.MSSKakeya.testConj f))

private noncomputable def mssP4NegativeSpectrum
    (C : lpCutoffs 2) (j : Nat) (t : Real)
    (f : SchwartzMap (Euclidean 2) Complex) :
    SchwartzMap (Euclidean 2) Complex :=
  SchwartzMap.smulLeftCLM Complex
    (dyadicHalfWaveSchwartzSymbol C WaveSign.minus j t :
      Euclidean 2 → Complex)
    (FourierTransform.fourier f)

/-- The negative spectrum is the reflection-conjugation of the positive
spectrum formed from the reflected-conjugate cutoff. -/
private theorem mssP4NegativeSpectrum_eq_reflectedConjPlusSpectrum
    (C : lpCutoffs 2) (j : Nat) (t : Real)
    (f : SchwartzMap (Euclidean 2) Complex) :
    mssP4NegativeSpectrum C j t f =
      Auto.Spherical.MSSKakeya.testNeg
        (Auto.Spherical.MSSKakeya.testConj
          (mssP4ReflectedPlusSpectrum C j t f)) := by
  have hfourier : FourierTransform.fourier
      (Auto.Spherical.MSSKakeya.testConj f) =
      Auto.Spherical.MSSKakeya.testNeg
        (Auto.Spherical.MSSKakeya.testConj
          (FourierTransform.fourier f)) := by
    simpa only [FourierTransform.fourierInv_fourier_eq] using
      Auto.Spherical.MSSKakeya.fourier_testConj_fourierInv
        (FourierTransform.fourier f)
  ext xi
  have hfourier_apply : FourierTransform.fourier
      (Auto.Spherical.MSSKakeya.testConj f : Euclidean 2 → Complex) (-xi) =
      star (FourierTransform.fourier (f : Euclidean 2 → Complex) xi) := by
    change (FourierTransform.fourier
      (Auto.Spherical.MSSKakeya.testConj f) :
        SchwartzMap (Euclidean 2) Complex) (-xi) = _
    rw [hfourier, Auto.Spherical.MSSKakeya.testNeg_apply,
      Auto.Spherical.MSSKakeya.testConj_apply, neg_neg,
      SchwartzMap.fourier_coe]
  have hband : dyadicBandpassMultiplier
      (mssP4ReflectedConjugateCutoffs C).cutoff j (-xi) =
      star (dyadicBandpassMultiplier C.cutoff j xi) := by
    rw [dyadicBandpassMultiplier_mssP4ReflectedConjugateCutoffs_apply,
      neg_neg]
  unfold mssP4NegativeSpectrum mssP4ReflectedPlusSpectrum
  rw [SchwartzMap.smulLeftCLM_apply_apply
      (dyadicHalfWaveSchwartzSymbol C WaveSign.minus j t).hasTemperateGrowth,
    Auto.Spherical.MSSKakeya.testNeg_apply,
    Auto.Spherical.MSSKakeya.testConj_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (dyadicHalfWaveSchwartzSymbol (mssP4ReflectedConjugateCutoffs C)
        WaveSign.plus j t).hasTemperateGrowth]
  simp only [smul_eq_mul, dyadicHalfWaveSchwartzSymbol_apply,
    dyadicHalfWaveSymbol, SchwartzMap.fourier_coe, star_mul]
  rw [hfourier_apply, hband, star_halfWaveMultiplier_plus_neg_eq_minus]
  simp only [star_star]
  ring

private theorem fourierInv_mssP4ReflectedPlusSpectrum_apply
    (C : lpCutoffs 2) (j : Nat) (t : Real)
    (f : SchwartzMap (Euclidean 2) Complex) (x : Euclidean 2) :
    FourierTransform.fourierInv (mssP4ReflectedPlusSpectrum C j t f) x =
      dyadicHalfWave (mssP4ReflectedConjugateCutoffs C).cutoff
        WaveSign.plus j t (Auto.Spherical.MSSKakeya.testConj f) x := by
  unfold mssP4ReflectedPlusSpectrum
  rw [SchwartzMap.fourierInv_coe]
  apply congrArg (fun q : Euclidean 2 → Complex => FourierTransform.fourierInv q x)
  funext xi
  simp only [SchwartzMap.smulLeftCLM_apply
    (dyadicHalfWaveSchwartzSymbol (mssP4ReflectedConjugateCutoffs C)
      WaveSign.plus j t).hasTemperateGrowth,
    smul_eq_mul, dyadicHalfWaveSchwartzSymbol_apply, dyadicHalfWaveSymbol,
    SchwartzMap.fourier_coe]

private theorem fourierInv_mssP4NegativeSpectrum_apply
    (C : lpCutoffs 2) (j : Nat) (t : Real)
    (f : SchwartzMap (Euclidean 2) Complex) (x : Euclidean 2) :
    FourierTransform.fourierInv (mssP4NegativeSpectrum C j t f) x =
      dyadicHalfWave C.cutoff WaveSign.minus j t f x := by
  unfold mssP4NegativeSpectrum
  rw [SchwartzMap.fourierInv_coe]
  apply congrArg (fun q : Euclidean 2 → Complex => FourierTransform.fourierInv q x)
  funext xi
  simp only [SchwartzMap.smulLeftCLM_apply
    (dyadicHalfWaveSchwartzSymbol C WaveSign.minus j t).hasTemperateGrowth,
    smul_eq_mul, dyadicHalfWaveSchwartzSymbol_apply, dyadicHalfWaveSymbol,
    SchwartzMap.fourier_coe]

/-- Pointwise reflected-conjugate transport from the positive to the negative
frequency-localized half-wave. -/
private theorem dyadicHalfWave_minus_eq_star_plus_reflectedConj
    (C : lpCutoffs 2) (j : Nat) (t : Real)
    (f : SchwartzMap (Euclidean 2) Complex) (x : Euclidean 2) :
    dyadicHalfWave C.cutoff WaveSign.minus j t f x =
      star (dyadicHalfWave (mssP4ReflectedConjugateCutoffs C).cutoff
        WaveSign.plus j t (Auto.Spherical.MSSKakeya.testConj f) x) := by
  have hreflect : FourierTransform.fourierInv (mssP4NegativeSpectrum C j t f) =
      Auto.Spherical.MSSKakeya.testConj
        (FourierTransform.fourierInv (mssP4ReflectedPlusSpectrum C j t f)) := by
    rw [mssP4NegativeSpectrum_eq_reflectedConjPlusSpectrum,
      Auto.Spherical.MSSKakeya.fourierInv_testNeg_eq_testNeg_fourierInv]
    exact (Auto.Spherical.MSSKakeya.testConj_fourierInv_eq_testNeg_fourierInv_testConj
      (mssP4ReflectedPlusSpectrum C j t f)).symm
  calc
    dyadicHalfWave C.cutoff WaveSign.minus j t f x =
        FourierTransform.fourierInv (mssP4NegativeSpectrum C j t f) x :=
      (fourierInv_mssP4NegativeSpectrum_apply C j t f x).symm
    _ = Auto.Spherical.MSSKakeya.testConj
        (FourierTransform.fourierInv (mssP4ReflectedPlusSpectrum C j t f)) x :=
      DFunLike.congr_fun hreflect x
    _ = star (FourierTransform.fourierInv (mssP4ReflectedPlusSpectrum C j t f) x) :=
      Auto.Spherical.MSSKakeya.testConj_apply _ _
    _ = star (dyadicHalfWave (mssP4ReflectedConjugateCutoffs C).cutoff
        WaveSign.plus j t (Auto.Spherical.MSSKakeya.testConj f) x) := by
      rw [fourierInv_mssP4ReflectedPlusSpectrum_apply C j t f x]

private theorem dyadicHalfWaveSpaceTime_minus_eq_star_plus_reflectedConj
    (C : lpCutoffs 2) (j : Nat) (f : SchwartzMap (Euclidean 2) Complex)
    (z : WaveSpaceTime) :
    dyadicHalfWaveSpaceTime C.cutoff WaveSign.minus j f z =
      star (dyadicHalfWaveSpaceTime (mssP4ReflectedConjugateCutoffs C).cutoff
        WaveSign.plus j (Auto.Spherical.MSSKakeya.testConj f) z) := by
  exact dyadicHalfWave_minus_eq_star_plus_reflectedConj C j z.2 f z.1

private theorem eLpNorm_testConj_eq
    (f : SchwartzMap (Euclidean 2) Complex) (p : ENNReal)
    (mu : Measure (Euclidean 2)) :
    eLpNorm (Auto.Spherical.MSSKakeya.testConj f : Euclidean 2 → Complex) p mu =
      eLpNorm (f : Euclidean 2 → Complex) p mu := by
  have htest : (Auto.Spherical.MSSKakeya.testConj f :
      Euclidean 2 → Complex) = star (f : Euclidean 2 → Complex) := by
    funext x
    exact Auto.Spherical.MSSKakeya.testConj_apply f x
  rw [htest, eLpNorm_star]

/-- The negative dyadic half-wave obeys the same p=4 estimate, transported
from the positive one by reflected-conjugate Fourier symmetry. -/
private theorem mssP4NegativeL4
    (C : lpCutoffs 2) (eta : Real) (heta : 0 < eta) :
    ∃ A : Real, 0 < A ∧ ∀ j : Nat,
      ∀ f : SchwartzMap (Euclidean 2) Complex,
        eLpNorm (dyadicHalfWaveSpaceTime C.cutoff WaveSign.minus j f)
            (4 : ENNReal) localSmoothingMeasure ≤
          ENNReal.ofReal
            (A * (2 : Real) ^ ((j : Real) * ((1 / 8 : Real) + eta))) *
            eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
  obtain ⟨A, hApos, hplus⟩ :=
    mssP4PositiveL4 (mssP4ReflectedConjugateCutoffs C) eta heta
  refine ⟨A, hApos, ?_⟩
  intro j f
  have hsymm : dyadicHalfWaveSpaceTime C.cutoff WaveSign.minus j f =
      star (dyadicHalfWaveSpaceTime (mssP4ReflectedConjugateCutoffs C).cutoff
        WaveSign.plus j (Auto.Spherical.MSSKakeya.testConj f)) := by
    funext z
    exact dyadicHalfWaveSpaceTime_minus_eq_star_plus_reflectedConj C j f z
  calc
    eLpNorm (dyadicHalfWaveSpaceTime C.cutoff WaveSign.minus j f)
        (4 : ENNReal) localSmoothingMeasure =
        eLpNorm (star (dyadicHalfWaveSpaceTime
          (mssP4ReflectedConjugateCutoffs C).cutoff WaveSign.plus j
          (Auto.Spherical.MSSKakeya.testConj f)))
          (4 : ENNReal) localSmoothingMeasure := by rw [hsymm]
    _ = eLpNorm (dyadicHalfWaveSpaceTime
          (mssP4ReflectedConjugateCutoffs C).cutoff WaveSign.plus j
          (Auto.Spherical.MSSKakeya.testConj f))
          (4 : ENNReal) localSmoothingMeasure := by rw [eLpNorm_star]
    _ ≤ ENNReal.ofReal
          (A * (2 : Real) ^ ((j : Real) * ((1 / 8 : Real) + eta))) *
          eLpNorm (Auto.Spherical.MSSKakeya.testConj f :
            Euclidean 2 → Complex) (4 : ENNReal) volume :=
      hplus j (Auto.Spherical.MSSKakeya.testConj f)
    _ = ENNReal.ofReal
          (A * (2 : Real) ^ ((j : Real) * ((1 / 8 : Real) + eta))) *
          eLpNorm (f : Euclidean 2 → Complex) (4 : ENNReal) volume := by
      rw [eLpNorm_testConj_eq]

/-- The fully assembled planar Mockenhaupt--Seeger--Sogge endpoint at
`p = 4`.  The positive sign is the finite coarse conic atlas and the negative
sign is its reflected-conjugate Fourier transport. -/
theorem p4LocalSmoothing_of_lpCutoffs (C : lpCutoffs 2) :
    p4LocalSmoothing C.cutoff := by
  intro eta heta
  unfold localSmoothing
  refine ⟨by norm_num, heta, ?_⟩
  obtain ⟨Aplus, hAplus_pos, hplus⟩ := mssP4PositiveL4 C eta heta
  obtain ⟨Aminus, hAminus_pos, hminus⟩ := mssP4NegativeL4 C eta heta
  let A : Real := Aplus + Aminus
  have hApos : 0 < A := by
    dsimp [A]
    exact add_pos hAplus_pos hAminus_pos
  refine ⟨A, hApos, ?_⟩
  intro j _hj f sigma
  have hexponent :
      (j : Real) * (1 / 2 - 1 / 4 - mssGain 4 + eta) =
        (j : Real) * ((1 / 8 : Real) + eta) := by
    rw [mssGain_four]
    ring
  cases sigma with
  | plus =>
      rw [show ENNReal.ofReal (4 : Real) = (4 : ENNReal) by norm_num,
        hexponent]
      have hcoeff : ENNReal.ofReal
          (Aplus * (2 : Real) ^ ((j : Real) * ((1 / 8 : Real) + eta))) ≤
          ENNReal.ofReal
            (A * (2 : Real) ^ ((j : Real) * ((1 / 8 : Real) + eta))) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right hAminus_pos.le)
        exact Real.rpow_nonneg (by norm_num) _
      exact (hplus j f).trans (by
        simpa only [mul_comm] using
          mul_le_mul_left hcoeff (eLpNorm (f : Euclidean 2 → Complex)
            (4 : ENNReal) volume))
  | minus =>
      rw [show ENNReal.ofReal (4 : Real) = (4 : ENNReal) by norm_num,
        hexponent]
      have hcoeff : ENNReal.ofReal
          (Aminus * (2 : Real) ^ ((j : Real) * ((1 / 8 : Real) + eta))) ≤
          ENNReal.ofReal
            (A * (2 : Real) ^ ((j : Real) * ((1 / 8 : Real) + eta))) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hAplus_pos.le)
        exact Real.rpow_nonneg (by norm_num) _
      exact (hminus j f).trans (by
        simpa only [mul_comm] using
          mul_le_mul_left hcoeff (eLpNorm (f : Euclidean 2 → Complex)
            (4 : ENNReal) volume))

/-- The complete real-exponent planar MSS local-smoothing family, obtained
from the proved `p = 4` endpoint through the verified endpoint interpolation
theorems. -/
theorem localSmoothing_of_lpCutoffs (C : lpCutoffs 2)
    {p η : Real} (hp : 2 < p) (hη : 0 < η) :
    localSmoothing C.cutoff p η := by
  exact p4LocalSmoothing_to_localSmoothing_all_p C
    (p4LocalSmoothing_of_lpCutoffs C) hp hη

/-- A finite coarse angular atlas for the endpoint assembly.  Each member is
a genuinely narrow structured conic datum.  The two reconstruction fields
are exact (up to the local restricted measure) Fourier identities: the
positive family reconstructs the positive dyadic half-wave, while the
reflected-conjugate family reconstructs the negative one after conjugating
the input and output.  Thus the structure records cutoff and symmetry data,
not any additional `L⁴` estimate. -/
structure MSSP4ConicAtlas (C : lpCutoffs 2) where
  sectorCount : Nat
  plusData : Fin sectorCount → MSSStructuredConicDatum
  minusData : Fin sectorCount → MSSStructuredConicDatum
  plus_measurable : ∀ (r : Fin sectorCount) (j : Nat)
    (f : SchwartzMap (Euclidean 2) Complex),
      AEStronglyMeasurable
        (conicOperator (mssP4ConicScale j)
          ((plusData r).D.radialTime.amplitude : Euclidean 2 → Complex)
          ((plusData r).D.radialTime.time : Real → Complex)
          (f : Euclidean 2 → Complex))
        localSmoothingMeasure
  minus_measurable : ∀ (r : Fin sectorCount) (j : Nat)
    (f : SchwartzMap (Euclidean 2) Complex),
      AEStronglyMeasurable
        (conicOperator (mssP4ConicScale j)
          ((minusData r).D.radialTime.amplitude : Euclidean 2 → Complex)
          ((minusData r).D.radialTime.time : Real → Complex)
          (f : Euclidean 2 → Complex))
        localSmoothingMeasure
  plus_reconstruct : ∀ (j : Nat) (f : SchwartzMap (Euclidean 2) Complex),
      dyadicHalfWaveSpaceTime C.cutoff WaveSign.plus j f =ᵐ[localSmoothingMeasure]
        ∑ r, conicOperator (mssP4ConicScale j)
          ((plusData r).D.radialTime.amplitude : Euclidean 2 → Complex)
          ((plusData r).D.radialTime.time : Real → Complex)
          (f : Euclidean 2 → Complex)
  minus_reconstruct : ∀ (j : Nat) (f : SchwartzMap (Euclidean 2) Complex),
      dyadicHalfWaveSpaceTime C.cutoff WaveSign.minus j f =ᵐ[localSmoothingMeasure]
        star (∑ r, conicOperator (mssP4ConicScale j)
          ((minusData r).D.radialTime.amplitude : Euclidean 2 → Complex)
          ((minusData r).D.radialTime.time : Real → Complex)
          ((Auto.Spherical.MSSKakeya.testConj f :
            SchwartzMap (Euclidean 2) Complex) : Euclidean 2 → Complex))

end

end Auto.Spherical.MSS

end Auto.Spherical.MSS
