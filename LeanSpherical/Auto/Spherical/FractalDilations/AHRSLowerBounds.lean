/-
AHRS lower-bound geometry and sharpness constructions.

This consolidated module preserves the declaration namespaces of its former
components and remains independent of PowerWeights and Bourgain.
-/

import LeanSpherical.Auto.Spherical.Auxiliary
import LeanSpherical.Auto.Spherical.FractalDilations.Auxiliary
import LeanSpherical.Auto.Spherical.FractalDilations.FractalDimensions
import LeanSpherical.Auto.Spherical.SphericalMaximal
import LeanSpherical.Auto.Spherical.SurfaceMeasureDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/- ===== Remaining former FractalDilations/Maximal.lean material ===== -/
section Former_MaximalGlobal
namespace Auto.Spherical.FractalDilations.Maximal
open Auto.Spherical.HardyLittlewoodMaximal
open Auto.Spherical.SphericalAverages
open Auto.Spherical.SurfaceCore
open MeasureTheory Set
noncomputable section
/-- The real-valued local maximal function is dominated by the existing
real-valued global maximal function on Schwartz data. -/
theorem fractalSphericalMaximalReal_le_normalizedSphericalMaximalReal
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    fractalSphericalMaximalReal d E f x ≤ normalizedSphericalMaximalReal d f x := by
  unfold fractalSphericalMaximalReal normalizedSphericalMaximalReal
  have hglobal : normalizedSphericalMaximal d (f : Euclidean d → ℂ) x ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (ENNReal.ofReal_ne_top : ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ ≠ ⊤) ?_
    exact normalizedSphericalMaximal_le_of_norm_le hd _ x
      (fun y => by
        change ‖f.toBoundedContinuousFunction y‖ ≤ ‖f.toBoundedContinuousFunction‖
        exact BoundedContinuousFunction.norm_coe_le_norm _ _)
  exact (ENNReal.toReal_le_toReal
    (fractalSphericalMaximal_ne_top hd E hE f x) hglobal).mpr
      (fractalSphericalMaximal_le_normalizedSphericalMaximal E hE _ x)

/-- Monotonicity also holds for the real-valued restricted maximal operator
when both suprema are finite, in particular for positive radii and Schwartz
data. -/
theorem fractalSphericalMaximalReal_mono
    {d : ℕ} (hd : 0 < d) {E F : Set ℝ} (hEF : E ⊆ F)
    (hF : F ⊆ Ioi (0 : ℝ)) (f : SchwartzMap (Euclidean d) ℂ)
    (x : Euclidean d) :
    fractalSphericalMaximalReal d E f x ≤ fractalSphericalMaximalReal d F f x := by
  unfold fractalSphericalMaximalReal
  apply ENNReal.toReal_mono
  · exact fractalSphericalMaximal_ne_top hd F hF f x
  · exact fractalSphericalMaximal_mono hEF _ x


/-- Real-valued subadditivity on Schwartz data. -/
theorem fractalSphericalMaximalReal_schwartz_add_le
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Ioi (0 : ℝ))
    (f g : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    fractalSphericalMaximalReal d E (f + g) x ≤
      fractalSphericalMaximalReal d E f x + fractalSphericalMaximalReal d E g x := by
  have hfg : fractalSphericalMaximal d E ((f + g : SchwartzMap (Euclidean d) ℂ) :
      Euclidean d → ℂ) x ≠ ⊤ :=
    fractalSphericalMaximal_ne_top hd E hE (f + g) x
  have hf : fractalSphericalMaximal d E (f : Euclidean d → ℂ) x ≠ ⊤ :=
    fractalSphericalMaximal_ne_top hd E hE f x
  have hg : fractalSphericalMaximal d E (g : Euclidean d → ℂ) x ≠ ⊤ :=
    fractalSphericalMaximal_ne_top hd E hE g x
  have hsum : fractalSphericalMaximal d E (f : Euclidean d → ℂ) x +
      fractalSphericalMaximal d E (g : Euclidean d → ℂ) x ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hf, hg⟩
  unfold fractalSphericalMaximalReal
  calc
    (fractalSphericalMaximal d E ((f + g : SchwartzMap (Euclidean d) ℂ) :
        Euclidean d → ℂ) x).toReal ≤
        (fractalSphericalMaximal d E (f : Euclidean d → ℂ) x +
          fractalSphericalMaximal d E (g : Euclidean d → ℂ) x).toReal :=
      (ENNReal.toReal_le_toReal hfg hsum).mpr
        (fractalSphericalMaximal_add_le E (f : Euclidean d → ℂ) (g : Euclidean d → ℂ)
          f.continuous g.continuous x)
    _ = fractalSphericalMaximalReal d E f x +
        fractalSphericalMaximalReal d E g x := ENNReal.toReal_add hf hg

/-- Negating a Schwartz input does not change the restricted maximal
function. -/
theorem fractalSphericalMaximalReal_schwartz_neg
    {d : ℕ} (E : Set ℝ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    fractalSphericalMaximalReal d E (-f) x = fractalSphericalMaximalReal d E f x := by
  have havg (r : ℝ) : normalizedSphericalAverage d
      ((-f : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r x =
      -normalizedSphericalAverage d (f : Euclidean d → ℂ) r x := by
    unfold normalizedSphericalAverage sphericalAverage
    change (surfaceMass d : ℂ)⁻¹ *
        ∫ ω : Metric.sphere (0 : Euclidean d) 1, -f (x + r • (ω : Euclidean d))
          ∂unitSurfaceMeasure d =
      -((surfaceMass d : ℂ)⁻¹ *
        ∫ ω : Metric.sphere (0 : Euclidean d) 1, f (x + r • (ω : Euclidean d))
          ∂unitSurfaceMeasure d)
    rw [integral_neg]
    ring
  unfold fractalSphericalMaximalReal fractalSphericalMaximal
  congr with r
  rw [havg r.1]
  simp

/-- The restricted maximal operator maps the zero Schwartz function to zero. -/
theorem fractalSphericalMaximalReal_zero
    {d : ℕ} (E : Set ℝ) (x : Euclidean d) :
    fractalSphericalMaximalReal d E (0 : SchwartzMap (Euclidean d) ℂ) x = 0 := by
  unfold fractalSphericalMaximalReal fractalSphericalMaximal
  simp [normalizedSphericalAverage, sphericalAverage]

/-- Pointwise difference domination for the restricted maximal operator. -/
theorem abs_sub_fractalSphericalMaximalReal_schwartz_le
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Ioi (0 : ℝ))
    (f g : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    |fractalSphericalMaximalReal d E f x - fractalSphericalMaximalReal d E g x| ≤
      fractalSphericalMaximalReal d E (f - g) x := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    have h := fractalSphericalMaximalReal_schwartz_add_le hd E hE g (f - g) x
    have hsum : g + (f - g) = f := by
      ext y
      simp
    rw [hsum] at h
    simpa [add_comm] using h
  · rw [sub_le_iff_le_add]
    have h := fractalSphericalMaximalReal_schwartz_add_le hd E hE f (g - f) x
    have hsum : f + (g - f) = g := by
      ext y
      simp
    rw [hsum] at h
    have hneg : fractalSphericalMaximalReal d E (g - f) x =
        fractalSphericalMaximalReal d E (f - g) x := by
      rw [show g - f = -(f - g) by
          ext y
          simp,
        fractalSphericalMaximalReal_schwartz_neg]
    rw [hneg] at h
    simpa [add_comm] using h

end
end Auto.Spherical.FractalDilations.Maximal
end Former_MaximalGlobal
/- ===== Former FractalDilations/AnnulusAlgebra.lean ===== -/
section Former_AnnulusAlgebra

/- This file was machine-generated by Codex -/






/-!
# Exponent bookkeeping for the annulus sharpness example

The lower Minkowski witness is available at every exponent strictly below the
upper Minkowski dimension.  This file records the elementary, but important,
fact that a strict violation of the annulus inequality survives after lowering
the dimension exponent a little.  It lets the geometric packing argument use
an actual finite separated family without introducing a spurious endpoint
loss.
-/

namespace Auto.Spherical.FractalDilations.AnnulusAlgebra

noncomputable section

/-- A strict annulus violation at a positive Minkowski dimension persists at
some nonnegative exponent strictly below that dimension. -/
theorem exists_annulus_exponent_lt_minkowski
    {d : ℕ} {β p q : ℝ}
    (hβ : 0 < β) (hq : 0 < q)
    (hbad : (1 - β) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    ∃ α : ℝ, 0 ≤ α ∧ α < β ∧
      (1 - α) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹ := by
  let m : ℝ := (d : ℝ) * p⁻¹ - ((1 - β) * q⁻¹ + ((d : ℝ) - 1))
  have hm : 0 < m := by
    dsimp [m]
    linarith
  let ε : ℝ := min (β / 2) (m * q / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (by positivity)
  have hεβ : ε ≤ β / 2 := by
    dsimp [ε]
    exact min_le_left _ _
  have hεm : ε ≤ m * q / 2 := by
    dsimp [ε]
    exact min_le_right _ _
  refine ⟨β - ε, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have hqin : q * q⁻¹ = 1 := mul_inv_cancel₀ hq.ne'
    have hsmall : ε * q⁻¹ < m := by
      calc
        ε * q⁻¹ ≤ (m * q / 2) * q⁻¹ :=
          mul_le_mul_of_nonneg_right hεm (inv_nonneg.mpr hq.le)
        _ = m / 2 := by
          field_simp
        _ < m := by linarith
    have hrearrange :
        (1 - (β - ε)) * q⁻¹ + ((d : ℝ) - 1) =
          ((1 - β) * q⁻¹ + ((d : ℝ) - 1)) + ε * q⁻¹ := by
      ring
    rw [hrearrange]
    dsimp [m] at hm
    linarith

end

end Auto.Spherical.FractalDilations.AnnulusAlgebra
end Former_AnnulusAlgebra

/- ===== Former FractalDilations/ClusterPacking.lean ===== -/
section Former_ClusterPacking

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.AssouadSpectrum
open Auto.Spherical.FractalDilations.CoveringNumbers
open Auto.Spherical.FractalDilations.Minkowski
open Auto.Spherical.FractalDilations.PackingExtraction
open Auto.Spherical.FractalDilations.SeparatedPacking







/-!
# Local separated witnesses for the upper Assouad spectrum

The clustered-radius sharpness example needs a finite family of actual radii,
not merely a lower bound for a local covering number.  This file combines the
upper-spectrum lower witness with the generic maximal-packing extraction.
-/

namespace Auto.Spherical.FractalDilations.ClusterPacking

open Set

noncomputable section

/-- A strict gap below an upper Assouad-spectrum exponent produces, at
arbitrarily small scales, a locally clustered finite family of radii.  The
members lie in one interval of length at least `δ ^ θ`, are separated at mesh
`δ / 2`, and have the required local cardinality lower bound. -/
theorem exists_upperAssouadSpectrum_strictlySeparated_lower_witness_at_small_scale
    {E : Set ℝ} {θ α γ : ℝ}
    (hθ0 : 0 ≤ θ) (hθone : θ ≤ 1)
    (hspectrum : upperAssouadSpectrum E θ = γ)
    (hα0 : 0 ≤ α) (hαγ : α < γ) :
    ∀ C : ℝ, 0 < C → ∀ δ₀ : ℝ, 0 < δ₀ →
      ∃ δ a b : ℝ, ∃ s : Finset ℝ,
        0 < δ ∧ δ < δ₀ ∧ δ < 1 ∧
          1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ δ ^ θ ≤ b - a ∧
          (↑s : Set ℝ) ⊆ E ∩ Icc a b ∧ StrictlySeparated s (δ / 2) ∧
          C * ((b - a) / δ) ^ α < (s.card : ℝ) := by
  intro C hC δ₀ hδ₀
  obtain ⟨δ, a, b, hδ, hδsmall, hδone, ha, hab, hb, hscale, hlarge⟩ :=
    exists_upperAssouadSpectrum_coveringNumber_lower_witness_at_small_scale
      hθ0 hθone hspectrum hα0 hαγ C hC δ₀ hδ₀
  have hlocal : E ∩ Icc a b ⊆ Icc (1 : ℝ) 2 := by
    intro x hx
    exact ⟨ha.trans hx.2.1, hx.2.2.trans hb⟩
  obtain ⟨s, hs, hssep, hcard⟩ :=
    exists_strictlySeparated_finset_card_ge_intervalCoveringNumber hlocal
      (δ := δ / 2) (by linarith)
  refine ⟨δ, a, b, s, hδ, hδsmall, hδone, ha, hab, hb, hscale,
    hs, hssep, ?_⟩
  calc
    C * ((b - a) / δ) ^ α <
        (intervalCoveringNumber (E ∩ Icc a b) δ : ℝ) := hlarge
    _ ≤ (s.card : ℝ) := by
      convert hcard using 1 <;> ring

/-- A local covering-number lower bound and a global interval cover give the
scale restriction needed for the upper-spectrum clustered-radius example.
The identical constant on the two estimates cancels, so this formulation is
also convenient when the local witness is requested after fixing a global
Minkowski cover constant. -/
theorem local_ratio_rpow_lt_of_covering_lower_and_global_cover
    {E : Set ℝ} {a b δ α B C : ℝ} {i : Finset ℝ}
    (hC : 0 < C)
    (hlower : C * ((b - a) / δ) ^ α <
      (intervalCoveringNumber (E ∩ Icc a b) δ : ℝ))
    (hcover : IsIntervalCover E δ i)
    (hcard : (i.card : ℝ) ≤ C * δ ^ (-B)) :
    ((b - a) / δ) ^ α < δ ^ (-B) := by
  have hlocalCover : IsIntervalCover (E ∩ Icc a b) δ i :=
    hcover.mono inter_subset_left
  have hlocal : (intervalCoveringNumber (E ∩ Icc a b) δ : ℝ) ≤
      C * δ ^ (-B) :=
    intervalCoveringNumber_le_of_intervalCover_card_le hlocalCover hcard
  have hmul : C * ((b - a) / δ) ^ α < C * δ ^ (-B) :=
    hlower.trans_le hlocal
  exact lt_of_mul_lt_mul_left hmul hC.le

/-- Rewrite the relative-length restriction in its more geometric form. -/
theorem length_lt_rpow_of_ratio_rpow_lt
    {L δ α B : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (hα : 0 < α)
    (hratio : (L / δ) ^ α < δ ^ (-B)) :
    L < δ ^ (1 - B / α) := by
  have hpow : (δ ^ (-B / α)) ^ α = δ ^ (-B) := by
    rw [← Real.rpow_mul hδ.le]
    congr 1
    field_simp
  have hratio' : L / δ < δ ^ (-B / α) := by
    apply (Real.rpow_lt_rpow_iff
      (div_nonneg hL hδ.le) (Real.rpow_nonneg hδ.le _) hα).mp
    rwa [hpow]
  have hmul : L < δ * δ ^ (-B / α) := by
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hratio'
  calc
    L < δ * δ ^ (-B / α) := hmul
    _ = δ ^ (1 - B / α) := by
      calc
        δ * δ ^ (-B / α) = δ ^ (1 : ℝ) * δ ^ (-B / α) := by
          rw [Real.rpow_one]
        _ = δ ^ (1 + -B / α) := (Real.rpow_add hδ _ _).symm
      congr 1
      ring

/-- Upper Minkowski control localizes the separated lower witnesses furnished
by the upper Assouad spectrum.  This is the quantitative replacement for the
equality-scale convention in the paper: with the upper spectrum convention,
the witness interval is initially only known to have length *at least*
`δ ^ θ`; the final inequality forces an upper bound on its relative
length. -/
theorem exists_upperAssouadSpectrum_localized_strictlySeparated_lower_witness_at_small_scale
    {E : Set ℝ} {θ α γ β ε : ℝ}
    (hθ₀ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hMinkowski : HasUpperMinkowskiExponent E β) (hε : 0 < ε)
    (hspectrum : upperAssouadSpectrum E θ = γ)
    (hα₀ : 0 ≤ α) (hαγ : α < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ₀ : ℝ, 0 < δ₀ →
      ∃ δ a b : ℝ, ∃ s : Finset ℝ,
        0 < δ ∧ δ < δ₀ ∧ δ < 1 ∧
          1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ δ ^ θ ≤ b - a ∧
          (↑s : Set ℝ) ⊆ E ∩ Icc a b ∧ StrictlySeparated s (δ / 2) ∧
          C * ((b - a) / δ) ^ α < (s.card : ℝ) ∧
          ((b - a) / δ) ^ α < δ ^ (-(β + ε)) := by
  obtain ⟨C, hC, hglobal⟩ := hMinkowski ε hε
  refine ⟨C, hC, ?_⟩
  intro δ₀ hδ₀
  obtain ⟨δ, a, b, hδ, hδsmall, hδone, ha, hab, hb, hscale, hlower⟩ :=
    exists_upperAssouadSpectrum_coveringNumber_lower_witness_at_small_scale
      hθ₀ hθone hspectrum hα₀ hαγ C hC δ₀ hδ₀
  obtain ⟨i, hcover, hcard⟩ := hglobal δ hδ hδone
  have hlocal : E ∩ Icc a b ⊆ Icc (1 : ℝ) 2 := by
    intro x hx
    exact ⟨ha.trans hx.2.1, hx.2.2.trans hb⟩
  obtain ⟨s, hs, hssep, hpack⟩ :=
    exists_strictlySeparated_finset_card_ge_intervalCoveringNumber hlocal
      (δ := δ / 2) (by linarith)
  refine ⟨δ, a, b, s, hδ, hδsmall, hδone, ha, hab, hb, hscale,
    hs, hssep, ?_, ?_⟩
  · calc
      C * ((b - a) / δ) ^ α <
          (intervalCoveringNumber (E ∩ Icc a b) δ : ℝ) := hlower
      _ ≤ (s.card : ℝ) := by
        convert hpack using 1 <;> ring
  · exact local_ratio_rpow_lt_of_covering_lower_and_global_cover
      hC hlower hcover hcard

end

end Auto.Spherical.FractalDilations.ClusterPacking
end Former_ClusterPacking

/- ===== Former FractalDilations/SharpnessGeometry.lean ===== -/
section Former_SharpnessGeometry

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.Definitions
open Auto.Spherical.FractalDilations.ExponentGeometry
open Auto.Spherical.FractalDilations.ExponentRegions







/-!
# Geometric assembly for fractal-dilation sharpness

The four lower-bound constructions in the paper have distinct analytic
content.  This module contains the entirely geometric final step: the exact
halfspace description of `Q` selects one applicable construction whenever an
exponent point lies outside `Q`.
-/

namespace Auto.Spherical.FractalDilations.SharpnessGeometry

open Set

noncomputable section

/-- Assemble the four sharpness tests into unboundedness outside the closed
exponent region.  Each premise is deliberately just the implication supplied
by one analytic lower-bound construction, so the remaining analytic work is
fully isolated from the planar geometry. -/
theorem fractalSphericalUnbounded_of_not_mem_Q_of_tests
    {d : ℕ} {E : Set ℝ} {β γ p q : ℝ}
    (hd : 2 ≤ d) (hβ : 0 ≤ β) (hβone : β ≤ 1) (hβγ : β ≤ γ)
    (htranslation : p⁻¹ < q⁻¹ → FractalSphericalUnbounded d E p q)
    (hcap : (d : ℝ) * q⁻¹ < p⁻¹ → FractalSphericalUnbounded d E p q)
    (hannulus : (1 - β) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹ →
      FractalSphericalUnbounded d E p q)
    (hcluster : clusterEdgeFunctional d (β / γ) β (reciprocalExponentPoint p q) < 0 →
      FractalSphericalUnbounded d E p q)
    (houtside : reciprocalExponentPoint p q ∉ Q d β γ) :
    FractalSphericalUnbounded d E p q := by
  have hbad : SharpnessViolation d β γ (reciprocalExponentPoint p q) := by
    by_contra hnot
    apply houtside
    exact (mem_Q_iff_not_sharpnessViolation hd hβ hβone hβγ).2 hnot
  rcases hbad with hbad | hbad | hbad | hbad
  · change p⁻¹ < q⁻¹ at hbad
    exact htranslation hbad
  · change (d : ℝ) * q⁻¹ < p⁻¹ at hbad
    exact hcap hbad
  · change (1 - β) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹ at hbad
    exact hannulus hbad
  · exact hcluster hbad

end

end Auto.Spherical.FractalDilations.SharpnessGeometry
end Former_SharpnessGeometry

/- ===== Former FractalDilations/SharpnessNormalization.lean ===== -/
section Former_SharpnessNormalization

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.Definitions
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Homogeneity
open Auto.Spherical.FractalDilations.Maximal
open Auto.Spherical.SurfaceCore







/-!
# Normalizing lower-bound test families

The sharpness examples naturally first produce a function whose input norm is
bounded by a finite positive quantity `A`, while its output norm is larger
than `C * A`.  This short module records the scalar normalization which turns
such a family into the definition of `FractalSphericalUnbounded`.
-/

namespace Auto.Spherical.FractalDilations.SharpnessNormalization

open MeasureTheory Set ENNReal

noncomputable section

/-- A family of tests with arbitrarily large output-to-input ratio yields
failure of every normalized strong-type bound. -/
theorem fractalSphericalUnbounded_of_large_ratio
    {d : ℕ} {E : Set ℝ} {p q : ℝ}
    (hlarge : ∀ C : ℝ, 0 < C → ∃ (f : SchwartzMap (Euclidean d) ℂ)
      (A : ENNReal), A ≠ 0 ∧ A ≠ ∞ ∧
        eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤ A ∧
          ENNReal.ofReal C * A <
            eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume) :
    FractalSphericalUnbounded d E p q := by
  intro C hC
  obtain ⟨f, A, hA0, hAtop, hinput, houtput⟩ := hlarge C hC
  let c : ℂ := (A.toReal)⁻¹
  have hArealpos : 0 < A.toReal := ENNReal.toReal_pos hA0 hAtop
  have hc : ENNReal.ofReal ‖c‖ = A⁻¹ := by
    dsimp [c]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hArealpos,
      ENNReal.ofReal_inv_of_pos hArealpos, ENNReal.ofReal_toReal hAtop]
  have hc' : ‖c‖ₑ = A⁻¹ := by simpa using hc
  have hcreal : ‖(‖c‖ : ℝ)‖ₑ = A⁻¹ := by simpa using hc
  refine ⟨c • f, ?_, ?_⟩
  · change eLpNorm (c • (f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume ≤ 1
    rw [eLpNorm_const_smul]
    rw [hc']
    calc
      A⁻¹ * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤ A⁻¹ * A :=
        by simpa only [mul_comm] using mul_le_mul_left hinput A⁻¹
      _ = 1 := ENNReal.inv_mul_cancel hA0 hAtop
  · change ENNReal.ofReal C <
      eLpNorm (fractalSphericalMaximalReal d E (c • f)) (ENNReal.ofReal q) volume
    have hmax : fractalSphericalMaximalReal d E (c • f) =
        (‖c‖ : ℝ) • fractalSphericalMaximalReal d E f := by
      ext x
      exact fractalSphericalMaximalReal_const_smul E c f x
    rw [hmax, eLpNorm_const_smul]
    rw [hcreal]
    have hdiv : ENNReal.ofReal C <
        eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume / A :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hA0) (Or.inl hAtop)).mpr houtput
    simpa only [div_eq_mul_inv, mul_comm] using hdiv

end

end Auto.Spherical.FractalDilations.SharpnessNormalization
end Former_SharpnessNormalization

/- ===== Former FractalDilations/SharpnessTests.lean ===== -/
section Former_SharpnessTests

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Maximal
open Auto.Spherical.SmoothDyadicPhysicalCore
open Auto.Spherical.SurfaceCore







/-!
# Elementary test-function facts for fractal spherical maximal operators

The sharpness constructions in the fractal-dilation theorem use translates,
small balls, and spherical caps.  This file contains the exact elementary
pointwise facts common to those constructions.  The genuinely quantitative
measure estimates needed to turn these tests into the full unboundedness
statement deliberately live separately from these algebraic identities.
-/

namespace Auto.Spherical.FractalDilations.SharpnessTests

open MeasureTheory Metric Set

noncomputable section

/-- A normalized spherical average only uses the values of the input on its
sampling sphere. -/
theorem normalizedSphericalAverage_eq_of_eq_on_sphere
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) (c : ℂ) (r : ℝ)
    (x : Euclidean d)
    (h : ∀ ω : sphere (0 : Euclidean d) 1,
      f (x + r • (ω : Euclidean d)) = c) :
    normalizedSphericalAverage d f r x = c := by
  calc
    normalizedSphericalAverage d f r x =
        normalizedSphericalAverage d (fun _ : Euclidean d => c) r x := by
      unfold normalizedSphericalAverage
      congr 1
      unfold sphericalAverage
      apply integral_congr_ae
      filter_upwards with ω
      exact h ω
    _ = c := normalizedSphericalAverage_const hd c r x

/-- Translation covariance for the normalized average. -/
theorem normalizedSphericalAverage_translate (d : ℕ) (f : Euclidean d → ℂ)
    (r : ℝ) (a x : Euclidean d) :
    normalizedSphericalAverage d (fun y => f (a + y)) r x =
      normalizedSphericalAverage d f r (a + x) := by
  unfold normalizedSphericalAverage
  rw [sphericalAverage_translate]

/-- The restricted maximal operator is translation covariant on arbitrary
data.  This is the pointwise identity behind the translate test in the
sharpness argument. -/
theorem fractalSphericalMaximal_translate
    {d : ℕ} (E : Set ℝ) (f : Euclidean d → ℂ) (a x : Euclidean d) :
    fractalSphericalMaximal d E (fun y => f (a + y)) x =
      fractalSphericalMaximal d E f (a + x) := by
  unfold fractalSphericalMaximal
  congr with t
  rw [normalizedSphericalAverage_translate]

/-- If the input is one on the ball containing the sampling sphere, its
normalized spherical average is one. -/
theorem normalizedSphericalAverage_eq_one_of_norm_add_abs_le
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) (r : ℝ)
    (x : Euclidean d)
    (hf : ∀ y : Euclidean d, ‖y‖ ≤ 1 → f y = 1)
    (hxr : ‖x‖ + |r| ≤ 1) :
    normalizedSphericalAverage d f r x = 1 := by
  apply normalizedSphericalAverage_eq_of_eq_on_sphere hd f 1 r x
  intro ω
  apply hf
  calc
    ‖x + r • (ω : Euclidean d)‖ ≤ ‖x‖ + ‖r • (ω : Euclidean d)‖ :=
      norm_add_le _ _
    _ = ‖x‖ + |r| := by
      rw [norm_smul, Real.norm_eq_abs]
      have hω : ‖(ω : Euclidean d)‖ = 1 := by
        simpa only [mem_sphere_zero_iff_norm] using ω.property
      rw [hω, mul_one]
    _ ≤ 1 := hxr

/-- The preceding ball test at an arbitrary spatial scale. -/
theorem normalizedSphericalAverage_eq_one_of_norm_add_abs_le_of_eq_on_ball
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) (R r : ℝ)
    (x : Euclidean d)
    (hf : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hxr : ‖x‖ + |r| ≤ R) :
    normalizedSphericalAverage d f r x = 1 := by
  apply normalizedSphericalAverage_eq_of_eq_on_sphere hd f 1 r x
  intro ω
  apply hf
  calc
    ‖x + r • (ω : Euclidean d)‖ ≤ ‖x‖ + ‖r • (ω : Euclidean d)‖ :=
      norm_add_le _ _
    _ = ‖x‖ + |r| := by
      rw [norm_smul, Real.norm_eq_abs]
      have hω : ‖(ω : Euclidean d)‖ = 1 := by
        simpa only [mem_sphere_zero_iff_norm] using ω.property
      rw [hω, mul_one]
    _ ≤ R := hxr

/-- The ball test is translation invariant: the ball may be centred at an
arbitrary Euclidean point. -/
theorem normalizedSphericalAverage_eq_one_of_dist_add_abs_le
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) (a : Euclidean d)
    (R r : ℝ) (x : Euclidean d)
    (hf : ∀ y : Euclidean d, dist y a ≤ R → f y = 1)
    (hxr : dist x a + |r| ≤ R) :
    normalizedSphericalAverage d f r x = 1 := by
  apply normalizedSphericalAverage_eq_of_eq_on_sphere hd f 1 r x
  intro ω
  apply hf
  calc
    dist (x + r • (ω : Euclidean d)) a ≤
        dist (x + r • (ω : Euclidean d)) x + dist x a :=
      dist_triangle _ _ _
    _ = |r| + dist x a := by
      rw [dist_eq_norm]
      have hsub : x + r • (ω : Euclidean d) - x = r • (ω : Euclidean d) := by
        abel
      rw [hsub, norm_smul, Real.norm_eq_abs]
      have hω : ‖(ω : Euclidean d)‖ = 1 := by
        simpa only [mem_sphere_zero_iff_norm] using ω.property
      rw [hω, mul_one]
    _ = dist x a + |r| := by ac_rfl
    _ ≤ R := hxr

/-- A radius in the dilation set gives a pointwise lower bound whenever the
input is one on the corresponding sampling sphere. -/
theorem one_le_fractalSphericalMaximal_of_norm_add_abs_le
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (f : Euclidean d → ℂ) {r : ℝ}
    (hr : r ∈ E) (x : Euclidean d)
    (hf : ∀ y : Euclidean d, ‖y‖ ≤ 1 → f y = 1)
    (hxr : ‖x‖ + |r| ≤ 1) :
    1 ≤ fractalSphericalMaximal d E f x := by
  calc
    (1 : ENNReal) = ENNReal.ofReal ‖normalizedSphericalAverage d f r x‖ := by
      rw [normalizedSphericalAverage_eq_one_of_norm_add_abs_le hd f r x hf hxr]
      norm_num
    _ ≤ fractalSphericalMaximal d E f x :=
      normalizedSphericalAverage_le_fractalSphericalMaximal E f hr x

/-- The arbitrary-scale version of the elementary radius lower bound. -/
theorem one_le_fractalSphericalMaximal_of_norm_add_abs_le_of_eq_on_ball
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (f : Euclidean d → ℂ) {r R : ℝ}
    (hr : r ∈ E) (x : Euclidean d)
    (hf : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hxr : ‖x‖ + |r| ≤ R) :
    1 ≤ fractalSphericalMaximal d E f x := by
  calc
    (1 : ENNReal) = ENNReal.ofReal ‖normalizedSphericalAverage d f r x‖ := by
      rw [normalizedSphericalAverage_eq_one_of_norm_add_abs_le_of_eq_on_ball
        hd f R r x hf hxr]
      norm_num
    _ ≤ fractalSphericalMaximal d E f x :=
      normalizedSphericalAverage_le_fractalSphericalMaximal E f hr x

/-- The arbitrary-centre version of the radius-test lower bound. -/
theorem one_le_fractalSphericalMaximal_of_dist_add_abs_le
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (f : Euclidean d → ℂ)
    {r R : ℝ} (hr : r ∈ E) (a x : Euclidean d)
    (hf : ∀ y : Euclidean d, dist y a ≤ R → f y = 1)
    (hxr : dist x a + |r| ≤ R) :
    1 ≤ fractalSphericalMaximal d E f x := by
  calc
    (1 : ENNReal) = ENNReal.ofReal ‖normalizedSphericalAverage d f r x‖ := by
      rw [normalizedSphericalAverage_eq_one_of_dist_add_abs_le hd f a R r x hf hxr]
      norm_num
    _ ≤ fractalSphericalMaximal d E f x :=
      normalizedSphericalAverage_le_fractalSphericalMaximal E f hr x

/-- The same elementary radius test for the real-valued operator on Schwartz
data. -/
theorem one_le_fractalSphericalMaximalReal_of_norm_add_abs_le
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {r : ℝ} (hr : r ∈ E)
    (x : Euclidean d)
    (hf : ∀ y : Euclidean d, ‖y‖ ≤ 1 → f y = 1)
    (hxr : ‖x‖ + |r| ≤ 1) :
    1 ≤ fractalSphericalMaximalReal d E f x := by
  unfold fractalSphericalMaximalReal
  apply (ENNReal.toReal_le_toReal ENNReal.one_ne_top
    (fractalSphericalMaximal_ne_top hd E hE f x)).mpr
  simpa using
    (one_le_fractalSphericalMaximal_of_norm_add_abs_le hd E
      (f : Euclidean d → ℂ) hr x hf hxr)

/-- The arbitrary-scale real-valued radius test. -/
theorem one_le_fractalSphericalMaximalReal_of_norm_add_abs_le_of_eq_on_ball
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {r R : ℝ} (hr : r ∈ E)
    (x : Euclidean d)
    (hf : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hxr : ‖x‖ + |r| ≤ R) :
    1 ≤ fractalSphericalMaximalReal d E f x := by
  unfold fractalSphericalMaximalReal
  apply (ENNReal.toReal_le_toReal ENNReal.one_ne_top
    (fractalSphericalMaximal_ne_top hd E hE f x)).mpr
  simpa using
    (one_le_fractalSphericalMaximal_of_norm_add_abs_le_of_eq_on_ball hd E
      (f : Euclidean d → ℂ) hr x hf hxr)

/-- The elementary radius test controls the `L^q` norm from below by the
norm of a literal ball indicator.  It is deliberately stated before any
asymptotic estimate for the ball volume. -/
theorem eLpNorm_ball_indicator_le_eLpNorm_fractalSphericalMaximalReal
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {r R s : ℝ} (hr : r ∈ E)
    (hf : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hsr : s + |r| ≤ R) (q : ℝ) :
    eLpNorm ((ball (0 : Euclidean d) s).indicator fun _ : Euclidean d => (1 : ℝ))
        (ENNReal.ofReal q) volume ≤
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume := by
  apply eLpNorm_mono
  intro x
  by_cases hx : x ∈ ball (0 : Euclidean d) s
  · rw [Set.indicator_of_mem hx, norm_one]
    have hxnorm : ‖x‖ < s := by
      simpa only [mem_ball, dist_zero_right] using hx
    have hxr : ‖x‖ + |r| ≤ R := by
      linarith [hxnorm.le, hsr]
    change 1 ≤ ‖(fractalSphericalMaximal d E (f : Euclidean d → ℂ) x).toReal‖
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact one_le_fractalSphericalMaximalReal_of_norm_add_abs_le_of_eq_on_ball
      hd E hE f hr x hf hxr
  · rw [Set.indicator_of_notMem hx]
    simp

/-- The indicator norm occurring in the preceding lower bound has the usual
explicit formula at finite positive exponents. -/
theorem eLpNorm_ball_indicator_one
    {d : ℕ} (s q : ℝ) (hq : 0 < q) :
    eLpNorm ((ball (0 : Euclidean d) s).indicator fun _ : Euclidean d => (1 : ℝ))
        (ENNReal.ofReal q) volume =
      volume (ball (0 : Euclidean d) s) ^ q⁻¹ := by
  rw [eLpNorm_indicator_const isOpen_ball.measurableSet
    (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top]
  simp only [enorm_one, one_mul, ENNReal.toReal_ofReal hq.le, one_div]

/-- An explicit `L^q` lower bound supplied by the smooth ball test. -/
theorem volume_ball_rpow_le_eLpNorm_fractalSphericalMaximalReal
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {r R s q : ℝ} (hr : r ∈ E)
    (hf : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hsr : s + |r| ≤ R) (hq : 0 < q) :
    volume (ball (0 : Euclidean d) s) ^ q⁻¹ ≤
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume := by
  rw [← eLpNorm_ball_indicator_one s q hq]
  exact eLpNorm_ball_indicator_le_eLpNorm_fractalSphericalMaximalReal
    hd E hE f hr hf hsr q

/-- There is a Schwartz test function which is one on the Euclidean unit
ball and zero outside the ball of radius two.  This is the smooth replacement
for the characteristic ball in the elementary sharpness test. -/
theorem exists_schwartz_unit_ball_test (d : ℕ) :
    ∃ f : SchwartzMap (Euclidean d) ℂ,
      (∀ y : Euclidean d, ‖y‖ ≤ 1 → f y = 1) ∧
      (∀ y : Euclidean d, 2 ≤ ‖y‖ → f y = 0) := by
  exact exists_schwartz_frequency_cutoff d

/-- Smooth compactly-supported replacements for characteristic functions of
balls are available at every positive scale. -/
theorem exists_schwartz_ball_test (d : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ f : SchwartzMap (Euclidean d) ℂ,
      (∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1) ∧
      (∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0) := by
  let b : ContDiffBump (0 : Euclidean d) :=
    ⟨R, 2 * R, hR, by linarith⟩
  let g : Euclidean d → ℂ := Complex.ofRealCLM ∘ b
  have hcompact : HasCompactSupport g := by
    exact b.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_⟩
  · intro y hy
    change (b y : ℂ) = 1
    have hmem : y ∈ closedBall (0 : Euclidean d) b.rIn := by
      simpa only [mem_closedBall, dist_zero_right] using hy
    rw [b.one_of_mem_closedBall hmem]
    norm_num
  · intro y hy
    change (b y : ℂ) = 0
    have hdist : b.rOut ≤ dist y (0 : Euclidean d) := by
      simpa only [dist_zero_right] using hy
    rw [b.zero_of_le_dist hdist]
    norm_num

/-- The smooth ball test can additionally be chosen with pointwise norm at
most one.  This is the input-side estimate needed for the large-ball version
of the translation obstruction. -/
theorem exists_schwartz_ball_test_bounded (d : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ f : SchwartzMap (Euclidean d) ℂ,
      (∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1) ∧
      (∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0) ∧
      (∀ y : Euclidean d, ‖f y‖ ≤ 1) := by
  let b : ContDiffBump (0 : Euclidean d) :=
    ⟨R, 2 * R, hR, by linarith⟩
  let g : Euclidean d → ℂ := Complex.ofRealCLM ∘ b
  have hcompact : HasCompactSupport g := by
    exact b.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_, ?_⟩
  · intro y hy
    change (b y : ℂ) = 1
    have hmem : y ∈ closedBall (0 : Euclidean d) b.rIn := by
      simpa only [mem_closedBall, dist_zero_right] using hy
    rw [b.one_of_mem_closedBall hmem]
    norm_num
  · intro y hy
    change (b y : ℂ) = 0
    have hdist : b.rOut ≤ dist y (0 : Euclidean d) := by
      simpa only [dist_zero_right] using hy
    rw [b.zero_of_le_dist hdist]
    norm_num
  · intro y
    change ‖(b y : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (ContDiffBump.nonneg' b y)]
    exact ContDiffBump.le_one b

/-- The `L^p` norm of a complex-valued unit ball indicator. -/
theorem eLpNorm_ball_indicator_one_complex
    {d : ℕ} (s p : ℝ) (hp : 0 < p) :
    eLpNorm ((ball (0 : Euclidean d) s).indicator fun _ : Euclidean d => (1 : ℂ))
        (ENNReal.ofReal p) volume =
      volume (ball (0 : Euclidean d) s) ^ p⁻¹ := by
  rw [eLpNorm_indicator_const isOpen_ball.measurableSet
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
  simp only [enorm_one, one_mul, ENNReal.toReal_ofReal hp.le, one_div]

/-- A bounded smooth ball test has input `L^p` norm no larger than the norm
of the enclosing radius-`2R` ball indicator. -/
theorem eLpNorm_schwartz_ball_test_le_volume_ball
    {d : ℕ} {R p : ℝ} (hp : 0 < p)
    (f : SchwartzMap (Euclidean d) ℂ)
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (hbound : ∀ y : Euclidean d, ‖f y‖ ≤ 1) :
    eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤
      volume (ball (0 : Euclidean d) (2 * R)) ^ p⁻¹ := by
  rw [← eLpNorm_ball_indicator_one_complex (2 * R) p hp]
  apply eLpNorm_mono
  intro x
  by_cases hx : x ∈ ball (0 : Euclidean d) (2 * R)
  · rw [Set.indicator_of_mem hx, norm_one]
    exact hbound x
  · rw [Set.indicator_of_notMem hx]
    have hnot : ¬ ‖x‖ < 2 * R := by
      simpa only [mem_ball, dist_zero_right] using hx
    have hge : 2 * R ≤ ‖x‖ := le_of_not_gt hnot
    rw [hzero x hge]

/-- The smooth-ball test can be centred anywhere.  This is the concrete
Schwartz family used for translated test functions. -/
theorem exists_schwartz_ball_test_at
    {d : ℕ} (a : Euclidean d) {R : ℝ} (hR : 0 < R) :
    ∃ f : SchwartzMap (Euclidean d) ℂ,
      (∀ y : Euclidean d, dist y a ≤ R → f y = 1) ∧
      (∀ y : Euclidean d, 2 * R ≤ dist y a → f y = 0) := by
  let b : ContDiffBump a := ⟨R, 2 * R, hR, by linarith⟩
  let g : Euclidean d → ℂ := Complex.ofRealCLM ∘ b
  have hcompact : HasCompactSupport g := by
    exact b.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_⟩
  · intro y hy
    change (b y : ℂ) = 1
    have hmem : y ∈ closedBall a b.rIn := hy
    rw [b.one_of_mem_closedBall hmem]
    norm_num
  · intro y hy
    change (b y : ℂ) = 0
    exact_mod_cast b.zero_of_le_dist hy

/-- A smooth ball test gives a pointwise lower bound for every point whose
sampling sphere stays inside that ball. -/
theorem exists_schwartz_ball_radius_test
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) {r R : ℝ}
    (hr : r ∈ E) (hR : 0 < R) :
    ∃ f : SchwartzMap (Euclidean d) ℂ,
      (∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1) ∧
      (∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0) ∧
      ∀ x : Euclidean d, ‖x‖ + |r| ≤ R →
        1 ≤ fractalSphericalMaximal d E (f : Euclidean d → ℂ) x := by
  obtain ⟨f, hf_one, hf_zero⟩ := exists_schwartz_ball_test d hR
  refine ⟨f, hf_one, hf_zero, ?_⟩
  intro x hx
  exact one_le_fractalSphericalMaximal_of_norm_add_abs_le_of_eq_on_ball
    hd E (f : Euclidean d → ℂ) hr x hf_one hx

end

end Auto.Spherical.FractalDilations.SharpnessTests
end Former_SharpnessTests

/- ===== Former FractalDilations/AnnulusBump.lean ===== -/
section Former_AnnulusBump

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.SurfaceCore







/-!
# Nonnegative smooth ball data for the annulus test

The annulus obstruction needs the small smooth ball test with its positivity
visible in the statement, rather than merely its absolute-value bound.
-/

namespace Auto.Spherical.FractalDilations.AnnulusBump

open MeasureTheory Metric Set

noncomputable section

/-- A compactly supported smooth ball cutoff may be chosen real-valued,
nonnegative, and bounded by one. -/
theorem exists_schwartz_ball_test_nonnegative_bounded
    (d : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ f : SchwartzMap (Euclidean d) ℂ,
      (∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1) ∧
      (∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0) ∧
      (∀ y : Euclidean d, 0 ≤ (f y).re) ∧
      (∀ y : Euclidean d, (f y).im = 0) ∧
      (∀ y : Euclidean d, ‖f y‖ ≤ 1) := by
  let b : ContDiffBump (0 : Euclidean d) := ⟨R, 2 * R, hR, by linarith⟩
  let g : Euclidean d → ℂ := Complex.ofRealCLM ∘ b
  have hcompact : HasCompactSupport g := by
    exact b.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    change (b y : ℂ) = 1
    have hmem : y ∈ closedBall (0 : Euclidean d) b.rIn := by
      simpa only [mem_closedBall, dist_zero_right] using hy
    rw [b.one_of_mem_closedBall hmem]
    norm_num
  · intro y hy
    change (b y : ℂ) = 0
    have hdist : b.rOut ≤ dist y (0 : Euclidean d) := by
      simpa only [dist_zero_right] using hy
    rw [b.zero_of_le_dist hdist]
    norm_num
  · intro y
    change 0 ≤ b y
    exact ContDiffBump.nonneg' b y
  · intro y
    change (b y : ℂ).im = 0
    simp
  · intro y
    change ‖(b y : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (ContDiffBump.nonneg' b y)]
    exact ContDiffBump.le_one b

end

/-- A nonnegative smooth ball cutoff has at least the mass of the ball on
which it is identically one. -/
theorem volume_ball_toReal_le_integral_re_of_eq_one_nonneg
    {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ) {R : ℝ}
    (hOne : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re) :
    (volume (ball (0 : Euclidean d) R)).toReal ≤
      ∫ y : Euclidean d, (f y).re := by
  let g : Euclidean d → ℝ :=
    (ball (0 : Euclidean d) R).indicator fun _ => (1 : ℝ)
  have hball_top : volume (ball (0 : Euclidean d) R) ≠ (⊤ : ENNReal) :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := R)).ne
  have hg_integrable : Integrable g volume := by
    dsimp [g]
    rw [integrable_indicator_iff isOpen_ball.measurableSet]
    exact integrableOn_const hball_top
  have hpoint : ∀ y : Euclidean d, g y ≤ (f y).re := by
    intro y
    dsimp [g]
    by_cases hy : y ∈ ball (0 : Euclidean d) R
    · rw [Set.indicator_of_mem hy]
      have hynorm : ‖y‖ ≤ R := by
        have : ‖y‖ < R := by
          simpa only [mem_ball, dist_zero_right] using hy
        exact this.le
      rw [hOne y hynorm]
      norm_num
    · rw [Set.indicator_of_notMem hy]
      exact hnonneg y
  calc
    (volume (ball (0 : Euclidean d) R)).toReal = ∫ y : Euclidean d, g y := by
      dsimp [g]
      rw [integral_indicator isOpen_ball.measurableSet, integral_const,
        Measure.real_def, Measure.restrict_apply_univ]
      simp
    _ ≤ ∫ y : Euclidean d, (f y).re :=
      integral_mono hg_integrable f.integrable.re hpoint

end Auto.Spherical.FractalDilations.AnnulusBump
end Former_AnnulusBump

/- ===== Former FractalDilations/AnnulusCore.lean ===== -/
section Former_AnnulusCore

/- This file was machine-generated by Codex -/

open Auto.Spherical.FourierRadius
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.SurfaceCore







/-!
# Mass preservation for normalized spherical averages

The annulus sharpness example is most efficiently handled by total mass: a
small nonnegative ball has mass of order `δ^d`, and every fixed normalized
spherical average preserves that mass.  This file exposes that Fubini fact
for the literal spherical averages used by the existing Stein development.
-/

namespace Auto.Spherical.FractalDilations.AnnulusCore

open MeasureTheory Metric Set

noncomputable section

private theorem integrable_sphere_translate_product
    {d : ℕ} (f : Euclidean d → ℂ) (hfcont : Continuous f)
    (hf : Integrable f volume) (r : ℝ) :
    Integrable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        f (p.1 + r • (p.2 : Euclidean d)))
      (volume.prod (unitSurfaceMeasure d)) := by
  have hmeas : AEStronglyMeasurable
      (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
        f (p.1 + r • (p.2 : Euclidean d)))
      (volume.prod (unitSurfaceMeasure d)) := by
    apply (hfcont.comp (continuous_fst.add
      ((continuous_const : Continuous fun _ : Euclidean d × sphere (0 : Euclidean d) 1 => r).smul
        (continuous_subtype_val.comp continuous_snd)))).aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).2 ?_
  constructor
  · filter_upwards with ω
    exact hf.comp_add_right (r • (ω : Euclidean d))
  · have h_eq : (fun ω : sphere (0 : Euclidean d) 1 =>
        ∫ x : Euclidean d, ‖f (x + r • (ω : Euclidean d))‖) =
        fun _ => ∫ x : Euclidean d, ‖f x‖ := by
      funext ω
      exact integral_add_right_eq_self (fun x : Euclidean d => ‖f x‖)
        (r • (ω : Euclidean d))
    rw [h_eq]
    exact integrable_const _

/-- A normalized spherical average preserves the integral of a continuous
integrable function. -/
theorem integral_normalizedSphericalAverage_eq_integral
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ)
    (hfcont : Continuous f) (hf : Integrable f volume) (r : ℝ) :
    (∫ x : Euclidean d, normalizedSphericalAverage d f r x) =
      ∫ x : Euclidean d, f x := by
  have hprod := integrable_sphere_translate_product f hfcont hf r
  have havg :
      (∫ x : Euclidean d, sphericalAverage d f r x) =
        (surfaceMass d : ℂ) * ∫ x : Euclidean d, f x := by
    calc
      (∫ x : Euclidean d, sphericalAverage d f r x) =
          ∫ x : Euclidean d, ∫ ω : sphere (0 : Euclidean d) 1,
            f (x + r • (ω : Euclidean d)) ∂unitSurfaceMeasure d := rfl
      _ = ∫ ω : sphere (0 : Euclidean d) 1, ∫ x : Euclidean d,
          f (x + r • (ω : Euclidean d)) ∂volume ∂unitSurfaceMeasure d :=
        integral_integral_swap hprod
      _ = ∫ _ : sphere (0 : Euclidean d) 1,
          (∫ x : Euclidean d, f x ∂volume) ∂unitSurfaceMeasure d := by
        apply integral_congr_ae
        filter_upwards with ω
        exact integral_add_right_eq_self f (r • (ω : Euclidean d))
      _ = (surfaceMass d : ℂ) * ∫ x : Euclidean d, f x := by
        simp [surfaceMass]
  calc
    (∫ x : Euclidean d, normalizedSphericalAverage d f r x) =
        ((surfaceMass d)⁻¹ : ℂ) * ∫ x : Euclidean d, sphericalAverage d f r x := by
      unfold normalizedSphericalAverage
      rw [integral_const_mul]
    _ = ((surfaceMass d)⁻¹ : ℂ) *
        ((surfaceMass d : ℂ) * ∫ x : Euclidean d, f x) := by rw [havg]
    _ = ∫ x : Euclidean d, f x := by
      have hmass : (surfaceMass d : ℂ) ≠ 0 := by
        exact_mod_cast surfaceMass_ne_zero hd
      field_simp

/-- On real-valued data, the normalized spherical average is real-valued and
has the literal scalar integral formula. -/
theorem normalizedSphericalAverage_ofReal_eq
    {d : ℕ} (g : Euclidean d → ℝ) (r : ℝ) (x : Euclidean d) :
    normalizedSphericalAverage d (fun y => (g y : ℂ)) r x =
      ((surfaceMass d)⁻¹ * ∫ ω : sphere (0 : Euclidean d) 1,
        g (x + r • (ω : Euclidean d)) ∂unitSurfaceMeasure d : ℝ) := by
  unfold normalizedSphericalAverage sphericalAverage
  have hInt :
      (∫ ω : sphere (0 : Euclidean d) 1,
        (g (x + r • (ω : Euclidean d)) : ℂ) ∂unitSurfaceMeasure d) =
        ((∫ ω : sphere (0 : Euclidean d) 1,
          g (x + r • (ω : Euclidean d)) ∂unitSurfaceMeasure d : ℝ) : ℂ) := by
    exact integral_ofReal
  rw [hInt]
  push_cast
  rfl

/-- Nonnegative real data have nonnegative normalized spherical averages in
the literal real coordinate. -/
theorem normalizedSphericalAverage_re_nonneg_of_nonneg
    {d : ℕ} (hd : 0 < d) (g : Euclidean d → ℝ) (hg : ∀ y, 0 ≤ g y)
    (r : ℝ) (x : Euclidean d) :
    0 ≤ (normalizedSphericalAverage d (fun y => (g y : ℂ)) r x).re := by
  rw [normalizedSphericalAverage_ofReal_eq]
  apply mul_nonneg
  · exact inv_nonneg.mpr (surfaceMass_pos hd).le
  · apply integral_nonneg
    intro ω
    exact hg _

/-- The standard smooth ball cutoff can be chosen real-valued and
nonnegative, in addition to being one on the inner ball, supported in the
doubled ball, and bounded by one. -/
theorem exists_schwartz_ball_test_real_nonnegative_bounded
    (d : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ f : SchwartzMap (Euclidean d) ℂ,
      (∀ y : Euclidean d, f y = ((f y).re : ℂ)) ∧
      (∀ y : Euclidean d, 0 ≤ (f y).re) ∧
      (∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1) ∧
      (∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0) ∧
      (∀ y : Euclidean d, ‖f y‖ ≤ 1) := by
  let b : ContDiffBump (0 : Euclidean d) :=
    ⟨R, 2 * R, hR, by linarith⟩
  let g : Euclidean d → ℂ := Complex.ofRealCLM ∘ b
  have hcompact : HasCompactSupport g := by
    exact b.hasCompactSupport.comp_left (by rfl)
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    change (b y : ℂ) = (((b y : ℂ).re : ℝ) : ℂ)
    simp
  · intro y
    change 0 ≤ (b y : ℂ).re
    simpa using ContDiffBump.nonneg' b y
  · intro y hy
    change (b y : ℂ) = 1
    have hmem : y ∈ closedBall (0 : Euclidean d) b.rIn := by
      simpa only [mem_closedBall, dist_zero_right] using hy
    rw [b.one_of_mem_closedBall hmem]
    norm_num
  · intro y hy
    change (b y : ℂ) = 0
    have hdist : b.rOut ≤ dist y (0 : Euclidean d) := by
      simpa only [dist_zero_right] using hy
    rw [b.zero_of_le_dist hdist]
    norm_num
  · intro y
    change ‖(b y : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (ContDiffBump.nonneg' b y)]
    exact ContDiffBump.le_one b

end

end Auto.Spherical.FractalDilations.AnnulusCore
end Former_AnnulusCore

/- ===== Former FractalDilations/ClusterGeometry.lean ===== -/
section Former_ClusterGeometry

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.SeparatedPacking
open Auto.Spherical.SurfaceCore







/-!
# Cartesian geometry for clustered-radius tests

The clustered-radius construction uses thin slabs in the distinguished radial
coordinate and a common transverse ball.  This file records their exact
Lebesgue volumes and the elementary disjointness supplied by separated radial
centres.  It is deliberately independent of the spherical averaging step.
-/

namespace Auto.Spherical.FractalDilations.ClusterGeometry

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

/-- The standard splitting of `Euclidean (n + 1)` into its first `n`
coordinates and its final coordinate. -/
def euclideanSuccCoordinates (n : ℕ) : Euclidean (n + 1) → Euclidean n × ℝ :=
  fun x =>
    (MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i => x (Fin.castAdd 1 i)),
      x (Fin.last n))

/-- A transverse ball times an open interval in the final coordinate. -/
def horizontalSlab (n : ℕ) (ρ a b : ℝ) : Set (Euclidean (n + 1)) :=
  euclideanSuccCoordinates n ⁻¹' (ball (0 : Euclidean n) ρ ×ˢ Ioo a b)

theorem measurable_euclideanSuccCoordinates (n : ℕ) :
    Measurable (euclideanSuccCoordinates n) := by
  have hfirst : Measurable (fun x : Euclidean (n + 1) =>
      MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i => x (Fin.castAdd 1 i))) := by
    apply (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp
    apply measurable_pi_lambda
    intro i
    fun_prop
  exact hfirst.prodMk (by fun_prop)

theorem map_euclideanSuccCoordinates_volume (n : ℕ) :
    Measure.map (euclideanSuccCoordinates n) volume =
      ((volume : Measure (Euclidean n)).prod volume) := by
  change Measure.map (fun x : Euclidean (n + 1) =>
      (MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i => x (Fin.castAdd 1 i)),
        x (Fin.last n))) volume = ((volume : Measure (Euclidean n)).prod volume)
  exact Auto.Spherical.SurfaceCore.map_euclideanSucc_coordinates_volume n

theorem measurableSet_horizontalSlab (n : ℕ) (ρ a b : ℝ) :
    MeasurableSet (horizontalSlab n ρ a b) := by
  exact ((isOpen_ball.prod isOpen_Ioo).measurableSet).preimage
    (measurable_euclideanSuccCoordinates n)

/-- The exact volume of a Cartesian transverse-ball/radial-interval slab. -/
theorem volume_horizontalSlab (n : ℕ) (ρ a b : ℝ) :
    volume (horizontalSlab n ρ a b) =
      volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (b - a) := by
  let A : Set (Euclidean n × ℝ) := ball (0 : Euclidean n) ρ ×ˢ Ioo a b
  have hA : MeasurableSet A := (isOpen_ball.prod isOpen_Ioo).measurableSet
  calc
    volume (horizontalSlab n ρ a b) = Measure.map (euclideanSuccCoordinates n) volume A := by
      symm
      simpa only [horizontalSlab, A] using
        (Measure.map_apply (measurable_euclideanSuccCoordinates n) hA)
    _ = ((volume : Measure (Euclidean n)).prod volume) A := by
      rw [map_euclideanSuccCoordinates_volume]
    _ = volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (b - a) := by
      simp only [A, Measure.prod_prod, Real.volume_Ioo]

/-- A horizontal slab of half-width `h`, centred at the final coordinate
`t`. -/
def centeredHorizontalSlab (n : ℕ) (ρ h t : ℝ) : Set (Euclidean (n + 1)) :=
  horizontalSlab n ρ (t - h) (t + h)

/-- Slabs with sufficiently separated final-coordinate centres are disjoint.
Their transverse radii may be different. -/
theorem disjoint_centeredHorizontalSlab_of_two_mul_le_abs_sub
    {n : ℕ} {ρ ρ' h s t : ℝ} (hsep : 2 * h ≤ |s - t|) :
    Disjoint (centeredHorizontalSlab n ρ h s)
      (centeredHorizontalSlab n ρ' h t) := by
  unfold centeredHorizontalSlab horizontalSlab
  apply Disjoint.preimage
  apply Disjoint.set_prod_right
  rw [Ioo_disjoint_Ioo]
  by_cases hst : s ≤ t
  · have habs : |s - t| = t - s := by
      calc
        |s - t| = -(s - t) := abs_of_nonpos (sub_nonpos.mpr hst)
        _ = t - s := by ring
    rw [habs] at hsep
    calc
      min (s + h) (t + h) ≤ s + h := min_le_left _ _
      _ ≤ t - h := by linarith
      _ ≤ max (s - h) (t - h) := le_max_right _ _
  · have hts : t ≤ s := le_of_not_ge hst
    have habs : |s - t| = s - t := abs_of_nonneg (sub_nonneg.mpr hts)
    rw [habs] at hsep
    calc
      min (s + h) (t + h) ≤ t + h := min_le_right _ _
      _ ≤ s - h := by linarith
      _ ≤ max (s - h) (t - h) := le_max_left _ _

/-- A strictly separated finite family of centres produces pairwise disjoint
horizontal slabs when the half-width is one quarter of the separation mesh. -/
theorem strictlySeparated_pairwiseDisjoint_centeredHorizontalSlabs
    {n : ℕ} {s : Finset ℝ} {ρ δ : ℝ}
    (hsep : StrictlySeparated s (δ / 2)) :
    (↑s : Set ℝ).PairwiseDisjoint
      (fun t => centeredHorizontalSlab n ρ (δ / 8) t) := by
  intro r hr t ht hrt
  apply disjoint_centeredHorizontalSlab_of_two_mul_le_abs_sub
  have hstrict : δ / 2 < |r - t| := hsep hr ht hrt
  by_cases hδ : 0 ≤ δ
  · have hquarter : δ / 4 ≤ δ / 2 := by linarith
    calc
      2 * (δ / 8) = δ / 4 := by ring
      _ ≤ |r - t| := (lt_of_le_of_lt hquarter hstrict).le
  · have hδneg : δ < 0 := lt_of_not_ge hδ
    calc
      2 * (δ / 8) = δ / 4 := by ring
      _ ≤ 0 := by linarith
      _ ≤ |r - t| := abs_nonneg _

/-- The volume of a centred slab is the transverse-ball volume times its
full radial width. -/
theorem volume_centeredHorizontalSlab (n : ℕ) (ρ h t : ℝ) :
    volume (centeredHorizontalSlab n ρ h t) =
      volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * h) := by
  rw [centeredHorizontalSlab, volume_horizontalSlab]
  congr 2
  ring

theorem measurableSet_centeredHorizontalSlab (n : ℕ) (ρ h t : ℝ) :
    MeasurableSet (centeredHorizontalSlab n ρ h t) := by
  exact measurableSet_horizontalSlab n ρ (t - h) (t + h)

/-- Exact volume of the finite disjoint slab union used as the output region
in the clustered-radius test. -/
theorem volume_biUnion_centeredHorizontalSlab
    {n : ℕ} {s : Finset ℝ} {ρ δ : ℝ}
    (hsep : StrictlySeparated s (δ / 2)) :
    volume (⋃ t ∈ s, centeredHorizontalSlab n ρ (δ / 8) t) =
      (s.card : ENNReal) *
        (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * (δ / 8))) := by
  rw [measure_biUnion_finset
    (strictlySeparated_pairwiseDisjoint_centeredHorizontalSlabs (n := n) (ρ := ρ) hsep)
    (fun t _ => measurableSet_centeredHorizontalSlab n ρ (δ / 8) t)]
  simp only [volume_centeredHorizontalSlab]
  simp

end

end Auto.Spherical.FractalDilations.ClusterGeometry

end Former_ClusterGeometry

/- ===== Former FractalDilations/SharpnessNormLower.lean ===== -/
section Former_SharpnessNormLower

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.SurfaceCore







/-!
# `L^q` lower bounds from geometric witnesses

The sharpness examples produce a pointwise lower bound on a measurable test
region.  This module packages the resulting `eLpNorm` lower bound, keeping
the later annulus and clustered-radius arguments focused on their geometry.
-/

namespace Auto.Spherical.FractalDilations.SharpnessNormLower

open MeasureTheory Set

noncomputable section

/-- If a nonnegative real function is at least `a` on a measurable region,
then its `L^q` seminorm dominates `a` times the `q`th root of that region's
volume. -/
theorem ENNReal.ofReal_mul_volume_rpow_le_eLpNorm_of_lower_bound
    {d : ℕ} (S : Set (Euclidean d)) (hS : MeasurableSet S)
    {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q)
    (g : Euclidean d → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hlower : ∀ x ∈ S, a ≤ g x) :
    ENNReal.ofReal a * volume S ^ (1 / q) ≤
      eLpNorm g (ENNReal.ofReal q) volume := by
  have hnorm : enorm a = ENNReal.ofReal a := by
    rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal ha]
    congr
    apply NNReal.eq
    simp [Real.norm_of_nonneg ha]
  have hindicator :
      eLpNorm (S.indicator fun _ : Euclidean d => a) (ENNReal.ofReal q) volume ≤
        eLpNorm g (ENNReal.ofReal q) volume := by
    apply eLpNorm_mono_real
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg ha]
      exact hlower x hx
    · rw [Set.indicator_of_notMem hx]
      simpa using hg x
  rw [eLpNorm_indicator_const hS
    (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top, hnorm,
    ENNReal.toReal_ofReal hq.le] at hindicator
  exact hindicator

end

end Auto.Spherical.FractalDilations.SharpnessNormLower
end Former_SharpnessNormLower

/- ===== Former FractalDilations/SharpnessVolume.lean ===== -/
section Former_SharpnessVolume

/- This file was machine-generated by Codex -/


open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.SurfaceCore






/-!
# Large-ball volume growth for sharpness tests

This file isolates the elementary volume growth used by the translation
obstruction.  Keeping it separate means that the eventual analytic
unboundedness proof only has to supply its Schwartz test functions and the
normalization argument.
-/

namespace Auto.Spherical.FractalDilations.SharpnessVolume

open MeasureTheory Metric Set Filter

noncomputable section

/-- The real volume of a positive Euclidean ball is its radius to the
dimension times the real volume of the unit ball. -/
theorem volume_ball_toReal (d : ℕ) (r : ℝ) (hr : 0 < r) :
    (volume (ball (0 : Euclidean d) r)).toReal =
      r ^ d * (volume (ball (0 : Euclidean d) 1)).toReal := by
  rw [Measure.addHaar_ball_of_pos volume (0 : Euclidean d) hr]
  simp only [finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]

/-- The real volume of the Euclidean unit ball is positive in positive
dimension. -/
theorem volume_unit_ball_toReal_pos {d : ℕ} (hd : 0 < d) :
    0 < (volume (ball (0 : Euclidean d) 1)).toReal := by
  apply ENNReal.toReal_pos
  · exact (Metric.measure_ball_pos volume (0 : Euclidean d) (by norm_num)).ne'
  · exact (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d))
      (r := (1 : ℝ))).ne

/-- A positive-radius Euclidean ball has a nonzero finite real power of its
volume.  This supplies the nondegeneracy side conditions for normalization. -/
theorem volume_ball_rpow_ne_zero_ne_top
    {d : ℕ} (r e : ℝ) (hr : 0 < r) :
    volume (ball (0 : Euclidean d) r) ^ e ≠ 0 ∧
      volume (ball (0 : Euclidean d) r) ^ e ≠ (⊤ : ENNReal) := by
  have hpos : 0 < volume (ball (0 : Euclidean d) r) :=
    Metric.measure_ball_pos volume (0 : Euclidean d) hr
  have htop : volume (ball (0 : Euclidean d) r) ≠ (⊤ : ENNReal) :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := r)).ne
  exact ⟨(ENNReal.rpow_pos hpos htop).ne',
    ENNReal.rpow_ne_top_of_ne_zero hpos.ne' htop⟩

/-- A higher real power eventually dominates a lower real power, with any
fixed positive coefficient on the right.  This is the purely ordered-field
part of the large-ball test. -/
theorem exists_rpow_separation {a b B C : ℝ} (hB : 0 < B) (hab : a < b) :
    ∃ T : ℝ, 0 < T ∧ C * T ^ a < T ^ b * B := by
  have hgrow : ∀ᶠ T : ℝ in atTop, C / B < T ^ (b - a) :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_gt_atTop (C / B)
  have hpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  obtain ⟨T, hTgrow, hTpos⟩ := (hgrow.and hpos).exists
  refine ⟨T, hTpos, ?_⟩
  have hbase : C < T ^ (b - a) * B := (div_lt_iff₀ hB).mp hTgrow
  have hTa : 0 < T ^ a := Real.rpow_pos_of_pos hTpos _
  have hmul : C * T ^ a < (T ^ (b - a) * B) * T ^ a := by
    calc
      C * T ^ a = C * T ^ a := rfl
      _ < (T ^ (b - a) * B) * T ^ a :=
        mul_lt_mul_of_pos_right hbase hTa
  calc
    C * T ^ a < (T ^ (b - a) * B) * T ^ a := hmul
    _ = (T ^ (b - a) * T ^ a) * B := by ring
    _ = T ^ ((b - a) + a) * B := by rw [← Real.rpow_add hTpos]
    _ = T ^ b * B := by
      have hsum : (b - a) + a = b := by ring
      rw [hsum]

/-- The power separation can be arranged beyond any prescribed threshold. -/
theorem exists_rpow_separation_above {a b B C M : ℝ} (hB : 0 < B) (hab : a < b) :
    ∃ T : ℝ, M < T ∧ 0 < T ∧ C * T ^ a < T ^ b * B := by
  have hgrow : ∀ᶠ T : ℝ in atTop, C / B < T ^ (b - a) :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_gt_atTop (C / B)
  have habove : ∀ᶠ T : ℝ in atTop, M < T := eventually_gt_atTop M
  have hpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  obtain ⟨T, hTgrow, hTM, hTpos⟩ := (hgrow.and (habove.and hpos)).exists
  refine ⟨T, hTM, hTpos, ?_⟩
  have hbase : C < T ^ (b - a) * B := (div_lt_iff₀ hB).mp hTgrow
  have hTa : 0 < T ^ a := Real.rpow_pos_of_pos hTpos _
  calc
    C * T ^ a < (T ^ (b - a) * B) * T ^ a :=
      mul_lt_mul_of_pos_right hbase hTa
    _ = (T ^ (b - a) * T ^ a) * B := by ring
    _ = T ^ ((b - a) + a) * B := by rw [← Real.rpow_add hTpos]
    _ = T ^ b * B := by
      have hsum : (b - a) + a = b := by ring
      rw [hsum]

/-- At every pair of positive exponents with `p < q` in reciprocal
coordinates, the volume gained by a large ball beats the input-volume cost.
The radii are `T` and `4T`; this fixed factor is convenient for smooth ball
cutoffs supported in the ball of radius `2R` with `R = 2T`. -/
theorem exists_large_ball_volume_gap
    {d : ℕ} (hd : 0 < d) {p q C : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hbad : p⁻¹ < q⁻¹) :
    ∃ T : ℝ, 0 < T ∧
      C * (volume (ball (0 : Euclidean d) (4 * T))).toReal ^ p⁻¹ <
        (volume (ball (0 : Euclidean d) T)).toReal ^ q⁻¹ := by
  let V : ℝ := (volume (ball (0 : Euclidean d) 1)).toReal
  have hV : 0 < V := volume_unit_ball_toReal_pos hd
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hab : (d : ℝ) * p⁻¹ < (d : ℝ) * q⁻¹ :=
    mul_lt_mul_of_pos_left hbad hd'
  have hB : 0 < V ^ q⁻¹ := Real.rpow_pos_of_pos hV _
  obtain ⟨T, hT, hsep⟩ := exists_rpow_separation
    (a := (d : ℝ) * p⁻¹) (b := (d : ℝ) * q⁻¹)
    (B := V ^ q⁻¹) (C := C * 4 ^ ((d : ℝ) * p⁻¹) * V ^ p⁻¹) hB hab
  refine ⟨T, hT, ?_⟩
  rw [volume_ball_toReal d (4 * T) (by positivity), volume_ball_toReal d T hT]
  change C * (((4 * T) ^ d * V) ^ p⁻¹) < (T ^ d * V) ^ q⁻¹
  have hleft : C * (((4 * T) ^ d * V) ^ p⁻¹) =
      (C * 4 ^ ((d : ℝ) * p⁻¹) * V ^ p⁻¹) * T ^ ((d : ℝ) * p⁻¹) := by
    rw [Real.mul_rpow (pow_nonneg (by positivity) _) hV.le]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 4 * T)]
    rw [Real.mul_rpow (by positivity) hT.le]
    ring
  have hright : (T ^ d * V) ^ q⁻¹ = T ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹ := by
    rw [Real.mul_rpow (pow_nonneg hT.le _) hV.le]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
  rw [hleft, hright]
  exact hsep

/-- The large-ball volume gap can be obtained with radius beyond any fixed
threshold.  This is the form used when the chosen radius must dominate a
member of the dilation set. -/
theorem exists_large_ball_volume_gap_above
    {d : ℕ} (hd : 0 < d) {p q C M : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hbad : p⁻¹ < q⁻¹) :
    ∃ T : ℝ, M < T ∧
      C * (volume (ball (0 : Euclidean d) (4 * T))).toReal ^ p⁻¹ <
        (volume (ball (0 : Euclidean d) T)).toReal ^ q⁻¹ := by
  let V : ℝ := (volume (ball (0 : Euclidean d) 1)).toReal
  have hV : 0 < V := volume_unit_ball_toReal_pos hd
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hab : (d : ℝ) * p⁻¹ < (d : ℝ) * q⁻¹ :=
    mul_lt_mul_of_pos_left hbad hd'
  have hB : 0 < V ^ q⁻¹ := Real.rpow_pos_of_pos hV _
  obtain ⟨T, hTM, hT, hsep⟩ := exists_rpow_separation_above
    (a := (d : ℝ) * p⁻¹) (b := (d : ℝ) * q⁻¹)
    (B := V ^ q⁻¹) (C := C * 4 ^ ((d : ℝ) * p⁻¹) * V ^ p⁻¹) (M := M) hB hab
  refine ⟨T, hTM, ?_⟩
  rw [volume_ball_toReal d (4 * T) (by positivity), volume_ball_toReal d T hT]
  change C * (((4 * T) ^ d * V) ^ p⁻¹) < (T ^ d * V) ^ q⁻¹
  have hleft : C * (((4 * T) ^ d * V) ^ p⁻¹) =
      (C * 4 ^ ((d : ℝ) * p⁻¹) * V ^ p⁻¹) * T ^ ((d : ℝ) * p⁻¹) := by
    rw [Real.mul_rpow (pow_nonneg (by positivity) _) hV.le]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 4 * T)]
    rw [Real.mul_rpow (by positivity) hT.le]
    ring
  have hright : (T ^ d * V) ^ q⁻¹ = T ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹ := by
    rw [Real.mul_rpow (pow_nonneg hT.le _) hV.le]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
  rw [hleft, hright]
  exact hsep

/-- `ENNReal` version of `exists_large_ball_volume_gap_above`, in precisely
the form consumed by the `eLpNorm` estimates. -/
theorem exists_large_ball_volume_gap_above_ennreal
    {d : ℕ} (hd : 0 < d) {p q C M : ℝ}
    (hC : 0 < C) (hp : 0 < p) (hq : 0 < q) (hbad : p⁻¹ < q⁻¹) :
    ∃ T : ℝ, M < T ∧
      ENNReal.ofReal C * volume (ball (0 : Euclidean d) (4 * T)) ^ p⁻¹ <
        volume (ball (0 : Euclidean d) T) ^ q⁻¹ := by
  obtain ⟨T, hTM, hreal⟩ :=
    exists_large_ball_volume_gap_above hd hp hq hbad (C := C) (M := M)
  refine ⟨T, hTM, ?_⟩
  let X : ENNReal := ENNReal.ofReal C * volume (ball (0 : Euclidean d) (4 * T)) ^ p⁻¹
  let Y : ENNReal := volume (ball (0 : Euclidean d) T) ^ q⁻¹
  have hvol4top : volume (ball (0 : Euclidean d) (4 * T)) ≠ (⊤ : ENNReal) :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d))
      (r := 4 * T)).ne
  have hvolTtop : volume (ball (0 : Euclidean d) T) ≠ (⊤ : ENNReal) :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := T)).ne
  have hXtop : X ≠ (⊤ : ENNReal) := by
    dsimp [X]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le) hvol4top)
  have hYtop : Y ≠ (⊤ : ENNReal) := by
    dsimp [Y]
    exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hq.le) hvolTtop
  apply (ENNReal.toReal_lt_toReal hXtop hYtop).mp
  change X.toReal < Y.toReal
  dsimp [X, Y]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow]
  exact hreal

end

end Auto.Spherical.FractalDilations.SharpnessVolume
end Former_SharpnessVolume

/- ===== Former FractalDilations/ShellBump.lean ===== -/
section Former_ShellBump

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Maximal
open Auto.Spherical.FractalDilations.SharpnessTests
open Auto.Spherical.SurfaceCore







/-!
# Smooth thickened-sphere test functions

The spherical-cap obstruction uses smooth radial cutoffs supported in a thin
neighbourhood of a sphere.  Squared radius is smooth at the origin, so a
one-dimensional `ContDiffBump` composed with `x ↦ ‖x‖²` gives a Schwartz
function without making any radial-smoothness assertion about `‖x‖` itself.
-/

namespace Auto.Spherical.FractalDilations.ShellBump

open MeasureTheory Metric Set

noncomputable section

/-- A smooth cutoff which is one on a squared-radius shell of thickness
`δ`, vanishes outside thickness `2δ`, and is bounded by one. -/
theorem exists_schwartz_squared_shell_test
    {d : ℕ} {r δ : ℝ}
    (hr : 0 < r) (hrtwo : r ≤ 2) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ∃ f : SchwartzMap (Euclidean d) ℂ,
      (∀ y : Euclidean d, |‖y‖ ^ 2 - r ^ 2| ≤ δ → f y = 1) ∧
      (∀ y : Euclidean d, 2 * δ ≤ |‖y‖ ^ 2 - r ^ 2| → f y = 0) ∧
      (∀ y : Euclidean d, ‖f y‖ ≤ 1) := by
  let b : ContDiffBump (r ^ 2) := ⟨δ, 2 * δ, hδ, by linarith⟩
  let sq : Euclidean d → ℝ := fun y => inner ℝ y y
  let g : Euclidean d → ℂ := Complex.ofRealCLM ∘ b ∘ sq
  have hsq : ContDiff ℝ (⊤ : ℕ∞) sq := by
    exact contDiff_id.inner ℝ contDiff_id
  have hsq_eq (y : Euclidean d) : sq y = ‖y‖ ^ 2 := by
    dsimp only [sq]
    exact real_inner_self_eq_norm_sq y
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact Complex.ofRealCLM.contDiff.comp (b.contDiff.comp hsq)
  have hcompact : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) 3)
    intro y hy
    have hynorm : 3 < ‖y‖ := by
      rw [mem_closedBall, dist_zero_right] at hy
      exact lt_of_not_ge hy
    have hsqy : 9 < ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    have hrSq : r ^ 2 ≤ 4 := by nlinarith
    have hdiff : 2 * δ ≤ ‖y‖ ^ 2 - r ^ 2 := by nlinarith
    have hdiffnonneg : 0 ≤ ‖y‖ ^ 2 - r ^ 2 := le_trans (by positivity) hdiff
    have hdist : b.rOut ≤ dist (sq y) (r ^ 2) := by
      rw [hsq_eq y, dist_eq_norm, Real.norm_eq_abs]
      simpa only [abs_of_nonneg hdiffnonneg] using hdiff
    change (b (sq y) : ℂ) = 0
    rw [b.zero_of_le_dist hdist]
    norm_num
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_, ?_⟩
  · intro y hy
    have hdist : dist (sq y) (r ^ 2) ≤ b.rIn := by
      rw [hsq_eq y, dist_eq_norm, Real.norm_eq_abs]
      exact hy
    change (b (sq y) : ℂ) = 1
    rw [b.one_of_mem_closedBall hdist]
    norm_num
  · intro y hy
    have hdist : b.rOut ≤ dist (sq y) (r ^ 2) := by
      rw [hsq_eq y, dist_eq_norm, Real.norm_eq_abs]
      exact hy
    change (b (sq y) : ℂ) = 0
    rw [b.zero_of_le_dist hdist]
    norm_num
  · intro y
    change ‖(b (sq y) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (ContDiffBump.nonneg' b _)]
    exact ContDiffBump.le_one b

/-- A point in the ball of radius `δ / 8` sees the radius-`r` sampling sphere
inside the squared-radius shell of thickness `δ`. -/
theorem abs_norm_sq_sub_sq_le_of_norm_le_eighth
    {d : ℕ} {r δ : ℝ} (hr : 0 ≤ r) (hrtwo : r ≤ 2)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (x : Euclidean d) (hx : ‖x‖ ≤ δ / 8)
    (ω : sphere (0 : Euclidean d) 1) :
    |‖x + r • (ω : Euclidean d)‖ ^ 2 - r ^ 2| ≤ δ := by
  have hω : ‖(ω : Euclidean d)‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using ω.property
  have hrω : ‖r • (ω : Euclidean d)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hω, mul_one]
  have hdiff : |‖x + r • (ω : Euclidean d)‖ - r| ≤ ‖x‖ := by
    calc
      |‖x + r • (ω : Euclidean d)‖ - r| =
          |‖x + r • (ω : Euclidean d)‖ - ‖r • (ω : Euclidean d)‖| := by rw [hrω]
      _ ≤ ‖(x + r • (ω : Euclidean d)) - r • (ω : Euclidean d)‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖x‖ := by congr 1 <;> abel
  have hdiff' : |‖x + r • (ω : Euclidean d)‖ - r| ≤ δ / 8 :=
    hdiff.trans hx
  have hsum : ‖x + r • (ω : Euclidean d)‖ + r ≤ 8 := by
    calc
      ‖x + r • (ω : Euclidean d)‖ + r ≤ ‖x‖ + ‖r • (ω : Euclidean d)‖ + r := by
        gcongr
        exact norm_add_le _ _
      _ = ‖x‖ + r + r := by rw [hrω]
      _ ≤ δ / 8 + 2 + 2 := by linarith
      _ ≤ 8 := by linarith
  have hsumabs : |‖x + r • (ω : Euclidean d)‖ + r| ≤ 8 := by
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) hr)]
    exact hsum
  calc
    |‖x + r • (ω : Euclidean d)‖ ^ 2 - r ^ 2| =
        |(‖x + r • (ω : Euclidean d)‖ - r) *
          (‖x + r • (ω : Euclidean d)‖ + r)| := by ring
    _ = |‖x + r • (ω : Euclidean d)‖ - r| *
          |‖x + r • (ω : Euclidean d)‖ + r| := abs_mul _ _
    _ ≤ (δ / 8) * 8 :=
      mul_le_mul hdiff' hsumabs (abs_nonneg _) (by positivity)
    _ = δ := by ring

/-- A squared-radius shell test has maximal function at least one on the
small ball `B(0, δ / 8)`. -/
theorem one_le_fractalSphericalMaximalReal_of_squared_shell
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {r δ : ℝ} (hrE : r ∈ E)
    (hrnonneg : 0 ≤ r) (hrtwo : r ≤ 2) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hf : ∀ y : Euclidean d, |‖y‖ ^ 2 - r ^ 2| ≤ δ → f y = 1)
    (x : Euclidean d) (hx : ‖x‖ ≤ δ / 8) :
    1 ≤ fractalSphericalMaximalReal d E f x := by
  unfold fractalSphericalMaximalReal
  apply (ENNReal.toReal_le_toReal ENNReal.one_ne_top
    (fractalSphericalMaximal_ne_top hd E hE f x)).mpr
  calc
    (1 : ENNReal) = ENNReal.ofReal ‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r x‖ := by
      rw [normalizedSphericalAverage_eq_of_eq_on_sphere hd (f : Euclidean d → ℂ) 1 r x]
      · norm_num
      · intro ω
        exact hf _ (abs_norm_sq_sub_sq_le_of_norm_le_eighth hrnonneg hrtwo hδ hδone x hx ω)
    _ ≤ fractalSphericalMaximal d E (f : Euclidean d → ℂ) x :=
      normalizedSphericalAverage_le_fractalSphericalMaximal E (f : Euclidean d → ℂ) hrE x

/-- The preceding pointwise shell test yields its explicit `L^q` lower bound. -/
theorem volume_ball_rpow_le_eLpNorm_fractalSphericalMaximalReal_of_squared_shell
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {r δ q : ℝ} (hrE : r ∈ E)
    (hrnonneg : 0 ≤ r) (hrtwo : r ≤ 2) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hf : ∀ y : Euclidean d, |‖y‖ ^ 2 - r ^ 2| ≤ δ → f y = 1)
    (hq : 0 < q) :
    volume (ball (0 : Euclidean d) (δ / 8)) ^ q⁻¹ ≤
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume := by
  rw [← eLpNorm_ball_indicator_one (δ / 8) q hq]
  apply eLpNorm_mono
  intro x
  by_cases hx : x ∈ ball (0 : Euclidean d) (δ / 8)
  · rw [Set.indicator_of_mem hx, norm_one]
    have hxnorm : ‖x‖ < δ / 8 := by
      simpa only [mem_ball, dist_zero_right] using hx
    change 1 ≤ ‖fractalSphericalMaximalReal d E f x‖
    have hnonneg : 0 ≤ fractalSphericalMaximalReal d E f x := by
      unfold fractalSphericalMaximalReal
      exact ENNReal.toReal_nonneg
    rw [Real.norm_of_nonneg hnonneg]
    exact one_le_fractalSphericalMaximalReal_of_squared_shell
      hd E hE f hrE hrnonneg hrtwo hδ hδone hf x hxnorm.le
  · rw [Set.indicator_of_notMem hx]
    simp

end

end Auto.Spherical.FractalDilations.ShellBump
end Former_ShellBump

/- ===== Former FractalDilations/AnnulusPositivity.lean ===== -/
section Former_AnnulusPositivity

/- This file was machine-generated by Codex -/

open Auto.Spherical.FourierRadius
open Auto.Spherical.FractalDilations.AnnulusCore
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.SurfaceCore







/-!
# Positivity of normalized spherical averages

The annulus test uses nonnegative real bumps.  Their complexified normalized
spherical averages are real and nonnegative, so the exact Fubini mass identity
can be converted into a positive lower bound without losing cancellations.
-/

namespace Auto.Spherical.FractalDilations.AnnulusPositivity

open MeasureTheory Metric Set

noncomputable section

/-- The real part of a normalized spherical average of a nonnegative real
input has exactly the original total mass. -/
theorem integral_re_normalizedSphericalAverage_eq_integral
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℝ)
    (hfcont : Continuous f) (hf : Integrable f volume) (r : ℝ) :
    (∫ x : Euclidean d,
      (normalizedSphericalAverage d (fun y => (f y : ℂ)) r x).re) =
      ∫ x : Euclidean d, f x := by
  have hfcontC : Continuous (fun y => (f y : ℂ)) :=
    Complex.continuous_ofReal.comp hfcont
  have hfC : Integrable (fun y => (f y : ℂ)) volume := hf.ofReal
  have havg : Integrable
      (normalizedSphericalAverage d (fun y => (f y : ℂ)) r) volume := by
    unfold normalizedSphericalAverage
    exact (integrable_sphericalAverage (fun y => (f y : ℂ)) hfcontC hfC r).const_mul _
  calc
    (∫ x : Euclidean d,
      (normalizedSphericalAverage d (fun y => (f y : ℂ)) r x).re) =
        (∫ x : Euclidean d,
          normalizedSphericalAverage d (fun y => (f y : ℂ)) r x).re :=
      integral_re havg
    _ = (∫ x : Euclidean d, (f x : ℂ)).re := by
      rw [integral_normalizedSphericalAverage_eq_integral hd
        (fun y => (f y : ℂ)) hfcontC hfC r]
    _ = ∫ x : Euclidean d, f x := by
      rw [integral_complex_ofReal]
      rfl

end

end Auto.Spherical.FractalDilations.AnnulusPositivity
end Former_AnnulusPositivity

/- ===== Former FractalDilations/AnnulusSupport.lean ===== -/
section Former_AnnulusSupport

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.SharpnessTests
open Auto.Spherical.SurfaceCore







/-!
# Annular support of a spherical average

A compactly supported ball bump has every fixed spherical average supported
in the corresponding radial annulus.  This elementary geometric fact is kept
separate from the mass and covering arguments in the annulus sharpness test.
-/

namespace Auto.Spherical.FractalDilations.AnnulusSupport

open MeasureTheory Metric Set

noncomputable section

/-- If the sampling sphere stays outside the support ball, its normalized
spherical average vanishes. -/
theorem normalizedSphericalAverage_eq_zero_of_radial_separation
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) {R r : ℝ}
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (x : Euclidean d) (hseparation : 2 * R ≤ abs (‖x‖ - abs r)) :
    normalizedSphericalAverage d f r x = 0 := by
  apply normalizedSphericalAverage_eq_of_eq_on_sphere hd f 0 r x
  intro ω
  apply hzero
  apply hseparation.trans
  apply abs_le.mpr
  constructor
  · have hradius : ‖r • (ω : Euclidean d)‖ = |r| := by
      rw [norm_smul, Real.norm_eq_abs]
      have hω : ‖(ω : Euclidean d)‖ = 1 := by
        simpa only [mem_sphere_zero_iff_norm] using ω.property
      rw [hω, mul_one]
    have htriangle : ‖r • (ω : Euclidean d)‖ ≤
        ‖x + r • (ω : Euclidean d)‖ + ‖x‖ := by
      calc
        ‖r • (ω : Euclidean d)‖ = ‖(x + r • (ω : Euclidean d)) - x‖ := by
          congr 1
          abel
        _ ≤ ‖x + r • (ω : Euclidean d)‖ + ‖x‖ := norm_sub_le _ _
    linarith [show |r| ≤ ‖x + r • (ω : Euclidean d)‖ + ‖x‖ by simpa [hradius] using htriangle]
  · have hradius : ‖r • (ω : Euclidean d)‖ = |r| := by
      rw [norm_smul, Real.norm_eq_abs]
      have hω : ‖(ω : Euclidean d)‖ = 1 := by
        simpa only [mem_sphere_zero_iff_norm] using ω.property
      rw [hω, mul_one]
    have htriangle : ‖x‖ ≤ ‖x + r • (ω : Euclidean d)‖ +
        ‖r • (ω : Euclidean d)‖ := by
      calc
        ‖x‖ = ‖(x + r • (ω : Euclidean d)) - r • (ω : Euclidean d)‖ := by
          congr 1
          abel
        _ ≤ ‖x + r • (ω : Euclidean d)‖ + ‖r • (ω : Euclidean d)‖ := norm_sub_le _ _
    linarith [show ‖x‖ ≤ ‖x + r • (ω : Euclidean d)‖ + |r| by simpa [hradius] using htriangle]

end

end Auto.Spherical.FractalDilations.AnnulusSupport
end Former_AnnulusSupport

/- ===== Former FractalDilations/ClusterBump.lean ===== -/
section Former_ClusterBump

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ClusterGeometry
open Auto.Spherical.SurfaceCore







/-!
# Smooth anisotropic test data for clustered radii

This module begins the smooth realization of the transverse-ball/radial-slab
sets from `ClusterGeometry`.
-/

namespace Auto.Spherical.FractalDilations.ClusterBump

open MeasureTheory Metric Set

noncomputable section

theorem contDiff_euclideanSuccCoordinates (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanSuccCoordinates n) := by
  unfold euclideanSuccCoordinates
  apply ContDiff.prodMk
  · change ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Euclidean (n + 1) =>
        WithLp.toLp 2 (fun i => x (Fin.castAdd 1 i)))
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi'
    intro i
    exact contDiff_piLp_apply (p := (2 : ENNReal))
  · exact contDiff_piLp_apply (p := (2 : ENNReal))

/-- A smooth Cartesian cutoff for the thin transverse-ball/radial-slab used
in the clustered-radii construction.  It is one on the inner slab, vanishes
off the doubled slab, and has pointwise norm at most one. -/
theorem exists_schwartz_horizontalSlab_test
    {n : ℕ} {ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 < h) :
    ∃ f : SchwartzMap (Euclidean (n + 1)) ℂ,
      (∀ x : Euclidean (n + 1), x ∈ horizontalSlab n ρ (-h) h → f x = 1) ∧
      (∀ x : Euclidean (n + 1),
        x ∉ horizontalSlab n (2 * ρ) (-(2 * h)) (2 * h) → f x = 0) ∧
      (∀ x : Euclidean (n + 1), 0 ≤ (f x).re) ∧
      (∀ x : Euclidean (n + 1), (f x).im = 0) ∧
      (∀ x : Euclidean (n + 1), ‖f x‖ ≤ 1) := by
  let hor : Euclidean (n + 1) → Euclidean n := fun x =>
    MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i => x (Fin.castAdd 1 i))
  let ver : Euclidean (n + 1) → ℝ := fun x => x (Fin.last n)
  let bhor : ContDiffBump (0 : Euclidean n) := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  let bver : ContDiffBump (0 : ℝ) := ⟨h, 2 * h, hh, by linarith⟩
  let g : Euclidean (n + 1) → ℂ := fun x =>
    Complex.ofReal (bhor (hor x) * bver (ver x))
  have hhor : ContDiff ℝ (⊤ : ℕ∞) hor := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Euclidean (n + 1) =>
        WithLp.toLp 2 (fun i => x (Fin.castAdd 1 i)))
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi'
    intro i
    exact contDiff_piLp_apply (p := (2 : ENNReal))
  have hver : ContDiff ℝ (⊤ : ℕ∞) ver := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclidean (n + 1) => x (Fin.last n))
    exact contDiff_piLp_apply (p := (2 : ENNReal))
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact Complex.ofRealCLM.contDiff.comp
      ((bhor.contDiff.comp hhor).mul (bver.contDiff.comp hver))
  have hcompact : HasCompactSupport g := by
    apply HasCompactSupport.intro
      (isCompact_closedBall (0 : Euclidean (n + 1)) (2 * (ρ + h)))
    intro x hx
    have hxnorm : 2 * (ρ + h) < ‖x‖ := by
      rw [mem_closedBall, dist_zero_right] at hx
      exact lt_of_not_ge hx
    by_cases hhorzero : bhor (hor x) = 0
    · simp [g, hhorzero]
    by_cases hverzero : bver (ver x) = 0
    · simp [g, hverzero]
    have hhorlt : ‖hor x‖ < 2 * ρ := by
      by_contra hnot
      apply hhorzero
      apply bhor.zero_of_le_dist
      rw [dist_zero_right]
      exact le_of_not_gt hnot
    have hverabs : |ver x| < 2 * h := by
      by_contra hnot
      apply hverzero
      apply bver.zero_of_le_dist
      rw [dist_eq_norm, Real.norm_eq_abs]
      simpa [bver] using (le_of_not_gt hnot)
    have hnormsq : ‖x‖ ^ 2 = ‖hor x‖ ^ 2 + (ver x) ^ 2 := by
      simpa only [hor, ver] using
        Auto.Spherical.SurfaceCore.norm_sq_euclideanSucc_coordinates n x
    have hhorsq : ‖hor x‖ ^ 2 < (2 * ρ) ^ 2 := by
      nlinarith [norm_nonneg (hor x)]
    have hversq : (ver x) ^ 2 < (2 * h) ^ 2 := by
      rw [← sq_abs (ver x)]
      nlinarith [abs_nonneg (ver x)]
    exfalso
    nlinarith [norm_nonneg x]
  have hschwartz_apply (x : Euclidean (n + 1)) :
      (hcompact.toSchwartzMap hsmooth) x = g x := rfl
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hschwartz_apply]
    simp only [g, Complex.ofReal_mul]
    change (hor x, ver x) ∈ ball (0 : Euclidean n) ρ ×ˢ Ioo (-h) h at hx
    have hhorball : dist (hor x) (0 : Euclidean n) ≤ ρ := by
      rw [dist_zero_right]
      have hlt : ‖hor x‖ < ρ := by
        simpa only [mem_ball, dist_zero_right] using hx.1
      exact hlt.le
    have hverball : dist (ver x) (0 : ℝ) ≤ h := by
      rw [dist_eq_norm, Real.norm_eq_abs]
      exact (abs_le.2 ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩)
    rw [bhor.one_of_mem_closedBall hhorball, bver.one_of_mem_closedBall hverball]
    norm_num
  · intro x hx
    rw [hschwartz_apply]
    simp only [g, Complex.ofReal_mul]
    by_contra hne
    have hprod : bhor (hor x) * bver (ver x) ≠ 0 := by
      exact_mod_cast hne
    have hhorzero : bhor (hor x) ≠ 0 := fun hzero => hprod (by simp [hzero])
    have hverzero : bver (ver x) ≠ 0 := fun hzero => hprod (by simp [hzero])
    have hhorlt : ‖hor x‖ < 2 * ρ := by
      by_contra hnot
      exact hhorzero (bhor.zero_of_le_dist (by
        rw [dist_zero_right]
        exact le_of_not_gt hnot))
    have hverabs : |ver x| < 2 * h := by
      by_contra hnot
      exact hverzero (bver.zero_of_le_dist (by
        rw [dist_eq_norm, Real.norm_eq_abs]
        simpa [bver] using (le_of_not_gt hnot)))
    apply hx
    change (hor x, ver x) ∈ ball (0 : Euclidean n) (2 * ρ) ×ˢ
      Ioo (-(2 * h)) (2 * h)
    constructor
    · simpa only [mem_ball, dist_zero_right] using hhorlt
    · exact abs_lt.mp hverabs
  · intro x
    rw [hschwartz_apply]
    simp only [g, Complex.ofReal_re]
    exact mul_nonneg (bhor.nonneg' (hor x)) (bver.nonneg' (ver x))
  · intro x
    rw [hschwartz_apply]
    simp only [g, Complex.ofReal_im]
  · intro x
    rw [hschwartz_apply]
    simp only [g, Complex.ofReal_mul]
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (bhor.nonneg' (hor x)),
      Real.norm_of_nonneg (bver.nonneg' (ver x))]
    exact mul_le_one₀ (bhor.le_one) (bver.nonneg' (ver x)) (bver.le_one)

/-- A bounded Schwartz function supported in the doubled horizontal slab has
the expected `Lᵖ` envelope.  This packages the input-side estimate for the
clustered-radius test independently of the later spherical geometry. -/
theorem eLpNorm_schwartz_horizontalSlab_le
    {n : ℕ} {ρ h p : ℝ} (hp : 0 < p)
    (f : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hzero : ∀ x : Euclidean (n + 1),
      x ∉ horizontalSlab n (2 * ρ) (-(2 * h)) (2 * h) → f x = 0)
    (hbound : ∀ x : Euclidean (n + 1), ‖f x‖ ≤ 1) :
    eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
      volume (horizontalSlab n (2 * ρ) (-(2 * h)) (2 * h)) ^ p⁻¹ := by
  let A : Set (Euclidean (n + 1)) :=
    horizontalSlab n (2 * ρ) (-(2 * h)) (2 * h)
  have hAmeas : MeasurableSet A :=
    measurableSet_horizontalSlab n (2 * ρ) (-(2 * h)) (2 * h)
  change eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
    volume A ^ p⁻¹
  calc
    eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
        eLpNorm (A.indicator fun _ : Euclidean (n + 1) => (1 : ℂ))
          (ENNReal.ofReal p) volume := by
      apply eLpNorm_mono
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, norm_one]
        exact hbound x
      · rw [Set.indicator_of_notMem hx]
        rw [hzero x hx]
    _ = volume A ^ p⁻¹ := by
      rw [eLpNorm_indicator_const hAmeas
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
      simp only [enorm_one, one_mul, ENNReal.toReal_ofReal hp.le, one_div]

/-- The preceding envelope written with the exact Cartesian-slab volume. -/
theorem eLpNorm_schwartz_horizontalSlab_le_explicit
    {n : ℕ} {ρ h p : ℝ} (hp : 0 < p)
    (f : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hzero : ∀ x : Euclidean (n + 1),
      x ∉ horizontalSlab n (2 * ρ) (-(2 * h)) (2 * h) → f x = 0)
    (hbound : ∀ x : Euclidean (n + 1), ‖f x‖ ≤ 1) :
    eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
      (volume (ball (0 : Euclidean n) (2 * ρ)) * ENNReal.ofReal (4 * h)) ^ p⁻¹ := by
  refine (eLpNorm_schwartz_horizontalSlab_le hp f hzero hbound).trans ?_
  have hwidth : (2 * h) - -(2 * h) = 4 * h := by ring
  rw [volume_horizontalSlab, hwidth]

end

end Auto.Spherical.FractalDilations.ClusterBump
end Former_ClusterBump

/- ===== Former FractalDilations/ClusterOutputGeometry.lean ===== -/
section Former_ClusterOutputGeometry

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ClusterGeometry
open Auto.Spherical.FractalDilations.SeparatedPacking
open Auto.Spherical.SurfaceCore







/-!
# Output regions for clustered-radius tests

The clustered construction uses one thin horizontal slab for every selected
radius.  This file isolates their disjointness and exact total volume.
-/

namespace Auto.Spherical.FractalDilations.ClusterOutputGeometry

open MeasureTheory Metric Set

noncomputable section

/-- The union of anisotropic output slabs associated to a finite cluster of
radii. -/
def clusterOutputRegion (n : ℕ) (r δ σ : ℝ) (s : Finset ℝ) :
    Set (Euclidean (n + 1)) :=
  ⋃ t ∈ s, centeredHorizontalSlab n (δ / (128 * σ)) (δ / 128) (r - t)

/-- Separation at the packing mesh makes the translated output slabs
pairwise disjoint. -/
theorem strictlySeparated_pairwiseDisjoint_clusterOutputSlabs
    {n : ℕ} {r δ σ : ℝ} {s : Finset ℝ}
    (hδ : 0 ≤ δ) (hsep : StrictlySeparated s (δ / 2)) :
    (↑s : Set ℝ).PairwiseDisjoint
      (fun t => centeredHorizontalSlab n (δ / (128 * σ)) (δ / 128) (r - t)) := by
  intro u hu v hv huv
  apply disjoint_centeredHorizontalSlab_of_two_mul_le_abs_sub
  have hstrict : δ / 2 < |u - v| := hsep hu hv huv
  have hsmall : δ / 64 ≤ δ / 2 := by linarith
  calc
    2 * (δ / 128) = δ / 64 := by ring
    _ ≤ |u - v| := hsmall.trans hstrict.le
    _ = |(r - u) - (r - v)| := by
      rw [show (r - u) - (r - v) = -(u - v) by ring, abs_neg]

/-- The finite output union has its expected cardinality-times-slab volume. -/
theorem volume_clusterOutputRegion
    {n : ℕ} {r δ σ : ℝ} {s : Finset ℝ}
    (hδ : 0 ≤ δ) (hsep : StrictlySeparated s (δ / 2)) :
    volume (clusterOutputRegion n r δ σ s) =
      (s.card : ENNReal) *
        (volume (ball (0 : Euclidean n) (δ / (128 * σ))) *
          ENNReal.ofReal (2 * (δ / 128))) := by
  unfold clusterOutputRegion
  rw [measure_biUnion_finset
    (strictlySeparated_pairwiseDisjoint_clusterOutputSlabs hδ hsep)
    (fun t _ => measurableSet_centeredHorizontalSlab n
      (δ / (128 * σ)) (δ / 128) (r - t))]
  simp only [volume_centeredHorizontalSlab]
  simp

/-- A member of the radius cluster identifies the corresponding output slab. -/
theorem mem_clusterOutputRegion_of_mem_centeredHorizontalSlab
    {n : ℕ} {r δ σ t : ℝ} {s : Finset ℝ}
    (ht : t ∈ s) (x : Euclidean (n + 1))
    (hx : x ∈ centeredHorizontalSlab n (δ / (128 * σ)) (δ / 128) (r - t)) :
    x ∈ clusterOutputRegion n r δ σ s :=
  mem_biUnion ht hx

/-- Coordinate inequalities extracted from one of the output slabs. -/
theorem norm_and_abs_sub_center_le_of_mem_centeredHorizontalSlab
    {n : ℕ} {rho h center : ℝ} {x : Euclidean (n + 1)}
    (hx : x ∈ centeredHorizontalSlab n rho h center) :
    ‖(euclideanSuccCoordinates n x).1‖ ≤ rho ∧
      |(euclideanSuccCoordinates n x).2 - center| ≤ h := by
  change (euclideanSuccCoordinates n x).1 ∈ ball (0 : Euclidean n) rho ∧
    (euclideanSuccCoordinates n x).2 ∈ Ioo (center - h) (center + h) at hx
  constructor
  · rw [mem_ball, dist_zero_right] at hx
    exact hx.1.le
  · rw [mem_Ioo] at hx
    exact abs_le.2 ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩

end

end Auto.Spherical.FractalDilations.ClusterOutputGeometry
end Former_ClusterOutputGeometry

/- ===== Former FractalDilations/ShellVolume.lean ===== -/
section Former_ShellVolume

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.SurfaceCore







/-!
# Volume bounds for thin spherical shells

This module records the elementary `O(δ)` volume bound for a shell around a
radius in `[1,2]`.  It is the input-side estimate in the spherical-cap
sharpness example.
-/

namespace Auto.Spherical.FractalDilations.ShellVolume

open MeasureTheory Metric Set ENNReal Filter Topology

noncomputable section

/-- The difference of the `d`th powers of two radii separated by `4δ` is
bounded linearly in `δ` when both radii remain in a fixed compact interval. -/
theorem shell_power_difference_le_linear
    (d : ℕ) {r δ : ℝ}
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2)
    (hδ : 0 ≤ δ) (hδquarter : δ ≤ 1 / 4) :
    (r + 2 * δ) ^ d - (r - 2 * δ) ^ d ≤
      (4 * (d : ℝ) * 3 ^ (d - 1)) * δ := by
  have ha0 : 0 ≤ r + 2 * δ := by linarith
  have hb0 : 0 ≤ r - 2 * δ := by linarith
  have hab : r - 2 * δ ≤ r + 2 * δ := by linarith
  have ha3 : r + 2 * δ ≤ 3 := by linarith
  have hb3 : r - 2 * δ ≤ 3 := by linarith
  have hpow : (r - 2 * δ) ^ d ≤ (r + 2 * δ) ^ d :=
    pow_le_pow_left₀ hb0 hab d
  have hmax : max |r + 2 * δ| |r - 2 * δ| ≤ 3 := by
    apply max_le
    · simpa only [abs_of_nonneg ha0] using ha3
    · simpa only [abs_of_nonneg hb0] using hb3
  have hmaxnonneg : 0 ≤ max |r + 2 * δ| |r - 2 * δ| :=
    (abs_nonneg _).trans (le_max_left _ _)
  have hmaxpow : max |r + 2 * δ| |r - 2 * δ| ^ (d - 1) ≤ 3 ^ (d - 1) :=
    pow_le_pow_left₀ hmaxnonneg hmax _
  calc
    (r + 2 * δ) ^ d - (r - 2 * δ) ^ d =
        |(r + 2 * δ) ^ d - (r - 2 * δ) ^ d| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hpow)]
    _ ≤ |(r + 2 * δ) - (r - 2 * δ)| * (d : ℝ) *
          max |r + 2 * δ| |r - 2 * δ| ^ (d - 1) :=
      abs_pow_sub_pow_le (r + 2 * δ) (r - 2 * δ) d
    _ ≤ (4 * δ) * (d : ℝ) * 3 ^ (d - 1) := by
      have hsep : |(r + 2 * δ) - (r - 2 * δ)| = 4 * δ := by
        rw [abs_of_nonneg (by linarith)]
        ring
      rw [hsep]
      gcongr
    _ = (4 * (d : ℝ) * 3 ^ (d - 1)) * δ := by ring

/-- The volume of the annulus containing a squared-radius shell is at most a
fixed multiple of its thickness.  The constant is deliberately coarse: its
only role in the cap test is that it is independent of `δ`. -/
theorem volume_thin_annulus_le
    (d : ℕ) {r δ : ℝ}
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2)
    (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4) :
    volume (ball (0 : Euclidean d) (r + 2 * δ) \ closedBall (0 : Euclidean d) (r - 2 * δ)) ≤
      ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
        volume (ball (0 : Euclidean d) 1) := by
  have ha : 0 < r + 2 * δ := by linarith
  have hb : 0 < r - 2 * δ := by linarith
  have hab : r - 2 * δ < r + 2 * δ := by linarith
  have hsubset : closedBall (0 : Euclidean d) (r - 2 * δ) ⊆
      ball (0 : Euclidean d) (r + 2 * δ) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_ball, dist_zero_right]
    exact hx.trans_lt hab
  have hunit_top : volume (ball (0 : Euclidean d) 1) ≠ (⊤ : ENNReal) :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := (1 : ℝ))).ne
  have hclosed_top : volume (closedBall (0 : Euclidean d) (r - 2 * δ)) ≠ (⊤ : ENNReal) := by
    rw [Measure.addHaar_closedBall volume (0 : Euclidean d) hb.le]
    simp only [finrank_euclideanSpace_fin]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunit_top
  have hdiff := shell_power_difference_le_linear d hrone hrtwo hδ.le hδquarter
  rw [measure_sdiff hsubset measurableSet_closedBall.nullMeasurableSet hclosed_top,
    Measure.addHaar_ball_of_pos volume (0 : Euclidean d) ha,
    Measure.addHaar_closedBall volume (0 : Euclidean d) hb.le]
  simp only [finrank_euclideanSpace_fin]
  rw [← ENNReal.sub_mul (fun _ _ => hunit_top)]
  rw [← ENNReal.ofReal_sub ((r + 2 * δ) ^ d) (pow_nonneg hb.le _)]
  gcongr

/-- If `a < b`, then at sufficiently small positive scales the power
`δ ^ b` is dominated by `δ ^ a`, with arbitrary fixed coefficients. -/
theorem exists_small_rpow_separation
    {a b A B C : ℝ} (hB : 0 < B) (hab : a < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ C * A * δ ^ b < B * δ ^ a := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have htend : Tendsto (fun δ : ℝ => δ ^ (b - a)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (b - a) (Or.inr hba.le)).tendsto
    rw [Real.zero_rpow hba.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hmulTend : Tendsto (fun δ : ℝ => C * A * δ ^ (b - a)) (𝓝[>] 0) (𝓝 0) := by
    convert tendsto_const_nhds.mul htend using 1 <;> simp
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, C * A * δ ^ (b - a) < B := by
    exact hmulTend.eventually (Iio_mem_nhds hB)
  have hscale : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Ioo (0 : ℝ) (1 / 4) :=
    Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨δ, hδsmall, hδscale⟩ := (hsmall.and hscale).exists
  refine ⟨δ, hδscale.1, hδscale.2, ?_⟩
  have hδpow : 0 < δ ^ a := Real.rpow_pos_of_pos hδscale.1 _
  have hmul : (C * A * δ ^ (b - a)) * δ ^ a < B * δ ^ a :=
    mul_lt_mul_of_pos_right hδsmall hδpow
  calc
    C * A * δ ^ b = C * A * (δ ^ (b - a) * δ ^ a) := by
      rw [← Real.rpow_add hδscale.1]
      congr 2
      ring
    _ = (C * A * δ ^ (b - a)) * δ ^ a := by ring
    _ < B * δ ^ a := hmul

end

end Auto.Spherical.FractalDilations.ShellVolume
end Former_ShellVolume

/- ===== Former FractalDilations/TranslationSharpness.lean ===== -/
section Former_TranslationSharpness

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.Definitions
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Maximal
open Auto.Spherical.FractalDilations.SharpnessNormalization
open Auto.Spherical.FractalDilations.SharpnessTests
open Auto.Spherical.FractalDilations.SharpnessVolume
open Auto.Spherical.SurfaceCore







/-!
# The large-ball translation obstruction

For `p > q`, a smooth function which is one on a large ball has output of
order `R^(d/q)` and input of order `R^(d/p)`.  This is the usual translation
obstruction, expressed directly with a single large smooth ball instead of a
finite sum of distant translates.
-/

namespace Auto.Spherical.FractalDilations.TranslationSharpness

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The translation/large-ball test rules out the strict region `p > q`.
The positivity assumptions are exactly those needed for the real-valued
maximal operator to be finite. -/
theorem fractalSphericalUnbounded_of_translation_large_balls
    {d : ℕ} {E : Set ℝ} {p q : ℝ}
    (hd : 0 < d) (hEpos : E ⊆ Ioi (0 : ℝ)) (hEne : E.Nonempty)
    (hp : 0 < p) (hq : 0 < q) (hbad : p⁻¹ < q⁻¹) :
    FractalSphericalUnbounded d E p q := by
  apply fractalSphericalUnbounded_of_large_ratio
  intro C hC
  obtain ⟨r, hr⟩ := hEne
  obtain ⟨T, hTabs, hgap⟩ := exists_large_ball_volume_gap_above_ennreal
    hd hC hp hq hbad (C := C) (M := |r|)
  have hT : 0 < T := lt_of_le_of_lt (abs_nonneg r) hTabs
  obtain ⟨f, hf_one, hf_zero, hf_bound⟩ :=
    exists_schwartz_ball_test_bounded d (R := 2 * T) (by positivity)
  let A : ENNReal := volume (ball (0 : Euclidean d) (4 * T)) ^ p⁻¹
  refine ⟨f, A, ?_, ?_, ?_, ?_⟩
  · dsimp [A]
    exact (ENNReal.rpow_pos
      (Metric.measure_ball_pos volume (0 : Euclidean d) (by positivity))
      (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d))
        (r := 4 * T)).ne).ne'
  · dsimp [A]
    exact ENNReal.rpow_ne_top_of_ne_zero
      (Metric.measure_ball_pos volume (0 : Euclidean d) (by positivity)).ne'
      (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d))
        (r := 4 * T)).ne
  · dsimp [A]
    convert eLpNorm_schwartz_ball_test_le_volume_ball hp f hf_zero hf_bound using 1 <;> ring
  · have hinside : T + |r| ≤ 2 * T := by linarith
    calc
      ENNReal.ofReal C * A < volume (ball (0 : Euclidean d) T) ^ q⁻¹ := by
        simpa only [A] using hgap
      _ ≤ eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume :=
        volume_ball_rpow_le_eLpNorm_fractalSphericalMaximalReal
          hd E hEpos f hr hf_one hinside hq

end

end Auto.Spherical.FractalDilations.TranslationSharpness
end Former_TranslationSharpness

/- ===== Former FractalDilations/AnnulusGeometry.lean ===== -/
section Former_AnnulusGeometry

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.AnnulusSupport
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.SeparatedPacking
open Auto.Spherical.FractalDilations.ShellVolume
open Auto.Spherical.SurfaceCore







/-!
# Geometry of the annuli in the small-ball test

This file supplies the elementary disjointness and volume estimates used when
a separated finite family of radii is tested against one small ball.  The
support statement is deliberately expressed using ordinary radial annuli,
which makes the packing and measure arguments independent of the particular
smooth cutoff chosen later.
-/

namespace Auto.Spherical.FractalDilations.AnnulusGeometry

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The open radial annulus of centre radius `r` and half-width `R`. -/
def radialAnnulus (d : ℕ) (r R : ℝ) : Set (Euclidean d) :=
  {x | |‖x‖ - r| < R}

/-- A ball-supported spherical average is supported in its corresponding
radial annulus. -/
theorem support_normalizedSphericalAverage_subset_radialAnnulus
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) {R r : ℝ}
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0) :
    Function.support (fun x : Euclidean d => normalizedSphericalAverage d f r x) ⊆
      radialAnnulus d (abs r) (2 * R) := by
  intro x hx
  change normalizedSphericalAverage d f r x ≠ 0 at hx
  change abs (‖x‖ - abs r) < 2 * R
  by_contra hnot
  exact hx (normalizedSphericalAverage_eq_zero_of_radial_separation
    hd f hzero x (le_of_not_gt hnot))

/-- Radial annuli whose centre radii are separated by at least twice their
half-width are disjoint. -/
theorem disjoint_radialAnnulus_of_two_mul_le_abs_sub
    {d : ℕ} {r s R : ℝ} (hsep : 2 * R ≤ |r - s|) :
    Disjoint (radialAnnulus d r R) (radialAnnulus d s R) := by
  rw [Set.disjoint_left]
  intro x hx hs
  change |‖x‖ - r| < R at hx
  change |‖x‖ - s| < R at hs
  have hxr : |r - ‖x‖| < R := by simpa [abs_sub_comm] using hx
  have hbound : |r - s| ≤ |r - ‖x‖| + |‖x‖ - s| := by
    calc
      |r - s| = |(r - ‖x‖) + (‖x‖ - s)| := by congr 1 <;> ring
      _ ≤ |r - ‖x‖| + |‖x‖ - s| := abs_add_le _ _
  have hlt : |r - s| < 2 * R := by linarith
  exact (not_lt_of_ge hsep) hlt

/-- A strictly `δ`-separated finite family gives pairwise disjoint radial
annuli of half-width `δ / 2`. -/
theorem strictlySeparated_pairwiseDisjoint_radialAnnuli
    {d : ℕ} {s : Finset ℝ} {δ : ℝ} (hsep : StrictlySeparated s δ) :
    (↑s : Set ℝ).PairwiseDisjoint (fun r => radialAnnulus d r (δ / 2)) := by
  intro r hr s hs hrs
  apply disjoint_radialAnnulus_of_two_mul_le_abs_sub
  have hstrict : δ < |r - s| := hsep hr hs hrs
  linarith

/-- The radial annulus at a radius in `[1,2]` has volume bounded linearly in
its half-width.  This is the ordinary-radius form of `volume_thin_annulus_le`.
-/
theorem volume_radialAnnulus_le
    (d : ℕ) {r R : ℝ}
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2) (hR : 0 < R) (hRhalf : R ≤ 1 / 2) :
    volume (radialAnnulus d r R) ≤
      ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * R) *
        volume (ball (0 : Euclidean d) 1) := by
  have hsubset : radialAnnulus d r R ⊆
      ball (0 : Euclidean d) (r + R) \ closedBall (0 : Euclidean d) (r - R) := by
    intro x hx
    change |‖x‖ - r| < R at hx
    rw [abs_lt] at hx
    constructor
    · rw [mem_ball, dist_zero_right]
      linarith [hx.2]
    · rw [mem_closedBall, dist_zero_right]
      exact not_le.mpr (by linarith [hx.1])
  calc
    volume (radialAnnulus d r R) ≤
        volume (ball (0 : Euclidean d) (r + R) \ closedBall (0 : Euclidean d) (r - R)) :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * R) *
        volume (ball (0 : Euclidean d) 1) := by
      have hthin := volume_thin_annulus_le d hrone hrtwo (δ := R / 2)
        (by positivity) (by linarith)
      have htwo : 2 * (R / 2) = R := by ring
      rw [htwo] at hthin
      calc
        volume (ball (0 : Euclidean d) (r + R) \ closedBall (0 : Euclidean d) (r - R)) ≤
            ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * (R / 2)) *
              volume (ball (0 : Euclidean d) 1) := hthin
        _ = ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * R) *
              volume (ball (0 : Euclidean d) 1) := by
          congr 2
          ring

/-- The union of radial annuli over a finite family of radii in `[1,2]` has
volume at most the cardinality times the single-annulus bound.  Disjointness
is not needed for this upper bound. -/
theorem volume_biUnion_radialAnnulus_le
    (d : ℕ) {E : Set ℝ} {s : Finset ℝ} {R : ℝ}
    (hsE : (↑s : Set ℝ) ⊆ E) (hE : E ⊆ Icc (1 : ℝ) 2)
    (hR : 0 < R) (hRhalf : R ≤ 1 / 2) :
    volume (⋃ r ∈ s, radialAnnulus d r R) ≤
      (s.card : ENNReal) *
        (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * R) *
          volume (ball (0 : Euclidean d) 1)) := by
  let A : ENNReal :=
    ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * R) *
      volume (ball (0 : Euclidean d) 1)
  calc
    volume (⋃ r ∈ s, radialAnnulus d r R) ≤
        ∑ r ∈ s, volume (radialAnnulus d r R) :=
      measure_biUnion_finset_le s (fun r => radialAnnulus d r R)
    _ ≤ ∑ _r ∈ s, A := by
      apply Finset.sum_le_sum
      intro r hr
      exact volume_radialAnnulus_le d (hE (hsE hr)).1 (hE (hsE hr)).2 hR hRhalf
    _ = (s.card : ENNReal) * A := by simp

/-- On a positive family of radii the absolute values in the support formula
may be removed. -/
theorem biUnion_radialAnnulus_abs_eq_of_subset_Ioi
    {d : ℕ} {E : Set ℝ} {s : Finset ℝ} {R : ℝ}
    (hsE : (↑s : Set ℝ) ⊆ E) (hEpos : E ⊆ Ioi (0 : ℝ)) :
    (⋃ r ∈ s, radialAnnulus d (abs r) R) =
      ⋃ r ∈ s, radialAnnulus d r R := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨r, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hr, hxr⟩
    refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨hr, ?_⟩⟩
    have hrpos : 0 < r := hEpos (hsE hr)
    rw [abs_of_pos hrpos] at hxr
    exact hxr
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨r, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hr, hxr⟩
    refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨hr, ?_⟩⟩
    have hrpos : 0 < r := hEpos (hsE hr)
    rw [abs_of_pos hrpos]
    exact hxr

/-- The support union occurring in the annulus test has the same volume
bound when the radii are known to lie in `[1,2]`. -/
theorem volume_biUnion_radialAnnulus_abs_le
    (d : ℕ) {E : Set ℝ} {s : Finset ℝ} {R : ℝ}
    (hsE : (↑s : Set ℝ) ⊆ E) (hE : E ⊆ Icc (1 : ℝ) 2)
    (hR : 0 < R) (hRhalf : R ≤ 1 / 2) :
    volume (⋃ r ∈ s, radialAnnulus d (abs r) R) ≤
      (s.card : ENNReal) *
        (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * R) *
          volume (ball (0 : Euclidean d) 1)) := by
  have hEpos : E ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one (hE hr).1
  rw [biUnion_radialAnnulus_abs_eq_of_subset_Ioi hsE hEpos]
  exact volume_biUnion_radialAnnulus_le d hsE hE hR hRhalf

end

end Auto.Spherical.FractalDilations.AnnulusGeometry
end Former_AnnulusGeometry

/- ===== Former FractalDilations/AnnulusScaleGap.lean ===== -/
section Former_AnnulusScaleGap

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.ShellVolume
open Auto.Spherical.SurfaceCore







/-!
# Small-scale power bookkeeping for the annulus test

The geometric packing witness supplies `N > δ^{-α}` radii.  This file turns
that one lower bound into the scalar inequality needed to compare the mass of
the annular sum with its finite support.  It is deliberately independent of
the particular Euclidean volume constants.
-/

namespace Auto.Spherical.FractalDilations.AnnulusScaleGap

open Filter Set

noncomputable section

/-- The elementary small-power separation holds uniformly at every
sufficiently small positive scale. -/
theorem exists_small_rpow_separation_below
    {a b A B C : ℝ} (hB : 0 < B) (hab : a < b) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧ ∀ δ : ℝ,
      0 < δ → δ < δ₀ → C * A * δ ^ b < B * δ ^ a := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have htend : Tendsto (fun δ : ℝ => δ ^ (b - a))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h := (Real.continuousAt_rpow_const 0 (b - a) (Or.inr hba.le)).tendsto
    rw [Real.zero_rpow hba.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hmulTend : Tendsto (fun δ : ℝ => C * A * δ ^ (b - a))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    convert tendsto_const_nhds.mul htend using 1 <;> simp
  have hevent : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), C * A * δ ^ (b - a) < B :=
    hmulTend.eventually (Iio_mem_nhds hB)
  obtain ⟨δ₁, hδ₁, hsubset⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  let δ₀ : ℝ := min δ₁ (1 / 4)
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min hδ₁ (by norm_num)
  have hδ₀quarter : δ₀ ≤ 1 / 4 := by
    dsimp [δ₀]
    exact min_le_right _ _
  have hδ₀δ₁ : δ₀ ≤ δ₁ := by
    dsimp [δ₀]
    exact min_le_left _ _
  refine ⟨δ₀, hδ₀, hδ₀quarter, ?_⟩
  intro δ hδ hδsmall
  have hbase : C * A * δ ^ (b - a) < B :=
    hsubset ⟨hδ, hδsmall.trans_le hδ₀δ₁⟩
  have hδpow : 0 < δ ^ a := Real.rpow_pos_of_pos hδ _
  have hmul : (C * A * δ ^ (b - a)) * δ ^ a < B * δ ^ a :=
    mul_lt_mul_of_pos_right hbase hδpow
  calc
    C * A * δ ^ b = C * A * (δ ^ (b - a) * δ ^ a) := by
      rw [← Real.rpow_add hδ]
      congr 2
      ring
    _ = (C * A * δ ^ (b - a)) * δ ^ a := by ring
    _ < B * δ ^ a := hmul

/-- At sufficiently small scales, the packing lower bound `N > δ^{-α}`
converts a strict power gap into the finite-family inequality used in the
annulus construction. -/
theorem exists_small_packing_rpow_gap
    {α a b r A B C : ℝ}
    (hB : 0 < B) (hr : 0 ≤ r) (hba : b < a) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∀ N : ℝ,
      δ ^ (-α) < N →
        C * A * δ ^ a * N ^ (1 - r) <
          B * δ ^ (b + α * r) * N := by
  obtain ⟨δ, hδ, hδsmall, hscale⟩ :=
    exists_small_rpow_separation (a := b) (b := a) (A := A) (B := B) (C := C)
      hB hba
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro N hN
  have hDpos : 0 < δ ^ (-α) := Real.rpow_pos_of_pos hδ _
  have hNpos : 0 < N := hDpos.trans hN
  have hNpow : (δ ^ (-α)) ^ r ≤ N ^ r :=
    Real.rpow_le_rpow hDpos.le hN.le hr
  have habsorb : N ^ (1 - r) * (δ ^ (-α)) ^ r ≤ N := by
    calc
      N ^ (1 - r) * (δ ^ (-α)) ^ r ≤ N ^ (1 - r) * N ^ r :=
        mul_le_mul_of_nonneg_left hNpow (Real.rpow_nonneg hNpos.le _)
      _ = N ^ ((1 - r) + r) := (Real.rpow_add hNpos _ _).symm
      _ = N := by
        rw [show (1 - r) + r = (1 : ℝ) by ring, Real.rpow_one]
  have hdelta_factor : δ ^ b * N ^ (1 - r) =
      δ ^ (b + α * r) * (N ^ (1 - r) * (δ ^ (-α)) ^ r) := by
    calc
      δ ^ b * N ^ (1 - r) = N ^ (1 - r) * δ ^ b := by ring
      _ = N ^ (1 - r) *
          (δ ^ (b + α * r) * δ ^ ((-α) * r)) := by
        congr 1
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      _ = δ ^ (b + α * r) * (N ^ (1 - r) * δ ^ ((-α) * r)) := by ring
      _ = δ ^ (b + α * r) * (N ^ (1 - r) * (δ ^ (-α)) ^ r) := by
        rw [← Real.rpow_mul hδ.le]
  have hright : (B * δ ^ b) * N ^ (1 - r) ≤
      B * δ ^ (b + α * r) * N := by
    calc
      (B * δ ^ b) * N ^ (1 - r) = B * (δ ^ b * N ^ (1 - r)) := by ring
      _ = B * (δ ^ (b + α * r) *
          (N ^ (1 - r) * (δ ^ (-α)) ^ r)) := by rw [hdelta_factor]
      _ ≤ B * (δ ^ (b + α * r) * N) := by
        gcongr
      _ = B * δ ^ (b + α * r) * N := by ring
  calc
    C * A * δ ^ a * N ^ (1 - r) =
        (C * A * δ ^ a) * N ^ (1 - r) := by ring
    _ < (B * δ ^ b) * N ^ (1 - r) :=
      mul_lt_mul_of_pos_right hscale (Real.rpow_pos_of_pos hNpos _)
    _ ≤ B * δ ^ (b + α * r) * N := hright

/-- Uniform version of `exists_small_packing_rpow_gap`, suited to the
packing witness whose exact small scale is chosen only afterwards. -/
theorem exists_small_packing_rpow_gap_below
    {α a b r A B C : ℝ}
    (hB : 0 < B) (hr : 0 ≤ r) (hba : b < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧ ∀ δ : ℝ,
      0 < δ → δ < δ₀ → ∀ N : ℝ, δ ^ (-α) ≤ N →
        C * A * δ ^ a * N ^ (1 - r) <
          B * δ ^ (b + α * r) * N := by
  obtain ⟨δ₀, hδ₀, hδ₀small, hscale⟩ :=
    exists_small_rpow_separation_below (a := b) (b := a) (A := A) (B := B)
      (C := C) hB hba
  refine ⟨δ₀, hδ₀, hδ₀small, ?_⟩
  intro δ hδ hδsmall N hN
  have hDpos : 0 < δ ^ (-α) := Real.rpow_pos_of_pos hδ _
  have hNpos : 0 < N := hDpos.trans_le hN
  have hNpow : (δ ^ (-α)) ^ r ≤ N ^ r :=
    Real.rpow_le_rpow hDpos.le hN hr
  have habsorb : N ^ (1 - r) * (δ ^ (-α)) ^ r ≤ N := by
    calc
      N ^ (1 - r) * (δ ^ (-α)) ^ r ≤ N ^ (1 - r) * N ^ r :=
        mul_le_mul_of_nonneg_left hNpow (Real.rpow_nonneg hNpos.le _)
      _ = N ^ ((1 - r) + r) := (Real.rpow_add hNpos _ _).symm
      _ = N := by
        rw [show (1 - r) + r = (1 : ℝ) by ring, Real.rpow_one]
  have hdelta_factor : δ ^ b * N ^ (1 - r) =
      δ ^ (b + α * r) * (N ^ (1 - r) * (δ ^ (-α)) ^ r) := by
    calc
      δ ^ b * N ^ (1 - r) = N ^ (1 - r) * δ ^ b := by ring
      _ = N ^ (1 - r) *
          (δ ^ (b + α * r) * δ ^ ((-α) * r)) := by
        congr 1
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      _ = δ ^ (b + α * r) * (N ^ (1 - r) * δ ^ ((-α) * r)) := by ring
      _ = δ ^ (b + α * r) * (N ^ (1 - r) * (δ ^ (-α)) ^ r) := by
        rw [← Real.rpow_mul hδ.le]
  have hright : (B * δ ^ b) * N ^ (1 - r) ≤
      B * δ ^ (b + α * r) * N := by
    calc
      (B * δ ^ b) * N ^ (1 - r) = B * (δ ^ b * N ^ (1 - r)) := by ring
      _ = B * (δ ^ (b + α * r) *
          (N ^ (1 - r) * (δ ^ (-α)) ^ r)) := by rw [hdelta_factor]
      _ ≤ B * (δ ^ (b + α * r) * N) := by
        gcongr
      _ = B * δ ^ (b + α * r) * N := by ring
  calc
    C * A * δ ^ a * N ^ (1 - r) =
        (C * A * δ ^ a) * N ^ (1 - r) := by ring
    _ < (B * δ ^ b) * N ^ (1 - r) :=
      mul_lt_mul_of_pos_right (hscale δ hδ hδsmall)
        (Real.rpow_pos_of_pos hNpos _)
    _ ≤ B * δ ^ (b + α * r) * N := hright

/-- The preceding abstract gap with the constants obtained from a ball of
radius `δ / 8`.  The statement is already factorized into the exact powers
of `δ` needed for the Minkowski annulus test. -/
theorem exists_small_annulus_factorized_gap
    {d : ℕ} {α p q C K V : ℝ}
    (hV : 0 < V) (hq : 1 ≤ q)
    (hbad : (1 - α) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∀ N : ℝ,
      δ ^ (-α) < N →
        C * (4 ^ (-((d : ℝ) * p⁻¹)) * V ^ p⁻¹) *
            (K * V / 4) ^ (1 - q⁻¹) *
            δ ^ ((d : ℝ) * p⁻¹ + (1 - q⁻¹)) * N ^ (1 - q⁻¹) <
          (8 ^ (-(d : ℝ)) * V) * δ ^ (d : ℝ) * N := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos.le
  have hba : (d : ℝ) - α * q⁻¹ <
      (d : ℝ) * p⁻¹ + (1 - q⁻¹) := by
    linarith [hbad]
  have hB : 0 < 8 ^ (-(d : ℝ)) * V :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hV
  obtain ⟨δ, hδ, hδsmall, hgap⟩ :=
    exists_small_packing_rpow_gap
      (α := α) (a := (d : ℝ) * p⁻¹ + (1 - q⁻¹))
      (b := (d : ℝ) - α * q⁻¹) (r := q⁻¹)
      (A := (4 ^ (-((d : ℝ) * p⁻¹)) * V ^ p⁻¹) *
        (K * V / 4) ^ (1 - q⁻¹))
      (B := 8 ^ (-(d : ℝ)) * V) (C := C) hB hr hba
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro N hN
  have h := hgap N hN
  convert h using 1 <;> ring

/-- Uniform below-threshold form of the factorized annulus scale gap. -/
theorem exists_small_annulus_factorized_gap_below
    {d : ℕ} {α p q C K V : ℝ}
    (hV : 0 < V) (hq : 1 ≤ q)
    (hbad : (1 - α) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧ ∀ δ : ℝ,
      0 < δ → δ < δ₀ → ∀ N : ℝ, δ ^ (-α) ≤ N →
        C * (4 ^ (-((d : ℝ) * p⁻¹)) * V ^ p⁻¹) *
            (K * V / 4) ^ (1 - q⁻¹) *
            δ ^ ((d : ℝ) * p⁻¹ + (1 - q⁻¹)) * N ^ (1 - q⁻¹) <
          (8 ^ (-(d : ℝ)) * V) * δ ^ (d : ℝ) * N := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos.le
  have hba : (d : ℝ) - α * q⁻¹ <
      (d : ℝ) * p⁻¹ + (1 - q⁻¹) := by
    linarith [hbad]
  have hB : 0 < 8 ^ (-(d : ℝ)) * V :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hV
  obtain ⟨δ₀, hδ₀, hδ₀small, hgap⟩ :=
    exists_small_packing_rpow_gap_below
      (α := α) (a := (d : ℝ) * p⁻¹ + (1 - q⁻¹))
      (b := (d : ℝ) - α * q⁻¹) (r := q⁻¹)
      (A := (4 ^ (-((d : ℝ) * p⁻¹)) * V ^ p⁻¹) *
        (K * V / 4) ^ (1 - q⁻¹))
      (B := 8 ^ (-(d : ℝ)) * V) (C := C) hB hr hba
  refine ⟨δ₀, hδ₀, hδ₀small, ?_⟩
  intro δ hδ hδsmall N hN
  have h := hgap δ hδ hδsmall N hN
  convert h using 1 <;> ring

/-- Reassemble the factorized small-scale inequality into the literal ball
and annulus-volume expression at the scale `R = δ / 8`. -/
theorem annulus_volume_gap_real_of_factorized
    {d : ℕ} {p q C K V δ N : ℝ}
    (hδ : 0 < δ) (hN : 0 < N) (hK : 0 ≤ K) (hV : 0 < V)
    (hfactor :
      C * (4 ^ (-((d : ℝ) * p⁻¹)) * V ^ p⁻¹) *
          (K * V / 4) ^ (1 - q⁻¹) *
          δ ^ ((d : ℝ) * p⁻¹ + (1 - q⁻¹)) * N ^ (1 - q⁻¹) <
        (8 ^ (-(d : ℝ)) * V) * δ ^ (d : ℝ) * N) :
    C * (((δ / 4) ^ (d : ℝ) * V) ^ p⁻¹) *
        (N * (K * (δ / 4) * V)) ^ (1 - q⁻¹) <
      N * (δ / 8) ^ (d : ℝ) * V := by
  have hδfour : 0 ≤ δ / 4 := by positivity
  have hKVfour : 0 ≤ K * V / 4 := by positivity
  have hA : ((δ / 4) ^ (d : ℝ) * V) ^ p⁻¹ =
      (4 ^ (-((d : ℝ) * p⁻¹)) * V ^ p⁻¹) *
        δ ^ ((d : ℝ) * p⁻¹) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hδfour _) hV.le]
    rw [← Real.rpow_mul hδfour]
    rw [Real.div_rpow hδ.le (by norm_num : (0 : ℝ) ≤ 4)]
    rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    ring
  have hB : (N * (K * (δ / 4) * V)) ^ (1 - q⁻¹) =
      N ^ (1 - q⁻¹) * (K * V / 4) ^ (1 - q⁻¹) *
        δ ^ (1 - q⁻¹) := by
    have hrewrite : K * (δ / 4) * V = (K * V / 4) * δ := by ring
    rw [hrewrite, Real.mul_rpow hN.le (mul_nonneg hKVfour hδ.le)]
    rw [Real.mul_rpow hKVfour hδ.le]
    ring
  have hδpow : δ ^ ((d : ℝ) * p⁻¹) * δ ^ (1 - q⁻¹) =
      δ ^ ((d : ℝ) * p⁻¹ + (1 - q⁻¹)) :=
    (Real.rpow_add hδ _ _).symm
  have hleft : C * (((δ / 4) ^ (d : ℝ) * V) ^ p⁻¹) *
      (N * (K * (δ / 4) * V)) ^ (1 - q⁻¹) =
      C * (4 ^ (-((d : ℝ) * p⁻¹)) * V ^ p⁻¹) *
          (K * V / 4) ^ (1 - q⁻¹) *
          δ ^ ((d : ℝ) * p⁻¹ + (1 - q⁻¹)) * N ^ (1 - q⁻¹) := by
    rw [hA, hB]
    calc
      C * ((4 ^ (-((d : ℝ) * p⁻¹)) * V ^ p⁻¹) *
          δ ^ ((d : ℝ) * p⁻¹)) *
          (N ^ (1 - q⁻¹) * (K * V / 4) ^ (1 - q⁻¹) *
            δ ^ (1 - q⁻¹)) =
          C * (4 ^ (-((d : ℝ) * p⁻¹)) * V ^ p⁻¹) *
            (K * V / 4) ^ (1 - q⁻¹) *
            (δ ^ ((d : ℝ) * p⁻¹) * δ ^ (1 - q⁻¹)) * N ^ (1 - q⁻¹) := by
              ring
      _ = C * (4 ^ (-((d : ℝ) * p⁻¹)) * V ^ p⁻¹) *
            (K * V / 4) ^ (1 - q⁻¹) *
            δ ^ ((d : ℝ) * p⁻¹ + (1 - q⁻¹)) * N ^ (1 - q⁻¹) := by
              rw [hδpow]
  have hright : N * (δ / 8) ^ (d : ℝ) * V =
      (8 ^ (-(d : ℝ)) * V) * δ ^ (d : ℝ) * N := by
    rw [Real.div_rpow hδ.le (by norm_num : (0 : ℝ) ≤ 8)]
    rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
    ring
  rw [hleft, hright]
  exact hfactor

/-- The literal `δ / 8` small-scale volume gap, uniform for every packing
cardinality above `δ^{-α}`. -/
theorem exists_small_annulus_volume_gap_real
    {d : ℕ} {α p q C K V : ℝ}
    (hK : 0 ≤ K) (hV : 0 < V) (hq : 1 ≤ q)
    (hbad : (1 - α) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∀ N : ℝ,
      δ ^ (-α) < N →
        C * (((δ / 4) ^ (d : ℝ) * V) ^ p⁻¹) *
            (N * (K * (δ / 4) * V)) ^ (1 - q⁻¹) <
          N * (δ / 8) ^ (d : ℝ) * V := by
  obtain ⟨δ, hδ, hδsmall, hfactor⟩ :=
    exists_small_annulus_factorized_gap (d := d) (α := α) (p := p) (q := q)
      (C := C) (K := K) hV hq hbad
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro N hN
  have hNpos : 0 < N :=
    (Real.rpow_pos_of_pos hδ (-α)).trans hN
  exact annulus_volume_gap_real_of_factorized hδ hNpos hK hV (hfactor N hN)

/-- Uniform below-threshold form of the literal `δ / 8` annulus volume gap. -/
theorem exists_small_annulus_volume_gap_real_below
    {d : ℕ} {α p q C K V : ℝ}
    (hK : 0 ≤ K) (hV : 0 < V) (hq : 1 ≤ q)
    (hbad : (1 - α) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧ ∀ δ : ℝ,
      0 < δ → δ < δ₀ → ∀ N : ℝ, δ ^ (-α) ≤ N →
        C * (((δ / 4) ^ (d : ℝ) * V) ^ p⁻¹) *
            (N * (K * (δ / 4) * V)) ^ (1 - q⁻¹) <
          N * (δ / 8) ^ (d : ℝ) * V := by
  obtain ⟨δ₀, hδ₀, hδ₀small, hfactor⟩ :=
    exists_small_annulus_factorized_gap_below (d := d) (α := α) (p := p)
      (q := q) (C := C) (K := K) (V := V) hV hq hbad
  refine ⟨δ₀, hδ₀, hδ₀small, ?_⟩
  intro δ hδ hδsmall N hN
  have hNpos : 0 < N :=
    (Real.rpow_pos_of_pos hδ (-α)).trans_le hN
  exact annulus_volume_gap_real_of_factorized hδ hNpos hK hV
    (hfactor δ hδ hδsmall N hN)

end

end Auto.Spherical.FractalDilations.AnnulusScaleGap
end Former_AnnulusScaleGap

/- ===== Former FractalDilations/ClusterTube.lean ===== -/
section Former_ClusterTube

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ClusterBump
open Auto.Spherical.FractalDilations.ClusterGeometry
open Auto.Spherical.SurfaceCore







/-!
# Smooth curved cap tubes for the clustered-radius example

The input in Section 4.4 of Anderson--Hughes--Roos--Seeger is a thin radial
shell restricted to a transverse cap, rather than a Cartesian slab.  This
module supplies its smooth compactly-supported replacement.  The separate
volume and spherical-cap estimates can use the sets defined here directly.
-/

namespace Auto.Spherical.FractalDilations.ClusterTube

open MeasureTheory Metric Set

noncomputable section

/-- The closed curved cap tube centred on the sphere of radius `r`: a radial
shell of width `δ`, restricted to transverse radius `σ`. -/
def closedSphericalCapTube (n : ℕ) (r δ σ : ℝ) : Set (Euclidean (n + 1)) :=
  {y | |‖y‖ - r| ≤ δ ∧ ‖(euclideanSuccCoordinates n y).1‖ ≤ σ}

/-- The open squared-radius cap tube used to record the support of the
smooth cutoff.  Squared radius keeps the radial cutoff smooth at the origin. -/
def squaredSphericalCapTube (n : ℕ) (r Δ σ : ℝ) : Set (Euclidean (n + 1)) :=
  {y | |‖y‖ ^ 2 - r ^ 2| < Δ ∧ ‖(euclideanSuccCoordinates n y).1‖ < σ}

/-- At radii at least one, a squared-radius error controls the ordinary radial
error with the same constant.  This is the final conversion used after the
clustered cap geometry estimates `‖x + tω‖² - r²`. -/
theorem abs_norm_sub_le_of_abs_norm_sq_sub_le
    {m : ℕ} {r δ : ℝ} (hr : 1 ≤ r) (y : Euclidean m)
    (h : |‖y‖ ^ 2 - r ^ 2| ≤ δ) :
    |‖y‖ - r| ≤ δ := by
  have hsum : 1 ≤ ‖y‖ + r := by
    exact le_trans (by norm_num) (add_le_add (norm_nonneg _) hr)
  have hfac : |‖y‖ - r| * (‖y‖ + r) ≤ δ := by
    rw [← abs_of_nonneg (add_nonneg (norm_nonneg _) (le_trans zero_le_one hr)),
      ← abs_mul]
    convert h using 1 <;> ring
  calc
    |‖y‖ - r| = |‖y‖ - r| * 1 := by ring
    _ ≤ |‖y‖ - r| * (‖y‖ + r) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ δ := hfac

theorem measurableSet_squaredSphericalCapTube (n : ℕ) (r Δ σ : ℝ) :
    MeasurableSet (squaredSphericalCapTube n r Δ σ) := by
  have hrad : Measurable (fun y : Euclidean (n + 1) => |‖y‖ ^ 2 - r ^ 2|) :=
    continuous_abs.measurable.comp
      ((measurable_norm.pow_const 2).sub measurable_const)
  have hhor : Measurable (fun y : Euclidean (n + 1) =>
      (euclideanSuccCoordinates n y).1) :=
    (contDiff_euclideanSuccCoordinates n).fst.continuous.measurable
  change MeasurableSet {y : Euclidean (n + 1) |
    |‖y‖ ^ 2 - r ^ 2| < Δ ∧ ‖(euclideanSuccCoordinates n y).1‖ < σ}
  exact (measurableSet_lt hrad measurable_const).inter
    (measurableSet_lt (measurable_norm.comp hhor) measurable_const)

/-- A nonnegative real-valued Schwartz cutoff for the curved tube in the
clustered-radius construction.  It equals one on the genuine radius tube and
is supported in a comparable squared-radius tube. -/
theorem exists_schwartz_sphericalCapTube_test
    {n : ℕ} {r δ σ : ℝ}
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2)
    (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4) (hσ : 0 < σ) :
    ∃ f : SchwartzMap (Euclidean (n + 1)) ℂ,
      (∀ y : Euclidean (n + 1), y ∈ closedSphericalCapTube n r δ σ → f y = 1) ∧
      (∀ y : Euclidean (n + 1),
        y ∉ squaredSphericalCapTube n r (10 * δ) (2 * σ) → f y = 0) ∧
      (∀ y : Euclidean (n + 1), 0 ≤ (f y).re) ∧
      (∀ y : Euclidean (n + 1), (f y).im = 0) ∧
      (∀ y : Euclidean (n + 1), ‖f y‖ ≤ 1) := by
  let hor : Euclidean (n + 1) → Euclidean n := fun y =>
    (euclideanSuccCoordinates n y).1
  let sq : Euclidean (n + 1) → ℝ := fun y => inner ℝ y y
  let bhor : ContDiffBump (0 : Euclidean n) := ⟨σ, 2 * σ, hσ, by linarith⟩
  let brad : ContDiffBump (r ^ 2) := ⟨5 * δ, 10 * δ, by positivity, by linarith⟩
  let radial : Euclidean (n + 1) → ℝ := fun y => brad (sq y)
  let g : Euclidean (n + 1) → ℂ := fun y =>
    Complex.ofReal (bhor (hor y) * radial y)
  have hhor : ContDiff ℝ (⊤ : ℕ∞) hor := by
    exact (contDiff_euclideanSuccCoordinates n).fst
  have hsq : ContDiff ℝ (⊤ : ℕ∞) sq := by
    exact contDiff_id.inner ℝ contDiff_id
  have hsq_eq (y : Euclidean (n + 1)) : sq y = ‖y‖ ^ 2 := by
    dsimp only [sq]
    exact real_inner_self_eq_norm_sq y
  have hradial : ContDiff ℝ (⊤ : ℕ∞) radial :=
    brad.contDiff.comp hsq
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact Complex.ofRealCLM.contDiff.comp
      ((bhor.contDiff.comp hhor).mul hradial)
  have hradialcompact : HasCompactSupport radial := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean (n + 1)) 3)
    intro y hy
    have hynorm : 3 < ‖y‖ := by
      rw [mem_closedBall, dist_zero_right] at hy
      exact lt_of_not_ge hy
    have hsqy : 9 < ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    have hrsq : r ^ 2 ≤ 4 := by nlinarith
    have hdiff : 10 * δ ≤ ‖y‖ ^ 2 - r ^ 2 := by
      nlinarith
    have hdiffnonneg : 0 ≤ ‖y‖ ^ 2 - r ^ 2 := le_trans (by positivity) hdiff
    change brad (sq y) = 0
    apply brad.zero_of_le_dist
    rw [hsq_eq, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hdiffnonneg]
    simpa [brad] using hdiff
  have hproductcompact : HasCompactSupport (fun y : Euclidean (n + 1) =>
      bhor (hor y) * radial y) := hradialcompact.mul_left
  have hcompact : HasCompactSupport g := by
    change HasCompactSupport ((fun z : ℝ => (z : ℂ)) ∘
      fun y : Euclidean (n + 1) => bhor (hor y) * radial y)
    exact hproductcompact.comp_left (g := fun z : ℝ => (z : ℂ)) (by rfl)
  have hschwartz_apply (y : Euclidean (n + 1)) :
      (hcompact.toSchwartzMap hsmooth) y = g y := rfl
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hschwartz_apply]
    simp only [g, Complex.ofReal_mul]
    change |‖y‖ - r| ≤ δ ∧ ‖hor y‖ ≤ σ at hy
    have hnormle : ‖y‖ ≤ r + δ := by
      linarith [((abs_le.mp hy.1).2)]
    have hsum : ‖y‖ + r ≤ 5 := by linarith
    have hsqdiff : |sq y - r ^ 2| ≤ 5 * δ := by
      rw [hsq_eq, show ‖y‖ ^ 2 - r ^ 2 = (‖y‖ - r) * (‖y‖ + r) by ring,
        abs_mul]
      calc
        |‖y‖ - r| * |‖y‖ + r| ≤ δ * |‖y‖ + r| :=
          mul_le_mul_of_nonneg_right hy.1 (abs_nonneg _)
        _ ≤ δ * 5 := by
          apply mul_le_mul_of_nonneg_left
            (show |‖y‖ + r| ≤ 5 by
              rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (le_trans zero_le_one hrone))]
              exact hsum)
          positivity
        _ = 5 * δ := by ring
    have hhorball : dist (hor y) (0 : Euclidean n) ≤ σ := by
      rw [dist_zero_right]
      exact hy.2
    have hradball : dist (sq y) (r ^ 2) ≤ 5 * δ := by
      rw [dist_eq_norm, Real.norm_eq_abs]
      exact hsqdiff
    have hradone : radial y = 1 := by
      change brad (sq y) = 1
      rw [brad.one_of_mem_closedBall hradball]
    rw [bhor.one_of_mem_closedBall hhorball, hradone]
    norm_num
  · intro y hy
    rw [hschwartz_apply]
    simp only [g, Complex.ofReal_mul]
    by_cases hhorout : 2 * σ ≤ ‖hor y‖
    · rw [show (bhor (hor y) : ℂ) = 0 by
        norm_cast
        apply bhor.zero_of_le_dist
        rw [dist_zero_right]
        exact hhorout, zero_mul]
    have hhorin : ‖hor y‖ < 2 * σ := lt_of_not_ge hhorout
    by_cases hradout : 10 * δ ≤ |sq y - r ^ 2|
    · rw [show (brad (sq y) : ℂ) = 0 by
        norm_cast
        apply brad.zero_of_le_dist
        rw [dist_eq_norm, Real.norm_eq_abs]
        exact hradout, mul_zero]
    exfalso
    apply hy
    have hradin : |‖y‖ ^ 2 - r ^ 2| < 10 * δ := by
      simpa only [hsq_eq] using lt_of_not_ge hradout
    exact ⟨hradin, by simpa only [hor] using hhorin⟩
  · intro y
    rw [hschwartz_apply]
    simp only [g, Complex.ofReal_re]
    exact mul_nonneg (bhor.nonneg' (hor y)) (brad.nonneg' (sq y))
  · intro y
    rw [hschwartz_apply]
    simp only [g, Complex.ofReal_im]
  · intro y
    rw [hschwartz_apply]
    simp only [g, Complex.ofReal_mul]
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (bhor.nonneg' (hor y)),
      Real.norm_of_nonneg (brad.nonneg' (sq y))]
    exact mul_le_one₀ (bhor.le_one) (brad.nonneg' (sq y)) (brad.le_one)

/-- The standard `Lᵖ` envelope for a bounded Schwartz function supported in
a squared-radius cap tube.  Quantitative tube-volume bounds are deliberately
kept separate from this functional-analytic step. -/
theorem eLpNorm_schwartz_sphericalCapTube_le
    {n : ℕ} {r Δ σ p : ℝ} (hp : 0 < p)
    (f : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hzero : ∀ y : Euclidean (n + 1),
      y ∉ squaredSphericalCapTube n r Δ σ → f y = 0)
    (hbound : ∀ y : Euclidean (n + 1), ‖f y‖ ≤ 1) :
    eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
      volume (squaredSphericalCapTube n r Δ σ) ^ p⁻¹ := by
  let A : Set (Euclidean (n + 1)) := squaredSphericalCapTube n r Δ σ
  have hAmeas : MeasurableSet A :=
    measurableSet_squaredSphericalCapTube n r Δ σ
  change eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
    volume A ^ p⁻¹
  calc
    eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
        eLpNorm (A.indicator fun _ : Euclidean (n + 1) => (1 : ℂ))
          (ENNReal.ofReal p) volume := by
      apply eLpNorm_mono
      intro y
      by_cases hy : y ∈ A
      · rw [Set.indicator_of_mem hy, norm_one]
        exact hbound y
      · rw [Set.indicator_of_notMem hy, hzero y hy]
    _ = volume A ^ p⁻¹ := by
      rw [eLpNorm_indicator_const hAmeas
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
      simp only [enorm_one, one_mul, ENNReal.toReal_ofReal hp.le, one_div]

end

end Auto.Spherical.FractalDilations.ClusterTube
end Former_ClusterTube

/- ===== Former FractalDilations/ShellSharpness.lean ===== -/
section Former_ShellSharpness

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.Definitions
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Maximal
open Auto.Spherical.FractalDilations.SharpnessNormalization
open Auto.Spherical.FractalDilations.SharpnessVolume
open Auto.Spherical.FractalDilations.ShellBump
open Auto.Spherical.FractalDilations.ShellVolume
open Auto.Spherical.SurfaceCore







/-!
# The spherical-cap sharpness test

This module turns the smooth squared-radius bump from `ShellBump` into the
usual cap obstruction.  The geometric support estimate is kept separate from
the eventual small-scale power comparison, so that every analytic estimate is
available in a directly reusable form.
-/

namespace Auto.Spherical.FractalDilations.ShellSharpness

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The support strip of a squared-radius shell lies in an ordinary thin
annulus. -/
theorem squared_shell_subset_thin_annulus
    {d : ℕ} {r δ : ℝ} (hrone : 1 ≤ r) (hδ : 0 < δ) :
    {y : Euclidean d | |‖y‖ ^ 2 - r ^ 2| < 2 * δ} ⊆
      ball (0 : Euclidean d) (r + 2 * δ) \
        closedBall (0 : Euclidean d) (r - 2 * δ) := by
  intro y hy
  have hynonneg : 0 ≤ ‖y‖ := norm_nonneg y
  have hupper : ‖y‖ < r + 2 * δ := by
    by_contra hnot
    have htr : r + 2 * δ ≤ ‖y‖ := le_of_not_gt hnot
    have hfirst : 2 * δ ≤ ‖y‖ - r := by linarith
    have hsecond : 1 ≤ ‖y‖ + r := by linarith
    have hproduct : (2 * δ) * 1 ≤ (‖y‖ - r) * (‖y‖ + r) :=
      mul_le_mul hfirst hsecond zero_le_one (by linarith)
    have hmain : 2 * δ ≤ ‖y‖ ^ 2 - r ^ 2 := by
      convert hproduct using 1 <;> ring
    have habs : 2 * δ ≤ |‖y‖ ^ 2 - r ^ 2| := hmain.trans (le_abs_self _)
    exact (not_le_of_gt hy) habs
  have hlower : r - 2 * δ < ‖y‖ := by
    by_contra hnot
    have htr : ‖y‖ ≤ r - 2 * δ := le_of_not_gt hnot
    have hfirst : 2 * δ ≤ r - ‖y‖ := by linarith
    have hsecond : 1 ≤ r + ‖y‖ := by linarith
    have hproduct : (2 * δ) * 1 ≤ (r - ‖y‖) * (r + ‖y‖) :=
      mul_le_mul hfirst hsecond zero_le_one (by linarith)
    have hmain : 2 * δ ≤ r ^ 2 - ‖y‖ ^ 2 := by
      convert hproduct using 1 <;> ring
    have hnonpos : ‖y‖ ^ 2 - r ^ 2 ≤ 0 := by linarith
    have habs : 2 * δ ≤ |‖y‖ ^ 2 - r ^ 2| := by
      rw [abs_of_nonpos hnonpos]
      linarith
    exact (not_le_of_gt hy) habs
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_zero_right]
    exact hupper
  · rw [mem_closedBall, dist_zero_right]
    exact not_le.mpr hlower

/-- The `Lᵖ` norm of a bounded squared-radius shell is controlled by the
volume of its containing thin annulus. -/
theorem eLpNorm_squared_shell_test_le_annulus
    {d : ℕ} {r δ p : ℝ} (hrone : 1 ≤ r) (hδ : 0 < δ) (hp : 0 < p)
    (f : SchwartzMap (Euclidean d) ℂ)
    (hzero : ∀ y : Euclidean d, 2 * δ ≤ |‖y‖ ^ 2 - r ^ 2| → f y = 0)
    (hbound : ∀ y : Euclidean d, ‖f y‖ ≤ 1) :
    eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤
      volume (ball (0 : Euclidean d) (r + 2 * δ) \
        closedBall (0 : Euclidean d) (r - 2 * δ)) ^ p⁻¹ := by
  let A : Set (Euclidean d) :=
    ball (0 : Euclidean d) (r + 2 * δ) \
      closedBall (0 : Euclidean d) (r - 2 * δ)
  have hAmeas : MeasurableSet A :=
    (isOpen_ball.measurableSet.diff measurableSet_closedBall)
  change eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤ volume A ^ p⁻¹
  calc
    eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤
        eLpNorm (A.indicator fun _ : Euclidean d => (1 : ℂ)) (ENNReal.ofReal p) volume := by
      apply eLpNorm_mono
      intro y
      by_cases hy : y ∈ A
      · rw [Set.indicator_of_mem hy, norm_one]
        exact hbound y
      · rw [Set.indicator_of_notMem hy]
        have hnot : ¬ |‖y‖ ^ 2 - r ^ 2| < 2 * δ := by
          intro hstrip
          exact hy (squared_shell_subset_thin_annulus hrone hδ hstrip)
        rw [hzero y (le_of_not_gt hnot)]
    _ = volume A ^ p⁻¹ := by
      rw [eLpNorm_indicator_const hAmeas
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
      simp only [enorm_one, one_mul, ENNReal.toReal_ofReal hp.le, one_div]

/-- Combining the elementary annulus-volume bound with the support estimate
gives the explicit input estimate used by the cap test. -/
theorem eLpNorm_squared_shell_test_le_thin_annulus_bound
    (d : ℕ) {r δ p : ℝ}
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2) (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4)
    (hp : 0 < p) (f : SchwartzMap (Euclidean d) ℂ)
    (hzero : ∀ y : Euclidean d, 2 * δ ≤ |‖y‖ ^ 2 - r ^ 2| → f y = 0)
    (hbound : ∀ y : Euclidean d, ‖f y‖ ≤ 1) :
    eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
        volume (ball (0 : Euclidean d) 1)) ^ p⁻¹ := by
  refine (eLpNorm_squared_shell_test_le_annulus hrone hδ hp f hzero hbound).trans ?_
  exact ENNReal.rpow_le_rpow
    (volume_thin_annulus_le d hrone hrtwo hδ hδquarter) (inv_nonneg.mpr hp.le)

/-- The two scale powers in the cap example separate below a sufficiently
small shell thickness.  This is the real-valued form of the comparison; the
next lemma transfers it to `ENNReal` norms. -/
theorem exists_small_squared_shell_gap_real
    {d : ℕ} (hd : 0 < d) {p q C : ℝ}
    (hC : 0 < C) (hp : 0 < p) (hq : 0 < q)
    (hbad : (d : ℝ) * q⁻¹ < p⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      C * (((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
        (volume (ball (0 : Euclidean d) 1)).toReal) ^ p⁻¹ <
      (((δ / 8) ^ d) * (volume (ball (0 : Euclidean d) 1)).toReal) ^ q⁻¹ := by
  let V : ℝ := (volume (ball (0 : Euclidean d) 1)).toReal
  let K : ℝ := 4 * (d : ℝ) * 3 ^ (d - 1)
  have hV : 0 < V := volume_unit_ball_toReal_pos hd
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hB : 0 < (8⁻¹ : ℝ) ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹ := by positivity
  obtain ⟨δ, hδ, hδquarter, hsep⟩ := exists_small_rpow_separation
    (a := (d : ℝ) * q⁻¹) (b := p⁻¹)
    (A := (K * V) ^ p⁻¹)
    (B := (8⁻¹ : ℝ) ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹)
    (C := C) hB hbad
  refine ⟨δ, hδ, hδquarter.le, ?_⟩
  have hleft : C * (K * δ * V) ^ p⁻¹ =
      (C * (K * V) ^ p⁻¹) * δ ^ p⁻¹ := by
    have hrewrite : K * δ * V = (K * V) * δ := by ring
    rw [hrewrite, Real.mul_rpow (mul_nonneg hK.le hV.le) hδ.le]
    ring
  have hright : (((δ / 8) ^ d) * V) ^ q⁻¹ =
      ((8⁻¹ : ℝ) ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹) * δ ^ ((d : ℝ) * q⁻¹) := by
    have hδ8 : 0 ≤ δ / 8 := by positivity
    calc
      (((δ / 8) ^ d) * V) ^ q⁻¹ =
          ((δ / 8) ^ d) ^ q⁻¹ * V ^ q⁻¹ := by
        rw [Real.mul_rpow (pow_nonneg hδ8 _) hV.le]
      _ = (δ / 8) ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ8]
      _ = (δ ^ ((d : ℝ) * q⁻¹) *
          (8⁻¹ : ℝ) ^ ((d : ℝ) * q⁻¹)) * V ^ q⁻¹ := by
        rw [show δ / 8 = δ * (8⁻¹ : ℝ) by ring,
          Real.mul_rpow hδ.le (by positivity)]
      _ = ((8⁻¹ : ℝ) ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹) *
          δ ^ ((d : ℝ) * q⁻¹) := by ring
  change C * (K * δ * V) ^ p⁻¹ < (((δ / 8) ^ d) * V) ^ q⁻¹
  rw [hleft, hright]
  exact hsep

/-- `ENNReal` form of the small-shell separation, tailored to the input and
output norms in the cap test. -/
theorem exists_small_squared_shell_gap
    {d : ℕ} (hd : 0 < d) {p q C : ℝ}
    (hC : 0 < C) (hp : 0 < p) (hq : 0 < q)
    (hbad : (d : ℝ) * q⁻¹ < p⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      ENNReal.ofReal C *
        (ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
          volume (ball (0 : Euclidean d) 1)) ^ p⁻¹ <
      volume (ball (0 : Euclidean d) (δ / 8)) ^ q⁻¹ := by
  let V : ℝ := (volume (ball (0 : Euclidean d) 1)).toReal
  let K : ℝ := 4 * (d : ℝ) * 3 ^ (d - 1)
  obtain ⟨δ, hδ, hδquarter, hreal⟩ :=
    exists_small_squared_shell_gap_real hd hC hp hq hbad
  have hK : 0 < K := by
    dsimp [K]
    have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hKδ : 0 ≤ K * δ := mul_nonneg hK.le hδ.le
  have hunit_top : volume (ball (0 : Euclidean d) 1) ≠ (⊤ : ENNReal) :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := (1 : ℝ))).ne
  let X : ENNReal := ENNReal.ofReal C *
    (ENNReal.ofReal (K * δ) * volume (ball (0 : Euclidean d) 1)) ^ p⁻¹
  let Y : ENNReal := volume (ball (0 : Euclidean d) (δ / 8)) ^ q⁻¹
  have hbase_top : ENNReal.ofReal (K * δ) * volume (ball (0 : Euclidean d) 1) ≠
      (⊤ : ENNReal) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunit_top
  have hXtop : X ≠ (⊤ : ENNReal) := by
    dsimp [X]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le) hbase_top)
  have hYtop : Y ≠ (⊤ : ENNReal) := by
    dsimp [Y]
    exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hq.le)
      (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := δ / 8)).ne
  refine ⟨δ, hδ, hδquarter, ?_⟩
  change X < Y
  apply (ENNReal.toReal_lt_toReal hXtop hYtop).mp
  have hleft : X.toReal = C * (K * δ * V) ^ p⁻¹ := by
    dsimp [X]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le,
      ← ENNReal.toReal_rpow, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hKδ]
  have hright : Y.toReal = (((δ / 8) ^ d) * V) ^ q⁻¹ := by
    dsimp [Y]
    rw [← ENNReal.toReal_rpow,
      volume_ball_toReal d (δ / 8) (by positivity)]
  change X.toReal < Y.toReal
  rw [hleft, hright]
  change C * (K * δ * V) ^ p⁻¹ < (((δ / 8) ^ d) * V) ^ q⁻¹ at hreal
  exact hreal

/-- The smooth thickened-sphere (or spherical-cap) example rules out the
strict region `d / q < 1 / p`. -/
theorem fractalSphericalUnbounded_of_spherical_cap
    {d : ℕ} (hd : 2 ≤ d)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hbad : (d : ℝ) * q⁻¹ < p⁻¹) :
    FractalSphericalUnbounded d E p q := by
  have hd0 : 0 < d := by omega
  have hEpos : E ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one (hE hr).1
  apply fractalSphericalUnbounded_of_large_ratio
  intro C hC
  obtain ⟨r, hr⟩ := hEne
  have hrone : 1 ≤ r := (hE hr).1
  have hrtwo : r ≤ 2 := (hE hr).2
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrone
  obtain ⟨δ, hδ, hδquarter, hgap⟩ :=
    exists_small_squared_shell_gap hd0 hC hp hq hbad
  have hδone : δ ≤ 1 := by linarith
  obtain ⟨f, hfone, hfzero, hfbound⟩ :=
    exists_schwartz_squared_shell_test (d := d) hrpos hrtwo hδ hδone
  let A : ENNReal :=
    (ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
      volume (ball (0 : Euclidean d) 1)) ^ p⁻¹
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd0
  have hKδ : 0 < (4 * (d : ℝ) * 3 ^ (d - 1)) * δ := by positivity
  have hbasepos : 0 < ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
      volume (ball (0 : Euclidean d) 1) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hKδ).ne'
      (Metric.measure_ball_pos volume (0 : Euclidean d) (by norm_num)).ne'
  have hbasetop : ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
      volume (ball (0 : Euclidean d) 1) ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := (1 : ℝ))).ne
  refine ⟨f, A, ?_, ?_, ?_, ?_⟩
  · dsimp [A]
    exact (ENNReal.rpow_pos hbasepos hbasetop).ne'
  · dsimp [A]
    exact ENNReal.rpow_ne_top_of_ne_zero hbasepos.ne' hbasetop
  · dsimp [A]
    exact eLpNorm_squared_shell_test_le_thin_annulus_bound d hrone hrtwo hδ hδquarter
      hp f hfzero hfbound
  · calc
      ENNReal.ofReal C * A < volume (ball (0 : Euclidean d) (δ / 8)) ^ q⁻¹ := by
        simpa only [A] using hgap
      _ ≤ eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume :=
        volume_ball_rpow_le_eLpNorm_fractalSphericalMaximalReal_of_squared_shell
          hd0 E hEpos f hr (by linarith [hrone]) hrtwo hδ.le hδone hfone hq

end

end Auto.Spherical.FractalDilations.ShellSharpness
end Former_ShellSharpness

/- ===== Former FractalDilations/AnnulusNorm.lean ===== -/
section Former_AnnulusNorm

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ExponentRegions







/-!
# Finite-support norm bookkeeping for the annulus test

The mass argument for the small-ball example first controls an `L¹` norm.
On the finite union of radial annuli, the standard finite-measure comparison
then transfers that information to every Banach exponent `q ≥ 1`.
-/

namespace Auto.Spherical.FractalDilations.AnnulusNorm

open MeasureTheory Set ENNReal

noncomputable section

/-- On a finite support, the `L¹` seminorm is controlled by the `L^q`
seminorm times the usual measure factor.  The statement is kept general so
the annulus construction can apply it to a finite sum of fixed-radius
averages. -/
theorem eLpNorm_one_le_eLpNorm_of_support_subset
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {S : Set X}
    {g : X → ℝ} {q : ℝ} (hq : 1 ≤ q)
    (hg : AEStronglyMeasurable g μ) (hsupport : Function.support g ⊆ S) :
    eLpNorm g 1 μ ≤ eLpNorm g (ENNReal.ofReal q) μ * μ S ^ (1 - q⁻¹) := by
  have hpq : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ.restrict S) (f := g) hpq (hg.restrict)
  rw [eLpNorm_restrict_eq_of_support_subset (p := (1 : ENNReal)) hsupport,
    eLpNorm_restrict_eq_of_support_subset (p := ENNReal.ofReal q) hsupport] at hcompare
  simpa [Measure.restrict_apply_univ, ENNReal.toReal_ofReal
    (le_trans zero_le_one hq),
    one_div, inv_one] using hcompare

end

end Auto.Spherical.FractalDilations.AnnulusNorm
end Former_AnnulusNorm

/- ===== Former FractalDilations/AnnulusNumericalBridge.lean ===== -/
section Former_AnnulusNumericalBridge

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.AnnulusScaleGap
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.SharpnessVolume
open Auto.Spherical.SurfaceCore







/-!
# ENNReal form of the annulus scale gap

This file translates the real power inequality at scale `δ / 8` into the
precise `ENNReal.toReal` expression generated by the norm and support-volume
lemmas.  It is the numerical interface consumed by the final Minkowski
annulus sharpness argument.
-/

namespace Auto.Spherical.FractalDilations.AnnulusNumericalBridge

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The small-scale annulus gap written in exactly the mixed real/`ENNReal`
form arising from the mass estimate. -/
theorem exists_small_annulus_ennreal_gap
    {d : ℕ} {α p q C : ℝ}
    (hd : 0 < d) (hq : 1 ≤ q)
    (hbad : (1 - α) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∀ N : ℕ,
      δ ^ (-α) < (N : ℝ) →
        C *
            (volume (ball (0 : Euclidean d) (2 * (δ / 8))) ^ p⁻¹).toReal *
            (((N : ENNReal) *
              (ENNReal.ofReal
                ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * (δ / 8))) *
                volume (ball (0 : Euclidean d) 1))) ^ (1 - q⁻¹)).toReal <
          (N : ℝ) * (volume (ball (0 : Euclidean d) (δ / 8))).toReal := by
  let K : ℝ := 2 * (d : ℝ) * 3 ^ (d - 1)
  let V : ℝ := (volume (ball (0 : Euclidean d) 1)).toReal
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hV : 0 < V := volume_unit_ball_toReal_pos hd
  obtain ⟨δ, hδ, hδsmall, hgap⟩ :=
    exists_small_annulus_volume_gap_real (d := d) (α := α) (p := p) (q := q)
      (C := C) (K := K) (V := V) hK hV hq hbad
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro N hN
  have hR : 0 < δ / 8 := by positivity
  have htwoR : 0 < 2 * (δ / 8) := by positivity
  have hKtwoR : 0 ≤ K * (2 * (δ / 8)) := by positivity
  have hA :
      (volume (ball (0 : Euclidean d) (2 * (δ / 8))) ^ p⁻¹).toReal =
        ((δ / 4) ^ (d : ℝ) * V) ^ p⁻¹ := by
    rw [← ENNReal.toReal_rpow]
    rw [volume_ball_toReal d (2 * (δ / 8)) htwoR]
    rw [show 2 * (δ / 8) = δ / 4 by ring, ← Real.rpow_natCast]
  have hB :
      (((N : ENNReal) *
        (ENNReal.ofReal (K * (2 * (δ / 8))) *
          volume (ball (0 : Euclidean d) 1))) ^ (1 - q⁻¹)).toReal =
        ((N : ℝ) * (K * (δ / 4) * V)) ^ (1 - q⁻¹) := by
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hKtwoR]
    dsimp [V]
    congr 1
    ring
  have hL : (volume (ball (0 : Euclidean d) (δ / 8))).toReal =
      (δ / 8) ^ (d : ℝ) * V := by
    rw [volume_ball_toReal d (δ / 8) hR, ← Real.rpow_natCast]
  rw [hA, hB, hL]
  simpa [mul_assoc] using hgap (N : ℝ) hN

/-- Uniform below-threshold ENNReal form of the annulus scale gap. -/
theorem exists_small_annulus_ennreal_gap_below
    {d : ℕ} {α p q C : ℝ}
    (hd : 0 < d) (hq : 1 ≤ q)
    (hbad : (1 - α) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧ ∀ δ : ℝ,
      0 < δ → δ < δ₀ → ∀ N : ℕ, δ ^ (-α) ≤ (N : ℝ) →
        C *
            (volume (ball (0 : Euclidean d) (2 * (δ / 8))) ^ p⁻¹).toReal *
            (((N : ENNReal) *
              (ENNReal.ofReal
                ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * (δ / 8))) *
                volume (ball (0 : Euclidean d) 1))) ^ (1 - q⁻¹)).toReal <
          (N : ℝ) * (volume (ball (0 : Euclidean d) (δ / 8))).toReal := by
  let K : ℝ := 2 * (d : ℝ) * 3 ^ (d - 1)
  let V : ℝ := (volume (ball (0 : Euclidean d) 1)).toReal
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hV : 0 < V := volume_unit_ball_toReal_pos hd
  obtain ⟨δ₀, hδ₀, hδ₀small, hgap⟩ :=
    exists_small_annulus_volume_gap_real_below (d := d) (α := α) (p := p)
      (q := q) (C := C) (K := K) (V := V) hK hV hq hbad
  refine ⟨δ₀, hδ₀, hδ₀small, ?_⟩
  intro δ hδ hδsmall N hN
  have hR : 0 < δ / 8 := by positivity
  have htwoR : 0 < 2 * (δ / 8) := by positivity
  have hKtwoR : 0 ≤ K * (2 * (δ / 8)) := by positivity
  have hA :
      (volume (ball (0 : Euclidean d) (2 * (δ / 8))) ^ p⁻¹).toReal =
        ((δ / 4) ^ (d : ℝ) * V) ^ p⁻¹ := by
    rw [← ENNReal.toReal_rpow]
    rw [volume_ball_toReal d (2 * (δ / 8)) htwoR]
    rw [show 2 * (δ / 8) = δ / 4 by ring, ← Real.rpow_natCast]
  have hB :
      (((N : ENNReal) *
        (ENNReal.ofReal (K * (2 * (δ / 8))) *
          volume (ball (0 : Euclidean d) 1))) ^ (1 - q⁻¹)).toReal =
        ((N : ℝ) * (K * (δ / 4) * V)) ^ (1 - q⁻¹) := by
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hKtwoR]
    dsimp [V]
    congr 1
    ring
  have hL : (volume (ball (0 : Euclidean d) (δ / 8))).toReal =
      (δ / 8) ^ (d : ℝ) * V := by
    rw [volume_ball_toReal d (δ / 8) hR, ← Real.rpow_natCast]
  rw [hA, hB, hL]
  simpa [mul_assoc] using hgap δ hδ hδsmall (N : ℝ) hN

end

end Auto.Spherical.FractalDilations.AnnulusNumericalBridge
end Former_AnnulusNumericalBridge

/- ===== Former FractalDilations/ClusterCapGeometry.lean ===== -/
section Former_ClusterCapGeometry

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ClusterGeometry
open Auto.Spherical.FractalDilations.ClusterTube
open Auto.Spherical.SurfaceCore
open Auto.Spherical.SurfaceHeightCore







/-!
# Spherical-cap geometry for clustered dilations

The clustered-radius sharpness example samples a thin horizontal slab through
a cap about the final-coordinate pole of the unit sphere.  This file isolates
the entirely finite-dimensional inclusion: points in the small cap, viewed
from a suitably thin output slab, land in the input slab.  Measure lower
bounds for that cap are kept separate from this deterministic geometry.
-/

namespace Auto.Spherical.FractalDilations.ClusterCapGeometry

open MeasureTheory Metric Set

noncomputable section

/-- The positive final-coordinate unit vector in `Euclidean (n + 1)`. -/
def euclideanSuccLast (n : ℕ) : Euclidean (n + 1) :=
  MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)
    (fun i : Fin (n + 1) => if i = Fin.last n then 1 else 0)

theorem norm_euclideanSuccLast (n : ℕ) : ‖euclideanSuccLast n‖ = 1 := by
  simpa only [euclideanSuccLast] using
    Auto.Spherical.SurfaceHeightCore.norm_euclideanSucc_last n

/-- The negative final-coordinate pole of the unit sphere. -/
def negEuclideanSuccLastSphere (n : ℕ) : sphere (0 : Euclidean (n + 1)) 1 :=
  ⟨-euclideanSuccLast n, by
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact norm_euclideanSuccLast n⟩

/-- The positive final-coordinate pole of the unit sphere. -/
def euclideanSuccLastSphere (n : ℕ) : sphere (0 : Euclidean (n + 1)) 1 :=
  ⟨euclideanSuccLast n, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_euclideanSuccLast n⟩

/-- The first `n` coordinates of the negative final-coordinate pole vanish. -/
theorem euclideanSuccCoordinates_negLast_fst (n : ℕ) :
    (euclideanSuccCoordinates n (-euclideanSuccLast n)).1 = 0 := by
  have hcast_ne_last (i : Fin n) : Fin.castAdd 1 i ≠ Fin.last n := by
    intro h
    apply (Nat.ne_of_lt i.isLt)
    simpa using congrArg Fin.val h
  ext i
  simp [euclideanSuccCoordinates, euclideanSuccLast,
    MeasurableEquiv.coe_toLp, PiLp.toLp_apply, hcast_ne_last]

/-- The final coordinate of the negative final-coordinate pole is `-1`. -/
theorem euclideanSuccCoordinates_negLast_snd (n : ℕ) :
    (euclideanSuccCoordinates n (-euclideanSuccLast n)).2 = -1 := by
  simp [euclideanSuccCoordinates, euclideanSuccLast,
    MeasurableEquiv.coe_toLp, PiLp.toLp_apply]

/-- A cap about the negative final-coordinate pole controls both the
transverse coordinates and the deviation of the final coordinate from `-1`.
This is the coordinate estimate used by the slab inclusion below. -/
theorem coordinate_bounds_of_mem_ball_negEuclideanSuccLastSphere
    {n : ℕ} {ε : ℝ} {ω : sphere (0 : Euclidean (n + 1)) 1}
    (hω : ω ∈ ball (negEuclideanSuccLastSphere n) ε) :
    ‖(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖ < ε ∧
      |(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).2 + 1| < ε := by
  have hdist : ‖(ω : Euclidean (n + 1)) + euclideanSuccLast n‖ < ε := by
    change dist (ω : Euclidean (n + 1)) (-euclideanSuccLast n) < ε at hω
    rw [dist_eq_norm] at hω
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hω
  have hsq := Auto.Spherical.SurfaceCore.norm_sq_euclideanSucc_coordinates n
    ((ω : Euclidean (n + 1)) + euclideanSuccLast n)
  have hcast_ne_last (i : Fin n) : Fin.castAdd 1 i ≠ Fin.last n := by
    intro h
    apply (Nat.ne_of_lt i.isLt)
    simpa using congrArg Fin.val h
  rw [show (fun i : Fin n =>
      (((ω : Euclidean (n + 1)) + euclideanSuccLast n) (Fin.castAdd 1 i))) =
        fun i : Fin n => (ω : Euclidean (n + 1)) (Fin.castAdd 1 i) by
        funext i
        simp [euclideanSuccLast, MeasurableEquiv.coe_toLp, PiLp.toLp_apply,
          hcast_ne_last]] at hsq
  rw [show ((ω : Euclidean (n + 1)) + euclideanSuccLast n) (Fin.last n) =
      (ω : Euclidean (n + 1)) (Fin.last n) + 1 by
        simp [euclideanSuccLast, MeasurableEquiv.coe_toLp, PiLp.toLp_apply]] at hsq
  change
    ‖MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i : Fin n =>
        (ω : Euclidean (n + 1)) (Fin.castAdd 1 i))‖ < ε ∧
      |(ω : Euclidean (n + 1)) (Fin.last n) + 1| < ε
  have hnorm_nonneg : 0 ≤ ‖(ω : Euclidean (n + 1)) + euclideanSuccLast n‖ :=
    norm_nonneg _
  have hεpos : 0 < ε := hnorm_nonneg.trans_lt hdist
  constructor
  · have hsq_nonneg : 0 ≤
        ‖MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i : Fin n =>
          (ω : Euclidean (n + 1)) (Fin.castAdd 1 i))‖ ^ 2 := sq_nonneg _
    have hlastsq_nonneg : 0 ≤ ((ω : Euclidean (n + 1)) (Fin.last n) + 1) ^ 2 :=
      sq_nonneg _
    nlinarith [sq_nonneg (ε - ‖(ω : Euclidean (n + 1)) + euclideanSuccLast n‖)]
  · have hfstsq_nonneg : 0 ≤
        ‖MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i : Fin n =>
          (ω : Euclidean (n + 1)) (Fin.castAdd 1 i))‖ ^ 2 := sq_nonneg _
    have hlast_nonneg : 0 ≤ |(ω : Euclidean (n + 1)) (Fin.last n) + 1| := abs_nonneg _
    have hlastsq : |(ω : Euclidean (n + 1)) (Fin.last n) + 1| ^ 2 =
        ((ω : Euclidean (n + 1)) (Fin.last n) + 1) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (ε - ‖(ω : Euclidean (n + 1)) + euclideanSuccLast n‖)]

/-- The corresponding coordinate bounds for a cap about the positive pole. -/
theorem coordinate_bounds_of_mem_ball_euclideanSuccLastSphere
    {n : ℕ} {ε : ℝ} {ω : sphere (0 : Euclidean (n + 1)) 1}
    (hω : ω ∈ ball (euclideanSuccLastSphere n) ε) :
    ‖(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖ < ε ∧
      |(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).2 - 1| < ε := by
  have hdist : ‖(ω : Euclidean (n + 1)) - euclideanSuccLast n‖ < ε := by
    change dist (ω : Euclidean (n + 1)) (euclideanSuccLast n) < ε at hω
    simpa only [dist_eq_norm] using hω
  have hsq := Auto.Spherical.SurfaceCore.norm_sq_euclideanSucc_coordinates n
    ((ω : Euclidean (n + 1)) - euclideanSuccLast n)
  have hcast_ne_last (i : Fin n) : Fin.castAdd 1 i ≠ Fin.last n := by
    intro h
    apply (Nat.ne_of_lt i.isLt)
    simpa using congrArg Fin.val h
  rw [show (fun i : Fin n =>
      (((ω : Euclidean (n + 1)) - euclideanSuccLast n) (Fin.castAdd 1 i))) =
        fun i : Fin n => (ω : Euclidean (n + 1)) (Fin.castAdd 1 i) by
        funext i
        simp [euclideanSuccLast, MeasurableEquiv.coe_toLp, PiLp.toLp_apply,
          hcast_ne_last]] at hsq
  rw [show ((ω : Euclidean (n + 1)) - euclideanSuccLast n) (Fin.last n) =
      (ω : Euclidean (n + 1)) (Fin.last n) - 1 by
        simp [euclideanSuccLast, MeasurableEquiv.coe_toLp, PiLp.toLp_apply]] at hsq
  change
    ‖MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i : Fin n =>
        (ω : Euclidean (n + 1)) (Fin.castAdd 1 i))‖ < ε ∧
      |(ω : Euclidean (n + 1)) (Fin.last n) - 1| < ε
  have hnorm_nonneg : 0 ≤ ‖(ω : Euclidean (n + 1)) - euclideanSuccLast n‖ :=
    norm_nonneg _
  have hεpos : 0 < ε := hnorm_nonneg.trans_lt hdist
  constructor
  · have hsq_nonneg : 0 ≤
        ‖MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i : Fin n =>
          (ω : Euclidean (n + 1)) (Fin.castAdd 1 i))‖ ^ 2 := sq_nonneg _
    have hlastsq_nonneg : 0 ≤ ((ω : Euclidean (n + 1)) (Fin.last n) - 1) ^ 2 :=
      sq_nonneg _
    nlinarith [sq_nonneg (ε - ‖(ω : Euclidean (n + 1)) - euclideanSuccLast n‖)]
  · have hfstsq_nonneg : 0 ≤
        ‖MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i : Fin n =>
          (ω : Euclidean (n + 1)) (Fin.castAdd 1 i))‖ ^ 2 := sq_nonneg _
    have hlast_nonneg : 0 ≤ |(ω : Euclidean (n + 1)) (Fin.last n) - 1| := abs_nonneg _
    have hlastsq : |(ω : Euclidean (n + 1)) (Fin.last n) - 1| ^ 2 =
        ((ω : Euclidean (n + 1)) (Fin.last n) - 1) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (ε - ‖(ω : Euclidean (n + 1)) - euclideanSuccLast n‖)]

/-- Cartesian coordinates commute with the affine sampling map used in the
clustered-radius construction. -/
theorem euclideanSuccCoordinates_add_smul
    (n : ℕ) (x z : Euclidean (n + 1)) (t : ℝ) :
    euclideanSuccCoordinates n (x + t • z) =
      ((euclideanSuccCoordinates n x).1 + t • (euclideanSuccCoordinates n z).1,
        (euclideanSuccCoordinates n x).2 + t * (euclideanSuccCoordinates n z).2) := by
  apply Prod.ext
  · ext i
    simp [euclideanSuccCoordinates, PiLp.toLp_apply]
  · simp [euclideanSuccCoordinates]

/-- The transverse part of a clustered output slab plus a cap of directions
stays inside the transverse tube.  The output scale `δ / σ` is absorbed by
the standard relation `δ ≤ σ²`. -/
theorem transverse_norm_add_smul_le_of_small_output_and_cap
    {n : ℕ} {δ σ t : ℝ} (hσ : 0 < σ)
    (hδσ : δ ≤ σ ^ 2) (ht0 : 0 ≤ t) (ht : t ≤ 2)
    (x : Euclidean (n + 1))
    (hx : ‖(euclideanSuccCoordinates n x).1‖ ≤ δ / (128 * σ))
    {ω : sphere (0 : Euclidean (n + 1)) 1}
    (hω : ω ∈ ball (euclideanSuccLastSphere n) (σ / 128)) :
    ‖(euclideanSuccCoordinates n (x + t • (ω : Euclidean (n + 1)))).1‖ ≤ σ := by
  rcases coordinate_bounds_of_mem_ball_euclideanSuccLastSphere hω with ⟨hωhor, _⟩
  have hδdiv : δ / (128 * σ) ≤ σ / 128 := by
    apply (div_le_iff₀ (by positivity : 0 < 128 * σ)).mpr
    nlinarith [hδσ]
  rw [euclideanSuccCoordinates_add_smul]
  calc
    ‖(euclideanSuccCoordinates n x).1 +
        t • (euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖ ≤
        ‖(euclideanSuccCoordinates n x).1‖ +
          ‖t • (euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖ :=
      norm_add_le _ _
    _ = ‖(euclideanSuccCoordinates n x).1‖ +
          |t| * ‖(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ δ / (128 * σ) + |t| * (σ / 128) := by
      apply add_le_add hx
      exact mul_le_mul_of_nonneg_left hωhor.le (abs_nonneg _)
    _ ≤ σ := by
      have habs_t : |t| ≤ 2 := abs_le.2 ⟨by linarith, ht⟩
      nlinarith

/-- The transverse and vertical errors used to expand the sampled squared
radius in the clustered-cap construction. -/
def clusterTransverse (n : ℕ) (y : Euclidean (n + 1)) : Euclidean n :=
  (euclideanSuccCoordinates n y).1

def clusterVertical (n : ℕ) (y : Euclidean (n + 1)) : ℝ :=
  (euclideanSuccCoordinates n y).2

/-- Pythagoras for the transverse/vertical coordinates used below.  Keeping
this tiny coercion-facing lemma separate makes the geometric calculation
independent of the implementation of `Euclidean`. -/
theorem norm_sq_cluster_coordinates (n : ℕ) (y : Euclidean (n + 1)) :
    ‖y‖ ^ 2 = ‖clusterTransverse n y‖ ^ 2 + clusterVertical n y ^ 2 := by
  change ‖y‖ ^ 2 =
    ‖MeasurableEquiv.toLp 2 (Fin n → ℝ)
        (fun i : Fin n => y (Fin.castAdd 1 i))‖ ^ 2 + y (Fin.last n) ^ 2
  exact Auto.Spherical.SurfaceCore.norm_sq_euclideanSucc_coordinates n y

/-- Exact squared-radius identity behind the curved cap-tube inclusion.
The sphere relation cancels the potentially large first-order cap curvature;
only the short interval factor `t - r` remains. -/
theorem cluster_squared_norm_identity
    (n : ℕ) (r t : ℝ) (x : Euclidean (n + 1))
    (ω : sphere (0 : Euclidean (n + 1)) 1) :
    let u := clusterTransverse n x
    let v := clusterVertical n x - (r - t)
    let a := clusterTransverse n (ω : Euclidean (n + 1))
    let b := clusterVertical n (ω : Euclidean (n + 1)) - 1
    ‖x + t • (ω : Euclidean (n + 1))‖ ^ 2 - r ^ 2 =
      t * (t - r) * (‖a‖ ^ 2 + b ^ 2) +
        ‖u‖ ^ 2 + 2 * t * inner ℝ u a + 2 * r * v + v ^ 2 + 2 * t * v * b := by
  dsimp only
  have hωnorm : ‖(ω : Euclidean (n + 1))‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using ω.property
  have hunit :
      ‖clusterTransverse n (ω : Euclidean (n + 1))‖ ^ 2 +
        (1 + (clusterVertical n (ω : Euclidean (n + 1)) - 1)) ^ 2 = 1 := by
    rw [show 1 + (clusterVertical n (ω : Euclidean (n + 1)) - 1) =
      clusterVertical n (ω : Euclidean (n + 1)) by ring]
    rw [← norm_sq_cluster_coordinates, hωnorm]
    norm_num
  have hysq :
      ‖x + t • (ω : Euclidean (n + 1))‖ ^ 2 =
        ‖clusterTransverse n x + t •
            clusterTransverse n (ω : Euclidean (n + 1))‖ ^ 2 +
          (r + (clusterVertical n x - (r - t)) +
            t * (clusterVertical n (ω : Euclidean (n + 1)) - 1)) ^ 2 := by
    calc
      ‖x + t • (ω : Euclidean (n + 1))‖ ^ 2 =
          ‖clusterTransverse n (x + t • (ω : Euclidean (n + 1)))‖ ^ 2 +
            clusterVertical n (x + t • (ω : Euclidean (n + 1)) ) ^ 2 := by
          exact norm_sq_cluster_coordinates n (x + t • (ω : Euclidean (n + 1)))
      _ = _ := by
          simp only [clusterTransverse, clusterVertical,
            euclideanSuccCoordinates_add_smul]
          ring
  rw [hysq, norm_add_sq_real]
  rw [inner_smul_right]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hcurv :
      ‖clusterTransverse n (ω : Euclidean (n + 1))‖ ^ 2 +
          (clusterVertical n (ω : Euclidean (n + 1)) - 1) ^ 2 =
        -2 * (clusterVertical n (ω : Euclidean (n + 1)) - 1) := by
    nlinarith [hunit]
  rw [hcurv]
  linear_combination t ^ 2 * hcurv

/-- A small anisotropic output box, sampled in directions from a very small
cap about the positive pole, lands in the curved input cap tube.  The proof
keeps the curvature cancellation from `cluster_squared_norm_identity`
explicit; this is the geometric core of the clustered-dilations test. -/
theorem sampled_mem_closedSphericalCapTube_of_small_output
    {n : ℕ} {r t δ σ : ℝ}
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2)
    (htzero : 0 ≤ t) (httwo : t ≤ 2)
    (hδ : 0 < δ) (hδσ : δ ≤ σ ^ 2)
    (hσ : 0 < σ) (hσone : σ ≤ 1)
    (hshort : |t - r| * σ ^ 2 ≤ δ)
    (x : Euclidean (n + 1))
    (hxhor : ‖(euclideanSuccCoordinates n x).1‖ ≤ δ / (128 * σ))
    (hxvert : |(euclideanSuccCoordinates n x).2 - (r - t)| ≤ δ / 128)
    {ω : sphere (0 : Euclidean (n + 1)) 1}
    (hω : ω ∈ ball (euclideanSuccLastSphere n) (σ / 128)) :
    x + t • (ω : Euclidean (n + 1)) ∈ closedSphericalCapTube n r δ σ := by
  let u : Euclidean n := clusterTransverse n x
  let v : ℝ := clusterVertical n x - (r - t)
  let a : Euclidean n := clusterTransverse n (ω : Euclidean (n + 1))
  let b : ℝ := clusterVertical n (ω : Euclidean (n + 1)) - 1
  have hδnonneg : 0 ≤ δ := hδ.le
  have hσnonneg : 0 ≤ σ := hσ.le
  have hσsqle : σ ^ 2 ≤ 1 := by
    have haux : 0 ≤ σ * (1 - σ) :=
      mul_nonneg hσnonneg (sub_nonneg.mpr hσone)
    nlinarith
  have hδone : δ ≤ 1 := hδσ.trans hσsqle
  have hu : ‖u‖ ≤ δ / (128 * σ) := by
    simpa only [u, clusterTransverse] using hxhor
  have hv : |v| ≤ δ / 128 := by
    simpa only [v, clusterVertical] using hxvert
  rcases coordinate_bounds_of_mem_ball_euclideanSuccLastSphere hω with ⟨ha_lt, hb_lt⟩
  have ha : ‖a‖ ≤ σ / 128 := by
    simpa only [a, clusterTransverse] using ha_lt.le
  have hb : |b| ≤ σ / 128 := by
    simpa only [b, clusterVertical] using hb_lt.le
  have hσdiv_nonneg : 0 ≤ σ / 128 := by positivity
  have ha_sq : ‖a‖ ^ 2 ≤ (σ / 128) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hσdiv_nonneg).2 ha
  have hb_sq : b ^ 2 ≤ (σ / 128) ^ 2 := by
    rw [← sq_abs b]
    exact (sq_le_sq₀ (abs_nonneg _) hσdiv_nonneg).2 hb
  have hab_sum_nonneg : 0 ≤ ‖a‖ ^ 2 + b ^ 2 := by positivity
  have hab_sum : ‖a‖ ^ 2 + b ^ 2 ≤ σ ^ 2 / 4096 := by
    calc
      ‖a‖ ^ 2 + b ^ 2 ≤ (σ / 128) ^ 2 + (σ / 128) ^ 2 :=
        add_le_add ha_sq hb_sq
      _ = σ ^ 2 / 8192 := by ring
      _ ≤ σ ^ 2 / 4096 := by nlinarith [sq_nonneg σ]
  have habst : |t| ≤ 2 := abs_le.2 ⟨by linarith, httwo⟩
  have hshort_div : |t - r| * (σ ^ 2 / 4096) ≤ δ / 4096 := by
    rw [show |t - r| * (σ ^ 2 / 4096) = (|t - r| * σ ^ 2) / 4096 by ring]
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4096)).2 hshort
  have hcurv_core : |t - r| * (‖a‖ ^ 2 + b ^ 2) ≤ δ / 4096 := by
    calc
      |t - r| * (‖a‖ ^ 2 + b ^ 2) ≤ |t - r| * (σ ^ 2 / 4096) :=
        mul_le_mul_of_nonneg_left hab_sum (abs_nonneg _)
      _ ≤ δ / 4096 := hshort_div
  have hterm1 : |t * (t - r) * (‖a‖ ^ 2 + b ^ 2)| ≤ δ / 16 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hab_sum_nonneg]
    have hmul : |t| * (|t - r| * (‖a‖ ^ 2 + b ^ 2)) ≤ 2 * (δ / 4096) :=
      mul_le_mul habst hcurv_core (by positivity) (by norm_num)
    calc
      |t| * |t - r| * (‖a‖ ^ 2 + b ^ 2) =
          |t| * (|t - r| * (‖a‖ ^ 2 + b ^ 2)) := by ring
      _ ≤ 2 * (δ / 4096) := hmul
      _ ≤ δ / 16 := by linarith only [hδnonneg]
  have hδsq : δ ^ 2 ≤ δ * σ ^ 2 := by
    have haux : 0 ≤ δ * (σ ^ 2 - δ) :=
      mul_nonneg hδnonneg (sub_nonneg.mpr hδσ)
    nlinarith only [haux]
  have hdenpos : 0 < 16384 * σ ^ 2 := by positivity
  have hu_square_bound : (δ / (128 * σ)) ^ 2 ≤ δ / 16384 := by
    calc
      (δ / (128 * σ)) ^ 2 = δ ^ 2 / (16384 * σ ^ 2) := by
        field_simp
        ring
      _ ≤ (δ * σ ^ 2) / (16384 * σ ^ 2) :=
        div_le_div_of_nonneg_right hδsq hdenpos.le
      _ = δ / 16384 := by
        field_simp
  have hu_sq : ‖u‖ ^ 2 ≤ δ / 16384 := by
    exact ((sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ δ / (128 * σ))).2 hu).trans
      hu_square_bound
  have hterm2 : |‖u‖ ^ 2| ≤ δ / 16 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hu_sq.trans (by linarith only [hδnonneg])
  have hua : ‖u‖ * ‖a‖ ≤ δ / 16384 := by
    calc
      ‖u‖ * ‖a‖ ≤ (δ / (128 * σ)) * (σ / 128) :=
        mul_le_mul hu ha (norm_nonneg _) (by positivity)
      _ = δ / 16384 := by
        field_simp
        ring
  have hinter : |inner ℝ u a| ≤ δ / 16384 :=
    (abs_real_inner_le_norm _ _).trans hua
  have hterm3 : |2 * t * inner ℝ u a| ≤ δ / 16 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hmul : |t| * |inner ℝ u a| ≤ 2 * (δ / 16384) :=
      mul_le_mul habst hinter (abs_nonneg _) (by norm_num)
    calc
      2 * |t| * |inner ℝ u a| = 2 * (|t| * |inner ℝ u a|) := by ring
      _ ≤ 2 * (2 * (δ / 16384)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ ≤ δ / 16 := by linarith only [hδnonneg]
  have hterm4 : |2 * r * v| ≤ δ / 16 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (le_trans zero_le_one hrone)]
    have hmul : r * |v| ≤ 2 * (δ / 128) :=
      mul_le_mul hrtwo hv (abs_nonneg _) (by norm_num)
    calc
      2 * r * |v| = 2 * (r * |v|) := by ring
      _ ≤ 2 * (2 * (δ / 128)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ ≤ δ / 16 := by linarith only [hδnonneg]
  have hterm5 : |v ^ 2| ≤ δ / 16 := by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs v]
    calc
      |v| ^ 2 ≤ (δ / 128) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ δ / 128)).2 hv
      _ ≤ δ / 16 := by
        have haux : 0 ≤ δ * (1 - δ) :=
          mul_nonneg hδnonneg (sub_nonneg.mpr hδone)
        nlinarith only [haux]
  have hvb : |v| * |b| ≤ δ / 16384 := by
    calc
      |v| * |b| ≤ (δ / 128) * (σ / 128) :=
        mul_le_mul hv hb (abs_nonneg _) (by positivity)
      _ = (δ * σ) / 16384 := by ring
      _ ≤ δ / 16384 := by
        apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 16384)).2
        simpa using mul_le_mul_of_nonneg_left hσone hδnonneg
  have hterm6 : |2 * t * v * b| ≤ δ / 16 := by
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hmul : |t| * (|v| * |b|) ≤ 2 * (δ / 16384) :=
      mul_le_mul habst hvb (by positivity) (by norm_num)
    calc
      2 * |t| * |v| * |b| = 2 * (|t| * (|v| * |b|)) := by ring
      _ ≤ 2 * (2 * (δ / 16384)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ ≤ δ / 16 := by linarith only [hδnonneg]
  have hsum_terms :
      |t * (t - r) * (‖a‖ ^ 2 + b ^ 2) + ‖u‖ ^ 2 +
          2 * t * inner ℝ u a + 2 * r * v + v ^ 2 + 2 * t * v * b| ≤ δ := by
    calc
      _ ≤ |t * (t - r) * (‖a‖ ^ 2 + b ^ 2) + ‖u‖ ^ 2 +
          2 * t * inner ℝ u a + 2 * r * v + v ^ 2| + |2 * t * v * b| := abs_add_le _ _
      _ ≤ (|t * (t - r) * (‖a‖ ^ 2 + b ^ 2) + ‖u‖ ^ 2 +
          2 * t * inner ℝ u a + 2 * r * v| + |v ^ 2|) + |2 * t * v * b| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((|t * (t - r) * (‖a‖ ^ 2 + b ^ 2) + ‖u‖ ^ 2 +
          2 * t * inner ℝ u a| + |2 * r * v|) + |v ^ 2|) + |2 * t * v * b| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (((|t * (t - r) * (‖a‖ ^ 2 + b ^ 2) + ‖u‖ ^ 2| +
          |2 * t * inner ℝ u a|) + |2 * r * v|) + |v ^ 2|) + |2 * t * v * b| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((((|t * (t - r) * (‖a‖ ^ 2 + b ^ 2)| + |‖u‖ ^ 2|) +
          |2 * t * inner ℝ u a|) + |2 * r * v|) + |v ^ 2|) + |2 * t * v * b| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((((δ / 16 + δ / 16) + δ / 16) + δ / 16) + δ / 16) + δ / 16 := by
        gcongr
      _ ≤ δ := by nlinarith
  have hradial_sq : |‖x + t • (ω : Euclidean (n + 1))‖ ^ 2 - r ^ 2| ≤ δ := by
    rw [show ‖x + t • (ω : Euclidean (n + 1))‖ ^ 2 - r ^ 2 =
      t * (t - r) * (‖a‖ ^ 2 + b ^ 2) + ‖u‖ ^ 2 +
        2 * t * inner ℝ u a + 2 * r * v + v ^ 2 + 2 * t * v * b by
      simpa only [u, v, a, b] using cluster_squared_norm_identity n r t x ω]
    exact hsum_terms
  change |‖x + t • (ω : Euclidean (n + 1))‖ - r| ≤ δ ∧
    ‖(euclideanSuccCoordinates n (x + t • (ω : Euclidean (n + 1)))).1‖ ≤ σ
  constructor
  · exact abs_norm_sub_le_of_abs_norm_sq_sub_le hrone _ hradial_sq
  · exact transverse_norm_add_smul_le_of_small_output_and_cap hσ hδσ htzero httwo x hxhor hω

end

end Auto.Spherical.FractalDilations.ClusterCapGeometry
end Former_ClusterCapGeometry

/- ===== Former FractalDilations/AnnulusMass.lean ===== -/
section Former_AnnulusMass

/- This file was machine-generated by Codex -/

open Auto.Spherical.FourierRadius
open Auto.Spherical.FractalDilations.AnnulusCore
open Auto.Spherical.FractalDilations.AnnulusGeometry
open Auto.Spherical.FractalDilations.AnnulusPositivity
open Auto.Spherical.FractalDilations.AnnulusSupport
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.SeparatedPacking
open Auto.Spherical.SurfaceCore







/-!
# Finite sums of annular spherical averages

For a separated finite set of radii, the real parts of the fixed-radius
averages have disjoint annular supports.  This module records their support,
positivity, integrability, and exact total mass.  It is the bridge between
the geometric packing witness and the norm comparison in `AnnulusNorm`.
-/

namespace Auto.Spherical.FractalDilations.AnnulusMass

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The real sum of the fixed-radius spherical averages indexed by a finite
radius family. -/
def annulusAverageSum (d : ℕ) (f : Euclidean d → ℂ) (s : Finset ℝ) :
    Euclidean d → ℝ :=
  fun x => ∑ r ∈ s, (normalizedSphericalAverage d f r x).re

/-- The real coordinate of any integrable normalized spherical average is
integrable. -/
theorem integrable_re_normalizedSphericalAverage
    {d : ℕ} (f : Euclidean d → ℂ) (hfcont : Continuous f)
    (hf : Integrable f volume) (r : ℝ) :
    Integrable (fun x : Euclidean d => (normalizedSphericalAverage d f r x).re) volume := by
  unfold normalizedSphericalAverage
  exact (integrable_sphericalAverage f hfcont hf r).const_mul _ |>.re

/-- The finite annular sum is supported in the union of its individual radial
annuli. -/
theorem support_annulusAverageSum_subset
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) {R : ℝ}
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0) (s : Finset ℝ) :
    Function.support (annulusAverageSum d f s) ⊆
      ⋃ r ∈ s, radialAnnulus d (abs r) (2 * R) := by
  intro x hx
  change (∑ r ∈ s, (normalizedSphericalAverage d f r x).re) ≠ 0 at hx
  by_contra hnot
  apply hx
  apply Finset.sum_eq_zero
  intro r hr
  have hnotr : x ∉ radialAnnulus d (abs r) (2 * R) := by
    intro hxr
    apply hnot
    exact Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨hr, hxr⟩⟩
  have hsep : 2 * R ≤ abs (‖x‖ - abs r) := by
    apply le_of_not_gt
    change ¬ abs (‖x‖ - abs r) < 2 * R at hnotr
    exact hnotr
  have havg : normalizedSphericalAverage d f r x = 0 :=
    normalizedSphericalAverage_eq_zero_of_radial_separation hd f hzero x hsep
  rw [havg]
  rfl

/-- A real nonnegative input gives a pointwise nonnegative finite annular
sum. -/
theorem annulusAverageSum_nonneg
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) (s : Finset ℝ)
    (hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ))
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re) :
    ∀ x : Euclidean d, 0 ≤ annulusAverageSum d f s x := by
  intro x
  unfold annulusAverageSum
  apply Finset.sum_nonneg
  intro r hr
  have hfun : (fun y : Euclidean d => ((f y).re : ℂ)) = f := by
    funext y
    exact (hreal y).symm
  rw [← hfun]
  exact normalizedSphericalAverage_re_nonneg_of_nonneg hd (fun y => (f y).re)
    hnonneg r x

/-- The annular sum is integrable whenever the input is continuous and
integrable. -/
theorem integrable_annulusAverageSum
    {d : ℕ} (f : Euclidean d → ℂ) (s : Finset ℝ)
    (hfcont : Continuous f) (hf : Integrable f volume) :
    Integrable (annulusAverageSum d f s) volume := by
  unfold annulusAverageSum
  apply integrable_finsetSum
  intro r hr
  exact integrable_re_normalizedSphericalAverage f hfcont hf r

/-- Every radius contributes the same mass, so a finite annular sum has
exactly its cardinality times the input's real mass. -/
theorem integral_annulusAverageSum_eq_card_mul
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) (s : Finset ℝ)
    (hfcont : Continuous f) (hf : Integrable f volume)
    (hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ)) :
    (∫ x : Euclidean d, annulusAverageSum d f s x) =
      (s.card : ℝ) * ∫ x : Euclidean d, (f x).re := by
  have hfun : (fun y : Euclidean d => ((f y).re : ℂ)) = f := by
    funext y
    exact (hreal y).symm
  have hterm : ∀ r ∈ s,
      Integrable (fun x : Euclidean d => (normalizedSphericalAverage d f r x).re) volume := by
    intro r hr
    exact integrable_re_normalizedSphericalAverage f hfcont hf r
  calc
    (∫ x : Euclidean d, annulusAverageSum d f s x) =
        ∑ r ∈ s, ∫ x : Euclidean d, (normalizedSphericalAverage d f r x).re := by
      unfold annulusAverageSum
      exact integral_finsetSum s hterm
    _ = ∑ r ∈ s, ∫ x : Euclidean d, (f x).re := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← hfun]
      exact integral_re_normalizedSphericalAverage_eq_integral hd
        (fun y => (f y).re) (Complex.continuous_re.comp hfcont) hf.re r
    _ = (s.card : ℝ) * ∫ x : Euclidean d, (f x).re := by simp

end

end Auto.Spherical.FractalDilations.AnnulusMass
end Former_AnnulusMass

/- ===== Former FractalDilations/ClusterTubeVolume.lean ===== -/
section Former_ClusterTubeVolume

/- This file was machine-generated by Codex -/

open Auto.Spherical.CoordinateIntegration
open Auto.Spherical.FractalDilations.ClusterBump
open Auto.Spherical.FractalDilations.ClusterCapGeometry
open Auto.Spherical.FractalDilations.ClusterGeometry
open Auto.Spherical.FractalDilations.ClusterTube
open Auto.Spherical.SurfaceCore







/-!
# Geometric volume estimates for curved cap tubes

This file starts the input-volume side of the clustered-radius example.  The
first reduction identifies a transverse cap on the sphere with the union of
two ordinary caps about the final-coordinate poles.
-/

namespace Auto.Spherical.FractalDilations.ClusterTubeVolume

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

/-- The two-sided transverse cap on the unit sphere. -/
def transverseSphereCap (n : ℕ) (ε : ℝ) : Set (sphere (0 : Euclidean (n + 1)) 1) :=
  {ω | ‖(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖ < ε}

theorem fin_castAdd_ne_last (n : ℕ) (i : Fin n) : Fin.castAdd 1 i ≠ Fin.last n := by
  intro h
  apply (Nat.ne_of_lt i.isLt)
  simpa using congrArg Fin.val h

theorem euclideanSuccCoordinates_sub_last (n : ℕ) (x : Euclidean (n + 1)) :
    euclideanSuccCoordinates n (x - euclideanSuccLast n) =
      ((euclideanSuccCoordinates n x).1, (euclideanSuccCoordinates n x).2 - 1) := by
  apply Prod.ext
  · ext i
    simp [euclideanSuccCoordinates, euclideanSuccLast,
      MeasurableEquiv.coe_toLp, PiLp.toLp_apply, fin_castAdd_ne_last]
  · simp [euclideanSuccCoordinates, euclideanSuccLast,
      MeasurableEquiv.coe_toLp, PiLp.toLp_apply]

theorem euclideanSuccCoordinates_add_last (n : ℕ) (x : Euclidean (n + 1)) :
    euclideanSuccCoordinates n (x + euclideanSuccLast n) =
      ((euclideanSuccCoordinates n x).1, (euclideanSuccCoordinates n x).2 + 1) := by
  apply Prod.ext
  · ext i
    simp [euclideanSuccCoordinates, euclideanSuccLast,
      MeasurableEquiv.coe_toLp, PiLp.toLp_apply, fin_castAdd_ne_last]
  · simp [euclideanSuccCoordinates, euclideanSuccLast,
      MeasurableEquiv.coe_toLp, PiLp.toLp_apply]

theorem norm_sq_sub_euclideanSuccLast (n : ℕ) (x : Euclidean (n + 1)) :
    ‖x - euclideanSuccLast n‖ ^ 2 =
      ‖(euclideanSuccCoordinates n x).1‖ ^ 2 +
        ((euclideanSuccCoordinates n x).2 - 1) ^ 2 := by
  calc
    ‖x - euclideanSuccLast n‖ ^ 2 =
        ‖(euclideanSuccCoordinates n (x - euclideanSuccLast n)).1‖ ^ 2 +
          ((euclideanSuccCoordinates n (x - euclideanSuccLast n)).2) ^ 2 := by
      exact Auto.Spherical.SurfaceCore.norm_sq_euclideanSucc_coordinates n _
    _ = ‖(euclideanSuccCoordinates n x).1‖ ^ 2 +
          ((euclideanSuccCoordinates n x).2 - 1) ^ 2 := by
      rw [euclideanSuccCoordinates_sub_last]

theorem norm_sq_add_euclideanSuccLast (n : ℕ) (x : Euclidean (n + 1)) :
    ‖x + euclideanSuccLast n‖ ^ 2 =
      ‖(euclideanSuccCoordinates n x).1‖ ^ 2 +
        ((euclideanSuccCoordinates n x).2 + 1) ^ 2 := by
  calc
    ‖x + euclideanSuccLast n‖ ^ 2 =
        ‖(euclideanSuccCoordinates n (x + euclideanSuccLast n)).1‖ ^ 2 +
          ((euclideanSuccCoordinates n (x + euclideanSuccLast n)).2) ^ 2 := by
      exact Auto.Spherical.SurfaceCore.norm_sq_euclideanSucc_coordinates n _
    _ = ‖(euclideanSuccCoordinates n x).1‖ ^ 2 +
          ((euclideanSuccCoordinates n x).2 + 1) ^ 2 := by
      rw [euclideanSuccCoordinates_add_last]

/-- A transverse cap is contained in the union of ordinary caps around the
two final-coordinate poles. -/
theorem transverseSphereCap_subset_pole_caps (n : ℕ) {ε : ℝ} :
    transverseSphereCap n ε ⊆
      ((fun ω : sphere (0 : Euclidean (n + 1)) 1 => (ω : Euclidean (n + 1))) ⁻¹'
          ball (euclideanSuccLast n) (2 * ε)) ∪
        ((fun ω : sphere (0 : Euclidean (n + 1)) 1 => (ω : Euclidean (n + 1))) ⁻¹'
          ball (-euclideanSuccLast n) (2 * ε)) := by
  intro ω hω
  change ‖(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖ < ε at hω
  let u : Euclidean n := (euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1
  let v : ℝ := (euclideanSuccCoordinates n (ω : Euclidean (n + 1))).2
  have hε : 0 < ε := lt_of_le_of_lt (norm_nonneg u) (by simpa [u] using hω)
  have hunitraw :
      ‖(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖ ^ 2 +
        (euclideanSuccCoordinates n (ω : Euclidean (n + 1))).2 ^ 2 = 1 := by
    have hnorm : ‖(ω : Euclidean (n + 1))‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using ω.property
    have hsplit := Auto.Spherical.SurfaceCore.norm_sq_euclideanSucc_coordinates n
      (ω : Euclidean (n + 1))
    rw [hnorm] at hsplit
    norm_num at hsplit
    exact hsplit.symm
  have hunit : ‖u‖ ^ 2 + v ^ 2 = 1 := by
    simpa [u, v] using hunitraw
  have husq : ‖u‖ ^ 2 < ε ^ 2 := by
    nlinarith [norm_nonneg u]
  by_cases hv : 0 ≤ v
  · left
    change dist (ω : Euclidean (n + 1)) (euclideanSuccLast n) < 2 * ε
    rw [dist_eq_norm]
    have hvsq : (v - 1) ^ 2 ≤ ‖u‖ ^ 2 := by
      nlinarith [sq_nonneg (v + 1), sq_nonneg (v - 1)]
    have hsq : ‖(ω : Euclidean (n + 1)) - euclideanSuccLast n‖ ^ 2 < (2 * ε) ^ 2 := by
      rw [norm_sq_sub_euclideanSuccLast]
      dsimp only [u, v] at hvsq ⊢
      nlinarith
    nlinarith [norm_nonneg ((ω : Euclidean (n + 1)) - euclideanSuccLast n)]
  · right
    have hv' : v ≤ 0 := le_of_not_ge hv
    change dist (ω : Euclidean (n + 1)) (-euclideanSuccLast n) < 2 * ε
    rw [dist_eq_norm, sub_neg_eq_add]
    have hvsq : (v + 1) ^ 2 ≤ ‖u‖ ^ 2 := by
      nlinarith [sq_nonneg (v + 1), sq_nonneg (v - 1)]
    have hsq : ‖(ω : Euclidean (n + 1)) + euclideanSuccLast n‖ ^ 2 < (2 * ε) ^ 2 := by
      rw [norm_sq_add_euclideanSuccLast]
      dsimp only [u, v] at hvsq ⊢
      nlinarith
    nlinarith [norm_nonneg ((ω : Euclidean (n + 1)) + euclideanSuccLast n)]

/-- The two-sided transverse cap has codimension-one surface mass.  This is
the form of the existing cap growth estimate that is convenient for polar
coordinates in the curved-tube volume bound. -/
theorem exists_unitSurfaceMeasure_transverseSphereCap_le_power (n : ℕ) :
    ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ ε : ℝ, 0 ≤ ε →
      (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
          (transverseSphereCap n ε) ≤ C * ENNReal.ofReal (ε ^ n) := by
  obtain ⟨C, hCtop, hcap⟩ :=
    Auto.Spherical.CoordinateIntegration.exists_unitSurfaceMeasure_cap_le_power
      (d := n + 1) (by omega)
  let D : ENNReal := 2 * C * (2 : ENNReal) ^ n
  refine ⟨D, ?_, ?_⟩
  · dsimp [D]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hCtop)
      (ENNReal.pow_ne_top (by norm_num))
  intro ε hε
  let A : Set (sphere (0 : Euclidean (n + 1)) 1) :=
    (fun ω : sphere (0 : Euclidean (n + 1)) 1 => (ω : Euclidean (n + 1))) ⁻¹'
      ball (euclideanSuccLast n) (2 * ε)
  let B : Set (sphere (0 : Euclidean (n + 1)) 1) :=
    (fun ω : sphere (0 : Euclidean (n + 1)) 1 => (ω : Euclidean (n + 1))) ⁻¹'
      ball (-euclideanSuccLast n) (2 * ε)
  have hsubset : transverseSphereCap n ε ⊆ A ∪ B := by
    simpa only [A, B] using transverseSphereCap_subset_pole_caps n (ε := ε)
  have hA : (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)) A ≤
      C * ENNReal.ofReal ((2 * ε) ^ n) := by
    simpa only [Nat.add_sub_cancel] using hcap (euclideanSuccLast n) (2 * ε)
      (by positivity)
  have hB : (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)) B ≤
      C * ENNReal.ofReal ((2 * ε) ^ n) := by
    simpa only [Nat.add_sub_cancel] using hcap (-euclideanSuccLast n) (2 * ε)
      (by positivity)
  have hpow : ENNReal.ofReal ((2 * ε) ^ n) =
      (2 : ENNReal) ^ n * ENNReal.ofReal (ε ^ n) := by
    rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg (by norm_num) _),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_pow hε]
    norm_num
  calc
    (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
        (transverseSphereCap n ε) ≤
        (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)) (A ∪ B) :=
      measure_mono hsubset
    _ ≤ (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)) A +
          (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)) B :=
      measure_union_le A B
    _ ≤ C * ENNReal.ofReal ((2 * ε) ^ n) + C * ENNReal.ofReal ((2 * ε) ^ n) :=
      add_le_add hA hB
    _ = D * ENNReal.ofReal (ε ^ n) := by
      rw [hpow]
      dsimp [D]
      ring

/-- Transverse coordinates scale in the expected way along a radial ray. -/
theorem norm_transverseCoordinates_smul
    (n : ℕ) (ρ : ℝ) (ω : Euclidean (n + 1)) :
    ‖(euclideanSuccCoordinates n (ρ • ω)).1‖ =
      |ρ| * ‖(euclideanSuccCoordinates n ω).1‖ := by
  have hcoords := euclideanSuccCoordinates_add_smul n
    (0 : Euclidean (n + 1)) ω ρ
  rw [show (0 : Euclidean (n + 1)) + ρ • ω = ρ • ω by simp] at hcoords
  have hzero : (euclideanSuccCoordinates n (0 : Euclidean (n + 1))).1 = 0 := by
    ext i
    simp [euclideanSuccCoordinates, PiLp.toLp_apply]
  rw [hcoords]
  rw [hzero, zero_add, norm_smul, Real.norm_eq_abs]

/-- A short squared-radius interval at radii at least one is contained in
the corresponding ordinary radial interval. -/
theorem radial_mem_Ioo_of_abs_sq_sub_lt
    {ρ r Δ : ℝ} (hρ : 0 ≤ ρ) (hr : 1 ≤ r)
    (h : |ρ ^ 2 - r ^ 2| < Δ) :
    ρ ∈ Ioo (r - Δ) (r + Δ) := by
  have hΔ : 0 < Δ := lt_of_le_of_lt (abs_nonneg _) h
  rw [mem_Ioo]
  constructor <;> by_contra hbad
  · have hle : ρ ≤ r - Δ := le_of_not_gt hbad
    have hfac : Δ ≤ r ^ 2 - ρ ^ 2 := by
      nlinarith [sq_nonneg (r - ρ), sq_nonneg (r + ρ)]
    have : Δ ≤ |ρ ^ 2 - r ^ 2| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    linarith
  · have hle : r + Δ ≤ ρ := le_of_not_gt hbad
    have hfac : Δ ≤ ρ ^ 2 - r ^ 2 := by
      nlinarith [sq_nonneg (ρ - r), sq_nonneg (ρ + r)]
    have : Δ ≤ |ρ ^ 2 - r ^ 2| := by
      rw [abs_of_nonneg (by linarith)]
      exact hfac
    linarith

/-- The radial power measure of a short positive interval is controlled by
the interval length times the largest radial density. -/
theorem volumeIoiPow_preimage_Ioo_le
    (n : ℕ) {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : lo ≤ hi) :
    (Measure.volumeIoiPow n) (Subtype.val ⁻¹' Ioo lo hi) ≤
      ENNReal.ofReal (hi ^ n) * ENNReal.ofReal (hi - lo) := by
  let J : Set ℝ := Ioo lo hi
  let S : Set (Ioi (0 : ℝ)) := Subtype.val ⁻¹' J
  have hJ : MeasurableSet J := by
    dsimp [J]
    exact measurableSet_Ioo
  have hS : MeasurableSet S := by
    exact hJ.preimage measurable_subtype_coe
  have hJpos : J ⊆ Ioi (0 : ℝ) := by
    intro ρ hρ
    exact lt_of_le_of_lt hlo hρ.1
  have hS_eq : S = Subtype.val ⁻¹' J := rfl
  let F : ℝ → ENNReal := J.indicator (fun _ => (1 : ENNReal))
  have hF : Measurable F := by
    exact (measurable_indicator_const_iff 1).mpr hJ
  have hmeasure :
      (Measure.volumeIoiPow n) S =
        ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ ^ n * F ρ := by
    calc
      (Measure.volumeIoiPow n) S =
          ∫⁻ ρ : Ioi (0 : ℝ), S.indicator (fun _ => (1 : ENNReal)) ρ ∂
            Measure.volumeIoiPow n := by
        rw [lintegral_indicator_const hS]
        simp
      _ = ∫⁻ ρ : Ioi (0 : ℝ), F ρ.1 ∂Measure.volumeIoiPow n := by
        apply lintegral_congr
        intro ρ
        by_cases hρ : ρ.1 ∈ J
        · have hρS : ρ ∈ S := hρ
          simp [F, hρ, hρS]
        · have hρS : ρ ∉ S := hρ
          simp [F, hρ, hρS]
      _ = ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ ^ n * F ρ :=
        lintegral_volumeIoiPow n F hF
  have hpoint (ρ : ℝ) :
      ENNReal.ofReal ρ ^ n * F ρ ≤ ENNReal.ofReal (hi ^ n) * F ρ := by
    by_cases hρ : ρ ∈ J
    · have hFρ : F ρ = 1 := by simp [F, hρ]
      rw [hFρ, mul_one, mul_one]
      have hρnonneg : 0 ≤ ρ := (hJpos hρ).le
      rw [← ENNReal.ofReal_pow hρnonneg]
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left₀ hρnonneg hρ.2.le n
    · have hFρ : F ρ = 0 := by simp [F, hρ]
      rw [hFρ, mul_zero, mul_zero]
  have hupper :
      (∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ ^ n * F ρ) ≤
        ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (hi ^ n) * F ρ := by
    apply lintegral_mono
    intro ρ
    exact hpoint ρ
  have hconst :
      (∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (hi ^ n) * F ρ) =
        ENNReal.ofReal (hi ^ n) * ENNReal.ofReal (hi - lo) := by
    rw [show (fun ρ : ℝ => ENNReal.ofReal (hi ^ n) * F ρ) =
      J.indicator (fun _ => ENNReal.ofReal (hi ^ n)) by
        funext ρ
        by_cases hρ : ρ ∈ J <;> simp [F, hρ]]
    rw [lintegral_indicator hJ]
    change ∫⁻ ρ : ℝ, ENNReal.ofReal (hi ^ n) ∂
      (volume.restrict (Ioi (0 : ℝ))).restrict J = _
    rw [Measure.restrict_restrict hJ]
    simp only [Set.inter_eq_left.mpr hJpos]
    rw [setLIntegral_const, Real.volume_Ioo]
  change (Measure.volumeIoiPow n) S ≤ _
  rw [hmeasure]
  exact hupper.trans_eq hconst

/-- Measurability of the transverse cap in the polar-coordinate argument. -/
theorem measurableSet_transverseSphereCap (n : ℕ) (ε : ℝ) :
    MeasurableSet (transverseSphereCap n ε) := by
  have hcoord : Measurable (fun ω : sphere (0 : Euclidean (n + 1)) 1 =>
      (euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1) :=
    ((contDiff_euclideanSuccCoordinates n).fst.continuous.measurable).comp
      continuous_subtype_val.measurable
  change MeasurableSet {ω : sphere (0 : Euclidean (n + 1)) 1 |
    ‖(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖ < ε}
  exact measurableSet_lt (measurable_norm.comp hcoord) measurable_const

/-- Under polar coordinates, a squared-radius cap tube is contained in a
transverse cap times a short radial interval. -/
theorem polar_mem_transverseCap_radialInterval_of_mem_squaredSphericalCapTube
    {n : ℕ} {r Δ σ : ℝ}
    (hr : 1 ≤ r) (hΔhalf : Δ ≤ 1 / 2)
    (ω : sphere (0 : Euclidean (n + 1)) 1) (ρ : Ioi (0 : ℝ))
    (hmem : ρ.1 • (ω : Euclidean (n + 1)) ∈
      squaredSphericalCapTube n r Δ σ) :
    ω ∈ transverseSphereCap n (2 * σ) ∧
      ρ ∈ Subtype.val ⁻¹' Ioo (r - Δ) (r + Δ) := by
  have hωnorm : ‖(ω : Euclidean (n + 1))‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using ω.property
  have hnorm : ‖ρ.1 • (ω : Euclidean (n + 1))‖ = ρ.1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ρ.2, hωnorm, mul_one]
  change |‖ρ.1 • (ω : Euclidean (n + 1))‖ ^ 2 - r ^ 2| < Δ ∧
    ‖(euclideanSuccCoordinates n (ρ.1 • (ω : Euclidean (n + 1)))).1‖ < σ at hmem
  have hradial : |ρ.1 ^ 2 - r ^ 2| < Δ := by
    simpa only [hnorm] using hmem.1
  have hρI : ρ.1 ∈ Ioo (r - Δ) (r + Δ) :=
    radial_mem_Ioo_of_abs_sq_sub_lt ρ.2.le hr hradial
  have hρhalf : (1 / 2 : ℝ) ≤ ρ.1 := by
    linarith [hρI.1]
  have hcoord : ρ.1 * ‖(euclideanSuccCoordinates n
      (ω : Euclidean (n + 1))).1‖ < σ := by
    have hρpos : 0 < ρ.1 := ρ.2
    rw [← abs_of_pos hρpos,
      ← norm_transverseCoordinates_smul n ρ.1 (ω : Euclidean (n + 1))]
    exact hmem.2
  have hsmall : (1 / 2 : ℝ) * ‖(euclideanSuccCoordinates n
      (ω : Euclidean (n + 1))).1‖ < σ := by
    calc
      (1 / 2 : ℝ) * ‖(euclideanSuccCoordinates n
          (ω : Euclidean (n + 1))).1‖ ≤
          ρ.1 * ‖(euclideanSuccCoordinates n
            (ω : Euclidean (n + 1))).1‖ :=
        mul_le_mul_of_nonneg_right hρhalf (norm_nonneg _)
      _ < σ := hcoord
  constructor
  · calc
      ‖(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖ =
          2 * ((1 / 2 : ℝ) *
            ‖(euclideanSuccCoordinates n (ω : Euclidean (n + 1))).1‖) := by ring
      _ < 2 * σ := mul_lt_mul_of_pos_left hsmall (by norm_num)
  · exact hρI

/-- Polar coordinates bound the volume of a curved cap tube by the product
of its angular cap measure and radial power measure. -/
theorem volume_squaredSphericalCapTube_le_polar_product
    {n : ℕ} {r Δ σ : ℝ}
    (hr : 1 ≤ r) (hΔhalf : Δ ≤ 1 / 2) :
    volume (squaredSphericalCapTube n r Δ σ) ≤
      (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
          (transverseSphereCap n (2 * σ)) *
        (Measure.volumeIoiPow n)
          (Subtype.val ⁻¹' Ioo (r - Δ) (r + Δ)) := by
  let A : Set (Euclidean (n + 1)) := squaredSphericalCapTube n r Δ σ
  let S : Set (sphere (0 : Euclidean (n + 1)) 1) := transverseSphereCap n (2 * σ)
  let I : Set (Ioi (0 : ℝ)) := Subtype.val ⁻¹' Ioo (r - Δ) (r + Δ)
  have hA : MeasurableSet A := measurableSet_squaredSphericalCapTube n r Δ σ
  have hS : MeasurableSet S := measurableSet_transverseSphereCap n (2 * σ)
  have hI : MeasurableSet I := measurableSet_Ioo.preimage measurable_subtype_coe
  have hindicator (p : sphere (0 : Euclidean (n + 1)) 1 × Ioi (0 : ℝ)) :
      A.indicator (fun _ => (1 : ENNReal))
          (p.2.1 • (p.1 : Euclidean (n + 1))) ≤
        (S ×ˢ I).indicator (fun _ => (1 : ENNReal)) p := by
    by_cases hp : p.2.1 • (p.1 : Euclidean (n + 1)) ∈ A
    · have hp' : p.1 ∈ S ∧ p.2 ∈ I := by
        exact polar_mem_transverseCap_radialInterval_of_mem_squaredSphericalCapTube
          hr hΔhalf p.1 p.2 hp
      have hp'' : p ∈ S ×ˢ I := hp'
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp'']
    · rw [Set.indicator_of_notMem hp]
      exact zero_le
  calc
    volume (squaredSphericalCapTube n r Δ σ) =
        ∫⁻ x : Euclidean (n + 1), A.indicator (fun _ => (1 : ENNReal)) x := by
          rw [lintegral_indicator_const hA]
          simp [A]
    _ = ∫⁻ p : sphere (0 : Euclidean (n + 1)) 1 × Ioi (0 : ℝ),
          A.indicator (fun _ => (1 : ENNReal))
            (p.2.1 • (p.1 : Euclidean (n + 1))) ∂
          ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)).prod
            (Measure.volumeIoiPow n)) := by
          simpa only [Nat.add_sub_cancel] using
            (Auto.Spherical.CoordinateIntegration.lintegral_polar_unitSurfaceMeasure
              (d := n + 1) (by omega)
              (A.indicator (fun _ => (1 : ENNReal))))
    _ ≤ ∫⁻ p : sphere (0 : Euclidean (n + 1)) 1 × Ioi (0 : ℝ),
          (S ×ˢ I).indicator (fun _ => (1 : ENNReal)) p ∂
          ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)).prod
            (Measure.volumeIoiPow n)) :=
      lintegral_mono hindicator
    _ = ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)).prod
          (Measure.volumeIoiPow n)) (S ×ˢ I) := by
      rw [lintegral_indicator_const (hS.prod hI)]
      simp
    _ = (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)) S *
          (Measure.volumeIoiPow n) I :=
      MeasureTheory.Measure.prod_prod S I

/-- Uniform cap-tube volume bound at unit radii.  The constant depends only
on the transverse dimension. -/
theorem exists_volume_squaredSphericalCapTube_le_power (n : ℕ) :
    ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ r Δ σ : ℝ,
      1 ≤ r → r ≤ 2 → 0 < Δ → Δ ≤ 1 / 2 → 0 ≤ σ →
      volume (squaredSphericalCapTube n r Δ σ) ≤
        C * ENNReal.ofReal Δ * ENNReal.ofReal (σ ^ n) := by
  obtain ⟨C₀, hC₀top, hcap⟩ :=
    exists_unitSurfaceMeasure_transverseSphereCap_le_power n
  let C : ENNReal := C₀ * (2 : ENNReal) ^ n * ENNReal.ofReal ((3 : ℝ) ^ n) * 2
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hC₀top (ENNReal.pow_ne_top (by norm_num)))
        ENNReal.ofReal_ne_top)
      (by norm_num)
  intro r Δ σ hr hrtwo hΔ hΔhalf hσ
  have hsurf0 := hcap (2 * σ) (by positivity)
  have hsurf :
      (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
          (transverseSphereCap n (2 * σ)) ≤
        (C₀ * (2 : ENNReal) ^ n) * ENNReal.ofReal (σ ^ n) := by
    calc
      (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
          (transverseSphereCap n (2 * σ)) ≤
          C₀ * ENNReal.ofReal ((2 * σ) ^ n) := hsurf0
      _ = (C₀ * (2 : ENNReal) ^ n) * ENNReal.ofReal (σ ^ n) := by
        have hpow : ENNReal.ofReal ((2 * σ) ^ n) =
            (2 : ENNReal) ^ n * ENNReal.ofReal (σ ^ n) := by
          rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg (by norm_num) _),
            ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_pow hσ]
          norm_num
        rw [hpow]
        ring
  have hradial0 := volumeIoiPow_preimage_Ioo_le n
    (lo := r - Δ) (hi := r + Δ)
    (by linarith) (by linarith)
  have hhi_nonneg : 0 ≤ r + Δ := by linarith
  have hhi_le_three : r + Δ ≤ 3 := by linarith
  have hradialCoeff : ENNReal.ofReal ((r + Δ) ^ n) ≤
      ENNReal.ofReal ((3 : ℝ) ^ n) := by
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ hhi_nonneg hhi_le_three n
  have hlength : ENNReal.ofReal ((r + Δ) - (r - Δ)) =
      2 * ENNReal.ofReal Δ := by
    rw [show (r + Δ) - (r - Δ) = 2 * Δ by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hradial :
      (Measure.volumeIoiPow n) (Subtype.val ⁻¹' Ioo (r - Δ) (r + Δ)) ≤
        ENNReal.ofReal ((3 : ℝ) ^ n) * (2 * ENNReal.ofReal Δ) := by
    calc
      (Measure.volumeIoiPow n) (Subtype.val ⁻¹' Ioo (r - Δ) (r + Δ)) ≤
          ENNReal.ofReal ((r + Δ) ^ n) *
            ENNReal.ofReal ((r + Δ) - (r - Δ)) := hradial0
      _ = ENNReal.ofReal ((r + Δ) ^ n) * (2 * ENNReal.ofReal Δ) := by
        rw [hlength]
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ n) * (2 * ENNReal.ofReal Δ) := by
        simpa only [mul_comm] using
          (mul_le_mul_right hradialCoeff (2 * ENNReal.ofReal Δ))
  calc
    volume (squaredSphericalCapTube n r Δ σ) ≤
        (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
            (transverseSphereCap n (2 * σ)) *
          (Measure.volumeIoiPow n)
            (Subtype.val ⁻¹' Ioo (r - Δ) (r + Δ)) :=
      volume_squaredSphericalCapTube_le_polar_product hr hΔhalf
    _ ≤ ((C₀ * (2 : ENNReal) ^ n) * ENNReal.ofReal (σ ^ n)) *
          (ENNReal.ofReal ((3 : ℝ) ^ n) * (2 * ENNReal.ofReal Δ)) := by
      gcongr
    _ = C * ENNReal.ofReal Δ * ENNReal.ofReal (σ ^ n) := by
      dsimp [C]
      ring

/-- A point in a small Euclidean ball about the pole has polar direction in
the corresponding spherical cap and radial coordinate in a short interval. -/
theorem polar_mem_poleCap_radialInterval_of_mem_ball
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (ω : sphere (0 : Euclidean (n + 1)) 1) (ρ : Ioi (0 : ℝ))
    (hmem : ρ.1 • (ω : Euclidean (n + 1)) ∈
      ball (euclideanSuccLast n) (ε / 4)) :
    ω ∈ ball (euclideanSuccLastSphere n) ε ∧
      ρ ∈ Subtype.val ⁻¹' Ioo (1 - ε / 4) (1 + ε / 4) := by
  have hωnorm : ‖(ω : Euclidean (n + 1))‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using ω.property
  have hρnorm : ‖ρ.1 • (ω : Euclidean (n + 1))‖ = ρ.1 := by
    rw [norm_smul, Real.norm_eq_abs]
    have hρpos : 0 < ρ.1 := ρ.2
    rw [abs_of_pos hρpos, hωnorm, mul_one]
  have hz : ‖euclideanSuccLast n‖ = 1 := norm_euclideanSuccLast n
  have hdist : dist (ρ.1 • (ω : Euclidean (n + 1))) (euclideanSuccLast n) < ε / 4 :=
    hmem
  have hrad : |ρ.1 - 1| < ε / 4 := by
    calc
      |ρ.1 - 1| = |‖ρ.1 • (ω : Euclidean (n + 1))‖ -
          ‖euclideanSuccLast n‖| := by rw [hρnorm, hz]
      _ ≤ ‖ρ.1 • (ω : Euclidean (n + 1)) - euclideanSuccLast n‖ :=
        abs_norm_sub_norm_le _ _
      _ = dist (ρ.1 • (ω : Euclidean (n + 1))) (euclideanSuccLast n) := by
        rw [dist_eq_norm]
      _ < ε / 4 := hmem
  constructor
  · change dist (ω : Euclidean (n + 1)) (euclideanSuccLast n) < ε
    calc
      dist (ω : Euclidean (n + 1)) (euclideanSuccLast n) ≤
          dist (ω : Euclidean (n + 1)) (ρ.1 • (ω : Euclidean (n + 1))) +
            dist (ρ.1 • (ω : Euclidean (n + 1))) (euclideanSuccLast n) :=
        dist_triangle _ _ _
      _ = |1 - ρ.1| +
            dist (ρ.1 • (ω : Euclidean (n + 1))) (euclideanSuccLast n) := by
        congr 1
        rw [dist_eq_norm]
        have hsub : (ω : Euclidean (n + 1)) - ρ.1 •
            (ω : Euclidean (n + 1)) = (1 - ρ.1) • (ω : Euclidean (n + 1)) := by
          module
        rw [hsub, norm_smul, Real.norm_eq_abs, hωnorm, mul_one]
      _ = |ρ.1 - 1| +
            dist (ρ.1 • (ω : Euclidean (n + 1))) (euclideanSuccLast n) := by
        rw [abs_sub_comm]
      _ < ε := by linarith [hrad, hdist]
  · rcases abs_lt.mp hrad with ⟨hl, hu⟩
    constructor <;> linarith

/-- The polar image of a small Euclidean pole ball is contained in the cap
times radial interval; hence its volume lower-bounds the product measure. -/
theorem volume_poleBall_le_unitSurfaceMeasure_poleCap_mul_radial
    {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    volume (ball (euclideanSuccLast n) (ε / 4)) ≤
      (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
          (ball (euclideanSuccLastSphere n) ε) *
        (Measure.volumeIoiPow n)
          (Subtype.val ⁻¹' Ioo (1 - ε / 4) (1 + ε / 4)) := by
  let B : Set (Euclidean (n + 1)) := ball (euclideanSuccLast n) (ε / 4)
  let S : Set (sphere (0 : Euclidean (n + 1)) 1) :=
    ball (euclideanSuccLastSphere n) ε
  let I : Set (Ioi (0 : ℝ)) := Subtype.val ⁻¹' Ioo (1 - ε / 4) (1 + ε / 4)
  have hB : MeasurableSet B := isOpen_ball.measurableSet
  have hS : MeasurableSet S := isOpen_ball.measurableSet
  have hI : MeasurableSet I := measurableSet_Ioo.preimage measurable_subtype_coe
  have hindicator (p : sphere (0 : Euclidean (n + 1)) 1 × Ioi (0 : ℝ)) :
      B.indicator (fun _ => (1 : ENNReal))
          (p.2.1 • (p.1 : Euclidean (n + 1))) ≤
        (S ×ˢ I).indicator (fun _ => (1 : ENNReal)) p := by
    by_cases hp : p.2.1 • (p.1 : Euclidean (n + 1)) ∈ B
    · have hp' : p.1 ∈ S ∧ p.2 ∈ I := by
        exact polar_mem_poleCap_radialInterval_of_mem_ball hε p.1 p.2 hp
      have hp'' : p ∈ S ×ˢ I := hp'
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp'']
    · rw [Set.indicator_of_notMem hp]
      exact zero_le
  calc
    volume (ball (euclideanSuccLast n) (ε / 4)) =
        ∫⁻ x : Euclidean (n + 1), B.indicator (fun _ => (1 : ENNReal)) x := by
          rw [lintegral_indicator_const hB]
          simp [B]
    _ = ∫⁻ p : sphere (0 : Euclidean (n + 1)) 1 × Ioi (0 : ℝ),
          B.indicator (fun _ => (1 : ENNReal))
            (p.2.1 • (p.1 : Euclidean (n + 1))) ∂
          ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)).prod
            (Measure.volumeIoiPow n)) := by
          simpa only [Nat.add_sub_cancel] using
            (Auto.Spherical.CoordinateIntegration.lintegral_polar_unitSurfaceMeasure
              (d := n + 1) (by omega)
              (B.indicator (fun _ => (1 : ENNReal))))
    _ ≤ ∫⁻ p : sphere (0 : Euclidean (n + 1)) 1 × Ioi (0 : ℝ),
          (S ×ˢ I).indicator (fun _ => (1 : ENNReal)) p ∂
          ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)).prod
            (Measure.volumeIoiPow n)) :=
      lintegral_mono hindicator
    _ = ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)).prod
          (Measure.volumeIoiPow n)) (S ×ˢ I) := by
      rw [lintegral_indicator_const (hS.prod hI)]
      simp
    _ = (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)) S *
          (Measure.volumeIoiPow n) I :=
      MeasureTheory.Measure.prod_prod S I

/-- An explicit lower bound for the pole cap after dividing by a controlled
short radial interval. -/
theorem poleCap_volume_div_radialCoefficient_le_unitSurfaceMeasure
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    volume (ball (euclideanSuccLast n) (ε / 4)) /
        (ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (ε / 2)) ≤
      (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
        (ball (euclideanSuccLastSphere n) ε) := by
  have hradial0 := volumeIoiPow_preimage_Ioo_le n
    (lo := 1 - ε / 4) (hi := 1 + ε / 4)
    (by linarith) (by linarith)
  have hhi_nonneg : 0 ≤ 1 + ε / 4 := by linarith
  have hhi_le_two : 1 + ε / 4 ≤ 2 := by linarith
  have hcoeff : ENNReal.ofReal ((1 + ε / 4) ^ n) ≤
      ENNReal.ofReal ((2 : ℝ) ^ n) := by
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ hhi_nonneg hhi_le_two n
  have hlength : ENNReal.ofReal ((1 + ε / 4) - (1 - ε / 4)) =
      ENNReal.ofReal (ε / 2) := by ring_nf
  have hradial :
      (Measure.volumeIoiPow n) (Subtype.val ⁻¹' Ioo (1 - ε / 4) (1 + ε / 4)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (ε / 2) := by
    calc
      (Measure.volumeIoiPow n) (Subtype.val ⁻¹' Ioo (1 - ε / 4) (1 + ε / 4)) ≤
          ENNReal.ofReal ((1 + ε / 4) ^ n) *
            ENNReal.ofReal ((1 + ε / 4) - (1 - ε / 4)) := hradial0
      _ = ENNReal.ofReal ((1 + ε / 4) ^ n) * ENNReal.ofReal (ε / 2) := by
        rw [hlength]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (ε / 2) := by
        simpa only [mul_comm] using
          (mul_le_mul_right hcoeff (ENNReal.ofReal (ε / 2)))
  have hcone := volume_poleBall_le_unitSurfaceMeasure_poleCap_mul_radial
    (n := n) hε
  have hmul : volume (ball (euclideanSuccLast n) (ε / 4)) ≤
      (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
          (ball (euclideanSuccLastSphere n) ε) *
        (ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (ε / 2)) := by
    calc
      volume (ball (euclideanSuccLast n) (ε / 4)) ≤
          (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
            (ball (euclideanSuccLastSphere n) ε) *
          (Measure.volumeIoiPow n)
            (Subtype.val ⁻¹' Ioo (1 - ε / 4) (1 + ε / 4)) := hcone
      _ ≤ (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
            (ball (euclideanSuccLastSphere n) ε) *
          (ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (ε / 2)) :=
        by
          simpa only [mul_comm] using
            (mul_le_mul_left hradial
              ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
                (ball (euclideanSuccLastSphere n) ε)))
  refine (ENNReal.div_le_iff ?_ ?_).2 hmul
  · exact mul_ne_zero
      (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) _)).ne'
      (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- A genuine power lower bound for a small spherical cap about the positive
pole.  It is derived directly from the polar-coordinate formula, so no
regularity assertion about surface measure is used as an additional axiom. -/
theorem exists_unitSurfaceMeasure_poleCap_ge_power (n : ℕ) :
    ∃ c : ENNReal, 0 < c ∧ c ≠ ⊤ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      c * ENNReal.ofReal (ε ^ n) ≤
        (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
          (ball (euclideanSuccLastSphere n) ε) := by
  let V : ENNReal := volume (ball (euclideanSuccLast n) (1 / 4))
  let A : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ n)
  let B : ENNReal := ENNReal.ofReal (1 / 2)
  let K : ENNReal := A * B
  let c : ENNReal := V / K
  have hV0 : V ≠ 0 := by
    dsimp [V]
    exact (Metric.measure_ball_pos volume (euclideanSuccLast n) (by norm_num)).ne'
  have hVtop : V ≠ ⊤ := by
    dsimp [V]
    exact (measure_ball_lt_top (μ := volume) (x := euclideanSuccLast n)
      (r := (1 / 4 : ℝ))).ne
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) _)).ne'
  have hB0 : B ≠ 0 := by
    dsimp [B]
    exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hK0 : K ≠ 0 := mul_ne_zero hA0 hB0
  have hKtop : K ≠ ⊤ := by
    dsimp [K, A, B]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨c, ENNReal.div_pos hV0 hKtop, ENNReal.div_ne_top hVtop hK0, ?_⟩
  intro ε hε hεhalf
  have hA_top : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.ofReal_ne_top
  have hE0 : ENNReal.ofReal ε ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hε).ne'
  have hD0 : A * ENNReal.ofReal (ε / 2) ≠ 0 := by
    apply mul_ne_zero hA0
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hDtop : A * ENNReal.ofReal (ε / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top hA_top ENNReal.ofReal_ne_top
  have hdenom : A * ENNReal.ofReal (ε / 2) = K * ENNReal.ofReal ε := by
    have hhalf : ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε * B := by
      rw [show ε / 2 = ε * (1 / 2) by ring,
        ENNReal.ofReal_mul hε.le]
    rw [hhalf]
    dsimp [K]
    ring
  have hvol : volume (ball (euclideanSuccLast n) (ε / 4)) =
      (ENNReal.ofReal ε) ^ (n + 1) * V := by
    dsimp [V]
    rw [Measure.addHaar_ball_of_pos volume (euclideanSuccLast n) (by positivity),
      Measure.addHaar_ball_of_pos volume (euclideanSuccLast n) (by norm_num)]
    rw [finrank_euclideanSpace_fin]
    rw [show (ε / 4) ^ (n + 1) = ε ^ (n + 1) * (1 / 4) ^ (n + 1) by ring]
    rw [ENNReal.ofReal_mul (pow_nonneg hε.le _),
      ENNReal.ofReal_pow hε.le,
      ENNReal.ofReal_pow (by positivity)]
    ring
  have hscaled : c * ENNReal.ofReal (ε ^ n) ≤
      volume (ball (euclideanSuccLast n) (ε / 4)) /
        (A * ENNReal.ofReal (ε / 2)) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hD0) (Or.inl hDtop)).2
    rw [hvol, hdenom, ENNReal.ofReal_pow hε.le]
    dsimp [c]
    calc
      (V / K * ENNReal.ofReal ε ^ n) * (K * ENNReal.ofReal ε) =
          (V / K * K) * (ENNReal.ofReal ε ^ n * ENNReal.ofReal ε) := by ring
      _ = V * ENNReal.ofReal ε ^ (n + 1) := by
          rw [ENNReal.div_mul_cancel hK0 hKtop, ← pow_succ]
      _ ≤ ENNReal.ofReal ε ^ (n + 1) * V := by
        simpa only [mul_comm] using
          (le_refl (V * ENNReal.ofReal ε ^ (n + 1)))
  calc
    c * ENNReal.ofReal (ε ^ n) ≤
        volume (ball (euclideanSuccLast n) (ε / 4)) /
          (A * ENNReal.ofReal (ε / 2)) := hscaled
    _ ≤ (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
          (ball (euclideanSuccLastSphere n) ε) := by
      exact poleCap_volume_div_radialCoefficient_le_unitSurfaceMeasure n hε hεhalf

end

end Auto.Spherical.FractalDilations.ClusterTubeVolume
end Former_ClusterTubeVolume

/- ===== Former FractalDilations/AnnulusDominance.lean ===== -/
section Former_AnnulusDominance

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.AnnulusGeometry
open Auto.Spherical.FractalDilations.AnnulusMass
open Auto.Spherical.FractalDilations.AssouadSpectrum
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Maximal
open Auto.Spherical.FractalDilations.Minkowski
open Auto.Spherical.FractalDilations.SeparatedPacking
open Auto.Spherical.SurfaceCore







/-!
# Pointwise domination of a disjoint annular sum

At a point of space, separated-radius averages of a small ball bump have at
most one nonzero summand.  For nonnegative real data their finite sum is
therefore pointwise dominated by the restricted spherical maximal function.
-/

namespace Auto.Spherical.FractalDilations.AnnulusDominance

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- A nonnegative finite sum with pairwise disjoint supports is bounded by
any common pointwise upper bound for its summands. -/
theorem Finset.sum_le_of_nonneg_of_pairwiseDisjoint_support
    {ι X : Type*} (s : Finset ι) (g : ι → X → ℝ)
    (x : X) (M : ℝ) (hM : 0 ≤ M)
    (hdisjoint : (↑s : Set ι).PairwiseDisjoint (fun i => Function.support (g i)))
    (hupper : ∀ i ∈ s, g i x ≤ M) :
    (∑ i ∈ s, g i x) ≤ M := by
  classical
  by_cases hsome : ∃ i, i ∈ s ∧ g i x ≠ 0
  · obtain ⟨i, hi, hix⟩ := hsome
    have hzero : ∀ j ∈ s, j ≠ i → g j x = 0 := by
      intro j hj hji
      by_contra hjx
      have hdj : Disjoint (Function.support (g i)) (Function.support (g j)) :=
        hdisjoint hi hj (Ne.symm hji)
      have hxi : x ∈ Function.support (g i) := Function.mem_support.mpr hix
      have hxj : x ∈ Function.support (g j) := Function.mem_support.mpr hjx
      exact (Set.disjoint_left.mp hdj hxi) hxj
    rw [Finset.sum_eq_single i hzero (fun hni => False.elim (hni hi))]
    exact hupper i hi
  · have hzero : ∀ i ∈ s, g i x = 0 := by
      intro i hi
      by_contra hix
      exact hsome ⟨i, hi, hix⟩
    rw [Finset.sum_eq_zero hzero]
    exact hM

/-- Strictly separated radii give pairwise disjoint supports for the real
parts of averages of a bump supported in the ball of radius `2R`. -/
theorem strictlySeparated_pairwiseDisjoint_support_re_normalizedSphericalAverage
    {d : ℕ} (hd : 0 < d) (f : Euclidean d → ℂ) {R δ : ℝ} (s : Finset ℝ)
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (hsep : StrictlySeparated s δ) (hRδ : 4 * R ≤ δ)
    (hsnonneg : ∀ r ∈ s, 0 ≤ r) :
    (↑s : Set ℝ).PairwiseDisjoint (fun r =>
      Function.support (fun x : Euclidean d =>
        (normalizedSphericalAverage d f r x).re)) := by
  intro r hr t ht hrt
  have hradial : Disjoint (radialAnnulus d r (2 * R)) (radialAnnulus d t (2 * R)) := by
    apply disjoint_radialAnnulus_of_two_mul_le_abs_sub
    calc
      2 * (2 * R) = 4 * R := by ring
      _ ≤ δ := hRδ
      _ ≤ |r - t| := (hsep hr ht hrt).le
  have hsup_r : Function.support (fun x : Euclidean d =>
      (normalizedSphericalAverage d f r x).re) ⊆ radialAnnulus d r (2 * R) := by
    have hbase := support_normalizedSphericalAverage_subset_radialAnnulus
      (r := r) hd f hzero
    rw [abs_of_nonneg (hsnonneg r hr)] at hbase
    intro x hx
    apply hbase
    change normalizedSphericalAverage d f r x ≠ 0
    intro hzero_avg
    apply hx
    change (normalizedSphericalAverage d f r x).re = 0
    rw [hzero_avg]
    rfl
  have hsup_t : Function.support (fun x : Euclidean d =>
      (normalizedSphericalAverage d f t x).re) ⊆ radialAnnulus d t (2 * R) := by
    have hbase := support_normalizedSphericalAverage_subset_radialAnnulus
      (r := t) hd f hzero
    rw [abs_of_nonneg (hsnonneg t ht)] at hbase
    intro x hx
    apply hbase
    change normalizedSphericalAverage d f t x ≠ 0
    intro hzero_avg
    apply hx
    change (normalizedSphericalAverage d f t x).re = 0
    rw [hzero_avg]
    rfl
  exact hradial.mono hsup_r hsup_t

/-- A fixed radius in the dilation set dominates the real coordinate of its
normalized average through the real-valued restricted maximal function. -/
theorem re_normalizedSphericalAverage_le_fractalSphericalMaximalReal
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hEpos : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {r : ℝ} (hr : r ∈ E)
    (x : Euclidean d) :
    (normalizedSphericalAverage d (f : Euclidean d → ℂ) r x).re ≤
      fractalSphericalMaximalReal d E f x := by
  have hraw := normalizedSphericalAverage_le_fractalSphericalMaximal E
    (f : Euclidean d → ℂ) hr x
  have htop := fractalSphericalMaximal_ne_top hd E hEpos f x
  have hnorm : ‖normalizedSphericalAverage d (f : Euclidean d → ℂ) r x‖ ≤
      fractalSphericalMaximalReal d E f x := by
    unfold fractalSphericalMaximalReal
    have hto := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).mpr hraw
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using hto
  exact (Complex.re_le_norm _).trans hnorm

/-- The disjoint annular sum of averages of a real nonnegative bump is
pointwise dominated by the maximal function over every set containing the
chosen finite family of radii. -/
theorem annulusAverageSum_le_fractalSphericalMaximalReal
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hEpos : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {R δ : ℝ} (s : Finset ℝ)
    (hsE : (↑s : Set ℝ) ⊆ E)
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (hsep : StrictlySeparated s δ) (hRδ : 4 * R ≤ δ) :
    ∀ x : Euclidean d, annulusAverageSum d (f : Euclidean d → ℂ) s x ≤
      fractalSphericalMaximalReal d E f x := by
  intro x
  let g : ℝ → Euclidean d → ℝ := fun r y =>
    (normalizedSphericalAverage d (f : Euclidean d → ℂ) r y).re
  have hsnonneg : ∀ r ∈ s, 0 ≤ r := by
    intro r hr
    exact (hEpos (hsE hr)).le
  have hdisjoint : (↑s : Set ℝ).PairwiseDisjoint (fun r => Function.support (g r)) := by
    exact strictlySeparated_pairwiseDisjoint_support_re_normalizedSphericalAverage
      hd (f : Euclidean d → ℂ) s hzero hsep hRδ hsnonneg
  have hterm_upper : ∀ r ∈ s, g r x ≤ fractalSphericalMaximalReal d E f x := by
    intro r hr
    exact re_normalizedSphericalAverage_le_fractalSphericalMaximalReal hd E hEpos f
      (hsE hr) x
  have hmax_nonneg : 0 ≤ fractalSphericalMaximalReal d E f x := by
    unfold fractalSphericalMaximalReal
    exact ENNReal.toReal_nonneg
  change (∑ r ∈ s, g r x) ≤ fractalSphericalMaximalReal d E f x
  exact Finset.sum_le_of_nonneg_of_pairwiseDisjoint_support s g x
    (fractalSphericalMaximalReal d E f x) hmax_nonneg hdisjoint hterm_upper

end

end Auto.Spherical.FractalDilations.AnnulusDominance
end Former_AnnulusDominance

/- ===== Former FractalDilations/AnnulusLowerBound.lean ===== -/
section Former_AnnulusLowerBound

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.AnnulusBump
open Auto.Spherical.FractalDilations.AnnulusDominance
open Auto.Spherical.FractalDilations.AnnulusGeometry
open Auto.Spherical.FractalDilations.AnnulusMass
open Auto.Spherical.FractalDilations.AnnulusNorm
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Maximal
open Auto.Spherical.FractalDilations.SeparatedPacking
open Auto.Spherical.SurfaceCore







/-!
# The mass lower bound for the Minkowski annulus test

For a nonnegative real bump, a finite separated family of radii produces a
sum of spherical averages whose total mass is the number of radii times the
mass of the bump.  Its support is a finite union of thin annuli, and it is
pointwise bounded by the restricted maximal operator.  This file packages
those three facts into the exact `L^q` lower-bound inequality used by the
Minkowski sharpness test.
-/

namespace Auto.Spherical.FractalDilations.AnnulusLowerBound

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The `L¹` seminorm of a nonnegative annular sum is its explicitly computed
mass. -/
theorem eLpNorm_one_annulusAverageSum_eq_ofReal_card_mul_integral
    {d : ℕ} (hd : 0 < d) (f : SchwartzMap (Euclidean d) ℂ) (s : Finset ℝ)
    (hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ))
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re) :
    eLpNorm (annulusAverageSum d (f : Euclidean d → ℂ) s) 1 volume =
      ENNReal.ofReal ((s.card : ℝ) * ∫ x : Euclidean d, (f x).re) := by
  have hsum_nonneg : ∀ x : Euclidean d,
      0 ≤ annulusAverageSum d (f : Euclidean d → ℂ) s x :=
    annulusAverageSum_nonneg hd (f : Euclidean d → ℂ) s hreal hnonneg
  have hsum_integrable : Integrable
      (annulusAverageSum d (f : Euclidean d → ℂ) s) volume :=
    integrable_annulusAverageSum (f : Euclidean d → ℂ) s f.continuous f.integrable
  calc
    eLpNorm (annulusAverageSum d (f : Euclidean d → ℂ) s) 1 volume =
        ∫⁻ x : Euclidean d, ‖annulusAverageSum d (f : Euclidean d → ℂ) s x‖ₑ :=
      eLpNorm_one_eq_lintegral_enorm
    _ = ∫⁻ x : Euclidean d,
        ENNReal.ofReal (annulusAverageSum d (f : Euclidean d → ℂ) s x) := by
      congr with x
      rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal (hsum_nonneg x)]
      congr
      exact NNReal.eq (Real.norm_of_nonneg (hsum_nonneg x))
    _ = ENNReal.ofReal (∫ x : Euclidean d,
        annulusAverageSum d (f : Euclidean d → ℂ) s x) :=
      (ofReal_integral_eq_lintegral_ofReal hsum_integrable
        (Filter.Eventually.of_forall hsum_nonneg)).symm
    _ = ENNReal.ofReal ((s.card : ℝ) * ∫ x : Euclidean d, (f x).re) := by
      rw [integral_annulusAverageSum_eq_card_mul hd (f : Euclidean d → ℂ) s
        f.continuous f.integrable hreal]

/-- The exact annulus mass is bounded by the maximal-function `L^q` norm
times the finite-annulus support factor.  This is the analytic core of the
Minkowski lower-bound test. -/
theorem ofReal_card_mul_integral_le_eLpNorm_fractalSphericalMaximal_mul_annuli
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hEpos : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {R δ : ℝ} (s : Finset ℝ)
    (hsE : (↑s : Set ℝ) ⊆ E)
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (hsep : StrictlySeparated s δ) (hRδ : 4 * R ≤ δ)
    (hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ))
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re)
    {q : ℝ} (hq : 1 ≤ q) :
    ENNReal.ofReal ((s.card : ℝ) * ∫ x : Euclidean d, (f x).re) ≤
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
        volume (⋃ r ∈ s, radialAnnulus d (abs r) (2 * R)) ^ (1 - q⁻¹) := by
  let H : Euclidean d → ℝ := annulusAverageSum d (f : Euclidean d → ℂ) s
  let U : Set (Euclidean d) := ⋃ r ∈ s, radialAnnulus d (abs r) (2 * R)
  have hH_nonneg : ∀ x : Euclidean d, 0 ≤ H x := by
    exact annulusAverageSum_nonneg hd (f : Euclidean d → ℂ) s hreal hnonneg
  have hH_integrable : Integrable H volume := by
    exact integrable_annulusAverageSum (f : Euclidean d → ℂ) s f.continuous f.integrable
  have hH_support : Function.support H ⊆ U := by
    exact support_annulusAverageSum_subset hd (f : Euclidean d → ℂ) hzero s
  have hH_le_max : ∀ x : Euclidean d,
      H x ≤ fractalSphericalMaximalReal d E f x := by
    exact annulusAverageSum_le_fractalSphericalMaximalReal hd E hEpos f s hsE
      hzero hsep hRδ
  have hmax_nonneg : ∀ x : Euclidean d,
      0 ≤ fractalSphericalMaximalReal d E f x := by
    intro x
    unfold fractalSphericalMaximalReal
    exact ENNReal.toReal_nonneg
  have hH_norm_le :
      eLpNorm H (ENNReal.ofReal q) volume ≤
        eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_of_nonneg (hH_nonneg x),
      Real.norm_of_nonneg (hmax_nonneg x)]
    exact hH_le_max x
  have hfinite_support := eLpNorm_one_le_eLpNorm_of_support_subset hq
    hH_integrable.aestronglyMeasurable hH_support
  calc
    ENNReal.ofReal ((s.card : ℝ) * ∫ x : Euclidean d, (f x).re) =
        eLpNorm H 1 volume := by
      exact eLpNorm_one_annulusAverageSum_eq_ofReal_card_mul_integral
        hd f s hreal hnonneg |>.symm
    _ ≤ eLpNorm H (ENNReal.ofReal q) volume * volume U ^ (1 - q⁻¹) :=
      hfinite_support
    _ ≤ eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
        volume U ^ (1 - q⁻¹) := by
      exact mul_le_mul_left hH_norm_le _

/-- For a smooth nonnegative ball cutoff, the exact mass in the preceding
lemma is at least the cardinality times the volume of its inner ball. -/
theorem ofReal_card_mul_volume_ball_toReal_le_eLpNorm_fractalSphericalMaximal_mul_annuli
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hEpos : E ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) {R δ : ℝ} (s : Finset ℝ)
    (hsE : (↑s : Set ℝ) ⊆ E)
    (hOne : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (hsep : StrictlySeparated s δ) (hRδ : 4 * R ≤ δ)
    (hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ))
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re)
    {q : ℝ} (hq : 1 ≤ q) :
    ENNReal.ofReal ((s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal) ≤
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
        volume (⋃ r ∈ s, radialAnnulus d (abs r) (2 * R)) ^ (1 - q⁻¹) := by
  have hball_mass : (volume (ball (0 : Euclidean d) R)).toReal ≤
      ∫ x : Euclidean d, (f x).re :=
    volume_ball_toReal_le_integral_re_of_eq_one_nonneg f hOne hnonneg
  have hmass : (s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal ≤
      (s.card : ℝ) * ∫ x : Euclidean d, (f x).re :=
    mul_le_mul_of_nonneg_left hball_mass (Nat.cast_nonneg _)
  calc
    ENNReal.ofReal ((s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal) ≤
        ENNReal.ofReal ((s.card : ℝ) * ∫ x : Euclidean d, (f x).re) :=
      ENNReal.ofReal_le_ofReal hmass
    _ ≤ eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
        volume (⋃ r ∈ s, radialAnnulus d (abs r) (2 * R)) ^ (1 - q⁻¹) :=
      ofReal_card_mul_integral_le_eLpNorm_fractalSphericalMaximal_mul_annuli
        hd E hEpos f s hsE hzero hsep hRδ hreal hnonneg hq

/-- Replacing the actual annular support by the explicit finite-union volume
bound gives the form of the mass estimate used in scale calculations. -/
theorem ofReal_card_mul_volume_ball_toReal_le_eLpNorm_fractalSphericalMaximal_mul_annulusVolumeBound
    {d : ℕ} (hd : 0 < d) (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2)
    (f : SchwartzMap (Euclidean d) ℂ) {R δ : ℝ} (s : Finset ℝ)
    (hsE : (↑s : Set ℝ) ⊆ E)
    (hOne : ∀ y : Euclidean d, ‖y‖ ≤ R → f y = 1)
    (hzero : ∀ y : Euclidean d, 2 * R ≤ ‖y‖ → f y = 0)
    (hsep : StrictlySeparated s δ) (hRδ : 4 * R ≤ δ)
    (hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ))
    (hnonneg : ∀ y : Euclidean d, 0 ≤ (f y).re)
    (hR : 0 < R) (hRquarter : R ≤ 1 / 4)
    {q : ℝ} (hq : 1 ≤ q) :
    ENNReal.ofReal ((s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal) ≤
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
        ((s.card : ENNReal) *
          (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
            volume (ball (0 : Euclidean d) 1))) ^ (1 - q⁻¹) := by
  let U : Set (Euclidean d) := ⋃ r ∈ s, radialAnnulus d (abs r) (2 * R)
  let V : ENNReal := (s.card : ENNReal) *
    (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
      volume (ball (0 : Euclidean d) 1))
  have hEpos : E ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one (hE hr).1
  have hmass :=
    ofReal_card_mul_volume_ball_toReal_le_eLpNorm_fractalSphericalMaximal_mul_annuli
      hd E hEpos f s hsE hOne hzero hsep hRδ hreal hnonneg hq
  have hvolume : volume U ≤ V := by
    exact volume_biUnion_radialAnnulus_abs_le d hsE hE (by linarith) (by linarith)
  have hexp_nonneg : 0 ≤ 1 - q⁻¹ := by
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hq)
  have hvolume_rpow : volume U ^ (1 - q⁻¹) ≤ V ^ (1 - q⁻¹) :=
    ENNReal.rpow_le_rpow hvolume hexp_nonneg
  change ENNReal.ofReal ((s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal) ≤
    eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
      V ^ (1 - q⁻¹)
  calc
    ENNReal.ofReal ((s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal) ≤
        eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
          volume U ^ (1 - q⁻¹) := hmass
    _ ≤ eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume *
          V ^ (1 - q⁻¹) :=
      mul_le_mul_right hvolume_rpow _

/-- A finite nonzero support factor can be cancelled from a mass lower bound.
This is stated abstractly over `ENNReal` so that the scale calculation for
the annulus test can be carried out entirely in real numbers. -/
theorem ENNReal.ofReal_mul_lt_of_mass_le_mul_and_toReal_gap
    {C L : ℝ} {A B out : ENNReal}
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hA_top : A ≠ (⊤ : ENNReal))
    (hB_zero : B ≠ 0) (hB_top : B ≠ (⊤ : ENNReal))
    (hmass : ENNReal.ofReal L ≤ out * B)
    (hgap : C * A.toReal * B.toReal < L) :
    ENNReal.ofReal C * A < out := by
  by_cases hout_top : out = (⊤ : ENNReal)
  · rw [hout_top]
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA_top)
  · apply (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA_top) hout_top).mp
    have hmass_real : L ≤ out.toReal * B.toReal := by
      have hprod_top : out * B ≠ (⊤ : ENNReal) := ENNReal.mul_ne_top hout_top hB_top
      have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hprod_top).mpr hmass
      simpa [ENNReal.toReal_ofReal hL, ENNReal.toReal_mul] using h
    have hB_pos : 0 < B.toReal := ENNReal.toReal_pos hB_zero hB_top
    have hreal_gap : C * A.toReal < out.toReal := by
      apply lt_of_mul_lt_mul_right _ hB_pos.le
      calc
        (C * A.toReal) * B.toReal = C * A.toReal * B.toReal := by ring
        _ < L := hgap
        _ ≤ out.toReal * B.toReal := hmass_real
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hreal_gap

end

end Auto.Spherical.FractalDilations.AnnulusLowerBound
end Former_AnnulusLowerBound

/- ===== Former FractalDilations/ClusterAverageLower.lean ===== -/
section Former_ClusterAverageLower

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.ClusterCapGeometry
open Auto.Spherical.FractalDilations.ClusterGeometry
open Auto.Spherical.FractalDilations.ClusterTube
open Auto.Spherical.FractalDilations.ClusterTubeVolume
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.SurfaceCore







/-!
# Lower spherical-average bounds for the clustered-radius test

This file converts the geometric cap inclusion into an analytic lower bound
for a normalized spherical average.  Keeping this step separate from the
packing and scale algebra makes the sharpness construction reusable.
-/

namespace Auto.Spherical.FractalDilations.ClusterAverageLower

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

/-- If a nonnegative test function is one on all samples from a spherical
cap, then the real part of its spherical average dominates the cap mass. -/
theorem unitSurfaceMeasure_ball_toReal_le_re_sphericalAverage_of_eq_one_on_cap
    {n : ℕ} (f : SchwartzMap (Euclidean (n + 1)) ℂ)
    {t ε : ℝ} (x : Euclidean (n + 1))
    (hf : ∀ ω : sphere (0 : Euclidean (n + 1)) 1,
      ω ∈ ball (euclideanSuccLastSphere n) ε →
        f (x + t • (ω : Euclidean (n + 1))) = 1)
    (hnonneg : ∀ y : Euclidean (n + 1), 0 ≤ (f y).re) :
    ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
        (ball (euclideanSuccLastSphere n) ε)).toReal ≤
      (Auto.Spherical.SurfaceCore.sphericalAverage (n + 1)
        (f : Euclidean (n + 1) → ℂ) t x).re := by
  let μ : Measure (sphere (0 : Euclidean (n + 1)) 1) :=
    Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1)
  let S : Set (sphere (0 : Euclidean (n + 1)) 1) :=
    ball (euclideanSuccLastSphere n) ε
  let F : sphere (0 : Euclidean (n + 1)) 1 → ℂ := fun ω =>
    f (x + t • (ω : Euclidean (n + 1)))
  let g : sphere (0 : Euclidean (n + 1)) 1 → ℝ := fun ω => (F ω).re
  have hS : MeasurableSet S := by
    dsimp [S]
    exact isOpen_ball.measurableSet
  have hFcont : Continuous F := by
    dsimp [F]
    exact f.continuous.comp (continuous_const.add
      ((continuous_const : Continuous fun _ : sphere (0 : Euclidean (n + 1)) 1 => t).smul
        continuous_subtype_val))
  have hFint : Integrable F μ :=
    hFcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have hgcont : Continuous g := Complex.continuous_re.comp hFcont
  have hgint : Integrable g μ :=
    hgcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have hindicator : Integrable (S.indicator fun _ : sphere (0 : Euclidean (n + 1)) 1 =>
      (1 : ℝ)) μ :=
    (integrable_const _).indicator hS
  have hpoint (ω : sphere (0 : Euclidean (n + 1)) 1) :
      S.indicator (fun _ => (1 : ℝ)) ω ≤ g ω := by
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      dsimp [g, F]
      rw [hf ω hω]
      norm_num
    · rw [Set.indicator_of_notMem hω]
      dsimp [g, F]
      exact hnonneg _
  calc
    (μ S).toReal = ∫ ω : sphere (0 : Euclidean (n + 1)) 1,
        S.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      rw [integral_indicator hS, integral_const, Measure.real_def,
        Measure.restrict_apply_univ]
      simp
    _ ≤ ∫ ω : sphere (0 : Euclidean (n + 1)) 1, g ω ∂μ :=
      integral_mono hindicator hgint hpoint
    _ = (Auto.Spherical.SurfaceCore.sphericalAverage (n + 1)
        (f : Euclidean (n + 1) → ℂ) t x).re := by
      change (∫ ω : sphere (0 : Euclidean (n + 1)) 1, RCLike.re (F ω) ∂μ) = _
      rw [integral_re hFint]
      rfl

/-- Dividing the preceding cap-mass estimate by the positive total surface
mass gives a lower bound for the normalized average. -/
theorem unitSurfaceMeasure_ball_toReal_div_surfaceMass_le_re_normalizedSphericalAverage
    {n : ℕ} (hn : 0 < n + 1)
    (f : SchwartzMap (Euclidean (n + 1)) ℂ)
    {t ε : ℝ} (x : Euclidean (n + 1))
    (hf : ∀ ω : sphere (0 : Euclidean (n + 1)) 1,
      ω ∈ ball (euclideanSuccLastSphere n) ε →
        f (x + t • (ω : Euclidean (n + 1))) = 1)
    (hnonneg : ∀ y : Euclidean (n + 1), 0 ≤ (f y).re) :
    ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
        (ball (euclideanSuccLastSphere n) ε)).toReal /
        Auto.Spherical.SurfaceCore.surfaceMass (n + 1) ≤
      (Auto.Spherical.SurfaceCore.normalizedSphericalAverage (n + 1)
        (f : Euclidean (n + 1) → ℂ) t x).re := by
  have hmass : 0 < Auto.Spherical.SurfaceCore.surfaceMass (n + 1) :=
    Auto.Spherical.SurfaceCore.surfaceMass_pos hn
  have hraw := unitSurfaceMeasure_ball_toReal_le_re_sphericalAverage_of_eq_one_on_cap
    f x hf hnonneg
  have hraw_nonneg : 0 ≤
      (Auto.Spherical.SurfaceCore.sphericalAverage (n + 1)
        (f : Euclidean (n + 1) → ℂ) t x).re :=
    le_trans (ENNReal.toReal_nonneg) hraw
  calc
    ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
        (ball (euclideanSuccLastSphere n) ε)).toReal /
        Auto.Spherical.SurfaceCore.surfaceMass (n + 1) =
        (Auto.Spherical.SurfaceCore.surfaceMass (n + 1))⁻¹ *
          ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
            (ball (euclideanSuccLastSphere n) ε)).toReal := by ring
    _ ≤ (Auto.Spherical.SurfaceCore.surfaceMass (n + 1))⁻¹ *
        (Auto.Spherical.SurfaceCore.sphericalAverage (n + 1)
          (f : Euclidean (n + 1) → ℂ) t x).re :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hmass.le)
    _ = (Auto.Spherical.SurfaceCore.normalizedSphericalAverage (n + 1)
        (f : Euclidean (n + 1) → ℂ) t x).re := by
      unfold Auto.Spherical.SurfaceCore.normalizedSphericalAverage
      rw [← Complex.ofReal_inv]
      simp [Complex.mul_re]

/-- The geometric clustered-cap inclusion supplies the normalized-average
lower bound on every small anisotropic output box. -/
theorem capMass_div_surfaceMass_le_re_normalizedSphericalAverage_of_small_output
    {n : ℕ} {r t δ σ : ℝ}
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2)
    (htzero : 0 ≤ t) (httwo : t ≤ 2)
    (hδ : 0 < δ) (hδσ : δ ≤ σ ^ 2)
    (hσ : 0 < σ) (hσone : σ ≤ 1)
    (hshort : |t - r| * σ ^ 2 ≤ δ)
    (f : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hf : ∀ y : Euclidean (n + 1), y ∈ closedSphericalCapTube n r δ σ → f y = 1)
    (hnonneg : ∀ y : Euclidean (n + 1), 0 ≤ (f y).re)
    (x : Euclidean (n + 1))
    (hxhor : ‖(euclideanSuccCoordinates n x).1‖ ≤ δ / (128 * σ))
    (hxvert : |(euclideanSuccCoordinates n x).2 - (r - t)| ≤ δ / 128) :
    ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
        (ball (euclideanSuccLastSphere n) (σ / 128))).toReal /
        Auto.Spherical.SurfaceCore.surfaceMass (n + 1) ≤
      (Auto.Spherical.SurfaceCore.normalizedSphericalAverage (n + 1)
        (f : Euclidean (n + 1) → ℂ) t x).re := by
  apply unitSurfaceMeasure_ball_toReal_div_surfaceMass_le_re_normalizedSphericalAverage
    (by omega) f x ?_ hnonneg
  intro ω hω
  apply hf
  exact sampled_mem_closedSphericalCapTube_of_small_output
    hrone hrtwo htzero httwo hδ hδσ hσ hσone hshort x hxhor hxvert hω

/-- Uniformly in the geometric parameters, the clustered cap construction
has normalized average at least a positive dimensional constant times
`σ ^ n` on its output box. -/
theorem exists_power_lower_re_normalizedSphericalAverage_of_small_output (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ {r t δ σ : ℝ}
      (hrone : 1 ≤ r) (hrtwo : r ≤ 2)
      (htzero : 0 ≤ t) (httwo : t ≤ 2)
      (hδ : 0 < δ) (hδσ : δ ≤ σ ^ 2)
      (hσ : 0 < σ) (hσone : σ ≤ 1)
      (hshort : |t - r| * σ ^ 2 ≤ δ)
      (f : SchwartzMap (Euclidean (n + 1)) ℂ)
      (hf : ∀ y : Euclidean (n + 1), y ∈ closedSphericalCapTube n r δ σ → f y = 1)
      (hnonneg : ∀ y : Euclidean (n + 1), 0 ≤ (f y).re)
      (x : Euclidean (n + 1))
      (hxhor : ‖(euclideanSuccCoordinates n x).1‖ ≤ δ / (128 * σ))
      (hxvert : |(euclideanSuccCoordinates n x).2 - (r - t)| ≤ δ / 128),
      c * σ ^ n ≤
        (Auto.Spherical.SurfaceCore.normalizedSphericalAverage (n + 1)
          (f : Euclidean (n + 1) → ℂ) t x).re := by
  obtain ⟨c₀, hc₀pos, hc₀top, hcap⟩ :=
    exists_unitSurfaceMeasure_poleCap_ge_power n
  let m : ℝ := Auto.Spherical.SurfaceCore.surfaceMass (n + 1)
  let c : ℝ := c₀.toReal / (((128 : ℝ) ^ n) * m)
  have hmpos : 0 < m := by
    dsimp [m]
    exact Auto.Spherical.SurfaceCore.surfaceMass_pos (by omega)
  have hc₀realpos : 0 < c₀.toReal := ENNReal.toReal_pos hc₀pos.ne' hc₀top
  have hdenpos : 0 < ((128 : ℝ) ^ n) * m := by positivity
  have hcpos : 0 < c := div_pos hc₀realpos hdenpos
  refine ⟨c, hcpos, ?_⟩
  intro r t δ σ hrone hrtwo htzero httwo hδ hδσ hσ hσone hshort f hf hnonneg x hxhor hxvert
  have hcapE := hcap (σ / 128) (by positivity) (by linarith)
  have hcapTop : (Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
      (ball (euclideanSuccLastSphere n) (σ / 128)) ≠ ⊤ :=
    measure_ne_top _ _
  have hleftTop : c₀ * ENNReal.ofReal ((σ / 128) ^ n) ≠ ⊤ :=
    ENNReal.mul_ne_top hc₀top ENNReal.ofReal_ne_top
  have hcapReal : c₀.toReal * (σ / 128) ^ n ≤
      ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
        (ball (euclideanSuccLastSphere n) (σ / 128))).toReal := by
    have hto := (ENNReal.toReal_le_toReal hleftTop hcapTop).mpr hcapE
    have hpow_nonneg : 0 ≤ (σ / 128) ^ n :=
      pow_nonneg (by positivity) _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpow_nonneg] at hto
    exact hto
  have hdiv : (c₀.toReal * (σ / 128) ^ n) / m ≤
      ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
        (ball (euclideanSuccLastSphere n) (σ / 128))).toReal / m :=
    (div_le_div_iff_of_pos_right hmpos).2 hcapReal
  have hrewrite : c * σ ^ n = (c₀.toReal * (σ / 128) ^ n) / m := by
    dsimp [c]
    rw [div_pow]
    field_simp
  calc
    c * σ ^ n = (c₀.toReal * (σ / 128) ^ n) / m := hrewrite
    _ ≤ ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
          (ball (euclideanSuccLastSphere n) (σ / 128))).toReal / m := hdiv
    _ = ((Auto.Spherical.SurfaceCore.unitSurfaceMeasure (n + 1))
          (ball (euclideanSuccLastSphere n) (σ / 128))).toReal /
        Auto.Spherical.SurfaceCore.surfaceMass (n + 1) := by rfl
    _ ≤ (Auto.Spherical.SurfaceCore.normalizedSphericalAverage (n + 1)
          (f : Euclidean (n + 1) → ℂ) t x).re :=
      capMass_div_surfaceMass_le_re_normalizedSphericalAverage_of_small_output
        hrone hrtwo htzero httwo hδ hδσ hσ hσone hshort f hf hnonneg x hxhor hxvert

end

end Auto.Spherical.FractalDilations.ClusterAverageLower
end Former_ClusterAverageLower

/- ===== Former FractalDilations/AnnulusSharpness.lean ===== -/
section Former_AnnulusSharpness

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.AnnulusBump
open Auto.Spherical.FractalDilations.AnnulusDominance
open Auto.Spherical.FractalDilations.AnnulusLowerBound
open Auto.Spherical.FractalDilations.AnnulusNumericalBridge
open Auto.Spherical.FractalDilations.Definitions
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Maximal
open Auto.Spherical.FractalDilations.Minkowski
open Auto.Spherical.FractalDilations.PackingExtraction
open Auto.Spherical.FractalDilations.SeparatedPacking
open Auto.Spherical.FractalDilations.SharpnessNormalization
open Auto.Spherical.FractalDilations.SharpnessTests
open Auto.Spherical.FractalDilations.SharpnessVolume
open Auto.Spherical.SurfaceCore







/-!
# The Minkowski annulus sharpness construction

This file assembles the separated-radius packing witness, the nonnegative
smooth ball bump, and the annular mass inequality into the non-endpoint
Minkowski obstruction.  The positive-Minkowski-dimension case is isolated
first; the zero-dimensional singleton-radius case is handled separately by
the final theorem assembly.
-/

namespace Auto.Spherical.FractalDilations.AnnulusSharpness

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- A strict annulus inequality at a positive upper Minkowski dimension
forces failure of every strong `L^p → L^q` estimate. -/
theorem fractalSphericalUnbounded_of_positive_minkowski_annulus
    {d : ℕ} {E : Set ℝ} {α β p q : ℝ}
    (hd : 0 < d) (hE : E ⊆ Icc (1 : ℝ) 2)
    (hMinkowski : upperMinkowskiDimension E = β)
    (hα0 : 0 ≤ α) (hαβ : α < β)
    (hp : 0 < p) (hq : 1 ≤ q)
    (hbad : (1 - α) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    FractalSphericalUnbounded d E p q := by
  apply fractalSphericalUnbounded_of_large_ratio
  intro C hC
  obtain ⟨δ₀, hδ₀, hδ₀small, hgap⟩ :=
    exists_small_annulus_ennreal_gap_below (d := d) (α := α) (p := p) (q := q)
      hd hq hbad
  obtain ⟨δ, s, hδ, hδlt, hδone, hsE, hsep, hcard⟩ :=
    exists_upperMinkowski_strictlySeparated_power_lower_witness_at_small_scale
      hE hMinkowski hα0 hαβ 1 (by norm_num) δ₀ hδ₀
  let R : ℝ := δ / 8
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have htwoR : 0 < 2 * R := by positivity
  have hRδ : 4 * R ≤ δ := by
    dsimp [R]
    linarith
  have hRquarter : R ≤ 1 / 4 := by
    dsimp [R]
    linarith
  have hcard' : δ ^ (-α) < (s.card : ℝ) := by
    simpa using hcard
  have hcardrealpos : 0 < (s.card : ℝ) :=
    (Real.rpow_pos_of_pos hδ (-α)).trans hcard'
  have hcardpos : 0 < s.card := by
    exact_mod_cast hcardrealpos
  obtain ⟨f, hOne, hzero, hnonneg, himag, hbound⟩ :=
    exists_schwartz_ball_test_nonnegative_bounded d hR
  have hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ) := by
    intro y
    apply Complex.ext <;> simp [himag y]
  let A : ENNReal := volume (ball (0 : Euclidean d) (2 * R)) ^ p⁻¹
  let B : ENNReal :=
    ((s.card : ENNReal) *
      (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
        volume (ball (0 : Euclidean d) 1))) ^ (1 - q⁻¹)
  have hinput : eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤ A := by
    dsimp [A]
    exact eLpNorm_schwartz_ball_test_le_volume_ball hp f hzero hbound
  have hmass :
      ENNReal.ofReal ((s.card : ℝ) *
        (volume (ball (0 : Euclidean d) R)).toReal) ≤
        eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume * B := by
    dsimp [B]
    exact ofReal_card_mul_volume_ball_toReal_le_eLpNorm_fractalSphericalMaximal_mul_annulusVolumeBound
      hd E hE f s hsE hOne hzero hsep hRδ hreal hnonneg hR hRquarter hq
  have hgap_real : C * A.toReal * B.toReal <
      (s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal := by
    dsimp [A, B, R]
    simpa using hgap δ hδ hδlt s.card hcard'.le
  have hAprops : A ≠ 0 ∧ A ≠ (⊤ : ENNReal) := by
    dsimp [A]
    exact volume_ball_rpow_ne_zero_ne_top (d := d) (2 * R) p⁻¹ htwoR
  have hcoeff_pos : 0 <
      (2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R) := by
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hunit_pos : 0 < volume (ball (0 : Euclidean d) 1) :=
    measure_ball_pos volume (0 : Euclidean d) (by norm_num)
  have hinner_pos : 0 <
      ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
        volume (ball (0 : Euclidean d) 1) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hcoeff_pos).ne' hunit_pos.ne'
  have hcard_ennreal_pos : 0 < (s.card : ENNReal) := by
    exact_mod_cast hcardpos
  have hbase_pos : 0 < (s.card : ENNReal) *
      (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
        volume (ball (0 : Euclidean d) 1)) :=
    ENNReal.mul_pos hcard_ennreal_pos.ne' hinner_pos.ne'
  have hunit_top : volume (ball (0 : Euclidean d) 1) ≠ (⊤ : ENNReal) :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := (1 : ℝ))).ne
  have hinner_top :
      ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
        volume (ball (0 : Euclidean d) 1) ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunit_top
  have hbase_top : (s.card : ENNReal) *
      (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
        volume (ball (0 : Euclidean d) 1)) ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top s.card) hinner_top
  have hqinv : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have hexp_nonneg : 0 ≤ 1 - q⁻¹ := sub_nonneg.mpr hqinv
  have hBzero : B ≠ 0 := by
    dsimp [B]
    exact (ENNReal.rpow_pos hbase_pos hbase_top).ne'
  have hBtop : B ≠ (⊤ : ENNReal) := by
    dsimp [B]
    exact ENNReal.rpow_ne_top_of_nonneg hexp_nonneg hbase_top
  have hLnonneg : 0 ≤ (s.card : ℝ) *
      (volume (ball (0 : Euclidean d) R)).toReal :=
    mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have hratio : ENNReal.ofReal C * A <
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume :=
    ENNReal.ofReal_mul_lt_of_mass_le_mul_and_toReal_gap hC.le hLnonneg
      hAprops.2 hBzero hBtop hmass hgap_real
  exact ⟨f, A, hAprops.1, hAprops.2, hinput, hratio⟩

/-- A single radius already gives the annular sharpness obstruction in the
zero-dimensional branch.  This is deliberately independent of a dimension
assumption on `E`: nonemptiness supplies the one radius used by the test. -/
theorem fractalSphericalUnbounded_of_single_radius_annulus
    {d : ℕ} {E : Set ℝ} {p q : ℝ}
    (hd : 0 < d) (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    (hp : 0 < p) (hq : 1 ≤ q)
    (hbad : q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    FractalSphericalUnbounded d E p q := by
  rcases hEne with ⟨r, hr⟩
  apply fractalSphericalUnbounded_of_large_ratio
  intro C hC
  have hbad_zero : (1 - (0 : ℝ)) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹ := by
    simpa using hbad
  obtain ⟨δ₀, hδ₀, hδ₀small, hgap⟩ :=
    exists_small_annulus_ennreal_gap_below (d := d) (α := 0) (p := p) (q := q)
      (C := C) hd hq hbad_zero
  let δ : ℝ := δ₀ / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδlt : δ < δ₀ := by
    dsimp [δ]
    linarith
  let s : Finset ℝ := {r}
  have hsE : (↑s : Set ℝ) ⊆ E := by
    intro t ht
    have htr : t = r := by
      simpa [s] using ht
    simpa [htr] using hr
  have hsep : StrictlySeparated s δ := by
    intro x y hx hy hxy
    simp only [s, Finset.mem_singleton] at hx hy
    subst x
    subst y
    exact (hxy rfl).elim
  have hcard : s.card = 1 := by simp [s]
  have hcardpos : 0 < s.card := by simp [s]
  have hcard_lower : δ ^ (-(0 : ℝ)) ≤ (s.card : ℝ) := by
    simp [s]
  let R : ℝ := δ / 8
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have htwoR : 0 < 2 * R := by positivity
  have hRδ : 4 * R ≤ δ := by
    dsimp [R]
    linarith
  have hRquarter : R ≤ 1 / 4 := by
    dsimp [R]
    linarith
  obtain ⟨f, hOne, hzero, hnonneg, himag, hbound⟩ :=
    exists_schwartz_ball_test_nonnegative_bounded d hR
  have hreal : ∀ y : Euclidean d, f y = ((f y).re : ℂ) := by
    intro y
    apply Complex.ext <;> simp [himag y]
  let A : ENNReal := volume (ball (0 : Euclidean d) (2 * R)) ^ p⁻¹
  let B : ENNReal :=
    ((s.card : ENNReal) *
      (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
        volume (ball (0 : Euclidean d) 1))) ^ (1 - q⁻¹)
  have hinput : eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤ A := by
    dsimp [A]
    exact eLpNorm_schwartz_ball_test_le_volume_ball hp f hzero hbound
  have hmass :
      ENNReal.ofReal ((s.card : ℝ) *
        (volume (ball (0 : Euclidean d) R)).toReal) ≤
        eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume * B := by
    dsimp [B]
    exact ofReal_card_mul_volume_ball_toReal_le_eLpNorm_fractalSphericalMaximal_mul_annulusVolumeBound
      hd E hE f s hsE hOne hzero hsep hRδ hreal hnonneg hR hRquarter hq
  have hgap_real : C * A.toReal * B.toReal <
      (s.card : ℝ) * (volume (ball (0 : Euclidean d) R)).toReal := by
    dsimp [A, B, R]
    simpa using hgap δ hδ hδlt s.card hcard_lower
  have hAprops : A ≠ 0 ∧ A ≠ (⊤ : ENNReal) := by
    dsimp [A]
    exact volume_ball_rpow_ne_zero_ne_top (d := d) (2 * R) p⁻¹ htwoR
  have hcoeff_pos : 0 <
      (2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R) := by
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hunit_pos : 0 < volume (ball (0 : Euclidean d) 1) :=
    measure_ball_pos volume (0 : Euclidean d) (by norm_num)
  have hinner_pos : 0 <
      ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
        volume (ball (0 : Euclidean d) 1) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hcoeff_pos).ne' hunit_pos.ne'
  have hcard_ennreal_pos : 0 < (s.card : ENNReal) := by
    exact_mod_cast hcardpos
  have hbase_pos : 0 < (s.card : ENNReal) *
      (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
        volume (ball (0 : Euclidean d) 1)) :=
    ENNReal.mul_pos hcard_ennreal_pos.ne' hinner_pos.ne'
  have hunit_top : volume (ball (0 : Euclidean d) 1) ≠ (⊤ : ENNReal) :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := (1 : ℝ))).ne
  have hinner_top :
      ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
        volume (ball (0 : Euclidean d) 1) ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunit_top
  have hbase_top : (s.card : ENNReal) *
      (ENNReal.ofReal ((2 * (d : ℝ) * 3 ^ (d - 1)) * (2 * R)) *
        volume (ball (0 : Euclidean d) 1)) ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top s.card) hinner_top
  have hqinv : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have hexp_nonneg : 0 ≤ 1 - q⁻¹ := sub_nonneg.mpr hqinv
  have hBzero : B ≠ 0 := by
    dsimp [B]
    exact (ENNReal.rpow_pos hbase_pos hbase_top).ne'
  have hBtop : B ≠ (⊤ : ENNReal) := by
    dsimp [B]
    exact ENNReal.rpow_ne_top_of_nonneg hexp_nonneg hbase_top
  have hLnonneg : 0 ≤ (s.card : ℝ) *
      (volume (ball (0 : Euclidean d) R)).toReal :=
    mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have hratio : ENNReal.ofReal C * A <
      eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume :=
    ENNReal.ofReal_mul_lt_of_mass_le_mul_and_toReal_gap hC.le hLnonneg
      hAprops.2 hBzero hBtop hmass hgap_real
  exact ⟨f, A, hAprops.1, hAprops.2, hinput, hratio⟩

end

end Auto.Spherical.FractalDilations.AnnulusSharpness
end Former_AnnulusSharpness

/- ===== Former FractalDilations/ClusterSharpness.lean ===== -/
section Former_ClusterSharpness

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.AnnulusDominance
open Auto.Spherical.FractalDilations.ClusterAverageLower
open Auto.Spherical.FractalDilations.ClusterGeometry
open Auto.Spherical.FractalDilations.ClusterOutputGeometry
open Auto.Spherical.FractalDilations.ClusterTube
open Auto.Spherical.FractalDilations.ClusterTubeVolume
open Auto.Spherical.FractalDilations.Definitions
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Maximal
open Auto.Spherical.FractalDilations.SeparatedPacking
open Auto.Spherical.FractalDilations.SharpnessNormalization
open Auto.Spherical.FractalDilations.SharpnessNormLower
open Auto.Spherical.SurfaceCore







/-!
# Analytic clustered-radius sharpness test

This file assembles the curved tube bump, cap lower bound, and finite output
slab union.  The remaining scale comparison is deliberately separated from
this geometric-analytic construction.
-/

namespace Auto.Spherical.FractalDilations.ClusterSharpness

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The clustered-radius construction supplies one Schwartz input with the
standard cap-tube input envelope and a lower bound on the whole finite union
of output slabs. -/
theorem exists_cluster_schwartz_test_with_bounds (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ENNReal, 0 < C ∧ C ≠ ⊤ ∧ ∀
      {E : Set ℝ} {r δ σ p q : ℝ} {s : Finset ℝ},
      (1 ≤ r) → r ≤ 2 → 0 < δ → δ ≤ 1 / 20 →
      0 < σ → σ ≤ 1 → δ ≤ σ ^ 2 →
      StrictlySeparated s (δ / 2) → (↑s : Set ℝ) ⊆ E → E ⊆ Ioi (0 : ℝ) → E ⊆ Icc (0 : ℝ) 2 →
      (∀ t ∈ s, |t - r| * σ ^ 2 ≤ δ) → 0 < p → 1 ≤ q →
      ∃ f : SchwartzMap (Euclidean (n + 1)) ℂ,
        eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
          (C * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n)) ^ p⁻¹ ∧
        ENNReal.ofReal (c * σ ^ n) *
            volume (clusterOutputRegion n r δ σ s) ^ (1 / q) ≤
          eLpNorm (fractalSphericalMaximalReal (n + 1) E f)
            (ENNReal.ofReal q) volume := by
  obtain ⟨c, hcpos, hcap⟩ :=
    exists_power_lower_re_normalizedSphericalAverage_of_small_output n
  obtain ⟨C₀, hC₀top, hvolume⟩ := exists_volume_squaredSphericalCapTube_le_power n
  let C : ENNReal := C₀ + 1
  have hCpos : 0 < C := by
    have hone : (1 : ENNReal) ≤ C := by
      dsimp [C]
      exact le_add_of_nonneg_left (show (0 : ENNReal) ≤ C₀ by exact bot_le)
    exact lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hone
  have hCtop : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.add_ne_top.mpr ⟨hC₀top, ENNReal.one_ne_top⟩
  have hCmono : C₀ ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (show (0 : ENNReal) ≤ 1 by norm_num)
  refine ⟨c, hcpos, C, hCpos, hCtop, ?_⟩
  intro E r δ σ p q s hrone hrtwo hδ hδsmall hσ hσone hδσ hsep hsE hEpos hEbound hshort hp hq
  have hδquarter : δ ≤ 1 / 4 := by linarith
  obtain ⟨f, hf_one, hf_zero, hf_nonneg, hf_imag, hf_bound⟩ :=
    exists_schwartz_sphericalCapTube_test hrone hrtwo hδ hδquarter hσ
  refine ⟨f, ?_, ?_⟩
  · calc
      eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
          volume (squaredSphericalCapTube n r (10 * δ) (2 * σ)) ^ p⁻¹ :=
        eLpNorm_schwartz_sphericalCapTube_le hp f hf_zero hf_bound
      _ ≤ (C * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n)) ^ p⁻¹ := by
        have hcoeff :
            C₀ * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n) ≤
              C * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (mul_le_mul_right
              (mul_le_mul_right hCmono (ENNReal.ofReal (10 * δ)))
              (ENNReal.ofReal ((2 * σ) ^ n)))
        exact ENNReal.rpow_le_rpow
          ((hvolume r (10 * δ) (2 * σ) hrone hrtwo (by positivity)
            (by linarith) (by positivity)).trans hcoeff)
          (inv_nonneg.mpr hp.le)
  · let U : Set (Euclidean (n + 1)) := clusterOutputRegion n r δ σ s
    have hU : MeasurableSet U := by
      dsimp [U, clusterOutputRegion]
      exact MeasurableSet.biUnion s.countable_toSet (fun t ht =>
        measurableSet_centeredHorizontalSlab n (δ / (128 * σ)) (δ / 128) (r - t))
    have ha : 0 ≤ c * σ ^ n := by positivity
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have hmax_nonneg (x : Euclidean (n + 1)) :
        0 ≤ fractalSphericalMaximalReal (n + 1) E f x := by
      unfold fractalSphericalMaximalReal
      exact ENNReal.toReal_nonneg
    have hlower (x : Euclidean (n + 1)) (hx : x ∈ U) :
        c * σ ^ n ≤ fractalSphericalMaximalReal (n + 1) E f x := by
      rcases Set.mem_iUnion.mp hx with ⟨t, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨ht, hx⟩
      obtain ⟨hxhor, hxvert⟩ :=
        norm_and_abs_sub_center_le_of_mem_centeredHorizontalSlab hx
      have htbound : t ∈ Icc (0 : ℝ) 2 := hEbound (hsE ht)
      have havg : c * σ ^ n ≤
          (Auto.Spherical.SurfaceCore.normalizedSphericalAverage (n + 1)
            (f : Euclidean (n + 1) → ℂ) t x).re :=
        hcap hrone hrtwo htbound.1 htbound.2 hδ hδσ hσ hσone
          (hshort t ht) f hf_one hf_nonneg x hxhor hxvert
      exact havg.trans
        (re_normalizedSphericalAverage_le_fractalSphericalMaximalReal
          (by omega) E hEpos f (hsE ht) x)
    change ENNReal.ofReal (c * σ ^ n) * volume U ^ (1 / q) ≤
      eLpNorm (fractalSphericalMaximalReal (n + 1) E f) (ENNReal.ofReal q) volume
    exact ENNReal.ofReal_mul_volume_rpow_le_eLpNorm_of_lower_bound
      U hU ha hqpos _ hmax_nonneg (fun x hx => hlower x hx)

/-- A scalar gap for the two envelopes of the clustered test normalizes to
failure of every strong-type bound.  This is the analytic interface used by
the upper-spectrum packing argument: all of the remaining work is the
one-variable comparison of the displayed input and output scales. -/
theorem fractalSphericalUnbounded_of_cluster_scale_gaps
    {n : ℕ} {E : Set ℝ} {p q : ℝ}
    (hp : 0 < p) (hq : 1 ≤ q)
    (hgap : ∀ c : ℝ, 0 < c → ∀ K : ENNReal, 0 < K → K ≠ ⊤ → ∀ D : ℝ, 0 < D →
      ∃ r δ σ : ℝ, ∃ s : Finset ℝ,
        1 ≤ r ∧ r ≤ 2 ∧ 0 < δ ∧ δ ≤ 1 / 20 ∧
        0 < σ ∧ σ ≤ 1 ∧ δ ≤ σ ^ 2 ∧
        StrictlySeparated s (δ / 2) ∧ (↑s : Set ℝ) ⊆ E ∧
        E ⊆ Ioi (0 : ℝ) ∧ E ⊆ Icc (0 : ℝ) 2 ∧
        (∀ t ∈ s, |t - r| * σ ^ 2 ≤ δ) ∧
        ENNReal.ofReal D *
            (K * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n)) ^ p⁻¹ <
          ENNReal.ofReal (c * σ ^ n) *
            volume (clusterOutputRegion n r δ σ s) ^ (1 / q)) :
    FractalSphericalUnbounded (n + 1) E p q := by
  obtain ⟨c, hc, K, hK, hKtop, htest⟩ :=
    exists_cluster_schwartz_test_with_bounds n
  apply fractalSphericalUnbounded_of_large_ratio
  intro D hD
  obtain ⟨r, δ, σ, s, hrone, hrtwo, hδ, hδsmall, hσ, hσone, hδσ,
    hsep, hsE, hEpos, hEbound, hshort, hscalar⟩ :=
    hgap c hc K hK hKtop D hD
  obtain ⟨f, hfinput, hfoutput⟩ :=
    htest hrone hrtwo hδ hδsmall hσ hσone hδσ hsep hsE hEpos hEbound hshort
      hp hq
  let A : ENNReal :=
    (K * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n)) ^ p⁻¹
  have hbase_pos :
      0 < K * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n) := by
    positivity
  have hbase_top :
      K * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n) ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hKtop ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact (ENNReal.rpow_pos hbase_pos hbase_top).ne'
  have hAtop : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le) hbase_top
  refine ⟨f, A, hA0, hAtop, ?_, ?_⟩
  · simpa only [A] using hfinput
  · exact hscalar.trans_le hfoutput

end

end Auto.Spherical.FractalDilations.ClusterSharpness
end Former_ClusterSharpness

/- ===== Former FractalDilations/AnnulusTheorem.lean ===== -/
section Former_AnnulusTheorem

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.AnnulusAlgebra
open Auto.Spherical.FractalDilations.AnnulusLowerBound
open Auto.Spherical.FractalDilations.AnnulusSharpness
open Auto.Spherical.FractalDilations.Definitions
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Minkowski







/-!
# The Minkowski annulus sharpness theorem

This module packages the annular small-ball obstruction in the form used by
Theorem 2.  Positive upper Minkowski dimension is reduced to a slightly
smaller packing exponent, while dimension zero uses the one-radius test.
-/

namespace Auto.Spherical.FractalDilations.AnnulusTheorem

noncomputable section

/-- The non-endpoint annular obstruction determined by upper Minkowski
dimension.  The `β = 0` branch is a genuine singleton-radius construction;
for `β > 0`, a strict lower packing exponent is chosen first. -/
theorem minkowski_annulus_test
    {d : ℕ} (hd : 2 ≤ d)
    (E : Set ℝ) (hE : E ⊆ Set.Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    {β p q : ℝ}
    (hβ : 0 ≤ β ∧ β ≤ 1)
    (hMinkowski : upperMinkowskiDimension E = β)
    (hp : 0 < p) (hq : 1 ≤ q)
    (hbad : (1 - β) * q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹) :
    FractalSphericalUnbounded d E p q := by
  have hd0 : 0 < d := by omega
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rcases hβ.1.eq_or_lt with hβzero | hβpos
  · have hβeq : β = 0 := hβzero.symm
    have hbadzero : q⁻¹ + ((d : ℝ) - 1) < (d : ℝ) * p⁻¹ := by
      simpa [hβeq] using hbad
    exact fractalSphericalUnbounded_of_single_radius_annulus
      hd0 hE hEne hp hq hbadzero
  · obtain ⟨α, hα0, hαβ, hbadα⟩ :=
      exists_annulus_exponent_lt_minkowski hβpos hq0 hbad
    exact fractalSphericalUnbounded_of_positive_minkowski_annulus
      hd0 hE hMinkowski hα0 hαβ hp hq hbadα

end

end Auto.Spherical.FractalDilations.AnnulusTheorem
end Former_AnnulusTheorem

/- ===== Former FractalDilations/ClusterNumericalBridge.lean ===== -/
section Former_ClusterNumericalBridge

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.AnnulusDominance
open Auto.Spherical.FractalDilations.AnnulusScaleGap
open Auto.Spherical.FractalDilations.ClusterOutputGeometry
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.SeparatedPacking
open Auto.Spherical.FractalDilations.SharpnessNormLower
open Auto.Spherical.FractalDilations.SharpnessVolume
open Auto.Spherical.SurfaceCore







/-!
# Numerical scale comparison for clustered radii

This file translates the two `ENNReal` envelopes supplied by
`ClusterSharpness` into ordinary real powers.  The later spectrum argument
uses these identities with `σ = ((b-a)/δ)^{-1/2}`.
-/

namespace Auto.Spherical.FractalDilations.ClusterNumericalBridge

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The scale-independent coefficient in the input envelope after setting
`σ = T^{-1/2}`. -/
def clusterInputCoefficient (n : ℕ) (K : ENNReal) (p : ℝ) : ℝ :=
  (K.toReal * 10 * (2 : ℝ) ^ n) ^ p⁻¹

/-- The scale-independent coefficient in the output envelope after setting
`σ = T^{-1/2}`. -/
def clusterOutputCoefficient (n : ℕ) (c q : ℝ) : ℝ :=
  c * ((((128 : ℝ) ^ n)⁻¹ / 64) *
    (volume (ball (0 : Euclidean n) 1)).toReal) ^ q⁻¹

/-- The real value of the input envelope in the clustered test. -/
theorem cluster_input_envelope_toReal
    {n : ℕ} {K : ENNReal} {δ σ p : ℝ}
    (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) :
    ((K * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n)) ^ p⁻¹).toReal =
      (K.toReal * (10 * δ) * (2 * σ) ^ n) ^ p⁻¹ := by
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]

/-- Factor the input envelope at the parabolic scale `σ = T^{-1/2}`. -/
theorem cluster_input_envelope_toReal_factorized
    {n : ℕ} {K : ENNReal} {δ T p : ℝ}
    (hδ : 0 < δ) (hT : 0 < T) :
    ((K * ENNReal.ofReal (10 * δ) *
        ENNReal.ofReal ((2 * T ^ (-(1 / 2 : ℝ))) ^ n)) ^ p⁻¹).toReal =
      clusterInputCoefficient n K p * δ ^ p⁻¹ *
        T ^ (-((n : ℝ) / 2 * p⁻¹)) := by
  rw [cluster_input_envelope_toReal hδ.le (Real.rpow_nonneg hT.le _)]
  have hbase :
      K.toReal * (10 * δ) * (2 * T ^ (-(1 / 2 : ℝ))) ^ n =
        (K.toReal * 10 * (2 : ℝ) ^ n) * δ * T ^ (-(n : ℝ) / 2) := by
    have hTnat : (T ^ (-(1 / 2 : ℝ))) ^ n = T ^ (-(n : ℝ) / 2) := by
      calc
        (T ^ (-(1 / 2 : ℝ))) ^ n =
            (T ^ (-(1 / 2 : ℝ))) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
        _ = T ^ ((-(1 / 2 : ℝ)) * (n : ℝ)) :=
          (Real.rpow_mul hT.le (-(1 / 2 : ℝ)) (n : ℝ)).symm
        _ = T ^ (-(n : ℝ) / 2) := by congr 1 <;> ring
    rw [mul_pow]
    rw [hTnat]
    ring
  rw [hbase, clusterInputCoefficient]
  have hconst : 0 ≤ K.toReal * 10 * (2 : ℝ) ^ n := by positivity
  have hTscale : 0 ≤ T ^ (-(n : ℝ) / 2) := Real.rpow_nonneg hT.le _
  rw [Real.mul_rpow (mul_nonneg hconst hδ.le) hTscale]
  rw [Real.mul_rpow hconst hδ.le]
  rw [show (T ^ (-(n : ℝ) / 2)) ^ p⁻¹ =
      T ^ ((-(n : ℝ) / 2) * p⁻¹) by
        exact (Real.rpow_mul hT.le (-(n : ℝ) / 2) p⁻¹).symm]
  ring

/-- The real value of the output envelope, after expanding the disjoint slab
union and the volume of its transverse ball. -/
theorem cluster_output_envelope_toReal
    {n : ℕ} {r δ σ q : ℝ} {s : Finset ℝ} {c : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hc : 0 ≤ c)
    (hsep : StrictlySeparated s (δ / 2)) :
    (ENNReal.ofReal (c * σ ^ n) *
        volume (clusterOutputRegion n r δ σ s) ^ (1 / q)).toReal =
      c * σ ^ n *
        ((s.card : ℝ) *
          (((δ / (128 * σ)) ^ n) *
            (volume (ball (0 : Euclidean n) 1)).toReal) *
          (2 * (δ / 128))) ^ (1 / q) := by
  have hρ : 0 < δ / (128 * σ) := by positivity
  have hcap : 0 ≤ c * σ ^ n := by positivity
  rw [volume_clusterOutputRegion hδ.le hsep]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcap,
    ← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_mul, volume_ball_toReal n (δ / (128 * σ)) hρ,
    ENNReal.toReal_ofReal (by positivity)]
  congr 2
  ring

/-- Factor the output envelope at the parabolic scale `σ = T^{-1/2}`. -/
theorem cluster_output_envelope_toReal_factorized
    {n : ℕ} {r δ T q c : ℝ} {s : Finset ℝ}
    (hδ : 0 < δ) (hT : 0 < T) (hc : 0 ≤ c)
    (hsep : StrictlySeparated s (δ / 2)) :
    (ENNReal.ofReal (c * (T ^ (-(1 / 2 : ℝ))) ^ n) *
        volume (clusterOutputRegion n r δ (T ^ (-(1 / 2 : ℝ))) s) ^ (1 / q)).toReal =
      clusterOutputCoefficient n c q * δ ^ (((n : ℝ) + 1) * q⁻¹) *
        T ^ (-((n : ℝ) / 2 * (1 - q⁻¹))) * (s.card : ℝ) ^ q⁻¹ := by
  let V : ℝ := (volume (ball (0 : Euclidean n) 1)).toReal
  let σ : ℝ := T ^ (-(1 / 2 : ℝ))
  have hσ : 0 < σ := Real.rpow_pos_of_pos hT _
  have hσnat : σ ^ n = T ^ (-(n : ℝ) / 2) := by
    dsimp [σ]
    calc
      (T ^ (-(1 / 2 : ℝ))) ^ n =
          (T ^ (-(1 / 2 : ℝ))) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
      _ = T ^ ((-(1 / 2 : ℝ)) * (n : ℝ)) :=
        (Real.rpow_mul hT.le (-(1 / 2 : ℝ)) (n : ℝ)).symm
      _ = T ^ (-(n : ℝ) / 2) := by congr 1 <;> ring
  have hratio : (δ / (128 * σ)) ^ n =
      δ ^ n * ((128 : ℝ) ^ n)⁻¹ * T ^ ((n : ℝ) / 2) := by
    rw [div_pow, mul_pow, hσnat]
    have hTinv : (T ^ (-(n : ℝ) / 2))⁻¹ = T ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_neg hT.le]
      congr 1
      ring
    rw [div_eq_mul_inv, mul_inv_rev, hTinv]
    ring
  have hδnat : δ ^ n * δ = δ ^ ((n : ℝ) + 1) := by
    calc
      δ ^ n * δ = δ ^ (n : ℝ) * δ ^ (1 : ℝ) := by
        rw [Real.rpow_natCast, Real.rpow_one]
      _ = δ ^ ((n : ℝ) + 1) := (Real.rpow_add hδ _ _).symm
  have hinside :
      (s.card : ℝ) * (((δ / (128 * σ)) ^ n) * V) * (2 * (δ / 128)) =
        ((s.card : ℝ) * ((((128 : ℝ) ^ n)⁻¹ / 64) * V)) *
          δ ^ ((n : ℝ) + 1) * T ^ ((n : ℝ) / 2) := by
    rw [hratio]
    rw [show 2 * (δ / 128) = δ / 64 by ring]
    rw [← hδnat]
    ring
  rw [cluster_output_envelope_toReal hδ hσ hc hsep]
  change c * σ ^ n *
      ((s.card : ℝ) * (((δ / (128 * σ)) ^ n) * V) * (2 * (δ / 128))) ^ (1 / q) = _
  rw [hinside, hσnat]
  rw [one_div]
  have hcard : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hcoef : 0 ≤ (((128 : ℝ) ^ n)⁻¹ / 64) * V := by
    dsimp [V]
    positivity
  have hδpow : 0 ≤ δ ^ ((n : ℝ) + 1) := Real.rpow_nonneg hδ.le _
  have hTpow : 0 ≤ T ^ ((n : ℝ) / 2) := Real.rpow_nonneg hT.le _
  rw [Real.mul_rpow (mul_nonneg (mul_nonneg hcard hcoef) hδpow) hTpow]
  rw [Real.mul_rpow (mul_nonneg hcard hcoef) hδpow]
  rw [Real.mul_rpow hcard hcoef]
  rw [show (δ ^ ((n : ℝ) + 1)) ^ q⁻¹ = δ ^ (((n : ℝ) + 1) * q⁻¹) by
    exact (Real.rpow_mul hδ.le ((n : ℝ) + 1) q⁻¹).symm]
  rw [show (T ^ ((n : ℝ) / 2)) ^ q⁻¹ = T ^ (((n : ℝ) / 2) * q⁻¹) by
    exact (Real.rpow_mul hT.le ((n : ℝ) / 2) q⁻¹).symm]
  rw [clusterOutputCoefficient]
  have hTcombine :
      T ^ (-(n : ℝ) / 2) * T ^ ((n : ℝ) / 2 * q⁻¹) =
        T ^ (-((n : ℝ) / 2 * (1 - q⁻¹))) := by
    rw [← Real.rpow_add hT]
    congr 1
    ring
  calc
    c * T ^ (-(n : ℝ) / 2) *
        ((s.card : ℝ) ^ q⁻¹ * ((((128 : ℝ) ^ n)⁻¹ / 64) * V) ^ q⁻¹ *
          δ ^ (((n : ℝ) + 1) * q⁻¹) * T ^ ((n : ℝ) / 2 * q⁻¹)) =
        (c * ((((128 : ℝ) ^ n)⁻¹ / 64) * V) ^ q⁻¹) *
          δ ^ (((n : ℝ) + 1) * q⁻¹) *
          (T ^ (-(n : ℝ) / 2) * T ^ ((n : ℝ) / 2 * q⁻¹)) *
          (s.card : ℝ) ^ q⁻¹ := by ring
    _ = (c * ((((128 : ℝ) ^ n)⁻¹ / 64) * V) ^ q⁻¹) *
          δ ^ (((n : ℝ) + 1) * q⁻¹) *
          T ^ (-((n : ℝ) / 2 * (1 - q⁻¹))) * (s.card : ℝ) ^ q⁻¹ := by
            rw [hTcombine]

/-- The elementary power comparison behind the clustered test.  The factor
`T ^ v` is common to the input and output scales; the positive gain `k` is
converted into a gain of `δ ^ (-a*k)` from `δ ^ (-a) ≤ T`. -/
theorem exists_small_cluster_power_gap_below
    {a k u v w I O D : ℝ}
    (hO : 0 < O) (hk : 0 < k) (hgap : w - a * k < u) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 20 ∧ ∀ δ T : ℝ,
      0 < δ → δ < δ₀ → δ ^ (-a) ≤ T →
        D * I * δ ^ u * T ^ v < O * δ ^ w * T ^ (v + k) := by
  obtain ⟨δ₁, hδ₁, hδ₁small, hsmall⟩ :=
    exists_small_rpow_separation_below (a := w - a * k) (b := u)
      (A := I) (B := O) (C := D) hO hgap
  let δ₀ : ℝ := min δ₁ (1 / 20)
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min hδ₁ (by norm_num)
  have hδ₀small : δ₀ ≤ 1 / 20 := by
    dsimp [δ₀]
    exact min_le_right _ _
  refine ⟨δ₀, hδ₀, hδ₀small, ?_⟩
  intro δ T hδ hδsmall hT
  have hδδ₁ : δ < δ₁ := hδsmall.trans_le (by
    dsimp [δ₀]
    exact min_le_left _ _)
  have hbase : D * I * δ ^ u < O * δ ^ (w - a * k) :=
    hsmall δ hδ hδδ₁
  have hδpow_pos : 0 < δ ^ (-a) := Real.rpow_pos_of_pos hδ _
  have hTpos : 0 < T := hδpow_pos.trans_le hT
  have hTpow : (δ ^ (-a)) ^ k ≤ T ^ k :=
    Real.rpow_le_rpow hδpow_pos.le hT hk.le
  have hTpow' : δ ^ (-a * k) ≤ T ^ k := by
    calc
      δ ^ (-a * k) = (δ ^ (-a)) ^ k := by
        rw [Real.rpow_mul hδ.le]
      _ ≤ T ^ k := hTpow
  have hδfactor : δ ^ (w - a * k) = δ ^ w * δ ^ (-a * k) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hright : O * δ ^ (w - a * k) ≤ O * δ ^ w * T ^ k := by
    calc
      O * δ ^ (w - a * k) = O * (δ ^ w * δ ^ (-a * k)) := by rw [hδfactor]
      _ ≤ O * (δ ^ w * T ^ k) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hTpow' (Real.rpow_nonneg hδ.le _)) hO.le
      _ = O * δ ^ w * T ^ k := by ring
  have hTv : 0 < T ^ v := Real.rpow_pos_of_pos hTpos _
  have hmul : (D * I * δ ^ u) * T ^ v <
      (O * δ ^ w * T ^ k) * T ^ v :=
    mul_lt_mul_of_pos_right (hbase.trans_le hright) hTv
  calc
    D * I * δ ^ u * T ^ v = (D * I * δ ^ u) * T ^ v := by ring
    _ < (O * δ ^ w * T ^ k) * T ^ v := hmul
    _ = O * δ ^ w * (T ^ k * T ^ v) := by ring
    _ = O * δ ^ w * T ^ (k + v) := by rw [← Real.rpow_add hTpos]
    _ = O * δ ^ w * T ^ (v + k) := by ring

/-- The numerical comparison in the exact `ENNReal` form consumed by the
clustered test.  A packing lower bound at the relative scale `T` and a strict
power gap force the output envelope to dominate any prescribed multiple of
the input envelope. -/
theorem exists_small_cluster_ennreal_gap_below
    {n : ℕ} {a α p q c D : ℝ} {K : ENNReal}
    (hn : 0 < n) (ha : 0 ≤ a) (hα : 0 ≤ α)
    (hc : 0 < c) (hK : 0 < K) (hKtop : K ≠ ⊤)
    (hD : 0 < D) (hp : 0 < p) (hq : 1 ≤ q)
    (hk : 0 < α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹))
    (hpower : ((n : ℝ) + 1) * q⁻¹ -
        a * (α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹)) < p⁻¹) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 20 ∧ ∀ {δ T r : ℝ} {s : Finset ℝ},
      0 < δ → δ < δ₀ → δ ^ (-a) ≤ T →
      StrictlySeparated s (δ / 2) → T ^ α < (s.card : ℝ) →
      ENNReal.ofReal D *
          (K * ENNReal.ofReal (10 * δ) *
            ENNReal.ofReal ((2 * T ^ (-(1 / 2 : ℝ))) ^ n)) ^ p⁻¹ <
        ENNReal.ofReal (c * ((T ^ (-(1 / 2 : ℝ))) ^ n)) *
          volume (clusterOutputRegion n r δ (T ^ (-(1 / 2 : ℝ))) s) ^ (1 / q) := by
  let I : ℝ := clusterInputCoefficient n K p
  let O : ℝ := clusterOutputCoefficient n c q
  let k : ℝ := α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹)
  let v : ℝ := -((n : ℝ) / 2 * p⁻¹)
  let w : ℝ := ((n : ℝ) + 1) * q⁻¹
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqinv : 0 < q⁻¹ := inv_pos.mpr hqpos
  have hV : 0 < (volume (ball (0 : Euclidean n) 1)).toReal :=
    volume_unit_ball_toReal_pos hn
  have hI : 0 < I := by
    dsimp [I, clusterInputCoefficient]
    apply Real.rpow_pos_of_pos
    have hKreal : 0 < K.toReal := ENNReal.toReal_pos hK.ne' hKtop
    positivity
  have hO : 0 < O := by
    dsimp [O, clusterOutputCoefficient]
    apply mul_pos hc
    apply Real.rpow_pos_of_pos
    have h128 : 0 < ((128 : ℝ) ^ n)⁻¹ / 64 := by positivity
    positivity
  obtain ⟨δ₀, hδ₀, hδ₀small, hsmall⟩ :=
    exists_small_cluster_power_gap_below (a := a) (k := k) (u := p⁻¹)
      (v := v) (w := w) (I := I) (O := O) (D := D) hO (by simpa [k] using hk)
      (by simpa [k, w] using hpower)
  refine ⟨δ₀, hδ₀, hδ₀small, ?_⟩
  intro δ T r s hδ hδsmall hT hsep hpack
  have hTpos : 0 < T := (Real.rpow_pos_of_pos hδ _).trans_le hT
  have hNpos : 0 < (s.card : ℝ) := (Real.rpow_pos_of_pos hTpos α).trans hpack
  have hpackpow : T ^ (α * q⁻¹) < (s.card : ℝ) ^ q⁻¹ := by
    have h := (Real.rpow_lt_rpow_iff
      (Real.rpow_nonneg hTpos.le α) hNpos.le hqinv).mpr hpack
    rw [show (T ^ α) ^ q⁻¹ = T ^ (α * q⁻¹) by
      exact (Real.rpow_mul hTpos.le α q⁻¹).symm] at h
    exact h
  have hscale := hsmall δ T hδ hδsmall hT
  have hout_exp : v + k = α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹) := by
    dsimp [v, k]
    ring
  have hrealgap :
      D * I * δ ^ p⁻¹ * T ^ v <
        O * δ ^ w * T ^ (-((n : ℝ) / 2 * (1 - q⁻¹))) *
          (s.card : ℝ) ^ q⁻¹ := by
    have hscale' : D * I * δ ^ p⁻¹ * T ^ v <
        O * δ ^ w * T ^ (α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹)) := by
      rw [← hout_exp]
      exact hscale
    have hfactor : 0 < O * δ ^ w * T ^ (-((n : ℝ) / 2 * (1 - q⁻¹))) := by
      positivity
    have hTsplit :
        T ^ (α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹)) =
          T ^ (-((n : ℝ) / 2 * (1 - q⁻¹))) * T ^ (α * q⁻¹) := by
      calc
        T ^ (α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹)) =
            T ^ (-((n : ℝ) / 2 * (1 - q⁻¹)) + α * q⁻¹) := by
              congr 1
              ring
        _ = T ^ (-((n : ℝ) / 2 * (1 - q⁻¹))) * T ^ (α * q⁻¹) :=
          Real.rpow_add hTpos _ _
    calc
      D * I * δ ^ p⁻¹ * T ^ v <
          O * δ ^ w * T ^ (α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹)) := hscale'
      _ = (O * δ ^ w * T ^ (-((n : ℝ) / 2 * (1 - q⁻¹)))) *
          T ^ (α * q⁻¹) := by
            rw [hTsplit]
            ring
      _ < (O * δ ^ w * T ^ (-((n : ℝ) / 2 * (1 - q⁻¹)))) *
          (s.card : ℝ) ^ q⁻¹ :=
            mul_lt_mul_of_pos_left hpackpow hfactor
      _ = O * δ ^ w * T ^ (-((n : ℝ) / 2 * (1 - q⁻¹)))*
          (s.card : ℝ) ^ q⁻¹ := by ring
  have hbase_top :
      K * ENNReal.ofReal (10 * δ) *
          ENNReal.ofReal ((2 * T ^ (-(1 / 2 : ℝ))) ^ n) ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hKtop ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hinput_top :
      (K * ENNReal.ofReal (10 * δ) *
          ENNReal.ofReal ((2 * T ^ (-(1 / 2 : ℝ))) ^ n)) ^ p⁻¹ ≠ (⊤ : ENNReal) :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le) hbase_top
  have hleft_top : ENNReal.ofReal D *
      (K * ENNReal.ofReal (10 * δ) *
          ENNReal.ofReal ((2 * T ^ (-(1 / 2 : ℝ))) ^ n)) ^ p⁻¹ ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hinput_top
  by_cases hright_top :
      (ENNReal.ofReal (c * ((T ^ (-(1 / 2 : ℝ))) ^ n)) *
        volume (clusterOutputRegion n r δ (T ^ (-(1 / 2 : ℝ))) s) ^ (1 / q)) = ⊤
  · rw [hright_top]
    exact lt_top_iff_ne_top.mpr hleft_top
  · apply (ENNReal.toReal_lt_toReal hleft_top hright_top).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le,
      cluster_input_envelope_toReal_factorized hδ hTpos]
    rw [cluster_output_envelope_toReal_factorized
      (n := n) (r := r) (δ := δ) (T := T) (q := q) (c := c) (s := s)
      hδ hTpos hc.le hsep]
    dsimp [I, O, v, w] at hrealgap
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrealgap

end

end Auto.Spherical.FractalDilations.ClusterNumericalBridge
end Former_ClusterNumericalBridge

/- ===== Former FractalDilations/ClusterSpectrumSharpness.lean ===== -/
section Former_ClusterSpectrumSharpness

/- This file was machine-generated by Codex -/

open Auto.Spherical.FractalDilations.AssouadSpectrum
open Auto.Spherical.FractalDilations.ClusterNumericalBridge
open Auto.Spherical.FractalDilations.ClusterPacking
open Auto.Spherical.FractalDilations.ClusterSharpness
open Auto.Spherical.FractalDilations.Definitions
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.SharpnessNormLower
open Auto.Spherical.FractalDilations.ShellSharpness







/-!
# Upper-spectrum clustered-radius sharpness

This is the final assembly of the clustered-radius obstruction.  The upper
Assouad-spectrum packing witness gives a finite family of radii in a short
interval.  At its natural parabolic scale, the analytic clustered test from
`ClusterSharpness` violates every proposed strong bound beyond the cluster
edge.
-/

namespace Auto.Spherical.FractalDilations.ClusterSpectrumSharpness

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- Either the spherical-cap obstruction already applies, or a strict
cluster edge inequality persists after lowering the spectrum exponent a
little.  This elementary alternative is what lets an infimum-defined upper
spectrum supply actual finite packings. -/
theorem spherical_cap_or_exists_cluster_exponent
    {n : ℕ} {a γ p q : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hγ : 0 < γ)
    (hp : 0 < p) (hq : 1 ≤ q)
    (hbad : ((n : ℝ) + 1) * q⁻¹ -
        a * (γ * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹)) < p⁻¹) :
    ((n : ℝ) + 1) * q⁻¹ < p⁻¹ ∨
      ∃ α : ℝ, 0 ≤ α ∧ α < γ ∧
        0 < α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹) ∧
        ((n : ℝ) + 1) * q⁻¹ -
          a * (α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹)) < p⁻¹ := by
  let k : ℝ := γ * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹)
  let w : ℝ := ((n : ℝ) + 1) * q⁻¹
  by_cases hk : 0 < k
  · right
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have hqinv : 0 < q⁻¹ := inv_pos.mpr hqpos
    have hqne : q ≠ 0 := ne_of_gt hqpos
    let m : ℝ := p⁻¹ - (w - a * k)
    have hm : 0 < m := by
      dsimp [m, w, k]
      linarith
    let ε : ℝ := min (γ / 2) (min (k * q / 2) (m * q / (2 * a)))
    have hε : 0 < ε := by
      dsimp [ε]
      apply lt_min
      · positivity
      · apply lt_min <;> positivity
    have hεγ : ε ≤ γ / 2 := by
      dsimp [ε]
      exact min_le_left _ _
    have hεk : ε ≤ k * q / 2 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hεm : ε ≤ m * q / (2 * a) := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    let α : ℝ := γ - ε
    have hα0 : 0 ≤ α := by
      dsimp [α]
      linarith
    have hαγ : α < γ := by
      dsimp [α]
      linarith
    have hεq : ε * q⁻¹ ≤ k / 2 := by
      calc
        ε * q⁻¹ ≤ (k * q / 2) * q⁻¹ :=
          mul_le_mul_of_nonneg_right hεk hqinv.le
        _ = k / 2 := by
          field_simp
    have hkα : 0 < α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹) := by
      have hkhalf : 0 < k / 2 := by positivity
      have hkαeq : α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹) =
          k - ε * q⁻¹ := by
        dsimp [α, k]
        ring
      rw [hkαeq]
      linarith
    have hεaq : a * ε * q⁻¹ ≤ m / 2 := by
      calc
        a * ε * q⁻¹ = a * (ε * q⁻¹) := by ring
        _ ≤ a * ((m * q / (2 * a)) * q⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hεm hqinv.le) ha.le
        _ = m / 2 := by
          field_simp
    have hpower : w - a *
        (α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹)) < p⁻¹ := by
      calc
        w - a * (α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹)) =
            (w - a * k) + a * ε * q⁻¹ := by
              dsimp [α, k]
              ring
        _ ≤ (w - a * k) + m / 2 := by
              exact add_le_add_right hεaq _
        _ < (w - a * k) + m := by linarith
        _ = p⁻¹ := by
              dsimp [m]
              ring
    exact ⟨α, hα0, hαγ, hkα, by simpa [w] using hpower⟩
  · left
    have hk' : k ≤ 0 := le_of_not_gt hk
    have hnonneg : 0 ≤ -(a * k) := by
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos ha.le hk')
    have hbad' : w - a * k < p⁻¹ := by
      simpa [w, k] using hbad
    have hw : w < p⁻¹ := by linarith
    simpa [w] using hw

/-- A strict clustered scale inequality, together with an upper-spectrum
packing exponent, gives the corresponding unbounded maximal operator. -/
theorem fractalSphericalUnbounded_of_upper_spectrum_cluster_gap
    {n : ℕ} {E : Set ℝ} {θ α γ p q : ℝ}
    (hn : 0 < n) (hE : E ⊆ Icc (1 : ℝ) 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hspectrum : upperAssouadSpectrum E θ = γ)
    (hα0 : 0 ≤ α) (hαγ : α < γ)
    (hp : 0 < p) (hq : 1 ≤ q)
    (hk : 0 < α * q⁻¹ - (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹))
    (hpower : ((n : ℝ) + 1) * q⁻¹ -
        (1 - θ) * (α * q⁻¹ -
          (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹)) < p⁻¹) :
    FractalSphericalUnbounded (n + 1) E p q := by
  apply fractalSphericalUnbounded_of_cluster_scale_gaps hp hq
  intro c hc K hK hKtop D hD
  obtain ⟨δ₀, hδ₀, hδ₀small, hgap⟩ :=
    exists_small_cluster_ennreal_gap_below
      (n := n) (a := 1 - θ) (α := α) (p := p) (q := q)
      (c := c) (K := K) (D := D) hn (by linarith) hα0 hc hK hKtop hD hp hq hk hpower
  obtain ⟨δ, a, b, s, hδ, hδsmall, hδone, ha, hab, hb, hscale,
    hs, hsep, hpack⟩ :=
    exists_upperAssouadSpectrum_strictlySeparated_lower_witness_at_small_scale
      hθ0 hθ1.le hspectrum hα0 hαγ 1 (by norm_num) δ₀ hδ₀
  let L : ℝ := b - a
  let T : ℝ := L / δ
  let σ : ℝ := T ^ (-(1 / 2 : ℝ))
  have hLpos : 0 < L := by
    dsimp [L]
    exact (Real.rpow_pos_of_pos hδ _).trans_le hscale
  have hTpos : 0 < T := by
    dsimp [T]
    positivity
  have hδlepow : δ ≤ δ ^ θ := by
    calc
      δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ θ := Real.rpow_le_rpow_of_exponent_ge hδ hδone.le hθ1.le
  have hδL : δ ≤ L := by
    exact hδlepow.trans hscale
  have hTone : 1 ≤ T := by
    dsimp [T]
    apply (le_div_iff₀ hδ).mpr
    simpa using hδL
  have hσ : 0 < σ := by
    dsimp [σ]
    exact Real.rpow_pos_of_pos hTpos _
  have hσone : σ ≤ 1 := by
    dsimp [σ]
    exact Real.rpow_le_one_of_one_le_of_nonpos hTone (by norm_num)
  have hσsq : σ ^ 2 = δ / L := by
    have hpow : σ ^ 2 = T⁻¹ := by
      dsimp [σ]
      calc
        (T ^ (-(1 / 2 : ℝ))) ^ 2 =
            (T ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) :=
              (Real.rpow_natCast _ _).symm
        _ = T ^ ((-(1 / 2 : ℝ)) * (2 : ℝ)) :=
              (Real.rpow_mul hTpos.le _ _).symm
        _ = T⁻¹ := by
              rw [show (-(1 / 2 : ℝ)) * (2 : ℝ) = -1 by ring,
                Real.rpow_neg_one]
    rw [hpow]
    dsimp [T]
    field_simp
  have hLone : L ≤ 1 := by
    dsimp [L]
    linarith
  have hδσ : δ ≤ σ ^ 2 := by
    rw [hσsq]
    apply (le_div_iff₀ hLpos).mpr
    nlinarith
  have hscaleT : δ ^ (-(1 - θ)) ≤ T := by
    dsimp [T]
    apply (le_div_iff₀ hδ).mpr
    calc
      δ ^ (-(1 - θ)) * δ = δ ^ (-(1 - θ)) * δ ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = δ ^ (-(1 - θ) + 1) := (Real.rpow_add hδ _ _).symm
      _ = δ ^ θ := by
        congr 1
        ring
      _ ≤ L := by simpa [L] using hscale
  have hsE : (↑s : Set ℝ) ⊆ E := fun t ht => (hs ht).1
  have hEpos : E ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le zero_lt_one (hE ht).1
  have hEbound : E ⊆ Icc (0 : ℝ) 2 := by
    intro t ht
    exact ⟨zero_le_one.trans (hE ht).1, (hE ht).2⟩
  have hshort : ∀ t ∈ s, |t - a| * σ ^ 2 ≤ δ := by
    intro t ht
    have htI : t ∈ Icc a b := (hs ht).2
    have habs : |t - a| ≤ L := by
      have ht_le : t ≤ b := htI.2
      rw [abs_of_nonneg (sub_nonneg.mpr htI.1)]
      dsimp [L]
      linarith [ht_le]
    calc
      |t - a| * σ ^ 2 ≤ L * σ ^ 2 :=
        mul_le_mul_of_nonneg_right habs (sq_nonneg σ)
      _ = δ := by
        rw [hσsq]
        field_simp
  have ha_two : a ≤ 2 := hab.trans hb
  have hδbound : δ ≤ 1 / 20 := hδsmall.le.trans hδ₀small
  refine ⟨a, δ, σ, s, ha, ha_two, hδ, hδbound, hσ, hσone, hδσ,
    hsep, hsE, hEpos, hEbound, hshort, ?_⟩
  apply hgap hδ hδsmall hscaleT hsep
  simpa [T, L] using hpack

/-- The upper-spectrum clustered-radius obstruction in the form of the
cluster edge in Theorem 2.  The zero-Minkowski branch reduces to the usual
spherical-cap test; otherwise the preceding packing construction applies. -/
theorem upper_spectrum_cluster_test_of_expanded_functional
    {d : ℕ} (hd : 2 ≤ d)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    {β θ p q : ℝ}
    (hβ : 0 ≤ β ∧ β ≤ 1)
    (hθ : 0 ≤ θ ∧ θ < 1)
    (hspectrum : upperAssouadSpectrum E θ = β / (1 - θ))
    (hp : 0 < p) (hq : 1 ≤ q)
    (hbad :
      β / (β / (1 - θ)) / 2 * ((d : ℝ) - 1) +
          ((d : ℝ) - β - ((d : ℝ) - 1) *
              (β / (β / (1 - θ))) / 2) * q⁻¹ -
            (1 + (β / (β / (1 - θ))) / 2 * ((d : ℝ) - 1)) * p⁻¹ < 0) :
    FractalSphericalUnbounded d E p q := by
  have hd_one : 1 ≤ d := by omega
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  by_cases hβzero : β = 0
  · subst β
    apply fractalSphericalUnbounded_of_spherical_cap hd E hE hEne hp hqpos
    norm_num at hbad ⊢
    linarith
  · have hβpos : 0 < β := lt_of_le_of_ne hβ.1 (Ne.symm hβzero)
    have hden : 0 < 1 - θ := sub_pos.mpr hθ.2
    have hγpos : 0 < β / (1 - θ) := div_pos hβpos hden
    have hbad' : (d : ℝ) * q⁻¹ - (1 - θ) *
        ((β / (1 - θ)) * q⁻¹ -
          ((d : ℝ) - 1) / 2 * (1 - q⁻¹ - p⁻¹)) < p⁻¹ := by
      have hid :
          β / (β / (1 - θ)) / 2 * ((d : ℝ) - 1) +
              ((d : ℝ) - β - ((d : ℝ) - 1) *
                  (β / (β / (1 - θ))) / 2) * q⁻¹ -
                (1 + (β / (β / (1 - θ))) / 2 * ((d : ℝ) - 1)) * p⁻¹ =
            ((d : ℝ) * q⁻¹ - (1 - θ) *
              ((β / (1 - θ)) * q⁻¹ -
                ((d : ℝ) - 1) / 2 * (1 - q⁻¹ - p⁻¹))) - p⁻¹ := by
        field_simp
        ring
      rw [hid] at hbad
      linarith
    let n : ℕ := d - 1
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hncast : (n : ℝ) + 1 = (d : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hd_one
    have hncast' : (n : ℝ) = (d : ℝ) - 1 := by linarith
    have hbadn : ((n : ℝ) + 1) * q⁻¹ - (1 - θ) *
        ((β / (1 - θ)) * q⁻¹ -
          (n : ℝ) / 2 * (1 - q⁻¹ - p⁻¹)) < p⁻¹ := by
      rw [hncast, hncast']
      exact hbad'
    rcases spherical_cap_or_exists_cluster_exponent
      (n := n) (a := 1 - θ) (γ := β / (1 - θ))
      hn (sub_pos.mpr hθ.2) hγpos hp hq hbadn with hcap |
        ⟨α, hα0, hαγ, hk, hpower⟩
    · apply fractalSphericalUnbounded_of_spherical_cap hd E hE hEne hp hqpos
      simpa only [hncast] using hcap
    · simpa only [n, Nat.sub_add_cancel hd_one] using
        (fractalSphericalUnbounded_of_upper_spectrum_cluster_gap
          (n := n) (E := E) (θ := θ) (α := α)
          (γ := β / (1 - θ)) (p := p) (q := q)
          hn hE hθ.1 hθ.2 hspectrum hα0 hαγ hp hq hk hpower)

end

end Auto.Spherical.FractalDilations.ClusterSpectrumSharpness
end Former_ClusterSpectrumSharpness
