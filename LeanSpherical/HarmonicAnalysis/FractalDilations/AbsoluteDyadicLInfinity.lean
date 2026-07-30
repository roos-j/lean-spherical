/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.AbsoluteDyadic
import LeanSpherical.HarmonicAnalysis.SmoothDyadicPhysicalCore

/-!
# The scale-uniform `L∞ → L∞` endpoint for an absolute dyadic piece

The fixed-`j` interpolation in the proof of Theorem 1 needs an endpoint
which is uniform in the absolute frequency scale.  This file proves that
endpoint for the *literal* operator
`fractalDyadicBandpassMaximal`.  The proof is physical: the absolute
bandpass at level `j` is a dilation of its level-zero Schwartz multiplier,
whose inverse-Fourier kernel has scale-invariant `L¹` norm.  Normalized
spherical averages are contractions on bounded functions.

No abstract maximal or strong-type premise is used here.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory FourierTransform Metric Set
open scoped FourierTransform

noncomputable section

/-- The scale-independent `L∞` coefficient of the canonical absolute
dyadic bandpass.  It is the `L¹` norm of the physical level-zero kernel. -/
def absoluteDyadicBandpassLInfinityConstant
    {d : Nat} (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0) : Real :=
  ∫ y : Euclidean d,
    ‖(𝓕⁻ (absoluteDyadicBandpass phi hphiOne hphiZero 0) :
      SchwartzMap (Euclidean d) Complex) y‖

/-- The physical `L∞` coefficient is nonnegative. -/
theorem absoluteDyadicBandpassLInfinityConstant_nonneg
    {d : Nat} (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0) :
    0 ≤ absoluteDyadicBandpassLInfinityConstant phi hphiOne hphiZero := by
  unfold absoluteDyadicBandpassLInfinityConstant
  exact integral_nonneg fun _ => norm_nonneg _

/-- Every canonical absolute bandpass is exactly the dilation of the
level-zero canonical bandpass. -/
theorem absoluteDyadicBandpass_eq_levelZero_scaled
    {d : Nat} (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (j : Nat) (xi : Euclidean d) :
    absoluteDyadicBandpass phi hphiOne hphiZero j xi =
      absoluteDyadicBandpass phi hphiOne hphiZero 0
        ((_root_.LeanSpherical.HarmonicAnalysis.dyadicScale j)⁻¹ • xi) := by
  simpa only [_root_.LeanSpherical.HarmonicAnalysis.dyadicScale] using
    (smooth_dyadic_bandpass_eq_scaled_base phi
      (absoluteDyadicBandpass phi hphiOne hphiZero 0)
      (absoluteDyadicBandpass phi hphiOne hphiZero j)
      (absoluteDyadicBandpass_spec phi hphiOne hphiZero 0) j
      (absoluteDyadicBandpass_spec phi hphiOne hphiZero j) xi)

/-- The literal absolute dyadic bandpass projection has a scale-uniform
physical `L∞` bound. -/
theorem norm_dyadicBandpassProjection_absoluteDyadicBandpass_le_of_uniform_norm
    {d : Nat} (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (j : Nat) (f : SchwartzMap (Euclidean d) Complex)
    {C : Real} (hfbound : ∀ x, ‖f x‖ ≤ C) (x : Euclidean d) :
    ‖dyadicBandpassProjection (absoluteDyadicBandpass phi hphiOne hphiZero j) f x‖ ≤
      absoluteDyadicBandpassLInfinityConstant phi hphiOne hphiZero * C := by
  let R : Real := _root_.LeanSpherical.HarmonicAnalysis.dyadicScale j
  have hR : 0 < R := by
    dsimp only [R]
    exact _root_.LeanSpherical.HarmonicAnalysis.dyadicScale_pos j
  have hrewrite :
      (fun xi : Euclidean d =>
        absoluteDyadicBandpass phi hphiOne hphiZero j xi *
          𝓕 (f : Euclidean d -> Complex) xi) =
        fun xi : Euclidean d =>
          absoluteDyadicBandpass phi hphiOne hphiZero 0 (R⁻¹ • xi) *
            𝓕 (f : Euclidean d -> Complex) xi := by
    funext xi
    rw [absoluteDyadicBandpass_eq_levelZero_scaled phi hphiOne hphiZero j xi]
  rw [dyadicBandpassProjection_apply, hrewrite]
  have hphysical := norm_fourierInv_scaled_schwartz_multiplier_le
    (absoluteDyadicBandpass phi hphiOne hphiZero 0) f hR hfbound x
  simpa only [absoluteDyadicBandpassLInfinityConstant, mul_comm] using hphysical

/-- The fixed absolute dyadic fractal maximal piece has a literal,
scale-uniform `L∞ → L∞` endpoint. -/
theorem fractalDyadicBandpassMaximal_absoluteDyadicBandpass_le_of_uniform_norm
    {d : Nat} (hd : 0 < d) (E : Set Real) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (j : Nat) (f : SchwartzMap (Euclidean d) Complex)
    {C : Real} (hfbound : ∀ x, ‖f x‖ ≤ C) (x : Euclidean d) :
    fractalDyadicBandpassMaximal d E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) f x ≤
      absoluteDyadicBandpassLInfinityConstant phi hphiOne hphiZero * C := by
  let K : Real := absoluteDyadicBandpassLInfinityConstant phi hphiOne hphiZero
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hfbound 0)
  have hK : 0 ≤ K := by
    simpa only [K] using
      absoluteDyadicBandpassLInfinityConstant_nonneg phi hphiOne hphiZero
  have hCK : 0 ≤ K * C := mul_nonneg hK hC
  have hEpos : E ⊆ Ioi (0 : Real) := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one (hE hr).1
  have hprojection : ∀ y : Euclidean d,
      ‖dyadicBandpassProjection (absoluteDyadicBandpass phi hphiOne hphiZero j) f y‖ ≤
        K * C := by
    intro y
    simpa only [K] using
      norm_dyadicBandpassProjection_absoluteDyadicBandpass_le_of_uniform_norm
        phi hphiOne hphiZero j f hfbound y
  change (fractalSphericalMaximal d E
    (dyadicBandpassProjection (absoluteDyadicBandpass phi hphiOne hphiZero j) f :
      Euclidean d -> Complex) x).toReal ≤ K * C
  rw [← ENNReal.toReal_ofReal hCK]
  apply (ENNReal.toReal_le_toReal
    (fractalSphericalMaximal_ne_top hd E hEpos
      (dyadicBandpassProjection (absoluteDyadicBandpass phi hphiOne hphiZero j) f) x)
    ENNReal.ofReal_ne_top).mpr
  calc
    fractalSphericalMaximal d E
        (dyadicBandpassProjection (absoluteDyadicBandpass phi hphiOne hphiZero j) f :
          Euclidean d -> Complex) x ≤
        normalizedSphericalMaximal d
          (dyadicBandpassProjection (absoluteDyadicBandpass phi hphiOne hphiZero j) f :
            Euclidean d -> Complex) x :=
      fractalSphericalMaximal_le_normalizedSphericalMaximal E hEpos _ x
    _ ≤ ENNReal.ofReal (K * C) :=
      normalizedSphericalMaximal_le_of_norm_le hd _ x hprojection

/-- The same endpoint expressed using the genuine bounded-continuous norm
of a Schwartz input. -/
theorem fractalDyadicBandpassMaximal_absoluteDyadicBandpass_le_bounded_norm
    {d : Nat} (hd : 0 < d) (E : Set Real) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (j : Nat) (f : SchwartzMap (Euclidean d) Complex) (x : Euclidean d) :
    fractalDyadicBandpassMaximal d E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) f x ≤
      absoluteDyadicBandpassLInfinityConstant phi hphiOne hphiZero *
        ‖f.toBoundedContinuousFunction‖ := by
  apply fractalDyadicBandpassMaximal_absoluteDyadicBandpass_le_of_uniform_norm
    hd E hE phi hphiOne hphiZero j f
  intro y
  change ‖f.toBoundedContinuousFunction y‖ ≤ ‖f.toBoundedContinuousFunction‖
  exact BoundedContinuousFunction.norm_coe_le_norm _ _

/-- Bundled literal scale-uniform endpoint data for interpolation at a
fixed absolute dyadic frequency. -/
theorem fractalDyadicBandpassMaximal_literal_linf_endpoint_facts
    {d : Nat} (hd : 0 < d) (E : Set Real) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0) (j : Nat) :
    0 ≤ absoluteDyadicBandpassLInfinityConstant phi hphiOne hphiZero ∧
    (∀ g : SchwartzMap (Euclidean d) Complex, ∀ x,
      0 ≤ fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g x) ∧
    (∀ g h : SchwartzMap (Euclidean d) Complex, ∀ x,
      fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) (g + h) x ≤
      fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g x +
      fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) h x) ∧
    (∀ g : SchwartzMap (Euclidean d) Complex,
      AEMeasurable (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g) volume) ∧
    (∀ g : SchwartzMap (Euclidean d) Complex, ∀ x,
      fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g x ≤
      absoluteDyadicBandpassLInfinityConstant phi hphiOne hphiZero *
        ‖g.toBoundedContinuousFunction‖) := by
  have hEpos : E ⊆ Ioi (0 : Real) := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one (hE hr).1
  refine ⟨absoluteDyadicBandpassLInfinityConstant_nonneg phi hphiOne hphiZero,
    ?_, ?_, ?_, ?_⟩
  · intro g x
    exact fractalDyadicBandpassMaximal_nonneg E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) g x
  · intro g h x
    exact fractalDyadicBandpassMaximal_add_le hd E hEpos
      (absoluteDyadicBandpass phi hphiOne hphiZero j) g h x
  · intro g
    exact (measurable_fractalDyadicBandpassMaximal E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) g).aemeasurable
  · intro g x
    exact fractalDyadicBandpassMaximal_absoluteDyadicBandpass_le_bounded_norm
      hd E hE phi hphiOne hphiZero j g x

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
