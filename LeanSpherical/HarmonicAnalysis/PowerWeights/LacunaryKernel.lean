/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.GlobalEntropyAllScale
import LeanSpherical.HarmonicAnalysis.PowerWeights.GlobalUnweighted
import LeanSpherical.HarmonicAnalysis.PowerWeights.GlobalLacunaryCover
import LeanSpherical.HarmonicAnalysis.PowerWeights.SelectorEntropy

/-!
# The literal lacunary kernel layer

The all-scale restricted-dilation argument has one genuinely new unweighted
input: Calderón's estimate for one radius in each dyadic physical scale.  This
file fixes the actual operator to which that argument applies.  It deliberately
does not introduce an abstract maximal-operator interface: every definition
below is the displayed Fourier multiplier from the relative cutoff
decomposition.

The first results are the pointwise splitting and physical-space realization
which are used by the Calderón decomposition.  In particular, a lacunary
selector is identified exactly with the restricted operator on its range, so
the entropy-square and low-frequency estimates already proved for arbitrary
radius sets can be used without a second implementation.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory FourierTransform Metric Set
open scoped BigOperators BoundedContinuousFunction Convolution ENNReal FourierTransform NNReal

noncomputable section

/-- The literal finite relative cutoff over a dyadic lacunary selector. -/
def lacunaryRelativeCutoffSphericalMaximal
    (d : ℕ) (r : ℤ → PositiveRadius) (phi : SchwartzMap (Euclidean d) ℂ)
    (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) : ENNReal :=
  ⨆ k : ℤ, ENNReal.ofReal
    ‖𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (-(r k : ℝ) • ξ) *
        phi (((2 : ℝ) ^ N)⁻¹ • ((r k : ℝ) • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖

/-- The low relative-frequency piece over a dyadic lacunary selector. -/
def lacunaryRelativeLowpassSphericalMaximal
    (d : ℕ) (r : ℤ → PositiveRadius) (phi : SchwartzMap (Euclidean d) ℂ)
    (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) : ENNReal :=
  ⨆ k : ℤ, ENNReal.ofReal
    ‖𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (-(r k : ℝ) • ξ) * phi ((r k : ℝ) • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x‖

/-- The literal `j`th relative-frequency band over a dyadic lacunary
selector. -/
def lacunaryRelativeBandpassSphericalMaximal
    (d : ℕ) (r : ℤ → PositiveRadius) (phi : SchwartzMap (Euclidean d) ℂ)
    (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) : ENNReal :=
  ⨆ k : ℤ, ENNReal.ofReal
    ‖𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (-(r k : ℝ) • ξ) *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • ((r k : ℝ) • ξ)) -
          phi (((2 : ℝ) ^ j)⁻¹ • ((r k : ℝ) • ξ))) *
        𝓕 (f : Euclidean d → ℂ) ξ) x‖

/-- A lacunary cutoff is exactly the restricted cutoff over the range of its
selector.  This elementary identification is what lets the later finite and
infinite block arguments retain the actual selected radii. -/
theorem lacunaryRelativeCutoffSphericalMaximal_eq_restricted
    {d : ℕ} (r : ℤ → PositiveRadius) (phi : SchwartzMap (Euclidean d) ℂ)
    (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    lacunaryRelativeCutoffSphericalMaximal d r phi N f x =
      restrictedRelativeCutoffSphericalMaximal d (Set.range fun k => (r k : ℝ)) phi N f x := by
  apply le_antisymm
  · unfold lacunaryRelativeCutoffSphericalMaximal
      restrictedRelativeCutoffSphericalMaximal
    refine iSup_le fun k => ?_
    exact le_iSup
      (fun s : ↥(Set.range (fun k => (r k : ℝ)) ∩ Ioi (0 : ℝ)) =>
        ENNReal.ofReal
          ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-s.1 • ξ) *
              phi (((2 : ℝ) ^ N)⁻¹ • (s.1 • ξ)) *
                𝓕 (f : Euclidean d → ℂ) ξ) x‖)
      ⟨r k, ⟨⟨k, rfl⟩, (r k).2⟩⟩
  · unfold lacunaryRelativeCutoffSphericalMaximal
      restrictedRelativeCutoffSphericalMaximal
    refine iSup_le fun s => ?_
    rcases s.2.1 with ⟨k, hk⟩
    rw [← hk]
    exact le_iSup
      (fun k : ℤ => ENNReal.ofReal
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-(r k : ℝ) • ξ) *
            phi (((2 : ℝ) ^ N)⁻¹ • ((r k : ℝ) • ξ)) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖) k

/-- The lacunary lowpass is the restricted lowpass on the range of the
selector. -/
theorem lacunaryRelativeLowpassSphericalMaximal_eq_restricted
    {d : ℕ} (r : ℤ → PositiveRadius) (phi : SchwartzMap (Euclidean d) ℂ)
    (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    lacunaryRelativeLowpassSphericalMaximal d r phi f x =
      restrictedRelativeLowpassSphericalMaximal d (Set.range fun k => (r k : ℝ)) phi f x := by
  apply le_antisymm
  · unfold lacunaryRelativeLowpassSphericalMaximal
      restrictedRelativeLowpassSphericalMaximal
    refine iSup_le fun k => ?_
    exact le_iSup
      (fun s : ↥(Set.range (fun k => (r k : ℝ)) ∩ Ioi (0 : ℝ)) =>
        ENNReal.ofReal
          ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-s.1 • ξ) * phi (s.1 • ξ) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖)
      ⟨r k, ⟨⟨k, rfl⟩, (r k).2⟩⟩
  · unfold lacunaryRelativeLowpassSphericalMaximal
      restrictedRelativeLowpassSphericalMaximal
    refine iSup_le fun s => ?_
    rcases s.2.1 with ⟨k, hk⟩
    rw [← hk]
    exact le_iSup
      (fun k : ℤ => ENNReal.ofReal
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-(r k : ℝ) • ξ) * phi ((r k : ℝ) • ξ) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖) k

/-- The lacunary `j`th band is the restricted bandpass on the selector's
range. -/
theorem lacunaryRelativeBandpassSphericalMaximal_eq_restricted
    {d : ℕ} (r : ℤ → PositiveRadius) (phi : SchwartzMap (Euclidean d) ℂ)
    (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    lacunaryRelativeBandpassSphericalMaximal d r phi j f x =
      restrictedRelativeBandpassSphericalMaximal d (Set.range fun k => (r k : ℝ)) phi j f x := by
  apply le_antisymm
  · unfold lacunaryRelativeBandpassSphericalMaximal
      restrictedRelativeBandpassSphericalMaximal
    refine iSup_le fun k => ?_
    exact le_iSup
      (fun s : ↥(Set.range (fun k => (r k : ℝ)) ∩ Ioi (0 : ℝ)) =>
        ENNReal.ofReal
          ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-s.1 • ξ) *
              (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (s.1 • ξ)) -
                phi (((2 : ℝ) ^ j)⁻¹ • (s.1 • ξ))) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖)
      ⟨r k, ⟨⟨k, rfl⟩, (r k).2⟩⟩
  · unfold lacunaryRelativeBandpassSphericalMaximal
      restrictedRelativeBandpassSphericalMaximal
    refine iSup_le fun s => ?_
    rcases s.2.1 with ⟨k, hk⟩
    rw [← hk]
    exact le_iSup
      (fun k : ℤ => ENNReal.ofReal
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-(r k : ℝ) • ξ) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • ((r k : ℝ) • ξ)) -
              phi (((2 : ℝ) ^ j)⁻¹ • ((r k : ℝ) • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖) k

/-- The literal pointwise relative-cutoff decomposition survives after
choosing one radius in every dyadic scale. -/
theorem lacunaryRelativeCutoffSphericalMaximal_le_lowpass_add_band_sum
    {d : ℕ} (r : ℤ → PositiveRadius) (phi : SchwartzMap (Euclidean d) ℂ)
    (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    lacunaryRelativeCutoffSphericalMaximal d r phi N f x ≤
      lacunaryRelativeLowpassSphericalMaximal d r phi f x +
        ∑ j ∈ Finset.range N,
          lacunaryRelativeBandpassSphericalMaximal d r phi j f x := by
  rw [lacunaryRelativeCutoffSphericalMaximal_eq_restricted,
    lacunaryRelativeLowpassSphericalMaximal_eq_restricted]
  simp_rw [lacunaryRelativeBandpassSphericalMaximal_eq_restricted]
  exact restrictedRelativeCutoffSphericalMaximal_le_lowpass_add_band_sum
    (Set.range fun k => (r k : ℝ)) phi N f x

/-- One fixed Schwartz kernel realizes every selected high relative-frequency
piece.  The physical scale is exactly `2^j / r`; this is the kernel identity
that starts the Calderón decomposition of the lacunary maximal function. -/
theorem exists_relative_dyadic_bandpass_surface_kernel
    {d : ℕ} (phi : SchwartzMap (Euclidean d) ℂ) :
    ∃ psi : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        psi ξ = phi ((2 : ℝ)⁻¹ • ξ) - phi ξ) ∧
      ∀ (j : ℕ) {r : ℝ}, 0 < r → ∀ (f : SchwartzMap (Euclidean d) ℂ)
        (x : Euclidean d),
        𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r • ξ) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x =
          ∫ ω : Metric.sphere (0 : Euclidean d) 1,
            ((fun y : Euclidean d =>
              ((((2 : ℝ) ^ j)⁻¹ * r)⁻¹) ^ d •
                (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ)
                  ((((2 : ℝ) ^ j)⁻¹ * r)⁻¹ • y))
              ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (f : Euclidean d → ℂ)) (x + r • (ω : Euclidean d))
            ∂unitSurfaceMeasure d := by
  obtain ⟨psi, hpsi⟩ := exists_schwartzMap_smooth_dyadic_bandpass phi 0
  refine ⟨psi, ?_, ?_⟩
  · intro ξ
    simpa using hpsi ξ
  · intro j r hr f x
    have hmult : (fun ξ : Euclidean d =>
        surfaceFourier d (-r • ξ) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
          𝓕 (f : Euclidean d → ℂ) ξ) =
        fun ξ : Euclidean d =>
          surfaceFourier d (-r • ξ) *
            psi (((2 : ℝ) ^ j)⁻¹ • (r • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ := by
      funext ξ
      rw [hpsi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))]
      simp only [zero_add, pow_zero, pow_one, inv_one, one_smul]
      have hscale : (2 : ℝ)⁻¹ • (((2 : ℝ) ^ j)⁻¹ • (r • ξ)) =
          ((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ) := by
        rw [smul_smul]
        congr 1
        rw [pow_succ, mul_inv_rev]
      rw [hscale]
    rw [hmult]
    exact fourierInv_relative_surface_scaled_schwartz_multiplier_eq_surface_convolution
      psi f j hr x

/-- The physical kernel of one relative high-frequency piece is dominated by
its positive surface-smoothed kernel.  This is the pointwise input used when
Calderón's decomposition separates the selected physical scales. -/
theorem norm_relative_surface_scaled_schwartz_multiplier_le_positive_kernel
    {d : ℕ} (psi f : SchwartzMap (Euclidean d) ℂ) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (x : Euclidean d) :
    ‖𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (-r • ξ) *
        psi (((2 : ℝ) ^ j)⁻¹ • (r • ξ)) *
        𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
      ∫ y : Euclidean d, ‖f y‖ *
        (∫ ω : Metric.sphere (0 : Euclidean d) 1,
          ‖(((((2 : ℝ) ^ j)⁻¹ * r)⁻¹) ^ d) •
            (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ)
              (((((2 : ℝ) ^ j)⁻¹ * r)⁻¹) •
                (x + r • (ω : Euclidean d) - y))‖
          ∂unitSurfaceMeasure d) := by
  let s : ℝ := (((2 : ℝ) ^ j)⁻¹ * r)⁻¹
  have hs : 0 < s := by
    dsimp [s]
    positivity
  calc
    ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r • ξ) *
          psi (((2 : ℝ) ^ j)⁻¹ • (r • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ =
        ‖sphericalAverage d
          (fun z : Euclidean d =>
            ((fun y : Euclidean d => s ^ d •
              (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ) (s • y))
              ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (f : Euclidean d → ℂ)) z) r x‖ := by
          rw [fourierInv_relative_surface_scaled_schwartz_multiplier_eq_surface_convolution
            psi f j hr x]
          rfl
    _ ≤ ∫ y : Euclidean d, ‖f y‖ *
        (∫ ω : Metric.sphere (0 : Euclidean d) 1,
          ‖s ^ d • (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ)
            (s • (x + r • (ω : Euclidean d) - y))‖
          ∂unitSurfaceMeasure d) :=
        norm_sphericalAverage_scaled_schwartz_convolution_le (𝓕⁻ psi) f hs x
    _ = _ := by rfl

/-- After choosing the fixed dyadic difference kernel, every literal
lacunary band is bounded by the same positive surface-smoothed kernel at its
own physical scale. -/
theorem exists_relative_dyadic_bandpass_positive_kernel_majorant
    {d : ℕ} (phi : SchwartzMap (Euclidean d) ℂ) :
    ∃ psi : SchwartzMap (Euclidean d) ℂ,
      (∀ ξ : Euclidean d,
        psi ξ = phi ((2 : ℝ)⁻¹ • ξ) - phi ξ) ∧
      ∀ (j : ℕ) {r : ℝ}, 0 < r → ∀ (f : SchwartzMap (Euclidean d) ℂ)
        (x : Euclidean d),
        ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r • ξ) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
          ∫ y : Euclidean d, ‖f y‖ *
            (∫ ω : Metric.sphere (0 : Euclidean d) 1,
              ‖(((((2 : ℝ) ^ j)⁻¹ * r)⁻¹) ^ d) •
                (𝓕⁻ psi : SchwartzMap (Euclidean d) ℂ)
                  (((((2 : ℝ) ^ j)⁻¹ * r)⁻¹) •
                    (x + r • (ω : Euclidean d) - y))‖
              ∂unitSurfaceMeasure d) := by
  obtain ⟨psi, hpsi⟩ := exists_schwartzMap_smooth_dyadic_bandpass phi 0
  refine ⟨psi, ?_, ?_⟩
  · intro ξ
    simpa using hpsi ξ
  · intro j r hr f x
    have hmult : (fun ξ : Euclidean d =>
        surfaceFourier d (-r • ξ) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) =
        fun ξ : Euclidean d =>
          surfaceFourier d (-r • ξ) *
            psi (((2 : ℝ) ^ j)⁻¹ • (r • ξ)) *
            𝓕 (f : Euclidean d → ℂ) ξ := by
      funext ξ
      rw [hpsi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))]
      simp only [zero_add, pow_zero, pow_one, inv_one, one_smul]
      have hscale : (2 : ℝ)⁻¹ • (((2 : ℝ) ^ j)⁻¹ • (r • ξ)) =
          ((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ) := by
        rw [smul_smul]
        congr 1
        rw [pow_succ, mul_inv_rev]
      rw [hscale]
    rw [hmult]
    exact norm_relative_surface_scaled_schwartz_multiplier_le_positive_kernel
      psi f j hr x

/-- The entropy-square endpoint specializes directly to a dyadic lacunary
selector.  This is the `L²` side of the later lacunary interpolation; the
Calderón argument supplies the complementary near-`L¹` estimate. -/
theorem memLp_two_lacunaryRelativeBandpass_global_of_unitEntropy
    {d : Nat} (hd : 2 ≤ d) (C0 C1 : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ xi : Euclidean (d + 1), 1 ≤ ‖xi‖ →
      ‖surfaceFourier (d + 1) xi‖ ≤ C0 / ‖xi‖ ^ ((d : ℝ) / 2))
    (hderiv : ∀ xi : Euclidean (d + 1), ∀ s : ℝ, 1 ≤ ‖xi‖ →
      s ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun t : ℝ => surfaceFourier (d + 1) (t • xi)) s‖ ≤
        C1 / ‖xi‖ ^ ((d : ℝ) / 2 - 1))
    (phi : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphi_norm : ∀ xi, ‖phi xi‖ ≤ 1)
    (j : Nat) (r : ℤ → PositiveRadius)
    (δ : ℝ≥0) (N : ℕ)
    (hN : unitMultiplicativeEntropy (Set.range fun k => (r k : ℝ)) δ ≤ N)
    (hδ : Real.log 2 * (δ : ℝ) ≤ 1)
    (f : SchwartzMap (Euclidean (d + 1)) ℂ) :
    MemLp (fun x =>
      (lacunaryRelativeBandpassSphericalMaximal (d + 1) r phi j f x).toReal)
        2 volume ∧
      (∫ x : Euclidean (d + 1),
        ‖(lacunaryRelativeBandpassSphericalMaximal (d + 1) r phi j f x).toReal‖ ^ 2) ≤
        24 * (N : ℝ) *
          (2 * ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
            2 * (8 * Real.log 2 * (δ : ℝ)) ^ 2 *
              (2 * (((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
                (12 * C0 *
                  ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) phi).toBoundedContinuousFunction‖) /
                  (dyadicScale j) ^ ((d : ℝ) / 2)))) ^ 2) *
          (∫ x : Euclidean (d + 1), ‖f x‖ ^ 2) := by
  simpa only [lacunaryRelativeBandpassSphericalMaximal_eq_restricted] using
    memLp_two_restrictedRelativeBandpassSphericalMaximal_global_of_unitEntropy
      hd C0 C1 hC0 hC1 hdecay hderiv phi f hphi_one hphi_zero hphi_norm j
      (Set.range fun k => (r k : ℝ)) (by
        refine ⟨r 0, ⟨0, rfl⟩⟩) (by
        intro s hs
        rcases hs with ⟨k, rfl⟩
        exact (r k).2)
      δ N hN hδ

/-- A literal dyadic lacunary selector satisfies the uniform square-function
endpoint for every relative-frequency band.  Its local entropy is bounded by
three with no condition on the selector beyond bounded-ratio lacunarity. -/
theorem memLp_two_lacunaryRelativeBandpass_global_of_isDyadicLacunaryRadiusSelector
    {d : Nat} (hd : 2 ≤ d) (C0 C1 : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ xi : Euclidean (d + 1), 1 ≤ ‖xi‖ →
      ‖surfaceFourier (d + 1) xi‖ ≤ C0 / ‖xi‖ ^ ((d : ℝ) / 2))
    (hderiv : ∀ xi : Euclidean (d + 1), ∀ s : ℝ, 1 ≤ ‖xi‖ →
      s ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun t : ℝ => surfaceFourier (d + 1) (t • xi)) s‖ ≤
        C1 / ‖xi‖ ^ ((d : ℝ) / 2 - 1))
    (phi : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphi_norm : ∀ xi, ‖phi xi‖ ≤ 1)
    (j : Nat) (r : ℤ → PositiveRadius) (hr : IsDyadicLacunaryRadiusSelector r)
    (f : SchwartzMap (Euclidean (d + 1)) ℂ) :
    MemLp (fun x =>
      (lacunaryRelativeBandpassSphericalMaximal (d + 1) r phi j f x).toReal)
        2 volume ∧
      (∫ x : Euclidean (d + 1),
        ‖(lacunaryRelativeBandpassSphericalMaximal (d + 1) r phi j f x).toReal‖ ^ 2) ≤
        144 * ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 *
          (∫ x : Euclidean (d + 1), ‖f x‖ ^ 2) := by
  have h := memLp_two_lacunaryRelativeBandpass_global_of_unitEntropy
    hd C0 C1 hC0 hC1 hdecay hderiv phi hphi_one hphi_zero hphi_norm j r 0 3
    (unitMultiplicativeEntropy_range_le_three_of_isDyadicLacunaryRadiusSelector r hr 0)
    (by norm_num) f
  refine ⟨h.1, ?_⟩
  calc
    (∫ x : Euclidean (d + 1),
      ‖(lacunaryRelativeBandpassSphericalMaximal (d + 1) r phi j f x).toReal‖ ^ 2) ≤
        24 * 3 * (2 * ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2) *
          (∫ x : Euclidean (d + 1), ‖f x‖ ^ 2) := by
      simpa using h.2
    _ = 144 * ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 *
          (∫ x : Euclidean (d + 1), ‖f x‖ ^ 2) := by ring

end

end LeanSpherical.HarmonicAnalysis
