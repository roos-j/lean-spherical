/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Convolution

/-!
# Core surface-measure and Euclidean analytic prerequisites

This module consolidates the concrete surface measure, its elementary
geometry and continuity properties, and the Euclidean analytic lemmas used
throughout the spherical maximal development.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- The real Euclidean space of dimension `d`. -/
abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The (unnormalized) surface measure on the Euclidean unit sphere. -/
def unitSurfaceMeasure (d : ℕ) : Measure (sphere (0 : Euclidean d) 1) :=
  (volume : Measure (Euclidean d)).toSphere

instance (d : ℕ) : IsFiniteMeasure (unitSurfaceMeasure d) := by
  unfold unitSurfaceMeasure
  infer_instance

/-- The total mass of `unitSurfaceMeasure` is the dimension times the volume
of the Euclidean unit ball. -/
theorem unitSurfaceMeasure_real_univ (d : ℕ) :
    (unitSurfaceMeasure d).real univ =
      (d : ℝ) * (volume : Measure (Euclidean d)).real (ball 0 1) := by
  simp [unitSurfaceMeasure]

/-- The oscillatory phase in the Fourier transform of surface measure. -/
def surfacePhase (d : ℕ) (ξ : Euclidean d) (ω : sphere (0 : Euclidean d) 1) : ℂ :=
  ((-2 * Real.pi * inner ℝ (ω : Euclidean d) ξ : ℝ) : ℂ) * Complex.I

/-- The Fourier--Stieltjes transform of the Euclidean unit-sphere measure. -/
def surfaceFourier (d : ℕ) (ξ : Euclidean d) : ℂ :=
  ∫ ω : sphere (0 : Euclidean d) 1,
    Complex.exp (surfacePhase d ξ ω) ∂unitSurfaceMeasure d

/-- The oscillatory kernel defining `surfaceFourier` has modulus one. -/
theorem norm_surfaceFourier_kernel (d : ℕ) (ξ : Euclidean d)
    (ω : sphere (0 : Euclidean d) 1) :
    ‖Complex.exp (surfacePhase d ξ ω)‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- The elementary Fourier--Stieltjes mass bound for surface measure. -/
theorem norm_surfaceFourier_le_surfaceMass (d : ℕ) (ξ : Euclidean d) :
    ‖surfaceFourier d ξ‖ ≤ (unitSurfaceMeasure d).real univ := by
  unfold surfaceFourier
  calc
    ‖∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d ξ ω) ∂unitSurfaceMeasure d‖
        ≤ ∫ ω : sphere (0 : Euclidean d) 1,
          ‖Complex.exp (surfacePhase d ξ ω)‖ ∂unitSurfaceMeasure d :=
      norm_integral_le_integral_norm _
    _ = ∫ _ : sphere (0 : Euclidean d) 1, (1 : ℝ) ∂unitSurfaceMeasure d := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [norm_surfaceFourier_kernel]
    _ = (unitSurfaceMeasure d).real univ := by simp

/-- At the origin the Fourier transform is the total surface mass. -/
theorem surfaceFourier_zero (d : ℕ) :
    surfaceFourier d 0 = ((unitSurfaceMeasure d).real univ : ℂ) := by
  simp [surfaceFourier, surfacePhase]

/-- The unnormalized spherical average of a complex-valued function. -/
def sphericalAverage (d : ℕ) (f : Euclidean d → ℂ) (r : ℝ) (x : Euclidean d) : ℂ :=
  ∫ ω : sphere (0 : Euclidean d) 1,
    f (x + r • (ω : Euclidean d)) ∂unitSurfaceMeasure d

/-- The total mass used to normalize the geometric surface measure. -/
def surfaceMass (d : ℕ) : ℝ :=
  (unitSurfaceMeasure d).real univ

/-- The normalized spherical average used in the conventional statement of
Stein's theorem.  In the relevant dimensions the surface mass is positive;
the inverse also gives a total definition in every dimension. -/
def normalizedSphericalAverage (d : ℕ) (f : Euclidean d → ℂ)
    (r : ℝ) (x : Euclidean d) : ℂ :=
  ((surfaceMass d)⁻¹ : ℂ) * sphericalAverage d f r x

/-- At radius zero, the unnormalized spherical average is surface mass times
the function value. -/
theorem sphericalAverage_zero (d : ℕ) (f : Euclidean d → ℂ) (x : Euclidean d) :
    sphericalAverage d f 0 x = ((unitSurfaceMeasure d).real univ : ℂ) * f x := by
  simp [sphericalAverage, mul_comm]

/-- The spherical maximal function over positive radii, represented in `ℝ≥0∞`
so that its supremum is always defined. -/
def sphericalMaximal (d : ℕ) (f : Euclidean d → ℂ) (x : Euclidean d) : ENNReal :=
  ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖sphericalAverage d f r.1 x‖

/-- The normalized spherical maximal operator over positive radii. -/
def normalizedSphericalMaximal (d : ℕ) (f : Euclidean d → ℂ)
    (x : Euclidean d) : ENNReal :=
  ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖normalizedSphericalAverage d f r.1 x‖

/-- Each individual spherical average is dominated by the spherical maximal
function. -/
theorem sphericalAverage_le_sphericalMaximal (d : ℕ) (f : Euclidean d → ℂ)
    (r : ℝ) (hr : 0 < r) (x : Euclidean d) :
    ENNReal.ofReal ‖sphericalAverage d f r x‖ ≤ sphericalMaximal d f x := by
  exact le_iSup
    (fun s : Ioi (0 : ℝ) => ENNReal.ofReal ‖sphericalAverage d f s.1 x‖)
    ⟨r, hr⟩

/-- Each normalized average is dominated by the normalized maximal function. -/
theorem normalizedSphericalAverage_le_normalizedSphericalMaximal
    (d : ℕ) (f : Euclidean d → ℂ) (r : ℝ) (hr : 0 < r) (x : Euclidean d) :
    ENNReal.ofReal ‖normalizedSphericalAverage d f r x‖ ≤
      normalizedSphericalMaximal d f x := by
  exact le_iSup
    (fun s : Ioi (0 : ℝ) => ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 x‖)
    ⟨r, hr⟩

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- In every positive dimension, the concrete surface measure has positive
total mass. -/
theorem unitSurfaceMeasure_univ_pos {d : ℕ} (hd : 0 < d) :
    0 < unitSurfaceMeasure d univ := by
  rw [Measure.measure_univ_pos]
  unfold unitSurfaceMeasure
  let i : Fin d := ⟨0, hd⟩
  letI : Nonempty (Fin d) := ⟨i⟩
  exact Measure.toSphere_ne_zero (volume : Measure (Euclidean d))

/-- The normalizing mass of the unit sphere is positive in every positive
dimension. -/
theorem surfaceMass_pos {d : ℕ} (hd : 0 < d) : 0 < surfaceMass d := by
  unfold surfaceMass
  exact ENNReal.toReal_pos (ne_of_gt (unitSurfaceMeasure_univ_pos hd))
    (measure_ne_top _ _)

/-- The normalizing mass can be inverted in every positive dimension. -/
theorem surfaceMass_ne_zero {d : ℕ} (hd : 0 < d) : surfaceMass d ≠ 0 :=
  ne_of_gt (surfaceMass_pos hd)

/-- The concrete surface average is translation covariant. -/
theorem sphericalAverage_translate (d : ℕ) (f : Euclidean d → ℂ) (r : ℝ)
    (a x : Euclidean d) :
    sphericalAverage d (fun y => f (a + y)) r x = sphericalAverage d f r (a + x) := by
  unfold sphericalAverage
  apply integral_congr_ae
  filter_upwards with ω
  simp only [add_assoc]

/-- Spherical averaging commutes with simultaneous Euclidean dilations of the
input and radius. -/
theorem sphericalAverage_dilate (d : ℕ) (f : Euclidean d → ℂ) (a r : ℝ)
    (x : Euclidean d) :
    sphericalAverage d (fun y => f (a • y)) r x =
      sphericalAverage d f (a * r) (a • x) := by
  unfold sphericalAverage
  apply integral_congr_ae
  filter_upwards with ω
  simp only [smul_add, smul_smul]

/-- The mass-normalized spherical average has the same simultaneous dilation
covariance. -/
theorem normalizedSphericalAverage_dilate (d : ℕ) (f : Euclidean d → ℂ)
    (a r : ℝ) (x : Euclidean d) :
    normalizedSphericalAverage d (fun y => f (a • y)) r x =
      normalizedSphericalAverage d f (a * r) (a • x) := by
  unfold normalizedSphericalAverage
  rw [sphericalAverage_dilate]

/-- Dilation identifies the literal compact-radius maximal norm on `[1, 2]`
with the corresponding norm on `[a, 2a]`. -/
theorem iSup_ennreal_norm_sphericalAverage_dilate_local
    {d : ℕ} (f : Euclidean d → ℂ) {a : ℝ} (ha : 0 < a) (x : Euclidean d) :
    (⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal ‖sphericalAverage d (fun y => f (a • y)) r.1 x‖) =
      ⨆ s : Icc a (a * 2),
        ENNReal.ofReal ‖sphericalAverage d f s.1 (a • x)‖ := by
  apply le_antisymm
  · apply iSup_le
    intro r
    let s : Icc a (a * 2) := ⟨a * r.1,
      by simpa using mul_le_mul_of_nonneg_left r.2.1 ha.le,
      by
        calc
          a * r.1 ≤ a * 2 := mul_le_mul_of_nonneg_left r.2.2 ha.le
          _ = a * 2 := rfl⟩
    rw [sphericalAverage_dilate d f a r.1 x]
    exact le_iSup (fun s : Icc a (a * 2) =>
      ENNReal.ofReal ‖sphericalAverage d f s.1 (a • x)‖) s
  · apply iSup_le
    intro s
    let r : Icc (1 : ℝ) 2 := ⟨s.1 / a,
      (le_div_iff₀ ha).2 (by simpa using s.2.1),
      (div_le_iff₀ ha).2 (by simpa [mul_comm] using s.2.2)⟩
    have hmul : a * r.1 = s.1 := by
      dsimp only [r]
      field_simp
    calc
      ENNReal.ofReal ‖sphericalAverage d f s.1 (a • x)‖ =
          ENNReal.ofReal ‖sphericalAverage d (fun y => f (a • y)) r.1 x‖ := by
        rw [sphericalAverage_dilate d f a r.1 x, hmul]
      _ ≤ ⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal ‖sphericalAverage d (fun y => f (a • y)) r.1 x‖ :=
        le_iSup (fun r : Icc (1 : ℝ) 2 =>
          ENNReal.ofReal ‖sphericalAverage d (fun y => f (a • y)) r.1 x‖) r

/-- The same local-radius dilation identity for the mass-normalized spherical
averages used in Stein's theorem. -/
theorem iSup_ennreal_norm_normalizedSphericalAverage_dilate_local
    {d : ℕ} (f : Euclidean d → ℂ) {a : ℝ} (ha : 0 < a) (x : Euclidean d) :
    (⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖) =
      ⨆ s : Icc a (a * 2),
        ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 (a • x)‖ := by
  apply le_antisymm
  · apply iSup_le
    intro r
    let s : Icc a (a * 2) := ⟨a * r.1,
      by simpa using mul_le_mul_of_nonneg_left r.2.1 ha.le,
      by
        calc
          a * r.1 ≤ a * 2 := mul_le_mul_of_nonneg_left r.2.2 ha.le
          _ = a * 2 := rfl⟩
    rw [normalizedSphericalAverage_dilate d f a r.1 x]
    exact le_iSup (fun s : Icc a (a * 2) =>
      ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 (a • x)‖) s
  · apply iSup_le
    intro s
    let r : Icc (1 : ℝ) 2 := ⟨s.1 / a,
      (le_div_iff₀ ha).2 (by simpa using s.2.1),
      (div_le_iff₀ ha).2 (by simpa [mul_comm] using s.2.2)⟩
    have hmul : a * r.1 = s.1 := by
      dsimp only [r]
      field_simp
    calc
      ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 (a • x)‖ =
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖ := by
        rw [normalizedSphericalAverage_dilate d f a r.1 x, hmul]
      _ ≤ ⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖ :=
        le_iSup (fun r : Icc (1 : ℝ) 2 =>
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖) r

/-- The positive-radius normalized maximal function is the supremum of its
literal dyadic radius blocks. -/
theorem normalizedSphericalMaximal_eq_iSup_dyadic_radius_blocks
    {d : ℕ} (f : Euclidean d → ℂ) (x : Euclidean d) :
    normalizedSphericalMaximal d f x =
      ⨆ k : ℤ, ⨆ r : Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)),
        ENNReal.ofReal ‖normalizedSphericalAverage d f r.1 x‖ := by
  unfold normalizedSphericalMaximal
  apply le_antisymm
  · apply iSup_le
    intro t
    obtain ⟨k, hk⟩ := exists_mem_Ico_zpow t.2 (by norm_num : (1 : ℝ) < 2)
    let r : Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) := ⟨t.1, hk.1, hk.2.le⟩
    exact le_iSup_of_le k
      (le_iSup (fun r : Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) =>
        ENNReal.ofReal ‖normalizedSphericalAverage d f r.1 x‖) r)
  · apply iSup_le
    intro k
    apply iSup_le
    intro r
    have hr : 0 < r.1 :=
      lt_of_lt_of_le (zpow_pos (by norm_num : (0 : ℝ) < 2) k) r.2.1
    exact le_iSup (fun t : Ioi (0 : ℝ) =>
      ENNReal.ofReal ‖normalizedSphericalAverage d f t.1 x‖) ⟨r.1, hr⟩

/-- After splitting radii into dyadic blocks, every block is exactly a unit
radius block applied to the correspondingly dilated input. -/
theorem normalizedSphericalMaximal_eq_iSup_dyadic_local
    {d : ℕ} (f : Euclidean d → ℂ) (x : Euclidean d) :
    normalizedSphericalMaximal d f x =
      ⨆ k : ℤ, ⨆ r : Icc (1 : ℝ) 2,
        ENNReal.ofReal ‖normalizedSphericalAverage d
          (fun y => f (((2 : ℝ) ^ k) • y)) r.1 (((2 : ℝ) ^ k)⁻¹ • x)‖ := by
  rw [normalizedSphericalMaximal_eq_iSup_dyadic_radius_blocks]
  apply iSup_congr
  intro k
  let a : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by
    dsimp [a]
    exact zpow_pos (by norm_num) _
  have hscale : a * 2 = (2 : ℝ) ^ (k + 1) := by
    dsimp [a]
    calc
      (2 : ℝ) ^ k * 2 = (2 : ℝ) ^ k * (2 : ℝ) ^ (1 : ℤ) := by norm_num
      _ = (2 : ℝ) ^ (k + 1) := (zpow_add₀ (by norm_num) k 1).symm
  have hlocal :=
    iSup_ennreal_norm_normalizedSphericalAverage_dilate_local f ha (a⁻¹ • x)
  rw [hscale] at hlocal
  simpa only [a, smul_smul, mul_inv_cancel₀ ha.ne', one_smul] using hlocal.symm

/-- Positive dilation conjugates the literal normalized maximal function to
itself. -/
theorem normalizedSphericalMaximal_dilate
    {d : ℕ} (f : Euclidean d → ℂ) {a : ℝ} (ha : 0 < a) (x : Euclidean d) :
    normalizedSphericalMaximal d (fun y => f (a • y)) x =
      normalizedSphericalMaximal d f (a • x) := by
  unfold normalizedSphericalMaximal
  apply le_antisymm
  · apply iSup_le
    intro r
    let s : Ioi (0 : ℝ) := ⟨a * r.1, mul_pos ha r.2⟩
    rw [normalizedSphericalAverage_dilate]
    exact le_iSup (fun s : Ioi (0 : ℝ) =>
      ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 (a • x)‖) s
  · apply iSup_le
    intro s
    let r : Ioi (0 : ℝ) := ⟨s.1 / a, div_pos s.2 ha⟩
    have hmul : a * r.1 = s.1 := by
      dsimp only [r]
      field_simp
    calc
      ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 (a • x)‖ =
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖ := by
        rw [normalizedSphericalAverage_dilate d f a r.1 x, hmul]
      _ ≤ ⨆ r : Ioi (0 : ℝ),
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖ :=
        le_iSup (fun r : Ioi (0 : ℝ) =>
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖) r

/-- The concrete normalized maximal function is subadditive on continuous
inputs. -/
theorem normalizedSphericalMaximal_add_le
    {d : ℕ} (f g : Euclidean d → ℂ) (hf : Continuous f) (hg : Continuous g)
    (x : Euclidean d) :
    normalizedSphericalMaximal d (f + g) x ≤
      normalizedSphericalMaximal d f x + normalizedSphericalMaximal d g x := by
  unfold normalizedSphericalMaximal
  apply iSup_le
  intro r
  have hint (h : Euclidean d → ℂ) (hh : Continuous h) : Integrable
      (fun ω : sphere (0 : Euclidean d) 1 => h (x + r.1 • (ω : Euclidean d)))
      (unitSurfaceMeasure d) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hh.comp
        ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => x).add
          ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => r.1).smul
            continuous_subtype_val))
    · exact HasCompactSupport.of_compactSpace _
  have havg : normalizedSphericalAverage d (f + g) r.1 x =
      normalizedSphericalAverage d f r.1 x + normalizedSphericalAverage d g r.1 x := by
    unfold normalizedSphericalAverage sphericalAverage
    change (surfaceMass d : ℂ)⁻¹ *
        ∫ ω : sphere (0 : Euclidean d) 1,
          (f (x + r.1 • (ω : Euclidean d)) + g (x + r.1 • (ω : Euclidean d)))
          ∂unitSurfaceMeasure d = _
    rw [MeasureTheory.integral_add (hint f hf) (hint g hg), mul_add]
  rw [havg]
  calc
    ENNReal.ofReal ‖normalizedSphericalAverage d f r.1 x +
        normalizedSphericalAverage d g r.1 x‖ ≤
        ENNReal.ofReal (‖normalizedSphericalAverage d f r.1 x‖ +
          ‖normalizedSphericalAverage d g r.1 x‖) :=
      ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖normalizedSphericalAverage d f r.1 x‖ +
        ENNReal.ofReal ‖normalizedSphericalAverage d g r.1 x‖ := by
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    _ ≤ normalizedSphericalMaximal d f x + normalizedSphericalMaximal d g x := by
      gcongr
      · exact normalizedSphericalAverage_le_normalizedSphericalMaximal d f r.1 r.2 x
      · exact normalizedSphericalAverage_le_normalizedSphericalMaximal d g r.1 r.2 x

/-- The Fourier phase is homogeneous in the frequency variable. -/
theorem surfacePhase_smul (d : ℕ) (a : ℝ) (ξ : Euclidean d)
    (ω : sphere (0 : Euclidean d) 1) :
    surfacePhase d (a • ξ) ω = (a : ℂ) * surfacePhase d ξ ω := by
  simp only [surfacePhase, inner_smul_right]
  push_cast
  ring

/-- Scaling the frequency only scales the phase inside the concrete
Fourier--Stieltjes integral. -/
theorem surfaceFourier_smul (d : ℕ) (a : ℝ) (ξ : Euclidean d) :
    surfaceFourier d (a • ξ) =
      ∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp ((a : ℂ) * surfacePhase d ξ ω) ∂unitSurfaceMeasure d := by
  unfold surfaceFourier
  apply integral_congr_ae
  filter_upwards with ω
  rw [surfacePhase_smul]

/-- The normalized average fixes every function at radius zero. -/
theorem normalizedSphericalAverage_zero {d : ℕ} (hd : 0 < d)
    (f : Euclidean d → ℂ) (x : Euclidean d) :
    normalizedSphericalAverage d f 0 x = f x := by
  rw [normalizedSphericalAverage, sphericalAverage_zero]
  change (↑(surfaceMass d) : ℂ)⁻¹ * ((↑(surfaceMass d) : ℂ) * f x) = f x
  have hmass : (↑(surfaceMass d) : ℂ) ≠ 0 := by
    exact_mod_cast surfaceMass_ne_zero hd
  rw [← mul_assoc, inv_mul_cancel₀ hmass, one_mul]

/-- The unnormalized average of a constant is its surface mass times that
constant. -/
theorem sphericalAverage_const (d : ℕ) (c : ℂ) (r : ℝ) (x : Euclidean d) :
    sphericalAverage d (fun _ => c) r x = (surfaceMass d : ℂ) * c := by
  simp [sphericalAverage, surfaceMass]

/-- The normalized average preserves constants in every positive dimension. -/
theorem normalizedSphericalAverage_const {d : ℕ} (hd : 0 < d) (c : ℂ)
    (r : ℝ) (x : Euclidean d) :
    normalizedSphericalAverage d (fun _ => c) r x = c := by
  rw [normalizedSphericalAverage, sphericalAverage_const]
  simp [surfaceMass_ne_zero hd]

/-- The elementary `L∞` bound for the unnormalized spherical average. -/
theorem norm_sphericalAverage_le_surfaceMass_mul (d : ℕ) (f : Euclidean d → ℂ)
    (r : ℝ) (x : Euclidean d) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ‖sphericalAverage d f r x‖ ≤ C * surfaceMass d := by
  unfold sphericalAverage
  apply norm_integral_le_of_norm_le_const
  filter_upwards with ω
  exact hC _

/-- The normalized spherical average is an `L∞` contraction. -/
theorem norm_normalizedSphericalAverage_le {d : ℕ} (hd : 0 < d)
    (f : Euclidean d → ℂ) (r : ℝ) (x : Euclidean d) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) :
    ‖normalizedSphericalAverage d f r x‖ ≤ C := by
  have hmass_pos : 0 < surfaceMass d := surfaceMass_pos hd
  have hmass_nonneg : 0 ≤ surfaceMass d := hmass_pos.le
  calc
    ‖normalizedSphericalAverage d f r x‖ =
        (surfaceMass d)⁻¹ * ‖sphericalAverage d f r x‖ := by
      rw [normalizedSphericalAverage, norm_mul]
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hmass_nonneg]
    _ ≤ (surfaceMass d)⁻¹ * (C * surfaceMass d) := by
      exact mul_le_mul_of_nonneg_left
        (norm_sphericalAverage_le_surfaceMass_mul d f r x hC)
        (inv_nonneg.mpr hmass_nonneg)
    _ = C := by
      calc
        (surfaceMass d)⁻¹ * (C * surfaceMass d) =
            C * ((surfaceMass d)⁻¹ * surfaceMass d) := by ring
        _ = C := by rw [inv_mul_cancel₀ (surfaceMass_ne_zero hd), mul_one]

/-- The normalized spherical maximal function satisfies the pointwise `L∞`
bound inherited from the concrete average. -/
theorem normalizedSphericalMaximal_le_of_norm_le {d : ℕ} (hd : 0 < d)
    (f : Euclidean d → ℂ) (x : Euclidean d) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) :
    normalizedSphericalMaximal d f x ≤ ENNReal.ofReal C := by
  unfold normalizedSphericalMaximal
  apply iSup_le
  intro r
  exact ENNReal.ofReal_le_ofReal
    (norm_normalizedSphericalAverage_le hd f r x hC)

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- The oscillatory phase is jointly continuous in frequency and the point on
the unit sphere. -/
theorem continuous_surfacePhase (d : ℕ) :
    Continuous (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
      surfacePhase d p.1 p.2) := by
  unfold surfacePhase
  fun_prop

/-- The Fourier--Stieltjes transform of the concrete unit-sphere measure is
continuous. -/
theorem continuous_surfaceFourier (d : ℕ) : Continuous (surfaceFourier d) := by
  unfold surfaceFourier
  apply continuous_of_dominated (F := fun ξ ω => Complex.exp (surfacePhase d ξ ω))
    (bound := fun _ => (1 : ℝ))
  · intro ξ
    exact ((continuous_surfacePhase d).comp
      ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => ξ).prodMk
        continuous_id)).cexp.aestronglyMeasurable
  · intro ξ
    filter_upwards with ω
    exact norm_surfaceFourier_kernel d ξ ω |>.le
  · exact integrable_const _
  · filter_upwards with ω
    exact ((continuous_surfacePhase d).comp
      (continuous_id.prodMk
        (continuous_const : Continuous fun _ : Euclidean d => ω))).cexp

/-- Restricting the concrete Fourier transform to any radial line gives a
continuous one-variable function. -/
theorem continuous_surfaceFourier_radial (d : ℕ) (ξ : Euclidean d) :
    Continuous (fun r : ℝ => surfaceFourier d (r • ξ)) := by
  exact (continuous_surfaceFourier d).comp (continuous_id.smul continuous_const)

/-- The norm of the concrete Fourier transform is continuous. -/
theorem continuous_norm_surfaceFourier (d : ℕ) :
    Continuous (fun ξ : Euclidean d => ‖surfaceFourier d ξ‖) :=
  (continuous_surfaceFourier d).norm

/-- The Fourier transform of the concrete compact surface measure is smooth
in every dimension.  This is obtained from the characteristic-function
regularity theorem after pushing surface measure forward to Euclidean space. -/
theorem contDiff_surfaceFourier (d : Nat) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (surfaceFourier d) := by
  let μ : Measure (Euclidean d) :=
    Measure.map Subtype.val (unitSurfaceMeasure d)
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hbound : ∀ᵐ x : Euclidean d ∂μ, ‖x‖ ≤ 1 := by
    rw [MeasureTheory.ae_map_iff continuous_subtype_val.aemeasurable
      (measurableSet_le continuous_norm.measurable measurable_const)]
    filter_upwards with ω
    have hnorm : ‖(ω : Euclidean d)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ω.property
    exact hnorm.le
  have htop : MemLp (id : Euclidean d → Euclidean d) ⊤ μ :=
    memLp_top_of_bound continuous_id.aestronglyMeasurable 1 hbound
  have hmoment : ∀ k : Nat, MemLp (id : Euclidean d → Euclidean d) (k : ENNReal) μ := by
    intro k
    exact htop.mono_exponent (by simp)
  have hcf : ContDiff ℝ (↑(⊤ : ℕ∞)) (MeasureTheory.charFun μ) :=
    MeasureTheory.contDiff_charFun' (n := ⊤) hmoment
  have heq : surfaceFourier d = fun ξ : Euclidean d =>
      MeasureTheory.charFun μ ((-2 * Real.pi) • ξ) := by
    funext ξ
    unfold surfaceFourier MeasureTheory.charFun μ
    rw [MeasureTheory.integral_map continuous_subtype_val.aemeasurable]
    · apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      unfold surfacePhase
      rw [inner_smul_right]
    · exact (by fun_prop)
  rw [heq]
  exact hcf.comp (ContinuousLinearMap.contDiff
    (ContinuousLinearMap.lsmul ℝ ℝ (-2 * Real.pi)))

/-- Multiplying the literal surface multiplier by compactly supported Schwartz
data produces a Schwartz multiplier, in every dimension. -/
theorem exists_schwartz_compactSupport_mul_surfaceFourier
    {d : Nat} (ψ : SchwartzMap (Euclidean d) ℂ)
    (hψcompact : HasCompactSupport (ψ : Euclidean d → ℂ))
    (r : ℝ) :
    ∃ m : SchwartzMap (Euclidean d) ℂ,
      ∀ ξ, m ξ = ψ ξ * surfaceFourier d (-r • ξ) := by
  let g : Euclidean d → ℂ := fun ξ => ψ ξ * surfaceFourier d (-r • ξ)
  have hcompact : HasCompactSupport g := by
    exact hψcompact.mul_right
  have hsurface : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun ξ : Euclidean d => surfaceFourier d (-r • ξ)) := by
    exact (contDiff_surfaceFourier d).comp
      (ContinuousLinearMap.contDiff (ContinuousLinearMap.lsmul ℝ ℝ (-r)))
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    exact (ψ.smooth (⊤ : ℕ∞)).mul hsurface
  exact ⟨hcompact.toSchwartzMap hsmooth, fun ξ => rfl⟩

/-- The radius derivative of the literal surface multiplier is also smooth
after compact Schwartz localization. -/
theorem exists_schwartz_compactSupport_mul_surfaceFourier_radius_deriv
    {d : Nat} (ψ : SchwartzMap (Euclidean d) ℂ)
    (hψcompact : HasCompactSupport (ψ : Euclidean d → ℂ))
    (r : ℝ) :
    ∃ m : SchwartzMap (Euclidean d) ℂ,
      ∀ ξ, m ξ = ψ ξ *
        deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r := by
  let D : Euclidean d → ℂ := fun ξ =>
    fderiv ℝ (surfaceFourier d) ((-r) • ξ) (-ξ)
  let g : Euclidean d → ℂ := fun ξ => ψ ξ * D ξ
  have hsurface : ContDiff ℝ (↑(⊤ : ℕ∞)) (surfaceFourier d) :=
    contDiff_surfaceFourier d
  have harg : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun ξ : Euclidean d => (-r) • ξ) :=
    ContinuousLinearMap.contDiff (ContinuousLinearMap.lsmul ℝ ℝ (-r))
  have hvec : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun ξ : Euclidean d => -ξ) := by
    simpa only [id_eq] using
      (contDiff_id.neg : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun ξ : Euclidean d => -ξ))
  let K : Euclidean d → Euclidean d → ℂ := fun _ => surfaceFourier d
  have hK : ContDiff ℝ (↑(⊤ : ℕ∞)) (Function.uncurry K) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : Euclidean d × Euclidean d => surfaceFourier d q.2)
    exact hsurface.comp contDiff_snd
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) D := by
    dsimp only [D]
    simpa only [K] using hK.fderiv_apply harg hvec (by simp)
  have hcompact : HasCompactSupport g := by
    exact hψcompact.mul_right
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    exact (ψ.smooth (⊤ : ℕ∞)).mul hD
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_⟩
  intro ξ
  have hsfAt : HasFDerivAt (surfaceFourier d)
      (fderiv ℝ (surfaceFourier d) (r • (-ξ))) (r • (-ξ)) :=
    ((hsurface.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hlinear : HasDerivAt (fun s : ℝ => s • (-ξ)) (-ξ) r :=
    by simpa only [id_eq, one_smul] using (hasDerivAt_id r).smul_const (-ξ)
  have hderiv := hsfAt.comp_hasDerivAt r hlinear
  change ψ ξ * D ξ = ψ ξ *
    deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r
  rw [show D ξ = fderiv ℝ (surfaceFourier d) ((-r) • ξ) (-ξ) by rfl]
  rw [show ((-r) • ξ : Euclidean d) = r • (-ξ) by rw [smul_neg, neg_smul]]
  rw [show deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r =
      fderiv ℝ (surfaceFourier d) (r • (-ξ)) (-ξ) by
    change deriv ((surfaceFourier d) ∘ fun s : ℝ => s • (-ξ)) r = _
    exact hderiv.deriv]

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set
open scoped Pointwise

noncomputable section

/-- Restricting a linear isometry to the unit sphere preserves the concrete
surface measure. -/
private theorem map_unitSurfaceMeasure_linearIsometry (d : Nat)
    (u : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) :
    let uSphere : sphere (0 : Euclidean d) 1 ≃ₜ sphere (0 : Euclidean d) 1 :=
      u.toHomeomorph.subtype (fun x => by
        simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
        rw [u.norm_map])
    Measure.map uSphere (unitSurfaceMeasure d) = unitSurfaceMeasure d := by
  dsimp only
  let uSphere : sphere (0 : Euclidean d) 1 ≃ₜ sphere (0 : Euclidean d) 1 :=
    u.toHomeomorph.subtype (fun x => by
      simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
      rw [u.norm_map])
  have huSphere : Measure.map uSphere (unitSurfaceMeasure d) = unitSurfaceMeasure d := by
    apply Measure.ext
    intro s hs
    simp only [unitSurfaceMeasure]
    rw [Measure.map_apply uSphere.continuous.measurable hs,
      Measure.toSphere_apply' (volume : Measure (Euclidean d))
        (hs.preimage uSphere.continuous.measurable),
      Measure.toSphere_apply' (volume : Measure (Euclidean d)) hs]
    congr 1
    let A : Set (Euclidean d) :=
      Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : Euclidean d) 1 → Euclidean d) ''
        (uSphere ⁻¹' s))
    let B : Set (Euclidean d) :=
      Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : Euclidean d) 1 → Euclidean d) '' s)
    change (volume : Measure (Euclidean d)) A = (volume : Measure (Euclidean d)) B
    have himage : u '' A = B := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with ⟨r, hr, z', hz', rfl⟩
        rcases hz' with ⟨ω, hω, rfl⟩
        refine ⟨r, hr, uSphere ω, ?_, ?_⟩
        · exact ⟨uSphere ω, hω, rfl⟩
        · simp [uSphere]
      · rintro ⟨r, hr, z, hz, rfl⟩
        rcases hz with ⟨ω, hω, rfl⟩
        refine ⟨r • ((uSphere.symm ω : sphere (0 : Euclidean d) 1) : Euclidean d), ?_, ?_⟩
        · refine ⟨r, hr, ((uSphere.symm ω : sphere (0 : Euclidean d) 1) : Euclidean d), ?_, rfl⟩
          refine ⟨uSphere.symm ω, ?_, rfl⟩
          simpa using hω
        · simp [uSphere]
    calc
      (volume : Measure (Euclidean d)) A =
          (volume : Measure (Euclidean d)) (u ⁻¹' (u '' A)) := by
            congr 1
            ext x
            simp
      _ = Measure.map u volume (u '' A) := by
            simpa only [LinearIsometryEquiv.coe_toMeasurableEquiv] using
              (u.toMeasurableEquiv.map_apply (μ := volume) (u '' A)).symm
      _ = (volume : Measure (Euclidean d)) (u '' A) := by
            rw [u.measurePreserving.map_eq]
      _ = (volume : Measure (Euclidean d)) B := by rw [himage]
  simpa only [uSphere] using huSphere

/-- The Fourier transform of the concrete sphere measure is invariant under
orthogonal changes of frequency coordinates. -/
theorem surfaceFourier_linearIsometry (d : Nat)
    (u : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) (ξ : Euclidean d) :
    surfaceFourier d (u ξ) = surfaceFourier d ξ := by
  let uSphere : sphere (0 : Euclidean d) 1 ≃ₜ sphere (0 : Euclidean d) 1 :=
    u.toHomeomorph.subtype (fun x => by
      simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
      rw [u.norm_map])
  have hmeasure : Measure.map uSphere (unitSurfaceMeasure d) = unitSurfaceMeasure d := by
    simpa only [uSphere] using map_unitSurfaceMeasure_linearIsometry d u
  have hpres : MeasurePreserving uSphere (unitSurfaceMeasure d) (unitSurfaceMeasure d) :=
    ⟨uSphere.continuous.measurable, hmeasure⟩
  have hintegral := hpres.integral_comp uSphere.measurableEmbedding
    (fun ω : sphere (0 : Euclidean d) 1 =>
      Complex.exp (surfacePhase d (u ξ) ω))
  calc
    surfaceFourier d (u ξ) =
        ∫ ω : sphere (0 : Euclidean d) 1,
          Complex.exp (surfacePhase d (u ξ) ω) ∂unitSurfaceMeasure d := rfl
    _ = ∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d (u ξ) (uSphere ω)) ∂unitSurfaceMeasure d := hintegral.symm
    _ = ∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp (surfacePhase d ξ ω) ∂unitSurfaceMeasure d := by
      apply integral_congr_ae
      filter_upwards with ω
      apply congrArg Complex.exp
      have hinter : inner ℝ ((uSphere ω : sphere (0 : Euclidean d) 1) : Euclidean d) (u ξ) =
          inner ℝ (ω : Euclidean d) ξ := by
        change inner ℝ (u ω) (u ξ) = inner ℝ (ω : Euclidean d) ξ
        exact u.inner_map_map _ _
      unfold surfacePhase
      rw [hinter]
    _ = surfaceFourier d ξ := rfl

/-- The concrete sphere Fourier transform is radial. -/
theorem surfaceFourier_eq_of_norm_eq (d : Nat) {ξ η : Euclidean d}
    (hξη : ‖ξ‖ = ‖η‖) :
    surfaceFourier d ξ = surfaceFourier d η := by
  let u : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
    Submodule.reflection (ℝ ∙ (ξ - η))ᗮ
  have hu : u ξ = η := Submodule.reflection_sub hξη
  calc
    surfaceFourier d ξ = surfaceFourier d (u ξ) :=
      (surfaceFourier_linearIsometry d u ξ).symm
    _ = surfaceFourier d η := by rw [hu]

/-- Central symmetry of the sphere makes its Fourier transform even. -/
theorem surfaceFourier_neg (d : Nat) (ξ : Euclidean d) :
    surfaceFourier d (-ξ) = surfaceFourier d ξ := by
  apply surfaceFourier_eq_of_norm_eq d
  simp

/-- After choosing any unit direction, the sphere Fourier transform reduces
to the radial frequency on that direction. -/
theorem surfaceFourier_eq_norm_smul_unit (d : Nat) (ξ v : Euclidean d)
    (hv : ‖v‖ = 1) :
    surfaceFourier d ξ = surfaceFourier d (‖ξ‖ • v) := by
  apply surfaceFourier_eq_of_norm_eq d
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hv, mul_one]

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory

noncomputable section

/-- Separating the final coordinate of `Euclidean (d + 1)` pushes Lebesgue
measure forward to the product of Lebesgue measures. -/
theorem map_euclideanSucc_coordinates_volume (d : Nat) :
    Measure.map (fun x : Euclidean (d + 1) =>
      (MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i)),
        x (Fin.last d))) volume =
      ((volume : Measure (Euclidean d)).prod volume) := by
  let e₀ : Euclidean (d + 1) ≃ᵐ (Fin (d + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm
  let e₁ : (Fin (d + 1) → ℝ) ≃ᵐ (Fin d ⊕ Fin 1 → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
      (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm
  let e₂ : (Fin d ⊕ Fin 1 → ℝ) ≃ᵐ (Fin d → ℝ) × (Fin 1 → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin 1 ↦ ℝ)
  let e₃ : (Fin d → ℝ) × (Fin 1 → ℝ) ≃ᵐ Euclidean d × ℝ :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin d → ℝ))
      (MeasurableEquiv.piUnique fun _ : Fin 1 ↦ ℝ)
  let e : Euclidean (d + 1) ≃ᵐ Euclidean d × ℝ :=
    e₀.trans (e₁.trans (e₂.trans e₃))
  have he₀ : MeasurePreserving e₀ volume volume := by
    simpa only [e₀, MeasurableEquiv.coe_toLp_symm] using
      (PiLp.volume_preserving_ofLp (Fin (d + 1)))
  have he₁ : MeasurePreserving e₁ volume volume := by
    simpa only [e₁] using
      (volume_measurePreserving_piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
        (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm
  have he₂ : MeasurePreserving e₂ volume volume := by
    simpa only [e₂] using
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin d ⊕ Fin 1 ↦ ℝ))
  have he₃a : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℝ)) volume volume := by
    exact PiLp.volume_preserving_toLp (Fin d)
  have he₃b : MeasurePreserving (MeasurableEquiv.piUnique fun _ : Fin 1 ↦ ℝ)
      volume volume := by
    exact volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ)
  have he₃ : MeasurePreserving e₃ volume ((volume : Measure (Euclidean d)).prod volume) := by
    change MeasurePreserving
      (Prod.map (MeasurableEquiv.toLp 2 (Fin d → ℝ))
        (MeasurableEquiv.piUnique fun _ : Fin 1 ↦ ℝ))
      volume ((volume : Measure (Euclidean d)).prod volume)
    simpa only [Measure.volume_eq_prod] using he₃a.prod he₃b
  have he : MeasurePreserving e volume ((volume : Measure (Euclidean d)).prod volume) := by
    change MeasurePreserving (e₃ ∘ e₂ ∘ e₁ ∘ e₀) volume
      ((volume : Measure (Euclidean d)).prod volume)
    exact he₃.comp (he₂.comp (he₁.comp he₀))
  have heq : (e : Euclidean (d + 1) → Euclidean d × ℝ) =
      fun x =>
        (MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i)),
          x (Fin.last d)) := by
    funext x
    change
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)
          (fun i => (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
            (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm x.ofLp (Sum.inl i)),
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
          (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm x.ofLp (Sum.inr 0)) = _
    have hleft (i : Fin d) :
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
          (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm x.ofLp (Sum.inl i) =
          x.ofLp (Fin.castAdd 1 i) := by
      rfl
    have hright (i : Fin 1) :
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) ↦ ℝ)
          (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).symm x.ofLp (Sum.inr i) =
          x.ofLp (Fin.natAdd d i) := by
      rfl
    simp_rw [hleft]
    rw [hright 0]
    rfl
  rw [← heq]
  exact he.map_eq

/-- The Euclidean square norm splits into its first `d` coordinates and its
final coordinate. -/
theorem norm_sq_euclideanSucc_coordinates (d : Nat) (x : Euclidean (d + 1)) :
    ‖x‖ ^ 2 =
      ‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
        (x (Fin.last d)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [MeasurableEquiv.coe_toLp, PiLp.toLp_apply]
  rw [Fin.sum_univ_castSucc]
  rfl

/-- The square-root form of the arbitrary-dimensional Cartesian norm split. -/
theorem norm_euclideanSucc_coordinates (d : Nat) (x : Euclidean (d + 1)) :
    ‖x‖ =
      Real.sqrt
        (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
          (x (Fin.last d)) ^ 2) := by
  calc
    ‖x‖ = |‖x‖| := (abs_of_nonneg (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt
        (‖MeasurableEquiv.toLp 2 (Fin d → ℝ) (fun i => x (Fin.castAdd 1 i))‖ ^ 2 +
          (x (Fin.last d)) ^ 2) := by
      rw [norm_sq_euclideanSucc_coordinates]

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory

noncomputable section

/-- A positive Euclidean dilation, with its usual Jacobian factor, preserves
the integral of the pointwise norm. -/
theorem integral_norm_dilate_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (k : Euclidean d → E) {R : ℝ}
    (hR : 0 < R) :
    (∫ x : Euclidean d, ‖(R ^ d) • k (R • x)‖) = ∫ x : Euclidean d, ‖k x‖ := by
  rw [show (fun x : Euclidean d => ‖(R ^ d) • k (R • x)‖) =
      fun x => R ^ d * ‖k (R • x)‖ by
        funext x
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hR.le _)],
      integral_const_mul,
      Measure.integral_comp_smul_of_nonneg volume (fun x : Euclidean d => ‖k x‖) R
        (hR := hR.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp [hR.ne']

/-- The unnormalised positive Euclidean dilation has the reciprocal Jacobian
factor in its `L¹` norm. -/
theorem integral_norm_comp_smul_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (f : Euclidean d → E) {R : ℝ} (hR : 0 < R) :
    (∫ x : Euclidean d, ‖f (R • x)‖) =
      (R ^ d)⁻¹ * ∫ x : Euclidean d, ‖f x‖ := by
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun x : Euclidean d => ‖f x‖) R (hR := hR.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]

/-- The square-energy version of Euclidean dilation.  This is the Jacobian
identity used when compact-radius `L²` estimates are transported to a
literal dyadic radius block. -/
theorem integral_norm_sq_comp_smul_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (f : Euclidean d → E) {R : ℝ} (hR : 0 < R) :
    (∫ x : Euclidean d, ‖f (R • x)‖ ^ (2 : ℕ)) =
      (R ^ d)⁻¹ * ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ) := by
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun x : Euclidean d => ‖f x‖ ^ (2 : ℕ)) R (hR := hR.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]

/-- Integrability is preserved by a positive Euclidean dilation with the
usual Jacobian factor. -/
theorem integrable_dilate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (k : Euclidean d → E) {R : ℝ}
    (hR : 0 < R) (hk : Integrable k) :
    Integrable (fun x : Euclidean d => (R ^ d) • k (R • x)) := by
  have hcomp : Integrable (fun x : Euclidean d => k (R • x)) :=
    Integrable.comp_smul hk hR.ne'
  convert Integrable.smul (R ^ d : ℝ) hcomp using 1
  ext x
  rfl

/-- The total derivative of a Euclidean dilation has the expected extra
factor of the dilation scale. -/
theorem fderiv_dilate
    {d : ℕ} (k : Euclidean d → ℂ) (hk : ContDiff ℝ 1 k)
    (R : ℝ) (x : Euclidean d) :
    fderiv ℝ (fun y : Euclidean d => (R ^ d) • k (R • y)) x =
      (R ^ (d + 1)) • fderiv ℝ k (R • x) := by
  have hcomp : DifferentiableAt ℝ (fun y : Euclidean d => k (R • y)) x :=
    (hk.differentiable (by norm_num)).differentiableAt.comp x
      (differentiableAt_id.const_smul R)
  calc
    fderiv ℝ (fun y : Euclidean d => (R ^ d) • k (R • y)) x =
        (R ^ d) • fderiv ℝ (fun y : Euclidean d => k (R • y)) x :=
      fderiv_fun_const_smul hcomp (R ^ d)
    _ = (R ^ d) • (R • fderiv ℝ k (R • x)) := by
      rw [fderiv_comp_smul]
    _ = (R ^ (d + 1)) • fderiv ℝ k (R • x) := by
      rw [smul_smul, ← pow_succ]

/-- The `L¹` norm of the derivative of a positive Euclidean dilation gains
exactly one factor of the scale. -/
theorem integral_norm_fderiv_dilate_eq
    {d : ℕ} (k : Euclidean d → ℂ) (hk : ContDiff ℝ 1 k)
    {R : ℝ} (hR : 0 < R) :
    (∫ x : Euclidean d,
      ‖fderiv ℝ (fun y : Euclidean d => (R ^ d) • k (R • y)) x‖) =
      R * ∫ x : Euclidean d, ‖fderiv ℝ k x‖ := by
  calc
    (∫ x : Euclidean d,
      ‖fderiv ℝ (fun y : Euclidean d => (R ^ d) • k (R • y)) x‖) =
        ∫ x : Euclidean d,
          ‖R • ((R ^ d) • fderiv ℝ k (R • x))‖ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [fderiv_dilate k hk R x, pow_succ, smul_smul,
          mul_comm (R ^ d) R]
    _ = R * ∫ x : Euclidean d, ‖(R ^ d) • fderiv ℝ k (R • x)‖ := by
      rw [show (fun x : Euclidean d => ‖R • ((R ^ d) • fderiv ℝ k (R • x))‖) =
        fun x => R * ‖(R ^ d) • fderiv ℝ k (R • x)‖ by
          funext x
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR],
        MeasureTheory.integral_const_mul]
    _ = R * ∫ x : Euclidean d, ‖fderiv ℝ k x‖ := by
      rw [integral_norm_dilate_eq d (fderiv ℝ k) hR]

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open Set

noncomputable section

/-- The positive frequency scale associated to a nonnegative dyadic level. -/
def dyadicScale (j : Nat) : Real := (2 : Real) ^ j

/-- The half-open annulus with radii between two consecutive dyadic scales. -/
def dyadicAnnulus (d j : Nat) : Set (Euclidean d) :=
  {xi | dyadicScale j <= norm xi /\ norm xi < dyadicScale (j + 1)}

/-- Dyadic scales are positive. -/
theorem dyadicScale_pos (j : Nat) : 0 < dyadicScale j := by
  simp [dyadicScale]

/-- Dyadic scales are monotone in their index. -/
theorem dyadicScale_mono {i j : Nat} (hij : i <= j) :
    dyadicScale i <= dyadicScale j := by
  unfold dyadicScale
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hij

/-- Points in strictly later annuli have strictly larger frequency norm. -/
theorem norm_lt_norm_of_mem_dyadicAnnulus_of_lt
    {d i j : Nat} (hij : i < j) {xi eta : Euclidean d}
    (hxi : xi ∈ dyadicAnnulus d i) (heta : eta ∈ dyadicAnnulus d j) :
    norm xi < norm eta := by
  rcases hxi with ⟨_, hxi_upper⟩
  rcases heta with ⟨heta_lower, _⟩
  have hscale : dyadicScale (i + 1) <= dyadicScale j :=
    dyadicScale_mono (Nat.succ_le_iff.mpr hij)
  exact lt_of_lt_of_le hxi_upper (hscale.trans heta_lower)

/-- Dyadic annuli at unequal levels are disjoint. -/
theorem dyadicAnnulus_disjoint {d i j : Nat} (hij : i ≠ j) :
    Disjoint (dyadicAnnulus d i) (dyadicAnnulus d j) := by
  rw [Set.disjoint_left]
  intro xi hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (lt_irrefl (norm xi))
      (norm_lt_norm_of_mem_dyadicAnnulus_of_lt hij hxi hxj)
  · exact (lt_irrefl (norm xi))
      (norm_lt_norm_of_mem_dyadicAnnulus_of_lt hji hxj hxi)

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Set

noncomputable section

/-- The compact-radius supremum of the norm of a jointly continuous
complex-valued family is measurable in the spatial variable. -/
theorem measurable_iSup_ennreal_norm_of_continuous
    {d : ℕ} {F : ℝ × Euclidean d → ℂ} {a b : ℝ}
    (hF : Continuous F) :
    Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal ‖F (r.1, x)‖) := by
  have hG : Measurable (⨆ r : Icc a b, fun x : Euclidean d =>
      ENNReal.ofReal ‖F (r.1, x)‖) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro r
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_const.prodMk continuous_id)).norm)).measurable
    · intro x
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_subtype_val.prodMk continuous_const)).norm)).lowerSemicontinuous
  have hEq : (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal ‖F (r.1, x)‖) =
      ⨆ r : Icc a b, fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖ := by
    funext x
    exact (iSup_apply
      (f := fun r : Icc a b => fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖) (a := x)).symm
  rw [hEq]
  exact hG

/-- The compact-radius supremum of the squared norm of a jointly continuous
complex-valued family is measurable in the spatial variable. -/
theorem measurable_iSup_ennreal_norm_sq_of_continuous
    {d : ℕ} {F : ℝ × Euclidean d → ℂ} {a b : ℝ}
    (hF : Continuous F) :
    Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal (‖F (r.1, x)‖ ^ 2)) := by
  have hG : Measurable (⨆ r : Icc a b, fun x : Euclidean d =>
      ENNReal.ofReal (‖F (r.1, x)‖ ^ 2)) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro r
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_const.prodMk continuous_id)).norm.pow 2)).measurable
    · intro x
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_subtype_val.prodMk continuous_const)).norm.pow 2)).lowerSemicontinuous
  have hEq : (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal (‖F (r.1, x)‖ ^ 2)) =
      ⨆ r : Icc a b, fun x : Euclidean d =>
        ENNReal.ofReal (‖F (r.1, x)‖ ^ 2) := by
    funext x
    exact (iSup_apply
      (f := fun r : Icc a b => fun x : Euclidean d =>
        ENNReal.ofReal (‖F (r.1, x)‖ ^ 2)) (a := x)).symm
  rw [hEq]
  exact hG

end

end LeanSpherical.HarmonicAnalysis

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Metric
open scoped BoundedContinuousFunction Convolution

noncomputable section

/-- If a smoothing kernel is `C¹` and compactly supported, convolution by it
has the expected total derivative. -/
theorem fderiv_convolution_right_eq_convolution_fderiv
    {d : ℕ} (f k : Euclidean d → ℂ) (hf : LocallyIntegrable f volume)
    (hk : HasCompactSupport k) (hk1 : ContDiff ℝ 1 k) (x : Euclidean d) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x =
      (f ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR (Euclidean d), volume]
        fderiv ℝ k) x := by
  exact
    (hk.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hf hk1 x).fderiv

/-- An integrable input convolved with a globally bounded `C¹` kernel is
differentiable, with derivative obtained by convolving against the kernel's
total derivative.  This is the non-compact version needed for Schwartz
kernels: the global derivative bound is an integrable majorant after it is
multiplied by the input. -/
theorem hasFDerivAt_convolution_right_of_bound
    {d : ℕ} (f k : Euclidean d → ℂ) (hf : Integrable f volume)
    (hk : ContDiff ℝ 1 k) {C₀ C₁ : ℝ}
    (hkb : ∀ z, ‖k z‖ ≤ C₀)
    (hdkb : ∀ z, ‖fderiv ℝ k z‖ ≤ C₁)
    (x₀ : Euclidean d) :
    HasFDerivAt (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k)
      ((f ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR (Euclidean d), volume]
        fderiv ℝ k) x₀) x₀ := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  let L' := L.precompR (Euclidean d)
  have hL : ∀ (z : ℂ) (A : Euclidean d →L[ℝ] ℂ), ‖L' z A‖ ≤ ‖z‖ * ‖A‖ := by
    intro z A
    have hEq : L' z A = z • A := by
      ext v
      simp [L, L', ContinuousLinearMap.precompR_apply, ContinuousLinearMap.mul_apply']
    rw [hEq, norm_smul]
  have hmeas (x : Euclidean d) : AEStronglyMeasurable
      (fun t : Euclidean d => L (f t) (k (x - t))) volume := by
    exact hf.aestronglyMeasurable.convolution_integrand_snd L
      hk.continuous.aestronglyMeasurable x
  have hdmeas (x : Euclidean d) : AEStronglyMeasurable
      (fun t : Euclidean d => L' (f t) (fderiv ℝ k (x - t))) volume := by
    exact hf.aestronglyMeasurable.convolution_integrand_snd L'
      (hk.continuous_fderiv (by norm_num)).aestronglyMeasurable x
  have hderiv (x t : Euclidean d) : HasFDerivAt
      (fun y : Euclidean d => k (y - t)) (fderiv ℝ k (x - t)) x := by
    simpa using!
      (hk.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub (hasFDerivAt_const t x))
  have hbound : ∀ᵐ t : Euclidean d ∂volume,
      ∀ x ∈ ball x₀ 1, ‖L' (f t) (fderiv ℝ k (x - t))‖ ≤ ‖f t‖ * C₁ := by
    filter_upwards with t
    intro x hx
    exact (hL _ _).trans (mul_le_mul_of_nonneg_left (hdkb _) (norm_nonneg _))
  have hmajor : Integrable (fun t : Euclidean d => ‖f t‖ * C₁) volume :=
    hf.norm.mul_const C₁
  have hexists : ∀ x : Euclidean d,
      ConvolutionExistsAt f k x L volume := by
    intro x
    change Integrable (fun t : Euclidean d => L (f t) (k (x - t))) volume
    refine Integrable.mono' (hf.norm.mul_const C₀) (hmeas x) ?_
    filter_upwards with t
    change ‖f t * k (x - t)‖ ≤ ‖f t‖ * C₀
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hkb _) (norm_nonneg _)
  simpa using!
    (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (ball_mem_nhds x₀ zero_lt_one)
      (Filter.Eventually.of_forall hmeas) (hexists x₀)
      (hdmeas x₀) hbound hmajor
      (Filter.Eventually.of_forall fun t x hx =>
        (L (f t)).hasFDerivAt.comp x (hderiv x t)))

/-- Once a convolution has the displayed pointwise derivative formula, its
total derivative satisfies the direct `L¹` Young bound. -/
theorem integral_norm_fderiv_convolution_right_le_of_hasFDerivAt
    {d : ℕ} (f k : Euclidean d → ℂ) (hf : Integrable f volume)
    (hderiv : ∀ x : Euclidean d,
      HasFDerivAt (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k)
        ((f ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR (Euclidean d), volume]
          fderiv ℝ k) x) x)
    (hdk : Integrable (fderiv ℝ k) volume) :
    (∫ x : Euclidean d,
      ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x‖) ≤
      (∫ x : Euclidean d, ‖f x‖) * (∫ x : Euclidean d, ‖fderiv ℝ k x‖) := by
  let D : Euclidean d → Euclidean d →L[ℝ] ℂ := fderiv ℝ k
  let L := (ContinuousLinearMap.mul ℝ ℂ).precompR (Euclidean d)
  have hL : ∀ (z : ℂ) (A : Euclidean d →L[ℝ] ℂ), ‖L z A‖ ≤ ‖z‖ * ‖A‖ := by
    intro z A
    have hEq : L z A = z • A := by
      ext v
      simp [L, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.mul_apply']
    rw [hEq, norm_smul]
  have hprodNorm :
      Integrable (fun p : Euclidean d × Euclidean d =>
        ‖f p.2‖ * ‖D (p.1 - p.2)‖) (volume.prod volume) := by
    simpa only [D, ContinuousLinearMap.mul_apply'] using
      (hf.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hdk.norm)
  have hscalar :
      Integrable (fun x : Euclidean d =>
        ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖) volume :=
    hprodNorm.integral_prod_left
  have hfiber : ∀ᵐ x : Euclidean d ∂volume,
      Integrable (fun t : Euclidean d => ‖f t‖ * ‖D (x - t)‖) volume := by
    exact (integrable_prod_iff hprodNorm.aestronglyMeasurable).mp hprodNorm |>.1
  have hconv : Integrable (f ⋆[L, volume] D) volume :=
    hf.integrable_convolution L hdk
  have hpoint : ∀ᵐ x : Euclidean d ∂volume,
      ‖(f ⋆[L, volume] D) x‖ ≤
        ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖ := by
    filter_upwards [hfiber] with x hx
    rw [convolution_def]
    calc
      ‖∫ t : Euclidean d, L (f t) (D (x - t))‖ ≤
          ∫ t : Euclidean d, ‖L (f t) (D (x - t))‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖ := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun t => norm_nonneg _
        · exact hx
        · exact Filter.Eventually.of_forall fun t => hL _ _
  have hfirst :
      (∫ x : Euclidean d, ‖(f ⋆[L, volume] D) x‖) ≤
        ∫ x : Euclidean d, ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖ := by
    exact integral_mono_ae hconv.norm hscalar hpoint
  have hswap :
      (∫ x : Euclidean d, ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖) =
        ∫ t : Euclidean d, ∫ x : Euclidean d, ‖f t‖ * ‖D (x - t)‖ := by
    exact integral_integral_swap hprodNorm
  have htranslate :
      (∫ t : Euclidean d, ∫ x : Euclidean d, ‖f t‖ * ‖D (x - t)‖) =
        (∫ t : Euclidean d, ‖f t‖) * (∫ x : Euclidean d, ‖D x‖) := by
    calc
      (∫ t : Euclidean d, ∫ x : Euclidean d, ‖f t‖ * ‖D (x - t)‖) =
          ∫ t : Euclidean d, ‖f t‖ * ∫ x : Euclidean d, ‖D (x - t)‖ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [integral_const_mul]
      _ = ∫ t : Euclidean d, ‖f t‖ * ∫ x : Euclidean d, ‖D x‖ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [integral_sub_right_eq_self (μ := volume)
          (fun x : Euclidean d => ‖D x‖) t]
      _ = (∫ t : Euclidean d, ‖f t‖) * (∫ x : Euclidean d, ‖D x‖) := by
        rw [integral_mul_const]
  calc
    (∫ x : Euclidean d,
      ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x‖) =
        ∫ x : Euclidean d, ‖(f ⋆[L, volume] D) x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [(hderiv x).fderiv]
    _ ≤ ∫ x : Euclidean d, ∫ t : Euclidean d, ‖f t‖ * ‖D (x - t)‖ := hfirst
    _ = (∫ x : Euclidean d, ‖f x‖) * (∫ x : Euclidean d, ‖D x‖) := hswap.trans htranslate
    _ = (∫ x : Euclidean d, ‖f x‖) * (∫ x : Euclidean d, ‖fderiv ℝ k x‖) := by rfl

/-- A compactly supported `C¹` smoothing convolution obeys the direct `L¹`
bound for its total derivative. -/
theorem integral_norm_fderiv_convolution_right_le
    {d : ℕ} (f k : Euclidean d → ℂ) (hf : Integrable f volume)
    (hk : HasCompactSupport k) (hk1 : ContDiff ℝ 1 k)
    (hdk : Integrable (fderiv ℝ k) volume) :
    (∫ x : Euclidean d,
      ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x‖) ≤
      (∫ x : Euclidean d, ‖f x‖) * (∫ x : Euclidean d, ‖fderiv ℝ k x‖) := by
  exact integral_norm_fderiv_convolution_right_le_of_hasFDerivAt f k hf
    (fun x => hk.hasFDerivAt_convolution_right
      (ContinuousLinearMap.mul ℝ ℂ) hf.locallyIntegrable hk1 x)
    hdk

/-- The same `L¹` derivative estimate for globally bounded smooth kernels.
This is the version applicable to Schwartz kernels. -/
theorem integral_norm_fderiv_convolution_right_le_of_bound
    {d : ℕ} (f k : Euclidean d → ℂ) (hf : Integrable f volume)
    (hk : ContDiff ℝ 1 k) {C₀ C₁ : ℝ}
    (hkb : ∀ z, ‖k z‖ ≤ C₀)
    (hdkb : ∀ z, ‖fderiv ℝ k z‖ ≤ C₁)
    (hdk : Integrable (fderiv ℝ k) volume) :
    (∫ x : Euclidean d,
      ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x‖) ≤
      (∫ x : Euclidean d, ‖f x‖) * (∫ x : Euclidean d, ‖fderiv ℝ k x‖) := by
  exact integral_norm_fderiv_convolution_right_le_of_hasFDerivAt f k hf
    (fun x => hasFDerivAt_convolution_right_of_bound f k hf hk hkb hdkb x) hdk

/-- Applying the preceding estimate to a Schwartz kernel requires no compact
support fiction: Schwartz decay supplies the global bounds and integrability
needed by the non-compact differentiation theorem. -/
theorem integral_norm_fderiv_convolution_right_le_schwartz
    {d : ℕ} (f : Euclidean d → ℂ) (hf : Integrable f volume)
    (k : SchwartzMap (Euclidean d) ℂ) :
    (∫ x : Euclidean d,
      ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (k : Euclidean d → ℂ)) x‖) ≤
      (∫ x : Euclidean d, ‖f x‖) *
        (∫ x : Euclidean d, ‖fderiv ℝ (k : Euclidean d → ℂ) x‖) := by
  let dk : SchwartzMap (Euclidean d) (Euclidean d →L[ℝ] ℂ) :=
    (SchwartzMap.fderivCLM ℂ (Euclidean d) ℂ) k
  have hdk : Integrable (fderiv ℝ (k : Euclidean d → ℂ)) volume := by
    have hdk_eq : (dk : Euclidean d → (Euclidean d →L[ℝ] ℂ)) =
        fderiv ℝ (k : Euclidean d → ℂ) := by
      funext x
      exact SchwartzMap.fderivCLM_apply ℂ k x
    rw [← hdk_eq]
    exact dk.integrable
  refine integral_norm_fderiv_convolution_right_le_of_bound f (k : Euclidean d → ℂ)
    hf (by simpa using k.smooth (1 : ℕ∞))
      (C₀ := ‖k.toBoundedContinuousFunction‖)
      (C₁ := ‖dk.toBoundedContinuousFunction‖) ?_ ?_ hdk
  · intro z
    exact BoundedContinuousFunction.norm_coe_le_norm
      (k.toBoundedContinuousFunction : Euclidean d →ᵇ ℂ) z
  · intro z
    calc
      ‖fderiv ℝ (k : Euclidean d → ℂ) z‖ = ‖dk z‖ := by
        rw [← SchwartzMap.fderivCLM_apply ℂ k z]
      _ = ‖dk.toBoundedContinuousFunction z‖ := rfl
      _ ≤ ‖dk.toBoundedContinuousFunction‖ :=
        BoundedContinuousFunction.norm_coe_le_norm
          (dk.toBoundedContinuousFunction : Euclidean d →ᵇ (Euclidean d →L[ℝ] ℂ)) z

end

end LeanSpherical.HarmonicAnalysis

open MeasureTheory
open scoped Convolution

noncomputable section

namespace LeanSpherical.HarmonicAnalysis

/-- The `L¹` norm of the convolution of two complex integrable functions on
finite-dimensional Euclidean space is bounded by the product of their `L¹`
norms. -/
theorem integral_norm_convolution_mul_le
    {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x : EuclideanSpace ℝ (Fin d), ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖) ≤
      (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖) *
        (∫ x : EuclideanSpace ℝ (Fin d), ‖g x‖) := by
  have hprod :
      Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        f p.2 * g (p.1 - p.2)) (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg
  have hprodNorm :
      Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖f p.2‖ * ‖g (p.1 - p.2)‖) (volume.prod volume) := by
    simpa only [norm_mul] using hprod.norm
  have hiter :
      Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        ∫ t : EuclideanSpace ℝ (Fin d), ‖f t‖ * ‖g (x - t)‖) volume :=
    hprodNorm.integral_prod_left
  have hconv :
      Integrable (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) volume :=
    hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  calc
    (∫ x : EuclideanSpace ℝ (Fin d), ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖) ≤
        ∫ x : EuclideanSpace ℝ (Fin d),
          ∫ t : EuclideanSpace ℝ (Fin d), ‖f t‖ * ‖g (x - t)‖ := by
      apply integral_mono hconv.norm hiter
      intro x
      change ‖∫ t : EuclideanSpace ℝ (Fin d), f t * g (x - t)‖ ≤ _
      simpa only [norm_mul] using
        (norm_integral_le_integral_norm
          (fun t : EuclideanSpace ℝ (Fin d) => f t * g (x - t)))
    _ = ∫ t : EuclideanSpace ℝ (Fin d),
        ∫ x : EuclideanSpace ℝ (Fin d), ‖f t‖ * ‖g (x - t)‖ := by
      exact integral_integral_swap hprodNorm
    _ = ∫ t : EuclideanSpace ℝ (Fin d), ‖f t‖ *
        ∫ x : EuclideanSpace ℝ (Fin d), ‖g x‖ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [integral_const_mul]
      rw [integral_sub_right_eq_self (μ := volume)
        (fun x : EuclideanSpace ℝ (Fin d) => ‖g x‖) t]
    _ = (∫ t : EuclideanSpace ℝ (Fin d), ‖f t‖) *
        (∫ x : EuclideanSpace ℝ (Fin d), ‖g x‖) := by
      rw [integral_mul_const]

/-- A bounded continuous function convolved with an even integrable kernel
has the expected pointwise `L∞` bound.  The evenness is exactly what lets the
literal convolution convention use translation invariance without a separate
reflection-invariance hypothesis on volume. -/
theorem norm_convolution_mul_le_bound_mul_integral_norm_of_even
    {d : Nat} (f g : EuclideanSpace ℝ (Fin d) → ℂ) (hf : Continuous f)
    {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C) (hg : Integrable g volume)
    (hgeven : ∀ y, g (-y) = g y)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x‖ ≤
      C * ∫ y : EuclideanSpace ℝ (Fin d), ‖g y‖ := by
  have hflip (y : EuclideanSpace ℝ (Fin d)) : g (x - y) = g (y - x) := by
    rw [show x - y = -(y - x) by abel, hgeven]
  have hgtranslate : Integrable (fun y : EuclideanSpace ℝ (Fin d) => g (x - y)) volume := by
    refine (hg.comp_sub_right x).congr (Filter.Eventually.of_forall ?_)
    intro y
    exact (hflip y).symm
  have hmajor : Integrable
      (fun y : EuclideanSpace ℝ (Fin d) => C * ‖g (x - y)‖) volume :=
    hgtranslate.norm.const_mul C
  have hmeas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin d) => f y * g (x - y)) volume :=
    hf.aestronglyMeasurable.mul hgtranslate.aestronglyMeasurable
  have hprod : Integrable
      (fun y : EuclideanSpace ℝ (Fin d) => f y * g (x - y)) volume := by
    refine hmajor.mono' hmeas (Filter.Eventually.of_forall ?_)
    intro y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg _)
  change ‖∫ y : EuclideanSpace ℝ (Fin d), f y * g (x - y)‖ ≤ _
  calc
    ‖∫ y : EuclideanSpace ℝ (Fin d), f y * g (x - y)‖ ≤
        ∫ y : EuclideanSpace ℝ (Fin d), ‖f y * g (x - y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : EuclideanSpace ℝ (Fin d), C * ‖g (x - y)‖ := by
      apply integral_mono hprod.norm hmajor
      intro y
      change ‖f y * g (x - y)‖ ≤ C * ‖g (x - y)‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg _)
    _ = C * ∫ y : EuclideanSpace ℝ (Fin d), ‖g y‖ := by
      rw [show (∫ y : EuclideanSpace ℝ (Fin d), C * ‖g (x - y)‖) =
          ∫ y : EuclideanSpace ℝ (Fin d), C * ‖g (y - x)‖ by
            apply integral_congr_ae
            filter_upwards with y
            rw [hflip]]
      rw [integral_const_mul]
      congr 1
      exact integral_sub_right_eq_self (μ := volume)
        (fun y : EuclideanSpace ℝ (Fin d) => ‖g y‖) x

/-- An integrable kernel convolved with a bounded continuous function has the
direct pointwise `L∞` bound.  This is the orientation used by the physical
realization of a smooth Fourier multiplier. -/
theorem norm_convolution_mul_le_integral_norm_mul_bound
    {d : Nat} (k f : EuclideanSpace ℝ (Fin d) → ℂ) (hk : Integrable k volume)
    (hf : Continuous f) {C : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖(k ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f) x‖ ≤
      (∫ y : EuclideanSpace ℝ (Fin d), ‖k y‖) * C := by
  have hshift : Continuous (fun y : EuclideanSpace ℝ (Fin d) => f (x - y)) :=
    hf.comp ((continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin d) => x).sub
      continuous_id)
  have hmajor : Integrable
      (fun y : EuclideanSpace ℝ (Fin d) => ‖k y‖ * C) volume :=
    hk.norm.mul_const C
  have hmeas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin d) => k y * f (x - y)) volume :=
    hk.aestronglyMeasurable.mul hshift.aestronglyMeasurable
  have hprod : Integrable
      (fun y : EuclideanSpace ℝ (Fin d) => k y * f (x - y)) volume := by
    refine hmajor.mono' hmeas (Filter.Eventually.of_forall ?_)
    intro y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
  change ‖∫ y : EuclideanSpace ℝ (Fin d), k y * f (x - y)‖ ≤ _
  calc
    ‖∫ y : EuclideanSpace ℝ (Fin d), k y * f (x - y)‖ ≤
        ∫ y : EuclideanSpace ℝ (Fin d), ‖k y * f (x - y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : EuclideanSpace ℝ (Fin d), ‖k y‖ * C := by
      apply integral_mono hprod.norm hmajor
      intro y
      change ‖k y * f (x - y)‖ ≤ ‖k y‖ * C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    _ = (∫ y : EuclideanSpace ℝ (Fin d), ‖k y‖) * C := by
      rw [integral_mul_const]

end LeanSpherical.HarmonicAnalysis
