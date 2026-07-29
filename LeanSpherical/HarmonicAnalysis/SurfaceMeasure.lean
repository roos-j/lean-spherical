/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Surface measure and its Fourier transform

This file contains the concrete geometric objects used by the spherical maximal
argument. The unit sphere carries the measure obtained from Lebesgue measure
by `Measure.toSphere`; no abstract choice of a surface measure is needed.

The Fourier convention here is
`exp (-2 * pi * <omega, xi> * I)`.
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
