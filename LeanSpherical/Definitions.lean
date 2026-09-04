/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.MetricSpace.CoveringNumbers
import LeanSpherical.Auto.Spherical.LegendreAssouad

/-!

# Basic definitions for this project

-/

namespace Spherical

open Filter MeasureTheory Set Topology ENNReal
open scoped ENNReal NNReal Topology

noncomputable section

/- `d`-dimensional real Euclidean space. -/
scoped notation "ℝ^" d:arg => EuclideanSpace ℝ (Fin d)

section SphericalMaximal

/-- `d`-dimensional Euclidean unit sphere -/
abbrev unitSphere (d : ℕ) := Metric.sphere (0 : ℝ^d) 1

/-- Normalized surface measure on the Euclidean unit sphere. -/
def unitSphereMeasure (d : ℕ) : Measure (unitSphere d) := by
  let μ : Measure (Metric.sphere (0 : ℝ^d) 1) := volume.toSphere
  exact (μ univ)⁻¹ • μ

/-- Spherical average of `f` centered at `x` with radius `t`. -/
def sphericalAverage {d : ℕ} (t : ℝ) (f : ℝ^d → ℂ) (x : ℝ^d) : ℂ :=
  ∫ y, f (x + t • (y : ℝ^d)) ∂(unitSphereMeasure d)

/-- The spherical maximal function restricted to a set of radii `E`. -/
def restrictedSphericalMaximal {d : ℕ} (E : Set ℝ) (f : ℝ^d → ℂ) (x : ℝ^d) : ENNReal :=
  ⨆ t ∈ E ∩ Ioi 0, ENNReal.ofReal ‖sphericalAverage t f x‖

@[inherit_doc restrictedSphericalMaximal]
abbrev M {d : ℕ} (E : Set ℝ) (f : ℝ^d → ℂ) (x : ℝ^d) : ENNReal := restrictedSphericalMaximal E f x

end SphericalMaximal

section FractalDimensions

/-- Compatibility name for the logarithmic dilation map now defined in
`Auto.Spherical.LegendreAssouad`. -/
abbrev logDilationSet := Auto.Spherical.LegendreAssouad.logDilationSet

/-- Compatibility name for the logarithmic ball now defined in
`Auto.Spherical.LegendreAssouad`. -/
abbrev logBall := Auto.Spherical.LegendreAssouad.logBall

/-- Compatibility name for the logarithmic entropy number now defined in
`Auto.Spherical.LegendreAssouad`. -/
abbrev entropyNumber := Auto.Spherical.LegendreAssouad.entropyNumber

@[inherit_doc entropyNumber]
abbrev N := Auto.Spherical.LegendreAssouad.N

/-- Compatibility name for the logarithmic upper Minkowski exponent now
defined in `Auto.Spherical.LegendreAssouad`. -/
abbrev upperMinkowskiExponent :=
  Auto.Spherical.LegendreAssouad.upperMinkowskiExponent

@[inherit_doc upperMinkowskiExponent]
abbrev β := Auto.Spherical.LegendreAssouad.β

/-- Compatibility name for the logarithmic Legendre--Assouad function now
defined in `Auto.Spherical.LegendreAssouad`. -/
abbrev legendreAssouadFunction :=
  Auto.Spherical.LegendreAssouad.legendreAssouadFunction

@[inherit_doc legendreAssouadFunction]
scoped notation "ν♯" => legendreAssouadFunction

/-- Compatibility name for the generalized inverse now defined in
`Auto.Spherical.LegendreAssouad`. -/
abbrev generalizedInverse := Auto.Spherical.LegendreAssouad.generalizedInverse

@[inherit_doc generalizedInverse]
scoped notation f "†" => generalizedInverse f

end FractalDimensions

namespace RestrictedDilations

/-- The critical exponent `p_β = 1 + β / (d - 1)`. -/
def criticalExponent (d : ℕ) (E : Set ℝ) : ℝ := 1 + β E / ((d : ℝ) - 1)

end RestrictedDilations

namespace PowerWeights

open RestrictedDilations

/-- Lebesgue measure weighted by the radial power `|x|^α`. -/
def powerWeight (d : ℕ) (α : ℝ) : Measure (ℝ^d) :=
  volume.withDensity fun x ↦ (ENNReal.ofReal ‖x‖) ^ α

/-- The weighted strong-type region, in coordinates `(1 / p, α / p)`. -/
def typeSet (d : ℕ) (E : Set ℝ) : Set (ℝ × ℝ) :=
  {q | ∃ α : ℝ, ∃ p : ENNReal, 1 ≤ p ∧ q = (ENNReal.toReal p⁻¹, α * (ENNReal.toReal p⁻¹)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ f : (ℝ^d) → ℂ, MemLp f p (powerWeight d α) →
      MemLp (M E f) p (powerWeight d α) ∧ eLpNorm (M E f) p (powerWeight d α)
        ≤ ENNReal.ofReal C * eLpNorm f p (powerWeight d α)}

/-- The lower endpoint function in Thm. 1.1, arXiv:2602.17613 -/
def lowerEndpoint (d : ℕ) (E : Set ℝ) (p : ℝ) : ℝ :=
  ((d : ℝ) - 1) * (p - 2) - ((ν♯ E)†) (((d : ℝ) - 1) * (p - 1))

/-- The upper endpoint function in Thm. 1.1, arXiv:2602.17613 -/
def upperEndpoint (d : ℕ) (E : Set ℝ) (p : ℝ) : ℝ :=
  ((d : ℝ) - 1) * (p - 1) - β E

/-- The closed region described by Theorem 1.1. -/
def admissibleRegion (d : ℕ) (E : Set ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 = 0 ∧ q.2 ∈ Icc 0 ((d : ℝ) - 1)} ∪
  {q | ∃ p α : ℝ, 1 ≤ p ∧ q = (p⁻¹, α / p) ∧
    criticalExponent d E ≤ p ∧ lowerEndpoint d E p ≤ α ∧ α ≤ upperEndpoint d E p}

end PowerWeights

end

end Spherical
