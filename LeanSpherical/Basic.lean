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

/-- Normalized surface measure on the Euclidean unit sphere. -/
def unitSphereMeasure (d : ℕ) : Measure (Metric.sphere (0 : ℝ^d) 1) := by
  let μ : Measure (Metric.sphere (0 : ℝ^d) 1) :=
    (volume : Measure (ℝ^d)).toSphere
  exact (μ univ)⁻¹ • μ

/-- Spherical average of `f` centered at `x` with radius `t`. -/
def sphericalAverage {d : ℕ} (t : ℝ) (f : ℝ^d → ℂ) (x : ℝ^d) : ℂ :=
  ∫ y, f (x + t • (y : ℝ^d)) ∂(unitSphereMeasure d)

/-- The spherical maximal function restricted to a set of radii `E`. -/
def restrictedSphericalMaximal {d : ℕ} (E : Set ℝ) (f : ℝ^d → ℂ) (x : ℝ^d) : ENNReal :=
  ⨆ t ∈ E ∩ Ioi 0, ENNReal.ofReal ‖sphericalAverage t f x‖

@[inherit_doc restrictedSphericalMaximal]
abbrev M {d : ℕ} (E : Set ℝ) (f : ℝ^d → ℂ) (x : ℝ^d) : ENNReal :=
  restrictedSphericalMaximal E f x

end SphericalMaximal

section FractalDimensions

/-- The image of a dilation set in logarithmic coordinates. -/
def logDilationSet (E : Set ℝ) : Set ℝ :=
  {u | ∃ r : Ioi (0 : ℝ), r.1 ∈ E ∧ Real.log r.1 / Real.log 2 = u}

/-- A closed ball in the logarithmic metric on the positive radii. -/
def logBall (c : Ioi (0 : ℝ)) (r : ℝ≥0) : Set ℝ :=
  {t | 0 < t ∧ |Real.log t / Real.log 2 - Real.log c.1 / Real.log 2| ≤ r}

/-- The minimum number of logarithmic intervals of diameter `δ` needed to cover `E`. -/
def entropyNumber (E : Set ℝ) (δ : ℝ≥0) : ENat :=
  Metric.externalCoveringNumber δ (logDilationSet E)

@[inherit_doc entropyNumber]
abbrev N (E : Set ℝ) (δ : ℝ≥0) : ENat :=
  entropyNumber E δ

/-- The upper Minkowski dimension of a dilation set. -/
def upperMinkowskiExponent (E : Set ℝ) : ℝ :=
  Filter.limsup
    (fun r : NNReal ↦ ENNReal.log (⨆ c : Ioi (0 : ℝ),
      N (E ∩ (logBall c 1)) r) / (Real.log ((r : ℝ)⁻¹) : EReal))
    (𝓝[>] 0) |>.toReal

@[inherit_doc upperMinkowskiExponent]
abbrev β (E : Set ℝ) : ℝ := upperMinkowskiExponent E

/-- The Legendre--Assouad function `ν♯` of a dilation set. -/
def legendreAssouadFunction (E : Set ℝ) (ρ : ℝ) : ℝ :=
  limsup (fun r : NNReal ↦ ENNReal.log (⨆ c : Ioi 0, ⨆ R : Icc r 1,
      (R.1 : ℝ≥0∞) ^ (-ρ) * N (E ∩ (logBall c R)) r) / (Real.log (r⁻¹) : EReal))
    (𝓝[>] 0) |>.toReal


@[inherit_doc legendreAssouadFunction]
scoped notation "ν♯" => legendreAssouadFunction

/-- Generalized inverse of an increasing function. -/
def generalizedInverse (f : ℝ → ℝ) (s : ℝ) : ℝ := sSup {ρ : ℝ | 0 ≤ ρ ∧ f ρ ≤ s}

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
  volume.withDensity fun x => (ENNReal.ofReal ‖x‖) ^ α

/-- The weighted strong-type region, in coordinates `(1 / p, α / p)`. -/
def typeSet (d : ℕ) (E : Set ℝ) : Set (ℝ × ℝ) :=
  {q | ∃ α : ℝ, ∃ p : ENNReal, 1 ≤ p ∧ q = (ENNReal.toReal p⁻¹, α * (ENNReal.toReal p⁻¹)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ f : (ℝ^d) → ℂ, MemLp f p volume →
      eLpNorm (M E f) p (powerWeight d α) ≤
        ENNReal.ofReal C * eLpNorm f p (powerWeight d α)}

/-- The lower endpoint function in Thm. 1.1, arXiv:2602.17613 -/
def lowerEndpoint (d : ℕ) (E : Set ℝ) (p : ℝ) : ℝ :=
  ((d : ℝ) - 1) * (p - 2) - generalizedInverse (ν♯ E) (((d : ℝ) - 1) * (p - 1))

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
