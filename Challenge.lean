/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
This file was assembled by Codex from the human-written files `LeanSpherical/Definitions.lean`, `LeanSpherical/Theorems.lean`.
No comments were added by Codex.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Challenge file for Comparator
-/

@[expose] public section

namespace Spherical
open Filter MeasureTheory Set Topology ENNReal
open scoped ENNReal NNReal Topology SchwartzMap
noncomputable section
/- `d`-dimensional real Euclidean space. -/
scoped notation "ℝ^" d:arg => EuclideanSpace ℝ (Fin d)

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

/-- The image of a dilation set in logarithmic coordinates. -/
def logDilationSet (E : Set ℝ) : Set ℝ :=
  {u | ∃ r : Ioi (0 : ℝ), r.1 ∈ E ∧ Real.log r.1 / Real.log 2 = u}

/-- A closed ball in the logarithmic metric on the positive radii. -/
def logBall (c : Ioi (0 : ℝ)) (r : ℝ≥0) : Set ℝ :=
  {t | 0 < t ∧ |Real.log t / Real.log 2 - Real.log c.1 / Real.log 2| ≤ r}

/-- The minimum number of logarithmic balls of radius `δ` needed to cover `E`. -/
def entropyNumber (E : Set ℝ) (δ : ℝ≥0) : ENat :=
  Metric.externalCoveringNumber δ (logDilationSet E)

@[inherit_doc entropyNumber]
abbrev N (E : Set ℝ) (δ : ℝ≥0) : ENat := entropyNumber E δ

/-- The Assouad dimension of a dilation set. -/
def assouadDimension (E : Set ℝ) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ ∃ C : ℝ, 0 < C ∧ ∀ c : Ioi 0, ∀ δ R : ℝ≥0,
    0 < δ → δ ≤ R → R ≤ 1 → N (E ∩ logBall c R) δ ≤ ENNReal.ofReal (C * (R / δ) ^ s) }

namespace RestrictedDilations
/-- The usual convex sequence example in `[1, 2]`. This will only be used for `0 < μ`. -/
def convexSeq (μ : ℝ) : Set ℝ := { x | ∃ n : ℕ, 1 ≤ n ∧ x = 1 + n ^ (-μ) }

/-- Given a (local) dilation set `E`, this is the global dilation set `⋃ k ∈ ℤ, 2^k E`. -/
def toGlobalSet (E : Set ℝ) : Set ℝ := ⋃ k : ℤ, (fun x : ℝ ↦ (2 : ℝ) ^ k * x) '' E

end RestrictedDilations

namespace PowerWeights
/-- Lebesgue measure weighted by the radial power `|x|^α`. -/
def powerWeight (d : ℕ) (α : ℝ) : Measure (ℝ^d) :=
  volume.withDensity fun x ↦ (ENNReal.ofReal ‖x‖) ^ α

/-- The weighted strong-type region, in coordinates `(1 / p, α / p)`.
-/
def typeSet (d : ℕ) (E : Set ℝ) : Set (ℝ × ℝ) :=
  {(0, 0)} ∪ {q | ∃ α : ℝ, ∃ p : ℝ≥0∞, 1 ≤ p ∧ q = (ENNReal.toReal p⁻¹, α * (ENNReal.toReal p⁻¹)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(ℝ^d, ℂ), MemLp f p (powerWeight d α) →
      eLpNorm (M E f) p (powerWeight d α)
        ≤ ENNReal.ofReal C * eLpNorm f p (powerWeight d α)}


variable {d : ℕ}

section FLLRS

open RestrictedDilations

/-- Boundedness of full spherical maximal function at the critical power weight.
Thm. 1.1 of FLLRS, arXiv:2610.18316.
-/
theorem eLpNorm_sphericalMaximal_powerWeight_critical_le_schwartzMap
    (hd : 2 ≤ d) {p : ℝ≥0∞} (hp : (d : ℝ≥0∞) / (d - 1) < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M (Ioi 0) f) p (powerWeight d (1 - d)) ≤
        (ENNReal.ofReal C) * eLpNorm f p (powerWeight d (1 - d)) :=
  sorry

/-- Boundedness of restricted spherical maximal function at the critical power weight.
Thm. 1.2 of FLLRS, arXiv:2610.18316. -/
theorem eLpNorm_restrictedSphericalMaximal_powerWeight_critical_le_schwartzMap
    (hd : 2 ≤ d) {E : Set ℝ}
    {p : ℝ≥0∞} (hp : ENNReal.ofReal (assouadDimension E / ((d : ℝ) - 1) + 1) < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M E f) p (powerWeight d (1 - d)) ≤
        (ENNReal.ofReal C) * eLpNorm f p (powerWeight d (1 - d)) :=
  sorry

/-- Power weight bounds for the sequence sets.
Thm. 1.3 of FLLRS, arXiv:2610.18316.
 -/
theorem convexSeq_powerWeight_iff
    (hd : 2 ≤ d) {μ : ℝ} (hμ : 0 < μ) {p : ℝ} {p₀ : ℝ}
    (hp₀ : p₀ = 1 + 1 / ((μ + 1) * (d - 1))) (hpp₀ : p₀ < p)
    {α : ℝ} :
    (p⁻¹, α / p) ∈ typeSet d (convexSeq μ) ↔
      d / (d - 1) < p ∧ 1 - d ≤ α ∧ α ≤ (d - 1) * (p - 1) - 1 / (μ + 1) ∨
      p = d / (d - 1) ∧ 1 - d < α ∧ α ≤ (d - 1) * (d / (d - 1) - 1) - 1 / (μ + 1) ∨
      p < d / (d - 1) ∧
        1 - d + (d - (d - 1) * p) / μ ≤ α ∧ α ≤ (d - 1) * (p - 1) - 1 / (μ + 1) :=
  sorry

/-- Power weight bounds for the globalized sequence sets.
Thm. 1.4 of FLLRS, arXiv:2610.18316.
-/
theorem globalConvexSeq_powerWeight_iff
    (hd : 2 ≤ d) {μ : ℝ} (hμ : 0 < μ) {p : ℝ} {p₀ : ℝ}
    (hp₀ : p₀ = 1 + 1 / ((μ + 1) * (d - 1))) (hpp₀ : p₀ < p)
    {α : ℝ} :
    (p⁻¹, α / p) ∈ typeSet d (toGlobalSet (convexSeq μ)) ↔
      α < (d - 1) * (p - 1) - (μ + 1)⁻¹ ∧ (p⁻¹, α / p) ∈ typeSet d (convexSeq μ) :=
  sorry

end FLLRS

end PowerWeights
end
end Spherical
