/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.MetricSpace.CoveringNumbers
-- Modules re-exported to keep the pre-module-system import visibility.
public import Aesop.Constants
public import Aesop.Exception
public import Aesop.Forward.State.ApplyGoalDiff
public import Aesop.Forward.State.Initial
public import Aesop.Script.OptimizeSyntax
public import Aesop.Script.StructureDynamic
public import Aesop.Script.StructureStatic
public import Aesop.Script.UScriptToSScript
public import Aesop.Script.Util
public import Aesop.Search.Expansion.Basic
public import Aesop.Search.Expansion.Simp
public import Aesop.Search.Queue
public import Aesop.Tree.Free
public import Aesop.Tree.Stats
public import Aesop.Util.EqualUpToIds
public import Aesop.Util.Tactic
public import Aesop.Util.Tactic.Unfold
public import Aesop.Util.UnionFind
public import Batteries.Data.UInt
public import Batteries.Lean.HashSet
public import Batteries.Lean.Meta.DiscrTree
public import Batteries.Lean.Meta.Inaccessible
public import Batteries.Lean.PersistentHashSet
public import ImportGraph.Imports.ImportGraph
public import ImportGraph.Lean.Environment
public import Init.Control.Option
public import Init.Control.Reader
public import Init.Control.State
public import Init.Control.StateRef
public import Lean.Compiler.IR.CompilerM
public import Lean.Meta.CollectMVars
public import Lean.Meta.DiscrTree.Main
public import Lean.Meta.SynthInstance
public import Lean.Meta.Tactic.Simp.Rewrite
public import Lean.Meta.Tactic.Split
public import Lean.Meta.WHNF
public import Lean.Parser.Term.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Data.List.Enum
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.DSimpPercent
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

/-!

# Basic definitions for this project

-/

namespace Spherical

open Filter MeasureTheory Set Topology ENNReal
open scoped ENNReal NNReal Topology SchwartzMap

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

/-- The upper Minkowski dimension of a dilation set. -/
def upperMinkowskiExponent (E : Set ℝ) : ℝ :=
  limsup (fun r : NNReal ↦ ENNReal.log (⨆ c : Ioi (0 : ℝ),
      N (E ∩ (logBall c 1)) r) / (Real.log ((r : ℝ)⁻¹) : EReal))
    (𝓝[>] 0) |>.toReal

@[inherit_doc upperMinkowskiExponent]
abbrev β (E : Set ℝ) : ℝ := upperMinkowskiExponent E

/-- The upper Assouad spectrum at `θ`.

**Implementation note:** This is only intended to be used for `θ : Ico 0 1`
but totalized as usual to all real numbers.
-/
def upperAssouadSpectrum (E : Set ℝ) (θ : ℝ) : ℝ :=
  limsup (fun r : NNReal ↦ ⨆ c : Ioi (0 : ℝ), ⨆ R : Icc (r ^ θ) 1,
      ENNReal.log (N (E ∩ (logBall c R)) r) /
        (Real.log ((R.1 : ℝ) / (r : ℝ)) : EReal))
    (𝓝[>] 0) |>.toReal

/-- The quasi-Assouad dimension of a dilation set. -/
def quasiAssouadDimension (E : Set ℝ) : ℝ :=
  limsup (upperAssouadSpectrum E) (𝓝[<] 1)

@[inherit_doc quasiAssouadDimension]
abbrev γ (E : Set ℝ) : ℝ := quasiAssouadDimension E

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

/-- The vertex `Q₁ = (0, 0)`, representing the (trivial) `L^∞` estimate. -/
def Q₁ : ℝ × ℝ := (0, 0)

/-- The vertex `Q₂(β)` on the diagonal. -/
def Q₂ (d : ℕ) (β : ℝ) : ℝ × ℝ :=
  ((d - 1) / (d - 1 + β), (d - 1) / (d - 1 + β))

/-- The vertex `Q₃(β)`. -/
def Q₃ (d : ℕ) (β : ℝ) : ℝ × ℝ :=
  ((d - β) / (d - β + 1), 1 / (d - β + 1))

/-- The vertex `Q₄(γ)`. -/
def Q₄ (d : ℕ) (γ : ℝ) : ℝ × ℝ :=
  (d * (d - 1) / (d ^ 2 + 2 * γ - 1), (d - 1) / (d ^ 2 + 2 * γ - 1))

/-- The closed quadrilateral `Q(β, γ)`, the convex hull of `Q₁, Q₂(β), Q₃(β), Q₄(γ)`. -/
def quadrilateral (d : ℕ) (β γ : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {Q₁, Q₂ d β, Q₃ d β, Q₄ d γ}

/-- The region `R(β, γ)` in Thm. 1.1, arXiv:2004.00984: the interior of `Q(β, γ)` together with
the half-open segment `[Q₁, Q₂(β))`. -/
def strongTypeRegion (d : ℕ) (β γ : ℝ) : Set (ℝ × ℝ) :=
  (segment ℝ Q₁ (Q₂ d β) \ {Q₂ d β}) ∪ interior (quadrilateral d β γ)

/-- The strong-type region of `M E`, in coordinates `(1 / p, 1 / q)`.
**Implementation note:** We prefer to use a priori estimates on Schwartz functions.
-/
def typeSet (d : ℕ) (E : Set ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ p q : ℝ≥0∞, 1 ≤ p ∧ 1 ≤ q ∧ z = (ENNReal.toReal p⁻¹, ENNReal.toReal q⁻¹) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(ℝ^d, ℂ),
      MemLp (M E f) q volume ∧ eLpNorm (M E f) q volume ≤ ENNReal.ofReal C * eLpNorm f p volume}

end RestrictedDilations

namespace PowerWeights

open RestrictedDilations

/-- Lebesgue measure weighted by the radial power `|x|^α`. -/
def powerWeight (d : ℕ) (α : ℝ) : Measure (ℝ^d) :=
  volume.withDensity fun x ↦ (ENNReal.ofReal ‖x‖) ^ α

/-- The weighted strong-type region, in coordinates `(1 / p, α / p)`.

**Implementation note:** We prefer to use a priori estimates on Schwartz functions
for finite `p` and take a union with the point `(0, 0)` representing the (trivial) `L^∞` estimate.
-/
def typeSet (d : ℕ) (E : Set ℝ) : Set (ℝ × ℝ) :=
  {(0, 0)} ∪ {q | ∃ α : ℝ, ∃ p : ℝ≥0∞, 1 ≤ p ∧ q = (ENNReal.toReal p⁻¹, α * (ENNReal.toReal p⁻¹)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(ℝ^d, ℂ), MemLp f p (powerWeight d α) →
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
