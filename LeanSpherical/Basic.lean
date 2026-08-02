/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

import Mathlib

-- import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
-- import Mathlib.MeasureTheory.MeasurableSpace.Basic
-- import Mathlib.Topology.MetricSpace.CoveringNumbers


/-!

# Basic definitions for this project

* spherical maximal function restricted to a set


-/

namespace Spherical

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section


section SphericalMaximal

/-- `d` dimensional real Euclidean space. -/
scoped notation "ℝ^" d => EuclideanSpace ℝ (Fin d)

/-- Surface measure on the Euclidean unit sphere. -/
def unitSphereMeasure (d : ℕ) : Measure (Metric.sphere (0 : ℝ^d) 1) := volume.toSphere

@[inherit_doc unitSphereMeasure]
scoped notation "σ" => unitSphereMeasure

/-- Spherical average of `f` centered at `x` with radius `t`. -/
def sphericalAverage {d : ℕ} (t : ℝ) (f : (ℝ^d) → ℂ) (x : ℝ^d) : ℂ :=
  ∫ y, f (x + t • (y : ℝ^d)) ∂σ d

@[inherit_doc sphericalAverage]
abbrev A {d : ℕ} (t : ℝ) (f : (ℝ^d) → ℂ) (x : ℝ^d) : ℂ := sphericalAverage t f x


/-- The spherical maximal function restricted to `E`. -/
def restrictedSphericalMaximal {d : ℕ} (E : Set ℝ) (f : (ℝ^d) → ℂ) (x : ℝ^d) : ENNReal :=
  ⨆ t ∈ E ∩ Ioi 0, ENNReal.ofReal ‖A t f x‖

@[inherit_doc restrictedSphericalMaximal]
abbrev ℳ {d : ℕ} (E : Set ℝ) (f : (ℝ^d) → ℂ) (x : ℝ^d) := restrictedSphericalMaximal E f x

end SphericalMaximal

section FractalDimensions

/-- The `log 2` image of a dilation set. -/
def logDilationSet (E : Set ℝ) : Set ℝ := {u | ∃ r : Ioi 0, r.1 ∈ E ∧ Real.log r.1 / Real.log 2 = u}

/-- A closed ball centered at `c` of radius `r` in the logarithmatic metric on `(0, ∞)`
  (meant to be applied only when `E ⊆ (0, ∞)`). -/
def logBall (c : Ioi (0 : ℝ)) (r : ℝ) : Set ℝ :=
  {t | 0 < t ∧ |(Real.log t / Real.log 2) - (Real.log c.1 / Real.log 2)| ≤ r}

/-- The minimum number of `δ` balls in the logarithmic metric required to cover `E` -/
def entropyNumber (E : Set ℝ) (δ : NNReal) : ENat :=
  Metric.externalCoveringNumber δ (logDilationSet E)

@[inherit_doc entropyNumber]
abbrev

end
