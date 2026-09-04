/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

import LeanSpherical.Definitions
import LeanSpherical.Auto.Spherical.FractalDilations.AHRSUpperBounds
import LeanSpherical.Auto.Spherical.FractalDilations.RSTypeSetCharacterization

namespace Spherical

open Filter MeasureTheory Set Topology ENNReal
open scoped Spherical ENNReal NNReal Topology SchwartzMap

/-- Spherical maximal theorem (`d = 2`: Bourgain, `d ≥ 3`: Stein), a priori estimate -/
theorem eLpNorm_sphericalMaximal_le_schwartzMap {d : ℕ} {p : ℝ≥0∞} (hd : 2 ≤ d)
    (hp : (d : ℝ≥0∞) / (d - 1) < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M (Ioi 0) f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume := by
  sorry

/-- Spherical maximal theorem (`d = 2`: Bourgain, `d ≥ 3`: Stein), `L^p` version -/
theorem eLpNorm_sphericalMaximal_le {d : ℕ} {p : ℝ≥0∞} (hd : 2 ≤ d)
    (hp : (d : ℝ≥0∞) / (d - 1) < p) :
    ∃ C : ℝ, ∀ f : (ℝ^d) → ℂ, MemLp f p volume →
      ∀ᵐ x ∂volume, ∀ t ∈ Ioi 0,
        Integrable (fun y : unitSphere d ↦ f (x + t • (y : ℝ^d))) (unitSphereMeasure d) ∧
      MemLp (M (Ioi 0) f) p volume ∧
      eLpNorm (M (Ioi 0) f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  sorry
  -- Auto.Spherical.FractalDilations.AHRSUpperBounds.eLpNorm_sphericalMaximal_le hd hp

/-- Sharpness of Bourgain's and Stein's theorems -/
theorem eLpNorm_sphericalMaximal_eq_top_of_le_criticalExponent {d : ℕ} {p : ℝ≥0∞} (hd : 2 ≤ d)
    (hp0 : 0 < p) (hp : p ≤ (d : ℝ≥0∞) / (d - 1)) :
    ∃ f : 𝓢(ℝ^d, ℂ), 0 < eLpNorm f p volume ∧
      eLpNorm (M (Ioi 0) f) p volume = ⊤ := by
  sorry

namespace RestrictedDilations

/-- Seeger-Wainger-Wright theorem, a priori estimate -/
theorem eLpNorm_restrictedSphericalMaximal_le_schwartzMap {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hE : E ⊆ Ioi 0)
    (hp : ENNReal.ofReal (criticalExponent d E) < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M E f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume := by
  sorry

/-- Seeger-Wainger-Wright theorem, `L^p` version -/
theorem eLpNorm_restrictedSphericalMaximal_le {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hE : E ⊆ Ioi 0)
    (hp : ENNReal.ofReal (criticalExponent d E) < p) :
    ∃ C : ℝ, ∀ f : (ℝ^d) → ℂ, MemLp f p volume →
      ∀ᵐ x ∂volume, ∀ t ∈ E,
        Integrable (fun y : unitSphere d ↦ f (x + t • (y : ℝ^d))) (unitSphereMeasure d) ∧
      MemLp (M E f) p volume ∧
      eLpNorm (M E f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  sorry
  -- Auto.Spherical.FractalDilations.AHRSUpperBounds.eLpNorm_restrictedSphericalMaximal_le
  --   hd hE hp

/-- Sharpness up to endpoints of Seeger-Wainger-Wright theorem -/
theorem eLpNorm_restrictedSphericalMaximal_ge_of_lt_criticalExponent {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hEne : E.Nonempty) (hE : E ⊆ Ioi 0)
    (hp0 : 0 < p) (hp : p < ENNReal.ofReal (criticalExponent d E)) :
    ∀ C : ℝ, ∃ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M E f) p volume ≥ (ENNReal.ofReal C) * eLpNorm f p volume :=
  sorry
  -- Auto.Spherical.FractalDilations.AHRSUpperBounds.eLpNorm_restrictedSphericalMaximal_ge_of_lt_criticalExponent
  --   hd hEne hE hp0 hp

/-- C.P. Calderon's theorem -/
theorem eLpNorm_lacunarySphericalMaximal_le_schwartzMap {d : ℕ} {p : ℝ≥0∞} (hd : 2 ≤ d)
    (hp : 1 < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M {2 ^ k | k : ℤ} f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  sorry
  -- Auto.Spherical.FractalDilations.AHRSUpperBounds.eLpNorm_lacunarySphericalMaximal_le hd hp

end RestrictedDilations

namespace PowerWeights

/-- Thm. 1.1 of arXiv:2602.17613 for `d ≥ 2`. -/
theorem closure_typeSet_eq
    {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi 0) :
    closure (typeSet d E) = admissibleRegion d E :=
  Auto.Spherical.FractalDilations.AHRSUpperBounds.closure_typeSet_eq hd hE hEpos

end PowerWeights

end Spherical
