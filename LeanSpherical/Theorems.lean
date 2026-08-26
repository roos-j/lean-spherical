/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

import LeanSpherical.Definitions
import LeanSpherical.Codex.Spherical.FractalDilations.DiagonalTheorem
import LeanSpherical.Codex.Spherical.MSS
import LeanSpherical.Codex.Spherical.PowerWeights.PowerWeightTheorem
import LeanSpherical.Codex.PowerWeights.DuoandikoetxeaVega

namespace Spherical

open Filter MeasureTheory Set Topology ENNReal
open scoped Spherical ENNReal NNReal Topology

/-- The Stein-Bourgain spherical maximal theorem -/
theorem eLpNorm_sphericalMaximal_le {d : ℕ} {p : ENNReal} (hd : 2 ≤ d)
    (hp : (d : ENNReal) / (d - 1) < p) :
    ∃ C : ℝ, ∀ f : (ℝ^d) → ℂ, MemLp f p volume → MemLp (M (Ioi (0 : ℝ)) f) p volume ∧
      eLpNorm (M (Ioi (0 : ℝ)) f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Codex.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_sphericalMaximal_le hd hp

namespace RestrictedDilations

/-- Seeger-Wainger-Wright theorem -/
theorem eLpNorm_restrictedSphericalMaximal_le {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hE : E ⊆ Ioi 0)
    (hp : ENNReal.ofReal (criticalExponent d E) < p) :
    ∃ C : ℝ, ∀ f : (ℝ^d) → ℂ, MemLp f p volume → MemLp (M E f) p volume ∧
      eLpNorm (M E f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Codex.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_restrictedSphericalMaximal_le
    hd hE hp

/-- Sharpness up to endpoints of Seeger-Wainger-Wright theorem -/
theorem eLpNorm_restrictedSphericalMaximal_ge_of_lt_criticalExponent {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hEne : E.Nonempty) (hE : E ⊆ Ioi 0)
    (hp0 : 0 < p) (hp : p < ENNReal.ofReal (criticalExponent d E)) :
    ∀ C : ℝ, ∃ f : (ℝ^d) → ℂ, MemLp f p volume ∧ 0 <  eLpNorm f p volume ∧
      eLpNorm (M E f) p volume ≥ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Codex.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_restrictedSphericalMaximal_ge_of_lt_criticalExponent
    hd hEne hE hp0 hp

/-- C.P. Calderon's theorem -/
theorem eLpNorm_lacunarySphericalMaximal_le {d : ℕ} {p : ℝ≥0∞} (hd : 2 ≤ d)
    (hp : 1 < p) :
    ∃ C : ℝ, ∀ f : (ℝ^d) → ℂ, MemLp f p volume → MemLp (M {2 ^ k | k : ℤ} f) p volume ∧
      eLpNorm (M {2 ^ k | k : ℤ} f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Codex.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_lacunarySphericalMaximal_le
    hd hp

end RestrictedDilations


namespace PowerWeights

/-- The planar negative-power circular maximal theorem: the negative-weight
planar case of Thm. 10 of Duoandikoetxea-Vega, J. London Math. Soc. (2) 53
(1996), 343-353. -/
theorem eLpNorm_circularMaximal_powerWeight_le_of_neg {p : ENNReal} {α : ℝ}
    (hp_top : p ≠ ∞) (hp : (2 : ENNReal) < p) (hα_lower : -1 < α) (hα_upper : α < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (ℝ^2) → ℂ, MemLp f p (powerWeight 2 α) →
      MemLp (M (Ioi (0 : ℝ)) f) p (powerWeight 2 α) ∧
        eLpNorm (M (Ioi (0 : ℝ)) f) p (powerWeight 2 α) ≤
          (ENNReal.ofReal C) * eLpNorm f p (powerWeight 2 α) :=
  Codex.PowerWeights.DuoandikoetxeaVega.eLpNorm_circularMaximal_powerWeight_le_of_neg
    hp_top hp hα_lower hα_upper

/-- Thm. 1.1 of arXiv:2602.17613 for `d ≥ 2`. -/
theorem closure_typeSet_eq
    {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi 0) :
    closure (typeSet d E) = admissibleRegion d E :=
  Codex.PowerWeights.DuoandikoetxeaVega.closure_typeSet_eq hd hE hEpos

end PowerWeights

end Spherical
