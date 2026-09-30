/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

module

public import LeanSpherical.Definitions
public import LeanSpherical.Auto.Spherical.AHRS.TheoremOne
public import LeanSpherical.Auto.Spherical.SWW
public import LeanSpherical.Auto.Spherical.PowerWeights.PlanarClosure
public import LeanSpherical.Auto.Spherical.RS.TypeSetCharacterization

@[expose] public section

namespace Spherical

open Filter MeasureTheory Set Topology ENNReal
open scoped Spherical ENNReal NNReal Topology SchwartzMap

/-- Spherical maximal theorem (`d = 2`: Bourgain, `d ≥ 3`: Stein), a priori estimate -/
theorem eLpNorm_sphericalMaximal_le_schwartzMap {d : ℕ} {p : ℝ≥0∞} (hd : 2 ≤ d)
    (hp : (d : ℝ≥0∞) / (d - 1) < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M (Ioi 0) f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.SWW.eLpNorm_sphericalMaximal_le_schwartzMap hd hp

/-- Spherical maximal theorem (`d = 2`: Bourgain, `d ≥ 3`: Stein), `L^p` version -/
theorem eLpNorm_sphericalMaximal_le {d : ℕ} {p : ℝ≥0∞} (hd : 2 ≤ d)
    (hp : (d : ℝ≥0∞) / (d - 1) < p) :
    ∃ C : ℝ, ∀ f : (ℝ^d) → ℂ, MemLp f p volume →
      ∀ᵐ x ∂volume, ∀ t ∈ Ioi (0 : ℝ),
        Integrable (fun y : unitSphere d ↦ f (x + t • (y : ℝ^d))) (unitSphereMeasure d) ∧
      MemLp (M (Ioi 0) f) p volume ∧
      eLpNorm (M (Ioi 0) f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.SWW.eLpNorm_sphericalMaximal_le_of_memLp hd hp

/-- Sharpness of Bourgain's and Stein's theorems -/
theorem eLpNorm_sphericalMaximal_eq_top_of_le_criticalExponent {d : ℕ} {p : ℝ≥0∞} (hd : 2 ≤ d)
    (hp0 : 0 < p) (hp : p ≤ (d : ℝ≥0∞) / (d - 1)) :
    ∃ f : 𝓢(ℝ^d, ℂ), 0 < eLpNorm f p volume ∧
      eLpNorm (M (Ioi 0) f) p volume = ⊤ :=
  Auto.Spherical.SWW.eLpNorm_sphericalMaximal_eq_top_schwartzMap
    hd hp0 hp

namespace RestrictedDilations

/-- Seeger-Wainger-Wright theorem, a priori estimate -/
theorem eLpNorm_restrictedSphericalMaximal_le_schwartzMap {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hE : E ⊆ Ioi 0)
    (hp : ENNReal.ofReal (criticalExponent d E) < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M E f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.SWW.eLpNorm_restrictedSphericalMaximal_le_schwartzMap
    hd hE hp

/-- Seeger-Wainger-Wright theorem, `L^p` version -/
theorem eLpNorm_restrictedSphericalMaximal_le {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hE : E ⊆ Ioi 0)
    (hp : ENNReal.ofReal (criticalExponent d E) < p) :
    ∃ C : ℝ, ∀ f : (ℝ^d) → ℂ, MemLp f p volume →
      ∀ᵐ x ∂volume, ∀ t ∈ E,
        Integrable (fun y : unitSphere d ↦ f (x + t • (y : ℝ^d))) (unitSphereMeasure d) ∧
      MemLp (M E f) p volume ∧
      eLpNorm (M E f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.SWW.eLpNorm_restrictedSphericalMaximal_le_of_memLp
    hd hE hp

/-- Sharpness up to endpoints of Seeger-Wainger-Wright theorem -/
theorem eLpNorm_restrictedSphericalMaximal_ge_of_lt_criticalExponent {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hEne : E.Nonempty) (hE : E ⊆ Ioi 0)
    (hp0 : 0 < p) (hp : p < ENNReal.ofReal (criticalExponent d E)) :
    ∀ C : ℝ, ∃ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M E f) p volume ≥ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.SWW.eLpNorm_restricted_ge_schwartz hd hEne hE hp0 hp

/-- C.P. Calderon's theorem -/
theorem eLpNorm_lacunarySphericalMaximal_le_schwartzMap {d : ℕ} {p : ℝ≥0∞} (hd : 2 ≤ d)
    (hp : 1 < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M {2 ^ k | k : ℤ} f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.SWW.eLpNorm_lacunarySphericalMaximal_le_schwartzMap
    hd hp

/-- Thm. 1.1 of Roos-Seeger, arXiv:2004.00984 -/
theorem strongTypeRegion_subset_typeSet {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ} (hE : E ⊆ Icc 1 2) :
    strongTypeRegion d (β E) (γ E) ⊆ typeSet d E :=
  Auto.Spherical.RS.strongTypeRegion_subset_typeSet hd hE

/-- **Typeset characterization theorem**.
Thm. 1.2 (i) of Roos-Seeger, arXiv:2004.00984. -/
theorem exists_closure_typeSet_eq_iff {d : ℕ} (hd : 2 ≤ d) (W : Set (ℝ × ℝ)) :
    (∃ E ⊆ Icc (1 : ℝ) 2, E.Nonempty ∧ closure (typeSet d E) = W) ↔
      IsClosed W ∧ Convex ℝ W ∧ ∃ b g : ℝ, 0 ≤ b ∧ b ≤ g ∧ g ≤ 1 ∧
        quadrilateral d b g ⊆ W ∧ W ⊆ quadrilateral d b b :=
  Auto.Spherical.RS.exists_closure_typeSet_eq_iff hd W

/-- Thm. 1.2 (ii) of Roos-Seeger, arXiv:2004.00984 -/
theorem β_eq_and_γ_eq {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ} (hE : E ⊆ Icc 1 2)
    {b g : ℝ} (hb : 0 ≤ b) (hbg : b ≤ g) (hg : g ≤ 1)
    (hlow : quadrilateral d b g ⊆ closure (typeSet d E))
    (hupp : closure (typeSet d E) ⊆ quadrilateral d b b) :
    β E = b ∧
      ((∀ g' : ℝ, b ≤ g' → g' ≤ 1 → quadrilateral d b g' ⊆ closure (typeSet d E) → g ≤ g') →
        γ E = g) :=
  Auto.Spherical.RS.β_eq_and_γ_eq
    hd hE hb hbg hg hlow hupp

end RestrictedDilations

namespace PowerWeights

/-- Thm. 1.1 of arXiv:2602.17613 for `d ≥ 2`. -/
theorem closure_typeSet_eq
    {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi 0) :
    closure (typeSet d E) = admissibleRegion d E :=
  Auto.Spherical.PowerWeights.closure_typeSet_eq hd hE hEpos

end PowerWeights

end Spherical
