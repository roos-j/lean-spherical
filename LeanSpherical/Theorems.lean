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
public import LeanSpherical.Auto.Spherical.FLLRS.Sec3SequenceBounds

/-!
# Main theorems

Human-readable statements of the main results of the project, in terms of the definitions in
`LeanSpherical.Definitions`. Each proof is a single application of the corresponding `Auto`
declaration.
-/

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
      eLpNorm (M E f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.SWW.eLpNorm_restrictedSphericalMaximal_le_of_memLp
    hd hE hp

/-- Sharpness up to endpoints of Seeger-Wainger-Wright theorem -/
theorem eLpNorm_restrictedSphericalMaximal_ge_of_lt_criticalExponent {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hEne : E.Nonempty) (hE : E ⊆ Ioi 0)
    (hp0 : 0 < p) (hp : p < ENNReal.ofReal (criticalExponent d E)) :
    ∀ C : ℝ, ∃ f : 𝓢(ℝ^d, ℂ), 0 < eLpNorm f p volume ∧
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

variable {d : ℕ}

/-- Thm. 1.1 of FRS, arXiv:2602.17613 for `d ≥ 2`. -/
theorem closure_typeSet_eq
    (hd : 2 ≤ d) {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi 0) :
    closure (typeSet d E) = admissibleRegion d E :=
  Auto.Spherical.PowerWeights.closure_typeSet_eq hd hE hEpos

section FLLRS

open RestrictedDilations

/-!
## Main theorems from FLLRS, arXiv:2610.18316.

**Implementation notes:** We choose to state the a priori bound for Schwartz
functions which is equivalent to the claimed boundedness.
-/

/-- Boundedness of full spherical maximal function at the critical power weight.
Thm. 1.1 of FLLRS, arXiv:2610.18316.
-/
theorem eLpNorm_sphericalMaximal_powerWeight_critical_le_schwartzMap
    (hd : 2 ≤ d) {p : ℝ≥0∞} (hp : (d : ℝ≥0∞) / (d - 1) < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M (Ioi 0) f) p (powerWeight d (1 - d)) ≤
        (ENNReal.ofReal C) * eLpNorm f p (powerWeight d (1 - d)) :=
  Auto.Spherical.FLLRS.eLpNorm_sphericalMaximal_powerWeight_critical_le_schwartzMap hd hp

/-- Boundedness of restricted spherical maximal function at the critical power weight.
Thm. 1.2 of FLLRS, arXiv:2610.18316. -/
theorem eLpNorm_restrictedSphericalMaximal_powerWeight_critical_le_schwartzMap
    (hd : 2 ≤ d) {E : Set ℝ}
    {p : ℝ≥0∞} (hp : ENNReal.ofReal (assouadDimension E / ((d : ℝ) - 1) + 1) < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ^d, ℂ),
      eLpNorm (M E f) p (powerWeight d (1 - d)) ≤
        (ENNReal.ofReal C) * eLpNorm f p (powerWeight d (1 - d)) :=
  Auto.Spherical.FLLRS.eLpNorm_restrictedSphericalMaximal_powerWeight_critical_le_schwartzMap hd hp

/-- Power weight bounds for the sequence sets.
Thm. 1.3 of FLLRS, arXiv:2610.18316.

**Implementation note:** We express boundedness of the maximal operator equivalently
as membership of the corresponding pair in the type set.
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
  Auto.Spherical.FLLRS.convexSeq_powerWeight_iff hd hμ hp₀ hpp₀

/-- Power weight bounds for the globalized sequence sets.
Thm. 1.4 of FLLRS, arXiv:2610.18316.

**Implementation note:** We express boundedness of the maximal operator equivalently
as membership of the corresponding pair in the type set.
-/
theorem globalConvexSeq_powerWeight_iff
    (hd : 2 ≤ d) {μ : ℝ} (hμ : 0 < μ) {p : ℝ} {p₀ : ℝ}
    (hp₀ : p₀ = 1 + 1 / ((μ + 1) * (d - 1))) (hpp₀ : p₀ < p)
    {α : ℝ} :
    (p⁻¹, α / p) ∈ typeSet d (toGlobalSet (convexSeq μ)) ↔
      α < (d - 1) * (p - 1) - (μ + 1)⁻¹ ∧ (p⁻¹, α / p) ∈ typeSet d (convexSeq μ) :=
  Auto.Spherical.FLLRS.globalConvexSeq_powerWeight_iff hd hμ hp₀ hpp₀

end FLLRS

end PowerWeights

end Spherical
