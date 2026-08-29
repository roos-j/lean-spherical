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
open scoped Spherical ENNReal NNReal Topology

/-- The Stein-Bourgain spherical maximal theorem -/
theorem eLpNorm_sphericalMaximal_le {d : ℕ} {p : ENNReal} (hd : 2 ≤ d)
    (hp : (d : ENNReal) / (d - 1) < p) :
    ∃ C : ℝ, ∀ f : (ℝ^d) → ℂ, MemLp f p volume → MemLp (M (Ioi (0 : ℝ)) f) p volume ∧
      eLpNorm (M (Ioi (0 : ℝ)) f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_sphericalMaximal_le hd hp

namespace RestrictedDilations

/-- Seeger-Wainger-Wright theorem -/
theorem eLpNorm_restrictedSphericalMaximal_le {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hE : E ⊆ Ioi 0)
    (hp : ENNReal.ofReal (criticalExponent d E) < p) :
    ∃ C : ℝ, ∀ f : (ℝ^d) → ℂ, MemLp f p volume → MemLp (M E f) p volume ∧
      eLpNorm (M E f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_restrictedSphericalMaximal_le
    hd hE hp

/-- Sharpness up to endpoints of Seeger-Wainger-Wright theorem -/
theorem eLpNorm_restrictedSphericalMaximal_ge_of_lt_criticalExponent {d : ℕ} {p : ℝ≥0∞}
    (hd : 2 ≤ d) {E : Set ℝ} (hEne : E.Nonempty) (hE : E ⊆ Ioi 0)
    (hp0 : 0 < p) (hp : p < ENNReal.ofReal (criticalExponent d E)) :
    ∀ C : ℝ, ∃ f : (ℝ^d) → ℂ, MemLp f p volume ∧ 0 <  eLpNorm f p volume ∧
      eLpNorm (M E f) p volume ≥ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_restrictedSphericalMaximal_ge_of_lt_criticalExponent
    hd hEne hE hp0 hp

/-- C.P. Calderon's theorem -/
theorem eLpNorm_lacunarySphericalMaximal_le {d : ℕ} {p : ℝ≥0∞} (hd : 2 ≤ d)
    (hp : 1 < p) :
    ∃ C : ℝ, ∀ f : (ℝ^d) → ℂ, MemLp f p volume → MemLp (M {2 ^ k | k : ℤ} f) p volume ∧
      eLpNorm (M {2 ^ k | k : ℤ} f) p volume ≤ (ENNReal.ofReal C) * eLpNorm f p volume :=
  Auto.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_lacunarySphericalMaximal_le
    hd hp

end RestrictedDilations


namespace FractalDilations

open Auto.Spherical.FractalDilations.AssouadSpectrum
open Auto.Spherical.FractalDilations.Definitions
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Minkowski
open Auto.Spherical.FractalDilations.StrongTypeExtension

/-- **Theorem 1 of arXiv:1909.05389** (Anderson--Hughes--Roos--Seeger,
*Spherical maximal functions and fractal dimensions of dilation sets*).

For a dilation set `E ⊆ [1, 2]` with upper Minkowski dimension `β` and
quasi-Assouad dimension `γ`, the fractal spherical maximal operator `M_E`
maps `L^p → L^q` for every exponent pair whose reciprocal point lies in
`R(β, γ) = Seg(β) ∪ interior Q(β, γ)`.  The estimate is stated on the
Schwartz core; see `hasFractalSphericalLpExtension_of_mem_R` for the
representative-independent `L^p` form. -/
theorem hasFractalSphericalStrongType_of_mem_R
    {d : ℕ} {β γ p q : ℝ}
    (hd : 3 ≤ d ∨ d = 2 ∧ γ ≤ 1 / 2)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2)
    (hβγ : 0 ≤ β ∧ β ≤ γ ∧ γ ≤ 1)
    (hMinkowski : upperMinkowskiDimension E = β)
    (hquasiAssouad : quasiAssouadDimension E = γ)
    (hp : 0 < p) (hq : 1 ≤ q)
    (hregion : reciprocalExponentPoint p q ∈ R d β γ) :
    HasFractalSphericalStrongType d E p q :=
  Auto.Spherical.FractalDilations.Theorems.theorem_one hd E hE hβγ hMinkowski
    hquasiAssouad hp hq hregion

/-- The representative-independent `L^p → L^q` form of Theorem 1 of
arXiv:1909.05389: a Lipschitz operator on `L^p` agreeing with `M_E` on the
Schwartz core and bounded into `L^q`. -/
theorem hasFractalSphericalLpExtension_of_mem_R
    {d : ℕ} {β γ p q : ℝ}
    (hd : 3 ≤ d ∨ d = 2 ∧ γ ≤ 1 / 2)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2)
    (hβγ : 0 ≤ β ∧ β ≤ γ ∧ γ ≤ 1)
    (hMinkowski : upperMinkowskiDimension E = β)
    (hquasiAssouad : quasiAssouadDimension E = γ)
    (hp : 0 < p) (hq : 0 < q) (hpone : 1 ≤ p) (hqone : 1 ≤ q)
    (hregion : reciprocalExponentPoint p q ∈ R d β γ) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hpone⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hqone⟩
    HasFractalSphericalLpExtension d E p q :=
  Auto.Spherical.FractalDilations.Theorems.theorem_one_Lp hd E hE hβγ hMinkowski
    hquasiAssouad hp hq hpone hqone hregion

end FractalDilations


namespace PowerWeights

/-- Thm. 1.1 of arXiv:2602.17613 for `d ≥ 2`. -/
theorem closure_typeSet_eq
    {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ} (hE : E.Nonempty) (hEpos : E ⊆ Ioi 0) :
    closure (typeSet d E) = admissibleRegion d E :=
  Auto.Spherical.PowerWeights.PlanarClosure.closure_typeSet_eq hd hE hEpos

end PowerWeights

namespace FractalDilations

open Auto.Spherical.FractalDilations.AssouadSpectrum
open Auto.Spherical.FractalDilations.Definitions
open Auto.Spherical.FractalDilations.ExponentRegions
open Auto.Spherical.FractalDilations.Minkowski

/-- **Theorem 1.1 of arXiv:2004.00984** (J. Roos and A. Seeger, *Spherical maximal functions
and fractal dimensions of dilation sets*, Amer. J. Math. **145** (2023), 1077--1110).

Let `d ≥ 2` and let `E ⊆ [1,2]` be a dilation set with upper Minkowski dimension `β` and
quasi-Assouad dimension `γ`.  Then `R(β,γ) ⊆ T_E`: the fractal spherical maximal operator
`M_E` maps `L^p → L^q` for every exponent pair whose reciprocal point lies in
`R(β,γ) = Seg(β) ∪ interior Q(β,γ)`.

This is the unrestricted form of Theorem 1 of arXiv:1909.05389
(`hasFractalSphericalStrongType_of_mem_R`), whose hypothesis
`3 ≤ d ∨ (d = 2 ∧ γ ≤ 1/2)` is removed here; the remaining planar case `d = 2`, `γ > 1/2`
is the new content of Roos--Seeger and is proved in
`Auto.Spherical.FractalDilations.RS.theorem_one_planar`. -/
theorem hasFractalSphericalStrongType_of_mem_R_of_two_le
    {d : ℕ} {β γ p q : ℝ} (hd : 2 ≤ d)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2)
    (hβγ : 0 ≤ β ∧ β ≤ γ ∧ γ ≤ 1)
    (hMinkowski : upperMinkowskiDimension E = β)
    (hquasiAssouad : quasiAssouadDimension E = γ)
    (hp : 0 < p) (hq : 1 ≤ q)
    (hregion : reciprocalExponentPoint p q ∈ R d β γ) :
    HasFractalSphericalStrongType d E p q :=
  Auto.Spherical.FractalDilations.RS.theorem_one_unrestricted hd hE hβγ.1 hβγ.2.1 hβγ.2.2
    hMinkowski hquasiAssouad hp hq hregion

open Auto.Spherical.FractalDilations.RS in
/-- **Theorem 1.2(i) of arXiv:2004.00984** (J. Roos and A. Seeger, *Spherical maximal functions
and fractal dimensions of dilation sets*, Amer. J. Math. **145** (2023), 1077--1110).

A set `W` in the reciprocal-exponent plane is the closure of the type set
`T_E = {(1/p,1/q) : M_E : L^p → L^q}` of some nonempty dilation set `E ⊆ [1,2]` if and only if
`W` is closed, convex and satisfies `Q(β,γ) ⊆ W ⊆ Q(β,β)` for some `0 ≤ β ≤ γ ≤ 1`. -/
theorem closure_fractalTypeSet_iff_isClosed_convex_sandwich {d : ℕ} (hd : 2 ≤ d)
    (W : Set ExponentPoint) :
    (∃ E : Set ℝ, E ⊆ Icc (1 : ℝ) 2 ∧ E.Nonempty ∧ closure (fractalTypeSet d E) = W) ↔
      (IsClosed W ∧ Convex ℝ W ∧ ∃ β γ : ℝ, 0 ≤ β ∧ β ≤ γ ∧ γ ≤ 1 ∧
        Q d β γ ⊆ W ∧ W ⊆ Q d β β) :=
  Auto.Spherical.FractalDilations.RS.closure_fractalTypeSet_iff_isClosed_convex_sandwich hd W

open Auto.Spherical.FractalDilations.RS in
/-- **Theorem 1.2(ii) of arXiv:2004.00984.**

If the closure of the type set of `E ⊆ [1,2]` satisfies `Q(β,γ) ⊆ closure (T_E) ⊆ Q(β,β)`, then
`β` is the upper Minkowski dimension of `E`; and if moreover `γ` is chosen minimally, then `γ`
is the quasi-Assouad dimension of `E`. -/
theorem dimensions_of_sandwich_closure_fractalTypeSet {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {β γ : ℝ}
    (hβ : 0 ≤ β) (hβγ : β ≤ γ) (hγ : γ ≤ 1)
    (hlower : Q d β γ ⊆ closure (fractalTypeSet d E))
    (hupper : closure (fractalTypeSet d E) ⊆ Q d β β) :
    upperMinkowskiDimension E = β ∧
      ((∀ g : ℝ, β ≤ g → g ≤ 1 → Q d β g ⊆ closure (fractalTypeSet d E) → γ ≤ g) →
        quasiAssouadDimension E = γ) :=
  Auto.Spherical.FractalDilations.RS.dimensions_of_sandwich_closure_fractalTypeSet hd hE hEne
    hβ hβγ hγ hlower hupper

end FractalDilations

end Spherical
