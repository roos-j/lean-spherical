/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/


import LeanSpherical.Auto.Spherical.FractalDilations.AHRSUpperBounds
import LeanSpherical.Auto.Spherical.FractalDilations.BRRS

/-!
# Beltran--Roos--Seeger: spherical maximal operators on radial functions

Formalization of the main results of arXiv:2412.09390 (Studia Math. 289
(2026), 1--32).  All BRS material lives in this file.  See
`automation/Instructions-brs.md` for the working rules and
`automation/Status-BRS.md` for the dependency ledger.
-/

namespace Auto.Spherical.FractalDilations.BRSRadial

open Filter MeasureTheory Set Topology ENNReal
open _root_.Spherical _root_.Spherical.RestrictedDilations
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.BRRS
open Auto.Spherical.FractalDilations.Auxiliary
open scoped Spherical ENNReal NNReal Topology

noncomputable section

/-! ## The radial type set

BRS studies the spherical maximal operator `M_E` acting on radial functions.
The radial type set `𝒯^rad_E` is the set of reciprocal exponent pairs
`(1/p, 1/q)` for which `M_E` is bounded from the radial subspace of `L^p` to
`L^q`.  Radiality is the reusable norm-radiality predicate from the radial
Fourier development. -/

/-- Strong `L^p_rad → L^q` boundedness of the spherical maximal operator with
dilations restricted to `E`. -/
def HasRadialStrongType (d : ℕ) (E : Set ℝ) (p q : ENNReal) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : (ℝ^d) → ℂ, MemLp f p volume →
    _root_.Auto.RadialFourierTransform.IsNormRadial f →
      MemLp (M E f) q volume ∧
        eLpNorm (M E f) q volume ≤ ENNReal.ofReal C * eLpNorm f p volume

/-- The radial type set `𝒯^rad_E` of BRS, in the reciprocal coordinates
`(1/p, 1/q)` with `1 ≤ p, q ≤ ∞`. -/
def radialTypeSet (d : ℕ) (E : Set ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ p q : ENNReal, 1 ≤ p ∧ 1 ≤ q ∧
    z = (ENNReal.toReal p⁻¹, ENNReal.toReal q⁻¹) ∧ HasRadialStrongType d E p q}

/-! ## The radial profile isometry

BRS works throughout with the profile `f₀` of a radial function `f`, and with
the measure `s^{d-1} ds` on `(0,∞)`.  Polar coordinates identify the two
`L^p` norms up to the total surface mass of the unit sphere. -/

/-- The `L^p` norm of a radial function in polar coordinates: it is the
`L^p(s^{d-1} ds)` norm of its profile times the total surface mass. -/
theorem eLpNorm_of_isNormRadial {d : ℕ} (hd : 0 < d) {p : ℝ} (hp : 0 < p)
    (f : (ℝ^d) → ℂ)
    (hf : _root_.Auto.RadialFourierTransform.IsNormRadial f) (hfm : Measurable f)
    (w : ℝ^d) (hw : ‖w‖ = 1) :
    eLpNorm f (ENNReal.ofReal p) volume =
      (ENNReal.ofReal (surfaceMass d)) ^ (1 / p) *
        (∫⁻ r : Ioi (0 : ℝ), (ENNReal.ofReal ‖f (r.1 • w)‖) ^ p
          ∂Measure.volumeIoiPow (d - 1)) ^ (1 / p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, ENNReal.toReal_ofReal hp.le]
  have hnorm : ∀ x : (ℝ^d), ‖f x‖ₑ = ENNReal.ofReal ‖f x‖ := fun x => (ofReal_norm _).symm
  simp only [hnorm]
  rw [brrs_lintegral_radial_norm_rpow_eq_polar hd f hf hfm p w hw,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p)]
  rfl

/-! ## The exponent regions of BRS

The vertices `P₁` and `P₂,β` are the ones already used for the full type set;
the radial vertex `P₃,β^rad` is new, and it is strictly beyond the non-radial
vertex `P₃,β` because the Knapp examples do not apply to radial data. -/

/-- The radial vertex `P₃,β^rad = (d(d−1)/(d²−1+β), (d−1)/(d²−1+β))`. -/
def P3rad (d : ℕ) (beta : ℝ) : ExponentPoint :=
  let D : ℝ := d
  (D * (D - 1) / (D ^ 2 - 1 + beta), (D - 1) / (D ^ 2 - 1 + beta))

/-- The closed triangle `Δ_β = △(P₁, P₂,β, P₃,β^rad)` of BRS. -/
def Delta (d : ℕ) (beta : ℝ) : Set ExponentPoint :=
  convexHull ℝ {Q1, Q2 d beta, P3rad d beta}

/-- In two dimensions the radial vertex is `(2/(3+β), 1/(3+β))`. -/
theorem P3rad_two (beta : ℝ) : P3rad 2 beta = (2 / (3 + beta), 1 / (3 + beta)) := by
  unfold P3rad
  norm_num

/-- The vertex `P₄,γ^rad = (1/(1+γ), 1/(2(1+γ)))` of BRS, in two dimensions. -/
def P4rad (gam : ℝ) : ExponentPoint := (1 / (1 + gam), 1 / (2 * (1 + gam)))

/-- The vertex `P₅,β,γ^rad` of BRS, in two dimensions. -/
def P5rad (beta gam : ℝ) : ExponentPoint :=
  (((1 - beta) * (2 - beta / gam) + 2 * (1 - beta / gam)) /
      (2 * ((1 - beta) + 2 * (1 - beta / gam))),
    (1 - beta / gam) / ((1 - beta) + 2 * (1 - beta / gam)))

/-- The closed quadrangle `𝒬^rad_{β,γ}` of BRS, in two dimensions.  It is
defined for `2γ − β > 1`. -/
def Qrad (beta gam : ℝ) : Set ExponentPoint :=
  convexHull ℝ {Q1, Q2 2 beta, P4rad gam, P5rad beta gam}

end

end Auto.Spherical.FractalDilations.BRSRadial
